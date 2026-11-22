#!/usr/bin/env python3
"""Build player and goalie season stats from Spordle's public API.

For every finished game in each league's current season this fetches the
lineups (who dressed -> games played) and per-game stat lines (goals, assists,
PIM, goalie GA/minutes/result) and keeps them in a SQLite database. Games
already stored are not fetched again unless they are recent (scorekeepers
sometimes fix sheets a day or two later) or had no stats yet.

It then writes stats/stats-<league>.json next to index.html, which the app's
Stats tab reads.

Run it from cron, e.g. every 30 minutes:
  */30 * * * * /usr/bin/python3 /var/www/hockey/scripts/collect_stats.py >> ~/hockey-stats/collect.log 2>&1
"""
import argparse
import json
import os
import sqlite3
import sys
import time
import urllib.parse
import urllib.request
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timedelta, timezone

API = 'https://pub-api.play.spordle.com/api/sp'
# Public, read-only key published by page.spordle.com itself (same one index.html uses).
API_KEY = 'f08ed9064e3cdc382e6abb305ff543d0150fb52f'

# Keep in step with LEAGUES in index.html.
LEAGUES = [
    {'key': 'pcaha', 'name': 'PCAHA A', 'officeId': 786},
    {'key': 'pcehl', 'name': 'PCEHL', 'officeId': 8585},
]

HERE = os.path.dirname(os.path.abspath(__file__))
DEFAULT_OUT = os.path.join(os.path.dirname(HERE), 'stats')
DEFAULT_DB = os.path.expanduser('~/hockey-stats/stats.db')

REFRESH_DAYS = 3      # re-fetch games this recent, to pick up sheet corrections
WORKERS = 4           # parallel requests; keep it polite
PLAYER_POSITIONS = {'F', 'C', 'LW', 'RW', 'W', 'D'}


def log(*a):
    print(datetime.now().strftime('%Y-%m-%d %H:%M:%S'), *a, flush=True)


def api(path, flt=None, tries=3):
    url = API + path
    if flt is not None:
        url += ('&' if '?' in path else '?') + 'filter=' + urllib.parse.quote(json.dumps(flt))
    req = urllib.request.Request(url, headers={'Authorization': 'API-Key ' + API_KEY,
                                               'User-Agent': 'hockey-stats-collector'})
    for i in range(tries):
        try:
            with urllib.request.urlopen(req, timeout=30) as r:
                return json.load(r)
        except Exception as e:  # network blip or 5xx: back off and retry
            if i == tries - 1:
                raise RuntimeError(f'{path}: {e}') from e
            time.sleep(2 * (i + 1))


SCHEMA = """
CREATE TABLE IF NOT EXISTS games (
  id INTEGER PRIMARY KEY, league TEXT, season TEXT, schedule_id INTEGER, category_id TEXT,
  start_time TEXT, home_team_id INTEGER, away_team_id INTEGER, home_score INTEGER, away_score INTEGER,
  fetched_at TEXT, has_stats INTEGER DEFAULT 0
);
CREATE TABLE IF NOT EXISTS teams (id INTEGER PRIMARY KEY, name TEXT, short_name TEXT, logo_url TEXT);
CREATE TABLE IF NOT EXISTS players (id INTEGER PRIMARY KEY, full_name TEXT);
-- one row per player per game: dressed (GP) plus their stat line
CREATE TABLE IF NOT EXISTS skater_games (
  game_id INTEGER, team_id INTEGER, player_id INTEGER, number INTEGER, position TEXT,
  goals INTEGER DEFAULT 0, assists INTEGER DEFAULT 0, points INTEGER DEFAULT 0, pim INTEGER DEFAULT 0,
  ppg INTEGER DEFAULT 0, shg INTEGER DEFAULT 0, gwg INTEGER DEFAULT 0, is_affiliate INTEGER DEFAULT 0,
  PRIMARY KEY (game_id, team_id, player_id)
);
CREATE TABLE IF NOT EXISTS goalie_games (
  game_id INTEGER, team_id INTEGER, player_id INTEGER, number INTEGER,
  minutes REAL, goals_against INTEGER, result TEXT, shutout INTEGER, starter INTEGER,
  PRIMARY KEY (game_id, team_id, player_id)
);
CREATE TABLE IF NOT EXISTS schedules (id INTEGER PRIMARY KEY, league TEXT, season TEXT, category_id TEXT, name TEXT, type TEXT);
CREATE TABLE IF NOT EXISTS categories (id TEXT PRIMARY KEY, league TEXT, name TEXT);
"""


def open_db(path):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    db = sqlite3.connect(path)
    db.executescript(SCHEMA)
    return db


def fetch_game(gid):
    """Lineups, per-game stat lines and the box score for one game.

    gameStats is Spordle's own per-player summary, but it sometimes leaves out a
    player (e.g. someone listed as a goalie who scored as a skater), so goals and
    assists are counted from the box score's goal-by-goal list instead.
    """
    stats = api(f'/games/{gid}/gameStats')
    try:
        lineups = api(f'/games/{gid}/lineups')
    except RuntimeError:
        lineups = {}
    try:
        box = api(f'/games/{gid}/boxScore')
    except RuntimeError:
        box = None
    return gid, stats, lineups, box


# Penalty minutes by duration, for players missing from gameStats.
PENALTY_MINUTES = {'Minor': 2, 'Double Minor': 4, 'Major': 5, 'Misconduct': 10,
                   'Game Misconduct': 10, 'Gross Misconduct': 10, 'Match': 10}


def box_tallies(box):
    """{(team_id, player_id): {'goals','assists','ppg','shg','pim','number','name'}} from a box score."""
    out = {}

    def row(team_id, p):
        pid = (p or {}).get('participantId')
        if not pid or not team_id:
            return None  # 'Unknown' scorer on the sheet: nobody to credit
        r = out.setdefault((team_id, pid), {'goals': 0, 'assists': 0, 'ppg': 0, 'shg': 0, 'pim': 0})
        r['number'] = p.get('number')
        r['name'] = p.get('fullName')
        return r

    for gl in (box or {}).get('goals') or []:
        if gl.get('isOwnGoal'):
            continue
        r = row(gl.get('teamId'), gl.get('participant'))
        if r:
            r['goals'] += 1
            r['ppg'] += int(bool(gl.get('isPowerplay')))
            r['shg'] += int(bool(gl.get('isShorthanded')))
        for a in gl.get('assists') or []:
            ra = row(gl.get('teamId'), a)
            if ra:
                ra['assists'] += 1
    for pn in (box or {}).get('penalties') or []:
        if pn.get('isBenchPenalty'):
            continue
        r = row(pn.get('teamId'), pn.get('participant'))
        if r:
            r['pim'] += PENALTY_MINUTES.get((pn.get('duration') or {}).get('name'), 2)
    return out


def store_game(db, gid, stats, lineups, box=None):
    db.execute('DELETE FROM skater_games WHERE game_id=?', (gid,))
    db.execute('DELETE FROM goalie_games WHERE game_id=?', (gid,))
    numbers = {}
    goalie_ids = set()
    # Everyone who dressed as a player gets a game played, even with no points.
    for team_id, members in (lineups or {}).items():
        for m in members:
            pos = set(m.get('positions') or [])
            pid = m.get('participantId')
            if not pid:
                continue
            numbers[(int(team_id), pid)] = m.get('number')
            p = m.get('participant') or {}
            if p.get('fullName'):
                db.execute('INSERT OR REPLACE INTO players VALUES (?,?)', (pid, p['fullName']))
            if 'G' in pos:
                goalie_ids.add((int(team_id), pid))
            elif pos & PLAYER_POSITIONS:
                db.execute('INSERT OR IGNORE INTO skater_games (game_id,team_id,player_id,number,position,is_affiliate) '
                           'VALUES (?,?,?,?,?,?)', (gid, int(team_id), pid, m.get('number'),
                                                    '/'.join(sorted(pos & PLAYER_POSITIONS)), int(bool(m.get('isAffiliate')))))
    for s in stats or []:
        pid, tid = s.get('participantId'), s.get('teamId')
        if not pid or not tid:
            continue
        p = s.get('participant') or {}
        if p.get('fullName'):  # only the name is kept; registry ids are not stored
            db.execute('INSERT OR REPLACE INTO players VALUES (?,?)', (pid, p['fullName']))
        if s.get('type') == 'Goalie':
            db.execute('INSERT OR REPLACE INTO goalie_games VALUES (?,?,?,?,?,?,?,?,?)',
                       (gid, tid, pid, numbers.get((tid, pid)), s.get('minutesPlayed') or 0, s.get('goalAgainst') or 0,
                        s.get('result'), int(bool(s.get('shutout'))), int(bool(s.get('starter')))))
        elif s.get('type') == 'Skater':
            db.execute('INSERT OR IGNORE INTO skater_games (game_id,team_id,player_id,number) VALUES (?,?,?,?)',
                       (gid, tid, pid, numbers.get((tid, pid))))
            db.execute('UPDATE skater_games SET goals=?,assists=?,points=?,pim=?,ppg=?,shg=?,gwg=? '
                       'WHERE game_id=? AND team_id=? AND player_id=?',
                       (s.get('goals') or 0, s.get('assists') or 0, s.get('points') or 0, s.get('pim') or 0,
                        s.get('powerplayGoals') or 0, s.get('shorthandedGoals') or 0, int(bool(s.get('gameWinningGoal'))),
                        gid, tid, pid))
    # Goals and assists from the box score (see fetch_game). PIM stays as gameStats
    # reported it, except for players gameStats left out.
    if box and (box.get('goals') or box.get('penalties')):
        tallies = box_tallies(box)
        in_stats = {(s.get('teamId'), s.get('participantId')) for s in stats or [] if s.get('type') == 'Skater'}
        db.execute('UPDATE skater_games SET goals=0, assists=0, points=0, ppg=0, shg=0 WHERE game_id=?', (gid,))
        for (tid, pid), t in tallies.items():
            if t.get('name') and t['name'] != 'Unknown':
                db.execute('INSERT OR IGNORE INTO players VALUES (?,?)', (pid, t['name']))
            db.execute('INSERT OR IGNORE INTO skater_games (game_id,team_id,player_id,number) VALUES (?,?,?,?)',
                       (gid, tid, pid, numbers.get((tid, pid), t.get('number'))))
            db.execute('UPDATE skater_games SET goals=?, assists=?, points=?, ppg=?, shg=? '
                       'WHERE game_id=? AND team_id=? AND player_id=?',
                       (t['goals'], t['assists'], t['goals'] + t['assists'], t['ppg'], t['shg'], gid, tid, pid))
            if (tid, pid) not in in_stats:
                db.execute('UPDATE skater_games SET pim=? WHERE game_id=? AND team_id=? AND player_id=?', (t['pim'], gid, tid, pid))
    # A goalie who dressed but has no goalie line didn't play; nothing to record.
    has = 1 if (stats or (box and box.get('goals'))) else 0
    db.execute('UPDATE games SET fetched_at=?, has_stats=? WHERE id=?',
               (datetime.now(timezone.utc).isoformat(), has, gid))


def current_season(lg):
    seasons = api(f"/seasons?officeId={lg['officeId']}")
    return next((s for s in seasons if s.get('isCurrent')), seasons[0])['seasonId']


def sync_league(db, lg, season, full=False):
    cats = api(f"/categories?officeId={lg['officeId']}&seasonId={season}")
    scheds = api(f"/schedules?officeId={lg['officeId']}&seasonId={season}")
    for c in cats:
        db.execute('INSERT OR REPLACE INTO categories VALUES (?,?,?)', (c['id'], lg['key'], c.get('name')))
    for s in scheds:
        db.execute('INSERT OR REPLACE INTO schedules VALUES (?,?,?,?,?,?)',
                   (s['id'], lg['key'], season, s.get('categoryId'), s.get('name'), s.get('type')))
    ids = [s['id'] for s in scheds]
    games = []
    for i in range(0, len(ids), 20):
        games += api('/games', {'where': {'scheduleId': {'inq': ids[i:i + 20]}}, 'include': ['homeTeam', 'awayTeam']})

    now = datetime.now(timezone.utc)
    known = {r[0]: (r[1], r[2]) for r in db.execute('SELECT id, fetched_at, has_stats FROM games WHERE league=? AND season=?', (lg['key'], season))}
    todo = []
    for g in games:
        for t in (g.get('homeTeam'), g.get('awayTeam')):
            if t:
                db.execute('INSERT OR REPLACE INTO teams VALUES (?,?,?,?)', (t['id'], t.get('name'), t.get('shortName'), t.get('logoUrl')))
        score = g.get('score') or {}
        start = datetime.fromisoformat(g['startTime'].replace('Z', '+00:00'))
        played = g.get('status') == 'Active' and start < now and score
        db.execute('INSERT INTO games (id,league,season,schedule_id,category_id,start_time,home_team_id,away_team_id,home_score,away_score) '
                   'VALUES (?,?,?,?,?,?,?,?,?,?) ON CONFLICT(id) DO UPDATE SET schedule_id=excluded.schedule_id, '
                   'category_id=excluded.category_id, start_time=excluded.start_time, home_team_id=excluded.home_team_id, '
                   'away_team_id=excluded.away_team_id, home_score=excluded.home_score, away_score=excluded.away_score',
                   (g['id'], lg['key'], season, g.get('scheduleId'), g.get('categoryId'), g['startTime'],
                    g.get('homeTeamId'), g.get('awayTeamId'),
                    score.get(str(g.get('homeTeamId'))), score.get(str(g.get('awayTeamId')))))
        if not played:
            continue
        fetched, has = known.get(g['id'], (None, 0))
        if full or not fetched or not has or start > now - timedelta(days=REFRESH_DAYS):
            todo.append(g['id'])
    # Games that were cancelled or moved out of the season keep no stats.
    live_ids = {g['id'] for g in games}
    for gid in set(known) - live_ids:
        for t in ('skater_games', 'goalie_games', 'games'):
            db.execute(f'DELETE FROM {t} WHERE {"id" if t == "games" else "game_id"}=?', (gid,))
    db.commit()

    log(f"{lg['name']} {season}: {len(games)} games, {len(todo)} to fetch")
    errors = 0
    with ThreadPoolExecutor(WORKERS) as ex:
        for n, fut in enumerate([ex.submit(fetch_game, gid) for gid in todo], 1):
            try:
                store_game(db, *fut.result())
            except Exception as e:
                errors += 1
                log('  failed:', e)
            if n % 50 == 0:
                db.commit()
                log(f'  {n}/{len(todo)}')
    db.commit()
    return errors


def export_league(db, lg, season, out_dir, current=False):
    q = lambda sql, *a: db.execute(sql, a).fetchall()
    key = lg['key']
    skaters = q("""
        SELECT sg.player_id, p.full_name, MAX(sg.number), sg.team_id, g.schedule_id,
               COUNT(*), SUM(goals), SUM(assists), SUM(points), SUM(pim), SUM(ppg), SUM(shg), SUM(gwg)
        FROM skater_games sg JOIN games g ON g.id = sg.game_id JOIN players p ON p.id = sg.player_id
        WHERE g.league=? AND g.season=?
        GROUP BY sg.player_id, sg.team_id, g.schedule_id""", key, season)
    goalies = q("""
        SELECT gg.player_id, p.full_name, MAX(gg.number), gg.team_id, g.schedule_id,
               COUNT(*), SUM(result='win'), SUM(result='loss'), SUM(result='tie'),
               SUM(goals_against), ROUND(SUM(minutes),1), SUM(shutout)
        FROM goalie_games gg JOIN games g ON g.id = gg.game_id JOIN players p ON p.id = gg.player_id
        WHERE g.league=? AND g.season=?
        GROUP BY gg.player_id, gg.team_id, g.schedule_id""", key, season)
    team_ids = {r[3] for r in skaters} | {r[3] for r in goalies}
    teams = {str(r[0]): [r[1], r[2]] for r in q('SELECT id,name,short_name FROM teams') if r[0] in team_ids}
    scheds = {str(r[0]): [r[1], r[2], r[3]] for r in q('SELECT id,category_id,name,type FROM schedules WHERE league=? AND season=?', key, season)}
    cat_ids = {v[0] for v in scheds.values()}
    cats = {r[0]: r[1] for r in q('SELECT id,name FROM categories WHERE league=?', key) if r[0] in cat_ids}
    # every season with stats, newest first, so the app can offer a season picker
    seasons = [r[0] for r in q('SELECT DISTINCT season FROM games WHERE league=? AND has_stats=1 ORDER BY season DESC', key)]
    games_done = q('SELECT COUNT(*), SUM(has_stats) FROM games WHERE league=? AND season=? AND fetched_at IS NOT NULL', key, season)[0]
    data = {
        'version': 1,
        'league': key,
        'season': season,
        'seasons': seasons,
        'generatedAt': datetime.now(timezone.utc).isoformat(timespec='seconds'),
        'games': games_done[0] or 0,
        'gamesWithStats': games_done[1] or 0,
        'teams': teams,                 # id -> [name, shortName]
        'schedules': scheds,            # id -> [categoryId, name, type]
        'categories': cats,             # id -> division name
        # one row per player per team per schedule; the app adds up the schedules being viewed
        'skaterCols': ['id', 'name', 'num', 'team', 'sched', 'gp', 'g', 'a', 'pts', 'pim', 'ppg', 'shg', 'gwg'],
        'skaters': [list(r) for r in skaters],
        'goalieCols': ['id', 'name', 'num', 'team', 'sched', 'gp', 'w', 'l', 't', 'ga', 'min', 'so'],
        'goalies': [list(r) for r in goalies],
    }
    if not current and not (games_done[1] or 0):
        log(f"{lg['name']} {season}: no game sheets, nothing written")
        return
    os.makedirs(out_dir, exist_ok=True)
    # stats-<league>-<season>.json for every season; stats-<league>.json is the current one
    names = [f'stats-{key}-{season}.json'] + ([f'stats-{key}.json'] if current else [])
    for name in names:
        path = os.path.join(out_dir, name)
        tmp = path + '.tmp'
        with open(tmp, 'w') as f:
            json.dump(data, f, separators=(',', ':'))
        os.replace(tmp, path)  # atomic, so the site never reads a half-written file
    log(f"{lg['name']} {season}: wrote {', '.join(names)} ({len(skaters)} skater rows, {len(goalies)} goalie rows)")


def backup(db, folder, keep_daily=14, keep_monthly=12):
    """One snapshot a day (stats-YYYY-MM-DD.db); keeps the last 14 days plus the first of each of the last 12 months."""
    folder = os.path.expanduser(folder)
    os.makedirs(folder, exist_ok=True)
    today = datetime.now().strftime('%Y-%m-%d')
    path = os.path.join(folder, f'stats-{today}.db')
    if os.path.exists(path):
        return
    tmp = path + '.tmp'
    dst = sqlite3.connect(tmp)
    db.backup(dst)  # consistent copy even while the database is in use
    dst.close()
    os.replace(tmp, path)
    snaps = sorted(f for f in os.listdir(folder) if f.startswith('stats-') and f.endswith('.db'))
    monthly = {}
    for f in snaps:
        monthly.setdefault(f[6:13], f)  # first snapshot of each month
    keep = set(snaps[-keep_daily:]) | set(sorted(monthly.values())[-keep_monthly:])
    for f in snaps:
        if f not in keep:
            os.remove(os.path.join(folder, f))
    log(f'backup: {path} ({len(keep)} kept)')


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--db', default=DEFAULT_DB)
    ap.add_argument('--out', default=DEFAULT_OUT, help='folder for stats-<league>.json')
    ap.add_argument('--league', action='append', help='only these league keys (default: all)')
    ap.add_argument('--full', action='store_true', help='re-fetch every finished game')
    ap.add_argument('--backup-dir', help='also keep a daily snapshot of the database here')
    ap.add_argument('--season', action='append', help='season(s) to sync, e.g. 2025-26 (default: the current one)')
    args = ap.parse_args()

    db = open_db(args.db)
    failed = False
    for lg in LEAGUES:
        if args.league and lg['key'] not in args.league:
            continue
        try:
            cur = current_season(lg)
            for season in args.season or [cur]:
                errors = sync_league(db, lg, season, args.full)
                export_league(db, lg, season, args.out, current=season == cur)
                failed |= errors > 0
            if args.season and cur not in args.season:
                export_league(db, lg, cur, args.out, current=True)  # refresh its list of seasons
        except Exception as e:
            log(f"{lg['name']}: FAILED - {e}")
            failed = True
    if args.backup_dir:
        try:
            backup(db, args.backup_dir)
        except Exception as e:
            log('backup FAILED -', e)
            failed = True
    sys.exit(1 if failed else 0)


if __name__ == '__main__':
    main()
