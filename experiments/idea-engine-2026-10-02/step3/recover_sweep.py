"""Adopt an orphaned sweep, then restart the approved campaign from its checkpoints.

No model calls here. One watcher per continuation, detached from the chat process.
Wait for the entire sweep process group, including its current Claude child.
"""
import argparse
from datetime import datetime, timezone
import fcntl
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(ROOT / 'atlas-data'))
from atomic import atomic_write_json


def snapshot():
    lines = subprocess.check_output(['ps', '-axo', 'pid,ppid,pgid,state,args'], text=True).splitlines()[1:]
    return {int(pid): {'parent': int(pp), 'group': int(pg), 'status': status, 'command': cmd}
            for pid, pp, pg, status, cmd in (line.strip().split(None, 4) for line in lines)}


def group_active(rows, group):
    return any(r['group'] == group and not r['status'].startswith('Z') for r in rows.values())


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--sweep-pid', type=int, required=True)
    ap.add_argument('--continuation', type=Path, required=True)
    args = ap.parse_args()
    folder = args.continuation.resolve()
    with (folder / '.recovery.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        rows = snapshot()
        sweep = rows.get(args.sweep_pid, {})
        expected = str(HERE / 'settle_nomap.py') + ' --sweep'
        if expected not in sweep.get('command', '') or sweep.get('group') != args.sweep_pid:
            raise RuntimeError('Expected sweep identity or process group changed')
        original = json.loads((folder / 'state.json').read_text())
        paused = {p: rows[p] for p in original['paused'] if p in rows}
        if len(paused) != len(original['paused']):
            raise RuntimeError('A paused process is missing; inspect before recovery')
        for row in paused.values():
            if not row['status'].startswith('T') or not (
                row['command'].endswith('Python resolution.py loop') or
                row['command'].startswith('caffeinate ') or
                str(ROOT / 'experiments/idea-engine-2026-10-02/screen.py') in row['command']
            ):
                raise RuntimeError('Paused process identity changed')
        state = {'stage': 'watching_sweep', 'pid': os.getpid(), 'sweep_pid': args.sweep_pid,
                 'paused': list(paused), 'exit_code': None}
        def save(**updates):
            state.update(updates)
            atomic_write_json(folder / 'recovery.json', state, indent=2)
        save()
        print(f'Watching sweep group {args.sweep_pid}; no additional model lane.', flush=True)
        while group_active(snapshot(), args.sweep_pid):
            time.sleep(30)
        # An orphan cannot be waitpid-ed: its exit status is unavailable, never inferred.
        save(stage='sweep_ended_exit_unavailable')
        subprocess.run([sys.executable, str(HERE / 'prescreen_priority.py')], cwd=ROOT, check=True)
        records = [json.loads(line) for line in (ROOT / 'resolution/prescreen.jsonl').read_text().splitlines()
                   if line.strip()]
        valid = [r for r in records if isinstance(r.get('mean'), (float, int))]
        save(recorded_problems=len(valid), at_or_above_0_3=sum(r['mean'] >= .3 for r in valid),
             recorded_cost=round(sum(r['cost'] for r in records), 4))
        # The old interpreter predates prescreen cost accounting. A checkpoint
        # restart is required so the resumed campaign observes the current daily cap.
        now = snapshot()
        for pid, expected_row in paused.items():
            if pid not in now or now[pid]['command'] != expected_row['command'] or not now[pid]['status'].startswith('T'):
                raise RuntimeError('Paused process changed before restoration')
        save(stage='restarting_campaign')
        for pid in paused:
            os.kill(pid, signal.SIGTERM)
        for pid in paused:
            try:
                os.kill(pid, signal.SIGCONT)
            except ProcessLookupError:
                pass
        deadline = time.monotonic() + 30
        while any(p in (current := snapshot()) and not current[p]['status'].startswith('Z') for p in paused):
            if time.monotonic() >= deadline:
                raise RuntimeError('Old campaign did not exit; refusing a second lane')
            time.sleep(1)
        with (folder / 'campaign-restarted.log').open('a') as log:
            campaign = subprocess.Popen([sys.executable, str(ROOT / 'resolution.py'), 'loop'], cwd=ROOT,
                                        stdin=subprocess.DEVNULL, stdout=log, stderr=subprocess.STDOUT,
                                        start_new_session=True)
        save(stage='campaign_restarted', campaign_pid=campaign.pid,
             finished_at=datetime.now(timezone.utc).isoformat())
        print(f'Campaign restarted from checkpoints: PID {campaign.pid}', flush=True)


if __name__ == '__main__':
    main()
