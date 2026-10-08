"""One bounded, operator-authorized calibration -> sweep continuation.

Pause the idle campaign tree for exclusive use of the model lane, and restore it
in finally. This is a foreground job, not a recurring scheduler or a second campaign.
"""
import argparse
from datetime import datetime
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time
from zoneinfo import ZoneInfo

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / 'atlas-data'))
sys.path.insert(0, str(ROOT / 'benchmarks/timesplit'))
sys.path.insert(0, str(HERE))
from atomic import atomic_write_json, atomic_write
import settle_nomap as S
import timesplit as T


def processes():
    lines = subprocess.check_output(['ps', '-axo', 'pid,ppid,args'], text=True).splitlines()[1:]
    return {int(p): (int(pp), cmd) for p, pp, cmd in (line.strip().split(None, 2) for line in lines)}


def campaign_tree(pid, rows):
    if pid not in rows or not rows[pid][1].endswith('Python resolution.py loop'):
        raise RuntimeError('Campaign identity changed; refusing to signal it')
    tree = [pid]
    for parent in tree:
        tree.extend(p for p, (pp, _) in rows.items() if pp == parent)
    for p in tree[1:]:
        cmd = rows[p][1]
        if not (cmd.startswith('caffeinate ') or
                str(ROOT / 'experiments/idea-engine-2026-10-02/screen.py') in cmd):
            raise RuntimeError(f'Campaign has active work (PID {p}); do not pause mid-call')
    return tree


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--pause-pid', type=int, required=True)
    ap.add_argument('--max-sweep-spend', type=float, default=150)
    a = ap.parse_args()
    folder = ROOT / 'runs' / ('nomap-continuation-' + datetime.now().strftime('%Y%m%d-%H%M%S'))
    folder.mkdir(parents=True)
    state = {'stage': 'starting', 'folder': str(folder), 'paused': []}
    rows = processes()
    tree = campaign_tree(a.pause_pid, rows)
    child = None

    def save(**updates):
        state.update(updates)
        atomic_write_json(folder / 'state.json', state, indent=2)

    def stop(signum, frame):
        raise KeyboardInterrupt

    def command(mode, cap, attempt):
        nonlocal child
        log = folder / f'{mode}-{attempt}.log'
        save(stage=mode, log=str(log))
        with log.open('w') as output:
            child = subprocess.Popen([sys.executable, str(HERE / 'settle_nomap.py'), '--' + mode,
                                      '--max-spend', str(cap)], cwd=ROOT, stdout=output,
                                     stderr=subprocess.STDOUT, start_new_session=True)
            rc = child.wait(timeout=12 * 3600)
        child = None
        return rc, log.read_text(errors='replace')

    for sig in (signal.SIGTERM, signal.SIGHUP):
        signal.signal(sig, stop)
    try:
        # Stop the parent before its sleeping screen; it cannot schedule another stage.
        for pid in tree:
            os.kill(pid, signal.SIGSTOP)
            state['paused'].append(pid)
            save(stage='paused')
        print(f'Campaign paused. Continuation evidence: {folder}', flush=True)
        for attempt in (1, 2):
            rc, log = command('calib', 16, attempt)
            if rc == 0:
                break
            if attempt == 1 and T.LIMIT_RE.search(log):
                wait = T.seconds_until_reset(log, now=datetime.now(ZoneInfo('America/Toronto')))
                save(stage='waiting_for_reset', wait_seconds=wait, resume_at=time.time() + wait)
                print(f'Claude reports its limit; waiting {wait/60:.1f} minutes before one resume.', flush=True)
                until = time.monotonic() + wait
                while time.monotonic() < until:
                    time.sleep(min(30, until - time.monotonic()))
            else:
                save(stage='calibration_stopped', exit_code=rc)
                return rc
        analysis = S.calibration_analysis()
        save(stage='calibration_analyzed', calibration=analysis)
        atomic_write_json(HERE / 'settle_nomap_analysis.json', analysis, indent=2)
        print('Calibration: ' + json.dumps(analysis), flush=True)
        if analysis['decision'] != 'sweep':
            save(stage='no_sweep', reason=analysis['decision'])
            return 2
        rc, log = command('sweep', a.max_sweep_spend, 1)
        prescreen = ROOT / 'resolution/prescreen.jsonl'
        drawn = [json.loads(line) for line in prescreen.read_text().splitlines() if line.strip()] if prescreen.exists() else []
        valid = [r for r in drawn if r.get('mean') is not None]
        summary = {'recorded_problems': len(valid), 'at_or_above_0_3': sum(r['mean'] >= .3 for r in valid),
                   'recorded_cost': round(sum(r['cost'] for r in drawn), 4), 'exit_code': rc,
                   'top': sorted(valid, key=lambda r: -r['mean'])[:20]}
        atomic_write_json(HERE / 'settle_nomap_sweep_summary.json', summary, indent=2)
        save(stage='finished' if rc == 0 else 'sweep_stopped', sweep=summary)
        return rc
    except BaseException as e:
        save(stage='error', error=repr(e))
        raise
    finally:
        if child is not None and child.poll() is None:
            os.killpg(child.pid, signal.SIGTERM)
            try:
                child.wait(timeout=10)
            except subprocess.TimeoutExpired:
                os.killpg(child.pid, signal.SIGKILL)
                child.wait()
        current = processes()
        restored = []
        for pid in reversed(state['paused']):
            if pid in current and current[pid] == rows[pid]:
                os.kill(pid, signal.SIGCONT)
                restored.append(pid)
        save(restored=restored, finished_at=datetime.now(ZoneInfo('America/Toronto')).isoformat())
        atomic_write(HERE / 'CONTINUATION.md', '# Screening continuation\n\n'
                     + 'Saved execution state (calibration and sweep completion are separate):\n\n```json\n'
                     + json.dumps(state, indent=2) + '\n```\n')
        print('Campaign processes restored: ' + str(restored), flush=True)


if __name__ == '__main__':
    raise SystemExit(main())
