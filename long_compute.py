"""Opt-in, model-free computation tier. Each script is one resumable case, not a proof.

Prepare immutable case scripts with `prepare`, then `run` the job directory. The
existing harness sandbox applies; hours of solver time do not hold a model call
open. Completed cases are skipped on resume. Timeouts require explicit retry.
"""
from __future__ import annotations

import argparse
import fcntl
import hashlib
import json
import math
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

import harness as H

sys.path.insert(0, str(Path(__file__).resolve().parent / 'atlas-data'))
from atomic import atomic_write_json


def digest(text):
    return hashlib.sha256(text.encode()).hexdigest()


def prepare(folder: Path, scripts: list[Path], problem: str, scope: str,
            order_by: str, seconds: float = 7200, total_seconds: float = 14400):
    if not all(math.isfinite(x) and x > 0 for x in (seconds, total_seconds)) or not scripts:
        raise ValueError('Positive time budgets and at least one case are required')
    sources = []
    for script in scripts:
        code = script.read_text()
        bad = H.unsafe_python(code, H.EXPLORE_MODULES, H.EXPLORE_FORBIDDEN)
        if bad:
            raise ValueError(f'{script.name}: refused {bad}')
        compile(code, str(script), 'exec')
        sources.append((script.resolve(), code))
    folder.mkdir(parents=True, exist_ok=False)
    jobs = []
    for i, (source, code) in enumerate(sources, 1):
        case = folder / f'case-{i:04d}'
        case.mkdir()
        (case / 'script.py').write_text(code)
        jobs.append({'id': case.name, 'source': str(source), 'sha256': digest(code)})
    manifest = {'version': 1, 'problem': problem, 'scope': scope, 'order_by': order_by,
                'seconds': seconds, 'total_seconds': total_seconds, 'jobs': jobs,
                'assistance': 'Operator selected scripts and attack order for the long computation tier.',
                'claimEligible': False}
    atomic_write_json(folder / 'manifest.json', manifest, indent=2)
    return manifest


def script_path(folder, job):
    path = folder / job['id'] / 'script.py'
    if path.resolve().parent != folder / job['id'] or not path.is_file():
        raise ValueError('Case script must remain inside its original case directory')
    code = path.read_text()
    if digest(code) != job['sha256']:
        raise ValueError(f"{job['id']}: script changed; prepare a new job instead")
    bad = H.unsafe_python(code, H.EXPLORE_MODULES, H.EXPLORE_FORBIDDEN)
    if bad:
        raise ValueError(f"{job['id']}: refused {bad}")
    return path


def stop_process(proc):
    if proc.poll() is None:
        os.killpg(proc.pid, signal.SIGTERM)
        try:
            proc.wait(timeout=3)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, signal.SIGKILL)
            proc.wait()


def run(folder: Path, retry_timeouts=False):
    folder = folder.resolve()
    with (folder / '.worker.lock').open('a') as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise RuntimeError('This computation already has a worker')
        manifest = json.loads((folder / 'manifest.json').read_text())
        if not all(math.isfinite(manifest[k]) and manifest[k] > 0 for k in ('seconds', 'total_seconds')):
            raise ValueError('Time budgets must be positive and finite')
        state_path = folder / 'state.json'
        state = json.loads(state_path.read_text()) if state_path.exists() else {'attempts': []}
        # A killed controller may have left its solver alive. Never duplicate it.
        for attempt in state['attempts']:
            if attempt['status'] != 'running':
                continue
            pid = attempt.get('pid')
            if pid:
                try:
                    os.kill(pid, 0)
                except ProcessLookupError:
                    pass
                else:
                    raise RuntimeError(f'Previous solver PID {pid} may still be alive; inspect before resuming')
            attempt.update(status='interrupted', elapsed=attempt['allowed_seconds'])
        atomic_write_json(state_path, state, indent=2)
        scripts = [(job, script_path(folder, job)) for job in manifest['jobs']]
        print('CANDIDATES: ' + json.dumps({'order_by': manifest['order_by'],
                                         'cases': [j['id'] for j, _ in scripts]}), flush=True)
        old_handlers = {}

        def interrupted(signum, frame):
            raise KeyboardInterrupt

        for sig in (signal.SIGTERM, signal.SIGHUP):
            old_handlers[sig] = signal.signal(sig, interrupted)
        try:
            for job, script in scripts:
                previous = [a for a in state['attempts'] if a['case'] == job['id']]
                if previous and (previous[-1]['status'] == 'completed' or
                                 previous[-1]['status'] == 'timeout' and not retry_timeouts):
                    continue
                remaining = manifest['total_seconds'] - sum(a.get('elapsed', 0) for a in state['attempts'])
                if remaining <= 0:
                    break
                allowed = min(manifest['seconds'], remaining)
                attempt = {'case': job['id'], 'status': 'running', 'allowed_seconds': allowed,
                           'started_at': time.time(), 'output': f"{job['id']}/attempt-{len(previous)+1}.log"}
                state['attempts'].append(attempt)
                atomic_write_json(state_path, state, indent=2)
                proc = None
                start = time.monotonic()
                try:
                    with (folder / attempt['output']).open('w') as output:
                        proc = subprocess.Popen(H.sandbox_argv(script), cwd=script.parent,
                                                stdout=output, stderr=subprocess.STDOUT, start_new_session=True,
                                                env={'PATH': '/usr/bin:/bin', 'HOME': str(script.parent),
                                                     'PYTHONUNBUFFERED': '1'})
                        attempt['pid'] = proc.pid
                        atomic_write_json(state_path, state, indent=2)
                        rc = proc.wait(timeout=allowed)
                        attempt.update(status='completed' if rc == 0 else 'failed', exit_code=rc)
                except subprocess.TimeoutExpired:
                    attempt['status'] = 'timeout'
                except BaseException:
                    attempt['status'] = 'interrupted'
                    raise
                finally:
                    if proc is not None:
                        stop_process(proc)
                    attempt['elapsed'] = round(time.monotonic() - start, 3)
                    atomic_write_json(state_path, state, indent=2)
                    write_summary(folder, manifest, state)
                print(f"COMPUTE-CASE case={job['id']} status={attempt['status']} "
                      f"wall={attempt['elapsed']:.1f}s", flush=True)
        finally:
            for sig, handler in old_handlers.items():
                signal.signal(sig, handler)
            write_summary(folder, manifest, state)
        return state


def write_summary(folder, manifest, state):
    latest = {a['case']: a for a in state['attempts']}
    lines = [f"# Long computation: problem {manifest['problem']}", '', manifest['scope'], '',
             'Computational evidence only. A completed process is not a verified mathematical result.',
             'Timeouts and interrupted cases establish no search floor. No model calls were made.', '',
             '| Case | Process status | Output |', '|---|---|---|']
    for job in manifest['jobs']:
        attempt = latest.get(job['id'], {})
        log = attempt.get('output')
        lines.append(f"| {job['id']} | {attempt.get('status', 'pending')} | "
                     + (f'[{log}]({log})' if log else '—') + ' |')
    from atomic import atomic_write
    atomic_write(folder / 'RESULTS.md', '\n'.join(lines) + '\n')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    sub = ap.add_subparsers(dest='cmd', required=True)
    prep = sub.add_parser('prepare')
    prep.add_argument('--output', type=Path, required=True)
    prep.add_argument('--script', type=Path, action='append', required=True)
    prep.add_argument('--problem', required=True)
    prep.add_argument('--scope', required=True)
    prep.add_argument('--order-by', required=True, help='Why this case order follows the necessary conditions')
    prep.add_argument('--seconds', type=float, default=7200)
    prep.add_argument('--total-seconds', type=float, default=14400)
    work = sub.add_parser('run')
    work.add_argument('folder', type=Path)
    work.add_argument('--retry-timeouts', action='store_true')
    args = ap.parse_args()
    if args.cmd == 'prepare':
        prepare(args.output, args.script, args.problem, args.scope, args.order_by, args.seconds, args.total_seconds)
        print(args.output / 'manifest.json')
    else:
        run(args.folder, args.retry_timeouts)


if __name__ == '__main__':
    main()
