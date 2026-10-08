"""No model calls. Real short subprocesses exercise checkpoints, timeouts and resume."""
import fcntl
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import long_compute as C


class LongCompute(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name).resolve()
        self.folder = self.root / 'job'

    def prepare(self, codes, seconds=5, total=10):
        scripts = []
        for i, code in enumerate(codes):
            script = self.root / f'input{i}.py'
            script.write_text(code)
            scripts.append(script)
        return C.prepare(self.folder, scripts, 'test', 'Runner test only', 'provided test order', seconds, total)

    def run_job(self, **kw):
        # Sandbox policy is tested separately. Use portable short children here.
        with patch.object(C.H, 'sandbox_argv', side_effect=lambda p: [sys.executable, '-I', str(p)]) as argv:
            state = C.run(self.folder, **kw)
            return state, argv.call_count

    def test_completed_cases_are_not_recomputed_and_no_proof_is_claimed(self):
        self.prepare(['print("witness candidate")', 'print(2+2)'])
        state, count = self.run_job()
        self.assertEqual(count, 2)
        self.assertEqual([a['status'] for a in state['attempts']], ['completed', 'completed'])
        state, count = self.run_job()
        self.assertEqual(count, 0)
        self.assertIn('not a verified mathematical result', (self.folder / 'RESULTS.md').read_text())

    def test_timeout_keeps_output_and_requires_explicit_retry(self):
        self.prepare(['import time\nprint("partial", flush=True)\ntime.sleep(10)'], seconds=.1)
        state, _ = self.run_job()
        self.assertEqual(state['attempts'][0]['status'], 'timeout')
        self.assertIn('partial', (self.folder / state['attempts'][0]['output']).read_text())
        _, count = self.run_job()
        self.assertEqual(count, 0)
        state, count = self.run_job(retry_timeouts=True)
        self.assertEqual(count, 1)
        self.assertEqual(len(state['attempts']), 2)

    def test_total_budget_survives_resume(self):
        self.prepare(['import time\ntime.sleep(1)', 'print("not reached")'], seconds=.1, total=.05)
        state, count = self.run_job()
        self.assertEqual(count, 1)
        _, count = self.run_job(retry_timeouts=True)
        self.assertEqual(count, 0)

    def test_changed_script_is_refused(self):
        self.prepare(['print(1)'])
        (self.folder / 'case-0001/script.py').write_text('print(2)')
        with self.assertRaisesRegex(ValueError, 'script changed'):
            self.run_job()

    def test_unsafe_script_is_refused_before_creating_job(self):
        with self.assertRaisesRegex(ValueError, 'refused'):
            self.prepare(['import os\nos.system("echo unsafe")'])
        self.assertFalse(self.folder.exists())

    def test_worker_lock_refuses_duplicate(self):
        self.prepare(['print(1)'])
        with (self.folder / '.worker.lock').open('a') as lock:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            with self.assertRaisesRegex(RuntimeError, 'already has a worker'):
                self.run_job()

    def test_live_orphan_is_not_duplicated(self):
        self.prepare(['print(1)'])
        (self.folder / 'state.json').write_text(json.dumps({'attempts': [
            {'case': 'case-0001', 'status': 'running', 'pid': C.os.getpid(), 'allowed_seconds': 1}]}))
        with self.assertRaisesRegex(RuntimeError, 'may still be alive'):
            self.run_job()

    def test_failed_process_is_not_completed(self):
        self.prepare(['raise ValueError("bad case")'])
        state, _ = self.run_job()
        self.assertEqual(state['attempts'][0]['status'], 'failed')


if __name__ == '__main__':
    unittest.main()
