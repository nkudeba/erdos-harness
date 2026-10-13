"""Recovery lifecycle checks; no real signals, provider calls, or campaign launch."""
import importlib.util
import json
from pathlib import Path
import signal
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('sweep_recovery', ROOT / 'experiments/idea-engine-2026-10-02/step3/recover_sweep.py')
M = importlib.util.module_from_spec(spec)
spec.loader.exec_module(M)


class Recovery(unittest.TestCase):
    def test_live_child_keeps_lane_reserved_after_parent_exits(self):
        self.assertTrue(M.group_active({9: {'group': 2, 'status': 'S'}}, 2))
        self.assertFalse(M.group_active({2: {'group': 2, 'status': 'Z'}}, 2))

    def test_priority_then_checkpoint_restart_with_unknown_exit(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            folder = root / 'continuation'
            folder.mkdir()
            (folder / 'state.json').write_text(json.dumps({'paused': [100]}))
            (root / 'resolution').mkdir()
            (root / 'resolution/prescreen.jsonl').write_text('{"problem":"655","mean":0.85,"cost":0.2}\n')
            paused = {100: {'parent': 1, 'group': 100, 'status': 'T',
                            'command': '/usr/bin/Python resolution.py loop'}}
            initial = {**paused, 200: {'parent': 1, 'group': 200, 'status': 'S',
                                       'command': 'python ' + str(M.HERE / 'settle_nomap.py') + ' --sweep'}}
            events = []
            with patch.object(M, 'ROOT', root), \
                    patch.object(M.sys, 'argv', ['recover', '--sweep-pid', '200', '--continuation', str(folder)]), \
                    patch.object(M, 'snapshot', side_effect=[initial, paused, paused, {}]), \
                    patch.object(M.subprocess, 'run', side_effect=lambda *a, **k: events.append('priority')), \
                    patch.object(M.os, 'kill', side_effect=lambda p, s: events.append(s)), \
                    patch.object(M.subprocess, 'Popen', return_value=SimpleNamespace(pid=300)) as launch:
                M.main()
            self.assertEqual(events, ['priority', signal.SIGTERM, signal.SIGCONT])
            self.assertEqual(launch.call_count, 1)
            state = json.loads((folder / 'recovery.json').read_text())
            self.assertEqual(state['stage'], 'campaign_restarted')
            self.assertIsNone(state['exit_code'])
            self.assertEqual(state['at_or_above_0_3'], 1)


if __name__ == '__main__':
    unittest.main()
