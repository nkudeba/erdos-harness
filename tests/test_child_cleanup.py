"""A killed harness run takes its model sessions with it (run_tracked, terminate_children).

Step 3's #120 engine run was stopped on 2026-10-07 and three of its `claude -p` sessions kept running, and billing, as
orphans until they were killed by hand."""
import subprocess, sys, threading, time, unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import harness as H


class RunTracked(unittest.TestCase):
    def test_output_and_returncode_pass_through(self):
        r = H.run_tracked([sys.executable, "-c", "import sys; print(sys.stdin.read().upper()); sys.exit(3)"], input="hi")
        self.assertEqual((r.returncode, r.stdout.strip()), (3, "HI"))
        self.assertEqual(H._LIVE_CHILDREN, set())

    def test_a_timeout_kills_the_child_and_raises(self):
        t0 = time.time()
        with self.assertRaises(subprocess.TimeoutExpired):
            H.run_tracked([sys.executable, "-c", "import time; time.sleep(30)"], timeout=1)
        self.assertLess(time.time() - t0, 10)
        self.assertEqual(H._LIVE_CHILDREN, set())

    def test_terminate_children_stops_a_tracked_session(self):
        out = {}
        th = threading.Thread(target=lambda: out.setdefault("r", H.run_tracked([sys.executable, "-c", "import time; time.sleep(30)"])))
        t0 = time.time()
        th.start()
        while not H._LIVE_CHILDREN and time.time() - t0 < 5:
            time.sleep(0.05)
        H.terminate_children()
        th.join(10)
        self.assertFalse(th.is_alive())
        self.assertNotEqual(out["r"].returncode, 0)
        self.assertLess(time.time() - t0, 10)


if __name__ == "__main__":
    unittest.main()
