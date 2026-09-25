"""The improvement loop's machinery (docs/improvement-loop.md): budget ledger, diagnosis, branch commits that never
touch HEAD, the index or the working tree. No model calls; git runs in a throwaway repository."""
import importlib.util, json, os, subprocess, tempfile, unittest
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("loop", ROOT / "benchmarks" / "timesplit" / "loop.py")
L = importlib.util.module_from_spec(spec)
spec.loader.exec_module(L)


class Budget(unittest.TestCase):
    def test_spent_reserved_and_left(self):
        with tempfile.TemporaryDirectory() as d:
            res = Path(d)
            (res / "screen-a.jsonl").write_text(json.dumps({"spend": 3.5}) + "\n" + json.dumps({"spend": 1.5}) + "\n")
            (res / "screen-a.infra.jsonl").write_text(json.dumps({"spend": 0.5}) + "\n")
            (res / "calib-x.ideas.jsonl").write_text(json.dumps({"cost_usd": 0.25}) + "\n")
            state = {"budget_usd": 200, "ledger": [
                {"kind": "explore-screen", "name": "screen-a", "estimate": 20, "in_flight": True},
                {"kind": "ideas", "name": "calib-x", "estimate": 1, "in_flight": False},
                {"kind": "manual", "name": "probe", "usd": 2.0, "in_flight": False}]}
            with patch.object(L, "RESULTS", res):
                b = L.budget(state)
                self.assertEqual(b["spent"], 7.75)                   # 5.5 run + 0.25 judge + 2 manual
                self.assertEqual(b["reserved"], 14.5)                # the in-flight screen's unspent estimate
                self.assertEqual(b["left"], 177.75)
                self.assertTrue(L.can_spend(state, 170))
                self.assertFalse(L.can_spend(state, 180))


class StopSignals(unittest.TestCase):
    def test_every_results_file_is_read_and_acks_are_honoured(self):
        with tempfile.TemporaryDirectory() as d:
            res = Path(d)
            # the operator's lane, not in the loop's ledger: its dev solve must still surface
            (res / "discover-v2-x.jsonl").write_text(
                json.dumps({"problem": "1213", "split": "dev", "solved": True, "contradiction": False}) + "\n"
                + json.dumps({"problem": "150", "split": "dev", "solved": False}) + "\n")
            (res / "train-a.jsonl").write_text(json.dumps({"problem": "997", "split": "train", "solved": True}) + "\n")
            (res / "screen-b.jsonl").write_text(
                json.dumps({"problem": "7", "split": "train", "solved": True, "contradiction": True}) + "\n")
            (res / "discover-v2-x.infra.jsonl").write_text(json.dumps({"problem": "9", "split": "dev", "solved": True}) + "\n")
            (res / "discover-v2-x.progress.jsonl").write_text(json.dumps({"problem": "9", "solved": True}) + "\n")
            with patch.object(L, "RESULTS", res):
                sig = L.stop_signals({})
                self.assertEqual(sorted((s["tag"], s["problem"], s["kind"]) for s in sig),
                                 [("discover-v2-x", "1213", "solve"), ("screen-b", "7", "contradiction"),
                                  ("train-a", "997", "solve")])
                stopping = {s["problem"] for s in sig if L.stops_the_loop(s)}
                self.assertEqual(stopping, {"1213", "7"})            # a train solve does not stop; a contradiction does
                acked = L.stop_signals({"acknowledged": [{"tag": "discover-v2-x", "problem": "1213"}]})
                self.assertTrue(next(s for s in acked if s["problem"] == "1213")["acknowledged"])
                self.assertFalse(next(s for s in acked if s["problem"] == "7")["acknowledged"])


class Diagnosis(unittest.TestCase):
    def test_rates_rejections_and_the_never_succeeds_flag(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / "runs" / "r1").mkdir(parents=True)
            ev = [{"ts": "2026-09-25T01:00:00Z", "stage": "program", "event": "skeleton_candidate_rejected",
                   "reason": "no improvement over the skeleton in force"},
                  {"ts": "2026-09-25T01:00:00Z", "stage": "program", "event": "conditional_certified"},
                  {"ts": "2026-09-25T01:00:00Z", "stage": "llm", "event": "response", "purpose": "plan", "cost_usd": 0.3}]
            ev += [{"ts": "2026-09-25T01:00:00Z", "stage": "lean", "event": "check", "name": "cascade"}] * 25
            (root / "runs" / "r1" / "log.jsonl").write_text("\n".join(json.dumps(e) for e in ev) + "\n")
            with patch.object(L, "ROOT", root):
                out = L.diagnose()
        self.assertEqual(out["rates"]["plans adopted / plan candidates"], [1, 2])
        self.assertEqual(out["plan_rejections"], {"not better than the incumbent": 1})
        self.assertIn("never succeeds: cascade closures / cascade passes = 0 of 25", out["flags"])


class BranchCommits(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        env = {**os.environ, "GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@t", "GIT_COMMITTER_NAME": "t",
               "GIT_COMMITTER_EMAIL": "t@t"}
        self.env = env
        run = lambda *a: subprocess.run(["git", *a], cwd=self.root, env=env, check=True, capture_output=True)
        run("init", "-q", "-b", "main")
        (self.root / "harness.py").write_text("v1\n")
        (self.root / "other.txt").write_text("not ours\n")
        run("add", ".")
        run("commit", "-q", "-m", "base")
        self.run_git = run

    def tearDown(self):
        self.tmp.cleanup()

    def git(self, *a):
        return subprocess.run(["git", *a], cwd=self.root, capture_output=True, text=True).stdout.strip()

    def test_commits_land_on_the_branch_and_nothing_else_moves(self):
        head = self.git("rev-parse", "HEAD")
        (self.root / "harness.py").write_text("v2 with fixes\n")
        (self.root / "other.txt").write_text("someone else's work in progress\n")
        with patch.object(L, "ROOT", self.root), patch.dict(os.environ, self.env):
            sha = L.commit_to_branch("iteration 1", paths=["harness.py"])
            self.assertIsNotNone(sha)
            self.assertEqual(self.git("rev-parse", "HEAD"), head)                  # HEAD untouched
            self.assertEqual(self.git("symbolic-ref", "--short", "HEAD"), "main")
            self.assertEqual((self.root / "harness.py").read_text(), "v2 with fixes\n")   # working tree untouched
            self.assertIn("M harness.py", self.git("status", "--short"))           # still uncommitted on main
            self.assertEqual(self.git("show", "harness-loop:harness.py"), "v2 with fixes")
            self.assertEqual(self.git("show", "harness-loop:other.txt"), "not ours")   # only named paths go in
            self.assertIn("Co-Authored-By: Claude", self.git("log", "-1", "--format=%B", "harness-loop"))
            self.assertIsNone(L.commit_to_branch("nothing new", paths=["harness.py"]))
            (self.root / "harness.py").write_text("v3\n")
            sha2 = L.commit_to_branch("iteration 2", paths=["harness.py"])
            self.assertEqual(self.git("rev-parse", "harness-loop^"), sha)          # the branch grows on its own tip


if __name__ == "__main__":
    unittest.main()
