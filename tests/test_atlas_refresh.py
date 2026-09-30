"""The self-maintaining Atlas: benchmark aliases resolve to catalogue numbers (atlas_ids.py), and atlas_refresh.py
re-ranks, commits only the Atlas's own paths on main, and pushes, all on timers. Git runs in throwaway repositories.
No model calls."""
import json, os, subprocess, sys, tempfile, unittest
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import atlas_ids as I
import atlas_refresh as R


def _w(p: Path, text: str):
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(text)


class Aliases(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        res = self.root / "benchmarks" / "timesplit" / "results"
        _w(res / "t.aliases.jsonl", json.dumps({"alias": 82251, "problem": "1213", "run_dir": "runs/x"}) + "\n")
        _w(res / "t.jsonl", json.dumps({"alias": 59388, "problem": "1213", "split": "dev"}) + "\n")
        _w(self.root / "benchmarks" / "deductive" / "masks" / "645.json", json.dumps({"true_problem": "645", "alias_id": "67734"}))
        _w(self.root / "benchmarks" / "timesplit" / "pool.json", json.dumps({"items": [{"problem": "1213", "split": "dev"}]}))

    def tearDown(self):
        self.tmp.cleanup()

    def test_both_benchmarks_resolve_and_real_ids_are_never_remapped(self):
        al = I.benchmark_aliases(self.root)
        self.assertEqual(I.resolve(82251, al)[0], 1213)
        self.assertEqual(I.resolve(59388, al)[1]["split"], "dev")
        self.assertEqual(I.resolve(67734, al), (645, {"problem": 645, "benchmark": "deductive", "split": None}))
        self.assertEqual(I.resolve(1213, al), (1213, None))            # a catalogue number is itself
        self.assertEqual(I.resolve(99999, al), (None, None))           # an unknown synthetic id stays unpublished

    def test_only_an_audited_evidence_directory_counts_as_verified(self):
        ev = self.root / "benchmarks" / "timesplit" / "evidence"
        _w(ev / "1213" / "original" / "AUDIT.json", json.dumps({"verdict": "PASS"}))
        _w(ev / "678-assembled" / "AUDIT.json", json.dumps({"verdict": "PASS"}))   # assembled: not a harness solve
        _w(ev / "990" / "AUDIT.json", json.dumps({"verdict": "FAIL"}))
        self.assertEqual(I.audited_evidence(self.root), {1213})


class Git(unittest.TestCase):
    """commit_paths and push against a local bare remote."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        base = Path(self.tmp.name)
        self.env = {**os.environ, "GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@t", "GIT_COMMITTER_NAME": "t",
                    "GIT_COMMITTER_EMAIL": "t@t"}
        self.remote, self.repo = base / "remote.git", base / "repo"
        run = lambda *a, cwd=base: subprocess.run(["git", *a], cwd=cwd, env=self.env, check=True, capture_output=True)
        run("init", "-q", "--bare", "-b", "main", str(self.remote))
        run("init", "-q", "-b", "main", str(self.repo))
        _w(self.repo / "atlas-data" / "rankings.json", "{}\n")
        _w(self.repo / "work.py", "v1\n")
        run("add", ".", cwd=self.repo)
        run("commit", "-q", "-m", "base", cwd=self.repo)
        run("remote", "add", "origin", str(self.remote), cwd=self.repo)
        run("push", "-q", "-u", "origin", "main", cwd=self.repo)
        self.run = run
        self._env = patch.dict(os.environ, self.env)
        self._env.start()

    def tearDown(self):
        self._env.stop()
        self.tmp.cleanup()

    def git(self, *a):
        return subprocess.run(["git", "-C", str(self.repo), *a], capture_output=True, text=True).stdout.strip()

    def test_commits_only_the_atlas_paths_and_pushes(self):
        _w(self.repo / "atlas-data" / "rankings.json", '{"new": 1}\n')
        _w(self.repo / "work.py", "someone's unfinished work\n")          # must stay uncommitted
        c = R.commit_paths(self.repo, ["atlas-data/rankings.json", "atlas-data/briefs"], "Atlas: refresh")
        self.assertIn("commit", c)
        self.assertEqual(self.git("show", "--name-only", "--format=", "HEAD"), "atlas-data/rankings.json")
        self.assertIn("M work.py", self.git("status", "--short"))
        self.assertEqual(R.push(self.repo), {"pushed": True})
        self.assertEqual(R.push(self.repo), {"pushed": False, "reason": "up to date"})
        self.assertEqual(R.commit_paths(self.repo, ["atlas-data/rankings.json"], "again"), {"skipped": "nothing changed"})

    def test_never_commits_off_main_or_mid_merge(self):
        _w(self.repo / "atlas-data" / "rankings.json", '{"x": 2}\n')
        self.run("checkout", "-q", "-b", "feature", cwd=self.repo)
        self.assertIn("not main", R.commit_paths(self.repo, ["atlas-data/rankings.json"], "m")["skipped"])
        self.run("checkout", "-q", "main", cwd=self.repo)
        (self.repo / ".git" / "MERGE_HEAD").write_text("0" * 40)
        self.assertEqual(R.commit_paths(self.repo, ["atlas-data/rankings.json"], "m"), {"skipped": "MERGE_HEAD present"})


class Timers(unittest.TestCase):
    """maybe_refresh re-ranks on a changed input at most every RERANK_EVERY, commits every COMMIT_EVERY, deploys
    every DEPLOY_EVERY, and never raises."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        (self.root / "erdos-atlas").mkdir()
        self._state = patch.object(R, "STATE", self.root / ".result-feed" / "atlas-refresh.json")
        self._state.start()
        self.calls = []
        self.patches = [patch.object(R, "rerank", lambda root: self.calls.append("rerank") or {"ok": True}),
                        patch.object(R, "commit_paths", lambda repo, paths, msg: self.calls.append(("commit", repo.name)) or {"commit": "abc"}),
                        patch.object(R, "push", lambda repo: self.calls.append(("push", repo.name)) or {"pushed": True})]
        for p in self.patches:
            p.start()

    def tearDown(self):
        for p in self.patches:
            p.stop()
        self._state.stop()
        self.tmp.cleanup()

    def test_first_call_does_everything_then_only_on_change_and_timers(self):
        with patch.object(R, "inputs_signature", return_value="s1"):
            R.maybe_refresh(self.root, now=10_000)
        self.assertEqual(self.calls, ["rerank", ("commit", self.root.name), ("push", self.root.name),
                                      ("commit", "erdos-atlas"), ("push", "erdos-atlas")])
        self.calls.clear()
        with patch.object(R, "inputs_signature", return_value="s1"):
            R.maybe_refresh(self.root, now=10_060)                         # nothing changed, timers not due
        self.assertEqual(self.calls, [])
        with patch.object(R, "inputs_signature", return_value="s2"):
            R.maybe_refresh(self.root, now=10_100)                         # changed, but inside RERANK_EVERY
            self.assertEqual(self.calls, [])
            R.maybe_refresh(self.root, now=10_000 + R.RERANK_EVERY)        # changed and due
        self.assertEqual(self.calls, ["rerank"])
        self.calls.clear()
        with patch.object(R, "inputs_signature", return_value="s2"):
            R.maybe_refresh(self.root, now=10_000 + R.DEPLOY_EVERY)        # both commit timers due
        self.assertIn(("push", "erdos-atlas"), self.calls)

    def test_an_error_is_recorded_not_raised(self):
        with patch.object(R, "inputs_signature", side_effect=RuntimeError("disk")):
            out = R.maybe_refresh(self.root, now=1)
        self.assertIn("RuntimeError", out["error"])


if __name__ == "__main__":
    unittest.main()
