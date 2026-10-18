"""The self-maintaining Atlas: benchmark aliases resolve to catalogue numbers (atlas_ids.py), and atlas_refresh.py
re-ranks, commits only the Atlas's own paths on main, and pushes, all on timers. A push refused because origin moved is
reconciled when that is safe, and stays on record when it is not. Git runs in throwaway repositories. No model calls."""
import io, json, os, subprocess, sys, tempfile, unittest
from contextlib import redirect_stderr
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


class _Repo(unittest.TestCase):
    """A checkout on main with a local bare remote as origin, in a throwaway directory. No tests of its own."""

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


class Git(_Repo):
    """commit_paths and push against a local bare remote."""

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


class Reconcile(_Repo):
    """A session pushes its branch straight to origin's main, as on 2026-10-15, and the publisher's next push is
    refused. It merges origin/main into local main and pushes once more when that is safe; otherwise it leaves the
    checkout exactly as it was and says why."""

    def setUp(self):
        super().setUp()
        _w(self.repo / ".gitignore", ".result-feed/\ntmp/\n")
        self.run("add", ".gitignore", cwd=self.repo)
        self.run("commit", "-q", "-m", "ignore", cwd=self.repo)
        self.run("push", "-q", "origin", "main", cwd=self.repo)
        self.other = self.repo.parent / "other"
        self.run("clone", "-q", str(self.remote), str(self.other))

    def land(self, path, text, force=False):
        """Another checkout commits `path` and pushes it straight to origin's main."""
        self.run("pull", "-q", "--ff-only", cwd=self.other)
        _w(self.other / path, text)
        self.run("add", *(["-f"] if force else []), path, cwd=self.other)
        self.run("commit", "-q", "-m", f"a session's change to {path}", cwd=self.other)
        self.run("push", "-q", "origin", "HEAD:main", cwd=self.other)

    def publish(self, text):
        """The publisher's own commit: a re-rank."""
        _w(self.repo / "atlas-data" / "rankings.json", text)
        self.assertIn("commit", R.commit_paths(self.repo, R.HARNESS_PATHS, R.COMMIT_MESSAGE))

    def campaign(self, n):
        """The resolution campaign's own commit, made the way resolution.commit makes it."""
        _w(self.repo / "resolution" / "state.json", json.dumps({"problem": n}) + "\n")
        self.run("add", "--", "resolution", cwd=self.repo)
        self.run("commit", "-q", "-m", f"resolution: #{n} Lean verified\n\nCo-Authored-By: x <x@x>", "--", "resolution",
                 cwd=self.repo)

    def remote_main(self):
        return subprocess.run(["git", "--git-dir", str(self.remote), "rev-parse", "main"], capture_output=True,
                              text=True).stdout.strip()

    def assertUntouched(self, res, head, why):
        self.assertFalse(res["pushed"])
        self.assertIn("[rejected]", res["error"])
        self.assertEqual(res["not_reconciled"], why)
        self.assertEqual(self.git("rev-parse", "HEAD"), head)
        self.assertFalse((self.repo / ".git" / "MERGE_HEAD").exists())
        self.assertNotEqual(self.remote_main(), head)

    def test_a_fast_forward_push_is_one_plain_push(self):
        self.publish('{"new": 1}\n')
        with patch.object(R, "reconcile", side_effect=AssertionError("a fast-forward needs no reconcile")):
            self.assertEqual(R.push(self.repo), {"pushed": True})
        self.assertEqual(self.remote_main(), self.git("rev-parse", "HEAD"))
        self.assertEqual(self.git("rev-list", "--merges", "--count", "HEAD"), "0")

    def test_a_refused_push_merges_origin_and_pushes_once_more(self):
        self.land("harness.py", "the session's fix\n")
        self.publish('{"new": 1}\n')
        self.campaign(655)                                             # stuck beside the publisher's on 2026-10-15
        _w(self.repo / "work.py", "someone's unfinished work\n")       # uncommitted work the merge does not touch
        _w(self.repo / "scratch.txt", "untracked\n")
        mine = self.git("rev-parse", "HEAD")
        res = R.push(self.repo)
        self.assertTrue(res["pushed"], res)
        self.assertEqual((res["reconciled"]["behind"], res["reconciled"]["ahead"]), (1, 2))
        self.assertEqual(self.remote_main(), self.git("rev-parse", "HEAD"))
        self.assertEqual(self.git("log", "-1", "--format=%s"), R.MERGE_MESSAGE)
        self.assertEqual(self.git("rev-parse", "HEAD^1"), mine)          # a merge on top: nothing rewritten
        self.assertEqual((self.repo / "harness.py").read_text(), "the session's fix\n")
        self.assertEqual((self.repo / "work.py").read_text(), "someone's unfinished work\n")
        self.assertEqual(self.git("status", "--porcelain"), "M work.py\n?? scratch.txt")

    def test_a_merge_that_would_touch_uncommitted_work_is_not_made(self):
        self.land("work.py", "v2 from a session\n")
        self.publish('{"new": 1}\n')
        _w(self.repo / "work.py", "someone's unfinished work\n")
        head = self.git("rev-parse", "HEAD")
        self.assertUntouched(R.push(self.repo), head, "the merge would touch uncommitted work: work.py")
        self.assertEqual((self.repo / "work.py").read_text(), "someone's unfinished work\n")

    def test_a_merge_in_progress_is_left_alone(self):
        self.land("harness.py", "the session's fix\n")
        self.publish('{"new": 1}\n')
        head = self.git("rev-parse", "HEAD")
        (self.repo / ".git" / "MERGE_HEAD").write_text(head + "\n")
        res = R.push(self.repo)
        (self.repo / ".git" / "MERGE_HEAD").unlink()
        self.assertUntouched(res, head, "MERGE_HEAD present")
        self.assertFalse((self.repo / "harness.py").exists())

    def test_someone_elses_commit_on_local_main_is_not_merged_around(self):
        self.land("harness.py", "the session's fix\n")
        self.publish('{"new": 1}\n')
        _w(self.repo / "work.py", "committed on main, never pushed\n")
        self.run("commit", "-q", "-am", "Fix the cascade", cwd=self.repo)
        head = self.git("rev-parse", "HEAD")
        self.assertUntouched(R.push(self.repo), head,
                             f"1 commit(s) that origin lacks are not automatic: {head[:7]} Fix the cascade")

    def test_automatic_means_the_writers_subject_and_only_the_writers_paths(self):
        self.publish('{"a": 1}\n')
        self.campaign(655)
        _w(self.repo / "work.py", "code\n")
        self.run("commit", "-q", "-am", R.COMMIT_MESSAGE, cwd=self.repo)           # the publisher's subject on code
        _w(self.repo / "resolution" / "config.json", "{}\n")
        self.run("add", "resolution", cwd=self.repo)
        self.run("commit", "-q", "-m", "Tune the campaign", cwd=self.repo)          # the campaign's paths, by hand
        theirs = self.git("rev-parse", "origin/main")
        verdicts = [(c[2], R._automatic(self.repo, c, R.AUTOMATIC, theirs))
                    for c in R._local_commits(self.repo, theirs)]
        self.assertEqual(verdicts, [("Tune the campaign", False), (R.COMMIT_MESSAGE, False),
                                    ("resolution: #655 Lean verified", True), (R.COMMIT_MESSAGE, True)])

    def test_a_merge_that_would_conflict_is_never_started(self):
        self.land("atlas-data/rankings.json", '{"theirs": 1}\n')
        self.publish('{"ours": 1}\n')
        head = self.git("rev-parse", "HEAD")
        self.assertUntouched(R.push(self.repo), head, "the merge would conflict in: atlas-data/rankings.json")
        self.assertEqual(self.git("status", "--porcelain"), "")

    def test_the_pages_passphrase_is_never_merged_over(self):
        _w(self.repo / ".result-feed" / "pages-passphrase", "the real one\n")      # ignored: a merge would clobber it
        self.land(".result-feed/pages-passphrase", "a committed one\n", force=True)
        self.publish('{"new": 1}\n')
        head = self.git("rev-parse", "HEAD")
        self.assertUntouched(R.push(self.repo), head,
                             "the merge would write under .result-feed/: .result-feed/pages-passphrase")
        self.assertEqual((self.repo / ".result-feed" / "pages-passphrase").read_text(), "the real one\n")

    def test_an_ignored_file_is_never_merged_over(self):
        _w(self.repo / "tmp" / "cache.json", "local\n")
        self.land("tmp/cache.json", "theirs\n", force=True)
        self.publish('{"new": 1}\n')
        head = self.git("rev-parse", "HEAD")
        self.assertUntouched(R.push(self.repo), head,
                             "the merge would overwrite untracked or ignored files: tmp/cache.json")
        self.assertEqual((self.repo / "tmp" / "cache.json").read_text(), "local\n")

    def test_an_earlier_reconcile_whose_push_failed_is_merged_around(self):
        self.land("harness.py", "fix 1\n")
        self.publish('{"a": 1}\n')
        self.assertIn("merged", R.reconcile(self.repo))                # merged, and say the push after it failed
        self.land("tests/test_x.py", "fix 2\n")                        # origin moves again before the next cycle
        self.publish('{"a": 2}\n')
        res = R.push(self.repo)
        self.assertTrue(res["pushed"], res)
        self.assertEqual(res["reconciled"]["ahead"], 3)                # two re-ranks and the earlier merge
        self.assertEqual(self.remote_main(), self.git("rev-parse", "HEAD"))
        self.assertEqual((self.repo / "tests" / "test_x.py").read_text(), "fix 2\n")

    def test_when_origin_already_has_every_local_commit_main_catches_up(self):
        # what the 2026-10-15 repair did: a session merged local main into its branch and pushed that to origin
        self.publish('{"a": 1}\n')
        self.run("pull", "-q", "--ff-only", str(self.repo), "main", cwd=self.other)
        self.land("harness.py", "the session's fix\n")
        res = R.push(self.repo)
        self.assertEqual((res["pushed"], res["reason"], res["reconciled"]["ahead"]), (False, "up to date", 0))
        self.assertEqual(self.git("rev-parse", "HEAD"), self.remote_main())
        self.assertEqual(self.git("rev-list", "--merges", "--count", "HEAD"), "0")


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
                        patch.object(R, "push", lambda repo, *a: self.calls.append(("push", repo.name)) or {"pushed": True})]
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

    def test_a_push_that_does_not_get_through_stays_on_record_until_one_does(self):
        # `last` is rewritten every 30-second cycle, so a refusal kept only there was invisible within a minute
        refused = {"pushed": False, "error": "[rejected] (fetch first)",
                   "not_reconciled": "the merge would touch uncommitted work: work.py"}
        results = [refused, refused, {"pushed": True}]
        harness_push = lambda repo, *a: results.pop(0) if repo == self.root else {"pushed": True}
        err, states = io.StringIO(), []
        with patch.object(R, "push", harness_push), patch.object(R, "inputs_signature", return_value="s1"), \
                redirect_stderr(err):
            for k in range(3):
                R.maybe_refresh(self.root, now=10_000 + k * R.COMMIT_EVERY)
                states.append(json.loads(R.STATE.read_text()))
        first, second = states[0]["push_stuck"]["harness"], states[1]["push_stuck"]["harness"]
        self.assertEqual((first["tries"], second["tries"]), (1, 2))
        self.assertEqual(second["since"], first["since"])
        self.assertEqual(second["why"], "[rejected] (fetch first); the merge would touch uncommitted work: work.py")
        self.assertNotIn("site", states[0]["push_stuck"])
        self.assertNotIn("push_stuck", states[2])
        self.assertEqual(err.getvalue().count("the harness push has not got through since"), 2)


if __name__ == "__main__":
    unittest.main()
