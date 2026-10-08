"""resolution.py, the autonomous resolution campaign (2026-10-08): its queue, how it reads a finished engine pass, the
order of its tiers, its daily cap, and the Lean run it builds. No model calls and no subprocesses: everything that would
run is patched."""
import json, sys, tempfile, unittest
from datetime import datetime, timedelta, timezone
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import resolution as R


def _claim(sess, cid, status, sig=None, settles=None, statement="s"):
    v = {"status": status}
    if sig is not None:
        v["novelty"] = {"verdict": "new", "significance": sig}
    if settles is not None:
        v["settles"] = settles
    return {"session": sess, "id": cid, "status": "PROVED", "statement": statement, "proof": "p", "validation": v}


class Base(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        d = Path(self.tmp.name)
        for name, val in (("CAMP", d), ("STATE", d / "state.json"), ("RESULTS", d / "results.jsonl"),
                          ("CONFIG", d / "config.json"), ("LOG", d / "log"), ("REVIEW", d / "REVIEW-NEEDED.md"),
                          ("SCREEN_RESULTS", d / "screen-results.jsonl")):
            p = patch.object(R, name, val)
            p.start()
            self.addCleanup(p.stop)
        self.d = d

    def engine_run(self, ledger) -> Path:
        self.k = getattr(self, "k", 0) + 1
        run = self.d / "runs" / f"20261008-000000-00000{self.k}-erdos99"
        (run / "engine").mkdir(parents=True)
        (run / "engine" / "engine.json").write_text(json.dumps({"ledger": ledger}))
        (run / "state.json").write_text(json.dumps({"statement": "theorem erdos_99 : True := by\n  sorry",
                                                    "statement_source": "formal-conjectures"}))
        (run / "problem.json").write_text(json.dumps({"id": "99", "statement": "Is it true?"}))
        return run


class Classify(Base):
    def test_complete_needs_both_settles_judges(self):
        both = {"settles": True, "answer": "false", "judges": [{"settles": True}, {"settles": True}]}
        run = self.engine_run([_claim("deep", "C1", "validated-new", 3, settles=both, statement="the answer is no")])
        out, info = R.classify(run)
        self.assertEqual((out, info["claim"], info["answer"]), ("complete", "deep/C1", "false"))

    def test_traction_and_none(self):
        run = self.engine_run([_claim("r1s1", "C1", "validated-new", 2), _claim("r1s2", "C1", "validated-new", 1)])
        out, info = R.classify(run)
        self.assertEqual(out, "traction")
        self.assertEqual([c["claim"] for c in info["claims"]], ["r1s1/C1"])
        run2 = self.engine_run([_claim("r1s1", "C1", "validated-new", 1), _claim("r1s2", "C1", "broken")])
        self.assertEqual(R.classify(run2)[0], "none")


class Tiers(Base):
    def test_lean_then_deep_then_a_cut_off_stage_then_the_queue(self):
        cfg = R.load_cfg()
        st = {"problems": {"5": {"next": "deep"}, "6": {"next": "lean"}, "7": {"running": "scout"}}}
        with patch.object(R, "queue", lambda s, c: [8, 9]):
            self.assertEqual(R.next_action(st, cfg), ("lean", 6))
            st["problems"]["6"]["next"] = None
            self.assertEqual(R.next_action(st, cfg), ("deep", 5))
            st["problems"]["5"]["next"] = None
            self.assertEqual(R.next_action(st, cfg), ("scout", 7))
            st["problems"]["7"]["running"] = None
            self.assertEqual(R.next_action(st, cfg), ("scout", 8))
            st["problems"]["7"].update({"running": "scout", "errors": cfg["max_errors"]})   # gave up on it
            self.assertEqual(R.next_action(st, cfg), ("scout", 8))

    def test_the_daily_cap_counts_the_last_24_hours(self):
        now = datetime(2026, 10, 8, 12, tzinfo=timezone.utc)
        for hours, spend in ((1, 10.0), (23, 5.0), (25, 100.0)):
            at = (now - timedelta(hours=hours)).strftime("%Y-%m-%dT%H:%M:%SZ")
            with R.RESULTS.open("a") as f:
                f.write(json.dumps({"at": at, "spend": spend}) + "\n")
        self.assertEqual(R.spent_since(24, now), 15.0)
        self.assertEqual(R.spent_since(168, now), 115.0)


class Queue(Base):
    def test_priority_first_then_least_studied_and_never_a_claimed_or_taken_problem(self):
        ranks = {"problems": [{"id": n, "status": "Unsolved", "partial": {"score": 50}} for n in (1, 2, 3, 4, 5)]
                 + [{"id": 6, "status": "Solved"}]}
        chars = {1: 900, 2: 100, 3: 500, 4: 50, 5: 10}
        fake_root = self.d / "root"
        (fake_root / "atlas-data").mkdir(parents=True)
        (fake_root / "atlas-data" / "rankings.json").write_text(json.dumps(ranks))
        (fake_root / "atlas-data" / "openai-math-2026-10-06.json").write_text(json.dumps(
            {"claimed_resolved": [{"problem": "5", "family": "1"}], "claimed_partial": []}))
        with patch.object(R, "ROOT", fake_root), patch.object(R, "forum_chars", lambda n: chars[n]):
            q = R.queue({"problems": {"2": {}}}, {"priority": [3]})
        self.assertEqual(q, [3, 4, 1])          # 3 by priority; 5 claimed, 2 taken, 6 solved; then least studied


class Lean(Base):
    def test_the_lean_run_is_a_normal_open_problem_run_committed_to_the_chains_direction(self):
        both = {"settles": True, "answer": "false", "judges": [{"settles": True}, {"settles": True}]}
        run = self.engine_run([_claim("deep", "C1", "validated-new", 3, settles=both, statement="no such set exists")])
        with patch.object(R, "ROOT", self.d):
            lean = R.build_lean_run(99, run, "deep/C1", "false")
            cmd = R.lean_cmd(lean, R.load_cfg())
        st = json.loads((lean / "state.json").read_text())
        self.assertEqual(st["discovery"]["decision"]["commit"], "neg")
        self.assertIn("no such set exists", st["discovery"]["best_proof"]["text"])
        self.assertNotIn("benchmark", st)                       # a verified proof belongs in knowledge/ and the Atlas
        self.assertIn("none: the informal proof is the harness's own", st["assistance"][0])
        self.assertIn("--open", cmd)
        self.assertNotIn("--benchmark", cmd)
        self.assertEqual(cmd[cmd.index("--discover") + 1], "on")      # open mode reads the seeded decision

    def test_a_verified_result_is_flagged_for_review(self):
        run = self.engine_run([])
        with patch.object(R, "ROOT", self.d):
            R.flag_for_review(99, run, "RUN-SUMMARY problem=99 exit=0", "deep/C1", run)
        text = R.REVIEW.read_text()
        self.assertIn("independent human review", text)
        self.assertIn("## #99", text)


if __name__ == "__main__":
    unittest.main()
