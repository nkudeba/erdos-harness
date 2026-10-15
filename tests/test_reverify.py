"""`harness.py reverify` and `resolution.py reverify-lean` (2026-10-14): a proof a verifier bug left `proved_unverified`
gets its final verification re-run, never a new search. #769's closed residual failed only Comparator, which the audit
had handed the frozen statement's `structure Cube` as a definition hole. No model calls and no Lean: `stage_verify`
and the subprocess are faked."""
import json, sys, tempfile, unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import harness as H
import resolution as R


class FakeHarness:
    """What `cmd_reverify` needs from a Harness: the resumed state, `stage_verify`, `save` and a log."""
    clears = True
    built = []

    def __init__(self, args):
        self.run_dir = Path(args.resume)
        self.problem = json.loads(Path(args.problem).read_text())
        self.state = json.loads((self.run_dir / "state.json").read_text())
        self.imports = list(H.DEFAULT_IMPORTS)
        self.log = type("Log", (), {"event": lambda *a, **k: None})()
        self.args = args
        FakeHarness.built.append(self)

    def stage_verify(self):
        self.state["verify"] = {"all_clear": FakeHarness.clears}
        return self.state["verify"]

    def save(self):
        (self.run_dir / "state.json").write_text(json.dumps(self.state))


class Reverify(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.run = Path(self.tmp.name) / "runs" / "20261014-162417-000000-resolve-lean-erdos769"
        (self.run / "neg").mkdir(parents=True)
        (self.run / "problem.json").write_text(json.dumps({"id": "769", "statement": "Is c(n) >> n^n?"}))
        (self.run / "state.json").write_text(json.dumps({"open_results": {"neg": 2}, "assistance": ["none"]}))
        (self.run / "neg" / "state.json").write_text(json.dumps({
            "statement": "theorem erdos_769_neg : True := by\n  sorry", "proof": "theorem erdos_769_neg : True := trivial",
            "verify": {"all_clear": False}, "outcome": "proved_unverified", "direction": "neg"}))
        FakeHarness.built = []

    def reverify(self, clears=True):
        FakeHarness.clears = clears
        lines = []
        with patch.object(H, "Harness", FakeHarness), patch.object(H, "KNOWLEDGE", Path(self.tmp.name) / "knowledge"), \
                patch.object(H, "emit_run_summary", lambda run_dir, rc: lines.append(rc)):
            rc = H.cmd_reverify(H.build_parser().parse_args(["reverify", "--run", str(self.run)]))
        return rc, lines

    def test_a_proof_that_now_clears_is_recorded_as_proved_and_says_how(self):
        rc, lines = self.reverify(True)
        self.assertEqual((rc, lines), (0, [0]))
        h = FakeHarness.built[0]
        self.assertEqual((h.direction, h.thm_name), ("neg", "erdos_769_neg"))
        self.assertEqual(h.args.audit, "on")
        neg = json.loads((self.run / "neg" / "state.json").read_text())
        self.assertEqual(neg["outcome"], "proved")
        self.assertIn("operator re-verification", neg["assistance"][-1])
        self.assertIn("False -> True", neg["assistance"][-1])
        self.assertEqual(json.loads((self.run / "neg" / "DONE").read_text())["exit"], 0)
        parent = json.loads((self.run / "state.json").read_text())
        self.assertEqual(parent["open_results"], {"neg": 0})
        self.assertEqual(json.loads((self.run / "DONE").read_text())["exit"], 0)
        self.assertTrue((Path(self.tmp.name) / "knowledge" / "open" / "769" / self.run.name / "Erdos769_neg.lean").exists())

    def test_a_proof_that_still_fails_stays_unverified(self):
        rc, lines = self.reverify(False)
        self.assertEqual((rc, lines), (2, [2]))
        self.assertEqual(json.loads((self.run / "neg" / "state.json").read_text())["outcome"], "proved_unverified")
        self.assertFalse((Path(self.tmp.name) / "knowledge" / "open").exists())


class ReverifyLean(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        d = Path(self.tmp.name)
        for name, val in (("CAMP", d), ("STATE", d / "state.json"), ("RESULTS", d / "results.jsonl"),
                          ("CONFIG", d / "config.json"), ("LOG", d / "log"), ("REVIEW", d / "REVIEW-NEEDED.md"),
                          ("FINDINGS", d / "STATEMENT-FINDINGS.md"), ("ROOT", d)):
            p = patch.object(R, name, val)
            p.start()
            self.addCleanup(p.stop)
        self.d = d
        eng = d / "runs" / "eng"
        (eng / "engine").mkdir(parents=True)
        (eng / "engine" / "engine.json").write_text(json.dumps({"ledger": []}))
        self.lean = d / "runs" / "lean"
        self.lean.mkdir()
        complete = {"claim": "deep/C1", "answer": "false", "statement": "c(n) < (n/2+2)^n", "intent": "new-math"}
        R.save_state({"problems": {"769": {"history": [], "status": "lean-partial", "next": None, "run_dir": "runs/eng",
                                           "lean_run": "runs/lean", "complete": complete, "track": "new-math"}}})

    def test_a_reverified_new_math_proof_goes_to_human_review(self):
        (self.lean / "SUMMARY.line").write_text("RUN-SUMMARY problem=769 exit=2 spend=$6.78")

        def fake_run(cmd, **k):
            self.assertEqual(cmd[2:4], ["reverify", "--run"])
            (self.lean / "SUMMARY.line").write_text("RUN-SUMMARY problem=769 exit=0 spend=$6.85")
            return type("P", (), {"returncode": 0})()
        with patch.object(R.subprocess, "run", fake_run), patch.object(R, "record_atlas") as atlas, patch.object(R, "commit"), \
                patch.object(R, "flag_for_review") as review:
            self.assertIn("exit 0", R.reverify_lean(769))
        p = R.load_state()["problems"]["769"]
        self.assertEqual((p["status"], p["history"][-1]["how"]), ("verified", "reverify"))
        review.assert_called_once()
        self.assertIn("re-verified by the operator after an audit fix", atlas.call_args[0][1])
        self.assertIn("awaiting human review", atlas.call_args[0][1])
        row = json.loads(R.RESULTS.read_text().splitlines()[-1])
        self.assertEqual(row["how"], "reverify")
        self.assertEqual(row["spend"], 0.07)          # only what the re-verification added: the daily cap counts rows

    def test_nothing_to_reverify(self):
        self.assertIn("no finished Lean stage", R.reverify_lean(5))


if __name__ == "__main__":
    unittest.main()
