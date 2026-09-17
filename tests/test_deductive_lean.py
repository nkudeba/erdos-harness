"""Real-Lean smoke test of the deductive loop's skeleton mechanics (opt-in: DEDUCTIVE_LEAN_TESTS=1).

The mocked tests in test_deductive_mode.py check the control flow; this one checks that what the loop
writes is Lean the kernel accepts: a residual skeleton compiles with its hypothesis holes, the free
specialist cascade discharges elementary hypotheses, and a spliced proof (`namespace <name>_ns` plus
`exact <name>_ns.<name>`) compiles. No model calls; three or four `lake env lean` compiles.
"""
import argparse, os, sys, tempfile, threading, unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import harness as H


class Log:
    def event(self, *a, **k):
        pass


SKELETON = """theorem erdos_99_hyp_a : ∀ n : ℕ, n + 0 = n := by
  sorry

theorem erdos_99_hyp_b : ∀ n : ℕ, 0 + n = n := by
  sorry

theorem erdos_99 : ∀ n : ℕ, n + 0 = n ∧ 0 + n = n := by
  intro n
  exact ⟨erdos_99_hyp_a n, erdos_99_hyp_b n⟩"""


@unittest.skipUnless(os.environ.get("DEDUCTIVE_LEAN_TESTS") == "1", "set DEDUCTIVE_LEAN_TESTS=1 for real Lean checks")
class SkeletonMechanicsInLean(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        h = H.Harness.__new__(H.Harness)
        h.problem = {"id": "99", "statement": "smoke", "tags": []}
        h.state = {}
        h.log = Log()
        h.run_dir = Path(self.tmp.name)
        h.args = argparse.Namespace(no_cascade=False, subgoal_prover=None)
        h.imports, h.libraries = list(H.DEFAULT_IMPORTS), []
        h.lean = H.LeanChecker(H.FORMAL, 420)
        h._lock = threading.Lock()
        h.checks = 0
        self.h = h
    def tearDown(self):
        self.tmp.cleanup()

    def test_skeleton_compiles_cascade_closes_and_splice_compiles(self):
        frozen = H.statement_prefix("theorem erdos_99 : ∀ n : ℕ, n + 0 = n ∧ 0 + n = n := by\n  sorry")
        res = self.h.check(SKELETON, "skeleton")
        self.assertTrue(res["ok"], res["errors"][:2])
        self.assertTrue(res["sorries"])                  # LeanChecker reports sorries as a flag
        parsed = H.parse_residual(SKELETON, 99)
        self.assertEqual(parsed["metric"]["open_conjectures"], 2)
        self.assertTrue(parsed["glue_sorry_free"])
        # the free cascade should discharge both elementary hypotheses: no conjecture survives
        closed = self.h._close_holes_without_model(SKELETON, frozen)
        self.assertEqual(H.hole_count(closed), 0, closed)
        fin = self.h.check(closed, "closed")
        self.assertTrue(fin["ok"] and not fin["sorries"], fin["errors"][:2])
        # a spliced child proof compiles and leaves exactly the other hypothesis open
        spliced = H.splice_hypothesis(SKELETON, "erdos_99_hyp_a",
                                      "theorem erdos_99_hyp_a : ∀ n : ℕ, n + 0 = n := by\n  intro n\n  simp")
        res2 = self.h.check(spliced, "spliced")
        self.assertTrue(res2["ok"], res2["errors"][:2])
        self.assertTrue(res2["sorries"])
        p2 = H.parse_residual(spliced, 99)
        self.assertEqual([h["name"] for h in p2["hypotheses"] if h["open"]], ["erdos_99_hyp_b"])


if __name__ == "__main__":
    unittest.main()
