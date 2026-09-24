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


@unittest.skipUnless(os.environ.get("DEDUCTIVE_LEAN_TESTS") == "1", "set DEDUCTIVE_LEAN_TESTS=1 for real Lean checks")
class CircularityProbeInLean(unittest.TestCase):
    """The free layer of the circular-premise guard: Lean closes a restatement of the target, and does NOT close
    the masked #275 premise (a translation), which is why the judge exists."""
    def setUp(self):
        sys.path.insert(0, str(Path(__file__).resolve().parent))
        import test_deductive_mode as T
        self.T = T
        self.tmp = tempfile.TemporaryDirectory()
        h = H.Harness.__new__(H.Harness)
        h.problem, h.state, h.log = {"id": "80317", "statement": "s", "tags": []}, {}, Log()
        h.run_dir = Path(self.tmp.name)
        h.args = argparse.Namespace(no_cascade=False, subgoal_prover=None)
        h.imports, h.libraries = list(H.DEFAULT_IMPORTS), []
        h.lean = H.LeanChecker(H.FORMAL, 420)
        h._lock, h.checks = threading.Lock(), 0
        self.h = h
    def tearDown(self):
        self.tmp.cleanup()

    def test_fixture_restatement_and_translation(self):
        T, fz = self.T, H.statement_prefix(self.T.ROOT_275)
        res = self.h.check(T.CVE_SKELETON, "cve-skeleton")
        self.assertTrue(res["ok"], res["errors"][:2])                    # target ⇐ premise really compiles
        restated = ("∀ (m : ℕ) (u : Fin m → ℤ) (q : Fin m → ℕ), (∀ j, 0 < q j) → (∃ t : ℤ, ∀ k : ℕ, k < 2 ^ m → "
                    "∃ j : Fin m, (q j : ℤ) ∣ (t + (k : ℤ) - u j)) → ∀ z : ℤ, ∃ j : Fin m, (q j : ℤ) ∣ (z - u j)")
        res = self.h.check(H.circularity_probe_source(T.CVE_SKELETON, fz, restated), "circ-restated")
        self.assertTrue(res["ok"] and not res["sorries"], res["errors"][:2])
        cve = H.parse_residual(T.CVE_SKELETON, 80317, main="erdos_80317")["hypotheses"][0]["statement"]
        res = self.h.check(H.circularity_probe_source(T.CVE_SKELETON, fz, cve), "circ-cve")
        self.assertFalse(res["ok"])


@unittest.skipUnless(os.environ.get("DEDUCTIVE_LEAN_TESTS") == "1", "set DEDUCTIVE_LEAN_TESTS=1 for real Lean checks")
class TimeoutLeavesNoOrphan(unittest.TestCase):
    def test_timed_out_lean_is_killed(self):
        import subprocess, time
        with tempfile.TemporaryDirectory() as tmp:
            dest = Path(tmp) / "orphan-probe-3141.lean"
            r = H.LeanChecker(H.FORMAL, 3).check("import Mathlib.Tactic\nexample : 1 = 1 := rfl", dest)
            self.assertTrue(r["timeout"])
            time.sleep(2)
            self.assertEqual(subprocess.run(["pgrep", "-f", "orphan-probe-3141"], capture_output=True, text=True).stdout, "")


@unittest.skipUnless(os.environ.get("DEDUCTIVE_LEAN_TESTS") == "1", "set DEDUCTIVE_LEAN_TESTS=1 for real Lean checks")
class RefinementProbeInLean(unittest.TestCase):
    """The refinement check's free layer in real Lean: H implies its own subcase (forward only), while a literal
    restatement goes both ways. Only the second may be refused without the judge."""
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        h = H.Harness.__new__(H.Harness)
        h.problem, h.state, h.log = {"id": "99", "statement": "s", "tags": []}, {}, Log()
        h.run_dir = Path(self.tmp.name)
        h.args = argparse.Namespace(no_cascade=False, subgoal_prover=None)
        h.imports, h.libraries = list(H.DEFAULT_IMPORTS), []
        h.lean = H.LeanChecker(H.FORMAL, 420)
        h._lock, h.checks = threading.Lock(), 0
        self.h = h
    def tearDown(self):
        self.tmp.cleanup()

    def _derives(self, premise, goal, tag):
        tac = "\n  ".join(["first"] + [f"| {t}" for t in H.REFINEMENT_TACTICS])
        src = f"def good (n : ℕ) : Prop := n = n\n\ntheorem refinement_probe (hH : {premise}) : {goal} := by\n  {tac}"
        r = self.h.check(src, tag)
        return r["ok"] and not r["sorries"]

    def test_subcase_is_one_way_and_restatement_both_ways(self):
        whole = "∀ n : ℕ, n % 24 = 1 → good n"
        subcase = "∀ n : ℕ, n % 24 = 1 → n % 5 = 1 → good n"
        self.assertTrue(self._derives(whole, subcase, "sub-fwd"))
        self.assertFalse(self._derives(subcase, whole, "sub-bwd"))
        self.assertTrue(self._derives(whole, whole, "same-fwd") and self._derives(whole, whole, "same-bwd"))
