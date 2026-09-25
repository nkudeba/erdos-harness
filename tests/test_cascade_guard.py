"""The free specialist cascade: every alternative must close its goal (real Lean part opt-in: DEDUCTIVE_LEAN_TESTS=1).

Unguarded, `first | … | (simp_all) | …` accepts a `simp_all` that only simplifies. The tactics after it never run,
and Lean reports the leftover goal at the enclosing `by`, a line above the hole. `_close_holes_without_model`
attributes errors by line, so it read the hole as closed; the keep-check then failed and reverted the whole pass,
genuine closures included. A replay of 41 saved passes (benchmarks/timesplit/analysis/cascade_replay.py) found
71 holes read as closed and 0 actually closed.
"""
import argparse, os, sys, tempfile, threading, unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import harness as H

# tactics that can succeed while leaving the goal open
MAY_LEAVE_GOALS = {"simp", "simp_all", "norm_num", "aesop", "field_simp", "ring_nf", "simp_arith", "push_cast"}
OLD_CASCADE = "first | omega | (simp_all) | positivity | (norm_num) | (nlinarith) | (decide +kernel) | (aesop)"

# `hyp_a` closes outright; `hyp_c` is the trap: simp_all only strips `+ 0`, and positivity closes it
SKELETON = """theorem erdos_98_hyp_a : ∀ n : ℕ, n + 0 = n := by
  sorry

theorem erdos_98_hyp_c (x : ℝ) (hx : 0 ≤ x) : 0 ≤ x * x + x + 0 := by
  sorry

theorem erdos_98 : True := by
  trivial"""


class CascadeShape(unittest.TestCase):
    def test_every_alternative_that_can_leave_a_goal_is_guarded(self):
        body = H.Harness.CASCADE.strip()
        self.assertTrue(body.startswith("first "))
        alts = [a.strip() for a in body[len("first"):].split("|") if a.strip()]
        self.assertGreater(len(alts), 3)
        for alt in alts:
            head = alt.strip("() ").split(";")[0].split()[0]
            if head in MAY_LEAVE_GOALS:
                self.assertRegex(alt, r";\s*done\)?$", f"`{alt}` can succeed without closing its goal")


class Log:
    def event(self, *a, **k):
        pass


@unittest.skipUnless(os.environ.get("DEDUCTIVE_LEAN_TESTS") == "1", "set DEDUCTIVE_LEAN_TESTS=1 for real Lean checks")
class CascadeInLean(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        h = H.Harness.__new__(H.Harness)
        h.problem = {"id": "98", "statement": "cascade", "tags": []}
        h.state = {}
        h.log = Log()
        h.run_dir = Path(self.tmp.name)
        h.args = argparse.Namespace(no_cascade=False, subgoal_prover=None)
        h.imports, h.libraries = list(H.DEFAULT_IMPORTS) + ["Mathlib.Tactic"], []
        h.lean = H.LeanChecker(H.FORMAL, 600)
        h._lock = threading.Lock()
        h.checks = 0
        self.h = h
        self.frozen = H.statement_prefix("theorem erdos_98 : True := by\n  sorry")

    def tearDown(self):
        self.tmp.cleanup()

    def test_the_old_string_misreads_one_hole_and_reverts_the_other(self):
        self.h.CASCADE = OLD_CASCADE                    # instance attribute shadows the class's fixed string
        out = self.h._close_holes_without_model(SKELETON, self.frozen)
        self.assertEqual(H.hole_count(out), 2, out)     # hyp_a's genuine closure was reverted with hyp_c's false one

    def test_the_guarded_cascade_closes_both(self):
        out = self.h._close_holes_without_model(SKELETON, self.frozen)
        self.assertEqual(H.hole_count(out), 0, out)
        res = self.h.check(out, "closed")
        self.assertTrue(res["ok"], res["errors"][:2])
        self.assertFalse(res["sorries"])


if __name__ == "__main__":
    unittest.main()
