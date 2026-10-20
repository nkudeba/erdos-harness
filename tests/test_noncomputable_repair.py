"""The free `noncomputable` repair (real Lean part opt-in: DEDUCTIVE_LEAN_TESTS=1; ERDOS_LEAN_PROJECT names a built Lean
project when the checkout has none).

Lean's error names its own fix ("consider marking it as 'noncomputable'"), yet seven skeletons on disk were rejected
for it, six after spending a repair round on it. A dev item's Lean stage (2026-10-20) ended on it twice: the plan's
repair added the keyword and broke something else, and the next plan dropped it again. `Harness.check` now marks the
definition itself, and a skeleton is re-checked against the frozen text after any such repair."""
import argparse, os, sys, tempfile, threading, unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import harness as H

IMPORTS = list(H.DEFAULT_IMPORTS) + ["Mathlib.Tactic"]
BODY = """open Set

/-- the top of a set of integers -/
def top (s : Set ℤ) : ℤ := sSup s

private def top2 (s : Set ℤ) : ℤ :=
  sSup s + 1

theorem erdos_98_hyp_a : top {0} = 0 := by
  sorry

theorem erdos_98 : True := by
  trivial
"""


def composed_line(body: str, body_line: int) -> int:
    inv = {b: c for c, b in H.compose_line_map(body, IMPORTS).items()}
    return inv[body_line]


def err(body: str, body_line: int) -> str:
    return (f"line {composed_line(body, body_line)}:4: failed to compile definition, consider marking it as "
            "'noncomputable' because it depends on 'Int.instConditionallyCompleteLinearOrder', which is 'noncomputable'")


class MarkNoncomputable(unittest.TestCase):
    def test_marks_each_named_definition_and_nothing_else(self):
        out = H.mark_noncomputable(BODY, [err(BODY, 4), err(BODY, 6)], IMPORTS)
        self.assertIn("\nnoncomputable def top (s : Set ℤ)", out)
        self.assertIn("\nprivate noncomputable def top2", out)        # visibility stays before the keyword
        self.assertIn("\ntheorem erdos_98_hyp_a", out)                 # a theorem is never touched
        self.assertEqual(H.mark_noncomputable(out, [err(out, 4)], IMPORTS), out)   # never marked twice

    def test_an_error_inside_a_definition_body_marks_its_head(self):
        out = H.mark_noncomputable(BODY, [err(BODY, 7)], IMPORTS)       # the error points at the body line
        self.assertIn("private noncomputable def top2", out)
        self.assertNotIn("noncomputable def top (", out)

    def test_other_errors_and_theorem_lines_change_nothing(self):
        self.assertEqual(H.mark_noncomputable(BODY, ["line 12:2: unsolved goals"], IMPORTS), BODY)
        self.assertEqual(H.mark_noncomputable(BODY, [err(BODY, 9)], IMPORTS), BODY)   # a theorem's line


class Log:
    def __init__(self):
        self.events = []

    def event(self, stage, event, **kw):
        self.events.append((stage, event, kw))


@unittest.skipUnless(os.environ.get("DEDUCTIVE_LEAN_TESTS") == "1", "set DEDUCTIVE_LEAN_TESTS=1 for real Lean checks")
class InLean(unittest.TestCase):
    def test_check_repairs_the_definition_and_keeps_the_repaired_body(self):
        with tempfile.TemporaryDirectory() as d:
            h = H.Harness.__new__(H.Harness)
            h.problem, h.state, h.log, h.run_dir = {"id": "98", "statement": "x", "tags": []}, {}, Log(), Path(d)
            h.args = argparse.Namespace(no_cascade=False, subgoal_prover=None)
            h.imports, h.libraries = list(IMPORTS), []
            h.lean = H.LeanChecker(Path(os.environ.get("ERDOS_LEAN_PROJECT") or H.FORMAL), 600)
            h._lock, h.checks = threading.Lock(), 0
            res = h.check(BODY, "nc")
            self.assertTrue(res["ok"], res["errors"])
            self.assertIn("noncomputable def top (", res["body"])
            self.assertIn("private noncomputable def top2", res["body"])
            self.assertTrue(any(e[1] == "noncomputable_repair" and e[2]["ok"] for e in h.log.events))
            final = h.check(BODY, "final-verify")                     # final verification is never repaired
            self.assertFalse(final["ok"])


if __name__ == "__main__":
    unittest.main()
