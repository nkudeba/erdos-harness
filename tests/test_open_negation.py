"""The `--open` negation, built from the frozen statement's SOURCE text with no model call (real Lean part opt-in:
DEDUCTIVE_LEAN_TESTS=1; ERDOS_LEAN_PROJECT names a built Lean project when the checkout has none, e.g. in a git worktree).

`_negate_statement` used to read the theorem's type from a `#check` in `infos`, which a plain check always leaves empty,
so it never fired: all 65 `--open` runs on disk paid a model call for their negation. Reading that `#check` with
positions would not have been safe either. Lean prints the true `∀ n : ℕ, (n : ℤ) - 1 < n` as `∀ (n : ℕ), ↑n - 1 < ↑n`,
which elaborates in ℕ, and Lean proves the negation built from that text. So the negation is now built from the source,
and kept only when Lean confirms, beside the positive theorem, that its type is `Not` of the frozen theorem's
(NEGATION_GUARD). Anything else falls back to the model, as before.
"""
import argparse, os, sys, tempfile, threading, unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import harness as H

CAST = "theorem erdos_98 : ∀ n : ℕ, (n : ℤ) - 1 < n := by\n  sorry"
# the pre-2026-10-15 shape, from the printed type: `↑n` with no target type elaborates in ℕ, where it is false at 0
PRINTED = "theorem erdos_98_neg : ¬ (∀ (n : ℕ), ↑n - 1 < ↑n) := by\n  sorry"

PRELUDE = """open Filter
open scoped Topology

scoped[EuclideanGeometry] notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

variable {X : Type*} [MetricSpace X]

/-- Smallest set containing `2, 3`. -/
def Erdos98.hofSet : Set ℕ :=
  {n | ∀ T : Set ℕ, 2 ∈ T → 3 ∈ T → n ∈ T}

"""
PLAIN = PRELUDE + """theorem erdos_98 :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℕ in atTop,
      c * (x : ℝ) ≤ ((Erdos98.hofSet ∩ Set.Icc 1 x).ncard : ℝ) := by
  sorry"""

BINDERS = """theorem erdos_98 (n : ℕ) (hn : 2 < n) :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
      (4 : ℚ) / (n : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ) := by
  sorry"""

# a universe-polymorphic statement with a def prelude: the plain `example : A = ¬ B := rfl` fails on it
UNIVERSES = """def Erdos98.Small {X : Type*} (s : Finset X) : Prop := s.card ≤ 3

theorem erdos_98 {X : Type*} [DecidableEq X] ⦃s : Finset X⦄ (hs : s.Nonempty) :
    Erdos98.Small s ∨ 3 < s.card := by
  sorry"""

# a section variable the statement uses: the source text negates to `∀ m, ¬ (m + 0 = m)`, which the guard must refuse
USED_VARIABLE = """variable (m : ℕ)

theorem erdos_98 : m + 0 = m := by
  sorry"""


class Log:
    def __init__(self):
        self.events = []

    def event(self, stage, event, **kw):
        self.events.append((stage, event, kw))


def _harness(tmp: str) -> H.Harness:
    h = H.Harness.__new__(H.Harness)
    h.problem = {"id": "98", "statement": "negation", "tags": []}
    h.state, h.log, h.run_dir = {}, Log(), Path(tmp)
    h.args = argparse.Namespace(no_cascade=False, subgoal_prover=None)
    h.imports, h.libraries = list(H.DEFAULT_IMPORTS), []
    h._lock, h.checks = threading.Lock(), 0
    return h


def _refusals(h) -> list[dict]:
    return [kw for _, ev, kw in h.log.events if ev == "negation_source_refused"]


class SourceNegation(unittest.TestCase):
    """What `source_negation` builds from the text (no Lean)."""

    def test_a_plain_statement_keeps_its_prelude_verbatim(self):
        neg, decl = H.source_negation(PLAIN, "erdos_98")
        self.assertEqual(neg, PRELUDE + "theorem erdos_98_neg :\n    ¬ (∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℕ in atTop,\n"
                                        "      c * (x : ℝ) ≤ ((Erdos98.hofSet ∩ Set.Icc 1 x).ncard : ℝ)) := by\n  sorry")
        self.assertEqual(decl, PLAIN[len(PRELUDE):])

    def test_binders_before_the_colon_become_a_forall(self):
        neg, _ = H.source_negation(BINDERS, "erdos_98")
        self.assertTrue(neg.startswith("theorem erdos_98_neg :\n    ¬ (∀ (n : ℕ) (hn : 2 < n),\n      ∃ x y z : ℕ,"), neg)
        self.assertTrue(neg.endswith("1 / (z : ℚ)) := by\n  sorry"), neg)

    def test_the_cast_statement_keeps_its_source_text(self):
        neg, _ = H.source_negation(CAST, "erdos_98")
        self.assertEqual(neg, "theorem erdos_98_neg :\n    ¬ (∀ n : ℕ, (n : ℤ) - 1 < n) := by\n  sorry")

    def test_comments_are_dropped_and_cannot_swallow_the_brackets(self):
        # the old code cut at the first "theorem " anywhere, the docstring's included
        pos = ("/-- The theorem below is Erdős #98. -/\n"
               "theorem erdos_98 (n : ℕ) -- the size\n"
               "    (hn : 2 < n) : -- a hypothesis\n"
               "    ∃ m, n < m -- the witness\n"
               "    := by\n  sorry -- open")
        neg, decl = H.source_negation(pos, "erdos_98")
        self.assertEqual(neg, "/-- The theorem below is Erdős #98. -/\ntheorem erdos_98_neg :\n"
                              "    ¬ (∀ (n : ℕ)\n    (hn : 2 < n),\n      ∃ m, n < m) := by\n  sorry")
        self.assertTrue(decl.startswith("theorem erdos_98 (n : ℕ) -- the size"))

    def test_strings_are_kept_and_hide_no_comment(self):
        neg, _ = H.source_negation('theorem erdos_98 : "a--b".length = 4 := by\n  sorry', "erdos_98")
        self.assertIn('¬ ("a--b".length = 4)', neg)

    def test_attributes_stay_with_the_positive_theorem_and_universes_carry_over(self):
        pos = "@[simp]\ntheorem erdos_98.{u} {X : Type u} (x : X) : x = x := by\n  sorry"
        neg, decl = H.source_negation(pos, "erdos_98")
        self.assertEqual(neg, "theorem erdos_98_neg.{u} :\n    ¬ (∀ {X : Type u} (x : X),\n      x = x) := by\n  sorry")
        self.assertEqual(decl, pos)

    def test_an_imports_directive_inside_the_theorem_is_carried(self):
        # `compose` honours a directive only at the start of a line
        pos = "theorem erdos_98 :\n-- IMPORTS: Mathlib.Data.Set.Card\n    Set.ncard ({1} : Set ℕ) = 1 := by\n  sorry"
        self.assertEqual(H.explicit_imports(pos), ["Mathlib.Data.Set.Card"])
        neg, _ = H.source_negation(pos, "erdos_98")
        self.assertIn("Mathlib.Data.Set.Card", H.explicit_imports(neg))
        self.assertTrue(neg.startswith("-- IMPORTS: Mathlib.Data.Set.Card\ntheorem erdos_98_neg :"), neg)

    def test_shapes_it_will_not_rewrite(self):
        cases = {
            "attached in": "open Real in\ntheorem erdos_98 : π > 3 := by\n  sorry",
            "in on the line": "open Real in theorem erdos_98 : π > 3 := by\n  sorry",
            "something after": "namespace Foo\ntheorem erdos_98 : True := by\n  sorry\nend Foo",
            "a command after": "theorem erdos_98 : True := by\n  sorry\ntheorem other : True := by\n  sorry",
            "not a sorry": "theorem erdos_98 : True := by\n  trivial",
            "twice": "theorem erdos_98 : True := by\n  sorry\ntheorem erdos_98 : True := by\n  sorry",
            "already negated": "theorem erdos_98_neg : False := by\n  sorry\ntheorem erdos_98 : True := by\n  sorry",
            "unbalanced": "theorem erdos_98 (n : ℕ)) : True := by\n  sorry",
            "no theorem": "def erdos_98 : Prop := True",
        }
        for what, pos in cases.items():
            with self.subTest(what):
                with self.assertRaises(ValueError):
                    H.source_negation(pos, "erdos_98")

    def test_the_guard_names_root_constants(self):
        guard = H.NEGATION_GUARD.format(neg="erdos_98_neg", pos="erdos_98")
        self.assertIn("@_root_.Eq Prop (type_of% @erdos_98_neg) (_root_.Not (type_of% @erdos_98))", guard)
        self.assertTrue(guard.startswith("example : (fun (_ : "))       # rfl unifies universes in the header


class NegateStatement(unittest.TestCase):
    """`_negate_statement` around a fake Lean."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.h = _harness(self.tmp.name)
        self.calls = []

    def _lean(self, ok: bool):
        def check(body, name, positions=False):
            self.calls.append((name, body))
            return {"ok": ok, "timeout": False, "errors": [] if ok else ["line 12:2: Type mismatch\n  rfl"],
                    "warnings": [], "infos": [], "sorries": True, "raw": "", "body": body}
        self.h.check = check

    def test_a_guarded_negation_needs_no_model_call(self):
        self._lean(True)
        self.h.ask = lambda *a, **k: self.fail("asked the model")
        neg = self.h._negate_statement(PLAIN)
        self.assertEqual(neg, H.source_negation(PLAIN, "erdos_98")[0])
        [(name, body)] = self.calls
        self.assertEqual(name, "negation-guard")
        # the negation exactly as frozen, then the positive theorem as written, then the guard
        self.assertTrue(body.startswith(neg + "\n\n" + PLAIN[len(PRELUDE):] + "\n\n"))
        self.assertTrue(body.endswith(H.NEGATION_GUARD.format(neg="erdos_98_neg", pos="erdos_98")))
        self.assertEqual(_refusals(self.h), [])

    def test_a_failed_guard_falls_back(self):
        self._lean(False)
        self.assertIsNone(self.h._negate_statement(BINDERS))
        [refused] = _refusals(self.h)
        self.assertEqual(refused["reason"], "the Lean guard failed")
        self.assertIn("Type mismatch", refused["first_error"])

    def test_a_shape_it_will_not_rewrite_costs_no_compile(self):
        self._lean(True)
        self.assertIsNone(self.h._negate_statement("open Real in\ntheorem erdos_98 : π > 3 := by\n  sorry"))
        self.assertEqual(self.calls, [])
        self.assertIn("in", _refusals(self.h)[0]["reason"])


class Stop(Exception):
    pass


class RunOpenRecordsThePath(unittest.TestCase):
    """The run says which path produced its negation: `negation_source` in state, `negation=` on `open/frozen_both`."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        h = self.h = _harness(self.tmp.name)
        h.state = {"statement": BINDERS}
        h.stage_formalize = h.stage_assess = lambda: None
        h.stage_discover = lambda: (_ for _ in ()).throw(Stop())     # stop right after both statements are frozen
        self.asked = []

    def _run(self):
        with self.assertRaises(Stop):
            self.h.run_open()
        [both] = [kw for _, ev, kw in self.h.log.events if ev == "frozen_both"]
        return both

    def test_source(self):
        self.h._negate_statement = lambda pos: "theorem erdos_98_neg : ¬ True := by\n  sorry"
        self.h.ask = lambda *a, **k: self.asked.append(a)
        self.assertEqual(self._run()["negation"], "source")
        self.assertEqual(self.h.state["negation_source"], "source")
        self.assertEqual(self.asked, [])

    def test_model(self):
        self.h._negate_statement = lambda pos: None
        self.h.ask = lambda *a, **k: self.asked.append(a) or "```lean\ntheorem erdos_98_neg : ¬ True := by\n  sorry\n```"
        self.h.check = lambda body, name, positions=False: {"ok": True}
        self.assertEqual(self._run()["negation"], "model")
        self.assertEqual(self.h.state["negation_source"], "model")
        self.assertEqual(len(self.asked), 1)


def _lean_project() -> Path:
    return Path(os.environ.get("ERDOS_LEAN_PROJECT") or H.FORMAL)


@unittest.skipUnless(os.environ.get("DEDUCTIVE_LEAN_TESTS") == "1", "set DEDUCTIVE_LEAN_TESTS=1 for real Lean checks")
class NegationInLean(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        proj = _lean_project()
        self._saved = (H.FORMAL, H.MATHLIB_SRC, H._INDEX, dict(H._decl_cache))
        if proj != H.FORMAL:                       # a worktree: point the index and module checks at the built project
            H.FORMAL, H.MATHLIB_SRC = proj, proj / ".lake" / "packages" / "mathlib" / "Mathlib"
            H._INDEX, H._decl_cache = H.DeclIndex(), {}
        self.h = _harness(self.tmp.name)
        self.h.lean = H.LeanChecker(proj, 600)

    def tearDown(self):
        H.FORMAL, H.MATHLIB_SRC, H._INDEX, cache = self._saved
        H._decl_cache.clear()
        H._decl_cache.update(cache)
        self.tmp.cleanup()

    def test_the_cast_statement_is_negated_from_source_and_the_printed_text_is_refused(self):
        neg = self.h._negate_statement(CAST)
        self.assertEqual(neg, H.source_negation(CAST, "erdos_98")[0], self.h.log.events)
        guard = H.NEGATION_GUARD.format(neg="erdos_98_neg", pos="erdos_98")
        res = self.h.check(f"{PRINTED}\n\n{CAST}\n\n{guard}", "negation-printed")
        self.assertFalse(res["ok"])
        self.assertEqual(len(res["errors"]), 1, res["errors"])      # the printed negation compiles; the guard does not
        self.assertIn("mismatch", res["errors"][0])

    def test_universes_are_accepted_and_a_used_variable_is_refused(self):
        self.assertEqual(self.h._negate_statement(UNIVERSES), H.source_negation(UNIVERSES, "erdos_98")[0],
                         self.h.log.events)
        self.assertIsNone(self.h._negate_statement(USED_VARIABLE))
        self.assertEqual(_refusals(self.h)[-1]["reason"], "the Lean guard failed")


if __name__ == "__main__":
    unittest.main()
