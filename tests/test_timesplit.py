"""The time-split benchmark's parsing, splitting and scoring rules (benchmarks/timesplit/).

No network and no model calls: every source is a fixture. What must never regress is the contamination
boundary -- no docstring, comment or problem number reaches a frozen statement -- and the scoring rule that a
verified proof of the WRONG direction is flagged, never counted."""
import importlib.util, json, tempfile, unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("timesplit", ROOT / "benchmarks" / "timesplit" / "timesplit.py")
T = importlib.util.module_from_spec(spec)
spec.loader.exec_module(T)

FC = '''/-
Copyright 2026 The Formal Conjectures Authors.
-/
module
public import FormalConjecturesUtil
/-!
# Erdős Problem 884
*References:*
- [erdosproblems.com/884](https://www.erdosproblems.com/884)
- [Tao25](https://terrytao.wordpress.com/wp-content/uploads/2025/09/erdos-884.pdf)
- [La26] D. Larsen, [A disproof](https://arxiv.org/abs/2607.01234) (2026).
-/
@[expose] public section
open Finset
namespace Erdos884
/-- The pairwise sum. -/
noncomputable abbrev pairSum (n : ℕ) : ℝ :=
    ∑ i ∈ range n, (i : ℝ)
/-- An unrelated helper that must not be pulled in. -/
def unused (n : ℕ) : ℕ := n + 1
/-- The target proposition; this was DISPROVED by Larsen [La26]. -/
def Erdos884Prop : Prop :=
    ∀ n : ℕ, pairSum n ≤ n ^ 2   -- a comment that must vanish
/--
Does it hold? This conjecture has been **disproved** by Larsen [La26].
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/x/y/blob/main/Main.lean#L45"]
theorem erdos_884 : answer(False) ↔ Erdos884Prop := by
  sorry
/-- A variant. -/
@[category research open, AMS 11]
theorem erdos_884.variants.weak : answer(sorry) ↔ ∀ n : ℕ, pairSum n ≤ 2 * n ^ 2 := by
  sorry
'''


class ParseFormalConjectures(unittest.TestCase):
    def test_answer_is_stripped_and_nothing_leaks(self):
        fc = T.parse_fc(FC, 884)
        self.assertIsNone(fc.get("error"))
        self.assertEqual((fc["form"], fc["answer"], fc["category"]), ("answer-iff", False, "research solved"))
        stmt = T.frozen_statement(fc, 54321)
        self.assertIn("theorem erdos_54321 :", stmt)
        self.assertIn("noncomputable abbrev pairSum", stmt)          # needed transitively through the Prop def
        self.assertIn("def TSProp : Prop", stmt)                      # Erdos884Prop renamed
        self.assertNotIn("unused", stmt)                              # not needed, not included
        for leak in ("884", "Erdos", "disproved", "DISPROVED", "Larsen", "comment", "answer("):
            self.assertNotIn(leak, stmt)
        self.assertTrue(stmt.rstrip().endswith(":= by\n  sorry"))
        self.assertIn("open Finset", stmt)
        self.assertEqual(fc["refs"]["La26"]["arxiv"], ["2607.01234"])

    def test_reverse_answer_form(self):
        src = "theorem erdos_7 : (∀ n : ℕ, n = n) ↔ answer(True) := by\n  sorry\n"
        fc = T.parse_fc(src, 7)
        self.assertEqual((fc["answer"], fc["prop"]), (True, "(∀ n : ℕ, n = n)"))

    def test_value_questions_are_refused(self):
        fc = T.parse_fc("theorem erdos_5 : Nat.succ 3 = answer(sorry) := by\n  sorry\n", 5)
        self.assertIn("non-boolean", fc["error"])

    def test_assertion_takes_its_truth_from_the_category(self):
        src = "/-- The claim. -/\n@[category research solved, AMS 5]\ntheorem erdos_9 (N : ℕ) : N ≤ N + 1 := by\n  sorry\n"
        fc = T.parse_fc(src, 9)
        self.assertEqual((fc["form"], fc["answer"], fc["binders"], fc["prop"]), ("assertion", True, "(N : ℕ)", "N ≤ N + 1"))
        self.assertIn("theorem erdos_1 (N : ℕ) :", T.frozen_statement(fc, 1))

    def test_a_negated_assertion_keeps_the_yes_reading(self):
        src = "/-- No. -/\n@[category research solved]\ntheorem erdos_3 : ¬ (∃ n : ℕ, n + 1 = 0) := by\n  sorry\n"
        fc = T.parse_fc(src, 3)
        self.assertEqual((fc["prop"], fc["answer"], fc.get("negation_stripped")), ("∃ n : ℕ, n + 1 = 0", False, True))

    def test_multipart_files_are_excluded_with_the_parts_named(self):
        src = "theorem erdos_11.parts.i : True := by\n  sorry\ntheorem erdos_11.parts.ii : True := by\n  sorry\n"
        self.assertIn("parts: parts.i, parts.ii", T.parse_fc(src, 11)["error"])

    def test_inline_open_travels_with_the_theorem(self):
        src = "/-- Q. -/\nopen Real in\n@[category research solved]\ntheorem erdos_2 : π > 3 := by\n  sorry\n"
        fc = T.parse_fc(src, 2)
        self.assertEqual(fc["inline_opens"], ["open Real in"])
        self.assertIn("open Real in\ntheorem erdos_8 :", T.frozen_statement(fc, 8))

    def test_a_let_inside_the_statement_does_not_end_it(self):
        src = ("/-- Q. -/\n@[category research solved]\ntheorem erdos_38 : ∃ B : Set ℕ, ∀ N : ℕ, let α := (N : ℝ) / 2\n"
               "    α ≤ N := by\n  sorry\n")
        fc = T.parse_fc(src, 38)
        self.assertEqual(fc["prop"], "∃ B : Set ℕ, ∀ N : ℕ, let α := (N : ℝ) / 2\n    α ≤ N")   # the newline ends the let
        self.assertTrue(T.frozen_statement(fc, 1).endswith("\n    α ≤ N := by\n  sorry"))

    def test_bindings_before_the_answer_stay_in_front_of_the_proposition(self):
        src = ("/-- Q. -/\n@[category research solved]\ntheorem erdos_469 :\n    letI A := {n : ℕ | 0 < n}\n"
               "    answer(True) ↔ Summable fun n : A ↦ 1 / (n : ℝ) := by\n  sorry\n")
        fc = T.parse_fc(src, 469)
        self.assertEqual((fc.get("error"), fc["answer"]), (None, True))
        self.assertEqual(fc["prop"], "letI A := {n : ℕ | 0 < n}\nSummable fun n : A ↦ 1 / (n : ℝ)")
        self.assertIn("\n    letI A := {n : ℕ | 0 < n}\n    Summable fun n", T.frozen_statement(fc, 1))

    def test_dot_notation_pulls_in_the_local_definition(self):
        src = ("def Nat.IsSumDivisors (n : ℕ) : Prop :=\n  n = 6\n/-- Q. -/\n@[category research solved]\n"
               "theorem erdos_469 : answer(True) ↔ ∃ n : ℕ, n.IsSumDivisors := by\n  sorry\n")
        self.assertIn("def Nat.IsSumDivisors", T.frozen_statement(T.parse_fc(src, 469), 1))

    def test_missing_file(self):
        self.assertEqual(T.parse_fc("", 1)["error"], "no formal-conjectures file")


class Sources(unittest.TestCase):
    def test_dates(self):
        self.assertEqual(T.parse_date("25 Apr, 2026"), "2026-04-25")
        self.assertEqual(T.parse_date("20 May 2026"), "2026-05-20")
        self.assertEqual(T.parse_date("21 May-9 Jun, 2026"), "2026-05-21")
        self.assertIsNone(T.parse_date("soon"))
        self.assertEqual((T.key_year("Er85"), T.key_year("BNPZ26"), T.key_year("ErGr76b")), (1985, 2026, 1976))

    def test_wiki_rows_follow_each_tables_header(self):
        md = ("### 1(a). AI standalone\n\n| Problem | AI systems | Date | Outcome |\n| --- | --- | --- | --- |\n"
              "| [[90]](https://www.erdosproblems.com/90) | OpenAI internal model | 20 May, 2026 | 🟢 Full solution\n\n"
              "### 1(d). AI collaborating with humans\n\n| Problem | Humans | AI systems | Date | Outcome |\n| --- | --- | --- | --- | --- |\n"
              "| [[90]](https://www.erdosproblems.com/90) | A. Person | GPT-5.5 Pro | 21 May-9 Jun, 2026 | 🟢 Improved explicit bound\n")
        rows = T.parse_wiki(md)["90"]
        self.assertEqual([(r["section"], r["date"], r["systems"]) for r in rows],
                         [("1(a)", "2026-05-20", "OpenAI internal model"), ("1(d)", "2026-05-21", "GPT-5.5 Pro")])

    def test_site_page(self):
        page = ("<html><body><div>Random Open</div><div>DISPROVED (LEAN)</div><div>This has been solved in the negative.</div>"
                "<div>- $500</div><p>Is every set small?</p><div>#90: [Er46b]</div><p>This was disproved by X [Xy26].</p>"
                "<div>Proof expositions (0)</div><div>This page was last edited 20 May 2026.</div></body></html>")
        s = T.parse_site(page, 90)
        self.assertEqual(s["statement"], "Is every set small?")
        self.assertIn("disproved by X", s["notes"])
        self.assertEqual(s["edited"], "2026-05-20")

    def test_only_resolving_sentences_date_the_resolution(self):
        strong = ["This was proved by Lewis [Le25], whose proof has been formalized in Lean.",
                  "Cambie and Kalviainen [CaKa26] answered this question in the negative by constructing a walk.",
                  "This conjecture has been **disproved**: in September 2025, Tao gave a conditional negative answer.",
                  "A negative answer was given by Cambie and Kalviainen [CaKa26]."]
        background = ["Zhao [Zh11] has proved $R(T)\\leq 2n-2$ for all large $n$ via an alternative method.",
                      "When $T$ is a path Gerencsér and Gyárfás [GeGy67] proved $R(T)=\\lfloor 3n/2\\rfloor-1$."]
        sents = T.resolution_sentences(" ".join(strong + background))
        self.assertEqual(len(T.strong_sentences(sents)), len(strong))
        for s in T.strong_sentences(sents):
            self.assertNotIn("Zh11", s)
            self.assertNotIn("GeGy67", s)

    def test_trivial_is_specific(self):
        for yes in ("The question is trivially true.", "It has a trivial solution: take A = N.", "This is trivial."):
            self.assertTrue(T.TRIVIAL_RE.search(yes), yes)
        for no in ("A non-trivial argument proved it.", "They improved the trivial bound.", "nontrivially solved"):
            self.assertFalse(T.TRIVIAL_RE.search(no), no)


def item(n="100", first="2026-03-01", **kw):
    return {"problem": n, "first_public": first, "exclude_reason": None, "probe": None, "mask": None, **kw}


class FormalConjecturesLibrary(unittest.TestCase):
    """Names only formal-conjectures defines are inlined with their namespace, dependencies and notation."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.old = T.CACHE
        T.CACHE = Path(self.tmp.name)
        lib = T.CACHE / "fcm" / "FormalConjecturesForMathlib" / "Data" / "Set"
        lib.mkdir(parents=True)
        (lib / "Density.lean").write_text(
            "module\n\npublic import Mathlib.Order.Interval.Set.Basic\n\n@[expose] public section\n\nnamespace Set\n\n"
            "open Filter\n\n/-- Partial density. -/\nnoncomputable abbrev partialDensity (S : Set ℕ) (b : ℕ) : ℝ :=\n  (S ∩ Iio b).ncard / b\n\n"
            "/-- Upper density. -/\nnoncomputable def upperDensity (S : Set ℕ) : ℝ :=\n  atTop.limsup fun b ↦ S.partialDensity b\n\n"
            "end Set\n")
        (lib / "Notation.lean").write_text("notation g \" ≪ \" f => Asymptotics.IsBigO Filter.atTop g f\n"
                                          "namespace SimpleGraph\nscoped notation \"χ(\" G \")\" => chromaticNumber G\nend SimpleGraph\n")

    def tearDown(self):
        T.CACHE = self.old
        self.tmp.cleanup()

    def test_definition_and_its_dependency_come_first(self):
        blocks, names = T.fcm_inline(["line 9:2: Unknown identifier `Set.upperDensity`"], "0 < A.upperDensity", T.fcm_decls())
        self.assertEqual(names, ["Set.partialDensity", "Set.upperDensity"])
        self.assertTrue(blocks[0].startswith("namespace Set\nopen Filter\n"))
        self.assertNotIn("Upper density", "\n".join(blocks))          # docstrings are stripped

    def test_notation_by_its_leading_token_only(self):
        _, names = T.fcm_inline(["unexpected token '≪'"], "theorem x : f ≪ g := by sorry", T.fcm_decls())
        self.assertEqual(names, ["notation ≪"])                        # the χ( notation's ")" matches nothing
        _, names = T.fcm_inline([], "theorem x (G : SimpleGraph V) : χ(G) = 3 := by sorry", T.fcm_decls())
        self.assertEqual(names, ["notation χ("])


class ImportResolution(unittest.TestCase):
    class Idx:
        by_name = {"SimpleGraph.CliqueFree": ("Mathlib.Combinatorics.SimpleGraph.Clique", "def", ""),
                   "Nat.nth": ("Mathlib.Data.Nat.Nth", "def", ""),
                   "EuclideanGeometry.angle": ("Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine", "def", ""),
                   "EuclideanGeometry.Cospherical": ("Mathlib.Analysis.InnerProductSpace.EuclideanDist", "def", "")}

        def lookup(self, name):
            hit = self.by_name.get(name)
            return (hit[0], hit[2]) if hit else None

    def test_declaration_field_and_namespace(self):
        errs = ["line 3:1: Invalid field `CliqueFree`: The environment does not contain `SimpleGraph.CliqueFree`, so",
                "line 4:1: Unknown identifier `Nat.nth`", "line 1:5: unknown namespace `EuclideanGeometry`"]
        mods = T.modules_for(errs, self.Idx(), ["Mathlib.Tactic"])
        # a namespace resolves through its shortest declaration: `EuclideanGeometry.angle`, not `.Cospherical`
        self.assertEqual(mods, ["Mathlib.Combinatorics.SimpleGraph.Clique", "Mathlib.Data.Nat.Nth",
                                "Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine"])
        self.assertEqual(T.modules_for(errs, self.Idx(), mods), [])          # nothing new once imported

    def test_classical_open_is_a_frozen_line(self):
        fc = T.parse_fc("/-- Q. -/\n@[category research solved]\ntheorem erdos_5 : ∃ n : ℕ, n = n := by\n  sorry\n", 5)
        self.assertTrue(T.frozen_statement(fc, 1, classical=True).startswith("open scoped Classical\n"))


class Splits(unittest.TestCase):
    def test_probe_verdicts(self):
        self.assertEqual(T.probe_verdict({"status_believed": "resolved", "answer_claimed": "no"}, False), "recalled")
        self.assertEqual(T.probe_verdict({"status_believed": "open", "answer_claimed": "no", "recalls_method": True}, False), "recalled")
        self.assertEqual(T.probe_verdict({"status_believed": "resolved", "answer_claimed": "yes"}, False), "misremembered")
        self.assertEqual(T.probe_verdict({"status_believed": "resolved", "source_recalled": "a 2026 preprint"}, True), "partial-recall")
        self.assertEqual(T.probe_verdict({"status_believed": "open", "answer_guess": "no"}, False), "unaware")

    def test_classification(self):
        cut = "2026-07-01"
        self.assertEqual(T.classify(item(first="2026-08-02"), cut), ("test", None))
        self.assertEqual(T.classify(item(), cut), ("unprobed", None))
        probed = T.classify(item(probe={"verdict": "unaware"}), cut)[0]
        self.assertIn(probed, ("dev", "train"))
        self.assertEqual(T.classify(item(first="2026-08-02", probe={"verdict": "recalled"}), cut)[0], "excluded")
        self.assertEqual(T.classify(item(probe={"verdict": "unaware"}, mask={"ok": False, "error": "x"}), cut)[0], "excluded")
        self.assertEqual(T.classify(item(probe={"verdict": "unaware"}, mask={"ok": True, "faithful": False}), cut)[0], "excluded")
        self.assertEqual(T.classify(item(exclude_reason="no statement text"), cut), ("excluded", "no statement text"))

    def test_dev_train_is_stable_and_balanced(self):
        a = [T.split_of(str(n)) for n in range(1, 1201)]
        self.assertEqual(a, [T.split_of(str(n)) for n in range(1, 1201)])
        self.assertTrue(500 < a.count("dev") < 700)

    def test_aliases_are_fresh_and_deterministic(self):
        taken = set(range(0, 2001))
        a = T.alias_for("387", "mask", set(taken))
        self.assertEqual(a, T.alias_for("387", "mask", set(taken)))
        self.assertTrue(20000 <= a < 100000)
        self.assertNotEqual(T.alias_for("387", "mask", taken | {a}), a)
        self.assertNotEqual(T.alias_for("387", "tag-1", set(taken)), T.alias_for("387", "tag-2", set(taken)))


class DiscoverFirst(unittest.TestCase):
    """Candidate discover-v1: the direction it commits to, and the negation it freezes for NO."""

    def test_commits_only_on_a_clear_and_supported_majority(self):
        ok = {"valid": True}
        d = T.decide_direction([{"answer": "false", "confidence": 0.8, "complete": True, "critic": ok},
                                {"answer": "false", "confidence": 0.6, "complete": False},
                                {"answer": "true", "confidence": 0.3, "complete": False}])
        self.assertEqual((d["commit"], d["answer"]), ("neg", "false"))
        d = T.decide_direction([{"answer": "true", "confidence": 0.7, "complete": False},
                                {"answer": "false", "confidence": 0.7, "complete": False}])
        self.assertIsNone(d["commit"])                                   # split: attack both, as the baseline does
        d = T.decide_direction([{"answer": "true", "confidence": 0.5, "complete": False},
                                {"answer": "true", "confidence": 0.4, "complete": False}])
        self.assertEqual(d["commit"], "pos")                             # unanimous, even without a refereed proof
        d = T.decide_direction([{"answer": "true", "confidence": 0.9, "complete": True, "critic": {"valid": False}},
                                {"error": "provider"}])
        self.assertIsNone(d["commit"])                                   # one refuted attempt is not agreement
        self.assertEqual(T.decide_direction([])["commit"], None)

    def test_v2_commits_on_one_confident_answer_when_the_other_attempt_produced_nothing(self):
        attempts = [{"error": "error_max_budget_usd"}, {"answer": "true", "confidence": 0.8, "complete": False}]
        self.assertIsNone(T.decide_direction(attempts)["commit"])                       # v1 (#392)
        self.assertEqual(T.decide_direction(attempts, single_confident=0.75)["commit"], "pos")
        weak = [{"error": "x"}, {"answer": "true", "confidence": 0.6, "complete": False}]
        self.assertIsNone(T.decide_direction(weak, single_confident=0.75)["commit"])
        split = [{"answer": "true", "confidence": 0.9}, {"answer": "false", "confidence": 0.8}]
        self.assertIsNone(T.decide_direction(split, single_confident=0.75)["commit"])   # disagreement never commits

    def test_negation_keeps_defs_and_turns_binders_into_a_forall(self):
        st = "open Real\n\ndef f (n : ℕ) : ℕ := n\n\ntheorem erdos_12 (n : ℕ) :\n    f n ≤ n + 1 := by\n  sorry"
        self.assertEqual(T.negated_statement(st),
                         "open Real\n\ndef f (n : ℕ) : ℕ := n\n\ntheorem erdos_12 :\n    ¬ (∀ (n : ℕ), f n ≤ n + 1) := by\n  sorry")
        st = "theorem erdos_3 :\n    ∃ n : ℕ,\n      n = 2 := by\n  sorry"
        self.assertEqual(T.negated_statement(st), "theorem erdos_3 :\n    ¬ (∃ n : ℕ,\n      n = 2) := by\n  sorry")


class UsageLimit(unittest.TestCase):
    def test_reset_parsing(self):
        from datetime import datetime
        now = datetime(2026, 9, 24, 7, 30)
        self.assertAlmostEqual(T.seconds_until_reset("You've hit your session limit · resets 8:10am (America/Toronto)", now),
                               40 * 60 + 180)
        self.assertAlmostEqual(T.seconds_until_reset("resets 1pm", now), 5.5 * 3600 + 180)
        self.assertEqual(T.seconds_until_reset("no time given", now), 1800.0)
        self.assertAlmostEqual(T.seconds_until_reset("resets 7:20am", now), 180.0)     # just passed: go now
        self.assertLessEqual(T.seconds_until_reset("resets 5am", now), 6 * 3600)          # tomorrow, capped

    def test_limit_detection(self):
        self.assertTrue(T.LIMIT_RE.search('RuntimeError("claude -p returned an error result (literature): success: '
                                          "You've hit your session limit · resets 8:10am"))
        self.assertFalse(T.LIMIT_RE.search("OAuth session expired and could not be refreshed"))


class BatchCheck(unittest.TestCase):
    """One Lean process for many statements; an error is charged only to the block it falls in."""

    class FakeChecker:
        def __init__(self, bad_token):
            self.bad = bad_token

        def check(self, src, dest):
            lines = [n for n, l in enumerate(src.splitlines(), 1) if self.bad in l]
            return {"ok": not lines, "timeout": False, "errors": [f"line {n}:4: unknown identifier '{self.bad}'" for n in lines]}

    def test_errors_are_attributed_to_their_block(self):
        import harness as H
        st = {"1": "theorem erdos_1 : True := by\n  sorry", "2": "theorem erdos_2 : Foo := by\n  sorry",
              "3": "open Real\n\ntheorem erdos_3 : 1 = 1 := by\n  sorry"}
        ok, errs = T.batch_check(H, self.FakeChecker("Foo"), st, 40)
        self.assertEqual(ok, {"1", "3"})
        self.assertIn("unknown identifier", errs["2"][0])
        self.assertEqual(T.batch_check(H, self.FakeChecker("Foo"), st, 1)[0], {"1", "3"})

    def test_an_unattributable_error_passes_nothing(self):
        import harness as H
        self.assertEqual(T.batch_check(H, self.FakeChecker("set_option maxHeartbeats"), {"1": "theorem erdos_1 : True := by\n  sorry"}, 40)[0], set())


class Scoring(unittest.TestCase):
    # These tests exercise the scoring logic on fake run directories that hold no real proof, so the audit is
    # stubbed to pass; `test_a_failed_audit_blocks_the_solve_and_the_contradiction` covers the other side.
    PASSED = {"verdict": "PASS", "failed": [], "lean_ok": True}

    def setUp(self):
        from unittest.mock import patch
        self._audit = patch.object(T, "audit_run", return_value=self.PASSED)
        self.audit_stub = self._audit.start()
        self.addCleanup(self._audit.stop)
        self.tmp = tempfile.TemporaryDirectory()
        self.run = Path(self.tmp.name) / "20260924-000000-000000-timesplit-erdos45678"
        for d in ("pos", "neg"):
            (self.run / d).mkdir(parents=True)
        (self.run / "log.jsonl").write_text(json.dumps({"ts": "2026-09-24T00:00:00Z", "stage": "run", "event": "start"}) + "\n"
                                            + json.dumps({"ts": "2026-09-24T00:01:00Z", "stage": "llm", "event": "response",
                                                          "purpose": "plan", "cost_usd": 1.5}) + "\n")

    def tearDown(self):
        self.tmp.cleanup()

    def _state(self, d, **kw):
        (self.run / d / "state.json").write_text(json.dumps(kw))

    GOOD = {"compiles": True, "sorry_free": True, "frozen_match": True, "axioms_clean": True, "banned": None}

    def test_true_direction_verified_is_solved(self):
        self._state("pos", outcome="proved", verify=self.GOOD, residual={"certified": 2, "open": 0})
        self._state("neg", outcome="partial", residual={"certified": 1, "open": 1}, target_believed_false={"cycle": 1})
        r = T.score_run(self.run, "45678", True)
        self.assertTrue(r["solved"])
        self.assertFalse(r["contradiction"])
        self.assertEqual((r["true_certified"], r["false_stopped"], r["true_abandoned"]), (2, True, False))

    def test_wrong_direction_verified_is_a_contradiction_not_a_solve(self):
        self._state("pos", outcome="proved", verify=self.GOOD)
        self._state("neg", outcome="partial")
        r = T.score_run(self.run, "45678", False)
        self.assertFalse(r["solved"])
        self.assertTrue(r["contradiction"])

    def test_a_proof_failing_any_gate_is_not_solved(self):
        for broken in ("compiles", "sorry_free", "frozen_match", "axioms_clean"):
            self._state("pos", outcome="proved", verify={**self.GOOD, broken: False})
            self._state("neg", outcome="partial")
            self.assertFalse(T.score_run(self.run, "45678", True)["solved"], broken)

    def test_mechanically_clean_counts_even_when_the_run_judge_demurs(self):
        self._state("pos", outcome="proved_unverified", verify={**self.GOOD, "faithful": {"faithful": False}})
        self._state("neg", outcome="partial")
        r = T.score_run(self.run, "45678", True)
        self.assertTrue(r["solved"])
        self.assertIs(r["directions"]["pos"]["judge_faithful"], False)

    def test_a_failed_audit_blocks_the_solve_and_the_contradiction(self):
        # a proof the harness verified by TEXT but whose elaborated statement is not the frozen one
        self.audit_stub.return_value = {"verdict": "FAIL", "failed": ["statement_identity"], "lean_ok": False}
        self._state("pos", outcome="proved", verify=self.GOOD)
        self._state("neg", outcome="partial")
        r = T.score_run(self.run, "45678", True)
        self.assertFalse(r["solved"])
        self.assertEqual(r["audit"]["failed"], ["statement_identity"])
        self.assertFalse(T.score_run(self.run, "45678", False)["contradiction"])
        # the wrong direction proved and every Lean check passing still reaches `contradiction`
        self.audit_stub.return_value = {"verdict": "FAIL", "failed": ["direction_matches_answer"], "lean_ok": True}
        self.assertTrue(T.score_run(self.run, "45678", False)["contradiction"])

    def test_the_audit_runs_only_when_a_direction_verified(self):
        self._state("pos", outcome="partial")
        self._state("neg", outcome="partial")
        self.assertIsNone(T.score_run(self.run, "45678", True)["audit"])
        self.audit_stub.assert_not_called()

    def test_a_run_committed_to_one_direction(self):
        (self.run / "state.json").write_text(json.dumps({"outcome": "proved_unverified", "verify": self.GOOD}))
        r = T.score_run(self.run, "45678", False, committed="neg")
        self.assertTrue(r["solved"])
        self.assertEqual(r["directions"]["pos"]["outcome"], "not attempted")
        r = T.score_run(self.run, "45678", True, committed="neg")        # committed to the wrong direction and proved it
        self.assertEqual((r["solved"], r["contradiction"]), (False, True))

    def test_mcnemar(self):
        self.assertEqual(T.mcnemar_exact(0, 0), 1.0)
        self.assertAlmostEqual(T.mcnemar_exact(0, 5), 0.0625)
        self.assertEqual(T.mcnemar_exact(3, 3), 1.0)

    def test_summary(self):
        recs = {"1": {"solved": True, "contradiction": False, "false_stopped": True, "true_abandoned": False,
                      "true_certified": 2, "spend": 4.0, "returncode": 0, "fatals": 0},
                "2": {"solved": False, "contradiction": False, "false_stopped": False, "true_abandoned": True,
                      "true_certified": 0, "spend": 6.0, "returncode": 1, "fatals": 0}}
        s = T.summarize(recs)
        self.assertEqual((s["items"], s["solved"], s["usd_per_solve"], s["infrastructure_failures"]), (2, 1, 10.0, ["2"]))
        self.assertTrue(s["rate_90"][0] < 0.5 < s["rate_90"][1])


# A residual in the shape the harness writes: hypothesis `a` is a refinement spliced into `a_ns`, with one sub-hypothesis
# certified (`a_hyp_c`, itself spliced) and one still open (`a_hyp_b`); `d` is certified with a private helper; `e` is
# certified but the glue never uses it; `p` is a published premise; `z`'s proof copy is called by the glue directly.
SKELETON = '''open Filter

def f (n : ℕ) : ℕ := n + 1

namespace erdos_77_hyp_a_ns
theorem erdos_77_hyp_a_hyp_b : ∀ n, f n > 0 := by
  sorry

namespace erdos_77_hyp_a_hyp_c_ns
theorem erdos_77_hyp_a_hyp_c : ∀ n, f n > n := by
  intro n; simp [f]
end erdos_77_hyp_a_hyp_c_ns

theorem erdos_77_hyp_a_hyp_c : ∀ n, f n > n := by
  exact erdos_77_hyp_a_hyp_c_ns.erdos_77_hyp_a_hyp_c

theorem erdos_77_hyp_a : ∀ n, f n ≥ 1 ∧ f n > n := by
  intro n; exact ⟨erdos_77_hyp_a_hyp_b n, erdos_77_hyp_a_hyp_c n⟩
end erdos_77_hyp_a_ns

theorem erdos_77_hyp_a : ∀ n, f n ≥ 1 ∧ f n > n := by
  exact erdos_77_hyp_a_ns.erdos_77_hyp_a

namespace erdos_77_hyp_d_ns
private lemma aux : 1 = 1 := rfl
theorem erdos_77_hyp_d : 2 = 2 := by
  exact aux ▸ rfl
end erdos_77_hyp_d_ns

theorem erdos_77_hyp_d : 2 = 2 := by
  exact erdos_77_hyp_d_ns.erdos_77_hyp_d

theorem erdos_77_hyp_e : 3 = 3 := by
  rfl

namespace erdos_77_hyp_z_ns
theorem erdos_77_hyp_z : 5 = 5 := by
  rfl
end erdos_77_hyp_z_ns

theorem erdos_77_hyp_z : 5 = 5 := by
  exact erdos_77_hyp_z_ns.erdos_77_hyp_z

-- PUBLISHED: Someone, A theorem (1950)
theorem erdos_77_hyp_p : 4 = 4 := by
  sorry

-- a comment naming erdos_77_hyp_e must not count as a use
theorem erdos_77 : True := by
  have := erdos_77_hyp_a
  have := erdos_77_hyp_d
  have := erdos_77_hyp_p
  have := erdos_77_hyp_z_ns.erdos_77_hyp_z
  trivial
'''


class DenseProgress(unittest.TestCase):
    """The dense metric counts closed, used, non-trivial hypotheses of the TRUE direction, maximal ones only."""

    def test_closed_used_and_maximal(self):
        st = T.residual_structure(SKELETON, 77, "erdos_77")
        self.assertTrue(st["main_present"])
        # `a` has no hole of its own but rests on the open `a_hyp_b`: not closed. Its certified `a_hyp_c` is the piece.
        self.assertEqual(st["maximal"], ["erdos_77_hyp_a_hyp_c", "erdos_77_hyp_d", "erdos_77_hyp_z"])
        self.assertEqual(st["closed_used"], ["erdos_77_hyp_a_hyp_c", "erdos_77_hyp_d", "erdos_77_hyp_z"])
        self.assertEqual(st["unused_closed"], ["erdos_77_hyp_e"])
        self.assertEqual(st["open_conjectures"], ["erdos_77_hyp_a_hyp_b"])
        self.assertEqual(st["open_published"], ["erdos_77_hyp_p"])
        self.assertEqual(st["harness_certified"], 5)        # a, a_hyp_c, d, e, z: what the harness's own count says

    def test_a_certified_step_counts_once_however_it_was_proved(self):
        closed = SKELETON.replace("theorem erdos_77_hyp_a_hyp_b : ∀ n, f n > 0 := by\n  sorry",
                                  "theorem erdos_77_hyp_a_hyp_b : ∀ n, f n > 0 := by\n  intro n; simp [f]")
        st = T.residual_structure(closed, 77, "erdos_77")
        self.assertEqual(st["maximal"], ["erdos_77_hyp_a", "erdos_77_hyp_d", "erdos_77_hyp_z"])
        self.assertEqual(len(st["closed_used"]), 5)         # a, a_hyp_b, a_hyp_c, d, z at any depth

    def test_the_negation_direction_has_its_own_main(self):
        neg = SKELETON.replace("erdos_77_hyp", "erdos_77_neg_hyp").replace("theorem erdos_77 :", "theorem erdos_77_neg :")
        st = T.residual_structure(neg, 77, "erdos_77_neg")
        self.assertEqual(st["maximal"], ["erdos_77_neg_hyp_a_hyp_c", "erdos_77_neg_hyp_d", "erdos_77_neg_hyp_z"])
        self.assertFalse(T.residual_structure(neg, 77, "erdos_77")["main_present"])

    class FakeChecker:
        """Fails the cascade on statements containing `hard`, the plain statement on `broken`; `spin` times out."""
        def __init__(self):
            self.sources = []

        def check(self, src, dest):
            self.sources.append(src)
            if "spin" in src:
                return {"ok": False, "timeout": True, "errors": ["lean check timed out"]}
            errs, block = [], None
            for n, line in enumerate(src.splitlines(), 1):
                if line.startswith("-- TS-"):
                    block = line.split()[1].split("-")[1]
                if block == "FREE" and "hard" in line:
                    errs.append(f"line {n}:2: linarith failed")
                if block == "CTX" and "broken" in line:
                    errs.append(f"line {n}:2: unknown identifier 'broken'")
            return {"ok": not errs, "timeout": False, "errors": errs}

    def test_triviality_verdicts_are_attributed_per_statement(self):
        import harness as H
        sk = ("def g (n : ℕ) : ℕ := n\n\n"
              "theorem erdos_9_hyp_easy : g 1 = 1 := by\n  exact erdos_9_hyp_easy_ns.erdos_9_hyp_easy\n\n"
              "theorem erdos_9_hyp_real : ∀ n, g n = n + 0 ∧ hard := by\n  exact x\n\n"
              "theorem erdos_9_hyp_bad : broken = 1 := by\n  exact y\n\n"
              "theorem erdos_9 : True := by\n  trivial\n")
        fc = self.FakeChecker()
        v = T.free_closable(H, fc, sk, ["erdos_9_hyp_easy", "erdos_9_hyp_real", "erdos_9_hyp_bad"], ["Mathlib"])
        self.assertEqual(v, {"erdos_9_hyp_easy": "trivial", "erdos_9_hyp_real": "nontrivial", "erdos_9_hyp_bad": "context_error"})
        src = fc.sources[0]
        # checked as examples: a sorry'd or failed THEOREM would stay in the environment for `exact?` to reuse
        self.assertNotIn("theorem erdos_9_hyp", src)
        self.assertEqual(src.count("example"), 6)
        self.assertIn("def g", src.split("-- TS-FREE 0")[1])         # each statement carries the skeleton's context

    def test_a_hung_statement_is_isolated_and_marked_unknown(self):
        import harness as H
        sk = ("theorem erdos_9_hyp_a : 1 = 1 := by\n  exact p\n\n"
              "theorem erdos_9_hyp_hang : spin = 2 := by\n  exact q\n\n"
              "theorem erdos_9 : True := by\n  trivial\n")
        fc = self.FakeChecker()
        v = T.free_closable(H, fc, sk, ["erdos_9_hyp_a", "erdos_9_hyp_hang"], ["Mathlib"])
        self.assertEqual(v, {"erdos_9_hyp_a": "trivial", "erdos_9_hyp_hang": "unknown"})
        self.assertEqual(len(fc.sources), 3)                           # the batch, then each statement alone

    def test_sign_test(self):
        self.assertEqual(T.sign_test_greater(0, 0), 1.0)
        self.assertAlmostEqual(T.sign_test_greater(8, 2), 56 / 1024)
        self.assertAlmostEqual(T.sign_test_greater(5, 0), 1 / 32)
        self.assertAlmostEqual(T.sign_test_greater(0, 3), 1.0)

    def test_paired_key_puts_a_solve_above_any_number_of_pieces(self):
        g = lambda k, size, c=0: {"pieces": k, "certified_size": size, "closed_lemmas": c}
        a = {"1": {"solved": True, "progress": g(0, 0)}, "2": {"solved": False, "progress": g(2, 900, 3)},
             "3": {"solved": False, "progress": g(1, 400)}, "4": {"solved": False, "progress": None},
             "5": {"solved": False, "progress": g(0, 0)}}
        b = {"1": {"solved": False, "progress": g(4, 5000, 4)}, "2": {"solved": False, "progress": g(1, 300, 1)},
             "3": {"solved": False, "progress": g(1, 400)}, "4": {"solved": False, "progress": g(1, 100)},
             "5": {"solved": True, "progress": g(0, 0)}}
        c = T.dense_compare(a, b)
        self.assertEqual((c["wins"], c["losses"], c["ties"], c["unmeasured"]), (["1", "2"], ["5"], 1, ["4"]))
        self.assertEqual(c["pairs"], 4)
        self.assertAlmostEqual(c["p_one_sided"], 0.5)
        self.assertEqual(c["closed_lemmas_delta"], -2)

    def test_a_direction_lost_to_the_limit_is_infrastructure(self):
        done = {"open": {"pos": "error: RuntimeError(\"You've hit your session limit · resets 4:10am\")", "neg": 3}, "exit": 3}
        self.assertEqual(list(T.lost_directions(done)), ["pos"])
        self.assertEqual(T.lost_directions({"open": {"pos": 3, "neg": 2}}), {})
        g = {"pieces": 1, "certified_size": 100, "closed_lemmas": 1}
        a = {"1": {"solved": False, "progress": g, "lost_directions": []},
             "2": {"solved": False, "progress": g, "lost_directions": []}}
        b = {"1": {"solved": False, "progress": g, "lost_directions": ["pos"]},
             "2": {"solved": False, "progress": g, "lost_directions": []}}
        c = T.dense_compare(a, b)
        self.assertEqual((c["pairs"], c["lost_a_direction"]), (1, ["1"]))

    def test_chunking_or_verbosity_alone_is_a_tie(self):
        run = lambda k, size: {"solved": False, "progress": {"pieces": k, "certified_size": size, "closed_lemmas": k}}
        self.assertEqual(T.dense_outcome(run(3, 1000), run(1, 1100)), "T")     # the same proof split three ways
        self.assertEqual(T.dense_outcome(run(1, 5000), run(1, 1000)), "T")     # one longer proof of the same step
        self.assertEqual(T.dense_outcome(run(2, 1500), run(1, 1000)), "W")
        self.assertEqual(T.dense_outcome(run(1, 900), run(2, 1500)), "L")
        c = T.dense_compare({"7": run(3, 1000)}, {"7": run(1, 1100)})
        self.assertEqual((c["wins"], c["pieces_only"]["wins"]), ([], ["7"]))   # the naive count would have called it

    def test_certified_size_covers_what_the_pieces_rest_on(self):
        st = T.residual_structure(SKELETON, 77, "erdos_77")
        under = set().union(*(st["support"][n] for n in st["maximal"]))
        self.assertIn("erdos_77_hyp_d_ns.aux", under)                          # a helper inside a spliced proof
        self.assertEqual(st["sizes"]["f"], 0)                                  # the problem's own def counts nothing
        self.assertNotIn("erdos_77_hyp_e", under)                              # unused



class CommitCalibration(unittest.TestCase):
    """A confidence floor only withholds a commitment; the report counts wrong commits against the truth."""

    @staticmethod
    def rec(truth, answers, confs, v1, v2):
        return {"problem": "1", "round": 0, "truth": truth, "spend": 1.0, "v1_commit": v1, "v2_commit": v2,
                "attempts": [{"answer": a, "confidence": c} for a, c in zip(answers, confs)]}

    def test_a_floor_withholds_a_low_confidence_commitment(self):
        r = self.rec(False, ["true", "true"], [0.5, 0.6], "pos", "pos")        # the #537 shape: unanimous, unsure, wrong
        self.assertEqual(T.commit_at_floor(r, None), "pos")
        self.assertEqual(T.commit_at_floor(r, 0.5), "pos")
        self.assertIsNone(T.commit_at_floor(r, 0.6))                           # mean 0.55
        self.assertIsNone(T.commit_at_floor(self.rec(True, ["true", None], [0.9, None], None, None), 0.5))

    def test_alloc_candidate_flags(self):
        import argparse
        a = argparse.Namespace(candidate="alloc", v3_flags=None)
        self.assertEqual(T.candidate_flags(a), T.ALLOC_FLAGS)
        self.assertIn("core-first", T.ALLOC_FLAGS)
        self.assertEqual(T.candidate_flags(argparse.Namespace(candidate="baseline")), [])

    def test_decide_direction_honours_the_calibrated_floor(self):
        unsure = [{"answer": "true", "confidence": 0.5}, {"answer": "true", "confidence": 0.6}]    # the #537 shape
        self.assertEqual(T.decide_direction(unsure)["commit"], "pos")
        self.assertIsNone(T.decide_direction(unsure, floor=0.6)["commit"])
        sure = [{"answer": "true", "confidence": 0.8}, {"answer": "true", "confidence": 0.7}]
        self.assertEqual(T.decide_direction(sure, floor=0.6)["commit"], "pos")

    def test_report_counts_wrong_commits_per_floor(self):
        recs = [self.rec(False, ["true", "true"], [0.5, 0.6], "pos", "pos"),
                self.rec(True, ["true", "true"], [0.8, 0.9], "pos", "pos"),
                self.rec(True, ["true", "false"], [0.7, 0.6], None, None)]
        rep = T.calibration_report(recs)
        row = lambda rule, f: next(x for x in rep["floors"] if x["rule"] == rule and x["floor"] == f)
        self.assertEqual((row("v1", None)["commits"], row("v1", None)["wrong"]), (2, 1))
        self.assertEqual((row("v1", 0.6)["commits"], row("v1", 0.6)["wrong"]), (1, 0))
        self.assertAlmostEqual(rep["attempt_accuracy"], 3 / 6)

if __name__ == "__main__":
    unittest.main()


class DiscoverV3(unittest.TestCase):
    def test_v3_fixes_v2s_settings_and_the_calibrated_floor(self):
        import argparse
        a = argparse.Namespace(candidate="discover-v3", discover_attempts=2, discover_effort="high", discover_budget=1.2,
                               critic_budget=0.3, gap_budget=1.2, gap_effort="medium", commit_floor=None)
        T.apply_candidate_settings(a)
        self.assertEqual((a.discover_effort, a.discover_budget, a.commit_floor), ("medium", 0.8, 0.6))
        b = argparse.Namespace(**{**vars(a), "commit_floor": 0.7})
        T.apply_candidate_settings(b)
        self.assertEqual(b.commit_floor, 0.7)                 # an explicit floor is kept
        c = argparse.Namespace(candidate="discover-v2", discover_effort="high", commit_floor=None)
        T.apply_candidate_settings(c)
        self.assertEqual((c.discover_effort, c.commit_floor), ("high", None))   # v2 keeps its own protocol

    def test_the_floor_refuses_dev_s_two_wrong_commits(self):
        # #537 (0.5, 0.6) and #871 (0.35, 0.3): both said "true", both were false; v2 committed, the floor does not
        for confs in ((0.5, 0.6), (0.35, 0.3)):
            attempts = [{"answer": "true", "confidence": c, "complete": False} for c in confs]
            self.assertIsNotNone(T.decide_direction(attempts, single_confident=0.75)["commit"])
            self.assertIsNone(T.decide_direction(attempts, single_confident=0.75, floor=0.6)["commit"])


class DiscoverV4(unittest.TestCase):
    """discover-v4: more rounds until a refereed complete proof appears (the conversion screen's #990 and #1037 got
    none in one round, where the calibration had them in 2 of 3 rounds each)."""
    INCOMPLETE = {"answer": "true", "confidence": 0.6, "complete": False, "cost": 0.3}
    REFEREED = {"answer": "false", "confidence": 0.9, "complete": True, "critic": {"valid": True}, "cost": 0.5}

    def _rounds(self, results):
        calls = []

        def run_round(r):
            calls.append(r)
            return [dict(x) for x in results[len(calls) - 1]]
        return run_round, calls

    def test_stops_at_the_first_refereed_complete_proof(self):
        run_round, calls = self._rounds([[self.REFEREED], [self.INCOMPLETE]])
        att, rounds, spent = T.run_more_rounds([dict(self.INCOMPLETE)], run_round, 3, 3.0, 0.3)
        self.assertEqual((rounds, len(calls)), (2, 1))
        self.assertEqual(att[-1]["round"], 2)
        self.assertAlmostEqual(spent, 0.8)

    def test_no_extra_round_when_the_first_already_has_one(self):
        run_round, calls = self._rounds([])
        att, rounds, _ = T.run_more_rounds([dict(self.REFEREED)], run_round, 3, 3.0, 0.5)
        self.assertEqual((rounds, calls), (1, []))

    def test_max_rounds_and_the_cost_cap(self):
        run_round, calls = self._rounds([[self.INCOMPLETE]] * 5)
        _, rounds, _ = T.run_more_rounds([dict(self.INCOMPLETE)], run_round, 3, 10.0, 0.3)
        self.assertEqual(rounds, 3)                                   # max_rounds in all
        run_round, calls = self._rounds([[{**self.INCOMPLETE, "cost": 1.2}]] * 5)
        _, rounds, spent = T.run_more_rounds([{**self.INCOMPLETE, "cost": 1.2}], run_round, 5, 3.0, 1.2)
        self.assertEqual(rounds, 2)                                   # a third round would pass the $3 cap
        self.assertAlmostEqual(spent, 2.4)

    def test_an_unrefereed_or_rejected_complete_proof_does_not_stop_the_rounds(self):
        self.assertFalse(T.has_refereed_complete([{"answer": "true", "complete": True, "critic": {"valid": False}}]))
        self.assertFalse(T.has_refereed_complete([{"answer": "true", "complete": True}]))
        self.assertTrue(T.has_refereed_complete([self.REFEREED]))

    def test_v4_settings(self):
        import argparse
        a = argparse.Namespace(candidate="discover-v4", commit_floor=None)
        T.apply_candidate_settings(a)
        self.assertEqual((a.discover_rounds, a.discover_total_budget, a.commit_floor, a.discover_effort),
                         (3, 3.0, 0.6, "medium"))


class EngineScreenRecord(unittest.TestCase):
    """discover-screen --discover-mode engine: the row says whether the engine's refereed complete chain lands on the
    TRUE side, and counts validated-new claims and those both judges rate significance 2 or more."""

    def test_record(self):
        import types
        from unittest.mock import patch
        with tempfile.TemporaryDirectory() as d:
            run = Path(d) / "runs" / "x-discover-erdos7"
            (run / "engine").mkdir(parents=True)
            (run / "state.json").write_text(json.dumps({"discovery": {"refereed_complete": True,
                "best_proof": {"answer": "true", "claim": "deep/C9", "text": "..."}}}))
            led = [{"session": "deep", "id": "C9", "validation": {"status": "valid-restatement"}},
                   {"session": "r1s1", "id": "C1", "validation": {"status": "validated-new", "novelty": {"significance": 2}}},
                   {"session": "r1s1", "id": "C2", "validation": {"status": "validated-new", "novelty": {"significance": 1}}},
                   {"session": "r1s1", "id": "C3", "status": "CONJECTURED"}]
            (run / "engine" / "engine.json").write_text(json.dumps({"ledger": led, "frontier": {"answer": "true"}}))
            args = types.SimpleNamespace(tag="t")
            with patch.object(T, "ROOT", Path(d)), patch.object(T, "protocol", lambda a: {}):
                rec = T.engine_screen_record(run, {"problem": "152", "answer": True, "split": "dev"}, 7, 2, {"spend": 21.4},
                                             args, ["--discover-mode", "engine"])
        self.assertEqual((rec["complete"], rec["refereed_true"], rec["refereed_false"]), (True, 1, 0))
        self.assertEqual((rec["validated_new"], rec["sig2"]), (2, 1))
        self.assertTrue(rec["direction_correct"])
        self.assertFalse(rec["solved"])                     # only Lean makes it a solve
        self.assertEqual(rec["claims"]["unvalidated-conjectured"], 1)
