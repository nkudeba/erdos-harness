"""Change A (a breadth-first cheap sweep over every open conjecture hypothesis, before core-first/per-cycle/
min-child-budget narrow the field to a handful attacked at length) and Change B (--attack-rounds /
--attack-decompose-rounds cap the long tail of one such depth attack). Also covers Change C's new defaults
(--refute changed, --premise-attack cheap) and Change D (--extract-subgoals). No provider calls; Lean and
child attacks are mocked, exactly as in test_deductive_mode.py and test_allocation_options.py (read first) --
except the DEDUCTIVE_LEAN_TESTS=1-gated class at the bottom, which compiles real Lean in formal/, as
test_deductive_lean.py does."""
import argparse, json, os, sys, tempfile, threading, unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parent))
import harness as H
from test_deductive_mode import FROZEN, Log, _judged, _stub


def plan_reply(skeleton: str, meta: dict | None = None) -> str:
    return "```lean\n" + skeleton + "\n```\n```json\n" + json.dumps(meta or {}) + "\n```\n"


class Isolated(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self._root, self._know = H.ROOT, H.KNOWLEDGE
        H.ROOT, H.KNOWLEDGE = self.root, self.root / "knowledge"
        (self.root / "run").mkdir()

    def tearDown(self):
        H.ROOT, H.KNOWLEDGE = self._root, self._know
        self.tmp.cleanup()

    def pdir(self):
        return self.root / "programs" / "erdos_99"


# One / two / three open conjecture hypotheses of increasing complexity (prop_complexity: a=3, b=7, c=11), so
# attack_order (no meta ratings -> all "unrated", no failures yet) is purely by complexity: a, b, c.
SKEL_ONE = """def foo (n : ℕ) : Prop := n = n

theorem erdos_99_hyp_a : ∀ n : ℕ, foo n := by
  sorry

theorem erdos_99 : ∀ n : ℕ, foo n := by
  intro n
  exact erdos_99_hyp_a n"""

SKEL_TWO = """def foo (n : ℕ) : Prop := n = n

theorem erdos_99_hyp_a : ∀ n : ℕ, foo n := by
  sorry

theorem erdos_99_hyp_b : ∀ n : ℕ, ∀ m : ℕ, foo n ∧ foo m := by
  sorry

theorem erdos_99 : ∀ n : ℕ, foo n := by
  intro n
  exact erdos_99_hyp_a n"""

SKEL_THREE = """def foo (n : ℕ) : Prop := n = n

theorem erdos_99_hyp_a : ∀ n : ℕ, foo n := by
  sorry

theorem erdos_99_hyp_b : ∀ n : ℕ, ∀ m : ℕ, foo n ∧ foo m := by
  sorry

theorem erdos_99_hyp_c : ∀ n : ℕ, ∀ m : ℕ, ∀ k : ℕ, foo n ∧ foo m ∧ foo k := by
  sorry

theorem erdos_99 : ∀ n : ℕ, foo n := by
  intro n
  exact erdos_99_hyp_a n"""

PROOF_A = "theorem erdos_99_hyp_a : ∀ n : ℕ, foo n := by\n  intro n\n  rfl"


def _sweep_harness(root, skeleton, **args_overrides):
    h = _stub(root / "run")
    h.args.sweep = "on"
    h.args.sweep_budget = 0.6
    h.args.sweep_max = 8
    for k, v in args_overrides.items():
        setattr(h.args, k, v)
    h._install_lemmas_module = lambda pdir: None
    h.ask = _judged(lambda purpose, prompt, **kw: plan_reply(skeleton))
    return h


class SweepAttemptsEveryOpenHypothesis(Isolated):
    """Test 1: the sweep tries every open conjecture once, in attack order, even when what is left is below
    --min-child-budget -- the sweep is gated only by its own floor (0.3) and --sweep-max, never by the
    depth phase's budget floor."""

    def test_attempts_every_conjecture_in_attack_order_below_min_child_budget(self):
        h = _sweep_harness(self.root, SKEL_THREE, min_child_budget=2.5, run_budget=5.0)
        h.spent_usd = lambda: 4.3          # $0.70 left: below min_child_budget (2.5), above the sweep floor (0.3)
        calls = []

        def attack(sub, name, sdir, cycle, module, remaining, recursive=False, cheap=False, **kw):
            calls.append((name, cheap, recursive))
            return 3, argparse.Namespace(state={"attempts": [], "stop_reason": "rounds exhausted"})
        h._attack_substatement = attack
        rc = h.run_program()
        self.assertEqual(rc, 3)
        self.assertEqual(calls, [("erdos_99_hyp_a", True, False), ("erdos_99_hyp_b", True, False),
                                 ("erdos_99_hyp_c", True, False)])
        sweep_ev = [e for e in h.log.events if e[1] == "sweep"]
        self.assertEqual(len(sweep_ev), 1)
        self.assertEqual(sweep_ev[0][2]["attempted"], 3)
        self.assertEqual(sweep_ev[0][2]["proved"], 0)
        # the depth phase still runs its own (unrelated) budget logic afterwards, and defers everything
        deferred = [e for e in h.log.events if e[1] == "hypotheses_deferred"]
        self.assertEqual(len(deferred), 1)
        self.assertEqual(set(deferred[0][2]["skipped"]), {"erdos_99_hyp_a", "erdos_99_hyp_b", "erdos_99_hyp_c"})
        # ledger rows for the sweep are written in the same shape as a depth ("hypothesis") row
        rows = [json.loads(l) for l in (self.pdir() / "ledger.jsonl").read_text().splitlines() if l.strip()]
        sweep_rows = [r for r in rows if r["kind"] == "sweep"]
        self.assertEqual(len(sweep_rows), 3)
        for r in sweep_rows:
            self.assertEqual(set(r), {"cycle", "kind", "sub", "run", "exit", "verified", "recursive", "statement", "at"})
            self.assertFalse(r["verified"])
            self.assertFalse(r["recursive"])

    def test_sweep_max_caps_attempts_per_cycle(self):
        h = _sweep_harness(self.root, SKEL_THREE, sweep_max=1)
        calls = []

        def attack(sub, name, sdir, cycle, module, remaining, recursive=False, cheap=False, **kw):
            calls.append((name, cheap))
            return 3, argparse.Namespace(state={"attempts": [], "stop_reason": "rounds exhausted"})
        h._attack_substatement = attack
        h.run_program()
        swept = [name for name, cheap in calls if cheap]
        self.assertEqual(swept, ["erdos_99_hyp_a"])           # only the easiest one, even though 3 are open
        sweep_ev = [e for e in h.log.events if e[1] == "sweep"]
        self.assertEqual(sweep_ev[0][2]["attempted"], 1)


class ProvedSweepIsSpliced(Isolated):
    """Test 2: a hypothesis the sweep proves is banked exactly like a certified depth child, logs via="sweep",
    and the (still open) rest is left for the depth phase -- whose own failure does NOT double-count."""

    def test_proved_hypothesis_is_spliced_and_counts_as_progress(self):
        h = _sweep_harness(self.root, SKEL_TWO, run_budget=5.0)
        h.spent_usd = lambda: 0.0
        calls = []

        def attack(sub, name, sdir, cycle, module, remaining, recursive=False, cheap=False, **kw):
            calls.append((name, cheap))
            if name == "erdos_99_hyp_a" and cheap:
                return 0, argparse.Namespace(state={"proof": PROOF_A})
            return 2, argparse.Namespace(state={"attempts": [], "stop_reason": "did not compile"})
        h._attack_substatement = attack
        rc = h.run_program()
        self.assertEqual(rc, 3)                               # hyp_b is still open: partial, not proved
        self.assertEqual(h.state["outcome"], "partial")
        # hyp_a: proved by the sweep, spliced, logged with via="sweep"
        discharged = [e for e in h.log.events if e[1] == "hypothesis_discharged"]
        self.assertEqual(len(discharged), 1)
        self.assertEqual(discharged[0][2]["name"], "erdos_99_hyp_a")
        self.assertEqual(discharged[0][2]["via"], "sweep")
        lemmas = (self.pdir() / "Lemmas.lean").read_text()
        self.assertIn("namespace erdos_99_hyp_a_ns", lemmas)
        residual = (self.pdir() / "Residual.lean").read_text()
        self.assertIn("erdos_99_hyp_a_ns.erdos_99_hyp_a", residual)
        self.assertTrue(h.state["program"]["certified_any"])
        # hyp_a is never attacked again by the depth phase; hyp_b is attacked (and fails) there, non-recursively
        self.assertEqual(calls, [("erdos_99_hyp_a", True), ("erdos_99_hyp_b", True), ("erdos_99_hyp_b", False)])
        failed = [e for e in h.log.events if e[1] == "hypothesis_failed"]
        self.assertEqual(len(failed), 1)
        self.assertEqual(failed[0][2]["name"], "erdos_99_hyp_b")
        # the sweep's own failure on hyp_b is recorded but excluded from failure_counts
        self.assertEqual(H.failure_counts(self.pdir()), {"erdos_99_hyp_b": 1})   # only the DEPTH failure counts
        sweep_failed = [e for e in h.log.events if e[1] == "sweep_failed"]
        self.assertEqual(len(sweep_failed), 1)
        self.assertEqual(sweep_failed[0][2]["name"], "erdos_99_hyp_b")

    def test_sweep_alone_can_close_the_skeleton(self):
        h = _sweep_harness(self.root, SKEL_ONE, run_budget=5.0)
        h.spent_usd = lambda: 0.0

        def verify():
            h.state["verify"] = {"all_clear": True}
            return h.state["verify"]
        h.stage_verify = verify
        h._attack_substatement = lambda *a, cheap=False, **k: (
            (0, argparse.Namespace(state={"proof": PROOF_A})) if cheap else (3, argparse.Namespace(state={})))
        rc = h.run_program()
        self.assertEqual(rc, 0)
        self.assertEqual(h.state["outcome"], "proved")
        self.assertEqual(H.hole_count(h.state["proof"]), 0)
        via_sweep = [e for e in h.log.events if e[1] == "hypothesis_discharged"]
        self.assertEqual(via_sweep[0][2]["via"], "sweep")


class FailureCountsExcludeSweep(unittest.TestCase):
    """Test 4 (pure): a cheap one-shot sweep failure is weak evidence and must not affect the attack order or
    the recursion decision the way a real (depth) failure does."""

    def test_sweep_kind_is_excluded_but_others_are_not(self):
        with tempfile.TemporaryDirectory() as tmp:
            pdir = Path(tmp)
            H.record_failure(pdir, {"name": "erdos_99_hyp_a", "kind": "sweep", "cycle": 1})
            H.record_failure(pdir, {"name": "erdos_99_hyp_a", "kind": "sweep", "cycle": 2})
            H.record_failure(pdir, {"name": "erdos_99_hyp_b", "cycle": 1})
            H.record_failure(pdir, {"name": "erdos_99_hyp_c", "kind": "skeleton", "cycle": 1})
            self.assertEqual(H.failure_counts(pdir), {"erdos_99_hyp_b": 1})


class AlreadySweptIsNotSweptAgain(Isolated):
    """Test 3: a hypothesis text already in self.state["swept"] is skipped -- in a later cycle of the same
    run, and (simulated via a pre-populated state, exactly how a resume would load it) after a resume."""

    def test_not_swept_again_in_a_later_cycle(self):
        h = _sweep_harness(self.root, SKEL_ONE, research_cycles=2, run_budget=1.0)
        h.spent_usd = lambda: 0.5           # $0.50 left: above the sweep floor (0.3), below min_child_budget (2.5)
        calls = []

        def attack(sub, name, sdir, cycle, module, remaining, recursive=False, cheap=False, **kw):
            calls.append((name, cheap, cycle))
            return 3, argparse.Namespace(state={"attempts": [], "stop_reason": "rounds exhausted"})
        h._attack_substatement = attack
        h.run_program()
        # attempted (and marked swept) once in cycle 1; skipped in cycle 2; the depth phase never runs at all
        # (min_child_budget=2.5 > $0.50 left), so every recorded call is the sweep's
        self.assertEqual(calls, [("erdos_99_hyp_a", True, 1)])
        sweep_ev = [e for e in h.log.events if e[1] == "sweep"]
        self.assertEqual([e[2]["attempted"] for e in sweep_ev], [1, 0])
        self.assertIn("swept", h.state)
        self.assertEqual(len(h.state["swept"]), 1)

    def test_not_swept_again_after_a_resume(self):
        sub = H.hypothesis_substatement(SKEL_ONE, "erdos_99_hyp_a")
        key = H.sweep_key(sub)
        h = _sweep_harness(self.root, SKEL_ONE, run_budget=5.0)
        h.spent_usd = lambda: 0.0
        h.state["swept"] = {key: {"name": "erdos_99_hyp_a", "cycle": 1, "proved": False, "spent": 0.05}}
        calls = []

        def attack(sub, name, sdir, cycle, module, remaining, recursive=False, cheap=False, **kw):
            calls.append((name, cheap))
            return 3, argparse.Namespace(state={"attempts": [], "stop_reason": "rounds exhausted"})
        h._attack_substatement = attack
        h.run_program()
        self.assertFalse(any(cheap for _, cheap in calls))    # the sweep never re-attempts the loaded hash
        sweep_ev = [e for e in h.log.events if e[1] == "sweep"]
        self.assertEqual(sweep_ev[0][2]["attempted"], 0)


class SweepOffReproducesOldBehaviour(Isolated):
    """Test 6: --sweep off skips the whole mechanism -- no cheap calls, no `swept` state, no sweep* log events."""

    def test_sweep_off(self):
        h = _sweep_harness(self.root, SKEL_TWO, sweep="off", run_budget=5.0)
        h.spent_usd = lambda: 0.0
        calls = []

        def attack(sub, name, sdir, cycle, module, remaining, recursive=False, cheap=False, **kw):
            calls.append((name, cheap))
            return 3, argparse.Namespace(state={"attempts": [], "stop_reason": "rounds exhausted"})
        h._attack_substatement = attack
        h.run_program()
        self.assertTrue(calls)                                 # the depth phase still ran
        self.assertTrue(all(not cheap for _, cheap in calls))  # but never through the cheap sweep path
        self.assertNotIn("swept", h.state)
        self.assertFalse(any(str(e[1]).startswith("sweep") for e in h.log.events))


class AttackSubstatementCaps(unittest.TestCase):
    """Test 5: the REAL _attack_substatement (not mocked) builds cargs correctly for both a normal (depth)
    child -- Change B's --attack-rounds/--attack-decompose-rounds -- and a cheap (sweep) child -- Change A's
    fixed one-shot shape and --sweep-budget cap. `Harness` itself is patched out so no subprocess or model
    call is made; `_attack_substatement` only ever reads `cargs` off of what it constructs and passes to it."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)

    def _harness(self):
        h = _stub(self.tmp.name)
        h.args.rounds, h.args.decompose_rounds, h.args.agentic = 6, 10, "escalate"
        h.args.attack_rounds, h.args.attack_decompose_rounds = 2, 0
        h.args.sweep_budget = 0.6
        h.args.run_budget = 5.0
        h.spent_usd = lambda: 0.0
        h.direction = None
        return h

    @staticmethod
    def _fake_child_class(captured):
        class FakeChild:
            BudgetExhausted = H.Harness.BudgetExhausted

            def __init__(self, cargs):
                captured.append(cargs)
                self.cargs = cargs
                self.imports = []
                self.state = {}

            def run(self):
                return 3
        return FakeChild

    def _attack(self, h, sdir_name, **kw):
        captured = []
        with patch.object(H, "Harness", self._fake_child_class(captured)):
            rc, child = h._attack_substatement("theorem x : True := by\n  sorry", "erdos_99_hyp_a",
                                               Path(self.tmp.name) / sdir_name, 1, None, 1, **kw)
        return rc, child, captured

    def test_depth_child_gets_change_b_caps(self):
        h = self._harness()
        rc, child, captured = self._attack(h, "sdir-depth", recursive=False)
        self.assertEqual(len(captured), 1)
        self.assertEqual(captured[0].rounds, 2)              # min(6, attack_rounds=2)
        self.assertEqual(captured[0].decompose_rounds, 0)    # min(10, attack_decompose_rounds=0)
        self.assertEqual(captured[0].agentic, "escalate")    # untouched by Change B
        self.assertEqual(rc, 3)

    def test_sweep_child_is_one_shot_no_agentic_no_decompose(self):
        h = self._harness()
        rc, child, captured = self._attack(h, "sdir-sweep", recursive=False, cheap=True)
        self.assertEqual(len(captured), 1)
        self.assertEqual(captured[0].rounds, 1)
        self.assertEqual(captured[0].agentic, "off")
        self.assertEqual(captured[0].decompose_rounds, 0)
        self.assertEqual(captured[0].run_budget, 0.6)        # min(left=5.0, sweep_budget=0.6)

    def test_sweep_child_budget_follows_the_sweep_budget_flag(self):
        h = self._harness()
        h.args.sweep_budget = 0.2
        rc, child, captured = self._attack(h, "sdir-sweep2", recursive=False, cheap=True)
        self.assertEqual(captured[0].run_budget, 0.2)

    def test_sweep_child_budget_never_exceeds_what_is_left(self):
        h = self._harness()
        h.spent_usd = lambda: 4.8            # only $0.20 left: below the sweep floor (0.3)
        rc, child, captured = self._attack(h, "sdir-sweep3", recursive=False, cheap=True)
        self.assertEqual((rc, child), (None, None))
        self.assertEqual(captured, [])       # no child constructed at all

    def test_recursive_child_is_not_capped_by_change_b(self):
        h = self._harness()
        rc, child, captured = self._attack(h, "sdir-rec", recursive=True)
        self.assertEqual(captured[0].rounds, 6)              # untouched: a recursive child runs its own loop
        self.assertEqual(captured[0].decompose_rounds, 10)

    def test_attack_rounds_flag_restores_old_behaviour(self):
        h = self._harness()
        h.args.attack_rounds, h.args.attack_decompose_rounds = 6, 10
        rc, child, captured = self._attack(h, "sdir-restore", recursive=False)
        self.assertEqual(captured[0].rounds, 6)
        self.assertEqual(captured[0].decompose_rounds, 10)


class CLIDefaults(unittest.TestCase):
    """Test 7: the new defaults (Change A/B/C), and the flags that restore the old behaviour, on the real
    argparse parser -- not just re-declared in a test, but read back from `build_parser()` itself."""

    def test_new_defaults(self):
        args = H.build_parser().parse_args(["run", "--problem", "1"])
        self.assertEqual(args.refute, "changed")             # Change C: was "auto"
        self.assertEqual(args.premise_attack, "full")        # back to full (2026-09-30): #678's last premise
        self.assertEqual(args.sweep, "off")                 # the train replay proved 0 of 9 deferred steps
        self.assertEqual(args.sweep_budget, 0.6)
        self.assertEqual(args.sweep_max, 8)
        self.assertEqual(args.attack_rounds, 2)
        self.assertEqual(args.attack_decompose_rounds, 0)

    def test_flags_restore_the_old_behaviour(self):
        args = H.build_parser().parse_args(["run", "--problem", "1", "--refute", "auto", "--premise-attack", "full",
                                            "--sweep", "off", "--attack-rounds", "6",
                                            "--attack-decompose-rounds", "10"])
        self.assertEqual(args.refute, "auto")
        self.assertEqual(args.premise_attack, "full")
        self.assertEqual(args.sweep, "off")
        self.assertEqual(args.attack_rounds, 6)
        self.assertEqual(args.attack_decompose_rounds, 10)


# Change D: name the exact missing sub-goal. This exact text is what real Lean printed for the macros below,
# captured in formal/ on 2026-09-26 (see the report): `extract_goal`'s own output has no `file:line:col:` of
# its own, so it lands as a continuation of whatever diagnostic happened to be open, never in its own `info`
# entry -- which is why the parser below reads raw compiler output, not res["infos"].
REAL_LEAN_RAW_SAMPLE = """theorem test_tactic_pos.extracted_1_1 (n : ℕ) : n = n := sorry
/private/tmp/xsorry_probe_check.lean:8:8: warning: declaration uses `sorry`
theorem test_term_pos.extracted_1_1 (n : ℕ) : n = n := sorry
/private/tmp/xsorry_probe_check.lean:11:8: warning: declaration uses `sorry`
theorem test_multi.extracted_1_1 (n m : ℕ) (h : n ≤ m) : n = n := sorry
theorem test_multi.extracted_1_3 (n m : ℕ) (h : n ≤ m) : m = m := sorry
/private/tmp/xsorry_probe_check.lean:13:8: warning: declaration uses `sorry`
"""


class ParseExtractedSubgoals(unittest.TestCase):
    """Pure parsing, on the fixed real-Lean sample above (required whether or not real Lean can be run here;
    see also RealLeanExtraction below, which regenerates this exact sample live)."""

    def test_parses_every_extracted_theorem_in_order(self):
        got = H.parse_extracted_subgoals(REAL_LEAN_RAW_SAMPLE)
        self.assertEqual(got, [
            "theorem test_tactic_pos.extracted_1_1 (n : ℕ) : n = n := sorry",
            "theorem test_term_pos.extracted_1_1 (n : ℕ) : n = n := sorry",
            "theorem test_multi.extracted_1_1 (n m : ℕ) (h : n ≤ m) : n = n := sorry",
            "theorem test_multi.extracted_1_3 (n m : ℕ) (h : n ≤ m) : m = m := sorry",
        ])

    def test_respects_the_limit(self):
        self.assertEqual(len(H.parse_extracted_subgoals(REAL_LEAN_RAW_SAMPLE, limit=2)), 2)

    def test_empty_or_no_match_is_empty(self):
        self.assertEqual(H.parse_extracted_subgoals(""), [])
        self.assertEqual(H.parse_extracted_subgoals("no relevant output here"), [])


class WithExtractGoalMacros(unittest.TestCase):
    def test_inserts_after_the_composed_header_and_replaces_every_sorry(self):
        src = H.compose("theorem t : True := by\n  sorry", ["Mathlib.Tactic"])
        out = H.with_extract_goal_macros(src)
        self.assertIn("import Mathlib.Tactic", out)
        self.assertIn('macro "xsorry" : tactic', out)
        self.assertIn('macro "xsorry" : term', out)
        self.assertNotIn("\n  sorry", out)                 # the body's sorry became xsorry
        self.assertIn("xsorry", out.splitlines()[-1])
        # the header precedes the macros, which precede the body
        self.assertLess(out.index("import Mathlib.Tactic"), out.index('macro "xsorry"'))
        self.assertLess(out.index('macro "xsorry"'), out.index("theorem t"))

    def test_falls_back_to_after_the_imports_with_no_recognized_header(self):
        src = "import Mathlib.Tactic\nimport Mathlib.Data.Nat.Basic\n\ntheorem t : True := by\n  sorry"
        out = H.with_extract_goal_macros(src)
        self.assertLess(out.index("import Mathlib.Data.Nat.Basic"), out.index('macro "xsorry"'))
        self.assertLess(out.index('macro "xsorry"'), out.index("theorem t"))
        self.assertIn("xsorry", out)

    def test_macro_bodies_are_not_themselves_mangled(self):
        # the macros' own RHS contains the literal word "sorry" twice; only the BODY's sorry is replaced
        out = H.with_extract_goal_macros(H.compose("theorem t : True := by\n  sorry", []))
        self.assertEqual(out.count("extract_goal; sorry"), 2)
        self.assertEqual(out.count("xsorry"), 3)            # 2 macro decls + 1 replaced site


class MissingSubgoalsMethod(unittest.TestCase):
    """The Harness method that ties the two pure pieces together: gated by --extract-subgoals, reads the best
    attempt off disk, and is best-effort (never raises, never blocks the run) if anything about that is
    missing or wrong."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.h = _stub(self.tmp.name)
        self.h.args.extract_subgoals = True
        self.child_dir = Path(self.tmp.name) / "child"
        (self.child_dir / "attempts").mkdir(parents=True)

    def _child(self):
        return argparse.Namespace(run_dir=self.child_dir)

    def _write_attempt(self, name, n_sorries):
        text = "theorem t : True := by\n" + "\n".join(["  sorry"] * n_sorries if n_sorries else ["  trivial"])
        (self.child_dir / "attempts" / f"{name}.lean").write_text(text)

    def test_off_by_default_returns_nothing(self):
        self.h.args.extract_subgoals = False
        self._write_attempt("a0", 1)
        digest = {"best_attempts": [{"name": "a0"}]}
        self.assertEqual(self.h._missing_subgoals(self._child(), digest, "tag"), [])

    def test_zero_or_too_many_sorries_are_skipped(self):
        self._write_attempt("zero", 0)
        self._write_attempt("many", 4)
        self.h.lean = type("L", (), {"check": lambda self, *a, **k: (_ for _ in ()).throw(AssertionError("should not check"))})()
        self.assertEqual(self.h._missing_subgoals(self._child(), {"best_attempts": [{"name": "zero"}]}, "t1"), [])
        self.assertEqual(self.h._missing_subgoals(self._child(), {"best_attempts": [{"name": "many"}]}, "t2"), [])

    def test_one_to_three_sorries_triggers_a_check_and_is_parsed(self):
        self._write_attempt("a0", 2)
        calls = []

        def fake_check(source, dest):
            calls.append(source)
            self.assertIn('macro "xsorry"', source)
            self.assertNotIn("  sorry", source)
            return {"ok": True, "raw": REAL_LEAN_RAW_SAMPLE, "errors": [], "warnings": [], "infos": [], "sorries": True}
        self.h.lean = type("L", (), {"check": staticmethod(fake_check)})()
        got = self.h._missing_subgoals(self._child(), {"best_attempts": [{"name": "a0"}]}, "extract-c1-0")
        self.assertEqual(len(calls), 1)
        self.assertEqual(got[0], "theorem test_tactic_pos.extracted_1_1 (n : ℕ) : n = n := sorry")

    def test_missing_attempt_file_is_swallowed(self):
        digest = {"best_attempts": [{"name": "does-not-exist"}]}
        self.assertEqual(self.h._missing_subgoals(self._child(), digest, "tag"), [])
        self.assertTrue(any(e[1] == "extract_subgoals_failed" for e in self.h.log.events))

    def test_no_best_attempt_or_no_run_dir_is_a_no_op(self):
        self.assertEqual(self.h._missing_subgoals(self._child(), {"best_attempts": []}, "tag"), [])
        self.assertEqual(self.h._missing_subgoals(argparse.Namespace(), {"best_attempts": [{"name": "a0"}]}, "tag"), [])

    def test_surfaced_under_proof_failures(self):
        with tempfile.TemporaryDirectory() as pdir_s:
            pdir = Path(pdir_s)
            H.record_failure(pdir, {"name": "erdos_99_hyp_a", "cycle": 1, "exit": 2, "attempts": 1,
                                    "stop_reason": "rounds exhausted", "unsolved_goals": [],
                                    "missing_subgoals": ["theorem erdos_99_hyp_a.extracted_1_1 (n : ℕ) : n = n := sorry"]})
            ctx = H.failures_context(pdir)
        self.assertIn("missing sub-goal (extract_goal): theorem erdos_99_hyp_a.extracted_1_1", ctx)


@unittest.skipUnless(os.environ.get("DEDUCTIVE_LEAN_TESTS") == "1", "set DEDUCTIVE_LEAN_TESTS=1 for real Lean checks")
class RealLeanExtraction(unittest.TestCase):
    """Regenerates REAL_LEAN_RAW_SAMPLE's underlying claim live: `extract_goal`, reached through the `xsorry`
    macros, really does print a named, typed, sorry'd copy of each replaced hole -- and the full method
    (macro-build -> real `lake env lean` check -> raw-text parse) recovers it end to end."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        h = H.Harness.__new__(H.Harness)
        h.problem = {"id": "99", "statement": "smoke", "tags": []}
        h.state = {}
        h.log = Log()
        h.run_dir = Path(self.tmp.name)
        h.args = argparse.Namespace(no_cascade=True, extract_subgoals=True)
        h.imports, h.libraries = list(H.DEFAULT_IMPORTS), []
        h.lean = H.LeanChecker(H.FORMAL, 420)
        h._lock = threading.Lock()
        h.checks = 0
        self.h = h

    def test_extract_goal_macros_compile_and_are_parsed(self):
        source = H.compose("theorem probe_extract (n m : ℕ) (h : n ≤ m) : n = n ∧ m = m := by\n"
                           "  constructor\n  sorry\n  sorry", self.h.imports)
        res = self.h.lean.check(H.with_extract_goal_macros(source), self.h.run_dir / "probe.lean")
        self.assertTrue(res["ok"])
        got = H.parse_extracted_subgoals(res["raw"])
        self.assertEqual(len(got), 2)
        self.assertTrue(all("probe_extract.extracted_" in g and g.endswith(":= sorry") for g in got))

    def test_missing_subgoals_end_to_end(self):
        (self.h.run_dir / "attempts").mkdir(parents=True)
        source = H.compose("theorem probe_extract2 (n : ℕ) : n = n ∧ n + 0 = n := by\n"
                           "  refine ⟨?_, ?_⟩\n  sorry\n  sorry", self.h.imports)
        (self.h.run_dir / "attempts" / "a0.lean").write_text(source)
        child = argparse.Namespace(run_dir=self.h.run_dir)
        got = self.h._missing_subgoals(child, {"best_attempts": [{"name": "a0"}]}, "extract-probe2")
        self.assertEqual(len(got), 2)
        self.assertTrue(all("probe_extract2.extracted_" in g for g in got))


if __name__ == "__main__":
    unittest.main()


class RestoreOmittedFrozen(unittest.TestCase):
    """A one-round sweep attempt used to die on a formatting slip: the sub-statement carries a `def` of the
    skeleton's context that the hypothesis never uses, the attempt drops it, and the frozen guard rejects the
    attempt without compiling it (train #283 `hyp_egypt`, all three one-shot attempts)."""
    FROZEN = ("open Filter Polynomial\n\ndef Condition (p : ℚ[X]) : Prop :=\n  p.leadingCoeff > 0\n\n"
              "theorem erdos_1_hyp_e :\n    ∀ k : ℕ, 3 ≤ k → k ≠ 0 :=")

    def test_an_omitted_unused_def_is_restored_verbatim(self):
        attempt = ("open Filter Polynomial\n\nprivate lemma aux : True := trivial\n\n"
                   "theorem erdos_1_hyp_e :\n    ∀ k : ℕ, 3 ≤ k → k ≠ 0 := by\n  intro k hk; omega\n")
        self.assertFalse(H.contains_frozen(attempt, self.FROZEN))
        fixed = H.restore_omitted_frozen(attempt, self.FROZEN)
        self.assertTrue(H.contains_frozen(fixed, self.FROZEN))
        self.assertIn("def Condition (p : ℚ[X]) : Prop :=", fixed)
        self.assertLess(fixed.index("def Condition"), fixed.index("private lemma aux"))   # after the header

    def test_a_redefined_def_is_never_replaced(self):
        attempt = ("open Filter Polynomial\n\ndef Condition (p : ℚ[X]) : Prop := True\n\n"
                   "theorem erdos_1_hyp_e :\n    ∀ k : ℕ, 3 ≤ k → k ≠ 0 := by\n  intro k hk; omega\n")
        self.assertEqual(H.restore_omitted_frozen(attempt, self.FROZEN), attempt)

    def test_an_altered_target_is_never_repaired(self):
        attempt = ("open Filter Polynomial\n\ntheorem erdos_1_hyp_e :\n    ∀ k : ℕ, 4 ≤ k → k ≠ 0 := by\n  omega\n")
        self.assertEqual(H.restore_omitted_frozen(attempt, self.FROZEN), attempt)

    def test_a_complete_attempt_is_unchanged(self):
        attempt = self.FROZEN + " by\n  intro k hk; omega\n"
        self.assertEqual(H.restore_omitted_frozen(attempt, self.FROZEN), attempt)


class CheapFallback(Isolated):
    """Train #678 (2026-09-30) certified 12 of 15 steps and ended with its last three elementary steps deferred for
    want of --min-child-budget, $2.44 unspent. A cheap one-shot proved all three for $0.73. The fallback gives every
    step the depth phase did not fund one cheap attempt with what is left, unless the plan rated it hard."""

    def _harness(self, skeleton, **kw):
        return _sweep_harness(self.root, skeleton, **{"sweep": "off", "cheap_fallback": "on", **kw})

    def test_a_budget_deferred_step_gets_one_cheap_attempt_after_the_depth_phase(self):
        h = self._harness(SKEL_THREE, min_child_budget=2.5, run_budget=5.0)
        h.spent_usd = lambda: 2.0          # $3.00 left: one depth child affordable, the other two deferred
        calls = []

        def attack(sub, name, sdir, cycle, module, remaining, recursive=False, cheap=False, **kw):
            calls.append((name, cheap))
            return 3, argparse.Namespace(state={"attempts": [], "stop_reason": "rounds exhausted"})
        h._attack_substatement = attack
        h.run_program()
        depth = [n for n, cheap in calls if not cheap]
        cheap = [n for n, cheap in calls if cheap]
        self.assertEqual(depth, ["erdos_99_hyp_a"])                        # the depth phase funded one
        self.assertEqual(cheap, ["erdos_99_hyp_b", "erdos_99_hyp_c"])      # the deferred two, cheaply, in order
        self.assertTrue(any(e[1] == "sweep" and e[2].get("via") == "fallback" for e in h.log.events))

    def test_a_cheap_proof_is_banked_and_can_close_the_skeleton(self):
        h = self._harness(SKEL_ONE, min_child_budget=2.5, run_budget=5.0)
        h.spent_usd = lambda: 3.0          # $2.00 left: the depth phase can fund nothing
        proof_state = {"proof": PROOF_A, "attempts": []}

        def attack(sub, name, sdir, cycle, module, remaining, recursive=False, cheap=False, **kw):
            self.assertTrue(cheap)         # only the fallback may run here
            return 0, argparse.Namespace(state=proof_state)
        h._attack_substatement = attack
        def bank(*a, **k):
            h.state["proof"] = a[2]        # as the real helper does when the skeleton closes
            return {"ok": True, "skeleton": a[2], "parsed": {**a[3], "hypotheses": []}, "proved": True}
        h._bank_certified = bank
        h.stage_verify = lambda: {"all_clear": True}
        h.run_program()
        self.assertTrue(any(e[1] == "sweep" and e[2].get("proved") == 1 and e[2].get("via") == "fallback"
                            for e in h.log.events))

    def test_hard_rated_and_already_attacked_steps_are_skipped(self):
        h = self._harness(SKEL_THREE, min_child_budget=2.5, run_budget=5.0)
        h.spent_usd = lambda: 2.0
        rated = {"erdos_99_hyp_c": "hard"}
        orig = H.parse_residual

        def parse(skel, pid, meta, main=None):
            p = orig(skel, pid, meta, main=main)
            for x in p["hypotheses"]:
                if x["name"] in rated:
                    x["difficulty"] = rated[x["name"]]
            return p
        calls = []

        def attack(sub, name, sdir, cycle, module, remaining, recursive=False, cheap=False, **kw):
            calls.append((name, cheap))
            return 3, argparse.Namespace(state={"attempts": [], "stop_reason": "rounds exhausted"})
        h._attack_substatement = attack
        with patch.object(H, "parse_residual", side_effect=parse):
            h.run_program()
        cheap = [n for n, c in calls if c]
        self.assertNotIn("erdos_99_hyp_c", cheap)                         # rated hard
        self.assertNotIn("erdos_99_hyp_a", cheap)                         # the depth phase already tried it
        self.assertEqual(cheap, ["erdos_99_hyp_b"])

    def test_off_restores_deferral(self):
        h = self._harness(SKEL_THREE, min_child_budget=2.5, run_budget=5.0, cheap_fallback="off")
        h.spent_usd = lambda: 2.0
        calls = []

        def attack(sub, name, sdir, cycle, module, remaining, recursive=False, cheap=False, **kw):
            calls.append((name, cheap))
            return 3, argparse.Namespace(state={"attempts": [], "stop_reason": "rounds exhausted"})
        h._attack_substatement = attack
        h.run_program()
        self.assertEqual([c for _, c in calls], [False])                  # one depth child, no cheap attempts

    def test_cli_default_is_on(self):
        args = H.build_parser().parse_args(["run", "--problem", "1"])
        self.assertEqual(args.cheap_fallback, "on")
