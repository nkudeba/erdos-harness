"""Cost-allocation options for the deductive research loop's cycle: `--refute changed` (skip the refute-first
script once the open conjecture hypotheses have not moved since the last run of this program) and
`--premise-attack` (full / cheap / off: what happens to open published premises once no conjecture is left to
attack). Both default to today's behaviour. No provider calls; Lean is mocked."""
import argparse, json, sys, tempfile, unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parent))
import harness as H
from test_deductive_mode import SKELETON, FROZEN, Log, _stub, _judged, JUDGE_OK


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


class OpenHypothesesSignature(unittest.TestCase):
    """The pure function --refute changed compares cycle to cycle: sha256 over sorted "name : statement" lines."""

    def test_order_independent(self):
        a = [{"name": "h1", "statement": "P"}, {"name": "h2", "statement": "Q"}]
        b = [{"name": "h2", "statement": "Q"}, {"name": "h1", "statement": "P"}]
        self.assertEqual(H.open_hypotheses_signature(a), H.open_hypotheses_signature(b))

    def test_sensitive_to_statement_and_name(self):
        base = [{"name": "h1", "statement": "P"}]
        self.assertNotEqual(H.open_hypotheses_signature(base), H.open_hypotheses_signature([{"name": "h1", "statement": "Q"}]))
        self.assertNotEqual(H.open_hypotheses_signature(base), H.open_hypotheses_signature([{"name": "h2", "statement": "P"}]))

    def test_empty_is_stable(self):
        self.assertEqual(H.open_hypotheses_signature([]), H.open_hypotheses_signature([]))


class RefuteChanged(Isolated):
    """--refute changed: the experiments step always runs on the first cycle of an invocation, and afterwards
    only when the set of open conjecture hypotheses of the skeleton in force has changed since the last run."""

    def _harness(self, refute):
        h = _stub(self.root / "run")
        h.args.refute = refute
        h.args.research_cycles = 2
        h._install_lemmas_module = lambda pdir: None
        h._attack_substatement = lambda *a, **k: (3, argparse.Namespace(state={}))
        pdir = self.pdir()
        pdir.mkdir(parents=True)
        (pdir / "Residual.lean").write_text(SKELETON)     # a skeleton already in force, unchanged cycle to cycle
        return h

    def test_changed_skips_when_hypotheses_are_unchanged(self):
        h = self._harness("changed")
        calls = []

        def experiments(cdir, cycle, hyp_txt):
            calls.append(cycle)
            return f"FINDING-FROM-CYCLE-{cycle}", {"refuted": [], "clear": [], "invariants": []}
        h._deductive_experiments = experiments
        plan_prompts = []

        def ask(purpose, prompt, **kw):
            if purpose == "plan":
                plan_prompts.append(prompt)
            return plan_reply(SKELETON)
        h.ask = _judged(ask)
        h.run_program()
        self.assertEqual(calls, [1])                                        # cycle 2 did not rerun the script
        skipped = [e for e in h.log.events if e[1] == "experiments_skipped"]
        self.assertEqual(len(skipped), 1)
        self.assertEqual(skipped[0][2]["cycle"], 2)
        self.assertEqual(skipped[0][2]["reason"], "open hypotheses unchanged since the last run")
        self.assertEqual(len(plan_prompts), 2)
        self.assertIn("FINDING-FROM-CYCLE-1", plan_prompts[1])              # cycle 2's plan still sees cycle 1's output
        self.assertEqual(h.state["last_refute_sig"], H.open_hypotheses_signature(
            [x for x in H.parse_residual(SKELETON, 99, main="erdos_99")["hypotheses"]
             if x["open"] and x["kind"] == "conjecture"]))
        self.assertEqual(h.state["last_refute_out"], "FINDING-FROM-CYCLE-1")

    def test_auto_runs_every_cycle(self):
        h = self._harness("auto")
        calls = []

        def experiments(cdir, cycle, hyp_txt):
            calls.append(cycle)
            return f"FINDING-FROM-CYCLE-{cycle}", {"refuted": [], "clear": [], "invariants": []}
        h._deductive_experiments = experiments
        h.ask = _judged(lambda purpose, prompt, **kw: plan_reply(SKELETON))
        h.run_program()
        self.assertEqual(calls, [1, 2])                                     # every cycle reran it
        self.assertFalse(any(e[1] == "experiments_skipped" for e in h.log.events))

    def test_off_never_runs_it(self):
        h = self._harness("off")
        calls = []
        h._deductive_experiments = lambda cdir, cycle, hyp_txt: (calls.append(cycle), ("", {}))[1]
        h.ask = _judged(lambda purpose, prompt, **kw: plan_reply(SKELETON))
        h.run_program()
        self.assertEqual(calls, [])
        self.assertFalse(any(e[1] == "experiments_skipped" for e in h.log.events))


CLOSED_HYP_A = "theorem erdos_99_hyp_a : ∀ n : ℕ, foo n := by\n  intro n\n  rfl"
# Only the published premise (erdos_99_hyp_rs) is still open: the conjecture hyp_a is already discharged, so
# `attack_order` (conjecture-only) returns nothing and the premise-attack branch is what runs each cycle.
ONLY_PREMISE_OPEN = H.splice_hypothesis(SKELETON, "erdos_99_hyp_a", CLOSED_HYP_A)
CLOSED_HYP_RS = "theorem erdos_99_hyp_rs : ∀ x : ℕ, 1 ≤ x → x ≤ x := by\n  intro x hx\n  exact le_refl x"
# The isolated sub-statement `_close_holes_without_model` is actually called with (`hypothesis_substatement`'s
# output). `_consider_skeleton` also calls the same method on the FULL candidate skeleton while adopting a plan
# (unrelated to premise-attack), which happens to contain "erdos_99_hyp_rs" as a substring too -- so the mocks
# below match this exact isolated text, never a bare substring, or they would rewrite the whole skeleton.
SUB_RS = H.hypothesis_substatement(ONLY_PREMISE_OPEN, "erdos_99_hyp_rs")


class PremiseAttack(Isolated):
    """Once no conjecture hypothesis is left, --premise-attack decides what happens to the open published
    premises: a full child (today's default), the free tactic cascade with no child (cheap), or nothing (off)."""

    def _harness(self, premise_attack):
        h = _stub(self.root / "run")
        h.args.premise_attack = premise_attack
        h.args.research_cycles = 1
        h._install_lemmas_module = lambda pdir: None
        h.stage_verify = lambda: None       # a fully closed residual would otherwise ask("backtranslate"/"faithful")
        pdir = self.pdir()
        pdir.mkdir(parents=True)
        (pdir / "Residual.lean").write_text(ONLY_PREMISE_OPEN)
        h.ask = _judged(lambda purpose, prompt, **kw: plan_reply(ONLY_PREMISE_OPEN))
        attacked = []

        def attack(sub, name, sdir, cycle, module, remaining, recursive=False, **kw):
            attacked.append(name)
            return 3, argparse.Namespace(state={})
        h._attack_substatement = attack
        h._attacked = attacked
        return h

    def test_cheap_splices_a_closable_premise_without_a_child(self):
        h = self._harness("cheap")
        h._close_holes_without_model = lambda code, frozen: CLOSED_HYP_RS if code == SUB_RS else code
        h.run_program()
        self.assertEqual(h._attacked, [])                    # no child spawned for the premise
        discharged = [e for e in h.log.events if e[1] == "hypothesis_discharged"]
        self.assertEqual(len(discharged), 1)
        self.assertEqual(discharged[0][2]["name"], "erdos_99_hyp_rs")
        self.assertFalse(any(e[1] == "premise_kept" for e in h.log.events))
        final = (self.pdir() / "Residual.lean").read_text()
        self.assertIn("erdos_99_hyp_rs_ns", final)
        self.assertEqual(H.hole_count(final), 0)

    def test_cheap_keeps_a_premise_the_cascade_cannot_close(self):
        h = self._harness("cheap")
        h._close_holes_without_model = lambda code, frozen: code      # closes nothing; still has its sorry
        h.run_program()
        self.assertEqual(h._attacked, [])
        kept = [e for e in h.log.events if e[1] == "premise_kept"]
        self.assertEqual(len(kept), 1)
        self.assertEqual(kept[0][2]["name"], "erdos_99_hyp_rs")
        self.assertEqual(kept[0][2]["reason"], "the free tactics do not close it")
        self.assertFalse(any(e[1] == "hypothesis_discharged" for e in h.log.events))
        self.assertIn("sorry", (self.pdir() / "Residual.lean").read_text())

    def test_off_never_attacks_premises(self):
        h = self._harness("off")
        closed_calls = []

        def close_holes(code, frozen):
            if code == SUB_RS:
                closed_calls.append(1)
            return code
        h._close_holes_without_model = close_holes
        h.run_program()
        self.assertEqual(h._attacked, [])
        self.assertEqual(closed_calls, [])                   # the cascade is never even tried on the premise
        not_attacked = [e for e in h.log.events if e[1] == "premises_not_attacked"]
        self.assertEqual(len(not_attacked), 1)
        self.assertEqual(not_attacked[0][2]["names"], ["erdos_99_hyp_rs"])
        self.assertFalse(any(e[1] in ("hypothesis_discharged", "premise_kept", "premises_attacked")
                             for e in h.log.events))

    def test_full_is_the_default_and_attacks_a_child(self):
        h = self._harness("full")
        h.run_program()
        self.assertEqual(h._attacked, ["erdos_99_hyp_rs"])   # today's behaviour: a full child is spawned
        attacked_ev = [e for e in h.log.events if e[1] == "premises_attacked"]
        self.assertEqual(len(attacked_ev), 1)
        self.assertEqual(attacked_ev[0][2]["names"], ["erdos_99_hyp_rs"])

    def test_premise_attack_defaults_to_full_when_unset(self):
        # An older stub (or any caller not yet updated for this flag) leaves args.premise_attack unset entirely;
        # the getattr fallback in harness.py must still reproduce today's behaviour.
        h = self._harness("full")
        del h.args.premise_attack
        h.run_program()
        self.assertEqual(h._attacked, ["erdos_99_hyp_rs"])



class PremiseEndgame(Isolated):
    """Train #678's third run (2026-10-01) certified every conjecture with two published premises left (Nair 1982,
    Nagura 1952). Cycles 4 and 5 spent its last $2.70 on experiments and re-plans of a closed skeleton, then deferred
    both premises at $1.33 and $0.48. In the endgame the loop no longer refutes or re-plans, and the last premise
    attack is funded with whatever is left (at least $1), instead of being deferred."""

    def _run(self, spent: float):
        h = _stub(self.root / "run")
        h.args.premise_attack = "full"
        h.args.refute = "auto"                     # would run the experiments, were it not the endgame
        h.args.research_cycles = 1
        h.args.min_child_budget = 2.5
        h.spent_usd = lambda: spent
        h._install_lemmas_module = lambda pdir: None
        h.stage_verify = lambda: None
        pdir = self.pdir()
        pdir.mkdir(parents=True, exist_ok=True)
        (pdir / "Residual.lean").write_text(ONLY_PREMISE_OPEN)
        purposes, experiments, attacked = [], [], []
        h.ask = _judged(lambda purpose, prompt, **kw: purposes.append(purpose) or plan_reply(ONLY_PREMISE_OPEN))
        h._deductive_experiments = (lambda *a, **k: experiments.append(1)
                                    or ("", {"refuted": [], "clear": [], "invariants": []}))

        def attack(sub, name, sdir, cycle, module, remaining, recursive=False, **kw):
            attacked.append(name)
            return 3, argparse.Namespace(state={})
        h._attack_substatement = attack
        h.run_program()
        return h, attacked, purposes, experiments

    def test_no_refutation_and_no_replan_in_the_endgame(self):
        h, attacked, purposes, experiments = self._run(spent=1.0)
        self.assertEqual(experiments, [])
        self.assertNotIn("plan", purposes)
        self.assertTrue(any(e[1] == "premise_endgame" for e in h.log.events))
        self.assertEqual(attacked, ["erdos_99_hyp_rs"])

    def test_the_last_premise_is_attacked_with_what_is_left(self):
        _, attacked, _, _ = self._run(spent=3.67)   # $1.33 left: below --min-child-budget, above the $1 floor
        self.assertEqual(attacked, ["erdos_99_hyp_rs"])

    def test_below_a_dollar_it_is_still_deferred(self):
        _, attacked, _, _ = self._run(spent=4.52)   # $0.48 left
        self.assertEqual(attacked, [])


if __name__ == "__main__":
    unittest.main()

