"""The deductive research loop (docs/deductive-research-mode.md): the unit of progress is a certified
CONDITIONAL THEOREM whose open hypotheses are the residual. No provider calls; Lean is mocked."""
import argparse, json, sys, tempfile, unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "atlas-data"))
import harness as H
import campaign as C


SKELETON = """def foo (n : ℕ) : Prop := n = n

-- derived: a counterexample would have to violate reflexivity
theorem erdos_99_hyp_a : ∀ n : ℕ, foo n := by
  sorry

-- PUBLISHED: Rosser–Schoenfeld 1962, Corollary 3
theorem erdos_99_hyp_rs : ∀ x : ℕ, 1 ≤ x → x ≤ x := by
  sorry

theorem erdos_99_hyp_done : True := by
  trivial

theorem erdos_99 : ∀ n : ℕ, foo n := by
  intro n
  exact erdos_99_hyp_a n"""

FROZEN = "theorem erdos_99 : ∀ n : ℕ, foo n := by\n  sorry"


class Log:
    def __init__(self):
        self.events = []
    def event(self, stage, event, **kw):
        self.events.append((stage, event, kw))


class ResidualParsing(unittest.TestCase):
    """A skeleton is real only if every sorry sits inside a hypothesis; kinds come from the tag or the ledger."""

    def test_hypotheses_kinds_and_metric(self):
        r = H.parse_residual(SKELETON, 99)
        names = [h["name"] for h in r["hypotheses"]]
        self.assertEqual(names, ["erdos_99_hyp_a", "erdos_99_hyp_rs", "erdos_99_hyp_done"])
        by = {h["name"]: h for h in r["hypotheses"]}
        self.assertEqual(by["erdos_99_hyp_a"]["kind"], "conjecture")
        self.assertEqual(by["erdos_99_hyp_rs"]["kind"], "published")
        self.assertIn("Rosser", by["erdos_99_hyp_rs"]["source"])
        self.assertFalse(by["erdos_99_hyp_done"]["open"])
        self.assertTrue(r["glue_sorry_free"] and r["main_present"])
        self.assertEqual(r["metric"]["open_conjectures"], 1)
        self.assertEqual(r["metric"]["published"], 1)
        self.assertEqual(r["metric"]["certified"], 1)
        self.assertEqual(by["erdos_99_hyp_a"]["statement"], "∀ n : ℕ, foo n")

    def test_published_without_a_source_is_just_a_conjecture(self):
        skel = SKELETON.replace("-- PUBLISHED: Rosser–Schoenfeld 1962, Corollary 3\n", "")
        meta = {"hypotheses": [{"name": "erdos_99_hyp_rs", "kind": "published"}]}   # claims published, cites nothing
        by = {h["name"]: h for h in H.parse_residual(skel, 99, meta)["hypotheses"]}
        self.assertEqual(by["erdos_99_hyp_rs"]["kind"], "conjecture")

    def test_a_sorry_in_the_glue_is_detected(self):
        skel = SKELETON.replace("  intro n\n  exact erdos_99_hyp_a n", "  sorry")
        self.assertFalse(H.parse_residual(skel, 99)["glue_sorry_free"])

    def test_improvement_order(self):
        def m(o, p, c, mx=None):
            return {"metric": {"open_conjectures": o, "published": p, "complexity": c, "certified": 0,
                               "max_complexity": mx if mx is not None else c}}
        self.assertTrue(H.residual_improves(m(1, 0, 9), None))
        # #645 lesson: four elementary lemmas (max 17) beat one compactness hypothesis (max 25)
        self.assertTrue(H.residual_improves(m(4, 0, 60, mx=17), m(1, 0, 25, mx=25)))
        self.assertFalse(H.residual_improves(m(1, 0, 25, mx=25), m(4, 0, 60, mx=17)))
        self.assertTrue(H.residual_improves(m(1, 0, 9, mx=9), m(2, 0, 18, mx=9)))    # same hard core: fewer wins
        self.assertTrue(H.residual_improves(m(1, 0, 9, mx=9), m(1, 1, 9, mx=9)))     # then fewer published premises
        self.assertTrue(H.residual_improves(m(2, 0, 12, mx=9), m(2, 0, 18, mx=9)))   # then lower total complexity
        self.assertFalse(H.residual_improves(m(1, 0, 9), m(1, 0, 9)))                # a tie is not progress

    def test_metric_reports_the_hardest_open_conjecture(self):
        r = H.parse_residual(SKELETON, 99)
        self.assertEqual(r["metric"]["max_complexity"], r["hypotheses"][0]["complexity"])

    def test_substatement_is_self_contained_and_open(self):
        sub = H.hypothesis_substatement(SKELETON, "erdos_99_hyp_a")
        self.assertIn("def foo", sub)
        self.assertIn("theorem erdos_99_hyp_a : ∀ n : ℕ, foo n := by\n  sorry", sub)
        self.assertNotIn("theorem erdos_99 ", sub)
        self.assertEqual(H.hole_count(sub), 1)

    def test_splice_discharges_a_hypothesis_without_duplicating_defs(self):
        proof = ("def foo (n : ℕ) : Prop := n = n\n\nprivate lemma helper : True := trivial\n\n"
                 "theorem erdos_99_hyp_a : ∀ n : ℕ, foo n := by\n  intro n\n  rfl")
        spliced = H.splice_hypothesis(SKELETON, "erdos_99_hyp_a", proof)
        self.assertIn("namespace erdos_99_hyp_a_ns", spliced)
        self.assertEqual(spliced.count("def foo"), 1)
        self.assertIn("exact erdos_99_hyp_a_ns.erdos_99_hyp_a", spliced)
        r = H.parse_residual(spliced, 99)
        by = {h["name"]: h for h in r["hypotheses"]}
        self.assertFalse(by["erdos_99_hyp_a"]["open"])
        self.assertEqual(len(r["hypotheses"]), 3)                          # the namespaced copy is not a second hypothesis
        self.assertEqual(r["metric"]["open_conjectures"], 0)
        self.assertTrue(r["glue_sorry_free"])
        # the remaining hypotheses can still be located after the splice
        self.assertIsNotNone(H.hypothesis_substatement(spliced, "erdos_99_hyp_rs"))

    def test_refutation_output_protocol(self):
        out = ('EXP: hello\nREFUTED: {"hypothesis": "erdos_99_hyp_a", "witness": {"n": 3}}\n'
               'CLEAR: {"hypothesis": "erdos_99_hyp_rs", "checked_to": 1000, "parameter": "x"}\n'
               'DERIVATION: a class with even modulus lies in one parity class, so ...\n'
               'INVARIANT: every near-miss has n divisible by 4 (n <= 5000)\n'
               'OBSERVED: the count of survivors is decreasing after n = 18\nREFUTED: not json\n')
        r = H.parse_refutation_output(out)
        self.assertEqual(r["refuted"], [{"hypothesis": "erdos_99_hyp_a", "witness": {"n": 3}}])
        self.assertEqual(r["clear"][0]["checked_to"], 1000)
        self.assertEqual(len(r["invariants"]), 1)
        self.assertEqual(r["derivations"][0]["derivation"][:7], "a class")      # derive first, check second
        self.assertEqual(len(r["observed"]), 1)                                # an observation is not a hypothesis

    def test_experiments_prompt_derives_before_checking(self):
        text = H.EXPERIMENTS_PROMPT.format(pid="99", statement_en="s", statement="t", literature="l",
                                           hypotheses="- h : P", refuted="(none)")
        for want in ("DERIVE FIRST, CHECK SECOND", "DERIVATION:", "OBSERVED:", "never a hypothesis until someone derives it"):
            self.assertIn(want, text)

    def test_sub_residual_target_is_the_main_theorem_not_a_hypothesis(self):
        """Inside a sub-residual the frozen target is itself named erdos_99_hyp_a; it must be the glue."""
        skel = ("theorem erdos_99_hyp_a_hyp_step : ∀ n : ℕ, n = n := by\n  sorry\n\n"
                "theorem erdos_99_hyp_a : ∀ n : ℕ, n = n := by\n  intro n\n  exact erdos_99_hyp_a_hyp_step n")
        r = H.parse_residual(skel, 99, main="erdos_99_hyp_a")
        self.assertTrue(r["main_present"] and r["glue_sorry_free"])
        self.assertEqual([h["name"] for h in r["hypotheses"]], ["erdos_99_hyp_a_hyp_step"])
        wrong = H.parse_residual(skel, 99)                  # without main, the target reads as a hypothesis
        self.assertFalse(wrong["main_present"])


class AttackOrder(unittest.TestCase):
    """Easiest first means the plan's rating first; a short statement can be the hardest mathematics."""

    def test_rating_beats_complexity(self):
        meta = {"hypotheses": [{"name": "erdos_99_hyp_a", "difficulty": "hard"},
                               {"name": "erdos_99_hyp_rs", "kind": "published", "source": "RS"}]}
        skel = SKELETON.replace("theorem erdos_99_hyp_done : True := by\n  trivial",
                                "theorem erdos_99_hyp_b : ∀ n : ℕ, ∀ m : ℕ, foo n ∧ foo m := by\n  sorry")
        r = H.parse_residual(skel, 99, meta)
        by = {h["name"]: h for h in r["hypotheses"]}
        self.assertEqual(by["erdos_99_hyp_a"]["difficulty"], "hard")
        self.assertEqual(by["erdos_99_hyp_b"]["difficulty"], "unrated")
        self.assertGreater(by["erdos_99_hyp_b"]["complexity"], by["erdos_99_hyp_a"]["complexity"])
        self.assertEqual([h["name"] for h in H.attack_order(r["hypotheses"])], ["erdos_99_hyp_b", "erdos_99_hyp_a"])

    def test_plan_prompt_asks_for_a_rating(self):
        text = H.PLAN_PROMPT.format(pid="99", statement_en="s", statement="t", literature="l", library="",
                                    lemmas="", residual="", experiments="", refuted="", ledger="", cycle=1,
                                    hyp_prefix="erdos_99_hyp_", failures="(none yet)")
        self.assertIn('"difficulty"', text)


class FailureFeedback(unittest.TestCase):
    """A failed attempt is analysed, banked and fed to the next plan; repeat failures sink in the attack order."""

    def test_digest_and_context(self):
        state = {"attempts": [
            {"name": "proof-r1-a0", "compiled": False, "n_sorries": 0, "errors": ["line 9:2: unsolved goals\n⊢ 2 ∣ q a\n", "type mismatch"]},
            {"name": "proof-r1-a1", "compiled": True, "n_sorries": 2, "errors": [], "summary": "needs a lemma about parity of u a - u b"},
            {"name": "bad", "rejected": True, "errors": ["altered the frozen theorem"]}],
            "critic_r1": "CRITIC NOTES: closest plan split on parity but lacked the halving lemma",
            "stop_reason": "rounds exhausted", "decomposition": {"errors": ["omega failed"]}}
        d = H.failure_digest(state, "erdos_99_hyp_a", "∀ n, P n", 1, 2)
        self.assertEqual(d["attempts"], 3)
        self.assertEqual(d["rejected_attempts"], 1)
        self.assertEqual(d["best_attempts"][0]["name"], "proof-r1-a1")     # compiled-with-sorries ranks first
        only_rejected = {"attempts": [{"name": "bad", "rejected": True, "errors": ["attempt altered the frozen theorem statement"]}]}
        d2 = H.failure_digest(only_rejected, "erdos_99_hyp_a", "∀ n, P n", 1, 2)
        self.assertEqual(d2["best_attempts"][0]["errors"], ["attempt altered the frozen theorem statement"])
        self.assertEqual(d["unsolved_goals"], ["⊢ 2 ∣ q a"])
        self.assertIn("halving lemma", d["diagnosis"])
        self.assertIn("needs a lemma", d["diagnosis"])
        with tempfile.TemporaryDirectory() as tmp:
            pdir = Path(tmp)
            self.assertEqual(H.failures_context(pdir), "(none yet)")
            H.record_failure(pdir, d)
            H.record_failure(pdir, d)
            ctx = H.failures_context(pdir)
            self.assertIn("unsolved goal: ⊢ 2 ∣ q a", ctx)
            self.assertIn("prover's diagnosis", ctx)
            self.assertEqual(H.failure_counts(pdir), {"erdos_99_hyp_a": 2})
            hyps = [{"name": "erdos_99_hyp_a", "open": True, "kind": "conjecture", "complexity": 1, "difficulty": "unrated"},
                    {"name": "erdos_99_hyp_b", "open": True, "kind": "conjecture", "complexity": 9, "difficulty": "unrated"}]
            self.assertEqual([h["name"] for h in H.attack_order(hyps, H.failure_counts(pdir))],
                             ["erdos_99_hyp_b", "erdos_99_hyp_a"])     # the twice-failed one goes last

    def test_plan_prompt_carries_failures_and_the_four_moves(self):
        text = H.PLAN_PROMPT.format(pid="99", statement_en="s", statement="t", literature="l", library="",
                                    lemmas="", residual="", experiments="", refuted="", ledger="", cycle=2,
                                    hyp_prefix="erdos_99_hyp_", failures="- erdos_99_hyp_a: unsolved goal ⊢ 2 ∣ q a")
        for want in ("PROOF FAILURES", "unsolved goal ⊢ 2 ∣ q a", "MOVES AFTER A FAILURE", "define", "failure_responses",
                     "from a failed proof"):
            self.assertIn(want, text)


class RefutedKnowledge(unittest.TestCase):
    """A refuted statement is banked with its witness and provenance and never re-proposed."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self._old = H.KNOWLEDGE
        H.KNOWLEDGE = Path(self.tmp.name)
    def tearDown(self):
        H.KNOWLEDGE = self._old
        self.tmp.cleanup()

    def test_record_load_and_block(self):
        self.assertEqual(H.refuted_context(99), "(none)")
        H.record_refutation(99, "erdos_99_hyp_a", "∀ n : ℕ, foo n", {"n": 3}, "cycles/c1/experiments.py", 1)
        rs = H.load_refutations(99)
        self.assertEqual(len(rs), 1)
        self.assertFalse(rs[0]["certified"])
        self.assertIn("NOT a Lean-certified", rs[0]["note"])
        self.assertIn("erdos_99_hyp_a", H.refuted_context(99))
        self.assertIsNotNone(H.statement_refuted("∀ n : ℕ,  foo n", rs))      # whitespace-insensitive
        self.assertIsNone(H.statement_refuted("∀ n : ℕ, n = 1", rs))


class Prompts(unittest.TestCase):
    """The prompts carry the protocol; percentages are banned as a status."""

    def test_plan_prompt_demands_a_skeleton_and_kinds(self):
        text = H.PLAN_PROMPT.format(pid="99", statement_en="s", statement="t", literature="l", library="",
                                    lemmas="", residual="", experiments="", refuted="", ledger="", cycle=1,
                                    hyp_prefix="erdos_99_hyp_", failures="(none yet)")
        for want in ("erdos_99_hyp_", "-- PUBLISHED:", "never as an `axiom`", "Never a percentage",
                     "NO `sorry`", "```json"):
            self.assertIn(want, text)

    def test_experiments_prompt_is_refute_first(self):
        text = H.EXPERIMENTS_PROMPT.format(pid="99", statement_en="s", statement="t", literature="l",
                                           hypotheses="- h : P", refuted="(none)")
        for want in ("REFUTED:", "CLEAR:", "INVARIANT:", "Never print a percentage", "REFUTE FIRST"):
            self.assertIn(want, text)

    def test_reduce_prompt_asks_for_a_lean_statement(self):
        text = H.REDUCE_PROMPT.format(pid="1", statement_en="s", notes="n", statement="t", check_seconds=45,
                                      modules="math", library="")
        self.assertIn('"lean"', text)
        self.assertIn("carried as a hypothesis, never as fact", text)

    def test_legacy_prompts_survive_for_the_lemma_loop(self):
        self.assertIn("numerical-experiments stage", H.EXPERIMENTS_PROMPT_LEMMA)
        self.assertIn("sub-statements", H.PLAN_PROMPT_LEMMA)


JUDGE_OK = '```json\n{"routine": false, "easier": true, "why": "a different result / a strict subcase"}\n```'


def _judged(fn):
    """A plan stub that also answers the judges: a premise is a genuine ingredient, a refinement is easier."""
    return lambda purpose, prompt, **kw: JUDGE_OK if purpose in ("circularity", "refinement") else fn(purpose, prompt, **kw)


def _stub(tmp, **state):
    h = H.Harness.__new__(H.Harness)
    h.problem = {"id": "99", "statement": "Is foo n true for every n?", "tags": []}
    h.state = {"statement": FROZEN, **state}
    h.log = Log()
    h.run_dir = Path(tmp)
    h.args = argparse.Namespace(no_cascade=True, run_budget=5.0, research_cycles=1, review_every=1,
                                hyps_per_cycle=4, refute="off", llm_timeout=60, review_wait=0, min_child_budget=2.5,
                                residual_depth=2, residual_depth_current=1,
                                # the breadth-first sweep is off by default (its train replay proved 0 of 9);
                                # pinned off here too, since these tests mock `_attack_substatement` once and a
                                # sweep would call the same mock first. tests/test_sweep_and_caps.py turns it on.
                                sweep="off")
    h.imports, h.libraries = list(H.DEFAULT_IMPORTS), []
    h.direction = None
    h.save = lambda: None
    h.report = lambda proved: None
    h.spent_usd = lambda: 0.0
    h._check_run_budget = lambda purpose: None
    def check(body, name):
        if name.startswith(("circularity", "refinement")):   # the free tactics close nothing by default
            return {"ok": False, "sorries": [], "errors": ["unsolved goals"], "infos": [], "body": body}
        return {"ok": True, "sorries": ["s"] if H.hole_count(body) else [], "errors": [], "infos": [], "body": body}
    h.check = check
    h._close_holes_without_model = lambda code, frozen: code
    h.ask = lambda purpose, prompt, **kw: JUDGE_OK
    return h


class ReductionCertification(unittest.TestCase):
    """A checked reduction that also compiles in Lean is `stated`; one the free cascade closes is `certified`."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
    def tearDown(self):
        self.tmp.cleanup()

    def test_stated_then_certified(self):
        h = _stub(self.tmp.name)
        e = {"id": "R1"}
        h._certify_reduction_statement(e, "theorem reduction_1 : True := by\n  sorry", 0)
        self.assertEqual(e["lean_status"], "stated")
        h._close_holes_without_model = lambda code, frozen: code.replace("sorry", "trivial")
        e = {"id": "R1"}
        h._certify_reduction_statement(e, "theorem reduction_1 : True := by\n  sorry", 0)
        self.assertEqual(e["lean_status"], "certified")
        self.assertEqual(e["lean_name"], "reduction_1")

    def test_compiled_under_the_frozen_defs(self):
        """95 of 141 reductions on statements with `def`s died as `Unknown identifier`: compiled without the defs."""
        frozen = ("open Finset\n\ndef erdos_7_Rep (n : ℕ) : Prop := n = n\n\n"
                  "theorem erdos_7_hyp_top : ∀ n : ℕ, erdos_7_Rep n := by\n  sorry")
        h = _stub(self.tmp.name, statement=frozen)
        seen = []
        inner = h.check
        h.check = lambda body, name: seen.append(body) or inner(body, name)
        e = {"id": "R1"}
        h._certify_reduction_statement(e, "theorem reduction_1 : ∀ n, erdos_7_Rep n := by\n  sorry", 0)
        self.assertEqual(e["lean_status"], "stated")
        self.assertEqual(e["lean_name"], "reduction_1")
        self.assertIn("def erdos_7_Rep", seen[0])
        self.assertIn("open Finset", seen[0])
        self.assertNotIn("erdos_7_hyp_top", seen[0])          # the target is not a premise
        own = "def erdos_7_Rep (n : ℕ) : Prop := True\n\ntheorem reduction_2 : erdos_7_Rep 0 := by\n  sorry"
        self.assertEqual(H.reduction_source(own, frozen).count("def erdos_7_Rep"), 1)
        self.assertEqual(H.reduction_theorem_name(own), "reduction_2")
        self.assertEqual(H.reduction_source(own, "theorem t : True := by\n  sorry"), own)

    def test_ill_typed_or_banned_is_dropped(self):
        h = _stub(self.tmp.name)
        e = {"id": "R1"}
        h._certify_reduction_statement(e, "theorem r : True := by native_decide", 0)
        self.assertEqual(e["lean_status"], "ill-typed")
        self.assertNotIn("lean", e)

    def test_context_labels_the_lean_status(self):
        h = _stub(self.tmp.name, reductions={"verified": [
            {"id": "R1", "kind": "parity", "claim": "c1", "justification": "j", "consequence": "q", "lean_status": "certified", "lean_name": "reduction_1"},
            {"id": "R2", "kind": "forced", "claim": "c2", "justification": "j", "consequence": "q", "lean_status": "stated"}]})
        ctx = h.reduction_context()
        self.assertIn("PROVED in Lean as `reduction_1`", ctx)
        self.assertIn("a hypothesis, not a fact", ctx)


class SkeletonAdoption(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.cdir = Path(self.tmp.name) / "c1"
        self.cdir.mkdir()
    def tearDown(self):
        self.tmp.cleanup()

    def test_first_valid_skeleton_is_adopted(self):
        h = _stub(self.tmp.name)
        v = h._consider_skeleton(SKELETON, {}, None, H.statement_prefix(FROZEN), 1, [], self.cdir)
        self.assertTrue(v["adopted"])
        self.assertEqual(v["parsed"]["metric"]["open_conjectures"], 1)
        self.assertTrue((self.cdir / "skeleton.lean").exists())

    def test_glue_with_a_sorry_is_not_a_conditional_theorem(self):
        h = _stub(self.tmp.name)
        bad = SKELETON.replace("  intro n\n  exact erdos_99_hyp_a n", "  sorry")
        v = h._consider_skeleton(bad, {}, None, H.statement_prefix(FROZEN), 1, [], self.cdir)
        self.assertFalse(v["adopted"])
        self.assertIn("glue", v["reason"])

    def test_refuted_statement_cannot_return_in_disguise(self):
        h = _stub(self.tmp.name)
        refs = [{"name": "old", "statement": "∀ n : ℕ, foo n", "witness": {"n": 3}}]
        v = h._consider_skeleton(SKELETON, {}, None, H.statement_prefix(FROZEN), 1, refs, self.cdir)
        self.assertFalse(v["adopted"])
        self.assertIn("refuted", v["reason"])

    def test_no_improvement_is_rejected(self):
        h = _stub(self.tmp.name)
        current = H.parse_residual(SKELETON, 99)
        v = h._consider_skeleton(SKELETON, {}, current, H.statement_prefix(FROZEN), 2, [], self.cdir)
        self.assertFalse(v["adopted"])
        self.assertIn("no improvement", v["reason"])

    def test_altered_frozen_theorem_is_rejected(self):
        h = _stub(self.tmp.name)
        v = h._consider_skeleton(SKELETON.replace("theorem erdos_99 :", "theorem erdos_99 (h : True) :"),
                                 {}, None, H.statement_prefix(FROZEN), 1, [], self.cdir)
        self.assertFalse(v["adopted"])


class DeductiveLoopEndToEnd(unittest.TestCase):
    """One mocked cycle: plan -> skeleton adopted -> the open conjecture is attacked and certified -> spliced back
    -> no hole left -> the skeleton IS the proof -> verification -> exit 0. Artifacts land where the docs say."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self._root, self._know = H.ROOT, H.KNOWLEDGE
        H.ROOT, H.KNOWLEDGE = self.root, self.root / "knowledge"
        (self.root / "run").mkdir()
    def tearDown(self):
        H.ROOT, H.KNOWLEDGE = self._root, self._know
        self.tmp.cleanup()

    def test_cycle_closes_the_residual(self):
        h = _stub(self.root / "run")
        skel = SKELETON.replace("-- PUBLISHED: Rosser–Schoenfeld 1962, Corollary 3\n"
                                "theorem erdos_99_hyp_rs : ∀ x : ℕ, 1 ≤ x → x ≤ x := by\n  sorry\n\n", "")
        plan = ("Here is the plan.\n```lean\n" + skel + "\n```\n```json\n"
                + json.dumps({"hypotheses": [{"name": "erdos_99_hyp_a", "kind": "conjecture", "derivation": "reflexivity"}],
                              "conjectures": [], "definitions": [], "route": "glue"}) + "\n```\n")
        asked = []
        h.ask = _judged(lambda purpose, prompt, **kw: asked.append(purpose) or plan)
        h._install_lemmas_module = lambda pdir: None
        proof = "theorem erdos_99_hyp_a : ∀ n : ℕ, foo n := by\n  intro n\n  rfl"
        child = argparse.Namespace(state={"proof": proof})
        h._attack_substatement = lambda sub, name, sdir, cycle, module, remaining, **k: (0, child)
        def verify():
            h.state["verify"] = {"all_clear": True}
            return h.state["verify"]
        h.stage_verify = verify
        rc = h.run_program()
        self.assertEqual(rc, 0)
        self.assertEqual(h.state["outcome"], "proved")
        self.assertEqual(asked, ["plan"])                       # refute was off; one plan call
        pdir = self.root / "programs" / "erdos_99"
        self.assertTrue((pdir / "Residual.lean").exists() and (pdir / "RESIDUAL.md").exists())
        self.assertTrue((pdir / "campaign.json").exists())
        self.assertEqual(h.state["residual"]["open"], 0)
        self.assertEqual(h.state["residual"]["certified"], 2)
        self.assertIn("exact erdos_99_hyp_a_ns.erdos_99_hyp_a", h.state["proof"])
        self.assertEqual(H.hole_count(h.state["proof"]), 0)
        kinds = [json.loads(l)["kind"] for l in (pdir / "ledger.jsonl").read_text().splitlines()]
        self.assertEqual(kinds, ["skeleton", "hypothesis"])

    def test_a_statement_without_the_main_theorem_stops_before_any_call(self):
        """Two #435 hard-step runs froze `erdos_<id>_hyp_top` and spent every cycle on plans no matcher could see."""
        h = _stub(self.root / "run", statement=FROZEN.replace("theorem erdos_99 ", "theorem erdos_99_hyp_top "))
        asked = []
        h.ask = lambda purpose, prompt, **kw: asked.append(purpose) or ""
        with self.assertRaisesRegex(ValueError, "no theorem named `erdos_99`"):
            h.run_program()
        self.assertEqual(asked, [])

    def test_a_published_premise_keeps_the_target_open(self):
        """The honesty trap: with the published RS premise still `sorry`, the loop must NOT declare a proof even
        after every conjecture is discharged. The residual reports 0 open conjectures and 1 premise."""
        h = _stub(self.root / "run")
        plan = ("```lean\n" + SKELETON + "\n```\n```json\n"
                + json.dumps({"hypotheses": [{"name": "erdos_99_hyp_rs", "kind": "published", "source": "RS 1962"}]}) + "\n```\n")
        h.ask = _judged(lambda purpose, prompt, **kw: plan)
        h._install_lemmas_module = lambda pdir: None
        proof = "theorem erdos_99_hyp_a : ∀ n : ℕ, foo n := by\n  intro n\n  rfl"
        h._attack_substatement = lambda *a, **k: (0, argparse.Namespace(state={"proof": proof}))
        h.stage_verify = lambda: {"all_clear": True}
        rc = h.run_program()
        self.assertEqual(rc, 3)
        self.assertEqual(h.state["outcome"], "partial")
        self.assertNotIn("proof", h.state)
        self.assertEqual(h.state["residual"]["open"], 0)
        self.assertEqual(h.state["residual"]["published"], 1)
        self.assertTrue((self.root / "programs" / "erdos_99" / "premises.jsonl").exists())


class ChildFunding(unittest.TestCase):
    """Never start a child it cannot fund: with $3 left and a $2.50 floor, only one of three hypotheses runs."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self._root, self._know = H.ROOT, H.KNOWLEDGE
        H.ROOT, H.KNOWLEDGE = self.root, self.root / "knowledge"
        (self.root / "run").mkdir()
    def tearDown(self):
        H.ROOT, H.KNOWLEDGE = self._root, self._know
        self.tmp.cleanup()

    def test_deferred_hypotheses_are_logged_not_starved(self):
        h = _stub(self.root / "run")
        h.args.run_budget, h.spent_usd = 5.0, (lambda: 2.0)
        skel = SKELETON.replace("theorem erdos_99_hyp_done : True := by\n  trivial",
                                "theorem erdos_99_hyp_b : ∀ n : ℕ, foo n ∧ foo n := by\n  sorry")
        skel = skel.replace("-- PUBLISHED: Rosser–Schoenfeld 1962, Corollary 3\n", "")
        plan = "```lean\n" + skel + "\n```\n```json\n" + json.dumps({"hypotheses": []}) + "\n```\n"
        h.ask = _judged(lambda purpose, prompt, **kw: plan)
        h._install_lemmas_module = lambda pdir: None
        started = []
        def attack(sub, name, sdir, cycle, module, remaining, **k):
            started.append(name); return 2, argparse.Namespace(state={})
        h._attack_substatement = attack
        rc = h.run_program()
        self.assertEqual(rc, 3)
        self.assertEqual(len(started), 1)                                    # $3 left funds one child at $2.50
        deferred = [e for e in h.log.events if e[1] == "hypotheses_deferred"]
        self.assertEqual(len(deferred), 1)
        self.assertEqual(len(deferred[0][2]["skipped"]), 2)


class BudgetStopStillReports(unittest.TestCase):
    """A budget stop inside a cycle must still leave RESIDUAL.md and state['residual'] behind."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self._root, self._know = H.ROOT, H.KNOWLEDGE
        H.ROOT, H.KNOWLEDGE = self.root, self.root / "knowledge"
        (self.root / "run").mkdir()
    def tearDown(self):
        H.ROOT, H.KNOWLEDGE = self._root, self._know
        self.tmp.cleanup()

    def test_residual_written_when_a_child_exhausts_the_budget(self):
        h = _stub(self.root / "run")
        h.args.min_child_budget = 0
        plan = "```lean\n" + SKELETON + "\n```\n```json\n" + json.dumps({"hypotheses": []}) + "\n```\n"
        h.ask = _judged(lambda purpose, prompt, **kw: plan)
        h._install_lemmas_module = lambda pdir: None
        def attack(*a, **k):
            raise H.Harness.BudgetExhausted("run budget $5.0 exhausted (spent $5.10)")
        h._attack_substatement = attack
        rc = h.run_program()
        self.assertEqual(rc, 3)
        pdir = self.root / "programs" / "erdos_99"
        self.assertTrue((pdir / "RESIDUAL.md").exists())
        self.assertEqual(h.state["residual"]["open"], 1)
        self.assertTrue(any(e[1] == "stopped_on_budget" for e in h.log.events))

    def test_paid_response_is_returned_and_the_next_call_raises(self):
        seen = []
        class Backend:
            def complete(self, purpose, prompt, effort_override=None, budget_override=None):
                seen.append(purpose); self.last_meta = {"cost_usd": 3.0}; return "proof text"
        h = H.Harness.__new__(H.Harness)
        h.llm, h.log, h.problem = Backend(), Log(), {"id": "99"}
        h.args = argparse.Namespace(run_budget=2.0, masked=False)
        h.run_dir = self.root / "run"
        spent = {"v": 0.0}
        h.spent_usd = lambda: spent["v"]
        def after_call():                       # the backend's cost lands in the log after the response
            spent["v"] = 3.0
        h.log.event = lambda stage, event, **kw: (after_call() if event == "response" else None)
        self.assertEqual(h.ask("prove", "p"), "proof text")     # over budget after this call, but returned
        with self.assertRaises(H.Harness.BudgetExhausted):
            h.ask("prove", "again")                              # the NEXT spend attempt raises
        self.assertEqual(seen, ["prove"])


class Refinement(unittest.TestCase):
    """A child that does not close its target but certifies `target <= sub-hypotheses` refines the parent."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self._root, self._know = H.ROOT, H.KNOWLEDGE
        H.ROOT, H.KNOWLEDGE = self.root, self.root / "knowledge"
        (self.root / "run").mkdir()
    def tearDown(self):
        H.ROOT, H.KNOWLEDGE = self._root, self._know
        self.tmp.cleanup()

    def test_partial_child_residual_is_spliced_as_a_refinement(self):
        h = _stub(self.root / "run")
        h.args.min_child_budget = 0
        skel = SKELETON.replace("-- PUBLISHED: Rosser–Schoenfeld 1962, Corollary 3\n"
                                "theorem erdos_99_hyp_rs : ∀ x : ℕ, 1 ≤ x → x ≤ x := by\n  sorry\n\n", "")
        plan = "```lean\n" + skel + "\n```\n```json\n" + json.dumps({"hypotheses": [{"name": "erdos_99_hyp_a", "difficulty": "hard"}]}) + "\n```\n"
        h.ask = _judged(lambda purpose, prompt, **kw: plan)
        h._install_lemmas_module = lambda pdir: None
        # Step 2: a refinement is spliced only if the child DISCHARGED something (here: the base case)
        sub_skel = ("def foo (n : ℕ) : Prop := n = n\n\n"
                    "theorem erdos_99_hyp_a_hyp_base : foo 0 := by\n  rfl\n\n"
                    "theorem erdos_99_hyp_a_hyp_step : ∀ n : ℕ, foo n := by\n  sorry\n\n"
                    "theorem erdos_99_hyp_a : ∀ n : ℕ, foo n := by\n  intro n\n  exact erdos_99_hyp_a_hyp_step n")
        sub_path = self.root / "sub_residual.lean"
        sub_path.write_text(sub_skel)
        seen = {}
        def attack(sub, name, sdir, cycle, module, remaining, recursive=False):
            seen["recursive"] = recursive
            child_state = {"residual": {"skeleton": str(sub_path), "meta": {"hypotheses": [{"name": "erdos_99_hyp_a_hyp_step", "difficulty": "elementary"}]}}}
            return 3, argparse.Namespace(state=child_state)
        h._attack_substatement = attack
        rc = h.run_program()
        self.assertEqual(rc, 3)
        self.assertTrue(seen["recursive"])                          # rated hard -> attacked with its own skeleton
        r = h.state["residual"]
        self.assertEqual(r["open"], 1)
        names = {x["name"] for x in r["hypotheses"] if x["open"]}
        self.assertEqual(names, {"erdos_99_hyp_a_hyp_step"})       # the parent's frontier is now the sub-hypothesis
        skeleton = (self.root / "programs" / "erdos_99" / "Residual.lean").read_text()
        self.assertIn("namespace erdos_99_hyp_a_ns", skeleton)
        self.assertEqual(skeleton.count("def foo"), 1)               # the child's copy of the parent's def is dropped
        refined = [e for e in h.log.events if e[1] == "hypothesis_refined"]
        self.assertTrue(refined)
        self.assertEqual(refined[0][2]["discharged"], ["erdos_99_hyp_a_hyp_base"])
        self.assertEqual(H.hole_count(skeleton), 1)

    def test_failed_child_is_banked_and_fed_forward(self):
        h = _stub(self.root / "run")
        h.args.min_child_budget = 0
        skel = SKELETON.replace("-- PUBLISHED: Rosser–Schoenfeld 1962, Corollary 3\n"
                                "theorem erdos_99_hyp_rs : ∀ x : ℕ, 1 ≤ x → x ≤ x := by\n  sorry\n\n", "")
        prompts = []
        plan = "```lean\n" + skel + "\n```\n```json\n" + json.dumps({"hypotheses": [], "failure_responses": [
            {"hypothesis": "erdos_99_hyp_a", "move": "define", "detail": "name the recurring parity structure"}]}) + "\n```\n"
        h.ask = _judged(lambda purpose, prompt, **kw: prompts.append(prompt) or plan)
        h._install_lemmas_module = lambda pdir: None
        h.args.research_cycles = 2
        child_state = {"attempts": [{"name": "proof-r1-a0", "compiled": False, "n_sorries": 0,
                                     "errors": ["line 3:2: unsolved goals\n⊢ False\n"]}], "stop_reason": "rounds exhausted"}
        h._attack_substatement = lambda *a, **k: (2, argparse.Namespace(state=child_state))
        rc = h.run_program()
        self.assertEqual(rc, 3)
        pdir = self.root / "programs" / "erdos_99"
        self.assertTrue((pdir / "failures.jsonl").exists())
        self.assertIn("unsolved goal: ⊢ False", prompts[1])         # cycle 2's plan saw cycle 1's failure
        self.assertTrue((pdir / "moves.jsonl").exists())
        self.assertIn("Moves the plan made", (pdir / "RESIDUAL.md").read_text())
        self.assertIn("Proof failures", (pdir / "RESIDUAL.md").read_text())


class FrozenGuardWithDefinitions(unittest.TestCase):
    """A hypothesis frozen as defs + theorem must accept helpers between the defs and the theorem."""

    FROZEN = ("def Cov (m : ℕ) (z : ℤ) : Prop := z = z\n\n"
              "theorem erdos_99_hyp_step : ∀ m : ℕ, ∀ z : ℤ, Cov m z := by\n  sorry")

    def test_helper_between_def_and_theorem_is_accepted(self):
        frozen = H.statement_prefix(self.FROZEN)
        attempt = ("def Cov (m : ℕ) (z : ℤ) : Prop := z = z\n\n"
                   "lemma helper (z : ℤ) : z = z := rfl\n\n"
                   "theorem erdos_99_hyp_step : ∀ m : ℕ, ∀ z : ℤ, Cov m z := by\n  intro m z\n  exact helper z")
        self.assertTrue(H.contains_frozen(attempt, frozen))

    def test_altered_header_or_missing_def_is_still_rejected(self):
        frozen = H.statement_prefix(self.FROZEN)
        altered = ("def Cov (m : ℕ) (z : ℤ) : Prop := z = z\n\n"
                   "theorem erdos_99_hyp_step : ∀ m : ℕ, ∀ z : ℤ, m = m → Cov m z := by\n  sorry")
        self.assertFalse(H.contains_frozen(altered, frozen))
        missing_def = "theorem erdos_99_hyp_step : ∀ m : ℕ, ∀ z : ℤ, Cov m z := by\n  sorry"
        self.assertFalse(H.contains_frozen(missing_def, frozen))
        changed_def = ("def Cov (m : ℕ) (z : ℤ) : Prop := True\n\n"
                       "theorem erdos_99_hyp_step : ∀ m : ℕ, ∀ z : ℤ, Cov m z := by\n  sorry")
        self.assertFalse(H.contains_frozen(changed_def, frozen))

    def test_single_theorem_behaviour_unchanged(self):
        frozen = H.statement_prefix(FROZEN)
        self.assertTrue(H.contains_frozen("theorem erdos_99 : ∀ n : ℕ, foo n := by\n  intro n\n  rfl", frozen))
        self.assertFalse(H.contains_frozen("theorem erdos_99 : ∀ n : ℕ, n = n := by\n  intro n\n  rfl", frozen))


class RejectedAttemptsKeepTheirCode(unittest.TestCase):
    def test_screen_records_code_and_the_missing_declaration(self):
        h = H.Harness.__new__(H.Harness)
        h.log = Log()
        frozen = H.statement_prefix("def Cov (z : ℤ) : Prop := z = z\n\ntheorem erdos_99_hyp_s : ∀ z : ℤ, Cov z := by\n  sorry")
        attempts = []
        altered = "def Cov (z : ℤ) : Prop := z = z\n\ntheorem erdos_99_hyp_s : ∀ z : ℤ, z = z → Cov z := by\n  intro z _\n  rfl"
        ok = h._screen(attempts, "proof-r1-a0", "plan", 1, altered, frozen)
        self.assertFalse(ok)
        self.assertEqual(attempts[0]["code"], altered)
        self.assertIn("missing verbatim theorem erdos_99_hyp_s", attempts[0]["errors"][0])
        self.assertNotIn("def Cov", attempts[0]["errors"][0])          # the def WAS present; only the header changed


class SplitSkeletonBlocks(unittest.TestCase):
    """A plan that splits its skeleton across fenced blocks must still be considered whole."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self._root, self._know = H.ROOT, H.KNOWLEDGE
        H.ROOT, H.KNOWLEDGE = self.root, self.root / "knowledge"
        (self.root / "run").mkdir()
    def tearDown(self):
        H.ROOT, H.KNOWLEDGE = self._root, self._know
        self.tmp.cleanup()

    def test_definitions_in_an_earlier_block_are_not_lost(self):
        h = _stub(self.root / "run")
        defs, rest = SKELETON.split("\n\n", 1)
        self.assertIn("def foo", defs)
        seen = []
        def check(body, name):
            seen.append(body)
            ok = "def foo" in body and not name.startswith("circularity")   # a block without the def would not compile
            return {"ok": ok, "sorries": ["s"] if H.hole_count(body) else [], "infos": [],
                    "errors": [] if ok else ["unknown identifier `foo`"], "body": body}
        h.check = check
        plan = ("```lean\n" + defs + "\n```\n\n-- continuation\n\n```lean\n" + rest + "\n```\n```json\n{}\n```\n")
        h.ask = _judged(lambda purpose, prompt, **kw: plan)
        h._install_lemmas_module = lambda pdir: None
        h._attack_substatement = lambda *a, **k: (2, argparse.Namespace(state={}))
        rc = h.run_program()
        self.assertEqual(rc, 3)                                          # a skeleton is in force
        self.assertEqual(h.state["residual"]["open"], 1)
        self.assertTrue(any(e[1] == "skeleton_candidate_rejected" for e in h.log.events))
        adopted = [e for e in h.log.events if e[1] == "skeleton"][0]
        self.assertTrue(adopted[2]["adopted"])
        self.assertEqual(adopted[2]["candidates"], 2)

    def test_plan_prompt_forbids_split_skeletons(self):
        text = H.PLAN_PROMPT.format(pid="99", statement_en="s", statement="t", literature="l", library="",
                                    lemmas="", residual="", experiments="", refuted="", ledger="", cycle=1,
                                    hyp_prefix="erdos_99_hyp_", failures="(none yet)")
        self.assertIn("Do not split it across two blocks", text)


class SkeletonRejectionFeedsForward(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self._root, self._know = H.ROOT, H.KNOWLEDGE
        H.ROOT, H.KNOWLEDGE = self.root, self.root / "knowledge"
        (self.root / "run").mkdir()
    def tearDown(self):
        H.ROOT, H.KNOWLEDGE = self._root, self._know
        self.tmp.cleanup()

    def test_rejected_skeleton_reaches_the_next_plan(self):
        h = _stub(self.root / "run")
        h.args.research_cycles = 2
        bad = SKELETON.replace("  intro n\n  exact erdos_99_hyp_a n", "  sorry")      # a sorry in the glue
        prompts = []
        h.ask = _judged(lambda purpose, prompt, **kw: prompts.append((purpose, prompt)) or ("```lean\n" + bad + "\n```\n```json\n{}\n```\n"))
        h._install_lemmas_module = lambda pdir: None
        rc = h.run_program()
        self.assertEqual(rc, 2)                                            # nothing adopted, nothing certified
        pdir = self.root / "programs" / "erdos_99"
        fs = [json.loads(l) for l in (pdir / "failures.jsonl").read_text().splitlines()]
        self.assertEqual(fs[0]["kind"], "skeleton")
        self.assertIn("glue", fs[0]["stop_reason"])
        plans = [p for purpose, p in prompts if purpose == "plan"]
        self.assertIn("YOUR OWN SKELETON was rejected", plans[1])           # cycle 2 saw cycle 1's rejection
        # each rejected plan got one repair round first, which saw the reason and the as-compiled skeleton
        repairs = [p for purpose, p in prompts if purpose == "plan-repair"]
        self.assertEqual(len(repairs), 2)
        self.assertIn("the glue is not glue", repairs[0])
        self.assertEqual(H.failure_counts(pdir), {})                       # skeleton entries are not hypotheses


class SubResidualIsolation(unittest.TestCase):
    def test_sub_residuals_get_their_own_directory_and_module(self):
        import types
        r = types.SimpleNamespace(problem={"id": "99"}, direction="program", program_subdir="erdos_99_hyp_a")
        r._program_dir = types.MethodType(H.Harness._program_dir, r)
        r._program_module_suffix = types.MethodType(H.Harness._program_module_suffix, r)
        with tempfile.TemporaryDirectory() as tmp:
            old = H.ROOT; H.ROOT = Path(tmp)
            try:
                d = r._program_dir()
                self.assertEqual(d.relative_to(Path(tmp)).as_posix(), "programs/erdos_99/sub/erdos_99_hyp_a")
                self.assertTrue(r._program_module_suffix().startswith("Sub") and r._program_module_suffix().isalnum())
            finally:
                H.ROOT = old


class PerCallCap(unittest.TestCase):
    """One call may not spend what the run no longer has."""

    def test_call_budget_is_capped_at_the_remaining_run_budget(self):
        seen = {}
        class Backend:
            call_budget_usd = 8.0
            def _tuning(self, purpose):
                return ("medium", 8.0)
            def complete(self, purpose, prompt, effort_override=None, budget_override=None):
                seen["budget"] = budget_override; self.last_meta = {}; return "ok"
        with tempfile.TemporaryDirectory() as tmp:
            h = H.Harness.__new__(H.Harness)
            h.llm, h.log, h.problem = Backend(), Log(), {"id": "99"}
            h.args = argparse.Namespace(run_budget=15.0, masked=False)
            h.run_dir = Path(tmp)
            h.spent_usd = lambda: 11.4
            h.ask("prove", "p")
            self.assertEqual(seen["budget"], 3.6)                   # $15 - $11.40 left, below the $8 per-call cap
            h.spent_usd = lambda: 2.0
            h.ask("prove", "p")
            self.assertIsNone(seen["budget"])                        # plenty left: the tuned cap stands
            h.spent_usd = lambda: 14.9
            h.ask("prove", "p")
            self.assertEqual(seen["budget"], 0.5)                    # never below the floor


class SummaryAndFacts(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.d = Path(self.tmp.name) / "20260101-000000-000000-erdos99"
        self.d.mkdir(parents=True)
    def tearDown(self):
        self.tmp.cleanup()

    def test_summary_line_and_facts_carry_the_residual(self):
        (self.d / "log.jsonl").write_text(json.dumps({"ts": "2026-01-01T00:00:00Z", "stage": "run", "event": "start"}) + "\n")
        (self.d / "state.json").write_text(json.dumps({"outcome": "partial", "mode": "research",
                                                        "residual": {"open": 1, "published": 1, "certified": 2, "hypotheses": []}}))
        line = H.run_summary_line(self.d, 3)
        self.assertIn("residual=open:1,published:1,certified:2", line)
        self.assertEqual(H.collect_run_facts(self.d, "99")["residual"]["open"], 1)


class CampaignConjectures(unittest.TestCase):
    """The residual as a campaign DAG: conjecture nodes are never dependencies; `residual` reports them."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
    def tearDown(self):
        self.tmp.cleanup()

    def test_manifest_validates_and_reports(self):
        parsed = H.parse_residual(SKELETON, 99)
        plan = H.residual_campaign_manifest(99, parsed, {"model_calls": 5, "lean_checks": 5, "wall_seconds": 60})
        by = C.validate(plan)
        self.assertEqual(by["target"]["scope"], "conditional")
        self.assertEqual(sorted(by["target"]["conditional_on"]), ["erdos_99_hyp_a", "erdos_99_hyp_rs"])
        self.assertEqual(by["target"]["depends_on"], ["erdos_99_hyp_done"])
        path = Path(self.tmp.name) / "campaign.json"
        path.write_text(json.dumps(plan))
        r = C.Campaign(path).residual()
        self.assertEqual({c["id"] for c in r["open_conjectures"]}, {"erdos_99_hyp_a", "erdos_99_hyp_rs"})
        self.assertEqual(r["published_premises"], 1)
        self.assertFalse(r["resolved"])
        self.assertEqual(C.main(["residual", "--manifest", str(path)]), 0)

    def test_a_conjecture_cannot_be_a_proof_dependency(self):
        plan = {"schema_version": 1, "id": "T", "targets": ["goal"],
                "budget": {"model_calls": 1, "lean_checks": 1, "wall_seconds": 1},
                "nodes": [{"id": "c", "kind": "conjecture", "scope": "general", "type": "True"},
                          {"id": "goal", "kind": "target", "scope": "general", "type": "True", "depends_on": ["c"]}]}
        with self.assertRaises(ValueError):
            C.validate(plan)
        plan["nodes"][1]["depends_on"], plan["nodes"][1]["conditional_on"] = [], ["c"]
        C.validate(plan)
        plan["nodes"][0].pop("type")
        with self.assertRaises(ValueError):
            C.validate(plan)


class BenchmarkIsolation(unittest.TestCase):
    """A benchmark must not be handed the reference proof, and a masked run must not name the problem."""

    def test_benchmark_mode_skips_the_lemma_store(self):
        h = H.Harness.__new__(H.Harness)
        h.problem, h.state = {"id": "99", "statement": "colouring monochromatic progression"}, {"statement": "t"}
        with patch.object(H, "playbook_for", lambda q, **k: "PLAYBOOK"), \
             patch.object(H, "lemmas_for", lambda q, **k: "HELPER FRAGMENTS FROM CHECKED PROOFS: no_mono ..."):
            h.args = argparse.Namespace(benchmark=False)
            self.assertIn("HELPER FRAGMENTS", h.playbook_block())
            h.args = argparse.Namespace(benchmark=True)
            block = h.playbook_block()
            self.assertIn("PLAYBOOK", block)
            self.assertNotIn("HELPER FRAGMENTS", block)

    def test_mask_scrubs_prose_but_not_identifiers(self):
        text = ("You are the planning stage on an OPEN Erdős problem (#80317). Source: erdosproblems.com/275 . "
                "Erdos problems cluster hard. (Erdős #674 lesson). theorem erdos_80317 : True := by trivial "
                "Formal.Library.CoveringSystems Erdos.Covering.density Erdos273.pool_bound")
        out = H.mask_prompt(text)
        self.assertNotIn("Erdős", out)
        self.assertNotIn("Erdos ", out)
        self.assertNotIn("erdosproblems.com", out)
        self.assertIn("erdos_80317", out)                       # theorem names are untouched
        self.assertIn("Erdos.Covering.density", out)            # library declaration names are untouched
        self.assertIn("Erdos273.pool_bound", out)
        self.assertIn("OPEN problem (#80317)", out)

    def test_mask_keeps_named_results_and_never_doubles_the_article(self):
        out = H.mask_prompt("Use the Erdős–Ko–Rado theorem, the Erdős-Szekeres bound, an Erdős–Rényi graph, "
                            "Erdős–Turán sets and the Chvátal–Erdős condition. The Erdős conjecture on this, "
                            "as Erdős showed—and Erdős's own note—is open (Erdős problem #7).")
        for name in ("Erdős–Ko–Rado", "Erdős-Szekeres", "Erdős–Rényi", "Erdős–Turán", "Chvátal–Erdős"):
            self.assertIn(name, out)
        self.assertNotIn("the the", out.lower())
        self.assertIn("the catalogue's conjecture", out)
        self.assertIn("as the catalogue's showed", out)            # a dash before lower case is punctuation
        self.assertIn("problem #7", out)
        self.assertNotIn("Erdős problem", out)

    def test_masked_backend_scrubs_every_call_and_forwards_attributes(self):
        seen = {}
        class Inner:
            timeout = 7
            def complete(self, purpose, prompt, effort_override=None, budget_override=None):
                seen["prompt"] = prompt; self.last_meta = {"cost_usd": 0.1}; return "ok"
        inner = Inner()
        m = H.MaskedBackend(inner)
        self.assertEqual(m.complete("prove-agentic", "Erdős problem #1 says hello"), "ok")
        self.assertEqual(seen["prompt"], "problem #1 says hello")
        self.assertEqual(m.last_meta, {"cost_usd": 0.1})        # attribute reads pass through
        m.timeout = 9                                           # and writes land on the inner backend
        self.assertEqual(inner.timeout, 9)
        self.assertFalse(hasattr(m, "complete_web"))            # the inner has none, so neither does the proxy
        class Web(Inner):
            def complete_web(self, purpose, prompt, **k):
                seen["web"] = prompt; return "w"
        mw = H.MaskedBackend(Web())
        self.assertTrue(hasattr(mw, "complete_web"))
        self.assertEqual(mw.complete_web("literature", "Erdős problem #2", budget_usd=1.0), "w")
        self.assertEqual(seen["web"], "problem #2")
        class Agentic(Inner):
            def complete_agentic(self, purpose, prompt, sandbox, turns):
                seen["agentic"] = prompt; return "a"
        H.MaskedBackend(Agentic()).complete_agentic("prove-agentic", "Erdős problem #3", "/sb", 5)
        self.assertEqual(seen["agentic"], "problem #3")

    def test_masked_ask_writes_a_masked_transcript_and_sends_masked_text(self):
        """The first masked run's transcript still read 'Erdos problem #80317': the scrub lived only in the
        backend proxy, so the file the harness wrote (and the agentic TASK.md) carried the raw prompt."""
        seen = {}
        class Backend:
            def complete(self, purpose, prompt, effort_override=None, budget_override=None):
                seen["prompt"] = prompt; self.last_meta = {}; return "ok"
        with tempfile.TemporaryDirectory() as tmp:
            h = H.Harness.__new__(H.Harness)
            h.llm, h.log, h.problem = Backend(), Log(), {"id": "80317"}
            h.args = argparse.Namespace(run_budget=None, masked=True)
            h.run_dir = Path(tmp)
            h._check_run_budget = lambda purpose: None
            h.ask("plan", "You work on Erdos problem #80317 from erdosproblems.com/275.")
            self.assertEqual(seen["prompt"], "You work on problem #80317 from the problem catalogue.")
            transcript = next(Path(tmp, "transcripts").glob("*.md")).read_text()
            self.assertNotIn("Erdos", transcript)
            self.assertIn("problem #80317", transcript)


class RecordFindingResidual(unittest.TestCase):
    def test_residual_is_recorded_with_history(self):
        import record_finding as RF
        with tempfile.TemporaryDirectory() as tmp:
            reviewed = Path(tmp) / "reviewed.json"
            reviewed.write_text(json.dumps({"99": {"score": 5}}))
            with patch.object(RF, "REVIEWED", reviewed), patch.object(RF, "ROOT", Path(tmp)):
                base = dict(score=None, rationale=[], requirement=[], source=[], partial=None, search_floor=None,
                            floor_kind=None, brief=None, assessed=None)
                RF._record(argparse.Namespace(**base, residual='{"open": 2}'), "99")
                RF._record(argparse.Namespace(**base, residual='{"open": 1}'), "99")
            e = json.loads(reviewed.read_text())["99"]
            self.assertEqual(e["residual"], {"open": 1})
            self.assertEqual(e["residual_history"][0]["residual"], {"open": 2})
            self.assertEqual(e["score"], 5)


if __name__ == "__main__":
    unittest.main()


# The masked #275 failure (2026-09-23): a sub-residual closed with a PUBLISHED premise that was the frozen
# theorem with the block starting at 0 instead of t.
ROOT_275 = """theorem erdos_80317
    (m : ℕ) (u : Fin m → ℤ) (q : Fin m → ℕ)
    (hq : ∀ j, 0 < q j)
    (hblock : ∃ t : ℤ, ∀ k : ℕ, k < 2 ^ m →
      ∃ j : Fin m, (q j : ℤ) ∣ (t + (k : ℤ) - u j)) :
    ∀ z : ℤ, ∃ j : Fin m, (q j : ℤ) ∣ (z - u j) := by
  sorry"""

CVE_SKELETON = """def C80317Cov (m : ℕ) (u : Fin m → ℤ) (q : Fin m → ℕ) (z : ℤ) : Prop :=
  ∃ j : Fin m, (q j : ℤ) ∣ (z - u j)

-- PUBLISHED: R. B. Crittenden and C. L. Vanden Eynden, Proc. Amer. Math. Soc. 24 (1970), 475-481
theorem erdos_80317_hyp_cve : ∀ (m : ℕ) (u : Fin m → ℤ) (q : Fin m → ℕ), (∀ j, 0 < q j) →
    (∀ k : ℕ, k < 2 ^ m → C80317Cov m u q (k : ℤ)) → ∀ z : ℤ, C80317Cov m u q z := by
  sorry

""" + ROOT_275.replace("  sorry", """  obtain ⟨t, ht⟩ := hblock
  intro z
  obtain ⟨j, hj⟩ := erdos_80317_hyp_cve m (fun j => u j - t) q hq (fun k hk => by
    obtain ⟨j, hj⟩ := ht k hk
    exact ⟨j, by show (q j : ℤ) ∣ (k : ℤ) - (u j - t); rw [show (k : ℤ) - (u j - t) = t + k - u j by ring]; exact hj⟩) (z - t)
  exact ⟨j, by rw [show z - u j = (z - t) - (u j - t) by ring]; exact hj⟩""")


class CircularPremise(unittest.TestCase):
    """A published premise the target follows from by routine steps proves the target from itself."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.cdir = Path(self.tmp.name) / "c1"
        self.cdir.mkdir()
    def tearDown(self):
        self.tmp.cleanup()

    def _h(self, verdict, lean_closes=False):
        h = _stub(self.tmp.name)
        h.problem = {"id": "80317", "statement": "s", "tags": []}
        h.state = {"statement": ROOT_275}
        asked = []
        def check(body, name):
            if name.startswith("circularity"):
                return {"ok": lean_closes, "sorries": [], "errors": [] if lean_closes else ["unsolved goals"], "infos": [], "body": body}
            return {"ok": True, "sorries": ["s"] if H.hole_count(body) else [], "errors": [], "infos": [], "body": body}
        h.check = check
        h.ask = lambda purpose, prompt, **kw: asked.append((purpose, prompt)) or verdict
        return h, asked

    def _consider(self, h):
        return h._consider_skeleton(CVE_SKELETON, {}, None, H.statement_prefix(ROOT_275), 1, [], self.cdir,
                                    main="erdos_80317")

    def test_the_275_premise_is_rejected_when_the_judge_calls_it_routine(self):
        h, asked = self._h('```json\n{"routine": true, "why": "translate every class by t"}\n```')
        v = self._consider(h)
        self.assertFalse(v["adopted"])
        self.assertIn("circular premise `erdos_80317_hyp_cve`", v["reason"])
        self.assertIn("translate every class by t", v["reason"])
        self.assertEqual([p for p, _ in asked], ["circularity"])
        self.assertIn("Crittenden", asked[0][1])                      # the judge sees the citation and the target
        self.assertIn("theorem erdos_80317", asked[0][1])
        self.assertTrue(any(e[1] == "circular_premise" for e in h.log.events))

    def test_a_genuine_ingredient_is_adopted(self):
        h, _ = self._h('```json\n{"routine": false, "why": "needs the parity descent"}\n```')
        self.assertTrue(self._consider(h)["adopted"])

    def test_a_restatement_lean_closes_needs_no_judge(self):
        h, asked = self._h("unused", lean_closes=True)
        v = self._consider(h)
        self.assertFalse(v["adopted"])
        self.assertIn("Lean closes premise → target", v["reason"])
        self.assertEqual(asked, [])

    def test_no_verdict_is_a_rejection(self):
        h, _ = self._h("I think it is probably fine.")
        v = self._consider(h)
        self.assertFalse(v["adopted"])
        self.assertIn("no verdict", v["reason"])

    def test_bare_json_verdict_is_read(self):
        h, _ = self._h('{"routine": false, "why": "different"}')
        self.assertTrue(self._consider(h)["adopted"])

    def test_checked_against_the_root_target_inside_a_sub_residual(self):
        h, asked = self._h('```json\n{"routine": false, "why": "x"}\n```')
        h.root_frozen = H.statement_prefix(FROZEN)                     # a different root: two judgements
        self._consider(h)
        self.assertEqual(len(asked), 2)
        self.assertIn("theorem erdos_99", asked[1][1])

    def test_conjectures_are_not_judged(self):
        h, asked = self._h("unused")
        skel = CVE_SKELETON.replace("-- PUBLISHED: R. B. Crittenden and C. L. Vanden Eynden, Proc. Amer. Math. Soc. 24 (1970), 475-481\n", "")
        h._consider_skeleton(skel, {}, None, H.statement_prefix(ROOT_275), 1, [], self.cdir, main="erdos_80317")
        self.assertEqual(asked, [])

    def test_probe_source_puts_the_premise_before_the_target_binders(self):
        prop = next(x for x in H.parse_residual(CVE_SKELETON, 80317, main="erdos_80317")["hypotheses"])["statement"]
        src = H.circularity_probe_source(CVE_SKELETON, H.statement_prefix(ROOT_275), prop)
        self.assertIn("def C80317Cov", src)
        self.assertIn("theorem circularity_probe (hH : ∀ (m : ℕ)", src)
        self.assertIn("(hq : ∀ j, 0 < q j)", src)
        self.assertTrue(src.rstrip().endswith("| aesop"))
        self.assertNotIn("sorry", src)
        self.assertEqual(H.frozen_theorem(H.statement_prefix(ROOT_275))[0], "erdos_80317")

    def test_plan_prompt_states_the_rule(self):
        self.assertIn("never anything the\n      target follows from by routine steps", H.PLAN_PROMPT)
        self.assertIn("use the Mathlib theorem by name", H.PLAN_PROMPT)

    def test_children_inherit_the_root_target(self):
        import inspect
        self.assertIn("child.root_frozen", inspect.getsource(H.Harness._attack_substatement))


class OpenModeBenchmark(unittest.TestCase):
    def test_a_benchmark_open_run_writes_no_knowledge(self):
        import inspect
        src = inspect.getsource(H.Harness.run_open)
        self.assertIn('self.run_dir / "open-report") if getattr(self.args, "benchmark", False)', src)


class NegationDirection(unittest.TestCase):
    """--open composes with the deductive loop: the negation child's hypotheses are `erdos_N_neg_hyp_*`, and every
    research sub-run beneath a direction stays in that direction's tree and budget."""

    def test_neg_hypotheses_are_hypotheses(self):
        skel = ("theorem erdos_99_neg_hyp_w : ∃ n : ℕ, n = 3 := by\n  sorry\n\n"
                "theorem erdos_99_neg : ¬ (∀ n : ℕ, n = 0) := by\n  intro h\n"
                "  obtain ⟨n, hn⟩ := erdos_99_neg_hyp_w\n  have := h n\n  omega")
        r = H.parse_residual(skel, 99, main="erdos_99_neg")
        self.assertTrue(r["main_present"] and r["glue_sorry_free"])
        self.assertEqual([h["name"] for h in r["hypotheses"]], ["erdos_99_neg_hyp_w"])
        self.assertEqual(r["metric"]["open_conjectures"], 1)

    def test_sub_runs_keep_the_open_direction(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        old = H.ROOT
        H.ROOT = Path(tmp.name)
        self.addCleanup(lambda: setattr(H, "ROOT", old))
        h = _stub(tmp.name)
        h.direction = "program"
        h.open_direction = "neg"
        h.program_subdir = "erdos_99_neg_hyp_w"
        self.assertEqual(h._program_dir(), Path(tmp.name) / "programs" / "erdos_99" / "neg" / "sub" / "erdos_99_neg_hyp_w")
        self.assertTrue(h._program_module_suffix().startswith("NegSub"))
        top = _stub(tmp.name)
        top.direction = "pos"
        self.assertEqual(H.open_direction_of(top), "pos")
        plain = _stub(tmp.name)
        plain.direction = "program"
        self.assertIsNone(H.open_direction_of(plain))

    def test_children_inherit_the_open_direction(self):
        import inspect
        self.assertIn("child.open_direction = open_direction_of(self)", inspect.getsource(H.Harness._attack_substatement))


class SplicedNamespaceDefs(unittest.TestCase):
    """masked #645: a spliced proof's private MetaM helper must not leak into later sub-statements."""
    def test_defs_inside_a_spliced_namespace_are_not_skeleton_defs(self):
        skel = ("def search : ℕ → Bool := fun _ => false\n\n"
                "namespace erdos_99_hyp_a_ns\nprivate def helper : ℕ := 3\n\nopen Lean Meta in\n"
                "private def build : ℕ → MetaM Expr := fun _ => pure (mkNatLit 0)\n\n"
                "theorem erdos_99_hyp_a : search 0 = false := rfl\nend erdos_99_hyp_a_ns\n\n"
                "theorem erdos_99_hyp_a : search 0 = false := by\n  exact erdos_99_hyp_a_ns.erdos_99_hyp_a\n\n"
                "theorem erdos_99_hyp_b : search 1 = false := by\n  sorry\n\n"
                "theorem erdos_99 : search 0 = false ∧ search 1 = false := ⟨erdos_99_hyp_a, erdos_99_hyp_b⟩")
        defs = H.skeleton_defs(skel)
        self.assertEqual(len(defs), 1)
        self.assertIn("def search", defs[0])
        sub = H.hypothesis_substatement(skel, "erdos_99_hyp_b")
        self.assertNotIn("MetaM", sub)
        self.assertIn("theorem erdos_99_hyp_b : search 1 = false := by\n  sorry", sub)


PREMISE_ONLY = """def foo (n : ℕ) : Prop := n = n

-- PUBLISHED: Rosser–Schoenfeld 1962, Corollary 3
theorem erdos_99_hyp_rs : ∀ n : ℕ, foo n := by
  sorry

theorem erdos_99 : ∀ n : ℕ, foo n := by
  intro n
  exact erdos_99_hyp_rs n"""


class PremisesAreAttackedWhenNothingElseIsOpen(unittest.TestCase):
    """masked #499 stopped at `open:0, published:1` with Birkhoff as the premise, although Mathlib proves it."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self._root, self._know = H.ROOT, H.KNOWLEDGE
        H.ROOT, H.KNOWLEDGE = self.root, self.root / "knowledge"
        (self.root / "run").mkdir()
    def tearDown(self):
        H.ROOT, H.KNOWLEDGE = self._root, self._know
        self.tmp.cleanup()

    def _run(self, child_rc, proof):
        h = _stub(self.root / "run")
        plan = ("```lean\n" + PREMISE_ONLY + "\n```\n```json\n"
                + json.dumps({"hypotheses": [{"name": "erdos_99_hyp_rs", "kind": "published", "source": "RS 1962"}]}) + "\n```\n")
        h.ask = _judged(lambda purpose, prompt, **kw: plan)
        h._install_lemmas_module = lambda pdir: None
        attacked = []
        def attack(sub, name, *a, **k):
            attacked.append(name)
            return child_rc, argparse.Namespace(state={"proof": proof} if proof else {})
        h._attack_substatement = attack
        def verify():
            h.state["verify"] = {"all_clear": True}
            return h.state["verify"]
        h.stage_verify = verify
        return h, h.run_program(), attacked

    def test_a_provable_premise_is_certified_and_the_skeleton_closes(self):
        h, rc, attacked = self._run(0, "theorem erdos_99_hyp_rs : ∀ n : ℕ, foo n := by\n  intro n\n  rfl")
        self.assertEqual(attacked, ["erdos_99_hyp_rs"])
        self.assertEqual(rc, 0)
        self.assertEqual(h.state["residual"]["published"], 0)
        self.assertTrue(any(e[1] == "premises_attacked" for e in h.log.events))

    def test_a_premise_that_resists_stays_a_premise(self):
        h, rc, attacked = self._run(2, None)
        self.assertEqual(attacked, ["erdos_99_hyp_rs"])
        self.assertEqual(rc, 3)
        self.assertEqual(h.state["residual"]["published"], 1)


class RestoreSpliced(unittest.TestCase):
    """A re-plan that writes only a delta gets the certified material it relies on back, in the original order."""
    CURRENT = ("noncomputable def W (n : ℕ) : ℕ := n\n\n"
               "namespace erdos_99_hyp_a_ns\ntheorem erdos_99_hyp_a : W 1 = 1 := rfl\nend erdos_99_hyp_a_ns\n\n"
               "theorem erdos_99_hyp_a : W 1 = 1 := by\n  exact erdos_99_hyp_a_ns.erdos_99_hyp_a\n\n"
               "namespace erdos_99_hyp_b_ns\ntheorem erdos_99_hyp_b : W 2 = 2 := rfl\nend erdos_99_hyp_b_ns\n\n"
               "theorem erdos_99_hyp_b : W 2 = 2 := by\n  exact erdos_99_hyp_b_ns.erdos_99_hyp_b\n\n"
               "theorem erdos_99_hyp_c : True := by\n  sorry\n\n"
               "theorem erdos_99 : W 1 = 1 ∧ W 2 = 2 := ⟨erdos_99_hyp_a, erdos_99_hyp_b⟩")

    def test_delta_candidate_gets_defs_and_certified_hypotheses(self):
        delta = ("-- a new premise\ntheorem erdos_99_hyp_c : True := by\n  sorry\n\n"
                 "theorem erdos_99 : W 1 = 1 ∧ W 2 = 2 := ⟨erdos_99_hyp_a, erdos_99_hyp_b⟩")
        out = H.restore_spliced(delta, self.CURRENT)
        self.assertTrue(out.startswith("noncomputable def W"))
        a, b = out.index("namespace erdos_99_hyp_a_ns"), out.index("namespace erdos_99_hyp_b_ns")
        self.assertLess(a, b)
        self.assertLess(out.index("end erdos_99_hyp_a_ns"), b)                  # not nested
        self.assertLess(b, out.index("-- a new premise"))                          # the comment stays with its decl
        self.assertEqual(out.count("theorem erdos_99_hyp_a : W 1 = 1 := by"), 1)
        r = H.parse_residual(out, 99)
        self.assertTrue(r["glue_sorry_free"] and r["main_present"])
        self.assertEqual(r["metric"]["certified"], 2)

    def test_a_complete_candidate_is_untouched(self):
        self.assertEqual(H.restore_spliced(self.CURRENT, self.CURRENT), self.CURRENT)

    def test_a_candidate_that_drops_a_hypothesis_does_not_get_it_back(self):
        cand = "theorem erdos_99 : W 1 = 1 := by\n  exact erdos_99_hyp_a"
        out = H.restore_spliced(cand, self.CURRENT)
        self.assertIn("namespace erdos_99_hyp_a_ns", out)
        self.assertNotIn("erdos_99_hyp_b", out)


class FalseDirectionStops(unittest.TestCase):
    """masked #16 --open: the negation's plan called its target false and the loop still spent $6.94 on it."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self._root, self._know = H.ROOT, H.KNOWLEDGE
        H.ROOT, H.KNOWLEDGE = self.root, self.root / "knowledge"
        (self.root / "run").mkdir()
    def tearDown(self):
        H.ROOT, H.KNOWLEDGE = self._root, self._know
        self.tmp.cleanup()

    def _run(self, ledger):
        h = _stub(self.root / "run")
        skel = SKELETON.replace("-- PUBLISHED: Rosser–Schoenfeld 1962, Corollary 3\n"
                                "theorem erdos_99_hyp_rs : ∀ x : ℕ, 1 ≤ x → x ≤ x := by\n  sorry\n\n", "")
        plan = "```lean\n" + skel + "\n```\n```json\n" + json.dumps(ledger) + "\n```\n"
        h.ask = _judged(lambda purpose, prompt, **kw: plan)
        h._install_lemmas_module = lambda pdir: None
        attacked = []
        h._attack_substatement = lambda sub, name, *a, **k: attacked.append(name) or (2, argparse.Namespace(state={}))
        return h, h.run_program(), attacked

    def test_target_believed_false_stops_without_attacking(self):
        h, rc, attacked = self._run({"target_belief": "false", "route": "refuted numerically: eps = 1/22369620",
                                     "hypotheses": [{"name": "erdos_99_hyp_a", "kind": "conjecture"}]})
        self.assertEqual(attacked, [])
        self.assertTrue(any(e[1] == "target_believed_false" for e in h.log.events))
        self.assertIn("believes the target FALSE", h.state["stop_reason"])
        self.assertTrue((self.root / "programs" / "erdos_99" / "RESIDUAL.md").exists())

    def test_a_hypothesis_believed_false_is_not_attacked(self):
        h, rc, attacked = self._run({"target_belief": "unsure",
                                     "hypotheses": [{"name": "erdos_99_hyp_a", "kind": "conjecture", "believed_false": True}]})
        self.assertEqual(attacked, [])
        self.assertTrue(any(e[1] == "hypotheses_believed_false" for e in h.log.events))

    def test_unsure_attacks_as_before(self):
        h, rc, attacked = self._run({"target_belief": "unsure",
                                     "hypotheses": [{"name": "erdos_99_hyp_a", "kind": "conjecture"}]})
        self.assertEqual(attacked, ["erdos_99_hyp_a"])


class RefuteScriptRepair(unittest.TestCase):
    """#242: every refute script crashed on `"n % 4 ... %d" % N` after computing everything; one repair is allowed."""
    def test_a_crash_with_no_result_line_gets_one_repair(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        h = _stub(tmp.name)
        h.state["literature"] = ""
        asked = []
        scripts = iter(['```python\nprint("x")\n```', '```python\nprint("CLEAR: {}")\n```'])
        h.ask = lambda purpose, prompt, **kw: asked.append(prompt) or next(scripts)
        runs = iter([(1, "Traceback (most recent call last):\nValueError: unsupported format character"),
                     (0, 'INVARIANT: every n is odd (n <= 100)')])
        h._run_py = lambda script, timeout, cwd: next(runs)
        out, parsed = h._deductive_experiments(Path(tmp.name), 1, "- h : P")
        self.assertEqual(len(asked), 2)
        self.assertIn("CRASHED", asked[1])
        self.assertEqual(len(parsed["invariants"]), 1)
        self.assertTrue(any(e[1] == "experiments_repair" for e in h.log.events))

    def test_prompt_forbids_percent_formatting(self):
        self.assertIn("never `%`-formatting", H.EXPERIMENTS_PROMPT)


class BenchmarkWritesNoKnowledge(unittest.TestCase):
    def test_benchmark_refutations_live_with_the_program(self):
        H.BENCHMARK_PIDS.add("45592")
        self.addCleanup(H.BENCHMARK_PIDS.discard, "45592")
        self.assertEqual(H.refuted_dir("45592"), H.ROOT / "programs" / "erdos_45592" / "refuted")
        self.assertEqual(H.refuted_dir("242"), H.KNOWLEDGE / "refuted" / "242")



class DischargeNotSplit(unittest.TestCase):
    """Step 2: progress is a discharge. A split that discharges nothing is not spliced (it could make the frontier
    harder: #242's negation turned 'a counterexample exists' into a stronger existential), and two consecutive
    cycles without a discharge stop the program with the obstruction recorded."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self._root, self._know = H.ROOT, H.KNOWLEDGE
        H.ROOT, H.KNOWLEDGE = self.root, self.root / "knowledge"
        (self.root / "run").mkdir()
    def tearDown(self):
        H.ROOT, H.KNOWLEDGE = self._root, self._know
        self.tmp.cleanup()

    def _run(self, cycles):
        h = _stub(self.root / "run")
        h.args.min_child_budget = 0
        h.args.research_cycles = cycles
        skel = SKELETON.replace("-- PUBLISHED: Rosser–Schoenfeld 1962, Corollary 3\n"
                                "theorem erdos_99_hyp_rs : ∀ x : ℕ, 1 ≤ x → x ≤ x := by\n  sorry\n\n", "")
        plan = "```lean\n" + skel + "\n```\n```json\n" + json.dumps({"hypotheses": [{"name": "erdos_99_hyp_a", "difficulty": "hard"}]}) + "\n```\n"
        h.ask = _judged(lambda purpose, prompt, **kw: plan)
        h._install_lemmas_module = lambda pdir: None
        sub_path = self.root / "split.lean"
        sub_path.write_text("def foo (n : ℕ) : Prop := n = n\n\n"
                            "theorem erdos_99_hyp_a_hyp_stronger : ∀ n : ℕ, foo n ∧ foo (n + 1) := by\n  sorry\n\n"
                            "theorem erdos_99_hyp_a : ∀ n : ℕ, foo n := by\n  intro n\n  exact (erdos_99_hyp_a_hyp_stronger n).1")
        h._attack_substatement = lambda *a, **k: (3, argparse.Namespace(state={"residual": {"skeleton": str(sub_path), "meta": {}}}))
        return h, h.run_program()

    def test_a_pure_split_is_not_spliced_and_is_fed_forward(self):
        h, rc = self._run(1)
        self.assertTrue(any(e[1] == "split_only_refinement" for e in h.log.events))
        self.assertFalse(any(e[1] == "hypothesis_refined" for e in h.log.events))
        self.assertEqual({x["name"] for x in h.state["residual"]["hypotheses"] if x["open"]}, {"erdos_99_hyp_a"})
        failures = (self.root / "programs" / "erdos_99" / "failures.jsonl").read_text()
        self.assertIn("split only", failures)

    def test_two_cycles_without_a_discharge_stop_the_program(self):
        h, rc = self._run(4)
        stalled = [e for e in h.log.events if e[1] == "descent_stalled"]
        self.assertEqual(len(stalled), 1)
        self.assertEqual(stalled[0][2]["cycle"], 3)          # cycle 1 adopted the first skeleton; 2 and 3 only split
        self.assertFalse(any(e[2].get("cycle") == 4 for e in h.log.events if isinstance(e[2], dict)))
        self.assertIn("descent stalled", h.state["stop_reason"])
        # the cycles RUN, not the cap: #455's brief said "six cycles" for a run that stopped at 3 of 6
        self.assertIn("ran 3 of 4 cycle(s)", h.state["stop_reason"])

    def test_first_skeleton_counts_as_progress(self):
        h, rc = self._run(1)
        self.assertEqual(h.state["stall_cycles"], 0)


class ResumeFundsDirectionsFromTheirOwnSpend(unittest.TestCase):
    def test_a_resumed_direction_gets_its_prior_spend_plus_a_share(self):
        parent = H.Harness.__new__(H.Harness)
        parent.spent_usd = lambda: 11.25
        child = argparse.Namespace(spent_usd=lambda: 9.64, args=argparse.Namespace(run_budget=6.875))
        parent._fund_direction(child, 25.0)
        self.assertAlmostEqual(child.args.run_budget, 9.64 + 6.875)     # the old rule left it at 6.875 < 9.64


class DefsVisibleFromTheHypothesis(unittest.TestCase):
    """#242: a refinement splices the child's skeleton (open sub-hypothesis + its own defs) into <name>_ns; the
    sub-statement for that open hypothesis needs those defs, but never a sibling certified block's internals."""
    SKEL = ("def es (n : ℕ) : Prop := n = n\n\n"
            "namespace erdos_99_hyp_mul_ns\nopen Lean Meta in\nprivate def build : ℕ → MetaM Expr := fun _ => pure (mkNatLit 0)\n\n"
            "theorem erdos_99_hyp_mul : es 1 := rfl\nend erdos_99_hyp_mul_ns\n\n"
            "theorem erdos_99_hyp_mul : es 1 := by\n  exact erdos_99_hyp_mul_ns.erdos_99_hyp_mul\n\n"
            "namespace erdos_99_hyp_core_ns\ndef hard (r : ℕ) : Prop := r = 1\n\n"
            "namespace erdos_99_hyp_core_hyp_easy_ns\nprivate def helper : ℕ := 7\n\n"
            "theorem erdos_99_hyp_core_hyp_easy : es 2 := rfl\nend erdos_99_hyp_core_hyp_easy_ns\n\n"
            "theorem erdos_99_hyp_core_hyp_residual : ∀ r, hard r → es r := by\n  sorry\n\n"
            "theorem erdos_99_hyp_core : es 3 := by\n  rfl\nend erdos_99_hyp_core_ns\n\n"
            "theorem erdos_99 : es 3 := rfl")

    def test_the_containing_block_is_visible_and_siblings_are_not(self):
        sub = H.hypothesis_substatement(self.SKEL, "erdos_99_hyp_core_hyp_residual")
        self.assertIn("def hard", sub)                 # same block as the open hypothesis
        self.assertIn("def es", sub)                   # top level
        self.assertNotIn("MetaM", sub)                 # a sibling certified block's internals
        self.assertNotIn("helper", sub)                # a nested sibling block inside the containing one
        self.assertIn("theorem erdos_99_hyp_core_hyp_residual : ∀ r, hard r → es r := by\n  sorry", sub)

    def test_a_top_level_hypothesis_sees_only_top_level_defs(self):
        self.assertEqual([d.split()[1] for d in H.skeleton_defs(self.SKEL)], ["es"])



class RefinementMustBeEasier(unittest.TestCase):
    """#242: a refinement certified 'a type II certificate gives a representation' and left open 'every hard prime
    has one', the same core in certificate form, and Step 2 counted it as progress. A refinement is now spliced only
    if its open pieces are strictly easier than the hypothesis they replace."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self._root, self._know = H.ROOT, H.KNOWLEDGE
        H.ROOT, H.KNOWLEDGE = self.root, self.root / "knowledge"
        (self.root / "run").mkdir()
    def tearDown(self):
        H.ROOT, H.KNOWLEDGE = self._root, self._know
        self.tmp.cleanup()

    def _run(self, verdict, probe_ok=lambda name: False):
        h = _stub(self.root / "run")
        h.args.min_child_budget = 0
        skel = SKELETON.replace("-- PUBLISHED: Rosser–Schoenfeld 1962, Corollary 3\n"
                                "theorem erdos_99_hyp_rs : ∀ x : ℕ, 1 ≤ x → x ≤ x := by\n  sorry\n\n", "")
        plan = "```lean\n" + skel + "\n```\n```json\n" + json.dumps({"hypotheses": [{"name": "erdos_99_hyp_a", "difficulty": "hard"}]}) + "\n```\n"
        asked = []
        def ask(purpose, prompt, **kw):
            asked.append((purpose, prompt))
            if purpose == "refinement":
                return verdict
            return JUDGE_OK if purpose == "circularity" else plan
        h.ask = ask
        def check(body, name):
            if name.startswith("refinement"):
                ok = probe_ok(name)
                return {"ok": ok, "sorries": [], "errors": [] if ok else ["unsolved goals"], "infos": [], "body": body}
            if name.startswith("circularity"):
                return {"ok": False, "sorries": [], "errors": ["unsolved goals"], "infos": [], "body": body}
            return {"ok": True, "sorries": ["s"] if H.hole_count(body) else [], "errors": [], "infos": [], "body": body}
        h.check = check
        h._install_lemmas_module = lambda pdir: None
        sub_path = self.root / "sub.lean"
        sub_path.write_text("def foo (n : ℕ) : Prop := n = n\n\n"
                            "theorem erdos_99_hyp_a_hyp_suffices : ∀ n : ℕ, foo n := by\n  intro n\n  rfl\n\n"
                            "theorem erdos_99_hyp_a_hyp_cert : ∀ n : ℕ, foo n := by\n  sorry\n\n"
                            "theorem erdos_99_hyp_a : ∀ n : ℕ, foo n := by\n  intro n\n  exact erdos_99_hyp_a_hyp_cert n")
        h._attack_substatement = lambda *a, **k: (3, argparse.Namespace(state={"residual": {"skeleton": str(sub_path), "meta": {}}}))
        rc = h.run_program()
        return h, asked

    def test_a_reformulation_is_not_spliced(self):
        h, asked = self._run('```json\n{"easier": false, "why": "the same primes, in certificate form"}\n```')
        self.assertTrue(any(e[1] == "refinement_not_easier" for e in h.log.events))
        self.assertFalse(any(e[1] == "hypothesis_refined" for e in h.log.events))
        self.assertEqual({x["name"] for x in h.state["residual"]["hypotheses"] if x["open"]}, {"erdos_99_hyp_a"})
        self.assertIn("certificate form", (self.root / "programs" / "erdos_99" / "failures.jsonl").read_text())
        self.assertEqual(h.state["stall_cycles"], 0)            # cycle 1 still adopted the first skeleton

    def test_a_strictly_easier_refinement_is_spliced(self):
        h, asked = self._run('```json\n{"easier": true, "why": "fewer residue classes"}\n```')
        self.assertTrue(any(e[1] == "hypothesis_refined" for e in h.log.events))
        prompt = [p for k, p in asked if k == "refinement"][0]
        self.assertIn("erdos_99_hyp_a_hyp_suffices", prompt)      # certified pieces are shown
        self.assertIn("erdos_99_hyp_a_hyp_cert", prompt)          # and the open frontier

    def test_a_literal_restatement_is_caught_by_lean_without_a_judge(self):
        h, asked = self._run("unused", probe_ok=lambda name: True)   # both directions close
        self.assertTrue(any(e[1] == "refinement_not_easier" for e in h.log.events))
        self.assertFalse(any(k == "refinement" for k, _ in asked))

    def test_one_direction_is_a_subcase_not_a_restatement(self):
        """H implies any subcase of itself: a forward-only probe must fall through to the judge."""
        h, asked = self._run('```json\n{"easier": true, "why": "a subcase"}\n```', probe_ok=lambda name: name.endswith("-fwd"))
        self.assertTrue(any(k == "refinement" for k, _ in asked))
        self.assertTrue(any(e[1] == "hypothesis_refined" for e in h.log.events))

    def test_no_verdict_is_no_splice(self):
        h, asked = self._run("It looks like progress to me.")
        self.assertTrue(any(e[1] == "refinement_not_easier" and "no verdict" in e[2]["why"] for e in h.log.events))
