"""Premise weakening (--premise-weaken on, 2026-10-14): in the premise endgame, a published premise stated with sharp
constants is replaced by the weakest form the glue needs, the certified steps that restate it get their certificates
back for free, the weakened premise is attacked instead of the original, and `residual_improves` adopts the swap only
when the residual improves. Train #678's third run ended with every conjecture certified and Nagura's prime in
(x, 6x/5] open, although its glue needs only a prime in [(k+2)/2, k-1].

No provider calls; Lean and child attacks are mocked as in test_deductive_mode.py and test_allocation_options.py,
except the DEDUCTIVE_LEAN_TESTS=1-gated class at the bottom, which compiles real Lean (ERDOS_LEAN_PROJECT names a built
Lean project when the checkout has none, e.g. in a git worktree)."""
import argparse, json, os, sys, tempfile, threading, unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parent))
import harness as H
from test_deductive_mode import Log, _stub, JUDGE_OK


def plan_reply(skeleton: str, meta: dict | None = None) -> str:
    return "```lean\n" + skeleton + "\n```\n```json\n" + json.dumps(meta or {}) + "\n```\n"


FROZEN = """def gap99 (n p : ℕ) : Prop := n < p ∧ p ≤ 2 * n ∧ 2 ≤ p

theorem erdos_99 : ∀ n : ℕ, 25 ≤ n → ∃ p : ℕ, p.Prime ∧ gap99 n p := by
  sorry"""

STEP_OLD = "∀ n p : ℕ, p.Prime → n < p → 5 * p ≤ 6 * n → gap99 n p"
STEP_NEW = "∀ n p : ℕ, p.Prime → n < p → p ≤ 2 * n → gap99 n p"
SHARP = "∀ n : ℕ, 25 ≤ n → ∃ p : ℕ, p.Prime ∧ n < p ∧ 5 * p ≤ 6 * n"
LOOSE = "∀ n : ℕ, 25 ≤ n → ∃ p : ℕ, p.Prime ∧ n < p ∧ p ≤ 2 * n"

OPEN_STEP = f"""def gap99 (n p : ℕ) : Prop := n < p ∧ p ≤ 2 * n ∧ 2 ≤ p

def ratio99 : ℕ := 6

-- derived: the prime the premise gives lies in the gap
theorem erdos_99_hyp_step : {STEP_OLD} := by
  sorry

-- PUBLISHED: J. Nagura, Proc. Japan Acad. 28 (1952), 177-181
theorem erdos_99_hyp_sharp : {SHARP} := by
  sorry

theorem erdos_99 : ∀ n : ℕ, 25 ≤ n → ∃ p : ℕ, p.Prime ∧ gap99 n p := by
  intro n hn
  obtain ⟨p, hp, h1, h2⟩ := erdos_99_hyp_sharp n hn
  exact ⟨p, hp, erdos_99_hyp_step n p hp h1 h2⟩"""

# the step needs primality (`two_le`), which no generic tactic supplies: a restated step is re-certified only by
# running this script again (the `restate` variant), never by the bridge
STEP_PROOF = f"""theorem erdos_99_hyp_step : {STEP_OLD} := by
  intro n p hp h1 h2
  show n < p ∧ p ≤ 2 * n ∧ 2 ≤ p
  exact ⟨h1, by omega, hp.two_le⟩"""

# the skeleton in force: the step is certified (spliced), only the published premise is open
IN_FORCE = H.splice_hypothesis(OPEN_STEP, "erdos_99_hyp_step", STEP_PROOF)

META = {"hypotheses": [{"name": "erdos_99_hyp_sharp", "kind": "published", "difficulty": "hard",
                        "source": "J. Nagura, Proc. Japan Acad. 28 (1952), 177-181"},
                       {"name": "erdos_99_hyp_step", "kind": "conjecture", "difficulty": "elementary"}]}

# the proposal: the premise replaced by Bertrand's form, the step restated with the looser bound (outline style: the
# certified namespace is not repeated, the restated step carries `sorry`)
PROPOSAL = f"""def gap99 (n p : ℕ) : Prop := n < p ∧ p ≤ 2 * n ∧ 2 ≤ p

def ratio99 : ℕ := 6

-- re-derived: the looser bound still lands in the gap
theorem erdos_99_hyp_step : {STEP_NEW} := by
  sorry

-- weakening of Nagura 1952: Bertrand's postulate is enough here
theorem erdos_99_hyp_loose : {LOOSE} := by
  sorry

theorem erdos_99 : ∀ n : ℕ, 25 ≤ n → ∃ p : ℕ, p.Prime ∧ gap99 n p := by
  intro n hn
  obtain ⟨p, hp, h1, h2⟩ := erdos_99_hyp_loose n hn
  exact ⟨p, hp, erdos_99_hyp_step n p hp h1 h2⟩"""

W_JSON = {"weakenings": [{"premise": "erdos_99_hyp_sharp", "weakened": "erdos_99_hyp_loose", "how": "loosened",
                          "mathlib": None, "from_premise": None, "difficulty": "moderate",
                          "why": "the glue only needs p ≤ 2n"}],
          "rederived": ["erdos_99_hyp_step"], "route": "Bertrand gives the prime; the step puts it in the gap"}

LOOSE_PROOF = f"""theorem erdos_99_hyp_loose : {LOOSE} := by
  intro n hn
  exact Nat.exists_prime_lt_and_le_two_mul n (by omega)"""
STEP_NEW_PROOF = f"""theorem erdos_99_hyp_step : {STEP_NEW} := by
  intro n p hp h1 h2
  exact ⟨h1, h2, hp.two_le⟩"""


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


def _parsed(skeleton=IN_FORCE, meta=META):
    return H.parse_residual(skeleton, 99, meta)


class PremiseConstants(unittest.TestCase):
    def test_constants_of_a_sharp_premise(self):
        self.assertEqual(H.premise_constants(SHARP), ["25", "5", "6"])
        self.assertEqual(H.premise_constants("∀ k : ℕ, 7 ≤ k → 2 ^ k ≤ erdos81727_L k"), ["7", "2"])
        self.assertEqual(H.premise_constants("∀ x : ℝ, 2 ≤ x → f x < 1.25506 * x / Real.log x"), ["2", "1.25506"])

    def test_structural_numerals_and_digits_in_names_do_not_count(self):
        self.assertEqual(H.premise_constants("∀ x : ℕ, 1 ≤ x → 0 < x + erdos81727_L x"), [])

    def test_a_premise_stated_through_a_definition_keeps_its_constants_there(self):
        defs = ["def e86081Nagura : Prop :=\n  ∀ x : ℝ, 25 ≤ x → ∃ p : ℕ, p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) < 6 * x / 5",
                "def e86081Lk (k : ℕ) : ℕ := (Finset.Icc 1 k).lcm id"]
        self.assertEqual(H.premise_constants("e86081Nagura", defs), ["25", "6", "5"])
        self.assertEqual(H.premise_constants("e86081Other", defs), [])


class AlphaNorm(unittest.TestCase):
    def test_bound_names_bare_and_grouped(self):
        self.assertEqual(H.bound_names(SHARP), ["n", "p"])
        self.assertEqual(H.bound_names("∀ (x : ℝ) (hx : 25 ≤ x), ∃ p q : ℕ, p < q"), ["x", "hx", "p", "q"])
        self.assertEqual(H.bound_names("∑ i ∈ Finset.range n, f i = 0"), ["i"])

    def test_renamed_bound_variables_compare_equal(self):
        # train #678 cycle 4 restated Nair with `n` for `k`
        self.assertEqual(H.alpha_norm("∀ k : ℕ, 7 ≤ k → 2 ^ k ≤ erdos81727_L k"),
                         H.alpha_norm("∀ n : ℕ, 7 ≤ n → 2 ^ n ≤ erdos81727_L n"))

    def test_a_different_constant_or_name_does_not(self):
        self.assertNotEqual(H.alpha_norm("∀ k : ℕ, 7 ≤ k → 2 ^ k ≤ L k"), H.alpha_norm("∀ k : ℕ, 8 ≤ k → 2 ^ k ≤ L k"))
        self.assertNotEqual(H.alpha_norm("∀ k : ℕ, 7 ≤ k → 2 ^ k ≤ L k"), H.alpha_norm("∀ k : ℕ, 7 ≤ k → 2 ^ k ≤ M k"))


def _weakened_parse(certified: bool):
    skel = PROPOSAL if not certified else H.splice_hypothesis(PROPOSAL, "erdos_99_hyp_loose", LOOSE_PROOF)
    meta = {"hypotheses": [{"name": "erdos_99_hyp_loose", "kind": "published", "source": "weakening of Nagura"},
                           {"name": "erdos_99_hyp_step", "kind": "conjecture"}]}
    p = H.parse_residual(H.splice_hypothesis(skel, "erdos_99_hyp_step", STEP_NEW_PROOF), 99, meta)
    return p


class ResidualImproves(unittest.TestCase):
    REG = [{"premise": "erdos_99_hyp_sharp", "premise_statement": SHARP, "weakened": "erdos_99_hyp_loose",
            "statement": LOOSE, "implied": True, "restatement": False}]

    def test_premise_replaced_by_a_certified_weakening_is_progress(self):
        new, old = _weakened_parse(certified=True), _parsed()
        self.assertEqual((new["metric"]["published"], old["metric"]["published"]), (0, 1))
        self.assertTrue(H.residual_improves(new, old))

    def test_an_open_weakening_lean_derives_from_the_premise_breaks_the_tie(self):
        new, old = _weakened_parse(certified=False), _parsed()
        self.assertEqual(new["metric"], {**old["metric"], "certified": new["metric"]["certified"]})
        self.assertFalse(H.residual_improves(new, old))                       # unregistered: a tie, no improvement
        H.annotate_weakenings(new, self.REG)
        self.assertEqual(next(h for h in new["hypotheses"] if h["name"] == "erdos_99_hyp_loose")["weakens"],
                         "erdos_99_hyp_sharp")
        self.assertTrue(H.residual_improves(new, old))

    def test_a_restatement_or_an_unchecked_entry_never_counts(self):
        for entry in ({**self.REG[0], "restatement": True}, {**self.REG[0], "implied": False}):
            new = H.annotate_weakenings(_weakened_parse(certified=False), [entry])
            self.assertFalse(H.residual_improves(new, _parsed()))

    def test_a_weakening_that_opens_a_conjecture_is_not_progress(self):
        meta = {"hypotheses": [{"name": "erdos_99_hyp_loose", "kind": "published", "source": "weakening"}]}
        cand = H.splice_hypothesis(PROPOSAL, "erdos_99_hyp_loose", LOOSE_PROOF)    # the restated step stays open
        new = H.parse_residual(cand, 99, meta)
        self.assertEqual(new["metric"]["open_conjectures"], 1)
        self.assertFalse(H.residual_improves(new, _parsed()))

    def test_the_tie_break_needs_every_other_premise_unchanged(self):
        new = H.annotate_weakenings(_weakened_parse(certified=False), self.REG)
        extra = {"name": "erdos_99_hyp_other", "statement": "∀ n : ℕ, 3 ≤ n → n ≤ n", "kind": "published", "open": True,
                 "complexity": 1}
        old = _parsed()
        old_two = {**old, "hypotheses": old["hypotheses"] + [extra], "metric": {**old["metric"], "published": 2}}
        new_two = {**new, "hypotheses": new["hypotheses"] + [{**extra, "statement": "∀ n : ℕ, 4 ≤ n → n ≤ n"}],
                   "metric": {**new["metric"], "published": 2}}
        self.assertFalse(H.premises_weakened(new_two, old_two))


class RecertifyVariants(unittest.TestCase):
    def test_bridge_and_restate_texts(self):
        v = H.recertify_variants(PROPOSAL, IN_FORCE, ["erdos_99_hyp_step"])["erdos_99_hyp_step"]
        bridge, restate = v["variants"]["bridge"], v["variants"]["restate"]
        # the bridge keeps the old certificate verbatim and derives the new statement from it
        self.assertIn("namespace erdos_99_hyp_step_ns", bridge)
        self.assertIn(STEP_OLD, bridge)
        self.assertIn(f"theorem erdos_99_hyp_step : {STEP_NEW} := by", bridge)
        self.assertIn("exact erdos_99_hyp_step_ns.erdos_99_hyp_step", bridge)
        self.assertIn("apply erdos_99_hyp_step_ns.erdos_99_hyp_step", bridge)
        # the restatement runs the old script under the new statement, inside the namespace
        self.assertNotIn(STEP_OLD, restate)
        self.assertIn("exact ⟨h1, by omega, hp.two_le⟩", restate)
        self.assertEqual(restate.count(f"theorem erdos_99_hyp_step : {STEP_NEW}"), 2)
        self.assertEqual(H.hole_count(bridge) + H.hole_count(restate), 0)

    def test_only_steps_certified_in_force_have_variants(self):
        self.assertEqual(H.recertify_variants(PROPOSAL, IN_FORCE, ["erdos_99_hyp_loose"]), {})
        self.assertEqual(H.recertify_variants(PROPOSAL, OPEN_STEP, ["erdos_99_hyp_step"]), {})

    def test_a_namespace_already_restored_is_not_inserted_twice(self):
        ns = next(m.group(0) for m in H.SPLICED_NS_RE.finditer(IN_FORCE))
        cand = PROPOSAL.replace("-- re-derived", ns + "\n\n-- re-derived")
        v = H.recertify_variants(cand, IN_FORCE, ["erdos_99_hyp_step"])["erdos_99_hyp_step"]
        self.assertNotIn("namespace", v["variants"]["bridge"])
        self.assertNotIn("restate", v["variants"])

    def test_a_dropped_definition_an_old_certificate_needs_comes_back(self):
        # train #678 cycle 4: the plan unfolded `erdos81727_B` in `hyp_size` and dropped the definition, so the old
        # certificate, which names it, could not be put back until the definition was
        current = ("def a99 : ℕ := 3\n\ndef b99 : ℕ := a99 + 1\n\ndef c99 : ℕ := 7\n\n"
                   "namespace erdos_99_hyp_x_ns\ntheorem erdos_99_hyp_x : b99 = 4 := by\n  rfl\nend erdos_99_hyp_x_ns\n\n"
                   "theorem erdos_99_hyp_x : b99 = 4 := by\n  exact erdos_99_hyp_x_ns.erdos_99_hyp_x")
        cand = "def c99 : ℕ := 7\n\ntheorem erdos_99_hyp_x : 3 + 1 = 4 := by\n  sorry"
        got = H.defs_for_certificates(cand, current, ["erdos_99_hyp_x"])
        self.assertEqual([H.decl_name(d) for d in got], ["a99", "b99"])     # b99 named, a99 through b99, in order
        self.assertEqual(H.defs_for_certificates(current, current, ["erdos_99_hyp_x"]), [])
        self.assertEqual(H.defs_for_certificates(cand, current, ["erdos_99_hyp_other"]), [])

    def test_block_variants_report_their_lines(self):
        v = H.recertify_variants(PROPOSAL, IN_FORCE, ["erdos_99_hyp_step"])["erdos_99_hyp_step"]
        text, lines = H.apply_block_variants(PROPOSAL, {"erdos_99_hyp_step": (v["span"], "X\nY\nZ")})
        first, last = lines["erdos_99_hyp_step"]
        self.assertEqual(text.splitlines()[first - 1:last], ["X", "Y", "Z"])

    def test_error_lines_take_the_header_off(self):
        imports = list(H.DEFAULT_IMPORTS)
        off = H.compose_offset("theorem a : True := by\n  trivial", imports)
        src = H.compose("theorem a : True := by\n  trivial", imports)
        self.assertEqual(src.splitlines()[off], "theorem a : True := by")
        self.assertEqual(H.error_lines([f"line {off + 2}:3: unsolved goals", "no line here"], off), {2})


class ProbeSource(unittest.TestCase):
    def test_generic_probe(self):
        src = H.weakening_probe_source(["def gap99 (n p : ℕ) : Prop := n < p ∧ p ≤ 2 * n"], SHARP, LOOSE, ["gap99"])
        self.assertIn(f"theorem weakening_probe (hP : {SHARP}) : {LOOSE} := by", src)
        self.assertIn("| exact hP", src)
        self.assertIn("peel hP", src)
        self.assertIn("(try unfold gap99 at hP)", src)
        self.assertTrue(src.startswith("def gap99"))

    def test_a_certified_step_the_script_names_comes_with_its_proof(self):
        # train #678's blueprint run derived the weakening from the certified `hyp_choice_q`; with the definitions alone
        # the probe answered `Unknown identifier`
        src = H.weakening_probe_source(["def gap99 (n p : ℕ) : Prop := n < p ∧ p ≤ 2 * n ∧ 2 ≤ p"], SHARP, LOOSE,
                                       script="intro n hn\nhave := erdos_99_hyp_step\nexact hP n hn |>.imp fun p h => ⟨h.1, h.2.1, by omega⟩")
        out = H.certified_context(src, IN_FORCE)
        self.assertIn("namespace erdos_99_hyp_step_ns", out)
        self.assertIn(f"theorem erdos_99_hyp_step : {STEP_OLD} := by\n  exact erdos_99_hyp_step_ns.erdos_99_hyp_step", out)
        self.assertLess(out.index("namespace erdos_99_hyp_step_ns"), out.index("theorem weakening_probe"))

    def test_an_open_hypothesis_is_never_put_back(self):
        src = H.weakening_probe_source([], SHARP, LOOSE, script="exact erdos_99_hyp_sharp")
        self.assertEqual(H.certified_context(src, IN_FORCE), src)

    def test_the_proposals_script_is_indented_under_the_probe(self):
        src = H.weakening_probe_source([], SHARP, LOOSE, script="intro n hn\nobtain ⟨p, hp⟩ := hP n hn\nexact ⟨p, hp.1, hp.2.1, by omega⟩")
        self.assertIn(":= by\n  intro n hn\n  obtain", src)
        self.assertNotIn("first", src)


def _loop_harness(root, reply=None, spent=1.0, cycles=1, check=None, attack=None, repair="", **args):
    """The premise endgame: IN_FORCE has every conjecture certified and one published premise open, rated hard."""
    h = _stub(root / "run", statement=FROZEN, residual={"meta": META})
    h.args.premise_attack = "full"
    h.args.premise_weaken = "on"
    h.args.research_cycles = cycles
    h.args.min_child_budget = 2.5
    h.args.plan_repairs = 1
    for k, v in args.items():
        setattr(h.args, k, v)
    h.spent_usd = lambda: spent
    h._install_lemmas_module = lambda pdir: None
    h.verified = []
    h.stage_verify = lambda: (h.verified.append(1), h.state.__setitem__("verify", {"all_clear": True}))
    pdir = root / "programs" / "erdos_99"
    pdir.mkdir(parents=True, exist_ok=True)
    (pdir / "Residual.lean").write_text(IN_FORCE)
    h.asked = []
    reply = plan_reply(PROPOSAL, W_JSON) if reply is None else reply

    def ask(purpose, prompt, **kw):
        h.asked.append((purpose, prompt))
        if purpose in ("circularity", "refinement"):
            return JUDGE_OK
        return reply if purpose == "weaken" else repair if purpose == "plan-repair" else plan_reply(IN_FORCE)
    h.ask = ask
    h.checked = []
    base = h.check

    def mock_check(body, name):
        h.checked.append(name)
        if check:
            r = check(body, name)
            if r is not None:
                return {"infos": [], "body": body, "sorries": [], "errors": [], **r}
        if name.endswith("-bwd"):                       # the weakening is not the premise restated
            return {"ok": False, "sorries": [], "errors": ["line 9:2: unsolved goals"], "infos": [], "body": body}
        return base(body, name)
    h.check = mock_check
    h.attacks = []

    def default_attack(sub, name, sdir, cycle, module, remaining, recursive=False, cheap=False, hint="", **kw):
        h.attacks.append({"name": name, "cheap": cheap, "hint": hint, "sub": sub, **kw})
        if name == "erdos_99_hyp_loose":
            return 0, argparse.Namespace(state={"proof": LOOSE_PROOF})
        return 3, argparse.Namespace(state={"attempts": [], "stop_reason": "rounds exhausted"})
    h._attack_substatement = attack.__get__(h) if attack else default_attack
    return h


def _events(h, name):
    return [e[2] for e in h.log.events if e[1] == name]


class WeakeningTarget(Isolated):
    def _target(self, meta=META, fails=None, state=None, skeleton=IN_FORCE):
        h = _stub(self.root / "run", statement=FROZEN, **(state or {}))
        return h._weakening_target(H.parse_residual(skeleton, 99, meta), skeleton, fails or {})

    def test_a_hard_premise_with_constants_is_the_target(self):
        self.assertEqual(self._target()["name"], "erdos_99_hyp_sharp")

    def test_a_premise_rated_easier_gets_its_direct_attack_first(self):
        meta = {"hypotheses": [{**META["hypotheses"][0], "difficulty": "moderate"}, META["hypotheses"][1]]}
        self.assertIsNone(self._target(meta))
        self.assertEqual(self._target(meta, fails={"erdos_99_hyp_sharp": 1})["name"], "erdos_99_hyp_sharp")

    def test_no_constant_no_target(self):
        skel = IN_FORCE.replace(SHARP, "∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ n < p")
        self.assertIsNone(self._target(skeleton=skel))

    def test_a_premise_is_offered_once_and_a_weakening_is_never_weakened_again(self):
        self.assertIsNone(self._target(state={"weaken_tried": {H.sweep_key(SHARP): {"name": "x"}}}))
        self.assertIsNone(self._target(state={"weakenings": [{"statement": SHARP}]}))


class WeakeningMoveInTheLoop(Isolated):
    def test_off_by_default_the_premise_is_attacked_as_before(self):
        h = _loop_harness(self.root, premise_weaken="off")
        h.run_program()
        self.assertNotIn("weaken", [p for p, _ in h.asked])
        self.assertEqual([a["name"] for a in h.attacks], ["erdos_99_hyp_sharp"])
        self.assertEqual(H.parse_residual(IN_FORCE, 99), H.parse_residual((self.pdir() / "Residual.lean").read_text(), 99))
        self.assertEqual(H.build_parser().parse_args(["run", "--problem", "1"]).premise_weaken, "off")

    def test_a_certified_weakening_is_adopted_and_closes_the_proof(self):
        h = _loop_harness(self.root)
        rc = h.run_program()
        self.assertEqual([p for p, _ in h.asked].count("weaken"), 1)
        # the weakened premise was attacked, with the original premise and the reason in its literature
        self.assertEqual([a["name"] for a in h.attacks], ["erdos_99_hyp_loose"])
        self.assertIn("THIS STATEMENT WEAKENS the published premise `erdos_99_hyp_sharp`", h.attacks[0]["hint"])
        self.assertIn(SHARP, h.attacks[0]["hint"])
        # the restated step was re-certified for free (the bridge compiled), not attacked
        self.assertEqual(_events(h, "pieces_recertified")[0]["pieces"], {"erdos_99_hyp_step": "bridge"})
        w = _events(h, "premise_weakened")[0]
        self.assertTrue(w["certified"] and w["implied"])
        self.assertEqual(w["metric"]["published"], 0)
        final = (self.pdir() / "Residual.lean").read_text()
        self.assertNotIn("theorem erdos_99_hyp_sharp", final)
        self.assertIn("namespace erdos_99_hyp_loose_ns", final)
        self.assertEqual(H.hole_count(final), 0)
        self.assertEqual(rc, 0)
        self.assertEqual(h.verified, [1])
        ledger = [json.loads(l) for l in (self.pdir() / "ledger.jsonl").read_text().splitlines()]
        self.assertTrue(any(r["kind"] == "weakening" and r["adopted"] and r["certified"] for r in ledger))
        self.assertIn("namespace erdos_99_hyp_loose_ns", (self.pdir() / "Lemmas.lean").read_text())
        self.assertEqual(h.state["weakenings"][0]["weakened"], "erdos_99_hyp_loose")

    def test_an_open_weakening_lean_derives_from_the_premise_is_adopted_but_is_no_discharge(self):
        h = _loop_harness(self.root)
        base = h._attack_substatement

        def fail(sub, name, *a, **kw):
            base(sub, name, *a, **kw)
            return 3, argparse.Namespace(state={"attempts": [], "stop_reason": "rounds exhausted"})
        h._attack_substatement = fail
        rc = h.run_program()
        self.assertEqual(rc, 3)
        w = _events(h, "premise_weakened")[0]
        self.assertTrue(w["implied"])
        self.assertFalse(w["certified"])
        final = (self.pdir() / "Residual.lean").read_text()
        self.assertIn("theorem erdos_99_hyp_loose", final)
        self.assertNotIn("theorem erdos_99_hyp_sharp", final)
        p = H.parse_residual(final, 99, h.state["residual"]["meta"])
        loose = next(x for x in p["hypotheses"] if x["name"] == "erdos_99_hyp_loose")
        self.assertEqual(loose["kind"], "published")                    # the citation covers it: Lean derived it
        self.assertIn("weakening of erdos_99_hyp_sharp", loose["source"])
        self.assertEqual(h.state["stall_cycles"], 1)                     # adopted, but nothing was discharged
        self.assertEqual([a["name"] for a in h.attacks], ["erdos_99_hyp_loose"])   # the original is not attacked too
        self.assertFalse(any(e[1] == "circular_premise" for e in h.log.events))

    def test_an_open_weakening_lean_cannot_derive_is_not_adopted(self):
        def check(body, name):
            if "weakening-c1-fwd" in name:
                return {"ok": False, "errors": ["line 9:2: unsolved goals"]}
        h = _loop_harness(self.root, check=check)
        base = h._attack_substatement
        h._attack_substatement = lambda sub, name, *a, **kw: (base(sub, name, *a, **kw),
                                                               (3, argparse.Namespace(state={})))[1]
        h.run_program()
        rejected = _events(h, "weakening_not_adopted")[0]
        self.assertFalse(rejected["implied"])
        self.assertIn("does not derive", rejected["reason"])
        self.assertEqual((self.pdir() / "Residual.lean").read_text(), IN_FORCE)
        fails = [json.loads(l) for l in (self.pdir() / "failures.jsonl").read_text().splitlines()]
        self.assertTrue(any(f.get("kind") == "weakening" and f["name"] == "erdos_99_hyp_sharp" for f in fails))
        self.assertEqual(H.failure_counts(self.pdir()).get("erdos_99_hyp_sharp"), None)
        self.assertTrue((self.pdir() / "alternatives.jsonl").exists())
        self.assertEqual([a["name"] for a in h.attacks], ["erdos_99_hyp_loose"])

    def test_a_declined_proposal_leaves_the_premise_to_its_direct_attack(self):
        reply = '```json\n{"weakenings": [], "route": "the glue needs the sharp constant"}\n```'
        h = _loop_harness(self.root, reply=reply)
        h.run_program()
        self.assertEqual(len(_events(h, "premise_weaken_declined")), 1)
        self.assertEqual([a["name"] for a in h.attacks], ["erdos_99_hyp_sharp"])
        self.assertEqual((self.pdir() / "Residual.lean").read_text(), IN_FORCE)

    def test_a_proposal_that_alters_the_frozen_theorem_is_rejected_unread(self):
        bad = PROPOSAL.replace("theorem erdos_99 : ∀ n : ℕ, 25 ≤ n", "theorem erdos_99 : ∀ n : ℕ, 26 ≤ n")
        h = _loop_harness(self.root, reply=plan_reply(bad, W_JSON))
        h.run_program()
        self.assertIn("frozen", _events(h, "premise_weaken_rejected")[0]["reason"])
        self.assertEqual([a["name"] for a in h.attacks], ["erdos_99_hyp_sharp"])

    def test_a_definition_changed_in_place_is_rejected(self):
        bad = PROPOSAL.replace("def ratio99 : ℕ := 6", "def ratio99 : ℕ := 2")
        h = _loop_harness(self.root, reply=plan_reply(bad, W_JSON))
        h.run_program()
        self.assertIn("`ratio99` in place", _events(h, "premise_weaken_rejected")[0]["reason"])

    def test_a_reused_premise_name_is_renamed(self):
        reply = plan_reply(PROPOSAL.replace("erdos_99_hyp_loose", "erdos_99_hyp_sharp"),
                           {**W_JSON, "weakenings": [{**W_JSON["weakenings"][0], "weakened": "erdos_99_hyp_sharp"}]})
        h = _loop_harness(self.root, reply=reply)
        h.run_program()
        self.assertEqual(_events(h, "premise_weakened")[0]["weakened"], "erdos_99_hyp_sharp_weak")
        self.assertEqual([a["name"] for a in h.attacks], ["erdos_99_hyp_sharp_weak"])

    def test_a_compile_failure_gets_one_repair_round(self):
        def check(body, name):
            if name.startswith("weaken-c1"):
                return {"ok": False, "errors": ["line 12:4: unknown identifier 'gap'"]}
        h = _loop_harness(self.root, check=check, repair=plan_reply(PROPOSAL, W_JSON))
        h.run_program()
        self.assertEqual([p for p, _ in h.asked if p in ("weaken", "plan-repair")], ["weaken", "plan-repair"])
        self.assertEqual(len(_events(h, "premise_weakened")), 1)      # the repaired candidate compiled

    def test_the_bridge_falls_back_to_the_restated_script_located_by_line(self):
        def check(body, name):
            if name == "weaken-recert-c1-0":
                off = H.compose_offset(body, list(H.DEFAULT_IMPORTS))
                ln = next(i for i, l in enumerate(body.splitlines(), 1) if "| exact erdos_99_hyp_step_ns" in l)
                return {"ok": False, "errors": [f"line {ln + off}:4: unsolved goals"]}
        h = _loop_harness(self.root, check=check)
        h.run_program()
        self.assertEqual(_events(h, "pieces_recertified")[0]["pieces"], {"erdos_99_hyp_step": "restate"})
        self.assertEqual(len(_events(h, "premise_weakened")), 1)

    def test_a_step_neither_variant_recovers_gets_one_cheap_attempt_with_its_old_proof(self):
        def check(body, name):
            if name.startswith("weaken-recert"):
                return {"ok": False, "errors": ["timed out"], "timeout": True}

        def attack(self_, sub, name, sdir, cycle, module, remaining, recursive=False, cheap=False, hint="", **kw):
            self_.attacks.append({"name": name, "cheap": cheap, "hint": hint})
            if name == "erdos_99_hyp_loose":
                return 0, argparse.Namespace(state={"proof": LOOSE_PROOF})
            return 0, argparse.Namespace(state={"proof": STEP_NEW_PROOF})
        h = _loop_harness(self.root, check=check, attack=attack)
        h.run_program()
        self.assertEqual(_events(h, "pieces_not_recertified")[0]["pieces"], ["erdos_99_hyp_step"])
        step = next(a for a in h.attacks if a["name"] == "erdos_99_hyp_step")
        self.assertTrue(step["cheap"])
        self.assertIn("THIS STEP WAS CERTIFIED IN LEAN", step["hint"])
        self.assertIn("exact ⟨h1, by omega, hp.two_le⟩", step["hint"])
        self.assertEqual(len(_events(h, "premise_weakened")), 1)
        self.assertEqual(H.hole_count((self.pdir() / "Residual.lean").read_text()), 0)

    def test_offered_once_across_cycles(self):
        reply = '```json\n{"weakenings": []}\n```'
        h = _loop_harness(self.root, reply=reply, cycles=2)
        h.run_program()
        self.assertEqual([p for p, _ in h.asked].count("weaken"), 1)

    def test_below_a_dollar_the_move_is_skipped(self):
        h = _loop_harness(self.root, spent=4.4, run_budget=5.0)
        h.run_program()
        self.assertNotIn("weaken", [p for p, _ in h.asked])
        self.assertEqual(len(_events(h, "premise_weaken_skipped")), 1)

    def test_cheap_premise_policy_tries_the_weakening_free_only(self):
        h = _loop_harness(self.root, premise_attack="cheap")
        h.run_program()
        self.assertEqual([p for p, _ in h.asked].count("weaken"), 1)
        self.assertEqual(h.attacks, [])                                   # no child under --premise-attack cheap
        self.assertEqual(len(_events(h, "premise_weakened")), 1)         # open, Lean-derived: adopted


class PlanAdoptionHonoursTheRegistry(Isolated):
    """A plan that keeps a Lean-checked weakening in place of the premise ties every count; the harness's registry, not
    the plan's ledger, says it is weaker."""

    def test_tie_break_from_the_registry_only(self):
        cdir = self.root / "c1"
        cdir.mkdir()
        cand = H.splice_hypothesis(PROPOSAL, "erdos_99_hyp_step", STEP_NEW_PROOF)
        meta = {"hypotheses": [{"name": "erdos_99_hyp_loose", "kind": "published", "source": "weakening of Nagura",
                                "weakens": "erdos_99_hyp_sharp", "weakens_statement": SHARP}]}
        for registry, adopted in (([], False), (ResidualImproves.REG, True)):
            h = _stub(self.root / "run", statement=FROZEN, weakenings=registry)
            v = h._consider_skeleton(cand, meta, _parsed(), H.statement_prefix(FROZEN), 2, [], cdir, current_src=IN_FORCE)
            self.assertEqual(bool(v.get("adopted")), adopted, v.get("reason"))


class PromptAndPurposes(unittest.TestCase):
    def test_the_prompt_formats_and_says_what_matters(self):
        p = H.WEAKEN_PROMPT.format(pid=99, name="erdos_99_hyp_sharp", difficulty="hard", source="Nagura 1952",
                                   statement=SHARP, history="", frozen=FROZEN, residual=IN_FORCE, hyp_prefix="erdos_99_hyp_")
        for s in ("WEAKEST statement", "existentially", "NEW name", "keeps its NAME", "VERBATIM", '"weakenings": []',
                  "from_premise", "Never change the body of an existing `def` in place"):
            self.assertIn(s, p)
        self.assertIn("weaken", H.Harness.IDEA_PURPOSES)
        self.assertIn("weaken", H.Harness.RESEARCH_GUIDANCE_PURPOSES)


def _lean_project() -> Path:
    return Path(os.environ.get("ERDOS_LEAN_PROJECT") or H.FORMAL)


REAL_FROZEN = """def erdos97_gap (n p : ℕ) : Prop := n < p ∧ p ≤ 2 * n

theorem erdos_97 : ∀ n : ℕ, 25 ≤ n → ∃ p : ℕ, p.Prime ∧ erdos97_gap n p := by
  sorry"""


def _real(text: str) -> str:
    return text.replace("gap99", "erdos97_gap").replace("ratio99", "erdos97_ratio").replace("erdos_99", "erdos_97")


@unittest.skipUnless(os.environ.get("DEDUCTIVE_LEAN_TESTS") == "1", "set DEDUCTIVE_LEAN_TESTS=1 for real Lean checks")
class WeakeningInLean(unittest.TestCase):
    """The free half of the move in real Lean, on the fixture above with real primes: the candidate compiles, the
    restated step's bridge fails and its old script proves the new statement, Lean derives the weakening from the sharp
    premise (and not the converse), and the weakened premise falls to the Mathlib theorem the proposal names. Then the
    whole transaction with a canned proposal and no child: adopted, and the skeleton is a sorry-free proof."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        proj = _lean_project()
        self._saved = (H.FORMAL, H.MATHLIB_SRC, H._INDEX, dict(H._decl_cache), H.ROOT, H.KNOWLEDGE)
        if proj != H.FORMAL:                       # a worktree: point the index and module checks at the built project
            H.FORMAL, H.MATHLIB_SRC = proj, proj / ".lake" / "packages" / "mathlib" / "Mathlib"
            H._INDEX, H._decl_cache = H.DeclIndex(), {}
        H.ROOT, H.KNOWLEDGE = self.root, self.root / "knowledge"
        h = H.Harness.__new__(H.Harness)
        h.problem = {"id": "97", "statement": "weakening smoke", "tags": []}
        h.state = {"statement": REAL_FROZEN, "residual": {"meta": {"hypotheses": [
            {"name": "erdos_97_hyp_sharp", "kind": "published", "difficulty": "hard", "source": "J. Nagura 1952"},
            {"name": "erdos_97_hyp_step", "kind": "conjecture"}]}}}
        h.log = Log()
        h.run_dir = self.root / "run"
        h.args = argparse.Namespace(no_cascade=False, subgoal_prover=None, run_budget=5.0, research_cycles=1,
                                    review_every=1, hyps_per_cycle=4, refute="off", llm_timeout=60, review_wait=0,
                                    min_child_budget=2.5, residual_depth=2, residual_depth_current=1, sweep="off",
                                    premise_attack="full", premise_weaken="on", plan_repairs=1)
        h.imports, h.libraries = list(H.DEFAULT_IMPORTS), []
        h.lean = H.LeanChecker(proj, 600)
        h._lock = threading.Lock()
        h.checks = 0
        h.direction = None
        h.save = lambda: None
        h.report = lambda proved: None
        h.spent_usd = lambda: 0.0
        h._check_run_budget = lambda purpose: None
        h._install_lemmas_module = lambda pdir: None
        self.h = h
        self.in_force = _real(IN_FORCE)
        self.proposal = _real(PROPOSAL)

    def tearDown(self):
        H.FORMAL, H.MATHLIB_SRC, H._INDEX, cache, H.ROOT, H.KNOWLEDGE = self._saved
        H._decl_cache.clear()
        H._decl_cache.update(cache)
        self.tmp.cleanup()

    def test_free_checks_then_the_whole_transaction(self):
        h = self.h
        res = h.check(self.in_force, "in-force")
        self.assertTrue(res["ok"] and res["sorries"], res["errors"][:2])
        # the restated step: the bridge cannot weaken a hypothesis, the old script proves the new statement
        cand, recert = h._recertify_pieces(self.proposal, self.in_force, ["erdos_97_hyp_step"], 1)
        self.assertEqual(recert, ["erdos_97_hyp_step"])
        self.assertEqual(next(e[2] for e in h.log.events if e[1] == "pieces_recertified")["pieces"],
                         {"erdos_97_hyp_step": "restate"})
        # Lean derives the weakening from the sharp premise, and not the converse
        self.assertEqual(h._weakening_implied(cand, self.in_force, _real(SHARP), _real(LOOSE), None, 1), (True, False))
        # the weakened premise falls to the Mathlib theorem the proposal names, auto-imported
        sub = H.hypothesis_substatement(cand, "erdos_97_hyp_loose")
        body = h._free_close(sub, "Nat.exists_prime_lt_and_le_two_mul", "free")
        self.assertIsNotNone(body)
        self.assertIn("-- IMPORTS: Mathlib.NumberTheory.Bertrand", body)
        # the transaction end to end: a canned proposal, no model call, no child
        h.ask = lambda purpose, prompt, **kw: (plan_reply(self.proposal, json.loads(json.dumps(W_JSON).replace(
            "erdos_99", "erdos_97").replace('"mathlib": null', '"mathlib": "Nat.exists_prime_lt_and_le_two_mul"')))
            if purpose == "weaken" else JUDGE_OK)

        def no_child(*a, **k):
            raise AssertionError("the weakened premise should fall without a child")
        h._attack_substatement = no_child
        pdir = self.root / "programs" / "erdos_97"
        pdir.mkdir(parents=True)
        (pdir / "Residual.lean").write_text(self.in_force)
        h.stage_verify = lambda: h.state.__setitem__("verify", {"all_clear": True})
        rc = h.run_program()
        self.assertEqual(rc, 0, [e for e in h.log.events if e[1] in ("premise_weaken_rejected", "weakening_not_adopted")])
        final = (pdir / "Residual.lean").read_text()
        fin = h.check(final, "final")
        self.assertTrue(fin["ok"], fin["errors"][:2])
        self.assertFalse(fin["sorries"])
        self.assertNotIn("hyp_sharp", final)


if __name__ == "__main__":
    unittest.main()
