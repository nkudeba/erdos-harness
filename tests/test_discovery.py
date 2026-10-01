"""In-run informal discovery (`--discover on`), cross-fed rounds, the ladder of easier variants, blueprint mode and
the residual outline. No provider calls: every model call goes through a scripted fake `call`."""
import argparse, json, re, sys, tempfile, threading, unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "benchmarks" / "timesplit"))
sys.path.insert(0, str(Path(__file__).resolve().parent))
import harness as H
from test_deductive_mode import FROZEN, Log, _stub

LEAN = "theorem erdos_99 : ∀ n : ℕ, n = n := by\n  sorry"

# A complete proof whose OPENING lemma is the part the runner's `text[-3500:]` used to cut away.
PROOF_HEAD = "LEMMA ZERO (the exact formula): every interval's lcm equals prod(I)/R(I)."
LONG_PROOF = PROOF_HEAD + "\n" + ("Detailed computation line. " * 200) + "\nTherefore the statement holds."


def answer(ans="true", conf=0.9, complete=True, steps=("step one", "step two"), gap=None, body=""):
    return (body or f"Proof sketch for {ans}.") + "\n```json\n" + json.dumps(
        {"answer": ans, "confidence": conf, "complete": complete, "key_steps": list(steps), "gap": gap}) + "\n```"


def referee(valid=True, first_error=None):
    return "Checked.\n```json\n" + json.dumps({"valid": valid, "first_error": first_error, "fixable": True}) + "\n```"


class FakeCall:
    """Scripted `call(purpose, prompt, effort, budget) -> (text, cost)`; `script(purpose, prompt, n)` answers."""

    def __init__(self, script, cost=0.1):
        self.script, self.cost, self.calls, self.lock = script, cost, [], threading.Lock()

    def __call__(self, purpose, prompt, effort, budget):
        with self.lock:
            n = sum(1 for p, _ in self.calls if p == purpose)
            self.calls.append((purpose, prompt))
        out = self.script(purpose, prompt, n)
        if isinstance(out, Exception):
            raise out
        return out, self.cost

    def prompts(self, purpose):
        return [p for q, p in self.calls if q == purpose]


class RunnerPromptsAreVerbatim(unittest.TestCase):
    """`mode="independent"` with v3's settings must ask exactly what discover-v3 asked."""

    def test_prompts_match_the_runner(self):
        import timesplit as T
        self.assertEqual(H.DISCOVER_FRAMES, T.DISCOVER_FRAMES)
        self.assertEqual(H.DISCOVER_PROMPT, T.DISCOVER_PROMPT)
        self.assertEqual(H.DISCOVER_CRITIC_PROMPT, T.CRITIC_PROMPT)
        self.assertEqual(H.DISCOVER_GAP_PROMPT, T.GAP_PROMPT)

    def test_direction_rule_matches_the_runner(self):
        import timesplit as T
        cases = [
            [{"answer": "true", "confidence": 0.9, "complete": True, "critic": {"valid": True}},
             {"answer": "true", "confidence": 0.5}],
            [{"answer": "true", "confidence": 0.55}, {"answer": "true", "confidence": 0.5}],
            [{"answer": "true", "confidence": 0.9}, {"answer": "false", "confidence": 0.9}],
            [{"answer": "false", "confidence": 0.8}, {"error": "over cap"}],
            [{"answer": "false", "confidence": 0.4, "complete": True, "critic": {"valid": False, "fixable": True}}],
        ]
        for atts in cases:
            for sc, fl in ((None, None), (0.75, None), (0.75, 0.6)):
                a, b = H.decide_direction(atts, sc, fl), T.decide_direction(atts, sc, fl)
                self.assertEqual({k: v for k, v in a.items() if k != "best"}, {k: v for k, v in b.items() if k != "best"})

    def test_v3_settings_are_the_defaults(self):
        import timesplit as T
        s = H.DiscoverySettings()
        v3 = T.DISCOVER_V3
        self.assertEqual((s.attempts, s.effort, s.budget, s.critic_budget, s.gap_budget, s.gap_effort, s.commit_floor),
                         (v3["discover_attempts"], v3["discover_effort"], v3["discover_budget"], v3["critic_budget"],
                          v3["gap_budget"], v3["gap_effort"], v3["commit_floor"]))


class IndependentMode(unittest.TestCase):
    def test_the_best_proof_reaches_the_guidance_whole(self):
        def script(purpose, prompt, n):
            if purpose == "discover":
                return answer(body=LONG_PROOF) if "explicit construction" in prompt else answer(conf=0.7, complete=False, gap="g")
            if purpose == "discover-critic":
                return referee(True)
            raise AssertionError(purpose)
        call = FakeCall(script)
        res = H.discovery_run(call, "Is it true?", LEAN, H.DiscoverySettings())
        self.assertEqual(res["decision"]["commit"], "pos")
        self.assertTrue(res["refereed_complete"])
        self.assertIn(PROOF_HEAD, res["guidance"])                 # the runner's text[-3500:] cut exactly this
        self.assertIn("Therefore the statement holds.", res["guidance"])
        self.assertTrue(res["best_proof"]["text"].startswith(LONG_PROOF))   # the whole response, JSON included
        self.assertEqual(len(call.prompts("discover")), 2)
        self.assertNotIn("WARM-UP", call.prompts("discover")[0])  # no ladder: the runner's prompt, untouched
        self.assertEqual(call.prompts("discover")[0], H.DISCOVER_PROMPT.format(statement="Is it true?", lean=LEAN,
                                                                           frame=H.DISCOVER_FRAMES[0]))
        self.assertAlmostEqual(res["spend"], 0.3, places=6)        # two attempts and one referee

    def test_a_failed_attempt_is_recorded_and_paid_for(self):
        def script(purpose, prompt, n):
            if purpose == "discover" and "structural argument" in prompt:
                return H.DiscoveryCallFailed("over cap", cost=0.8)
            return answer(conf=0.8, complete=False)
        res = H.discovery_run(FakeCall(script), "Q", LEAN, H.DiscoverySettings(gap_round=False))
        errs = [a for a in res["attempts"] if a.get("error")]
        self.assertEqual(len(errs), 1)
        self.assertEqual(errs[0]["cost"], 0.8)
        self.assertEqual(res["decision"]["commit"], "pos")         # one confident answer may commit (v2's rule)

    def test_a_usage_limit_propagates(self):
        def script(purpose, prompt, n):
            return RuntimeError("usage limit reached")
        with self.assertRaises(RuntimeError):
            H.discovery_run(FakeCall(script), "Q", LEAN, H.DiscoverySettings())

    def test_v4_rounds_stop_at_the_first_refereed_proof_and_at_the_cap(self):
        def script(purpose, prompt, n):
            if purpose == "discover":
                return answer(complete=n >= 2) if True else None    # the 3rd and 4th attempts are complete
            return referee(True)
        call = FakeCall(script)
        res = H.discovery_run(call, "Q", LEAN, H.DiscoverySettings(rounds=3, total_budget=10.0, gap_round=False))
        self.assertEqual(res["rounds"], 2)
        call = FakeCall(lambda p, q, n: answer(complete=False), cost=1.0)
        res = H.discovery_run(call, "Q", LEAN, H.DiscoverySettings(rounds=3, total_budget=3.0, gap_round=False))
        self.assertEqual(res["rounds"], 1)                          # a second round would pass the $3 cap


class CrossFed(unittest.TestCase):
    def test_a_synthesis_seeds_the_next_round_with_assignments(self):
        synthesis = ("=== DIRECTION\nTrue.\n=== ESTABLISHED\nA1 proved the base case.\n=== ROUTE\n1. base [established]\n"
                     "2. induction [open]\n=== GAPS\nG1: the induction step.\n=== DEAD ENDS\nA2's averaging fails.\n"
                     "=== ASSIGNMENTS\n1. Close G1 by strong induction on n.\n2. Try a generating-function route.\n")

        def script(purpose, prompt, n):
            if purpose == "discover-synthesis":
                return synthesis
            if purpose == "discover":
                return answer(complete="Close G1" in prompt, conf=0.8)
            return referee(True)
        call = FakeCall(script)
        res = H.discovery_run(call, "Q", LEAN, H.DiscoverySettings(mode="crossfed", rounds=2, total_budget=10.0))
        self.assertEqual(len(call.prompts("discover-synthesis")), 1)
        syn_prompt = call.prompts("discover-synthesis")[0]
        self.assertIn("[A1] round 1", syn_prompt)
        self.assertIn("Exactly 2 numbered lines", syn_prompt)
        r2 = call.prompts("discover")[2:]
        self.assertEqual(len(r2), 2)
        self.assertTrue(all("CONSOLIDATED FINDINGS" in p and "A2's averaging fails" in p for p in r2))
        self.assertIn("APPROACH FOR THIS ATTEMPT: Close G1 by strong induction on n.", r2[0] + r2[1])
        self.assertTrue(res["refereed_complete"])
        self.assertEqual(res["syntheses"][0]["assignments"][1], "Try a generating-function route.")

    def test_no_synthesis_once_a_refereed_proof_exists(self):
        call = FakeCall(lambda p, q, n: referee(True) if p == "discover-critic" else answer())
        H.discovery_run(call, "Q", LEAN, H.DiscoverySettings(mode="crossfed", rounds=3, total_budget=10.0))
        self.assertEqual(call.prompts("discover-synthesis"), [])


class Ladder(unittest.TestCase):
    def test_rungs_are_solved_bottom_up_and_seed_the_main_attempts(self):
        variants = ("=== VARIANT 1\nSTATEMENT: the case k = 1.\nTEACHES: the double count.\n"
                    "=== VARIANT 2\nSTATEMENT: the case k = 2.\nTEACHES: the second moment.\n")

        def script(purpose, prompt, n):
            if purpose == "discover-ladder":
                return variants
            if purpose == "discover-rung":
                return ("Solved.\n```json\n" + json.dumps({"answer": "true", "confidence": 0.9, "complete": True,
                                                           "key_steps": ["count pairs"], "method": f"double count {n}",
                                                           "transfer": "use it for all k"}) + "\n```")
            if purpose == "discover":
                return answer(complete=False)
            return referee(True)
        call = FakeCall(script)
        res = H.discovery_run(call, "Q", LEAN, H.DiscoverySettings(ladder=2, total_budget=10.0, gap_round=False))
        rungs = call.prompts("discover-rung")
        self.assertEqual(len(rungs), 2)
        self.assertNotIn("ALREADY SOLVED", rungs[0])
        self.assertIn("double count 0", rungs[1])                  # rung 2 sees rung 1's method
        self.assertTrue(all("WARM-UP RESULTS" in p and "the case k = 2." in p for p in call.prompts("discover")))
        self.assertIn("WARM-UP RESULTS", res["guidance"])
        self.assertEqual(sum(1 for r in res["ladder"] if r.get("rung")), 2)

    def test_the_ladder_respects_the_discovery_cap(self):
        call = FakeCall(lambda p, q, n: answer(complete=False), cost=0.2)
        res = H.discovery_run(call, "Q", LEAN, H.DiscoverySettings(ladder=3, total_budget=0.1, gap_round=False))
        self.assertEqual(call.prompts("discover-ladder"), [])
        self.assertEqual(res["ladder"], [])


class BlueprintParsing(unittest.TestCase):
    TEXT = ("=== STEP S1: the exact formula\nKIND: lemma\nSTATEMENT: lcm(I) = prod(I)/R(I) for every interval I.\n"
            "USES: none\nPROOF: Count multiples of p^j, with $\\frac{a}{b}$ LaTeX that JSON would choke on.\n"
            "=== STEP S2: a prime in a window\nKIND: published\nSTATEMENT: for x >= 25 there is a prime in (x, 6x/5].\n"
            "USES: none\nPROOF: Nagura 1952.\n"
            "=== STEP S3: conclusion\nKIND: glue\nSTATEMENT: the theorem.\nUSES: S1, S2\nPROOF: combine.\n")

    def test_steps_and_rendering(self):
        steps = H.parse_blueprint(self.TEXT)
        self.assertEqual([s["id"] for s in steps], ["S1", "S2", "S3"])
        self.assertEqual(steps[1]["kind"], "published")
        self.assertEqual(steps[2]["uses"], ["S1", "S2"])
        self.assertIn("\\frac{a}{b}", steps[0]["proof"])
        one = H.blueprint_text(steps, ["S3"])
        self.assertIn("[S3] conclusion", one)
        self.assertIn("Statements it may use", one)
        self.assertIn("[S1] lcm(I)", one)
        self.assertNotIn("Count multiples", one)                   # only the USED steps' statements, not their proofs

    def test_expanded_ids_keep_their_parent(self):
        steps = H.parse_blueprint("=== STEP S4.1: half\nKIND: lemma\nSTATEMENT: a.\nUSES: none\nPROOF: b.\n"
                                  "=== STEP S4.2: glue\nKIND: glue\nSTATEMENT: c.\nUSES: S4.1\nPROOF: d.\n")
        self.assertEqual([s["id"] for s in steps], ["S4.1", "S4.2"])
        self.assertEqual(steps[1]["uses"], ["S4.1"])


SPLICED = """def foo (n : ℕ) : Prop := n = n

namespace erdos_99_hyp_a_ns
def foo (n : ℕ) : Prop := n = n
theorem erdos_99_hyp_a : ∀ n : ℕ, foo n := by
  intro n
  rfl
end erdos_99_hyp_a_ns

theorem erdos_99_hyp_a : ∀ n : ℕ, foo n := by
  exact erdos_99_hyp_a_ns.erdos_99_hyp_a

theorem erdos_99_hyp_b : ∀ n : ℕ, n + 0 = n := by
  sorry

theorem erdos_99 : ∀ n : ℕ, foo n := by
  intro n
  exact erdos_99_hyp_a n"""


class ResidualOutline(unittest.TestCase):
    def test_certified_proofs_are_elided_and_restored(self):
        out = H.residual_outline(SPLICED)
        self.assertNotIn("namespace erdos_99_hyp_a_ns", out)
        self.assertIn("erdos_99_hyp_a is certified in Lean", out)
        self.assertIn("exact erdos_99_hyp_a_ns.erdos_99_hyp_a", out)
        self.assertIn("theorem erdos_99_hyp_b", out)
        self.assertIn("def foo", out)
        back = H.restore_spliced(out, SPLICED)              # a plan returning the outline unchanged loses nothing
        self.assertIn("namespace erdos_99_hyp_a_ns", back)

    def test_view_is_the_old_tail_by_default(self):
        h = _stub(tempfile.mkdtemp())
        self.assertEqual(h._residual_view("x" * 9000), "x" * 6000)
        h.args.residual_view = "outline"
        long = SPLICED + "\n" + "-- filler\n" * 3000
        view = h._residual_view(long)
        self.assertIn("def foo", view)                       # the head survives
        self.assertIn("characters omitted", view)


class HarnessStage(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        p = patch.object(H, "ROOT", self.root)
        p.start()
        self.addCleanup(p.stop)
        self.h = _stub(self.tmp.name)
        self.h.args.discover = "on"
        self.h.save = lambda: None

    def script(self, purpose, prompt, n):
        if purpose == "discover":
            return answer(body=LONG_PROOF)
        return referee(True)

    def test_stage_discover_runs_once_and_writes_its_record(self):
        call = FakeCall(self.script)
        self.h._discovery_caller = lambda: call
        out = self.h.stage_discover()
        self.assertEqual(out["decision"]["commit"], "pos")
        rec = json.loads((self.root / "discovery.json").read_text())
        self.assertEqual(len(rec["attempts"]), 2)
        self.assertTrue(all("key_steps" in a for a in rec["attempts"]))   # what the idea judge reads
        n = len(call.calls)
        self.h.stage_discover()
        self.assertEqual(len(call.calls), n)                              # resumed: not run again

    def test_off_by_default(self):
        self.h.args.discover = "off"
        self.h._discovery_caller = lambda: self.fail("no call expected")
        self.assertIsNone(self.h.stage_discover())

    def test_guidance_reaches_research_stages_but_not_judges(self):
        self.h.state["discovery"] = {"guidance": "THE ROUTE: count multiples."}
        for purpose in ("plan", "prove", "prove-agentic", "experiments"):
            self.assertIn("THE ROUTE: count multiples.", self.h._with_research_guidance(purpose, "p"))
        for purpose in ("formalize", "faithful", "backtranslate", "circularity", "discover", "discover-critic"):
            self.assertNotIn("count multiples", self.h._with_research_guidance(purpose, "p"))

    def test_operator_guidance_reaches_discovery_but_not_its_referee(self):
        g = self.root / "atlas-data" / "research-guidance" / "99.md"
        g.parent.mkdir(parents=True)
        g.write_text("Try the forced construction first.")
        self.assertIn("forced construction", self.h._with_research_guidance("discover", "p"))
        self.assertIn("forced construction", self.h._with_research_guidance("discover-rung", "p"))
        self.assertNotIn("forced construction", self.h._with_research_guidance("discover-critic", "p"))

    def test_stop_after_discover(self):
        self.h.args.stop_after = "discover"
        self.h.args.discover = "off"                     # --stop-after discover implies it
        self.h.args.backend, self.h.args.resume, self.h.args.open = "claude-cli", None, False
        self.h.stage_literature = lambda: None
        self.h.stage_informal_context = lambda: None
        self.h._discovery_caller = lambda: FakeCall(self.script)
        self.assertEqual(self.h.run(), 3)
        self.assertEqual(json.loads((self.root / "DONE").read_text())["outcome"], "discovered")

    def test_one_committed_direction_gets_the_whole_remainder(self):
        child = _stub(self.tmp.name)
        child.args = argparse.Namespace(run_budget=None)
        child.spent_usd = lambda: 1.0
        self.h.spent_usd = lambda: 2.0
        self.h._fund_direction(child, 10.0, n=1)
        self.assertEqual(child.args.run_budget, 9.0)
        self.h._fund_direction(child, 10.0)
        self.assertEqual(child.args.run_budget, 5.0)

    def test_run_open_commits_and_children_never_rerun_discovery(self):
        import inspect
        src = inspect.getsource(H.Harness.run_open)
        self.assertIn("disc = self.stage_discover() or {}", src)
        self.assertIn("if direction not in directions:", src)
        self.assertIn('cargs.discover = "off"', src)
        self.assertIn('cargs.discover = "off"', inspect.getsource(H.Harness._attack_substatement))


class BlueprintMode(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        p = patch.object(H, "ROOT", self.root)
        p.start()
        self.addCleanup(p.stop)
        self.h = _stub(self.tmp.name)
        self.h.args.blueprint = "on"
        self.h.thm_name = "erdos_99"
        self.pdir = self.root / "programs" / "erdos_99"
        self.pdir.mkdir(parents=True)

    def test_a_proof_for_this_direction_becomes_steps(self):
        self.h.state["discovery"] = {"best_proof": {"answer": "true", "text": LONG_PROOF}}
        call = FakeCall(lambda p, q, n: BlueprintParsing.TEXT)
        self.h._discovery_caller = lambda: call
        self.h._maybe_blueprint(self.pdir)
        self.assertEqual([s["id"] for s in self.h.state["blueprint"]["steps"]], ["S1", "S2", "S3"])
        self.assertIn(PROOF_HEAD, call.prompts("blueprint")[0])
        self.assertTrue((self.pdir / "BLUEPRINT.md").exists())
        block = self.h._blueprint_block()
        self.assertIn('"blueprint_steps"', block)
        self.assertIn("[S2] a prime in a window", block)

    def test_a_proof_of_the_other_direction_is_not_used(self):
        self.h.state["discovery"] = {"best_proof": {"answer": "false", "text": "counterexample"}}
        self.h._discovery_caller = lambda: self.fail("no call expected")
        self.h._maybe_blueprint(self.pdir)
        self.assertEqual(self.h.state["blueprint"]["steps"], [])

    def test_a_sub_residual_expands_its_own_step(self):
        self.h.state["blueprint_step"] = {"name": "erdos_99_hyp_a", "ids": ["S4"], "text": "[S4] the hard bound",
                                          "why": "it failed a direct attack"}
        call = FakeCall(lambda p, q, n: "=== STEP S4.1: half\nKIND: lemma\nSTATEMENT: a.\nUSES: none\nPROOF: b.\n")
        self.h._discovery_caller = lambda: call
        self.h._maybe_blueprint(self.pdir)
        self.assertEqual(self.h.state["blueprint"]["source"], "step")
        self.assertIn("it failed a direct attack", call.prompts("blueprint-expand")[0])
        self.assertIn("=== STEP S4.1", call.prompts("blueprint-expand")[0])

    def test_each_hypothesis_gets_its_step(self):
        self.h.state["blueprint"] = {"steps": H.parse_blueprint(BlueprintParsing.TEXT), "source": "proof"}
        self.h._plan_meta = {"hypotheses": [{"name": "erdos_99_hyp_a", "blueprint_steps": ["s1"]},
                                            {"name": "erdos_99_hyp_b", "blueprint_steps": ["S9"]}]}
        text, ids = self.h._blueprint_for_name("erdos_99_hyp_a")
        self.assertEqual(ids, ["S1"])
        self.assertIn("lcm(I) = prod(I)/R(I)", text)
        self.assertEqual(self.h._blueprint_for_name("erdos_99_hyp_b"), ("", []))    # an unknown step id maps nowhere
        self.h.args.blueprint = "off"
        self.assertEqual(self.h._blueprint_for_name("erdos_99_hyp_a"), ("", []))

    def test_the_child_state_carries_its_step_and_the_guidance(self):
        self.h.state["blueprint"] = {"steps": H.parse_blueprint(BlueprintParsing.TEXT), "source": "proof"}
        self.h.state["discovery"] = {"guidance": "G", "decision": {"commit": "pos"}, "best_proof": {"text": "P"}}
        self.h._plan_meta = {"hypotheses": [{"name": "erdos_99_hyp_a", "blueprint_steps": ["S1"]}]}
        self.h.args.run_budget = None
        self.h.args.rounds, self.h.args.decompose_rounds = 6, 10
        seen = {}

        class Child:
            def __init__(self, cargs):
                seen["args"] = cargs
                self.state = json.loads((Path(cargs.resume) / "state.json").read_text())
            def run(self):
                return 2
        sdir = self.root / "c1" / "hyp-0"
        orig = H.Harness
        with patch.object(H, "Harness", Child):
            rc, child = orig._attack_substatement(self.h, "theorem erdos_99_hyp_a : True := by\n  sorry",
                                                  "erdos_99_hyp_a", sdir, 1, None, 1)
        self.assertEqual(rc, 2)
        self.assertEqual(seen["args"].discover, "off")
        self.assertTrue(child.state["literature"].startswith(H.BLUEPRINT_CHILD_HEADER))
        self.assertIn("lcm(I) = prod(I)/R(I)", child.state["literature"])
        self.assertEqual(child.state["discovery"], {"decision": {"commit": "pos"}, "guidance": "G"})
        self.assertEqual(child.state["blueprint_step"]["ids"], ["S1"])


class Flags(unittest.TestCase):
    def test_everything_new_is_off_by_default(self):
        a = H.build_parser().parse_args(["run", "--problem", "x"])
        self.assertEqual((a.discover, a.blueprint, a.residual_view, a.library, a.discover_mode, a.discover_ladder),
                         ("off", "off", "tail", None, "independent", 0))
        b = H.build_parser().parse_args(["run", "--problem", "x", "--stop-after", "discover"])
        self.assertEqual(b.stop_after, "discover")


if __name__ == "__main__":
    unittest.main()


class RunnerCandidates(unittest.TestCase):
    """benchmarks/timesplit/timesplit.py: the in-run candidates launch the harness with its own discovery, and a
    library's cutoff sits strictly before the resolution with the problem's identity excluded."""

    def test_in_run_candidates_pass_their_flags(self):
        import timesplit as T
        for cand, must in (("discover-v5", ["--discover", "on"]),
                           ("blueprint", ["--blueprint", "on", "--residual-view", "outline"]),
                           ("crossfed", ["--discover-mode", "crossfed", "--discover-ladder", "3"])):
            flags = T.candidate_flags(argparse.Namespace(candidate=cand))
            for m in must:
                self.assertIn(m, flags)
            H.build_parser().parse_args(["run", "--problem", "x", *flags])        # every flag exists in the harness
        self.assertEqual(T.candidate_flags(argparse.Namespace(candidate="discover-v3")), [])

    def test_library_spec(self):
        import timesplit as T
        spec = T.library_spec({"problem": "152", "first_public": "2026-04-03"})
        self.assertEqual(spec["cutoff"], "2026-03-27")
        self.assertTrue(any(re.search(p, "erdosproblems.com/forum/thread/152", re.I) for p in spec["exclude"]))
        self.assertTrue(any(re.search(p, "This is Erdős Problem #152.", re.I) for p in spec["exclude"]))
        self.assertFalse(any(re.search(p, "Erdős Problem #1520", re.I) for p in spec["exclude"]))
