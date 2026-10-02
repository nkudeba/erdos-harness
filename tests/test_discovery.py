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

    def test_a_library_reaches_every_discovery_prompt(self):
        # regression (2026-10-01): stage_discover logged `stage="discover"`, a second value for RunLog.event's own
        # first argument, so every --library run crashed before its first call
        lib = self.root / "lib"
        lib.mkdir()
        (lib / "DIGEST.md").write_text("## Sumsets of Sidon sets (1996)\nThe energy identity E = 2n^2 - n.")
        self.h.args.library = str(lib)
        call = FakeCall(self.script)
        self.h._discovery_caller = lambda: call
        self.h.stage_discover()
        self.assertTrue(all("LITERATURE LIBRARY" in p and "energy identity" in p for p in call.prompts("discover")))
        self.assertTrue(any(e[:2] == ("library", "used") for e in self.h.log.events))

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

    def test_a_merged_hypothesis_is_decomposed_at_once(self):
        self.h.state["blueprint"] = {"steps": H.parse_blueprint(BlueprintParsing.TEXT), "source": "proof"}
        self.h._plan_meta = {"hypotheses": [{"name": "erdos_99_hyp_all", "blueprint_steps": ["S1", "S2", "S3"]},
                                            {"name": "erdos_99_hyp_two", "blueprint_steps": ["S1", "S2"]}]}
        self.assertTrue(self.h._blueprint_merged("erdos_99_hyp_all"))
        self.assertFalse(self.h._blueprint_merged("erdos_99_hyp_two"))
        self.h.args.blueprint = "off"
        self.assertFalse(self.h._blueprint_merged("erdos_99_hyp_all"))
        import inspect
        self.assertIn("self._blueprint_merged(h[\"name\"])", inspect.getsource(H.Harness._run_program_deductive))

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


class Draws(unittest.TestCase):
    """--discover-draws: independent draws (ladder shared) until a refereed complete proof appears."""

    def test_a_second_draw_runs_only_while_no_refereed_proof_exists(self):
        def script(purpose, prompt, n):
            if purpose == "discover":
                return answer(complete=n >= 2)          # draw 1's two attempts incomplete, draw 2's complete
            return referee(True)
        call = FakeCall(script)
        res = H.discovery_run(call, "Q", LEAN, H.DiscoverySettings(draws=3, total_budget=10.0, gap_round=False))
        self.assertEqual(res["draws"], 2)
        self.assertEqual(sorted({a["draw"] for a in res["attempts"]}), [1, 2])
        self.assertTrue(res["refereed_complete"])
        self.assertEqual(len(call.prompts("discover")), 4)

    def test_the_cap_stops_draws_and_one_draw_is_the_old_behaviour(self):
        call = FakeCall(lambda p, q, n: answer(complete=False), cost=1.0)
        res = H.discovery_run(call, "Q", LEAN, H.DiscoverySettings(draws=3, total_budget=3.0, gap_round=False))
        self.assertEqual(res["draws"], 1)                 # a second draw would cost ~$2 more than the $3 cap allows
        call = FakeCall(lambda p, q, n: answer(complete=False))
        res = H.discovery_run(call, "Q", LEAN, H.DiscoverySettings(gap_round=False))
        self.assertEqual((res["draws"], len(res["attempts"])), (1, 2))

    def test_the_ladder_is_shared_across_draws(self):
        variants = "=== VARIANT 1\nSTATEMENT: the case k = 1.\nTEACHES: counting.\n"

        def script(purpose, prompt, n):
            if purpose == "discover-ladder":
                return variants
            if purpose == "discover-rung":
                return "ok\n```json\n" + json.dumps({"answer": "true", "complete": True, "method": "count"}) + "\n```"
            return answer(complete=False)
        call = FakeCall(script)
        H.discovery_run(call, "Q", LEAN, H.DiscoverySettings(draws=2, ladder=1, total_budget=20.0, gap_round=False))
        self.assertEqual(len(call.prompts("discover-ladder")), 1)
        self.assertEqual(len(call.prompts("discover-rung")), 1)
        self.assertEqual(len(call.prompts("discover")), 4)


class Blackboard(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        p = patch.object(H, "ROOT", self.root)
        p.start()
        self.addCleanup(p.stop)
        self.h = _stub(self.tmp.name)
        self.h.args.blackboard = "on"

    def test_append_and_read_keep_the_newest_whole_entries(self):
        for i in range(30):
            self.h._blackboard_append(f"entry {i}", [f"- fact {i} " + "x" * 300])
        text = self.h._read_blackboard(2000)
        self.assertIn("entry 29", text)
        self.assertNotIn("entry 0 ", text)
        self.assertIn("earlier entries omitted", text)
        self.assertTrue(text.startswith("# Campaign blackboard: problem 99"))
        self.h.args.blackboard = "off"
        self.assertEqual(self.h._read_blackboard(), "")

    def test_discovery_reads_it_and_writes_back(self):
        self.h._blackboard_append("Lean residual, direction pos", ["- [Lean] erdos_99_hyp_a: base case holds"])
        self.h.args.discover = "on"
        call = FakeCall(lambda p, q, n: referee(True) if p == "discover-critic" else answer(body=LONG_PROOF))
        self.h._discovery_caller = lambda: call
        self.h.save = lambda: None
        self.h.stage_discover()
        self.assertTrue(all("CAMPAIGN BLACKBOARD" in p and "base case holds" in p for p in call.prompts("discover")))
        board = (self.root / "programs" / "erdos_99" / "BLACKBOARD.md").read_text()
        self.assertIn("discovery decided TRUE", board)
        self.assertIn("refereed complete proof: yes", board)

    def test_the_program_writes_its_lean_facts(self):
        parsed = H.parse_residual(SPLICED, 99)
        pdir = self.root / "programs" / "erdos_99"
        pdir.mkdir(parents=True, exist_ok=True)
        self.h._blackboard_program(pdir, parsed, [])
        board = (pdir / "BLACKBOARD.md").read_text()
        self.assertIn("[Lean] the frozen target follows", board)
        self.assertIn("[Lean] erdos_99_hyp_a", board)
        self.assertIn("open conjecture", board)

    def test_facts_certified_in_a_sub_residual_reach_the_board(self):
        """#455: the gap bound was certified inside the attack on the core, under a refinement the parent refused,
        and the board's Lean entry left it out. A direction child's entry also read 'run pos'."""
        pdir = self.root / "programs" / "erdos_99"
        sub = pdir / "sub" / "erdos_99_hyp_b"
        sub.mkdir(parents=True)
        (sub / "Residual.lean").write_text(
            "def Chain (n : ℕ) : Prop := n = n\n\n"
            "namespace erdos_99_hyp_b_hyp_c_ns\ndef Chain (n : ℕ) : Prop := n = n\n"
            "theorem erdos_99_hyp_b_hyp_c : ∀ n : ℕ, Chain n := by\n  intro n\n  rfl\nend erdos_99_hyp_b_hyp_c_ns\n\n"
            "theorem erdos_99_hyp_b_hyp_c : ∀ n : ℕ, Chain n := by\n  exact erdos_99_hyp_b_hyp_c_ns.erdos_99_hyp_b_hyp_c\n\n"
            "theorem erdos_99_hyp_b_hyp_d : ∀ n : ℕ, n + 0 = n := by\n  sorry\n\n"
            "theorem erdos_99_hyp_b : ∀ n : ℕ, n + 0 = n := by\n  exact erdos_99_hyp_b_hyp_d\n")
        self.h.run_dir = self.root / "20261002-000000-000000-erdos99" / "pos"
        self.h._blackboard_program(pdir, H.parse_residual(SPLICED, 99), [])
        board = (pdir / "BLACKBOARD.md").read_text()
        self.assertIn("[Lean] erdos_99_hyp_b_hyp_c (proved while attacking erdos_99_hyp_b)", board)
        self.assertIn("where def Chain (n : ℕ) : Prop := n = n", board)
        self.assertNotIn("[Lean] erdos_99_hyp_b_hyp_d", board)          # still open below
        self.assertIn("run 20261002-000000-000000-erdos99/pos", board)
        self.assertIn("erdos_99_hyp_b_hyp_c", self.h._read_blackboard())


class Reroute(unittest.TestCase):
    STEPS = ("=== STEP S1: setup\nKIND: lemma\nSTATEMENT: a.\nUSES: none\nPROOF: b.\n"
             "=== STEP S2: a prime in a short window\nKIND: published\nSTATEMENT: for x >= 25 a prime lies in (x, 6x/5].\n"
             "USES: none\nPROOF: Nagura 1952.\n"
             "=== STEP S3: glue\nKIND: glue\nSTATEMENT: the theorem.\nUSES: S1, S2\nPROOF: combine.\n")
    NEW = ("=== STEP S1: setup\nKIND: lemma\nSTATEMENT: a.\nUSES: none\nPROOF: b.\n"
           "=== STEP S2: Bertrand\nKIND: published\nSTATEMENT: a prime lies in (n, 2n].\nUSES: none\nPROOF: Chebyshev.\n"
           "=== STEP S3: glue\nKIND: glue\nSTATEMENT: the theorem.\nUSES: S1, S2\nPROOF: combine.\n")

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.h = _stub(self.tmp.name)
        self.pdir = Path(self.tmp.name)

    def test_mathlib_names_are_verified_not_trusted(self):
        steps = H.parse_blueprint(self.STEPS)
        with patch.object(H, "find_decl", lambda n: ("Mathlib.NumberTheory.Bertrand", "sig") if n == "Nat.real" else None):
            missing = H.blueprint_mark_mathlib(steps, {"S2": "Nat.invented_name"})
        self.assertEqual(missing, ["S2"])
        self.assertIn("NOT IN MATHLIB", H.blueprint_text(steps))

    def test_a_refereed_variant_with_fewer_missing_premises_is_adopted(self):
        def script(purpose, prompt, n):
            if purpose == "blueprint-reroute" and n == 0:
                return ('```json\n{"mathlib": {"S2": null}, "variant": true, "avoids": ["S2"]}\n```\n=== VARIANT PROOF\n'
                        + "Use Bertrand's postulate twice instead of Nagura. " * 20)
            if purpose == "blueprint-reroute":
                return '```json\n{"mathlib": {"S2": "Nat.exists_prime_lt_and_le_two_mul"}, "variant": false}\n```'
            if purpose == "discover-critic":
                return referee(True)
            if purpose == "blueprint":
                return self.NEW
            raise AssertionError(purpose)
        self.h._discovery_caller = lambda: FakeCall(script)
        bertrand = lambda n: ("Mathlib.NumberTheory.Bertrand", "theorem ...") if n == "Nat.exists_prime_lt_and_le_two_mul" else None
        with patch.object(H, "find_decl", bertrand):
            steps, rec = self.h._blueprint_reroute(self.pdir, H.parse_blueprint(self.STEPS), "proof", "a proof", "medium", 0.6)
        self.assertTrue(rec["adopted"])
        self.assertEqual((rec["missing_before"], rec["missing_after"]), (["S2"], []))
        self.assertEqual(steps[1]["mathlib"], "Nat.exists_prime_lt_and_le_two_mul")
        self.assertIn("ADOPTED", (self.pdir / "REROUTE.md").read_text())

    def test_an_unrefereed_variant_keeps_the_original(self):
        def script(purpose, prompt, n):
            if purpose == "blueprint-reroute":
                return '```json\n{"mathlib": {"S2": null}, "variant": true}\n```\n=== VARIANT PROOF\n' + "x " * 400
            return referee(False, "step 2 is wrong")
        self.h._discovery_caller = lambda: FakeCall(script)
        with patch.object(H, "find_decl", lambda n: None):
            steps, rec = self.h._blueprint_reroute(self.pdir, H.parse_blueprint(self.STEPS), "proof", "a proof", "medium", 0.6)
        self.assertFalse(rec["variant_refereed"])
        self.assertEqual(steps[1]["title"], "a prime in a short window")
        self.assertTrue(steps[1]["missing"])


class Rediscover(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        p = patch.object(H, "ROOT", self.root)
        p.start()
        self.addCleanup(p.stop)
        self.h = _stub(self.tmp.name)
        self.h.args.rediscover = 1
        self.pdir = self.root / "programs" / "erdos_99"
        self.pdir.mkdir(parents=True)
        self.parsed = H.parse_residual(SPLICED, 99)

    def test_a_refereed_proof_becomes_the_steps_blueprint(self):
        self.h._queue_rediscover("erdos_99_hyp_b")
        H.record_failure(self.pdir, {"name": "erdos_99_hyp_b", "cycle": 1, "stop_reason": "unsolved goals",
                                     "diagnosis": "needs the zero case"})
        call = FakeCall(lambda p, q, n: referee(True) if p == "discover-critic" else answer(body="Induct on n."))
        self.h._discovery_caller = lambda: call
        self.h._maybe_rediscover(self.pdir, 2, self.parsed, SPLICED)
        prompt = call.prompts("discover")[0]
        self.assertIn("[Lean] erdos_99_hyp_a", prompt)             # the machine-checked facts reach the step's discovery
        self.assertIn("needs the zero case", prompt)               # and what broke in Lean
        self.assertIn("theorem erdos_99_hyp_b", prompt)
        text, ids = self.h._blueprint_for_name("erdos_99_hyp_b")
        self.assertEqual(ids, ["R"])
        self.assertIn("Induct on n.", text)
        n = len(call.calls)
        self.h._queue_rediscover("erdos_99_hyp_b")
        self.h._maybe_rediscover(self.pdir, 3, self.parsed, SPLICED)
        self.assertEqual(len(call.calls), n)                       # at most --rediscover N per run

    def test_a_refereed_disproof_is_a_failure_the_plan_must_answer(self):
        self.h._queue_rediscover("erdos_99_hyp_b")
        call = FakeCall(lambda p, q, n: referee(True) if p == "discover-critic" else answer(ans="false", body="n = 3 breaks it"))
        self.h._discovery_caller = lambda: call
        self.h._maybe_rediscover(self.pdir, 2, self.parsed, SPLICED)
        fails = [f for f in H.load_failures(self.pdir) if f.get("kind") == "rediscover"]
        self.assertEqual(len(fails), 1)
        self.assertIn("FALSE", fails[0]["diagnosis"])
        self.assertNotIn("erdos_99_hyp_b", self.h.state.get("step_proofs") or {})

    def test_off_by_default_and_the_hooks_exist(self):
        self.h.args.rediscover = 0
        self.h._queue_rediscover("erdos_99_hyp_b")
        self.assertNotIn("rediscover_queue", self.h.state)
        import inspect
        src = inspect.getsource(H.Harness._run_program_deductive)
        self.assertIn("self._maybe_rediscover(pdir, cycle, parsed, skeleton)", src)
        self.assertIn('h["name"] in (self.state.get("step_proofs") or {})', src)
        self.assertIn("self._blackboard_program(pdir, parsed, load_refutations(pid))", src)


class DiscoverModel(unittest.TestCase):
    def test_route_choosing_calls_may_use_another_model(self):
        h = _stub(tempfile.mkdtemp())
        h.llm = H.ClaudeCliBackend("claude-opus-5-5", 60)
        h.args.discover_model = "claude-other-model"
        self.assertEqual(h._fresh_backend().model, "claude-other-model")
        h.args.discover_model = None
        self.assertEqual(h._fresh_backend().model, "claude-opus-5-5")
