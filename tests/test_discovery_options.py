"""The discovery fixes and options (docs/discovery-limits-2026-09-24.md). No provider calls; Lean is mocked except where
a real Python subprocess is the point (the exploration sandbox's runner)."""
import argparse, json, os, subprocess, sys, tempfile, unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parent))
import harness as H
from test_deductive_mode import SKELETON, FROZEN, Log, _stub, _judged, JUDGE_OK

PLAN_FIELDS = dict(pid="99", statement_en="s", statement="t", literature="l", library="", lemmas="", residual="",
                   experiments="", refuted="", failures="", hyp_prefix="erdos_99_hyp_", ledger="", cycle=1)


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


class HoistDefinitions(unittest.TestCase):
    """Train #997's cycle-2 plan put the frozen block's definition after proofs that use it."""

    SRC = ("def E (n : ℕ) : Prop := n = n\n\n"
           "namespace erdos_9_hyp_a_ns\ntheorem erdos_9_hyp_a : ∀ x : ℕ, W x := by\n  intro x; rfl\nend erdos_9_hyp_a_ns\n\n"
           "theorem erdos_9_hyp_a : ∀ x : ℕ, W x := by\n  exact erdos_9_hyp_a_ns.erdos_9_hyp_a\n\n"
           "open Set\n\ndef W (x : ℕ) : Prop := x = x\n\n"
           "theorem erdos_9 : ∀ x : ℕ, W x := by\n  exact erdos_9_hyp_a")

    def test_a_definition_moves_above_its_first_use_with_its_opens(self):
        out = H.hoist_defs(self.SRC)
        self.assertLess(out.index("def W"), out.index("namespace erdos_9_hyp_a_ns"))
        self.assertLess(out.index("open Set"), out.index("def W"))
        self.assertEqual(sorted(H.split_decls(out)), sorted(H.split_decls(self.SRC)))   # nothing added or lost
        frozen = "open Set\n\ndef W (x : ℕ) : Prop := x = x\n\ntheorem erdos_9 : ∀ x : ℕ, W x :="
        self.assertTrue(H.contains_frozen(out, frozen))

    def test_well_ordered_code_is_untouched(self):
        self.assertEqual(H.hoist_defs(SKELETON), SKELETON)


class SubStatementContext(unittest.TestCase):
    """A hypothesis extracted for a child keeps the top-level `open`s in force (train #152's v3 smoke run lost every
    attack to a dropped `open scoped Pointwise`)."""

    SK = ("open Function Set\nopen scoped Pointwise\n\ndef iso (A : Set ℕ) : Set ℕ := A + A\n\n"
          "open Classical in\nnoncomputable def pick (A : Set ℕ) : ℕ := 0\n\n"
          "theorem erdos_9_hyp_a : ∀ A : Set ℕ, A + A = iso A := by\n  sorry\n\n"
          "theorem erdos_9 : True := by\n  trivial")

    def test_opens_travel_with_the_hypothesis(self):
        sub = H.hypothesis_substatement(self.SK, "erdos_9_hyp_a")
        self.assertIn("open scoped Pointwise", sub)
        self.assertIn("open Function Set", sub)
        self.assertIn("open Classical in\nnoncomputable def pick", sub.replace("\n\n", "\n"))
        self.assertTrue(sub.rstrip().endswith("sorry"))


class PlanContext(Isolated):
    def test_experiments_digest_keeps_findings_printed_early(self):
        out = "OBSERVED: family A grows like 0.3 p^2\n" + ("EXP: noise line\n" * 400) + "CLEAR: {\"hypothesis\": \"h\"}\n"
        d = H.experiments_digest(out, 4000)
        self.assertIn("OBSERVED: family A grows like 0.3 p^2", d)      # the old tail cut this
        self.assertLessEqual(len(d), 4100)
        self.assertEqual(H.experiments_digest("short", 4000), "short")

    def test_plan_notes_put_human_direction_first(self):
        p = self.root / "p"
        p.mkdir()
        (p / "PLAN.md").write_text("\n\n## Cycle 1 (t)\n\nold idea\n\nRoute: via runs\n\n## HUMAN DIRECTION (t)\ntry the dual\n"
                                   "\n\n## Cycle 2 (t)\n\nnewer idea\n")
        ctx = H.plan_notes_context(p)
        self.assertTrue(ctx.startswith("HUMAN DIRECTION"))
        self.assertIn("try the dual", ctx)
        self.assertIn("Route: via runs", ctx)
        self.assertIn("newer idea", ctx)

    def test_a_refused_route_is_recorded_and_shown_to_the_next_plan(self):
        h = _stub(self.root / "run")
        pdir = self.pdir()
        pdir.mkdir(parents=True)
        cur = H.parse_residual(SKELETON, 99, main="erdos_99")
        h._record_plan_rejection(pdir, pdir, 2, {"reason": "no improvement over the skeleton in force", "parsed": cur},
                                 SKELETON, {"route": "the same route again"}, cur)
        self.assertFalse((pdir / "failures.jsonl").exists())           # a refusal is not the planner's failure
        extras = h._plan_extras(pdir, stalled=False)
        self.assertIn("ROUTES NOT ADOPTED", extras)
        self.assertIn("the same route again", extras)

    def test_failure_digest_carries_what_the_attempt_tried(self):
        state = {"attempts": [{"name": "a1", "plan": "induction on n with a potential function", "compiled": True,
                               "errors": ["unsolved goals\n⊢ foo n"]}]}
        d = H.failure_digest(state, "erdos_99_hyp_a", "∀ n, foo n", 1, 3)
        p = self.root / "p"
        p.mkdir()
        H.record_failure(p, d)
        self.assertIn("tried: induction on n with a potential function", H.failures_context(p))


class PlanRepair(Isolated):
    def test_a_plan_that_does_not_compile_gets_one_repair_round(self):
        h = _stub(self.root / "run")
        broken = SKELETON.replace("def foo (n : ℕ) : Prop := n = n", "def foo (n : ℕ) : Prop := n = BROKEN")
        seen = []

        def ask(purpose, prompt, **kw):
            seen.append(purpose)
            return plan_reply(broken if purpose == "plan" else SKELETON)
        h.ask = _judged(ask)
        base = h.check
        h.check = lambda body, name: ({"ok": False, "sorries": [], "errors": ["line 3:30: Unknown identifier `BROKEN`"],
                                       "infos": [], "body": body} if "BROKEN" in body else base(body, name))
        h._install_lemmas_module = lambda pdir: None
        h._attack_substatement = lambda *a, **k: (3, argparse.Namespace(state={}))
        h.run_program()
        self.assertEqual(seen[:2], ["plan", "plan-repair"])
        self.assertTrue(any(e[1] == "plan_repaired" for e in h.log.events))
        adopted = [e for e in h.log.events if e[1] == "skeleton"][0][2]
        self.assertTrue(adopted["adopted"])
        self.assertEqual(adopted["repaired"], 1)

    def test_repairs_can_be_turned_off(self):
        h = _stub(self.root / "run")
        h.args.plan_repairs = 0
        broken = SKELETON.replace("def foo (n : ℕ) : Prop := n = n", "def foo (n : ℕ) : Prop := n = BROKEN")
        seen = []
        h.ask = _judged(lambda purpose, prompt, **kw: seen.append(purpose) or plan_reply(broken))
        base = h.check
        h.check = lambda body, name: ({"ok": False, "sorries": [], "errors": ["Unknown identifier `BROKEN`"],
                                       "infos": [], "body": body} if "BROKEN" in body else base(body, name))
        h._install_lemmas_module = lambda pdir: None
        h.run_program()
        self.assertNotIn("plan-repair", seen)


ALT = SKELETON.replace("erdos_99_hyp_a", "erdos_99_hyp_alt")


class Routes(Isolated):
    def test_two_routes_the_judge_picks_and_the_other_is_kept(self):
        h = _stub(self.root / "run")
        h.args.routes = 2
        replies = iter([plan_reply(SKELETON, {"route": "route one"}), plan_reply(ALT, {"route": "route two"})])
        prompts = []

        def ask(purpose, prompt, **kw):
            prompts.append((purpose, prompt))
            if purpose == "route-judge":
                return '```json\n{"choice": 2, "why": "the second is more elementary"}\n```'
            return next(replies)
        h.ask = _judged(ask)
        h._install_lemmas_module = lambda pdir: None
        h._attack_substatement = lambda *a, **k: (3, argparse.Namespace(state={}))
        h.run_program()
        plans = [p for purpose, p in prompts if purpose == "plan"]
        self.assertEqual(len(plans), 2)
        self.assertIn("ROUTE FOR THIS PLAN", plans[1])
        self.assertNotIn("ROUTE FOR THIS PLAN", plans[0])
        self.assertIn("erdos_99_hyp_alt", (self.pdir() / "Residual.lean").read_text())
        alts = [json.loads(l) for l in (self.pdir() / "alternatives.jsonl").read_text().splitlines()]
        self.assertEqual(alts[0]["route"], "route one")
        self.assertTrue(any(e[1] == "route_chosen" and e[2]["choice"] == 2 for e in h.log.events))

    def test_after_a_stall_a_route_that_is_not_better_may_switch(self):
        h = _stub(self.root / "run", stall_cycles=1)
        h.args.routes = 2
        pdir = self.pdir()
        pdir.mkdir(parents=True)
        (pdir / "Residual.lean").write_text(SKELETON)
        h.ask = _judged(lambda purpose, prompt, **kw: plan_reply(ALT, {"route": "a new framework"})
                        if purpose == "plan" else '```json\n{"choice": 1}\n```')
        h._install_lemmas_module = lambda pdir: None
        h._attack_substatement = lambda *a, **k: (3, argparse.Namespace(state={}))
        h.run_program()
        self.assertTrue(any(e[1] == "route_switch" for e in h.log.events))
        self.assertIn("erdos_99_hyp_alt", (pdir / "Residual.lean").read_text())

    def test_without_routes_a_stalled_program_keeps_the_old_rule(self):
        h = _stub(self.root / "run", stall_cycles=1)
        pdir = self.pdir()
        pdir.mkdir(parents=True)
        (pdir / "Residual.lean").write_text(SKELETON)
        h.ask = _judged(lambda purpose, prompt, **kw: plan_reply(ALT))
        h._install_lemmas_module = lambda pdir: None
        h._attack_substatement = lambda *a, **k: (3, argparse.Namespace(state={}))
        h.run_program()
        self.assertFalse(any(e[1] == "route_switch" for e in h.log.events))
        self.assertNotIn("erdos_99_hyp_alt", (pdir / "Residual.lean").read_text())
        self.assertTrue((pdir / "refusals.jsonl").exists())


class PromptVariants(unittest.TestCase):
    def _h(self, **flags):
        h = H.Harness.__new__(H.Harness)
        h.args = argparse.Namespace(**flags)
        return h

    def test_every_swap_target_exists(self):
        plan = H.PLAN_PROMPT.format(**PLAN_FIELDS)
        for swaps in H.PLAN_SWAPS.values():
            H.apply_swaps(plan, swaps)
        exp = H.EXPERIMENTS_PROMPT.format(pid="99", statement_en="s", statement="t", literature="l", hypotheses="h", refuted="r")
        for swaps in H.EXPERIMENT_SWAPS.values():
            H.apply_swaps(exp, swaps)

    def test_empirical_and_core_first(self):
        plan = H.PLAN_PROMPT.format(**PLAN_FIELDS)
        self.assertEqual(self._h()._plan_prompt_variant(plan), plan)
        v = self._h(empirical="on", attack_order="core-first")._plan_prompt_variant(plan)
        self.assertIn("EMPIRICAL conjecture", v)
        self.assertIn('"basis": "derived" | "empirical"', v)
        self.assertIn("HARDEST open conjecture first", v)
        self.assertNotIn("leaves hard ones for\n    later cycles", v)

    def test_a_broken_swap_target_fails_loudly(self):
        with self.assertRaises(ValueError):
            H.apply_swaps("some prompt", [("missing text", "x")])

    def test_empirical_basis_is_parsed_and_reported(self):
        meta = {"hypotheses": [{"name": "erdos_99_hyp_a", "kind": "conjecture", "basis": "empirical"}]}
        r = H.parse_residual(SKELETON, 99, meta)
        self.assertEqual({h["name"]: h["basis"] for h in r["hypotheses"]}["erdos_99_hyp_a"], "empirical")
        with tempfile.TemporaryDirectory() as d:
            md = H.render_residual_md("99", r, Path(d) / "Residual.lean", [], 1, [])
        self.assertIn("conjecture (empirical)", md)

    def test_literature_wide_asks_for_techniques_and_obstructions(self):
        prob = {"id": "99", "statement": "s"}
        self.assertNotIn("TRANSFERABLE TECHNIQUES", H.literature_prompt(prob))
        wide = H.literature_prompt(prob, "wide")
        for part in ("PARTIAL RESULTS", "ANALOGOUS SOLVED PROBLEMS", "TRANSFERABLE TECHNIQUES", "KNOWN OBSTRUCTIONS"):
            self.assertIn(part, wide)


class CoreFirst(Isolated):
    def test_the_hardest_hypothesis_is_attacked_first_with_its_share(self):
        h = _stub(self.root / "run")
        h.args.attack_order = "core-first"
        h.args.core_share = 0.5
        two = SKELETON.replace("theorem erdos_99_hyp_done : True := by\n  trivial",
                               "theorem erdos_99_hyp_easy : 1 = 1 := by\n  sorry")
        meta = {"hypotheses": [{"name": "erdos_99_hyp_a", "difficulty": "hard"},
                               {"name": "erdos_99_hyp_easy", "difficulty": "elementary"}]}
        h.ask = _judged(lambda purpose, prompt, **kw: plan_reply(two, meta))
        calls = []

        def attack(sub, name, sdir, cycle, module, remaining, recursive=False, **kw):
            calls.append((name, kw.get("share")))
            return 3, argparse.Namespace(state={})
        h._attack_substatement = attack
        h._install_lemmas_module = lambda pdir: None
        h.run_program()
        self.assertEqual(calls[0], ("erdos_99_hyp_a", 0.5))
        self.assertEqual(calls[1][1], None)


class IdeaRetries(unittest.TestCase):
    def test_an_over_budget_plan_is_retried_at_the_same_effort(self):
        h = _stub(tempfile.mkdtemp())
        seen = []

        class LLM:
            last_meta = {}
            call_budget_usd = 8.0
            def _tuning(self, purpose):
                return (None, 8.0)
            def complete(self, purpose, prompt, effort_override=None, budget_override=None):
                seen.append((effort_override, budget_override))
                if len(seen) == 1:
                    raise RuntimeError("claude -p returned an error result (plan): error_max_budget_usd: budget")
                return "ok"
        h.llm = LLM()
        h._note_budget = lambda purpose: None
        del h.ask                                           # the real ask, not the stub's
        h.args.run_budget = 20.0
        self.assertEqual(H.Harness.ask(h, "plan", "p", effort="high", budget=2.0), "ok")
        self.assertEqual(seen[1][0], "high")               # not lowered
        self.assertAlmostEqual(seen[1][1], 4.0)


class Exploration(Isolated):
    def _h(self):
        h = _stub(self.root / "run")
        h.args.explore, h.args.explore_budget, h.args.explore_turns = "on", 1.5, 10
        h._outbound = lambda p: p
        h._with_research_guidance = lambda purpose, p: p
        h.saved = []
        h.save = lambda: h.saved.append(1)
        return h

    def test_a_session_leaves_a_notebook_every_plan_sees(self):
        h = self._h()
        seen = {}

        class LLM:
            last_meta = {"cost_usd": 0.7, "turns": 9}
            def complete_explore(self, purpose, prompt, sandbox, turns, budget=None, **kw):
                seen.update(sandbox=sandbox, budget=budget, prompt=prompt)
                (sandbox / "NOTEBOOK.md").write_text("## Verdict\nTRUE 0.8: isolated sums grow like 0.3 n^2\n"
                                                     "## Conjectures\n- iso(A) >= c n^2 | ET sets to p=149 | survives\n")
                (sandbox / "e1.py").write_text("print(1)")
                return "## Verdict\nTRUE 0.8"
        h.llm = LLM()
        entry = h._explore("problem")
        self.assertTrue(os.access(seen["sandbox"] / "run.sh", os.X_OK))
        self.assertTrue((seen["sandbox"] / "runner.py").exists())
        self.assertEqual(seen["budget"], 1.5)
        self.assertIn("TRUE 0.8", entry["verdict"])
        self.assertEqual(entry["scripts"], ["e1.py"])
        ctx = h._exploration_context()
        self.assertIn("EXPLORATION NOTEBOOK", ctx)
        self.assertIn("iso(A) >= c n^2", ctx)
        pdir = self.pdir()
        pdir.mkdir(parents=True)
        self.assertIn("iso(A) >= c n^2", h._plan_extras(pdir, stalled=False))
        cost = [e for e in h.log.events if e[0] == "llm" and e[1] == "response" and e[2].get("purpose") == "explore"]
        self.assertEqual(cost[0][2]["cost_usd"], 0.7)      # spend accounting sees the session

    def test_the_problem_is_explored_once(self):
        h = self._h()
        calls = []
        h._explore = lambda scope="problem", **k: calls.append(scope)
        h.state["exploration"] = {"notebooks": [{"scope": "problem", "text": "x"}]}
        h._maybe_explore()
        self.assertEqual(calls, [])                          # the --open parent already explored it
        h.state["exploration"] = {}
        h._maybe_explore()
        self.assertEqual(calls, ["problem"])

    def test_a_cut_off_session_still_yields_its_notebook(self):
        h = self._h()

        class LLM:
            last_meta = {"cost_usd": 1.5}
            def complete_explore(self, purpose, prompt, sandbox, turns, budget=None, **kw):
                (sandbox / "NOTEBOOK.md").write_text("## Verdict\nUNSURE\n## Conjectures\n- partial data\n")
                raise RuntimeError("claude -p returned an error result (explore): error_max_budget_usd")
        h.llm = LLM()
        entry = h._explore("problem")
        self.assertIn("partial data", entry["text"])

    def test_a_session_that_never_wrote_its_notebook_keeps_its_computations(self):
        h = self._h()

        class LLM:
            last_meta = {"cost_usd": 1.5}
            def complete_explore(self, purpose, prompt, sandbox, turns, budget=None, **kw):
                (sandbox / "runs.log").write_text("\n===== s1.py (exit 0) =====\nn=8 iso=5\n")
                return "ran out before writing the notebook"
        h.llm = LLM()
        entry = h._explore("problem")
        self.assertIn("n=8 iso=5", entry["text"])
        self.assertTrue(any(e[1] == "notebook_missing" for e in h.log.events))

    def test_masked_backend_masks_exploration_prompts(self):
        seen = {}

        class Inner:
            def complete_explore(self, purpose, prompt, sandbox, turns, budget=None, **kw):
                seen["p"] = prompt
                return ""
        H.MaskedBackend(Inner()).complete_explore("explore", "an Erdős problem", Path("/tmp"), 1)
        self.assertEqual(seen["p"], "an problem")


class ToolBoundaries(unittest.TestCase):
    """Every CLI call loads no MCP server; tool sessions read and write only where they are meant to."""

    def cmd_for(self, call):
        seen = {}
        def run(cmd, **kw):
            seen["cmd"] = cmd
            return type("R", (), {"returncode": 0, "stderr": "",
                                  "stdout": json.dumps({"type": "result", "subtype": "success", "is_error": False,
                                                        "result": "ok", "total_cost_usd": 0.01, "num_turns": 1})})()
        with patch.object(H, "run_tracked", side_effect=run):
            call(H.ClaudeCliBackend(None, 10))
        return seen["cmd"]

    def test_no_mcp_connectors_on_any_call(self):
        for call in (lambda b: b.complete("plan", "x"),
                     lambda b: b.complete_agentic("prove-agentic", "x", Path("/tmp"), 3),
                     lambda b: b.complete_explore("explore", "x", Path("/tmp"), 3)):
            cmd = self.cmd_for(call)
            self.assertIn("--strict-mcp-config", cmd)
            self.assertEqual(cmd[cmd.index("--mcp-config") + 1], '{"mcpServers":{}}')

    def test_the_prover_reads_only_its_sandbox_mathlib_libraries_and_own_modules(self):
        cmd = self.cmd_for(lambda b: b.complete_agentic("prove-agentic", "x", Path("/tmp"), 3,
                                                        read_paths=["/F/Formal/Programs/Erdos99*"]))
        allowed = cmd[cmd.index("--allowedTools") + 1: cmd.index("--allowedTools") + 20]
        for bare in ("Read", "Edit", "Write", "Grep", "Glob"):
            self.assertNotIn(bare, allowed)                  # a bare rule reaches every file on the machine
        self.assertNotIn("--add-dir", cmd)
        self.assertIn("Read(//F/Formal/Programs/Erdos99*)", cmd)
        self.assertIn(f"Grep(/{H.FORMAL}/.lake/packages/**)", cmd)
        self.assertIn("Edit(./**)", cmd)

    def test_exploration_reads_and_writes_only_its_sandbox(self):
        cmd = self.cmd_for(lambda b: b.complete_explore("explore", "x", Path("/tmp"), 3, effort="medium"))
        self.assertEqual(cmd[cmd.index("--effort") + 1], "medium")
        rules = [c for c in cmd if c.startswith(("Read(", "Grep(", "Glob(", "Edit(", "Write("))]
        self.assertTrue(rules and all(r.endswith("(./**)") for r in rules), rules)
        self.assertIn("Bash(./run.sh:*)", cmd)

    def test_own_module_paths_name_this_problem_only(self):
        h = H.Harness.__new__(H.Harness)
        h.problem = {"id": "12345"}
        self.assertEqual(h._own_module_paths(), [f"{H.FORMAL}/Formal/Programs/Erdos12345*"])


class ExploreRunner(unittest.TestCase):
    """The sandbox runner applies the harness's screen before running anything."""

    def run_script(self, code):
        with tempfile.TemporaryDirectory() as d:
            d = Path(d)
            (d / "runner.py").write_text(H.explore_runner_source())
            (d / "s.py").write_text(code)
            r = subprocess.run([sys.executable, str(d / "runner.py"), "s.py"], capture_output=True, text=True, cwd=str(d),
                               timeout=120)
            return r.returncode, r.stdout

    def test_allowed_code_runs_and_forbidden_code_is_refused(self):
        rc, out = self.run_script("from math import comb\nprint(comb(6, 3))\n")
        self.assertEqual(rc, 0)
        self.assertIn("20", out)
        for bad in ("import os\n", "import subprocess\n", "print(open('x').read())\n", "import numpy as np\nnp.save('a', 1)\n"):
            rc, out = self.run_script(bad)
            self.assertEqual(rc, 2, bad)
            self.assertIn("REFUSED", out)

    def test_the_runner_screen_agrees_with_the_harness_screen(self):
        for code in ("import numpy\n", "import os\n", "x = eval('1')\n", "import networkx as nx\nnx.write_gml(g, 'f')\n"):
            harness_says = H.unsafe_python(code, allowed=H.EXPLORE_MODULES, extra=H.EXPLORE_FORBIDDEN)
            rc, _ = self.run_script(code)
            self.assertEqual(harness_says is not None, rc == 2, code)


if __name__ == "__main__":
    unittest.main()
