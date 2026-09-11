import argparse, json, unittest, tempfile
from pathlib import Path
import harness as H


def _h(tmp, **state):
    """A Harness with just enough wired up to exercise one stage."""
    h = H.Harness.__new__(H.Harness)
    h.run_dir = Path(tmp)
    h.problem = {"id": "99273", "statement": "Is there a covering system with all moduli p-1, p>=5 prime?"}
    h.direction = None
    h.state = {"statement": "theorem t : True := by sorry", "mode": "search-first", **state}
    h.log = H.RunLog(h.run_dir)
    h.llm = argparse.Namespace(total_cost_usd=0.0)
    h.save = lambda: None
    h.args = argparse.Namespace(reduce="auto", reduce_seconds=10, search_escalate="auto",
                                search_escalate_seconds=30, search_seconds=90)
    return h


class SandboxReachesTheSolver(unittest.TestCase):
    """The allowlist promises pysat to model-written scripts. `python -I` hides the user site directory
    where it lives, so every stage that runs such a script must go through sandbox_argv -- stage_search
    once had its own bare `-I` invocation and would have failed every import."""

    def test_argv_names_the_solver_path_when_one_exists(self):
        argv = H.sandbox_argv(Path("/tmp/x.py"))
        self.assertEqual(argv[:2], [H.sys.executable, "-I"])
        if H.SOLVER_AVAILABLE:
            self.assertIn("sys.path.insert", argv[3])
            self.assertIn("site-packages", argv[3])
        else:
            self.assertEqual(argv[2], "/tmp/x.py")

    def test_a_relative_script_path_still_runs(self):
        """The sandbox runs with cwd set to the script's directory, so a relative path handed in by a
        caller is unfindable from inside. Cost a live #273 escalation: FileNotFoundError, rc=1, 0 seconds."""
        import os, subprocess, tempfile
        from pathlib import Path
        with tempfile.TemporaryDirectory() as tmp:
            sdir = Path(tmp) / "search"
            sdir.mkdir()
            (sdir / "s.py").write_text("print('ran')")
            cwd = os.getcwd()
            try:
                os.chdir(tmp)
                argv = H.sandbox_argv(Path("search/s.py"))          # relative, as a caller may give it
            finally:
                os.chdir(cwd)
            r = subprocess.run(argv, capture_output=True, text=True, timeout=60, cwd=str(sdir),
                               env={"PATH": "/usr/bin:/bin", "HOME": str(sdir)})
            self.assertEqual(r.returncode, 0, r.stderr[:300])
            self.assertIn("ran", r.stdout)

    def test_no_stage_builds_its_own_sandbox_command(self):
        src = Path(H.__file__).read_text()
        self.assertEqual(src.count('sys.executable, "-I"'), 2, "sandbox_argv must be the only builder")


class ReductionsMustBeChecked(unittest.TestCase):
    """A proposed reduction is fed to the search and proof stages as fact, so an unverified one is a
    liability. Only claims whose check script prints REDUCTION-OK may propagate."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
    def tearDown(self):
        self.tmp.cleanup()

    def _run(self, reductions):
        h = _h(self.tmp.name)
        h.ask = lambda *a, **k: "```json\n" + json.dumps({"reductions": reductions}) + "\n```"
        h.stage_reduce()
        return h.state["reductions"]

    def test_a_passing_check_is_kept_and_propagates(self):
        r = self._run([{"kind": "parity", "claim": "every modulus is even", "justification": "j",
                        "consequence": "two disjoint systems", "check": "print('REDUCTION-OK')"}])
        self.assertEqual([e["claim"] for e in r["verified"]], ["every modulus is even"])
        h = _h(self.tmp.name, reductions=r)
        self.assertIn("every modulus is even", h.reduction_context())
        self.assertIn("[parity]", h.reduction_context())

    def test_a_failing_check_is_refuted_and_never_propagates(self):
        r = self._run([{"kind": "parity", "claim": "false claim", "justification": "j", "consequence": "c",
                        "check": "print('REDUCTION-FAIL m=9 is odd')"}])
        self.assertEqual(r["verified"], [])
        self.assertEqual(r["rejected"][0]["verdict"], "refuted")
        self.assertIn("m=9 is odd", r["rejected"][0]["detail"])
        self.assertEqual(_h(self.tmp.name, reductions=r).reduction_context(), "")

    def test_a_check_that_says_nothing_is_not_evidence(self):
        r = self._run([{"kind": "symmetry", "claim": "c", "justification": "j", "consequence": "c",
                        "check": "print('looks fine to me')"}])
        self.assertEqual(r["verified"], [])
        self.assertEqual(r["rejected"][0]["verdict"], "check_failed")

    def test_an_unsafe_check_is_rejected_unrun(self):
        r = self._run([{"kind": "parity", "claim": "c", "justification": "j", "consequence": "c",
                        "check": "import os; os.system('echo hi'); print('REDUCTION-OK')"}])
        self.assertEqual(r["verified"], [])
        self.assertEqual(r["rejected"][0]["verdict"], "unchecked")

    def test_no_context_block_when_there_is_nothing_to_say(self):
        self.assertEqual(_h(self.tmp.name).reduction_context(), "")
        self.assertEqual(_h(self.tmp.name, reductions={"verified": []}).reduction_context(), "")


class EscalationReplacesAbort(unittest.TestCase):
    """#273's search cleared everything below its first real candidate with a cheap screen, then stopped on
    a timer -- recording a floor one step below where the problem starts. That shape must change tools."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.sdir = Path(self.tmp.name) / "search"
        self.sdir.mkdir(parents=True)
        (self.sdir / "stdout.txt").write_text("L with reciprocal density >= 1: 4 (smallest 55440)\n"
                                              "L=55440 (43 moduli, density 1.044): aborted (budget)\n")
    def tearDown(self):
        self.tmp.cleanup()

    def _esc(self, result, script):
        h = _h(self.tmp.name)
        h.ask = lambda *a, **k: "```python\n" + script + "\n```"
        return h.escalate_search(result, "witness", self.sdir, "")

    def test_a_screen_only_range_escalates(self):
        out = self._esc({"status": "none", "searched": {"exhaustive_to": 55439, "kind": "screen"}, "elapsed_s": 18},
                        "print('NONE')\nprint('SEARCHED: {\"exhaustive_to\": 55440, \"parameter\": \"lcm\", \"kind\": \"exhaustive\"}')")
        self.assertEqual(out["escalation"]["status"], "none")
        # the solver decided the case the screen could not, so the recorded range is upgraded
        self.assertEqual(out["searched"]["kind"], "exhaustive")
        self.assertEqual(out["searched"]["exhaustive_to"], 55440)

    def test_an_undecided_escalation_leaves_the_original_floor_alone(self):
        out = self._esc({"status": "none", "searched": {"exhaustive_to": 55439, "kind": "screen"}, "elapsed_s": 18},
                        "print('NONE')\nprint('SEARCHED: {\"exhaustive_to\": null, \"parameter\": \"lcm\", \"kind\": \"partial\"}')")
        self.assertEqual(out["searched"]["kind"], "screen")      # not overwritten by an undecided run
        self.assertEqual(out["escalation"]["searched"]["kind"], "partial")

    def test_a_witness_from_the_solver_wins(self):
        out = self._esc({"status": "none", "searched": None, "elapsed_s": 95},
                        "print('WITNESS: {\"moduli\": [4, 6]}')")
        self.assertEqual(out["status"], "found")
        self.assertEqual(out["witness"], {"moduli": [4, 6]})

    def test_a_clean_exhaustive_sweep_is_left_alone(self):
        called = []
        h = _h(self.tmp.name)
        h.ask = lambda *a, **k: called.append(1) or "```python\nprint('NONE')\n```"
        out = h.escalate_search({"status": "none", "elapsed_s": 5,
                                 "searched": {"exhaustive_to": 1e9, "kind": "exhaustive"}},
                                "witness", self.sdir, "")
        self.assertEqual(called, [])                              # no model call, nothing to escalate to
        self.assertNotIn("escalation", out)

    def test_a_found_witness_is_never_re_searched(self):
        h = _h(self.tmp.name)
        h.ask = lambda *a, **k: self.fail("must not escalate after a hit")
        self.assertEqual(h.escalate_search({"status": "found", "witness": {"n": 1}}, "witness", self.sdir, ""),
                         {"status": "found", "witness": {"n": 1}})

    def test_one_rejected_import_does_not_throw_away_the_escalation(self):
        """A live #273 escalation was lost to a single `import sys`. stage_search has retried on a screen
        rejection since an `import json` cost it a stage; the escalation was written without that."""
        calls = []
        h = _h(self.tmp.name)
        def ask(purpose, prompt, **k):
            calls.append(prompt)
            if len(calls) == 1:
                return "```python\nimport sys\nprint('NONE')\n```"
            return ("```python\nprint('NONE')\n"
                    "print('SEARCHED: {\"exhaustive_to\": 55440, \"parameter\": \"lcm\", \"kind\": \"exhaustive\"}')\n```")
        h.ask = ask
        out = h.escalate_search({"status": "none", "searched": {"exhaustive_to": 55439, "kind": "screen"}},
                                "witness", self.sdir, "")
        self.assertEqual(len(calls), 2, "must retry once after a screen rejection")
        self.assertIn("import sys", calls[1])          # the retry names what was rejected
        self.assertEqual(out["escalation"]["status"], "none")
        self.assertEqual(out["searched"]["kind"], "exhaustive")

    def test_it_gives_up_after_the_retry(self):
        calls = []
        h = _h(self.tmp.name)
        h.ask = lambda *a, **k: calls.append(1) or "```python\nimport os\nprint('NONE')\n```"
        out = h.escalate_search({"status": "none", "searched": None}, "witness", self.sdir, "")
        self.assertEqual(len(calls), 2)
        self.assertEqual(out["escalation"]["status"], "rejected")

    def test_off_disables_it(self):
        h = _h(self.tmp.name)
        h.args.search_escalate = "off"
        h.ask = lambda *a, **k: self.fail("must not call the model when disabled")
        out = h.escalate_search({"status": "none", "searched": None}, "witness", self.sdir, "")
        self.assertNotIn("escalation", out)


class ReadingsAreRecorded(unittest.TestCase):
    """A proof is about the frozen statement, not the English sentence. Conventions the formalisation
    supplies (#273 requires DISTINCT moduli; the published sentence does not say so) belong in the record."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
    def tearDown(self):
        self.tmp.cleanup()

    def test_classified_and_risky_readings_are_flagged(self):
        h = _h(self.tmp.name)
        h.ask = lambda *a, **k: "```json\n" + json.dumps({"readings": [
            {"reading": "the moduli must be distinct", "where": "x.2 = y.2 -> x = y",
             "load_bearing": "essential", "why": "without it 0,1,2,3 mod 4 is a trivial solution"},
            {"reading": "only positive n", "where": "n : N", "load_bearing": "risky", "why": "narrows the claim"},
            {"reading": "unlabelled", "where": "", "load_bearing": "nonsense", "why": ""}]}) + "\n```"
        h.record_readings()
        got = h.state["documented_readings"]
        self.assertEqual([r["load_bearing"] for r in got], ["essential", "risky", "unclassified"])
        self.assertIn("distinct", got[0]["reading"])

    def test_no_readings_is_a_valid_answer(self):
        h = _h(self.tmp.name)
        h.ask = lambda *a, **k: '```json\n{"readings": []}\n```'
        h.record_readings()
        self.assertEqual(h.state["documented_readings"], [])

    def test_a_failed_call_never_fails_the_run(self):
        h = _h(self.tmp.name)
        def boom(*a, **k):
            raise RuntimeError("provider down")
        h.ask = boom
        h.record_readings()
        self.assertEqual(h.state["documented_readings"], [])


if __name__ == "__main__":
    unittest.main()


class TimeoutKeepsTheScriptsOutput(unittest.TestCase):
    """A timeout is the path that triggers escalation, and it was the path that threw away the script's
    progress lines -- so the escalation prompt got an empty tail exactly when it needed to know where the
    first script stopped. Live on #273: `stdout.txt` was never written."""

    def test_partial_stdout_survives_a_timeout(self):
        import subprocess, tempfile
        from pathlib import Path
        with tempfile.TemporaryDirectory() as tmp:
            sdir = Path(tmp)
            script = sdir / "s.py"
            script.write_text("import time\nprint('L=55440: aborted', flush=True)\ntime.sleep(30)\n")
            try:
                subprocess.run(H.sandbox_argv(script), capture_output=True, timeout=2, cwd=str(sdir),
                               env={"PATH": "/usr/bin:/bin", "HOME": str(sdir)})
                self.fail("expected a timeout")
            except subprocess.TimeoutExpired as e:
                out = (e.stdout or b"").decode(errors="replace")
                self.assertIn("L=55440", out, "TimeoutExpired must carry the partial output we now persist")


class SameDefectsAuditedAcrossEveryNewPath(unittest.TestCase):
    """The escalation had three defects: no retry on a safety rejection, output discarded on timeout, and
    a cwd-relative path. Each was a CLASS, not a one-off. These check the other new paths for the same."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
    def tearDown(self):
        self.tmp.cleanup()

    def test_reduce_reasks_when_a_check_trips_the_safety_screen(self):
        calls = []
        h = _h(self.tmp.name)
        def ask(purpose, prompt, **k):
            calls.append(prompt)
            bad = {"kind": "parity", "claim": "c", "justification": "j", "consequence": "q",
                   "check": "import sys\nprint('REDUCTION-OK')"}
            good = dict(bad, check="print('REDUCTION-OK')")
            return "```json\n" + json.dumps({"reductions": [bad if len(calls) == 1 else good]}) + "\n```"
        h.ask = ask
        h.stage_reduce()
        self.assertEqual(len(calls), 2, "a rejected check must be re-asked, not silently dropped")
        self.assertIn("rejected by the safety screen", calls[1])
        self.assertEqual(len(h.state["reductions"]["verified"]), 1)

    def test_reduce_reasks_when_the_reply_is_not_json(self):
        calls = []
        h = _h(self.tmp.name)
        h.ask = lambda *a, **k: calls.append(1) or "no json here at all"
        h.stage_reduce()
        self.assertEqual(len(calls), 2)
        self.assertEqual(h.state["reductions"]["verified"], [])

    def test_run_py_keeps_partial_output_on_timeout(self):
        from pathlib import Path
        h = H.Harness.__new__(H.Harness)
        d = Path(self.tmp.name)
        (d / "slow.py").write_text("import time\nprint('partial progress', flush=True)\ntime.sleep(30)\n")
        rc, out = H.Harness._run_py(h, d / "slow.py", 2, d)
        self.assertEqual(rc, -9)
        self.assertIn("partial progress", out, "a timed-out script's output must not be discarded")
        self.assertIn("[timeout]", out)

    def test_a_recorded_floor_kind_reaches_the_problem_file(self):
        """known_floor_note reads the PROBLEM file, so a kind recorded only in reviewed.json never gets
        to the next search -- which is the whole point of typing floors.

        Asserts the round-trip, not a literal: #273's kind was `screen` and became `exhaustive` when the
        candidate lcms were eliminated algebraically, and a test pinned to the value fails on a correct
        data update while still not checking that the kind actually propagates."""
        import json as _json, pathlib as _p
        prob = _json.loads(_p.Path("problems/erdos_273.json").read_text())
        kind = prob.get("search_floor_kind")
        self.assertIn(kind, ("screen", "exhaustive", "published"), "a filed floor must carry a typed kind")
        atlas = _json.loads(_p.Path("atlas-data/reviewed.json").read_text())["273"]
        self.assertEqual(kind, atlas.get("search_floor_kind"),
                         "the problem file and the Atlas must not disagree about how the floor was obtained")
        self.assertEqual(float(prob["search_floor"]), float(atlas["search_floor"]))
        h = H.Harness.__new__(H.Harness)
        h.problem, h.state = prob, {}
        self.assertIn(kind, h.known_floor_note())


class EveryRetryPromptActuallyRenders(unittest.TestCase):
    """A retry path that is never exercised can carry a NameError or a missing format key and look fine.
    The construct retry shipped referencing an `archive_note` that did not exist in scope."""

    def test_construct_retry_prompt_renders(self):
        p = H.CONSTRUCT_PROMPT.format(pid="1", statement_en="e", notes="n", statement="s",
                                      known="unknown", iteration=2, archive="[]", program="(none)")
        self.assertGreater(len(p), 100)

    def test_search_and_escalate_and_reduce_prompts_render(self):
        self.assertGreater(len(H.SEARCH_PROMPT.format(
            kind="witness", pid="1", statement_en="e", notes="n", statement="s", cap_seconds=90,
            cap_candidates=10 ** 7, kind_expl="x", solver_line=H.SOLVER_LINE, known_floor="")), 100)
        self.assertGreater(len(H.Harness.ESCALATE_PROMPT.format(
            kind="witness", pid="1", statement="s", statement_en="e", tail="t",
            solver_line="sl", cap_seconds=900, modules="math")), 100)
        self.assertGreater(len(H.REDUCE_PROMPT.format(
            pid="1", statement_en="e", notes="n", statement="s", check_seconds=45, modules="math",
            library="")), 100)
        self.assertGreater(len(H.READINGS_PROMPT.format(
            pid="1", statement_en="e", notes="n", statement="s")), 100)

    def test_lean_timeout_keeps_what_lean_printed(self):
        import inspect
        src = inspect.getsource(H.LeanChecker.check)
        self.assertIn("TimeoutExpired as e", src, "the Lean timeout path must capture partial output")
        self.assertNotIn('"raw": ""', src)


class ConstraintsAreAContractNotProse(unittest.TestCase):
    """A live #273 escalation was handed a cardinality bound, seven forced moduli and an affine symmetry
    as prose, asserted none of them, and produced an instance no stronger than one written without them.
    Constraint-bearing reductions now arrive by id, and the escalation has to account for them."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.sdir = Path(self.tmp.name) / "search"
        self.sdir.mkdir(parents=True)
        (self.sdir / "stdout.txt").write_text("L=55440: aborted\n")
        self.reds = {"verified": [
            {"id": "R1", "kind": "forced", "claim": "c1", "justification": "j", "consequence": "q",
             "constraint": "moduli 4,6,10,12,16,18,22 must each be used"},
            {"id": "R2", "kind": "parity", "claim": "c2", "justification": "j", "consequence": "q"},
            {"id": "R3", "kind": "forced", "claim": "c3", "justification": "j", "consequence": "q",
             "constraint": "at least 18 congruences"}]}
    def tearDown(self):
        self.tmp.cleanup()

    def test_constraints_render_as_a_must_assert_contract(self):
        ctx = _h(self.tmp.name, reductions=self.reds).reduction_context()
        self.assertIn("ASSERTABLE CONSTRAINTS", ctx)
        self.assertIn("R1: moduli 4,6,10,12,16,18,22 must each be used", ctx)
        self.assertIn("R3: at least 18 congruences", ctx)
        self.assertIn("MUST assert", ctx)
        self.assertEqual(_h(self.tmp.name, reductions=self.reds).assertable_ids(), ["R1", "R3"])

    def test_a_reduction_with_no_constraint_is_not_demanded(self):
        self.assertNotIn("R2:", _h(self.tmp.name, reductions=self.reds).reduction_context()
                         .split("ASSERTABLE CONSTRAINTS")[1])

    def test_an_encoding_that_asserts_nothing_is_rewritten_before_the_solver_runs(self):
        calls = []
        h = _h(self.tmp.name, reductions=self.reds)
        def ask(purpose, prompt, **k):
            calls.append(prompt)
            if len(calls) == 1:
                return "```python\nprint('NONE')\n```"          # no ASSERTED line at all
            return ("```python\nprint('ASSERTED: {\"used\": [\"R1\", \"R3\"], \"skipped\": {}}')\n"
                    "print('NONE')\n```")
        h.ask = ask
        out = h.escalate_search({"status": "none", "searched": {"exhaustive_to": 1, "kind": "screen"}},
                                "witness", self.sdir, "")
        self.assertEqual(len(calls), 2, "an encoding asserting nothing must be rewritten")
        self.assertIn("assert none of", calls[1])
        self.assertEqual(out["escalation"]["constraints_asserted"]["used"], ["R1", "R3"])
        self.assertEqual(out["escalation"]["constraints_available"], ["R1", "R3"])

    def test_ignored_constraints_are_recorded_not_hidden(self):
        h = _h(self.tmp.name, reductions=self.reds)
        h.ask = lambda *a, **k: ("```python\nprint('ASSERTED: {\"used\": [\"R1\"], "
                                 "\"skipped\": {\"R3\": \"no reason\"}}')\nprint('NONE')\n```")
        out = h.escalate_search({"status": "none", "searched": None}, "witness", self.sdir, "")
        esc = out["escalation"]
        self.assertEqual(esc["constraints_asserted"]["used"], ["R1"])
        self.assertIn("R3", esc["constraints_asserted"]["skipped"])


class CandidatesAreOrderedByConstraintNotSize(unittest.TestCase):
    """Three attempts on #273 went to L=55440 because it is numerically first, when it is among the
    loosest of the 29 candidates (slack 0.0437, 7 of 43 moduli forced). L=100800 has slack 0.000089 and
    45 of 50 forced, collapsing to 12 enumerable subsets. Order by slack, not by size."""

    def test_the_search_prompt_states_the_rule_with_its_worked_numbers(self):
        r = H.SEARCH_PROMPT.format(kind="witness", pid="1", statement_en="e", notes="n", statement="s",
                                   cap_seconds=90, cap_candidates=10 ** 7, kind_expl="x",
                                   solver_line=H.SOLVER_LINE, known_floor="")
        self.assertIn("NOT BY SIZE", r)
        self.assertIn("LEAST SLACK FIRST", r)
        self.assertIn("55440", r)          # the wrong entry point
        self.assertIn("100800", r)         # the right one
        self.assertIn("CANDIDATES:", r)    # and the ordering must be reported

    def test_the_escalation_targets_the_most_constrained_undecided_case(self):
        r = H.Harness.ESCALATE_PROMPT.format(kind="witness", pid="1", statement="s", statement_en="e",
                                             tail="t", solver_line="sl", cap_seconds=900, modules="math")
        self.assertIn("MOST", r)
        self.assertIn("not the first or the smallest", r)
        self.assertIn("100800", r)
