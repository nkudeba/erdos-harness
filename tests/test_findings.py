"""Changes driven by the 2026-09-10 open-problem assessments (#287, #488, #848).

Each test pins a behaviour that a real finding showed was missing, so a regression is legible as
"the thing we learned stopped being true".
"""
import argparse, sys, tempfile, unittest
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import harness as H


class PlanRound(unittest.TestCase):
    """Tier-L one-shot rounds never produced the proof, only the plan, so they are budgeted as plans."""

    def test_constants_are_cheaper_than_a_proof_call(self):
        self.assertLess(H.PLAN_ROUND_BUDGET, 8.0)
        self.assertIn(H.PLAN_ROUND_EFFORT, ("low", "medium"))

    def test_ask_forwards_per_call_tuning(self):
        seen = {}

        class Backend:
            def complete(self, purpose, prompt, effort_override=None, budget_override=None):
                seen.update(purpose=purpose, effort=effort_override, budget=budget_override)
                return "ok"
        h = H.Harness.__new__(H.Harness)
        h.llm, h.log = Backend(), type("L", (), {"event": lambda *a, **k: None})()
        h.args = argparse.Namespace(run_budget=None)
        h.run_dir = Path(tempfile.mkdtemp())
        h._check_run_budget = lambda purpose: None
        self.assertEqual(h.ask("prove", "p", effort="medium", budget=2.5), "ok")
        self.assertEqual((seen["effort"], seen["budget"]), ("medium", 2.5))
        h.ask("prove", "p")
        self.assertEqual((seen["effort"], seen["budget"]), (None, None))


class SearchFloorFeedback(unittest.TestCase):
    """An exhaustive miss is a finding: it must be recorded so the region is not searched twice."""

    def test_prompt_asks_for_the_covered_range(self):
        rendered = H.SEARCH_PROMPT.format(kind="counterexample", pid="1", statement_en="s", notes="n",
                                          statement="t", cap_seconds=90, cap_candidates=10 ** 7, kind_expl="e",
                                          solver_line=H.SOLVER_LINE, known_floor="")
        self.assertIn("SEARCHED:", rendered)
        self.assertIn("exhaustive_to", rendered)
        # A floor must say how it was obtained: a cheap screen is not an exhaustive search, and reporting
        # one as the other is a false claim of progress.
        for kind in ('"exhaustive"', '"screen"', '"partial"'):
            self.assertIn(kind, rendered)

    def test_a_solver_is_offered_when_one_is_installed(self):
        # the search stage's biggest miss was hand-rolling a DFS for a question a SAT solver decides
        if H.SOLVER_AVAILABLE:
            self.assertIn("pysat", H.SOLVER_LINE)
            self.assertIn("pysat", H.ALLOWED_PY_MODULES)
        else:
            self.assertIn("no SAT solver", H.SOLVER_LINE)

    def test_a_recorded_floor_later_suppresses_the_search(self):
        # the floor a clean sweep would record, fed back through the problem file, must skip the next search
        futile, why = H.search_futility({}, {"search_floor": 4e19})
        self.assertTrue(futile)
        self.assertIn("problem file", why)
        self.assertFalse(H.search_futility({}, {"search_floor": 1000})[0])


class RouteDisclosure(unittest.TestCase):
    """A supplied proof route can narrow the formalization (#649's positive-integer domain), so say so."""

    problem = {"id": "649", "statement": "Is every pair of primes realized?", "notes": "n"}

    def test_no_route_means_no_disclosure(self):
        p = H.compare_prompt(self.problem, "back", route="")
        self.assertNotIn("ASSISTANCE DISCLOSURE", p)
        self.assertNotIn("NARROWED TO FIT", p)

    def test_route_is_disclosed_in_both_prompt_forms(self):
        for direction in (None, "pos", "neg"):
            p = H.compare_prompt(self.problem, "back", direction=direction, route="use n = 2^k and p = 2, q = 7")
            self.assertIn("ASSISTANCE DISCLOSURE", p)
            self.assertIn("NARROWED TO FIT", p)
            self.assertIn("use n = 2^k", p)

    def test_supplied_route_reports_operator_assistance(self):
        h = H.Harness.__new__(H.Harness)
        h.state = {}
        self.assertEqual(h._supplied_route(), "")
        h.state = {"literature": "Sawhney proves it for large N"}
        self.assertIn("Sawhney", h._supplied_route())
        h.state["operator_context"] = [{"sha256": "a"}]
        self.assertIn("operator-supplied", h._supplied_route())
        h.state["literature_provenance"] = {"mode": "source_notes_fallback"}
        self.assertIn("fallback", h._supplied_route())


if __name__ == "__main__":
    unittest.main()


class RecordedFloorsReachTheNextSearch(unittest.TestCase):
    """A recorded floor is only worth recording if the next search is told about it. search_futility
    skips the stage when the floor is out of reach, but the in-between case -- a floor worth respecting
    that is not big enough to abandon the search -- was passed nothing at all."""

    def _h(self, problem, state):
        import argparse
        h = H.Harness.__new__(H.Harness)
        h.problem, h.state = problem, state
        return h

    def test_a_filed_floor_is_named_with_its_kind(self):
        note = self._h({"search_floor": 55440.0, "search_floor_kind": "screen"}, {}).known_floor_note()
        self.assertIn("55440", note)
        self.assertIn("screen", note)
        self.assertIn("START ABOVE IT", note)

    def test_the_larger_of_filed_and_found_wins(self):
        note = self._h({"search_floor": 1e5}, {"search_floor_found": {"exhaustive_to": 1e9,
                                                                      "kind": "exhaustive"}}).known_floor_note()
        self.assertIn("1e+09", note)
        self.assertIn("exhaustive", note)

    def test_no_floor_means_no_note(self):
        self.assertEqual(self._h({}, {}).known_floor_note(), "")
        self.assertEqual(self._h({"search_floor": 0}, {}).known_floor_note(), "")
