"""The research engine (`--discover-mode engine`): the frontier map, assignments, research sessions, the referee,
adversary and novelty judges, the meta-review round, and the stage's outputs. No provider calls: every model call
goes through a scripted fake `call`, and every research session through a fake `session`."""
import json, sys, tempfile, threading, unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parent))
import harness as H
from test_discovery import FakeCall
from test_deductive_mode import _stub

LEAN = "theorem erdos_99 : ∀ n : ℕ, n = n := by\n  sorry"

FRONTIER = """Preamble the parser ignores.
=== DIRECTION
TRUE, confidence 0.85: the random model and every computed case agree.
=== KNOWN
- liminf q_n/n^2 > 0.352 | Richter 1976 | counting repeated gaps
=== BARRIERS
- sieving by fixed primes | the sequence 1+Pn^2 avoids them | does not rule out a growing set of primes
=== CORE
Show that the gap sequence skips almost every even value. This is hard because $\\sum_p 1/p$ diverges.
=== TARGET T1
TYPE: QUANT
STATEMENT: liminf q_n/n^2 >= 0.54.
BEYOND: improves Richter's 0.352.
VALUE: a sharper count of repeated gaps.
TEST: greedy sequences up to 10^6.
=== TARGET T2
TYPE: QUANT
STATEMENT: liminf q_n/n^2 >= 0.6.
BEYOND: improves T1.
VALUE: two primes at once.
TEST: none
=== TARGET T3
TYPE: SPECIAL
STATEMENT: the conclusion holds when every gap is a multiple of 6.
BEYOND: no special case is known.
VALUE: isolates the mod-5 obstruction.
TEST: none
=== ANGLE A1
TECHNIQUE: entropy compression
IDEA: encode a convex prime chain by its second differences.
BARRIERS: not a sieve, so 1+Pn^2 does not apply.
FIRST STEP: bound the number of convex chains with gaps at most G.
=== ANGLE A2
TECHNIQUE: large sieve
IDEA: sieve the gap values instead of the primes.
BARRIERS: the sieve dimension grows, which the fixed-prime barrier does not cover.
FIRST STEP: a large-sieve inequality for the set of used gaps.
"""


def notebook(*claims):
    blocks = []
    for i, (status, ty, st) in enumerate(claims, 1):
        blocks.append(f"### C{i}\nSTATEMENT: {st}\nSTATUS: {status}\nTYPE: {ty}\nBEYOND: beats Richter.\n"
                      f"PROOF: Step one.\nCase 1: small n, checked.\nTherefore the claim holds.")
    return "## Result\nThe best claim.\n## Claims\n" + "\n".join(blocks) + "\n## Data\nn | q_n\n## Dead ends\nnone\n"


def judge(purpose, valid=True, broken=False, verdict="new", sig=2):
    if purpose == "engine-referee":
        return "```json\n" + json.dumps({"valid": valid, "first_error": None if valid else "step 2 fails", "fixable": True}) + "\n```"
    if purpose == "engine-adversary":
        return "```json\n" + json.dumps({"broken": broken, "how": "n=3 breaks it" if broken else None,
                                         "severity": "fatal" if broken else "none"}) + "\n```"
    return "```json\n" + json.dumps({"verdict": verdict, "cite": None, "significance": sig, "why": "not in the literature"}) + "\n```"


META = """=== STATE
- liminf >= 0.54 (validated)
=== LESSONS
The entropy angle stalls at the singular series.
=== NEXT
1. Push the constant to 0.6 with two primes at once; technique: mod 3 and mod 5 together; first step: the joint count.
2. Attack CORE by entropy compression; first step: the second-difference code.
"""


class FakeSession:
    def __init__(self, notebooks, cost=1.0):
        self.notebooks, self.cost, self.calls, self.lock = notebooks, cost, [], threading.Lock()

    def __call__(self, purpose, prompt, label, turns, budget, effort):
        with self.lock:
            self.calls.append((label, prompt))
        nb = self.notebooks(label, prompt)
        if isinstance(nb, Exception):
            raise nb
        return "reply", nb, self.cost


class Frontier(unittest.TestCase):
    def test_sections_targets_angles_and_direction(self):
        f = H.parse_frontier(FRONTIER)
        self.assertEqual((f["answer"], f["confidence"]), ("true", 0.85))
        self.assertIn("Richter 1976", f["known"])
        self.assertIn("1+Pn^2", f["barriers"])
        self.assertEqual([t["type"] for t in f["targets"]], ["QUANT", "QUANT", "SPECIAL"])
        self.assertEqual(f["targets"][0]["test"], "greedy sequences up to 10^6.")
        self.assertEqual([a["technique"] for a in f["angles"]], ["entropy compression", "large sieve"])
        self.assertIn("convex chains", f["angles"][0]["first_step"])
        block = H.frontier_block(f)
        self.assertIn("KNOWN:", block)
        self.assertNotIn("TARGET", block)          # targets go out one per session, not to every session

    def test_assignments_are_bold_and_broad(self):
        f = H.parse_frontier(FRONTIER)
        picks = H.engine_assignments(f, 4, 0.5)
        self.assertEqual([p["kind"] for p in picks], ["angle", "angle", "target", "target"])
        self.assertEqual({p["type"] for p in picks if p["kind"] == "target"}, {"QUANT", "SPECIAL"})   # one of each first
        self.assertIn("ATTACK THE CORE", H.assignment_text(picks[0]))
        self.assertIn("PROVE THIS TARGET", H.assignment_text(picks[2]))
        many = H.engine_assignments(f, 7, 0.5)                      # more sessions than targets + angles: no repeats
        self.assertEqual(len(many), 5)


class Claims(unittest.TestCase):
    def test_claim_blocks_parse_with_multiline_proofs(self):
        cs = H.parse_claims(notebook(("PROVED", "QUANT", "liminf >= 0.54"), ("CONJECTURED", "core", "U(x) = o(x)")))
        self.assertEqual([(c["id"], c["status"], c["type"]) for c in cs], [("C1", "PROVED", "QUANT"), ("C2", "CONJECTURED", "OTHER")])
        self.assertIn("Case 1: small n", cs[0]["proof"])           # "Case 1:" is not a field
        self.assertEqual(H.parse_claims("## Result\n(no notebook written)\n"), [])

    def test_a_proof_keeps_every_line_whatever_its_header(self):
        """#455 r1s3 wrote `PROOF.` (a period): the proof landed in BEYOND, was clipped, and the referee failed it."""
        nb = ("## Claims\n### C1\nSTATEMENT: liminf >= 0.80\nSTATUS: PROVED (computer-assisted)\nTYPE: QUANT\n"
              "BEYOND: Richter's 0.352.\nPROOF.\nSetup. Let S = {3,5,7}.\nKEY STEP: the game value.\n"
              + "(2) The sequence is a game path. " * 80 + "\nTherefore the bound holds.\n"
              "### C2\n**STATEMENT:** a second claim\n**STATUS:** CONJECTURED\n**PROOF:** data only\n## Data\n")
        c1, c2 = H.parse_claims(nb)
        self.assertEqual(c1["beyond"], "Richter's 0.352.")
        self.assertIn("KEY STEP: the game value.", c1["proof"])      # an ALL-CAPS line inside a proof is not a field
        self.assertTrue(c1["proof"].endswith("Therefore the bound holds."))
        self.assertEqual((c2["statement"], c2["status"], c2["proof"]), ("a second claim", "CONJECTURED", "data only"))

    def test_status_needs_both_judges_and_a_new_verdict(self):
        st = H.engine_status
        self.assertEqual(st({"referee": {"valid": False}, "adversary": {"broken": False}}), "broken")
        self.assertEqual(st({"referee": {"valid": True}, "adversary": {"broken": True}}), "broken")
        self.assertEqual(st({"referee": {"valid": True}, "adversary": {"error": "over cap"}}), "unjudged")
        self.assertEqual(st({"referee": {"valid": True}, "adversary": {"broken": False}, "novelty": {"verdict": "new"}}),
                         "validated-new")
        self.assertEqual(st({"referee": {"valid": True}, "adversary": {"broken": False}, "novelty": {"verdict": "known"}}),
                         "valid-known")


class EngineRun(unittest.TestCase):
    def _call(self, frontier=FRONTIER, broken_for=None):
        def script(purpose, prompt, n):
            if purpose == "engine-frontier":
                return frontier
            if purpose == "engine-meta":
                return META
            broken = bool(broken_for and broken_for in prompt)
            return judge(purpose, valid=not broken, broken=broken)
        return FakeCall(script, cost=0.1)

    def test_two_rounds_validate_and_feed_forward(self):
        call = self._call(broken_for="0.6")
        sess = FakeSession(lambda label, prompt: notebook(("PROVED", "QUANT", "liminf >= 0.54" if label.startswith("r1") else "liminf >= 0.6"),
                                                          ("CONJECTURED", "OTHER", "U(x) = o(x)")))
        s = H.EngineSettings(sessions=2, rounds=2, total_budget=50)
        res = H.engine_run(call, sess, "PROBLEM", LEAN, s, workers=2)
        self.assertEqual(len(res["rounds"]), 2)
        self.assertEqual(len(sess.calls), 4)
        r2 = [p for label, p in sess.calls if label.startswith("r2")]
        self.assertTrue(all("NEXT-ROUND ASSIGNMENT" in p and "liminf >= 0.54 (validated)" in p for p in r2))
        statuses = {(c["session"], c["statement"]): (c.get("validation") or {}).get("status") for c in res["ledger"]}
        self.assertEqual(statuses[("r1s1", "liminf >= 0.54")], "validated-new")
        self.assertEqual(statuses[("r2s1", "liminf >= 0.6")], "broken")
        self.assertIsNone(statuses[("r1s1", "U(x) = o(x)")])           # a conjecture is not validated
        self.assertEqual(res["decision"]["commit"], "pos")
        self.assertIn("NEW (QUANT): liminf >= 0.54", res["guidance"])
        # novelty is judged only after both referees pass, and never for the broken claim
        self.assertEqual(len(call.prompts("engine-novelty")), 2)
        self.assertTrue(all("0.6" not in p.split("THE CLAIM:")[1] for p in call.prompts("engine-novelty")))
        # judges see the frontier and the claim, never the operator guidance (checked at the Harness level)
        self.assertIn("Richter 1976", call.prompts("engine-novelty")[0])
        report = H.engine_report(res, "test")
        self.assertLess(report.index("[validated-new]"), report.index("[broken]"))

    def test_budget_bounds_the_sessions(self):
        call = self._call()
        sess = FakeSession(lambda label, prompt: notebook(("PROVED", "QUANT", "x")), cost=3.0)
        s = H.EngineSettings(sessions=4, rounds=2, session_budget=3.0, total_budget=8.0)
        res = H.engine_run(call, sess, "PROBLEM", LEAN, s, workers=4)
        self.assertEqual(len(sess.calls), 1)                 # the reserve for judging leaves room for one session only
        self.assertLessEqual(res["spend"], 8.0 + 3.0)        # a call may overrun its own cap, never start past the total

    def test_later_rounds_size_themselves_from_actual_costs(self):
        """#455: sessions cost $1.2-2.0 against a $3 cap and judging $0.31 a claim, so a cap-based reserve ran 2 of round
        2's 4 assignments and dropped the two that aimed at the core."""
        meta4 = META.replace("2. Attack CORE", "2. Attack CORE by entropy").rstrip() + (
            "\n3. Attack CORE in the no-dip subclass; first step: the walk data.\n4. Distinct discriminants theorem.\n")

        def script(purpose, prompt, n):
            return FRONTIER if purpose == "engine-frontier" else meta4 if purpose == "engine-meta" else judge(purpose)
        sess = FakeSession(lambda label, prompt: notebook(("PROVED", "QUANT", f"claim {label}")), cost=1.0)
        res = H.engine_run(FakeCall(script, cost=0.1), sess, "PROBLEM", LEAN,
                           H.EngineSettings(sessions=4, rounds=2, session_budget=3.0, total_budget=24.0), workers=4)
        self.assertEqual([len(r["sessions"]) for r in res["rounds"]], [4, 4])
        self.assertTrue(any("no-dip subclass" in p for label, p in sess.calls if label == "r2s3"))

    def test_a_failed_session_and_a_failed_frontier(self):
        call = self._call()
        sess = FakeSession(lambda label, prompt: H.DiscoveryCallFailed("over cap", cost=0.5) if label == "r1s1"
                           else notebook(("REFUTED", "NEGATIVE", "every gap repeats twice")))
        res = H.engine_run(call, sess, "PROBLEM", LEAN, H.EngineSettings(sessions=2, rounds=1, total_budget=50), workers=2)
        self.assertEqual(res["rounds"][0]["sessions"][0]["error"], "over cap")
        refuted = [c for c in res["ledger"] if c["status"] == "REFUTED"]
        self.assertTrue(refuted and "is FALSE" in call.prompts("engine-referee")[0])
        bad = FakeCall(lambda purpose, prompt, n: H.DiscoveryCallFailed("down", cost=0.0))
        res = H.engine_run(bad, sess, "PROBLEM", LEAN, H.EngineSettings())
        self.assertEqual((res["error"], res["ledger"]), ("down", []))


class Literature(unittest.TestCase):
    QUERIES = "1. convex prime sequence gaps Richter\n2. primes nondecreasing gaps growth\n3. x\n4. arithmetic progressions of primes least prime"

    def _call(self, lit_verdict):
        def script(purpose, prompt, n):
            if purpose == "engine-frontier":
                return FRONTIER
            if purpose == "engine-litq":
                return self.QUERIES
            if purpose == "engine-novelty-lit":
                return "```json\n" + json.dumps({"verdict": lit_verdict, "cite": "Richter 1976" if lit_verdict != "new" else None,
                                                 "nearest": "Richter 1976 proves 0.352"}) + "\n```"
            return judge(purpose)
        return FakeCall(script, cost=0.1)

    def test_queries_search_and_a_verdict(self):
        seen = []

        def search(q):
            seen.append(q)
            return [{"title": "On convex sequences of primes", "year": "1976", "abstract": "We prove liminf > 0.352."}]
        rec = H.engine_literature_check(self._call("new"), search, H.EngineSettings(), "PROBLEM",
                                        {"statement": "liminf >= 0.54", "type": "QUANT", "beyond": "Richter"})
        self.assertEqual(len(seen), 3)                       # the one-word line is not a query
        self.assertEqual(rec["papers"], [{"title": "On convex sequences of primes", "year": "1976"}])  # deduplicated
        self.assertEqual(rec["verdict"], "new")

    def test_a_paper_that_has_it_demotes_the_claim(self):
        sess = FakeSession(lambda label, prompt: notebook(("PROVED", "QUANT", "liminf >= 0.54")))
        res = H.engine_run(self._call("known"), sess, "PROBLEM", LEAN, H.EngineSettings(sessions=1, rounds=1, total_budget=50),
                           search=lambda q: [{"title": "Richter", "year": "1976", "abstract": "0.352"}])
        v = res["ledger"][0]["validation"]
        self.assertEqual((v["status"], v["literature"]["cite"]), ("valid-known", "Richter 1976"))
        self.assertEqual(res["validated"], [])

    def test_a_failed_search_is_unchecked_never_new(self):
        def broken(q):
            raise OSError("network down")
        rec = H.engine_literature_check(self._call("new"), broken, H.EngineSettings(), "PROBLEM",
                                        {"statement": "x", "type": "QUANT"})
        self.assertEqual(rec["verdict"], "unchecked")
        self.assertEqual(len(rec["search_errors"]), 3)


class Stage(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        p = patch.object(H, "ROOT", self.root)
        p.start()
        self.addCleanup(p.stop)
        self.h = _stub(self.tmp.name)
        self.h.args.discover = "on"
        self.h.args.discover_mode = "engine"
        self.h.args.blackboard = "on"
        self.h.args.engine_sessions, self.h.args.engine_rounds = 2, 1
        self.h.save = lambda: None

    def test_stage_writes_its_outputs_and_the_board(self):
        call = FakeCall(lambda purpose, prompt, n: FRONTIER if purpose == "engine-frontier" else judge(purpose))
        sess = FakeSession(lambda label, prompt: notebook(("PROVED", "QUANT", "liminf >= 0.54")))
        self.h._discovery_caller = lambda: call
        self.h._engine_session_caller = lambda: sess
        self.h._engine_search = lambda: None
        keep = self.h.stage_discover()
        self.assertEqual(keep["mode"], "engine")
        self.assertEqual(len(keep["validated"]), 2)
        out = Path(self.h.run_dir) / "engine"
        self.assertTrue((out / "engine.json").exists() and (out / "IDEAS.md").exists())
        board = (self.root / "programs" / "erdos_99" / "BLACKBOARD.md").read_text()
        self.assertIn("NEW, refereed informally, not Lean-checked (QUANT): liminf >= 0.54", board)
        done = [e for e in self.h.log.events if e[1] == "done"]
        self.assertEqual(done[-1][2]["validated"], 2)
        self.assertEqual(self.h.stage_discover(), keep)      # once per run

    def test_a_benchmark_run_never_searches(self):
        self.h.args.benchmark = True
        self.assertIsNone(self.h._engine_search())
        self.h.args.benchmark = False
        self.assertTrue(callable(self.h._engine_search()))

    def test_operator_guidance_reaches_generators_not_judges(self):
        g = self.root / "atlas-data" / "research-guidance"
        g.mkdir(parents=True)
        (g / "99.md").write_text("Try the entropy angle.")
        self.h.problem["id"] = "99"
        for purpose in ("engine-frontier", "engine-session", "engine-meta"):
            self.assertIn("Try the entropy angle.", self.h._with_research_guidance(purpose, "P"))
        for purpose in ("engine-referee", "engine-adversary", "engine-novelty"):
            self.assertNotIn("Try the entropy angle.", self.h._with_research_guidance(purpose, "P"))


if __name__ == "__main__":
    unittest.main()
