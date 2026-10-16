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
SIGNIFICANCE: 1
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
SIGNIFICANCE: 2 (an expert would note it)
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

    def __call__(self, purpose, prompt, label, turns, budget, effort, files=None, **kw):
        with self.lock:
            self.calls.append((label, prompt))
            self.files = getattr(self, "files", {})
            self.files[label] = dict(files or {})
            self.kw = getattr(self, "kw", {})
            self.kw[label] = dict(kw)
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
        self.assertEqual([t["significance"] for t in f["targets"]], [1, None, 2])
        picks = H.engine_assignments(f, 4, 0.5)
        self.assertEqual([p["kind"] for p in picks], ["angle", "angle", "target", "target"])
        self.assertEqual([p["type"] for p in picks if p["kind"] == "target"], ["SPECIAL", "QUANT"])   # most significant first
        self.assertIn("ATTACK THE CORE", H.assignment_text(picks[0]))
        self.assertIn("PROVE THIS TARGET", H.assignment_text(picks[2]))
        many = H.engine_assignments(f, 7, 0.5)                      # more sessions than targets + angles: no repeats
        self.assertEqual(len(many), 5)

    def test_zero_sessions_assign_nothing(self):
        """A map-and-rate screen (`--engine-sessions 0`, step 3) must buy no session. The slices went negative and
        assigned one angle plus every target but the last."""
        f = H.parse_frontier(FRONTIER)
        self.assertEqual(H.engine_assignments(f, 0, 0.5), [])


class EngineCompleteFallback(unittest.TestCase):
    """Step 3's #20: an equivalence with an unproven statement, graded valid-restatement and REJECTED by both settles
    judges, was reported as the engine's complete proof of an open problem."""

    def _claim(self, settles=None):
        v = {"status": "valid-restatement", "novelty": {"verdict": "restatement", "significance": 0}}
        if settles is not None:
            v["settles"] = {"settles": settles, "answer": "true" if settles else None}
        return {"session": "r1s1", "id": "C2", "status": "PROVED", "statement": "f < c^n iff spread matching", "validation": v}

    def test_a_restatement_the_settles_judges_rejected_is_not_complete(self):
        self.assertIsNone(H.engine_complete({"ledger": [self._claim(settles=False)]}))

    def test_an_unchecked_restatement_still_falls_back(self):
        self.assertEqual(H.engine_complete({"ledger": [self._claim()]})["id"], "C2")

    def test_a_settled_claim_is_complete(self):
        self.assertEqual(H.engine_complete({"ledger": [self._claim(settles=True)]})["id"], "C2")


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

    def test_claims_anywhere_and_proof_sections_attached(self):
        """The #455 deep dive: C1 under ## Claims pointing at "Proof of C1 below", then ## Proof of C1, then C2-C4 under
        that section, with `STATEMENT (method barrier):` and `EVIDENCE/MECHANISM:` headers. One claim of four was read,
        with no proof, and the referee failed it."""
        nb = ("## Result\nx\n## Claims\n### C1\nSTATEMENT: theta < 3/4 suffices.\nSTATUS: PROVED\nTYPE: STRUCTURE\n"
              "PROOF: see Proof of C1 below.\n## Proof of C1\nStep 1. The stay count.\nStep 5. Siegel, once per field.\n"
              "### C2\nSTATEMENT (beyond 3/4): theta < 5/6 gives liminf >= 2.\nSTATUS: PROVED\nTYPE: QUANT\nPROOF. As in C1.\n"
              "### C3\nSTATEMENT (method barrier): 3/4 is the limit.\nSTATUS: CONJECTURED\nTYPE: NEGATIVE\n"
              "EVIDENCE/MECHANISM: the recursion's fixed point.\n## Data\n### D1\nnothing\n")
        cs = {c["id"]: c for c in H.parse_claims(nb)}
        self.assertEqual(sorted(cs), ["C1", "C2", "C3"])
        self.assertIn("Siegel, once per field", cs["C1"]["proof"])
        self.assertEqual(cs["C2"]["statement"], "theta < 5/6 gives liminf >= 2.")
        self.assertEqual((cs["C3"]["status"], cs["C3"]["proof"]), ("CONJECTURED", "the recursion's fixed point."))
        two = "## Claims\n### C2\nSTATEMENT: one claim\nSTATUS: PROVED\n### C2\nSTATEMENT: another claim\nSTATUS: PROVED\n"
        self.assertEqual(len(H.parse_claims(two)), 2)                     # one label, two different claims: both kept

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
        s = H.EngineSettings(sessions=2, rounds=2, total_budget=50, gap_rounds=0)   # rounds alone; the gap phase is tested in Dependencies
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
        # novelty is judged (by two judges) only after both referees pass, and never for the broken claim
        self.assertEqual(len(call.prompts("engine-novelty")), 4)
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

    def test_a_frontier_cut_off_by_its_cap_is_retried_once(self):
        """#1203: the map hit its cap mid-answer, the text was lost, and the whole engine stopped after $2.60."""
        budgets = []

        def script(purpose, prompt, n):
            if purpose == "engine-frontier":
                return H.DiscoveryCallFailed("error_max_budget_usd: over cap", cost=2.6) if n == 0 else FRONTIER
            return judge(purpose)

        class Rec(FakeCall):
            def __call__(self, purpose, prompt, effort, budget):
                budgets.append((purpose, budget))
                return super().__call__(purpose, prompt, effort, budget)
        sess = FakeSession(lambda label, prompt: notebook(("PROVED", "QUANT", "x")))
        res = H.engine_run(Rec(script), sess, "PROBLEM", LEAN, H.EngineSettings(sessions=1, rounds=1, total_budget=50))
        self.assertNotIn("error", res)
        self.assertEqual([b for p, b in budgets if p == "engine-frontier"], [8.0, 12.0])
        self.assertGreaterEqual(res["frontier"]["cost"], 2.6)

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


def rating(prompt, n):
    """T1 is a minor improvement, T2 a solid partial result, T3 the core restated; judge 2 doubts T2's novelty."""
    target = prompt.split("THE TARGET:")[1].split("Answer from everything")[0]   # the target only, not the rubric
    if "0.54" in target:
        v = {"verdict": "new", "significance": 1, "reach": "high"}
    elif "0.6" in target:
        v = {"verdict": "new", "significance": 2, "reach": "medium"}
    else:
        v = {"verdict": "restatement", "significance": 3, "reach": "low"}
    return "```json\n" + json.dumps({**v, "cite": None, "why": "w"}) + "\n```"


class ProbesAndMarathon(unittest.TestCase):
    """v6 (2026-10-07). Probes MEASURE reach: step 3's predicted reach rated 69 of 70 significant targets low, and the one
    significance-2 result came from an unrated angle. A marathon continues the deep dive's line over several legs, as
    openai/math gave each result hours of thinking."""

    PROBE_NB = ("## Claims\n### C1\nSTATEMENT: the k = 4 case\nSTATUS: PROVED\nTYPE: SPECIAL\nBEYOND: new.\nPROOF: Step one.\n"
                "## Routes\nROUTE: pigeonhole on residues | OUTCOME: partial | BARRIER: the large-prime range\n"
                "## Probe verdict\nPROGRESS: strong\nP_SUCCESS: 0.7\nNEXT: extend to k = 5\n")
    EMPTY_NB = "## Claims\n## Probe verdict\nPROGRESS: none\nP_SUCCESS: 0.05\nNEXT: nothing obvious\n"

    def test_the_parsers(self):
        v = H.parse_probe_verdict(self.PROBE_NB)
        self.assertEqual((v["progress"], v["p_success"]), ("strong", 0.7))
        self.assertIn("k = 5", v["next"])
        self.assertEqual(H.parse_routes(self.PROBE_NB), ["ROUTE: pigeonhole on residues | OUTCOME: partial | BARRIER: the large-prime range"])
        self.assertEqual(H.parse_probe_verdict("no verdict")["progress"], None)

    def test_measured_progress_orders_the_score(self):
        new2 = {"claims": [{"validation": {"status": "validated-new", "novelty": {"significance": 2}}}], "verdict": {}}
        routine = {"claims": [{"validation": {"status": "valid-routine"}}], "verdict": {}}
        strong = {"claims": [], "verdict": {"progress": "strong", "p_success": 0.6}}
        none = {"claims": [], "verdict": {"progress": "none", "p_success": 0.0}}
        scores = [H.probe_score(x) for x in (new2, routine, strong, none)]
        self.assertEqual(scores, sorted(scores, reverse=True))

    def _script(self):
        def script(purpose, prompt, n):
            if purpose == "engine-frontier":
                return FRONTIER
            if purpose == "engine-deep-plan":
                return DEEP_PLAN
            if purpose == "engine-meta":
                return META
            return judge(purpose)
        return script

    def test_probes_run_first_and_their_traction_decides_round_one(self):
        f = H.parse_frontier(FRONTIER)
        last = f["angles"][-1]["id"]                     # the probes find traction on the LAST angle in map order
        def nb(label, prompt):
            if label.startswith("p"):
                return self.PROBE_NB if f"({last})" in prompt else self.EMPTY_NB
            return notebook(("PROVED", "QUANT", f"claim {label}"))
        sess = FakeSession(nb)
        res = H.engine_run(FakeCall(self._script(), cost=0.1), sess, "PROBLEM", LEAN,
                           H.EngineSettings(sessions=2, rounds=1, total_budget=80, probe_items=4), workers=2)
        labels = [l for l, _ in sess.calls]
        self.assertEqual(sorted(l for l in labels if l.startswith("p")), ["p1", "p2", "p3", "p4"])
        self.assertTrue(all("PROBE. A short first attempt" in pr for l, pr in sess.calls if l.startswith("p")))
        r1 = [pr for l, pr in sess.calls if l.startswith("r1")]
        angle_session = next(pr for pr in r1 if "ATTACK THE CORE" in pr.split("YOUR TEAMMATES")[0])
        self.assertIn(f"({last})", angle_session.split("YOUR TEAMMATES")[0])   # measured, not map order
        self.assertTrue(any(x["score"] > 2 for x in res["probes"]))
        self.assertTrue(any(c.get("session") == next(x["label"] for x in res["probes"] if x["score"] > 2) for c in res["ledger"]))

    def test_with_no_sessions_it_is_a_map_and_probe_screen(self):
        sess = FakeSession(lambda label, prompt: self.EMPTY_NB)
        res = H.engine_run(FakeCall(self._script(), cost=0.1), sess, "PROBLEM", LEAN,
                           H.EngineSettings(sessions=0, rounds=1, total_budget=40, probe_items=3))
        self.assertEqual(sorted(l for l, _ in sess.calls), ["p1", "p2", "p3"])
        self.assertEqual(res["rounds"], [])

    def test_a_marathon_continues_the_deep_dive_with_its_routes_and_notebooks(self):
        deep_nb = notebook(("PROVED", "QUANT", "deep claim")) + "## Routes\nROUTE: max-plus | OUTCOME: failed | BARRIER: rank growth\n"
        def nb(label, prompt):
            if label == "deep":
                return deep_nb
            if label.startswith("marathon"):
                return notebook(("PROVED", "QUANT", f"leg claim {label}")) + f"## Routes\nROUTE: route of {label} | OUTCOME: partial | BARRIER: b\n"
            return notebook(("PROVED", "QUANT", f"claim {label}"))
        sess = FakeSession(nb)
        res = H.engine_run(FakeCall(self._script(), cost=0.1), sess, "PROBLEM", LEAN,
                           H.EngineSettings(sessions=1, rounds=1, total_budget=120, deep_budget=8.0, marathon_legs=2))
        labels = [l for l, _ in sess.calls]
        self.assertEqual([l for l in labels if l.startswith("marathon")], ["marathon-1", "marathon-2"])
        leg2 = dict(sess.calls)["marathon-2"]
        self.assertIn("leg 2 of 2", leg2)
        self.assertIn("max-plus", leg2)                  # the deep dive's routes
        self.assertIn("route of marathon-1", leg2)        # and leg 1's
        self.assertEqual(set(sess.files["marathon-2"]), {"prior/deep.md", "prior/leg-1.md"})
        self.assertEqual(len(res["marathon"]["legs"]), 2)
        self.assertTrue(any(c.get("session") == "marathon-2" for c in res["ledger"]))

    def test_an_empty_leg_ends_the_marathon(self):
        def nb(label, prompt):
            if label.startswith("marathon"):
                return "## Claims\n"
            return notebook(("PROVED", "QUANT", f"claim {label}"))
        sess = FakeSession(nb)
        res = H.engine_run(FakeCall(self._script(), cost=0.1), sess, "PROBLEM", LEAN,
                           H.EngineSettings(sessions=1, rounds=1, total_budget=120, deep_budget=8.0, marathon_legs=3))
        self.assertEqual([l for l, _ in sess.calls if l.startswith("marathon")], ["marathon-1"])
        self.assertIn("no route and no claim", res["marathon"]["stopped"])


class SelfAudit(unittest.TestCase):
    """openai/math's #3 trace ends in seven audit passes: the dependency chain, the hypotheses of every cited theorem,
    small examples, parameter order and circularity, repair and re-audit, and concerns it could not resolve stated
    plainly. Sessions now audit before they claim PROVED, and the judges decide the authors' concerns."""

    def test_audit_and_concerns_are_parsed(self):
        nb = ("## Claims\n### C1\nSTATEMENT: F(A,X,4) << X^(1/3-c)\nSTATUS: PROVED\nTYPE: QUANT\nPROOF: step 1. step 2.\n"
              "AUDIT: chain: L0 -> Key lemma -> count; cited Bloom-Sisask Thm 17, hypotheses checked\n"
              "CONCERNS: the truncation parameter may depend on the mesh\n## Routes\nROUTE: x | OUTCOME: failed | BARRIER: y\n")
        c = H.parse_claims(nb)[0]
        self.assertEqual(c["proof"], "step 1. step 2.")
        self.assertIn("Bloom-Sisask", c["audit"])
        self.assertIn("truncation", c["concerns"])

    def test_the_judges_see_unresolved_concerns_and_not_a_none(self):
        self.assertIn("decide each one", H.concerns_context({"concerns": "the mesh may be circular"}))
        for none in ("none", "None.", "n/a", "No unresolved concerns", ""):
            self.assertEqual(H.concerns_context({"concerns": none}), "", none)

    def test_the_prompts_carry_the_protocol(self):
        sp = " ".join(H.SESSION_PROMPT.split())
        for phrase in ("## Routes", "AUDIT before you mark any claim PROVED", "state its hypotheses", "CONCERNS:"):
            self.assertIn(phrase, sp)
        self.assertIn("state its hypotheses and check that each one holds", " ".join(H.CLAIM_REFEREE_PROMPT.split()))


class ReachFix(unittest.TestCase):
    """Step 3's screen found 1 OPEN target in 20 problems against 6 predicted. The map asked for targets a strong
    mathematician proves "in weeks" while the judges rated reach as the chance of a proof "in a day", so 69 of 70
    significant targets came out low; and the gate sorted by significance first, so #873's one target slot went to an
    unreachable significance-3 target over the reachable significance-2 one."""

    def test_a_reachable_significance_two_target_outranks_an_unreachable_three(self):
        f = {"targets": [{"id": "T1", "significance": 3}, {"id": "T2", "significance": 2}], "angles": []}
        ratings = {"T1": {"verdict": "new", "significance": 3, "reach": "low", "p_week": 0.05},
                   "T2": {"verdict": "new", "significance": 2, "reach": "medium", "p_week": 0.4}}
        self.assertEqual([x["id"] for x in H.engine_gate_targets(f, ratings, 2)["targets"]], ["T2", "T1"])

    def test_without_probabilities_the_reach_level_decides(self):
        self.assertGreater(H.target_value({"significance": 2, "reach": "medium"}), H.target_value({"significance": 3, "reach": "low"}))
        self.assertGreater(H.target_value({"significance": 2, "map_reach": "high"}), H.target_value({"significance": 2}))

    def test_the_rubric_uses_one_horizon(self):
        rubric = " ".join(H.TARGET_RATING_PROMPT.split())
        self.assertIn("ONE focused week", rubric)
        self.assertNotIn("a day of focused work", rubric)
        self.assertIn("STEPPING STONES", H.FRONTIER_PROMPT)
        self.assertIn("REACH:", H.FRONTIER_PROMPT)

    def test_the_map_s_reach_is_parsed(self):
        f = H.parse_frontier("=== TARGET T1\nTYPE: SPECIAL\nSTATEMENT: the k = 4 case\nSIGNIFICANCE: 2\nREACH: medium\n")
        self.assertEqual(f["targets"][0]["map_reach"], "medium")


class TargetRating(unittest.TestCase):
    """v4: the novelty judges rate every target BEFORE any work, and round 1 attacks only those rated new at the bar.
    v1-v3's 18 validated-new claims were all significance 1 while the maps had labelled 1-6 targets per problem at 2-3."""

    def _run(self, s, ck=None, rate=rating):
        def script(purpose, prompt, n):
            if purpose == "engine-frontier":
                return FRONTIER
            if purpose == "engine-target-rate":
                return rate(prompt, n)
            if purpose == "engine-meta":
                return META
            return judge(purpose)
        call = FakeCall(script, cost=0.1)
        sess = FakeSession(lambda label, prompt: notebook(("PROVED", "QUANT", f"claim {label}")))
        return H.engine_run(call, sess, "PROBLEM", LEAN, s, workers=2, checkpoint=ck), call, sess

    def test_round_one_attacks_only_targets_rated_at_the_bar(self):
        res, call, sess = self._run(H.EngineSettings(sessions=3, rounds=2, total_budget=60, min_target_sig=2))
        self.assertEqual(len(call.prompts("engine-target-rate")), 6)          # 3 targets x 2 judges
        r1 = [p for label, p in sess.calls if label.startswith("r1")]
        targets = [p for p in r1 if "PROVE THIS TARGET" in p.split("YOUR TEAMMATES")[0]]
        self.assertEqual(len(targets), 1)
        self.assertIn("(T2, type QUANT, significance 2 of 3)", targets[0])
        self.assertEqual(sum("ATTACK THE CORE" in p.split("YOUR TEAMMATES")[0] for p in r1), 2)   # angles fill the rest
        self.assertEqual(res["ratings"]["T1"]["significance"], 1)
        self.assertEqual(res["ratings"]["T3"]["verdict"], "restatement")
        self.assertIn("TARGETS AS THE JUDGES RATED THEM", call.prompts("engine-meta")[0])
        self.assertIn("rated new, significance 2 if proved, reach medium", H.engine_report(res, "t"))

    def test_off_by_default_and_never_rated_twice(self):
        res, call, sess = self._run(H.EngineSettings(sessions=2, rounds=1, total_budget=30))
        self.assertEqual(call.prompts("engine-target-rate"), [])
        self.assertIsNone(res["ratings"])
        # a real checkpoint holds an entry for every target: a rating, or "not rated (budget)"
        ck = {"frontier": {**H.parse_frontier(FRONTIER), "text": FRONTIER},
              "ratings": {"T1": {"verdict": "new", "significance": 3, "reach": "high"},
                          "T2": {"verdict": "routine", "significance": 1, "reach": "high"},
                          "T3": {"error": "not rated (budget)", "cost": 0.0}}}
        res, call, sess = self._run(H.EngineSettings(sessions=2, rounds=1, total_budget=30, min_target_sig=2), ck)
        self.assertEqual(call.prompts("engine-target-rate"), [])               # a resume reuses the checkpointed ratings
        self.assertTrue(any("(T1, type QUANT, significance 3 of 3)" in p for label, p in sess.calls))

    def test_a_map_and_rate_screen_runs_no_session(self):
        """`--engine-sessions 0`: the frontier map and the judges' ratings only, to choose where a full run is worth buying."""
        res, call, sess = self._run(H.EngineSettings(sessions=0, rounds=2, total_budget=30, min_target_sig=2))
        self.assertEqual(sess.calls, [])
        self.assertEqual(len(call.prompts("engine-target-rate")), 6)
        self.assertEqual(res["rounds"], [])
        self.assertEqual(call.prompts("engine-meta"), [])
        self.assertEqual(res["ratings"]["T2"]["significance"], 2)

    def test_the_conservative_reading_and_an_empty_gate(self):
        def split(prompt, n):                                                  # one judge says new 3, the other routine 1
            v = {"verdict": "new", "significance": 3} if n % 2 else {"verdict": "routine", "significance": 1}
            return "```json\n" + json.dumps({**v, "reach": "high", "cite": None, "why": "w"}) + "\n```"
        res, call, sess = self._run(H.EngineSettings(sessions=2, rounds=1, total_budget=30, min_target_sig=2), rate=split)
        self.assertTrue(all(r["verdict"] == "routine" for r in res["ratings"].values()))
        self.assertTrue(all("ATTACK THE CORE" in p.split("YOUR TEAMMATES")[0] for label, p in sess.calls))



DEEP_PLAN = """=== GOAL
Prove liminf q_n/n^2 >= 1 + delta (beyond the profinite cap), significance 2.
=== WHY THIS LINE
The discriminant walk couples size with residues.
=== PLAN
1. [established] liminf >= 0.54. 2. Couple the walk with least split primes.
=== PITFALLS
The r1s2 exponent swap.
"""


def claim(cid, st, proof, status="PROVED", vstat=None, session="deep", **kw):
    c = {"id": cid, "session": session, "status": status, "type": "QUANT", "statement": st, "proof": proof, "beyond": ""}
    if vstat:
        c["validation"] = {"status": vstat}
    c.update(kw)
    return c


def verdict(purpose, ok=True, nov=("routine", 0)):
    if purpose == "engine-referee":
        return "```json\n" + json.dumps({"valid": ok, "first_error": None if ok else "the lemmas C1 and C5 are never stated", "fixable": True}) + "\n```"
    if purpose == "engine-adversary":
        return "```json\n" + json.dumps({"broken": not ok, "how": None if ok else "C1(i) is used with two incompatible signs",
                                         "severity": "none" if ok else "fixable"}) + "\n```"
    return "```json\n" + json.dumps({"verdict": nov[0], "cite": None, "significance": nov[1], "why": "w"}) + "\n```"


class Dependencies(unittest.TestCase):
    """v5: a claim counts only when every lemma it cites is valid. A gap-closing version of a lemma lifts what rests on it.
    #152's deep dive wrote a proof of the whole problem (C9) from C1, C5, C6 and C7. Its referee never saw them, and the
    one real error, in C5, never got a session."""

    def test_citations(self):
        c = claim("C9", "main", "By C5(b) and C7, then C5 again; C12 is not a claim; C9 is itself.")
        self.assertEqual(H.claim_citations(c, {"C5", "C7", "C9"}), ["C5", "C7"])
        g = claim("C5g1", "x", "fixes C5 with C1", supersedes="C5")
        self.assertEqual(H.claim_citations(g, {"C1", "C5"}), ["C1"])
        c7 = claim("C7", "the interior case", "C6 and C5(b) give it. ∎\nREMAINING CASE (now CLOSED by C9): the end pair.")
        self.assertEqual(H.claim_citations(c7, {"C5", "C6", "C7", "C9"}), ["C6", "C5"])   # commentary after the end mark

    def test_a_claim_waits_for_its_lemmas_and_a_fixed_lemma_lifts_it(self):
        c5 = claim("C5", "lemma", "a sign identity", vstat="broken")
        c7 = claim("C7", "middle", "by C5", vstat="valid-routine")
        c9 = claim("C9", "main", "from C7 and C5", vstat="validated-new")
        other = claim("C5", "unrelated", "x", vstat="broken", session="r1s1")      # same id, another notebook
        led = [c5, c7, c9, other]
        H.engine_resolve(led)
        self.assertEqual((c9["validation"]["status"], c9["validation"]["own_status"]), ("conditional", "validated-new"))
        self.assertEqual(c9["validation"]["pending"], ["deep/C7", "deep/C5"])
        self.assertEqual(c7["validation"]["status"], "conditional")
        led.append(claim("C5g1", "lemma", "fixed", vstat="valid-routine", supersedes="C5"))
        H.engine_resolve(led)
        self.assertEqual((c7["validation"]["status"], c9["validation"]["status"]), ("valid-routine", "validated-new"))
        self.assertNotIn("pending", c9["validation"])
        led[-1] = claim("C5g1", "C5 is false", "a counterexample", status="REFUTED", vstat="valid-routine", refutes="C5")
        H.engine_resolve(led)
        self.assertEqual(c9["validation"]["status"], "conditional")             # a refutation never stands in for the lemma

    def test_a_complete_chain_is_reported_with_every_lemma(self):
        """engine_complete: an unconditional valid restatement is the engine's answer; its text is the whole chain."""
        c1 = claim("C1", "the identity", "algebra", vstat="valid-routine")
        c7 = claim("C7", "the interior case", "from C1", vstat="broken")
        g = claim("C7g1", "the interior case, for all n", "fixed, from C1", vstat="valid-routine", supersedes="C7")
        c9 = claim("C9", "the whole problem", "from C7 and C1", vstat="valid-restatement")
        res = {"ledger": [c1, c7, g, c9]}
        H.engine_resolve(res["ledger"])
        self.assertIs(H.engine_complete(res), c9)
        text = H.engine_chain_text(c9, res["ledger"])
        self.assertLess(text.index("LEMMA C1"), text.index("LEMMA C7 (its corrected version C7g1)"))
        self.assertLess(text.index("C7g1"), text.index("THEOREM C9"))
        self.assertNotIn("STATEMENT: the interior case\n", text)          # the broken original gives way to its fix
        c9["validation"]["status"] = "conditional"
        self.assertIsNone(H.engine_complete(res))

    def test_a_settled_claim_is_complete_whatever_its_novelty_verdict(self):
        """#204: the engine proved the full answer twice and its judges, recalling the 2025 resolution, said "known"."""
        def script(purpose, prompt, n):
            if purpose == "engine-settles":
                full = "cannot both hold" in prompt.split("THE CLAIM:")[1]
                return "```json\n" + json.dumps({"settles": full, "answer": "false" if full else None, "why": "w"}) + "\n```"
            return judge(purpose)
        call = FakeCall(script)
        c = claim("C1", "For every n the covering and the disjointness rule cannot both hold.", "pigeonhole", vstat="valid-known")
        v = H.engine_settles(call, H.EngineSettings(), "P", LEAN, c, H._DiscoverySpend(10))
        self.assertEqual((v["settles"], v["answer"]), (True, "false"))
        c["validation"]["settles"] = v
        side = claim("C2", "the case of three primes", "x", vstat="valid-restatement")
        self.assertIs(H.engine_complete({"ledger": [side, c]}), c)                # settled beats an unchecked restatement
        split = H.engine_settles(FakeCall(lambda p, pr, n: "```json\n" + json.dumps(
            {"settles": True, "answer": "true" if n == 0 else "false"}) + "\n```"), H.EngineSettings(), "P", LEAN, c,
            H._DiscoverySpend(10))
        self.assertFalse(split["settles"])                                       # the two judges must agree on the answer

    def test_recognition_of_the_real_problem_is_recorded(self):
        res = {"frontier": {"text": "FALSE. I believe this is Erdős Problem #204 (Erdős–Graham 1980); see erdosproblems.com/204."},
               "ledger": [{"validation": {"novelty": {"cite": "resolves Erdos #204", "why": "x"}}}]}
        self.assertEqual(H.engine_recognized(res), ["204"])

    def test_circular_citations_are_conditional(self):
        a = claim("C1", "a", "by C2", vstat="valid-routine")
        b = claim("C2", "b", "by C1", vstat="valid-routine")
        H.engine_resolve([a, b])
        self.assertEqual((a["validation"]["status"], b["validation"]["status"]), ("conditional", "conditional"))

    def test_the_judges_see_the_cited_lemmas(self):
        call = FakeCall(lambda purpose, prompt, n: judge(purpose))
        v = H.engine_validate(call, H.EngineSettings(), "P", "K", claim("C9", "main", "from C5"), H._DiscoverySpend(10),
                              lemmas=[{"id": "C5", "statement": "the sign identity"}])
        for purpose in ("engine-referee", "engine-adversary"):
            self.assertIn("[C5] the sign identity", call.prompts(purpose)[0])
        self.assertEqual(v["lemmas"], ["C5"])

    def test_a_chosen_claims_lemma_is_judged_too(self):
        call = FakeCall(lambda purpose, prompt, n: FRONTIER if purpose == "engine-frontier" else judge(purpose))
        sess = FakeSession(lambda label, prompt: notebook(("PROVED", "REDUCTION", "the main claim, via C3"),
                                                          ("PROVED", "QUANT", "a side claim"), ("PROVED", "OTHER", "the lemma")))
        res = H.engine_run(call, sess, "PROBLEM", LEAN, H.EngineSettings(sessions=1, rounds=1, total_budget=50, validate_max=1))
        judged = {c["id"] for c in res["ledger"] if c.get("validation")}
        self.assertEqual(judged, {"C1", "C3"})                                 # C3 ranks last, but C1 rests on it
        self.assertEqual(res["gaps"]["targets"], [])                           # on by default, with nothing broken to close
        self.assertFalse(any(label.startswith("gap-") for label, p in sess.calls))

    def _gap_ledger(self):
        c1 = claim("C1", "the split identity", "algebra", vstat="valid-routine")
        c5 = claim("C5", "the sign lemma", "uses C1 twice")
        c5["validation"] = {"referee": {"valid": True}, "adversary": {"broken": True, "how": "C1(i) is used with two incompatible signs"},
                            "status": "broken"}
        c9 = claim("C9", "the whole problem", "from C1 and C5")
        c9["validation"] = {"referee": {"valid": False, "first_error": "the lemmas C1 and C5 are never stated"},
                            "adversary": {"broken": False}, "status": "broken"}
        return c1, c5, c9

    def _gap_call(self):
        def script(purpose, prompt, n):
            if purpose == "engine-target-rate":
                big = "the whole problem" in prompt.split("THE TARGET:")[1]
                return "```json\n" + json.dumps({"verdict": "restatement" if big else "new", "significance": 3 if big else 1,
                                                 "reach": "medium", "cite": None, "why": "w"}) + "\n```"
            text = prompt.split("THE CLAIM:")[1]
            if "the whole problem" in text:
                return verdict(purpose, ok="LEMMAS THIS PROOF CITES" in prompt, nov=("restatement", 3))
            if "the sign lemma" in text and "repaired" not in text:
                return verdict(purpose, ok=purpose != "engine-adversary")
            return verdict(purpose)
        return FakeCall(script, cost=0.05)

    def test_the_gap_phase_closes_the_lemma_under_a_high_value_claim(self):
        c1, c5, c9 = self._gap_ledger()
        ledger = [c1, c5, c9]
        sess = FakeSession(lambda label, prompt: "## Claims\n### C1\nSTATEMENT: the sign lemma, repaired\nSTATUS: PROVED\n"
                                                 "TYPE: QUANT\nBEYOND: x\nPROOF: complete, from C1 with one sign throughout.\n")
        res = H.engine_gap_phase(self._gap_call(), sess, H.EngineSettings(gap_rounds=2, total_budget=50), "P", LEAN, "FB", "",
                                 "K", ledger, H._DiscoverySpend(50))
        self.assertEqual([label for label, p in sess.calls], ["gap-deep-C5-1"])
        prompt = sess.calls[0][1]
        self.assertIn("two incompatible signs", prompt)
        self.assertIn("[C1] the split identity", prompt)
        self.assertIn("the sign lemma", sess.files["gap-deep-C5-1"]["prior/notebook.md"])
        g = next(c for c in ledger if c["id"] == "C5g1")
        self.assertEqual((g["supersedes"], g["validation"]["status"]), ("C5", "valid-routine"))
        self.assertEqual(c9["validation"]["own_status"], "valid-restatement")   # re-judged with its lemmas in view
        self.assertEqual(c9["validation"]["status"], "valid-restatement")       # and no longer waiting on C5
        self.assertEqual(res["high"], ["deep/C9"])
        self.assertEqual(res["targets"], ["deep/C5"])

    def test_a_refuting_gap_session_leaves_the_claim_conditional(self):
        c1, c5, c9 = self._gap_ledger()
        ledger = [c1, c5, c9]
        sess = FakeSession(lambda label, prompt: "### C1\nSTATEMENT: the sign lemma fails at n = 5\nSTATUS: REFUTED\n"
                                                 "TYPE: NEGATIVE\nBEYOND: x\nPROOF: n = 5 breaks it.\n")
        H.engine_gap_phase(self._gap_call(), sess, H.EngineSettings(gap_rounds=3, total_budget=50), "P", LEAN, "FB", "",
                           "K", ledger, H._DiscoverySpend(50))
        self.assertEqual(len(sess.calls), 1)                                   # a refutation ends the rounds
        self.assertEqual(c9["validation"]["status"], "conditional")
        self.assertEqual(next(c for c in ledger if c["id"] == "C5g1").get("refutes"), "C5")


class DeepDive(unittest.TestCase):
    def test_one_long_session_on_the_chosen_line_with_the_notebooks(self):
        def script(purpose, prompt, n):
            if purpose == "engine-frontier":
                return FRONTIER
            if purpose == "engine-deep-plan":
                return DEEP_PLAN
            return judge(purpose)
        call = FakeCall(script, cost=0.1)
        sess = FakeSession(lambda label, prompt: notebook(("PROVED", "QUANT", f"claim from {label}")))
        res = H.engine_run(call, sess, "PROBLEM", LEAN, H.EngineSettings(sessions=2, rounds=1, total_budget=50,
                                                                         deep_budget=8.0), workers=2)
        labels = [label for label, p in sess.calls]
        self.assertEqual(labels[-1], "deep")
        deep_prompt = dict(sess.calls)["deep"]
        self.assertIn("DEEP DIVE", deep_prompt)
        self.assertIn("beyond the profinite cap", deep_prompt)
        self.assertEqual(sorted(sess.files["deep"]), ["prior/r1s1.md", "prior/r1s2.md"])
        self.assertIn("claim from r1s1", sess.files["deep"]["prior/r1s1.md"])
        self.assertEqual(res["deep"]["validated"], 1)
        self.assertIn("deep", {c["session"] for c in res["validated"]})
        self.assertTrue(all("_sessions" not in r for r in res["rounds"]))      # notebooks are not copied into engine.json

    def test_a_plan_cut_off_by_its_cap_is_retried_once(self):
        """#152's hard step: the deep dive's plan spent $2.62 against its $2 cap, wrote nothing, and the deep dive never
        ran. The plan, like the map, now gets one retry at 1.5x its cap."""
        budgets = []

        def script(purpose, prompt, n):
            if purpose == "engine-frontier":
                return FRONTIER
            if purpose == "engine-deep-plan":
                return H.DiscoveryCallFailed("error_max_budget_usd: over cap", cost=2.62) if n == 0 else DEEP_PLAN
            return judge(purpose)

        class Rec(FakeCall):
            def __call__(self, purpose, prompt, effort, budget):
                budgets.append((purpose, budget))
                return super().__call__(purpose, prompt, effort, budget)
        sess = FakeSession(lambda label, prompt: notebook(("PROVED", "QUANT", f"claim from {label}")))
        res = H.engine_run(Rec(script), sess, "PROBLEM", LEAN, H.EngineSettings(sessions=1, rounds=1, total_budget=50,
                                                                              deep_budget=8.0))
        self.assertEqual([b for p, b in budgets if p == "engine-deep-plan"], [2.0, 3.0])
        self.assertIn("deep", [label for label, p in sess.calls])
        self.assertNotIn("error", res["deep"])

    def test_a_deep_dive_that_failed_at_its_plan_is_retried_on_resume(self):
        """#152's hard step: the checkpoint kept the plan's cut-off error as the deep dive's result, so a resume skipped it."""
        def script(purpose, prompt, n):
            return FRONTIER if purpose == "engine-frontier" else DEEP_PLAN if purpose == "engine-deep-plan" else judge(purpose)
        sess = FakeSession(lambda label, prompt: notebook(("PROVED", "QUANT", f"claim from {label}")))
        s = H.EngineSettings(sessions=1, rounds=1, total_budget=50, deep_budget=8.0)
        first = H.engine_run(FakeCall(script, cost=0.1), sess, "PROBLEM", LEAN, H.EngineSettings(sessions=1, rounds=1, total_budget=50))
        ck = {"frontier": first["frontier"], "rounds": [{**r, "_sessions": []} for r in first["rounds"]], "meta": None, "next": [],
              "deep": {"plan_cost": 2.62, "error": "claude -p returned an error result (engine-deep-plan): error_max_budget_usd:"}}
        res = H.engine_run(FakeCall(script, cost=0.1), sess, "PROBLEM", LEAN, s, checkpoint=ck)
        self.assertIn("deep", [label for label, p in sess.calls])
        self.assertNotIn("error", res["deep"])
        done = {"plan_cost": 1.0, "goal": "g", "error": "the session failed", "cost": 3.0}
        sess2 = FakeSession(lambda label, prompt: notebook(("PROVED", "QUANT", "x")))
        H.engine_run(FakeCall(script, cost=0.1), sess2, "PROBLEM", LEAN, s, checkpoint={**ck, "deep": done})
        self.assertNotIn("deep", [label for label, p in sess2.calls])        # a session that ran and failed is final

    def test_the_meta_review_gets_the_same_retry(self):
        budgets = []

        def script(purpose, prompt, n):
            if purpose == "engine-frontier":
                return FRONTIER
            if purpose == "engine-meta":
                return H.DiscoveryCallFailed("error_max_budget_usd: over cap", cost=2.1) if n == 0 else META
            return judge(purpose)

        class Rec(FakeCall):
            def __call__(self, purpose, prompt, effort, budget):
                budgets.append((purpose, budget))
                return super().__call__(purpose, prompt, effort, budget)
        sess = FakeSession(lambda label, prompt: notebook(("PROVED", "QUANT", f"claim {label}")))
        res = H.engine_run(Rec(script), sess, "PROBLEM", LEAN, H.EngineSettings(sessions=2, rounds=2, total_budget=60), workers=2)
        self.assertEqual([b for p, b in budgets if p == "engine-meta"], [2.0, 3.0])
        self.assertEqual(len(res["rounds"]), 2)

    def test_off_by_default(self):
        call = FakeCall(lambda purpose, prompt, n: FRONTIER if purpose == "engine-frontier" else judge(purpose))
        sess = FakeSession(lambda label, prompt: notebook(("PROVED", "QUANT", "x")))
        res = H.engine_run(call, sess, "PROBLEM", LEAN, H.EngineSettings(sessions=1, rounds=1, total_budget=50))
        self.assertIsNone(res["deep"])
        self.assertNotIn("deep", [label for label, p in sess.calls])


class SessionLegs(unittest.TestCase):
    """v6 (2026-10-07): a session that stops with budget left and a route under ## Next goes back into its own sandbox.
    82% of 90 round sessions on disk stopped under 60% of their $3 cap, and 14 of 18 deep dives did too, although the
    deep dive's prompt already said not to stop at the first result: a session ends when its first route ends."""

    @staticmethod
    def nb(route, claim="liminf >= 0.54"):
        return notebook(("PROVED", "QUANT", claim)) + f"## Next\nNEXT: {route}\n"

    class Legs:
        """A fake session that knows which leg it is on, and records each leg's budget and notebook handling."""
        def __init__(self, script, cost=1.0):
            self.script, self.cost, self.calls, self.lock = script, cost, [], threading.Lock()

        def __call__(self, purpose, prompt, label, turns, budget, effort, files=None, keep_notebook=False):
            with self.lock:
                self.calls.append({"label": label, "prompt": prompt, "budget": budget, "keep": keep_notebook})
                k = sum(1 for c in self.calls if c["label"] == label)
            return f"reply {k}", self.script(label, k), self.cost

    def run_legs(self, sess, s, budget=3.0, spend=None, slot=None):
        return H.engine_session_legs(sess, s, spend or H._DiscoverySpend(50), "engine-session", "r1s1", "FIRST",
                                     lambda leg, route: f"CONT {leg}: {route}", 80, budget, "high", slot=slot)

    def test_the_next_route_is_read_from_the_notebook(self):
        self.assertEqual(H.parse_next_route(self.nb("prove the k=3 case first")), "prove the k=3 case first")
        for none in ("NONE", "**NONE**", "NONE (the assignment is proved)", "NONE - nothing left"):
            self.assertIsNone(H.parse_next_route(self.nb(none)), none)
        self.assertEqual(H.parse_next_route(self.nb("none of the logged routes; try the dual")),
                         "none of the logged routes; try the dual")
        self.assertIn("Choose the most promising route", H.parse_next_route(notebook(("PROVED", "QUANT", "x"))))
        self.assertIn("## Next\nNEXT:", H.SESSION_PROMPT)
        self.assertIn("Write NEXT: NONE only when", H.SESSION_PROMPT)

    def test_a_session_goes_back_until_it_writes_none(self):
        sess = self.Legs(lambda label, k: self.nb("the k=3 case" if k == 1 else "NONE"))
        reply, nb, cost, legs = self.run_legs(sess, H.EngineSettings(session_legs=4))
        self.assertEqual((legs, cost, reply), (2, 2.0, "reply 2"))
        self.assertEqual([c["keep"] for c in sess.calls], [False, True])       # leg 2 keeps leg 1's notebook
        self.assertEqual(sess.calls[1]["budget"], 2.0)                          # the rest of its OWN budget, no more
        self.assertEqual(sess.calls[1]["prompt"], "CONT 2: the k=3 case")

    def test_the_leg_cap_the_budget_and_the_engine_total_each_stop_it(self):
        always = lambda label, k: self.nb(f"route {k + 1}")
        self.assertEqual(self.run_legs(self.Legs(always), H.EngineSettings(session_legs=2))[3], 2)
        # $3 budget, $1 a leg: after leg 3 nothing is left, so a fourth never starts
        self.assertEqual(self.run_legs(self.Legs(always), H.EngineSettings(session_legs=9))[3], 3)
        # $0.50 left after leg 1 is under leg_min_budget
        self.assertEqual(self.run_legs(self.Legs(always, cost=2.5), H.EngineSettings(session_legs=9))[3], 1)
        # the engine's total: $1 spent of a $2.5 cap, and a $2 continuation would pass it
        self.assertEqual(self.run_legs(self.Legs(always), H.EngineSettings(session_legs=9), spend=H._DiscoverySpend(2.5))[3], 1)

    def test_one_leg_by_default(self):
        sess = self.Legs(lambda label, k: self.nb("another route"))
        self.assertEqual(self.run_legs(sess, H.EngineSettings())[3], 1)
        self.assertEqual(len(sess.calls), 1)

    def test_a_resume_continues_from_the_last_finished_leg(self):
        slot = {"legs": 1, "reply": "r", "notebook": self.nb("route X"), "cost": 1.0}
        sess = self.Legs(lambda label, k: self.nb("NONE"))
        _, nb, cost, legs = self.run_legs(sess, H.EngineSettings(session_legs=3), slot=slot)
        self.assertEqual((legs, cost), (2, 2.0))
        self.assertEqual([(c["keep"], c["prompt"]) for c in sess.calls], [(True, "CONT 2: route X")])  # leg 1 not re-bought
        self.assertEqual(slot["legs"], 2)

    def test_round_sessions_and_the_deep_dive_continue_in_engine_run(self):
        def script(purpose, prompt, n):
            return FRONTIER if purpose == "engine-frontier" else DEEP_PLAN if purpose == "engine-deep-plan" else judge(purpose)
        sess = self.Legs(lambda label, k: self.nb("NONE" if k == 2 else "push to 0.6", claim=f"claim {label} {k}"))
        res = H.engine_run(FakeCall(script, cost=0.1), sess, "PROBLEM", LEAN,
                           H.EngineSettings(sessions=2, rounds=1, total_budget=60, deep_budget=6.0, session_legs=3), workers=2)
        self.assertEqual([x["legs"] for x in res["rounds"][0]["sessions"]], [2, 2])
        self.assertEqual([x["cost"] for x in res["rounds"][0]["sessions"]], [2.0, 2.0])
        self.assertEqual((res["deep"]["legs"], res["deep"]["cost"]), (2, 2.0))
        cont = [c for c in sess.calls if c["keep"]]
        self.assertEqual(sorted(c["label"] for c in cont), ["deep", "r1s1", "r1s2"])
        r1 = next(c["prompt"] for c in cont if c["label"] == "r1s1")
        self.assertIn("CONTINUATION, leg 2 of at most 3", r1)
        self.assertIn("push to 0.6", r1)
        self.assertIn("YOUR ASSIGNMENT:", r1)
        deep = next(c["prompt"] for c in cont if c["label"] == "deep")
        self.assertIn("DEEP DIVE", deep.split("YOUR ASSIGNMENT:")[-1])           # the deep dive keeps its plan
        self.assertIn("claim r1s1 2", {c["statement"] for c in res["ledger"]})   # the last leg's notebook is judged

    def test_the_deep_dive_plan_is_not_bought_twice(self):
        def script(purpose, prompt, n):
            return FRONTIER if purpose == "engine-frontier" else DEEP_PLAN if purpose == "engine-deep-plan" else judge(purpose)
        sess = self.Legs(lambda label, k: self.nb("NONE"))
        first = H.engine_run(FakeCall(script, cost=0.1), sess, "PROBLEM", LEAN,
                             H.EngineSettings(sessions=1, rounds=1, total_budget=50))
        ck = {"frontier": first["frontier"], "rounds": [{**r, "_sessions": []} for r in first["rounds"]], "meta": None,
              "next": [], "deep_legs": {"plan_text": "GOAL:\nthe kept plan", "plan_cost": 1.0, "goal": "the kept plan",
                                        "legs": 1, "notebook": self.nb("route Y"), "cost": 1.0, "reply": "r"}}
        call = FakeCall(script, cost=0.1)
        sess2 = self.Legs(lambda label, k: self.nb("NONE"))
        res = H.engine_run(call, sess2, "PROBLEM", LEAN, H.EngineSettings(sessions=1, rounds=1, total_budget=50,
                                                                          deep_budget=6.0, session_legs=2), checkpoint=ck)
        self.assertEqual(call.prompts("engine-deep-plan"), [])
        self.assertEqual([(c["label"], c["keep"]) for c in sess2.calls], [("deep", True)])
        self.assertEqual((res["deep"]["legs"], res["deep"]["goal"]), (2, "the kept plan"))
        self.assertNotIn("deep_legs", ck)

    def test_the_session_caller_keeps_a_continuation_notebook(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        p = patch.object(H, "ROOT", Path(tmp.name))
        p.start()
        self.addCleanup(p.stop)
        h = _stub(tmp.name)
        seen = []

        class Backend:
            last_meta = {"cost_usd": 0.5, "turns": 3}

            def complete_explore(self, purpose, prompt, sb, turns, budget=None, effort=None, system_prompt=None):
                seen.append((sb / "NOTEBOOK.md").read_text())
                (sb / "NOTEBOOK.md").write_text(seen[-1] + "leg\n")
                return "done"
        h.llm = Backend()
        session = h._engine_session_caller()
        session("engine-session", "P1", "r1s1", 10, 3.0, "high")
        _, nb, _ = session("engine-session", "P2", "r1s1", 10, 2.0, "high", keep_notebook=True)
        self.assertEqual(seen, ["## Result\n(not yet)\n", "## Result\n(not yet)\nleg\n"])
        self.assertEqual(nb, "## Result\n(not yet)\nleg\nleg\n")
        reqs = [e for e in h.log.events if e[0] == "llm" and e[1] == "request"]
        self.assertEqual([bool(e[2].get("continuation")) for e in reqs], [False, True])


class InfraVerdicts(unittest.TestCase):
    """2026-10-07: the CLI's own limit wording ("You've hit your session limit · resets 4:50pm", "You've hit your weekly
    limit") did not match HARD_RE, so a limit inside the engine read as an ordinary failed call. Judges recorded
    "unjudged" verdicts, a resume kept them, and #273's probe claims and #570's step-2 deep dive were never judged."""

    LIMIT = "claude -p returned an error result (engine-referee): success: You've hit your session limit · resets 4:50pm (America/Toronto)"
    NB = ("## Claims\n### C1\nSTATEMENT: the k = 4 case\nSTATUS: PROVED\nTYPE: SPECIAL\nBEYOND: new.\nPROOF: Step one.\n"
          "## Probe verdict\nPROGRESS: partial\nP_SUCCESS: 0.2\nNEXT: k = 5\n")

    def _script(self, fail_referee=False):
        def script(purpose, prompt, n):
            if purpose == "engine-frontier":
                return FRONTIER
            if fail_referee and purpose == "engine-referee":
                return RuntimeError(self.LIMIT)
            return judge(purpose)
        return script

    def test_the_cli_limit_wording_is_hard(self):
        for msg in (self.LIMIT, "You've hit your weekly limit", "You've hit your usage limit"):
            self.assertIsNotNone(H.ClaudeCliBackend.HARD_RE.search(msg), msg)
        self.assertIsNone(H.ClaudeCliBackend.HARD_RE.search("rate limit exceeded, retry"))   # transient: retried

    def test_a_limit_at_a_judge_stops_the_run_instead_of_becoming_a_verdict(self):
        sess = FakeSession(lambda label, prompt: self.NB)
        ck = {}
        with self.assertRaisesRegex(RuntimeError, "session limit"):
            H.engine_run(FakeCall(self._script(fail_referee=True)), sess, "PROBLEM", LEAN,
                         H.EngineSettings(sessions=0, rounds=1, total_budget=40, probe_items=2), checkpoint=ck,
                         save=lambda c: None)
        self.assertFalse(any((c.get("validation") or {}).get("status") == "unjudged" for c in H._ck_claims(ck)))

    def test_a_resume_rejudges_exactly_the_failed_verdicts(self):
        sess = FakeSession(lambda label, prompt: self.NB)
        ck = {}
        s = H.EngineSettings(sessions=0, rounds=1, total_budget=40, probe_items=2)
        H.engine_run(FakeCall(self._script()), sess, "PROBLEM", LEAN, s, checkpoint=ck, save=lambda c: None)
        probe_claims = [c for x in ck["probes"] for c in x["claims"]]
        self.assertTrue(all(c["validation"]["status"] == "validated-new" for c in probe_claims))
        # what the old pattern let through: one claim's judges failed on the limit, another's settles check did
        bad, settled = probe_claims[0], probe_claims[1]
        bad["validation"] = {"status": "unjudged", "referee": {"error": self.LIMIT}, "adversary": {"error": self.LIMIT}}
        settled["validation"]["settles"] = {"settles": False, "judges": [{"error": self.LIMIT}]}
        ck["probes"][0]["score"] = 0.0
        call, sess2 = FakeCall(self._script()), FakeSession(lambda label, prompt: self.NB)
        res = H.engine_run(call, sess2, "PROBLEM", LEAN, s, checkpoint=ck, save=lambda c: None)
        self.assertEqual(len(call.prompts("engine-referee")), 1)                 # the one failed verdict, nothing else
        self.assertTrue(bad["validation"].get("rejudged"))
        self.assertEqual(bad["validation"]["status"], "validated-new")
        self.assertNotIn("error", json.dumps(settled["validation"].get("settles")))   # settles redone, not kept as False
        self.assertEqual(ck["rejudged"], 1)
        self.assertGreater(res["probes"][0]["score"], 3.0)                       # the probe's score follows its new verdict
        self.assertEqual(sess2.calls, [])                                        # no probe was bought again

    def test_failed_ratings_are_rated_again(self):
        f = H.parse_frontier(FRONTIER)
        ck = {"gaps": {"rated": {"r1s1/C1": {"error": "no novelty verdict", "panel": [{"error": self.LIMIT}]},
                                 "r1s2/C1": {"verdict": "new", "significance": 2}}},
              "ratings": {f["targets"][0]["id"]: {"error": "no novelty verdict", "panel": [{"error": self.LIMIT}]}}}
        H.engine_drop_infra(ck)
        self.assertEqual(sorted(ck["gaps"]["rated"]), ["r1s2/C1"])
        self.assertEqual((ck["ratings"], ck["ratings_dropped"]), ({}, 2))
        # a resume rates exactly the targets that have no rating, and buys no map
        sess = FakeSession(lambda label, prompt: self.NB)
        ck = {}
        s = H.EngineSettings(sessions=0, rounds=1, total_budget=40, min_target_sig=2)
        H.engine_run(FakeCall(lambda purpose, prompt, n: FRONTIER if purpose == "engine-frontier" else rating(prompt, n)),
                     sess, "PROBLEM", LEAN, s, checkpoint=ck, save=lambda c: None)
        lost = sorted(ck["ratings"])[0]
        ck["ratings"][lost] = {"error": "no novelty verdict", "panel": [{"error": self.LIMIT}]}
        call = FakeCall(lambda purpose, prompt, n: FRONTIER if purpose == "engine-frontier" else rating(prompt, n))
        H.engine_run(call, sess, "PROBLEM", LEAN, s, checkpoint=ck, save=lambda c: None)
        self.assertEqual(call.prompts("engine-frontier"), [])
        self.assertEqual(len(call.prompts("engine-target-rate")), s.rate_judges)
        self.assertNotIn("error", ck["ratings"][lost])

    def test_budget_skips_and_real_verdicts_are_kept(self):
        ck = {"probes": [{"claims": [
            {"id": "C1", "session": "p1", "status": "PROVED", "validation": {"status": "unjudged", "skipped": "engine budget"}},
            {"id": "C2", "session": "p1", "status": "PROVED", "validation": {"status": "broken", "referee": {"valid": False}}}]}]}
        self.assertEqual(H.engine_drop_infra(ck), [])


class MoreRoundsOnResume(unittest.TestCase):
    """The campaign's deep tier resumes a one-round run with two rounds. That run never planned a second round, so its
    checkpoint holds no assignments, and without a review on resume the second round silently did not happen."""

    def test_a_resume_that_adds_a_round_plans_it(self):
        def script(purpose, prompt, n):
            return FRONTIER if purpose == "engine-frontier" else META if purpose == "engine-meta" else judge(purpose)
        sess = FakeSession(lambda label, prompt: notebook(("PROVED", "QUANT", f"claim {label}")))
        ck = {}
        H.engine_run(FakeCall(script, cost=0.1), sess, "PROBLEM", LEAN, H.EngineSettings(sessions=2, rounds=1, total_budget=40),
                     checkpoint=ck, save=lambda c: None)
        self.assertEqual(ck["next"], [])                                  # one round, nothing planned
        call, sess2 = FakeCall(script, cost=0.1), FakeSession(lambda label, prompt: notebook(("PROVED", "QUANT", f"claim {label}")))
        res = H.engine_run(call, sess2, "PROBLEM", LEAN, H.EngineSettings(sessions=2, rounds=2, total_budget=80),
                           checkpoint=ck, save=lambda c: None)
        self.assertEqual(len(call.prompts("engine-meta")), 1)
        self.assertIn(LEAN, call.prompts("engine-meta")[0])          # the team lead plans against the formal statement
        self.assertEqual(len(res["rounds"]), 2)
        self.assertTrue(all("NEXT-ROUND ASSIGNMENT" in p for label, p in sess2.calls if label.startswith("r2")))
        self.assertEqual(sorted(l for l, p in sess2.calls), ["r2s1", "r2s2"])     # round 1 was not bought again


class DecideByComputation(unittest.TestCase):
    """2026-10-08, resolve objective: the map spells out the computation that could settle the problem (a counterexample
    search, a finite check), and that computation leads round 1 and the probes. A disproof is a complete answer."""

    DECIDE = ("=== DECIDE\nIf false, a counterexample is a set of at most 40 residues; none is excluded above lcm 10^6. "
              "Encode as SAT with pysat over lcm in (10^6, 2*10^6], about 3*10^5 instances.\n")

    def _script(self, frontier):
        def script(purpose, prompt, n):
            return frontier if purpose == "engine-frontier" else DEEP_PLAN if purpose == "engine-deep-plan" else judge(purpose)
        return script

    def test_the_section_is_asked_for_and_parsed_only_when_resolving(self):
        call = FakeCall(self._script(FRONTIER), cost=0.1)
        H.engine_run(call, FakeSession(lambda l, p: notebook(("PROVED", "QUANT", "x"))), "PROBLEM", LEAN,
                     H.EngineSettings(sessions=1, rounds=1, total_budget=40, objective="resolve"))
        self.assertIn("=== DECIDE", call.prompts("engine-frontier")[0])
        self.assertIn("TARGET T1 below must be the complete answer", call.prompts("engine-frontier")[0])
        call = FakeCall(self._script(FRONTIER), cost=0.1)
        H.engine_run(call, FakeSession(lambda l, p: notebook(("PROVED", "QUANT", "x"))), "PROBLEM", LEAN,
                     H.EngineSettings(sessions=1, rounds=1, total_budget=40))
        self.assertNotIn("=== DECIDE", call.prompts("engine-frontier")[0])
        f = H.parse_frontier(FRONTIER.replace("=== TARGET T1", self.DECIDE + "=== TARGET T1"))
        self.assertIn("pysat", H.decide_plan(f))
        self.assertIsNone(H.decide_plan(H.parse_frontier(FRONTIER.replace("=== TARGET T1", "=== DECIDE\nNONE: no finite witness.\n=== TARGET T1"))))

    def test_the_computation_leads_round_one_and_the_probes(self):
        frontier = FRONTIER.replace("=== TARGET T1", self.DECIDE + "=== TARGET T1")
        sess = FakeSession(lambda label, prompt: notebook(("REFUTED", "NEGATIVE", "a counterexample with 37 residues")))
        H.engine_run(FakeCall(self._script(frontier), cost=0.1), sess, "PROBLEM", LEAN,
                     H.EngineSettings(sessions=2, rounds=1, total_budget=60, objective="resolve", probe_items=2), workers=2)
        prompts = dict(sess.calls)
        self.assertIn("DECIDE THE PROBLEM BY COMPUTATION", prompts["p1"])
        self.assertIn("DECIDE THE PROBLEM BY COMPUTATION", prompts["r1s1"])
        self.assertNotIn("DECIDE THE PROBLEM BY COMPUTATION", prompts["r1s2"].split("YOUR TEAMMATES")[0])   # a teammate's
        # a decide session's scripts may run 10 minutes, in its prompt and its sandbox; the others keep 2
        self.assertEqual((sess.kw["p1"].get("seconds"), sess.kw["r1s1"].get("seconds")), (600, 600))
        self.assertNotIn("seconds", sess.kw["r1s2"])
        self.assertIn("A run is capped at 600 s", prompts["r1s1"])
        self.assertIn("A run is capped at 120 s", prompts["r1s2"])
        sess = FakeSession(lambda label, prompt: notebook(("PROVED", "QUANT", "x")))
        H.engine_run(FakeCall(self._script(frontier), cost=0.1), sess, "PROBLEM", LEAN,
                     H.EngineSettings(sessions=2, rounds=1, total_budget=60), workers=2)
        self.assertFalse(any("DECIDE THE PROBLEM" in p for l, p in sess.calls))         # advance: unchanged


class Objective(unittest.TestCase):
    """2026-10-08: the campaign aims the deep dive at settling the problem. In step 2 every solved problem had a complete
    proof from its deep dive; step 3, aimed at significant partial results, produced partial results."""

    def test_the_deep_plan_carries_the_objective(self):
        def script(purpose, prompt, n):
            return FRONTIER if purpose == "engine-frontier" else DEEP_PLAN if purpose == "engine-deep-plan" else judge(purpose)
        for objective, phrase in (("resolve", "SETTLING the problem"), ("advance", "a solid partial result")):
            call = FakeCall(script, cost=0.1)
            H.engine_run(call, FakeSession(lambda label, prompt: notebook(("PROVED", "QUANT", "x"))), "PROBLEM", LEAN,
                         H.EngineSettings(sessions=1, rounds=1, total_budget=50, deep_budget=6.0, objective=objective))
            self.assertIn(phrase, call.prompts("engine-deep-plan")[0])
            self.assertIn(LEAN, call.prompts("engine-deep-plan")[0])     # "as the formal statement poses it" needs it
        self.assertEqual(H.EngineSettings().objective, "advance")

    def test_the_settle_chance_is_read_from_the_plan(self):
        plan = DEEP_PLAN.replace("=== GOAL\n", "=== GOAL\nSETTLE CHANCE: 0.3\n", 1)
        self.assertIn("SETTLE CHANCE: 0.3", plan)
        def script(purpose, prompt, n):
            return FRONTIER if purpose == "engine-frontier" else plan if purpose == "engine-deep-plan" else judge(purpose)
        res = H.engine_run(FakeCall(script, cost=0.1), FakeSession(lambda l, p: notebook(("PROVED", "QUANT", "x"))),
                           "PROBLEM", LEAN, H.EngineSettings(sessions=1, rounds=1, total_budget=50, deep_budget=6.0,
                                                             objective="resolve"))
        self.assertEqual(res["deep"]["settle_chance"], 0.3)


class SettleScreen(unittest.TestCase):
    """2026-10-08, REPORT 3.8: the deep plan's SETTLE CHANCE, asked of the map alone before any work, put the dev items the
    engine went on to settle first. `--engine-settle-draws N` makes it a stage of its own, the campaign's ripeness
    screen, and a scout resumes the screen's run without buying the map again."""

    def _call(self, chances):
        def script(purpose, prompt, n):
            if purpose == "engine-frontier":
                return FRONTIER
            if purpose == "engine-settle-screen":
                c = chances[n]
                return "=== GOAL\n" + (f"SETTLE CHANCE: {c}\n" if c is not None else "") + "Prove the core.\n=== PLAN\n1. go"
            return judge(purpose)
        return FakeCall(script, cost=0.2)

    def test_a_map_and_settle_screen_runs_no_session_and_sees_no_result(self):
        call, sess = self._call([0.4, 0.2]), FakeSession(lambda l, p: notebook(("PROVED", "QUANT", "x")))
        res = H.engine_run(call, sess, "PROBLEM", LEAN, H.EngineSettings(sessions=0, rounds=1, total_budget=20,
                                                                         settle_draws=2, gap_rounds=0))
        self.assertEqual(sess.calls, [])
        self.assertEqual(sorted(d["chance"] for d in res["settle_screen"]["draws"]), [0.2, 0.4])
        self.assertAlmostEqual(res["settle_screen"]["mean"], 0.3)
        self.assertAlmostEqual(res["spend"], 0.6)
        prompt = call.prompts("engine-settle-screen")[0]
        self.assertIn(H.SETTLE_SCREEN_RESULTS, prompt)
        self.assertIn("SETTLE CHANCE", prompt)           # the resolve objective, whatever the run's own
        self.assertIn("Richter", prompt)                 # the map
        self.assertIn(LEAN, prompt)                      # what "settle" means: #951 scored 0.575 without it
        self.assertIn("Prove the core", res["settle_screen"]["draws"][0]["goal"])
        self.assertIsNone(H.engine_run(self._call([0.4]), sess, "PROBLEM", LEAN,
                                       H.EngineSettings(sessions=0, rounds=1, total_budget=20)).get("settle_screen"))

    def test_a_resume_draws_again_only_where_a_draw_gave_no_number(self):
        call, s, spend = self._call([None, 0.5, 0.1]), H.EngineSettings(settle_draws=2), H._DiscoverySpend(10)
        first = H.engine_settle_screen(call, s, "PROBLEM", LEAN, "MAP", spend)
        self.assertEqual(sorted(str(d["chance"]) for d in first["draws"]), ["0.5", "None"])
        self.assertEqual(first["mean"], 0.5)
        again = H.engine_settle_screen(call, s, "PROBLEM", LEAN, "MAP", spend, have=first)
        self.assertEqual(len(call.prompts("engine-settle-screen")), 3)
        self.assertAlmostEqual(again["mean"], 0.3)
        self.assertAlmostEqual(again["cost"], 0.6)
        self.assertEqual((H.settle_chance("**SETTLE CHANCE:** 0.25"), H.settle_chance("SETTLE CHANCE: 1.5"),
                          H.settle_chance("no line")), (0.25, 1.0, None))

    def test_the_scout_resumes_the_screen_and_keeps_its_record(self):
        ck = {}
        H.engine_run(self._call([0.4, 0.2]), FakeSession(lambda l, p: notebook(("PROVED", "QUANT", "x"))), "PROBLEM", LEAN,
                     H.EngineSettings(sessions=0, rounds=1, total_budget=20, settle_draws=2, gap_rounds=0),
                     checkpoint=ck, save=lambda c: None)
        call, sess = self._call([0.9]), FakeSession(lambda l, p: notebook(("PROVED", "QUANT", "x")))
        res = H.engine_run(call, sess, "PROBLEM", LEAN, H.EngineSettings(sessions=1, rounds=1, total_budget=40, gap_rounds=0),
                           checkpoint=ck, save=lambda c: None)
        self.assertEqual((call.prompts("engine-frontier"), call.prompts("engine-settle-screen")), ([], []))
        self.assertEqual(len(sess.calls), 1)
        self.assertAlmostEqual(res["settle_screen"]["mean"], 0.3)


PLAN = """=== TARGET
ANSWER: TRUE
Every n satisfies P(n).
=== LEMMA L1
STATEMENT: P holds for every prime.
DIFFICULTY: elementary
ROUTE: induction on the prime.
TEST: primes below 100.
=== LEMMA L2
STATEMENT: P is multiplicative.
DIFFICULTY: moderate
ROUTE: the Chinese remainder theorem.
TEST: n below 100.
=== GLUE
Factor n into primes. By L1 each prime factor satisfies P, and by L2 so does their product.
=== CHANGES
The first skeleton.
"""


class LiteratureGate(unittest.TestCase):
    """2026-10-15: #1199 was settled by arXiv:2607.17333 in July 2026 while erdosproblems.com still listed it open, and the
    campaign spent $83 on it. The engine now searches the literature before the map, and stops if a paper settles it."""

    def script(self, settled):
        def go(purpose, prompt, n):
            if purpose == "engine-literature-queries":
                return "QUERY: Owings sumset question monochromatic\nQUERY: monochromatic sumset infinite colouring\n"
            if purpose == "engine-literature-verdict":
                return "```json\n" + json.dumps({"settled": settled, "work": "An affirmative answer to Owings's sumset question",
                                                  "answer": "true", "confidence": 0.95, "why": "it proves the statement"}) + "\n```"
            if purpose == "engine-frontier":
                return FRONTIER
            return judge(purpose)
        return go

    def search(self, q):
        self.queries.append(q)
        return [{"title": "An affirmative answer to Owings's sumset question", "year": "2026", "abstract": "B+B monochromatic."},
                {"title": "Monochromatic infinite sumsets", "year": "2017", "abstract": ""}]

    def setUp(self):
        self.queries = []

    def test_a_settling_paper_ends_the_run_before_the_map(self):
        call, ck = FakeCall(self.script(True), cost=0.05), {}
        res = H.engine_run(call, FakeSession(lambda l, p: ""), "PROBLEM", LEAN,
                           H.EngineSettings(sessions=1, literature_scan=True), checkpoint=ck, lit_search=self.search)
        self.assertEqual(res["stopped"], "resolved in the literature")
        self.assertNotIn("error", res)                       # a finding, never an outage
        self.assertEqual(call.prompts("engine-frontier"), [])
        self.assertEqual(self.queries, ["Owings sumset question monochromatic", "monochromatic sumset infinite colouring"])
        self.assertEqual(len(ck["literature"]["works"]), 2)  # deduplicated across the two queries

    def test_an_unsettled_search_reaches_the_map_and_is_never_bought_twice(self):
        call, ck = FakeCall(self.script(False), cost=0.05), {}
        s = H.EngineSettings(sessions=0, literature_scan=True)
        H.engine_run(call, FakeSession(lambda l, p: ""), "PROBLEM", LEAN, s, checkpoint=ck, lit_search=self.search)
        self.assertIn("LITERATURE SEARCH", call.prompts("engine-frontier")[0])
        self.assertIn("Owings", call.prompts("engine-frontier")[0])
        H.engine_run(call, FakeSession(lambda l, p: ""), "PROBLEM", LEAN, s, checkpoint=ck, lit_search=self.search)
        self.assertEqual(len(call.prompts("engine-literature-queries")), 1)

    def test_no_search_means_no_gate(self):
        # a benchmark or masked run passes no search: a paper could reveal the published answer
        call = FakeCall(self.script(True), cost=0.05)
        res = H.engine_run(call, FakeSession(lambda l, p: ""), "PROBLEM", LEAN,
                           H.EngineSettings(sessions=0, literature_scan=True), lit_search=None)
        self.assertNotIn("stopped", res)
        self.assertEqual(call.prompts("engine-literature-queries"), [])

    def test_a_low_confidence_verdict_does_not_stop(self):
        self.assertFalse(H.literature_settled({"verdict": {"settled": True, "confidence": 0.5}}, 0.7))
        self.assertTrue(H.literature_settled({"verdict": {"settled": True, "confidence": "0.8"}}, 0.7))
        self.assertFalse(H.literature_settled({"verdict": {"settled": "yes", "confidence": 1}}, 0.7))


class ResearchProgram(unittest.TestCase):
    """2026-10-13, the analytical deep tier: a proof skeleton whose glue is refereed, lemma sessions judged against each
    lemma as stated, and one assembled chain the settles judges and the campaign's Lean tier see."""

    def _call(self, plans, glue_ok=True, settles_on="Every n satisfies"):
        def script(purpose, prompt, n):
            if purpose == "engine-frontier":
                return FRONTIER
            if purpose == "engine-program-plan":
                return plans[min(n, len(plans) - 1)]
            if purpose == "engine-referee" and "The target follows from the lemmas" in prompt and not glue_ok:
                return judge(purpose, valid=False)
            if purpose == "engine-settles":
                return "```json\n" + json.dumps({"settles": settles_on in prompt, "answer": "true"}) + "\n```"
            if purpose == "engine-intent":
                return "```json\n" + json.dumps({"class": "new-math", "why": "nothing like it is known", "source": None}) + "\n```"
            return judge(purpose)
        return FakeCall(script, cost=0.1)

    def _settings(self, **kw):
        base = dict(sessions=0, rounds=1, total_budget=120, program_cycles=3, program_budget=80, gap_rounds=0,
                    settles_max=3, intent_judges=2)
        base.update(kw)
        return H.EngineSettings(**base)

    def test_the_parser_and_the_adoption_rule(self):
        plan = H.parse_program_plan(PLAN.replace("=== LEMMA L1\nSTATEMENT: P holds for every prime.",
                                                 "=== LEMMA L1\nUSE: r1s1/C1"))
        self.assertEqual((plan["answer"], plan["target"]), ("true", "Every n satisfies P(n)."))
        self.assertEqual([(l["id"], l["use"], l["difficulty"]) for l in plan["lemmas"]],
                         [("L1", "r1s1/C1", "elementary"), ("L2", "", "moderate")])
        self.assertIn("By L1", plan["glue"])
        valid = {"r1s1/C1": {"statement": "P holds for every prime.", "proof": "By C2 and induction.", "_chain": "x C2"}}
        sk, why = H.program_resolve_plan(plan, None, valid, [])
        self.assertEqual([l["status"] for l in sk["lemmas"]], ["established", "open"])
        self.assertNotIn("C2", sk["lemmas"][0]["proof"])                    # another notebook's numbers never cite
        self.assertIsNone(H.program_resolve_plan(plan, None, {}, [])[0])      # an unknown key is refused
        self.assertIsNone(H.program_resolve_plan(plan, None, valid, ["P is multiplicative."])[0])   # refuted before
        easy = {"lemmas": [{"status": "open", "difficulty": "elementary", "statement": "a"}]}
        hard = {"lemmas": [{"status": "open", "difficulty": "hard", "statement": "b"}]}
        self.assertTrue(H.program_better(easy, hard, 0)[0])
        self.assertFalse(H.program_better(hard, easy, 0)[0])
        self.assertTrue(H.program_better(hard, easy, 1)[0])                   # a new route after a stalled cycle

    def test_an_extension_clears_a_stopped_program_once(self):
        # the campaign's persistence pass (2026-10-15): more cycles and budget, and the last pass's stop cleared once
        ck = {"program": {"cycles": [{"cycle": 1, "finished": True}, {"cycle": 2, "finished": True}], "stall": 2,
                          "stop": "2 cycles without a discharge", "start_spend": 0.0}}
        s = self._settings(program_cycles=2, program_extend=True)
        call = self._call([PLAN])
        out = H.engine_program(call, FakeSession(lambda l, p: ""), s, "PROBLEM", LEAN, "", "", "", [],
                               H._DiscoverySpend(50.0), ck=ck)
        st = ck["program"]
        self.assertEqual([(e["after_cycles"], e["stall"]) for e in st["extensions"]], [(2, 2)])
        self.assertEqual(st["stall"], 0)
        self.assertEqual(out["stop"], "2 cycles")              # this run had no new cycles to give: it stops again
        H.engine_program(call, FakeSession(lambda l, p: ""), s, "PROBLEM", LEAN, "", "", "", [], H._DiscoverySpend(50.0),
                         ck=ck)
        self.assertEqual(len(st["extensions"]), 1)             # never twice at the same point
        self.assertEqual(call.prompts("engine-program-plan"), [])

    def test_a_skeleton_closes_into_one_chain_the_settles_judges_see(self):
        call = self._call([PLAN])
        sess = FakeSession(lambda l, p: notebook(("PROVED", "QUANT", "whatever the session wrote")))
        res = H.engine_run(call, sess, "PROBLEM", LEAN, self._settings())
        self.assertTrue(res["program"]["done"])
        self.assertIn(LEAN, call.prompts("engine-program-plan")[0])
        self.assertEqual(sorted(l for l, _ in sess.calls), ["p1L1", "p1L2"])
        self.assertIn("PROVE LEMMA L2", dict(sess.calls)["p1L2"])
        comp = H.engine_complete(res)
        self.assertEqual((comp["session"], comp["id"]), ("program", "C3"))
        chain = H.engine_chain_text(comp, res["ledger"])
        self.assertIn("P holds for every prime.", chain)
        self.assertIn("P is multiplicative.", chain)
        self.assertEqual(comp["validation"]["intent"]["class"], "new-math")
        # a session claim that settles at the same significance does not displace the assembled chain
        rival = {"session": "r1s1", "id": "C1", "status": "PROVED", "statement": "Every n satisfies P(n), with R5.",
                 "proof": "p", "validation": {**comp["validation"], "status": "validated-new"}}
        self.assertEqual(H.engine_complete({"ledger": [rival] + res["ledger"]})["session"], "program")
        # the lemma referee judged the LEMMA's statement, not the session's
        self.assertTrue(any("P holds for every prime." in p for p in call.prompts("engine-referee")))

    def test_a_refuted_lemma_kills_the_skeleton_and_the_next_plan_routes_around_it(self):
        plan2 = PLAN.replace("P is multiplicative.", "P holds for every product of two primes.").replace(
            "The first skeleton.", "L2 was refuted; this route avoids it.")
        call = self._call([PLAN, plan2])

        def nb(label, prompt):
            refute = label == "p1L2"
            return notebook(("REFUTED" if refute else "PROVED", "QUANT", "n = 6 breaks it" if refute else "fine"))
        res = H.engine_run(call, FakeSession(nb), "PROBLEM", LEAN, self._settings())
        self.assertEqual(res["program"]["refuted"], ["P is multiplicative."])
        self.assertIn("P is multiplicative.", call.prompts("engine-program-plan")[1].split("REFUTED STATEMENTS")[1])
        self.assertTrue(res["program"]["done"])
        self.assertIn("P holds for every product of two primes.", H.engine_chain_text(H.engine_complete(res), res["ledger"]))

    def test_a_broken_glue_is_refused_and_the_program_stalls_out(self):
        call = self._call([PLAN], glue_ok=False)
        sess = FakeSession(lambda l, p: notebook(("PROVED", "QUANT", "x")))
        res = H.engine_run(call, sess, "PROBLEM", LEAN, self._settings(program_stall=2))
        self.assertEqual(sess.calls, [])
        self.assertFalse(res["program"]["done"])
        self.assertIn("without a discharge", res["program"]["stop"])
        self.assertTrue(all("glue did not pass" in r["why"] for r in res["program"]["refused"]))
        self.assertIsNone(H.engine_complete(res))

    def test_a_resume_buys_neither_the_plan_nor_a_finished_attack_twice(self):
        ck, crashed = {}, {"done": False}

        def nb(label, prompt):
            if label == "p1L2" and not crashed["done"]:
                crashed["done"] = True
                return Crash("battery")
            return notebook(("PROVED", "QUANT", "x"))
        with self.assertRaises(Crash):
            H.engine_run(self._call([PLAN]), FakeSession(nb), "PROBLEM", LEAN, self._settings(), workers=1,
                         checkpoint=ck, save=lambda c: None)
        call, sess = self._call([PLAN]), FakeSession(nb)
        res = H.engine_run(call, sess, "PROBLEM", LEAN, self._settings(), workers=1, checkpoint=ck, save=lambda c: None)
        self.assertEqual(call.prompts("engine-program-plan"), [])
        self.assertEqual([l for l, _ in sess.calls], ["p1L2"])
        self.assertTrue(res["program"]["done"])

    def test_the_intent_panel_and_the_screen(self):
        P = H.intent_panel
        self.assertEqual(P([{"class": "new-math"}, {"class": "new-math"}])["class"], "new-math")
        self.assertEqual(P([{"class": "new-math"}, {"class": "known-result", "source": "Ruzsa 1998"}])["class"], "known-result")
        self.assertEqual(P([{"class": "formalization-gap"}, {"class": "known-result"}])["class"], "formalization-gap")
        self.assertEqual(P([{"error": "x"}, {"class": "new-math"}])["class"], "unclear")

        def script(purpose, prompt, n):
            if purpose == "engine-frontier":
                return FRONTIER
            if purpose == "engine-settle-screen":
                return "=== GOAL\nSETTLE CHANCE: 0.85\nDisprove it with the regular n-gon.\n=== PLAN\n1."
            if purpose == "engine-intent":
                return "```json\n" + json.dumps({"class": "formalization-gap", "why": "the n-gon is degenerate", "source": None}) + "\n```"
            return judge(purpose)
        call = FakeCall(script, cost=0.1)
        res = H.engine_run(call, FakeSession(lambda l, p: ""), "PROBLEM", LEAN,
                           H.EngineSettings(sessions=0, rounds=1, total_budget=20, settle_draws=2, intent_judges=2,
                                            gap_rounds=0))
        self.assertEqual(res["intent"]["class"], "formalization-gap")
        self.assertIn("regular n-gon", call.prompts("engine-intent")[0])
        low = FakeCall(lambda pu, pr, n: FRONTIER if pu == "engine-frontier" else
                       "=== GOAL\nSETTLE CHANCE: 0.05\nNo line.\n" if pu == "engine-settle-screen" else judge(pu), cost=0.1)
        H.engine_run(low, FakeSession(lambda l, p: ""), "PROBLEM", LEAN,
                     H.EngineSettings(sessions=0, rounds=1, total_budget=20, settle_draws=2, intent_judges=2, gap_rounds=0))
        self.assertEqual(low.prompts("engine-intent"), [])                  # below the bar, not classified


PLAN_A = PLAN.replace("Every n satisfies P(n).", "Theorem A: every prime n satisfies Q(n).")
PLAN_B = """=== TARGET
ANSWER: TRUE
Theorem B: every n satisfies Q(n).
=== LEMMA L1
USE: R1
=== LEMMA L2
STATEMENT: Q is multiplicative.
DIFFICULTY: moderate
ROUTE: the Chinese remainder theorem.
TEST: n below 100.
=== GLUE
By L1 every prime satisfies Q, and by L2 so does every product of primes.
=== CHANGES
R1 is proved; this is the line's stretch goal, built on it.
"""


class BuildTrack(unittest.TestCase):
    """2026-10-16, the operator: the campaign was screening out the hard problems because they need new mathematics,
    instead of building it. The screen's deep plan already names a progress line when no settling line is plausible; the
    judges now rate that line, and the research program can be committed to it and climb it one proved theorem (rung) at
    a time."""

    LINE = "SETTLE CHANCE: 0.02\nNo settling line, so major progress: prove Theorem A, then the stretch goal Theorem B."

    def _screen_call(self, chance, verdict="new", sig=2):
        def script(purpose, prompt, n):
            if purpose == "engine-frontier":
                return FRONTIER
            if purpose == "engine-settle-screen":
                return (f"=== GOAL\nSETTLE CHANCE: {chance}\nNo settling line, so major progress: prove Theorem A.\n"
                        "=== WHY THIS LINE\nit isolates the core.\n=== PLAN\n1. the prime case\n2. Theorem B, the stretch goal")
            if purpose == "engine-target-rate":
                return "```json\n" + json.dumps({"verdict": verdict, "significance": sig, "reach": "medium",
                                                 "p_week": 0.3, "why": "a solid special case"}) + "\n```"
            return judge(purpose)
        return FakeCall(script, cost=0.1)

    def test_the_screen_rates_each_draws_line_below_the_bar_once(self):
        ck, call = {}, self._screen_call(0.02)
        s = H.EngineSettings(sessions=0, rounds=1, total_budget=20, settle_draws=2, gap_rounds=0, progress_rate=True)
        res = H.engine_run(call, FakeSession(lambda l, p: ""), "PROBLEM", LEAN, s, checkpoint=ck, save=lambda c: None)
        scr = res["settle_screen"]
        self.assertEqual(sorted(x["draw"] for x in scr["progress"]), ["D1", "D2"])
        self.assertIn("=== PLAN", scr["draws"][0]["text"])          # the whole plan is kept, not only the goal
        rates = call.prompts("engine-target-rate")
        self.assertEqual(len(rates), 4)                             # two judges for each of two draws
        self.assertIn("MAIN TARGET", rates[0])
        self.assertIn("Theorem B, the stretch goal", rates[0])
        best = H.progress_best(scr)
        self.assertEqual((best["significance"], best["p_week"], best["value"]), (2, 0.3, 0.6))
        self.assertIn("prove Theorem A", best["goal"])
        again = self._screen_call(0.02)
        H.engine_run(again, FakeSession(lambda l, p: ""), "PROBLEM", LEAN, s, checkpoint=ck, save=lambda c: None)
        self.assertEqual(again.prompts("engine-target-rate"), [])   # a resume never rates twice
        ripe = self._screen_call(0.5)
        res = H.engine_run(ripe, FakeSession(lambda l, p: ""), "PROBLEM", LEAN, s)
        self.assertEqual(ripe.prompts("engine-target-rate"), [])    # a problem that passes the screen is not rated
        self.assertNotIn("progress", res["settle_screen"])
        for verdict, sig in (("known", 3), ("restatement", 3), ("new", 1)):
            res = H.engine_run(self._screen_call(0.02, verdict, sig), FakeSession(lambda l, p: ""), "PROBLEM", LEAN, s)
            self.assertIsNone(H.progress_best(res["settle_screen"]), (verdict, sig))

    def _program_call(self, plans, reject_assembled=False):
        def script(purpose, prompt, n):
            if purpose == "engine-frontier":
                return FRONTIER
            if purpose == "engine-program-plan":
                return plans[min(n, len(plans) - 1)]
            if purpose == "engine-referee" and reject_assembled and "a complete argument assembled" in prompt:
                return judge(purpose, valid=False)
            if purpose == "engine-settles":
                return "```json\n" + json.dumps({"settles": False, "answer": None}) + "\n```"
            return judge(purpose)
        return FakeCall(script, cost=0.1)

    def _settings(self, **kw):
        base = dict(sessions=0, rounds=1, total_budget=200, program_cycles=3, program_budget=150, gap_rounds=0,
                    settles_max=3, program_line=self.LINE)
        base.update(kw)
        return H.EngineSettings(**base)

    def test_a_build_program_aims_at_the_line_and_climbs_it_rung_by_rung(self):
        call = self._program_call([PLAN_A, PLAN_B])
        sess = FakeSession(lambda l, p: notebook(("PROVED", "QUANT", "whatever the session wrote")))
        res = H.engine_run(call, sess, "PROBLEM", LEAN, self._settings())
        prog = res["program"]
        self.assertEqual([(r["key"], r["valid"], r["significance"]) for r in prog["rungs"]], [("R1", True, 2), ("R2", True, 2)])
        self.assertFalse(prog["done"])                               # a build program never stops at its first theorem
        self.assertEqual(prog["stop"], "3 cycles")
        self.assertEqual(prog["established"], 3)                     # A's two lemmas, then B's open one
        plans = call.prompts("engine-program-plan")
        self.assertIn("prove Theorem A, then the stretch goal Theorem B", plans[0])
        self.assertNotIn("settles the problem as Erdős posed it", plans[0])
        self.assertIn("(nothing yet: the target is the line's main theorem)", plans[0])
        self.assertIn("[R1] PROVED in cycle 1", plans[1])
        self.assertIn("its target, a theorem on the way to the problem", dict(sess.calls)["p1L1"])
        # the third plan re-proposed Theorem B, which is already proved: refused before any judge was paid
        self.assertIn("its target is already proved on this line", prog["refused"][-1]["why"])
        keys = {H.engine_claim_key(c) for c in res["ledger"]}
        self.assertTrue({"program-R1/C3", "program-R2/C3"} <= keys)  # each rung its own notebook: no key collides
        r2 = next(c for c in res["ledger"] if H.engine_claim_key(c) == "program-R2/C3")
        self.assertIn("Theorem A: every prime n satisfies Q(n).", H.engine_chain_text(r2, res["ledger"]))
        report = H.engine_report(res, "build")
        self.assertIn("Build track", report)
        self.assertIn("**R2** (proved", report)

    def test_a_rung_of_reused_results_only_counts_toward_the_stall(self):
        corollary = ("=== TARGET\nANSWER: TRUE\nTheorem C: Q(p) for every prime p > 2.\n=== LEMMA L1\nUSE: R1\n"
                     "=== GLUE\nImmediate from L1.\n=== CHANGES\nA corollary of R1.\n")
        call = self._program_call([PLAN_A, corollary])
        res = H.engine_run(call, FakeSession(lambda l, p: notebook(("PROVED", "QUANT", "x"))), "PROBLEM", LEAN,
                           self._settings(program_cycles=6, program_stall=2))
        self.assertEqual([r["key"] for r in res["program"]["rungs"]], ["R1", "R2"])
        self.assertEqual(res["program"]["stop"], "2 cycles without a discharge")   # not six cycles of corollaries

    def test_a_rejected_rung_has_no_key_to_build_on(self):
        call = self._program_call([PLAN_A, PLAN_B], reject_assembled=True)
        res = H.engine_run(call, FakeSession(lambda l, p: notebook(("PROVED", "QUANT", "x"))), "PROBLEM", LEAN,
                           self._settings(program_cycles=2))
        self.assertEqual([(r["key"], r["valid"]) for r in res["program"]["rungs"]], [("R1", False)])
        self.assertIn("NOT PROVED: the assembled argument for this target was rejected", call.prompts("engine-program-plan")[1])
        self.assertIn("uses R1, which is not an established lemma", res["program"]["refused"][-1]["why"])

    def test_a_rung_left_unassembled_is_assembled_first_on_the_next_pass(self):
        sk = H.program_resolve_plan(H.parse_program_plan(PLAN_A), None, {}, [])[0]
        for l in sk["lemmas"]:
            l.update(status="established", proof="by computation")
        ck = {"program": {"cycles": [{"cycle": 1, "finished": True}], "stall": 0, "skeleton": sk, "start_spend": 0.0,
                          "stop": "budget, with every lemma of the rung established"}}
        call = self._program_call([PLAN_B])
        out = H.engine_program(call, FakeSession(lambda l, p: ""), self._settings(program_cycles=1, program_extend=True),
                               "PROBLEM", LEAN, "", "", "", [], H._DiscoverySpend(50.0), ck=ck)
        self.assertEqual([r["key"] for r in out["rungs"]], ["R1"])
        self.assertIsNone(ck["program"]["skeleton"])
        self.assertEqual(call.prompts("engine-program-plan"), [])   # no plan was bought to finish it

    def test_the_settle_program_is_unchanged(self):
        plan = H.program_plan_prompt("S", "L", "M", "E", "K", "R", "F")
        self.assertIn("The aim is new mathematics: a skeleton that settles the problem as Erdős posed it.", plan)
        self.assertIn("ANSWER: TRUE (the formal statement holds) or FALSE (its negation holds)", plan)
        self.assertNotIn("PROVED ON THIS LINE", plan)


class Crash(Exception):
    """A dead battery, a kill, a hung call: anything that is not a failed call and stops the run outright."""


class Resume(unittest.TestCase):
    """2026-10-02: the Mac's battery died seven minutes into a v3 run, and an idle sleep earlier hung two judge calls for
    6.5 hours. A frontier map alone has cost $9, so a cut-off run must resume without buying anything twice."""

    def _call(self, crash_on=None):
        def script(purpose, prompt, n):
            if crash_on and crash_on(purpose, n):
                raise Crash(purpose)
            return FRONTIER if purpose == "engine-frontier" else META if purpose == "engine-meta" else judge(purpose)
        return FakeCall(script, cost=0.1)

    def _store(self):
        box = {}

        def save(ck):
            box["ck"] = json.loads(json.dumps(ck))       # what a reload from disk would see
        return box, save

    def test_a_crash_mid_round_keeps_the_map_and_the_finished_sessions(self):
        box, save = self._store()
        first = self._call()
        crashing = FakeSession(lambda label, prompt: Crash(label) if label == "r1s2" else notebook(("PROVED", "QUANT", label)))
        s = H.EngineSettings(sessions=2, rounds=1, total_budget=50)
        with self.assertRaises(Crash):
            H.engine_run(first, crashing, "PROBLEM", LEAN, s, workers=1, save=save)
        self.assertEqual(sorted(box["ck"]["partial"]["done"]), ["r1s1"])
        again = self._call()
        sess = FakeSession(lambda label, prompt: notebook(("PROVED", "QUANT", label)))
        res = H.engine_run(again, sess, "PROBLEM", LEAN, s, workers=1, checkpoint=box["ck"], save=save)
        self.assertEqual(again.prompts("engine-frontier"), [])            # the map is not bought twice
        self.assertEqual([label for label, p in sess.calls], ["r1s2"])     # nor the finished session
        self.assertEqual(sorted(c["statement"] for c in res["ledger"]), ["r1s1", "r1s2"])
        self.assertGreaterEqual(res["spend"], box["ck"]["spend"] - 1e-9)
        self.assertNotIn("partial", box["ck"])

    def test_verdicts_already_reached_are_not_judged_again(self):
        box, save = self._store()
        s = H.EngineSettings(sessions=1, rounds=1, total_budget=50)
        sess = FakeSession(lambda label, prompt: notebook(("PROVED", "QUANT", "a"), ("PROVED", "QUANT", "b")))
        with self.assertRaises(Crash):          # the third referee call is the second claim's... crash on the 2nd referee
            H.engine_run(self._call(lambda purpose, n: purpose == "engine-referee" and n == 1), sess, "PROBLEM", LEAN, s,
                         workers=1, save=save)
        judged = [c for c in box["ck"]["partial"]["done"]["r1s1"]["claims"] if c.get("validation")]
        self.assertEqual(len(judged), 1)
        again = self._call()
        res = H.engine_run(again, FakeSession(lambda label, prompt: notebook()), "PROBLEM", LEAN, s, workers=1,
                           checkpoint=box["ck"], save=save)
        self.assertEqual(len(again.prompts("engine-referee")), 1)          # only the claim not yet judged
        self.assertEqual(len([c for c in res["ledger"] if (c.get("validation") or {}).get("status") == "validated-new"]), 2)

    def test_a_finished_round_is_never_rerun(self):
        box, save = self._store()
        s = H.EngineSettings(sessions=2, rounds=2, total_budget=50)
        crashing = FakeSession(lambda label, prompt: Crash(label) if label.startswith("r2") else notebook(("PROVED", "QUANT", label)))
        with self.assertRaises(Crash):
            H.engine_run(self._call(), crashing, "PROBLEM", LEAN, s, workers=1, save=save)
        self.assertEqual(len(box["ck"]["rounds"]), 1)
        self.assertTrue(box["ck"]["next"])
        again = self._call()
        sess = FakeSession(lambda label, prompt: notebook(("PROVED", "QUANT", label)))
        res = H.engine_run(again, sess, "PROBLEM", LEAN, s, workers=1, checkpoint=box["ck"], save=save)
        self.assertEqual([label for label, p in sess.calls], ["r2s1", "r2s2"])
        self.assertTrue(all("NEXT-ROUND ASSIGNMENT" in p for label, p in sess.calls))
        self.assertEqual(again.prompts("engine-meta"), [])
        self.assertEqual(len(res["rounds"]), 2)

    def test_the_deep_dive_session_is_kept_before_it_is_judged(self):
        box, save = self._store()

        def script(purpose, prompt, n):
            if purpose == "engine-referee" and "from deep" in prompt:
                raise Crash(purpose)
            return (FRONTIER if purpose == "engine-frontier" else DEEP_PLAN if purpose == "engine-deep-plan" else judge(purpose))
        s = H.EngineSettings(sessions=1, rounds=1, total_budget=50, deep_budget=8.0)
        sess = FakeSession(lambda label, prompt: notebook(("PROVED", "QUANT", f"claim from {label}")))
        with self.assertRaises(Crash):
            H.engine_run(FakeCall(script, cost=0.1), sess, "PROBLEM", LEAN, s, workers=1, save=save)
        self.assertIn("deep_partial", box["ck"])
        sess2 = FakeSession(lambda label, prompt: notebook())
        res = H.engine_run(self._call(), sess2, "PROBLEM", LEAN, s, workers=1, checkpoint=box["ck"], save=save)
        self.assertEqual(sess2.calls, [])                                  # neither a round nor the deep session again
        self.assertEqual(res["deep"]["validated"], 1)


REPAIRED = """=== VERDICT
REPAIRED: the hypothesis is restricted to integer x, the only case the proof uses.
=== STATEMENT
Assume U(c) for integer x. Then F(n) tends to infinity.
=== PROOF
As before, with x = n - 1 an integer throughout.
=== CHANGES
U(c) now quantifies over integers, so the adversary's non-integer x no longer applies.
"""


class Repair(unittest.TestCase):
    """#1203: the adversary broke a conditional proof of the whole statement over a technicality it called fixable
    (the hypothesis was stated for real x, the proof uses integer x). A fixable break used to be final."""

    def _call(self, fatal=False, severity="fixable"):
        def script(purpose, prompt, n):
            if purpose == "engine-frontier":
                return FRONTIER
            if purpose == "engine-repair":
                return "=== VERDICT\nFATAL: the counterexample stands.\n" if fatal else REPAIRED
            broken = "U(c) for real x" in prompt
            if purpose == "engine-adversary":
                return "```json\n" + json.dumps({"broken": broken, "how": "non-integer x" if broken else None,
                                                 "severity": severity if broken else "none"}) + "\n```"
            return judge(purpose)
        return FakeCall(script, cost=0.1)

    def _run(self, call, repair_max=3, checkpoint=None, save=None):
        sess = FakeSession(lambda label, prompt: notebook(("PROVED", "CONDITIONAL", "Assume U(c) for real x. Then F -> infinity.")))
        return H.engine_run(call, sess, "PROBLEM", LEAN, H.EngineSettings(sessions=1, rounds=1, total_budget=50,
                                                                          repair_max=repair_max, gap_rounds=0),
                            checkpoint=checkpoint, save=save)          # the one-shot repair alone; gap closing is tested apart

    def test_a_fixable_break_is_repaired_and_judged_again(self):
        call = self._call()
        res = self._run(call)
        by = {c["id"]: c for c in res["ledger"]}
        self.assertEqual(by["C1"]["validation"]["status"], "broken")          # the original stays as it was judged
        self.assertEqual(by["C1r"]["validation"]["status"], "validated-new")
        self.assertEqual(by["C1r"]["repaired_from"], "r1s1/C1")
        self.assertIn("integer x", by["C1r"]["statement"])
        self.assertEqual(len(call.prompts("engine-repair")), 1)
        self.assertEqual([c["id"] for c in res["validated"]], ["C1r"])

    def test_fatal_repairs_and_fatal_breaks_add_nothing(self):
        res = self._run(self._call(fatal=True))
        self.assertEqual([c["id"] for c in res["ledger"]], ["C1"])
        call = self._call(severity="fatal")                                   # the referee passes, the adversary: fatal
        res = self._run(call)
        self.assertEqual(res["ledger"][0]["validation"]["status"], "broken")
        self.assertEqual(call.prompts("engine-repair"), [])                   # a fatal break is never "repaired"

    def test_repairs_are_checkpointed(self):
        box = {}

        def save(ck):
            box["ck"] = json.loads(json.dumps(ck))
        self._run(self._call(), save=save)
        again = self._call()
        res = self._run(again, checkpoint=box["ck"], save=save)
        self.assertEqual(again.prompts("engine-repair"), [])
        self.assertIn("C1r", [c["id"] for c in res["ledger"]])


class Panel(unittest.TestCase):
    def test_the_conservative_verdict_wins(self):
        P = H.engine_novelty_panel
        self.assertEqual(P([{"verdict": "new", "significance": 2}, {"verdict": "routine", "significance": 1}])["verdict"], "routine")
        both = P([{"verdict": "new", "significance": 2}, {"verdict": "new", "significance": 1}])
        self.assertEqual((both["verdict"], both["significance"]), ("new", 1))
        self.assertEqual(P([{"verdict": "new", "significance": 2}, {"error": "over cap"}])["verdict"], "unrated")
        self.assertIn("error", P([{"error": "a"}, {"error": "b"}]))

    def test_sessions_see_their_teammates(self):
        sess = FakeSession(lambda label, prompt: notebook(("CONJECTURED", "QUANT", "x")))
        call = FakeCall(lambda purpose, prompt, n: FRONTIER if purpose == "engine-frontier" else judge(purpose))
        H.engine_run(call, sess, "PROBLEM", LEAN, H.EngineSettings(sessions=3, rounds=1, total_budget=50), workers=3)
        prompts = dict(sess.calls)
        self.assertIn("YOUR TEAMMATES THIS ROUND", prompts["r1s1"])
        self.assertIn("r1s2:", prompts["r1s1"])
        self.assertNotIn("r1s1:", prompts["r1s1"])


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
        n_calls, n_sessions = len(call.calls), len(sess.calls)
        again = self.h.stage_discover()                     # a resume re-enters the engine from its checkpoint...
        self.assertEqual(again["validated"], keep["validated"])
        self.assertEqual((len(call.calls), len(sess.calls)), (n_calls, n_sessions))   # ...and buys nothing twice

    def test_no_frontier_map_is_an_infrastructure_error(self):
        """A usage limit at the first call is never a result: three step-2 items were recorded as $0 problems."""
        def boom(purpose, prompt, n):
            return H.DiscoveryCallFailed("claude -p returned an error result: You've hit your weekly limit", cost=0.0)
        self.h._discovery_caller = lambda: FakeCall(boom)
        self.h._engine_session_caller = lambda: FakeSession(lambda label, prompt: notebook(("PROVED", "QUANT", "x")))
        self.h._engine_search = lambda: None
        with self.assertRaisesRegex(RuntimeError, "no frontier map"):
            self.h.stage_discover()
        self.assertNotIn("discovery", self.h.state)

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
