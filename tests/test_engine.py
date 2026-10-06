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

    def __call__(self, purpose, prompt, label, turns, budget, effort, files=None):
        with self.lock:
            self.calls.append((label, prompt))
            self.files = getattr(self, "files", {})
            self.files[label] = dict(files or {})
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
    target = prompt.split("THE TARGET:")[1]
    if "0.54" in target:
        v = {"verdict": "new", "significance": 1, "reach": "high"}
    elif "0.6" in target:
        v = {"verdict": "new", "significance": 2, "reach": "medium"}
    else:
        v = {"verdict": "restatement", "significance": 3, "reach": "low"}
    return "```json\n" + json.dumps({**v, "cite": None, "why": "w"}) + "\n```"


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
        ck = {"frontier": {**H.parse_frontier(FRONTIER), "text": FRONTIER},
              "ratings": {"T1": {"verdict": "new", "significance": 3, "reach": "high"}}}
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
        self.assertIsNone(res["gaps"])                                         # the gap phase is off by default
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
                                                                          repair_max=repair_max),
                            checkpoint=checkpoint, save=save)

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
