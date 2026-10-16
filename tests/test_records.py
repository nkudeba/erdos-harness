"""The record and explicit tracks (2026-10-15): the engine objectives, certificates re-checked by the harness after each
session, and the survey that finds the targets. The checkers run for real in the script sandbox; no model calls."""
import importlib.util, json, sys, tempfile, unittest, unittest.mock
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "tests"))
import harness as H

spec = importlib.util.spec_from_file_location("records_survey", ROOT / "atlas-data" / "records" / "survey.py")
S = importlib.util.module_from_spec(spec)
spec.loader.exec_module(S)

NOTEBOOK = """## Result
A new term.
## Claims
### C1
STATEMENT: a(14) = 52.
STATUS: PROVED
TYPE: QUANT
BEYOND: the entry stops at a(13).
PROOF: an exhaustive search over all candidates.
AUDIT: two independent searches agree.
CERTIFICATE: the extremal set, embedded in check_c1.py
CHECK: check_c1.py
CONCERNS: none
### C2
STATEMENT: a(15) >= 60.
STATUS: PROVED
TYPE: QUANT
BEYOND: new.
PROOF: an explicit set.
CHECK: `check_c2.py`.
### C3
STATEMENT: the gap closes.
STATUS: CONJECTURED
TYPE: OTHER
BEYOND: new.
PROOF: evidence.
"""


class Claims(unittest.TestCase):
    def test_certificate_fields_are_read(self):
        c = {x["id"]: x for x in H.parse_claims(NOTEBOOK)}
        self.assertEqual(c["C1"]["check"], "check_c1.py")
        self.assertIn("extremal set", c["C1"]["certificate"])
        self.assertEqual(c["C1"]["concerns"], "none")              # CERTIFICATE and CHECK end the AUDIT field
        self.assertEqual(c["C2"]["check"], "check_c2.py")          # backticks and the full stop are stripped
        self.assertNotIn("check", c["C3"])


class CertificateChecks(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.sb = Path(self.tmp.name)

    def test_the_harness_reruns_each_checker_and_the_referee_sees_it(self):
        (self.sb / "check_c1.py").write_text("S = [1, 2, 4, 8]\nok = all(b % a == 0 for a, b in zip(S, S[1:]))\n"
                                             "print('CERTIFIED' if ok else 'NO')\n")
        (self.sb / "check_c2.py").write_text("print('almost')\n")
        section = H.certificate_checks(self.sb, NOTEBOOK)
        self.assertIn("### C1 certificate: CERTIFIED", section)
        self.assertIn("### C2 certificate: FAILED", section)        # exit 0 but no CERTIFIED line
        self.assertIn("S = [1, 2, 4, 8]", section)                  # the checker's source travels with the verdict
        c = {x["id"]: x for x in H.parse_claims(NOTEBOOK + section)}
        self.assertEqual((c["C1"]["certificate_check"], c["C2"]["certificate_check"]), ("CERTIFIED", "FAILED"))
        self.assertIn("INDEPENDENT CERTIFICATE CHECK", c["C1"]["proof"])
        self.assertNotIn("certificate_check", c["C3"])
        # a second pass replaces the section, never stacks it
        again = H.certificate_checks(self.sb, NOTEBOOK + section)
        self.assertEqual(again.count(H.CERT_SECTION), 1)

    def test_a_missing_or_forbidden_checker_fails(self):
        (self.sb / "check_c1.py").write_text("print(open('x').read())\nprint('CERTIFIED')\n")
        section = H.certificate_checks(self.sb, NOTEBOOK)
        self.assertIn("### C1 certificate: FAILED", section)
        self.assertIn("forbids", section)
        self.assertIn("### C2 certificate: MISSING", section)

    def test_a_checker_outside_the_sandbox_is_not_run(self):
        nb = NOTEBOOK.replace("CHECK: check_c1.py", "CHECK: ../../etc/x.py")
        self.assertIn("### C1 certificate: MISSING", H.certificate_checks(self.sb, nb))


COMPUTE = """## Long computation deep/long_pyr21.py (2026-10-16 09:26 UTC)
What it decides, in the session's words: P(21) exactly, with a witness chain
Process: completed, exit 0, 992 s of 5400 s allowed. A completed process is evidence, not a result.
Last output:
```
t=21 Y_t=89600000000000 |R_t|=3
RESULT: P(20)=7242080052479 (witness [2, 3, 7, 127]); P(21)=64750853277599 (witness [2, 5, 11]); range 89600000000000
```
"""

HITS = {64750853277599: [{"a": "A082449", "name": "smallest prime which takes at least n steps", "keywords": "nonn,more",
                          "terms": 21, "index": 20, "last": True}],
        7242080052479: [{"a": "A082449", "name": "smallest prime which takes at least n steps", "keywords": "nonn,more",
                         "terms": 21, "index": 19, "last": False}]}


class Oeis(unittest.TestCase):
    """2026-10-16: #695's search reported P(21) = 64750853277599 as a record. It is the last listed term of A082449, whose
    next term is open; nothing in the run looked."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.lib = Path(self.tmp.name)
        (self.lib / "COMPUTE.md").write_text(COMPUTE)
        self.asked = []

        def fake(value, timeout=20.0):
            self.asked.append(value)
            return None if value == 1234567 else HITS.get(value, [])
        p = unittest.mock.patch.object(H, "oeis_search", fake)
        p.start()
        self.addCleanup(p.stop)

    def test_a_listed_value_is_known_and_a_wanted_next_term_is_named(self):
        text = H.computations_text(self.lib, oeis=True)
        self.assertIn("RESULT: P(20)=7242080052479", text)
        self.assertIn("64750853277599 is KNOWN to OEIS: A082449", text)
        self.assertIn("the LAST listed term; the entry is marked 'more'", text)
        self.assertEqual(sorted(self.asked), [7242080052479, 64750853277599])   # no witness list, no round bound
        self.assertNotIn("OEIS LOOKUP", H.computations_text(self.lib, oeis=False))   # a benchmark run never looks
        self.assertEqual(H.computations_text(None), "")
        notes = H.oeis_notes("a(5) = 9876543 and 1234567")
        self.assertIn("9876543: in no OEIS entry", notes)
        self.assertIn("1234567: the OEIS lookup failed, so this value is unchecked", notes)   # never "not found"

    def test_the_judges_see_the_lookup_with_the_certificate(self):
        sb = Path(self.tmp.name)
        (sb / "check_c1.py").write_text("print('CERTIFIED')\n")
        nb = NOTEBOOK.replace("STATEMENT: a(14) = 52.", "STATEMENT: P(21) = 64750853277599.")
        section = H.certificate_checks(sb, nb, oeis=True)
        self.assertIn("OEIS LOOKUP of the claim's values", section)
        c = {x["id"]: x for x in H.parse_claims(nb + section)}
        self.assertIn("is KNOWN to OEIS: A082449", c["C1"]["proof"])
        self.assertNotIn("OEIS LOOKUP", H.certificate_checks(sb, nb))

    def test_the_lead_and_the_sessions_see_the_computations_but_the_screen_does_not(self):
        from test_engine import FakeCall, FakeSession, FRONTIER, notebook, judge, LEAN

        def script(purpose, prompt, n):
            if purpose == "engine-frontier":
                return FRONTIER
            if purpose == "engine-settle-screen":
                return "=== GOAL\nSETTLE CHANCE: 0.4\nCompute the next term.\n=== PLAN\n1. go"
            return judge(purpose)
        call = FakeCall(script, cost=0.1)
        sess = FakeSession(lambda l, p: notebook(("PROVED", "QUANT", "x")))
        s = H.EngineSettings(sessions=1, rounds=1, total_budget=30, settle_draws=1, gap_rounds=0,
                             computations=H.computations_text(self.lib, oeis=True))
        H.engine_run(call, sess, "PROBLEM", LEAN, s)
        self.assertNotIn("COMPUTATIONS THE CAMPAIGN RAN", call.prompts("engine-settle-screen")[0])   # the map alone
        self.assertIn("64750853277599 is KNOWN to OEIS", sess.calls[0][1])
        self.assertTrue(any("64750853277599 is KNOWN to OEIS" in p for p in call.prompts("engine-novelty")))


class Objectives(unittest.TestCase):
    def test_record_and_explicit_runs_get_their_map_section_and_the_cli_accepts_them(self):
        self.assertIn("its records", H.OBJECTIVE_BLOCKS["record"])
        self.assertIn("threshold N0", H.OBJECTIVE_BLOCKS["explicit"])
        for k in ("record", "explicit"):
            self.assertIn("SETTLE CHANCE", H.DEEP_OBJECTIVES[k])         # the screen's parser reads the same line
            self.assertIn("=== DECIDE", H.OBJECTIVE_BLOCKS[k])           # so the deciding computation leads round 1
            args = H.build_parser().parse_args(["run", "--problem", "x.json", "--engine-objective", k])
            self.assertEqual(args.engine_objective, k)


class Survey(unittest.TestCase):
    def test_a_wanted_short_sequence_outranks_a_finished_one(self):
        wanted = S.oeis_summary("A000001", {"data": "1,2,3,5", "keyword": "nonn,more", "link": [
            "N. J. A. Sloane, <a href=\"b000001.txt\">Table of n, a(n) for n = 1..9</a>"]})
        done = S.oeis_summary("A000002", {"data": "1,2,3", "keyword": "nonn,fini,full"})
        self.assertEqual((wanted["known_terms"], wanted["more"]), (9, True))
        self.assertTrue(done["complete"])
        self.assertGreater(S.record_score([wanted])[0], S.record_score([done])[0])
        self.assertEqual(S.record_score([done]), (0.0, []))

    def test_page_text_is_the_page_and_its_comments(self):
        d = {"thread": "Forum\n Random\nLet f(n) be ... known for sufficiently large n.\n Proof expositions (0)\n Order by\n"
                       " a comment: verified up to 10^6.\nAll comments are the responsibility of the user"}
        text = S.page_text(d)
        self.assertNotIn("Forum", text)
        self.assertIn("sufficiently large", text)
        self.assertIn("verified up to", text)


mspec = importlib.util.spec_from_file_location("methods_build", ROOT / "atlas-data" / "methods" / "build.py")
M = importlib.util.module_from_spec(mspec)
mspec.loader.exec_module(M)


class Methods(unittest.TestCase):
    CLAIMS = ("There are 2 proof claims (partial or full) for this problem.\n A full proof \nclaimed by Ann (using GPT-6).\n"
              " Summary:\n We prove it by a semigroup argument.\n Notes:\n Lean-checked.\n|\n External link to proof\n |\n"
              " Submitted 2026-07-24 17:04:43 by \n ann\n A partial proof \nclaimed by Bo.\n Summary:\n The odd case.\n"
              " Submitted 2026-08-05 22:46:47 by \n bo\n")

    def test_every_claim_form_is_read_with_its_scope(self):
        cs = M.parse_claims(self.CLAIMS)
        self.assertEqual([(c["by"], c["scope"], c["date"]) for c in cs],
                         [("Ann (using GPT-6)", "full", "2026-07-24"), ("Bo", "partial", "2026-08-05")])
        self.assertEqual(cs[0]["summary"], "We prove it by a semigroup argument.")
        self.assertEqual(cs[0]["notes"], "Lean-checked.")

    def test_the_digest_ranks_neighbours_and_never_the_problem_itself(self):
        entries = [{"problem": 1, "kind": "claim", "tags": ["geometry"], "words": ["isosceles"], "state": "open",
                    "statement": "me", "by": "x", "scope": "full", "summary": "own claim"},
                   {"problem": 2, "kind": "claim", "tags": ["geometry", "distances"], "words": ["isosceles"],
                    "state": "open", "statement": "near", "by": "y", "scope": "partial", "summary": "a lattice"},
                   {"problem": 3, "kind": "solution", "tags": ["primes"], "words": [], "state": "proved",
                    "statement": "far", "summary": "sieve"}]
        d = M.methods_digest(1, entries)
        self.assertIn("#2", d)
        self.assertIn("A partial proof claimed by y", d)
        self.assertNotIn("own claim", d)
        self.assertNotIn("#3", d)                              # nothing shared, so not offered


if __name__ == "__main__":
    unittest.main()
