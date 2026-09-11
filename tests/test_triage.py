"""Triage routing, statement shape, search-script safety screen, and problem-page parsing (no model, no Lean)."""
import argparse, sys, unittest
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import harness as H

A = argparse.Namespace(mode=None, allow_construct=False, allow_research=False)


class Routing(unittest.TestCase):
    def test_rules(self):
        self.assertEqual(H.decide_mode({"status": "resolved", "depth": "trivial", "shape": "witness"}, A)[0], "fast")
        self.assertEqual(H.decide_mode({"status": "resolved", "depth": "elementary", "shape": "finite-check"}, A)[0], "fast")
        self.assertEqual(H.decide_mode({"status": "open", "shape": "witness"}, A)[0], "search-first")
        self.assertEqual(H.decide_mode({"status": "open", "shape": "universal", "computable": True}, A)[0], "search-first")
        self.assertEqual(H.decide_mode({"status": "open", "shape": "extremal-bound"}, A)[0], "fast")
        self.assertEqual(H.decide_mode({"status": "open", "shape": "extremal-bound"},
                                       argparse.Namespace(mode=None, allow_construct=True, allow_research=False))[0], "construct")
        self.assertEqual(H.decide_mode({"status": "open", "depth": "research", "shape": "structural"}, A)[0], "fast")
        self.assertEqual(H.decide_mode({"status": "open", "depth": "research", "shape": "structural"},
                                       argparse.Namespace(mode=None, allow_construct=False, allow_research=True))[0], "research")
        self.assertEqual(H.decide_mode({}, argparse.Namespace(mode="search-first", allow_construct=False, allow_research=False))[0], "search-first")
        # the site's own finite-computation class wins over the model's guess for open problems
        self.assertEqual(H.decide_mode({"status": "open", "shape": "universal", "depth": "research", "computable": False}, A,
                                       {"class": "falsifiable"})[0], "search-first")
        self.assertEqual(H.decide_mode({"status": "resolved", "depth": "trivial"}, A, {"class": "verifiable"})[0], "fast")


class SearchFutility(unittest.TestCase):
    """A site 'falsifiable/verifiable/decidable' class promises a FINITE witness, not a reachable one.

    Erdős #287 is the motivating case: published prime-chain certificates put any counterexample above
    4e19 with ~7e19 terms, so the bounded Python search can only re-derive a known check. Before this gate
    the site class routed it straight to search-first.
    """

    def test_floor_parsing(self):
        f = H.known_search_floor
        self.assertIsNone(f(""))
        self.assertIsNone(f("a perfectly ordinary problem statement with no exhaustive check"))
        self.assertEqual(f("no counterexample below 4x10^19"), 4e19)
        self.assertEqual(f(r"any counterexample must have $n_1 > 3.9 \times 10^{19}$"), 3.9e19)
        self.assertEqual(f("verified up to 10^9 by exhaustive search"), 1e9)
        self.assertEqual(f("checked for all n below 4.2e12"), 4.2e12)
        self.assertEqual(f("no solutions below 409938931585744826"), 409938931585744826.0)
        # the largest bound in the text wins
        self.assertEqual(f("verified up to 10^6; later no counterexample below 10^15"), 1e15)
        # a bare magnitude with no 'already checked' context must NOT count
        self.assertIsNone(f("the construction uses 10^20 points"))

    def test_futility_gate(self):
        far = {"status": "open", "shape": "universal", "search_floor": 4e19}
        near = {"status": "open", "shape": "universal", "search_floor": 10 ** 6}
        self.assertTrue(H.search_futility(far)[0])
        self.assertFalse(H.search_futility(near)[0])
        self.assertFalse(H.search_futility({"status": "open"})[0])
        # literature text alone is enough
        self.assertTrue(H.search_futility({}, {"notes": "no counterexample below 4x10^19"})[0])
        self.assertTrue(H.search_futility({}, None, "any counterexample must exceed 10^25")[0])
        # a string floor from the model is parsed too
        self.assertTrue(H.search_futility({"search_floor": "4x10^19"})[0])

    def test_routing_skips_futile_search(self):
        a = {"status": "open", "shape": "universal", "depth": "research", "search_floor": 4e19}
        mode, reason = H.decide_mode(a, A, {"class": "falsifiable"})
        self.assertEqual(mode, "fast")
        self.assertIn("search skipped", reason)
        # ... and the same target without the floor still routes to the search
        b = dict(a); b.pop("search_floor")
        self.assertEqual(H.decide_mode(b, A, {"class": "falsifiable"})[0], "search-first")
        # a witness-shaped target is gated too
        c = {"status": "open", "shape": "witness", "search_floor": 10 ** 30}
        self.assertEqual(H.decide_mode(c, A)[0], "fast")
        # an explicit --mode override still wins over the gate
        forced = argparse.Namespace(mode="search-first", allow_construct=False, allow_research=False)
        self.assertEqual(H.decide_mode(a, forced, {"class": "falsifiable"})[0], "search-first")
        # research routing is preserved, with the skip noted
        r = argparse.Namespace(mode=None, allow_construct=False, allow_research=True)
        mode, reason = H.decide_mode(a, r, {"class": "falsifiable"})
        self.assertEqual(mode, "research")
        self.assertIn("search skipped", reason)


class Shape(unittest.TestCase):
    def test_shapes(self):
        self.assertEqual(H.statement_shape("theorem erdos_399 :\n    ∃ n x y k : ℕ, 1 < x * y ∧ (n ! = x ^ k) := by\n  sorry"), "witness")
        self.assertEqual(H.statement_shape("theorem erdos_645 (c : ℕ → Bool) :\n    ∃ x d : ℕ, 0 < x ∧ c x = c (x + d) := by\n  sorry"), "witness")
        self.assertEqual(H.statement_shape("theorem erdos_t : ∀ n : ℕ, n + 0 = n := by\n  sorry"), "counterexample")
        self.assertEqual(H.statement_shape("theorem erdos_u (n : ℕ) (h : 2 ≤ n) : n ^ 2 ≠ 7 := by\n  sorry"), "counterexample")
        self.assertEqual(H.statement_shape("theorem erdos_363 :\n    Set.Infinite {S : Finset ℕ | S.card = 4} := by\n  sorry"), "witness")


class Safety(unittest.TestCase):
    def test_python_screen(self):
        self.assertIsNone(H.unsafe_python("import math, itertools\nfrom fractions import Fraction\nprint(math.factorial(10))"))
        self.assertEqual(H.unsafe_python("import os\n"), "import os")
        self.assertEqual(H.unsafe_python("from pathlib import Path"), "from pathlib import")
        self.assertIsNotNone(H.unsafe_python("x = open('f')"))
        self.assertIsNotNone(H.unsafe_python("import math\nprint(__import__('os'))"))
        self.assertIsNotNone(H.unsafe_python("import sys\n"))


class PageParse(unittest.TestCase):
    def test_parse_399(self):
        info = H.parse_problem_page((Path(__file__).parent / "fixtures" / "erdos399.html").read_text())
        self.assertTrue(info["status_line"].startswith("DISPROVED"))
        self.assertIn("n! = x^k", info["statement"])
        self.assertIn("Barfield", info["discussion"])
        self.assertEqual(info["comments"], 0)

    def test_parse_1193_flags(self):
        info = H.parse_problem_page((Path(__file__).parent / "fixtures" / "erdos1193.html").read_text())
        self.assertIn("lower density", info["statement"])
        self.assertTrue({"presumably", "trivial"} & set(info["flags"]))


if __name__ == "__main__":
    unittest.main()
