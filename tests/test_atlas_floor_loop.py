"""The Atlas -> harness feedback loop for search floors (no model, no Lean).

`record_finding.py` can only stamp `problems/erdos_<n>.json` when that file already exists, and it
exists only for the problems the harness has actually attacked (42 of 1,217). Every floor recorded for
any other problem lived in `atlas-data/reviewed.json` and nowhere `search_futility` looked, so the
loop the Atlas is supposed to close was open: #366 (1e22), #287 (4e19), #647 (9.2e18) and #848 (2.6e17)
all had floors far past what a bounded search can enumerate, none had a problem file, and every one of
them would still have spent a search stage re-deriving a known check.
"""
import json, sys, unittest
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import harness as H

ATLAS = json.loads((Path(H.ROOT) / "atlas-data" / "reviewed.json").read_text())


class AtlasFloor(unittest.TestCase):
    def test_unreachable_floor_skips_the_search_without_a_problem_file(self):
        for pid in ("366", "287", "647", "848"):
            with self.subTest(problem=pid):
                self.assertFalse((Path(H.ROOT) / "problems" / f"erdos_{pid}.json").exists(),
                                 f"#{pid} is expected to have no problem file")
                self.assertGreater(float(ATLAS[pid]["search_floor"]), H.SEARCH_REACH)
                futile, why = H.search_futility({}, {"id": pid})
                self.assertTrue(futile, f"#{pid}'s recorded floor must skip the search stage")
                self.assertIn("Atlas", why)

    def test_floor_is_visible_even_when_inside_search_reach(self):
        """Visibility and the skip decision are separate: #7's 1.1e7 is recorded, and correctly
        does NOT skip, because SEARCH_REACH counts enumerable items rather than lcm values."""
        floor, source = H.atlas_search_floor(7)
        self.assertEqual(floor, float(ATLAS["7"]["search_floor"]))
        self.assertIn("published", source)
        self.assertLess(floor, H.SEARCH_REACH)
        self.assertFalse(H.search_futility({}, {"id": "7"})[0])

    def test_problem_file_and_atlas_agree_on_273(self):
        floor, source = H.atlas_search_floor(273)
        filed = json.loads((Path(H.ROOT) / "problems" / "erdos_273.json").read_text())["search_floor"]
        self.assertEqual(floor, float(filed))
        self.assertIn("exhaustive", source)

    def test_absent_or_malformed_is_not_a_floor(self):
        self.assertIsNone(H.atlas_search_floor(None))
        self.assertIsNone(H.atlas_search_floor(999999))
        self.assertFalse(H.search_futility({}, {"id": "999999"})[0])
        self.assertFalse(H.search_futility({}, None)[0])

    def test_largest_floor_wins(self):
        futile, why = H.search_futility({"search_floor": 1e20}, {"id": "273"})
        self.assertTrue(futile)
        self.assertIn("triage", why, "the larger of the triage and Atlas floors must be reported")
        futile, why = H.search_futility({"search_floor": 1.0}, {"id": "366"})
        self.assertTrue(futile)
        self.assertIn("Atlas", why)


if __name__ == "__main__":
    unittest.main()
