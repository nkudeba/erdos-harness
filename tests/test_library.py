"""library.py: the dated literature library. No network and no model calls here; the parts that decide what may
enter a library (dates, arXiv versions, exclusions) are pure functions."""
import sys, unittest
from datetime import date
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import library as L


def work(when, url=None, title="t", abstract=None):
    w = {"publication_date": when, "title": title, "best_oa_location": {"pdf_url": url, "landing_page_url": url},
         "open_access": {"oa_url": url}, "primary_location": {}}
    if abstract:
        w["abstract_inverted_index"] = {word: [i] for i, word in enumerate(abstract.split())}
    return w


class Dates(unittest.TestCase):
    CUT = date(2026, 3, 27)

    def test_placeholder_january_first_is_not_trusted(self):
        self.assertIsNotNone(L.ambiguous_date(work("2026-01-01"), self.CUT))
        self.assertIsNone(L.ambiguous_date(work("2025-01-01"), self.CUT))      # an earlier year is before the cutoff either way
        self.assertIsNone(L.ambiguous_date(work("2026-02-14"), self.CUT))

    def test_arxiv_month_must_precede_the_cutoff_month(self):
        self.assertIsNotNone(L.ambiguous_date(work("2026-03-02", "https://arxiv.org/abs/2603.01234"), self.CUT))
        self.assertIsNotNone(L.ambiguous_date(work("2025-12-01", "https://arxiv.org/pdf/2604.00001"), self.CUT))
        self.assertIsNone(L.ambiguous_date(work("2026-02-20", "https://arxiv.org/abs/2602.09999"), self.CUT))

    def test_arxiv_ids(self):
        self.assertEqual(L.arxiv_id(work("x", "https://arxiv.org/pdf/1204.6595")), "1204.6595")
        self.assertEqual(L.arxiv_id(work("x", "http://arxiv.org/abs/math/0503001")), "math/0503001")
        self.assertIsNone(L.arxiv_id(work("x", "https://doi.org/10.1/abc")))


class Exclusions(unittest.TestCase):
    def test_problem_identity_patterns(self):
        pats = [r"erdosproblems\.com/(?:forum/thread/)?152\b", r"Erd(?:ő|o|ö)s\s+problem\s*#?\s*152\b"]
        self.assertTrue(L.excluded("see erdosproblems.com/forum/thread/152 for", pats))
        self.assertTrue(L.excluded("This settles Erdős Problem #152.", pats))
        self.assertIsNone(L.excluded("Erdős Problem #1520 is different", pats))
        self.assertIsNone(L.excluded("isolated sums in Sidon sets", pats))

    def test_abstract_reconstruction(self):
        self.assertEqual(L.abstract_of(work("x", abstract="we prove a bound")), "we prove a bound")


if __name__ == "__main__":
    unittest.main()
