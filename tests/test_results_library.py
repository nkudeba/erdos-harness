"""results_library.py: one run builds on another's validated results and on the openai/math release (2026-10-07).

openai/math's results build on earlier model results; here each run started from its own problem's blackboard alone.
Two guards matter most: no benchmark alias and no time-split dev or test problem may enter the library, and a benchmark
or masked run never reads it."""
import argparse, json, sys, tempfile, unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import harness as H
import results_library as L


def _engine_json(claims):
    return json.dumps({"ledger": claims})


def _claim(cid, st, status="validated-new", sig=2, kind="PROVED"):
    return {"session": "r1s1", "id": cid, "status": kind, "statement": st,
            "validation": {"status": status, "novelty": {"significance": sig}}}


class Entries(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        (self.root / "benchmarks" / "timesplit").mkdir(parents=True)
        (self.root / "benchmarks" / "timesplit" / "pool.json").write_text(json.dumps(
            {"items": [{"problem": "401", "split": "dev"}, {"problem": "152", "split": "train"}]}))
        for name, claims in {"20261007-1-erdos873": [_claim("C1", "F(A,X,4) << X^(1/3-c)"),
                                                      _claim("C2", "a broken one", status="broken")],
                             "20261007-2-erdos401": [_claim("C1", "a dev item's solution")],
                             "20261007-3-erdos893177": [_claim("C1", "an alias's claim")],
                             "20261007-4-erdos152": [_claim("C1", "a train item's lemma", status="valid-routine", sig=1)]}.items():
            d = self.root / "runs" / name / "engine"
            d.mkdir(parents=True)
            (d / "engine.json").write_text(_engine_json(claims))

    def tearDown(self):
        self.tmp.cleanup()

    def test_only_valid_claims_from_catalogue_problems_outside_dev_and_test(self):
        e = L.harness_entries(self.root)
        self.assertEqual(sorted((x["problem"], x["claim"]) for x in e), [(152, "r1s1/C1"), (873, "r1s1/C1")])
        self.assertTrue(all("not human-reviewed" in x["trust"] for x in e))


class Selection(unittest.TestCase):
    ENTRIES = [
        {"source": "harness", "problem": 873, "claim": "r1s1/C1", "status": "validated-new", "significance": 2,
         "statement": "F(A,X,4) << X^(1/3-c) for least common multiples of consecutive terms", "trust": "t"},
        {"source": "openai/math", "family": "160", "title": "Superexponential van der Waerden numbers.",
         "statement": "W_r(k)^(1/k) tends to infinity for van der Waerden numbers", "manuscripts": [], "erdos": [138],
         "lean": True, "trust": "Lean-formalized in the release, not checked by us"},
        {"source": "openai/math", "family": "128", "title": "Shortest common superstring.",
         "statement": "a factor-two approximation algorithm", "manuscripts": [], "erdos": [], "lean": True, "trust": "t"},
    ]

    def test_own_results_first_and_a_mapped_family_always(self):
        own = L.select("least common multiple of consecutive terms", [], self.ENTRIES, 6, problem=873)
        self.assertEqual(own[0]["claim"], "r1s1/C1")
        self.assertNotIn("128", [e.get("family") for e in own])          # unrelated: under the overlap bar
        mapped = L.select("Prove that W(k)^(1/k) -> infinity", [], self.ENTRIES, 6, problem=138)
        self.assertEqual(mapped[0]["family"], "160")

    def test_render_labels_every_entry(self):
        r = L.render(self.ENTRIES[:2])
        self.assertIn("[harness #873 r1s1/C1, validated-new, significance 2", r)
        self.assertIn("[openai/math family 160, Lean-formalized in the release, not checked by us]", r)
        self.assertIn("never treat an unverified one as proved", r)
        self.assertEqual(L.render([]), "")

    def test_the_release_map_is_indexed(self):
        md = ("**160. Superexponential van der Waerden numbers.** Resolves Erdős's question. ([Lean](lean/docs/160.md))\n"
              "</td>\n</tr></tbody>\n&emsp;[Superexponential van der Waerden numbers](preprints/X/paper.pdf)\n\n"
              "**161. Counterexamples to Sidorenko.** Disproves it.\n</td>\n")
        with tempfile.TemporaryDirectory() as d:
            src, out = Path(d) / "CONTENTS.md", Path(d) / "families.json"
            src.write_text(md)
            self.assertEqual(L.index_openai(src, out), 2)
            fams = json.loads(out.read_text())["families"]
            self.assertEqual([(f["family"], f["lean"]) for f in fams], [("160", True), ("161", False)])
            self.assertEqual(fams[0]["manuscripts"][0]["title"], "Superexponential van der Waerden numbers")
            self.assertIn("Apache", json.loads(out.read_text())["license"])


class HarnessFlag(unittest.TestCase):
    def _h(self, **args):
        h = H.Harness.__new__(H.Harness)
        h.problem = {"id": "138", "statement": "Prove that W(k)^(1/k) -> infinity", "tags": []}
        h.state = {"statement": "theorem erdos_138 : True := by sorry"}
        h.args = argparse.Namespace(results_library="on", benchmark=False, masked=False, **args)
        events = []
        h.log = type("L", (), {"event": lambda self, *a, **k: events.append((a, k))})()
        return h, events

    def test_off_by_default(self):
        h, _ = self._h()
        h.args.results_library = "off"
        self.assertEqual(h._results_library_block(), "")

    def test_never_in_a_benchmark_or_masked_run(self):
        for kw in ({"benchmark": True}, {"masked": True}):
            h, ev = self._h()
            for k, v in kw.items():
                setattr(h.args, k, v)
            self.assertEqual(h._results_library_block(), "")
            self.assertTrue(any(k.get("skipped") for a, k in ev))
        h, _ = self._h()
        h.state["benchmark"] = True
        self.assertEqual(h._results_library_block(), "")

    def test_on_it_carries_the_relevant_release_family(self):
        h, ev = self._h()
        block = h._results_library_block()
        self.assertIn("RESULTS LIBRARY", block)
        self.assertIn("openai/math family 160", block)


if __name__ == "__main__":
    unittest.main()
