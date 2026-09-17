"""Deliverable 2 of the covering-systems library: a tagged problem must REACH the library.

The compounding thesis is that the second run in a cluster starts from the first one's certified
machinery. That only happens if the module lands in the run's import header AND the prompts say so;
a library nobody is told about is a library nobody uses.
"""
import json, re, tempfile, unittest
from pathlib import Path

import harness as H


class ClusterLibraryResolution(unittest.TestCase):
    def test_a_tagged_problem_gets_the_cluster_module(self):
        prob = {"id": "273", "tags": ["number theory", "covering systems"]}
        self.assertIn("Formal.Library.CoveringSystems", H.cluster_libraries(prob))

    def test_the_tag_match_is_case_and_space_insensitive(self):
        prob = {"id": "7", "tags": ["  Covering Systems "]}
        self.assertIn("Formal.Library.CoveringSystems", H.cluster_libraries(prob))

    def test_an_untagged_problem_gets_nothing(self):
        self.assertEqual(H.cluster_libraries({"id": "1", "tags": ["ramsey theory"]}), [])
        self.assertEqual(H.cluster_libraries({"id": "1"}), [])

    def test_a_table_entry_with_no_source_file_is_dropped(self):
        """`import` of a module that does not exist is a hard Lean error, so a stale table entry would
        fail every check in the cluster rather than the one attempt that wanted the library."""
        saved = dict(H.CLUSTER_LIBRARIES)
        try:
            H.CLUSTER_LIBRARIES["ghost cluster"] = "Formal.Library.NoSuchModule"
            self.assertEqual(H.cluster_libraries({"id": "1", "tags": ["ghost cluster"]}), [])
        finally:
            H.CLUSTER_LIBRARIES.clear()
            H.CLUSTER_LIBRARIES.update(saved)

    def test_the_module_source_actually_exists_where_the_table_says(self):
        for module in H.CLUSTER_LIBRARIES.values():
            self.assertTrue(H.library_module_path(module).exists(), module)


class ImportHeaderCarriesTheLibrary(unittest.TestCase):
    def test_compose_emits_the_library_import_line(self):
        imports = list(H.DEFAULT_IMPORTS) + ["Formal.Library.CoveringSystems"]
        src = H.compose("theorem t : True := trivial", imports)
        self.assertIn("import Formal.Library.CoveringSystems", src)

    def test_library_import_survives_a_body_that_declares_its_own_imports(self):
        imports = list(H.DEFAULT_IMPORTS) + ["Formal.Library.CoveringSystems"]
        src = H.compose("-- IMPORTS: Mathlib.Data.Real.Basic\ntheorem t : True := trivial", imports)
        self.assertIn("import Formal.Library.CoveringSystems", src)
        self.assertIn("import Mathlib.Data.Real.Basic", src)


class LibraryNoteNamesWithoutPasting(unittest.TestCase):
    def test_empty_when_there_is_no_library(self):
        self.assertEqual(H.library_note([]), "")

    def test_declarations_are_fully_qualified_names(self):
        decls = H.library_declarations("Formal.Library.CoveringSystems")
        self.assertIn("Erdos.Covering.CongruenceFamily.not_exact_of_distinctModuli", decls)
        self.assertIn("Erdos.Covering.CongruenceFamily.rootOfUnity_identity", decls)
        self.assertIn("Erdos.Covering.Erdos273.not_dvd_360", decls)

    def test_no_proof_text_is_pasted(self):
        """The module is imported, not inlined: the note must stay a catalogue. Proof tactics in the
        note would mean paying for the same text on every call and inviting restatement over reuse."""
        note = H.library_note(["Formal.Library.CoveringSystems"])
        source = H.library_module_path("Formal.Library.CoveringSystems").read_text()
        self.assertLess(len(note), len(source) // 3)
        for tactic in (":= by", "refine ", "Finset.sum_nbij'", "exact_mod_cast"):
            self.assertNotIn(tactic, note)

    def test_a_missing_module_yields_no_declarations(self):
        self.assertEqual(H.library_declarations("Formal.Library.NoSuchModule"), [])


class PromptsAnnounceTheLibrary(unittest.TestCase):
    """Acceptance criterion: 'the prove prompt states the library is importable'."""

    LIB = ["Formal.Library.CoveringSystems"]

    def test_prove_prompt_carries_the_block(self):
        note = H.library_note(self.LIB)
        prompt = H.prove_prompt({"id": "273", "statement": "s"}, "theorem erdos_273 : True := by sorry",
                                "", [], "", 1, 1, H.DEFAULT_IMPORTS + self.LIB, library=note)
        self.assertIn("import Formal.Library.CoveringSystems", prompt)
        self.assertIn("Erdos.Covering.CongruenceFamily.density", prompt)

    def test_agentic_prompt_carries_the_block(self):
        note = H.library_note(self.LIB)
        prompt = H.agentic_prompt({"id": "273", "statement": "s"}, "theorem erdos_273 : True := by sorry",
                                  "", "", "", H.DEFAULT_IMPORTS + self.LIB, 40, library=note)
        self.assertIn("import Formal.Library.CoveringSystems", prompt)

    def test_reduce_prompt_has_a_library_slot(self):
        filled = H.REDUCE_PROMPT.format(pid="273", statement_en="s", notes="n", statement="t",
                                        check_seconds=45, modules="math",
                                        library=H.library_note(self.LIB))
        self.assertIn("import Formal.Library.CoveringSystems", filled)

    def test_prompts_stay_clean_when_there_is_no_library(self):
        prompt = H.prove_prompt({"id": "1", "statement": "s"}, "theorem erdos_1 : True := by sorry",
                                "", [], "", 1, 1, H.DEFAULT_IMPORTS)
        self.assertNotIn("ALREADY-FORMALISED CLUSTER LIBRARY", prompt)


class LibraryContextIsSafeOnAPartialHarness(unittest.TestCase):
    def test_no_libraries_attribute_is_not_a_crash(self):
        """Stages are exercised on `Harness.__new__` objects in other tests; the accessor must not
        assume __init__ ran."""
        h = H.Harness.__new__(H.Harness)
        self.assertEqual(h.library_context(), "")


if __name__ == "__main__":
    unittest.main()


class BinomialCoefficientsCluster(unittest.TestCase):
    """The `binomial coefficients` tag covers 22 catalogue problems (#175, #376-#379, #384, #386,
    #387, #396, #397, #683-#685, #698-#700, #730, #731, #849, #1093-#1095) -- the same cluster size
    as covering systems. The module banks what the #699 runs certified plus the Lucas-theorem
    consequences, so a later problem in the cluster imports them by name instead of re-deriving them.

    It earned its place in the table by building sorry-free: all 11 declarations print
    `[propext, Classical.choice, Quot.sound]` with no `sorryAx` (checked 2026-09-12). One of them,
    `residue_route_fails`, did NOT before repair -- it was accepted from a continuation report that
    cited a verification log which had never been written."""

    MODULE = "Formal.Library.BinomialCoefficients"

    def test_tag_maps_to_the_module(self):
        self.assertEqual(H.CLUSTER_LIBRARIES.get("binomial coefficients"), self.MODULE)

    def test_699_and_its_neighbours_pick_it_up(self):
        for tags in (["number theory", "binomial coefficients"], ["Binomial Coefficients"]):
            self.assertIn(self.MODULE, H.cluster_libraries({"tags": tags}))

    @staticmethod
    def _code_only(src: str) -> str:
        """Strip block and line comments: the module DOCUMENTS a `sorryAx` repair, and a bare
        substring grep would flag that prose as if the proofs themselves had a hole."""
        src = re.sub(r"/-.*?-/", "", src, flags=re.S)
        return "\n".join(l.split("--")[0] for l in src.split("\n"))

    def test_module_file_exists_and_is_sorry_free(self):
        p = Path(H.FORMAL) / "Formal" / "Library" / "BinomialCoefficients.lean"
        self.assertTrue(p.exists(), "the table names a module that is not in the repo")
        code = self._code_only(p.read_text())
        for banned in H.BANNED_IN_PROOFS:
            self.assertNotIn(banned, code, f"library proof text contains `{banned.strip()}`")

    def test_library_states_its_provenance_and_does_not_claim_a_resolution(self):
        src = (Path(H.FORMAL) / "Formal" / "Library" / "BinomialCoefficients.lean").read_text()
        self.assertIn("Nothing here is new mathematics", src)
        self.assertIn("OPEN", src, "the module must say #699 is open")
        self.assertIn("Lucas", src, "published results must be attributed")

    def test_it_records_that_the_residue_route_is_not_necessary(self):
        """The one-way limitation is the thing a later run most needs to know: `block_prime` only
        ever yields a prime p > j, and at (10,3,5) the shared prime is p = 3 = i."""
        src = (Path(H.FORMAL) / "Formal" / "Library" / "BinomialCoefficients.lean").read_text()
        self.assertIn("sufficient, not necessary", src)
        self.assertIn("counterexample_forces_smooth_block", src)
