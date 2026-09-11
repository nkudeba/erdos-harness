import unittest
import harness as H


class DeclName(unittest.TestCase):
 """stage_partial names its lemmas from the Lean source. A doc comment in front of a lemma once
 made an anchored re.match return None; .group(1) then raised AFTER partial.lean was written but
 BEFORE report.md / state["partial"] / the partial/saved event, so certified lemmas survived on
 disk while the run reported an infrastructure error and lemmas=0."""

 def test_doc_comment_before_the_declaration(self):
  self.assertEqual(H.decl_name("/-- A residue class mod m. -/\nprivate lemma erdos_273_count_le (L : Nat) :"),
                   "erdos_273_count_le")

 def test_plain_attribute_and_modifiers(self):
  self.assertEqual(H.decl_name("theorem foo : True"), "foo")
  self.assertEqual(H.decl_name("@[simp]\nlemma bar : True"), "bar")
  self.assertEqual(H.decl_name("noncomputable def baz : Nat"), "baz")
  self.assertEqual(H.decl_name("protected theorem qux : True"), "qux")

 def test_never_raises_on_a_block_with_no_declaration(self):
  for junk in ("/-! section header -/", "", "-- just a comment", "import Mathlib"):
   self.assertEqual(H.decl_name(junk), "(unnamed)")


if __name__ == "__main__":
 unittest.main()
