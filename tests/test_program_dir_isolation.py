import types, unittest
from pathlib import Path
import harness as H


class ProgramDirIsolation(unittest.TestCase):
 """--open runs a research program for BOTH directions at once. They must not share
 programs/erdos_<n>/ or they race on cycles/, Lemmas.lean and ledger.jsonl: with a
 second-resolution cycle name both directions land in the same cycle dir, both append
 identically named lemmas to one Lemmas.lean, and the second sub-goal dies with
 FileNotFoundError. Observed live on #677 (2026-09-10)."""

 def _runner(self, direction):
  r = types.SimpleNamespace()
  r.problem = {"id": "677"}
  r.direction = direction
  r._program_dir = types.MethodType(H.Harness._program_dir, r)
  r._program_module_suffix = types.MethodType(H.Harness._program_module_suffix, r)
  return r

 def test_pos_and_neg_get_distinct_program_dirs(self):
  pos, neg, plain = (self._runner("pos"), self._runner("neg"), self._runner(None))
  dpos, dneg, dplain = pos._program_dir(), neg._program_dir(), plain._program_dir()
  self.assertNotEqual(dpos, dneg)
  self.assertEqual(dpos.parent, dneg.parent)
  self.assertEqual(dplain, dpos.parent)          # a non-open run keeps the historical path
  for d in (dpos, dneg):
   self.assertTrue(d.is_dir())

 def test_pos_and_neg_get_distinct_lemma_modules(self):
  suffixes = {d: self._runner(d)._program_module_suffix() for d in ("pos", "neg", None)}
  self.assertEqual(suffixes[None], "")
  self.assertNotEqual(suffixes["pos"], suffixes["neg"])
  self.assertTrue(all(s.isalnum() for s in suffixes.values() if s))   # valid Lean identifier tail


if __name__ == "__main__":
 unittest.main()
