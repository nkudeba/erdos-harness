import unittest
from geometry_witness import affine_blocking_witness
class GeometryWitness(unittest.TestCase):
 def test_projective_blockers_become_finite_exact_affine_points(self):
  a=[(0,0,1),(1,0,1),(0,1,1)]
  b=[(1,0,0),(0,1,0),(1,-1,0)]
  r=affine_blocking_witness(a,b)
  self.assertEqual(len(r['blockers']),3)
  self.assertEqual(r['certificate_kind'],'rational_precheck_only')
 def test_missing_blocker_and_duplicate_are_rejected(self):
  for a,b in [([(0,0,1),(1,0,1),(0,1,1)],[(1,0,0)]), ([(0,0,1),(0,0,2)],[])]:
   with self.assertRaises(ValueError):affine_blocking_witness(a,b)
