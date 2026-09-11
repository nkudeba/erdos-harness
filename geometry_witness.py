"""Exact preprocessing for finite blocking-set witnesses; never a Lean certificate.
Projective input is converted to an affine chart with no points at infinity.
"""
from fractions import Fraction as Q
from itertools import combinations

def affine_blocking_witness(blue, red):
    points=[tuple(Q(x) for x in p) for p in [*blue,*red]]
    if not points or any(len(p)!=3 or p==(0,0,0) for p in points):
        raise ValueError('Expected nonzero projective triples')
    # Each point forbids at most two t for L=x+t*y+t²*z. Among 2N+1 choices
    # there is a chart avoiding all N points, even when coordinates are negative.
    t=next(t for t in range(2*len(points)+1) if all(x+t*y+t*t*z for x,y,z in points))
    def convert(p):
        x,y,z=p;d=x+t*y+t*t*z
        # Rows (0,1,0), (0,0,1), (1,t,t²) have determinant 1.
        return (y/d,z/d)
    pts=list(map(convert,points));a=pts[:len(blue)];b=pts[len(blue):]
    if len(set(a))!=len(a) or len(set(b))!=len(b) or set(a)&set(b):raise ValueError('Distinct/disjoint point sets required')
    def area(p,q,r):return (q[0]-p[0])*(r[1]-p[1])-(q[1]-p[1])*(r[0]-p[0])
    noncollinear=next((ids for ids in combinations(range(len(a)),3) if area(*(a[i] for i in ids))),None)
    if noncollinear is None:raise ValueError('Blue points are collinear')
    blockers=[]
    for i,j in combinations(range(len(a)),2):
        k=next((k for k,r in enumerate(b) if area(a[i],a[j],r)==0),None)
        if k is None:raise ValueError(f'Unblocked pair {i},{j}')
        blockers.append([i,j,k])
    return {'certificate_kind':'rational_precheck_only','chart_t':t,'A':[[str(v) for v in p] for p in a],
            'B':[[str(v) for v in p] for p in b],'noncollinear_indices':list(noncollinear),'blockers':blockers,
            'proof_obligation':'Recheck exact coordinates and all incidences in Lean, then prove the real-line bridge and full cardinality claim.'}
