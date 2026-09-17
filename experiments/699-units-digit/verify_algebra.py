"""
Exact-integer check of every non-vacuous step in the written i=3 reduction (this session).
For all n with 4|n, 8<=n<=NMAX, and all 1<=j<=n/2 with A'|j  (k=j/A', h=n/(2A')):
  (E1)  B' | j(j-1)          <=>  B' | k(2h-k)
  (E2)  C' | j(j-1)(j-2)     <=>  C' | k(h-k)(2h-k)
  (E3)  gcd(B',C')=1,  gcd(2h,B')=1,  gcd(h,C')=1,  B'=(n-1)/e, C'=(n/2-1)/e'  with e,e' in {1,3}
  (E4)  k=h (j=n/2) never satisfies B' | k(2h-k)   [so j<n/2]
  (E5)  whenever B' | k(2h-k):  with d=h-k, l=(h^2-d^2)/B' is a positive integer, l <= (h^2-1)/B'
        and  C' | k(h-k)(2h-k)  <=>  C' | d*l
Also: for odd n and for n ≡ 2 mod 4 (r=1), U(3) has no solution (direct check).
"""
import sys
from math import gcd
NMAX = int(sys.argv[1])

def bigpart(m):
    while m % 2 == 0: m //= 2
    if m % 3 == 0 and m % 9 != 0: m //= 3
    return m

cnt = {k: 0 for k in ["pairs", "E1", "E2", "E4", "E5", "B_hits"]}
for n in range(8, NMAX + 1):
    A, B, C = bigpart(n), bigpart(n - 1), bigpart(n - 2)
    if n % 4 != 0:
        # odd n or r=1: U(3) must have no solutions
        j = A * ((4 + A - 1) // A)
        while 2 * j <= n:
            assert not ((j*(j-1)) % B == 0 and (j*(j-1)*(j-2)) % C == 0), (n, j)
            j += A
        continue
    h = n // (2 * A)
    assert gcd(B, C) == 1 and gcd(2*h, B) == 1 and gcd(h, C) == 1
    assert B == (n-1) // (3 if (n-1) % 3 == 0 and (n-1) % 9 else 1)
    assert C == (n//2 - 1) // (3 if (n//2-1) % 3 == 0 and (n//2-1) % 9 else 1)
    for k in range(1, h + 1):
        j = k * A; cnt["pairs"] += 1
        e1a = (j*(j-1)) % B == 0; e1b = (k*(2*h-k)) % B == 0
        assert e1a == e1b, ("E1", n, j); cnt["E1"] += 1
        e2a = (j*(j-1)*(j-2)) % C == 0; e2b = (k*(h-k)*(2*h-k)) % C == 0
        assert e2a == e2b, ("E2", n, j); cnt["E2"] += 1
        if k == h:
            assert not e1b, ("E4", n); cnt["E4"] += 1
        elif e1b:
            cnt["B_hits"] += 1
            d = h - k; num = h*h - d*d
            assert num % B == 0 and num > 0
            l = num // B; assert 1 <= l <= (h*h - 1) // B
            assert e2b == ((d*l) % C == 0), ("E5", n, j); cnt["E5"] += 1
            if e2b:
                # a U(3) solution would land here; the bound must then hold
                assert A*A < 4.5*h + 2.25, ("BOUND", n, j)
print("ALL-CHECKS-PASSED", NMAX, cnt)
