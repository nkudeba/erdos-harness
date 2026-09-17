"""
Erdos #699, i=3 slice.  Exact-integer exploration.

A counterexample (n,3,j) needs: every prime p>=3 dividing C(n,3) has p ∤ C(n,j).
Primes >=3 dividing C(n,3)=n(n-1)(n-2)/6: every odd prime p>=5 dividing n(n-1)(n-2),
plus p=3 iff 9 | n(n-1)(n-2).  p ∤ C(n,j)  <=>  j is digit-wise dominated by n in base p (Lucas).

Units-digit part of that condition, per prime power p^e || (n-t):  j mod p^e <= t.
Equivalently  A' | j,  B' | j(j-1),  C' | j(j-1)(j-2)  with
  A' = odd part of n     (drop the 3 if 3 || n),
  B' = odd part of n-1   (drop the 3 if 3 || n-1),
  C' = odd part of n-2   (drop the 3 if 3 || n-2).
"""
import sys, math
import numpy as np

N = int(sys.argv[1]) if len(sys.argv) > 1 else 200000

# smallest-prime-factor sieve
spf = np.arange(N + 1, dtype=np.int64)
for p in range(2, int(N ** 0.5) + 1):
    if spf[p] == p:
        blk = spf[p*p::p]
        mask = blk == np.arange(p*p, N + 1, p)
        blk[mask] = p
        spf[p*p::p] = blk

def factor(m):
    f = {}
    while m > 1:
        p = int(spf[m]); f[p] = f.get(p, 0) + 1; m //= p
    return f

def big_part(m):
    """product of p^e over odd p^e || m, dropping 3^1 exactly (3 with e>=2 is kept)."""
    out = 1
    for p, e in factor(m).items():
        if p == 2: continue
        if p == 3 and e == 1: continue
        out *= p ** e
    return out

def constraint_primes(n):
    """odd primes p with p | C(n,3)  (p=3 only if 9 | n(n-1)(n-2))."""
    ps = set()
    for t in range(3):
        for p, e in factor(n - t).items():
            if p == 2: continue
            if p == 3 and e == 1: continue
            ps.add(p)
    return ps

def dominated(j, n, p):
    """Lucas: p ∤ C(n,j)  <=>  every base-p digit of j <= that of n."""
    while j:
        if j % p > n % p: return False
        j //= p; n //= p
    return True

units_survivors = []
full_counterexamples = []
for n in range(8, N + 1):
    A = big_part(n); B = big_part(n - 1); C = big_part(n - 2)
    j = A * ((4 + A - 1) // A)          # smallest multiple of A that is >= 4
    while 2 * j <= n:
        if (j * (j - 1)) % B == 0 and (j * (j - 1) * (j - 2)) % C == 0:
            ps = constraint_primes(n)
            killers = sorted(p for p in ps if not dominated(j, n, p))
            r = (n & -n).bit_length() - 1
            units_survivors.append((n, j, r, n >> r, killers))
            if not killers:
                full_counterexamples.append((n, j))
        j += A

print(f"N = {N}")
print(f"units-digit survivors (A'|j, B'|j(j-1), C'|j(j-1)(j-2), 4<=j<=n/2): {len(units_survivors)}")
print(f"FULL counterexamples to #699 at i=3: {len(full_counterexamples)}  {full_counterexamples}")
print()
print("  n         j        r  a(odd part)   a <= 2.12*sqrt(h)?   killed by (higher-digit carry at p):")
for n, j, r, a, killers in units_survivors:
    A = big_part(n); h = n // (2 * A)
    bound = math.sqrt(4.5 * h + 1)
    print(f"{n:9d} {j:9d} {r:4d} {a:10d}    A'={A:<8d} h={h:<8d} {'ok ' if A <= bound else 'VIOLATES'}  {killers}")
