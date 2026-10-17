# Checker for C2 (and the upper-bound half of C1):
#  * the embedded chains are prime chains from 2 (p_{i+1} = m_i p_i + 1), every term proved prime by
#    (a) trial division for p < 10^6, else (b) Pocklington with F = p_i (needs p_i > m_i, so p_i^2 > p_{i+1}),
#    independently also PARI isprime (rigorous below 2^64);
#  * H(p) (Pratt-tree height = longest chain ending at p, H(2)=1) by exact recursive factorisation of p-1;
#  * g(p) = number of steps of p -> gpf(p-1) to reach 2 (the statistic of OEIS A082449).
from cypari2 import Pari
from functools import lru_cache
from math import gcd, isqrt
pari = Pari()
C22 = [2, 5, 11, 89, 179, 359, 719, 1439, 25903, 103613, 621679, 2486717, 14920303, 179043637, 716174549,
       1432349099, 25782283783, 1082855918887, 10828559188871, 21657118377743, 433142367554861, 866284735109723]
C23 = [2, 5, 11, 89, 179, 359, 719, 1439, 2879, 414577, 1658309, 3316619, 26532953, 53065907, 4457536189,
       106980868537, 641885211223, 3851311267339, 92431470416137, 369725881664549, 739451763329099,
       1478903526658199, 2957807053316399]
C24 = C23 + [94649825706124769]          # m = 32: P(24) <= 94649825706124769 (deep/C3 had 115504631269039577)
def trial(n):
    if n < 2: return False
    return all(n % d for d in range(2, isqrt(n) + 1))
def pock(N, F):
    # N-1 = F*R, F prime, F^2 > N  =>  N prime iff some a with a^(N-1)=1, gcd(a^((N-1)/F)-1, N)=1
    assert (N - 1) % F == 0 and F * F > N
    for a in range(2, 200):
        if pow(a, N - 1, N) != 1: return False
        if gcd(pow(a, (N - 1) // F, N) - 1, N) == 1: return True
    return False
def chain_ok(C):
    ok = C[0] == 2
    for i in range(len(C) - 1):
        ok &= C[i] < C[i + 1] and (C[i + 1] - 1) % C[i] == 0
    for i, p in enumerate(C):
        if p < 10**6: ok &= trial(p)
        else: ok &= pock(p, C[i - 1])
        ok &= bool(pari.isprime(p))
    return ok
def pf(n): return [int(x) for x in pari.factor(n)[0]] if n > 1 else []
@lru_cache(None)
def H(p): return 1 if p == 2 else 1 + max(H(r) for r in pf(p - 1))
@lru_cache(None)
def g(p): return 0 if p == 2 else 1 + g(max(pf(p - 1)))
allok = True
for C, k in ((C22, 22), (C23, 23), (C24, 24)):
    ok = chain_ok(C) and len(C) == k and H(C[-1]) == k and g(C[-1]) == k - 1
    print("k=%d last=%d chain/Pocklington ok, H=%d, g=%d -> %s" % (k, C[-1], H(C[-1]), g(C[-1]), ok))
    print("  multipliers:", [(C[i + 1] - 1) // C[i] for i in range(len(C) - 1)])
    allok &= ok
# A082449(n) = min{p : g(p) >= n}; g(p) <= H(p)-1 so A082449(n) >= P(n+1).  Since g(C23[-1]) = 22,
# A082449(22) <= 2957807053316399 < 11407852252734739.
allok &= g(C23[-1]) >= 22 and C23[-1] < 11407852252734739 and C24[-1] < 115504631269039577
print("A082449(22) <= %d: %s" % (C23[-1], allok))
if allok: print("CERTIFIED")
