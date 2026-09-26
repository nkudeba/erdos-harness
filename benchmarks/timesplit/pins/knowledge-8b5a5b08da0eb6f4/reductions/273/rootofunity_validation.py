"""Step 2: the Mirsky-Newman generating function for a NEAR-exact cover, validated before use.

A family of classes (a_i mod m_i) covering Z with multiplicity c(n) at n satisfies, as formal series,
    sum_i z^{a_i}/(1 - z^{m_i})  =  sum_{n>=0} c(n) z^n .
If the family covers every n at least once and the total excess is the multiset E (residues mod L
counted with their extra multiplicity, L = lcm), then
    sum_i z^{a_i}/(1 - z^{m_i})  =  1/(1-z)  +  sum_{r in E} z^r/(1 - z^L) .            (*)

VALIDATION comes first: check (*) numerically on covering systems whose answer is already known.
Only then use it.
"""
import cmath, itertools, random
from fractions import Fraction

def multiplicity(classes, L):
    c = [0] * L
    for a, m in classes:
        for n in range(L):
            if (n - a) % m == 0:
                c[n] += 1
    return c

def lhs(classes, z):
    return sum(z ** a / (1 - z ** m) for a, m in classes)

def rhs(excess, L, z):
    return 1 / (1 - z) + sum(z ** r for r in excess) / (1 - z ** L)

def lcm(xs):
    from math import gcd
    out = 1
    for x in xs:
        out = out * x // gcd(out, x)
    return out

def check(name, classes):
    L = lcm([m for _, m in classes])
    c = multiplicity(classes, L)
    if min(c) < 1:
        print(f"  {name}: NOT a cover (residue {c.index(min(c))} uncovered) -- skipped")
        return
    excess = [r for r in range(L) for _ in range(c[r] - 1)]
    worst = 0.0
    for _ in range(6):
        z = cmath.exp(2j * cmath.pi * random.random()) * random.uniform(0.3, 0.8)
        if any(abs(1 - z ** m) < 1e-9 for _, m in classes) or abs(1 - z) < 1e-9:
            continue
        worst = max(worst, abs(lhs(classes, z) - rhs(excess, L, z)))
    print(f"  {name}: L={L}, overlap={len(excess)}, max |LHS-RHS| = {worst:.2e}"
          f"  {'OK' if worst < 1e-8 else 'MISMATCH'}")

print("validating identity (*) on known covering systems")
check("classic {2,3,4,6,12}", [(0, 2), (0, 3), (1, 4), (5, 6), (7, 12)])
check("exact cover {2,4,4} (repeats 4)", [(0, 2), (1, 4), (3, 4)])
check("trivial {1}", [(0, 1)])
check("Selfridge-style divisors of 12", [(0, 2), (0, 3), (1, 4), (1, 6), (11, 12)])
