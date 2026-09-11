"""
Stronger form of the fibre/Fourier test + a complete propagation algorithm.

TIGHTEST FORM.  For a given modulus set U and divisor d, the test is
    2*max{L/m : m in U, d|m} - sum{L/m : m in U, d|m}  <=  k_U.
Let mu_d = min{m in U : d|m}, so max = L/mu_d.  For mu = mu_d the test AT d = mu reads
    2*L/mu - sum{L/m : m in U, mu|m}  <=  k_U,
and since {m : mu|m} is a SUBSET of {m : d|m} (because d|mu), its sum is smaller, so the
d = mu constraint is TIGHTER.  Hence ranging over mu in U dominates ranging over all d | L:

    U is alive  <=>  for every mu in U:   L/mu  -  sum_{m in U, mu|m, m != mu} L/m  <=  k_U

Writing w_m = L/m, T = sum_U w_m, k_U = T - L, this is
    for every mu in U:   sum_{m in U} c_m^mu  >=  w_mu + L,   c_m^mu = w_m * (2 if mu|m and m!=mu else 1)

COMPLETENESS.  The left side is monotone increasing in U.  So if mu violates its constraint
under the MAXIMAL set A, it violates under every U subset of A that contains it -- mu can be in
NO valid modulus set, and may be deleted outright.  Iterate to a fixed point (unit propagation).
Terminates with either sum 1/m < 1 over the survivors (=> L eliminated, complete) or a maximal
set on which every constraint holds (=> this test cannot eliminate L).
"""
from fractions import Fraction
from sympy import isprime, divisors

def admissible(L):
    return [m for m in divisors(L) if m >= 4 and isprime(m+1)]

def propagate(L, A=None, trace=False):
    U = list(A if A is not None else admissible(L))
    removed = []
    while True:
        if not U: return U, removed, "empty"
        T = sum(L//m for m in U)
        k = T - L
        bad = None
        for mu in U:
            Amu = sum(L//m for m in U if m != mu and m % mu == 0)
            slackmu = k + Amu - L//mu        # >= 0 required
            if slackmu < 0:
                if bad is None or slackmu < bad[1]: bad = (mu, slackmu)
        if bad is None:
            return U, removed, "fixpoint"
        mu, s = bad
        removed.append((mu, s))
        if trace: print(f"    drop m={mu} (deficit {s})")
        U = [m for m in U if m != mu]
        if sum(Fraction(1, m) for m in U) < 1:
            return U, removed, "reciprocal<1"

if __name__ == "__main__":
    import sys
    NMAX = 400_000
    from sympy import primerange
    S = [Fraction(0)]*(NMAX+1)
    for p in primerange(5, NMAX+1):
        m = p-1
        f = Fraction(1, m)
        for Lm in range(m, NMAX+1, m): S[Lm] += f
    cands = [L for L in range(2, NMAX+1) if S[L] >= 1]
    print(f"candidates (sum 1/m >= 1) with L <= {NMAX}: {len(cands)}\n")
    dead, alive = [], []
    for L in cands:
        U, removed, why = propagate(L)
        if why == "reciprocal<1" or why == "empty":
            dead.append((L, len(removed)))
        else:
            alive.append((L, U, removed))
    print(f"ELIMINATED by propagation: {len(dead)} / {len(cands)}")
    print("  " + ", ".join(str(L) for L, _ in dead))
    print(f"\nSURVIVING: {len(alive)}")
    for L, U, removed in alive:
        rec = sum(Fraction(1,m) for m in U)
        print(f"  L={L:>7}  |A|={len(admissible(L)):>3} -> |U|={len(U):>3} after dropping {len(removed):>3}"
              f"   sum 1/m = {float(rec):.6f}   k_max={sum(L//m for m in U)-L}")
