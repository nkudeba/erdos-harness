"""
Transfer of the fibre/Fourier test to Erdos #7:
    "Is there a distinct covering system all of whose moduli are odd?"

Same theorem, different admissible set.  Here L is odd and EVERY divisor m > 1 of L is
admissible, so with U = A = {m : m | L, m > 1}:

    sum_{m | L, mu | m} L/m  =  sum_{s | L/mu} L/(mu s)  =  (L/mu) * sigma(L/mu)/(L/mu)
                             =  sigma(L/mu)
    k_A = sum_{m|L, m>1} L/m - L = (sigma(L) - L) - L = sigma(L) - 2L

so the constraint  L/mu <= sum_{m in U, mu|m, m != mu} L/m + k  becomes, writing n = L/mu,

        2n - sigma(n)  <=  sigma(L) - 2L        for every n | L with n < L.

The reciprocal screen is sum_{d|L, d>1} 1/d = sigma(L)/L - 1 >= 1, i.e. L ABUNDANT.
So the candidate set is exactly the ODD ABUNDANT NUMBERS, the smallest being 945.
"""
import sys
from fractions import Fraction

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 2_000_000

# sigma sieve
sig = [0]*(NMAX+1)
for d in range(1, NMAX+1):
    for n in range(d, NMAX+1, d):
        sig[n] += d

def divisors_of(n):
    ds=[]; i=1
    while i*i <= n:
        if n % i == 0:
            ds.append(i)
            if i != n//i: ds.append(n//i)
        i += 1
    return sorted(ds)

def propagate(L):
    """Complete propagation on U = {m | L, m > 1}. Returns (survived?, U, dropped)."""
    U = [m for m in divisors_of(L) if m > 1]
    dropped = []
    while True:
        if not U: return False, U, dropped
        T = sum(L//m for m in U); k = T - L
        bad = None
        for mu in U:
            Amu = sum(L//m for m in U if m != mu and m % mu == 0)
            s = k + Amu - L//mu
            if s < 0 and (bad is None or s < bad[1]): bad = (mu, s)
        if bad is None: return True, U, dropped
        dropped.append(bad)
        U = [m for m in U if m != bad[0]]
        if sum(Fraction(1,m) for m in U) < 1:
            return False, U, dropped

cands = [L for L in range(3, NMAX+1, 2) if sig[L] >= 2*L]
print(f"odd L <= {NMAX:,} passing the reciprocal screen (L abundant): {len(cands)}")
print(f"  smallest {cands[0]}, largest {cands[-1]}\n")

dead = []; alive = []
for L in cands:
    ok, U, dropped = propagate(L)
    (alive if ok else dead).append((L, U, dropped))

print(f"ELIMINATED by the fibre/Fourier test: {len(dead):,} / {len(cands):,}  ({100*len(dead)/len(cands):.2f}%)")
print(f"SURVIVING: {len(alive):,}")
if alive:
    print("\nsmallest surviving candidates:")
    for L, U, dropped in alive[:12]:
        print(f"  L={L:>9}  sigma(L)/L = {sig[L]/L:.5f}  |U|={len(U):<4} dropped={len(dropped)}")
    print(f"\n  => no odd distinct covering system has lcm below {alive[0][0]}")
else:
    print(f"\n  => NO odd distinct covering system has lcm <= {NMAX:,}")
print("\nworked example, the smallest candidate L=945:")
L=945
print(f"  sigma(945)={sig[945]}, abundance sigma-2L = {sig[945]-2*945}")
worst=max(((2*n-sig[n], n) for n in divisors_of(L) if n<L))
print(f"  max over n|L, n<L of 2n-sigma(n) = {worst[0]} at n={worst[1]} (i.e. mu = L/n = {L//worst[1]})")
print(f"  {worst[0]} > {sig[945]-2*945}  ->  ELIMINATED")
