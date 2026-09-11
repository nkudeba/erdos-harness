"""
Erdos #273 -- eliminate candidate lcm values L by the Fourier/root-of-unity test.

For any covering system with distinct moduli m | L, residues a_m, excess count k:
  for every d | L, d > 1, and zeta a primitive d-th root of unity,
        sum_{m in U, d | m} (L/m) zeta^{a_m}  =  sum_{j mod d} e(j) zeta^j,
  where e(j) >= 0 is the excess on the fibre j mod d.  Hence LHS has modulus <= k.

  ELEMENTARY PROOF (no generating functions): split Z/L into the d fibres j mod d.
  A modulus m with d | m sits inside one fibre, contributing L/m to it.  A modulus with
  d doesn't divide m spreads evenly over the 16/g fibres j = a_m mod g (g = gcd(m,d)), whose
  zeta-transform is zeta^{a_m} * sum_t zeta^{g t} = 0.  Each fibre holds L/d points each
  covered >= 1, and the constant part has zero transform, leaving only the excess.

Universal test (independent of which subset U is chosen):
  every U contains the FORCED moduli (1/m > slack), and U is a subset of A, so
        2*max{L/m : m forced, d|m}  -  sum{L/m : m in A, d|m}   >   k_max = floor(slack*L)
  for any single d eliminates L outright.
"""
from fractions import Fraction
from sympy import isprime, divisors, primerange

NMAX = 400_000

# --- pass 1: reciprocal sieve over admissible moduli m = p-1, p >= 5 prime
S = [Fraction(0)] * (NMAX + 1)
adm = [p - 1 for p in primerange(5, NMAX + 1)]
for m in adm:
    f = Fraction(1, m)
    for Lm in range(m, NMAX + 1, m):
        S[Lm] += f
cands = [L for L in range(2, NMAX + 1) if S[L] >= 1]
print(f"L <= {NMAX} passing the reciprocal screen (sum 1/m >= 1): {len(cands)}")
print(f"  smallest {cands[0]}, largest {cands[-1]}")

# --- pass 2: Fourier test
def analyse(L):
    A = [m for m in divisors(L) if m >= 4 and isprime(m + 1)]
    slack = sum(Fraction(1, m) for m in A) - 1
    kmax = int(slack * L)                       # k = L*(sum_U 1/m - 1) <= slack*L
    forced = [m for m in A if Fraction(1, m) > slack]
    best = None
    for d in divisors(L):
        if d == 1: continue
        F = [L // m for m in forced if m % d == 0]
        if not F: continue
        tot = sum(L // m for m in A if m % d == 0)
        bound = 2 * max(F) - tot
        if best is None or bound - kmax > best[1] - best[2]:
            best = (d, bound, kmax, max(F), tot)
    return A, slack, kmax, forced, best

killed, alive = [], []
for L in cands:
    A, slack, kmax, forced, best = analyse(L)
    if best and best[1] > best[2]:
        killed.append((L, best))
    else:
        alive.append((L, slack, kmax, best, len(A), len(forced)))

print(f"\nELIMINATED by the Fourier test: {len(killed)} / {len(cands)}")
for L, b in killed:
    print(f"  L={L:>7}  d={b[0]:<7} max L/m (forced)={b[3]:<6} sum L/m over admissible multiples={b[4]:<7} "
          f"|P| >= {b[1]:<6} > k_max={b[2]}")
print(f"\nSURVIVING: {len(alive)}")
for L, slack, kmax, best, na, nf in alive:
    print(f"  L={L:>7} |A|={na:<3} forced={nf:<3} slack={float(slack):.6f} k_max={kmax:<5} best d-test: {best}")
