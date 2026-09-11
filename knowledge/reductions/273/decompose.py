"""Erdos #273 by decomposition, not brute force.

For a candidate lcm L, let A(L) = admissible moduli dividing L (m = p-1, p >= 5 prime) and
slack = sum_{m in A} 1/m - 1.  Then:

  * every m with 1/m > slack is FORCED into any solution (dropping it puts the sum below 1);
  * the total overlap of the chosen classes is exactly sum_{used} L/m - L, and is at most slack*L,
    so when slack*L is small the classes must almost exactly TILE Z/L;
  * the choice of which non-forced moduli to use is a tiny subset enumeration, not part of the SAT;
  * a subset whose overlap is exactly 0 would be an EXACT covering system with distinct moduli, which
    cannot exist for >= 2 congruences (Mirsky-Newman / Davenport-Rado: the largest modulus of a
    disjoint covering system must repeat).  Excluded on paper, no search.

Each surviving subset fixes the modulus set, so every modulus is used exactly once: EXACTLY-one
residue per modulus rather than at-most-one, which propagates far harder than the generic encoding.
"""
import sys, time
from fractions import Fraction
from itertools import combinations
from sympy import isprime, divisors
from pysat.formula import IDPool, CNF
from pysat.card import CardEnc, EncType
from pysat.solvers import Cadical153

def admissible(L): return [d for d in divisors(L) if d >= 4 and isprime(d + 1)]

def structure(L):
    ms = admissible(L)
    slack = sum(Fraction(1, m) for m in ms) - 1
    if slack < 0:
        return None
    forced = [m for m in ms if Fraction(1, m) > slack]
    free = [m for m in ms if m not in forced]
    base = sum(L // m for m in forced)
    subsets = []
    if len(free) <= 24:
        for r in range(len(free) + 1):
            for sub in combinations(free, r):
                cov = base + sum(L // m for m in sub)
                if cov >= L:
                    subsets.append((cov - L, forced + list(sub)))
        subsets.sort(key=lambda t: (t[0], len(t[1])))
    return {"L": L, "ms": ms, "slack": slack, "forced": forced, "free": free,
            "budget": float(slack * L), "subsets": subsets}

def decide_subset(L, U, overlap, cap=None):
    """Residues only: the modulus set U is fixed, so each modulus gets EXACTLY one class."""
    pool, cnf = IDPool(), CNF()
    v = lambda m, a: pool.id(("x", m, a))
    pin = min(U)
    for m in U:
        lits = [v(m, a) for a in range(m)]
        cnf.append(lits)                                            # at least one
        cnf.extend(CardEnc.atmost(lits=lits, bound=1, vpool=pool,
                                  encoding=EncType.seqcounter).clauses)
    cnf.append([v(pin, 0)])                                         # translation symmetry
    for a in range(1, pin):
        cnf.append([-v(pin, a)])
    for n in range(L):
        if n % pin == 0:
            continue
        cnf.append([v(m, n % m) for m in U])
    t0 = time.time()
    with Cadical153(bootstrap_with=cnf) as s:
        ok = s.solve()
    return ok, time.time() - t0, cnf.nv, len(cnf.clauses)

if __name__ == "__main__":
    L = int(sys.argv[1])
    st = structure(L)
    print(f"L={L}  moduli={len(st['ms'])}  slack={float(st['slack']):.6f}  "
          f"forced={len(st['forced'])}  free={st['free']}", flush=True)
    print(f"overlap budget = {st['budget']:.1f} points; forced alone cover "
          f"{sum(L//m for m in st['forced'])} of {L}", flush=True)
    subs = st["subsets"]
    print(f"free-subsets reaching full coverage: {len(subs)}", flush=True)
    exact = [s for s in subs if s[0] == 0]
    print(f"  of these, {len(exact)} have overlap 0 -> EXCLUDED by Mirsky-Newman "
          f"(no exact covering system with distinct moduli)", flush=True)
    todo = [s for s in subs if s[0] > 0]
    print(f"  {len(todo)} to decide by solver\n", flush=True)
    for overlap, U in todo:
        ok, el, nv, nc = decide_subset(L, U, overlap)
        verdict = "*** SAT ***" if ok else "UNSAT" if ok is False else "undecided"
        print(f"  overlap={overlap:<3} |U|={len(U):<3} {nv:>7}v {nc:>8}c  {verdict} in {el:.0f}s", flush=True)
        if ok:
            print("  WITNESS SUBSET:", U, flush=True)
            break
