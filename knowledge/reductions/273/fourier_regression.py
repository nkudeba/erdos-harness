"""Regression via DFS cover-finder: the screen must NEVER kill a genuine cover."""
from itertools import combinations
from math import gcd
from sympy import divisors

def find_cover(U, L):
    """DFS: repeatedly take the least uncovered point and try every modulus that can cover it."""
    U = sorted(U, reverse=True)
    n = len(U)
    best = {}
    def rec(i, covered, assign):
        if i == n:
            return assign if len(covered) == L else None
        m = U[i]
        for a in range(m):
            new = covered | set(range(a, L, m))
            r = rec(i+1, new, assign+[(m, a)])
            if r: return r
        return None
    # prune: order by descending modulus so big classes are placed first
    return rec(0, set(), [])

def screen_kill(U, k, L):
    for d in divisors(L):
        if d == 1: continue
        W = sorted((L//m for m in U if m % d == 0), reverse=True)
        if W and 2*W[0]-sum(W) > k: return (d, W, 2*W[0]-sum(W))
    return None

tested = falsekill = 0
kmin = 10**9; kmin_ex = None
for L in (12, 16, 24, 30, 36, 48, 60):
    D = [d for d in divisors(L) if d > 1]
    for size in range(2, min(len(D), 6)+1):
        for U in combinations(D, size):
            if sum(L//m for m in U) < L: continue
            l = 1
            for m in U: l = l*m//gcd(l, m)
            if l != L: continue
            sol = find_cover(list(U), L)
            if not sol: continue
            k = sum(L//m for m in U) - L
            tested += 1
            if k < kmin: kmin, kmin_ex = k, (L, U, sol)
            kill = screen_kill(U, k, L)
            if kill:
                falsekill += 1
                print(f"  !! FALSE KILL L={L} U={U} sol={sol} k={k} at d={kill[0]} W={kill[1]} bound={kill[2]}")
print(f"tested {tested} genuine covering systems (distinct moduli, lcm = L exactly)")
print(f"FALSE KILLS: {falsekill}")
print(f"tightest genuine cover found: k={kmin}  {kmin_ex}")
