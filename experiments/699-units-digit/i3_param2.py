"""
Parametrised verification of Conjecture U(3) -- corrected a-range.

Written reduction: a solution (n,j) of U(3) has 4|n, n=2^r a (a odd), A' = a or a/3 (the latter iff 3||a),
h = n/(2A') in {2^(r-1), 3*2^(r-1)}, j = kA', 1<=k<=h-1, and
     B' | k(2h-k),   C' | k(h-k)(2h-k),   A'^2 < 4.5h + 2.25.
For fixed r every odd a with A'^2 < 4.5h+2.25 is tested, i.e. a <= sqrt(4.5*2^(r-1)+2.25) when 3∤a or 9|a,
and a <= sqrt(121.5*2^(r-1)+20.25) when 3||a.  Hence a run to R covers EVERY n with 2 <= v_2(n) <= R,
in particular every n < 2^(R+1).
"""
import sys, math, time
from sympy import factorint
from sympy.ntheory.modular import crt
from multiprocessing import Pool

def big_part(m):
    f = factorint(m); out = 1; g = {}
    for p, e in f.items():
        if p == 2 or (p == 3 and e == 1): continue
        out *= p**e; g[p] = e
    return out, g

def unitary_splits(g):
    items = list(g.items())
    for mask in range(1 << len(items)):
        B1 = 1
        for b, (p, e) in enumerate(items):
            if mask >> b & 1: B1 *= p**e
        yield B1

def test_r(r):
    t0 = time.time(); survivors = []; tested = 0; nmax = 0
    a_max = int(math.isqrt(int(121.5 * 2**(r-1) + 20.25)) + 1)
    for a in range(1, a_max + 1, 2):
        n = (1 << r) * a
        v3 = 0; t = a
        while t % 3 == 0: t //= 3; v3 += 1
        Ap = a // 3 if v3 == 1 else a
        h = n // (2 * Ap)
        if Ap * Ap >= 4.5 * h + 2.25: continue
        tested += 1; nmax = max(nmax, n)
        Bp, gB = big_part(n - 1)
        Cp, _ = big_part(n - 2)
        for B1 in unitary_splits(gB):
            B2 = Bp // B1
            if B1 == 1: k0 = (2 * h) % B2
            elif B2 == 1: k0 = 0
            else: k0 = int(crt([B1, B2], [0, (2 * h) % B2])[0])
            for k in range(k0, h, Bp):
                if k < 1: continue
                if (k * (h - k) * (2 * h - k)) % Cp == 0 and k * Ap >= 4:
                    j = k * Ap
                    assert j % Ap == 0 and (j*(j-1)) % Bp == 0 and (j*(j-1)*(j-2)) % Cp == 0
                    survivors.append((n, j, r, a))
    return r, nmax, tested, survivors, time.time() - t0

if __name__ == "__main__":
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    with Pool() as pool:
        for r, nmax, tested, surv, dt in pool.imap_unordered(test_r, range(lo, hi + 1)):
            print(f"r={r:2d}  covers all n with v2(n)={r:2d}; largest candidate n={nmax:>18d}  candidates {tested:>7d}  survivors {surv}  ({dt:.0f}s)", flush=True)
    print("DONE", lo, hi)
