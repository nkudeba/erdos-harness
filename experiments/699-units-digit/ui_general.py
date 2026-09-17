"""
Units-digit system U(i) for general i, direct enumeration.

A counterexample (n,i,j) to #699 needs, for every t<i and every prime power p^e || (n-t) with p>=i
(and, when p=i is prime, e>=2):  j mod p^e <= t   [Lucas, digits 0..e-1].
U(i): that system has no solution with i<j<=n/2.
We enumerate j as multiples of N_0 (the qualifying part of n) and test the rest; then, for each
survivor, test the FULL Lucas condition to see which higher-digit carry (if any) kills it.
"""
import sys
import numpy as np

N = int(sys.argv[1]); I_MAX = int(sys.argv[2])
spf = np.arange(N + 1, dtype=np.int64)
for p in range(2, int(N ** 0.5) + 1):
    if spf[p] == p:
        blk = spf[p*p::p]; mask = blk == np.arange(p*p, N + 1, p); blk[mask] = p; spf[p*p::p] = blk

def factor(m):
    f = {}
    while m > 1:
        p = int(spf[m]); f[p] = f.get(p, 0) + 1; m //= p
    return f

def qualifying(m, i):
    """list of (p^e, p) over p^e || m with p>=i (p==i needs e>=2)"""
    out = []
    for p, e in factor(m).items():
        if p < i: continue
        if p == i and e == 1: continue
        out.append((p**e, p))
    return out

def dominated(j, n, p):
    while j:
        if j % p > n % p: return False
        j //= p; n //= p
    return True

for i in range(4, I_MAX + 1):
    surv = []; full = []
    for n in range(2 * i + 2, N + 1):
        Q = [qualifying(n - t, i) for t in range(i)]
        N0 = 1
        for q, p in Q[0]: N0 *= q
        j = N0 * ((i + 1 + N0 - 1) // N0)
        while 2 * j <= n:
            ok = True
            for t in range(1, i):
                for q, p in Q[t]:
                    if j % q > t: ok = False; break
                if not ok: break
            if ok:
                killers = sorted(p for t in range(i) for q, p in Q[t] if not dominated(j, n, p))
                surv.append((n, j, killers))
                if not killers: full.append((n, j))
            j += N0
    print(f"i={i}: n<={N}: units-digit survivors {len(surv)}, full counterexamples {len(full)} {full}")
    for s in surv[:40]: print("    ", s)
