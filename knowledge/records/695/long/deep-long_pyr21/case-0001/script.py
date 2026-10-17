# LONG: exhaustive pyramid (numpy sieve + PARI candidates) at scale F: R_t = {p prime: H(p) >= t} exact on (0, Y_t],
# Y_t = floor(F*2e10/2^(16-t)) for t <= 16, F*2e10*2^(t-16) for t > 16.  F=140: Y_20 = 4.48e13, Y_21 = 8.96e13.
# Decides P(21) if P(21) <= 8.96e13 (beam upper bound: P(21) <= 85301359593119).
import numpy as np, time
from cypari2 import Pari
pari = Pari(); pari.allocatemem(3 * 10**9)
TEST = False
F, T = (1, 18) if TEST else (140, 21)
SIEVE_MAX = (F * 20_000_000_000) >> 6          # sieve levels t <= 10
SEG = 100_000_000
CHUNK = 20_000_000
t0 = time.time()
Yt = {t: (F * 20_000_000_000) >> (16 - t) if t <= 16 else (F * 20_000_000_000) << (t - 16) for t in range(2, T + 1)}
assert all(Yt[t - 1] == Yt[t] // 2 for t in range(3, T + 1))
Bn = int(SIEVE_MAX ** 0.5) + 2
bs = np.ones(Bn + 1, dtype=bool); bs[:2] = False
for i in range(2, int(Bn ** 0.5) + 1):
    if bs[i]: bs[i * i::i] = False
BP = np.nonzero(bs)[0][1:].astype(np.int64)
def seg_primes(ilo, ihi):
    a = np.ones(ihi - ilo, dtype=bool); nhi = 2 * ihi + 1
    for p in BP.tolist():
        if p * p > nhi: break
        st = max(p * p, ((2 * ilo + 1 + p - 1) // p) * p)
        if st % 2 == 0: st += p
        a[(st - 1) // 2 - ilo::p] = False
    if ilo == 0: a[0] = False
    return a
def mark_seg(Q, ilo, ihi):
    L = ihi - ilo; m = np.zeros(L, dtype=bool)
    small = Q[Q < L // 32]; large = Q[(Q >= L // 32) & (Q < ihi)]
    for q in small.tolist():
        st = max(q, ((ilo + q - 1) // q) * q); m[st - ilo::q] = True
    pos = np.maximum(large, ((ilo + large - 1) // large) * large); lq = large
    while len(pos):
        keep = pos < ihi; pos = pos[keep]; lq = lq[keep]
        m[pos - ilo] = True; pos = pos + lq
    return m
SMALLP = [int(p) for p in BP[:60]]
isp = pari('(v)->select(x->isprime(x),v)')
def test_batch(parts):
    c = np.unique(np.concatenate(parts))
    for p in SMALLP: c = c[(c % p != 0) | (c == p)]
    return np.array([int(x) for x in isp(pari(c.tolist()))], dtype=np.int64) if len(c) else np.zeros(0, dtype=np.int64)
R = {}; mins = {}
for t in range(2, T + 1):
    Y = Yt[t]; Q = None if t == 2 else R[t - 1][R[t - 1] <= Y // 2]
    if Y <= SIEVE_MAX:
        out = []; imax = Y // 2 + 1
        for ilo in range(0, imax, SEG):
            ihi = min(imax, ilo + SEG); a = seg_primes(ilo, ihi)
            if Q is not None: a &= mark_seg(Q, ilo, ihi)
            v = 2 * (np.nonzero(a)[0] + ilo) + 1; out.append(v[v <= Y])
            if ilo // SEG % 50 == 49: print(f"  t={t} seg {ilo // SEG + 1} of {imax // SEG + 1} time={time.time()-t0:.0f}", flush=True)
        R[t] = np.concatenate(out); del out
    else:
        res = []; parts = []; cnt = 0
        for q in Q.tolist():
            parts.append(np.arange(2 * q + 1, Y + 1, 2 * q, dtype=np.int64)); cnt += len(parts[-1])
            if cnt > CHUNK:
                res.append(test_batch(parts)); parts = []; cnt = 0
                print(f"  t={t} batch done, time={time.time()-t0:.0f}", flush=True)
        if parts: res.append(test_batch(parts))
        R[t] = np.unique(np.concatenate(res)) if res else np.zeros(0, dtype=np.int64)
    if t - 2 in R: del R[t - 2]
    mins[t] = R[t][:3].tolist()
    print(f"t={t} Y_t={Y} |R_t|={len(R[t])} smallest={mins[t]} time={time.time()-t0:.0f}", flush=True)
# witness chain for the minimum of the top two levels, via the Pratt-tree recursion (PARI factor), memoised
from functools import lru_cache
@lru_cache(maxsize=None)
def longest(p):
    if p == 2: return (2,)
    best = ()
    for q in [int(x) for x in pari.factor(p - 1)[0]]:
        c = longest(q)
        if len(c) > len(best): best = c
    return best + (p,)
summary = []
for t in (T - 1, T):
    if mins[t]:
        ch = longest(mins[t][0]); summary.append(f"P({t})={mins[t][0]} (H={len(ch)}, witness {list(ch)})")
    else:
        summary.append(f"P({t})>{Yt[t]}")
print("RESULT: " + "; ".join(summary) + f"; exact ranges Y_t = {Yt[T-1]}, {Yt[T]}")
