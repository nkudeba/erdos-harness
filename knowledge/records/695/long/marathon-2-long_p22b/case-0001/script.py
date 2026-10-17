# Refined pyramid (Lemma R) for P(T) = least prime with Pratt height >= T.  Independent rewrite (marathon leg 2).
# A_t = floor(Y/2^(T-t+1)) (t<T), A_T = Y ; B_t = floor((Y+1)/2^(T-t)) - 1 (t<T), B_T = Y.
# Full_t = R_t ∩ (0,A_t];  C_t = {q in R_t ∩ (A_t,B_t]: 2^i(q+1)-1 prime, i=1..T-t};  S_t = Full_t ∪ C_t.
# Full_t = {p<=A_t prime: some r in S_{t-1} | p-1};  C_t = {q in (A_t,B_t] prime with tail: some r in S_{t-1} | q-1}.
import numpy as np, time
from cypari2 import Pari
pari = Pari(); pari.allocatemem(2 * 10**9)
T0 = time.time()
def log(*a): print(*a, "[%.0fs]" % (time.time() - T0), flush=True)

pari(r"tailok(n,L)=for(i=1,L,if(!isprime(2^i*(n+1)-1),return(0)));1")
F_ISP = pari('(v)->select(x->isprime(x),v)')
F_TAIL = pari('(v,L)->select(x->isprime(x)&&tailok(x,L),v)')

def primes_upto(n):
    s = np.ones(n + 1, bool); s[:2] = False
    for i in range(2, int(n ** .5) + 1):
        if s[i]: s[i*i::i] = False
    return np.nonzero(s)[0].astype(np.int64)
SMALL = [int(x) for x in primes_upto(1000)[1:]]          # odd primes < 1000 for presieve
BAD = {}
def badres(l, L):
    k = (l, L)
    if k not in BAD:
        b = np.zeros(l, bool); b[0] = True
        for i in range(1, min(L, l) + 1): b[(pow(2, -i, l) - 1) % l] = True   # 2^i(n+1) = 1 mod l
        BAD[k] = b
    return BAD[k]

def test(n, L):
    """n: int64 array of odd numbers. Return python list of those prime with 2-tail of length L."""
    if len(n) == 0: return []
    big = n[n >= 2000]; small = n[n < 2000]
    ok = np.ones(len(big), bool)
    for l in SMALL:
        ok &= ~badres(l, L)[big % l]
    cand = np.concatenate([small, big[ok]])
    out = []
    for k in range(0, len(cand), 1 << 20):
        v = pari(cand[k:k + (1 << 20)].tolist())
        r = F_ISP(v) if L == 0 else F_TAIL(v, L)
        out.extend(int(x) for x in r)
    return out

BP = primes_upto(3 * 10**7)[1:]
def seg_primes(ilo, ihi):      # mask over i in [ilo,ihi): 2i+1 prime
    a = np.ones(ihi - ilo, bool); top = 2 * ihi + 1
    assert int(BP[-1]) ** 2 > top
    for p in BP.tolist():
        if p * p > top: break
        st = max(p * p, -(-(2 * ilo + 1) // p) * p)
        if st % 2 == 0: st += p
        a[(st - 1) // 2 - ilo::p] = False
    if ilo == 0: a[0] = False
    return a

LQ = 1 << 18
def mark_seg(S, nsmall, ilo, ihi):   # mask over i in [ilo,ihi): some r in S, r | i (i>=r)
    m = np.zeros(ihi - ilo, bool)
    for r in S[:nsmall].tolist():
        if r >= ihi: break
        st = max(r, -(-ilo // r) * r)
        m[st - ilo::r] = True
    jmax = (ihi - 1) // LQ
    if jmax >= 1 and nsmall < len(S):
        js = np.arange(1, jmax + 1, dtype=np.int64)
        lo = np.maximum(np.searchsorted(S, -(-ilo // js)), nsmall)
        hi = np.searchsorted(S, -(-ihi // js))
        c = np.maximum(hi - lo, 0); tot = int(c.sum())
        if tot:
            off = np.repeat(np.cumsum(c) - c, c)
            idx = np.arange(tot, dtype=np.int64) - off + np.repeat(lo, c)
            m[np.repeat(js, c) * S[idx] - ilo] = True
    return m

CH = 1 << 22
def gen_mult(S, ilo, ihi):     # all i = j*r in [ilo, ihi], r in S, j >= 1, as int64 chunks (S in blocks)
    for b in range(0, len(S), 1 << 22):
        yield from gen_mult_block(S[b:b + (1 << 22)], ilo, ihi)
def gen_mult_block(S, ilo, ihi):
    j0 =np.maximum(-(-ilo // S), 1); j1 = ihi // S
    cnt = np.maximum(j1 - j0 + 1, 0)
    csa = np.cumsum(cnt)
    k = 0; n = len(S)
    while k < n:
        if cnt[k] > CH:
            r = int(S[k])
            for a in range(int(j0[k]), int(j1[k]) + 1, CH):
                yield r * np.arange(a, min(int(j1[k]), a + CH - 1) + 1, dtype=np.int64)
            k += 1; continue
        base = int(csa[k - 1]) if k else 0
        e = int(np.searchsorted(csa, base + CH, side='right'))
        e = max(e, k + 1); e = min(e, n)
        while e > k + 1 and cnt[e - 1] > CH: e -= 1
        c = cnt[k:e]; tot = int(c.sum())
        if tot:
            off = np.repeat(np.cumsum(c) - c, c)
            jj = np.arange(tot, dtype=np.int64) - off + np.repeat(j0[k:e], c)
            yield np.repeat(S[k:e], c) * jj
        k = e

SEG = 1 << 26
def level(t, hold, A, B, L, info):
    S = hold[0]
    imaxA = (A - 1) // 2
    inv = sum(float((1.0 / S[b:b + (1 << 22)].astype(np.float64)).sum()) for b in range(0, len(S), 1 << 22))
    EA = imaxA * inv
    tl = time.time()
    log("   t=%d EA/imax=%.4f |S|=%d" % (t, EA / imaxA, len(S)))
    if EA < THR * imaxA:
        found = []
        for i in gen_mult(S, 1, imaxA):
            found.append(np.unique(np.array(test(2 * i + 1, 0), dtype=np.int64)))
            if time.time() - tl > 150: log("   t=%d cand at i=%d/%d" % (t, int(i[-1]), imaxA)); tl = time.time()
        full = np.unique(np.concatenate(found)) if found else np.zeros(0, np.int64); del found; mode = "cand"
    else:
        nsmall = int(np.searchsorted(S, LQ)); outs = []
        for ilo in range(0, imaxA + 1, SEG):
            ihi = min(imaxA + 1, ilo + SEG)
            a = seg_primes(ilo, ihi); a &= mark_seg(S, nsmall, ilo, ihi)
            outs.append((ilo, np.nonzero(a)[0].astype(np.uint32))); del a
            if time.time() - tl > 150: log("   t=%d sieve at i=%d/%d" % (t, ihi, imaxA)); tl = time.time()
        full = None; mode = "sieve"      # outs converted after the tail part, once S is released
    C = np.zeros(0, np.int64); cmode = "-"
    if B > A:
        ilo = (A + 1) // 2; ihi = (B - 1) // 2
        EB = (ihi - ilo + 1) * inv
        W = 2
        for l in SMALL:
            if l <= L + 2 and pari.znorder(pari.Mod(2, l)) == l - 1: W *= l
        NW = (B - A) / W
        cc = []
        if NW < EB:
            cmode = "wheel(W=%d)" % W
            u0 = A // W + 1; u1 = (B + 1) // W
            for a in range(u0, u1 + 1, CH):
                q = W * np.arange(a, min(u1, a + CH - 1) + 1, dtype=np.int64) - 1
                q = q[(q > A) & (q <= B)]
                for x in test(q, L):      # membership in R_t: some prime factor of q-1 lies in S
                    fs = [int(f) for f in pari.factor(x - 1)[0]]
                    if any(f % 2 and np.searchsorted(S, f) < len(S) and S[np.searchsorted(S, f)] == f for f in fs):
                        cc.append(x)
        else:
            cmode = "cand"
            for i in gen_mult(S, ilo, ihi):
                cc.extend(test(2 * i + 1, L))
                if time.time() - tl > 150: log("   t=%d tail-cand at i=%d/%d" % (t, int(i[-1]), ihi)); tl = time.time()
        C = np.unique(np.array(cc, dtype=np.int64))
    hold.clear(); del S                  # release S_{t-1} (memory) before building the int64 array
    if full is None:
        full = np.empty(sum(len(o) for _, o in outs), np.int64); k = 0
        while outs:
            ilo, o = outs.pop(0)
            full[k:k + len(o)] = 2 * (o.astype(np.int64) + ilo) + 1; k += len(o)
    info[t] = (len(full), len(C), int(full[0]) if len(full) else None, mode, cmode)
    return full, C

def run(T, Y, keep=3):
    if REFINED:
        A = {t: Y >> (T - t + 1) for t in range(2, T)}; A[T] = Y
        B = {t: ((Y + 1) >> (T - t)) - 1 for t in range(2, T)}; B[T] = Y
    else:     # plain pyramid (Lemma 1 only): Full_t = R_t ∩ (0, Y/2^(T-t)], no tail sets
        A = {t: Y >> (T - t) for t in range(2, T + 1)}; B = dict(A)
    info = {}
    full = primes_upto(A[2])[1:]
    L = T - 2; W = 2
    for l in SMALL:
        if l <= L + 2 and pari.znorder(pari.Mod(2, l)) == l - 1: W *= l
    q = W * np.arange(A[2] // W + 1, (B[2] + 1) // W + 1, dtype=np.int64) - 1
    C = np.unique(np.array(test(q[(q > A[2]) & (q <= B[2])], L), dtype=np.int64))
    info[2] = (len(full), len(C), 3, "sieve", "wheel")
    log("t=2", info[2])
    kept = {}
    for t in range(3, T + 1):
        S = np.union1d(full, C) if len(C) else full
        del full, C
        if t - 1 >= T - keep: kept[t - 1] = S
        hold = [S]; del S
        full, C = level(t, hold, A[t], B[t], T - t, info)
        log("t=%d A=%d B=%d" % (t, A[t], B[t]), info[t])
    kept[T] = full
    return info, kept

memo = {2: (1, None)}
def Hp(p):
    if p in memo: return memo[p][0]
    best, arg = 0, None
    for r in pari.factor(p - 1)[0]:
        r = int(r); h = Hp(r)
        if h > best: best, arg = h, r
    memo[p] = (best + 1, arg); return best + 1
def chain(p):
    Hp(p); c = [p]
    while memo[c[-1]][1] is not None: c.append(memo[c[-1]][1])
    return c[::-1]

# long_p22b: cross-check of long_p22 with the PLAIN pyramid (Lemma 1 only, no tail sets) and different
# segment size / small-modulus cutoff / sieve-vs-candidate threshold.  Range (0, Y/2]: plain A_t = refined A_t.
SEG = 1 << 25; LQ = 1 << 16
TEST = False
if TEST:
    T, Y, REFINED, UB, THR = 19, 1_840_000_000_000, False, 619108107719, 0.002
else:
    T, Y, REFINED, UB, THR = 22, 433142367554861, False, 866284735109723, 0.002
if True:
    log("long_p22b: T=%d Y=%d refined=%s" % (T, Y, REFINED))
    info, kept = run(T, Y, keep=4)
    print("counts (t,|Full_t|,|C_t|,min):", [(t,) + info[t][:3] for t in sorted(info)])
    for t in sorted(kept): print("level", t, len(kept[t]), kept[t].tolist()[:(40 if t < T - 1 else 200)])
    top = kept[T].tolist(); prev = kept[T - 1].tolist()
    if top:
        p = top[0]; h = Hp(p); c = chain(p)
        ok = len(c) == h and c[0] == 2 and all(c[i + 1] % c[i] == 1 and pari.isprime(c[i + 1]) for i in range(len(c) - 1))
        print("RESULT: min R_%d ∩ (0,%d] = %d (refined=%s), H=%d, chain valid %s, chain %s; |R_%d ∩ (0,Y]|=%d; UB %d in top set: %s; min level-%d set = %s"
              % (T, Y, p, REFINED, h, ok, c, T, len(top), UB, UB in top, T - 1, prev[0] if prev else None))
    else:
        print("RESULT: R_%d ∩ (0,%d] empty (refined=%s); UB %d (should be in top set if UB<=Y)" % (T, Y, REFINED, UB))
