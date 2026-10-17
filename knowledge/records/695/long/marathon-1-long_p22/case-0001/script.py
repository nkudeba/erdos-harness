# Refined pyramid for P(T) = least p with Pratt height H(p) >= T.
# Levels t=2..T. A_t = floor(Y/2^(T-t+1)) (t<T), A_T = Y; B_t = floor((Y+1)/2^(T-t)) - 1 (t<T), B_T = Y.
# Full_t = R_t ∩ (0,A_t];  C_t = {q in R_t ∩ (A_t,B_t] : 2^i(q+1)-1 prime for i=1..T-t}  (pure 2-tail).
# Lemma: for a chain p_1..p_T with p_T <= Y and t<T, either p_t <= Y/2^(T-t+1) or m_t=..=m_{T-1}=2.
# Hence R_T ∩ (0,Y] = {p<=Y prime : some r in Full_{T-1} ∪ C_{T-1} divides p-1}, and recursively
# Full_t, C_t are generated from S_{t-1} = Full_{t-1} ∪ C_{t-1} (see notebook for the proof).
import numpy as np, time, math
from cypari2 import Pari
pari = Pari(); pari.allocatemem(3 * 10**9)
t00 = time.time()

def log(*a):
    print(*a, "time=%.0f" % (time.time() - t00), flush=True)

pari(r"""tailok(n,L) = for(i=1,L, if(!isprime(2^i*(n+1)-1), return(0))); 1""")
_isp = pari('(v)->select(x->isprime(x),v)')
_tail = pari('(v,L)->select(x->isprime(x) && tailok(x,L),v)')
SMALL = [p for p in range(3, 542) if all(p % d for d in range(2, int(p ** .5) + 1))]

def base_primes(n):
    s = np.ones(n + 1, dtype=bool); s[:2] = False
    for i in range(2, int(n ** .5) + 1):
        if s[i]: s[i * i::i] = False
    return np.nonzero(s)[0][1:].astype(np.int64)   # odd primes

BP = None
def seg_primes(ilo, ihi):            # bool over i in [ilo,ihi): 2i+1 prime
    a = np.ones(ihi - ilo, dtype=bool); nhi = 2 * ihi + 1
    for p in BP.tolist():
        if p * p > nhi: break
        st = max(p * p, ((2 * ilo + 1 + p - 1) // p) * p)
        if st % 2 == 0: st += p
        a[(st - 1) // 2 - ilo::p] = False
    if ilo == 0: a[0] = False
    return a

LQ = 1 << 20
def mark_seg(S, Ssmall, ilo, ihi):   # bool over i in [ilo,ihi): some q in S with q | i, i >= q
    m = np.zeros(ihi - ilo, dtype=bool)
    for q in Ssmall:
        if q >= ihi: break
        st = max(q, ((ilo + q - 1) // q) * q)
        m[st - ilo::q] = True
    a0 = np.searchsorted(S, LQ)
    jmax = (ihi - 1) // LQ
    for j in range(1, jmax + 1):
        lo = max(a0, np.searchsorted(S, -(-ilo // j)))
        hi = np.searchsorted(S, -(-ihi // j))
        if hi > lo:
            m[j * S[lo:hi] - ilo] = True
    return m

def presieve(n, L):
    # keep n with n, 2(n+1)-1, ..., 2^L(n+1)-1 all free of factors in SMALL (n itself may equal a small prime)
    ok = np.ones(len(n), dtype=bool)
    for l in SMALL:
        r = n % l
        if L == 0:
            ok &= (r != 0) | (n == l)
        else:
            bad = np.zeros(l, dtype=bool)
            for i in range(L + 1):
                bad[(pow(2, -i, l) - 1) % l] = True      # 2^i (n+1) == 1 mod l
            ok &= ~bad[r] | (n == l)
    return n[ok]

def test(n, L):
    if len(n) == 0: return np.zeros(0, dtype=np.int64)
    n = presieve(n, L) if L <= 64 else n
    out = [np.zeros(0, dtype=np.int64)]
    for k in range(0, len(n), 1 << 21):
        v = pari(n[k:k + (1 << 21)].tolist())
        res = _isp(v) if L == 0 else _tail(v, L)
        out.append(np.array([int(x) for x in res], dtype=np.int64))
    return np.concatenate(out)

CH = 1 << 22
def gen_candidates(S, ilo, ihi):     # yields arrays of i = j*q in [ilo,ihi], q in S, j>=1
    cnt = ihi // S - (np.maximum(ilo, S) - 1) // S
    cnt = np.maximum(cnt, 0)
    k = 0; nS = len(S)
    while k < nS:
        if cnt[k] > CH:
            q = int(S[k]); j0 = max(-(-ilo // q), 1); j1 = ihi // q
            for jj in range(j0, j1 + 1, CH):
                yield q * np.arange(jj, min(j1, jj + CH - 1) + 1, dtype=np.int64)
            k += 1; continue
        e = k; tot = 0
        while e < nS and cnt[e] <= CH and tot + cnt[e] <= CH:
            tot += cnt[e]; e += 1
        if e == k: e = k + 1; tot = cnt[k]
        qs = S[k:e]; cs = cnt[k:e]
        if tot > 0:
            j0 = np.maximum(-(-ilo // qs), 1)
            off = np.repeat(np.cumsum(cs) - cs, cs)
            jj = np.arange(tot, dtype=np.int64) - off + np.repeat(j0, cs)
            yield np.repeat(qs, cs) * jj
        k = e

SEG = 1 << 26
def level(t, S, A, B, L, Sfull, Cprev, mode_log):
    """returns (Full_t sorted int64, C_t sorted int64). S sorted = Full_{t-1} ∪ C_{t-1}."""
    imaxA = (A - 1) // 2; imaxB = (B - 1) // 2
    EA = int((imaxA // S).sum()) if len(S) else 0
    EB = int((imaxB // S).sum()) - EA if len(S) else 0
    # Full part
    if EA < imaxA * 0.035 or imaxA > 2 ** 37:
        found = [np.zeros(0, dtype=np.int64)]; tl = time.time()
        for i in gen_candidates(S, 1, imaxA):
            found.append(test(2 * i + 1, 0))
            if time.time() - tl > 120:
                log("  level %d cand progress i=%d of %d, found %d" % (t, int(i[-1]), imaxA, sum(len(f) for f in found))); tl = time.time()
        full = np.unique(np.concatenate(found)); del found; modeA = "cand(%d)" % EA
    else:
        Ssmall = [int(q) for q in S[S < LQ]]
        outs = []; tl = time.time()
        for ilo in range(0, imaxA + 1, SEG):
            ihi = min(imaxA + 1, ilo + SEG)
            a = seg_primes(ilo, ihi) & mark_seg(S, Ssmall, ilo, ihi)
            outs.append((ilo, np.nonzero(a)[0].astype(np.uint32)))
            del a
            if time.time() - tl > 120:
                log("  level %d sieve progress i=%d of %d" % (t, ihi, imaxA)); tl = time.time()
        full = np.empty(sum(len(o) for _, o in outs), dtype=np.int64); k = 0
        for ilo, o in outs:
            full[k:k + len(o)] = 2 * (o.astype(np.int64) + ilo) + 1; k += len(o)
        del outs; modeA = "sieve"
    # tail part (A, B]
    C = []
    if B > A and L >= 1:
        W = 2
        for l in SMALL:
            if l <= L + 2 and pow(2, (l - 1) // 2, l) == l - 1 and all(pow(2, (l - 1) // f, l) != 1
                    for f in range(2, l) if (l - 1) % f == 0 and all(f % g for g in range(2, f))):
                W *= l
        nwheel = (B - A) // W
        if nwheel * 0.5e-6 < EB * 0.3e-6:
            u0 = (A + 1) // W + 1; u1 = (B + 1) // W
            cand = []
            for uu in range(u0, u1 + 1, CH):
                u = W * np.arange(uu, min(u1, uu + CH - 1) + 1, dtype=np.int64)
                cand.extend(int(x) for x in test(u - 1, L))
            # predecessor check: q in R_t iff some prime factor r of q-1 lies in S
            for q in cand:
                fs = [int(f) for f in pari.factor(q - 1)[0]]
                if any((r < len(S) and False) or (np.searchsorted(S, r) < len(S) and S[np.searchsorted(S, r)] == r) for r in fs):
                    C.append(q)
            modeB = "wheel(W=%d,n=%d,cc=%d)" % (W, nwheel, len(cand))
        else:
            for i in gen_candidates(S, imaxA + 1, imaxB):
                C.extend(int(x) for x in test(2 * i + 1, L))
            modeB = "cand(%d)" % EB
    else:
        modeB = "-"
    C = np.unique(np.array(C, dtype=np.int64))
    mode_log.append((t, modeA, modeB))
    return full, C

def run(T, Y, keep_from=None):
    global BP
    A = {t: (Y >> (T - t + 1)) if t < T else Y for t in range(2, T + 1)}
    B = {t: ((Y + 1) >> (T - t)) - 1 if t < T else Y for t in range(2, T + 1)}
    BP = base_primes(int(math.isqrt(max(A[t] for t in A if A[t] < 2 ** 38))) + 100)
    ml = []
    # level 2: all odd primes
    full = np.concatenate([2 * (np.nonzero(seg_primes(ilo, min((A[2] - 1) // 2 + 1, ilo + SEG)))[0] + ilo) + 1
                           for ilo in range(0, (A[2] - 1) // 2 + 1, SEG)]).astype(np.int64)
    L = T - 2
    C = np.zeros(0, dtype=np.int64)
    if B[2] > A[2]:
        # tail part of level 2: q prime with full 2-tail; use the generic wheel via a dummy S = {} check skipped
        W = 2
        for l in SMALL:
            if l <= L + 2 and all(pow(2, (l - 1) // f, l) != 1 for f in range(2, l) if (l - 1) % f == 0 and all(f % g for g in range(2, f))):
                W *= l
        u0 = (A[2] + 1) // W + 1; u1 = (B[2] + 1) // W
        cc = []
        for uu in range(u0, u1 + 1, CH):
            u = W * np.arange(uu, min(u1, uu + CH - 1) + 1, dtype=np.int64)
            cc.extend(test(u - 1, L))
        C = np.unique(np.array(cc, dtype=np.int64))
    log("t=2 A=%d B=%d |Full|=%d |C|=%d" % (A[2], B[2], len(full), len(C)))
    stats = {2: (len(full), len(C), int(full[0]))}
    kept = {}
    for t in range(3, T + 1):
        S = np.union1d(full, C) if len(C) else full
        if keep_from and t - 1 >= keep_from: kept[t - 1] = S
        full, C = level(t, S, A[t], B[t], T - t, full, C, ml)
        del S
        mn = int(full[0]) if len(full) else None
        stats[t] = (len(full), len(C), mn)
        log("t=%d A=%d B=%d |Full|=%d |C|=%d min=%s mode=%s" % (t, A[t], B[t], len(full), len(C), mn, ml[-1][1:]))
    kept[T] = full
    return stats, full, kept

memo = {2: (1, None)}
def H(p):                            # exact Pratt height, with argmax predecessor (independent of the pyramid)
    if p in memo: return memo[p][0]
    best, arg = 0, None
    for r in pari.factor(p - 1)[0]:
        r = int(r); h = H(r)
        if h > best: best, arg = h, r
    memo[p] = (best + 1, arg); return best + 1
def chain(p):
    H(p); c = [p]
    while memo[c[-1]][1] is not None: c.append(memo[c[-1]][1])
    return c[::-1]

TEST = False
if TEST:
    T, Y = 20, 7_360_000_000_000; UB = 7242080052479; PREV = 619108107719
else:
    T, Y = 22, 866284735109723; UB = 866284735109723; PREV = 64750853277599   # UB: certified chain (deep/C3)
st, top, kept = run(T, Y, keep_from=T - 3)
print("checkpoint counts (t, |Full_t|=|R_t ∩ (0,A_t]|, |C_t|, min Full_t):", [(t,) + st[t] for t in sorted(st)])
for t in sorted(kept):
    v = kept[t].tolist()
    print("level %d set (%d):" % (t, len(v)), v if len(v) <= 400 else v[:400] + ["..."])
toplist = top.tolist()
ok_ub = UB in toplist
p = toplist[0] if toplist else None
lev_prev = kept[T - 1].tolist()
ok_prev = (lev_prev[0] == PREV) if lev_prev else False
if p is not None:
    h = H(p); c = chain(p)
    valid = len(c) == h and c[0] == 2 and all(c[i + 1] % c[i] == 1 and pari.isprime(c[i]) for i in range(len(c) - 1)) and pari.isprime(c[-1])
    print("Pratt check: H(%d) = %d, chain valid %s" % (p, h, valid))
    def gg(x):
        s = 0
        while x != 2:
            x = max(int(f) for f in pari.factor(x - 1)[0]); s += 1
        return s
    try:
        print("gpf-iteration steps g(top elements, first 20):", [(x, gg(x)) for x in toplist[:20]])
    except Exception as e:
        print("g failed", e)
    hs = [H(x) for x in toplist[:50]]
    print("H of first 50 top elements:", hs)
    print("RESULT: P(%d)=%d (exhaustive over (0,%d], refined pyramid; H=%d exact via Pratt recursion, witness %s); |R_%d ∩ (0,Y]|=%d; UB endpoint %d found in top set: %s; min of level %d set = %s (expected P(%d)=%d): %s"
          % (T, p, Y, h, c, T, len(toplist), UB, ok_ub, T - 1, lev_prev[0] if lev_prev else None, T - 1, PREV, ok_prev))
else:
    print("RESULT: R_%d ∩ (0,%d] is EMPTY (inconsistent with the UB chain: BUG)" % (T, Y))
