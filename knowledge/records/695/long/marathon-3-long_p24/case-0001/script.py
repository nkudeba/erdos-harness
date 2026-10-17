# long_p24: same code as long_p23i.py (leg-3 pyr3), exhaustive refined pyramid T=24, Y=9e15.
# Decides R_24 ∩ (0,9e15]: P(24) exactly if P(24) <= 9e15, else the lower bound P(24) > 9e15.
# (Certified upper bound: P(24) <= 94649825706124769, check_c2.py.)  MODE="TEST" reproduces leg-1/C1.
#   Levels t = 2..T.  A_t = floor(Y/2^(T-t+1)) (t<T), A_T = Y;  B_t = floor((Y+1)/2^(T-t)) - 1 (t<T), B_T = Y.
#   Full_t = R_t ∩ (0,A_t];  C_t = {q in R_t ∩ (A_t,B_t] : 2^i(q+1)-1 prime, i=1..T-t};  S_t = Full_t ∪ C_t.
#   Recursion: Full_t = {p<=A_t prime: ∃ r in S_{t-1}, r | p-1, r<p};  C_t likewise on (A_t,B_t] with the tail test.
#   Wheel: q > l with a 2-tail of length L and l <= L+2 an odd prime with 2 a primitive root  =>  l | q+1.
import numpy as np, time, math
from cypari2 import Pari
pari = Pari(); pari.allocatemem(4 * 10**9)
T0 = time.time()
def log(*a): print(*a, "[%.0fs]" % (time.time() - T0), flush=True)

pari(r"""tl(q,L)=for(i=1,L,if(!isprime(2^i*(q+1)-1),return(0)));1""")
GW = pari(r"""(A,B,W,L)->my(w=List(),q0=(A+1)\W*W-1);if(q0<=A,q0+=W);forstep(q=q0,B,W,if(isprime(q)&&tl(q,L),listput(w,q)));Vec(w)""")

def primes_upto(n):
    s = np.ones(n + 1, dtype=bool); s[:2] = False; s[4::2] = False
    for i in range(3, math.isqrt(n) + 1, 2):
        if s[i]: s[i * i::2 * i] = False
    return np.flatnonzero(s)
BASE = primes_upto(2 * 10**6)
ODDBASE = BASE[1:]

def is_prim_root2(l):
    if l == 3: return True
    ph = l - 1
    fs = [f for f in range(2, ph + 1) if ph % f == 0 and all(f % g for g in range(2, math.isqrt(f) + 1))]
    return all(pow(2, ph // f, l) != 1 for f in fs)
def odd_wheel(L):
    w = 1
    for l in ODDBASE[:50].tolist():
        if l <= L + 2 and is_prim_root2(l): w *= l
    return w

def tolist_np(v):
    return np.array([int(x) for x in v], dtype=np.int64)

SEG = 1 << 26
LQ = 1 << 16
LSPLIT = 1 << 12; BL = 1 << 19
SMALLP = ODDBASE[(ODDBASE >= 23) & (ODDBASE < LSPLIT)].astype(np.int64)
LARGEP = ODDBASE[ODDBASE >= LSPLIT].astype(np.int64)
def sieve_full(S, imax):
    seg = SEG if imax < 2**33 else 4 * SEG
    out = []; tl0 = time.time()
    k1 = int(np.searchsorted(S, LQ)); k2 = int(np.searchsorted(S, seg))
    Ssm = S[:k1].tolist(); Smid = S[k1:k2]
    Smax = int(S[-1])
    for ilo in range(0, imax + 1, seg):
        ihi = min(imax + 1, ilo + seg); L = ihi - ilo
        pat = get_pattern(seg)
        off = ilo % PER
        pm = pat[off:off + L].copy()          # 2i+1 coprime to 3*5*7*11*13*17*19
        if ilo == 0:
            pm[0] = False                      # n = 1
            for l in (3, 5, 7, 11, 13, 17, 19):
                if (l - 1) // 2 < L: pm[(l - 1) // 2] = True
        nmax = 2 * ihi - 1
        assert nmax < int(BASE[-1]) ** 2
        sp = SMALLP[SMALLP * SMALLP <= nmax]
        if len(sp):
            spl = sp.tolist(); h = (sp - 1) // 2
            for b0 in range(0, L, BL):
                b1 = min(L, b0 + BL); blk = pm[b0:b1]
                offs = ((h - (ilo + b0)) % sp).tolist()
                for l, o in zip(spl, offs):
                    blk[o::l] = False
            if ilo == 0:
                for l in spl:
                    if (l - 1) // 2 < L: pm[(l - 1) // 2] = True     # restore the primes l themselves
        for l in LARGEP.tolist():
            if l * l > nmax: break
            st = (l * l - 1) // 2
            if st < ilo: st = ilo + (((l - 1) // 2 - ilo) % l)
            pm[st - ilo::l] = False
        mk = np.zeros(L, dtype=bool)
        for r in Ssm:
            if r >= ihi: break
            st = max(r, -(-ilo // r) * r)
            mk[st - ilo::r] = True
        sm = Smid[Smid < ihi]
        if len(sm):
            j0 = np.maximum(1, -(-ilo // sm)); j1 = (ihi - 1) // sm
            cnt = np.maximum(j1 - j0 + 1, 0)
            for (r_, j0_, cnt_) in split_counts(sm, j0, cnt, 1):
                tot = int(cnt_.sum())
                if tot == 0: continue
                off = np.repeat(np.cumsum(cnt_) - cnt_, cnt_)
                jj = np.repeat(j0_, cnt_) + (np.arange(tot, dtype=np.int64) - off)
                mk[np.repeat(r_, cnt_) * jj - ilo] = True
        if ihi > seg:
            jlo = max(1, ilo // (Smax + 1)); jhi = (ihi - 1) // seg
            for j in range(jlo, jhi + 1):
                lo = max(k2, int(np.searchsorted(S, -(-ilo // j))))
                hi = int(np.searchsorted(S, -(-ihi // j)))
                if hi > lo: mk[j * S[lo:hi] - ilo] = True
        pm &= mk
        del mk
        idx = np.flatnonzero(pm)
        del pm
        out.append((ilo, idx.astype(np.uint32)))
        del idx
        if time.time() - tl0 > 240: log("   sieve progress i=%d of %d" % (ihi, imax)); tl0 = time.time()
    return out

def assemble(pieces):
    n = sum(len(o) for _, o in pieces)
    full = np.empty(n, dtype=np.int64); k = 0
    pieces.reverse()
    while pieces:
        ilo, o = pieces.pop()
        full[k:k + len(o)] = 2 * (o.astype(np.int64) + ilo) + 1; k += len(o)
        del o
    return full

PER = 3 * 5 * 7 * 11 * 13 * 17 * 19
_PAT = {}
def get_pattern(seg):
    if seg not in _PAT:
        _PAT.clear()
        base = np.ones(PER, dtype=bool)
        for l in (3, 5, 7, 11, 13, 17, 19):
            base[(l - 1) // 2::l] = False
        reps = (seg + PER) // PER + 1
        _PAT[seg] = np.tile(base, reps)
    return _PAT[seg]

GFULL2 = pari(r"""(rs,j0,j1)->my(w=List());for(k=1,#rs,my(s=2*rs[k]);forstep(n=s*j0[k]+1,s*j1[k]+1,s,if(isprime(n),listput(w,n))));Vec(w)""")
CAPC = 1 << 24
def cand_full(S, A):
    res = []; tl0 = time.time(); done = 0
    rs_all = S[:int(np.searchsorted(S, (A - 1) // 2, side='right'))]     # 2r+1 <= A
    for k in range(0, len(rs_all), 1 << 20):
        r = rs_all[k:k + (1 << 20)]
        cnt = (A - 1) // (2 * r)                                          # j = 1..cnt
        j0 = np.ones(len(r), dtype=np.int64)
        for (r_, j0_, cnt_) in split_counts(r, j0, cnt, 1, CAPC):
            j1_ = j0_ + cnt_ - 1
            v = GFULL2(pari.Vecsmall(r_.tolist()), pari.Vecsmall(j0_.tolist()), pari.Vecsmall(j1_.tolist()))
            res.append(tolist_np(v)); done += int(cnt_.sum())
            if time.time() - tl0 > 240: log("   cand_full progress %d candidates, r-index %d/%d" % (done, k, len(rs_all))); tl0 = time.time()
    return np.unique(np.concatenate(res)) if res else np.zeros(0, np.int64)

GTAIL = pari(r"""(v,L)->my(w=List());for(i=1,#v,if(isprime(v[i])&&tl(v[i],L),listput(w,v[i])));Vec(w)""")
PRE = ODDBASE[:40].tolist()          # odd primes 3..179 for presieving
def bad_table(l, L):
    bad = np.zeros(l, dtype=bool)
    for i in range(0, L + 1):        # 2^i (n+1) - 1 == 0 mod l  <=>  n == 2^{-i} - 1 mod l
        bad[(pow(2, -i, l) - 1) % l] = True
    return bad
def presieve_tail(n, L):
    ok = np.ones(len(n), dtype=bool)
    for l in PRE:
        ok &= ~bad_table(l, L)[n % l]
    return n[ok]                     # all n here exceed 179, and so do their tail members
CAP = 1 << 23
def split_counts(r, j0, cnt, step, CAP=CAP):
    k = 0; n = len(r)
    while k < n:
        if cnt[k] > CAP:
            c = int(cnt[k]); s = 0
            while s < c:
                e = min(c, s + CAP)
                yield (r[k:k + 1], j0[k:k + 1] + step * s, np.array([e - s], dtype=np.int64)); s = e
            k += 1; continue
        cs = np.cumsum(cnt[k:])
        e = k + int(np.searchsorted(cs, CAP, side='right'))
        if e == k: e = k + 1
        yield (r[k:e], j0[k:e], cnt[k:e]); k = e

def cand_C(S, A, B, L):
    Wo = odd_wheel(L)
    inv = np.zeros(Wo, dtype=np.int64)
    for x in range(1, Wo):
        if math.gcd(x, Wo) == 1: inv[x] = pow(x, -1, Wo)
    rs = S[:int(np.searchsorted(S, (B - 1) // 2, side='right'))]
    res = []; tl0 = time.time()
    for k in range(0, len(rs), 1 << 20):
        if time.time() - tl0 > 240: log("   cand_C progress r-index %d/%d" % (k, len(rs))); tl0 = time.time()
        r = rs[k:k + (1 << 20)]
        r = r[np.gcd(r, Wo) == 1]
        if len(r) == 0: continue
        c = (-inv[r % Wo]) % Wo
        j1 = (A - 1) // (2 * r) + 1
        j0 = j1 + ((c - j1) % Wo)
        jm = (B - 1) // (2 * r)
        cnt = np.where(jm >= j0, (jm - j0) // Wo + 1, 0)
        if int(cnt.sum()) == 0: continue
        for (r_, j0_, cnt_) in split_counts(r, j0, cnt, Wo):
            tot = int(cnt_.sum())
            off = np.repeat(np.cumsum(cnt_) - cnt_, cnt_)
            jj = np.repeat(j0_, cnt_) + Wo * (np.arange(tot, dtype=np.int64) - off)
            n = 2 * np.repeat(r_, cnt_) * jj + 1
            n = presieve_tail(n, L)
            for z in range(0, len(n), 1 << 21):
                res.append(tolist_np(GTAIL(pari.Vecsmall(n[z:z + (1 << 21)].tolist()), L)))
    return np.unique(np.concatenate(res)) if res else np.zeros(0, np.int64)

def wheel_C(S, A, B, L):
    W = 2 * odd_wheel(L)
    qs = []
    q0 = A
    CHW = W * (1 << 22)
    while q0 < B:
        q1 = min(B, q0 + CHW)
        qs.extend(int(x) for x in GW(q0, q1, W, L)); q0 = q1
    keep = []
    for q in qs:      # membership: some prime factor of q-1 lies in S
        fs = [int(x) for x in pari.factor(q - 1)[0]]
        if any(f < q and np.searchsorted(S, f) < len(S) and S[np.searchsorted(S, f)] == f for f in fs):
            keep.append(q)
    return np.array(sorted(keep), dtype=np.int64)

CS_SIEVE = 3.5e-9; CS_CAND = 0.45e-6
def run(T, Y, keep_from, verbose=True):
    A = {t: (Y >> (T - t + 1)) for t in range(2, T)}; A[T] = Y
    B = {t: ((Y + 1) >> (T - t)) - 1 for t in range(2, T)}; B[T] = Y
    assert A[2] <= 4 * 10**12
    full = assemble(sieve_full(np.array([1], dtype=np.int64), (A[2] - 1) // 2))  # r=1 divides every i: all odd primes
    C = wheel_C(np.array([2], dtype=np.int64), A[2], B[2], T - 2) if B[2] > A[2] else np.zeros(0, np.int64)
    stats = {2: (len(full), len(C), int(full[0]))}; kept = {}
    log("t=2 A=%d B=%d |Full|=%d |C|=%d" % (A[2], B[2], len(full), len(C)))
    for t in range(3, T + 1):
        tlev = time.time()
        S = np.union1d(full, C) if len(C) else full
        del full, C
        if t - 1 >= keep_from: kept[t - 1] = S
        imax = (A[t] - 1) // 2
        L = T - t
        EA = float(sum(int((imax // S[k:k + (1 << 24)]).sum()) for k in range(0, len(S), 1 << 24)))
        pieces = None
        if EA * CS_CAND < imax * CS_SIEVE or A[t] > 3_900_000_000_000:
            full = cand_full(S, A[t]); mode = "cand(E=%.3g)" % EA
        else:
            pieces = sieve_full(S, imax); mode = "sieve(E=%.3g)" % EA
        if B[t] > A[t]:
            Wo = odd_wheel(L)
            EB = float(sum(int(((B[t] // 2) // S[k:k + (1 << 24)]).sum() - ((A[t] // 2) // S[k:k + (1 << 24)]).sum())
                           for k in range(0, len(S), 1 << 24))) / Wo
            if EB * CS_CAND < (B[t] - A[t]) / (2 * Wo) * 0.3e-6:
                C = cand_C(S, A[t], B[t], L); mode += " Ccand(E=%.3g)" % EB
            else:
                C = wheel_C(S, A[t], B[t], L); mode += " Cwheel"
        else:
            C = np.zeros(0, np.int64)
        del S
        if pieces is not None:
            full = assemble(pieces); del pieces
        mn = int(full[0]) if len(full) else None
        stats[t] = (len(full), len(C), mn)
        if verbose: log("t=%d A=%d B=%d |Full|=%d |C|=%d min=%s %s lev=%.1fs" % (t, A[t], B[t], len(full), len(C), mn, mode, time.time() - tlev))
    kept[T] = full
    return stats, kept

memo = {2: (1, None)}
def H(p):
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

LEG1_T20 = [(2, 912392, 0, 3), (3, 1745871, 0, 7), (4, 3346326, 0, 23), (5, 6303716, 0, 47), (6, 9787450, 0, 283),
            (7, 10486429, 0, 719), (8, 7986676, 0, 1439), (9, 4671246, 0, 2879), (10, 2214896, 0, 34549),
            (11, 900139, 0, 138197), (12, 324237, 0, 1266767), (13, 103861, 0, 14619833), (14, 28475, 0, 36449279),
            (15, 6390, 0, 377982107), (16, 1212, 1, 1432349099), (17, 209, 1, 22111003847), (18, 38, 1, 54560052479),
            (19, 4, 1, 619108107719), (20, 1, 0, 7242080052479)]
PKNOWN = {14: 36449279, 15: 377982107, 16: 1432349099, 17: 22111003847, 18: 54560052479, 19: 619108107719,
          20: 7242080052479, 21: 64750853277599, 22: 866284735109723, 23: 2957807053316399}
MODE = "P24"            # TEST | P23 | P24
if MODE == "TEST": T, Y = 20, 7_360_000_000_000
elif MODE == "P23": T, Y = 23, 3465138940438892
else: T, Y = 24, 9 * 10**15
log("MODE %s T=%d Y=%d" % (MODE, T, Y))
st, kept = run(T, Y, keep_from=T - 4)
trip = [(t,) + st[t] for t in sorted(st)]
print("checkpoint triples (t, |Full_t|, |C_t|, min Full_t):", trip, flush=True)
for t in sorted(kept):
    v = kept[t].tolist(); print("level %d set S_t = Full_t ∪ C_t (%d):" % (t, len(v)), v[:60], flush=True)
top = kept[T].tolist()
Afin = {t: (Y >> (T - t + 1)) for t in range(2, T)}
if top:
    p = top[0]; h = H(p); c = chain(p)
    valid = len(c) == h and c[0] == 2 and all((c[i + 1] - 1) % c[i] == 0 and pari.isprime(c[i + 1]) for i in range(len(c) - 1))
    hs = [H(x) for x in top[:30]]
    print("H of top elements:", hs)
    desc = "min R_%d ∩ (0,%d] = %d, |R_%d ∩ (0,Y]| = %d, H=%d exact (Pratt recursion), chain valid %s, chain %s" % (T, Y, p, T, len(top), h, valid, c)
else:
    desc = "R_%d ∩ (0,%d] is EMPTY, i.e. P(%d) > %d" % (T, Y, T, Y)
Afin[T] = Y
extra = []
for t in sorted(st):
    if t not in PKNOWN: continue
    mn = st[t][2]; P = PKNOWN[t]
    ok = (mn == P) if P <= Afin[t] else (mn is None)
    extra.append("level %d: min Full=%s, A=%d, believed P(%d)=%d: %s" % (t, mn, Afin[t], t, P, "consistent" if ok else "CONTRADICTS"))
if MODE == "TEST":
    print("TEST triples equal leg-1/C1:", trip == LEG1_T20)
print("RESULT: " + desc + "; " + "; ".join(extra))
