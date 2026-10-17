## Result
Marathon leg 1. Novelty status, from the harness OEIS lookup: P(1..21) are already KNOWN as numbers. P(21)=64750853277599 is the LAST listed term of A056637 (least prime of Erdős–Selfridge class n−, a(20)) and of A082449 (a(20)). Both entries are marked "more", so **the first open term is P(22)**.
- C1 (PROVED, computer-certified, ~45 s): a new refined pyramid (Lemma R, pure-2-tail refinement) is a second, independent implementation. It reproduces P(3..20) exactly, including P(19)=619108107719 (deep/C1 had only an upper bound) and P(20)=7242080052479 (deep/C2 "conditional": one implementation). These values are known (OEIS), so C1 is a verification, not a record.
- C2 (CONJECTURED: proved modulo the correctness of deep's long_pyr21 output, which is not certified here): P(22) > 1.792·10^14. The three R_21 elements ≤ 8.96e13 are 64750853277599, 70643220056567 and 85301359593119; 2q+1 is composite for each of them.
- C3 (PROVED, routine): P(k) = A082449(k−1) (gpf-iteration record) exactly for k ≤ 20 (k=21 given P(21)), by the criterion g(P(k)) ≥ k−1. A056637 is a different sequence: the class falls short at k = 13, 18, 20. So the open term is A082449(21), and it equals P(22) iff g(P(22)) ≥ 21.
- P(22) itself: long_p22.py (refined pyramid, T=22, Y=866284735109723 = the certified deep/C3 upper bound) is queued as a LONG. Est. 20–40 min. It is exhaustive on (0, Y], so it must return P(22). It also re-derives R_21 ∩ (0, 2.16e14], an independent check of P(21). No claim is made about its outcome before it runs.

## Claims
### C1
STATEMENT: Let H(p) be the maximum length of a prime chain ending at p (H(2)=1), R_t={p prime: H(p) ≥ t}, P(t)=min R_t. Then P(3..20) = 7, 23, 47, 283, 719, 1439, 2879, 34549, 138197, 1266767, 14619833, 36449279, 377982107, 1432349099, 22111003847, 54560052479, 619108107719, 7242080052479. Moreover R_20 ∩ (0, 7.36·10^12] = {7242080052479}, and R_19 ∩ (0, 1.84·10^12] ∪ C_19 = {619108107719, 654720629749, 859409458847, 1326660230783, 3621040026239} (first four: all of R_19 ∩ (0,1.84e12]).
STATUS: PROVED (computer-assisted)
TYPE: SPECIAL
BEYOND: The values are known numerically (OEIS A082449/A056637), so this is not a record. It closes two gaps the referee left in the team's own claims: deep/C1's P(19) minimality was not certified, and deep/C2 had one implementation. This is a second implementation with different ranges and a different algorithm (refined pyramid, adaptive candidate/sieve, wheel for 2-tails).
PROOF:
Lemma 1 (deep/C1). For p ≥ 3 and t ≥ 3: p ∈ R_t iff some r ∈ R_{t−1} divides p−1. Every such r is odd, so p = mr+1 with m even and r ≤ (p−1)/2. R_2 = odd primes.
Lemma R (refinement). Fix T and Y. Let p_2<…<p_T be the last T−1 terms of a chain from 2 (so p_t ∈ R_t), with p_T ≤ Y and m_i = (p_{i+1}−1)/p_i, which is even ≥ 2 for i ≥ 2. For 2 ≤ t < T, either (a) p_t ≤ A_t := ⌊Y/2^{T−t+1}⌋, or (b) m_t = … = m_{T−1} = 2. In case (b), p_t ≤ B_t := ⌊(Y+1)/2^{T−t}⌋ − 1, and 2^i(p_t+1)−1 is prime for i=1..T−t.
Proof: p_T > p_t·∏_{i=t}^{T−1} m_i. If some m_i ≥ 4, the product is ≥ 2^{T−t+1}, so p_t < Y/2^{T−t+1}. Otherwise p_{t+i} = 2^i(p_t+1)−1, and p_T ≤ Y gives the bound. ∎
Define Full_t = R_t ∩ (0, A_t] and C_t = {q ∈ R_t ∩ (A_t, B_t] : 2^i(q+1)−1 prime for i=1..T−t}, with A_T = B_T = Y and S_t = Full_t ∪ C_t.
Recursion (proved by induction on t):
- Full_t = {p ≤ A_t prime : ∃ r ∈ S_{t−1}, r | p−1}. (⊆R_t by Lemma 1. ⊇: a witness r ≤ (p−1)/2 ≤ ⌊A_t/2⌋ = A_{t−1} for t<T. For t=T, r ≤ Y/4 = A_{T−1}, or r ∈ (Y/4,(Y−1)/2] with m=2, so r ∈ C_{T−1}.)
- C_t = {q ∈ (A_t,B_t] prime with 2-tail : ∃ r ∈ S_{t−1}, r | q−1}. (Witness r with m ≥ 4 has r ≤ (B_t−1)/4 < Y/2^{T−t+2}, so r ∈ Full_{t−1}. With m=2, r = (q−1)/2 ≤ B_{t−1} and r has a 2-tail of length T−t+1, so r ∈ Full_{t−1} ∪ C_{t−1}.)
Hence R_T ∩ (0,Y] = Full_T, computed exactly.
Wheel lemma (used to enumerate C_t at sieve levels). If q > ℓ has a 2-tail of length L, then q+1 ≡ 0 mod 2ℓ for every odd prime ℓ ≤ L+2 with 2 a primitive root mod ℓ. (Otherwise q+1 ≡ 2^{−i} mod ℓ for some i ≤ ℓ−2 ≤ L, so ℓ | 2^i(q+1)−1, which is > ℓ.) This is the frontier map's p1/C2(ii) in a slightly sharper range. For wheel candidates, membership is decided by factoring q−1 and looking each prime factor up in S_{t−1}.
Computation: check_c1.py, T=20, Y=7.36e12. Full_t is computed by segmented sieve + marking, or by enumerating all candidates jq·2+1 and testing them with PARI isprime (BPSW, proven below 2^64; all values < 2^43). The method is chosen adaptively. Output: min Full_t = P(t) ≤ A_t for t=3..20 and Full_20 = {7242080052479}. The witness chain is re-derived from the top element by an exact Pratt recursion (factor p−1 recursively; independent of the pyramid), giving H = 20.
AUDIT:
- Dependency chain: Lemma 1, Lemma R, the recursion, the code. Lemma R's inequality p_T > p_t∏m_i holds because p_{i+1} = m_i p_i + 1 > m_i p_i.
- The floor bookkeeping was checked by hand: A_{t−1} = ⌊A_t/2⌋ for t<T, B_{t−1} ≥ (B_t−1)/2, and (B_t−1)/4 < Y/2^{T−t+2}.
- Code tests:
  - T=17, Y=8e10 reproduces all 14 check_c1 (deep) counts |R_t(Y_t)|, t=3..16, exactly (A_t equals deep's Y_t there).
  - T=20 reproduces P(15..20), and the top set is the singleton deep/C4 found.
  - Level-2 tails and the wheel modulus W are computed from a primitive-root test (W=81510 = 2·3·5·11·13·19 at L=18, 4290 at L=11..16, 330 at L=9,10).
- Sensitivity: m_1 may be 1 (2→3), but Lemma R uses only m_i for i ≥ 2.
CERTIFICATE: deterministic exhaustive refined pyramid (T=20, Y=7.36e12), rebuilt from scratch. Claimed minima and the top set are embedded.
CHECK: check_c1.py (≈45 s; prints CERTIFIED)
CONCERNS: none mathematical. Values are known in OEIS (as A082449/A056637 terms), hence not new.

### C2
STATEMENT: P(22) > 1.792·10^14 (no prime chain of length 22 has last term ≤ 179200000000000).
STATUS: CONJECTURED (proved modulo the correctness of the completed LONG run deep/long_pyr21.py, whose source is not in this sandbox)
TYPE: SPECIAL
BEYOND: Beyond P(22) ≥ 2P(21)+1. It is the first lower bound on the open OEIS term.
PROOF: long_pyr21 reported R_21 ∩ (0, 8.96e13] = {64750853277599, 70643220056567, 85301359593119} (the output line in TASK.md is truncated at the front; these are the visible elements). Any p ∈ R_22 with p ≤ 1.792e14 has a predecessor r ≤ (p−1)/2 ≤ 8.96e13, so r is in that set and m = (p−1)/r ≤ 2 for all three. q22.py: 2r+1 factors as 11·2013227·5847767, 5·1604833·17607619 and 61·1303·1933·1110401.
CONCERNS: (1) Exactness of the R_21 list rests on long_pyr21 only. (2) The front of the printed list is truncated, so smaller elements might be missing. (Any smaller element would be < P(21), which contradicts its RESULT line.) long_p22 re-derives this independently.

### C3
STATEMENT: Let g(p) be the number of steps of p ↦ gpf(p−1) needed to reach 2, and let A082449(n) = min{p prime : g(p) ≥ n}. Then for every n ≥ 1, A082449(n) ≥ P(n+1), with equality iff g(P(n+1)) ≥ n. For n = 1..19, A082449(n) = P(n+1), with P(n+1) as in C1. The same holds for n = 20 given P(21) = 64750853277599. In contrast, A056637 (least prime of Erdős–Selfridge class n) satisfies A056637(n) ≥ P(n+1), but the class of P(k) is < k−1 for k = 2, 3, 13, 18, 20. So A056637 differs from P(k+1) at least where minimality fails, and only A082449 is the same sequence as P(k+1) (so far).
STATUS: PROVED (for n ≤ 19; n = 20 conditional on P(21))
TYPE: OTHER
BEYOND: It identifies exactly which OEIS entry our P(k) is, and gives a one-line test for whether P(22) is the open term A082449(21): it is iff g(P(22)) ≥ 21. Routine.
PROOF:
- g(p) ≤ H(p) − 1: the orbit p, gpf(p−1), …, 2 reversed is a prime chain of length g(p)+1 ending at p.
- Hence g(p) ≥ n implies H(p) ≥ n+1, so A082449(n) ≥ P(n+1).
- If g(P(n+1)) ≥ n then A082449(n) ≤ P(n+1).
- Conversely, if A082449(n) = P(n+1) then g(P(n+1)) ≥ n by definition.
- The same argument applies to the class: cls(2)=cls(3)=0 and cls(p) = 1 + max cls(r) over r | p−1, so cls(p) ≤ H(p) − 1 by induction.
- check_c3.py computes H and g for the 21 values by PARI factorisation: H(P(k)) = k and g(P(k)) = k−1 for all k ≤ 21.
- oeis_map.py: cls(P(k)) = k−1 except at k = 2, 3, 13, 18, 20, where cls = 0, 1, 11, 16, 18.
AUDIT: The inequality direction was checked on all 21 values. g and cls follow the OEIS definitions as stated in their titles: A082449 counts steps to reach 2; A056637 is "class n−" with class 1 = p−1 3-smooth. The equality claim for A056637 is NOT made.
CERTIFICATE: the 21 values embedded; H and g recomputed by factorisation.
CHECK: check_c3.py
CONCERNS: the A082449 indexing (a(n) ↔ g ≥ n) is from its title as quoted by the harness; it matches the harness's report a(19)=7242080052479=P(20) and a(20)=P(21). The UB endpoint 866284735109723 has H=22, cls=21, g=21.

## Routes
- ROUTE: novelty check via the harness OEIS lookup | OUTCOME: P(19..21) KNOWN (A082449 a(18..20), A056637 a(18..20)); P(22) is the first open term | BARRIER: none; this retargets the marathon to P(22).
- ROUTE: one more pyramid level from long_pyr21's R_21 | OUTCOME: P(22) > 1.792e14 (C2) | BARRIER: needs R_21 beyond 8.96e13.
- ROUTE: refined pyramid (Lemma R: only pure-2 tails need the factor-2 range) + adaptive candidate testing (PARI isprime 0.3 µs, conversion 0.4 µs) + wheel for 2-tails | OUTCOME: T=20 in 41 s (old: 86 s numpy, 390 s GP). P(22) at Y=8.66e14 projected at ~29× the T=20 cost, ≈20–40 min, memory peak ≈6 GB | BARRIER: the 120 s cap, so it is a LONG.
- ROUTE: beam seeded with the exact level sets of the T=20 refined pyramid (N=3000 smallest per level, m ≤ 3000) | OUTCOME: rediscovers P(21)=64750853277599 as its level-21 minimum, which is consistent evidence for long_pyr21. Level 22: 866284735109723, the same as deep/C3, so no better UB for P(22) | BARRIER: int64 cap on m·q; not exhaustive.
- ROUTE: wide GP beam B=16000 (deep's algorithm) | OUTCOME: in 120 s it reached k=43; k=29 improves (3.94e22 vs 6.57e22); k=21 gives only 8.53e13 (it misses P(21)); k=22, 23 are unchanged. Queued as LONG for k ≤ 100 | BARRIER: 120 s cap.
- ROUTE (analysis): P(23) | OUTCOME: out of reach of a 2 h LONG. UB 1.14e16 means ~13× the P(22) run (~5 h), and the dense levels cannot be split across runs that share no files | BARRIER: numpy sieve speed (~8 ns/number) and the 2 h cap. It needs a better UB, or the {2,4}-tail refinement (≤1.5×).
- ROUTE (analysis): treat m ∈ {2,4} as special too (gain 3 instead of 2) | OUTCOME: not implemented | BARRIER: needs a wheel for mixed {2,4} words. The gain is 1.5×, not needed for P(22).

## Next
NEXT (leg 2):
(1) Read the long_p22 RESULT. Plan B if it crashed (memory) or timed out: rerun with Y lowered. Since P(22) > 1.792e14 (C2), Y must stay above that, so Y=4.4e14 halves the cost; an empty top set then gives P(22) > Y.
(2) Independent reproduction of P(22). The deep's unrefined numpy pyramid (check_c2 code) needs F = ⌈P(22)/1.28e12⌉, i.e. about 4.8× long_pyr21 if P(22) ≈ 8.7e14. GP at full scale is infeasible: about 3e8-element GP vectors at level 7.
(3) For the OEIS comparison, A056637 (ES class) and A082449 (gpf iteration) are not definitionally P(k−1). Check the class (2,3 lumped) and the gpf-iteration length of P(22) directly; if they agree, P(22) is the next term of both.
(4) Embed the long_beam words in check_c3b.py.
Earlier text: read the long_p22 RESULT. If it is consistent (the UB endpoint is in the top set, the level-21 minimum is 64750853277599, and the witness is valid), record P(22) as C3 and check it against A056637 (class) / A082449 (gpf iteration), since those definitions differ from H. Then P(23): needs a better upper bound than 1.14e16 (deep/C3) and Y ~ 13× larger. Use Lemma R with {2,4}-tails, or a beam seeded from the exact level sets that long_p22 prints.
LONG: long_beam.py | 2 | wide GP beam (B=16000; TEST mode B=400 reproduces deep/C3 exactly): Pocklington-proved chains for k ≤ 100. It prints the multiplier words (as m/2) for every improved k ≤ 40 and k ≡ 0 mod 10, plus the full log10 table. Next leg: embed the words in a checker to sharpen C3 (part b)
LONG: long_p22.py | 1.5 | P(22) exactly: exhaustive refined pyramid over (0, 866284735109723] (the upper bound is the certified deep/C3 chain), with exact Pratt-recursion witness, plus R_21 ∩ (0,2.16e14] (independent re-derivation of P(21)) and checkpoint counts

## Data
check_c1 (T=20, Y=7.36e12) checkpoint counts (t, |Full_t| = |R_t ∩ (0, A_t]|, |C_t|, min):
(2,912392,0,3) (3,1745871,0,7) (4,3346326,0,23) (5,6303716,0,47) (6,9787450,0,283) (7,10486429,0,719) (8,7986676,0,1439) (9,4671246,0,2879) (10,2214896,0,34549) (11,900139,0,138197) (12,324237,0,1266767) (13,103861,0,14619833) (14,28475,0,36449279) (15,6390,0,377982107) (16,1212,1,1432349099) (17,209,1,22111003847) (18,38,1,54560052479) (19,4,1,619108107719) (20,1,0,7242080052479), with A_t = ⌊7.36e12/2^{21−t}⌋.
Level-19 set (Full ∪ C): 619108107719, 654720629749, 859409458847, 1326660230783, 3621040026239. The 2-tail element 3621040026239 → 7242080052479 = P(20).
Small multipliers of the known R_21 elements (q22.py): 2q+1, 4q+1, 6q+1 are all composite for q ∈ {64750853277599, 70643220056567, 85301359593119}.

## Certificate checks (re-run by the harness)

### C1 certificate: CERTIFIED
`check_c1.py`: exit 0, 42.4 s. Last output:
```
429704729711, 438658307083, 439740436559, 441163522493, 441520125353, 444389610839, 449757617087, 450747812717, 451666575289, 452722808227, 454735058269, 454904911049, 454904913383, 455318026789, 458514429089, 905260006559]
level 18 set (39): [54560052479, 110874748763, 136132234559, 272942948093, 309554053859, 328082152283, 369594037559, 394823306803, 397998069247, 429704729423, 429704729711, 450747812717, 454904913383, 486998692919, 491040472303, 505896071963, 619108107719, 654720629749, 663330115391, 682019038997, 682330504459, 702398777273, 713822681983, 716396531387, 756280324277, 764151384377, 772639606967, 775924401293, 793892075279, 795688878827, 798298191077, 815092290137, 816793407349, 820205380703, 832073082839, 859409458847, 882327044987, 883040250707, 1810520013119]
level 19 set (5): [619108107719, 654720629749, 859409458847, 1326660230783, 3621040026239]
level 20 set (1): [7242080052479]
Pratt check: H(7242080052479) = 20, chain valid 1
H of first 50 top elements: [20]
RESULT: P(20)=7242080052479 (exhaustive over (0,7360000000000], refined pyramid; H=20 exact via Pratt recursion, witness [2, 3, 7, 127, 509, 1019, 2039, 4079, 32633, 65267, 913739, 1827479, 109648741, 1315784893, 5263139573, 452630003279, 905260006559, 1810520013119, 3621040026239, 7242080052479]); |R_20 ∩ (0,Y]|=1; UB endpoint 7242080052479 found in top set: True; min of level 19 set = 619108107719 (expected P(19)=619108107719): True
minima = claimed P(t) for t=3..20, each <= A_t: True
CERTIFIED

```
Checker source (10871 characters):
```python
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
    if len(n) == 0: return []
    n = presieve(n, L) if L <= 64 else n
    out = []
    for k in range(0, len(n), 1 << 21):
        v = pari(n[k:k + (1 << 21)].tolist())
        res = _isp(v) if L == 0 else _tail(v, L)
        out.extend(int(x) for x in res)
    return out

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
        found = []; tl = time.time()
        for i in gen_candidates(S, 1, imaxA):
            found.extend(test(2 * i + 1, 0))
            if time.time() - tl > 120:
                log("  level %d cand progress i=%d of %d, found %d" % (t, int(i[-1]), imaxA, len(found))); tl = time.time()
        full = np.unique(np.array(found, dtype=np.int64)); modeA = "cand(%d)" % EA
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
            

[... 1871 characters omitted from the middle ...]

 use the generic wheel via a dummy S = {} check skipped
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

TEST = True   # checker for C1: T=20, Y=7.36e12
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
    hs = [H(x) for x in toplist[:50]]
    print("H of first 50 top elements:", hs)
    print("RESULT: P(%d)=%d (exhaustive over (0,%d], refined pyramid; H=%d exact via Pratt recursion, witness %s); |R_%d ∩ (0,Y]|=%d; UB endpoint %d found in top set: %s; min of level %d set = %s (expected P(%d)=%d): %s"
          % (T, p, Y, h, c, T, len(toplist), UB, ok_ub, T - 1, lev_prev[0] if lev_prev else None, T - 1, PREV, ok_prev))
else:
    print("RESULT: R_%d ∩ (0,%d] is EMPTY (inconsistent with the UB chain: BUG)" % (T, Y))
CLAIM = [None, 2, 3, 7, 23, 47, 283, 719, 1439, 2879, 34549, 138197, 1266767, 14619833, 36449279,
         377982107, 1432349099, 22111003847, 54560052479, 619108107719, 7242080052479]
A_ = {t: (Y >> (T - t + 1)) if t < T else Y for t in range(2, T + 1)}
okm = all(st[t][2] == CLAIM[t] and CLAIM[t] <= A_[t] for t in range(3, T + 1))
print("minima = claimed P(t) for t=3..20, each <= A_t:", okm)
if okm and toplist == [7242080052479] and ok_ub and ok_prev and valid and h == 20:
    print("CERTIFIED")

```
OEIS LOOKUP of the claim's values (automatic; a value OEIS lists is known, not a record):
- 1266767 is KNOWN to OEIS: A056637 (a(n) is the least prime of class n-, according to the Erdős-Selfridge classification of primes.): its term a(11), not its last term; the entry is marked 'more' (more terms wanted) | A081430 (Class 11- primes.): its term a(1), not its last term | A105017 (Positions of records in A064097.): its term a(34), not its last term
- 14619833 is KNOWN to OEIS: A246497 (Smallest k such that 9^^n is not congruent to 9^^(n-1) mod k, where 9^^n denotes the power tower 9^9^...^9 (in which 9 a): its term a(12), not its last term; the entry is marked 'more' (more terms wanted) | A082449 (Let f(p) = greatest prime divisor of p-1. Sequence gives smallest prime which takes at least n steps to reach 2 when f i): its term a(12), not its last term; the entry is marked 'more' (more terms wanted) | A175189 (Smallest integer m such that phi(phi(m))^n + tau(phi(m))^n = phi(rad(m))^n, where n is the number of iterations of phi(p): its term a(12), not its last term; the entry is marked 'more' (more terms wanted)
- 36449279 is KNOWN to OEIS: A056637 (a(n) is the least prime of class n-, according to the Erdős-Selfridge classification of primes.): its term a(13), not its last term; the entry is marked 'more' (more terms wanted) | A246491 (Smallest k such that 3^^n is not congruent to 3^^(n-1) mod k, where 3^^n denotes the power tower 3^3^...^3 (in which 3 a): its term a(14), not its last term; the entry is marked 'more' (more terms wanted) | A246497 (Smallest k such that 9^^n is not congruent to 9^^(n-1) mod k, where 9^^n denotes the power tower 9^9^...^9 (in which 9 a): its term a(13), not its last term; the entry is marked 'more' (more terms wanted)
- 377982107 is KNOWN to OEIS: A056637 (a(n) is the least prime of class n-, according to the Erdős-Selfridge classification of primes.): its term a(14), not its last term; the entry is marked 'more' (more terms wanted) | A246491 (Smallest k such that 3^^n is not congruent to 3^^(n-1) mod k, where 3^^n denotes the power tower 3^3^...^3 (in which 3 a): its term a(15), the LAST listed term; the entry is marked 'more' (more terms wanted) | A129248 (a(n) = n-th prime of class 14- according to the Erdős-Selfridge classification.): its term a(1), not its last term
- 1432349099 is KNOWN to OEIS: A056637 (a(n) is the least prime of class n-, according to the Erdős-Selfridge classification of primes.): its term a(15), not its last term; the entry is marked 'more' (more terms wanted) | A246497 (Smallest k such that 9^^n is not congruent to 9^^(n-1) mod k, where 9^^n denotes the power tower 9^9^...^9 (in which 9 a): its term a(15), the LAST listed term; the entry is marked 'more' (more terms wanted) | A082449 (Let f(p) = greatest prime divisor of p-1. Sequence gives smallest prime which takes at least n steps to reach 2 when f i): its term a(15), not its last term; the entry is marked 'more' (more terms wanted)
- 22111003847 is KNOWN to OEIS: A056637 (a(n) is the least prime of class n-, according to the Erdős-Selfridge classification of primes.): its term a(16), not its last term; the entry is marked 'more' (more terms wanted) | A082449 (Let f(p) = greatest prime divisor of p-1. Sequence gives smallest prime which takes at least n steps to reach 2 when f i): its term a(16), not its last term; the entry is marked 'more' (more terms wanted) | A129250 (Primes of Erdős-Selfridge class 16-.): its term a(1), not its last term; the entry is marked 'more' (more terms wanted)
- 54560052479 is KNOWN to OEIS: A082449 (Let f(p) = greatest prime divisor of p-1. Sequence gives smallest prime which takes at least n steps to reach 2 when f i): its term a(17), not its last term; the entry is marked 'more' (more terms wanted) | A129250 (Primes of Erdős-Selfridge class 16-.): its term a(8), not its last term; the entry is marked 'more' (more terms wanted)
- 619108107719 is KNOWN to OEIS: A056637 (a(n) is the least prime of class n-, according to the Erdős-Selfridge classification of primes.): its term a(18), not its last term; the entry is marked 'more' (more terms wanted) | A082449 (Let f(p) = greatest prime divisor of p-1. Sequence gives smallest prime which takes at least n steps to reach 2 when f i): its term a(18), not its last term; the entry is marked 'more' (more terms wanted) | A396362 (Primes of Erdős-Selfridge class 18-.): its term a(1), not its last term

### C3 certificate: CERTIFIED
`check_c3.py`: exit 0, 0.1 s. Last output:
```
1 2 H = 1 g = 0 True
2 3 H = 2 g = 1 True
3 7 H = 3 g = 2 True
4 23 H = 4 g = 3 True
5 47 H = 5 g = 4 True
6 283 H = 6 g = 5 True
7 719 H = 7 g = 6 True
8 1439 H = 8 g = 7 True
9 2879 H = 9 g = 8 True
10 34549 H = 10 g = 9 True
11 138197 H = 11 g = 10 True
12 1266767 H = 12 g = 11 True
13 14619833 H = 13 g = 12 True
14 36449279 H = 14 g = 13 True
15 377982107 H = 15 g = 14 True
16 1432349099 H = 16 g = 15 True
17 22111003847 H = 17 g = 16 True
18 54560052479 H = 18 g = 17 True
19 619108107719 H = 19 g = 18 True
20 7242080052479 H = 20 g = 19 True
21 64750853277599 H = 21 g = 20 True
CERTIFIED

```
Checker source (1079 characters):
```python
# Checker for C3: g(p) = number of steps of p -> gpf(p-1) to reach 2 (A082449's statistic), H(p) = Pratt height.
# Lemma: g(p) <= H(p)-1 (the gpf orbit reversed is a chain of length g(p)+1 ending at p). Hence
# A082449(n) := min{p : g(p) >= n} >= P(n+1), with equality iff g(P(n+1)) >= n.
# We verify g(P(k)) = k-1 = H(P(k)) - 1 for the claimed values P(2..21) (P(2..20) are certified by check_c1.py).
from cypari2 import Pari
from functools import lru_cache
pari = Pari()
P = [2, 3, 7, 23, 47, 283, 719, 1439, 2879, 34549, 138197, 1266767, 14619833, 36449279, 377982107, 1432349099,
     22111003847, 54560052479, 619108107719, 7242080052479, 64750853277599]
def pf(n): return [int(x) for x in pari.factor(n)[0]] if n > 1 else []
@lru_cache(None)
def H(p): return 1 if p == 2 else 1 + max(H(r) for r in pf(p - 1))
@lru_cache(None)
def g(p): return 0 if p == 2 else 1 + g(max(pf(p - 1)))
ok = all(pari.isprime(p) for p in P)
for k, p in enumerate(P, 1):
    good = H(p) == k and g(p) == k - 1
    print(k, p, "H =", H(p), "g =", g(p), good); ok &= good
if ok: print("CERTIFIED")

```
OEIS LOOKUP of the claim's values (automatic; a value OEIS lists is known, not a record):
- 64750853277599 is KNOWN to OEIS: A056637 (a(n) is the least prime of class n-, according to the Erdős-Selfridge classification of primes.): its term a(20), the LAST listed term; the entry is marked 'more' (more terms wanted) | A082449 (Let f(p) = greatest prime divisor of p-1. Sequence gives smallest prime which takes at least n steps to reach 2 when f i): its term a(20), the LAST listed term; the entry is marked 'more' (more terms wanted)
