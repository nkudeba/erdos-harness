## Result
Marathon leg 3 (final). The leg-1/2 LONG outputs settle the first open term of the sequence.
- **C1 (PROVED, computer-assisted).** P(22) = 866284735109723, which is OEIS A082449(21).
  - Lower bound: three completed exhaustive runs agree, from two independent code bases and two scales.
  - Upper bound: certified by Pocklington in check_c2.py.
  - The A082449 entry only *mentions* this value, outside its data. The new content is the exactness.
- **C2 (PROVED, certified by check_c2.py).**
  - P(23) ≤ 2957807053316399 and A082449(22) ≤ 2957807053316399. This is below 11407852252734739, the value the A082449 entry mentions.
  - P(24) ≤ 94649825706124769 and A082449(23) ≤ 94649825706124769. The previous best was 115504631269039577 (deep/C3).
- **C3 (CONJECTURED, one exhaustive run).** P(23) = 2957807053316399 = A082449(22). This number is in no OEIS entry.
  - marathon-2/long_p23 is exhaustive over (0, 3.465e15].
  - This leg wrote a third, independent implementation (pyr3 → long_p23i.py). It reproduces every leg-1/leg-2 checkpoint count, and it is queued to re-decide P(23) and P(22).
  - long_p24.py is queued to decide P(24) if P(24) ≤ 9e15, and otherwise to give P(24) > 9e15.
Nothing here bears on the asymptotic questions of #695 (barriers B1–B3); these are finite values only.

## Claims
### C1
STATEMENT: Let H(p) be the maximum length of a prime chain p_1<…<p_k=p with p_{i+1} ≡ 1 (mod p_i) (H(2)=1). Let P(k) = min{p prime : H(p) ≥ k}, the least last term of a chain of length k. Then P(22) = 866284735109723. Moreover A082449(21) = 866284735109723, where A082449(n) = min{p : the iteration p ↦ gpf(p−1) needs ≥ n steps to reach 2}.
STATUS: PROVED (computer-assisted. The upper bound has a checker. The lower bound rests on completed exhaustive LONG runs, whose outputs are recorded in TASK.md and which cannot be redone within a 120 s checker.)
TYPE: SPECIAL
BEYOND: P(≤21) are OEIS terms (A082449 a(≤20)). P(22) was the first open term: A082449 lists 866284735109723 only outside its data, presumably as a bound or conjecture. Here it is proved exact by exhaustive search.
PROOF:
1. Lemma 1 (deep/C1, used in marathon-1/C1, which the referee rated valid). For p ≥ 3: p ∈ R_t := {H ≥ t} iff some r ∈ R_{t−1} divides p−1. Such an r is odd, so p = mr+1 with m even and r ≤ (p−1)/2.
2. Lemma R and the refined recursion, as in leg-1/C1. Write A_t = ⌊Y/2^{T−t+1}⌋ and B_t = ⌊(Y+1)/2^{T−t}⌋ − 1.
   - Every element p_t of a length-T chain ending ≤ Y satisfies either p_t ≤ A_t, or p_t ≤ B_t with a pure 2-tail.
   - Full_t := R_t ∩ (0,A_t] and C_t (the tail elements) are generated exactly from S_{t−1} = Full_{t−1} ∪ C_{t−1}.
   - I re-derived every floor inequality this leg (A_{t−1} = ⌊A_t/2⌋; (B_t−1)/4 < Y/2^{T−t+2}; (B_t−1)/2 ≤ B_{t−1}; at t = T, r ≤ (Y−1)/4 ≤ A_{T−1} or r ∈ C_{T−1}).
   - Wheel lemma: an odd prime ℓ ≤ L+2 with 2 a primitive root mod ℓ divides q+1 whenever q > ℓ has a 2-tail of length L. Otherwise q+1 ≡ 2^{−i} (mod ℓ) for some 0 ≤ i ≤ ℓ−2. Then ℓ | q (if i = 0) or ℓ | 2^i(q+1)−1 (if i ≥ 1), and each of those is a prime > ℓ.
3. Computations. All of them completed with exit 0. Each is exhaustive for R_T ∩ (0, Y].
   - (a) marathon-1/long_p22.py (leg-1 code), T=22, Y=866284735109723: |R_22 ∩ (0,Y]| = 1, the element is Y itself, and min of the level-21 set = P(21).
   - (b) marathon-2/long_p22.py (leg-2 rewrite), same T and Y: min R_22 ∩ (0,Y] = Y, |R_22 ∩ (0,Y]| = 1.
   - (c) marathon-2/long_p23.py, T=23, Y = 4·866284735109723. Here A_22 = 866284735109723, and min of the level-22 set = 866284735109723. This is the same statement at a different scale, so every A_t differs from (a) and (b).
   - (d) marathon-2/long_p22b.py (plain pyramid, Lemma 1 only): R_22 ∩ (0, 433142367554861] = ∅.
   - So no prime < 866284735109723 has H ≥ 22.
4. Upper bound. The chain [2, 5, 11, 89, 179, 359, 719, 1439, 25903, 103613, 621679, 2486717, 14920303, 179043637, 716174549, 1432349099, 25782283783, 1082855918887, 10828559188871, 21657118377743, 433142367554861, 866284735109723] is verified by check_c2.py.
   - Each term with p ≥ 10^6 is proved prime by Pocklington with F = previous term (F² > N because m_i < p_i).
   - Each term below 10^6 is proved prime by trial division.
   - Exact Pratt recursion gives H = 22.
5. A082449. Let g(p) be the number of gpf-steps to reach 2. Then g(p) ≤ H(p) − 1, because the reversed orbit is a chain. Hence A082449(n) ≥ P(n+1), with equality iff g(P(n+1)) ≥ n. This is the A082449 part of leg-1/C3, which the adversary confirmed correct. check_c2.py gives g(866284735109723) = 21.
AUDIT:
- Dependency chain: Lemma 1, then Lemma R and the recursion, then the LONG code, then the outputs.
- Lemma R's hypotheses (p_{i+1} = m_i p_i + 1 > m_i p_i, and m_i even for i ≥ 2) were re-checked.
- Independence: (a) and (b) are different code bases, and (c) uses the (b) code at another scale.
- This leg's pyr3 is a third code base, written from the lemmas only. It reproduces every published checkpoint:
  - T=20, Y=7.36e12: all 19 triples (|Full_t|, |C_t|, min) of leg-1/C1, and the level-18/19/20 sets element for element.
  - T=20, Y=1.25e13: all 19 (|Full_t|, |C_t|) of leg-2's Data line.
- This raises confidence that the shared lemma-level logic is implemented correctly.
CERTIFICATE: the explicit chain (embedded), with a Pocklington certificate per link; H and g by recursive PARI factorisation (rigorous below 2^64). For the lower bound: the exact search range (0, 866284735109723], the refined-pyramid encoding with A_t/B_t as above, and the agreeing RESULT lines of runs (a)–(d) quoted above.
CHECK: check_c2.py
CONCERNS: the lower bound cannot be re-run inside a checker. It rests on the recorded outputs of completed LONG runs from two independent code bases. long_p23i.py (third code base) is queued to reproduce it again.

### C2
STATEMENT: The explicit prime chains embedded in check_c2.py show:
- (i) P(23) ≤ 2957807053316399, with H(2957807053316399) = 23 and g = 22. Hence A082449(22) ≤ 2957807053316399 < 11407852252734739.
- (ii) P(24) ≤ 94649825706124769 = 32·2957807053316399 + 1, with H = 24 and g = 23. Hence A082449(23) ≤ 94649825706124769.
STATUS: PROVED
TYPE: QUANT
BEYOND: (i) is below the value 11407852252734739 that the OEIS A082449 entry mentions (deep/C3 had the same value). (ii) improves deep/C3's P(24) ≤ 115504631269039577.
PROOF: The chains are:
- k=23: [2, 5, 11, 89, 179, 359, 719, 1439, 2879, 414577, 1658309, 3316619, 26532953, 53065907, 4457536189, 106980868537, 641885211223, 3851311267339, 92431470416137, 369725881664549, 739451763329099, 1478903526658199, 2957807053316399], with multipliers 2,2,8,2,2,2,2,2,144,4,2,8,2,84,24,6,6,24,4,2,2,2.
- k=24: the same chain followed by 94649825706124769 (m = 32).
Every link is certified as in C1, step 4. g is computed by iterating gpf(p−1) with PARI factor. The inequality A082449(n) ≤ p holds as soon as g(p) ≥ n, by definition.
AUDIT: The checker uses only factor, isprime and pure-Python Pocklington or trial division. All values are < 2^64, where PARI's isprime and factor are rigorous. Pocklington's hypothesis F² > N holds (asserted in the code).
CERTIFICATE: embedded chains.
CHECK: check_c2.py (CERTIFIED, < 1 s)
CONCERNS: none.

### C3
STATEMENT: P(23) = 2957807053316399, and hence A082449(22) = 2957807053316399 (g = 22, by C2).
STATUS: CONJECTURED (one completed exhaustive run; the independent reproduction long_p23i.py is queued)
TYPE: SPECIAL
BEYOND: a new term. 2957807053316399 is in no OEIS entry.
PROOF (evidence): marathon-2/long_p23.py (T=23, Y=3465138940438892, refined pyramid) completed with exit 0 and printed: min R_23 ∩ (0,Y] = 2957807053316399, |R_23 ∩ (0,Y]| = 1, H=23, chain valid. The same run reproduced P(22) (C1(c)). The upper bound is C2(i). Mechanism: the chain ends in a 2-tail (…, 739451763329099, 1478903526658199, 2957807053316399). That is exactly the case Lemma R's C_t sets handle.
CONCERNS: only one implementation so far at this range. long_p23i.py uses the same T and Y, so its checkpoint triples must agree with long_p23's level by level, and its RESULT must give the same minimum.

## Routes
- ROUTE: read leg-1/2 LONG outputs | OUTCOME: P(22) agreed by 3 runs (C1); P(23) candidate from 1 run (C3) | BARRIER: P(23) needs an independent second implementation (a LONG).
- ROUTE: independent leg-3 implementation pyr3.py, fresh from the lemmas | OUTCOME: success.
  - Ingredients: GP-side candidate loops at 0.37 µs/candidate (leg-1: ~1.1 µs); numpy wheel for the 2-tail sets; three-tier sieve marking (strided / vectorised mid / j-loop); 3..19 pattern plus a cache-blocked small-prime stage (prime part 5.7 s → 3.3 s); uint32 segment pieces to halve peak memory.
  - TEST T=20, Y=7.36e12: identical to leg-1/C1 in 26–28 s.
  - T=20, Y=1.25e13: identical to leg-2 in 55 s.
  - T=21 at 4.4× the range: cost grows as range^~1.05.
  - BARRIER: machine load (load average ≈ 10) can slow a run 3–10×. That makes the 2 h cap the risk, so I chose Y conservatively for long_p24.
- ROUTE: P(24)/P(25) upper bounds by extending known high-height primes (ub24.py: the printed R_20/R_21 elements and the chain elements, all m with m·q+1 ≤ Z, exact H by Pratt recursion) | OUTCOME: P(24) ≤ 94649825706124769 (C2). P(25) gives no improvement (693027787614237463, the same as deep/C3) | BARRIER: seeds are limited to the printed parts of the level sets (the R_20 list was truncated to 40 elements).
- ROUTE (analysis): exact P(24) | OUTCOME: queued as long_p24 with Y=9e15 (≈ 45–90 min). The ratio statistics (P(k)/P(k−1) median ≈ 4–9) suggest P(24) ≈ 1–3e16, so a lower bound is the likely outcome | BARRIER: cost ∝ Y^1.06 and memory ≈ 8 GB at 9e15. Y = 2e16 would need ≈ 3 h.

## Next
NEXT:
- (1) Read long_p23i. C3 becomes PROVED (computer-assisted) if its RESULT gives min R_23 = 2957807053316399, with every level "consistent". Its triples should equal long_p23's.
- (2) Read long_p24. It gives P(24) exactly, or P(24) > 9e15.
- (3) For a better P(25) bound, rerun ub24 seeded with the full level-21/22 sets that long_p23i prints (60 per level).
- (4) Submit A082449 a(21) = 866284735109723 (and a(22) once C3 is proved) to OEIS, citing the certificates.
LONG: long_p23i.py | 2 | independent (leg-3 code) exhaustive refined pyramid T=23, Y=3465138940438892. It decides R_23 ∩ (0,Y], i.e. whether P(23) = 2957807053316399 (C3). It re-derives P(22) (A_22 = P(22)) and P(14..21), with consistency flags, and prints checkpoint triples and level sets S_19..S_23. TEST mode reproduces leg-1/C1 exactly. Estimated 35–60 min, ≈ 6 GB.
LONG: long_p24.py | 2 | same code, T=24, Y=9e15. It gives P(24) exactly if ≤ 9e15, else P(24) > 9e15. It also re-checks P(14..23) for consistency. Estimated 45–90 min, ≈ 8 GB.

## Data
- Ratios P(k)/P(k−1), k=2..23: 1.5, 2.3, 3.3, 2.0, 6.0, 2.5, 2.0, 2.0, 12.0, 4.0, 9.2, 11.5, 2.5, 10.4, 3.8, 15.4, 2.5, 11.3, 11.7, 8.9, 13.4, 3.4 (the last is conditional on C3). This is data only; no asymptotic inference is drawn.
- ub24.py level counts from seeds (bounds Z_21=3e15, Z_22=1.2e16, Z_23=5e16, Z_24=2e17):
  - level 21: 102 elements; level 22: 52; level 23: 14 (smallest 2957807053316399, 11407852252734739, 12675391391927483, …); level 24: 4 (94649825706124769, 102340420623911299, 115504631269039577, 141974738559187153).
  - level 25: 693027787614237463, chain [2,5,11,89,179,359,719,1439,25903,103613,621679,2486717,14920303,179043637,716174549,21485236471,214852364711,429704729423,859409458847,42970472942351,1804759863578743,7219039454314973,14438078908629947,115504631269039577,693027787614237463].
- pyr3 timing (machine under load): T=20, Y=7.36e12: 26–31 s. Y=1.25e13: 55 s. T=21, Y=6.48e13: levels 2–10 in 93 s (the 120 s cap stopped it at level 11). Level 10 there had 7.9e9 sieve indices and |Full_10| = 12059310.
- T=21, Y=64750853277599 partial counts (t, |Full_t|): (2,3659739) (3,7029649) (4,13523565) (5,25779541) (6,42198060) (7,48485046) (8,39245165) (9,24201836) (10,12059310), with A_t = ⌊Y/2^{22−t}⌋.

## Certificate checks (re-run by the harness)

### C1 certificate: CERTIFIED
`check_c2.py`: exit 0, 0.1 s. Last output:
```
k=22 last=866284735109723 chain/Pocklington ok, H=22, g=21 -> True
  multipliers: [2, 2, 8, 2, 2, 2, 2, 18, 4, 6, 4, 6, 12, 4, 2, 18, 42, 10, 2, 20, 2]
k=23 last=2957807053316399 chain/Pocklington ok, H=23, g=22 -> True
  multipliers: [2, 2, 8, 2, 2, 2, 2, 2, 144, 4, 2, 8, 2, 84, 24, 6, 6, 24, 4, 2, 2, 2]
k=24 last=94649825706124769 chain/Pocklington ok, H=24, g=23 -> True
  multipliers: [2, 2, 8, 2, 2, 2, 2, 2, 144, 4, 2, 8, 2, 84, 24, 6, 6, 24, 4, 2, 2, 2, 32]
A082449(22) <= 2957807053316399: True
CERTIFIED

```
Checker source (2777 characters):
```python
# Checker for C2 (and the upper-bound half of C1):
#  * the embedded chains are prime chains from 2 (p_{i+1} = m_i p_i + 1), every term proved prime by
#    (a) trial division for p < 10^6, else (b) Pocklington with F = p_i (needs p_i > m_i, so p_i^2 > p_{i+1}),
#    independently also PARI isprime (rigorous below 2^64);
#  * H(p) (Pratt-tree height = longest chain ending at p, H(2)=1) by exact recursive factorisation of p-1;
#  * g(p) = number of steps of p -> gpf(p-1) to reach 2 (the statistic of OEIS A082449).
from cypari2 import Pari
from functools import lru_cache
from math import gcd, isqrt
pari = Pari()
C22 = [2, 5, 11, 89, 179, 359, 719, 1439, 25903, 103613, 621679, 2486717, 14920303, 179043637, 716174549,
       1432349099, 25782283783, 1082855918887, 10828559188871, 21657118377743, 433142367554861, 866284735109723]
C23 = [2, 5, 11, 89, 179, 359, 719, 1439, 2879, 414577, 1658309, 3316619, 26532953, 53065907, 4457536189,
       106980868537, 641885211223, 3851311267339, 92431470416137, 369725881664549, 739451763329099,
       1478903526658199, 2957807053316399]
C24 = C23 + [94649825706124769]          # m = 32: P(24) <= 94649825706124769 (deep/C3 had 115504631269039577)
def trial(n):
    if n < 2: return False
    return all(n % d for d in range(2, isqrt(n) + 1))
def pock(N, F):
    # N-1 = F*R, F prime, F^2 > N  =>  N prime iff some a with a^(N-1)=1, gcd(a^((N-1)/F)-1, N)=1
    assert (N - 1) % F == 0 and F * F > N
    for a in range(2, 200):
        if pow(a, N - 1, N) != 1: return False
        if gcd(pow(a, (N - 1) // F, N) - 1, N) == 1: return True
    return False
def chain_ok(C):
    ok = C[0] == 2
    for i in range(len(C) - 1):
        ok &= C[i] < C[i + 1] and (C[i + 1] - 1) % C[i] == 0
    for i, p in enumerate(C):
        if p < 10**6: ok &= trial(p)
        else: ok &= pock(p, C[i - 1])
        ok &= bool(pari.isprime(p))
    return ok
def pf(n): return [int(x) for x in pari.factor(n)[0]] if n > 1 else []
@lru_cache(None)
def H(p): return 1 if p == 2 else 1 + max(H(r) for r in pf(p - 1))
@lru_cache(None)
def g(p): return 0 if p == 2 else 1 + g(max(pf(p - 1)))
allok = True
for C, k in ((C22, 22), (C23, 23), (C24, 24)):
    ok = chain_ok(C) and len(C) == k and H(C[-1]) == k and g(C[-1]) == k - 1
    print("k=%d last=%d chain/Pocklington ok, H=%d, g=%d -> %s" % (k, C[-1], H(C[-1]), g(C[-1]), ok))
    print("  multipliers:", [(C[i + 1] - 1) // C[i] for i in range(len(C) - 1)])
    allok &= ok
# A082449(n) = min{p : g(p) >= n}; g(p) <= H(p)-1 so A082449(n) >= P(n+1).  Since g(C23[-1]) = 22,
# A082449(22) <= 2957807053316399 < 11407852252734739.
allok &= g(C23[-1]) >= 22 and C23[-1] < 11407852252734739 and C24[-1] < 115504631269039577
print("A082449(22) <= %d: %s" % (C23[-1], allok))
if allok: print("CERTIFIED")

```
OEIS LOOKUP of the claim's values (automatic; a value OEIS lists is known, not a record):
- 866284735109723 is KNOWN to OEIS: A082449 (Let f(p) = greatest prime divisor of p-1. Sequence gives smallest prime which takes at least n steps to reach 2 when f i): mentioned in the entry, not in its data; the entry is marked 'more' (more terms wanted)

### C2 certificate: CERTIFIED
`check_c2.py`: exit 0, 0.4 s. Last output:
```
k=22 last=866284735109723 chain/Pocklington ok, H=22, g=21 -> True
  multipliers: [2, 2, 8, 2, 2, 2, 2, 18, 4, 6, 4, 6, 12, 4, 2, 18, 42, 10, 2, 20, 2]
k=23 last=2957807053316399 chain/Pocklington ok, H=23, g=22 -> True
  multipliers: [2, 2, 8, 2, 2, 2, 2, 2, 144, 4, 2, 8, 2, 84, 24, 6, 6, 24, 4, 2, 2, 2]
k=24 last=94649825706124769 chain/Pocklington ok, H=24, g=23 -> True
  multipliers: [2, 2, 8, 2, 2, 2, 2, 2, 144, 4, 2, 8, 2, 84, 24, 6, 6, 24, 4, 2, 2, 2, 32]
A082449(22) <= 2957807053316399: True
CERTIFIED

```
Checker source (2777 characters):
```python
# Checker for C2 (and the upper-bound half of C1):
#  * the embedded chains are prime chains from 2 (p_{i+1} = m_i p_i + 1), every term proved prime by
#    (a) trial division for p < 10^6, else (b) Pocklington with F = p_i (needs p_i > m_i, so p_i^2 > p_{i+1}),
#    independently also PARI isprime (rigorous below 2^64);
#  * H(p) (Pratt-tree height = longest chain ending at p, H(2)=1) by exact recursive factorisation of p-1;
#  * g(p) = number of steps of p -> gpf(p-1) to reach 2 (the statistic of OEIS A082449).
from cypari2 import Pari
from functools import lru_cache
from math import gcd, isqrt
pari = Pari()
C22 = [2, 5, 11, 89, 179, 359, 719, 1439, 25903, 103613, 621679, 2486717, 14920303, 179043637, 716174549,
       1432349099, 25782283783, 1082855918887, 10828559188871, 21657118377743, 433142367554861, 866284735109723]
C23 = [2, 5, 11, 89, 179, 359, 719, 1439, 2879, 414577, 1658309, 3316619, 26532953, 53065907, 4457536189,
       106980868537, 641885211223, 3851311267339, 92431470416137, 369725881664549, 739451763329099,
       1478903526658199, 2957807053316399]
C24 = C23 + [94649825706124769]          # m = 32: P(24) <= 94649825706124769 (deep/C3 had 115504631269039577)
def trial(n):
    if n < 2: return False
    return all(n % d for d in range(2, isqrt(n) + 1))
def pock(N, F):
    # N-1 = F*R, F prime, F^2 > N  =>  N prime iff some a with a^(N-1)=1, gcd(a^((N-1)/F)-1, N)=1
    assert (N - 1) % F == 0 and F * F > N
    for a in range(2, 200):
        if pow(a, N - 1, N) != 1: return False
        if gcd(pow(a, (N - 1) // F, N) - 1, N) == 1: return True
    return False
def chain_ok(C):
    ok = C[0] == 2
    for i in range(len(C) - 1):
        ok &= C[i] < C[i + 1] and (C[i + 1] - 1) % C[i] == 0
    for i, p in enumerate(C):
        if p < 10**6: ok &= trial(p)
        else: ok &= pock(p, C[i - 1])
        ok &= bool(pari.isprime(p))
    return ok
def pf(n): return [int(x) for x in pari.factor(n)[0]] if n > 1 else []
@lru_cache(None)
def H(p): return 1 if p == 2 else 1 + max(H(r) for r in pf(p - 1))
@lru_cache(None)
def g(p): return 0 if p == 2 else 1 + g(max(pf(p - 1)))
allok = True
for C, k in ((C22, 22), (C23, 23), (C24, 24)):
    ok = chain_ok(C) and len(C) == k and H(C[-1]) == k and g(C[-1]) == k - 1
    print("k=%d last=%d chain/Pocklington ok, H=%d, g=%d -> %s" % (k, C[-1], H(C[-1]), g(C[-1]), ok))
    print("  multipliers:", [(C[i + 1] - 1) // C[i] for i in range(len(C) - 1)])
    allok &= ok
# A082449(n) = min{p : g(p) >= n}; g(p) <= H(p)-1 so A082449(n) >= P(n+1).  Since g(C23[-1]) = 22,
# A082449(22) <= 2957807053316399 < 11407852252734739.
allok &= g(C23[-1]) >= 22 and C23[-1] < 11407852252734739 and C24[-1] < 115504631269039577
print("A082449(22) <= %d: %s" % (C23[-1], allok))
if allok: print("CERTIFIED")

```
OEIS LOOKUP of the claim's values (automatic; a value OEIS lists is known, not a record):
- 2957807053316399: in no OEIS entry (searched 2026-10-17).
- 11407852252734739 is KNOWN to OEIS: A082449 (Let f(p) = greatest prime divisor of p-1. Sequence gives smallest prime which takes at least n steps to reach 2 when f i): mentioned in the entry, not in its data; the entry is marked 'more' (more terms wanted)
- 94649825706124769: in no OEIS entry (searched 2026-10-17).
