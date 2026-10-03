## Result
**C1 (PROVED, computer-assisted with a hand-checkable certificate).** The bounded-window constant is exactly c₁ = 6w(2312) = 1.5857431411…, where w(k) = loglog k/log k.
- (a) Unconditionally, F(n) ≥ 6w(2312) for every n outside E = {n : some n+k with 3 ≤ k ≤ 13093 is 61-smooth}. Also #E∩[0,N] = O((log N)^{18}).
- (b) Under Dickson, for every K ≥ 13093 there are infinitely many n ∉ E with max_{3≤k≤K} ω(n+k)w(k) = 6w(2312) exactly.

This repairs r1s3/C3, which had an uncertified SAT step. The cases k₀ ∈ {3,4} are now closed by a forcing chain:
- k₀ = 4 dies at p = 13, with witnesses ≤ 158.
- k₀ = 3 dies at p = 61, with witnesses ≤ 13093. The primes 13,…,59 are each forced into n+3, which overflows its cap of 17.

It also improves r1s3/C1 (6w(2314) off E) to the sharp 6w(2312).

**C2 (PROVED, NEGATIVE).** The exceptional set cannot be removed by residue information plus "one large prime per non-smooth term" (Størmer). For n_e = 2310·2^e − 2312 with ord_M(2) | e, that information yields at most 7w(30032) < 6w(2312). So "F(n) ≥ 6w(2312) for all large n" lies beyond the bounded-window + S-unit method.

## Claims
### C1
STATEMENT: Let w(k) = loglog k/log k and T = 6w(2312) = 1.58574314111350…
- (a) Let n ≥ 0 be such that none of n+3, …, n+13093 is 61-smooth (each has a prime factor > 61). Then some k ∈ [3, 13093] has ω(n+k)·w(k) ≥ T, so F(n) ≥ T.
- (b) Let E be the set of n failing the hypothesis of (a). Then #(E∩[0,N]) ≤ 13091·Ψ(N+13093, 61) = O((log N)^{18}).
- (c) Assume Dickson's prime k-tuples conjecture. For every K ≥ 13093 there are infinitely many n with max_{3≤k≤K} ω(n+k)w(k) = T and n ∉ E. So T is exactly the best constant obtainable from any bounded window, even off E.

STATUS: PROVED. Parts (a) and (c) use the finite computations in verify.py and dick.py: 50-digit Decimal arithmetic, every step re-checkable by hand.

TYPE: QUANT / SPECIAL.

BEYOND:
- r1s3/C1 had 6w(2314) off a polylog set.
- r1s3/C3 claimed 6w(2312) via an uncertified SAT call (broken).
- Here the uncertified step is replaced by an explicit forcing certificate, and the constant matches the Dickson ceiling exactly.

PROOF of (a): Suppose ω(n+k)w(k) < T for all 3 ≤ k ≤ 13093. Write c(k) = ω_{≤61}(n+k) and r_p = (−n mod p). Then p | n+k ⇔ k ≡ r_p (mod p).
- Since n+k has a prime factor > 61, ω(n+k) ≥ c(k)+1. Hence c(k) ≤ b_k := max{b : (b+1)w(k) < T}.
- Values of b_k: b_3 = 17, b_4 = 5, b_5 = 4, b_k = 3 for 6 ≤ k ≤ ~180, b_k = 4 up to 2312, and b_k = 5 on [2313, ~30000].
- b_2312 = 4, because 6w(2312) = T is not < T. All b_k were computed with 50-digit Decimal; the only exact tie T/w(k) ∈ ℤ is at k = 2312.

Step 1 (position of the 2310-multiple). Let k₀ ∈ [0, 2309] with 2310 | n+k₀.
- If k₀ ∈ [5, 2309], the term k = k₀ has c ≥ 5 > 4 ≥ b_k. Indeed b_k ≤ 4 on [5, 2312], since 6w(k) ≥ 6w(2312) there: w(5) = 0.2957 > w(2312), w rises to k = 15 and then decreases.
- If k₀ ∈ {0, 1, 2}, the term k = k₀+2310 ∈ [2310, 2312] has c ≥ 5 > b_k. Contradiction in both cases.
- So k₀ ∈ {3, 4}, i.e. r_p ≡ k₀ (mod p) for p ∈ {2, 3, 5, 7, 11}.

Step 2 (forcing chain). Call position k *full* if the counts already forced satisfy count(k) = b_k. Counts only grow as more primes are placed, so full positions stay full, and no further prime may hit a full position. If every residue class mod p except one contains a full position in [3, 13093], then r_p is forced to that class. If every class contains one, we have a contradiction.
- k₀ = 4: every class mod 13 contains a full position ≤ 158. For example k = 4 is full (count 5 = b_4). Contradiction.
- Heuristic reason: the positions 4 + 2310j (j = 0..12) are all full and cover every class mod 13, since 2310 ≡ 9 (mod 13).
- k₀ = 3: r_p = 3 is forced successively for p = 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59. The largest witnesses used are 157, 213, 1053, 423, 1053, 1095, 2033, 1823, 1599, 2313, 11313, 2733.
- After that, n+3 has c = 5 + 12 = 17 = b_3, so position 3 is full. Every class mod 61 then contains a full position ≤ 13093. Contradiction.
- verify.py lists the witnesses, recomputing counts directly as #{placed p : p | k − r_p}.

PROOF of (b): n ∈ E means one of 13091 shifts of n lands on a 61-smooth number ≤ N+13093. Ψ(x, 61) ≍ (log x)^{18}, since π(61) = 18.

PROOF of (c):
- Set-up. Let Q = ∏_{p≤K} p^{a_p} with p^{a_p} > K, and take n = −2 + Qt.
  - For 3 ≤ k ≤ K, v_p(n+k) = v_p(k−2) for all p ≤ K, so n+k = (k−2)·m_k(t) with m_k(t) = 1 + (Q/(k−2))t.
  - Each m_k ≡ 1 mod every p ≤ K.
  - The K−2 forms are admissible: for q ≤ K no form vanishes mod q, and for q > K at most K−2 < q classes are excluded.
- Under Dickson, infinitely many t make every m_k(t) a prime > K. Then ω(n+k) = ω(k−2) + 1, and no term is 61-smooth.
- Remains to show sup_{k≥3} (ω(k−2)+1)w(k) = T:
  - r = ω(k−2) ≤ 2: the value is ≤ 3·max w = 3w(15) = 1.104.
  - r ≥ 3: then k ≥ P_r + 2 ≥ 32 lies where w decreases, so the value is ≤ (r+1)w(P_r + 2). Computed for 3 ≤ r ≤ 1000, the maximum is at r = 5, which is T itself. The next values are r=6: 1.58407, r=7: 1.56790, r=4: 1.56660.
  - r > 1000: log P_r ≥ log (r+1)! ≥ (r+1)(log(r+1) − 1) =: L. The bound becomes log L/(log(r+1) − 1) = 1 + (1 + log(y−1))/(y−1) with y = log(r+1). This is decreasing in y and equals 1.470 at r = 1000.
- Combined with (a), equality holds. ∎

### C2
STATEMENT:
- Fix Z ≥ K ≥ 30032 and let M = P(Z)/2310. For e ≡ 0 (mod ord_M 2), put n_e = 2310·2^e − 2312, an infinite family.
- Then n_e ≡ −2 (mod p) for all p ≤ Z, and n_e + 2312 = 2310·2^e is Z-smooth.
- By S-unit finiteness, for large e no other term n_e+k (k ≤ K) is Z-smooth.
- Hence the "residue + one-large-prime" lower bound for n_e is max(5w(2312), max_{3≤k≤K, k≠2312} (ω(k−2)+1)w(k)) = 7w(30032) = 1.5840721 < T.
- So no argument using only the residues n mod p (p ≤ Z), Størmer/S-unit finiteness and "each non-smooth term has ≥ 1 extra prime" can prove F(n) ≥ T for all large n. The E-exemption in C1 is necessary for this method.

STATUS: PROVED.

TYPE: NEGATIVE.

BEYOND:
- The blackboard has the abstract pattern "a ≡ −2, designated smooth k* = 2312 gives 7w(30032)".
- New here: this pattern is realised by actual integers (an explicit infinite family), so the barrier is genuine. Note that the valuation-exact pattern (mod p^a) cannot be realised with a smooth term, which is why the squarefree modulus is used.
- Also new: the team-lead goal "F(n) ≥ 6w(2312) for all large n via SAT + Størmer" is unreachable as stated.

PROOF:
- Residues and smoothness. n_e + 2 = 2310(2^e − 1) and M | 2^e − 1, so P(Z) | n_e + 2. Then n_e + k ≡ k − 2 (mod p), giving ω_{≤Z}(n_e+k) = ω_{≤Z}(k−2) = ω(k−2) for 3 ≤ k ≤ K.
- Maximum away from 2312:
  - For k ≠ 2312, the value of (ω(k−2)+1)w(k) is checked numerically for k < 40000. The top values are 30032: 1.584072, 2732: 1.568459, 212: 1.566601.
  - Beyond 40000, use the r-analysis of C1(c). For r ≤ 5 the value is ≤ 6w(40000) < 1.568. For r ≥ 6 it is ≤ (r+1)w(P_r + 2) ≤ 7w(30032).
- At k = 2312 the term is smooth, so it gets no +1: 5w(2312) = 1.3214. ∎

Heuristic (not claimed): F(n_e) ≥ T for large e. The terms 2310·2^e + d, d small, are very unlikely to all be (smooth)·prime along an exponentially sparse sequence.

## Data
- chain.py (float) and verify.py (50-digit) agree:
  - k₀ = 4 contradiction at p = 13 (witnesses ≤ 158).
  - k₀ = 3 forced chain 13…59 → 3, contradiction at p = 61 (max witness 13093).
- dick.py:
  - (r+1)w(P_r+2) for r = 5, 6, 7, 4: 1.585743, 1.584072, 1.567903, 1.566601.
  - Tail bound at r = 1000: 1.470.
  - 7w(30033) = 1.5840692 (the blackboard's unconditional liminf) is below 7w(30032) = 1.5840721 (the C2 barrier). So the one-exemption constant lies in an interval of width 3·10⁻⁶.

## Dead ends
- Removing E by Størmer alone is impossible (C2).
- Using exact valuations mod p^a to forbid smooth terms fails, because the adversary is free to use a squarefree pattern.
