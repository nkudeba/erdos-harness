## Result
**C1 (PROVED, refereed by me only, not Lean-checked).** Convention: F(n) = sup_{k≥3} ω(n+k)w(k), with w(k) = loglog k/log k. This equals Lean's ⨆, because the k ≤ 2 terms are ≤ 0 and the family is bounded above.

Put L = log N, L2 = log L, L3 = log L2 and L4 = log L3. There are absolute constants K0 and N0 such that for N ≥ N0 and every integer K with K0 ≤ K ≤ L^{1/2}:

  #{n ∈ (N,2N]∩ℤ : F(n) ≤ 40·L2·loglog K/log K} ≥ N·exp(−1.6·K·L2).

- K = ⌊L2·L4/L3⌋ gives the GOAL: #{F(n) ≤ 41·L2·L4/L3} ≥ N·exp(−1.6·L2²·L4/L3).
- K = ⌊L^{1/2}⌋ gives something **stronger than the GOAL**: F(n) ≤ 80·logloglog n for at least N·exp(−1.6·L^{1/2}·L2) = N^{1−o(1)} integers n ∈ (N,2N]. Hence liminf F(n)/logloglog n ≤ 80.

This is the conjectured true order: r2s3/C2 predicts liminf F/L3 = 1/log 2. For fixed θ ≥ 80, #{n ≤ 2N : F(n) ≤ θ·L3} ≥ N·exp(−L^{40/θ+o(1)}). Together with r1s2/C1 (≤ N·exp(−L^{a}) for a < 1/(1+θ)), −log(density) = L^{Θ(1/θ)}.

Nothing here touches F(n) → ∞; every barrier on the map still stands. The plan's "method ceiling L2·L4/L3" (Secondary deliverable) is FALSE (see C2): it holds only for a common sifting limit.

## Claims
### C1
STATEMENT: Notation as in Result; ω_I(m) = #{p | m : p ∈ I}; P(x) = ∏_{p≤x} p. There are absolute K0, N0 such that for all integers N ≥ N0 and K ∈ [K0, L^{1/2}], with T := 40·L2·loglog K/log K,
 #{n ∈ ℤ∩(N,2N] : ω(n+k)·w(k) ≤ T for every k ≥ 3} ≥ N·exp(−1.6·K·L2).
Corollaries:
- (a) [GOAL] #{n∈(N,2N] : F(n) ≤ 41·L2L4/L3} ≥ N·exp(−1.6·L2²L4/L3) for large N.
- (b) #{n∈(N,2N] : F(n) ≤ 80·L3(N)} ≥ N·exp(−1.6·L^{1/2}L2). Hence F(n) ≤ 80·logloglog n for infinitely many n, and liminf F(n)/loglog n = 0.
- (c) For fixed θ ≥ 80 and large N: #{n∈(N,2N] : F(n) ≤ θL3} ≥ N·exp(−1.6·L^{40/θ}·L2).
- (d) For any threshold Θ(N) with 80L3 ≤ Θ ≤ (w(15)−ε)L2, #{n ≤ 2N : F(n) ≤ Θ} ≥ N^{1−o(1)}. By r1s1/C1 this set nevertheless has density 0.
STATUS: PROVED
TYPE: QUANT / STRUCTURE
BEYOND: KNOWN has only lower bounds for F (liminf ≥ 1.584) and almost-all normal order w(15)·L2. No upper bound for liminf F below the normal order was known, and no lower bound for any exceptional set {F < Θ}. C1 gives liminf F ≤ 80·L3, matching the conjectured order L3. It strictly beats the assignment's target L2L4/L3, and it also gives the target with the requested count.

PROOF.
**0. Elementary facts.** Each was checked numerically in check1.py and proved as stated.
- (F1) w increases on (1, e^e] and decreases on [e^e, ∞). Since d/du[log u/u] = (1−log u)/u², w(k) ≤ w(15) = 0.36788 for all integers k ≥ 3. The function x ↦ log x/loglog x increases for x ≥ e^e.
- (F2) For m ≥ 3, ω(m) ≤ max(7, 4·log m/loglog m).
  - Let r = ω(m) ≥ 8. Then m ≥ r!, so log m ≥ r·log(r/e) ≥ (r/2)·log r, because r ≥ e².
  - If r ≥ (log m)^{1/2}, then log r ≥ ½·loglog m, which gives r ≤ 4·log m/loglog m.
  - Otherwise r < (log m)^{1/2} ≤ 4·log m/loglog m, since log x ≤ 4√x for all x > 0.
  - Checked for m ≤ 2·10⁶.
- (F3) For all k ≥ 3, ω(k−2)·w(k) ≤ 4.
  - If k−2 ≤ 15, then ω(k−2) ≤ 2 (as 30 > 15) and w(k) ≤ 0.368.
  - If k−2 ≥ 16, then ω(k−2) ≤ max(7, 4·log k/loglog k) by (F2) and (F1), so the product is ≤ max(7·0.368, 4).
  - Numerically the maximum for k ≤ 2·10⁶ is 1.372.
- (F4) (Rosser–Schoenfeld 1962.) For x > 1, loglog x + B − 1/(2log²x) < Σ_{p≤x} 1/p < loglog x + B + 1/log²x, with B = 0.2615. Hence:
  - for 286 ≤ x < y, Σ_{x<p≤y} 1/p ≤ log(log y/log x) + 0.05;
  - Σ_{p≤N} 1/p ≤ L2 + 0.3.
  - Also P(x) < 4^x (Chebyshev).
- (F5) Bonferroni.
  - For an integer s ≥ 0 and t even: Σ_{l≤t} (−1)^l·C(s,l) ≥ 1_{s=0} ≥ Σ_{l≤t+1} (−1)^l·C(s,l).
  - For independent events with probabilities h_p ∈ [0,1] and t even: ∏(1−h_p) ≤ Σ_{l≤t} (−1)^l·e_l(h) ≤ ∏(1−h_p) + e_{t+1}(h).
  - e_l(h) ≤ H^l/l! ≤ (eH/l)^l, where H = Σ h_p.
- (F6) Product lemma: if 0 ≤ A_j ≤ U_j and A_j ≥ U_j − D_j, then ∏A_j ≥ ∏U_j − Σ_j D_j·∏_{i≠j} U_i.
  - Proof: telescope ∏U − ∏A = Σ_j (U_j − A_j)·∏_{i<j} A_i·∏_{i>j} U_i, and use ∏_{i<j} A_i ≤ ∏_{i<j} U_i.
  - Checked on 20000 random instances.

**1. Parameters.** Constants: B′ = 200 and i₀ = 10. Put M = P(2K) and impose n ≡ −2 (mod M).
- Prime ranges: for i ≥ i₀, I_i = {p prime : p > 2K, L/2^{i+1} < log p ≤ L/2^i}. There are at most log₂L nonempty ranges.
- For 3 ≤ k ≤ K, let i(k) = min{i ≥ i₀ : 2^i ≥ B′·i²·k}, and z_k = exp(L/2^{i(k)}).
- Term k is *sieved at* range i iff i ≥ i(k). So term k is sieved by every prime in (2K, z_k]. Let K_i = {3 ≤ k ≤ K : i(k) ≤ i}.
  - Since 2^x/x² increases for x ≥ 3, |K_i| ≤ min(K, 2^i/(B′i²)).
  - Since K ≤ L^{1/2}, we get 2^{i(K)} < 2B′·(log₂L)²·L^{1/2} < L/log 2K, so z_k > 2K for every k.
- For p ∈ I_i put h_p = |K_i|/p ≤ K/p < ½, and H_i = Σ_{p∈I_i} h_p ≤ 0.75·|K_i| by (F4).
- Let t_i be the even integer with (e²+2)·H_i + i + 3 ≤ t_i + 1 ≤ (e²+2)·H_i + i + 5.
- For n, p ∈ I_i put x_p(n) = 1 if p | n+k for some k ∈ K_i, and x_p(n) = 0 otherwise. Such a k is unique, since p > K.
- S = {n ∈ (N,2N] : n ≡ −2 (M), x_p(n) = 0 for all p ∈ ∪I_i}.
- π_i = ∏_{p∈I_i} (1−h_p) ≥ exp(−1.5·H_i), using log(1−h) ≥ −h − h² ≥ −1.5h for h ≤ ½.

**2. Sieve lemma.** Let d be squarefree with all prime factors > 2K, and let a ∈ ℤ. Define S_d(a) by the same conditions as S, except that n ≡ a (mod d) is added and the conditions x_p = 0 are imposed only for p ∤ d. Then
 |S| ≥ 0.99·(N/M)·∏π_i − E   and   |S_d(a)| ≤ 1.01·(N/(Md))·∏π_i·∏_{p|d, p∈∪I_i} (1 + 2h_p) + E,
where E ≤ N^{0.04}.

Proof.
- Put A_i(n) = ∏_{p∈I_i} (1−x_p(n)), U_i = Σ_{l≤t_i} (−1)^l·e_l(x^{(i)}(n)) and D_i = e_{t_i+1}(x^{(i)}(n)), where x^{(i)} = (x_p)_{p∈I_i}. By (F5), 0 ≤ A_i ≤ U_i and A_i ≥ U_i − D_i.
- Upper bound: 1_{S_d(a)} ≤ ∏_i U_i^{(d)}, where the superscript (d) drops the primes p | d.
- Lower bound: by (F6), 1_S ≥ ∏U_i − Σ_i D_i·∏_{j≠i} U_j.
- Expanding: for squarefree e with prime factors in ∪I_i, p ∤ d, ∏_{p|e} x_p(n) = Σ_κ 1[n ≡ −κ(p) (mod p) for all p | e], where κ runs over the maps assigning to each p | e an element of K_{i(p)}.
- By CRT (M, d, e are pairwise coprime), each class has N/(Mde) + θ elements, |θ| ≤ 1. So the main terms are (N/(Md))·∏_i u_i^{(d)} and (N/M)·[∏u_i − Σ_i δ_i·∏_{j≠i} u_j]. Here u_i = Σ_{l≤t_i} (−1)^l·e_l(h^{(i)}) and δ_i = e_{t_i+1}(h^{(i)}).
- By (F5), π_i ≤ u_i ≤ π_i + δ_i, and δ_i ≤ (eH_i/(t_i+1))^{t_i+1} ≤ e^{−(t_i+1)} ≤ exp(−2H_i − i − 3) ≤ π_i·e^{−i−3}. The same holds with (d), because H_i^{(d)} ≤ H_i and π_i^{(d)} ≥ π_i.
- Since Σ_{i≥10} e^{−i−3} < 0.01, both main-term claims follow. Note π_i^{(d)} = π_i·∏_{p|d, p∈I_i} (1−h_p)^{−1}, and (1−h)^{−1} ≤ 1+2h for h ≤ ½.
- Error: E ≤ (1 + log₂L)·∏_i (2K·|I_i|)^{t_i+1}, with |I_i| ≤ e^{L/2^i}. So log E ≤ Σ_i (t_i+1)·L/2^i + Σ_i (t_i+1)·log 2K + O(L3).
  - First sum: ≤ L·[7.05/B′·Σ_{i≥10} i^{−2} + Σ_{i≥10} (i+5)·2^{−i}] = 0.035·L (computed).
  - Second sum: Σ_i (t_i+1) ≤ 9.4·Σ H_i + O(L2²), and Σ H_i ≤ K·Σ_{2K<p≤N} 1/p ≤ K(L2+0.3). So the second sum is ≤ 11·K·L2² = o(L), as K ≤ L^{1/2}. ∎

Consequently |S| ≥ 0.99·N·exp(−1.5K(L2+0.3) − 2.78K) − E ≥ N·exp(−1.55·K·L2), using M < 4^{2K}.

**3. Thresholds.** For k ≥ 3 put R_k = ⌊(T−4)/(5.1·w(k))⌋ and log y_k = L/(4R_k). Then:
- (i) any product d of R_k distinct primes ≤ y_k satisfies d ≤ N^{1/4}, and there are at most N^{1/4} such d;
- (ii) for m ≤ 3N, ω_{>y_k}(m) < log(3N)/log y_k ≤ 4R_k(1 + 1.1/L).
Also, for n ≡ −2 (mod M) and p ≤ 2K, p | n+k ⟺ p | k−2. So ω_{≤2K}(n+k) ≤ ω(k−2) ≤ 4/w(k) by (F3).

**4. Window terms, 3 ≤ k ≤ K.**
- Bad set: B_k = {n ∈ S : ω_{(z_k, y_k]}(n+k) ≥ R_k}, which is empty if y_k ≤ z_k.
- Good n are fine: for n ∈ S \ B_k, primes in (2K, z_k] do not divide n+k. So ω(n+k) < ω(k−2) + R_k + 4R_k(1+1.1/L) ≤ ω(k−2) + 5.1·R_k, and ω(n+k)·w(k) ≤ 4 + (T−4) = T.
- Counting: every n ∈ B_k lies in S_d(−k) for some product d of R_k primes in (z_k, y_k]. By the lemma, with X_k = (e·μ_k/R_k)^{R_k} and μ_k = Σ_{z_k<p≤y_k} (1+2h_p)/p,
  |B_k| ≤ 1.01·(N/M)·∏π_i·μ_k^{R_k}/R_k! + N^{1/4}·E ≤ 1.03·(|S|+E)·X_k + N^{0.29}.
- Bounding μ_k: Σ_{p>2K} 2h_p/p ≤ 2K·Σ_{m>2K} 1/(m(m−1)) = 1. Then (F4) gives μ_k ≤ log(L/log z_k) + 1.05 = i(k)·log 2 + 1.05.
  - If i(k) > i₀, minimality gives 2^{i(k)−1} < B′·i(k)²·k, so i(k)·log 2 < 5.99 + 2·log i(k) + log k. With i(k) ≤ 3log₂k + 30 (checked) this gives μ_k ≤ log k + 2·log(4.33·log k + 30) + 7.04. If i(k) = i₀, then μ_k ≤ 8.
- (W) Claim: R_k ≥ e²·μ_k and R_k ≥ 3·log k + 2. This yields X_k ≤ e^{−R_k} ≤ e^{−2}·k^{−3}.
  - Since log K ≤ L2/2, T ≥ 80·loglog K. Take K0 with loglog K0 ≥ 5.87, so T ≥ 469.
  - For 16 ≤ k ≤ K: 1/w(k) = log k/loglog k ≥ log k/loglog K, so R_k ≥ ((80·loglog K − 4)/(5.1·loglog K))·log k − 1 ≥ 15.5·log k − 1.
  - If log k ≥ 17: f(x) = 15.5x − 1 − 7.39·(x + 2·log(4.33x+30) + 7.04) satisfies f(17) = 262.5 − 246.2 > 0, and f′(x) ≥ 8.11 − 14.78·4.33/(4.33x+30) > 0.
  - If log k < 17, or k < 16: 1/w(k) ≥ e (the minimum of x/log x), so R_k ≥ (e/5.1)·(T−4) − 1 ≥ 246.8 ≥ 7.39·33.4 ≥ e²·μ_k. (For x < 17 the bound on μ_k is ≤ 33.33.)
  - The second inequality is clear in both cases.

**5. Middle terms, K < k ≤ N^{1/4}.**
- Bad set: B_k = {n ∈ S : ω(n+k)·w(k) > T}.
- Reduction: if n ∈ B_k, then ω_{>2K}(n+k) > (T−4)/w(k) ≥ 5.1·R_k by step 3.
  - If y_k ≤ 2K this contradicts (ii), so B_k = ∅.
  - Otherwise ω_{(2K, y_k]}(n+k) ≥ R_k, so n ∈ S_d(−k) for some product d of R_k primes in (2K, y_k].
- Counting: as in step 4, |B_k| ≤ 1.03·(|S|+E)·X_k + N^{0.29}, with X_k = (e(L2+1.3)/R_k)^{R_k}. This uses Σ_{p≤N} 1/p ≤ L2 + 0.3.
- Put ρ = R_k/(e(L2+1.3)) and s = log k. Note R_k increases with k.
- (O1) ρ ≥ e. At k = K+1, (T−4)/w(K) ≥ 40·L2 − 4·log K/loglog K ≥ 39.65·L2. Then R ≥ 7.77·L2 − 1 ≥ e²(L2+1.3) for L2 ≥ 28.
- (O2) R_k·log ρ ≥ 3s + 2.
  - If s ≤ (log K)^4: log s ≤ 4·loglog K, so R_k ≥ 3.9s − 1 ≥ 3s + 2.
  - If s > (log K)^4: ρ ≥ 2.7·(loglog K/log K)·s/log s − 0.02 ≥ s^{1/2}. So R_k·log ρ ≥ (T−4)·s/10.2 − log s ≥ 3s + 2.
- Hence X_k ≤ e^{−2}·k^{−3}.

**6. Far terms, k > N^{1/4}.** No sieve is needed. Here m = n+k ≥ N.
- If k ≤ N: m ≤ 3N. By (F2) and (F1), ω(m)·w(k) ≤ 4·(log 3N/loglog 3N)·w(N^{1/4}) ≤ 16·1.01 < 17.
- If k > N: m < 3k, and ω(m)·w(k) ≤ 4·(log 3k/loglog 3k)·(loglog k/log k) ≤ 4(1 + 1.1/log k) < 5.
- Both are < T.

**7. Assembly.**
- Σ_{k≥3} X_k ≤ e^{−2}·Σ_{k≥3} k^{−3} < 0.011.
- The error terms total ≤ N^{1/4}·N^{0.29} + 1.03·E = O(N^{0.6}), which is ≤ 0.01·|S| since |S| ≥ N^{0.9}.
- So G = S \ ∪_k B_k has |G| ≥ 0.97·|S| − 0.01·|S| ≥ N·exp(−1.6·K·L2).
- Every n ∈ G has ω(n+k)·w(k) ≤ T for all k ≥ 3.
- All steps need only N ≥ N0 (absolute) and K ≥ K0. ∎

Corollaries.
- (a) K = ⌊L2L4/L3⌋. Here log K ≥ L3 − L4 − o(1) and loglog K ≤ L4, so T ≤ 40·L2L4/(L3−L4−o(1)) ≤ 41·L2L4/L3.
- (b) K = ⌊L^{1/2}⌋. Here T ≤ 40·L2·(L3 − log 2)/(L2/2 − 0.01) ≤ 80·L3(N) ≤ 80·L3(n) for n > N.
- (c) K = ⌊L^{40/θ}⌋ (so K ≤ L^{1/2}). Then T ≤ θ·(L3 + log(40/θ))·(1+o(1/L2)) ≤ θ·L3.
- (d) follows from (b) and r1s1/C1.

### C2 (NEGATIVE: the plan's "method ceiling" is false)
STATEMENT: The Secondary deliverable says that sieving a window of shifts at level ≤ N cannot certify F(n) = o(L2L4/L3). As a statement about window-sieve constructions, this is false. The construction of C1 is exactly a window sieve at level N^{0.04+o(1)}, with term-dependent sifting limits and per-range Brun truncations, and it certifies F(n) ≤ 80·L3 on N^{1−o(1)} values. The ceiling L2L4/L3 holds only under a common sifting limit log z ≍ L/K: then a window term may carry ≍K primes > z, which forces T ≳ K·w(15) and hence T ≳ L2L4/L3.
STATUS: PROVED (it is C1)
TYPE: NEGATIVE
MECHANISM:
- The top window terms need only that their number of primes above z_k stays ≲ T/w(k). This is an upper-tail event with mean log(L/log z_k) ≈ log k + 2·loglog k.
- With per-range truncations, the level costs Σ_i |K_i|·L/2^i ≈ L·Σ 1/(B′i²) and stays bounded.
- What is left: the constant (80 vs the conjectured 1/log 2), and of course F → ∞.

## Data
- check1.py results:
  - product-Bonferroni (F6): 0 violations in 20000 trials;
  - independent Bonferroni (F5): 0 violations in 3000 trials;
  - (F2): 0 violations for m ≤ 2·10⁶;
  - argmax w = 15, w(15) = 0.3678768;
  - max ω(k−2)·w(k) = 1.372 for k ≤ 2·10⁶;
  - max(i(k) − 3log₂k) = 13.2 < 30;
  - level coefficient 0.03496;
  - The W1 check in the script used constant 6.04, a slip; the notebook proof now uses the correct 7.04 and threshold x ≥ 17, checked by hand: f(17) > 0 and f′ > 0.
- check2.py results:
  - f(17) = 16.26, and f is increasing on [17, 10⁵];
  - e²·μ-bound at x = 17 is 246.21 ≤ (e/5.1)·465 − 1 = 246.84;
  - coefficient 15.55;
  - O1 margin > 0 for L2 ≥ 28;
  - O2 coefficients 3.89 and 2.73.
- Audit (2nd pass) of every step:
  - steps 3–7 use m = n+k ≤ 3N only for k ≤ N^{1/4};
  - k > N is covered in step 6;
  - all class counts are over the N consecutive integers in (N,2N];
  - K_i = ∅ for i < i(3) = 18;
  - all sifted primes are > 2K ≥ 286, so (F4) applies.

## Dead ends
- The plan's common sifting limit log z = L/(cK) caps the method at L2·L4/L3. Pure Brun with one truncation even loses a factor L2, since log z ≈ L/(K·L2). Both are fixed by giving each term its own limit and each prime range its own truncation, plus an upper-tail count for the large primes.
- The constant 40 (hence 80·L3) is not optimised. The losses are the factor 5.1 from level N^{1/4} for d and the e² margins.
