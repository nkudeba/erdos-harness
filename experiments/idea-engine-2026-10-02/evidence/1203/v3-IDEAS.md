# Research engine: problem 1203, run 20261002-190542-547817-erdos1203

Spend $32.2873; 22 claim(s); 1 validated as new. Validated means a step referee and an adversary found no error and a novelty judge called it new. It is informal: nothing here is Lean-checked or human-reviewed.

## [validated-new] deep/C1 PROVED QUANT
**Statement.** Notation as in Result; ω_I(m) = #{p | m : p ∈ I}; P(x) = ∏_{p≤x} p. There are absolute K0, N0 such that for all integers N ≥ N0 and K ∈ [K0, L^{1/2}], with T := 40·L2·loglog K/log K,
 #{n ∈ ℤ∩(N,2N] : ω(n+k)·w(k) ≤ T for every k ≥ 3} ≥ N·exp(−1.6·K·L2).
Corollaries:
- (a) [GOAL] #{n∈(N,2N] : F(n) ≤ 41·L2L4/L3} ≥ N·exp(−1.6·L2²L4/L3) for large N.
- (b) #{n∈(N,2N] : F(n) ≤ 80·L3(N)} ≥ N·exp(−1.6·L^{1/2}L2). Hence F(n) ≤ 80·logloglog n for infinitely many n, and liminf F(n)/loglog n = 0.
- (c) For fixed θ ≥ 80 and large N: #{n∈(N,2N] : F(n) ≤ θL3} ≥ N·exp(−1.6·L^{40/θ}·L2).
- (d) For any threshold Θ(N) with 80L3 ≤ Θ ≤ (w(15)−ε)L2, #{n ≤ 2N : F(n) ≤ Θ} ≥ N^{1−o(1)}. By r1s1/C1 this set nevertheless has density 0.
**Beyond.** KNOWN has only lower bounds for F (liminf ≥ 1.584) and almost-all normal order w(15)·L2. No upper bound for liminf F below the normal order was known, and no lower bound for any exceptional set {F < Θ}. C1 gives liminf F ≤ 80·L3, matching the conjectured order L3. It strictly beats the assignment's target L2L4/L3, and it also gives the target with the requested count.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "new", "significance": 1, "cite": null, "why": "No published upper bound on liminf F below the trivial ~(1/e)loglog n is known to me; the CRT-plus-counting construction giving F(n) ≤ 80·L3 infinitely often (with explicit counts) is a nice complement but is the opposite direction from the problem and does not advance proving F(n)→∞.", "panel": [{"verdict": "new", "cite": null, "significance": 1, "why": "No published upper bound on liminf F below the trivial ~(1/e)loglog n is known to me; the CRT-plus-counting construction giving F(n) ≤ 80·L3 infinitely often (with explicit counts) is a nice complement but is the opposite direction from the problem and does not advance proving F(n)→∞."}, {"verdict": "new", "cite": null, "significance": 2, "why": "No published upper bound on limin`
**Proof or evidence.**

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

## [valid-routine] r1s1/C2 PROVED QUANT
**Statement.** Fix ε∈(0,w(15)) and let S_ε={k≥3 : w(k)>ε}. This set is finite and nonempty, and it contains 15.
Put A(ε)=Σ_{k∈S_ε}Q(ε/w(k)). Then #{n≤N : F(n) < ε loglog N} ≤ N (log N)^{-A(ε)} (loglog N)^{O_ε(1)}.
In particular the same bound holds for #{n≤N : F(n)<ε loglog n}.
**Beyond.** KNOWN gives F≥(1/e-ε)L2 off a set O(N(log N)^{-c(ε)}) using one shift, which yields exponent Q(ε/w(15)).
C2 sums the large-deviation exponents over all shifts with w(k)>ε. It also covers the regime L3 ≪ F ≪ L2, which the window-total theorem (fixed C or C=θL3) does not reach.
Values: A(0.3)=1.29 (|S|=374), A(0.25)=21.28 (|S|=5499), A(0.2)=821.0 (|S|=332102). Single-shift values: 0.018, 0.058, 0.125.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 1, "cite": "Rankin's trick + Nair–Tenenbaum/Henriot (or Brun sieve) bounds for sub-multiplicative functions of finitely many shifts; Halberstam/Kubilius joint independence of ω(n+k)", "why": "The bound is the joint lower-tail large deviation for ω at a fixed finite set of shifts; Rankin's method with standard multi-shift moment bounds gives exactly the summed exponent Σ Q(ε/w(k)). It sharpens an almost-all exceptional-set exponent but does not touch the zero-exceptions core of the problem.", "panel": [{"verdict": "routine", "cite": "Rankin's trick + Nair–Tenenbaum/Henriot (or Brun sieve) bounds for sub-multiplicative functions of finitely many shifts; Halberstam/Kubilius joint independence of ω(n+k)", "significance": 1, "why": "The bound is the joint `
**Proof or evidence.**

Let u_k=ε/w(k)∈(0,1) for k∈S, so K:=max S, and apply Lemma U with y_k=u_k.
If F(n)<εL2 then for each k∈S, ω(n+k)w(k) ≤ F(n) < εL2, so ω(n+k) < u_kL2. (F(n) ≥ ω(n+k)w(k), since the family is bounded above by maximal order.)
Hence 1 ≤ ∏_k u_k^{ω(n+k)-u_kL2}, and the count is ≤ exp(L2Σu_k log(1/u_k))·Σ_n∏u_k^{ω(n+k)}.
Choose t = the even integer in [e²Y L2+1, e²Y L2+3], and log z = log N/(4t).
Then (1+Yπ(z))^t ≤ ((1+Y)z)^t = (1+Y)^t N^{1/4} = N^{1/4+o(1)}.
Also λ ≤ loglog z ≤ L2 for large N, so t+1 ≥ e²Yλ.
Mertens gives λ = loglog z - loglog K + O(1) = L2 - L3 - O_ε(1).
So count ≤ 2N exp(-L2Σ_k[(1-u_k) - u_k log(1/u_k)] + Y(L3+O_ε(1))) + e^{O(L2)}N^{1/4+o(1)} = N(log N)^{-A(ε)}(L2)^{O_ε(1)}.
The last form uses (1-u)+u log u = Q(u). ∎
CONJECTURE (sharpness): the true count is N(log N)^{-A(ε)+o(1)}.
Mechanism: under the independence heuristic, the shifts with w(k)≤ε are almost surely harmless. A k with u_k≥1+δ costs (log N)^{-Q(u_k)}, and Σ_k over all k≤N is o(1). This is not proved: a lower bound needs a joint lower-bound sieve.

## [valid-routine] r1s1/C1 PROVED STRUCTURE
**Statement.** For each ε>0, #{n≤N : |F(n) - w(15)·loglog N| > ε loglog N} = O_ε(N/loglog N). Hence F(n) ~ w(15) loglog n for almost all n.
**Beyond.** KNOWN has only the lower bound F ≥ (w(15)-ε)L2 a.e. (one shift). C1 adds the upper bound, giving the exact normal order.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 1, "cite": "Hardy–Ramanujan (1917) uniform bound for #{m≤x: ω(m)=r}; Sathe–Selberg / Erdős–Nicolas large-deviation bounds for ω", "why": "Lower bound is the one-shift normal-order argument; the upper bound is a union bound over k of Hardy–Ramanujan tails (log N)^{-Q(λ_k)} with λ_k=(1/e+ε)/w(k)>1, which sums to O(N(log N)^{-c(ε)}), stronger than claimed. It is an almost-all statement and does not touch the exceptional n that the problem is about.", "panel": [{"verdict": "routine", "cite": "Hardy–Ramanujan (1917) uniform bound for #{m≤x: ω(m)=r}; Sathe–Selberg / Erdős–Nicolas large-deviation bounds for ω", "significance": 1, "why": "Lower bound is the one-shift normal-order argument; the upper bound is a union bound over k of Hardy–Ramanujan tails (log `
**Proof or evidence.**

Lower bound: Turán gives Σ_{m≤2N}(ω(m)-L2)² ≪ N L2, so ω(n+15) ≥ (1-ε')L2 except for O(N/(ε'²L2)) values n.
Upper bound: set T=(w(15)+ε)L2 and fix K0 (depending only on ε) as below.
(i) k≤2: w(k)≤0 in the Lean convention, so these k are harmless.
(ii) 3≤k≤K0: w(k)≤w(15). Turán applied to K0 shifts gives ω(n+k) ≤ (1+ε/w(15))L2 for all such k, except for O_ε(N/L2) values n.
(iii) k≥N: m=n+k≤2k. Robin's bound ω(m) ≤ 1.3841 log m/loglog m (m≥3) and monotonicity of log x/loglog x for x≥e^e give ω(m)w(k) ≤ 1.3841(1+log2/log k) < 2 < T.
(iv) K0<k<N: Rankin. Σ_{m≤x}z^{ω(m)} ≤ x∏_{p≤x}(1+(z-1)/p), so #{m≤x: ω(m)≥v} ≤ x exp((z-1)ℓ - v log z) with ℓ = loglog x+1 (x≥3; Rosser–Schoenfeld gives Σ_{p≤x}1/p ≤ loglog x+1).
With z=v/ℓ this is ≤ x exp(-v(log(v/ℓ)-1)). Take x=2N, v_k=T/w(k) ≥ w(15)L2 log k/loglog k, and ℓ ≤ L2+2, so v_k/ℓ ≥ (w(15)/2) log k/loglog k.
Choose K0 so that log(0.18 log k/loglog k)-1 ≥ ½ loglog k for k≥K0. Then v_k(log(v_k/ℓ)-1) ≥ (w(15)/2)L2 log k ≥ (L2/6)log k.
So Σ_{K0<k<N} #{n≤N: ω(n+k) ≥ v_k} ≤ 2N Σ_{k>K0} k^{-L2/6} = o(N/L2).
Off the exceptional sets, ω(n+k)w(k) ≤ T for every k, so F(n) ≤ T. ∎

## [valid-routine] r1s2/C1 PROVED QUANT
**Statement.** Notation: L = log N, L2 = log L, L3 = log L2, w(k) = loglog k / log k. Fix ε ∈ (0,1) and c ∈ (0,1). Put J = ⌊L^{1−ε}⌋. For N ≥ N₀(ε, c), every n ≤ N outside a set of size ≤ N·exp(−L^{1−ε}) satisfies:
- (A) some k with J/2 < k ≤ J has ω(n+k) ≥ c·ε·L2;
- (B) F(n) ≥ c·(ε/(1−ε))·L3.

Corollary: for every θ > 0 and every a ∈ (0, 1/(1+θ)), #{n ≤ N : F(n) < θ·L3} ≤ N·exp(−(log N)^a) for N ≥ N₀(θ, a).
**Beyond.** KNOWN (b) gives exponent 1−θ′ for θ < θ′ < 1. C1 gives any exponent a < 1/(1+θ), which is strictly larger since (1+θ)(1−θ) < 1. C1 also covers every θ ≥ 1, where KNOWN gives nothing.
- The gain is bookkeeping: the witness k lies at scale log k = (1−ε)·L2, not L2, so w(k) ≈ L3/((1−ε)·L2).
- Using a pure lower-tail factorial-moment (Bonferroni) bound on the window total, with no Rankin upper-tail weights, lets the mean per term be ε·L2. That is the full level allowed.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 1, "cite": null, "why": "An almost-all exceptional-set bound from a standard Brun/Bonferroni lower-tail moment bound on the window total of small-prime counts (level log z ≈ L^ε/L2, so mean εL2 per term), plus reading w(k) off at scale log k=(1−ε)L2; it optimizes the known Rankin–Brun bound and does not touch the every-n core.", "panel": [{"verdict": "routine", "cite": null, "significance": 1, "why": "An almost-all exceptional-set bound from a standard Brun/Bonferroni lower-tail moment bound on the window total of small-prime counts (level log z ≈ L^ε/L2, so mean εL2 per term), plus reading w(k) off at scale log k=(1−ε)L2; it optimizes the known Rankin–Brun bound and does not touch the every-n core."}, {"verdict": "new", "cite": null, "significance": `
**Proof or evidence.**

Parameters. Let W = {k ∈ ℤ : J/2 < k ≤ J}, so J/2 ≤ |W| ≤ J/2 + 1. Choose log z = L^ε/(100·L2). Let P be the set of primes in (J, z]; note z > J for large N. Put λ = Σ_{p∈P} 1/p and μ = |W|·λ.
- By Mertens, λ = loglog z − loglog J + o(1) = ε·L2 − 2·L3 + O_ε(1), using loglog z = ε·L2 − L3 − log 100 and loglog J = L3 + log(1−ε) + o(1).
- Hence (ε/3)·L^{1−ε}·L2 ≤ μ ≤ L^{1−ε}·L2 for large N.

Step 1 (one prime per window). Let S(n) = Σ_{k∈W} ω_P(n+k).
- Two elements of W differ by less than J/2 < p for every p ∈ P. So each p ∈ P divides at most one n+k with k ∈ W.
- Hence S(n) = #{p ∈ P : p | Δ(n)}, where Δ(n) = ∏_{k∈W}(n+k).
- The condition p | Δ(n) says n mod p lies in a set of exactly |W| residues; the −k are distinct mod p because |W| < p.

Step 2 (factorial moments). Let T ⊂ P with |T| = j and d = ∏T.
- By CRT, d | Δ(n) holds exactly for n in |W|^j residue classes mod d. Each class has N/d + θ members in [1, N], with |θ| < 1.
- Summing over T: Σ_{n≤N} C(S(n), j) = N·e_j(q) + θ′·|W|^j·C(|P|, j), with |θ′| ≤ 1. Here q_p = |W|/p ∈ (0,1) and e_j is the j-th elementary symmetric function.

Step 3 (Bonferroni). Let R_M(S,u) = Σ_{j≤M} (−1)^j·C(S,j)·u^j − (1−u)^S, for integers S ≥ 0 and u ∈ [0,1].
- R_0 = 1 − (1−u)^S ≥ 0.
- R_M(S,0) = 0, and ∂_u R_M(S,u) = −S·R_{M−1}(S−1,u). To see this, use j·C(S,j) = S·C(S−1,j−1).
- By induction, sign R_M = (−1)^M on [0,1].
- So for even M: (1−u)^S ≤ Σ_{j≤M} (−u)^j·C(S,j). This was checked exactly for S < 40, M < 40 and u ∈ (1/20)ℤ.

Combining with Step 2, for even M:
Σ_n (1−u)^{S(n)} ≤ N·Σ_{j≤M} (−u)^j·e_j(q) + Σ_{j≤M} (|W|·|P|)^j.

The two pieces are bounded as follows.
- Main sum: Σ_{j≤M} (−u)^j·e_j(q) = ∏_p (1 − u·q_p) − Σ_{j>M} (−u)^j·e_j(q) ≤ e^{−uμ} + Σ_{j>M} μ^j/j!, using e_j ≤ μ^j/j!.
- Tail: if M ≥ e²μ, then μ^j/j! ≤ (eμ/j)^j ≤ e^{−j}, so the tail is ≤ e^{−M}.
- Error sum: Σ_{j≤M} (|W|·|P|)^j ≤ 2·(J·z)^M.

Take M to be the least even integer ≥ e²μ.

Step 4 (lower tail). Take u = 1−c. If S(n) ≤ cμ, then (1−u)^{S(n)} ≥ c^{cμ}. So
#{n ≤ N : S(n) ≤ cμ} ≤ c^{−cμ}·[N·e^{−(1−c)μ} + N·e^{−M} + 2·(Jz)^M].
Bound the three terms separately.
- First term: c^{−cμ}·e^{−(1−c)μ} = e^{−μ·h(c)}, where h(c) = 1 − c + c·log c ∈ (0,1].
- Second term: c^{−cμ}·e^{−M} ≤ e^{μ/e − e²μ} ≤ e^{−μ}.
- Third term: M·log(Jz) ≤ (e²·L^{1−ε}·L2 + 2)·(L^ε/(100·L2) + L2) = (e²/100)·L + O(L^{1−ε}·L2²) ≤ L/10. Also c^{−cμ} ≤ e^{μ/e} = N^{o(1)}. So the third term is ≤ N^{1/5}.

Total: ≤ 2N·e^{−h(c)·(ε/3)·L^{1−ε}·L2} + N^{1/5} ≤ N·exp(−L^{1−ε}) for large N.

Step 5 (conclusion). If S(n) > cμ = c·|W|·λ, then some k ∈ W has ω(n+k) ≥ ω_P(n+k) > c·λ = c·(ε·L2 − 2·L3 − O(1)).
- For (A), run the argument with c replaced by some c′ ∈ (c,1). For large N, c′·λ ≥ c·ε·L2, which gives (A).
- Since 16 ≤ J/2 < k ≤ J and w is decreasing on [e^e, ∞), w(k) ≥ w(J). Here log J ≤ (1−ε)·L2 and loglog J ≥ L3 + log(1−ε) − o(1).
- So ω(n+k)·w(k) ≥ c·(ε/(1−ε))·L3·(1 − o(1)). Replacing c by a slightly larger c′ < 1 absorbs the o(1) and gives (B).
- F(n) is a sup over a family that is bounded above, so F(n) ≥ ω(n+k)·w(k), also for Lean's ⨆.

Corollary: put ε = 1 − a. Then ε/(1−ε) = (1−a)/a > θ ⟺ a < 1/(1+θ). Pick c < 1 with c·(1−a)/a > θ. ∎

## [valid-routine] r1s3/C1 PROVED QUANT
**Statement.** Let E = {n ∈ ℕ : ∃ k ∈ {0,…,2314} with 2310 | n+k and n+k 11-smooth}. Then:
- For every n ∉ E there is k ∈ [5, 2314] with ω(n+k)·w(k) ≥ 6·w(2314) = 1.585652…, so F(n) ≥ 6·w(2314).
- #(E ∩ [0, N]) ≤ 2315·Ψ(N+2314, 11) ≤ 2315·∏_{p ≤ 11}(1 + log(N+2314)/log p) = O((log N)^5).
**Beyond.** KNOWN has liminf F ≥ 7w(30033) = 1.58407 for all large n, and the Dickson bounded-window ceiling 6w(2312) = 1.585743. C1 gives 1.585653 for all n, with no "n large" needed and nothing ineffective, outside a polylog-thin set. It also shows that the bounded-window gap [7w(30033), 6w(2312)] is caused only by the thin set E.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 0, "cite": null, "why": "Immediate from Erdős's CRT/primorial argument: in [5,2314] one term is divisible by 2310, and if that term is not 11-smooth it has a sixth prime factor; the exceptional set is bounded by the trivial smooth-number count. The numerical gain (≈0.0016, still below the bounded-window ceiling, with an infinite exceptional set) does not touch the problem's core.", "panel": [{"verdict": "routine", "cite": null, "significance": 0, "why": "Immediate from Erdős's CRT/primorial argument: in [5,2314] one term is divisible by 2310, and if that term is not 11-smooth it has a sixth prime factor; the exceptional set is bounded by the trivial smooth-number count. The numerical gain (≈0.0016, still below the bounded-window ceiling, with an infin`
**Proof or evidence.**

1. Let k0 ∈ {0,…,2309} be the residue with n + k0 ≡ 0 (mod 2310).
2. Choose k as follows. If 5 ≤ k0 ≤ 2309, put k = k0. If k0 ∈ {0,1,2,3,4}, put k = k0 + 2310 ∈ [2310, 2314]. In both cases k ∈ [5, 2314] and 2310 | n+k. Also n + k ≥ 5 > 0.
3. Since n ∉ E, the number n+k is not 11-smooth. So it has a prime factor ≥ 13, in addition to 2, 3, 5, 7, 11. Hence ω(n+k) ≥ 6.
4. Now bound w(k) from below, using unimodality:
   - On [5, 15], w ≥ w(5) = 0.29568.
   - On [16, 2314], w ≥ w(2314) = 0.264275.
   - So w(k) ≥ w(2314) > 0, and ω(n+k)·w(k) ≥ 6w(2314).
   - The script also checks "min over k0 of max{w(k): k ≡ k0, 0 ≤ k ≤ 2314} = w(2314), attained at k0 = 4".
5. The family k ↦ ω(n+k)w(k) is bounded above (blackboard routine fact, via ω(m) ≪ log m/loglog m). So the real (and Lean) supremum F(n) is ≥ this value.
6. Counting E: each n ∈ E equals s − k with s an 11-smooth number ≤ N + 2314 and 0 ≤ k ≤ 2314. Ψ(x, 11) ≤ ∏_{p≤11}(1 + log x/log p).

Numerics (s1.py): 6w(2312) = 1.585743141, 6w(2313) = 1.585697859, 6w(2314) = 1.585652599, 7w(30033) = 1.584069153. Counts of 11-smooth multiples of 2310 up to N:

| N | count |
|---|---|
| 10⁶ | 125 |
| 10⁹ | 1900 |
| 10¹² | 10808 |
| 10¹⁸ | 108246 |
| 10³⁰ | 1712985 |

## [valid-routine] r1s4/C1 PROVED NEGATIVE
**Statement.** Fix A > 1. Put K = ⌊(log N)^A⌋, y = N^{1/6}, D = y² = N^{1/3}, P = ∏_{K<p≤y} p and Δ_K(n) = ∏_{k=1}^{K}(n+k). Let λ_d be Selberg's optimal weights (λ₁ = 1, supported on d | P, d ≤ y). Then f(n) = (Σ_{d | (Δ_K(n),P)} λ_d)² is a majorant of 1_{S₀}, where S₀ = {n : (Δ_K(n), P) = 1}. It uses only divisors d | Δ_K(n) with d ≤ D, and K ≥ e·log D for large N. Its mass satisfies Σ_{n≤N} f(n) ≤ N^{1−(A−1)/(6A)+o(1)}.
In particular, the T10 claim "K ≥ e·log D ⇒ every Λ² majorant has mass ≥ N^{1−o(1)}" is false for r = 0.
**Beyond.** KNOWN's level/dimension barrier states "Λ² bounds become trivial once K > e·log D". That holds for the dense-prime model G ≈ (log D)^K/K!, but it is false for the window sieve actually used here, where the sifting primes are > K. This corrects a KNOWN item and blocks T10 as stated.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 0, "cite": "Selberg upper-bound sieve in dimension κ=K (e.g. Halberstam–Richert, Sieve Methods, Ch. 3–4; Friedlander–Iwaniec, Opera de Cribro, Ch. 7)", "why": "The bound N^{1-(A-1)/(6A)+o(1)} is the standard Selberg Λ² computation for K-dimensional sifting by primes >K at level y=N^{1/6}; it only corrects an over-broad internal barrier statement and gives no progress toward F(n)→∞.", "panel": [{"verdict": "routine", "cite": "Selberg upper-bound sieve in dimension κ=K (e.g. Halberstam–Richert, Sieve Methods, Ch. 3–4; Friedlander–Iwaniec, Opera de Cribro, Ch. 7)", "significance": 0, "why": "The bound N^{1-(A-1)/(6A)+o(1)} is the standard Selberg Λ² computation for K-dimensional sifting by primes >K at level y=N^{1/6}; it only corrects an over-broad inte`
**Proof or evidence.**

1. Local densities. For a squarefree m whose primes are all > K, let ρ(m) = #{n mod m : m | Δ_K(n)}. For p > K the residues −1, …, −K mod p are distinct, so ρ(p) = K. By CRT ρ(m) = K^{ω(m)}, which is < m. Every block of m consecutive n contains exactly ρ(m) such n, so #{n ≤ N : m | Δ_K(n)} = Nρ(m)/m + θρ(m) with |θ| ≤ 1.
2. Selberg. Write g = ρ/id, so g(p) = K/p ∈ (0,1). Then Σ_{n≤N} f(n) = N·Σ_{d,e} λ_d λ_e g([d,e]) + R. Selberg's minimisation (standard; e.g. Halberstam–Richert Thm 3.2) makes the quadratic form equal to 1/G(y), where G(y) = Σ_{d≤y, d|P} h(d) and h(p) = g(p)/(1−g(p)) = K/(p−K). The optimal weights satisfy |λ_d| ≤ 1. Also ρ([d,e]) ≤ ρ(d)ρ(e), so |R| ≤ (Σ_{d≤y, d|P} ρ(d))² ≤ (Σ_{d≤y} d)² ≤ y⁴ = N^{2/3}.
3. Lower bound for G. By the PNT, M := π(2K) − π(K) ≥ K/(2·log K) for large K. For K < p ≤ 2K we have h(p) = K/(p−K) ≥ 1. Let j = ⌊log y / log 2K⌋. For large N, j ≈ log N/(6A·L2) ≤ M, because A > 1. Every product of j distinct primes from (K, 2K] is ≤ (2K)^j ≤ y and has h ≥ 1. So G(y) ≥ C(M, j) ≥ (M/j)^j.
   Now log M ≥ A·L2 − O(L3) and log j ≤ L2, so log(M/j) ≥ (A−1)·L2 − O(L3). Also j ≥ log N/(6(A·L2 + 1)) − 1. Hence log G(y) ≥ ((A−1)/(6A))·log N·(1 − o(1)).
4. Combining: mass ≤ N^{1−(A−1)/(6A)+o(1)} + N^{2/3} = N^{1−(A−1)/(6A)+o(1)}, since (A−1)/(6A) < 1/3. Finally f ≥ 0, and f(n) = λ₁² = 1 when (Δ_K(n), P) = 1. ∎

## [valid-routine] r1s4/C2 PROVED NEGATIVE
**Statement.** Fix K, D > K and z ≥ D, and a profile r_k ≥ 0 (k ≤ K). Let S = {n ∈ ℤ : ω_{(K,z]}(n+k) ≤ r_k for all k ≤ K}. Let f(n) = Σ_{d | (Δ_K(n), P(K,D])} λ_d with arbitrary real λ_d (any level ≤ D) and f ≥ 1_S on all of ℤ. Then the main-term density M = Σ_d λ_d ρ(d)/d satisfies M ≥ ∏_{K<p≤D}(1 − K/p) ≥ exp(−K·log(log D/log 2K) − c·K) for an absolute constant c. Hence the sieve upper bound N·M + Σ|λ_d|ρ(d) is ≥ N·exp(−K·log(log D/log 2K) − cK).
Consequence: if E_C(N) is bounded via one window of length K with D ≤ N, the bound is never better than N·exp(−K·(L2 + O(1))). To reach N·exp(−(log N)^β) one needs K ≥ (log N)^β/(L2 + O(1)).
**Beyond.** This is a rigorous form of the "local" half of the blackboard's level barrier conjecture, for arbitrary divisor-sum majorants. It is elementary.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 0, "cite": "Standard sieve fact: an upper-bound sieve majorant has main term at least the sifted density ∏(1−ρ(p)/p) (e.g. Friedlander–Iwaniec, Opera de Cribro; Halberstam–Richert, Sieve Methods)", "why": "f is periodic mod P(K,D] and is at least 1 on every class with Δ_K(n) coprime to P(K,D] (CRT handles the primes in (D,z]), so M ≥ ∏(1−K/p), and Mertens gives the rest. This is the textbook statement that an upper-bound sieve cannot beat the sifted density, and it only formalizes the already-noted level barrier.", "panel": [{"verdict": "routine", "cite": "Standard sieve fact: an upper-bound sieve majorant has main term at least the sifted density ∏(1−ρ(p)/p) (e.g. Friedlander–Iwaniec, Opera de Cribro; Halberstam–Richert, Sieve Methods)", "significanc`
**Proof or evidence.**

- f is periodic mod Q = P(K,D], and its average over a period is M. Let S_D = {n : ω_{(K,D]}(n+k) ≤ r_k for all k}; it is periodic mod Q.
- For n ∈ S_D, CRT gives n′ ≡ n (mod Q) such that n′+k ≢ 0 mod p for every p ∈ (D, z] and every k. This is possible because p > K leaves p − K ≥ 1 admissible residues, and z is finite. Then n′ ∈ S, so f(n) = f(n′) ≥ 1. Hence f ≥ 1_{S_D}, so M ≥ dens(S_D) ≥ dens{n : (Δ_K(n), Q) = 1} = ∏(1 − K/p).
- Primes p > 2K: log(1 − K/p) ≥ −K/p − K²/p². Mertens and Σ_{p>2K} K²/p² ≤ K give total ≥ −K·log(log D/log 2K) − O(K).
- Primes K < p ≤ 2K: Σ log(p/(p−K)) ≤ Σ_{m=1}^{K} log(2K/m) = K·log 2K − log K! ≤ K(1 + log 2).
- The error term is ≥ 0. ∎

## [valid-routine] r2s1/C2 PROVED NEGATIVE
**Statement.** - Fix Z ≥ K ≥ 30032 and let M = P(Z)/2310. For e ≡ 0 (mod ord_M 2), put n_e = 2310·2^e − 2312, an infinite family.
- Then n_e ≡ −2 (mod p) for all p ≤ Z, and n_e + 2312 = 2310·2^e is Z-smooth.
- By S-unit finiteness, for large e no other term n_e+k (k ≤ K) is Z-smooth.
- Hence the "residue + one-large-prime" lower bound for n_e is max(5w(2312), max_{3≤k≤K, k≠2312} (ω(k−2)+1)w(k)) = 7w(30032) = 1.5840721 < T.
- So no argument using only the residues n mod p (p ≤ Z), Størmer/S-unit finiteness and "each non-smooth term has ≥ 1 extra prime" can prove F(n) ≥ T for all large n. The E-exemption in C1 is necessary for this method.
**Beyond.** - The blackboard has the abstract pattern "a ≡ −2, designated smooth k* = 2312 gives 7w(30032)".
- New here: this pattern is realised by actual integers (an explicit infinite family), so the barrier is genuine. Note that the valuation-exact pattern (mod p^a) cannot be realised with a smooth term, which is why the squarefree modulus is used.
- Also new: the team-lead goal "F(n) ≥ 6w(2312) for all large n via SAT + Størmer" is unreachable as stated.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 0, "cite": null, "why": "This is an explicit CRT/order-of-2 realisation of the blackboard's abstract 'a ≡ −2 with designated smooth term 2312' pattern, plus standard S-unit finiteness. It is correct and useful internally for ruling out the team's SAT+Størmer strategy, but it is a barrier for a non-literature method and says nothing new about F(n).", "panel": [{"verdict": "routine", "cite": null, "significance": 1, "why": "This is an explicit CRT/order-of-2 realisation of the blackboard's abstract 'a ≡ −2 with designated smooth term 2312' pattern, plus standard S-unit finiteness. It is correct and useful internally for ruling out the team's SAT+Størmer strategy, but it is a barrier for a non-literature method and says nothing new about F(n)."}, {"verdi`
**Proof or evidence.**

- Residues and smoothness. n_e + 2 = 2310(2^e − 1) and M | 2^e − 1, so P(Z) | n_e + 2. Then n_e + k ≡ k − 2 (mod p), giving ω_{≤Z}(n_e+k) = ω_{≤Z}(k−2) = ω(k−2) for 3 ≤ k ≤ K.
- Maximum away from 2312:
  - For k ≠ 2312, the value of (ω(k−2)+1)w(k) is checked numerically for k < 40000. The top values are 30032: 1.584072, 2732: 1.568459, 212: 1.566601.
  - Beyond 40000, use the r-analysis of C1(c). For r ≤ 5 the value is ≤ 6w(40000) < 1.568. For r ≥ 6 it is ≤ (r+1)w(P_r + 2) ≤ 7w(30032).
- At k = 2312 the term is smooth, so it gets no +1: 5w(2312) = 1.3214. ∎

Heuristic (not claimed): F(n_e) ≥ T for large e. The terms 2310·2^e + d, d small, are very unlikely to all be (smooth)·prime along an exponentially sparse sequence.

## [valid-routine] r2s2/C1 PROVED NEGATIVE
**Statement.** Notation:
- Let N be large and W a set of K consecutive integers.
- Let r ≥ 1, and let P be any set of primes in (K, ∞) that contains every prime in (K, 2K].
- For each prime p, write h(p) = K/(p−K). Put h(d) = ∏_{p|d} h(p) and G_S(ξ) = Σ_{d ≤ ξ, d squarefree, p|d ⇒ p∈S} h(d).
- For a finite set E ⊂ P, put q_E = ∏_{p∈E} p. Let K_r(E) be the number of maps φ: E → W with all fibres of size ≤ r.

For the event Exc_r = {n ≤ N : ω_P(n+k) ≤ r for all k ∈ W}, the "pattern + Λ²" scheme does the following:
- Since p > K, each prime p ∈ P divides at most one n+k with k ∈ W. So Exc_r is contained in the union, over finite E ⊂ P and φ: E → W with fibres ≤ r, of the sets
  A(E,φ) = {n ≤ N : n ≡ −φ(p) (mod p) for all p ∈ E, and p ∤ ∏_{k∈W}(n+k) for all p ∈ P∖E}.
- Each set is bounded by Selberg's sieve: |A(E,φ)| ≤ N/(q_E·G_{P∖E}(ξ_E)) + R(E,φ), with any level ξ_E ≤ N. Here N/q_E is the length, and the sieve has dimension K with ω(p) = K, so h(p) = K/(p−K).

The scheme's bound is therefore B ≥ N·V, where V := Σ_E K_r(E)/(q_E·G_{P∖E}(ξ_E)).

Claim: for every δ ∈ (0,1] there is N₀(δ) such that for N ≥ N₀ we have V ≥ N^{−δ}, uniformly in K ≥ 1, r ≥ 1, W, P and the ξ_E ≤ N. Moreover V ≥ 1 (so B ≥ N, the trivial bound) as soon as K/log K ≥ 10·log N + 10·log K + 20.

The same holds if the caps r_k depend on k, as long as every r_k ≥ 1. It holds for every local superset of {F(n) < C} that includes all injective patterns. This is automatic: w(k) ≤ 0.368, so C/w(k) > 1 for every C ≥ 0.37, which permits ω(n+k) = 1.
**Beyond.** - The lead asked in round 1 to decide whether r1s4/C1's r = 0 power saving extends to r ≍ C·A·L2/L3. That is, whether combining Λ² with Lemma U gives N^{1−c(C)}.
- C1 settles this negatively for the natural combination, and already at r = 1. This is far below the r ≍ L2/L3 that F < C actually allows.
- It also pins down where the gain is lost:
  - The entropy of patterns from primes in (K, 2K] is exp(c·K/log K). Each such prime hits the window with probability ≥ 1/2.
  - This beats any Selberg G, since G ≤ e²KN always.
- The KNOWN list had only the heuristic "Rankin cost swamps the saving".
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Novelty.** `{"verdict": "routine", "significance": 1, "cite": null, "why": "This is a method-specific barrier: a union bound over prime-to-shift patterns plus Selberg's sieve loses because the entropy of patterns from primes in (K,2K] exceeds any sieve saving. That is a short, standard computation making precise the known heuristic that pattern/Rankin entropy swamps the sieve gain, and it says nothing new about F(n) itself.", "panel": [{"verdict": "routine", "cite": null, "significance": 1, "why": "This is a method-specific barrier: a union bound over prime-to-shift patterns plus Selberg's sieve loses because the entropy of patterns from primes in (K,2K] exceeds any sieve saving. That is a short, standard computation making precise the known heuristic that pattern/Rankin entropy swamps the sieve gain,`
**Proof or evidence.**

(0) Monotonicity. h ≥ 0, so G_{P∖E}(ξ_E) ≤ G_P(ξ_E) ≤ G_P(N). Also K_r(∅) = 1, and K_r(E) ≥ K_1(E) = (K)_{|E|} = K(K−1)⋯(K−|E|+1) for r ≥ 1, counting injective φ. Hence
  V ≥ U/G_P(N) with U := Σ_{E⊂P} (K)_{|E|}/q_E, and also V ≥ 1/G_P(N) from the E = ∅ term.

(1) General bound G_P(N) ≤ e²·K·N (Rankin with σ = 1).
- First, G_P(N) ≤ Σ_d h(d)·N/d = N·∏_{p∈P}(1 + h(p)/p) ≤ N·exp(Σ_{p∈P} h(p)/p).
- Primes p ∈ (K, 2K]: h(p)/p = K/(p(p−K)) ≤ 1/(p−K). The numbers p−K are distinct integers in [1, K], so these terms sum to ≤ 1 + log K.
- Primes p > 2K: p−K ≥ p/2, so h(p)/p ≤ 2K/p². These terms sum to ≤ 2K·Σ_{n>2K} 1/(n(n−1)) = 2K/(2K) = 1.
- So G_P(N) ≤ N·e^{2+log K} = e²KN.

(2) Lower bound for U when K ≥ 144.
- Let Q = primes in (K, 2K] ⊂ P and m = |Q|. Every E ⊂ Q has |E| ≤ m ≤ K/2. (For K ≥ 12, primes in (K, 2K] are coprime to 6, so m ≤ K/3 + 2 ≤ K/2; also checked numerically for 12 ≤ K ≤ 2·10⁵.)
- So (K)_{|E|} ≥ (K/2)^{|E|}, since each factor is ≥ K − |E| + 1 > K/2. Also q_E ≤ (2K)^{|E|}.
- Hence U ≥ Σ_{E⊂Q} 4^{−|E|} = (5/4)^m.
- By Rosser–Schoenfeld (π(x) > x/log x for x ≥ 17 and π(x) < 1.25506·x/log x), m > 2K/log 2K − 1.25506·K/log K ≥ K/(2 log K) once log K ≥ 4.97, i.e. K ≥ 144. (Also checked directly for 144 ≤ K ≤ 2·10⁵.)
- So U ≥ exp(0.111·K/log K).

(3) Case K/log K ≥ 10 log N + 10 log K + 20. By (0), (1) and (2), log V ≥ 0.111·K/log K − log N − log K − 2 ≥ 0. So V ≥ 1. (The threshold forces K ≥ 144.)

(4) Case K ≤ (log N)^{1+δ/4}. Use Rankin with σ = δ/2:
- G_P(N) ≤ N^σ·∏(1 + h(p)p^{−σ}).
- Primes p ∈ (K, 2K]: Σ h(p)p^{−σ} ≤ K^{−σ}·Σ_{j=1}^{K} K/j ≤ K^{1−σ}(1 + log K).
- Primes p > 2K: Σ h(p)p^{−σ} ≤ 2K·Σ_{n>2K} n^{−1−σ} ≤ 2K·(2K)^{−σ}/σ ≤ (4/δ)·K^{1−σ}.
- Also K^{1−σ} ≤ (log N)^{(1+δ/4)(1−δ/2)} ≤ (log N)^{1−δ/4}.
- Hence log G_P(N) ≤ (δ/2)·log N + (log N)^{1−δ/4}·(1 + 2 log log N + 4/δ) ≤ δ·log N for N ≥ N₀(δ).
- So V ≥ 1/G_P(N) ≥ N^{−δ}.

(5) Gap check. Suppose neither (3) nor (4) applies, so K > (log N)^{1+δ/4}. The function x/log x increases for x ≥ e, so K/log K ≥ (log N)^{1+δ/4}/((1+δ/4)·log log N) > 10 log N + 10 log K + 20 for N ≥ N₀(δ). Two subcases:
- If K ≤ (log N)², then log K ≤ 2·log log N, and the left side is ≫ (log N)^{1+δ/4}/log log N, which dominates the right side.
- If K > (log N)², then K/log K − 10·log K ≥ K^{0.9} ≥ (log N)^{1.8} > 10·log N + 20 for large N.

In (3), the threshold together with N ≥ e³ forces K/log K ≥ 50, hence K ≥ 144. So (3) applies, and the cases cover everything. ∎

Remarks:
- Both regimes are genuine. Case (4) is exactly where r1s4's Selberg saving N^{(A−1)/(6A)} vanishes, since A → 1. Case (3) is exactly where it exists.
- The obstruction is not the truth. Heuristically the independent-model probability of Exc_1 is ≈ exp(−K·L2) per window, far below 1/N. The scheme loses because the Λ² main term 1/G_{P∖E} can never be smaller than 1/(e²KN). Meanwhile the Λ² masses of the hit patterns from P ∩ (K, 2K] sum to (5/4)^m ≫ N.

## [broken] deep/C2 PROVED NEGATIVE
**Statement.** The Secondary deliverable says that sieving a window of shifts at level ≤ N cannot certify F(n) = o(L2L4/L3). As a statement about window-sieve constructions, this is false. The construction of C1 is exactly a window sieve at level N^{0.04+o(1)}, with term-dependent sifting limits and per-range Brun truncations, and it certifies F(n) ≤ 80·L3 on N^{1−o(1)} values. The ceiling L2L4/L3 holds only under a common sifting limit log z ≍ L/K: then a window term may carry ≍K primes > z, which forces T ≳ K·w(15) and hence T ≳ L2L4/L3.
**Referee.** `{"valid": false, "first_error": "The central assertion — that construction C1 is a window sieve at level N^{0.04+o(1)} certifying F(n) <= 80*L3 on N^{1-o(1)} values of n — is stated with no proof, and C1 is not supplied. It must control all shifts k up to about N^{1/(80 L3)}, with term-dependent sifting limits log z_k of order L/L2. Making Brun's sieve work at that dimension and level is unjustified. The 'common sifting limit forces T >~ L2L4/L3' step is also asserted without derivation.", "fixable": false}`
**Adversary.** `{"broken": true, "how": "To certify F(n)<=80*L3, every shift k<=(log N)^{1/160} needs omega(n+k)<=m_k<=L2/2, below the typical count. A window sieve can only enforce this by sifting each such term to z_k with log z_k >~ L/m_k >~ 2L/L2. So at primes near N^{1/L2} roughly (log N)^{1/160} terms are sifted together, giving sieve dimension kappa ~ (log N)^{1/160}. Lower-bound and fundamental-lemma sieves need log D/log z >~ beta_kappa ~ kappa, so the required level is >= N^{(log N)^{1/160}/L2}, far above N, let alone N^{0.04}. Per-range Brun truncations do not help: in that prime range the truncation length must still be ~kappa. Term-dependent limits therefore do not escape the ceiling. Redoing the count for general T (number of binding terms K=exp((L2/2T)log(L2/T)) must be <~L2) gives exactly `
**Proof or evidence.**

(none)

## [broken] r1s3/C3 PROVED QUANT
**Statement.** Let E* = {n ∈ ℕ : ∃ k ∈ [0, 4000] with n+k 4000-smooth}. Then:
- #(E* ∩ [0, N]) ≤ 4001·(1 + log(N+4000)/log 2)^{π(4000)} = (log N)^{O(1)}.
- For every n ∉ E* there is k ∈ [3, 4000] with ω(n+k)·w(k) ≥ 6w(2312). Hence F(n) ≥ 6w(2312) = 1.585743141.
**Beyond.** - Improves C1 to the exact Dickson ceiling 6w(2312) (by C2, this is sharp for bounded windows).
- So the non-smooth bounded-window constant equals 6w(2312) exactly, under Dickson for the upper bound.
- Known before: [7w(30033), 6w(2312)].
**Referee.** `{"valid": false, "first_error": "Step 5: the decisive case k0∈{3,4} rests solely on the unverified assertion that the CNF from s2.py is UNSAT (window [3,4000], primes 13..4000); no certificate (DRAT/LRAT), encoding audit, or tabulated bounds b_k = t_k − ω_{≤11}(k−k0) is given, so this step is unproved. (Also, step 4's 't_k = 4 on [5,2312]' is false — t_k = 3 for roughly k∈[6,190] since w(k) > 1.2·w(2312) there — though this overestimate is only a relaxation and harmless if UNSAT holds.)", "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Proof or evidence.**

1. Let k0 ∈ [0, 2309] be such that 2310 | n + k0. Since n ∉ E*, no n+k with k ≤ 4000 is 4000-smooth. In particular each such n+k has a prime factor > 4000, which is not counted in ω_{≤4000}. So ω(n+k) ≥ ω_{≤4000}(n+k) + 1.
2. Case k0 ∈ {0, 1, 2} ∪ [5, 2309]: argue as in C1.
   - Put k = k0 + 2310 ∈ [2310, 2312] or k = k0 ∈ [5, 2309].
   - Then ω(n+k) ≥ 6, and w(k) ≥ min(w(5), w(2312)) = w(2312).
3. Case k0 ∈ {3, 4}. Write c_p = (−n mod p) for primes 13 ≤ p ≤ 4000. Then p | n+k ⇔ k ≡ c_p (mod p). Also ω_{≤11}(n+k) = ω_{≤11}(k − k0), with value 5 when 2310 | k − k0.
4. Suppose, for contradiction, that (ω(n+k))·w(k) < 6w(2312) for all k ∈ [3, 4000]. By step 1, for every such k:
   - ω_{≤11}(k − k0) + #{13 ≤ p ≤ 4000 : c_p ≡ k (mod p)} ≤ t_k,
   - where t_k = max{t : (t+1)·w(k) < 6w(2312)}.
   - For example t_3 = 17, t_4 = 5, and t_k = 4 on [5, 2312].
5. s2.py encodes exactly this system as CNF: one-hot residues c_p for every prime 13 ≤ p ≤ 4000, and sequential-counter at-most-b constraints for each k ∈ [3, 4000]. The CNF is UNSAT for k0 = 3 and for k0 = 4, so no residue choice satisfies step 4.
   - Primes > 4000 are omitted. This is valid because they only increase ω.
   - The SAT problem is not trivial: for window 2400 the k0 = 3 instance is SAT, so the window 4000 is really needed.
6. Count of E*: each element is s − k with s a 4000-smooth number ≤ N + 4000 and k ≤ 4000, and Ψ(x, y) ≤ ∏_{p≤y}(1 + log x/log p).

Remark: by Størmer/Baker, for large n at most one term in the window is smooth. But one smooth term already breaks the argument. Unconditionally, that case only gives the known 7w(30033).

## [broken] r1s3/C2 PROVED OTHER
**Statement.** Assume Dickson. For each fixed K there are infinitely many n ∉ E with max_{3≤k≤K} ω(n+k)w(k) ≤ 6w(2312). So no bounded-window argument can push the C1 constant beyond 6w(2312), even off E.
**Referee.** `{"valid": false, "first_error": "The step 'no n+k with k ≤ 2314 is 11-smooth, so n ∉ E' is only justified for k=2 (and only if K≥13) and for 3≤k≤K. For K<2314 the values n+k with K<k≤2314 are not controlled by the construction, and k=0,1 are not addressed. It is easily repaired by taking K≥2314 WLOG (the max is monotone in K) and noting n+1=Mt−1 and n=2(Mt/2−1) have no prime factors ≤K. Separately, Dickson admissibility and the max value 6w(2312) are asserted, not proved; both check out (admissibility holds; sup_k (ω(k−2)+1)w(k)=6w(2312)≈1.58575 via primorial check plus Robin's bound).", "fixable": true}`
**Adversary.** `{"broken": false, "how": "No counterexample. The Dickson system (M/(k-2))m+1, M=lcm(1..K), is admissible. The max of (ω(k-2)+1)w(k) is 6w(2312)=1.585745, since 7w(30032)=1.5840 and 5w(212)=1.5666; 1.587 > 1.586945 holds. Gap: for K<2314 (or K<13) the proof's 'no n+k with k≤2314 is 11-smooth' is not justified by the construction; fix by building with K'=max(K,2314) and using monotonicity in K.", "severity": "fixable"}`
**Proof or evidence.**

Use the known Dickson construction n ≡ −2 (mod lcm-type modulus), with n+k = (k−2)·(prime) for 3 ≤ k ≤ K and n+2 divisible by every prime ≤ K. Then no n+k with k ≤ 2314 is 11-smooth:
- for k ≠ 2, n+k has a large prime factor;
- n+2 is divisible by 13.

So n ∉ E. The maximum is known (blackboard) to be 6w(2312).

CONSEQUENCE FOR T2: 1.587 > 6w(2312) + 1.2·10⁻³. Even after deleting a polylog-thin set, T2 requires windows that grow with n. This sharpens "c₁ barrier": the barrier is not the smooth-plant phenomenon.

## [broken] r2s1/C1 PROVED QUANT
**Statement.** Let w(k) = loglog k/log k and T = 6w(2312) = 1.58574314111350…
- (a) Let n ≥ 0 be such that none of n+3, …, n+13093 is 61-smooth (each has a prime factor > 61). Then some k ∈ [3, 13093] has ω(n+k)·w(k) ≥ T, so F(n) ≥ T.
- (b) Let E be the set of n failing the hypothesis of (a). Then #(E∩[0,N]) ≤ 13091·Ψ(N+13093, 61) = O((log N)^{18}).
- (c) Assume Dickson's prime k-tuples conjecture. For every K ≥ 13093 there are infinitely many n with max_{3≤k≤K} ω(n+k)w(k) = T and n ∉ E. So T is exactly the best constant obtainable from any bounded window, even off E.
**Beyond.** - r1s3/C1 had 6w(2314) off a polylog set.
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

Step 2 (forcing chain). Call position k *full* if the counts already forced satisfy count(k) = b_k. Counts only grow as more primes are placed, so full positions stay full, and no further prime may hit a full position. If every residue class mod p except one contains a full position in [3, 13093], then r_p is forced to that class. If 
**Referee.** `{"valid": false, "first_error": "Proof of (a), Step 2 (forcing chain): the text breaks off mid-sentence ('If )') and the explicit forcing certificate is never given. Everything up to Step 1 checks out (T, the b_k table, and k0 ∈ {3,4}), but nothing turns k0 ∈ {3,4} into a contradiction: no forced residues for primes 13..61 and no final clash. This is the step that was supposed to replace the broken uncertified SAT call, so (a) is unproved. (b) and (c) also come with no proof; the bound in (b) is a routine union bound, but (c) needs an explicit residue pattern plus a Dickson argument.", "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Proof or evidence.**

(none)

## [broken] r2s3/C1 PROVED CONDITIONAL
**Statement.** Notation:
- L = log x, L2 = log L, L3 = log L2, and w(k) = loglog k/log k.
- For an integer K ≥ 2, H_K = (K/2,K] ∩ ℤ and J = |H_K| ≥ K/2.
- ω*(m) = #{p prime : p | m, K < p ≤ √x}. This depends on x and K.
- E(x,K,R) = #{n ∈ ℤ∩(x,2x] : ω*(n+h) ≤ R for all h ∈ H_K}.
- q_h(x,K,R) = x^{-1}·#{n ∈ ℤ∩(x,2x] : ω*(n+h) > R}.

**Hypothesis U(c)**, with c ∈ (0,1] fixed. There is x₀ such that for all x ≥ x₀, all integers K ∈ [32, L²] and all integers R ≥ 0,
  E(x,K,R) ≤ x·∏_{h∈H_K} (1 − q_h)^c.
(The case c = 1 is exact independence of the J single-term events. Only the case R = ⌊2L2⌋, K = ⌊L^a⌋ with a = 2log2+ε is used.)

**Theorem.** Assume U(c). Then for every ε > 0 there is n₀ such that F(n) ≥ (1/log 2 − ε)·logloglog n for all n ≥ n₀. Hence F(n) → ∞.
**Beyond.** KNOWN contains no conditional proof of F → ∞. The map's barriers are not violated:
- U is a statement about primes in (K,√x] with K = L^{1.39} > log x. For n ≤ 2x these primes cannot be steered by CRT, so U is consistent with the c₀ and archimedean barriers.
- U uses windows of length L^{1.39+ε} ≫ log n, so it is consistent with the c₁/Dickson barrier.
- It is a pointwise statement only where its bound is < 1; elsewhere it is a counting statement.
**Referee.** `{"valid": true, "first_error": null, "fixable": true}`
**Adversary.** `{"broken": true, "how": "Hypothesis U(c) as literally stated (for all real x ≥ x0) is false: for non-integer x with frac(x) ∈ [1/2,1), (x,2x] contains ⌊2x⌋−⌊x⌋ = x+1−frac(x) > x integers; taking R ≥ L makes every q_h = 0, so E(x,K,R) > x = x·∏(1−q_h)^c for every c and every admissible K, at arbitrarily large x. The conditional theorem is therefore vacuous as stated. The fix is to restrict U to integer x (the proof only uses x = n−1) or to replace x by ⌊2x⌋−⌊x⌋. Lemmas 1, 2 and the deduction F(n) ≥ (2/a)·L3 otherwise check out; the ε bookkeeping needs a re-choice of ε (1/(log2+ε/2) is slightly below 1/log2−ε).", "severity": "fixable"}`
**Proof or evidence.**

**Lemma 1 (unconditional).** Fix a ∈ (1,2) and put K = ⌊L^a⌋. Let 1 ≤ r ≤ 3L2. Then for x large and every h ∈ H_K,
  x·q_h(x,K,r−1) ≥ (x/(2L))·(S^r/r!)·(1 − r²/(2KS²)),
where S = Σ_{K<p≤T} 1/p and T = x^{1/(4r)}.

*Proof of Lemma 1.*
- As n runs over (x,2x], m = n+h covers (x+h, 2x+h] ⊇ (x+K, 2x]. Count those m in (x+K, 2x] of the form m = p₁⋯p_r·q, where K < p₁ < … < p_r ≤ T and q is a prime with (x+K)/P < q ≤ 2x/P, P = ∏p_i.
- Since P ≤ T^r = x^{1/4}, we get q > x^{3/4} > √x. So the primes of m in (K,√x] are exactly p₁,…,p_r, and ω*(m) = r > r−1.
- Unique factorisation makes distinct (p,q)-data give distinct m.
- By the PNT, uniformly for Y = x/P ≥ x^{3/4} and x large, the number of q is ≥ (x−K)/(P·1.9·log x) ≥ x/(2PL).
- Summing over r-sets of primes gives ≥ (x/2L)·e_r, where e_r = Σ_{p₁<…<p_r} 1/P.
- Expand S^r as a sum over ordered r-tuples. Tuples with distinct entries give r!·e_r. Tuples with a coincidence at some pair of positions i<j contribute ≤ C(r,2)·S₂·S^{r−2}, where S₂ = Σ_{p>K} p^{−2} ≤ 1/K.
- Hence e_r ≥ (S^r/r!)(1 − r²/(2KS²)). ∎

**Lemma 2.** With a ∈ (1,2), K = ⌊L^a⌋ and R = ⌊2L2⌋, we have q_h(x,K,R) ≥ L^{−(2log2−1)}·e^{−O(L3)} for every h ∈ H_K.

*Proof of Lemma 2.*
- Take r = R+1 ∈ (2L2, 2L2+1].
- By Mertens, S = log log T − log log K + o(1). Here log log T = L2 − log(4r) = L2 − L3 − O(1), and log log K = L3 + log a + o(1). So L2 − 2L3 − O(1) ≤ S ≤ L2.
- Stirling: r! ≤ e·r^{r+1/2}e^{−r}. This was checked numerically for all r < 170 and is standard in general.
- Therefore log(S^r/r!) ≥ r(1 − log(r/S)) − O(log r).
- We have r/S ≤ 2(1 + O(L3/L2)). Since 1 − log 2 > 0 and 2L2 < r ≤ 2L2+1, this gives r(1 − log(r/S)) ≥ 2L2(1 − log 2) − O(L3).
- The factor 1 − r²/(2KS²) = 1 − o(1), because K = L^a.
- Lemma 1 then gives log q_h ≥ −log 2 − L2 + 2L2(1 − log 2) − O(L3) = −(2log2 − 1)L2 − O(L3). ∎

**Proof of the Theorem.**
- Fix ε ∈ (0, 1/2). Put a = 2log2 + ε ∈ (1,2), K = ⌊L^a⌋ (so 32 ≤ K ≤ L² for large x), and R = ⌊2L2⌋.
- Since (1−q)^c ≤ e^{−cq}, U(c) and Lemma 2 give
  E ≤ x·exp(−c·J·min_h q_h) ≤ x·exp(−c(L^a/2 − 1)·L^{1−2log2}·e^{−O(L3)}) = x·exp(−(c/2)·L^{1+ε}·(L2)^{−O(1)}(1+o(1))).
  This is < 1 for large x, so E = 0.
- Given a large n, put x = n − 1. Then n ∈ (x,2x], so there is h ∈ (K/2,K] with ω(n+h) ≥ ω*(n+h) ≥ R+1 > 2L2.
- Since h > K/2 > e^e and w is decreasing on [e^e,∞), w(h) ≥ w(K) = loglog K/log K. Here log K ≤ aL2, and loglog K ≥ L3 + log a − o(1) ≥ L3 for large x.
- Hence F(n) ≥ ω(n+h)·w(h) ≥ 2L2·L3/(aL2) = (2/a)·L3(x).
- Finally L3(n) − L3(x) → 0, and 2/a = 1/(log 2 + ε/2). Since ε is arbitrary, the Theorem follows.
- (Lean side: the family k ↦ ω(n+k)w(k) is bounded above, as noted on the blackboard, so the ⨆ is ≥ every term.) ∎

REMARKS.
- (i) The constant comes from the variational problem sup_{t>1} t/(1+I(t)) with I(t) = t log t − t + 1. The supremum is attained at t = 2 and equals 1/log 2 (numerically 1.4426950409 at t = 2.00001). Using threshold R ≈ tλ needs a window K = L^{1+I(t)+ε} and yields t/(1+I(t))·L3.
- (ii) A lower-tail variant takes R = θL2 with θ < 1 and K ≍ L/L2. It needs a single-term upper bound p_h ≤ L^{−I(θ)+o(1)} (Halberstam–Richert/Hall–Tenenbaum type, recalled, not checked) and gives only θL3 with θ < 1. So the upper-tail regime is the right one.
- (iii) Honesty note: in the one instance used, the bound in U(c) is < 1. There U(c) is a pointwise "every window of length L^{1.39+ε} has a term with > 2L2 prime factors in (L^{1.39}, √x]" statement. It is a Janson-type independence hypothesis, not a known theorem.

## [broken] r2s4/C2 PROVED QUANT
**Statement.** Fix θ > 0 and s = 1/θ. Let T(n) = #{k ≥ 3 : ω(n+k)·w(k) ≥ θ L3(N)}. Then (1/N) Σ_{N<n≤2N} T(n) = (log N)^{e^{s}−1+o(1)}.
**Beyond.** This is the first quantitative statement about the supply of witnesses at the critical scale. It shows witnesses at k ≈ (log N)^{s e^s} with ω ≈ e^s L2 are polylogarithmically abundant on average, which identifies the right statistic for any future proof.
**Referee.** `{"valid": false, "first_error": "Step (0): p_k = 0 for k >= N^eps is justified only by comparing y_k with max_{m<=3N} omega(m), which covers only k <= N (n+k <= 3N). Since k is unbounded, k > N is not handled; it needs omega(n+k) <= (1+o(1)) log(3k)/loglog(3k) < y_k. Also, in step (2) the bound 'for t <= L3 the ratio is >= (theta/2)(L3/2)' is false for t near log B (the ratio there is about theta log(theta B/e), which is bounded). The correct bound (theta/2)(t - log(2e/theta)) >= 2 still gives the conclusion for large B.", "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Proof or evidence.**

see "Proof of C2/C3" below.

Write p_k = P_n(ω(n+k) ≥ y_k), where y_k = θL3/w(k) = θL3·log k/loglog k. Then E T = Σ_k p_k and −log P_model = Σ_k −log(1−p_k).

(0) Large k contribute nothing. Fix ε > 0. For k ≥ N^ε we have y_k ≥ θL3·ε log N/L2. This exceeds max_{m≤3N} ω(m) ~ log N/L2 once θεL3 > 2. So p_k = 0.

(1) Small k. Take δ > 0. If k ≥ (log N)^{(1+2δ)s}, then y_k ≥ (1+δ)L2 for large N, because log k/loglog k is increasing. So p_k ≤ 1/2 (Turán). Hence at most (log N)^{(1+2δ)s} indices have p_k > 1/2. For each of them:
- 1−p_k ≥ P(n+k is a prime power) ≥ 1/(2 log 3N), since y_k > 1 for k ≥ 3 and large N.
- So −log(1−p_k) ≤ 2L2.
Their total is ≤ (log N)^{(1+2δ)s+o(1)}, which is (log N)^{<e^s−1} for small δ, since e^s−1 > s.

(2) Upper bound on p_k when y_k ≥ (1+δ)L2. Hardy–Ramanujan gives #{m≤x: ω(m)=r} ≤ c₁ x/log x·(L2(x)+c₂)^{r−1}/(r−1)!. Put λ = L2+c₃. Chernoff then gives p_k ≤ C·exp(−λQ((y_k−1)/λ)).
- Range β = log k/L2 ∈ [(1+2δ)s, B]: here y_k = θβL2(1+O_B(1/L3)), so p_k ≤ (log N)^{−Q(θβ)+o(1)} uniformly. Summing over k ∈ [e^{βL2}, e^{(β+dβ)L2}] gives Σ p_k ≤ (log N)^{max_β(β−Q(θβ))+o(1)} = (log N)^{e^s−1+o(1)}. The max is at θβ = e^s: d/dβ = 1 − θ log(θβ) = 0, and the value is s e^s − (e^s·s − e^s + 1) = e^s − 1.
- Range β ∈ [B, ε log N/L2], t = log β: one checks λQ(u) ≥ y' log(y'/(eλ)) ≥ 2βL2 = 2 log k, with y' = y_k − 1.
  - At fixed t the ratio y' log(y'/eλ)/(βL2) is ≈ θ log(θβ/e) ≥ 2 once B ≥ e^{1+2/θ}/θ.
  - For t ≤ L3 it is ≥ (θ/2)(L3/2) → ∞.
  - For t ∈ [L3, L2] it is ≥ (θL3/(2t))·(t−log 2t) ≳ θL3/2 → ∞.
  - So p_k ≤ C k^{−2}, and this range contributes ≤ (log N)^{−B}.
  Since p_k ≤ 1/2 here, −log(1−p_k) ≤ 2p_k. So E T and −log P_model are both ≤ (log N)^{e^s−1+o(1)}.

(3) Lower bound. Fix η > 0 and x₀ = e^s, β₀ = x₀/θ. For k ∈ [(log N)^{β₀−η}, (log N)^{β₀}], y_k ≤ x₀L2(1+o(1)). Sathe–Selberg holds uniformly for r ≤ AL2, also on (N+k, 2N+k] with k ≤ N^{1/2}. With r = ⌈y_k⌉ it gives p_k ≥ P(ω=r) ≥ c(log N)^{−1}L2^{r−1}/(r−1)! = (log N)^{−Q(x₀)+O(η)+o(1)}. Summing, Σ p_k ≥ (log N)^{β₀−Q(x₀)−O(η)−o(1)} = (log N)^{e^s−1−O(η)−o(1)}. Finally −log(1−p) ≥ p. Let η → 0. ∎

## [broken] r2s4/C3 PROVED ANALOGUE
**Statement.** Independent-shift model: let Y_k (k ≥ 3) be independent, with Y_k distributed as ω(n+k) for n uniform in (N,2N]. Then −log P(∀k: Y_k w(k) < θL3) = (log N)^{e^{1/θ}−1+o(1)}.
**Beyond.** A rigorous model theorem behind C1. Any proof of exponent > e^{1/θ}−1 must use correlations between shifts in an essential way.
**Referee.** `{"valid": false, "first_error": "No proof is given at all: the asserted asymptotic -log P = (log N)^{e^{1/θ}-1+o(1)} is unsupported (and w(k), L3 are not even defined). Heuristic recomputation via Sathe–Selberg (optimize λ/θ + λ − λlogλ − 1 at λ=e^{1/θ}) reproduces the exponent, but the needed steps — uniform Selberg asymptotics for ω on (N+k,2N+k] up to t≈e^{1/θ}L2, handling the non-small-probability range λ<1, the large-k tail, (log N)^{o(1)} error control, and a matching lower bound — are all missing.", "fixable": true}`
**Adversary.** `{"broken": false, "how": null, "severity": "none"}`
**Proof or evidence.**

(none)

## [not validated] r1s1/C3 CONJECTURED OTHER
**Statement.** In the Brun–Rankin scheme of Lemma U, choose per-shift ranges (K_k, z_k] and weights y_k (profile-adapted, r_k = C log k/loglog k), at level ≤ N.
The certified saving X satisfies X ≤ (1+o(1))·max_{K'} min(K'·λ, log N/(e²·log z(K'))), with log z(K') ≥ e^{r(K')}·log K'.
So X ≤ (log N)^{1-(C-o(1))/L3}, the same exponent as the single window (blackboard). Heterogeneous r_k change only constants.
Reason: a shift of scale k gives saving only if λ_k > r_k, i.e. log z_k ≥ e^{r_k} log k. It costs level ≈ (saving)·log z_k. Over dyadic scales 2^j ≤ K', both total saving and total level cost are geometric sums dominated by the top scale, which reduces to a single window at scale K'.
Also, the "first step" bound N∏_kP(ω≤r_k)e^{O(K)} for K=(log N)^β needs λ≈L2, i.e. z = N^{Ω(1)}, while the level gives log z ≤ log N/(e²K L2).
Lemma U does give #{n≤N: ω(n+k)≤r_k ∀k∈[16,K]} ≤ N exp(-(1-β-o(1))K L2), with λ = L2 - log(e²K L2) - loglog K ≈ (1-β)L2. That is the first step with the exponent multiplied by (1-β), valid for K ≤ log N/L2³ and any fixed β<1. It is weaker than the blackboard bound for fixed C, so it is not claimed as new.
**Proof or evidence.**

(none)

## [not validated] r1s2/C2 OTHER NEGATIVE
**Statement.** For J ≥ 0 put Φ(J) = sup_{0≤j≤J, k≥3} w(k)/w(j+k), and G_J(n) = max_{0≤j≤J} F(n+j).
- (i) F(n) ≤ G_J(n) ≤ Φ(J)·F(n) for all n.
- (ii) Φ(J) = (w(15)+o(1))·log J/loglog J. Numerically Φ(10³) = 1.316, Φ(10⁴) = 1.526, Φ(10⁵) = 1.733; for large J the sup is attained at k = 15, j = J.
- (iii) NEGATIVE: route A2 ("one C-exception forces a run of J C·Φ(J)-exceptions; count runs with a location-uniform density bound") is no stronger than producing a direct witness for F(n). A location-uniform density input at polylog scale can certify at most F ≥ 1 + o(1).
**Beyond.** Settles that assignment A2 cannot beat the c₀/c₁ ceilings on its own.
**Proof or evidence.**

(i) Take k ≥ 3 and j ≤ J. Since w(j+k) > 0,
ω(n+j+k)·w(k) = ω(n+(j+k))·w(j+k)·[w(k)/w(j+k)] ≤ F(n)·Φ(J).
Terms with k ≤ 2 have w(k) ≤ 0 (in Lean, log 0 = log 1 = 0), and F ≥ 0.

(iii) First, the propagation is a change of variables.
- Any certificate that G_J(n) ≥ C·Φ(J) is a pair (j, k) with ω(n+j+k)·w(k) ≥ C·Φ(J).
- By (i), this pair already gives F(n) ≥ C through the shift j+k.
- So A2 proves nothing that a direct witness search over shifts ≤ J + k does not.

Second, the counting input is unavailable at polylog scale.
- A location-uniform (Banach) density bound for {m : ω(m) ≤ r} on intervals of length H can only come from sieving by primes p ≤ z with z^{O(1)} ≤ H.
- Take n ≡ 0 (mod P(z)) with P(z) ≤ n. Then ω_{≤z}(n+k) = ω_{≤z}(k) for every k. So the maximum of ω_{≤z} over (n, n+H] is ≤ max_{k≤H} ω(k) = (1+o(1))·log H/loglog H.
- Hence such inputs certify ω(m) ≥ C·log J/loglog J within a run of length J only for C ≤ 1 + o(1). Via (i) that is F ≥ 1 − o(1), Erdős's bound.
- The CRT version of the same adversary is the KNOWN c₀ barrier, so the sharper constant 1.384 is all that residue methods can give.
∎

## [not validated] r2s2/C2 CONJECTURED NEGATIVE
**Statement.** - Fix C > 6w(2312). Let M be any function on ℤ of the form Σ_{d≤N} c_d(n mod d) with M ≥ 1 on the local superset {n : ∀k ≤ N, ω_{≤N}(n+k)·w(k) < C}.
- Conjecture: the mean of M over ℤ is ≥ exp(−(log N)^{1−c(C)/L3}) for some c(C) > 0.
- Equivalently, by LP duality: there is a measure ν on ℤ/P(N) that is uniform modulo every d ≤ N and gives the local exceptional event ν-mass ≥ exp(−(log N)^{1−c(C)/L3}).
- If true, no level-N local-majorant method (sieve, moments, Rankin) gives N^{1−c(C)}.
**Proof or evidence.**

- Uniformity mod d ≤ N amounts to m_Y-wise independence of the residues at primes ~Y, where m_Y = log N/log Y.
- A per-term cap r = C·log K/loglog K constrains only primes with λ(Y) = log(log Y/log K) > r, that is, log Y ≥ log K·e^r = L2·(log N)^{CA/L3}.
- Moment-matching bounds for m-wise independent Bernoulli sums give an upper bound exp(−Θ(m_Y)), and such bounds are typically tight up to constants in the exponent. This gives exactly (log N)^{1−Θ(C)/L3}.
- This matches the upper bounds already obtained (blackboard; r1s2/C1), and the r1s1/C3 barrier conjecture.
- The small primes p ≤ log N (forced uniform) cost only exp(−exp(O(L3·L4))) = N^{−o(1)}.
- Not proved: an exact D-uniform construction with per-residue (not just per-bit) control.

## [not validated] r2s3/C2 CONJECTURED CONDITIONAL
**Statement.** liminf_{n→∞} F(n)/logloglog n = 1/log 2.
**Beyond.** This is the first predicted exact growth rate of min F. KNOWN has only O(1) constants.
**Proof or evidence.**

- Model ω(n+k) for n+k ~ x as Poisson(L2), independent over k. Large primes are not shared; small primes p ≤ L shift each term by only O(L3), which changes probabilities by factors (L2)^{O(1)}. The adversarial CRT choice n ≡ −2 mod P(L) also only affects O(L3).
- For k ~ L^b, F < θL3 requires ω(n+k) < θbL2.
  - For θb < 1 (lower tail), the cost is ≈ L^b·L2·I(θb) per range. The total cost is L^{1/θ+o(1)}.
  - For θb > 1 (upper tail), the expected number of violators is Σ L^{b−I(θb)}, with sup_b (b − I(θb)) = e^{1/θ} − 1, attained at θb = e^{1/θ}. Checked numerically for θ ∈ {1, 1.2, 1/log2, 2, 3, 5, 10}.
- So −log P(F(n) < θL3) = L^{max(1/θ, e^{1/θ}−1)+o(1)} = L^{e^{1/θ}−1+o(1)}, since e^u − 1 > u.
- This exponent exceeds 1 iff θ < 1/log 2. Therefore min_{x<n≤2x} F(n) ≈ (1/log 2)·L3.
- C1's proof is exactly the rigorous upper-tail half of this computation.

## [not validated] r2s3/C3 CONJECTURED NEGATIVE
**Statement.** For fixed θ > 1/log 2, #{n ≤ N : F(n) < θ·L3(N)} = N·exp(−(log N)^{e^{1/θ}−1+o(1)}). For θ < 1/log 2 the set is finite.
**Beyond.** - This predicts that the exceptional-set exponent cannot be 1 − o(1) for θ > 1/log 2. That is relevant to r2s4's target.
- It compares as follows with the rigorous r1s2/C1 exponent 1/(1+θ):
  - Model exponent e^{1/θ} − 1 > 1/θ > 1/(1+θ).
  - The lower-tail-only part of the model gives exactly 1/θ. This suggests r1s2's mechanism is the lower-tail one, and that the upper-tail ("one term with abnormally many factors") mechanism is where the extra gain lies.
**Proof or evidence.**

(none)

## [not validated] r2s4/C1 CONJECTURED NEGATIVE
**Statement.** Conjecture. Put s = 1/θ.
(a) For θ > 1/log 2: #{n ≤ N : F(n) < θ L3} = N·exp(−(log N)^{e^{s}−1+o(1)}).
(b) For θ < 1/log 2: {n : F(n) < θ·L3(n)} is finite.
Hence liminf_{n} F(n)/logloglog n = 1/log 2. In particular the assignment's target (exponent 1−o(1) for all θ) fails for every θ > 1/log 2.
**Beyond.** KNOWN and round 1 only give upper bounds on the exceptional set, with exponent 1/(1+θ) (r1s2), and the team target assumed exponent 1−o(1). This is the first prediction of the true size of the set and of the growth rate of the minimum of F.
**Proof or evidence.**

Write k = (log N)^β. Then w(k) = (L3+log β)/(βL2), so the constraint ω(n+k)·w(k) < θL3 reads ω(n+k) < θβL2·(1+O(1/L3)).
- Upper-tail side: by Sathe–Selberg, P(ω(m) ≥ xL2) = (log N)^{−Q(x)+o(1)} for m≈N, where Q(x) = x log x − x + 1. So the expected number of k at scale β violating the constraint is (log N)^{β−Q(θβ)}. Maximising over x = θβ gives x = e^{s} and exponent e^{s}−1.
- Lower-tail side: β < s forces ω(n+k) < xL2 with x < 1. In an independent model this costs (log N)^{s+o(1)} in total, which is < e^{s}−1.
- So the cost of being exceptional is exp(−(log N)^{e^{s}−1+o(1)}). It is ≥ 1/N, i.e. the set is nonempty, iff e^{s}−1 < 1 iff θ > 1/log 2.
- Adversary view: n ≤ N can pay a cost of up to log N = (log N)^1. It can kill every witness family with β−Q(x) < 1, but no family with β−Q(x) > 1. The worst case is therefore F ≈ L3·sup_x x/(1+Q(x)). The derivative condition gives x = 2 and value 2/(2 log 2) = 1/log 2.
- Robustness: (i) CRT on primes ≤ Z costs e^{−Z} and shifts every ω by only O(L3) = o(L2). (ii) Sieving all window terms off primes in (K,z] costs exp(−K log(log z/log K)) with K = (log N)^{s e^s}, and s e^s > e^s − 1. (iii) Prime-tuple patterns (n+k = smooth·prime) cost exp(−K·L2). So none of these beats the random-model cost.
- Consistency check: r1s2's proven exponent satisfies 1/(1+θ) < 1−e^{−s} < e^{s}−1.

## Frontier map

=== DIRECTION
TRUE, confidence 0.9.

Evidence:
- **Typical size.** By Hardy–Ramanujan applied at k = 15, F(n) ≥ ω(n+15)·w(15) ≈ 0.36788·loglog n for almost all n. Here w(k) = loglog k/log k, and w(15) ≈ 1/e is the largest value of w on the integers.
- **Rare exceptions.** The almost-all bound #{n ≤ N : F(n) < C} ≤ N·exp(−(log N)^{1−(C+o(1))/L3}) is known (blackboard, informal). Here L2 = loglog n and L3 = logloglog n.
- **Shape of a counterexample.** For F(n) < C, every n+k with 16 ≤ k ≤ (log n)^A must satisfy ω(n+k) < C·log k/loglog k ≈ (CA/L3)·L2, which is far below the normal order L2.
  - So the window must be a run of length at least (log n)^{1+ε} made entirely of "rough almost-primes".
  - Uniform tuple heuristics give about N·(log N)^{−(1−o(1))K} such n ≤ N. This is far below 1 once K ≥ (log N)^{1+ε}.
- **Dickson-type constructions.** These only control windows of bounded length (or heuristically up to about log n/L2). Beyond that, typical behaviour gives F ≳ L3.
- **Sharp conjecture.** min over N < n ≤ 2N of F(n) = (1+o(1))·L3(N), so F → ∞, but only like logloglog n in the worst case.
- **The Lean statement is faithful.** For each n, the family k ↦ ω(n+k)w(k) is bounded above, because ω(m) ≤ (1+o(1))·log m/loglog m. So ⨆ is the true supremum and not Mathlib's junk value 0. Also log 0 = log 1 = 0, so k = 0, 1 contribute 0.

=== KNOWN
- F(n) ≥ 1 − o(1) | Erdős [Er80, p.107], problem page | CRT: some n+k with k ≤ P_r is divisible by the primorial P_r.
- For every n, F(n) ≥ 9·w(P₉+15) = 1.384012…, with P₉ = 223092870 | blackboard (routine) | some k ∈ [16, P₉+15] has P₉ | n+k, and w is decreasing for k ≥ 16.
- Small-prime ceiling: if n ≡ −2 (mod P(Z)), then ω_{≤Z}(n+k)·w(k) ≤ 9·w(P₉+2) for all k ≥ 3 | blackboard | explicit residue analysis. So c₀ ≈ 1.38401.
- liminf F(n) ≥ 7·w(30033) = 1.584069… | blackboard (informal, unverified) | residue analysis plus "one large prime per term".
- Under Dickson's conjecture, for each fixed K, liminf_n max_{3≤k≤K} ω(n+k)w(k) ≤ 6·w(2312) ≈ 1.586 | blackboard (conditional) | prime-tuple construction n+k = (smooth)·(prime). So c₁ ∈ [1.5841, 1.586] is the ceiling for bounded windows.
- #{n ≤ N : F(n) < C} ≤ N·exp(−(log N)^{1−(C+o(1))/L3}). For θ < θ′ < 1, #{n ≤ N : F(n) < θ·L3} ≤ N·exp(−(log N)^{1−θ′}) | blackboard (informal) | Rankin–Brun moments of the window total Σ_k ω_{(K,z]}(n+k).
- F(n) ≥ ω(n+15)·w(15) for all n, with w(15) = 0.367877 (and w(14) = 0.367717, w(16) = 0.367806). Hence F(n) ≥ (1/e − ε)·L2 except for O(N(log N)^{−c(ε)}) values n ≤ N | standard (Hardy–Ramanujan, Sathe–Selberg) | one shift.
- Witness range: ω(m) ≤ (1+o(1))·log m/loglog m, so ω(n+k)·w(k) ≤ (1+o(1))·log(2n)/log k for k ≤ n. Any k witnessing F(n) ≥ C therefore has k ≤ n^{1/C+o(1)}, and k ≥ n gives at most about 1.384 | standard | maximal order of ω.
- Density barrier at polynomial scales: #{m ≤ x : ω(m) ≥ α·log x/loglog x} = x^{1−α+o(1)}. So windows at scale k = n^θ yield at most C ≤ 1 + o(1) | standard (Hardy–Ramanujan, Erdős–Nicolas) | counting.
- Sylvester–Erdős type bound, n ≥ K^{1+ε}: the K-smooth part of Δ_K(n) = ∏_{k≤K}(n+k) is at most K!·(2n)^{π(K)}. Hence at most π(K)(1+o(1)) + K·log K/log n terms are K-smooth, and ω_{>K}(Δ_K(n)) ≥ K − (1+o(1))·π(K) | standard (Legendre valuations) | each prime > K divides at most one term.
- Lower bounds ω(Δ_K(n)) ≥ π(K) + c·π(K) for n > K, and Grimm-type distinct-prime results | Ramachandra–Shorey–Tijdeman; Laishram–Shorey (recalled, verify) | Baker / valuation methods. These are far below the K·L2/L3 needed.
- Almost-prime tuples: for fixed K, infinitely many n have every n+k (k ≤ K) equal to (K-smooth)·P_R with R ≪ K·log K | Halberstam–Richert; Diamond–Halberstam–Richert; Maynard (uniform for K ≤ (log x)^c) | weighted sieve.
- Jacobsthal function: j(P(z)) ≪ z²·log² z | Iwaniec | sieve. This is the best "every interval" tool, and it is location-independent.
- Related Erdős problems #248, #679, #890 (consecutive-shift statistics of ω). The exact statements and status are recalled only; verify before citing. #679 is a k < n, (1+ε)-type cousin of this problem.

=== BARRIERS
- **Small-prime (CRT) barrier, c₀ = 9·w(P₉+2) ≈ 1.38401.**
  - Defeats: any argument using only n mod p for p ≤ Z, because n ≡ −2 (mod P(Z)) is consistent with every such constraint.
  - Does not rule out: arguments that use primes larger than the window.
- **Bounded-window (one-large-prime) barrier, c₁ ≈ 1.584–1.586.**
  - Defeats: any argument looking only at k ≤ K with K fixed. Under Dickson, n+k = s_k·(prime) for all k ≤ K infinitely often, and heuristically even for K up to about log n/L2.
  - Does not rule out: windows K ≥ (log n)^{1+ε}, where such tuples heuristically do not exist.
- **Scale (large-deviation) barrier.**
  - Defeats: all methods at scales k = n^θ, or more generally log k ≫ L2·L3. Exponential sums over primes (Σ_{p∼P} e(hn/p), Vinogradov–Korobov) and short-interval results of length x^θ cap at C ≤ 1, since high-ω integers have density k^{−C}.
  - Consequence: all the gain lives at polylog scales, log k ≍ L2.
  - Does not rule out: polylog-scale arguments.
- **Local-plus-size consistency barrier.**
  - The pattern n+k = s_k·(single prime) for all k ≤ K satisfies every congruence condition mod primes ≤ K, every valuation identity (Legendre, Kummer) and every archimedean size bound (∏ ≥ n^K).
  - Defeats: purely elementary valuation/size arguments, including Sylvester–Erdős–Selfridge style. They cannot even prove ω_{>K}(Δ_K(n)) ≥ (1+δ)K.
  - Does not rule out: arguments using the actual distribution of primes.
- **Archimedean barrier.**
  - n mod p is free for p ≲ log n (CRT within size n), so the adversary can make the window miss every prime in (K, log n].
  - Defeats: any residue-only argument. A proof must use n ≤ N against primes in (log n, (log n)^{O(1)}] in a way that sees size.
- **Level / dimension barrier for counting.**
  - The window statistic is a K-dimensional sieve. The fundamental lemma needs z ≤ N^{1/(cK·log K)}, and Λ² bounds become trivial once K > e·log D. The large sieve gives at best (N+Q²)/J with J ≤ Q^{1+o(1)}.
  - Defeats: all moment and sieve methods as a route to zero exceptions. Their exceptional-set exponent caps at (log N)^{1−(C+o(1))/L3} (blackboard).
  - Does not rule out: almost-all statements with weaker exceptional sets, or non-counting arguments.
- **Parity.**
  - The sieve cannot tell n+k = s·q from s·q₁q₂ (q's large).
  - Defeats: any sieve proof that some window term has ≥ 2 large primes. That is exactly what beating c₁ requires.
- **Individual short intervals.**
  - Even "every interval of length (log x)^A contains a squarefree number" is open (best known: x^{1/5+ε}, Filaseta–Trifonov).
  - Defeats: hopes of a cheap deterministic statement about multiplicative structure in polylog intervals.

=== CORE
For every C and all large n, some k ≤ (log n)^{A(C)} must have ω(n+k) ≥ C·log k/loglog k.

A crisp sufficient form (proved by pigeonhole and the definition of w; nearly necessary): there are A and ψ(n) → ∞ such that every interval (n, n+(log n)^A] contains an m with ω(m) ≥ ψ(n)·L2/L3. Then F(n) ≥ (ψ/A)(1 − o(1)).

Equivalently, at the binomial level: no n admits a run of (log n)^A consecutive integers each having at most O(L2/L3) prime factors (L2/L3 is far below the normal order L2).

Why it is hard:
- It is a statement about every individual polylog-length interval.
- Small primes cannot do it (c₀ barrier).
- Bounded windows cannot do it (c₁ barrier, via Dickson).
- Large scales cannot do it (density barrier).
- Elementary valuations cannot do it (local-plus-size barrier).
- Counting cannot certify zero exceptions (level/dimension barrier).
- Even forcing two large primes in one term hits parity.
- The analogous squarefree-in-polylog-interval question is open.

Expect the full problem to remain out of reach. The realistic wins are exceptional-set exponents, structure, conditional proofs, and barrier theorems.

=== TARGET T1
TYPE: QUANT
STATEMENT: For each C > 0 there is δ(C) > 0 with #{n ≤ N : F(n) < C} ≤ N^{1−δ(C)} for N ≥ N₀(C).
BEYOND: Improves N·exp(−(log N)^{1−(C+o(1))/L3}) (blackboard) to a power saving. That bound is the provable limit of K-dimensional sieving with K < log N, so a new input is required, for example a large-sieve inequality exploiting that exceptional n fail at every scale k simultaneously.
VALUE: It is the first counting result that crosses the K ≈ log N dimension wall. It shows the wall is not intrinsic, and it is the regime where the exceptional set heuristically becomes empty.
SIGNIFICANCE: 2
TEST: Sieve-compute E_C(N) = {n ≤ N : max_{16≤k≤10⁴} ω(n+k)w(k) < C} for N ≤ 10¹⁰ and C ∈ [1.6, 2.2]. Fit log|E_C(N)|/log N against log log N.

=== TARGET T2
TYPE: QUANT
STATEMENT: There is δ > 0 with liminf_{n→∞} F(n) ≥ 1.587 + δ. Note c₁ ≤ 6·w(2312) ≈ 1.586 under Dickson for bounded windows.
BEYOND: The known liminf ≥ 1.58407 is sharp for bounded windows. Exceeding it requires excluding (smooth)·(prime) patterns of length (log n)^{1+ε} for every n. This is a reach target, not a weeks target.
VALUE: It would be the first unconditional use of growing windows: a parity-type breakthrough on the actual obstruction.
SIGNIFICANCE: 3
TEST: For n ≤ 10¹² ending long runs of (smooth)·(prime) integers, compute the minimal window K needed to exceed 1.6. Check K ≈ log n/L2.

=== TARGET T3
TYPE: STRUCTURE
STATEMENT: For almost all n (density 1), the maximum defining F(n) is attained at k = 15 and F(n) = ω(n+15)·w(15). Consequently (F(n)/w(15) − L2)/√L2 converges in distribution to N(0,1), and F(n) ~ L2/e in density.
BEYOND: Only the lower bound F ≥ ω(n+15)w(15) and the L3-type almost-all bounds are known; the blackboard pictured typical F as about L3, which is wrong. The proof:
- Use w(15) > w(k) for k ≠ 15, with gap at least 7·10⁻⁵, which beats √L2 fluctuations once L2 ≫ 10⁸.
- Union-bound large deviations of ω(n+k) over k ≤ e^{√L2}.
- Use Sathe–Selberg tails for √L2-scale and larger k.
- Use the maximal order of ω for k ≥ n^δ.
VALUE: Separates the two regimes cleanly: typical F ≍ L2, worst case ≍ L3. Exceptional sets must be measured against L3, not L2.
SIGNIFICANCE: 1
TEST: Compute the argmax of k ↦ ω(n+k)w(k) for random n ≈ 10^{18}. Expect a spread over k ∈ {13..17} at feasible sizes, because the w-gaps are of order 10⁻⁴.

=== TARGET T4
TYPE: STRUCTURE
STATEMENT: Let n ≥ n₀(C) with F(n) < C. Then:
- (a) Propagation: for 0 ≤ j ≤ J, F(n+j) < C·w(15)/w(J+16)·(1+o(1)). So one exception spawns an interval of length J of C′-exceptions, with C′ ≍ C·log J/loglog J.
- (b) For every K ∈ [K₀, (log n)^{3}], at least c·K/log K indices k ≤ K have n+k free of primes ≤ K^{1/3} with ω(n+k) ≤ C·log K/loglog K. Hence n+k has a prime factor ≥ n^{loglog K/(2C·log K)}.
- (c) #{p ∈ (K, z] : p | Δ_K(n)} ≤ C·K·log K/loglog K for all z.
BEYOND: No structural description of counterexamples is recorded. Part (b) uses the β-sieve lower bound uniformly in the interval, (a) uses the definition, and (c) uses that each p > K divides one term.
VALUE: Pins the adversary to "long rough almost-prime runs plus CRT avoidance of medium primes", the exact object any proof must exclude. Part (a) converts all-n statements into Banach-density statements.
SIGNIFICANCE: 1
TEST: For the n ≤ 10¹⁰ minimizing max_{k≤10⁴} ω(n+k)w(k), verify that (b) and (c) hold with room to spare.

=== TARGET T5
TYPE: SPECIAL
STATEMENT: Uniformly in x ≥ 1, for h ≥ h₀(C, ε): #{n ∈ (x, x+h] : F(n) < C} ≤ h·exp(−(log h)^{1−ε}). Hence F(n) → ∞ outside a set of upper Banach density zero.
BEYOND: Known exceptional bounds are for initial segments [1, N] only. All sieve error terms depend on moduli at most h^{1/2}, not on x, so the bound is location-uniform.
VALUE: Combined with T4(a), it reduces CORE to making the short-interval count fall below J on intervals of length J. This isolates exactly which strengthening of sieve uniformity would suffice.
SIGNIFICANCE: 1
TEST: Compute exception counts in random windows (x, x+10⁶] for x ∈ {10¹², 10¹⁵, 10¹⁸}. Check that they are independent of x.

=== TARGET T6
TYPE: CONDITIONAL
STATEMENT: Assume the uniform Bateman–Horn / Hardy–Littlewood upper bound for almost-prime windows:
- there is an absolute B such that for x ≥ B, 2 ≤ K ≤ (log x)³ and 0 ≤ r ≤ L2(x),
- #{n ≤ x : ω(n+k) ≤ r for all 16 ≤ k ≤ K} ≤ x·(B^{r+1}·log K·L2(x)^r / (r!·log x))^{K−15}.

Then F(n) → ∞; in fact F(n) ≥ (1/2 − o(1))·L3(n).
BEYOND: No conditional proof is known. Dickson-type hypotheses have only been used in the opposite direction, to build bad bounded windows.
VALUE: Gives the full statement under a standard-shape tuple conjecture via a one-line union bound. Take K = (log x)², r = 2C·L2/L3; then B^r·L2^r/r! = (log x)^{o(1)}, so the count is below 1. It also shows exactly which uniformity (K up to (log x)^{1+ε}, count below 1) is needed.
SIGNIFICANCE: 1
TEST: Check the hypothesis numerically for K ≤ 30 and x ≤ 10¹⁰ against actual counts.

=== TARGET T7
TYPE: REDUCTION
STATEMENT: Let K = ⌊(log n)²⌋ and ν(n) = #{p > K prime : p | C(n+K, K)}. If ν(n)·L3/(K·L2) → ∞, then F(n) → ∞.
Proof:
- Each p > K divides at most one n+k, so Σ_{16≤k≤K} ω_{>K}(n+k) ≥ ν(n) − 15·log(2n)/log K.
- By pigeonhole, some k ∈ [16, K] has ω(n+k) ≥ ν/K − o(1).
- Since w(k) ≥ w(K) = (log 2 + L3)/(2·L2), we get F(n) ≥ (ν·L3)/(2K·L2)·(1 − o(1)).
BEYOND: Known bounds give only ν ≥ K − (1+o(1))π(K) (Sylvester–Erdős). The hypothesis is about the radical of a single binomial coefficient. It is not equivalent to CORE, because it asks for many large primes on average rather than one rich term.
VALUE: Moves CORE onto ω(C(n+K, K)), where Kummer-carry and Diophantine literature (Ramachandra–Shorey–Tijdeman, Laishram–Shorey) applies. The intermediate goal ν ≥ (1+δ)K already crosses the local-plus-size barrier.
SIGNIFICANCE: 1
TEST: Compute ν(n)/K for n ≤ 10¹² with K = ⌊(log n)²⌋. Report the minimum ratio and compare it with L2.

=== TARGET T8
TYPE: ANALOGUE
STATEMENT: Random-CRT model:
- small primes p ≤ (log N)^{1/2} act deterministically through n mod p;
- each prime p > (log N)^{1/2} divides n+k independently with probability 1/p, conditioned on the Kummer/CRT constraint that p hits at most one term of each window of length < p.

Prove that, almost surely, min_{N<n≤2N} F(n) = (1+o(1))·L3(N).
BEYOND: Only heuristic order-of-magnitude claims exist (blackboard). No model computation pins down the worst-case constant.
VALUE: Gives the true conjectural rate and the right exponent targets for T1. It also shows which window lengths (about log N/L2 controlled, (log N)^{1+ε} uncontrolled) a real proof must handle.
SIGNIFICANCE: 1
TEST: Monte-Carlo the model for N = 10^{20}–10^{60} and compare with exact minima of F over windows for n ≤ 10^{10}.

=== TARGET T9
TYPE: NEGATIVE
STATEMENT: Unconditionally, there are infinitely many n with F(n) ≤ B·L2·L4/L3, where L4 = log L3. In particular liminf F(n)/loglog n = 0, so the normal order L2/e is not a lower bound for all n.
BEYOND: Nothing upper-bounds liminf F unconditionally. Method:
- Fix n ≡ −2 (mod P(z)).
- Use Maynard-uniform weighted-sieve weights making every n+k, k ≤ K₀ = L2/(log L2)², equal to (smooth)·P_R with R ≪ K₀·log K₀.
- Control ω(n+k) for k > K₀ on the weighted set via sieve-weighted large-deviation (moment) bounds, uniformly for k ≤ x^δ.
VALUE: Rules out the natural strengthening "F ≫ L2 always" and calibrates where the true minimum lies (conjecturally L3).
SIGNIFICANCE: 1
TEST: Exhibit numerically small values of F(n)/L2 among n ≤ 10^{12} with n ≡ −2 (mod P(23)) and n+15 prime.

=== TARGET T10
TYPE: NEGATIVE
STATEMENT: Barrier theorem. Let D ≤ N and K ≥ e·log D. Any Λ²- or β-sieve majorant of 1_{S} for S = {n ≤ N : each n+k (k ≤ K) has at most r prime factors in (K, z]}, built from divisors d | Δ_K(n) with d ≤ D, has total mass ≥ N^{1−o(1)}. Consequently any upper-bound sieve or moment method on the window statistic gives exceptional-set exponents no better than (log N)^{1−(C−o(1))/L3}.
BEYOND: The blackboard only conjectures this limitation (evidence only). Proving it needs Selberg's optimality of Λ² plus G(D) ≤ (e·log D/K)^K·(log K)^{O(K)}, together with Ankeny–Onishi-type high-dimension sieve limits.
VALUE: Certifies that T1 requires a non-sieve ingredient, and stops wasted effort on moment refinements.
SIGNIFICANCE: 2
TEST: Numerically optimize Λ² weights for K ≤ 20, D ≤ 10⁶ and compare the bound with N·V(z).

=== ANGLE A1
TECHNIQUE: Multi-scale high-dimensional sieve with profile-adapted Rankin weights (refinement of the known window-total method).
IDEA: Exceptional n are anomalous at every scale k ∈ [16, K], with thresholds r_k = C·log k/loglog k that are tiny for small k. Build one sieve over all primes in (16, z]. Each prime gets weights tuned to which k it hits, so that the λ > R constraint is only needed scale by scale. Aim for exponent (log N)^{1−o(1)} independent of C, then push toward T1 by combining with a dual large-sieve inequality for the vector (n mod p)_p.
BARRIERS: It must beat the dimension barrier (T10). The only hope is that heterogeneous r_k reduce the effective dimension; if T10 is proved, this angle is capped at exp(−(log N)^{1−o(1)}).
FIRST STEP: Prove #{n ≤ N : ω(n+k) ≤ r_k for all 16 ≤ k ≤ K} ≤ N·∏_k P(ω ≤ r_k)·e^{O(K)} for K ≤ log N/(L2)³, and compute the resulting exponent explicitly.

=== ANGLE A2
TECHNIQUE: Propagation plus location-uniform Banach-density bounds (new combination; not used in KNOWN).
IDEA: By T4(a), one C-exception at n forces all of [n, n+J] to be C′-exceptions with C′ ≍ C·log J/loglog J. Count C′-exceptions in intervals of length J with the location-uniform sieve (T5). A contradiction needs the uniform bound to fall below J. So find J where the C′-threshold equals c·L2(n) (still below normal order) and use the full L2-strength lower tail ω ≤ c·L2 in J consecutive integers.
BARRIERS: It hits the individual-interval barrier at J ≈ (log n)^{L3/C}. The gain over plain counting is that the target is now a dense-run statement: J consecutive integers all with ω ≤ c·L2, at density (log n)^{−1+c·log(e/c)} each. Runs of that set are a Jacobsthal-type object.
FIRST STEP: Prove the propagation lemma with explicit constants. Then prove: every interval of length (log x)^{A} contains an m with ω(m) ≥ c·L2 for some c > 0, at least for x in a set of logarithmic density 1.

=== ANGLE A3
TECHNIQUE: Maynard–Tao weights with sieve-weighted large deviations (not used in KNOWN).
IDEA: Use GPY/Maynard weights as a probe of the adversary rather than as a constructor. Bound from above the weighted mass of n whose windows of length K ≈ (log n)^{θ} are entirely almost-prime. Compare with the unweighted mass to find how long such runs can be, then extrapolate the maximal adversarial window length K*(n) toward the threshold needed for T2.
BARRIERS: Parity blocks proving "≥ 2 large primes" directly. This angle instead bounds the frequency of long runs, which is a counting question, but on a structured subset of density far below the level barrier.
FIRST STEP: Prove T9. As a by-product, obtain uniform-in-K (K ≤ (log x)^{c}) large-deviation bounds for ω(n+k) on Maynard-weighted sets.

=== ANGLE A4
TECHNIQUE: Kummer carries and Diophantine digit theory (Baker / Stewart-type bounds for digits in several bases; not used in KNOWN).
IDEA: Via T7, p | C(n+K, K) for p ∈ (K, z] iff adding K to n carries in base p, i.e. n mod p ≥ p − K. Higher powers p^j | C(n+K, K) count carries in higher digits. Exceptional n must have "carry-free last digits" in most bases p ∈ (K, z]. Seek a theorem that an integer n ≤ N cannot be carry-free in ≥ (1 − η)·π(z) bases for z ≥ (log N)^{1+ε}, using the simultaneous structure of the base-p expansions of a single n (linear forms in logs control n through leading digits).
BARRIERS: It must beat the local-plus-size barrier. Baker-type input is global (it sees n exactly, not only residues and size), so the barrier does not apply formally.
FIRST STEP: For primes p ∈ (P, 2P], P = (log N)², bound #{n ≤ N : n mod p < p − K for all but m of these p} via the larger sieve (Gallagher). Determine whether it beats the large-sieve value N^{1/2}.

=== ANGLE A5
TECHNIQUE: Function-field model with monodromy and Chebotarev (Katz, Sawin–Shusterman, Bank–Bary-Soroker–Rosenzweig; not used in KNOWN).
IDEA: In F_q[t], let F_q(f) = max_{d, deg g<d} ω(f+g)·log(d·log q)/(d·log q). Large-q equidistribution of factorization types in the "interval" {f+g} is uniform in f. Use it to test the exceptional-set question (T1 analogue: is #{f : F_q(f) < C} ≤ q^{(1−δ)n}?) and to see whether monodromy of the window product ∏_g (f+g) supplies the missing "global prime" input.
BARRIERS: For fixed n and q → ∞, F_q is small. So the meaningful regime is q fixed and n → ∞, where the same level barrier reappears; Deligne-level square-root cancellation is the hoped-for extra input.
FIRST STEP: Compute min_f F_q(f) exactly for q ∈ {2, 3}, n ≤ 28. Prove that the Galois group of ∏_{deg g<d}(f+g) over F_q(coefficients of f) is the full wreath-type product for d ≤ c·log n.

=== ANGLE A6
TECHNIQUE: Conditional route with hypothesis-weakening (uniform Bateman–Horn, then Montgomery-type short-interval large sieve).
IDEA: First make T6 rigorous. Then weaken the hypothesis:
- require the tuple bound only for a positive proportion of k ≤ K and K = (log x)^{1+ε};
- derive that from a conjectural large-sieve inequality in short intervals with error O(1) rather than O(Q²), i.e. a "large sieve for intervals of length (log x)^{A}" conjecture;
- deduce F → ∞ from the weakest such statement.
BARRIERS: Conditional, so no barrier applies directly. The aim is to locate the weakest standard-looking hypothesis, and to check it is not refuted by Friedlander–Granville-type uniformity failures.
FIRST STEP: Prove T6 in full. Then show the hypothesis can be restricted to windows of n ≡ −2 (mod P(√K)), a single admissible profile, without losing the conclusion.

## Meta-review

=== STATE
**Validated this round (all rated routine by novelty review):**
- [r1s1/C1] F(n) ~ w(15)·L2 for almost all n. The exceptional set for |F(n) − w(15)L2| > εL2 is O(N(log N)^{−c(ε)}), which is stronger than the stated O(N/L2). The lower bound comes from the one-shift normal order; the upper bound is a union over k of Hardy–Ramanujan tails with λ_k = (1/e+ε)/w(k) > 1.
- [r1s1/C2] #{n ≤ N : F(n) < εL2} ≤ N(log N)^{−A(ε)}(L2)^{O_ε(1)}, where A(ε) = Σ_{k∈S_ε} Q(ε/w(k)) and S_ε = {k ≥ 3 : w(k) > ε} is finite. This is the joint lower-tail Rankin bound over the finite set of useful shifts.
- [r1s2/C1] Fix θ > 0 and a < 1/(1+θ). Then #{n ≤ N : F(n) < θL3} ≤ N·exp(−(log N)^a).
  - This improves the blackboard exponent from 1 − θ′ to 1/(1+θ).
  - By-product (A): outside N·exp(−L^{1−ε}), some k ∈ (J/2, J] with J = L^{1−ε} has ω(n+k) ≥ cεL2.
- [r1s3/C1] F(n) ≥ 6·w(2314) = 1.585652 for all n outside E, where E = {n : some n+k (k ≤ 2314) is 11-smooth and divisible by 2310}. Also #(E ∩ [0,N]) = O((log N)^5).
  - This lies within 10⁻⁴ of the conditional bounded-window ceiling 6w(2312) = 1.585745.
  - On the complement of a polylog-sparse set it supersedes the unverified blackboard liminf 7w(30033) = 1.584069.
- [r1s4/C1] Correction to an internal barrier claim. Take K = (log N)^A, sift by primes in (K, N^{1/6}], use Selberg Λ² at level D = N^{1/3}, and take r = 0 (no prime in the range). The majorant has mass N^{1−(A−1)/(6A)+o(1)}, a power saving. So "K ≥ e·log D ⇒ Λ² is trivial" is false.
- [r1s4/C2] Main-term floor for any linear majorant of level D in one window of length K: M ≥ ∏_{K<p≤D}(1 − K/p) ≥ exp(−K·log(log D/log 2K) − cK). Reaching N·exp(−(log N)^β) therefore needs K ≥ (log N)^β/(L2+O(1)).
  - The floor is below 1/N once K ≳ log N/L2.
  - So the floor itself is not what blocks zero exceptions; the error terms and level are.

**Best unvalidated ideas:**
- [r1s3/C3] F(n) ≥ 6w(2312) off E* = {some n+k, k ≤ 4000, is 4000-smooth}, with #E* ≤ (log N)^{O(1)}.
  - Broken only because the SAT/UNSAT step for the case k₀ ∈ {3,4} has no certificate and no encoding audit. The logic is otherwise unchallenged.
- [r1s3/C2] Under Dickson, infinitely many n ∉ E have bounded-window max ≤ 6w(2312).
  - The gap is mechanical: take K ≥ 2314 WLOG (the max is monotone in K), and handle k = 0, 1 and the range (K, 2314].
  - The adversary confirmed the admissible system and the numerics: 7w(30032) = 1.5840 and 5w(212) = 1.5666 are both below 6w(2312).
- [r1s1/C3] Profile-adapted Lemma U (heterogeneous r_k, z_k, y_k) gains only constants; its exceptional exponent stays at (log N)^{1−(C−o(1))/L3}. This is a plausible barrier statement, not checked.
- [r1s2/C2] Shifting n by up to J costs a factor Φ(J) = (w(15)+o(1))·log J/loglog J. Hence "one exception forces a run of exceptions" gives nothing beyond a direct witness. Not checked.
- New observation from the r1s3 cleanup: Størmer/S-unit finiteness implies that for n large, at most one term of [n, n+4000] is 4000-smooth.
  - This is a non-counting, every-n tool.
  - It converts the polylog exceptional sets E and E* into "finite", provided the window argument tolerates one smooth term.

=== LESSONS
**What failed and why.**
- All validated results are routine. They are almost-all or exceptional-set statements and saturate exactly as the level/dimension barrier predicts.
- r1s3/C3 failed on rigour, not mathematics: a computer step was asserted without a checkable certificate (DRAT/LRAT) or a tabulated bound table b_k.
- r1s3/C2 failed on bookkeeping at the window edge.

**Which barriers bit.**
- The c₁ barrier is now essentially reached from below: 6w(2314) holds off a sparse set, and the ceiling is 6w(2312). Nothing beyond c₁ is possible with bounded windows.
- r1s4 sharpened our understanding of the level/dimension barrier.
  - For the r = 0 event, Λ² gives a genuine power saving at K = (log N)^A, so the "Λ² trivial" barrier was overstated.
  - The real obstruction to a power saving for F < C is the Rankin cost t^{Kr} for allowing r = CA·L2/L3 prime factors per term. Heuristically this cost (≫ log N in the exponent) swamps the dimension saving N^{c}.
  - Nobody has computed this trade-off with per-term majorants rather than a Rankin weight on the window total.
- Counting can never reach zero exceptions; r1s4/C2 locates the reason in error terms and level, not in the main term.
- Parity and the individual-interval barriers were untouched.

**Most alive angles.**
- (i) Determine the bounded-window constant exactly and unconditionally for all large n: a SAT certificate plus Størmer finiteness. This is a complete theorem with a matching conditional upper bound (Dickson), which is as good as bounded windows can ever give.
- (ii) Use the r = 0 power saving as a lever. Either it extends to r ≈ CA·L2/L3, giving exceptional set N^{1−c(C)} for every fixed C, which beats the map's stated cap and would be significant; or it doesn't, and we get a sharp barrier theorem.
- (iii) A clean conditional proof of CORE. r1s4/C2 shows the main-term floor drops below 1/N already at K ≍ log N/L2, so a natural uniform tuple upper-bound hypothesis might suffice.

=== NEXT
1. **Repair r1s3/C3 + C2 into a sharp bounded-window theorem.** Goal: F(n) ≥ 6w(2312) for all sufficiently large n, unconditionally, and under Dickson no bounded window exceeds 6w(2312). Technique: certified SAT plus S-unit finiteness.
   - First step: regenerate the CNF for window [3,4000] with primes 13..4000 and an explicit, audited table b_k = t_k − ω_{≤11}(k−k₀). Produce a DRAT proof checked by drat-trim.
   - Then rerun with one term allowed to be 4000-smooth at each position. Justify the "at most one smooth term" reduction by Størmer/Mahler finiteness of pairs of 4000-smooth integers at distance ≤ 4000.
   - Fix C2 by taking K ≥ 2314 WLOG and treating k = 0, 1 explicitly.
2. **Combine r1s4/C1 (Λ² power saving at r = 0) with Lemma U / r1s2/C1.** Decide whether #{n ≤ N : F(n) < C} ≤ N^{1−c(C)} holds for each fixed C.
   - Technique: Selberg Λ² in dimension K = (log N)^A, using per-term almost-prime majorants for 1_{ω_{(K,y]}(n+k) ≤ r} with r = CA·L2/L3, rather than a Rankin weight on the window total.
   - First step: write the per-term majorant as Σ_{j≤r} (Λ²-weights on d | n+k with ω(d) ≤ j). Compute the resulting Euler product, effective dimension and level loss. Compare the r-cost against the N^{(A−1)/(6A)} saving.
   - Output either a power-saving theorem or a rigorous barrier theorem stating that per-term cost ≥ dimension saving.
3. **Attack CORE conditionally.** Prove F(n) → ∞ under an explicit uniform almost-prime-tuple upper bound "Hypothesis U".
   - Hypothesis U: for K ≤ (log x)², the number of n ∈ [x, 2x] with each a_i·n + b_i having ≤ r prime factors in (K, x^{1/10}] is ≤ x·∏_p(1 − ν(p)/p)·(c·r·L2)^{rK}, with no additive error term.
   - First step: check U against Hensley–Richards and Maier-matrix obstructions, so it is not refuted.
   - Then run the union bound over cofactor profiles s_k (weighted by Σ 1/s over K-smooth s, ≈ e^γ·log K). Show the total is < 1 on [x, 2x] once K = C′·log x/L2 for C′ large enough relative to C.
4. **Push r1s2/C1 to its natural limit.** Prove #{n ≤ N : F(n) < θL3} ≤ N·exp(−(log N)^{1−o(1)}) for every fixed θ, and show the exponent is optimal under a Dickson/almost-prime-tuple heuristic.
   - Technique: Brun/Bonferroni lower-tail moments over several dyadic windows (K/2, K], K = L^{1−ε_j}, run jointly. Pair this with an almost-prime-tuple construction (Halberstam–Richert weights) giving a heuristic lower bound for the exceptional count.
   - First step: redo the r1s2/C1 optimisation with the witness scale log k = (1−ε)·L2 treated as a free parameter. Locate where the loss 1/(1+θ) enters and whether summing scales removes it.

## Deep dive

GOAL: **Theorem to prove (unconditional).** Write L = log N, L2 = log L, L3 = log L2, L4 = log L3, and w(k) = loglog k / log k. Use the convention that F(n) = max over k ≥ 3, so w(k) is defined, and state this explicitly.

There is an absolute constant C such that, for all large N,

  #{ n ≤ N : F(n) ≤ C · L2·L4/L3 } ≥ N · exp(−O(L2²·L4/L3)) = N^{1−o(1)}.

**Corollaries.**
- F(n) ≪ (log log n)·(log log log log n)/(log log log n) for infinitely many n. In particular liminf F(n)/log log n = 0.
- Almost all n have F(n) ~ w(15)·log log n (r1s1/C1). So F is genuinely smaller than its normal order on a dense-ish subsequence.
- For every threshold between C·L2·L4/L3 and (w(15) − ε)·L2, the exceptional set {F(n) < threshold} has size N^{1−o(1)}. This gives the first lower bound for the exceptional sets whose upper bounds are r1s1/C2 and r1s2/C1.

**Secondary deliverable (the method's own ceiling).** Any argument that controls ω(n+k) only by sieving a window of shifts at level ≤ N cannot certify F(n) = o(L2·L4/L3). So the result is sharp for the method.

**Why an expert would rate it 2.** The problem is two-sided in spirit: F(n) → ∞ is asked, but nothing is known about how slowly F can grow.

Currently the frontier pins liminf F only between 1.584 (blackboard, informal) and the normal order w(15)·L2. This theorem gives:
- the first unconditional upper bound for liminf F below the normal order, together with an N^{1−o(1)} count;
- a matching method-barrier.

Combined with the heuristic liminf F/L3 = 1/log 2 (r2s3/C2), it narrows the true order of the minimal growth to [constant, L2·L4/L3]. It also certifies that every almost-all statement about F has a genuine threshold.

This is a structural theorem about Erdős's function, not a constant inside a known ceiling. It does not prove F(n) → ∞, and the write-up must say so plainly.
