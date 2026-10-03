## Result
**C1 (CONDITIONAL, PROVED).** Assume Hypothesis U(c) for one fixed c ∈ (0,1]. U(c) says the J events "n+h has more than R prime factors in (K,√x]", h ∈ (K/2,K], are approximately independent, up to an exponent c. Then F(n) ≥ (1/log 2 − ε)·logloglog n for all n ≥ n₀(ε,c). In particular F(n) → ∞. The only unconditional input is an elementary lower bound for one term's upper tail (Lemma 1).

**C2 (CONJECTURED, with mechanism).** The constant is sharp: under the Kubilius/Poisson model, liminf F(n)/L3(n) = 1/log 2.

**C3 (CONJECTURED, with mechanism).** For fixed θ > 1/log 2, #{n ≤ N : F(n) < θL3} = N·exp(−(log N)^{e^{1/θ}−1+o(1)}). For θ < 1/log 2 the set is finite. So an exceptional-set exponent 1 − o(1) for every fixed θ (r2s4's target) is false under the model once θ > 1/log 2 = 1.4427.

Why new: KNOWN has only almost-all bounds and bounded-window constants. No conditional proof of F → ∞ is on the map. C1 also pins down the window length needed: (log n)^{2 log 2 + ε}. It gives ω(m) ≥ 2·loglog n somewhere in every such window, which is far beyond CORE's L2/L3 scale.

## Claims

### C1
STATEMENT. Notation:
- L = log x, L2 = log L, L3 = log L2, and w(k) = loglog k/log k.
- For an integer K ≥ 2, H_K = (K/2,K] ∩ ℤ and J = |H_K| ≥ K/2.
- ω*(m) = #{p prime : p | m, K < p ≤ √x}. This depends on x and K.
- E(x,K,R) = #{n ∈ ℤ∩(x,2x] : ω*(n+h) ≤ R for all h ∈ H_K}.
- q_h(x,K,R) = x^{-1}·#{n ∈ ℤ∩(x,2x] : ω*(n+h) > R}.

**Hypothesis U(c)**, with c ∈ (0,1] fixed. There is x₀ such that for all x ≥ x₀, all integers K ∈ [32, L²] and all integers R ≥ 0,
  E(x,K,R) ≤ x·∏_{h∈H_K} (1 − q_h)^c.
(The case c = 1 is exact independence of the J single-term events. Only the case R = ⌊2L2⌋, K = ⌊L^a⌋ with a = 2log2+ε is used.)

**Theorem.** Assume U(c). Then for every ε > 0 there is n₀ such that F(n) ≥ (1/log 2 − ε)·logloglog n for all n ≥ n₀. Hence F(n) → ∞.

STATUS: PROVED (conditional on U(c)).
TYPE: CONDITIONAL

BEYOND: KNOWN contains no conditional proof of F → ∞. The map's barriers are not violated:
- U is a statement about primes in (K,√x] with K = L^{1.39} > log x. For n ≤ 2x these primes cannot be steered by CRT, so U is consistent with the c₀ and archimedean barriers.
- U uses windows of length L^{1.39+ε} ≫ log n, so it is consistent with the c₁/Dickson barrier.
- It is a pointwise statement only where its bound is < 1; elsewhere it is a counting statement.

PROOF.

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

### C2
STATEMENT: liminf_{n→∞} F(n)/logloglog n = 1/log 2.
STATUS: CONJECTURED. The ≥ direction is PROVED under U(c) (C1).
TYPE: CONDITIONAL / OTHER
BEYOND: This is the first predicted exact growth rate of min F. KNOWN has only O(1) constants.
EVIDENCE/MECHANISM:
- Model ω(n+k) for n+k ~ x as Poisson(L2), independent over k. Large primes are not shared; small primes p ≤ L shift each term by only O(L3), which changes probabilities by factors (L2)^{O(1)}. The adversarial CRT choice n ≡ −2 mod P(L) also only affects O(L3).
- For k ~ L^b, F < θL3 requires ω(n+k) < θbL2.
  - For θb < 1 (lower tail), the cost is ≈ L^b·L2·I(θb) per range. The total cost is L^{1/θ+o(1)}.
  - For θb > 1 (upper tail), the expected number of violators is Σ L^{b−I(θb)}, with sup_b (b − I(θb)) = e^{1/θ} − 1, attained at θb = e^{1/θ}. Checked numerically for θ ∈ {1, 1.2, 1/log2, 2, 3, 5, 10}.
- So −log P(F(n) < θL3) = L^{max(1/θ, e^{1/θ}−1)+o(1)} = L^{e^{1/θ}−1+o(1)}, since e^u − 1 > u.
- This exponent exceeds 1 iff θ < 1/log 2. Therefore min_{x<n≤2x} F(n) ≈ (1/log 2)·L3.
- C1's proof is exactly the rigorous upper-tail half of this computation.

### C3
STATEMENT: For fixed θ > 1/log 2, #{n ≤ N : F(n) < θ·L3(N)} = N·exp(−(log N)^{e^{1/θ}−1+o(1)}). For θ < 1/log 2 the set is finite.
STATUS: CONJECTURED (same model as C2).
TYPE: NEGATIVE (heuristic obstruction)
BEYOND:
- This predicts that the exceptional-set exponent cannot be 1 − o(1) for θ > 1/log 2. That is relevant to r2s4's target.
- It compares as follows with the rigorous r1s2/C1 exponent 1/(1+θ):
  - Model exponent e^{1/θ} − 1 > 1/θ > 1/(1+θ).
  - The lower-tail-only part of the model gives exactly 1/θ. This suggests r1s2's mechanism is the lower-tail one, and that the upper-tail ("one term with abnormally many factors") mechanism is where the extra gain lies.

## Data
check1.py (x = 2·10⁶, z = √x, H = (K/2,K], y = K). Counts E against the independence prediction x·p₁^J, where p₁ is the empirical single-term probability:

| K | R | E | x·p₁^J | ratio |
|---|---|---|---|---|
| 8 | 0 | 21651 | 27571 | 0.79 |
| 8 | 1 | 519991 | 547845 | 0.95 |
| 8 | 2 | 1154883 | 1173143 | 0.98 |
| 8 | 3 | 1922828 | 1923611 | 1.00 |
| 12 | 0 | 3805 | 6109 | 0.62 |
| 16 | 0 | 996 | 1780 | 0.56 |
| 16 | 3 | 1970604 | 1970765 | 1.00 |

- In every case E ≤ x·p₁^J. Here p₁ is the density over m ∈ (x,2x], used as a proxy for each 1 − q_h; the shift by h ≤ 16 is negligible. So the data are consistent with U(1). The tested K are below the hypothesis range K ≥ 32; this is only a plausibility check.
- With the Poisson P_R in place of the empirical p₁, the upper tail fails badly: c_eff = 0.14 at K = 16, R = 3. **So U must be stated with empirical single-term densities (as above), not with Poisson tails.**
- Rankin's inequality Σ_{r≤R} λ^r/r! ≤ (eλ/R)^R and Stirling's bound were verified on a grid (0 violations).

## Dead ends
- **Poisson-form hypothesis.** "E ≤ x·(B·P_R(λ))^J" is useless in the upper tail (B^J kills it). Its variant x·P_R^{cJ} is empirically false there (c_eff → 0), so we replaced it with empirical q_h.
- **Hypotheses counting n ≤ x instead of n ∈ (x,2x] are FALSE.** For example, n = 1 with H = [1,K], y = K, z = 2K: n+h < p for every p ∈ (K+1,2K]. The count is ≥ 1 while the main term is exp(−cK/log K) < 1/x. So a dyadic n-range is essential.
- **Reducing to the r = 0 sieve by pigeonhole over R+1 disjoint prime sets** loses (R+1)e^{−λ/(R+1)} against the Poisson e^{−λ}λ^R/R!. It only gives F ≥ c/(1+ε) < 1.
- **Reducing to AP-form sieve bounds** (force the ≤ R primes per term as congruences) needs a modulus z^{JR} ≫ x. That is impossible in the range J ≳ L/L2 that the main-term floor (r1s4/C2) requires.
