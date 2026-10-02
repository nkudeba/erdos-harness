# Literature library (papers dated before 2026-10-02; 6 paper(s))

Summaries of what each paper states, written by a model for this problem. Unverified: a summary can be wrong, and a paper's claim is not a Lean fact.

## Linear equations in primes (2010)
https://doi.org/10.4007/annals.2010.171.1753; full text: yes

**Verdict: the paper is mostly not relevant.** It counts finite prime configurations parametrised by affine-linear forms. It proves nothing about infinite sequences of primes, about growth rates such as q_n/n², or about consecutive gaps. Below are the only pieces that could plausibly serve as ingredients, for example for building long finite convex blocks of primes.

**Definitions**

- **Complexity (Def. 1.5).** Ψ has i-complexity ≤ s if "one can cover the t−1 forms {ψ_j : j ≠ i} by s+1 classes, such that ψ_i does not lie in the affine-linear span of any of these classes."
- **Lemma 1.6.** "this system has finite complexity if and only if no two of the ψ_i are affinely dependent. Furthermore, in this case the complexity of the system is less than or equal to t − dim(Ψ̇)." Proved by elementary linear algebra.

**Main results**

- **Main Theorem.** "Suppose that the inverse Gowers-norm conjecture GI(s) and the Möbius and nilsequences conjecture MN(s) are true for some finite s ≥ 1. Then the generalised Hardy-Littlewood conjecture is true for all systems of affine-linear forms of complexity at most s."
  - The conjecture is (1.7): Σ_{n∈K∩ℤ^d} Π Λ(ψ_i(n)) = β_∞ Π_p β_p + o(N^d), with β_∞ = vol_d(K ∩ Ψ^{-1}((ℝ⁺)^t)) and β_p = E_{n∈ℤ_p^d} Π Λ_{ℤ_p}(ψ_i(n)).
- **Corollary 1.7 (unconditional).** The conjecture holds for "all systems of affine-linear forms of complexity at most 2", in particular whenever "codim(Ψ̇(ℝ^d)) ≤ 2".
  - GI(2) and MN(2) were proved in the authors' earlier papers.
  - A note added in April 2008 says MN(s) is "fully resolved … for every s"; GI(s) for s ≥ 3 remains open per this text.
- **Corollary 1.9 (qualitative).** Assuming GI(s) and MN(s), if Ψ has complexity ≤ s, is solvable at every p, and is solvable at ∞ in an open convex cone K, then there are "infinitely many n ∈ K∩ℤ^d such that ψ_1(n),…,ψ_t(n) are all prime."
- **Lemma 1.3.** β_p = 1 + O(p^{-1}), and β_p = 1 + O(p^{-2}) if no two forms are affinely related. Proved by a probabilistic count mod p plus Bonferroni inequalities.

**Possible use (my observation, not stated in the paper)**

The finite pattern ψ_i(a,b,c) = a + bi + c·i(i−1)/2, for i = 0,…,k−1, is a block of k numbers with constant second difference c. Taking c ≥ 0 gives nondecreasing gaps. No two of these forms are parallel and dim Ψ̇ = 3, so by Lemma 1.6 the complexity is ≤ k−3.

- For k ≤ 5 the asymptotic count is therefore unconditional by Corollary 1.7.
- For larger k it is conditional on GI(k−3).
- Arithmetic progressions (Example 8) are the case c = 0. For k = 4 the count is (1+o(1)) S₁ N²/(4 log⁴N) with S₁ ≈ 0.4764.

This gives densities of finite convex prime blocks only. Nothing in the paper chains such blocks into an infinite sequence or controls n² growth.

**Method chain behind the Main Theorem**

1. Linear-algebra reduction to s-normal form (Lemma 4.4).
2. The W-trick.
3. An enveloping-sieve pseudorandom majorant ν (Prop. 6.4, via Selberg/Goldston–Yıldırım).
4. The generalised von Neumann theorem (Prop. 7.1, repeated Cauchy–Schwarz).
5. A transferred inverse theorem via Koopman–von Neumann decomposition (Props. 10.1, 10.3).
6. Orthogonality of Λ′_{b,W} − 1 to nilsequences (Prop. 10.2, via MN(s)).

The error terms are ineffective because of Siegel zeros; they become effective under GRH.

**Stated limitations and open questions near the problem**

- The "binary"/infinite-complexity case is excluded: any d = 1, t > 1 system, e.g. twin primes or (n, n+2). The paper says this is "probably well beyond the reach of current technology."
- Questions about consecutive primes, or polynomial patterns in a single variable, fall into that excluded regime.
- GI(s) for s ≥ 3 is stated as open.
- Chowla's conjecture for non-homogeneous polynomials is called "hopeless with current technology."

The paper states no question about convex sequences of primes or Richter-type bounds.

## Variants of the Selberg sieve, and bounded intervals containing many primes (2014)
https://doi.org/10.1186/s40687-014-0012-7; full text: abstract only

(No text or abstract was available, so this paper is cited, not summarised.)

## Bounded gaps between primes (2014)
https://doi.org/10.4007/annals.2014.179.3.7; full text: abstract only

# Summary: "Bounded gaps between primes" (2014-02-20)

**Only the abstract is available, and its main result is missing.** The abstract reads "It is proved that where pn is the n-th prime." The displayed formula was lost in extraction. I will not fill it in from memory, so the paper's actual theorem, and any constant in it, cannot be quoted from this text.

## What the text does say

1. **Main result.** Some statement about $p_n$, the $n$-th prime. Judging by the title it concerns gaps between consecutive primes, but the exact inequality is absent.
2. **Method.** "a refinement of the recent work of Goldston, Pintz and Yıldırım on the small gaps between consecutive primes." That is, a sieve-weight approach in the GPY framework.
3. **Key ingredient.** "a stronger version of the Bombieri-Vinogradov theorem that is applicable when the moduli are free from large prime divisors only, but it is adequate for our purpose."
   - This is an equidistribution estimate for primes in arithmetic progressions.
   - It is restricted to smooth moduli, i.e. moduli with no large prime factors.
   - No level of distribution, exponent or constant is given in the text.

No lemmas, explicit constructions or numerical constants appear. The abstract states no open questions.

## Relevance to the problem

**Not directly relevant, as far as this text shows.**

- **What the problem needs.** It asks about sequences of primes $q_1<q_2<\cdots$ whose gaps $q_{n+1}-q_n$ are non-decreasing, i.e. "convex" prime sequences. The question is whether such a sequence must have $q_n/n^2\to\infty$, improving on Richter's $\liminf q_n/n^2>0.352$. That question is about how slowly a sequence with non-decreasing gaps can grow while staying inside the primes. Answering it would need:
  - upper-bound or density information about primes in long, roughly arithmetic, slowly-growing-gap configurations; or
  - constructions of long such configurations.
- **What the paper offers.** It concerns *small* gaps between *consecutive* primes, and the problem's sequence is not made of consecutive primes. Small-gap results do not obviously constrain convex subsequences.

**Possibly tangential uses.** These are pointers to tools only, not claims about the answer.

- **Smooth-moduli Bombieri–Vinogradov.** A mathematician might ask whether this equidistribution input helps with counting primes in structured configurations, such as quadratic-like progressions.
- **GPY-type sieve weights.** The same question applies to the sieve machinery. Nothing in the text addresses this.

## Recommendation

Obtain the full statement of the main theorem, and of the Bombieri–Vinogradov variant, from a source dated before the cutoff before relying on this paper. Based on the abstract alone, treat it as background on prime distribution rather than as an ingredient for this problem.

## Primes in tuples I (2009)
https://doi.org/10.4007/annals.2009.170.819; full text: yes

**Overall verdict: the paper is essentially not relevant to this problem.**

GPY proves *existence* results: infinitely many short windows that contain at least two (or ν+1) primes. The problem asks how fast a prime sequence with non-decreasing gaps must grow. That needs constraints on many primes in prescribed configurations, typically upper-bound sieve or density information. The paper gives no such upper bounds. It also says its method "fails to prove anything about more than two primes in a given tuple" (Question 3). Only marginal tools might be reusable.

**Possibly usable ingredients (quoted from the paper):**

1. **Gallagher's singular-series average (3.7).** As h → ∞, the sum of 𝔖(H_k) over distinct 1 ≤ h₁,…,h_k ≤ h is asymptotic to h^k. Here 𝔖(H) = ∏_p (1 − ν_p(H)/p)(1 − 1/p)^{−k} (2.2). It is cited from Gallagher [10], not proved in the paper. It is relevant only if one averages over gap patterns.

2. **Proposition 1 (divisor-sum correlations).** If R ≪ N^{1/2}(log N)^{−4M} and h ≤ R^C, then the sum over n ≤ N of Λ_R(n;H₁,ℓ₁)Λ_R(n;H₂,ℓ₂) equals C(ℓ₁+ℓ₂, ℓ₁) · (log R)^{r+ℓ₁+ℓ₂}/(r+ℓ₁+ℓ₂)! · (𝔖(H)+o_M(1)) · N.
   - Λ_R is defined in (2.13).
   - Method: Perron-type contour integrals (6.6), factoring out ζ-powers (7.9), and shifting contours into the classical zero-free region (Lemma 3, Section 8).

3. **Proposition 2.** This is the analogous result with an extra weight θ(n+h₀), with three cases according to h₀ ∉ H, h₀ ∈ H₁∖H₂, or h₀ ∈ H₁∩H₂.
   - Range: valid for R ≪ N^{1/4}(log N)^{−B(M)}, or R ≪ N^{ϑ/2−ε} under level of distribution ϑ.
   - Method: Bombieri–Vinogradov plus Cauchy–Schwarz (9.13), followed by the same contour analysis.

4. **Lemma 2 (divisor-sum bounds).** For real m > 0 and x ≥ 1:
   - The squarefree sum of d_m(q)/q over q ≤ x is ≤ (m+1+log x)^{m+1}.
   - The squarefree sum of d_m(q) over q ≤ x is ≤ x(m+1+log x)^{m+1}.
   - Method: induction on m.

5. **Main theorems, which go the "wrong direction" for this problem.**
   - Theorem 2: liminf (p_{n+1}−p_n)/log p_n = 0.
   - Theorem 3: under level ϑ, for ν ≥ 2, E_ν ≤ (√ν − √(2ϑ))², with E_ν = liminf (p_{n+ν}−p_n)/log p_n. Unconditionally, E_ν ≤ (√ν − 1)².
   - Theorem 1: under level ϑ > 1/2, every admissible k-tuple with k ≥ C(ϑ) contains two primes infinitely often; k = 6 suffices if ϑ ≥ 0.971.
   - Method: the Granville–Soundararajan comparison of the weighted sums Q₂ and Q₁ in (3.3), together with an eigenvector or quadratic-form optimisation (3.14).
   - These only produce clusters of primes. They say nothing about long monotone-gap chains, and nothing limiting the density of such chains.

**Open questions stated in the paper (none directly about convex prime sequences):**

- Q1: Can bounded gaps be proved unconditionally by this method?
- Q2: Is ϑ = 1/2 a true barrier? Soundararajan showed it is for this argument.
- Q3: Under Elliott–Halberstam, can one get three or more primes in admissible k-tuples?
- Q4: Under Elliott–Halberstam, can the twin prime conjecture be proved by a refinement of the method?
- Announced for later papers: liminf (p_{n+1}−p_n)/((log p_n)^{1/2}(log log p_n)²) < ∞ (1.9), and results uniform in k.

**Bottom line.** Nothing in the paper bounds q_n/n² for prime sequences with non-decreasing gaps. At most, items 1–4 are generic sieve and divisor-sum machinery an attacker might adapt.

## Primes in tuples II (2010)
https://doi.org/10.1007/s11511-010-0044-9; full text: yes

## Relevance

**The paper is essentially not relevant.** It proves that some pairs of consecutive primes are unusually close. The problem asks how fast a prime sequence with non-decreasing gaps must grow, given Richter's known bound liminf q_n/n² > 0.352. The paper says nothing about such sequences, long chains of primes, or growth of the form q_n/n². Below are the only items that conceivably touch on prime gaps or prime differences.

## Possibly usable statements (quoted)

**Theorem 1.**
liminf_{n→∞} (p_{n+1} − p_n) / (√(log p_n) · (log log p_n)²) < ∞.

**Theorem 2.**
"Let us suppose that an N > N₀ is given such that for any real primitive character χ mod q, q ⩽ e^{3√(log N)}, we have L(s,χ) ≠ 0 for s ∈ (1 − 1/(9√(log N)), 1). Let A = A_N = {a_j}_{j=1}^h ⊆ [1,N] ∩ ℕ be arbitrary … with h ⩾ C √(log N) · log₂² N … Then there exists n ∈ [N, 2N] such that at least two numbers of the form n + a_j and n + a_{j'}, 1 ⩽ j < j' ⩽ h, are primes."

**Theorem 3.**
"Let A ⊆ ℕ be an arbitrary sequence satisfying A(N) > C √(log N) · log₂² N for N > N₀. Then infinitely many elements of A − A can be written as the difference of two primes."

- **Method for Theorems 1–3:** the GPY weighted sieve. It uses Λ_R(n;H,ℓ) = (1/(K+ℓ)!) Σ_{d | P_H(n), d ⩽ R} μ(d) (log R/d)^{K+ℓ}.
- Theorems 4 and 5 give asymptotics for Σ Λ_R Λ_R and Σ Λ_R Λ_R θ(n+h₀), restricted to regular residue classes mod P = ∏_{p⩽√(log N)} p. These are proved by contour integration in the zero-free region of ζ.
- The parameters are uniform in K ⩽ c₁ √(log N)/log₂² N, with R = (3N)^{1/4−o(1)}.

**Theorem 6 (Bombieri–Vinogradov with moduli Mq).**
For X in a sequence X_n → ∞ (avoiding Landau–Siegel zeros via Lemma 14 and the Landau–Page theorem):

Σ_{q⩽Q*, (q,M)=1} E*(X, Mq) ≪ (X/M) · L¹⁵ · e^{−c₂ log X / log Y(X)},

with Q* = X^{1/2} M^{−3} e^{−c*√(log X)}.
- **Method:** the explicit formula plus Montgomery's zero-density estimate N*(1−δ,Q,T) ≪ (Q²T)^{3δ/(1+δ)} (log QT)⁹.

**Lemma 16 (quasi-monotonicity of the singular-series average).**
Let S*_A(k) = h^{−k} Σ_{H⊂A, |H|=k} S(H). If k < εh/log₂ N, then

S*_A(k+1) ⩾ S*_A(k) · (1 + O(ε) + O(1/log N)).

- **Method:** count z-quasiprime tuples and apply a Chebyshev-type rearrangement inequality.
- It holds for any A ⊆ [1,N] with |A| = h.
- Of everything here, this lemma is the most transferable tool, since it averages Hardy–Littlewood densities over arbitrary shift sets. Its connection to the problem is still speculative.

**Lemma 14.** Hypothesis S(Y) holds for a sequence Y_n → ∞ with Y_n ⩽ e^{√(Y_{n−1})}.

**Constant quoted:** the conditional result p_{n+1} − p_n ⩽ 16 infinitely often, assuming level of distribution ϑ ⩾ 0.98. (This is a citation of Primes in tuples I.)

## Open questions or remarks stated in the paper

- Since 2005 there has been no progress toward bounded gaps (1.5). Extending Bombieri–Vinogradov enough to get bounded gaps "will require some basic new ideas."
- The asymptotic B_A(k) ∼ h^k "is probably not true if A is arbitrary, and even for A = [1,h] it might fail if k is as large as h/(log h)^C."
- The authors cannot localize gaps of size O(√(log N) · log₂² N) to every dyadic interval [N, 2N], because of possible Landau–Siegel zeros.

None of these is close to the convex-sequence growth question.

## Very Large Gaps between Consecutive Primes (1997)
https://doi.org/10.1006/jnth.1997.2081; full text: abstract only

(No text or abstract was available, so this paper is cited, not summarised.)
# erdosproblems.com #455: problem page and forum thread (fetched 2026-10-02T01:25:19Z)

Comments are unverified; several withdraw earlier claims.

## Page
OPEN
This is open, and cannot be resolved with a finite computation.
Let $q_1<q_2<\cdots$ be a sequence of primes such that\[q_{n+1}-q_n\geq q_n-q_{n-1}.\]Must\[\lim_n \frac{q_n}{n^2}=\infty?\]
#455: [ErGr80,p.91]
number theory
Richter [Ri76] proved that\[\liminf_n \frac{q_n}{n^2}>0.352\cdots.\]
Additional thanks to: Terence Tao

## Forum comments
Order by
 oldest first or
 newest first. (The most recent comments are highlighted in a red border.)