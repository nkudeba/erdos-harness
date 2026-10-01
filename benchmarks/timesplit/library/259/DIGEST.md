# Literature library (papers dated before 2026-04-14; 6 paper(s))

Summaries of what each paper states, written by a model for this problem. Unverified: a summary can be wrong, and a paper's claim is not a Lean fact.

## On the irrationality of certain series (1974)
https://doi.org/10.2140/pjm.1974.55.85; full text: yes

# Relevance of Erdős–Straus (1974) to the irrationality of Σ μ(n)² n/2ⁿ

**Verdict: the paper is not directly relevant.** Its machinery covers series Σ bₙ/(a₁⋯aₙ) where the bₙ are integers that are small compared with aₙ₋₁aₙ. The problem's series has this shape with aₙ = 2 for all n and bₙ = μ(n)²n. But here bₙ/(aₙ₋₁aₙ) = μ(n)²n/4 does not tend to 0. So hypothesis (2.2) of the main criterion fails, and none of the paper's results apply as stated. The paper does not mention squarefree numbers, μ, or base-2 series with integer-valued coefficients. Below is what is closest. The extracted text is OCR-garbled, so quotations are reconstructed where noted.

**Theorem 1.1** (from their earlier paper [2]). "If {aₙ} is a monotonic sequence of positive integers with aₙ ≥ n^{11/24} [exponent garbled in source] for all large n, then the series Σ φ(n)/(a₁⋯aₙ) and Σ σ(n)/(a₁⋯aₙ) are irrational."

**Theorem 2.1 (the rationality criterion).** "Let {bₙ} be a sequence of integers and {aₙ} a sequence of positive integers with aₙ > 1 for all large n and (2.2) lim bₙ/(aₙ₋₁aₙ) = 0. Then the series Σ bₙ/(a₁⋯aₙ) is rational if and only if there exists a positive integer B and a sequence of integers {cₙ} so that for all large n we have (2.4) Bbₙ = cₙaₙ − cₙ₊₁, |cₙ₊₁| < aₙ/2."
- **Method:** elementary. Multiply the series by B·a₁⋯a_{N−1} and take cₙ to be the nearest integer to Bbₙ/aₙ. The tail Rₙ is less than 1/2 in absolute value, which forces the recursion.

**Remark after Theorem 2.1.** For rational values cₙ₊₁/aₙ → 0. Hence "either aₙ → ∞ or cₙ = 0 and hence bₙ = 0 for all large n."
- With aₙ = 2 this is the trivial case, but (2.2) already fails for the problem.

**Corollary 2.10.** Assume the hypotheses of Theorem 2.1, together with bₙ > 0, aₙ₊₁ ≥ aₙ, lim (bₙ₊₁ − bₙ)/aₙ ≤ 0 and lim inf aₙ/bₙ = 0. Then the series is irrational.
- **Method:** from (2.4), cₙ₊₁ > cₙ would force a large jump in bₙ, so cₙ is eventually nonincreasing. That makes bₙ/aₙ bounded, a contradiction.
- Without the lim inf hypothesis, rational values occur only when Bbₙ = C(aₙ − 1).

**Theorem 3.1.** "Let pₙ be the nth prime and let {aₙ} be a monotonic sequence of positive integers satisfying lim pₙ/aₙ² = 0 and lim inf aₙ/pₙ = 0. Then the series Σ pₙ/(a₁⋯aₙ) is irrational."
- **Method:** Theorem 2.1, plus a counting of the indices where cₙ₊₁ > cₙ, which force prime gaps larger than √pₙ.

**Theorem 3.7.** If {aₙ} is monotonic with aₙ > n^{1/2+δ}, then 1, x, y, z are rationally independent, where:
- x = Σ φ(n)/(a₁⋯aₙ),
- y = Σ σ(n)/(a₁⋯aₙ),
- z = Σ dₙ/(a₁⋯aₙ), with |dₙ| < n^{1/2−δ} and infinitely many dₙ ≠ 0.

**Method for Theorem 3.7:**
- Apply Theorem 2.1 along the primes.
- Use Selberg's Theorem 3.10 on primes in almost all short intervals: for increasing Φ with Φ(x)/x decreasing to 0 and lim inf log Φ(x)/log x > 19/77, for almost all x, π(x+Φ(x)) − π(x) ~ Φ(x)/log x. It is applied with Φ(x) = x^{1/2+δ}.
- Use Dirichlet's theorem to make σ(p+1)/(p+1) and φ(p+1)/(p+1) dense, which rules out rational limit points with denominator c.

**Open questions stated in the paper** (none is close to the problem):
- The conjecture that Σ φ(n)/(a₁⋯aₙ) and Σ σ(n)/(a₁⋯aₙ) are irrational assuming only that {aₙ} is monotonic.
- Whether the weaker hypothesis lim inf aₙ₊₁/aₙ > 0 would suffice. The choices aₙ = φ(n)+1 and aₙ = σ(n)+1 show some condition is needed.

**Only conceivable transferable idea:** the shape of the "nearest-integer recursion" Bbₙ = cₙaₙ − cₙ₊₁. Using it on the problem's series would require regrouping it so that the denominators grow faster than the numerators. The paper does not do this.

## Some number theoretic results (1971)
https://doi.org/10.2140/pjm.1971.36.635; full text: yes

**Relevance.** Partial. Section 1, on sums of residues mod p (Conjecture 1.1, Corollary 1.3, Lemmas 1.4–1.5, Theorem 1.7), is not relevant. Section 2 is relevant only through its methods. It treats series Σ f(n)/(a₁⋯aₙ) for f = d, σ, φ. The problem's series has aₙ = 2 for all n and numerator μ(n)²·n. The paper proves nothing about μ² or about numerators of size n with constant aₙ.

**Results from §2**

- **Earlier result cited [Erdős 1948].** "the series Σ d(n)t⁻ⁿ is irrational for every integer t, |t| > 1."

- **Lemma 2.2.** "The series (2.1) is irrational if there exists a δ > 0 so that the inequality aₙ < (log n)^{1−δ} holds for infinitely many values of n." Here (2.1) is ξ = Σ d(n)/(a₁⋯aₙ) with 2 ≤ a₁ ≤ a₂ ≤ ⋯.
  - Method: Assume ξ = a/b.
  - Monotonicity gives an interval I of length n/log n on which aᵢ = t is constant.
  - Take the consecutive primes p₁, p₂, … greater than (log n)². By the Chinese remainder theorem, choose x so that d(x+l) ≡ 0 (mod t^{l+1}) for l = 0, …, k−1, with k = [(log n)^{δ/2}]. This is system (2.4): x+i is divisible by a product of i+1 primes, each to power t−1. It kills the first k terms modulo integers.
  - Bound the tail in two parts. Terms with s > 10 log n are small by (2.7). For the rest, an averaging argument (2.12) over x₀ + yA picks x with d(x+k+s) < 2^{k/4} for 0 ≤ s < 10 log n. That gives a tail < 1, which is a contradiction.

- **Lemma 2.14.** "If there exists a positive constant c so that |aₙ| > c(log n)^{1/4} for all n then the series (2.1) is irrational." Monotonicity is not needed here.
  - Method: the Dirichlet divisor theorem (2.15), Σ_{n≤N} d(n) ~ N log N.
  - Kac's result (2.16): "d(n) < (log n)^{log 2+ε} for almost all n."
  - These give Lemma 2.17: for almost all x, "d(x+y) < b⁻¹(2c)^{−y}(log x)^{3y/4}, y = 3, 4, …".

- **Theorem 2.23.** "The series (2.1) is irrational whenever 2 ≤ a₁ ≤ a₂ ≤ ⋯ ≤ aₙ ≤ ⋯."

- **Lemma 2.27.** "Let {aₙ} be a sequence of positive integers with aₙ ≥ 2 and {bₙ} a sequence of positive integers so that bₙ₊₁ = o(aₙaₙ₊₁). If ξ = Σ bₙ/(a₁⋯aₙ) is rational then aₙ = O(bₙ)."

- **Lemma 2.29.** Rationality of ξ = a/b, under bₙ₊₁ = o(aₙaₙ₊₁), is equivalent to the existence of positive integers cₙ with "b bₙ = cₙaₙ − cₙ₊₁, 0 < cₙ₊₁ < aₙ, and cₙ₊₁ = o(aₙ)" for all large n.
  - Caution: with aₙ = 2 and bₙ = μ(n)²n, the hypothesis bₙ₊₁ = o(aₙaₙ₊₁) fails. So 2.27 and 2.29 do not apply directly.

- **Lemma 2.32 (sieve, constants due to E. Miech).** "Given an integer a and ε > 0 then for large y the number of integers m satisfying m ≢ 0, m ≢ a (mod p) for all primes p, with 2 < p < y^{1/5} exceeds y^{1−ε}."

- **Theorem 2.26.** "If {aₙ} is a monotonic sequence of integers with aₙ ≥ n^{11/12} for all large n then the series in (2.25) are irrational." Here (2.25) means Σ φ(n)/(a₁⋯aₙ) and Σ σ(n)/(a₁⋯aₙ).
  - Method: Lemma 2.29 gives b f(n) = cₙaₙ − cₙ₊₁.
  - Restrict to n with aₙ₊₁/aₙ < 1 + n^{−1/2}.
  - Use n = 2qm, with q a prime near x^{1/12} and m sieved by Lemma 2.32. This gives f(n) = n(1 + O(x^{−2/11})) and f(2q) = A/q with q ∤ A.
  - The result is a contradiction (2.42)–(2.43).

- **Remarks.**
  - The authors say similar results hold for σₖ and for products of powers of σₖ and φ, if aₙ is monotonic and grows faster than some fractional power of the numerators.
  - There are 2^{ℵ₀} rational series of type (2.25), even with cₙ ∈ {1, 2}, or {1, 2, 3} for φ.
  - The choice aₙ = f(n) + 1 gives a sum equal to 1, so some restriction on aₙ is necessary.

**Open questions stated in the paper**

- **Conjecture 2.24.** "The series (2.1) is irrational whenever aₙ …". The condition is lost in the scan, so the exact hypothesis is unknown.
- **Stated as reasonable to conjecture.** The series (2.25) are irrational whenever aₙ increases monotonically; this is proved only under aₙ ≥ n^{11/12}.
- **Claim without proof.** "With considerable additional effort" monotonicity in Theorem 2.23 can be weakened to aₘ/aₙ ≥ c > 0 for m > n.

**Possible ingredient for the problem.** The template of Lemma 2.2 and [Erdős 1948] covers the constant case aₙ = t: choose x by the Chinese remainder theorem so that a block of numerators is controlled modulo powers of t, then bound the tail. For μ²(n)n/2ⁿ the analogous control would come from congruences on x+l modulo squares of primes, which make μ(x+l)² = 0. The paper does not carry this out.

## Transcendence of power series for some number theoretic functions (2008)
https://doi.org/10.1090/s0002-9939-08-09737-2; full text: abstract only

**Paper:** "Transcendence of power series for some number theoretic functions" (2008-10-28). Only the abstract was provided, so nothing below goes beyond it.

## Verdict on relevance

The paper is only marginally relevant. Its results are about transcendence of **power series as functions**, over ℤ(z). The problem asks about the **arithmetic nature of one value**: the series Σ μ(n)² n zⁿ evaluated at z = 1/2. Transcendence of a function over ℤ(z) does not, by itself, imply anything about whether its value at a rational point is irrational. The abstract states no results about special values, irrationality or the point z = 1/2.

## Statements in the abstract that could be ingredients

**1. Fatou's theorem (new proof).**
> "if an algebraic function has a power series expansion with bounded integer coefficients, then it must be a rational function."

- **Method:** the abstract says only that a "new proof" is given. The technique is not described.
- **Possible relevance:** the coefficients μ(n)² are bounded integers (0 or 1). So the theorem applies to F(z) = Σ μ(n)² zⁿ. If F is not rational, it is transcendental over ℤ(z).
- **Caveat:** the problem's series is z·F′(z) at z = 1/2. Its coefficients n·μ(n)² are unbounded, so the theorem does not apply to it directly.
- **Caveat:** the abstract does not state the case μ(n)² explicitly.

**2. Completely multiplicative ±1 functions.**
> "for any non–trivial completely multiplicative function from ℕ to {−1,1}, the series Σ_{n=1}^∞ f(n)zⁿ is transcendental over ℤ(z); in particular, Σ_{n=1}^∞ λ(n)zⁿ is transcendental, where λ is Liouville's function."

- **Method:** Fatou's theorem reduces the claim to showing the series is not rational. The abstract does not say how non-rationality is shown.
- **Relevance:** μ² is multiplicative but not completely multiplicative, and it takes values in {0,1}, not {−1,1}. So this result does not cover μ².

**3. Möbius function.**
> "The transcendence of Σ_{n=1}^∞ μ(n)zⁿ is also proved."

- **Method:** not described in the abstract. Presumably it again goes through Fatou's theorem plus a proof of non-rationality, since the coefficients are bounded integers.
- **Relevance:** this is the closest statement to the problem. It concerns μ, not μ², and transcendence of the function, not irrationality of a value. The non-rationality argument might be adaptable to show Σ μ(n)² zⁿ is not rational, but that would still only be a statement about the function.

## Constructions and constants

None are given in the abstract.

## Open questions stated

None are stated in the abstract. Nothing in the provided text addresses irrationality of values such as Σ μ(n)² n/2ⁿ.

## Bottom line

The paper gives function-level transcendence tools: Fatou's theorem and the non-rationality of certain arithmetic power series. These do not bear directly on irrationality at z = 1/2. Any use for the problem would need a separate value-level argument, and the abstract supplies none.

## On Gaps between Squarefree Numbers (1990)
https://doi.org/10.1007/978-1-4612-3464-7_15; full text: abstract only

# Summary: "On Gaps between Squarefree Numbers" (1990), abstract only

**Relevance verdict.** This paper is at most marginally relevant. Only the abstract is available. It concerns short intervals that contain a squarefree number. It says nothing about irrationality, about series of the form Σ μ(n)² n/2ⁿ, or about Diophantine approximation. The only possible ingredient is an upper bound on gaps between consecutive squarefree numbers, which controls how sparse the support of μ(n)² can be. Whether that helps with the problem is not addressed by the text.

**Results quoted in the abstract.** All are statements of the form: "for x sufficiently large, there is a squarefree number in (x, x+h]". Each item gives the admissible h = h(x), who proved it and the method, where the abstract states one.

- **Fogels [3]:** h = x^{2/5+ε} for every ε > 0. No method is stated.
- **Davenport and Estermann (reported by Roth [9]):** h ≫ x^{1/3} and h ≫ x^{1/3}(log x)^{-2/3} respectively, "for sufficiently large choices of the implied constants". The method is elementary arguments.
- **Roth [9]:** h = x^{1/4+ε}, by an elementary proof.
- **Roth [9]:** h ≫ x^{3/13}(log x)^{4/13}, by applying a result of van der Corput (exponential sums).
- **Nair [6]:** h ≫ x^{1/4}. This is a modification of Roth's elementary proof that removes the ε.
- **First author [1]:** h ≫ x^{3/13}, by elementary means.
- **Richert [8]:** h ≫ x^{2/9} log x, by exponential sum techniques.
- **Rankin [7]:** h = x^{θ+ε} with θ = 0.221982…, by exponential sums.
- **Schmidt [10]:** θ = 109556/494419 = 0.221585…, by exponential sums.
- **Graham and Kolesnik [4]:** θ = 1057/4785 = 0.2208986…, by exponential sums.

The abstract says only that "the authors investigated the problem further". It does not state the paper's own theorem, exponent, constants, constructions or lemmas.

**Possible use for the problem.** These results show that μ(n)² = 1 for some n in every interval (x, x + x^{0.221}] for large x. So the coefficient sequence n·μ(n)² has no long runs of zeros. Whether such gap information bears on the irrationality of Σ μ(n)² n/2ⁿ is not addressed in the text.

**Open questions stated.** None appear in the abstract. No open question close to the problem is given.

**Caveat.** The full paper's main theorem and its methods are not in the supplied text, so they cannot be reported here.

## On Gaps Between Squarefree Numbers II (1992)
https://doi.org/10.1112/jlms/s2-45.2.215; full text: abstract only

# Summary: "On Gaps Between Squarefree Numbers II" (1992), abstract only

## Relevance

This paper is **essentially not relevant**. At most it offers one weak, indirect ingredient.

- The problem asks whether Σ μ(n)² n/2ⁿ is irrational. That is a question about the arithmetic nature of a series whose coefficients are supported on the squarefree numbers.
- The paper is about short intervals: how small h(x) can be while (x, x+h] is still guaranteed to contain a squarefree number.
- The only conceivable link is that bounds on gaps between consecutive squarefree numbers control the support of the coefficient sequence. Such information sometimes enters arguments about lacunarity or non-periodicity of the coefficients. The paper itself makes no such connection.
- It says nothing about irrationality, power series at 1/2, or binary expansions.

## Main result, as quoted

> "THEOREM. There exists a constant c > 0 such that for x sufficiently large the interval (x, x + cx s log x] contains a squarefree number."

**The exponent is garbled in the supplied text.** "x s" stands in for x raised to some power, and that power does not survive in the abstract. I cannot state it without using memory, so I don't.

- **Method:** the abstract says "The proof of the theorem will be elementary."
- It builds on groundwork from the authors' earlier paper [3], which it partly re-presents with "new approaches to some of the previous work."

## Prior results mentioned (exponents also garbled)

- The authors [3] showed "by elementary means that there is a constant c > 0 such that, for x sufficiently large, the interval (x, x + h] with h = cx& contains a squarefree number."
- "Using exponential sums, they showed that ^ may be replaced by ^."
- The exponents in both statements are lost in the text provided.
- The history of the problem is attributed to Fogels, Roth, Richert, Rankin, Schmidt, Graham–Kolesnik, the second author [14, 15], and the first author [2]. A fuller history is in [3].

## Notation and constants

These are listed only in case the full text is consulted:

- c is a sufficiently large constant, with c ≥ 1.
- x is sufficiently large, meaning x ≥ x₀(c).
- a, b, d, u are positive integers, and p is a prime.
- The implied constant c′ in ≪ is independent of c.
- θ > 9 (as garbled), with the condition "x* > h…/(log x)".
- α is real, and v₁, v₂ and the parameter written "ft" are positive reals.

No lemmas or constructions are stated in the abstract.

## Open questions stated

None are stated in the supplied text. Nothing is said about irrationality or about sums like Σ μ(n)² n/2ⁿ.

## Bottom line for the attacker

The only possible use is an explicit gap bound: consecutive squarefree numbers near x differ by at most cx^θ log x for some θ < 1 that is not recoverable from this text. Whether that helps depends entirely on the strategy chosen. The paper offers no direct tool for the irrationality question.

## Irrationality of Certain Lambert Series (2004)
https://doi.org/10.3836/tjm/1244208475; full text: yes

**Relevance verdict.** The paper is only marginally relevant. It proves irrationality of Lambert series $\sum a_n/(1-q^n)$ whose coefficients $\{a_n\}$ are periodic of period two. It also treats reciprocal sums of binary recurrences. The target series $\sum \mu(n)^2 n/2^n$ is a power series at $x=1/2$. Writing it as a Lambert series $\sum b_d\, x^d/(1-x^d)$ needs $\sum_{d\mid n} b_d=\mu(n)^2 n$, and that $b_d$ is not periodic of period two. Nothing in the paper applies directly. The method (Borwein-type contour integrals) is the only possible ingredient.

**Exact statements**

- **Theorem 1.** "Let K be either Q or an imaginary quadratic field. Assume that q is an integer in K with |q| > 1 and {a_n} a periodic sequence in K of period two, not identically zero. Then θ = Σ_{n≥1} a_n/(1−q^n) ∉ K."
- **Corollary 1.** "Let q ∈ Z with |q| ≥ 2 and {a_n}, {b_n} be periodic sequences in Q of period two, not identically zero. Then the numbers 1, Σ a_n/(q^n−1), Σ b_n/(q^n−1) are linearly independent over Q if and only if {a_n} and {b_n} are linearly independent over Q."
- **Example 1.** The numbers 1, L_q(1)=Σ1/(q^n−1) and L_q(−1)=Σ(−1)^n/(q^n−1) are linearly independent over Q for q ∈ Z, |q| ≥ 2.
- **Theorem 2.** This is the same conclusion, θ ∉ Q(q), for an algebraic integer q with |q|>1 and |q^σ|<1 for every conjugate q^σ ≠ q (a Pisot-type condition).
- **Theorem 3.** "Let q be a quadratic integer satisfying |q| > 1 and |q^σ| < 1 … γ a unit in Q(q) with |γ| ≤ 1, and α ∈ Q(q)^× with (den(q^l α))^4 < |q| for some l ∈ N. Then ξ = Σ γ^n/(1−αq^n) ∉ Q(q), provided αq^n ≠ 1."
- **Corollaries 2 and 3.** These give irrationality over Q(ρ₁) of Σ γ^n/R_{an+b} and Σ γ^n/(R_{an+b}R_{a(n+1)+b}) for binary recurrences R_n under unit and denominator conditions. Examples include Fibonacci and Lucas sums and T₁ = Σ1/(F_nF_{n+1}) ∉ Q(√5).

**Method**

- The paper uses Borwein's integral, modified as
 F_n(q) = (1/2πi)∮_{|t|=1} [(−1/t)∏_{k=1}^{2n}(1−q^k/t)] / [∏_{k=1}^n(1−q^{2k}t)] · Σ_m a_m/(1−q^m/t) dt.
- **Lemmas 1 and 2 (residue theorem).** These give D_n(q)F_n(q) = A_n(q)θ + B_n(q), with A_n, B_n ∈ Z[a₁,a₂,q] and D_n = ∏_{k=n+1}^{2n}(1−q^{2k}).
- **Bound on D_n (equation (5)).** |D_n| ≤ c₁|q|^{3n²+n}.
- **Lemma 3 (residues exterior to the circle).** 0 < |F_n(q)| ≤ c₃|q|^{−3n²−2n}.
- **Conclusion.** Together these give 0 < |A_nθ+B_n| ≪ |q|^{−n}, which forces θ ∉ K.
- **Theorem 2.** It additionally bounds the conjugates, |A_n^σ| ≤ c₇n and |B_n^σ| ≤ c₈n², and then takes the norm.
- **Theorem 3.** It uses an analogous integral G_n(q,α,γ) and needs the denominator condition (denα)^4 < |q|.

**Why period two matters.** The key step for (7) is the closed form Σ_m a_m/q^{(ν+1)m} = (a₁q^{ν+1}+a₂)/(q^{2(ν+1)}−1). This rational form exists only because a_m is periodic. Coefficients like μ²(n)n, or its Lambert-transformed coefficients, would not give such closed forms.

**Background cited.** Erdős [10] proved L₂(1) = Σ1/(2^n−1) is irrational. Borwein [3], [4] gave irrationality measures for Σ1/(q^n+α). Bézivin [2] proved linear independence for values of the q-exponential.

**Open questions.** The paper states no open questions, and none are close to the problem.
