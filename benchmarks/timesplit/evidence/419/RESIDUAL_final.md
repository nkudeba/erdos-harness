# Residual — Erdős #42884 (after cycle 2, 2026-10-20T22:05:53Z)

**Nothing here resolves the problem.** A residual skeleton is a certified conditional theorem: the frozen target follows by machine-checked glue from the hypotheses below. The OPEN hypotheses are the residual; the problem is exactly as open as they are.

Skeleton: `/Users/nicolas.kudeba/workspace/erdos-harness/programs/erdos_42884/Residual.lean`

| open conjectures | published premises | discharged (certified) | complexity of open conjectures |
|---|---|---|---|
| 0 | 0 | 18 | 0 |

| hypothesis | kind | status | complexity | derivation / source |
|---|---|---|---|---|
| `erdos_42884_hyp_product_formula` | conjecture | certified | 6 |  |
| `erdos_42884_hyp_legendre_lower` | conjecture | certified | 7 |  |
| `erdos_42884_hyp_large_prime_unique` | conjecture | certified | 11 |  |
| `erdos_42884_hyp_large_prime_val` | conjecture | certified | 8 |  |
| `erdos_42884_hyp_list_sum_le_prod` | conjecture | certified | 7 | List induction: x + y ≤ x*y for x, y ≥ 2. The empty list gives 0 ≤ 1. |
| `erdos_42884_hyp_block_invariant` | conjecture | certified | 10 | Induction on L = x::L' with P = prod L'. If P ≥ 2s, use the IH and s*x ≤ (x-1)*P. If P < 2s, use sum L' ≤ P and 2s² + xP - sx - sP = s² + (s-x)(s-P) > 0. |
| `erdos_42884_hyp_three_blocks` | conjecture | certified | 11 |  |
| `erdos_42884_hyp_small_prime_sum` | conjecture | certified | 6 | three_blocks with s = √m, applied to the multiset of small prime factors with multiplicity. Its product divides m, so it is ≤ m. |
| `erdos_42884_hyp_small_prime_product` | conjecture | certified | 7 |  |
| `erdos_42884_hyp_split_hyp_prod_formula` | conjecture | certified | 5 |  |
| `erdos_42884_hyp_split_hyp_large_prod` | conjecture | certified | 6 |  |
| `erdos_42884_hyp_split` | conjecture | certified | 4 | product_formula, plus splitting primeFactors(n+1) by q*q ≤ n+1. The complement is ∅ or {P} (large_prime_unique), and the P-factor equals largeFactorH (large_pri |
| `erdos_42884_hyp_h_mem` | conjecture | certified | 6 |  |
| `erdos_42884_hyp_sandwich` | conjecture | certified | 6 |  |
| `erdos_42884_hyp_h_kP` | conjecture | certified | 7 |  |
| `erdos_42884_hyp_h_sq` | conjecture | certified | 4 |  |
| `erdos_42884_hyp_exp_tail` | conjecture | certified | 1 |  |
| `erdos_42884_hyp_closed` | conjecture | certified | 0 |  |

Statements:

- `erdos_42884_hyp_product_formula` : `∀ m : ℕ, 2 ≤ m → (σ 0 m.factorial : ℝ) / (σ 0 (m - 1).factorial : ℝ) = ∏ q ∈ m.primeFactors, (1 + (m.factorization q : ℝ) / (((m - 1).factorial.factorization q : ℝ) + 1))`
- `erdos_42884_hyp_legendre_lower` : `∀ m q : ℕ, 1 ≤ m → q.Prime → q ∣ m → m ≤ q * ((m - 1).factorial.factorization q + 1)`
- `erdos_42884_hyp_large_prime_unique` : `∀ m P Q : ℕ, m ≠ 0 → P.Prime → Q.Prime → P ∣ m → Q ∣ m → m < P * P → m < Q * Q → P = Q`
- `erdos_42884_hyp_large_prime_val` : `∀ k P : ℕ, 1 ≤ k → k < P → P.Prime → (k * P).factorization P = 1 ∧ (k * P - 1).factorial.factorization P = k - 1`
- `erdos_42884_hyp_list_sum_le_prod` : `∀ L : List ℕ, (∀ x ∈ L, 2 ≤ x) → L.sum ≤ L.prod`
- `erdos_42884_hyp_block_invariant` : `∀ (s : ℝ) (L : List ℕ), 0 < s → (∀ x ∈ L, 2 ≤ x ∧ (x : ℝ) ≤ s) → s * ((L.sum : ℕ) : ℝ) ≤ ((L.prod : ℕ) : ℝ) + 2 * s ^ 2`
- `erdos_42884_hyp_three_blocks` : `∀ (s : ℝ) (L : List ℕ), 0 < s → (∀ x ∈ L, 2 ≤ x ∧ (x : ℝ) ≤ s) → ((L.prod : ℕ) : ℝ) ≤ s ^ 2 → ((L.sum : ℕ) : ℝ) ≤ 3 * s`
- `erdos_42884_hyp_small_prime_sum` : `∀ m : ℕ, 1 ≤ m → ∑ q ∈ Finset.filter (fun q => q * q ≤ m) m.primeFactors, (m.factorization q : ℝ) * (q : ℝ) ≤ 3 * Real.sqrt (m : ℝ)`
- `erdos_42884_hyp_small_prime_product` : `∀ m : ℕ, 2 ≤ m → ∏ q ∈ Finset.filter (fun q => q * q ≤ m) m.primeFactors, (1 + (m.factorization q : ℝ) / (((m - 1).factorial.factorization q : ℝ) + 1)) ≤ Real.exp (3 / Real.sqrt (m : ℝ))`
- `erdos_42884_hyp_split_hyp_prod_formula` : `∀ n : ℕ, factorialDivisorRatio n = ∏ q ∈ (n + 1).primeFactors, (1 + ((n + 1).factorization q : ℝ) / ((n.factorial.factorization q : ℝ) + 1))`
- `erdos_42884_hyp_split_hyp_large_prod` : `∀ n : ℕ, ∏ q ∈ Finset.filter (fun q => ¬ q * q ≤ n + 1) (n + 1).primeFactors, (1 + ((n + 1).factorization q : ℝ) / ((n.factorial.factorization q : ℝ) + 1)) = largeFactorH (n + 1)`
- `erdos_42884_hyp_split` : `∀ n : ℕ, factorialDivisorRatio n = largeFactorH (n + 1) * smallPrimeProduct (n + 1)`
- `erdos_42884_hyp_h_mem` : `∀ m : ℕ, 1 ≤ largeFactorH m ∧ largeFactorH m ≤ 2 ∧ largeFactorH m ∈ limitPointSet`
- `erdos_42884_hyp_sandwich` : `∀ n : ℕ, largeFactorH (n + 1) ≤ factorialDivisorRatio n ∧ factorialDivisorRatio n ≤ largeFactorH (n + 1) * Real.exp (3 / Real.sqrt ((n : ℝ) + 1))`
- `erdos_42884_hyp_h_kP` : `∀ k P : ℕ, 1 ≤ k → k < P → P.Prime → largeFactorH (k * P) = 1 + 1 / (k : ℝ)`
- `erdos_42884_hyp_h_sq` : `∀ q : ℕ, q.Prime → largeFactorH (q * q) = 1`
- `erdos_42884_hyp_exp_tail` : `Tendsto (fun n : ℕ => Real.exp (3 / Real.sqrt ((n : ℝ) + 1))) atTop (nhds 1)`
- `erdos_42884_hyp_closed` : `IsClosed limitPointSet`

## Proof failures (what broke, fed back into the next plan)

- cycle 1: `erdos_42884_hyp_sandwich` exit 2, 3 attempt(s); mode=fast: 1 proof round(s) (3 attempts) and 0 refinement round(s) exhausted without a sorry-free proof
- cycle 1: `erdos_42884_hyp_small_prime_product` exit 2, 3 attempt(s); mode=fast: 1 proof round(s) (3 attempts) and 0 refinement round(s) exhausted without a sorry-free proof
- cycle 1: `erdos_42884_hyp_three_blocks` exit 2, 3 attempt(s); mode=fast: 1 proof round(s) (3 attempts) and 0 refinement round(s) exhausted without a sorry-free proof

## Moves the plan made in response

- cycle 2: `erdos_42884_hyp_three_blocks` → **lemma** — The failure was only the unknown name le_or_lt. The invariant s*sum ≤ prod + 2s² is now its own hypothesis, with sum ≤ prod as a helper. three_blocks is derived in the glue.
- cycle 2: `erdos_42884_hyp_small_prime_product` → **lemma** — The missing fact was the sum bound Σ v_q(m)*q ≤ 3√m, which is now a hypothesis. The glue proves the exp bound from it using legendre_lower, 1+t ≤ e^t and exp_sum.
- cycle 2: `erdos_42884_hyp_sandwich` → **define** — Named smallPrimeProduct. The residual is the single factorisation F n = h(n+1)*smallPrimeProduct(n+1), stated for all n so the n=0 edge case is included. The glue proves both sandwich bounds from it.

## Refuted statements (never re-propose)

- (none)
