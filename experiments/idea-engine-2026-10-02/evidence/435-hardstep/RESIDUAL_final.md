# Residual — Erdős #727285 (after cycle 2, 2026-10-03T11:17:23Z)

**Nothing here resolves the problem.** A residual skeleton is a certified conditional theorem: the frozen target follows by machine-checked glue from the hypotheses below. The OPEN hypotheses are the residual; the problem is exactly as open as they are.

Skeleton: `/Users/nicolas.kudeba/workspace/erdos-harness/programs/erdos_727285/Residual.lean`

| open conjectures | published premises | discharged (certified) | complexity of open conjectures |
|---|---|---|---|
| 0 | 0 | 16 | 0 |

| hypothesis | kind | status | complexity | derivation / source |
|---|---|---|---|---|
| `erdos_727285_hyp_S21a_phi_le_hyp_tower` | conjecture | certified | 12 |  |
| `erdos_727285_hyp_S21a_phi_le_hyp_support` | conjecture | certified | 8 |  |
| `erdos_727285_hyp_S21a_phi_le_hyp_symm` | conjecture | certified | 5 |  |
| `erdos_727285_hyp_S21a_phi_le_hyp_large` | conjecture | certified | 13 |  |
| `erdos_727285_hyp_S21a_phi_le_hyp_small` | conjecture | certified | 13 |  |
| `erdos_727285_hyp_S7_phi_basic` | conjecture | certified | 26 |  |
| `erdos_727285_hyp_S20_L7_small` | conjecture | certified | 10 |  |
| `erdos_727285_hyp_S21a_phi_le` | conjecture | certified | 8 |  |
| `erdos_727285_hyp_S4b_other` | conjecture | certified | 8 |  |
| `erdos_727285_hyp_S6_phiP_congr` | conjecture | certified | 13 |  |
| `erdos_727285_hyp_S11_case_lt` | conjecture | certified | 18 |  |
| `erdos_727285_hyp_S11_case_top` | conjecture | certified | 18 |  |
| `erdos_727285_hyp_S11_other_primes` | conjecture | certified | 20 |  |
| `erdos_727285_hyp_S11_glue` | conjecture | certified | 16 |  |
| `erdos_727285_hyp_S12_T_lower` | conjecture | certified | 13 |  |
| `erdos_727285_hyp_S21_choose_mem_T` | conjecture | certified | 8 |  |

Statements:

- `erdos_727285_hyp_S21a_phi_le_hyp_tower` : `∀ n : ℕ, erdos_727285_Good n → ∀ i ∈ Finset.Ico 1 n, ¬ (erdos_727285_NotTower n i ∧ erdos_727285_NotTower n (n - i)) → erdos_727285_phi n (n.choose i : ℤ) ≤ (n.choose i : ℤ)`
- `erdos_727285_hyp_S21a_phi_le_hyp_support` : `∀ n : ℕ, erdos_727285_Good n → ∀ i ∈ Finset.Ico 1 n, erdos_727285_phi n (n.choose i : ℤ) ≤ (erdos_727285_R n i : ℤ)`
- `erdos_727285_hyp_S21a_phi_le_hyp_symm` : `∀ n i : ℕ, i ≤ n → erdos_727285_R n (n - i) = erdos_727285_R n i`
- `erdos_727285_hyp_S21a_phi_le_hyp_large` : `∀ n : ℕ, erdos_727285_Good n → ∀ i : ℕ, 1 ≤ i → 2 * i ≤ n → 35 ≤ i → erdos_727285_NotTower n i → erdos_727285_R n i ≤ n.choose i`
- `erdos_727285_hyp_S21a_phi_le_hyp_small` : `∀ n : ℕ, erdos_727285_Good n → ∀ i : ℕ, 1 ≤ i → 2 * i ≤ n → i ≤ 34 → erdos_727285_NotTower n i → erdos_727285_R n i ≤ n.choose i`
- `erdos_727285_hyp_S7_phi_basic` : `∀ n : ℕ, erdos_727285_Good n → (∀ r : ℤ, 0 ≤ erdos_727285_phi n r) ∧ (∀ r : ℤ, (n : ℤ) ∣ erdos_727285_phi n r - r) ∧ (∀ r : ℤ, erdos_727285_phi n (r + (n : ℤ)) = erdos_727285_phi n r) ∧ (∀ r : ℤ, erdos_727285_phi n (r - (n : ℤ)) = erdos_727285_phi n r) ∧ erdos_727285_phi n 0 = 0 ∧ erdos_727285_phi n (erdos_727285_X n) = erdos_727285_X n`
- `erdos_727285_hyp_S20_L7_small` : `∀ n i : ℕ, erdos_727285_Good n → 1 ≤ i → i ≤ 34 → 2 * i ≤ n → erdos_727285_NotTower n i → erdos_727285_R n i ≤ n.choose i`
- `erdos_727285_hyp_S21a_phi_le` : `∀ n : ℕ, erdos_727285_Good n → ∀ i ∈ Finset.Ico 1 n, erdos_727285_phi n (n.choose i : ℤ) ≤ (n.choose i : ℤ)`
- `erdos_727285_hyp_S4b_other` : `∀ n p q d : ℕ, n ≠ 0 → p.Prime → q.Prime → p ≠ q → q ^ (n.factorization q) ∣ n.choose (p ^ d)`
- `erdos_727285_hyp_S6_phiP_congr` : `∀ n : ℕ, erdos_727285_Good n → ∀ p ∈ n.primeFactors, ∀ r r' : ℤ, (p : ℤ) ^ (n.factorization p) ∣ r - r' → erdos_727285_phiP n p r = erdos_727285_phiP n p r'`
- `erdos_727285_hyp_S11_case_lt` : `∀ n : ℕ, erdos_727285_Good n → ∀ p ∈ n.primeFactors, ∀ d ∈ Finset.Icc 1 (n.factorization p), ∀ r : ℤ, erdos_727285_digits n p r d < p - 1 → erdos_727285_phiP n p (r + (n.choose (p ^ d) : ℤ)) = erdos_727285_phiP n p r + (n.choose (p ^ d) : ℤ)`
- `erdos_727285_hyp_S11_case_top` : `∀ n : ℕ, erdos_727285_Good n → ∀ p ∈ n.primeFactors, ∀ d ∈ Finset.Icc 1 (n.factorization p), ∀ r : ℤ, p - 1 ≤ erdos_727285_digits n p r d → erdos_727285_phiP n p (r + (n.choose (p ^ d) : ℤ)) ≤ erdos_727285_phiP n p r + (n.choose (p ^ d) : ℤ)`
- `erdos_727285_hyp_S11_other_primes` : `∀ n : ℕ, erdos_727285_Good n → ∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, q ≠ p → ∀ d ∈ Finset.Icc 1 (n.factorization p), ∀ r : ℤ, erdos_727285_phiP n q (r + (n.choose (p ^ d) : ℤ)) = erdos_727285_phiP n q r`
- `erdos_727285_hyp_S11_glue` : `∀ n : ℕ, erdos_727285_Good n → ∀ p ∈ n.primeFactors, ∀ d ∈ Finset.Icc 1 (n.factorization p), ∀ r : ℤ, erdos_727285_phi n (r + (n.choose (p ^ d) : ℤ)) ≤ erdos_727285_phi n r + (n.choose (p ^ d) : ℤ)`
- `erdos_727285_hyp_S12_T_lower` : `∀ n : ℕ, erdos_727285_Good n → (∀ r : ℤ, erdos_727285_phi n r ∈ erdos_727285_T n) ∧ (∀ t ∈ erdos_727285_T n, erdos_727285_phi n t ≤ t)`
- `erdos_727285_hyp_S21_choose_mem_T` : `∀ n : ℕ, erdos_727285_Good n → ∀ i ∈ Finset.Ico 1 n, (n.choose i : ℤ) ∈ erdos_727285_T n`

## Proof failures (what broke, fed back into the next plan)

- cycle 1: `erdos_727285_hyp_S7_digits_spec` exit 3, 3 attempt(s); mode=fast: 1 proof round(s) (3 attempts) and 0 refinement round(s) exhausted without a sorry-free proof
- cycle 1: `erdos_727285_hyp_S21_choose_mem_T` exit 3, 3 attempt(s); mode=fast: 1 proof round(s) (3 attempts) and 0 refinement round(s) exhausted without a sorry-free proof
- cycle 1: `erdos_727285_hyp_S21a_phi_le_hyp_tower` exit 3, 3 attempt(s); mode=fast: 1 proof round(s) (3 attempts) and 0 refinement round(s) exhausted without a sorry-free proof
- cycle 1: `erdos_727285_hyp_S21a_phi_le_hyp_large` exit 3, 3 attempt(s); mode=fast: 1 proof round(s) (3 attempts) and 0 refinement round(s) exhausted without a sorry-free proof
- cycle 1: `erdos_727285_hyp_S11_tower_step_hyp_case_lt` exit 3, 3 attempt(s); mode=fast: 1 proof round(s) (3 attempts) and 0 refinement round(s) exhausted without a sorry-free proof
- cycle 1: `erdos_727285_hyp_S11_tower_step_hyp_case_top` exit 3, 3 attempt(s); run budget exhausted after fast mode: run budget $0.6 exhausted (spent $0.68)
- cycle 1: `erdos_727285_hyp_S11_tower_step_hyp_other_primes` exit 2, 3 attempt(s); mode=fast: 1 proof round(s) (3 attempts) and 0 refinement round(s) exhausted without a sorry-free proof
  - unsolved goal: `n : ℕ hn : erdos_727285_Good n p : ℕ hp : p ∈ n.primeFactors q : ℕ hq : q ∈ n.primeFactors hqp : q ≠ p d : ℕ hd : d ∈ Finset.Icc 1 (n.factorization p) r : ℤ hC : ↑q ^ n.factorization q ∣ ↑(n.choose (p`
- cycle 1: `erdos_727285_hyp_S11_case_top` exit 3, 3 attempt(s); mode=fast: 1 proof round(s) (3 attempts) and 0 refinement round(s) exhausted without a sorry-free proof

## Moves the plan made in response

- cycle 1: `erdos_727285_hyp_S21a_phi_le_hyp_tower` → **defer** — Certified; no longer needed separately.
- cycle 1: `erdos_727285_hyp_S21a_phi_le_hyp_large` → **defer** — Absorbed into the certified S21a.
- cycle 2: `erdos_727285_hyp_S11_case_top` → **lemma** — Both attempts reduced to two sorry'd helpers (key_digits, carry_bound) and then broke on the sum algebra. I state those two facts as hypotheses: the digit fact in pointwise weighted form, and the carry bound as an ite-su
- cycle 2: `erdos_727285_hyp_S21a_phi_le_hyp_tower` → **defer** — Superseded: S21a is certified.
- cycle 2: `erdos_727285_hyp_S21a_phi_le_hyp_large` → **defer** — Superseded: S21a is certified.
- cycle 2: `erdos_727285_hyp_S11_tower_step_hyp_case_lt` → **defer** — Superseded: S11_case_lt is certified.
- cycle 2: `erdos_727285_hyp_S11_tower_step_hyp_case_top` → **lemma** — Same as S11_case_top; split into top_pointwise and S10_carry.
- cycle 2: `erdos_727285_hyp_S11_tower_step_hyp_other_primes` → **defer** — Superseded: other_primes is now glue from phiP_congr and S4b_other.

## Refuted statements (never re-propose)

- (none)
