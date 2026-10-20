# Residual — Erdős #95799 (after cycle 1, 2026-10-20T09:05:14Z)

**Nothing here resolves the problem.** A residual skeleton is a certified conditional theorem: the frozen target follows by machine-checked glue from the hypotheses below. The OPEN hypotheses are the residual; the problem is exactly as open as they are.

Skeleton: `/Users/nicolas.kudeba/workspace/erdos-harness/programs/erdos_95799/Residual.lean`

| open conjectures | published premises | discharged (certified) | complexity of open conjectures |
|---|---|---|---|
| 0 | 0 | 14 | 0 |

| hypothesis | kind | status | complexity | derivation / source |
|---|---|---|---|---|
| `erdos_95799_hyp_cheb` | conjecture | certified | 5 | Certified in Lean (namespace erdos_95799_hyp_cheb_ns). Chebyshev-type bound: #primes in (K,6K] ≤ K/5 for K ≥ e^100. |
| `erdos_95799_hyp_param` | conjecture | certified | 8 | Certified in Lean (namespace erdos_95799_hyp_param_ns). Numerics: 2T-1 < L·∏(h/p) with T = ⌈e^K⌉+h and L = ⌊e^{2K}⌋. |
| `erdos_95799_hyp_count_hyp_char` | conjecture | certified | 0 | Complex.exp_add, Complex.exp_conj, induction on n |
| `erdos_95799_hyp_count_hyp_square` | conjecture | certified | 1 | Complex.mul_conj, map_sum, Finset.sum_mul_sum, S1.1 |
| `erdos_95799_hyp_count_hyp_fiber` | conjecture | certified | 0 | explicit bijection with a shifted range, omega side goals |
| `erdos_95799_hyp_count_hyp_regroup` | conjecture | certified | 1 | Finset.sum_product, sum_fiberwise_of_maps_to, sum_const, S1.4 |
| `erdos_95799_hyp_count_hyp_fejer` | conjecture | certified | 2 | combine S1.2 and S1.5, scale by 1/L |
| `erdos_95799_hyp_count_hyp_lower_hyp_one` | conjecture | certified | 0 | Frequency set {0}, coefficient 1; ee95799 (m*0) = exp 0 = 1. |
| `erdos_95799_hyp_count_hyp_lower_hyp_mul` | conjecture | certified | 10 | Take the frequency set (s ×ˢ t).image (+) and coefficient c'(θ) = sum over pairs with x+y = θ of c x * d y. Then ee(m x) * ee(m y) = ee(m(x+y)) and the coeffici |
| `erdos_95799_hyp_count_hyp_lower_hyp_single` | conjecture | certified | 6 | For p >= 2h, gw(h,p,.) is the autocorrelation 1_J * 1_{-J} of J = {0..h-1} on Z/p. Its DFT is /sum_{j<h} e(bj/p)/^2 >= 0 and its mean is h^2/p. Fourier inversio |
| `erdos_95799_hyp_count_hyp_lower` | conjecture | certified | 13 | C1 steps (1)-(3): g_p=1_J*1_{-J} with no wrap since p>=2h, so its transform is >=0; CRT product; Parseval against the Fejer kernel. Numerically checked as the I |
| `erdos_95799_hyp_count_hyp_count` | conjecture | certified | 26 | C1 step (4): 0<=wF<=1_G on (-L,L), G is symmetric, and (-T,T) holds 2T-1 integers |
| `erdos_95799_hyp_count` | conjecture | certified | 19 | Certified in Lean (namespace erdos_95799_hyp_count_ns, 633 lines). Fejér positivity plus orthogonality plus symmetry of G. |
| `erdos_95799_hyp_shift` | conjecture | certified | 14 | Certified in Lean (namespace erdos_95799_hyp_shift_ns). Pigeonhole for p ≤ ⌊log n⌋; the G-condition handles the remaining primes. |

Statements:

- `erdos_95799_hyp_cheb` : `∀ K : ℕ, Real.exp 100 ≤ (K : ℝ) → (((ePset K).card : ℕ) : ℝ) ≤ (K : ℝ) / 5`
- `erdos_95799_hyp_param` : `∀ K : ℕ, Real.exp 100 ≤ (K : ℝ) → (((ePset K).card : ℕ) : ℝ) ≤ (K : ℝ) / 5 → 2 * (((⌈Real.exp (K : ℝ)⌉₊ + (K + 1) / 2 : ℕ)) : ℝ) - 1 < ((⌊Real.exp (2 * (K : ℝ))⌋₊ : ℕ) : ℝ) * ∏ p ∈ ePset K, (((((K + 1) / 2 : ℕ)) : ℝ) / (p : ℝ))`
- `erdos_95799_hyp_count_hyp_char` : `S11Prop95799`
- `erdos_95799_hyp_count_hyp_square` : `S11Prop95799 → S12Prop95799`
- `erdos_95799_hyp_count_hyp_fiber` : `S14Prop95799`
- `erdos_95799_hyp_count_hyp_regroup` : `S14Prop95799 → S15Prop95799`
- `erdos_95799_hyp_count_hyp_fejer` : `S12Prop95799 → S15Prop95799 → S16Prop95799`
- `erdos_95799_hyp_count_hyp_lower_hyp_one` : `NonnegTrig95799 (fun _ => (1 : ℝ)) 1`
- `erdos_95799_hyp_count_hyp_lower_hyp_mul` : `∀ (F G : ℤ → ℝ) (a b : ℝ), 0 ≤ a → 0 ≤ b → NonnegTrig95799 F a → NonnegTrig95799 G b → NonnegTrig95799 (fun m => F m * G m) (a * b)`
- `erdos_95799_hyp_count_hyp_lower_hyp_single` : `∀ h p : ℕ, 1 ≤ h → 2 * h ≤ p → NonnegTrig95799 (fun m => gw95799 h p m / (h : ℝ)) ((h : ℝ) / (p : ℝ))`
- `erdos_95799_hyp_count_hyp_lower` : `S16Prop95799 → ∀ (h L : ℕ) (P : Finset ℕ), 1 ≤ h → 1 ≤ L → (∀ p ∈ P, Nat.Prime p ∧ 2 * h ≤ p) → (L : ℝ) * ∏ p ∈ P, ((h : ℝ) / (p : ℝ)) ≤ Fsum95799 h L P`
- `erdos_95799_hyp_count_hyp_count` : `∀ (h L T : ℕ) (P : Finset ℕ), 1 ≤ h → 1 ≤ T → (∀ p ∈ P, Nat.Prime p ∧ 2 * h ≤ p) → 2 * (T : ℝ) - 1 < Fsum95799 h L P → ∃ m : ℤ, (T : ℤ) ≤ m ∧ m < (L : ℤ) ∧ ∀ p ∈ P, ∃ d : ℤ, |d| ≤ (h : ℤ) - 1 ∧ (p : ℤ) ∣ m - d`
- `erdos_95799_hyp_count` : `∀ (h L T : ℕ) (P : Finset ℕ), 1 ≤ h → 1 ≤ T → (∀ p ∈ P, Nat.Prime p ∧ 2 * h ≤ p) → 2 * (T : ℝ) - 1 < (L : ℝ) * ∏ p ∈ P, ((h : ℝ) / (p : ℝ)) → ∃ m : ℤ, (T : ℤ) ≤ m ∧ m < (L : ℤ) ∧ erdosG h P m`
- `erdos_95799_hyp_shift` : `∀ (K n : ℕ), 3 ≤ K → Real.exp (K : ℝ) ≤ (n : ℝ) → erdosG ((K + 1) / 2) (ePset K) ((n : ℤ) + (((K + 1) / 2 : ℕ) : ℤ)) → ∀ p : ℕ, p ≤ 6 * K → p.Prime → p ∣ ∏ i ∈ Finset.Icc 1 ⌊Real.log n⌋₊, (n + i)`

## Proof failures (what broke, fed back into the next plan)

- cycle 1: `(skeleton)` exit None, 1 attempt(s); skeleton rejected: does not compile: line 64:16: Unknown identifier `erdos_95799_hyp_cheb_ns.erdos_95799_hyp_cheb`
- cycle 2: `(skeleton)` exit None, 1 attempt(s); skeleton rejected: a sorry outside the hypothesis lemmas: the glue is not glue
- cycle 1: `erdos_95799_hyp_count_hyp_count` exit 3, 3 attempt(s); mode=fast: 1 proof round(s) (3 attempts) and 0 refinement round(s) exhausted without a sorry-free proof
  - unsolved goal: `h p : ℕ hp : 0 < p m : ℤ hg : max 0 (↑h - ↑(cdist95799 p m)) ≠ 0 hlt : ↑(cdist95799 p m) < ↑h hlt' : min (m % ↑p) (↑p - m % ↑p) < ↑h hp' : 0 < ↑p h0 : 0 ≤ m % ↑p h1 : m % ↑p < ↑p ⊢ ∃ d, |d| ≤ ↑h - 1 ∧`

## Moves the plan made in response

- cycle 1: `skeleton (cycle 2, sorry outside hypotheses)` → **split** — No inlined proofs in the glue any more. The whole Fourier/counting part is one hypothesis (hyp_count, S1-S5), and the shift is one hypothesis (S6). The glue contains only casts, omega and linarith.
- cycle 2: `erdos_95799_hyp_count_hyp_count` → **split** — The failure was the S3(c) extraction step: from cdist < h get d with |d| <= h-1 and p | m-d. It broke only on the nonexistent name Int.ediv_add_emod; Int.emod_add_ediv / Int.ediv_add_emod' are the usual names. The recurs
- cycle 3: `erdos_95799_hyp_count_hyp_count` → **defer** — Nothing to change: this was proved in cycle 2 (verified) after the cycle-1 failure, which was caused by the invented name Int.ediv_add_emod. It is now in Lemmas.lean.
- cycle 3: `erdos_95799_hyp_count_hyp_lower` → **defer** — Superseded and not needed. The parent erdos_95799_hyp_count is certified (633-line namespace), so the S4 lower bound no longer appears as an open premise in the skeleton.
- cycle 4: `erdos_95799_hyp_count_hyp_count` → **lemma** — The cycle-1 failure was an invented name (Int.ediv_add_emod) in the S3(c) residue step. The fact was isolated as good95799, proved using Int.emod_add_ediv_mul, and the lemma was certified in cycle 2. Nothing is left open
- cycle 1: `erdos_95799_hyp_count_hyp_count` → **lemma** — The only breakage was an invented name (Int.ediv_add_emod) in the S3(c) residue step. The certified version supplies this as the private lemma good95799, using Int.emod_add_ediv_mul, and was verified in cycle 2. No open 
- cycle 1: `erdos_95799_hyp_count_hyp_count` → **lemma** — The cycle-1 failure needed Euclidean decomposition plus the centred-residue choice of d. That fact is now the certified private lemma good95799, which uses Int.emod_add_ediv_mul instead of the nonexistent Int.ediv_add_em
- cycle 1: `skeleton (cycles 1-2 rejections)` → **define** — Both rejections concerned earlier skeletons: an unknown namespace identifier and a sorry in the glue. The skeleton in force compiles with the harness-restored namespaces and has no sorry outside the certified lemmas.

## Refuted statements (never re-propose)

- `erdos_95799_hyp_positivity` : `∀ (h L : ℕ) (P : Finset ℕ), 1 ≤ h → 1 ≤ L → (∀ p ∈ P, p.Prime ∧ h ≤ p) → (L : ℝ) * ∏ p ∈ P, ((h : ℝ) / (p : ℝ)) ≤ Ssum h L P` — witness `{"h": 2, "L": 2, "P": [2]}` (numerical, not Lean-certified)
- `erdos_95799_hyp_positivity` : `∀ (h L : ℕ) (P : Finset ℕ), 1 ≤ h → 1 ≤ L → (∀ p ∈ P, p.Prime ∧ h ≤ p) → (L : ℝ) * ∏ p ∈ P, ((h : ℝ) / (p : ℝ)) ≤ Ssum h L P` — witness `{"h": 2, "L": 2, "P": [2]}` (numerical, not Lean-certified)
