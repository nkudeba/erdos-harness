# Residual — Erdős #41635 (after cycle 3, 2026-10-14T17:31:24Z)

**Nothing here resolves the problem.** A residual skeleton is a certified conditional theorem: the frozen target follows by machine-checked glue from the hypotheses below. The OPEN hypotheses are the residual; the problem is exactly as open as they are.

Skeleton: `/Users/nicolas.kudeba/workspace/erdos-harness/programs/erdos_41635/Residual.lean`

| open conjectures | published premises | discharged (certified) | complexity of open conjectures |
|---|---|---|---|
| 0 | 2 | 17 | 0 |

| hypothesis | kind | status | complexity | derivation / source |
|---|---|---|---|---|
| `erdos_41635_hyp_pasch` | conjecture | certified | 23 |  |
| `erdos_41635_hyp_cs_pair` | conjecture | certified | 10 |  |
| `erdos_41635_hyp_octahedra` | conjecture | certified | 10 |  |
| `erdos_41635_hyp_box` | conjecture | certified | 27 |  |
| `erdos_41635_hyp_upper_hyp_pasch` | conjecture | certified | 14 |  |
| `erdos_41635_hyp_upper_hyp_hom_upper` | conjecture | certified | 10 |  |
| `erdos_41635_hyp_upper_hyp_octa_cs` | conjecture | certified | 6 |  |
| `erdos_41635_hyp_upper_hyp_box_to_bound_hyp_pi_floor` | conjecture | certified | 4 | S1.1.1: for x ≥ 0 and a natural p, p ≤ x iff p ≤ ⌊x⌋₊ (Nat.le_floor_iff), so the subtype {p prime, p ≤ x} is in bijection with the primes ≤ ⌊x⌋₊, whose count is |
| `erdos_41635_hyp_upper_hyp_box_to_bound_hyp_rs_upper` | published | premise (published, not formalised here) | 5 | Rosser, Schoenfeld, Illinois J. Math. 6 (1962), Theorem 1, Corollary 1, (3.6) |
| `erdos_41635_hyp_upper_hyp_box_to_bound_hyp_rs_lower` | published | premise (published, not formalised here) | 4 | Rosser, Schoenfeld, Illinois J. Math. 6 (1962), Theorem 1, Corollary 1, (3.5) |
| `erdos_41635_hyp_upper_hyp_box_to_bound_hyp_rough` | conjecture | certified | 18 | S2 bullet 1: /{1} ∪ primes ≤ n/ = π(n)+1 < 1.26 n/ln n + 1 ≤ C n lnln n/ln n for n ≥ 16, since lnln 16 > 1. |
| `erdos_41635_hyp_upper_hyp_box_to_bound_hyp_smooth_tail` | conjecture | certified | 18 | S2 Case E with y0 = (ln n)^20, so ln y0 = 20 lnln n. The count of a ≤ n with a/P(a) y0-smooth is ≤ Σ_{m≤√n, smooth} π(n/m) + n Σ_{m>√n, smooth} 1/m. The first s |
| `erdos_41635_hyp_upper_hyp_box_to_bound_hyp_box_part` | conjecture | certified | 30 | S2 Cases G/S: dyadic boxes Z_{l,j} x Q_j x P_k, the injective decomposition, box sparsity giving /T_B/ <= (3/m_B)^{1/8}/B/, and mass sums |
| `erdos_41635_hyp_upper_hyp_box_to_bound` | conjecture | certified | 17 | Blueprint S1.7-S1.16 (S2 of the refereed informal proof): split A into 1/primes, the injective decomposition a=s*q*P(a) into dyadic boxes Z_{l,j} x Q_j x Q_k, C |
| `erdos_41635_hyp_upper` | conjecture | certified | 16 | Blueprint S15. Split A into four parts: 1 and primes (S5); Case G and Case S boxes, bounded by the certified erdos_41635_hyp_box together with S8–S12; and the r |
| `erdos_41635_hyp_sq_cancel` | conjecture | certified | 6 |  |
| `erdos_41635_hyp_Sn_valid` | conjecture | certified | 3 |  |
| `erdos_41635_hyp_mertens_lower` | conjecture | certified | 5 |  |
| `erdos_41635_hyp_Sn_card_lower` | conjecture | certified | 12 |  |

Statements:

- `erdos_41635_hyp_pasch` : `∀ (n : ℕ) (A : Finset ℕ), ErdosValid41635 A n → ∀ x1 x2 y1 y2 z1 z2 : ℕ, 0 < x1 → 0 < x2 → 0 < y1 → 0 < y2 → 0 < z1 → 0 < z2 → x1 ≠ x2 → y1 ≠ y2 → z1 ≠ z2 → ¬ (x1 * y1 * z1 ∈ A ∧ x1 * y2 * z2 ∈ A ∧ x2 * y1 * z2 ∈ A ∧ x2 * y2 * z1 ∈ A)`
- `erdos_41635_hyp_cs_pair` : `∀ (X Y : Finset ℕ) (G : Finset (ℕ × ℕ)), G ⊆ X ×ˢ Y → X.Nonempty → Y.Nonempty → (G.card : ℝ) ^ 4 ≤ (X.card : ℝ) ^ 2 * (Y.card : ℝ) ^ 2 * ∑ y1 ∈ Y, ∑ y2 ∈ Y, (((X.filter (fun x => (x, y1) ∈ G ∧ (x, y2) ∈ G)).card : ℝ)) ^ 2`
- `erdos_41635_hyp_octahedra` : `∀ (X Y Z : Finset ℕ) (T : Finset (ℕ × ℕ × ℕ)), T ⊆ X ×ˢ (Y ×ˢ Z) → X.Nonempty → Y.Nonempty → Z.Nonempty → (T.card : ℝ) ^ 8 ≤ ((X.card : ℝ) * Y.card * Z.card) ^ 6 * (erdosOctaHom X Y Z T : ℝ)`
- `erdos_41635_hyp_box` : `∀ (n : ℕ) (A : Finset ℕ), ErdosValid41635 A n → ∀ (X Y Z : Finset ℕ), X.Nonempty → Y.Nonempty → Z.Nonempty → (∀ x ∈ X, 0 < x) → (∀ y ∈ Y, 0 < y) → (∀ z ∈ Z, 0 < z) → (((X ×ˢ (Y ×ˢ Z)).filter (fun t => t.1 * t.2.1 * t.2.2 ∈ A)).card : ℝ) ^ 8 * ((min X.card (min Y.card Z.card) : ℕ) : ℝ) ≤ 3 * ((X.card : ℝ) * Y.card * Z.card) ^ 8`
- `erdos_41635_hyp_upper_hyp_pasch` : `∀ (A : Finset ℕ) (n : ℕ), A ⊆ Finset.Ioc 0 n → (∀ᵉ (a ∈ A) (b ∈ A) (c ∈ A) (d ∈ A), a ≤ b → b ≤ c → c ≤ d → IsSquare (a * b * c * d) → a * d = b * c) → erdosPaschFree A`
- `erdos_41635_hyp_upper_hyp_hom_upper` : `∀ (A : Finset ℕ), erdosPaschFree A → ∀ X Y Z : Finset ℕ, erdosOctaHom X Y Z (erdosBoxTriples A X Y Z) ≤ X.card * Y.card ^ 2 * Z.card ^ 2 + X.card ^ 2 * Y.card * Z.card ^ 2 + X.card ^ 2 * Y.card ^ 2 * Z.card`
- `erdos_41635_hyp_upper_hyp_octa_cs` : `∀ (X Y Z : Finset ℕ) (T : Finset (ℕ × ℕ × ℕ)), T ⊆ X ×ˢ (Y ×ˢ Z) → T.card ^ 8 ≤ erdosOctaHom X Y Z T * (X.card * Y.card * Z.card) ^ 6`
- `erdos_41635_hyp_upper_hyp_box_to_bound_hyp_pi_floor` : `∀ x : ℝ, 0 ≤ x → erdosPiReal x = Nat.primeCounting ⌊x⌋₊`
- `erdos_41635_hyp_upper_hyp_box_to_bound_hyp_rs_upper` : `∀ x : ℝ, 1 < x → (erdosPiReal x : ℝ) < 1.25506 * x / Real.log x`
- `erdos_41635_hyp_upper_hyp_box_to_bound_hyp_rs_lower` : `∀ x : ℝ, 17 ≤ x → x / Real.log x < (erdosPiReal x : ℝ)`
- `erdos_41635_hyp_upper_hyp_box_to_bound_hyp_rough` : `(∀ x : ℝ, 1 < x → (Nat.primeCounting ⌊x⌋₊ : ℝ) < 1.26 * x / Real.log x) → ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ((erdosRough n).card : ℝ) ≤ C * ((n : ℝ) * Real.log (Real.log n) / Real.log n)`
- `erdos_41635_hyp_upper_hyp_box_to_bound_hyp_smooth_tail` : `(∀ x : ℝ, 1 < x → (Nat.primeCounting ⌊x⌋₊ : ℝ) < 1.26 * x / Real.log x) → ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ((erdosSmoothTail n).card : ℝ) ≤ C * ((n : ℝ) * Real.log (Real.log n) / Real.log n)`
- `erdos_41635_hyp_upper_hyp_box_to_bound_hyp_box_part` : `(∀ x : ℝ, 1 < x → (Nat.primeCounting ⌊x⌋₊ : ℝ) < 1.26 * x / Real.log x) → (∀ x : ℝ, 17 ≤ x → x / Real.log x < (Nat.primeCounting ⌊x⌋₊ : ℝ)) → ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset ℕ, A ⊆ Finset.Ioc 0 n → erdosBoxSparse A → ((A \ (erdosRough n ∪ erdosSmoothTail n)).card : ℝ) ≤ C * ((n : ℝ) * Real.log (Real.log n) / Real.log n)`
- `erdos_41635_hyp_upper_hyp_box_to_bound` : `∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset ℕ, A ⊆ Finset.Ioc 0 n → erdosBoxSparse A → (A.card : ℝ) ≤ C * ((n : ℝ) * Real.log (Real.log n) / Real.log n)`
- `erdos_41635_hyp_upper` : `∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset ℕ, ErdosValid41635 A n → (A.card : ℝ) ≤ C * ((n : ℝ) * Real.log (Real.log n) / Real.log n)`
- `erdos_41635_hyp_sq_cancel` : `∀ x y z : ℕ, 0 < x → IsSquare (x ^ 2 * (y * z)) → IsSquare (y * z)`
- `erdos_41635_hyp_Sn_valid` : `∀ n : ℕ, ErdosValid41635 (erdosSpq n) n`
- `erdos_41635_hyp_mertens_lower` : `∀ x : ℝ, 1 < x → Real.log (Real.log x) - 1 < ∑ q ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, (1 / (q : ℝ))`
- `erdos_41635_hyp_Sn_card_lower` : `∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → c * ((n : ℝ) * Real.log (Real.log n) / Real.log n) ≤ ((erdosSpq n).card : ℝ)`

## Published premises (hypotheses, never axioms)

- `erdos_41635_hyp_rosser_schoenfeld` — Rosser, Schoenfeld, Illinois J. Math. 6 (1962), (3.5)-(3.6)
- `erdos_41635_hyp_pnt_dyadic` — PNT; Ramanujan 1919
- `erdos_41635_hyp_mertens` — Mertens 1874; Hardy-Wright Thm 427, 429
- `erdos_41635_hyp_upper_hyp_box_to_bound_hyp_rs_upper` — Rosser, Schoenfeld, Illinois J. Math. 6 (1962), Theorem 1, Corollary 1, (3.6)
- `erdos_41635_hyp_upper_hyp_box_to_bound_hyp_rs_lower` — Rosser, Schoenfeld, Illinois J. Math. 6 (1962), Theorem 1, Corollary 1, (3.5)
- `erdos_41635_hyp_upper_hyp_box_to_bound_hyp_rs_upper` — Rosser, Schoenfeld, Illinois J. Math. 6 (1962), Theorem 1, Corollary 1, (3.6)
- `erdos_41635_hyp_upper_hyp_box_to_bound_hyp_rs_lower` — Rosser, Schoenfeld, Illinois J. Math. 6 (1962), Theorem 1, Corollary 1, (3.5)

## Proof failures (what broke, fed back into the next plan)

- cycle 1: `erdos_41635_hyp_pasch` exit 2, 1 attempt(s); proof compiled but final verification (axioms/frozen/faithfulness) did not clear
- cycle 1: `erdos_41635_hyp_box` exit 2, 3 attempt(s); mode=fast: 1 proof round(s) (3 attempts) and 0 refinement round(s) exhausted without a sorry-free proof
- cycle 2: `erdos_41635_hyp_Sn_lower` exit 2, 8 attempt(s); mode=fast: 2 proof round(s) (8 attempts) and 0 refinement round(s) exhausted without a sorry-free proof
- cycle 2: `erdos_41635_hyp_upper` exit 2, 9 attempt(s); mode=fast: 2 proof round(s) (9 attempts) and 0 refinement round(s) exhausted without a sorry-free proof
- cycle 3: `erdos_41635_hyp_upper` exit 3, 0 attempt(s); deductive research program ran 1 of 1 cycle(s); residual: 1 open conjecture(s), 0 published premise(s) (see programs/erd
- cycle 4: `erdos_41635_hyp_upper` exit 3, 0 attempt(s); deductive research program ran 1 of 1 cycle(s); residual: 1 open conjecture(s), 0 published premise(s) (see programs/erd
- cycle 1: `erdos_41635_hyp_upper` exit 3, 0 attempt(s); deductive research program ran 1 of 1 cycle(s); residual: 1 open conjecture(s), 0 published premise(s) (see programs/erd
- cycle 2: `erdos_41635_hyp_upper` exit 3, 0 attempt(s); deductive research program ran 1 of 1 cycle(s); residual: 1 open conjecture(s), 0 published premise(s) (see programs/erd

## Moves the plan made in response

- cycle 1: `erdos_41635_hyp_box` → **lemma** — The missing Cauchy–Schwarz/octahedron counts were stated as cs_pair (S2) and octahedra (S3); all three are now certified.
- cycle 1: `erdos_41635_hyp_Sn_lower` → **split** — Replaced by the weaker constant-free Sn_card_lower (∃ c) plus positivity done in the glue; certified.
- cycle 1: `erdos_41635_hyp_upper` → **defer** — Genuine analytic core (S5–S15). Top-level splits raise the open count and were not adopted (cycles 2 and 4). The recursive child failed because its open piece quantified over box-sparse sets, which strengthens H. Next re
- cycle 2: `erdos_41635_hyp_box` → **defer** — Now certified in a later cycle; no change needed, it is used by name.
- cycle 2: `erdos_41635_hyp_Sn_lower` → **split** — Already superseded by the certified erdos_41635_hyp_Sn_card_lower (via mertens_lower and the pairSet count); the lower direction is closed.
- cycle 2: `erdos_41635_hyp_upper` → **defer** — Genuinely hard core. Top-level splits (smooth_count + rough_bound) lose the adoption metric, so it is kept whole. The recursive child must keep every open piece either A-free (smooth_count, S14) or quantified over ErdosV
- cycle 1: `erdos_41635_hyp_upper` → **defer** — This is the genuinely hard analytic core: Chebyshev, dyadic PNT and Mertens inputs plus the S8–S14 box decomposition. Top-level splits into smooth_count and rough_bound were rejected by the adoption metric because they r
- cycle 1: `erdos_41635_hyp_Sn_lower` → **lemma** — Already superseded by erdos_41635_hyp_Sn_card_lower, which is certified via mertens_lower and the pairSet count. The lower direction is closed.

## Refuted statements (never re-propose)

- (none)
