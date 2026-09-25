open Filter
open scoped Nat

def admissibleCounts (n : ℕ) : Set ℕ :=
  { t + 1 | (t) (_ : ∃ a : Fin (t + 1) → ℕ, (n)! = ∏ i, a i ∧
      Monotone a ∧ a (Fin.last t) ≤ n ^ 2) }

-- Elementary: for n > 0 take t = n - 1 and a i = i + 1. The product is n!, the tuple is
-- monotone, and the last factor is n ≤ n^2. Only makes the set nonempty so that sInf is its least element.
theorem erdos_95503_neg_hyp_nonempty : ∀ n : ℕ, 0 < n → (admissibleCounts n).Nonempty := by
  sorry

-- The core, stated without A. The target is the negation of the little-o claim.
-- R1 and Stirling show the normalized error is bounded below, so the conjecture can only fail
-- if admissible counts are infinitely often too LARGE by a margin c·n/log n.
-- Any counterexample must satisfy this (see the DERIVATION lines, with 0 < c ≤ 1/2).
theorem erdos_95503_neg_hyp_gap : ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 2 ≤ n ∧
    ∀ s ∈ admissibleCounts n,
      (n : ℝ) / 2 - n / (2 * Real.log n) + c * (n / Real.log n) ≤ (s : ℝ) := by
  sorry

theorem erdos_95503_neg : ¬ (∀ (A : ℕ → ℕ), (∀ n > 0,
    IsLeast { t + 1 | (t) (_ : ∃ a : Fin (t + 1) → ℕ, (n)! = ∏ i, a i ∧
      Monotone a ∧ a (Fin.last t) ≤ n ^ 2) } (A n)) →
    ((fun (n : ℕ) => (A n - n / 2 + n / (2 * Real.log n) : ℝ)) =o[atTop] fun n => n / Real.log n)) := by
  intro hall
  classical
  obtain ⟨c, hc, hgap⟩ := erdos_95503_neg_hyp_gap
  have hA : ∀ n : ℕ, n > 0 → IsLeast (admissibleCounts n) (sInf (admissibleCounts n)) :=
    fun n hn => ⟨Nat.sInf_mem (erdos_95503_neg_hyp_nonempty n hn), fun x hx => Nat.sInf_le hx⟩
  have ho := hall (fun n => sInf (admissibleCounts n)) (fun n hn => hA n hn)
  have hev := ho.def (half_pos hc)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  obtain ⟨n, hnN, hn2, hbound⟩ := hgap N
  have hmem := (hA n (by omega)).1
  have h1 := hbound (sInf (admissibleCounts n)) hmem
  have h2 : ‖((sInf (admissibleCounts n) : ℕ) : ℝ) - (n : ℝ) / 2 + (n : ℝ) / (2 * Real.log n)‖
      ≤ c / 2 * ‖(n : ℝ) / Real.log n‖ := hN n hnN
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have hq : 0 < (n : ℝ) / Real.log n := div_pos hnpos hlog
  rw [Real.norm_of_nonneg hq.le] at h2
  have h3 := le_trans (Real.le_norm_self _) h2
  nlinarith [mul_pos hc hq]