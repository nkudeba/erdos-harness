open Filter
open scoped Nat

-- Derived (R2, elementary): the list 1,2,...,n (t = n-1, a i = i+1) is a monotone factorization
-- of n! with last factor n <= n^2. So the defining set is nonempty for every n > 0, and the
-- unique A of the hypothesis exists as sInf.
theorem erdos_57606_neg_hyp_nonempty : ∀ n : ℕ, n > 0 →
    ({ t + 1 | (t) (_ : ∃ a : Fin (t + 1) → ℕ, (n)! = ∏ i, a i ∧
      Monotone a ∧ a (Fin.last t) ≤ n ^ 2) } : Set ℕ).Nonempty := by
  sorry

-- Derived necessary condition for a counterexample (R1 + the O(1) volume-bound analysis):
-- the negation holds iff some c > 0 and infinitely many n force every factorization of n!
-- into parts <= n^2 to use at least n/2 - n/(2 log n) + c n/log n factors.
-- Believed FALSE: the problem is reported solved affirmatively, and BFD packings give a
-- normalized excess of 0.029 at n = 12000, with the excess decreasing in n.
theorem erdos_57606_neg_hyp_waste : ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 2 ≤ n ∧
    ∀ (t : ℕ) (a : Fin (t + 1) → ℕ), (n)! = ∏ i, a i → Monotone a → a (Fin.last t) ≤ n ^ 2 →
      (n : ℝ) / 2 - n / (2 * Real.log n) + c * ((n : ℝ) / Real.log n) ≤ (t : ℝ) + 1 := by
  sorry

theorem erdos_57606_neg : ¬ (∀ (A : ℕ → ℕ), (∀ n > 0,
    IsLeast { t + 1 | (t) (_ : ∃ a : Fin (t + 1) → ℕ, (n)! = ∏ i, a i ∧
      Monotone a ∧ a (Fin.last t) ≤ n ^ 2) } (A n)) →
    ((fun (n : ℕ) => (A n - n / 2 + n / (2 * Real.log n) : ℝ)) =o[atTop] fun n => n / Real.log n)) := by
  intro h
  obtain ⟨c, hc, hn⟩ := erdos_57606_neg_hyp_waste
  have hne := erdos_57606_neg_hyp_nonempty
  have ho := h (fun n => sInf { t + 1 | (t) (_ : ∃ a : Fin (t + 1) → ℕ, (n)! = ∏ i, a i ∧
      Monotone a ∧ a (Fin.last t) ≤ n ^ 2) })
    (fun n hn0 => ⟨Nat.sInf_mem (hne n hn0), by intro x hx; exact Nat.sInf_le hx⟩)
  have hb := ho.def (half_pos hc)
  rw [Filter.eventually_atTop] at hb
  obtain ⟨N, hN⟩ := hb
  obtain ⟨n, hNn, h2, hall⟩ := hn N
  have hmem := Nat.sInf_mem (hne n (by omega))
  obtain ⟨t, ⟨a, hprod, hmono, hlast⟩, ht⟩ := hmem
  have key := hall t a hprod hmono hlast
  have hb' := hN n hNn
  simp only [Real.norm_eq_abs] at hb'
  rw [← ht] at hb'
  push_cast at hb'
  have hlog : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hx : 0 < (n : ℝ) / Real.log n := div_pos (by positivity) hlog
  rw [abs_of_pos hx] at hb'
  have habs := le_abs_self ((t : ℝ) + 1 - n / 2 + n / (2 * Real.log n))
  have hcx := mul_pos hc hx
  linarith