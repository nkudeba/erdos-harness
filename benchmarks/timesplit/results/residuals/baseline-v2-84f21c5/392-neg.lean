open Filter
open scoped Nat

def erdos37270FactSet (n : ℕ) : Set ℕ :=
  { t + 1 | (t) (_ : ∃ a : Fin (t + 1) → ℕ, (n)! = ∏ i, a i ∧
      Monotone a ∧ a (Fin.last t) ≤ n ^ 2) }

-- Derived (R1): for n > 0 the set is nonempty, witnessed by a = (1,2,...,n) padded
-- by leading 1s. So Nat.sInf_mem gives membership and Nat.sInf_le gives minimality.
theorem erdos_37270_neg_hyp_isLeast_sInf :
    ∀ n > 0, IsLeast (erdos37270FactSet n) (sInf (erdos37270FactSet n)) := by
  sorry

-- Derived (R2/R3): the error term is bounded below by 1/(2 log n) > 0. So the negation of the
-- little-o statement for the true minimum A(n) = sInf is exactly this infinitely-often
-- positive-density excess. A counterexample must satisfy it.
theorem erdos_37270_neg_hyp_io_excess :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, ∃ n ≥ N,
      c * ((n : ℝ) / Real.log n) ≤
        ((sInf (erdos37270FactSet n) : ℕ) : ℝ) - n / 2 + n / (2 * Real.log n) := by
  sorry

theorem erdos_37270_neg : ¬ (∀ (A : ℕ → ℕ), (∀ n > 0,
    IsLeast { t + 1 | (t) (_ : ∃ a : Fin (t + 1) → ℕ, (n)! = ∏ i, a i ∧
      Monotone a ∧ a (Fin.last t) ≤ n ^ 2) } (A n)) →
    ((fun (n : ℕ) => (A n - n / 2 + n / (2 * Real.log n) : ℝ)) =o[atTop] fun n => n / Real.log n)) := by
  intro h
  have ho := h (fun n => sInf (erdos37270FactSet n)) erdos_37270_neg_hyp_isLeast_sInf
  obtain ⟨c, hc, hio⟩ := erdos_37270_neg_hyp_io_excess
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (ho.def (half_pos hc))
  obtain ⟨n, hn, hge⟩ := hio (max N 2)
  have h1 := hN n (le_of_max_le_left hn)
  have hn2' : 2 ≤ n := le_of_max_le_right hn
  have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn2'
  have hlog : 0 < Real.log n := Real.log_pos (by linarith)
  have hq : 0 < (n:ℝ) / Real.log n := div_pos (by linarith) hlog
  simp only [Real.norm_eq_abs] at h1
  rw [abs_of_pos hq] at h1
  have habs := le_abs_self
    (((sInf (erdos37270FactSet n) : ℕ) : ℝ) - n / 2 + n / (2 * Real.log n))
  have hcq : 0 < c * ((n:ℝ) / Real.log n) := mul_pos hc hq
  linarith