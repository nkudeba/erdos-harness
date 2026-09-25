open Filter
open scoped Nat

-- CHECK: Real.log_le_log Real.log_pow Real.log_mul Real.log_exp Filter.Frequently.and_eventually Asymptotics.IsLittleO.def div_mul_cancel₀
-- LOOGLE: ?x ^ ?n / (?n)! ≤ Real.exp ?x

-- Existence of the true minimal-factor function (R1): for each n > 0, a = (1,2,...,n) is a monotone witness
-- with product n! and last entry ≤ n ≤ n²; the set of lengths is a nonempty subset of ℕ, so sInf is least.
theorem erdos_29589_neg_hyp_exists :
    ∃ A : ℕ → ℕ, ∀ n > 0,
      IsLeast { t + 1 | (t) (_ : ∃ a : Fin (t + 1) → ℕ, (n)! = ∏ i, a i ∧
        Monotone a ∧ a (Fin.last t) ≤ n ^ 2) } (A n) := by
  sorry

-- Elementary Stirling-type lower bound: n^n/n! is one term of the series for e^n.
theorem erdos_29589_neg_hyp_fact_lower :
    ∀ n : ℕ, 1 ≤ n → ((n : ℝ) ^ n) ≤ ((n)! : ℝ) * Real.exp n := by
  sorry

-- Linear log-waste: optimal factorizations waste ≥ c·n in log for infinitely many n.
-- By the DERIVATION (S(n) = O(log n)), the target is equivalent to this.
-- Believed FALSE: the literature suggests the asymptotic holds, i.e. W*(n) = o(n).
theorem erdos_29589_neg_hyp_linear_waste :
    ∀ A : ℕ → ℕ, (∀ n > 0,
      IsLeast { t + 1 | (t) (_ : ∃ a : Fin (t + 1) → ℕ, (n)! = ∏ i, a i ∧
        Monotone a ∧ a (Fin.last t) ≤ n ^ 2) } (A n)) →
      ∃ c : ℝ, 0 < c ∧ ∃ᶠ n : ℕ in atTop,
        ((n)! : ℝ) * Real.exp (c * n) ≤ (n : ℝ) ^ (2 * A n) := by
  sorry

theorem erdos_29589_neg :
    ¬ (∀ (A : ℕ → ℕ), (∀ n > 0,
      IsLeast { t + 1 | (t) (_ : ∃ a : Fin (t + 1) → ℕ, (n)! = ∏ i, a i ∧
        Monotone a ∧ a (Fin.last t) ≤ n ^ 2) } (A n)) →
      ((fun (n : ℕ) => (A n - n / 2 + n / (2 * Real.log n) : ℝ)) =o[atTop] fun n => n / Real.log n)) := by
  intro hall
  obtain ⟨A, hA⟩ := erdos_29589_neg_hyp_exists
  have ho := hall A hA
  obtain ⟨c, hc, hfreq⟩ := erdos_29589_neg_hyp_linear_waste A hA
  have hev := ho.def (show (0:ℝ) < c / 4 by positivity)
  have hev3 : ∀ᶠ n : ℕ in atTop, 3 ≤ n := eventually_ge_atTop 3
  obtain ⟨n, hn1, hn2, hn3⟩ := (hfreq.and_eventually (hev.and hev3)).exists
  have hn2' : ‖(A n : ℝ) - (n : ℝ) / 2 + (n : ℝ) / (2 * Real.log n)‖
      ≤ c / 4 * ‖(n : ℝ) / Real.log n‖ := hn2
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hn2'
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1r : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hl : 0 < Real.log (n : ℝ) := Real.log_pos hn1r
  have hfac : (0 : ℝ) < ((n)! : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have H3 := erdos_29589_neg_hyp_fact_lower n (by omega)
  have e1 := Real.log_le_log (pow_pos hnpos n) H3
  rw [Real.log_pow, Real.log_mul hfac.ne' (Real.exp_pos _).ne', Real.log_exp] at e1
  have e2 := Real.log_le_log (mul_pos hfac (Real.exp_pos _)) hn1
  rw [Real.log_mul hfac.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_pow] at e2
  push_cast at e2
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = (n : ℝ) / (2 * Real.log n) := ⟨_, rfl⟩
  have hq : q * (2 * Real.log n) = n := by
    rw [hqdef]
    exact div_mul_cancel₀ _ (by linarith)
  have hqpos : 0 < q := by
    rw [hqdef]
    exact div_pos hnpos (by linarith)
  have hr : (n : ℝ) / Real.log n = 2 * q := by
    rw [hqdef]
    ring
  rw [← hqdef, hr, abs_of_pos (by linarith : (0 : ℝ) < 2 * q)] at hn2'
  have hexp : ((A n : ℝ) - n / 2 + q - c * q) * (2 * Real.log n)
      = 2 * (A n : ℝ) * Real.log n - n * Real.log n + n - c * n := by
    linear_combination (1 - c) * hq
  have hfq : c * q ≤ (A n : ℝ) - n / 2 + q := by
    by_contra hcon
    push_neg at hcon
    have hneg : ((A n : ℝ) - n / 2 + q - c * q) * (2 * Real.log n) < 0 :=
      mul_neg_of_neg_of_pos (by linarith) (by linarith)
    nlinarith
  have hcq : 0 < c * q := mul_pos hc hqpos
  have habs := le_abs_self ((A n : ℝ) - n / 2 + q)
  nlinarith