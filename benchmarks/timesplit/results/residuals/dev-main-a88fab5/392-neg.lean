open Filter
open scoped Nat

def erdos21397S (n : ℕ) : Set ℕ :=
  { t + 1 | (t) (_ : ∃ a : Fin (t + 1) → ℕ, (n)! = ∏ i, a i ∧
      Monotone a ∧ a (Fin.last t) ≤ n ^ 2) }

-- Derived (R1): the factors 1,2,…,n (t = n-1) are monotone, multiply to n!, and the last one is n ≤ n^2.
namespace erdos_21397_neg_hyp_nonempty_ns
open Filter

open scoped Nat

open Filter

open scoped Nat

theorem erdos_21397_neg_hyp_nonempty :
    ∀ n : ℕ, n > 0 → (erdos21397S n).Nonempty := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine ⟨m + 1, m, ⟨fun i => (i : ℕ) + 1, ?_, ?_, ?_⟩, rfl⟩
  · exact (Finset.prod_range_add_one_eq_factorial (m + 1)).symm.trans
      (Fin.prod_univ_eq_prod_range (fun i => i + 1) (m + 1)).symm
  · intro i j hij
    show (i : ℕ) + 1 ≤ (j : ℕ) + 1
    have h : (i : ℕ) ≤ j := hij
    omega
  · show (Fin.last m : ℕ) + 1 ≤ (m + 1) ^ 2
    rw [Fin.val_last]
    nlinarith
end erdos_21397_neg_hyp_nonempty_ns

theorem erdos_21397_neg_hyp_nonempty :
    ∀ n : ℕ, n > 0 → (erdos21397S n).Nonempty := by
  exact erdos_21397_neg_hyp_nonempty_ns.erdos_21397_neg_hyp_nonempty

-- Derived: n^n/n! is one term of the exponential series, so n^n/n! ≤ e^n
-- (Mathlib: Real.pow_div_factorial_le_exp (hx : 0 ≤ x) (n : ℕ)); then clear the denominator.
-- CHECK: Real.pow_div_factorial_le_exp div_le_iff₀ Real.log_le_log Real.log_mul Real.log_exp Real.log_pow
namespace erdos_21397_neg_hyp_pow_le_exp_mul_factorial_ns
-- CHECK: Real.pow_div_factorial_le_exp div_le_iff₀
open Filter

open scoped Nat

open Filter

open scoped Nat

theorem erdos_21397_neg_hyp_pow_le_exp_mul_factorial :
    ∀ n : ℕ, ((n : ℝ) ^ n) ≤ Real.exp (n : ℝ) * ((n)! : ℝ) := by
  intro n
  have h := Real.pow_div_factorial_le_exp (x := (n : ℝ)) (Nat.cast_nonneg n) n
  have hf : (0 : ℝ) < ((n)! : ℝ) := by exact_mod_cast Nat.factorial_pos n
  rw [div_le_iff₀ hf] at h
  exact h
end erdos_21397_neg_hyp_pow_le_exp_mul_factorial_ns

theorem erdos_21397_neg_hyp_pow_le_exp_mul_factorial :
    ∀ n : ℕ, ((n : ℝ) ^ n) ≤ Real.exp (n : ℝ) * ((n)! : ℝ) := by
  exact erdos_21397_neg_hyp_pow_le_exp_mul_factorial_ns.erdos_21397_neg_hyp_pow_le_exp_mul_factorial



-- Derived (R3) from the previous hypothesis: taking logs gives n log n - n ≤ log n!.
theorem erdos_21397_neg_hyp_stirling_lower :
    ∀ n : ℕ, 2 ≤ n →
      (n : ℝ) / 2 - n / (2 * Real.log n) - 2 ≤ Real.log ((n)! : ℝ) / (2 * Real.log n) := by
  intro n hn
  have h := erdos_21397_neg_hyp_pow_le_exp_mul_factorial n
  have hnR : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hnR
  have hf : (0 : ℝ) < ((n)! : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have h2 : (n : ℝ) * Real.log n ≤ n + Real.log ((n)! : ℝ) := by
    have h3 := Real.log_le_log (pow_pos hpos n) h
    rw [Real.log_pow, Real.log_mul (Real.exp_pos _).ne' hf.ne', Real.log_exp] at h3
    exact h3
  have h2L : (0 : ℝ) < 2 * Real.log n := by linarith
  rw [le_div_iff₀ h2L]
  have e : (n : ℝ) / (2 * Real.log n) * (2 * Real.log n) = n := div_mul_cancel₀ _ h2L.ne'
  have expand : ((n : ℝ) / 2 - n / (2 * Real.log n) - 2) * (2 * Real.log n)
      = (n : ℝ) * Real.log n - n - 4 * Real.log n := by
    rw [sub_mul, sub_mul, e]
    ring
  rw [expand]
  linarith

-- Derived (R4): a witness of the target needs total log-waste ≥ c·n in every factorization, infinitely often.
-- Stated as an excess over L(n) = log n!/(2 log n). The "+2" is harmless because n/log n → ∞.
theorem erdos_21397_neg_hyp_core :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 2 ≤ n ∧
      ∀ m ∈ erdos21397S n,
        c * ((n : ℝ) / Real.log n) + 2 ≤ (m : ℝ) - Real.log ((n)! : ℝ) / (2 * Real.log n) := by
  sorry

open Filter
open scoped Nat

theorem erdos_21397_neg : ¬ (∀ (A : ℕ → ℕ), (∀ n > 0,
    IsLeast { t + 1 | (t) (_ : ∃ a : Fin (t + 1) → ℕ, (n)! = ∏ i, a i ∧
      Monotone a ∧ a (Fin.last t) ≤ n ^ 2) } (A n)) →
    ((fun (n : ℕ) => (A n - n / 2 + n / (2 * Real.log n) : ℝ)) =o[atTop] fun n => n / Real.log n)) := by
  intro h
  have hne := erdos_21397_neg_hyp_nonempty
  obtain ⟨c, hc, hcore⟩ := erdos_21397_neg_hyp_core
  have hlo := h (fun n => sInf (erdos21397S n)) (by
    intro n hn
    show sInf (erdos21397S n) ∈ erdos21397S n ∧
      sInf (erdos21397S n) ∈ lowerBounds (erdos21397S n)
    exact ⟨Nat.sInf_mem (hne n hn), fun x hx => Nat.sInf_le hx⟩)
  have hb := hlo.bound (half_pos hc)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hb
  obtain ⟨n, hNn, hn2, hall⟩ := hcore N
  have hmem : sInf (erdos21397S n) ∈ erdos21397S n := Nat.sInf_mem (hne n (by omega))
  have hc1 := hall _ hmem
  have hst := erdos_21397_neg_hyp_stirling_lower n hn2
  have h1 := hN n hNn
  simp only [Real.norm_eq_abs] at h1
  have hnR : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hnR
  have hX : 0 < (n : ℝ) / Real.log n := div_pos (by linarith) hlog
  rw [abs_of_pos hX] at h1
  have h2 := (le_abs_self _).trans h1
  have hcX : 0 < c * ((n : ℝ) / Real.log n) := mul_pos hc hX
  have key : c / 2 * ((n : ℝ) / Real.log n) = c * ((n : ℝ) / Real.log n) / 2 := by ring
  rw [key] at h2
  linarith