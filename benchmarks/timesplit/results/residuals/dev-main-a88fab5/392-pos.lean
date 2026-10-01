open Filter
open scoped Nat

-- Derived (R1): if n! = ∏ a_i with every a_i ≤ n^2, then n! ≤ (n^2)^t, so t ≥ log n!/(2 log n).
-- Combined with log n! ≥ n log n - n (from e^n ≥ n^n/n!), this gives t ≥ n/2 - n/(2 log n).
-- Verified numerically for 2 ≤ n ≤ 1500 by the refutation stage.
namespace erdos_21397_hyp_lower_ns
open Filter

open scoped Nat

open Filter

open scoped Nat

theorem erdos_21397_hyp_lower : ∀ n : ℕ, 2 ≤ n → ∀ t : ℕ, ∀ a : Fin t → ℕ,
    n ! = ∏ i, a i → (∀ i, a i ≤ n ^ 2) →
    (n : ℝ) / 2 - n / (2 * Real.log n) ≤ (t : ℝ) := by
  intro n hn t a hprod ha
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hL : 0 < Real.log n := Real.log_pos (by linarith)
  have hfacN : n ! ≤ (n ^ 2) ^ t := by
    rw [hprod]
    have := Finset.prod_le_pow_card Finset.univ a (n ^ 2) (fun i _ => ha i)
    simpa [Finset.card_univ, Fintype.card_fin] using this
  have hfac : ((n ! : ℕ) : ℝ) ≤ ((n:ℝ) ^ 2) ^ t := by exact_mod_cast hfacN
  have hlog1 : Real.log ((n ! : ℕ) : ℝ) ≤ t * (2 * Real.log n) := by
    have := Real.log_le_log (by positivity) hfac
    rw [Real.log_pow, Real.log_pow] at this
    push_cast at this
    linarith
  have hst : (n:ℝ) * Real.log n - n ≤ Real.log ((n ! : ℕ) : ℝ) := by
    have h := Real.pow_div_factorial_le_exp (x := (n:ℝ)) (by positivity) n
    rw [div_le_iff₀ (by positivity)] at h
    have h2 := Real.log_le_log (by positivity) h
    rw [Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_pow] at h2
    linarith
  have h1 : (n:ℝ) / (2 * Real.log n) * (2 * Real.log n) = n :=
    div_mul_cancel₀ _ (by positivity)
  by_contra hc
  push_neg at hc
  have := mul_lt_mul_of_pos_right hc hL
  nlinarith
end erdos_21397_hyp_lower_ns

theorem erdos_21397_hyp_lower : ∀ n : ℕ, 2 ≤ n → ∀ t : ℕ, ∀ a : Fin t → ℕ,
    n ! = ∏ i, a i → (∀ i, a i ≤ n ^ 2) →
    (n : ℝ) / 2 - n / (2 * Real.log n) ≤ (t : ℝ) := by
  exact erdos_21397_hyp_lower_ns.erdos_21397_hyp_lower



-- Hard core (upper construction): factorizations of n! into parts ≤ n^2 with total waste o(n).
-- Equivalent to the upper half of the target; believed proved in the 2025 factorial-decomposition
-- literature (unverified attribution), so stated as a conjecture rather than a published premise.
theorem erdos_21397_hyp_upper : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    ∃ s : ℕ, ∃ b : Fin (s + 1) → ℕ, n ! = ∏ i, b i ∧ Monotone b ∧ b (Fin.last s) ≤ n ^ 2 ∧
      ((s + 1 : ℕ) : ℝ) ≤ (n : ℝ) / 2 - n / (2 * Real.log n) + ε * ((n : ℝ) / Real.log n) := by
  sorry

open Filter
open scoped Nat

theorem erdos_21397 (A : ℕ → ℕ) (h : ∀ n > 0,
    IsLeast { t + 1 | (t) (_ : ∃ a : Fin (t + 1) → ℕ, (n)! = ∏ i, a i ∧
      Monotone a ∧ a (Fin.last t) ≤ n ^ 2) } (A n)) :
    ((fun (n : ℕ) => (A n - n / 2 + n / (2 * Real.log n) : ℝ)) =o[atTop] fun n => n / Real.log n) := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  filter_upwards [erdos_21397_hyp_upper c hc, eventually_ge_atTop 3] with n hn hn3
  have hpos : n > 0 := by omega
  have hn1 : (1:ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hL : 0 < Real.log n := Real.log_pos hn1
  have hg : 0 ≤ (n:ℝ) / Real.log n := div_nonneg (Nat.cast_nonneg n) hL.le
  have hcg : 0 ≤ c * ((n:ℝ) / Real.log n) := mul_nonneg hc.le hg
  obtain ⟨t, ⟨a, hprod, hmono, hlast⟩, hta⟩ := (h n hpos).1
  have hall : ∀ i, a i ≤ n ^ 2 := fun i => le_trans (hmono (Fin.le_last i)) hlast
  have hlow := erdos_21397_hyp_lower n (by omega) (t + 1) a hprod hall
  obtain ⟨s, b, hbprod, hbmono, hblast, hbound⟩ := hn
  have hmem : s + 1 ∈ { t + 1 | (t) (_ : ∃ a : Fin (t + 1) → ℕ, (n)! = ∏ i, a i ∧
      Monotone a ∧ a (Fin.last t) ≤ n ^ 2) } := ⟨s, ⟨b, hbprod, hbmono, hblast⟩, rfl⟩
  have hle : A n ≤ s + 1 := (h n hpos).2 hmem
  have hleR : (A n : ℝ) ≤ (s : ℝ) + 1 := by exact_mod_cast hle
  have htaR : ((t + 1 : ℕ) : ℝ) = (A n : ℝ) := by exact_mod_cast hta
  push_cast at htaR hlow hbound
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hg, abs_le]
  constructor <;> linarith