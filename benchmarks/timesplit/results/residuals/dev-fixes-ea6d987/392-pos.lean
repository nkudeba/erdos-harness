open Filter
open scoped Nat

-- Derived (R2, volume bound): every factor is ≤ a (Fin.last t) ≤ n^2 by monotonicity,
-- so n! = ∏ a i ≤ (n^2)^(t+1); now take logarithms. Elementary.
namespace erdos_29589_hyp_volume_ns
open Filter

open scoped Nat

theorem erdos_29589_hyp_volume : ∀ n : ℕ, 2 ≤ n → ∀ t : ℕ,
    (∃ a : Fin (t + 1) → ℕ, (n)! = ∏ i, a i ∧ Monotone a ∧ a (Fin.last t) ≤ n ^ 2) →
    Real.log ((n)! : ℝ) ≤ 2 * ((t : ℝ) + 1) * Real.log (n : ℝ) := by
  intro n hn t ⟨a, hprod, hmono, hlast⟩
  have hle : ∀ i, a i ≤ n ^ 2 := fun i => (hmono (Fin.le_last i)).trans hlast
  have hnat : (n)! ≤ (n ^ 2) ^ (t + 1) := by
    rw [hprod]
    calc ∏ i, a i ≤ ∏ _i : Fin (t+1), n ^ 2 :=
          Finset.prod_le_prod (fun i _ => Nat.zero_le _) (fun i _ => hle i)
      _ = (n ^ 2) ^ (t + 1) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hreal : ((n)! : ℝ) ≤ (n : ℝ) ^ (2 * (t + 1)) := by
    rw [pow_mul]; exact_mod_cast hnat
  have hpos : (0:ℝ) < (n)! := by exact_mod_cast Nat.factorial_pos n
  calc Real.log ((n)! : ℝ) ≤ Real.log ((n:ℝ) ^ (2 * (t + 1))) := Real.log_le_log hpos hreal
    _ = 2 * ((t:ℝ) + 1) * Real.log n := by rw [Real.log_pow]; push_cast; ring
end erdos_29589_hyp_volume_ns

theorem erdos_29589_hyp_volume : ∀ n : ℕ, 2 ≤ n → ∀ t : ℕ,
    (∃ a : Fin (t + 1) → ℕ, (n)! = ∏ i, a i ∧ Monotone a ∧ a (Fin.last t) ≤ n ^ 2) →
    Real.log ((n)! : ℝ) ≤ 2 * ((t : ℝ) + 1) * Real.log (n : ℝ) := by
  exact erdos_29589_hyp_volume_ns.erdos_29589_hyp_volume



-- Derived: log n! = Σ log k ≥ ∫_1^n log x dx = n log n - n + 1 (log is increasing).
-- Equivalently n! ≥ (n/e)^n. Elementary.
namespace erdos_29589_hyp_logfact_lower_ns
open Filter

open scoped Nat

theorem erdos_29589_hyp_logfact_lower : ∀ n : ℕ, 1 ≤ n →
    (n : ℝ) * Real.log (n : ℝ) - n ≤ Real.log ((n)! : ℝ) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hk0 : (0:ℝ) < k := by exact_mod_cast hk
    have hf : (0:ℝ) < ((k ! : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos k
    have hlog : Real.log ((k:ℝ)+1) - Real.log k ≤ 1 / k := by
      rw [← Real.log_div (by positivity) hk0.ne']
      have h1 := Real.log_le_sub_one_of_pos (show (0:ℝ) < ((k:ℝ)+1)/k by positivity)
      have e : ((k:ℝ)+1)/k - 1 = 1/k := by field_simp; ring
      linarith
    have hmul : (k:ℝ) * (Real.log ((k:ℝ)+1) - Real.log k) ≤ 1 := by
      have h3 := mul_le_mul_of_nonneg_left hlog hk0.le
      rwa [mul_one_div_cancel hk0.ne'] at h3
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) hf.ne']
    push_cast
    nlinarith
end erdos_29589_hyp_logfact_lower_ns

theorem erdos_29589_hyp_logfact_lower : ∀ n : ℕ, 1 ≤ n →
    (n : ℝ) * Real.log (n : ℝ) - n ≤ Real.log ((n)! : ℝ) := by
  exact erdos_29589_hyp_logfact_lower_ns.erdos_29589_hyp_logfact_lower



-- Derived: Stirling gives log n! = n log n - n + O(log n), and log n = o(n). Moderate.
namespace erdos_29589_hyp_logfact_upper_ns
open Filter

open scoped Nat

theorem erdos_29589_hyp_logfact_upper : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    Real.log ((n)! : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) - n + ε * n := by
  intro ε hε
  filter_upwards [eventually_ge_atTop (⌈(1 - Real.log ε) / ε⌉₊ + 1)] with n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hNpos : (0:ℝ) < ((m+1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
  have h1 := Stirling.log_stirlingSeq_formula (m+1)
  have h0 := Stirling.log_stirlingSeq_formula 1
  have hanti : Stirling.stirlingSeq (m+1) ≤ Stirling.stirlingSeq 1 :=
    Stirling.stirlingSeq'_antitone (Nat.zero_le m)
  have hlog : Real.log (Stirling.stirlingSeq (m+1)) ≤ Real.log (Stirling.stirlingSeq 1) :=
    Real.log_le_log (Stirling.stirlingSeq'_pos m) hanti
  have e1 : Real.log (2 * ((m+1:ℕ):ℝ)) = Real.log 2 + Real.log ((m+1:ℕ):ℝ) :=
    Real.log_mul (by norm_num) hNpos.ne'
  have e2 : Real.log (((m+1:ℕ):ℝ) / Real.exp 1) = Real.log ((m+1:ℕ):ℝ) - 1 := by
    rw [Real.log_div hNpos.ne' (Real.exp_pos 1).ne', Real.log_exp]
  have e3 : Real.log (Stirling.stirlingSeq 1) = 1 - 1/2 * Real.log 2 := by
    rw [h0]
    norm_num [Real.log_inv]
    try ring
  rw [e1, e2] at h1
  have hl : Real.log (ε * ((m+1:ℕ):ℝ)) ≤ ε * ((m+1:ℕ):ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_mul hε.ne' hNpos.ne'] at hl
  have hc : (1 - Real.log ε) / ε ≤ ((m+1:ℕ):ℝ) := by
    refine (Nat.le_ceil _).trans ?_
    exact_mod_cast (by omega : ⌈(1 - Real.log ε) / ε⌉₊ ≤ m + 1)
  have hc' : 1 - Real.log ε ≤ ε * ((m+1:ℕ):ℝ) := by
    rw [div_le_iff₀ hε] at hc
    linarith
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith
end erdos_29589_hyp_logfact_upper_ns

theorem erdos_29589_hyp_logfact_upper : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    Real.log ((n)! : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) - n + ε * n := by
  exact erdos_29589_hyp_logfact_upper_ns.erdos_29589_hyp_logfact_upper



-- Derived (hard core): the "waste" Σ log(n^2/a_i) of some admissible factorization is ≤ ε n
-- for all large n. This is exactly the upper half of the conjecture in waste form
-- (R2 reduction); the expected route is the smooth-number pairing of the large primes.
theorem erdos_29589_hyp_waste : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∃ t : ℕ,
    (∃ a : Fin (t + 1) → ℕ, (n)! = ∏ i, a i ∧ Monotone a ∧ a (Fin.last t) ≤ n ^ 2) ∧
    2 * ((t : ℝ) + 1) * Real.log (n : ℝ) ≤ Real.log ((n)! : ℝ) + ε * n := by
  sorry

theorem erdos_29589 (A : ℕ → ℕ) (h : ∀ n > 0,
    IsLeast { t + 1 | (t) (_ : ∃ a : Fin (t + 1) → ℕ, (n)! = ∏ i, a i ∧
      Monotone a ∧ a (Fin.last t) ≤ n ^ 2) } (A n)) :
    ((fun (n : ℕ) => (A n - n / 2 + n / (2 * Real.log n) : ℝ)) =o[atTop] fun n => n / Real.log n) := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hc2 : (0:ℝ) < c / 2 := by positivity
  filter_upwards [erdos_29589_hyp_waste (c / 2) hc2, erdos_29589_hyp_logfact_upper (c / 2) hc2,
    Filter.eventually_ge_atTop 3] with n hwn hun hn3
  obtain ⟨t, ht, hineq⟩ := hwn
  obtain ⟨⟨t0, ht0, hA0⟩, hlb⟩ := h n (by omega)
  have hle' : A n ≤ t + 1 := hlb ⟨t, ht, rfl⟩
  have hvol := erdos_29589_hyp_volume n (by omega) t0 ht0
  have hlow := erdos_29589_hyp_logfact_lower n (by omega)
  have hnR : (3:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn3
  have hL : 0 < Real.log (n:ℝ) := Real.log_pos (by linarith)
  have hle : ((A n : ℕ) : ℝ) ≤ (t:ℝ) + 1 := by exact_mod_cast hle'
  have hAeq : ((A n : ℕ) : ℝ) = (t0:ℝ) + 1 := by exact_mod_cast hA0.symm
  have h1 := mul_le_mul_of_nonneg_right hle hL.le
  have h2 : ((A n : ℕ) : ℝ) * Real.log (n:ℝ) = ((t0:ℝ) + 1) * Real.log (n:ℝ) := by
    rw [hAeq]
  have hlo : (n:ℝ) * Real.log (n:ℝ) - n ≤ 2 * ((A n : ℕ) : ℝ) * Real.log (n:ℝ) := by
    linarith
  have hup : 2 * ((A n : ℕ) : ℝ) * Real.log (n:ℝ) ≤ (n:ℝ) * Real.log (n:ℝ) - n + c * n := by
    linarith
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg n) hL.le), abs_le]
  have h2L : (0:ℝ) < 2 * Real.log (n:ℝ) := by linarith
  have hu : (n:ℝ) / (2 * Real.log (n:ℝ)) * (2 * Real.log (n:ℝ)) = n :=
    div_mul_cancel₀ _ h2L.ne'
  have hv : (n:ℝ) / Real.log (n:ℝ) = 2 * ((n:ℝ) / (2 * Real.log (n:ℝ))) := by ring
  have hu0 : (0:ℝ) ≤ (n:ℝ) / (2 * Real.log (n:ℝ)) := div_nonneg (Nat.cast_nonneg n) h2L.le
  have hcu0 : (0:ℝ) ≤ c * ((n:ℝ) / (2 * Real.log (n:ℝ))) := mul_nonneg hc.le hu0
  have hY : (((A n : ℕ) : ℝ) - (n:ℝ) / 2 + (n:ℝ) / (2 * Real.log (n:ℝ))) * (2 * Real.log (n:ℝ))
      = 2 * ((A n : ℕ) : ℝ) * Real.log (n:ℝ) - n * Real.log (n:ℝ) + n := by
    rw [add_mul, hu]; ring
  have hY0 : (0:ℝ) ≤ ((A n : ℕ) : ℝ) - (n:ℝ) / 2 + (n:ℝ) / (2 * Real.log (n:ℝ)) := by
    by_contra hneg
    push_neg at hneg
    have := mul_neg_of_neg_of_pos hneg h2L
    linarith
  have hcu : c * ((n:ℝ) / (2 * Real.log (n:ℝ))) * (2 * Real.log (n:ℝ)) = c * n := by
    rw [mul_assoc, hu]
  have hY1 : ((A n : ℕ) : ℝ) - (n:ℝ) / 2 + (n:ℝ) / (2 * Real.log (n:ℝ))
      ≤ c * ((n:ℝ) / (2 * Real.log (n:ℝ))) := by
    by_contra hneg
    push_neg at hneg
    have := mul_lt_mul_of_pos_right hneg h2L
    linarith
  rw [hv]
  constructor
  · linarith
  · linarith