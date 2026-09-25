open Filter
open scoped Nat

def erdos37270Adm (n t : ℕ) : Prop :=
  ∃ a : Fin (t + 1) → ℕ, (n)! = ∏ i, a i ∧ Monotone a ∧ a (Fin.last t) ≤ n ^ 2

-- DERIVED (R1, counting bound): every factor is ≤ n^2, so n! ≤ (n^2)^(t+1).
-- Take logs and divide by 2 log n > 0 (valid for n ≥ 2).
namespace erdos_37270_hyp_lower_ns
open Filter

open scoped Nat

open Filter

open scoped Nat

theorem erdos_37270_hyp_lower : ∀ n t : ℕ, 2 ≤ n → erdos37270Adm n t →
    Real.log ((n)! : ℝ) / (2 * Real.log n) ≤ (t : ℝ) + 1 := by
  rintro n t hn ⟨a, hprod, hmono, hlast⟩
  have hle : ∀ i, a i ≤ n ^ 2 := fun i => (hmono (Fin.le_last i)).trans hlast
  have h1 : (n)! ≤ (n ^ 2) ^ (t + 1) := by
    rw [hprod]
    calc ∏ i, a i ≤ ∏ _i : Fin (t + 1), n ^ 2 := Finset.prod_le_prod' (fun i _ => hle i)
      _ = (n ^ 2) ^ (t + 1) := by simp
  have h2 : ((n)! : ℝ) ≤ (n : ℝ) ^ (2 * (t + 1)) := by
    rw [pow_mul]; exact_mod_cast h1
  have hpos : (0 : ℝ) < ((n)! : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have h3 : Real.log ((n)! : ℝ) ≤ ((2 * (t + 1) : ℕ) : ℝ) * Real.log n := by
    rw [← Real.log_pow]; exact Real.log_le_log hpos h2
  have hlog : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  rw [div_le_iff₀ (by linarith)]
  push_cast at h3
  have e : ((t : ℝ) + 1) * (2 * Real.log n) = 2 * ((t : ℝ) + 1) * Real.log n := by ring
  linarith
end erdos_37270_hyp_lower_ns

theorem erdos_37270_hyp_lower : ∀ n t : ℕ, 2 ≤ n → erdos37270Adm n t →
    Real.log ((n)! : ℝ) / (2 * Real.log n) ≤ (t : ℝ) + 1 := by
  exact erdos_37270_hyp_lower_ns.erdos_37270_hyp_lower



-- DERIVED (elementary Stirling bracket): n log n - n ≤ log n! ≤ n log n - n + log n + 1.
-- Compare ∑ log k with ∫ log x, then divide by 2 log n.
namespace erdos_37270_hyp_stirling_ns
open Filter

open scoped Nat

private lemma logfact_bounds (n : ℕ) (hn : 1 ≤ n) :
    (n:ℝ) * Real.log n - n ≤ Real.log ((n)! : ℝ) ∧
    Real.log ((n)! : ℝ) ≤ (n:ℝ) * Real.log n - n + Real.log n + 1 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [Nat.factorial]
  | succ n hn ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hnpos : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
    have hn1 : (0:ℝ) < (n:ℝ) + 1 := by linarith
    have hfac : Real.log (((n+1)! : ℕ) : ℝ) = Real.log ((n:ℝ)+1) + Real.log ((n)! : ℝ) := by
      have hf : ((n)! : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, Real.log_mul (ne_of_gt hn1) hf]
    have ha : Real.log ((n:ℝ)+1) - Real.log n ≤ ((n:ℝ)+1) * (n:ℝ)⁻¹ - 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < ((n:ℝ)+1)/n by positivity)
      rw [Real.log_div (ne_of_gt hn1) (ne_of_gt hnpos), div_eq_mul_inv] at this
      exact this
    have hb : Real.log (n:ℝ) - Real.log ((n:ℝ)+1) ≤ (n:ℝ) * ((n:ℝ)+1)⁻¹ - 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < (n:ℝ)/((n:ℝ)+1) by positivity)
      rw [Real.log_div (ne_of_gt hnpos) (ne_of_gt hn1), div_eq_mul_inv] at this
      exact this
    have i1 : (n:ℝ) * (n:ℝ)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hnpos)
    have i2 : ((n:ℝ)+1) * ((n:ℝ)+1)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hn1)
    have ha' := mul_le_mul_of_nonneg_left ha hnpos.le
    have hb' := mul_le_mul_of_nonneg_left hb hn1.le
    have j1 : (n:ℝ) * (((n:ℝ)+1) * (n:ℝ)⁻¹) = (n:ℝ) + 1 := by
      rw [mul_comm ((n:ℝ)+1), ← mul_assoc, i1, one_mul]
    have j2 : ((n:ℝ)+1) * ((n:ℝ) * ((n:ℝ)+1)⁻¹) = n := by
      rw [mul_comm (n:ℝ), ← mul_assoc, i2, one_mul]
    have h1 : (n:ℝ) * Real.log ((n:ℝ)+1) - (n:ℝ) * Real.log n ≤ 1 := by
      have : (n:ℝ) * (Real.log ((n:ℝ)+1) - Real.log n) ≤ 1 := by
        calc (n:ℝ) * (Real.log ((n:ℝ)+1) - Real.log n)
            ≤ (n:ℝ) * (((n:ℝ)+1) * (n:ℝ)⁻¹ - 1) := ha'
          _ = 1 := by rw [mul_sub, j1]; ring
      linarith [this]
    have h2 : ((n:ℝ)+1) * Real.log (n:ℝ) - ((n:ℝ)+1) * Real.log ((n:ℝ)+1) ≤ -1 := by
      have : ((n:ℝ)+1) * (Real.log (n:ℝ) - Real.log ((n:ℝ)+1)) ≤ -1 := by
        calc ((n:ℝ)+1) * (Real.log (n:ℝ) - Real.log ((n:ℝ)+1))
            ≤ ((n:ℝ)+1) * ((n:ℝ) * ((n:ℝ)+1)⁻¹ - 1) := hb'
          _ = -1 := by rw [mul_sub, j2]; ring
      linarith [this]
    rw [hfac]
    push_cast
    constructor
    · nlinarith [ih1, h1]
    · nlinarith [ih2, h2]

open Filter

open scoped Nat

theorem erdos_37270_hyp_stirling : ∀ n : ℕ, 2 ≤ n →
    (n : ℝ) / 2 - n / (2 * Real.log n) ≤ Real.log ((n)! : ℝ) / (2 * Real.log n) ∧
    Real.log ((n)! : ℝ) / (2 * Real.log n) ≤
      (n : ℝ) / 2 - n / (2 * Real.log n) + (1 / 2 + 1 / (2 * Real.log n)) := by
  intro n hn
  obtain ⟨h1, h2⟩ := logfact_bounds n (by omega)
  have hL : 0 < Real.log (n:ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hinv : Real.log (n:ℝ) * (Real.log (n:ℝ))⁻¹ = 1 := mul_inv_cancel₀ hL.ne'
  have hn' : (n:ℝ) * Real.log (n:ℝ) * (Real.log (n:ℝ))⁻¹ = n := by
    rw [mul_assoc, hinv, mul_one]
  have hi : 0 ≤ (Real.log (n:ℝ))⁻¹ := inv_nonneg.mpr hL.le
  have k1 := mul_le_mul_of_nonneg_right h1 hi
  have k2 := mul_le_mul_of_nonneg_right h2 hi
  simp only [div_eq_mul_inv, mul_inv]
  constructor
  · nlinarith [k1, hn', hinv]
  · nlinarith [k2, hn', hinv]
end erdos_37270_hyp_stirling_ns

theorem erdos_37270_hyp_stirling : ∀ n : ℕ, 2 ≤ n →
    (n : ℝ) / 2 - n / (2 * Real.log n) ≤ Real.log ((n)! : ℝ) / (2 * Real.log n) ∧
    Real.log ((n)! : ℝ) / (2 * Real.log n) ≤
      (n : ℝ) / 2 - n / (2 * Real.log n) + (1 / 2 + 1 / (2 * Real.log n)) := by
  exact erdos_37270_hyp_stirling_ns.erdos_37270_hyp_stirling



-- DERIVED: n / log n → ∞, while 1/2 + 1/(2 log n) is bounded for n ≥ 3.
namespace erdos_37270_hyp_small_ns
open Filter

open scoped Nat

open Filter

open scoped Nat

theorem erdos_37270_hyp_small : ∀ c : ℝ, 0 < c → ∀ᶠ n : ℕ in atTop,
    1 / 2 + 1 / (2 * Real.log n) ≤ c * ((n : ℝ) / Real.log n) := by
  intro c hc
  have h1 := (Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop).def hc
  filter_upwards [h1, eventually_ge_atTop 3] with n hn h3
  simp only [Function.comp_apply, id_eq, Real.norm_eq_abs] at hn
  have hn3 : (3:ℝ) ≤ n := by exact_mod_cast h3
  have he : Real.exp 1 ≤ (n:ℝ) := by
    have := Real.exp_one_lt_d9
    linarith
  have hlog : 1 ≤ Real.log n := by
    have := Real.log_le_log (Real.exp_pos 1) he
    rwa [Real.log_exp] at this
  have hL : 0 < Real.log n := by linarith
  rw [abs_of_nonneg hL.le, abs_of_nonneg (by linarith : (0:ℝ) ≤ n)] at hn
  have ha : 1 / (2 * Real.log n) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hb : 1 ≤ c * ((n : ℝ) / Real.log n) := by
    rw [← mul_div_assoc, le_div_iff₀ hL]
    linarith
  linarith
end erdos_37270_hyp_small_ns

theorem erdos_37270_hyp_small : ∀ c : ℝ, 0 < c → ∀ᶠ n : ℕ in atTop,
    1 / 2 + 1 / (2 * Real.log n) ≤ c * ((n : ℝ) / Real.log n) := by
  exact erdos_37270_hyp_small_ns.erdos_37270_hyp_small



-- CONJECTURE (hard core, R1): admissible factorizations exist with only o(n / log n)
-- factors beyond the counting bound. Equivalently, the total waste is o(n).
-- This is the upper-bound construction (Tao-style greedy plus smooth numbers).
theorem erdos_37270_hyp_upper : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∃ t : ℕ,
    erdos37270Adm n t ∧
    (t : ℝ) + 1 ≤ Real.log ((n)! : ℝ) / (2 * Real.log n) + ε * ((n : ℝ) / Real.log n) := by
  sorry

open Filter
open scoped Nat

theorem erdos_37270 (A : ℕ → ℕ) (h : ∀ n > 0,
    IsLeast { t + 1 | (t) (_ : ∃ a : Fin (t + 1) → ℕ, (n)! = ∏ i, a i ∧
      Monotone a ∧ a (Fin.last t) ≤ n ^ 2) } (A n)) :
    ((fun (n : ℕ) => (A n - n / 2 + n / (2 * Real.log n) : ℝ)) =o[atTop] fun n => n / Real.log n) := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hc2 : (0 : ℝ) < c / 2 := by linarith
  filter_upwards [erdos_37270_hyp_upper (c / 2) hc2, erdos_37270_hyp_small (c / 2) hc2,
    Filter.eventually_ge_atTop 2] with n hn1 hn2 hn3
  obtain ⟨t, ht, htle⟩ := hn1
  have hpos : n > 0 := by omega
  have hA := h n hpos
  have hAle : A n ≤ t + 1 := by
    apply hA.2
    exact ⟨t, ht, rfl⟩
  obtain ⟨s, hs, hsA⟩ := hA.1
  have hL := erdos_37270_hyp_lower n s hn3 hs
  have hst := erdos_37270_hyp_stirling n hn3
  have hlog : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hg0 : 0 ≤ (n : ℝ) / Real.log n := div_nonneg (Nat.cast_nonneg n) hlog.le
  have hsA' : (s : ℝ) + 1 = (A n : ℝ) := by exact_mod_cast hsA
  have hAle' : (A n : ℝ) ≤ (t : ℝ) + 1 := by exact_mod_cast hAle
  have hsplit : c / 2 * ((n : ℝ) / Real.log n) + c / 2 * ((n : ℝ) / Real.log n)
      = c * ((n : ℝ) / Real.log n) := by ring
  have hcg : 0 ≤ c * ((n : ℝ) / Real.log n) := mul_nonneg hc.le hg0
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg hg0, abs_le]
  constructor <;> linarith [hst.1, hst.2]