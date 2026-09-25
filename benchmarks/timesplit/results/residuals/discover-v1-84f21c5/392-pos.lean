open Filter
open scoped Nat

-- Derived (R1): every factor is ≤ n^2 (monotone, last ≤ n^2), so n! ≤ (n^2)^(t+1); take logs.
theorem erdos_95503_hyp_count : ∀ n : ℕ, 2 ≤ n → ∀ t : ℕ, ∀ a : Fin (t + 1) → ℕ,
    (n)! = ∏ i, a i → Monotone a → a (Fin.last t) ≤ n ^ 2 →
    Real.log ((n)! : ℝ) ≤ 2 * ((t : ℝ) + 1) * Real.log n := by
  sorry

-- Derived (R1, ordering irrelevant): a list of factors ≤ n^2 with product n! (nonempty since n! ≥ 2)
-- can be sorted into a monotone Fin-tuple of the same length.
theorem erdos_95503_hyp_sort : ∀ n : ℕ, 2 ≤ n → ∀ l : List ℕ, l.prod = (n)! →
    (∀ x ∈ l, x ≤ n ^ 2) → ∃ t : ℕ, ∃ a : Fin (t + 1) → ℕ, t + 1 = l.length ∧
      (n)! = ∏ i, a i ∧ Monotone a ∧ a (Fin.last t) ≤ n ^ 2 := by
  sorry

-- Derived (R2): integral comparison ∫_1^n log x dx ≤ log n!, i.e. n! ≥ (n/e)^n.
namespace erdos_95503_hyp_logfact_lower_ns
open Filter

open scoped Nat

-- CHECK: Real.pow_div_factorial_le_exp
theorem erdos_95503_hyp_logfact_lower : ∀ n : ℕ, 2 ≤ n →
    (n : ℝ) * Real.log n - n ≤ Real.log ((n)! : ℝ) := by
  intro n hn
  have hpos : (0:ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hnpos : (0:ℝ) < (n:ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have h := Real.pow_div_factorial_le_exp (x := (n:ℝ)) hnpos.le n
  have h2 : (n:ℝ) ^ n ≤ Real.exp n * (n ! : ℝ) := by
    rwa [div_le_iff₀ hpos] at h
  have h3 := Real.log_le_log (by positivity) h2
  rw [Real.log_pow, Real.log_mul (Real.exp_pos _).ne' hpos.ne', Real.log_exp] at h3
  linarith
end erdos_95503_hyp_logfact_lower_ns

theorem erdos_95503_hyp_logfact_lower : ∀ n : ℕ, 2 ≤ n →
    (n : ℝ) * Real.log n - n ≤ Real.log ((n)! : ℝ) := by
  exact erdos_95503_hyp_logfact_lower_ns.erdos_95503_hyp_logfact_lower



-- Derived (R2): log n! ≤ n log n - n + 1 + log n, and 1 + log n = o(n).
theorem erdos_95503_hyp_logfact_upper : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    Real.log ((n)! : ℝ) ≤ (n : ℝ) * Real.log n - n + ε * n := by
  sorry

-- Derived (R2, statement (★)): the hard core. A grouping of the prime factors of n! into
-- groups with product ≤ n^2 and total waste 2·len·log n − log n! ≤ ε n.
-- Any counterexample to the target must violate this for some ε > 0 infinitely often.
theorem erdos_95503_hyp_packing : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    ∃ l : List ℕ, l.prod = (n)! ∧ (∀ x ∈ l, x ≤ n ^ 2) ∧
      2 * (l.length : ℝ) * Real.log n ≤ Real.log ((n)! : ℝ) + ε * n := by
  sorry

theorem erdos_95503 (A : ℕ → ℕ) (h : ∀ n > 0,
    IsLeast { t + 1 | (t) (_ : ∃ a : Fin (t + 1) → ℕ, (n)! = ∏ i, a i ∧
      Monotone a ∧ a (Fin.last t) ≤ n ^ 2) } (A n)) :
    ((fun (n : ℕ) => (A n - n / 2 + n / (2 * Real.log n) : ℝ)) =o[atTop] fun n => n / Real.log n) := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  filter_upwards [erdos_95503_hyp_logfact_upper c hc, erdos_95503_hyp_packing c hc,
    eventually_ge_atTop 2] with n hup hpk hn
  obtain ⟨l, hlprod, hlbd, hlw⟩ := hpk
  obtain ⟨t, a, htl, hprod, hmono, hlast⟩ := erdos_95503_hyp_sort n hn l hlprod hlbd
  have hA := h n (by omega)
  have hmem : t + 1 ∈ { t + 1 | (t) (_ : ∃ a : Fin (t + 1) → ℕ, (n)! = ∏ i, a i ∧
      Monotone a ∧ a (Fin.last t) ≤ n ^ 2) } := ⟨t, ⟨a, hprod, hmono, hlast⟩, rfl⟩
  have hle : A n ≤ t + 1 := hA.2 hmem
  obtain ⟨s, ⟨b, hbprod, hbmono, hblast⟩, hs⟩ := hA.1
  have hcnt := erdos_95503_hyp_count n hn s b hbprod hbmono hblast
  have hlow := erdos_95503_hyp_logfact_lower n hn
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hL : 0 < Real.log (n:ℝ) := Real.log_pos (by linarith)
  have hL0 : Real.log (n:ℝ) ≠ 0 := ne_of_gt hL
  have hxs : (A n : ℝ) = (s:ℝ) + 1 := by rw [← hs]; push_cast; ring
  have hxt : (A n : ℝ) ≤ (t:ℝ) + 1 := by exact_mod_cast hle
  have htlR : (t:ℝ) + 1 = (l.length : ℝ) := by exact_mod_cast htl
  have hq : (n:ℝ) / Real.log n * Real.log n = n := by field_simp
  have h1 : 0 ≤ 2 * (A n : ℝ) - n + (n:ℝ) / Real.log n := by
    by_contra hneg
    push_neg at hneg
    have hm := mul_neg_of_pos_of_neg hL hneg
    have e : Real.log n * (2 * (A n : ℝ) - n + (n:ℝ) / Real.log n)
        = 2 * (A n : ℝ) * Real.log n - n * Real.log n
          + (n:ℝ) / Real.log n * Real.log n := by ring
    rw [e, hq, hxs] at hm
    linarith
  have h2 : 0 ≤ (n:ℝ) - (n:ℝ) / Real.log n + 2 * c * ((n:ℝ) / Real.log n) - 2 * (A n : ℝ) := by
    by_contra hneg
    push_neg at hneg
    have hm := mul_neg_of_pos_of_neg hL hneg
    have e : Real.log n * ((n:ℝ) - (n:ℝ) / Real.log n + 2 * c * ((n:ℝ) / Real.log n)
        - 2 * (A n : ℝ))
        = n * Real.log n - (n:ℝ) / Real.log n * Real.log n
          + 2 * c * ((n:ℝ) / Real.log n * Real.log n) - 2 * (A n : ℝ) * Real.log n := by ring
    rw [e, hq] at hm
    have hxL := mul_le_mul_of_nonneg_right hxt hL.le
    rw [htlR] at hxL
    linarith
  have hqnn : 0 ≤ (n:ℝ) / Real.log n := div_nonneg (by linarith) hL.le
  have hf : (n:ℝ) / (2 * Real.log n) = (n:ℝ) / Real.log n / 2 := by ring
  have hcq : 0 ≤ c * ((n:ℝ) / Real.log n) := mul_nonneg hc.le hqnn
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg hqnn, abs_le]
  constructor <;> linarith [hf]