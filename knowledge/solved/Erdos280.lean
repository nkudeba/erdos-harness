import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

set_option maxHeartbeats 1000000
set_option autoImplicit false

-- CHECK: Nat.mod_pow_succ Asymptotics.isLittleO_iff Nat.le_ceil mul_one_div_cancel Real.sq_sqrt Real.sqrt_pos

private lemma erdos_280_key (m i : ℕ)
    (h : ∀ j ≤ i, m % 2 ^ (j + 1) ≠ (2 ^ j + 1) % 2 ^ (j + 1)) :
    m % 2 ^ (i + 1) = 1 := by
  induction i with
  | zero =>
    have h0 := h 0 le_rfl
    simp only [pow_zero, zero_add, pow_one] at h0 ⊢
    omega
  | succ i ih =>
    have hi : m % 2 ^ (i + 1) = 1 := ih (fun j hj => h j (Nat.le_succ_of_le hj))
    have hs := h (i + 1) le_rfl
    have hP : 1 < 2 ^ (i + 1) := Nat.one_lt_two_pow (by omega)
    have hlt : 2 ^ (i + 1) + 1 < 2 ^ (i + 1 + 1) := by
      rw [pow_succ 2 (i + 1)]; omega
    rw [Nat.mod_eq_of_lt hlt] at hs
    rw [Nat.mod_pow_succ, hi] at hs ⊢
    have ht : m / 2 ^ (i + 1) % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have ht' : m / 2 ^ (i + 1) % 2 = 0 ∨ m / 2 ^ (i + 1) % 2 = 1 := by omega
    rcases ht' with ht' | ht'
    · rw [ht']; simp
    · rw [ht'] at hs; omega

private lemma erdos_280_filter (k : ℕ) :
    (Finset.range (2 ^ (k + 1))).filter
      (fun m => ∀ i ≤ k, m % 2 ^ (i + 1) ≠ (2 ^ i + 1) % 2 ^ (i + 1)) = {1} := by
  ext m
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨hm, h⟩
    have := erdos_280_key m k h
    rwa [Nat.mod_eq_of_lt hm] at this
  · rintro rfl
    refine ⟨Nat.one_lt_two_pow (by omega), ?_⟩
    intro i hi
    have h1 : 1 < 2 ^ (i + 1) := Nat.one_lt_two_pow (by omega)
    rw [Nat.mod_eq_of_lt h1]
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · decide
    · have h2 : 1 < 2 ^ i := Nat.one_lt_two_pow hpos.ne'
      have hlt : 2 ^ i + 1 < 2 ^ (i + 1) := by rw [pow_succ]; omega
      rw [Nat.mod_eq_of_lt hlt]
      omega

private lemma erdos_280_sq_le (n : ℕ) (hn : 4 ≤ n) : n ^ 2 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h1 : 2 * n + 1 ≤ n ^ 2 := by nlinarith
    calc (n + 1) ^ 2 = n ^ 2 + (2 * n + 1) := by ring
      _ ≤ 2 ^ n + n ^ 2 := Nat.add_le_add ih h1
      _ ≤ 2 ^ n + 2 ^ n := Nat.add_le_add_left ih _
      _ = 2 ^ (n + 1) := by ring

private lemma erdos_280_log_le (x : ℝ) (hx : 0 < x) : Real.log x ≤ x / 2 := by
  have hs : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  have h1 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 :=
    Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx)
  have h2 : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx.le
  nlinarith [sq_nonneg (Real.sqrt x - 2), h1, h2, hsq]

private lemma erdos_280_growth (k : ℕ) :
    (1 + (1 / 2 : ℝ)) * ((k : ℝ) + 1) * Real.log ((k : ℝ) + 1) < (2 : ℝ) ^ (k + 1) := by
  have hx : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hlog := erdos_280_log_le _ hx
  have hmul : (1 + (1 / 2 : ℝ)) * ((k : ℝ) + 1) * Real.log ((k : ℝ) + 1)
      ≤ (1 + (1 / 2 : ℝ)) * ((k : ℝ) + 1) * (((k : ℝ) + 1) / 2) := by
    apply mul_le_mul_of_nonneg_left hlog
    positivity
  have hsq : (3 / 4 : ℝ) * ((k : ℝ) + 1) ^ 2 < (2 : ℝ) ^ (k + 1) := by
    rcases Nat.lt_or_ge k 3 with hk | hk
    · interval_cases k <;> norm_num
    · have h := erdos_280_sq_le (k + 1) (by omega)
      have h' : (((k + 1) ^ 2 : ℕ) : ℝ) ≤ ((2 ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast h
      push_cast at h'
      have hpos : (0 : ℝ) < ((k : ℝ) + 1) ^ 2 := by positivity
      linarith
  linarith

private lemma erdos_280_littleO :
    Asymptotics.IsLittleO Filter.atTop (fun _ : ℕ => (1 : ℝ)) (fun k : ℕ => (k : ℝ) + 1) := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  rw [Filter.eventually_atTop]
  refine ⟨⌈1 / c⌉₊, fun k hk => ?_⟩
  have hk1 : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
  simp only [Real.norm_eq_abs, abs_one, abs_of_nonneg hk1]
  have h1 : (1 / c : ℝ) ≤ (⌈1 / c⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : ((⌈1 / c⌉₊ : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h3 : 1 / c ≤ (k : ℝ) + 1 := by linarith
  calc (1 : ℝ) = c * (1 / c) := (mul_one_div_cancel hc.ne').symm
    _ ≤ c * ((k : ℝ) + 1) := mul_le_mul_of_nonneg_left h3 hc.le

-- Zero-based indexing: term k of the sequence is n_{k+1}. Congruence spelled out via `%`.
-- o(k) expressed with Asymptotics.IsLittleO.
theorem erdos_280 :
    ∃ (n a : ℕ → ℕ) (ε : ℝ), 0 < ε ∧ StrictMono n ∧
      (∀ k : ℕ, (1 + ε) * ((k : ℝ) + 1) * Real.log ((k : ℝ) + 1) < (n k : ℝ)) ∧
      Asymptotics.IsLittleO Filter.atTop
        (fun k : ℕ =>
          (((Finset.range (n k)).filter
              (fun m => ∀ i ≤ k, m % n i ≠ a i % n i)).card : ℝ))
        (fun k : ℕ => (k : ℝ) + 1) := by
  refine ⟨fun k => 2 ^ (k + 1), fun k => 2 ^ k + 1, 1 / 2, by norm_num, ?_, ?_, ?_⟩
  · intro i j hij
    show 2 ^ (i + 1) < 2 ^ (j + 1)
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  · intro k
    exact_mod_cast erdos_280_growth k
  · have hf : (fun k : ℕ => (((Finset.range (2 ^ (k + 1))).filter
        (fun m => ∀ i ≤ k, m % 2 ^ (i + 1) ≠ (2 ^ i + 1) % 2 ^ (i + 1))).card : ℝ))
        = fun _ => (1 : ℝ) := by
      funext k
      rw [erdos_280_filter k, Finset.card_singleton, Nat.cast_one]
    show Asymptotics.IsLittleO Filter.atTop (fun k : ℕ => (((Finset.range (2 ^ (k + 1))).filter
        (fun m => ∀ i ≤ k, m % 2 ^ (i + 1) ≠ (2 ^ i + 1) % 2 ^ (i + 1))).card : ℝ))
        (fun k : ℕ => (k : ℝ) + 1)
    rw [hf]
    exact erdos_280_littleO
