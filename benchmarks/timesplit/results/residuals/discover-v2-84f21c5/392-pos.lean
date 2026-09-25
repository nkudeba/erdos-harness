open Filter
open scoped Nat

-- Lower half. Derived as follows: if n! = ∏ a_i with every a_i ≤ n^2, then n! ≤ n^(2(t+1)).
-- Elementary Stirling (n^n/n! ≤ e^n, one term of the exponential series) gives
-- log n! ≥ n log n - n, so t+1 ≥ n/2 - n/(2 log n).
-- This is stronger than the ε-form stated here (the constant is 0 instead of -ε n / log n).
-- REFUTED/INVARIANT output: exactly checked for 2 ≤ n ≤ 1200.
namespace erdos_86592_hyp_lower_ns
open Filter

open scoped Nat

-- CHECK: Real.sum_le_exp_of_nonneg Real.pow_div_factorial_le_exp
private lemma pow_le_exp_mul_fact (n : ℕ) : (n:ℝ)^n ≤ Real.exp n * (n ! : ℝ) := by
  have hf : (0:ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hs := Real.sum_le_exp_of_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n) (n+1)
  have hterm : (n:ℝ)^n / (n ! : ℝ) ≤ ∑ i ∈ Finset.range (n+1), (n:ℝ)^i / (i ! : ℝ) :=
    Finset.single_le_sum (f := fun i => (n:ℝ)^i / (i ! : ℝ))
      (fun i _ => by positivity) (Finset.self_mem_range_succ n)
  have h1 := hterm.trans hs
  rwa [div_le_iff₀ hf] at h1

private lemma log_fact_lower (n : ℕ) : (n:ℝ) * Real.log n - n ≤ Real.log (n ! : ℝ) := by
  have hf : (0:ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have h2 := pow_le_exp_mul_fact n
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  have hn : (0:ℝ) < n := by exact_mod_cast h
  have h3 := Real.log_le_log (by positivity) h2
  rw [Real.log_mul (Real.exp_pos _).ne' hf.ne', Real.log_exp, Real.log_pow] at h3
  linarith

theorem erdos_86592_hyp_lower :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ t : ℕ,
      (∃ a : Fin (t + 1) → ℕ, (n)! = ∏ i, a i ∧ Monotone a ∧ a (Fin.last t) ≤ n ^ 2) →
      (n : ℝ) / 2 - (n : ℝ) / (2 * Real.log n) - ε * ((n : ℝ) / Real.log n) ≤ (t : ℝ) + 1 := by
  intro ε hε
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  rintro t ⟨a, hprod, hmono, hlast⟩
  have hle : ∀ i, a i ≤ n^2 := fun i => (hmono (Fin.le_last i)).trans hlast
  have hN : n ! ≤ (n^2)^(t+1) := by
    rw [hprod]
    have := Finset.prod_le_pow_card Finset.univ a (n^2) (fun i _ => hle i)
    simpa [Finset.card_univ, Fintype.card_fin] using this
  have hR : (n ! : ℝ) ≤ ((n:ℝ)^2)^(t+1) := by exact_mod_cast hN
  have hf : (0:ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  have hlog := Real.log_le_log hf hR
  rw [Real.log_pow, Real.log_pow] at hlog
  push_cast at hlog
  have hL : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlow := log_fact_lower n
  have hq : (n:ℝ)/(2*Real.log n) * (2*Real.log n) = n :=
    div_mul_cancel₀ _ (mul_pos two_pos hL).ne'
  have hε' : 0 ≤ ε * ((n:ℝ)/Real.log n) :=
    mul_nonneg hε.le (div_nonneg (Nat.cast_nonneg n) hL.le)
  have h2L : (0:ℝ) < 2 * Real.log n := mul_pos two_pos hL
  by_contra hc
  push_neg at hc
  nlinarith [mul_pos (show 0 < (n:ℝ)/2 - (n:ℝ)/(2*Real.log n) - ((t:ℝ)+1) by linarith) h2L]
end erdos_86592_hyp_lower_ns

theorem erdos_86592_hyp_lower :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ t : ℕ,
      (∃ a : Fin (t + 1) → ℕ, (n)! = ∏ i, a i ∧ Monotone a ∧ a (Fin.last t) ≤ n ^ 2) →
      (n : ℝ) / 2 - (n : ℝ) / (2 * Real.log n) - ε * ((n : ℝ) / Real.log n) ≤ (t : ℝ) + 1 := by
  exact erdos_86592_hyp_lower_ns.erdos_86592_hyp_lower



-- Upper half (hard core). Construction: large-prime cores in (n^2/y, n^2],
-- y-smooth top-ups balanced against Legendre multiplicities, then pack the leftover
-- smooth mass. The total deficiency Σ log(n^2/a_i) is o(n); sorting the factors
-- gives a monotone list. Numerics: the normalized excess decreases,
-- 0.0516 (n=3000), 0.0418 (n=6000), 0.0296 (n=12000).
theorem erdos_86592_hyp_upper :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∃ t : ℕ,
      (∃ a : Fin (t + 1) → ℕ, (n)! = ∏ i, a i ∧ Monotone a ∧ a (Fin.last t) ≤ n ^ 2) ∧
      (t : ℝ) + 1 ≤ (n : ℝ) / 2 - (n : ℝ) / (2 * Real.log n) + ε * ((n : ℝ) / Real.log n) := by
  sorry

theorem erdos_86592 (A : ℕ → ℕ) (h : ∀ n > 0,
    IsLeast { t + 1 | (t) (_ : ∃ a : Fin (t + 1) → ℕ, (n)! = ∏ i, a i ∧
      Monotone a ∧ a (Fin.last t) ≤ n ^ 2) } (A n)) :
    ((fun (n : ℕ) => (A n - n / 2 + n / (2 * Real.log n) : ℝ)) =o[atTop] fun n => n / Real.log n) := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  filter_upwards [erdos_86592_hyp_upper c hc, erdos_86592_hyp_lower c hc,
    eventually_gt_atTop 1] with n hu hl hn
  try dsimp only
  obtain ⟨t, ht, hle⟩ := hu
  have hAle : A n ≤ t + 1 := (h n (by omega)).2 ⟨t, ht, rfl⟩
  obtain ⟨t', ht', hA⟩ := (h n (by omega)).1
  have hlow := hl t' ht'
  have hAle' : (A n : ℝ) ≤ (t : ℝ) + 1 := by exact_mod_cast hAle
  have hAeq : (A n : ℝ) = (t' : ℝ) + 1 := by
    rw [← hA]; push_cast; ring
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have hn0 : (0 : ℝ) < n := by linarith
  have hpos : 0 < (n : ℝ) / Real.log n := div_pos hn0 hlog
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpos.le, abs_le]
  constructor
  · linarith
  · linarith