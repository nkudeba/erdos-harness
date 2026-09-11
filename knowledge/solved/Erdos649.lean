import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic

set_option maxHeartbeats 1000000
set_option autoImplicit false

-- IMPORTS: Mathlib.Tactic
-- IMPORTS: Mathlib.Algebra.BigOperators.Fin
-- IMPORTS: Mathlib.Data.Nat.Factorial.Basic
-- IMPORTS: Mathlib.Data.Nat.Prime.Basic
private lemma power_of_two649 (n : ℕ) (hn : 0 < n)
    (h : ∀ r : ℕ, Nat.Prime r → r ∣ n → r = 2) :
    ∃ k : ℕ, n = 2 ^ k := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn1 : n = 1
    · exact ⟨0, by simpa using hn1⟩
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hn1
    have hp2 := h p hp hpn
    subst p
    obtain ⟨m, hm⟩ := hpn
    have hmpos : 0 < m := by omega
    have hmlt : m < n := by omega
    have hmn : m ∣ n := ⟨2, by omega⟩
    obtain ⟨k, hk⟩ := ih m hmlt hmpos (fun r hr hrd => h r hr (dvd_trans hrd hmn))
    refine ⟨k + 1, ?_⟩
    rw [hm, hk, pow_succ]
    omega

private lemma power_two_mod_seven649 (k : ℕ) :
    2 ^ k % 7 = 1 ∨ 2 ^ k % 7 = 2 ∨ 2 ^ k % 7 = 4 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rcases ih with h | h | h <;> norm_num [pow_succ, Nat.mul_mod, h]

def IsGreatestPrimeFactor649 (n p : ℕ) : Prop :=
  2 ≤ n ∧
  Nat.Prime p ∧
  p ∣ n ∧
  ∀ r : ℕ, Nat.Prime r → r ∣ n → r ≤ p

theorem erdos_649 :
    ¬ (∀ p q : ℕ, Nat.Prime p → Nat.Prime q →
      ∃ n : ℕ,
        IsGreatestPrimeFactor649 n p ∧
        IsGreatestPrimeFactor649 (n + 1) q) := by
  intro h
  obtain ⟨n, hn, hn1⟩ := h 2 7 (by norm_num) (by norm_num)
  obtain ⟨k, hk⟩ := power_of_two649 n (by have := hn.1; omega) (by
    intro r hr hrd
    have := hn.2.2.2 r hr hrd
    have := hr.two_le
    omega)
  have hmod := Nat.mod_eq_zero_of_dvd hn1.2.2.1
  rw [hk] at hmod
  rcases power_two_mod_seven649 k with h | h | h <;>
    rw [Nat.add_mod, h] at hmod <;> norm_num at hmod
