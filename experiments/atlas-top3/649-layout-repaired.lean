import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factors

set_option maxHeartbeats 1000000
set_option autoImplicit false

private lemma powers_two_mod_seven (k : ℕ) :
    2 ^ k % 7 = 1 ∨ 2 ^ k % 7 = 2 ∨ 2 ^ k % 7 = 4 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rcases ih with h | h | h <;> simp [pow_succ, Nat.mul_mod, h]

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
  have hn0 : n ≠ 0 := by have := hn.1; omega
  have hpow : n = 2 ^ n.primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd hn0 (by
      intro r hr hd
      have := hn.2.2.2 r hr hd
      have := hr.two_le
      omega)
  have hmod := Nat.mod_eq_zero_of_dvd hn1.2.2.1
  rw [hpow, Nat.add_mod] at hmod
  rcases powers_two_mod_seven n.primeFactorsList.length with hr | hr | hr <;>
    norm_num [hr] at hmod

#print axioms erdos_649
