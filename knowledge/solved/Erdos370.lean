import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic

set_option maxHeartbeats 1000000
set_option autoImplicit false

private lemma erdos_370_mem (k : ℕ) :
    (k + 3) ^ 2 * (k ^ 2 + 6 * k + 7) ∈
      {n : ℕ | 2 ≤ n ∧ (∀ p ∈ n.primeFactors, p ^ 2 < n) ∧
        (∀ p ∈ (n + 1).primeFactors, p ^ 2 < n + 1)} := by
  have hexp : (k + 3) ^ 2 = k ^ 2 + 6 * k + 9 := by ring
  have h9 : 9 ≤ (k + 3) ^ 2 := by rw [hexp]; omega
  have h7 : 7 ≤ k ^ 2 + 6 * k + 7 := by omega
  have hsq : (k + 3) ^ 2 * (k ^ 2 + 6 * k + 7) + 1 = ((k + 2) * (k + 4)) ^ 2 := by ring
  have hbig : (k + 3) ^ 2 * 7 ≤ (k + 3) ^ 2 * (k ^ 2 + 6 * k + 7) :=
    Nat.mul_le_mul_left ((k + 3) ^ 2) h7
  simp only [Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_⟩
  · omega
  · intro p hp
    rw [Nat.mem_primeFactors] at hp
    obtain ⟨hp, hdvd, -⟩ := hp
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
    · have h2 : p ≤ k + 3 := Nat.le_of_dvd (by omega) (hp.dvd_of_dvd_pow h)
      have h3 : p ^ 2 ≤ (k + 3) ^ 2 := Nat.pow_le_pow_left h2 2
      omega
    · have h2 : p ≤ k ^ 2 + 6 * k + 7 := Nat.le_of_dvd (by omega) h
      have h3 : p ^ 2 ≤ (k ^ 2 + 6 * k + 7) ^ 2 := Nat.pow_le_pow_left h2 2
      have h4 : (k ^ 2 + 6 * k + 7) ^ 2 < (k + 3) ^ 2 * (k ^ 2 + 6 * k + 7) := by
        rw [pow_two (k ^ 2 + 6 * k + 7)]
        apply Nat.mul_lt_mul_of_pos_right _ (by omega)
        rw [hexp]; omega
      omega
  · intro p hp
    rw [hsq] at hp ⊢
    rw [Nat.mem_primeFactors] at hp
    obtain ⟨hp, hdvd, -⟩ := hp
    have h1 : p ∣ (k + 2) * (k + 4) := hp.dvd_of_dvd_pow hdvd
    have h2 : p ≤ k + 4 := by
      rcases (Nat.Prime.dvd_mul hp).mp h1 with h | h
      · have := Nat.le_of_dvd (by omega) h
        omega
      · exact Nat.le_of_dvd (by omega) h
    have h3 : k + 4 < (k + 2) * (k + 4) := by
      have : (k + 2) * (k + 4) = k * (k + 4) + 2 * (k + 4) := by ring
      rw [this]; omega
    have h4 : p ^ 2 ≤ (k + 4) ^ 2 := Nat.pow_le_pow_left h2 2
    have h5 : (k + 4) ^ 2 < ((k + 2) * (k + 4)) ^ 2 := Nat.pow_lt_pow_left h3 (by norm_num)
    omega

theorem erdos_370 :
    Set.Infinite {n : ℕ | 2 ≤ n ∧ (∀ p ∈ n.primeFactors, p ^ 2 < n) ∧
      (∀ p ∈ (n + 1).primeFactors, p ^ 2 < n + 1)} := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  refine ⟨(a + 3) ^ 2 * (a ^ 2 + 6 * a + 7), erdos_370_mem a, ?_⟩
  have hexp : (a + 3) ^ 2 = a ^ 2 + 6 * a + 9 := by ring
  have h1 : a + 3 ≤ (a + 3) ^ 2 := by rw [hexp]; omega
  have h2 : (a + 3) ^ 2 * 1 ≤ (a + 3) ^ 2 * (a ^ 2 + 6 * a + 7) :=
    Nat.mul_le_mul_left ((a + 3) ^ 2) (by omega)
  omega
