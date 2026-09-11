import Mathlib.Tactic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic

set_option autoImplicit false
set_option maxHeartbeats 1000000

private lemma erdos370_family (t : ℕ) :
    (∀ p : ℕ, p.Prime → p ∣ (6*t+8)*(6*t+10) → p*p < (6*t+8)*(6*t+10)) ∧
    (∀ p : ℕ, p.Prime → p ∣ (6*t+8)*(6*t+10)+1 → p*p < (6*t+8)*(6*t+10)+1) := by
  constructor
  · intro p hp hd
    have hfactor : (6*t+8)*(6*t+10) = (2*(3*t+4))*(2*(3*t+5)) := by ring
    rw [hfactor] at hd
    have hbound : p ≤ 3*t+5 := by
      rcases hp.dvd_mul.mp hd with h | h
      · rcases hp.dvd_mul.mp h with h | h
        · have := Nat.le_of_dvd (by norm_num : 0 < 2) h
          omega
        · have := Nat.le_of_dvd (by omega : 0 < 3*t+4) h
          omega
      · rcases hp.dvd_mul.mp h with h | h
        · have := Nat.le_of_dvd (by norm_num : 0 < 2) h
          omega
        · exact Nat.le_of_dvd (by omega) h
    nlinarith [Nat.mul_le_mul hbound hbound]
  · intro p hp hd
    have hfactor : (6*t+8)*(6*t+10)+1 = (3*(2*t+3))*(3*(2*t+3)) := by ring
    rw [hfactor] at hd
    have hm : p ∣ 3*(2*t+3) := (hp.dvd_mul.mp hd).elim id id
    have hbound : p ≤ 3*t+5 := by
      rcases hp.dvd_mul.mp hm with h | h
      · have := Nat.le_of_dvd (by norm_num : 0 < 3) h
        omega
      · have := Nat.le_of_dvd (by omega : 0 < 2*t+3) h
        omega
    nlinarith [Nat.mul_le_mul hbound hbound]

theorem erdos_370 :
    {n : ℕ | (∀ p : ℕ, p.Prime → p ∣ n → p*p < n) ∧
      (∀ p : ℕ, p.Prime → p ∣ n+1 → p*p < n+1)}.Infinite := by
  have hm : StrictMono (fun t : ℕ => (6*t+8)*(6*t+10)) := by
    apply strictMono_nat_of_lt_succ
    intro t
    nlinarith
  exact (Set.infinite_range_of_injective hm.injective).mono (by
    rintro n ⟨t, rfl⟩
    exact erdos370_family t)

#print axioms erdos_370
