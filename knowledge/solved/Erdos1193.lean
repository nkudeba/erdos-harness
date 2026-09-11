import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Logic.Equiv.Set
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Finset.NatAntidiagonal

set_option maxHeartbeats 1000000
set_option autoImplicit false

private lemma erdos_1193_card (n : ℕ) :
    Nat.card {p : ↥(Set.univ : Set ℕ) × ↥(Set.univ : Set ℕ) // (p.1 : ℕ) + (p.2 : ℕ) = n}
      = n + 1 := by
  have e : {p : ↥(Set.univ : Set ℕ) × ↥(Set.univ : Set ℕ) // (p.1 : ℕ) + (p.2 : ℕ) = n} ≃
      {p : ℕ × ℕ // p ∈ Finset.antidiagonal n} :=
    ((Equiv.Set.univ ℕ).prodCongr (Equiv.Set.univ ℕ)).subtypeEquiv (fun p => by
      simp [Finset.mem_antidiagonal, Equiv.Set.univ])
  rw [Nat.card_congr e, Nat.card_eq_finsetCard, Finset.Nat.card_antidiagonal]

private lemma erdos_1193_set (N : ℕ) :
    {n : ℕ | n ∈ Set.Iio N ∧
      Nat.card {p : ↥(Set.univ : Set ℕ) × ↥(Set.univ : Set ℕ) // (p.1 : ℕ) + (p.2 : ℕ) = n}
        = n + 1} = Set.Iio N := by
  ext n
  simp [erdos_1193_card]

private lemma erdos_1193_ncard (N : ℕ) : Set.ncard (Set.Iio N) = N := by
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_Iio, Nat.card_Iio]

-- CHECK: Nat.card Set.ncard Filter.liminf
theorem erdos_1193 :
    ∃ (A : Set ℕ) (g : ℕ → ℕ), Monotone g ∧ (∀ n, 0 < g n) ∧
      0 < Filter.liminf
        (fun N : ℕ =>
          ((Set.ncard {n : ℕ | n ∈ Set.Iio N ∧
              Nat.card {p : A × A // (p.1 : ℕ) + (p.2 : ℕ) = n} = g n} : ℝ) / N))
        Filter.atTop := by
  refine ⟨Set.univ, fun n => n + 1, fun a b h => Nat.succ_le_succ h, fun n => Nat.succ_pos n, ?_⟩
  have hev : ∀ᶠ N : ℕ in Filter.atTop,
      ((Set.ncard {n : ℕ | n ∈ Set.Iio N ∧
          Nat.card {p : ↥(Set.univ : Set ℕ) × ↥(Set.univ : Set ℕ) //
            (p.1 : ℕ) + (p.2 : ℕ) = n} = n + 1} : ℝ) / N) = (1 : ℝ) := by
    rw [Filter.eventually_atTop]
    refine ⟨1, fun N hN => ?_⟩
    rw [erdos_1193_set N, erdos_1193_ncard N]
    have : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    exact div_self this
  beta_reduce
  rw [Filter.liminf_congr hev, Filter.liminf_const]
  exact one_pos
