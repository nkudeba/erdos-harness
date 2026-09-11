import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Lattice.Fold

set_option maxHeartbeats 1000000

-- IMPORTS: Mathlib.Data.Nat.Choose.Central
-- IMPORTS: Mathlib.Data.Set.Finite.Basic
-- IMPORTS: Mathlib.Data.Finset.Lattice.Fold

private lemma erdos_397_key (a : ℕ) :
    Nat.centralBinom a * (Nat.centralBinom (2 * a + 1 + 1) *
        Nat.centralBinom (8 * a ^ 2 + 8 * a + 1)) =
      Nat.centralBinom (a + 1) * (Nat.centralBinom (2 * a) *
        Nat.centralBinom (8 * a ^ 2 + 8 * a + 1 + 1)) := by
  have h1 := Nat.succ_mul_centralBinom_succ a
  have h2 := Nat.succ_mul_centralBinom_succ (2 * a)
  have h3 := Nat.succ_mul_centralBinom_succ (2 * a + 1)
  have h4 := Nat.succ_mul_centralBinom_succ (8 * a ^ 2 + 8 * a + 1)
  have hK : 0 < (a + 1) * (2 * a + 1) * (2 * a + 1 + 1) * (8 * a ^ 2 + 8 * a + 1 + 1) := by
    positivity
  apply Nat.eq_of_mul_eq_mul_left hK
  calc (a + 1) * (2 * a + 1) * (2 * a + 1 + 1) * (8 * a ^ 2 + 8 * a + 1 + 1) *
        (Nat.centralBinom a * (Nat.centralBinom (2 * a + 1 + 1) *
          Nat.centralBinom (8 * a ^ 2 + 8 * a + 1)))
      = (a + 1) * (2 * a + 1) * (8 * a ^ 2 + 8 * a + 1 + 1) * Nat.centralBinom a *
          Nat.centralBinom (8 * a ^ 2 + 8 * a + 1) *
          ((2 * a + 1 + 1) * Nat.centralBinom (2 * a + 1 + 1)) := by ring
    _ = (a + 1) * (2 * a + 1) * (8 * a ^ 2 + 8 * a + 1 + 1) * Nat.centralBinom a *
          Nat.centralBinom (8 * a ^ 2 + 8 * a + 1) *
          (2 * (2 * (2 * a + 1) + 1) * Nat.centralBinom (2 * a + 1)) := by rw [h3]
    _ = (a + 1) * (8 * a ^ 2 + 8 * a + 1 + 1) * Nat.centralBinom a *
          Nat.centralBinom (8 * a ^ 2 + 8 * a + 1) * (2 * (2 * (2 * a + 1) + 1)) *
          ((2 * a + 1) * Nat.centralBinom (2 * a + 1)) := by ring
    _ = (a + 1) * (8 * a ^ 2 + 8 * a + 1 + 1) * Nat.centralBinom a *
          Nat.centralBinom (8 * a ^ 2 + 8 * a + 1) * (2 * (2 * (2 * a + 1) + 1)) *
          (2 * (2 * (2 * a) + 1) * Nat.centralBinom (2 * a)) := by rw [h2]
    _ = (2 * a + 1) * (2 * a + 1 + 1) * Nat.centralBinom (2 * a) *
          (2 * (2 * (8 * a ^ 2 + 8 * a + 1) + 1) * Nat.centralBinom (8 * a ^ 2 + 8 * a + 1)) *
          (2 * (2 * a + 1) * Nat.centralBinom a) := by ring
    _ = (2 * a + 1) * (2 * a + 1 + 1) * Nat.centralBinom (2 * a) *
          ((8 * a ^ 2 + 8 * a + 1 + 1) * Nat.centralBinom (8 * a ^ 2 + 8 * a + 1 + 1)) *
          ((a + 1) * Nat.centralBinom (a + 1)) := by rw [← h4, ← h1]
    _ = (a + 1) * (2 * a + 1) * (2 * a + 1 + 1) * (8 * a ^ 2 + 8 * a + 1 + 1) *
        (Nat.centralBinom (a + 1) * (Nat.centralBinom (2 * a) *
          Nat.centralBinom (8 * a ^ 2 + 8 * a + 1 + 1))) := by ring

private lemma erdos_397_mem (a c : ℕ) (ha : 2 ≤ a) (hc : 2 * a + 1 + 1 < c)
    (hprod : Nat.centralBinom a * (Nat.centralBinom (2 * a + 1 + 1) * Nat.centralBinom c) =
      Nat.centralBinom (a + 1) * (Nat.centralBinom (2 * a) * Nat.centralBinom (c + 1))) :
    (({a, 2 * a + 1 + 1, c} : Finset ℕ), ({a + 1, 2 * a, c + 1} : Finset ℕ)) ∈
      {p : Finset ℕ × Finset ℕ |
        Disjoint p.1 p.2 ∧ p.1.Nonempty ∧ p.2.Nonempty ∧
        (∀ m ∈ p.1, 0 < m) ∧ (∀ n ∈ p.2, 0 < n) ∧
        ∏ m ∈ p.1, Nat.centralBinom m = ∏ n ∈ p.2, Nat.centralBinom n} := by
  have hn1 : a ∉ ({2 * a + 1 + 1, c} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have hn2 : 2 * a + 1 + 1 ∉ ({c} : Finset ℕ) := by
    simp only [Finset.mem_singleton]; omega
  have hn3 : a + 1 ∉ ({2 * a, c + 1} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have hn4 : 2 * a ∉ ({c + 1} : Finset ℕ) := by
    simp only [Finset.mem_singleton]; omega
  simp only [Set.mem_setOf_eq]
  refine ⟨?_, ⟨a, Finset.mem_insert_self _ _⟩, ⟨a + 1, Finset.mem_insert_self _ _⟩, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hx'
    omega
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    omega
  · intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    omega
  · rw [Finset.prod_insert hn1, Finset.prod_insert hn2, Finset.prod_singleton,
      Finset.prod_insert hn3, Finset.prod_insert hn4, Finset.prod_singleton]
    exact hprod

theorem erdos_397 :
    Set.Infinite {p : Finset ℕ × Finset ℕ |
      Disjoint p.1 p.2 ∧ p.1.Nonempty ∧ p.2.Nonempty ∧
      (∀ m ∈ p.1, 0 < m) ∧ (∀ n ∈ p.2, 0 < n) ∧
      ∏ m ∈ p.1, Nat.centralBinom m = ∏ n ∈ p.2, Nat.centralBinom n} := by
  intro hfin
  set N : ℕ := hfin.toFinset.sup (fun p : Finset ℕ × Finset ℕ => p.1.sup id) with hN
  have hmem := erdos_397_mem (N + 2) (8 * (N + 2) ^ 2 + 8 * (N + 2) + 1) (by omega)
    (by nlinarith [Nat.zero_le ((N + 2) ^ 2)]) (erdos_397_key _)
  have hin := hfin.mem_toFinset.mpr hmem
  have h1 : ({N + 2, 2 * (N + 2) + 1 + 1, 8 * (N + 2) ^ 2 + 8 * (N + 2) + 1} : Finset ℕ).sup id
      ≤ N :=
    Finset.le_sup (f := fun p : Finset ℕ × Finset ℕ => p.1.sup id) hin
  have h2 : N + 2 ≤
      ({N + 2, 2 * (N + 2) + 1 + 1, 8 * (N + 2) ^ 2 + 8 * (N + 2) + 1} : Finset ℕ).sup id :=
    Finset.le_sup (f := id) (Finset.mem_insert_self _ _)
  omega
