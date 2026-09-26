import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic

set_option maxHeartbeats 1000000
set_option autoImplicit false

private def Erdos424Aux.hofSet' : Set ℕ :=
  {n | ∀ T : Set ℕ, 2 ∈ T → 3 ∈ T → (∀ a ∈ T, ∀ b ∈ T, a ≠ b → a * b - 1 ∈ T) → n ∈ T}


def Erdos424.hofSet : Set ℕ :=
  {n | ∀ T : Set ℕ, 2 ∈ T → 3 ∈ T → (∀ a ∈ T, ∀ b ∈ T, a ≠ b → a * b - 1 ∈ T) → n ∈ T}


-- IMPORTS: Mathlib.Tactic
-- IMPORTS: Mathlib.Algebra.BigOperators.Fin
-- IMPORTS: Mathlib.Data.Nat.Factorial.Basic
-- IMPORTS: Mathlib.Data.Nat.Prime.Basic
/-- Local copy of the frozen set (definitionally equal to `Erdos424.hofSet`), so helper lemmas can
live above the frozen block. -/

private lemma Erdos424Aux.two_mem : 2 ∈ Erdos424Aux.hofSet' :=
  fun _ h2 _ _ => h2


private lemma Erdos424Aux.three_mem : 3 ∈ Erdos424Aux.hofSet' :=
  fun _ _ h3 _ => h3
