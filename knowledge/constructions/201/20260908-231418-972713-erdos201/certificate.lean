import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card

set_option maxHeartbeats 1000000
set_option autoImplicit false

-- IMPORTS: Mathlib.Data.Finset.Powerset
-- IMPORTS: Mathlib.Data.Finset.Card
-- Object: A = [0, 4, 6, 8, 10, 12, 13, 14, 16, 18, 20, 22, 24, 26] (N = 14).  Claims: (i) every 8-subset of A contains a 3-term AP,
-- hence addRothNumber A ≤ 7 and G_3(14) ≤ 7;  (ii) W = [0, 1, 3, 4, 9, 10, 12, 13] ⊆ {0,…,13} is 3-AP-free
-- with |W| = 8, hence rothNumberNat 14 ≥ 8.  Together: R_3(14) - G_3(14) ≥ 1.
set_option maxRecDepth 8192 in
theorem construct_cert :
    (({0, 4, 6, 8, 10, 12, 13, 14, 16, 18, 20, 22, 24, 26} : Finset ℕ).card = 14 ∧
      ∀ t ∈ ({0, 4, 6, 8, 10, 12, 13, 14, 16, 18, 20, 22, 24, 26} : Finset ℕ).powersetCard 8,
        ∃ a ∈ t, ∃ b ∈ t, ∃ c ∈ t, a < b ∧ b < c ∧ a + c = b + b) ∧
    ((∀ x ∈ ({0, 1, 3, 4, 9, 10, 12, 13} : Finset ℕ), x < 14) ∧ ({0, 1, 3, 4, 9, 10, 12, 13} : Finset ℕ).card = 8 ∧
      ∀ a ∈ ({0, 1, 3, 4, 9, 10, 12, 13} : Finset ℕ), ∀ b ∈ ({0, 1, 3, 4, 9, 10, 12, 13} : Finset ℕ), ∀ c ∈ ({0, 1, 3, 4, 9, 10, 12, 13} : Finset ℕ),
        a < b → b < c → a + c ≠ b + b) := by
  decide +kernel
