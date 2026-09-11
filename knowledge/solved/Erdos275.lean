import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex

set_option maxHeartbeats 1000000
set_option autoImplicit false

-- IMPORTS: Mathlib.Tactic
-- IMPORTS: Mathlib.Algebra.BigOperators.Fin
-- IMPORTS: Mathlib.Data.Nat.Factorial.Basic
-- IMPORTS: Mathlib.Data.Nat.Prime.Basic
-- IMPORTS: Mathlib.RingTheory.RootsOfUnity.Complex
private lemma geometric_zero (f : ℤ → ℂ) (b : ℂ) (hb : b ≠ 0)
    (h0 : f 0 = 0) (hs : ∀ x, f (x + 1) = b * f x) : ∀ x, f x = 0 := by
  intro x
  induction x using Int.induction_on with
  | zero => exact h0
  | succ k ih => simpa [ih] using hs (k : ℤ)
  | pred k ih =>
    have h := hs (-(k : ℤ) - 1)
    have he : -(k : ℤ) - 1 + 1 = -(k : ℤ) := by ring
    rw [he, ih] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hb

private lemma sum_geometric_zero {ι : Type*} (S : Finset ι)
    (b : ι → ℂ) (f : ι → ℤ → ℂ) (hb : ∀ i ∈ S, b i ≠ 0)
    (hf : ∀ i ∈ S, ∀ x, f i (x + 1) = b i * f i x)
    (h0 : ∀ k : ℕ, k < S.card → ∑ i ∈ S, f i k = 0) :
    ∀ x : ℤ, ∑ i ∈ S, f i x = 0 := by
  classical
  induction S using Finset.induction_on generalizing f with
  | empty => simp
  | @insert j S hj ih =>
    have hdiff : ∀ x : ℤ, ∑ i ∈ S, (b i - b j) * f i x = 0 := by
      apply ih (fun i x => (b i - b j) * f i x)
      · exact fun i hi => hb i (Finset.mem_insert_of_mem hi)
      · intro i hi x
        rw [hf i (Finset.mem_insert_of_mem hi) x]
        ring
      · intro k hk
        have h1 := h0 k (by simp only [Finset.card_insert_of_notMem hj]; omega)
        have h2 := h0 (k + 1) (by simp only [Finset.card_insert_of_notMem hj]; omega)
        simp only [Finset.sum_insert hj, Nat.cast_add, Nat.cast_one] at h1 h2
        simp only [hf j (Finset.mem_insert_self _ _)] at h2
        calc
          ∑ i ∈ S, (b i - b j) * f i k =
              (∑ i ∈ S, f i ((k : ℤ) + 1)) - b j * ∑ i ∈ S, f i k := by
                simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
                congr 1
                apply Finset.sum_congr rfl
                intro i hi
                exact (hf i (Finset.mem_insert_of_mem hi) k).symm
          _ = 0 := by linear_combination h2 - b j * h1
    apply geometric_zero (fun x => ∑ i ∈ insert j S, f i x) (b j)
      (hb j (Finset.mem_insert_self _ _))
    · exact h0 0 (by simp)
    · intro x
      simp only [Finset.sum_insert hj, hf j (Finset.mem_insert_self _ _)]
      have h := hdiff x
      simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
      have he : ∑ i ∈ S, f i (x + 1) = ∑ i ∈ S, b i * f i x :=
        Finset.sum_congr rfl (fun i hi => hf i (Finset.mem_insert_of_mem hi) x)
      rw [he]
      linear_combination h

theorem erdos_275
    (r : ℕ) (a : Fin r → ℤ) (n : Fin r → ℕ)
    (hn : ∀ i, 0 < n i)
    (hcover : ∃ s : ℤ, ∀ k : ℕ, k < 2 ^ r →
      ∃ i : Fin r, (n i : ℤ) ∣ (s + (k : ℤ) - a i)) :
    ∀ x : ℤ, ∃ i : Fin r, (n i : ℤ) ∣ (x - a i) := by
  classical
  obtain ⟨s, hs⟩ := hcover
  let z : Fin r → ℂ := fun i => Complex.exp (2 * Real.pi * Complex.I / n i)
  have hz : ∀ i, z i ≠ 0 := fun i => Complex.exp_ne_zero _
  have hroot : ∀ i, IsPrimitiveRoot (z i) (n i) :=
    fun i => Complex.isPrimitiveRoot_exp (n i) (Nat.ne_of_gt (hn i))
  let U : Finset (Fin r) := Finset.univ
  let b : Finset (Fin r) → ℂ := fun t => ∏ i ∈ t, z i
  let f : Finset (Fin r) → ℤ → ℂ := fun t x =>
    (∏ i ∈ t, z i ^ (s - a i)) * b t ^ x * ∏ i ∈ U \ t, (-1 : ℂ)
  have hb : ∀ t, b t ≠ 0 := fun t => Finset.prod_ne_zero_iff.mpr (fun i _ => hz i)
  have hexpand : ∀ x : ℤ,
      (∏ i : Fin r, (z i ^ (s + x - a i) - 1)) = ∑ t ∈ U.powerset, f t x := by
    intro x
    have he : ∀ i, z i ^ (s + x - a i) - 1 =
        z i ^ (s - a i) * z i ^ x + (-1 : ℂ) := by
      intro i
      rw [show s + x - a i = (s - a i) + x by ring, zpow_add₀ (hz i)]
      ring
    simp only [he]
    rw [Finset.prod_add]
    apply Finset.sum_congr rfl
    intro t ht
    simp only [Finset.prod_mul_distrib, Finset.prod_zpow, f, b, U]
  have hall : ∀ x : ℤ, ∑ t ∈ U.powerset, f t x = 0 := by
    apply sum_geometric_zero U.powerset b f
    · exact fun t _ => hb t
    · intro t ht x
      dsimp [f]
      rw [zpow_add₀ (hb t), zpow_one]
      ring
    · intro k hk
      rw [← hexpand]
      have hk' : k < 2 ^ r := by simpa [U] using hk
      obtain ⟨i, hi⟩ := hs k hk'
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact sub_eq_zero.mpr ((hroot i).zpow_eq_one_iff_dvd _ |>.mpr hi)
  intro x
  have hp : (∏ i : Fin r, (z i ^ (x - a i) - 1)) = 0 := by
    have h := (hexpand (x - s)).trans (hall (x - s))
    simpa only [show s + (x - s) = x by ring] using h
  obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hp
  exact ⟨i, (hroot i).zpow_eq_one_iff_dvd _ |>.mp (sub_eq_zero.mp hi)⟩
