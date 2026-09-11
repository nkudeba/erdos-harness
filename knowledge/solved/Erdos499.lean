import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Convex.DoublyStochasticMatrix
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option maxHeartbeats 1000000
set_option autoImplicit false

-- IMPORTS: Mathlib.Analysis.MeanInequalities Mathlib.Analysis.SpecialFunctions.Pow.Real Mathlib.Analysis.Convex.Birkhoff
-- CHECK: exists_eq_sum_perm_of_mem_doublyStochastic doublyStochastic_eq_convexHull_permMatrix mem_doublyStochastic_iff_sum mem_convexHull_iff_exists_fintype Real.rpow_sum_of_nonneg Real.finset_prod_rpow Equiv.Perm.permMatrix_apply Real.rpow_add_of_nonneg

private lemma erdos_499_prod_rpow {ι : Type*} (s : Finset ι) (x : ℝ) (hx : 0 ≤ x)
    (f : ι → ℝ) (hf : ∀ k ∈ s, 0 ≤ f k) :
    ∏ k ∈ s, x ^ f k = x ^ (∑ k ∈ s, f k) := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | @insert a s ha ih =>
    intro hf
    have h1 : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
    have h2 : ∀ k ∈ s, 0 ≤ f k := fun k hk => hf k (Finset.mem_insert_of_mem hk)
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih h2,
      Real.rpow_add_of_nonneg hx h1 (Finset.sum_nonneg h2)]

private lemma erdos_499_rpow_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ k ∈ s, 0 ≤ f k) (r : ℝ) :
    (∏ k ∈ s, f k) ^ r = ∏ k ∈ s, f k ^ r := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | @insert a s ha ih =>
    intro hf
    have h1 : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
    have h2 : ∀ k ∈ s, 0 ≤ f k := fun k hk => hf k (Finset.mem_insert_of_mem hk)
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      Real.mul_rpow h1 (Finset.prod_nonneg h2), ih h2]

private lemma erdos_499_row (n : ℕ) (v : Fin n → ℝ) (hv : ∀ j, 0 ≤ v j)
    (hs : ∑ j, v j = 1) :
    (1 / (n : ℝ)) ≤ ∏ j, v j ^ v j := by
  have hn : (0 : ℝ) < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at hs
    · exact_mod_cast h
  have hgm := Real.geom_mean_le_arith_mean_weighted Finset.univ v (fun j => (v j)⁻¹)
    (fun j _ => hv j) hs (fun j _ => inv_nonneg.mpr (hv j))
  have hle : ∑ j, v j * (v j)⁻¹ ≤ (n : ℝ) := by
    calc ∑ j, v j * (v j)⁻¹ ≤ ∑ _j : Fin n, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro j _
          by_cases h : v j = 0
          · simp [h]
          · exact (mul_inv_cancel₀ h).le
      _ = n := by simp
  have hprod : ∏ j, (v j)⁻¹ ^ v j = (∏ j, v j ^ v j)⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun j _ => Real.inv_rpow (hv j) (v j)
  have hQpos : 0 < ∏ j, v j ^ v j := by
    apply Finset.prod_pos
    intro j _
    rcases (hv j).eq_or_lt with h | h
    · rw [← h]; simp
    · exact Real.rpow_pos_of_pos h _
  have hQinv : (∏ j, v j ^ v j)⁻¹ ≤ n := by
    rw [← hprod]; exact hgm.trans hle
  have h1 : (∏ j, v j ^ v j)⁻¹ * ∏ j, v j ^ v j = 1 := inv_mul_cancel₀ hQpos.ne'
  have h2 : (∏ j, v j ^ v j)⁻¹ * ∏ j, v j ^ v j ≤ n * ∏ j, v j ^ v j :=
    mul_le_mul_of_nonneg_right hQinv hQpos.le
  rw [div_le_iff₀ hn, mul_comm]
  linarith

private lemma erdos_499_core {ι : Type*} [Fintype ι] (n : ℕ) (a : Fin n → Fin n → ℝ)
    (h0 : ∀ i j, 0 ≤ a i j) (hrow : ∀ i, ∑ j, a i j = 1)
    (w : ι → ℝ) (hw : ∀ k, 0 ≤ w k) (hw1 : ∑ k, w k = 1) (τ : ι → Equiv.Perm (Fin n))
    (hdec : ∀ i j, a i j = ∑ k, w k * (if τ k i = j then 1 else 0)) :
    ∃ σ : Equiv.Perm (Fin n), (n : ℝ) ^ (-(n : ℤ)) ≤ ∏ i, a i (σ i) := by
  obtain ⟨σ, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun σ : Equiv.Perm (Fin n) => ∏ i, a i (σ i)) Finset.univ_nonempty
  refine ⟨σ, ?_⟩
  have hM : 0 ≤ ∏ i, a i (σ i) := Finset.prod_nonneg fun i _ => h0 i _
  have hA : ∏ k, (∏ i, a i (τ k i)) ^ w k ≤ ∏ i, a i (σ i) := by
    calc ∏ k, (∏ i, a i (τ k i)) ^ w k ≤ ∏ k, (∏ i, a i (σ i)) ^ w k := by
          apply Finset.prod_le_prod
          · intro k _
            exact Real.rpow_nonneg (Finset.prod_nonneg fun i _ => h0 i _) _
          · intro k _
            exact Real.rpow_le_rpow (Finset.prod_nonneg fun i _ => h0 i _)
              (hmax (τ k) (Finset.mem_univ _)) (hw k)
      _ = (∏ i, a i (σ i)) ^ (∑ k, w k) :=
          erdos_499_prod_rpow Finset.univ (∏ i, a i (σ i)) hM w (fun k _ => hw k)
      _ = ∏ i, a i (σ i) := by rw [hw1, Real.rpow_one]
  have hB : ∏ k, (∏ i, a i (τ k i)) ^ w k = ∏ i, ∏ j, a i j ^ a i j := by
    calc ∏ k, (∏ i, a i (τ k i)) ^ w k = ∏ k, ∏ i, a i (τ k i) ^ w k := by
          refine Finset.prod_congr rfl fun k _ => ?_
          exact erdos_499_rpow_prod Finset.univ (fun i => a i (τ k i)) (fun i _ => h0 i _) (w k)
      _ = ∏ i, ∏ k, a i (τ k i) ^ w k := Finset.prod_comm
      _ = ∏ i, ∏ k, ∏ j, a i j ^ (w k * if τ k i = j then 1 else 0) := by
          refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun k _ => ?_
          rw [Finset.prod_eq_single (τ k i)]
          · simp
          · intro j _ hj
            simp [hj, Ne.symm hj]
          · intro h
            exact absurd (Finset.mem_univ _) h
      _ = ∏ i, ∏ j, ∏ k, a i j ^ (w k * if τ k i = j then 1 else 0) := by
          refine Finset.prod_congr rfl fun i _ => Finset.prod_comm
      _ = ∏ i, ∏ j, a i j ^ a i j := by
          refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
          have hnn : ∀ k, 0 ≤ w k * (if τ k i = j then (1 : ℝ) else 0) := fun k =>
            mul_nonneg (hw k) (by split_ifs <;> norm_num)
          rw [erdos_499_prod_rpow Finset.univ (a i j) (h0 i j)
            (fun k => w k * if τ k i = j then 1 else 0) (fun k _ => hnn k)]
          congr 1
          exact (hdec i j).symm
  have hC : ∏ _i : Fin n, (1 / (n : ℝ)) ≤ ∏ i, ∏ j, a i j ^ a i j := by
    apply Finset.prod_le_prod
    · intro i _; positivity
    · intro i _; exact erdos_499_row n (a i) (h0 i) (hrow i)
  have hpow : (n : ℝ) ^ (-(n : ℤ)) = ∏ _i : Fin n, (1 / (n : ℝ)) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, zpow_neg, zpow_natCast,
      one_div, inv_pow]
  rw [hpow]
  rw [hB] at hA
  exact hC.trans hA

theorem erdos_499 (n : ℕ) (hn : 1 ≤ n) (a : Fin n → Fin n → ℝ)
    (h0 : ∀ i j, 0 ≤ a i j)
    (hrow : ∀ i, ∑ j, a i j = 1)
    (hcol : ∀ j, ∑ i, a i j = 1) :
    ∃ σ : Equiv.Perm (Fin n), (n : ℝ) ^ (-(n : ℤ)) ≤ ∏ i, a i (σ i) := by
  have hM : Matrix.of a ∈ doublyStochastic ℝ (Fin n) := by
    rw [mem_doublyStochastic_iff_sum]
    exact ⟨fun i j => by simpa using h0 i j, fun i => by simpa using hrow i,
      fun j => by simpa using hcol j⟩
  obtain ⟨w, hw, hw1, hsum⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hM
  refine erdos_499_core n a h0 hrow w hw hw1 (fun σ => σ) ?_
  intro i j
  have h : a i j = (∑ σ, w σ • σ.permMatrix ℝ) i j := by
    rw [hsum, Matrix.of_apply]
  rw [h, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul]
  congr 1
  by_cases hσ : σ i = j
  · subst hσ
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def]
  · simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
      hσ, Ne.symm hσ]
