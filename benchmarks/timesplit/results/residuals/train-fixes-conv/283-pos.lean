open Filter Polynomial Finset

namespace erdos_50182_hyp_R1_ns
open Filter Polynomial Finset

def IntValued (p : ℚ[X]) : Prop :=
  ∀ n : ℤ, ∃ z : ℤ, p.eval (n : ℚ) = z

def FinNoFixedDivisor (p : ℚ[X]) : Prop :=
  ¬ ∃ d : ℤ, d ≥ 2 ∧
    ∀ j ∈ Finset.range (p.natDegree + 1), ∃ z : ℤ, p.eval ((j : ℚ) + 1) = d * z

private lemma natDeg_diff_le (q : ℚ[X]) (N : ℕ) (hq : q.natDegree ≤ N + 1) :
    (q.comp (X + C 1) - q).natDegree ≤ N := by
  have hnc : (q.comp (X + C 1)).natDegree = q.natDegree := by
    rw [natDegree_comp, natDegree_X_add_C, mul_one]
  by_cases h : q.natDegree = N + 1
  · have hq0 : q ≠ 0 := by
      rintro rfl
      simp at h
    have hc0 : q.comp (X + C 1) ≠ 0 := by
      intro h0
      rw [h0, natDegree_zero] at hnc
      omega
    by_cases hd0 : q.comp (X + C 1) - q = 0
    · rw [hd0, natDegree_zero]; omega
    have hX : (X + C (1:ℚ)).natDegree ≠ 0 := by
      rw [natDegree_X_add_C]; norm_num
    have hlt : (q.comp (X + C 1) - q).degree < (q.comp (X + C 1)).degree := by
      apply degree_sub_lt
      · rw [degree_eq_natDegree hc0, degree_eq_natDegree hq0, hnc]
      · exact hc0
      · rw [leadingCoeff_comp hX, leadingCoeff_X_add_C, one_pow, mul_one]
    have := natDegree_lt_natDegree hd0 hlt
    rw [hnc] at this
    omega
  · have h1 : q.natDegree ≤ N := by omega
    calc (q.comp (X + C 1) - q).natDegree
        ≤ max (q.comp (X + C 1)).natDegree q.natDegree := natDegree_sub_le _ _
      _ ≤ N := by rw [hnc, max_self]; exact h1

private lemma key_div (d : ℤ) : ∀ N : ℕ, ∀ q : ℚ[X], q.natDegree ≤ N →
    (∀ j : ℕ, j ≤ N → ∃ z : ℤ, q.eval ((j : ℚ) + 1) = d * z) →
    ∀ m : ℕ, ∃ z : ℤ, q.eval ((m : ℚ) + 1) = d * z := by
  intro N
  induction N with
  | zero =>
    intro q hq hj m
    obtain ⟨z, hz⟩ := hj 0 le_rfl
    refine ⟨z, ?_⟩
    rw [eq_C_of_natDegree_le_zero hq] at hz ⊢
    simpa using hz
  | succ N ih =>
    intro q hq hj
    have hev : ∀ x : ℚ, (q.comp (X + C 1) - q).eval x = q.eval (x + 1) - q.eval x := by
      intro x
      simp [eval_comp]
    have h' := ih (q.comp (X + C 1) - q) (natDeg_diff_le q N hq) (by
      intro j hjN
      obtain ⟨a, ha⟩ := hj (j + 1) (by omega)
      obtain ⟨b, hb⟩ := hj j (by omega)
      refine ⟨a - b, ?_⟩
      rw [hev]
      rw [show ((j : ℚ) + 1 + 1) = ((j + 1 : ℕ) : ℚ) + 1 by push_cast; ring]
      rw [ha, hb, Int.cast_sub]
      ring)
    intro m
    induction m with
    | zero => exact hj 0 (by omega)
    | succ m ihm =>
      obtain ⟨a, ha⟩ := ihm
      obtain ⟨b, hb⟩ := h' m
      refine ⟨a + b, ?_⟩
      have := hev ((m : ℚ) + 1)
      have e : ((m + 1 : ℕ) : ℚ) + 1 = (m : ℚ) + 1 + 1 := by push_cast; ring
      rw [e, Int.cast_add]
      linear_combination hb + ha - this

theorem erdos_50182_hyp_R1 :
    ∀ p : ℚ[X], IntValued p → ∀ d : ℤ,
      (∀ j ∈ Finset.range (p.natDegree + 1), ∃ z : ℤ, p.eval ((j : ℚ) + 1) = d * z) →
      ∀ n : ℤ, n ≥ 1 → ∃ z : ℤ, p.eval (n : ℚ) = d * z := by
  intro p _ d hd n hn
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = (m : ℤ) + 1 := ⟨(n - 1).toNat, by omega⟩
  have := key_div d p.natDegree p le_rfl
    (fun j hj => hd j (Finset.mem_range.mpr (by omega))) m
  first
    | (push_cast; exact this)
    | simpa using this
end erdos_50182_hyp_R1_ns

theorem erdos_50182_hyp_R1 :
    ∀ p : ℚ[X], erdos_50182_hyp_R1_ns.IntValued p → ∀ d : ℤ,
      (∀ j ∈ Finset.range (p.natDegree + 1), ∃ z : ℤ, p.eval ((j : ℚ) + 1) = d * z) →
      ∀ n : ℤ, n ≥ 1 → ∃ z : ℤ, p.eval (n : ℚ) = d * z := by
  exact erdos_50182_hyp_R1_ns.erdos_50182_hyp_R1

theorem erdos_50182_hyp_egypt :
    ∀ k : ℕ, 3 ≤ k → ∃ n : Fin (k + 1) → ℤ, 0 = n 0 ∧ StrictMono n ∧
      1 = ∑ i ∈ Finset.Icc 1 (Fin.last k), (1 : ℚ) / (n i) ∧
      (k : ℚ) = ∑ i ∈ Finset.Icc 1 (Fin.last k), (1 : ℚ) := by
  sorry

theorem erdos_50182_hyp_core :
    ∀ p : ℚ[X], erdos_50182_hyp_R1_ns.IntValued p → p.leadingCoeff > 0 → 0 < p.natDegree →
      erdos_50182_hyp_R1_ns.FinNoFixedDivisor p →
      ∀ᶠ (m : ℤ) in atTop, ∃ k ≥ 1, ∃ n : Fin (k + 1) → ℤ, 0 = n 0 ∧ StrictMono n ∧
        1 = ∑ i ∈ Finset.Icc 1 (Fin.last k), (1 : ℚ) / (n i) ∧
        (m : ℚ) = ∑ i ∈ Finset.Icc 1 (Fin.last k), p.eval (n i : ℚ) ∧
        (2 ≤ n 1) ∧
        (∀ q : ℕ, q.Prime → n (Fin.last k) < 2 * (q : ℤ) →
          ∀ i ∈ Finset.Icc 1 (Fin.last k), ¬ ((q : ℤ) ∣ n i)) := by
  sorry

open Filter Polynomial Finset

def Condition (p : ℚ[X]) : Prop :=
  (∀ n : ℤ, ∃ z : ℤ, p.eval (n : ℚ) = z) → p.leadingCoeff > 0 →
  ¬ (∃ d : ℤ, d ≥ 2 ∧ ∀ n : ℤ, n ≥ 1 → ∃ z : ℤ, p.eval (n : ℚ) = d * z) →
  ∀ᶠ (m : ℤ) in atTop, ∃ k ≥ 1, ∃ n : Fin (k + 1) → ℤ, 0 = n 0 ∧ StrictMono n ∧
  1 = ∑ i ∈ Finset.Icc 1 (Fin.last k), (1 : ℚ) / (n i) ∧
  (m : ℚ) = ∑ i ∈ Finset.Icc 1 (Fin.last k), p.eval (n i : ℚ)

theorem erdos_50182 :
    ∀ p : ℚ[X], Condition p := by
  intro p
  unfold Condition
  intro hint hlc hN
  by_cases hdeg : p.natDegree = 0
  · have hC : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero hdeg
    have hev : ∀ x : ℚ, p.eval x = p.coeff 0 := by
      intro x
      rw [hC]
      simp
    obtain ⟨z, hz⟩ := hint 0
    have hc : p.coeff 0 = (z : ℚ) := by
      rw [← hev 0]
      simpa using hz
    have hlc' : (0 : ℚ) < (z : ℚ) := by
      have h1 : p.leadingCoeff = p.coeff 0 := by
        simp only [Polynomial.leadingCoeff, hdeg]
      rw [h1, hc] at hlc
      exact hlc
    have hzpos : 0 < z := by exact_mod_cast hlc'
    have hz1 : z = 1 := by
      by_contra hne
      apply hN
      refine ⟨z, by omega, fun n _ => ⟨1, ?_⟩⟩
      rw [hev, hc]
      simp
    have hp1 : ∀ x : ℚ, p.eval x = 1 := by
      intro x
      simp [hev, hc, hz1]
    filter_upwards [eventually_ge_atTop (3 : ℤ)] with m hm
    obtain ⟨n, h0, hmono, hrec, hcnt⟩ := erdos_50182_hyp_egypt m.toNat (by omega)
    refine ⟨m.toNat, by omega, n, h0, hmono, hrec, ?_⟩
    have hs : ∑ i ∈ Finset.Icc 1 (Fin.last m.toNat), p.eval (n i : ℚ)
        = ∑ i ∈ Finset.Icc 1 (Fin.last m.toNat), (1 : ℚ) :=
      Finset.sum_congr rfl (fun i _ => hp1 _)
    rw [hs, ← hcnt]
    have hmt : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg (by omega)
    exact_mod_cast hmt.symm
  · have hfin : erdos_50182_hyp_R1_ns.FinNoFixedDivisor p := by
      unfold erdos_50182_hyp_R1_ns.FinNoFixedDivisor
      intro h
      obtain ⟨d, hd, hj⟩ := h
      exact hN ⟨d, hd, erdos_50182_hyp_R1_ns.erdos_50182_hyp_R1 p hint d hj⟩
    have h := erdos_50182_hyp_core p hint hlc (Nat.pos_of_ne_zero hdeg) hfin
    filter_upwards [h] with m hm
    obtain ⟨k, hk, n, h0, hmono, hrec, hsum, -, -⟩ := hm
    exact ⟨k, hk, n, h0, hmono, hrec, hsum⟩