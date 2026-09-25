open Filter Polynomial Finset

def IntValued (p : ℚ[X]) : Prop :=
  ∀ n : ℤ, ∃ z : ℤ, p.eval (n : ℚ) = z

def NoFixedDivisor (p : ℚ[X]) : Prop :=
  ¬ (∃ d : ℤ, d ≥ 2 ∧ ∀ n : ℤ, n ≥ 1 → ∃ z : ℤ, p.eval (n : ℚ) = d * z)

def Reps (p : ℚ[X]) (m : ℤ) : Prop :=
  ∃ k ≥ 1, ∃ n : Fin (k + 1) → ℤ, 0 = n 0 ∧ StrictMono n ∧
  1 = ∑ i ∈ Finset.Icc 1 (Fin.last k), (1 : ℚ) / (n i) ∧
  (m : ℚ) = ∑ i ∈ Finset.Icc 1 (Fin.last k), p.eval (n i : ℚ)

def CompleteTail (p : ℚ[X]) (N0 : ℤ) : Prop :=
  ∀ᶠ (m : ℤ) in atTop, ∃ S : Finset ℤ, (∀ s ∈ S, N0 ≤ s) ∧
    (m : ℚ) = ∑ s ∈ S, p.eval (s : ℚ)

-- Derived (R1): a constant p with positive leading coefficient and no fixed divisor is p = 1.
-- Then m = k, and 1 = 1/2+1/3+1/6 extended by 1/N = 1/(N+1) + 1/(N(N+1)) on the largest
-- denominator gives every length k ≥ 3.
namespace erdos_31732_hyp_constant_ns
open Filter Polynomial Finset

open Filter Polynomial Finset

private lemma exists_rep (j : ℕ) : ∃ f : ℕ → ℕ, f 0 = 0 ∧
    (∀ a b, a < b → b ≤ j + 3 → f a < f b) ∧
    ∑ i ∈ Finset.Icc 1 (j + 3), (1 : ℚ) / (f i) = 1 := by
  induction j with
  | zero =>
    refine ⟨fun i => if i = 0 then 0 else if i = 1 then 2 else if i = 2 then 3 else 6,
      by simp, ?_, ?_⟩
    · intro a b hab hb
      have hb' : b ≤ 3 := by omega
      interval_cases b <;> interval_cases a <;> first | decide | simp | norm_num
    · have hI : Finset.Icc 1 (0 + 3) = ({1, 2, 3} : Finset ℕ) := by
        first
          | decide
          | rfl
          | (ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega)
      rw [hI, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
      norm_num
  | succ j ih =>
    obtain ⟨f, hf0, hmono, hsum⟩ := ih
    have e3 : ∑ i ∈ Finset.Icc 1 (j + 3), (1 : ℚ) / (f i)
        = ∑ i ∈ Finset.Icc 1 (j + 2), (1 : ℚ) / (f i) + 1 / (f (j + 3)) :=
      Finset.sum_Icc_succ_top (show 1 ≤ j + 2 + 1 by omega) (fun i => (1 : ℚ) / (f i))
    have hs : ∑ i ∈ Finset.Icc 1 (j + 2), (1 : ℚ) / (f i) + 1 / (f (j + 3)) = 1 := by
      rw [← e3]; exact hsum
    have hN : 2 ≤ f (j + 3) := by
      have h01 := hmono 0 1 (by omega) (by omega)
      have h13 := hmono 1 (j + 3) (by omega) le_rfl
      omega
    obtain ⟨g, g_low, g3, g4⟩ : ∃ g : ℕ → ℕ, (∀ i, i ≤ j + 2 → g i = f i) ∧
        g (j + 3) = f (j + 3) + 1 ∧ g (j + 4) = f (j + 3) * (f (j + 3) + 1) :=
      ⟨fun i => if i ≤ j + 2 then f i else if i = j + 3 then f (j + 3) + 1
          else f (j + 3) * (f (j + 3) + 1),
        fun i hi => if_pos hi,
        by simp <;> omega,
        by simp <;> omega⟩
    refine ⟨g, by rw [g_low 0 (by omega)]; exact hf0, ?_, ?_⟩
    · intro a b hab hb
      rcases (show b ≤ j + 2 ∨ b = j + 3 ∨ b = j + 4 by omega) with h1 | h1 | h1
      · rw [g_low a (by omega), g_low b h1]; exact hmono a b hab (by omega)
      · rw [h1, g3, g_low a (by omega)]
        have := hmono a (j + 3) (by omega) le_rfl
        omega
      · rcases (show a ≤ j + 2 ∨ a = j + 3 by omega) with h2 | h2
        · rw [h1, g4, g_low a h2]
          have := hmono a (j + 3) (by omega) le_rfl
          nlinarith
        · rw [h1, h2, g3, g4]
          nlinarith
    · have e4a : ∑ i ∈ Finset.Icc 1 (j + 1 + 3), (1 : ℚ) / (g i)
          = ∑ i ∈ Finset.Icc 1 (j + 3), (1 : ℚ) / (g i) + 1 / (g (j + 4)) :=
        Finset.sum_Icc_succ_top (show 1 ≤ j + 3 + 1 by omega) (fun i => (1 : ℚ) / (g i))
      have e4b : ∑ i ∈ Finset.Icc 1 (j + 3), (1 : ℚ) / (g i)
          = ∑ i ∈ Finset.Icc 1 (j + 2), (1 : ℚ) / (g i) + 1 / (g (j + 3)) :=
        Finset.sum_Icc_succ_top (show 1 ≤ j + 2 + 1 by omega) (fun i => (1 : ℚ) / (g i))
      have hcongr : ∑ i ∈ Finset.Icc 1 (j + 2), (1 : ℚ) / (g i)
          = ∑ i ∈ Finset.Icc 1 (j + 2), (1 : ℚ) / (f i) :=
        Finset.sum_congr rfl (fun i hi => by rw [g_low i (Finset.mem_Icc.mp hi).2])
      have hpos : (0 : ℚ) < f (j + 3) := by exact_mod_cast (show 0 < f (j + 3) by omega)
      have key : (1 : ℚ) / ((f (j + 3) + 1 : ℕ) : ℚ)
          + 1 / ((f (j + 3) * (f (j + 3) + 1) : ℕ) : ℚ) = 1 / (f (j + 3) : ℚ) := by
        push_cast
        have h1 : (f (j + 3) : ℚ) ≠ 0 := hpos.ne'
        have h2 : (f (j + 3) : ℚ) + 1 ≠ 0 := by positivity
        first
          | (field_simp; ring)
          | field_simp
          | (rw [div_add_div _ _ h2 (mul_ne_zero h1 h2),
                div_eq_div_iff (mul_ne_zero h2 (mul_ne_zero h1 h2)) h1]; ring)
      rw [e4a, e4b, hcongr, g3, g4]
      linarith [key, hs]

private lemma sum_fin_Icc (k : ℕ) (F : ℕ → ℚ) :
    ∑ i ∈ Finset.Icc (1 : Fin (k + 2)) (Fin.last (k + 1)), F i.val
      = ∑ i ∈ Finset.Icc 1 (k + 1), F i := by
  apply Finset.sum_bij (fun (a : Fin (k + 2)) _ => a.val)
  · intro a ha
    simp only [Finset.mem_Icc, Fin.le_iff_val_le_val, Fin.val_one, Fin.val_last] at ha ⊢
    omega
  · intro a _ b _ h
    exact Fin.ext h
  · intro b hb
    simp only [Finset.mem_Icc] at hb
    refine ⟨⟨b, by omega⟩, ?_, rfl⟩
    simp only [Finset.mem_Icc, Fin.le_iff_val_le_val, Fin.val_one, Fin.val_last, Fin.val_mk]
    omega
  · intro a _
    rfl

theorem erdos_31732_hyp_constant :
    ∀ p : ℚ[X], IntValued p → p.leadingCoeff > 0 → NoFixedDivisor p →
      p.natDegree = 0 → ∀ᶠ (m : ℤ) in atTop, Reps p m := by
  intro p hint hlc hnfd hdeg
  unfold IntValued at hint
  unfold NoFixedDivisor at hnfd
  have hC := Polynomial.eq_C_of_natDegree_eq_zero hdeg
  have hev : ∀ x : ℚ, p.eval x = p.coeff 0 := by
    intro x
    calc p.eval x = (Polynomial.C (p.coeff 0)).eval x := by rw [← hC]
      _ = p.coeff 0 := Polynomial.eval_C
  have hc : 0 < p.coeff 0 := by
    have h := hlc
    rw [Polynomial.leadingCoeff, hdeg] at h
    exact h
  obtain ⟨z, hz⟩ := hint 0
  have hz' : p.coeff 0 = (z : ℚ) := (hev _).symm.trans hz
  have hzpos : 0 < z := by
    have := hc
    rw [hz'] at this
    exact_mod_cast this
  have hz1 : z = 1 := by
    by_contra hne
    apply hnfd
    refine ⟨z, by omega, fun n _ => ⟨1, ?_⟩⟩
    rw [hev, hz']
    simp
  have hev1 : ∀ x : ℚ, p.eval x = 1 := by
    intro x
    rw [hev, hz', hz1, Int.cast_one]
  rw [Filter.eventually_atTop]
  refine ⟨3, fun m hm => ?_⟩
  obtain ⟨j, hj⟩ : ∃ j : ℕ, m = (j : ℤ) + 3 := ⟨(m - 3).toNat, by omega⟩
  obtain ⟨f, hf0, hmono, hsum⟩ := exists_rep j
  unfold Reps
  refine ⟨j + 3, by omega, fun i => ((f i.val : ℕ) : ℤ), ?_, ?_, ?_, ?_⟩
  · simp [hf0]
  · intro a b hab
    have hb := b.is_lt
    show ((f a.val : ℕ) : ℤ) < ((f b.val : ℕ) : ℤ)
    exact_mod_cast hmono a.val b.val (Fin.lt_iff_val_lt_val.mp hab) (by omega)
  · have hconv := sum_fin_Icc (j + 2) (fun i => (1 : ℚ) / (((f i : ℕ) : ℤ) : ℚ))
    have h' : ∑ i ∈ Finset.Icc 1 (j + 3), (1 : ℚ) / (((f i : ℕ) : ℤ) : ℚ) = 1 := by
      simp only [Int.cast_natCast]
      exact hsum
    exact (hconv.trans h').symm
  · have hconv := sum_fin_Icc (j + 2) (fun i => p.eval (((f i : ℕ) : ℤ) : ℚ))
    have h' : ∑ i ∈ Finset.Icc 1 (j + 3), p.eval (((f i : ℕ) : ℤ) : ℚ) = (m : ℚ) := by
      simp only [hev1]
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one,
        show j + 3 + 1 - 1 = j + 3 by omega, hj]
      norm_num
    exact (hconv.trans h').symm
end erdos_31732_hyp_constant_ns

theorem erdos_31732_hyp_constant :
    ∀ p : ℚ[X], IntValued p → p.leadingCoeff > 0 → NoFixedDivisor p →
      p.natDegree = 0 → ∀ᶠ (m : ℤ) in atTop, Reps p m := by
  exact erdos_31732_hyp_constant_ns.erdos_31732_hyp_constant



-- Derived from R2 (the gcd over any deg+1 consecutive values equals the full gcd, so every
-- tail n ≥ N0 has gcd 1) plus the Roth–Szekeres (1954) / Graham (1964, Duke Math. J. 31,
-- "Complete sequences of polynomial values") completeness criterion, applied to a tail on
-- which p is positive and increasing.
theorem erdos_31732_hyp_complete_tail :
    ∀ p : ℚ[X], IntValued p → p.leadingCoeff > 0 → NoFixedDivisor p →
      0 < p.natDegree → ∀ N0 : ℤ, CompleteTail p N0 := by
  sorry

-- Core (Graham 1963 method): completeness of every tail of the value sequence, together with
-- reciprocal-neutral swaps and the splitting 1/n = Σ_{t∈T} 1/(nt), lifts to Egyptian-fraction
-- representations of 1 with prescribed p-sum for every large m.
theorem erdos_31732_hyp_lift :
    ∀ p : ℚ[X], IntValued p → p.leadingCoeff > 0 → 0 < p.natDegree →
      (∀ N0 : ℤ, CompleteTail p N0) → ∀ᶠ (m : ℤ) in atTop, Reps p m := by
  sorry

open Filter Polynomial Finset

def Condition (p : ℚ[X]) : Prop :=
  (∀ n : ℤ, ∃ z : ℤ, p.eval (n : ℚ) = z) → p.leadingCoeff > 0 →
  ¬ (∃ d : ℤ, d ≥ 2 ∧ ∀ n : ℤ, n ≥ 1 → ∃ z : ℤ, p.eval (n : ℚ) = d * z) →
  ∀ᶠ (m : ℤ) in atTop, ∃ k ≥ 1, ∃ n : Fin (k + 1) → ℤ, 0 = n 0 ∧ StrictMono n ∧
  1 = ∑ i ∈ Finset.Icc 1 (Fin.last k), (1 : ℚ) / (n i) ∧
  (m : ℚ) = ∑ i ∈ Finset.Icc 1 (Fin.last k), p.eval (n i : ℚ)

theorem erdos_31732 :
    ∀ p : ℚ[X], Condition p := by
  intro p
  unfold Condition
  intro hint hlc hnd
  have key : ∀ᶠ (m : ℤ) in atTop, Reps p m := by
    rcases Nat.eq_zero_or_pos p.natDegree with h0 | hpos
    · exact erdos_31732_hyp_constant p hint hlc hnd h0
    · exact erdos_31732_hyp_lift p hint hlc hpos
        (erdos_31732_hyp_complete_tail p hint hlc hnd hpos)
  exact key