open scoped Classical
open Filter

def RequiredCondition (A : Finset ℕ) (n : ℕ) : Prop :=
  A ⊆ Finset.Ioc 0 n ∧ ∀ᵉ (a ∈ A) (b ∈ A) (c ∈ A) (d ∈ A),
  a ≤ b → b ≤ c → c ≤ d → IsSquare (a * b * c * d) → a * d = b * c

def p (n : ℕ) (k : ℕ) : Prop := ∃ A : Finset ℕ, RequiredCondition A n ∧ A.card = k

-- CONJECTURE (believed FALSE): this is the only way the negated Θ can hold.
-- The construction primes ∪ squarefree semiprimes already gives g = O(f).
-- So ¬Θ is equivalent to ¬(f = O(g)), i.e. admissible sets beating every multiple of g infinitely often.
theorem erdos_87680_neg_hyp_large :
    ∀ C : ℝ, ∃ᶠ n : ℕ in atTop, ∃ A : Finset ℕ, RequiredCondition A n ∧
      C * ‖(n : ℝ) * Real.log (Real.log n) / Real.log n‖ < (A.card : ℝ) := by
  sorry

theorem erdos_87680_neg :
    ¬ ((fun n : ℕ ↦ (Nat.findGreatest (p n) n : ℝ)) =Θ[atTop]
      (fun n : ℕ ↦ (n : ℝ) * Real.log (Real.log n) / Real.log n)) := by
  intro h
  obtain ⟨c, hc⟩ := h.1.bound
  have hc' : ∀ᶠ n : ℕ in atTop, ‖(Nat.findGreatest (p n) n : ℝ)‖ ≤
      c * ‖(n : ℝ) * Real.log (Real.log n) / Real.log n‖ := hc
  obtain ⟨n, ⟨A, hA, hcard⟩, hn⟩ :=
    ((erdos_87680_neg_hyp_large c).and_eventually hc').exists
  have hAn : A.card ≤ n := by
    have := Finset.card_le_card hA.1
    simpa using this
  have hle : A.card ≤ Nat.findGreatest (p n) n := Nat.le_findGreatest hAn ⟨A, hA, rfl⟩
  have hle' : (A.card : ℝ) ≤ (Nat.findGreatest (p n) n : ℝ) := by exact_mod_cast hle
  have hnorm : ‖(Nat.findGreatest (p n) n : ℝ)‖ = (Nat.findGreatest (p n) n : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  linarith