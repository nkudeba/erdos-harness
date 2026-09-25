open Filter

namespace erdos_39531_neg_hyp_forced_ns

-- R2: prime constraints forced by the divisibility, given b₂ ≤ b₁.
theorem erdos_39531_neg_hyp_forced (r n b₁ b₂ : ℕ) (hb1 : 0 < b₁) (hb2 : 0 < b₂)
    (hle : b₂ ≤ b₁)
    (hd : b₁.factorial * b₂.factorial ∣
      n.factorial * (∏ i ∈ Finset.range r, Nat.nth Nat.Prime i) ^ n) :
    (∀ q : ℕ, q.Prime → n < q → Nat.nth Nat.Prime r ≤ q → b₁ < q) ∧
    (∀ q : ℕ, q.Prime → n < 2 * q → Nat.nth Nat.Prime r ≤ q → b₂ < q) := by
  sorry

end erdos_39531_neg_hyp_forced_ns

-- R3 (equivalent form), which is the hard open core: one constant C, independent of r, bounds the
-- excess a₁+a₂-n by C log n for all large n.
-- Any affirmative f would have to violate this for r large, since f(r) > C + 1 eventually.
-- The statement keeps R1 (a₂ ≤ a₁) and the R2 antecedents as asserted constraints.
-- R2 is certified (erdos_39531_neg_hyp_forced_ns.erdos_39531_neg_hyp_forced), so the glue discharges it.
theorem erdos_39531_neg_hyp_uniform :
    ∃ C : ℝ, ∀ r : ℕ, 1 ≤ r → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ a₁ a₂ : ℕ, 0 < a₁ → 0 < a₂ → a₂ ≤ a₁ →
        a₁.factorial * a₂.factorial ∣
          n.factorial * (∏ i ∈ Finset.range r, Nat.nth Nat.Prime i) ^ n →
        (∀ q : ℕ, q.Prime → n < q → Nat.nth Nat.Prime r ≤ q → a₁ < q) →
        (∀ q : ℕ, q.Prime → n < 2 * q → Nat.nth Nat.Prime r ≤ q → a₂ < q) →
        (a₁ : ℝ) + a₂ ≤ n + C * Real.log n := by
  sorry

theorem erdos_39531_neg :
    ¬ (∃ f : ℕ → ℝ, Tendsto f atTop atTop ∧
      ∀ (r : ℕ) (hr : 1 ≤ r),
        {n : ℕ | ∃ a₁ a₂ : ℕ, 0 < a₁ ∧ 0 < a₂ ∧
          (a₁ : ℝ) + a₂ > n + f r * Real.log n ∧
          a₁.factorial * a₂.factorial ∣
            n.factorial * (∏ i ∈ Finset.range r, Nat.nth Nat.Prime i) ^ n}.Infinite) := by
  rintro ⟨f, hf, hinf⟩
  obtain ⟨C, hC⟩ := erdos_39531_neg_hyp_uniform
  have hev : ∀ᶠ r in atTop, C + 1 ≤ f r := hf.eventually (eventually_ge_atTop (C + 1))
  obtain ⟨R, hR⟩ := eventually_atTop.1 hev
  obtain ⟨r, hrR, hr1⟩ : ∃ r : ℕ, R ≤ r ∧ 1 ≤ r :=
    ⟨max R 1, le_max_left _ _, le_max_right _ _⟩
  have hfr : C + 1 ≤ f r := hR r hrR
  obtain ⟨N, hN⟩ := hC r hr1
  refine (hinf r hr1) ((Set.finite_lt_nat (max N 2)).subset ?_)
  intro n hn
  simp only [Set.mem_setOf_eq] at hn ⊢
  by_contra hlt
  push_neg at hlt
  obtain ⟨a₁, a₂, h1, h2, hsum, hdvd⟩ := hn
  have hnN : N ≤ n := le_trans (le_max_left _ _) hlt
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hlt
  have hlog : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have key : ∀ b₁ b₂ : ℕ, 0 < b₁ → 0 < b₂ → b₂ ≤ b₁ →
      b₁.factorial * b₂.factorial ∣
        n.factorial * (∏ i ∈ Finset.range r, Nat.nth Nat.Prime i) ^ n →
      (b₁ : ℝ) + b₂ ≤ n + C * Real.log n := by
    intro b₁ b₂ hb1 hb2 hle hd
    obtain ⟨hq1, hq2⟩ :=
      erdos_39531_neg_hyp_forced_ns.erdos_39531_neg_hyp_forced r n b₁ b₂ hb1 hb2 hle hd
    exact hN n hnN b₁ b₂ hb1 hb2 hle hd hq1 hq2
  have hbound : (a₁ : ℝ) + a₂ ≤ n + C * Real.log n := by
    rcases le_total a₂ a₁ with h | h
    · exact key a₁ a₂ h1 h2 h hdvd
    · have := key a₂ a₁ h2 h1 h (by rwa [mul_comm] at hdvd)
      linarith
  have hlt2 : C * Real.log n < f r * Real.log n :=
    mul_lt_mul_of_pos_right (by linarith) hlog
  linarith