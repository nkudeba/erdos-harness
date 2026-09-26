def erdos_58615_Admissible (f : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, ∀ h : ℝ, h > 0 → 2 * f x ≤ f (x + h) + f (x + 2 * h)

-- R1 (symmetry reduction): g(t) = f(x + t*(y-x)) is admissible whenever f is and x < y,
-- since h' = h*(y-x) > 0; then g 0 ≤ g 1 is f x ≤ f y. Pure affine rescaling.
namespace erdos_58615_hyp_wlog_unit_ns
theorem erdos_58615_hyp_wlog_unit :
    (∀ g : ℝ → ℝ, erdos_58615_Admissible g → g 0 ≤ g 1) →
      ∀ f : ℝ → ℝ, erdos_58615_Admissible f → Monotone f := by
  intro H f hf a b hab
  rcases eq_or_lt_of_le hab with h | h
  · rw [h]
  · have hg : erdos_58615_Admissible (fun t => f (a + t * (b - a))) := by
      intro t k hk
      have hpos : k * (b - a) > 0 := mul_pos hk (sub_pos.mpr h)
      have := hf (a + t * (b - a)) (k * (b - a)) hpos
      have e1 : a + (t + k) * (b - a) = a + t * (b - a) + k * (b - a) := by ring
      have e2 : a + (t + 2 * k) * (b - a) = a + t * (b - a) + 2 * (k * (b - a)) := by ring
      show 2 * f (a + t * (b - a)) ≤ f (a + (t + k) * (b - a)) + f (a + (t + 2 * k) * (b - a))
      rw [e1, e2]
      exact this
    have h0 : f (a + 0 * (b - a)) ≤ f (a + 1 * (b - a)) := H _ hg
    have e0 : a + 0 * (b - a) = a := by ring
    have e1' : a + 1 * (b - a) = b := by ring
    rwa [e0, e1'] at h0
end erdos_58615_hyp_wlog_unit_ns

theorem erdos_58615_hyp_wlog_unit :
    (∀ g : ℝ → ℝ, erdos_58615_Admissible g → g 0 ≤ g 1) →
      ∀ f : ℝ → ℝ, erdos_58615_Admissible f → Monotone f := by
  exact erdos_58615_hyp_wlog_unit_ns.erdos_58615_hyp_wlog_unit



-- Doubling lemma: if f 1 < f 0, put a_k = 1 - 1/2^k ∈ [0,1).
-- Apply the hypothesis at a_k with h = 1/2^(k+1); then a_k + h = a_{k+1} and a_k + 2h = 1.
-- This gives f(a_k) - f 1 ≥ 2^k (f 0 - f 1), contradicting any upper bound on f '' [0,1) (Archimedean).
namespace erdos_58615_hyp_bdd_imp_le_ns
theorem erdos_58615_hyp_bdd_imp_le :
    ∀ f : ℝ → ℝ, erdos_58615_Admissible f → BddAbove (f '' Set.Ico (0:ℝ) 1) → f 0 ≤ f 1 := by
  intro f hf hb
  by_contra hlt
  push_neg at hlt
  obtain ⟨M, hM⟩ := hb
  have key : ∀ k : ℕ, ((k:ℝ) + 1) * (f 0 - f 1) ≤ f (1 - (1/2:ℝ)^k) - f 1 := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      have hpos : (0:ℝ) < (1/2:ℝ)^(k+1) := by positivity
      have h1 := hf (1 - (1/2:ℝ)^k) ((1/2:ℝ)^(k+1)) hpos
      have e1 : (1:ℝ) - (1/2:ℝ)^k + (1/2:ℝ)^(k+1) = 1 - (1/2:ℝ)^(k+1) := by
        rw [pow_succ]; ring
      have e2 : (1:ℝ) - (1/2:ℝ)^k + 2 * (1/2:ℝ)^(k+1) = 1 := by
        rw [pow_succ]; ring
      rw [e1, e2] at h1
      push_cast
      have hk : (0:ℝ) ≤ (k:ℝ) * (f 0 - f 1) :=
        mul_nonneg (Nat.cast_nonneg k) (by linarith)
      nlinarith
  have hδ : (0:ℝ) < f 0 - f 1 := by linarith
  obtain ⟨k, hk⟩ := exists_nat_gt ((M - f 1) / (f 0 - f 1))
  have hk2 : M - f 1 < (k:ℝ) * (f 0 - f 1) := (div_lt_iff₀ hδ).mp hk
  have hmem : (1 - (1/2:ℝ)^k) ∈ Set.Ico (0:ℝ) 1 := by
    have a1 : (1/2:ℝ)^k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have a2 : (0:ℝ) < (1/2:ℝ)^k := by positivity
    exact ⟨by linarith, by linarith⟩
  have hle : f (1 - (1/2:ℝ)^k) ≤ M := hM (Set.mem_image_of_mem f hmem)
  have := key k
  nlinarith
end erdos_58615_hyp_bdd_imp_le_ns

theorem erdos_58615_hyp_bdd_imp_le :
    ∀ f : ℝ → ℝ, erdos_58615_Admissible f → BddAbove (f '' Set.Ico (0:ℝ) 1) → f 0 ≤ f 1 := by
  exact erdos_58615_hyp_bdd_imp_le_ns.erdos_58615_hyp_bdd_imp_le



-- Hard core: local boundedness above on [0,1) for every admissible f.
-- It follows from the target (a monotone f is bounded by f 1 there), so it is the genuine open content.
-- Kemperman (1969) reportedly proves regularity of such f; not verified, so it is kept as a conjecture.
theorem erdos_58615_hyp_bdd_above :
    ∀ f : ℝ → ℝ, erdos_58615_Admissible f → BddAbove (f '' Set.Ico (0:ℝ) 1) := by
  sorry

theorem erdos_58615 :
    ∀ (f : ℝ → ℝ)
    (hf : ∀ x : ℝ, ∀ h : ℝ, h > 0 → 2 * f x ≤ f (x + h) + f (x + 2 * h)),
    Monotone f := by
  intro f hf
  exact erdos_58615_hyp_wlog_unit
    (fun g hg => erdos_58615_hyp_bdd_imp_le g hg (erdos_58615_hyp_bdd_above g hg)) f hf