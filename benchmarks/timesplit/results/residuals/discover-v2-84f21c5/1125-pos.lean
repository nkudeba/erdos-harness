namespace erdos_38829_hyp_chain_ns
theorem erdos_38829_hyp_chain :
    ∀ (f : ℝ → ℝ),
    (∀ x : ℝ, ∀ h : ℝ, h > 0 → 2 * f x ≤ f (x + h) + f (x + 2 * h)) →
    ∀ x y : ℝ, x < y → ∀ n : ℕ,
      (2 : ℝ) ^ n * (f x - f y) ≤ f (y - (1 / 2 : ℝ) ^ n * (y - x)) - f y := by
  intro f hf x y hxy n
  induction n with
  | zero => simp
  | succ n ih =>
    have hd : 0 < y - x := by linarith
    have hh : (1/2:ℝ)^(n+1) * (y-x) > 0 := by positivity
    have key := hf (y - (1/2:ℝ)^n * (y-x)) ((1/2:ℝ)^(n+1) * (y-x)) hh
    have e1 : y - (1/2:ℝ)^n * (y-x) + (1/2:ℝ)^(n+1) * (y-x)
        = y - (1/2:ℝ)^(n+1) * (y-x) := by ring
    have e2 : y - (1/2:ℝ)^n * (y-x) + 2 * ((1/2:ℝ)^(n+1) * (y-x)) = y := by ring
    rw [e1, e2] at key
    rw [pow_succ]
    nlinarith [ih, key]
end erdos_38829_hyp_chain_ns

theorem erdos_38829_hyp_chain :
    ∀ (f : ℝ → ℝ),
    (∀ x : ℝ, ∀ h : ℝ, h > 0 → 2 * f x ≤ f (x + h) + f (x + 2 * h)) →
    ∀ x y : ℝ, x < y → ∀ n : ℕ,
      (2 : ℝ) ^ n * (f x - f y) ≤ f (y - (1 / 2 : ℝ) ^ n * (y - x)) - f y := by
  exact erdos_38829_hyp_chain_ns.erdos_38829_hyp_chain



theorem erdos_38829_hyp_core :
    ∀ (f : ℝ → ℝ),
    (∀ x : ℝ, ∀ h : ℝ, h > 0 → 2 * f x ≤ f (x + h) + f (x + 2 * h)) →
    ∀ x y : ℝ, x < y → f y < f x →
      ∃ n : ℕ, f (y - (1 / 2 : ℝ) ^ n * (y - x)) - f y < (2 : ℝ) ^ n * (f x - f y) := by
  sorry

theorem erdos_38829 :
    ∀ (f : ℝ → ℝ)
    (hf : ∀ x : ℝ, ∀ h : ℝ, h > 0 → 2 * f x ≤ f (x + h) + f (x + 2 * h)),
    Monotone f := by
  intro f hf
  intro a b hab
  rcases eq_or_lt_of_le hab with h | h
  · rw [h]
  · by_contra hne
    have hlt : f b < f a := not_le.mp hne
    obtain ⟨n, hn⟩ := erdos_38829_hyp_core f hf a b h hlt
    have hc := erdos_38829_hyp_chain f hf a b h n
    linarith