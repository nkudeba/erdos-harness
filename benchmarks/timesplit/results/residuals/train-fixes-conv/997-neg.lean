-- Sufficient condition that is strictly quantitative: a single α together with an explicit
-- sublinear discrepancy bound g(k) = o(k) that holds uniformly over all windows and intervals.
-- A witness for the target must satisfy this (take g k = sup of the window discrepancies).
-- Believed FALSE: Maynard–Tao plus Banks–Freiberg–Maynard produce arbitrarily long runs of
-- consecutive primes that cluster mod 1 (see the notes).
theorem erdos_56307_neg_hyp_uniform_bound :
    ∃ α : ℝ, ∃ g : ℕ → ℝ,
      Filter.Tendsto (fun k : ℕ => g k / (k : ℝ)) Filter.atTop (nhds 0) ∧
      ∀ k n : ℕ, ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
        |(((Finset.Ioc n (n + k)).filter
            (fun m ↦ Int.fract (α * (m.nth Nat.Prime)) ∈ Set.Ico a b)).card : ℝ)
          - (b - a) * k| ≤ g k := by
  sorry

open Set

def IsWellDistributed (x : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ k in Filter.atTop, ∀ n : ℕ,
  ∀ a b, 0 ≤ a → a ≤ b → b ≤ 1 →
    letI I := Ico a b
    let count := (Finset.Ioc n (n + k)).filter (fun m ↦ x m ∈ I)
    abs ((count.card : ℝ) - (b - a) * k) < ε * k

theorem erdos_56307_neg :
    ¬ (∀ α : ℝ, ¬ IsWellDistributed (fun n ↦ Int.fract (α * (n.nth Nat.Prime)))) := by
  intro h
  obtain ⟨α, g, hg, hbound⟩ := erdos_56307_neg_hyp_uniform_bound
  apply h α
  intro ε hε
  have h1 : ∀ᶠ k : ℕ in Filter.atTop, g k / (k : ℝ) ∈ Iio ε :=
    hg.eventually (Iio_mem_nhds hε)
  have h2 : ∀ᶠ k : ℕ in Filter.atTop, 1 ≤ k := Filter.eventually_ge_atTop 1
  filter_upwards [h1, h2] with k hk hk1
  intro n a b ha hab hb1
  have hkpos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hk' : g k / (k : ℝ) < ε := hk
  have hlt : g k < ε * k := by
    rwa [div_lt_iff₀ hkpos] at hk'
  exact lt_of_le_of_lt (hbound k n a b ha hab hb1) hlt