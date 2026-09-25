-- Why a counterexample must satisfy this: IsGreatest requires the formula value itself to be non-representable.
-- So a counterexample n whose formula value IS representable would refute the inner statement at once.
-- Believed FALSE: the harness verified formula(n) is non-representable for every eligible n <= 260.
-- (For those n the least representable integer in its residue class is exactly formula(n) + n.)
theorem erdos_44628_neg_hyp_formula_representable :
    ∃ n : ℕ, n ≠ 0 ∧ (∀ p k : ℕ, p.Prime → n ≠ p ^ k) ∧
      ∃ c : ℕ → ℕ,
        ((∑ p ∈ n.primeFactors,
          (∑ d ∈ Finset.Icc 1 (n.factorization p), (n.choose (p ^ d) : ℤ)) * ((p : ℤ) - 1)) - n)
          = ∑ i ∈ Finset.Ico 1 n, (c i : ℤ) * (n.choose i : ℤ) := by
  sorry

theorem erdos_44628_neg :
    ¬ (∀ (n : ℕ), n ≠ 0 →
      (∀ p k : ℕ, p.Prime → n ≠ p ^ k) →
      IsGreatest
        {m : ℤ | ¬ ∃ c : ℕ → ℕ, m = ∑ i ∈ Finset.Ico 1 n, (c i : ℤ) * (n.choose i : ℤ)}
        ((∑ p ∈ n.primeFactors,
          (∑ d ∈ Finset.Icc 1 (n.factorization p), (n.choose (p ^ d) : ℤ)) * ((p : ℤ) - 1)) - n)) := by
  intro h
  obtain ⟨n, hn0, hpp, c, hc⟩ := erdos_44628_neg_hyp_formula_representable
  have hmem := (h n hn0 hpp).1
  simp only [Set.mem_setOf_eq] at hmem
  exact hmem ⟨c, hc⟩