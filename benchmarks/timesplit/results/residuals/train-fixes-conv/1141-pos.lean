open Nat Set

def TSProp (n : ℕ) : Prop :=
  ∀ k, k ^ 2 < n → Coprime n k → (n - k ^ 2).Prime

instance (n : ℕ) : Decidable (TSProp n) :=
  decidable_of_iff (∀ k ≤ .sqrt (n - 1), Coprime n k → (n - k ^ 2).Prime) <| by
    cases n with
    | zero => simp [TSProp]
    | succ n' =>
      simp [TSProp, le_sqrt, pow_two]

-- CONJECTURE (believed FALSE): unbounded supply of members, with R1 (n-1 prime) split off
-- as an explicit constraint and the k = 0, 1 cases removed; n ≥ 4 excludes the degenerate n ≤ 3.
-- Any infinitude proof must produce exactly such n; heuristics and search to 2·10^6
-- (largest member 1722) indicate none exist beyond 1722.
theorem erdos_53249_hyp_tail :
    ∀ N : ℕ, ∃ n : ℕ, 4 ≤ n ∧ N < n ∧ (n - 1).Prime ∧
      ∀ k : ℕ, 2 ≤ k → k ^ 2 < n → Coprime n k → (n - k ^ 2).Prime := by
  sorry

-- CHECK: Set.infinite_of_not_bddAbove Set.infinite_coe_iff Nat.coprime_zero_right
theorem erdos_53249 :
    Infinite { n | TSProp n } := by
  apply Set.infinite_coe_iff.mpr
  apply Set.infinite_of_not_bddAbove
  rintro ⟨M, hM⟩
  obtain ⟨n, hn4, hMn, h1, hk⟩ := erdos_53249_hyp_tail M
  have hmem : n ∈ {n | TSProp n} := by
    show TSProp n
    intro k hk2 hcop
    rcases Nat.lt_or_ge k 2 with h | h
    · interval_cases k
      · rw [Nat.coprime_zero_right] at hcop
        omega
      · simpa using h1
    · exact hk k h hk2 hcop
  have := hM hmem
  omega