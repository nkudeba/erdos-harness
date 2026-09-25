-- CHECK: Set.infinite_of_not_bddAbove Nat.le_add_left
-- Local residue criterion (reduction R2, "if" direction only). Proof sketch: put i = p - n % p.
-- Then 1 ≤ i ≤ k, and n + i = p * (n / p + 1), so p divides the factor n + i and hence the product.
-- The hypothesis also covers p ≤ k automatically (reduction R1), since then p ≤ n % p + k.
namespace erdos_72072_hyp_local_ns
theorem erdos_72072_hyp_local :
    ∀ n k p : ℕ, 0 < p → p ≤ n % p + k → p ∣ ∏ i ∈ Finset.Icc 1 k, (n + i) := by
  intro n k p hp hle
  have hr : n % p < p := Nat.mod_lt n hp
  have hmem : p - n % p ∈ Finset.Icc 1 k := by
    rw [Finset.mem_Icc]; omega
  have hdiv : p ∣ n + (p - n % p) := by
    have h := Nat.div_add_mod n p
    refine ⟨n / p + 1, ?_⟩
    rw [Nat.mul_add, Nat.mul_one]
    generalize p * (n / p) = q at h ⊢
    generalize n % p = r at h hr ⊢
    omega
  exact dvd_trans hdiv (Finset.dvd_prod_of_mem (fun i => n + i) hmem)
end erdos_72072_hyp_local_ns

theorem erdos_72072_hyp_local :
    ∀ n k p : ℕ, 0 < p → p ≤ n % p + k → p ∣ ∏ i ∈ Finset.Icc 1 k, (n + i) := by
  exact erdos_72072_hyp_local_ns.erdos_72072_hyp_local



-- Open core (reduction R3): the residue-class covering problem, with the product removed.
-- Primes p ≤ ⌊log n⌋ are dropped (R1). For each prime p in (⌊log n⌋, (2+ε) log n],
-- n must lie in one of the k allowed classes p-k, ..., p-1 mod p (R2).
-- Expected true by the first-moment heuristic; the known method only reaches 2-δ (CRT/PNT).
theorem erdos_72072_hyp_core :
    ∃ ε > (0 : ℝ), ∀ N : ℕ, ∃ n ≥ N, ∀ p : ℕ, p.Prime → ⌊Real.log n⌋₊ < p →
      (p : ℝ) ≤ (2 + ε) * Real.log n → p ≤ n % p + ⌊Real.log n⌋₊ := by
  sorry

theorem erdos_72072 :
    ∃ ε > (0 : ℝ),
    { (n : ℕ) | ∀ (p : ℕ), p ≤ (2 + ε) * Real.log n → p.Prime →
      p ∣ ∏ i ∈ Finset.Icc 1 ⌊Real.log n⌋₊, (n + i) }.Infinite := by
  obtain ⟨ε, hε, hcore⟩ := erdos_72072_hyp_core
  refine ⟨ε, hε, ?_⟩
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  obtain ⟨n, hnB, hn⟩ := hcore (B + 1)
  have hle : n ≤ B := by
    apply hB
    simp only [Set.mem_setOf_eq]
    intro p hp hprime
    apply erdos_72072_hyp_local n ⌊Real.log (n : ℝ)⌋₊ p hprime.pos
    by_cases hk : ⌊Real.log (n : ℝ)⌋₊ < p
    · exact hn p hprime hk hp
    · exact le_trans (not_lt.mp hk) (Nat.le_add_left _ _)
  omega