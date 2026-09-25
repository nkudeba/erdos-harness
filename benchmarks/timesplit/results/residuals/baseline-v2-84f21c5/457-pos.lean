def erdos_32534_resGood (ε : ℝ) (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ⌊Real.log n⌋₊ < p → (p : ℝ) ≤ (2 + ε) * Real.log n →
    p - ⌊Real.log n⌋₊ ≤ n % p

-- DERIVED (R1): p prime. If p ≤ k, then k consecutive integers contain a multiple of p.
-- If p > k, at most one of n+1..n+k is a multiple of p. p divides n+i iff i ≡ -n (mod p).
-- For i in [1,k] that means i = p - n % p (needs n % p > 0), i.e. p ≤ k + n % p.
-- k = 0: the product is 1 and p ≤ n % p is false, so both sides are false.
namespace erdos_32534_hyp_dvd_iff_ns
theorem erdos_32534_hyp_dvd_iff :
    ∀ p n k : ℕ, p.Prime →
      (p ∣ ∏ i ∈ Finset.Icc 1 k, (n + i) ↔ p ≤ k + n % p) := by
  intro p n k hp
  rw [Prime.dvd_finsetProd_iff hp.prime]
  have hdm := Nat.div_add_mod n p
  have hlt := Nat.mod_lt n hp.pos
  generalize n / p = q at hdm
  generalize n % p = r at hdm hlt ⊢
  subst hdm
  constructor
  · rintro ⟨i, hi, hdvd⟩
    rw [Finset.mem_Icc] at hi
    have h1 : p ∣ r + i := by
      have : p * q + r + i = p * q + (r + i) := by ring
      rw [this] at hdvd
      exact (Nat.dvd_add_right (dvd_mul_right p q)).mp hdvd
    have := Nat.le_of_dvd (by omega) h1
    omega
  · intro h
    refine ⟨p - r, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    refine ⟨q + 1, ?_⟩
    rw [Nat.mul_succ]
    omega
end erdos_32534_hyp_dvd_iff_ns

theorem erdos_32534_hyp_dvd_iff :
    ∀ p n k : ℕ, p.Prime →
      (p ∣ ∏ i ∈ Finset.Icc 1 k, (n + i) ↔ p ≤ k + n % p) := by
  exact erdos_32534_hyp_dvd_iff_ns.erdos_32534_hyp_dvd_iff



-- DERIVED (open core, residue form of the target via R1): infinitely many n satisfy the
-- CRT-type condition n % p ≥ p - ⌊log n⌋ for every prime p in (⌊log n⌋, (2+ε) log n].
-- Heuristic density is ∏ k/p = exp(-O(k/log k)); a proof needs equidistribution beyond sieve/CRT.
theorem erdos_32534_hyp_core :
    ∃ ε > (0 : ℝ), { n : ℕ | erdos_32534_resGood ε n }.Infinite := by
  sorry

theorem erdos_32534 :
    ∃ ε > (0 : ℝ),
    { (n : ℕ) | ∀ (p : ℕ), p ≤ (2 + ε) * Real.log n → p.Prime →
      p ∣ ∏ i ∈ Finset.Icc 1 ⌊Real.log n⌋₊, (n + i) }.Infinite := by
  obtain ⟨ε, hε, hinf⟩ := erdos_32534_hyp_core
  refine ⟨ε, hε, Set.Infinite.mono ?_ hinf⟩
  intro n hn
  have hn' : erdos_32534_resGood ε n := hn
  rw [Set.mem_setOf_eq]
  intro p hp hpp
  rw [erdos_32534_hyp_dvd_iff p n _ hpp]
  by_cases hk : p ≤ ⌊Real.log (n : ℝ)⌋₊
  · omega
  · have hlt : ⌊Real.log (n : ℝ)⌋₊ < p := by omega
    have h := hn' p hpp hlt hp
    omega