-- CHECK: mapClusterPt_iff_frequently Filter.frequently_atTop Metric.mem_nhds_iff Metric.isOpen_iff Filter.Frequently.and_eventually
open Filter
open scoped ArithmeticFunction.sigma

noncomputable def factorialDivisorRatio (n : ℕ) : ℝ :=
  (σ 0 (n + 1).factorial : ℝ) / (σ 0 n.factorial : ℝ)

def limitPointSet : Set ℝ :=
  {1} ∪ {x | ∃ k : ℕ, 1 ≤ k ∧ x = 1 + 1 / (k : ℝ)}

-- R1: τ multiplicative via factorization; (n+1)! = n! * (n+1), only primes dividing n+1 change.
namespace erdos_24786_hyp_product_formula_ns
-- CHECK: Nat.primeFactors_mono Nat.support_factorization ArithmeticFunction.sigma_zero_apply Nat.card_divisors
open Filter

open scoped ArithmeticFunction.sigma

private lemma fz_of_not_mem {m p : ℕ} (hm : m ≠ 0) (hp : p ∉ m.primeFactors) :
    m.factorization p = 0 := by
  rw [Nat.mem_primeFactors] at hp
  by_cases hpp : p.Prime
  · exact Nat.factorization_eq_zero_of_not_dvd (fun h => hp ⟨hpp, h, hm⟩)
  · exact Nat.factorization_eq_zero_of_not_prime m hpp

theorem erdos_24786_hyp_product_formula :
    ∀ n : ℕ, factorialDivisorRatio n =
      ∏ p ∈ (n + 1).primeFactors,
        (((n.factorial.factorization p : ℝ) + ((n + 1).factorization p : ℝ) + 1) /
          ((n.factorial.factorization p : ℝ) + 1)) := by
  intro n
  have h1 : (n+1).factorial ≠ 0 := Nat.factorial_ne_zero _
  have h0 : n.factorial ≠ 0 := Nat.factorial_ne_zero _
  have hn1 : n + 1 ≠ 0 := by omega
  have hfac : (n+1).factorial.factorization = n.factorial.factorization + (n+1).factorization := by
    rw [Nat.factorial_succ, Nat.factorization_mul hn1 h0, add_comm]
  have hsub0 : n.factorial.primeFactors ⊆ (n+1).factorial.primeFactors :=
    Nat.primeFactors_mono (Nat.factorial_dvd_factorial (Nat.le_succ n)) h1
  have hsub1 : (n+1).primeFactors ⊆ (n+1).factorial.primeFactors :=
    Nat.primeFactors_mono (Nat.dvd_factorial (Nat.succ_pos n) le_rfl) h1
  unfold factorialDivisorRatio
  rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply,
    Nat.card_divisors h1, Nat.card_divisors h0, Nat.cast_prod, Nat.cast_prod]
  have eA : ∏ p ∈ n.factorial.primeFactors, (((n.factorial.factorization p + 1 : ℕ)) : ℝ)
      = ∏ p ∈ (n+1).factorial.primeFactors, ((n.factorial.factorization p : ℝ) + 1) := by
    rw [Finset.prod_subset hsub0]
    · apply Finset.prod_congr rfl
      intro p _
      push_cast
      ring
    · intro p _ hp
      rw [fz_of_not_mem h0 hp]
      norm_num
  have eB : ∏ p ∈ (n+1).factorial.primeFactors, ((((n+1).factorial.factorization p + 1 : ℕ)) : ℝ)
      = ∏ p ∈ (n+1).factorial.primeFactors,
          ((n.factorial.factorization p : ℝ) + ((n + 1).factorization p : ℝ) + 1) := by
    apply Finset.prod_congr rfl
    intro p _
    rw [hfac, Finsupp.add_apply]
    push_cast
    ring
  rw [eA, eB, ← Finset.prod_div_distrib]
  symm
  apply Finset.prod_subset hsub1
  intro p _ hp
  rw [fz_of_not_mem hn1 hp, Nat.cast_zero, add_zero]
  exact div_self (by positivity)
end erdos_24786_hyp_product_formula_ns

theorem erdos_24786_hyp_product_formula :
    ∀ n : ℕ, factorialDivisorRatio n =
      ∏ p ∈ (n + 1).primeFactors,
        (((n.factorial.factorization p : ℝ) + ((n + 1).factorization p : ℝ) + 1) /
          ((n.factorial.factorization p : ℝ) + 1)) := by
  exact erdos_24786_hyp_product_formula_ns.erdos_24786_hyp_product_formula



-- R2: n+1 = p prime gives e_p = 0, a_p = 1, single factor 2.
namespace erdos_24786_hyp_prime_two_ns
-- CHECK: ArithmeticFunction.isMultiplicative_sigma ArithmeticFunction.IsMultiplicative.map_mul_of_coprime ArithmeticFunction.sigma_zero_apply Nat.Prime.divisors Nat.Prime.coprime_iff_not_dvd
open Filter

open scoped ArithmeticFunction.sigma

theorem erdos_24786_hyp_prime_two :
    ∀ p : ℕ, p.Prime → factorialDivisorRatio (p - 1) = 2 := by
  intro p hp
  have h1 : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_lt.le
  unfold factorialDivisorRatio
  rw [h1]
  have hfac : p.factorial = p * (p - 1).factorial := by
    have := Nat.factorial_succ (p - 1)
    rw [h1] at this
    exact this
  have hcop : Nat.Coprime p (p - 1).factorial := by
    rw [Nat.Prime.coprime_iff_not_dvd hp, Nat.Prime.dvd_factorial hp]
    have := hp.one_lt
    omega
  have hmul : σ 0 (p * (p - 1).factorial) = σ 0 p * σ 0 (p - 1).factorial :=
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop
  have hp2 : σ 0 p = 2 := by
    rw [ArithmeticFunction.sigma_zero_apply, Nat.Prime.divisors hp]
    exact Finset.card_pair hp.one_lt.ne
  have hpos : (σ 0 (p - 1).factorial : ℝ) ≠ 0 := by
    rw [ArithmeticFunction.sigma_zero_apply]
    have : 0 < ((p - 1).factorial.divisors).card :=
      Finset.card_pos.mpr (Nat.nonempty_divisors.mpr (Nat.factorial_ne_zero _))
    exact_mod_cast this.ne'
  rw [hfac, hmul, hp2]
  push_cast
  field_simp
end erdos_24786_hyp_prime_two_ns

theorem erdos_24786_hyp_prime_two :
    ∀ p : ℕ, p.Prime → factorialDivisorRatio (p - 1) = 2 := by
  exact erdos_24786_hyp_prime_two_ns.erdos_24786_hyp_prime_two



-- R3: for n+1 = k*p with p prime > k, v_p(n!) = k-1, other primes q | k have v_q(n!) ≥ p-1.
theorem erdos_24786_hyp_sandwich :
    ∀ k p n : ℕ, 1 ≤ k → p.Prime → k < p → n + 1 = k * p →
      1 + 1 / (k : ℝ) ≤ factorialDivisorRatio n ∧
      factorialDivisorRatio n ≤
        (1 + 1 / (k : ℝ)) * ∏ q ∈ k.primeFactors, (1 + (k.factorization q : ℝ) / (p : ℝ)) := by
  sorry

-- R4: every factor ≥ 1, and some prime divides n+1 ≥ 2 with a ≥ 1.
namespace erdos_24786_hyp_gt_one_ns
-- CHECK: ArithmeticFunction.sigma_zero_apply Nat.divisors_subset_of_dvd Finset.ssubset_iff_of_subset Nat.mem_divisors_self
open Filter

open scoped ArithmeticFunction.sigma

theorem erdos_24786_hyp_gt_one :
    ∀ n : ℕ, 1 ≤ n → 1 < factorialDivisorRatio n := by
  intro n hn
  have hf0 : n.factorial ≠ 0 := Nat.factorial_ne_zero n
  have hf1 : (n+1).factorial ≠ 0 := Nat.factorial_ne_zero (n+1)
  have hlt : n.factorial < (n+1).factorial := by
    rw [Nat.factorial_succ]
    have : 0 < n.factorial := Nat.factorial_pos n
    nlinarith
  have hsub : n.factorial.divisors ⊆ (n+1).factorial.divisors :=
    Nat.divisors_subset_of_dvd hf1 (Nat.factorial_dvd_factorial (Nat.le_succ n))
  have hss : n.factorial.divisors ⊂ (n+1).factorial.divisors := by
    rw [Finset.ssubset_iff_of_subset hsub]
    refine ⟨(n+1).factorial, Nat.mem_divisors_self _ hf1, ?_⟩
    intro hmem
    rw [Nat.mem_divisors] at hmem
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hf0) hmem.1
    omega
  have hcard := Finset.card_lt_card hss
  have hN : σ 0 n.factorial < σ 0 (n+1).factorial := by
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact hcard
  have hpos : (0:ℝ) < (σ 0 n.factorial : ℝ) := by
    have : 0 < σ 0 n.factorial := by
      rw [ArithmeticFunction.sigma_zero_apply]
      exact Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hf0⟩
    exact_mod_cast this
  unfold factorialDivisorRatio
  rw [one_lt_div hpos]
  exact_mod_cast hN
end erdos_24786_hyp_gt_one_ns

theorem erdos_24786_hyp_gt_one :
    ∀ n : ℕ, 1 ≤ n → 1 < factorialDivisorRatio n := by
  exact erdos_24786_hyp_gt_one_ns.erdos_24786_hyp_gt_one



-- L is {1} together with a sequence 1 + 1/k decreasing to 1; the only accumulation point is 1 ∈ L.
namespace erdos_24786_hyp_closed_ns
open Filter

open scoped ArithmeticFunction.sigma

theorem erdos_24786_hyp_closed : IsClosed limitPointSet := by
  have hf : Tendsto (fun k : ℕ => (1:ℝ) + 1 / ((k:ℝ) + 1)) atTop (nhds 1) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat).const_add (1:ℝ)
    rw [add_zero] at h
    exact h
  have hset : limitPointSet = insert 1 (Set.range (fun k : ℕ => (1:ℝ) + 1 / ((k:ℝ) + 1))) := by
    ext x
    simp only [limitPointSet, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq,
      Set.mem_insert_iff, Set.mem_range]
    constructor
    · rintro (h | ⟨k, hk, rfl⟩)
      · exact Or.inl h
      · right
        refine ⟨k - 1, ?_⟩
        have hc : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by
          rw [Nat.cast_sub hk]; push_cast; ring
        show (1:ℝ) + 1 / (((k - 1 : ℕ) : ℝ) + 1) = 1 + 1 / (k : ℝ)
        rw [hc]
    · rintro (h | ⟨k, rfl⟩)
      · exact Or.inl h
      · right
        refine ⟨k + 1, by omega, ?_⟩
        show (1:ℝ) + 1 / ((k:ℝ) + 1) = 1 + 1 / (((k + 1 : ℕ)) : ℝ)
        rw [Nat.cast_succ]
  rw [hset]
  exact hf.isCompact_insert_range.isClosed
end erdos_24786_hyp_closed_ns

theorem erdos_24786_hyp_closed : IsClosed limitPointSet := by
  exact erdos_24786_hyp_closed_ns.erdos_24786_hyp_closed



-- Lemma A + Lemma B: R(n) = g(n)·Q(n), g(n) ∈ L, 1 ≤ Q(n) ≤ exp(log2(n+1)/(√n-1)) → 1, and g ≤ 2.
theorem erdos_24786_hyp_approx :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∃ y ∈ limitPointSet, |factorialDivisorRatio n - y| < ε := by
  sorry

-- From R3: take n = k*p - 1 with p prime, p → ∞ (infinitely many primes).
theorem erdos_24786_hyp_witness :
    ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n ≥ N,
      |factorialDivisorRatio n - (1 + 1 / (k : ℝ))| < ε := by
  sorry

-- From R3 with k large (diagonal), or n = 2^j - 1: R = (v₂(n!)+j+1)/(v₂(n!)+1) → 1.
theorem erdos_24786_hyp_witness_one :
    ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n ≥ N, |factorialDivisorRatio n - 1| < ε := by
  sorry

theorem erdos_24786 :
    {x : ℝ | MapClusterPt x atTop factorialDivisorRatio} = limitPointSet := by
  have key : ∀ y : ℝ, (∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n ≥ N, |factorialDivisorRatio n - y| < ε) →
      MapClusterPt y atTop factorialDivisorRatio := by
    intro y hy
    rw [mapClusterPt_iff_frequently]
    intro s hs
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hs
    rw [Filter.frequently_atTop]
    intro N
    obtain ⟨n, hn, hlt⟩ := hy ε hε N
    refine ⟨n, hn, hsub ?_⟩
    rw [Metric.mem_ball, Real.dist_eq]
    exact hlt
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hx
    by_contra hxL
    have hopen : IsOpen (limitPointSetᶜ) := erdos_24786_hyp_closed.isOpen_compl
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen x hxL
    have hfreq : ∃ᶠ n in atTop, factorialDivisorRatio n ∈ Metric.ball x (δ / 2) :=
      (mapClusterPt_iff_frequently.mp hx) _ (Metric.ball_mem_nhds x (by linarith))
    have hev := erdos_24786_hyp_approx (δ / 2) (by linarith)
    obtain ⟨n, hn1, y, hyL, hy⟩ := (hfreq.and_eventually hev).exists
    have hyx : y ∈ Metric.ball x δ := by
      rw [Metric.mem_ball, Real.dist_eq] at hn1 ⊢
      rw [abs_sub_lt_iff] at hn1 hy ⊢
      obtain ⟨h1, h2⟩ := hn1
      obtain ⟨h3, h4⟩ := hy
      constructor <;> linarith
    exact hball hyx hyL
  · intro hx
    simp only [limitPointSet, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq] at hx
    rcases hx with rfl | ⟨k, hk, rfl⟩
    · exact key 1 erdos_24786_hyp_witness_one
    · exact key _ (erdos_24786_hyp_witness k hk)