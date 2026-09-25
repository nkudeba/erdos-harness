open Filter

-- CHECK: Set.infinite_of_forall_exists_gt Nat.factorial_one dvd_mul_right

def erdos_51534_S (r : ℕ) (M : ℝ) : Set ℕ :=
  {n : ℕ | ∃ a₁ a₂ : ℕ, 0 < a₁ ∧ 0 < a₂ ∧
    (a₁ : ℝ) + a₂ > n + M * Real.log n ∧
    a₁.factorial * a₂.factorial ∣
      n.factorial * (∏ i ∈ Finset.range r, Nat.nth Nat.Prime i) ^ n}

def erdos_51534_LargeCarry (q n a₁ a₂ : ℕ) : Prop :=
  a₁ ≤ n ∧ a₂ ≤ n ∧
    ∀ p : ℕ, p.Prime → q ≤ p →
      padicValNat p a₁.factorial + padicValNat p a₂.factorial ≤ padicValNat p n.factorial

-- Derived (R1 bookkeeping): pick R_m for each integer m, and let f r be the largest m ≤ r
-- with R_j ≤ r for all j ≤ m (fall back to 0, using the first premise).
-- Then f r is an integer m with R_m ≤ r, and f tends to infinity.
namespace erdos_51534_hyp_bookkeeping_ns
open Filter

open Filter

theorem erdos_51534_hyp_bookkeeping :
    ∀ S : ℕ → ℝ → Set ℕ, (∀ r : ℕ, 1 ≤ r → (S r 0).Infinite) →
      (∀ M : ℝ, ∃ R : ℕ, ∀ r : ℕ, R ≤ r → (S r M).Infinite) →
      ∃ f : ℕ → ℝ, Tendsto f atTop atTop ∧ ∀ r : ℕ, 1 ≤ r → (S r (f r)).Infinite := by
  classical
  intro S h1 h2
  choose R hR using h2
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℕ, ∀ r, g r =
      Nat.findGreatest (fun m => R (m:ℝ) ≤ r) r := ⟨_, fun _ => rfl⟩
  refine ⟨fun r => (g r : ℝ), ?_, ?_⟩
  · rw [Filter.tendsto_atTop]
    intro b
    rw [Filter.eventually_atTop]
    refine ⟨max ⌈b⌉₊ (R (⌈b⌉₊ : ℝ)), fun r hr => ?_⟩
    have hA : ⌈b⌉₊ ≤ r := le_of_max_le_left hr
    have hB : R (⌈b⌉₊ : ℝ) ≤ r := le_of_max_le_right hr
    have h3 : ⌈b⌉₊ ≤ g r := by
      rw [hg r]
      exact Nat.le_findGreatest (P := fun m => R (m:ℝ) ≤ r) hA hB
    have h4 : (⌈b⌉₊ : ℝ) ≤ (g r : ℝ) := by exact_mod_cast h3
    exact le_trans (Nat.le_ceil b) h4
  · intro r hr
    show (S r ((g r : ℕ) : ℝ)).Infinite
    by_cases h0 : g r = 0
    · rw [h0, Nat.cast_zero]
      exact h1 r hr
    · have hspec : R ((g r : ℕ) : ℝ) ≤ r :=
        Nat.findGreatest_of_ne_zero (P := fun m => R (m:ℝ) ≤ r) (hg r).symm h0
      exact hR _ r hspec
end erdos_51534_hyp_bookkeeping_ns

theorem erdos_51534_hyp_bookkeeping :
    ∀ S : ℕ → ℝ → Set ℕ, (∀ r : ℕ, 1 ≤ r → (S r 0).Infinite) →
      (∀ M : ℝ, ∃ R : ℕ, ∀ r : ℕ, R ≤ r → (S r M).Infinite) →
      ∃ f : ℕ → ℝ, Tendsto f atTop atTop ∧ ∀ r : ℕ, 1 ≤ r → (S r (f r)).Infinite := by
  exact erdos_51534_hyp_bookkeeping_ns.erdos_51534_hyp_bookkeeping



-- Derived (R2): P = ∏_{i<r} p_i is squarefree, with prime divisors exactly the primes < nth Prime r.
-- For p ≥ q we have v_p(P^n) = 0, and the carry condition is assumed.
-- For p < q we have v_p(P^n) = n, v_p(a₁!) ≤ v_p(n!) since a₁ ≤ n, and v_p(a₂!) ≤ a₂ ≤ n.
-- Conclude by Nat.factorization_le_iff_dvd.
namespace erdos_51534_hyp_reduction_ns
-- CHECK: sub_one_mul_padicValNat_factorial Nat.nth_count Nat.nth_lt_nth Nat.Prime.factorization_pos_of_dvd Nat.factorization_def
open Filter

open Filter

private lemma erdos_51534_vfact_le (p m : ℕ) (hp : p.Prime) :
    m.factorial.factorization p ≤ m := by
  haveI := Fact.mk hp
  rw [Nat.factorization_def _ hp]
  have e := sub_one_mul_padicValNat_factorial (p := p) m
  have h1' : 1 ≤ p - 1 := by have := hp.two_le; omega
  have h2' := mul_le_mul_of_nonneg_right h1' (Nat.zero_le (padicValNat p m.factorial))
  rw [one_mul] at h2'
  omega

theorem erdos_51534_hyp_reduction :
    ∀ r n a₁ a₂ : ℕ, erdos_51534_LargeCarry (Nat.nth Nat.Prime r) n a₁ a₂ →
      a₁.factorial * a₂.factorial ∣
        n.factorial * (∏ i ∈ Finset.range r, Nat.nth Nat.Prime i) ^ n := by
  intro r n a₁ a₂ h
  obtain ⟨h1, h2, h3⟩ := h
  set P := ∏ i ∈ Finset.range r, Nat.nth Nat.Prime i with hP
  have hPpos : P ≠ 0 := by
    rw [hP, Finset.prod_ne_zero_iff]
    intro i _
    exact (Nat.prime_nth_prime i).ne_zero
  have hL : a₁.factorial * a₂.factorial ≠ 0 :=
    mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)
  have hR : n.factorial * P ^ n ≠ 0 :=
    mul_ne_zero (Nat.factorial_ne_zero n) (pow_ne_zero _ hPpos)
  refine (Nat.factorization_le_iff_dvd hL hR).mp (fun p => ?_)
  by_cases hp : p.Prime
  · rw [Nat.factorization_mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _),
      Nat.factorization_mul (Nat.factorial_ne_zero _) (pow_ne_zero _ hPpos),
      Nat.factorization_pow]
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    by_cases hq : Nat.nth Nat.Prime r ≤ p
    · have := h3 p hp hq
      rw [← Nat.factorization_def _ hp, ← Nat.factorization_def _ hp,
        ← Nat.factorization_def _ hp] at this
      omega
    · push_neg at hq
      have hinf := Nat.infinite_setOf_prime
      have hc : Nat.nth Nat.Prime (Nat.count Nat.Prime p) = p := Nat.nth_count hp
      have hlt : Nat.count Nat.Prime p < r := by
        rw [← Nat.nth_lt_nth hinf, hc]; exact hq
      have hdvd : p ∣ P := by
        rw [hP, ← hc]
        exact Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hlt)
      have hfp : 0 < P.factorization p := hp.factorization_pos_of_dvd hPpos hdvd
      have hA : a₁.factorial.factorization p ≤ n.factorial.factorization p :=
        (Nat.factorization_le_iff_dvd (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)).mpr
          (Nat.factorial_dvd_factorial h1) p
      have hB := erdos_51534_vfact_le p a₂ hp
      have : n ≤ n * P.factorization p := by nlinarith
      omega
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
    exact Nat.zero_le _
end erdos_51534_hyp_reduction_ns

theorem erdos_51534_hyp_reduction :
    ∀ r n a₁ a₂ : ℕ, erdos_51534_LargeCarry (Nat.nth Nat.Prime r) n a₁ a₂ →
      a₁.factorial * a₂.factorial ∣
        n.factorial * (∏ i ∈ Finset.range r, Nat.nth Nat.Prime i) ^ n := by
  exact erdos_51534_hyp_reduction_ns.erdos_51534_hyp_reduction



-- Derived (core; the random-pair argument of the discovery stage).
-- Choose a₁, a₂ uniform in [Y, 2Y-k) with k = ⌈M log 4Y⌉ + 1.
-- For q with (q-1)/(40 log q) ≥ M, carries at every prime p ≥ q compensate the block with high
-- probability: a union bound for p > (log Y)^3, and Hoeffding on base-p digits for p ≤ (log Y)^3.
theorem erdos_51534_hyp_core :
    ∀ M : ℝ, ∃ R : ℕ, ∀ r : ℕ, R ≤ r → ∀ N₀ : ℕ, ∃ n : ℕ, N₀ ≤ n ∧
      ∃ a₁ a₂ : ℕ, 0 < a₁ ∧ 0 < a₂ ∧ (a₁ : ℝ) + a₂ > n + M * Real.log n ∧
        erdos_51534_LargeCarry (Nat.nth Nat.Prime r) n a₁ a₂ := by
  sorry

open Filter

theorem erdos_51534 :
    ∃ f : ℕ → ℝ, Tendsto f atTop atTop ∧
      ∀ (r : ℕ) (hr : 1 ≤ r),
        {n : ℕ | ∃ a₁ a₂ : ℕ, 0 < a₁ ∧ 0 < a₂ ∧
          (a₁ : ℝ) + a₂ > n + f r * Real.log n ∧
          a₁.factorial * a₂.factorial ∣
            n.factorial * (∏ i ∈ Finset.range r, Nat.nth Nat.Prime i) ^ n}.Infinite := by
  have h0 : ∀ r : ℕ, 1 ≤ r → (erdos_51534_S r 0).Infinite := by
    intro r _
    apply Set.infinite_of_forall_exists_gt
    intro N
    refine ⟨N + 1, ?_, Nat.lt_succ_self N⟩
    simp only [erdos_51534_S, Set.mem_setOf_eq]
    refine ⟨N + 1, 1, Nat.succ_pos N, Nat.one_pos, ?_, ?_⟩
    · rw [zero_mul, add_zero]
      push_cast
      linarith
    · rw [Nat.factorial_one, mul_one]
      exact dvd_mul_right _ _
  have hS : ∀ M : ℝ, ∃ R : ℕ, ∀ r : ℕ, R ≤ r → (erdos_51534_S r M).Infinite := by
    intro M
    obtain ⟨R, hR⟩ := erdos_51534_hyp_core M
    refine ⟨R, fun r hrR => ?_⟩
    apply Set.infinite_of_forall_exists_gt
    intro N
    obtain ⟨n, hn, a₁, a₂, h1, h2, h3, h4⟩ := hR r hrR (N + 1)
    refine ⟨n, ?_, by omega⟩
    simp only [erdos_51534_S, Set.mem_setOf_eq]
    exact ⟨a₁, a₂, h1, h2, h3, erdos_51534_hyp_reduction r n a₁ a₂ h4⟩
  obtain ⟨f, hf, hfr⟩ := erdos_51534_hyp_bookkeeping erdos_51534_S h0 hS
  exact ⟨f, hf, fun r hr => hfr r hr⟩