open Filter

-- CHECK: Real.log_nonneg Nat.one_le_cast Set.finite_lt_nat Filter.Tendsto.eventually Filter.eventually_ge_atTop
-- Derived core (the R1 equivalent form of the negation, with the R3 symmetry assumption a₂ ≤ a₁ built in).
-- It says there is one constant K such that, for every r ≥ 1 and every large n, every valid pair
-- satisfies a₁ + a₂ ≤ n + K log n.
-- It removes the quantifier over f. The glue below derives the target from it.
-- This is the genuinely open core; heuristics (Kummer carries) suggest it may be FALSE.
namespace erdos_56143_neg_hyp_uniform_bound_ns
open Filter

def erdos56143Smooth (B m : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ m → p ≤ B

def erdos56143LargePrimeOK (r n a₁ a₂ : ℕ) : Prop :=
  ∀ q : ℕ, q.Prime → Nat.nth Nat.Prime (r - 1) < q →
    padicValNat q a₁.factorial + padicValNat q a₂.factorial ≤ padicValNat q n.factorial

-- PUBLISHED: C. Størmer, 1897 ("Quelques théorèmes sur l'équation de Pell x²-Dy²=±1"); also D. H. Lehmer, 1964, "On a problem of Størmer", Illinois J. Math. 8, Theorem 1: for every finite set of primes there are only finitely many pairs of consecutive integers both composed of those primes.
theorem erdos_56143_neg_hyp_uniform_bound_hyp_stormer :
    ∀ B : ℕ, ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      ¬ (erdos56143Smooth B m ∧ erdos56143Smooth B (m + 1)) := by
  sorry

-- If a₁ ≥ n+2 then (n+1)(n+2) divides a₁!/n!. Also a₁!/n! divides P^n, since a₁! divides a₁!a₂!, which divides n!·P^n. Hence every prime factor of n+1 and of n+2 divides P, so it is at most p_r.
namespace erdos_56143_neg_hyp_uniform_bound_hyp_bridge_ns

open Filter

theorem erdos_56143_neg_hyp_uniform_bound_hyp_bridge :
    ∀ r n a₁ a₂ : ℕ, 1 ≤ r → n + 2 ≤ a₁ →
      a₁.factorial * a₂.factorial ∣
        n.factorial * (∏ i ∈ Finset.range r, Nat.nth Nat.Prime i) ^ n →
      erdos56143Smooth (Nat.nth Nat.Prime (r - 1)) (n + 1) ∧
        erdos56143Smooth (Nat.nth Nat.Prime (r - 1)) (n + 1 + 1) := by
  intro r n a₁ a₂ hr ha hdiv
  have h1 : (n + 1 + 1).factorial ∣
      n.factorial * (∏ i ∈ Finset.range r, Nat.nth Nat.Prime i) ^ n :=
    (Nat.factorial_dvd_factorial ha).trans ((dvd_mul_right _ _).trans hdiv)
  have e : (n + 1 + 1).factorial = n.factorial * ((n + 1) * (n + 1 + 1)) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]; ring
  rw [e] at h1
  have h2 : (n + 1) * (n + 1 + 1) ∣ (∏ i ∈ Finset.range r, Nat.nth Nat.Prime i) ^ n :=
    (mul_dvd_mul_iff_left (Nat.factorial_ne_zero n)).mp h1
  have key : ∀ p, p.Prime → p ∣ (∏ i ∈ Finset.range r, Nat.nth Nat.Prime i) ^ n →
      p ≤ Nat.nth Nat.Prime (r - 1) := by
    intro p hp hd
    have hd' := hp.dvd_of_dvd_pow hd
    obtain ⟨i, hi, hpi⟩ := (Prime.dvd_finset_prod_iff hp.prime _).mp hd'
    rw [Finset.mem_range] at hi
    have hpe := (Nat.prime_dvd_prime_iff_eq hp (Nat.prime_nth_prime i)).mp hpi
    rw [hpe]
    exact Nat.nth_monotone Nat.infinite_setOf_prime (by omega)
  unfold erdos56143Smooth
  constructor
  · intro p hp hd
    exact key p hp ((hd.trans (dvd_mul_right _ _)).trans h2)
  · intro p hp hd
    exact key p hp ((hd.trans (dvd_mul_left _ _)).trans h2)

end erdos_56143_neg_hyp_uniform_bound_hyp_bridge_ns

theorem erdos_56143_neg_hyp_uniform_bound_hyp_bridge :
    ∀ r n a₁ a₂ : ℕ, 1 ≤ r → n + 2 ≤ a₁ →
      a₁.factorial * a₂.factorial ∣
        n.factorial * (∏ i ∈ Finset.range r, Nat.nth Nat.Prime i) ^ n →
      erdos56143Smooth (Nat.nth Nat.Prime (r - 1)) (n + 1) ∧
        erdos56143Smooth (Nat.nth Nat.Prime (r - 1)) (n + 1 + 1) := by
  exact erdos_56143_neg_hyp_uniform_bound_hyp_bridge_ns.erdos_56143_neg_hyp_uniform_bound_hyp_bridge

-- A prime q > p_r is coprime to P = ∏ first r primes. So v_q(a₁!a₂!) ≤ v_q(n!·P^n) = v_q(n!).
namespace erdos_56143_neg_hyp_uniform_bound_hyp_large_prime_ns

open Filter

private lemma erdos56143_not_dvd_prod (r q : ℕ) (hq : q.Prime)
    (hlt : Nat.nth Nat.Prime (r - 1) < q) :
    ¬ q ∣ ∏ i ∈ Finset.range r, Nat.nth Nat.Prime i := by
  intro h1
  obtain ⟨i, hi, hqi⟩ := (Prime.dvd_finset_prod_iff hq.prime _).mp h1
  have heq : q = Nat.nth Nat.Prime i :=
    (Nat.prime_dvd_prime_iff_eq hq (Nat.prime_nth_prime i)).mp hqi
  have hi' : i ≤ r - 1 := by rw [Finset.mem_range] at hi; omega
  have hmono : Nat.nth Nat.Prime i ≤ Nat.nth Nat.Prime (r - 1) :=
    Nat.nth_monotone Nat.infinite_setOf_prime hi'
  omega

theorem erdos_56143_neg_hyp_uniform_bound_hyp_large_prime :
    ∀ r n a₁ a₂ : ℕ, 1 ≤ r →
      a₁.factorial * a₂.factorial ∣
        n.factorial * (∏ i ∈ Finset.range r, Nat.nth Nat.Prime i) ^ n →
      erdos56143LargePrimeOK r n a₁ a₂ := by
  intro r n a₁ a₂ hr hdvd q hq hlt
  haveI : Fact q.Prime := ⟨hq⟩
  have hPne : (∏ i ∈ Finset.range r, Nat.nth Nat.Prime i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => (Nat.prime_nth_prime i).ne_zero)
  have hndvd : ¬ q ∣ (∏ i ∈ Finset.range r, Nat.nth Nat.Prime i) ^ n := fun h =>
    erdos56143_not_dvd_prod r q hq hlt (hq.dvd_of_dvd_pow h)
  have hval := padicValNat.eq_zero_of_not_dvd hndvd
  have hB : n.factorial * (∏ i ∈ Finset.range r, Nat.nth Nat.Prime i) ^ n ≠ 0 :=
    mul_ne_zero (Nat.factorial_ne_zero _) (pow_ne_zero _ hPne)
  have h3 : padicValNat q (a₁.factorial * a₂.factorial) ≤
      padicValNat q (n.factorial * (∏ i ∈ Finset.range r, Nat.nth Nat.Prime i) ^ n) :=
    (padicValNat_dvd_iff_le hB).mp (dvd_trans pow_padicValNat_dvd hdvd)
  rw [padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _),
    padicValNat.mul (Nat.factorial_ne_zero _) (pow_ne_zero _ hPne), hval] at h3
  omega

end erdos_56143_neg_hyp_uniform_bound_hyp_large_prime_ns

theorem erdos_56143_neg_hyp_uniform_bound_hyp_large_prime :
    ∀ r n a₁ a₂ : ℕ, 1 ≤ r →
      a₁.factorial * a₂.factorial ∣
        n.factorial * (∏ i ∈ Finset.range r, Nat.nth Nat.Prime i) ^ n →
      erdos56143LargePrimeOK r n a₁ a₂ := by
  exact erdos_56143_neg_hyp_uniform_bound_hyp_large_prime_ns.erdos_56143_neg_hyp_uniform_bound_hyp_large_prime

-- Core (genuinely open): the large-prime valuation constraints alone, with a₁ ≤ n+1, force a gain of at most K·log n, with K uniform in r. By Kummer, the gain s satisfies v_q((n+1)…(n+s)) ≤ carries_q, for every prime q > p_r.
namespace erdos_56143_neg_hyp_uniform_bound_hyp_core_ns
open Filter

-- CHECK: Real.log_nonneg Nat.one_le_cast Set.finite_lt_nat Filter.Tendsto.eventually Filter.eventually_ge_atTop
-- CHECK: Real.tendsto_log_atTop tendsto_natCast_atTop_atTop Filter.eventually_atTop
open Filter

def erdos56143Smooth (B m : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ m → p ≤ B

def erdos56143LargePrimeOK (r n a₁ a₂ : ℕ) : Prop :=
  ∀ q : ℕ, q.Prime → Nat.nth Nat.Prime (r - 1) < q →
    padicValNat q a₁.factorial + padicValNat q a₂.factorial ≤ padicValNat q n.factorial

-- Derived (rigorous, Legendre): if n ≤ a₁ then v_q(a₁!) ≥ v_q(n!), so the large-prime condition
-- forces v_q(a₂!) = 0 for every prime q > p_r. If a₂ ≥ p_{r+1} = Nat.nth Nat.Prime r, take
-- q = p_{r+1} > p_r (strict monotonicity of nth prime, r ≥ 1); then q ∣ a₂!, a contradiction.
namespace erdos_56143_neg_hyp_uniform_bound_hyp_core_hyp_high_ns

open Filter

theorem erdos_56143_neg_hyp_uniform_bound_hyp_core_hyp_high :
    ∀ r n a₁ a₂ : ℕ, 1 ≤ r → n ≤ a₁ → a₁ ≤ n + 1 → 0 < a₂ →
      erdos56143LargePrimeOK r n a₁ a₂ → a₂ < Nat.nth Nat.Prime r := by
  intro r n a₁ a₂ hr hn _ _ hok
  by_contra hcon
  push_neg at hcon
  have hq : (Nat.nth Nat.Prime r).Prime := Nat.prime_nth_prime r
  have hlt : Nat.nth Nat.Prime (r - 1) < Nat.nth Nat.Prime r :=
    Nat.nth_strictMono Nat.infinite_setOf_prime (by omega)
  have h := hok _ hq hlt
  have h1 : padicValNat (Nat.nth Nat.Prime r) n.factorial ≤
      padicValNat (Nat.nth Nat.Prime r) a₁.factorial := by
    rw [← Nat.factorization_def _ hq, ← Nat.factorization_def _ hq]
    exact ((Nat.factorization_le_iff_dvd (Nat.factorial_ne_zero _)
      (Nat.factorial_ne_zero _)).mpr (Nat.factorial_dvd_factorial hn)) _
  have h2 : 1 ≤ padicValNat (Nat.nth Nat.Prime r) a₂.factorial := by
    rw [← Nat.factorization_def _ hq]
    exact (Nat.Prime.dvd_iff_one_le_factorization hq (Nat.factorial_ne_zero _)).mp
      ((Nat.Prime.dvd_factorial hq).mpr hcon)
  omega

end erdos_56143_neg_hyp_uniform_bound_hyp_core_hyp_high_ns

theorem erdos_56143_neg_hyp_uniform_bound_hyp_core_hyp_high :
    ∀ r n a₁ a₂ : ℕ, 1 ≤ r → n ≤ a₁ → a₁ ≤ n + 1 → 0 < a₂ →
      erdos56143LargePrimeOK r n a₁ a₂ → a₂ < Nat.nth Nat.Prime r := by
  exact erdos_56143_neg_hyp_uniform_bound_hyp_core_hyp_high_ns.erdos_56143_neg_hyp_uniform_bound_hyp_core_hyp_high

-- Hard core: the target restricted to the only non-degenerate regime a₂ ≤ a₁ < n < a₁ + a₂
-- (the cases a₁ ≥ n and a₁ + a₂ ≤ n are discharged by the glue). Any counterexample to the
-- target must live here.
theorem erdos_56143_neg_hyp_uniform_bound_hyp_core_hyp_core :
    ∃ K : ℕ, ∀ r : ℕ, 1 ≤ r → ∃ n₀ : ℕ, ∀ n a₁ a₂ : ℕ, n₀ ≤ n → a₂ ≤ a₁ →
      a₁ < n → n < a₁ + a₂ → erdos56143LargePrimeOK r n a₁ a₂ →
      (a₁ : ℝ) + a₂ ≤ n + (K : ℝ) * Real.log n := by
  sorry

theorem erdos_56143_neg_hyp_uniform_bound_hyp_core :
    ∃ K : ℕ, ∀ r : ℕ, 1 ≤ r → ∃ n₀ : ℕ, ∀ n a₁ a₂ : ℕ, n₀ ≤ n → a₂ ≤ a₁ →
      0 < a₂ → a₁ ≤ n + 1 → erdos56143LargePrimeOK r n a₁ a₂ →
      (a₁ : ℝ) + a₂ ≤ n + (K : ℝ) * Real.log n := by
  obtain ⟨K, hK⟩ := erdos_56143_neg_hyp_uniform_bound_hyp_core_hyp_core
  refine ⟨K + 1, ?_⟩
  intro r hr
  obtain ⟨n₀, hn₀⟩ := hK r hr
  have hev : ∀ᶠ m : ℕ in atTop,
      ((Nat.nth Nat.Prime r : ℕ) : ℝ) + 1 ≤ Real.log (m : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop _)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max n₀ (max N 1), ?_⟩
  intro n a₁ a₂ hn h21 ha2 ha1 hok
  have hn0 : n₀ ≤ n := le_trans (le_max_left _ _) hn
  have hnN : N ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn1 : 1 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr hn1)
  have hKl : (0 : ℝ) ≤ (K : ℝ) * Real.log (n : ℝ) := mul_nonneg (Nat.cast_nonneg K) hlog0
  have key : ((K + 1 : ℕ) : ℝ) * Real.log (n : ℝ)
      = (K : ℝ) * Real.log (n : ℝ) + Real.log (n : ℝ) := by
    push_cast
    ring
  by_cases hlow : a₁ + a₂ ≤ n
  · have h : ((a₁ + a₂ : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hlow
    push_cast at h
    linarith
  · by_cases hlt : a₁ < n
    · have h := hn₀ n a₁ a₂ hn0 h21 hlt (by omega) hok
      linarith
    · have hp := erdos_56143_neg_hyp_uniform_bound_hyp_core_hyp_high r n a₁ a₂ hr
        (by omega) ha1 ha2 hok
      have hlogN := hN n hnN
      have h1 : (a₁ : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast ha1
      have hp' : a₂ + 1 ≤ Nat.nth Nat.Prime r := hp
      have h2 : (a₂ : ℝ) + 1 ≤ ((Nat.nth Nat.Prime r : ℕ) : ℝ) := by exact_mod_cast hp'
      linarith
end erdos_56143_neg_hyp_uniform_bound_hyp_core_ns

theorem erdos_56143_neg_hyp_uniform_bound_hyp_core :
    ∃ K : ℕ, ∀ r : ℕ, 1 ≤ r → ∃ n₀ : ℕ, ∀ n a₁ a₂ : ℕ, n₀ ≤ n → a₂ ≤ a₁ →
      0 < a₂ → a₁ ≤ n + 1 → erdos56143LargePrimeOK r n a₁ a₂ →
      (a₁ : ℝ) + a₂ ≤ n + (K : ℝ) * Real.log n := by
  exact erdos_56143_neg_hyp_uniform_bound_hyp_core_ns.erdos_56143_neg_hyp_uniform_bound_hyp_core



theorem erdos_56143_neg_hyp_uniform_bound :
    ∃ K : ℕ, ∀ r : ℕ, 1 ≤ r → ∃ n₀ : ℕ, ∀ n a₁ a₂ : ℕ, n₀ ≤ n → a₂ ≤ a₁ →
      0 < a₁ → 0 < a₂ →
      a₁.factorial * a₂.factorial ∣
        n.factorial * (∏ i ∈ Finset.range r, Nat.nth Nat.Prime i) ^ n →
      (a₁ : ℝ) + a₂ ≤ n + (K : ℝ) * Real.log n := by
  obtain ⟨K, hK⟩ := erdos_56143_neg_hyp_uniform_bound_hyp_core
  refine ⟨K, fun r hr => ?_⟩
  obtain ⟨n₁, h1⟩ := hK r hr
  obtain ⟨N, hN⟩ := erdos_56143_neg_hyp_uniform_bound_hyp_stormer (Nat.nth Nat.Prime (r - 1))
  refine ⟨max n₁ N, fun n a₁ a₂ hn h21 _h1pos h2pos hdvd => ?_⟩
  have hn1 : n₁ ≤ n := (le_max_left n₁ N).trans hn
  have hnN : N ≤ n := (le_max_right n₁ N).trans hn
  have ha : a₁ ≤ n + 1 := by
    by_contra h
    push_neg at h
    obtain ⟨hs1, hs2⟩ :=
      erdos_56143_neg_hyp_uniform_bound_hyp_bridge r n a₁ a₂ hr (by omega) hdvd
    exact hN (n + 1) (by omega) ⟨hs1, hs2⟩
  exact h1 n a₁ a₂ hn1 h21 h2pos ha
    (erdos_56143_neg_hyp_uniform_bound_hyp_large_prime r n a₁ a₂ hr hdvd)
end erdos_56143_neg_hyp_uniform_bound_ns

theorem erdos_56143_neg_hyp_uniform_bound :
    ∃ K : ℕ, ∀ r : ℕ, 1 ≤ r → ∃ n₀ : ℕ, ∀ n a₁ a₂ : ℕ, n₀ ≤ n → a₂ ≤ a₁ →
      0 < a₁ → 0 < a₂ →
      a₁.factorial * a₂.factorial ∣
        n.factorial * (∏ i ∈ Finset.range r, Nat.nth Nat.Prime i) ^ n →
      (a₁ : ℝ) + a₂ ≤ n + (K : ℝ) * Real.log n := by
  exact erdos_56143_neg_hyp_uniform_bound_ns.erdos_56143_neg_hyp_uniform_bound



theorem erdos_56143_neg :
    ¬ (∃ f : ℕ → ℝ, Tendsto f atTop atTop ∧
      ∀ (r : ℕ) (hr : 1 ≤ r),
        {n : ℕ | ∃ a₁ a₂ : ℕ, 0 < a₁ ∧ 0 < a₂ ∧
          (a₁ : ℝ) + a₂ > n + f r * Real.log n ∧
          a₁.factorial * a₂.factorial ∣
            n.factorial * (∏ i ∈ Finset.range r, Nat.nth Nat.Prime i) ^ n}.Infinite) := by
  rintro ⟨f, hf, hinf⟩
  obtain ⟨K, hK⟩ := erdos_56143_neg_hyp_uniform_bound
  have hev : ∀ᶠ r in atTop, (K : ℝ) ≤ f r := hf.eventually (eventually_ge_atTop (K : ℝ))
  obtain ⟨r, hr⟩ := (hev.and (eventually_ge_atTop 1)).exists
  obtain ⟨n₀, hn₀⟩ := hK r hr.2
  apply (hinf r hr.2)
  apply (Set.finite_lt_nat n₀).subset
  intro n hn
  obtain ⟨a₁, a₂, h1, h2, hsum, hdvd⟩ := hn
  simp only [Set.mem_setOf_eq]
  by_contra hlt
  push_neg at hlt
  have hlog : 0 ≤ Real.log (n : ℝ) := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · exact Real.log_nonneg (Nat.one_le_cast.mpr h)
  have hb : (a₁ : ℝ) + a₂ ≤ n + (K : ℝ) * Real.log n := by
    rcases le_total a₂ a₁ with h | h
    · exact hn₀ n a₁ a₂ hlt h h1 h2 hdvd
    · have hd' : a₂.factorial * a₁.factorial ∣
          n.factorial * (∏ i ∈ Finset.range r, Nat.nth Nat.Prime i) ^ n := by
        rw [Nat.mul_comm a₂.factorial a₁.factorial]
        exact hdvd
      have := hn₀ n a₂ a₁ hlt h h2 h1 hd'
      linarith
  have hm : (K : ℝ) * Real.log n ≤ f r * Real.log n :=
    mul_le_mul_of_nonneg_right hr.1 hlog
  linarith