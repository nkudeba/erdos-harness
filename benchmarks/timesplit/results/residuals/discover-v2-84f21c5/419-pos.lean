-- CHECK: Finset.prod_filter_mul_prod_filter_not mapClusterPt_iff_frequently Nat.exists_infinite_primes exists_nat_one_div_lt
open Filter
open scoped ArithmeticFunction.sigma

noncomputable def factorialDivisorRatio (n : ℕ) : ℝ :=
  (σ 0 (n + 1).factorial : ℝ) / (σ 0 n.factorial : ℝ)

def limitPointSet : Set ℝ :=
  {1} ∪ {x | ∃ k : ℕ, 1 ≤ k ∧ x = 1 + 1 / (k : ℝ)}

noncomputable def primeFactorTerm (n p : ℕ) : ℝ :=
  1 + ((n + 1).factorization p : ℝ) / ((n.factorial.factorization p : ℝ) + 1)

noncomputable def ratioProd (n : ℕ) : ℝ :=
  ∏ p ∈ (n + 1).primeFactors, primeFactorTerm n p

noncomputable def smallProd (n : ℕ) : ℝ :=
  ∏ p ∈ (n + 1).primeFactors.filter (fun p => p * p ≤ n + 1), primeFactorTerm n p

noncomputable def largeProd (n : ℕ) : ℝ :=
  ∏ p ∈ (n + 1).primeFactors.filter (fun p => ¬ (p * p ≤ n + 1)), primeFactorTerm n p

noncomputable def errBound (n : ℕ) : ℝ :=
  2 * (Real.exp (Real.logb 2 ((n : ℝ) + 1) / (Real.sqrt ((n : ℝ) + 1) - 1)) - 1)

namespace erdos_70386_hyp_err_tendsto_ns
open Filter

open scoped ArithmeticFunction.sigma

private lemma sqrt_tendsto_aux :
    Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ) + 1)) atTop atTop := by
  refine Filter.tendsto_atTop_atTop.2 fun b => ⟨⌈b ^ 2⌉₊, fun n hn => ?_⟩
  have hb : b ^ 2 ≤ (n : ℝ) := Nat.ceil_le.mp hn
  have : |b| ≤ Real.sqrt ((n : ℝ) + 1) := Real.abs_le_sqrt (by linarith)
  exact le_trans (le_abs_self b) this

private lemma ratio_tendsto_aux :
    Tendsto (fun n : ℕ => Real.logb 2 ((n : ℝ) + 1) /
      (Real.sqrt ((n : ℝ) + 1) - 1)) atTop (nhds 0) := by
  have h1 : Tendsto (fun t : ℝ => Real.log t ^ 1 / (1 * t + (-1))) atTop (nhds 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero
  have h3 := (h1.comp sqrt_tendsto_aux).const_mul (2 / Real.log 2)
  rw [mul_zero] at h3
  refine h3.congr (fun n => ?_)
  have hx : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  simp only [Function.comp_apply, pow_one, one_mul]
  rw [Real.log_sqrt hx]
  unfold Real.logb
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
    div_eq_mul_inv, sub_eq_add_neg]
  ring

theorem erdos_70386_hyp_err_tendsto :
    Tendsto errBound atTop (nhds 0) := by
  have hc : Continuous (fun y : ℝ => 2 * (Real.exp y - 1)) := by fun_prop
  have h := (hc.tendsto 0).comp ratio_tendsto_aux
  simp only [Real.exp_zero, sub_self, mul_zero] at h
  refine h.congr (fun n => ?_)
  simp only [Function.comp_apply, errBound]
end erdos_70386_hyp_err_tendsto_ns

namespace erdos_70386_hyp_closed_ns
open Filter

open scoped ArithmeticFunction.sigma

theorem erdos_70386_hyp_closed : IsClosed limitPointSet := by
  set u : ℕ → ℝ := fun k => 1 + 1 / ((k:ℝ) + 1) with hu
  have hT : Tendsto u atTop (nhds 1) := by
    have h := (tendsto_const_nhds (x := (1:ℝ))).add tendsto_one_div_add_atTop_nhds_zero_nat
    rw [add_zero] at h
    exact h
  have h1 : limitPointSet ⊆ insert (1:ℝ) (Set.range u) := by
    rintro x (hx | ⟨k, hk, rfl⟩)
    · rw [Set.mem_singleton_iff] at hx
      exact Or.inl hx
    · refine Or.inr ⟨k - 1, ?_⟩
      have hc : ((k - 1 : ℕ) : ℝ) + 1 = k := by
        rw [Nat.cast_sub hk]; simp
      simp only [hu, hc]
  have h2 : insert (1:ℝ) (Set.range u) ⊆ limitPointSet := by
    rintro x (hx | ⟨k, rfl⟩)
    · exact Or.inl hx
    · refine Or.inr ⟨k + 1, by omega, ?_⟩
      simp only [hu]
      push_cast
      ring
  have hEq : limitPointSet = insert (1:ℝ) (Set.range u) := Set.Subset.antisymm h1 h2
  rw [hEq]
  exact IsCompact.isClosed (Filter.Tendsto.isCompact_insert_range hT)
end erdos_70386_hyp_closed_ns

-- R1: τ(N) = ∏ (v_p(N)+1), v_p((n+1)!) = v_p(n!) + v_p(n+1); primes not dividing n+1 cancel.
namespace erdos_70386_hyp_ratio_eq_ns
-- CHECK: Finset.prod_filter_mul_prod_filter_not mapClusterPt_iff_frequently Nat.exists_infinite_primes exists_nat_one_div_lt
open Filter

open scoped ArithmeticFunction.sigma

theorem erdos_70386_hyp_ratio_eq :
    ∀ n : ℕ, factorialDivisorRatio n = ratioProd n := by
  intro n
  have hf : (n + 1).factorial = (n + 1) * n.factorial := Nat.factorial_succ n
  have hfac : (n + 1).factorial.factorization = (n + 1).factorization + n.factorial.factorization := by
    rw [hf, Nat.factorization_mul (Nat.succ_ne_zero n) (Nat.factorial_ne_zero n)]
  set S := (n + 1).factorial.primeFactors with hS
  have hsub1 : n.factorial.primeFactors ⊆ S :=
    Nat.primeFactors_mono (Nat.factorial_dvd_factorial (Nat.le_succ n)) (Nat.factorial_ne_zero _)
  have hsub2 : (n + 1).primeFactors ⊆ S :=
    Nat.primeFactors_mono (Dvd.intro _ hf.symm) (Nat.factorial_ne_zero _)
  have hA : (σ 0 (n + 1).factorial : ℝ) = ∏ p ∈ S, (((n + 1).factorial.factorization p : ℝ) + 1) := by
    rw [ArithmeticFunction.sigma_zero_apply, Nat.card_divisors (Nat.factorial_ne_zero _)]
    push_cast; rfl
  have hB : (σ 0 n.factorial : ℝ) = ∏ p ∈ S, ((n.factorial.factorization p : ℝ) + 1) := by
    rw [ArithmeticFunction.sigma_zero_apply, Nat.card_divisors (Nat.factorial_ne_zero _)]
    push_cast
    apply Finset.prod_subset hsub1
    intro p _ hp
    rw [Nat.factorization_eq_zero_of_not_dvd]
    · simp
    · intro hd
      exact hp (Nat.mem_primeFactors.2 ⟨Nat.prime_of_mem_primeFactors (by assumption), hd,
        Nat.factorial_ne_zero _⟩)
  have hC : ratioProd n = ∏ p ∈ S, primeFactorTerm n p := by
    unfold ratioProd
    apply Finset.prod_subset hsub2
    intro p hpS hp
    unfold primeFactorTerm
    rw [Nat.factorization_eq_zero_of_not_dvd]
    · simp
    · intro hd
      exact hp (Nat.mem_primeFactors.2 ⟨Nat.prime_of_mem_primeFactors hpS, hd, Nat.succ_ne_zero n⟩)
  have hBpos : (0 : ℝ) < ∏ p ∈ S, ((n.factorial.factorization p : ℝ) + 1) :=
    Finset.prod_pos (fun p _ => by positivity)
  unfold factorialDivisorRatio
  rw [hA, hB, hC, div_eq_iff hBpos.ne', ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _
  unfold primeFactorTerm
  rw [hfac, Finsupp.add_apply]
  have : ((n.factorial.factorization p : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring
end erdos_70386_hyp_ratio_eq_ns

theorem erdos_70386_hyp_ratio_eq :
    ∀ n : ℕ, factorialDivisorRatio n = ratioProd n := by
  exact erdos_70386_hyp_ratio_eq_ns.erdos_70386_hyp_ratio_eq



-- R3 small part: for p*p ≤ m, v_p((m-1)!)+1 > √m - 1/√m ≥ √m - 1, Σ a_p ≤ log₂ m, and 1+t ≤ e^t.
namespace erdos_70386_hyp_small_bound_ns
-- CHECK: Nat.log_le_self Real.le_logb_iff_rpow_le Real.exp_sum Finset.prod_pow_eq_pow_sum div_le_div_of_nonneg_left div_le_div_of_nonneg_right Nat.factorization_prod_pow_eq_self
open Filter

open scoped ArithmeticFunction.sigma

private lemma small_factor_bound (n p : ℕ) (hn : 1 ≤ n) (hp : p.Prime) (hpp : p * p ≤ n + 1) :
    Real.sqrt ((n:ℝ) + 1) ≤ (n.factorial.factorization p : ℝ) + 1 := by
  have hv : n / p ≤ n.factorial.factorization p := by
    rw [Nat.factorization_factorial hp (Nat.lt_succ_of_le (Nat.log_le_self p n))]
    have h1 : (1:ℕ) ∈ Finset.Ico 1 (n + 1) := by
      simp only [Finset.mem_Ico]; omega
    have := Finset.single_le_sum (f := fun i => n / p ^ i) (fun i _ => Nat.zero_le _) h1
    simpa using this
  have hlt : n + 1 ≤ p * (n / p + 1) := by
    have h1 := Nat.div_add_mod n p
    have h2 := Nat.mod_lt n hp.pos
    have h3 : p * (n / p + 1) = p * (n / p) + p := by ring
    rw [h3]
    generalize p * (n / p) = t at h1 ⊢
    generalize n % p = r at h1 h2
    omega
  have hs0 : 0 ≤ Real.sqrt ((n:ℝ) + 1) := Real.sqrt_nonneg _
  have hss : Real.sqrt ((n:ℝ) + 1) * Real.sqrt ((n:ℝ) + 1) = (n:ℝ) + 1 :=
    Real.mul_self_sqrt (by positivity)
  have hps : (p:ℝ) ≤ Real.sqrt ((n:ℝ) + 1) := by
    have h := Real.sqrt_le_sqrt (show ((p:ℝ) * p) ≤ (n:ℝ) + 1 by exact_mod_cast hpp)
    rwa [Real.sqrt_mul_self (Nat.cast_nonneg p)] at h
  have hlt' : (n:ℝ) + 1 ≤ (p:ℝ) * (((n / p : ℕ) : ℝ) + 1) := by exact_mod_cast hlt
  have hv' : ((n / p : ℕ) : ℝ) ≤ (n.factorial.factorization p : ℝ) := by exact_mod_cast hv
  have hspos : 0 < Real.sqrt ((n:ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have hq0 : (0:ℝ) ≤ ((n / p : ℕ) : ℝ) + 1 := by positivity
  have hA := mul_le_mul_of_nonneg_right hps hq0
  nlinarith [mul_le_mul_of_nonneg_left hv' hs0]

theorem erdos_70386_hyp_small_bound :
    ∀ n : ℕ, 1 ≤ n → 1 ≤ smallProd n ∧
      smallProd n ≤ Real.exp (Real.logb 2 ((n : ℝ) + 1) / (Real.sqrt ((n : ℝ) + 1) - 1)) := by
  intro n hn
  unfold smallProd
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt ((n:ℝ) + 1) := ⟨_, rfl⟩
  rw [← hs]
  set S := (n + 1).primeFactors.filter (fun p => p * p ≤ n + 1) with hS
  have hs1 : 1 < s := by
    have hss : s * s = (n:ℝ) + 1 := by rw [hs]; exact Real.mul_self_sqrt (by positivity)
    have h1 : (1:ℝ) ≤ n := by exact_mod_cast hn
    have h0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg _
    nlinarith
  have hmem : ∀ p ∈ S, p.Prime ∧ p * p ≤ n + 1 := by
    intro p hp
    rw [hS, Finset.mem_filter, Nat.mem_primeFactors] at hp
    exact ⟨hp.1.1, hp.2⟩
  have hterm : ∀ p ∈ S, 1 ≤ primeFactorTerm n p ∧
      primeFactorTerm n p ≤ Real.exp (((n + 1).factorization p : ℝ) / (s - 1)) := by
    intro p hp
    obtain ⟨hpr, hpp⟩ := hmem p hp
    have hb := small_factor_bound n p hn hpr hpp
    rw [← hs] at hb
    have ha : (0:ℝ) ≤ ((n + 1).factorization p : ℝ) := Nat.cast_nonneg _
    have hd : (0:ℝ) < (n.factorial.factorization p : ℝ) + 1 := by positivity
    unfold primeFactorTerm
    constructor
    · have : 0 ≤ ((n + 1).factorization p : ℝ) / ((n.factorial.factorization p : ℝ) + 1) :=
        div_nonneg ha hd.le
      linarith
    · calc 1 + ((n + 1).factorization p : ℝ) / ((n.factorial.factorization p : ℝ) + 1)
          ≤ Real.exp (((n + 1).factorization p : ℝ) / ((n.factorial.factorization p : ℝ) + 1)) := by
            linarith [Real.add_one_le_exp
              (((n + 1).factorization p : ℝ) / ((n.factorial.factorization p : ℝ) + 1))]
        _ ≤ Real.exp (((n + 1).factorization p : ℝ) / (s - 1)) := by
            apply Real.exp_le_exp.mpr
            exact div_le_div_of_nonneg_left ha (by linarith) (by linarith)
  have hnat : 2 ^ (∑ p ∈ S, (n + 1).factorization p) ≤ n + 1 := by
    have hm : n + 1 ≠ 0 := by omega
    have hfull := Nat.factorization_prod_pow_eq_self hm
    simp only [Finsupp.prod, Nat.support_factorization] at hfull
    rw [← Finset.prod_pow_eq_pow_sum]
    calc ∏ p ∈ S, 2 ^ ((n + 1).factorization p)
        ≤ ∏ p ∈ S, p ^ ((n + 1).factorization p) := by
          apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
          intro p hp
          exact Nat.pow_le_pow_left (hmem p hp).1.two_le _
      _ ≤ ∏ p ∈ (n + 1).primeFactors, p ^ ((n + 1).factorization p) := by
          apply Nat.le_of_dvd
          · rw [hfull]; omega
          · exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
      _ = n + 1 := hfull
  have hsum : (∑ p ∈ S, ((n + 1).factorization p : ℝ)) ≤ Real.logb 2 ((n:ℝ) + 1) := by
    have hnatR : (2:ℝ) ^ (((∑ p ∈ S, (n + 1).factorization p : ℕ)) : ℝ) ≤ (n:ℝ) + 1 := by
      rw [Real.rpow_natCast]; exact_mod_cast hnat
    have := (Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ) < 2)
      (by positivity : (0:ℝ) < (n:ℝ) + 1)).mpr hnatR
    rw [Nat.cast_sum] at this
    exact this
  constructor
  · calc (1:ℝ) = ∏ p ∈ S, (1:ℝ) := by rw [Finset.prod_const_one]
      _ ≤ ∏ p ∈ S, primeFactorTerm n p :=
          Finset.prod_le_prod (fun _ _ => zero_le_one) (fun p hp => (hterm p hp).1)
  · calc ∏ p ∈ S, primeFactorTerm n p
        ≤ ∏ p ∈ S, Real.exp (((n + 1).factorization p : ℝ) / (s - 1)) :=
          Finset.prod_le_prod (fun p hp => le_trans zero_le_one (hterm p hp).1)
            (fun p hp => (hterm p hp).2)
      _ = Real.exp (∑ p ∈ S, ((n + 1).factorization p : ℝ) / (s - 1)) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp (Real.logb 2 ((n:ℝ) + 1) / (s - 1)) := by
          apply Real.exp_le_exp.mpr
          rw [← Finset.sum_div]
          exact div_le_div_of_nonneg_right hsum (by linarith)
end erdos_70386_hyp_small_bound_ns

theorem erdos_70386_hyp_small_bound :
    ∀ n : ℕ, 1 ≤ n → 1 ≤ smallProd n ∧
      smallProd n ≤ Real.exp (Real.logb 2 ((n : ℝ) + 1) / (Real.sqrt ((n : ℝ) + 1) - 1)) := by
  exact erdos_70386_hyp_small_bound_ns.erdos_70386_hyp_small_bound



-- R2: at most one prime p | m with p*p > m; if m = k p then k < p, a = 1, v_p((m-1)!) = k-1,
-- so largeProd is 1 (empty) or exactly 1 + 1/k.
namespace erdos_70386_hyp_large_mem_ns
open Filter

open scoped ArithmeticFunction.sigma

private lemma large_term (n p : ℕ) (hn : 1 ≤ n) (hp : p.Prime) (hd : p ∣ n + 1)
    (hpp : ¬ p * p ≤ n + 1) : ∃ k : ℕ, 1 ≤ k ∧ primeFactorTerm n p = 1 + 1 / (k : ℝ) := by
  obtain ⟨k, hk⟩ := hd
  cases k with
  | zero => simp at hk
  | succ j =>
    refine ⟨j + 1, by omega, ?_⟩
    have hp2 := hp.two_le
    have hne : n + 1 ≠ 0 := by omega
    have hlt : n + 1 < p * p := not_le.mp hpp
    have h1 : 1 ≤ (n + 1).factorization p :=
      (hp.pow_dvd_iff_le_factorization hne).mp (by rw [pow_one]; exact ⟨j + 1, hk⟩)
    have h2 : ¬ 2 ≤ (n + 1).factorization p := by
      intro h
      have h3 := (hp.pow_dvd_iff_le_factorization hne).mpr h
      have h4 := Nat.le_of_dvd (by omega) h3
      rw [pow_two] at h4
      exact hpp h4
    have hf : (n + 1).factorization p = 1 := by omega
    have hnj : n = (p - 1) + j * p := by
      have h5 : n + 1 = p * j + p := by rw [hk]; ring
      rw [mul_comm j p]
      generalize p * j = t at *
      omega
    have hdiv : n / p = j := by
      rw [hnj, Nat.add_mul_div_right _ _ (by omega : 0 < p),
        Nat.div_eq_of_lt (by omega : p - 1 < p), zero_add]
    have hlog : Nat.log p n < 2 :=
      Nat.log_lt_of_lt_pow (by omega) (by rw [pow_two]; exact lt_trans (Nat.lt_succ_self n) hlt)
    have hv : n.factorial.factorization p = j := by
      rw [Nat.factorization_factorial hp hlog]
      have hI : Finset.Ico 1 2 = {1} := by decide
      rw [hI, Finset.sum_singleton, pow_one, hdiv]
    unfold primeFactorTerm
    rw [hf, hv]
    first
      | (push_cast; ring)
      | push_cast
      | simp

theorem erdos_70386_hyp_large_mem :
    ∀ n : ℕ, 1 ≤ n → 1 ≤ largeProd n ∧ largeProd n ≤ 2 ∧ largeProd n ∈ limitPointSet := by
  intro n hn
  set s := (n + 1).primeFactors.filter (fun p => ¬ (p * p ≤ n + 1)) with hs
  have hlp : largeProd n = ∏ p ∈ s, primeFactorTerm n p := rfl
  have hmem : ∀ p ∈ s, p.Prime ∧ p ∣ n + 1 ∧ ¬ p * p ≤ n + 1 := by
    intro p hp
    rw [hs, Finset.mem_filter, Nat.mem_primeFactors] at hp
    exact ⟨hp.1.1, hp.1.2.1, hp.2⟩
  rcases s.eq_empty_or_nonempty with h | ⟨p, hp⟩
  · rw [hlp, h, Finset.prod_empty]
    refine ⟨le_refl _, by norm_num, ?_⟩
    unfold limitPointSet
    exact Or.inl rfl
  · have hsing : s = {p} := by
      rw [Finset.eq_singleton_iff_unique_mem]
      refine ⟨hp, fun q hq => ?_⟩
      obtain ⟨hpP, hpd, hpl⟩ := hmem p hp
      obtain ⟨hqP, hqd, hql⟩ := hmem q hq
      by_contra hne
      have hcop : Nat.Coprime q p := (Nat.coprime_primes hqP hpP).mpr hne
      have hdvd : q * p ∣ n + 1 := hcop.mul_dvd_of_dvd_of_dvd hqd hpd
      have hle := Nat.le_of_dvd (by omega) hdvd
      have hpl' : n + 1 < p * p := not_le.mp hpl
      have hql' : n + 1 < q * q := not_le.mp hql
      have h1 : (n + 1) * (n + 1) < (p * p) * (q * q) :=
        mul_lt_mul'' hpl' hql' (Nat.zero_le _) (Nat.zero_le _)
      have e : (q * p) * (q * p) = (p * p) * (q * q) := by ring
      have h2 : (p * p) * (q * q) ≤ (n + 1) * (n + 1) := by
        rw [← e]; exact Nat.mul_le_mul hle hle
      exact absurd (lt_of_lt_of_le h1 h2) (lt_irrefl _)
    obtain ⟨hpP, hpd, hpl⟩ := hmem p hp
    obtain ⟨k, hk1, hk⟩ := large_term n p hn hpP hpd hpl
    rw [hlp, hsing, Finset.prod_singleton, hk]
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    refine ⟨?_, ?_, ?_⟩
    · have : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
      linarith
    · have : 1 / (k : ℝ) ≤ 1 := by
        rw [div_le_one (by linarith)]; exact hk'
      linarith
    · unfold limitPointSet
      exact Or.inr ⟨k, hk1, rfl⟩
end erdos_70386_hyp_large_mem_ns

theorem erdos_70386_hyp_large_mem :
    ∀ n : ℕ, 1 ≤ n → 1 ≤ largeProd n ∧ largeProd n ≤ 2 ∧ largeProd n ∈ limitPointSet := by
  exact erdos_70386_hyp_large_mem_ns.erdos_70386_hyp_large_mem



-- R2 specialised: m = k p with k < p; p is the unique large prime (p*p > kp), and every
-- q | k has q*q ≤ k*k < kp, so largeProd = 1 + 1/((k-1)+1).
theorem erdos_70386_hyp_large_witness :
    ∀ k p : ℕ, p.Prime → 1 ≤ k → k < p → largeProd (k * p - 1) = 1 + 1 / (k : ℝ) := by
  sorry

theorem erdos_70386_hyp_err_tendsto :
    Tendsto errBound atTop (nhds 0) := by
  exact erdos_70386_hyp_err_tendsto_ns.erdos_70386_hyp_err_tendsto

theorem erdos_70386_hyp_closed : IsClosed limitPointSet := by
  exact erdos_70386_hyp_closed_ns.erdos_70386_hyp_closed

theorem erdos_70386 :
    {x : ℝ | MapClusterPt x atTop factorialDivisorRatio} = limitPointSet := by
  have hr : factorialDivisorRatio = ratioProd := funext erdos_70386_hyp_ratio_eq
  have hS := erdos_70386_hyp_closed
  have hT := erdos_70386_hyp_err_tendsto
  have hsplit : ∀ n : ℕ, ratioProd n = largeProd n * smallProd n := by
    intro n
    unfold ratioProd largeProd smallProd
    rw [mul_comm, Finset.prod_filter_mul_prod_filter_not]
  have hclose : ∀ n : ℕ, 1 ≤ n → |ratioProd n - largeProd n| ≤ errBound n := by
    intro n hn
    obtain ⟨hs1, hs2, -⟩ := erdos_70386_hyp_large_mem n hn
    obtain ⟨hE1, hE2⟩ := erdos_70386_hyp_small_bound n hn
    have hb : errBound n =
        2 * (Real.exp (Real.logb 2 ((n : ℝ) + 1) / (Real.sqrt ((n : ℝ) + 1) - 1)) - 1) := rfl
    rw [hsplit n, hb, abs_le]
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.2 hs1) (sub_nonneg.2 hE1),
        mul_nonneg (sub_nonneg.2 hs2) (sub_nonneg.2 hE1)]
    · nlinarith [mul_nonneg (sub_nonneg.2 hs1) (sub_nonneg.2 hE1),
        mul_nonneg (sub_nonneg.2 hs2) (sub_nonneg.2 hE1)]
  have happrox : ∀ n : ℕ, 1 ≤ n → ∃ s ∈ limitPointSet, |ratioProd n - s| ≤ errBound n := by
    intro n hn
    obtain ⟨-, -, hsS⟩ := erdos_70386_hyp_large_mem n hn
    exact ⟨largeProd n, hsS, hclose n hn⟩
  have hwitb : ∀ k p : ℕ, p.Prime → 1 ≤ k → k < p →
      |ratioProd (k * p - 1) - (1 + 1 / (k : ℝ))| ≤ errBound (k * p - 1) := by
    intro k p hp hk hkp
    have h2 := hp.two_le
    have hkp2 : 2 ≤ k * p := by nlinarith
    have hn : 1 ≤ k * p - 1 := by omega
    rw [← erdos_70386_hyp_large_witness k p hp hk hkp]
    exact hclose _ hn
  have hev : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ n ≥ N0, errBound n < ε := by
    intro ε hε
    exact Filter.eventually_atTop.mp (hT.eventually (gt_mem_nhds hε))
  have hwit : ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
      ∃ n ≥ N, |ratioProd n - (1 + 1 / (k : ℝ))| < ε := by
    intro k hk ε hε N
    obtain ⟨N0, hN0⟩ := hev ε hε
    obtain ⟨p, hp1, hp⟩ := Nat.exists_infinite_primes (N0 + N + k + 2)
    have hkp : p ≤ k * p := by nlinarith
    refine ⟨k * p - 1, by omega, ?_⟩
    have h1 := hwitb k p hp hk (by omega)
    have h2 := hN0 (k * p - 1) (by omega)
    linarith
  rw [hr]
  ext x
  show MapClusterPt x atTop ratioProd ↔ x ∈ limitPointSet
  constructor
  · intro hx
    rw [mapClusterPt_iff_frequently] at hx
    by_contra hxS
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hS.isOpen_compl x hxS
    obtain ⟨N0, hN0⟩ := hev (ε / 2) (half_pos hε)
    have hfr := hx (Metric.ball x (ε / 2)) (Metric.ball_mem_nhds x (half_pos hε))
    rw [Filter.frequently_atTop] at hfr
    obtain ⟨n, hn, hnb⟩ := hfr (N0 + 1)
    obtain ⟨y, hyS, hy⟩ := happrox n (by omega)
    have hb := hN0 n (by omega)
    rw [Metric.mem_ball, Real.dist_eq] at hnb
    have hyb : y ∈ Metric.ball x ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      have h1 := abs_lt.mp hnb
      have h2 := abs_le.mp hy
      rw [abs_lt]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    exact hball hyb hyS
  · intro hx
    rw [mapClusterPt_iff_frequently]
    intro s hs
    rw [Filter.frequently_atTop]
    intro N
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hs
    simp only [limitPointSet, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq] at hx
    rcases hx with rfl | ⟨k, hk, rfl⟩
    · obtain ⟨j, hj⟩ := exists_nat_one_div_lt (half_pos hε)
      obtain ⟨m, hm, hm2⟩ := hwit (j + 1) (by omega) (ε / 2) (half_pos hε) N
      push_cast at hm2
      have hpos : (0:ℝ) < 1 / ((j:ℝ) + 1) := by positivity
      refine ⟨m, hm, hsub ?_⟩
      rw [Metric.mem_ball, Real.dist_eq]
      have h1 := abs_lt.mp hm2
      rw [abs_lt]
      constructor <;> linarith [h1.1, h1.2]
    · obtain ⟨m, hm, hm2⟩ := hwit k hk ε hε N
      refine ⟨m, hm, hsub ?_⟩
      rw [Metric.mem_ball, Real.dist_eq]
      exact hm2