import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic

set_option maxHeartbeats 1000000
set_option autoImplicit false

-- CHECK: mapClusterPt_iff_frequently isClosed_setOf_clusterPt tendsto_one_div_add_atTop_nhds_zero_nat Filter.not_frequently Filter.frequently_atTop Metric.mem_nhds_iff
-- CHECK: tendsto_natCast_atTop_atTop Filter.Tendsto.div_const Filter.Tendsto.const_mul Filter.Tendsto.sub_const gt_mem_nhds Real.isLittleO_log_rpow_atTop
open Filter
open scoped ArithmeticFunction.sigma

noncomputable def factorialDivisorRatio (n : ℕ) : ℝ :=
  (σ 0 (n + 1).factorial : ℝ) / (σ 0 n.factorial : ℝ)

def limitPointSet : Set ℝ :=
  {1} ∪ {x | ∃ k : ℕ, 1 ≤ k ∧ x = 1 + 1 / (k : ℝ)}

noncomputable def primeFactorRatio (n p : ℕ) : ℝ :=
  ((n.factorial.factorization p : ℝ) + ((n + 1).factorization p : ℝ) + 1) /
    ((n.factorial.factorization p : ℝ) + 1)

noncomputable def mainTerm (n : ℕ) : ℝ :=
  ∏ p ∈ (n + 1).primeFactors.filter (fun p => n + 1 < p ^ 2), (1 + (p : ℝ) / ((n + 1 : ℕ) : ℝ))

noncomputable def errDelta (m : ℕ) : ℝ :=
  Real.log (m : ℝ) / Real.log 2 / Real.sqrt (m : ℝ)

def S3Prop : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    factorialDivisorRatio n = (∏ p ∈ (n + 1).primeFactors, primeFactorRatio n p) ∧
    ∀ p ∈ (n + 1).primeFactors, 1 ≤ primeFactorRatio n p

def S4Prop : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (∀ q : ℕ, q.Prime → q ∣ n + 1 → n + 1 < q ^ 2 →
      (n + 1).factorization q = 1 ∧ n.factorial.factorization q + 1 = (n + 1) / q ∧
      primeFactorRatio n q = 1 + (q : ℝ) / ((n + 1 : ℕ) : ℝ) ∧ q ≤ n + 1) ∧
    (∀ q q' : ℕ, q.Prime → q'.Prime → q ∣ n + 1 → q' ∣ n + 1 →
      n + 1 < q ^ 2 → n + 1 < q' ^ 2 → q = q')

def S5Prop : Prop :=
  ∀ n p : ℕ, 1 ≤ n → p.Prime → p ∣ n + 1 → p ^ 2 ≤ n + 1 →
    1 ≤ primeFactorRatio n p ∧
    primeFactorRatio n p ≤ Real.exp (((n + 1).factorization p : ℝ) / Real.sqrt ((n + 1 : ℕ) : ℝ))

def S6Prop : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    ((∑ p ∈ m.primeFactors, m.factorization p : ℕ) : ℝ) ≤ Real.log (m : ℝ) / Real.log 2

def S7Prop : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    1 ≤ mainTerm n ∧ mainTerm n ≤ 2 ∧ mainTerm n ≤ factorialDivisorRatio n ∧
    factorialDivisorRatio n ≤ mainTerm n * Real.exp (errDelta (n + 1)) ∧
    factorialDivisorRatio n - mainTerm n ≤ 2 * (Real.exp (errDelta (n + 1)) - 1)

namespace erdos_37099_hyp_product_ns
-- CHECK: ArithmeticFunction.sigma_zero_apply Nat.card_divisors Nat.factorization_eq_zero_iff Nat.primeFactors_mono Nat.factorization_mul Finset.prod_div_distrib
open Filter

open scoped ArithmeticFunction.sigma

private lemma fact_zero_of_not_mem (m p : ℕ) (hp : p ∉ m.primeFactors) :
    m.factorization p = 0 := by
  rw [Nat.factorization_eq_zero_iff]
  rw [Nat.mem_primeFactors] at hp
  tauto

private lemma tau_eq_prod (m : ℕ) (hm : m ≠ 0) (S : Finset ℕ) (hS : m.primeFactors ⊆ S) :
    (σ 0 m : ℝ) = ∏ p ∈ S, ((m.factorization p : ℝ) + 1) := by
  rw [ArithmeticFunction.sigma_zero_apply, Nat.card_divisors hm]
  push_cast
  apply Finset.prod_subset hS
  intro p _ hp
  rw [fact_zero_of_not_mem m p hp]
  simp

theorem erdos_37099_hyp_product : S3Prop := by
  intro n hn
  have h1 : (n + 1) ≠ 0 := by omega
  have h2 : n.factorial ≠ 0 := Nat.factorial_ne_zero n
  have hF : ∀ p, (n + 1).factorial.factorization p
      = n.factorial.factorization p + (n + 1).factorization p := by
    intro p
    rw [Nat.factorial_succ, Nat.factorization_mul h1 h2, Finsupp.add_apply]
    omega
  have hS1 : n.factorial.primeFactors ⊆ (n + 1).factorial.primeFactors :=
    Nat.primeFactors_mono (Nat.factorial_dvd_factorial (by omega)) (Nat.factorial_ne_zero _)
  have hS2 : (n + 1).primeFactors ⊆ (n + 1).factorial.primeFactors :=
    Nat.primeFactors_mono (Nat.dvd_factorial (by omega) le_rfl) (Nat.factorial_ne_zero _)
  constructor
  · unfold factorialDivisorRatio
    rw [tau_eq_prod _ (Nat.factorial_ne_zero _) (n + 1).factorial.primeFactors subset_rfl,
      tau_eq_prod _ h2 (n + 1).factorial.primeFactors hS1, ← Finset.prod_div_distrib]
    have hc : ∀ p ∈ (n + 1).factorial.primeFactors,
        (((n + 1).factorial.factorization p : ℝ) + 1) / ((n.factorial.factorization p : ℝ) + 1)
          = primeFactorRatio n p := by
      intro p _
      unfold primeFactorRatio
      rw [hF p]
      push_cast
      ring
    rw [Finset.prod_congr rfl hc]
    symm
    apply Finset.prod_subset hS2
    intro p _ hp
    have h0 : (n + 1).factorization p = 0 := fact_zero_of_not_mem _ p hp
    unfold primeFactorRatio
    rw [h0, Nat.cast_zero, add_zero]
    exact div_self (by positivity)
  · intro p _
    unfold primeFactorRatio
    rw [one_le_div (by positivity)]
    have := Nat.cast_nonneg (α := ℝ) ((n + 1).factorization p)
    linarith
end erdos_37099_hyp_product_ns

namespace erdos_37099_hyp_large_prime_ns
-- CHECK: Nat.factorization_def padicValNat_factorial Nat.log_lt_of_lt_pow Nat.Prime.pow_dvd_iff_le_factorization Nat.Coprime.mul_dvd_of_dvd_of_dvd Nat.coprime_primes
open Filter

open scoped ArithmeticFunction.sigma

theorem erdos_37099_hyp_large_prime : S4Prop := by
  intro n hn
  constructor
  · intro q hq hdvd hsq
    have hq2 : 2 ≤ q := hq.two_le
    have hne : n + 1 ≠ 0 := by omega
    have hB : (n + 1).factorization q = 1 := by
      have h1 : 1 ≤ (n + 1).factorization q :=
        (hq.pow_dvd_iff_le_factorization hne).mp (by simpa using hdvd)
      have h2 : ¬ 2 ≤ (n + 1).factorization q := by
        intro h
        have h3 := (hq.pow_dvd_iff_le_factorization hne).mpr h
        have h4 := Nat.le_of_dvd (by omega) h3
        exact Nat.lt_irrefl _ (lt_of_lt_of_le hsq h4)
      omega
    have hlt : n < q ^ 2 := lt_of_le_of_lt (Nat.le_succ n) hsq
    have hlog : Nat.log q n < 2 := Nat.log_lt_of_lt_pow (by omega) hlt
    haveI := Fact.mk hq
    have hA : n.factorial.factorization q = n / q := by
      rw [Nat.factorization_def _ hq, padicValNat_factorial hlog]
      rw [show Finset.Ico 1 2 = {1} by decide, Finset.sum_singleton, pow_one]
    have hdvd' := hdvd
    obtain ⟨c, hc⟩ := hdvd'
    have hcdiv : (n + 1) / q = c := by
      rw [hc]; exact Nat.mul_div_cancel_left c (by omega)
    have hnq : n / q + 1 = c := by
      have hdm := Nat.div_add_mod n q
      have hml := Nat.mod_lt n (by omega : q > 0)
      set a := n / q
      set r := n % q
      have h1 : a < c := by
        by_contra h
        push_neg at h
        have := Nat.mul_le_mul (le_refl q) h
        linarith
      have h2 : c < a + 2 := by
        by_contra h
        push_neg at h
        have := Nat.mul_le_mul (le_refl q) h
        nlinarith
      omega
    refine ⟨hB, by rw [hA, hcdiv]; exact hnq, ?_, Nat.le_of_dvd (by omega) hdvd⟩
    have hc0 : (c:ℝ) ≠ 0 := by
      have : c ≠ 0 := by
        rintro rfl
        omega
      exact_mod_cast this
    have hq0 : (q:ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
    have hcast : ((n + 1 : ℕ) : ℝ) = (q:ℝ) * (c:ℝ) := by
      rw [hc, Nat.cast_mul]
    have key : ((n.factorial.factorization q : ℕ) : ℝ) = (c:ℝ) - 1 := by
      have h' : n.factorial.factorization q + 1 = c := by rw [hA]; exact hnq
      have : ((n.factorial.factorization q : ℕ) : ℝ) + 1 = (c:ℝ) := by exact_mod_cast h'
      linarith
    unfold primeFactorRatio
    rw [hB, key, hcast, Nat.cast_one, sub_add_cancel]
    field_simp
    try ring
  · intro q q' hq hq' h1 h2 hs hs'
    by_contra hne
    have hcop : Nat.Coprime q q' := (Nat.coprime_primes hq hq').mpr hne
    have hd := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h1 h2
    have hle := Nat.le_of_dvd (by omega) hd
    rcases le_total q q' with h | h
    · have := Nat.mul_le_mul h (le_refl q)
      nlinarith
    · have := Nat.mul_le_mul h (le_refl q')
      nlinarith
end erdos_37099_hyp_large_prime_ns

namespace erdos_37099_hyp_small_prime_ns
-- CHECK: Nat.succ_div_of_dvd Nat.succ_div_of_not_dvd Nat.Prime.pow_dvd_iff_le_factorization div_le_div_of_nonneg_left Real.add_one_le_exp Real.sqrt_le_sqrt Real.sqrt_sq
open Filter

open scoped ArithmeticFunction.sigma

private lemma pow_div_dvd_factorial_aux (p : ℕ) : ∀ n : ℕ, p ^ (n / p) ∣ n.factorial
  | 0 => by simp
  | n + 1 => by
    have ih := pow_div_dvd_factorial_aux p n
    rw [Nat.factorial_succ]
    by_cases h : p ∣ n + 1
    · rw [Nat.succ_div_of_dvd h, pow_succ, mul_comm (n + 1)]
      exact Nat.mul_dvd_mul ih h
    · rw [Nat.succ_div_of_not_dvd h]
      exact Dvd.dvd.mul_left ih _

theorem erdos_37099_hyp_small_prime : S5Prop := by
  intro n p hn hp hdvd hsq
  unfold primeFactorRatio
  have hvk : n / p ≤ n.factorial.factorization p :=
    (hp.pow_dvd_iff_le_factorization (Nat.factorial_ne_zero n)).mp
      (pow_div_dvd_factorial_aux p n)
  have hk : (n + 1) / p = n / p + 1 := Nat.succ_div_of_dvd hdvd
  have hkp : (n + 1) / p * p = n + 1 := Nat.div_mul_cancel hdvd
  have hppos := hp.pos
  have hpp : p * p ≤ (n + 1) / p * p := by
    rw [hkp]; nlinarith [hsq]
  have hpk : p ≤ (n + 1) / p := by nlinarith
  have hkk : n + 1 ≤ (n + 1) / p * ((n + 1) / p) := by nlinarith
  have hvk1 : (n + 1) / p ≤ n.factorial.factorization p + 1 := by omega
  have h1 : n + 1 ≤ (n.factorial.factorization p + 1) * (n.factorial.factorization p + 1) := by
    nlinarith
  have hvR : ((n + 1 : ℕ) : ℝ) ≤ ((n.factorial.factorization p : ℝ) + 1) ^ 2 := by
    have : ((n + 1 : ℕ) : ℝ) ≤
        (((n.factorial.factorization p + 1) * (n.factorial.factorization p + 1) : ℕ) : ℝ) := by
      exact_mod_cast h1
    rw [sq]
    push_cast at this ⊢
    linarith
  have hsqrt : Real.sqrt ((n + 1 : ℕ) : ℝ) ≤ (n.factorial.factorization p : ℝ) + 1 := by
    calc Real.sqrt ((n + 1 : ℕ) : ℝ)
        ≤ Real.sqrt (((n.factorial.factorization p : ℝ) + 1) ^ 2) := Real.sqrt_le_sqrt hvR
      _ = (n.factorial.factorization p : ℝ) + 1 := Real.sqrt_sq (by positivity)
  have hpos : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hv1 : (0 : ℝ) < (n.factorial.factorization p : ℝ) + 1 := by positivity
  have he : (0 : ℝ) ≤ ((n + 1).factorization p : ℝ) := Nat.cast_nonneg _
  constructor
  · rw [le_div_iff₀ hv1, one_mul]
    linarith
  · have heq : (n.factorial.factorization p : ℝ) + ((n + 1).factorization p : ℝ) + 1
        = ((n.factorial.factorization p : ℝ) + 1) + ((n + 1).factorization p : ℝ) := by ring
    rw [heq, add_div, div_self hv1.ne']
    have h2 : ((n + 1).factorization p : ℝ) / ((n.factorial.factorization p : ℝ) + 1)
        ≤ ((n + 1).factorization p : ℝ) / Real.sqrt ((n + 1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_left he hpos hsqrt
    have h3 := Real.add_one_le_exp (((n + 1).factorization p : ℝ) / Real.sqrt ((n + 1 : ℕ) : ℝ))
    linarith
end erdos_37099_hyp_small_prime_ns

namespace erdos_37099_hyp_omega_le_log_ns
open Filter

open scoped ArithmeticFunction.sigma

private lemma two_pow_omega_le (m : ℕ) (hm0 : m ≠ 0) :
    2 ^ (∑ p ∈ m.primeFactors, m.factorization p) ≤ m := by
  rw [← Finset.prod_pow_eq_pow_sum]
  calc ∏ p ∈ m.primeFactors, 2 ^ m.factorization p
        ≤ ∏ p ∈ m.primeFactors, p ^ m.factorization p := by
          apply Finset.prod_le_prod
          · intro i _; positivity
          · intro i hi
            exact Nat.pow_le_pow_left (Nat.prime_of_mem_primeFactors hi).two_le _
    _ = m := by
          conv_rhs => rw [← Nat.factorization_prod_pow_eq_self hm0]
          rw [Finsupp.prod, Nat.support_factorization]

theorem erdos_37099_hyp_omega_le_log : S6Prop := by
  intro m hm
  have hm0 : m ≠ 0 := by omega
  have key := two_pow_omega_le m hm0
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hlog2]
  have h2 : ((2:ℝ) ^ (∑ p ∈ m.primeFactors, m.factorization p)) ≤ (m:ℝ) := by
    exact_mod_cast key
  have h3 := Real.log_le_log (by positivity) h2
  rw [Real.log_pow] at h3
  exact_mod_cast h3
end erdos_37099_hyp_omega_le_log_ns

namespace erdos_37099_hyp_main_term_bounds_ns
open Filter

open scoped ArithmeticFunction.sigma

theorem erdos_37099_hyp_main_term_bounds : S3Prop → S4Prop → S5Prop → S6Prop → S7Prop := by
  intro h3 h4 h5 h6 n hn
  obtain ⟨hR, hge⟩ := h3 n hn
  obtain ⟨hL, huniq⟩ := h4 n hn
  have hmain : mainTerm n = ∏ p ∈ (n + 1).primeFactors.filter (fun p => n + 1 < p ^ 2),
      primeFactorRatio n p := by
    unfold mainTerm
    apply Finset.prod_congr rfl
    intro p hp
    rw [Finset.mem_filter, Nat.mem_primeFactors] at hp
    exact ((hL p hp.1.1 hp.1.2.1 hp.2).2.2.1).symm
  have hT1 : 1 ≤ mainTerm n ∧ mainTerm n ≤ 2 := by
    unfold mainTerm
    rcases Finset.eq_empty_or_nonempty ((n + 1).primeFactors.filter (fun p => n + 1 < p ^ 2))
      with he | ⟨q, hq⟩
    · rw [he, Finset.prod_empty]; norm_num
    · have hq' := hq
      rw [Finset.mem_filter, Nat.mem_primeFactors] at hq'
      have hsing : (n + 1).primeFactors.filter (fun p => n + 1 < p ^ 2) = {q} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        refine ⟨hq, fun x hx => ?_⟩
        rw [Finset.mem_filter, Nat.mem_primeFactors] at hx
        exact huniq x q hx.1.1 hq'.1.1 hx.1.2.1 hq'.1.2.1 hx.2 hq'.2
      rw [hsing, Finset.prod_singleton]
      have hqle := (hL q hq'.1.1 hq'.1.2.1 hq'.2).2.2.2
      have hmpos : (0:ℝ) < ((n + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos n)
      have hqle' : (q:ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hqle
      have h0 : (0:ℝ) ≤ (q:ℝ) / ((n + 1 : ℕ) : ℝ) := div_nonneg (Nat.cast_nonneg _) hmpos.le
      have h1 : (q:ℝ) / ((n + 1 : ℕ) : ℝ) ≤ 1 := by
        rw [div_le_one hmpos]; exact hqle'
      constructor <;> linarith
  obtain ⟨S, hS⟩ : ∃ S : Finset ℕ, S = (n + 1).primeFactors.filter (fun p => ¬ (n + 1 < p ^ 2)) :=
    ⟨_, rfl⟩
  have hSsub : S ⊆ (n + 1).primeFactors := by rw [hS]; exact Finset.filter_subset _ _
  have hSmem : ∀ p ∈ S, p.Prime ∧ p ∣ n + 1 ∧ p ^ 2 ≤ n + 1 := by
    intro p hp
    rw [hS, Finset.mem_filter, Nat.mem_primeFactors] at hp
    exact ⟨hp.1.1, hp.1.2.1, Nat.le_of_not_lt hp.2⟩
  have hsplit : factorialDivisorRatio n = mainTerm n * ∏ p ∈ S, primeFactorRatio n p := by
    rw [hR, hmain, hS]
    exact (Finset.prod_filter_mul_prod_filter_not _ _ _).symm
  have hB1 : 1 ≤ ∏ p ∈ S, primeFactorRatio n p := by
    calc (1:ℝ) = ∏ p ∈ S, (1:ℝ) := (Finset.prod_const_one).symm
      _ ≤ ∏ p ∈ S, primeFactorRatio n p :=
        Finset.prod_le_prod (fun _ _ => zero_le_one) (fun p hp => hge p (hSsub hp))
  have hsqpos : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.succ_pos n))
  have hB2 : ∏ p ∈ S, primeFactorRatio n p ≤ Real.exp (errDelta (n + 1)) := by
    calc ∏ p ∈ S, primeFactorRatio n p
        ≤ ∏ p ∈ S, Real.exp (((n + 1).factorization p : ℝ) / Real.sqrt ((n + 1 : ℕ) : ℝ)) :=
          Finset.prod_le_prod (fun p hp => le_trans zero_le_one (hge p (hSsub hp)))
            (fun p hp => (h5 n p hn (hSmem p hp).1 (hSmem p hp).2.1 (hSmem p hp).2.2).2)
      _ = Real.exp (∑ p ∈ S, ((n + 1).factorization p : ℝ) / Real.sqrt ((n + 1 : ℕ) : ℝ)) := by
          rw [Real.exp_sum]
      _ ≤ Real.exp (errDelta (n + 1)) := by
          apply Real.exp_le_exp.mpr
          rw [← Finset.sum_div]
          unfold errDelta
          have h6' := h6 (n + 1) (by omega)
          rw [Nat.cast_sum] at h6'
          have hsum : ∑ p ∈ S, ((n + 1).factorization p : ℝ)
              ≤ ∑ p ∈ (n + 1).primeFactors, ((n + 1).factorization p : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hSsub (fun _ _ _ => Nat.cast_nonneg _)
          have hfin := le_trans hsum h6'
          gcongr
  have hδ : 0 ≤ errDelta (n + 1) := by
    unfold errDelta
    have hl1 : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) := by
      apply Real.log_nonneg
      have : (1:ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.succ_pos n)
      exact this
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    exact div_nonneg (div_nonneg hl1 hl2.le) (Real.sqrt_nonneg _)
  have hE1 : 1 ≤ Real.exp (errDelta (n + 1)) := by
    have := Real.add_one_le_exp (errDelta (n + 1))
    linarith
  rw [hsplit]
  have hT0 : 0 ≤ mainTerm n := by linarith [hT1.1]
  have hTB := mul_le_mul_of_nonneg_left hB2 hT0
  have hTB1 : mainTerm n ≤ mainTerm n * ∏ p ∈ S, primeFactorRatio n p :=
    le_mul_of_one_le_right hT0 hB1
  have hprod : 0 ≤ (2 - mainTerm n) * (Real.exp (errDelta (n + 1)) - 1) :=
    mul_nonneg (by linarith [hT1.2]) (by linarith)
  refine ⟨hT1.1, hT1.2, hTB1, hTB, ?_⟩
  nlinarith [hTB, hprod]
end erdos_37099_hyp_main_term_bounds_ns

namespace erdos_37099_hyp_main_term_mem_ns
open Filter

open scoped ArithmeticFunction.sigma

theorem erdos_37099_hyp_main_term_mem : S4Prop → ∀ n : ℕ, 1 ≤ n → mainTerm n ∈ limitPointSet := by
  intro hS4 n hn
  obtain ⟨_, huniq⟩ := hS4 n hn
  unfold mainTerm limitPointSet
  rcases ((n + 1).primeFactors.filter (fun p => n + 1 < p ^ 2)).eq_empty_or_nonempty with hE | ⟨q, hq⟩
  · rw [hE, Finset.prod_empty]
    exact Or.inl rfl
  · have hFq : (n + 1).primeFactors.filter (fun p => n + 1 < p ^ 2) = {q} := by
      rw [Finset.eq_singleton_iff_unique_mem]
      refine ⟨hq, fun x hx => ?_⟩
      simp only [Finset.mem_filter, Nat.mem_primeFactors] at hx hq
      exact huniq x q hx.1.1 hq.1.1 hx.1.2.1 hq.1.2.1 hx.2 hq.2
    simp only [Finset.mem_filter, Nat.mem_primeFactors] at hq
    rw [hFq, Finset.prod_singleton]
    obtain ⟨⟨hp, hdvd, _⟩, _⟩ := hq
    obtain ⟨k, hk⟩ := hdvd
    refine Or.inr ⟨k, ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos k with h0 | h0
      · subst h0
        simp at hk
      · exact h0
    · have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
      rw [hk]
      push_cast
      rw [← div_div, div_self hq0]
end erdos_37099_hyp_main_term_mem_ns

namespace erdos_37099_hyp_closed_ns
-- CHECK: Filter.Tendsto.isCompact_insert_range IsCompact.isClosed tendsto_one_div_add_atTop_nhds_zero_nat Filter.Tendsto.const_add
open Filter

open scoped ArithmeticFunction.sigma

theorem erdos_37099_hyp_closed : IsClosed limitPointSet := by
  have hT : Tendsto (fun k : ℕ => (1:ℝ) + 1 / ((k:ℝ) + 1)) atTop (nhds 1) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_add (1:ℝ)
    rw [add_zero] at this
    exact this
  have heq : limitPointSet = insert 1 (Set.range (fun k : ℕ => (1:ℝ) + 1 / ((k:ℝ) + 1))) := by
    ext x
    simp only [limitPointSet, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq,
      Set.mem_insert_iff, Set.mem_range]
    constructor
    · rintro (h | ⟨k, hk, rfl⟩)
      · exact Or.inl h
      · right
        refine ⟨k - 1, ?_⟩
        have hc : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by
          rw [Nat.cast_sub hk]; simp
        simp only [hc]
    · rintro (h | ⟨k, rfl⟩)
      · exact Or.inl h
      · right
        exact ⟨k + 1, by omega, by norm_num⟩
  rw [heq]
  exact hT.isCompact_insert_range.isClosed
end erdos_37099_hyp_closed_ns

namespace erdos_37099_hyp_main_term_kp_ns
-- CHECK: mapClusterPt_iff_frequently isClosed_setOf_clusterPt tendsto_one_div_add_atTop_nhds_zero_nat Filter.not_frequently Filter.frequently_atTop Metric.mem_nhds_iff
open Filter

open scoped ArithmeticFunction.sigma

theorem erdos_37099_hyp_main_term_kp : S4Prop →
    ∀ k p : ℕ, 1 ≤ k → p.Prime → k < p → mainTerm (k * p - 1) = 1 + 1 / (k : ℝ) := by
  intro hS4 k p hk hp hkp
  have hp2 := hp.two_le
  have h2 : 2 ≤ k * p := by nlinarith
  have hn1 : k * p - 1 + 1 = k * p := by omega
  have hset : ((k * p).primeFactors.filter (fun q => k * p < q ^ 2)) = {p} := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_singleton, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨hq, hqd, _⟩, hlt⟩
      exact (hS4 (k * p - 1) (by omega)).2 q p hq hp (by rw [hn1]; exact hqd)
        (by rw [hn1]; exact Nat.dvd_mul_left p k) (by rw [hn1]; exact hlt)
        (by rw [hn1]; nlinarith)
    · intro hq
      rw [hq]
      exact ⟨⟨hp, Nat.dvd_mul_left p k, by omega⟩, by nlinarith⟩
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  unfold mainTerm
  rw [hn1, hset, Finset.prod_singleton]
  rw [Nat.cast_mul, mul_comm, ← div_div, div_self hpR]
end erdos_37099_hyp_main_term_kp_ns

theorem erdos_37099_hyp_product : S3Prop := by
  exact erdos_37099_hyp_product_ns.erdos_37099_hyp_product

theorem erdos_37099_hyp_large_prime : S4Prop := by
  exact erdos_37099_hyp_large_prime_ns.erdos_37099_hyp_large_prime

theorem erdos_37099_hyp_small_prime : S5Prop := by
  exact erdos_37099_hyp_small_prime_ns.erdos_37099_hyp_small_prime

theorem erdos_37099_hyp_omega_le_log : S6Prop := by
  exact erdos_37099_hyp_omega_le_log_ns.erdos_37099_hyp_omega_le_log

theorem erdos_37099_hyp_main_term_bounds : S3Prop → S4Prop → S5Prop → S6Prop → S7Prop := by
  exact erdos_37099_hyp_main_term_bounds_ns.erdos_37099_hyp_main_term_bounds

-- S8 step 1: log x / √x → 0 as x → ∞; follows from Real.isLittleO_log_rpow_atTop with r = 1/2
-- (√x = x^(1/2) for x ≥ 0), or from tendsto_log_div_rpow_nhds_zero style lemmas.
namespace erdos_37099_hyp_log_div_sqrt_ns
open Filter

open scoped ArithmeticFunction.sigma

theorem erdos_37099_hyp_log_div_sqrt :
    Tendsto (fun x : ℝ => Real.log x / Real.sqrt x) atTop (nhds 0) := by
  have hfun : (fun x : ℝ => Real.log x / Real.sqrt x) =
      fun x : ℝ => Real.log x / x ^ (1/2 : ℝ) := by
    funext x
    rw [Real.sqrt_eq_rpow]
  rw [hfun]
  exact (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1/2)).tendsto_div_nhds_zero
end erdos_37099_hyp_log_div_sqrt_ns

theorem erdos_37099_hyp_log_div_sqrt :
    Tendsto (fun x : ℝ => Real.log x / Real.sqrt x) atTop (nhds 0) := by
  exact erdos_37099_hyp_log_div_sqrt_ns.erdos_37099_hyp_log_div_sqrt



-- S8 steps 2-3: derived from erdos_37099_hyp_log_div_sqrt via continuity of exp (no sorry).
theorem erdos_37099_hyp_err_tendsto :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m : ℕ, M ≤ m → 2 * (Real.exp (errDelta m) - 1) < ε := by
  intro ε hε
  have h0 := erdos_37099_hyp_log_div_sqrt
  have h1 : Tendsto (fun m : ℕ => Real.log (m : ℝ) / Real.sqrt (m : ℝ)) atTop (nhds 0) :=
    h0.comp tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun m : ℕ => errDelta m) atTop (nhds 0) := by
    have h3 := h1.div_const (Real.log 2)
    rw [zero_div] at h3
    refine Filter.Tendsto.congr (fun m => ?_) h3
    simp only [errDelta]
    ring
  have h4 : Tendsto (fun m : ℕ => 2 * (Real.exp (errDelta m) - 1)) atTop
      (nhds (2 * (Real.exp 0 - 1))) :=
    (((Real.continuous_exp.tendsto 0).comp h2).sub_const 1).const_mul 2
  rw [Real.exp_zero, sub_self, mul_zero] at h4
  have h5 := h4.eventually (gt_mem_nhds hε)
  rw [Filter.eventually_atTop] at h5
  exact h5

theorem erdos_37099_hyp_main_term_mem : S4Prop → ∀ n : ℕ, 1 ≤ n → mainTerm n ∈ limitPointSet := by
  exact erdos_37099_hyp_main_term_mem_ns.erdos_37099_hyp_main_term_mem

theorem erdos_37099_hyp_closed : IsClosed limitPointSet := by
  exact erdos_37099_hyp_closed_ns.erdos_37099_hyp_closed

theorem erdos_37099_hyp_main_term_kp : S4Prop →
    ∀ k p : ℕ, 1 ≤ k → p.Prime → k < p → mainTerm (k * p - 1) = 1 + 1 / (k : ℝ) := by
  exact erdos_37099_hyp_main_term_kp_ns.erdos_37099_hyp_main_term_kp

theorem erdos_37099 :
    {x : ℝ | MapClusterPt x atTop factorialDivisorRatio} = limitPointSet := by
  have hS4 := erdos_37099_hyp_large_prime
  have h7 := erdos_37099_hyp_main_term_bounds erdos_37099_hyp_product erdos_37099_hyp_large_prime
    erdos_37099_hyp_small_prime erdos_37099_hyp_omega_le_log
  have hconv : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      |factorialDivisorRatio n - mainTerm n| < ε := by
    intro ε hε
    obtain ⟨M, hM⟩ := erdos_37099_hyp_err_tendsto ε hε
    refine ⟨max M 1, fun n hn => ?_⟩
    have h1 : 1 ≤ n := le_trans (le_max_right M 1) hn
    have hM' : M ≤ n + 1 := by
      have := le_trans (le_max_left M 1) hn
      omega
    obtain ⟨_, _, hTR, _, hRT⟩ := h7 n h1
    have hb := hM (n + 1) hM'
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ factorialDivisorRatio n - mainTerm n)]
    linarith
  have hS11 : ∀ x : ℝ, MapClusterPt x atTop factorialDivisorRatio → x ∈ limitPointSet := by
    intro x hx
    by_contra hxL
    have hopen : IsOpen limitPointSetᶜ := erdos_37099_hyp_closed.isOpen_compl
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen x hxL
    obtain ⟨N, hN⟩ := hconv (r / 2) (by linarith)
    have hfreq : ∃ᶠ n in atTop, factorialDivisorRatio n ∈ Metric.ball x (r / 2) := by
      first
      | exact (mapClusterPt_iff_frequently.mp hx) _ (Metric.ball_mem_nhds x (by linarith))
      | exact (mapClusterPt_iff.mp hx) _ (Metric.ball_mem_nhds x (by linarith))
      | exact ((mapClusterPt_iff _ _ _).mp hx) _ (Metric.ball_mem_nhds x (by linarith))
    have hev : ∀ᶠ n in atTop, factorialDivisorRatio n ∉ Metric.ball x (r / 2) := by
      rw [Filter.eventually_atTop]
      refine ⟨max N 1, fun n hn => ?_⟩
      have hn1 : 1 ≤ n := le_trans (le_max_right N 1) hn
      have hnN : N ≤ n := le_trans (le_max_left N 1) hn
      have hT := erdos_37099_hyp_main_term_mem hS4 n hn1
      have hTnot : ¬ (|mainTerm n - x| < r) := by
        intro hlt
        have hmem : mainTerm n ∈ Metric.ball x r := by
          rw [Metric.mem_ball, Real.dist_eq]
          exact hlt
        have hc := hball hmem
        rw [Set.mem_compl_iff] at hc
        exact hc hT
      intro hR
      rw [Metric.mem_ball, Real.dist_eq] at hR
      have hN' := hN n hnN
      have h3 := abs_sub_le (mainTerm n) (factorialDivisorRatio n) x
      rw [abs_sub_comm (mainTerm n) (factorialDivisorRatio n)] at h3
      have h4 := not_lt.mp hTnot
      linarith
    exact Filter.not_frequently.mpr hev hfreq
  have hS12 : ∀ k : ℕ, 1 ≤ k → MapClusterPt (1 + 1 / (k : ℝ)) atTop factorialDivisorRatio := by
    intro k hk
    have key : ∀ s ∈ nhds (1 + 1 / (k : ℝ)), ∃ᶠ n in atTop, factorialDivisorRatio n ∈ s := by
      intro s hs
      obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp hs
      rw [Filter.frequently_atTop]
      intro N₀
      obtain ⟨N, hN⟩ := hconv ε hε
      obtain ⟨p, hp_ge, hp⟩ := Nat.exists_infinite_primes (k + N₀ + N + 2)
      have hkp : p ≤ k * p := by nlinarith
      refine ⟨k * p - 1, by omega, ?_⟩
      apply hεs
      rw [Metric.mem_ball, Real.dist_eq]
      have h1 := hN (k * p - 1) (by omega)
      rw [erdos_37099_hyp_main_term_kp hS4 k p hk hp (by omega)] at h1
      exact h1
    first
    | exact mapClusterPt_iff_frequently.mpr key
    | exact mapClusterPt_iff.mpr key
    | exact (mapClusterPt_iff _ _ _).mpr key
  have h13 : MapClusterPt (1 : ℝ) atTop factorialDivisorRatio := by
    have hC : IsClosed {x : ℝ | MapClusterPt x atTop factorialDivisorRatio} := by
      first
      | exact isClosed_setOf_clusterPt
      | exact isClosed_setOf_clusterPt (f := Filter.map factorialDivisorRatio atTop)
    have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 : Tendsto (fun k : ℕ => (1 : ℝ) + 1 / ((k : ℝ) + 1)) atTop (nhds (1 + 0)) :=
      tendsto_const_nhds.add h0
    rw [add_zero] at h1
    have hmem := hC.mem_of_tendsto h1 (Filter.Eventually.of_forall fun k => by
      show MapClusterPt (1 + 1 / ((k : ℝ) + 1)) atTop factorialDivisorRatio
      have hk := hS12 (k + 1) (by omega)
      rw [Nat.cast_add, Nat.cast_one] at hk
      exact hk)
    exact hmem
  ext x
  constructor
  · intro hx
    exact hS11 x hx
  · intro hx
    simp only [limitPointSet, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq] at hx
    rcases hx with h | ⟨k, hk, rfl⟩
    · subst h
      exact h13
    · exact hS12 k hk
