import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic

set_option maxHeartbeats 1000000
set_option autoImplicit false

open Filter
open scoped ArithmeticFunction.sigma

noncomputable def factorialDivisorRatio (n : ℕ) : ℝ :=
  (σ 0 (n + 1).factorial : ℝ) / (σ 0 n.factorial : ℝ)

def limitPointSet : Set ℝ :=
  {1} ∪ {x | ∃ k : ℕ, 1 ≤ k ∧ x = 1 + 1 / (k : ℝ)}

-- CHECK: mapClusterPt_iff_frequently Filter.Tendsto.eventually_mem Filter.Frequently.and_eventually Real.one_le_exp Metric.tendsto_atTop tendsto_of_tendsto_of_tendsto_of_le_of_le
-- CHECK: Real.exp_sum Real.add_one_le_exp Real.exp_le_exp div_le_div_iff₀ Finset.sum_div Finset.prod_le_prod Finset.prod_const_one Real.mul_self_sqrt Real.sqrt_pos Nat.prime_of_mem_primeFactors Nat.dvd_of_mem_primeFactors le_of_mul_le_mul_left

open Classical in
noncomputable def largeFactorH (m : ℕ) : ℝ :=
  if h : ∃ P : ℕ, P.Prime ∧ P ∣ m ∧ m < P * P then
    1 + 1 / ((m / Classical.choose h : ℕ) : ℝ)
  else 1

noncomputable def smallPrimeProduct (m : ℕ) : ℝ :=
  ∏ q ∈ Finset.filter (fun q => q * q ≤ m) m.primeFactors,
    (1 + (m.factorization q : ℝ) / (((m - 1).factorial.factorization q : ℝ) + 1))

namespace erdos_42884_hyp_product_formula_ns
open Filter

open scoped ArithmeticFunction.sigma

private lemma fz42884 {n q : ℕ} (h : q ∉ n.primeFactors) : n.factorization q = 0 := by
  by_contra hne
  exact h (Nat.support_factorization n ▸ Finsupp.mem_support_iff.mpr hne)

private lemma key42884 (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ((a * b).divisors.card : ℝ) / (b.divisors.card : ℝ)
      = ∏ q ∈ a.primeFactors, (1 + (a.factorization q : ℝ) / ((b.factorization q : ℝ) + 1)) := by
  rw [Nat.card_divisors (mul_ne_zero ha hb), Nat.card_divisors hb, Nat.primeFactors_mul ha hb,
    Nat.factorization_mul ha hb]
  simp only [Finsupp.coe_add, Pi.add_apply, Nat.cast_prod, Nat.cast_add, Nat.cast_one]
  rw [Finset.prod_subset (Finset.subset_union_left (s₂ := b.primeFactors))
      (f := fun q => (1 + (a.factorization q : ℝ) / ((b.factorization q : ℝ) + 1)))
      (fun q _ hq => by simp [fz42884 hq])]
  rw [Finset.prod_subset (Finset.subset_union_right (s₁ := a.primeFactors))
      (f := fun q => ((b.factorization q : ℝ) + 1))
      (fun q _ hq => by simp [fz42884 hq])]
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro q _
  have hpos : (b.factorization q : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring_nf

theorem erdos_42884_hyp_product_formula :
    ∀ m : ℕ, 2 ≤ m →
      (σ 0 m.factorial : ℝ) / (σ 0 (m - 1).factorial : ℝ)
        = ∏ q ∈ m.primeFactors,
            (1 + (m.factorization q : ℝ) / (((m - 1).factorial.factorization q : ℝ) + 1)) := by
  intro m hm
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  simp only [ArithmeticFunction.sigma_zero_apply]
  rw [Nat.factorial_succ]
  exact key42884 (n + 1) n.factorial (by omega) (Nat.factorial_ne_zero n)
end erdos_42884_hyp_product_formula_ns

namespace erdos_42884_hyp_legendre_lower_ns
open Filter

open scoped ArithmeticFunction.sigma

private lemma pow_dvd_fact_mul (q : ℕ) (hq : 1 ≤ q) : ∀ j : ℕ, q ^ j ∣ (q * j).factorial := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have hpos : 1 ≤ q * (j + 1) := Nat.mul_pos hq (Nat.succ_pos j)
    have hexp : q * (j + 1) = q * j + q := by ring
    obtain ⟨r, hr⟩ : ∃ r, q * (j + 1) = r + 1 := ⟨q * (j + 1) - 1, by omega⟩
    have hrle : q * j ≤ r := by omega
    rw [hr, Nat.factorial_succ, pow_succ, mul_comm (q ^ j) q]
    apply Nat.mul_dvd_mul
    · rw [← hr]; exact dvd_mul_right q (j + 1)
    · exact ih.trans (Nat.factorial_dvd_factorial hrle)

theorem erdos_42884_hyp_legendre_lower :
    ∀ m q : ℕ, 1 ≤ m → q.Prime → q ∣ m →
      m ≤ q * ((m - 1).factorial.factorization q + 1) := by
  intro m q hm hq hqm
  obtain ⟨k, rfl⟩ := hqm
  have hq2 : 2 ≤ q := hq.two_le
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hm
    · exact h
  have hqk : q * k = q * (k - 1) + q := by
    rw [← Nat.mul_succ]; congr 1; omega
  have hdvd : q ^ (k - 1) ∣ (q * k - 1).factorial :=
    (pow_dvd_fact_mul q (by omega) (k - 1)).trans
      (Nat.factorial_dvd_factorial (by omega))
  have hle : k - 1 ≤ (q * k - 1).factorial.factorization q :=
    (hq.pow_dvd_iff_le_factorization (Nat.factorial_ne_zero _)).mp hdvd
  exact Nat.mul_le_mul le_rfl (by omega)
end erdos_42884_hyp_legendre_lower_ns

namespace erdos_42884_hyp_large_prime_unique_ns
open Filter

open scoped ArithmeticFunction.sigma

theorem erdos_42884_hyp_large_prime_unique :
    ∀ m P Q : ℕ, m ≠ 0 → P.Prime → Q.Prime → P ∣ m → Q ∣ m →
      m < P * P → m < Q * Q → P = Q := by
  intro m P Q hm hP hQ hPm hQm hPP hQQ
  by_contra hne
  have hcop : Nat.Coprime P Q := (Nat.coprime_primes hP hQ).mpr hne
  have hdvd : P * Q ∣ m := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hPm hQm
  have hle : P * Q ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hdvd
  rcases le_total P Q with h | h
  · have h1 : P * P ≤ P * Q := Nat.mul_le_mul le_rfl h
    linarith
  · have h1 : Q * Q ≤ P * Q := Nat.mul_le_mul h le_rfl
    linarith
end erdos_42884_hyp_large_prime_unique_ns

namespace erdos_42884_hyp_large_prime_val_ns
open Filter

open scoped ArithmeticFunction.sigma

theorem erdos_42884_hyp_large_prime_val :
    ∀ k P : ℕ, 1 ≤ k → k < P → P.Prime →
      (k * P).factorization P = 1 ∧ (k * P - 1).factorial.factorization P = k - 1 := by
  intro k P hk hkP hP
  have hP2 : 2 ≤ P := hP.two_le
  constructor
  · have hk0 : k ≠ 0 := by omega
    have hP0 : P ≠ 0 := by omega
    rw [Nat.factorization_mul hk0 hP0, Finsupp.add_apply, hP.factorization_self]
    have hnd : ¬ P ∣ k := fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
    rw [Nat.factorization_eq_zero_of_not_dvd hnd]
  · haveI := Fact.mk hP
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hlt : (j + 1) * P < P * P := Nat.mul_lt_mul_of_pos_right hkP (by omega)
    have hexp : (j + 1) * P = j * P + P := by ring
    have hsq : (j + 1) * P - 1 < P ^ 2 := by
      rw [pow_two]; omega
    have hlog : Nat.log P ((j + 1) * P - 1) < 2 := by
      first
        | exact Nat.log_lt_of_lt_pow (by rw [hexp]; omega) hsq
        | exact Nat.log_lt_of_lt_pow hsq
    rw [Nat.factorization_def _ hP, padicValNat_factorial hlog]
    have hI : Finset.Ico 1 2 = ({1} : Finset ℕ) := by decide
    rw [hI, Finset.sum_singleton, pow_one]
    have h1 : j * P ≤ (j + 1) * P - 1 := by rw [hexp]; omega
    have h2 : (j + 1) * P - 1 < (j + 1) * P := by rw [hexp]; omega
    have e : j + 1 - 1 = j := by omega
    rw [e]
    apply le_antisymm
    · exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (by omega)).mpr h2)
    · exact (Nat.le_div_iff_mul_le (by omega)).mpr h1
end erdos_42884_hyp_large_prime_val_ns

namespace erdos_42884_hyp_h_mem_ns
open Filter

open scoped ArithmeticFunction.sigma

private lemma aux_inv (k : ℕ) :
    1 ≤ 1 + 1 / (k : ℝ) ∧ 1 + 1 / (k : ℝ) ≤ 2 ∧ 1 + 1 / (k : ℝ) ∈ limitPointSet := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    refine ⟨by norm_num, by norm_num, ?_⟩
    exact Set.mem_union_left _ (by simp)
  · have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
    have h0 : (0:ℝ) < k := by linarith
    refine ⟨?_, ?_, ?_⟩
    · have : 0 ≤ 1 / (k:ℝ) := by positivity
      linarith
    · have : 1 / (k:ℝ) ≤ 1 := by rw [div_le_one h0]; exact hk1
      linarith
    · exact Set.mem_union_right _ ⟨k, by omega, rfl⟩

theorem erdos_42884_hyp_h_mem :
    ∀ m : ℕ, 1 ≤ largeFactorH m ∧ largeFactorH m ≤ 2 ∧ largeFactorH m ∈ limitPointSet := by
  intro m
  unfold largeFactorH
  split_ifs with h
  · exact aux_inv _
  · exact ⟨le_refl _, by norm_num, Set.mem_union_left _ (Set.mem_singleton 1)⟩
end erdos_42884_hyp_h_mem_ns

namespace erdos_42884_hyp_h_kP_ns
open Filter

open scoped ArithmeticFunction.sigma

theorem erdos_42884_hyp_h_kP :
    ∀ k P : ℕ, 1 ≤ k → k < P → P.Prime → largeFactorH (k * P) = 1 + 1 / (k : ℝ) := by
  intro k P hk hkP hP
  unfold largeFactorH
  have hex : ∃ Q : ℕ, Q.Prime ∧ Q ∣ k * P ∧ k * P < Q * Q :=
    ⟨P, hP, dvd_mul_left P k, by nlinarith [hP.two_le]⟩
  rw [dif_pos hex]
  obtain ⟨hQ, hQd, hQlt⟩ := Classical.choose_spec hex
  have hQP : Classical.choose hex = P := by
    by_contra hne
    have hdk : Classical.choose hex ∣ k := by
      rcases (Nat.Prime.dvd_mul hQ).mp hQd with h | h
      · exact h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hQ hP).mp h) hne
    have hQk : Classical.choose hex ≤ k := Nat.le_of_dvd (by omega) hdk
    nlinarith
  rw [hQP, Nat.mul_div_cancel k hP.pos]
end erdos_42884_hyp_h_kP_ns

namespace erdos_42884_hyp_h_sq_ns
open Filter

open scoped ArithmeticFunction.sigma

theorem erdos_42884_hyp_h_sq :
    ∀ q : ℕ, q.Prime → largeFactorH (q * q) = 1 := by
  intro q hq
  unfold largeFactorH
  split_ifs with h
  · exfalso
    obtain ⟨P, hP, hdvd, hlt⟩ := h
    have hPq : P ∣ q := ((Nat.Prime.dvd_mul hP).mp hdvd).elim id id
    have hEq : P = q := (Nat.prime_dvd_prime_iff_eq hP hq).mp hPq
    subst hEq
    exact lt_irrefl _ hlt
  · rfl
end erdos_42884_hyp_h_sq_ns

namespace erdos_42884_hyp_exp_tail_ns
open Filter

open scoped ArithmeticFunction.sigma

-- CHECK: Real.tendsto_sqrt_atTop Real.tendsto_exp_nhds_zero_nhds_one
theorem erdos_42884_hyp_exp_tail :
    Tendsto (fun n : ℕ => Real.exp (3 / Real.sqrt ((n : ℝ) + 1))) atTop (nhds 1) := by
  have h0 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ) + 1)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp h0
  have h2 : Tendsto (fun n : ℕ => 3 / Real.sqrt ((n : ℝ) + 1)) atTop (nhds 0) :=
    Tendsto.div_atTop tendsto_const_nhds h1
  exact Real.tendsto_exp_nhds_zero_nhds_one.comp h2
end erdos_42884_hyp_exp_tail_ns

namespace erdos_42884_hyp_closed_ns
open Filter

open scoped ArithmeticFunction.sigma

private lemma limitPointSet_eq :
    limitPointSet = insert (1:ℝ) (Set.range (fun n : ℕ => 1 + 1 / ((n:ℝ) + 1))) := by
  ext x
  simp only [limitPointSet, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq,
    Set.mem_insert_iff, Set.mem_range]
  constructor
  · rintro (h | ⟨k, hk, rfl⟩)
    · left; exact h
    · right
      refine ⟨k - 1, ?_⟩
      have hc : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by
        rw [Nat.cast_sub hk]; push_cast; ring
      rw [hc]
  · rintro (h | ⟨n, rfl⟩)
    · left; exact h
    · right
      exact ⟨n + 1, by omega, by push_cast; ring⟩

theorem erdos_42884_hyp_closed : IsClosed limitPointSet := by
  have ht : Tendsto (fun n : ℕ => 1 + 1 / ((n:ℝ) + 1)) atTop (nhds 1) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_add (1:ℝ)
    rw [add_zero] at this
    exact this
  rw [limitPointSet_eq]
  exact ht.isCompact_insert_range.isClosed
end erdos_42884_hyp_closed_ns

-- S2: from m! = m*(m-1)!, v_q(m!) = v_q((m-1)!) + v_q(m), and the divisor-count product formula
-- (ArithmeticFunction.sigma_zero_apply, Nat.card_divisors).
theorem erdos_42884_hyp_product_formula :
    ∀ m : ℕ, 2 ≤ m →
      (σ 0 m.factorial : ℝ) / (σ 0 (m - 1).factorial : ℝ)
        = ∏ q ∈ m.primeFactors,
            (1 + (m.factorization q : ℝ) / (((m - 1).factorial.factorization q : ℝ) + 1)) := by
  exact erdos_42884_hyp_product_formula_ns.erdos_42884_hyp_product_formula

-- S3: Legendre, first term: the multiples q, 2q, ..., (m/q - 1)q lie below m.
theorem erdos_42884_hyp_legendre_lower :
    ∀ m q : ℕ, 1 ≤ m → q.Prime → q ∣ m →
      m ≤ q * ((m - 1).factorial.factorization q + 1) := by
  exact erdos_42884_hyp_legendre_lower_ns.erdos_42884_hyp_legendre_lower

-- S4(a): two distinct such primes P, Q would give m ≥ P*Q ≥ min(P,Q)^2 > m.
theorem erdos_42884_hyp_large_prime_unique :
    ∀ m P Q : ℕ, m ≠ 0 → P.Prime → Q.Prime → P ∣ m → Q ∣ m →
      m < P * P → m < Q * Q → P = Q := by
  exact erdos_42884_hyp_large_prime_unique_ns.erdos_42884_hyp_large_prime_unique

-- S4(b): kP - 1 = (k-1)P + (P-1) < P^2, so only the multiples P, ..., (k-1)P count.
theorem erdos_42884_hyp_large_prime_val :
    ∀ k P : ℕ, 1 ≤ k → k < P → P.Prime →
      (k * P).factorization P = 1 ∧ (k * P - 1).factorial.factorization P = k - 1 := by
  exact erdos_42884_hyp_large_prime_val_ns.erdos_42884_hyp_large_prime_val

-- S5 step 1: list induction; x + y ≤ x*y for x, y ≥ 2 since (x-1)(y-1) ≥ 1 (empty list: 0 ≤ 1).
namespace erdos_42884_hyp_list_sum_le_prod_ns
open Filter

open scoped ArithmeticFunction.sigma

theorem erdos_42884_hyp_list_sum_le_prod :
    ∀ L : List ℕ, (∀ x ∈ L, 2 ≤ x) → L.sum ≤ L.prod := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons x L ih =>
    intro h
    have hx : 2 ≤ x := h x (by simp)
    have hL : ∀ y ∈ L, 2 ≤ y := fun y hy => h y (by simp [hy])
    have ih' := ih hL
    rw [List.sum_cons, List.prod_cons]
    rcases L with _ | ⟨y, L'⟩
    · simp
    · have hy : 2 ≤ y := hL y (by simp)
      have hs : 2 ≤ (y :: L').sum := by
        rw [List.sum_cons]; omega
      have hp : 2 ≤ (y :: L').prod := le_trans hs ih'
      nlinarith
end erdos_42884_hyp_list_sum_le_prod_ns

theorem erdos_42884_hyp_list_sum_le_prod :
    ∀ L : List ℕ, (∀ x ∈ L, 2 ≤ x) → L.sum ≤ L.prod := by
  exact erdos_42884_hyp_list_sum_le_prod_ns.erdos_42884_hyp_list_sum_le_prod



-- S5 (invariant form): induction on L = x :: L', P = prod L'.
-- If P ≥ 2s: IH and s*x ≤ (x-1)*P (since x ≥ 2). If P < 2s: sum L' ≤ P (list_sum_le_prod) and
-- 2s² + xP - sx - sP = s² + (s-x)(s-P) > 0 because 0 ≤ s-x < s and |s-P| < s.
namespace erdos_42884_hyp_block_invariant_ns
open Filter

open scoped ArithmeticFunction.sigma

private lemma aux_sum_prod (L : List ℕ) (h : ∀ x ∈ L, 2 ≤ x) :
    L.sum ≤ L.prod ∧ L.sum + 2 ≤ 2 * L.prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ha : 2 ≤ a := h a (by simp)
    obtain ⟨h1, h2⟩ := ih (fun x hx => h x (by simp [hx]))
    have hP : 1 ≤ L.prod := by omega
    rw [List.sum_cons, List.prod_cons]
    constructor
    · nlinarith [Nat.mul_le_mul (Nat.sub_le_sub_right ha 2) (Nat.sub_le_sub_right hP 1)]
    · nlinarith [Nat.mul_le_mul (Nat.sub_le_sub_right ha 2) (Nat.sub_le_sub_right hP 1)]

private lemma main_aux (s : ℝ) (hs : 0 < s) : ∀ L : List ℕ,
    (∀ x ∈ L, 2 ≤ x ∧ (x : ℝ) ≤ s) →
      s * ((L.sum : ℕ) : ℝ) ≤ ((L.prod : ℕ) : ℝ) + 2 * s ^ 2 := by
  intro L
  induction L with
  | nil =>
    intro _
    simp only [List.sum_nil, List.prod_nil, Nat.cast_zero, Nat.cast_one, mul_zero]
    positivity
  | cons a L ih =>
    intro hL
    have ha := hL a (by simp)
    have hL' : ∀ x ∈ L, 2 ≤ x ∧ (x : ℝ) ≤ s := fun x hx => hL x (by simp [hx])
    have ih' := ih hL'
    obtain ⟨h1, _⟩ := aux_sum_prod L (fun x hx => (hL' x hx).1)
    have h1r : ((L.sum : ℕ) : ℝ) ≤ ((L.prod : ℕ) : ℝ) := by exact_mod_cast h1
    have ha2 : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha.1
    have has : (a : ℝ) ≤ s := ha.2
    rw [List.sum_cons, List.prod_cons, Nat.cast_add, Nat.cast_mul]
    rcases le_total (2 * s) ((L.prod : ℕ) : ℝ) with hP | hP
    · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (a:ℝ) - 1) (sub_nonneg.2 hP),
        mul_nonneg (sub_nonneg.2 ha2) hs.le]
    · nlinarith [mul_le_mul_of_nonneg_left h1r hs.le,
        mul_nonneg (sub_nonneg.2 has) (sub_nonneg.2 hP),
        mul_nonneg hs.le (by linarith : (0:ℝ) ≤ (a:ℝ))]

theorem erdos_42884_hyp_block_invariant :
    ∀ (s : ℝ) (L : List ℕ), 0 < s → (∀ x ∈ L, 2 ≤ x ∧ (x : ℝ) ≤ s) →
      s * ((L.sum : ℕ) : ℝ) ≤ ((L.prod : ℕ) : ℝ) + 2 * s ^ 2 := by
  intro s L hs hL
  exact main_aux s hs L hL
end erdos_42884_hyp_block_invariant_ns

theorem erdos_42884_hyp_block_invariant :
    ∀ (s : ℝ) (L : List ℕ), 0 < s → (∀ x ∈ L, 2 ≤ x ∧ (x : ℝ) ≤ s) →
      s * ((L.sum : ℕ) : ℝ) ≤ ((L.prod : ℕ) : ℝ) + 2 * s ^ 2 := by
  exact erdos_42884_hyp_block_invariant_ns.erdos_42884_hyp_block_invariant



-- S5: derived from the invariant, using prod ≤ s².
theorem erdos_42884_hyp_three_blocks :
    ∀ (s : ℝ) (L : List ℕ), 0 < s → (∀ x ∈ L, 2 ≤ x ∧ (x : ℝ) ≤ s) →
      ((L.prod : ℕ) : ℝ) ≤ s ^ 2 → ((L.sum : ℕ) : ℝ) ≤ 3 * s := by
  intro s L hs hL hprod
  have hinv := erdos_42884_hyp_block_invariant s L hs hL
  have h3 : s * ((L.sum : ℕ) : ℝ) ≤ s * (3 * s) := by nlinarith
  exact le_of_mul_le_mul_left h3 hs

-- S6 steps 1-3: apply three_blocks with s = √m to the list of prime factors q with q*q ≤ m,
-- each repeated v_q(m) times; its product divides m, so it is ≤ m = s². (m = 1: empty sum.)
namespace erdos_42884_hyp_small_prime_sum_ns
open Filter

open scoped ArithmeticFunction.sigma

private lemma e42884_step (s S P y : ℝ) (hs : 0 < s) (hy2 : 2 ≤ y) (hys : y ≤ s)
    (h : (S = 0 ∧ P = 1) ∨ (S ≤ P ∧ S * s ≤ 2 * s * s + P ∧ 2 ≤ P)) :
    S + y ≤ P * y ∧ (S + y) * s ≤ 2 * s * s + P * y ∧ 2 ≤ P * y := by
  rcases h with ⟨hS, hP1⟩ | ⟨h1, h2, h3⟩
  · subst hS; subst hP1
    have k1 : y * s ≤ s * s := mul_le_mul_of_nonneg_right hys hs.le
    have k2 : 0 ≤ s * s := by positivity
    refine ⟨by linarith, by nlinarith, by linarith⟩
  · have k0 : 0 ≤ (P - 2) * (y - 2) := mul_nonneg (by linarith) (by linarith)
    have hA : S + y ≤ P * y := by nlinarith
    have hB : 2 ≤ P * y := by nlinarith
    refine ⟨hA, ?_, hB⟩
    rcases le_or_gt (s * y) (P * (y - 1)) with hc | hc
    · nlinarith
    · have hP : P ≤ 2 * s := by
        by_contra hcon'
        have hcon : 2 * s < P := not_le.mp hcon'
        have k4 : 0 ≤ (P - 2 * s) * (y - 2) := mul_nonneg (by linarith) (by linarith)
        have k5 : 0 < (P - 2 * s) * y := mul_pos (by linarith) (by linarith)
        nlinarith
      have k5 : P * (s - y) ≤ 2 * s * (s - y) :=
        mul_le_mul_of_nonneg_right hP (by linarith)
      have k6 : S * s ≤ P * s := mul_le_mul_of_nonneg_right h1 hs.le
      nlinarith

private lemma e42884_pow_step (s S P y : ℝ) (hs : 0 < s) (hy2 : 2 ≤ y) (hys : y ≤ s) (a : ℕ)
    (h : (S = 0 ∧ P = 1) ∨ (S ≤ P ∧ S * s ≤ 2 * s * s + P ∧ 2 ≤ P)) :
    (S + (a : ℝ) * y = 0 ∧ P * y ^ a = 1) ∨
      (S + (a : ℝ) * y ≤ P * y ^ a ∧ (S + (a : ℝ) * y) * s ≤ 2 * s * s + P * y ^ a ∧
        2 ≤ P * y ^ a) := by
  induction a with
  | zero => simpa using h
  | succ n ih =>
    right
    have e1 : S + ((n + 1 : ℕ) : ℝ) * y = (S + (n : ℝ) * y) + y := by push_cast; ring
    have e2 : P * y ^ (n + 1) = (P * y ^ n) * y := by ring
    rw [e1, e2]
    exact e42884_step s _ _ y hs hy2 hys ih

private lemma e42884_fin_inv (s : ℝ) (hs : 0 < s) (f : ℕ → ℕ) (T : Finset ℕ) :
    (∀ q ∈ T, 2 ≤ (q : ℝ) ∧ (q : ℝ) ≤ s) →
    (((∑ q ∈ T, (f q : ℝ) * (q : ℝ)) = 0 ∧ (∏ q ∈ T, (q : ℝ) ^ (f q)) = 1) ∨
      ((∑ q ∈ T, (f q : ℝ) * (q : ℝ)) ≤ ∏ q ∈ T, (q : ℝ) ^ (f q) ∧
        (∑ q ∈ T, (f q : ℝ) * (q : ℝ)) * s ≤ 2 * s * s + ∏ q ∈ T, (q : ℝ) ^ (f q) ∧
        2 ≤ ∏ q ∈ T, (q : ℝ) ^ (f q))) := by
  refine Finset.induction_on T ?_ ?_
  · intro _
    left
    simp
  · intro a T ha ih hT
    have hT' : ∀ q ∈ T, 2 ≤ (q : ℝ) ∧ (q : ℝ) ≤ s :=
      fun q hq => hT q (Finset.mem_insert_of_mem hq)
    have ha' := hT a (Finset.mem_insert_self a T)
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have := e42884_pow_step s _ _ (a : ℝ) hs ha'.1 ha'.2 (f a) (ih hT')
    rw [add_comm ((f a : ℝ) * (a : ℝ)), mul_comm ((a : ℝ) ^ (f a))]
    exact this

theorem erdos_42884_hyp_small_prime_sum :
    ∀ m : ℕ, 1 ≤ m →
      ∑ q ∈ Finset.filter (fun q => q * q ≤ m) m.primeFactors,
          (m.factorization q : ℝ) * (q : ℝ) ≤ 3 * Real.sqrt (m : ℝ) := by
  intro m hm
  set T := Finset.filter (fun q => q * q ≤ m) m.primeFactors with hTdef
  have hm0 : 0 < m := hm
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm0
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm'
  have hss : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm'.le
  have hT : ∀ q ∈ T, 2 ≤ (q : ℝ) ∧ (q : ℝ) ≤ Real.sqrt m := by
    intro q hq
    rw [hTdef, Finset.mem_filter] at hq
    have hp : q.Prime := Nat.prime_of_mem_primeFactors hq.1
    refine ⟨by exact_mod_cast hp.two_le, ?_⟩
    have h1 : ((q : ℝ) * q) ≤ (m : ℝ) := by exact_mod_cast hq.2
    have h2 := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_mul_self (Nat.cast_nonneg q)] at h2
  have hP : (∏ q ∈ T, (q : ℝ) ^ (m.factorization q)) ≤ m := by
    have h1 : (∏ q ∈ T, q ^ (m.factorization q)) ≤ m := by
      calc (∏ q ∈ T, q ^ (m.factorization q))
            ≤ ∏ q ∈ m.primeFactors, q ^ (m.factorization q) :=
            Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _)
              (fun q hq _ => Nat.one_le_pow _ _ (Nat.prime_of_mem_primeFactors hq).pos)
        _ = m := by
          have := Nat.prod_factorization_pow_eq_self (Nat.pos_iff_ne_zero.mp hm0)
          rw [Finsupp.prod, Nat.support_factorization] at this
          exact this
    exact_mod_cast h1
  rcases e42884_fin_inv (Real.sqrt m) hs (⇑m.factorization) T hT with ⟨h0, _⟩ | ⟨_, h2, _⟩
  · rw [h0]; positivity
  · nlinarith
end erdos_42884_hyp_small_prime_sum_ns

theorem erdos_42884_hyp_small_prime_sum :
    ∀ m : ℕ, 1 ≤ m →
      ∑ q ∈ Finset.filter (fun q => q * q ≤ m) m.primeFactors,
          (m.factorization q : ℝ) * (q : ℝ) ≤ 3 * Real.sqrt (m : ℝ) := by
  exact erdos_42884_hyp_small_prime_sum_ns.erdos_42884_hyp_small_prime_sum



theorem erdos_42884_small_prime_product_le :
    ∀ m : ℕ, 1 ≤ m → smallPrimeProduct m ≤ Real.exp (3 / Real.sqrt (m : ℝ)) := by
  intro m hm
  have hm' : 0 < m := by omega
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm'
  have hsq : 0 < Real.sqrt (m:ℝ) := Real.sqrt_pos.mpr hm0
  have hsum := erdos_42884_hyp_small_prime_sum m hm
  unfold smallPrimeProduct
  calc _ ≤ ∏ q ∈ Finset.filter (fun q => q * q ≤ m) m.primeFactors,
          Real.exp ((m.factorization q : ℝ) * (q : ℝ) / (m : ℝ)) := by
        apply Finset.prod_le_prod
        · intro q _
          positivity
        · intro q hq
          have hqF := (Finset.mem_filter.mp hq).1
          have hqp : q.Prime := Nat.prime_of_mem_primeFactors hqF
          have hqd : q ∣ m := Nat.dvd_of_mem_primeFactors hqF
          have hL := erdos_42884_hyp_legendre_lower m q hm hqp hqd
          have hL' : (m:ℝ) ≤ (q:ℝ) * (((m - 1).factorial.factorization q : ℝ) + 1) := by
            exact_mod_cast hL
          have ha : (0:ℝ) ≤ (m.factorization q : ℝ) := Nat.cast_nonneg _
          have hv : (0:ℝ) < ((m - 1).factorial.factorization q : ℝ) + 1 := by positivity
          have hdiv : (m.factorization q : ℝ) / (((m - 1).factorial.factorization q : ℝ) + 1)
              ≤ (m.factorization q : ℝ) * (q : ℝ) / (m : ℝ) := by
            rw [div_le_div_iff₀ hv hm0]
            nlinarith [mul_le_mul_of_nonneg_left hL' ha]
          have he := Real.add_one_le_exp ((m.factorization q : ℝ) * (q : ℝ) / (m : ℝ))
          linarith
    _ = Real.exp (∑ q ∈ Finset.filter (fun q => q * q ≤ m) m.primeFactors,
          (m.factorization q : ℝ) * (q : ℝ) / (m : ℝ)) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (3 / Real.sqrt (m : ℝ)) := by
        apply Real.exp_le_exp.mpr
        rw [← Finset.sum_div, div_le_div_iff₀ hm0 hsq]
        have hmm := Real.mul_self_sqrt (le_of_lt hm0)
        nlinarith [mul_le_mul_of_nonneg_right hsum (le_of_lt hsq)]

-- S6 (old statement, now derived).
theorem erdos_42884_hyp_small_prime_product :
    ∀ m : ℕ, 2 ≤ m →
      ∏ q ∈ Finset.filter (fun q => q * q ≤ m) m.primeFactors,
          (1 + (m.factorization q : ℝ) / (((m - 1).factorial.factorization q : ℝ) + 1))
        ≤ Real.exp (3 / Real.sqrt (m : ℝ)) := by
  intro m hm
  exact erdos_42884_small_prime_product_le m (by omega)

theorem erdos_42884_small_prime_product_one_le : ∀ m : ℕ, 1 ≤ smallPrimeProduct m := by
  intro m
  unfold smallPrimeProduct
  calc (1:ℝ) = ∏ q ∈ Finset.filter (fun q => q * q ≤ m) m.primeFactors, (1:ℝ) :=
        Finset.prod_const_one.symm
    _ ≤ _ := by
      apply Finset.prod_le_prod
      · intro q _
        exact zero_le_one
      · intro q _
        have : (0:ℝ) ≤ (m.factorization q : ℝ) / (((m - 1).factorial.factorization q : ℝ) + 1) := by
          positivity
        linarith

-- S7 core (S2 + S4): by product_formula, split primeFactors(n+1) into {q : q*q ≤ n+1} and the
-- complement; by large_prime_unique the complement is ∅ or {P}, and by large_prime_val the
-- P-factor is 1 + 1/k = largeFactorH (n+1). n = 0: F 0 = 1, largeFactorH 1 = 1, empty product.
namespace erdos_42884_hyp_split_ns
open Filter

open scoped ArithmeticFunction.sigma

-- S2: (n+1)! = (n+1) * n!, so v_q((n+1)!) = v_q(n!) + v_q(n+1); tau(N) = prod (v_q(N)+1)
-- (Nat.card_divisors); the ratio telescopes to prod_{q | n+1} (1 + a_q/(v_q+1)).
-- Primes not dividing n+1 contribute factor 1.  n = 0 gives 1 = empty product.
namespace erdos_42884_hyp_split_hyp_prod_formula_ns

-- CHECK: Nat.card_divisors ArithmeticFunction.sigma_zero_apply Nat.primeFactors_mul Nat.support_factorization
open Filter

open scoped ArithmeticFunction.sigma

theorem erdos_42884_hyp_split_hyp_prod_formula :
    ∀ n : ℕ, factorialDivisorRatio n =
      ∏ q ∈ (n + 1).primeFactors,
        (1 + ((n + 1).factorization q : ℝ) / ((n.factorial.factorization q : ℝ) + 1)) := by
  intro n
  unfold factorialDivisorRatio
  have hn0 : n.factorial ≠ 0 := Nat.factorial_ne_zero n
  have hn1 : n + 1 ≠ 0 := Nat.succ_ne_zero n
  have hfac : (n+1).factorial = (n+1) * n.factorial := Nat.factorial_succ n
  have hF : (n+1).factorial.factorization = (n+1).factorization + n.factorial.factorization := by
    rw [hfac, Nat.factorization_mul hn1 hn0]
  have hS : (n+1).factorial.primeFactors = (n+1).primeFactors ∪ n.factorial.primeFactors := by
    rw [hfac, Nat.primeFactors_mul hn1 hn0]
  have hz : ∀ m p : ℕ, p ∉ m.primeFactors → m.factorization p = 0 := by
    intro m p hp
    by_contra h
    exact hp (by rw [← Nat.support_factorization, Finsupp.mem_support_iff]; exact h)
  have hA : (σ 0 (n+1).factorial : ℝ) = ∏ p ∈ (n+1).factorial.primeFactors,
      (((n+1).factorization p : ℝ) + (n.factorial.factorization p : ℝ) + 1) := by
    rw [ArithmeticFunction.sigma_zero_apply, Nat.card_divisors (Nat.factorial_ne_zero _)]
    push_cast
    refine Finset.prod_congr rfl (fun p _ => ?_)
    simp only [hF, Finsupp.coe_add, Pi.add_apply]
    push_cast
    ring
  have hB : (σ 0 n.factorial : ℝ) = ∏ p ∈ (n+1).factorial.primeFactors,
      ((n.factorial.factorization p : ℝ) + 1) := by
    rw [ArithmeticFunction.sigma_zero_apply, Nat.card_divisors hn0]
    push_cast
    apply Finset.prod_subset
    · rw [hS]; exact Finset.subset_union_right
    · intro p _ hp
      rw [hz _ _ hp]
      simp
  have hC : ∏ q ∈ (n + 1).primeFactors,
        (1 + ((n + 1).factorization q : ℝ) / ((n.factorial.factorization q : ℝ) + 1))
      = ∏ q ∈ (n + 1).factorial.primeFactors,
        (1 + ((n + 1).factorization q : ℝ) / ((n.factorial.factorization q : ℝ) + 1)) := by
    apply Finset.prod_subset
    · rw [hS]; exact Finset.subset_union_left
    · intro p _ hp
      rw [hz _ _ hp]
      simp
  have hBpos : (0 : ℝ) < ∏ p ∈ (n+1).factorial.primeFactors,
      ((n.factorial.factorization p : ℝ) + 1) :=
    Finset.prod_pos (fun p _ => by positivity)
  rw [hA, hB, hC, div_eq_iff hBpos.ne', ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun p _ => ?_)
  have hne : ((n.factorial.factorization p : ℝ) + 1) ≠ 0 := by positivity
  rw [add_mul, div_mul_cancel₀ _ hne]
  ring

end erdos_42884_hyp_split_hyp_prod_formula_ns

theorem erdos_42884_hyp_split_hyp_prod_formula :
    ∀ n : ℕ, factorialDivisorRatio n =
      ∏ q ∈ (n + 1).primeFactors,
        (1 + ((n + 1).factorization q : ℝ) / ((n.factorial.factorization q : ℝ) + 1)) := by
  exact erdos_42884_hyp_split_hyp_prod_formula_ns.erdos_42884_hyp_split_hyp_prod_formula

-- S7.2–S7.4 (uses S4): at most one prime P | m with P*P > m; for it a_P = 1 and
-- v_P((m-1)!) = m/P - 1 (Legendre, since m-1 < P^2), so its factor is 1 + 1/(m/P),
-- which equals largeFactorH m (the Classical.choose witness is forced to be P).
-- No such prime: empty product = 1 = largeFactorH.  Edge m = 1 (n = 0): both sides 1.
namespace erdos_42884_hyp_split_hyp_large_prod_ns

-- CHECK: padicValNat_factorial Nat.factorization_def Nat.log_lt_of_lt_pow Nat.succ_div_of_dvd Nat.Prime.pow_dvd_iff_le_factorization
open Filter

open scoped ArithmeticFunction.sigma

theorem erdos_42884_hyp_split_hyp_large_prod :
    ∀ n : ℕ,
      ∏ q ∈ Finset.filter (fun q => ¬ q * q ≤ n + 1) (n + 1).primeFactors,
        (1 + ((n + 1).factorization q : ℝ) / ((n.factorial.factorization q : ℝ) + 1))
      = largeFactorH (n + 1) := by
  intro n
  by_cases h : ∃ P : ℕ, P.Prime ∧ P ∣ n + 1 ∧ n + 1 < P * P
  · have h' := h
    obtain ⟨P, hP, hPd, hPl⟩ := h'
    have huniq : ∀ Q : ℕ, Q.Prime → Q ∣ n + 1 → n + 1 < Q * Q → Q = P := by
      intro Q hQ hQd hQl
      by_contra hne
      have hcop : Nat.Coprime Q P := (Nat.coprime_primes hQ hP).mpr hne
      have hdvd : Q * P ∣ n + 1 := hcop.mul_dvd_of_dvd_of_dvd hQd hPd
      have hle : Q * P ≤ n + 1 := Nat.le_of_dvd (Nat.succ_pos n) hdvd
      have h1 : (n + 1) * (n + 1) < (Q * Q) * (P * P) :=
        mul_lt_mul'' hQl hPl (Nat.zero_le _) (Nat.zero_le _)
      have h2 : (Q * P) * (Q * P) ≤ (n + 1) * (n + 1) := Nat.mul_le_mul hle hle
      have h3 : (Q * Q) * (P * P) = (Q * P) * (Q * P) := by ring
      rw [h3] at h1
      exact absurd h2 (not_le.mpr h1)
    have hS : Finset.filter (fun q => ¬ q * q ≤ n + 1) (n + 1).primeFactors = {P} := by
      ext q
      simp only [Finset.mem_filter, Nat.mem_primeFactors, Finset.mem_singleton, not_le]
      constructor
      · rintro ⟨⟨hq, hqd, -⟩, hql⟩
        exact huniq q hq hqd hql
      · rintro rfl
        exact ⟨⟨hP, hPd, Nat.succ_ne_zero n⟩, hPl⟩
    rw [hS, Finset.prod_singleton]
    unfold largeFactorH
    rw [dif_pos h]
    have hc := Classical.choose_spec h
    have hcP : Classical.choose h = P := huniq _ hc.1 hc.2.1 hc.2.2
    rw [hcP]
    have hP2 := hP.two_le
    have hPle : P ≤ n + 1 := Nat.le_of_dvd (Nat.succ_pos n) hPd
    have hv1 : (n + 1).factorization P = 1 := by
      have hge : 1 ≤ (n + 1).factorization P :=
        (hP.pow_dvd_iff_le_factorization (Nat.succ_ne_zero n)).mp (by rwa [pow_one])
      have hlt : ¬ 2 ≤ (n + 1).factorization P := by
        intro h2
        have hd := (hP.pow_dvd_iff_le_factorization (Nat.succ_ne_zero n)).mpr h2
        have := Nat.le_of_dvd (Nat.succ_pos n) hd
        rw [pow_two] at this
        omega
      omega
    have hv2 : n.factorial.factorization P = n / P := by
      haveI := Fact.mk hP
      rw [Nat.factorization_def _ hP]
      rw [padicValNat_factorial (b := 2) (Nat.log_lt_of_lt_pow (by omega) (by rw [pow_two]; omega))]
      rw [show Finset.Ico 1 2 = {1} from by decide, Finset.sum_singleton, pow_one]
    have hdiv : (n + 1) / P = n / P + 1 := Nat.succ_div_of_dvd hPd
    rw [hv1, hv2, hdiv]
    simp only [Nat.cast_add, Nat.cast_one]
  · have hS : Finset.filter (fun q => ¬ q * q ≤ n + 1) (n + 1).primeFactors = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro q hq hql
      rw [Nat.mem_primeFactors] at hq
      exact h ⟨q, hq.1, hq.2.1, not_le.mp hql⟩
    rw [hS, Finset.prod_empty]
    unfold largeFactorH
    rw [dif_neg h]

end erdos_42884_hyp_split_hyp_large_prod_ns

theorem erdos_42884_hyp_split_hyp_large_prod :
    ∀ n : ℕ,
      ∏ q ∈ Finset.filter (fun q => ¬ q * q ≤ n + 1) (n + 1).primeFactors,
        (1 + ((n + 1).factorization q : ℝ) / ((n.factorial.factorization q : ℝ) + 1))
      = largeFactorH (n + 1) := by
  exact erdos_42884_hyp_split_hyp_large_prod_ns.erdos_42884_hyp_split_hyp_large_prod

theorem erdos_42884_hyp_split :
    ∀ n : ℕ, factorialDivisorRatio n = largeFactorH (n + 1) * smallPrimeProduct (n + 1) := by
  intro n
  rw [erdos_42884_hyp_split_hyp_prod_formula n, ← erdos_42884_hyp_split_hyp_large_prod n]
  unfold smallPrimeProduct
  rw [Nat.add_sub_cancel, mul_comm]
  first
  | exact (Finset.prod_filter_mul_prod_filter_not _ _ _).symm
  | exact (Finset.prod_filter_mul_prod_filter_not ((n + 1).primeFactors)
      (fun q => q * q ≤ n + 1) _).symm
end erdos_42884_hyp_split_ns

theorem erdos_42884_hyp_split :
    ∀ n : ℕ, factorialDivisorRatio n = largeFactorH (n + 1) * smallPrimeProduct (n + 1) := by
  exact erdos_42884_hyp_split_ns.erdos_42884_hyp_split



-- S7 (last clause): h takes values 1 or 1 + 1/k with k ≥ 1 (note 1/0 = 0 in Lean at m = 0).
theorem erdos_42884_hyp_h_mem :
    ∀ m : ℕ, 1 ≤ largeFactorH m ∧ largeFactorH m ≤ 2 ∧ largeFactorH m ∈ limitPointSet := by
  exact erdos_42884_hyp_h_mem_ns.erdos_42884_hyp_h_mem

-- S7: derived from split, h_mem and the two bounds on smallPrimeProduct.
theorem erdos_42884_hyp_sandwich :
    ∀ n : ℕ, largeFactorH (n + 1) ≤ factorialDivisorRatio n ∧
      factorialDivisorRatio n ≤ largeFactorH (n + 1) * Real.exp (3 / Real.sqrt ((n : ℝ) + 1)) := by
  intro n
  have hsplit := erdos_42884_hyp_split n
  obtain ⟨hh1, _, _⟩ := erdos_42884_hyp_h_mem (n + 1)
  have hlo := erdos_42884_small_prime_product_one_le (n + 1)
  have hhi := erdos_42884_small_prime_product_le (n + 1) (by omega)
  push_cast at hhi
  rw [hsplit]
  have hh0 : (0:ℝ) ≤ largeFactorH (n + 1) := by linarith
  constructor
  · have h := mul_le_mul_of_nonneg_left hlo hh0
    rw [mul_one] at h
    exact h
  · exact mul_le_mul_of_nonneg_left hhi hh0

-- S4 + S11 step 2: P is the unique prime with P | kP and P^2 > kP, and kP / P = k.
theorem erdos_42884_hyp_h_kP :
    ∀ k P : ℕ, 1 ≤ k → k < P → P.Prime → largeFactorH (k * P) = 1 + 1 / (k : ℝ) := by
  exact erdos_42884_hyp_h_kP_ns.erdos_42884_hyp_h_kP

-- S12 step 1: the only prime factor of q*q is q, and q*q < q*q fails.
theorem erdos_42884_hyp_h_sq :
    ∀ q : ℕ, q.Prime → largeFactorH (q * q) = 1 := by
  exact erdos_42884_hyp_h_sq_ns.erdos_42884_hyp_h_sq

-- S8 (analytic tail): 3/√(n+1) → 0 and exp is continuous at 0.
theorem erdos_42884_hyp_exp_tail :
    Tendsto (fun n : ℕ => Real.exp (3 / Real.sqrt ((n : ℝ) + 1))) atTop (nhds 1) := by
  exact erdos_42884_hyp_exp_tail_ns.erdos_42884_hyp_exp_tail

-- S9: the only accumulation point of S is 1, which lies in S.
theorem erdos_42884_hyp_closed : IsClosed limitPointSet := by
  exact erdos_42884_hyp_closed_ns.erdos_42884_hyp_closed

theorem erdos_42884 :
    {x : ℝ | MapClusterPt x atTop factorialDivisorRatio} = limitPointSet := by
  have happrox : Tendsto (fun n : ℕ => factorialDivisorRatio n - largeFactorH (n + 1))
      atTop (nhds 0) := by
    have hup : Tendsto (fun n : ℕ => 2 * (Real.exp (3 / Real.sqrt ((n : ℝ) + 1)) - 1))
        atTop (nhds 0) := by
      have h := (erdos_42884_hyp_exp_tail.sub_const 1).const_mul 2
      rw [sub_self, mul_zero] at h
      exact h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun n => ?_) (fun n => ?_)
    · obtain ⟨hlo, _⟩ := erdos_42884_hyp_sandwich n
      show (0 : ℝ) ≤ factorialDivisorRatio n - largeFactorH (n + 1)
      linarith
    · obtain ⟨_, hhi⟩ := erdos_42884_hyp_sandwich n
      obtain ⟨_, h2, _⟩ := erdos_42884_hyp_h_mem (n + 1)
      have he : 1 ≤ Real.exp (3 / Real.sqrt ((n : ℝ) + 1)) := Real.one_le_exp (by positivity)
      have key : largeFactorH (n + 1) * (Real.exp (3 / Real.sqrt ((n : ℝ) + 1)) - 1)
          ≤ 2 * (Real.exp (3 / Real.sqrt ((n : ℝ) + 1)) - 1) :=
        mul_le_mul_of_nonneg_right h2 (by linarith)
      have hexpand : largeFactorH (n + 1) * (Real.exp (3 / Real.sqrt ((n : ℝ) + 1)) - 1)
          = largeFactorH (n + 1) * Real.exp (3 / Real.sqrt ((n : ℝ) + 1)) - largeFactorH (n + 1) := by
        ring
      show factorialDivisorRatio n - largeFactorH (n + 1)
          ≤ 2 * (Real.exp (3 / Real.sqrt ((n : ℝ) + 1)) - 1)
      linarith
  have hclust : ∀ y : ℝ,
      (∀ ε > 0, ∀ N : ℕ, ∃ n ≥ N, |factorialDivisorRatio n - y| < ε) →
        MapClusterPt y atTop factorialDivisorRatio := by
    intro y hy
    rw [mapClusterPt_iff_frequently]
    intro s hs
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hs
    rw [Filter.frequently_atTop]
    intro N
    obtain ⟨n, hn, hlt⟩ := hy ε hε N
    exact ⟨n, hn, hsub (by rw [Metric.mem_ball, Real.dist_eq]; exact hlt)⟩
  refine Set.ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · have hx' : MapClusterPt x atTop factorialDivisorRatio := hx
    by_contra hxS
    obtain ⟨δ, hδ, hball⟩ :=
      Metric.isOpen_iff.mp erdos_42884_hyp_closed.isOpen_compl x hxS
    have hfreq := mapClusterPt_iff_frequently.mp hx' (Metric.ball x (δ / 2))
      (Metric.ball_mem_nhds x (half_pos hδ))
    have hev := happrox.eventually_mem (Metric.ball_mem_nhds (0 : ℝ) (half_pos hδ))
    obtain ⟨n, hn1, hn2⟩ := (hfreq.and_eventually hev).exists
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt] at hn1 hn2
    have hin : largeFactorH (n + 1) ∈ Metric.ball x δ := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hn1.1, hn1.2, hn2.1, hn2.2]
    exact hball hin (erdos_42884_hyp_h_mem (n + 1)).2.2
  · show MapClusterPt x atTop factorialDivisorRatio
    simp only [limitPointSet, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq] at hx
    rcases hx with hx | ⟨k, hk, rfl⟩
    · subst hx
      apply hclust
      intro ε hε N
      obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.mp happrox ε hε
      obtain ⟨q, hq, hqp⟩ := Nat.exists_infinite_primes (N + N0 + 2)
      have hval := erdos_42884_hyp_h_sq q hqp
      have hqq : q ≤ q * q := by
        have := Nat.mul_le_mul (le_refl q) (show 1 ≤ q by omega)
        rw [mul_one] at this
        exact this
      generalize hm : q * q = m at hqq hval
      refine ⟨m - 1, by omega, ?_⟩
      have h1 : m - 1 + 1 = m := by omega
      have hd := hN0 (m - 1) (by omega)
      simp only [Real.dist_eq, sub_zero] at hd
      rw [h1, hval] at hd
      exact hd
    · apply hclust
      intro ε hε N
      obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.mp happrox ε hε
      obtain ⟨p, hp, hpp⟩ := Nat.exists_infinite_primes (N + N0 + k + 2)
      have hval := erdos_42884_hyp_h_kP k p hk (by omega) hpp
      have hpkp : p ≤ k * p := by
        have := Nat.mul_le_mul hk (le_refl p)
        rw [one_mul] at this
        exact this
      generalize hm : k * p = m at hpkp hval
      refine ⟨m - 1, by omega, ?_⟩
      have h1 : m - 1 + 1 = m := by omega
      have hd := hN0 (m - 1) (by omega)
      simp only [Real.dist_eq, sub_zero] at hd
      rw [h1, hval] at hd
      exact hd
