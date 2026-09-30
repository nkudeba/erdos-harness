import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.Bertrand

set_option maxHeartbeats 1000000
set_option autoImplicit false

def erdos_28730_L (k : ℕ) : ℕ := (Finset.Icc 1 k).lcm id

def erdos_28730_Admissible (k p : ℕ) : Prop :=
  p.Prime ∧ k < p ^ 2 ∧ p ≤ k ∧ ¬ p ∣ k ∧ ¬ p ∣ (k + 1)

def erdos_28730_blockProd (a l : ℕ) : ℕ := ∏ i ∈ Finset.Ioc a (a + l), i

def erdos_28730_loss (a l : ℕ) : ℕ :=
  erdos_28730_blockProd a l / (Finset.Ioc a (a + l)).lcm id

namespace erdos_28730_hyp_prime_ns
open Asymptotics Filter Finset

private lemma erdos_28730_mul_le_of_two_primes {r s N : ℕ} (hr : r.Prime) (hs : s.Prime)
    (hne : r ≠ s) (hN : 0 < N) (h1 : r ∣ N) (h2 : s ∣ N) : r * s ≤ N :=
  Nat.le_of_dvd hN (Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes hr hs).mpr hne) h1 h2)

theorem erdos_28730_hyp_prime :
    ∀ k : ℕ, 400 ≤ k → ∃ p, erdos_28730_Admissible k p := by
  intro k hk
  obtain ⟨p1, hp1, h1a, h1b⟩ := Nat.exists_prime_lt_and_le_two_mul (k / 2) (by omega)
  obtain ⟨p2, hp2, h2a, h2b⟩ := Nat.exists_prime_lt_and_le_two_mul (k / 4) (by omega)
  obtain ⟨p3, hp3, h3a, h3b⟩ := Nat.exists_prime_lt_and_le_two_mul (k / 8) (by omega)
  have key : ∀ p, p.Prime → k / 8 < p → p ≤ k →
      (p ∣ k ∨ p ∣ k + 1) ∨ erdos_28730_Admissible k p := by
    intro p hp ha hb
    by_cases h : p ∣ k ∨ p ∣ k + 1
    · left; exact h
    · right
      push_neg at h
      refine ⟨hp, ?_, hb, h.1, h.2⟩
      have h8 : k < 8 * p := by omega
      have hp8 : 8 ≤ p := by omega
      nlinarith
  have contra : ∀ r s N, r.Prime → s.Prime → r ≠ s → k / 8 < r → k / 8 < s →
      N ≤ k + 1 → 0 < N → r ∣ N → s ∣ N → False := by
    intro r s N hr hs hne hr8 hs8 hN hN0 hrN hsN
    have hmul := erdos_28730_mul_le_of_two_primes hr hs hne hN0 hrN hsN
    have a : k + 1 ≤ 8 * r := by omega
    have b : k + 1 ≤ 8 * s := by omega
    have hab : (k + 1) * (k + 1) ≤ (8 * r) * (8 * s) := Nat.mul_le_mul a b
    nlinarith
  rcases key p1 hp1 (by omega) (by omega) with h1 | h1
  · rcases key p2 hp2 (by omega) (by omega) with h2 | h2
    · rcases key p3 hp3 (by omega) (by omega) with h3 | h3
      · exfalso
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
        first
          | exact contra p1 p2 k hp1 hp2 (by omega) (by omega) (by omega) (by omega) (by omega) h1 h2
          | exact contra p1 p3 k hp1 hp3 (by omega) (by omega) (by omega) (by omega) (by omega) h1 h3
          | exact contra p2 p3 k hp2 hp3 (by omega) (by omega) (by omega) (by omega) (by omega) h2 h3
          | exact contra p1 p2 (k+1) hp1 hp2 (by omega) (by omega) (by omega) (by omega) (by omega) h1 h2
          | exact contra p1 p3 (k+1) hp1 hp3 (by omega) (by omega) (by omega) (by omega) (by omega) h1 h3
          | exact contra p2 p3 (k+1) hp2 hp3 (by omega) (by omega) (by omega) (by omega) (by omega) h2 h3
      · exact ⟨p3, h3⟩
    · exact ⟨p2, h2⟩
  · exact ⟨p1, h1⟩
end erdos_28730_hyp_prime_ns

-- Derived (R3): Bertrand's postulate (Nat.exists_prime_lt_and_le_two_mul) gives primes in (k/2^(i+1), k/2^i], i=0..3,
-- all > sqrt k for k ≥ 400; at most one prime > sqrt k divides k and at most two divide k+1.
theorem erdos_28730_hyp_prime :
    ∀ k : ℕ, 400 ≤ k → ∃ p, erdos_28730_Admissible k p := by
  exact erdos_28730_hyp_prime_ns.erdos_28730_hyp_prime

namespace erdos_28730_hyp_lcm_pos_ns
open Asymptotics Filter Finset

theorem erdos_28730_hyp_lcm_pos :
    ∀ n k : ℕ, 0 < (Finset.Ioc n (n + k)).lcm id := by
  intro n k
  apply Nat.pos_of_ne_zero
  intro h
  rw [Finset.lcm_eq_zero_iff] at h
  obtain ⟨x, hx, hx0⟩ := h
  simp only [Finset.mem_coe, Finset.mem_Ioc] at hx
  simp only [id] at hx0
  omega
end erdos_28730_hyp_lcm_pos_ns

-- Elementary: an lcm of positive naturals (or of the empty set) is positive.
theorem erdos_28730_hyp_lcm_pos :
    ∀ n k : ℕ, 0 < (Finset.Ioc n (n + k)).lcm id := by
  exact erdos_28730_hyp_lcm_pos_ns.erdos_28730_hyp_lcm_pos

namespace erdos_28730_hyp_ineq_ns
open Asymptotics Filter Finset

private lemma bern (a d n : ℕ) : (a+d)^(n+1) ≤ a^(n+1) + (n+1)*d*(a+d)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : a^(n+1) ≤ (a+d)^(n+1) := Nat.pow_le_pow_left (Nat.le_add_right a d) _
    have h2 : a^(n+1) * d ≤ (a+d)^(n+1) * d := Nat.mul_le_mul h1 (le_refl d)
    calc (a+d)^(n+1+1) = (a+d)^(n+1) * (a+d) := pow_succ _ _
      _ ≤ (a^(n+1) + (n+1)*d*(a+d)^n) * (a+d) := Nat.mul_le_mul ih (le_refl _)
      _ = a^(n+1+1) + a^(n+1)*d + (n+1)*d*((a+d)^n*(a+d)) := by ring
      _ ≤ a^(n+1+1) + (a+d)^(n+1)*d + (n+1)*d*((a+d)^n*(a+d)) := by linarith
      _ = a^(n+1+1) + (n+1+1)*d*(a+d)^(n+1) := by ring

private lemma key (y k p u : ℕ) (hk : 1 ≤ k) (hu : u + 1 ≤ p) (hbig : 2*p*k^2 < y + 2*k) :
    u * (y+2*k)^k < p * y^k := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n+1 := ⟨k-1, by omega⟩
  have hb := bern y (2*(n+1)) n
  have hZpos : 0 < (y+2*(n+1))^n := by positivity
  have e1 : (y+2*(n+1))^(n+1) = (y+2*(n+1))^n * (y+2*(n+1)) := pow_succ _ _
  rw [e1] at hb ⊢
  generalize (y+2*(n+1))^n = Z at hb hZpos ⊢
  generalize y^(n+1) = W at hb ⊢
  have h1 : p * (Z*(y+2*(n+1))) ≤ p * (W + (n+1)*(2*(n+1))*Z) := Nat.mul_le_mul (le_refl p) hb
  have h2 : (2*p*(n+1)^2) * Z < (y+2*(n+1)) * Z := mul_lt_mul_of_pos_right hbig hZpos
  have h3 : (u+1) * (Z*(y+2*(n+1))) ≤ p * (Z*(y+2*(n+1))) := Nat.mul_le_mul hu (le_refl _)
  nlinarith [h1, h2, h3]

private lemma L_ne_zero (k : ℕ) : erdos_28730_L k ≠ 0 := by
  have h : erdos_28730_L k ∣ k.factorial := by
    unfold erdos_28730_L
    exact Finset.lcm_dvd (fun d hd => by
      rw [Finset.mem_Icc] at hd
      exact Nat.dvd_factorial hd.1 hd.2)
  intro h0
  rw [h0] at h
  exact Nat.factorial_ne_zero k (zero_dvd_iff.mp h)

private lemma dvd_L {k d : ℕ} (h1 : 1 ≤ d) (h2 : d ≤ k) : d ∣ erdos_28730_L k := by
  unfold erdos_28730_L
  exact Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨h1, h2⟩)

private lemma choose_dvd_L (k j : ℕ) (hk : 0 < k) (hj : j ≤ k) :
    k.choose j ∣ erdos_28730_L k := by
  have hC : k.choose j ≠ 0 := (Nat.choose_pos hj).ne'
  refine (Nat.factorization_prime_le_iff_dvd hC (L_ne_zero k)).mp ?_
  intro q hq
  have h1 : q ^ (k.choose j).factorization q ≤ k := Nat.pow_factorization_choose_le hk
  have h2 : 1 ≤ q ^ (k.choose j).factorization q := Nat.one_le_pow _ _ hq.pos
  exact (hq.pow_dvd_iff_le_factorization (L_ne_zero k)).mp (dvd_L h2 h1)

private lemma not_sq_dvd_L (k p : ℕ) (hp : p.Prime) (hk2 : k < p^2) :
    ¬ p * p ∣ erdos_28730_L k := by
  intro h
  let f : ℕ → ℕ := fun d => if p ∣ d then d / p else d
  have hT : erdos_28730_L k ∣ p * ∏ d ∈ Finset.Icc 1 k, f d := by
    unfold erdos_28730_L
    apply Finset.lcm_dvd
    intro d hd
    have hdi := Finset.dvd_prod_of_mem f hd
    show d ∣ _
    by_cases hpd : p ∣ d
    · have hf : f d = d / p := if_pos hpd
      rw [hf] at hdi
      obtain ⟨e, he⟩ := hpd
      rw [he, Nat.mul_div_cancel_left e hp.pos] at hdi
      rw [he]
      exact mul_dvd_mul_left p hdi
    · have hf : f d = d := if_neg hpd
      rw [hf] at hdi
      exact Dvd.dvd.mul_left hdi p
  have hnd : ¬ p ∣ ∏ d ∈ Finset.Icc 1 k, f d := by
    intro hdvd
    obtain ⟨d, hd, hpf⟩ := (Prime.dvd_finset_prod_iff hp.prime f).mp hdvd
    rw [Finset.mem_Icc] at hd
    by_cases hpd : p ∣ d
    · have hf : f d = d / p := if_pos hpd
      rw [hf] at hpf
      obtain ⟨e, he⟩ := hpd
      rw [he, Nat.mul_div_cancel_left e hp.pos] at hpf
      obtain ⟨g, hg⟩ := hpf
      rw [hg] at he
      have hg1 : 1 ≤ g := by
        rcases Nat.eq_zero_or_pos g with h0 | h0
        · rw [h0] at he; omega
        · exact h0
      have h3 : p * p * 1 ≤ p * (p * g) := by
        rw [← mul_assoc]; exact Nat.mul_le_mul (le_refl _) hg1
      have hp2 : p^2 = p*p := by ring
      rw [hp2] at hk2
      linarith [hd.2]
    · have hf : f d = d := if_neg hpd
      rw [hf] at hpf
      exact hpd hpf
  apply hnd
  exact (mul_dvd_mul_iff_left hp.ne_zero).mp (h.trans hT)

theorem erdos_28730_hyp_ineq :
    ∀ k : ℕ, 400 ≤ k → ∀ p : ℕ, erdos_28730_Admissible k p →
      ∃ x : ℕ, erdos_28730_L k / p ∣ x ∧ x % p = p - 1 ∧ k + 1 ≤ x ∧
        ∏ j ∈ Finset.range (k + 1), (x + j) < erdos_28730_L k * ∏ j ∈ Finset.Icc 1 k, (x - j) := by
  intro k hk p hp
  obtain ⟨hpp, hpk2, hpk, hndk, hndk1⟩ := hp
  have hp2 : 2 ≤ p := hpp.two_le
  have hpL : p ∣ erdos_28730_L k := dvd_L (by omega) hpk
  have hLeq : p * (erdos_28730_L k / p) = erdos_28730_L k := Nat.mul_div_cancel' hpL
  have hQnd : ¬ p ∣ erdos_28730_L k / p := by
    intro h
    apply not_sq_dvd_L k p hpp hpk2
    calc p * p ∣ p * (erdos_28730_L k / p) := mul_dvd_mul_left p h
      _ = erdos_28730_L k := hLeq
  have hcop : Nat.Coprime (erdos_28730_L k / p) p :=
    ((Nat.Prime.coprime_iff_not_dvd hpp).mpr hQnd).symm
  have hC : k.choose 6 ∣ erdos_28730_L k := choose_dvd_L k 6 (by omega) (by omega)
  have hCle : k.choose 6 ≤ erdos_28730_L k :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (L_ne_zero k)) hC
  have hdesc : (k + 1 - 6)^6 ≤ 720 * k.choose 6 := by
    have h1 := Nat.pow_sub_le_descFactorial k 6
    rw [Nat.descFactorial_eq_factorial_mul_choose] at h1
    have h2 : (6:ℕ).factorial = 720 := by decide
    rw [h2] at h1
    exact h1
  generalize hQdef : erdos_28730_L k / p = Q at hLeq hQnd hcop ⊢
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by omega)
  have hQbig : 2 * k^3 < Q := by
    obtain ⟨t, rfl⟩ : ∃ t, k = t + 5 := ⟨k - 5, by omega⟩
    have ht : 395 ≤ t := by omega
    have e : t + 5 + 1 - 6 = t := by omega
    rw [e] at hdesc
    have h1 : (t+5)^4 ≤ (2*t)^4 := Nat.pow_le_pow_left (by omega) 4
    have h3 : 156025 ≤ t^2 := by nlinarith
    have h4 : 0 < t^4 := by positivity
    have h6 : 156025 * t^4 ≤ t^2 * t^4 := Nat.mul_le_mul h3 (le_refl _)
    have hpQ : p * Q ≤ (t+5) * Q := Nat.mul_le_mul hpk (le_refl _)
    by_contra hcon
    push_neg at hcon
    have h7 : (t+5) * Q ≤ (t+5) * (2*(t+5)^3) := Nat.mul_le_mul (le_refl _) hcon
    have h8 : t^6 = t^2 * t^4 := by ring
    have h9 : (2*t)^4 = 16 * t^4 := by ring
    have h10 : (t+5) * (2*(t+5)^3) = 2 * (t+5)^4 := by ring
    have h11 : erdos_28730_L (t+5) = p * Q := hLeq.symm
    omega
  obtain ⟨u, hux, hup⟩ : ∃ u, Q * u % p = p - 1 ∧ u < p := by
    refine ⟨m * (p-1) % p, ?_, Nat.mod_lt _ (by omega)⟩
    have h1 : Q * (m*(p-1) % p) ≡ Q * (m*(p-1)) [MOD p] :=
      Nat.ModEq.mul_left _ (Nat.mod_modEq _ _)
    have h2 : Q * m ≡ 1 [MOD p] := by
      unfold Nat.ModEq
      rw [hm, Nat.mod_eq_of_lt (by omega : 1 < p)]
    have h3 : Q * (m*(p-1)) ≡ 1 * (p-1) [MOD p] := by
      rw [← mul_assoc]; exact h2.mul_right _
    have h4 := h1.trans h3
    unfold Nat.ModEq at h4
    rw [h4, one_mul]
    exact Nat.mod_eq_of_lt (by omega)
  have hu1 : 1 ≤ u := by
    rcases Nat.eq_zero_or_pos u with h0 | h0
    · rw [h0, mul_zero, Nat.zero_mod] at hux; omega
    · exact h0
  have hQu : Q * 1 ≤ Q * u := Nat.mul_le_mul (le_refl Q) hu1
  have hk3 : k ≤ k^3 := Nat.le_self_pow (by norm_num) k
  have hxk : k + 1 ≤ Q * u := by linarith
  refine ⟨Q * u, dvd_mul_right Q u, hux, hxk, ?_⟩
  obtain ⟨y, hy⟩ : ∃ y, Q * u = y + k := ⟨Q * u - k, by omega⟩
  have hsplit : ∏ j ∈ Finset.range (k + 1), (Q * u + j)
      = (∏ j ∈ Finset.range k, (Q * u + (j + 1))) * (Q * u) := by
    rw [Finset.prod_range_succ', add_zero]
  rw [hsplit, ← hLeq]
  have hA : ∏ j ∈ Finset.range k, (Q * u + (j + 1)) ≤ (y + 2*k)^k := by
    have := Finset.prod_le_pow_card (Finset.range k) (fun j => Q * u + (j + 1)) (y + 2*k) (by
      intro j hj
      rw [Finset.mem_range] at hj
      show Q * u + (j + 1) ≤ y + 2*k
      omega)
    rwa [Finset.card_range] at this
  have hB : y^k ≤ ∏ j ∈ Finset.Icc 1 k, (Q * u - j) := by
    have := Finset.pow_card_le_prod (Finset.Icc 1 k) (fun j => Q * u - j) y (by
      intro j hj
      rw [Finset.mem_Icc] at hj
      show y ≤ Q * u - j
      omega)
    rwa [Nat.card_Icc, Nat.add_sub_cancel] at this
  have hpk' : p * k^2 ≤ k * k^2 := Nat.mul_le_mul hpk (le_refl _)
  have hbig : 2*p*k^2 < y + 2*k := by nlinarith
  have hkey := key y k p u (by omega) (by omega) hbig
  have h1 : u * ∏ j ∈ Finset.range k, (Q * u + (j + 1)) < p * ∏ j ∈ Finset.Icc 1 k, (Q * u - j) :=
    lt_of_le_of_lt (Nat.mul_le_mul (le_refl u) hA)
      (lt_of_lt_of_le hkey (Nat.mul_le_mul (le_refl p) hB))
  have hQpos : 0 < Q := by omega
  calc (∏ j ∈ Finset.range k, (Q * u + (j + 1))) * (Q * u)
      = Q * (u * ∏ j ∈ Finset.range k, (Q * u + (j + 1))) := by ring
    _ < Q * (p * ∏ j ∈ Finset.Icc 1 k, (Q * u - j)) := mul_lt_mul_of_pos_left h1 hQpos
    _ = p * Q * ∏ j ∈ Finset.Icc 1 k, (Q * u - j) := by ring
end erdos_28730_hyp_ineq_ns

-- Derived (R2 inequality): take x = (L_k/p)*u with u ∈ [1,p-1], (L_k/p)u ≡ -1 (mod p) (gcd(L_k/p,p)=1 as p^2>k).
-- Then x/L_k = u/p ≤ 1-1/p and, since x ≥ L_k/k > 3k^3, ∏(x+j)/(x-j) < 1+1/k ≤ p/(p-1).
theorem erdos_28730_hyp_ineq :
    ∀ k : ℕ, 400 ≤ k → ∀ p : ℕ, erdos_28730_Admissible k p →
      ∃ x : ℕ, erdos_28730_L k / p ∣ x ∧ x % p = p - 1 ∧ k + 1 ≤ x ∧
        ∏ j ∈ Finset.range (k + 1), (x + j) < erdos_28730_L k * ∏ j ∈ Finset.Icc 1 k, (x - j) := by
  exact erdos_28730_hyp_ineq_ns.erdos_28730_hyp_ineq

-- Every element of the block divides the product, so the lcm divides the product (Finset.lcm_dvd).
namespace erdos_28730_hyp_lcm_dvd_prod_ns
open Asymptotics Filter Finset

theorem erdos_28730_hyp_lcm_dvd_prod :
    ∀ a l : ℕ, (Finset.Ioc a (a + l)).lcm id ∣ erdos_28730_blockProd a l := by
  intro a l
  unfold erdos_28730_blockProd
  rw [Finset.lcm_dvd_iff]
  intro b hb
  exact Finset.dvd_prod_of_mem (fun i : ℕ => i) hb
end erdos_28730_hyp_lcm_dvd_prod_ns

theorem erdos_28730_hyp_lcm_dvd_prod :
    ∀ a l : ℕ, (Finset.Ioc a (a + l)).lcm id ∣ erdos_28730_blockProd a l := by
  exact erdos_28730_hyp_lcm_dvd_prod_ns.erdos_28730_hyp_lcm_dvd_prod



-- Reindexing: Ioc (x-1) (x+k) = {x, ..., x+k} when 1 ≤ x.
namespace erdos_28730_hyp_prod_top_ns
open Asymptotics Filter Finset

private lemma erdos_28730_aux (y : ℕ) : ∀ l : ℕ,
    ∏ i ∈ Finset.Ioc y (y + l), i = ∏ j ∈ Finset.range l, (y + 1 + j) := by
  intro l
  induction l with
  | zero => simp
  | succ l ih =>
    rw [show y + (l + 1) = (y + l) + 1 by omega,
      Finset.prod_Ioc_succ_top (by omega : y ≤ y + l), ih, Finset.prod_range_succ]
    rw [show y + 1 + l = y + l + 1 by omega]

theorem erdos_28730_hyp_prod_top :
    ∀ k x : ℕ, 1 ≤ x →
      erdos_28730_blockProd (x - 1) (k + 1) = ∏ j ∈ Finset.range (k + 1), (x + j) := by
  intro k x hx
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  unfold erdos_28730_blockProd
  rw [Nat.add_sub_cancel]
  exact erdos_28730_aux y (k + 1)
end erdos_28730_hyp_prod_top_ns

theorem erdos_28730_hyp_prod_top :
    ∀ k x : ℕ, 1 ≤ x →
      erdos_28730_blockProd (x - 1) (k + 1) = ∏ j ∈ Finset.range (k + 1), (x + j) := by
  exact erdos_28730_hyp_prod_top_ns.erdos_28730_hyp_prod_top



-- Reindexing: Ioc (x-k-1) (x-1) = {x-k, ..., x-1} when k+1 ≤ x.
namespace erdos_28730_hyp_prod_bot_ns
open Asymptotics Filter Finset

theorem erdos_28730_hyp_prod_bot :
    ∀ k x : ℕ, k + 1 ≤ x →
      erdos_28730_blockProd (x - k - 1) k = ∏ j ∈ Finset.Icc 1 k, (x - j) := by
  intro k x hx
  unfold erdos_28730_blockProd
  apply Finset.prod_nbij' (fun a => x - a) (fun b => x - b)
  all_goals
    intro a ha
    simp only [Finset.mem_Ioc, Finset.mem_Icc, Finset.mem_coe] at ha ⊢
    omega
end erdos_28730_hyp_prod_bot_ns

theorem erdos_28730_hyp_prod_bot :
    ∀ k x : ℕ, k + 1 ≤ x →
      erdos_28730_blockProd (x - k - 1) k = ∏ j ∈ Finset.Icc 1 k, (x - j) := by
  exact erdos_28730_hyp_prod_bot_ns.erdos_28730_hyp_prod_bot



-- Derived from R1/R2: loss(B) = prod_p p^{sum_e (N_{p^e}(B)-1)_+}. Every prime power q ≤ k with q ≠ p
-- divides x, so it has floor(k/q)+1 multiples in [x,x+k] and floor(k/q) multiples in [x-k,x-1].
-- For p, x ≡ -1 (mod p) and 1 ≤ k mod p ≤ p-2 give a+1 versus a multiples. So the loss ratio is L_k.
namespace erdos_28730_hyp_loss_ns
open Asymptotics Filter Finset

def erdos_28730_N (a l q : ℕ) : ℕ := (a + l) / q - a / q

def erdos_28730_E (a l r B : ℕ) : ℕ :=
  ∑ e ∈ Finset.Icc 1 B, (erdos_28730_N a l (r ^ e) - 1)

-- lcm of a block divides its product, and the product of positive integers is positive
namespace erdos_28730_hyp_loss_hyp_loss_pos_ns

open Asymptotics Filter Finset

theorem erdos_28730_hyp_loss_hyp_loss_pos : ∀ a l : ℕ, 0 < erdos_28730_loss a l := by
  intro a l
  unfold erdos_28730_loss erdos_28730_blockProd
  have hprod : 0 < ∏ i ∈ Finset.Ioc a (a + l), i := by
    apply Finset.prod_pos
    intro i hi
    rw [Finset.mem_Ioc] at hi
    omega
  have hdvd : (Finset.Ioc a (a + l)).lcm id ∣ ∏ i ∈ Finset.Ioc a (a + l), i := by
    apply Finset.lcm_dvd_iff.mpr
    intro b hb
    exact Finset.dvd_prod_of_mem (fun i => i) hb
  have hlpos : 0 < (Finset.Ioc a (a + l)).lcm id := Nat.pos_of_dvd_of_pos hdvd hprod
  exact Nat.div_pos (Nat.le_of_dvd hprod hdvd) hlpos

end erdos_28730_hyp_loss_hyp_loss_pos_ns

theorem erdos_28730_hyp_loss_hyp_loss_pos : ∀ a l : ℕ, 0 < erdos_28730_loss a l := by
  exact erdos_28730_hyp_loss_hyp_loss_pos_ns.erdos_28730_hyp_loss_hyp_loss_pos

-- lcm of positive integers is positive
namespace erdos_28730_hyp_loss_hyp_L_pos_ns

open Asymptotics Filter Finset

theorem erdos_28730_hyp_loss_hyp_L_pos : ∀ k : ℕ, 0 < erdos_28730_L k := by
  intro k
  unfold erdos_28730_L
  rw [Nat.pos_iff_ne_zero, Ne, Finset.lcm_eq_zero_iff]
  simp

end erdos_28730_hyp_loss_hyp_L_pos_ns

theorem erdos_28730_hyp_loss_hyp_L_pos : ∀ k : ℕ, 0 < erdos_28730_L k := by
  exact erdos_28730_hyp_loss_hyp_L_pos_ns.erdos_28730_hyp_loss_hyp_L_pos

-- Legendre-style count: v_r(prod) = sum_e N_{r^e}, v_r(lcm) = #{e : N_{r^e} ≥ 1} since N is
-- nonincreasing in e; N_{r^e} = 0 once r^e > a+l, which holds for e > B ≥ a+l
namespace erdos_28730_hyp_loss_hyp_val_ns
-- Derived from R1/R2: loss(B) = prod_p p^{sum_e (N_{p^e}(B)-1)_+}. Every prime power q ≤ k with q ≠ p
-- divides x, so it has floor(k/q)+1 multiples in [x,x+k] and floor(k/q) multiples in [x-k,x-1].
-- For p, x ≡ -1 (mod p) and 1 ≤ k mod p ≤ p-2 give a+1 versus a multiples. So the loss ratio is L_k.
open Asymptotics Filter Finset

def erdos_28730_N (a l q : ℕ) : ℕ := (a + l) / q - a / q

def erdos_28730_E (a l r B : ℕ) : ℕ :=
  ∑ e ∈ Finset.Icc 1 B, (erdos_28730_N a l (r ^ e) - 1)

open Asymptotics Filter Finset

private lemma e28730_lt_two_pow (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; omega

private lemma e28730_count (a l q : ℕ) :
    ∑ i ∈ Finset.Ioc a (a + l), (if q ∣ i then 1 else 0) = (a + l) / q - a / q := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [show a + (l + 1) = a + l + 1 by omega, Finset.sum_Ioc_succ_top (by omega), ih]
    have hmono : a / q ≤ (a + l) / q := Nat.div_le_div_right (by omega)
    by_cases h : q ∣ a + l + 1
    · rw [if_pos h, Nat.succ_div_of_dvd h]; omega
    · rw [if_neg h, Nat.succ_div_of_not_dvd h]; omega

private lemma e28730_sum_le (t B : ℕ) (h : t ≤ B) :
    ∑ e ∈ Finset.Icc 1 B, (if e ≤ t then 1 else 0) = t := by
  rw [← Finset.card_filter]
  have : (Finset.Icc 1 B).filter (fun e => e ≤ t) = Finset.Icc 1 t := by
    ext e; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [this, Nat.card_Icc]; omega

private lemma e28730_lcm_fact (r : ℕ) (s : Finset ℕ) :
    (∀ i ∈ s, i ≠ 0) →
    s.lcm id ≠ 0 ∧ (s.lcm id).factorization r = s.sup (fun i => i.factorization r) := by
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | @insert b s hb ih =>
    intro hs
    have hb0 : b ≠ 0 := hs b (Finset.mem_insert_self b s)
    obtain ⟨h1, h2⟩ := ih (fun i hi => hs i (Finset.mem_insert_of_mem hi))
    rw [Finset.lcm_insert, Finset.sup_insert]
    have hl : (GCDMonoid.lcm (id b) (s.lcm id) : ℕ) = Nat.lcm b (s.lcm id) := rfl
    rw [hl]
    refine ⟨Nat.lcm_ne_zero hb0 h1, ?_⟩
    rw [Nat.factorization_lcm hb0 h1, Finsupp.sup_apply, h2]

theorem erdos_28730_hyp_loss_hyp_val : ∀ a l r B : ℕ, r.Prime → a + l ≤ B →
    (erdos_28730_loss a l).factorization r = erdos_28730_E a l r B := by
  intro a l r B hr hB
  unfold erdos_28730_loss erdos_28730_blockProd erdos_28730_E erdos_28730_N
  generalize hs : Finset.Ioc a (a + l) = s
  have hpos : ∀ i ∈ s, i ≠ 0 := by
    intro i hi; rw [← hs, Finset.mem_Ioc] at hi; omega
  have hle : ∀ i ∈ s, i ≤ B := by
    intro i hi; rw [← hs, Finset.mem_Ioc] at hi; omega
  have hprod_ne : (∏ i ∈ s, i) ≠ 0 := Finset.prod_ne_zero_iff.mpr hpos
  have hdvd : s.lcm id ∣ ∏ i ∈ s, i :=
    Finset.lcm_dvd_iff.mpr (fun i hi => Finset.dvd_prod_of_mem (fun j => j) hi)
  obtain ⟨_, hlcmf⟩ := e28730_lcm_fact r s hpos
  obtain ⟨t, ht⟩ : ∃ t, s.sup (fun i => i.factorization r) = t := ⟨_, rfl⟩
  rw [ht] at hlcmf
  have hfB : ∀ i ∈ s, i.factorization r ≤ B := by
    intro i hi
    have hi0 := hpos i hi
    have h1 : r ^ i.factorization r ∣ i := (hr.pow_dvd_iff_le_factorization hi0).mpr le_rfl
    have h2 : r ^ i.factorization r ≤ i := Nat.le_of_dvd (Nat.pos_of_ne_zero hi0) h1
    have h3 : 2 ^ i.factorization r ≤ r ^ i.factorization r := Nat.pow_le_pow_left hr.two_le _
    have h4 := e28730_lt_two_pow (i.factorization r)
    exact le_of_lt (lt_of_lt_of_le h4 (h3.trans (h2.trans (hle i hi))))
  have htB : t ≤ B := by rw [← ht]; exact Finset.sup_le hfB
  have hvi : ∀ i ∈ s, i.factorization r = ∑ e ∈ Finset.Icc 1 B, (if r ^ e ∣ i then 1 else 0) := by
    intro i hi
    have hiff : ∀ e, (r ^ e ∣ i ↔ e ≤ i.factorization r) :=
      fun e => hr.pow_dvd_iff_le_factorization (hpos i hi)
    simp only [hiff]
    exact (e28730_sum_le _ _ (hfB i hi)).symm
  have hNe : ∀ e ∈ Finset.Icc 1 B,
      ∑ i ∈ s, (if r ^ e ∣ i then 1 else 0) = (a + l) / r ^ e - a / r ^ e := by
    intro e _; rw [← hs]; exact e28730_count a l (r ^ e)
  have hPf : (∏ i ∈ s, i).factorization r = ∑ i ∈ s, i.factorization r := by
    rw [Nat.factorization_prod hpos, Finsupp.finset_sum_apply]
  have hP : (∏ i ∈ s, i).factorization r
      = ∑ e ∈ Finset.Icc 1 B, ((a + l) / r ^ e - a / r ^ e) := by
    rw [hPf, Finset.sum_congr rfl hvi, Finset.sum_comm]
    exact Finset.sum_congr rfl hNe
  have hpt : ∀ e ∈ Finset.Icc 1 B, ((a + l) / r ^ e - a / r ^ e)
      = ((a + l) / r ^ e - a / r ^ e - 1) + (if e ≤ t then 1 else 0) := by
    intro e he
    rw [← hNe e he]
    rw [Finset.mem_Icc] at he
    split_ifs with het
    · have hne : s.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        rintro rfl
        simp at ht
        omega
      obtain ⟨i, hi, hieq⟩ := Finset.exists_mem_eq_sup s hne (fun i => i.factorization r)
      have hvt : i.factorization r = t := by rw [← ht, hieq]
      have hdiv : r ^ e ∣ i := (hr.pow_dvd_iff_le_factorization (hpos i hi)).mpr (by omega)
      have := Finset.single_le_sum (f := fun j => if r ^ e ∣ j then 1 else 0)
        (fun j _ => Nat.zero_le _) hi
      simp only [hdiv, ↓reduceIte] at this
      omega
    · have h0 : ∑ i ∈ s, (if r ^ e ∣ i then 1 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [if_neg]
        intro hdiv
        have h1 := (hr.pow_dvd_iff_le_factorization (hpos i hi)).mp hdiv
        have h2 : i.factorization r ≤ t := by
          rw [← ht]; exact Finset.le_sup (f := fun i => i.factorization r) hi
        omega
      simp [h0]
  rw [Nat.factorization_div hdvd, Finsupp.tsub_apply, hlcmf, hP, Finset.sum_congr rfl hpt,
    Finset.sum_add_distrib, e28730_sum_le t B htB]
  omega
end erdos_28730_hyp_loss_hyp_val_ns

theorem erdos_28730_hyp_loss_hyp_val : ∀ a l r B : ℕ, r.Prime → a + l ≤ B →
    (erdos_28730_loss a l).factorization r = erdos_28730_E a l r B := by
  exact erdos_28730_hyp_loss_hyp_val_ns.erdos_28730_hyp_loss_hyp_val



-- v_r(lcm(1..k)) = #{e ≥ 1 : r^e ≤ k}, and such e are ≤ k ≤ B
namespace erdos_28730_hyp_loss_hyp_Lval_ns
open Asymptotics Filter Finset

def erdos_28730_N (a l q : ℕ) : ℕ := (a + l) / q - a / q

def erdos_28730_E (a l r B : ℕ) : ℕ :=
  ∑ e ∈ Finset.Icc 1 B, (erdos_28730_N a l (r ^ e) - 1)

open Asymptotics Filter Finset

private lemma erdos_28730_ub (r k : ℕ) (hr : r.Prime) : ∀ s : Finset ℕ,
    (∀ a ∈ s, 0 < a ∧ a ≤ k) → s.lcm id ≠ 0 ∧ (s.lcm id).factorization r ≤ Nat.log r k := by
  intro s
  refine Finset.induction_on s (fun _ => by simp) ?_
  intro a s ha ih h
  have hs : ∀ b ∈ s, 0 < b ∧ b ≤ k := fun b hb => h b (Finset.mem_insert_of_mem hb)
  obtain ⟨ih1, ih2⟩ := ih hs
  obtain ⟨ha0, hak⟩ := h a (Finset.mem_insert_self a s)
  rw [Finset.lcm_insert]
  change Nat.lcm a (s.lcm id) ≠ 0 ∧ (Nat.lcm a (s.lcm id)).factorization r ≤ Nat.log r k
  refine ⟨Nat.lcm_ne_zero ha0.ne' ih1, ?_⟩
  rw [Nat.factorization_lcm ha0.ne' ih1, Finsupp.sup_apply]
  refine max_le ?_ ih2
  have hd : r ^ (a.factorization r) ∣ a := (hr.pow_dvd_iff_le_factorization ha0.ne').2 le_rfl
  have hle : r ^ (a.factorization r) ≤ k := (Nat.le_of_dvd ha0 hd).trans hak
  exact Nat.le_log_of_pow_le hr.one_lt hle

theorem erdos_28730_hyp_loss_hyp_Lval : ∀ k r B : ℕ, r.Prime → k ≤ B →
    (erdos_28730_L k).factorization r =
      ((Finset.Icc 1 B).filter (fun e => r ^ e ≤ k)).card := by
  intro k r B hr hkB
  have hL := erdos_28730_ub r k hr (Finset.Icc 1 k)
    (fun a ha => by rw [Finset.mem_Icc] at ha; omega)
  have hfact : (erdos_28730_L k).factorization r = Nat.log r k := by
    unfold erdos_28730_L
    apply le_antisymm hL.2
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp
    · have hp : r ^ Nat.log r k ≤ k := Nat.pow_log_le_self r hk.ne'
      have hmem : r ^ Nat.log r k ∈ Finset.Icc 1 k :=
        Finset.mem_Icc.2 ⟨Nat.one_le_pow _ _ hr.pos, hp⟩
      have hd : r ^ Nat.log r k ∣ (Finset.Icc 1 k).lcm id := Finset.dvd_lcm (f := id) hmem
      exact (hr.pow_dvd_iff_le_factorization hL.1).1 hd
  rw [hfact]
  have hset : (Finset.Icc 1 B).filter (fun e => r ^ e ≤ k) = Finset.Icc 1 (Nat.log r k) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩
      exact ⟨h1, Nat.le_log_of_pow_le hr.one_lt h2⟩
    · rintro ⟨h1, h2⟩
      have hk : k ≠ 0 := by
        intro hk; subst hk; rw [Nat.log_zero_right] at h2; omega
      have hp : r ^ e ≤ k :=
        (Nat.pow_le_pow_right hr.pos h2).trans (Nat.pow_log_le_self r hk)
      have hlog : Nat.log r k ≤ k := Nat.log_le_self r k
      exact ⟨⟨h1, by omega⟩, hp⟩
  rw [hset, Nat.card_Icc]
  omega
end erdos_28730_hyp_loss_hyp_Lval_ns

theorem erdos_28730_hyp_loss_hyp_Lval : ∀ k r B : ℕ, r.Prime → k ≤ B →
    (erdos_28730_L k).factorization r =
      ((Finset.Icc 1 B).filter (fun e => r ^ e ≤ k)).card := by
  exact erdos_28730_hyp_loss_hyp_Lval_ns.erdos_28730_hyp_loss_hyp_Lval



-- a block of l ≤ q consecutive integers contains at most one multiple of q
namespace erdos_28730_hyp_loss_hyp_big_ns
open Asymptotics Filter Finset

def erdos_28730_N (a l q : ℕ) : ℕ := (a + l) / q - a / q

def erdos_28730_E (a l r B : ℕ) : ℕ :=
  ∑ e ∈ Finset.Icc 1 B, (erdos_28730_N a l (r ^ e) - 1)

open Asymptotics Filter Finset

theorem erdos_28730_hyp_loss_hyp_big : ∀ a l q : ℕ, 0 < q → l ≤ q →
    erdos_28730_N a l q ≤ 1 := by
  intro a l q hq hl
  unfold erdos_28730_N
  have h1 : (a + l) / q ≤ (a + q) / q := Nat.div_le_div_right (by omega)
  have h2 : (a + q) / q = a / q + 1 := Nat.add_div_right a hq
  omega
end erdos_28730_hyp_loss_hyp_big_ns

theorem erdos_28730_hyp_loss_hyp_big : ∀ a l q : ℕ, 0 < q → l ≤ q →
    erdos_28730_N a l q ≤ 1 := by
  exact erdos_28730_hyp_loss_hyp_big_ns.erdos_28730_hyp_loss_hyp_big



-- q ∣ x: [x, x+k] has k/q + 1 multiples of q, [x-k, x-1] has k/q ≥ 1
namespace erdos_28730_hyp_loss_hyp_small_ns
-- Derived from R1/R2: loss(B) = prod_p p^{sum_e (N_{p^e}(B)-1)_+}. Every prime power q ≤ k with q ≠ p
-- divides x, so it has floor(k/q)+1 multiples in [x,x+k] and floor(k/q) multiples in [x-k,x-1].
-- For p, x ≡ -1 (mod p) and 1 ≤ k mod p ≤ p-2 give a+1 versus a multiples. So the loss ratio is L_k.
open Asymptotics Filter Finset

def erdos_28730_N (a l q : ℕ) : ℕ := (a + l) / q - a / q

def erdos_28730_E (a l r B : ℕ) : ℕ :=
  ∑ e ∈ Finset.Icc 1 B, (erdos_28730_N a l (r ^ e) - 1)

open Asymptotics Filter Finset

theorem erdos_28730_hyp_loss_hyp_small : ∀ q x k : ℕ, 0 < q → q ∣ x → q ≤ k → k + 1 ≤ x →
    erdos_28730_N (x - 1) (k + 1) q = erdos_28730_N (x - k - 1) k q + 1 ∧
      1 ≤ erdos_28730_N (x - k - 1) k q := by
  intro q x k hq hdvd hqk hkx
  obtain ⟨t, rfl⟩ := hdvd
  unfold erdos_28730_N
  have hk : q * (k / q) + k % q = k := Nat.div_add_mod k q
  have hb : k % q < q := Nat.mod_lt _ hq
  have ha : 0 < k / q := Nat.div_pos hqk hq
  have ht : k / q + 1 ≤ t := by
    by_contra h
    push_neg at h
    have : q * t ≤ q * (k / q) := Nat.mul_le_mul_left q (by omega)
    omega
  obtain ⟨s, hs⟩ : ∃ s, t = k / q + s + 1 := ⟨t - (k / q) - 1, by omega⟩
  generalize k / q = a at *
  generalize k % q = b at *
  subst hs
  have e1 : q * (a + s + 1) = q * a + q * s + q := by ring
  have e2 : q * (2 * a + s + 1) = 2 * (q * a) + q * s + q := by ring
  have e3 : q * (a + s) = q * a + q * s := by ring
  have h1 : q * (a + s + 1) - 1 + (k + 1) = b + q * (2 * a + s + 1) := by
    rw [e1, e2]
    generalize q * a = A at *
    generalize q * s = S at *
    omega
  have h2 : q * (a + s + 1) - 1 = (q - 1) + q * (a + s) := by
    rw [e1, e3]
    generalize q * a = A at *
    generalize q * s = S at *
    omega
  have h4 : q * (a + s + 1) - k - 1 + k = (q - 1) + q * (a + s) := by
    rw [e1, e3]
    generalize q * a = A at *
    generalize q * s = S at *
    omega
  have h3 : q * (a + s + 1) - k - 1 = (q - b - 1) + q * s := by
    rw [e1]
    generalize q * a = A at *
    generalize q * s = S at *
    omega
  rw [h1, h4, h3, h2]
  have l1 : q - 1 < q := by omega
  have l2 : q - b - 1 < q := by omega
  simp only [Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt hb, Nat.div_eq_of_lt l1,
    Nat.div_eq_of_lt l2]
  omega
end erdos_28730_hyp_loss_hyp_small_ns

theorem erdos_28730_hyp_loss_hyp_small : ∀ q x k : ℕ, 0 < q → q ∣ x → q ≤ k → k + 1 ≤ x →
    erdos_28730_N (x - 1) (k + 1) q = erdos_28730_N (x - k - 1) k q + 1 ∧
      1 ≤ erdos_28730_N (x - k - 1) k q := by
  exact erdos_28730_hyp_loss_hyp_small_ns.erdos_28730_hyp_loss_hyp_small



-- prime powers r^e ≤ k with r ≠ p divide L_k / p (v_r(L_k) ≥ e, p-part removed), hence x
namespace erdos_28730_hyp_loss_hyp_div_ns
open Asymptotics Filter Finset

def erdos_28730_N (a l q : ℕ) : ℕ := (a + l) / q - a / q

def erdos_28730_E (a l r B : ℕ) : ℕ :=
  ∑ e ∈ Finset.Icc 1 B, (erdos_28730_N a l (r ^ e) - 1)

open Asymptotics Filter Finset

theorem erdos_28730_hyp_loss_hyp_div : ∀ k p x r e : ℕ, erdos_28730_Admissible k p →
    erdos_28730_L k / p ∣ x → r.Prime → 1 ≤ e → r ^ e ≤ k → r ≠ p → r ^ e ∣ x := by
  intro k p x r e hadm hx hr he hrk hne
  obtain ⟨hpp, _, hpk, _, _⟩ := hadm
  have hmem1 : r ^ e ∈ Finset.Icc 1 k := by
    rw [Finset.mem_Icc]
    exact ⟨Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hr.ne_zero), hrk⟩
  have hmem2 : p ∈ Finset.Icc 1 k := by
    rw [Finset.mem_Icc]
    exact ⟨hpp.one_lt.le, hpk⟩
  have h1 : r ^ e ∣ erdos_28730_L k := by
    unfold erdos_28730_L
    exact Finset.dvd_lcm (f := id) hmem1
  have h2 : p ∣ erdos_28730_L k := by
    unfold erdos_28730_L
    exact Finset.dvd_lcm (f := id) hmem2
  have hcop : Nat.Coprime (r ^ e) p :=
    Nat.Coprime.pow_left e ((Nat.coprime_primes hr hpp).mpr hne)
  have h3 : r ^ e ∣ p * (erdos_28730_L k / p) := by
    rw [Nat.mul_div_cancel' h2]
    exact h1
  exact dvd_trans (Nat.Coprime.dvd_of_dvd_mul_left hcop h3) hx
end erdos_28730_hyp_loss_hyp_div_ns

theorem erdos_28730_hyp_loss_hyp_div : ∀ k p x r e : ℕ, erdos_28730_Admissible k p →
    erdos_28730_L k / p ∣ x → r.Prime → 1 ≤ e → r ^ e ≤ k → r ≠ p → r ^ e ∣ x := by
  exact erdos_28730_hyp_loss_hyp_div_ns.erdos_28730_hyp_loss_hyp_div



-- k < p^2 forces e = 1; x ≡ -1 mod p and 1 ≤ k mod p ≤ p-2 give k/p+1 vs k/p multiples
namespace erdos_28730_hyp_loss_hyp_p_ns
open Asymptotics Filter Finset

def erdos_28730_N (a l q : ℕ) : ℕ := (a + l) / q - a / q

def erdos_28730_E (a l r B : ℕ) : ℕ :=
  ∑ e ∈ Finset.Icc 1 B, (erdos_28730_N a l (r ^ e) - 1)

open Asymptotics Filter Finset

theorem erdos_28730_hyp_loss_hyp_p : ∀ k p x e : ℕ, erdos_28730_Admissible k p →
    x % p = p - 1 → k + 1 ≤ x → 1 ≤ e → p ^ e ≤ k →
    erdos_28730_N (x - 1) (k + 1) (p ^ e) = erdos_28730_N (x - k - 1) k (p ^ e) + 1 ∧
      1 ≤ erdos_28730_N (x - k - 1) k (p ^ e) := by
  intro k p x e hA hxmod hkx he1 hek
  obtain ⟨hp, hk2, hpk, hndk, hndk1⟩ := hA
  have hp2 := hp.two_le
  have hp0 : 0 < p := by omega
  have he : e = 1 := by
    by_contra hne
    have h2 : 2 ≤ e := by omega
    have h3 := Nat.pow_le_pow_right hp0 h2
    exact absurd (lt_of_le_of_lt (h3.trans hek) hk2) (lt_irrefl _)
  subst he
  clear hk2 hek
  rw [pow_one]
  unfold erdos_28730_N
  obtain ⟨t, hx⟩ : ∃ t, x = p * t + (p - 1) :=
    ⟨x / p, by have := Nat.div_add_mod x p; omega⟩
  obtain ⟨s, r, hk, hr⟩ : ∃ s r, k = p * s + r ∧ r < p :=
    ⟨k / p, k % p, (Nat.div_add_mod k p).symm, Nat.mod_lt _ hp0⟩
  have hr0 : r ≠ 0 := by
    intro h; apply hndk; exact ⟨s, by omega⟩
  have hr1 : r ≠ p - 1 := by
    intro h; apply hndk1; exact ⟨s + 1, by rw [mul_add, mul_one]; omega⟩
  have hs : s ≠ 0 := by
    intro h; rw [h, mul_zero] at hk; omega
  have hts : s ≤ t := by
    by_contra h
    have h' : t + 1 ≤ s := by omega
    have h3 := Nat.mul_le_mul (le_refl p) h'
    rw [mul_add, mul_one] at h3
    omega
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hts
  have hpt : p * t = p * s + p * d := by rw [hd, mul_add]
  have hA1 : p * (t + 1 + s) = p * t + p + p * s := by ring
  have e1 : x - 1 + (k + 1) = (r - 1) + p * (t + 1 + s) := by omega
  have e2 : x - 1 = (p - 2) + p * t := by omega
  have e3 : x - k - 1 + k = (p - 2) + p * t := by omega
  have e4 : x - k - 1 = (p - 2 - r) + p * d := by omega
  have q1 : (x - 1 + (k + 1)) / p = t + 1 + s := by
    rw [e1, Nat.add_mul_div_left _ _ hp0, Nat.div_eq_of_lt (by omega), zero_add]
  have q2 : (x - 1) / p = t := by
    rw [e2, Nat.add_mul_div_left _ _ hp0, Nat.div_eq_of_lt (by omega), zero_add]
  have q3 : (x - k - 1 + k) / p = t := by
    rw [e3, Nat.add_mul_div_left _ _ hp0, Nat.div_eq_of_lt (by omega), zero_add]
  have q4 : (x - k - 1) / p = d := by
    rw [e4, Nat.add_mul_div_left _ _ hp0, Nat.div_eq_of_lt (by omega), zero_add]
  rw [q1, q2, q3, q4]
  omega
end erdos_28730_hyp_loss_hyp_p_ns

theorem erdos_28730_hyp_loss_hyp_p : ∀ k p x e : ℕ, erdos_28730_Admissible k p →
    x % p = p - 1 → k + 1 ≤ x → 1 ≤ e → p ^ e ≤ k →
    erdos_28730_N (x - 1) (k + 1) (p ^ e) = erdos_28730_N (x - k - 1) k (p ^ e) + 1 ∧
      1 ≤ erdos_28730_N (x - k - 1) k (p ^ e) := by
  exact erdos_28730_hyp_loss_hyp_p_ns.erdos_28730_hyp_loss_hyp_p



theorem erdos_28730_hyp_loss :
    ∀ k p x : ℕ, erdos_28730_Admissible k p → erdos_28730_L k / p ∣ x → x % p = p - 1 →
      k + 1 ≤ x →
      erdos_28730_loss (x - 1) (k + 1) = erdos_28730_L k * erdos_28730_loss (x - k - 1) k := by
  intro k p x hadm hdvd hmod hx
  have hLpos : erdos_28730_L k ≠ 0 := (erdos_28730_hyp_loss_hyp_L_pos k).ne'
  have hl1 : erdos_28730_loss (x - 1) (k + 1) ≠ 0 :=
    (erdos_28730_hyp_loss_hyp_loss_pos _ _).ne'
  have hl2 : erdos_28730_loss (x - k - 1) k ≠ 0 :=
    (erdos_28730_hyp_loss_hyp_loss_pos _ _).ne'
  apply Nat.eq_of_factorization_eq hl1 (mul_ne_zero hLpos hl2)
  intro r
  by_cases hr : r.Prime
  swap
  · rw [Nat.factorization_eq_zero_of_not_prime _ hr, Nat.factorization_eq_zero_of_not_prime _ hr]
  rw [Nat.factorization_mul hLpos hl2, Finsupp.add_apply]
  have hB1 : x - 1 + (k + 1) ≤ x + k := by omega
  have hB2 : x - k - 1 + k ≤ x + k := by omega
  have hB3 : k ≤ x + k := by omega
  rw [erdos_28730_hyp_loss_hyp_val (x - 1) (k + 1) r (x + k) hr hB1,
    erdos_28730_hyp_loss_hyp_val (x - k - 1) k r (x + k) hr hB2,
    erdos_28730_hyp_loss_hyp_Lval k r (x + k) hr hB3]
  unfold erdos_28730_E
  rw [Finset.card_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
  have hqpos : 0 < r ^ e := pow_pos hr.pos e
  by_cases hq : r ^ e ≤ k
  · have key : erdos_28730_N (x - 1) (k + 1) (r ^ e) = erdos_28730_N (x - k - 1) k (r ^ e) + 1 ∧
        1 ≤ erdos_28730_N (x - k - 1) k (r ^ e) := by
      by_cases hrp : r = p
      · rw [hrp] at hq ⊢
        exact erdos_28730_hyp_loss_hyp_p k p x e hadm hmod hx he1 hq
      · exact erdos_28730_hyp_loss_hyp_small (r ^ e) x k hqpos
          (erdos_28730_hyp_loss_hyp_div k p x r e hadm hdvd hr he1 hq hrp) hq hx
    simp only [if_pos hq]
    omega
  · have h1 := erdos_28730_hyp_loss_hyp_big (x - 1) (k + 1) (r ^ e) hqpos (by omega)
    have h2 := erdos_28730_hyp_loss_hyp_big (x - k - 1) k (r ^ e) hqpos (by omega)
    simp only [if_neg hq]
    omega
end erdos_28730_hyp_loss_ns

theorem erdos_28730_hyp_loss :
    ∀ k p x : ℕ, erdos_28730_Admissible k p → erdos_28730_L k / p ∣ x → x % p = p - 1 →
      k + 1 ≤ x →
      erdos_28730_loss (x - 1) (k + 1) = erdos_28730_L k * erdos_28730_loss (x - k - 1) k := by
  exact erdos_28730_hyp_loss_ns.erdos_28730_hyp_loss



namespace Finset
def lcmInterval {α : Type*} [CommSemiring α] [NormalizedGCDMonoid α]
    [Preorder α] [LocallyFiniteOrder α] (n k : α) : α := (Finset.Ioc n (n + k)).lcm id
end Finset

open Asymptotics Filter Finset

theorem erdos_28730 :
    ∀ᶠ k in atTop, {(m, n) | n + k ≤ m ∧ lcmInterval m (k + 1) < lcmInterval n k}.Nonempty := by
  rw [Filter.eventually_atTop]
  refine ⟨400, fun k hk => ?_⟩
  obtain ⟨p, hp⟩ := erdos_28730_hyp_prime k hk
  obtain ⟨x, hdvd, hmod, hx, hlt⟩ := erdos_28730_hyp_ineq k hk p hp
  have e1 : ∏ j ∈ Finset.range (k + 1), (x + j)
      = (Finset.Ioc (x - 1) (x - 1 + (k + 1))).lcm id * erdos_28730_loss (x - 1) (k + 1) := by
    rw [← erdos_28730_hyp_prod_top k x (by omega)]
    unfold erdos_28730_loss
    exact (Nat.mul_div_cancel' (erdos_28730_hyp_lcm_dvd_prod _ _)).symm
  have e2 : ∏ j ∈ Finset.Icc 1 k, (x - j)
      = (Finset.Ioc (x - k - 1) (x - k - 1 + k)).lcm id * erdos_28730_loss (x - k - 1) k := by
    rw [← erdos_28730_hyp_prod_bot k x hx]
    unfold erdos_28730_loss
    exact (Nat.mul_div_cancel' (erdos_28730_hyp_lcm_dvd_prod _ _)).symm
  have hid : (Finset.Ioc (x - 1) (x - 1 + (k + 1))).lcm id * erdos_28730_L k
        * ∏ j ∈ Finset.Icc 1 k, (x - j)
      = (Finset.Ioc (x - k - 1) (x - k - 1 + k)).lcm id * ∏ j ∈ Finset.range (k + 1), (x + j) := by
    rw [e1, e2, erdos_28730_hyp_loss k p x hp hdvd hmod hx]
    ring
  have hB := erdos_28730_hyp_lcm_pos (x - k - 1) k
  refine ⟨(x - 1, x - k - 1), ?_⟩
  show x - k - 1 + k ≤ x - 1 ∧
    (Finset.Ioc (x - 1) (x - 1 + (k + 1))).lcm id < (Finset.Ioc (x - k - 1) (x - k - 1 + k)).lcm id
  refine ⟨by omega, ?_⟩
  have h1 := mul_lt_mul_of_pos_left hlt hB
  rw [← hid, mul_assoc] at h1
  exact lt_of_mul_lt_mul_right h1 (Nat.zero_le _)
