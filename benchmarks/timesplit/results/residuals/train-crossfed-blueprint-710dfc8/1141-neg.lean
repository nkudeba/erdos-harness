open Nat Set

def TSProp (n : ℕ) : Prop :=
  ∀ k, k ^ 2 < n → Coprime n k → (n - k ^ 2).Prime

namespace erdos_24202_neg_hyp_sieve_ns

open Nat Set

theorem erdos_24202_neg_hyp_sieve :
    ∀ n k q : ℕ, q.Prime → Nat.Coprime n k → 4 * k ^ 2 ≤ n → q ∣ n - k ^ 2 →
      4 * q < 3 * n → ¬ TSProp n := by
  intro n k q hq hcop h4 hdvd h3 hT
  have hn : k ^ 2 < n := by omega
  have hp : (n - k ^ 2).Prime := hT k hn hcop
  have h2 : 2 ≤ q := hq.two_le
  rcases hp.eq_one_or_self_of_dvd q hdvd with h | h
  · omega
  · omega

end erdos_24202_neg_hyp_sieve_ns

namespace erdos_24202_neg_hyp_count_ns

-- IMPORTS: Mathlib.Data.Nat.Totient
-- IMPORTS: Mathlib.RingTheory.Coprime.Lemmas
-- IMPORTS: Mathlib.Analysis.SpecialFunctions.Pow.Real
open Nat Set

private lemma crt_aux (m p a u v k : ℤ) (huv : u * p + v * m = 1) :
    m * p ∣ a * u * p - k ↔ m ∣ a - k ∧ p ∣ k := by
  constructor
  · intro h
    have hm : m ∣ a * u * p - k := _root_.dvd_trans (_root_.dvd_mul_right m p) h
    have hp : p ∣ a * u * p - k := _root_.dvd_trans (_root_.dvd_mul_left p m) h
    refine ⟨?_, ?_⟩
    · have e : a - k = (a * u * p - k) + m * (a * v) := by linear_combination (-a) * huv
      rw [e]
      exact _root_.dvd_add hm (_root_.dvd_mul_right m _)
    · have h2 : p ∣ p * (a * u) - (a * u * p - k) :=
        _root_.dvd_sub (_root_.dvd_mul_right p _) hp
      have e : p * (a * u) - (a * u * p - k) = k := by ring
      rwa [e] at h2
  · rintro ⟨hm, hp⟩
    have hcop : IsCoprime m p := ⟨v, u, by linear_combination huv⟩
    have hm' : m ∣ a * u * p - k := by
      have e : a * u * p - k = (a - k) - m * (a * v) := by linear_combination a * huv
      rw [e]
      exact _root_.dvd_sub hm (_root_.dvd_mul_right m _)
    have hp' : p ∣ a * u * p - k := _root_.dvd_sub (_root_.dvd_mul_left p (a * u)) hp
    exact hcop.mul_dvd hm' hp'

private lemma base_count (m : ℕ) (hm : 0 < m) (a : ℤ) (X : ℕ) :
    |((((Finset.Icc 1 X).filter (fun k : ℕ => (m : ℤ) ∣ a - k)).card : ℕ) : ℝ)
      - (X : ℝ) / m| ≤ 1 := by
  set s := (Finset.Icc 1 X).filter (fun k : ℕ => (m : ℤ) ∣ a - k) with hs
  have hmZ : (0 : ℤ) < m := by exact_mod_cast hm
  have hlow : X / m ≤ s.card := by
    set t := ((a - 1) % (m : ℤ)).toNat with htdef
    have hnn : 0 ≤ (a - 1) % (m : ℤ) := Int.emod_nonneg _ (ne_of_gt hmZ)
    have hlt : (a - 1) % (m : ℤ) < m := Int.emod_lt_of_pos _ hmZ
    have ht : (t : ℤ) = (a - 1) % (m : ℤ) := Int.toNat_of_nonneg hnn
    have htm : t < m := by
      have : (t : ℤ) < m := by rw [ht]; exact hlt
      exact_mod_cast this
    have hdiv : (a - 1) % (m : ℤ) + (m : ℤ) * ((a - 1) / (m : ℤ)) = a - 1 := by
      rw [Int.emod_def]; ring
    calc X / m = (Finset.range (X / m)).card := (Finset.card_range _).symm
      _ ≤ s.card := by
        apply Finset.card_le_card_of_injOn (fun j : ℕ => t + 1 + j * m)
        · intro j hj
          have hj' : j < X / m := by simpa using hj
          have h1 : (j + 1) * m ≤ X / m * m := Nat.mul_le_mul (Nat.succ_le_of_lt hj') le_rfl
          have h2 : X / m * m ≤ X := Nat.div_mul_le_self X m
          have h3 : (j + 1) * m = j * m + m := by ring
          have key : t + 1 + j * m ∈ s := by
            rw [hs, Finset.mem_filter, Finset.mem_Icc]
            refine ⟨⟨by omega, by omega⟩, ?_⟩
            refine ⟨(a - 1) / (m : ℤ) - j, ?_⟩
            push_cast
            linear_combination -hdiv - ht
          exact key
        · intro i hi j hj hij
          have h' : t + 1 + i * m = t + 1 + j * m := hij
          have h'' : i * m = j * m := by omega
          exact Nat.eq_of_mul_eq_mul_right hm h''
  have hup : s.card ≤ X / m + 1 := by
    calc s.card ≤ (Finset.range (X / m + 1)).card := by
          apply Finset.card_le_card_of_injOn (fun k : ℕ => (k - 1) / m)
          · intro k hk
            have hk' : k ∈ s := hk
            rw [hs, Finset.mem_filter, Finset.mem_Icc] at hk'
            have h1 : (k - 1) / m ≤ X / m := by
              apply Nat.div_le_div_right
              omega
            have key : (k - 1) / m ∈ Finset.range (X / m + 1) :=
              Finset.mem_range.mpr (Nat.lt_succ_of_le h1)
            exact key
          · intro k1 hk1 k2 hk2 hk
            have e : (k1 - 1) / m = (k2 - 1) / m := hk
            have h1 : k1 ∈ s := hk1
            have h2 : k2 ∈ s := hk2
            rw [hs, Finset.mem_filter, Finset.mem_Icc] at h1 h2
            obtain ⟨⟨hk1a, hk1b⟩, hk1d⟩ := h1
            obtain ⟨⟨hk2a, hk2b⟩, hk2d⟩ := h2
            have d1 := Nat.div_add_mod (k1 - 1) m
            have d2 := Nat.div_add_mod (k2 - 1) m
            have r1 := Nat.mod_lt (k1 - 1) hm
            have r2 := Nat.mod_lt (k2 - 1) hm
            rw [e] at d1
            generalize (k2 - 1) / m = D at d1 d2
            generalize (k1 - 1) % m = R1 at d1 r1
            generalize (k2 - 1) % m = R2 at d2 r2
            generalize m * D = MD at d1 d2
            have hb1 : k1 < k2 + m := by omega
            have hb2 : k2 < k1 + m := by omega
            have hd : (m : ℤ) ∣ (k2 : ℤ) - k1 := by
              have := _root_.dvd_sub hk1d hk2d
              have e2 : a - (k1 : ℤ) - (a - k2) = (k2 : ℤ) - k1 := by ring
              rwa [e2] at this
            obtain ⟨c, hc⟩ := hd
            have hb1' : (k1 : ℤ) < k2 + m := by exact_mod_cast hb1
            have hb2' : (k2 : ℤ) < k1 + m := by exact_mod_cast hb2
            have hc0 : c = 0 := by
              by_contra hne
              rcases _root_.lt_or_gt_of_ne hne with hneg | hpos
              · have hle : c ≤ -1 := by omega
                have := _root_.mul_le_mul_of_nonneg_left hle hmZ.le
                rw [mul_neg_one] at this
                linarith
              · have hge : 1 ≤ c := by omega
                have := _root_.mul_le_mul_of_nonneg_left hge hmZ.le
                rw [mul_one] at this
                linarith
            rw [hc0, mul_zero] at hc
            omega
      _ = X / m + 1 := Finset.card_range _
  have hD1 : X / m * m ≤ X := Nat.div_mul_le_self X m
  have hD2 : X < (X / m + 1) * m := by
    have d := Nat.div_add_mod X m
    have r := Nat.mod_lt X hm
    have e : (X / m + 1) * m = m * (X / m) + m := by ring
    omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hR1 : ((X / m : ℕ) : ℝ) ≤ (X : ℝ) / m := by
    rw [_root_.le_div_iff₀ hmR]; exact_mod_cast hD1
  have hR2 : (X : ℝ) / m < ((X / m : ℕ) : ℝ) + 1 := by
    rw [_root_.div_lt_iff₀ hmR]; exact_mod_cast hD2
  have hlowR : ((X / m : ℕ) : ℝ) ≤ (s.card : ℝ) := by exact_mod_cast hlow
  have hupR : (s.card : ℝ) ≤ ((X / m : ℕ) : ℝ) + 1 := by exact_mod_cast hup
  rw [abs_le]
  constructor <;> linarith

private lemma sieve_count (X : ℕ) : ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → ∀ m : ℕ, 0 < m →
    (∀ p ∈ P, Nat.Coprime p m) → ∀ a : ℤ,
    |((((Finset.Icc 1 X).filter (fun k : ℕ => (m : ℤ) ∣ a - k ∧ ∀ p ∈ P, ¬ p ∣ k)).card : ℕ) : ℝ)
      - (X : ℝ) / m * ∏ p ∈ P, (1 - 1 / (p : ℝ))| ≤ (2 : ℝ) ^ P.card := by
  intro P
  induction P using Finset.induction_on with
  | empty =>
    intro _ m hm _ a
    have hfe : (Finset.Icc 1 X).filter
          (fun k : ℕ => (m : ℤ) ∣ a - k ∧ ∀ p ∈ (∅ : Finset ℕ), ¬ p ∣ k)
        = (Finset.Icc 1 X).filter (fun k : ℕ => (m : ℤ) ∣ a - k) := by
      apply Finset.filter_congr
      intro k _
      simp
    rw [hfe, Finset.prod_empty, mul_one, Finset.card_empty, pow_zero]
    exact base_count m hm a X
  | @insert p P hp ih =>
    intro hprime m hm hcop a
    have hpP : ∀ q ∈ P, q.Prime := fun q hq => hprime q (Finset.mem_insert_of_mem hq)
    have hpp : p.Prime := hprime p (Finset.mem_insert_self p P)
    have hcopP : ∀ q ∈ P, Nat.Coprime q m := fun q hq => hcop q (Finset.mem_insert_of_mem hq)
    have hpm : Nat.Coprime p m := hcop p (Finset.mem_insert_self p P)
    have hZ : IsCoprime (p : ℤ) (m : ℤ) := Nat.isCoprime_iff_coprime.mpr hpm
    obtain ⟨u, v, huv⟩ := hZ
    have hmp : 0 < m * p := Nat.mul_pos hm hpp.pos
    have hcopP' : ∀ q ∈ P, Nat.Coprime q (m * p) := by
      intro q hq
      have hqp : q ≠ p := fun h => hp (by rw [← h]; exact hq)
      exact Nat.Coprime.mul_right (hcopP q hq) ((Nat.coprime_primes (hpP q hq) hpp).mpr hqp)
    have ih1 := ih hpP m hm hcopP a
    have ih2 := ih hpP (m * p) hmp hcopP' (a * u * p)
    set C := (Finset.Icc 1 X).filter
      (fun k : ℕ => (m : ℤ) ∣ a - k ∧ ∀ q ∈ insert p P, ¬ q ∣ k) with hCdef
    set A := (Finset.Icc 1 X).filter
      (fun k : ℕ => (m : ℤ) ∣ a - k ∧ ∀ q ∈ P, ¬ q ∣ k) with hA
    set B := (Finset.Icc 1 X).filter
      (fun k : ℕ => ((m * p : ℕ) : ℤ) ∣ a * u * p - k ∧ ∀ q ∈ P, ¬ q ∣ k) with hB
    have hC : C = A.filter (fun k => ¬ p ∣ k) := by
      ext k
      simp only [hCdef, hA, Finset.mem_filter, Finset.forall_mem_insert]
      tauto
    have hB' : B = A.filter (fun k => p ∣ k) := by
      ext k
      simp only [hA, hB, Finset.mem_filter]
      have key := crt_aux (m : ℤ) (p : ℤ) a u v (k : ℤ) huv
      rw [Nat.cast_mul, key, Int.natCast_dvd_natCast]
      tauto
    have hcard : (A.filter (fun k => p ∣ k)).card + (A.filter (fun k => ¬ p ∣ k)).card
        = A.card := Finset.card_filter_add_card_filter_not _
    rw [← hB', ← hC] at hcard
    have hcardP : (insert p P).card = P.card + 1 := by simp [hp]
    have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hpp.ne_zero
    have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hmain : (X : ℝ) / m * ((1 - 1 / (p : ℝ)) * ∏ q ∈ P, (1 - 1 / (q : ℝ)))
        = (X : ℝ) / m * ∏ q ∈ P, (1 - 1 / (q : ℝ))
          - (X : ℝ) / ((m * p : ℕ) : ℝ) * ∏ q ∈ P, (1 - 1 / (q : ℝ)) := by
      rw [Nat.cast_mul, show (X : ℝ) / ((m : ℝ) * (p : ℝ)) = (X : ℝ) / m * (1 / p) by
        rw [_root_.div_mul_div_comm, mul_one]]
      ring
    have hcR : (C.card : ℝ) = (A.card : ℝ) - (B.card : ℝ) := by
      have : (B.card : ℝ) + C.card = A.card := by exact_mod_cast hcard
      linarith
    have hpow : (2 : ℝ) ^ (P.card + 1) = 2 * 2 ^ P.card := by ring
    rw [Finset.prod_insert hp, hcardP, hmain, hcR, hpow]
    rw [abs_le] at ih1 ih2 ⊢
    constructor <;> linarith [ih1.1, ih1.2, ih2.1, ih2.2]

theorem erdos_24202_neg_hyp_count :
    ∀ n q : ℕ, 1 ≤ n → 1 ≤ q → Nat.Coprime n q → ∀ (r : ℤ) (X : ℕ),
      (((Finset.Icc 1 X).filter
          (fun k : ℕ => (k : ℤ) % (q : ℤ) = r % (q : ℤ) ∧ Nat.Coprime k n)).card : ℝ)
        ≥ ((X : ℝ) / q) * ((n.totient : ℝ) / n) - (2 : ℝ) ^ n.primeFactors.card := by
  intro n q hn hq hnq r X
  have hP : ∀ p ∈ n.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hcop : ∀ p ∈ n.primeFactors, Nat.Coprime p q :=
    fun p hp => Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hp) hnq
  have h := sieve_count X n.primeFactors hP q hq hcop r
  have hfeq : (Finset.Icc 1 X).filter
        (fun k : ℕ => (k : ℤ) % (q : ℤ) = r % (q : ℤ) ∧ Nat.Coprime k n)
      = (Finset.Icc 1 X).filter
        (fun k : ℕ => (q : ℤ) ∣ r - k ∧ ∀ p ∈ n.primeFactors, ¬ p ∣ k) := by
    apply Finset.filter_congr
    intro k _
    have e1 : ((k : ℤ) % (q : ℤ) = r % (q : ℤ)) ↔ (q : ℤ) ∣ r - k := Int.modEq_iff_dvd
    rw [e1]
    apply and_congr_right
    intro _
    constructor
    · intro hc p hp hpk
      have hpn := Nat.dvd_of_mem_primeFactors hp
      have h1 := Nat.dvd_gcd hpk hpn
      rw [hc.gcd_eq_one] at h1
      exact (Nat.prime_of_mem_primeFactors hp).one_lt.ne' (Nat.dvd_one.mp h1)
    · intro hall
      by_contra hc
      obtain ⟨p, hp, hpk, hpn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
      exact hall p (Nat.mem_primeFactors.mpr ⟨hp, hpn, by omega⟩) hpk
  rw [hfeq]
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hP0 : ∏ p ∈ n.primeFactors, (p : ℝ) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr
      (fun p hp => Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero)
  have hprod : ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ))
      = (∏ p ∈ n.primeFactors, ((p - 1 : ℕ) : ℝ)) / ∏ p ∈ n.primeFactors, (p : ℝ) := by
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have hp1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_lt.le
    have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
    rw [Nat.cast_sub hp1, Nat.cast_one, _root_.sub_div, _root_.div_self hp0]
  have htot : ((n.totient : ℝ) / n) = ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ)) := by
    rw [hprod, _root_.div_eq_div_iff hn0 hP0]
    have h0 := Nat.totient_mul_prod_primeFactors n
    rw [mul_comm (∏ p ∈ n.primeFactors, ((p - 1 : ℕ) : ℝ))]
    rw [← Nat.cast_prod, ← Nat.cast_prod, ← Nat.cast_mul, ← Nat.cast_mul, h0]
  rw [htot]
  rw [abs_le] at h
  linarith [h.1]

end erdos_24202_neg_hyp_count_ns

namespace erdos_24202_neg_hyp_count_pos_ns

open Nat Set

private lemma prodc_le_24202 (s : Finset ℕ) :
    (∏ p ∈ s, (if p < 59049 then 4 ^ 10 else 1)) ≤ (4 ^ 10) ^ 59049 := by
  have h1 : (∏ p ∈ s, (if p < 59049 then (4:ℕ) ^ 10 else 1))
      = ∏ p ∈ s.filter (· < 59049), (4:ℕ) ^ 10 := by
    rw [Finset.prod_filter]
  rw [h1, Finset.prod_const]
  apply Nat.pow_le_pow_right (by norm_num)
  refine le_trans (Finset.card_le_card (t := Finset.range 59049) ?_) (Finset.card_range _).le
  intro x hx
  rw [Finset.mem_filter] at hx
  exact Finset.mem_range.mpr hx.2

private lemma lemA_24202 : ∃ C : ℕ, ∀ m : ℕ,
    (∏ p ∈ m.primeFactors, (2 * p)) ^ 10 ≤
      C * (∏ p ∈ m.primeFactors, p) * (∏ p ∈ m.primeFactors, (p - 1)) ^ 10 := by
  refine ⟨(4 ^ 10) ^ 59049, fun m => ?_⟩
  have hpt : ∀ p ∈ m.primeFactors,
      (2 * p) ^ 10 ≤ (if p < 59049 then 4 ^ 10 else 1) * p * (p - 1) ^ 10 := by
    intro p hp
    have h2 := (Nat.prime_of_mem_primeFactors hp).two_le
    split_ifs with h
    · have e1 : 2 * p ≤ 4 * (p - 1) := by omega
      calc (2 * p) ^ 10 ≤ (4 * (p - 1)) ^ 10 := Nat.pow_le_pow_left e1 10
        _ = 4 ^ 10 * (p - 1) ^ 10 := by rw [mul_pow]
        _ ≤ 4 ^ 10 * p * (p - 1) ^ 10 := by
          apply Nat.mul_le_mul ?_ le_rfl
          nlinarith
    · have h3 : (3:ℕ) ^ 10 ≤ p := by
        have e : (3:ℕ) ^ 10 = 59049 := by norm_num
        rw [e]
        omega
      have e1 : 2 * p ≤ 3 * (p - 1) := by omega
      calc (2 * p) ^ 10 ≤ (3 * (p - 1)) ^ 10 := Nat.pow_le_pow_left e1 10
        _ = 3 ^ 10 * (p - 1) ^ 10 := by rw [mul_pow]
        _ ≤ p * (p - 1) ^ 10 := Nat.mul_le_mul h3 le_rfl
        _ = 1 * p * (p - 1) ^ 10 := by ring
  have hc := prodc_le_24202 m.primeFactors
  calc (∏ p ∈ m.primeFactors, (2 * p)) ^ 10 = ∏ p ∈ m.primeFactors, (2 * p) ^ 10 := by
        rw [Finset.prod_pow]
    _ ≤ ∏ p ∈ m.primeFactors, ((if p < 59049 then 4 ^ 10 else 1) * p * (p - 1) ^ 10) :=
        Finset.prod_le_prod (fun _ _ => Nat.zero_le _) hpt
    _ = (∏ p ∈ m.primeFactors, (if p < 59049 then 4 ^ 10 else 1)) * (∏ p ∈ m.primeFactors, p)
          * (∏ p ∈ m.primeFactors, (p - 1)) ^ 10 := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow]
    _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul hc le_rfl) le_rfl

theorem erdos_24202_neg_hyp_count_pos :
    ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → ∀ q : ℕ, q.Prime → (q : ℝ) ≤ (n : ℝ) ^ (0.35 : ℝ) →
      0 < (((Nat.sqrt n / 2 : ℕ) : ℝ) / q) * ((n.totient : ℝ) / n)
            - (2 : ℝ) ^ n.primeFactors.card := by
  obtain ⟨C, hC⟩ := lemA_24202
  obtain ⟨D, hD⟩ : ∃ D : ℕ, D = 4 ^ 20 * C ^ 2 := ⟨_, rfl⟩
  refine ⟨D + 9, fun n hn q hq hqn => ?_⟩
  have hn0 : 0 < n := by omega
  have hq0 : 0 < q := hq.pos
  have hq20 : q ^ 20 ≤ n ^ 7 := by
    have h1 : (q : ℝ) ^ (20:ℕ) ≤ ((n : ℝ) ^ (0.35 : ℝ)) ^ (20:ℕ) := by gcongr
    have h2 : ((n : ℝ) ^ (0.35 : ℝ)) ^ (20:ℕ) = (n : ℝ) ^ (7:ℕ) := by
      rw [← Real.rpow_natCast ((n : ℝ) ^ (0.35 : ℝ)) 20, ← Real.rpow_mul (by positivity),
        show (0.35:ℝ) * ((20:ℕ):ℝ) = ((7:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    rw [h2] at h1
    exact_mod_cast h1
  obtain ⟨X, hXdef⟩ : ∃ X : ℕ, X = Nat.sqrt n / 2 := ⟨_, rfl⟩
  have hs3 : 3 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by omega)
  have hlt := Nat.lt_succ_sqrt n
  have h4X : Nat.sqrt n + 1 ≤ 4 * X := by omega
  have hX2 : n < (4 * X) * (4 * X) := lt_of_lt_of_le hlt (Nat.mul_le_mul h4X h4X)
  have hX10 : n ^ 10 < (4 * X) ^ 20 := by
    have := pow_lt_pow_left₀ hX2 (Nat.zero_le n) (by norm_num : (10:ℕ) ≠ 0)
    calc n ^ 10 < ((4 * X) * (4 * X)) ^ 10 := this
      _ = (4 * X) ^ 20 := by ring
  have hid := Nat.totient_mul_prod_primeFactors n
  have hBpos : 0 < ∏ p ∈ n.primeFactors, (p - 1) :=
    Finset.prod_pos (fun p hp => by
      have := (Nat.prime_of_mem_primeFactors hp).two_le
      omega)
  have hQn : ∏ p ∈ n.primeFactors, p ≤ n := Nat.le_of_dvd hn0 (Nat.prod_primeFactors_dvd n)
  have ha : ∏ p ∈ n.primeFactors, (2 * p) = 2 ^ n.primeFactors.card * ∏ p ∈ n.primeFactors, p := by
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  have hCn := hC n
  generalize ∏ p ∈ n.primeFactors, (2 * p) = a at ha hCn
  generalize ∏ p ∈ n.primeFactors, p = Q at ha hCn hQn hid
  generalize ∏ p ∈ n.primeFactors, (p - 1) = B at hCn hBpos hid
  have T : a * q < X * B := by
    by_contra hcon
    push_neg at hcon
    have h20 : (X * B) ^ 20 ≤ (a * q) ^ 20 := Nat.pow_le_pow_left hcon 20
    have step1 : (a * q) ^ 20 ≤ C ^ 2 * n ^ 9 * B ^ 20 := by
      calc (a * q) ^ 20 = (a ^ 10) ^ 2 * q ^ 20 := by ring
        _ ≤ (C * Q * B ^ 10) ^ 2 * n ^ 7 := Nat.mul_le_mul (Nat.pow_le_pow_left hCn 2) hq20
        _ = C ^ 2 * Q ^ 2 * B ^ 20 * n ^ 7 := by ring
        _ ≤ C ^ 2 * n ^ 2 * B ^ 20 * n ^ 7 := by gcongr
        _ = C ^ 2 * n ^ 9 * B ^ 20 := by ring
    have hB20 : 0 < B ^ 20 := by positivity
    have h9 : 0 < n ^ 9 := by positivity
    have hDn : D < n := by omega
    have step2a : D * n ^ 9 < n ^ 10 := by nlinarith
    have step2 : D * n ^ 9 * B ^ 20 < n ^ 10 * B ^ 20 := mul_lt_mul_of_pos_right step2a hB20
    have step3 : n ^ 10 * B ^ 20 < (4 * X) ^ 20 * B ^ 20 := mul_lt_mul_of_pos_right hX10 hB20
    have hfin : 4 ^ 20 * (X * B) ^ 20 < 4 ^ 20 * (X * B) ^ 20 := by
      calc 4 ^ 20 * (X * B) ^ 20 ≤ 4 ^ 20 * (a * q) ^ 20 := Nat.mul_le_mul le_rfl h20
        _ ≤ 4 ^ 20 * (C ^ 2 * n ^ 9 * B ^ 20) := Nat.mul_le_mul le_rfl step1
        _ = D * n ^ 9 * B ^ 20 := by rw [hD]; ring
        _ < n ^ 10 * B ^ 20 := step2
        _ < (4 * X) ^ 20 * B ^ 20 := step3
        _ = 4 ^ 20 * (X * B) ^ 20 := by ring
    exact lt_irrefl _ hfin
  have key : 2 ^ n.primeFactors.card * (q * n) < X * n.totient := by
    by_contra hcon
    push_neg at hcon
    have h1 := Nat.mul_le_mul hcon (le_refl Q)
    have e1 : X * n.totient * Q = n * (X * B) := by rw [mul_assoc, hid]; ring
    have e2 : 2 ^ n.primeFactors.card * (q * n) * Q = n * (a * q) := by rw [ha]; ring
    rw [e1, e2] at h1
    have h2 : n * (a * q) < n * (X * B) := mul_lt_mul_of_pos_left T hn0
    exact absurd h1 (not_le.mpr h2)
  rw [← hXdef]
  have hq' : (0:ℝ) < q := by exact_mod_cast hq0
  have hn' : (0:ℝ) < n := by exact_mod_cast hn0
  have keyR : (2:ℝ) ^ n.primeFactors.card * ((q:ℝ) * n) < (X:ℝ) * n.totient := by
    exact_mod_cast key
  have eq : ((X:ℝ) / q) * ((n.totient : ℝ) / n) = ((X:ℝ) * n.totient) / ((q:ℝ) * n) := by
    field_simp
  rw [eq, sub_pos, lt_div_iff₀ (mul_pos hq' hn')]
  exact keyR

end erdos_24202_neg_hyp_count_pos_ns

def GoodPrime (n q : ℕ) : Prop :=
  q.Prime ∧ ¬ q ∣ n ∧ (q : ℝ) ≤ (n : ℝ) ^ (0.35 : ℝ) ∧ ∃ r : ℤ, (q : ℤ) ∣ r ^ 2 - (n : ℤ)

namespace erdos_24202_neg_hyp_square_ns

-- IMPORTS: Mathlib.NumberTheory.Bertrand
open Nat Set

private lemma real_bound_aux (q n : ℕ) (h : q ^ 20 ≤ n ^ 7) :
    (q : ℝ) ≤ (n : ℝ) ^ (0.35 : ℝ) := by
  have h0 : (0:ℝ) ≤ (n:ℝ) ^ (0.35:ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  rw [← Real.rpow_le_rpow_iff (Nat.cast_nonneg q) h0 (show (0:ℝ) < ((20:ℕ):ℝ) by norm_num)]
  rw [← Real.rpow_mul (Nat.cast_nonneg n)]
  rw [show (0.35:ℝ) * ((20:ℕ):ℝ) = ((7:ℕ):ℝ) by norm_num]
  rw [Real.rpow_natCast, Real.rpow_natCast]
  exact_mod_cast h

theorem erdos_24202_neg_hyp_square :
    ∃ N₂ : ℕ, ∀ m : ℕ, 1 ≤ m → N₂ ≤ m ^ 2 → ∃ q : ℕ, GoodPrime (m ^ 2) q := by
  refine ⟨2 ^ 30, ?_⟩
  intro m hm hN
  have hm15 : 2 ^ 15 ≤ m := by
    by_contra hcon
    push_neg at hcon
    have : m ^ 2 < (2 ^ 15) ^ 2 := Nat.pow_lt_pow_left hcon (by norm_num)
    norm_num at this hN
    linarith
  have hs1 : 1 ≤ Nat.sqrt m := Nat.sqrt_pos.mpr (by omega)
  have hss : Nat.sqrt m * Nat.sqrt m ≤ m := Nat.sqrt_le m
  have hlt : m < (Nat.sqrt m + 1) * (Nat.sqrt m + 1) := Nat.lt_succ_sqrt m
  obtain ⟨p1, hp1, h1l, h1u⟩ := Nat.exists_prime_lt_and_le_two_mul (Nat.sqrt m + 1) (by omega)
  obtain ⟨p2, hp2, h2l, h2u⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (2 * (Nat.sqrt m + 1)) (by omega)
  have main : ∃ q, q.Prime ∧ ¬ q ∣ m ∧ q ≤ 4 * (Nat.sqrt m + 1) := by
    by_cases d1 : p1 ∣ m
    · by_cases d2 : p2 ∣ m
      · exfalso
        have hne : p1 ≠ p2 := by omega
        have hcop : Nat.Coprime p1 p2 := (Nat.coprime_primes hp1 hp2).mpr hne
        have hd := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop d1 d2
        have hle := Nat.le_of_dvd (by omega) hd
        nlinarith
      · exact ⟨p2, hp2, d2, by omega⟩
    · exact ⟨p1, hp1, d1, by omega⟩
  obtain ⟨q, hq, hqm, hqle⟩ := main
  have h64 : 64 ^ 10 ≤ m ^ 4 := by
    calc (64:ℕ) ^ 10 = (2 ^ 15) ^ 4 := by norm_num
      _ ≤ m ^ 4 := Nat.pow_le_pow_left hm15 4
  have hq2 : q * q ≤ 64 * m := by
    have := Nat.mul_le_mul hqle hqle
    nlinarith
  refine ⟨q, hq, ?_, ?_, ⟨(m:ℤ), by push_cast; simp⟩⟩
  · intro h
    exact hqm (hq.dvd_of_dvd_pow h)
  · apply real_bound_aux
    calc q ^ 20 = (q * q) ^ 10 := by ring
      _ ≤ (64 * m) ^ 10 := Nat.pow_le_pow_left hq2 10
      _ = 64 ^ 10 * m ^ 10 := by ring
      _ ≤ m ^ 4 * m ^ 10 := Nat.mul_le_mul_right _ h64
      _ = (m ^ 2) ^ 7 := by ring

end erdos_24202_neg_hyp_square_ns

instance (n : ℕ) : Decidable (TSProp n) :=
  decidable_of_iff (∀ k ≤ .sqrt (n - 1), Coprime n k → (n - k ^ 2).Prime) <| by
    cases n with
    | zero => simp [TSProp]
    | succ n' =>
      simp [TSProp, le_sqrt, pow_two]

theorem erdos_24202_neg_hyp_sieve :
    ∀ n k q : ℕ, q.Prime → Nat.Coprime n k → 4 * k ^ 2 ≤ n → q ∣ n - k ^ 2 →
      4 * q < 3 * n → ¬ TSProp n := by
  exact erdos_24202_neg_hyp_sieve_ns.erdos_24202_neg_hyp_sieve

theorem erdos_24202_neg_hyp_count :
    ∀ n q : ℕ, 1 ≤ n → 1 ≤ q → Nat.Coprime n q → ∀ (r : ℤ) (X : ℕ),
      (((Finset.Icc 1 X).filter
          (fun k : ℕ => (k : ℤ) % (q : ℤ) = r % (q : ℤ) ∧ Nat.Coprime k n)).card : ℝ)
        ≥ ((X : ℝ) / q) * ((n.totient : ℝ) / n) - (2 : ℝ) ^ n.primeFactors.card := by
  exact erdos_24202_neg_hyp_count_ns.erdos_24202_neg_hyp_count

theorem erdos_24202_neg_hyp_count_pos :
    ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → ∀ q : ℕ, q.Prime → (q : ℝ) ≤ (n : ℝ) ^ (0.35 : ℝ) →
      0 < (((Nat.sqrt n / 2 : ℕ) : ℝ) / q) * ((n.totient : ℝ) / n)
            - (2 : ℝ) ^ n.primeFactors.card := by
  exact erdos_24202_neg_hyp_count_pos_ns.erdos_24202_neg_hyp_count_pos

-- S6 (size of k): 2k ≤ Nat.sqrt n, so 4k² ≤ (Nat.sqrt n)² ≤ n.
namespace erdos_24202_neg_hyp_k_bound_ns
open Nat Set

theorem erdos_24202_neg_hyp_k_bound :
    ∀ n k : ℕ, k ≤ Nat.sqrt n / 2 → 4 * k ^ 2 ≤ n := by
  intro n k hk
  have h1 : 2 * k ≤ Nat.sqrt n := by omega
  have h2 : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
  have h3 : (2 * k) * (2 * k) ≤ Nat.sqrt n * Nat.sqrt n := Nat.mul_le_mul h1 h1
  calc 4 * k ^ 2 = (2 * k) * (2 * k) := by ring
    _ ≤ Nat.sqrt n * Nat.sqrt n := h3
    _ ≤ n := h2
end erdos_24202_neg_hyp_k_bound_ns

theorem erdos_24202_neg_hyp_k_bound :
    ∀ n k : ℕ, k ≤ Nat.sqrt n / 2 → 4 * k ^ 2 ≤ n := by
  exact erdos_24202_neg_hyp_k_bound_ns.erdos_24202_neg_hyp_k_bound



-- S6 (divisibility): k ≡ r (mod q) gives k² ≡ r² ≡ n (mod q); since k² ≤ n the ℕ-difference is the ℤ-difference.
namespace erdos_24202_neg_hyp_root_lift_ns
open Nat Set

theorem erdos_24202_neg_hyp_root_lift :
    ∀ n q k : ℕ, ∀ r : ℤ, q.Prime → (k : ℤ) % (q : ℤ) = r % (q : ℤ) →
      (q : ℤ) ∣ r ^ 2 - (n : ℤ) → 4 * k ^ 2 ≤ n → q ∣ n - k ^ 2 := by
  intro n q k r _ hkr hdiv hle
  have hk : k ^ 2 ≤ n := by
    have := Nat.zero_le (k ^ 2)
    linarith
  have hmod : (k : ℤ) ≡ r [ZMOD (q : ℤ)] := hkr
  have h2 : (q : ℤ) ∣ r ^ 2 - (k : ℤ) ^ 2 := (hmod.pow 2).dvd
  have h3 : (q : ℤ) ∣ (n : ℤ) - (k : ℤ) ^ 2 := by
    have := dvd_sub h2 hdiv
    have e : (r ^ 2 - (k : ℤ) ^ 2) - (r ^ 2 - (n : ℤ)) = (n : ℤ) - (k : ℤ) ^ 2 := by ring
    rwa [e] at this
  have h4 : ((n - k ^ 2 : ℕ) : ℤ) = (n : ℤ) - (k : ℤ) ^ 2 := by
    rw [Nat.cast_sub hk, Nat.cast_pow]
  rw [← h4] at h3
  exact Int.natCast_dvd_natCast.mp h3
end erdos_24202_neg_hyp_root_lift_ns

theorem erdos_24202_neg_hyp_root_lift :
    ∀ n q k : ℕ, ∀ r : ℤ, q.Prime → (k : ℤ) % (q : ℤ) = r % (q : ℤ) →
      (q : ℤ) ∣ r ^ 2 - (n : ℤ) → 4 * k ^ 2 ≤ n → q ∣ n - k ^ 2 := by
  exact erdos_24202_neg_hyp_root_lift_ns.erdos_24202_neg_hyp_root_lift



-- S6 (size of q): for n ≥ 2, n^0.35 < 3n/4, since n^0.65 ≥ 2^0.65 > 4/3.
namespace erdos_24202_neg_hyp_small_q_ns
open Nat Set

theorem erdos_24202_neg_hyp_small_q :
    ∀ n q : ℕ, 2 ≤ n → (q : ℝ) ≤ (n : ℝ) ^ (0.35 : ℝ) → 4 * q < 3 * n := by
  intro n q hn h
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hnpos : (0:ℝ) < (n:ℝ) := by linarith
  have hq0 : (0:ℝ) ≤ (q:ℝ) := by positivity
  have h1 : (q:ℝ) * q ≤ (n:ℝ) ^ (0.35:ℝ) * (n:ℝ) ^ (0.35:ℝ) :=
    mul_self_le_mul_self hq0 h
  have h2 : (n:ℝ) ^ (0.35:ℝ) * (n:ℝ) ^ (0.35:ℝ) = (n:ℝ) ^ (0.7:ℝ) := by
    rw [← Real.rpow_add hnpos]
    norm_num
  have h3 : (n:ℝ) ^ (0.7:ℝ) ≤ (n:ℝ) := by
    calc (n:ℝ) ^ (0.7:ℝ) ≤ (n:ℝ) ^ (1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
      _ = n := Real.rpow_one _
  have h4 : ((q * q : ℕ) : ℝ) ≤ (n:ℝ) := by
    push_cast
    linarith
  have h5 : q * q ≤ n := by exact_mod_cast h4
  by_contra hc
  push_neg at hc
  nlinarith [Nat.mul_le_mul hc hc, Nat.mul_le_mul hn (le_refl n)]
end erdos_24202_neg_hyp_small_q_ns

theorem erdos_24202_neg_hyp_small_q :
    ∀ n q : ℕ, 2 ≤ n → (q : ℝ) ≤ (n : ℝ) ^ (0.35 : ℝ) → 4 * q < 3 * n := by
  exact erdos_24202_neg_hyp_small_q_ns.erdos_24202_neg_hyp_small_q



-- S6: glue from sieve, count, count_pos and the three elementary lemmas above.
theorem erdos_24202_neg_hyp_good_kills :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ q : ℕ, GoodPrime n q → ¬ TSProp n := by
  obtain ⟨N₁, hN₁⟩ := erdos_24202_neg_hyp_count_pos
  refine ⟨max N₁ 2, fun n hn q hq => ?_⟩
  obtain ⟨hqp, hqn, hqle, r, hr⟩ := hq
  have hn1 : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hcop : Nat.Coprime n q := ((Nat.Prime.coprime_iff_not_dvd hqp).mpr hqn).symm
  have hpos := hN₁ n hn1 q hqp hqle
  have hcount := erdos_24202_neg_hyp_count n q (by omega) hqp.one_lt.le hcop r (Nat.sqrt n / 2)
  have hreal := lt_of_lt_of_le hpos hcount
  have hcard : 0 < ((Finset.Icc 1 (Nat.sqrt n / 2)).filter
      (fun k : ℕ => (k : ℤ) % (q : ℤ) = r % (q : ℤ) ∧ Nat.Coprime k n)).card := by
    exact_mod_cast hreal
  obtain ⟨k, hk⟩ := Finset.card_pos.mp hcard
  rw [Finset.mem_filter, Finset.mem_Icc] at hk
  obtain ⟨⟨_, hkX⟩, hkr, hkc⟩ := hk
  have h4 := erdos_24202_neg_hyp_k_bound n k hkX
  have hdiv := erdos_24202_neg_hyp_root_lift n q k r hqp hkr hr h4
  exact erdos_24202_neg_hyp_sieve n k q hqp hkc.symm h4 hdiv
    (erdos_24202_neg_hyp_small_q n q hn2 hqle)

theorem erdos_24202_neg_hyp_square :
    ∃ N₂ : ℕ, ∀ m : ℕ, 1 ≤ m → N₂ ≤ m ^ 2 → ∃ q : ℕ, GoodPrime (m ^ 2) q := by
  exact erdos_24202_neg_hyp_square_ns.erdos_24202_neg_hyp_square

-- PUBLISHED: Davenport, Multiplicative Number Theory, Ch. 5 (Kronecker symbol χ_D induced to modulus 4n);
-- stated through its consequence: χ(p) = 1 forces p ∤ 4n and (n/p) = 1.
namespace erdos_24202_neg_hyp_kronecker_ns
open Nat Set

-- CHECK: Nat.sq_mul_squarefree_of_pos ZMod.isUnit_iff_coprime MulChar.one_apply Nat.Prime.coprime_iff_not_dvd Nat.Coprime.coprime_dvd_right jacobiSym.mod_right MulChar.map_nonunit
-- S8.2 + S8.3 + S8.4: chi(x) := J(n | val x) on units, 0 off units, is a Dirichlet character mod 4n
-- (periodicity is jacobiSym.mod_right, multiplicativity is jacobiSym.mul_right).
namespace erdos_24202_neg_hyp_kronecker_hyp_char_ns
-- CHECK: jacobiSym.mod_right jacobiSym.mul_right jacobiSym.eq_zero_iff_not_coprime ZMod.isUnit_iff_coprime ZMod.val_natCast Int.gcd_natCast_natCast
open Nat Set

private lemma odd_mod4 (n b : ℕ) : Odd (b % (4 * n)) ↔ Odd b := by
  simp only [Nat.odd_iff]
  rw [Nat.mod_mod_of_dvd b ⟨2 * n, by ring⟩]

private lemma J_mod (n b : ℕ) (hb : Odd b) :
    jacobiSym (n : ℤ) (b % (4 * n)) = jacobiSym (n : ℤ) b := by
  rw [jacobiSym.mod_right (n : ℤ) hb]
  simp

private lemma cop4 (n a : ℕ) (ha : Odd a) (hn : Nat.gcd n a = 1) :
    Nat.Coprime a (4 * n) := by
  apply Nat.Coprime.mul_right
  · have h2 : Nat.Coprime 2 a :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by obtain ⟨t, ht⟩ := ha; omega)
    have h4 : Nat.Coprime (2 ^ 2) a := Nat.Coprime.pow_left 2 h2
    exact Nat.Coprime.symm h4
  · exact Nat.Coprime.symm hn

private lemma gcd_conv (n b : ℕ) (hg : Int.gcd (n : ℤ) (b : ℤ) = 1) : Nat.gcd n b = 1 := by
  first
  | (rw [Int.gcd_natCast_natCast] at hg; exact hg)
  | exact hg
  | simpa using hg

private lemma odd_of_cop (n a : ℕ) (ha : Nat.Coprime a (4 * n)) : Odd a := by
  have h2 : ¬ 2 ∣ a := fun hd => by
    have h3 := Nat.dvd_gcd hd (show 2 ∣ 4 * n from ⟨2 * n, by ring⟩)
    rw [Nat.Coprime.gcd_eq_one ha] at h3
    omega
  exact Nat.odd_iff.2 (by omega)

-- PUBLISHED: Davenport, Multiplicative Number Theory, Ch. 5 (Kronecker symbol χ_D induced to modulus 4n);
-- stated through its consequence: χ(p) = 1 forces p ∤ 4n and (n/p) = 1.
open Nat Set

theorem erdos_24202_neg_hyp_kronecker_hyp_char :
    ∀ n : ℕ, 1 ≤ n →
      ∃ χ : DirichletCharacter ℂ (4 * n),
        (∀ a : ℕ, Nat.Coprime a (4 * n) →
            χ (a : ZMod (4 * n)) = ((jacobiSym (n : ℤ) a : ℤ) : ℂ)) ∧
        (∀ a : ℕ, ¬ Nat.Coprime a (4 * n) → χ (a : ZMod (4 * n)) = 0) := by
  intro n hn
  haveI : NeZero (4 * n) := ⟨by omega⟩
  let f : ZMod (4 * n) → ℂ := fun x =>
    if Odd x.val then ((jacobiSym (n : ℤ) x.val : ℤ) : ℂ) else 0
  have hf1 : f 1 = 1 := by
    have h1 : (1 : ZMod (4 * n)).val = 1 := by
      rw [ZMod.val_one_eq_one_mod]
      exact Nat.mod_eq_of_lt (by omega)
    simp [f, h1, jacobiSym.one_right]
  have hfm : ∀ x y : ZMod (4 * n), f (x * y) = f x * f y := by
    intro x y
    simp only [f]
    rw [ZMod.val_mul]
    by_cases hx : Odd x.val <;> by_cases hy : Odd y.val
    · have hxy : Odd (x.val * y.val) := hx.mul hy
      haveI : NeZero x.val := ⟨by obtain ⟨t, ht⟩ := hx; omega⟩
      haveI : NeZero y.val := ⟨by obtain ⟨t, ht⟩ := hy; omega⟩
      rw [if_pos ((odd_mod4 n _).2 hxy), if_pos hx, if_pos hy, J_mod n _ hxy,
        jacobiSym.mul_right, Int.cast_mul]
    all_goals
      have hxy : ¬ Odd (x.val * y.val) := fun h => by
        have := Nat.odd_mul.1 h
        tauto
      rw [if_neg (fun h => hxy ((odd_mod4 n _).1 h))]
      simp [hx, hy]
  have hnon : ∀ a : ZMod (4 * n), ¬ IsUnit a → f a = 0 := by
    intro a ha
    simp only [f]
    split_ifs with h
    · haveI : NeZero a.val := ⟨by obtain ⟨t, ht⟩ := h; omega⟩
      have hJ : jacobiSym (n : ℤ) a.val = 0 := by
        rw [jacobiSym.eq_zero_iff_not_coprime]
        intro hg
        apply ha
        have hcop := cop4 n a.val h (gcd_conv n a.val hg)
        rw [← ZMod.natCast_zmod_val a]
        first
        | exact (ZMod.isUnit_iff_coprime _ _).2 hcop
        | exact ⟨ZMod.unitOfCoprime _ hcop, rfl⟩
      rw [hJ]
      simp
    · rfl
  let χ : DirichletCharacter ℂ (4 * n) :=
    { toFun := f, map_one' := hf1, map_mul' := hfm, map_nonunit' := hnon }
  refine ⟨χ, ?_, ?_⟩
  · intro a ha
    show f (a : ZMod (4 * n)) = _
    simp only [f]
    rw [ZMod.val_natCast]
    have hodd : Odd a := odd_of_cop n a ha
    rw [if_pos ((odd_mod4 n a).2 hodd), J_mod n a hodd]
  · intro a ha
    show f (a : ZMod (4 * n)) = 0
    simp only [f]
    rw [ZMod.val_natCast]
    split_ifs with h
    · have hodd := (odd_mod4 n a).1 h
      haveI : NeZero a := ⟨by obtain ⟨t, ht⟩ := hodd; omega⟩
      rw [J_mod n a hodd]
      have hJ : jacobiSym (n : ℤ) a = 0 := by
        rw [jacobiSym.eq_zero_iff_not_coprime]
        intro hg
        exact ha (cop4 n a hodd (gcd_conv n a hg))
      rw [hJ]
      simp
    · rfl
end erdos_24202_neg_hyp_kronecker_hyp_char_ns

theorem erdos_24202_neg_hyp_kronecker_hyp_char :
    ∀ n : ℕ, 1 ≤ n →
      ∃ χ : DirichletCharacter ℂ (4 * n),
        (∀ a : ℕ, Nat.Coprime a (4 * n) →
            χ (a : ZMod (4 * n)) = ((jacobiSym (n : ℤ) a : ℤ) : ℂ)) ∧
        (∀ a : ℕ, ¬ Nat.Coprime a (4 * n) → χ (a : ZMod (4 * n)) = 0) := by
  exact erdos_24202_neg_hyp_kronecker_hyp_char_ns.erdos_24202_neg_hyp_kronecker_hyp_char



-- S8.8: CRT a ≡ 1 mod 8, a ≡ nonresidue mod q, a ≡ 1 mod other odd primes of n; reciprocity gives J(n|a) = -1.
namespace erdos_24202_neg_hyp_kronecker_hyp_odd_ns
-- CHECK: Nat.exists_eq_pow_mul_and_not_dvd FiniteField.exists_nonsquare ZMod.nonsquare_iff_jacobiSym_eq_neg_one jacobiSym.mod_right' jacobiSym.quadratic_reciprocity_one_mod_four jacobiSym.mod_left'
open Nat Set

private lemma split_pow_aux (m q : ℕ) (hm : m ≠ 0) (hq : q.Prime) :
    ∃ i s : ℕ, ¬ q ∣ s ∧ m = q ^ i * s := by
  first
  | exact Nat.exists_eq_pow_mul_and_not_dvd hm q hq.ne_one
  | exact ⟨_, _, Nat.not_dvd_ordCompl hq hm, (Nat.ordProj_mul_ordCompl_eq_self m q).symm⟩

-- PUBLISHED: Davenport, Multiplicative Number Theory, Ch. 5 (Kronecker symbol χ_D induced to modulus 4n);
-- stated through its consequence: χ(p) = 1 forces p ∤ 4n and (n/p) = 1.
open Nat Set

theorem erdos_24202_neg_hyp_kronecker_hyp_odd :
    ∀ n d m : ℕ, n = d * m ^ 2 → Squarefree d → 2 ≤ d →
      (∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ∣ d) → 0 < m →
        ∃ a : ℕ, Nat.Coprime a (4 * n) ∧ jacobiSym (n : ℤ) a = -1 := by
  intro n d m hn hsq hd2 hq hm
  obtain ⟨q, hqp, hq2, hqd⟩ := hq
  obtain ⟨d', rfl⟩ := hqd
  have hd' : ¬ q ∣ d' := by
    rintro ⟨c, rfl⟩
    have hu := hsq q ⟨c, by ring⟩
    exact hqp.ne_one (Nat.isUnit_iff.mp hu)
  obtain ⟨i, s, hs, rfl⟩ := split_pow_aux m q (by omega) hqp
  have hd'0 : 0 < d' := Nat.pos_of_ne_zero (by rintro rfl; simp at hd2)
  have hs0 : 0 < s := Nat.pos_of_ne_zero (by rintro rfl; simp at hm)
  have hqt : ¬ q ∣ d' * s ^ 2 := by
    intro h
    rcases (Nat.Prime.dvd_mul hqp).mp h with h | h
    · exact hd' h
    · exact hs (hqp.dvd_of_dvd_pow h)
  have htpos : 0 < d' * s ^ 2 := by positivity
  have hnt : n = q ^ (2 * i + 1) * (d' * s ^ 2) := by rw [hn]; ring
  subst hnt
  generalize d' * s ^ 2 = t at hqt htpos ⊢
  have hq8t : Nat.Coprime (8 * t) q := by
    apply Nat.Coprime.symm
    rw [Nat.Prime.coprime_iff_not_dvd hqp]
    intro h
    rcases (Nat.Prime.dvd_mul hqp).mp h with h | h
    · have hle := Nat.le_of_dvd (by norm_num) h
      interval_cases q <;> first
        | omega
        | exact absurd hqp (by norm_num)
        | exact absurd h (by norm_num)
    · exact hqt h
  haveI := Fact.mk hqp
  obtain ⟨x, hx⟩ := FiniteField.exists_nonsquare (F := ZMod q)
    (by rw [ZMod.ringChar_zmod_n]; exact hq2)
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx ⟨0, by simp⟩
  have hgx : ((x.val : ℕ) : ZMod q) = x := ZMod.natCast_zmod_val x
  have hqg : ¬ q ∣ x.val := by
    intro h
    apply hx0
    rw [← hgx]
    obtain ⟨c, hc⟩ := h
    rw [hc]
    push_cast
    simp
  obtain ⟨a, ha1, hag⟩ := Nat.chineseRemainder hq8t 1 x.val
  have ha1' : a % (8 * t) = 1 % (8 * t) := ha1
  have hag' : a % q = x.val % q := hag
  have ha8 : a % (8 * t) = 1 := by
    rw [ha1']; exact Nat.mod_eq_of_lt (by omega)
  have ha4 : a % 4 = 1 := by
    have h := Nat.mod_mod_of_dvd a (show 4 ∣ 8 * t from ⟨2 * t, by ring⟩)
    rw [ha8] at h
    omega
  have ha4t : a % (4 * t) = 1 := by
    have h := Nat.mod_mod_of_dvd a (show 4 * t ∣ 8 * t from ⟨2, by ring⟩)
    rw [ha8] at h
    rw [← h]
    exact Nat.mod_eq_of_lt (by omega)
  have hodd : Odd a := Nat.odd_iff.mpr (by omega)
  have hqodd : Odd q := hqp.odd_of_ne_two hq2
  have hca8 : Nat.Coprime a (8 * t) := by
    show Nat.gcd a (8 * t) = 1
    rw [Nat.gcd_comm, Nat.gcd_rec, ha8, Nat.gcd_one_left]
  have hcaq : Nat.Coprime a q := by
    show Nat.gcd a q = 1
    rw [Nat.gcd_comm, Nat.gcd_rec, hag', ← Nat.gcd_rec, Nat.gcd_comm]
    exact ((Nat.Prime.coprime_iff_not_dvd hqp).mpr hqg).symm
  refine ⟨a, ?_, ?_⟩
  · have e : 4 * (q ^ (2 * i + 1) * t) = q ^ (2 * i + 1) * (4 * t) := by ring
    rw [e]
    exact Nat.Coprime.mul_right (Nat.Coprime.pow_right _ hcaq)
      (Nat.Coprime.coprime_dvd_right ⟨2, by ring⟩ hca8)
  · push_cast
    rw [jacobiSym.mul_left, jacobiSym.pow_left]
    have h1 : jacobiSym (t : ℤ) a = 1 := by
      rw [jacobiSym.mod_right' t hodd, ha4t, jacobiSym.one_right]
    have h2 : jacobiSym (q : ℤ) a = -1 := by
      rw [← jacobiSym.quadratic_reciprocity_one_mod_four ha4 hqodd]
      rw [jacobiSym.mod_left' (a₂ := ((x.val : ℕ) : ℤ)) (by exact_mod_cast hag')]
      rw [ZMod.nonsquare_iff_jacobiSym_eq_neg_one]
      first
        | (rw [Int.cast_natCast, hgx]; exact hx)
        | simpa [hgx] using hx
    rw [h1, h2, pow_succ, pow_mul]
    norm_num
end erdos_24202_neg_hyp_kronecker_hyp_odd_ns

theorem erdos_24202_neg_hyp_kronecker_hyp_odd :
    ∀ n d m : ℕ, n = d * m ^ 2 → Squarefree d → 2 ≤ d →
      (∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ∣ d) → 0 < m →
        ∃ a : ℕ, Nat.Coprime a (4 * n) ∧ jacobiSym (n : ℤ) a = -1 := by
  exact erdos_24202_neg_hyp_kronecker_hyp_odd_ns.erdos_24202_neg_hyp_kronecker_hyp_odd



-- S8.9: CRT a ≡ 5 mod 8, a ≡ 1 mod odd primes of m; J(2|a) = -1 by the second supplementary law.
namespace erdos_24202_neg_hyp_kronecker_hyp_two_ns

-- CHECK: Nat.exists_eq_two_pow_mul_odd jacobiSym.mul_left jacobiSym.at_two jacobiSym.sq_one' ZMod.χ₈_nat_eq_if_mod_eight Int.gcd_natCast_natCast
open Nat Set

theorem erdos_24202_neg_hyp_kronecker_hyp_two :
    ∀ n m : ℕ, n = 2 * m ^ 2 → 0 < m →
      ∃ a : ℕ, Nat.Coprime a (4 * n) ∧ jacobiSym (n : ℤ) a = -1 := by
  intro n m hn hm
  obtain ⟨e, o, ho, hmo⟩ := Nat.exists_eq_two_pow_mul_odd (n := m) (by omega)
  obtain ⟨j, hj⟩ := ho
  have h2 : Nat.Coprime (4 * o + 1) 2 := by
    show Nat.gcd _ _ = 1
    have h1 := Nat.gcd_dvd_left (4 * o + 1) 2
    have h2' := Nat.gcd_dvd_right (4 * o + 1) 2
    have h3 : Nat.gcd (4 * o + 1) 2 ∣ 4 * o :=
      Dvd.dvd.mul_right (dvd_trans h2' (by norm_num)) o
    exact Nat.dvd_one.mp ((Nat.dvd_add_right h3).mp h1)
  have ho' : Nat.Coprime (4 * o + 1) o := by
    show Nat.gcd _ _ = 1
    have h1 := Nat.gcd_dvd_left (4 * o + 1) o
    have h2' := Nat.gcd_dvd_right (4 * o + 1) o
    have h3 : Nat.gcd (4 * o + 1) o ∣ 4 * o := Dvd.dvd.mul_left h2' 4
    exact Nat.dvd_one.mp ((Nat.dvd_add_right h3).mp h1)
  have h4n : 4 * n = 2 ^ (2 * e + 3) * o ^ 2 := by
    rw [hn, hmo]; ring
  have hcop : Nat.Coprime (4 * o + 1) (4 * n) := by
    rw [h4n]
    exact Nat.Coprime.mul_right (Nat.Coprime.pow_right _ h2) (Nat.Coprime.pow_right _ ho')
  have hmc : Nat.Coprime (4 * o + 1) m :=
    Nat.Coprime.coprime_dvd_right ⟨8 * m, by rw [hn]; ring⟩ hcop
  refine ⟨4 * o + 1, hcop, ?_⟩
  have hodd : Odd (4 * o + 1) := ⟨2 * o, by ring⟩
  have hcast : (n : ℤ) = 2 * (m : ℤ) ^ 2 := by rw [hn]; push_cast; ring
  rw [hcast, jacobiSym.mul_left, jacobiSym.at_two hodd, jacobiSym.sq_one' ?_]
  · rw [ZMod.χ₈_nat_eq_if_mod_eight, if_neg (by omega), if_neg (by omega)]
    norm_num
  · rw [Int.gcd_natCast_natCast]
    exact hmc.symm

end erdos_24202_neg_hyp_kronecker_hyp_two_ns

theorem erdos_24202_neg_hyp_kronecker_hyp_two :
    ∀ n m : ℕ, n = 2 * m ^ 2 → 0 < m →
      ∃ a : ℕ, Nat.Coprime a (4 * n) ∧ jacobiSym (n : ℤ) a = -1 := by
  exact erdos_24202_neg_hyp_kronecker_hyp_two_ns.erdos_24202_neg_hyp_kronecker_hyp_two

-- S8.10 step 4: a squarefree d ≥ 2 with no odd prime factor is a power of 2, hence d = 2.
namespace erdos_24202_neg_hyp_kronecker_hyp_pow2_ns

open Nat Set

theorem erdos_24202_neg_hyp_kronecker_hyp_pow2 :
    ∀ d : ℕ, Squarefree d → 2 ≤ d → (¬ ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ∣ d) → d = 2 := by
  intro d hsq hd hno
  have key : ∀ p, p.Prime → p ∣ d → p = 2 := by
    intro p hp hpd
    by_contra hne
    exact hno ⟨p, hp, hne, hpd⟩
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show d ≠ 1 by omega)
  have hp2 := key p hp hpd
  subst hp2
  obtain ⟨e, rfl⟩ := hpd
  by_cases he : e = 1
  · subst he
    norm_num
  · exfalso
    obtain ⟨q, hq, hqe⟩ := Nat.exists_prime_and_dvd he
    have hq2 := key q hq (dvd_mul_of_dvd_right hqe 2)
    subst hq2
    have h4 : 2 * 2 ∣ 2 * e := mul_dvd_mul_left 2 hqe
    have hu := hsq 2 h4
    rw [Nat.isUnit_iff] at hu
    omega

end erdos_24202_neg_hyp_kronecker_hyp_pow2_ns

theorem erdos_24202_neg_hyp_kronecker_hyp_pow2 :
    ∀ d : ℕ, Squarefree d → 2 ≤ d → (¬ ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ∣ d) → d = 2 := by
  exact erdos_24202_neg_hyp_kronecker_hyp_pow2_ns.erdos_24202_neg_hyp_kronecker_hyp_pow2

-- S8.1(g) + S8.5(ii): for an odd prime p ∤ n, J(n|p) is the Legendre symbol; value 1 means n is a square mod p.
namespace erdos_24202_neg_hyp_kronecker_hyp_sq_ns

-- CHECK: ZMod.isSquare_of_jacobiSym_eq_one ZMod.intCast_zmod_eq_zero_iff_dvd ZMod.natCast_zmod_val
open Nat Set

theorem erdos_24202_neg_hyp_kronecker_hyp_sq :
    ∀ n p : ℕ, p.Prime → Nat.Coprime p (4 * n) → jacobiSym (n : ℤ) p = 1 →
      ∃ r : ℤ, (p : ℤ) ∣ r ^ 2 - (n : ℤ) := by
  intro n p hp _ hJ
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨c, hc⟩ := ZMod.isSquare_of_jacobiSym_eq_one hJ
  refine ⟨(c.val : ℤ), ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast at hc ⊢
  rw [ZMod.natCast_zmod_val]
  linear_combination -hc

end erdos_24202_neg_hyp_kronecker_hyp_sq_ns

theorem erdos_24202_neg_hyp_kronecker_hyp_sq :
    ∀ n p : ℕ, p.Prime → Nat.Coprime p (4 * n) → jacobiSym (n : ℤ) p = 1 →
      ∃ r : ℤ, (p : ℤ) ∣ r ^ 2 - (n : ℤ) := by
  exact erdos_24202_neg_hyp_kronecker_hyp_sq_ns.erdos_24202_neg_hyp_kronecker_hyp_sq

theorem erdos_24202_neg_hyp_kronecker :
    ∀ n : ℕ, 1 ≤ n → (¬ ∃ m : ℕ, n = m ^ 2) →
      ∃ χ : DirichletCharacter ℂ (4 * n), χ ≠ 1 ∧
        ∀ p : ℕ, p.Prime → χ (p : ZMod (4 * n)) = 1 →
          ¬ p ∣ n ∧ ∃ r : ℤ, (p : ℤ) ∣ r ^ 2 - (n : ℤ) := by
  intro n hn hns
  obtain ⟨χ, hcop, hncop⟩ := erdos_24202_neg_hyp_kronecker_hyp_char n hn
  have hneg : ∃ a : ℕ, Nat.Coprime a (4 * n) ∧ jacobiSym (n : ℤ) a = -1 := by
    obtain ⟨a, b, ha, hb, hab, hsq⟩ := Nat.sq_mul_squarefree_of_pos (by omega : 0 < n)
    have hab' : n = a * b ^ 2 := by rw [← hab]; ring
    have ha1 : a ≠ 1 := by
      rintro rfl
      exact hns ⟨b, by rw [← hab]; ring⟩
    have ha2 : 2 ≤ a := by omega
    by_cases hq : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ∣ a
    · exact erdos_24202_neg_hyp_kronecker_hyp_odd n a b hab' hsq ha2 hq hb
    · have h2 : a = 2 := erdos_24202_neg_hyp_kronecker_hyp_pow2 a hsq ha2 hq
      subst h2
      exact erdos_24202_neg_hyp_kronecker_hyp_two n b hab' hb
  refine ⟨χ, ?_, ?_⟩
  · intro h
    obtain ⟨a, ha, hja⟩ := hneg
    have hu : IsUnit (a : ZMod (4 * n)) := (ZMod.isUnit_iff_coprime a (4 * n)).mpr ha
    have h1 := hcop a ha
    rw [h, MulChar.one_apply hu, hja] at h1
    norm_num at h1
  · intro p hp hχ
    have hc : Nat.Coprime p (4 * n) := by
      by_contra hc
      rw [hncop p hc] at hχ
      exact zero_ne_one hχ
    have hj : jacobiSym (n : ℤ) p = 1 := by
      have := hcop p hc
      rw [hχ] at this
      exact_mod_cast this.symm
    refine ⟨?_, erdos_24202_neg_hyp_kronecker_hyp_sq n p hp hc hj⟩
    have hpn : Nat.Coprime p n := Nat.Coprime.coprime_dvd_right (dvd_mul_left n 4) hc
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp hpn
end erdos_24202_neg_hyp_kronecker_ns

theorem erdos_24202_neg_hyp_kronecker :
    ∀ n : ℕ, 1 ≤ n → (¬ ∃ m : ℕ, n = m ^ 2) →
      ∃ χ : DirichletCharacter ℂ (4 * n), χ ≠ 1 ∧
        ∀ p : ℕ, p.Prime → χ (p : ZMod (4 * n)) = 1 →
          ¬ p ∣ n ∧ ∃ r : ℤ, (p : ℤ) ∣ r ^ 2 - (n : ℤ) := by
  exact erdos_24202_neg_hyp_kronecker_ns.erdos_24202_neg_hyp_kronecker



-- PUBLISHED: Linnik–Vinogradov 1966; P. Pollack, Proc. AMS 142 (2014), least prime with χ(p) = 1.
theorem erdos_24202_neg_hyp_linnik :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ χ : DirichletCharacter ℂ Q, χ ≠ 1 →
      ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ C * (Q : ℝ) ^ ((1 : ℝ) / 4 + ε) ∧ χ (p : ZMod Q) = 1 := by
  sorry

-- S10 (arithmetic): C·4^0.3·n^0.3 ≤ n^0.35 once n^0.05 ≥ C·4^0.3, i.e. for n ≥ (C·4^0.3)^20.
namespace erdos_24202_neg_hyp_rpow_absorb_ns
open Nat Set

theorem erdos_24202_neg_hyp_rpow_absorb :
    ∀ C : ℝ, 0 < C → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      C * (((4 * n : ℕ) : ℝ)) ^ ((1 : ℝ) / 4 + (0.05 : ℝ)) ≤ (n : ℝ) ^ (0.35 : ℝ) := by
  intro C hC
  refine ⟨⌈(4 * C) ^ (20:ℝ)⌉₊, fun n hn => ?_⟩
  have hpos : (0:ℝ) < (4 * C) ^ (20:ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hnge : (4 * C) ^ (20:ℝ) ≤ (n:ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
  have hnpos : (0:ℝ) < n := lt_of_lt_of_le hpos hnge
  have he : (1:ℝ) / 4 + (0.05:ℝ) = 0.3 := by norm_num
  rw [he]
  have hcast : (((4 * n : ℕ) : ℝ)) = 4 * (n:ℝ) := by norm_num
  rw [hcast, Real.mul_rpow (by norm_num) hnpos.le]
  have h4 : (4:ℝ) ^ (0.3:ℝ) ≤ 4 := by
    have := Real.rpow_le_rpow_of_exponent_le (x := (4:ℝ)) (by norm_num)
      (show (0.3:ℝ) ≤ 1 by norm_num)
    simpa using this
  have hsmall : 4 * C ≤ (n:ℝ) ^ (0.05:ℝ) := by
    have h1 := Real.rpow_le_rpow hpos.le hnge (show (0:ℝ) ≤ 0.05 by norm_num)
    rw [← Real.rpow_mul (by linarith)] at h1
    have h20 : (20:ℝ) * 0.05 = 1 := by norm_num
    rw [h20, Real.rpow_one] at h1
    exact h1
  have hsplit : (n:ℝ) ^ (0.35:ℝ) = (n:ℝ) ^ (0.3:ℝ) * (n:ℝ) ^ (0.05:ℝ) := by
    rw [← Real.rpow_add hnpos]
    congr 1
    norm_num
  rw [hsplit]
  have hA : 0 ≤ (n:ℝ) ^ (0.3:ℝ) := Real.rpow_nonneg hnpos.le _
  calc C * ((4:ℝ) ^ (0.3:ℝ) * (n:ℝ) ^ (0.3:ℝ))
      ≤ C * (4 * (n:ℝ) ^ (0.3:ℝ)) := by gcongr
    _ = (4 * C) * (n:ℝ) ^ (0.3:ℝ) := by ring
    _ ≤ (n:ℝ) ^ (0.05:ℝ) * (n:ℝ) ^ (0.3:ℝ) := by gcongr
    _ = (n:ℝ) ^ (0.3:ℝ) * (n:ℝ) ^ (0.05:ℝ) := by ring
end erdos_24202_neg_hyp_rpow_absorb_ns

theorem erdos_24202_neg_hyp_rpow_absorb :
    ∀ C : ℝ, 0 < C → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      C * (((4 * n : ℕ) : ℝ)) ^ ((1 : ℝ) / 4 + (0.05 : ℝ)) ≤ (n : ℝ) ^ (0.35 : ℝ) := by
  exact erdos_24202_neg_hyp_rpow_absorb_ns.erdos_24202_neg_hyp_rpow_absorb



-- S10: glue from kronecker, linnik (ε = 0.05, Q = 4n) and rpow_absorb.
theorem erdos_24202_neg_hyp_nonsquare :
    ∃ N₃ : ℕ, ∀ n : ℕ, N₃ ≤ n → (¬ ∃ m : ℕ, n = m ^ 2) → ∃ q : ℕ, GoodPrime n q := by
  obtain ⟨C, hC, hlin⟩ := erdos_24202_neg_hyp_linnik (0.05 : ℝ) (by norm_num)
  obtain ⟨N, hN⟩ := erdos_24202_neg_hyp_rpow_absorb C hC
  refine ⟨max N 1, fun n hn hns => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  obtain ⟨χ, hχ1, hχ⟩ := erdos_24202_neg_hyp_kronecker n hn1 hns
  obtain ⟨p, hp, hple, hpχ⟩ := hlin (4 * n) (by omega) χ hχ1
  obtain ⟨hpn, r, hr⟩ := hχ p hp hpχ
  exact ⟨p, hp, hpn, le_trans hple (hN n hnN), r, hr⟩

theorem erdos_24202_neg :
    ¬ (Infinite { n | TSProp n }) := by
  intro hinf
  obtain ⟨N₁, hN₁⟩ := erdos_24202_neg_hyp_good_kills
  obtain ⟨N₂, hN₂⟩ := erdos_24202_neg_hyp_square
  obtain ⟨N₃, hN₃⟩ := erdos_24202_neg_hyp_nonsquare
  have hfin : Set.Finite { n | TSProp n } := by
    apply (Set.finite_Iio (max (max N₁ N₂) (max N₃ 2))).subset
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    simp only [Set.mem_Iio]
    by_contra hlt
    push_neg at hlt
    have h1 : N₁ ≤ n := ((le_max_left N₁ N₂).trans (le_max_left _ _)).trans hlt
    have h2 : N₂ ≤ n := ((le_max_right N₁ N₂).trans (le_max_left _ _)).trans hlt
    have h3 : N₃ ≤ n := ((le_max_left N₃ 2).trans (le_max_right _ _)).trans hlt
    have h4 : 2 ≤ n := ((le_max_right N₃ 2).trans (le_max_right _ _)).trans hlt
    by_cases hsq : ∃ m : ℕ, n = m ^ 2
    · obtain ⟨m, rfl⟩ := hsq
      have hm : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with h | h
        · subst h
          norm_num at h4
        · exact h
      obtain ⟨q, hq⟩ := hN₂ m hm h2
      exact hN₁ (m ^ 2) h1 q hq hn
    · obtain ⟨q, hq⟩ := hN₃ n h3 hsq
      exact hN₁ n h1 q hq hn
  have hinf' : Set.Infinite { n | TSProp n } := by
    first
    | exact Set.infinite_coe_iff.mp hinf
    | exact hinf
  exact hinf' hfin
