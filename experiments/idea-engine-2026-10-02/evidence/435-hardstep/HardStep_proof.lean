def erdos_727285_Rep (n : ℕ) (m : ℤ) : Prop :=
  ∃ c : ℕ → ℕ, m = ∑ i ∈ Finset.Ico 1 n, (c i : ℤ) * (n.choose i : ℤ)

def erdos_727285_X (n : ℕ) : ℤ :=
  ∑ p ∈ n.primeFactors,
    (∑ d ∈ Finset.Icc 1 (n.factorization p), (n.choose (p ^ d) : ℤ)) * ((p : ℤ) - 1)

def erdos_727285_Good (n : ℕ) : Prop :=
  n ≠ 0 ∧ ∀ p k : ℕ, p.Prime → n ≠ p ^ k

open Classical in
noncomputable def erdos_727285_digits (n p : ℕ) (r : ℤ) : ℕ → ℕ :=
  if h : ∃ e : ℕ → ℕ, (∀ d, e d < p) ∧
      (∀ d, d ∉ Finset.Icc 1 (n.factorization p) → e d = 0) ∧
      ((p : ℤ) ^ (n.factorization p) ∣
        r - ∑ d ∈ Finset.Icc 1 (n.factorization p), (e d : ℤ) * (n.choose (p ^ d) : ℤ))
  then Classical.choose h else fun _ => 0

noncomputable def erdos_727285_phiP (n p : ℕ) (r : ℤ) : ℤ :=
  ∑ d ∈ Finset.Icc 1 (n.factorization p),
    (erdos_727285_digits n p r d : ℤ) * (n.choose (p ^ d) : ℤ)

noncomputable def erdos_727285_phi (n : ℕ) (r : ℤ) : ℤ :=
  ∑ p ∈ n.primeFactors, erdos_727285_phiP n p r

def erdos_727285_gens (n : ℕ) : Set ℤ :=
  insert (n : ℤ) {g | ∃ p ∈ n.primeFactors, ∃ d ∈ Finset.Icc 1 (n.factorization p),
    g = (n.choose (p ^ d) : ℤ)}

def erdos_727285_T (n : ℕ) : AddSubmonoid ℤ :=
  AddSubmonoid.closure (erdos_727285_gens n)

def erdos_727285_J (n i q : ℕ) : ℕ :=
  n.factorization q - (n.choose i).factorization q

def erdos_727285_R (n i : ℕ) : ℕ :=
  ∑ q ∈ n.primeFactors, (q - 1) *
    ∑ d ∈ Finset.Icc 1 (erdos_727285_J n i q), n.choose (q ^ d)

def erdos_727285_NotTower (n i : ℕ) : Prop :=
  ∀ p ∈ n.primeFactors, ∀ j ∈ Finset.Icc 1 (n.factorization p), i ≠ p ^ j

def erdos_727285_Jstar (i q : ℕ) : ℕ :=
  if i = q ^ (i.factorization q) then i.factorization q - 1 else i.factorization q

namespace erdos_727285_hyp_S7_phi_basic_ns
open Classical in

private lemma e7_modp_aux (p A : ℕ) (hp : 1 ≤ p) (hA : 1 ≤ A) :
    (p * A - 1) % p = p - 1 ∧ (p * A - 1) / p = A - 1 := by
  have h : p * A - 1 = (p - 1) + p * (A - 1) := by
    obtain ⟨A', rfl⟩ : ∃ A', A = A' + 1 := ⟨A - 1, by omega⟩
    have e : p * (A' + 1) = p * A' + p := by ring
    rw [e, Nat.add_sub_cancel]
    omega
  rw [h]
  refine ⟨?_, ?_⟩
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega), zero_add]

private lemma e7_luc (p : ℕ) (hp : p.Prime) (t : ℕ) (ht : 1 ≤ t) :
    ∀ d : ℕ, ¬ p ∣ (p ^ d * t - 1).choose (p ^ d - 1) := by
  haveI := Fact.mk hp
  intro d
  induction d with
  | zero =>
    intro h
    simp at h
    exact hp.ne_one h
  | succ d ih =>
    have hB : 1 ≤ p ^ d := Nat.one_le_pow _ _ hp.pos
    have hA : 1 ≤ p ^ d * t := by
      have := Nat.mul_le_mul hB ht
      simpa using this
    obtain ⟨hNm, hNd⟩ := e7_modp_aux p (p ^ d * t) hp.one_lt.le hA
    obtain ⟨hKm, hKd⟩ := e7_modp_aux p (p ^ d) hp.one_lt.le hB
    have e1 : p ^ (d + 1) * t = p * (p ^ d * t) := by rw [pow_succ', mul_assoc]
    have e2 : p ^ (d + 1) = p * p ^ d := pow_succ' p d
    rw [e1, e2]
    intro hdvd
    apply ih
    have h1 : (p * (p ^ d * t) - 1).choose (p * p ^ d - 1) ≡
        ((p * (p ^ d * t) - 1) % p).choose ((p * p ^ d - 1) % p) *
          ((p * (p ^ d * t) - 1) / p).choose ((p * p ^ d - 1) / p) [MOD p] :=
      Choose.choose_modEq_choose_mod_mul_choose_div_nat
    rw [hNm, hNd, hKm, hKd, Nat.choose_self, one_mul] at h1
    have h2 := Nat.mod_eq_zero_of_dvd hdvd
    unfold Nat.ModEq at h1
    rw [h2] at h1
    exact Nat.dvd_of_mod_eq_zero h1.symm

private lemma e7_hid (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    n * (n - 1).choose (k - 1) = n.choose k * k := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.add_sub_cancel]
  exact Nat.succ_mul_choose_eq n' k'

private lemma e7_decomp (n p : ℕ) (hn : n ≠ 0) (hp : p.Prime) (d : ℕ) (hd1 : 1 ≤ d)
    (hda : d ≤ n.factorization p) :
    ∃ u : ℤ, (n.choose (p ^ d) : ℤ) = (p : ℤ) ^ (n.factorization p - d) * u ∧ ¬ (p : ℤ) ∣ u := by
  have hpa : p ^ (n.factorization p) ∣ n := (hp.pow_dvd_iff_le_factorization hn).mpr le_rfl
  have hpd : p ^ d ∣ n := (pow_dvd_pow p hda).trans hpa
  obtain ⟨t, ht⟩ := hpd
  have ht1 : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · rw [h, mul_zero] at ht; exact absurd ht hn
    · exact h
  have hpdpos : 0 < p ^ d := pow_pos hp.pos d
  have hid := e7_hid n (p ^ d) (Nat.one_le_iff_ne_zero.mpr hn) hpdpos
  have hL : ¬ p ∣ (n - 1).choose (p ^ d - 1) := by
    rw [ht]; exact e7_luc p hp t ht1 d
  have hV1 : p ^ (n.factorization p - d) ∣ n.choose (p ^ d) := by
    apply Nat.dvd_of_mul_dvd_mul_right hpdpos
    rw [← pow_add, Nat.sub_add_cancel hda, ← hid]
    exact Dvd.dvd.mul_right hpa _
  obtain ⟨w, hw⟩ := hV1
  refine ⟨(w : ℤ), ?_, ?_⟩
  · rw [hw, Nat.cast_mul, Nat.cast_pow]
  · intro hdv
    rw [Int.natCast_dvd_natCast] at hdv
    obtain ⟨z, hz⟩ := hdv
    have h1 : p ^ (n.factorization p + 1) ∣ n * (n - 1).choose (p ^ d - 1) := by
      rw [hid, hw, hz]
      refine ⟨z, ?_⟩
      rw [show n.factorization p + 1 = (n.factorization p - d) + 1 + d by omega]
      ring
    have h2 : p ^ (n.factorization p + 1) ∣ n :=
      (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hL)).dvd_of_dvd_mul_right h1
    have := (hp.pow_dvd_iff_le_factorization hn).mp h2
    omega

private lemma e7_other (n p q : ℕ) (hn : n ≠ 0) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (d : ℕ) : q ^ (n.factorization q) ∣ n.choose (p ^ d) := by
  have hid := e7_hid n (p ^ d) (Nat.one_le_iff_ne_zero.mpr hn) (Nat.one_le_pow _ _ hp.pos)
  have hqn : q ^ (n.factorization q) ∣ n := (hq.pow_dvd_iff_le_factorization hn).mpr le_rfl
  have h1 : q ^ (n.factorization q) ∣ n.choose (p ^ d) * p ^ d := by
    rw [← hid]; exact Dvd.dvd.mul_right hqn _
  have hcop : Nat.Coprime (q ^ (n.factorization q)) (p ^ d) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hq hp).mpr (Ne.symm hpq))
  exact hcop.dvd_of_dvd_mul_right h1

private lemma e7_uniq_aux (n p : ℕ) (hn : n ≠ 0) (hp : p.Prime) :
    ∀ m, m ≤ n.factorization p → ∀ c : ℕ → ℤ, (∀ d ∈ Finset.Icc 1 m, |c d| < p) →
      (p : ℤ) ^ (n.factorization p) ∣ ∑ d ∈ Finset.Icc 1 m, c d * (n.choose (p ^ d) : ℤ) →
      ∀ d ∈ Finset.Icc 1 m, c d = 0 := by
  have hp0' : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  intro m
  induction m with
  | zero =>
    intro _ c _ _ d hd
    rw [Finset.mem_Icc] at hd
    omega
  | succ m ih =>
    intro hm c hc hdiv
    rw [Finset.sum_Icc_succ_top (show 1 ≤ m + 1 by omega)] at hdiv
    obtain ⟨u, hu, hpu⟩ := e7_decomp n p hn hp (m + 1) (by omega) hm
    have h1 : (p : ℤ) ^ (n.factorization p - m) ∣
        ∑ d ∈ Finset.Icc 1 m, c d * (n.choose (p ^ d) : ℤ) := by
      apply Finset.dvd_sum
      intro d hd
      rw [Finset.mem_Icc] at hd
      obtain ⟨v, hv, _⟩ := e7_decomp n p hn hp d hd.1 (by omega)
      rw [hv]
      exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (pow_dvd_pow _ (by omega)) _) _
    have h2 : (p : ℤ) ^ (n.factorization p - m) ∣ c (m + 1) * (n.choose (p ^ (m + 1)) : ℤ) :=
      (dvd_add_right h1).mp
        ((pow_dvd_pow (p : ℤ) (by omega : n.factorization p - m ≤ n.factorization p)).trans hdiv)
    have hpow : (p : ℤ) ^ (n.factorization p - m) =
        (p : ℤ) ^ (n.factorization p - (m + 1)) * p := by
      rw [← pow_succ]; congr 1; omega
    rw [hpow, hu, show c (m + 1) * ((p : ℤ) ^ (n.factorization p - (m + 1)) * u) =
      (p : ℤ) ^ (n.factorization p - (m + 1)) * (c (m + 1) * u) by ring] at h2
    have hcu : (p : ℤ) ∣ c (m + 1) * u :=
      (mul_dvd_mul_iff_left (pow_ne_zero _ hp0')).mp h2
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hc0 : (p : ℤ) ∣ c (m + 1) := (hpZ.dvd_or_dvd hcu).resolve_right hpu
    have hcz : c (m + 1) = 0 :=
      Int.eq_zero_of_abs_lt_dvd hc0 (hc (m + 1) (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩))
    rw [hcz, zero_mul, add_zero] at hdiv
    intro d hd
    rw [Finset.mem_Icc] at hd
    by_cases hdm : d = m + 1
    · subst hdm; exact hcz
    · exact ih (by omega) c
        (fun d' hd' => hc d' (by rw [Finset.mem_Icc] at hd' ⊢; omega)) hdiv d
        (by rw [Finset.mem_Icc]; omega)

private lemma e7_exist_aux (n p : ℕ) (hn : n ≠ 0) (hp : p.Prime) :
    ∀ m, m ≤ n.factorization p → ∀ r : ℤ, (p : ℤ) ^ (n.factorization p - m) ∣ r →
      ∃ e : ℕ → ℕ, (∀ d, e d < p) ∧ (∀ d, d ∉ Finset.Icc 1 m → e d = 0) ∧
        (p : ℤ) ^ (n.factorization p) ∣
          r - ∑ d ∈ Finset.Icc 1 m, (e d : ℤ) * (n.choose (p ^ d) : ℤ) := by
  intro m
  induction m with
  | zero =>
    intro _ r hr
    refine ⟨fun _ => 0, fun _ => hp.pos, fun _ _ => rfl, ?_⟩
    simpa using hr
  | succ m ih =>
    intro hm r hr
    obtain ⟨u, hu, hpu⟩ := e7_decomp n p hn hp (m + 1) (by omega) hm
    obtain ⟨s, hs⟩ := hr
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    obtain ⟨α, β, hab⟩ := (Prime.coprime_iff_not_dvd hpZ).mpr hpu
    have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
    obtain ⟨R, Q, hRQ, hR0, hRlt⟩ : ∃ R Q : ℤ, R + p * Q = s * β ∧ 0 ≤ R ∧ R < p :=
      ⟨s * β % p, s * β / p, Int.emod_add_mul_ediv _ _,
        Int.emod_nonneg _ hp0.ne',
        Int.emod_lt_of_pos _ hp0⟩
    obtain ⟨c, hc⟩ : ∃ c : ℕ, (c : ℤ) = R := ⟨R.toNat, Int.toNat_of_nonneg hR0⟩
    have hcp : c < p := by omega
    have key : (p : ℤ) ^ (n.factorization p - m) ∣
        r - (c : ℤ) * (n.choose (p ^ (m + 1)) : ℤ) := by
      have hpow : (p : ℤ) ^ (n.factorization p - m) =
          (p : ℤ) ^ (n.factorization p - (m + 1)) * p := by
        rw [← pow_succ]; congr 1; omega
      rw [hpow, hu, hs, hc]
      exact ⟨s * α + Q * u, by
        linear_combination (-(p : ℤ) ^ (n.factorization p - (m + 1)) * s) * hab +
          (-(p : ℤ) ^ (n.factorization p - (m + 1)) * u) * hRQ⟩
    obtain ⟨e', he1, he2, he3⟩ := ih (by omega) (r - (c : ℤ) * (n.choose (p ^ (m + 1)) : ℤ)) key
    refine ⟨fun d => if d = m + 1 then c else e' d, ?_, ?_, ?_⟩
    · intro d
      try dsimp only
      split_ifs
      · exact hcp
      · exact he1 d
    · intro d hd
      try dsimp only
      rw [if_neg (by intro h; apply hd; rw [Finset.mem_Icc]; omega)]
      exact he2 d (by intro h; apply hd; rw [Finset.mem_Icc] at h ⊢; omega)
    · try dsimp only
      rw [Finset.sum_Icc_succ_top (show 1 ≤ m + 1 by omega)]
      have hsum : ∑ d ∈ Finset.Icc 1 m,
          ((if d = m + 1 then c else e' d : ℕ) : ℤ) * (n.choose (p ^ d) : ℤ) =
          ∑ d ∈ Finset.Icc 1 m, (e' d : ℤ) * (n.choose (p ^ d) : ℤ) := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [Finset.mem_Icc] at hd
        rw [if_neg (by omega)]
      rw [hsum, if_pos rfl]
      convert he3 using 1
      ring

private lemma e7_digits_spec (n p : ℕ) (hn : n ≠ 0) (hp : p.Prime) (r : ℤ) :
    (∀ d, erdos_727285_digits n p r d < p) ∧
    (∀ d, d ∉ Finset.Icc 1 (n.factorization p) → erdos_727285_digits n p r d = 0) ∧
    ((p : ℤ) ^ (n.factorization p) ∣
      r - ∑ d ∈ Finset.Icc 1 (n.factorization p),
        (erdos_727285_digits n p r d : ℤ) * (n.choose (p ^ d) : ℤ)) := by
  have hex : ∃ e : ℕ → ℕ, (∀ d, e d < p) ∧
      (∀ d, d ∉ Finset.Icc 1 (n.factorization p) → e d = 0) ∧
      ((p : ℤ) ^ (n.factorization p) ∣
        r - ∑ d ∈ Finset.Icc 1 (n.factorization p), (e d : ℤ) * (n.choose (p ^ d) : ℤ)) :=
    e7_exist_aux n p hn hp (n.factorization p) le_rfl r (by simp)
  have h : erdos_727285_digits n p r = Classical.choose hex := by
    unfold erdos_727285_digits
    exact dif_pos hex
  rw [h]
  exact Classical.choose_spec hex

private lemma e7_phiP_eq (n p : ℕ) (hn : n ≠ 0) (hp : p.Prime) (r : ℤ) (e : ℕ → ℕ)
    (he : ∀ d ∈ Finset.Icc 1 (n.factorization p), e d < p)
    (hdiv : (p : ℤ) ^ (n.factorization p) ∣
      r - ∑ d ∈ Finset.Icc 1 (n.factorization p), (e d : ℤ) * (n.choose (p ^ d) : ℤ)) :
    erdos_727285_phiP n p r =
      ∑ d ∈ Finset.Icc 1 (n.factorization p), (e d : ℤ) * (n.choose (p ^ d) : ℤ) := by
  obtain ⟨h1, -, h3⟩ := e7_digits_spec n p hn hp r
  have habs : ∀ d ∈ Finset.Icc 1 (n.factorization p),
      |(fun d => (erdos_727285_digits n p r d : ℤ) - e d) d| < p := by
    intro d hd
    show |(erdos_727285_digits n p r d : ℤ) - e d| < p
    have := h1 d
    have := he d hd
    rw [abs_lt]
    constructor <;> omega
  have hsum : (p : ℤ) ^ (n.factorization p) ∣ ∑ d ∈ Finset.Icc 1 (n.factorization p),
      ((erdos_727285_digits n p r d : ℤ) - e d) * (n.choose (p ^ d) : ℤ) := by
    have h := dvd_sub hdiv h3
    have heq : ∑ d ∈ Finset.Icc 1 (n.factorization p),
        ((erdos_727285_digits n p r d : ℤ) - e d) * (n.choose (p ^ d) : ℤ) =
        (r - ∑ d ∈ Finset.Icc 1 (n.factorization p), (e d : ℤ) * (n.choose (p ^ d) : ℤ)) -
        (r - ∑ d ∈ Finset.Icc 1 (n.factorization p),
          (erdos_727285_digits n p r d : ℤ) * (n.choose (p ^ d) : ℤ)) := by
      simp only [sub_mul, Finset.sum_sub_distrib]; ring
    rw [heq]; exact h
  have hc := e7_uniq_aux n p hn hp (n.factorization p) le_rfl
    (fun d => (erdos_727285_digits n p r d : ℤ) - e d) habs hsum
  unfold erdos_727285_phiP
  apply Finset.sum_congr rfl
  intro d hdm
  have h' : (erdos_727285_digits n p r d : ℤ) - e d = 0 := hc d hdm
  have h'' : erdos_727285_digits n p r d = e d := by omega
  rw [h'']

theorem erdos_727285_hyp_S7_phi_basic :
    ∀ n : ℕ, erdos_727285_Good n →
      (∀ r : ℤ, 0 ≤ erdos_727285_phi n r) ∧
      (∀ r : ℤ, (n : ℤ) ∣ erdos_727285_phi n r - r) ∧
      (∀ r : ℤ, erdos_727285_phi n (r + n) = erdos_727285_phi n r) ∧
      (∀ r : ℤ, erdos_727285_phi n (r - n) = erdos_727285_phi n r) ∧
      erdos_727285_phi n 0 = 0 ∧
      erdos_727285_phi n (erdos_727285_X n) = erdos_727285_X n := by
  intro n hn
  have hn0 : n ≠ 0 := hn.1
  have shift : ∀ r s : ℤ, (n : ℤ) ∣ r - s → erdos_727285_phi n r = erdos_727285_phi n s := by
    intro r s hrs
    unfold erdos_727285_phi
    apply Finset.sum_congr rfl
    intro p hpm
    have hp := Nat.prime_of_mem_primeFactors hpm
    obtain ⟨h1, -, h3⟩ := e7_digits_spec n p hn0 hp s
    have hpn : (p : ℤ) ^ (n.factorization p) ∣ (n : ℤ) := by
      exact_mod_cast (hp.pow_dvd_iff_le_factorization hn0).mpr le_rfl
    have hdiv : (p : ℤ) ^ (n.factorization p) ∣ r - ∑ d ∈ Finset.Icc 1 (n.factorization p),
        (erdos_727285_digits n p s d : ℤ) * (n.choose (p ^ d) : ℤ) := by
      have := dvd_add (hpn.trans hrs) h3
      rwa [sub_add_sub_cancel] at this
    rw [e7_phiP_eq n p hn0 hp r _ (fun d _ => h1 d) hdiv]
    rfl
  have key : ∀ p ∈ n.primeFactors, ∀ r : ℤ,
      (p : ℤ) ^ (n.factorization p) ∣ erdos_727285_phi n r - r := by
    intro p hpm r
    have hp := Nat.prime_of_mem_primeFactors hpm
    obtain ⟨-, -, h3⟩ := e7_digits_spec n p hn0 hp r
    have h3' : (p : ℤ) ^ (n.factorization p) ∣ r - erdos_727285_phiP n p r := h3
    unfold erdos_727285_phi
    rw [← Finset.add_sum_erase _ _ hpm]
    have hrest : (p : ℤ) ^ (n.factorization p) ∣
        ∑ q ∈ n.primeFactors.erase p, erdos_727285_phiP n q r := by
      apply Finset.dvd_sum
      intro q hq
      have hqp : q ≠ p := Finset.ne_of_mem_erase hq
      have hq' := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hq)
      unfold erdos_727285_phiP
      apply Finset.dvd_sum
      intro d _
      apply Dvd.dvd.mul_left
      exact_mod_cast e7_other n q p hn0 hq' hp hqp d
    have := dvd_sub hrest h3'
    have heq : erdos_727285_phiP n p r + ∑ x ∈ n.primeFactors.erase p, erdos_727285_phiP n x r - r =
        ∑ q ∈ n.primeFactors.erase p, erdos_727285_phiP n q r - (r - erdos_727285_phiP n p r) := by
      ring
    rw [heq]
    exact this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r
    unfold erdos_727285_phi erdos_727285_phiP
    exact Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun d _ => by positivity
  · intro r
    rw [Int.ofNat_dvd_left]
    by_cases hm0 : (erdos_727285_phi n r - r).natAbs = 0
    · rw [hm0]; exact dvd_zero _
    · rw [← Nat.factorization_prime_le_iff_dvd hn0 hm0]
      intro p hp
      by_cases hpn : p ∣ n
      · have hpm : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpn, hn0⟩
        apply (hp.pow_dvd_iff_le_factorization hm0).mp
        rw [← Int.ofNat_dvd_left]
        push_cast
        exact key p hpm r
      · rw [Nat.factorization_eq_zero_of_not_dvd hpn]; exact Nat.zero_le _
  · intro r
    apply shift
    exact ⟨1, by ring⟩
  · intro r
    apply shift
    exact ⟨-1, by ring⟩
  · unfold erdos_727285_phi
    apply Finset.sum_eq_zero
    intro p hpm
    have hp := Nat.prime_of_mem_primeFactors hpm
    rw [e7_phiP_eq n p hn0 hp 0 (fun _ => 0) (fun d _ => hp.pos) (by simp)]
    simp
  · have hX : ∀ p ∈ n.primeFactors, erdos_727285_phiP n p (erdos_727285_X n) =
        (∑ d ∈ Finset.Icc 1 (n.factorization p), (n.choose (p ^ d) : ℤ)) * ((p : ℤ) - 1) := by
      intro p hpm
      have hp := Nat.prime_of_mem_primeFactors hpm
      have hsplit : erdos_727285_X n =
          (∑ d ∈ Finset.Icc 1 (n.factorization p), (n.choose (p ^ d) : ℤ)) * ((p : ℤ) - 1) +
          ∑ q ∈ n.primeFactors.erase p,
            (∑ d ∈ Finset.Icc 1 (n.factorization q), (n.choose (q ^ d) : ℤ)) * ((q : ℤ) - 1) := by
        unfold erdos_727285_X
        exact (Finset.add_sum_erase _ _ hpm).symm
      have hrest : (p : ℤ) ^ (n.factorization p) ∣ ∑ q ∈ n.primeFactors.erase p,
          (∑ d ∈ Finset.Icc 1 (n.factorization q), (n.choose (q ^ d) : ℤ)) * ((q : ℤ) - 1) := by
        apply Finset.dvd_sum
        intro q hq
        have hqp : q ≠ p := Finset.ne_of_mem_erase hq
        have hq' := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hq)
        apply Dvd.dvd.mul_right
        apply Finset.dvd_sum
        intro d _
        exact_mod_cast e7_other n q p hn0 hq' hp hqp d
      have hdivX : (p : ℤ) ^ (n.factorization p) ∣ erdos_727285_X n -
          ∑ d ∈ Finset.Icc 1 (n.factorization p), ((p - 1 : ℕ) : ℤ) * (n.choose (p ^ d) : ℤ) := by
        rw [hsplit]
        convert hrest using 1
        rw [← Finset.mul_sum, Nat.cast_sub hp.one_le, Nat.cast_one]
        ring
      rw [e7_phiP_eq n p hn0 hp _ (fun _ => p - 1) (fun d _ => Nat.sub_lt hp.pos one_pos) hdivX]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d _
      push_cast [Nat.cast_sub hp.one_le]
      ring
    unfold erdos_727285_phi
    rw [Finset.sum_congr rfl hX]
    rfl
end erdos_727285_hyp_S7_phi_basic_ns

namespace erdos_727285_hyp_S20_L7_small_ns
open Classical in

-- CHECK: Nat.choose_mul Nat.succ_mul_choose_eq Nat.Prime.pow_dvd_iff_le_factorization Finset.sum_sigma' Nat.pow_right_injective Nat.choose_eq_factorial_div_factorial
private lemma choose_ratio (n i k : ℕ) (hk : k ≤ i) (hn : 2 * i ≤ n) :
    n.choose k * (2 * i).choose i ≤ n.choose i * (2 * i).choose k := by
  have hin : i ≤ n := by omega
  have h1 : n.choose i * i.choose k = n.choose k * (n - k).choose (i - k) :=
    Nat.choose_mul (n := n) hk
  have h2 : (2 * i).choose i * i.choose k = (2 * i).choose k * (2 * i - k).choose (i - k) :=
    Nat.choose_mul (n := 2 * i) hk
  have h3 : (2 * i - k).choose (i - k) ≤ (n - k).choose (i - k) :=
    Nat.choose_le_choose _ (by omega)
  have hx : 0 < i.choose k := Nat.choose_pos hk
  have key : n.choose k * (2 * i).choose i * i.choose k
      ≤ n.choose i * (2 * i).choose k * i.choose k := by
    calc n.choose k * (2 * i).choose i * i.choose k
        = n.choose k * ((2 * i).choose k * (2 * i - k).choose (i - k)) := by
          rw [mul_assoc, h2]
      _ ≤ n.choose k * ((2 * i).choose k * (n - k).choose (i - k)) :=
          Nat.mul_le_mul (le_refl _) (Nat.mul_le_mul (le_refl _) h3)
      _ = (2 * i).choose k * (n.choose k * (n - k).choose (i - k)) := by ring
      _ = (2 * i).choose k * (n.choose i * i.choose k) := by rw [h1]
      _ = n.choose i * (2 * i).choose k * i.choose k := by ring
  exact le_of_mul_le_mul_right key hx

private lemma J_le (n i q : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
    erdos_727285_J n i q ≤ i.factorization q := by
  unfold erdos_727285_J
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hid : (m + 1) * m.choose j = (m + 1).choose (j + 1) * (j + 1) :=
    Nat.succ_mul_choose_eq m j
  have h1 : m.choose j ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have h2 : (m + 1).choose (j + 1) ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hf : ((m + 1) * m.choose j).factorization q
      = ((m + 1).choose (j + 1) * (j + 1)).factorization q := by rw [hid]
  rw [Nat.factorization_mul (by omega) h1, Nat.factorization_mul h2 (by omega)] at hf
  simp only [Finsupp.add_apply] at hf
  omega

private lemma R_le_sum (n i : ℕ) (hi1 : 1 ≤ i) (hin : 2 * i ≤ n)
    (hnt : erdos_727285_NotTower n i) :
    erdos_727285_R n i ≤ ∑ k ∈ Finset.Icc 2 (i / 2), (k - 1) * n.choose k := by
  unfold erdos_727285_R
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_sigma']
  set S := n.primeFactors.sigma (fun q => Finset.Icc 1 (erdos_727285_J n i q)) with hS
  have hmem : ∀ x ∈ S, x.1.Prime ∧ 1 ≤ x.2 ∧ 2 * x.1 ^ x.2 ≤ i := by
    intro x hx
    rw [hS, Finset.mem_sigma, Nat.mem_primeFactors, Finset.mem_Icc] at hx
    obtain ⟨⟨hq, hqn, hn0⟩, hd1, hdJ⟩ := hx
    have hJ := J_le n i x.1 hi1 (by omega)
    have hdv : x.2 ≤ i.factorization x.1 := le_trans hdJ hJ
    have hdvd : x.1 ^ x.2 ∣ i := (hq.pow_dvd_iff_le_factorization (by omega)).mpr hdv
    have hne : i ≠ x.1 ^ x.2 := by
      refine hnt x.1 (Nat.mem_primeFactors.mpr ⟨hq, hqn, hn0⟩) x.2 ?_
      rw [Finset.mem_Icc]
      unfold erdos_727285_J at hdJ
      constructor <;> omega
    obtain ⟨m, hm⟩ := hdvd
    refine ⟨hq, hd1, ?_⟩
    have hm2 : 2 ≤ m := by
      rcases Nat.lt_or_ge m 2 with h | h
      · interval_cases m
        · rw [Nat.mul_zero] at hm; omega
        · rw [Nat.mul_one] at hm; exact absurd hm hne
      · exact h
    calc 2 * x.1 ^ x.2 = x.1 ^ x.2 * 2 := by ring
      _ ≤ x.1 ^ x.2 * m := Nat.mul_le_mul (le_refl _) hm2
      _ = i := hm.symm
  calc _ ≤ ∑ x ∈ S, (x.1 ^ x.2 - 1) * n.choose (x.1 ^ x.2) := by
        apply Finset.sum_le_sum
        intro x hx
        obtain ⟨hq, hd1, _⟩ := hmem x hx
        have : x.1 ≤ x.1 ^ x.2 := by
          calc x.1 = x.1 ^ 1 := (pow_one _).symm
            _ ≤ x.1 ^ x.2 := Nat.pow_le_pow_right hq.pos hd1
        exact Nat.mul_le_mul (by omega) (le_refl _)
    _ = ∑ k ∈ S.image (fun x => x.1 ^ x.2), (k - 1) * n.choose k := by
        symm
        apply Finset.sum_image
        intro x hx y hy hxy
        obtain ⟨hqx, hdx, _⟩ := hmem x hx
        obtain ⟨hqy, hdy, _⟩ := hmem y hy
        obtain ⟨q1, d1⟩ := x
        obtain ⟨q2, d2⟩ := y
        have hq1 : q1.Prime := hqx
        have hq2 : q2.Prime := hqy
        have hd1' : 1 ≤ d1 := hdx
        have hxy' : q1 ^ d1 = q2 ^ d2 := hxy
        have hq : q1 = q2 := by
          have h1 : q1 ∣ q2 ^ d2 := by
            rw [← hxy']; exact dvd_pow_self q1 (by omega)
          exact (Nat.prime_dvd_prime_iff_eq hq1 hq2).mp (hq1.dvd_of_dvd_pow h1)
        subst hq
        have hd : d1 = d2 := Nat.pow_right_injective hq1.two_le hxy'
        subst hd
        rfl
    _ ≤ ∑ k ∈ Finset.Icc 2 (i / 2), (k - 1) * n.choose k := by
        apply Finset.sum_le_sum_of_subset
        intro k hk
        rw [Finset.mem_image] at hk
        obtain ⟨x, hx, rfl⟩ := hk
        obtain ⟨hq, hd1, h2⟩ := hmem x hx
        have : x.1 ≤ x.1 ^ x.2 := by
          calc x.1 = x.1 ^ 1 := (pow_one _).symm
            _ ≤ x.1 ^ x.2 := Nat.pow_le_pow_right hq.pos hd1
        have := hq.two_le
        simp only [Finset.mem_Icc]
        constructor <;> omega

set_option maxRecDepth 10000 in

private lemma check_fact (i : ℕ) (hi1 : 1 ≤ i) (hi34 : i ≤ 34) :
    ∑ k ∈ Finset.Icc 2 (i / 2),
        (k - 1) * ((2 * i).factorial / (k.factorial * (2 * i - k).factorial))
      ≤ (2 * i).factorial / (i.factorial * (2 * i - i).factorial) := by
  interval_cases i <;> decide +kernel

private lemma small_check (i : ℕ) (hi1 : 1 ≤ i) (hi34 : i ≤ 34) :
    ∑ k ∈ Finset.Icc 2 (i / 2), (k - 1) * (2 * i).choose k ≤ (2 * i).choose i := by
  have h := check_fact i hi1 hi34
  have e : ∑ k ∈ Finset.Icc 2 (i / 2), (k - 1) * (2 * i).choose k
      = ∑ k ∈ Finset.Icc 2 (i / 2),
          (k - 1) * ((2 * i).factorial / (k.factorial * (2 * i - k).factorial)) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [Nat.choose_eq_factorial_div_factorial (by omega : k ≤ 2 * i)]
  rw [e, Nat.choose_eq_factorial_div_factorial (by omega : i ≤ 2 * i)]
  exact h

private lemma sum_le_choose (n i : ℕ) (hi1 : 1 ≤ i) (hi34 : i ≤ 34) (hin : 2 * i ≤ n) :
    ∑ k ∈ Finset.Icc 2 (i / 2), (k - 1) * n.choose k ≤ n.choose i := by
  have hc := small_check i hi1 hi34
  have hpos : 0 < (2 * i).choose i := Nat.choose_pos (by omega)
  have key : (∑ k ∈ Finset.Icc 2 (i / 2), (k - 1) * n.choose k) * (2 * i).choose i
      ≤ n.choose i * (2 * i).choose i := by
    calc (∑ k ∈ Finset.Icc 2 (i / 2), (k - 1) * n.choose k) * (2 * i).choose i
        = ∑ k ∈ Finset.Icc 2 (i / 2), (k - 1) * (n.choose k * (2 * i).choose i) := by
          rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro k _; ring
      _ ≤ ∑ k ∈ Finset.Icc 2 (i / 2), (k - 1) * (n.choose i * (2 * i).choose k) := by
          apply Finset.sum_le_sum
          intro k hk
          rw [Finset.mem_Icc] at hk
          exact Nat.mul_le_mul (le_refl _) (choose_ratio n i k (by omega) hin)
      _ = n.choose i * ∑ k ∈ Finset.Icc 2 (i / 2), (k - 1) * (2 * i).choose k := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
      _ ≤ n.choose i * (2 * i).choose i := Nat.mul_le_mul (le_refl _) hc
  exact le_of_mul_le_mul_right key hpos

theorem erdos_727285_hyp_S20_L7_small :
    ∀ n i : ℕ, erdos_727285_Good n → 1 ≤ i → i ≤ 34 → 2 * i ≤ n →
      erdos_727285_NotTower n i → erdos_727285_R n i ≤ n.choose i := by
  intro n i _ hi1 hi34 hin hnt
  exact le_trans (R_le_sum n i hi1 hin hnt) (sum_le_choose n i hi1 hi34 hin)
end erdos_727285_hyp_S20_L7_small_ns

namespace erdos_727285_hyp_S21a_phi_le_ns
namespace erdos_727285_hyp_S21a_phi_le_hyp_tower_ns
-- CHECK: Choose.choose_modEq_choose_mod_mul_choose_div_nat Finset.sum_Icc_succ_top Int.eq_zero_of_abs_lt_dvd Nat.succ_mul_choose_eq
private lemma e727_divmod (q A : ℕ) (hq : 2 ≤ q) (hA : 1 ≤ A) :
    (q * A - 1) % q = q - 1 ∧ (q * A - 1) / q = A - 1 := by
  obtain ⟨B, rfl⟩ : ∃ B, A = B + 1 := ⟨A - 1, by omega⟩
  have h1 : q * (B + 1) - 1 = (q - 1) + q * B := by
    rw [mul_add, mul_one]
    generalize q * B = t
    omega
  rw [h1, Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ (by omega : 0 < q),
    Nat.mod_eq_of_lt (by omega : q - 1 < q), Nat.div_eq_of_lt (by omega : q - 1 < q)]
  refine ⟨rfl, ?_⟩
  omega

private lemma e727_lucas_aux (q : ℕ) (hq : q.Prime) (m : ℕ) (hm : 1 ≤ m) :
    ∀ d : ℕ, ¬ q ∣ (q ^ d * m - 1).choose (q ^ d - 1) := by
  haveI := Fact.mk hq
  have hq2 := hq.two_le
  intro d
  induction d with
  | zero =>
    rw [pow_zero, one_mul, Nat.sub_self, Nat.choose_zero_right]
    exact hq.not_dvd_one
  | succ d ih =>
    intro hdvd
    apply ih
    have hA : 1 ≤ q ^ d * m := by
      have := Nat.mul_pos (pow_pos hq.pos d) (show 0 < m by omega)
      omega
    have hB : 1 ≤ q ^ d := Nat.one_le_pow _ _ hq.pos
    have e1 : q ^ (d + 1) * m = q * (q ^ d * m) := by rw [pow_succ]; ring
    have e2 : q ^ (d + 1) = q * q ^ d := by rw [pow_succ]; ring
    obtain ⟨h1, h2⟩ := e727_divmod q (q ^ d * m) hq2 hA
    obtain ⟨h3, h4⟩ := e727_divmod q (q ^ d) hq2 hB
    have hl : (q ^ (d + 1) * m - 1).choose (q ^ (d + 1) - 1) ≡
        ((q ^ (d + 1) * m - 1) % q).choose ((q ^ (d + 1) - 1) % q) *
        ((q ^ (d + 1) * m - 1) / q).choose ((q ^ (d + 1) - 1) / q) [MOD q] :=
      Choose.choose_modEq_choose_mod_mul_choose_div_nat
    rw [e1, e2, h1, h2, h3, h4, Nat.choose_self, one_mul] at hl
    rw [e1, e2] at hdvd
    exact Nat.modEq_zero_iff_dvd.mp (hl.symm.trans (Nat.modEq_zero_iff_dvd.mpr hdvd))

private lemma e727_id (n k : ℕ) (hn : n ≠ 0) (hk : 0 < k) :
    n * (n - 1).choose (k - 1) = n.choose k * k := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  obtain ⟨K, rfl⟩ : ∃ K, k = K + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.add_sub_cancel]
  exact Nat.succ_mul_choose_eq N K

private lemma e727_val (n q d : ℕ) (hn : n ≠ 0) (hq : q.Prime) (hd1 : 1 ≤ d)
    (hdb : d ≤ n.factorization q) :
    q ^ (n.factorization q - d) ∣ n.choose (q ^ d) ∧
    ¬ q ^ (n.factorization q - d + 1) ∣ n.choose (q ^ d) := by
  have hqd : q ^ d ∣ n := (hq.pow_dvd_iff_le_factorization hn).mpr hdb
  have hqb : q ^ (n.factorization q) ∣ n := (hq.pow_dvd_iff_le_factorization hn).mpr le_rfl
  have hpos : 0 < q ^ d := pow_pos hq.pos d
  have hid := e727_id n (q ^ d) hn hpos
  refine ⟨?_, ?_⟩
  · have hdiv : q ^ (n.factorization q) ∣ n.choose (q ^ d) * q ^ d := by
      rw [← hid]; exact Dvd.dvd.mul_right hqb _
    have hsplit : q ^ (n.factorization q) = q ^ (n.factorization q - d) * q ^ d := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit] at hdiv
    exact Nat.dvd_of_mul_dvd_mul_right hpos hdiv
  · intro h
    obtain ⟨m, hm⟩ := hqd
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · rw [h0, mul_zero] at hm; exact absurd hm hn
      · exact h0
    have hcop : Nat.Coprime (q ^ (n.factorization q + 1)) ((n - 1).choose (q ^ d - 1)) := by
      apply Nat.Coprime.pow_left
      rw [Nat.Prime.coprime_iff_not_dvd hq]
      have := e727_lucas_aux q hq m hm1 d
      rwa [← hm] at this
    have h2 : q ^ (n.factorization q + 1) ∣ n * (n - 1).choose (q ^ d - 1) := by
      rw [hid]
      have : q ^ (n.factorization q + 1) = q ^ (n.factorization q - d + 1) * q ^ d := by
        rw [← pow_add]; congr 1; omega
      rw [this]
      exact mul_dvd_mul_right h _
    have h3 : q ^ (n.factorization q + 1) ∣ n := hcop.dvd_of_dvd_mul_right h2
    have := (hq.pow_dvd_iff_le_factorization hn).mp h3
    omega

private lemma e727_other (n p q j : ℕ) (hn : n ≠ 0) (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) : q ^ (n.factorization q) ∣ n.choose (p ^ j) := by
  have h1 : q ^ (n.factorization q) ∣ n.choose (p ^ j) * p ^ j := by
    rw [← e727_id n (p ^ j) hn (pow_pos hp.pos j)]
    exact Dvd.dvd.mul_right ((hq.pow_dvd_iff_le_factorization hn).mpr le_rfl) _
  have hc : Nat.Coprime (q ^ (n.factorization q)) (p ^ j) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hq hp).mpr (Ne.symm hpq))
  exact hc.dvd_of_dvd_mul_right h1

private lemma e727_unique_aux (n q : ℕ) (hn : n ≠ 0) (hq : q.Prime) :
    ∀ m : ℕ, m ≤ n.factorization q → ∀ f : ℕ → ℤ, (∀ d ∈ Finset.Icc 1 m, |f d| < q) →
      ((q : ℤ) ^ (n.factorization q) ∣ ∑ d ∈ Finset.Icc 1 m, f d * (n.choose (q ^ d) : ℤ)) →
      ∀ d ∈ Finset.Icc 1 m, f d = 0 := by
  intro m
  induction m with
  | zero =>
    intro _ f _ _ d hd
    rw [Finset.mem_Icc] at hd
    omega
  | succ m ih =>
    intro hm f hf hdiv
    have hqZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
    obtain ⟨hV1, hV2⟩ := e727_val n q (m + 1) hn hq (by omega) hm
    have hlow : (q : ℤ) ^ (n.factorization q - m) ∣
        ∑ d ∈ Finset.Icc 1 m, f d * (n.choose (q ^ d) : ℤ) := by
      apply Finset.dvd_sum
      intro d hd
      rw [Finset.mem_Icc] at hd
      obtain ⟨hv, _⟩ := e727_val n q d hn hq hd.1 (by omega)
      have h1 : (q : ℤ) ^ (n.factorization q - d) ∣ (n.choose (q ^ d) : ℤ) := by
        exact_mod_cast hv
      exact Dvd.dvd.mul_left ((pow_dvd_pow (q : ℤ) (by omega)).trans h1) _
    rw [Finset.sum_Icc_succ_top (by omega)] at hdiv
    have htop : (q : ℤ) ^ (n.factorization q - m) ∣
        f (m + 1) * (n.choose (q ^ (m + 1)) : ℤ) := by
      have h1 : (q : ℤ) ^ (n.factorization q - m) ∣ (q : ℤ) ^ (n.factorization q) :=
        pow_dvd_pow _ (by omega)
      exact (dvd_add_right hlow).mp (h1.trans hdiv)
    obtain ⟨u, hu⟩ := hV1
    have hexp : n.factorization q - m = (n.factorization q - (m + 1)) + 1 := by omega
    have hfz : f (m + 1) = 0 := by
      rw [hexp, hu, pow_succ] at htop
      push_cast at htop
      have hne : ((q : ℤ) ^ (n.factorization q - (m + 1))) ≠ 0 :=
        pow_ne_zero _ (by exact_mod_cast hq.ne_zero)
      have heq' : f (m + 1) * ((q : ℤ) ^ (n.factorization q - (m + 1)) * (u : ℤ)) =
          (q : ℤ) ^ (n.factorization q - (m + 1)) * (f (m + 1) * (u : ℤ)) := by ring
      rw [heq'] at htop
      have h3 : (q : ℤ) ∣ f (m + 1) * (u : ℤ) := (mul_dvd_mul_iff_left hne).mp htop
      rcases hqZ.dvd_or_dvd h3 with h4 | h4
      · have hb := hf (m + 1) (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
        exact Int.eq_zero_of_abs_lt_dvd h4 hb
      · exfalso
        have hqu : q ∣ u := Int.natCast_dvd_natCast.mp h4
        apply hV2
        rw [hu, pow_succ]
        exact mul_dvd_mul_left _ hqu
    rw [hfz, zero_mul, add_zero] at hdiv
    intro d hd
    rw [Finset.mem_Icc] at hd
    rcases Nat.lt_or_ge d (m + 1) with h | h
    · exact ih (by omega) f
        (fun d hd' => hf d (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd').1,
          by have := (Finset.mem_Icc.mp hd').2; omega⟩))
        hdiv d (Finset.mem_Icc.mpr ⟨hd.1, by omega⟩)
    · have : d = m + 1 := by omega
      rw [this]; exact hfz

private lemma e727_unique (n q : ℕ) (hn : n ≠ 0) (hq : q.Prime) (r : ℤ) (e e' : ℕ → ℕ)
    (he : ∀ d, e d < q) (he' : ∀ d, e' d < q)
    (h1 : (q : ℤ) ^ (n.factorization q) ∣
      r - ∑ d ∈ Finset.Icc 1 (n.factorization q), (e d : ℤ) * (n.choose (q ^ d) : ℤ))
    (h2 : (q : ℤ) ^ (n.factorization q) ∣
      r - ∑ d ∈ Finset.Icc 1 (n.factorization q), (e' d : ℤ) * (n.choose (q ^ d) : ℤ)) :
    ∀ d ∈ Finset.Icc 1 (n.factorization q), e d = e' d := by
  set A := ∑ d ∈ Finset.Icc 1 (n.factorization q), (e d : ℤ) * (n.choose (q ^ d) : ℤ) with hA
  set B := ∑ d ∈ Finset.Icc 1 (n.factorization q), (e' d : ℤ) * (n.choose (q ^ d) : ℤ) with hB
  have h : (q : ℤ) ^ (n.factorization q) ∣ A - B := by
    have h3 := dvd_sub h2 h1
    have h4 : r - B - (r - A) = A - B := by ring
    rwa [h4] at h3
  have hs : ∑ d ∈ Finset.Icc 1 (n.factorization q),
      ((e d : ℤ) - (e' d : ℤ)) * (n.choose (q ^ d) : ℤ) = A - B := by
    rw [hA, hB, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun d _ => by ring)
  have hb : ∀ d ∈ Finset.Icc 1 (n.factorization q), |((e d : ℤ) - (e' d : ℤ))| < (q : ℤ) := by
    intro d _
    have k1 := he d
    have k2 := he' d
    rw [abs_lt]
    constructor <;> omega
  have hd : (q : ℤ) ^ (n.factorization q) ∣ ∑ d ∈ Finset.Icc 1 (n.factorization q),
      ((e d : ℤ) - (e' d : ℤ)) * (n.choose (q ^ d) : ℤ) := by
    rw [hs]; exact h
  have key := e727_unique_aux n q hn hq (n.factorization q) le_rfl
    (fun d => (e d : ℤ) - (e' d : ℤ)) hb hd
  intro d hd'
  have h3 : (e d : ℤ) - (e' d : ℤ) = 0 := key d hd'
  omega

private lemma e727_digits_spec (n p : ℕ) (r : ℤ)
    (h : ∃ e : ℕ → ℕ, (∀ d, e d < p) ∧
      (∀ d, d ∉ Finset.Icc 1 (n.factorization p) → e d = 0) ∧
      ((p : ℤ) ^ (n.factorization p) ∣
        r - ∑ d ∈ Finset.Icc 1 (n.factorization p), (e d : ℤ) * (n.choose (p ^ d) : ℤ))) :
    (∀ d, erdos_727285_digits n p r d < p) ∧
      ((p : ℤ) ^ (n.factorization p) ∣
        r - ∑ d ∈ Finset.Icc 1 (n.factorization p),
          (erdos_727285_digits n p r d : ℤ) * (n.choose (p ^ d) : ℤ)) := by
  have hs := Classical.choose_spec h
  unfold erdos_727285_digits
  rw [dif_pos h]
  exact ⟨hs.1, hs.2.2⟩

theorem erdos_727285_hyp_S21a_phi_le_hyp_tower :
    ∀ n : ℕ, erdos_727285_Good n → ∀ i ∈ Finset.Ico 1 n,
      ¬ (erdos_727285_NotTower n i ∧ erdos_727285_NotTower n (n - i)) →
      erdos_727285_phi n (n.choose i : ℤ) ≤ (n.choose i : ℤ) := by
  intro n hgood i hi htow
  have hn : n ≠ 0 := hgood.1
  obtain ⟨p, hp, j, hj, hij⟩ : ∃ p ∈ n.primeFactors, ∃ j ∈ Finset.Icc 1 (n.factorization p),
      n.choose i = n.choose (p ^ j) := by
    by_contra hcon
    push_neg at hcon
    apply htow
    constructor
    · intro p hp j hj heq
      exact hcon p hp j hj (by rw [heq])
    · intro p hp j hj heq
      apply hcon p hp j hj
      rw [Finset.mem_Ico] at hi
      rw [← heq, Nat.choose_symm hi.2.le]
  rw [hij]
  have hpP : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hsumj : ∑ d ∈ Finset.Icc 1 (n.factorization p),
      (((if d = j then 1 else 0 : ℕ)) : ℤ) * (n.choose (p ^ d) : ℤ) =
      (n.choose (p ^ j) : ℤ) := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd hj h
  have hphi : erdos_727285_phi n (n.choose (p ^ j) : ℤ) = (n.choose (p ^ j) : ℤ) := by
    unfold erdos_727285_phi
    rw [Finset.sum_eq_single p]
    · have he0 : ∀ d, (if d = j then 1 else 0 : ℕ) < p := by
        intro d
        have := hpP.two_le
        split_ifs <;> omega
      have h0 : (p : ℤ) ^ (n.factorization p) ∣ (n.choose (p ^ j) : ℤ) -
          ∑ d ∈ Finset.Icc 1 (n.factorization p),
            (((if d = j then 1 else 0 : ℕ)) : ℤ) * (n.choose (p ^ d) : ℤ) := by
        rw [hsumj, sub_self]; exact dvd_zero _
      have hex : ∃ e : ℕ → ℕ, (∀ d, e d < p) ∧
          (∀ d, d ∉ Finset.Icc 1 (n.factorization p) → e d = 0) ∧
          ((p : ℤ) ^ (n.factorization p) ∣
            (n.choose (p ^ j) : ℤ) - ∑ d ∈ Finset.Icc 1 (n.factorization p),
              (e d : ℤ) * (n.choose (p ^ d) : ℤ)) := by
        refine ⟨fun d => if d = j then 1 else 0, he0, ?_, h0⟩
        intro d hd
        show (if d = j then 1 else 0) = 0
        split_ifs with h
        · exact absurd (h ▸ hj) hd
        · rfl
      obtain ⟨hdlt, hddvd⟩ := e727_digits_spec n p _ hex
      have huniq := e727_unique n p hn hpP _ (erdos_727285_digits n p (n.choose (p ^ j) : ℤ))
        (fun d => if d = j then 1 else 0) hdlt he0 hddvd h0
      unfold erdos_727285_phiP
      have hcongr : ∑ d ∈ Finset.Icc 1 (n.factorization p),
          (erdos_727285_digits n p (n.choose (p ^ j) : ℤ) d : ℤ) * (n.choose (p ^ d) : ℤ) =
          ∑ d ∈ Finset.Icc 1 (n.factorization p),
            (((if d = j then 1 else 0 : ℕ)) : ℤ) * (n.choose (p ^ d) : ℤ) :=
        Finset.sum_congr rfl (fun d hd => by rw [huniq d hd])
      rw [hcongr, hsumj]
    · intro q hq hqp
      have hqP : q.Prime := Nat.prime_of_mem_primeFactors hq
      have hdv : (q : ℤ) ^ (n.factorization q) ∣ (n.choose (p ^ j) : ℤ) := by
        exact_mod_cast e727_other n p q j hn hpP hqP (Ne.symm hqp)
      have h0 : (q : ℤ) ^ (n.factorization q) ∣ (n.choose (p ^ j) : ℤ) -
          ∑ d ∈ Finset.Icc 1 (n.factorization q), (((0 : ℕ)) : ℤ) * (n.choose (q ^ d) : ℤ) := by
        simpa using hdv
      have hex : ∃ e : ℕ → ℕ, (∀ d, e d < q) ∧
          (∀ d, d ∉ Finset.Icc 1 (n.factorization q) → e d = 0) ∧
          ((q : ℤ) ^ (n.factorization q) ∣
            (n.choose (p ^ j) : ℤ) - ∑ d ∈ Finset.Icc 1 (n.factorization q),
              (e d : ℤ) * (n.choose (q ^ d) : ℤ)) :=
        ⟨fun _ => 0, fun _ => hqP.pos, fun _ _ => rfl, h0⟩
      obtain ⟨hdlt, hddvd⟩ := e727_digits_spec n q _ hex
      have huniq := e727_unique n q hn hqP _ _ (fun _ => 0) hdlt (fun _ => hqP.pos) hddvd h0
      unfold erdos_727285_phiP
      apply Finset.sum_eq_zero
      intro d hd
      rw [huniq d hd]
      simp
    · intro h; exact absurd hp h
  exact hphi.le
end erdos_727285_hyp_S21a_phi_le_hyp_tower_ns

theorem erdos_727285_hyp_S21a_phi_le_hyp_tower :
    ∀ n : ℕ, erdos_727285_Good n → ∀ i ∈ Finset.Ico 1 n,
      ¬ (erdos_727285_NotTower n i ∧ erdos_727285_NotTower n (n - i)) →
      erdos_727285_phi n (n.choose i : ℤ) ≤ (n.choose i : ℤ) := by
  exact erdos_727285_hyp_S21a_phi_le_hyp_tower_ns.erdos_727285_hyp_S21a_phi_le_hyp_tower



namespace erdos_727285_hyp_S21a_phi_le_hyp_support_ns

private lemma e727_key (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    n * (n - 1).choose (k - 1) = n.choose k * k := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  exact Nat.succ_mul_choose_eq n' k'

private lemma e727_h3 {q d n : ℕ} (hq : q.Prime) (hdvd : q ^ d ∣ n) (hn : n ≠ 0) :
    ¬ q ∣ (n - 1).choose (q ^ d - 1) := by
  haveI := Fact.mk hq
  obtain ⟨m, rfl⟩ := hdvd
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp at hn
    · exact h
  have hqd : 1 ≤ q ^ d := Nat.one_le_pow _ _ hq.pos
  have h1 : q ^ d * 1 ≤ q ^ d * m := Nat.mul_le_mul (le_refl _) hm
  rw [mul_one] at h1
  have hle : q ^ d - 1 ≤ q ^ d * m - 1 := by omega
  have hv := padicValNat_choose (p := q) (n := q ^ d * m - 1) (k := q ^ d - 1)
    (b := Nat.log q (q ^ d * m - 1) + 1) hle (Nat.lt_succ_self _)
  have hsub : q ^ d * m - 1 - (q ^ d - 1) = q ^ d * (m - 1) := by
    rw [Nat.mul_sub_one]; omega
  have hzero : padicValNat q ((q ^ d * m - 1).choose (q ^ d - 1)) = 0 := by
    rw [hv, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i hi
    rw [Finset.mem_Ico] at hi
    rw [hsub, not_le]
    have hNpos : 0 < q ^ i := pow_pos hq.pos i
    rcases le_or_gt i d with hid | hid
    · obtain ⟨c, hc⟩ := pow_dvd_pow q hid
      have hc1 : 1 ≤ c := by
        rcases Nat.eq_zero_or_pos c with h | h
        · rw [h, mul_zero] at hc; omega
        · exact h
      obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
      have hA : (q ^ d - 1) % q ^ i = q ^ i - 1 := by
        have h2 : q ^ d - 1 = (q ^ i - 1) + q ^ i * c' := by
          rw [hc, mul_add, mul_one]; omega
        rw [h2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      have hB : (q ^ d * (m - 1)) % q ^ i = 0 :=
        Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_right (pow_dvd_pow q hid) (m - 1))
      rw [hA, hB]; omega
    · have hQ : 1 ≤ q ^ (i - d) := Nat.one_le_pow _ _ hq.pos
      have hsplit : q ^ i = q ^ d * q ^ (i - d) := by
        rw [← pow_add]; congr 1; omega
      have h2 : q ^ d * 1 ≤ q ^ d * q ^ (i - d) := Nat.mul_le_mul (le_refl _) hQ
      rw [mul_one] at h2
      have hA : (q ^ d - 1) % (q ^ d * q ^ (i - d)) = q ^ d - 1 :=
        Nat.mod_eq_of_lt (by omega)
      rw [hsplit, hA, Nat.mul_mod_mul_left]
      have hr : (m - 1) % q ^ (i - d) < q ^ (i - d) := Nat.mod_lt _ (by omega)
      have h3 : q ^ d * ((m - 1) % q ^ (i - d) + 1) ≤ q ^ d * q ^ (i - d) :=
        Nat.mul_le_mul (le_refl _) hr
      rw [mul_add, mul_one] at h3
      omega
  intro hdiv
  rcases padicValNat.eq_zero_iff.mp hzero with h | h | h
  · exact hq.one_lt.ne' h
  · exact (Nat.choose_pos hle).ne' h
  · exact h hdiv

private lemma e727_h1 {n q d : ℕ} (hq : q.Prime) (hn : n ≠ 0) (hd : d ≤ n.factorization q) :
    q ^ (n.factorization q - d) ∣ n.choose (q ^ d) := by
  have hk : 1 ≤ q ^ d := Nat.one_le_pow _ _ hq.pos
  have hkey := e727_key n (q ^ d) (by omega) hk
  have hdn : q ^ n.factorization q ∣ n := (hq.pow_dvd_iff_le_factorization hn).mpr le_rfl
  have h1 : q ^ (n.factorization q - d) * q ^ d ∣ n.choose (q ^ d) * q ^ d := by
    rw [← pow_add, Nat.sub_add_cancel hd, ← hkey]
    exact Dvd.dvd.mul_right hdn _
  exact Nat.dvd_of_mul_dvd_mul_right (by omega) h1

private lemma e727_h2 {n q d : ℕ} (hq : q.Prime) (hn : n ≠ 0) (hd : d ≤ n.factorization q) :
    ¬ q ^ (n.factorization q - d + 1) ∣ n.choose (q ^ d) := by
  intro h
  have hk : 1 ≤ q ^ d := Nat.one_le_pow _ _ hq.pos
  have hkey := e727_key n (q ^ d) (by omega) hk
  have hqd : q ^ d ∣ n := (hq.pow_dvd_iff_le_factorization hn).mpr hd
  have h3 := e727_h3 hq hqd hn
  have hbig : q ^ (n.factorization q + 1) ∣ n * (n - 1).choose (q ^ d - 1) := by
    have e : n.factorization q + 1 = (n.factorization q - d + 1) + d := by omega
    rw [hkey, e, pow_add]
    exact mul_dvd_mul_right h _
  have hcop : Nat.Coprime (q ^ (n.factorization q + 1)) ((n - 1).choose (q ^ d - 1)) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hq).mpr h3)
  exact Nat.pow_succ_factorization_not_dvd hn hq (hcop.dvd_of_dvd_mul_right hbig)

private lemma e727_support {n q : ℕ} (hq : q.Prime) (hn : n ≠ 0) (e : ℕ → ℕ)
    (he : ∀ d, e d < q)
    (hsupp : ∀ d, d ∉ Finset.Icc 1 (n.factorization q) → e d = 0)
    (r : ℤ) (J : ℕ) (hJ : J ≤ n.factorization q)
    (hr : (q : ℤ) ^ (n.factorization q - J) ∣ r)
    (hsum : (q : ℤ) ^ (n.factorization q) ∣
      r - ∑ d ∈ Finset.Icc 1 (n.factorization q), (e d : ℤ) * (n.choose (q ^ d) : ℤ)) :
    ∀ d, J < d → e d = 0 := by
  by_contra hcon
  push_neg at hcon
  have hne : ((Finset.Icc 1 (n.factorization q)).filter (fun d => J < d ∧ e d ≠ 0)).Nonempty := by
    obtain ⟨d, hJd, hed⟩ := hcon
    refine ⟨d, Finset.mem_filter.mpr ⟨?_, hJd, hed⟩⟩
    by_contra hnot
    exact hed (hsupp d hnot)
  obtain ⟨d0, hd0S, hmax⟩ := Finset.exists_max_image _ id hne
  have hd0S' := hd0S
  rw [Finset.mem_filter, Finset.mem_Icc] at hd0S'
  obtain ⟨⟨hd01, hd0a⟩, hJd0, hed0⟩ := hd0S'
  have hbig : ∀ d, d0 < d → e d = 0 := by
    intro d hd
    by_contra hed
    have hmem : d ∈ (Finset.Icc 1 (n.factorization q)).filter (fun d => J < d ∧ e d ≠ 0) := by
      refine Finset.mem_filter.mpr ⟨?_, by omega, hed⟩
      by_contra hnot
      exact hed (hsupp d hnot)
    have h' : d ≤ d0 := hmax d hmem
    omega
  have hm1 : n.factorization q - d0 + 1 ≤ n.factorization q - J := by omega
  have hm2 : n.factorization q - d0 + 1 ≤ n.factorization q := by omega
  have hall : (q : ℤ) ^ (n.factorization q - d0 + 1) ∣
      ∑ d ∈ Finset.Icc 1 (n.factorization q), (e d : ℤ) * (n.choose (q ^ d) : ℤ) := by
    have h1 : (q : ℤ) ^ (n.factorization q - d0 + 1) ∣ r := (pow_dvd_pow _ hm1).trans hr
    have h2 := (pow_dvd_pow (q : ℤ) hm2).trans hsum
    have h3 := dvd_sub h1 h2
    rwa [sub_sub_cancel] at h3
  have hd0mem : d0 ∈ Finset.Icc 1 (n.factorization q) := Finset.mem_Icc.mpr ⟨hd01, hd0a⟩
  have hrest : (q : ℤ) ^ (n.factorization q - d0 + 1) ∣
      ∑ d ∈ (Finset.Icc 1 (n.factorization q)).erase d0, (e d : ℤ) * (n.choose (q ^ d) : ℤ) := by
    apply Finset.dvd_sum
    intro d hd
    rw [Finset.mem_erase, Finset.mem_Icc] at hd
    obtain ⟨hne', hd1, hda⟩ := hd
    rcases lt_or_gt_of_ne hne' with hlt | hgt
    · have hg : q ^ (n.factorization q - d) ∣ n.choose (q ^ d) := e727_h1 hq hn hda
      have hg' : (q : ℤ) ^ (n.factorization q - d) ∣ (n.choose (q ^ d) : ℤ) := by
        exact_mod_cast hg
      exact Dvd.dvd.mul_left ((pow_dvd_pow _ (by omega)).trans hg') _
    · rw [hbig d hgt]; simp
  have heq := Finset.add_sum_erase (Finset.Icc 1 (n.factorization q))
    (fun d => (e d : ℤ) * (n.choose (q ^ d) : ℤ)) hd0mem
  have hterm : (q : ℤ) ^ (n.factorization q - d0 + 1) ∣ (e d0 : ℤ) * (n.choose (q ^ d0) : ℤ) := by
    have h4 := dvd_sub hall hrest
    rw [← heq, add_sub_cancel_right] at h4
    exact h4
  have hnat : q ^ (n.factorization q - d0 + 1) ∣ e d0 * n.choose (q ^ d0) := by
    exact_mod_cast hterm
  have hnd : ¬ q ∣ e d0 := fun h => by
    have h5 := Nat.le_of_dvd (Nat.pos_of_ne_zero hed0) h
    have h6 := he d0
    omega
  have hcop : Nat.Coprime (q ^ (n.factorization q - d0 + 1)) (e d0) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hq).mpr hnd)
  exact e727_h2 hq hn hd0a (hcop.dvd_of_dvd_mul_left hnat)

private lemma e727_phiP_le {n q i : ℕ} (hq : q.Prime) (hn : n ≠ 0) (hc : n.choose i ≠ 0) :
    erdos_727285_phiP n q (n.choose i : ℤ) ≤
      (((q - 1) * ∑ d ∈ Finset.Icc 1 (erdos_727285_J n i q), n.choose (q ^ d) : ℕ) : ℤ) := by
  unfold erdos_727285_phiP
  by_cases h : ∃ e : ℕ → ℕ, (∀ d, e d < q) ∧
      (∀ d, d ∉ Finset.Icc 1 (n.factorization q) → e d = 0) ∧
      ((q : ℤ) ^ (n.factorization q) ∣
        (n.choose i : ℤ) - ∑ d ∈ Finset.Icc 1 (n.factorization q), (e d : ℤ) * (n.choose (q ^ d) : ℤ))
  · have hdig : erdos_727285_digits n q (n.choose i : ℤ) = Classical.choose h := by
      unfold erdos_727285_digits
      rw [dif_pos h]
    obtain ⟨he, hsupp, hsum⟩ := Classical.choose_spec h
    rw [hdig]
    set e := Classical.choose h with he_def
    have hJa : erdos_727285_J n i q ≤ n.factorization q := by
      unfold erdos_727285_J; omega
    have hr : (q : ℤ) ^ (n.factorization q - erdos_727285_J n i q) ∣ (n.choose i : ℤ) := by
      have h1 : q ^ (n.choose i).factorization q ∣ n.choose i :=
        (hq.pow_dvd_iff_le_factorization hc).mpr le_rfl
      have h2 : n.factorization q - erdos_727285_J n i q ≤ (n.choose i).factorization q := by
        unfold erdos_727285_J; omega
      have h3 : q ^ (n.factorization q - erdos_727285_J n i q) ∣ n.choose i :=
        (pow_dvd_pow q h2).trans h1
      exact_mod_cast h3
    have hzero := e727_support hq hn e he hsupp _ _ hJa hr hsum
    have hsub : Finset.Icc 1 (erdos_727285_J n i q) ⊆ Finset.Icc 1 (n.factorization q) :=
      Finset.Icc_subset_Icc le_rfl hJa
    have hEq : ∑ d ∈ Finset.Icc 1 (erdos_727285_J n i q), (e d : ℤ) * (n.choose (q ^ d) : ℤ) =
        ∑ d ∈ Finset.Icc 1 (n.factorization q), (e d : ℤ) * (n.choose (q ^ d) : ℤ) := by
      apply Finset.sum_subset hsub
      intro d hd hnd
      have hlt : erdos_727285_J n i q < d := by
        rw [Finset.mem_Icc] at hd hnd
        omega
      rw [hzero d hlt]
      simp
    rw [← hEq, Nat.cast_mul, Nat.cast_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d _
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have h7 := he d
    have h' : e d ≤ q - 1 := by omega
    exact Nat.cast_le.mpr h'
  · have hdig : erdos_727285_digits n q (n.choose i : ℤ) = fun _ => 0 := by
      unfold erdos_727285_digits
      rw [dif_neg h]
    rw [hdig]
    simp only [Nat.cast_zero, zero_mul, Finset.sum_const_zero]
    positivity

theorem erdos_727285_hyp_S21a_phi_le_hyp_support :
    ∀ n : ℕ, erdos_727285_Good n → ∀ i ∈ Finset.Ico 1 n,
      erdos_727285_phi n (n.choose i : ℤ) ≤ (erdos_727285_R n i : ℤ) := by
  intro n hgood i hi
  have hn : n ≠ 0 := hgood.1
  rw [Finset.mem_Ico] at hi
  have hc : n.choose i ≠ 0 := (Nat.choose_pos (by omega)).ne'
  unfold erdos_727285_phi erdos_727285_R
  rw [Nat.cast_sum]
  apply Finset.sum_le_sum
  intro q hq
  exact e727_phiP_le (Nat.prime_of_mem_primeFactors hq) hn hc

end erdos_727285_hyp_S21a_phi_le_hyp_support_ns

theorem erdos_727285_hyp_S21a_phi_le_hyp_support :
    ∀ n : ℕ, erdos_727285_Good n → ∀ i ∈ Finset.Ico 1 n,
      erdos_727285_phi n (n.choose i : ℤ) ≤ (erdos_727285_R n i : ℤ) := by
  exact erdos_727285_hyp_S21a_phi_le_hyp_support_ns.erdos_727285_hyp_S21a_phi_le_hyp_support

namespace erdos_727285_hyp_S21a_phi_le_hyp_symm_ns

theorem erdos_727285_hyp_S21a_phi_le_hyp_symm :
    ∀ n i : ℕ, i ≤ n → erdos_727285_R n (n - i) = erdos_727285_R n i := by
  intro n i hi
  unfold erdos_727285_R erdos_727285_J
  rw [Nat.choose_symm hi]

end erdos_727285_hyp_S21a_phi_le_hyp_symm_ns

theorem erdos_727285_hyp_S21a_phi_le_hyp_symm :
    ∀ n i : ℕ, i ≤ n → erdos_727285_R n (n - i) = erdos_727285_R n i := by
  exact erdos_727285_hyp_S21a_phi_le_hyp_symm_ns.erdos_727285_hyp_S21a_phi_le_hyp_symm

namespace erdos_727285_hyp_S21a_phi_le_hyp_large_ns
private lemma e727_choose_mono_half {n a b : ℕ} (hab : a ≤ b) (hb : b ≤ n / 2) :
    n.choose a ≤ n.choose b := by
  revert hb
  induction b, hab using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ b hab ih =>
    intro hb
    exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

private lemma e727_step32 (n k : ℕ) (h : 5 * k + 3 ≤ 2 * n) :
    3 * n.choose k ≤ 2 * n.choose (k + 1) := by
  have e := Nat.choose_succ_right_eq n k
  have h1 : 3 * (k + 1) ≤ 2 * (n - k) := by omega
  refine Nat.le_of_mul_le_mul_right ?_ (by omega : 0 < k + 1)
  calc 3 * n.choose k * (k + 1) = n.choose k * (3 * (k + 1)) := by ring
    _ ≤ n.choose k * (2 * (n - k)) := Nat.mul_le_mul le_rfl h1
    _ = 2 * (n.choose k * (n - k)) := by ring
    _ = 2 * (n.choose (k + 1) * (k + 1)) := by rw [e]
    _ = 2 * n.choose (k + 1) * (k + 1) := by ring

private lemma e727_iter (n k : ℕ) : ∀ j : ℕ, 5 * (k + j) + 3 ≤ 2 * n + 5 →
    3 ^ j * n.choose k ≤ 2 ^ j * n.choose (k + j) := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro h
    have h1 := ih (by omega)
    have h2 := e727_step32 n (k + j) (by omega)
    calc 3 ^ (j + 1) * n.choose k = 3 * (3 ^ j * n.choose k) := by ring
      _ ≤ 3 * (2 ^ j * n.choose (k + j)) := Nat.mul_le_mul le_rfl h1
      _ = 2 ^ j * (3 * n.choose (k + j)) := by ring
      _ ≤ 2 ^ j * (2 * n.choose (k + j + 1)) := Nat.mul_le_mul le_rfl h2
      _ = 2 ^ (j + 1) * n.choose (k + (j + 1)) := by
          rw [show k + (j + 1) = k + j + 1 by omega]; ring

private lemma e727_expo (j : ℕ) (hj : 10 ≤ j) : (4 * j + 2) * 2 ^ j ≤ 3 ^ j := by
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ j hj ih =>
    calc (4 * (j + 1) + 2) * 2 ^ (j + 1) = (8 * j + 12) * 2 ^ j := by ring
      _ ≤ (12 * j + 6) * 2 ^ j := Nat.mul_le_mul (by omega) le_rfl
      _ = 3 * ((4 * j + 2) * 2 ^ j) := by ring
      _ ≤ 3 * 3 ^ j := Nat.mul_le_mul le_rfl ih
      _ = 3 ^ (j + 1) := by ring

private lemma e727_comb (n i : ℕ) (hi : 35 ≤ i) (hin : 2 * i ≤ n) :
    (i - 1) * n.choose (i / 2) ≤ n.choose i := by
  set j := 3 * i / 10 with hj
  have hj10 : 10 ≤ j := by omega
  have hk : i / 2 + j ≤ i := by omega
  have hit := e727_iter n (i / 2) j (by omega)
  have hex := e727_expo j hj10
  have hmono : n.choose (i / 2 + j) ≤ n.choose i := e727_choose_mono_half hk (by omega)
  have hi1 : i - 1 ≤ 4 * j + 2 := by omega
  have hpos : 0 < 2 ^ j := by positivity
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  calc 2 ^ j * ((i - 1) * n.choose (i / 2))
        ≤ 2 ^ j * ((4 * j + 2) * n.choose (i / 2)) :=
          Nat.mul_le_mul le_rfl (Nat.mul_le_mul hi1 le_rfl)
    _ = ((4 * j + 2) * 2 ^ j) * n.choose (i / 2) := by ring
    _ ≤ 3 ^ j * n.choose (i / 2) := Nat.mul_le_mul hex le_rfl
    _ ≤ 2 ^ j * n.choose (i / 2 + j) := hit
    _ ≤ 2 ^ j * n.choose i := Nat.mul_le_mul le_rfl hmono

private lemma e727_J_le (n i q : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
    erdos_727285_J n i q ≤ i.factorization q := by
  unfold erdos_727285_J
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have h : (m + 1) * m.choose k = (m + 1).choose (k + 1) * (k + 1) := Nat.succ_mul_choose_eq m k
  have hC1 : m.choose k ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hC2 : (m + 1).choose (k + 1) ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hm1 : m + 1 ≠ 0 := by omega
  have hk1 : k + 1 ≠ 0 := by omega
  have e : ((m + 1) * m.choose k).factorization q
      = ((m + 1).choose (k + 1) * (k + 1)).factorization q := by rw [h]
  rw [Nat.factorization_mul hm1 hC1, Nat.factorization_mul hC2 hk1] at e
  simp only [Finsupp.add_apply] at e
  omega

private lemma e727_two_pow_le (n i q d : ℕ) (hi : 1 ≤ i) (hin : i ≤ n)
    (hNT : erdos_727285_NotTower n i) (hq : q ∈ n.primeFactors)
    (hd : d ∈ Finset.Icc 1 (erdos_727285_J n i q)) : 2 * q ^ d ≤ i := by
  have hqp : q.Prime := (Nat.mem_primeFactors.mp hq).1
  rw [Finset.mem_Icc] at hd
  have hJi := e727_J_le n i q hi hin
  have hJn : erdos_727285_J n i q ≤ n.factorization q := by
    unfold erdos_727285_J; omega
  set J := erdos_727285_J n i q with hJ
  have hdvd : q ^ J ∣ i := (hqp.pow_dvd_iff_le_factorization (by omega)).mpr hJi
  obtain ⟨m, hm⟩ := hdvd
  have hne : i ≠ q ^ J := hNT q hq J (Finset.mem_Icc.mpr ⟨by omega, hJn⟩)
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
    omega
  have hm1 : m ≠ 1 := by
    rintro rfl
    simp at hm
    exact hne hm
  have hm2 : 2 ≤ m := by omega
  calc 2 * q ^ d ≤ 2 * q ^ J := Nat.mul_le_mul le_rfl (Nat.pow_le_pow_right hqp.pos hd.2)
    _ ≤ m * q ^ J := Nat.mul_le_mul hm2 le_rfl
    _ = i := by rw [hm]; ring

private lemma e727_fact_sum_le (S : Finset ℕ) :
    ∀ i : ℕ, i ≠ 0 → ∑ q ∈ S, (q - 1) * i.factorization q ≤ i - 1 := by
  intro i
  induction i using Nat.strong_induction_on
  rename_i i ih
  intro hi
  by_cases h1 : i = 1
  · subst h1; simp
  obtain ⟨p, hp, hpi⟩ := Nat.exists_prime_and_dvd h1
  obtain ⟨m, rfl⟩ := hpi
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hi
  have hp2 := hp.two_le
  have hmpos := Nat.pos_of_ne_zero hm0
  have hmlt : m < p * m := by nlinarith
  have ihm := ih m hmlt hm0
  have hsplit : ∑ q ∈ S, (q - 1) * (p * m).factorization q
      = ∑ q ∈ S, (q - 1) * p.factorization q + ∑ q ∈ S, (q - 1) * m.factorization q := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    rw [Nat.factorization_mul hp.ne_zero hm0, Finsupp.add_apply, Nat.mul_add]
  have hpbound : ∑ q ∈ S, (q - 1) * p.factorization q ≤ p - 1 := by
    rw [hp.factorization]
    by_cases hpS : p ∈ S
    · rw [Finset.sum_eq_single p]
      · simp
      · intro b _ hb
        simp [Finsupp.single_apply, Ne.symm hb]
      · intro h; exact absurd hpS h
    · rw [Finset.sum_eq_zero]
      · exact Nat.zero_le _
      · intro q hq
        have hqp : p ≠ q := fun h => hpS (by rw [h]; exact hq)
        simp [Finsupp.single_apply, hqp]
  rw [hsplit]
  have hpm : p + m ≤ p * m + 1 := by nlinarith
  generalize p * m = P at *
  omega

private lemma e727_s_bound (n i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
    ∑ q ∈ n.primeFactors, (q - 1) * erdos_727285_J n i q ≤ i - 1 := by
  calc ∑ q ∈ n.primeFactors, (q - 1) * erdos_727285_J n i q
        ≤ ∑ q ∈ n.primeFactors, (q - 1) * i.factorization q := by
          apply Finset.sum_le_sum
          intro q _
          exact Nat.mul_le_mul le_rfl (e727_J_le n i q hi hin)
    _ ≤ i - 1 := e727_fact_sum_le n.primeFactors i (by omega)

theorem erdos_727285_hyp_S21a_phi_le_hyp_large :
    ∀ n : ℕ, erdos_727285_Good n → ∀ i : ℕ, 1 ≤ i → 2 * i ≤ n → 35 ≤ i →
      erdos_727285_NotTower n i → erdos_727285_R n i ≤ n.choose i := by
  intro n hn i hi hin hi35 hNT
  have hCfin := e727_comb n i hi35 hin
  have hinner : ∀ q ∈ n.primeFactors,
      ∑ d ∈ Finset.Icc 1 (erdos_727285_J n i q), n.choose (q ^ d)
        ≤ erdos_727285_J n i q * n.choose (i / 2) := by
    intro q hq
    calc ∑ d ∈ Finset.Icc 1 (erdos_727285_J n i q), n.choose (q ^ d)
          ≤ ∑ d ∈ Finset.Icc 1 (erdos_727285_J n i q), n.choose (i / 2) := by
            apply Finset.sum_le_sum
            intro d hd
            have h2 := e727_two_pow_le n i q d hi (by omega) hNT hq hd
            exact e727_choose_mono_half (by omega) (by omega)
      _ = erdos_727285_J n i q * n.choose (i / 2) := by
            rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul, Nat.add_sub_cancel]
  have hs := e727_s_bound n i hi (by omega)
  calc erdos_727285_R n i
        = ∑ q ∈ n.primeFactors, (q - 1) *
            ∑ d ∈ Finset.Icc 1 (erdos_727285_J n i q), n.choose (q ^ d) := rfl
    _ ≤ ∑ q ∈ n.primeFactors, (q - 1) * (erdos_727285_J n i q * n.choose (i / 2)) := by
        apply Finset.sum_le_sum
        intro q hq
        exact Nat.mul_le_mul le_rfl (hinner q hq)
    _ = (∑ q ∈ n.primeFactors, (q - 1) * erdos_727285_J n i q) * n.choose (i / 2) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro q _
        ring
    _ ≤ (i - 1) * n.choose (i / 2) := Nat.mul_le_mul hs le_rfl
    _ ≤ n.choose i := hCfin
end erdos_727285_hyp_S21a_phi_le_hyp_large_ns

theorem erdos_727285_hyp_S21a_phi_le_hyp_large :
    ∀ n : ℕ, erdos_727285_Good n → ∀ i : ℕ, 1 ≤ i → 2 * i ≤ n → 35 ≤ i →
      erdos_727285_NotTower n i → erdos_727285_R n i ≤ n.choose i := by
  exact erdos_727285_hyp_S21a_phi_le_hyp_large_ns.erdos_727285_hyp_S21a_phi_le_hyp_large



namespace erdos_727285_hyp_S21a_phi_le_hyp_small_ns
private lemma kummer_le (n i q : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
    n.factorization q ≤ (n.choose i).factorization q + i.factorization q := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h : (m + 1) * m.choose k = (m + 1).choose (k + 1) * (k + 1) :=
    Nat.succ_mul_choose_eq m k
  have h1 : (m + 1) ≠ 0 := by omega
  have h2 : m.choose k ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have h3 : (m + 1).choose (k + 1) ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have h4 : (k + 1) ≠ 0 := by omega
  have h' : ((m + 1) * m.choose k).factorization q
      = ((m + 1).choose (k + 1) * (k + 1)).factorization q := by rw [h]
  rw [Nat.factorization_mul h1 h2, Nat.factorization_mul h3 h4] at h'
  simp only [Finsupp.add_apply] at h'
  omega

private lemma lt_pow_aux (q : ℕ) (hq : 2 ≤ q) : ∀ d : ℕ, d < q ^ d := by
  intro d
  induction d with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    have h2 : q ^ k * 2 ≤ q ^ k * q := Nat.mul_le_mul le_rfl hq
    first | omega | nlinarith

private lemma choose_ratio (i k : ℕ) (hk : k ≤ i) :
    ∀ n, 2 * i ≤ n → n.choose k * (2 * i).choose i ≤ n.choose i * (2 * i).choose k := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact le_of_eq (Nat.mul_comm _ _)
  | succ n hn ih =>
    have e1 := Nat.choose_mul_succ_eq n k
    have e2 := Nat.choose_mul_succ_eq n i
    have hwu : n + 1 - i ≤ n + 1 - k := by omega
    have hpos : 0 < (n + 1 - k) * (n + 1 - i) := Nat.mul_pos (by omega) (by omega)
    generalize n.choose k = a at e1 ih
    generalize n.choose i = b at e2 ih
    generalize (n + 1).choose k = a' at e1 ⊢
    generalize (n + 1).choose i = b' at e2 ⊢
    generalize (2 * i).choose i = A at ih ⊢
    generalize (2 * i).choose k = B at ih ⊢
    generalize n + 1 - k = u at e1 hwu hpos
    generalize n + 1 - i = w at e2 hwu hpos
    apply le_of_mul_le_mul_right _ hpos
    calc a' * A * (u * w) = (a * (n + 1)) * A * w := by rw [e1]; ring
      _ = (a * A) * ((n + 1) * w) := by ring
      _ ≤ (b * B) * ((n + 1) * w) := by gcongr
      _ ≤ (b * B) * ((n + 1) * u) := by gcongr
      _ = (b * (n + 1)) * B * u := by ring
      _ = b' * B * (u * w) := by rw [e2]; ring

private def Wf (N i : ℕ) : ℕ :=
  ∑ q ∈ Finset.range (i + 1), ∑ d ∈ Finset.Icc 1 i,
    (if q ^ d ∣ i ∧ q ^ d < i then (q - 1) * N.choose (q ^ d) else 0)

set_option maxRecDepth 100000 in

private lemma check_raw : ∀ i < 35,
    ∑ q ∈ Finset.range (i + 1), ∑ d ∈ Finset.Icc 1 i,
      (if q ^ d ∣ i ∧ q ^ d < i then
        (q - 1) * ((2 * i).descFactorial (q ^ d) / (q ^ d).factorial) else 0)
      ≤ (2 * i).descFactorial i / i.factorial := by
  decide +kernel

private lemma check (i : ℕ) (hi : i < 35) : Wf (2 * i) i ≤ (2 * i).choose i := by
  have h := check_raw i hi
  unfold Wf
  simp only [Nat.choose_eq_descFactorial_div_factorial]
  exact h

private lemma W_mul (i n : ℕ) (hn : 2 * i ≤ n) :
    Wf n i * (2 * i).choose i ≤ n.choose i * Wf (2 * i) i := by
  unfold Wf
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q _
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d _
  split_ifs with h
  · have hr := choose_ratio i (q ^ d) (le_of_lt h.2) n hn
    generalize q - 1 = w
    calc w * n.choose (q ^ d) * (2 * i).choose i
        = w * (n.choose (q ^ d) * (2 * i).choose i) := by ring
      _ ≤ w * (n.choose i * (2 * i).choose (q ^ d)) := Nat.mul_le_mul le_rfl hr
      _ = n.choose i * (w * (2 * i).choose (q ^ d)) := by ring
  · simp

private lemma R_le_W (n i : ℕ) (hi1 : 1 ≤ i) (hin : 2 * i ≤ n)
    (hNT : erdos_727285_NotTower n i) : erdos_727285_R n i ≤ Wf n i := by
  unfold erdos_727285_R Wf
  have hi0 : i ≠ 0 := by omega
  calc ∑ q ∈ n.primeFactors, (q - 1) * ∑ d ∈ Finset.Icc 1 (erdos_727285_J n i q), n.choose (q ^ d)
      ≤ ∑ q ∈ n.primeFactors, ∑ d ∈ Finset.Icc 1 i,
          (if q ^ d ∣ i ∧ q ^ d < i then (q - 1) * n.choose (q ^ d) else 0) := by
        apply Finset.sum_le_sum
        intro q hq
        have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
        have hk := kummer_le n i q hi1 (by omega)
        have hJ1 : erdos_727285_J n i q ≤ i.factorization q := by
          unfold erdos_727285_J; omega
        have hJ2 : erdos_727285_J n i q ≤ n.factorization q := by
          unfold erdos_727285_J; omega
        have hcond : ∀ d ∈ Finset.Icc 1 (erdos_727285_J n i q), q ^ d ∣ i ∧ q ^ d < i := by
          intro d hd
          rw [Finset.mem_Icc] at hd
          have hdv : q ^ d ∣ i := (hqp.pow_dvd_iff_le_factorization hi0).mpr (by omega)
          have hne : i ≠ q ^ d := hNT q hq d (by rw [Finset.mem_Icc]; omega)
          have hle : q ^ d ≤ i := Nat.le_of_dvd (by omega) hdv
          exact ⟨hdv, lt_of_le_of_ne hle (fun h => hne h.symm)⟩
        rw [Finset.mul_sum]
        calc ∑ d ∈ Finset.Icc 1 (erdos_727285_J n i q), (q - 1) * n.choose (q ^ d)
            = ∑ d ∈ Finset.Icc 1 (erdos_727285_J n i q),
                (if q ^ d ∣ i ∧ q ^ d < i then (q - 1) * n.choose (q ^ d) else 0) :=
              Finset.sum_congr rfl (fun d hd => (if_pos (hcond d hd)).symm)
          _ ≤ _ := by
              apply Finset.sum_le_sum_of_subset
              intro d hd
              have hc := (hcond d hd).2
              have hlt := lt_pow_aux q hqp.two_le d
              rw [Finset.mem_Icc] at hd ⊢
              omega
    _ ≤ ∑ q ∈ n.primeFactors ∪ Finset.range (i + 1), ∑ d ∈ Finset.Icc 1 i,
          (if q ^ d ∣ i ∧ q ^ d < i then (q - 1) * n.choose (q ^ d) else 0) :=
        Finset.sum_le_sum_of_subset (fun x hx => Finset.mem_union_left _ hx)
    _ = ∑ q ∈ Finset.range (i + 1), ∑ d ∈ Finset.Icc 1 i,
          (if q ^ d ∣ i ∧ q ^ d < i then (q - 1) * n.choose (q ^ d) else 0) := by
        symm
        apply Finset.sum_subset (fun x hx => Finset.mem_union_right _ hx)
        intro q _ hq
        rw [Finset.mem_range] at hq
        apply Finset.sum_eq_zero
        intro d hd
        rw [Finset.mem_Icc] at hd
        rw [if_neg]
        rintro ⟨_, hlt⟩
        have : q ≤ q ^ d := by
          calc q = q ^ 1 := (pow_one q).symm
            _ ≤ q ^ d := Nat.pow_le_pow_right (by omega) hd.1
        omega

theorem erdos_727285_hyp_S21a_phi_le_hyp_small :
    ∀ n : ℕ, erdos_727285_Good n → ∀ i : ℕ, 1 ≤ i → 2 * i ≤ n → i ≤ 34 →
      erdos_727285_NotTower n i → erdos_727285_R n i ≤ n.choose i := by
  intro n _ i hi1 hi2 hi34 hNT
  have hR := R_le_W n i hi1 hi2 hNT
  have hW := W_mul i n hi2
  have hc := check i (by omega)
  have hcpos : 0 < (2 * i).choose i := Nat.choose_pos (by omega)
  have key : erdos_727285_R n i * (2 * i).choose i ≤ n.choose i * (2 * i).choose i :=
    calc erdos_727285_R n i * (2 * i).choose i ≤ Wf n i * (2 * i).choose i :=
          Nat.mul_le_mul hR le_rfl
      _ ≤ n.choose i * Wf (2 * i) i := hW
      _ ≤ n.choose i * (2 * i).choose i := Nat.mul_le_mul le_rfl hc
  exact le_of_mul_le_mul_right key hcpos
end erdos_727285_hyp_S21a_phi_le_hyp_small_ns

theorem erdos_727285_hyp_S21a_phi_le_hyp_small :
    ∀ n : ℕ, erdos_727285_Good n → ∀ i : ℕ, 1 ≤ i → 2 * i ≤ n → i ≤ 34 →
      erdos_727285_NotTower n i → erdos_727285_R n i ≤ n.choose i := by
  exact erdos_727285_hyp_S21a_phi_le_hyp_small_ns.erdos_727285_hyp_S21a_phi_le_hyp_small



theorem erdos_727285_hyp_S21a_phi_le :
    ∀ n : ℕ, erdos_727285_Good n → ∀ i ∈ Finset.Ico 1 n,
      erdos_727285_phi n (n.choose i : ℤ) ≤ (n.choose i : ℤ) := by
  intro n hn i hi
  have hi' := Finset.mem_Ico.mp hi
  by_cases ht : erdos_727285_NotTower n i ∧ erdos_727285_NotTower n (n - i)
  · have h1 := erdos_727285_hyp_S21a_phi_le_hyp_support n hn i hi
    have h2 : erdos_727285_R n i ≤ n.choose i := by
      rcases le_or_gt (2 * i) n with h | h
      · rcases le_or_gt 35 i with h' | h'
        · exact erdos_727285_hyp_S21a_phi_le_hyp_large n hn i hi'.1 h h' ht.1
        · exact erdos_727285_hyp_S21a_phi_le_hyp_small n hn i hi'.1 h (by omega) ht.1
      · have hs := erdos_727285_hyp_S21a_phi_le_hyp_symm n i hi'.2.le
        have hc : n.choose (n - i) = n.choose i := Nat.choose_symm hi'.2.le
        rw [← hs, ← hc]
        rcases le_or_gt 35 (n - i) with h' | h'
        · exact erdos_727285_hyp_S21a_phi_le_hyp_large n hn (n - i) (by omega) (by omega) h' ht.2
        · exact erdos_727285_hyp_S21a_phi_le_hyp_small n hn (n - i) (by omega) (by omega)
            (by omega) ht.2
    have h3 : (erdos_727285_R n i : ℤ) ≤ (n.choose i : ℤ) := by exact_mod_cast h2
    exact le_trans h1 h3
  · exact erdos_727285_hyp_S21a_phi_le_hyp_tower n hn i hi ht
end erdos_727285_hyp_S21a_phi_le_ns

theorem erdos_727285_hyp_S7_phi_basic :
    ∀ n : ℕ, erdos_727285_Good n →
      (∀ r : ℤ, 0 ≤ erdos_727285_phi n r) ∧
      (∀ r : ℤ, (n : ℤ) ∣ erdos_727285_phi n r - r) ∧
      (∀ r : ℤ, erdos_727285_phi n (r + (n : ℤ)) = erdos_727285_phi n r) ∧
      (∀ r : ℤ, erdos_727285_phi n (r - (n : ℤ)) = erdos_727285_phi n r) ∧
      erdos_727285_phi n 0 = 0 ∧
      erdos_727285_phi n (erdos_727285_X n) = erdos_727285_X n := by
  exact erdos_727285_hyp_S7_phi_basic_ns.erdos_727285_hyp_S7_phi_basic

theorem erdos_727285_hyp_S20_L7_small :
    ∀ n i : ℕ, erdos_727285_Good n → 1 ≤ i → i ≤ 34 → 2 * i ≤ n →
      erdos_727285_NotTower n i → erdos_727285_R n i ≤ n.choose i := by
  exact erdos_727285_hyp_S20_L7_small_ns.erdos_727285_hyp_S20_L7_small

theorem erdos_727285_hyp_S21a_phi_le :
    ∀ n : ℕ, erdos_727285_Good n → ∀ i ∈ Finset.Ico 1 n,
      erdos_727285_phi n (n.choose i : ℤ) ≤ (n.choose i : ℤ) := by
  exact erdos_727285_hyp_S21a_phi_le_ns.erdos_727285_hyp_S21a_phi_le

-- S4(b): from p^d * C(n,p^d) = n * C(n-1,p^d-1) and gcd(q^{v_q n}, p^d) = 1.
namespace erdos_727285_hyp_S4b_other_ns
-- CHECK: Nat.succ_mul_choose_eq Nat.Prime.pow_dvd_iff_le_factorization Nat.coprime_primes
theorem erdos_727285_hyp_S4b_other :
    ∀ n p q d : ℕ, n ≠ 0 → p.Prime → q.Prime → p ≠ q →
      q ^ (n.factorization q) ∣ n.choose (p ^ d) := by
  intro n p q d hn hp hq hpq
  have hqa : q ^ (n.factorization q) ∣ n :=
    (hq.pow_dvd_iff_le_factorization hn).mpr le_rfl
  have hcop : Nat.Coprime (q ^ (n.factorization q)) (p ^ d) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hq hp).mpr (Ne.symm hpq))
  have key : n ∣ n.choose (p ^ d) * p ^ d := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hpos := pow_pos hp.pos d
    obtain ⟨j, hj⟩ : ∃ j, p ^ d = j + 1 := ⟨p ^ d - 1, by omega⟩
    rw [hj]
    have h := Nat.succ_mul_choose_eq m j
    exact ⟨m.choose j, h.symm⟩
  exact hcop.dvd_of_dvd_mul_right (dvd_trans hqa key)
end erdos_727285_hyp_S4b_other_ns

theorem erdos_727285_hyp_S4b_other :
    ∀ n p q d : ℕ, n ≠ 0 → p.Prime → q.Prime → p ≠ q →
      q ^ (n.factorization q) ∣ n.choose (p ^ d) := by
  exact erdos_727285_hyp_S4b_other_ns.erdos_727285_hyp_S4b_other



-- S6(c) uniqueness: the digit vector of r depends only on r mod p^{a_p} (digit injectivity S5 + existence S6).
namespace erdos_727285_hyp_S6_phiP_congr_ns
private lemma lucas_aux (p : ℕ) (hp : p.Prime) :
    ∀ d N : ℕ, p ^ d ∣ N + 1 → Nat.choose N (p ^ d - 1) % p = 1 := by
  haveI := Fact.mk hp
  intro d
  induction d with
  | zero =>
    intro N _
    rw [pow_zero, Nat.sub_self, Nat.choose_zero_right]
    exact Nat.mod_eq_of_lt hp.one_lt
  | succ d ih =>
    intro N hN
    obtain ⟨t, ht⟩ := hN
    have h1 : N + 1 = p * (p ^ d * t) := by rw [ht]; ring
    have h0 : p ^ d * t ≠ 0 := by
      intro h0; rw [h0, mul_zero] at h1; omega
    obtain ⟨w, hw⟩ : ∃ w, p ^ d * t = w + 1 := ⟨p ^ d * t - 1, by omega⟩
    have hp2 := hp.two_le
    have hNw : N = (p - 1) + p * w := by
      have h2 : p * (w + 1) = p * w + p := by ring
      rw [hw] at h1; omega
    obtain ⟨s, hs⟩ : ∃ s, p ^ d = s + 1 := ⟨p ^ d - 1, by have := pow_pos hp.pos d; omega⟩
    have hk : p ^ (d + 1) - 1 = (p - 1) + p * s := by
      have h3 : p ^ (d + 1) = p * s + p := by rw [pow_succ, hs]; ring
      omega
    have hlt : p - 1 < p := by omega
    have hL := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p)
      (n := (p - 1) + p * w) (k := (p - 1) + p * s)
    simp only [Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ hp.pos,
      Nat.mod_eq_of_lt hlt, Nat.div_eq_of_lt hlt, Nat.choose_self, zero_add, one_mul] at hL
    have hih := ih w (Dvd.intro t hw)
    rw [hs, Nat.add_sub_cancel] at hih
    rw [hk, hNw]
    unfold Nat.ModEq at hL
    rw [hL]; exact hih

private lemma choose_decomp (n p : ℕ) (hp : p.Prime) (hn : n ≠ 0) (d : ℕ)
    (hd : d ∈ Finset.Icc 1 (n.factorization p)) :
    ∃ u : ℤ, ((n.choose (p ^ d) : ℕ) : ℤ) = (p : ℤ) ^ (n.factorization p - d) * u ∧
      ¬ (p : ℤ) ∣ u := by
  obtain ⟨hd1, hda⟩ := Finset.mem_Icc.mp hd
  have hpos : 0 < p ^ d := pow_pos hp.pos d
  obtain ⟨m, hm, hmp⟩ : ∃ m, p ^ (n.factorization p) * m = n ∧ ¬ p ∣ m :=
    ⟨_, Nat.ordProj_mul_ordCompl_eq_self n p, Nat.not_dvd_ordCompl hp hn⟩
  have hdvd : p ^ d ∣ n := (pow_dvd_pow p hda).trans (Nat.ordProj_dvd n p)
  obtain ⟨n', hn'⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨k, hk⟩ : ∃ k, p ^ d = k + 1 := ⟨p ^ d - 1, by omega⟩
  have hsc : (n' + 1) * Nat.choose n' k = Nat.choose (n' + 1) (k + 1) * (k + 1) :=
    Nat.succ_mul_choose_eq n' k
  rw [← hn', ← hk] at hsc
  have hL := lucas_aux p hp d n' (by rw [← hn']; exact hdvd)
  rw [hk, Nat.add_sub_cancel] at hL
  have hC : ¬ p ∣ Nat.choose n' k := by
    rintro ⟨c, hc⟩
    rw [hc, Nat.mul_mod_right] at hL
    omega
  have hpa : p ^ (n.factorization p - d) * p ^ d = p ^ (n.factorization p) :=
    pow_sub_mul_pow p hda
  have key : Nat.choose n (p ^ d) * p ^ d =
      p ^ (n.factorization p - d) * (m * Nat.choose n' k) * p ^ d := by
    rw [← hsc]
    have h5 : p ^ (n.factorization p - d) * (m * Nat.choose n' k) * p ^ d =
        p ^ (n.factorization p - d) * p ^ d * m * Nat.choose n' k := by ring
    rw [h5, hpa, hm]
  have hg := Nat.eq_of_mul_eq_mul_right hpos key
  refine ⟨((m * Nat.choose n' k : ℕ) : ℤ), by exact_mod_cast hg, ?_⟩
  intro h
  have h' : p ∣ m * Nat.choose n' k := by exact_mod_cast h
  rcases (Nat.Prime.dvd_mul hp).mp h' with h'' | h''
  · exact hmp h''
  · exact hC h''

private lemma uniq (p a : ℕ) (hp : p.Prime) (g : ℕ → ℤ)
    (hg : ∀ d ∈ Finset.Icc 1 a, ∃ u : ℤ, g d = (p : ℤ) ^ (a - d) * u ∧ ¬ (p : ℤ) ∣ u)
    (e e' : ℕ → ℕ) (he : ∀ d, e d < p) (he' : ∀ d, e' d < p)
    (hdiv : (p : ℤ) ^ a ∣ ∑ d ∈ Finset.Icc 1 a, ((e d : ℤ) - (e' d : ℤ)) * g d) :
    ∀ d ∈ Finset.Icc 1 a, e d = e' d := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨d1, hd1I, hd1ne⟩ := hcon
  have hSne : ((Finset.Icc 1 a).filter (fun d => e d ≠ e' d)).Nonempty :=
    ⟨d1, Finset.mem_filter.mpr ⟨hd1I, hd1ne⟩⟩
  set S := (Finset.Icc 1 a).filter (fun d => e d ≠ e' d) with hS
  set d0 := S.max' hSne with hd0
  have hd0S : d0 ∈ S := S.max'_mem hSne
  obtain ⟨hd0I, hd0ne⟩ := Finset.mem_filter.mp hd0S
  have hd0a := Finset.mem_Icc.mp hd0I
  have hrest : (p : ℤ) ^ (a - d0 + 1) ∣
      ∑ d ∈ (Finset.Icc 1 a).erase d0, ((e d : ℤ) - (e' d : ℤ)) * g d := by
    apply Finset.dvd_sum
    intro d hd
    show (p : ℤ) ^ (a - d0 + 1) ∣ ((e d : ℤ) - (e' d : ℤ)) * g d
    obtain ⟨hne, hdI⟩ := Finset.mem_erase.mp hd
    by_cases hed : e d = e' d
    · rw [hed, sub_self, zero_mul]; exact dvd_zero _
    · have hdS : d ∈ S := Finset.mem_filter.mpr ⟨hdI, hed⟩
      have hle : d ≤ d0 := S.le_max' d hdS
      have hlt : d < d0 := lt_of_le_of_ne hle hne
      have hdd := Finset.mem_Icc.mp hdI
      obtain ⟨u, hu, -⟩ := hg d hdI
      rw [hu]
      exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (pow_dvd_pow _ (by omega)) _) _
  have htot : (p : ℤ) ^ (a - d0 + 1) ∣
      ∑ d ∈ Finset.Icc 1 a, ((e d : ℤ) - (e' d : ℤ)) * g d :=
    (pow_dvd_pow _ (by omega)).trans hdiv
  rw [← Finset.add_sum_erase _ _ hd0I] at htot
  have hf0 : (p : ℤ) ^ (a - d0 + 1) ∣ ((e d0 : ℤ) - (e' d0 : ℤ)) * g d0 :=
    (dvd_add_left hrest).mp htot
  obtain ⟨u0, hu0, hnu⟩ := hg d0 hd0I
  rw [hu0, pow_succ] at hf0
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hf1 : (p : ℤ) ^ (a - d0) * p ∣
      (p : ℤ) ^ (a - d0) * (((e d0 : ℤ) - (e' d0 : ℤ)) * u0) := by
    have hr : ((e d0 : ℤ) - (e' d0 : ℤ)) * ((p : ℤ) ^ (a - d0) * u0) =
        (p : ℤ) ^ (a - d0) * (((e d0 : ℤ) - (e' d0 : ℤ)) * u0) := by ring
    rw [← hr]; exact hf0
  have h2 : (p : ℤ) ∣ ((e d0 : ℤ) - (e' d0 : ℤ)) * u0 :=
    (mul_dvd_mul_iff_left (pow_ne_zero _ hp0)).mp hf1
  have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rcases hpi.dvd_or_dvd h2 with h3 | h3
  · obtain ⟨k, hk⟩ := h3
    have hpp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
    have b1 : ((e d0 : ℕ) : ℤ) < p := by exact_mod_cast he d0
    have b2 : ((e' d0 : ℕ) : ℤ) < p := by exact_mod_cast he' d0
    have b3 : (0 : ℤ) ≤ (e d0 : ℤ) := by positivity
    have b4 : (0 : ℤ) ≤ (e' d0 : ℤ) := by positivity
    rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
    · have hk1 : k ≤ -1 := by omega
      nlinarith [mul_le_mul_of_nonneg_left hk1 hpp0.le]
    · rw [hk0, mul_zero] at hk
      exact hd0ne (by omega)
    · have hk1 : 1 ≤ k := by omega
      nlinarith [mul_le_mul_of_nonneg_left hk1 hpp0.le]
  · exact hnu h3

private lemma digits_spec (n p : ℕ) (r : ℤ)
    (h : ∃ e : ℕ → ℕ, (∀ d, e d < p) ∧
      (∀ d, d ∉ Finset.Icc 1 (n.factorization p) → e d = 0) ∧
      ((p : ℤ) ^ (n.factorization p) ∣
        r - ∑ d ∈ Finset.Icc 1 (n.factorization p), (e d : ℤ) * (n.choose (p ^ d) : ℤ))) :
    (∀ d, erdos_727285_digits n p r d < p) ∧
      ((p : ℤ) ^ (n.factorization p) ∣
        r - ∑ d ∈ Finset.Icc 1 (n.factorization p),
          (erdos_727285_digits n p r d : ℤ) * (n.choose (p ^ d) : ℤ)) := by
  have hd : erdos_727285_digits n p r = Classical.choose h := by
    rw [erdos_727285_digits, dif_pos h]
  obtain ⟨h1, -, h3⟩ := Classical.choose_spec h
  rw [hd]
  exact ⟨h1, h3⟩

private lemma digits_zero (n p : ℕ) (r : ℤ)
    (h : ¬ ∃ e : ℕ → ℕ, (∀ d, e d < p) ∧
      (∀ d, d ∉ Finset.Icc 1 (n.factorization p) → e d = 0) ∧
      ((p : ℤ) ^ (n.factorization p) ∣
        r - ∑ d ∈ Finset.Icc 1 (n.factorization p), (e d : ℤ) * (n.choose (p ^ d) : ℤ))) :
    erdos_727285_digits n p r = fun _ => 0 := by
  rw [erdos_727285_digits, dif_neg h]

theorem erdos_727285_hyp_S6_phiP_congr :
    ∀ n : ℕ, erdos_727285_Good n → ∀ p ∈ n.primeFactors, ∀ r r' : ℤ,
      (p : ℤ) ^ (n.factorization p) ∣ r - r' →
      erdos_727285_phiP n p r = erdos_727285_phiP n p r' := by
  intro n hn p hp r r' hdiv
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hn0 : n ≠ 0 := hn.1
  have key : ∀ x y : ℤ, (p : ℤ) ^ (n.factorization p) ∣ x - y →
      (∃ e : ℕ → ℕ, (∀ d, e d < p) ∧
        (∀ d, d ∉ Finset.Icc 1 (n.factorization p) → e d = 0) ∧
        ((p : ℤ) ^ (n.factorization p) ∣
          x - ∑ d ∈ Finset.Icc 1 (n.factorization p), (e d : ℤ) * (n.choose (p ^ d) : ℤ))) →
      (∃ e : ℕ → ℕ, (∀ d, e d < p) ∧
        (∀ d, d ∉ Finset.Icc 1 (n.factorization p) → e d = 0) ∧
        ((p : ℤ) ^ (n.factorization p) ∣
          y - ∑ d ∈ Finset.Icc 1 (n.factorization p), (e d : ℤ) * (n.choose (p ^ d) : ℤ))) := by
    rintro x y hxy ⟨e, h1, h2, h3⟩
    refine ⟨e, h1, h2, ?_⟩
    have h4 : y - ∑ d ∈ Finset.Icc 1 (n.factorization p), (e d : ℤ) * (n.choose (p ^ d) : ℤ) =
        (x - ∑ d ∈ Finset.Icc 1 (n.factorization p), (e d : ℤ) * (n.choose (p ^ d) : ℤ))
          - (x - y) := by ring
    rw [h4]
    exact dvd_sub h3 hxy
  unfold erdos_727285_phiP
  by_cases h : ∃ e : ℕ → ℕ, (∀ d, e d < p) ∧
      (∀ d, d ∉ Finset.Icc 1 (n.factorization p) → e d = 0) ∧
      ((p : ℤ) ^ (n.factorization p) ∣
        r - ∑ d ∈ Finset.Icc 1 (n.factorization p), (e d : ℤ) * (n.choose (p ^ d) : ℤ))
  · have h' := key r r' hdiv h
    obtain ⟨he, hs⟩ := digits_spec n p r h
    obtain ⟨he', hs'⟩ := digits_spec n p r' h'
    have huniq := uniq p (n.factorization p) hpp (fun d => (n.choose (p ^ d) : ℤ))
      (fun d hd => choose_decomp n p hpp hn0 d hd) _ _ he he' (by
        have hsum : ∑ d ∈ Finset.Icc 1 (n.factorization p),
            ((erdos_727285_digits n p r d : ℤ) - (erdos_727285_digits n p r' d : ℤ)) *
              (n.choose (p ^ d) : ℤ) =
            (r' - ∑ d ∈ Finset.Icc 1 (n.factorization p),
              (erdos_727285_digits n p r' d : ℤ) * (n.choose (p ^ d) : ℤ)) -
            (r - ∑ d ∈ Finset.Icc 1 (n.factorization p),
              (erdos_727285_digits n p r d : ℤ) * (n.choose (p ^ d) : ℤ)) + (r - r') := by
          simp only [sub_mul, Finset.sum_sub_distrib]
          ring
        show (p : ℤ) ^ (n.factorization p) ∣ ∑ d ∈ Finset.Icc 1 (n.factorization p),
            ((erdos_727285_digits n p r d : ℤ) - (erdos_727285_digits n p r' d : ℤ)) *
              (n.choose (p ^ d) : ℤ)
        rw [hsum]
        exact dvd_add (dvd_sub hs' hs) hdiv)
    apply Finset.sum_congr rfl
    intro d hd
    rw [huniq d hd]
  · have h' : ¬ ∃ e : ℕ → ℕ, (∀ d, e d < p) ∧
        (∀ d, d ∉ Finset.Icc 1 (n.factorization p) → e d = 0) ∧
        ((p : ℤ) ^ (n.factorization p) ∣
          r' - ∑ d ∈ Finset.Icc 1 (n.factorization p), (e d : ℤ) * (n.choose (p ^ d) : ℤ)) :=
      fun h'' => h (key r' r (by rw [← neg_sub]; exact dvd_neg.mpr hdiv) h'')
    rw [digits_zero n p r h, digits_zero n p r' h']
end erdos_727285_hyp_S6_phiP_congr_ns

theorem erdos_727285_hyp_S6_phiP_congr :
    ∀ n : ℕ, erdos_727285_Good n → ∀ p ∈ n.primeFactors, ∀ r r' : ℤ,
      (p : ℤ) ^ (n.factorization p) ∣ r - r' →
      erdos_727285_phiP n p r = erdos_727285_phiP n p r' := by
  exact erdos_727285_hyp_S6_phiP_congr_ns.erdos_727285_hyp_S6_phiP_congr



-- S11 case e_d < p-1: raising digit d by one gives the digit vector of r + g_d (S6(c)).
namespace erdos_727285_hyp_S11_case_lt_ns
private lemma e727_dvd_sub {k a b : ℕ} (h1 : k ∣ a) (h2 : k ∣ b) : k ∣ a - b := by
  rcases le_or_gt b a with hab | hab
  · have h : (k:ℤ) ∣ ((a - b : ℕ) : ℤ) := by
      rw [Nat.cast_sub hab]
      exact dvd_sub (Int.natCast_dvd_natCast.2 h1) (Int.natCast_dvd_natCast.2 h2)
    exact Int.natCast_dvd_natCast.1 h
  · rw [Nat.sub_eq_zero_of_le hab.le]; exact dvd_zero k

private lemma e727_vsub (p n d m : ℕ) (hp : p.Prime) (hn0 : 0 < n) (hn : p ^ d ∣ n)
    (hm0 : 0 < m) (hmd : m < p ^ d) : (n - m).factorization p = m.factorization p := by
  have hm0' : m ≠ 0 := by omega
  have hpdn : p ^ d ≤ n := Nat.le_of_dvd hn0 hn
  have hnm : n - m ≠ 0 := by omega
  have hvm : p ^ (m.factorization p) ∣ m := (hp.pow_dvd_iff_le_factorization hm0').2 le_rfl
  have hvd : m.factorization p < d := by
    by_contra h
    push_neg at h
    have h' : p ^ d ∣ m := (pow_dvd_pow p h).trans hvm
    have := Nat.le_of_dvd hm0 h'
    omega
  have h1 : p ^ (m.factorization p) ∣ n - m :=
    e727_dvd_sub ((pow_dvd_pow p hvd.le).trans hn) hvm
  have h2 : ¬ p ^ (m.factorization p + 1) ∣ n - m := by
    intro h
    have hn' : p ^ (m.factorization p + 1) ∣ n := (pow_dvd_pow p (Nat.succ_le_of_lt hvd)).trans hn
    have h3 : p ^ (m.factorization p + 1) ∣ n - (n - m) := e727_dvd_sub hn' h
    rw [Nat.sub_sub_self (by omega : m ≤ n)] at h3
    have := (hp.pow_dvd_iff_le_factorization hm0').1 h3
    omega
  have h3 := (hp.pow_dvd_iff_le_factorization hnm).1 h1
  have h4 : ¬ (m.factorization p + 1 ≤ (n - m).factorization p) :=
    fun h => h2 ((hp.pow_dvd_iff_le_factorization hnm).2 h)
  omega

private lemma e727_ndvd_choose (p n d : ℕ) (hp : p.Prime) (hn0 : 0 < n) (hn : p ^ d ∣ n) :
    ∀ j, j < p ^ d → ¬ p ∣ (n - 1).choose j := by
  have hpdn : p ^ d ≤ n := Nat.le_of_dvd hn0 hn
  intro j
  induction j with
  | zero =>
    intro _
    rw [Nat.choose_zero_right]
    exact hp.not_dvd_one
  | succ j ih =>
    intro hj
    have hB := ih (by omega)
    have heq := Nat.choose_succ_right_eq (n - 1) j
    have hsub : n - 1 - j = n - (j + 1) := by omega
    rw [hsub] at heq
    have hA0 : (n - 1).choose (j + 1) ≠ 0 := (Nat.choose_pos (by omega)).ne'
    have hB0 : (n - 1).choose j ≠ 0 := (Nat.choose_pos (by omega)).ne'
    have hv := e727_vsub p n d (j + 1) hp hn0 hn (by omega) hj
    have hf : ((n - 1).choose (j + 1) * (j + 1)).factorization p =
        ((n - 1).choose j * (n - (j + 1))).factorization p := by rw [heq]
    rw [Nat.factorization_mul hA0 (by omega), Nat.factorization_mul hB0 (by omega)] at hf
    simp only [Finsupp.add_apply] at hf
    have hB' : ((n - 1).choose j).factorization p = 0 := by
      by_contra hne
      apply hB
      have h1 : 1 ≤ ((n - 1).choose j).factorization p := by omega
      have h2 := (hp.pow_dvd_iff_le_factorization hB0).2 h1
      rwa [pow_one] at h2
    intro hA
    have h1 : p ^ 1 ∣ (n - 1).choose (j + 1) := by rw [pow_one]; exact hA
    have h2 := (hp.pow_dvd_iff_le_factorization hA0).1 h1
    omega

private lemma e727_keyK (n p d : ℕ) (hp : p.Prime) (hn0 : n ≠ 0) (hd1 : 1 ≤ d)
    (hda : d ≤ n.factorization p) :
    ∃ u, n.choose (p ^ d) = p ^ (n.factorization p - d) * u ∧ ¬ p ∣ u := by
  have hpa : p ^ (n.factorization p) ∣ n := (hp.pow_dvd_iff_le_factorization hn0).2 le_rfl
  obtain ⟨w, hw⟩ := hpa
  have hwp : ¬ p ∣ w := by
    rintro ⟨t, rfl⟩
    have h1 : p ^ (n.factorization p) * p ∣ p ^ (n.factorization p) * (p * t) :=
      mul_dvd_mul_left _ (dvd_mul_right p t)
    rw [← pow_succ, ← hw] at h1
    have := (hp.pow_dvd_iff_le_factorization hn0).1 h1
    omega
  have hn0' : 0 < n := Nat.pos_of_ne_zero hn0
  have hpd_dvd : p ^ d ∣ n := (pow_dvd_pow p hda).trans ⟨w, hw⟩
  have hpd_pos : 0 < p ^ d := pow_pos hp.pos d
  have hpdn : p ^ d ≤ n := Nat.le_of_dvd hn0' hpd_dvd
  have hc := e727_ndvd_choose p n d hp hn0' hpd_dvd (p ^ d - 1) (by omega)
  have heq : n * (n - 1).choose (p ^ d - 1) = n.choose (p ^ d) * p ^ d := by
    have h := Nat.succ_mul_choose_eq (n - 1) (p ^ d - 1)
    have e1 : n - 1 + 1 = n := by omega
    have e2 : p ^ d - 1 + 1 = p ^ d := by omega
    simp only [Nat.succ_eq_add_one, e1, e2] at h
    exact h
  refine ⟨w * (n - 1).choose (p ^ d - 1), ?_, ?_⟩
  · apply Nat.eq_of_mul_eq_mul_right hpd_pos
    rw [← heq]
    have hsplit : p ^ (n.factorization p - d) * p ^ d = p ^ (n.factorization p) := by
      rw [← pow_add]; congr 1; omega
    calc n * (n - 1).choose (p ^ d - 1)
        = p ^ (n.factorization p) * w * (n - 1).choose (p ^ d - 1) := by rw [← hw]
      _ = p ^ (n.factorization p - d) * (w * (n - 1).choose (p ^ d - 1)) * p ^ d := by
          rw [← hsplit]; ring
  · intro h
    rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h1
    · exact hwp h1
    · exact hc h1

private lemma e727_uniq (n p : ℕ) (hp : p.Prime) (hn0 : n ≠ 0) (e e' : ℕ → ℕ)
    (he : ∀ d, e d < p) (he' : ∀ d, e' d < p) : ∀ j, j ≤ n.factorization p →
    (p : ℤ) ^ (n.factorization p) ∣
      ∑ d ∈ Finset.Icc 1 j, ((e d : ℤ) - (e' d : ℤ)) * (n.choose (p ^ d) : ℤ) →
    ∀ d ∈ Finset.Icc 1 j, e d = e' d := by
  intro j
  induction j with
  | zero =>
    intro _ _ d hd
    rw [Finset.mem_Icc] at hd
    omega
  | succ j ih =>
    intro hj hdiv
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ j + 1)] at hdiv
    obtain ⟨u, hu, hup⟩ := e727_keyK n p (j + 1) hp hn0 (by omega) hj
    have hlow : (p : ℤ) ^ (n.factorization p - j) ∣
        ∑ d ∈ Finset.Icc 1 j, ((e d : ℤ) - (e' d : ℤ)) * (n.choose (p ^ d) : ℤ) := by
      apply Finset.dvd_sum
      intro d hd
      rw [Finset.mem_Icc] at hd
      obtain ⟨v, hv, -⟩ := e727_keyK n p d hp hn0 hd.1 (by omega)
      apply Dvd.dvd.mul_left
      rw [hv]; push_cast
      exact Dvd.dvd.mul_right (pow_dvd_pow _ (by omega)) _
    have htop : (p : ℤ) ^ (n.factorization p - j) ∣
        ((e (j+1) : ℤ) - (e' (j+1) : ℤ)) * (n.choose (p ^ (j+1)) : ℤ) := by
      have h1 : (p : ℤ) ^ (n.factorization p - j) ∣ (p : ℤ) ^ (n.factorization p) :=
        pow_dvd_pow _ (by omega)
      exact (dvd_add_right hlow).1 (h1.trans hdiv)
    have hpow : (p : ℤ) ^ (n.factorization p - j) =
        (p : ℤ) ^ (n.factorization p - (j + 1)) * p := by
      rw [← pow_succ]; congr 1; omega
    rw [hu, hpow] at htop
    push_cast at htop
    have htop' : (p : ℤ) ^ (n.factorization p - (j + 1)) * p ∣
        (p : ℤ) ^ (n.factorization p - (j + 1)) * (((e (j+1) : ℤ) - (e' (j+1) : ℤ)) * u) := by
      have hre : ((e (j+1) : ℤ) - (e' (j+1) : ℤ)) * ((p : ℤ) ^ (n.factorization p - (j + 1)) * (u : ℤ))
          = (p : ℤ) ^ (n.factorization p - (j + 1)) * (((e (j+1) : ℤ) - (e' (j+1) : ℤ)) * u) := by
        ring
      rw [← hre]; exact htop
    have hP0 : (p : ℤ) ^ (n.factorization p - (j + 1)) ≠ 0 :=
      pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
    have hpu : (p : ℤ) ∣ ((e (j+1) : ℤ) - (e' (j+1) : ℤ)) * u :=
      (mul_dvd_mul_iff_left hP0).1 htop'
    have hpp : _root_.Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hEq : e (j+1) = e' (j+1) := by
      rcases hpp.dvd_or_dvd hpu with h | h
      · obtain ⟨k, hk⟩ := h
        have h1 : (e (j+1) : ℤ) < p := by exact_mod_cast he (j+1)
        have h2 : (e' (j+1) : ℤ) < p := by exact_mod_cast he' (j+1)
        have h3 : (0:ℤ) ≤ e (j+1) := by positivity
        have h4 : (0:ℤ) ≤ e' (j+1) := by positivity
        have hp0 : (0:ℤ) ≤ p := by positivity
        rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
        · exfalso
          have hk1 : k ≤ -1 := by omega
          have : (p : ℤ) * k ≤ (p : ℤ) * (-1) := mul_le_mul_of_nonneg_left hk1 hp0
          linarith
        · rw [hk0, mul_zero, sub_eq_zero] at hk
          exact_mod_cast hk
        · exfalso
          have hk1 : 1 ≤ k := by omega
          have : (p : ℤ) * 1 ≤ (p : ℤ) * k := mul_le_mul_of_nonneg_left hk1 hp0
          linarith
      · exact absurd (Int.natCast_dvd_natCast.1 h) hup
    rw [hEq, sub_self, zero_mul, add_zero] at hdiv
    intro d hd
    rw [Finset.mem_Icc] at hd
    by_cases hdj : d = j + 1
    · rw [hdj]; exact hEq
    · exact ih (by omega) hdiv d (Finset.mem_Icc.2 ⟨hd.1, by omega⟩)

private lemma e727_exist (n p : ℕ) (hp : p.Prime) (hn0 : n ≠ 0) :
    ∀ j, j ≤ n.factorization p → ∀ r : ℤ, (p : ℤ) ^ (n.factorization p - j) ∣ r →
    ∃ e : ℕ → ℕ, (∀ d, e d < p) ∧ (∀ d, d ∉ Finset.Icc 1 j → e d = 0) ∧
      (p : ℤ) ^ (n.factorization p) ∣
        r - ∑ d ∈ Finset.Icc 1 j, (e d : ℤ) * (n.choose (p ^ d) : ℤ) := by
  intro j
  induction j with
  | zero =>
    intro _ r hr
    refine ⟨fun _ => 0, fun _ => hp.pos, fun _ _ => rfl, ?_⟩
    simpa using hr
  | succ j ih =>
    intro hj r hr
    obtain ⟨u, hu, hup⟩ := e727_keyK n p (j + 1) hp hn0 (by omega) hj
    obtain ⟨s, hs⟩ := hr
    obtain ⟨x, y, hxy⟩ :=
      Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hup)
    obtain ⟨c, hcdef⟩ : ∃ c : ℤ, c = y * s % p := ⟨_, rfl⟩
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hc0 : 0 ≤ c := by rw [hcdef]; exact Int.emod_nonneg _ hp0
    have hcp : c < p := by rw [hcdef]; exact Int.emod_lt_of_pos _ (by exact_mod_cast hp.pos)
    have hdm : c + p * (y * s / p) = y * s := by rw [hcdef, Int.emod_def]; ring
    have hcmod : (p : ℤ) ∣ s - c * u :=
      ⟨s * x + (y * s / p) * u, by linear_combination (-s) * hxy + (-(u:ℤ)) * hdm⟩
    obtain ⟨t, ht⟩ := hcmod
    have hpow : (p : ℤ) ^ (n.factorization p - j) =
        (p : ℤ) ^ (n.factorization p - (j + 1)) * p := by
      rw [← pow_succ]; congr 1; omega
    have hr' : (p : ℤ) ^ (n.factorization p - j) ∣ r - c * (n.choose (p ^ (j + 1)) : ℤ) := by
      refine ⟨t, ?_⟩
      rw [hs, hu, hpow]; push_cast
      linear_combination ((p : ℤ) ^ (n.factorization p - (j + 1))) * ht
    obtain ⟨e, he1, he2, he3⟩ := ih (by omega) _ hr'
    have hS : ∑ d ∈ Finset.Icc 1 (j + 1),
        ((if d = j + 1 then c.toNat else e d : ℕ) : ℤ) * (n.choose (p ^ d) : ℤ) =
        (∑ d ∈ Finset.Icc 1 j, (e d : ℤ) * (n.choose (p ^ d) : ℤ)) +
          c * (n.choose (p ^ (j + 1)) : ℤ) := by
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ j + 1), if_pos rfl, Int.toNat_of_nonneg hc0]
      congr 1
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mem_Icc] at hd
      rw [if_neg (show d ≠ j + 1 by omega)]
    refine ⟨fun d => if d = j + 1 then c.toNat else e d, ?_, ?_, ?_⟩
    · intro d
      show (if d = j + 1 then c.toNat else e d) < p
      split_ifs
      · omega
      · exact he1 d
    · intro d hd
      show (if d = j + 1 then c.toNat else e d) = 0
      have hne : d ≠ j + 1 := by
        intro h; apply hd; rw [Finset.mem_Icc]; omega
      rw [if_neg hne]
      apply he2
      intro hd'
      apply hd
      rw [Finset.mem_Icc] at hd' ⊢
      omega
    · show (p : ℤ) ^ (n.factorization p) ∣ r - ∑ d ∈ Finset.Icc 1 (j + 1),
          ((if d = j + 1 then c.toNat else e d : ℕ) : ℤ) * (n.choose (p ^ d) : ℤ)
      rw [hS]
      have h : r - ((∑ d ∈ Finset.Icc 1 j, (e d : ℤ) * (n.choose (p ^ d) : ℤ)) +
          c * (n.choose (p ^ (j + 1)) : ℤ)) =
          (r - c * (n.choose (p ^ (j + 1)) : ℤ)) -
            ∑ d ∈ Finset.Icc 1 j, (e d : ℤ) * (n.choose (p ^ d) : ℤ) := by ring
      rw [h]; exact he3

theorem erdos_727285_hyp_S11_case_lt :
    ∀ n : ℕ, erdos_727285_Good n → ∀ p ∈ n.primeFactors,
      ∀ d ∈ Finset.Icc 1 (n.factorization p), ∀ r : ℤ,
      erdos_727285_digits n p r d < p - 1 →
      erdos_727285_phiP n p (r + (n.choose (p ^ d) : ℤ)) =
        erdos_727285_phiP n p r + (n.choose (p ^ d) : ℤ) := by
  intro n hn p hp d hd r hlt
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hn0 : n ≠ 0 := hn.1
  have hspec : ∀ r' : ℤ, (∀ x, erdos_727285_digits n p r' x < p) ∧
      (∀ x, x ∉ Finset.Icc 1 (n.factorization p) → erdos_727285_digits n p r' x = 0) ∧
      (p : ℤ) ^ (n.factorization p) ∣ r' - ∑ x ∈ Finset.Icc 1 (n.factorization p),
        (erdos_727285_digits n p r' x : ℤ) * (n.choose (p ^ x) : ℤ) := by
    intro r'
    have h := e727_exist n p hpp hn0 _ le_rfl r' (by simp)
    have hd' : erdos_727285_digits n p r' = Classical.choose h := by
      unfold erdos_727285_digits; exact dif_pos h
    rw [hd']; exact Classical.choose_spec h
  obtain ⟨he1, he2, he3⟩ := hspec r
  obtain ⟨hf1, hf2, hf3⟩ := hspec (r + (n.choose (p ^ d) : ℤ))
  have hlt' : erdos_727285_digits n p r d + 1 < p := by omega
  have hsum' : ∑ x ∈ Finset.Icc 1 (n.factorization p),
      ((if x = d then erdos_727285_digits n p r d + 1 else erdos_727285_digits n p r x : ℕ) : ℤ)
        * (n.choose (p ^ x) : ℤ) =
      ∑ x ∈ Finset.Icc 1 (n.factorization p),
        (erdos_727285_digits n p r x : ℤ) * (n.choose (p ^ x) : ℤ) + (n.choose (p ^ d) : ℤ) := by
    have h1 : ∀ x ∈ Finset.Icc 1 (n.factorization p),
        ((if x = d then erdos_727285_digits n p r d + 1 else erdos_727285_digits n p r x : ℕ) : ℤ)
          * (n.choose (p ^ x) : ℤ) =
        (erdos_727285_digits n p r x : ℤ) * (n.choose (p ^ x) : ℤ) +
          (if x = d then (n.choose (p ^ x) : ℤ) else 0) := by
      intro x _
      by_cases hx : x = d
      · rw [if_pos hx, if_pos hx, hx]; push_cast; ring
      · rw [if_neg hx, if_neg hx, add_zero]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, if_pos hd]
  have hv1 : ∀ x, (if x = d then erdos_727285_digits n p r d + 1
      else erdos_727285_digits n p r x) < p := by
    intro x
    split_ifs
    · exact hlt'
    · exact he1 x
  have hdiv : (p : ℤ) ^ (n.factorization p) ∣ ∑ x ∈ Finset.Icc 1 (n.factorization p),
      ((erdos_727285_digits n p (r + (n.choose (p ^ d) : ℤ)) x : ℤ) -
        ((if x = d then erdos_727285_digits n p r d + 1 else erdos_727285_digits n p r x : ℕ) : ℤ))
        * (n.choose (p ^ x) : ℤ) := by
    have h := dvd_sub he3 hf3
    have hsplit : ∑ x ∈ Finset.Icc 1 (n.factorization p),
        ((erdos_727285_digits n p (r + (n.choose (p ^ d) : ℤ)) x : ℤ) -
          ((if x = d then erdos_727285_digits n p r d + 1 else erdos_727285_digits n p r x : ℕ) : ℤ))
          * (n.choose (p ^ x) : ℤ) =
        ∑ x ∈ Finset.Icc 1 (n.factorization p),
          (erdos_727285_digits n p (r + (n.choose (p ^ d) : ℤ)) x : ℤ) * (n.choose (p ^ x) : ℤ) -
        ∑ x ∈ Finset.Icc 1 (n.factorization p),
          ((if x = d then erdos_727285_digits n p r d + 1 else erdos_727285_digits n p r x : ℕ) : ℤ)
            * (n.choose (p ^ x) : ℤ) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [hsplit, hsum']
    have h2 : ∑ x ∈ Finset.Icc 1 (n.factorization p),
          (erdos_727285_digits n p (r + (n.choose (p ^ d) : ℤ)) x : ℤ) * (n.choose (p ^ x) : ℤ) -
        (∑ x ∈ Finset.Icc 1 (n.factorization p),
          (erdos_727285_digits n p r x : ℤ) * (n.choose (p ^ x) : ℤ) + (n.choose (p ^ d) : ℤ)) =
        (r - ∑ x ∈ Finset.Icc 1 (n.factorization p),
          (erdos_727285_digits n p r x : ℤ) * (n.choose (p ^ x) : ℤ)) -
        ((r + (n.choose (p ^ d) : ℤ)) - ∑ x ∈ Finset.Icc 1 (n.factorization p),
          (erdos_727285_digits n p (r + (n.choose (p ^ d) : ℤ)) x : ℤ) * (n.choose (p ^ x) : ℤ)) := by
      ring
    rw [h2]; exact h
  have hunq := e727_uniq n p hpp hn0
    (erdos_727285_digits n p (r + (n.choose (p ^ d) : ℤ)))
    (fun x => if x = d then erdos_727285_digits n p r d + 1 else erdos_727285_digits n p r x)
    hf1 hv1 _ le_rfl hdiv
  unfold erdos_727285_phiP
  rw [← hsum']
  apply Finset.sum_congr rfl
  intro x hx
  exact congrArg (fun t : ℕ => (t : ℤ) * (n.choose (p ^ x) : ℤ)) (hunq x hx)
end erdos_727285_hyp_S11_case_lt_ns

theorem erdos_727285_hyp_S11_case_lt :
    ∀ n : ℕ, erdos_727285_Good n → ∀ p ∈ n.primeFactors,
      ∀ d ∈ Finset.Icc 1 (n.factorization p), ∀ r : ℤ,
      erdos_727285_digits n p r d < p - 1 →
      erdos_727285_phiP n p (r + (n.choose (p ^ d) : ℤ)) =
        erdos_727285_phiP n p r + (n.choose (p ^ d) : ℤ) := by
  exact erdos_727285_hyp_S11_case_lt_ns.erdos_727285_hyp_S11_case_lt



-- S11 case e_d = p-1: carry, lower digits supported below d (S6(b)), then the carry lemma S10.
namespace erdos_727285_hyp_S11_case_top_ns
private lemma e727_digits_spec (n p : ℕ) (r : ℤ)
    (h : ∃ e : ℕ → ℕ, (∀ i, e i < p) ∧
      (∀ i, i ∉ Finset.Icc 1 (n.factorization p) → e i = 0) ∧
      ((p : ℤ) ^ (n.factorization p) ∣
        r - ∑ i ∈ Finset.Icc 1 (n.factorization p), (e i : ℤ) * (n.choose (p ^ i) : ℤ))) :
    (∀ i, erdos_727285_digits n p r i < p) ∧
      ((p : ℤ) ^ (n.factorization p) ∣
        r - ∑ i ∈ Finset.Icc 1 (n.factorization p),
          (erdos_727285_digits n p r i : ℤ) * (n.choose (p ^ i) : ℤ)) := by
  have hc : erdos_727285_digits n p r = Classical.choose h := by
    unfold erdos_727285_digits
    rw [dif_pos h]
  rw [hc]
  exact ⟨(Classical.choose_spec h).1, (Classical.choose_spec h).2.2⟩

private lemma e727_core (p a d : ℕ) (hp : p.Prime) (g : ℕ → ℤ)
    (hg : ∀ i ∈ Finset.Icc 1 a, ∃ u : ℤ, g i = (p : ℤ) ^ (a - i) * u ∧ ¬ (p : ℤ) ∣ u)
    (hgpos : ∀ i, 0 ≤ g i)
    (hcarry : ∑ i ∈ Finset.Icc 1 (d - 1), g i ≤ g d)
    (hd : d ∈ Finset.Icc 1 a)
    (e f : ℕ → ℕ) (he : ∀ i, e i < p) (hf : ∀ i, f i < p) (hed : p - 1 ≤ e d)
    (h : ℕ → ℤ) (hh : ∀ i, h i = (f i : ℤ) - e i - (if i = d then 1 else 0))
    (hdiv : (p : ℤ) ^ a ∣ ∑ i ∈ Finset.Icc 1 a, h i * g i) :
    ∑ i ∈ Finset.Icc 1 a, h i * g i ≤ 0 := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  rw [Finset.mem_Icc] at hd
  obtain ⟨hd1, hd2⟩ := hd
  have H1 : ∀ i, i ≠ d → -(p : ℤ) < h i ∧ h i < p := by
    intro i hi
    rw [hh, if_neg hi]
    have := he i
    have := hf i
    constructor <;> omega
  have H2 : ∀ m, m ≤ a → (p : ℤ) ^ (a - m) ∣ ∑ i ∈ Finset.Icc 1 m, h i * g i := by
    intro m hm
    apply Finset.dvd_sum
    intro i hi
    rw [Finset.mem_Icc] at hi
    obtain ⟨u, hu, -⟩ := hg i (Finset.mem_Icc.mpr ⟨hi.1, by omega⟩)
    rw [hu]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (pow_dvd_pow _ (by omega)) _) _
  have H3 : ∀ i, 1 ≤ i → i ≤ a → ∀ x : ℤ, (p : ℤ) ^ (a - i + 1) ∣ x * g i → (p : ℤ) ∣ x := by
    intro i hi1 hi2 x hx
    obtain ⟨u, hu, hnu⟩ := hg i (Finset.mem_Icc.mpr ⟨hi1, hi2⟩)
    rw [hu, pow_succ] at hx
    have hx' : (p : ℤ) ^ (a - i) * (p : ℤ) ∣ (p : ℤ) ^ (a - i) * (x * u) := by
      have e0 : x * ((p : ℤ) ^ (a - i) * u) = (p : ℤ) ^ (a - i) * (x * u) := by ring
      rw [e0] at hx
      exact hx
    have hne : (p : ℤ) ^ (a - i) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
    have hpx : (p : ℤ) ∣ x * u := (mul_dvd_mul_iff_left hne).mp hx'
    rcases hpz.dvd_or_dvd hpx with h1 | h1
    · exact h1
    · exact absurd h1 hnu
  have H4 : ∀ x : ℤ, (p : ℤ) ∣ x → -(p : ℤ) < x → x < p → x = 0 := by
    rintro x ⟨k, hk⟩ h1 h2
    subst hk
    rcases lt_trichotomy k 0 with hk | hk | hk
    · exfalso
      have : k ≤ -1 := by omega
      nlinarith
    · rw [hk, mul_zero]
    · exfalso
      have : 1 ≤ k := by omega
      nlinarith
  have H5 : ∀ k, d + k ≤ a → (p : ℤ) ^ a ∣ ∑ i ∈ Finset.Icc 1 (d + k), h i * g i →
      ∑ i ∈ Finset.Icc 1 (d + k), h i * g i = ∑ i ∈ Finset.Icc 1 d, h i * g i := by
    intro k
    induction k with
    | zero => intro _ _; rfl
    | succ k ih =>
      intro hk hdv
      have hsplit : ∑ i ∈ Finset.Icc 1 (d + (k + 1)), h i * g i
          = ∑ i ∈ Finset.Icc 1 (d + k), h i * g i + h (d + k + 1) * g (d + k + 1) := by
        rw [show d + (k + 1) = d + k + 1 by omega]
        exact Finset.sum_Icc_succ_top (show 1 ≤ d + k + 1 by omega) (fun i => h i * g i)
      have hlow := H2 (d + k) (by omega)
      have hterm : (p : ℤ) ^ (a - (d + k + 1) + 1) ∣ h (d + k + 1) * g (d + k + 1) := by
        have e1 : a - (d + k + 1) + 1 = a - (d + k) := by omega
        rw [e1]
        have e2 : h (d + k + 1) * g (d + k + 1)
            = ∑ i ∈ Finset.Icc 1 (d + (k + 1)), h i * g i
              - ∑ i ∈ Finset.Icc 1 (d + k), h i * g i := by
          rw [hsplit]; ring
        rw [e2]
        exact dvd_sub (dvd_trans (pow_dvd_pow _ (by omega)) hdv) hlow
      have hpd := H3 (d + k + 1) (by omega) (by omega) _ hterm
      have hne : d + k + 1 ≠ d := by omega
      have hz : h (d + k + 1) = 0 := by
        have hb := H1 (d + k + 1) hne
        exact H4 _ hpd hb.1 hb.2
      have heq : ∑ i ∈ Finset.Icc 1 (d + (k + 1)), h i * g i
          = ∑ i ∈ Finset.Icc 1 (d + k), h i * g i := by
        rw [hsplit, hz, zero_mul, add_zero]
      rw [heq]
      apply ih (by omega)
      rw [← heq]
      exact hdv
  have hS : ∑ i ∈ Finset.Icc 1 a, h i * g i = ∑ i ∈ Finset.Icc 1 d, h i * g i := by
    have := H5 (a - d) (by omega) (by rw [show d + (a - d) = a by omega]; exact hdiv)
    rwa [show d + (a - d) = a by omega] at this
  rw [hS] at hdiv ⊢
  obtain ⟨c, rfl⟩ : ∃ c, d = c + 1 := ⟨d - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hcarry
  rw [Finset.sum_Icc_succ_top (show 1 ≤ c + 1 by omega)] at hdiv ⊢
  have hlow := H2 c (by omega)
  have hterm : (p : ℤ) ^ (a - (c + 1) + 1) ∣ h (c + 1) * g (c + 1) := by
    rw [show a - (c + 1) + 1 = a - c by omega]
    have e2 : h (c + 1) * g (c + 1)
        = (∑ i ∈ Finset.Icc 1 c, h i * g i + h (c + 1) * g (c + 1))
          - ∑ i ∈ Finset.Icc 1 c, h i * g i := by ring
    rw [e2]
    exact dvd_sub (dvd_trans (pow_dvd_pow _ (by omega)) hdiv) hlow
  have hpd := H3 (c + 1) (by omega) (by omega) _ hterm
  have hhc : h (c + 1) = (f (c + 1) : ℤ) - p := by
    rw [hh, if_pos rfl]
    have := he (c + 1)
    have := hf (c + 1)
    omega
  have hf0 : h (c + 1) = -(p : ℤ) := by
    rw [hhc] at hpd ⊢
    have hfp : (p : ℤ) ∣ (f (c + 1) : ℤ) := by
      have := dvd_add hpd (dvd_refl (p : ℤ))
      simpa using this
    have hfc := hf (c + 1)
    have := H4 _ hfp (by omega) (by omega)
    omega
  have hSc : ∑ i ∈ Finset.Icc 1 c, h i * g i ≤ ((p : ℤ) - 1) * ∑ i ∈ Finset.Icc 1 c, g i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mem_Icc] at hi
    have hne : i ≠ c + 1 := by omega
    have hb : h i ≤ (p : ℤ) - 1 := by have := (H1 i hne).2; omega
    exact mul_le_mul_of_nonneg_right hb (hgpos i)
  rw [hf0]
  have hgd := hgpos (c + 1)
  have hm := mul_le_mul_of_nonneg_left hcarry (show (0 : ℤ) ≤ (p : ℤ) - 1 by linarith)
  nlinarith

private lemma e727_lucas (p : ℕ) (hp : p.Prime) :
    ∀ i N : ℕ, p ^ i ∣ N + 1 → ¬ p ∣ N.choose (p ^ i - 1) := by
  haveI := Fact.mk hp
  have hp2 : 2 ≤ p := hp.two_le
  intro i
  induction i with
  | zero =>
    intro N _
    simp only [pow_zero, Nat.sub_self, Nat.choose_zero_right, Nat.dvd_one]
    exact hp.one_lt.ne'
  | succ i ih =>
    intro N hN hdv
    obtain ⟨m, hm⟩ := hN
    have hpi : 1 ≤ p ^ i := Nat.one_le_pow _ _ hp.pos
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h, mul_zero] at hm; omega
      · exact h
    have hpm : 1 ≤ p ^ i * m := Nat.one_le_iff_ne_zero.mpr (by positivity)
    set M := p ^ i * m - 1 with hM
    have hNe : N = (p - 1) + p * M := by
      have : p ^ (i + 1) * m = p * (p ^ i * m) := by rw [pow_succ]; ring
      rw [this] at hm
      have e1 : p * (p ^ i * m) = p * M + p := by
        rw [hM]
        have : p ^ i * m = (p ^ i * m - 1) + 1 := by omega
        conv_lhs => rw [this]
        ring
      omega
    have hKe : p ^ (i + 1) - 1 = (p - 1) + p * (p ^ i - 1) := by
      have : p ^ (i + 1) = p * (p ^ i - 1) + p := by
        rw [pow_succ]
        have : p ^ i = (p ^ i - 1) + 1 := by omega
        conv_lhs => rw [this]
        ring
      omega
    have hlt : p - 1 < p := by omega
    have hmod : ∀ x : ℕ, ((p - 1) + p * x) % p = p - 1 := by
      intro x
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
    have hdiv : ∀ x : ℕ, ((p - 1) + p * x) / p = x := by
      intro x
      rw [Nat.add_mul_div_left _ _ hp.pos, Nat.div_eq_of_lt hlt, zero_add]
    have hcong := (Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := N)
      (k := p ^ (i + 1) - 1) (p := p))
    rw [hKe, hNe, hmod, hmod, hdiv, hdiv, Nat.choose_self, one_mul] at hcong
    have hMd : p ^ i ∣ M + 1 := ⟨m, by omega⟩
    apply ih M hMd
    rw [hKe, hNe] at hdv
    rw [Nat.dvd_iff_mod_eq_zero] at hdv ⊢
    rw [← hcong]
    exact hdv

private lemma e727_val (n : ℕ) (hn : erdos_727285_Good n) (p : ℕ) (hpn : p ∈ n.primeFactors)
    (i : ℕ) (hi : i ∈ Finset.Icc 1 (n.factorization p)) :
    ∃ u : ℤ, (n.choose (p ^ i) : ℤ) = (p : ℤ) ^ (n.factorization p - i) * u ∧ ¬ (p : ℤ) ∣ u := by
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpn
  have hn0 : n ≠ 0 := hn.1
  rw [Finset.mem_Icc] at hi
  obtain ⟨hi1, hi2⟩ := hi
  obtain ⟨m, hm, hmp⟩ : ∃ m, p ^ n.factorization p * m = n ∧ ¬ p ∣ m :=
    ⟨_, Nat.ordProj_mul_ordCompl_eq_self n p, Nat.not_dvd_ordCompl hp hn0⟩
  have hpi : p ^ i ∣ n := (pow_dvd_pow p hi2).trans (Nat.ordProj_dvd n p)
  have hkey := Nat.add_one_mul_choose_eq (n - 1) (p ^ i - 1)
  have h1 : n - 1 + 1 = n := by omega
  have h2 : p ^ i - 1 + 1 = p ^ i := Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.pos)
  simp only [h1, h2] at hkey
  have hsplit : p ^ n.factorization p = p ^ (n.factorization p - i) * p ^ i := by
    rw [← pow_add, Nat.sub_add_cancel hi2]
  have hC : n.choose (p ^ i) * p ^ i
      = p ^ (n.factorization p - i) * (m * (n - 1).choose (p ^ i - 1)) * p ^ i := by
    calc n.choose (p ^ i) * p ^ i = n * (n - 1).choose (p ^ i - 1) := hkey.symm
      _ = (p ^ n.factorization p * m) * (n - 1).choose (p ^ i - 1) := by rw [hm]
      _ = p ^ (n.factorization p - i) * (m * (n - 1).choose (p ^ i - 1)) * p ^ i := by
        rw [hsplit]; ring
  have hC' := Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos i) hC
  refine ⟨((m * (n - 1).choose (p ^ i - 1) : ℕ) : ℤ), ?_, ?_⟩
  · rw [hC']
    push_cast
    ring
  · intro hdvd
    have hd' : p ∣ m * (n - 1).choose (p ^ i - 1) := Int.natCast_dvd_natCast.mp hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hd' with h | h
    · exact hmp h
    · have hN : p ^ i ∣ n - 1 + 1 := by rw [h1]; exact hpi
      exact e727_lucas p hp i (n - 1) hN h

private lemma e727_double (n : ℕ) (hn : erdos_727285_Good n) (p : ℕ) (hpn : p ∈ n.primeFactors)
    (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j + 1 ≤ n.factorization p) :
    2 * (n.choose (p ^ j) : ℤ) ≤ (n.choose (p ^ (j + 1)) : ℤ) := by
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpn
  have hp2 : 2 ≤ p := hp.two_le
  have hn0 : n ≠ 0 := hn.1
  have hdvd : p ^ (j + 1) ∣ n := (pow_dvd_pow p hj2).trans (Nat.ordProj_dvd n p)
  obtain ⟨m, hm⟩ := hdvd
  have hm2 : 2 ≤ m := by
    rcases Nat.lt_or_ge m 2 with h | h
    · interval_cases m
      · simp at hm; exact absurd hm hn0
      · exact absurd (by rw [hm, mul_one]) (hn.2 p (j + 1) hp)
    · exact h
  set k := p ^ j with hk
  have hk2 : 2 ≤ k := by
    have := Nat.pow_le_pow_right hp.pos hj1
    rw [pow_one] at this
    omega
  have hK : p ^ (j + 1) = p * k := by rw [hk, pow_succ, mul_comm]
  have hKk : 2 * k ≤ p * k := Nat.mul_le_mul_right k hp2
  have hnK : 2 * (p * k) ≤ n := by rw [hm, hK]; nlinarith
  have hstep := Nat.choose_succ_right_eq n k
  have h1 : 2 * n.choose k ≤ n.choose (k + 1) := by
    have hnk : 2 * (k + 1) ≤ n - k := by omega
    have : 2 * n.choose k * (k + 1) ≤ n.choose (k + 1) * (k + 1) := by
      rw [hstep]
      calc 2 * n.choose k * (k + 1) = n.choose k * (2 * (k + 1)) := by ring
        _ ≤ n.choose k * (n - k) := Nat.mul_le_mul_left _ hnk
    exact Nat.le_of_mul_le_mul_right this (by omega)
  have hmono : ∀ s, k + 1 + s ≤ p * k → n.choose (k + 1) ≤ n.choose (k + 1 + s) := by
    intro s
    induction s with
    | zero => intro _; exact le_rfl
    | succ s ih =>
      intro hs
      have := ih (by omega)
      have h3 : k + 1 + s < n / 2 := by omega
      have := Nat.choose_le_succ_of_lt_half_left h3
      rw [show k + 1 + (s + 1) = k + 1 + s + 1 by omega]
      omega
  have h4 := hmono (p * k - (k + 1)) (by omega)
  rw [show k + 1 + (p * k - (k + 1)) = p * k by omega] at h4
  rw [hK]
  exact_mod_cast h1.trans h4

private lemma e727_carry (n : ℕ) (hn : erdos_727285_Good n) (p : ℕ) (hpn : p ∈ n.primeFactors)
    (d : ℕ) (hd : d ∈ Finset.Icc 1 (n.factorization p)) :
    ∑ i ∈ Finset.Icc 1 (d - 1), (n.choose (p ^ i) : ℤ) ≤ (n.choose (p ^ d) : ℤ) := by
  rw [Finset.mem_Icc] at hd
  obtain ⟨hd1, hd2⟩ := hd
  have key : ∀ m, m + 1 ≤ n.factorization p →
      ∑ i ∈ Finset.Icc 1 m, (n.choose (p ^ i) : ℤ) ≤ (n.choose (p ^ (m + 1)) : ℤ) := by
    intro m
    induction m with
    | zero =>
      intro _
      rw [Finset.Icc_eq_empty (by norm_num)]
      simp
    | succ m ih =>
      intro hm
      rw [Finset.sum_Icc_succ_top (show 1 ≤ m + 1 by omega)]
      have h1 := ih (by omega)
      have h2 := e727_double n hn p hpn (m + 1) (by omega) (by omega)
      linarith
  have := key (d - 1) (by omega)
  rwa [show d - 1 + 1 = d by omega] at this

theorem erdos_727285_hyp_S11_case_top :
    ∀ n : ℕ, erdos_727285_Good n → ∀ p ∈ n.primeFactors,
      ∀ d ∈ Finset.Icc 1 (n.factorization p), ∀ r : ℤ,
      p - 1 ≤ erdos_727285_digits n p r d →
      erdos_727285_phiP n p (r + (n.choose (p ^ d) : ℤ)) ≤
        erdos_727285_phiP n p r + (n.choose (p ^ d) : ℤ) := by
  intro n hn p hpn d hd r hdig
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpn
  have hp2 : 2 ≤ p := hp.two_le
  have hexr : ∃ e : ℕ → ℕ, (∀ i, e i < p) ∧
      (∀ i, i ∉ Finset.Icc 1 (n.factorization p) → e i = 0) ∧
      ((p : ℤ) ^ (n.factorization p) ∣
        r - ∑ i ∈ Finset.Icc 1 (n.factorization p), (e i : ℤ) * (n.choose (p ^ i) : ℤ)) := by
    by_contra hne
    have h0 : erdos_727285_digits n p r d = 0 := by
      unfold erdos_727285_digits
      rw [dif_neg hne]
    omega
  obtain ⟨he, hdivr⟩ := e727_digits_spec n p r hexr
  by_cases hexs : ∃ e : ℕ → ℕ, (∀ i, e i < p) ∧
      (∀ i, i ∉ Finset.Icc 1 (n.factorization p) → e i = 0) ∧
      ((p : ℤ) ^ (n.factorization p) ∣
        (r + (n.choose (p ^ d) : ℤ)) -
          ∑ i ∈ Finset.Icc 1 (n.factorization p), (e i : ℤ) * (n.choose (p ^ i) : ℤ))
  · obtain ⟨hf, hdivs⟩ := e727_digits_spec n p (r + (n.choose (p ^ d) : ℤ)) hexs
    unfold erdos_727285_phiP
    set F := erdos_727285_digits n p (r + (n.choose (p ^ d) : ℤ)) with hF
    set E := erdos_727285_digits n p r with hE
    have h1 : ∑ i ∈ Finset.Icc 1 (n.factorization p),
        (if i = d then (1 : ℤ) else 0) * (n.choose (p ^ i) : ℤ) = (n.choose (p ^ d) : ℤ) := by
      rw [Finset.sum_eq_single d]
      · simp
      · intro b _ hb
        simp [hb]
      · intro hnot
        exact absurd hd hnot
    have hsum : ∑ i ∈ Finset.Icc 1 (n.factorization p),
        ((F i : ℤ) - E i - (if i = d then 1 else 0)) * (n.choose (p ^ i) : ℤ)
        = ∑ i ∈ Finset.Icc 1 (n.factorization p), (F i : ℤ) * (n.choose (p ^ i) : ℤ)
          - ∑ i ∈ Finset.Icc 1 (n.factorization p), (E i : ℤ) * (n.choose (p ^ i) : ℤ)
          - (n.choose (p ^ d) : ℤ) := by
      rw [← h1, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hdiv : (p : ℤ) ^ (n.factorization p) ∣ ∑ i ∈ Finset.Icc 1 (n.factorization p),
        ((F i : ℤ) - E i - (if i = d then 1 else 0)) * (n.choose (p ^ i) : ℤ) := by
      rw [hsum]
      have hds := dvd_sub hdivr hdivs
      have heq : r - ∑ i ∈ Finset.Icc 1 (n.factorization p), (E i : ℤ) * (n.choose (p ^ i) : ℤ)
          - (r + (n.choose (p ^ d) : ℤ)
            - ∑ i ∈ Finset.Icc 1 (n.factorization p), (F i : ℤ) * (n.choose (p ^ i) : ℤ))
          = ∑ i ∈ Finset.Icc 1 (n.factorization p), (F i : ℤ) * (n.choose (p ^ i) : ℤ)
            - ∑ i ∈ Finset.Icc 1 (n.factorization p), (E i : ℤ) * (n.choose (p ^ i) : ℤ)
            - (n.choose (p ^ d) : ℤ) := by ring
      rw [heq] at hds
      exact hds
    have hcore : ∑ i ∈ Finset.Icc 1 (n.factorization p),
        ((F i : ℤ) - E i - (if i = d then 1 else 0)) * (n.choose (p ^ i) : ℤ) ≤ 0 :=
      e727_core p (n.factorization p) d hp (fun i => (n.choose (p ^ i) : ℤ))
        (fun i hi => e727_val n hn p hpn i hi) (fun i => by positivity)
        (e727_carry n hn p hpn d hd) hd E F he hf hdig
        (fun i => (F i : ℤ) - E i - (if i = d then 1 else 0)) (fun i => rfl) hdiv
    rw [hsum] at hcore
    linarith
  · have h0 : ∀ i, erdos_727285_digits n p (r + (n.choose (p ^ d) : ℤ)) i = 0 := by
      intro i
      unfold erdos_727285_digits
      rw [dif_neg hexs]
    have hL : erdos_727285_phiP n p (r + (n.choose (p ^ d) : ℤ)) = 0 := by
      unfold erdos_727285_phiP
      simp [h0]
    have hR : 0 ≤ erdos_727285_phiP n p r := by
      unfold erdos_727285_phiP
      apply Finset.sum_nonneg
      intro i _
      positivity
    have : (0 : ℤ) ≤ (n.choose (p ^ d) : ℤ) := by positivity
    linarith
end erdos_727285_hyp_S11_case_top_ns

theorem erdos_727285_hyp_S11_case_top :
    ∀ n : ℕ, erdos_727285_Good n → ∀ p ∈ n.primeFactors,
      ∀ d ∈ Finset.Icc 1 (n.factorization p), ∀ r : ℤ,
      p - 1 ≤ erdos_727285_digits n p r d →
      erdos_727285_phiP n p (r + (n.choose (p ^ d) : ℤ)) ≤
        erdos_727285_phiP n p r + (n.choose (p ^ d) : ℤ) := by
  exact erdos_727285_hyp_S11_case_top_ns.erdos_727285_hyp_S11_case_top



theorem erdos_727285_hyp_S11_other_primes :
    ∀ n : ℕ, erdos_727285_Good n → ∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, q ≠ p →
      ∀ d ∈ Finset.Icc 1 (n.factorization p), ∀ r : ℤ,
      erdos_727285_phiP n q (r + (n.choose (p ^ d) : ℤ)) = erdos_727285_phiP n q r := by
  intro n hG p hp q hq hqp d hd r
  apply erdos_727285_hyp_S6_phiP_congr n hG q hq
  have hdv : q ^ (n.factorization q) ∣ n.choose (p ^ d) :=
    erdos_727285_hyp_S4b_other n p q d hG.1 (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq) (Ne.symm hqp)
  have hdvZ : (q : ℤ) ^ (n.factorization q) ∣ (n.choose (p ^ d) : ℤ) := by
    exact_mod_cast hdv
  have heq : r + (n.choose (p ^ d) : ℤ) - r = (n.choose (p ^ d) : ℤ) := by ring
  rw [heq]
  exact hdvZ

theorem erdos_727285_hyp_S11_glue :
    ∀ n : ℕ, erdos_727285_Good n → ∀ p ∈ n.primeFactors,
      ∀ d ∈ Finset.Icc 1 (n.factorization p), ∀ r : ℤ,
      erdos_727285_phi n (r + (n.choose (p ^ d) : ℤ)) ≤
        erdos_727285_phi n r + (n.choose (p ^ d) : ℤ) := by
  intro n hG p hp d hd r
  have hpart : erdos_727285_phiP n p (r + (n.choose (p ^ d) : ℤ)) ≤
      erdos_727285_phiP n p r + (n.choose (p ^ d) : ℤ) := by
    rcases lt_or_ge (erdos_727285_digits n p r d) (p - 1) with h | h
    · exact (erdos_727285_hyp_S11_case_lt n hG p hp d hd r h).le
    · exact erdos_727285_hyp_S11_case_top n hG p hp d hd r h
  have hrest : ∑ q ∈ n.primeFactors.erase p,
      erdos_727285_phiP n q (r + (n.choose (p ^ d) : ℤ)) =
      ∑ q ∈ n.primeFactors.erase p, erdos_727285_phiP n q r := by
    apply Finset.sum_congr rfl
    intro q hq
    exact erdos_727285_hyp_S11_other_primes n hG p hp q (Finset.mem_of_mem_erase hq)
      (Finset.ne_of_mem_erase hq) d hd r
  unfold erdos_727285_phi
  rw [← Finset.add_sum_erase _ _ hp, ← Finset.add_sum_erase _ _ hp]
  linarith [hpart, hrest]

theorem erdos_727285_hyp_S12_T_lower :
    ∀ n : ℕ, erdos_727285_Good n →
      (∀ r : ℤ, erdos_727285_phi n r ∈ erdos_727285_T n) ∧
      (∀ t ∈ erdos_727285_T n, erdos_727285_phi n t ≤ t) := by
  intro n hG
  obtain ⟨_, _, hadd, _, h0, _⟩ := erdos_727285_hyp_S7_phi_basic n hG
  have hgen : ∀ p ∈ n.primeFactors, ∀ d ∈ Finset.Icc 1 (n.factorization p),
      (n.choose (p ^ d) : ℤ) ∈ erdos_727285_T n := by
    intro p hp d hd
    unfold erdos_727285_T
    apply AddSubmonoid.subset_closure
    unfold erdos_727285_gens
    refine Set.mem_insert_of_mem _ ?_
    rw [Set.mem_setOf_eq]
    exact ⟨p, hp, d, hd, rfl⟩
  have hn0 : (0 : ℤ) ≤ (n : ℤ) := by positivity
  refine ⟨fun r => ?_, ?_⟩
  · unfold erdos_727285_phi
    apply sum_mem
    intro p hp
    unfold erdos_727285_phiP
    apply sum_mem
    intro d hd
    have h2 : ((erdos_727285_digits n p r d : ℕ) : ℤ) * (n.choose (p ^ d) : ℤ) =
        (erdos_727285_digits n p r d) • (n.choose (p ^ d) : ℤ) := by
      rw [nsmul_eq_mul]
    rw [h2]
    exact nsmul_mem (hgen p hp d hd) _
  · have key : ∀ t ∈ erdos_727285_T n, ∀ r : ℤ,
        erdos_727285_phi n (r + t) ≤ erdos_727285_phi n r + t := by
      intro t ht
      unfold erdos_727285_T at ht
      induction ht using AddSubmonoid.closure_induction with
      | mem x hx =>
        intro r
        unfold erdos_727285_gens at hx
        rw [Set.mem_insert_iff] at hx
        rcases hx with hx | hx
        · rw [hx, hadd r]
          linarith
        · rw [Set.mem_setOf_eq] at hx
          obtain ⟨p, hp, d, hd, hxe⟩ := hx
          rw [hxe]
          exact erdos_727285_hyp_S11_glue n hG p hp d hd r
      | zero =>
        intro r
        simp
      | add x y _ _ ihx ihy =>
        intro r
        have h1 := ihx r
        have h2 := ihy (r + x)
        have h3 : r + (x + y) = r + x + y := by ring
        rw [h3]
        linarith
    intro t ht
    have h := key t ht 0
    simp only [zero_add] at h
    linarith [h0]

theorem erdos_727285_hyp_S21_choose_mem_T :
    ∀ n : ℕ, erdos_727285_Good n → ∀ i ∈ Finset.Ico 1 n,
      (n.choose i : ℤ) ∈ erdos_727285_T n := by
  intro n hG i hi
  have hle := erdos_727285_hyp_S21a_phi_le n hG i hi
  obtain ⟨_, hcong, _, _, _, _⟩ := erdos_727285_hyp_S7_phi_basic n hG
  obtain ⟨k, hk⟩ := hcong (n.choose i : ℤ)
  have hn : (0 : ℤ) < (n : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hG.1
  have hk0 : k ≤ 0 := by
    by_contra h
    push_neg at h
    nlinarith
  have hphiT := (erdos_727285_hyp_S12_T_lower n hG).1 (n.choose i : ℤ)
  have hnT : (n : ℤ) ∈ erdos_727285_T n := by
    unfold erdos_727285_T
    apply AddSubmonoid.subset_closure
    unfold erdos_727285_gens
    exact Set.mem_insert _ _
  have heq : (n.choose i : ℤ) =
      erdos_727285_phi n (n.choose i : ℤ) + ((-k).toNat) • (n : ℤ) := by
    rw [nsmul_eq_mul, Int.toNat_of_nonneg (by omega)]
    linear_combination -hk
  rw [heq]
  exact add_mem hphiT (nsmul_mem hnT _)

theorem erdos_727285 :
    ∀ n : ℕ, n ≠ 0 → (∀ p k : ℕ, p.Prime → n ≠ p ^ k) →
      ¬ erdos_727285_Rep n (erdos_727285_X n - (n : ℤ)) := by
  intro n hn hpp hrep
  have hG : erdos_727285_Good n := ⟨hn, hpp⟩
  unfold erdos_727285_Rep at hrep
  obtain ⟨c, hc⟩ := hrep
  have hmem : erdos_727285_X n - (n : ℤ) ∈ erdos_727285_T n := by
    rw [hc]
    apply sum_mem
    intro i hi
    have h1 := erdos_727285_hyp_S21_choose_mem_T n hG i hi
    have h2 : (c i : ℤ) * (n.choose i : ℤ) = (c i) • (n.choose i : ℤ) := by
      rw [nsmul_eq_mul]
    rw [h2]
    exact nsmul_mem h1 (c i)
  have hle := (erdos_727285_hyp_S12_T_lower n hG).2 _ hmem
  obtain ⟨_, _, _, hsub, _, hX⟩ := erdos_727285_hyp_S7_phi_basic n hG
  rw [hsub, hX] at hle
  have hpos : (0 : ℤ) < (n : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  linarith