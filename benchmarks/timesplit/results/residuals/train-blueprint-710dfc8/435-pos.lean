-- CHECK: Finset.sum_induction Int.eq_ofNat_of_zero_le Set.mem_setOf_eq
def Rep36823 (n : ℕ) (m : ℤ) : Prop :=
  ∃ c : ℕ → ℕ, m = ∑ i ∈ Finset.Ico 1 n, (c i : ℤ) * (n.choose i : ℤ)

def T36823 (n : ℕ) : ℤ :=
  ∑ p ∈ n.primeFactors,
    (∑ d ∈ Finset.Icc 1 (n.factorization p), (n.choose (p ^ d) : ℤ)) * ((p : ℤ) - 1)

def Adm36823 (n : ℕ) (x : ℕ → ℕ → ℕ) : Prop :=
  ∀ p ∈ n.primeFactors, ∀ d ∈ Finset.Icc 1 (n.factorization p), x p d < p

def DigSum36823 (n : ℕ) (x : ℕ → ℕ → ℕ) : ℤ :=
  ∑ p ∈ n.primeFactors, ∑ d ∈ Finset.Icc 1 (n.factorization p),
    (x p d : ℤ) * (n.choose (p ^ d) : ℤ)

def InR36823 (n : ℕ) (m : ℤ) : Prop :=
  ∃ x : ℕ → ℕ → ℕ, Adm36823 n x ∧ DigSum36823 n x ≤ m ∧ (n : ℤ) ∣ m - DigSum36823 n x

def F36823 (k : ℕ) : ℕ :=
  ∑ p ∈ k.primeFactors, (p - 1) *
    ∑ d ∈ (Finset.Icc 1 (k.factorization p)).filter (fun d => p ^ d < k), (2 * k).choose (p ^ d)

-- S5(ii)+S6(a): existence of admissible digits (valuations S3, S4, then CRT)
theorem erdos_36823_hyp_digits_exist : ∀ n : ℕ, n ≠ 0 → (∀ p k : ℕ, p.Prime → n ≠ p ^ k) →
    ∀ m : ℤ, ∃ x : ℕ → ℕ → ℕ, Adm36823 n x ∧ (n : ℤ) ∣ m - DigSum36823 n x := by
  sorry

-- S6(d): digits are at most p-1, so the digit sum is at most T
namespace erdos_36823_hyp_digits_le_ns
theorem erdos_36823_hyp_digits_le : ∀ n : ℕ, n ≠ 0 → (∀ p k : ℕ, p.Prime → n ≠ p ^ k) →
    ∀ x : ℕ → ℕ → ℕ, Adm36823 n x → DigSum36823 n x ≤ T36823 n := by
  intro n _ _ x hx
  unfold DigSum36823 T36823
  apply Finset.sum_le_sum
  intro p hp
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro d hd
  have h1 : x p d < p := hx p hp d hd
  have h2 : (x p d : ℤ) ≤ (p : ℤ) - 1 := by omega
  have h3 : (0 : ℤ) ≤ (n.choose (p ^ d) : ℤ) := by positivity
  calc (x p d : ℤ) * (n.choose (p ^ d) : ℤ)
      ≤ ((p : ℤ) - 1) * (n.choose (p ^ d) : ℤ) := mul_le_mul_of_nonneg_right h2 h3
    _ = (n.choose (p ^ d) : ℤ) * ((p : ℤ) - 1) := mul_comm _ _
end erdos_36823_hyp_digits_le_ns

theorem erdos_36823_hyp_digits_le : ∀ n : ℕ, n ≠ 0 → (∀ p k : ℕ, p.Prime → n ≠ p ^ k) →
    ∀ x : ℕ → ℕ → ℕ, Adm36823 n x → DigSum36823 n x ≤ T36823 n := by
  exact erdos_36823_hyp_digits_le_ns.erdos_36823_hyp_digits_le



-- S7 step 3, using S1(iv): indices 1 and p^d are distinct and lie in [1,n)
namespace erdos_36823_hyp_rep_digits_ns
theorem erdos_36823_hyp_rep_digits : ∀ n : ℕ, n ≠ 0 → (∀ p k : ℕ, p.Prime → n ≠ p ^ k) →
    ∀ (x : ℕ → ℕ → ℕ) (k : ℕ), Adm36823 n x →
      Rep36823 n (DigSum36823 n x + (n : ℤ) * (k : ℤ)) := by
  intro n hn0 hpk x k _hx
  have hn2 : 2 ≤ n := by
    have := hpk 2 0 Nat.prime_two
    simp at this
    omega
  have hmem : ∀ p ∈ n.primeFactors, ∀ d ∈ Finset.Icc 1 (n.factorization p),
      p ^ d ∈ Finset.Ico 1 n := by
    intro p hp d hd
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    rw [Finset.mem_Icc] at hd
    have hdvd : p ^ d ∣ n := (Nat.pow_dvd_pow p hd.2).trans (Nat.ordProj_dvd n p)
    have hle : p ^ d ≤ n := Nat.le_of_dvd (by omega) hdvd
    have hne : n ≠ p ^ d := hpk p d hpp
    have hpos : 0 < p ^ d := pow_pos hpp.pos d
    rw [Finset.mem_Ico]
    omega
  have h1 : ∑ i ∈ Finset.Ico 1 n, ((if i = 1 then k else 0 : ℕ) : ℤ) * (n.choose i : ℤ)
      = (n : ℤ) * (k : ℤ) := by
    rw [Finset.sum_eq_single 1]
    · rw [if_pos rfl, Nat.choose_one_right]
      ring
    · intro b _ hb
      rw [if_neg hb]
      simp
    · intro h
      exfalso
      exact h (by rw [Finset.mem_Ico]; omega)
  have h2 : ∑ i ∈ Finset.Ico 1 n,
      ((∑ p ∈ n.primeFactors, ∑ d ∈ Finset.Icc 1 (n.factorization p),
        (if p ^ d = i then x p d else 0) : ℕ) : ℤ) * (n.choose i : ℤ)
      = DigSum36823 n x := by
    unfold DigSum36823
    push_cast
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    rw [Finset.sum_eq_single (p ^ d)]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · intro h
      exact absurd (hmem p hp d hd) h
  refine ⟨fun i => (if i = 1 then k else 0) +
    ∑ p ∈ n.primeFactors, ∑ d ∈ Finset.Icc 1 (n.factorization p),
      (if p ^ d = i then x p d else 0), ?_⟩
  simp only [Nat.cast_add, add_mul, Finset.sum_add_distrib]
  rw [h1, h2]
  ring
end erdos_36823_hyp_rep_digits_ns

theorem erdos_36823_hyp_rep_digits : ∀ n : ℕ, n ≠ 0 → (∀ p k : ℕ, p.Prime → n ≠ p ^ k) →
    ∀ (x : ℕ → ℕ → ℕ) (k : ℕ), Adm36823 n x →
      Rep36823 n (DigSum36823 n x + (n : ℤ) * (k : ℤ)) := by
  exact erdos_36823_hyp_rep_digits_ns.erdos_36823_hyp_rep_digits



-- S11(iii): rho(0) = 0, witnessed by the zero digit family
namespace erdos_36823_hyp_zero_ns
theorem erdos_36823_hyp_zero : ∀ n : ℕ, n ≠ 0 → (∀ p k : ℕ, p.Prime → n ≠ p ^ k) →
    InR36823 n 0 := by
  intro n _ _
  refine ⟨fun _ _ => 0, ?_, ?_, ?_⟩
  · unfold Adm36823
    intro p hp d _
    show 0 < p
    exact (Nat.prime_of_mem_primeFactors hp).pos
  · simp [DigSum36823]
  · simp [DigSum36823]
end erdos_36823_hyp_zero_ns

theorem erdos_36823_hyp_zero : ∀ n : ℕ, n ≠ 0 → (∀ p k : ℕ, p.Prime → n ≠ p ^ k) →
    InR36823 n 0 := by
  exact erdos_36823_hyp_zero_ns.erdos_36823_hyp_zero



-- S9+S10: p * C(n,p^d) lies in R (doubling inequality and monotonicity S8)
theorem erdos_36823_hyp_ph : ∀ n : ℕ, n ≠ 0 → (∀ p k : ℕ, p.Prime → n ≠ p ^ k) →
    ∀ p ∈ n.primeFactors, ∀ d ∈ Finset.Icc 1 (n.factorization p),
      InR36823 n ((p : ℤ) * (n.choose (p ^ d) : ℤ)) := by
  sorry

-- S11 (Lemma 3): carry propagation, so R is closed under addition once every p*h lies in R
theorem erdos_36823_hyp_closed : ∀ n : ℕ, n ≠ 0 → (∀ p k : ℕ, p.Prime → n ≠ p ^ k) →
    (∀ p ∈ n.primeFactors, ∀ d ∈ Finset.Icc 1 (n.factorization p),
      InR36823 n ((p : ℤ) * (n.choose (p ^ d) : ℤ))) →
    ∀ a b : ℤ, InR36823 n a → InR36823 n b → InR36823 n (a + b) := by
  sorry

-- S13+S14+S15: analytic Lemma 5 for k ≥ 18
theorem erdos_36823_hyp_lemma5_large : ∀ k : ℕ, 18 ≤ k → F36823 k ≤ (2 * k).choose k := by
  sorry

-- S16: finite check of Lemma 5 for 2 ≤ k ≤ 17
namespace erdos_36823_hyp_lemma5_small_ns
private lemma F36823_eq (k : ℕ) (hk : k ≠ 0) :
    F36823 k = ∑ p ∈ (Finset.range (k+1)).filter Nat.Prime, (p - 1) *
      ∑ d ∈ (Finset.range (k+1)).filter (fun d => 1 ≤ d ∧ p ^ d ∣ k ∧ p ^ d < k),
        (2*k).choose (p^d) := by
  unfold F36823
  have hsub : k.primeFactors ⊆ (Finset.range (k+1)).filter Nat.Prime := by
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hk) hp.2.1), hp.1⟩
  rw [Finset.sum_subset hsub ?_]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.mem_filter] at hp
    congr 1
    apply Finset.sum_congr ?_ (fun _ _ => rfl)
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    rw [hp.2.pow_dvd_iff_le_factorization hk]
    have := Nat.factorization_lt p hk
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨by omega, h1, h2, h3⟩
    · rintro ⟨_, h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
  · intro p hp hnot
    rw [Finset.mem_filter] at hp
    have h0 : k.factorization p = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hdvd; exact hnot (Nat.mem_primeFactors.mpr ⟨hp.2, hdvd, hk⟩)
    rw [h0]; simp

theorem erdos_36823_hyp_lemma5_small : ∀ k : ℕ, 2 ≤ k → k ≤ 17 → F36823 k ≤ (2 * k).choose k := by
  intro k h2 h17
  rw [F36823_eq k (by omega)]
  interval_cases k <;>
    norm_num [Finset.sum_filter, Finset.sum_range_succ, Nat.choose_eq_factorial_div_factorial,
      Nat.factorial, Nat.dvd_iff_mod_eq_zero]
end erdos_36823_hyp_lemma5_small_ns

theorem erdos_36823_hyp_lemma5_small : ∀ k : ℕ, 2 ≤ k → k ≤ 17 → F36823 k ≤ (2 * k).choose k := by
  exact erdos_36823_hyp_lemma5_small_ns.erdos_36823_hyp_lemma5_small



-- S2+S12+S17: each generator lies in R, given Lemma 5
theorem erdos_36823_hyp_gen :
    (∀ k : ℕ, 2 ≤ k → F36823 k ≤ (2 * k).choose k) →
    ∀ n : ℕ, n ≠ 0 → (∀ p k : ℕ, p.Prime → n ≠ p ^ k) →
    ∀ i ∈ Finset.Ico 1 n, InR36823 n (n.choose i : ℤ) := by
  sorry

-- S5(i)+S6(b,e): uniqueness of digits forces rho(N) = T = N + n > N
namespace erdos_36823_hyp_notN_ns
private lemma h36823_id (n j : ℕ) (hn : 0 < n) (hj : 0 < j) :
    n * (n-1).choose (j-1) = n.choose j * j := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  exact Nat.succ_mul_choose_eq n' j'

private lemma h36823_pdvd (n p a j : ℕ) (hp : p.Prime) (hn : 0 < n) (ha : p ^ a ∣ n)
    (hj : 0 < j) (hja : j < p ^ a) : p ∣ n.choose j := by
  by_contra h
  have hc : Nat.Coprime (p ^ a) (n.choose j) :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).2 h)
  have h1 : p ^ a ∣ n.choose j * j := dvd_trans ha (Dvd.intro _ (h36823_id n j hn hj))
  have h2 : p ^ a ∣ j := hc.dvd_of_dvd_mul_left h1
  have := Nat.le_of_dvd hj h2
  omega

private lemma h36823_cong (n p a : ℕ) (hp : p.Prime) (hn : 0 < n) (ha : p ^ a ∣ n) :
    ∀ k, k < p ^ a → (p : ℤ) ∣ ((n-1).choose k : ℤ) - (-1) ^ k := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have h2 : p ∣ n.choose (k+1) := h36823_pdvd n p a (k+1) hp hn ha (by omega) hk
    have h3 : n.choose (k+1) = (n-1).choose k + (n-1).choose (k+1) := by
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      exact Nat.choose_succ_succ n' k
    have h4 : ((n-1).choose (k+1) : ℤ) - (-1) ^ (k+1)
        = (n.choose (k+1) : ℤ) - (((n-1).choose k : ℤ) - (-1) ^ k) := by
      rw [h3]; push_cast; ring
    rw [h4]
    exact dvd_sub (Int.natCast_dvd_natCast.mpr h2) h1

private lemma h36823_ndvd (n p a k : ℕ) (hp : p.Prime) (hn : 0 < n) (ha : p ^ a ∣ n)
    (hk : k < p ^ a) : ¬ p ∣ (n-1).choose k := by
  intro h
  have h1 := h36823_cong n p a hp hn ha k hk
  have h2 : (p : ℤ) ∣ (-1) ^ k := by
    have := dvd_sub (Int.natCast_dvd_natCast.mpr h) h1
    rwa [sub_sub_cancel] at this
  have h3 : (p : ℤ) ∣ 1 := by
    have : ((-1 : ℤ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
    rw [← this]; exact Dvd.dvd.mul_right h2 _
  have h4 : p ∣ 1 := by exact_mod_cast h3
  exact hp.one_lt.ne' (Nat.dvd_one.mp h4)

private lemma h36823_V1 (n p d : ℕ) (hp : p.Prime) (hn : n ≠ 0)
    (hd : d ≤ n.factorization p) : p ^ (n.factorization p - d) ∣ n.choose (p ^ d) := by
  have hpa : p ^ n.factorization p ∣ n := (hp.pow_dvd_iff_le_factorization hn).2 le_rfl
  have hpos : 0 < p ^ d := pow_pos hp.pos d
  have h1 : p ^ n.factorization p ∣ n.choose (p ^ d) * p ^ d :=
    dvd_trans hpa (Dvd.intro _ (h36823_id n (p ^ d) (Nat.pos_of_ne_zero hn) hpos))
  have h5 : p ^ n.factorization p = p ^ (n.factorization p - d) * p ^ d := by
    rw [← pow_add, Nat.sub_add_cancel hd]
  rw [h5] at h1
  exact Nat.dvd_of_mul_dvd_mul_right hpos h1

private lemma h36823_V2 (n p d : ℕ) (hp : p.Prime) (hn : n ≠ 0) (hd1 : 1 ≤ d)
    (hd : d ≤ n.factorization p) : ¬ p ^ (n.factorization p - d + 1) ∣ n.choose (p ^ d) := by
  intro h
  have hpa : p ^ n.factorization p ∣ n := (hp.pow_dvd_iff_le_factorization hn).2 le_rfl
  have hpos : 0 < p ^ d := pow_pos hp.pos d
  have h5 : p ^ (n.factorization p + 1) = p ^ (n.factorization p - d + 1) * p ^ d := by
    rw [← pow_add, show n.factorization p - d + 1 + d = n.factorization p + 1 by omega]
  have h1 : p ^ (n.factorization p + 1) ∣ n.choose (p ^ d) * p ^ d := by
    rw [h5]; exact mul_dvd_mul_right h _
  rw [← h36823_id n (p ^ d) (Nat.pos_of_ne_zero hn) hpos] at h1
  have hlt : p ^ d - 1 < p ^ n.factorization p := by
    have : p ^ d ≤ p ^ n.factorization p := Nat.pow_le_pow_right hp.pos hd
    omega
  have hc : Nat.Coprime (p ^ (n.factorization p + 1)) ((n-1).choose (p ^ d - 1)) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2
      (h36823_ndvd n p (n.factorization p) _ hp (Nat.pos_of_ne_zero hn) hpa hlt))
  have h2 : p ^ (n.factorization p + 1) ∣ n := hc.dvd_of_dvd_mul_right h1
  have := (hp.pow_dvd_iff_le_factorization hn).1 h2
  omega

private lemma h36823_S4 (n p q d : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hn : n ≠ 0) : p ^ n.factorization p ∣ n.choose (q ^ d) := by
  have hpa : p ^ n.factorization p ∣ n := (hp.pow_dvd_iff_le_factorization hn).2 le_rfl
  have hpos : 0 < q ^ d := pow_pos hq.pos d
  have h1 : p ^ n.factorization p ∣ n.choose (q ^ d) * q ^ d :=
    dvd_trans hpa (Dvd.intro _ (h36823_id n (q ^ d) (Nat.pos_of_ne_zero hn) hpos))
  have hc : Nat.Coprime (p ^ n.factorization p) (q ^ d) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hq).2 hpq)
  exact hc.dvd_of_dvd_mul_right h1

private lemma h36823_L (n : ℕ) (hn : n ≠ 0) (y : ℕ → ℕ → ℕ)
    (hy : ∀ p ∈ n.primeFactors, ∀ d ∈ Finset.Icc 1 (n.factorization p), y p d < p)
    (hdvd : n ∣ ∑ p ∈ n.primeFactors, ∑ d ∈ Finset.Icc 1 (n.factorization p),
        y p d * n.choose (p ^ d)) :
    ∀ p ∈ n.primeFactors, ∀ d ∈ Finset.Icc 1 (n.factorization p), y p d = 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨p, hp, d0, hd0, hy0⟩ := hcon
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  obtain ⟨D, hDS, hDmax⟩ := Finset.exists_max_image
    ((Finset.Icc 1 (n.factorization p)).filter (fun d => y p d ≠ 0)) id
    ⟨d0, Finset.mem_filter.2 ⟨hd0, hy0⟩⟩
  have hDIcc : D ∈ Finset.Icc 1 (n.factorization p) := (Finset.mem_filter.1 hDS).1
  have hyD : y p D ≠ 0 := (Finset.mem_filter.1 hDS).2
  have hDb := Finset.mem_Icc.1 hDIcc
  have hyDlt : y p D < p := hy p hp D hDIcc
  have hpa : p ^ n.factorization p ∣ n := (hpp.pow_dvd_iff_le_factorization hn).2 le_rfl
  have hKa : p ^ (n.factorization p - D + 1) ∣ p ^ n.factorization p :=
    pow_dvd_pow p (by omega)
  have hKE := dvd_trans hKa (dvd_trans hpa hdvd)
  have hR2 : p ^ (n.factorization p - D + 1) ∣ ∑ q ∈ n.primeFactors.erase p,
      ∑ d ∈ Finset.Icc 1 (n.factorization q), y q d * n.choose (q ^ d) := by
    apply Finset.dvd_sum
    intro q hq
    apply Finset.dvd_sum
    intro d _
    have hq' := Finset.mem_erase.1 hq
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq'.2
    exact Dvd.dvd.mul_left (dvd_trans hKa (h36823_S4 n p q d hpp hqp (Ne.symm hq'.1) hn)) _
  have hR1 : p ^ (n.factorization p - D + 1) ∣
      ∑ d ∈ (Finset.Icc 1 (n.factorization p)).erase D, y p d * n.choose (p ^ d) := by
    apply Finset.dvd_sum
    intro d hd
    have hd' := Finset.mem_erase.1 hd
    have hdb := Finset.mem_Icc.1 hd'.2
    by_cases hlt : D < d
    · have hz : y p d = 0 := by
        by_contra hne
        have hmem : d ∈ (Finset.Icc 1 (n.factorization p)).filter (fun d => y p d ≠ 0) :=
          Finset.mem_filter.2 ⟨hd'.2, hne⟩
        have : d ≤ D := hDmax d hmem
        omega
      rw [hz, zero_mul]
      exact dvd_zero _
    · have hdD : d < D := by have := hd'.1; omega
      exact Dvd.dvd.mul_left (dvd_trans (pow_dvd_pow p (by omega))
        (h36823_V1 n p d hpp hn hdb.2)) _
  have h1 := Finset.add_sum_erase n.primeFactors
    (fun q => ∑ d ∈ Finset.Icc 1 (n.factorization q), y q d * n.choose (q ^ d)) hp
  have h2 := Finset.add_sum_erase (Finset.Icc 1 (n.factorization p))
    (fun d => y p d * n.choose (p ^ d)) hDIcc
  try simp only at h1 h2
  rw [← h1, ← h2] at hKE
  have h3 := (Nat.dvd_add_right (dvd_add hR1 hR2)).mp (by
    rw [show ∀ a b c : ℕ, b + c + a = a + b + c from fun a b c => by ring]
    exact hKE)
  have hpy : ¬ p ∣ y p D := by
    intro h
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hyD) h
    omega
  have hc : Nat.Coprime (p ^ (n.factorization p - D + 1)) (y p D) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hpp).2 hpy)
  exact h36823_V2 n p D hpp hn hDb.1 hDb.2 (hc.dvd_of_dvd_mul_left h3)

theorem erdos_36823_hyp_notN : ∀ n : ℕ, n ≠ 0 → (∀ p k : ℕ, p.Prime → n ≠ p ^ k) →
    ¬ InR36823 n (T36823 n - n) := by
  rintro n hn _ ⟨x, hadm, hle, hdvd⟩
  have hadm' : ∀ p ∈ n.primeFactors, ∀ d ∈ Finset.Icc 1 (n.factorization p), x p d < p :=
    hadm
  have key : ∀ p ∈ n.primeFactors, ∀ d ∈ Finset.Icc 1 (n.factorization p),
      (((p - 1 - x p d) * n.choose (p ^ d) : ℕ) : ℤ)
        = (n.choose (p ^ d) : ℤ) * ((p : ℤ) - 1) - (x p d : ℤ) * (n.choose (p ^ d) : ℤ) := by
    intro p hp d hd
    have h1 := hadm' p hp d hd
    have h2 : ((p - 1 - x p d : ℕ) : ℤ) = (p : ℤ) - 1 - (x p d : ℤ) := by
      rw [Nat.cast_sub (by omega : x p d ≤ p - 1), Nat.cast_sub (by omega : 1 ≤ p)]
      simp
    rw [Nat.cast_mul, h2]; ring
  have hEq : T36823 n - DigSum36823 n x = ((∑ p ∈ n.primeFactors,
      ∑ d ∈ Finset.Icc 1 (n.factorization p), (p - 1 - x p d) * n.choose (p ^ d) : ℕ) : ℤ) := by
    unfold T36823 DigSum36823
    rw [← Finset.sum_sub_distrib, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Nat.cast_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [key p hp d hd]
  have hL := h36823_L n hn (fun p d => p - 1 - x p d)
    (fun p hp d hd => by
      have := (Nat.prime_of_mem_primeFactors hp).one_lt
      show p - 1 - x p d < p
      omega)
    (by
      have h3 : (n : ℤ) ∣ T36823 n - n - DigSum36823 n x + n := dvd_add hdvd (dvd_refl _)
      have h4 : T36823 n - n - DigSum36823 n x + n = T36823 n - DigSum36823 n x := by ring
      rw [h4, hEq] at h3
      exact Int.natCast_dvd_natCast.mp h3)
  have hzero : (∑ p ∈ n.primeFactors, ∑ d ∈ Finset.Icc 1 (n.factorization p),
      (p - 1 - x p d) * n.choose (p ^ d)) = 0 :=
    Finset.sum_eq_zero (fun p hp => Finset.sum_eq_zero (fun d hd => by
      rw [show p - 1 - x p d = 0 from hL p hp d hd, zero_mul]))
  rw [hzero] at hEq
  have hn1 : (1 : ℤ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  push_cast at hEq
  linarith
end erdos_36823_hyp_notN_ns

theorem erdos_36823_hyp_notN : ∀ n : ℕ, n ≠ 0 → (∀ p k : ℕ, p.Prime → n ≠ p ^ k) →
    ¬ InR36823 n (T36823 n - n) := by
  exact erdos_36823_hyp_notN_ns.erdos_36823_hyp_notN



theorem erdos_36823 (n : ℕ) (hn : n ≠ 0)
    (hpk : ∀ p k : ℕ, p.Prime → n ≠ p ^ k) :
    IsGreatest
      {m : ℤ | ¬ ∃ c : ℕ → ℕ, m = ∑ i ∈ Finset.Ico 1 n, (c i : ℤ) * (n.choose i : ℤ)}
      ((∑ p ∈ n.primeFactors,
        (∑ d ∈ Finset.Icc 1 (n.factorization p), (n.choose (p ^ d) : ℤ)) * ((p : ℤ) - 1)) - n) := by
  show IsGreatest {m : ℤ | ¬ Rep36823 n m} (T36823 n - (n : ℤ))
  have hnpos : (0 : ℤ) < (n : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hzero := erdos_36823_hyp_zero n hn hpk
  have hadd := erdos_36823_hyp_closed n hn hpk (erdos_36823_hyp_ph n hn hpk)
  have hL5 : ∀ k : ℕ, 2 ≤ k → F36823 k ≤ (2 * k).choose k := by
    intro k hk
    by_cases h : 18 ≤ k
    · exact erdos_36823_hyp_lemma5_large k h
    · exact erdos_36823_hyp_lemma5_small k hk (by omega)
  have hgen := erdos_36823_hyp_gen hL5 n hn hpk
  have hnotN := erdos_36823_hyp_notN n hn hpk
  have hex := erdos_36823_hyp_digits_exist n hn hpk
  have hle := erdos_36823_hyp_digits_le n hn hpk
  have hrep := erdos_36823_hyp_rep_digits n hn hpk
  have hmul : ∀ (k : ℕ) (v : ℤ), InR36823 n v → InR36823 n ((k : ℤ) * v) := by
    intro k v hv
    induction k with
    | zero => simpa using hzero
    | succ k ih =>
      have e : ((k + 1 : ℕ) : ℤ) * v = (k : ℤ) * v + v := by push_cast; ring
      rw [e]
      exact hadd _ _ ih hv
  refine ⟨?_, ?_⟩
  · show ¬ Rep36823 n (T36823 n - (n : ℤ))
    rintro ⟨c, hc⟩
    have h : InR36823 n (∑ i ∈ Finset.Ico 1 n, (c i : ℤ) * (n.choose i : ℤ)) :=
      Finset.sum_induction _ (InR36823 n) hadd hzero
        (fun i hi => hmul _ _ (hgen i hi))
    rw [← hc] at h
    exact hnotN h
  · intro m hm
    by_contra hlt
    push_neg at hlt
    obtain ⟨x, hxa, hxd⟩ := hex m
    have hb := hle x hxa
    obtain ⟨y, hy⟩ := hxd
    have hy0 : 0 ≤ y := by
      by_contra hneg
      push_neg at hneg
      have h1 : y ≤ -1 := by omega
      have h2 : (n : ℤ) * y ≤ (n : ℤ) * (-1) := mul_le_mul_of_nonneg_left h1 hnpos.le
      linarith
    lift y to ℕ using hy0 with k
    have hr := hrep x k hxa
    have he : m = DigSum36823 n x + (n : ℤ) * (k : ℤ) := by
      rw [← hy]; ring
    rw [he] at hm
    exact (show ¬ Rep36823 n (DigSum36823 n x + (n : ℤ) * (k : ℤ)) from hm) hr