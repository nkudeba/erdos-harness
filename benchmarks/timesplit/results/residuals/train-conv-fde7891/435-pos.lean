def erdos_27285_Rep (n : ℕ) (m : ℤ) : Prop :=
  ∃ c : ℕ → ℕ, m = ∑ i ∈ Finset.Ico 1 n, (c i : ℤ) * (n.choose i : ℤ)

def erdos_27285_X (n : ℕ) : ℤ :=
  ∑ p ∈ n.primeFactors,
    (∑ d ∈ Finset.Icc 1 (n.factorization p), (n.choose (p ^ d) : ℤ)) * ((p : ℤ) - 1)

namespace erdos_27285_hyp_rep_add_ns
theorem erdos_27285_hyp_rep_add :
    ∀ n : ℕ, 2 ≤ n → ∀ y k : ℤ, erdos_27285_Rep n y → 0 ≤ k →
      erdos_27285_Rep n (y + k * (n : ℤ)) := by
  intro n hn y k hy hk
  obtain ⟨c, rfl⟩ := hy
  refine ⟨fun i => c i + if i = 1 then k.toNat else 0, ?_⟩
  have h1 : (1:ℕ) ∈ Finset.Ico 1 n := Finset.mem_Ico.mpr ⟨le_refl _, by omega⟩
  simp only [Nat.cast_add, Nat.cast_ite, Nat.cast_zero, add_mul, Finset.sum_add_distrib,
    ite_mul, zero_mul]
  rw [Finset.sum_ite_eq', if_pos h1, Nat.choose_one_right, Int.toNat_of_nonneg hk]
end erdos_27285_hyp_rep_add_ns

-- Elementary closure fact: n = C(n,1) is a generator when n ≥ 2, so raising c 1 by k
-- adds k*n to a representation.
theorem erdos_27285_hyp_rep_add :
    ∀ n : ℕ, 2 ≤ n → ∀ y k : ℤ, erdos_27285_Rep n y → 0 ≤ k →
      erdos_27285_Rep n (y + k * (n : ℤ)) := by
  exact erdos_27285_hyp_rep_add_ns.erdos_27285_hyp_rep_add

namespace erdos_27285_hyp_cover_ns
-- CHECK: Nat.succ_mul_choose_eq Nat.isCoprime_iff_coprime Nat.factorization_prime_le_iff_dvd Finset.sum_nbij'
private lemma choose_prime_dvd (p N d j : ℕ) (hp : p.Prime) (hd : p ^ d ∣ N + 1)
    (hj0 : 0 < j) (hj : j < p ^ d) : p ∣ (N + 1).choose j := by
  obtain ⟨J, rfl⟩ : ∃ J, j = J + 1 := ⟨j - 1, by omega⟩
  by_contra h
  have hc : Nat.Coprime (p ^ d) ((N + 1).choose (J + 1)) :=
    Nat.Coprime.pow_left d ((Nat.Prime.coprime_iff_not_dvd hp).mpr h)
  have key : (N + 1).choose (J + 1) * (J + 1) = (N + 1) * N.choose J := by
    first
    | exact (Nat.succ_mul_choose_eq N J).symm
    | exact (Nat.add_one_mul_choose_eq N J).symm
  have h2 : p ^ d ∣ (N + 1).choose (J + 1) * (J + 1) := by
    rw [key]; exact Dvd.dvd.mul_right hd _
  have h3 : p ^ d ∣ J + 1 := by
    first
    | exact hc.dvd_of_dvd_mul_left h2
    | exact hc.dvd_of_dvd_mul_right (by rwa [mul_comm] at h2)
  have h4 := Nat.le_of_dvd (by omega) h3
  omega

private lemma choose_pred_mod (p N d : ℕ) (hp : p.Prime) (hd : p ^ d ∣ N + 1) :
    ∀ k, k < p ^ d → (p : ℤ) ∣ (N.choose k : ℤ) - (-1) ^ k := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have h2 : p ∣ (N + 1).choose (k + 1) := choose_prime_dvd p N d (k + 1) hp hd (by omega) hk
    have h2' : (p : ℤ) ∣ ((N + 1).choose (k + 1) : ℤ) := by exact_mod_cast h2
    have h3 : (N + 1).choose (k + 1) = N.choose k + N.choose (k + 1) := Nat.choose_succ_succ N k
    have h4 : (N.choose (k + 1) : ℤ) - (-1) ^ (k + 1)
        = ((N + 1).choose (k + 1) : ℤ) - ((N.choose k : ℤ) - (-1) ^ k) := by
      rw [h3]; push_cast; ring
    rw [h4]; exact dvd_sub h2' h1

private lemma not_dvd_choose_pred (p N d : ℕ) (hp : p.Prime) (hd : p ^ d ∣ N + 1) :
    ¬ p ∣ N.choose (p ^ d - 1) := by
  intro h
  have hpos := pow_pos hp.pos d
  have h1 := choose_pred_mod p N d hp hd (p ^ d - 1) (by omega)
  have h2 : (p : ℤ) ∣ (N.choose (p ^ d - 1) : ℤ) := by exact_mod_cast h
  have h3 : (p : ℤ) ∣ (-1 : ℤ) ^ (p ^ d - 1) := by
    have := dvd_sub h2 h1
    rwa [sub_sub_cancel] at this
  have h4 : (p : ℤ) ∣ 1 := by
    rcases neg_one_pow_eq_or ℤ (p ^ d - 1) with h5 | h5
    · rwa [h5] at h3
    · rw [h5] at h3; exact (dvd_neg).mp h3
  have h5 : p ∣ 1 := by exact_mod_cast h4
  exact hp.one_lt.ne' (Nat.dvd_one.mp h5)

private lemma choose_ppow_eq (n p d : ℕ) (hp : p.Prime) (hn : n ≠ 0) (hd : d ≤ n.factorization p) :
    n.choose (p ^ d) = p ^ (n.factorization p - d) *
      ((n / p ^ (n.factorization p)) * (n - 1).choose (p ^ d - 1)) := by
  have hpa : p ^ n.factorization p ∣ n := (hp.pow_dvd_iff_le_factorization hn).mpr le_rfl
  have hpd : p ^ d - 1 + 1 = p ^ d := by have := pow_pos hp.pos d; omega
  have key : n * (n - 1).choose (p ^ d - 1) = n.choose (p ^ d) * p ^ d := by
    obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
    have k0 : (N + 1) * N.choose (p ^ d - 1) = (N + 1).choose (p ^ d - 1 + 1) * (p ^ d - 1 + 1) := by
      first
      | exact Nat.succ_mul_choose_eq N (p ^ d - 1)
      | exact Nat.add_one_mul_choose_eq N (p ^ d - 1)
    rw [hpd] at k0
    rw [Nat.add_sub_cancel]; exact k0
  have hpow : p ^ n.factorization p = p ^ d * p ^ (n.factorization p - d) := by
    rw [← pow_add, Nat.add_sub_of_le hd]
  apply Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos d)
  calc p ^ d * n.choose (p ^ d) = n.choose (p ^ d) * p ^ d := mul_comm _ _
    _ = n * (n - 1).choose (p ^ d - 1) := key.symm
    _ = p ^ n.factorization p * (n / p ^ n.factorization p) * (n - 1).choose (p ^ d - 1) := by
        rw [Nat.mul_div_cancel' hpa]
    _ = p ^ d * (p ^ (n.factorization p - d) *
          ((n / p ^ n.factorization p) * (n - 1).choose (p ^ d - 1))) := by
        rw [hpow]; ring

private lemma digits_aux (p : ℤ) (hp : 0 < p) : ∀ (a : ℕ) (u : ℕ → ℤ) (t : ℤ),
    (∀ j, IsCoprime (u j) p) →
    ∃ e : ℕ → ℕ, (∀ j, (e j : ℤ) < p) ∧
      p ^ a ∣ (∑ j ∈ Finset.range a, (e j : ℤ) * p ^ j * u j) - t := by
  intro a
  induction a with
  | zero =>
    intro u t _
    refine ⟨fun _ => 0, fun _ => by simp only [Nat.cast_zero]; exact hp, ?_⟩
    rw [pow_zero]; exact one_dvd _
  | succ a ih =>
    intro u t hu
    obtain ⟨α, β, hαβ⟩ := hu 0
    obtain ⟨r, hr⟩ : ∃ r, r = (t * α) % p := ⟨_, rfl⟩
    have hr0 : 0 ≤ r := by rw [hr]; exact Int.emod_nonneg _ hp.ne'
    have hrp : r < p := by rw [hr]; exact Int.emod_lt_of_pos _ hp
    have hrdef : r = t * α - p * (t * α / p) := by rw [hr]; exact Int.emod_def _ _
    have hdv : p ∣ t - r * u 0 :=
      ⟨(t * α / p) * u 0 + t * β, by rw [hrdef]; linear_combination (-t) * hαβ⟩
    obtain ⟨t', ht'⟩ := hdv
    obtain ⟨e', he'lt, he'⟩ := ih (fun j => u (j + 1)) t' (fun j => hu (j + 1))
    obtain ⟨e, he0, hes⟩ : ∃ e : ℕ → ℕ, e 0 = r.toNat ∧ ∀ i, e (i + 1) = e' i :=
      ⟨fun j => if j = 0 then r.toNat else e' (j - 1), by simp, fun i => by simp⟩
    have hre : ((r.toNat : ℕ) : ℤ) = r := Int.toNat_of_nonneg hr0
    refine ⟨e, ?_, ?_⟩
    · intro j
      cases j with
      | zero => rw [he0, hre]; exact hrp
      | succ i => rw [hes]; exact he'lt i
    · rw [Finset.sum_range_succ']
      have hs : ∑ i ∈ Finset.range a, (e (i + 1) : ℤ) * p ^ (i + 1) * u (i + 1)
          = p * ∑ i ∈ Finset.range a, (e' i : ℤ) * p ^ i * u (i + 1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [hes, pow_succ]; ring
      rw [hs, he0, hre, pow_zero, mul_one]
      have hfin : p * ∑ i ∈ Finset.range a, (e' i : ℤ) * p ^ i * u (i + 1) + r * u 0 - t
          = p * ((∑ i ∈ Finset.range a, (e' i : ℤ) * p ^ i * u (i + 1)) - t') := by
        linear_combination (-1 : ℤ) * ht'
      rw [hfin, pow_succ']
      exact mul_dvd_mul_left p he'

private lemma rep_zero (n : ℕ) : erdos_27285_Rep n 0 := ⟨fun _ => 0, by simp⟩

private lemma rep_add {n : ℕ} {y z : ℤ} (hy : erdos_27285_Rep n y) (hz : erdos_27285_Rep n z) :
    erdos_27285_Rep n (y + z) := by
  obtain ⟨c1, rfl⟩ := hy
  obtain ⟨c2, rfl⟩ := hz
  refine ⟨fun i => c1 i + c2 i, ?_⟩
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  push_cast; ring

private lemma rep_single (e : ℕ) {n i : ℕ} (hi : i ∈ Finset.Ico 1 n) :
    erdos_27285_Rep n ((e : ℤ) * (n.choose i : ℤ)) := by
  refine ⟨fun k => if k = i then e else 0, ?_⟩
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd hi h

private lemma rep_sum {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (h : ∀ x ∈ s, erdos_27285_Rep n (f x)) : erdos_27285_Rep n (∑ x ∈ s, f x) :=
  Finset.sum_induction f (erdos_27285_Rep n) (fun _ _ ha hb => rep_add ha hb) (rep_zero n) h

private lemma prime_part (n p : ℕ) (hp : p.Prime) (hn : n ≠ 0) (hnp : ∀ k : ℕ, n ≠ p ^ k) (t : ℤ) :
    ∃ y : ℤ, erdos_27285_Rep n y ∧
      y ≤ (∑ d ∈ Finset.Icc 1 (n.factorization p), (n.choose (p ^ d) : ℤ)) * ((p : ℤ) - 1) ∧
      ((n / p ^ (n.factorization p) : ℕ) : ℤ) ∣ y ∧ ((p : ℤ) ^ (n.factorization p)) ∣ y - t := by
  set F := n.factorization p with hF
  have hpF : p ^ F ∣ n := (hp.pow_dvd_iff_le_factorization hn).mpr (by omega)
  have hnd : ¬ p ∣ n / p ^ F := by
    intro h
    have h2 : p ^ (F + 1) ∣ n := by
      have e : n = p ^ F * (n / p ^ F) := (Nat.mul_div_cancel' hpF).symm
      rw [e, pow_succ]
      exact mul_dvd_mul_left _ h
    have := (hp.pow_dvd_iff_le_factorization hn).mp h2
    omega
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hu : ∀ j, IsCoprime ((((n / p ^ F) * (n - 1).choose (p ^ (F - j) - 1) : ℕ) : ℤ)) (p : ℤ) := by
    intro j
    have hv : ¬ p ∣ (n - 1).choose (p ^ (F - j) - 1) := by
      apply not_dvd_choose_pred p (n - 1) (F - j) hp
      rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
      exact (pow_dvd_pow p (Nat.sub_le F j)).trans hpF
    have hc : Nat.Coprime ((n / p ^ F) * (n - 1).choose (p ^ (F - j) - 1)) p :=
      Nat.coprime_mul_iff_left.mpr ⟨((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd).symm,
        ((Nat.Prime.coprime_iff_not_dvd hp).mpr hv).symm⟩
    exact Nat.isCoprime_iff_coprime.mpr hc
  obtain ⟨e, he, hdiv⟩ : ∃ e : ℕ → ℕ, (∀ j, (e j : ℤ) < p) ∧ (p : ℤ) ^ F ∣
      (∑ j ∈ Finset.range F, (e j : ℤ) * (p : ℤ) ^ j *
        ((((n / p ^ F) * (n - 1).choose (p ^ (F - j) - 1) : ℕ) : ℤ))) - t :=
    digits_aux (p : ℤ) hp0 F
      (fun j => (((n / p ^ F) * (n - 1).choose (p ^ (F - j) - 1) : ℕ) : ℤ)) t hu
  have hterm : ∀ j ∈ Finset.range F, (e j : ℤ) * (p : ℤ) ^ j *
      ((((n / p ^ F) * (n - 1).choose (p ^ (F - j) - 1) : ℕ) : ℤ))
      = (e j : ℤ) * (n.choose (p ^ (F - j)) : ℤ) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have h1 := choose_ppow_eq n p (F - j) hp hn (by omega)
    rw [← hF] at h1
    rw [show F - (F - j) = j by omega] at h1
    rw [h1]; push_cast; ring
  have hsum : (∑ j ∈ Finset.range F, (e j : ℤ) * (p : ℤ) ^ j *
      ((((n / p ^ F) * (n - 1).choose (p ^ (F - j) - 1) : ℕ) : ℤ)))
      = ∑ j ∈ Finset.range F, (e j : ℤ) * (n.choose (p ^ (F - j)) : ℤ) :=
    Finset.sum_congr rfl hterm
  rw [hsum] at hdiv
  refine ⟨∑ j ∈ Finset.range F, (e j : ℤ) * (n.choose (p ^ (F - j)) : ℤ), ?_, ?_, ?_, hdiv⟩
  · apply rep_sum
    intro j _
    apply rep_single
    rw [Finset.mem_Ico]
    have h1 : p ^ (F - j) ∣ n := (pow_dvd_pow p (Nat.sub_le F j)).trans hpF
    have h2 : p ^ (F - j) ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h1
    have h3 : p ^ (F - j) ≠ n := fun h => hnp (F - j) h.symm
    have h4 := pow_pos hp.pos (F - j)
    omega
  · have hle : ∀ j ∈ Finset.range F, (e j : ℤ) * (n.choose (p ^ (F - j)) : ℤ)
        ≤ ((p : ℤ) - 1) * (n.choose (p ^ (F - j)) : ℤ) := by
      intro j _
      have : (e j : ℤ) ≤ (p : ℤ) - 1 := by have := he j; omega
      exact mul_le_mul_of_nonneg_right this (Nat.cast_nonneg _)
    refine le_trans (Finset.sum_le_sum hle) (le_of_eq ?_)
    rw [Finset.sum_mul]
    apply Finset.sum_nbij' (fun j => F - j) (fun d => F - d)
    · intro j hj; simp only [Finset.mem_range, Finset.mem_Icc, Finset.mem_coe] at hj ⊢; omega
    · intro d hd; simp only [Finset.mem_range, Finset.mem_Icc, Finset.mem_coe] at hd ⊢; omega
    · intro j hj; simp only [Finset.mem_range, Finset.mem_coe] at hj ⊢; omega
    · intro d hd; simp only [Finset.mem_Icc, Finset.mem_coe] at hd ⊢; omega
    · intro j _
      show ((p : ℤ) - 1) * (n.choose (p ^ (F - j)) : ℤ) = (n.choose (p ^ (F - j)) : ℤ) * ((p : ℤ) - 1)
      ring
  · apply Finset.dvd_sum
    intro j hj
    rw [← hterm j hj]
    apply Dvd.dvd.mul_left
    push_cast
    exact dvd_mul_right _ _

private lemma dvd_of_forall_ppow (n : ℕ) (hn : n ≠ 0) (z : ℤ)
    (h : ∀ p ∈ n.primeFactors, ((p : ℤ) ^ n.factorization p) ∣ z) : (n : ℤ) ∣ z := by
  rcases eq_or_ne z 0 with hz | hz
  · rw [hz]; exact dvd_zero _
  have hz' : z.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hz
  have hle : ∀ p : ℕ, p.Prime → n.factorization p ≤ z.natAbs.factorization p := by
    intro p hp
    by_cases hpn : p ∣ n
    · have h1 := h p (Nat.mem_primeFactors.mpr ⟨hp, hpn, hn⟩)
      have h2 : p ^ n.factorization p ∣ z.natAbs := by
        have := Int.natAbs_dvd_natAbs.mpr h1
        simpa [Int.natAbs_pow] using this
      exact (hp.pow_dvd_iff_le_factorization hz').mp h2
    · rw [Nat.factorization_eq_zero_of_not_dvd hpn]; exact Nat.zero_le _
  have key : n ∣ z.natAbs := by
    first
    | exact (Nat.factorization_prime_le_iff_dvd hn hz').mp hle
    | exact (Nat.factorization_le_iff_dvd hn hz').mp (Finsupp.le_def.mpr fun p => by
        by_cases hp : p.Prime
        · exact hle p hp
        · simp [Nat.factorization_eq_zero_of_non_prime n hp])
  first
  | exact Int.ofNat_dvd_left.mpr key
  | exact Int.natCast_dvd.mpr key
  | exact Int.natAbs_dvd_natAbs.mp (by simpa using key)

theorem erdos_27285_hyp_cover :
    ∀ n : ℕ, n ≠ 0 → (∀ p k : ℕ, p.Prime → n ≠ p ^ k) →
      ∀ m : ℤ, ∃ y k : ℤ, erdos_27285_Rep n y ∧ y ≤ erdos_27285_X n ∧ m = y + k * (n : ℤ) := by
  intro n hn hnp m
  have H : ∀ p : ℕ, ∃ y : ℤ, p.Prime → (erdos_27285_Rep n y ∧
      y ≤ (∑ d ∈ Finset.Icc 1 (n.factorization p), (n.choose (p ^ d) : ℤ)) * ((p : ℤ) - 1) ∧
      ((n / p ^ (n.factorization p) : ℕ) : ℤ) ∣ y ∧ ((p : ℤ) ^ (n.factorization p)) ∣ y - m) := by
    intro p
    by_cases hp : p.Prime
    · obtain ⟨y, hy⟩ := prime_part n p hp hn (fun k => hnp p k hp) m
      exact ⟨y, fun _ => hy⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose Y hY using H
  have hdvd : (n : ℤ) ∣ (∑ p ∈ n.primeFactors, Y p) - m := by
    apply dvd_of_forall_ppow n hn
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    rw [← Finset.add_sum_erase n.primeFactors Y hp]
    have e : Y p + ∑ q ∈ n.primeFactors.erase p, Y q - m
        = (Y p - m) + ∑ q ∈ n.primeFactors.erase p, Y q := by ring
    rw [e]
    apply dvd_add (hY p hpp).2.2.2
    apply Finset.dvd_sum
    intro q hq
    obtain ⟨hqp, hq'⟩ := Finset.mem_erase.mp hq
    have hqq := Nat.prime_of_mem_primeFactors hq'
    refine dvd_trans ?_ (hY q hqq).2.2.1
    have hqF : q ^ n.factorization q ∣ n := (hqq.pow_dvd_iff_le_factorization hn).mpr le_rfl
    have hpF : p ^ n.factorization p ∣ n := (hpp.pow_dvd_iff_le_factorization hn).mpr le_rfl
    have hcop : Nat.Coprime (p ^ n.factorization p) (q ^ n.factorization q) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes hpp hqq).mpr (Ne.symm hqp))
    have h3 : p ^ n.factorization p ∣ q ^ n.factorization q * (n / q ^ n.factorization q) := by
      rw [Nat.mul_div_cancel' hqF]; exact hpF
    have h4 : p ^ n.factorization p ∣ n / q ^ n.factorization q := by
      first
      | exact hcop.dvd_of_dvd_mul_left h3
      | exact hcop.dvd_of_dvd_mul_right (by rwa [mul_comm] at h3)
    exact_mod_cast h4
  obtain ⟨k, hk⟩ := hdvd
  refine ⟨∑ p ∈ n.primeFactors, Y p, -k, ?_, ?_, ?_⟩
  · exact rep_sum _ _ (fun p hp => (hY p (Nat.prime_of_mem_primeFactors hp)).1)
  · unfold erdos_27285_X
    exact Finset.sum_le_sum (fun p hp => (hY p (Nat.prime_of_mem_primeFactors hp)).2.1)
  · linear_combination (-1 : ℤ) * hk
end erdos_27285_hyp_cover_ns

-- Digit lemma (rigorous sketch in the refutation output): the digit sums
-- sum_{p,d} c_{p,d} C(n,p^d) with 0 ≤ c ≤ p-1 hit every residue mod n. Each such sum is
-- representable and at most X n.
theorem erdos_27285_hyp_cover :
    ∀ n : ℕ, n ≠ 0 → (∀ p k : ℕ, p.Prime → n ≠ p ^ k) →
      ∀ m : ℤ, ∃ y k : ℤ, erdos_27285_Rep n y ∧ y ≤ erdos_27285_X n ∧ m = y + k * (n : ℤ) := by
  exact erdos_27285_hyp_cover_ns.erdos_27285_hyp_cover

-- CONJECTURE (derived). This is the weakest statement the glue uses: the single integer
-- X(n) - n is not a nonnegative combination of C(n,i), 1 <= i < n.
-- It follows from the Apéry-criterion argument: x_r + C(n,i) >= x_{r + C(n,i)} for every
-- digit vector r, so X(n) is the least representable element of its class mod n.
-- It is also equivalent to the former hyp_apery, via the certified rep_add. If some m < X(n)
-- with m ≡ X(n) (mod n) were representable, then m <= X(n) - n, and X(n) - n = m + k*n with
-- k >= 0 would be representable.
-- Checked exactly (Dijkstra over residues) for every non-prime-power n <= 260 and several
-- families up to n ~ 768.
theorem erdos_27285_hyp_top :
    ∀ n : ℕ, n ≠ 0 → (∀ p k : ℕ, p.Prime → n ≠ p ^ k) →
      ¬ erdos_27285_Rep n (erdos_27285_X n - (n : ℤ)) := by
  sorry

theorem erdos_27285 (n : ℕ) (hn : n ≠ 0)
    (hpk : ∀ p k : ℕ, p.Prime → n ≠ p ^ k) :
    IsGreatest
      {m : ℤ | ¬ ∃ c : ℕ → ℕ, m = ∑ i ∈ Finset.Ico 1 n, (c i : ℤ) * (n.choose i : ℤ)}
      ((∑ p ∈ n.primeFactors,
        (∑ d ∈ Finset.Icc 1 (n.factorization p), (n.choose (p ^ d) : ℤ)) * ((p : ℤ) - 1)) - n) := by
  have hn0 : (0 : ℤ) < (n : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have h2 : 2 ≤ n := by
    have h1 := hpk 2 0 Nat.prime_two
    rw [pow_zero] at h1
    omega
  constructor
  · show ¬ erdos_27285_Rep n (erdos_27285_X n - (n : ℤ))
    exact erdos_27285_hyp_top n hn hpk
  · intro m hm
    have hm' : ¬ erdos_27285_Rep n m := hm
    show m ≤ erdos_27285_X n - (n : ℤ)
    by_contra hlt
    push_neg at hlt
    obtain ⟨y, k, hy, hyX, hmk⟩ := erdos_27285_hyp_cover n hn hpk m
    have hk : 0 ≤ k := by
      by_contra hk'
      push_neg at hk'
      have hkn : k * (n : ℤ) ≤ -(n : ℤ) := by nlinarith
      linarith
    apply hm'
    rw [hmk]
    exact erdos_27285_hyp_rep_add n h2 y k hy hk