-- CHECK: Finset.lcm_eq_zero_iff Finset.prod_pos lt_of_mul_lt_mul_right Filter.eventually_atTop Nat.le_of_dvd

def erdos_55963_L (k : ℕ) : ℕ := (Finset.Icc 1 k).lcm id

def erdos_55963_Good (k p A : ℕ) : Prop :=
  p.Prime ∧ k + 1 < 2 * p ∧ p + 1 ≤ k ∧
    (∃ t, 1 ≤ t ∧ t + 1 ≤ p ∧ A = t * (erdos_55963_L k / p)) ∧ p ∣ A + 1

-- PUBLISHED: S. Ramanujan, "A proof of Bertrand's postulate", J. Indian Math. Soc. 11 (1919); pi(x) - pi(x/2) >= 2 for x >= 11 (the second Ramanujan prime is R_2 = 11)
theorem erdos_55963_hyp_ramanujan :
    ∀ x : ℕ, 11 ≤ x → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ x < 2 * p ∧ q ≤ x := by
  sorry

-- Derived: since p^2 > k and 2p > k, v_p(lcm(1..k)) = 1, so L/p is a unit mod p; take t ≡ -(L/p)^{-1} mod p, which is nonzero, so 1 ≤ t ≤ p-1.
namespace erdos_55963_hyp_crt_ns
open Asymptotics Filter Finset

private lemma erdos_55963_coprime (k p : ℕ) (hp : p.Prime) (hk1 : k + 1 < 2 * p)
    (hk2 : p + 1 ≤ k) : Nat.Coprime (erdos_55963_L k / p) p := by
  have hp2 := hp.two_le
  have hpS : ∀ i ∈ (Finset.Icc 1 k).erase p, Nat.Coprime p i := by
    intro i hi
    rw [Finset.mem_erase, Finset.mem_Icc] at hi
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    rintro ⟨j, hj⟩
    rcases j with _ | _ | j
    · simp at hj; omega
    · simp at hj; omega
    · have : p * 2 ≤ i := by rw [hj]; exact Nat.mul_le_mul_left _ (by omega)
      omega
  have hprod : Nat.Coprime p (∏ i ∈ (Finset.Icc 1 k).erase p, i) :=
    Nat.Coprime.prod_right hpS
  have hMdvd : ((Finset.Icc 1 k).erase p).lcm id ∣ ∏ i ∈ (Finset.Icc 1 k).erase p, i :=
    Finset.lcm_dvd (fun i hi => Finset.dvd_prod_of_mem (fun x => x) hi)
  have hpM : Nat.Coprime p (((Finset.Icc 1 k).erase p).lcm id) :=
    Nat.Coprime.coprime_dvd_right hMdvd hprod
  have hpL : p ∣ erdos_55963_L k := by
    unfold erdos_55963_L
    exact Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  have hLM : erdos_55963_L k ∣ p * ((Finset.Icc 1 k).erase p).lcm id := by
    unfold erdos_55963_L
    apply Finset.lcm_dvd
    intro i hi
    by_cases h : i = p
    · subst h; exact dvd_mul_right _ _
    · exact dvd_mul_of_dvd_right (Finset.dvd_lcm (f := id) (Finset.mem_erase.mpr ⟨h, hi⟩)) _
  have hcM : erdos_55963_L k / p ∣ ((Finset.Icc 1 k).erase p).lcm id := by
    have h := hLM
    rw [← Nat.mul_div_cancel' hpL] at h
    exact (Nat.mul_dvd_mul_iff_left hp.pos).mp h
  exact (Nat.Coprime.coprime_dvd_right hcM hpM).symm

theorem erdos_55963_hyp_crt :
    ∀ k p : ℕ, p.Prime → k + 1 < 2 * p → p + 1 ≤ k →
      ∃ t, 1 ≤ t ∧ t + 1 ≤ p ∧ p ∣ t * (erdos_55963_L k / p) + 1 := by
  intro k p hp hk1 hk2
  have hc := erdos_55963_coprime k p hp hk1 hk2
  obtain ⟨u, hult, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hc hp.one_lt
  generalize erdos_55963_L k / p = c at hc hu ⊢
  have hu0 : u ≠ 0 := by
    rintro rfl; rw [mul_zero, Nat.zero_mod] at hu; exact absurd hu (by norm_num)
  refine ⟨p - u, by omega, by omega, ?_⟩
  have h1 : (p - u) * c + u * c = p * c := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hult.le]
  have h2 := Nat.div_add_mod (c * u) p
  rw [hu, mul_comm c u] at h2
  generalize (p - u) * c = X at h1 ⊢
  generalize u * c = Y at h1 h2
  have h3 : p * (Y / p) + (X + 1) = p * c := by omega
  have h4 : p ∣ p * (Y / p) + (X + 1) := by rw [h3]; exact dvd_mul_right _ _
  exact (Nat.dvd_add_right (dvd_mul_right p (Y / p))).mp h4
end erdos_55963_hyp_crt_ns

theorem erdos_55963_hyp_crt :
    ∀ k p : ℕ, p.Prime → k + 1 < 2 * p → p + 1 ≤ k →
      ∃ t, 1 ≤ t ∧ t + 1 ≤ p ∧ p ∣ t * (erdos_55963_L k / p) + 1 := by
  exact erdos_55963_hyp_crt_ns.erdos_55963_hyp_crt



-- Derived (R2, Lemma 1): for primes q ≠ p with q ≤ k, v_q(A) ≥ v_q(L) ≥ v_q(i), so v_q(A+i) ≥ v_q(i) and the q-loss is at least v_q(k!); for q = p, both A+1 and A+1+p lie in the block.
namespace erdos_55963_hyp_right_ns
open Asymptotics Filter Finset

private lemma e55963_prodIcc (n : ℕ) : ∏ x ∈ Finset.Icc 1 n, x = Nat.factorial n := by
  induction n with
  | zero => first | rfl | decide | simp
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ n + 1), ih, Nat.factorial_succ]
    ring

theorem erdos_55963_hyp_right :
    ∀ k p A : ℕ, erdos_55963_Good k p A → k < A →
      (Finset.Icc A (A + k)).lcm id * Nat.factorial k ∣ (∏ i ∈ Finset.Icc A (A + k), i) := by
  intro k p A hG hkA
  obtain ⟨hp, h2p, hpk, ⟨t, ht1, htp, hA⟩, hpA⟩ := hG
  have hp2 := hp.two_le
  have hL : ∀ i ∈ Finset.Icc 1 k, i ∣ erdos_55963_L k := by
    intro i hi
    unfold erdos_55963_L
    exact Finset.dvd_lcm (f := id) hi
  have hnd : ∀ i, 1 ≤ i → i ≤ k → i ≠ p → ¬ p ∣ i := by
    intro i h1 h2 h3 hdiv
    obtain ⟨c, hc⟩ := hdiv
    have hc2 : c = 0 ∨ c = 1 ∨ 2 ≤ c := by omega
    rcases hc2 with rfl | rfl | hc2
    · rw [Nat.mul_zero] at hc; omega
    · rw [Nat.mul_one] at hc; omega
    · have : p * 2 ≤ p * c := Nat.mul_le_mul_left p hc2
      omega
  have hcop : ∀ i, 1 ≤ i → i ≤ k → i ≠ p → Nat.Coprime p i :=
    fun i h1 h2 h3 => (Nat.Prime.coprime_iff_not_dvd hp).2 (hnd i h1 h2 h3)
  have hpL : p ∣ erdos_55963_L k := hL p (by rw [Finset.mem_Icc]; omega)
  have hdA : ∀ i, 1 ≤ i → i ≤ k → i ≠ p → i ∣ A := by
    intro i h1 h2 h3
    have hi : i ∣ erdos_55963_L k := hL i (by rw [Finset.mem_Icc]; omega)
    have hi' : i ∣ p * (erdos_55963_L k / p) := by
      rw [Nat.mul_div_cancel' hpL]; exact hi
    have hi2 : i ∣ erdos_55963_L k / p := by
      first
        | exact Nat.Coprime.dvd_of_dvd_mul_left (hcop i h1 h2 h3).symm hi'
        | exact Nat.Coprime.dvd_of_dvd_mul_right (hcop i h1 h2 h3).symm (by rwa [mul_comm] at hi')
    rw [hA]
    exact Dvd.dvd.mul_left hi2 t
  have key : ∀ a ∈ Finset.Icc A (A + k),
      Nat.factorial k ∣ ∏ x ∈ (Finset.Icc A (A + k)).erase a, x := by
    intro a ha
    rw [Finset.mem_Icc] at ha
    have hmemT : ∀ i ∈ (Finset.Icc 1 k).erase p, 1 ≤ i ∧ i ≤ k ∧ i ≠ p := by
      intro i hi
      rw [Finset.mem_erase, Finset.mem_Icc] at hi
      omega
    have hpT : p ∈ Finset.Icc 1 k := by rw [Finset.mem_Icc]; omega
    have hfac0 : p * ∏ i ∈ (Finset.Icc 1 k).erase p, i = ∏ i ∈ Finset.Icc 1 k, i :=
      Finset.mul_prod_erase (Finset.Icc 1 k) (fun i => i) hpT
    have hfac : Nat.factorial k = p * ∏ i ∈ (Finset.Icc 1 k).erase p, i := by
      rw [hfac0, e55963_prodIcc]
    have hcopT : Nat.Coprime p (∏ i ∈ (Finset.Icc 1 k).erase p, i) := by
      apply Nat.Coprime.prod_right
      intro i hi
      obtain ⟨h1, h2, h3⟩ := hmemT i hi
      exact hcop i h1 h2 h3
    have hpE : p ∣ ∏ x ∈ (Finset.Icc A (A + k)).erase a, x := by
      by_cases ha1 : a = A + 1
      · have hmem : A + 1 + p ∈ (Finset.Icc A (A + k)).erase a := by
          rw [Finset.mem_erase, Finset.mem_Icc]; omega
        exact dvd_trans (Nat.dvd_add hpA (dvd_refl p)) (Finset.dvd_prod_of_mem (fun x => x) hmem)
      · have hmem : A + 1 ∈ (Finset.Icc A (A + k)).erase a := by
          rw [Finset.mem_erase, Finset.mem_Icc]; omega
        exact dvd_trans hpA (Finset.dvd_prod_of_mem (fun x => x) hmem)
    have hTE : ∏ i ∈ (Finset.Icc 1 k).erase p, i ∣ ∏ x ∈ (Finset.Icc A (A + k)).erase a, x := by
      have h1 : ∏ i ∈ (Finset.Icc 1 k).erase p, i ∣
          ∏ i ∈ (Finset.Icc 1 k).erase p, (if A + i = a then A else A + i) := by
        apply Finset.prod_dvd_prod_of_dvd
        intro i hi
        obtain ⟨h1, h2, h3⟩ := hmemT i hi
        split_ifs with h
        · exact hdA i h1 h2 h3
        · exact Nat.dvd_add (hdA i h1 h2 h3) (dvd_refl i)
      have hinj : ∀ x ∈ (Finset.Icc 1 k).erase p, ∀ y ∈ (Finset.Icc 1 k).erase p,
          (if A + x = a then A else A + x) = (if A + y = a then A else A + y) → x = y := by
        intro x hx y hy hxy
        obtain ⟨hx1, _, _⟩ := hmemT x hx
        obtain ⟨hy1, _, _⟩ := hmemT y hy
        split_ifs at hxy <;> omega
      have h2 : ∏ x ∈ ((Finset.Icc 1 k).erase p).image (fun i => if A + i = a then A else A + i), x
          = ∏ i ∈ (Finset.Icc 1 k).erase p, (if A + i = a then A else A + i) := by
        first
          | exact Finset.prod_image hinj
          | rw [Finset.prod_image hinj]
          | exact Finset.prod_image (fun x hx y hy h => hinj x hx y hy h)
      have h3 : ((Finset.Icc 1 k).erase p).image (fun i => if A + i = a then A else A + i)
          ⊆ (Finset.Icc A (A + k)).erase a := by
        intro x hx
        rw [Finset.mem_image] at hx
        obtain ⟨i, hi, rfl⟩ := hx
        obtain ⟨h1, h2, h3⟩ := hmemT i hi
        rw [Finset.mem_erase, Finset.mem_Icc]
        split_ifs with h <;> omega
      rw [← h2] at h1
      exact dvd_trans h1 (Finset.prod_dvd_prod_of_subset _ _ _ h3)
    rw [hfac]
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcopT hpE hTE
  have hfd : Nat.factorial k ∣ ∏ i ∈ Finset.Icc A (A + k), i := by
    have hmem : A ∈ Finset.Icc A (A + k) := by rw [Finset.mem_Icc]; omega
    exact dvd_trans (key A hmem) (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.erase_subset _ _))
  obtain ⟨R, hR⟩ := hfd
  rw [hR, mul_comm (Nat.factorial k) R]
  refine mul_dvd_mul_right ?_ _
  rw [Finset.lcm_dvd_iff]
  intro a ha
  have hP : a * ∏ x ∈ (Finset.Icc A (A + k)).erase a, x = ∏ x ∈ Finset.Icc A (A + k), x :=
    Finset.mul_prod_erase _ (fun x => x) ha
  have h1 : a * Nat.factorial k ∣ R * Nat.factorial k := by
    rw [mul_comm R, ← hR, ← hP]
    exact mul_dvd_mul_left a (key a ha)
  first
    | exact Nat.dvd_of_mul_dvd_mul_right (Nat.factorial_pos k) h1
    | exact (Nat.mul_dvd_mul_iff_right (Nat.factorial_pos k)).1 h1
end erdos_55963_hyp_right_ns

theorem erdos_55963_hyp_right :
    ∀ k p A : ℕ, erdos_55963_Good k p A → k < A →
      (Finset.Icc A (A + k)).lcm id * Nat.factorial k ∣ (∏ i ∈ Finset.Icc A (A + k), i) := by
  exact erdos_55963_hyp_right_ns.erdos_55963_hyp_right



-- Derived (R2, Lemma 2): for q ≠ p, q ≤ k, the multiplicity counts are floor(k/q^j) for j ≤ e_q and at most 1 above, so the q-loss is at most v_q(k!) - e_q; for q = p, A-(p-1) is the only multiple of p (2p-1 > k) and p^2 > k; primes q > k contribute no loss.
namespace erdos_55963_hyp_left_ns
-- CHECK: Nat.factorization_lcm Nat.Prime.pow_dvd_iff_le_factorization Nat.factorization_prime_le_iff_dvd Finset.sum_nbij' Finset.sum_Icc_succ_top Finset.exists_mem_eq_sup
private lemma my_dvd_sub {a m n : ℕ} (h1 : a ∣ m) (h2 : a ∣ n) : a ∣ m - n := by
  first
  | exact Nat.dvd_sub' h1 h2
  | exact Nat.dvd_sub h1 h2
  | exact dvd_sub' h1 h2

private lemma lcm_fact_le (q c : ℕ) (s : Finset ℕ) :
    (∀ x ∈ s, x ≠ 0) → (∀ x ∈ s, x.factorization q ≤ c) → (s.lcm id).factorization q ≤ c := by
  refine Finset.induction_on s ?_ ?_
  · intro _ _
    simp
  · intro a s ha ih h0 hc
    rw [Finset.lcm_insert]
    have hs0 : s.lcm id ≠ 0 := by
      intro h
      rw [Finset.lcm_eq_zero_iff] at h
      obtain ⟨x, hx, hx0⟩ := h
      exact h0 x (Finset.mem_insert_of_mem (Finset.mem_coe.mp hx)) hx0
    have ha0 : a ≠ 0 := h0 a (Finset.mem_insert_self a s)
    show (Nat.lcm a (s.lcm id)).factorization q ≤ c
    rw [Nat.factorization_lcm ha0 hs0, Finsupp.sup_apply]
    exact _root_.sup_le (hc a (Finset.mem_insert_self a s))
      (ih (fun x hx => h0 x (Finset.mem_insert_of_mem hx))
        (fun x hx => hc x (Finset.mem_insert_of_mem hx)))

private lemma fact_factorial (q : ℕ) : ∀ k : ℕ,
    (Nat.factorial k).factorization q = ∑ i ∈ Finset.Icc 1 k, i.factorization q
  | 0 => by
    rw [Finset.Icc_eq_empty (by norm_num)]
    simp
  | k + 1 => by
    rw [Nat.factorial_succ, Nat.factorization_mul (by omega : k + 1 ≠ 0) (Nat.factorial_ne_zero k),
      Finsupp.add_apply, Finset.sum_Icc_succ_top (show 1 ≤ k + 1 by omega), fact_factorial q k]
    ring

private lemma key_q (k p A q : ℕ) (hp : p.Prime) (h2p : k + 1 < 2 * p) (hpk : p + 1 ≤ k)
    (hAL : ∀ r : ℕ, r.Coprime p → r ∣ erdos_55963_L k → r ∣ A)
    (hpA : p ∣ A + 1) (hkA : k < A) (hq : q.Prime) :
    (erdos_55963_L k).factorization q + ∑ b ∈ Finset.Icc (A - k) (A - 1), b.factorization q ≤
      ((Finset.Icc (A - k) (A - 1)).lcm id).factorization q +
        ∑ i ∈ Finset.Icc 1 k, i.factorization q := by
  have hp2 := hp.two_le
  have hLlcm : erdos_55963_L k = (Finset.Icc 1 k).lcm id := rfl
  have hI0 : ∀ i ∈ Finset.Icc 1 k, i ≠ 0 := by
    intro i hi; rw [Finset.mem_Icc] at hi; omega
  have hB0 : ∀ b ∈ Finset.Icc (A - k) (A - 1), b ≠ 0 := by
    intro b hb; rw [Finset.mem_Icc] at hb; omega
  have hL0 : erdos_55963_L k ≠ 0 := by
    rw [hLlcm]; intro h
    rw [Finset.lcm_eq_zero_iff] at h
    obtain ⟨x, hx, hx0⟩ := h
    exact hI0 x (Finset.mem_coe.mp hx) hx0
  have hM0 : (Finset.Icc (A - k) (A - 1)).lcm id ≠ 0 := by
    intro h
    rw [Finset.lcm_eq_zero_iff] at h
    obtain ⟨x, hx, hx0⟩ := h
    exact hB0 x (Finset.mem_coe.mp hx) hx0
  have hvle : ∀ x y : ℕ, x ≠ 0 → y ≠ 0 → x ∣ y → x.factorization q ≤ y.factorization q := by
    intro x y hx hy hxy
    exact (hq.pow_dvd_iff_le_factorization hy).mp
      (dvd_trans ((hq.pow_dvd_iff_le_factorization hx).mpr le_rfl) hxy)
  have hie : ∀ i ∈ Finset.Icc 1 k, i.factorization q ≤ (erdos_55963_L k).factorization q := by
    intro i hi
    apply hvle i _ (hI0 i hi) hL0
    rw [hLlcm]
    exact Finset.dvd_lcm (f := id) hi
  obtain ⟨i0, hi0, hi0e⟩ : ∃ i0 ∈ Finset.Icc 1 k,
      (erdos_55963_L k).factorization q ≤ i0.factorization q := by
    have hne : (Finset.Icc 1 k).Nonempty := ⟨1, by rw [Finset.mem_Icc]; omega⟩
    obtain ⟨j, hj, heq⟩ :=
      Finset.exists_mem_eq_sup (Finset.Icc 1 k) hne (fun x => x.factorization q)
    have h1 : (erdos_55963_L k).factorization q ≤
        (Finset.Icc 1 k).sup (fun x => x.factorization q) := by
      rw [hLlcm]
      exact lcm_fact_le q _ _ hI0 (fun x hx => Finset.le_sup (f := fun x => x.factorization q) hx)
    exact ⟨j, hj, h1.trans (le_of_eq heq)⟩
  have hi0' := hi0
  rw [Finset.mem_Icc] at hi0'
  have hqk : k < q ^ ((erdos_55963_L k).factorization q + 1) := by
    by_contra hcon
    push_neg at hcon
    have hpos : 0 < q ^ ((erdos_55963_L k).factorization q + 1) := pow_pos hq.pos _
    have hmem : q ^ ((erdos_55963_L k).factorization q + 1) ∈ Finset.Icc 1 k := by
      rw [Finset.mem_Icc]; omega
    have h1 := hie _ hmem
    have h2 : (erdos_55963_L k).factorization q + 1 ≤
        (q ^ ((erdos_55963_L k).factorization q + 1)).factorization q :=
      (hq.pow_dvd_iff_le_factorization (by omega)).mp dvd_rfl
    omega
  rcases eq_or_ne q p with hqp | hqp
  · rw [hqp] at hvle hi0e ⊢
    have he1 : (erdos_55963_L k).factorization p ≤ 1 := by
      by_contra hcon
      push_neg at hcon
      have h1 : p ^ 2 ∣ i0 := (hp.pow_dvd_iff_le_factorization (by omega)).mpr (by omega)
      have h2 : p ^ 2 ≤ i0 := Nat.le_of_dvd (by omega) h1
      have h3 : 2 * p ≤ p ^ 2 := by rw [pow_two]; nlinarith [Nat.zero_le p]
      omega
    have hpmem : p ∈ Finset.Icc 1 k := by rw [Finset.mem_Icc]; omega
    have hpp : 1 ≤ p.factorization p :=
      (hp.pow_dvd_iff_le_factorization hp.ne_zero).mp (by simp)
    have hsum1 : p.factorization p ≤ ∑ i ∈ Finset.Icc 1 k, i.factorization p :=
      Finset.single_le_sum (f := fun i => i.factorization p) (fun i _ => Nat.zero_le _) hpmem
    have hb0mem : A - (p - 1) ∈ Finset.Icc (A - k) (A - 1) := by
      rw [Finset.mem_Icc]; omega
    have hzero : ∀ b ∈ Finset.Icc (A - k) (A - 1), b ≠ A - (p - 1) → b.factorization p = 0 := by
      intro b hb hne
      rw [Finset.mem_Icc] at hb
      by_contra hcon
      have h1 : p ^ 1 ∣ b := (hp.pow_dvd_iff_le_factorization (by omega)).mpr (by omega)
      rw [pow_one] at h1
      have h2 : p ∣ (A + 1) - b := my_dvd_sub hpA h1
      obtain ⟨c, hc⟩ := h2
      rcases Nat.lt_or_ge c 2 with hc2 | hc2
      · interval_cases c <;> omega
      · have : 2 * p ≤ p * c := by nlinarith [Nat.zero_le p]
        omega
    have hsumB : ∑ b ∈ Finset.Icc (A - k) (A - 1), b.factorization p =
        (A - (p - 1)).factorization p :=
      Finset.sum_eq_single (A - (p - 1)) hzero (fun h => absurd hb0mem h)
    have hM := hvle (A - (p - 1)) _ (by omega) hM0 (Finset.dvd_lcm (f := id) hb0mem)
    omega
  · have hqeL : q ^ (erdos_55963_L k).factorization q ∣ erdos_55963_L k :=
      (hq.pow_dvd_iff_le_factorization hL0).mpr le_rfl
    have hqeA : q ^ (erdos_55963_L k).factorization q ∣ A :=
      hAL _ (Nat.Coprime.pow_left _ ((Nat.coprime_primes hq hp).mpr hqp)) hqeL
    have hre : ∑ i ∈ Finset.Icc 1 k, i.factorization q =
        ∑ b ∈ Finset.Icc (A - k) (A - 1), (A - b).factorization q := by
      apply Finset.sum_nbij' (fun i => A - i) (fun b => A - b)
      · intro i hi
        simp only [Finset.mem_coe, Finset.mem_Icc] at hi ⊢
        omega
      · intro b hb
        simp only [Finset.mem_coe, Finset.mem_Icc] at hb ⊢
        omega
      · intro i hi
        simp only [Finset.mem_coe, Finset.mem_Icc] at hi ⊢
        omega
      · intro b hb
        simp only [Finset.mem_coe, Finset.mem_Icc] at hb ⊢
        omega
      · intro i hi
        simp only [Finset.mem_coe, Finset.mem_Icc] at hi
        have h : A - (A - i) = i := by omega
        show i.factorization q = (A - (A - i)).factorization q
        rw [h]
    rw [hre]
    obtain ⟨e, he⟩ : ∃ e, e = (erdos_55963_L k).factorization q := ⟨_, rfl⟩
    rw [← he] at hie hi0e hqk hqeA ⊢
    set B := Finset.Icc (A - k) (A - 1) with hB
    have hF4 : ∀ b ∈ B, (A - b).factorization q < b.factorization q →
        q ^ (e + 1) ∣ b ∧ (A - b).factorization q = e := by
      intro b hb hlt
      have hb' := hb
      rw [hB, Finset.mem_Icc] at hb'
      have hiI : A - b ∈ Finset.Icc 1 k := by rw [Finset.mem_Icc]; omega
      have hle := hie (A - b) hiI
      have hAb0 : A - b ≠ 0 := by omega
      have hb0 : b ≠ 0 := by omega
      have heq : (A - b).factorization q = e := by
        by_contra hne
        have hlt' : (A - b).factorization q + 1 ≤ e := by omega
        have h1 : q ^ ((A - b).factorization q + 1) ∣ A := dvd_trans (pow_dvd_pow q hlt') hqeA
        have h2 : q ^ ((A - b).factorization q + 1) ∣ b :=
          (hq.pow_dvd_iff_le_factorization hb0).mpr (by omega)
        have h3 : q ^ ((A - b).factorization q + 1) ∣ A - b := my_dvd_sub h1 h2
        have h4 := (hq.pow_dvd_iff_le_factorization hAb0).mp h3
        omega
      exact ⟨(hq.pow_dvd_iff_le_factorization hb0).mpr (by omega), heq⟩
    have hF5 : ∀ b1 ∈ B, ∀ b2 ∈ B, q ^ (e + 1) ∣ b1 → q ^ (e + 1) ∣ b2 → b1 = b2 := by
      intro b1 hb1 b2 hb2 h1 h2
      rw [hB, Finset.mem_Icc] at hb1 hb2
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · have h3 : q ^ (e + 1) ∣ b2 - b1 := my_dvd_sub h2 h1
        have h4 := Nat.le_of_dvd (by omega) h3
        omega
      · have h3 : q ^ (e + 1) ∣ b1 - b2 := my_dvd_sub h1 h2
        have h4 := Nat.le_of_dvd (by omega) h3
        omega
    obtain ⟨bs, hbs, hbse, hothers⟩ : ∃ bs ∈ B, e ≤ (A - bs).factorization q ∧
        ∀ b ∈ B, b ≠ bs → b.factorization q ≤ (A - b).factorization q := by
      by_cases hex : ∃ b ∈ B, (A - b).factorization q < b.factorization q
      · obtain ⟨b1, hb1, hlt1⟩ := hex
        obtain ⟨hd1, heq1⟩ := hF4 b1 hb1 hlt1
        refine ⟨b1, hb1, heq1.ge, ?_⟩
        intro b hb hne
        by_contra hcon
        push_neg at hcon
        obtain ⟨hd, _⟩ := hF4 b hb hcon
        exact hne (hF5 b hb b1 hb1 hd hd1)
      · push_neg at hex
        refine ⟨A - i0, ?_, ?_, fun b hb _ => hex b hb⟩
        · rw [hB, Finset.mem_Icc]; omega
        · rw [show A - (A - i0) = i0 by omega]
          exact hi0e
    have e1 : bs.factorization q + ∑ x ∈ B.erase bs, x.factorization q =
        ∑ x ∈ B, x.factorization q :=
      Finset.add_sum_erase B (fun x : ℕ => x.factorization q) hbs
    have e2 : (A - bs).factorization q + ∑ x ∈ B.erase bs, (A - x).factorization q =
        ∑ x ∈ B, (A - x).factorization q :=
      Finset.add_sum_erase B (fun x : ℕ => (A - x).factorization q) hbs
    have hs : ∑ x ∈ B.erase bs, x.factorization q ≤ ∑ x ∈ B.erase bs, (A - x).factorization q :=
      Finset.sum_le_sum (fun b hb =>
        hothers b (Finset.mem_of_mem_erase hb) (Finset.ne_of_mem_erase hb))
    have hM := hvle bs (B.lcm id) (hB0 bs hbs) hM0 (Finset.dvd_lcm (f := id) hbs)
    omega

open Asymptotics Filter Finset

theorem erdos_55963_hyp_left :
    ∀ k p A : ℕ, erdos_55963_Good k p A → k < A →
      erdos_55963_L k * (∏ i ∈ Finset.Icc (A - k) (A - 1), i) ∣
        (Finset.Icc (A - k) (A - 1)).lcm id * Nat.factorial k := by
  intro k p A hG hkA
  obtain ⟨hp, h2p, hpk, ⟨t, ht1, htp, hA⟩, hpA⟩ := hG
  have hp2 := hp.two_le
  have hpL : p ∣ erdos_55963_L k := by
    unfold erdos_55963_L
    exact Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  have hAL : ∀ r : ℕ, r.Coprime p → r ∣ erdos_55963_L k → r ∣ A := by
    intro r hr hrL
    have hLeq : p * (erdos_55963_L k / p) = erdos_55963_L k := Nat.mul_div_cancel' hpL
    have h1 : r ∣ p * (erdos_55963_L k / p) := by rw [hLeq]; exact hrL
    have h1' : r ∣ (erdos_55963_L k / p) * p := by rw [mul_comm]; exact h1
    have h2 : r ∣ erdos_55963_L k / p := by
      first
      | exact hr.dvd_of_dvd_mul_left h1
      | exact hr.dvd_of_dvd_mul_right h1'
      | exact hr.dvd_of_dvd_mul_left h1'
      | exact hr.dvd_of_dvd_mul_right h1
    rw [hA]
    exact Dvd.dvd.mul_left h2 t
  have hB0 : ∀ b ∈ Finset.Icc (A - k) (A - 1), b ≠ 0 := by
    intro b hb; rw [Finset.mem_Icc] at hb; omega
  have hI0 : ∀ i ∈ Finset.Icc 1 k, i ≠ 0 := by
    intro i hi; rw [Finset.mem_Icc] at hi; omega
  have hL0 : erdos_55963_L k ≠ 0 := by
    unfold erdos_55963_L
    intro h
    rw [Finset.lcm_eq_zero_iff] at h
    obtain ⟨x, hx, hx0⟩ := h
    exact hI0 x (Finset.mem_coe.mp hx) hx0
  have hM0 : (Finset.Icc (A - k) (A - 1)).lcm id ≠ 0 := by
    intro h
    rw [Finset.lcm_eq_zero_iff] at h
    obtain ⟨x, hx, hx0⟩ := h
    exact hB0 x (Finset.mem_coe.mp hx) hx0
  have hP0 : (∏ i ∈ Finset.Icc (A - k) (A - 1), i) ≠ 0 := Finset.prod_ne_zero_iff.mpr hB0
  have hX : erdos_55963_L k * (∏ i ∈ Finset.Icc (A - k) (A - 1), i) ≠ 0 := mul_ne_zero hL0 hP0
  have hY : (Finset.Icc (A - k) (A - 1)).lcm id * Nat.factorial k ≠ 0 :=
    mul_ne_zero hM0 (Nat.factorial_ne_zero k)
  have key : ∀ q : ℕ, q.Prime →
      (erdos_55963_L k * (∏ i ∈ Finset.Icc (A - k) (A - 1), i)).factorization q ≤
        ((Finset.Icc (A - k) (A - 1)).lcm id * Nat.factorial k).factorization q := by
    intro q hq
    rw [Nat.factorization_mul hL0 hP0, Nat.factorization_mul hM0 (Nat.factorial_ne_zero k),
      Finsupp.add_apply, Finsupp.add_apply, Nat.factorization_prod hB0,
      Finsupp.finset_sum_apply, fact_factorial]
    exact key_q k p A q hp h2p hpk hAL hpA hkA hq
  first
  | exact (Nat.factorization_prime_le_iff_dvd hX hY).mp key
  | exact (Nat.factorization_le_iff_dvd hX hY).mp (fun q => by
      by_cases hq : q.Prime
      · exact key q hq
      · simp [Nat.factorization_eq_zero_of_non_prime _ hq])
end erdos_55963_hyp_left_ns

theorem erdos_55963_hyp_left :
    ∀ k p A : ℕ, erdos_55963_Good k p A → k < A →
      erdos_55963_L k * (∏ i ∈ Finset.Icc (A - k) (A - 1), i) ∣
        (Finset.Icc (A - k) (A - 1)).lcm id * Nat.factorial k := by
  exact erdos_55963_hyp_left_ns.erdos_55963_hyp_left



-- Derived: A ≥ L/p > L/k ≥ 2^k/k (Nair: L ≥ 2^k for k ≥ 7), so A - k ≥ 4k^3 for k ≥ 25. Then L/A = p/t ≥ p/(p-1) > 1 + 1/k ≥ 1 + 4k^2/(A-k) ≥ prod (A+i)/(A-i).
namespace erdos_55963_hyp_final_ns
open Asymptotics Filter Finset

private lemma e55963_L_ne_zero (k : ℕ) : erdos_55963_L k ≠ 0 := by
  unfold erdos_55963_L
  intro h
  rw [Finset.lcm_eq_zero_iff] at h
  obtain ⟨x, hx, hx0⟩ := h
  simp at hx hx0 <;> omega

private lemma e55963_choose_dvd (n j k : ℕ) (hj : j ≤ n) (hn : 0 < n) (hnk : n ≤ k) :
    n.choose j ∣ erdos_55963_L k := by
  have hC : n.choose j ≠ 0 := (Nat.choose_pos hj).ne'
  have hL : erdos_55963_L k ≠ 0 := e55963_L_ne_zero k
  refine (Nat.factorization_prime_le_iff_dvd hC hL).mp ?_
  intro q hq
  have h1 : (n.choose j).factorization q ≤ Nat.log q n := Nat.factorization_choose_le_log
  have hmem : q ^ Nat.log q n ∈ Finset.Icc 1 k := by
    rw [Finset.mem_Icc]
    exact ⟨Nat.one_le_pow _ _ hq.pos, (Nat.pow_log_le_self q hn.ne').trans hnk⟩
  have h2 : q ^ Nat.log q n ∣ erdos_55963_L k := by
    unfold erdos_55963_L
    exact Finset.dvd_lcm (f := id) hmem
  have h3 : Nat.log q n ≤ (erdos_55963_L k).factorization q :=
    (hq.pow_dvd_iff_le_factorization hL).mp h2
  omega

private lemma e55963_pow (m : ℕ) (hm : 12 ≤ m) : 3 * m * (2 * m + 1) ^ 4 ≤ 4 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have key : 3 * (n + 1) * (2 * (n + 1) + 1) ^ 4 ≤ 4 * (3 * n * (2 * n + 1) ^ 4) := by
      obtain ⟨j, rfl⟩ : ∃ j, n = j + 12 := ⟨n - 12, by omega⟩
      nlinarith [Nat.zero_le (j^5), Nat.zero_le (j^4), Nat.zero_le (j^3),
        Nat.zero_le (j^2), Nat.zero_le j]
    calc 3 * (n + 1) * (2 * (n + 1) + 1) ^ 4 ≤ 4 * (3 * n * (2 * n + 1) ^ 4) := key
      _ ≤ 4 * 4 ^ n := Nat.mul_le_mul le_rfl ih
      _ = 4 ^ (n + 1) := by ring

private lemma e55963_bern (B c : ℕ) : ∀ n : ℕ, (B + c) ^ n * B ≤ B ^ (n + 1) + n * c * (B + c) ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : B ^ (n + 1) ≤ (B + c) ^ (n + 1) := Nat.pow_le_pow_left (Nat.le_add_right B c) _
    calc (B + c) ^ (n + 1) * B = (B + c) * ((B + c) ^ n * B) := by ring
      _ ≤ (B + c) * (B ^ (n + 1) + n * c * (B + c) ^ n) := Nat.mul_le_mul le_rfl ih
      _ = B ^ (n + 1 + 1) + c * B ^ (n + 1) + n * c * (B + c) ^ (n + 1) := by ring
      _ ≤ B ^ (n + 1 + 1) + c * (B + c) ^ (n + 1) + n * c * (B + c) ^ (n + 1) :=
          Nat.add_le_add (Nat.add_le_add le_rfl (Nat.mul_le_mul le_rfl h1)) le_rfl
      _ = B ^ (n + 1 + 1) + (n + 1) * c * (B + c) ^ (n + 1) := by ring

theorem erdos_55963_hyp_final :
    ∀ k p A : ℕ, erdos_55963_Good k p A → 25 ≤ k →
      k < A ∧ (∏ i ∈ Finset.Icc A (A + k), i) <
        erdos_55963_L k * (∏ i ∈ Finset.Icc (A - k) (A - 1), i) := by
  intro k p A hG hk
  obtain ⟨hp, h2p, hpk, ⟨t, ht1, htp, hA⟩, _hdiv⟩ := hG
  have hLne : erdos_55963_L k ≠ 0 := e55963_L_ne_zero k
  have hLpos : 0 < erdos_55963_L k := Nat.pos_of_ne_zero hLne
  have hpL : p ∣ erdos_55963_L k := by
    have hmem : p ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨hp.one_lt.le, by omega⟩
    unfold erdos_55963_L
    exact Finset.dvd_lcm (f := id) hmem
  obtain ⟨D, hD⟩ := hpL
  rw [hD, Nat.mul_div_cancel_left D hp.pos] at hA
  have hDbig : 3 * k ^ 3 < D := by
    obtain ⟨m, hm⟩ : ∃ m, m = k / 2 := ⟨_, rfl⟩
    have hCd : (2 * m).choose m ∣ erdos_55963_L k :=
      e55963_choose_dvd (2 * m) m k (by omega) (by omega) (by omega)
    have hCle : (2 * m).choose m ≤ p * D := by
      have := Nat.le_of_dvd hLpos hCd
      rw [hD] at this
      exact this
    have h4 := Nat.four_pow_lt_mul_centralBinom m (by omega)
    rw [Nat.centralBinom_eq_two_mul_choose] at h4
    have hpow := e55963_pow m (by omega)
    have hk4 : k ^ 4 ≤ (2 * m + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
    have h5 : m * (3 * k ^ 4) < m * (2 * m).choose m := by
      calc m * (3 * k ^ 4) ≤ m * (3 * (2 * m + 1) ^ 4) :=
            Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hk4)
        _ = 3 * m * (2 * m + 1) ^ 4 := by ring
        _ ≤ 4 ^ m := hpow
        _ < m * (2 * m).choose m := h4
    have h6 : 3 * k ^ 4 < (2 * m).choose m := lt_of_mul_lt_mul_left h5 (Nat.zero_le _)
    have h7 : p * (3 * k ^ 3) < p * D := by
      calc p * (3 * k ^ 3) ≤ k * (3 * k ^ 3) := Nat.mul_le_mul (by omega) le_rfl
        _ = 3 * k ^ 4 := by ring
        _ < (2 * m).choose m := h6
        _ ≤ p * D := hCle
    exact lt_of_mul_lt_mul_left h7 (Nat.zero_le _)
  have hAD : D ≤ A := by
    rw [hA]
    calc D = 1 * D := (one_mul D).symm
      _ ≤ t * D := Nat.mul_le_mul ht1 le_rfl
  have hkk : 25 * k ^ 2 ≤ k ^ 3 := by
    calc 25 * k ^ 2 ≤ k * k ^ 2 := Nat.mul_le_mul hk le_rfl
      _ = k ^ 3 := by ring
  have hkk2 : 25 * k ≤ k ^ 2 := by
    calc 25 * k ≤ k * k := Nat.mul_le_mul hk le_rfl
      _ = k ^ 2 := by ring
  have hA_big : 2 * k ^ 3 + 2 * k ^ 2 + k + 1 < A := by linarith
  have hkA : k < A := by linarith
  refine ⟨hkA, ?_⟩
  obtain ⟨B, hB⟩ : ∃ B, A = B + k := ⟨A - k, by omega⟩
  obtain ⟨E, hE⟩ : ∃ E, E = (k + 1) * (2 * k) := ⟨_, rfl⟩
  have hkE : k * E = 2 * k ^ 3 + 2 * k ^ 2 := by rw [hE]; ring
  have hpkE : p * E ≤ k * E := Nat.mul_le_mul (by omega) le_rfl
  have hpE : p * E < B := by linarith
  have hEB : E ≤ B := by
    have : E ≤ p * E := by
      calc E = 1 * E := (one_mul E).symm
        _ ≤ p * E := Nat.mul_le_mul hp.one_lt.le le_rfl
    omega
  obtain ⟨F, hF⟩ : ∃ F, B = E + F := ⟨B - E, by omega⟩
  have hBpos : 0 < B := lt_of_le_of_lt (Nat.zero_le _) hpE
  obtain ⟨X, hX⟩ : ∃ X, X = (B + 2 * k) ^ (k + 1) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = B ^ k := ⟨_, rfl⟩
  have hYpos : 0 < Y := by rw [hY]; exact pow_pos hBpos _
  have hb' : X * B ≤ B * B * Y + E * X := by
    have := e55963_bern B (2 * k) (k + 1)
    rw [hX, hY, hE]
    calc (B + 2 * k) ^ (k + 1) * B
        ≤ B ^ (k + 1 + 1) + (k + 1) * (2 * k) * (B + 2 * k) ^ (k + 1) := this
      _ = B * B * B ^ k + (k + 1) * (2 * k) * (B + 2 * k) ^ (k + 1) := by ring
  have hXB : X * B = X * E + X * F := by rw [hF]; ring
  have hXF : X * F ≤ B * B * Y := by linarith
  have a1 : (t + 1) * E ≤ p * E := Nat.mul_le_mul htp le_rfl
  have a2 : (t + 1) * F ≤ p * F := Nat.mul_le_mul htp le_rfl
  have hpE' : p * E < E + F := by rw [← hF]; exact hpE
  have h1 : t * (E + F) < p * F := by nlinarith
  have hBA : B ≤ A := by omega
  have hkey : t * (B * B) < p * A * F := by
    calc t * (B * B) = t * (E + F) * B := by rw [← hF]; ring
      _ < p * F * B := mul_lt_mul_of_pos_right h1 hBpos
      _ ≤ p * F * A := Nat.mul_le_mul le_rfl hBA
      _ = p * A * F := by ring
  have hcore : t * X < p * A * Y := by
    have : t * X * F < p * A * Y * F := by
      calc t * X * F = t * (X * F) := by ring
        _ ≤ t * (B * B * Y) := Nat.mul_le_mul le_rfl hXF
        _ = t * (B * B) * Y := by ring
        _ < p * A * F * Y := mul_lt_mul_of_pos_right hkey hYpos
        _ = p * A * Y * F := by ring
    exact lt_of_mul_lt_mul_right this (Nat.zero_le _)
  have hP1 : (∏ i ∈ Finset.Icc A (A + k), i) ≤ X := by
    calc (∏ i ∈ Finset.Icc A (A + k), i) ≤ ∏ i ∈ Finset.Icc A (A + k), (A + k) :=
          Finset.prod_le_prod (fun i _ => Nat.zero_le i) (fun i hi => (Finset.mem_Icc.mp hi).2)
      _ = (A + k) ^ (k + 1) := by
          rw [Finset.prod_const, Nat.card_Icc]
          congr 1
          omega
      _ = X := by
          rw [hX]
          congr 1
          omega
  have hP2 : Y ≤ ∏ i ∈ Finset.Icc (A - k) (A - 1), i := by
    calc Y = B ^ k := hY
      _ = ∏ i ∈ Finset.Icc (A - k) (A - 1), B := by
          rw [Finset.prod_const, Nat.card_Icc]
          congr 1
          omega
      _ ≤ ∏ i ∈ Finset.Icc (A - k) (A - 1), i :=
          Finset.prod_le_prod (fun i _ => Nat.zero_le _)
            (fun i hi => by rw [Finset.mem_Icc] at hi; omega)
  rw [hD]
  have hLt : p * D * t = p * A := by rw [hA]; ring
  have hfin : t * (∏ i ∈ Finset.Icc A (A + k), i) <
      t * (p * D * ∏ i ∈ Finset.Icc (A - k) (A - 1), i) := by
    calc t * (∏ i ∈ Finset.Icc A (A + k), i) ≤ t * X := Nat.mul_le_mul le_rfl hP1
      _ < p * A * Y := hcore
      _ = p * D * t * Y := by rw [hLt]
      _ ≤ p * D * t * ∏ i ∈ Finset.Icc (A - k) (A - 1), i := Nat.mul_le_mul le_rfl hP2
      _ = t * (p * D * ∏ i ∈ Finset.Icc (A - k) (A - 1), i) := by ring
  exact lt_of_mul_lt_mul_left hfin (Nat.zero_le _)
end erdos_55963_hyp_final_ns

theorem erdos_55963_hyp_final :
    ∀ k p A : ℕ, erdos_55963_Good k p A → 25 ≤ k →
      k < A ∧ (∏ i ∈ Finset.Icc A (A + k), i) <
        erdos_55963_L k * (∏ i ∈ Finset.Icc (A - k) (A - 1), i) := by
  exact erdos_55963_hyp_final_ns.erdos_55963_hyp_final



namespace Finset
def lcmInterval {α : Type*} [CommSemiring α] [NormalizedGCDMonoid α]
    [Preorder α] [LocallyFiniteOrder α] (n k : α) : α := (Finset.Ioc n (n + k)).lcm id
end Finset

open Asymptotics Filter Finset

theorem erdos_55963 :
    ∀ᶠ k in atTop, {(m, n) | n + k ≤ m ∧ lcmInterval m (k + 1) < lcmInterval n k}.Nonempty := by
  rw [Filter.eventually_atTop]
  refine ⟨25, fun k hk => ?_⟩
  obtain ⟨p0, q, hp0, hq, hpq, h2p, hqx⟩ := erdos_55963_hyp_ramanujan (k - 1) (by omega)
  have hk1 : k + 1 < 2 * q := by omega
  have hk2 : q + 1 ≤ k := by omega
  obtain ⟨t, ht1, ht2, hdvd⟩ := erdos_55963_hyp_crt k q hq hk1 hk2
  obtain ⟨A, hA⟩ : ∃ A, A = t * (erdos_55963_L k / q) := ⟨_, rfl⟩
  have hgood : erdos_55963_Good k q A := by
    unfold erdos_55963_Good
    refine ⟨hq, hk1, hk2, ⟨t, ht1, ht2, hA⟩, ?_⟩
    rw [hA]
    exact hdvd
  obtain ⟨hkA, hfin⟩ := erdos_55963_hyp_final k q A hgood hk
  have h1 := erdos_55963_hyp_right k q A hgood hkA
  have h2 := erdos_55963_hyp_left k q A hgood hkA
  have e1 : lcmInterval (A - 1) (k + 1) = (Finset.Icc A (A + k)).lcm id := by
    show (Finset.Ioc (A - 1) (A - 1 + (k + 1))).lcm id = _
    congr 1
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have e2 : lcmInterval (A - k - 1) k = (Finset.Icc (A - k) (A - 1)).lcm id := by
    show (Finset.Ioc (A - k - 1) (A - k - 1 + k)).lcm id = _
    congr 1
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  refine ⟨(A - 1, A - k - 1), ?_⟩
  show A - k - 1 + k ≤ A - 1 ∧ lcmInterval (A - 1) (k + 1) < lcmInterval (A - k - 1) k
  refine ⟨by omega, ?_⟩
  rw [e1, e2]
  have hPR : 0 < ∏ i ∈ Finset.Icc A (A + k), i := by
    apply Finset.prod_pos
    intro i hi
    rw [Finset.mem_Icc] at hi
    omega
  have hmem : ∀ x ∈ Finset.Icc (A - k) (A - 1), x ≠ 0 := by
    intro x hx
    rw [Finset.mem_Icc] at hx
    omega
  have hlpos : 0 < (Finset.Icc (A - k) (A - 1)).lcm id := by
    apply Nat.pos_of_ne_zero
    rw [Ne, Finset.lcm_eq_zero_iff]
    rintro ⟨x, hx, hx0⟩
    exact hmem x (Finset.mem_coe.mp hx) hx0
  have hR := Nat.le_of_dvd hPR h1
  have hL := Nat.le_of_dvd (Nat.mul_pos hlpos (Nat.factorial_pos k)) h2
  have hlt : (Finset.Icc A (A + k)).lcm id * Nat.factorial k <
      (Finset.Icc (A - k) (A - 1)).lcm id * Nat.factorial k :=
    (hR.trans_lt hfin).trans_le hL
  exact lt_of_mul_lt_mul_right hlt (Nat.zero_le _)