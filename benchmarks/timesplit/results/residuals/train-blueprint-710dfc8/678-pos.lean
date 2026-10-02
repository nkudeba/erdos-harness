def e86081Lk (k : ℕ) : ℕ := (Finset.Icc 1 k).lcm id

def e86081Nagura : Prop :=
  ∀ x : ℝ, 25 ≤ x → ∃ p : ℕ, p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) < 6 * x / 5

def e86081Nair : Prop := ∀ k : ℕ, 7 ≤ k → 2 ^ k ≤ e86081Lk k

def e86081RealIneq : Prop :=
  ∀ (k : ℕ) (X : ℝ), 1 ≤ k → 4 * (k : ℝ) ^ 3 ≤ X - k →
    ∏ i ∈ Finset.Icc 1 k, (X + (i : ℝ)) <
      (1 + 1 / (k : ℝ)) * ∏ i ∈ Finset.Icc 1 k, (X - (i : ℝ))

-- PUBLISHED: J. Nagura, "On the interval containing at least one prime number", Proc. Japan Acad. 28 (1952), 177–181 (main theorem)
theorem erdos_86081_hyp_nagura : e86081Nagura := by
  sorry

-- PUBLISHED: M. Nair, "On Chebyshev-type inequalities for primes", Amer. Math. Monthly 89 (1982), 126–129
theorem erdos_86081_hyp_nair : e86081Nair := by
  sorry

-- S8: apply Nagura at x = (k+1)/2 ≥ 25; then q < 3(k+1)/5 ≤ k-1.
namespace erdos_86081_hyp_choice_q_ns
open Asymptotics Filter Finset

theorem erdos_86081_hyp_choice_q :
    e86081Nagura → ∀ k : ℕ, 49 ≤ k → ∃ q : ℕ, q.Prime ∧ k + 1 < 2 * q ∧ q ≤ k - 1 := by
  intro hN k hk
  have hk' : (49:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  obtain ⟨p, hp, h1, h2⟩ := hN (((k:ℝ) + 1) / 2) (by linarith)
  refine ⟨p, hp, ?_, ?_⟩
  · have h3 : (k:ℝ) + 1 < 2 * (p:ℝ) := by linarith
    exact_mod_cast h3
  · have h3 : (p:ℝ) < (k:ℝ) := by linarith
    have h4 : p < k := by exact_mod_cast h3
    omega
end erdos_86081_hyp_choice_q_ns

theorem erdos_86081_hyp_choice_q :
    e86081Nagura → ∀ k : ℕ, 49 ≤ k → ∃ q : ℕ, q.Prime ∧ k + 1 < 2 * q ∧ q ≤ k - 1 := by
  exact erdos_86081_hyp_choice_q_ns.erdos_86081_hyp_choice_q



-- S9: R = L_k/q is coprime to q because q^2 > k; pick u ∈ [1,q-1] with uR ≡ -1 mod q and set X = uR; Nair gives X ≥ k+1.
namespace erdos_86081_hyp_choice_X_ns
open Asymptotics Filter Finset

private lemma e86081_sq_lt_two_pow (n : ℕ) (hn : 5 ≤ n) : n * n < 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ]
    nlinarith

private lemma e86081_q_dvd_L (k q : ℕ) (hq1 : 1 ≤ q) (hqk : q ≤ k) : q ∣ e86081Lk k := by
  unfold e86081Lk
  exact Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨hq1, hqk⟩)

private lemma e86081_L_dvd (k q : ℕ) :
    e86081Lk k ∣ q * ∏ i ∈ (Finset.Icc 1 k).erase q, i := by
  unfold e86081Lk
  rw [Finset.lcm_dvd_iff]
  intro b hb
  show b ∣ q * _
  by_cases h : b = q
  · rw [h]; exact dvd_mul_right q _
  · exact dvd_mul_of_dvd_right
      (Finset.dvd_prod_of_mem (fun i : ℕ => i) (Finset.mem_erase.mpr ⟨h, hb⟩)) _

private lemma e86081_not_dvd_R (k q : ℕ) (hq : q.Prime) (hk : k + 1 < 2 * q) (hqk : q ≤ k) :
    ¬ q * q ∣ e86081Lk k := by
  intro h
  have h2 := h.trans (e86081_L_dvd k q)
  rw [Nat.mul_dvd_mul_iff_left hq.pos] at h2
  obtain ⟨i, hi, hqi⟩ := (Prime.dvd_finset_prod_iff hq.prime (fun i : ℕ => i)).mp h2
  rw [Finset.mem_erase, Finset.mem_Icc] at hi
  obtain ⟨c, rfl⟩ := hqi
  rcases Nat.lt_or_ge c 2 with hc | hc
  · interval_cases c <;> omega
  · have : q * 2 ≤ q * c := Nat.mul_le_mul_left q hc
    omega

theorem erdos_86081_hyp_choice_X :
    e86081Nair → ∀ k q : ℕ, 49 ≤ k → q.Prime → k + 1 < 2 * q → q ≤ k - 1 →
      ∃ X : ℕ, k + 1 ≤ X ∧
        (∀ p : ℕ, p.Prime → p ≤ k → p ≠ q → p ^ Nat.log p k ∣ X) ∧
        q ∣ X + 1 ∧ e86081Lk k ≤ k * X ∧ q * X ≤ (q - 1) * e86081Lk k := by
  intro hNair k q hk hq hkq hqk
  have hq1 : 1 ≤ q := hq.one_lt.le
  have hqk' : q ≤ k := by omega
  obtain ⟨R, hR⟩ := e86081_q_dvd_L k q hq1 hqk'
  have hRq : ¬ q ∣ R := by
    intro hd
    apply e86081_not_dvd_R k q hq hkq hqk'
    rw [hR]
    exact Nat.mul_dvd_mul_left q hd
  haveI := Fact.mk hq
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hR0 : (R : ZMod q) ≠ 0 := by
    intro h0
    exact hRq ((CharP.cast_eq_zero_iff (ZMod q) q R).mp h0)
  obtain ⟨u, hu⟩ : ∃ u : ℕ, u = (-((R : ZMod q)⁻¹)).val := ⟨_, rfl⟩
  have hdvd : q ∣ u * R + 1 := by
    rw [← CharP.cast_eq_zero_iff (ZMod q) q]
    push_cast
    rw [hu, ZMod.natCast_zmod_val, neg_mul, inv_mul_cancel₀ hR0]
    ring
  have hult : u < q := by rw [hu]; exact ZMod.val_lt _
  have hu1 : 1 ≤ u := by
    rcases Nat.eq_zero_or_pos u with h | h
    · rw [h, zero_mul, zero_add] at hdvd
      have := Nat.le_of_dvd one_pos hdvd
      have := hq.two_le
      omega
    · exact h
  have hL2 := hNair k (by omega)
  rw [hR] at hL2
  have hRu : R ≤ u * R := by nlinarith
  have hc : q * R ≤ k * (u * R) := by
    calc q * R ≤ k * R := Nat.mul_le_mul_right R hqk'
      _ ≤ k * (u * R) := Nat.mul_le_mul_left k hRu
  refine ⟨u * R, ?_, ?_, hdvd, ?_, ?_⟩
  · by_contra hcon
    have h1 : u * R ≤ k := by omega
    have h2 : k * (u * R) ≤ k * k := Nat.mul_le_mul_left k h1
    have h3 := e86081_sq_lt_two_pow k (by omega)
    omega
  · intro p hp hpk hpq
    have hk0 : k ≠ 0 := by omega
    have hpe : p ^ Nat.log p k ≤ k := Nat.pow_log_le_self p hk0
    have hpe1 : 1 ≤ p ^ Nat.log p k := Nat.one_le_pow _ _ hp.pos
    have hdL : p ^ Nat.log p k ∣ q * R := by
      rw [← hR]; unfold e86081Lk
      exact Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨hpe1, hpe⟩)
    have hcop : Nat.Coprime (p ^ Nat.log p k) q :=
      Nat.Coprime.pow_left _ ((Nat.coprime_primes hp hq).mpr hpq)
    have hpR : p ^ Nat.log p k ∣ R := by
      first
        | exact hcop.dvd_of_dvd_mul_left hdL
        | exact hcop.dvd_of_dvd_mul_right (by rw [mul_comm]; exact hdL)
    exact dvd_mul_of_dvd_right hpR u
  · rw [hR]; exact hc
  · rw [hR]
    have : u ≤ q - 1 := by omega
    calc q * (u * R) = u * (q * R) := by ring
      _ ≤ (q - 1) * (q * R) := Nat.mul_le_mul_right _ this
end erdos_86081_hyp_choice_X_ns

theorem erdos_86081_hyp_choice_X :
    e86081Nair → ∀ k q : ℕ, 49 ≤ k → q.Prime → k + 1 < 2 * q → q ≤ k - 1 →
      ∃ X : ℕ, k + 1 ≤ X ∧
        (∀ p : ℕ, p.Prime → p ≤ k → p ≠ q → p ^ Nat.log p k ∣ X) ∧
        q ∣ X + 1 ∧ e86081Lk k ≤ k * X ∧ q * X ≤ (q - 1) * e86081Lk k := by
  exact erdos_86081_hyp_choice_X_ns.erdos_86081_hyp_choice_X



-- S11 (via S4, S5, S6, S10, Legendre): the excess on X..X+k is at least v_p(k!) for every prime p.
namespace erdos_86081_hyp_mside_ns
private lemma e86_fact_eq (k : ℕ) : ∏ t ∈ Finset.range k, (t + 1) = k.factorial := by
  induction k with
  | zero => simp
  | succ n ih => rw [Finset.prod_range_succ, ih, Nat.factorial_succ]; ring

private lemma e86_pt (p k X t Z : ℕ) (hp : p.Prime) (hX : p ^ Nat.log p k ∣ X) (ht : t < k)
    (hZ : Z ≠ 0) (hdiv : ∀ d, d ∣ X → d ∣ t + 1 → d ∣ Z) :
    (t + 1).factorization p ≤ Z.factorization p := by
  have h1 : p ^ (t + 1).factorization p ∣ t + 1 :=
    (hp.pow_dvd_iff_le_factorization (by omega)).mpr le_rfl
  have hle : p ^ (t + 1).factorization p ≤ k :=
    le_trans (Nat.le_of_dvd (Nat.succ_pos t) h1) (by omega)
  have h2 : (t + 1).factorization p ≤ Nat.log p k := by
    first
      | exact Nat.le_log_of_pow_le hp.one_lt hle
      | exact (Nat.pow_le_iff_le_log hp.one_lt (by omega)).1 hle
  have h3 : p ^ (t + 1).factorization p ∣ X := (pow_dvd_pow p h2).trans hX
  exact (hp.pow_dvd_iff_le_factorization hZ).mp (hdiv _ h3 h1)

private lemma e86_sum (p k X : ℕ) (hp : p.Prime) (hX : p ^ Nat.log p k ∣ X) (S : Finset ℕ)
    (hS : ∀ t ∈ S, t < k) :
    (∏ t ∈ S, (t + 1)).factorization p ≤ (∏ t ∈ S, (X + (t + 1))).factorization p := by
  have e1 : (∏ t ∈ S, (t + 1)).factorization = ∑ t ∈ S, (t + 1).factorization :=
    Nat.factorization_prod (fun t _ => Nat.succ_ne_zero t)
  have e2 : (∏ t ∈ S, (X + (t + 1))).factorization = ∑ t ∈ S, (X + (t + 1)).factorization :=
    Nat.factorization_prod (fun t _ => Nat.succ_ne_zero (X + t))
  rw [e1, e2]
  simp only [Finsupp.finset_sum_apply]
  apply Finset.sum_le_sum
  intro t ht
  exact e86_pt p k X t _ hp hX (hS t ht) (by omega) (fun d h1 h2 => dvd_add h1 h2)

private lemma e86_q (k q : ℕ) (hq : q.Prime) (h1 : k + 1 < 2 * q) (h2 : 49 ≤ k) :
    k.factorial.factorization q ≤ 1 := by
  haveI := Fact.mk hq
  have hq26 : 26 ≤ q := by omega
  have hlt : k < q ^ 2 := by rw [pow_two]; nlinarith
  have hlog : Nat.log q k < 2 := by
    first
      | exact Nat.log_lt_of_lt_pow (by omega) hlt
      | exact (Nat.lt_pow_iff_log_lt hq.one_lt (by omega)).1 hlt
  rw [Nat.factorization_def _ hq, padicValNat_factorial hlog]
  have hI : Finset.Ico 1 2 = {1} := by
    ext x
    simp only [Finset.mem_Ico, Finset.mem_singleton]
    constructor <;> intro h <;> omega
  rw [hI, Finset.sum_singleton, pow_one]
  have := (Nat.div_lt_iff_lt_mul hq.pos).2 (show k < 2 * q by omega)
  omega

private lemma e86_key (k q X : ℕ) (hk : 49 ≤ k) (hq : q.Prime) (h1 : k + 1 < 2 * q)
    (h2 : q ≤ k - 1) (hX0 : k + 1 ≤ X)
    (hX : ∀ p : ℕ, p.Prime → p ≠ q → p ^ Nat.log p k ∣ X) (hqX : q ∣ X + 1)
    (i : ℕ) (hi : i ≤ k) :
    k.factorial * (X + i) ∣ ∏ j ∈ Finset.range (k + 1), (X + j) := by
  rw [Finset.prod_range_succ']
  simp only [add_zero]
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · simp only [add_zero]
    apply mul_dvd_mul_right
    have hne : (∏ t ∈ Finset.range k, (X + (t + 1))) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]; intro t _; omega
    apply (Nat.factorization_prime_le_iff_dvd (Nat.factorial_ne_zero k) hne).mp
    intro p hp
    by_cases hpq : p = q
    · rw [hpq]
      have hd : q ∣ ∏ t ∈ Finset.range k, (X + (t + 1)) :=
        hqX.trans (Finset.dvd_prod_of_mem (fun t => X + (t + 1))
          (Finset.mem_range.mpr (by omega : 0 < k)))
      have := hq.factorization_pos_of_dvd hne hd
      have := e86_q k q hq h1 hk
      omega
    · rw [← e86_fact_eq k]
      exact e86_sum p k X hp (hX p hp hpq) _ (fun t ht => Finset.mem_range.mp ht)
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have hj : j ∈ Finset.range k := Finset.mem_range.mpr (by omega)
    rw [← Finset.mul_prod_erase _ (fun t => X + (t + 1)) hj]
    show k.factorial * (X + (j + 1)) ∣
      ((X + (j + 1)) * ∏ t ∈ (Finset.range k).erase j, (X + (t + 1))) * X
    rw [show ((X + (j + 1)) * ∏ t ∈ (Finset.range k).erase j, (X + (t + 1))) * X
        = (X + (j + 1)) * ((∏ t ∈ (Finset.range k).erase j, (X + (t + 1))) * X) by ring,
      mul_comm (k.factorial)]
    apply mul_dvd_mul_left
    have hE2 : (∏ t ∈ (Finset.range k).erase j, (X + (t + 1))) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]; intro t _; omega
    have hXne : X ≠ 0 := by omega
    have hne : (∏ t ∈ (Finset.range k).erase j, (X + (t + 1))) * X ≠ 0 :=
      mul_ne_zero hE2 hXne
    apply (Nat.factorization_prime_le_iff_dvd (Nat.factorial_ne_zero k) hne).mp
    intro p hp
    by_cases hpq : p = q
    · rw [hpq]
      have hd : q ∣ (∏ t ∈ (Finset.range k).erase j, (X + (t + 1))) * X := by
        apply Dvd.dvd.mul_right
        by_cases hj0 : j = 0
        · have hmem : q ∈ (Finset.range k).erase j :=
            Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩
          refine Dvd.dvd.trans ?_ (Finset.dvd_prod_of_mem (fun t => X + (t + 1)) hmem)
          show q ∣ X + (q + 1)
          have : X + (q + 1) = (X + 1) + q := by ring
          rw [this]; exact dvd_add hqX dvd_rfl
        · have hmem : 0 ∈ (Finset.range k).erase j :=
            Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩
          exact hqX.trans (Finset.dvd_prod_of_mem (fun t => X + (t + 1)) hmem)
      have := hq.factorization_pos_of_dvd hne hd
      have := e86_q k q hq h1 hk
      omega
    · have hXp := hX p hp hpq
      have hfac : k.factorial = (j + 1) * ∏ t ∈ (Finset.range k).erase j, (t + 1) := by
        rw [← e86_fact_eq k]
        exact (Finset.mul_prod_erase _ (fun t => t + 1) hj).symm
      have hE1 : (∏ t ∈ (Finset.range k).erase j, (t + 1)) ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]; intro t _; omega
      have hj1 : j + 1 ≠ 0 := by omega
      rw [hfac, Nat.factorization_mul hj1 hE1, Nat.factorization_mul hE2 hXne]
      first
        | simp only [Finsupp.add_apply]
        | simp only [Finsupp.coe_add, Pi.add_apply]
      have a1 := e86_pt p k X j X hp hXp (by omega) hXne (fun d h1 _ => h1)
      have a2 := e86_sum p k X hp hXp ((Finset.range k).erase j)
        (fun t ht => Finset.mem_range.mp (Finset.mem_of_mem_erase ht))
      omega

open Asymptotics Filter Finset

theorem erdos_86081_hyp_mside :
    ∀ k q X : ℕ, 49 ≤ k → q.Prime → k + 1 < 2 * q → q ≤ k - 1 → k + 1 ≤ X →
      (∀ p : ℕ, p.Prime → p ≤ k → p ≠ q → p ^ Nat.log p k ∣ X) → q ∣ X + 1 →
      k.factorial * (Finset.Icc X (X + k)).lcm id ∣ ∏ i ∈ Finset.range (k + 1), (X + i) := by
  intro k q X hk hq h1 h2 hX0 hXp hqX
  have hX : ∀ p : ℕ, p.Prime → p ≠ q → p ^ Nat.log p k ∣ X := by
    intro p hp hpq
    by_cases hpk : p ≤ k
    · exact hXp p hp hpk hpq
    · rw [Nat.log_of_lt (by omega)]; simp
  have key := e86_key k q X hk hq h1 h2 hX0 hX hqX
  obtain ⟨N, hN⟩ : k.factorial ∣ ∏ i ∈ Finset.range (k + 1), (X + i) :=
    (dvd_mul_right (k.factorial) (X + 0)).trans (key 0 (Nat.zero_le _))
  rw [hN]
  apply mul_dvd_mul_left
  apply Finset.lcm_dvd
  intro y hy
  rw [Finset.mem_Icc] at hy
  have h := key (y - X) (by omega)
  rw [show X + (y - X) = y by omega, hN] at h
  exact Nat.dvd_of_mul_dvd_mul_left (Nat.factorial_pos k) h
end erdos_86081_hyp_mside_ns

theorem erdos_86081_hyp_mside :
    ∀ k q X : ℕ, 49 ≤ k → q.Prime → k + 1 < 2 * q → q ≤ k - 1 → k + 1 ≤ X →
      (∀ p : ℕ, p.Prime → p ≤ k → p ≠ q → p ^ Nat.log p k ∣ X) → q ∣ X + 1 →
      k.factorial * (Finset.Icc X (X + k)).lcm id ∣ ∏ i ∈ Finset.range (k + 1), (X + i) := by
  exact erdos_86081_hyp_mside_ns.erdos_86081_hyp_mside



-- S12 (via S4, S5, S6, S7, S10, Legendre): the excess on X-k..X-1 is exactly v_p(k!) - v_p(L_k).
namespace erdos_86081_hyp_nside_ns
open Asymptotics Filter Finset

private lemma e86081_fact_lcm (T : Finset ℕ) (a : ℕ → ℕ) (ha : ∀ i ∈ T, a i ≠ 0) (p : ℕ) :
    (T.lcm a).factorization p = T.sup (fun i => (a i).factorization p) := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    have ha0 : a j ≠ 0 := ha j (Finset.mem_insert_self j s)
    have hs' : ∀ x ∈ s, a x ≠ 0 := fun x hx => ha x (Finset.mem_insert_of_mem hx)
    have hl : s.lcm a ≠ 0 := by
      intro h
      rw [Finset.lcm_eq_zero_iff] at h
      obtain ⟨x, hx, h0⟩ := h
      exact hs' x hx h0
    rw [Finset.lcm_insert, Finset.sup_insert]
    have e : GCDMonoid.lcm (a j) (s.lcm a) = Nat.lcm (a j) (s.lcm a) := rfl
    rw [e, Nat.factorization_lcm ha0 hl, Finsupp.sup_apply, ih hs']

private lemma e86081_fact_count (p x B : ℕ) (hp : p.Prime) (hx : x ≠ 0) (hB : x ≤ B) :
    x.factorization p = #{e ∈ Finset.Icc 1 B | p ^ e ∣ x} := by
  have hlt : x.factorization p < x := Nat.factorization_lt p hx
  have : {e ∈ Finset.Icc 1 B | p ^ e ∣ x} = Finset.Icc 1 (x.factorization p) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_Icc, hp.pow_dvd_iff_le_factorization hx]
    omega
  rw [this, Nat.card_Icc]; omega

private lemma e86081_sum_count (T : Finset ℕ) (a : ℕ → ℕ) (ha : ∀ i ∈ T, a i ≠ 0) (p B : ℕ)
    (hp : p.Prime) (hB : ∀ i ∈ T, a i ≤ B) :
    ∑ i ∈ T, (a i).factorization p = ∑ e ∈ Finset.Icc 1 B, #{i ∈ T | p ^ e ∣ a i} := by
  rw [Finset.sum_congr rfl (fun i hi => e86081_fact_count p (a i) B hp (ha i hi) (hB i hi))]
  simp only [Finset.card_filter]
  exact Finset.sum_comm

private lemma e86081_lcm_count (T : Finset ℕ) (a : ℕ → ℕ) (ha : ∀ i ∈ T, a i ≠ 0) (p B : ℕ)
    (hp : p.Prime) (hB : ∀ i ∈ T, a i ≤ B) :
    (T.lcm a).factorization p =
      ∑ e ∈ Finset.Icc 1 B, if (∃ i ∈ T, p ^ e ∣ a i) then 1 else 0 := by
  rw [← Finset.card_filter, e86081_fact_lcm T a ha p]
  have hsup : T.sup (fun i => (a i).factorization p) ≤ B := by
    apply Finset.sup_le
    intro i hi
    have := Nat.factorization_lt p (ha i hi)
    have := hB i hi
    omega
  have : {e ∈ Finset.Icc 1 B | ∃ i ∈ T, p ^ e ∣ a i} =
      Finset.Icc 1 (T.sup (fun i => (a i).factorization p)) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, _⟩, i, hi, hd⟩
      refine ⟨h1, ?_⟩
      rw [hp.pow_dvd_iff_le_factorization (ha i hi)] at hd
      exact le_trans hd (Finset.le_sup (f := fun i => (a i).factorization p) hi)
    · rintro ⟨h1, h2⟩
      have hbot : (⊥ : ℕ) < e := by rw [bot_eq_zero']; omega
      obtain ⟨i, hi, hle⟩ := (Finset.le_sup_iff hbot).mp h2
      refine ⟨⟨h1, by omega⟩, i, hi, ?_⟩
      rw [hp.pow_dvd_iff_le_factorization (ha i hi)]
      exact hle
  rw [this, Nat.card_Icc]; omega

private lemma e86081_level (k q X p e : ℕ) (hk : 49 ≤ k) (hq : q.Prime) (h2q : k + 1 < 2 * q)
    (hqk : q ≤ k - 1) (hX : k + 1 ≤ X)
    (hpow : ∀ p : ℕ, p.Prime → p ≤ k → p ≠ q → p ^ Nat.log p k ∣ X) (hqX : q ∣ X + 1)
    (hp : p.Prime) (he : 1 ≤ e) :
    #{i ∈ Finset.Icc 1 k | p ^ e ∣ i} +
        (if (∃ i ∈ Finset.Icc 1 k, p ^ e ∣ X - i) then 1 else 0) =
      (if (∃ i ∈ Finset.Icc 1 k, p ^ e ∣ i) then 1 else 0) +
        #{i ∈ Finset.Icc 1 k | p ^ e ∣ X - i} := by
  by_cases hdX : p ^ e ∣ X
  · have key : ∀ i ∈ Finset.Icc 1 k, (p ^ e ∣ X - i ↔ p ^ e ∣ i) := by
      intro i hi
      rw [Finset.mem_Icc] at hi
      constructor
      · intro h
        have := Nat.dvd_sub hdX h
        rwa [show X - (X - i) = i by omega] at this
      · intro h
        exact Nat.dvd_sub hdX h
    rw [Finset.filter_congr key]
    have : (∃ i ∈ Finset.Icc 1 k, p ^ e ∣ X - i) ↔ (∃ i ∈ Finset.Icc 1 k, p ^ e ∣ i) :=
      ⟨fun ⟨i, hi, h⟩ => ⟨i, hi, (key i hi).mp h⟩, fun ⟨i, hi, h⟩ => ⟨i, hi, (key i hi).mpr h⟩⟩
    simp only [this]
    exact Nat.add_comm _ _
  by_cases hdk : k < p ^ e
  · have h1 : {i ∈ Finset.Icc 1 k | p ^ e ∣ i} = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro i hi hd
      rw [Finset.mem_Icc] at hi
      have := Nat.le_of_dvd (by omega) hd
      omega
    have h2 : ¬ (∃ i ∈ Finset.Icc 1 k, p ^ e ∣ i) := by
      rintro ⟨i, hi, hd⟩
      rw [Finset.mem_Icc] at hi
      have := Nat.le_of_dvd (by omega) hd
      omega
    have h3 : #{i ∈ Finset.Icc 1 k | p ^ e ∣ X - i} ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro i hi j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hi hj
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · have := Nat.dvd_sub hi.2 hj.2
        rw [show X - i - (X - j) = j - i by omega] at this
        have := Nat.le_of_dvd (by omega) this
        omega
      · have := Nat.dvd_sub hj.2 hi.2
        rw [show X - j - (X - i) = i - j by omega] at this
        have := Nat.le_of_dvd (by omega) this
        omega
    rw [h1, if_neg h2, Finset.card_empty]
    split_ifs with h4
    · obtain ⟨i, hi, hd⟩ := h4
      have : 0 < #{i ∈ Finset.Icc 1 k | p ^ e ∣ X - i} :=
        Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hd⟩⟩
      omega
    · have : {i ∈ Finset.Icc 1 k | p ^ e ∣ X - i} = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro i hi hd
        exact h4 ⟨i, hi, hd⟩
      rw [this, Finset.card_empty]
  push_neg at hdk
  have hpk : p ≤ k := le_trans (Nat.le_self_pow (by omega) p) hdk
  have hpq : p = q := by
    by_contra hne
    apply hdX
    have hle : e ≤ Nat.log p k := Nat.le_log_of_pow_le hp.one_lt hdk
    exact (pow_dvd_pow p hle).trans (hpow p hp hpk hne)
  subst q
  have he1 : e = 1 := by
    by_contra hne
    have : p ^ 2 ≤ p ^ e := Nat.pow_le_pow_right hp.pos (by omega)
    have : 2 * p ≤ p ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul_right p hp.two_le
    omega
  subst he1
  clear hq
  simp only [pow_one]
  have hp2 := hp.two_le
  have hdq : p ∣ X - (p - 1) := by
    have : X + 1 = (X - (p - 1)) + p := by omega
    rw [this] at hqX
    exact (Nat.dvd_add_left (dvd_refl p)).mp hqX
  have hA : ∃ i ∈ Finset.Icc 1 k, p ∣ i :=
    ⟨p, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, dvd_refl p⟩
  have hB : ∃ i ∈ Finset.Icc 1 k, p ∣ X - i :=
    ⟨p - 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hdq⟩
  have hC : #{i ∈ Finset.Icc 1 k | p ∣ i} = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨p, ?_⟩
    ext i
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨h1, h2⟩, c, rfl⟩
      rcases c with _ | _ | c
      · omega
      · simp
      · nlinarith
    · rintro rfl
      exact ⟨⟨by omega, by omega⟩, dvd_refl _⟩
  have hD : #{i ∈ Finset.Icc 1 k | p ∣ X - i} = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨p - 1, ?_⟩
    ext i
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨h1, h2⟩, hd⟩
      have h3 := Nat.dvd_sub hqX hd
      rw [show X + 1 - (X - i) = i + 1 by omega] at h3
      obtain ⟨c, hc⟩ := h3
      rcases c with _ | _ | c
      · omega
      · omega
      · nlinarith
    · rintro rfl
      exact ⟨⟨by omega, by omega⟩, hdq⟩
  rw [hC, hD, if_pos hA, if_pos hB]

theorem erdos_86081_hyp_nside :
    ∀ k q X : ℕ, 49 ≤ k → q.Prime → k + 1 < 2 * q → q ≤ k - 1 → k + 1 ≤ X →
      (∀ p : ℕ, p.Prime → p ≤ k → p ≠ q → p ^ Nat.log p k ∣ X) → q ∣ X + 1 →
      k.factorial * (Finset.Icc (X - k) (X - 1)).lcm id =
        e86081Lk k * ∏ i ∈ Finset.Icc 1 k, (X - i) := by
  intro k q X hk hq h2q hqk hX hpow hqX
  unfold e86081Lk
  have hJ : ∀ x ∈ Finset.Icc 1 k, x ≠ 0 := by
    intro x hx; rw [Finset.mem_Icc] at hx; omega
  have hP : ∀ i ∈ Finset.Icc 1 k, X - i ≠ 0 := by
    intro i hi; rw [Finset.mem_Icc] at hi; omega
  have hlcm0 : ∀ (s : Finset ℕ) (a : ℕ → ℕ), (∀ x ∈ s, a x ≠ 0) → s.lcm a ≠ 0 := by
    intro s a hs h
    rw [Finset.lcm_eq_zero_iff] at h
    obtain ⟨x, hx, h0⟩ := h
    exact hs x hx h0
  have hS : (Finset.Icc (X - k) (X - 1)).lcm id = (Finset.Icc 1 k).lcm (fun i => X - i) := by
    have : Finset.Icc (X - k) (X - 1) = (Finset.Icc 1 k).image (fun i => X - i) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_image]
      constructor
      · intro h; exact ⟨X - x, by omega, by omega⟩
      · rintro ⟨i, hi, rfl⟩; omega
    rw [this, Finset.lcm_image]; rfl
  rw [hS]
  have hfac : k.factorial ≠ 0 := Nat.factorial_ne_zero k
  have hprod : ∏ i ∈ Finset.Icc 1 k, (X - i) ≠ 0 := Finset.prod_ne_zero_iff.mpr hP
  have hL1 := hlcm0 _ _ hP
  have hL2 := hlcm0 _ id hJ
  have hfp : k.factorial = ∏ i ∈ Finset.Icc 1 k, i := by
    rw [← Finset.prod_Ico_id_eq_factorial]
    rfl
  apply Nat.eq_of_factorization_eq
  · exact mul_ne_zero hfac hL1
  · exact mul_ne_zero hL2 hprod
  · intro p
    rw [Nat.factorization_mul hfac hL1, Nat.factorization_mul hL2 hprod]
    by_cases hp : p.Prime
    · simp only [Finsupp.add_apply]
      rw [hfp, Nat.factorization_prod hJ, Nat.factorization_prod hP]
      simp only [Finsupp.finsetSum_apply]
      have h1 := e86081_sum_count (Finset.Icc 1 k) (fun i => i) hJ p X hp
        (by intro i hi; rw [Finset.mem_Icc] at hi; omega)
      have h2 := e86081_sum_count (Finset.Icc 1 k) (fun i => X - i) hP p X hp
        (by intro i hi; omega)
      have h3 := e86081_lcm_count (Finset.Icc 1 k) (fun i => X - i) hP p X hp
        (by intro i hi; omega)
      have h4 := e86081_lcm_count (Finset.Icc 1 k) id hJ p X hp
        (by intro i hi; rw [Finset.mem_Icc] at hi; simp only [id_eq]; omega)
      simp only [id_eq] at h4
      have h5 := Finset.sum_congr rfl (fun e (he : e ∈ Finset.Icc 1 X) =>
        e86081_level k q X p e hk hq h2q hqk hX hpow hqX hp (Finset.mem_Icc.mp he).1)
      rw [h1, h2, h3, h4, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact h5
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
end erdos_86081_hyp_nside_ns

theorem erdos_86081_hyp_nside :
    ∀ k q X : ℕ, 49 ≤ k → q.Prime → k + 1 < 2 * q → q ≤ k - 1 → k + 1 ≤ X →
      (∀ p : ℕ, p.Prime → p ≤ k → p ≠ q → p ^ Nat.log p k ∣ X) → q ∣ X + 1 →
      k.factorial * (Finset.Icc (X - k) (X - 1)).lcm id =
        e86081Lk k * ∏ i ∈ Finset.Icc 1 k, (X - i) := by
  exact erdos_86081_hyp_nside_ns.erdos_86081_hyp_nside



-- S13: each ratio (X+i)/(X-i) ≤ 1 + 2k/(X-k); then use 1+t ≤ e^t and e^x < 1 + 2x for 0 < x ≤ 1/2.
namespace erdos_86081_hyp_real_ineq_ns
open Asymptotics Filter Finset

theorem erdos_86081_hyp_real_ineq : e86081RealIneq := by
  intro k X hk hX
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hk3 : 0 < 4 * (k:ℝ) ^ 3 := by positivity
  have hd : 0 < X - k := by linarith
  have hX0 : 0 < X := by linarith
  obtain ⟨t, ht_def⟩ : ∃ t : ℝ, t = 2 * k / (X - k) := ⟨_, rfl⟩
  have ht : 0 < t := by rw [ht_def]; apply div_pos <;> linarith
  have hpos : ∀ i ∈ Finset.Icc 1 k, 0 < X - (i:ℝ) := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    have : (i:ℝ) ≤ k := by exact_mod_cast hi.2
    linarith
  have hfac : ∀ i ∈ Finset.Icc 1 k, X + (i:ℝ) ≤ (1 + t) * (X - i) := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    have hik : (i:ℝ) ≤ k := by exact_mod_cast hi.2
    have hi1 : (1:ℝ) ≤ i := by exact_mod_cast hi.1
    have e : (1 + t) * (X - i) = (X - i) + 2 * k * (X - i) / (X - k) := by
      rw [ht_def]; ring
    rw [e]
    have : 2 * (i:ℝ) ≤ 2 * k * (X - i) / (X - k) := by
      rw [le_div_iff₀ hd]
      nlinarith [mul_nonneg (sub_nonneg.mpr hik) hX0.le]
    linarith
  have hprod : ∏ i ∈ Finset.Icc 1 k, (X + (i:ℝ)) ≤
      ∏ i ∈ Finset.Icc 1 k, ((1 + t) * (X - (i:ℝ))) := by
    apply Finset.prod_le_prod
    · intro i hi
      have := hpos i hi
      have : (0:ℝ) ≤ i := by positivity
      linarith
    · exact hfac
  rw [Finset.prod_mul_distrib, Finset.prod_const] at hprod
  simp only [Nat.card_Icc, Nat.add_sub_cancel] at hprod
  have ht2e : 2 * (k:ℝ) * t * k = 4 * (k:ℝ) ^ 3 / (X - k) := by
    rw [ht_def]; ring
  have ht2 : 2 * (k:ℝ) * t * k ≤ 1 := by
    rw [ht2e, div_le_one hd]; linarith
  have hkt : 2 * (k:ℝ) * t ≤ 1 := by
    have : 0 ≤ 2 * (k:ℝ) * t := by positivity
    nlinarith
  have key : ∀ j : ℕ, 1 ≤ j → j ≤ k → (1 + t) ^ j < 1 + 2 * (j:ℝ) * t := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
      intro _
      rw [pow_one]; push_cast; linarith
    | succ j hj ih =>
      intro hjk
      have h1 := ih (by omega)
      have hjk' : (j:ℝ) ≤ k := by exact_mod_cast (show j ≤ k by omega)
      have hjt : 2 * (j:ℝ) * t ≤ 1 := by
        have : 2 * (j:ℝ) * t ≤ 2 * (k:ℝ) * t := by
          have := mul_le_mul_of_nonneg_right hjk' ht.le
          nlinarith
        linarith
      calc (1 + t) ^ (j + 1) = (1 + t) ^ j * (1 + t) := pow_succ _ _
        _ < (1 + 2 * (j:ℝ) * t) * (1 + t) := mul_lt_mul_of_pos_right h1 (by linarith)
        _ ≤ 1 + 2 * ((j + 1 : ℕ) : ℝ) * t := by
          push_cast
          nlinarith [mul_le_mul_of_nonneg_right hjt ht.le]
  have hpow := key k hk le_rfl
  have hP : 0 < ∏ i ∈ Finset.Icc 1 k, (X - (i:ℝ)) := Finset.prod_pos hpos
  have hfin : 1 + 2 * (k:ℝ) * t ≤ 1 + 1 / (k:ℝ) := by
    have : 2 * (k:ℝ) * t ≤ 1 / k := by
      rw [le_div_iff₀ (by positivity)]; linarith
    linarith
  calc ∏ i ∈ Finset.Icc 1 k, (X + (i:ℝ))
      ≤ (1 + t) ^ k * ∏ i ∈ Finset.Icc 1 k, (X - (i:ℝ)) := hprod
    _ < (1 + 2 * (k:ℝ) * t) * ∏ i ∈ Finset.Icc 1 k, (X - (i:ℝ)) :=
        mul_lt_mul_of_pos_right hpow hP
    _ ≤ (1 + 1 / (k:ℝ)) * ∏ i ∈ Finset.Icc 1 k, (X - (i:ℝ)) :=
        mul_le_mul_of_nonneg_right hfin hP.le
end erdos_86081_hyp_real_ineq_ns

theorem erdos_86081_hyp_real_ineq : e86081RealIneq := by
  exact erdos_86081_hyp_real_ineq_ns.erdos_86081_hyp_real_ineq



-- S14: from Nair, 2^k ≥ k^5 gives X - k ≥ 4k^3; S13 then gives the bound (1+1/k)·P_-, and 1+1/k < q/(q-1) ≤ L_k/X.
namespace erdos_86081_hyp_main_ineq_ns
private lemma e86081_pow5 (n : ℕ) (hn : 23 ≤ n) : n ^ 5 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h1 : 23 * n ^ 4 ≤ n ^ 5 := by
      calc 23 * n ^ 4 ≤ n * n ^ 4 := Nat.mul_le_mul_right _ hn
        _ = n ^ 5 := by ring
    have h2 : 23 * n ^ 3 ≤ n ^ 4 := by
      calc 23 * n ^ 3 ≤ n * n ^ 3 := Nat.mul_le_mul_right _ hn
        _ = n ^ 4 := by ring
    have h3 : 23 * n ^ 2 ≤ n ^ 3 := by
      calc 23 * n ^ 2 ≤ n * n ^ 2 := Nat.mul_le_mul_right _ hn
        _ = n ^ 3 := by ring
    have h4 : 23 * n ≤ n ^ 2 := by
      calc 23 * n ≤ n * n := Nat.mul_le_mul_right _ hn
        _ = n ^ 2 := by ring
    have hexp : (n + 1) ^ 5 = n ^ 5 + 5 * n ^ 4 + 10 * n ^ 3 + 10 * n ^ 2 + 5 * n + 1 := by ring
    have h6 : (n + 1) ^ 5 ≤ 2 * n ^ 5 := by
      rw [hexp]; linarith
    calc (n + 1) ^ 5 ≤ 2 * n ^ 5 := h6
      _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (n + 1) := by ring

open Asymptotics Filter Finset

theorem erdos_86081_hyp_main_ineq :
    e86081Nair → e86081RealIneq → ∀ k q X : ℕ, 49 ≤ k → q.Prime → k + 1 < 2 * q →
      q ≤ k - 1 → e86081Lk k ≤ k * X → q * X ≤ (q - 1) * e86081Lk k →
      ∏ i ∈ Finset.range (k + 1), (X + i) < e86081Lk k * ∏ i ∈ Finset.Icc 1 k, (X - i) := by
  intro hNair hineq k q X hk hq hq2 hqk hLX hqX
  have hL2 : 2 ^ k ≤ e86081Lk k := hNair k (by omega)
  have h5 : k ^ 5 ≤ 2 ^ k := e86081_pow5 k (by omega)
  have hk4 : k * k ^ 4 ≤ k * X := by
    calc k * k ^ 4 = k ^ 5 := by ring
      _ ≤ 2 ^ k := h5
      _ ≤ e86081Lk k := hL2
      _ ≤ k * X := hLX
  have hX4 : k ^ 4 ≤ X := Nat.le_of_mul_le_mul_left hk4 (by omega)
  have h49 : 49 * k ^ 3 ≤ k ^ 4 := by
    calc 49 * k ^ 3 ≤ k * k ^ 3 := Nat.mul_le_mul_right _ hk
      _ = k ^ 4 := by ring
  have hk3 : k ≤ k ^ 3 := by
    calc k = k ^ 1 := (pow_one k).symm
      _ ≤ k ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hXbig : 4 * k ^ 3 + k ≤ X := by linarith
  have hXge : k + 1 ≤ X := by linarith
  have hs : Finset.range (k + 1) = insert 0 (Finset.Icc 1 k) := by
    ext i
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have h0 : (0 : ℕ) ∉ Finset.Icc 1 k := by simp
  rw [hs, Finset.prod_insert h0, add_zero]
  have hcast : ((∏ i ∈ Finset.Icc 1 k, (X - i) : ℕ) : ℝ)
      = ∏ i ∈ Finset.Icc 1 k, ((X : ℝ) - (i : ℝ)) := by
    rw [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i hi
    rw [Finset.mem_Icc] at hi
    rw [Nat.cast_sub (by omega)]
  rw [← Nat.cast_lt (α := ℝ), Nat.cast_mul, Nat.cast_mul, hcast, Nat.cast_prod]
  push_cast
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hLpos : (0 : ℝ) < (e86081Lk k : ℝ) := by
    have : 0 < e86081Lk k := lt_of_lt_of_le (by positivity) hL2
    exact_mod_cast this
  have hXr : (k : ℝ) + 1 ≤ X := by exact_mod_cast hXge
  have hbig : 4 * (k : ℝ) ^ 3 ≤ X - k := by
    have : ((4 * k ^ 3 + k : ℕ) : ℝ) ≤ X := by exact_mod_cast hXbig
    push_cast at this
    linarith
  have hR := hineq k (X : ℝ) (by omega) hbig
  have hQpos : 0 < ∏ i ∈ Finset.Icc 1 k, ((X : ℝ) - (i : ℝ)) := by
    apply Finset.prod_pos
    intro i hi
    rw [Finset.mem_Icc] at hi
    have : (i : ℝ) ≤ k := by exact_mod_cast hi.2
    linarith
  have hq1 : 1 ≤ q := hq.one_lt.le
  have hqXr : (q : ℝ) * X ≤ ((q : ℝ) - 1) * (e86081Lk k : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).mpr hqX
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hq1, Nat.cast_one] at this
    exact this
  have hqk' : (q : ℝ) < k + 1 := by
    have : q < k + 1 := by omega
    exact_mod_cast this
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have key : (X : ℝ) * (k + 1) < k * (e86081Lk k : ℝ) := by
    by_contra hc
    push_neg at hc
    nlinarith [mul_le_mul_of_nonneg_left hc hq0,
      mul_le_mul_of_nonneg_right hqXr (by linarith : (0 : ℝ) ≤ k + 1),
      mul_lt_mul_of_pos_right hqk' hLpos]
  have hXk : (X : ℝ) * (1 + 1 / k) < e86081Lk k := by
    rw [mul_add, mul_one, mul_one_div]
    have : (X : ℝ) / k < e86081Lk k - X := by
      rw [div_lt_iff₀ hkpos]
      nlinarith
    linarith
  have h1 := mul_lt_mul_of_pos_left hR hXpos
  have h2 := mul_lt_mul_of_pos_right hXk hQpos
  have h3 : (X : ℝ) * ((1 + 1 / (k : ℝ)) * ∏ i ∈ Finset.Icc 1 k, ((X : ℝ) - (i : ℝ)))
      = ((X : ℝ) * (1 + 1 / (k : ℝ))) * ∏ i ∈ Finset.Icc 1 k, ((X : ℝ) - (i : ℝ)) := by ring
  rw [h3] at h1
  exact lt_trans h1 h2
end erdos_86081_hyp_main_ineq_ns

theorem erdos_86081_hyp_main_ineq :
    e86081Nair → e86081RealIneq → ∀ k q X : ℕ, 49 ≤ k → q.Prime → k + 1 < 2 * q →
      q ≤ k - 1 → e86081Lk k ≤ k * X → q * X ≤ (q - 1) * e86081Lk k →
      ∏ i ∈ Finset.range (k + 1), (X + i) < e86081Lk k * ∏ i ∈ Finset.Icc 1 k, (X - i) := by
  exact erdos_86081_hyp_main_ineq_ns.erdos_86081_hyp_main_ineq



namespace Finset
def lcmInterval {α : Type*} [CommSemiring α] [NormalizedGCDMonoid α]
    [Preorder α] [LocallyFiniteOrder α] (n k : α) : α := (Finset.Ioc n (n + k)).lcm id
end Finset

open Asymptotics Filter Finset

theorem erdos_86081 :
    ∀ᶠ k in atTop, {(m, n) | n + k ≤ m ∧ lcmInterval m (k + 1) < lcmInterval n k}.Nonempty := by
  refine Filter.eventually_atTop.2 ⟨49, fun k hk => ?_⟩
  obtain ⟨q, hq, hq1, hq2⟩ := erdos_86081_hyp_choice_q erdos_86081_hyp_nagura k hk
  obtain ⟨X, hX1, hXa, hXb, hXc, hXd⟩ :=
    erdos_86081_hyp_choice_X erdos_86081_hyp_nair k q hk hq hq1 hq2
  have hm := erdos_86081_hyp_mside k q X hk hq hq1 hq2 hX1 hXa hXb
  have hn := erdos_86081_hyp_nside k q X hk hq hq1 hq2 hX1 hXa hXb
  have hi := erdos_86081_hyp_main_ineq erdos_86081_hyp_nair erdos_86081_hyp_real_ineq
    k q X hk hq hq1 hq2 hXc hXd
  have e1 : Finset.lcmInterval (X - 1) (k + 1) = (Finset.Icc X (X + k)).lcm id := by
    show (Finset.Ioc (X - 1) (X - 1 + (k + 1))).lcm id = (Finset.Icc X (X + k)).lcm id
    have hs : Finset.Ioc (X - 1) (X - 1 + (k + 1)) = Finset.Icc X (X + k) := by
      ext x
      simp only [Finset.mem_Ioc, Finset.mem_Icc]
      omega
    rw [hs]
  have e2 : Finset.lcmInterval (X - 1 - k) k = (Finset.Icc (X - k) (X - 1)).lcm id := by
    show (Finset.Ioc (X - 1 - k) (X - 1 - k + k)).lcm id = (Finset.Icc (X - k) (X - 1)).lcm id
    have hs : Finset.Ioc (X - 1 - k) (X - 1 - k + k) = Finset.Icc (X - k) (X - 1) := by
      ext x
      simp only [Finset.mem_Ioc, Finset.mem_Icc]
      omega
    rw [hs]
  refine ⟨(X - 1, X - 1 - k), ?_⟩
  show X - 1 - k + k ≤ X - 1 ∧ Finset.lcmInterval (X - 1) (k + 1) < Finset.lcmInterval (X - 1 - k) k
  refine ⟨by omega, ?_⟩
  rw [e1, e2]
  have hP : 0 < ∏ i ∈ Finset.range (k + 1), (X + i) := Finset.prod_pos fun i _ => by omega
  have h1 := Nat.le_of_dvd hP hm
  exact lt_of_mul_lt_mul_left (h1.trans_lt (hi.trans_eq hn.symm)) (Nat.zero_le _)