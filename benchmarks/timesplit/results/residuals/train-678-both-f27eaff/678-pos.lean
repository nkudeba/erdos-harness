-- CHECK: Nat.eq_iff_prime_padicValNat_eq padicValNat.mul Nat.eq_of_factorization_eq Nat.factorization_def Nat.factorization_eq_zero_of_non_prime Finset.lcm_eq_zero_iff Finset.prod_ne_zero_iff Nat.coprime_primes Nat.Coprime.pow_left Finset.sum_add_distrib
def erdos81727_L (k : ℕ) : ℕ := (Finset.Icc 1 k).lcm id

def erdos81727_admissible (k q : ℕ) : Prop :=
  q.Prime ∧ k + 2 ≤ 2 * q ∧ 2 * q + 2 ≤ 2 * k

def erdos81727_A (N k : ℕ) : Finset ℕ := Finset.Ioc (N - k - 1) (N - k - 1 + k)

def erdos81727_B (N k : ℕ) : Finset ℕ := Finset.Ioc (N - 1) (N - 1 + (k + 1))

def erdos81727_cnt (d : ℕ) (s : Finset ℕ) : ℕ := (s.filter (fun x => d ∣ x)).card

namespace erdos_81727_hyp_residue_ns
open Asymptotics Filter Finset

theorem erdos_81727_hyp_residue :
    ∀ k q : ℕ, erdos81727_admissible k q →
      ∃ u : ℕ, 1 ≤ u ∧ u < q ∧ q ∣ erdos81727_L k / q * u + 1 := by
  intro k q hadm
  obtain ⟨hq, h1, h2⟩ := hadm
  haveI := Fact.mk hq
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hq2 := hq.two_le
  have hqmem : q ∈ Finset.Icc 1 k := by
    rw [Finset.mem_Icc]; omega
  have hndvd : ¬ q ∣ ((Finset.Icc 1 k).erase q).lcm id := by
    intro hd
    have hdp : ((Finset.Icc 1 k).erase q).lcm id ∣ ∏ i ∈ (Finset.Icc 1 k).erase q, i :=
      Finset.lcm_dvd (fun i hi => Finset.dvd_prod_of_mem (fun j : ℕ => j) hi)
    obtain ⟨i, hi, hqi⟩ := (Prime.dvd_finset_prod_iff hq.prime (fun j : ℕ => j)).mp (hd.trans hdp)
    rw [Finset.mem_erase, Finset.mem_Icc] at hi
    obtain ⟨c, hc⟩ := hqi
    have hc' : i = q * c := hc
    have hcases : c = 0 ∨ c = 1 ∨ 2 ≤ c := by omega
    rcases hcases with h | h | h
    · subst h; rw [Nat.mul_zero] at hc'; omega
    · subst h; rw [Nat.mul_one] at hc'; omega
    · have : q * 2 ≤ q * c := Nat.mul_le_mul_left q h
      omega
  have hcop : Nat.Coprime q (((Finset.Icc 1 k).erase q).lcm id) :=
    (Nat.Prime.coprime_iff_not_dvd hq).mpr hndvd
  have hL : erdos81727_L k = q * ((Finset.Icc 1 k).erase q).lcm id := by
    unfold erdos81727_L
    conv_lhs => rw [← Finset.insert_erase hqmem]
    rw [Finset.lcm_insert]
    show Nat.lcm q (((Finset.Icc 1 k).erase q).lcm id) = _
    exact Nat.Coprime.lcm_eq_mul hcop
  rw [hL, Nat.mul_div_cancel_left _ hq.pos]
  set L' := ((Finset.Icc 1 k).erase q).lcm id with hL'
  have hne : (L' : ZMod q) ≠ 0 := by
    intro h
    exact hndvd ((CharP.cast_eq_zero_iff (ZMod q) q L').mp h)
  set v : ZMod q := -((L' : ZMod q))⁻¹ with hv
  have hv0 : v ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hne)
  refine ⟨v.val, ?_, ZMod.val_lt v, ?_⟩
  · rw [Nat.one_le_iff_ne_zero]
    intro h0
    exact hv0 ((ZMod.val_eq_zero v).mp h0)
  · rw [← CharP.cast_eq_zero_iff (ZMod q) q]
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_one, ZMod.natCast_zmod_val, hv,
      mul_neg, mul_inv_cancel₀ hne]
    ring
end erdos_81727_hyp_residue_ns

-- Derived: admissibility forces 3 ≤ q ≤ k and q^2 > k, so v_q(L) = 1.
-- Hence gcd(L/q, q) = 1, and the inverse of L/q mod q gives u ∈ [1, q-1] with (L/q)u ≡ -1 (mod q).
theorem erdos_81727_hyp_residue :
    ∀ k q : ℕ, erdos81727_admissible k q →
      ∃ u : ℕ, 1 ≤ u ∧ u < q ∧ q ∣ erdos81727_L k / q * u + 1 := by
  exact erdos_81727_hyp_residue_ns.erdos_81727_hyp_residue

namespace erdos_81727_hyp_size_ns
open Asymptotics Filter Finset

private lemma pow_bound (k : ℕ) (hk : 46 ≤ k) : 2 * k ^ 4 < 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h1 : 46 * n ^ 3 ≤ n ^ 4 := by
      calc 46 * n ^ 3 ≤ n * n ^ 3 := Nat.mul_le_mul_right _ hn
        _ = n ^ 4 := by ring
    have h2 : 46 * n ^ 2 ≤ n ^ 3 := by
      calc 46 * n ^ 2 ≤ n * n ^ 2 := Nat.mul_le_mul_right _ hn
        _ = n ^ 3 := by ring
    have h3 : 46 * n ≤ n ^ 2 := by
      calc 46 * n ≤ n * n := Nat.mul_le_mul_right _ hn
        _ = n ^ 2 := by ring
    have h5 : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
    have h6 : (n + 1) ^ 4 = n ^ 4 + 4 * n ^ 3 + 6 * n ^ 2 + 4 * n + 1 := by ring
    rw [h5, h6]
    first | omega | linarith | nlinarith

private lemma prod_Ioc_shift (a n : ℕ) (f : ℕ → ℕ) :
    ∏ i ∈ Finset.Ioc a (a + n), f i = ∏ i ∈ Finset.range n, f (a + 1 + i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show a + (n + 1) = a + n + 1 by omega, Finset.prod_Ioc_succ_top (by omega : a ≤ a + n),
      ih, Finset.prod_range_succ, show a + n + 1 = a + 1 + n by omega]

private lemma prod_key (N : ℤ) (j : ℕ) (hN : (j : ℤ) * ((j : ℤ) + 1) ≤ N) :
    (∏ i ∈ Finset.range j, (N + ((i : ℤ) + 1))) * (N - (j : ℤ) * ((j : ℤ) + 1)) ≤
      (∏ i ∈ Finset.range j, (N - ((i : ℤ) + 1))) * N := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    push_cast at hN ⊢
    have hj0 : (0 : ℤ) ≤ (j : ℤ) := by positivity
    have hN' : (j : ℤ) * ((j : ℤ) + 1) ≤ N := by nlinarith
    have ih' := ih hN'
    have hnn : 0 ≤ N - ((j : ℤ) + 1) := by nlinarith [sq_nonneg ((j : ℤ) + 1)]
    have hN0 : (0 : ℤ) ≤ N := by linarith
    have hP : 0 ≤ ∏ i ∈ Finset.range j, (N + ((i : ℤ) + 1)) :=
      Finset.prod_nonneg (fun i _ => by
        have : (0 : ℤ) ≤ (i : ℤ) := by positivity
        linarith)
    have hpoly : (N + ((j : ℤ) + 1)) * (N - ((j : ℤ) + 1) * ((j : ℤ) + 1 + 1)) ≤
        (N - (j : ℤ) * ((j : ℤ) + 1)) * (N - ((j : ℤ) + 1)) := by
      nlinarith [pow_nonneg (by linarith : (0 : ℤ) ≤ (j : ℤ) + 1) 3]
    nlinarith [mul_le_mul_of_nonneg_right ih' hnn, mul_le_mul_of_nonneg_left hpoly hP]

theorem erdos_81727_hyp_size :
    ∀ k q u M : ℕ, 46 ≤ k → 3 ≤ q → q ≤ k → 1 ≤ u → u < q → 2 ^ k ≤ q * M →
      k + 1 ≤ M * u ∧
        (∏ i ∈ erdos81727_B (M * u) k, i) < q * M * (∏ i ∈ erdos81727_A (M * u) k, i) := by
  intro k q u M hk hq hqk hu1 huq hpow
  have h4 := pow_bound k hk
  have a1 : q * q ≤ k * k := Nat.mul_le_mul hqk hqk
  have a2 : k * (k + 1) ≤ k * (2 * k) := Nat.mul_le_mul_left k (by omega)
  have hqq : q * q * k * (k + 1) ≤ 2 * k ^ 4 := by
    calc q * q * k * (k + 1) = (q * q) * (k * (k + 1)) := by ring
      _ ≤ (k * k) * (k * (2 * k)) := Nat.mul_le_mul a1 a2
      _ = 2 * k ^ 4 := by ring
  have hM : q * k * (k + 1) < M := by
    by_contra h
    push_neg at h
    have h' : q * M ≤ q * (q * k * (k + 1)) := Nat.mul_le_mul_left q h
    have e : q * (q * k * (k + 1)) = q * q * k * (k + 1) := by ring
    rw [e] at h'
    first | omega | linarith
  have hMpos : 0 < M := by omega
  have hN1 : M ≤ M * u := by
    calc M = M * 1 := (mul_one M).symm
      _ ≤ M * u := Nat.mul_le_mul_left M hu1
  have hqk1 : 1 ≤ q * k := Nat.mul_pos (by omega) (by omega)
  have hk1 : k + 1 ≤ q * k * (k + 1) := by
    calc k + 1 = 1 * (k + 1) := (one_mul _).symm
      _ ≤ (q * k) * (k + 1) := Nat.mul_le_mul_right _ hqk1
  have hkk : k * (k + 1) ≤ q * k * (k + 1) := by
    calc k * (k + 1) = 1 * k * (k + 1) := by ring
      _ ≤ q * k * (k + 1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
  generalize hN : M * u = N at hN1 ⊢
  have hNk : k + 1 ≤ N := by omega
  have hbig : q * k * (k + 1) < N := by omega
  refine ⟨hNk, ?_⟩
  have hB : ∏ i ∈ erdos81727_B N k, i = (∏ i ∈ Finset.range k, (N + (i + 1))) * N := by
    unfold erdos81727_B
    rw [prod_Ioc_shift, Finset.prod_range_succ']
    have e : N - 1 + 1 = N := by omega
    simp only [e, add_zero]
  have hA : ∏ i ∈ erdos81727_A N k, i = ∏ i ∈ Finset.range k, (N - (i + 1)) := by
    unfold erdos81727_A
    rw [prod_Ioc_shift]
    have hr := Finset.prod_range_reflect (fun i => N - (i + 1)) k
    try beta_reduce at hr
    rw [← hr]
    apply Finset.prod_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    try beta_reduce
    omega
  rw [hB, hA]
  have hcastB : ((∏ i ∈ Finset.range k, (N + (i + 1)) : ℕ) : ℤ) =
      ∏ i ∈ Finset.range k, ((N : ℤ) + ((i : ℤ) + 1)) := by
    rw [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_one]
  have hcastA : ((∏ i ∈ Finset.range k, (N - (i + 1)) : ℕ) : ℤ) =
      ∏ i ∈ Finset.range k, ((N : ℤ) - ((i : ℤ) + 1)) := by
    rw [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have hle : i + 1 ≤ N := by omega
    rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_one]
  apply (Nat.cast_lt (α := ℤ)).mp
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, hcastB, hcastA]
  have hNz : (0 : ℤ) ≤ (N : ℤ) := by positivity
  have hPpos : 0 < ∏ i ∈ Finset.range k, ((N : ℤ) + ((i : ℤ) + 1)) :=
    Finset.prod_pos (fun i _ => by positivity)
  have hkz : (k : ℤ) * ((k : ℤ) + 1) ≤ (N : ℤ) := by exact_mod_cast (le_trans hkk hbig.le)
  have key := prod_key (N : ℤ) k hkz
  generalize hPd : (∏ i ∈ Finset.range k, ((N : ℤ) + ((i : ℤ) + 1))) = P at key hPpos ⊢
  generalize hQd : (∏ i ∈ Finset.range k, ((N : ℤ) - ((i : ℤ) + 1))) = Q at key ⊢
  have hbz : (q : ℤ) * k * (k + 1) < N := by exact_mod_cast hbig
  have huq' : u + 1 ≤ q := huq
  have huz : (u : ℤ) + 1 ≤ q := by exact_mod_cast huq'
  have h1 : (u : ℤ) * N < q * (N - k * (k + 1)) := by
    nlinarith [mul_le_mul_of_nonneg_right huz hNz]
  have hqz : (0 : ℤ) ≤ q := by positivity
  have h2 : (u : ℤ) * P * N < q * Q * N := by
    nlinarith [mul_lt_mul_of_pos_left h1 hPpos, mul_le_mul_of_nonneg_left key hqz]
  have h3 : (u : ℤ) * P < q * Q := lt_of_mul_lt_mul_right h2 hNz
  have hNM : (N : ℤ) = M * u := by exact_mod_cast hN.symm
  have hMz : (0 : ℤ) < M := by exact_mod_cast hMpos
  rw [hNM]
  nlinarith [mul_lt_mul_of_pos_left h3 hMz]
end erdos_81727_hyp_size_ns

-- Derived (pure size estimate, no lcm): with N = M*u ≥ M ≥ 2^k/q ≥ 2^k/k,
-- prod(B) < qM prod(A) iff u * prod_{i=1..k}(N+i) < q * prod_{i=1..k}(N-i),
-- which follows from u ≤ q-1 and prod (N+i)/(N-i) ≤ exp(2k^2/(N-k)) ≤ e^{1/q} < q/(q-1), as N - k ≥ 2k^2 q.
theorem erdos_81727_hyp_size :
    ∀ k q u M : ℕ, 46 ≤ k → 3 ≤ q → q ≤ k → 1 ≤ u → u < q → 2 ^ k ≤ q * M →
      k + 1 ≤ M * u ∧
        (∏ i ∈ erdos81727_B (M * u) k, i) < q * M * (∏ i ∈ erdos81727_A (M * u) k, i) := by
  exact erdos_81727_hyp_size_ns.erdos_81727_hyp_size

-- PUBLISHED: J. Nagura, "On the interval containing at least one prime number", Proc. Japan Acad. 28 (1952), 177-181 (for x ≥ 25 there is a prime in (x, 6x/5]).
theorem erdos_81727_hyp_nagura :
    ∀ x : ℝ, 25 ≤ x → ∃ p : ℕ, p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ 6 / 5 * x := by
  sorry

-- PUBLISHED: M. Nair, "On Chebyshev-type inequalities for primes", Amer. Math. Monthly 89 (1982), 126-129 (lcm(1,...,n) ≥ 2^n for n ≥ 7).
theorem erdos_81727_hyp_nair : ∀ k : ℕ, 7 ≤ k → 2 ^ k ≤ erdos81727_L k := by
  sorry

-- Derived (R1, valuation form, product half): v_p(x) = #{j ≥ 1 : p^j ∣ x}; sum over the interval and swap the sums.
-- Terms with j ≥ T vanish because p^j > j ≥ T > n + l ≥ every (positive) element.
namespace erdos_81727_hyp_vprod_ns
open Asymptotics Filter Finset

private lemma erdos81727_vx (p x T : ℕ) (hp : p.Prime) (hx : 0 < x) (hxT : x < T) :
    padicValNat p x = ((Finset.Ico 1 T).filter (fun j => p ^ j ∣ x)).card := by
  haveI := Fact.mk hp
  have hv : p ^ padicValNat p x ∣ x := pow_padicValNat_dvd
  have hle : p ^ padicValNat p x ≤ x := Nat.le_of_dvd hx hv
  have hlt : padicValNat p x < p ^ padicValNat p x := by
    first
    | exact Nat.lt_pow_self hp.one_lt
    | exact Nat.lt_pow_self hp.one_lt _
  have hset : (Finset.Ico 1 T).filter (fun j => p ^ j ∣ x)
      = Finset.Ico 1 (padicValNat p x + 1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Ico]
    rw [padicValNat_dvd_iff_le hx.ne']
    omega
  rw [hset, Nat.card_Ico]
  omega

private lemma erdos81727_vprod (p : ℕ) (hp : p.Prime) (s : Finset ℕ) :
    (∀ x ∈ s, 0 < x) → padicValNat p (∏ i ∈ s, i) = ∑ i ∈ s, padicValNat p i := by
  haveI := Fact.mk hp
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp
  · intro a s ha ih hs
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have h1 : a ≠ 0 := (hs a (Finset.mem_insert_self a s)).ne'
    have h2 : (∏ i ∈ s, i) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun x hx => (hs x (Finset.mem_insert_of_mem hx)).ne')
    rw [padicValNat.mul h1 h2, ih (fun x hx => hs x (Finset.mem_insert_of_mem hx))]

theorem erdos_81727_hyp_vprod :
    ∀ p n l T : ℕ, p.Prime → n + l < T →
      padicValNat p (∏ i ∈ Finset.Ioc n (n + l), i) =
        ∑ j ∈ Finset.Ico 1 T, erdos81727_cnt (p ^ j) (Finset.Ioc n (n + l)) := by
  intro p n l T hp hT
  rw [erdos81727_vprod p hp _ (fun x hx => by rw [Finset.mem_Ioc] at hx; omega)]
  have hsum : ∑ x ∈ Finset.Ioc n (n + l), padicValNat p x
      = ∑ x ∈ Finset.Ioc n (n + l), ((Finset.Ico 1 T).filter (fun j => p ^ j ∣ x)).card := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_Ioc] at hx
    exact erdos81727_vx p x T hp (by omega) (by omega)
  rw [hsum]
  simp only [erdos81727_cnt, Finset.card_filter]
  exact Finset.sum_comm
end erdos_81727_hyp_vprod_ns

theorem erdos_81727_hyp_vprod :
    ∀ p n l T : ℕ, p.Prime → n + l < T →
      padicValNat p (∏ i ∈ Finset.Ioc n (n + l), i) =
        ∑ j ∈ Finset.Ico 1 T, erdos81727_cnt (p ^ j) (Finset.Ioc n (n + l)) := by
  exact erdos_81727_hyp_vprod_ns.erdos_81727_hyp_vprod



-- Derived (R1, valuation form, lcm half): v_p(lcm I) = max_{x ∈ I} v_p(x) = #{j ≥ 1 : some x ∈ I has p^j ∣ x},
-- because the set of such j is downward closed.
namespace erdos_81727_hyp_vlcm_ns
-- CHECK: Nat.factorization_lcm Finsupp.sup_apply Nat.Prime.pow_dvd_iff_le_factorization Finset.lcm_insert Finset.sum_Ico_consecutive
private lemma lcm_ne_zero_aux (s : Finset ℕ) (h : ∀ x ∈ s, x ≠ 0) : s.lcm id ≠ 0 := by
  intro h0
  rw [Finset.lcm_eq_zero_iff] at h0
  obtain ⟨x, hx, hx0⟩ := h0
  exact h x hx hx0

private lemma pow_dvd_lcm_aux (p j : ℕ) (hp : p.Prime) (hj : 1 ≤ j) (s : Finset ℕ) :
    (∀ x ∈ s, x ≠ 0) → p ^ j ∣ s.lcm id → ∃ x ∈ s, p ^ j ∣ x := by
  refine Finset.induction_on s ?_ ?_
  · intro _ hd
    rw [Finset.lcm_empty] at hd
    have h1 := Nat.le_of_dvd one_pos hd
    have h2 : p ≤ p ^ j := by
      calc p = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ j := Nat.pow_le_pow_right hp.pos hj
    have h3 := hp.two_le
    omega
  · intro a s ha ih hs hd
    rw [Finset.lcm_insert] at hd
    have ha0 : a ≠ 0 := hs a (Finset.mem_insert_self a s)
    have hs' : ∀ x ∈ s, x ≠ 0 := fun x hx => hs x (Finset.mem_insert_of_mem hx)
    have hb0 := lcm_ne_zero_aux s hs'
    have hd' : p ^ j ∣ Nat.lcm a (s.lcm id) := hd
    rw [hp.pow_dvd_iff_le_factorization (Nat.lcm_ne_zero ha0 hb0),
      Nat.factorization_lcm ha0 hb0, Finsupp.sup_apply] at hd'
    rcases le_sup_iff.mp hd' with h1 | h1
    · exact ⟨a, Finset.mem_insert_self a s, (hp.pow_dvd_iff_le_factorization ha0).mpr h1⟩
    · obtain ⟨x, hx, hx'⟩ := ih hs' ((hp.pow_dvd_iff_le_factorization hb0).mpr h1)
      exact ⟨x, Finset.mem_insert_of_mem hx, hx'⟩

private lemma pow_dvd_lcm_iff (p j : ℕ) (hp : p.Prime) (hj : 1 ≤ j) (s : Finset ℕ)
    (h : ∀ x ∈ s, x ≠ 0) : p ^ j ∣ s.lcm id ↔ ∃ x ∈ s, p ^ j ∣ x := by
  constructor
  · exact pow_dvd_lcm_aux p j hp hj s h
  · rintro ⟨x, hx, hdx⟩
    exact hdx.trans (Finset.dvd_lcm (f := id) hx)

private lemma lt_pow_aux (p v : ℕ) (hp : 2 ≤ p) : v < p ^ v := by
  induction v with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    have h2 := Nat.mul_le_mul (le_refl (p ^ k)) hp
    linarith

open Asymptotics Filter Finset

theorem erdos_81727_hyp_vlcm :
    ∀ p n l T : ℕ, p.Prime → n + l < T →
      padicValNat p ((Finset.Ioc n (n + l)).lcm id) =
        ∑ j ∈ Finset.Ico 1 T,
          (if 1 ≤ erdos81727_cnt (p ^ j) (Finset.Ioc n (n + l)) then 1 else 0) := by
  intro p n l T hp hT
  have hpos : ∀ x ∈ Finset.Ioc n (n + l), x ≠ 0 := by
    intro x hx; rw [Finset.mem_Ioc] at hx; omega
  have hL0 := lcm_ne_zero_aux _ hpos
  rw [← Nat.factorization_def _ hp]
  set L := (Finset.Ioc n (n + l)).lcm id with hL
  set v := L.factorization p with hv
  have hiff : ∀ j, 1 ≤ j →
      (1 ≤ erdos81727_cnt (p ^ j) (Finset.Ioc n (n + l)) ↔ j ≤ v) := by
    intro j hj
    rw [hv, ← hp.pow_dvd_iff_le_factorization hL0, hL, pow_dvd_lcm_iff p j hp hj _ hpos]
    unfold erdos81727_cnt
    constructor
    · intro h
      obtain ⟨x, hx⟩ := Finset.card_pos.mp h
      rw [Finset.mem_filter] at hx
      exact ⟨x, hx.1, hx.2⟩
    · rintro ⟨x, hx, hdx⟩
      exact Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hdx⟩⟩
  have hvT : v < T := by
    rcases Nat.eq_zero_or_pos v with h0 | h0
    · omega
    · have hd : p ^ v ∣ L := (hp.pow_dvd_iff_le_factorization hL0).mpr le_rfl
      rw [hL, pow_dvd_lcm_iff p v hp h0 _ hpos] at hd
      obtain ⟨x, hx, hdx⟩ := hd
      rw [Finset.mem_Ioc] at hx
      have h1 := Nat.le_of_dvd (by omega) hdx
      have h2 := lt_pow_aux p v hp.two_le
      exact lt_of_lt_of_le h2 (le_trans h1 (by omega : x ≤ T))
  have hsum : ∀ j ∈ Finset.Ico 1 T,
      (if 1 ≤ erdos81727_cnt (p ^ j) (Finset.Ioc n (n + l)) then 1 else 0)
        = (if j ≤ v then 1 else 0) := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    by_cases h : j ≤ v
    · rw [if_pos ((hiff j hj.1).mpr h), if_pos h]
    · rw [if_neg (fun h' => h ((hiff j hj.1).mp h')), if_neg h]
  rw [Finset.sum_congr rfl hsum]
  rw [← Finset.sum_Ico_consecutive _ (show 1 ≤ v + 1 by omega) (show v + 1 ≤ T by omega)]
  have h1s : ∀ j ∈ Finset.Ico 1 (v + 1), (if j ≤ v then 1 else 0 : ℕ) = 1 := by
    intro j hj; rw [Finset.mem_Ico] at hj; rw [if_pos (by omega)]
  have e1 : ∑ j ∈ Finset.Ico 1 (v + 1), (if j ≤ v then 1 else 0 : ℕ) = v := by
    rw [Finset.sum_congr rfl h1s, Finset.sum_const, Nat.card_Ico, smul_eq_mul]
    omega
  have e2 : ∑ j ∈ Finset.Ico (v + 1) T, (if j ≤ v then 1 else 0 : ℕ) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj; rw [Finset.mem_Ico] at hj; rw [if_neg (by omega)]
  linarith [e1, e2]
end erdos_81727_hyp_vlcm_ns

theorem erdos_81727_hyp_vlcm :
    ∀ p n l T : ℕ, p.Prime → n + l < T →
      padicValNat p ((Finset.Ioc n (n + l)).lcm id) =
        ∑ j ∈ Finset.Ico 1 T,
          (if 1 ≤ erdos81727_cnt (p ^ j) (Finset.Ioc n (n + l)) then 1 else 0) := by
  exact erdos_81727_hyp_vlcm_ns.erdos_81727_hyp_vlcm



-- Derived: v_p(lcm(1..k)) = #{j ≥ 1 : p^j ≤ k}; this is the special case n = 0 of the lcm formula.
namespace erdos_81727_hyp_vL_ns
open Asymptotics Filter Finset

theorem erdos_81727_hyp_vL :
    ∀ k p T : ℕ, p.Prime → k < T →
      padicValNat p (erdos81727_L k) =
        ∑ j ∈ Finset.Ico 1 T, (if p ^ j ≤ k then 1 else 0) := by
  intro k p T hp hkT
  haveI := Fact.mk hp
  have hp1 : 1 < p := hp.one_lt
  have hlt : ∀ n : ℕ, n < p ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ]; nlinarith
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · rw [Finset.sum_eq_zero]
    · show padicValNat p ((Finset.Icc 1 0).lcm id) = 0
      rw [Finset.Icc_eq_empty (by norm_num)]
      simp
    · intro j _
      have := pow_pos hp.pos j
      split_ifs with h <;> omega
  have hk0 : k ≠ 0 := by omega
  obtain ⟨e, he⟩ : ∃ e, e = Nat.log p k := ⟨_, rfl⟩
  have hpe_iff : ∀ j, p ^ j ≤ k ↔ j ≤ e := fun j => by
    rw [he]; exact (Nat.le_log_iff_pow_le hp1 hk0).symm
  have hsum : (∑ j ∈ Finset.Ico 1 T, (if p ^ j ≤ k then 1 else 0)) = e := by
    have h1 : p ^ e ≤ k := (hpe_iff e).mpr le_rfl
    have h2 := hlt e
    have hfilt : (Finset.Ico 1 T).filter (fun j => p ^ j ≤ k) = Finset.Icc 1 e := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Icc]
      rw [hpe_iff j]
      constructor
      · rintro ⟨⟨h3, _⟩, h4⟩; exact ⟨h3, h4⟩
      · rintro ⟨h3, h4⟩; exact ⟨⟨h3, by omega⟩, h4⟩
    rw [← Finset.card_filter, hfilt, Nat.card_Icc]; omega
  rw [hsum]
  have hL0 : erdos81727_L k ≠ 0 := by
    unfold erdos81727_L
    intro h
    rw [Finset.lcm_eq_zero_iff] at h
    simp at h
  apply le_antisymm
  · have hCcop : Nat.Coprime p (∏ x ∈ Finset.Icc 1 k, x / p ^ (x.factorization p)) := by
      apply Nat.Coprime.prod_right
      intro x hx
      have : x ≠ 0 := by rw [Finset.mem_Icc] at hx; omega
      exact Nat.coprime_ordCompl hp this
    have hdiv : erdos81727_L k ∣ p ^ e * ∏ x ∈ Finset.Icc 1 k, x / p ^ (x.factorization p) := by
      unfold erdos81727_L
      apply Finset.lcm_dvd
      intro x hx
      have hx0 : x ≠ 0 := by rw [Finset.mem_Icc] at hx; omega
      have hxk : x ≤ k := by rw [Finset.mem_Icc] at hx; omega
      have hd : p ^ (x.factorization p) ∣ x := Nat.ordProj_dvd x p
      have hle : x.factorization p ≤ e := by
        rw [← hpe_iff]; exact le_trans (Nat.le_of_dvd (by omega) hd) hxk
      have hx_eq : x = p ^ (x.factorization p) * (x / p ^ (x.factorization p)) :=
        (Nat.mul_div_cancel' hd).symm
      have h2 : x / p ^ (x.factorization p) ∣
          ∏ y ∈ Finset.Icc 1 k, y / p ^ (y.factorization p) := Finset.dvd_prod_of_mem _ hx
      show x ∣ _
      calc x = p ^ (x.factorization p) * (x / p ^ (x.factorization p)) := hx_eq
        _ ∣ _ := mul_dvd_mul (pow_dvd_pow p hle) h2
    have hv : p ^ padicValNat p (erdos81727_L k) ∣
        p ^ e * ∏ x ∈ Finset.Icc 1 k, x / p ^ (x.factorization p) :=
      (pow_padicValNat_dvd).trans hdiv
    have hcop2 := Nat.Coprime.pow_left (padicValNat p (erdos81727_L k)) hCcop
    have h3 : p ^ padicValNat p (erdos81727_L k) ∣ p ^ e := hcop2.dvd_of_dvd_mul_right hv
    exact (Nat.pow_dvd_pow_iff_le_right hp1).mp h3
  · rw [← padicValNat_dvd_iff_le hL0]
    unfold erdos81727_L
    have hmem : p ^ e ∈ Finset.Icc 1 k := by
      rw [Finset.mem_Icc]; exact ⟨Nat.one_le_pow _ _ hp.pos, (hpe_iff e).mpr le_rfl⟩
    exact Finset.dvd_lcm (f := id) hmem
end erdos_81727_hyp_vL_ns

theorem erdos_81727_hyp_vL :
    ∀ k p T : ℕ, p.Prime → k < T →
      padicValNat p (erdos81727_L k) =
        ∑ j ∈ Finset.Ico 1 T, (if p ^ j ≤ k then 1 else 0) := by
  exact erdos_81727_hyp_vL_ns.erdos_81727_hyp_vL



-- Derived: l consecutive integers with l ≤ d contain at most one multiple of d.
namespace erdos_81727_hyp_cnt_le_one_ns
open Asymptotics Filter Finset

theorem erdos_81727_hyp_cnt_le_one :
    ∀ d a l : ℕ, 0 < d → l ≤ d → erdos81727_cnt d (Finset.Ioc a (a + l)) ≤ 1 := by
  intro d a l hd hl
  unfold erdos81727_cnt
  rw [Finset.card_le_one]
  intro x hx y hy
  rw [Finset.mem_filter, Finset.mem_Ioc] at hx hy
  obtain ⟨⟨hx1, hx2⟩, c, rfl⟩ := hx
  obtain ⟨⟨hy1, hy2⟩, e, rfl⟩ := hy
  rcases lt_trichotomy c e with h | h | h
  · have h1 : d * (c + 1) ≤ d * e := Nat.mul_le_mul (le_refl d) (Nat.succ_le_of_lt h)
    rw [Nat.mul_add, Nat.mul_one] at h1
    exfalso
    linarith
  · rw [h]
  · have h1 : d * (e + 1) ≤ d * c := Nat.mul_le_mul (le_refl d) (Nat.succ_le_of_lt h)
    rw [Nat.mul_add, Nat.mul_one] at h1
    exfalso
    linarith
end erdos_81727_hyp_cnt_le_one_ns

theorem erdos_81727_hyp_cnt_le_one :
    ∀ d a l : ℕ, 0 < d → l ≤ d → erdos81727_cnt d (Finset.Ioc a (a + l)) ≤ 1 := by
  exact erdos_81727_hyp_cnt_le_one_ns.erdos_81727_hyp_cnt_le_one



-- Derived: if d ∣ N and d ≤ l, then [N, N+l] has floor(l/d)+1 multiples of d and [N-l, N-1] has floor(l/d) ≥ 1.
namespace erdos_81727_hyp_cnt_smooth_ns
open Asymptotics Filter Finset

private lemma erdos81727_cnt_Ioc (d a b : ℕ) (h : a ≤ b) :
    erdos81727_cnt d (Finset.Ioc a b) + a / d = b / d := by
  have hu : Finset.Ioc 0 a ∪ Finset.Ioc a b = Finset.Ioc 0 b :=
    Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le a) h
  have hdisj : Disjoint ((Finset.Ioc 0 a).filter (fun x => d ∣ x))
      ((Finset.Ioc a b).filter (fun x => d ∣ x)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hx hx'
    omega
  have hc := Finset.card_union_add_card_inter ((Finset.Ioc 0 a).filter (fun x => d ∣ x))
      ((Finset.Ioc a b).filter (fun x => d ∣ x))
  rw [Finset.disjoint_iff_inter_eq_empty.mp hdisj, Finset.card_empty, add_zero,
    ← Finset.filter_union, hu] at hc
  have h1 := Nat.Ioc_filter_dvd_card_eq_div b d
  have h2 := Nat.Ioc_filter_dvd_card_eq_div a d
  unfold erdos81727_cnt
  omega

private lemma erdos81727_hdiv (d q r : ℕ) (hd : 0 < d) (hr : r < d) :
    (d * q + r) / d = q := by
  rw [Nat.add_comm, Nat.add_mul_div_left r q hd, Nat.div_eq_of_lt hr, zero_add]

theorem erdos_81727_hyp_cnt_smooth :
    ∀ N d l : ℕ, 0 < d → d ≤ l → d ∣ N → l + 1 ≤ N →
      erdos81727_cnt d (Finset.Ioc (N - 1) (N - 1 + (l + 1))) =
          erdos81727_cnt d (Finset.Ioc (N - l - 1) (N - l - 1 + l)) + 1 ∧
        1 ≤ erdos81727_cnt d (Finset.Ioc (N - l - 1) (N - l - 1 + l)) := by
  intro N d l hd hdl hdN hN
  have hA := erdos81727_cnt_Ioc d (N - l - 1) (N - l - 1 + l) (by omega)
  have hB := erdos81727_cnt_Ioc d (N - 1) (N - 1 + (l + 1)) (by omega)
  obtain ⟨t, rfl⟩ := hdN
  have hlr : d * (l / d) + l % d = l := Nat.div_add_mod l d
  have hr : l % d < d := Nat.mod_lt l hd
  have hs1 : 0 < l / d := Nat.div_pos hdl hd
  generalize l / d = s at hlr hs1
  generalize l % d = r at hlr hr
  have hlt : d * s < d * t := by omega
  have hst : s < t := Nat.lt_of_mul_lt_mul_left hlt
  obtain ⟨w, rfl⟩ : ∃ w, t = s + 1 + w := ⟨t - s - 1, by omega⟩
  have r1 : d * (s + 1 + w) = d * s + d * w + d := by ring
  have r2 : d * (s + w) = d * s + d * w := by ring
  have r3 : d * (2 * s + 1 + w) = d * s + d * s + d * w + d := by ring
  have f1 : (d * (s + 1 + w) - 1) / d = s + w := by
    have e : d * (s + 1 + w) - 1 = d * (s + w) + (d - 1) := by omega
    rw [e]; exact erdos81727_hdiv d _ _ hd (by omega)
  have f2 : (d * (s + 1 + w) - 1 + (l + 1)) / d = 2 * s + 1 + w := by
    have e : d * (s + 1 + w) - 1 + (l + 1) = d * (2 * s + 1 + w) + r := by omega
    rw [e]; exact erdos81727_hdiv d _ _ hd hr
  have f3 : (d * (s + 1 + w) - l - 1) / d = w := by
    have e : d * (s + 1 + w) - l - 1 = d * w + (d - 1 - r) := by omega
    rw [e]; exact erdos81727_hdiv d _ _ hd (by omega)
  have f4 : (d * (s + 1 + w) - l - 1 + l) / d = s + w := by
    have e : d * (s + 1 + w) - l - 1 + l = d * (s + w) + (d - 1) := by omega
    rw [e]; exact erdos81727_hdiv d _ _ hd (by omega)
  rw [f1, f2] at hB
  rw [f3, f4] at hA
  constructor <;> omega
end erdos_81727_hyp_cnt_smooth_ns

theorem erdos_81727_hyp_cnt_smooth :
    ∀ N d l : ℕ, 0 < d → d ≤ l → d ∣ N → l + 1 ≤ N →
      erdos81727_cnt d (Finset.Ioc (N - 1) (N - 1 + (l + 1))) =
          erdos81727_cnt d (Finset.Ioc (N - l - 1) (N - l - 1 + l)) + 1 ∧
        1 ≤ erdos81727_cnt d (Finset.Ioc (N - l - 1) (N - l - 1 + l)) := by
  exact erdos_81727_hyp_cnt_smooth_ns.erdos_81727_hyp_cnt_smooth



-- Derived: if N ≡ -1 (mod q) and (l+2)/2 ≤ q ≤ l-1, then [N, N+l] contains exactly the multiples N+1 and N+1+q,
-- and [N-l, N-1] contains exactly N+1-q.
namespace erdos_81727_hyp_cnt_q_ns
open Asymptotics Filter Finset

theorem erdos_81727_hyp_cnt_q :
    ∀ N q l : ℕ, l + 2 ≤ 2 * q → 2 * q + 2 ≤ 2 * l → q ∣ N + 1 → l + 1 ≤ N →
      erdos81727_cnt q (Finset.Ioc (N - 1) (N - 1 + (l + 1))) = 2 ∧
        erdos81727_cnt q (Finset.Ioc (N - l - 1) (N - l - 1 + l)) = 1 := by
  intro N q l h1 h2 hd hN
  have hq3 : 3 ≤ q := by omega
  obtain ⟨t, ht⟩ := id hd
  constructor
  · have hS : (Finset.Ioc (N - 1) (N - 1 + (l + 1))).filter (fun x => q ∣ x)
        = {N + 1, N + 1 + q} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨hx1, hx2⟩, s, hs⟩
        have a1 : q * t < q * (s + 1) := by
          rw [mul_add, mul_one, ← hs, ← ht]; omega
        have a2 : q * s < q * (t + 2) := by
          rw [mul_add, ← hs, ← ht]; omega
        have b1 := Nat.lt_of_mul_lt_mul_left a1
        have b2 := Nat.lt_of_mul_lt_mul_left a2
        have hc : s = t ∨ s = t + 1 := by omega
        rcases hc with h | h
        · subst h; left; rw [hs, ← ht]
        · subst h; right; rw [hs, mul_add, mul_one, ← ht]
      · rintro (rfl | rfl)
        · exact ⟨⟨by omega, by omega⟩, hd⟩
        · exact ⟨⟨by omega, by omega⟩, Nat.dvd_add hd (dvd_refl q)⟩
    unfold erdos81727_cnt
    rw [hS, Finset.card_pair (by omega)]
  · have hS : (Finset.Ioc (N - l - 1) (N - l - 1 + l)).filter (fun x => q ∣ x)
        = {N + 1 - q} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨hx1, hx2⟩, s, hs⟩
        have a1 : q * t < q * (s + 2) := by
          rw [mul_add, ← hs, ← ht]; omega
        have a2 : q * s < q * t := by
          rw [← hs, ← ht]; omega
        have b1 := Nat.lt_of_mul_lt_mul_left a1
        have b2 := Nat.lt_of_mul_lt_mul_left a2
        have hst : t = s + 1 := by omega
        have hx : N + 1 = x + q := by
          rw [ht, hst, mul_add, mul_one, hs]
        omega
      · rintro rfl
        exact ⟨⟨by omega, by omega⟩, Nat.dvd_sub hd (dvd_refl q)⟩
    unfold erdos81727_cnt
    rw [hS, Finset.card_singleton]
end erdos_81727_hyp_cnt_q_ns

theorem erdos_81727_hyp_cnt_q :
    ∀ N q l : ℕ, l + 2 ≤ 2 * q → 2 * q + 2 ≤ 2 * l → q ∣ N + 1 → l + 1 ≤ N →
      erdos81727_cnt q (Finset.Ioc (N - 1) (N - 1 + (l + 1))) = 2 ∧
        erdos81727_cnt q (Finset.Ioc (N - l - 1) (N - l - 1 + l)) = 1 := by
  exact erdos_81727_hyp_cnt_q_ns.erdos_81727_hyp_cnt_q



theorem erdos_81727_size_c3 :
    ∀ k q u M : ℕ, 46 ≤ k → 3 ≤ q → q ≤ k → 1 ≤ u → u < q → 2 ^ k ≤ q * M →
      k + 1 ≤ M * u ∧
        (∏ i ∈ erdos81727_B (M * u) k, i) < q * M * (∏ i ∈ erdos81727_A (M * u) k, i) := by
  first
  | exact erdos_81727_hyp_size_ns.erdos_81727_hyp_size
  | exact erdos_81727_hyp_size

theorem erdos_81727_residue_c3 :
    ∀ k q : ℕ, erdos81727_admissible k q →
      ∃ u : ℕ, 1 ≤ u ∧ u < q ∧ q ∣ erdos81727_L k / q * u + 1 := by
  first
  | exact erdos_81727_hyp_residue_ns.erdos_81727_hyp_residue
  | exact erdos_81727_hyp_residue

theorem erdos_81727_count_glue (k q u : ℕ) (hk : 46 ≤ k) (hadm : erdos81727_admissible k q)
    (hdiv : q ∣ erdos81727_L k / q * u + 1) (hNk : k + 1 ≤ erdos81727_L k / q * u) :
    (∏ i ∈ erdos81727_B (erdos81727_L k / q * u) k, i) *
        (erdos81727_A (erdos81727_L k / q * u) k).lcm id =
      erdos81727_L k * (∏ i ∈ erdos81727_A (erdos81727_L k / q * u) k, i) *
        (erdos81727_B (erdos81727_L k / q * u) k).lcm id := by
  obtain ⟨hq, hq1, hq2⟩ := hadm
  have hqmem : q ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hqdvd : q ∣ erdos81727_L k := by
    unfold erdos81727_L
    exact Finset.dvd_lcm hqmem
  have hLq : erdos81727_L k = q * (erdos81727_L k / q) := (Nat.mul_div_cancel' hqdvd).symm
  have hL0 : erdos81727_L k ≠ 0 := by
    unfold erdos81727_L
    intro h
    rw [Finset.lcm_eq_zero_iff] at h
    simp at h <;> omega
  have hdvdN : ∀ d : ℕ, d ∣ erdos81727_L k → Nat.Coprime d q →
      d ∣ erdos81727_L k / q * u := by
    intro d hd hc
    have h1 : d ∣ q * (erdos81727_L k / q) := by rw [← hLq]; exact hd
    have h2 : d ∣ erdos81727_L k / q := by
      first
      | exact Nat.Coprime.dvd_of_dvd_mul_left hc h1
      | exact Nat.Coprime.dvd_of_dvd_mul_right hc h1
    exact Dvd.dvd.mul_right h2 u
  generalize erdos81727_L k / q * u = N at hdiv hNk hdvdN ⊢
  show (∏ i ∈ Finset.Ioc (N - 1) (N - 1 + (k + 1)), i) *
        (Finset.Ioc (N - k - 1) (N - k - 1 + k)).lcm id =
      erdos81727_L k * (∏ i ∈ Finset.Ioc (N - k - 1) (N - k - 1 + k), i) *
        (Finset.Ioc (N - 1) (N - 1 + (k + 1))).lcm id
  have hPB : (∏ i ∈ Finset.Ioc (N - 1) (N - 1 + (k + 1)), i) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro x hx
    rw [Finset.mem_Ioc] at hx
    omega
  have hPA : (∏ i ∈ Finset.Ioc (N - k - 1) (N - k - 1 + k), i) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro x hx
    rw [Finset.mem_Ioc] at hx
    omega
  have hlB : (Finset.Ioc (N - 1) (N - 1 + (k + 1))).lcm id ≠ 0 := by
    intro h
    rw [Finset.lcm_eq_zero_iff] at h
    simp at h <;> omega
  have hlA : (Finset.Ioc (N - k - 1) (N - k - 1 + k)).lcm id ≠ 0 := by
    intro h
    rw [Finset.lcm_eq_zero_iff] at h
    simp at h <;> omega
  have hX : (∏ i ∈ Finset.Ioc (N - 1) (N - 1 + (k + 1)), i) *
        (Finset.Ioc (N - k - 1) (N - k - 1 + k)).lcm id ≠ 0 := mul_ne_zero hPB hlA
  have hY : erdos81727_L k * (∏ i ∈ Finset.Ioc (N - k - 1) (N - k - 1 + k), i) *
        (Finset.Ioc (N - 1) (N - 1 + (k + 1))).lcm id ≠ 0 :=
    mul_ne_zero (mul_ne_zero hL0 hPA) hlB
  have hval : ∀ p : ℕ, p.Prime →
      padicValNat p ((∏ i ∈ Finset.Ioc (N - 1) (N - 1 + (k + 1)), i) *
        (Finset.Ioc (N - k - 1) (N - k - 1 + k)).lcm id) =
      padicValNat p (erdos81727_L k * (∏ i ∈ Finset.Ioc (N - k - 1) (N - k - 1 + k), i) *
        (Finset.Ioc (N - 1) (N - 1 + (k + 1))).lcm id) := by
    intro p hp
    haveI : Fact p.Prime := ⟨hp⟩
    rw [padicValNat.mul hPB hlA, padicValNat.mul (mul_ne_zero hL0 hPA) hlB,
      padicValNat.mul hL0 hPA]
    rw [erdos_81727_hyp_vprod p (N - 1) (k + 1) (N + k + 1) hp (by omega),
      erdos_81727_hyp_vprod p (N - k - 1) k (N + k + 1) hp (by omega),
      erdos_81727_hyp_vlcm p (N - 1) (k + 1) (N + k + 1) hp (by omega),
      erdos_81727_hyp_vlcm p (N - k - 1) k (N + k + 1) hp (by omega),
      erdos_81727_hyp_vL k p (N + k + 1) hp (by omega)]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    try beta_reduce
    have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
    have hpos : 0 < p ^ j := pow_pos hp.pos j
    by_cases hd : p ^ j ≤ k
    · by_cases hpq : p = q
      · have hjeq : j = 1 := by
          by_contra hne
          have hj2 : 2 ≤ j := by omega
          have hqq : q * q ≤ k := by
            calc q * q = q ^ 2 := (sq q).symm
              _ ≤ q ^ j := Nat.pow_le_pow_right hq.pos hj2
              _ = p ^ j := by rw [hpq]
              _ ≤ k := hd
          nlinarith [Nat.mul_le_mul hq1 hq1, Nat.zero_le (k * k)]
        have hpj : p ^ j = q := by rw [hjeq, pow_one]; exact hpq
        rw [hpj] at hd ⊢
        obtain ⟨h1, h2⟩ := erdos_81727_hyp_cnt_q N q k hq1 hq2 hdiv hNk
        split_ifs <;> omega
      · have hcop : Nat.Coprime (p ^ j) q :=
          Nat.Coprime.pow_left j ((Nat.coprime_primes hp hq).mpr hpq)
        have hmem : p ^ j ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨by omega, hd⟩
        have hdl : p ^ j ∣ erdos81727_L k := by
          unfold erdos81727_L
          exact Finset.dvd_lcm hmem
        obtain ⟨h1, h2⟩ :=
          erdos_81727_hyp_cnt_smooth N (p ^ j) k hpos hd (hdvdN _ hdl hcop) hNk
        split_ifs <;> omega
    · have h1 := erdos_81727_hyp_cnt_le_one (p ^ j) (N - 1) (k + 1) hpos (by omega)
      have h2 := erdos_81727_hyp_cnt_le_one (p ^ j) (N - k - 1) k hpos (by omega)
      split_ifs <;> omega
  first
  | exact (Nat.eq_iff_prime_padicValNat_eq _ _ hX hY).mpr hval
  | exact Nat.eq_of_factorization_eq hX hY (fun p => by
      by_cases hp : p.Prime
      · rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
        exact hval p hp
      · rw [Nat.factorization_eq_zero_of_non_prime _ hp,
          Nat.factorization_eq_zero_of_non_prime _ hp])

namespace Finset
def lcmInterval {α : Type*} [CommSemiring α] [NormalizedGCDMonoid α]
    [Preorder α] [LocallyFiniteOrder α] (n k : α) : α := (Finset.Ioc n (n + k)).lcm id
end Finset

open Asymptotics Filter Finset

theorem erdos_81727 :
    ∀ᶠ k in atTop, {(m, n) | n + k ≤ m ∧ lcmInterval m (k + 1) < lcmInterval n k}.Nonempty := by
  refine Filter.eventually_atTop.2 ⟨46, fun k hk => ?_⟩
  have hk46 : (46 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  obtain ⟨p, hp, hp1, hp2⟩ := erdos_81727_hyp_nagura ((11 / 20 : ℝ) * (k : ℝ)) (by linarith)
  have h1 : k + 2 ≤ 2 * p := by
    have h : (k : ℝ) + 2 ≤ 2 * (p : ℝ) := by linarith
    exact_mod_cast h
  have h2 : 2 * p + 2 ≤ 2 * k := by
    have h : 2 * (p : ℝ) + 2 ≤ 2 * (k : ℝ) := by linarith
    exact_mod_cast h
  have hadm : erdos81727_admissible k p := ⟨hp, h1, h2⟩
  obtain ⟨u, hu1, huq, hdiv⟩ := erdos_81727_residue_c3 k p hadm
  have hmem : p ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hqdvd : p ∣ erdos81727_L k := by
    unfold erdos81727_L
    exact Finset.dvd_lcm hmem
  have hLM : erdos81727_L k = p * (erdos81727_L k / p) := (Nat.mul_div_cancel' hqdvd).symm
  have hnair := erdos_81727_hyp_nair k (by omega)
  have h2k : 2 ^ k ≤ p * (erdos81727_L k / p) := hnair.trans_eq hLM
  obtain ⟨hN, hsize⟩ := erdos_81727_size_c3 k p u (erdos81727_L k / p) hk
    (by omega) (by omega) hu1 huq h2k
  rw [← hLM] at hsize
  have hid := erdos_81727_count_glue k p u hk hadm hdiv hN
  have hA0 : (erdos81727_A (erdos81727_L k / p * u) k).lcm id ≠ 0 := by
    unfold erdos81727_A
    intro h
    rw [Finset.lcm_eq_zero_iff] at h
    simp at h <;> omega
  have key : ∀ a b c d e : ℕ, a ≠ 0 → b * a = c * d * e → b < c * d → e < a := by
    intro a b c d e ha hb hc
    by_contra hcon
    push_neg at hcon
    have h3 : b * a < c * d * a := mul_lt_mul_of_pos_right hc (Nat.pos_of_ne_zero ha)
    have h4 : c * d * a ≤ c * d * e := Nat.mul_le_mul_left (c * d) hcon
    linarith
  have hlt := key _ _ _ _ _ hA0 hid hsize
  generalize erdos81727_L k / p * u = N at hN hlt
  refine ⟨(N - 1, N - k - 1), ?_⟩
  show N - k - 1 + k ≤ N - 1 ∧ lcmInterval (N - 1) (k + 1) < lcmInterval (N - k - 1) k
  exact ⟨by omega, hlt⟩