import Mathlib

set_option maxHeartbeats 1000000
set_option autoImplicit false

open Filter ENNReal

def Erdos455ConvexChain (p : ℕ → ℕ) (L : ℕ) : Prop :=
  (∀ i, i ≤ L → (p i).Prime) ∧ (∀ i, i < L → p i < p (i + 1)) ∧
    (∀ i, i + 2 ≤ L → p (i + 1) - p i ≤ p (i + 2) - p (i + 1))

-- Derived (elementary). Steps:
-- (i) gaps are nondecreasing, so equal gaps e form one block, i.e. a prime AP;
-- (ii) such a block has at most 2r(e)-2 gaps, where r(e) is the least prime not dividing e (pigeonhole mod r(e));
-- (iii) only d_0 can be odd;
-- (iv) sum over even e ≤ x of r(e) is less than 2.63x;
-- (v) hence i+1 ≤ M(d_i) ≤ 1 + 5.26 d_i, so i ≤ 6 d_i.
namespace erdos_455_hyp_no_short_convex_chain_hyp_gap_lower_ns
open Filter ENNReal

-- CHECK: CharP.cast_eq_zero_iff ZMod.natCast_zmod_val ZMod.val_lt inv_mul_cancel₀ Finset.card_biUnion_le
private lemma erdos455_ap_bound (c e k r : ℕ) (he : 0 < e) (hr : r.Prime) (hre : ¬ r ∣ e)
    (hp : ∀ s, s ≤ k → (c + s * e).Prime) : k + 2 ≤ 2 * r := by
  by_contra hk
  push_neg at hk
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : NeZero r := ⟨hr.ne_zero⟩
  have hr2 : 2 ≤ r := hr.two_le
  have he0 : (e : ZMod r) ≠ 0 := by
    intro h0
    exact hre ((CharP.cast_eq_zero_iff (ZMod r) r e).mp h0)
  obtain ⟨u, hu⟩ : ∃ u : ZMod r, u = -(c : ZMod r) * (e : ZMod r)⁻¹ := ⟨_, rfl⟩
  have hut : u.val < r := ZMod.val_lt u
  have hval : ((u.val : ℕ) : ZMod r) = u := by
    first
    | exact ZMod.natCast_zmod_val u
    | simp
  have hdiv : r ∣ c + u.val * e := by
    rw [← CharP.cast_eq_zero_iff (ZMod r) r, Nat.cast_add, Nat.cast_mul, hval, hu,
      mul_assoc, inv_mul_cancel₀ he0]
    ring
  have hc2 : 2 ≤ c + 0 * e := (hp 0 (Nat.zero_le _)).two_le
  rw [zero_mul, add_zero] at hc2
  have hpos : 0 < c + u.val * e := Nat.lt_of_lt_of_le (by omega : 0 < c) (Nat.le_add_right c _)
  have hle : r ≤ c + u.val * e := Nat.le_of_dvd hpos hdiv
  have hprime := hp (u.val + r) (by omega)
  have hexp : c + (u.val + r) * e = (c + u.val * e) + r * e := by ring
  have hdiv2 : r ∣ c + (u.val + r) * e := by
    rw [hexp]
    exact dvd_add hdiv (dvd_mul_right r e)
  rcases hprime.eq_one_or_self_of_dvd r hdiv2 with h1 | h1
  · omega
  · have h3 : r ≤ r * e := by nlinarith
    rw [hexp] at h1
    nlinarith

private lemma erdos455_mono (p : ℕ → ℕ) (L : ℕ) (h : Erdos455ConvexChain p L) :
    ∀ a b, a ≤ b → b < L → p (a + 1) - p a ≤ p (b + 1) - p b := by
  have hc : ∀ j, j + 2 ≤ L → p (j + 1) - p j ≤ p (j + 2) - p (j + 1) := h.2.2
  have key : ∀ a k, a + k < L → p (a + 1) - p a ≤ p (a + k + 1) - p (a + k) := by
    intro a k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have h3 := ih (by omega)
      have h2 := hc (a + k) (by omega)
      have e1 : a + (k + 1) = a + k + 1 := by omega
      have e2 : a + k + 1 + 1 = a + k + 2 := by omega
      rw [e1, e2]
      exact le_trans h3 h2
  intro a b hab hb
  have := key a (b - a) (by omega)
  have e3 : a + (b - a) = b := by omega
  rw [e3] at this
  exact this

private lemma erdos455_prim_ge (n : ℕ) : n * n ≤ 2 * primorial n + n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n ≤ 9
    · interval_cases n <;> decide
    · push_neg at hn
      obtain ⟨m, hm⟩ : ∃ m, m = n / 2 := ⟨_, rfl⟩
      have hm5 : 5 ≤ m := by omega
      have hmn : m < n := by omega
      have hIH := ih m hmn
      obtain ⟨q, hq, hmq, hq2⟩ := Nat.exists_prime_lt_and_le_two_mul m (by omega)
      have hsplit := primorial_add m (n - m)
      rw [show m + (n - m) = n by omega] at hsplit
      have hmem : q ∈ (Finset.Ico (m + 1) (n + 1)).filter Nat.Prime := by
        rw [Finset.mem_filter, Finset.mem_Ico]
        exact ⟨⟨by omega, by omega⟩, hq⟩
      have hpos : 0 < ∏ p ∈ (Finset.Ico (m + 1) (n + 1)).filter Nat.Prime, p :=
        Finset.prod_pos (fun p hp => (Finset.mem_filter.mp hp).2.pos)
      have hqle : q ≤ ∏ p ∈ (Finset.Ico (m + 1) (n + 1)).filter Nat.Prime, p :=
        Nat.le_of_dvd hpos (Finset.dvd_prod_of_mem _ hmem)
      have hge : primorial m * (m + 1) ≤ primorial n := by
        rw [hsplit]
        exact Nat.mul_le_mul_left _ ((Nat.succ_le_of_lt hmq).trans hqle)
      have hn2 : n ≤ 2 * m + 1 := by omega
      have h1 : n * n ≤ (2 * m + 1) * (2 * m + 1) := Nat.mul_le_mul hn2 hn2
      have h2 : (m * m) * (m + 1) ≤ (2 * primorial m + m) * (m + 1) := Nat.mul_le_mul_right _ hIH
      have h3 : 2 * (primorial m * (m + 1)) ≤ 2 * primorial n := by omega
      nlinarith

private lemma erdos455_recip (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / primorial n ≤ 3 - 2 / N := by
  induction N with
  | zero => omega
  | succ N ih =>
    rcases Nat.eq_zero_or_pos N with rfl | hN0
    · norm_num
    · rw [Finset.sum_Icc_succ_top (by omega)]
      have h := ih hN0
      have hp := erdos455_prim_ge (N + 1)
      have hP : (0 : ℝ) < primorial (N + 1) := by exact_mod_cast primorial_pos _
      have hpR : ((N : ℝ) + 1) * ((N : ℝ) + 1) ≤ 2 * (primorial (N + 1) : ℝ) + ((N : ℝ) + 1) := by
        exact_mod_cast hp
      have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
      have key : (1 : ℝ) / primorial (N + 1) ≤ 2 / N - 2 / ((N : ℝ) + 1) := by
        rw [div_sub_div _ _ hNR.ne' (by positivity), div_le_div_iff₀ hP (by positivity)]
        nlinarith
      push_cast
      linarith

private lemma erdos455_tail (x : ℕ) :
    ∑ n ∈ Finset.Icc 1 x, x / primorial n ≤ 3 * x := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  have h := erdos455_recip x hx
  have hxR : (0 : ℝ) ≤ x := by positivity
  have hc : ((∑ n ∈ Finset.Icc 1 x, x / primorial n : ℕ) : ℝ) ≤ 3 * x := by
    push_cast
    calc ∑ n ∈ Finset.Icc 1 x, ((x / primorial n : ℕ) : ℝ)
        ≤ ∑ n ∈ Finset.Icc 1 x, (x : ℝ) * (1 / primorial n) := by
          apply Finset.sum_le_sum
          intro n _
          rw [mul_one_div]
          exact Nat.cast_div_le
      _ = (x : ℝ) * ∑ n ∈ Finset.Icc 1 x, (1 : ℝ) / primorial n := by rw [Finset.mul_sum]
      _ ≤ (x : ℝ) * 3 := by
          apply mul_le_mul_of_nonneg_left _ hxR
          have : (0 : ℝ) ≤ 2 / x := by positivity
          linarith
      _ = 3 * x := by ring
  exact_mod_cast hc

private lemma erdos455_point (m : ℕ → ℕ)
    (hm : ∀ e, 0 < e → ∀ r, r.Prime → ¬ r ∣ e → m e + 2 ≤ 2 * r) (x e : ℕ)
    (he1 : 1 ≤ e) (hex : e ≤ x) :
    m e ≤ 2 * ((Finset.Icc 1 x).filter (fun n => primorial n ∣ e)).card := by
  have hq : (Nat.minFac (e + 1)).Prime := Nat.minFac_prime (by omega)
  have hw : (Nat.minFac (e + 1)).Prime ∧ ¬ Nat.minFac (e + 1) ∣ e := by
    refine ⟨hq, ?_⟩
    intro hd
    have h1 : Nat.minFac (e + 1) ∣ (e + 1) - e := by
      first
      | exact Nat.dvd_sub' (Nat.minFac_dvd _) hd
      | exact Nat.dvd_sub (Nat.minFac_dvd _) hd
    rw [Nat.add_sub_cancel_left] at h1
    have h3 := Nat.le_of_dvd one_pos h1
    have h2 := hq.one_lt
    omega
  have hex' : ∃ r, r.Prime ∧ ¬ r ∣ e := ⟨_, hw⟩
  obtain ⟨F, hFdef⟩ : ∃ F, F = Nat.find hex' := ⟨_, rfl⟩
  have hF : F.Prime ∧ ¬ F ∣ e := by rw [hFdef]; exact Nat.find_spec hex'
  have hmin : ∀ q, q < F → ¬ (q.Prime ∧ ¬ q ∣ e) := by
    intro q hq'
    rw [hFdef] at hq'
    exact Nat.find_min hex' hq'
  have hFle' : F ≤ Nat.minFac (e + 1) := by rw [hFdef]; exact Nat.find_min' hex' hw
  have hmf : Nat.minFac (e + 1) ≤ e + 1 := Nat.minFac_le (by omega)
  have hF2 := hF.1.two_le
  have hsub : Finset.Icc 1 (F - 1) ⊆ (Finset.Icc 1 x).filter (fun n => primorial n ∣ e) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨hn.1, by omega⟩, ?_⟩
    unfold primorial
    apply Finset.prod_primes_dvd
    · intro a ha
      rw [Finset.mem_filter] at ha
      exact ha.2.prime
    · intro a ha
      rw [Finset.mem_filter, Finset.mem_range] at ha
      have := hmin a (by omega)
      by_contra hna
      exact this ⟨ha.2, hna⟩
  have hc := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hc
  have := hm e (by omega) F hF.1 hF.2
  omega

private lemma erdos455_sum_bound (m : ℕ → ℕ)
    (hm : ∀ e, 0 < e → ∀ r, r.Prime → ¬ r ∣ e → m e + 2 ≤ 2 * r) (x : ℕ) :
    ∑ e ∈ Finset.Icc 1 x, m e ≤ 6 * x := by
  have h1 : ∀ e ∈ Finset.Icc 1 x,
      m e ≤ 2 * ((Finset.Icc 1 x).filter (fun n => primorial n ∣ e)).card := by
    intro e he
    rw [Finset.mem_Icc] at he
    exact erdos455_point m hm x e he.1 he.2
  have h2 : ∑ e ∈ Finset.Icc 1 x, ((Finset.Icc 1 x).filter (fun n => primorial n ∣ e)).card
      = ∑ n ∈ Finset.Icc 1 x, ((Finset.Icc 1 x).filter (fun e => primorial n ∣ e)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have h3 : ∀ n, ((Finset.Icc 1 x).filter (fun e => primorial n ∣ e)).card
      = x / primorial n := by
    intro n
    have hI : Finset.Icc 1 x = Finset.Ioc 0 x := by
      ext y
      simp only [Finset.mem_Icc, Finset.mem_Ioc]
      omega
    rw [hI]
    exact Nat.Ioc_filter_dvd_card_eq_div x (primorial n)
  have h4 := erdos455_tail x
  calc ∑ e ∈ Finset.Icc 1 x, m e
      ≤ ∑ e ∈ Finset.Icc 1 x,
          2 * ((Finset.Icc 1 x).filter (fun n => primorial n ∣ e)).card :=
        Finset.sum_le_sum h1
    _ = 2 * ∑ e ∈ Finset.Icc 1 x,
          ((Finset.Icc 1 x).filter (fun n => primorial n ∣ e)).card := by
        rw [Finset.mul_sum]
    _ = 2 * ∑ n ∈ Finset.Icc 1 x, x / primorial n := by
        rw [h2]
        simp only [h3]
    _ ≤ 6 * x := by omega

theorem erdos_455_hyp_no_short_convex_chain_hyp_gap_lower :
    ∀ L : ℕ, ∀ p : ℕ → ℕ, Erdos455ConvexChain p L →
      ∀ i, i < L → i ≤ 6 * (p (i + 1) - p i) := by
  intro L p h i hi
  have hprime : ∀ j, j ≤ L → (p j).Prime := h.1
  have hlt : ∀ j, j < L → p j < p (j + 1) := h.2.1
  have hmono : ∀ a b, a ≤ b → b < L → p (a + 1) - p a ≤ p (b + 1) - p b :=
    erdos455_mono p L h
  have hfib : ∀ e, 0 < e → ∀ r, r.Prime → ¬ r ∣ e →
      ((Finset.range (i + 1)).filter (fun j => p (j + 1) - p j = e)).card + 2 ≤ 2 * r := by
    intro e he r hr hre
    obtain ⟨S, hS⟩ : ∃ S, S = (Finset.range (i + 1)).filter (fun j => p (j + 1) - p j = e) :=
      ⟨_, rfl⟩
    rw [← hS]
    have hr2 := hr.two_le
    rcases S.eq_empty_or_nonempty with hemp | hne
    · rw [hemp, Finset.card_empty]; omega
    · have hpos := Finset.card_pos.mpr hne
      have haS : S.min' hne ∈ S := Finset.min'_mem S hne
      have hbS : S.max' hne ∈ S := Finset.max'_mem S hne
      have hsubI : S ⊆ Finset.Icc (S.min' hne) (S.max' hne) := by
        intro j hj
        rw [Finset.mem_Icc]
        exact ⟨Finset.min'_le S j hj, Finset.le_max' S j hj⟩
      have hcS := Finset.card_le_card hsubI
      rw [Nat.card_Icc] at hcS
      obtain ⟨a, ha⟩ : ∃ a, a = S.min' hne := ⟨_, rfl⟩
      obtain ⟨b, hb⟩ : ∃ b, b = S.max' hne := ⟨_, rfl⟩
      rw [← ha] at haS hcS
      rw [← hb] at hbS hcS
      rw [hS, Finset.mem_filter, Finset.mem_range] at haS hbS
      have hab : a ≤ b := by omega
      have hconst : ∀ j, a ≤ j → j ≤ b → p (j + 1) - p j = e := by
        intro j hj1 hj2
        have h1 := hmono a j hj1 (by omega)
        have h2 := hmono j b hj2 (by omega)
        omega
      have hap : ∀ s, s ≤ b - a + 1 → p (a + s) = p a + s * e := by
        intro s
        induction s with
        | zero => intro _; simp
        | succ s ih =>
          intro hs
          have h1 := ih (by omega)
          have hd := hconst (a + s) (by omega) (by omega)
          have hl := hlt (a + s) (by omega)
          have e1 : a + (s + 1) = a + s + 1 := by omega
          rw [e1, add_mul, one_mul]
          generalize s * e = w at h1 ⊢
          omega
      have hbound := erdos455_ap_bound (p a) e (b - a + 1) r he hr hre (by
        intro s hs
        rw [← hap s hs]
        exact hprime (a + s) (by omega))
      omega
  have hsub : Finset.range (i + 1) ⊆ (Finset.Icc 1 (p (i + 1) - p i)).biUnion
      (fun e => (Finset.range (i + 1)).filter (fun j => p (j + 1) - p j = e)) := by
    intro j hj
    have hj' : j < i + 1 := Finset.mem_range.mp hj
    rw [Finset.mem_biUnion]
    refine ⟨p (j + 1) - p j, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      constructor
      · have := hlt j (by omega); omega
      · exact hmono j i (by omega) hi
    · exact Finset.mem_filter.mpr ⟨hj, rfl⟩
  have h2 : (Finset.range (i + 1)).card ≤ ∑ e ∈ Finset.Icc 1 (p (i + 1) - p i),
      ((Finset.range (i + 1)).filter (fun j => p (j + 1) - p j = e)).card :=
    le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
  have hsum : ∑ e ∈ Finset.Icc 1 (p (i + 1) - p i),
      ((Finset.range (i + 1)).filter (fun j => p (j + 1) - p j = e)).card
        ≤ 6 * (p (i + 1) - p i) := erdos455_sum_bound _ hfib _
  rw [Finset.card_range] at h2
  omega
end erdos_455_hyp_no_short_convex_chain_hyp_gap_lower_ns

theorem erdos_455_hyp_no_short_convex_chain_hyp_gap_lower :
    ∀ L : ℕ, ∀ p : ℕ → ℕ, Erdos455ConvexChain p L →
      ∀ i, i < L → i ≤ 6 * (p (i + 1) - p i) := by
  exact erdos_455_hyp_no_short_convex_chain_hyp_gap_lower_ns.erdos_455_hyp_no_short_convex_chain_hyp_gap_lower

#print axioms erdos_455_hyp_no_short_convex_chain_hyp_gap_lower
