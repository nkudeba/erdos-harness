import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.Primorial

set_option maxHeartbeats 1000000
set_option autoImplicit false

def ePset (K : ℕ) : Finset ℕ := (Finset.Ioc K (6 * K)).filter Nat.Prime

def erdosG (h : ℕ) (P : Finset ℕ) (m : ℤ) : Prop :=
  ∀ p ∈ P, ∃ d : ℤ, |d| ≤ (h : ℤ) - 1 ∧ (p : ℤ) ∣ m - d

-- Certified verbatim (hyp-0, namespace erdos_95799_hyp_cheb_ns), restated with Pset renamed ePset.
namespace erdos_95799_hyp_cheb_ns
theorem erdos_95799_hyp_cheb :
    ∀ K : ℕ, Real.exp 100 ≤ (K : ℝ) → (((ePset K).card : ℕ) : ℝ) ≤ (K : ℝ) / 5 := by
  intro K hK
  have hKpos : (0:ℝ) < K := lt_of_lt_of_le (Real.exp_pos 100) hK
  have hlogK : (100:ℝ) ≤ Real.log K := by
    have := Real.log_le_log (Real.exp_pos 100) hK
    rwa [Real.log_exp] at this
  have hlog4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 4)
    linarith
  have hsub : ePset K ⊆ Finset.filter Nat.Prime (Finset.range (6 * K + 1)) := by
    intro p hp
    simp only [ePset, Finset.mem_filter, Finset.mem_Ioc] at hp
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hp.2⟩
  have h1 : K ^ (ePset K).card ≤ ∏ p ∈ ePset K, p := by
    calc K ^ (ePset K).card = ∏ _p ∈ ePset K, K := (Finset.prod_const K).symm
      _ ≤ ∏ p ∈ ePset K, p := by
        apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
        intro p hp
        simp only [ePset, Finset.mem_filter, Finset.mem_Ioc] at hp
        omega
  have h2 : ∏ p ∈ ePset K, p ≤ primorial (6 * K) := by
    unfold primorial
    apply Finset.prod_le_prod_of_subset_of_one_le' hsub
    intro i hi _
    simp only [Finset.mem_filter] at hi
    exact hi.2.one_lt.le
  have h3 : K ^ (ePset K).card ≤ 4 ^ (6 * K) :=
    le_trans h1 (le_trans h2 (primorial_le_4_pow _))
  have h4 : (K:ℝ) ^ (ePset K).card ≤ (4:ℝ) ^ (6 * K) := by exact_mod_cast h3
  have h5 := Real.log_le_log (pow_pos hKpos _) h4
  rw [Real.log_pow, Real.log_pow] at h5
  push_cast at h5
  have hc : (0:ℝ) ≤ ((ePset K).card : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hlogK hc, mul_le_mul_of_nonneg_left hlog4 hKpos.le]
end erdos_95799_hyp_cheb_ns

theorem erdos_95799_hyp_cheb :
    ∀ K : ℕ, Real.exp 100 ≤ (K : ℝ) → (((ePset K).card : ℕ) : ℝ) ≤ (K : ℝ) / 5 := by
  exact erdos_95799_hyp_cheb_ns.erdos_95799_hyp_cheb



-- Certified verbatim (hyp-1, namespace erdos_95799_hyp_param_ns), restated with Pset renamed ePset.
namespace erdos_95799_hyp_param_ns
theorem erdos_95799_hyp_param :
    ∀ K : ℕ, Real.exp 100 ≤ (K : ℝ) → (((ePset K).card : ℕ) : ℝ) ≤ (K : ℝ) / 5 →
      2 * (((⌈Real.exp (K : ℝ)⌉₊ + (K + 1) / 2 : ℕ)) : ℝ) - 1 <
        ((⌊Real.exp (2 * (K : ℝ))⌋₊ : ℕ) : ℝ) *
          ∏ p ∈ ePset K, (((((K + 1) / 2 : ℕ)) : ℝ) / (p : ℝ)) := by
  intro K hK hcard
  have h100 : (101:ℝ) ≤ (K:ℝ) := by
    have := Real.add_one_le_exp (100:ℝ); linarith
  have hK1 : 1 ≤ K := by
    have : (1:ℝ) ≤ K := by linarith
    exact_mod_cast this
  set h := (K + 1) / 2 with hh
  have h2h : K ≤ 2 * h := by omega
  have hhK : h ≤ K := by omega
  have h2hR : (K:ℝ) ≤ 2 * (h:ℝ) := by exact_mod_cast h2h
  have hhKR : (h:ℝ) ≤ K := by exact_mod_cast hhK
  have hfac : ∀ p ∈ ePset K, (1/12:ℝ) ≤ (h:ℝ) / (p:ℝ) := by
    intro p hp
    simp only [ePset, Finset.mem_filter, Finset.mem_Ioc] at hp
    have hp1 : (K:ℝ) < p := by exact_mod_cast hp.1.1
    have hp2 : (p:ℝ) ≤ 6 * K := by exact_mod_cast hp.1.2
    have hp0 : (0:ℝ) < p := by linarith
    rw [le_div_iff₀ hp0]; linarith
  have hprod : (1/12:ℝ) ^ (ePset K).card ≤ ∏ p ∈ ePset K, ((h:ℝ) / (p:ℝ)) := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => by norm_num) hfac
  have he1 : (2:ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1:ℝ); linarith
  have he4 : (12:ℝ) ≤ Real.exp 4 := by
    have h4 : Real.exp 4 = Real.exp 1 ^ 4 := by
      rw [← Real.exp_nat_mul]; norm_num
    have h16 : (2:ℝ) ^ 4 ≤ Real.exp 1 ^ 4 := by gcongr
    rw [h4]; nlinarith
  have hpow : (12:ℝ) ^ (ePset K).card ≤ Real.exp (4 * (K:ℝ) / 5) := by
    calc (12:ℝ) ^ (ePset K).card ≤ Real.exp 4 ^ (ePset K).card := by gcongr
      _ = Real.exp (((ePset K).card : ℝ) * 4) := by rw [Real.exp_nat_mul]
      _ ≤ Real.exp (4 * (K:ℝ) / 5) := by
          apply Real.exp_le_exp.mpr; linarith
  have hprodlow : Real.exp (-(4 * (K:ℝ) / 5)) ≤ ∏ p ∈ ePset K, ((h:ℝ) / (p:ℝ)) := by
    calc Real.exp (-(4 * (K:ℝ) / 5)) = 1 / Real.exp (4 * (K:ℝ) / 5) := by
          rw [Real.exp_neg]; ring
      _ ≤ 1 / (12:ℝ) ^ (ePset K).card := by gcongr
      _ = (1/12:ℝ) ^ (ePset K).card := by rw [one_div_pow]
      _ ≤ _ := hprod
  have hceil : ((⌈Real.exp (K:ℝ)⌉₊ : ℕ) : ℝ) < Real.exp K + 1 :=
    Nat.ceil_lt_add_one (Real.exp_pos _).le
  have hfloor : Real.exp (2 * (K:ℝ)) - 1 < ((⌊Real.exp (2 * (K:ℝ))⌋₊ : ℕ) : ℝ) :=
    Nat.sub_one_lt_floor _
  have hexpK : (K:ℝ) + 1 ≤ Real.exp K := Real.add_one_le_exp _
  have hexp5 : (10:ℝ) ≤ Real.exp ((K:ℝ) / 5) := by
    have := Real.add_one_le_exp ((K:ℝ) / 5); linarith
  have hsplit : Real.exp (2 * (K:ℝ)) * Real.exp (-(4 * (K:ℝ) / 5))
      = Real.exp K * Real.exp ((K:ℝ) / 5) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hfl0 : (0:ℝ) ≤ ((⌊Real.exp (2 * (K:ℝ))⌋₊ : ℕ) : ℝ) := Nat.cast_nonneg _
  have key : (Real.exp (2 * (K:ℝ)) - 1) * Real.exp (-(4 * (K:ℝ) / 5))
      ≤ ((⌊Real.exp (2 * (K:ℝ))⌋₊ : ℕ) : ℝ) * ∏ p ∈ ePset K, ((h:ℝ) / (p:ℝ)) :=
    mul_le_mul hfloor.le hprodlow (Real.exp_pos _).le hfl0
  have hsmall : Real.exp (-(4 * (K:ℝ) / 5)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  have hm : 10 * Real.exp K ≤ Real.exp K * Real.exp ((K:ℝ) / 5) := by
    nlinarith [Real.exp_pos (K:ℝ)]
  have hexpand : (Real.exp (2 * (K:ℝ)) - 1) * Real.exp (-(4 * (K:ℝ) / 5))
      = Real.exp (2 * (K:ℝ)) * Real.exp (-(4 * (K:ℝ) / 5)) - Real.exp (-(4 * (K:ℝ) / 5)) := by
    ring
  have hcast : (((⌈Real.exp (K:ℝ)⌉₊ + h : ℕ)) : ℝ)
      = ((⌈Real.exp (K:ℝ)⌉₊ : ℕ) : ℝ) + (h:ℝ) := by push_cast; ring
  rw [hcast]
  linarith
end erdos_95799_hyp_param_ns

theorem erdos_95799_hyp_param :
    ∀ K : ℕ, Real.exp 100 ≤ (K : ℝ) → (((ePset K).card : ℕ) : ℝ) ≤ (K : ℝ) / 5 →
      2 * (((⌈Real.exp (K : ℝ)⌉₊ + (K + 1) / 2 : ℕ)) : ℝ) - 1 <
        ((⌊Real.exp (2 * (K : ℝ))⌋₊ : ℕ) : ℝ) *
          ∏ p ∈ ePset K, (((((K + 1) / 2 : ℕ)) : ℝ) / (p : ℝ)) := by
  exact erdos_95799_hyp_param_ns.erdos_95799_hyp_param



-- Blueprint S1-S5: Fejér kernel positivity + orthogonality give
-- #(G ∩ (-L,L)) ≥ L ∏ (h/p); G is symmetric, so G ∩ [T,L) is nonempty once 2T-1 < L ∏ (h/p).
namespace erdos_95799_hyp_count_ns
noncomputable def ee95799 (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))

def S11Prop95799 : Prop :=
  (∀ a b : ℝ, ee95799 a * ee95799 b = ee95799 (a + b)) ∧ ee95799 0 = 1 ∧
  (∀ a : ℝ, (starRingEnd ℂ) (ee95799 a) = ee95799 (-a)) ∧
  (∀ (n : ℕ) (θ : ℝ), ee95799 ((n : ℝ) * θ) = ee95799 θ ^ n)

def S12Prop95799 : Prop :=
  ∀ L : ℕ, 1 ≤ L → ∀ θ : ℝ,
    (((‖∑ k ∈ Finset.range L, ee95799 ((k : ℝ) * θ)‖ ^ 2 : ℝ)) : ℂ) =
      ∑ k ∈ Finset.range L, ∑ k' ∈ Finset.range L,
        ee95799 ((((k : ℤ) - (k' : ℤ) : ℤ) : ℝ) * θ)

def S14Prop95799 : Prop :=
  ∀ L : ℕ, 1 ≤ L → ∀ m : ℤ, |m| < (L : ℤ) →
    ((((Finset.range L ×ˢ Finset.range L).filter
        (fun q : ℕ × ℕ => (q.1 : ℤ) - (q.2 : ℤ) = m)).card : ℕ) : ℤ) = (L : ℤ) - |m|

def S15Prop95799 : Prop :=
  ∀ L : ℕ, 1 ≤ L → ∀ g : ℤ → ℂ,
    ∑ k ∈ Finset.range L, ∑ k' ∈ Finset.range L, g ((k : ℤ) - (k' : ℤ)) =
      ∑ m ∈ Finset.Ioo (-(L : ℤ)) (L : ℤ), ((((L : ℤ) - |m| : ℤ)) : ℂ) * g m

noncomputable def fejerSum95799 (L : ℕ) (θ : ℝ) : ℂ :=
  ∑ m ∈ Finset.Ioo (-(L : ℤ)) (L : ℤ),
    (((1 - |(m : ℝ)| / (L : ℝ)) : ℝ) : ℂ) * ee95799 ((m : ℝ) * θ)

def S16Prop95799 : Prop :=
  ∀ L : ℕ, 1 ≤ L → ∀ θ : ℝ,
    (∃ r : ℝ, 0 ≤ r ∧ fejerSum95799 L θ = (r : ℂ)) ∧ fejerSum95799 L 0 = (L : ℂ)

def cdist95799 (p : ℕ) (m : ℤ) : ℤ := min (m % (p : ℤ)) ((p : ℤ) - m % (p : ℤ))

noncomputable def gw95799 (h p : ℕ) (m : ℤ) : ℝ := max 0 ((h : ℝ) - (cdist95799 p m : ℝ))

noncomputable def Fsum95799 (h L : ℕ) (P : Finset ℕ) : ℝ :=
  ∑ m ∈ Finset.Ioo (-(L : ℤ)) (L : ℤ),
    (1 - |(m : ℝ)| / (L : ℝ)) * ∏ p ∈ P, (gw95799 h p m / (h : ℝ))

-- S1.1: exp(2πi·) is a character (Complex.exp_add, Complex.exp_conj, induction)
namespace erdos_95799_hyp_count_hyp_char_ns

theorem erdos_95799_hyp_count_hyp_char : S11Prop95799 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b
    simp only [ee95799]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  · simp [ee95799]
  · intro a
    simp only [ee95799]
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    push_cast
    ring
  · intro n θ
    simp only [ee95799]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring

end erdos_95799_hyp_count_hyp_char_ns

theorem erdos_95799_hyp_count_hyp_char : S11Prop95799 := by
  exact erdos_95799_hyp_count_hyp_char_ns.erdos_95799_hyp_count_hyp_char

-- S1.2: |A|^2 = A * conj A, expanded with Finset.sum_mul_sum and S1.1
namespace erdos_95799_hyp_count_hyp_square_ns

theorem erdos_95799_hyp_count_hyp_square : S11Prop95799 → S12Prop95799 := by
  rintro ⟨hmul, _h0, hconj, _hpow⟩
  intro L _ θ
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k' _
  rw [hconj, hmul]
  congr 1
  push_cast
  ring

end erdos_95799_hyp_count_hyp_square_ns

theorem erdos_95799_hyp_count_hyp_square : S11Prop95799 → S12Prop95799 := by
  exact erdos_95799_hyp_count_hyp_square_ns.erdos_95799_hyp_count_hyp_square

-- S1.3 + S1.4: fibre of (k,k') ↦ k - k' over m has L - |m| elements (bijection, omega)
namespace erdos_95799_hyp_count_hyp_fiber_ns

private lemma fiber_pos95799 (L j : ℕ) (hj : j < L) :
    ((Finset.range L ×ˢ Finset.range L).filter
        (fun q : ℕ × ℕ => (q.1 : ℤ) - (q.2 : ℤ) = (j : ℤ))) =
      (Finset.range (L - j)).image (fun b => (b + j, b)) := by
  ext ⟨a, b⟩
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_image,
    Prod.mk.injEq]
  constructor
  · rintro ⟨⟨ha, hb⟩, h⟩
    exact ⟨b, by omega, by omega, rfl⟩
  · rintro ⟨c, hc, h1, h2⟩
    refine ⟨⟨by omega, by omega⟩, by omega⟩

private lemma fiber_neg95799 (L j : ℕ) (hj : j < L) :
    ((Finset.range L ×ˢ Finset.range L).filter
        (fun q : ℕ × ℕ => (q.1 : ℤ) - (q.2 : ℤ) = -(j : ℤ))) =
      (Finset.range (L - j)).image (fun a => (a, a + j)) := by
  ext ⟨a, b⟩
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_image,
    Prod.mk.injEq]
  constructor
  · rintro ⟨⟨ha, hb⟩, h⟩
    exact ⟨a, by omega, rfl, by omega⟩
  · rintro ⟨c, hc, h1, h2⟩
    refine ⟨⟨by omega, by omega⟩, by omega⟩

theorem erdos_95799_hyp_count_hyp_fiber : S14Prop95799 := by
  intro L hL m hm
  rcases (show 0 ≤ m ∨ m < 0 by omega) with h | h
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = (j : ℤ) := ⟨m.toNat, by omega⟩
    have habs : |(j : ℤ)| = (j : ℤ) := abs_of_nonneg (Int.natCast_nonneg j)
    rw [habs] at hm ⊢
    have hjL : j < L := by omega
    have hinj : Function.Injective (fun b : ℕ => (b + j, b)) := by
      intro x y hxy
      have := congrArg Prod.snd hxy
      simpa using this
    rw [fiber_pos95799 L j hjL, Finset.card_image_of_injective _ hinj, Finset.card_range]
    omega
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = -(j : ℤ) := ⟨(-m).toNat, by omega⟩
    have habs : |(-(j : ℤ))| = (j : ℤ) := by
      rw [abs_neg]; exact abs_of_nonneg (Int.natCast_nonneg j)
    rw [habs] at hm ⊢
    have hjL : j < L := by omega
    have hinj : Function.Injective (fun a : ℕ => (a, a + j)) := by
      intro x y hxy
      have := congrArg Prod.fst hxy
      simpa using this
    rw [fiber_neg95799 L j hjL, Finset.card_image_of_injective _ hinj, Finset.card_range]
    omega

end erdos_95799_hyp_count_hyp_fiber_ns

theorem erdos_95799_hyp_count_hyp_fiber : S14Prop95799 := by
  exact erdos_95799_hyp_count_hyp_fiber_ns.erdos_95799_hyp_count_hyp_fiber

-- S1.5: regroup the double sum by difference (Finset.sum_fiberwise_of_maps_to + S1.4)
namespace erdos_95799_hyp_count_hyp_regroup_ns

theorem erdos_95799_hyp_count_hyp_regroup : S14Prop95799 → S15Prop95799 := by
  intro h14 L hL g
  have h1 : ∑ k ∈ Finset.range L, ∑ k' ∈ Finset.range L, g ((k : ℤ) - (k' : ℤ)) =
      ∑ q ∈ Finset.range L ×ˢ Finset.range L, g ((q.1 : ℤ) - (q.2 : ℤ)) :=
    (Finset.sum_product' (Finset.range L) (Finset.range L)
      (fun (a b : ℕ) => g ((a : ℤ) - (b : ℤ)))).symm
  have hmaps : ∀ q ∈ Finset.range L ×ˢ Finset.range L,
      (q.1 : ℤ) - (q.2 : ℤ) ∈ Finset.Ioo (-(L : ℤ)) (L : ℤ) := by
    intro q hq
    simp only [Finset.mem_product, Finset.mem_range] at hq
    simp only [Finset.mem_Ioo]
    constructor <;> omega
  rw [h1, ← Finset.sum_fiberwise_of_maps_to hmaps
    (fun q : ℕ × ℕ => g ((q.1 : ℤ) - (q.2 : ℤ)))]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  have hab : |m| < (L : ℤ) := by
    rw [Finset.mem_Ioo] at hm
    rw [abs_lt]
    exact hm
  have hc := h14 L hL m hab
  have hfib : ∀ q ∈ (Finset.range L ×ˢ Finset.range L).filter
      (fun q : ℕ × ℕ => (q.1 : ℤ) - (q.2 : ℤ) = m),
      g ((q.1 : ℤ) - (q.2 : ℤ)) = g m := by
    intro q hq
    rw [Finset.mem_filter] at hq
    rw [hq.2]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, nsmul_eq_mul, ← hc]
  push_cast
  rfl

end erdos_95799_hyp_count_hyp_regroup_ns

theorem erdos_95799_hyp_count_hyp_regroup : S14Prop95799 → S15Prop95799 := by
  exact erdos_95799_hyp_count_hyp_regroup_ns.erdos_95799_hyp_count_hyp_regroup

-- S1.6: Fejer identity = (1/L)|A|^2 ≥ 0, value L at θ = 0 (from S1.2, S1.5)
namespace erdos_95799_hyp_count_hyp_fejer_ns

private lemma key95799 (h15 : S15Prop95799) (L : ℕ) (hL : 1 ≤ L) (θ : ℝ) :
    ∑ k ∈ Finset.range L, ∑ k' ∈ Finset.range L,
        ee95799 ((((k : ℤ) - (k' : ℤ) : ℤ) : ℝ) * θ) = (L : ℂ) * fejerSum95799 L θ := by
  have h : ∑ k ∈ Finset.range L, ∑ k' ∈ Finset.range L,
        ee95799 ((((k : ℤ) - (k' : ℤ) : ℤ) : ℝ) * θ) =
      ∑ m ∈ Finset.Ioo (-(L : ℤ)) (L : ℤ), ((((L : ℤ) - |m| : ℤ)) : ℂ) * ee95799 ((m : ℝ) * θ) :=
    h15 L hL (fun m : ℤ => ee95799 ((m : ℝ) * θ))
  rw [h, fejerSum95799, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [← mul_assoc]
  congr 1
  have hL0 : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h2 : (L : ℝ) * (|(m : ℝ)| / L) = |(m : ℝ)| := by field_simp
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_intCast,
    Complex.ofReal_inj, mul_sub, mul_one, h2, Int.cast_sub, Int.cast_abs, Int.cast_natCast]

theorem erdos_95799_hyp_count_hyp_fejer : S12Prop95799 → S15Prop95799 → S16Prop95799 := by
  intro h12 h15 L hL θ
  have hL0 : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  refine ⟨⟨‖∑ k ∈ Finset.range L, ee95799 ((k : ℝ) * θ)‖ ^ 2 / L, by positivity, ?_⟩, ?_⟩
  · have hk := key95799 h15 L hL θ
    rw [← h12 L hL θ] at hk
    rw [Complex.ofReal_div, Complex.ofReal_natCast, hk]
    field_simp
  · have hk := key95799 h15 L hL 0
    have he : ee95799 0 = 1 := by simp [ee95799]
    simp only [mul_zero, he, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one] at hk
    exact (mul_left_cancel₀ hL0 hk).symm

end erdos_95799_hyp_count_hyp_fejer_ns

theorem erdos_95799_hyp_count_hyp_fejer : S12Prop95799 → S15Prop95799 → S16Prop95799 := by
  exact erdos_95799_hyp_count_hyp_fejer_ns.erdos_95799_hyp_count_hyp_fejer

-- C1 steps (1)-(3): g_p = 1_J * 1_{-J} has no wraparound since p ≥ 2h, so its transform is ≥ 0;
-- the CRT product has transform ≥ 0 with mean ∏ h/p; pairing with the Fejer kernel (S1.6) gives S ≥ L ∏ h/p.
namespace erdos_95799_hyp_count_hyp_lower_ns
noncomputable def ee95799 (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))

def S11Prop95799 : Prop :=
  (∀ a b : ℝ, ee95799 a * ee95799 b = ee95799 (a + b)) ∧ ee95799 0 = 1 ∧
  (∀ a : ℝ, (starRingEnd ℂ) (ee95799 a) = ee95799 (-a)) ∧
  (∀ (n : ℕ) (θ : ℝ), ee95799 ((n : ℝ) * θ) = ee95799 θ ^ n)

def S12Prop95799 : Prop :=
  ∀ L : ℕ, 1 ≤ L → ∀ θ : ℝ,
    (((‖∑ k ∈ Finset.range L, ee95799 ((k : ℝ) * θ)‖ ^ 2 : ℝ)) : ℂ) =
      ∑ k ∈ Finset.range L, ∑ k' ∈ Finset.range L,
        ee95799 ((((k : ℤ) - (k' : ℤ) : ℤ) : ℝ) * θ)

def S14Prop95799 : Prop :=
  ∀ L : ℕ, 1 ≤ L → ∀ m : ℤ, |m| < (L : ℤ) →
    ((((Finset.range L ×ˢ Finset.range L).filter
        (fun q : ℕ × ℕ => (q.1 : ℤ) - (q.2 : ℤ) = m)).card : ℕ) : ℤ) = (L : ℤ) - |m|

def S15Prop95799 : Prop :=
  ∀ L : ℕ, 1 ≤ L → ∀ g : ℤ → ℂ,
    ∑ k ∈ Finset.range L, ∑ k' ∈ Finset.range L, g ((k : ℤ) - (k' : ℤ)) =
      ∑ m ∈ Finset.Ioo (-(L : ℤ)) (L : ℤ), ((((L : ℤ) - |m| : ℤ)) : ℂ) * g m

noncomputable def fejerSum95799 (L : ℕ) (θ : ℝ) : ℂ :=
  ∑ m ∈ Finset.Ioo (-(L : ℤ)) (L : ℤ),
    (((1 - |(m : ℝ)| / (L : ℝ)) : ℝ) : ℂ) * ee95799 ((m : ℝ) * θ)

def S16Prop95799 : Prop :=
  ∀ L : ℕ, 1 ≤ L → ∀ θ : ℝ,
    (∃ r : ℝ, 0 ≤ r ∧ fejerSum95799 L θ = (r : ℂ)) ∧ fejerSum95799 L 0 = (L : ℂ)

def cdist95799 (p : ℕ) (m : ℤ) : ℤ := min (m % (p : ℤ)) ((p : ℤ) - m % (p : ℤ))

noncomputable def gw95799 (h p : ℕ) (m : ℤ) : ℝ := max 0 ((h : ℝ) - (cdist95799 p m : ℝ))

noncomputable def Fsum95799 (h L : ℕ) (P : Finset ℕ) : ℝ :=
  ∑ m ∈ Finset.Ioo (-(L : ℤ)) (L : ℤ),
    (1 - |(m : ℝ)| / (L : ℝ)) * ∏ p ∈ P, (gw95799 h p m / (h : ℝ))

def NonnegTrig95799 (F : ℤ → ℝ) (c0 : ℝ) : Prop :=
  ∃ (s : Finset ℝ) (c : ℝ → ℝ), (0 : ℝ) ∈ s ∧ (∀ θ ∈ s, 0 ≤ c θ) ∧ c0 ≤ c 0 ∧
    ∀ m : ℤ, ((F m : ℝ) : ℂ) = ∑ θ ∈ s, (c θ : ℂ) * ee95799 ((m : ℝ) * θ)

-- The constant 1 is the trigonometric polynomial with frequency set {0} and coefficient 1.
namespace erdos_95799_hyp_count_hyp_lower_hyp_one_ns

theorem erdos_95799_hyp_count_hyp_lower_hyp_one :
    NonnegTrig95799 (fun _ => (1 : ℝ)) 1 := by
  refine ⟨{0}, fun _ => (1 : ℝ), Finset.mem_singleton_self 0,
    fun _ _ => zero_le_one, le_refl _, ?_⟩
  intro m
  simp [ee95799]

end erdos_95799_hyp_count_hyp_lower_hyp_one_ns

theorem erdos_95799_hyp_count_hyp_lower_hyp_one :
    NonnegTrig95799 (fun _ => (1 : ℝ)) 1 := by
  exact erdos_95799_hyp_count_hyp_lower_hyp_one_ns.erdos_95799_hyp_count_hyp_lower_hyp_one

-- Multiply the two expansions. Use frequencies x+y and coefficients c x * d y, merging collisions.
-- The merged coefficients are still nonnegative. The (0,0) term gives coefficient at 0 >= c 0 * d 0 >= a*b.
namespace erdos_95799_hyp_count_hyp_lower_hyp_mul_ns

private lemma ee_add95799 (a b : ℝ) : ee95799 a * ee95799 b = ee95799 (a + b) := by
  unfold ee95799
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma term95799 (m : ℤ) (x y cx dy : ℝ) :
    ((cx : ℂ) * ee95799 ((m : ℝ) * x)) * ((dy : ℂ) * ee95799 ((m : ℝ) * y)) =
      ((cx * dy : ℝ) : ℂ) * ee95799 ((m : ℝ) * (x + y)) := by
  rw [mul_add, ← ee_add95799]
  push_cast
  ring

theorem erdos_95799_hyp_count_hyp_lower_hyp_mul :
    ∀ (F G : ℤ → ℝ) (a b : ℝ), 0 ≤ a → 0 ≤ b →
      NonnegTrig95799 F a → NonnegTrig95799 G b →
      NonnegTrig95799 (fun m => F m * G m) (a * b) := by
  intro F G a b ha hb hF' hG'
  obtain ⟨s, c, hs0, hc, hca, hF⟩ := hF'
  obtain ⟨t, d, ht0, hd, hdb, hG⟩ := hG'
  have hnn : ∀ ψ : ℝ, ∀ q ∈ (s ×ˢ t).filter (fun q : ℝ × ℝ => q.1 + q.2 = ψ),
      0 ≤ c q.1 * d q.2 := by
    intro ψ q hq
    rw [Finset.mem_filter, Finset.mem_product] at hq
    exact mul_nonneg (hc _ hq.1.1) (hd _ hq.1.2)
  refine ⟨(s ×ˢ t).image (fun q : ℝ × ℝ => q.1 + q.2),
    fun ψ => ∑ q ∈ (s ×ˢ t).filter (fun q : ℝ × ℝ => q.1 + q.2 = ψ), c q.1 * d q.2,
    ?_, ?_, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨(0, 0), Finset.mem_product.mpr ⟨hs0, ht0⟩, by simp⟩
  · intro ψ _
    exact Finset.sum_nonneg (hnn ψ)
  · have hmem : ((0 : ℝ), (0 : ℝ)) ∈ (s ×ˢ t).filter (fun q : ℝ × ℝ => q.1 + q.2 = 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hs0, ht0⟩, by simp⟩
    have h1 := Finset.single_le_sum (f := fun q : ℝ × ℝ => c q.1 * d q.2) (hnn 0) hmem
    have h2 : a * b ≤ c 0 * d 0 := mul_le_mul hca hdb hb (le_trans ha hca)
    exact le_trans h2 h1
  · intro m
    have e1 : ((F m * G m : ℝ) : ℂ)
        = ∑ q ∈ s ×ˢ t, ((c q.1 * d q.2 : ℝ) : ℂ) * ee95799 ((m : ℝ) * (q.1 + q.2)) := by
      rw [Complex.ofReal_mul, hF m, hG m, Finset.sum_product, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun θ _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun φ _ => ?_)
      exact term95799 m θ φ (c θ) (d φ)
    have e2 := (Finset.sum_fiberwise_of_maps_to (g := fun q : ℝ × ℝ => q.1 + q.2)
      (f := fun q : ℝ × ℝ => ((c q.1 * d q.2 : ℝ) : ℂ) * ee95799 ((m : ℝ) * (q.1 + q.2)))
      (t := (s ×ˢ t).image (fun q : ℝ × ℝ => q.1 + q.2))
      (fun q hq => Finset.mem_image_of_mem _ hq))
    show ((F m * G m : ℝ) : ℂ) = _
    rw [e1, ← e2]
    refine Finset.sum_congr rfl (fun ψ _ => ?_)
    simp only [Complex.ofReal_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun q hq => ?_)
    rw [(Finset.mem_filter.mp hq).2]

end erdos_95799_hyp_count_hyp_lower_hyp_mul_ns

theorem erdos_95799_hyp_count_hyp_lower_hyp_mul :
    ∀ (F G : ℤ → ℝ) (a b : ℝ), 0 ≤ a → 0 ≤ b →
      NonnegTrig95799 F a → NonnegTrig95799 G b →
      NonnegTrig95799 (fun m => F m * G m) (a * b) := by
  exact erdos_95799_hyp_count_hyp_lower_hyp_mul_ns.erdos_95799_hyp_count_hyp_lower_hyp_mul

-- If p >= 2h, then gw(h,p,.) = 1_J * 1_{-J} on Z/p with J = {0,...,h-1}.
-- Its DFT coefficients are |sum_{j<h} e(bj/p)|^2/p >= 0, and the mean is h^2/p.
-- Dividing by h: frequencies b/p for b < p, coefficient at 0 equal to h/p.
namespace erdos_95799_hyp_count_hyp_lower_hyp_single_ns
-- C1 steps (1)-(3): g_p = 1_J * 1_{-J} has no wraparound since p ≥ 2h, so its transform is ≥ 0;
-- the CRT product has transform ≥ 0 with mean ∏ h/p; pairing with the Fejer kernel (S1.6) gives S ≥ L ∏ h/p.
noncomputable def ee95799 (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))

def S11Prop95799 : Prop :=
  (∀ a b : ℝ, ee95799 a * ee95799 b = ee95799 (a + b)) ∧ ee95799 0 = 1 ∧
  (∀ a : ℝ, (starRingEnd ℂ) (ee95799 a) = ee95799 (-a)) ∧
  (∀ (n : ℕ) (θ : ℝ), ee95799 ((n : ℝ) * θ) = ee95799 θ ^ n)

def S12Prop95799 : Prop :=
  ∀ L : ℕ, 1 ≤ L → ∀ θ : ℝ,
    (((‖∑ k ∈ Finset.range L, ee95799 ((k : ℝ) * θ)‖ ^ 2 : ℝ)) : ℂ) =
      ∑ k ∈ Finset.range L, ∑ k' ∈ Finset.range L,
        ee95799 ((((k : ℤ) - (k' : ℤ) : ℤ) : ℝ) * θ)

def S14Prop95799 : Prop :=
  ∀ L : ℕ, 1 ≤ L → ∀ m : ℤ, |m| < (L : ℤ) →
    ((((Finset.range L ×ˢ Finset.range L).filter
        (fun q : ℕ × ℕ => (q.1 : ℤ) - (q.2 : ℤ) = m)).card : ℕ) : ℤ) = (L : ℤ) - |m|

def S15Prop95799 : Prop :=
  ∀ L : ℕ, 1 ≤ L → ∀ g : ℤ → ℂ,
    ∑ k ∈ Finset.range L, ∑ k' ∈ Finset.range L, g ((k : ℤ) - (k' : ℤ)) =
      ∑ m ∈ Finset.Ioo (-(L : ℤ)) (L : ℤ), ((((L : ℤ) - |m| : ℤ)) : ℂ) * g m

noncomputable def fejerSum95799 (L : ℕ) (θ : ℝ) : ℂ :=
  ∑ m ∈ Finset.Ioo (-(L : ℤ)) (L : ℤ),
    (((1 - |(m : ℝ)| / (L : ℝ)) : ℝ) : ℂ) * ee95799 ((m : ℝ) * θ)

def S16Prop95799 : Prop :=
  ∀ L : ℕ, 1 ≤ L → ∀ θ : ℝ,
    (∃ r : ℝ, 0 ≤ r ∧ fejerSum95799 L θ = (r : ℂ)) ∧ fejerSum95799 L 0 = (L : ℂ)

def cdist95799 (p : ℕ) (m : ℤ) : ℤ := min (m % (p : ℤ)) ((p : ℤ) - m % (p : ℤ))

noncomputable def gw95799 (h p : ℕ) (m : ℤ) : ℝ := max 0 ((h : ℝ) - (cdist95799 p m : ℝ))

noncomputable def Fsum95799 (h L : ℕ) (P : Finset ℕ) : ℝ :=
  ∑ m ∈ Finset.Ioo (-(L : ℤ)) (L : ℤ),
    (1 - |(m : ℝ)| / (L : ℝ)) * ∏ p ∈ P, (gw95799 h p m / (h : ℝ))

def NonnegTrig95799 (F : ℤ → ℝ) (c0 : ℝ) : Prop :=
  ∃ (s : Finset ℝ) (c : ℝ → ℝ), (0 : ℝ) ∈ s ∧ (∀ θ ∈ s, 0 ≤ c θ) ∧ c0 ≤ c 0 ∧
    ∀ m : ℤ, ((F m : ℝ) : ℂ) = ∑ θ ∈ s, (c θ : ℂ) * ee95799 ((m : ℝ) * θ)

private lemma E_mul95799 (a b : ℝ) : ee95799 a * ee95799 b = ee95799 (a + b) := by
  unfold ee95799
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma E_conj95799 (a : ℝ) : (starRingEnd ℂ) (ee95799 a) = ee95799 (-a) := by
  unfold ee95799
  rw [show (2 * (Real.pi:ℂ) * Complex.I * ((a:ℝ):ℂ)) = ((2 * Real.pi * a : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

private lemma lemA95799 (h : ℕ) (θ : ℝ) (m : ℤ) :
    ((Complex.normSq (∑ j ∈ Finset.range h, ee95799 ((j:ℝ) * θ)) : ℝ) : ℂ) * ee95799 ((m:ℝ) * θ) =
      ∑ j ∈ Finset.range h, ∑ j' ∈ Finset.range h,
        ee95799 ((((j:ℤ) - (j':ℤ) + m : ℤ) : ℝ) * θ) := by
  rw [← Complex.mul_conj, map_sum, Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j' _ => ?_)
  rw [E_conj95799, E_mul95799, E_mul95799]
  congr 1
  push_cast
  ring

private lemma lemB95799 (p : ℕ) (hp0 : 0 < p) (k : ℤ) :
    ∑ b ∈ Finset.range p, ee95799 ((k:ℝ) * ((b:ℝ)/(p:ℝ))) =
      if (p:ℤ) ∣ k then (p:ℂ) else 0 := by
  have hpR : (p:ℝ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hpow : ∀ b : ℕ, ee95799 ((k:ℝ) * ((b:ℝ)/(p:ℝ))) = ee95799 ((k:ℝ)/(p:ℝ)) ^ b := by
    intro b
    unfold ee95799
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun b _ => hpow b)]
  have hint : ∀ n : ℤ, ee95799 (n:ℝ) = 1 := by
    intro n
    unfold ee95799
    rw [show (2 * (Real.pi:ℂ) * Complex.I * (((n:ℝ)):ℂ)) = (n:ℂ) * (2 * Real.pi * Complex.I) by
      push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I n
  split_ifs with hd
  · obtain ⟨q, hq⟩ := hd
    have hw : ee95799 ((k:ℝ)/(p:ℝ)) = 1 := by
      rw [show (k:ℝ)/(p:ℝ) = ((q:ℤ):ℝ) by
        rw [hq, div_eq_iff hpR]; push_cast; ring]
      exact hint q
    rw [hw]
    simp
  · have hw1 : ee95799 ((k:ℝ)/(p:ℝ)) ≠ 1 := by
      intro hw
      unfold ee95799 at hw
      rw [Complex.exp_eq_one_iff] at hw
      obtain ⟨n, hn⟩ := hw
      have hne : (2 * (Real.pi:ℂ) * Complex.I) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have h1 : (((k:ℝ)/(p:ℝ) : ℝ) : ℂ) = ((n:ℝ):ℂ) := by
        apply mul_left_cancel₀ hne
        push_cast at hn ⊢
        linear_combination hn
      have h2 : (k:ℝ)/(p:ℝ) = (n:ℝ) := Complex.ofReal_injective h1
      apply hd
      refine ⟨n, ?_⟩
      have h3 : (k:ℝ) = (p:ℝ) * (n:ℝ) := by
        rw [← h2]; field_simp
      exact_mod_cast h3
    have hwp : ee95799 ((k:ℝ)/(p:ℝ)) ^ p = 1 := by
      rw [← hpow p, div_self hpR, mul_one]
      exact hint k
    rw [geom_sum_eq hw1, hwp]
    simp

private lemma key95799 (h p : ℕ) (hp0 : 0 < p) (m : ℤ) :
    ∑ b ∈ Finset.range p,
      ((Complex.normSq (∑ j ∈ Finset.range h, ee95799 ((j:ℝ) * ((b:ℝ)/(p:ℝ)))) : ℝ) : ℂ) *
        ee95799 ((m:ℝ) * ((b:ℝ)/(p:ℝ)))
      = (p:ℂ) * ∑ j ∈ Finset.range h, ∑ j' ∈ Finset.range h,
          (if (p:ℤ) ∣ ((j:ℤ) - (j':ℤ) + m) then (1:ℂ) else 0) := by
  calc (∑ b ∈ Finset.range p,
      ((Complex.normSq (∑ j ∈ Finset.range h, ee95799 ((j:ℝ) * ((b:ℝ)/(p:ℝ)))) : ℝ) : ℂ) *
        ee95799 ((m:ℝ) * ((b:ℝ)/(p:ℝ))))
      = ∑ b ∈ Finset.range p, ∑ j ∈ Finset.range h, ∑ j' ∈ Finset.range h,
          ee95799 ((((j:ℤ) - (j':ℤ) + m : ℤ) : ℝ) * ((b:ℝ)/(p:ℝ))) :=
        Finset.sum_congr rfl (fun b _ => lemA95799 h ((b:ℝ)/(p:ℝ)) m)
    _ = ∑ j ∈ Finset.range h, ∑ b ∈ Finset.range p, ∑ j' ∈ Finset.range h,
          ee95799 ((((j:ℤ) - (j':ℤ) + m : ℤ) : ℝ) * ((b:ℝ)/(p:ℝ))) := Finset.sum_comm
    _ = ∑ j ∈ Finset.range h, ∑ j' ∈ Finset.range h, ∑ b ∈ Finset.range p,
          ee95799 ((((j:ℤ) - (j':ℤ) + m : ℤ) : ℝ) * ((b:ℝ)/(p:ℝ))) :=
        Finset.sum_congr rfl (fun j _ => Finset.sum_comm)
    _ = ∑ j ∈ Finset.range h, ∑ j' ∈ Finset.range h,
          (if (p:ℤ) ∣ ((j:ℤ) - (j':ℤ) + m) then (p:ℂ) else 0) :=
        Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun j' _ => lemB95799 p hp0 _))
    _ = (p:ℂ) * ∑ j ∈ Finset.range h, ∑ j' ∈ Finset.range h,
          (if (p:ℤ) ∣ ((j:ℤ) - (j':ℤ) + m) then (1:ℂ) else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j' _ => ?_)
        rw [mul_ite, mul_one, mul_zero]

private lemma count95799 (h p : ℕ) (hp : 2 * h ≤ p) (hp0 : 0 < p) (m : ℤ) :
    (((∑ j ∈ Finset.range h, ∑ j' ∈ Finset.range h,
        (if (p:ℤ) ∣ ((j:ℤ) - (j':ℤ) + m) then (1:ℕ) else 0) : ℕ)) : ℝ) = gw95799 h p m := by
  obtain ⟨r, hr⟩ : ∃ r : ℕ, m % (p:ℤ) = (r:ℤ) :=
    ⟨(m % (p:ℤ)).toNat, (Int.toNat_of_nonneg (Int.emod_nonneg m (by omega))).symm⟩
  have hrp : r < p := by
    have := Int.emod_lt_of_pos m (show (0:ℤ) < (p:ℤ) by omega)
    rw [hr] at this
    exact_mod_cast this
  obtain ⟨q, hq⟩ : ∃ q : ℤ, m = (p:ℤ) * q + (r:ℤ) :=
    ⟨m / (p:ℤ), by rw [← hr]; have := Int.emod_def m (p:ℤ); linarith⟩
  have hcond : ∀ j j' : ℕ, j < h → j' < h →
      ((p:ℤ) ∣ (j:ℤ) - (j':ℤ) + m ↔ (j' = j + r ∨ j' + p = j + r)) := by
    intro j j' hj hj'
    have hj1 : (j:ℤ) < h := by exact_mod_cast hj
    have hj2 : (j':ℤ) < h := by exact_mod_cast hj'
    have hr1 : (r:ℤ) < p := by exact_mod_cast hrp
    have hpp : 2 * (h:ℤ) ≤ p := by exact_mod_cast hp
    have hj0 : (0:ℤ) ≤ j := by positivity
    have hj0' : (0:ℤ) ≤ j' := by positivity
    have hr0 : (0:ℤ) ≤ r := by positivity
    have hp0' : (0:ℤ) ≤ p := by positivity
    have hh0 : (0:ℤ) ≤ h := by positivity
    rw [hq]
    constructor
    · rintro ⟨k, hk⟩
      have h1 : (p:ℤ) * (k - q) = j - j' + r := by linear_combination -1 * hk
      have hk0 : 0 ≤ k - q := by
        by_contra hneg
        have : (p:ℤ) * (-(k - q) - 1) ≥ 0 := mul_nonneg hp0' (by omega)
        nlinarith
      have hk1 : k - q ≤ 1 := by
        by_contra hneg
        have : (p:ℤ) * ((k - q) - 2) ≥ 0 := mul_nonneg hp0' (by omega)
        nlinarith
      have : k - q = 0 ∨ k - q = 1 := by omega
      rcases this with h0 | h0
      · rw [h0, mul_zero] at h1; left; omega
      · rw [h0, mul_one] at h1; right; omega
    · rintro (h0 | h0)
      · refine ⟨q, ?_⟩
        have : (j':ℤ) = j + r := by exact_mod_cast h0
        rw [this]; ring
      · refine ⟨q + 1, ?_⟩
        have : (j':ℤ) + p = j + r := by exact_mod_cast h0
        linear_combination -1 * this
  have hsum : ∀ j ∈ Finset.range h,
      (∑ j' ∈ Finset.range h, (if (p:ℤ) ∣ ((j:ℤ) - (j':ℤ) + m) then (1:ℕ) else 0)) =
        (if j + r < h then 1 else 0) + (if p ≤ j + r then 1 else 0) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [Finset.sum_congr rfl (fun j' hj' =>
      if_congr (hcond j j' hj (Finset.mem_range.mp hj')) rfl rfl)]
    have hsplit : ∀ j' ∈ Finset.range h,
        (if (j' = j + r ∨ j' + p = j + r) then (1:ℕ) else 0) =
          (if j' = j + r then 1 else 0) +
            (if j' = j + r - p then (if p ≤ j + r then 1 else 0) else 0) := by
      intro j' _
      split_ifs <;> omega
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_range]
    split_ifs <;> omega
  have e1 : (Finset.range h).filter (fun j => j + r < h) = Finset.range (h - r) := by
    ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega
  have e2 : (Finset.range h).filter (fun j => p ≤ j + r) = Finset.Ico (p - r) h := by
    ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  have c1 : (∑ j ∈ Finset.range h, if j + r < h then (1:ℕ) else 0) = h - r := by
    rw [← Finset.card_filter, e1, Finset.card_range]
  have c2 : (∑ j ∈ Finset.range h, if p ≤ j + r then (1:ℕ) else 0) = h - (p - r) := by
    rw [← Finset.card_filter, e2, Nat.card_Ico]
  rw [Finset.sum_congr rfl hsum, Finset.sum_add_distrib, c1, c2]
  have key : (((h - r + (h - (p - r)) : ℕ) : ℤ)) =
      max 0 ((h:ℤ) - min (r:ℤ) ((p:ℤ) - (r:ℤ))) := by
    rw [max_def, min_def]
    split_ifs <;> omega
  have e3 : (((h - r + (h - (p - r)) : ℕ)) : ℝ) =
      ((((h - r + (h - (p - r)) : ℕ) : ℤ)) : ℝ) := (Int.cast_natCast _).symm
  rw [e3, key]
  unfold gw95799 cdist95799
  rw [hr]
  push_cast
  try rfl

theorem erdos_95799_hyp_count_hyp_lower_hyp_single :
    ∀ h p : ℕ, 1 ≤ h → 2 * h ≤ p →
      NonnegTrig95799 (fun m => gw95799 h p m / (h : ℝ)) ((h : ℝ) / (p : ℝ)) := by
  intro h p hh hp
  have hp0 : 0 < p := by omega
  have hpR : (0:ℝ) < (p:ℝ) := Nat.cast_pos.mpr hp0
  have hhR : (0:ℝ) < (h:ℝ) := Nat.cast_pos.mpr (by omega)
  have hpC : (p:ℂ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hhC : (h:ℂ) ≠ 0 := by exact_mod_cast (show h ≠ 0 by omega)
  have main : ∀ m : ℤ, ((gw95799 h p m / (h:ℝ) : ℝ) : ℂ) =
      ∑ b ∈ Finset.range p,
        ((Complex.normSq (∑ j ∈ Finset.range h, ee95799 ((j:ℝ) * ((b:ℝ)/(p:ℝ)))) /
          ((p:ℝ) * (h:ℝ)) : ℝ) : ℂ) * ee95799 ((m:ℝ) * ((b:ℝ)/(p:ℝ))) := by
    intro m
    have hterm : ∀ b : ℕ,
        ((Complex.normSq (∑ j ∈ Finset.range h, ee95799 ((j:ℝ) * ((b:ℝ)/(p:ℝ)))) /
          ((p:ℝ) * (h:ℝ)) : ℝ) : ℂ) * ee95799 ((m:ℝ) * ((b:ℝ)/(p:ℝ))) =
        (1 / ((p:ℂ) * (h:ℂ))) *
          (((Complex.normSq (∑ j ∈ Finset.range h, ee95799 ((j:ℝ) * ((b:ℝ)/(p:ℝ)))) : ℝ) : ℂ) *
            ee95799 ((m:ℝ) * ((b:ℝ)/(p:ℝ)))) := by
      intro b
      push_cast
      ring
    have hc : (∑ j ∈ Finset.range h, ∑ j' ∈ Finset.range h,
        (if (p:ℤ) ∣ ((j:ℤ) - (j':ℤ) + m) then (1:ℂ) else 0)) = ((gw95799 h p m : ℝ) : ℂ) := by
      rw [← count95799 h p hp hp0 m]
      push_cast
      refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun j' _ => ?_))
      split_ifs <;> simp
    rw [Finset.sum_congr rfl (fun b _ => hterm b), ← Finset.mul_sum, key95799 h p hp0 m, hc]
    push_cast
    field_simp
    try ring
  unfold NonnegTrig95799
  refine ⟨(Finset.range p).image (fun b : ℕ => (b:ℝ)/(p:ℝ)),
    fun θ => Complex.normSq (∑ j ∈ Finset.range h, ee95799 ((j:ℝ) * θ)) / ((p:ℝ) * (h:ℝ)),
    ?_, ?_, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hp0, by simp⟩
  · intro θ _
    exact div_nonneg (Complex.normSq_nonneg _) (by positivity)
  · show (h:ℝ)/(p:ℝ) ≤
      Complex.normSq (∑ j ∈ Finset.range h, ee95799 ((j:ℝ) * 0)) / ((p:ℝ) * (h:ℝ))
    have hS : (∑ j ∈ Finset.range h, ee95799 ((j:ℝ) * 0)) = ((h:ℝ):ℂ) := by
      simp [ee95799]
    have hph : (0:ℝ) < (p:ℝ) * (h:ℝ) := mul_pos hpR hhR
    rw [hS, Complex.normSq_ofReal, div_le_div_iff₀ hpR hph]
    exact le_of_eq (by ring)
  · intro m
    have hinj : ∀ a ∈ Finset.range p, ∀ b ∈ Finset.range p,
        (a:ℝ)/(p:ℝ) = (b:ℝ)/(p:ℝ) → a = b := by
      intro a _ b _ hab
      rw [div_left_inj' hpR.ne'] at hab
      exact_mod_cast hab
    rw [Finset.sum_image hinj]
    exact main m
end erdos_95799_hyp_count_hyp_lower_hyp_single_ns

theorem erdos_95799_hyp_count_hyp_lower_hyp_single :
    ∀ h p : ℕ, 1 ≤ h → 2 * h ≤ p →
      NonnegTrig95799 (fun m => gw95799 h p m / (h : ℝ)) ((h : ℝ) / (p : ℝ)) := by
  exact erdos_95799_hyp_count_hyp_lower_hyp_single_ns.erdos_95799_hyp_count_hyp_lower_hyp_single



theorem erdos_95799_hyp_count_hyp_lower : S16Prop95799 →
    ∀ (h L : ℕ) (P : Finset ℕ), 1 ≤ h → 1 ≤ L →
      (∀ p ∈ P, Nat.Prime p ∧ 2 * h ≤ p) →
      (L : ℝ) * ∏ p ∈ P, ((h : ℝ) / (p : ℝ)) ≤ Fsum95799 h L P := by
  intro hS16 h L P hh hL hP
  have hprod : ∀ Q : Finset ℕ, (∀ p ∈ Q, Nat.Prime p ∧ 2 * h ≤ p) →
      NonnegTrig95799 (fun m => ∏ p ∈ Q, (gw95799 h p m / (h : ℝ)))
        (∏ p ∈ Q, ((h : ℝ) / (p : ℝ))) := by
    intro Q
    induction Q using Finset.induction_on with
    | empty =>
      intro _
      simp only [Finset.prod_empty]
      exact erdos_95799_hyp_count_hyp_lower_hyp_one
    | @insert a s ha ih =>
      intro hQ
      have ha' := hQ a (Finset.mem_insert_self a s)
      have hs : ∀ p ∈ s, Nat.Prime p ∧ 2 * h ≤ p :=
        fun p hp => hQ p (Finset.mem_insert_of_mem hp)
      have h1 := erdos_95799_hyp_count_hyp_lower_hyp_single h a hh ha'.2
      have h2 := ih hs
      have h3 := erdos_95799_hyp_count_hyp_lower_hyp_mul
        (fun m => gw95799 h a m / (h : ℝ))
        (fun m => ∏ p ∈ s, (gw95799 h p m / (h : ℝ)))
        ((h : ℝ) / (a : ℝ)) (∏ p ∈ s, ((h : ℝ) / (p : ℝ)))
        (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (Finset.prod_nonneg (fun p _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
        h1 h2
      simp only [Finset.prod_insert ha]
      exact h3
  obtain ⟨s, c, hs0, hc, hc0, hF⟩ := hprod P hP
  have hF' : ∀ m : ℤ, ((∏ p ∈ P, (gw95799 h p m / (h : ℝ)) : ℝ) : ℂ) =
      ∑ θ ∈ s, (c θ : ℂ) * ee95799 ((m : ℝ) * θ) := hF
  have key : ((Fsum95799 h L P : ℝ) : ℂ) = ∑ θ ∈ s, (c θ : ℂ) * fejerSum95799 L θ := by
    unfold Fsum95799 fejerSum95799
    rw [Complex.ofReal_sum]
    simp_rw [Complex.ofReal_mul, hF', Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun θ _ => Finset.sum_congr rfl (fun m _ => by ring))
  have hr : ∀ θ : ℝ, ∃ r : ℝ, 0 ≤ r ∧ fejerSum95799 L θ = (r : ℂ) :=
    fun θ => (hS16 L hL θ).1
  choose r hr0 hrE using hr
  simp_rw [hrE] at key
  have key3 : Fsum95799 h L P = ∑ θ ∈ s, c θ * r θ := by exact_mod_cast key
  have hr00 : r 0 = (L : ℝ) := by
    have e1 := (hS16 L hL 0).2
    rw [hrE 0] at e1
    exact_mod_cast e1
  rw [key3]
  calc (L : ℝ) * ∏ p ∈ P, ((h : ℝ) / (p : ℝ))
      = (∏ p ∈ P, ((h : ℝ) / (p : ℝ))) * (L : ℝ) := by ring
    _ ≤ c 0 * r 0 := by
        rw [hr00]
        exact mul_le_mul_of_nonneg_right hc0 (Nat.cast_nonneg L)
    _ ≤ ∑ θ ∈ s, c θ * r θ :=
        Finset.single_le_sum (f := fun θ => c θ * r θ)
          (fun θ hθ => mul_nonneg (hc θ hθ) (hr0 θ)) hs0
end erdos_95799_hyp_count_hyp_lower_ns

theorem erdos_95799_hyp_count_hyp_lower : S16Prop95799 →
    ∀ (h L : ℕ) (P : Finset ℕ), 1 ≤ h → 1 ≤ L →
      (∀ p ∈ P, Nat.Prime p ∧ 2 * h ≤ p) →
      (L : ℝ) * ∏ p ∈ P, ((h : ℝ) / (p : ℝ)) ≤ Fsum95799 h L P := by
  exact erdos_95799_hyp_count_hyp_lower_ns.erdos_95799_hyp_count_hyp_lower



-- C1 step (4): 0 ≤ wF ≤ 1_G·1_{|m|<L}, with G = {m : cdist p m ≤ h-1 ∀ p} = erdosG-set.
-- G is symmetric and (-T,T) holds 2T-1 integers, so S > 2T-1 forces a point of G in [T,L).
namespace erdos_95799_hyp_count_hyp_count_ns
-- Blueprint S1-S5: Fejér kernel positivity + orthogonality give
-- #(G ∩ (-L,L)) ≥ L ∏ (h/p); G is symmetric, so G ∩ [T,L) is nonempty once 2T-1 < L ∏ (h/p).
noncomputable def ee95799 (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))

def S11Prop95799 : Prop :=
  (∀ a b : ℝ, ee95799 a * ee95799 b = ee95799 (a + b)) ∧ ee95799 0 = 1 ∧
  (∀ a : ℝ, (starRingEnd ℂ) (ee95799 a) = ee95799 (-a)) ∧
  (∀ (n : ℕ) (θ : ℝ), ee95799 ((n : ℝ) * θ) = ee95799 θ ^ n)

def S12Prop95799 : Prop :=
  ∀ L : ℕ, 1 ≤ L → ∀ θ : ℝ,
    (((‖∑ k ∈ Finset.range L, ee95799 ((k : ℝ) * θ)‖ ^ 2 : ℝ)) : ℂ) =
      ∑ k ∈ Finset.range L, ∑ k' ∈ Finset.range L,
        ee95799 ((((k : ℤ) - (k' : ℤ) : ℤ) : ℝ) * θ)

def S14Prop95799 : Prop :=
  ∀ L : ℕ, 1 ≤ L → ∀ m : ℤ, |m| < (L : ℤ) →
    ((((Finset.range L ×ˢ Finset.range L).filter
        (fun q : ℕ × ℕ => (q.1 : ℤ) - (q.2 : ℤ) = m)).card : ℕ) : ℤ) = (L : ℤ) - |m|

def S15Prop95799 : Prop :=
  ∀ L : ℕ, 1 ≤ L → ∀ g : ℤ → ℂ,
    ∑ k ∈ Finset.range L, ∑ k' ∈ Finset.range L, g ((k : ℤ) - (k' : ℤ)) =
      ∑ m ∈ Finset.Ioo (-(L : ℤ)) (L : ℤ), ((((L : ℤ) - |m| : ℤ)) : ℂ) * g m

noncomputable def fejerSum95799 (L : ℕ) (θ : ℝ) : ℂ :=
  ∑ m ∈ Finset.Ioo (-(L : ℤ)) (L : ℤ),
    (((1 - |(m : ℝ)| / (L : ℝ)) : ℝ) : ℂ) * ee95799 ((m : ℝ) * θ)

def S16Prop95799 : Prop :=
  ∀ L : ℕ, 1 ≤ L → ∀ θ : ℝ,
    (∃ r : ℝ, 0 ≤ r ∧ fejerSum95799 L θ = (r : ℂ)) ∧ fejerSum95799 L 0 = (L : ℂ)

def cdist95799 (p : ℕ) (m : ℤ) : ℤ := min (m % (p : ℤ)) ((p : ℤ) - m % (p : ℤ))

noncomputable def gw95799 (h p : ℕ) (m : ℤ) : ℝ := max 0 ((h : ℝ) - (cdist95799 p m : ℝ))

noncomputable def Fsum95799 (h L : ℕ) (P : Finset ℕ) : ℝ :=
  ∑ m ∈ Finset.Ioo (-(L : ℤ)) (L : ℤ),
    (1 - |(m : ℝ)| / (L : ℝ)) * ∏ p ∈ P, (gw95799 h p m / (h : ℝ))

private lemma good95799 (h p : ℕ) (m : ℤ) (hp : 0 < p) (hne : gw95799 h p m ≠ 0) :
    ∃ d : ℤ, |d| ≤ (h : ℤ) - 1 ∧ (p : ℤ) ∣ m - d := by
  have hlt : (cdist95799 p m : ℝ) < h := by
    by_contra hc
    push_neg at hc
    apply hne
    unfold gw95799
    exact max_eq_left (by linarith)
  have hc : cdist95799 p m < (h : ℤ) := by exact_mod_cast hlt
  unfold cdist95799 at hc
  have h0 := Int.emod_nonneg m (show (p : ℤ) ≠ 0 by omega)
  have h1 := Int.emod_lt_of_pos m (show (0 : ℤ) < p by omega)
  have hdiv : (p : ℤ) ∣ m - m % (p : ℤ) :=
    ⟨m / (p : ℤ), by have := Int.emod_add_ediv_mul m (p : ℤ); linarith⟩
  generalize m % (p : ℤ) = r at *
  rcases le_total r ((p : ℤ) - r) with hle | hle
  · rw [min_eq_left hle] at hc
    exact ⟨r, abs_le.mpr ⟨by omega, by omega⟩, hdiv⟩
  · rw [min_eq_right hle] at hc
    refine ⟨r - p, abs_le.mpr ⟨by omega, by omega⟩, ?_⟩
    have e : m - (r - (p : ℤ)) = (m - r) + p := by ring
    rw [e]
    exact dvd_add hdiv (dvd_refl _)

private lemma term_bound95799 (h L T : ℕ) (P : Finset ℕ) (hh : 1 ≤ h)
    (hP : ∀ p ∈ P, Nat.Prime p ∧ 2 * h ≤ p)
    (key : ∀ m : ℤ, (T : ℤ) ≤ m → m < (L : ℤ) →
      ¬ (∀ p ∈ P, ∃ d : ℤ, |d| ≤ (h : ℤ) - 1 ∧ (p : ℤ) ∣ m - d)) :
    ∀ m ∈ Finset.Ioo (-(L : ℤ)) (L : ℤ),
      (1 - |(m : ℝ)| / (L : ℝ)) * ∏ p ∈ P, (gw95799 h p m / (h : ℝ)) ≤
        (if m ∈ Finset.Ioo (-(T : ℤ)) (T : ℤ) then (1 : ℝ) else 0) := by
  have hhpos : (0 : ℝ) < h := by
    have : 0 < h := by omega
    exact_mod_cast this
  intro m hm
  rw [Finset.mem_Ioo] at hm
  have hLpos : (0 : ℝ) < L := by
    have : (0 : ℤ) < L := by omega
    exact_mod_cast this
  have hm' : |(m : ℝ)| < (L : ℝ) := by
    rw [abs_lt]
    constructor
    · exact_mod_cast hm.1
    · exact_mod_cast hm.2
  have hw0 : 0 ≤ 1 - |(m : ℝ)| / (L : ℝ) := by
    have := (div_le_one hLpos).mpr hm'.le
    linarith
  have hfac : ∀ p ∈ P, 0 ≤ gw95799 h p m / (h : ℝ) ∧ gw95799 h p m / (h : ℝ) ≤ 1 := by
    intro p hp
    have hp0 : 0 < p := (hP p hp).1.pos
    have hc0 : (0 : ℝ) ≤ (cdist95799 p m : ℝ) := by
      have : 0 ≤ cdist95799 p m := by
        unfold cdist95799
        have a := Int.emod_nonneg m (show (p : ℤ) ≠ 0 by omega)
        have b := Int.emod_lt_of_pos m (show (0 : ℤ) < p by omega)
        exact le_min a (by omega)
      exact_mod_cast this
    have g0 : 0 ≤ gw95799 h p m := by
      unfold gw95799
      exact le_max_left _ _
    have g1 : gw95799 h p m ≤ h := by
      unfold gw95799
      exact max_le hhpos.le (by linarith)
    exact ⟨div_nonneg g0 hhpos.le, (div_le_one hhpos).mpr g1⟩
  have hprod1 : ∏ p ∈ P, (gw95799 h p m / (h : ℝ)) ≤ 1 :=
    Finset.prod_le_one (fun p hp => (hfac p hp).1) (fun p hp => (hfac p hp).2)
  split_ifs with hmT
  · have := mul_le_mul_of_nonneg_left hprod1 hw0
    have : 0 ≤ |(m : ℝ)| / (L : ℝ) := by positivity
    linarith
  · have hz : ∏ p ∈ P, (gw95799 h p m / (h : ℝ)) = 0 := by
      by_contra hne
      have hg : ∀ p ∈ P, ∃ d : ℤ, |d| ≤ (h : ℤ) - 1 ∧ (p : ℤ) ∣ m - d := by
        intro p hp
        apply good95799 h p m (hP p hp).1.pos
        intro h0
        apply hne
        exact Finset.prod_eq_zero hp (by rw [h0, zero_div])
      rw [Finset.mem_Ioo] at hmT
      rcases le_or_gt (T : ℤ) m with h1 | h1
      · exact key m h1 hm.2 hg
      · have h3 : (T : ℤ) ≤ -m := by omega
        apply key (-m) h3 (by omega)
        intro p hp
        obtain ⟨d, hd, hdv⟩ := hg p hp
        refine ⟨-d, by rw [abs_neg]; exact hd, ?_⟩
        have e : -m - -d = -(m - d) := by ring
        rw [e]
        exact (dvd_neg).mpr hdv
    rw [hz, mul_zero]

theorem erdos_95799_hyp_count_hyp_count :
    ∀ (h L T : ℕ) (P : Finset ℕ), 1 ≤ h → 1 ≤ T →
      (∀ p ∈ P, Nat.Prime p ∧ 2 * h ≤ p) →
      2 * (T : ℝ) - 1 < Fsum95799 h L P →
      ∃ m : ℤ, (T : ℤ) ≤ m ∧ m < (L : ℤ) ∧
        ∀ p ∈ P, ∃ d : ℤ, |d| ≤ (h : ℤ) - 1 ∧ (p : ℤ) ∣ m - d := by
  intro h L T P hh hT hP hF
  by_contra hcon
  have key : ∀ m : ℤ, (T : ℤ) ≤ m → m < (L : ℤ) →
      ¬ (∀ p ∈ P, ∃ d : ℤ, |d| ≤ (h : ℤ) - 1 ∧ (p : ℤ) ∣ m - d) :=
    fun m h1 h2 hg => hcon ⟨m, h1, h2, hg⟩
  have hsum : Fsum95799 h L P ≤ ∑ m ∈ Finset.Ioo (-(L : ℤ)) (L : ℤ),
      (if m ∈ Finset.Ioo (-(T : ℤ)) (T : ℤ) then (1 : ℝ) else 0) := by
    unfold Fsum95799
    exact Finset.sum_le_sum (term_bound95799 h L T P hh hP key)
  have hle : ∑ m ∈ Finset.Ioo (-(L : ℤ)) (L : ℤ),
      (if m ∈ Finset.Ioo (-(T : ℤ)) (T : ℤ) then (1 : ℝ) else 0) ≤
      ∑ m ∈ Finset.Ioo (-(T : ℤ)) (T : ℤ), (1 : ℝ) := by
    rw [← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx
      exact (Finset.mem_filter.1 hx).2
    · intro _ _ _
      exact zero_le_one
  have hc : (Finset.Ioo (-(T : ℤ)) (T : ℤ)).card + 1 = 2 * T := by
    rw [Int.card_Ioo]
    omega
  have hcR : ((Finset.Ioo (-(T : ℤ)) (T : ℤ)).card : ℝ) + 1 = 2 * (T : ℝ) := by
    exact_mod_cast hc
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at hle
  linarith
end erdos_95799_hyp_count_hyp_count_ns

theorem erdos_95799_hyp_count_hyp_count :
    ∀ (h L T : ℕ) (P : Finset ℕ), 1 ≤ h → 1 ≤ T →
      (∀ p ∈ P, Nat.Prime p ∧ 2 * h ≤ p) →
      2 * (T : ℝ) - 1 < Fsum95799 h L P →
      ∃ m : ℤ, (T : ℤ) ≤ m ∧ m < (L : ℤ) ∧
        ∀ p ∈ P, ∃ d : ℤ, |d| ≤ (h : ℤ) - 1 ∧ (p : ℤ) ∣ m - d := by
  exact erdos_95799_hyp_count_hyp_count_ns.erdos_95799_hyp_count_hyp_count



theorem erdos_95799_hyp_count :
    ∀ (h L T : ℕ) (P : Finset ℕ), 1 ≤ h → 1 ≤ T →
      (∀ p ∈ P, Nat.Prime p ∧ 2 * h ≤ p) →
      2 * (T : ℝ) - 1 < (L : ℝ) * ∏ p ∈ P, ((h : ℝ) / (p : ℝ)) →
      ∃ m : ℤ, (T : ℤ) ≤ m ∧ m < (L : ℤ) ∧ erdosG h P m := by
  intro h L T P hh hT hP hL
  have hF := erdos_95799_hyp_count_hyp_lower
    (erdos_95799_hyp_count_hyp_fejer
      (erdos_95799_hyp_count_hyp_square erdos_95799_hyp_count_hyp_char)
      (erdos_95799_hyp_count_hyp_regroup erdos_95799_hyp_count_hyp_fiber))
  have hT' : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have hL1 : 1 ≤ L := by
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · subst h0
      rw [Nat.cast_zero, zero_mul] at hL
      linarith
    · exact h0
  exact erdos_95799_hyp_count_hyp_count h L T P hh hT hP
    (lt_of_lt_of_le hL (hF h L P hh hL1 hP))
end erdos_95799_hyp_count_ns

theorem erdos_95799_hyp_count :
    ∀ (h L T : ℕ) (P : Finset ℕ), 1 ≤ h → 1 ≤ T →
      (∀ p ∈ P, Nat.Prime p ∧ 2 * h ≤ p) →
      2 * (T : ℝ) - 1 < (L : ℝ) * ∏ p ∈ P, ((h : ℝ) / (p : ℝ)) →
      ∃ m : ℤ, (T : ℤ) ≤ m ∧ m < (L : ℤ) ∧ erdosG h P m := by
  exact erdos_95799_hyp_count_ns.erdos_95799_hyp_count



-- Blueprint S6: primes ≤ ⌊log n⌋ divide by pigeonhole; primes in (⌊log n⌋, 6K] lie in ePset K
-- and divide n + (h - d) with 1 ≤ h - d ≤ 2h-1 ≤ K ≤ ⌊log n⌋.
namespace erdos_95799_hyp_shift_ns
theorem erdos_95799_hyp_shift :
    ∀ (K n : ℕ), 3 ≤ K → Real.exp (K : ℝ) ≤ (n : ℝ) →
      erdosG ((K + 1) / 2) (ePset K) ((n : ℤ) + (((K + 1) / 2 : ℕ) : ℤ)) →
      ∀ p : ℕ, p ≤ 6 * K → p.Prime →
        p ∣ ∏ i ∈ Finset.Icc 1 ⌊Real.log n⌋₊, (n + i) := by
  intro K n hK hn hG p hp6 hp
  have hlog : (K:ℝ) ≤ Real.log n := by
    have := Real.log_le_log (Real.exp_pos _) hn
    rwa [Real.log_exp] at this
  have hKL : K ≤ ⌊Real.log (n:ℝ)⌋₊ := Nat.le_floor hlog
  suffices H : ∃ i ∈ Finset.Icc 1 ⌊Real.log (n:ℝ)⌋₊, p ∣ n + i by
    obtain ⟨i, hi, hdiv⟩ := H
    exact dvd_trans hdiv (Finset.dvd_prod_of_mem _ hi)
  by_cases hpK : p ≤ K
  · refine ⟨p - n % p, ?_, ?_⟩
    · have h2 := Nat.mod_lt n hp.pos
      rw [Finset.mem_Icc]; omega
    · have h1 := Nat.div_add_mod n p
      have h2 := Nat.mod_lt n hp.pos
      refine ⟨n / p + 1, ?_⟩
      rw [mul_add, mul_one]; omega
  · push_neg at hpK
    have hmem : p ∈ ePset K := by
      unfold ePset
      rw [Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨hpK, hp6⟩, hp⟩
    obtain ⟨d, hd, hdvd⟩ := hG p hmem
    rw [abs_le] at hd
    obtain ⟨hd1, hd2⟩ := hd
    have hi := Int.toNat_of_nonneg
      (show (0:ℤ) ≤ (((K + 1) / 2 : ℕ) : ℤ) - d by omega)
    refine ⟨((((K + 1) / 2 : ℕ) : ℤ) - d).toNat, ?_, ?_⟩
    · rw [Finset.mem_Icc]; omega
    · rw [← Int.natCast_dvd_natCast, Nat.cast_add, hi]
      have e : (n:ℤ) + ((((K + 1) / 2 : ℕ) : ℤ) - d)
          = (n:ℤ) + (((K + 1) / 2 : ℕ) : ℤ) - d := by ring
      rw [e]; exact hdvd
end erdos_95799_hyp_shift_ns

theorem erdos_95799_hyp_shift :
    ∀ (K n : ℕ), 3 ≤ K → Real.exp (K : ℝ) ≤ (n : ℝ) →
      erdosG ((K + 1) / 2) (ePset K) ((n : ℤ) + (((K + 1) / 2 : ℕ) : ℤ)) →
      ∀ p : ℕ, p ≤ 6 * K → p.Prime →
        p ∣ ∏ i ∈ Finset.Icc 1 ⌊Real.log n⌋₊, (n + i) := by
  exact erdos_95799_hyp_shift_ns.erdos_95799_hyp_shift



theorem erdos_95799 :
    ∃ ε > (0 : ℝ),
    { (n : ℕ) | ∀ (p : ℕ), p ≤ (2 + ε) * Real.log n → p.Prime →
      p ∣ ∏ i ∈ Finset.Icc 1 ⌊Real.log n⌋₊, (n + i) }.Infinite := by
  refine ⟨1, by norm_num, ?_⟩
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  obtain ⟨K, hKdef⟩ : ∃ K : ℕ, K = ⌈Real.exp 100⌉₊ + B + 3 := ⟨_, rfl⟩
  have hceil : Real.exp 100 ≤ (⌈Real.exp 100⌉₊ : ℝ) := Nat.le_ceil _
  have hKR : (K : ℝ) = (⌈Real.exp 100⌉₊ : ℝ) + (B : ℝ) + 3 := by
    rw [hKdef]
    first
      | (push_cast; ring)
      | push_cast
      | simp
  have hB0 : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg _
  have he100 := Real.exp_pos 100
  have hK100 : Real.exp 100 ≤ (K : ℝ) := by linarith
  have hK3 : 3 ≤ K := by omega
  have hcard := erdos_95799_hyp_cheb K hK100
  have hpar := erdos_95799_hyp_param K hK100 hcard
  have hh1 : 1 ≤ (K + 1) / 2 := by omega
  have hT1 : 1 ≤ ⌈Real.exp (K : ℝ)⌉₊ + (K + 1) / 2 := by omega
  have hP : ∀ p ∈ ePset K, Nat.Prime p ∧ 2 * ((K + 1) / 2) ≤ p := by
    intro p hp
    simp only [ePset, Finset.mem_filter, Finset.mem_Ioc] at hp
    exact ⟨hp.2, by omega⟩
  obtain ⟨m, hTm, hmL, hG⟩ := erdos_95799_hyp_count ((K + 1) / 2)
    ⌊Real.exp (2 * (K : ℝ))⌋₊ (⌈Real.exp (K : ℝ)⌉₊ + (K + 1) / 2) (ePset K) hh1 hT1 hP hpar
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = m - (((K + 1) / 2 : ℕ) : ℤ) :=
    ⟨(m - (((K + 1) / 2 : ℕ) : ℤ)).toNat, by omega⟩
  have hmn : m = (n : ℤ) + (((K + 1) / 2 : ℕ) : ℤ) := by omega
  rw [hmn] at hG
  have hn1 : ⌈Real.exp (K : ℝ)⌉₊ ≤ n := by omega
  have hnL : n < ⌊Real.exp (2 * (K : ℝ))⌋₊ := by omega
  have hexp : Real.exp (K : ℝ) ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hn1)
  have hnL' : (n : ℝ) < (⌊Real.exp (2 * (K : ℝ))⌋₊ : ℝ) := by exact_mod_cast hnL
  have hnR : (n : ℝ) < Real.exp (2 * (K : ℝ)) :=
    lt_of_lt_of_le hnL' (Nat.floor_le (Real.exp_pos _).le)
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (Real.exp_pos _) hexp
  have hlog : Real.log n < 2 * (K : ℝ) := by
    have := Real.log_lt_log hnpos hnR
    rwa [Real.log_exp] at this
  have hsh := erdos_95799_hyp_shift K n hK3 hexp hG
  have hnB : n ≤ B := (mem_upperBounds.mp hB) n (by
    rw [Set.mem_setOf_eq]
    intro p hp hpr
    have h6 : (p : ℝ) ≤ ((6 * K : ℕ) : ℝ) := by
      push_cast
      linarith
    have h6' : p ≤ 6 * K := by exact_mod_cast h6
    exact hsh p h6' hpr)
  have hnBR : (n : ℝ) ≤ (B : ℝ) := by exact_mod_cast hnB
  have hKe := Real.add_one_le_exp (K : ℝ)
  linarith
