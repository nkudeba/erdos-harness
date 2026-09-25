open Set

def IsWellDistributed (x : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ k in Filter.atTop, ∀ n : ℕ,
  ∀ a b, 0 ≤ a → a ≤ b → b ≤ 1 →
    letI I := Ico a b
    let count := (Finset.Ioc n (n + k)).filter (fun m ↦ x m ∈ I)
    abs ((count.card : ℝ) - (b - a) * k) < ε * k

def IsAdmissible (H : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ h ∈ H, h % p ≠ r

def BFTConsecutivePrimesInTuples : Prop :=
  ∀ m : ℕ, ∃ K₀ : ℕ, ∀ H : Finset ℕ, IsAdmissible H → K₀ ≤ H.card →
    ∃ B : Finset ℕ, B ⊆ H ∧ B.card = m ∧
      Set.Infinite {n : ℕ | (∀ b ∈ B, (n + b).Prime) ∧
        ∀ q : ℕ, q.Prime → ∀ b₁ ∈ B, ∀ b₂ ∈ B, n + b₁ ≤ q → q ≤ n + b₂ →
          ∃ b ∈ B, q = n + b}

def SmallAdmissibleTuples : Prop :=
  ∀ α : ℝ, ∀ K : ℕ, ∃ H : Finset ℕ, H.card = K ∧ IsAdmissible H ∧
    ∀ h ∈ H, ∃ z : ℤ, |α * (h : ℝ) - (z : ℝ)| < 1 / 16

def ClusteredWindows (x : ℕ → ℝ) (δ : ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ n : ℕ, ∃ c : ℝ, ∀ m ∈ Finset.Ioc n (n + k),
    ∃ z : ℤ, |x m - c - (z : ℝ)| < δ

-- PUBLISHED: Banks, Freiberg, Turnage-Butterbaugh, "Consecutive primes in tuples", Acta Arith. 167 (2015), Theorem 1 (via Maynard–Tao)
theorem erdos_51190_hyp_bft : BFTConsecutivePrimesInTuples := by
  sorry

-- Derived (Lemma 1): W = ∏_{p≤K} p, pigeonhole t0 with ‖t0·α·W‖ < 1/(16K), H = {0, W t0, ..., (K-1) W t0};
-- all h ≡ 0 mod p ≤ K, and K elements miss a class mod p > K; ‖α h‖ ≤ i‖t0 α W‖ < 1/16.
namespace erdos_51190_hyp_small_tuples_ns
-- IMPORTS: Mathlib.NumberTheory.DiophantineApproximation.Basic
open Set

theorem erdos_51190_hyp_small_tuples : SmallAdmissibleTuples := by
  intro α K
  set ξ : ℝ := α * (K.factorial : ℝ) with hξ
  obtain ⟨t, ht0, -, ht⟩ :=
    Real.exists_nat_abs_mul_sub_round_le ξ (show 0 < 17 * K + 16 by omega)
  set D := K.factorial * t with hD
  have hDpos : 0 < D := Nat.mul_pos (Nat.factorial_pos K) ht0
  refine ⟨(Finset.range K).image (fun i => D * i), ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _
      (fun i j hij => Nat.eq_of_mul_eq_mul_left hDpos hij), Finset.card_range]
  · intro p hp
    by_cases hpK : p ≤ K
    · refine ⟨1, hp.one_lt, ?_⟩
      intro h hh
      rw [Finset.mem_image] at hh
      obtain ⟨i, -, rfl⟩ := hh
      have hdvd : p ∣ D * i :=
        Dvd.dvd.mul_right (Dvd.dvd.mul_right (Nat.dvd_factorial hp.pos hpK) t) i
      obtain ⟨c, hc⟩ := hdvd
      show D * i % p ≠ 1
      rw [hc, Nat.mul_mod_right]
      omega
    · push_neg at hpK
      by_contra hcon
      push_neg at hcon
      have hsub : Finset.range p ⊆
          ((Finset.range K).image (fun i => D * i)).image (fun h => h % p) := by
        intro r hr
        rw [Finset.mem_range] at hr
        obtain ⟨h, hh, hhr⟩ := hcon r hr
        exact Finset.mem_image.mpr ⟨h, hh, hhr⟩
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_image_le (s := (Finset.range K).image (fun i => D * i))
        (f := fun h => h % p)
      have h3 := Finset.card_image_le (s := Finset.range K) (f := fun i => D * i)
      rw [Finset.card_range] at h1 h3
      omega
  · intro h hh
    rw [Finset.mem_image] at hh
    obtain ⟨i, hi, rfl⟩ := hh
    rw [Finset.mem_range] at hi
    refine ⟨(i : ℤ) * round ((t : ℝ) * ξ), ?_⟩
    have heq : α * ((D * i : ℕ) : ℝ) - (((i : ℤ) * round ((t : ℝ) * ξ) : ℤ) : ℝ)
        = (i : ℝ) * ((t : ℝ) * ξ - (round ((t : ℝ) * ξ) : ℝ)) := by
      simp only [hD, hξ]
      push_cast
      ring
    show |α * ((D * i : ℕ) : ℝ) - (((i : ℤ) * round ((t : ℝ) * ξ) : ℤ) : ℝ)| < 1 / 16
    rw [heq, abs_mul, Nat.abs_cast]
    have hx0 : 0 ≤ |(t : ℝ) * ξ - (round ((t : ℝ) * ξ) : ℝ)| := abs_nonneg _
    rw [le_div_iff₀ (by positivity)] at ht
    push_cast at ht
    have hi' : (i : ℝ) ≤ K := by exact_mod_cast hi.le
    have hm := mul_le_mul_of_nonneg_right hi' hx0
    nlinarith
end erdos_51190_hyp_small_tuples_ns

theorem erdos_51190_hyp_small_tuples : SmallAdmissibleTuples := by
  exact erdos_51190_hyp_small_tuples_ns.erdos_51190_hyp_small_tuples



-- Derived (Lemma 2): apply BFT with m = k to a small tuple of size ≥ K₀; take n from the infinite set large;
-- the consecutive primes n+b_j are p_r,...,p_{r+k-1}; α(n+b_j) = αn + z_j + e_j with |e_j| < 1/16, so c = α n.
theorem erdos_51190_hyp_bridge :
    SmallAdmissibleTuples → BFTConsecutivePrimesInTuples →
      ∀ α : ℝ, Irrational α →
        ClusteredWindows (fun n : ℕ ↦ Int.fract (α * (n.nth Nat.Prime))) (1 / 16) := by
  sorry

-- Derived: with ε = 1/4, a window whose fractional parts lie in an arc of length 1/8 gives an interval
-- [a,b) ⊆ [0,1] (the arc, or its larger half when it wraps 0) with count − (b−a)k ≥ 3k/8, for every k ≥ 1.
namespace erdos_51190_hyp_cluster_not_wd_ns
open Set

private lemma key_not_wd (x : ℕ → ℝ) (hx : ∀ m, 0 ≤ x m ∧ x m < 1)
    (h : ClusteredWindows x (1 / 16)) : ¬ IsWellDistributed x := by
  intro hWD
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp (hWD (1/4) (by norm_num))
  obtain ⟨n, c, hc⟩ := h (K+1) (by omega)
  have bound : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      ((((Finset.Ioc n (n + (K+1))).filter (fun m ↦ x m ∈ Ico a b)).card : ℕ) : ℝ)
        < (b - a) * ((K+1 : ℕ) : ℝ) + 1/4 * ((K+1 : ℕ) : ℝ) := by
    intro a b h0 hab hb
    have h' := hK (K+1) (by omega) n a b h0 hab hb
    dsimp only at h'
    have h'' := (abs_lt.mp h').2
    have h3 : ((((Finset.Ioc n (n + (K+1))).filter (fun m ↦ x m ∈ Ico a b)).card : ℕ) : ℝ)
        - (b - a) * ((K+1 : ℕ) : ℝ) < 1/4 * ((K+1 : ℕ) : ℝ) := by
      convert h''
    linarith
  set c' := Int.fract c with hc'
  have hc0 : 0 ≤ c' := Int.fract_nonneg c
  have hc1 : c' < 1 := Int.fract_lt_one c
  set FA := (Finset.Ioc n (n + (K+1))).filter
    (fun m ↦ x m ∈ Ico (max (c' - 1/16) 0) (min (c' + 1/16) 1)) with hFA
  set FB := (Finset.Ioc n (n + (K+1))).filter
    (fun m ↦ x m ∈ Ico (min (c' + 15/16) 1) 1) with hFB
  set FC := (Finset.Ioc n (n + (K+1))).filter
    (fun m ↦ x m ∈ Ico 0 (max (c' - 15/16) 0)) with hFC
  have cover : Finset.Ioc n (n + (K+1)) ⊆ FA ∪ FB ∪ FC := by
    intro m hm
    obtain ⟨z, hz⟩ := hc m hm
    have hz' : |x m - c' - (((z + ⌊c⌋ : ℤ)) : ℝ)| < 1/16 := by
      have e : x m - c' - (((z + ⌊c⌋ : ℤ)) : ℝ) = x m - c - z := by
        rw [hc', ← Int.self_sub_floor c]; push_cast; ring
      rw [e]; exact hz
    generalize hw : z + ⌊c⌋ = w at hz'
    obtain ⟨hl, hr⟩ := abs_lt.mp hz'
    have hx0 := (hx m).1
    have hx1 := (hx m).2
    have hwlt : (w : ℝ) < 2 := by linarith
    have hwgt : (-2 : ℝ) < w := by linarith
    have hwlt' : w < 2 := by exact_mod_cast hwlt
    have hwgt' : -2 < w := by exact_mod_cast hwgt
    simp only [hFA, hFB, hFC, Finset.mem_union, Finset.mem_filter, Set.mem_Ico]
    have hcases : w = -1 ∨ w = 0 ∨ w = 1 := by omega
    rcases hcases with h1 | h1 | h1
    · have : (w : ℝ) = -1 := by rw [h1]; norm_num
      right
      exact ⟨hm, hx0, lt_max_of_lt_left (by linarith)⟩
    · have : (w : ℝ) = 0 := by rw [h1]; norm_num
      left; left
      exact ⟨hm, max_le (by linarith) hx0, lt_min (by linarith) hx1⟩
    · have : (w : ℝ) = 1 := by rw [h1]; norm_num
      left; right
      exact ⟨hm, (min_le_left _ _).trans (by linarith), hx1⟩
  have hA : (FA.card : ℝ) < (min (c' + 1/16) 1 - max (c' - 1/16) 0) * ((K+1 : ℕ) : ℝ)
      + 1/4 * ((K+1 : ℕ) : ℝ) :=
    bound (max (c' - 1/16) 0) (min (c' + 1/16) 1) (le_max_right _ _)
      (max_le (le_min (by linarith) (by linarith)) (le_min (by linarith) (by norm_num)))
      (min_le_right _ _)
  have hB : (FB.card : ℝ) < (1 - min (c' + 15/16) 1) * ((K+1 : ℕ) : ℝ)
      + 1/4 * ((K+1 : ℕ) : ℝ) :=
    bound (min (c' + 15/16) 1) 1 (le_min (by linarith) (by norm_num)) (min_le_right _ _) le_rfl
  have hC : (FC.card : ℝ) < (max (c' - 15/16) 0 - 0) * ((K+1 : ℕ) : ℝ)
      + 1/4 * ((K+1 : ℕ) : ℝ) :=
    bound 0 (max (c' - 15/16) 0) le_rfl (le_max_right _ _) (max_le (by linarith) (by norm_num))
  have lA : min (c' + 1/16) 1 - max (c' - 1/16) 0 ≤ 1/8 := by
    have := min_le_left (c' + 1/16) 1
    have := le_max_left (c' - 1/16) 0
    linarith
  have lB : 1 - min (c' + 15/16) 1 ≤ 1/16 := by
    have : 15/16 ≤ min (c' + 15/16) 1 := le_min (by linarith) (by norm_num)
    linarith
  have lC : max (c' - 15/16) 0 - 0 ≤ 1/16 := by
    have : max (c' - 15/16) 0 ≤ 1/16 := max_le (by linarith) (by norm_num)
    linarith
  have hcard : (Finset.Ioc n (n + (K+1))).card = K+1 := by simp
  have h1 := Finset.card_le_card cover
  have h2 := Finset.card_union_le (FA ∪ FB) FC
  have h3 := Finset.card_union_le FA FB
  have hsum : K + 1 ≤ FA.card + FB.card + FC.card := by omega
  have hsumR : ((K+1 : ℕ) : ℝ) ≤ (FA.card : ℝ) + FB.card + FC.card := by exact_mod_cast hsum
  have hk : (0:ℝ) < ((K+1 : ℕ) : ℝ) := by positivity
  have mA := mul_le_mul_of_nonneg_right lA hk.le
  have mB := mul_le_mul_of_nonneg_right lB hk.le
  have mC := mul_le_mul_of_nonneg_right lC hk.le
  linarith

theorem erdos_51190_hyp_cluster_not_wd :
    ∀ y : ℕ → ℝ, ClusteredWindows (fun n ↦ Int.fract (y n)) (1 / 16) →
      ¬ IsWellDistributed (fun n ↦ Int.fract (y n)) := by
  intro y hy
  exact key_not_wd (fun n ↦ Int.fract (y n))
    (fun m ↦ ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩) hy
end erdos_51190_hyp_cluster_not_wd_ns

theorem erdos_51190_hyp_cluster_not_wd :
    ∀ y : ℕ → ℝ, ClusteredWindows (fun n ↦ Int.fract (y n)) (1 / 16) →
      ¬ IsWellDistributed (fun n ↦ Int.fract (y n)) := by
  exact erdos_51190_hyp_cluster_not_wd_ns.erdos_51190_hyp_cluster_not_wd



-- Derived (R2): α = a/q makes every value a multiple of 1/q; the interval [1/(4q), 3/(4q)) is always empty,
-- so ε = 1/(4q) fails for every k ≥ 1 and every n.
namespace erdos_51190_hyp_rational_ns
-- CHECK: Rat.cast_def div_mul_cancel₀ Finset.filter_eq_empty_iff
open Set

theorem erdos_51190_hyp_rational :
    ∀ α : ℝ, ¬ Irrational α →
      ¬ IsWellDistributed (fun n : ℕ ↦ Int.fract (α * (n.nth Nat.Prime))) := by
  intro α hα hwd
  have hmem : α ∈ Set.range ((↑) : ℚ → ℝ) := by
    unfold Irrational at hα
    exact not_not.mp hα
  obtain ⟨r, hr⟩ := hmem
  have hdpos : 0 < r.den := Nat.pos_of_ne_zero r.den_nz
  have hd : (0:ℝ) < (r.den : ℝ) := by exact_mod_cast hdpos
  have hd1 : (1:ℝ) ≤ (r.den : ℝ) := by exact_mod_cast hdpos
  have hα2 : α * (r.den : ℝ) = (r.num : ℝ) := by
    rw [← hr, Rat.cast_def]
    exact div_mul_cancel₀ _ hd.ne'
  have key : ∀ x : ℕ, Int.fract (α * (x : ℝ)) ∉
      Ico (1 / (4 * (r.den : ℝ))) (3 / (4 * (r.den : ℝ))) := by
    intro x hx
    rw [Set.mem_Ico] at hx
    obtain ⟨h1, h2⟩ := hx
    have e1 := (div_le_iff₀ (by positivity : (0:ℝ) < 4 * (r.den : ℝ))).mp h1
    have e2 := (lt_div_iff₀ (by positivity : (0:ℝ) < 4 * (r.den : ℝ))).mp h2
    have hj : Int.fract (α * (x : ℝ)) * (r.den : ℝ)
        = (((r.num * (x : ℤ) - ⌊α * (x : ℝ)⌋ * (r.den : ℤ)) : ℤ) : ℝ) := by
      unfold Int.fract
      push_cast
      rw [← hα2]
      ring
    have h3 : (0:ℝ) < (((r.num * (x : ℤ) - ⌊α * (x : ℝ)⌋ * (r.den : ℤ)) : ℤ) : ℝ) := by
      rw [← hj]; nlinarith
    have h4 : (((r.num * (x : ℤ) - ⌊α * (x : ℝ)⌋ * (r.den : ℤ)) : ℤ) : ℝ) < 1 := by
      rw [← hj]; nlinarith
    have h5 : (0 : ℤ) < r.num * (x : ℤ) - ⌊α * (x : ℝ)⌋ * (r.den : ℤ) := by
      exact_mod_cast h3
    have h6 : r.num * (x : ℤ) - ⌊α * (x : ℝ)⌋ * (r.den : ℤ) < 1 := by
      exact_mod_cast h4
    omega
  have hε : (0:ℝ) < 1 / (2 * (r.den : ℝ)) := by positivity
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp (hwd (1 / (2 * (r.den : ℝ))) hε)
  have ha0 : (0:ℝ) ≤ 1 / (4 * (r.den : ℝ)) := by positivity
  have hab : 1 / (4 * (r.den : ℝ)) ≤ 3 / (4 * (r.den : ℝ)) := by
    have hp : (0:ℝ) < 1 / (4 * (r.den : ℝ)) := by positivity
    have : 3 / (4 * (r.den : ℝ)) = 3 * (1 / (4 * (r.den : ℝ))) := by ring
    linarith
  have hb1 : 3 / (4 * (r.den : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  have hKK := hK K le_rfl 0 _ _ ha0 hab hb1
  have hc : ((Finset.Ioc 0 (0 + K)).filter (fun m ↦ Int.fract (α * ((m.nth Nat.Prime : ℕ) : ℝ))
      ∈ Ico (1 / (4 * (r.den : ℝ))) (3 / (4 * (r.den : ℝ))))).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro m _
    exact key _
  simp only [] at hKK
  rw [hc] at hKK
  have hba : 3 / (4 * (r.den : ℝ)) - 1 / (4 * (r.den : ℝ)) = 1 / (2 * (r.den : ℝ)) := by
    ring
  rw [hba, Nat.cast_zero, zero_sub, abs_neg, abs_of_nonneg (by positivity)] at hKK
  linarith
end erdos_51190_hyp_rational_ns

theorem erdos_51190_hyp_rational :
    ∀ α : ℝ, ¬ Irrational α →
      ¬ IsWellDistributed (fun n : ℕ ↦ Int.fract (α * (n.nth Nat.Prime))) := by
  exact erdos_51190_hyp_rational_ns.erdos_51190_hyp_rational



theorem erdos_51190 :
    ∀ α : ℝ, ¬ IsWellDistributed (fun n ↦ Int.fract (α * (n.nth Nat.Prime))) := by
  intro α
  by_cases hα : Irrational α
  · exact erdos_51190_hyp_cluster_not_wd (fun n : ℕ => α * (n.nth Nat.Prime))
      (erdos_51190_hyp_bridge erdos_51190_hyp_small_tuples erdos_51190_hyp_bft α hα)
  · exact erdos_51190_hyp_rational α hα