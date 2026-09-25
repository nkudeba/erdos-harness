open Set

def IsWellDistributed (x : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ k in Filter.atTop, ∀ n : ℕ,
  ∀ a b, 0 ≤ a → a ≤ b → b ≤ 1 →
    letI I := Ico a b
    let count := (Finset.Ioc n (n + k)).filter (fun m ↦ x m ∈ I)
    abs ((count.card : ℝ) - (b - a) * k) < ε * k

def HasEmptyWindows (x : ℕ → ℝ) (δ : ℝ) : Prop :=
  ∀ K : ℕ, ∃ k ≥ K, ∃ n : ℕ, ∃ a b : ℝ, 0 ≤ a ∧ a ≤ b ∧ b ≤ 1 ∧ δ ≤ b - a ∧
    ∀ m ∈ Finset.Ioc n (n + k), x m ∉ Ico a b

-- R2: for α = a/q, Int.fract(α p) ∈ {0, 1/q, ..., (q-1)/q}, so Ico (1/(3q)) (2/(3q)) is
-- missed by every term; every window (n, k) is empty, with length 1/(3q).
namespace erdos_56307_hyp_rational_empty_ns
open Set

theorem erdos_56307_hyp_rational_empty :
    ∀ a : ℤ, ∀ q : ℕ, 0 < q →
      HasEmptyWindows
        (fun n : ℕ ↦ Int.fract (((a : ℝ) / (q : ℝ)) * (n.nth Nat.Prime))) (1 / (3 * (q : ℝ))) := by
  intro a q hq K
  have hq' : (0:ℝ) < q := by exact_mod_cast hq
  have hqne : (q:ℝ) ≠ 0 := ne_of_gt hq'
  have hq1 : (1:ℝ) ≤ q := by
    have h : 1 ≤ q := hq
    exact_mod_cast h
  have h3q : (0:ℝ) < 3 * q := by linarith
  have hc0 : (0:ℝ) < 1 / (3 * q) := div_pos one_pos h3q
  have hc1 : 1 / (3 * (q:ℝ)) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have e1 : (q:ℝ) * (1 / (3 * q)) = 1 / 3 := by
    rw [mul_one_div, div_eq_iff (mul_ne_zero three_ne_zero hqne)]; ring
  have e2 : (q:ℝ) * (2 * (1 / (3 * q))) = 2 / 3 := by
    have : (q:ℝ) * (2 * (1 / (3 * q))) = 2 * ((q:ℝ) * (1 / (3 * q))) := by ring
    rw [this, e1]; norm_num
  have hc : (q:ℝ) * ((a:ℝ) / q) = a := by field_simp
  refine ⟨K, le_rfl, 0, 1 / (3 * q), 2 * (1 / (3 * q)), hc0.le, by linarith, by linarith,
    by linarith, ?_⟩
  intro m _ hm
  simp only [Set.mem_Ico] at hm
  obtain ⟨lo, hi⟩ := hm
  set y : ℝ := (a:ℝ) / q * ((Nat.nth Nat.Prime m : ℕ) : ℝ) with hy
  have hf : Int.fract y = y - ⌊y⌋ := rfl
  obtain ⟨z, hz⟩ : ∃ z : ℤ, (z:ℝ) = q * Int.fract y :=
    ⟨a * ((Nat.nth Nat.Prime m : ℕ) : ℤ) - q * ⌊y⌋, by
      rw [hf]; push_cast
      linear_combination (-((Nat.nth Nat.Prime m : ℕ) : ℝ)) * hc - (q:ℝ) * hy⟩
  have l1 := mul_le_mul_of_nonneg_left lo hq'.le
  have l2 := mul_lt_mul_of_pos_left hi hq'
  have h1 : (0:ℝ) < z := by rw [hz]; linarith
  have h2 : (z:ℝ) < 1 := by rw [hz]; linarith
  have h1' : (0:ℤ) < z := by exact_mod_cast h1
  have h2' : z < 1 := by exact_mod_cast h2
  omega
end erdos_56307_hyp_rational_empty_ns

theorem erdos_56307_hyp_rational_empty :
    ∀ a : ℤ, ∀ q : ℕ, 0 < q →
      HasEmptyWindows
        (fun n : ℕ ↦ Int.fract (((a : ℝ) / (q : ℝ)) * (n.nth Nat.Prime))) (1 / (3 * (q : ℝ))) := by
  exact erdos_56307_hyp_rational_empty_ns.erdos_56307_hyp_rational_empty



-- Hard core (Maynard 2015 + Banks–Freiberg–Maynard 2016 heuristic): for irrational α there are
-- arbitrarily long runs of consecutive primes whose values α p mod 1 cluster in an arc of length 1/5.
-- The complementary arc contains an interval of fixed length that the run misses entirely.
namespace erdos_56307_hyp_irrational_empty_ns
def ErdosAdmissible (H : Finset ℕ) : Prop :=
  ∀ ℓ : ℕ, Nat.Prime ℓ → ∃ r : ℕ, ∀ h ∈ H, ¬ ℓ ∣ (h + r)

-- PUBLISHED: Banks–Freiberg–Maynard, "On limit points of the sequence of normalized prime gaps",
-- Proc. LMS 2016 (the Maynard–Tao consecutive-primes theorem: every admissible k-tuple with k large
-- in terms of m contains m elements h'_i such that the n+h'_i are consecutive primes for infinitely
-- many n). The statement below is a weakening of it. The exact theorem number needs verification.
theorem erdos_56307_hyp_irrational_empty_hyp_consecutive_in_tuple :
    ∀ m : ℕ, ∃ k : ℕ, ∀ H : Finset ℕ, ErdosAdmissible H → k ≤ H.card →
      ∃ n j : ℕ, ∀ i : ℕ, 1 ≤ i → i ≤ m → ∃ h ∈ H, Nat.nth Nat.Prime (j + i) = n + h := by
  sorry

-- Derived: take H = {M*i : 1 ≤ i ≤ k} with M a multiple of the primorial of k.
-- Such an H is admissible: it is ≡ 0 mod ℓ for ℓ ≤ k, and has k < ℓ elements otherwise.
-- By density of {j * P * α} (α irrational), choose M with 0 ≤ fract(α M) < 1/(10k).
-- Then fract(α M i) = i * fract(α M) < 1/10.
namespace erdos_56307_hyp_irrational_empty_hyp_bohr_tuple_ns

open Set

private lemma small_fract (β ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ Int.fract ((N:ℝ) * β) < ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (1/ε)
  have hn0 : 0 < n := by
    have : (0:ℝ) < n := lt_trans (by positivity) hn
    exact_mod_cast this
  have hnr : (0:ℝ) < n := by exact_mod_cast hn0
  obtain ⟨j, q, hq, -, hqj⟩ := Real.exists_int_int_abs_mul_sub_le β hn0
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hq.le
  have hm : 0 < m := by exact_mod_cast hq
  have hsmall : 1 / ((n:ℝ) + 1) < ε := by
    rw [div_lt_iff₀ (by positivity)]
    have := (div_lt_iff₀ hε).mp hn
    nlinarith
  have hlt1 : 1 / ((n:ℝ) + 1) < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  push_cast at hqj
  have hab := abs_le.mp hqj
  rcases le_or_gt 0 ((m:ℝ) * β - j) with h0 | h0
  · refine ⟨m, hm, ?_⟩
    have hf : Int.fract ((m:ℝ) * β) = (m:ℝ) * β - j := by
      rw [Int.fract_eq_iff]
      refine ⟨h0, by linarith [hab.2], j, ?_⟩
      ring
    rw [hf]; linarith [hab.2]
  · obtain ⟨e, hedef⟩ : ∃ e : ℝ, e = -((m:ℝ) * β - j) := ⟨_, rfl⟩
    have he : 0 < e := by rw [hedef]; linarith
    have hle : e ≤ 1/((n:ℝ)+1) := by rw [hedef]; linarith [hab.1]
    have h1e : (1:ℝ) ≤ 1 / e := by
      rw [le_div_iff₀ he]; linarith
    obtain ⟨t, htdef⟩ : ∃ t : ℕ, t = ⌊1 / e⌋₊ := ⟨_, rfl⟩
    have ht1 : (t : ℝ) ≤ 1 / e := by rw [htdef]; exact Nat.floor_le (by positivity)
    have ht2 : 1 / e < (t : ℝ) + 1 := by rw [htdef]; exact Nat.lt_floor_add_one _
    have htpos : 1 ≤ t := by rw [htdef]; exact Nat.le_floor (by exact_mod_cast h1e)
    have htr : (1:ℝ) ≤ (t : ℝ) := by exact_mod_cast htpos
    have hte1 : (t : ℝ) * e ≤ 1 := by rwa [le_div_iff₀ he] at ht1
    have hte2 : 1 < ((t : ℝ) + 1) * e := by rwa [div_lt_iff₀ he] at ht2
    refine ⟨t * m, Nat.mul_pos (by omega) hm, ?_⟩
    have hf : Int.fract ((((t * m : ℕ)) : ℝ) * β) = 1 - (t : ℝ) * e := by
      rw [Int.fract_eq_iff]
      refine ⟨by linarith, by nlinarith, (t : ℤ) * j - 1, ?_⟩
      rw [hedef]
      push_cast
      ring
    rw [hf]
    nlinarith

theorem erdos_56307_hyp_irrational_empty_hyp_bohr_tuple :
    ∀ α : ℝ, Irrational α → ∀ k : ℕ, ∃ H : Finset ℕ, ErdosAdmissible H ∧ k ≤ H.card ∧
      ∀ h ∈ H, Int.fract (α * (h : ℝ)) < 1 / 10 := by
  intro α _ k
  obtain ⟨N, hN, hf⟩ := small_fract (α * (Nat.factorial k : ℝ)) (1 / (10 * ((k:ℝ) + 1)))
    (by positivity)
  have hcpos : 0 < N * Nat.factorial k := Nat.mul_pos hN (Nat.factorial_pos k)
  have hinj : Function.Injective (fun s : ℕ => s * (N * Nat.factorial k)) :=
    fun a b h => Nat.eq_of_mul_eq_mul_right hcpos h
  refine ⟨(Finset.Icc 1 k).image (fun s => s * (N * Nat.factorial k)), ?_, ?_, ?_⟩
  · intro ℓ hℓ
    by_cases hlk : ℓ ≤ k
    · refine ⟨1, ?_⟩
      intro h hh hdiv
      obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hh
      have h1 : ℓ ∣ s * (N * Nat.factorial k) :=
        Dvd.dvd.mul_left (Dvd.dvd.mul_left (Nat.dvd_factorial hℓ.pos hlk) N) s
      have := (Nat.dvd_add_right h1).mp hdiv
      exact hℓ.one_lt.ne' (Nat.dvd_one.mp this)
    · push_neg at hlk
      have hl0 : 0 < ℓ := hℓ.pos
      have hcard : (((Finset.Icc 1 k).image (fun s => s * (N * Nat.factorial k))).image
            (fun h => (ℓ - h % ℓ) % ℓ)).card < (Finset.range ℓ).card := by
        have h2 := (Finset.card_image_le (s := (Finset.Icc 1 k).image
            (fun s => s * (N * Nat.factorial k))) (f := fun h => (ℓ - h % ℓ) % ℓ))
        have h3 := (Finset.card_image_le (s := Finset.Icc 1 k)
            (f := fun s => s * (N * Nat.factorial k)))
        rw [Nat.card_Icc] at h3
        rw [Finset.card_range]
        omega
      obtain ⟨r, hr, hrn⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
      refine ⟨r, ?_⟩
      intro h hh hd
      apply hrn
      rw [Finset.mem_range] at hr
      rw [Finset.mem_image]
      refine ⟨h, hh, ?_⟩
      have ha : h % ℓ < ℓ := Nat.mod_lt _ hl0
      have hd2 : ℓ ∣ h % ℓ + r := by
        have hdm := Nat.div_add_mod h ℓ
        rw [← hdm, add_assoc] at hd
        exact (Nat.dvd_add_right (dvd_mul_right ℓ _)).mp hd
      show (ℓ - h % ℓ) % ℓ = r
      generalize h % ℓ = a at ha hd2 ⊢
      obtain ⟨e, he⟩ := hd2
      have he2 : e ≤ 1 := by
        by_contra hcon
        push_neg at hcon
        have : ℓ * 2 ≤ ℓ * e := Nat.mul_le_mul_left ℓ hcon
        omega
      interval_cases e
      · have ha0 : a = 0 := by omega
        have hr0 : r = 0 := by omega
        subst ha0; subst hr0
        simp
      · rw [Nat.mod_eq_of_lt (by omega)]
        omega
  · rw [Finset.card_image_of_injective _ hinj, Nat.card_Icc]
    omega
  · intro h hh
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hh
    rw [Finset.mem_Icc] at hs
    have hf0 := Int.fract_nonneg ((N:ℝ) * (α * (Nat.factorial k : ℝ)))
    have hsk : (s:ℝ) ≤ k := by exact_mod_cast hs.2
    have hkf : (k:ℝ) * Int.fract ((N:ℝ) * (α * (Nat.factorial k : ℝ))) < 1/10 := by
      rw [lt_div_iff₀ (by positivity)] at hf
      nlinarith
    have hsf : (s:ℝ) * Int.fract ((N:ℝ) * (α * (Nat.factorial k : ℝ))) < 1/10 := by
      have : (s:ℝ) * Int.fract ((N:ℝ) * (α * (Nat.factorial k : ℝ)))
          ≤ k * Int.fract ((N:ℝ) * (α * (Nat.factorial k : ℝ))) :=
        mul_le_mul_of_nonneg_right hsk hf0
      linarith
    have key : Int.fract (α * ((s * (N * Nat.factorial k) : ℕ) : ℝ))
        = s * Int.fract ((N:ℝ) * (α * (Nat.factorial k : ℝ))) := by
      rw [Int.fract_eq_iff]
      refine ⟨by positivity, by linarith, s * ⌊(N:ℝ) * (α * (Nat.factorial k : ℝ))⌋, ?_⟩
      unfold Int.fract
      push_cast
      ring
    rw [key]
    exact hsf

end erdos_56307_hyp_irrational_empty_hyp_bohr_tuple_ns

theorem erdos_56307_hyp_irrational_empty_hyp_bohr_tuple :
    ∀ α : ℝ, Irrational α → ∀ k : ℕ, ∃ H : Finset ℕ, ErdosAdmissible H ∧ k ≤ H.card ∧
      ∀ h ∈ H, Int.fract (α * (h : ℝ)) < 1 / 10 := by
  exact erdos_56307_hyp_irrational_empty_hyp_bohr_tuple_ns.erdos_56307_hyp_irrational_empty_hyp_bohr_tuple

-- Derived: circle geometry. Let c0 = fract c.
-- If c0 ≤ 1/2, the arc lies in [c0, c0 + 1/10), so use Ico (c0 + 1/10) 1.
-- Otherwise the arc lies in [c0, 1) ∪ [0, 1/10), so use Ico (1/10) (1/2).
namespace erdos_56307_hyp_irrational_empty_hyp_arc_gap_ns

open Set

private lemma fract_add_small_aux (c t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Int.fract (c + t) = Int.fract c + t ∨ Int.fract (c + t) = Int.fract c + t - 1 := by
  have h1 := Int.fract_nonneg (c + t)
  have h2 := Int.fract_lt_one (c + t)
  have h3 := Int.fract_nonneg c
  have h4 := Int.fract_lt_one c
  have e1 := Int.floor_add_fract (c + t)
  have e2 := Int.floor_add_fract c
  have hlt : ((⌊c + t⌋ - ⌊c⌋ : ℤ) : ℝ) < 2 := by push_cast; linarith
  have hgt : (-1 : ℝ) < ((⌊c + t⌋ - ⌊c⌋ : ℤ) : ℝ) := by push_cast; linarith
  have hlt' : ⌊c + t⌋ - ⌊c⌋ < 2 := by exact_mod_cast hlt
  have hgt' : -1 < ⌊c + t⌋ - ⌊c⌋ := by exact_mod_cast hgt
  have hcase : ⌊c + t⌋ - ⌊c⌋ = 0 ∨ ⌊c + t⌋ - ⌊c⌋ = 1 := by omega
  rcases hcase with h | h
  · left
    have hz : ⌊c + t⌋ = ⌊c⌋ := by omega
    have : (⌊c + t⌋ : ℝ) = (⌊c⌋ : ℝ) := by exact_mod_cast hz
    linarith
  · right
    have hz : ⌊c + t⌋ = ⌊c⌋ + 1 := by omega
    have : (⌊c + t⌋ : ℝ) = (⌊c⌋ : ℝ) + 1 := by exact_mod_cast hz
    linarith

theorem erdos_56307_hyp_irrational_empty_hyp_arc_gap :
    ∀ c : ℝ, ∃ a b : ℝ, 0 ≤ a ∧ a ≤ b ∧ b ≤ 1 ∧ 2 / 5 ≤ b - a ∧
      ∀ t : ℝ, 0 ≤ t → t < 1 / 10 → Int.fract (c + t) ∉ Set.Ico a b := by
  intro c
  have hf0 := Int.fract_nonneg c
  have hf1 := Int.fract_lt_one c
  by_cases h : Int.fract c < 1 / 2
  · refine ⟨Int.fract c + 1 / 10, Int.fract c + 1 / 2, by linarith, by linarith,
      by linarith, by linarith, ?_⟩
    intro t ht0 ht1 hmem
    rw [Set.mem_Ico] at hmem
    rcases fract_add_small_aux c t ht0 (by linarith) with e | e
    · rw [e] at hmem; linarith [hmem.1]
    · rw [e] at hmem; linarith [hmem.1]
  · push_neg at h
    refine ⟨Int.fract c - 1 / 2, Int.fract c - 1 / 10, by linarith, by linarith,
      by linarith, by linarith, ?_⟩
    intro t ht0 ht1 hmem
    rw [Set.mem_Ico] at hmem
    rcases fract_add_small_aux c t ht0 (by linarith) with e | e
    · rw [e] at hmem; linarith [hmem.2]
    · rw [e] at hmem; linarith [hmem.1]

end erdos_56307_hyp_irrational_empty_hyp_arc_gap_ns

theorem erdos_56307_hyp_irrational_empty_hyp_arc_gap :
    ∀ c : ℝ, ∃ a b : ℝ, 0 ≤ a ∧ a ≤ b ∧ b ≤ 1 ∧ 2 / 5 ≤ b - a ∧
      ∀ t : ℝ, 0 ≤ t → t < 1 / 10 → Int.fract (c + t) ∉ Set.Ico a b := by
  exact erdos_56307_hyp_irrational_empty_hyp_arc_gap_ns.erdos_56307_hyp_irrational_empty_hyp_arc_gap

open Set

-- CHECK: Int.fract_add_intCast
theorem erdos_56307_hyp_irrational_empty :
    ∀ α : ℝ, Irrational α → ∃ δ > 0,
      HasEmptyWindows (fun n : ℕ ↦ Int.fract (α * (n.nth Nat.Prime))) δ := by
  intro α hα
  refine ⟨2 / 5, by norm_num, ?_⟩
  intro K
  obtain ⟨k0, hk0⟩ := erdos_56307_hyp_irrational_empty_hyp_consecutive_in_tuple K
  obtain ⟨H, hadm, hcard, hfr⟩ := erdos_56307_hyp_irrational_empty_hyp_bohr_tuple α hα k0
  obtain ⟨n, j, hj⟩ := hk0 H hadm hcard
  obtain ⟨a, b, ha, hab, hb, hlen, hnot⟩ :=
    erdos_56307_hyp_irrational_empty_hyp_arc_gap (α * (n : ℝ))
  refine ⟨K, le_rfl, j, a, b, ha, hab, hb, hlen, ?_⟩
  intro m hm
  rw [Finset.mem_Ioc] at hm
  obtain ⟨h, hH, hp⟩ := hj (m - j) (by omega) (by omega)
  have hm' : j + (m - j) = m := by omega
  rw [hm'] at hp
  show Int.fract (α * ((Nat.nth Nat.Prime m : ℕ) : ℝ)) ∉ Ico a b
  rw [hp]
  have key : Int.fract (α * ((n + h : ℕ) : ℝ)) = Int.fract (α * (n : ℝ) + Int.fract (α * (h : ℝ))) := by
    have e : α * ((n + h : ℕ) : ℝ)
        = (α * (n : ℝ) + Int.fract (α * (h : ℝ))) + ((⌊α * (h : ℝ)⌋ : ℤ) : ℝ) := by
      push_cast
      rw [mul_add]
      linarith [Int.fract_add_floor (α * (h : ℝ))]
    rw [e, Int.fract_add_intCast]
  rw [key]
  exact hnot _ (Int.fract_nonneg _) (hfr h hH)
end erdos_56307_hyp_irrational_empty_ns

theorem erdos_56307_hyp_irrational_empty :
    ∀ α : ℝ, Irrational α → ∃ δ > 0,
      HasEmptyWindows (fun n : ℕ ↦ Int.fract (α * (n.nth Nat.Prime))) δ := by
  exact erdos_56307_hyp_irrational_empty_ns.erdos_56307_hyp_irrational_empty



theorem erdos_56307 :
    ∀ α : ℝ, ¬ IsWellDistributed (fun n ↦ Int.fract (α * (n.nth Nat.Prime))) := by
  have key : ∀ x : ℕ → ℝ, ∀ δ : ℝ, δ > 0 → HasEmptyWindows x δ → ¬ IsWellDistributed x := by
    intro x δ hδ hE hWD
    have hev := hWD δ hδ
    rw [Filter.eventually_atTop] at hev
    obtain ⟨K, hK⟩ := hev
    obtain ⟨k, hk, n, a, b, ha, hab, hb, hlen, hempty⟩ := hE K
    have h2 : |(((Finset.Ioc n (n + k)).filter (fun m ↦ x m ∈ Ico a b)).card : ℝ)
        - (b - a) * k| < δ * k := hK k hk n a b ha hab hb
    have hcard : ((Finset.Ioc n (n + k)).filter (fun m ↦ x m ∈ Ico a b)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro m hm
      exact hempty m hm
    rw [hcard, Nat.cast_zero, zero_sub, abs_neg] at h2
    have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    have hnn : (0:ℝ) ≤ (b - a) * k := mul_nonneg (by linarith) hk0
    rw [abs_of_nonneg hnn] at h2
    have h3 : δ * k ≤ (b - a) * k := mul_le_mul_of_nonneg_right hlen hk0
    linarith
  intro α
  by_cases hα : Irrational α
  · obtain ⟨δ, hδ, hE⟩ := erdos_56307_hyp_irrational_empty α hα
    exact key _ δ hδ hE
  · have hmem : α ∈ Set.range ((↑) : ℚ → ℝ) := by
      unfold Irrational at hα
      exact not_not.mp hα
    obtain ⟨r, rfl⟩ := hmem
    have hpos : 0 < r.den := Nat.pos_of_ne_zero r.den_nz
    have hE := erdos_56307_hyp_rational_empty r.num r.den hpos
    rw [← Rat.cast_def] at hE
    have h0 : (0:ℝ) < (r.den : ℝ) := by exact_mod_cast hpos
    exact key _ _ (div_pos one_pos (by linarith)) hE