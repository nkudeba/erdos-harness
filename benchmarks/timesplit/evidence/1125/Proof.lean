-- S1: apply (H) at x = 2p - q', h = q' - p.
namespace erdos_877933_hyp_reflect_ns
theorem erdos_877933_hyp_reflect :
    ∀ (f : ℝ → ℝ), (∀ x : ℝ, ∀ h : ℝ, h > 0 → 2 * f x ≤ f (x + h) + f (x + 2 * h)) →
    ∀ ρ p q' : ℝ, p < q' → f p < ρ → f q' < ρ → f (2 * p - q') < ρ := by
  intro f hf ρ p q' hpq hp hq
  have h1 := hf (2 * p - q') (q' - p) (by linarith)
  have e1 : 2 * p - q' + (q' - p) = p := by ring
  have e2 : 2 * p - q' + 2 * (q' - p) = q' := by ring
  rw [e1, e2] at h1
  linarith
end erdos_877933_hyp_reflect_ns

theorem erdos_877933_hyp_reflect :
    ∀ (f : ℝ → ℝ), (∀ x : ℝ, ∀ h : ℝ, h > 0 → 2 * f x ≤ f (x + h) + f (x + 2 * h)) →
    ∀ ρ p q' : ℝ, p < q' → f p < ρ → f q' < ρ → f (2 * p - q') < ρ := by
  exact erdos_877933_hyp_reflect_ns.erdos_877933_hyp_reflect



-- S2: induction on j using S1.
namespace erdos_877933_hyp_progression_ns
theorem erdos_877933_hyp_progression :
    ∀ (f : ℝ → ℝ), (∀ x : ℝ, ∀ h : ℝ, h > 0 → 2 * f x ≤ f (x + h) + f (x + 2 * h)) →
    ∀ ρ q d : ℝ, 0 < d → f q < ρ → f (q + d) < ρ →
    ∀ j : ℕ, f (q - (j : ℝ) * d) < ρ ∧ f (q - (j : ℝ) * d + d) < ρ := by
  intro f hf ρ q d hd hq hqd j
  induction j with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, sub_zero]
    exact ⟨hq, hqd⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    have e1 : q - ((n+1:ℕ):ℝ) * d + d = q - (n:ℝ) * d := by push_cast; ring
    have e2 : q - ((n+1:ℕ):ℝ) * d + 2 * d = q - (n:ℝ) * d + d := by push_cast; ring
    have key := hf (q - ((n+1:ℕ):ℝ) * d) d hd
    rw [e1, e2] at key
    refine ⟨by linarith, ?_⟩
    rw [e1]
    exact h1
end erdos_877933_hyp_progression_ns

theorem erdos_877933_hyp_progression :
    ∀ (f : ℝ → ℝ), (∀ x : ℝ, ∀ h : ℝ, h > 0 → 2 * f x ≤ f (x + h) + f (x + 2 * h)) →
    ∀ ρ q d : ℝ, 0 < d → f q < ρ → f (q + d) < ρ →
    ∀ j : ℕ, f (q - (j : ℝ) * d) < ρ ∧ f (q - (j : ℝ) * d + d) < ρ := by
  exact erdos_877933_hyp_progression_ns.erdos_877933_hyp_progression



-- S3: halving, induction on k applying (H) at x_k with h = (y - x_k)/2.
namespace erdos_877933_hyp_halving_ns
theorem erdos_877933_hyp_halving :
    ∀ (f : ℝ → ℝ), (∀ x : ℝ, ∀ h : ℝ, h > 0 → 2 * f x ≤ f (x + h) + f (x + 2 * h)) →
    ∀ x y : ℝ, x < y → ∀ k : ℕ,
      f (y - (y - x) / 2 ^ k) - f y ≥ 2 ^ k * (f x - f y) ∧ y - (y - x) / 2 ^ k < y := by
  intro f hf x y hxy k
  induction k with
  | zero =>
    constructor <;> simp <;> linarith
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hd : 0 < y - x := by linarith
    have hpos : (y - x) / 2 ^ (k + 1) > 0 := by positivity
    have e0 : (y - x) / 2 ^ k = 2 * ((y - x) / 2 ^ (k + 1)) := by
      rw [pow_succ, ← div_div]; ring
    have key := hf (y - (y - x) / 2 ^ k) ((y - x) / 2 ^ (k + 1)) hpos
    have e1 : y - (y - x) / 2 ^ k + (y - x) / 2 ^ (k + 1) = y - (y - x) / 2 ^ (k + 1) := by
      linarith
    have e2 : y - (y - x) / 2 ^ k + 2 * ((y - x) / 2 ^ (k + 1)) = y := by
      linarith
    rw [e1, e2] at key
    have hpow : (2:ℝ) ^ (k + 1) * (f x - f y) = 2 * (2 ^ k * (f x - f y)) := by ring
    constructor
    · linarith
    · linarith
end erdos_877933_hyp_halving_ns

theorem erdos_877933_hyp_halving :
    ∀ (f : ℝ → ℝ), (∀ x : ℝ, ∀ h : ℝ, h > 0 → 2 * f x ≤ f (x + h) + f (x + 2 * h)) →
    ∀ x y : ℝ, x < y → ∀ k : ℕ,
      f (y - (y - x) / 2 ^ k) - f y ≥ 2 ^ k * (f x - f y) ∧ y - (y - x) / 2 ^ k < y := by
  exact erdos_877933_hyp_halving_ns.erdos_877933_hyp_halving



-- S4: one-step amplification (DST), from S2 and two applications of (H).
namespace erdos_877933_hyp_dst_ns
private lemma dst_core (f : ℝ → ℝ)
    (H : ∀ x : ℝ, ∀ h : ℝ, h > 0 → 2 * f x ≤ f (x + h) + f (x + 2 * h))
    (ρ a t d : ℝ) (hd : 0 < d) (hat : a < t) (hta : t ≤ a + d)
    (hfa : ρ < f a) (ht : f t < ρ) (ht2 : f (t + d) < ρ) :
    f (a + 2 * d) - ρ > 4 * (f a - ρ) := by
  rcases lt_or_eq_of_le hta with hlt | heq
  · have h1 := H a (t - a) (by linarith)
    rw [show a + (t - a) = t by ring, show a + 2 * (t - a) = 2 * t - a by ring] at h1
    have h2 := H (2 * t - a) (a + d - t) (by linarith)
    rw [show 2 * t - a + (a + d - t) = t + d by ring,
      show 2 * t - a + 2 * (a + d - t) = a + 2 * d by ring] at h2
    linarith
  · have h0 := H (t - d) d hd
    rw [show t - d + d = t by ring, show t - d + 2 * d = t + d by ring,
      show t - d = a by linarith] at h0
    linarith

private lemma dst_step (f : ℝ → ℝ)
    (H : ∀ x : ℝ, ∀ h : ℝ, h > 0 → 2 * f x ≤ f (x + h) + f (x + 2 * h))
    (ρ a d : ℝ) (hd : 0 < d) (hfa : ρ < f a) :
    ∀ n : ℕ, ∀ q : ℝ, a < q → q - a ≤ ((n : ℝ) + 1) * d → f q < ρ → f (q + d) < ρ →
      f (a + 2 * d) - ρ > 4 * (f a - ρ) := by
  intro n
  induction n with
  | zero =>
    intro q hq hle h1 h2
    have hle' : q ≤ a + d := by
      have : ((((0 : ℕ) : ℝ)) + 1) * d = d := by simp
      linarith
    exact dst_core f H ρ a q d hd hq hle' hfa h1 h2
  | succ n ih =>
    intro q hq hle h1 h2
    by_cases hc : q - a ≤ ((n : ℝ) + 1) * d
    · exact ih q hq hc h1 h2
    · push_neg at hc
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hnd : ((n : ℝ) + 1) * d ≥ d := by nlinarith
      have hcast : (((n + 1 : ℕ) : ℝ) + 1) * d = ((n : ℝ) + 1) * d + d := by
        push_cast; ring
      have h0 := H (q - d) d hd
      rw [show q - d + d = q by ring, show q - d + 2 * d = q + d by ring] at h0
      apply ih (q - d) (by linarith) (by linarith) (by linarith)
      rw [show q - d + d = q by ring]
      exact h1

theorem erdos_877933_hyp_dst :
    ∀ (f : ℝ → ℝ), (∀ x : ℝ, ∀ h : ℝ, h > 0 → 2 * f x ≤ f (x + h) + f (x + 2 * h)) →
    ∀ ρ a q d : ℝ, 0 < d → a < q → ρ < f a → f q < ρ → f (q + d) < ρ →
      f (a + 2 * d) - ρ > 4 * (f a - ρ) := by
  intro f H ρ a q d hd haq hfa hq hqd
  obtain ⟨n, hn⟩ := exists_nat_gt ((q - a) / d)
  have h1 : q - a < (n : ℝ) * d := (div_lt_iff₀ hd).mp hn
  have h2 : q - a ≤ ((n : ℝ) + 1) * d := by nlinarith
  exact dst_step f H ρ a d hd hfa n q haq h2 hq hqd
end erdos_877933_hyp_dst_ns

theorem erdos_877933_hyp_dst :
    ∀ (f : ℝ → ℝ), (∀ x : ℝ, ∀ h : ℝ, h > 0 → 2 * f x ≤ f (x + h) + f (x + 2 * h)) →
    ∀ ρ a q d : ℝ, 0 < d → a < q → ρ < f a → f q < ρ → f (q + d) < ρ →
      f (a + 2 * d) - ρ > 4 * (f a - ρ) := by
  exact erdos_877933_hyp_dst_ns.erdos_877933_hyp_dst



-- S5: chain lemma, induction on i ≤ K using S4.
namespace erdos_877933_hyp_chain_ns
private lemma refl_step (f : ℝ → ℝ)
    (H : ∀ x : ℝ, ∀ h : ℝ, h > 0 → 2 * f x ≤ f (x + h) + f (x + 2 * h))
    {ρ p q' : ℝ} (hp : f p < ρ) (hq : f q' < ρ) (hpq : p < q') :
    f (2 * p - q') < ρ := by
  have h := H (2 * p - q') (q' - p) (by linarith)
  rw [show 2 * p - q' + (q' - p) = p by ring,
    show 2 * p - q' + 2 * (q' - p) = q' by ring] at h
  linarith

private lemma prog_step (f : ℝ → ℝ)
    (H : ∀ x : ℝ, ∀ h : ℝ, h > 0 → 2 * f x ≤ f (x + h) + f (x + 2 * h))
    {ρ q d : ℝ} (hd : 0 < d) (h0 : f q < ρ) (h1 : f (q + d) < ρ) :
    ∀ n : ℕ, f (q - (n : ℝ) * d) < ρ ∧ f (q - (n : ℝ) * d + d) < ρ := by
  intro n
  induction n with
  | zero =>
    constructor
    · simpa using h0
    · simpa using h1
  | succ n ih =>
    have hr := refl_step f H ih.1 ih.2 (by linarith)
    have e1 : q - ((n + 1 : ℕ) : ℝ) * d = 2 * (q - (n : ℝ) * d) - (q - (n : ℝ) * d + d) := by
      push_cast; ring
    have e2 : q - ((n + 1 : ℕ) : ℝ) * d + d = q - (n : ℝ) * d := by
      push_cast; ring
    constructor
    · rw [e1]; exact hr
    · rw [e2]; exact ih.1

private lemma dst_step (f : ℝ → ℝ)
    (H : ∀ x : ℝ, ∀ h : ℝ, h > 0 → 2 * f x ≤ f (x + h) + f (x + 2 * h))
    {ρ a q d : ℝ} (ha : ρ < f a) (hd : 0 < d) (h0 : f q < ρ) (h1 : f (q + d) < ρ)
    (hqa : a < q) : f (a + 2 * d) - ρ ≥ 4 * (f a - ρ) := by
  have hnn : 0 ≤ (q - a) / d := div_nonneg (by linarith) hd.le
  obtain ⟨j, hj1, hj2⟩ : ∃ j : ℕ, (j : ℝ) ≤ (q - a) / d ∧ (q - a) / d < (j : ℝ) + 1 :=
    ⟨⌊(q - a) / d⌋₊, Nat.floor_le hnn, Nat.lt_floor_add_one _⟩
  have e1 : (j : ℝ) * d ≤ q - a := by rwa [le_div_iff₀ hd] at hj1
  have e2 : q - a < ((j : ℝ) + 1) * d := by rwa [div_lt_iff₀ hd] at hj2
  have e3 : ((j : ℝ) + 1) * d = (j : ℝ) * d + d := by ring
  obtain ⟨ht, ht'⟩ := prog_step f H hd h0 h1 j
  generalize htd : q - (j : ℝ) * d = t at ht ht'
  have hta : a ≤ t := by linarith
  have hta' : t < a + d := by linarith
  have hne : a < t := by
    rcases eq_or_lt_of_le hta with h | h
    · rw [← h] at ht; linarith
    · exact h
  have H1 := H a (t - a) (by linarith)
  rw [show a + (t - a) = t by ring, show a + 2 * (t - a) = 2 * t - a by ring] at H1
  have H2 := H (2 * t - a) (a + d - t) (by linarith)
  rw [show 2 * t - a + (a + d - t) = t + d by ring,
    show 2 * t - a + 2 * (a + d - t) = a + 2 * d by ring] at H2
  linarith

theorem erdos_877933_hyp_chain :
    ∀ (f : ℝ → ℝ), (∀ x : ℝ, ∀ h : ℝ, h > 0 → 2 * f x ≤ f (x + h) + f (x + 2 * h)) →
    ∀ ρ a : ℝ, ρ < f a → ∀ K : ℕ, ∀ q : ℕ → ℝ,
      (∀ i ≤ K, f (q i) < ρ) → (∀ i < K, q i < q (i + 1)) → q K - q 0 < q 0 - a →
      f (a + 2 * (q K - q 0)) - ρ ≥ 4 ^ K * (f a - ρ) := by
  intro f H ρ a ha K q hq hinc hK
  have hmono : ∀ n i, i + n ≤ K → q i ≤ q (i + n) := by
    intro n
    induction n with
    | zero => intro i _; simp
    | succ n ih =>
      intro i hi
      have h1 := ih i (by omega)
      have h2 := hinc (i + n) (by omega)
      rw [show i + (n + 1) = i + n + 1 by omega]
      linarith
  have hle : ∀ i ≤ K, q i ≤ q K := by
    intro i hi
    have := hmono (K - i) i (by omega)
    rwa [show i + (K - i) = K by omega] at this
  have hpos : 0 < f a - ρ := by linarith
  have key : ∀ i ≤ K, f (a + 2 * (q i - q 0)) - ρ ≥ 4 ^ i * (f a - ρ) := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have IH := ih (by omega)
      have h4 : 0 < (4:ℝ) ^ i * (f a - ρ) := mul_pos (pow_pos (by norm_num) i) hpos
      have hqi := hle i (by omega)
      have hd := hinc i (by omega)
      have hq1 : f (q i + (q (i + 1) - q i)) < ρ := by
        rw [show q i + (q (i + 1) - q i) = q (i + 1) by ring]
        exact hq (i + 1) hi
      have step := dst_step f H (ρ := ρ) (a := a + 2 * (q i - q 0)) (q := q i)
        (d := q (i + 1) - q i) (by linarith) (by linarith) (hq i (by omega)) hq1
        (by linarith)
      rw [show a + 2 * (q i - q 0) + 2 * (q (i + 1) - q i) = a + 2 * (q (i + 1) - q 0) by ring]
        at step
      have e : (4:ℝ) ^ (i + 1) * (f a - ρ) = 4 * (4 ^ i * (f a - ρ)) := by ring
      rw [e]
      linarith
  exact key K le_rfl
end erdos_877933_hyp_chain_ns

theorem erdos_877933_hyp_chain :
    ∀ (f : ℝ → ℝ), (∀ x : ℝ, ∀ h : ℝ, h > 0 → 2 * f x ≤ f (x + h) + f (x + 2 * h)) →
    ∀ ρ a : ℝ, ρ < f a → ∀ K : ℕ, ∀ q : ℕ → ℝ,
      (∀ i ≤ K, f (q i) < ρ) → (∀ i < K, q i < q (i + 1)) → q K - q 0 < q 0 - a →
      f (a + 2 * (q K - q 0)) - ρ ≥ 4 ^ K * (f a - ρ) := by
  exact erdos_877933_hyp_chain_ns.erdos_877933_hyp_chain



-- S6: a downward progression with step < v - u, started above v, hits (u, v); uses S2.
namespace erdos_877933_hyp_hit_ns
theorem erdos_877933_hyp_hit :
    ∀ (f : ℝ → ℝ), (∀ x : ℝ, ∀ h : ℝ, h > 0 → 2 * f x ≤ f (x + h) + f (x + 2 * h)) →
    ∀ ρ p p' u v : ℝ, p < p' → f p < ρ → f p' < ρ → u < v → v < p → p' - p < v - u →
      ∃ w, f w < ρ ∧ u < w ∧ w < v := by
  intro f hf ρ p p' u v hpp' hp hp' huv hvp hd
  obtain ⟨d, rfl⟩ : ∃ d, p' = p + d := ⟨p' - p, by ring⟩
  have dpos : 0 < d := by linarith
  have key : ∀ n : ℕ, f (p - (n:ℝ)*d) < ρ ∧ f (p - (n:ℝ)*d + d) < ρ := by
    intro n
    induction n with
    | zero =>
      constructor
      · simpa using hp
      · have e : p - ((0:ℕ):ℝ)*d + d = p + d := by simp
        rw [e]; exact hp'
    | succ k ih =>
      obtain ⟨h1, h2⟩ := ih
      have e2 := hf (p - ((k+1:ℕ):ℝ)*d) d dpos
      have e3 : p - ((k+1:ℕ):ℝ)*d + 2*d = p - (k:ℝ)*d + d := by push_cast; ring
      have e1 : p - ((k+1:ℕ):ℝ)*d + d = p - (k:ℝ)*d := by push_cast; ring
      rw [e3, e1] at e2
      rw [e1]
      constructor
      · linarith
      · exact h1
  have hx : 0 ≤ (p - v) / d := div_nonneg (by linarith) dpos.le
  have h1 := Nat.floor_le hx
  have h2 := Nat.lt_floor_add_one ((p - v) / d)
  have h1' : (⌊(p - v) / d⌋₊ : ℝ) * d ≤ p - v := (le_div_iff₀ dpos).mp h1
  have h2' : p - v < ((⌊(p - v) / d⌋₊ : ℝ) + 1) * d := (div_lt_iff₀ dpos).mp h2
  refine ⟨p - ((⌊(p - v) / d⌋₊ + 1 : ℕ) : ℝ) * d, (key _).1, ?_, ?_⟩
  · push_cast
    nlinarith
  · push_cast
    nlinarith
end erdos_877933_hyp_hit_ns

theorem erdos_877933_hyp_hit :
    ∀ (f : ℝ → ℝ), (∀ x : ℝ, ∀ h : ℝ, h > 0 → 2 * f x ≤ f (x + h) + f (x + 2 * h)) →
    ∀ ρ p p' u v : ℝ, p < p' → f p < ρ → f p' < ρ → u < v → v < p → p' - p < v - u →
      ∃ w, f w < ρ ∧ u < w ∧ w < v := by
  exact erdos_877933_hyp_hit_ns.erdos_877933_hyp_hit



-- S7: Bolzano–Weierstrass in neighbourhood form; from Set.Infinite.exists_accPt_of_subset_isCompact,
-- isCompact_Icc and the T1 characterisation of accumulation points.
namespace erdos_877933_hyp_accum_ns
-- CHECK: Set.Infinite.exists_accPt_of_subset_isCompact accPt_iff_nhds
theorem erdos_877933_hyp_accum :
    ∀ (A : Set ℝ) (y : ℝ), A.Infinite → A ⊆ Set.Icc y (y + 1) →
      ∃ z ∈ Set.Icc y (y + 1), ∀ ε > 0, (A ∩ Set.Ioo (z - ε) (z + ε)).Infinite := by
  intro A y hA hsub
  obtain ⟨z, hz, hacc⟩ := hA.exists_accPt_of_subset_isCompact isCompact_Icc hsub
  refine ⟨z, hz, fun ε hε => ?_⟩
  intro hfin
  have hFfin : ((A ∩ Set.Ioo (z - ε) (z + ε)) \ {z}).Finite :=
    hfin.subset (fun x hx => hx.1)
  have hU : Set.Ioo (z - ε) (z + ε) ∩ ((A ∩ Set.Ioo (z - ε) (z + ε)) \ {z})ᶜ ∈ nhds z :=
    Filter.inter_mem (Ioo_mem_nhds (by linarith) (by linarith))
      (hFfin.isClosed.isOpen_compl.mem_nhds (fun h => h.2 rfl))
  rw [accPt_iff_nhds] at hacc
  obtain ⟨w, ⟨⟨hwU, hwF⟩, hwA⟩, hwz⟩ := hacc _ hU
  exact hwF ⟨⟨hwA, hwU⟩, hwz⟩
end erdos_877933_hyp_accum_ns

theorem erdos_877933_hyp_accum :
    ∀ (A : Set ℝ) (y : ℝ), A.Infinite → A ⊆ Set.Icc y (y + 1) →
      ∃ z ∈ Set.Icc y (y + 1), ∀ ε > 0, (A ∩ Set.Ioo (z - ε) (z + ε)).Infinite := by
  exact erdos_877933_hyp_accum_ns.erdos_877933_hyp_accum



-- S8: density left of an accumulation point; from S6.
namespace erdos_877933_hyp_density_ns
private lemma prog_877933 (f : ℝ → ℝ)
    (hf : ∀ x : ℝ, ∀ h : ℝ, h > 0 → 2 * f x ≤ f (x + h) + f (x + 2 * h))
    (ρ p d : ℝ) (hd : 0 < d) (hp : f p < ρ) (hq : f (p + d) < ρ) :
    ∀ n : ℕ, f (p - n * d) < ρ ∧ f (p - n * d + d) < ρ := by
  intro n
  induction n with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, sub_zero]
    exact ⟨hp, hq⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    have key := hf (p - ((n:ℝ)+1) * d) d hd
    have e1 : p - ((n:ℝ)+1) * d + d = p - n * d := by ring
    have e2 : p - ((n:ℝ)+1) * d + 2 * d = p - n * d + d := by ring
    rw [e1, e2] at key
    push_cast
    refine ⟨by linarith, ?_⟩
    rw [e1]
    exact h1

theorem erdos_877933_hyp_density :
    ∀ (f : ℝ → ℝ), (∀ x : ℝ, ∀ h : ℝ, h > 0 → 2 * f x ≤ f (x + h) + f (x + 2 * h)) →
    ∀ ρ z : ℝ, (∀ ε > 0, ({w | f w < ρ} ∩ Set.Ioo (z - ε) (z + ε)).Infinite) →
      ∀ u v : ℝ, u < v → v ≤ z → ∃ w, f w < ρ ∧ u < w ∧ w < v := by
  classical
  intro f hf ρ z hinf u v huv hvz
  obtain ⟨v', hv'⟩ : ∃ v', v' = (u + v) / 2 := ⟨_, rfl⟩
  have hv'u : u < v' := by rw [hv']; linarith
  have hv'v : v' < v := by rw [hv']; linarith
  have hv'z : v' < z := by linarith
  obtain ⟨ε, hε⟩ : ∃ ε, ε = min ((v' - u) / 2) (z - v') := ⟨_, rfl⟩
  have hεpos : ε > 0 := by rw [hε]; exact lt_min (by linarith) (by linarith)
  have hε1 : ε ≤ (v' - u) / 2 := by rw [hε]; exact min_le_left _ _
  have hε2 : ε ≤ z - v' := by rw [hε]; exact min_le_right _ _
  have key : ∀ p q : ℝ, f p < ρ → f q < ρ → p < q → z - ε < p → q < z + ε →
      ∃ w, f w < ρ ∧ u < w ∧ w < v := by
    intro p q hp hq hpq hpz hqz
    obtain ⟨d, hd⟩ : ∃ d, d = q - p := ⟨_, rfl⟩
    have hdpos : 0 < d := by rw [hd]; linarith
    have hpd : p + d = q := by rw [hd]; ring
    have hq' : f (p + d) < ρ := by rw [hpd]; exact hq
    have hprog := prog_877933 f hf ρ p d hdpos hp hq'
    have hdsmall : d < v' - u := by rw [hd]; linarith
    have hpv : v' ≤ p := by linarith
    have hex : ∃ n : ℕ, p - n * d < v' := by
      obtain ⟨N, hN⟩ := exists_nat_gt ((p - v') / d)
      refine ⟨N, ?_⟩
      have := (div_lt_iff₀ hdpos).mp hN
      linarith
    have hn : p - (Nat.find hex : ℝ) * d < v' := Nat.find_spec hex
    have hmin : ∀ m < Nat.find hex, ¬ (p - (m:ℝ) * d < v') :=
      fun m hm => Nat.find_min hex hm
    generalize Nat.find hex = n at hn hmin
    cases n with
    | zero =>
      simp only [Nat.cast_zero, zero_mul, sub_zero] at hn
      linarith
    | succ m =>
      have h1 := hmin m (Nat.lt_succ_self m)
      push_neg at h1
      have hfm := (hprog (m+1)).1
      have e : p - ((m:ℝ)+1) * d = p - m * d - d := by ring
      push_cast at hn hfm
      refine ⟨p - ((m:ℝ)+1) * d, hfm, ?_, ?_⟩
      · rw [e]; linarith
      · linarith
  obtain ⟨x, hx, y, hy, hxy⟩ := (hinf ε hεpos).nontrivial
  have hfx : f x < ρ := hx.1
  have hfy : f y < ρ := hy.1
  have hx1 : z - ε < x := hx.2.1
  have hx2 : x < z + ε := hx.2.2
  have hy1 : z - ε < y := hy.2.1
  have hy2 : y < z + ε := hy.2.2
  rcases lt_or_gt_of_ne hxy with h | h
  · exact key x y hfx hfy h hx1 hy2
  · exact key y x hfy hfx h hy1 hx2
end erdos_877933_hyp_density_ns

theorem erdos_877933_hyp_density :
    ∀ (f : ℝ → ℝ), (∀ x : ℝ, ∀ h : ℝ, h > 0 → 2 * f x ≤ f (x + h) + f (x + 2 * h)) →
    ∀ ρ z : ℝ, (∀ ε > 0, ({w | f w < ρ} ∩ Set.Ioo (z - ε) (z + ε)).Infinite) →
      ∀ u v : ℝ, u < v → v ≤ z → ∃ w, f w < ρ ∧ u < w ∧ w < v := by
  exact erdos_877933_hyp_density_ns.erdos_877933_hyp_density



-- S9: chains of every length, induction on K from the density hypothesis (D).
namespace erdos_877933_hyp_chain_exists_ns
private lemma chain_aux (f : ℝ → ℝ) (ρ α β : ℝ)
    (hβ : f β < ρ)
    (hd : ∀ u v : ℝ, α ≤ u → u < v → v ≤ β → ∃ w, f w < ρ ∧ u < w ∧ w < v) :
    ∀ K : ℕ, 1 ≤ K → ∀ a, α ≤ a → a < β → f a < ρ →
      ∃ q : ℕ → ℝ, q 0 = a ∧ q K = β ∧ (∀ i ≤ K, f (q i) < ρ) ∧
        ∀ i < K, q i < q (i + 1) := by
  intro K hK
  induction K, hK using Nat.le_induction with
  | base =>
    intro a _ hab ha
    refine ⟨fun i => if i = 0 then a else β, by simp, by simp, ?_, ?_⟩
    · intro i hi
      by_cases h : i = 0
      · subst h; simpa using ha
      · dsimp only; rw [if_neg h]; exact hβ
    · intro i hi
      have : i = 0 := by omega
      subst this; simpa using hab
  | succ K hK ih =>
    intro a hαa hab ha
    obtain ⟨w, hw, haw, hwb⟩ := hd a β hαa hab le_rfl
    obtain ⟨q, hq0, hqK, hqf, hqm⟩ := ih w (by linarith) hwb hw
    refine ⟨fun i => if i = 0 then a else q (i-1), by simp, ?_, ?_, ?_⟩
    · have h1 : K + 1 ≠ 0 := by omega
      dsimp only; rw [if_neg h1]
      have e : K + 1 - 1 = K := by omega
      rw [e]; exact hqK
    · intro i hi
      by_cases h : i = 0
      · subst h; simpa using ha
      · dsimp only; rw [if_neg h]; exact hqf _ (by omega)
    · intro i hi
      by_cases h : i = 0
      · subst h
        have h1 : (0:ℕ) + 1 ≠ 0 := by omega
        dsimp only; rw [if_pos rfl, if_neg h1]
        have e : 0 + 1 - 1 = 0 := by omega
        rw [e, hq0]; exact haw
      · have h1 : i + 1 ≠ 0 := by omega
        dsimp only; rw [if_neg h, if_neg h1]
        have := hqm (i-1) (by omega)
        have e : i - 1 + 1 = i + 1 - 1 := by omega
        rw [e] at this; exact this

theorem erdos_877933_hyp_chain_exists :
    ∀ (f : ℝ → ℝ) (ρ α β : ℝ), α < β → f α < ρ → f β < ρ →
      (∀ u v : ℝ, α ≤ u → u < v → v ≤ β → ∃ w, f w < ρ ∧ u < w ∧ w < v) →
      ∀ K : ℕ, 1 ≤ K → ∃ q : ℕ → ℝ, q 0 = α ∧ q K = β ∧ (∀ i ≤ K, f (q i) < ρ) ∧
        ∀ i < K, q i < q (i + 1) := by
  intro f ρ α β hab hα hβ hd K hK
  exact chain_aux f ρ α β hβ hd K hK α le_rfl hab hα
end erdos_877933_hyp_chain_exists_ns

theorem erdos_877933_hyp_chain_exists :
    ∀ (f : ℝ → ℝ) (ρ α β : ℝ), α < β → f α < ρ → f β < ρ →
      (∀ u v : ℝ, α ≤ u → u < v → v ≤ β → ∃ w, f w < ρ ∧ u < w ∧ w < v) →
      ∀ K : ℕ, 1 ≤ K → ∃ q : ℕ → ℝ, q 0 = α ∧ q K = β ∧ (∀ i ≤ K, f (q i) < ρ) ∧
        ∀ i < K, q i < q (i + 1) := by
  exact erdos_877933_hyp_chain_exists_ns.erdos_877933_hyp_chain_exists



-- S10+S11: Icc y (y+1) is uncountable and is the countable union of the sets {f < N}.
namespace erdos_877933_hyp_infinite_level_ns
-- CHECK: Cardinal.mk_Icc_real Cardinal.le_aleph0_iff_set_countable Cardinal.aleph0_lt_continuum
theorem erdos_877933_hyp_infinite_level :
    ∀ (f : ℝ → ℝ) (y : ℝ), ∃ N : ℕ, ({u | f u < (N : ℝ)} ∩ Set.Icc y (y + 1)).Infinite := by
  intro f y
  by_contra h
  have hfin : ∀ N : ℕ, ({u | f u < (N : ℝ)} ∩ Set.Icc y (y + 1)).Finite := by
    intro N
    by_contra hN
    exact h ⟨N, hN⟩
  have hsub : Set.Icc y (y + 1) ⊆ ⋃ N : ℕ, ({u | f u < (N : ℝ)} ∩ Set.Icc y (y + 1)) := by
    intro u hu
    obtain ⟨N, hN⟩ := exists_nat_gt (f u)
    exact Set.mem_iUnion.mpr ⟨N, Set.mem_inter hN hu⟩
  have hc : (Set.Icc y (y + 1)).Countable :=
    (Set.countable_iUnion fun N => (hfin N).countable).mono hsub
  have hcard := Cardinal.mk_Icc_real (show y < y + 1 by linarith)
  have h2 := Cardinal.le_aleph0_iff_set_countable.mpr hc
  rw [hcard] at h2
  exact absurd h2 (not_le.mpr Cardinal.aleph0_lt_continuum)
end erdos_877933_hyp_infinite_level_ns

theorem erdos_877933_hyp_infinite_level :
    ∀ (f : ℝ → ℝ) (y : ℝ), ∃ N : ℕ, ({u | f u < (N : ℝ)} ∩ Set.Icc y (y + 1)).Infinite := by
  exact erdos_877933_hyp_infinite_level_ns.erdos_877933_hyp_infinite_level



theorem erdos_877933 :
    ∀ (f : ℝ → ℝ)
    (hf : ∀ x : ℝ, ∀ h : ℝ, h > 0 → 2 * f x ≤ f (x + h) + f (x + 2 * h)),
    Monotone f := by
  intro f hf
  intro x y hxy
  by_contra hcon
  push_neg at hcon
  have hlt : x < y := lt_of_le_of_ne hxy (fun h => by subst h; exact lt_irrefl _ hcon)
  obtain ⟨N, hN⟩ := erdos_877933_hyp_infinite_level f y
  obtain ⟨z, hzI, hz⟩ := erdos_877933_hyp_accum _ y hN Set.inter_subset_right
  have hz' : ∀ ε > 0, ({w | f w < (N : ℝ)} ∩ Set.Ioo (z - ε) (z + ε)).Infinite := by
    intro ε hε
    exact (hz ε hε).mono (fun w hw => ⟨hw.1.1, hw.2⟩)
  have hD := erdos_877933_hyp_density f hf (N : ℝ) z hz'
  have hδ : 0 < f x - f y := by linarith
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (((N : ℝ) - f y) / (f x - f y)) (by norm_num : (1 : ℝ) < 2)
  have hk' : (N : ℝ) - f y < 2 ^ k * (f x - f y) := by
    rw [div_lt_iff₀ hδ] at hk; exact hk
  obtain ⟨hk1, hk2⟩ := erdos_877933_hyp_halving f hf x y hlt k
  generalize ha : y - (y - x) / 2 ^ k = a at hk1 hk2
  have hfa : (N : ℝ) < f a := by linarith
  have haz : a < z := by linarith [hzI.1]
  obtain ⟨q0, hq0f, haq0, hq0z⟩ := hD a z haz le_rfl
  obtain ⟨qs, hqsf, hq0qs, hqsm⟩ :=
    hD q0 (min z (2 * q0 - a)) (lt_min hq0z (by linarith)) (min_le_left _ _)
  have hqs1 : qs < z := lt_of_lt_of_le hqsm (min_le_left _ _)
  have hqs2 : qs < 2 * q0 - a := lt_of_lt_of_le hqsm (min_le_right _ _)
  have hDq : ∀ u v : ℝ, q0 ≤ u → u < v → v ≤ qs → ∃ w, f w < (N : ℝ) ∧ u < w ∧ w < v :=
    fun u v _ huv hv => hD u v huv (by linarith)
  have hpos : 0 < f a - (N : ℝ) := by linarith
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt
    ((f (a + 2 * (qs - q0)) - (N : ℝ)) / (f a - (N : ℝ))) (by norm_num : (1 : ℝ) < 4)
  have hKC : f (a + 2 * (qs - q0)) - (N : ℝ) < 4 ^ K * (f a - (N : ℝ)) := by
    rw [div_lt_iff₀ hpos] at hK; exact hK
  have hX : 0 < (4 : ℝ) ^ K * (f a - (N : ℝ)) := mul_pos (by positivity) hpos
  obtain ⟨q, hq0, hqK, hqf, hqinc⟩ :=
    erdos_877933_hyp_chain_exists f (N : ℝ) q0 qs hq0qs hq0f hqsf hDq (K + 1) (by omega)
  have hch := erdos_877933_hyp_chain f hf (N : ℝ) a hfa (K + 1) q hqf hqinc
    (by rw [hqK, hq0]; linarith)
  rw [hqK, hq0] at hch
  have h4 : (4 : ℝ) ^ (K + 1) = 4 ^ K * 4 := pow_succ 4 K
  rw [h4] at hch
  nlinarith [hX, hKC, hch]