open scoped Classical
open Filter

def RequiredCondition (A : Finset ℕ) (n : ℕ) : Prop :=
  A ⊆ Finset.Ioc 0 n ∧ ∀ᵉ (a ∈ A) (b ∈ A) (c ∈ A) (d ∈ A),
  a ≤ b → b ≤ c → c ≤ d → IsSquare (a * b * c * d) → a * d = b * c

def p (n : ℕ) (k : ℕ) : Prop := ∃ A : Finset ℕ, RequiredCondition A n ∧ A.card = k

-- CHECK: Asymptotics.IsBigO.antisymm Asymptotics.IsBigO.of_bound Nat.le_findGreatest Nat.findGreatest_spec

noncomputable def pairSet (n : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 n).filter
    (fun m => ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ r * r ≤ n ∧ n < s * s ∧ m = r * s)

-- Derived: elements r*s of pairSet n are edges of a bipartite prime graph (small prime r ≤ √n,
-- large prime s > √n, uniquely determined). A square product of four edges has all prime
-- degrees even, so it is {e,e,f,f} or a 4-cycle r1s1,r1s2,r2s1,r2s2 whose min r1s1 and max
-- r2s2 are opposite edges; in both cases ad = bc.
namespace erdos_44458_hyp_pairSet_valid_ns
open scoped Classical

open Filter

private lemma peel {t M y : ℕ} (ht : t.Prime) (h : t * M = y * y) : ∃ z, M = t * (z * z) := by
  have h1 : t ∣ y * y := ⟨M, h.symm⟩
  have h2 : t ∣ y := by
    rcases (Nat.Prime.dvd_mul ht).mp h1 with h2 | h2 <;> exact h2
  obtain ⟨z, rfl⟩ := h2
  refine ⟨z, Nat.eq_of_mul_eq_mul_left ht.pos ?_⟩
  rw [h]; ring

private lemma two_primes {u v y : ℕ} (hu : u.Prime) (hv : v.Prime) (h : u * v = y * y) : u = v := by
  obtain ⟨z, hz⟩ := peel hu h
  exact (Nat.prime_dvd_prime_iff_eq hu hv).mp ⟨z * z, hz⟩

private lemma four_primes {p1 p2 p3 p4 y : ℕ} (hp1 : p1.Prime) (hp2 : p2.Prime)
    (hp3 : p3.Prime) (hp4 : p4.Prime) (h : p1 * p2 * p3 * p4 = y * y) :
    (p1 = p2 ∧ p3 = p4) ∨ (p1 = p3 ∧ p2 = p4) ∨ (p1 = p4 ∧ p2 = p3) := by
  have h' : p1 * (p2 * p3 * p4) = y * y := by rw [← h]; ring
  obtain ⟨z, hz⟩ := peel hp1 h'
  have hd : p1 ∣ p2 * p3 * p4 := ⟨z * z, hz⟩
  rcases (Nat.Prime.dvd_mul hp1).mp hd with hd | hd
  · rcases (Nat.Prime.dvd_mul hp1).mp hd with hd | hd
    · have e := (Nat.prime_dvd_prime_iff_eq hp1 hp2).mp hd
      have h2 : p3 * p4 = z * z :=
        Nat.eq_of_mul_eq_mul_left hp1.pos (by rw [← hz, e]; ring)
      exact Or.inl ⟨e, two_primes hp3 hp4 h2⟩
    · have e := (Nat.prime_dvd_prime_iff_eq hp1 hp3).mp hd
      have h2 : p2 * p4 = z * z :=
        Nat.eq_of_mul_eq_mul_left hp1.pos (by rw [← hz, e]; ring)
      exact Or.inr (Or.inl ⟨e, two_primes hp2 hp4 h2⟩)
  · have e := (Nat.prime_dvd_prime_iff_eq hp1 hp4).mp hd
    have h2 : p2 * p3 = z * z :=
      Nat.eq_of_mul_eq_mul_left hp1.pos (by rw [← hz, e]; ring)
    exact Or.inr (Or.inr ⟨e, two_primes hp2 hp3 h2⟩)

private lemma two_sep {u v S y : ℕ} (hu : u.Prime) (hv : v.Prime) (huS : ¬ u ∣ S)
    (h : u * v * S = y * y) : u = v ∧ ∃ z, S = z * z := by
  have h' : u * (v * S) = y * y := by rw [← h]; ring
  obtain ⟨z, hz⟩ := peel hu h'
  have hd : u ∣ v * S := ⟨z * z, hz⟩
  rcases (Nat.Prime.dvd_mul hu).mp hd with hd | hd
  · have e := (Nat.prime_dvd_prime_iff_eq hu hv).mp hd
    refine ⟨e, z, ?_⟩
    rw [e] at hz
    exact Nat.eq_of_mul_eq_mul_left hv.pos hz
  · exact absurd hd huS

private lemma four_sep {r1 r2 r3 r4 S y : ℕ} (hr1 : r1.Prime) (hr2 : r2.Prime)
    (hr3 : r3.Prime) (hr4 : r4.Prime)
    (h1S : ¬ r1 ∣ S) (h2S : ¬ r2 ∣ S) (h3S : ¬ r3 ∣ S) (_h4S : ¬ r4 ∣ S)
    (h : r1 * r2 * r3 * r4 * S = y * y) :
    ((r1 = r2 ∧ r3 = r4) ∨ (r1 = r3 ∧ r2 = r4) ∨ (r1 = r4 ∧ r2 = r3)) ∧ ∃ z, S = z * z := by
  have h' : r1 * (r2 * r3 * r4 * S) = y * y := by rw [← h]; ring
  obtain ⟨z, hz⟩ := peel hr1 h'
  have hd : r1 ∣ r2 * r3 * r4 * S := ⟨z * z, hz⟩
  rcases (Nat.Prime.dvd_mul hr1).mp hd with hd | hd
  · rcases (Nat.Prime.dvd_mul hr1).mp hd with hd | hd
    · rcases (Nat.Prime.dvd_mul hr1).mp hd with hd | hd
      · have e := (Nat.prime_dvd_prime_iff_eq hr1 hr2).mp hd
        have h2 : r3 * r4 * S = z * z :=
          Nat.eq_of_mul_eq_mul_left hr1.pos (by rw [← hz, e]; ring)
        obtain ⟨e', hS⟩ := two_sep hr3 hr4 h3S h2
        exact ⟨Or.inl ⟨e, e'⟩, hS⟩
      · have e := (Nat.prime_dvd_prime_iff_eq hr1 hr3).mp hd
        have h2 : r2 * r4 * S = z * z :=
          Nat.eq_of_mul_eq_mul_left hr1.pos (by rw [← hz, e]; ring)
        obtain ⟨e', hS⟩ := two_sep hr2 hr4 h2S h2
        exact ⟨Or.inr (Or.inl ⟨e, e'⟩), hS⟩
    · have e := (Nat.prime_dvd_prime_iff_eq hr1 hr4).mp hd
      have h2 : r2 * r3 * S = z * z :=
        Nat.eq_of_mul_eq_mul_left hr1.pos (by rw [← hz, e]; ring)
      obtain ⟨e', hS⟩ := two_sep hr2 hr3 h2S h2
      exact ⟨Or.inr (Or.inr ⟨e, e'⟩), hS⟩
  · exact absurd hd h1S

private lemma small_not_dvd_large {r s n : ℕ} (hr : r.Prime) (hrn : r * r ≤ n)
    (hs : s.Prime) (hsn : n < s * s) : ¬ r ∣ s := by
  intro h
  have e := (Nat.prime_dvd_prime_iff_eq hr hs).mp h
  rw [e] at hrn
  exact absurd (lt_of_le_of_lt hrn hsn) (lt_irrefl _)

private lemma small_not_dvd_S {r s1 s2 s3 s4 n : ℕ} (hr : r.Prime) (hrn : r * r ≤ n)
    (hs1 : s1.Prime) (hs1n : n < s1 * s1) (hs2 : s2.Prime) (hs2n : n < s2 * s2)
    (hs3 : s3.Prime) (hs3n : n < s3 * s3) (hs4 : s4.Prime) (hs4n : n < s4 * s4) :
    ¬ r ∣ s1 * s2 * s3 * s4 := by
  intro h
  rcases (Nat.Prime.dvd_mul hr).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
      · exact small_not_dvd_large hr hrn hs1 hs1n h
      · exact small_not_dvd_large hr hrn hs2 hs2n h
    · exact small_not_dvd_large hr hrn hs3 hs3n h
  · exact small_not_dvd_large hr hrn hs4 hs4n h

private lemma cr {x y u v : ℕ} (hu : 0 < u) (hv : 0 < v) (h1 : x * u ≤ y * u)
    (h2 : y * v ≤ x * v) : x = y := by
  have a1 : x ≤ y := by
    by_contra hc
    push_neg at hc
    nlinarith
  have a2 : y ≤ x := by
    by_contra hc
    push_neg at hc
    nlinarith
  omega

private lemma cl {x y u v : ℕ} (hu : 0 < u) (hv : 0 < v) (h1 : u * x ≤ u * y)
    (h2 : v * y ≤ v * x) : x = y := by
  have a1 : x ≤ y := by
    by_contra hc
    push_neg at hc
    nlinarith
  have a2 : y ≤ x := by
    by_contra hc
    push_neg at hc
    nlinarith
  omega

theorem erdos_44458_hyp_pairSet_valid : ∀ n : ℕ, RequiredCondition (pairSet n) n := by
  intro n
  unfold RequiredCondition
  refine ⟨fun x hx => ?_, ?_⟩
  · simp only [pairSet, Finset.mem_filter] at hx
    exact hx.1
  intro a ha b hb c hc d hd hab hbc hcd hsq
  simp only [pairSet, Finset.mem_filter] at ha hb hc hd
  obtain ⟨_, r1, s1, hr1, hs1, hr1n, hs1n, rfl⟩ := ha
  obtain ⟨_, r2, s2, hr2, hs2, hr2n, hs2n, rfl⟩ := hb
  obtain ⟨_, r3, s3, hr3, hs3, hr3n, hs3n, rfl⟩ := hc
  obtain ⟨_, r4, s4, hr4, hs4, hr4n, hs4n, rfl⟩ := hd
  obtain ⟨y, hy⟩ := hsq
  have h8 : r1 * r2 * r3 * r4 * (s1 * s2 * s3 * s4) = y * y := by rw [← hy]; ring
  obtain ⟨hrp, hS⟩ := four_sep hr1 hr2 hr3 hr4
    (small_not_dvd_S hr1 hr1n hs1 hs1n hs2 hs2n hs3 hs3n hs4 hs4n)
    (small_not_dvd_S hr2 hr2n hs1 hs1n hs2 hs2n hs3 hs3n hs4 hs4n)
    (small_not_dvd_S hr3 hr3n hs1 hs1n hs2 hs2n hs3 hs3n hs4 hs4n)
    (small_not_dvd_S hr4 hr4n hs1 hs1n hs2 hs2n hs3 hs3n hs4 hs4n) h8
  obtain ⟨z, hz⟩ := hS
  have hsp := four_primes hs1 hs2 hs3 hs4 hz
  have hr1p := hr1.pos
  have hr2p := hr2.pos
  have hr3p := hr3.pos
  have hr4p := hr4.pos
  have hs1p := hs1.pos
  have hs2p := hs2.pos
  have hs3p := hs3.pos
  have hs4p := hs4.pos
  have hac := le_trans hab hbc
  have hbd := le_trans hbc hcd
  rcases hrp with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
  rcases hsp with ⟨f1, f2⟩ | ⟨f1, f2⟩ | ⟨f1, f2⟩ <;>
  (subst e1; subst e2; subst f1; subst f2) <;>
  first
  | ring1
  | (rw [le_antisymm hab hbd])
  | (have e := cr (by assumption) (by assumption) hab hcd; subst e; ring1)
  | (have e := cl (by assumption) (by assumption) hab hcd; subst e; ring1)
  | (have e := cr (by assumption) (by assumption) hac hbd; subst e; ring1)
  | (have e := cl (by assumption) (by assumption) hac hbd; subst e; ring1)
end erdos_44458_hyp_pairSet_valid_ns

theorem erdos_44458_hyp_pairSet_valid : ∀ n : ℕ, RequiredCondition (pairSet n) n := by
  exact erdos_44458_hyp_pairSet_valid_ns.erdos_44458_hyp_pairSet_valid



-- Derived from Chebyshev's bound π(x) ≫ x/log x and Mertens' Σ_{p≤x} 1/p = log log x + O(1):
-- |pairSet n| = Σ_{r ≤ √n} (π(n/r) − π(√n)) ≥ (n/(2 log n)) Σ_{r≤√n} 1/r − π(√n)^2.
theorem erdos_44458_hyp_pairSet_large :
    (fun n : ℕ ↦ (n : ℝ) * Real.log (Real.log n) / Real.log n) =O[atTop]
      (fun n : ℕ ↦ ((pairSet n).card : ℝ)) := by
  sorry

-- Hard core (upper bound). A counterexample to the target must violate exactly this,
-- since the two hypotheses above give the Omega side.
theorem erdos_44458_hyp_upper :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℕ, RequiredCondition A n →
      (A.card : ℝ) ≤ C * ((n : ℝ) * Real.log (Real.log n) / Real.log n) := by
  sorry

theorem erdos_44458 :
    (fun n : ℕ ↦ (Nat.findGreatest (p n) n : ℝ)) =Θ[atTop]
      (fun n : ℕ ↦ (n : ℝ) * Real.log (Real.log n) / Real.log n) := by
  obtain ⟨C, hC⟩ := erdos_44458_hyp_upper
  have hle : ∀ n : ℕ, ∀ A : Finset ℕ, RequiredCondition A n →
      A.card ≤ Nat.findGreatest (p n) n := by
    intro n A hA
    apply Nat.le_findGreatest
    · calc A.card ≤ (Finset.Ioc 0 n).card := Finset.card_le_card hA.1
        _ = n := by simp
    · exact ⟨A, hA, rfl⟩
  have hspec : ∀ n : ℕ, p n (Nat.findGreatest (p n) n) := by
    intro n
    apply Nat.findGreatest_spec (Nat.zero_le n)
    refine ⟨∅, ⟨Finset.empty_subset _, ?_⟩, rfl⟩
    intro a ha
    simp at ha
  refine Asymptotics.IsBigO.antisymm ?_ ?_
  · apply Asymptotics.IsBigO.of_bound |C|
    filter_upwards [hC] with n hn
    obtain ⟨A, hA, hcard⟩ := hspec n
    have h1 := hn A hA
    rw [hcard] at h1
    show ‖(Nat.findGreatest (p n) n : ℝ)‖ ≤
      |C| * ‖(n : ℝ) * Real.log (Real.log n) / Real.log n‖
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg (Nat.findGreatest (p n) n))]
    calc (Nat.findGreatest (p n) n : ℝ)
        ≤ C * ((n : ℝ) * Real.log (Real.log n) / Real.log n) := h1
      _ ≤ |C * ((n : ℝ) * Real.log (Real.log n) / Real.log n)| := le_abs_self _
      _ = |C| * |(n : ℝ) * Real.log (Real.log n) / Real.log n| := abs_mul _ _
  · apply erdos_44458_hyp_pairSet_large.trans
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards with n
    show ‖((pairSet n).card : ℝ)‖ ≤ 1 * ‖(Nat.findGreatest (p n) n : ℝ)‖
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg (pairSet n).card),
      abs_of_nonneg (Nat.cast_nonneg (Nat.findGreatest (p n) n)), one_mul]
    exact_mod_cast hle n _ (erdos_44458_hyp_pairSet_valid n)