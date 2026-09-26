open Filter

def Represents (ε : ℝ) (p : ℕ) (a : ZMod p) (s : Multiset ℕ) : Prop :=
  (∀ n ∈ s, 1 ≤ n ∧ (n : ℝ) ≤ (p : ℝ) ^ ε ∧ n.Coprime p) ∧
    (s.map fun n : ℕ ↦ (n : ZMod p)⁻¹).sum = a

noncomputable def C (ε : ℝ) : ℕ :=
  sInf {C | ∀ p : ℕ, p.Prime → ∀ a : ZMod p, ∃ s : Multiset ℕ, s.card ≤ C ∧ Represents ε p a s}

def Reach (ε : ℝ) (p : ℕ) (D : ℕ) : Set (ZMod p) :=
  {a | ∃ s : Multiset ℕ, s.card ≤ D ∧ Represents ε p a s}

-- R1: n = 1 is always admissible (1 ≤ p^ε, gcd(1,p)=1); take a.val ≤ p-1 copies of 1.
namespace erdos_85699_hyp_trivial_rep_ns
open Filter

theorem erdos_85699_hyp_trivial_rep :
    ∀ ε : ℝ, 0 < ε → ∀ p : ℕ, p.Prime → ∀ a : ZMod p,
      ∃ s : Multiset ℕ, s.card ≤ p ∧ Represents ε p a s := by
  intro ε hε p hp a
  haveI : Fact p.Prime := ⟨hp⟩
  refine ⟨Multiset.replicate a.val 1, ?_, ?_⟩
  · rw [Multiset.card_replicate]
    exact (ZMod.val_lt a).le
  · unfold Represents
    refine ⟨?_, ?_⟩
    · intro n hn
      rw [Multiset.eq_of_mem_replicate hn]
      refine ⟨le_refl _, ?_, Nat.coprime_one_left p⟩
      have h1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
      have := Real.one_le_rpow h1 hε.le
      simpa using this
    · rw [Multiset.map_replicate, Multiset.sum_replicate]
      simp only [Nat.cast_one, inv_one, nsmul_eq_mul, mul_one]
      exact ZMod.natCast_zmod_val a
end erdos_85699_hyp_trivial_rep_ns

theorem erdos_85699_hyp_trivial_rep :
    ∀ ε : ℝ, 0 < ε → ∀ p : ℕ, p.Prime → ∀ a : ZMod p,
      ∃ s : Multiset ℕ, s.card ≤ p ∧ Represents ε p a s := by
  exact erdos_85699_hyp_trivial_rep_ns.erdos_85699_hyp_trivial_rep

-- R2: p ≥ 2 gives p^ε ≤ p^ε' for ε ≤ ε' (Real.rpow_le_rpow_of_exponent_le), so the constraint only weakens.
namespace erdos_85699_hyp_mono_ns
open Filter

theorem erdos_85699_hyp_mono :
    ∀ ε ε' : ℝ, ε ≤ ε' → ∀ p : ℕ, p.Prime → ∀ a : ZMod p, ∀ s : Multiset ℕ,
      Represents ε p a s → Represents ε' p a s := by
  intro ε ε' h p hp a s hs
  obtain ⟨h1, h2⟩ := hs
  refine ⟨fun n hn => ?_, h2⟩
  obtain ⟨b1, b2, b3⟩ := h1 n hn
  refine ⟨b1, le_trans b2 ?_, b3⟩
  have hp1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.one_lt.le
  exact Real.rpow_le_rpow_of_exponent_le hp1 h
end erdos_85699_hyp_mono_ns

theorem erdos_85699_hyp_mono :
    ∀ ε ε' : ℝ, ε ≤ ε' → ∀ p : ℕ, p.Prime → ∀ a : ZMod p, ∀ s : Multiset ℕ,
      Represents ε p a s → Represents ε' p a s := by
  exact erdos_85699_hyp_mono_ns.erdos_85699_hyp_mono

-- Additivity of Reach: concatenate multisets (s + t); card and map-sum are additive
-- (Multiset.card_add, Multiset.map_add, Multiset.sum_add); admissibility is pointwise.
namespace erdos_85699_hyp_reach_add_ns
open Filter

theorem erdos_85699_hyp_reach_add :
    ∀ ε : ℝ, ∀ p D1 D2 : ℕ, ∀ a b : ZMod p,
      a ∈ Reach ε p D1 → b ∈ Reach ε p D2 → a + b ∈ Reach ε p (D1 + D2) := by
  intro ε p D1 D2 a b ha hb
  simp only [Reach, Represents, Set.mem_setOf_eq] at ha hb ⊢
  obtain ⟨s, hs, hsR, hsum⟩ := ha
  obtain ⟨t, ht, htR, htsum⟩ := hb
  refine ⟨s + t, ?_, ?_, ?_⟩
  · rw [Multiset.card_add]; omega
  · intro n hn
    rcases Multiset.mem_add.mp hn with h | h
    · exact hsR n h
    · exact htR n h
  · rw [Multiset.map_add, Multiset.sum_add, hsum, htsum]
end erdos_85699_hyp_reach_add_ns

theorem erdos_85699_hyp_reach_add :
    ∀ ε : ℝ, ∀ p D1 D2 : ℕ, ∀ a b : ZMod p,
      a ∈ Reach ε p D1 → b ∈ Reach ε p D2 → a + b ∈ Reach ε p (D1 + D2) := by
  exact erdos_85699_hyp_reach_add_ns.erdos_85699_hyp_reach_add



-- Pigeonhole in ZMod p: if 2|S| > p then S and a - S (both of size |S|) intersect,
-- giving x ∈ S, y ∈ S with x + y = a.
namespace erdos_85699_hyp_half_cover_ns
open Filter

theorem erdos_85699_hyp_half_cover :
    ∀ p : ℕ, p.Prime → ∀ S : Set (ZMod p), p < 2 * S.ncard →
      ∀ a : ZMod p, ∃ x ∈ S, ∃ y ∈ S, x + y = a := by
  intro p hp S hS a
  haveI : NeZero p := ⟨hp.ne_zero⟩
  by_contra h
  push_neg at h
  set T : Set (ZMod p) := (fun x => a - x) '' S with hT
  have hTcard : T.ncard = S.ncard :=
    Set.ncard_image_of_injective S sub_right_injective
  have hdisj : Disjoint S T := by
    rw [Set.disjoint_left]
    intro x hx hxT
    obtain ⟨y, hy, hxy⟩ := hxT
    exact h x hx y hy (by rw [← hxy]; ring)
  have h1 : (S ∪ T).ncard = S.ncard + T.ncard := Set.ncard_union_eq hdisj
  have h2 : (S ∪ T).ncard ≤ (Set.univ : Set (ZMod p)).ncard :=
    Set.ncard_le_ncard (Set.subset_univ _)
  rw [Set.ncard_univ, Nat.card_zmod] at h2
  omega
end erdos_85699_hyp_half_cover_ns

theorem erdos_85699_hyp_half_cover :
    ∀ p : ℕ, p.Prime → ∀ S : Set (ZMod p), p < 2 * S.ncard →
      ∀ a : ZMod p, ∃ x ∈ S, ∃ y ∈ S, x + y = a := by
  exact erdos_85699_hyp_half_cover_ns.erdos_85699_hyp_half_cover



-- Hard core, weakened: bounded-length sums of inverses of n ≤ p^(1/k) cover MORE THAN HALF
-- of ZMod p for large p. Expected from Bourgain-type bounds for short sums of modular inverses
-- (or sum-product growth); strictly weaker than full covering.
theorem erdos_85699_hyp_core_half :
    ∀ k : ℕ, 2 ≤ k → ∃ D N : ℕ, ∀ p : ℕ, p.Prime → N ≤ p →
      p < 2 * (Reach (1 / (k : ℝ)) p D).ncard := by
  sorry

theorem erdos_85699_hyp_core :
    ∀ k : ℕ, 2 ≤ k → ∃ C0 N : ℕ, ∀ p : ℕ, p.Prime → N ≤ p → ∀ a : ZMod p,
      ∃ s : Multiset ℕ, s.card ≤ C0 ∧ Represents (1 / (k : ℝ)) p a s := by
  intro k hk
  obtain ⟨D, N, h⟩ := erdos_85699_hyp_core_half k hk
  refine ⟨D + D, N, ?_⟩
  intro p hp hN a
  obtain ⟨x, hx, y, hy, hxy⟩ := erdos_85699_hyp_half_cover p hp _ (h p hp hN) a
  have hmem := erdos_85699_hyp_reach_add (1 / (k : ℝ)) p D D x y hx hy
  rw [hxy] at hmem
  exact hmem

theorem erdos_85699 :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℕ, ∀ p : ℕ, p.Prime → ∀ a : ZMod p,
    ∃ s : Multiset ℕ, s.card ≤ C ∧ Represents ε p a s := by
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε + 2)
  have hεinv : 0 < 1 / ε := one_div_pos.mpr hε
  have h2 : (2 : ℝ) ≤ (k : ℝ) := by linarith
  have hk2 : 2 ≤ k := by exact_mod_cast h2
  have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
  have hlt : 1 / ε < (k : ℝ) := by linarith
  have h1 : 1 < (k : ℝ) * ε := by
    rw [div_lt_iff₀ hε] at hlt
    exact hlt
  have hle : 1 / (k : ℝ) ≤ ε := by
    rw [div_le_iff₀ hkpos, mul_comm]
    exact h1.le
  obtain ⟨C0, N, hCN⟩ := erdos_85699_hyp_core k hk2
  refine ⟨max C0 N, ?_⟩
  intro p hp a
  by_cases hpN : N ≤ p
  · obtain ⟨s, hs, hrep⟩ := hCN p hp hpN a
    exact ⟨s, le_trans hs (le_max_left _ _),
      erdos_85699_hyp_mono (1 / (k : ℝ)) ε hle p hp a s hrep⟩
  · obtain ⟨s, hs, hrep⟩ := erdos_85699_hyp_trivial_rep ε hε p hp a
    have hpN' : p ≤ N := by omega
    exact ⟨s, le_trans hs (le_trans hpN' (le_max_right _ _)), hrep⟩