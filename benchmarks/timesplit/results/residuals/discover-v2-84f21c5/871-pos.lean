def GoodAt (A : Set ℕ) (f : ℕ → Bool) (n : ℕ) : Prop :=
  (∃ a ∈ A, ∃ b ∈ A, f a = true ∧ f b = true ∧ a + b = n) ∧
  (∃ a ∈ A, ∃ b ∈ A, f a = false ∧ f b = false ∧ a + b = n)

def FinitelyColourable (A : Set ℕ) : Prop :=
  ∃ N0 : ℕ, ∀ M : ℕ, ∃ f : ℕ → Bool, ∀ n, N0 ≤ n → n ≤ M → GoodAt A f n

def RepHyp (A : Set ℕ) : Prop :=
  ∀ t, ∀ᶠ n in Filter.atTop, ∃ pairs : Finset (ℕ × ℕ),
    pairs.card ≥ t ∧
      ∀ p ∈ pairs, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n ∧ p.1 ≤ p.2

def LogThick (A : Set ℕ) : Prop :=
  ∀ᶠ n in Filter.atTop, ∃ pairs : Finset (ℕ × ℕ),
    pairs.card ≥ 4 * Nat.log 2 n + 2 ∧
      ∀ p ∈ pairs, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n ∧ p.1 ≤ p.2

-- Compactness (König): GoodAt A f n depends only on f restricted to [0, n];
-- Bool^ℕ is compact, so finite-window colourings for all M give a global one.
namespace erdos_35296_hyp_compact_ns
private def Ext (A : Set ℕ) (N0 : ℕ) (s : ℕ → Bool) (k : ℕ) : Prop :=
  ∀ M : ℕ, ∃ f : ℕ → Bool, (∀ i < k, f i = s i) ∧ ∀ n, N0 ≤ n → n ≤ M → GoodAt A f n

private lemma ext_step (A : Set ℕ) (N0 : ℕ) (s : ℕ → Bool) (k : ℕ) (h : Ext A N0 s k) :
    ∃ b : Bool, Ext A N0 (fun i => if i = k then b else s i) (k+1) := by
  by_contra hne
  have h1 : ¬ Ext A N0 (fun i => if i = k then true else s i) (k+1) := fun h' => hne ⟨true, h'⟩
  have h2 : ¬ Ext A N0 (fun i => if i = k then false else s i) (k+1) := fun h' => hne ⟨false, h'⟩
  simp only [Ext, not_forall] at h1 h2
  obtain ⟨M1, hM1⟩ := h1
  obtain ⟨M2, hM2⟩ := h2
  obtain ⟨f, hfs, hfg⟩ := h (max M1 M2)
  cases hfk : f k with
  | true =>
    apply hM1
    refine ⟨f, ?_, ?_⟩
    · intro i hi
      by_cases hik : i = k
      · subst hik
        rw [if_pos rfl]
        exact hfk
      · rw [if_neg hik]
        exact hfs i (by omega)
    · intro n hn1 hn2
      exact hfg n hn1 (le_trans hn2 (le_max_left _ _))
  | false =>
    apply hM2
    refine ⟨f, ?_, ?_⟩
    · intro i hi
      by_cases hik : i = k
      · subst hik
        rw [if_pos rfl]
        exact hfk
      · rw [if_neg hik]
        exact hfs i (by omega)
    · intro n hn1 hn2
      exact hfg n hn1 (le_trans hn2 (le_max_right _ _))

private noncomputable def seqC (A : Set ℕ) (N0 : ℕ)
    (h0 : Ext A N0 (fun _ => false) 0) : (k : ℕ) → {s : ℕ → Bool // Ext A N0 s k}
  | 0 => ⟨fun _ => false, h0⟩
  | k + 1 =>
    ⟨fun i => if i = k then
        Classical.choose (ext_step A N0 (seqC A N0 h0 k).1 k (seqC A N0 h0 k).2)
      else (seqC A N0 h0 k).1 i,
     Classical.choose_spec (ext_step A N0 (seqC A N0 h0 k).1 k (seqC A N0 h0 k).2)⟩

private lemma seq_coh (A : Set ℕ) (N0 : ℕ) (h0 : Ext A N0 (fun _ => false) 0)
    (k j i : ℕ) (hi : i < k) :
    (seqC A N0 h0 (k+j)).1 i = (seqC A N0 h0 k).1 i := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [← ih]
    show (if i = k + j then _ else (seqC A N0 h0 (k+j)).1 i) = _
    rw [if_neg (by omega)]

private lemma good_congr (A : Set ℕ) (f g : ℕ → Bool) (n : ℕ) (hfg : ∀ i ≤ n, f i = g i)
    (h : GoodAt A f n) : GoodAt A g n := by
  obtain ⟨⟨a, ha, b, hb, hfa, hfb, hab⟩, ⟨c, hc, d, hd, hfc, hfd, hcd⟩⟩ := h
  refine ⟨⟨a, ha, b, hb, ?_, ?_, hab⟩, ⟨c, hc, d, hd, ?_, ?_, hcd⟩⟩
  · rw [← hfg a (by omega)]; exact hfa
  · rw [← hfg b (by omega)]; exact hfb
  · rw [← hfg c (by omega)]; exact hfc
  · rw [← hfg d (by omega)]; exact hfd

theorem erdos_35296_hyp_compact :
    ∀ (A : Set ℕ) (N0 : ℕ),
      (∀ M : ℕ, ∃ f : ℕ → Bool, ∀ n, N0 ≤ n → n ≤ M → GoodAt A f n) →
      ∃ f : ℕ → Bool, ∀ n, N0 ≤ n → GoodAt A f n := by
  intro A N0 hyp
  have h0 : Ext A N0 (fun _ => false) 0 := by
    intro M
    obtain ⟨f, hf⟩ := hyp M
    exact ⟨f, fun i hi => absurd hi (Nat.not_lt_zero _), hf⟩
  refine ⟨fun i => (seqC A N0 h0 (i+1)).1 i, ?_⟩
  intro n hn
  obtain ⟨h, hagree, hgood⟩ := (seqC A N0 h0 (n+1)).2 n
  refine good_congr A h _ n ?_ (hgood n hn le_rfl)
  intro i hi
  rw [hagree i (by omega)]
  have := seq_coh A N0 h0 (i+1) (n-i) i (by omega)
  rw [show i + 1 + (n - i) = n + 1 by omega] at this
  exact this
end erdos_35296_hyp_compact_ns

theorem erdos_35296_hyp_compact :
    ∀ (A : Set ℕ) (N0 : ℕ),
      (∀ M : ℕ, ∃ f : ℕ → Bool, ∀ n, N0 ≤ n → n ≤ M → GoodAt A f n) →
      ∃ f : ℕ → Bool, ∀ n, N0 ≤ n → GoodAt A f n := by
  exact erdos_35296_hyp_compact_ns.erdos_35296_hyp_compact



-- Erdős–Nathanson log case, finite version: at least 4·log₂ n + 1 disjoint strict pairs
-- give P(bad at n) ≤ 2(3/4)^r ≤ 2·n^{-1.66}, which is summable. Choose N0 so the tail sum
-- is below 1; then averaging over colourings of [0, M] yields a good colouring.
theorem erdos_35296_hyp_log :
    ∀ (A : Set ℕ), LogThick A → FinitelyColourable A := by
  sorry

-- Open core: r(n) → ∞ but r(n) is not eventually ≥ 4·log₂ n + 2.
-- The target asserts this case; it is not known.
theorem erdos_35296_hyp_slow :
    ∀ (A : Set ℕ), RepHyp A → ¬ LogThick A → FinitelyColourable A := by
  sorry

theorem erdos_35296 :
    ∀ (A : Set ℕ),
        (∀ᶠ n in Filter.atTop, ∃ a ∈ A, ∃ b ∈ A, a + b = n) ∧
        (∀ t, ∀ᶠ n in Filter.atTop, ∃ pairs : Finset (ℕ × ℕ),
          pairs.card ≥ t ∧
            ∀ p ∈ pairs, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n ∧ p.1 ≤ p.2) →
        ∃ (B C : Set ℕ),
          (∀ x, x ∈ A ↔ x ∈ B ∨ x ∈ C) ∧
          Disjoint B C ∧
          (∀ᶠ n in Filter.atTop, ∃ a ∈ B, ∃ b ∈ B, a + b = n) ∧
          (∀ᶠ n in Filter.atTop, ∃ a ∈ C, ∃ b ∈ C, a + b = n) := by
  intro A hA
  obtain ⟨_, h2⟩ := hA
  have hfc : FinitelyColourable A := by
    by_cases hL : LogThick A
    · exact erdos_35296_hyp_log A hL
    · exact erdos_35296_hyp_slow A h2 hL
  obtain ⟨N0, hN0⟩ := hfc
  obtain ⟨f, hf⟩ := erdos_35296_hyp_compact A N0 hN0
  refine ⟨{x | x ∈ A ∧ f x = true}, {x | x ∈ A ∧ f x = false}, ?_, ?_, ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      cases h : f x
      · exact Or.inr ⟨hx, h⟩
      · exact Or.inl ⟨hx, h⟩
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩)
      · exact hx
      · exact hx
  · rw [Set.disjoint_left]
    rintro x ⟨_, hy1⟩ ⟨_, hy2⟩
    rw [hy1] at hy2
    simp at hy2
  · rw [Filter.eventually_atTop]
    refine ⟨N0, fun n hn => ?_⟩
    obtain ⟨⟨a, ha, b, hb, hfa, hfb, hab⟩, _⟩ := hf n hn
    exact ⟨a, ⟨ha, hfa⟩, b, ⟨hb, hfb⟩, hab⟩
  · rw [Filter.eventually_atTop]
    refine ⟨N0, fun n hn => ?_⟩
    obtain ⟨_, ⟨a, ha, b, hb, hfa, hfb, hab⟩⟩ := hf n hn
    exact ⟨a, ⟨ha, hfa⟩, b, ⟨hb, hfb⟩, hab⟩