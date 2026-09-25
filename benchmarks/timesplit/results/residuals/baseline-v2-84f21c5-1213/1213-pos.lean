def HasEqualIntervalSums (A : ℕ → ℕ) (s : ℕ) : Prop :=
  ∃ u v x y : ℕ, u < v ∧ v ≤ s ∧ x < y ∧ y ≤ s ∧ (u, v) ≠ (x, y) ∧
    ∑ i ∈ Finset.Ico u v, A i = ∑ i ∈ Finset.Ico x y, A i

def GoodPrefix (a K : ℕ) (A : ℕ → ℕ) (s : ℕ) : Prop :=
  0 < s ∧ A 0 = a ∧ StrictMonoOn A (Set.Iio s) ∧
    (∀ i, i + 1 < s → A (i + 1) - A i ≤ K) ∧ ¬ HasEqualIntervalSums A s

-- DERIVED (König's lemma, cf. reduction R3): GoodPrefix is prefix-closed, since fewer intervals
-- means fewer possible collisions. At index i the value A i lies in [a, a + i*K], so the tree of
-- good prefixes is finitely branching. Arbitrarily large last terms force arbitrarily long good
-- prefixes, because A (s-1) ≤ a + (s-1)K. An infinite finitely-branching tree has an infinite
-- branch, and every prefix of that branch is good.
namespace erdos_94894_hyp_compact_ns
private lemma good_congr {a K : ℕ} {A B : ℕ → ℕ} {s : ℕ} (h : ∀ i < s, A i = B i)
    (hA : GoodPrefix a K A s) : GoodPrefix a K B s := by
  obtain ⟨hs, h0, hmono, hgap, hne⟩ := hA
  refine ⟨hs, ?_, ?_, ?_, ?_⟩
  · rw [← h 0 hs]; exact h0
  · intro x hx y hy hxy
    have hx' : x < s := hx
    have hy' : y < s := hy
    rw [← h x hx', ← h y hy']
    exact hmono hx hy hxy
  · intro i hi
    rw [← h i (by omega), ← h (i+1) hi]
    exact hgap i hi
  · rintro ⟨u, v, x, y, huv, hv, hxy, hy, hne', hsum⟩
    apply hne
    refine ⟨u, v, x, y, huv, hv, hxy, hy, hne', ?_⟩
    have e1 : ∑ i ∈ Finset.Ico u v, A i = ∑ i ∈ Finset.Ico u v, B i :=
      Finset.sum_congr rfl (fun i hi => by rw [Finset.mem_Ico] at hi; exact h i (by omega))
    have e2 : ∑ i ∈ Finset.Ico x y, A i = ∑ i ∈ Finset.Ico x y, B i :=
      Finset.sum_congr rfl (fun i hi => by rw [Finset.mem_Ico] at hi; exact h i (by omega))
    rw [e1, e2]; exact hsum

private lemma good_prefix {a K : ℕ} {A : ℕ → ℕ} {s t : ℕ} (hA : GoodPrefix a K A s)
    (ht : 0 < t) (hts : t ≤ s) : GoodPrefix a K A t := by
  obtain ⟨hs, h0, hmono, hgap, hne⟩ := hA
  refine ⟨ht, h0, hmono.mono (Set.Iio_subset_Iio hts), fun i hi => hgap i (by omega), ?_⟩
  rintro ⟨u, v, x, y, huv, hv, hxy, hy, hne', hsum⟩
  exact hne ⟨u, v, x, y, huv, by omega, hxy, by omega, hne', hsum⟩

private lemma good_growth {a K : ℕ} {A : ℕ → ℕ} {s : ℕ} (hA : GoodPrefix a K A s) :
    ∀ i < s, A i ≤ a + K * i := by
  obtain ⟨hs, h0, hmono, hgap, hne⟩ := hA
  intro i
  induction i with
  | zero => intro _; simp [h0]
  | succ n ih =>
    intro hn
    have h1 := ih (by omega)
    have h2 := hgap n hn
    rw [Nat.mul_succ]; omega

private def PP (a K : ℕ) (n : ℕ) (B : ℕ → ℕ) : Prop :=
  ∀ m, ∃ s A, GoodPrefix a K A s ∧ m ≤ s ∧ ∀ i < n, A i = B i

private lemma pp_step {a K n : ℕ} {B : ℕ → ℕ} (h : PP a K n B) :
    ∃ c, PP a K (n+1) (Function.update B n c) := by
  by_contra hc
  push Not at hc
  have hc' : ∀ c, ∃ m, ∀ s A, GoodPrefix a K A s → m ≤ s →
      ∃ i < n + 1, A i ≠ Function.update B n c i := by
    intro c
    have := hc c
    unfold PP at this
    push Not at this
    exact this
  choose m hm using hc'
  obtain ⟨s, A, hG, hMs, hag⟩ := h (n + 1 + ∑ c ∈ Finset.range (a + K * n + 1), m c)
  have hcn : A n ≤ a + K * n := good_growth hG n (by omega)
  have hle : m (A n) ≤ ∑ c ∈ Finset.range (a + K * n + 1), m c :=
    Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
  obtain ⟨i, hi, hne⟩ := hm (A n) s A hG (by omega)
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
  · rw [Function.update_of_ne (by omega)] at hne
    exact hne (hag i hi)
  · subst hi
    rw [Function.update_self] at hne
    exact hne rfl

open Classical in

private noncomputable def nxt (a K : ℕ) (n : ℕ) (B : ℕ → ℕ) : ℕ → ℕ :=
  if h : PP a K n B then Function.update B n (Classical.choose (pp_step h)) else B

private noncomputable def seqB (a K : ℕ) : ℕ → (ℕ → ℕ)
  | 0 => fun _ => 0
  | n+1 => nxt a K n (seqB a K n)

private lemma sq_pp {a K : ℕ} (h0 : PP a K 0 (fun _ => 0)) : ∀ n, PP a K n (seqB a K n) := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
    show PP a K (n+1) (nxt a K n (seqB a K n))
    unfold nxt
    rw [dif_pos ih]
    exact Classical.choose_spec (pp_step ih)

private lemma nxt_agree {a K n : ℕ} {B : ℕ → ℕ} : ∀ i < n, nxt a K n B i = B i := by
  intro i hi
  unfold nxt
  split_ifs
  · rw [Function.update_of_ne (by omega)]
  · rfl

private lemma sq_stable {a K : ℕ} (n : ℕ) : ∀ k, ∀ i < n, seqB a K (n + k) i = seqB a K n i := by
  intro k
  induction k with
  | zero => intro i _; rfl
  | succ k ih =>
    intro i hi
    show nxt a K (n + k) (seqB a K (n + k)) i = _
    rw [nxt_agree i (by omega)]
    exact ih i hi

theorem erdos_94894_hyp_compact :
    ∀ a K : ℕ, 1 ≤ a → 1 ≤ K →
      (∀ f : ℕ, ∃ (s : ℕ) (A : ℕ → ℕ), GoodPrefix a K A s ∧ f < A (s - 1)) →
      ∃ A : ℕ → ℕ, ∀ s, 0 < s → GoodPrefix a K A s := by
  intro a K ha hK hf
  have h0 : PP a K 0 (fun _ => 0) := by
    intro m
    obtain ⟨s, A, hG, hlt⟩ := hf (a + K * m)
    have hs := hG.1
    have hgr := good_growth hG (s - 1) (by omega)
    refine ⟨s, A, hG, ?_, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    by_contra hms
    have : K * (s - 1) ≤ K * m := Nat.mul_le_mul_left K (by omega)
    omega
  refine ⟨fun i => seqB a K (i + 1) i, fun s hs => ?_⟩
  obtain ⟨s', A, hG, hss', hag⟩ := sq_pp h0 s s
  apply good_congr _ (good_prefix hG hs hss')
  intro i hi
  rw [hag i hi]
  have := sq_stable (a := a) (K := K) (i + 1) (s - (i + 1)) i (by omega)
  rw [show i + 1 + (s - (i + 1)) = s by omega] at this
  exact this
end erdos_94894_hyp_compact_ns

theorem erdos_94894_hyp_compact :
    ∀ a K : ℕ, 1 ≤ a → 1 ≤ K →
      (∀ f : ℕ, ∃ (s : ℕ) (A : ℕ → ℕ), GoodPrefix a K A s ∧ f < A (s - 1)) →
      ∃ A : ℕ → ℕ, ∀ s, 0 < s → GoodPrefix a K A s := by
  exact erdos_94894_hyp_compact_ns.erdos_94894_hyp_compact



-- CONJECTURE (the open core; this is the infinite-sequence form of the problem): no infinite
-- strictly increasing sequence starting at a, with gaps ≤ K, has all finite interval sums distinct.
-- Evidence: K = 1 is rigorous (f = 2a). Any constant gap d is rigorous. Exhaustive DFS closes
-- (a,K) ∈ {(1,2),(2,2),(3,2),(1,3),(2,3)}. Periodic patterns of period ≤ 3 collide early.
theorem erdos_94894_hyp_core :
    ∀ a K : ℕ, 1 ≤ a → 1 ≤ K → ¬ ∃ A : ℕ → ℕ, ∀ s, 0 < s → GoodPrefix a K A s := by
  sorry

theorem erdos_94894 :
    ∀ a K : ℕ, 1 ≤ a → 1 ≤ K → ∃ f : ℕ,
    ∀ (s : ℕ) (A : ℕ → ℕ), 0 < s → A 0 = a → StrictMonoOn A (Set.Iio s) →
      (∀ i, i + 1 < s → A (i + 1) - A i ≤ K) → f < A (s - 1) → HasEqualIntervalSums A s := by
  intro a K ha hK
  by_contra h
  apply erdos_94894_hyp_core a K ha hK
  apply erdos_94894_hyp_compact a K ha hK
  intro f
  by_contra h2
  apply h
  refine ⟨f, ?_⟩
  intro s A hs h0 hmono hgap hf
  by_contra h3
  exact h2 ⟨s, A, ⟨hs, h0, hmono, hgap, h3⟩, hf⟩