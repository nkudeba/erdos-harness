import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic

set_option maxHeartbeats 1000000
set_option autoImplicit false

def HasEqualIntervalSums (A : ℕ → ℕ) (s : ℕ) : Prop :=
  ∃ u v x y : ℕ, u < v ∧ v ≤ s ∧ x < y ∧ y ≤ s ∧ (u, v) ≠ (x, y) ∧
    ∑ i ∈ Finset.Ico u v, A i = ∑ i ∈ Finset.Ico x y, A i

def erdos59388WinSum (A : ℕ → ℕ) (i L : ℕ) : ℕ :=
  ∑ t ∈ Finset.Ico i (i + L), A t

def erdos59388WinCount (A : ℕ → ℕ) (s L X D : ℕ) : ℕ :=
  ((Finset.range (s + 1 - L)).filter
    (fun i => X ≤ erdos59388WinSum A i L ∧ erdos59388WinSum A i L < X + D)).card

-- Derived (pigeonhole): the pairs (L,i) with 1 ≤ L ≤ N and i + L ≤ s give pairwise distinct
-- intervals Ico i (i+L). If more than D of them have window sum in [X, X+D), which contains
-- only D integers, two of them share a sum.
namespace erdos_59388_hyp_pigeon_ns
theorem erdos_59388_hyp_pigeon :
    ∀ (A : ℕ → ℕ) (s N X D : ℕ),
      D < ∑ L ∈ Finset.Icc 1 N, erdos59388WinCount A s L X D → HasEqualIntervalSums A s := by
  intro A s N X D h
  let S : Finset (Σ _ : ℕ, ℕ) := (Finset.Icc 1 N).sigma (fun L =>
    (Finset.range (s + 1 - L)).filter
      (fun i => X ≤ erdos59388WinSum A i L ∧ erdos59388WinSum A i L < X + D))
  have hcard : S.card = ∑ L ∈ Finset.Icc 1 N, erdos59388WinCount A s L X D := by
    rw [Finset.card_sigma]; rfl
  have hmaps : Set.MapsTo (fun p : (Σ _ : ℕ, ℕ) => erdos59388WinSum A p.2 p.1)
      (S : Set (Σ _ : ℕ, ℕ)) (Finset.Ico X (X + D) : Set ℕ) := by
    rintro ⟨L, i⟩ hp
    have hp' := Finset.mem_sigma.1 hp
    rw [Finset.mem_filter] at hp'
    exact Finset.mem_Ico.2 hp'.2.2
  have hlt : (Finset.Ico X (X + D)).card < S.card := by
    rw [Nat.card_Ico, hcard]; omega
  obtain ⟨p, hp, q, hq, hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
  obtain ⟨L, i⟩ := p
  obtain ⟨L', i'⟩ := q
  have hp' := Finset.mem_sigma.1 hp
  have hq' := Finset.mem_sigma.1 hq
  rw [Finset.mem_filter, Finset.mem_range] at hp' hq'
  rw [Finset.mem_Icc] at hp' hq'
  simp only at heq hp' hq'
  refine ⟨i, i + L, i', i' + L', by omega, by omega, by omega, by omega, ?_, heq⟩
  intro hh
  simp only [Prod.mk.injEq] at hh
  obtain ⟨h1, h2⟩ := hh
  subst h1
  obtain rfl : L = L' := by omega
  exact hne rfl
end erdos_59388_hyp_pigeon_ns

theorem erdos_59388_hyp_pigeon :
    ∀ (A : ℕ → ℕ) (s N X D : ℕ),
      D < ∑ L ∈ Finset.Icc 1 N, erdos59388WinCount A s L X D → HasEqualIntervalSums A s := by
  exact erdos_59388_hyp_pigeon_ns.erdos_59388_hyp_pigeon



-- Derived (harmonic bound): 2KN/(KL) = 2N/L in ℕ, and ∑_{L ≤ N} ⌊2N/L⌋ ≥ 2N·H_N − N.
-- With N = 4^K we have H_N ≥ K + 1, so the sum is at least 2KN + N > 2KN.
namespace erdos_59388_hyp_harmonic_ns
private lemma blk (e n : ℕ) (h : n ≤ e) :
    2 ^ (e + 1) + n * 2 ^ e ≤ ∑ L ∈ Finset.Ioc 0 (2 ^ n), 2 ^ (e + 1) / L := by
  induction n with
  | zero =>
    have h1 : Finset.Ioc 0 (2 ^ 0) = {1} := by
      ext x; simp only [Finset.mem_Ioc, Finset.mem_singleton, pow_zero]; omega
    rw [h1, Finset.sum_singleton]
    simp
  | succ n ih =>
    have ih' := ih (by omega)
    rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le (2 ^ n))
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ n))]
    have hblock : 2 ^ e ≤ ∑ L ∈ Finset.Ioc (2 ^ n) (2 ^ (n + 1)), 2 ^ (e + 1) / L := by
      have hc : ∀ L ∈ Finset.Ioc (2 ^ n) (2 ^ (n + 1)), 2 ^ (e - n) ≤ 2 ^ (e + 1) / L := by
        intro L hL
        rw [Finset.mem_Ioc] at hL
        rw [Nat.le_div_iff_mul_le (by omega)]
        calc 2 ^ (e - n) * L ≤ 2 ^ (e - n) * 2 ^ (n + 1) := Nat.mul_le_mul_left _ hL.2
          _ = 2 ^ (e + 1) := by rw [← pow_add]; congr 1; omega
      have hs := Finset.card_nsmul_le_sum _ _ _ hc
      rw [Nat.card_Ioc, smul_eq_mul] at hs
      have h2 : (2 ^ (n + 1) - 2 ^ n) * 2 ^ (e - n) = 2 ^ e := by
        rw [pow_succ, show 2 ^ n * 2 - 2 ^ n = 2 ^ n by omega, ← pow_add]
        congr 1; omega
      rw [h2] at hs
      exact hs
    have h3 : (n + 1) * 2 ^ e = n * 2 ^ e + 2 ^ e := by ring
    rw [h3]
    linarith

theorem erdos_59388_hyp_harmonic :
    ∀ K : ℕ, 1 ≤ K →
      2 * K * 4 ^ K < ∑ L ∈ Finset.Icc 1 (4 ^ K), 2 * K * 4 ^ K / (K * L) := by
  intro K hK
  have hN : (4:ℕ) ^ K = 2 ^ (2 * K) := by rw [pow_mul]; norm_num
  have hterm : ∀ L ∈ Finset.Icc 1 (4 ^ K), 2 * K * 4 ^ K / (K * L) = 2 ^ (2 * K + 1) / L := by
    intro L _
    rw [show 2 * K * 4 ^ K = K * (2 * 4 ^ K) by ring,
      Nat.mul_div_mul_left _ _ (by omega : 0 < K), hN, pow_succ]
    congr 1; ring
  rw [Finset.sum_congr rfl hterm]
  have hI : Finset.Icc 1 (4 ^ K) = Finset.Ioc 0 (2 ^ (2 * K)) := by
    rw [hN]; ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [hI]
  have hb := blk (2 * K) (2 * K) le_rfl
  rw [hN]
  have hp : 0 < 2 ^ (2 * K + 1) := by positivity
  nlinarith
end erdos_59388_hyp_harmonic_ns

theorem erdos_59388_hyp_harmonic :
    ∀ K : ℕ, 1 ≤ K →
      2 * K * 4 ^ K < ∑ L ∈ Finset.Icc 1 (4 ^ K), 2 * K * 4 ^ K / (K * L) := by
  exact erdos_59388_hyp_harmonic_ns.erdos_59388_hyp_harmonic



-- Derived (window walk): the gaps lie in [1,K], so A i ≤ a + K i, and s − 1 > N forces L < s.
-- The windows W_L(i) are strictly increasing in i with steps at most K·L.
-- They start at W_L(0) ≤ L a + K L² ≤ X and end at W_L(s−L) ≥ A(s−1) > X + D.
-- Hence at least ⌊D/(KL)⌋ of them land in [X, X+D).
namespace erdos_59388_hyp_window_count_ns
private lemma walk_count (c : ℕ) (hc : 0 < c) : ∀ (n : ℕ) (f : ℕ → ℕ) (X D : ℕ),
    (∀ i < n, f i ≤ f (i+1) ∧ f (i+1) ≤ f i + c) → f 0 < X + c → X + D ≤ f n →
    D / c ≤ ∑ i ∈ Finset.range (n+1), (if X ≤ f i ∧ f i < X + D then 1 else 0) := by
  intro n
  induction n with
  | zero =>
    intro f X D _ h0 hn
    have hD : D < c := by omega
    rw [Nat.div_eq_of_lt hD]; exact Nat.zero_le _
  | succ n ih =>
    intro f X D hstep h0 hn
    have h01 : f 0 ≤ f 1 ∧ f 1 ≤ f 0 + c := hstep 0 (by omega)
    have hstep' : ∀ i < n, (fun j => f (j+1)) i ≤ (fun j => f (j+1)) (i+1) ∧
        (fun j => f (j+1)) (i+1) ≤ (fun j => f (j+1)) i + c :=
      fun i hi => hstep (i+1) (by omega)
    rw [Finset.sum_range_succ']
    by_cases hX : X ≤ f 0
    · by_cases hD : D < c
      · rw [Nat.div_eq_of_lt hD]; exact Nat.zero_le _
      · have ih' : (D - c) / c ≤ ∑ i ∈ Finset.range (n+1),
            (if X + c ≤ f (i+1) ∧ f (i+1) < X + c + (D - c) then 1 else 0) :=
          ih (fun j => f (j+1)) (X + c) (D - c) hstep' (show f 1 < X + c + c by omega)
            (show X + c + (D - c) ≤ f (n+1) by omega)
        have hmono : (∑ i ∈ Finset.range (n+1),
            (if X + c ≤ f (i+1) ∧ f (i+1) < X + c + (D - c) then 1 else 0)) ≤
            ∑ i ∈ Finset.range (n+1), (if X ≤ f (i+1) ∧ f (i+1) < X + D then 1 else 0) :=
          Finset.sum_le_sum (fun i _ => by split_ifs <;> omega)
        have hdiv : (D - c + c) / c = (D - c) / c + 1 := Nat.add_div_right (D - c) hc
        have hDc : D - c + c = D := by omega
        rw [hDc] at hdiv
        rw [if_pos (show X ≤ f 0 ∧ f 0 < X + D from ⟨hX, by omega⟩)]
        omega
    · have ih' : D / c ≤ ∑ i ∈ Finset.range (n+1),
          (if X ≤ f (i+1) ∧ f (i+1) < X + D then 1 else 0) :=
        ih (fun j => f (j+1)) X D hstep' (show f 1 < X + c by omega)
          (show X + D ≤ f (n+1) by omega)
      exact le_trans ih' (Nat.le_add_right _ _)

theorem erdos_59388_hyp_window_count :
    ∀ a K : ℕ, 1 ≤ a → 1 ≤ K → ∀ (s : ℕ) (A : ℕ → ℕ), 0 < s → A 0 = a →
      StrictMonoOn A (Set.Iio s) →
      (∀ i, i + 1 < s → A (i + 1) - A i ≤ K) →
      4 ^ K * a + K * 4 ^ K * 4 ^ K + 2 * K * 4 ^ K < A (s - 1) →
      ∀ L ∈ Finset.Icc 1 (4 ^ K),
        2 * K * 4 ^ K / (K * L) ≤
          erdos59388WinCount A s L (4 ^ K * a + K * 4 ^ K * 4 ^ K) (2 * K * 4 ^ K) := by
  intro a K ha hK s A hs hA0 hmono hgap hbig L hL
  rw [Finset.mem_Icc] at hL
  generalize hN : 4 ^ K = N at hbig hL ⊢
  have F1 : ∀ i, i < s → A i ≤ a + K * i := by
    intro i
    induction i with
    | zero => intro _; rw [hA0]; omega
    | succ i ih =>
      intro h
      have h1 := ih (by omega)
      have h2 := hgap i h
      have e2 : K * (i+1) = K * i + K := by ring
      rw [e2]; omega
  have F3 : ∀ i m, i + m < s → A (i+m) ≤ A i + K * m := by
    intro i m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro h
      have h1 := ih (by omega)
      have h2 := hgap (i + m) (by omega)
      have e : i + (m+1) = i + m + 1 := by omega
      rw [e]
      have e2 : K * (m+1) = K * m + K := by ring
      rw [e2]
      omega
  have hsL : L < s := by
    by_contra hcon
    have h1 := F1 (s-1) (by omega)
    have h2 : K * (s - 1) ≤ K * N := Nat.mul_le_mul (le_refl K) (by omega)
    have h3 : 1 * a ≤ N * a := Nat.mul_le_mul (by omega : 1 ≤ N) (le_refl a)
    have h4 : K * N * 1 ≤ K * N * N := Nat.mul_le_mul (le_refl (K*N)) (by omega : 1 ≤ N)
    omega
  have hW : ∀ i, erdos59388WinSum A (i+1) L + A i = erdos59388WinSum A i L + A (i+L) := by
    intro i
    unfold erdos59388WinSum
    have e1 := Finset.sum_Ico_succ_top (show i ≤ i + L by omega) A
    have e2 := Finset.sum_eq_sum_Ico_succ_bot (show i < i + L + 1 by omega) A
    rw [show i + 1 + L = i + L + 1 by omega]
    omega
  have hW0 : erdos59388WinSum A 0 L ≤ L * (a + K * L) := by
    unfold erdos59388WinSum
    have hb : ∀ t ∈ Finset.Ico 0 (0 + L), A t ≤ a + K * L := by
      intro t ht
      rw [Finset.mem_Ico] at ht
      have h1 := F1 t (by omega)
      have h2 : K * t ≤ K * L := Nat.mul_le_mul (le_refl K) (by omega)
      omega
    calc ∑ t ∈ Finset.Ico 0 (0 + L), A t ≤ ∑ t ∈ Finset.Ico 0 (0 + L), (a + K * L) :=
          Finset.sum_le_sum hb
      _ = L * (a + K * L) := by rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]; simp
  have hWend : A (s-1) ≤ erdos59388WinSum A (s-L) L := by
    unfold erdos59388WinSum
    exact Finset.single_le_sum (f := A) (fun i _ => Nat.zero_le _)
      (by rw [Finset.mem_Ico]; omega)
  have hc : 0 < K * L := Nat.mul_pos (by omega) (by omega)
  have hsteps : ∀ i < s - L, erdos59388WinSum A i L ≤ erdos59388WinSum A (i+1) L ∧
      erdos59388WinSum A (i+1) L ≤ erdos59388WinSum A i L + K * L := by
    intro i hi
    have e := hW i
    have hlt : A i < A (i + L) :=
      hmono (Set.mem_Iio.mpr (by omega)) (Set.mem_Iio.mpr (by omega)) (by omega)
    have hle := F3 i L (by omega)
    omega
  have h0 : erdos59388WinSum A 0 L < N * a + K * N * N + K * L := by
    have e : L * (a + K * L) = L * a + K * L * L := by ring
    have h1 : L * a ≤ N * a := Nat.mul_le_mul hL.2 (le_refl a)
    have h2 : K * L * L ≤ K * N * N := Nat.mul_le_mul (Nat.mul_le_mul (le_refl K) hL.2) hL.2
    omega
  have hend : N * a + K * N * N + 2 * K * N ≤ erdos59388WinSum A (s - L) L := by
    omega
  unfold erdos59388WinCount
  rw [Finset.card_filter, show s + 1 - L = s - L + 1 by omega]
  exact walk_count (K*L) hc (s - L) (fun i => erdos59388WinSum A i L) _ _ hsteps h0 hend
end erdos_59388_hyp_window_count_ns

theorem erdos_59388_hyp_window_count :
    ∀ a K : ℕ, 1 ≤ a → 1 ≤ K → ∀ (s : ℕ) (A : ℕ → ℕ), 0 < s → A 0 = a →
      StrictMonoOn A (Set.Iio s) →
      (∀ i, i + 1 < s → A (i + 1) - A i ≤ K) →
      4 ^ K * a + K * 4 ^ K * 4 ^ K + 2 * K * 4 ^ K < A (s - 1) →
      ∀ L ∈ Finset.Icc 1 (4 ^ K),
        2 * K * 4 ^ K / (K * L) ≤
          erdos59388WinCount A s L (4 ^ K * a + K * 4 ^ K * 4 ^ K) (2 * K * 4 ^ K) := by
  exact erdos_59388_hyp_window_count_ns.erdos_59388_hyp_window_count



theorem erdos_59388 :
    ∀ a K : ℕ, 1 ≤ a → 1 ≤ K → ∃ f : ℕ,
    ∀ (s : ℕ) (A : ℕ → ℕ), 0 < s → A 0 = a → StrictMonoOn A (Set.Iio s) →
      (∀ i, i + 1 < s → A (i + 1) - A i ≤ K) → f < A (s - 1) → HasEqualIntervalSums A s := by
  intro a K ha hK
  refine ⟨4 ^ K * a + K * 4 ^ K * 4 ^ K + 2 * K * 4 ^ K, ?_⟩
  intro s A hs h0 hmono hgap hf
  have h1 : 2 * K * 4 ^ K < ∑ L ∈ Finset.Icc 1 (4 ^ K), 2 * K * 4 ^ K / (K * L) :=
    erdos_59388_hyp_harmonic K hK
  have h2 : ∑ L ∈ Finset.Icc 1 (4 ^ K), 2 * K * 4 ^ K / (K * L) ≤
      ∑ L ∈ Finset.Icc 1 (4 ^ K),
        erdos59388WinCount A s L (4 ^ K * a + K * 4 ^ K * 4 ^ K) (2 * K * 4 ^ K) := by
    apply Finset.sum_le_sum
    intro L hL
    exact erdos_59388_hyp_window_count a K ha hK s A hs h0 hmono hgap hf L hL
  exact erdos_59388_hyp_pigeon A s (4 ^ K) (4 ^ K * a + K * 4 ^ K * 4 ^ K) (2 * K * 4 ^ K)
    (lt_of_lt_of_le h1 h2)
