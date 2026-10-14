"""Assemble the alias-41635 residual into an unconditional proof: the two Rosser-Schoenfeld premises out, Mathlib-provable
bounds in. Every edit asserts how often its pattern occurs, so a drifted residual fails loudly instead of silently."""
import re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))
import harness as H

SRC = ROOT / "programs" / "erdos_41635" / "Residual.lean"
HDR = ROOT / "runs" / "20261013-234514-534186-hardlean-erdos41635" / "attempts" / "residual-refine-c1-0.lean"
OUT = Path(sys.argv[1])

text = SRC.read_text()


def sub1(old: str, new: str, s: str, count: int = 1) -> str:
    n = s.count(old)
    assert n == count, f"expected {count} of {old[:80]!r}, found {n}"
    return s.replace(old, new)


def region(s: str, start: str, end: str) -> tuple[str, str, str]:
    i = s.index(start)
    j = s.index(end, i)
    return s[:i], s[i:j], s[j:]


HYP126 = "(∀ x : ℝ, 1 < x → (Nat.primeCounting ⌊x⌋₊ : ℝ) < 1.26 * x / Real.log x)"
HYP5 = "(∀ x : ℝ, 1 < x → (Nat.primeCounting ⌊x⌋₊ : ℝ) < 5 * x / Real.log x)"
HYPLOW = "(∀ x : ℝ, 17 ≤ x → x / Real.log x < (Nat.primeCounting ⌊x⌋₊ : ℝ))"

# ---- 1. the two published premises out, a Mathlib-derived bound in -----------------------------------------------
PREMISES = """-- PUBLISHED: Rosser–Schoenfeld, Illinois J. Math. 6 (1962), Theorem 1, Corollary 1, (3.6)
theorem erdos_41635_hyp_upper_hyp_box_to_bound_hyp_rs_upper :
    ∀ x : ℝ, 1 < x → (erdosPiReal x : ℝ) < 1.25506 * x / Real.log x := by
  sorry

-- PUBLISHED: Rosser–Schoenfeld, Illinois J. Math. 6 (1962), Theorem 1, Corollary 1, (3.5)
theorem erdos_41635_hyp_upper_hyp_box_to_bound_hyp_rs_lower :
    ∀ x : ℝ, 17 ≤ x → x / Real.log x < (erdosPiReal x : ℝ) := by
  sorry
"""
CHEB5 = """-- OPERATOR-ASSISTED (2026-10-14): in place of the two Rosser–Schoenfeld premises. The pieces need SOME constant
-- in Chebyshev's upper bound, not theirs; 5 follows from Mathlib's `Chebyshev.pi_le_log4_mul_div`. The dyadic
-- bounds box_part needs are proved inside its namespace from the central binomial coefficient (Erdős's proof of
-- Bertrand's postulate, kept quantitative).
theorem erdos_41635_cheb_upper5 :
    ∀ x : ℝ, 1 < x → (Nat.primeCounting ⌊x⌋₊ : ℝ) < 5 * x / Real.log x := by
  intro x hx
  have h := Chebyshev.pi_le_log4_mul_div hx
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos hx
  have hL' : Real.log x ≠ 0 := hL.ne'
  have hs : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx0.le
  rw [hs] at h
  have hsq : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hss : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hlogs : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 := Real.log_le_sub_one_of_pos hsq
  rw [hs] at hlogs
  have hlx : Real.log x < 2 * Real.sqrt x := by linarith
  have h1 : Real.sqrt x < 2 * (x / Real.log x) := by
    rw [mul_div_assoc', lt_div_iff₀ hL]
    nlinarith
  have h4 : Real.log 4 < 1.3863 := by
    have e : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [e]; have := Real.log_two_lt_d9; linarith
  have h2 : Real.log 4 * x / (Real.log x / 2) = 2 * Real.log 4 * (x / Real.log x) := by
    field_simp
  have h3 : 5 * x / Real.log x = 5 * (x / Real.log x) := by ring
  have hq : 0 < x / Real.log x := div_pos hx0 hL
  rw [h2] at h
  rw [h3]
  have := mul_lt_mul_of_pos_right h4 hq
  linarith
"""
text = sub1(PREMISES, CHEB5, text)

# ---- 2. rough: constant 1.26 -> 5, its C from 3 to 6 --------------------------------------------------------------
head, rough, tail = region(text, "-- S2 bullet 1:", "-- S2 Case E:")
rough = sub1("< 1.26 n/log n + 1", "< 5 n/log n + 1", rough)
rough = sub1(HYP126, HYP5, rough, 2)
rough = sub1("refine ⟨3, ⌈Real.exp (Real.exp 1)⌉₊, fun n hn => ?_⟩", "refine ⟨6, ⌈Real.exp (Real.exp 1)⌉₊, fun n hn => ?_⟩", rough)
rough = sub1("have hgoal : 3 * ((n:ℝ) * Real.log L / L) = 3 * ((n:ℝ) / L) * Real.log L := by ring",
             "have hgoal : 6 * ((n:ℝ) * Real.log L / L) = 6 * ((n:ℝ) / L) * Real.log L := by ring", rough)
rough = sub1("have h126 : 1.26 * (n:ℝ) / L = 1.26 * ((n:ℝ) / L) := by ring",
             "have h126 : 5 * (n:ℝ) / L = 5 * ((n:ℝ) / L) := by ring", rough)
rough = sub1("(by linarith : (0:ℝ) ≤ 3 * ((n:ℝ) / L))", "(by linarith : (0:ℝ) ≤ 6 * ((n:ℝ) / L))", rough)
assert "1.26" not in rough, "rough still mentions 1.26"
text = head + rough + tail

# ---- 3. smooth_tail: 1.26 -> 5, 2.52 = 2*1.26 -> 10, 50.4 = 40*1.26 -> 200 ----------------------------------------
head, smooth, tail = region(text, "-- S2 Case E:", "namespace erdos_41635_hyp_upper_hyp_box_to_bound_hyp_box_part_ns")
for old, new in (("1.26", "5"), ("2.52", "10"), ("50.4", "200")):
    assert smooth.count(old) > 0, old
    smooth = smooth.replace(old, new)
text = head + smooth + tail

# ---- 4. box_part: both dyadic bounds proved outright; every hypothesis dropped -----------------------------------
head, box, tail = region(text, "namespace erdos_41635_hyp_upper_hyp_box_to_bound_hyp_box_part_ns",
                         "theorem erdos_41635_hyp_upper_hyp_box_to_bound : ∃ C")

NEW_DYADIC = """/-- OPERATOR-ASSISTED (2026-10-14): every prime in `(n, 2n]` divides the central binomial coefficient. -/
private lemma pow_card_primes_le41635 (n : ℕ) :
    n ^ ((Finset.Ioc n (2 * n)).filter Nat.Prime).card ≤ 4 ^ n := by
  set T := (Finset.Ioc n (2 * n)).filter Nat.Prime with hT
  calc n ^ T.card = ∏ _p ∈ T, n := (Finset.prod_const n).symm
    _ ≤ ∏ p ∈ T, p := Finset.prod_le_prod' (fun p hp => by
        rw [hT, Finset.mem_filter, Finset.mem_Ioc] at hp; omega)
    _ ≤ Nat.centralBinom n := Nat.le_of_dvd (Nat.centralBinom_pos n)
        (Finset.prod_primes_dvd _ (fun p hp => (Finset.mem_filter.1 hp).2.prime)
          (fun p hp => by
            rw [hT, Finset.mem_filter, Finset.mem_Ioc] at hp
            rw [Nat.centralBinom_eq_two_mul_choose]
            exact hp.2.dvd_choose hp.1.1 (by omega) hp.1.2))
    _ ≤ 4 ^ n := Nat.centralBinom_le_four_pow n

/-- OPERATOR-ASSISTED (2026-10-14): Erdős's proof of Bertrand's postulate, kept quantitative. The central binomial
coefficient is at most what the primes up to `2n/3` contribute, times `2n` for each prime in `(n, 2n]`. -/
private lemma centralBinom_le_with_primes41635 (n : ℕ) (hn : 2 < n) :
    Nat.centralBinom n ≤ (2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) *
      (2 * n) ^ ((Finset.Ioc n (2 * n)).filter Nat.Prime).card := by
  set T := (Finset.Ioc n (2 * n)).filter Nat.Prime with hT
  have n_pos : 0 < n := by omega
  have n2_pos : 1 ≤ 2 * n := by omega
  let f : ℕ → ℕ := fun x => x ^ n.centralBinom.factorization x
  have hsplit : Nat.centralBinom n = (∏ x ∈ Finset.range (2 * n / 3 + 1), f x) * ∏ x ∈ T, f x := by
    have hsub : Finset.range (2 * n / 3 + 1) ⊆ Finset.range (2 * n + 1) :=
      Finset.range_subset_range.2 (by omega)
    conv_lhs => rw [← Nat.prod_pow_factorization_centralBinom n]
    rw [← Finset.prod_sdiff hsub, mul_comm]
    congr 1
    symm
    apply Finset.prod_subset
    · intro p hp
      rw [hT, Finset.mem_filter, Finset.mem_Ioc] at hp
      rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_range]
      omega
    · intro p hp hpT
      rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_range] at hp
      by_cases hpr : p.Prime
      · have hpn : p ≤ n := by
          by_contra hcon
          exact hpT (by rw [hT, Finset.mem_filter, Finset.mem_Ioc]; exact ⟨⟨by omega, by omega⟩, hpr⟩)
        show p ^ n.centralBinom.factorization p = 1
        rw [Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul hn hpn (by omega), pow_zero]
      · show p ^ n.centralBinom.factorization p = 1
        rw [Nat.factorization_eq_zero_of_not_prime _ hpr, pow_zero]
  have hsmall : ∏ x ∈ Finset.range (2 * n / 3 + 1), f x ≤ (2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) := by
    let S := {p ∈ Finset.range (2 * n / 3 + 1) | Nat.Prime p}
    have : ∏ x ∈ S, f x = ∏ x ∈ Finset.range (2 * n / 3 + 1), f x := by
      refine Finset.prod_filter_of_ne fun p _ h => ?_
      contrapose h; dsimp only [f]
      rw [Nat.factorization_eq_zero_of_not_prime n.centralBinom h, _root_.pow_zero]
    rw [← this, ← Finset.prod_filter_mul_prod_filter_not S (· ≤ Nat.sqrt (2 * n))]
    apply mul_le_mul'
    · refine (Finset.prod_le_prod' fun p _ => (?_ : f p ≤ 2 * n)).trans ?_
      · exact Nat.pow_factorization_choose_le (mul_pos two_pos n_pos)
      have : (Finset.Icc 1 (Nat.sqrt (2 * n))).card = Nat.sqrt (2 * n) := by
        rw [Nat.card_Icc, Nat.add_sub_cancel]
      rw [Finset.prod_const]
      refine pow_right_mono₀ n2_pos ((Finset.card_le_card fun x hx => ?_).trans this.le)
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.1 h1).2.one_lt.le, h2⟩
    · refine le_trans ?_ (primorial_le_four_pow (2 * n / 3))
      refine (Finset.prod_le_prod' fun p hp => (?_ : f p ≤ p)).trans ?_
      · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
        refine (pow_right_mono₀ (Finset.mem_filter.1 h1).2.one_lt.le ?_).trans (pow_one p).le
        exact Nat.factorization_choose_le_one (Nat.sqrt_lt'.mp <| not_le.1 h2)
      refine Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _) ?_
      exact fun p hp _ => (Finset.mem_filter.1 hp).2.one_lt.le
  have hT' : ∏ x ∈ T, f x ≤ (2 * n) ^ T.card := by
    calc ∏ x ∈ T, f x ≤ ∏ _x ∈ T, (2 * n) :=
          Finset.prod_le_prod' fun p _ => Nat.pow_factorization_choose_le (mul_pos two_pos n_pos)
      _ = (2 * n) ^ T.card := Finset.prod_const _
  rw [hsplit]
  exact Nat.mul_le_mul hsmall hT'

private lemma not_prime_two_pow41635 (j : ℕ) (hj : 2 ≤ j) : ¬ (2 ^ j).Prime := by
  intro hp
  have h2 : 2 ∣ 2 ^ j := dvd_pow_self 2 (by omega)
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2
  have h4 : 2 ^ 2 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
  omega

/-- For `j ≥ 2` the dyadic block's primes are the primes in `(2^j, 2·2^j]`. -/
private lemma dyQ_eq41635 (j : ℕ) (hj : 2 ≤ j) :
    dyQ j = (Finset.Ioc (2 ^ j) (2 * 2 ^ j)).filter Nat.Prime := by
  unfold dyQ
  have hpow : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; ring
  have hA := not_prime_two_pow41635 j hj
  have hB := not_prime_two_pow41635 (j + 1) (by omega)
  ext p
  simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨h1, h2⟩, hp⟩
    refine ⟨⟨?_, by omega⟩, hp⟩
    rcases Nat.lt_or_ge (2 ^ j) p with h | h
    · exact h
    · exact absurd (show p = 2 ^ j by omega ▸ hp) (by
        intro hq; exact hA (by rw [show 2 ^ j = p by omega]; exact hp))
  · rintro ⟨⟨h1, h2⟩, hp⟩
    refine ⟨⟨by omega, ?_⟩, hp⟩
    rcases Nat.lt_or_ge p (2 ^ (j + 1)) with h | h
    · exact h
    · exfalso; exact hB (by rw [show 2 ^ (j + 1) = p by omega]; exact hp)

private lemma big_pow41635 (j : ℕ) (hj : 20 ≤ j) : 288 * (j + 1) ^ 2 ≤ 2 ^ j := by
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have : (k + 2) ^ 2 ≤ 2 * (k + 1) ^ 2 := by nlinarith
    calc 288 * (k + 1 + 1) ^ 2 = 288 * (k + 2) ^ 2 := by ring
      _ ≤ 288 * (2 * (k + 1) ^ 2) := by omega
      _ = 2 * (288 * (k + 1) ^ 2) := by ring
      _ ≤ 2 * 2 ^ k := by omega
      _ = 2 ^ (k + 1) := by ring

"""
NEW_CHEB_UP = """/-- OPERATOR-ASSISTED (2026-10-14): the dyadic upper bound, from `n ^ #primes ≤ 4 ^ n`, with no hypothesis. -/
private lemma cheb_up (j : ℕ) :
    ((dyQ j).card : ℝ) ≤ 4 * 2 ^ j / (j + 1) := by
  set c := (dyQ j).card with hc
  suffices h : (j + 1) * c ≤ 4 * 2 ^ j by
    rw [le_div_iff₀ (by positivity)]
    have : (((j + 1) * c : ℕ) : ℝ) ≤ ((4 * 2 ^ j : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this
    linarith
  have hpow : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; ring
  rcases Nat.lt_or_ge j 2 with hj | hj
  · have hc' : c ≤ 2 ^ j := by
      calc c ≤ (Finset.Ico (2 ^ j) (2 ^ (j + 1))).card := by rw [hc]; unfold dyQ; exact Finset.card_filter_le _ _
        _ = 2 ^ j := by rw [Nat.card_Ico]; omega
    have h0 : 0 < 2 ^ j := by positivity
    interval_cases j <;> omega
  · rw [hc, dyQ_eq41635 j hj]
    set c' := ((Finset.Ioc (2 ^ j) (2 * 2 ^ j)).filter Nat.Prime).card with hc'
    have h := pow_card_primes_le41635 (2 ^ j)
    rw [← hc', ← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul] at h
    have h' : j * c' ≤ 2 * 2 ^ j := (Nat.pow_le_pow_iff_right (by norm_num)).mp h
    have : c' ≤ j * c' := Nat.le_mul_of_pos_left c' (by omega)
    nlinarith

"""
NEW_CHEB_LOW = """/-- OPERATOR-ASSISTED (2026-10-14): the dyadic lower bound for `j ≥ 80`, from the quantitative Bertrand bound
above, with no hypothesis. Its only use is at `j ≥ 80`. -/
private lemma cheb_low (j : ℕ) (hj : 80 ≤ j) :
    (2 : ℝ) ^ j / (2 * (j + 1)) ≤ (dyQ j).card := by
  rw [dyQ_eq41635 j (by omega)]
  set n := 2 ^ j with hn
  set c := ((Finset.Ioc n (2 * n)).filter Nat.Prime).card with hc
  set s := Nat.sqrt (2 * n) with hs
  have hn4 : 4 ≤ n := by
    rw [hn]; calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2n : 2 * n = 2 ^ (j + 1) := by rw [hn, pow_succ]; ring
  have hA := Nat.four_pow_lt_mul_centralBinom n hn4
  have hB := centralBinom_le_with_primes41635 n (by omega)
  rw [← hc, ← hs] at hB
  have hC : 4 ^ n < (2 * n) * ((2 * n) ^ s * 4 ^ (2 * n / 3) * (2 * n) ^ c) := by
    calc 4 ^ n < n * Nat.centralBinom n := hA
      _ ≤ (2 * n) * Nat.centralBinom n := Nat.mul_le_mul_right _ (by omega)
      _ ≤ (2 * n) * ((2 * n) ^ s * 4 ^ (2 * n / 3) * (2 * n) ^ c) := Nat.mul_le_mul_left _ hB
  have hD : 2 ^ (2 * n) < 2 ^ ((j + 1) * (1 + s + c) + 2 * (2 * n / 3)) := by
    have e1 : (4 : ℕ) ^ n = 2 ^ (2 * n) := by rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    have e2 : (2 * n) * ((2 * n) ^ s * 4 ^ (2 * n / 3) * (2 * n) ^ c) =
        2 ^ ((j + 1) * (1 + s + c) + 2 * (2 * n / 3)) := by
      rw [h2n, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, ← pow_mul]
      ring
    rw [e1, e2] at hC
    exact hC
  have hE : 2 * n < (j + 1) * (1 + s + c) + 2 * (2 * n / 3) :=
    (Nat.pow_lt_pow_iff_right (by norm_num)).mp hD
  have hs2 : s * s ≤ 2 * n := Nat.sqrt_le (2 * n)
  have hs1 : 1 ≤ s := by rw [hs]; exact Nat.le_sqrt.mpr (by omega)
  have hbig := big_pow41635 j (by omega)
  have hF : (6 * (j + 1) * (1 + s)) * (6 * (j + 1) * (1 + s)) ≤ n * n := by
    have h1 : (1 + s) * (1 + s) ≤ 4 * (s * s) := by nlinarith
    have h3 : 288 * (j + 1) ^ 2 * n ≤ n * n := by
      rw [hn]; exact Nat.mul_le_mul_right _ hbig
    calc (6 * (j + 1) * (1 + s)) * (6 * (j + 1) * (1 + s))
        = 36 * (j + 1) ^ 2 * ((1 + s) * (1 + s)) := by ring
      _ ≤ 36 * (j + 1) ^ 2 * (4 * (s * s)) := Nat.mul_le_mul_left _ h1
      _ ≤ 36 * (j + 1) ^ 2 * (4 * (2 * n)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hs2)
      _ = 288 * (j + 1) ^ 2 * n := by ring
      _ ≤ n * n := h3
  have hG : 6 * (j + 1) * (1 + s) ≤ n := Nat.mul_self_le_mul_self_iff.mp hF
  have hH : n ≤ 2 * ((j + 1) * c) := by
    have e : (j + 1) * (1 + s + c) = (j + 1) * (1 + s) + (j + 1) * c := by ring
    rw [e] at hE
    have e2 : 6 * (j + 1) * (1 + s) = 6 * ((j + 1) * (1 + s)) := by ring
    rw [e2] at hG
    omega
  rw [div_le_iff₀ (by positivity)]
  have : ((n : ℕ) : ℝ) ≤ ((2 * ((j + 1) * c) : ℕ) : ℝ) := by exact_mod_cast hH
  push_cast at this
  rw [hn] at this
  push_cast at this
  linarith

"""
# old cheb_up: from its header to primeCounting_le_add
i = box.index("private lemma cheb_up\n")
j = box.index("private lemma primeCounting_le_add")
box = box[:i] + NEW_DYADIC + NEW_CHEB_UP + box[j:]
# old cheb_low: from its header to sum_shift_le
i = box.index("private lemma cheb_low\n")
j = box.index("private lemma sum_shift_le")
box = box[:i] + NEW_CHEB_LOW + box[j:]
# y_big
box = sub1("private lemma y_big\n    (h1 : " + HYP126[1:] + "\n    (h2 : " + HYPLOW[1:] + "\n    (X : ℝ)",
           "private lemma y_big\n    (X : ℝ)", box)
box = sub1("have hlow := cheb_low h1 h2 j (by omega)", "have hlow := cheb_low j hj80", box)
# analytic_box_sum
box = sub1("private lemma analytic_box_sum :\n    " + HYP126 + " →\n    " + HYPLOW + " →\n",
           "private lemma analytic_box_sum :\n", box)
i = box.index("private lemma analytic_box_sum :\n")
k = box.index("  intro h1 h2\n", i)
box = box[:k] + box[k + len("  intro h1 h2\n"):]
box = sub1("y_big h1 h2 X", "y_big X", box, 2)
box = sub1("cheb_up h1 j", "cheb_up j", box)
box = sub1("cheb_up h1 k", "cheb_up k", box)
# the box_part theorem, inside its namespace and its wrapper
BOXHYPS = "theorem erdos_41635_hyp_upper_hyp_box_to_bound_hyp_box_part :\n    " + HYP126 + " →\n    " + HYPLOW + " →\n"
box = sub1(BOXHYPS, "theorem erdos_41635_hyp_upper_hyp_box_to_bound_hyp_box_part :\n", box, 2)
box = sub1("  intro h1 h2\n  obtain ⟨C, N, hC⟩ := analytic_box_sum h1 h2\n", "  obtain ⟨C, N, hC⟩ := analytic_box_sum\n", box)
assert "1.26" not in box and "17 ≤ x" not in box, "box_part still mentions a premise"
text = head + box + tail

# ---- 5. the glue: hup from Mathlib, no hlow ------------------------------------------------------------------------
i = text.index("  have hup : ∀ x : ℝ, 1 < x → (Nat.primeCounting ⌊x⌋₊ : ℝ) < 1.26 * x / Real.log x := by\n")
j = text.index("  obtain ⟨C1, N1, h1⟩ := erdos_41635_hyp_upper_hyp_box_to_bound_hyp_rough hup\n", i)
text = text[:i] + ("  have hup : ∀ x : ℝ, 1 < x → (Nat.primeCounting ⌊x⌋₊ : ℝ) < 5 * x / Real.log x :=\n"
                   "    erdos_41635_cheb_upper5\n") + text[j:]
text = sub1("erdos_41635_hyp_upper_hyp_box_to_bound_hyp_box_part hup hlow", "erdos_41635_hyp_upper_hyp_box_to_bound_hyp_box_part", text)

assert "sorry" not in re.sub(r"--.*", "", text), "a sorry is left"
assert "1.25506" not in text and "rs_upper" not in text and "rs_lower" not in text

imports = [l.split()[1] for l in HDR.read_text().splitlines() if l.startswith("import ")]
imports += ["Mathlib.NumberTheory.Bertrand"]
OUT.write_text(H.compose(text, list(dict.fromkeys(imports))))
print(OUT, len(OUT.read_text().splitlines()), "lines;", len(imports), "imports")
