-- CHECK: Real.rpow_def_of_pos Real.log_rpow Real.log_mul Real.log_le_log Real.log_lt_log Real.exp_one_lt_d9 Asymptotics.isLittleO_one_iff Metric.tendsto_nhds div_mul_cancel₀ div_le_iff₀ le_div_iff₀
open Real
noncomputable def scaleL (n : ℕ) : ℝ := exp (sqrt (log n * log (log n)))

open Filter Real

noncomputable def f (N : ℕ) : ℕ :=
  sSup {r : ℕ | ∃ n : Fin r → ℕ, ∃ a : Fin r → ℤ,
    StrictMono n ∧ (∀ i, 0 < n i ∧ n i ≤ N) ∧
    ∀ m : ℤ, ∀ i j : Fin r, m ≡ a i [ZMOD (n i : ℤ)] → m ≡ a j [ZMOD (n j : ℤ)] → i = j}

-- Upper half: f(N) ≤ N / L(N)^{1-ε} eventually. A counterexample to the target with
-- limsup of f(N)·L(N)/N in log-scale > 0 must violate this; it is the smooth/rough
-- moduli split plus the fibre bound #{i : p ∣ n_i} ≤ p·f(N/p) at the sharp balance.
namespace erdos_43382_hyp_upper_ns
-- CHECK: Real.rpow_def_of_pos Real.log_rpow Real.log_mul Real.log_le_log Real.log_lt_log Real.exp_one_lt_d9 Asymptotics.isLittleO_one_iff Metric.tendsto_nhds div_mul_cancel₀ div_le_iff₀ le_div_iff₀
open Real

open Filter Real

def smoothP (y : ℝ) (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → (p : ℝ) ≤ y

def roughP (y : ℝ) (n : ℕ) : Prop := ¬ smoothP y n

noncomputable def fRestr (P : ℕ → Prop) (N : ℕ) : ℕ :=
  sSup {r : ℕ | ∃ n : Fin r → ℕ, ∃ a : Fin r → ℤ,
    StrictMono n ∧ (∀ i, 0 < n i ∧ n i ≤ N ∧ P (n i)) ∧
    ∀ m : ℤ, ∀ i j : Fin r, m ≡ a i [ZMOD (n i : ℤ)] → m ≡ a j [ZMOD (n j : ℤ)] → i = j}

noncomputable def psiCount (N : ℕ) (y : ℝ) : ℕ :=
  Nat.card {n : ℕ // 1 ≤ n ∧ n ≤ N ∧ smoothP y n}

-- Derived: an admissible family splits into its y-smooth and y-rough subfamilies, each admissible
-- (strict monotonicity and disjointness are inherited by subfamilies), and both restricted sets are
-- bounded by N so the sSup's are attained maxima.
theorem erdos_43382_hyp_upper_hyp_split :
    ∀ (y : ℝ) (N : ℕ), f N ≤ fRestr (smoothP y) N + fRestr (roughP y) N := by
  sorry

-- Derived: the moduli of an admissible family are distinct, so a family of y-smooth moduli in [1,N]
-- injects into the set of y-smooth integers in [1,N].
namespace erdos_43382_hyp_upper_hyp_smooth_le_psi_ns

-- CHECK: Real.rpow_def_of_pos Real.log_rpow Real.log_mul Real.log_le_log Real.log_lt_log Real.exp_one_lt_d9 Asymptotics.isLittleO_one_iff Metric.tendsto_nhds div_mul_cancel₀ div_le_iff₀ le_div_iff₀
open Real

open Filter Real

theorem erdos_43382_hyp_upper_hyp_smooth_le_psi :
    ∀ (y : ℝ) (N : ℕ), fRestr (smoothP y) N ≤ psiCount N y := by
  intro y N
  unfold fRestr psiCount
  apply csSup_le'
  intro r hr
  obtain ⟨n, a, hmono, hbd, -⟩ := hr
  haveI : Finite {n : ℕ // 1 ≤ n ∧ n ≤ N ∧ smoothP y n} := by
    apply Finite.of_injective
      (fun x : {n : ℕ // 1 ≤ n ∧ n ≤ N ∧ smoothP y n} =>
        (⟨x.1, Nat.lt_succ_of_le x.2.2.1⟩ : Fin (N+1)))
    intro x z h
    have h2 := congrArg Fin.val h
    exact Subtype.ext h2
  have hinj : Function.Injective
      (fun i : Fin r => (⟨n i, Nat.succ_le_of_lt (hbd i).1, (hbd i).2.1, (hbd i).2.2⟩ :
        {n : ℕ // 1 ≤ n ∧ n ≤ N ∧ smoothP y n})) := by
    intro i j h
    exact hmono.injective (congrArg Subtype.val h)
  have := Nat.card_le_card_of_injective _ hinj
  simpa using this

end erdos_43382_hyp_upper_hyp_smooth_le_psi_ns

theorem erdos_43382_hyp_upper_hyp_smooth_le_psi :
    ∀ (y : ℝ) (N : ℕ), fRestr (smoothP y) N ≤ psiCount N y := by
  exact erdos_43382_hyp_upper_hyp_smooth_le_psi_ns.erdos_43382_hyp_upper_hyp_smooth_le_psi

-- PUBLISHED: Canfield, Erdős, Pomerance (1983), "On a problem of Oppenheim concerning factorisatio
-- numerorum", Corollary to Theorem 3.1: Psi(x, L(x)^a) = x L(x)^{-1/(2a)+o(1)}; here a = 1/2, and
-- the factor 1/2 is absorbed by the o(1) (L(N) → ∞).
theorem erdos_43382_hyp_upper_hyp_psi :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      (psiCount N (scaleL N ^ (1/2 : ℝ)) : ℝ) ≤ (N : ℝ) * scaleL N ^ (-1 + ε) / 2 := by
  sorry

-- Conjecture (the open core): moduli having a prime factor > L(N)^{1/2} contribute at most
-- N / L(N)^{1+o(1)}. Via the fibre decomposition #{i : P(n_i) = p} ≤ p f(N/p) and Σ 1/n_i ≤ 1,
-- this is exactly where de la Bretèche–Ford–Vandehey only reach exponent √3/2.
theorem erdos_43382_hyp_upper_hyp_rough :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      (fRestr (roughP (scaleL N ^ (1/2 : ℝ))) N : ℝ) ≤ (N : ℝ) * scaleL N ^ (-1 + ε) / 2 := by
  sorry

theorem erdos_43382_hyp_upper :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, (f N : ℝ) ≤ (N : ℝ) * scaleL N ^ (-1 + ε) := by
  intro ε hε
  filter_upwards [erdos_43382_hyp_upper_hyp_psi ε hε, erdos_43382_hyp_upper_hyp_rough ε hε]
    with N h1 h2
  have hs := erdos_43382_hyp_upper_hyp_split (scaleL N ^ (1/2 : ℝ)) N
  have hp := erdos_43382_hyp_upper_hyp_smooth_le_psi (scaleL N ^ (1/2 : ℝ)) N
  have hs' : (f N : ℝ) ≤ (fRestr (smoothP (scaleL N ^ (1/2 : ℝ))) N : ℝ)
      + (fRestr (roughP (scaleL N ^ (1/2 : ℝ))) N : ℝ) := by
    exact_mod_cast hs
  have hp' : (fRestr (smoothP (scaleL N ^ (1/2 : ℝ))) N : ℝ)
      ≤ (psiCount N (scaleL N ^ (1/2 : ℝ)) : ℝ) := by
    exact_mod_cast hp
  linarith
end erdos_43382_hyp_upper_ns

theorem erdos_43382_hyp_upper :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, (f N : ℝ) ≤ (N : ℝ) * scaleL N ^ (-1 + ε) := by
  exact erdos_43382_hyp_upper_ns.erdos_43382_hyp_upper



-- Lower half: f(N) ≥ N / L(N)^{1+ε} eventually. Should follow from a construction with
-- moduli p·m (m smooth, p a prime in a window) and greedy CRT residue assignment,
-- tuned so the surviving count is N·L^{-1-o(1)}.
theorem erdos_43382_hyp_lower :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, (N : ℝ) * scaleL N ^ (-1 - ε) ≤ (f N : ℝ) := by
  sorry

theorem erdos_43382 :
    ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ᶠ N : ℕ in atTop, (f N : ℝ) = (N : ℝ) * scaleL N ^ (-1 + o N) := by
  have hLog : ∀ N : ℕ, 3 ≤ N → 0 < Real.log (scaleL N) := by
    intro N hN
    have h3 : (3:ℝ) ≤ N := by exact_mod_cast hN
    have he : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
    have h1 : 1 < Real.log N := by
      have := Real.log_lt_log (Real.exp_pos 1) (lt_of_lt_of_le he h3)
      rwa [Real.log_exp] at this
    have h2 : 0 < Real.log (Real.log N) := Real.log_pos h1
    unfold scaleL
    rw [Real.log_exp]
    exact Real.sqrt_pos.mpr (mul_pos (by linarith) h2)
  have hLpos : ∀ N : ℕ, 0 < scaleL N := by
    intro N
    unfold scaleL
    exact Real.exp_pos _
  refine ⟨fun N => 1 - (Real.log N - Real.log (f N)) / Real.log (scaleL N), ?_, ?_⟩
  · have h1 : (1 : ℕ → ℝ) = fun _ => (1:ℝ) := rfl
    rw [h1, Asymptotics.isLittleO_one_iff, Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [erdos_43382_hyp_upper (ε/2) (by positivity),
      erdos_43382_hyp_lower (ε/2) (by positivity), eventually_ge_atTop 3] with N hu hl h3
    have hLN := hLog N h3
    have hL := hLpos N
    have h3' : (3:ℝ) ≤ N := by exact_mod_cast h3
    have hN : (0:ℝ) < N := by linarith
    have hP : (0:ℝ) < (N:ℝ) * scaleL N ^ (-1 - ε/2) :=
      mul_pos hN (Real.rpow_pos_of_pos hL _)
    have hf : (0:ℝ) < (f N : ℝ) := lt_of_lt_of_le hP hl
    have A : Real.log (f N) ≤ Real.log N + (-1 + ε/2) * Real.log (scaleL N) := by
      have := Real.log_le_log hf hu
      rwa [Real.log_mul hN.ne' (Real.rpow_pos_of_pos hL _).ne', Real.log_rpow hL] at this
    have B : Real.log N + (-1 - ε/2) * Real.log (scaleL N) ≤ Real.log (f N) := by
      have := Real.log_le_log hP hl
      rwa [Real.log_mul hN.ne' (Real.rpow_pos_of_pos hL _).ne', Real.log_rpow hL] at this
    have hx1 : (Real.log N - Real.log (f N)) / Real.log (scaleL N) ≤ 1 + ε/2 := by
      rw [div_le_iff₀ hLN]; linarith
    have hx2 : 1 - ε/2 ≤ (Real.log N - Real.log (f N)) / Real.log (scaleL N) := by
      rw [le_div_iff₀ hLN]; linarith
    simp only [Real.dist_eq, sub_zero]
    rw [abs_lt]
    constructor <;> linarith
  · filter_upwards [erdos_43382_hyp_lower 1 one_pos, eventually_ge_atTop 3] with N hl h3
    show (f N : ℝ) = (N:ℝ) * scaleL N ^ (-1 + (1 - (Real.log N - Real.log (f N)) / Real.log (scaleL N)))
    have hLN := hLog N h3
    have hL := hLpos N
    have h3' : (3:ℝ) ≤ N := by exact_mod_cast h3
    have hN : (0:ℝ) < N := by linarith
    have hP : (0:ℝ) < (N:ℝ) * scaleL N ^ (-1 - (1:ℝ)) :=
      mul_pos hN (Real.rpow_pos_of_pos hL _)
    have hf : (0:ℝ) < (f N : ℝ) := lt_of_lt_of_le hP hl
    have hx : Real.log (scaleL N) * ((Real.log N - Real.log (f N)) / Real.log (scaleL N))
        = Real.log N - Real.log (f N) := by
      rw [mul_comm]; exact div_mul_cancel₀ _ hLN.ne'
    have key : Real.log (scaleL N) *
        (-1 + (1 - (Real.log N - Real.log (f N)) / Real.log (scaleL N)))
        = Real.log (f N) - Real.log N := by
      have e : -1 + (1 - (Real.log N - Real.log (f N)) / Real.log (scaleL N))
          = -((Real.log N - Real.log (f N)) / Real.log (scaleL N)) := by ring
      rw [e, mul_neg, hx]; ring
    rw [Real.rpow_def_of_pos hL, key, Real.exp_sub, Real.exp_log hf, Real.exp_log hN,
      mul_comm, div_mul_cancel₀ _ hN.ne']