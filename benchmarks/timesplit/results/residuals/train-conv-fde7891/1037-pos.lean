open Filter

def IsTrivialSet {V : Type*} (G : SimpleGraph V) (s : Set V) : Prop :=
  G.IsIndepSet s ∨ G.IsClique s

-- BELIEVED FALSE: this is a strengthening of the target obtained by dropping both degree hypotheses.
-- It contradicts Erdős's 1947 random-graph lower bound for diagonal Ramsey numbers:
-- G(n,1/2) has no trivial set of size > 2 log_2 n, so it fails for C = 3.
-- It is recorded only so that the glue compiles; the frozen target is itself believed false (see route).
theorem erdos_25820_hyp_ramsey_unbounded :
    ∀ C : ℝ, ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      ∃ s : Set (Fin n), IsTrivialSet G s ∧ (C * Real.log (n : ℝ) < (s.ncard : ℝ)) := by
  sorry

theorem erdos_25820 :
    ∀ ε : ℝ, 0 < ε → ∀ C : ℝ, ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      (∀ d : ℕ, {v : Fin n | (G.neighborSet v).ncard = d}.ncard ≤ 2) →
      ((1 / 2 + ε) * (n : ℝ) <
        ((Set.range fun v : Fin n => (G.neighborSet v).ncard).ncard : ℝ)) →
      ∃ s : Set (Fin n), IsTrivialSet G s ∧ (C * Real.log (n : ℝ) < (s.ncard : ℝ)) := by
  intro ε _ C
  filter_upwards [erdos_25820_hyp_ramsey_unbounded C] with n hn
  intro G _ _
  exact hn G