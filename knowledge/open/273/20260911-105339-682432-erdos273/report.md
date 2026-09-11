# Open problem #273 — two-direction attack (run 20260911-105339-682432-erdos273)

**REQUIRES HUMAN REVIEW BEFORE ANY EXTERNAL CLAIM.** Automated formalization of an open problem can be subtly wrong; a Lean proof here certifies the FROZEN statement below, not necessarily the problem.

- English statement: Is there a covering system all of whose moduli are of the form $p-1$ for some primes $p\geq 5$?
- triage: search-first — shape=witness, computable=True

Review milestones: {"schema_version": 1, "artifact_sha256": "338d8b4acc9ea4ec60cd452ce5d8aec84fec07b6d0e263109d4ca64dab643c0b", "stage": "no_candidate", "candidate_solution": false, "mechanically_verified": false, "statement_independently_audited": false, "externally_reviewed": false, "resolution_claim_eligible": false, "scope": "full_problem_candidate", "catalogue_status_changed": false, "pending": ["clean_replay", "statement_audit", "adversarial_checks", "external_review"], "notice": "Operator-recorded review evidence; reviewer identity and independence require human verification. No automatic catalogue update."}
## Direction `pos` — outcome: **not_proved** (exit 2)
```lean
theorem erdos_273 :
    ∃ (k : ℕ) (m : Fin k → ℕ) (a : Fin k → ℤ),
      (∀ i, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ m i + 1 = p) ∧
      Function.Injective m ∧
      (∀ n : ℤ, ∃ i, n ≡ a i [ZMOD (m i : ℤ)]) := by
  sorry
```
- spent: $6.85

Review milestones: {"schema_version": 1, "artifact_sha256": "446d89957c4b8c5d174fe2d729b156de94d28fffe99a313bf03f346e2f6ae561", "stage": "no_candidate", "candidate_solution": false, "mechanically_verified": false, "statement_independently_audited": false, "externally_reviewed": false, "resolution_claim_eligible": false, "scope": "full_problem_candidate", "catalogue_status_changed": false, "pending": ["clean_replay", "statement_audit", "adversarial_checks", "external_review"], "notice": "Operator-recorded review evidence; reviewer identity and independence require human verification. No automatic catalogue update."}
## Direction `neg` — outcome: **not_proved** (exit 2)
```lean
theorem erdos_273_neg :
    ¬ (∃ (k : ℕ) (m : Fin k → ℕ) (a : Fin k → ℤ),
      (∀ i, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ m i + 1 = p) ∧
      Function.Injective m ∧
      (∀ n : ℤ, ∃ i, n ≡ a i [ZMOD (m i : ℤ)])) := by
  sorry
```
- spent: $3.69

