# Open problem #273 — two-direction attack (run 20260911-151747-638616-erdos273)

**REQUIRES HUMAN REVIEW BEFORE ANY EXTERNAL CLAIM.** Automated formalization of an open problem can be subtly wrong; a Lean proof here certifies the FROZEN statement below, not necessarily the problem.

- English statement: Is there a covering system all of whose moduli are of the form $p-1$ for some primes $p\geq 5$?
- triage: search-first — shape=witness, computable=True

Review milestones: {"schema_version": 1, "artifact_sha256": "b3bfed98c100a55d2d6b5d2e9a17198795493afdaa9ad3a39c92d79577608a38", "stage": "no_candidate", "candidate_solution": false, "mechanically_verified": false, "statement_independently_audited": false, "externally_reviewed": false, "resolution_claim_eligible": false, "scope": "full_problem_candidate", "catalogue_status_changed": false, "pending": ["clean_replay", "statement_audit", "adversarial_checks", "external_review"], "notice": "Operator-recorded review evidence; reviewer identity and independence require human verification. No automatic catalogue update."}
## Direction `pos` — outcome: **budget_exhausted** (exit 2)
```lean
theorem erdos_273 :
    ∃ (k : ℕ) (a : Fin k → ℤ) (m : Fin k → ℕ),
      (∀ i, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ m i = p - 1) ∧
      Function.Injective m ∧
      (∀ n : ℤ, ∃ i, (m i : ℤ) ∣ (n - a i)) := by
  sorry
```
- spent: $10.80

Review milestones: {"schema_version": 1, "artifact_sha256": "ea248a0fdf327a3a0cf720666fa04dca4d2792bb25fa5b1cc543242ae88a1c0a", "stage": "no_candidate", "candidate_solution": false, "mechanically_verified": false, "statement_independently_audited": false, "externally_reviewed": false, "resolution_claim_eligible": false, "scope": "full_problem_candidate", "catalogue_status_changed": false, "pending": ["clean_replay", "statement_audit", "adversarial_checks", "external_review"], "notice": "Operator-recorded review evidence; reviewer identity and independence require human verification. No automatic catalogue update."}
## Direction `neg` — outcome: **not_proved** (exit 2)
```lean
theorem erdos_273_neg :
    ¬ (∃ (k : ℕ) (a : Fin k → ℤ) (m : Fin k → ℕ),
      (∀ i, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ m i = p - 1) ∧
      Function.Injective m ∧
      (∀ n : ℤ, ∃ i, (m i : ℤ) ∣ (n - a i))) := by
  sorry
```
- spent: $8.74

