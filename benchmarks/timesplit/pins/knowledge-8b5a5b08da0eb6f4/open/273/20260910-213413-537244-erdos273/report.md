# Open problem #273 — two-direction attack (run 20260910-213413-537244-erdos273)

**REQUIRES HUMAN REVIEW BEFORE ANY EXTERNAL CLAIM.** Automated formalization of an open problem can be subtly wrong; a Lean proof here certifies the FROZEN statement below, not necessarily the problem.

- English statement: Is there a covering system all of whose moduli are of the form $p-1$ for some primes $p\geq 5$?
- triage: search-first — shape=witness, computable=True

Review milestones: {"schema_version": 1, "artifact_sha256": "40dacc550ff1a0d0e3b99df52a151b774aeba888f93b9ba21c0a0a8a710e5b0a", "stage": "no_candidate", "candidate_solution": false, "mechanically_verified": false, "statement_independently_audited": false, "externally_reviewed": false, "resolution_claim_eligible": false, "scope": "full_problem_candidate", "catalogue_status_changed": false, "pending": ["clean_replay", "statement_audit", "adversarial_checks", "external_review"], "notice": "Operator-recorded review evidence; reviewer identity and independence require human verification. No automatic catalogue update."}
## Direction `pos` — outcome: **infrastructure_error** (exit error: AttributeError("'NoneType' object has no attribute 'group'"))
```lean
theorem erdos_273 :
    ∃ S : Finset (ℤ × ℕ),
      (∀ x ∈ S, ∃ p : ℕ, Nat.Prime p ∧ 5 ≤ p ∧ x.2 = p - 1) ∧
      (∀ x ∈ S, ∀ y ∈ S, x.2 = y.2 → x = y) ∧
      (∀ n : ℤ, ∃ x ∈ S, ((x.2 : ℤ)) ∣ (n - x.1)) := by
  sorry
```
- spent: $9.29

Review milestones: {"schema_version": 1, "artifact_sha256": "5ca45a7a200bef957cd58b47df12d85fc14af01a4dee12e34f93bb4bb62ea58c", "stage": "no_candidate", "candidate_solution": false, "mechanically_verified": false, "statement_independently_audited": false, "externally_reviewed": false, "resolution_claim_eligible": false, "scope": "full_problem_candidate", "catalogue_status_changed": false, "pending": ["clean_replay", "statement_audit", "adversarial_checks", "external_review"], "notice": "Operator-recorded review evidence; reviewer identity and independence require human verification. No automatic catalogue update."}
## Direction `neg` — outcome: **not_proved** (exit 2)
```lean
theorem erdos_273_neg :
    ¬ (∃ S : Finset (ℤ × ℕ),
      (∀ x ∈ S, ∃ p : ℕ, Nat.Prime p ∧ 5 ≤ p ∧ x.2 = p - 1) ∧
      (∀ x ∈ S, ∀ y ∈ S, x.2 = y.2 → x = y) ∧
      (∀ n : ℤ, ∃ x ∈ S, ((x.2 : ℤ)) ∣ (n - x.1))) := by
  sorry
```
- spent: $7.09

