# Open problem #7 — two-direction attack (run 20260911-164451-984441-erdos7)

**REQUIRES HUMAN REVIEW BEFORE ANY EXTERNAL CLAIM.** Automated formalization of an open problem can be subtly wrong; a Lean proof here certifies the FROZEN statement below, not necessarily the problem.

- English statement: Is there a distinct covering system all of whose moduli are odd?
- triage: search-first — site class verifiable (a bounded computation could decide/exhibit it)

Review milestones: {"schema_version": 1, "artifact_sha256": "dcb6f3399ad2aef7b7da764ccf5d87f3ae9df26e98a95b0f40b247fdfa001f9b", "stage": "no_candidate", "candidate_solution": false, "mechanically_verified": false, "statement_independently_audited": false, "externally_reviewed": false, "resolution_claim_eligible": false, "scope": "full_problem_candidate", "catalogue_status_changed": false, "pending": ["clean_replay", "statement_audit", "adversarial_checks", "external_review"], "notice": "Operator-recorded review evidence; reviewer identity and independence require human verification. No automatic catalogue update."}
## Direction `pos` — outcome: **not_proved** (exit 2)
```lean
-- CHECK: Function.Injective Odd Int.dvd_iff_emod_eq_zero
theorem erdos_7 :
    ∃ (k : ℕ) (m : Fin k → ℕ) (a : Fin k → ℤ),
      (∀ i, 1 < m i) ∧
      (∀ i, Odd (m i)) ∧
      Function.Injective m ∧
      (∀ n : ℤ, ∃ i, (m i : ℤ) ∣ (n - a i)) := by
  sorry
```
- spent: $8.46

Review milestones: {"schema_version": 1, "artifact_sha256": "0c6ed148f46a820b1b7c371b0966a57b8014e8ac8d515b797c82a4686c2242a5", "stage": "no_candidate", "candidate_solution": false, "mechanically_verified": false, "statement_independently_audited": false, "externally_reviewed": false, "resolution_claim_eligible": false, "scope": "full_problem_candidate", "catalogue_status_changed": false, "pending": ["clean_replay", "statement_audit", "adversarial_checks", "external_review"], "notice": "Operator-recorded review evidence; reviewer identity and independence require human verification. No automatic catalogue update."}
## Direction `neg` — outcome: **not_proved** (exit 2)
```lean
-- CHECK: Function.Injective Odd Int.dvd_iff_emod_eq_zero
theorem erdos_7_neg :
    ¬ (∃ (k : ℕ) (m : Fin k → ℕ) (a : Fin k → ℤ),
      (∀ i, 1 < m i) ∧
      (∀ i, Odd (m i)) ∧
      Function.Injective m ∧
      (∀ n : ℤ, ∃ i, (m i : ℤ) ∣ (n - a i))) := by
  sorry
```
- spent: $8.81

