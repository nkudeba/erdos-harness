# Open problem #242 — two-direction attack (run 20260923-113735-833279-erdos242)

**REQUIRES HUMAN REVIEW BEFORE ANY EXTERNAL CLAIM.** Automated formalization of an open problem can be subtly wrong; a Lean proof here certifies the FROZEN statement below, not necessarily the problem.

- English statement: For every $n>2$ there exist distinct integers $1\leq x<y<z$ such that\[\frac{4}{n} = \frac{1}{x}+\frac{1}{y}+\frac{1}{z}.\]
- triage: research — forced by --mode

Review milestones: {"schema_version": 1, "artifact_sha256": "eab7fa504a707fb7c5f424369fe09d8e162b889cc6ab995b15c44e3d51243572", "stage": "no_candidate", "candidate_solution": false, "mechanically_verified": false, "statement_independently_audited": false, "externally_reviewed": false, "resolution_claim_eligible": false, "scope": "full_problem_candidate", "catalogue_status_changed": false, "pending": ["clean_replay", "statement_audit", "adversarial_checks", "external_review"], "notice": "Operator-recorded review evidence; reviewer identity and independence require human verification. No automatic catalogue update."}
## Direction `pos` — outcome: **partial** (exit 3)
```lean
theorem erdos_242 (n : ℕ) (hn : 2 < n) :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
      (4 : ℚ) / (n : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ) := by
  sorry
```
- spent: $19.57

Review milestones: {"schema_version": 1, "artifact_sha256": "68d2d52a5aa1740c2191c8efd728f50983998593618b5450be5f487abe75bdb9", "stage": "no_candidate", "candidate_solution": false, "mechanically_verified": false, "statement_independently_audited": false, "externally_reviewed": false, "resolution_claim_eligible": false, "scope": "full_problem_candidate", "catalogue_status_changed": false, "pending": ["clean_replay", "statement_audit", "adversarial_checks", "external_review"], "notice": "Operator-recorded review evidence; reviewer identity and independence require human verification. No automatic catalogue update."}
## Direction `neg` — outcome: **partial** (exit 3)
```lean
theorem erdos_242_neg :
    ¬ (∀ n : ℕ, 2 < n →
      ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
        (4 : ℚ) / (n : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)) := by
  sorry
```
- spent: $3.26

