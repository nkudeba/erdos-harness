# Open problem #699 — two-direction attack (run 20260911-180317-544808-erdos699)

**REQUIRES HUMAN REVIEW BEFORE ANY EXTERNAL CLAIM.** Automated formalization of an open problem can be subtly wrong; a Lean proof here certifies the FROZEN statement below, not necessarily the problem.

- English statement: Is it true that for every $1\leq i<j\leq n/2$ there exists some prime $p\geq i$ such that\[p\mid \textrm{gcd}\left(\binom{n}{i}, \binom{n}{j}\right)?\]
- triage: fast — open + research depth without --allow-research: fast+agentic+decompose, then partial results; search skipped: a witness is already excluded below ~4.17e+19 (problem file), far past what the bounded search can enumerate (~1e+09), so the search stage could only re-derive a known check

Review milestones: {"schema_version": 1, "artifact_sha256": "34f8b690ebf228f4d0e79e1ddd2c407604cb97a0b08616c1f9205981e3ebd995", "stage": "no_candidate", "candidate_solution": false, "mechanically_verified": false, "statement_independently_audited": false, "externally_reviewed": false, "resolution_claim_eligible": false, "scope": "full_problem_candidate", "catalogue_status_changed": false, "pending": ["clean_replay", "statement_audit", "adversarial_checks", "external_review"], "notice": "Operator-recorded review evidence; reviewer identity and independence require human verification. No automatic catalogue update."}
## Direction `pos` — outcome: **budget_exhausted+partial** (exit 3)
```lean
theorem erdos_699 :
    ∀ n i j : ℕ, 1 ≤ i → i < j → 2 * j ≤ n →
      ∃ p : ℕ, Nat.Prime p ∧ i ≤ p ∧
        p ∣ Nat.gcd (Nat.choose n i) (Nat.choose n j) := by
  sorry
```
- partial results: {'dir': '/Users/nicolas.kudeba/workspace/erdos-harness/knowledge/partial/699/20260911-180317-544808-erdos699-pos', 'lemmas': ["quot_gcd_dvd_choose'", "dvd_descFactorial'"]}
- spent: $10.53

Review milestones: {"schema_version": 1, "artifact_sha256": "c9de82f66dc7ee9635f8c0fdb76ab03d9ba433e4f8aef157ea914d1a13e1fa8d", "stage": "no_candidate", "candidate_solution": false, "mechanically_verified": false, "statement_independently_audited": false, "externally_reviewed": false, "resolution_claim_eligible": false, "scope": "full_problem_candidate", "catalogue_status_changed": false, "pending": ["clean_replay", "statement_audit", "adversarial_checks", "external_review"], "notice": "Operator-recorded review evidence; reviewer identity and independence require human verification. No automatic catalogue update."}
## Direction `neg` — outcome: **budget_exhausted** (exit 2)
```lean
theorem erdos_699_neg :
    ¬ (∀ n i j : ℕ, 1 ≤ i → i < j → 2 * j ≤ n →
      ∃ p : ℕ, Nat.Prime p ∧ i ≤ p ∧
        p ∣ Nat.gcd (Nat.choose n i) (Nat.choose n j)) := by
  sorry
```
- spent: $6.59

