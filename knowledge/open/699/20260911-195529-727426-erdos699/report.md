# Open problem #699 — two-direction attack (run 20260911-195529-727426-erdos699)

**REQUIRES HUMAN REVIEW BEFORE ANY EXTERNAL CLAIM.** Automated formalization of an open problem can be subtly wrong; a Lean proof here certifies the FROZEN statement below, not necessarily the problem.

- English statement: Is it true that for every $1\leq i<j\leq n/2$ there exists some prime $p\geq i$ such that\[p\mid \textrm{gcd}\left(\binom{n}{i}, \binom{n}{j}\right)?\]
- triage: research — open + research depth and --allow-research; search skipped: a witness is already excluded below ~4.17e+19 (problem file), far past what the bounded search can enumerate (~1e+09), so the search stage could only re-derive a known check

Review milestones: {"schema_version": 1, "artifact_sha256": "ed7d8955d1d310017d2ae49f4152be24c2126aac5b33d5e0a502177d5f22417d", "stage": "no_candidate", "candidate_solution": false, "mechanically_verified": false, "statement_independently_audited": false, "externally_reviewed": false, "resolution_claim_eligible": false, "scope": "full_problem_candidate", "catalogue_status_changed": false, "pending": ["clean_replay", "statement_audit", "adversarial_checks", "external_review"], "notice": "Operator-recorded review evidence; reviewer identity and independence require human verification. No automatic catalogue update."}
## Direction `pos` — outcome: **infrastructure_error** (exit error: RuntimeError("claude -p returned an error result (reduce): success: You've hit your session limit · resets 11pm (America/Toronto)"))
```lean
theorem erdos_699 (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hjn : 2 * j ≤ n) :
    ∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i ∧ p ∣ Nat.choose n j := by
  sorry
```
- spent: $16.01

Review milestones: {"schema_version": 1, "artifact_sha256": "bec6a1ee63f6ef1ee0a11c1b8fb9a94b1497d512f698f94fad41e1b16f1c5aa6", "stage": "no_candidate", "candidate_solution": false, "mechanically_verified": false, "statement_independently_audited": false, "externally_reviewed": false, "resolution_claim_eligible": false, "scope": "full_problem_candidate", "catalogue_status_changed": false, "pending": ["clean_replay", "statement_audit", "adversarial_checks", "external_review"], "notice": "Operator-recorded review evidence; reviewer identity and independence require human verification. No automatic catalogue update."}
## Direction `neg` — outcome: **partial** (exit 3)
```lean
theorem erdos_699_neg : ¬ (∀ (n i j : ℕ), 1 ≤ i → i < j → 2 * j ≤ n →
    ∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.choose n i ∧ p ∣ Nat.choose n j) := by
  sorry
```
- spent: $13.19

