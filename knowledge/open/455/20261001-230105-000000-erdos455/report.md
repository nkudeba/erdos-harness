# Open problem #455 — two-direction attack (run 20261001-230105-000000-erdos455)

**REQUIRES HUMAN REVIEW BEFORE ANY EXTERNAL CLAIM.** Automated formalization of an open problem can be subtly wrong; a Lean proof here certifies the FROZEN statement below, not necessarily the problem.

- English statement: Let $q_1<q_2<\cdots$ be a sequence of primes such that\[q_{n+1}-q_n\geq q_n-q_{n-1}.\]Must\[\lim_n \frac{q_n}{n^2}=\infty?\]
- triage: research — operator: open problem #455, attacked with the 2026-10-02 discovery features

Review milestones: {"schema_version": 1, "artifact_sha256": "5cbbecbf6b3172f7f4d531bc3662f596b3c887d8b3c1fbe99aa8fc17d92d1613", "stage": "no_candidate", "candidate_solution": false, "mechanically_verified": false, "statement_independently_audited": false, "externally_reviewed": false, "resolution_claim_eligible": false, "scope": "full_problem_candidate", "catalogue_status_changed": false, "pending": ["clean_replay", "statement_audit", "adversarial_checks", "external_review"], "notice": "Operator-recorded review evidence; reviewer identity and independence require human verification. No automatic catalogue update."}
## Direction `pos` — outcome: **partial** (exit 3)
```lean
open Filter ENNReal

theorem erdos_455 :
    ∀ q : ℕ → ℕ, StrictMono q →
    (∀ n, (q n).Prime ∧ q (n + 2) - q (n + 1) ≥ q (n + 1) - q n) →
    Tendsto (fun n : ℕ => (q n : ℝ) / n ^ 2) atTop atTop := by
  sorry
```
- spent: $15.13

## Direction `neg` — not attacked: the discovery stage committed to `pos`

