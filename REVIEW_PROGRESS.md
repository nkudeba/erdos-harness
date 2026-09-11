# Independent review and experiments

Work in progress. The earlier baseline used Claude; new runs use Codex, so differences between those runs cannot isolate the effect of code changes.

## Confirmed in this review

- Seven existing helper tests passed.
- Four archived proofs (#399, #493, #645, #674) recompiled with standard axioms and no sorry. This checks proof preservation, not fresh proof discovery.
- Added outcome tests for provider errors containing text, failed/malformed verification verdicts, and frozen-statement decoys in nested comments or strings. All passed.
- Run success now requires explicit boolean verification success. String `"false"` no longer passes the judge gate.
- Provider error text is rejected as an error instead of passed to the prover as a completion.
- Successful proof attempts are recorded. Unknown provider costs are reported as unavailable.
- Mock pipeline tests use a separate knowledge library instead of overwriting real proofs.
- Added a Codex CLI backend; a real provider smoke test passed. It uses a read-only sandbox for text completions.

## Active experiments

- #316 recovery completed: Lean and faithfulness verification passed.
- #532 baseline/current text runs both reached decomposition and then stopped on provider credits. Current had a compiling partial with three holes; baseline's latest repair had a type mismatch. These are incomplete experiments, not solve-rate wins.
- Real-Lean/scripted-model repair integration test passed with isolated knowledge output.

## Findings requiring more work

- The source declaration index is approximate, particularly generated additive declarations. Do not treat missing index hits as proof that a declaration does not exist.
- The textual statement guard does not establish equality of elaborated theorem types. Local notation, extra variables, or instances could change meaning without changing statement text.
- Replaced the learning command with isolated candidate lessons, disjoint held-out problems, identical frozen targets for before/after proof searches, strict gain/no-loss promotion, and saved-proof regression. Mocked workflow tests cover promotion, ties, regressions, and provider errors. A live learning cycle is still untested due provider credits.
- Existing reports from interrupted runs must not be counted as proof-search failures.
- No improvement in mathematical solve rate has yet been established in this review.

## Additional verified evidence

- `references/Erdos532.lean`: community proof adapted to the exact frozen target,
  compiled on the installed toolchain with no sorry and standard axioms.
- `runs/regress/regress-20260908-010810.md`: 7/7 passing, comprising six archived
  problem proofs (#316, #397, #399, #493, #645, #674) and the #532 reference fixture.
- Reference-assisted #532 is not counted as an autonomous solve.
- The assistant-assisted #370 proof passed after one compiler repair.
- Decomposition progress now checkpoints immediately, and final verification
  rechecks banned constructs and frozen text even for resumed proofs.

## Infrastructure

Codex returned “Your workspace is out of credits” during #532. No credit purchase,
reset, or quota change was attempted. The agentic run is inconclusive; its scratch
file is not a proof artifact. Continue offline checks without repeatedly calling
that backend.

Final consolidated findings: REVIEW_RESULTS.md. Final combined regression: 8/8 passed.
