# Independent harness review — September 8, 2026

## Result

Eight proof artifacts pass Lean compilation, no-sorry screening, banned-construct
screening, and standard-axiom checks. The combined report is `runs/regress/regress-20260908-011453.md`.

| Problem | Evidence | Classification |
|---|---|---|
| 493, 674 | Original proofs still pass | Saved-proof regressions |
| 399, 645, 397 | Earlier baseline proofs still pass | Saved-proof regressions |
| 316 | Recovered interrupted final verification; Lean and faithfulness passed | Recovered baseline result |
| 370 | New 50-line proof using n=(6t+8)(6t+10), repaired once and checked | Assistant-assisted proof |
| 532 | Community proof adapted to the frozen positive-integer target and checked | Reference-assisted fixture |

These are eight checked artifacts, **not eight fresh autonomous solves**. Fast
regression does not establish that a new search can rediscover each proof.

## Why #532 got stuck

Both the original and improved harness were tested with the same Codex provider,
one sample, two proof rounds, and two refinement rounds. Formalizations differed,
so this is an end-to-end comparison rather than a fixed-target ablation.

The text-only runs gravitated toward rebuilding the ultrafilter argument.
The improved run checked some progress and reached a partial with three holes;
the baseline's latest repair had a type mismatch. Both were interrupted by
workspace credits before completing the budget. A tool-enabled attempt was also
interrupted. None counts as a solve, and none proves the problem is beyond the
harness's capabilities.

The successful community route uses Mathlib's Hindman theorem on positive
naturals, then groups terms into successively larger blocks to make a strictly
increasing sequence while preserving finite sums. Taking a stream's range directly
is insufficient: streams may repeat, and zero is an additional trap over naturals.
`references/Erdos532.lean` includes this adaptation and retained attribution.

## What changed

- Codex text and tool-enabled backends, with provider failures treated as failures.
- Explicit boolean verification success required for a successful exit.
- Final banned-construct/frozen-text checks apply to resumed proofs too; a failed
  mechanical check skips model judgment.
- Nested comments and quoted code cannot satisfy the textual statement guard;
  string literal identity is preserved. This is still lexical screening, not an
  equality check on elaborated theorem types.
- Source-module retrieval through `-- READ:`; faster local search when rg exists.
- Partial proofs compile and remain available for decomposition, but never count
  as complete proofs. Compiler notes no longer inflate compiler-error counts.
- Successful attempts are logged; unknown provider cost remains unknown.
- Decomposition progress checkpoints immediately and resumes directly.
- Run IDs avoid same-second collisions, state saves replace files atomically,
  recorded problem input prevents incompatible checkpoint reuse.
- Mock tests isolate knowledge and run pointers. Restored #674's real provenance
  after discovering the old mock had overwritten it.
- Helper fragments are labeled as context-dependent, not independently verified.

## Learning loop

`learning.py` replaces immediate lesson promotion with staged candidate knowledge.
Training and evaluation problem IDs are disjoint. Before/after proof searches use
the same frozen statement and literature context, with isolated knowledge copies.
Promotion requires a strict held-out gain, preservation of earlier successes,
and passing saved-proof regression. Ties, regressions, and provider failures leave
active lessons unchanged. Training does not change model weights or rewrite code.

Tests exercise strict-gain promotion, rejection on ties/regressions/provider errors,
and identical evaluation statements. A live paid cycle remains untested. One
stochastic gain would still need replication before claiming general improvement.

## Validation

- 7 original helper tests passed.
- 9 outcome/checkpoint/retrieval tests passed.
- 2 learning tests passed, including multiple promotion/rejection scenarios.
- Real Lean plus scripted-model repair pipeline passed with isolated knowledge.
- Combined artifact regression: **8 passed, 0 failed**.
- #370's final standalone check had no warnings and only propext,
  Classical.choice, and Quot.sound.

## Next experiments

After provider credits are available, run repeated fixed-statement comparisons on
#532 with source access versus text-only retrieval; then use #370 or #198 as a
held-out transfer case. Keep reference-assisted runs separate from autonomous
search. Current results do not establish an autonomous solve-rate gain.


## 8 September comparison retry

Retried the matched #532 comparison. Initial provider-credit errors were followed by a successful probe and resumed runs; both then timed out on refinement calls at 900 seconds. Zero comparison pairs completed, so autonomous solve-rate improvement remains unproven. Details: [retry report](runs/comparison-retry-20260908/report.md).


## Completed fresh comparison — 8 September, 15:47 UTC

The sequential fresh #532 pair completed without provider failures: baseline 0/1 verified solves (15.51 minutes), improved 0/1 (13.09 minutes), under matching model and search budgets. The improved final candidate had no explicit sorry placeholders but two Lean errors. Observed solve-rate difference on this one problem is zero; a general solve-rate gain remains unproven. See [completed pair report](runs/comparison-retry-20260908/completed-pair-report.md).


## #532 repair success — 8 September 2026

Corrected stale candidate/error pairing in refinement and persisted failed candidates across resume. In a separate common-repair extension (three extra rounds allowed per candidate), the improved candidate solved #532 in one round and passed compilation, frozen-statement, axiom, and faithfulness checks. The baseline candidate remained unverified after three rounds; a credit interruption was resumed without resetting its allowance. No manual proof edits or reference proof were supplied. All 11 currently saved proof files passed regression. This is a targeted repair success, not a general solve-rate estimate. See [repair report](runs/comparison-retry-20260908/repair-extension/report.md).
