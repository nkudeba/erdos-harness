# Three promising untried Erdős candidates

**Scope correction (2026-09-10).** The operator's original request was for the three most promising
*unsolved* problems in the sense of **open on erdosproblems.com** — problems nobody has resolved. This
experiment instead selected the three highest-ranked problems *untried by the harness*, all of which have
published resolutions. The reconstruction results below stand on their own terms, but they do not answer
the question that was asked. The open-problem selection is being done separately; see the `open-top3`
work that follows this experiment.

Selected from the Atlas ranking after checking actual run history: #649 (rank 12, score 87), #105 (rank 14, score 73), and #275 (rank 15, score 70). #280 was excluded because a recent Claude run had already attempted and solved it. All three selected problems have published resolutions; these are reconstruction experiments, not claims to resolve open mathematics.

## Final results

| Problem | Final result | Recovery needed |
|---|---|---|
| #649 | Full harness checks passed for the positive-integer interpretation | Private helper layout normalized |
| #105 | Full harness checks passed; nine blue points and six blockers | Redundant finite-case tactics and simplification repaired |
| #275 | Full harness checks passed for the universal congruence-covering theorem | Generated proof unchanged; interrupted final audit resumed |

All three use only `Classical.choice`, `Quot.sound`, and `propext`, with no proof gaps. All remain at `mechanically_verified`, with `claimEligible=false`; independent review is pending. The final Python suite ran 87 tests: 76 passed and 11 optional tests skipped. The separate prior-proof replay passed all 11 included proofs.

## Experiment conditions and assistance

Initial Claude runs exhausted their bounded web-research calls before saving a checkpoint. The operator reconstructed the problem-input checkpoint and supplied only the original problem's published informal resolution notes as the literature context. Subsequent Claude attempts hit an account spending limit, so proof generation continued with Codex. Codex also eventually exhausted workspace credits.

No external Lean solution was supplied to the proof generator. The saved Codex artifacts survived the provider failures. Recovery used the file backend with zero new proof-generation rounds. The current Codex assistant supplied the final plain-English backtranslations and statement comparisons through that backend; these are operator-assisted semantic audits, not independent human review.

The auxiliary 12-blue/9-red configuration and sparse-polynomial proof guide researched by the operator were not supplied to these proof-generation runs. In particular, #105's actual saved proof uses a different 9-blue/6-red configuration discovered during its run.

## Lessons applied to the harness

- Preserve initial run state before research, and preserve mechanical verification before a semantic audit. Provider failures no longer erase completed milestones.
- Recover complete saved sandbox candidates on resume, before requesting new proof work. Keep the original frozen-statement, no-gap, compiler and axiom gates.
- Hoist interleaved private helpers when the exact frozen definitions and theorem remain unchanged. This repairs #649's rejected layout without relaxing the target.
- Repair narrowly recognized `left`/`right`/`linarith` branches that report only “No goals to be solved,” including whole-context normalization and branch searches reached after simplification already closes a case. A second bounded pass handles redundant `simp only` calls reporting “made no progress.” Every retry logs its own diagnostics, even when the error count is unchanged. Full compilation must still pass. Final verification checks the saved artifact without silently applying this tactic repair.
- Deduplicate compiler diagnostics so repeated finite-case errors do not bury useful feedback.
- Treat “out of credits” as a hard provider failure. Count failed-call costs when reported, and check the run budget before further calls.
- Permit bounded literature lookup failures to fall back to existing source notes, with provenance. Authentication/account-limit failures still stop the run.
- Pass retrieved informal proof routes to formalization so representation choices can reflect the proof strategy without weakening the target.
- Add explicitly attributed `--informal-context` input and an exact projective-to-affine blocking-witness prechecker for future assisted experiments. Neither is a replacement for a Lean proof.

## Verification boundaries

Lean compilation, no proof gaps, exact frozen target matching and the standard-axiom audit are mechanical requirements. Automated/operator semantic comparison does not satisfy the independent review milestones. None of these runs is eligible for an external resolution claim until those milestones are completed.

For #649, the proof addresses positive integers, as intended by the supplied published resolution notes. The literal word “integer” would need clarification if negative values with greatest prime factor defined using absolute value were intended: n = -8 realizes the particular pair p = 2, q = 7. This caveat is retained in the saved semantic verdict.

This small, deliberately favorable trio, resumed across providers and repaired with operator involvement, does not estimate an autonomous solve rate or establish a statistically measured improvement. It does demonstrate concrete recoverable failure modes. Recorded cost data are incomplete, particularly for Codex and the earliest failed web calls; unavailable costs are not zero.

## Evidence

The individual run logs, final artifacts, state checkpoints, `results.json`, and `live-feed-check.json` accompany this report. `regression.log` records 11 previously verified proofs passing Lean again (198, 316, 363, 370, 397, 399, 493, 532, 645, 674, 1193). That replay preceded the final recovery/checkpoint edits; the full Python suite was rerun after those edits. `105-discovered-witness-check.json` records an additional exact-rational incidence check for all 36 unordered pairs in the actual nine-point witness.

The live site's existing publisher watches these run records and updates the results feed automatically. Published mathematical status remains separate from harness run outcomes and review milestones.

Source statements and supplied discussion: [#649](https://www.erdosproblems.com/649), [#105](https://www.erdosproblems.com/105), [#275](https://www.erdosproblems.com/275). The retrieved informal [#105 forum discussion](https://www.erdosproblems.com/forum/thread/105) and [covering-intervals paper](https://par.nsf.gov/servlets/purl/10165575) are saved beside this report for research provenance.

---

## Continuation (Claude Opus 5 session, 2026-09-10, after Codex exhausted its credits)

Two gaps this report names for itself are now closed, and one new caveat is recorded.

**Lean replay after the final edits.** The regression referenced above ran before the recovery and
checkpoint edits of 11:23–11:46. It was rerun afterwards over the whole saved corpus, now 16 proofs:
**16 passed, 0 failed**, every one compiling sorry-free with only `Classical.choice`, `Quot.sound` and
`propext`. This covers #649, #105 and #275 in their post-edit form, plus #280 and #499 from the parallel
ladder lane. Evidence: `regression-after-final-edits.log`. The Python suite was also rerun independently:
87 tests, 76 passed, 11 skipped, 0 failed, matching the figure above.

**Independent-ish statement review.** A second assistant re-read the three frozen statements against the
erdosproblems.com sources: `STATEMENT-REVIEW-claude.md`. All three are faithful. The #649 positive-integer
caveat is confirmed as real but not damaging, because the site's own discussion disproves the question with
exactly p = 2, q = 7 under that reading. This is still not the independent human review the milestones
require, and `claimEligible` stays false for all three.

**Audit of the harness changes made during the experiment.** The new automatic repairs were checked for
gate weakening and none was found: `normalize_helper_layout` only reorders unchanged private lemmas and
re-checks `contains_frozen`; `repair_closed_goal_branches` fires only when every diagnostic is in the
harmless class, recompiles, and keeps the result only if it compiles or strictly reduces the error count;
sandbox recovery re-runs the hole, frozen and banned gates before compiling; and final verification is
explicitly exempt from tactic repair. The Lean compiler remains the ground truth in every path.

**Caveat added by this review.** `formalize_prompt` now receives the retrieved literature as a "retrieved
informal proof route". Combined with the operator-supplied resolution notes, the proof strategy can shape
the choice of formalization. #649's positive-integer domain is a concrete instance. This is disclosed
above, but it is worth stating as a standing property of the pipeline rather than a one-off.
