# Cheap judges for budget routing

**Question (operator, 2026-09-26):** can a fast, cheap model make the harness's quick judgment calls, so that the
expensive model's budget goes to the deductions? The call that matters most is "will an attack on this hypothesis
succeed?". The measurement behind that:
- Failed hypothesis attacks cost $317.6 (median $3.51 each).
- Successful ones cost a median of $0.22.
- 65% of the steps still open when unsolved runs ended were never attacked.

**Data:** `attacks.jsonl` holds 87 past hypothesis attacks (56 proved, 31 failed), each with its closed Lean statement,
outcome, cost and the plan's own difficulty rating. They come from train items and from runs outside the benchmark
only. The 155 dev attacks are excluded, because a judge chosen on them would carry dev solutions into every later
dev evaluation.

**Script:** `judge_eval.py --model <m>`. AUC is the chance a random proved attack scores above a random failed one
(0.5 = no signal).

## Haiku 4.5, statement only, 2026-09-26 ($1.05 for 87 judgments, $0.012 each)

| judge | items | AUC | Brier |
|---|---|---|---|
| the plan's own difficulty rating (free: the plan already writes it) | 55 rated | **0.981** | |
| statement length (free) | all 87 | 0.644 | |
| statement length (free) | 32 the plan did not rate | 0.693 | |
| Haiku p_success | all 87 | 0.786 | 0.266 |
| Haiku p_success | 55 rated | 0.857 | |
| Haiku p_success | 32 the plan did not rate | 0.641 | |
| always the base rate (0.64) | all 87 | 0.5 | 0.229 |

- **The plan's rating is already an almost perfect router.** Elementary: 29 proved of 29. Moderate: 5 of 6. Hard: 1
  of 20.
- **Haiku adds nothing.** On rated items it is worse than the free rating. On unrated items it is worse than
  statement length. Its probabilities score worse than a constant: it is ~30 points too pessimistic in every bin. It
  says 0.16 where 47% succeed, and 0.78 where 100% do. It agreed with the plan's rating on 28 of 55 items.
- **Decision:** no cheap judge for this call. The allocation fixes use the free signal, the plan's rating:
  - the sweep attacks easiest-first;
  - "hard" gets depth budget only after the cheap sweep.
- **Caveat:** Haiku saw only the Lean statement, while the plan's rating had the whole problem and skeleton. A judge
  given the same context costs more and still has to beat a free AUC of 0.98.

## Where a cheap model is still worth testing

A cheap **prover** is a different question from a cheap judge. Lean checks a proof for free, so a wrong cheap proof
costs only money. The next test would give Haiku one-shot proof attempts on the same 87 statements, compile them,
and compare the success rate and cost with Opus's one-shots. 224 of the 281 prove successes on disk came from
one-shot round 1.

## Jev (TypeSafe AI "System One" decision model, early access since 2026-09-15)

Jev returns typed values with probabilities, not text, at a claimed $0.042 per million input tokens. It could only
ever be a judge, not a prover. The same script scores it once there is API access (waitlist; the key would go in an
environment variable). The bar it must clear is:
- AUC above 0.69 on the unrated items;
- a Brier score below 0.229;
- ideally, approaching 0.98 on rated items.

Its own documentation says it is "not great with numbers", and these inputs are Lean statements.
