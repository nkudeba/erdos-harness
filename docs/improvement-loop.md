# The harness improvement loop

A self-driving loop that improves the harness until it solves an Erdős problem. It is started from Claude Code with:

```
/loop Advance the harness improvement loop by one step, following docs/improvement-loop.md
```

Each wake-up reads `benchmarks/timesplit/loop/state.json`, does the ONE next step of the current phase, records it,
and schedules the next wake-up. While a run is in flight, it sleeps for a long time instead of polling. The machinery
is `benchmarks/timesplit/loop.py` (state, budget, diagnosis, branch commits) and `benchmarks/timesplit/timesplit.py`
(runs, screens, scoring). Neither makes a model call on its own.

## Authority (operator, 2026-09-25)

- **Budget: $200** for everything the loop launches: harness runs, screens, calibrations and judges.
  `loop.py status` shows what is spent and what is reserved. Before any launch, `loop.py can-spend --usd <estimate>`
  must say OK. The session driving the loop also spends; that cost is not measurable from here, and it is not
  counted against the cap.
- **Commit to branch `harness-loop`** through `loop.py commit`, never to `main`, and never push. The commit is
  built in a temporary index: HEAD, the index and the working tree are untouched, because another session shares
  this checkout. Merging is the operator's decision.
- **Dev evaluations may be launched without asking**, within the budget.

## Stopping conditions (checked at every wake-up, in this order)

`loop.py status` checks conditions 1 and 4 mechanically. It prints a `STOP SIGNAL` line for every dev or test solve
and every contradiction in ANY results file, including lanes the operator started, until `loop.py ack` records that
the signal was handled. Start every wake-up with it. The check exists because the loop once scored only its own
tags: dev #1213, solved by the operator's discover-v2 lane at 09:00Z on 2026-09-25, went unnoticed until 17:15Z.

1. **A solve.** A time-split item's TRUE direction is verified (`solved` in its record, with no contradiction), on
   dev or test.
   - Re-run it once on a fresh alias to replicate. Then stop, send a push notification, and write the evidence to
     RESULTS.md.
   - A verified proof on a real open problem also stops the loop, for human review; `claimEligible` stays false.
2. **The budget.** When `left` falls below the cheapest next step, finish what is in flight, record it, and stop.
3. **A plateau.** Four consecutive iterations rejected: stop and write up what was learned.
4. **A contradiction.** A verified proof of the WRONG direction stops everything until the item is re-audited.

To stop: `loop.py set --stop "<reason>"`, a PushNotification to the operator, then `ScheduleWakeup(stop=true)`.

## One iteration

`state.phase` moves through these phases. One wake-up does one phase, or one wait.

1. **diagnose**
   - Run `loop.py diagnose --since <start of the last iteration>`, and `score` / `progress` / `ideas` for the last
     evaluation.
   - Write `loop/iterations/<n>.md`: what happened, what the numbers say, and a critique. Which assumption might be
     wrong? Is the instrument trustworthy? Look especially for a stage that never succeeds or a cost that jumped.
     Today's biggest finds (the cascade at 0/71, the connectors at $2.60 a session, silent refusals, discarded
     over-cap answers) were all visible in the logs.
2. **propose**
   - Pick ONE change aimed at the top blocker, or a small bundle declared as one.
   - Write its hypothesis, the prediction, and the gate it must pass into `benchmarks/timesplit/RESULTS.md`, BEFORE
     anything is launched.
   - Every third iteration must be structural, not a tweak: a new stage, representation or search strategy. Look at
     how the systems that actually resolved these problems in 2026 worked.
3. **implement**
   - Delegate the code to a Sonnet subagent with a precise spec: files, behaviour, tests.
   - Review its diff yourself. `python3 -m unittest discover -s tests` must pass.
   - A new capability goes behind a flag, default off; a clear bug fix may go on by default, recorded in
     CLAUDE.md.
   - Commit with `loop.py commit`.
4. **screen**, cheapest informative check first:
   - **replay** (free): recompile or re-parse saved artifacts (see `analysis/cascade_replay.py`).
   - **explore-screen** (about $1.50 an item, train): `timesplit.py explore-screen --tag <t>`, then `ideas --tag <t>`
     against the tool-less baseline (`ideas --tag calib-ideas --from-calibration train-v2r1`, graded once).
   - **dev screen** (about $8 an item): the first 5 dev items, candidate and baseline on the SAME pin, with the
     paired `(solved, pieces AND certified_size)` rule.
   - `pin` a candidate before its first run. Before each launch: `loop.py register --kind ... --name <tag>
     --estimate <usd>`.
5. **wait**
   - While something is in flight: `ScheduleWakeup` 1800-3600 s. A long fallback is fine; the harness does not
     notify.
   - When it lands: `progress`, `ideas`, `score --baseline`; then `loop.py finish --name <tag>`.
6. **decide**, by the rule written in step 2:
   - A screen that passes may be extended to the full dev split if the budget allows.
   - A kept change becomes the new baseline, pinned; a rejected one is reverted or left behind its flag.
   - Record the outcome under the prediction in RESULTS.md.
   - Commit, set `iteration += 1` and `phase = diagnose`.

## Delegation: keep the expensive model for insight

| work | who |
|---|---|
| diagnosis, budgets, scoring, replays, calibration, commits | code (`loop.py`, `timesplit.py`) |
| summarising or clustering TRAIN transcripts and failure digests | Haiku subagent (`model: "haiku"`) |
| implementing a specified change, and its tests | Sonnet subagent (`model: "sonnet"`) |
| critique, proposals, gate decisions, reviewing diffs | the loop itself (Opus) |
| inside the harness: exploration, plans, core attacks | the strongest model, with more budget |

A harness stage moves to a cheaper model only after an agreement check against Opus on saved inputs. The honesty
judges (circularity, refinement, faithfulness) never move.

## Rules that do not bend

- **Quarantine.** Read transcripts of TRAIN runs only. Dev and test are read through aggregate numbers alone
  (`diagnose`, `score`, `progress`, `ideas`), never their transcripts, notebooks or residuals. Idea notes exist for
  train only.
- **Honesty gates are off limits:** Lean verification, frozen-statement checks, the circularity and refinement
  judges' semantics, contradiction handling, `claimEligible`. A change there stops the loop and asks the operator.
- **Never delete** runs, results, knowledge or other sessions' work. Never kill a process the loop did not start.
- **At most one heavy lane launched by the loop at a time.** Lanes the operator started (the discover-v2 dev lane,
  for one) keep running beside it, and the loop never stops them. The usage limit is shared, and the runners wait
  out a limit and resume by themselves. Check `pgrep -f "harness.py run"` before launching, and do not launch a
  second loop lane while one is in flight.
- **Every prediction is written before its launch.** Every outcome is recorded, including failures.
- **Pinned evaluations.** Compare a candidate only with a baseline run on the same pin and items.

## State file

`benchmarks/timesplit/loop/state.json`:
- `goal`, `iteration`, `phase`, `candidate`, `baseline`, `stop`;
- `ledger` (every launch and its estimate; `loop.py status` computes the actual spend);
- `notes` (short records of decisions).

Keep it small; the detail lives in `loop/iterations/<n>.md` and RESULTS.md.
