# Time-split benchmark results

One section per evaluation. Predictions are written **before** launch, and nothing below them is edited after the
outcomes arrive. Per-item outcomes live in `results/<tag>.jsonl`, and `score --tag <tag> --baseline <tag>`
reprints them.

## Baseline, 2026-09-24: `baseline-8b5a5b0`

**Protocol.**
- Pinned code: `pin_8b5a5b08da0eb6f4_harness.py`, an identical copy of `harness.py` at `ce09b11`.
- Pinned knowledge: `pins/knowledge-8b5a5b08da0eb6f4` (without `solved/` and the lemma store).
- Model and budget: `claude-opus-5-5`, **$8 per item for both directions together**.
- Loop settings: 2 research cycles, 3 hypotheses per cycle, literature stage on (model memory, no web).
- Machine limits: `--lean-timeout 1800`, 2 compile workers, a 3 h wall-clock cap per item.
- Order: dev (18 items), then test (2).

This runs as a second lane beside the other session's masked-benchmark lane, a budget decision the operator made
explicitly (CLAUDE.md: concurrent lanes do not corrupt each other).

**Write-ahead predictions** (my estimates from the statements alone; no transcript or solution was read):

| split | expected solved | range | P(at least one) |
|---|---|---|---|
| dev (18) | 1.0 | 0-3 | 0.55 |
| test (2) | 0.06 | 0-1 | 0.06 |

Per item on dev, P(solved):

- #1125: 0.20. A functional inequality; an elementary argument probably exists.
- #401: 0.10; #729: 0.08.
- #457, #825, #888, #204, #537: 0.05 each.
- The other ten: 0.02–0.04 each.

On test: #193 at 0.05 (needs an explicit infinite construction) and #547 at 0.01.

I also expect:
- a contradiction (a verified wrong direction) with probability 0.05;
- one to three infrastructure failures, because two lanes share the usage limit and an 8-core machine.

**Outcome: stopped after one item, because the first item exposed a harness bug.** #150 (unsolved, $1.83 of $8):

- Both directions ran their two cycles, and **every hypothesis the loop tried to attack was rejected before a
  proof was attempted**, with `Unknown identifier 'Tendsto'` (pos) and `'atTop'` (neg).
- The cause is in `hypothesis_substatement`: a child statement is built from the skeleton's `def`s only, so
  the frozen statement's `open Filter` never reaches it. Any statement written under an `open` loses every
  hypothesis that uses the opened names. That covers most formal-conjectures statements, and any real open-problem
  run whose frozen statement opens a namespace.
- The other hypotheses were deferred: about $3.5 left per direction, against the $2.50 minimum per child.

The second item (#202) was stopped mid-run and is not scored.

## Baseline v2, 2026-09-24: `baseline-v2-84f21c5`

**Protocol** as above, except for the code:
- Harness: `pin_84f21c561c540e02_harness.py`, which is `harness.py` at `ce09b11` plus
  [`pins/fix-opens.patch`](pins/fix-opens.patch).
- The patch adds `skeleton_context`: sub-statements carry the top-level `open`s in force at the hypothesis, and
  an `open X in` travels only with the definition it precedes.
- Verified in Lean before launch: the old child statement fails with `Unknown identifier 'Tendsto'`; the fixed one
  compiles.
- The live `harness.py` is untouched: the fix goes upstream only once measured.

**Predictions:** those written above stand unchanged. They were made before any outcome. #150's unsolved result
under the buggy code was seen before this launch.

**Outcome.** To be filled in when the lane finishes.

### Usage-limit event, 2026-09-24 ~07:00–07:25 EDT

Four concurrent lanes (baseline v2, discover-v1, discover-v2 and the train diagnostic) exhausted the account's
session limit after about 4 hours ("resets 8:10am"). Every lane recorded its next items as infrastructure and
stopped; v1's #419 was killed mid-prove. By design, nothing interrupted was recorded as a result.

**What changed:**
- The runner now **waits out a usage limit** (the reset time is parsed from the error). It then either resumes
  the same run in place (`--resume`), if the harness got past its first stage, or restarts the item fresh, if the
  limit struck discovery.
- **The limit, not the lane count, sets the pace.** Parallel lanes only hit it sooner and kill more in-flight runs.
  So from 12:12 EDT two lanes run: baseline v2 (10 dev items left) and discover-v2 (18).
- **discover-v1 is paused at 5 of 18.** v2 is v1 plus the fixes its diagnostics called for, and v1's value is now
  ablation only. The test split runs once dev is decided.

### Baseline v2 paused after #729, 2026-09-24 ~16:15 EDT (operator's request)

The pause frees CPU for discover-v2. The baseline had 10 of 18 dev items done, all unsolved ($47.84). #729 finished
under its own run; the runner was stopped so it would not start another item. The deferred items are #825, #865,
#871, #888, #1125, #1180 and #1213.

**Before any verdict:** run the baseline on every item discover-v2 solves (a win counts only against the
baseline's own run), and ideally on all the deferred items, so a baseline-only solve is not missed. Resume with:

```bash
python3 benchmarks/timesplit/timesplit.py run --split dev --harness pin_84f21c561c540e02_harness.py \
  --knowledge benchmarks/timesplit/pins/knowledge-8b5a5b08da0eb6f4 --budget 8 --allow-concurrent --tag baseline-v2-84f21c5
```

## Top-up arm, 2026-09-24: `discover-v2-84f21c5+topup16` (operator's request)

An unsolved discover-v2 run whose committed direction ends **at most one open conjecture short** is resumed in
place with its total budget raised to **$16**. Its certified hypotheses stay; only the residual is attacked. The
trigger reads the run's own residual, never the answer. The $8 arm is unchanged, and every item's total spend is
recorded, so solves per dollar remain comparable.

The first item is **#150**. After $8.02 it had 2 hypotheses certified and 1 open: `hyp_limit`, a limit via
Fekete's lemma on super-multiplicative pole counts. discover-v2's second round had proved that step informally,
and the referee accepted it. Mathlib has Fekete's lemma for subadditive sequences.

**Write-ahead:** P(#150 closes with the extra ~$8) = 0.35. It closes only if the prover finds the log transform to
subadditivity, plus the super-multiplicativity estimate, in Lean.

**Outcome (15:45 EDT): not closed.** The spend went from $8.02 to $17.24, overshooting the $16 total by $1.24 on its
last call. The residual is unchanged at 3 certified and 1 open (`hyp_limit`).

The resumed program first tried a `define` move to restructure around the open step, which was rejected as no
improvement over the skeleton in force. It then spent the rest attacking `hyp_limit` without closing it. On this
item, doubling the budget bought no progress at all: the missing step is hard to formalize, not merely
under-funded.

## Candidate discover-v1, 2026-09-24: `discover-v1-84f21c5`

**What changes.** The same pinned harness, knowledge, $8 budget and settings as baseline v2. Before the harness
starts, the runner:

1. runs **2 parallel informal attempts** at high effort, each capped at $1.20, one leading with construction or
   counterexample and one with a structural argument;
2. gives each attempt that claims a complete proof a **referee pass** (medium effort, capped at $0.30);
3. **commits to one direction** when the attempts agree (≥ 75% of the weight, and either a refereed proof or
   unanimity), spending the remaining budget there; otherwise it runs both directions, as the baseline does;
4. hands the best attempt's key steps, gap and text to every research stage as guidance.

The live `harness.py` is unchanged. The candidate lane runs **in parallel with the baseline v2 lane**, over the
same items in the same order, so both arms see the same machine load and API conditions.

The design comes from evidence outside this benchmark (the #242 and #275 research runs), not from dev
transcripts. Calibration used only train item #1148: at $0.50 per attempt, high effort overran the cap every
time. At a $1.50 cap it cost $0.77 and took 7 minutes. High and medium effort both gave the correct direction,
and neither completed a proof.

**Write-ahead predictions:**
- The attempts commit on about 70% of items, and a commitment points the right way about 85% of the time.
- dev: an expected 1.5 solved (range 0–4), against 1.0 for the baseline.
- P(the candidate solves strictly more dev items than the baseline): 0.45.
- P(an evident gain, meaning 3 or more more discordant items in its favour and none against): 0.15.
- A committed wrong direction wastes that item: expect 1 or 2 such items.

**Outcome.** To be filled in when the lane finishes.

## Candidate discover-v2, 2026-09-24: `discover-v2-84f21c5`

**Why v2 exists.** Everything below comes from train runs (quarantine rule) and from v1's aggregate mechanics,
never from dev transcripts.

- **Train #152:** the harness certified every step the discovery route supplied. It stopped at the one step
  both attempts had named as missing.
- **Train #997:** discovery produced two refereed complete proofs resting on a published theorem. The harness
  certified 3 hypotheses and was left with one "bridge" lemma. It stopped at `--research-cycles 2` with $4
  unspent, still productive.
- **v1 mechanics on dev (#392):** one attempt overran its $1.20 cap, the survivor alone was not "unanimous", and
  the budget went back to a 50/50 split.
- **v2 smoke test on train #1148:** medium-effort attempts returned for $0.31 and $0.71. A high-effort attempt on
  the missing step overran even $1.50 and returned nothing: a capped call keeps no partial output.

**What changes from v1.**
1. First round: 2 attempts at **medium** effort, $0.80 cap each.
2. **One confident answer (≥ 0.75) may commit** when the other attempt produced nothing. Disagreement still never
   commits.
3. **A second round on the named missing step**, one attempt at medium effort ($1.20 cap) plus a referee pass.
   Its proof or partial result goes into the guidance.
4. **`--research-cycles 6`:** the budget and the stall rule (2 cycles with no discharge) decide when to stop, not
   a fixed cap of 2.

Same pinned harness, knowledge and **$8 total**. This bundles three changes, so a gain here needs ablation before
it is attributed.

**Write-ahead predictions:**
- dev: an expected 1.5 solved (range 0–4).
- P(v2 solves strictly more dev items than the baseline): 0.50. P(an evident gain, ≥ 3 discordant for and none
  against): 0.20.
- Items with the true direction closed modulo published premises only: 1–3.
- The second round proves its missing step, and the referee accepts it, on about 3 of 18 items.

**Outcome.** To be filled in when the lane finishes.

## Dense progress metric, 2026-09-24 (operator's choice: gate iterations on certified progress)

**Why.** Three arms and 21 dev runs at $8 solved nothing. A solve-only gate cannot separate candidates at this
budget. The operator chose to gate each iteration on how much of the TRUE direction's proof gets certified, with a
guard against trivial lemmas, and to keep full solves as the final check. README "Scoring" has the definition
(measurement version 3): `pieces`, `certified_size`, and the paired call that needs both.

**Validation before anything was compared.**
- 9 new unit tests (47 in `tests/test_timesplit.py`).
- On all 25 distinct runs measured (26 records; the top-up shares v2 #150's run directory), the structural pass
  agreed with the harness's own certified count (none stale).
- One resolver miss was found and fixed before any measurement was kept: a glue can call a spliced proof copy
  directly (`exact h_ns.h n a hn`), which made baseline #204's and #729's lemmas look unused.
- Lean pass: every context block compiled, and every cascade block failed genuinely. Checked by hand on v2 #150
  and baseline #419.

**What each guard did on these runs.** The harness counts 45 certified hypotheses, and 39 pieces remain.
- *used* removed 3: baseline #419 had 3 of its 4 orphaned by a re-plan.
- *closed* removed 1: a refinement parent over open sub-hypotheses (v1 #202).
- *maximal* collapsed 2: v2 #150's upper bound is one piece resting on two certified sub-lemmas.
- *non-trivial* removed **0**: no certified hypothesis in any run is closable by the free cascade on its own. The
  failure mode the operator asked to guard against does not occur here. The guards that bite are the structural
  ones.

**One change after first use, before any gate bound.** The first key was `(solved, pieces)`. On first use its
calls visibly depended on how a plan chunked the argument. On #392, the baseline's 3 pieces and v2's 1 piece both
leave a single hypothesis, named `hyp_upper` in both runs, open. The call was therefore changed to need more
pieces AND more certified size (version 2), before any candidate was gated on it. On these five items the calls
did not change, because the two measures agree in direction on every one.

**A second fix, from a measurement that failed.** v2 #419's certified statements would not elaborate in isolation
(`Unknown constant Real.logb`). The harness had added that module mid-run for an unknown identifier, and the check
used only the problem file's imports. Triviality is now checked under full `import Mathlib` (version 3). Every
measurement was redone, and every one matched version 2 except #419, which went from 5 pieces judged "unknown"
to 5 judged non-trivial.

**Pre-registration caveat.** The gate rule was written after the structural counts of these runs had been seen.
The comparisons below are therefore descriptive. The gate binds from the next candidate on.

**Descriptive results.** Pieces / certified size / open conjectures in the true direction, on the five dev items
all three arms ran:

| item | baseline v2 | discover-v1 | discover-v2 |
|---|---|---|---|
| #150 | 0 / 0 / 2 | 1 / 2025 / 3 | **1 / 11778 / 1** |
| #202 | **2 / 1305 / 0** (+2 published) | 1 / 1036 / 3 | 1 / 713 / 2 |
| #204 | **3 / 3073 / 7** | 2 / 2910 / 3 | 2 / 2573 / 4 |
| #392 | **3 / 4384 / 1** | 1 / 593 / 4 | 1 / 1979 / 1 |
| #401 | 2 / 855 / 1 | 2 / 3131 / 1 | 2 / 1438 / 1 |
| spend | $20.56 | $34.06 | $36.60 |

- Against the baseline, v1 and v2 each score **1 win (#150), 3 losses (#202, #204, #392), 1 tie**. The one-sided
  p is 0.94 for both.
- Certified size: v1 +78 characters in total, v2 +8,864, almost all from #150.
- Spend: v1 +$13.50 and v2 +$16.04 over the five items.
- The baseline's other six items give 4 pieces for $35.36.
- Train diagnostics, for reference: #152 has 2 pieces (12,347 characters); #997 has 3 pieces (6,933).
- **v2 on nine items (through #570), measured by hand because its lane started before the metric existed:**
  - record against the baseline: 3 wins (#150, #419, #570), 4 losses, 2 ties, one-sided p = 0.77;
  - +$21.34 of spend.
  - **Head to head with v1** on their 5 shared items, every item ties under the gate rule (equal pieces on each).
    v2 certified 18,481 characters against 9,695, left 9 hypotheses open against 14, and spent $36.60 against
    $34.06.
  - **Correction (2026-09-25):** baseline #537's record lost BOTH directions to a usage limit and kept a $2.00
    partial as its result. The runner did not detect a direction lost under `--open` and has been fixed
    (`lost_directions`); such records are now left out of paired comparisons. Over the 8 valid pairs, v2 against the
    baseline is **3 wins, 3 losses, 2 ties** (one-sided p = 0.66).
  - On #537 it committed to the WRONG direction: discovery called the statement true, and the answer is no. The
    true direction was never attempted, so the item scores 0 pieces, against the baseline's 1. This is v2's first
    wrong commit, and v1's write-ahead expected 1 or 2 such items. It is not caused by v2's looser rule. Both
    attempts said "true", at confidence 0.5 and 0.6, and v1's unanimity rule commits on the same attempts.
  - Its wins are large and its losses small. On #419 it has 5 pieces (10,274 characters) with one hypothesis
    open, against the baseline's 1 piece (822) with three open. A sign test ignores magnitude, and this is why.

**Reading.** On certified progress, front-loading informal discovery and committing to one direction is mixed,
not a gain.
- When it works, it works big. On #150 and #419 it certified the large step the baseline never reached, and left
  one hypothesis open.
- Otherwise it certifies a little less than the baseline, at about $2.50 more per item.
- The baseline stopped every direction at the 2-cycle cap, with $2-6 unspent on 7 of 11 items, so it got its
  pieces cheaply.

On the 5-item screen, v2 lost 1-3, and README's screen rule says to run the rest of dev only if a candidate does
not lose. It is still running because it was launched before the rule existed. Whether to pause it is the
operator's call.

**Found in passing.** The harness's free cascade stops at the first alternative that makes progress (CLAUDE.md,
"The harness's own cascade stops early"). A free replay of the harness's saved cascade passes, outside dev and
test, measures what the guarded form would close. Results are below.

### Cascade replay, 2026-09-24: the harness's first free pass is a no-op

`analysis/cascade_replay.py` recompiles the harness's own saved cascade passes (`attempts/cascade.lean`, the last
pass kept in each directory). It uses only the 42 passes outside time-split dev and test: train runs, plus the
other session's masked and research runs, 38 runs in all. Each pass is compiled four ways:
- with every hole back to `sorry`;
- exactly as saved;
- with the harness's cascade followed by `<;> done`, so a leftover goal errs on the hole's own line;
- with the guarded cascade.

Lean only, no model calls. One pass timed out, which leaves 41.

| | holes |
|---|---|
| in the 41 passes (every attempt compiles apart from its `sorry`s) | 71 |
| the harness **believed** it closed (no error on the hole's line) | **71** |
| its cascade **actually** closes | **0** |
| the guarded cascade closes | **3** (one pass) |

- Every one of the 41 passes contained a false closure. So the harness's keep-check failed every time and
  reverted the whole pass: realised closures, 0.
- No genuine closure was lost to those reverts, because there were none to lose.
- Across every log on disk, the harness recorded a cascade closure 4 times.

**Why.** An unguarded `simp_all`, `norm_num` or `aesop` that only simplifies ends `first` successfully with the goal
still open. Lean then reports "unsolved goals" at the enclosing `by`, one line above the hole, so line attribution
reads the hole as closed. With every alternative guarded, `first` either closes the goal or fails on the hole's
line, which fixes both the early stop and the misreading.

**Candidate** `pin_3aaab15508852d05_harness.py` is the 84f21c5 pin plus this one-line change
([`pins/cascade-guard.patch`](pins/cascade-guard.patch)). Measured offline, it gains 3 free closures in 71 holes
and saves one wasted compile, the keep-check, per pass. That is a correctness fix of small measured effect, and
too small for a $8-per-item dev run to detect.

**Applied upstream, 2026-09-24, at the operator's request.** The live `harness.py` now carries the guarded
`CASCADE`, with `tests/test_cascade_guard.py`. Under real Lean, the old string reads one hole as closed and reverts
the other, genuine, closure; the new one closes both. The evaluations above ran on pins that keep the old string,
so their comparisons are unaffected. A future arm pinned from the live harness differs from them in the cascade,
among other things.

## Commit-rule calibration on train, 2026-09-24: `calibration-train-v2r1` (operator's request)

**Why.** On dev #537 both of v2's first-round attempts said "true", at confidence 0.5 and 0.6. The answer is no.
Both commit rules act on unanimity alone, so the run was lost to the wrong direction. The question is whether
the confidence the attempts report can say when a unanimous answer is safe to commit to. Dev may not be used to
tune that (quarantine), so the calibration runs on train.

**Protocol.**
- `timesplit.py calibrate --tag train-v2r1 --rounds 3`: v2's first round alone. That is 2 parallel attempts at
  medium effort, each capped at $0.80, plus a $0.30 referee pass on any attempt that claims a complete proof.
- **3 independent rounds on each of the 15 train items** (9 true, 6 false), with no harness run.
- For each round it records every attempt's answer, confidence, completeness and referee verdict, and what the v1
  and v2 rules would commit to.
- `calibrate --report` gives the commit rate and wrong-commit rate at mean-confidence floors 0.5-0.9.
- Estimated cost: about $20, from v2's measured first-round mean of $0.44 per item.

**Decision rule, written before launch.** Adopt the smallest floor at which the observed wrong-commit rate among
v2-rule commits is at most 1 in 20, with at least 40% of rounds still committing. If no floor qualifies, reported
confidence does not separate right answers from wrong ones. The recommendation would then be to stop committing on
unanimity alone, and to commit only on a refereed complete proof.

**Write-ahead predictions.**
- Attempt accuracy: 0.80. The build probe, which had the full identity as a cue, guessed 26 of 31 right.
- Unanimous rounds: about 80%.
- v1-rule commits: about 75% of rounds, of which about 12% are wrong.
- Confidence discriminates weakly: wrong-commit rate about 0.25 below a mean confidence of 0.7, about 0.08 above.
- P(some floor qualifies under the rule above): 0.35.
- Agreement across an item's three rounds separates right from wrong better than reported confidence does: 0.5.

**Outcome (45 rounds, $28.88): the floor is 0.6.**

| mean-confidence floor | commit rate | wrong commits |
|---|---|---|
| none (the v1 and v2 rules) | 96% | 7 of 43 (16%) |
| 0.5 | 93% | 6 of 42 |
| **0.6** | **73%** | **0 of 33** (Jeffreys 90% upper bound 5.7%) |
| 0.7 | 60% | 0 of 27 |
| 0.8 | 49% | 0 of 22 |

- **The wrong commits.** All 7 were FALSE statements called true: 4 items (#387, #619, #884, #990), every one below
  a mean confidence of 0.6. The model called 13 of the 15 items true; 9 are.
- **Against the predictions.**
  - Attempt accuracy was 0.80, as predicted.
  - Commits ran at 96% of rounds, against a predicted 75%, and 16% of them were wrong, against 12%.
  - Confidence discriminated far more sharply than predicted: 7 of 10 commits below 0.6 were wrong, and 0 of 33 at
    or above.
  - A floor qualified (predicted P = 0.35).
  - Agreement across rounds was useless (predicted P = 0.5 that it would beat confidence). Three items got the
    same wrong answer in all three rounds.
- **Adopted as `--commit-floor 0.6`** for future discover arms. It is not applied to the running discover-v2 arm,
  whose protocol is fixed. On dev #537 (both attempts "true", at 0.5 and 0.6, answer no), the floor would have
  withheld the commitment.
- **Caveat.** 15 items; the rounds within an item are correlated.

## Smoke run of candidate v3 on train #152, 2026-09-25: `train-v3-smoke`

**Purpose.** An end-to-end check of the discovery build on one train item. It is not an evaluation.
- Live harness, with every fix of 2026-09-24 and the `v3` flags (`V3_FLAGS`): exploration and core exploration,
  empirical conjectures, two routes, core-first attack, high-effort plans, the wide literature memo, two-cycle
  sub-residuals.
- $8 for both directions, 6 research cycles.
- The train diagnostic under discover-v1 got 2 pieces on this item, and an idea-hit grade of **partial**.

**Write-ahead predictions.**
- The exploration stage runs and leaves a notebook with conjectures: 0.9.
- The notebook states quadratic growth of isolated sums (≫ n²) as a conjecture: 0.5.
- Idea-hit grade: hit 0.25, partial 0.55, miss 0.2.
- Solved: 0.05.
- At least 2 pieces in the true direction: 0.5.
- An exploration session costs under $1.50 once MCP connectors are off: 0.8.

**Outcome (2026-09-25): not solved, $8.22, 0 pieces. The run exposed a live-harness bug.**
- **Exploration worked** ($1.25, 37 turns, 12 scripts). Its verdict: TRUE at 0.85, "the data suggests f(n) ≍ n²",
  which is the published growth rate. Idea grade: **partial**, as for discover-v1. The notebook has the right double
  count for k = 1 but not the published k = 1, 2, 3 argument.
- **Every hypothesis attack was rejected before a proof was tried**, with `failed to synthesize instance
  HAdd (Set ℕ) (Set ℕ)`. The live harness still built sub-statements from definitions alone and dropped `open scoped
  Pointwise`. `fix-opens.patch` had fixed that in the baseline's pin on 2026-09-24, but was never upstreamed. It is
  now (`skeleton_context` in `harness.py`, with a test). The extracted hypothesis compiles in Lean.
- **Spend:** plans $4.19 (high effort, two routes), experiments $2.24, exploration $1.25, and $0.00 on proving. The
  remaining hypotheses were deferred against the $2.50 minimum per child. At $8 an item, v3's plan settings leave
  nothing for proofs.
- **What worked:** the plan repair fixed a noncomputable definition in one round, the route judge chose on a stated
  identity, and the negation direction called its false target false and stopped.
- **Predictions:** notebook with conjectures yes (0.9); n² conjecture yes (0.5); idea grade partial (0.55); not
  solved (0.95); at least 2 pieces no (0.5); session under $1.50 yes (0.8).

## Improvement loop, iteration 1 (seeded 2026-09-25): does exploration find the key idea?

**Question.** Does a tool-using exploration session find the published key idea more often than tool-less discovery
does? The exploration is `--explore`, a Python sandbox; the tool-less discovery is v2's first round. This is the
cheapest test of the claim behind v3, and it needs no Lean.

**Protocol.**
- **Tool-less arm:** round 0 of `calibration-train-v2r1`, graded by the idea judge:
  `ideas --tag calib-ideas --from-calibration train-v2r1`. About $1.20.
- **Exploration arm:** `explore-screen --tag explore-train-1` on the train items. That is the literature memo and
  one $1.50 exploration session per item, at medium effort, with the wide memo and the live harness. Then `ideas`.
  About $25 for 14 items. #152 comes from the v3 smoke run, which launched before the loop and is not counted.
- **Paired call per item** on the grade: hit > partial > miss.
- #1179 is graded "route unknown" and skipped wherever its note says so.

**Gate, written before launch.** Proceed to the dev screen only if exploration wins at least 3 more items than it
loses (W − L ≥ 3). The dev screen is 5 items, with v3 and a baseline both on a new pin of the live harness, about
$80. Otherwise the exploration stage needs work first: that is iteration 2.

**Write-ahead predictions.**
- Tool-less discovery: 4 hits, 5 partials, 6 misses.
- Exploration: 5 hits, 6 partials, 4 misses.
- P(W − L ≥ 3) = 0.35.
- An exploration session costs $1.00-1.60 and writes a notebook in at least 12 of 14 runs.

**Outcome (2026-09-25): the gate fails. W − L = −2 (1 win, 3 losses, 11 ties over 15 items).**

| arm | hit | partial | miss | spend |
|---|---|---|---|---|
| tool-less discovery (calibration round 0) | 7 | 8 | 0 | $0.64 (judge only) |
| exploration (explore-train-1, plus #152 from the smoke run) | 5 | 10 | 0 | $9.96 + $0.91 judge |

- **Paired:** exploration wins #990 (it built the published Vandermonde counterexample family). It loses #259, #678
  and #1037, where tool-less attempts recalled the published route and the exploration sessions stopped after 1-3
  scripts on a weaker recollection. The other 11 are ties.
- **Directions:** exploration named the right one on 12 of 14. It was right on false statements where tool-less
  discovery had been wrong: #884 (wrong in all three calibration rounds) and #990.
- **Sessions were short:** a median of 3 scripts at $0.71, far under the $1.50 cap. On most items the model
  concluded from recall rather than exploring.
- **Against the predictions:** tool-less discovery 7/8/0 (predicted 4/5/6); exploration 5/10/0 (predicted 5/6/4);
  P(W − L ≥ 3) was 0.35 and it did not happen; cost $0.33-1.27 a session (predicted $1.00-1.60); a notebook in all
  14 runs (predicted at least 12).
- **Decision:** exploration at $1.50 and medium effort does not beat tool-less discovery at finding the key idea on
  train. `--explore` stays off by default. Its one clear value here was finding constructions and counterexamples,
  and that is the lead to keep.

## Improvement loop, iteration 2 (2026-09-25): does the fixed harness convert known ideas?

**Why.** On half the train items tool-less discovery already reaches the published key idea, and the harness has
never converted one. The diagnosis points at conversion: 61 deferrals for budget, and 33 runs stopped on budget. Of
the fixes of 2026-09-24/25 (cascade, sub-statement opens, plan repair, hoisting, over-cap recovery, no connectors),
none has been measured on a full run.

**Protocol.**
- Candidate `baseline` on the live harness: every fix, no discovery flags. `--open`, $8 an item, 6 research cycles.
- Items: train #283, #435, #997 and #1141, the four whose key idea both arms found.
- Tag `train-fixes-conv`. About $32. Train, so failures can be read.

**How the result is used, written before launch.**
- If at least one item is solved, or closed apart from published premises, run the fixed baseline on the 5-item dev
  screen, pinned, against `baseline-v2-84f21c5`.
- If none is, read these train transcripts for the conversion blocker; iteration 3 targets it.

**Write-ahead predictions.**
- P(at least one of the 4 solved) = 0.30.
- P(at least one closed apart from published premises) = 0.50.
- Mean pieces in the true direction at least 2: 0.5.
- The hardest hypothesis gets at least one child attack on every item: 0.7.
- No sub-statement is rejected for a lost `open`: 0.9.
- About $8 an item.

**Interim (2026-09-25).**
- #283: 1 piece. Allocation starved it: proving got 13% of the spend, and the core was deferred every cycle.
- #435: its true direction died on the usage limit, so it is not a result and will be rerun in place.
- **#997: closed apart from ONE published premise** (Banks–Freiberg–Turnage-Butterbaugh 2015), with 3 pieces and 0
  open conjectures. **The decision rule is met.** #1141 and the #435 rerun complete the iteration.

### Iteration 2, next step: dev screen of the fixed harness, `dev-fixes-ea6d987`

**Candidate.**
- `pin_ea6d9878462aac38_harness.py` (every fix up to 2026-09-25, including `skeleton_context`, the plan repair,
  hoisting, the guarded cascade, over-cap recovery and no MCP connectors).
- The baseline protocol (`--open`, no discovery flags), $8, **6 research cycles**. The comparison arm,
  `baseline-v2-84f21c5`, ran 2, so this is a bundle of the fixes and the cycle count; attribute any gain to the
  bundle only.
- Items: the first 5 dev items (#150, #202, #204, #392, #401), paired with `baseline-v2-84f21c5`.

**Gate, written before launch.**
- If the screen does not lose on the dense rule (W ≥ L) and loses no solve, extend to the baseline's other valid
  items (#419, #457, #570, #618, #729). #537 is excluded: its baseline record lost both directions.
- On the 10 pairs, keep the fixed harness as the new baseline if it loses no solve and either solves more, or wins
  the dense sign test at one-sided p ≤ 0.05.

**Write-ahead predictions.**
- P(at least one solve among the 5) = 0.12.
- P(at least one true direction closed apart from published premises) = 0.35.
- Dense calls on the 5: 3 wins, 1 loss, 1 tie expected; P(W ≥ L) = 0.7.
- $40.
