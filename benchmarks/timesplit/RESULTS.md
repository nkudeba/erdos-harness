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

**Outcome (lane done 2026-09-25 ~09:00Z; recorded 2026-09-25 17:30Z by the loop, from aggregate numbers only).**
- **1 of 18 dev items solved: #1213**, its TRUE direction verified, for $2.64. See "Stop signal: dev #1213" below.
- $124.38 on the 18 results, plus $5.85 on infrastructure launches. 0 contradictions.
- Discovery committed on 17 of 18 items, 15 of them to the true direction. 2 wrong commits spent their whole budget
  on a false statement.
- No true direction closed apart from published premises (predicted 1–3). The second round proved its missing step
  on 1 item (predicted about 3).
- **Against the predictions:** 1 solved (expected 1.5, range 0–4). Whether v2 solves more than the baseline is
  still undecided: the baseline was paused before it reached #1213 (see "Baseline v2 paused"). The run that settles
  it is pre-registered below.

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

**Train outcome (all 4 items, $37.29 including the infrastructure launches).**

| item | true direction | pieces | open | closed apart from published premises |
|---|---|---|---|---|
| #283 | pos | 1 | 2 | no |
| #435 (rerun in place) | pos | 1 | 2 | no |
| #997 | pos | 3 | 0 | **yes** (BFT15) |
| #1141 | neg | 2 | 1 | no |

- **Against the predictions:** no solves (P ≥ 1 was 0.30); one item closed apart from published premises (0.50);
  mean pieces 1.75 (predicted at least 2, 0.5); sub-statements lost to a missing `open`: **0** (0.9); about $8 an
  item.
- **The core was NOT attacked on every item** (0.7). On 3 of 4, hypotheses including the cores were deferred for
  budget and never attacked: #283's `hyp_core`, `hyp_constant` and `hyp_egypt`; #435's `hyp_lower` and `hyp_window`;
  #1141's `mod6`. #997, the one closed, attacked everything.
- **Blocker for iteration 3: allocation.** On #283, proving got 13% of the spend. The refutation script reran every
  cycle in both directions (39%), and the false direction spent as much as the true one.

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

**Budget amendment, written 2026-09-25 while the screen was running and before any of its outcomes were read.**
- The extension to 5 more dev items is dropped. $109 is free, and iteration 3 (`alloc`: about $34 train, plus about
  $40 on dev) targets the blocker the evidence names, while the extension would only sharpen the estimate for fixes
  that are already on by default as correctness fixes.
- The screen's dense comparison is reported as it stands.
- `dev-fixes-ea6d987` becomes the baseline for iteration 3's dev screen: same 5 items, and pins that differ only by
  iteration 3's default-off options.

**Outcome (2026-09-25): the fixed harness LOSES the screen. 0 wins, 2 losses (#202, #401), 3 ties. $34.21, against
$20.56 for `baseline-v2-84f21c5`.**

| item | fixed (pieces / size / open) | old baseline (pieces / size / open) |
|---|---|---|
| #150 | 0 / 0 / 2 | 0 / 0 / 2 |
| #202 | 1 / 527 / 1 | 2 / 1305 / 0 |
| #204 | 3 / 2885 / 1 | 3 / 3073 / 7 |
| #392 | 3 / 3135 / 1 | 3 / 4384 / 1 |
| #401 | 0 / 0 / 1 | 2 / 855 / 1 |

- **Why, from aggregate counts only** (spend by stage and direction, event counts; no dev transcript was read):
  - #202: the FALSE direction took 62% of the fixed run's spend ($3.25 of $5.27), and the true direction's proving
    got $0.18. Six cycles let a direction that never judged its target false keep spending.
  - #401: the true direction spent $2.77 on proving, one failed attack at a hard piece, where the old run's plan
    had chosen two lemmas it could discharge for $0.27. That difference is between plans, not between harnesses.
  - Certified work was not being orphaned by re-plans: every discharged hypothesis survives in the final residual,
    in both arms.
- **Reading:** single runs vary a lot from plan to plan; 0-2-3 over 5 is within noise (two-sided p = 0.5). The fixes
  are correctness fixes and stay on. The more cycles bought, the more spending in the false direction. That is the
  cost `alloc`'s commit-when-confident step targets.
- **Predictions:** no solves (P ≥ 1 was 0.12); none closed apart from published premises (0.35); W ≥ L did not hold
  (0.7). The prediction was wrong in direction.

## Improvement loop, iteration 3 (written 2026-09-25, launches after the dev screen): `alloc`, budget follows the core

**Why.** Iteration 2 found the conversion blocker to be allocation. On 3 of 4 train items, hypotheses including the
cores were deferred for budget and never attacked. On #283 proving got 13% of the spend, the refutation script 39%
(rerun every cycle in both directions), and the false direction spent as much as the true one. On #997 the last budget
went on a published premise at the level of Maynard–Tao.

**Candidate `alloc`,** declared as one bundle aimed at one blocker:
1. Discovery's first round, v2's settings (2 attempts at medium effort, $0.80 cap), with the train-calibrated commit
   floor of 0.6. It commits to one direction only when confident; otherwise the run is `--open` as before.
2. `--attack-order core-first`: the hardest open conjecture is attacked first, with half of what is left.
3. `--refute changed`: the refutation script reruns only when the open hypotheses changed.
4. `--premise-attack cheap`: a published premise gets only the free tactics, never a full child.

It runs on a new pin taken after the harness change lands, with the fixed harness otherwise unchanged: $8, 6
research cycles.

**Screen:** the same 4 train items as iteration 2 (#283, #435, #997, #1141), paired with `train-fixes-conv`. About
$34, including discovery.

**Gate, written before launch.** Go to a dev screen, paired with `dev-fixes-ea6d987` on the same 5 items, if both
hold:
- the core is attacked (a child run on the hardest open conjecture) on at least 3 of the 4 items;
- the total true-direction pieces are at least iteration 2's 7, or a new item is solved or closed apart from
  published premises.

Otherwise the allocation change is rejected, and the notes say why.

**Write-ahead predictions.**
- Discovery commits on 3 of 4 items: #1141 (false) with a weaker belief; #283, #435 and #997 at confidence ≥ 0.6.
  All commits are correct: 0.8.
- The core is attacked on at least 3 of 4: 0.75.
- Pieces at least 7: 0.55.
- At least one item solved: 0.2.
- At least one new item closed apart from published premises: 0.35.

**Outcome (2026-09-25): rejected. True-direction pieces 2 against iteration 2's 7; no item newly solved or closed.
$27.30.**

| item | iteration 2 (pieces / open) | `alloc` (pieces / open) | $ (iteration 2 → `alloc`) |
|---|---|---|---|
| #283 | 1 / 2 | 1 / 2 | 5.89 → 8.06 |
| #435 | 1 / 2 | 0 / 2 | 8.01 → 9.66 |
| #997 | 3 / 0, apart from BFT15 | 1 / 0, apart from BFT15 | 8.26 → 2.32 |
| #1141 | 2 / 1 | 0 / 2 | 8.03 → 7.26 |

- **Gate:** the core was reached on 4 of 4, but the pieces fell short, and #997's closure was not new. So the gate
  failed.
- **Predictions:**
  - Discovery committed on 4 of 4, all correctly (predicted 3, with #1141 weaker).
  - Core reached on at least 3: yes (0.75).
  - Pieces at least 7: no (0.55).
  - A solve: no (0.2).
  - A new closure: no (0.35).
- **Reading:**
  - The commit rule, `--refute changed` and `--premise-attack cheap` saved money at no measurable cost.
  - Core-first lost the pieces. All four cores got half a budget, were split and not cracked, and the easy pieces
    iteration 2 banked were then deferred for lack of budget.
  - Two of the cores are deep published analytic results (BFT15; Burgess plus Siegel) that no budget here can
    formalize.
- **New harness finding:** on #1141, two re-plans reduced the open count by dropping the one certified lemma.
  `residual_improves` does not weigh certified work.
- Details: `loop/iterations/3.md`.

## Stop signal: dev #1213 solved by `discover-v2-84f21c5` (found by the loop 2026-09-25 17:15Z)

**What happened.**
- The operator's discover-v2 dev lane (pin `84f21c5`, $8, 6 cycles, candidate `discover-v2`) solved dev #1213.
  - The run started at 08:36:57Z, took 22 minutes and cost $2.64, including $0.36 for discovery.
  - Discovery committed to TRUE with weight share 1.0. One of its two attempts claimed a complete proof, at
    confidence 0.93.
  - The harness closed the residual: 4 hypotheses certified, 0 open, 0 published premises.
- **Found 8 hours late.** The loop scored only its own tags and never read the operator's results file, so stopping
  condition 1 was never checked mechanically. `loop.py status` now lists every solve or contradiction in any
  results file until it is acknowledged (`loop.py ack`).

**Independent re-check (no model calls).** The transcripts were not read. Of the proof, the loop saw only its
declaration names (`hyp_long`, `hyp_sumbound`, `hyp_count`, `hyp_pigeon`), while locating the main theorem.
- `runs/20260925-043526-696629-timesplit-erdos82251/final/Erdos82251.lean` compiles in `formal/` under
  `lake env lean`, with no errors and no warnings. It contains no `sorry`.
- `#print axioms erdos_82251` gives `[propext, Classical.choice, Quot.sound]`.
- The frozen theorem's signature appears verbatim in the file.
- The run's frozen statement equals `masks/1213.json`'s `statement_lean`, up to the theorem's alias name. That is
  formal-conjectures@077138338750's `ErdosProblems/1213.lean` main theorem with `answer(True)` stripped.
- The harness's own final verification agrees: compiles, sorry-free, standard axioms, frozen match. The
  faithfulness judge passed the statement.
- Item facts: dev, probe `unaware`, first public 2026-04-21, answer True from formal-conjectures' `answer(...)`.

**What it is and is not.**
- It is a **mechanically verified** proof of the frozen statement, `claimEligible=false`.
- It re-derives a result published on 2026-04-21, by a model that, asked directly, does not know the result.
  That is evidence about the harness, not new mathematics.
- The faithfulness judge added one caution: the route it was shown called the general-K case "likely open", so a
  claimed proof should be checked closely. That concerns provability, not faithfulness, and Lean has settled
  provability of the frozen statement. A human should still read the proof against the English statement.

### Replication, written before launch: `replicate-1213-84f21c5`

**Protocol.**
- Same pin, knowledge and settings as the solving lane, on a fresh alias (a new tag):
  `--candidate discover-v2 --discover-attempts 2 --discover-budget 0.8 --discover-effort medium --gap-budget 1.2
  --gap-effort medium --budget 8 --research-cycles 6`.
- One difference cannot be removed. The runner is today's `timesplit.py`. The lane ran the copy loaded when it
  started (2026-09-24 12:12 EDT), and that copy was never committed. The v2 path's options are unchanged, and the
  options added since (commit floor, `alloc`, `v3`) are off for v2.
- It launches when the in-flight alloc item (#1141) finishes, keeping one loop lane at a time. About $8 is
  reserved.

**Write-ahead.**
- P(the TRUE direction verifies again) = 0.6.
- If it does, it most likely costs under $4.

**Rule.**
- If it verifies, stopping condition 1 is met. The loop records the evidence, notifies the operator, and stops.
- If it does not, the solve stands as verified but unreplicated, and the loop continues. The operator is told
  either way.

**Outcome (2026-09-25 18:57Z): REPLICATED.** The TRUE direction verified again on the fresh alias 59388.
- $3.92, including $0.32 for discovery. 37 minutes. 3 hypotheses certified, 0 open, 0 published premises.
- Discovery again committed to TRUE at share 1.0.
- The run: `runs/20260925-141600-634401-timesplit-erdos59388`.
- **Independent re-check (no model calls; the proof was not read):**
  - `final/Erdos59388.lean` compiles in `formal/`.
  - It contains no `sorry` and no `native_decide`.
  - `#print axioms erdos_59388` gives `[propext, Classical.choice, Quot.sound]`.
  - The frozen statement equals `masks/1213.json`'s `statement_lean`, and its definition and theorem signature
    appear verbatim.
  - The same checks now also cover the original run's definitions: verbatim, with no `native_decide`.
- **Predictions:** P(verifies) was 0.6; it verified. "Most likely under $4": $3.92.
- **Stopping condition 1 is met:** a dev item's TRUE direction is verified and has been replicated once on a fresh
  alias.
- **Attribution, stated plainly.** The solve came from `discover-v2`, the candidate built with the operator on
  2026-09-24 before the loop started, on pin `84f21c5`. None of the loop's three iterations produced it. Iteration
  1 (exploration), iteration 2 (the fixed harness) and iteration 3 (`alloc`) were all rejected. What the loop
  contributed here was the check that found the solve, and the replication.
- **Not recorded in the Atlas, by design.** A dev item's route written where the harness reads would carry its
  solution into every later evaluation. `claimEligible` stays false; the proofs await human review.

### Baseline on #1213, written before launch: `baseline-v2-84f21c5-1213`

- **Why:** "Baseline v2 paused" requires it before any verdict: a v2 win counts only against the baseline's own run
  on the same item. The baseline never reached #1213.
- **Protocol:** baseline v2 exactly, as its protocol record gives it: pin `84f21c5`, `--open`, no discovery, $8,
  2 research cycles. It runs after the replication, in the same lane.
- **Write-ahead:** P(the baseline solves #1213) = 0.4. A solve would mean discovery was not needed for this item.

**Outcome (2026-09-25 19:45Z): the baseline does NOT solve #1213.**
- $7.48 under `--open`. The true direction certified 1 hypothesis and left 1 open.
- The false direction's plan judged its target false and stopped (`target_believed_false`).
- Run: `runs/20260925-145711-117917-timesplit-erdos94894`.
- **Reading:** on this item, the discovery stage is what made the difference. With discovery, 2 of 2 runs solved
  it, at $2.64 and $3.92. Without it, the one baseline run left the true direction one hypothesis short at $7.48.
  One pair is not a rate.
- **The v2 verdict so far:** v2 solved 1 item and the baseline 0, with #1213 now paired. That is one discordant pair
  for v2, short of the pre-registered "evident gain" (≥ 3 discordant for, none against). The baseline still has not
  run 6 of v2's items (#825, #865, #871, #888, #1125, #1180), so a solve only the baseline would find is not ruled
  out there.

## The improvement loop stops (2026-09-25 19:50Z): stopping condition 1

- **Goal met:** a dev item's TRUE direction is verified in Lean (#1213) and replicated once on a fresh alias. Both
  proofs pass the loop's own mechanical re-check. Human review is pending, and `claimEligible` stays false.
- **The loop's spend:** $121.71 of the $200 cap, and $78.29 is left unspent. This session's own model use is not
  counted, as the protocol says.
- **Its iterations:**
  - Iteration 1 (exploration): rejected.
  - Iteration 2 (the fixed harness): lost its dev screen, W0 L2 T3.
  - Iteration 3 (`alloc`): rejected, 2 pieces against 7.
  - None of them produced the solve. It came from `discover-v2` (2026-09-24, before the loop), and the loop
    found it, checked it and replicated it.
- **What the loop learned that outlives it:**
  - Discovery that yields a complete, refereed informal proof is what converts. The solved item is the one where
    discovery wrote the whole argument, and the baseline without it fell one hypothesis short.
  - At $8, budget allocation cannot buy a deep core. Two of iteration 3's four cores are published analytic results
    no budget here could formalize.
  - Two instrument lessons:
    - The pieces rule scores a cheaper route to the same end state as a loss (#997).
    - A stop check must read every results file, the operator's lanes included.
  - One harness finding: `residual_improves` lets a re-plan drop a certified lemma to lower the open count (#1141).
- **For the operator:**
  - Review the two proofs:
    - `runs/20260925-043526-696629-timesplit-erdos82251/final/Erdos82251.lean`
    - `runs/20260925-141600-634401-timesplit-erdos59388/final/Erdos59388.lean`
  - Decide whether to merge branch `harness-loop`.
  - Decide whether to finish the baseline on v2's 6 unpaired dev items.

## Baseline v2 on discover-v2's 6 unpaired dev items (operator's request, 2026-09-26), written before launch

- **Items:** #825, #865, #871, #888, #1125 and #1180, the dev items baseline v2 never reached. The run appends to
  `baseline-v2-84f21c5` (the resume command in "Baseline v2 paused"), so `score --tag discover-v2-84f21c5 --baseline
  baseline-v2-84f21c5` pairs 17 of 18 items. #1213's pair is in `baseline-v2-84f21c5-1213`.
- **Protocol:** unchanged: pin `84f21c5`, `--open`, no discovery, $8, 2 research cycles.
- **Write-ahead:**
  - P(the baseline solves at least one of the 6) = 0.12. discover-v2 solved none of them and got 0–2 pieces each.
  - About $35 in total.

**Outcome (2026-09-26): none solved, $38.74.**

| item | spend | notes |
|---|---|---|
| #825 | $5.79 | |
| #865 | $8.18 | |
| #871 | $9.91 | $1.91 over its $8 cap: parallel agentic sessions check the cap only between turns, a known limit |
| #888 | $4.21 | the false direction stopped as believed false |
| #1125 | $8.80 | the false direction stopped as believed false |
| #1180 | $1.85 | the false direction stopped as believed false |

No record is infrastructure, and no record lost a direction.

**The discover-v2 verdict, with every dev item now paired** (17 in `baseline-v2-84f21c5`, and #1213 in
`baseline-v2-84f21c5-1213`):
- **Solves:** discover-v2 1 (#1213), baseline 0. One discordant pair for v2 and none against, short of the
  pre-registered "evident gain" (≥ 3 for, none against). McNemar p = 1.0 on 17 pairs, so nothing is significant.
- **Dense (15 measured pairs):** v2 wins 6, loses 4, ties 5; one-sided sign test p = 0.38.
- **Spend:** v2 spent $27.08 more on the 17 pairs.
- **Against its predictions:**
  - 1 solved (expected 1.5, range 0–4);
  - "v2 solves strictly more than the baseline" held (0.50);
  - no evident gain (0.20).
- **Reading:**
  - The one solve anywhere on dev in 37 runs belongs to v2. On #1213 the discovery stage is what made the difference,
    and the baseline fell one step short.
  - Across the split, v2 is not shown to be better. One pair is an anecdote, and the dense metric is within noise.
  - Its two wrong commits (#537, #871) are what `discover-v3`'s calibrated floor removes.

## #1213 verified by the automated audit (2026-09-26): no human review needed

The operator ruled that a problem already resolved in the literature needs no human review, provided the
verification is complete without one. `audit.py` is that verification. Both #1213 proofs pass all 13 checks (see
`AUDIT.md` in each run):

| check | original (alias 82251) | replication (alias 59388) |
|---|---|---|
| kernel replay (`leanchecker`), compiles, no `sorry` | pass | pass |
| axioms exactly `[propext, Classical.choice, Quot.sound]` | pass | pass |
| no kernel bypass, elaboration-time code or untrusted import | pass | pass |
| **elaborated statement identity** (the proved type and the frozen definition, hashed against a clean elaboration) | pass | pass |
| provenance: the benchmark's statement, formal-conjectures@077138338750, answer `True` | pass | pass |
| faithfulness judges (at build, at verification) | pass | pass |
| blindness: probe `unaware`, masked, `--benchmark`, no prompt names the problem (12 and 18 prompts scanned) | pass | pass |

**Verdict: #1213's formal-conjectures statement is proved in Lean, twice, by blind runs.** The proofs, audits and discovery records are kept in `evidence/1213/`, because `runs/` is not tracked. The solving pin and its knowledge snapshot are tracked too, so the runs can be reproduced exactly. It is a reconstruction
of a result published 2026-04-21, not new mathematics. One response in the original run used the word "Erdős"
unprompted. That is a recall signal to note, not a leak, since no prompt contained it.

**The audit found a hole in the harness's own verification.** `stage_verify` checks that the frozen statement's
TEXT appears in the proof. `tests/test_audit.py` shows a file that proves `(3 : ℕ) < 2` by declaring
`instance : LT ℕ := ⟨fun _ _ => True⟩` above the verbatim frozen theorem:
- it compiles, with no `sorry` and no axioms at all, and it passes `leanchecker`;
- it would have been recorded as `verified`;
- only the elaborated-identity check rejects it.

Every earlier saved proof is being re-audited for this, and the result is recorded below when it lands.

## Breadth before depth: a replay on train, written before launch (2026-09-26)

**What was fixed, and why** (every research-program log on disk):
- 51 of the 79 steps left open by unsolved runs were never attacked: 37 deferred for budget, 14 never reached.
- A hypothesis attack that succeeds costs a median $0.22. 224 of 281 successes came in the one-shot round 1.
- Rounds 3+ produced 1 success, and decompose 1 in 192 escalations. Failed attacks cost $317.6.
- The harness now defaults to:
  - a cheap one-shot sweep of every open conjecture before any depth attack;
  - depth attacks capped at 2 rounds (one-shot + one agentic);
  - `--refute changed` and `--premise-attack cheap`.
- Design: CLAUDE.md, "Breadth before depth".

**Replay:** the 10 distinct train steps that the final residuals left open and no attack ever touched get exactly the
sweep's cheap attempt:
- one round, no agentic, no decompose, $0.60 cap;
- on copies of each run's direction state, so the original runs' accounting is untouched;
- more conservative than a live sweep: no program lemma module, no discovery guidance.

The plan rated them hard 5, moderate 3, unrated 2.

**Write-ahead:**
- 3 of the 10 proved (range 1–5); P(at least 2) = 0.7.
- At most 1 of the 5 "hard" steps. The historical one-shot rates are hard ~5%, moderate ~80%, unrated ~55%.
- Under $6 in total.

**Outcome (2026-09-26): 0 of 9 proved. The prediction was wrong, and the sweep goes back to off by default.**

| step (train) | the plan's rating | result | $ |
|---|---|---|---|
| #283 `hyp_egypt` | unrated | not proved: the omitted-def repair fired, but the proof failed (unsolved goals) | 0.51 |
| #283 `hyp_complete_tail` | moderate | not proved: attempts compiled with `sorry` left | 0.22 |
| #283 `hyp_core` | hard | not a fair replay: it needs the run's lemma module (`IntValued`), which the replay did not import | 0.31 |
| #435 `hyp_lower` | hard | not proved: `sorry` left | 0.19 |
| #435 `hyp_window` | hard | not proved: `sorry` left | 0.27 |
| #1141 `neg_hyp_tail` | hard | not proved: `sorry` left | 0.18 |
| #1141 `hyp_coprime_in_class` | unrated | not proved: `sorry` left | 0.26 |
| #152 `hyp_duality` | moderate | not proved: an `omega` failure and `sorry` left | 0.53 |
| #152 `hyp_gap_linear` | hard | not proved: `le_or_lt` unknown (Mathlib renamed it) and `sorry` left | 0.22 |
| #997 `hyp_bridge` | moderate | replay crashed: the older run has no `launch.json` | 0 |

- **Reading:** the steps a run defers are the hard ones. The attack order is easiest-first, so the historical
  $0.22 median of a *successful* attack was a selection effect, not a property of the deferred steps. "65% never
  attacked" is true, but a cheap attempt does not convert them.
- **What stays:**
  - The round cap (Change B). It needs no replay: 1 success in rounds 3+ out of 278, and 1 decompose success in 192.
  - The two validated defaults.
  - The omitted-declaration repair, a bug fix that fired here.
  - The audit.
- **What goes back behind its flag:** the sweep (`--sweep on`).
- **The real blocker on these items is the hard step itself.** That is the next thing to work on, not allocation.

## Complete-proof conversion on train (2026-09-30), written before launch: `train-conv-fde7891`

**Why.**
- The one solve on dev (#1213) came from discovery writing a complete, refereed informal proof, which the harness
  then formalized for $2.28. The baseline without discovery failed on the same item.
- Everywhere else, the steps left open are the hard cores. Neither allocation (iteration 3) nor cheap attempts
  (the sweep replay, 0 of 9) converts them.
- **The question:** when discovery writes a complete refereed proof, does the harness convert it?

**Items.** The four train items where the train calibration's discovery wrote complete, refereed proofs:

| item | answer | complete refereed proof in |
|---|---|---|
| #678 | yes | 3 of 3 rounds |
| #435 | yes | 3 of 3 rounds |
| #990 | no | 2 of 3 rounds |
| #1037 | no | 2 of 3 rounds |

#678, #990 and #1037 have never had a Lean run. #435 has, with 0–1 pieces at $8.

**Protocol.**
- `discover-v3` (v2's settings plus the calibrated 0.6 floor) on pin `fde7891`. That pin is `main` 6dd67e3: round
  caps, `--refute changed`, `--premise-attack cheap`, the omitted-declaration repair, the audit in final
  verification, and the sweep off.
- **$16 per item**, twice the usual; 6 research cycles.
- A solve now means the true direction verified AND passing the audit's Lean checks.
- Train, so the transcripts may be read.

**Write-ahead predictions.**
- Discovery commits to the true direction on all 4: 0.75. The floor may send a less confident item to `--open`.
- Discovery writes a complete refereed proof on at least 3 of 4: 0.7.
- **Solves**, by item:
  - #678 0.35: a CRT construction, elementary.
  - #435 0.2: its Apéry/valuation core resisted twice.
  - #990 0.2: an explicit lacunary polynomial plus the Vandermonde identity, intricate.
  - #1037 0.1: needs a random graph with small cliques and independent sets, a probabilistic existence argument
    that Mathlib lacks.
  - That makes 0.85 expected, P(at least 1) = 0.6, P(at least 2) = 0.2.
- About $50: an item stops early when it is solved or stalls.

**How the result is used.**
- **At least one converts:** build a blueprint mode, in which the skeleton follows the refereed proof step by step
  and each hypothesis carries its step's informal proof. Route budget by whether discovery wrote a complete proof.
  Then test that on dev, paired.
- **None converts:** read these train transcripts for where conversion breaks, and fix that first. The suspects
  are a plan that ignores the proof, a step too big for one attack, and a Mathlib gap.

**Interim (2026-09-30): #435 and #678 did not convert, and #678 lost a solve to the deferral rule.**
- **#435:** discovery wrote two complete refereed proofs (0.85, 0.9) and committed to TRUE.
  - The harness certified 2 of 3 steps. `hyp_top` stayed open: X(n) − n is not representable, the Apéry-set
    lower bound.
  - Its recursive children's decompositions were judged not easier, or split-only, so nothing was spliced.
  - $13.98.
- **#678:** discovery wrote one complete refereed proof (0.9) and committed to TRUE.
  - The harness certified **12 of 15** steps. Two of its six cycles were lost to skeletons that did not compile
    (undefined names).
  - The last three steps (`hyp_loss_hyp_small`, `hyp_loss_hyp_div`, `hyp_loss_hyp_p`) are elementary lemmas about
    counting multiples. They are siblings of lemmas the run had just proved, and they were **never attacked**:
    cycles 5 and 6 deferred them because a child needs `--min-child-budget` $2.50 and $4.85, then $2.44, was left.
  - $13.56.
- **The decisive replay:** the sweep's cheap one-shot attempt proved **all three** (`hyp_div` $0.17, `hyp_small`
  $0.23, `hyp_p` $0.33). With $0.73 of the $2.44 it left unspent, #678 would have been solved.
- **Reading, next to the 0-of-9 replay above:**
  - Cheap attempts fail on deferred steps that are genuinely hard; 5 of those 9 were rated hard.
  - They succeed on easy steps deferred only for budget.
  - Counting only steps not rated hard, cheap attempts proved 3 of 7 deferred steps.
  - The fix below targets exactly that case.

**Assembled #678 (2026-09-30): a complete proof, but NOT an autonomous solve.**
- **Assembly:** the run's final residual (12 certified steps) plus the three cheap-attempt proofs from the replay,
  spliced mechanically (`splice_hypothesis`) and compiled with the run's own import header.
- **The audit's Lean checks all pass:**
  - compiles, with no `sorry`;
  - axioms `[propext, Classical.choice, Quot.sound]`;
  - kernel replay;
  - the elaborated statement identical to the frozen one (`erdos_28730` and `Finset.lcmInterval`).
- Kept at `evidence/678-assembled/`.
- **What it is:**
  - A Lean proof of #678's formal-conjectures statement, which says there are infinitely many cases where a longer
    block of consecutive integers has a smaller lcm.
  - Its last three steps came from a replay outside the run. By the honesty rules it is not a harness solve, and it
    is not scored as one.
  - It shows the cheap fallback below would have closed the run. Only a fresh run can show the fallback doing it.
- **An audit bug the assembly exposed, fixed:**
  - A frozen `def` inside a `namespace` (here `Finset.lcmInterval`) was looked up by its bare name. It was missing
    from both elaborations, which read as a failed identity check.
  - `frozen_names` now qualifies names by namespace. A test covers it.
  - The #1213 and earlier audits are unaffected, because their frozen defs are top-level.

**The fix: `--cheap-fallback on`, the default.**
- After each cycle's depth attacks, every open step the depth phase did not fund gets ONE cheap one-shot attempt
  with what is left: steps deferred for `--min-child-budget` or beyond `--hyps-per-cycle`.
- Steps rated hard are skipped. Deferred hard steps went 0 of 5, and the plan's rating separates the cases (hard 1
  of 20 proved, elementary 29 of 29).
- It shares the sweep's once-per-statement memory.
- `tests/test_sweep_and_caps.py`, class CheapFallback.
- **To be confirmed:** a fresh #678 run on a pin carrying the fix, after the current lane.

**Outcome (2026-09-30): 0 of 4 solved by the harness itself. $56.06.**

| item | answer | discovery | true direction | $ |
|---|---|---|---|---|
| #435 | yes | 2 complete refereed proofs (0.85, 0.9), committed | 2 certified, 1 open: the Apéry lower bound `hyp_top`; its refinements were judged not easier | 13.98 |
| #678 | yes | 1 complete refereed proof (0.9), committed | 12 certified, 3 open: never attacked, deferred for budget; assembled offline into an audit-passing proof | 13.56 |
| #990 | no | no complete proof this time; both said TRUE (0.6, 0.45), so the floor blocked a WRONG commit | 2 certified, 1 open: the core construction `hyp_family`. Its key bound M ≤ 4m was twice judged "H restated" | 13.75 |
| #1037 | no | no complete proof; both said FALSE (0.55, 0.5), so the floor sent it to `--open` | 1 certified, 1 open. The false direction was stopped as believed false | 14.77 |

- **Against the predictions:**
  - Solves 0 (expected 0.85; P(at least 1) was 0.6).
  - Commits: 2 of 4, both correct (predicted all 4 correct at 0.75). The floor blocked two low-confidence answers.
  - Complete refereed proofs on 2 of 4 (predicted at least 3 at 0.7). Discovery is stochastic: the calibration rounds
    had complete proofs for #990 and #1037 in 2 of 3 rounds each, and this time neither did.
  - Spend $56 (predicted ~$50).
- **The three distinct conversion failures:**
  1. **Budget deferral of easy last steps (#678).** Fixed by `--cheap-fallback on`. The replay and the assembled
     proof show it would have closed #678. A fresh run must confirm it.
  2. **No complete proof from discovery this time (#990, #1037).** Then the plan improvises a route. On #990 its
     choice of exponents needs a bound that is at least as hard as the problem. Discovery is cheap ($0.4–1.1 a
     round), and complete proofs appeared in 2 of 3 calibration rounds. **Retrying discovery until a refereed
     complete proof appears** (capped) is the next lever.
  3. **A genuinely hard core, even with a complete proof (#435).** The Apéry-set lower bound needs a finer
     decomposition than the recursive children produce. This is blueprint work: the refereed proof's own sub-steps
     become the hypotheses.
- **The floor worked as designed.** It refused a wrong commit (#990) and cost nothing on #1037, where the harness
  stopped the false direction itself.

## #678 fresh, with the cheap fallback (2026-09-30), written before launch: `train-678-fallback-543fd9d`

- **Question:** does the harness now close #678 by itself? The previous run left three easy steps deferred with
  budget unspent.
- **Protocol:** the same as `train-conv-fde7891` (`discover-v3`, $16, 6 cycles), on pin `543fd9d`, which is `main`
  041f352 with `--cheap-fallback on`. A fresh alias; discovery and plans are drawn anew.
- **Write-ahead:**
  - P(solved, meaning the true direction verified with the audit passing) = 0.45. The last run's route and budget
    would now close, but a fresh run can take another route, lose cycles to skeletons that do not compile, or get
    no complete proof from discovery (it did in 1 of 2 attempts last time).
  - P(the fallback fires at least once and proves something) = 0.7.
  - About $14.

## `discover-v4` on #990 and #1037 (train, 2026-09-30), written before launch: `train-v4-543fd9d`

- **Why:**
  - In the conversion screen, discovery's single round produced no complete proof for #990 or #1037. The train
    calibration had one in 2 of 3 rounds for each.
  - Without one, the plan improvised. On #990 its key bound was twice judged as hard as the problem.
- **Candidate `discover-v4`:**
  - `discover-v3` plus further rounds of the same two parallel attempts until one yields a complete proof its referee
    accepts: up to 3 rounds, never starting a round that would take discovery past $3.
  - Rounds are pooled for the direction decision, and the floor still applies.
  - Unit-tested in `tests/test_timesplit.py`, class DiscoverV4.
- **Protocol:**
  - Pin `543fd9d`, the same harness as the #678 rerun; the only change is the runner's discovery.
  - $16, 6 cycles.
  - It launches when the #678 rerun ends.
- **Write-ahead:**
  - A refereed complete proof within 3 rounds: #990 0.75, #1037 0.65.
  - A commit to the true direction (NO) on each: 0.65.
  - Solved: #990 0.25. Even with the construction written out, the multiplicity-at-1 argument and the M ≤ 4m bound
    are intricate Lean.
  - Solved: #1037 0.1. It needs graphs with small clique and independence numbers, a probabilistic existence
    argument that Mathlib lacks.
  - Discovery spend $1–3 an item, about $30 in all.

**Outcome (2026-09-30): not solved. Closed apart from ONE published premise, $11.70.**
- **Discovery:** two complete refereed proofs (0.93, 0.9), committed to TRUE.
- **The harness:** 4 certified steps and 0 open conjectures. One published premise stayed open: `hyp_ramanujan`,
  "for x ≥ 11 there are primes p < q in (x/2, x]" (Ramanujan 1919). Mathlib has only Bertrand's single prime. The
  previous run's route needed Bertrand alone (used four times), so this plan's route asked for more than it needed.
- **The fallback fired once:** a cheap attempt on the deferred `hyp_final` in cycle 1 failed ($0.82). The next
  cycle's depth attack proved that step.
- **Why it stopped:**
  1. `--premise-attack cheap`, the default since 2026-09-26, gave the premise only the free tactics
     (`premise_kept`, cycles 3 and 4) and never a real attack. The earlier `full` policy attacks a premise only
     once no conjecture is left, so on this run it could only have helped.
  2. In cycle 4 the plan proposed replacing the premise with a strictly WEAKER conjecture: a prime in (n+1, 2n] for
     n ≥ 12, Bertrand with one endpoint removed. `residual_improves` rejected it as "no improvement", because it
     ranks fewer open conjectures ahead of fewer published premises. For a complete proof, a premise not in Mathlib
     blocks as much as a conjecture.
  3. Then two stalled cycles ended the run, with about $4 unspent.
- **Against the predictions:** solved no (0.45). The fallback fired, but it proved nothing (predicted: fires and
  proves something, 0.7).
- **Follow-ups:**
  - `--premise-attack cheap` as a default is reconsidered below, with a replay of a full attack on the premise.
  - Letting a plan trade a published premise for a weaker, plausibly provable conjecture once no conjecture is open
    is a change to the adoption rule. It is recorded as a candidate and not made here.

**The premise, attacked in full (2026-09-30): proved for $3.22.**
- A replayed full attack on `hyp_ramanujan` proved it in its first agentic round. The one-shots failed on Mathlib
  names.
- Spliced into the run's residual, the proof is complete and passes all 7 of the audit's Lean checks
  (`evidence/678-assembled-b/`, not an autonomous solve).
- **So both #678 runs ended one mechanical policy short of a solve:**
  - the first on deferral, now fixed by the cheap fallback;
  - the second on `--premise-attack cheap`.
- **`--premise-attack` is back to `full` by default.** Premises are attacked only once no conjecture is left, when a
  full attack has no better use for the money.
- **Next:** a third fresh #678 run with both fixes, after the v4 lane. Pre-registered in the section below when it
  launches.

## #678 fresh, both fixes (2026-09-30), written before launch: `train-678-both-f27eaff`

- **Question:** with the cheap fallback AND `--premise-attack full`, does the harness close #678 by itself?
  - The two earlier runs each ended one policy short.
  - Both fixes are on by default in pin `f27eaff` (main cf2bc72).
- **Protocol:** as before: `discover-v3`, $16, 6 cycles, a fresh alias. It launches after the v4 lane.
- **Write-ahead:**
  - P(solved: true direction verified and audit passing) = 0.55. Both known blockers are removed. A fresh run can
    still take a new route, lose cycles to skeletons that do not compile, or hit a genuinely hard step.
  - About $13.

**Outcome of `discover-v4` (2026-09-30): 0 of 2 solved. $24.06.**
- **#990:** 3 rounds and 6 attempts, ALL saying TRUE, which is wrong, at 0.4–0.6, and none complete. The floor
  blocked a commit. The true direction ended with 3 certified and 2 open. $16.34.
  - The retries bought nothing here. This session's four rounds on #990 produced no complete disproof, against 2 of
    3 in the calibration. The per-round rate looks closer to 2 in 7 than 2 in 3.
- **#1037:** round 1 already had a complete refereed disproof (0.88), so no retry was needed, and it committed
  correctly to NO.
  - The true direction: 3 certified, 0 open conjectures, and **1 published premise**, Erdős 1947 (Ramsey graphs
    with no clique or independent set above C log r exist). $7.72.
  - Pin `543fd9d` still had `--premise-attack cheap`, so the premise got only the free tactics. A full attack is
    being replayed, as it was for #678's Ramanujan premise.
- **Against the predictions:**
  - A complete proof within 3 rounds: #990 no (0.75), #1037 yes (0.65).
  - A correct commit: #990 no (0.65), #1037 yes (0.65).
  - Solves: 0 (0.25, 0.1).
  - $24 (predicted ~$30).
- **Reading:** discovery retries do not reliably produce a complete proof on #990. The live blocker on #1037 is the
  premise policy that has already been reverted.

**#1037's premise, attacked in full (2026-09-30): proved for $2.70.**
- A replayed full attack proved Erdős's 1947 Ramsey-graph bound in Lean.
- Spliced into the run's residual, the disproof is complete and passes all 7 of the audit's Lean checks
  (`evidence/1037-assembled/`, not an autonomous solve).
- **The pattern:** #678 and #1037 both ended closed apart from one published premise that Mathlib lacks, and a full
  attack proved each for about $3. `--premise-attack full`, the default again, would have run that attack in-run.

**Outcome (2026-10-01): not solved. Every conjecture certified, closed apart from TWO published premises, $15.52.**
- **Discovery:** two complete refereed proofs (0.88, 0.88), committed to TRUE.
- **The cheap fallback worked in-run for the first time:** in cycle 3 it proved **4 of 4** deferred steps for $1.47.
  With them, 8 certified and 0 open conjectures.
- **What stayed open:** Nagura 1952 (a prime in (n, 6n/5] for n ≥ 25) and Nair 1982 (lcm(1..n) ≥ 2^n for n ≥ 7).
  Neither is in Mathlib.
- **Why it stopped:**
  - `--premise-attack full` did choose to attack both premises (`premises_attacked`, cycles 4 and 5).
  - But cycles 4 and 5 first spent the last $2.70 on experiments and two re-plans of a skeleton that was already
    closed.
  - Both premises were then deferred at $1.33 and $0.48, below `--min-child-budget` $2.50, and two stalled cycles
    ended the run.
- **Against the prediction:** solved no (0.55). Spend $15.52 (predicted ~$13).
- **The fix, `premise endgame`, on by default with `--premise-attack full`:** once only published premises are open,
  - a cycle no longer runs the refutation script or re-plans;
  - the last premise attack is funded with whatever is left, at least $1, instead of being deferred.
  - Tests: `tests/test_allocation_options.py`, class PremiseEndgame.
  - Replays of full attacks on Nair and Nagura are running.
