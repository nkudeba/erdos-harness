# Open problems with the Navier–Stokes features (2026-10-02)

Written before the full run on #455 launched. The outcome section below is added when it ends and nothing above it
changes.

## What was built for this

These four features are in `harness.py`, all default OFF; CLAUDE.md describes them in "In-run discovery, blueprints
and dated libraries".

1. **`--discover-draws N`**: independent discovery draws, which share the ladder, until a refereed complete proof
   appears.
   - Train screens put one draw's rate on hard items at about 0.29 (benchmarks/timesplit/RESULTS.md, Screen D).
2. **`--blueprint-reroute on`**: premise-aware routing.
   - Each cited step of a blueprint is checked against Mathlib. A claimed name must exist in the local declaration
     index; an unsure or invented name counts as missing.
   - When a step is missing, a variant proof avoiding it is requested, refereed, and adopted only if it leaves fewer
     missing premises.
   - Runs C and D ended every closure attempt at a premise Mathlib lacks.
3. **`--rediscover N`**: Lean inside the discovery loop.
   - A conjecture that FAILED a Lean attack gets its own cross-fed discovery. That discovery is told what Lean has
     already certified around the step and what broke.
   - A refereed proof becomes the step's blueprint, and its next attack is recursive.
   - A refereed disproof becomes a failure the next plan must answer.
4. **`--blackboard on`**: campaign memory in `programs/erdos_<n>/BLACKBOARD.md`.
   - Each run appends its discovery synthesis, its Lean-certified facts (marked [Lean]), its open steps and its
     failures.
   - The next run's discovery starts from it.
   - `--discover-model` routes the route-choosing calls to another model. It is unused here, because of Fable's usage
     limit.

## The discovery screen: 7 open problems, no Lean, $12.90

The candidates were open on erdosproblems.com, never attacked by the harness, formalised in formal-conjectures, carried
no prize, and had no fresh claimed resolution.
- #1062 and #1054 were dropped: both now carry claimed resolutions, one Lean-verified.
- #859 was dropped after the screen: a full Lean proof was claimed by conjectures.io on 2026-09-27, unverified.

Each problem got:
- one cross-fed draw with a ladder of three easier variants;
- its formal-conjectures statement, answer stripped;
- its forum thread as its library;
- `--blackboard on`.

| # | decided | refereed complete proof | what the ladder proved informally | the open core every attempt named | $ |
|---|---|---|---|---|---|
| 1203 | TRUE | no | limsup F = ∞; liminf F ≥ 1; F → ∞ on a density-one set | an integer with ≥ C·log K/log log K prime factors in EVERY short interval (n, n+K] | 1.06 |
| 463 | TRUE | no | "almost every n" for f(n) = log n; the full statement under Elliott–Halberstam | a pointwise lower-bound sieve for primes p with ⌊n/p⌋+1 p-rough (the parity barrier) | 1.83 |
| 455 | TRUE | no | liminf q_n/n² > 0 with an explicit constant, a weaker form of Richter 1976 | zero density of small gaps along a convex prime sequence: a uniform sieve for long almost-quadratic prime patterns | 1.33 |
| 153 | TRUE | no | the asymptotically-maximum case (as on the forum); a bound above the Cauchy–Schwarz value 4 | Sidon sets with diameter between (1+δ)n² and Cn² (the forum's remaining case) | 1.96 |
| 1192 | TRUE | no | r = 2 (Ruzsa's theorem) and a weaker probabilistic version for all r | a "block lemma" for r ≥ 3 | 2.33 |
| 859 | TRUE | no | d_t exists, by periodicity mod lcm(1..t); Erdős's two-sided bounds | the exact asymptotic d_t ~ c₁/(log t)^{c₂} | 1.87 |
| 156 | TRUE | no | the greedy lower bound N^{1/3}; maximal Sidon sets of size O(n^{1/3}) in ℤ_n for n = p², p²−1, p³ | a Sidon set Y of size O(√L) with [1, L] ⊆ Y − Y | 2.51 |

**Reading:**
- On every problem, discovery reconstructed the published partial results and named the open core precisely, matching
  the forum record wherever there is one (#153 and #1192). It did not invent a proof.
- These problems are not open from neglect. The 2026 AI wave has already taken most of those, and these remaining
  ones sit behind real barriers: the parity problem, uniform sieves, and structure theorems for Sidon sets.
- Possibly new: #156's cyclic-group analogue and #1203's density-one statement. Both are informal and unchecked, and
  neither is a resolution.

## The full run: #455

**Why #455:**
- No proof claim.
- The frozen statement needs only Mathlib.
- The decomposition is clean: non-decreasing gaps must tend to infinity (elementary), plus the open zero-density core.

**Settings:**
- `--open --discover on --discover-mode crossfed --discover-rounds 2 --discover-ladder 3 --discover-draws 3`
  `--discover-total-budget 9`
- `--blueprint on --blueprint-reroute on --residual-view outline --rediscover 2 --blackboard on`
- `--library experiments/open-discovery-2026-10-02/library/455-full`: six OpenAlex papers (Green–Tao, GPY I and II,
  Maynard, Zhang, Pintz) plus the forum thread.
- `--run-budget 40 --research-cycles 6`, Opus 5.5.
- Statement: formal-conjectures `erdos_455`, answer stripped, recorded in the run state.

**Write-ahead** (`predict.py record --problem 455 --p-resolve 0.002`):
- Resolved (true direction verified, audit passing): 0.002.
- Discovery writes a refereed complete proof in 3 draws: 0.05. If it does, the proof is more likely flawed than not,
  given the barrier.
- A certified conditional theorem with at least one non-trivial certified piece: 0.6.
- Rediscovery fires at least once: 0.6. It writes a refereed proof of a failed step: 0.25.
- The blackboard ends with [Lean] entries: 0.7.
- About $35–40.

**Honesty:** #455 is open. Any Lean result is mechanically verified, never a resolution by itself; `claimEligible` stays
false; a claim would need human review.

## Outcome

The run ended on 2026-10-02 at 05:45 UTC after 93 minutes: exit 3 (partial), $18.99 of the $40 cap, 65 model calls,
119 Lean checks. The descent stalled after cycle 3 of 6: two cycles discharged nothing.

```
RUN-SUMMARY problem=455 exit=3 outcome=partial directions=pos:partial verified=None spend=$18.99 llm_calls=65 lean_checks=119 lemmas=2 fatals=0 wall=93m mode=research dir=runs/20261001-230105-000000-erdos455
```

The summary line the run wrote itself says `outcome=running`. That was a reporting bug, fixed after the run, and the
corrected reprint is shown above.

**#455 is still open.** Nothing below is a resolution. Nothing has had human review, and `claimEligible` stays false.

### What it produced

- **Discovery** ($3.70): three draws, 12 attempts, every one TRUE, none a refereed complete proof. The run committed to
  the true direction with the whole budget.
  - The synthesis reduced the problem to `U(x) = o(x)`: the gap sequence must skip almost every even value.
  - It listed the dead ends: sieving with fixed small primes only; proving that runs of equal gaps are rare, which is
    false in the Cramér model; sieving the whole configuration at once.
  - One warm-up rung gave a complete informal proof of the probabilistic analogue.
- **Cycle 1 skeleton**, a certified conditional theorem: the frozen statement follows, by Lean-checked glue, from two
  hypotheses.
  - `hyp_convex_tail`, which says `(n−k)·d_k ≤ q_n − q_k`, was certified within a minute.
  - `hyp_no_short_convex_chain` is the open core: no chain of n/2+1 primes below Cn² with nondecreasing gaps
    ≤ 2Cn.
- **The core's sub-residual certified `hyp_gap_lower`.** In any finite chain of primes with nondecreasing gaps, the
  i-th gap is at least i/6. Summed, this gives `q_n ≥ n(n−1)/12`, so liminf q_n/n² ≥ 1/12.
  - That is a weaker form of Richter 1976 (0.352), which makes it a reconstruction of published mathematics.
  - The proof is 300 lines. It includes the bound Σ_{even e ≤ x} r(e) < 2.63x, where r(e) is the least prime not
    dividing e.
  - It passes every Lean check of `audit.py`: source scan, imports, compile, no sorry, standard axioms, statement
    identity, and kernel replay with `leanchecker`.
  - The proof and its audit record are in `evidence/455_gap_lower.lean` and `evidence/455_gap_lower.audit.json`.
    `programs/` is gitignored, so without this copy the proof would live on one machine.
- **The core stayed open.** The sub-residual offered the same refinement three times: the gap bound plus a "flat
  chain" piece. The refinement judge refused it each time, correctly: the flat-chain piece is the core restated,
  because the gap bound supplies its extra conditions for free.

### The four new features, as used

| feature | fired | what it did |
|---|---|---|
| `--discover-draws 3` | yes | all 3 draws ran, because none produced a refereed proof; $3.70 in total |
| `--blueprint-reroute on` | no | no refereed complete proof, so no blueprint, so nothing to reroute. **Untested live.** |
| `--rediscover 2` | once | on the core, after its failed attack. Its prompt carried the [Lean] facts. All 4 attempts used them and named the step as implying #455. No proof; $0.76 |
| `--blackboard on` | yes | discovery read the screen's entry (6,395 characters); the run appended its discovery, the rediscovery and its Lean residual |

### The predictions, scored

| write-ahead | p | happened |
|---|---|---|
| resolved | 0.002 | no |
| a refereed complete proof in 3 draws | 0.05 | no |
| a certified conditional theorem with a non-trivial certified piece | 0.6 | partly: the conditional theorem was certified, but its certified piece is the elementary tail lemma. The non-trivial gap bound sits below a refused refinement |
| rediscovery fires | 0.6 | yes |
| rediscovery writes a refereed proof of a failed step | 0.25 | no |
| the blackboard ends with [Lean] entries | 0.7 | yes |
| cost | $35–40 | $18.99: the stall rule stopped the run at cycle 3 |

### Defects the run exposed, and what was done

- **The brief said "six cycles" for a run that stopped at three.** The stop message printed the `--research-cycles`
  cap. It now says `ran N of M cycle(s)`, and `tests/test_deductive_mode.py` checks it.
- **The summary line printed `outcome=running` for a finished `--open` run.** `run_summary_line` now maps the run's
  OWN `DONE` exit code, as `collect_run_facts` already did; a caller's exit code still cannot set it.
  `tests/test_run_summary.py` checks it.
- **The blackboard left out the strongest Lean fact.** The gap bound lived in a sub-residual, and the entry header read
  "run pos".
  - `_blackboard_sub_facts` now lists facts certified below, with the definitions they use, and the header names the
    parent run (`tests/test_discovery.py`).
  - A corrected entry was appended to `programs/erdos_455/BLACKBOARD.md` by hand.
- **The automatic brief also left out the gap bound**, because its facts carry no statements of sub-residual lemmas.
  - The brief was corrected by hand (`455-brief.md`, filed with `record_finding.py --brief`).
  - Not fixed in the harness.
- **The Atlas finding is recorded:** the rationale, the requirement and the residual JSON, under #455 in
  `atlas-data/reviewed.json`.

### Reading

- On #455 the pipeline reached exactly the published frontier, and no further.
  - It reproved, in Lean, a weaker form of the one published partial result (Richter 1976).
  - It isolated the open core, the uniform sieve for nearly quadratic prime patterns.
  - It recognised every restatement of that core as a restatement: the refinement judge three times, the rediscovery
    attempts four times.
- That is honest behaviour, but not new mathematics.
- Two of the four new features never met their trigger:
  - the reroute, because there was no refereed proof;
  - the second rediscovery, because only one step ever failed.
- So this run is evidence about discovery, rediscovery and the blackboard, not about rerouting.
- A next run on #455 would start from the blackboard. It would gain only if the plan stops re-proposing the
  flat-chain split.
  - The refusals do reach the plan already.
  - What it lacks is a route to `U(x) = o(x)`, and nothing in this run suggests one.
- **Better targets** for the reroute and blueprint features are problems where discovery does find a refereed proof:
  the train items where a crossfed draw succeeded about 0.29 of the time.
