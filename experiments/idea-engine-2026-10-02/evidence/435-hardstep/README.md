# #435: a hard step proved in Lean from the research engine's proof, and the full statement assembled

This is evaluation evidence only. Nothing the harness runs may read it.

**What it is.**
- A machine-checked Lean proof of #435's formal statement: for n ≥ 1 not a prime power, X(n) − n is the largest
  integer that is not a non-negative combination of C(n,1), …, C(n,n−1).
- #435 is a time-split TRAIN item, resolved in the literature (Hwang–Song, arXiv:2412.17882; Cambie's forum proof,
  formalised by Aristotle per Alexeev, February 2026). This is a reconstruction of a published result, never new
  mathematics. For a problem resolved in the literature, the audit's pass is the verification.
- **It is not an autonomous solve.** It was put together from three runs, with operator budget raises and a mid-run
  harness fix (listed below). It is not scored as a solve.

## How it was put together

1. **The train run** (`train-conv-fde7891`, alias 27285, `runs/20260929-221804-024129-timesplit-erdos27285`, $12.84).
   Its deductive program certified 2 steps, the upper-bound half among them. It stalled on `hyp_top`: X(n) − n is NOT
   representable. That is the lower-bound half, the only step it left open.
2. **The research engine on the step** (`runs/20261002-235647-826042-hardstep-erdos727285`, $8.00).
   - It ran masked under `--benchmark`, with a fresh synthetic id.
   - Its frame said that the whole problem was resolved recently, without saying how. That cue is not available on
     open problems.
   - Two sessions proved the step informally (r1s1/C1, deep/C1r), and each passed a step referee and an adversary.
   - The route was a digit potential φ on ℤ/n built from the tower generators C(n,p^d). It is a lower bound for the
     Apéry set, by a carry lemma and an inequality (E) for every non-tower binomial. See `engine_IDEAS.md`.
3. **The deductive Lean loop with that proof as its blueprint** (`runs/20261003-004608-866727-hardlean-erdos727285`,
   `hardsteps_lean.py`).
   - The blueprint had 22 steps (`BLUEPRINT.md`). The first skeleton had 23 hypotheses, and the run reached 34
     certified lemmas in all.
   - It took one run and three resumes, $66.28 in total. The run's `assistance` field records each one:
     - the run ended partial at $15.25 with 17 of 25 steps certified, and the operator raised the budget to $35;
     - the operator stopped it at $29.83 to load the splice fix `8641308`, after a certified proof of S19b had been
       thrown away by a harness bug, and raised the budget to $50;
     - the run ended partial at $50.66 with 4 steps open, and the operator raised the budget to $70.
   - It closed at 11:16 UTC on 2026-10-03. The run's final verification (`--audit on`) cleared.
   - `HardStep_AUDIT.md` passes all 7 Lean checks. The `benchmark_record` row fails because this is not a time-split
     evaluation run.
4. **Assembly** (by the operator, mechanical).
   - The step's identifiers were renamed back to the train run's: `erdos_727285` → `erdos_27285_hyp_top`, plus the two
     frozen defs.
   - The renamed proof was spliced into the train run's final `Residual.lean` with `splice_hypothesis`.
   - The result was compiled under the train run's import header plus `Mathlib.Data.Nat.Choose.Lucas`. That is
     `Erdos435_assembled.lean`.

## Checks

`audit.lean_checks` against the train run's frozen statement (`assembled-checks.json`). All 7 pass:
- source scan, imports, compiles, no `sorry`;
- axioms `[propext, Classical.choice, Quot.sound]`;
- elaborated statement identity of `erdos_27285`;
- kernel replay.

## Was the route new?

No. It is the published route, as `benchmarks/timesplit/ideas/435.md` describes it:
- the Apéry set with respect to n;
- the C(n,p^j) acting as mixed-radix digits through their valuations;
- every other binomial no smaller than its digit representative.

The model's memory of public solutions cannot be excluded, only cued less.

## What it shows about the harness

The train run stalled on its hard step, and the step-level failure rate for hard steps was 1 in 20. With an informal,
refereed proof as its blueprint, the deductive loop certified that step. That cost $66 against the train run's $13.
More than half of it went on the last few steps: the tower carry step S11, and the inequality S21a for non-tower
binomials.

## Files

- `Erdos435_assembled.lean`: the full statement, assembled. `assembled-checks.json` holds its checks.
- `HardStep_proof.lean`: the hard step's proof as the Lean run closed it. `HardStep_AUDIT.md` and `.json`,
  `HardStep_SUMMARY.line`.
- `BLUEPRINT.md`: the engine's proof, cut into steps. `RESIDUAL_final.md` is the Lean run's final residual.
- `engine_IDEAS.md`: the engine run's claims and verdicts.

## Where the $66.28 went

- About $11 at the top level: plans $6.60 (eight calls, including re-plans the adoption rule refused) and refutation
  experiments $2.91.
- The rest went to children:
  - cheap one-shot attempts proved roughly 8 of about 20;
  - depth and recursive children proved 16 of 18 (S12 and S21 failed at depth, then closed by restructuring);
  - the core steps took most of it: S11 in five pieces, S21a, S12 and S7.
- Two kinds of waste were avoidable:
  - the S19b proof lost to the splice bug, together with its re-attack;
  - two re-plans that only split statements. The adoption rule refused them, because more explicit statements score
    higher on syntactic complexity.
