# erdos-harness — instructions for any coding agent

`CLAUDE.md` in this directory is the full working guide and the single source of truth: Atlas upkeep,
the two scoring axes, what to read before attacking an open problem, and the honesty rules. Read it.
Everything below is the part that agents most often get wrong, repeated here because Codex and other
drivers do not read `CLAUDE.md`.

## Reporting a run — one line, never a log dump

`harness.py run` ends by printing one greppable line (also written to `<run_dir>/SUMMARY.line` and
appended to `runs/summary-log.tsv`), on the fatal path too:

```
RUN-SUMMARY problem=677 exit=3 outcome=running directions=pos:infrastructure_error,neg:running \
  verified=None spend=$8.07 llm_calls=19 lean_checks=42 lemmas=5 residual=open:2,published:1,certified:3 \
  fatals=2 wall=60m mode=research dir=runs/...
```

A background watcher must use it instead of parsing `log.jsonl`:

```bash
tail -1 <run_dir>/SUMMARY.line
grep RUN-SUMMARY <lane.log> | tail -1
python3 harness.py summary --problem 677              # read-only reprint, any time
```

`summary` takes the exit code from the run's own `DONE` and does not overwrite `SUMMARY.line` without
`--write`. Never have a watcher re-derive the exit code: `echo "... $(date) exit=$?"` reports `date`'s
status, not the command's. Capture `EX=$?` on the very next line, or just read `SUMMARY.line`.

Run **one** watcher per lane. Do not start a second waiter for a condition something is already
waiting on, and do not echo tens of log lines per check.

`residual=` appears on research runs: the deductive loop's conditional theorem — how many hypotheses the
frozen target still rests on, by kind. `open` conjectures are exactly as unproved as the problem; a
`published` premise is a cited theorem stated as a hypothesis (never an axiom). Read
`programs/erdos_<n>/RESIDUAL.md` for the statements. `lemmas=` alone no longer measures progress.

## Pacing

One model lane at a time (`CLAUDE.md` explains why: spend limits are a hard failure). Runs resume with
`--resume`. macOS has no `timeout`; use a perl alarm. The harness defaults to `claude-opus-5-5`
(`DEFAULT_CLAUDE_MODEL`); never use Opus 5, and never let a call reach the CLI default (Fable), which hits its
usage limit long before Opus and kills a run at the literature stage with exit 1.

## Honesty

A compiling Lean proof is mechanically verified, never a resolved problem. Record operator assistance.
Report unavailable costs as unavailable, not as zero. `outcome` in the summary line comes from the
parent run only — a research sub-run logs its own `outcome=proved` for a certified lemma, and reporting
that as the problem's outcome would claim an open problem was solved.

## Briefs, facts, solvers, floors

- Every run ends with a plain-language brief in `atlas-data/briefs/<n>.md`, shown on the Atlas problem page.
  `python3 harness.py brief --problem N` regenerates one. It is fact-pinned and must never claim a solve.
- Take run facts from `collect_run_facts(run_dir, pid)`, never from one `state.json`: `--open` children and
  research sub-runs keep their own state, and reading the parent alone has produced three wrong reports.
- For "does a finite object exist?", encode it for `pysat` (available, on the allowlist) instead of writing a
  backtracking loop. UNSAT is a proof of non-existence in the encoded range; a timed-out DFS proves nothing.
- Every search floor carries a `kind`: `exhaustive` / `screen` / `published` / `unrecorded`. Never report a
  screen as a search. File it in **enumerable-object units** (#993's `n <= 32` is 1.1e11 trees), not the
  problem's own parameter, or the triage gate reads an unreachable check as a cheap one and runs it anyway.
- `search_futility` reads a recorded floor from `problems/erdos_<n>.json` **or** from `atlas-data/reviewed.json`
  (`atlas_search_floor`). It used to read the problem file alone, which exists for ~40 of 1,217 problems, so
  floors recorded for the rest were inert.
- Before a solver call, ask what the structure forces. A residue-free algebraic necessary condition eliminated
  20 of 29 candidates on #273 in milliseconds, including the two that had absorbed four solver timeouts.

## Cluster libraries

- A problem TAG can carry a formalised Lean module into the run: `CLUSTER_LIBRARIES` in `harness.py` maps
  `covering systems -> Formal.Library.CoveringSystems`. The module is added to the import header and NAMED
  (names only, never bodies) in the reduce/prove prompts. Import the machinery; do not re-derive it.
- A module only goes in the table once it builds sorry-free. `_ensure_library` runs `lake build` at run
  start and DROPS a module that will not build — an `import` of an unbuilt module fails every check in the
  cluster, not just the attempt that wanted it.
- A library that reconstructs a published theorem (Mirsky-Newman, 1950) says so in its own docstring. It is
  mechanically verified, never new mathematics.

## Reductions, escalation, readings

- `stage_reduce` looks for structural reductions before any search, and **empirically checks each one** in
  the sandbox before it is allowed to reach the search or proof prompts. An unchecked reduction is a
  liability: downstream stages treat it as fact.
- A stalled search (timeout, or a range cleared only by a cheap `screen`) **escalates** to a SAT encoding
  that decides the first undecided case, instead of stopping on a timer. An undecided escalation never
  overwrites the existing floor with a weaker claim.
- `record_readings` records what the frozen Lean statement assumes beyond the published sentence, classified
  `essential` / `conventional` / `risky`. A proof is about the frozen statement; the gap is part of the result.
- Every model-written script runs via `sandbox_argv(script)` — never build your own `-I` command line, or
  the script cannot import the solver the allowlist promises.
- Order candidate cases by **slack** in the screening necessary condition, not by size, and factor out
  whatever that condition forces. #273 spent three attempts on its smallest candidate, which was among its
  loosest; the tightest one collapses to 12 enumerable cases. A search that enumerates cases must print
  `CANDIDATES: {"order_by": ..., "cases": [...]}` in attack order.
- `score` and `partial` are NOT probabilities — sums of hand-assigned points, never checked against an
  outcome. For estimates use `python3 atlas-data/predict.py estimate --problem N` (free, no model calls);
  it returns a reference-class ceiling, never a calibrated number. Every run logs a prediction to
  `atlas-data/predictions.jsonl`; `predict.py score` reports Brier and calibration once outcomes land.
