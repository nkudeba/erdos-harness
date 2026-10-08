# Long computation tier

`long_compute.py` runs finite computation cases without keeping a model session
open. It is opt-in. Defaults are two hours per case and four hours across all
attempts, including retries. This adds a computation capability; it is not evidence
that the harness can resolve more open problems.

## Select the work

Check the forum and existing search floor first. Derive necessary conditions before
calling a solver. For finite existence questions use the existing SAT solver when
appropriate. Order cases by least slack in those conditions and isolate the forced
structure. Each script should be one independently checkable case or a modest batch
of cases. The controller checkpoints between scripts, not inside a solver call.

Do not blindly replay an old session script. Several #366 scripts stop themselves
after 108 seconds and print `PARTIAL` with exit code zero. Raising the controller's
timeout does not remove that limit or make their output exhaustive. Review the code,
its parameter coverage, internal stop conditions and expected output first.

Prepare a job with scripts listed in attack order:

```sh
python3 long_compute.py prepare --output runs/long-compute-PROBLEM \
  --problem PROBLEM --script /absolute/path/case1.py --script /absolute/path/case2.py \
  --scope 'Exact finite cases being decided, with their necessary-condition reduction' \
  --order-by 'Increasing slack in the stated necessary condition' \
  --seconds 7200 --total-seconds 14400
python3 long_compute.py run runs/long-compute-PROBLEM
```

The scripts are copied, hashed, syntax-checked and screened with the exploration
allowlist. Execution always uses `harness.sandbox_argv`, including isolation, solver
imports, PARI secure mode and the macOS sandbox. No model calls are made. One worker
owns a job directory. SIGTERM/SIGHUP stop the active solver and save an interrupted
attempt. Output goes directly to a file instead of accumulating in memory.

## Resume and inspect

Rerun the same `run` command. Completed cases are skipped. Failed or interrupted
cases can retry within the remaining total budget. Timed-out cases are skipped
unless `--retry-timeouts` is explicitly supplied. A possibly live orphan solver
prevents resume. A controller killed without cleanup conservatively charges that
attempt's full allowance. Altered scripts are refused; use a new job for new code.

`manifest.json` pins the source scripts, order, scope and budgets. `state.json`
records every attempt, elapsed time and process status. Each case has its own
attempt logs. `RESULTS.md` links them and distinguishes pending, completed, failed,
interrupted and timed-out processes.

An exit-zero process is **not** an exhaustive result, witness certificate, Lean
verification or resolution. Inspect the actual output and independently validate
its mathematical claims. A timeout establishes no floor. Record any established
finding through the usual Atlas workflow with its scope, floor kind and enumerable
object units; feed reviewed evidence back through research guidance. Open-problem
resolution still requires the existing Lean audit and independent human review.

## Relationship to the queue sweep

The map-free screen and the Claude campaign continue to share one model lane.
Finish `settle_nomap.py --calib`, then inspect `--analyze`. `--sweep` refuses an
incomplete or failing calibration. The sweep is serial, stops immediately on a
hard provider failure, and reserves each problem's full call cap against both
`--max-spend` (default $150 additional spend) and the campaign's rolling daily cap.
It resumes from saved problem rows. Recorded prescreens already order the campaign
queue, so no priority-list rewrite is necessary.

The long computation tier is available for suitable cases if the completed queue
sweep confirms few promising targets. It is not automatically enabled from the
current incomplete calibration. Do not claim the queue-wide distribution from the
24 open calibration items completed so far.

Validation on 2026-10-08: eight controller tests cover timeout, preserved output,
budget persistence, resume, changed-script refusal, unsafe-script refusal, duplicate
workers and live-orphan detection. A real sandbox smoke test used CaDiCaL to decide
contradictory unit clauses. This checks plumbing, not mathematical performance or
multi-hour reliability.
