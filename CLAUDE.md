# erdos-harness — working instructions

LLM + Lean 4 harness for Erdős problems. `harness.py` is the pipeline, `formal/` is the Lean project,
`runs/<ts>-erdos<N>/` holds every run, `knowledge/solved/` holds verified proofs, `atlas-data/` holds the
feasibility ranking of the whole 1,217-problem catalogue.

## Keep the Atlas current — do this as you learn, not at the end

The Atlas is the memory that decides what we attack next, so **every time a run or an assessment teaches us
something about a problem, record it before moving on.** A finding that stays in a chat transcript is lost.

The ranker picks up *mechanical* evidence by itself: it scans `runs/` and `knowledge/solved/`, so a verified
proof moves a problem to the Demonstrated tier with no action from you. What it cannot see is the qualitative
half, and that is the half worth recording:

- a feasibility assessment (why a problem is or is not worth the budget)
- a published exhaustive check that makes a bounded search pointless, as a **search floor**
- a third-party resolution or refutation claim, marked as verified or not
- a proof route that worked, or a class of approach that provably fails
- a corrected reading of the statement (several site snippets are truncated or ambiguous)

Record it with:

```bash
python3 atlas-data/record_finding.py --problem 287 --score 8 \
  --rationale "why, in one or two sentences" \
  --requirement "what an attempt would actually have to do" \
  --search-floor 4e19 --source experiments/open-top3/287-assessment.md
```

This merges into `atlas-data/reviewed.json`, stamps `problems/erdos_<n>.json` with the search floor when you
pass one, and regenerates `rankings.json`, `rankings.csv` and the private site's `data.json`. Use
`--no-rerank` to batch several findings, then run `python3 atlas-data/rank_problems.py` once. No model calls,
no cost. Scores are heuristic feasibility estimates, never probabilities.

A recorded `search_floor` closes the loop back into the harness: `search_futility` in `harness.py` reads it
from the problem file at triage time and skips a futile search stage without spending a model call.

**The live site picks these up on its own.** Revised scores ride the same 30-second channel as run evidence:
`result_feed.py` publishes every reviewed problem's score, reasons and requirements to `/api/results`, and
the page overlays them on its baked snapshot, re-sorting ranks and recomputing tiers. So recording a finding
is the whole job — no rebuild, no redeploy. `.result-feed/status.json` shows `revised_scores` (accepted) and
`pending_scores` (queued). If `pending_scores` stays non-zero, the deployed build predates live rankings and
the site needs one redeploy; the publisher keeps run evidence flowing meanwhile and starts sending scores by
itself once the new build is up.

## Two axes, not one

`score` asks whether the harness can produce a **complete** proof. For an open problem that means new
mathematics, so every open target scores low and the list collapses into an undifferentiated tail.
`partial` (unsolved problems only, 1-80) asks the question that actually matters there: **how much certified
partial value is reachable** — a proved special case to formalize, an explicit object to certify, a reusable
definition. The two are independent and must never be summed. #488 and #848 both sit at priority 8 with
partial 63, which is the correct reading: hopeless as resolutions, genuinely worth formalizing in part.

## Before attacking an open problem

Fetch its forum thread and proof-claims page first: `python3 atlas-data/fetch_forum.py --problems N`. The
main page is not the whole record. #488's claimed counterexample and #287's "no counterexample below 4e19"
certificates exist only there, and either one changes whether the problem is worth a run at all. The ranker
reads whatever is cached and derives its own penalties from it.

## Honesty rules that outrank convenience

- A compiling Lean proof is **mechanically verified**, never a resolved problem. Keep `claimEligible=false`
  until independent human review; never describe a reconstruction of a published result as new mathematics.
- Record assistance. Operator-supplied notes, a supplied proof route, a recovered sandbox, a model switch —
  all of it goes in the run report. A result nobody can reproduce unaided is not an autonomous solve.
- Report unavailable costs as unavailable, not as zero.
- Distinguish **open on erdosproblems.com** from **untried by the harness**. They are not the same target
  class, and confusing them wasted a full experiment cycle (see `experiments/atlas-top3/REPORT.md`).

## Reporting a finished run — one line, any driver

Every `harness.py run` ends by printing a single greppable line and writing it to
`<run_dir>/SUMMARY.line` and `runs/summary-log.tsv`:

```
RUN-SUMMARY problem=677 exit=3 outcome=running directions=pos:infrastructure_error,neg:running \
  verified=None spend=$8.07 llm_calls=19 lean_checks=42 lemmas=5 fatals=2 wall=60m mode=research dir=runs/...
```

It fires on the fatal path too (a `finally`), so a crashed run still reports. Spend includes the
research-program sub-runs that live under `programs/erdos_<n>/`, and unknown cost prints as
`unavailable`, never `$0`. `outcome` is read from THIS run only — sub-runs log their own
`run/end outcome=proved` for a certified lemma, and counting those would report an open problem as
proved (regression-tested in `tests/test_run_summary.py`).

**So a background watcher never needs to parse `log.jsonl`.** Whatever is driving the lane — Codex,
Claude Code, cron, a plain shell — report a finished run with one line:

```bash
tail -1 <run_dir>/SUMMARY.line          # or: grep RUN-SUMMARY <lane.log> | tail -1
python3 harness.py summary --problem 677   # reprint for the latest run, any time
```

`summary` is a **read-only reprint**; it takes the exit code from the run's own `DONE` and will not
overwrite `SUMMARY.line` unless you pass `--write`. Do not have a watcher re-derive the exit code and
pass `--exit-code`: one did, read `$?` after a command substitution (which resets it), and rewrote a
crashed open-problem run as `exit=0` — proved-and-verified in this harness's exit-code convention. In a
lane script capture `EX=$?` on the very next line after the command, or just read `SUMMARY.line`.

Keep watchers to ONE per lane and let the harness do the summarising; polling the log and echoing
30 lines per check is what this replaced.

## --run-budget is a real cap; keep it that way

`spent_usd()` counts this run's own log **plus** every descendant: `--open` pos/neg children (under
`run_dir`) and research-program sub-runs (under `programs/erdos_<n>/`, filtered to this run's window).
It used to read only its own log file, so in `research`/`--open` — the modes that spend most — the cap
was unenforceable: a resumed #677 spent **$22.67 against `--run-budget 8`** before it was noticed and
killed by hand. Sub-run budgets are now `min(remaining, remaining/n)` and the cycle stops when the
parent budget is gone; the old `max(3.0, ...)` floor guaranteed $3 per sub-run with nothing left.
Covered by `tests/test_budget_accounting.py`.

Practical: `--open` halves the budget per direction, and each direction then runs its own research
program. Budget the whole thing, not one lane, and check `harness.py summary --problem N` mid-run.

## Every run writes a plain-language brief — that is how the Atlas explains itself

`stage_brief` runs at the end of EVERY run (proved, partial, not proved, or crashed) and writes
`atlas-data/briefs/<n>.md`, which the ranker folds into `rankings.json` and the site's `data.json`, and
`result_feed.py` publishes on the same 30-second channel as score revisions. The problem page renders it
under "In plain language". Regenerate one any time:

```bash
python3 harness.py brief --problem 273              # from that problem's latest run
python3 atlas-data/record_finding.py --problem 273 --brief path.md   # or write one by hand
```

The brief is fact-pinned: facts come from `collect_run_facts` plus the problem's `reviewed.json` entry
(labelled as **not** from this run), never from the model's memory. Four fixed sections — what the problem
asks / what we tried / what we found / what would move it — a machine-readable front matter repeating the
hard numbers, and rules that forbid claiming a resolution and require explaining each term on first use.
Briefs are written for a reader with no mathematics and for the next AI that opens the page.

## Facts about a run come from the whole tree, never from one state.json

`collect_run_facts(run_dir, pid)` is the single source: it walks child logs, `pos`/`neg` child state,
research sub-runs under `programs/erdos_<n>/` (windowed to this run) and partial-result directories a crash
never recorded. Reading the parent's `state.json` alone produced three separate wrong reports — spend
under-counted, an open problem shown as `exit=0` (proved), and a brief announcing "zero certified results"
for a run holding seven. **When a stage fans out, its read-side aggregate must fan out too.**

## Prefer a decision procedure to a hand-written search

`python-sat` (CaDiCaL) is available to search scripts and on the allowlist. Search scripts run under
`python -I`, which hides the user site directory, so `_run_py` injects the solver path on the command line
— do not relax the isolation flag. For "does a finite object with these properties exist?" (covering
systems, colourings, hypergraphs, Sidon sets, exact covers, designs) state it as constraints: a hand-rolled
DFS explores ~10^6-10^7 nodes and then times out, whereas UNSAT is a *proof* of non-existence in the encoded
range. #273's search aborted on a timer one step below its first real candidate; that is the failure mode
this replaces. It is not a magic wand — #273 at lcm 55,440 (212k vars) was still undecided after 75 min —
but the harness can now attempt the class at all.

## Reductions before search — and every reduction is checked

`stage_reduce` runs after triage, before construct/research/search (`--reduce auto|off|always`, auto = on
unless triage routed `fast`). It asks for structural facts that change the *shape* of the problem — parity
and congruence restrictions, symmetry quotients, substitutions, forced components, decompositions, known
equivalent forms — and then **empirically checks each one** in the sandbox: the proposal must ship a script
that prints `REDUCTION-OK`, or it is recorded as `refuted` / `check_failed` / `unchecked` and never
propagates. Only checked claims reach the search and proof prompts, via `reduction_context()`.

Why the checking is not optional: a reduction travels downstream **as fact**. A wrong one is worse than
none. The stage exists because #273's decisive fact — every admissible modulus `p-1` is even, so the
classes split by parity and a covering system must contain *two disjoint* covering systems — was found by a
human reading the problem, and would have reshaped both the search and the proof.

## Stalled search escalates to a decision procedure; it does not stop on a timer

`escalate_search` fires when a bounded search found nothing AND it stalled — timed out, burned its wall
clock, or only cleared its range with a `screen`. It re-asks for a SAT encoding that DECIDES the first
undecided case, with `--search-escalate-seconds` (default 900). Needs a solver; `--search-escalate off`
disables it.

The escalation supersedes the first attempt only where it learned more: a witness, or a genuinely
`exhaustive` range. An undecided solver run leaves the original floor standing rather than overwriting it
with a weaker claim. This is the #273 failure mode directly: the screen cleared every lcm below 55,440 in
18 seconds, reached the first candidate that could host a covering system, and quit on a timer.

## The frozen statement's readings are part of the result

`record_readings` runs at freeze time and records every convention the formal statement commits to that the
published sentence does not state: omitted conventions (distinctness, non-triviality, strictness), domain
choices (ℕ vs ℤ, truncated subtraction), resolved ambiguities, added or dropped hypotheses. Each is
classified `essential` / `conventional` / `risky` / `unclassified`, and a `risky` one gets its own
`formalize/reading_risk` event — that is the flag a human should read first. They appear in the run report
and in the brief. A proof is about the frozen statement, not the English sentence: #273's requires DISTINCT
moduli (necessary — without it `{0,1,2,3} mod 4` is trivial — and standard, but a reading), and a human
noticed it rather than the harness reporting it.

## One sandbox runner

`sandbox_argv(script)` builds the command line for every model-written script. It keeps `-I` and names the
solver's site directory explicitly, because `-I` hides the user site where `pysat` lives. Any stage that
runs model-written Python must go through it — `stage_search` had its own bare `-I` call and would have
failed every `import pysat` the allowlist promises. `tests/test_reduce_escalate_readings.py` asserts there
are exactly two such invocations in the file, both inside the helper.

## Order candidate cases by constraint, not by size

When a necessary condition screens candidate cases, compute its **slack** per survivor — how much of the
budget may go unused — and attack **least slack first**. Tight slack forces structure: most of the object
is determined before any search, so a *larger* case can be decidable where a smaller one is hopeless.
Anything the condition forces belongs outside the hard search, asserted or enumerated.

#273 cost three attempts to learn this. 29 candidate lcms survive the reciprocal screen. L=55,440 is the
smallest and was attacked three times for that reason — slack 0.0437, 7 of its 43 moduli forced, 36 free;
four solver runs timed out. L=100,800 has slack 0.000089, **45 of 50 moduli forced and 5 free**, so its
subset choice collapses to 12 enumerable cases and leaves the solver entirely — and 2 of those 12 die to
Mirsky–Newman (no exact covering system with distinct moduli) without any search at all.

Both `SEARCH_PROMPT` and the escalation carry the rule with those numbers, and a search that enumerates
cases must print `CANDIDATES: {"order_by": ..., "cases": [[case, slack], ...]}` in attack order, which is
logged as `search/candidate_order`. Prose guidance was read past twice in this codebase; report it or it
did not happen.

## A search floor must say how it was obtained

`exhaustive` (every candidate tested, including a solver UNSAT) / `screen` (excluded by a cheap arithmetic
filter) / `published` (third-party, not rerun) / `unrecorded`. The search script must return `kind` in its
`SEARCHED:` payload; `record_finding.py` takes `--floor-kind`. A screen reported as a search is a false claim
of progress: #273's `exhaustive_to: 55439` is a screen, and is one below where the real work starts.

## Gotchas

- `erdosproblems.com` 403s WebFetch; plain `curl -A "Mozilla/5.0"` works. The site's `/forum/thread/<n>` and
  its proof-claims page carry decisive information the main page does not — read them before attacking.
- The site's `falsifiable` / `verifiable` / `decidable` classes promise a finite witness, **not a reachable
  one**. Check for a search floor first.
- `native_decide` is banned in proofs. Kernel `decide` has timed out at 420 s on a 3,003-case check, so
  finite certificates must be small or Bool-reflected.
- macOS has no `timeout` binary; use a perl alarm.
- Pace model runs in ONE lane. Spend limits are a hard failure that stops a lane with exit 1, and runs are
  resumable with `--resume`.
