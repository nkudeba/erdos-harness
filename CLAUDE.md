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
at triage time — from `problems/erdos_<n>.json` when that file exists, and otherwise straight from
`reviewed.json` via `atlas_search_floor` — and skips a futile search stage without spending a model call.
File it in enumerable-object units, not the problem's own parameter; see the floor section below.

**The live site picks these up on its own.** Revised scores ride the same 30-second channel as run evidence:
`result_feed.py` publishes every reviewed problem's score, reasons and requirements to `/api/results`, and
the page overlays them on its baked snapshot, re-sorting ranks and recomputing tiers. So recording a finding
is the whole job — no rebuild, no redeploy. `.result-feed/status.json` shows `revised_scores` (accepted) and
`pending_scores` (queued). If `pending_scores` stays non-zero, the deployed build predates live rankings and
the site needs one redeploy; the publisher keeps run evidence flowing meanwhile and starts sending scores by
itself once the new build is up.

## The scores are not probabilities, and there is now a way to get some

`score` is a sum of hand-assigned points; `partial` likewise. Neither has ever been checked against an
outcome, so neither is a probability — score 12 does not mean 12%. `rankings.json` says so in its own
metadata. Read them as an ordering device and as tiers (`≥70` Promising, `≥50` Plausible, `≥30`
Difficult, `≥15` Research, below that Frontier).

To get real probabilities you need predictions recorded BEFORE outcomes. The project had 26 settled
attempts and zero predictions, making all of that evidence unusable for calibration. Now:

```bash
python3 atlas-data/predict.py estimate --problem 273    # decomposed ceiling, no model calls
python3 atlas-data/predict.py estimate --all --nonzero  # whole catalogue, ~0.2 s, still free
python3 atlas-data/predict.py record --problem N --p-resolve 0.001 --basis "why"
python3 atlas-data/predict.py score                     # Brier + calibration bins, once outcomes land
```

`stage_assess` logs a prediction to `atlas-data/predictions.jsonl` on every run, so the log fills by
itself. Calibration stays impossible until outcomes accumulate, and `score` reports that honestly
instead of printing a flattering Brier.

**A prediction is settled by the attempt it was made for, never by the problem's current status.** A
harness row names its run (`by: triage/<run>`); any other row is settled by the first run of that problem
that started after it; the outcome is that run's `DONE` (exit 0 = proved and verified; a fatal `DONE` stays
unsettled; benchmark runs never settle anything). Scoring by current status used to settle a write-ahead
prediction at once from an older attempt, and would flip a failed attempt to a success when a later run
solved the problem. When every settled outcome is the same, `score` prints no Brier at all (six p≈0
predictions of six failures printed a "perfect" 0.0000); otherwise it prints the base-rate reference and a
skill score beside it. Benchmark predictions go in `benchmarks/deductive/RESULTS.md`, written before launch.

**The estimate is a decomposition, not an opinion:**
`P(resolve) = reachability × class base rate`. Reachability is *arithmetic* — a recorded search floor
past the bounded-search reach (`10^9`) pins it to 0 whatever else is true — which is why the whole
catalogue costs nothing to triage. The class rate comes from observed outcomes under a Jeffreys prior,
so `0/7` gives a small positive number rather than a false zero.

Two refusals are deliberate. Nothing is ever labelled `calibrated`. And an **already-solved problem
nobody has attempted gets no estimate at all**: the 19/19 reconstruction rate was earned on targets
chosen for being reconstructable, and applying it to an untouched problem would launder that selection
into a prediction.

**What it says today:** of 639 open problems, **602 pin to exactly 0** by reachability alone, and 37
survive — all at the same 0.0625 class rate, differing only in `partial`. That is the honest picture:
the ceiling barely discriminates, so `partial` remains the axis that decides where budget goes.

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
`run_dir`) and research-program sub-runs (under `programs/erdos_<n>/`, **attributed by ownership**: every
program child records `owner_runs`, its spawner plus the spawner's owners, so a resumed older run is never
charged a newer run's sub-runs; sub-runs that predate the marker fall back to the window
[this run's start, the next run's start)). Attribution by time alone would have charged the first masked
#275 run, resumed, $23.74 against a true $8.05.
It used to read only its own log file, so in `research`/`--open` — the modes that spend most — the cap
was unenforceable: a resumed #677 spent **$22.67 against `--run-budget 8`** before it was noticed and
killed by hand. Sub-run budgets are now `min(remaining, remaining/n)` and the cycle stops when the
parent budget is gone; the old `max(3.0, ...)` floor guaranteed $3 per sub-run with nothing left.
Covered by `tests/test_budget_accounting.py`.

Practical: `--open` halves the budget per direction, and each direction then runs its own research
program. Budget the whole thing, not one lane, and check `harness.py summary --problem N` mid-run.

The cap is enforced BEFORE every model call, never right after one (a paid response was being thrown away
uncompiled), and **each call is capped at what the run has left**: the per-call cap (`--call-budget`, $8) used to
apply unchanged with $4 remaining, so one prove call overshot a $15 run to $16.11. A call is never capped below
$0.50.

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
research sub-runs under `programs/erdos_<n>/` (attributed by `owner_runs`, as `spent_usd` is) and partial-result directories a crash
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
of progress: #273's old `exhaustive_to: 55439` was a screen, one below where the real work starts. It is now
`110880` / `exhaustive`, by algebra rather than enumeration — see `knowledge/reductions/273/`.

**And it must be filed in units the gate can compare.** `search_futility` measures a floor against
`SEARCH_REACH = 1e9`, which counts *objects a bounded search can enumerate*. A floor filed in the problem's
own parameter — `n = 32` vertices, `n = 12`, `62` — reads as a trivially cheap search and lets the stage run,
which is exactly backwards: #993's `n <= 32` is 1.1e11 trees and #743's `n <= 12` is 1.07e10 tree families.
File the object count and say so in the rationale. Where no object count is meaningful because each candidate
is itself a hard decision (#273 and #7 file an lcm), the floor will not trip the gate at all — put the reason
in a `--requirement` instead of inflating the number.

**The loop only closes if the harness can see the floor.** `record_finding.py` stamps
`problems/erdos_<n>.json` only when that file already exists, which is true for the ~40 problems the harness
has attacked. `search_futility` therefore also reads `atlas-data/reviewed.json` directly
(`atlas_search_floor`), because it previously read the problem file alone — leaving #366 (1e22), #287 (4e19),
#647 (9.2e18) and #848 (2.6e17) recorded and *inert*, every one of them still free to spend a search stage
re-deriving a known check. Covered by `tests/test_atlas_floor_loop.py`.

## Prefer a cheap necessary condition to a solver call

A residue-free algebraic test can decide in milliseconds what a SAT encoding does not decide in 37 minutes.
#273: the fibre/Fourier condition — group ℤ/L by residue mod `d`, note that moduli not divisible by `d`
cancel, so the imbalance must be paid out of the overlap `k` — eliminated **20 of the 29** candidate lcm
values, including both candidates that had absorbed five attempts and four solver timeouts. Ask what the
structure forces before asking a solver to search.

Two riders, both learned the same day. **Check the forum first anyway**: the identical test transferred
verbatim to #7 and reproduced a floor ~3,300× weaker than one already posted there, so it banked nothing.
And **the algebra eats exactly the candidates a search wants**: it bites when slack is tiny, which is the
same property that makes a candidate look attackable, so success here can leave the target *less* tractable
than before — say so plainly rather than reporting the eliminations alone.

## Cluster libraries — import the machinery, never re-derive it

The catalogue clusters hard (22 covering-system problems, 67 Ramsey, 22 Sidon), and until now every run
started from near zero: only Lean tactics accumulated. `CLUSTER_LIBRARIES` in `harness.py` maps a problem
TAG to a formalised Lean module; a problem carrying the tag gets the module added to its import header and
named — **names only, never bodies** — in the reduce/prove/agentic prompts, so the model reuses certified
results by name instead of re-deriving them.

```
covering systems -> Formal.Library.CoveringSystems
```

`Formal/Library/CoveringSystems.lean` holds the density bound, the pool/reciprocal screen, the finite form
of the generating-function identity, the root-of-unity condition (`‖Σ_{r∈E} ζʳ‖ = L/m` at a
divisibility-maximal `m`, hence `L/m ≤ k`), Mirsky–Newman / Davenport–Rado, and the #273 facts earlier runs
certified — all sorry-free on `[propext, Classical.choice, Quot.sound]`.

Rules for adding a cluster:

- The module must **build sorry-free** before it goes in the table. `Harness._ensure_library` runs
  `lake build <module>` at run start and **drops** a module that will not build, because `import` of an
  unbuilt module is a hard Lean error that would fail every check in the cluster, not just the attempt
  that wanted the library.
- Never paste lemma text into a prompt. The header already imports the module; the prompt block lists
  declaration names and tells the model to `#check` one for a signature.
- Mirsky–Newman is a **published theorem** (1950). A library entry reconstructing published mathematics
  says so in its own docstring; the module is mechanically verified, never new mathematics.
- Mathlib v4.32.0-rc1 has **no** `CoveringSystem` / `StrictCoveringSystem` — those live in
  `google-deepmind/formal-conjectures`, not Mathlib. `CongruenceFamily` is defined in the module, shaped so
  a `StrictCoveringSystem` is the case `Covers ∧ DistinctModuli`.

Covered by `tests/test_cluster_library.py`.

## Gotchas

- **Model: `claude-opus-5-5`, never Opus 5.** `DEFAULT_CLAUDE_MODEL` in `harness.py` is what the claude-cli
  backend uses when `--model` is omitted; `prepare.py`/`probe.py` default to the same. Never let a call fall
  through to the `claude` CLI's own default: on this account that is Fable, which hits a usage limit long
  before Opus and kills a run at the first stage with exit 1 after ~$0.002. Runs before 2026-09-23 (all
  recorded baselines, and the first three sessions of masked #275) used `claude-opus-5`, so comparing against
  them is a model switch — record it. Each resume logs its model in `state["invocations"]`.
- **Model calls see no ambient context.** Every `claude -p` call passes `--setting-sources ""`, which loads no
  settings and stops CLAUDE.md discovery. Until 2026-09-23 every call saw THIS file and the operator's global
  CLAUDE.md, i.e. a list of benchmark problems, the theorems behind them, and "masked #275" beside
  `erdos_80317`: no masked benchmark or recall probe before that date was blind. Never drop the flag; never
  write a benchmark's alias id next to its true number in a file a model call could load.
- `erdosproblems.com` 403s WebFetch; plain `curl -A "Mozilla/5.0"` works. The site's `/forum/thread/<n>` and
  its proof-claims page carry decisive information the main page does not — read them before attacking.
- The site's `falsifiable` / `verifiable` / `decidable` classes promise a finite witness, **not a reachable
  one**. Check for a search floor first.
- `native_decide` is banned in proofs. Kernel `decide` has timed out at 420 s on a 3,003-case check, so
  finite certificates must be small or Bool-reflected.
- macOS has no `timeout` binary; use a perl alarm.
- Pace model runs in ONE lane. This is a **spend-pacing** rule, not a correctness one: the account's usage
  limit is the shared resource, and hitting it is a hard failure that stops a lane with exit 1 (runs are
  resumable with `--resume`). Concurrent runs do not corrupt each other — audited 2026-09-11: each run's
  Lean attempts are written inside its own `run_dir`, `lake env lean` only reads `.lake/build`, `lake build`
  is reached only via a cluster library or `--allow-research` and its module names carry problem id +
  direction, `runs/current` is swapped atomically, and `--open` already runs both directions at once by
  design. So a second lane is a budget decision, not a data-safety one; check what is live with
  `pgrep -f "harness.py run"` and budget the total, not the lane.

## The Atlas is written under a lock — keep it that way

`record_finding.py` used to mutate `atlas-data/reviewed.json` with a bare read-modify-write. Two agents
recording findings for DIFFERENT problems at once each read the same dict and the second write silently
erased the first — both printing success — and because `write_text` truncates first, an interrupted write
left the Atlas's memory of every assessed problem unparseable, which `load()` then reads as `{}`.

`atlas-data/atomic.py` fixes both: `locked(path)` holds an exclusive `flock` across the whole
read-modify-write (locking only the write still loses updates — the stale *read* is the bug), and
`atomic_write` renames a fully-written temp file over the target so a reader sees the old file or the new
one, never a half-written one. The lock lives on a sibling `.<name>.lock` because `os.replace` would
otherwise drop a lock held on the replaced inode. The rerank subprocess runs **outside** the lock.

Any new writer of a shared Atlas file must go through these helpers. Covered by
`tests/test_atlas_concurrency.py`.

## The research program is deductive by default — the residual is the artifact

`--mode research --allow-research` now runs the **deductive loop** (`--research-loop deductive`, the
default; `lemma` keeps the old experiments → conjecture-ledger → sub-lemmas loop for comparison). Its unit
of progress is a **certified conditional theorem**, kept as `programs/erdos_<n>/Residual.lean`: optional
`def`s, hypothesis lemmas `theorem erdos_<n>_hyp_<x> : <closed Prop> := by sorry`, and the frozen theorem
proved from them by glue with **no `sorry` of its own**. The open hypotheses ARE the residual. A cycle is:

1. **Refute first.** A model-written script (`EXPERIMENTS_PROMPT`) tries to break every open hypothesis on
   small cases and near-miss families and prints `REFUTED:`/`CLEAR:`/`INVARIANT:` lines — never a
   percentage. An exact witness against a hypothesis kills the skeleton in force and is banked under
   `knowledge/refuted/<n>/` (labelled *numerical, not Lean-certified*); refuted statements are fed back so
   no plan re-proposes them in any disguise, and `_consider_skeleton` rejects one that does.
2. **Plan = skeleton.** `PLAN_PROMPT` demands the skeleton plus a JSON ledger tagging each hypothesis
   `conjecture` (with a *derivation*, not a support rate) or `published` (with `-- PUBLISHED: <citation>`;
   a published tag without a source is downgraded to a conjecture). Published theorems enter **as
   hypotheses, never as `axiom`** — the audit stays `[propext, Classical.choice, Quot.sound]` and the trust
   boundary sits in the theorem's signature. Provenance goes to `premises.jsonl`.
   **A published premise may not be the target in disguise** (`_circular_premise`). The masked #275 run closed
   its residual with a premise tagged `PUBLISHED: Crittenden–Vanden Eynden 1970` that was the frozen theorem
   translated by `t`: it compiled on the standard axioms with every `sorry` inside a hypothesis, so every gate
   passed and the target was proved from itself. Every open published premise is now checked against the
   skeleton's own target AND the root target (`root_frozen`, passed to children, because that premise entered
   one level down): first Lean tries `premise → target` with free tactics (catches restatements), then one
   `circularity` judge call asks whether the target follows by routine steps (catches translations,
   specialisations, contrapositives). A missing verdict rejects. If a needed result is in Mathlib (Hindman for
   #532), the model must use the Mathlib theorem by name; it is certified and not a premise.
3. **Adopt only if real and better.** Frozen theorem verbatim, no banned construct, every `sorry` inside a
   hypothesis, nothing refuted, compiles; the free specialist cascade gets a go at the holes; then
   `residual_improves`: the HARDEST open conjecture must get easier first (max complexity), then fewer open
   conjectures, then fewer published premises, then lower total complexity. Count-first was tried and lost
   on the #645 benchmark: the first skeleton reduced the target to ONE compactness hypothesis exactly as
   hard as the target, and a count-first rule would have refused the four-lemma structural route the
   reference proof uses. A skeleton with no hole left is a proof and goes through `stage_verify`.
4. **Attack only the residual.** Open conjecture hypotheses are attacked easiest-first as closed
   sub-statements: the plan rates each one `elementary` / `moderate` / `hard` in its JSON ledger and that
   rating orders the attack before syntactic complexity (complexity alone sent the masked #275 run at its
   own "genuinely open residual" first, because it had the shortest statement). `--hyps-per-cycle` caps the
   count and `--min-child-budget` (default $2.50) refuses to start a child it cannot fund, deferring the
   rest with a `hypotheses_deferred` event: three children at $1.32 each all died after one $1.33 prove
   call with nothing compiled. Budget a deductive run at roughly $4 for reduce, refute and plan plus $2.50
   per hypothesis you expect to attack. A certified one is spliced back
   (`splice_hypothesis`: proof in `<name>_ns`, hypothesis becomes `exact <name>_ns.<name>`) and the residual
   shrinks. `Lemmas.lean` still accumulates the certified proofs as an importable module.
5. **Learn from failures, grow in depth.** A child that fails leaves a *failure digest* (unsolved goals,
   best attempts' errors, the prover's own diagnosis) in `failures.jsonl`; the next plan sees it under
   PROOF FAILURES and must answer with one of four moves — `lemma` (state the missing fact as a new
   hypothesis), `split`, `define` (name the recurring structure and restate in terms of it: that is how a
   concept like U(i) enters, from a failed proof), or `defer` (rate it hard) — recorded in `moves.jsonl`.
   A hypothesis that failed once, or is rated hard, is attacked with its OWN skeleton one level down
   (`--residual-depth`, default 2; sub-residuals live in `programs/erdos_<n>/sub/<name>/`); a child that
   certifies `hypothesis <= sub-hypotheses` without closing them is spliced in as a REFINEMENT, so the
   parent's frontier becomes the simpler pieces. Invariant extraction is derive-first: the script prints a
   `DERIVATION:` before each `INVARIANT:`, and a pattern it cannot derive is `OBSERVED:`, never a hypothesis.
   **The frozen guard matches each frozen declaration separately.** A research child freezes `def`s + a
   hypothesis theorem, and a skeleton puts hypothesis lemmas between its `def`s and the target, so a guard that
   demanded the frozen text as ONE contiguous block rejected every proof with a helper between the defs and the
   theorem and every sub-residual skeleton. On the funded masked #275 run it threw away two sorry-free,
   standard-axiom proofs of the descent lemma unread ($4.53) — `contains_frozen` now requires every frozen
   declaration verbatim but not contiguous (`contains_frozen_contiguous` remains for the layout repair), rejected
   attempts keep their code and name the missing declaration, and a rejected skeleton is itself a `skeleton`
   failure the next plan must fix first.
6. **Render.** `RESIDUAL.md` (hypotheses by kind, refuted list, proof failures and the moves made),
   `campaign.json` (the argument as a DAG:
   `conjecture` nodes the target is `conditional_on`; `harness.py campaign residual --manifest …` reports
   it), `state["residual"]`, and `residual=open:k,published:p,certified:c` on the `RUN-SUMMARY` line.
   `record_finding.py --residual '<json>'` files it in the Atlas with a history so shrinkage is visible.

**Progress is a discharge, not a split (Step 2, 2026-09-23).** A cycle counts as progress only if it discharged
something: a spliced proof, a refinement in which the child certified at least one of its sub-hypotheses, or an
adopted skeleton with fewer open conjectures (the first skeleton counts). A refinement that discharges nothing is
NOT spliced (`split_only_refinement`), because splitting can make the frontier harder: #242's negation turned "a
counterexample exists" into the stronger "a counterexample exists in the quadratic-residue classes". Its
decomposition goes to the next plan as a failure digest instead. `STALL_LIMIT` (2) consecutive cycles without a
discharge stop the program (`descent_stalled`, reason in `stop_reason`); the count lives in `state["stall_cycles"]`
and survives resumes.

**A refinement is spliced only if its open pieces are strictly easier** (`_refinement_not_easier`). Discharging a
piece is not enough when the piece is the trivial direction: #242's last step certified "a type II certificate gives a
representation" and left open "every hard prime has one", the same core in certificate form. A free Lean layer refuses
an open piece that is equivalent to the old hypothesis in BOTH directions by routine tactics (one direction proves
nothing: any hypothesis implies its own subcases, which is what a real reduction leaves open); then one `refinement`
judge call decides "strictly easier" vs "restatement or harder". Checked on #242's two real refinements: the Mordell
step judged easier, the type-II step judged not easier. No verdict means no splice (`refinement_not_easier`).

**Two directions (`--open`) compose with the deductive loop** — decided and tested 2026-09-23 on masked #16. Each
direction runs its own program (`erdos_N_neg_hyp_*` names parse; sub-runs keep their direction via
`open_direction_of`, so directories, modules and budgets stay separate). The failure mode is a false direction
eating the budget: on #16 the negation's plan knew its target was false and still spent 70% of the run. The plan
now reports `target_belief` and per-hypothesis `believed_false`; `target_belief: "false"` stops that direction
(`target_believed_false` event, reason in `stop_reason`), and a believed-false hypothesis is never attacked. Each
direction starts with its own prior spend plus half of what is left (`_fund_direction`; without the prior spend a
resumed direction could start below what it had already spent and stop at once, as #242's productive side did); when one ends, `_hand_over_budget` gives the other its own spend plus
the whole run's remainder (a `budget_handover` event), so a direction that stops early no longer strands its half.

`stage_reduce` now asks for a Lean statement beside each check; a checked reduction the cascade closes is
`certified` and so labelled in prompts, one that only type-checks is `stated` and carried "as a hypothesis,
not a fact". Nothing about the honesty gates changed: a closed skeleton is *mechanically verified*, never a
resolution; `claimEligible=false` until human review. Design and acceptance test:
`docs/deductive-research-mode.md`. Covered by `tests/test_deductive_mode.py`.

**Benchmark it on solved problems before trusting it on open ones.** `benchmarks/deductive/prepare.py
--problem 645 --launch` re-derives a saved solve BLIND (resolution notes withheld) under `--benchmark`, which never
writes `knowledge/solved`, harvests no lemmas and writes no brief. The README there classifies the 19 saved
proofs: eight are deductive arguments (645, 275, 499, 532, 350, 476, 649, 16) and are the test set; the
certificate ones (674, 493, 399, 316, 105) are not deductive benchmarks. Judge by `RESIDUAL.md`, never `lemmas=`.

**Two contamination paths, learned on the first run.** The lemma store `knowledge/lemmas.jsonl` is harvested
from every verified proof and fed to provers as "helper fragments", so on #645 the child was handed the
reference proof; `--benchmark` now excludes it. The model's own memory of public solutions cannot be excluded,
only cued less and measured: `prepare.py --masked` (synthetic id, paraphrase, renamed theorem, no tags, `--masked`
prompt scrub) plus `probe.py` before and `compare.py` after. A closed masked run is evidence about the loop only
when the probe showed no recognition and the route differs from the reference.

## Current research guidance reaches the model

Store concise operator next steps in `atlas-data/research-guidance/<id>.md`, and link the file from an Atlas finding. The harness reloads this file for assessment, reduction, experiments, planning, ordinary and agentic proving, refinement, decomposition, criticism, search and construction. It applies to fresh runs, resumed checkpoints and research children without modifying the frozen problem input. Guidance is labelled unverified operator context, logged with its source and hash, and preserved in the actual prompt transcript (also TASK.md for agentic attempts). It is excluded from formalization and blind verification prompts. Record new results, open obligations and refuted routes with explicit status; do not promote a draft or numerical check into a proved premise.
