# erdos-harness — working instructions

LLM + Lean 4 harness for Erdős problems. `harness.py` is the pipeline, `formal/` is the Lean project,
`runs/<ts>-erdos<N>/` holds every run, `knowledge/solved/` holds verified proofs, `atlas-data/` holds the
feasibility ranking of the whole 1,217-problem catalogue.

## Keep the Atlas current — do this as you learn, not at the end

**It now keeps itself current too.** The publisher LaunchAgent re-ranks on any change, commits and pushes
`atlas-data/`, and puts the Atlas live (`atlas_refresh.py`, `docs/live-results.md`). Benchmark runs are attributed to
their catalogue number through `atlas_ids.py`, as status only. What still needs you is the qualitative half below.

**The live Atlas is the encrypted GitHub Pages site** (2026-10-01): https://nkudeba.github.io/erdos-atlas-site/.
- The passphrase is in `.result-feed/pages-passphrase`, and nothing should ever print or commit it.
- `atlas_pages.py` rebuilds, encrypts and pushes it at most every 10 minutes when anything changed.
- ChatGPT Sites deploys only from the ChatGPT app (no CLI, API or git hook). Its source repository, `erdos-atlas`, is
  kept current but goes live there only when someone deploys it by hand.

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
is the whole job — no rebuild, no redeploy. The Pages site gets the same data with its next deploy, within about
10 minutes. `.result-feed/status.json` shows `revised_scores` (accepted) and
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

- A compiling Lean proof is **mechanically verified**, never a resolved problem by itself. Whether it can be
  trusted without anyone reading it is decided by `python3 audit.py --run <run_dir>` (no model calls, about 90 s),
  which writes `AUDIT.md` and `AUDIT.json` into the run. It checks:
  - a kernel replay with `leanchecker`;
  - exactly the standard axioms;
  - no `sorry`, kernel bypass or elaboration-time code;
  - trusted imports;
  - that the proved constant's **elaborated type** is structurally identical to a clean elaboration of the frozen
    statement.

  When `tools/install.sh` has been run, the audit adds two independent checks, the way openai/math verifies its 405 Lean
  results:
  - `comparator` (leanprover/comparator): the proof must match a separately written challenge statement, definitions
    included, on the permitted axioms, through the Lean kernel;
  - `nanoda`: the same proof through an independent kernel.

  macOS has no Landlock, so Comparator runs without its sandbox (the repo's fake-landrun shim), and each audit says so.
  #1125 passes both, and the redefined-`<` attack fails Comparator (`tests/test_audit.py`).

  **Comparator gets no definition holes** (fixed 2026-10-14). It already requires every declaration the statement uses
  to match the challenge, the frozen definitions and structures included. A name in its `definition_names` is a HOLE
  that the proof may fill with any body of the same type.
  - The audit used to list the frozen definitions there. Their bodies escaped Comparator's comparison (only
    `statement_identity` compared them).
  - It also stopped Comparator on #769's `structure Cube` ("not a definition"), which left a closed proof
    `proved_unverified`.
  - `harness.py reverify --run R` re-runs final verification on a run's own proof after such a fix. It never searches
    for a proof, and it records itself in the run's `assistance`. `resolution.py reverify-lean --problem N` does the
    same for a campaign Lean stage and records the outcome as the loop would.

  The last check is new, and it is not optional. The harness's own final check compares TEXT, and a redefined `<`
  lets a file prove `(3 : ℕ) < 2` with the frozen text verbatim, no `sorry` and no axioms. `tests/test_audit.py`
  shows that attack passing every text check and failing the audit.
  - **Problems already resolved in the literature** (every time-split item): an audit PASS is the verification,
    and no human review is needed to call the proof verified. It is still a reconstruction of a published result,
    never new mathematics.
  - **Problems open on erdosproblems.com:** the audit is necessary but not sufficient. A claim of resolution also
    needs independent human review, because our own formalization of an open statement has no external check.
    `claimEligible` stays false until then.
  - Faithfulness of the frozen statement rests on its provenance, which the audit records: formal-conjectures for
    time-split items, plus the faithfulness judges.
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

**A deductive run may fund itself, by a rule set before it starts** (`--budget-extend STEP --budget-extend-max CAP`, off
by default):
- When a cycle runs out of money and it, or the cycle before, discharged a step, the budget grows by STEP from the
  spend, never past CAP. The last step is clamped to CAP, not refused: a full step would have taken #152's run from
  $63 to $73 against a $70 cap and left the last $7 unspent. Under $1 of room is refused.
- That includes a cycle too poor to fund a child, not only one that hits the cap. When steps would be deferred for
  `--min-child-budget`, the extension fires before they are. Until 2026-10-06 it fired only on a hard budget stop:
  #152's whole-problem run deferred all four open steps two cycles running ($1.21, then $0.14 left). Those starved
  cycles counted as a stall and ended it at $30.34 under a $70 cap.
- A cycle that ran dry without a discharge counts toward the stall limit. A child that came back with certified
  pieces the parent had not yet banked counts as a discharge, for both the stall count and the extension.
  #152's resumed run stopped at the refinement judge's budget check, right after its `split_ne` child proved 7 of
  8 pieces. A resumed run starts with no record of earlier progress, so it was refused the extension (2026-10-06).
- Each extension is logged (`program/budget_extended`) and named in the stop reason.
- #435's hard step needed three hand-raised budgets; this rule replaces them.

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
- **A killed run takes its model sessions with it.** Every `claude -p` call goes through `run_tracked`. SIGTERM and
  SIGHUP terminate the tracked sessions, then the run (`terminate_children`). Killing a run used to leave its in-flight
  sessions running and billing as orphans (step 3's #120, 2026-10-07). Kill a run with plain `kill <pid>`, never
  `kill -9`, which skips the handler. A process-group kill would also take down the launcher, such as `screen.py`.
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
   shrinks. `Lemmas.lean` still accumulates the certified proofs as an importable module, keeping ONE block per
   hypothesis name, the newest (`lemma_blocks_deduped`). A re-plan that reused a name used to leave two
   `namespace <name>_ns` blocks. After that the module never built again, and no attempt could import a certified lemma
   (#152, 2026-10-06). For the same reason, the residual in force must contain the frozen statement, as an adopted
   skeleton must. Otherwise it is archived as `Residual.stale-*.lean`. A sub-residual lives in
   `sub/<hypothesis name>/`, and #152's re-stated `hyp_c6` kept loading its OLD closed skeleton. That skeleton had
   0 open steps, so it refused every new plan and never reported a proof.
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
not a fact". The statement is compiled under the frozen statement's own `def`s and `open`s (`reduction_source`). Until
2026-10-03 it was compiled alone, and 95 of 141 reductions on statements with `def`s died as `Unknown identifier`.
Nothing about the honesty gates changed: a closed skeleton is *mechanically verified*, never a
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

### Breadth before depth (2026-09-26)

Measured over every research-program log on disk: 79 steps were still open at the end of unsolved runs, and
51 of them (65%) were **never attacked** — most deferred for want of `--min-child-budget`. Of 152 hypothesis
children that DID prove their target, the median cost was $0.22 (66% <= $0.50, 74% <= $1.00), and of 278
`prove` SUCCESS events only 1 happened in round 3 or later (224 in round 1). The 86 that failed cost a median
$3.51 ($317.6 total) chasing extra rounds and decompose escalations that almost never paid off. So the loop
spent most of its money on long tails that rarely pay, while cheap one-shot attempts — which usually work —
were never even offered to most hypotheses.

**Change A**, `--sweep {on,off}`, **default `off`**; `--sweep-budget` USD per attempt, default 0.6; `--sweep-max`
attempts per cycle, default 8:
- Before core-first, the per-cycle cap and min-child-budget narrow the field, `_sweep_cycle` gives every open
  conjecture hypothesis one cheap one-shot try: `_attack_substatement(..., cheap=True)`, one round, no agentic, no
  decompose.
- A hit is banked exactly like a certified depth child (the shared `_bank_certified`, logged `via="sweep"`).
- A miss is recorded with `kind="sweep"` and excluded from `failure_counts`.
- Each hypothesis TEXT is swept at most once (`self.state["swept"]`).
- **Why it is off.** The pre-registered train replay gave the sweep's exact attempt to the 10 steps that runs left
  open and never attacked, and it proved **0 of 9** ($2.67; one replay crashed, one was unfair for want of the lemma
  module). The prediction was 3.
  - The runs' never-attacked steps are mostly the HARD ones: the attack order is easiest-first, so the $0.22 median
    of a *successful* attack was selection, not a property of the deferred steps.
  - Most misses compiled with `sorry` holes left: genuine difficulty, not formatting.
  - Turn it on only with a screen that shows otherwise.

**Cheap fallback**, `--cheap-fallback {on,off}`, **default `on`** (2026-09-30). This is the sweep's cheap attempt, aimed
where the evidence says it pays:
- After each cycle's depth attacks, every open step the depth phase did not fund gets ONE cheap one-shot attempt
  with what is left: steps deferred for `--min-child-budget` or beyond `--hyps-per-cycle`.
- Steps the plan rated **hard** are skipped.
- **Why:**
  - Train #678 certified 12 of 15 steps. Its last three were elementary counting lemmas, siblings of ones it had
    just proved, and they sat deferred with $2.44 unspent. The cheap attempt proved all three for $0.73, and the
    assembled proof passes the audit (`benchmarks/timesplit/evidence/678-assembled/`).
  - Deferred HARD steps went 0 of 5, and the plan's rating separates the two cases: hard 1 of 20 proved, elementary
    29 of 29.
- It shares the sweep's once-per-statement memory.
- `off` restores plain deferral.

**Change B**, `--attack-rounds` (default 2) / `--attack-decompose-rounds` (default 0): caps a normal (depth)
child's `rounds`/`decompose_rounds` in `_attack_substatement`, freeing the tail budget for the sweep and for
the next plan's response to the failure digest. `--attack-rounds 6 --attack-decompose-rounds 10` restores the
old caps. Recursive (sub-residual) children are uncapped here — they run their own deductive loop, and their
OWN hypothesis children get the same caps in turn.

**Change C**: `--refute` now defaults to `changed` (was `auto`), validated in the improvement loop's iteration 3:
it saved money at no measured cost. **`--premise-attack` is back to `full`** (2026-09-30).
- It went to `cheap` on 2026-09-26, on #997's evidence: its last open premise was BFT15, far beyond reach.
- But premises are attacked only once no conjecture is left. At that point a full attack spends money with no
  better use, and it is the only remaining path to a solve.
- On train #678 the fresh run closed every conjecture and kept Ramanujan's two-primes premise under `cheap`. A
  replayed full attack proved it for $3.22, and the assembled proof passes the audit
  (`benchmarks/timesplit/evidence/678-assembled-b/`).
- `--refute auto --premise-attack cheap` gives the other combinations.

**Premise endgame** (2026-09-30, on with `--premise-attack full`):
- Once every conjecture is certified and only published premises are open, a cycle skips the refutation script and
  the plan, and spends what is left on the premises.
- The last premise attack is funded with whatever remains, at least $1, rather than deferred for
  `--min-child-budget`.
- Train #678's third run certified all 8 conjectures with $2.70 left. It spent that on two re-plans of a closed
  skeleton, then deferred both premises (Nair 1982, Nagura 1952) at $1.33 and $0.48.
- The endgame alone would not have saved that run. A replayed full attack proved Nair for $1.53, but left Nagura's
  core unproved: a prime in (n, 6n/5] for n ≥ 131, which needs explicit Chebyshev bounds that Mathlib lacks.
- A published premise is not free when Mathlib lacks it.
  - The plan rated Nagura `hard` every cycle. In cycle 4 it proposed trading Nagura for Ramanujan, which is provable
    for $3.22, at the cost of 2 open conjectures.
  - `residual_improves` refused that trade, because it ignores premise ratings and ranks any premise below any open
    conjecture.
  - The endgame skips such a re-plan. That is harmless only while the adoption rule refuses the trade.
  - Two candidate fixes are in `benchmarks/timesplit/RESULTS.md`; neither is implemented.

**Omitted frozen declarations are put back** (`restore_omitted_frozen`, always on). A one-round sweep attempt
was lost to a formatting slip. Train #283's `hyp_egypt` sub-statement carries the skeleton's unused `def
Condition`, all three one-shot attempts dropped it, and the frozen guard rejected each without compiling it
(48 of 1,073 attempts overall died on a missing frozen `def`). Now:
- a frozen `def` or `open` the attempt merely LEFT OUT is re-inserted verbatim after its header;
- a declaration the attempt redefines is never replaced;
- an altered target theorem is never repaired;
- the guard itself is unchanged.

**Final verification runs `audit.py`** (`--audit on`, the default). `stage_verify` adds the audit's Lean checks to
every final proof. Research-program sub-lemmas are exempt, because they reach a final proof only spliced into it.
`frozen_match` is a text check, and the honesty rules above show a proof of `3 < 2` passing it. The verdict
carries `audit`, and a failed check leaves `all_clear` false.

Covered by `tests/test_sweep_and_caps.py` and `tests/test_audit.py`.

## Measure self-improvement on the time-split benchmark, nowhere else

`benchmarks/timesplit/` holds problems resolved in 2026 that the model does not know are resolved. The frozen
Lean statement is formal-conjectures' main theorem with `answer(...)` stripped; every docstring and comment is
removed, and every identifier carrying the problem number is renamed. Each item runs `--open` under a fixed
protocol with a fresh synthetic id per evaluation, because `programs/erdos_<id>/` and the Atlas are keyed by id.
`solved` means the TRUE direction verified. A verified proof of the wrong direction is a `contradiction` to
re-audit, never a solve.

As built on 2026-09-24 it has 35 items: test 2, dev 18, train 15. The stated June 2026 cutoff protected little:
35 of the 53 problems the probe excluded were resolved in 2026 itself, so the probe, not the date, decides
contamination.

Gate a harness change on `dev`, paired against the baseline (`score --baseline`). Report `test` and never
select on it. Harvest lessons and lemmas from `train` runs only: anything learned from a dev or test run carries
that item's solution into every later evaluation. The model's prior guess of the answer is right 26 times in 31,
so calling the direction is a weak signal. See `benchmarks/timesplit/README.md`.

**A solve's proof is kept in `benchmarks/timesplit/evidence/<n>/`** (proof, `AUDIT.md`, discovery record). Benchmark runs never write `knowledge/solved/` and `runs/` is untracked, so without this copy a solve's evidence lives on one machine. Track its pin and knowledge snapshot through a `.gitignore` exception if their contents are in no commit: `git cat-file -e $(git hash-object pin_<sha>_harness.py)` tells you. Like `ideas/`, the evidence directory is evaluation-only: nothing the harness runs may read it.

**Gate iterations on `pieces`, keep solves as the verdict.** Three arms and 20 dev runs at $8 solved nothing, so
a solve-only gate cannot tell a better harness from a worse one. `pieces` counts the true direction's certified
steps that are:
- **closed**: nothing beneath them open. A refinement parent over open sub-hypotheses has no hole of its own and
  the harness's `certified` counts it.
- **used**: the glue reaches them. Baseline #419 had 3 of 4 certified lemmas orphaned by a re-plan.
- **non-trivial**: the free cascade does not prove them alone.
- **maximal**: counted once however the prover structured the proof.

Each item is measured at record time (`progress --tag` for older runs, Lean only). A paired item is a win only
with more `pieces` AND a larger `certified_size`. Finer chunking alone raises the first, and verbosity alone
raises the second; on #392 the naive count said 3-1 where both runs had the same single hypothesis open. A
candidate is kept when it loses no solve and wins the sign test at one-sided p ≤ 0.05. It gates iterations and
never describes a problem.

**The free cascade must have every alternative close its goal (fixed 2026-09-24).** `first | … | (simp_all) | …`
accepted a `simp_all` or `norm_num` that only simplifies, so the tactics after it never ran. Lean then reported the
leftover goal at the enclosing `by`, a line above the hole. `_close_holes_without_model` attributes errors by line,
so it read the hole as closed, its keep-check failed, and it reverted the whole pass, genuine closures included.

A replay of 41 saved passes outside time-split dev and test (`benchmarks/timesplit/analysis/cascade_replay.py`)
found 71 holes read as closed and 0 actually closed; the guarded string closes 3. `CASCADE` is now guarded
(`(simp_all; done)`, `(norm_num; done)`, `(aesop; done)`), and `tests/test_cascade_guard.py` pins both the
shape and, under `DEDUCTIVE_LEAN_TESTS=1`, the Lean behaviour. Time-split pins before 3aaab15 keep the old string,
so an arm pinned from the live harness differs from `baseline-v2-84f21c5` in the cascade as well as in anything
else committed since `ce09b11`. Build a candidate on that pin plus patches, or re-run the baseline.

## Discovery fixes and options (2026-09-24)

`docs/discovery-limits-2026-09-24.md` is the audit behind these. The **fixes are on by default** and change
every run on the live harness.
- **No MCP server on any call.** `--setting-sources ""` does not stop the claude.ai account's connectors, which
  arrive as tool definitions after a session's first tool call: 221k-326k cache-write tokens, $1.78-$2.63 for a
  session that read one file. `_run` now passes `--strict-mcp-config` with an empty `--mcp-config`, and that
  session costs $0.0125.
- **Tool sessions are scoped.** A bare `Read` in `--allowedTools` reads any file on the machine (measured: the
  benchmark's reference notes, by absolute path). The prover may now read only:
  - its sandbox;
  - `formal/.lake/packages`;
  - `Formal/Library`;
  - its own `Formal/Programs/Erdos<id>*` modules. Other runs' certified lemmas live under `Programs` too.

  It writes only in its sandbox. Exploration reads and writes only its sandbox. `scoped_read_rules` builds the
  rules.
- **Text past the cap is kept.** When a call ends past `--max-budget-usd`, the json result drops its text even
  though the turn finished and was billed. `_run` reads stream-json and keeps a text call's answer
  (`recovered_over_budget`).
- **An over-budget idea call** (plan, experiments, route judge) is retried at the same effort, never a lower one.
- **Plans.**
  - A skeleton that does not compile gets one repair round with its compiler errors (`--plan-repairs`). 25 of 95
    plan candidates had died that way.
  - `hoist_defs` moves a definition above its first use; this alone would have saved train #997's cycle 2.
  - A plan now sees its own earlier notes and any HUMAN DIRECTION (`plan_notes_context`).
  - It sees the routes that were refused and why (`refusals.jsonl`). 39 refusals were silent.
  - Every finding line of the experiments comes first (`experiments_digest`); #152's growth data had been
    truncated away.
  - Failure digests carry what each attempt tried.
- **Masking keeps named results.** "Erdős–Ko–Rado" had become "the the catalogue's–Ko–Rado".
- **Sub-statements keep the `open`s in force** (`skeleton_context`). This fix was measured in the time-split pins
  on 2026-09-24 but not upstreamed. On the live harness a child lost `open scoped Pointwise`, and every hypothesis
  attack of the v3 smoke run failed on `HAdd (Set ℕ) (Set ℕ)` before any proof was tried.

**The options are off by default,** so baseline pins and the masked series keep their protocol. The time-split
candidate `v3` (`V3_FLAGS`) turns them on together:
- `--explore`: an agentic session that computes in a Python sandbox (`./run.sh`, the usual static screen plus
  numpy, sympy and networkx) and writes NOTEBOOK.md. Every later plan, experiments call, proof attempt and child
  sees the notebook. It runs once per run (both `--open` directions share it).
- `--explore-core`: after a cycle that discharged nothing, explore the hardest open hypothesis.
- `--empirical`: a systematically supported pattern may become a hypothesis with `basis: empirical`, labelled as
  such; Lean still decides.
- `--routes k`: k plans per cycle on different routes. A route judge picks one, and the rest are kept; after a
  stall a new route may replace the incumbent even if it is not "better" by the syntactic measure.
- `--attack-order core-first` with `--core-share`: the hardest hypothesis is attacked first, with a real budget.
- `--plan-effort`, `--plan-budget`, `--stall-credit easier`, `--literature-scope wide` (partial results,
  analogues, techniques, obstructions), `--child-cycles`.

`timesplit.py ideas` grades, blind, whether a run's notes contain the key idea of the published resolution,
against `benchmarks/timesplit/ideas/<n>.md`. Those notes exist for train items only, and the harness never sees
them.

## Current research guidance reaches the model

Store concise operator next steps in `atlas-data/research-guidance/<id>.md`, and link the file from an Atlas finding. The harness reloads this file for assessment, reduction, experiments, planning, ordinary and agentic proving, refinement, decomposition, criticism, search and construction. It applies to fresh runs, resumed checkpoints and research children without modifying the frozen problem input. Guidance is labelled unverified operator context, logged with its source and hash, and preserved in the actual prompt transcript (also TASK.md for agentic attempts). It is excluded from formalization and blind verification prompts. Record new results, open obligations and refuted routes with explicit status; do not promote a draft or numerical check into a proved premise.

Operator guidance now also reaches the in-run discovery stage's own calls (`discover`, `discover-ladder`,
`discover-rung`, `discover-synthesis`, `discover-gap`), never its referee.

## In-run discovery, blueprints and dated libraries (2026-10-01)

Built after OpenAI's Navier–Stokes report (2026-09-08). Its transferable lesson is structure, not scale:
- groups seeded with every variant;
- easier problems first, whose solution seeded the main attack;
- a consolidator cross-feeding intermediate results;
- agents that could read the literature.

Strategy and ranking: `docs/ns-capacity-2026-10-01.md`. Evidence: `benchmarks/timesplit/RESULTS.md`, "Navier–Stokes
lessons, built and screened". **Every flag below is OFF by default.**

- **`--discover on`**: the runner's discover-v3, moved into harness.py (the section "informal discovery (in-run)").
  - It runs once per run, after the statement is frozen. Under `--open` a confident decision commits the run to ONE
    direction with the whole budget (`--discover-commit off` keeps both).
  - Its guidance reaches every research stage through `_with_research_guidance`, and every child through its state.
    Children run with `--discover off`.
  - The prompts and the decision rule are the runner's verbatim, and `tests/test_discovery.py` fails if they drift.
  - The best refereed proof is passed WHOLE, head and tail beyond 14,000 characters. The runner's v2–v4 still pass
    `text[-3500:]`, which cut #678's opening lemma; that is kept for their protocol and fixed only in the in-run stage.
  - Parallel calls each use their own backend (`_fresh_backend`), so every cost is logged against the call that made
    it and `spent_usd` counts discovery.
- **`--discover-mode crossfed`**: after each round, a synthesis writes what is established, the route, the gaps, the
  dead ends and k assignments, and the next round starts from it. **`--discover-ladder k`**: k easier variants are
  solved bottom-up first, and their methods seed the main attempts.
  - `--stop-after discover` runs this stage alone. `timesplit.py discover-screen` is its no-Lean screen; `ideas
    --tag` grades it.
  - Screen A, 10 weak train items, no Lean:
    - refereed proofs of the true side on 3 of 8 items that never had one;
    - no fooled referee;
    - ideas W3 L1;
    - $2.12 an item.
    On #152 the ladder's rungs found the published method, which the main attempt then used in its first round.
  - Screen B adds `--library`: direction right on 5 of 5 against 3 of 5. Both FALSE statements called true were
    corrected. Proof-finding is not shown to change.
  - Screen D re-drew four of Screen A's items: a refereed proof only on 1 of 4. On the never-complete items, a
    crossfed draw finds a refereed proof about 0.29 of the time, against 0 in 24 baseline rounds. So DRAW AGAIN
    before concluding: a single draw is not the item's rate.
- **`--blueprint on`**: discovery's refereed complete proof, for THIS direction, becomes numbered steps (`=== STEP
  S1` blocks, robust to LaTeX). Then:
  - the plan maps each hypothesis to steps (`"blueprint_steps"` in its ledger);
  - each child's literature opens with its step's informal proof;
  - a sub-residual first EXPANDS its step into smaller steps (`blueprint-expand`), so depth follows the proof instead
    of improvising (the #435 failure);
  - a hypothesis mapped to 3 or more steps is decomposed at once (`_blueprint_merged`). Plans merge steps despite the
    instruction (#678's `hyp_nside` covered seven), and merged hypotheses are the ones that fail.
  - Run C, train #435 and #678: the pipeline worked end to end.
    - #678 certified every conjecture within 2 cycles, then stopped at two published premises (Nagura, Nair).
    - Its wall is the ROUTE discovery chose: Nagura is not in Mathlib, and an earlier run found a Bertrand-only route.
    - So a `published` blueprint step outside Mathlib should trigger a reroute round. That is not built yet; see
      docs/ns-capacity-2026-10-01.md.
- **`--residual-view outline`**: re-plans see the skeleton with every certified proof namespace elided (`restore_spliced`
  puts them back), head and tail kept. The default `tail` shows the last 6,000 characters: 16% of #678's 38,045.
- **`--library DIR`**: a dated literature digest (`library.py`, `timesplit.py library`) joins the discovery prompts
  and the plan.
  - Nothing in it is dated on or after the cutoff (the first public date minus 7 days for a benchmark item), and
    OpenAlex's placeholder 1 January dates are dropped.
  - arXiv texts are always version 1, so no later version can cite the resolution.
  - A document that names the problem is excluded.
  - Digests read only the supplied text: a paper with no text is cited, not summarised, because a summary from memory
    has no date.
  - The arXiv export API rate-limits this machine; search goes through OpenAlex.
- **Runner candidates:**
  - `discover-v5` = in-run discovery;
  - `blueprint` = v5 + blueprint + outline;
  - `crossfed` = crossfed + ladder 3 + a $6 discovery cap;
  - `crossfed-blueprint` = both.
  The runner launches them with `--open`, and the harness commits.

**Four more (2026-10-02), the ranked ideas in docs/ns-capacity-2026-10-01.md, all OFF by default**
(`tests/test_discovery.py`):
- **`--discover-draws N`**: independent draws, sharing the ladder, until a refereed complete proof appears.
- **`--blueprint-reroute on`**: every cited blueprint step gets a VERIFIED Mathlib name, or is marked missing.
  - A claimed name must exist in the local declaration index (`find_decl`); an unsure or invented name counts as
    missing.
  - When a step is missing, a variant proof avoiding it is requested, refereed, and adopted only if it leaves strictly
    fewer missing premises.
  - The plan's blueprint shows `MATHLIB HAS IT` or `NOT IN MATHLIB` per step.
- **`--rediscover N`**: Lean inside the discovery loop.
  - A conjecture that failed a Lean attack, or whose refinement was refused, gets ONE cross-fed discovery of its own.
    It is told the Lean-certified facts around the step and what broke.
  - A refereed proof becomes that step's blueprint (`_blueprint_for_name` returns "R"), and its next attack is
    recursive.
  - A refereed DISPROOF is recorded as a `rediscover` failure the next plan must answer.
- **`--blackboard on`**: campaign memory in `programs/erdos_<n>/BLACKBOARD.md`.
  - Each run appends its discovery synthesis, its [Lean]-certified facts, its open steps and its failures, under a lock
    shared by both `--open` directions.
  - The next run's discovery reads the newest whole entries.
  - Benchmark aliases are fresh per evaluation, so nothing leaks between evaluations.
- **`--discover-model`**: routes discovery, synthesis and blueprint calls to another model. The usage limit, not
  dollars, decides whether to use Fable.

First use on OPEN problems: `experiments/open-discovery-2026-10-02/REPORT.md`.
- A no-Lean screen of 7 open problems ($12.90) produced no refereed proof.
- On every problem it reconstructed the published partial results and named the same open core as the forum.
- #455 then got the full pipeline: $18.99, stalled at cycle 3 of 6.
  - It certified and audited `i ≤ 6·gap_i` for convex prime chains, a weaker form of Richter 1976, and left the core
    open.
  - Rediscovery and the blackboard fired; the reroute never did (no refereed proof).
  - Facts certified inside a sub-residual now reach the blackboard (`_blackboard_sub_facts`), even under a refused
    refinement. The automatic brief still misses them.

**The research engine, `--discover-mode engine`** (2026-10-02, OFF by default; harness.py "research engine",
`tests/test_engine.py`, `experiments/idea-engine-2026-10-02/REPORT.md`):
- **Why.** The old discovery attempts were one-shot essays: on #455 a median of 4,300 output tokens and 49 s each. One
  of them found a beyond-frontier constant and the synthesis filed it under dead ends.
- **What a run does:**
  - a frontier map (KNOWN, BARRIERS, CORE), plus typed TARGETs beyond the frontier and ANGLEs on the core;
  - parallel tool-using research sessions with a Python sandbox (`--engine-session-budget`, default $3), half on core
    angles and half on targets of distinct types;
  - for every proved or refuted claim, a step referee and an adversary; a novelty judge only if both pass;
  - outside benchmarks, an OpenAlex literature check before a claim keeps `validated-new`;
  - a meta-review that writes the next round's assignments.
- **Outputs:** `engine/engine.json`, `engine/IDEAS.md` and a blackboard entry. Only `validated-new` counts, and it is
  informal: never Lean-checked or human-reviewed by itself.
- **Operator guidance** reaches the frontier, session and meta calls, never the judges.
- **v1 on #455** ($15.42):
  - liminf q_n/n² ≥ 0.80024, against Richter's 0.352. It came from a max-plus certificate mod 15015; the certificate
    was re-run independently and the literature search found nothing better.
  - A barrier: the Lean run's finite core implies class-number-one finiteness.
  - The engine rated both significance 1; the bar for the loop is significance ≥ 2.
- **Later additions**, each off unless flagged:
  - `engine/checkpoint.json` resumes a cut-off run without buying anything twice: the map, each session and each
    verdict.
  - `--engine-deep-budget` buys one long session on the most promising line after the rounds.
  - Broken claims a judge calls fixable are repaired once and re-judged (`--engine-repair-max`, default 3).
- **Tally after v1–v3** on #455, #1203, #153 and #156: 18 validated-new claims, every one significance 1. The best are
  #455's liminf q_n/n² ≥ 0.86429 (certificate re-run independently) and #156's cyclic analogue.
- **`--engine-min-target-sig N`** (v4): the two novelty judges rate every frontier target as if proved, on the same
  scale, and round 1 attacks only targets they rate new at ≥ N.
  - Why: the maps labelled 1–6 targets per problem at significance 2–3, but sessions settled for what they could prove.
  - The final verdict is still the post-hoc panel on the actual proof.
- **v5: chain-aware validation (always on) and gap closing (`--engine-gap-rounds N`, off by default).**
  - A proof may cite other claims of its notebook. The judges see the cited lemmas, and a claim's `status` stays
    `conditional` (with `pending`) until every lemma under it is valid. `own_status` keeps its own verdict.
  - Gap closing: broken claims are rated "if proved", the most dependent first. Each one worth significance ≥ 2 or the
    core is re-judged with its lemmas, then gets tool-using gap-closing sessions, and so does every lemma under it.
  - First test, #152's hard-step run ($5.49): it turned the deep dive's dropped would-be proof of the whole problem
    into a refereed chain, iso ≥ (n−18)/4 for every Sidon set. That is informal and has the "resolved" cue; see the
    idea-engine REPORT.
- **Hard steps:** `experiments/idea-engine-2026-10-02/hardsteps.py` points the engine at steps train runs left open as
  hard. `hardsteps_lean.py` hands a refereed proof to the deductive loop as its blueprint.
  - The frozen theorem must be named `erdos_<id>`: a CLI run matches plans only against that name, and the loop now
    refuses a statement without it.
  - The frame tells the model that the problem was resolved, so a hard-step result is not evidence about open
    problems.
  - **First result, #435 `hyp_top`:** the train run's only open step. The engine proved it informally for $8. The
    deductive loop certified it with that proof as its blueprint, for $66 over three operator-funded resumes. The full
    #435 statement then assembles and passes the audit
    (`experiments/idea-engine-2026-10-02/evidence/435-hardstep/`).
    - It is a reconstruction by the published route, not an autonomous solve.
    - On the way it exposed the splice bug fixed in `8641308`: an `open ... in` left behind by a dropped duplicate def.

**Where the engine stands (2026-10-06), and step 3.** Details: `experiments/idea-engine-2026-10-02/REPORT.md`.
- **Step 2: whole time-split dev problems, open framing, no cue** (`timesplit.py discover-screen --discover-mode engine`,
  tag `engine-v5-dev`, $8–20 an item):
  - clean, refereed, complete proofs of the true answer on 3 of the 6 items the engine did not recognize: #1125, #401
    and #618. The pre-registered prediction was 1 of 8.
  - **#1125 is proved in Lean end to end** (`benchmarks/timesplit/evidence/1125/`):
    - the engine's proof is the blueprint, and Lean cost $2.79;
    - the audit passes all 13 checks, the blindness checks included;
    - those checks need the Lean stage's own time-split record, which `hardsteps_lean.py` now writes. Without it the
      verdict was FAIL.
  - #204 and #392 were solved but recognized, so they are not evidence. #570 and #865 were not solved.
- **Contamination is real.** A masked high-effort engine can name the problem and recall its resolution. Grade on
  `recognized_true` (`engine_recognized`), and judge completeness with the settles check (`engine_settles`, both judges
  agree), never with the novelty verdict: judges who remember a result say "known".
- **Step 3, next.** Open problems:
  1. a broad map-and-rate screen (`--engine-sessions 0 --engine-min-target-sig 2`) over 20–30 high-`partial` open
     problems;
  2. full engine runs, with gap closing on, on the 2–3 where the judges see a reachable significance-2/3 target;
  3. Lean on any complete chain (`hardsteps_lean.py --full-run --chain`).

  On an open problem the audit is necessary but not sufficient: a resolution also needs human review.
- **The account has a weekly usage limit** (it resets Monday 09:00 Toronto). It stopped every lane on 2026-10-06, and
  the lanes resumed after the reset. Budget a week, not a day.

**Engine v6 (2026-10-07): measure reach, think longer, audit in-session, build on other results.**
- **Why.** Step 3's map-and-rate screen of 20 open problems found 1 OPEN target against 6 predicted. There were three
  causes, all ours:
  - the map built targets for "weeks" while the judges rated reach "in a day" (69 of 70 significant targets came out
    low);
  - the map was never asked for reachable stepping stones;
  - assignment sorted by significance and never attacked #873's one reachable target. #873's significance-2 result
    came from an unrated angle.
- **Reach fix (always on).**
  - The map builds a ladder: at least three narrow significance-2 stepping stones, each with a REACH.
  - Judges rate reach over ONE focused week, with a probability `p_week`.
  - Targets are ordered by expected value (`target_value`).
- **`--engine-probe-items N`.** Short probe sessions on targets and angles before round 1. They MEASURE reach: their
  judged claims and verdicts order round 1. With `--engine-sessions 0` this is a map-and-probe screen.
- **`--engine-marathon-legs N`.** The deep dive's line continues for N legs, each reading every earlier leg's notebook
  and the accumulated `## Routes` log.
- **`--engine-session-legs N`.** A round session or deep dive that stops with budget left goes back into its own sandbox
  to take the route it named under `## Next`, up to N legs within its own budget (`engine_session_legs`).
  - Why: outside the time-split dev and test sets, 52 of 63 round sessions on disk stopped under 60% of their cap
    (median $1.44 of $3, 10 turns), and 8 of 9 deep dives did too, although the deep dive's prompt already said not to
    stop. A session ends when its first route ends: #20's sessions refuted their assigned route, named the corrected
    statement, and stopped with $2 left.
  - Prompting alone does not fix this, so the harness does. Every session now writes `## Next`, and `NEXT: NONE` ends it.
  - Each finished leg is checkpointed, and so is the deep dive's plan, so a resume buys neither again.
- **Self-audit (always on).** Sessions keep a routes log and audit before PROVED: the dependency chain, every cited
  theorem's hypotheses, small cases, parameter order. Claims carry AUDIT and CONCERNS, and the judges decide the
  concerns.
- **`--results-library on`.** Other runs' validated results plus the openai/math families relevant to the problem
  (`results_library.py`). Never in benchmark or masked runs, and no dev or test item ever enters it.
- **The audit** adds Comparator and nanoda when `tools/install.sh` has been run (see the honesty rules).
- **Off by default** until a dev screen against v5: probes, marathon, session legs and the library.

**The resolution campaign, `resolution.py` (2026-10-08).** Not `campaign.py`, the campaign DAG.
- **Why.** The operator's direction: aim at significance-3 results, check everything possible in Lean, and run without
  human intervention.
  - Step 2 showed the engine can settle problems: 3 of 6 unrecognized dev items, one proved in Lean.
  - Step 3 aimed it at the most-studied open problems and at partial targets, and got partial results.
- **What it does.** Each open problem moves screen → scout → deep → Lean, each tier resuming the last.
  - **screen** (`--engine-settle-draws 2 --engine-sessions 0`, about $3-6): the map, then two draws of the deep plan's
    SETTLE CHANCE from the map alone, before any work. On step 2's dev items its mean was 0.46 on the three the engine
    settled and 0.09 on the rest, with #1125 (settled, 0.085) the miss (REPORT 3.8).
    - A problem at or above 0.3 is scouted.
    - Below the bar, a fixed quarter chosen by a hash of the number is scouted anyway, as the control arm. Every row
      carries its arm, so the two arms' settle rates measure the screen.
    - Scouts take the pass arm first, highest chance first.
    - `import-screens` takes passes drawn from maps already on disk (REPORT 3.9). Nothing is screened out on such a
      draw, because those maps predate the resolve objective.
  - **scout:** the engine on the whole problem, with `--engine-objective resolve`, so the deep dive aims at settling it.
  - **deep:** for a problem with traction. It adds a round planned by the team lead (a resume that adds rounds now
    plans them), a marathon leg and gap closing.
  - **Lean:** for a complete answer, meaning both settles judges agree. It is a normal open-problem run, never a
    benchmark run, with the whole chain as its blueprint, committed to the direction the chain proves, then the audit.
  - **The statement is made to compile first** (`resolution.lean_statement`, 2026-10-14). The screen freezes the text
    alone and the engine never compiles it, so #655's Lean stage ended after $0.06 on `unknown namespace
    EuclideanGeometry`: formal-conjectures statements use that library's own names (`ℝ²`, `distinctDistances`) and
    Mathlib beyond `Mathlib.Tactic`.
    - It runs the time-split mask builder's repair loop (`timesplit.freeze_compiling`): imports, `open scoped
      Classical`, and formal-conjectures declarations inlined verbatim, in rounds.
    - Every inlined declaration must read the same at the campaign's pinned commit, because the local copy of the
      library is the benchmark's.
    - A statement that still fails is `lean-blocked`, at no cost. `resolution.py requeue-lean --problem N` sends a
      complete answer back to Lean, and it is the operator's call.
- **Two tracks, by intent** (`--engine-intent-judges 2`, REPORT 3.11). Judges classify the screen's line and every
  settling claim: new mathematics about the problem as posed, a formalization gap, or a known result.
  - A pass goes to the **new-mathematics** track unless they name a gap or a known result. Those go to the
    **statement-findings** track.
  - New-math problems whose scout did not settle them get the **program** tier: the research program, the analytical
    deep tier ($90).
- **The research program** (`--engine-program-cycles N`, harness `engine_program`): the deductive loop's rules in
  informal mathematics.
  - A lead writes a proof skeleton: a target, lemmas, and a glue that a referee and an adversary must pass.
  - Sessions attack the open lemmas, each judged against the lemma as stated.
  - Refutations and failures shape the next plan.
  - A closed skeleton becomes one chain for the settles judges and Lean.
- **What it writes:** `resolution/results.jsonl` and an Atlas finding.
  - A verified open-problem proof judged new mathematics goes to `resolution/REVIEW-NEEDED.md`, with `claimEligible`
    false until human review.
  - A verified gap or known result goes to `resolution/STATEMENT-FINDINGS.md`: a finding about the formal statement,
    never a resolution.
- **The queue:** four known lines first (#366, #686, #488, #873), then the least-studied unsolved problems.
  - Step 3.7 found that typical problems did no better than heavily studied ones. So the order matters less than the
    strength of each attempt.
- **What makes an attempt stronger:**
  - **Decide by computation.** Under `--engine-objective resolve`, the map has a DECIDE section naming the computation
    that could settle the problem, and T1 must be the complete answer. A feasible plan leads round 1 and the probes.
    Its sessions run scripts for up to 10 minutes (`--engine-decide-seconds`): the runner's cap and the CLI's
    `BASH_DEFAULT_TIMEOUT_MS`, checked live.
  - **The results library** is on, including openai/math method digests: each Erdős-related family's abstract, main
    statements and proof overview, from the release's LaTeX (`results_library.py --digest-openai`).
  - **The deep dive states `SETTLE CHANCE: p`.** A problem gets the $40 deep pass only if p ≥ 0.1 (`SETTLE_FLOOR`) or a
    claim is already rated 3. #366's own team lead saw no settling line.
- **Lean on partial results:** every validated-new PROVED claim at significance ≥ 2 gets its own Lean run under a fresh
  id. The harness formalizes the claim, with a crosscheck judge, then proves it from the engine's chain.
- **Restarts are safe:** one loop at a time (an exclusive lock), and a stage records its run at launch, so an
  interrupted stage resumes. A stage writes only its own problem's entry (`save_problem`, under the state file's lock).
  A stage used to save the whole state it read when it started, which erased any entry written meanwhile.
- **A usage limit is an outage, not a verdict** (`limit_wait`). A stage that ended on one waits for the stated reset
  and resumes, with no error counted. The weekly limit's dated reset ("resets Oct 13 at 9am") was once read as no time
  at all. From 2026-10-09 to 10-13 the campaign then dropped ten problems it never screened, among them the prescreen's
  top nine.
- **The queue follows the map-free prescreen** (`resolution/prescreen.jsonl`, from `step3/settle_nomap.py --sweep`;
  REPORT 3.10), then forum size. 156 of the 264 problems with a pinned formal statement are swept.
  - Its top scores mostly flag statements easier than the problem: a formalization gap (#655's regular n-gon) or a
    published result (#32, #695).
  - A settle there is a formalization or literature finding, so review it for intent.
- **Pacing:**
  - one lane: it waits while any driver runs;
  - a daily cap in `resolution/config.json`, default $150;
  - usage limits are waited out.
- **Running it unattended is the operator's decision.** The permission system refused both a LaunchAgent and a loop
  started from a session. Run `caffeinate -s python3 resolution.py loop` yourself, or `python3 resolution.py once` for
  one stage; `python3 resolution.py status` shows where it is.

**PARI/GP in the research sandbox (2026-10-08).** `cypari2` (PARI 2.15.4) is an allowed module for every model-written
script, and the session prompt names its Thue, class-group, elliptic-curve and rational-point functions. Both v6 full
runs had stopped at a significance-2 step with "infeasible without PARI/Magma". Three layers keep scripts contained:
- the static screen names PARI's shell, file and environment functions, and numpy's file readers (`np.loadtxt` could
  read the benchmark's answers before this);
- PARI runs in secure mode, set before the script (`PARI_SECURE`);
- on macOS every sandboxed script runs under a Seatbelt profile (`sandbox_prefix`): no network, no process but the
  interpreter, no reads under the home directory outside the script's folder, and no writes outside it.

A name built at runtime gets past the screen, and the kernel stops it. `tests/test_sandbox_pari.py` covers this.

**Robustness fixes the same day:**
- **A usage limit is a hard error.** `HARD_RE` now matches "You've hit your session limit" and "…weekly limit". A
  resume also drops every judge verdict and rating that an infrastructure failure produced, and judges those claims
  again (`engine_drop_infra`). That repair gave step-2 dev #570 a significance-2 result its judges had never seen.
- **An interrupted model call is retried.** A stream with no result event is either a kill or a connection that died
  across a system sleep. On 2026-10-08 a dead battery cost #1055's map this way.

Two operating notes:
- A `discover-screen` or in-run lane matches `pgrep -f "harness.py run"`, so another lane's `timesplit.py run` refuses
  to start items while it is live. Pass `--allow-concurrent` deliberately.
- Lean runs share the machine's compile capacity with any other lane, and a saturated machine turns compile timeouts
  into apparent mathematical failures.

**Opt-in long computation tier (2026-10-08).** `long_compute.py prepare` copies and hashes explicitly selected case
scripts; `long_compute.py run <job-dir>` executes them through `sandbox_argv`, with two hours per case and four hours
total by default, without holding a model call open. It checkpoints between scripts, preserves output, skips completed
cases on resume, and retries timeouts only with `--retry-timeouts`. Process success is not mathematical success; no
floor or proof is inferred automatically. Review internal script timers (some #366 scripts stop themselves at 108 s)
before extending them. See `docs/long-computation-tier.md`. This tier passed controller tests and a real SAT sandbox
smoke test; improved mathematical performance and multi-hour reliability have not yet been established.
