# erdos-harness

An LLM + Lean 4 harness for attempting [Erdős problems](https://www.erdosproblems.com), built
around one principle: **the LLM is sampled, never trusted — Lean is the ground truth.**

Its rankings and run evidence feed the [Erdős Atlas](https://github.com/nkudeba/erdos-atlas), a searchable
ranking of all 1,217 problems in the catalogue. A personal project by Nick Kudeba, built with Claude Code.

```
                 ┌─────────────┐
   problem.json  │  literature │  what's already known? proof route? witnesses?
        │        └──────┬──────┘
        ▼               ▼
   ┌──────────────────────────┐     K independent candidates, each compiled;
   │        formalize         │──►  adversarial cross-check picks the most
   └────────────┬─────────────┘     faithful; statement is then FROZEN
                ▼
   ┌──────────────────────────┐     rounds of M diverse attempts; every attempt
   │      prove (loop)        │──►  compiled; errors fed back; `-- LOOGLE:` /
   └────────────┬─────────────┘     `-- GREP:` retrieval directives honored
                ▼ (if stuck)
   ┌──────────────────────────┐     lemma skeleton with `sorry`s (compiled!),
   │  decompose + refine      │──►  then progressive sorry-elimination
   └────────────┬─────────────┘
                ▼
   ┌──────────────────────────┐     clean compile + no sorry + #print axioms +
   │         verify           │──►  blind back-translation faithfulness judge
   └──────────────────────────┘
```

## Why each piece exists

| Layer | Failure mode it kills |
|---|---|
| Lean compile of every artifact | hallucinated lemmas, wrong syntax, invalid proofs |
| Frozen-statement guard | the classic cheat: "proving" a subtly different theorem |
| Candidate cross-check + sanity examples | faithful-looking but vacuous/mis-quantified formalizations |
| Literature stage | re-deriving what's known; picking the wrong proof direction for resolved problems |
| Retrieval (loogle + mathlib grep + `Try this` capture) | reproving what mathlib already has |
| `#print axioms` | proofs smuggled through `sorryAx` or custom axioms |
| Blind back-translation | statement drift you stop seeing after staring at Lean for an hour |
| Banned constructs (`native_decide`, `axiom`, `unsafe`) | technically-compiling non-proofs |

## Setup

```bash
# 1. Lean toolchain + mathlib (one-time, ~10 min)
curl -sSf https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --default-toolchain none
export PATH="$HOME/.elan/bin:$PATH"
lake +leanprover-community/mathlib4:lean-toolchain new formal math
cd formal && lake exe cache get
```

## Usage

Describe the problem in `problems/erdos_NNN.json`:

```json
{
  "id": "NNN",
  "statement": "exact English statement from erdosproblems.com",
  "status": "solved (X, 1994)",
  "notes": "known resolution route, witnesses, caveats",
  "url": "https://www.erdosproblems.com/NNN"
}
```

Then:

```bash
# normal use — needs a logged-in `claude` CLI
python3 harness.py run --problem problems/erdos_NNN.json --backend claude-cli

# agent-served mode — harness writes prompts to runs/<id>/llm/pending/*.json and
# waits for runs/<id>/llm/done/<id>.txt; any outer agent (or human) answers them
python3 harness.py run --problem problems/erdos_NNN.json --backend file

# check any standalone .lean file against the project
python3 harness.py check path/to/File.lean
```

Useful flags: `--samples` (attempts per round), `--rounds` (proving rounds before
decomposition), `--resume <run_dir>` (stages checkpoint to `state.json` and are skipped on
resume), `--skip-literature`, `--agentic off|escalate|always` (sandboxed compile-loop attempts;
default `escalate` = after one plain round), `--agentic-samples`, `--agentic-turns`,
`--call-budget` (max USD per `claude -p` call).

Other commands:

```bash
python3 harness.py regress                 # recompile every verified proof in knowledge/solved (fast)
python3 harness.py regress --full --problems 493 674   # re-run whole pipelines
python3 harness.py retrospect runs/<run>   # LLM proposes ≤3 general lessons → knowledge/playbook.md
python3 harness.py improve --problems 363 --eval-problems 493 674   # gated learning loop (see below)
python3 tests/test_helpers.py && python3 -m unittest tests/test_outcomes.py tests/test_learning.py tests/test_backend_retry.py
python3 tests/test_pipeline_mock.py        # end-to-end with real Lean and a scripted model (~3 min)
```

Every run leaves a full audit trail in `runs/<timestamp>-erdosNNN/`:
`log.jsonl` (every event), `transcripts/` (every prompt+response), `attempts/`
(every compiled candidate), `report.md`, and — on success — `final/ErdosNNN.lean`.

## Reporting a run

Each `run` prints one line (`RUN-SUMMARY problem=… exit=… outcome=… spend=… lemmas=… dir=…`), also saved
to `<run_dir>/SUMMARY.line` and `runs/summary-log.tsv`, and emitted on the fatal path too. Reprint it any
time with `python3 harness.py summary --problem <n>`. Background watchers should tail that instead of
parsing `log.jsonl`.

## Honest expectations

This harness will not solve open Erdős problems on your laptop. It's built for the workflow
around *resolved or tractable* statements: formalize faithfully, search for proofs with
compiler-guided repair, and verify ruthlessly. On genuinely open problems its realistic
contributions are (a) trustworthy formalizations, (b) literature triage, and (c) verified
partial results — which is roughly what the 2025 wave of "AI solved an Erdős problem"
results actually were, most being literature finds or adaptations rather than new mathematics.

## Review additions (September 2026)

A second provider (OpenAI Codex CLI) is supported when a `codex` binary is on `PATH`. It is **not**
installed on the development machine, so this backend is untested here (its three trial runs on #532
died on provider errors before any Lean check):

```bash
python3 harness.py run --problem problems/erdos_532.json --backend codex-cli --agentic off
```

`--agentic always --agentic-samples 1` gives Codex a scratch directory and a Lean
checking script so it can read Mathlib and repair its proof. The independent harness
still checks the returned proof. Codex sessions are bounded by `--llm-timeout`;
`--agentic-turns` applies only to the Claude backend. Codex cost is unavailable,
not zero. A provider error is an infrastructure failure, not an unsuccessful proof.

Proof attempts can request `-- READ: Mathlib.Combinatorics.Hindman` to retrieve a
bounded source module. Source-index signatures are approximate; Lean remains the
check on generated declarations and argument types. Partial proofs are retained
for refinement, but cannot pass final verification.

Compare implementations using the same text-only provider and sample budget:

```bash
python3 battle_test.py --engine baseline --problem problems/erdos_532.json
python3 battle_test.py --engine current --problem problems/erdos_532.json
```

The baseline adapter uses Codex despite the legacy log's `claude-cli` label. These
are stochastic end-to-end comparisons: formalization and model samples may differ.
For fixed-statement comparisons, use separate checkpoints containing the same
`statement` and `literature`, and supply each checkpoint with `--resume`.

The learning command now stages lessons in a separate knowledge directory:

```bash
python3 harness.py improve --problems 532 --eval-problems 493 674 645 \
  --backend claude-cli --cycles 1 --rounds 2 --decompose-rounds 2
```

Training and evaluation IDs must be disjoint. It evaluates the old and candidate
lessons in fresh runs, requires at least one additional held-out success and no
lost successes, and recompiles the candidate's saved proofs before promoting
lesson files. Ties, regressions, and provider errors leave active lessons unchanged.
Each evaluation gets its own knowledge copy; before/after proof searches use the same frozen statement and literature context. Artifacts live in `runs/learning-*`.
This is retrieval/prompt learning, not model-weight training or autonomous code
rewriting. A single stochastic gain needs replication before claiming general
improvement. `retrospect` by itself still appends directly; use `improve` for gated
promotion. `ERDOS_KNOWLEDGE` selects an isolated knowledge directory.

Verification and workflow tests:

```bash
python3 tests/test_helpers.py
python3 tests/test_outcomes.py
python3 tests/test_learning.py
python3 tests/test_pipeline_mock.py
python3 harness.py regress
```

The mock pipeline uses real Lean with scripted model responses and isolated
knowledge. It tests repair plumbing, not model solve rate. Fast regression checks
saved proofs; it does not show that fresh proof search still succeeds.

## Battle-test findings and the knowledge layer (September 2026)

Full details, per-problem results and the bug list are in [RESULTS.md](RESULTS.md). In short: with
Claude Fable 5.1 as the sampler, the *original* one-shot harness solved every ladder problem it was
given (399, 645, 397, 316) in round 1, so the real weaknesses were infrastructure: Lean's coded
diagnostics (`error(lean.unknownIdentifier):`) were dropped by the parser, `autoImplicit` was silently on
for standalone files (a misspelled name in a statement compiled as a different theorem), and failed code
was never fed back. All three are fixed and covered by tests.

The harness now carries a `knowledge/` directory it both reads and writes:

| file | written by | read by |
|---|---|---|
| `knowledge/playbook.md` | `retrospect` (LLM lessons, deduped, provenance-tagged) and hand edits | prove/agentic prompts (keyword-matched, ≤3000 chars) |
| `knowledge/lemmas.jsonl` | verified proofs (helper lemmas harvested automatically) | prove prompts (offered verbatim with their imports) |
| `knowledge/solved/` | every verified proof | `regress` (recompile), `improve` (promotion gate) |
| `runs/.cache/decl_index-*.tsv` | one pass over Mathlib/Batteries/core (265k declarations) | `-- CHECK:`, auto-import, verified-name blocks |

"Recursive self-improvement" here means exactly this loop: run → retrospect → held-out evaluation →
promote only on a strict gain with no regressions. The model's weights never change; what accumulates is
compiler-grounded knowledge (proofs, lemmas, lessons) plus prompt/retrieval behaviour, and every claimed
improvement is a Lean-checked artifact. Treat single-run gains as evidence, not proof.

`python3 harness.py regress --references` also checks the labeled #370
assistant-written proof and #532 community-proof adaptation. They are not
counted as autonomous search successes. Attribution and scope are in
`references/README.md`.

### Repair checkpoints

Refinement now persists both the best compiling outline and the latest failed
candidate with its compiler diagnostics. The next round repairs that candidate,
including when it contains no `sorry` but still fails compilation. Resuming keeps
that candidate/error pair and numbers new attempts after prior attempts. The
frozen theorem, banned-code checks, compilation, and final axiom audit still gate
acceptance.

On Erdős #532 this flow repaired the model-generated candidate in one extra round;
the resulting proof passed full verification. The saved proof is
`knowledge/solved/Erdos532.lean`. This is a targeted repair result, not evidence of
a general solve-rate improvement. The initial matched pair remains 0/1 for both
engines; repair-extension results are reported separately under
`runs/comparison-retry-20260908/repair-extension/`.

## Triaged open-problem pipeline (September 2026, second extension)

The pipeline now routes every target after formalization and never claims anything externally:

```
literature → formalize → cross-check → FREEZE → assess (triage) → [search] → prove (one-shot → agentic → decompose) → verify
                                                     │                                        ↘ partial results (exit 3)
                                                     ├─ construct  (--allow-construct; extremal/bound targets)
                                                     └─ program    (--allow-research; open research-depth targets)
```

| stage / command | what it does | gate |
|---|---|---|
| `assess` | one medium-effort, $1-capped JSON classification (shape, status, depth, computable, known_bound, routes, tier); routing rules are code (`decide_mode`), flags override, decision logged in `state.json` and `report.md` | always |
| `scout` | ranks OPEN problems from `teorth/erdosproblems` (falsifiable/verifiable/decidable, no prize, target tags, short, few comments, ambiguity flags) and writes `problems/erdos_<n>.json` with the site's own discussion as notes | `python3 harness.py scout --top 15` |
| `--open` | formalizes the conjecture AND its negation (negation built from Lean's own `#check` type), freezes both, attacks both in parallel, reports to `knowledge/open/<n>/<run>/` marked *requires human review before any external claim* | flag |
| `search` | model-written bounded Python search (stdlib only, static safety screen, time cap) for a witness / counterexample of the FROZEN statement; hits are logged and handed to the prover to certify with `decide +kernel` / `norm_num` | routed `search-first` or `--search always` |
| `--literature-web` | WebSearch/WebFetch limited to erdosproblems.com, its forum, arXiv, MathOverflow; Lean proof repositories are forbidden and detected; extracts `KNOWN_BOUND` | flag, `--web-budget` |
| `construct` | FunSearch-lite: model-written generator/valid/score/mutate/certificate program, random local search + model-proposed variants, archive, Lean certificate of the best finite object → `knowledge/constructions/<n>/` ("certified bound, not a resolution") | `--allow-construct`, `--construct-budget` |
| `program` | persistent research program `programs/erdos_<n>/` (PLAN.md, `Lemmas.lean` compiled as module `Formal.Programs.Erdos<n>` and imported by later attempts, `ledger.jsonl`), cycles of experiments → sub-statements → standard pipeline → certified lemmas → retrospect; `REVIEW.md` every k cycles with an optional pause for human direction through the file backend | `--allow-research` + `--run-budget` |
| specialist cascade | before any model call on a skeleton, Lean itself tries `omega / simp_all / positivity / norm_num / nlinarith / decide +kernel / aesop`, then `exact?`, then an optional external `--subgoal-prover module:function`; the log records which component closed each hole | always (`--no-cascade` to ablate) |
| ensembles | `--models a,b` rotates models across agentic attempts from round 2; a cheap critic call reviews the failed plans before each agentic round; agentic sessions continue from the best previous sandbox (files + summary) | round ≥ 2 |
| budgets | `--run-budget` stops cleanly with exit 2; per-call caps by stage (triage $1, judges $2.5, formalize $4, proof $8); a proof call that overruns its cap escalates to the agentic mode; token counts (in/out/cache read/write) are logged next to every cost | always |

Exit codes: `0` proved and verified · `3` partial results only · `2` not proved (including a clean budget stop) · `1` infrastructure/provider failure (resumable).
Every report states the outcome, the mode tried, and why the run stopped.

### Dependency-aware research campaigns

`python3 harness.py campaign status --manifest campaigns/bsd/campaign.json` shows an explicit research graph with exact formal contracts, unresolved gaps, and separate numerical/literature evidence. `next` selects ready obligations; `run --node ID` performs bounded repair attempts; `verify --node ID --candidate FILE` independently checks supplied proofs. Certificates invalidate when their contracts, dependencies, artifacts or verification environment change. Budgets persist across nodes and restarts.

The [BSD campaign notes](campaigns/bsd/README.md) document the reviewed rank-two CM route, its missing implications, commands, and verification boundaries. The included curve checks are infrastructure tests, not BSD proofs or evidence of a higher autonomous solve rate. This is an opt-in layer; existing `run`, `program`, and learning workflows remain available.

### Recovery from interrupted proof runs

A resumed run rechecks complete `sandbox/*/Attempt.lean` artifacts before spending another proof round. Private helper placement and a narrow class of redundant finite-case tactics and no-progress simplifications can be repaired mechanically in at most two passes; every recovered artifact must still pass the frozen-statement guard, Lean, the no-gap check, and the axiom audit. Final verification checks the saved proof without applying this tactic repair.

Mechanical verification is saved before the language audit. A provider outage therefore preserves that milestone while leaving semantic verification incomplete. Account-credit failures stop immediately. Failed-call costs are counted when the provider reports them; unavailable costs remain labelled unavailable. A bounded literature lookup can fall back to supplied source notes, but authentication and account-limit failures do not trigger that fallback.

`--informal-context notes.md` attaches explicitly attributed informal guidance to a run; this makes the run assisted. External Lean files and Lean code fences are rejected. `geometry_witness.affine_blocking_witness` converts exact projective point configurations into rational affine coordinates and checks their incidence certificate; it is a precheck, and Lean must still prove the target. Neither option was used to seed the three proof-generation runs in [the September candidate experiment](experiments/atlas-top3/REPORT.md).

## Sources and credits

- Problem statements, statuses and discussion come from [erdosproblems.com](https://www.erdosproblems.com),
  maintained by T. F. Bloom, and the open-problem metadata from
  [teorth/erdosproblems](https://github.com/teorth/erdosproblems). `atlas-data/forum/` keeps snapshots of the
  site's problem pages and forum threads, which the Atlas and the literature stage read. Their text and
  comments belong to the site and to the people who wrote them.
- `experiments/atlas-top3/275-paper.pdf` and its text are P. Balister, B. Bollobás, R. Morris,
  J. Sahasrabudhe and M. Tiba, "Covering intervals with arithmetic progressions", the paper that experiment
  worked from. Copyright belongs to its authors.
