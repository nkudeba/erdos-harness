# Task brief: the covering-systems library

Implements priority 02 ("compounding libraries per cluster") from the harness strategy. Full reasoning:
https://claude.ai/code/artifact/7cff0215-742f-4dff-a32b-a4e633f4995c

## Why this task

The harness has 19 verified proofs and 0 solved open problems. All 19 had a proof route already
available. Each run currently starts from near zero: nothing accumulates except Lean tactics. The
catalogue clusters hard — **22 covering-system problems** (#2, #7, #8, #27, #202, #203, #204, #273,
#274–#281, #586, #947, #1113, #1188–#1190, #275) — so formalising the cluster's core machinery once
should make every later run in it cheaper. That is the hypothesis to test.

## What already exists (do not redo)

- `knowledge/partial/273/20260910-213413-537244-erdos273-pos/partial.lean` — the **density bound**
  (`erdos_273_density`: a finite covering system with moduli dividing `L` has `Σ 1/mᵢ ≥ 1`), the pool
  bound, and `erdos_273_not_selfridge`. Sorry-free, axioms `[propext, Classical.choice, Quot.sound]`.
- `knowledge/partial/273/reductions-formalised/Erdos273_reductions.lean` — the **admissibility sieve**
  (`erdos_273_sieve`: for every prime `q`, an admissible `m` with `q < m+1` has `q ∤ m+1`), evenness,
  **parity confinement** (`erdos_273_parity`), and the 17-smallest reciprocal bound. All sorry-free.
- `knowledge/reductions/273/STRUCTURE.md` — the candidate-lcm structure, the slack ordering, and the
  **root-of-unity condition** with its derivation.
- `knowledge/reductions/273/rootofunity_validation.py` — numerical validation of the identity and of
  the condition, to ~1e-15, against four known covering systems including one with two
  divisibility-maximal moduli.
- Mathlib has `StrictCoveringSystem` with an `injective_mod` field — find it and build on it rather
  than redefining a covering system.

## Deliverables

### 1. `formal/Formal/Library/CoveringSystems.lean`

A real Lean module, not a concatenation. Migrate the existing lemmas into it, restated against one
shared definition (Mathlib's if it fits), and add:

**(a) Mirsky–Newman / Davenport–Rado.** A disjoint covering system of `ℤ` by `≥ 2` congruences must
repeat its largest modulus; hence distinct moduli admit no exact cover. Proved by generating functions
— evaluate `Σᵢ z^{aᵢ}/(1 − z^{mᵢ}) = 1/(1−z)` near a primitive `M`-th root of unity for `M` the largest
modulus; only that term has a pole, and the right side is finite there. This is a **published theorem**;
reconstructing it is not new mathematics and the module must say so in its docstring.

**(b) The root-of-unity condition.** For a covering with excess multiset `E` (`k = |E|`) and any
**divisibility-maximal** `m` (no other modulus in the family is a multiple of it):

    |Σ_{r ∈ E} ζ^r| = L/m   for ζ a primitive m-th root of unity,   hence  L/m ≤ k.

It subsumes (a): `k = 0` demands `L/m ≤ 0`. The script in `knowledge/reductions/273/` validates it
numerically — the Lean proof needs the same pole argument as (a), so do (a) first and share the
machinery.

**Acceptance:** `lake build Formal.Library.CoveringSystems` succeeds; every declaration is sorry-free
with `#print axioms` showing only `propext`, `Classical.choice`, `Quot.sound`; `native_decide` is not
used anywhere (it is banned — see CLAUDE.md).

### 2. Make the library reachable from a run

The research program already installs `programs/erdos_<n>/Lemmas.lean` as an importable module
(`_install_lemmas_module`). Add a cluster-library path so a problem tagged `covering systems` gets
`Formal.Library.CoveringSystems` added to its imports and named in the prove/reduce prompts as
already-available machinery. Do not paste lemma text into prompts; import it.

**Acceptance:** a run on a `covering systems` problem shows the module in its composed header, and the
prove prompt states the library is importable.

### 3. Measure whether it compounded — this is the actual point

Re-run **#273** and then **#7** (`--reduce always`, `--run-budget 20`) against the library and compare
to the recorded baseline for #273 (`runs/20260911-105339-682432-erdos273`: `$12.45`, 23 llm calls, 43
Lean checks, 0 artifacts recorded by the run itself).

Report a table: model calls, Lean checks, spend, and **certified artifacts** per run. Write it to
`experiments/covering-library/REPORT.md`.

**The test:** is the second run visibly cheaper per artifact than the first? If yes, repeat the pattern
for Ramsey (67 problems) and Sidon sets (22). If no, say so plainly — that is a valid and cheap result,
and it falsifies the compounding thesis for the price of one cluster instead of four.

## Rules that outrank convenience

Read `CLAUDE.md` and `AGENTS.md` first; both are current. In particular:

- A compiling Lean proof is **mechanically verified**, never a resolved problem. #273 and #7 stay open.
- Record assistance. If a proof route came from the literature or an operator, it goes in the report.
- Report unavailable costs as unavailable, not as zero.
- Take run facts from `collect_run_facts(run_dir, pid)`, never from one `state.json`.
- Every run writes a plain-language brief; do not disable it.
- `python3 atlas-data/record_finding.py` after each finding, with `--floor-kind` when recording a floor.

## Out of scope

Do not attempt to resolve #273 or #7. Do not add solver time to the `L = 100800` instances — four
attempts have timed out and the next lever there is algebraic, not computational.
