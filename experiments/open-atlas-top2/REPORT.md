# Open-problem attempt — Erdős #273 and #677 (2026-09-10/11)

Plain-English write-up: https://claude.ai/code/artifact/06228470-b362-4890-8349-1131a9784bfd

**Neither problem is solved.** Both remain open on erdosproblems.com. Everything below is certified
partial value plus infrastructure findings. Nothing here is a claim on either problem, and no proof
has had independent human review (`claimEligible=false` throughout).

## Selection

`score` (can the harness produce a complete proof) tops out at 25 across the 639 unsolved problems,
with a **20-way tie** — all unreviewed, all with the identical signal breakdown. This is the collapse
CLAUDE.md documents. `partial` narrowed the tie to 8 at (25, 51). From those 8, #273 and #677 are the
only two whose *finite certificate direction* would settle the problem outright:

| # | finite direction | why the other six were dropped |
|---|---|---|
| 273 | YES — exhibit a covering system | 252/288/406/677* need an infinite argument either way |
| 677 | NO — exhibit one colliding pair | 324's witness needs an infinite distinctness proof |

Recorded in `SELECTION.md`. Note the Atlas's own rank order inside the tie is by problem number
(`meta.method`), so "top 2 by rank" (#10, #11) is an artifact, not a judgement.

## #273 — covering system with all moduli `p-1`, `p ≥ 5` prime

Frozen statement audited faithful (finite `Finset`, distinct moduli, moduli ≥ 4 so `p - 1` cannot
truncate in ℕ, empty `S` excluded by the covering clause). The distinctness clause is not in the
site's one-line statement but is the correct reading — without it `{0,1,2,3} mod 4` is a trivial
solution — and matches the forum's treatment.

- **Parity reduction** (this session): every admissible modulus is even, so each class is confined to
  one parity. The problem is exactly **two disjoint covering systems with distinct moduli drawn from
  `H = {m ≥ 2 : 2m+1 prime}`**. Reciprocal budget over smooth `L' ≤ 4·10^6` tops out at 2.30.
- **Search**: the reciprocal screen leaves only 4 values of `L ≤ 120,000`, smallest **55,440**
  (`2^4·3^2·5·7·11`, 43 admissible divisors, density 1.044). The run eliminated everything below it in
  18 s of arithmetic, reached 55,440, and **aborted on its time budget**. So `exhaustive_to: 55439` is
  honest and free — the real search never started.
- **Exhaustive elimination** of the 29 screen-passing candidates up to 393,120 was attempted with a
  density prune and a per-prime-power capacity prune; both inconclusive (>2·10^7 nodes on `L' = 27720`
  alone). The third-party `lcm ≥ 393120` claim was **not** independently confirmed here.
- **Certified** (7 lemmas, recompiled and axiom-audited independently: sorry-free,
  `[propext, Classical.choice, Quot.sound]`) — `knowledge/partial/273/...-pos/`:
  - `erdos_273_density` — every finite covering system with moduli dividing `L` has `Σ 1/mᵢ ≥ 1`.
    The standard density condition, reusable for any covering-system problem.
  - `erdos_273_pool_bound` — distinct moduli from a finite pool `P` force `Σ_{d∈P} 1/d ≥ 1`; the
    screen that kills a candidate lcm without exhibiting a covering.
  - `erdos_273_not_selfridge` — no admissible covering has all moduli dividing 360 (eligible moduli
    `{4,6,10,12,18,30,36,40,60,72,180}`, reciprocal sum `7/9 < 1`). Certifies exactly why Selfridge's
    divisors-of-360 covering needs the modulus `2 = 3-1` that `p ≥ 5` forbids.
- Cost **$17.44**. Atlas: score 25 → **6**, search floor 55,440.

## #677 — `M(n,k) = lcm(n+1..n+k)`; is `M(n,k) ≠ M(m,k)` for `m ≥ n+k`?

Frozen statement matches formal-conjectures exactly.

- **Counterexample search**: none for `k ≤ 12`, `n,m ≤ 2·10^5`. `k = 3` reduces to the single cubic
  `x³ - x = 2(y³ - y)`; exhaustive to `y < 10^9`, sole solution `(y,x) = (4,5)` — that is `n=2, m=3`,
  i.e. `lcm{3,4,5} = lcm{4,5,6} = 60` with `m-n = 1 < k`, which the hypothesis **allows**. Not a
  counterexample.
- **Certified**: the `k ≤ 2` case of the frozen statement, proved by hand (`erdos_677_k_le_two`,
  sorry-free, standard axioms) and independently reached by the run. `Formal/Programs/Erdos677Pos.lean`
  and `Erdos677Neg.lean` build clean, 12 lemmas total. (The raw `programs/erdos_677/*/Lemmas.lean`
  accumulators do not compile standalone — they carry `-- IMPORTS:` directives, not `import` lines;
  the installed modules are the artifacts that matter.)
- **Wall at `k = 3`**: `M(·,k)` stops being monotone (9998 descents for `k=3`, `n<20000`) and the
  problem becomes Thue–Siegel/elliptic. Both the program's own plan and manual reading agree: do not
  spend bounded search there.
- Cost **$34.02** — see the budget bug below; this is ~4× the resume cap and was stopped by hand.
  Atlas: score 25 → **7**, search floor 10^9.

## Infrastructure findings (the more valuable half)

1. **`RUN-SUMMARY` reporting added** (requested). One greppable line per run, on the fatal path too,
   written to `<run_dir>/SUMMARY.line` + `runs/summary-log.tsv`; `harness.py summary` reprints it
   read-only. Documented in `CLAUDE.md`, `AGENTS.md` (new — Codex reads that), `README.md`.
2. **`stage_partial` discarded certified lemmas.** An anchored `re.match` for the declaration name
   returns `None` when a block opens with a `/-- … -/` doc comment; `.group(1)` then raised *after*
   `partial.lean` was written but *before* `report.md`, `state["partial"]` and `partial/saved`. #273's
   7 lemmas survived on disk while the run reported `infrastructure_error` and `lemmas=0`. Fixed
   (`decl_name`), `tests/test_decl_name.py`.
3. **`--run-budget` was unenforceable in `research`/`--open`.** `spent_usd()` read only the run's own
   log; `--open` children and research sub-runs log elsewhere, so the parent never saw their spend and
   the cap never tripped. Compounded by `max(3.0, ...)`, which guaranteed $3 per sub-run with the
   budget already gone. Resumed #677 spent **$22.67 against `--run-budget 8`**. Fixed: spend counts all
   descendants (program logs windowed to this run); sub-runs get `min(remaining, remaining/n)` and the
   cycle stops at zero. `tests/test_budget_accounting.py`.

Also observed, already fixed in-tree before this session's later runs: `--open` ran both directions'
research programs against a shared `programs/erdos_<n>/`, racing on cycle names, `Lemmas.lean` and
`ledger.jsonl` (the `FileNotFoundError` that killed #677's pos direction, and duplicate ledger rows).

Suite: 108 → **122 tests**, all passing.

## Honest summary

Two long shots correctly demoted from a 20-way tie at 25 to individually assessed 6 and 7, with search
floors that stop future runs repeating this ground; three reusable machine-checked results on #273 and
the `k ≤ 2` case of #677; three real harness defects fixed. No mathematics that was not already known,
and no progress on either open question.
