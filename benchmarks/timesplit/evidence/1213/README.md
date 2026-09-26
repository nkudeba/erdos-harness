# #1213: the verified proofs (dev split)

Benchmark runs never write `knowledge/solved/`, and `runs/` is not tracked. This directory is therefore the durable
copy of the one time-split solve. It is evaluation evidence only, like `../../ideas/`: no harness stage, prompt or
lemma store may read it.

**The statement.** Let a, K ≥ 1. Take a strictly increasing sequence of integers starting at a, with gaps at most K,
that is long enough. Must two distinct intervals of it have equal sums? The frozen Lean statement is
formal-conjectures@077138338750 `ErdosProblems/1213.lean` main theorem, with `answer(True)` stripped
(`../../masks/1213.json`). The answer is True, first public 2026-04-21, and the probe verdict is `unaware`.

| | original | replication |
|---|---|---|
| tag | `discover-v2-84f21c5` (the operator's dev lane) | `replicate-1213-84f21c5` |
| alias | 82251 | 59388 |
| started | 2026-09-25 08:36Z | 2026-09-25 18:16Z |
| cost, wall | $2.64, 22 min | $3.92, 37 min |
| certified hypotheses | 4, 0 open, 0 published | 3, 0 open, 0 published |
| proof | `original/Erdos82251.lean` | `replication/Erdos59388.lean` |
| audit | PASS, 13 of 13 | PASS, 13 of 13 |

- **Protocol.**
  - Both runs: pin `pin_84f21c561c540e02_harness.py` (tracked for this reason) with the knowledge snapshot
    `../../pins/knowledge-8b5a5b08da0eb6f4/`, masked, `--benchmark`, $8, 6 research cycles.
  - Discovery: `--candidate discover-v2 --discover-attempts 2 --discover-budget 0.8 --discover-effort medium
    --gap-budget 1.2 --gap-effort medium`.
  - `discovery.json` holds each run's informal attempts. The original's included a complete proof at confidence
    0.93, which is the route the harness formalized.
- **Baseline.** Baseline v2 without discovery, on the same pin, did not solve it (`baseline-v2-84f21c5-1213`,
  $7.48). The true direction was left one hypothesis short.

**Re-verify** (no model calls):

```bash
cd formal && lake env lean ../benchmarks/timesplit/evidence/1213/original/Erdos82251.lean   # silent = no errors
```

Append `#print axioms erdos_82251` to a copy to see `[propext, Classical.choice, Quot.sound]`. The full audit
(`python3 audit.py --run <run_dir>`) needs the original run directory, because it also checks provenance and
blindness. Its reports are the `AUDIT.md` files here.

**What it is.** A machine-verified, blind re-derivation of a result published on 2026-04-21, by a model that, asked
directly, does not know it. It is evidence about the harness, not new mathematics.
