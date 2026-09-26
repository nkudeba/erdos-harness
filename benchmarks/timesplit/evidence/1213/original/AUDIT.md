# Audit: PASS

- run: `runs/20260925-043526-696629-timesplit-erdos82251`
- at: 2026-09-26T14:39:17Z
- proof: `runs/20260925-043526-696629-timesplit-erdos82251/final/Erdos82251.lean` (sha256 3f7c56c0eab3d617…)
- benchmark: #1213 (dev), tag `discover-v2-84f21c5`, alias 82251

| check | result | detail |
|---|---|---|
| source_scan | pass | no sorry, kernel bypass or elaboration-time code |
| imports | pass | 4 import(s), all Mathlib, Formal.Library or the statement's own |
| compiles | pass | no errors |
| no_sorry_warning | pass | 0 sorry warning(s) |
| axioms | pass | [Classical.choice, Quot.sound, propext] |
| statement_identity | pass | the proved `erdos_82251` and 1 frozen definition(s) are structurally identical to a clean elaboration of the frozen statement (2 constant(s) compared) |
| kernel_replay | pass | all declarations replayed |
| provenance | pass | the pos direction of the benchmark's statement (google-deepmind/formal-conjectures@077138338750 FormalConjectures/ErdosProblems/1213.lean (main theorem; answer stripped; comments removed; identity renamed)) |
| direction_matches_answer | pass | proved pos, recorded answer True (formal-conjectures answer(...)) |
| faithfulness_judges | pass | at build: True; at verification: True |
| probe | pass | probe verdict: unaware |
| masked_benchmark_run | pass | masked=True, --benchmark=True, knowledge=benchmarks/timesplit/pins/knowledge-8b5a5b08da0eb6f4 |
| no_identity_in_prompts | pass | 12 prompt(s) scanned; matches: {'problem number with context': 0, 'Erdős by name': 0} |

Other verified runs of this item: 1
- `replicate-1213-84f21c5` alias 59388: `runs/20260925-141600-634401-timesplit-erdos59388`

Model responses naming the problem (a recall signal, not a leak): {'problem number with context': 0, 'Erdős by name': 1}

PASS means: Lean's kernel accepts a proof of exactly the frozen statement's meaning, on the standard axioms, with nothing that bypasses the kernel; and, for a benchmark item, that statement is the benchmark's own and the run was blind by every check above. It certifies the proof, not the novelty: a reconstruction of a published result stays a reconstruction.
