# Audit: FAIL

- run: `runs/20261003-004608-866727-hardlean-erdos727285`
- at: 2026-10-03T11:19:34Z
- proof: `runs/20261003-004608-866727-hardlean-erdos727285/final/Erdos727285.lean` (sha256 bdac6d6803f22362…)
- benchmark: #None (None), tag `None`, alias None

| check | result | detail |
|---|---|---|
| source_scan | pass | no sorry, kernel bypass or elaboration-time code |
| imports | pass | 5 import(s), all Mathlib, Formal.Library or the statement's own |
| compiles | pass | no errors |
| no_sorry_warning | pass | 0 sorry warning(s) |
| axioms | pass | [Classical.choice, Quot.sound, propext] |
| statement_identity | pass | the proved `erdos_727285` and 2 frozen definition(s) are structurally identical to a clean elaboration of the frozen statement (3 constant(s) compared) |
| kernel_replay | pass | all declarations replayed |
| benchmark_record | FAIL | no time-split record points at this run |

PASS means: Lean's kernel accepts a proof of exactly the frozen statement's meaning, on the standard axioms, with nothing that bypasses the kernel; and, for a benchmark item, that statement is the benchmark's own and the run was blind by every check above. It certifies the proof, not the novelty: a reconstruction of a published result stays a reconstruction.
