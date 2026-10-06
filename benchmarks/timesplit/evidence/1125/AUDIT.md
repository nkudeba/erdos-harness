# Audit: FAIL

- run: `runs/20261006-100843-326327-hardlean-erdos877933`
- at: 2026-10-06T14:55:10Z
- proof: `runs/20261006-100843-326327-hardlean-erdos877933/final/Erdos877933.lean` (sha256 7e426d1afa91beaf…)
- benchmark: #None (None), tag `None`, alias None

| check | result | detail |
|---|---|---|
| source_scan | pass | no sorry, kernel bypass or elaboration-time code |
| imports | pass | 5 import(s), all Mathlib, Formal.Library or the statement's own |
| compiles | pass | no errors |
| no_sorry_warning | pass | 0 sorry warning(s) |
| axioms | pass | [Classical.choice, Quot.sound, propext] |
| statement_identity | pass | the proved `erdos_877933` and 0 frozen definition(s) are structurally identical to a clean elaboration of the frozen statement (1 constant(s) compared) |
| kernel_replay | pass | all declarations replayed |
| benchmark_record | FAIL | no time-split record points at this run |

PASS means: Lean's kernel accepts a proof of exactly the frozen statement's meaning, on the standard axioms, with nothing that bypasses the kernel; and, for a benchmark item, that statement is the benchmark's own and the run was blind by every check above. It certifies the proof, not the novelty: a reconstruction of a published result stays a reconstruction.
