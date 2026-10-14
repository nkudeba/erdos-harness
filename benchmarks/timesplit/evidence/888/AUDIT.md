# Audit: FAIL

- run: `benchmarks/timesplit/evidence/888/Proof.lean (assembled; frozen statement and records from runs/20261013-234514-534186-hardlean-erdos41635)`
- at: 2026-10-14T20:03:19Z
- proof: `benchmarks/timesplit/evidence/888/Proof.lean` (sha256 8c302357b8fb0b53…)
- benchmark: #888 (dev), tag `program-v1-dev-lean`, alias 41635

| check | result | detail |
|---|---|---|
| source_scan | pass | no sorry, kernel bypass or elaboration-time code |
| imports | pass | 12 import(s), all Mathlib, Formal.Library or the statement's own |
| compiles | pass | no errors |
| no_sorry_warning | pass | 0 sorry warning(s) |
| axioms | pass | [Classical.choice, Quot.sound, propext] |
| statement_identity | pass | the proved `erdos_41635` and 2 frozen definition(s) are structurally identical to a clean elaboration of the frozen statement (3 constant(s) compared) |
| kernel_replay | pass | all declarations replayed |
| comparator | pass | the proof matches the challenge statement (2 definition(s) compared), on the permitted axioms, through the Lean kernel; sandbox: none (fake-landrun shim) |
| nanoda | pass | the independent nanoda kernel accepts the proof |
| provenance | pass | the pos direction of the benchmark's statement (google-deepmind/formal-conjectures@077138338750 FormalConjectures/ErdosProblems/888.lean (main theorem; answer stripped; comments removed; identity renamed)) |
| direction_matches_answer | pass | proved pos, recorded answer True (formal-conjectures assertion, category 'research solved') |
| faithfulness_judges | FAIL | at build: True; at verification: None |
| probe | pass | probe verdict: unaware |
| masked_benchmark_run | pass | masked=True, --benchmark=True, knowledge=lemma store excluded (--benchmark) |
| no_identity_in_prompts | FAIL | 552 prompt(s) scanned; matches: {'problem number with context': 0, 'Erdős by name': 8} |

Other verified runs of this item: 0

Model responses naming the problem (a recall signal, not a leak): {'problem number with context': 0, 'Erdős by name': 34}

PASS means: Lean's kernel accepts a proof of exactly the frozen statement's meaning, on the standard axioms, with nothing that bypasses the kernel; and, for a benchmark item, that statement is the benchmark's own and the run was blind by every check above. It certifies the proof, not the novelty: a reconstruction of a published result stays a reconstruction.
