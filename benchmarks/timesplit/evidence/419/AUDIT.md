# Audit: PASS

- run: `runs/20261020-172154-145563-hardlean-erdos42884`
- at: 2026-10-20T23:55:41Z
- proof: `runs/20261020-172154-145563-hardlean-erdos42884/final/Erdos42884.lean` (sha256 819f2a16a85bd1bf…)
- benchmark: #419 (dev), tag `dev-scout-baseline-20a1462-lean`, alias 42884

| check | result | detail |
|---|---|---|
| source_scan | pass | no sorry, kernel bypass or elaboration-time code |
| imports | pass | 4 import(s), all Mathlib, Formal.Library or the statement's own |
| compiles | pass | no errors |
| no_sorry_warning | pass | 0 sorry warning(s) |
| axioms | pass | [Classical.choice, Quot.sound, propext] |
| statement_identity | pass | the proved `erdos_42884` and 2 frozen definition(s) are structurally identical to a clean elaboration of the frozen statement (3 constant(s) compared) |
| kernel_replay | pass | all declarations replayed |
| comparator | pass | the proof matches the challenge statement (2 definition(s) compared), on the permitted axioms, through the Lean kernel; sandbox: none (fake-landrun shim) |
| nanoda | pass | the independent nanoda kernel accepts the proof |
| provenance | pass | the pos direction of the benchmark's statement (google-deepmind/formal-conjectures@077138338750 FormalConjectures/ErdosProblems/419.lean (main theorem; answer stripped; comments removed; identity renamed)) |
| direction_matches_answer | pass | proved pos, recorded answer True (formal-conjectures assertion, category 'research solved') |
| faithfulness_judges | pass | at build: True; at verification: True |
| probe | pass | probe verdict: unaware |
| masked_benchmark_run | pass | masked=True, --benchmark=True, knowledge=lemma store excluded (--benchmark) |
| no_identity_in_prompts | pass | 136 prompt(s) scanned; matches: {'problem number with context': 0, 'Erdős by name': 0} |

Other verified runs of this item: 0

Model responses naming the problem (a recall signal, not a leak): {'problem number with context': 0, 'Erdős by name': 18}

PASS means: Lean's kernel accepts a proof of exactly the frozen statement's meaning, on the standard axioms, with nothing that bypasses the kernel; and, for a benchmark item, that statement is the benchmark's own and the run was blind by every check above. It certifies the proof, not the novelty: a reconstruction of a published result stays a reconstruction.
