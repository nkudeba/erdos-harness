# #678, assembled (train): a complete Lean proof, NOT an autonomous solve

This is evaluation evidence only, like `../../ideas/`: nothing the harness runs may read it.

**The statement.** Are there infinitely many n, m and k ≥ 3 with m ≥ n + k and lcm(n+1, …, n+k) > lcm(m+1, …,
m+k+1)? The frozen statement is formal-conjectures' main theorem with `answer(True)` stripped. It is a train item.

**How the proof was put together.**
- **The run** (`train-conv-fde7891`, alias 28730, pin `fde7891`, $13.56):
  - discovery wrote one complete refereed proof;
  - the deductive program certified 12 of 15 steps;
  - the last three (`hyp_loss_hyp_small`, `_div`, `_p`, lemmas about counting multiples) were never attacked,
    deferred for `--min-child-budget` with $2.44 left.
- **A replay** (`benchmarks/timesplit/analysis/replay_sweep.py`, list `../../analysis/deferred_678.json`) gave each of
  the three the cheap one-shot attempt. All three were proved, for $0.73 in total.
- **Assembly:** the three proofs were spliced into the run's final `Residual.lean` with `splice_hypothesis` and
  compiled under the run's own import header, giving `Erdos28730_assembled.lean`.

**Checks.** `audit.lean_checks` passes all 7:
- compiles, no `sorry`;
- axioms `[propext, Classical.choice, Quot.sound]`;
- kernel replay;
- elaborated statement identity (`erdos_28730` and `Finset.lcmInterval`).

**What it is.**
- A machine-checked proof of #678's formal statement.
- Its last step was done outside the run, so it is not a harness solve and is not scored as one.
- It is the evidence behind `--cheap-fallback on`. A fresh run on a pin carrying the fallback is the real test.
