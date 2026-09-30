# #1037, assembled (train): a complete Lean disproof, NOT an autonomous solve

This is evaluation evidence only: nothing the harness runs may read it.

**The run** (`train-v4-543fd9d`, alias 95105, pin `543fd9d`, $7.72):
- discovery wrote a complete refereed disproof in round 1 and committed to NO;
- the deductive program certified 3 steps with no conjecture left open;
- ONE published premise stayed open: Erdős 1947, Ramsey graphs with no clique or independent set larger than
  C·log r exist;
- `--premise-attack cheap`, that pin's default, gave the premise only the free tactics.

**The completion:**
- A replayed full attack (`analysis/replay_sweep.py --full --budget 5`, list `../../analysis/premise_1037.json`)
  proved Erdős's bound in Lean for $2.70.
- Spliced into the run's residual under its own imports, it gives `Erdos95105_assembled.lean`.

**Checks.** `audit.lean_checks` passes all 7:
- compiles, no `sorry`;
- standard axioms;
- kernel replay;
- elaborated statement identity with the frozen NO statement.

**What it is.** A machine-checked disproof of #1037's formal statement. It is not a harness solve, because the last
step ran outside the run. `--premise-attack full` is the default again (2026-09-30), and it would have run exactly
this attack.
