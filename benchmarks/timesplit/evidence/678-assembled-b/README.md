# #678, assembled again (train): a complete Lean proof, NOT an autonomous solve

This is evaluation evidence only: nothing the harness runs may read it.

**The run** (`train-678-fallback-543fd9d`, alias 55963, pin `543fd9d`, $11.70):
- discovery wrote two complete refereed proofs;
- the deductive program closed every conjecture (4 certified);
- the run stopped with ONE published premise open, `hyp_ramanujan`: for x ≥ 11 there are primes p < q in (x/2, x]
  (Ramanujan 1919; Mathlib has only Bertrand's single prime).

**Why it stopped:** `--premise-attack cheap`, then the default, gave the premise only the free tactics.

**The completion:**
- A replayed full attack (`analysis/replay_sweep.py --full --budget 4`, list `../../analysis/premise_678.json`)
  proved the premise for $3.22, in its first agentic round.
- It was spliced into the run's `Residual.lean` and compiled under the run's own header, giving
  `Erdos55963_assembled.lean`.

**Checks.** `audit.lean_checks` passes all 7:
- compiles, no `sorry`;
- standard axioms;
- kernel replay;
- elaborated statement identity (`erdos_55963`, `Finset.lcmInterval`).

**What it is.** A second machine-checked proof of #678's formal statement, reached by a different route from
`../678-assembled/`. It is not a harness solve, because the last step ran outside the run. It is the evidence
behind returning `--premise-attack` to `full`.
