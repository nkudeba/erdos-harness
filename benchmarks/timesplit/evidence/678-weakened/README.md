# #678 after premise weakening (train, 2026-10-15): two audited proofs, NOT autonomous solves

This is evaluation evidence only: nothing the harness runs may read it.

**The replays.** `analysis/replay_weaken.py` ran the premise-weakening move (`--premise-weaken on`, harness `b1762b5`)
on the final state of three train runs of #678. Each run had ended with every conjecture certified and only published
premises open. In each replay:
- one proposal call stated the weakest premise the glue uses: eventually, a prime in about ((k+1)/2, k−1];
- one direct attack certified that premise from Mathlib's Bertrand machinery;
- the swap was adopted.

Details and costs ($7.52 in all) are in `../../RESULTS.md`, "Premise weakening".

**Files.**
- `55963_proof.lean`: run 55963's residual exactly as the replay left it. Ramanujan's premise is replaced by the
  certified `hyp_bertrand_gap`, and nothing is open.
- `81727_proof.lean`: run 81727's replay residual, with Nagura replaced by the certified `hyp_halfprime`. Nair is spliced
  in from the 2026-09-30 premise replay (`runs/replay-premises-678c/81727-erdos_81727_hyp_nair`, $1.53).
- `assemble.py` rebuilds both from the replay directories. It compiles each under its run's header, plus the modules the
  replay auto-imported (`Mathlib.NumberTheory.Bertrand`, `Mathlib.NumberTheory.Primorial`), and runs
  `audit.lean_checks`. `55963-checks.json` and `81727-checks.json` are its output.

**Checks.** Both pass all 7 of `audit.lean_checks`:
- compiles, no `sorry`;
- standard axioms;
- kernel replay;
- imports trusted;
- source scan;
- elaborated statement identical to the frozen one (`erdos_<alias>`, `Finset.lcmInterval`).

**What they are.**
- Two more machine-checked proofs of #678's formal statement, by the route the premise-weakening move opens.
- Neither is a harness solve. Each replay started from a saved final state, outside its run, and 81727's last step
  comes from a different replay.
- They show what the move would have done in-run:
  - closed 55963 by itself, within the about $4 that run left unspent;
  - closed 81727 together with the endgame's attack on Nair. That needs about $4.05, more than the $2.70 its endgame had.
