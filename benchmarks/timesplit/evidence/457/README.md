# Time-split dev #457: Lean-verified, operator-assisted, audit FAIL (not a solve)

- **What is proved:** formal-conjectures' main theorem for #457 (answer stripped, comments removed, identity
  renamed to `erdos_95799`), the TRUE direction. `Proof.lean` compiles sorry-free on `[propext, Classical.choice,
  Quot.sound]`.
  - `AUDIT.md` passes 14 of 15 checks: kernel replay, Comparator, nanoda, statement identity, provenance, faithfulness
    judges and the probe among them.
  - It FAILS `no_identity_in_prompts`. One engine deep-dive prompt carried the model's own note, from an earlier
    session's notebook, to "check erdosproblems.com". It names the site, never the problem number. This is the same
    failure as #888's.
- **Route:**
  - The campaign's scout settings (iteration 5, Arm C, pin `20a146201f4a59bb`) settled it informally for $15.31, with
    claim `r1s2/C1`.
  - The Lean stage then ran via `hardsteps_lean.py --full-run --chain`.
- **Lean stage, $21.07 over four invocations:**
  1. The session limit stopped it ($1.50).
  2. It stalled with no skeleton adopted, on a missing `noncomputable` ($2.55). Fixed in `8b00676`.
  3. 13 of 14 steps certified ($12.01). It stopped at its 4-cycle cap. The last step had been rejected unattempted in
     every cycle by a duplicate-definition bug, fixed in `057328b`.
  4. Two resumes by the operator's agent. The first raised the cycle cap ($0.42). The second reset the stall counter
     ($4.59). The last step was certified in 13 minutes, and the residual closed.
- **Why it is not a solve:** the resumes are assistance (`state.json` → `assistance`), and the audit fails one
  blindness check.
  - No proof text or route was supplied at any point.
  - It is also a reconstruction of a result published in 2026, not new mathematics.
  - One intent judge suspected the formal statement is easier than the problem as intended.
- **To make it count:** a fresh alias, end to end, on a harness with both fixes. That means the scout, then the Lean
  stage with its defaults, with no resume, and an audit that passes.
