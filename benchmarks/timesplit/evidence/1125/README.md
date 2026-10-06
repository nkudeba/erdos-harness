# #1125: found and proved end to end, unaided (dev item)

This is evaluation evidence only. Nothing the harness runs may read it.

**The statement.** If f: ℝ→ℝ satisfies 2f(x) ≤ f(x+h)+f(x+2h) for every x ∈ ℝ and h > 0, then f is monotone. The
frozen statement is formal-conjectures' main theorem with `answer(True)` stripped. #1125 is a time-split DEV item: posed
in 1984, resolved on erdosproblems.com in April 2026.

**How it was found and proved.**
1. **The research engine on the whole problem**, run by step 2 of the idea-engine experiment
   (`timesplit.py discover-screen --discover-mode engine`, tag `engine-v5-dev`). The run is
   `runs/20261006-021530-371610-discover-erdos77933`, $13.04.
   - It was masked, framed as open, with no "resolved" cue and no library.
   - The engine named no problem number (`recognized: []`).
   - Its deep dive wrote `deep/C1`, a 3,883-character elementary proof, in `engine_proof.md`. Both the step referee
     and the adversary passed it, and both settles judges agree it answers the problem: true.
2. **The deductive Lean loop, with that proof as its blueprint** (`experiments/idea-engine-2026-10-02/hardsteps_lean.py
   --full-run --chain`, `runs/20261006-100843-326327-hardlean-erdos877933`, $2.79, 46 minutes).
   - The blueprint had 12 steps and the first skeleton 10 hypotheses.
   - All 10 were certified: 4 by depth children and 6 by cheap one-shot attempts.
   - No re-plan, no recursion, no operator action after launch.
3. **The audit** (`AUDIT.md`): **PASS on all 13 checks**, re-run on 2026-10-06 at 16:05 UTC.
   - The 7 Lean checks:
     - source scan, imports, compiles, no `sorry`;
     - axioms `[propext, Classical.choice, Quot.sound]`;
     - statement identity of the proved theorem with a clean elaboration of the frozen statement;
     - kernel replay.
   - The 6 blindness checks:
     - provenance: formal-conjectures' statement;
     - direction matches the recorded answer;
     - the faithfulness judges;
     - probe `unaware`;
     - masked `--benchmark` run;
     - no identity in any of the 70 prompts.
   - The prompts scanned include the engine run's own prompts, so the check covers the whole chain.
   - **Correction.** The first audit's verdict was FAIL, not PASS: the Lean stage wrote no time-split record, so
     `benchmark_record` failed before any blindness check ran. That audit passed only the 7 Lean checks. The Lean stage
     now writes its record (`results/engine-v5-dev-lean.jsonl`), and this row was backfilled with
     `hardsteps_lean.py --record-only`.

**A recall signal, reported by the audit.** Five engine responses say "Erdős", all from the novelty judges, none from
the session that wrote the proof.
- They placed the statement as Kemperman's inequality on the Erdős problems list.
- They believed the general case still open.
- They could not recall the problem number or its status.

So the judges knew the problem family, not its April 2026 resolution.

**What it is.**
- A machine-checked proof of #1125's formal statement, found and formalized by the harness without the answer, a cue
  or a proof route from anyone. For a problem resolved in the literature, an audit pass is the verification.
- **It is not new mathematics:** the problem was resolved in April 2026.
- **The model's memory cannot be excluded.** Its knowledge cutoff, June 2026, is after the resolution, and it did not
  name the problem. Whether its route matches the published one has not been compared.
- **Operator involvement:** the experiment's protocol, written before launch; the decision to run the Lean stage on the
  engine's complete claim, which the engine itself had marked complete; and the parallel lanes. No mathematical input.

**Cost:** $15.83 in all (engine $13.04, Lean $2.79).

## Files

- `Proof.lean` (562 lines), `AUDIT.md`, `AUDIT.json`, `SUMMARY.line`.
- `engine_proof.md`: the informal proof the blueprint came from, with its referee and adversary verdicts.
- `engine_IDEAS.md`: the engine run's claims and verdicts.
