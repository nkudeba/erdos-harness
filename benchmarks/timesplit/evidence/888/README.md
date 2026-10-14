# #888: the research engine's chain, proved in Lean, with the last two premises finished by the operator (dev item)

This is evaluation evidence only. Nothing the harness runs may read it.

**The statement.** Let A ⊆ {1, …, n} be such that whenever a ≤ b ≤ c ≤ d are in A and abcd is a square, ad = bc.
Then the largest such A has size Θ(n·log log n / log n).
- The frozen statement is formal-conjectures' main theorem with `answer(True)` stripped. It commits to that Θ form,
  which the faithfulness judge noted at build time: a proof settles the English question up to constants.
- #888 is a time-split DEV item. erdosproblems.com records it as proved by GPT-5.5 Pro (prompted by Chojecki).
- So this is a **reconstruction of a published result, never new mathematics.**

**It is not an autonomous solve.** It was finished by hand, as below. The time-split record of the Lean run stays
`solved: false`.

## How it was put together

1. **The research engine on the whole problem** (`runs/20261013-211446-601153-discover-erdos41635`, $37.24).
   - REPORT 3.11, tag `program-v1-dev`: masked, framed as open, no "resolved" cue.
   - The research program closed its skeleton in one cycle. Its assembled chain `program/C4` passes both settles
     judges, and the engine never named #888 (`recognized_true` false).
   - It did name a related problem, #121.
2. **The deductive Lean loop with that chain as its blueprint** (`runs/20261013-234514-534186-hardlean-erdos41635`,
   `hardsteps_lean.py --claim program/C4 --full-run --chain`, $94.09).
   - It ended with 17 certified lemmas, 0 open conjectures and 2 published premises: Rosser–Schoenfeld 1962,
     π(x) < 1.25506·x/log x for x > 1, and π(x) > x/log x for x ≥ 17.
   - Two operator-funded resumes, recorded in the run's `assistance` field:
     - the stall counter was reset and the budget raised to $75;
     - then reset again, raised to $95, with `--child-cycles 4 --residual-depth 3`.
3. **The finish, by the operator (a Claude Code session), 2026-10-14. No harness model calls.**
   - **The two premises came out.** The pieces never needed Rosser–Schoenfeld's constants, only Chebyshev-strength
     bounds.
   - **π(x) < 5·x/log x for x > 1** (`erdos_41635_cheb_upper5`). It follows from Mathlib's
     `Chebyshev.pi_le_log4_mul_div`, which gives π(x) ≤ log 4·x/log √x + √x. The bound log x < 2√x does the rest:
     2·log 4 + 2 < 5. The run already imported that module.
   - **The dyadic bounds that `box_part` used the premises for**, now proved outright from the central binomial
     coefficient. This is Erdős's proof of Bertrand's postulate, kept quantitative:
     - n^#P ≤ C(2n, n) ≤ 4^n, where P is the set of primes in (n, 2n]. So #(primes in [2^j, 2^(j+1))) ≤ 4·2^j/(j+1).
     - C(2n, n) ≤ (2n)^√(2n) · 4^(2n/3) · (2n)^#P, and 4^n < n·C(2n, n). So #(primes in [2^j, 2^(j+1))) ≥
       2^j/(2(j+1)) for j ≥ 80. The old lemma claimed it for j ≥ 5, but its only use was at j ≥ 80.
   - **The pieces were re-pointed:**
     - `hyp_rough`: hypothesis 1.26 → 5, its constant 3 → 6.
     - `hyp_smooth_tail`: 1.26 → 5, 2.52 → 10, 50.4 → 200. The proofs are unchanged apart from these constants.
     - `hyp_box_part`: no hypothesis at all.
     - The glue: no premise.
   - The new lemmas are about 200 lines of textbook number theory, written and compiled by the operator's session.
     They are not the harness's work. Everything specific to #888 is the harness's own: the engine's chain, the
     17 certified lemmas, and the glue.
   - `assemble.py` performs every edit on the run's final `Residual.lean`, asserting each pattern's count. The result
     was compiled under the run's own import header plus `Mathlib.NumberTheory.Bertrand`. That is `Proof.lean`.

## Checks

`AUDIT.md`, from `audit.lean_checks` on `Proof.lean` against the Lean run's frozen statement, plus `audit.benchmark_checks`
on the Lean run. **13 of 15 pass; the verdict is FAIL.**

- **All 9 Lean checks pass:**
  - source scan, imports, compiles, no `sorry`;
  - axioms `[propext, Classical.choice, Quot.sound]`;
  - statement identity of `erdos_41635` and its 2 frozen definitions with a clean elaboration of the frozen statement;
  - kernel replay;
  - Comparator (without its sandbox: macOS has no Landlock);
  - the independent nanoda kernel.
- **So the proof is mechanically verified:** Lean's kernel, and a second kernel, accept a proof of exactly the frozen
  statement.
- **Two protocol checks fail:**
  - **`faithfulness_judges`: at build True; at verification, not run.** The Lean run never reached its own
    verification stage, and no judge was run outside the protocol to fill the row.
  - **`no_identity_in_prompts`: 8 of 552 prompts contain "Erdős" by name.**
    - All 8 are in the ENGINE run's prompts, none in the Lean run's.
    - Every one is the model's own citation of a classical result, carried from one session's notebook into later
      prompts: "Erdős's bound π(x) + O(x^{3/4})" for multiplicative Sidon sets, "textbook Erdős 1964" (the box lemma),
      "Erdős–Sárközy–Sós 1995".
    - None names the problem or its number. But the masked protocol does not scrub a model-written "Erdős's", and the
      check counts it.
    - 30 distinct responses say "Erdős": 25 in the engine run and 5 in the Lean run. The audit's 34 counts the
      research program's transcripts twice. On #1125 the count was 5. The model knew the literature around the
      problem; it did not name #888.
- The probe was `unaware`, the run was masked and `--benchmark`, and the direction matches the recorded answer.

## What it shows about the harness

- **The plan asked for more than it needed.** Both premises were written with Rosser–Schoenfeld's exact constants,
  which Mathlib cannot prove. The pieces needed only some constant, and the module that gives one was already in the
  run's imports. This is the Nagura lesson again, with a cheaper way out: generalize the constant before citing the
  sharp form.
- The lower bound was the real gap. Mathlib has Bertrand's postulate, but no count of primes in a dyadic interval.
  Mathlib's own central-binomial lemmas give one in about 150 lines.

## Cost

- **Harness:** $131.33 (engine $37.24, Lean $94.09).
- **The finish:** no harness spend. It was done in the operator's Claude Code session.

## Files

- `Proof.lean`: the full statement, assembled. `AUDIT.md` and `assembled-checks.json` hold its checks.
- `assemble.py`: the edits, from the run's `Residual.lean` to `Proof.lean`.
- `RESIDUAL_final.md`: the Lean run's final residual, before the finish. `LeanRun_SUMMARY.line` is its summary line.
- `engine_IDEAS.md`: the engine run's claims and verdicts.
