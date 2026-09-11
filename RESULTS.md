# Results — 2026-07-10

Two real Erdős problems, both taken from English statement to a verified Lean 4 proof by the
harness pipeline (literature → autoformalize → adversarial cross-check → frozen-statement proof
search → layered verification), with independent adversarial audits afterwards.

## Erdős #493 — PROVED & VERIFIED (all clear)

> Does there exist a k such that every sufficiently large integer can be written in the form
> ∏ᵢ aᵢ − ∑ᵢ aᵢ for some integers aᵢ ≥ 2?  — solved affirmatively (Eli Seamans; k = 2)

- Run dir: `runs/20260710-174820-erdos493/` · final artifact: `final/Erdos493.lean`
- Formalization: 4 independent candidates generated, all compiled; adversarial judge picked the
  most literal ℤ encoding; frozen statement matches DeepMind formal-conjectures' expert statement
  (ours strictly stronger: extra `0 < k`).
- Proof: found in round 1 (witness `![n+2, 2]`, `omega` + `ring`). 3/3 attempts compiled.
- Verification: sorry-free; `#print axioms` = `[propext, Classical.choice, Quot.sound]`; blind
  back-translation judged faithful; 4-skeptic audit (live-site statement, vacuity/direction,
  formal-conjectures diff, byte-level soundness incl. hexdump) — **0 refutations**.
- Honest caveat (raised by the auditors, correctly): the problem as recorded is mathematically
  trivial — the run demonstrates the pipeline, not mathematical depth.

## Erdős #674 — PROVED & VERIFIED (all clear)

> Are there any integer solutions to x^x·y^y = z^z with x, y, z > 1?  — solved affirmatively
> (Chao Ko, 1940)

- Run dir: `runs/20260710-190011-erdos674/` · final artifact: `final/Erdos674.lean`
- The interesting one: any witness has astronomically large x^x, so brute computation is
  impossible — the prover had to do a real mathematical maneuver. The accepted proof introduces
  an abstract helper lemma reducing `(2¹²·3⁶)^X · (2⁸·3⁸)^Y = (2¹¹·3⁷)^Z` to two linear exponent
  identities (`12X+8Y = 11Z`, `6X+8Y = 7Z`) via a `mul_pow`/`pow_mul`/`pow_add` rewrite chain,
  then instantiates Ko's witness with `norm_num` closing the small arithmetic.
- Round 1: 2/3 attempts compiled; the naive numeral-witness attempt timed out at 420 s —
  exactly the failure mode the harness's timeout guard exists for.
- Verification: sorry-free; axioms = standard triple; ℕ-vs-ℤ domain shift judged harmless
  (x,y,z > 1 makes them coincide); blind back-translation faithful. 4-skeptic audit — **0
  refutations**, including an independent exact-bignum brute-force of the equation in Python.
- Notable: unlike #493, DeepMind's formal-conjectures has NO formalization of #674
  (erdosproblems.com lists "Formalised statement? No"), so this statement + proof were produced
  without any expert reference to lean on.

## Bugs the layered design caught during the build (all fixed in harness.py)

1. Lean's sorry-warning uses backtick quoting → detector missed it (candidates all rejected).
2. Frozen-statement guard polluted by the `-- CANDIDATE n` marker comment → all honest proofs
   rejected pre-compile. Guard is now comment-insensitive on both sides.
3. `#print axioms` output has no `file:line:` prefix → axioms never captured → verification
   failed closed. Now parsed from raw output, including the "does not depend on any axioms" form.
4. `statement_prefix` truncated at the first `:=` (would break on let-binders) — latent, fixed.
5. `json_block` accepted non-dict JSON → crash path. Fixed.
6. `has_banned` flagged the substring "axiom" anywhere (false positives) while the real
   backstop (#3) was broken. Now word-boundary regexes + comment stripping.
7. FileBackend could consume a stale response after resume; counter now derived from all dirs
   and stale `done/` files are deleted at request time.

Every stage of both runs is replayable from `runs/*/transcripts/` (every prompt and response)
and `runs/*/log.jsonl` (every event, timestamped).

---

# Results — 2026-09-07/08: battle test, bug fixes, and the self-improvement layer

Model behind every `claude -p` call: **claude-fable-5-1** (the CLI default here). Budget per run:
`--rounds 3 --decompose-rounds 5`. The original harness was frozen as `harness_baseline.py` for comparison.

## Target selection

Targets were drawn from the 298 problems marked "(Lean)" in `teorth/erdosproblems`, cross-referenced with
`google-deepmind/formal-conjectures` (expert statements) and `plby/lean-proofs` (community Lean proofs).
Ranking community proofs by *transitive* code size (top files often just import a multi-file development)
gave a ladder of self-contained proofs: 399 (8 lines) · 316 (31) · 397 (76) · 363 (108) · 645 (124) ·
198 (135) · 370 (263) · 532 (230) · 1193 (12, but needs a density definition). Problem files use the exact
erdosproblems.com statement and the site's public resolution notes; unlike the July files they contain **no
Lean technique hints**.

## Baseline harness (original code) — all four attempted problems fell in ROUND 1

| # | statement | community proof | baseline result | wall |
|---|---|---|---|---|
| 399 | n! = x^k ± y^k has no solutions with xy>1, k>2 (false: 10! = 48⁴ − 36⁴) | 8 lines | ✅ round 1 | 10 min |
| 645 | every 2-colouring of ℕ has a monochromatic x, x+d, x+2d with d > x | 124 lines | ✅ round 1, ~80-line case analysis following Alweiss's argument | 17 min |
| 397 | finitely many solutions of ∏C(2mᵢ,mᵢ) = ∏C(2nⱼ,nⱼ) with distinct indices (false) | 76 lines | ✅ round 1: proved the c = 8a²+8a+1 identity via `Nat.succ_mul_centralBinom_succ` ratios and an unbounded-`sup` infinitude argument | 20 min |
| 316 | finite A ⊂ ℕ∖{1} with Σ1/n < 2 always splits into two parts with Σ1/n < 1 (false) | 31 lines (`decide +kernel` over 2¹¹ subsets) | ✅ round 1 — **no brute force**: used Sándor's set (proper divisors of 120) and an integrality argument (120·Σ over each part is an integer, total 239/120, so k₁+k₂ = 239 with both < 120) | 14 min |
| 363, 198, 1193 | | | ⏸ not run: the account's usage limit was hit mid-lane (provider error, not a math failure) | |

Honest reading: with Fable 5.1 as the sampler, the original one-shot design already solves everything up to
~125 community-proof lines in one round. The interesting failures were **infrastructure**, found while
reading the code and by a mock end-to-end test, not by the model getting stuck.

## Bugs found in the original harness (all fixed, all covered by tests)

1. **Coded Lean diagnostics were dropped.** Lean ≥ 4.2x emits `path:8:23: error(lean.unknownIdentifier): …`;
   the message regex required a bare `error:` so every such message vanished from the feedback. The prover
   literally never saw "unknown identifier" errors (only uncoded ones like `unsolved goals`).
2. **`autoImplicit` was silently ON.** `lake env lean File.lean` ignores the lakefile's
   `relaxedAutoImplicit = false`, so an unknown identifier inside a *theorem statement* became an implicit
   variable instead of an error — a misspelled `Nat.Prime` in a formalization would compile as a different
   (vacuous) theorem and pass the frozen-statement guard. The composed header now sets `autoImplicit false`.
3. **Failed code was never fed back.** Next-round prompts carried only attempt names and two truncated errors;
   the model could not repair, only regenerate.
4. Noise retrieval: loogle was queried with the first four five-letter English words of the statement
   ("there", "exist", "solutions"), costing up to 80 s of web timeouts per stage for nothing.
5. Helper lemmas named `erdos_397_key` were skipped by the lemma harvester's `startswith("erdos_")` filter.
6. Provider/network errors (`ENOTFOUND`, overloaded, usage-limit) killed whole lanes; now retried with backoff
   when transient, and always distinguished from mathematical failure (exit 1 vs 2).
7. **Unbounded thinking on retrieval-style stages.** At the CLI's default effort the #363 literature summary
   cost $6.52 (25 min), and one-shot proof calls thought for 34 min before hitting the $8 cap with nothing to
   show. Now: literature/judge calls run at `--effort medium` with a $2.50 cap, formalize/cross-check at
   `high` with $4, proof search keeps the default effort and $8; a proof call that overruns its budget is a
   failed attempt that forces escalation to the compiler-in-the-loop mode instead of aborting the run.

## What was added (harness.py, +~1000 lines; tests/ +5 files)

- **Declaration index**: one pass over Mathlib + Batteries + Lean core (265k declarations, 13 s to build,
  1 s from cache), with namespace tracking, synthesized `to_additive` twins (`Finset.sum_range_succ`), and
  fuzzy suggestions. Powers: `-- CHECK:` directive, verified-name blocks in prompts (every Mathlib-looking name
  the literature stage mentions is checked), and **auto-import** — an `unknown identifier` whose declaration
  lives in an unimported module adds the module and recompiles, without an LLM round.
- **Repair context**: the two most promising failed attempts (compiling-with-`sorry` first) travel to the next
  round with full code and full compiler output; partial proofs are kept and seed the decompose stage.
- **Agentic escalation** (`--agentic escalate`, default): after one plain round, sandboxed `claude -p`
  sessions (`--permission-mode acceptEdits`, the only shell command allowed is `./check.sh` = `lake env lean`,
  Mathlib source readable) iterate with the compiler themselves; the harness still independently compiles
  and verifies what comes back. A max-turns/budget error is a failed attempt, not a fatal run.
- **Default header `Mathlib.Tactic`** (47 s/check vs 20 s): the prompts recommended `positivity`,
  `interval_cases`, `field_simp`, `gcongr`, `decide +kernel` — none of which the old 3-file header imported.
- **Cost accounting** (JSON mode; `--max-budget-usd` per call; a task system prompt that cut per-call
  overhead 3×), atomic state saves, resume-safe verification, provenance in `state.json`.
- **Knowledge layer** (`knowledge/`): `playbook.md` (tagged lessons, retrieved by keyword into prompts),
  `lemmas.jsonl` (helper lemmas harvested from verified proofs, offered verbatim with their imports),
  `solved/` (verified proofs = regression corpus). Commands: `regress` (recompile every verified proof;
  `--full` re-runs pipelines), `retrospect <run>` (LLM proposes ≤3 general lessons from a run's digest;
  deduped, provenance-tagged), `improve` (train → retrospect → held-out evaluation → promotion gate that
  requires a strict held-out gain, no lost successes, and a passing regression; see `learning.py`).

A concurrent Codex session (evening of 2026-09-07, while this session was paused on the usage limit)
contributed: `CodexCliBackend` (the `codex` CLI is **not** installed on this machine; its three #532 runs died
on provider errors), a `-- READ: <module>` directive, nested-comment/string-aware frozen-statement matching,
stricter exit codes, the gated `learning.py` promotion workflow, `battle_test.py`, and two test files.

## Merged harness — results (updated as lanes finish)

| # | new-harness result | how | cost |
|---|---|---|---|
| 493 (regression) | ✅ round 1, verified | one-shot | $1.39 |
| 674 (regression) | ✅ round 1, verified | one-shot | ≈$1.5 |
| **363** | ✅ **verified — first problem the one-shot design could not do** | the plain round-1 call thought for 34 min and exceeded its $8 budget with no output (twice, across a spend-limit restart); the resumed run with `--agentic always --agentic-samples 1` produced a 194-line sorry-free proof in one sandboxed session of 22 tool turns / 16 min | $11.68 logged (literature alone $6.52 for 25 min of thinking; agentic $4.25) + ≈$8 for the budget-capped one-shot call and an unlogged call killed by the spend limit |
| 198 | ✅ round 1, verified (75-line proof: factorial-based Sidon set hitting every infinite AP) | one-shot | $2.40 |
| **1193** | ✅ **verified — second one-shot failure rescued by the agentic mode**: all three round-1 one-shot attempts failed on the heavy statement (`Nat.card` of a subtype of A×A, `Set.ncard`, `Filter.liminf` over ℝ; a systematic `Set.univ`-as-binder syntax slip); one sandboxed session (9 turns, 7 min, $1.50) proved it with A = ℕ, g = n+1, an antidiagonal equivalence, and `Filter.liminf_congr`/`liminf_const` | one-shot ✗ → agentic ✓ | $2.92 (first run: literature/formalize/one-shots) + $1.75 (agentic run) |
| **370** | ✅ **verified — third one-shot failure rescued by the agentic mode**: the three round-1 one-shots shared one trivial gap (`linarith` could not see `9 ≤ (k+3)^2`), which hid everything after line 13; the agentic session fixed it in 4 turns / 3 min ($1.07). 60-line proof with the family n = (k+3)²·(k²+6k+7), n+1 = ((k+2)(k+4))², bounding every prime factor | one-shot ✗ → agentic ✓ | $4.43 |
| **532** | ✅ **verified — fourth one-shot failure rescued by the agentic mode** (Hindman's theorem): the round-1 one-shot call overran its $8 cap ($9.02 charged) and returned nothing; the resumed run went straight to two parallel sandboxed sessions and one produced a 105-line proof in 9 min that transfers Mathlib's `Hindman.FS, Hindman.FS_partition_regular` from streams of positive naturals to subset sums | one-shot ✗ → agentic ✓ | $14.66 total logged |

**Why #363 needed the compiler in the loop.** The proof the agent found is not Ulas's explicit polynomial
family (the community proof) but an Erdős-style pigeonhole argument: take the blocks [x, x+3] for
x ≡ 1 (mod 4) in a long range (pairwise disjoint), bound the number of primes that can divide any block
product with `Nat.primeCounting'_add_le` (via `Nat.totient 210 = 48` by `decide +kernel`), so there are more
subsets of blocks than parity vectors of prime exponents; two distinct subsets share a parity vector
(`Finset.exists_ne_map_eq_of_card_lt_of_maps_to`), and their symmetric difference is a non-empty disjoint
collection whose product has all exponents even, hence a square (`Nat.factorization`). Getting the dozen
Finset/factorization lemma names and coercions right took 22 compile-edit cycles — exactly what a one-shot
call cannot do, and why the per-call budget overrun is now treated as "escalate", not "fail".

---

# Second extension — triaged open-problem pipeline (2026-09-08/09)

Built in the requested order; each step was checked with unit tests, the real-Lean mock pipeline, `regress`
(11/11 green throughout: 316, 397, 399, 493, 645, 674, 363, 198, 1193 + the two attributed reference fixtures), and a
small live check on the solved ladder where affordable.

| step | status | battle test |
|---|---|---|
| 0 triage (`assess`, routing rules in code, decision logged) | done | **all 9 solved problems route `fast`**, $0.17–0.23 each (≈1.8% of a typical run); the model's free-text `recommended_mode` was often "construct" and is correctly ignored by the rules; open problems in the site's finite-computation classes route `search-first` (verified live on #364 verifiable and #242 falsifiable) |
| 1 `scout` | done | 370 candidate pages fetched (cached under `runs/.cache/site`), tags enforced, status sentences stripped; top-15 written: 364, 172, 424, 450, 201, 242, 340, 375, 377, 385, 475, 488, 723, 824, 929 |
| 2 `--open` (both directions, `#check`-derived negation, `knowledge/open/`) | done | **live on #424** (the 2, 3, ab−1 closure sequence; open, flagged 'presumably'): positive statement frozen after cross-check, negation built from Lean's `#check` type and compiled, both directions attacked in parallel (one-shot → one agentic sandbox → 2 refinement rounds each) under a $16 budget: **neither direction proved** (as expected for a genuinely open problem); the positive direction salvaged two trivial membership lemmas as partial results; exit 3; report written to `knowledge/open/424/<run>/report.md` marked *requires human review before any external claim*; $7.12 total |
| 3 `search` (bounded stdlib Python, safety screen, timeout, witness → Lean certificate) | done | **live: #399 forced `search-first` — the model's script found the witness {"n": 10, "x": 48, "y": 36, "k": 4} in 0.1 s; the prover certified it in round 1; verified; $0.35 for the whole run.** First attempt was rejected by the safety screen for `import json` (allowlist gap, fixed + one retry with the rejection reason) |
| 4 `--literature-web` (erdosproblems.com / forum / arXiv only; Lean repos forbidden and detected; `KNOWN_BOUND`) | done | not live-tested (an earlier web probe cost $6 for one call; opt-in only) |
| 5 `construct` (generator/valid/score/mutate/certificate program, local search + model variants, archive, Lean certificate) | done | driver verified offline (toy Sidon program, `decide` certificate compiled). **Live on #201 (G₃(N) vs R₃(N)), $2.93, 2 iterations:** the model wrote an exact Roth-number branch-and-bound and found A = {0,4,6,8,10,12,13,14,16,18,20,22,24,26} (14 elements) with roth(A) = 7 while R₃(14) = 8 — a witness to the strict gap G₃(14) ≤ 7 < 8 ≤ R₃(14) the problem asks about. Its Lean certificate (`decide` over all 3003 eight-subsets) **timed out at 420 s → recorded as uncertified**, exactly as the label requires. Fix applied afterwards: certificates must be `Bool` programs proved by `decide +kernel`, get a 900 s timeout, and fall back to the next-best object. **Validation:** a hand-written Bool-reflection certificate for the same object (assistant-written after the run, stored as `certificate-bool-assistant.lean` next to the run's artifacts) compiled in 239 s — so the found set is a genuinely certifiable strict-gap witness G₃(14) ≤ 7 < 8 ≤ R₃(14), and the stage only lacked the right certificate style |
| 6 `program` (PLAN.md, `Lemmas.lean` as module `Formal.Programs.Erdos<n>`, ledger, REVIEW.md + file-backend pause) | done | **live, one cycle on #172** (monochromatic sums+products of a k-set, open): experiments script ran (after a `sys`-import rejection was made explicit and retried), PLAN.md written with a conjecture table, 5 sub-statements proposed, **5/5 certified as lemmas** (degenerate cases k ≤ 1 / r ≤ 1, monotonicity in the number of colours, a sequence→Finset bridge, …) for $2.76 of child runs; exit 3 (partial), REVIEW.md written. Two defects found and fixed live: (i) sub-goal proofs were being rejected by the faithfulness judge (they are lemmas, not the problem) — mechanical verification is now the bar for `direction=program`; (ii) the concatenated lemma module lacked an import header and namespaces — fixed, and `Formal.Programs.Erdos172` now builds (97 s) |
| 7 ensembles & specialists (`--models` rotation from round 2, critic call, specialist tactic cascade before any model call, `--subgoal-prover` hook, persistent sandboxes) | done | cascade/`exact?` passes are exercised on every decompose skeleton; hole closures are logged with the component |
| 8 partial results (`knowledge/partial/<n>/`, exit 3) | done | unit-tested; counted below when they occur |
| 9 `improve` over a cluster with held-out problems | done | **live:** train on #316 (unit fractions), held-out #399/#674: before {399 ✓, 674 ✓} → after {399 ✓, 674 ✓}, saved proofs recompile ✓, **promoted = false** — the gate demands a strict held-out gain, and a tie on already-solved problems is correctly not promoted (the candidate lessons stay in `runs/learning-*/candidate-1/`). Lesson for using the loop: held-out problems must be ones the current knowledge does NOT solve, otherwise no gain is measurable. Cycle cost $6.59 (2 baseline evals $2.83, training run $2.27, 2 re-evals $1.49 — the re-evals reuse frozen statements, hence cheaper); 3 candidate lessons produced |
| 10 tokens next to cost, `--run-budget`, per-problem stop reasons | done | every `llm/response` event carries `{in, out, cache_read, cache_write}`; reports state outcome, mode and why the run stopped |

Live outcomes for the queued tests are appended below as they finish.

## Dependency-aware BSD research infrastructure (Codex, 2026-09-09)

Reviewed Claude's latest updates and the user-supplied BSD assessment PDF. Added the opt-in `campaign` layer with an explicit dependency graph, separate evidence, independently compiled proof contracts, artifact-bound certificates, persistent repair context and shared invocation budgets. The BSD manifest records the rank-two CM nonvanishing, Selmer and rational-rank obligations separately; no BSD theorem or autonomous solve-rate improvement is claimed. See [review and validation](campaigns/bsd/REVIEW.md) and [campaign notes](campaigns/bsd/README.md).

## Next ladder — the 300–1000-line self-contained tier (2026-09-09, lane L)

Same harness, one sequential lane, per problem:
`--run-budget 25 --rounds 3 --decompose-rounds 3 --agentic-samples 1 --agentic-turns 100` (round 1 one-shot, rounds 2–3
sandboxed compile-loop sessions, then 3 refinement rounds). Problem files for #476/#350/#16 were written from the
erdosproblems.com statement + resolution notes (no Lean hints); #280/#499 already existed. Community proofs
(plby/lean-proofs, `import Mathlib` only) are the difficulty proxy; they were never shown to the harness.

**Model note.** #280 ran on claude-fable-5-1 (`runs/lanes/laneL.log`). Partway through #499 the account hit its
monthly Fable spend limit; the backend reports that as a hard error and the lane stopped with exit 1, as designed
(infrastructure failure, not a mathematical one). The remaining work was rerouted to **claude-opus-5** via
`--model claude-opus-5` (`runs/lanes/laneM.log`), resuming #499 from its frozen statement and three recorded
one-shot failures. Cross-model comparison is therefore not available on this tier: each problem's result below
names the model that produced it.

| # | statement (resolved direction) | community proof | result | how | cost | wall |
|---|---|---|---|---|---|---|
| 280 | sieve count with n_k > (1+ε)k log k is o(k) — FALSE claim, so prove the negation (Cambie's n_k = 2^k, a_k = 2^{k-1}+1) | 262 lines | ✅ PROVED & VERIFIED (all clear) | one-shot, round 1, 121 lines: `m % 2^(i+1) = 1` for every survivor by induction, filter = {1}, growth via log x ≤ x/2 and k² ≤ 2^k, IsLittleO of a constant | $4.43 | 20 min |
| 499 | every real n×n doubly stochastic matrix has a permutation σ with ∏ a_{iσ(i)} ≥ n^{-n} (TRUE) | 223 lines | ✅ PROVED & VERIFIED (all clear) | Fable's 3 one-shot attempts had the right plan (Birkhoff + weighted AM–GM) but failed on lemma signatures; **Opus 5** closed it in the FIRST agentic session, 154 lines: row-wise `∏ vⱼ^vⱼ ≥ 1/n` from `Real.geom_mean_le_arith_mean_weighted`, then Birkhoff | $9.70 ($8.74 Fable one-shots + $0.96 Opus 5) | 34 min total, 6 min on Opus 5 |
| 350 | finite A ⊂ ℕ with distinct subset sums has Σ 1/n < 2 (Ryavec, TRUE) | 436 lines | ✅ PROVED & VERIFIED (all clear) | **Opus 5**: one-shot failed on a single unknown name (`sum_le_tsum`); round-2 agentic session produced 407 lines following Ryavec's generating-function route (product ∏(1+x^n), logarithm bounds, an integral) | $8.04 | 40 min |
| 16 | odd numbers not of the form 2^k + p are NOT an AP ∪ density-0 set (Chen; negation) | 371 lines | ⏳ queued | | | |
| 476 | Erdős–Heilbronn: A ⊆ F_p ⇒ |A +̂ A| ≥ min(2|A|−3, p) (TRUE) | 540 lines | ⏳ queued | | | |

## Atlas top-3 reconstruction experiment — #649, #105, #275 (Codex, 2026-09-09/10; continued by Claude)

A separate experiment ranked the whole 1,217-problem catalogue for harness feasibility (`atlas-data/`), then
attacked the three highest-ranked problems the harness had never tried: **#649** (greatest prime factors of
consecutive integers, disproved), **#105** (Erdős–Purdy, a line meeting A twice and B never, disproved, $50) and
**#275** (a system of r congruences covering 2^r consecutive integers covers all, proved). #280 was excluded
because the ladder lane had just solved it. Artifacts: `experiments/atlas-top3/`.

All three produced Lean proofs that pass every mechanical gate. **They are not autonomous solves.** The initial
runs exhausted their bounded web-research budget and then hit the Fable spend limit; the operator reconstructed
the checkpoint and supplied each problem's *published informal resolution notes* as literature context, and
formalization now reads that proof route. Proof generation finished on Codex. No external Lean proof was supplied.
All three stay at `mechanically_verified` with `claimEligible=false`.

| # | site status | result | assistance | caveat |
|---|---|---|---|---|
| 649 | disproved (Lean) | ✅ mechanically verified — P(n)=2 forces n=2^k, then 7 ∣ 2^k+1 contradicts 2^k mod 7 ∈ {1,2,4} | operator-supplied resolution notes; private-helper layout repair | proof fixes the domain to positive integers; under a negative reading with P(\|n\|), n = −8 realizes p=2, q=7. The site's own disproof uses the same positive reading |
| 105 | disproved (Lean) | ✅ mechanically verified — explicit counterexample, 9 points in A and 6 blockers in B | operator-supplied notes; redundant finite-case tactic repair | witness found during the run (9 blue/6 red), not the 12/9 configuration the operator had researched |
| 275 | proved (Lean) | ✅ mechanically verified — roots-of-unity expansion over the powerset | operator-supplied notes and informal route | — |

**Verification done in continuation (2026-09-10):** the Lean replay Codex ran preceded its own final edits, so it
was rerun over the full corpus afterwards — **16 proofs, 16 passed, 0 failed**, all sorry-free on the three standard
axioms (`experiments/atlas-top3/regression-after-final-edits.log`). Python suite rerun: 87 tests, 76 passed,
11 skipped, 0 failed. A second assistant re-read all three frozen statements against erdosproblems.com and found
them faithful (`experiments/atlas-top3/STATEMENT-REVIEW-claude.md`); that is still not independent human review.
The harness's new automatic repairs were audited for gate weakening and none was found: every repair recompiles
and re-checks the frozen statement, banned tokens and hole count, and final verification never applies repair.

## Per-problem outcome table (what was and was not solved, mode tried, why it stopped)

Generated from `runs/` (latest verified run per problem; costs are the sum over all runs of that problem; the four
July/baseline solves show $0.00 because those runs used the original text-mode backend without cost logging).

| # | class | outcome | mode | why it stopped / notes | total cost (all runs) | runs | tokens in/out/cache-write (best run) |
|---|---|---|---|---|---|---|---|
| 172 | open | program: 6 ledger entries, certified_any=True | research | research program cycles finished (see programs/erdos_172/REVIEW.md) | $3.52 | 1 | 25k/46k/57k |
| 198 | resolved | PROVED & VERIFIED | fast | — | $2.40 | 1 | 0k/0k/0k |
| 201 | open | construct: uncertified (best 1.014) | construct | forced by --mode | $2.93 | 1 | 19k/41k/43k |
| 242 | open | not proved / incomplete | fast | open + research depth without --allow-research: fast+agentic+decompose, then partial results | $0.89 | 1 | 12k/6k/28k |
| 316 | resolved | PROVED & VERIFIED | fast | — | $0.00 | 1 | 0k/0k/0k |
| 363 | resolved | PROVED & VERIFIED | fast | — | $11.68 | 1 | 0k/0k/0k |
| 364 | open | not proved / incomplete | fast | open + research depth without --allow-research: fast+agentic+decompose, then partial results | $1.10 | 2 | 11k/8k/21k |
| 370 | resolved | PROVED & VERIFIED | fast | — | $4.43 | 1 | 0k/0k/0k |
| 397 | resolved | PROVED & VERIFIED | fast | — | $0.00 | 1 | 0k/0k/0k |
| 399 | resolved | PROVED & VERIFIED | fast | — | $0.00 | 1 | 0k/0k/0k |
| 424 | open | open: {"pos": 3, "neg": 2} | fast | open + research depth without --allow-research: fast+agentic+decompose, then partial results | $1.39 | 1 | 13k/14k/32k |
| 493 | resolved | PROVED & VERIFIED | fast | — | $1.39 | 2 | 0k/0k/0k |
| 532 | resolved | PROVED & VERIFIED | fast | — | $14.66 | 4 | 29k/30k/147k |
| 645 | resolved | PROVED & VERIFIED | fast | — | $0.00 | 1 | 0k/0k/0k |
| 674 | resolved | PROVED & VERIFIED | fast | — | $2.50 | 3 | 0k/0k/0k |
| 1193 | resolved | PROVED & VERIFIED | fast | — | $4.67 | 2 | 0k/0k/0k |

Total logged spend across all September runs (both extensions, including wasted one-shot overruns and re-runs): **$71.64**.
Budget guards now in place: per-call caps by stage, `--run-budget` per run, budget-overrun → agentic escalation, spend-limit errors stop the lane.

## What is NOT solved, and why (honest summary)

- **Open problems attacked (#364, #242, #424, #172, #201):** none resolved — correct, since they are open. The pipeline's
  job on them is triage, cheap computational probes, both-direction attacks, certified partial lemmas and constructions,
  and reports that a human must review. That is what happened: #172 gained 5 certified lemmas (degenerate cases, colour
  monotonicity, a sequence→Finset bridge); #201 produced a certifiable strict-gap witness (certified by the corrected
  Bool-reflection style); #424 produced two trivial partial lemmas; #364/#242 stopped after triage by design.
- **Resolved problems the harness could NOT do one-shot but DID do with the compiler in the loop:** #363, #1193, #370, #532.
  The pattern is consistent: long one-shot thinking either overruns the budget or trips on one lemma-name/syntax slip that
  hides the rest; 4–22 compile-edit cycles fix it.
- **Not attempted on the harder self-contained tiers** (community proofs of 300–1000 lines: #476 Erdős–Heilbronn,
  #350 Ryavec, #499 van der Waerden-type, #280, #16, …): out of scope for this session's budget; they are the next ladder.
