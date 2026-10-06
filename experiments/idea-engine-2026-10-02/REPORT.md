# The research engine: iterating idea generation on open problems (2026-10-02)

Goal, from the operator: iterate the idea-generation stage, boldly and broadly, until it generates genuinely novel and
valid ideas. Three failures come first:
- steps rated hard succeed 1 time in 20;
- on open problems, discovery produced 0 refereed proofs in 10 draws across 7 problems;
- discovery reaches the published frontier and stops, leaving the problem restated as the core.

## Diagnosis (no model calls)

- **The attempts were one-shot essays.** On #455 each discovery attempt got a median of 4,300 output tokens and 49
  seconds (16 attempts, $2.51). The whole stage cost $3.70. That is enough to write down what the model already knows.
- **A beyond-frontier result was generated, then thrown away.** One #455 attempt (`transcripts/011-discover.md`) noted,
  unverified, that sharpening its AP lemma from 2p−1 to p−1 terms gives liminf q_n/n² ≈ 0.543.
  - That is above Richter's published 0.352.
  - The arithmetic checks out. Each gap value e repeats at most p(e)−2 times once the primes exceed p(e), where p(e) is
    the least prime not dividing e. Then the count of gaps up to x is at most 0.92005x + O(1), so liminf q_n/n² ≥
    1/(2·0.92005) = 0.5434.
  - With p(e)−1 repeats the same computation gives exactly 0.3521, which suggests that is Richter's argument. Not
    checked against his paper: his bound may hold for every n rather than in the limit, in which case the early
    blocks matter.
  - The synthesis filed it under dead ends, because it does not finish the problem.

## What the engine changes (`--discover-mode engine`, harness.py "research engine")

1. **Objective.** A frontier map (KNOWN, BARRIERS, CORE) and a portfolio of targets strictly beyond KNOWN, of seven
   types: QUANT, SPECIAL, CONDITIONAL, STRUCTURE, ANALOGUE, NEGATIVE, REDUCTION. A new result counts whether or not it
   resolves the problem.
2. **Boldness.** Half the round-1 sessions attack the CORE through distinct ANGLEs. Each angle must name its technique,
   explain why the known barriers do not stop it, and give a sharp first step. At least half the angles use techniques
   KNOWN does not use.
3. **Depth.** Every session is a tool-using agent with a Python sandbox: $3, 80 turns, high effort, so roughly 30× the
   old attempt's thinking. It keeps a NOTEBOOK.md with typed claims (PROVED / CONJECTURED / REFUTED) and full proofs.
4. **Validation.** For each proved or refuted claim, a step referee and an adversary run in parallel. A novelty judge
   (new / known / routine / restatement, significance 0–3) runs only when both pass. Only `validated-new` counts.
5. **Evolution.** A meta-review reads every verdict and writes round 2's assignments: push validated results further,
   repair broken ones, combine, and attack the core afresh.

## Success criteria (written before any engine result was seen)

A claim is **genuinely novel and valid** only if all four hold:
- the engine marks it `validated-new` with significance ≥ 2;
- an independent check by this session (Opus 5.5, reading the proof) finds no error;
- a literature search (OpenAlex, plus the forum) finds no prior proof of it or of anything stronger;
- it is not a restatement of the problem.

The loop stops when the panel holds **at least 3 such claims on at least 2 problems**. At least one of them should then
go to Lean, through the deductive loop with the claim as its frozen target. Below that bar, iterate on the engine.

**Predictions for v1 on #455** (written at launch, before the frontier call returned):
- the frontier map lists a QUANT target at or near 0.54;
- a session proves it, and the novelty judge calls it new or routine at significance ≤ 1;
- no core angle produces a validated new result;
- cost $20–30.

## Iterations

### v1 on #455: $15.42, 66 min (`runs/20261002-041515-654114-erdos455`)

**Depth.**
- The frontier map took 112,513 output tokens over 23 minutes ($2.32), against 4,300 tokens for an old attempt.
- The 6 sessions cost $1.20–2.00 each, within their $3 caps, and ran 7–34 turns.

**The frontier map**, unprompted by anything #455-specific:
- It recovered the 0.5434 bound, and noticed that Richter's 0.352 equals 1/(1+κ). That suggests his run cap was p(v)−1.
- It found a barrier. The finite core statement that the Lean run left open implies Heilbronn–Linfoot-type finiteness of
  the class-number-one fields 1−4A. Euler polynomials x²+x+A give long convex prime chains, so any proof of that core
  needs class-number strength input. This explains why the Lean core resisted. It is unvalidated.
- It also gave a sieve-friendly reduction (T9), an exact discriminant-walk reformulation (T10), and six research-level
  angles on the core.

**17 claims:** 2 validated-new, 6 valid but routine, 3 broken, 6 not validated.

| claim | engine verdict | this session's check |
|---|---|---|
| liminf q_n/n² ≥ **0.80024** for every convex prime sequence (r1s1/C1), computer-assisted via a max-plus certificate mod 15015 = 3·5·7·11·13 | validated-new, significance 1 | **Holds.** The proof reads correctly. `check.py`, re-run independently, reproduces ρ = 18748 exactly (max = min), potential range 50, 1/κ′ = 0.800240, in 9 s. An OpenAlex search (8 queries) found no improvement on Richter. Two sessions (r1s1, r1s3) found the same constant independently. |
| a "one repeated gap per period" multiplicity pattern is never locally admissible (r2s1/C3) | validated-new, significance 1 | minor |
| if a convex prime sequence has ≤ n^θ glitches (θ < 1/2), then q_n/n² → ∞ (r1s4/C1); the GRH version allows n/(log n)⁵ | valid-routine, significance 1 | reads correctly; "routine" is defensible |
| sup-over-shifts family large sieve: refuted as stated; any repair implies Linnik–Vinogradov with no ε (r1s2, r2s2) | broken once, repaired in round 2 | a real barrier lemma |

**Judges.**
- They caught two real errors, an exponent swap and an off-by-one in a residue window.
- They falsely broke one correct claim, r1s3/C1, because of a parser bug of mine: the session wrote `PROOF.`, the proof
  landed in BEYOND, and was clipped. Fixed, with a regression test.
- The meta-review then read the false break as a missing case.

**Budget sizing.** The cap-based reserve ran only 2 of round 2's 4 assignments and dropped the two aimed at the core.
Later rounds now size themselves from round 1's actual costs.

**Against the criteria: 0 qualifying claims.** The 0.80024 bound is novel and valid by every check here, but the novelty
judge rated it significance 1: it is a congruence-only constant that the profinite barrier caps at 1, with no bearing on
the core. The bar stands.

**Predictions:**
- QUANT target near 0.54: yes (T1).
- Proved and judged at significance ≤ 1: yes, but the session went past it to 0.800.
- No validated core progress: yes.
- Cost $20–30: no, $15.42.

### v1.1 on #1203: $22.10, 103 min (`runs/20261002-054831-996193-erdos1203`)

v1.1 is v1 plus the parser fix, the literature check, cost-based sizing and a $5 frontier cap.
- **A first attempt failed.** Under the old $2 cap the frontier map was cut off mid-answer: $2.60 lost
  (`runs/20261002-052159-979147-erdos1203`).
- **#153 was stopped early.** Its v1.1 run (`runs/20261002-054707-230028-erdos153`) was killed to move it to v2. The
  interrupted call's cost is unavailable.
- **The map** ran 252,030 tokens over 49 minutes ($5.13). It names exact ceilings for whole families of methods: about
  1.3840 using small primes only, about 1.5858 for one-large-prime arguments, an HL barrier, and a ceiling of
  N·exp(−(log N)^{1−ε}) for counting methods.

**19 claims:** 4 validated-new, all significance 1. Every one also passed the literature check, with the judge noting
that absence from the search is weak evidence.

| claim | this session's check |
|---|---|
| liminf F(n) ≥ 7·w(30046) = **1.58403** (r1s2/C1), against the known 1 − o(1); a CRT window plus Størmer–Mahler S-unit finiteness. r1s3 found 1.5835 by the same route; the novelty judge called that one routine. | **Holds**: every case checked by hand, and both numerical values recomputed. |
| sharpened to liminf F ≥ 7·w(30033) = **1.58407** (r2s2/C1). The method's ceiling is pinned to [7w(30033), 7w(30032)], width 3·10⁻⁶. Under Dickson's conjecture, the HL barrier constant is ≤ 6w(2312), below the 6w(2310) quoted in KNOWN. | not re-checked |
| #{n ≤ N : F(n) < C} ≤ N·exp(−(log N)^{1−ε}) (r1s1/C1), by a uniform-dimension Rankin–Brun sieve | not re-checked |
| #{n ≤ N : F(n) < C} ≤ N·exp(−(log N)^{1−(C+o(1))/logloglog N}) (r2s1/C1). Found independently by r2s3 and r2s4, and it refutes the map's own "counting caps at exp(−(log N)^{1−ε})". | not re-checked |

**The same two weaknesses as #455:**
- **Duplication.** In round 2, three of four sessions proved the same bound.
- **The novelty judge varies.** It called the same 1.584 constant new once and routine once.

v2 targets both, plus significance.

**Against the criteria: still 0.** Six claims are validated-new across #455 and #1203, and I checked two independently.
All six are rated significance 1: constants pushed to their method's ceiling, sharper exceptional sets, and barriers.

### v2 on #153: $23.36 (`runs/20261002-073216-923101-erdos153`)

v2 adds three things: significance-ranked targets, teammate awareness, and a two-judge novelty panel that keeps the
conservative verdict.
- **The frontier map was cut off at its $5 cap** ($5.25, lost), then succeeded on the 1.5× retry ($3.81, 139k tokens).
  That is $9.06 in all, so round 1 could afford only 3 sessions.
- **The Mac idle-slept with two judge calls in flight.** macOS stops the monotonic clock behind Python's subprocess
  timeouts, so the calls hung for 6.5 hours until they were killed by hand. That claim is `unjudged`.
  - Runs now hold `caffeinate -i -w <screen pid>`, a temporary assertion that ends with the process, plus the app's
    keep-awake.
  - The 517-minute wall time is almost all sleep.
- **Teammate awareness worked.** Sessions took distinct lines (A1, A2, T4, and in round 2 four different
  assignments), and no constant was duplicated.

**12 claims:** 2 validated-new. Both judges agreed on significance 1 for each, and the literature check found both
new.
- **r2s2/C1.** A Sidon set made of at most K affine images of Singer difference sets, plus n^{1−ε} exceptional
  elements, has Q(A) → ∞. The engine typed it NEGATIVE; it is really a special case.
- **r2s1/C1.** A negative result: the weighted (fractional) relaxation of edge loading cannot beat the known bound.

The rest were 4 routine, 4 broken, and one significance-3 target (T4: C* > 1) not proved. Its session instead proved,
in a continuum model, that the known c·log(1/δ) bound is sharp for every profile-plus-pair argument.

**After three problems: 10 validated-new claims, every one significance 1.** The engine reliably generates novel,
refereed results of two kinds: constants pushed to the ceiling of their method, and precise barrier or special-case
theorems. It has not produced a significance-2 result. v3 adds the deep dive.

### Interruptions, and checkpointing (2026-10-02, 20:17 UTC)

The Mac's battery died seven minutes after v3 launched. Its #455 continuation
(`runs/20261002-160957-739019-erdos455`) lost the frontier call in flight, at a cost that is unavailable. Together with
the earlier idle-sleep stall, that settles it: a run that keeps nothing until it finishes re-buys everything after any
interruption, and a map alone has cost $9.

`engine_run` now checkpoints to `engine/checkpoint.json` after:
- the frontier map;
- every session, as it finishes;
- every verdict;
- every round;
- the deep dive's session, before it is judged.

Resuming the same run dir picks up from the checkpoint. `screen.py --resume RUN_DIR` drives it. `tests/test_engine.py`
class Resume covers four cases: a crash mid-round, mid-validation, between rounds, and inside the deep dive.

### A truncated frontier map, caught on resume (20:47 UTC)

v3's first #455 map came back with `turns=2` as its final 9,904 characters, from target T9 on, and was checkpointed
like that. The cause: a text answer past the per-message output cap continues in a second message, and the CLI's
`result` holds only that second message.

The run was stopped two minutes into its sessions, which had started from a near-empty map. Those four sessions' cost
is unavailable. The map ($3.68) was dropped from the checkpoint, and the run resumed.

`_run` now joins every assistant text of a text-only call (`d285928`, `tests/test_backend_retry.py`).

The bug was rare elsewhere: 11 of 3,642 text calls on disk ran past one message, and 4 of those were frontier maps.
#1203's and #153's maps also ran to two turns but parsed whole. Their first message most likely held only thinking.

### v3 on #455, a continuation from the blackboard: $36.11 (`runs/20261002-160957-739019-erdos455`)

This run includes $3.68 for the truncated map and two resumes. It started from v1's results on the blackboard, so the
new map already listed 0.80024 under KNOWN and aimed past it: liminf ≥ 1, a conditional target, limsup = ∞, and the
glitch theorem for θ < 1.

**Rounds 1–2: 8 sessions.**
- **The congruence game at z = 17** (r1s2, r1s3, independently): liminf q_n/n² ≥ **0.86429**. The z = 17 game value is
  exactly 295,318 per period of 255,255. I re-ran r1s3's certificate here and it reproduces exactly in 89 s
  (`evidence/455/check_0.86429.*`).
  - The bound is monotone: as z grows, the bounds only improve and converge to a limit in [1, 1.157].
  - Growing z with n cannot beat 1 while z ≤ (2−ε) log n.
- **The few-glitch theorem extended to θ < 2/3** (r2s2), using new normal forms: every long e = 2 run is a segment of
  an Euler polynomial with a fundamental discriminant.
- **Refutations and broken claims.**
  - The conditional target's hypothesis (uniform Hardy–Littlewood) was refuted outright.
  - Several structural claims were broken by the judges.

**The deep dive** ($2.08 to plan, $5.37 for the session, 165k tokens). The plan chose θ < 1 for the glitch theorem.
The session produced four claims:
- **C1, θ < 3/4, unconditional: validated-new**, significance 1 from both judges, literature new. It uses a new
  mechanism, a large sieve per "stay" on one discriminant row, which goes past the per-run Linnik–Vinogradov barrier.
- **C2, θ < 5/6 implies liminf ≥ 2: broken.** One sieve step's range may be empty; the argument still supports θ < 4/5.
- **C4, θ < 1 under a split-density hypothesis that GRH implies: broken.** It assumes uniformity in a parameter that
  grows with n.
- **C3: a conjectured barrier at 3/4**, the Burgess exponent.

On the first parse the deep dive's C1 was read without its proof and marked broken. The session had written "see
Proof of C1 below" and put C2–C4 under that section. `parse_claims` now reads claims anywhere and attaches proof
sections. Replayed on all 30 notebooks, 12 gain claims and none loses one. The deep dive was re-judged from its
checkpoint, with no session re-run.

**The judges' reason for significance 1** on the θ < 3/4 result: it goes "beyond the single-run Linnik–Vinogradov
barrier" with "a genuinely joint multi-discriminant argument", but it "leaves the core untouched". Their bar for 2 is
contact with the core, not a new mechanism.

**After four engine runs (#455 twice, #1203, #153): 14 validated-new claims, all significance 1.** I checked three
independently: 0.80024, 0.86429 and 1.584. The deep dive did what it was built for, a longer push down the most
promising line, and moved the glitch threshold from 2/3 to 3/4. That still did not reach significance 2.

### v3 on #1203, a continuation: $32.29 (`runs/20261002-190542-547817-erdos1203`)

**The map.** It ran 370,259 tokens in three turns, 69 minutes and $7.56. The multi-message fix kept it whole: 21,895
characters with every section. It aimed past v1.1: a power-saving exceptional set (significance 2), liminf F ≥
1.587 + δ (significance 3), and a sieve barrier theorem (significance 2).

**Rounds 1–2: 8 sessions, mostly judged routine** (8 routine, 7 broken).
- **The map's own sieve barrier was refuted for r = 0.** A Selberg majorant gives a power saving. Round 2 then proved
  the saving is special to r = 0 and fails for r ≥ 1.
- **F has normal order w(15)·log log n**, via a uniform multi-shift Rankin–Brun lemma.
- **Off a polylog-thin explicit set** (n near 61-smooth plants), F(n) ≥ 6·w(2312) = 1.585743. That is exactly the
  bounded-window ceiling under Dickson's conjecture. The significance-3 target itself runs into the parity barrier.
- **A conditional proof that F → ∞** under a near-independence hypothesis U(c), giving F ≥ (1/log 2 − ε)·log log log n.
  The adversary broke it: U(c) was written for real x and fails for non-integer x. The fix it named, integer x, is the
  only case the proof uses. This motivated the repair pass (`d3a22f9`).
- **Heuristic and moment theorem:** liminf F/log log log n = 1/log 2 in the random model.

**The deep dive:** $0.60 to plan, $3.65 for the session.
- **C1, validated-new: liminf F(n)/log log log n ≤ 80**, with N^{1−o(1)} such n in (N, 2N].
  - The two novelty judges split, 1 and 2. One wrote that "no published upper bound on liminf F … is known". The
    conservative panel records 1.
  - It matches the conjectured order: round 2's heuristic gives 1/log 2 ≈ 1.44.
  - I checked the proof's structure and elementary lemmas (`evidence/1203/v3-deep-NOTEBOOK.md`), not every constant.
  - **This is the closest any claim has come to the bar.**
- **C2, broken (fatal):** it overstated what the construction certifies.

### v3 on #156: $28.39 (`runs/20261002-214504-015603-erdos156`), and the first repair passes

**#156** asks for a maximal Sidon set in [1, N] of size O(N^{1/3}). The known bounds are (2N)^{1/3} below and
O((N log N)^{1/3}) above.
- **Validated new, significance 1:** every maximal Sidon set has |A| ≥ (1.2679 − o(1))·N^{1/3}, up from the known
  2^{1/3} = 1.2599.
- **The deep dive proved the cyclic analogue:** ℤ_n with n = m(q²+q+1) has a maximal Sidon set of size exactly q+m, so
  O(n^{1/3}), for m ≤ q/2 with q ≥ 160, and for m ≤ 3q/10 in general.
  - It is a Singer difference set in a subgroup plus a Sidon transversal of its cosets. Maximality comes from an exact
    coset tiling, so there is no log loss.
  - Validated new, significance 1, literature new. The first screen had flagged this analogue as possibly new.
- **Not proved:** the case n = q³−1 is only conjectured. Random greedy succeeded for every q ≤ 67.
- **The repair pass's first live use:** all 3 fixable broken claims came back valid, though routine.

**Repair passes on #1203 and #455**, resumed from their checkpoints for $2.02 and $1.86.
- **#1203:** the conditional proof that F → ∞ (U(c), repaired to integer x) now passes the referee and the adversary.
  - The novelty panel calls it a restatement or routine: the hypothesis carries the difficulty.
  - The thin-set constant 6w(2312) was repaired and validated new.
- **#455:** the dichotomy behind the θ < 2/3 glitch theorem was repaired and validated new.

**Tally after four problems: 18 validated-new claims, all significance 1.** One got a 2 from one of its two judges: #1203's
liminf F/L₃ ≤ 80.

### Hard steps: the engine on a step the Lean loop failed (hs1, 2026-10-03)

The first failure on the list is that steps rated hard succeed 1 time in 20. `hardsteps.py` banks the 18 open hard steps
left by train runs (`--list`). Each runs masked under `--benchmark`, with a fresh synthetic id, as the engine's whole
target. `hardsteps_lean.py` then hands a refereed proof to the deductive loop as its blueprint, and Lean decides.

Protocol note: the step's frame tells the model that the whole problem "was resolved recently, and you are not told
how". That is a cue that a proof exists, which an open problem never gives, and #435's novelty judges repeated it. A
hard-step result therefore measures the engine on a step known to be provable. It is not evidence about open problems.

**#435 `hyp_top`** (bank index 5, from train-conv): X(n) − n is not a sum of the binomials C(n,i), 0 < i < n, for n not
a prime power. With the Brauer upper bound, this is the whole lower-bound half of the problem. The Lean loop had failed
on it. Engine run: $8.00, 11 claims (`runs/20261002-235647-826042-hardstep-erdos727285`).
- **The step itself was proved twice** (r1s1/C1, then the deep dive's C1r). Each proof passed both the step referee and
  the adversary. The panel rated each a *restatement* at significance 3, which here means it is the step, proved whole.
- **The core inequality (E)** was proved three times (r1s2/C1, r1s3/C3, deep/C2). It says every non-tower binomial
  C(n,i) is at least its residue's potential.
- **Validated new** (significance 1 and 2 from the two judges): the dual-certificate reduction r1s3/C1. A digit
  potential on ℤ/n is a lower bound for the Apéry set once (E) and a carry lemma hold.
- 3 claims broke, among them the finite check to n = 160 that one session reported as proved.

This is informal and refereed only. The Lean stage took three launches, and both failures were bugs in this experiment's
launcher, not mathematics:
- **Launch 1:** the rename `erdos_<old>\b` never matches before `_`, so the frozen statement kept its old ids. Killed.
- **Launch 2** ($1.09): a CLI run matches plans only against `theorem erdos_<id>`, and the step's theorem was
  `erdos_<id>_hyp_top`. A complete four-hypothesis skeleton was logged as "no skeleton block in the plan". Replayed
  offline with the theorem renamed, the same plan parses and compiles. Killed. The loop now refuses such a statement
  before any call (`60d3130`).
- **Found on the way, a harness bug that predates this work:** `stage_reduce` compiled each reduction's Lean statement
  without the problem's own `def`s. On statements with `def`s, 95 of 141 reductions died as `Unknown identifier` after
  their numerical check had passed. Fixed in `31d3f6e`. Launch 3's two reductions now type-check as `stated`.

**Lean stage, launch 3** (`runs/20261003-004608-866727-hardlean-erdos727285`, $15.25, 104 min). It ended partial:
**17 of 25 steps certified** (the second plan split S19 in two), 8 open. The blueprint had 22 steps.
- The plan rated 9 steps elementary, 13 moderate and 1 hard. Of the 17 certified steps:
  - 8 came from cheap one-shot attempts (8 of 14 tried);
  - 6 from depth children (6 of 7);
  - 3 were proved inside the cycle-2 skeleton itself (S7_periodic, S19a, S19).
- **Open:** S6 (digit surjectivity), S7_digits_spec, S7_phi_basic, S11 (the tower carry step, rated hard), S12 (closure
  induction), S18, S19b and S21 (every binomial lies in T). These are the proof's core: the Apéry-potential argument.
  Everything certified is supporting arithmetic.
- **Resumed by the operator** with `--run-budget` raised from 15 to 35. This is budget only, recorded in the run's
  `assistance`.

**Result: the hard step is proved in Lean, and the full #435 statement assembles**
(`evidence/435-hardstep/README.md`).
- **The run.** After three funded resumes (budget 15 → 35 → 50 → 70, recorded in its `assistance`), the Lean run
  closed at $66.28 with verification cleared. Its audit passes all 7 Lean checks.
  - Recursive children did the decisive work: S19b, S12, S21a, and S11 as five pieces. The plan's own re-cuts did the
    rest.
  - One resume was stopped to load the splice fix `8641308`. Without it, a certified proof was being thrown away.
- **The assembly.** The step's proof was spliced into the train run's final residual, where it was the only open step.
  The result passes all 7 audit checks against #435's frozen statement.
- **What it is.** A reconstruction of a published result by the published route: the Apéry set, and the C(n,p^j) as
  mixed-radix digits. Assembled by the operator, so not an autonomous solve.
- **For the hard-step failure mode** ("steps rated hard succeed 1 time in 20"): an informal, refereed proof from the
  engine, used as the blueprint, took a stalled hard step to a certified one. The cost was about 5× the original run
  ($74 for engine and Lean, against $12.84), and it needed operator budget decisions to get there.

**Two more hard steps from the bank** (`--engine-sessions 3 --engine-rounds 1 --engine-deep-budget 6`, $20 caps):
- **#1179 `hyp_fixed_delta`** ($15.11, `runs/20261003-083314-684014-hardstep-erdos799065`): the uniform ε-balance of
  random k-subsets of every abelian group of order N, with k = ⌈(1+δ)·log₂N⌉. **The deep dive proved the step
  itself** (deep/C1). Both the referee and the adversary passed it, and the panel rated it a restatement at
  significance 3.
  - The proof is a moment method: a Fourier "Good" event, then a split of G into small and large cyclic factors, rank
    bounds, an Odlyzko-type count of 0/1 relations, and Cramer minor bounds.
  - It is informal. A Lean stage would need finite abelian duality and moment estimates, far more than #435 did, and is
    not funded.
- **A false significance-2 verdict, recorded as a calibration failure.** In the same #1179 run, r1s3/C1 proves the
  statement with (3/2 + δ)·log₂N. Both novelty judges called it new at significance 2: the first claim ever to clear
  the conservative panel's bar.
  - It is weaker than the (1 + o(1))·log₂N bound the problem's page attributes to Erdős–Hall (1976).
  - The judges did not know that paper, and hard-step runs skip the literature check and get no library.
  - The pre-registered bar's own literature-search requirement exists for exactly this case. A panel "new" is not
    evidence of novelty for older literature.
- **#152 `hyp_runs`** ($13.02, `runs/20261003-072447-715298-hardstep-erdos792759`): **not proved.** The step needs
  diffRuns(A) ≥ 3|A| + M for every large Sidon set.
  - The best results were R ≥ n − 3 (validated new, significance 1) and a conditional R ≥ c·n^{3/2}.
  - Its deep dive never ran: the plan call spent $2.62 against its $2 cap and wrote nothing. That is now fixed:
    - `cdb0a17`: a capped call is retried at 1.5× its cap;
    - `d2a06bf`: a deep dive that failed at its plan is retried on resume;
    - `7e4a8f4`: a finished engine run can be resumed.
  - Resumed with a $23 cap to run it.

**Hard-step tally:** 2 of 3 steps proved informally (#435, #1179), against 1 in 20 for hard steps in the Lean loop
alone. Lean has certified 1 of them so far (#435).
- **Can a prompt fix the false verdict?** No, on this evidence.
  - The replay (`novelty_replay.py`, about $1.60) put #1179's r1s3/C1 through the masked novelty prompt again: 2 judges
    on the current prompt, and 2 on a variant that first asks for the strongest known result on the same question.
  - All 4 still said "new, significance 2". Both variant judges named Erdős–Rényi's 2·log₂N as the strongest bound they
    knew. Their text mentions "Hall", but neither cited the Erdős–Hall (1 + o(1))·log₂N bound.
  - The gap is recall of older literature, not prompting, so the prompt is unchanged. What closes it is the problem's
    own bibliography. Open-problem runs get it through their library; hard-step runs do not.
- **#152's deep dive, resumed** ($21.44 for the run in all): **nothing validated new, and the step is still unproved.**
  - The notebook's headline claims did not survive validation:
    - C9: iso(A) ≥ (n−18)/4 for every Sidon set, which is the whole of #152;
    - C7: a linear bound except in the end-pair case.
  - The referee broke both because their proofs only add up inequalities from lemmas that are never stated or proved
    inside the claim. The adversary broke C5, the lemma under C7, for using one identity with two incompatible signs.
  - Only C6 (R ≤ 2·iso_off + 1 + 2(n−1)[1 ∈ A−A]) and C1 survived, as routine.
  - The repair pass did not rescue them. A notebook's "Result" section is not a result until the referee has read the
    proof.

## v5: dependency-aware validation and gap closing (2026-10-06)

**What changed** (`07898b3`, `de2db38`, all in `harness.py`, research engine):
- **Citations.** A claim's proof may cite other claims of its notebook. The referee and the adversary now see those
  lemmas' statements, taken as given.
- **Chain statuses.** `engine_resolve` keeps each claim's own verdict in `own_status`. Its `status` stays
  `conditional`, with a `pending` list, until everything under it is valid. A gap-closing or repaired version of a
  lemma stands in for it; a refutation never does. A proof ends at its last end mark (∎, □, QED), so citations after
  it are commentary.
- **Gap closing** (`--engine-gap-rounds N`, off by default):
  - broken claims are rated "if proved", the most dependent first;
  - each claim that would be the core, or new at significance 2 or more, is re-judged with its lemmas in view;
  - if it is still broken, it gets a tool-using gap-closing session that sees the objections, the lemmas and the
    notebook, for up to N rounds;
  - every lemma under it is settled the same way.
- **The Lean loop can fund itself** (`1176f75`): `--budget-extend STEP --budget-extend-max CAP`.

**Test on #152's hard-step run** ($5.49 more, $26.93 in all; `--engine-gap-rounds 2 --engine-gap-max 2`). The
deep dive's would-be proof of the whole problem (C9) had been thrown away as broken.
- **Ratings.** The judges rated C9 a restatement at significance 3 ("implies the whole problem") and C7 new at
  significance 2.
- **C9, re-judged with its lemmas in view:** both the referee and the adversary passed it. It was then conditional on
  C7, because the one-shot repair of the same resume had already fixed C5 as C5r.
- **C7, re-judged:** still broken. It had used C5r's strong form, which holds only under a hypothesis (H_κ) that
  nothing proves.
- **One gap session on C7** ($1.12) produced C7g1. C7g1 proves C7's full statement with an 8,300-character proof
  citing only C6:
  - iso ≥ (3n−4−[n odd])/4 when 1 ∉ A−A;
  - iso ≥ (n−10)/4 for an interior consecutive pair.

  Both judges passed it, and the novelty panel called it new at significance 2 (2, 2).
- **C9, re-judged against C7g1:** passed. **Every Sidon set with n ≥ 4 has at least (n−18)/4 isolated sums, so the
  whole of #152 now stands as a refereed chain:** C9 ← C7g1, C5r, C1, C6, all valid.
- **My own checks:**
  - I read C9's proof. It plays the a₃+a_j family of sums against a_i+a_n through C1's run identity and C6, and
    every step reads as sound.
  - The C9 and C7g1 inequalities held on 14,042 Sidon sets: Erdős–Turán sets and their reflections for p ≤ 37,
    every Sidon set in [0, 26] containing 0, and random dense sets, half of them forced to contain an end pair. No
    violation; the smallest slack was 3. The bounds are loose, so this only rules out a false statement.
- **Caveats:**
  - Informal. Nothing here is Lean-checked or read by a mathematician.
  - The step's frame said the problem was resolved.
  - #152 was resolved in 2026: the DeepMind prover agent's Lean proof gives I ≥ n²/16 − O(n). The engine's bound is
    linear, so weaker, but it answers the question.
  - C1's quadruple count a−b+1 = c−d is the k = 1 piece of the published double count, so the route partly overlaps
    the published one.
- **What it shows:** before v5 the engine dropped exactly this chain. A referee without the lemmas, plus a lemma error
  that never got a session, cost a complete argument for a research problem.

## Step 2: the engine on whole problems, with no cue (pre-registered 2026-10-06, before launch)

**Question.** Can the engine produce a complete, correct proof of a research problem that was open until 2026, unaided?
Solving one is significance 3 by definition. This is the benchmark the next engine changes will be judged on.

**Protocol.**
- Items: 8 dev items, drawn with `random.Random(20261006).sample` from the 18 masked dev items: #204, #392, #401,
  #570, #618, #865, #888 and #1125. One answer is FALSE (#204); the rest are TRUE.
- Each runs through `timesplit.py discover-screen --discover-mode engine`, tag `engine-v5-dev`, on the live harness at
  `675cb22`. A fresh synthetic alias per item, masked prompts.
- Framing: the whole problem, as the engine frames any open problem. No "resolved" cue, no library (dev items have
  none), and the literature check is skipped on benchmark runs.
- Engine: `--engine-total-budget 28`, 3 sessions, 1 round, a $6 deep dive, gap closing with 2 rounds on at most 2
  targets.
- Success: an unconditional refereed chain that the judges call the problem itself (`engine_complete`), on the TRUE
  side. Each one then goes to Lean, which alone makes it a solve.

**Predictions:**
- complete refereed chains on the TRUE side: 1 of 8 (range 0–2);
- complete chains on the FALSE side: 0 (at most 1);
- validated-new claims both judges rate significance ≥ 2: 2 in all;
- the frontier map's direction right on 6 of 8 (the model's prior guess was right 26 times in 31);
- spend: $25 ± 5 an item, about $200 in all.

**Deviation, recorded after item 1 of 8 (#204) and before any other result.**
- **What #204 showed.** The masked engine recognized the problem: its map wrote "I believe this is Erdős Problem
  #204" and recalled a 2025 arXiv resolution. It then proved the full (correct, negative) answer twice, refereed and
  unconditional. The novelty judges, remembering the paper, rated both proofs "known", so the pre-registered rule
  (`valid-restatement`) missed them.
- **What changes:**
  1. Every item is graded under BOTH rules: the pre-registered one, and "settles". Under "settles", both settles
     judges agree that an unconditional valid claim answers the formal statement; `step2_grade.py` applies it to runs
     made before the check existed.
  2. Items whose engine names the true problem number (`recognized_true`) are reported apart. A recognized item's
     proof is no evidence of unaided research.
- **#204:** pre-registered rule: not complete. Settles rule: complete, correct (false). Recognized: yes.

**Step 2, first five items** (the account's weekly usage limit stopped three others at their first call; they are
being re-run):

| item | truth | recognized | pre-registered rule | settles rule | notes |
|---|---|---|---|---|---|
| #204 | false | **yes** | no | **complete, correct** | the map named the problem and recalled a 2025 resolution |
| #392 | true | **yes** | complete, correct | complete, correct | recognized, so not evidence of unaided research |
| #570 | true | no | no | no | |
| #865 | true | no | no | no | 5 validated-new, 3 with both judges at significance ≥ 2: partial results |
| **#1125** | true | **no** | **complete, correct** | **complete, correct** | **clean: an unaided, refereed proof of a problem resolved in April 2026** |

**#1125, read by me.** The claim: if f: ℝ→ℝ satisfies 2f(x) ≤ f(x+h)+f(x+2h) for all x and all h > 0, then f is
nondecreasing. That is exactly the frozen statement (`Monotone f`). The proof (3,883 characters, `deep/C1`) is
elementary:
1. **Reflection.** L_ρ = {f < ρ} is closed under p, q′ ↦ 2p−q′, so it propagates down arithmetic progressions.
2. **Halving.** A drop f(x) > f(y) forces f(x_k) − f(y) ≥ 2^k·δ along points approaching y from the left.
3. **Chain lemma.** Each consecutive pair in L_ρ quadruples f − ρ at a fixed endpoint.
4. **Conclusion.** Some {f < N} ∩ [y, y+1] is infinite, so it accumulates and its progressions make it dense. That
   gives chains of every length K, so the value at a fixed point exceeds ρ + 4^K·(f(a) − ρ) for every K, which is a
   contradiction.

I checked every use of the hypothesis (h > 0 each time) and every inequality. The one gap is trivial: in Step 5, n must
also make z − p_n < v − u. It is clean by the recognition check: the map named no problem number. Memory of the April
2026 resolution cannot be excluded, only cued less, and the published route has not been compared. Lean verification
launched (`runs/20261006-100843-326327-hardlean-erdos877933`).

**#401: a second clean, refereed, complete proof** (`r1s2/C1`, $8.16, graded by the new settles check at run time).
Not recognized; both settles judges agree; the answer is correct (true). The claim: with q = p_{r+1}, P = p_1⋯p_r and
K = (q−1)/(20 log q), for all large N there are N ≤ m < 2N and 1 ≤ a < N with a!(m−a)! | n!Pⁿ for n = m − ⌈K log N⌉.
So f(r) = (p_{r+1}−1)/(40 log p_{r+1}) witnesses the statement. I read the proof (4,636 characters):
- **The reduction.** The primes below q are absorbed by Pⁿ, because D·log₂ 2N ≤ n. For the primes p ≥ q it suffices
  that v_p(∏_{j<D}(m−j)) ≤ v_p(C(m,a)).
- **Kummer's carry count** bounds v_p(C(m,a)) from below by the digit comparisons a_i > m_i. A deterministic bound caps
  v_p of the product at D/(p−1) + t + Z.
- **Two ranges of primes.** For q ≤ p ≤ D³, digit statistics transferred from (ℤ/p^L)² bound the failures by
  8·0.958^L. For D³ < p ≤ 2N a direct count bounds them by D⁻² + 2/D + o(1).

Every inequality checks, including (2^{1/5}·5/6) < 0.958 and T ≤ L/5 for large N. I believe it is correct. Its Lean
verification is queued behind #1125's.

**#1125 is proved in Lean, end to end.** The engine's complete claim, used as the blueprint, became a Lean proof in one
run of the deductive loop: $2.79, 46 minutes, all 10 hypotheses certified, no re-plan, no recursion.
- **The audit passes all 13 checks** (`benchmarks/timesplit/evidence/1125/`): the 7 Lean checks plus the 6 blindness
  checks. The prompt scan covers the engine run as well as the Lean run.
- **Correction.** The first audit's verdict was FAIL: the Lean stage wrote no time-split record, so the blindness checks
  never ran. `hardsteps_lean.py` now writes one (`results/engine-v5-dev-lean.jsonl`), and the re-run passes.
- **A recall signal.** The engine's novelty judges, not the session that wrote the proof, placed the statement as
  Kemperman's inequality on the Erdős list. They believed it still open and could not recall its number.
- **The whole path:** the engine on the whole problem ($13.04), with no cue and no recognition, then the Lean loop
  ($2.79). That is $15.83 for a machine-checked proof of a problem posed in 1984 and resolved in April 2026.
- **What it is not:**
  - new mathematics;
  - proof that memory played no part, since the model's cutoff is after the resolution.
- The Lean stage still ran outside the time-split runner, which is why its record was written by
  `hardsteps_lean.py`.

**#618: a third clean, refereed, complete proof** (`r1s1/C1`, $19.40, with 5 more validated-new claims, 4 of them
both-judge significance ≥ 2).
- **The claim:** h₂(G) ≤ 12(d+1)n^{3/2} + 2n for every triangle-free G with maximum degree d, so Δ = o(√n) gives
  h₂ = o(n²). That is exactly the frozen statement.
- **Recognition.** The engine named #134, the sibling problem with Δ < n^{1/2−ε} that Alon solved before 2026, and
  treated #618's o(√n) version as the open follow-up. Its judges know no published result for that version. That is
  pre-2026 background knowledge, not a recalled answer, so `recognized_true` is false.
- **My reading of the proof** (3,125 characters). I checked each step:
  - **Repair lemma:** adding a bad pair's edge never makes a triangle.
  - **Construction:** hub v joins to a random independent set L_v. L_v is the set of vertices whose coin, at rate
    q(deg+1), is 1 and whose priority is a local minimum. So P(x ∈ L_v) = q exactly, with independence for pairs at
    distance ≥ 3. The neighbourhood of v's neighbourhood and the neighbouring hubs' sets are excluded.
  - **No triangles:** every triangle case is ruled out.
  - **Coverage:** P(C_v) ≥ q²/e. The covariance is ≤ 0 for adjacent hubs, ≤ q⁴ for hubs at distance 2, and 0 otherwise.
    Chebyshev gives P(X = 0) ≤ (4e+e²)(d+1)²/|T|.
  - **Arithmetic:** with s = 2d² + ⌈3(d+1)√n⌉ the total is ≤ 10.6(d+1)n^{3/2} + 1.5n.

  I believe it is correct. It is probabilistic, so a Lean version must be derandomized over a finite space, which will
  cost more than #1125 or #401.

## Status at the session handoff (2026-10-06, updated 16:00 UTC)

**Finished since the handoff.** #888's step-2 row is in, and the step-2 table below is final.

**#152 whole problem in Lean: partial at $30.34 (certified 9 steps, 5 open), then resumed after two harness fixes.**
- **Budget starvation.** The run had a $70 self-funding cap, and the extension fired once ($20 to $30.48). In cycles 4
  and 5 it deferred every open step for `--min-child-budget`, with $1.21 and then $0.14 left. The extension fired only
  on a hard budget stop, so those two starved cycles counted as a stall and ended the run.
- **Lemma blocks.** A re-plan reused the name `hyp_interior` for a new statement. `Lemmas.lean` then held two
  `namespace` blocks declaring the same constants, so the module stopped building and later attempts could not import
  certified lemmas.
- **Fix.** Both are fixed in `c9ec386`: the extension now fires before steps are deferred for money, and one block is
  kept per name.
- **Resume, recorded in the run's `assistance`.** The resume reset the stall count and set the budget to $40.48, the
  value the fixed rule would have granted. The cap is still $70, and there was no mathematical input.
- **Open steps.** The five open steps are the argument's real core:
  - `split_ne`, the nonempty split identity;
  - `c6`;
  - the three extreme-pair counting bounds `noconsec_rhs`, `interior_rhs` and `edge_rhs`.

**Still running.**

| what | run | how to finish |
|---|---|---|
| #401 in Lean (clean solve 2) | `runs/20261006-105451-996165-hardlean-erdos893177` | 5 of 9 steps certified in its first cycle. If `SUMMARY.line` says `outcome=proved`, run `python3 audit.py --run <dir>`, then copy `Proof.lean`, `AUDIT.md` and the engine proof to `benchmarks/timesplit/evidence/401/`, as for 1125. It started before `c9ec386`; if it ends starved, resume it as #152 was |
| #152 whole problem in Lean (engine chain), resumed | `runs/20261006-013445-204681-hardlean-erdos892759` | the same, with the evidence in `experiments/idea-engine-2026-10-02/evidence/152-chain/`; this is a train item with the "resolved" cue |

**Not started.** #618 in Lean. Its proof is probabilistic and needs derandomizing over a finite space first, so it will
cost more than #1125 or #401. Decide before launching:
`hardsteps_lean.py --engine-run runs/20261006-100457-390025-discover-erdos33868 --claim r1s1/C1 --full-run <same> --chain --id 833868`.

**Next: step 3, open problems.**
1. **Screen.** Map and rate 20–30 high-`partial` open problems with the engine (`--engine-sessions 0
   --engine-min-target-sig 2`), after fetching each problem's forum thread.
2. **Attack.** Pick the 2–3 where both judges rate a reachable target at significance ≥ 2, and run the full engine with
   gap closing. Grade every complete chain by settles and recognition.
3. **Verify.** Send any complete chain to Lean. An open-problem resolution needs human review even after the audit, and
   `claimEligible` stays false until then.

**Step 2, final (all 8 items, $111.45 of engine spend):**

| item | truth | recognized | complete (settles) | correct | validated-new (significance ≥ 2) | spend |
|---|---|---|---|---|---|---|
| #204 | false | yes | yes | yes | 0 | $13.18 |
| #392 | true | yes | yes | yes | 0 | $11.68 |
| **#401** | true | no | **yes** | **yes** | 1 (0) | $8.16 |
| #570 | true | no | no | — | 0 | $9.98 |
| **#618** | true | no | **yes** | **yes** | 5 (4) | $19.40 |
| #865 | true | no | no | — | 5 (3) | $13.35 |
| #888 | true | no | no | — | 4 (1) | $22.66 |
| **#1125** | true | no | **yes** | **yes**, Lean-verified | 1 (0) | $13.04 |

**Against the predictions written before launch:**
- Clean complete proofs on the true side: predicted 1 of 8 (range 0–2), observed **3 of the 6 unrecognized items**,
  with #1125 verified in Lean.
- Complete proofs on the wrong side: predicted 0, observed 0.
- Both-judge significance-2 claims: predicted 2, observed 8.
- Spend: predicted about $200, observed $111.
- The two recognized items were also solved correctly. They are reported apart and count for nothing.

The result exceeds the pre-registered expectation on every axis. It rests on 8 items: one sample, not a rate.
