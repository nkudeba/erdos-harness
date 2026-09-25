# What keeps the harness from new ideas (2026-09-24)

**Scope.** This covers everything tested through 2026-09-24:
- the masked deductive benchmarks (`benchmarks/deductive/RESULTS.md`);
- the time-split dev arms: baseline v2, discover-v1, discover-v2 and the #150 top-up;
- the two train diagnostics, #152 and #997.

Train transcripts were read. Dev and test were used only in aggregate (counts, spend, mechanical failure types),
under the benchmark's quarantine rule. Line numbers refer to `harness.py` as of this date.

## 1. What the record says

**What closes.** Constructions and finite checks.
- On the 8 masked benchmark runs, every close came from the **first** skeleton, adopted in cycle 1 and
  discharged at depth 1.
- The other session's summary: the loop "does not yet close problems whose difficulty is an infinite argument it
  has to invent".

**What stalls.** Exactly that invented argument.
- Masked #473 stalled at a prime-pair lemma, #403 at an infinite tail, and #275 after $40.
- Time split: 0 of 27 dev runs solved. In 5 of the baseline's 11 runs the only open hypothesis is named
  `hyp_core`.

**Re-plans have never produced a close.**
- 95 plan candidates in all logs; 31 adopted.
- 39 were refused as "not better than the skeleton in force". These refusals are not recorded as failures (5024),
  so the next plan never learns of them.
- 25 did not compile: 13 unknown identifiers, 12 other errors. There is one compile and no repair round
  (4698-4700).

**Two train runs show both kinds of failure.**
- **#997, where the leap was easy.**
  - Both discovery attempts found the published route in one call each, for $0.28 and $0.35: an admissible tuple
    plus Banks–Freiberg–Turnage-Butterbaugh (2015) plus pigeonhole on an arc. Both were refereed valid.
  - The harness certified 3 pieces and carried BFT as a published premise.
  - No attempt at the remaining bridge ever ran: the cycle-2 re-plan dropped a definition
    (`Unknown identifier IsWellDistributed`), and the 2-cycle cap ended the run with $4 unspent.
- **#152, where the leap was needed.**
  - The published result, by DeepMind's prover agent, is ≫ |A|² isolated sums.
  - The cycle-1 experiments computed exactly that growth. On Erdős–Turán sets they found 7,055 isolated sums at
    p = 149, about 0.32 p², and the Bose–Chowla family also grows quadratically.
  - Under the rules those lines are `OBSERVED`, "never a hypothesis until someone derives it" (1530), and a plan
    conjecture "must be derived" (1601-1602).
  - The plan kept the route of a $0.42 tool-less sketch instead (runs of A−A). It saw only the last 4,000
    characters of the experiment output (4971), so the Bose–Chowla and exhaustive-search data never reached it.
  - The core child's refinement was refused as a restatement. Cycle 2's skeleton did not compile
    (`Unknown identifier α`), and the run ended.

## 2. Where the thinking budget goes

Across all $537 of logged model spend:

| stage | share | mean per call |
|---|---|---|
| Lean proving (`prove`, `prove-agentic`) | 57% | $0.58–0.63 |
| **plan** (the call that chooses the route) | 10% | **$0.32** |
| experiments (the only computation) | 10% | $0.31 |
| refine / reduce / literature / critic | 15% | $0.13–0.33 |

v2's discovery attempts cost $0.09–0.50 each. Its dedicated attack on the named missing step cost $0.07–0.65 per
item: it ran on 6 items, claimed a proof twice, and was refereed valid once. The route is chosen on about thirty
cents of thought, and most of the money goes to formalising whatever route was chosen.

## 3. The limits, ranked

1. **Ideas are formed blind.**
   - Discovery, plan and every judge run with `--tools ""` (249-253).
   - The only computation is one pre-written stdlib script per cycle (4650). Its author never sees it run, and
     the next experiments call gets no earlier output (4632-4634).
   - The agentic prover can run only `./check.sh`, which is Lean (273-280). No stage can compute, look, and try
     again.
2. **Thought is priced like a reply.**
   - Plan, experiments and prove pass no `--effort` flag, so they run at the CLI default (176).
   - Judges and critic are fixed at medium effort with a $1 cap (171); literature is medium with $2.5.
   - Output that runs past its cap is discarded (229-239). A plan that thinks too long is retried at a LOWER
     effort (2695-2699).
   - v2 dropped to medium effort for the same reason: a capped call returns nothing.
3. **Data cannot become a conjecture.**
   - Derive-first is written into both the experiments and the plan prompts.
   - `OBSERVED` lines are parsed (6477) and never used. #152 is the cost of this rule.
4. **The first route locks in.**
   - Adoption needs `residual_improves`, a purely syntactic score (quantifiers × 3 plus connectives plus length/60,
     6073); a tie counts as no improvement (6281-6296).
   - The refinement judge refuses "an equivalent reformulation … a change of variables" (6155-6156). A
     reformulation into a new framework is the usual shape of a leap.
   - The stall count ignores gains in complexity (5037).
5. **One route at a time.**
   - One plan per cycle and one skeleton in force; extra Lean blocks are fallbacks only (5004-5017).
   - Competing skeletons are never explored, and there is no sampling control (190-195).
   - v2 draws 2 informal sketches in total.
6. **The core is starved.**
   - "The harness attacks elementary hypotheses first and leaves hard ones for later cycles" is written into the
     plan prompt (1633-1634).
   - Each child needs at least $2.50 (5088). The default is 2 research cycles, and a recursive child gets 1 cycle
     with at most 2 hypotheses (4848-4851).
7. **Informal work is thrown away.**
   - The plan's `route`, `conjectures` and notes are written to PLAN.md and never read back (4993-4996 against
     4966-4973).
   - Failure digests keep compiler errors but not the attempt's plan (6507-6508).
   - Human direction from `--review-wait` is ignored by the deductive loop (5222).
   - Discovery reaches the harness as 3,500 characters of "not a verified proof" guidance.
8. **Retrieval is thin and, when masked, damaged.**
   - The literature memo asks "who resolved it" in under 600 words, at medium effort. It is computed once and
     reused for every hypothesis (1995-2010, 4838).
   - Masking rewrites "Erdős–Ko–Rado" to "the the catalogue's–Ko–Rado" (verified), and likewise Erdős–Turán and
     Erdős–Szekeres. So masked runs lose technique names.
9. **The instrument cannot see ideas.** `pieces` counts Lean only. An informal leap scores zero until it is
   formalised, and #150's refereed Fekete step still is not.

## 4. What to change, by expected value per dollar

- **A. An exploration stage with a sandbox, run as a loop.**
  - The loop is: compute small cases, look at them, conjecture, test the conjecture, sketch a proof. Several
    rounds run in one session, with a Python sandbox (numpy, sympy, networkx, pysat).
  - Output: a research notebook of conjectures, each with numerical evidence and a proof sketch. It replaces the
    tool-less discovery attempts.
- **B. Empirical conjectures may become hypotheses.**
  - They are labelled `empirical` and never counted as facts. Lean is still the only thing that certifies, so a
    false conjecture simply fails, as any hypothesis can.
  - Show `OBSERVED` lines at the top of the plan's context instead of truncating them.
- **C. A route portfolio.**
  - Draw k cheap sketches from diverse frames, select by numerical tests and a route judge, and run the best two
    as parallel skeletons.
  - Tell the planner when its route was refused, and why.
- **D. Rebalance the spend.**
  - Plan at high effort with a real budget. Give the core one early, well-funded attack instead of the leftovers.
  - Keep partial output when a call hits its cap (stream the JSON).
- **E. Remove the mechanical waste.**
  - Give a plan that does not compile a repair round, and restore dropped definitions. Together these cost
    #152's and #997's cycle 2.
  - Put word boundaries on the masking regex.
- **F. Measure ideas directly.**
  - For time-split items the published route is known. A blind judge can check whether a run's notebook contains
    the resolution's key idea (the "idea hit"). This is evaluation only, and the harness never sees the route.
  - Report it beside `pieces` and solves.

**Order of testing:**
1. Train, on the idea hit: no Lean, about $1-3 per item.
2. Dev, on `pieces` with the paired rule.
3. Test, on solves, never selected on.

## 5. What not to change

Keep the honesty gates as **scoring** rules:
- Lean verification;
- the circularity check on published premises;
- the refinement judge's refusal to count a restatement as progress;
- `claimEligible=false`.

Each of them is right about what counts. What limits discovery is that some of them also act as **exploration**
rules. They stop a reformulation from being explored, an observed pattern from being attacked, and a new route
from replacing the old one. Exploration can be loosened without loosening what is reported as proved.
