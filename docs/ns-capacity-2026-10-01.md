# What would move the harness toward Navier–Stokes-level capacity, at our budget (2026-10-01)

Written after reading OpenAI's own account (openai.com/index/navier-stokes-solution, 2026-09-08, updated 09-10) and
the press record of the Buckmaster–Alpöge work, and after building and screening the four changes in
`benchmarks/timesplit/RESULTS.md`, "Navier–Stokes lessons, built and screened". Claims about OpenAI's system are
OpenAI's; priority and contamination are disputed, and Clay has verified nothing.

## 1. What the result actually took

| ingredient | OpenAI (Navier–Stokes, forced) | Buckmaster–Alpöge (Euler, forced) | this harness before 2026-09-30 |
|---|---|---|---|
| a known route | the forced-blowup programme, reachable through a cached web | Córdoba–Martínez-Zoroa's programme, reproduced with Claude | literature memo from model memory, ≤ 600 words, no tools |
| the tractable alternative | Clay's (C)/(D): with a force, choose the flow and call the residual the force | the same freedom in simpler equations | the frozen statement only; readings recorded, never chosen |
| a curriculum | "easier" problems first; unforced Euler fell (≈100 agents, ≈50 h) and seeded Navier–Stokes | IPM, then Boussinesq, then Euler | none |
| breadth | ≈10,000 concurrent agents; groups seeded with every variant (A, B to prove, C, D to disprove) | two people, two model families, months | 2 informal attempts, 3 fixed frames |
| consolidation | Codex merged each group's most useful insights and fed them back as prompts | the humans | none; v4's retries were independent |
| execution | 130 billion output tokens; 2.7 million messages | "bookkeeping of inductive orders and constants" delegated to the models | one plan call (≈$0.32) chooses the route; 57% of spend formalizes it |
| verification | Lean, 17 h by GPT-6 Astra; an independent kernel replay found no `sorry` and standard axioms only | Lean, 7 days after the first solution | Lean plus `audit.py`; the elaborated-statement identity check goes beyond the replay |
| what still needed people | faithfulness of the formal statement to Fefferman's; readability (Tao: an opaque search has near-zero mathematical value) | readability ("the worst proof the authors had ever seen in mathematics") | human review for any open-problem claim |

Two ingredients matter more than the agent count:
- **The route existed.** The forced alternative gives a construction a degree of freedom, and a niche published
  programme already used it. OpenAI's search began after a rumour that pointed at exactly that programme.
- **A related easier problem fell first and seeded the main attack.** Neither of these is scale.

## 2. The arithmetic

130 billion output tokens is about $6.5M at published GPT-6 Astra rates (VentureBeat's arithmetic). A time-split item
here gets $8–16, and a serious open-problem campaign $50–300, a ratio of 10⁴–10⁶. Nothing at this budget reproduces
the search. What can transfer is the structure that made the compute productive, pointed at problems whose difficulty
is closer to ours.

**The capacity question at our scale is whether more spend buys more progress.** Today it does not:
- #150, doubled from $8 to $16: no new step.
- #990, six discovery attempts over three rounds: no complete proof.
- Iteration 2's extra cycles fed the false direction.

A harness whose results do not grow with spend cannot grow into larger problems, however much compute it is given.

## 3. What was built today, and the first evidence

All of it is behind default-off flags; see CLAUDE.md, "In-run discovery, blueprints and dated libraries".

1. **Discovery in-run** (`--discover on`), with the best proof passed whole.
   - The one dev solve (#1213) came from discovery, but that stage existed only in the benchmark runner, so no
     open-problem run ever had it.
   - The runner also passed the last 3,500 characters of the proof, cutting #678's opening lemma.
2. **Cross-fed rounds and a ladder** (`--discover-mode crossfed --discover-ladder 3`): OpenAI's structure at a
   few dollars.
   - First datum, train #152. The three calibration rounds never produced a complete proof, and their notes graded
     `partial` (the k = 1 double count only).
   - With the ladder, the rungs found the shifted-energy method on easier variants. The main attempt then wrote a
     complete, refereed proof by the published route, the k = 1, 2, 3 counts with Sidon uniqueness of differences,
     for $1.40. That is one item, and Screen A's full results are in RESULTS.md.
3. **Blueprint mode** (`--blueprint on --residual-view outline`).
   - The refereed proof becomes numbered steps, each child gets its step's proof, and sub-residuals expand their
     step before planning.
   - Re-plans see an outline with certified proofs elided. Before, they saw the last 6,000 characters of a residual
     that reached 38,045 on #678.
4. **A dated literature library** (`library.py`, `--library`). Nothing in it is dated on or after the item's
   resolution; arXiv full texts are version 1 only; the problem's own identity patterns are excluded.

## 4. What would move capacity further, ranked by expected value per dollar

1. **Measure the scaling curve before building more.**
   - On the hard tier (the 8 train items where discovery never wrote a complete proof), run crossfed discovery at
     1×, 3× and 10× breadth (attempts per round × rounds) and plot:
     - P(refereed complete proof of the true direction);
     - the idea-hit grade;
     - the fooled-referee rate.
   - About $5 × 3 × 8 = $120 for the three points.
   - If the curve rises, capacity is a budget question and the next dollar goes to breadth. If it is flat, it is a
     model or structure question, and more agents would waste money exactly as OpenAI's would have without the
     consolidator.
   - This is the single most informative experiment available, because it tells us which of the levers below to buy.
2. **Make conversion scale with proof length: a blueprint graph, not a list.**
   - A 166-page proof was formalized in 17 hours because the informal proof was the plan.
   - Here the bottleneck after a correct informal proof is conversion: #435 and #678 each had complete refereed proofs
     and did not close.
   - Next step after Run C:
     - steps carry dependency edges (`USES`, already extracted);
     - independent leaves are attacked in parallel under the cheap-first policy ($0.22 median success);
     - a failed leaf is expanded, not re-planned.
   - A 30–50-step blueprint would cost $15–50 to formalize. That is the size of argument a hard Erdős problem needs,
     and it is within a campaign budget.
   - **Then put Lean inside the discovery loop**, the one thing this harness has that OpenAI's informal search did not
     have until its end:
     - OpenAI's consolidator judged which insights were "most useful" by model judgment. Here a blueprint's cheap
       steps can be formalized during discovery, and their certified fraction is a fitness no referee can fake. The
       measured rates say that signal is reliable: elementary steps 29 of 29 proved, hard 1 of 20.
     - The next round's synthesis then knows which steps are TRUE in Lean and which are open, and aims the
       population at the open ones.
     - This is AlphaEvolve's recipe (model mutation plus an automatic evaluator), applied to proofs rather than
       constructions, at about $10–20 a generation.
3. **Persistent campaigns with a blackboard: time instead of parallelism.**
   - OpenAI's groups shared intermediate results for 88 hours. A campaign here can run for weeks at a few dollars a
     day if each run starts from what the last one learned.
   - Today each run's discovery starts from scratch, with only operator guidance and the program's Lean residual.
     Proposed:
     - each run's final synthesis (established / route / gaps / dead ends) is appended to
       `programs/erdos_<n>/BLACKBOARD.md`;
     - the next run's discovery reads it as its round-0 synthesis;
     - refuted routes already persist in `knowledge/refuted/`, and certified lemmas in `Lemmas.lean`.
   - Cheap to build, and it is the only lever that turns a small daily budget into accumulated search.
4. **Stand on published programmes: reproduce, then extend.**
   - Buckmaster–Alpöge began by having Claude reproduce Córdoba–Martínez-Zoroa's argument, then extended it rung by
     rung.
   - The Atlas analogue is a target class of its own: open problems whose best partial result has a published method
     that plausibly extends (`--requirement` can record it).
   - The run first reproduces and formalizes that partial result, which is a certified partial result for the
     `partial` axis even if nothing else follows. Then it attacks the extension with the library and a ladder whose
     rungs are the intermediate cases.
   - This is the closest honest analogue to what happened with Navier–Stokes, and it suits problems that are hard
     rather than neglected.
5. **The strongest model for the few calls that choose the route.**
   - OpenAI's result needed a model beyond its released best, and OpenAI's own post says the forced-Euler result came
     from an internal Anthropic model.
   - Here, discovery attempts, the synthesis and the first plan are about ten calls per problem.
   - Proposed:
     - `--discover-model`, routing those calls to the strongest model the account has;
     - a no-Lean screen on the hard tier, paired against Opus 5.5, before any adoption.
   - The account's usage limit, not dollars, is the constraint (Fable stops runs at the first stage when it is the
     default), so this needs the operator's go-ahead.
6. **Computation where recall fails.**
   - Exploration lost to tool-less discovery on train (W1 L3 T11), because train items are recall-dominated.
   - On the hard tier and on open problems, computation is the main source of new information: the DeepMind
     singularity work found its objects numerically before any proof.
   - Keep `--explore` for constructions and counterexamples, its one measured strength (#990's Vandermonde family).
     Test it on the hard tier, not the easy one.
7. **Referees that scale with proof length.**
   - The referee is one medium-effort call. A fooled referee costs a whole run committed to a false statement, and the
     risk grows with length.
   - For proofs longer than about 8,000 characters:
     - two independent referees, which must agree;
     - the blueprint extraction as a structural check (a step that cannot be stated precisely is a gap).
8. **Human route hints are the highest-leverage input there is.**
   - The dispute itself is the evidence: one word, "forced", may have collapsed a search worth millions.
   - `atlas-data/research-guidance/<n>.md` already reaches every research stage. Discovery now reads it too.
   - For a flagship problem, an expert's one-paragraph route hint is worth more than any budget here. It is recorded
     as assistance, never hidden.

## 5. What not to expect

At $10–300 a problem and the current model, no Millennium-scale result. The realistic gains are three:
- more solves of problems that are open mainly from neglect, the class the 2026 AI resolutions came from;
- certified partial results on hard problems (special cases, reproduced programmes, explicit constructions);
- an architecture whose output grows with spend, so that a stronger model or cheaper tokens translate directly into
  capacity.

The last one is the lesson of the OpenAI result that applies most directly here: the structure is what made its
compute count.
