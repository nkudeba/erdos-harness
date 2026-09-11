# Self-assessment — the #273 / #677 run, and what it says about the harness

Written 2026-09-11, after attacking the two open problems the Atlas rated most tractable. Neither was
solved (expected). The value was in what the attempt exposed.

## How the run actually went

| | intended | actual |
|---|---|---|
| outcome | no solve, some certified partial value | correct: 19 machine-checked results, 0 solves |
| cost | ~$32 | **$51.46** — the cap did not work |
| failures | 0 | **5 infrastructure faults**, 4 of them budget/limit related |
| results reaching the reader | all | **7 of 19 were nearly lost**, and the summary said `lemmas=0` |

The mathematics behaved as predicted. Every serious problem was in the plumbing, and each one was
distorting the record in the direction of looking *worse or better than the truth*, never neutrally.

## The one root cause behind three separate bugs

Spend under-counted, an open problem reported as `exit=0` (= proved), and a brief that announced "zero
certified results, no search floor" for a run holding seven certified lemmas and a recorded floor.

Three symptoms, one cause: **a run's own `state.json` is not the run.** `--open` splits into `pos`/`neg`
children with their own state; the research program spawns sub-runs that log under `programs/erdos_<n>/`.
Every consumer that read the parent alone got a systematically wrong answer.

Fixed by making that structural, not a habit: `collect_run_facts(run_dir, pid)` walks the whole tree —
child logs, child state, program sub-runs windowed to this run, and partial-result directories on disk
that a crash never got to record — and `spent_usd`, `run_summary_line` and `stage_brief` all read from it.
The lesson generalises past this harness: *when a process fans out, every read-side aggregate must fan out
with it, or it silently reports on a fraction of the work.*

## The capability gap that mattered most

#273's search stage did the cheap arithmetic screen correctly, reached the first genuine candidate
(lcm = 55,440: 43 admissible moduli, density 1.044), and **aborted on its time budget without deciding it**.
Its recorded floor, `exhaustive_to: 55439`, is one below where the work starts — impressive-sounding and
worth nothing.

That is not a budget problem. The stage writes a bespoke Python backtracking loop, which explores maybe
10^6–10^7 nodes before the cap. The question it was asked — *does a finite object with these properties
exist?* — is a constraint-satisfaction problem, and a SAT solver answers that class of question by
construction, returning UNSAT as a **proof of non-existence in the encoded range** that a timed-out DFS can
never produce.

So the harness now has a solver. `python-sat` (CaDiCaL) is on the search allowlist, and because search
scripts run under `python -I` — which hides the user site directory — the runner injects the solver path on
the command line rather than relaxing isolation. The prompt now tells the stage to *prefer a declarative
encoding over a hand-written search* for existence questions, naming the shapes this covers: covering
systems, colourings, hypergraphs, Sidon sets, exact covers, small designs.

**Honest caveat, measured not assumed.** I encoded #273 at lcm 55,440 myself (212,597 variables, 360,379
clauses, with the seven forced moduli asserted and translation symmetry pinned) and CaDiCaL had not decided
it after 75 minutes. So the solver is not a magic wand here. What changed is the *class of thing the harness
can attempt*: it can now state a finite existence question declaratively and get a real UNSAT proof when the
instance is within reach, instead of always hand-rolling a loop that can only ever time out.

## A floor is only as strong as what produced it

`exhaustive_to: 55439` (an arithmetic screen) and `exhaustive_to: 1e9` (every case enumerated) were recorded
in the same field and read identically downstream — and the brief generator, given both, guessed wrong about
each. Floors are now typed: `exhaustive` / `screen` / `published` / `unrecorded`, required from the search
script, accepted by `record_finding.py --floor-kind`, and reported by the brief with an explicit instruction
never to guess the provenance.

## Lessons worth carrying to harder problems

1. **Prefer a decision procedure to a search loop.** The generalisable version: before enumerating, ask
   whether the property can be *stated* to a solver. Applies far past covering systems.
2. **Facts must be gathered from the whole process tree.** Any fan-out needs a matching fan-in.
3. **Type your evidence, don't just size it.** "Checked to N" is meaningless without how.
4. **Fail loud on the honest side.** Every bug here made a failed run look finished (`exit=0`), or a
   productive run look empty (`lemmas=0`). Reporting defaults should err pessimistic.
5. **A cap that isn't tested isn't a cap.** `--run-budget 8` allowed $22.67 for months, presumably.
6. **The formalisation may add a convention the source text omits.** #273's frozen statement requires
   *distinct* moduli — correct and necessary (without it `{0,1,2,3} mod 4` is a trivial solution), but it is
   a reading, not a transcription. Those should be recorded explicitly, not left for a human to notice.

## Built since (2026-09-11), with the live result

All three of the items below were implemented. The reduction stage was then run live on #273 — the problem
whose decisive fact it existed to catch — for **$0.53 and 201 seconds**. It proposed four reductions,
checked three, and refuted one:

1. **The parity decomposition it was built to find.** All moduli `p-1` are even, so a solution is exactly
   *two* covering systems with disjoint moduli drawn from `H2 = {(p-1)/2}`. Found by hand before; now found
   and checked by the harness.
2. **New:** no admissible modulus is `2 mod 6` — if `m ≡ 2 mod 3` then `3 | p`, forcing `p = 3`. So
   8, 14, 20, 26, … are excluded, and *the standard 2, 4, 8, 16 doubling chain is blocked at its second
   step*. I had not seen this.
3. **New:** any solution needs **at least 18 congruences**, because the 17 smallest elements of `H2` have
   reciprocal sum 1.99835 < 2. That also yields a mid-search rejection filter: `Σ 2/m` must reach 2, not
   `Σ 1/m` reach 1.
4. **Refuted:** a translation-symmetry claim whose check could not generate an instance. The claim is in
   fact true (I used it in my own SAT encoding), so this is a *false negative* — conservative in the right
   direction, but the checking is weaker than the proposing.

I re-verified (2) and (3) independently: no admissible modulus below 4000 is `2 mod 6`, and `H2`'s
reciprocal sum first crosses 2 at its 18th element. Both hold.

So the stage does what it was built for, and more. The honest caveat is (4): a check that fails to construct
a test case rejects a true reduction, which costs us silently.

## What I would build next, in order

1. **A reduction stage.** The parity argument that halves #273 — every modulus `p-1` is even, so the classes
   split by parity and you need *two disjoint* covering systems — was found by hand, not by the harness, and
   it is the single most informative fact about the problem. A stage that hunts for structural reductions
   (parity, symmetry, a change of variables, a known equivalent form) before any search would pay for itself.
2. **Escalation instead of abort.** When the screen clears everything below the first real candidate, that is
   the moment to escalate to the decision procedure, not to stop on a timer. The stage should recognise
   "cheap part done, hard part begins here" and change tools.
3. **Record the reading, not just the statement.** A `documented_readings` field on the frozen statement for
   every convention the formalisation supplies that the source text does not.
