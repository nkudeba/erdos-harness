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
