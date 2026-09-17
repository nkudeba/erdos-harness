# Deductive roadmap — from two benchmark runs to open problems (2026-09-17, revised the same day)

Written after the first two deductive benchmark runs (`benchmarks/deductive/RESULTS.md`), then revised after
an operator correction: the first draft let the Atlas's resolution axis ("can this be closed by any means")
leak into the deductive program, as a SAT-closed hybrid for #273 and as search vocabulary ("finite check plus
a tail") for progress. Those belong to a separate track. This document is about deduction only.

## Two tracks, kept apart

- **Deductive track (this document).** Progress is derivation: statements proved from certified statements,
  the unproved frontier stated in ever simpler objects, and an argument that ends in a proof. Finite
  computation appears only *inside* an argument — a base case by `decide`, a small case split, a numerical
  check of an invariant before it is proved.
- **Resolution-by-any-means track (Atlas `score` axis).** Bounded search, SAT decision procedures, witness
  certificates. Legitimate, measured elsewhere, and never used to describe deductive progress.

## What the two runs established

- Reductions are certified before any plan (colour-flip symmetry on #645, translation invariance on #275).
- Refute-first kills bad lemmas for cents and produced the parity invariants that became #275's case split.
- Skeletons compile as real conditional theorems, and on masked #275 the loop derived its own route (induction
  with a parity split), not the reference's analytic one, and named its hard core honestly.
- Discharging hypotheses is where budget died. Proving an elementary case lemma in Lean *is* derivation; it is
  the deductive bottleneck, not a brute-force one.
- The residual metric (quantifier counts, length) is a surface proxy for content and misfired once, sending the
  loop at the hardest case first. Progress is "more of the argument proved, remainder in simpler objects" — a
  judgement about content, now partly delegated to the plan's own difficulty rating.

## What is still missing for first-principles work

1. **Proof-failure feedback into planning.** A child's failure is discarded today. Its unsolved goals, the
   missing lemma it named, and whether the hypothesis was too strong must reach the next plan, which can then
   add a lemma, weaken a case or introduce a definition. The proof-side analogue of refute-first.
2. **Depth.** A hypothesis child should build its own skeleton, so the argument grows as a tree of lemmas
   rather than a flat list of cases.
3. **Derive first, check second.** Invariant extraction should ask for a derivation with a numerical check
   attached; the empirical step suggests, never decides.
4. **Definitions driven by failure.** A new concept (U(i) on #699) is a documented move after a failed proof
   exposes recurring structure, not a stray option in the plan prompt.
5. **Prover strength**, measured on the benchmark set: elementary hypotheses discharged per dollar.

## The path, in order

1. Build (1) and (2): failure feedback and recursive residuals.
2. Rerun masked #275 at ~$15. Success = the two parity cases *proved* and spliced; the all-odd case attacked
   with failure feedback in place, its obstruction recorded if it does not close.
3. Finish the masked benchmark set (#499, #532 with Hindman as a published premise, #350, #476), recording a
   prediction before each run, to obtain derivation-based base rates: skeleton produced, elementary
   hypotheses proved, depth reached.
4. First open targets, attacked by proof with depth: #699's U(3) (the acceptance chain is known) and #242's
   six residue classes (the identities are certifiable glue). Judge by certified derivation steps and by the
   content of RESIDUAL.md, never by floors or object counts.
5. Residuals are the interface to humans: post U(3) on the forum, import published theorems as named
   premises (`-- PUBLISHED:`), record every residual with `record_finding.py --residual`.

## Budget and expectation

~$4 per cycle for reduce, refute and plan, plus $2.50–$5 per hypothesis attacked; a serious attempt on an open
problem is $50–$100 across sessions on one lane. Full solutions remain unlikely on any schedule. The realistic
deductive output is certified reductions, refuted routes and a hard core stated precisely enough that a human
or a later cycle can attack it — which is what this project produced by hand on #273 and #699 and what the
loop now produces and Lean checks.
