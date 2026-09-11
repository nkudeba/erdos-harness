# Harness review and BSD applicability — 2026-09-09

## Reviewed changes

Reviewed Claude's recent project transcript, current `harness.py`, README and RESULTS. Existing work includes triage, search/construction certificates, specialist tactics, partial results, persistent `program` mode and gated learning. These were preserved.

The recorded evidence supports narrower findings than a general solve-rate gain: search-first reduced the reported #399 cost; #201 search found a finite object but certificate generation needed an assistant-written Boolean proof; the held-out learning comparison tied and correctly did not promote; #172 and #424 were interrupted by the spend limit. The earlier #370/#499 comparison remains incomplete (see `runs/solve-rate-exploration/report.md`).

## Main changes applied

Added `campaign.py`, exposed through `harness.py campaign`, as an opt-in orchestration layer. It maintains explicit proof dependencies and unresolved mathematical gaps, selects ready formal obligations, retains repair candidates and exact compiler errors, records model transcripts, and shares invocation reservations across restarts. Contract-first compilation plus a separate audit rejects proofs of different propositions and proofs requiring added hypotheses. Certificates bind the node, dependency certificates, source/compiled artifacts and verification environment.

The BSD manifest incorporates the supplied PDF's rank-two CM strategy and its specific missing implications. Numerical evidence and literature entries cannot unlock proof dependencies. Rank equality, special families, infrastructure lemmas and the full leading-term formula remain distinguishable. `formal_targets_verified` is deliberately separate from human mathematical meaning review. Detailed mathematics, sources and usage are in README.md in this directory.

The existing repair tests used a permissive fake compiler that accepted any code other than one designated broken string. Claude's new specialist cascade therefore appeared to solve the test before reaching its intended model-repair path. Set `no_cascade=True` in that fixture so the tests exercise candidate/feedback continuity again; production specialist behavior was preserved.

## What this enables next

The next substantial work is a reviewed formal rank/analytic/Selmer interface and an exact formal contract for a restricted known theorem. The campaign makes these deficiencies visible and permits verified results to be reused across sessions. It does not manufacture a missing nonvanishing theorem, prove the independence of rational points from coordinate checks, or translate p-adic vanishing into complex analytic rank without a comparison theorem.

Recursive improvement can accumulate freshly verified lemmas and repair evidence. General strategy promotion should remain tied to completed held-out comparisons plus saved-proof regressions. No autonomous solve-rate improvement or BSD theorem is claimed for this change.

## Validation

See validation.json for completed results and the accompanying logs. All curve fixtures in this pass were assistant-authored; model repair in the integration test uses a deterministic test double with real Lean. No paid model calls were made.

Completed: 41 unit tests and seven helper tests passed; the opt-in campaign suite passed 19 checks (including repeated unit checks and three real-Lean integration tests). The scripted #674 pipeline passed, all 11 saved Erdős proofs recompiled with clean axioms, and five assistant-authored campaign fixtures received fresh certificates. Both general BSD targets remain unverified; campaign model calls: zero.
