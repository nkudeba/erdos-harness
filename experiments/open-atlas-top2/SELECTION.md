# Selecting the two "most solvable still-open" problems from the Atlas

Date: 2026-09-10. Snapshot: `atlas-data/rankings.json` (2026-09-09, 1,217 problems).

## What the Atlas actually says

Filtering to `status == "Unsolved"` leaves 639 problems. On the **solvability** axis (`score`, "can the
harness produce a *complete* proof") the maximum among them is **25**, and **20 problems tie at 25**.
All 20 are unreviewed and carry the identical generic signal breakdown:

    Base: unresolved target      +15
    External formal statement     +3
    Library fit: number theory    +5
    Compact statement             +2

This is exactly the collapse `CLAUDE.md` documents: for an open problem a complete proof means new
mathematics, so every open target scores low and the tail is undifferentiated. The Atlas's own `rank`
field breaks the tie **by problem number** (`meta.method`: "ties ordered by problem number"), which
would nominate #10 and #11 — an artefact, not a judgement.

## Tie-break used

1. `score` desc → 20 candidates at 25.
2. `partial` desc (the Atlas's second axis, the one CLAUDE.md says actually matters for open targets)
   → 8 candidates at (25, 51): **252, 273, 288, 324, 389, 406, 677, 1056**.
3. Among those 8, keep the ones where **one direction is a finite certificate** — the only thing this
   harness has ever demonstrated on an open problem. That leaves:
   - **#273** — affirmative answer = an explicit finite covering system. *Selected.*
   - **#677** — negative answer = one explicit triple (n,k,m). *Selected.*
   - #1056 — affirmative answer is finite only for a *fixed* k; the site (and the open content) is the
     ∀k version, so a certificate does not resolve it. Not selected.
   The other five (#252, #288, #324, #389, #406) need an infinite/asymptotic argument in both directions.

All eight sit in the site's "This is open, and cannot be resolved with a finite computation" class, so
the site's own falsifiable/verifiable/decidable labels could not be used as the discriminator.

## Honest caveat

The Atlas does not distinguish these eight. Step 3 is *my* judgement, not the Atlas's, and a different
reading ("follow the rank column literally") would have picked #10 and #11. Recorded here so the choice
is auditable.
