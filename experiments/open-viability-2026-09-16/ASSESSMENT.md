# Which open problem could the harness fully resolve? — viability assessment, 2026-09-16

Operator session (Claude Fable 5.1, Claude Code), **no paid harness run, no model calls billed to a run**;
session cost unavailable. Inputs: `atlas-data/rankings.json` (snapshot 2026-09-09), `reviewed.json`,
`predict.py estimate --all`, `runs/summary-log.tsv`, the forum caches, and live fetches of #273, #306, #475,
#699 on 2026-09-16. Nothing here is a resolution claim; third-party claims are labelled unverified.

## Method

"Full solution" was read as a complete, Lean-certified resolution of a problem that is **open on
erdosproblems.com** (639 problems), not merely untried by the harness. For a harness that proves by search,
reduction and certificate, a full solution is realistic only when the resolution *is* a finite object at a
reachable size. So the 37 unsolved problems in the site's finite-certificate classes were split by what the
certificate would be:

| kind | problems | verdict |
|---|---|---|
| YES-witness would resolve it | #273, #307, #835, #7, #366, #647, #364 | only #273 has a witness plausibly within compute reach: #7 floor 1.15e7 (lcm), #366 1e22, #647 9.2e18, #364 >1e28; #835 first open case is an ~2M-variable colouring of J(20,10) after k=4,6 (also k+1 prime) failed; #307 has no floor but forum searches imply ≥60 primes in P∪Q |
| certificate would be a COUNTEREXAMPLE to a believed-true conjecture | #742, #23, #583, #628, #1020, #617, #743, #167, #993, #551, #488, #848, #779, #128, #672, #556, #64, #107, #19, #580, #547, ... | a harness cannot "find" these; the positive direction is an infinite argument |
| "resolved up to a finite check" (site: DECIDABLE) | #475, #742, #19 | thresholds are non-explicit or astronomically large (Füredi tower for #742; four-paper large-p proof for #475 with no stated p_0) |

Problems outside the finite classes (#699, #686, #1056, #306, ...) need an infinite argument in at least one
direction, so a full solution there is new mathematics, not a harness capability.

## Ranking for a FULL solution

1. **#273** (covering system, all moduli p−1, p ≥ 5). The affirmative side is a finite certificate: two
   disjoint distinct-modulus covering systems over H2 = {(p−1)/2}. Harness state: parity + 0/4 mod 6 +
   ≥18 congruences reductions checked; fibre/Fourier algebra eliminated 20 of 29 candidate lcms below 4e5;
   exhaustive floor 110880; 9 loose survivors; SAT at L=100800 (~440k vars) undecided in 37 min; best
   constructive attempt left ~12% uncovered. Live thread (unverified): any covering needs a modulus with
   p > 877 (BBMST distortion, ideal_ombrer 12 Jul 2026); Σ1/(p−1) ≥ 1+exp(−3.36e21) via Filaseta–Kalogirou;
   Zeraoulia's proof-claim L ≥ 393120. Honest read: a witness, if one exists, lives at large lcm with forced
   overlaps; the negative side needs a nonexistence theorem (research). **Low probability, but the only
   problem where the whole affirmative path is engineering.**
2. **#306** — not a harness solve: Yuren Tang (Zenodo v0.0.3, 19 Jun 2026) claims a complete Lean proof
   modulo two Rosser–Schoenfeld axioms; site still OPEN. Harness role = verification + closing the axiom
   boundary (Mathlib v4.32.0-rc1 has θ(x) ≤ log 4·x and asymptotic PNT-adjacent bounds, no explicit RS bounds).
3. **#699** — most banked partial value (11 certified lemmas, cluster library) but the residual core is
   Conjecture U(3), an exponential-Diophantine coincidence with no known uniform-in-r route, and i ≥ 4 rests on
   an unverified, ineffective manuscript. No harness expansion closes it.
4. **#475** — DECIDABLE on the site since the four-paper resolution for large p, but no explicit p_0 and a
   2^(p−1)-subset check per prime. Not a target.

## Harness expansions that would matter for #273

- **Constructive search in the halved two-system form**: fix forced moduli (1/m > slack), enumerate free
  subsets outside the solver, add the fibre/Fourier inequalities and the Mirsky–Newman condition as
  constraints, break the residue-translation symmetry, and run candidate lcms past the 4e5 compute cap
  (reciprocal screen + Fourier propagation are milliseconds per L, so 1e6–1e7 is affordable). Candidate order
  by slack, per CLAUDE.md.
- **A certificate format for a found covering system** that the Lean kernel can check without enumerating L
  residues (CRT/tree certificate whose leaves name the covering congruence, or a Bool-reflected checker),
  since kernel `decide` timed out at 420 s on a 3,003-case check and `native_decide` is banned.
- Nothing above helps a NO answer; do not budget for one.

## Other findings recorded this session

- #1056: explicit YES witnesses for every 2 ≤ k ≤ 14 (OEIS A060427; k=14 at p=10428007), a Lean-formalised
  Wilson-reflection construction for four equal factorial residues (third party, unverified); arbitrary k open.
- #686: non-square N settled by Pell (AlphaProof-formalised); squares 4, 25, 49, 64, 81 open, excluded for
  k ≤ 4 and (4, 49, 64) at k = 3; a disproof needs non-representability of one square for all k.
