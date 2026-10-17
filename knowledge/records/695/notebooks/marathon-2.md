## Result
Marathon leg 2. No new PROVED claim this leg. The main product is three tested, self-contained LONG computations that decide P(22), the first open term (A082449(21), per leg-1/C3), and probe P(23). P(22) can only come out of a LONG: the 120 s cap allows about 1/30 of the needed work, and a checker cannot split the dense levels.
- Leg 1's LONGs (long_p22.py, long_beam.py) never ran. Their outputs are not in TASK.md, and their sources are not in the sandbox (the notebook copy is truncated). So this leg rewrote the refined pyramid from scratch (pyr.py → long_*.py).
- Validation: TEST mode T=20, Y=7.36e12 reproduces all 19 checkpoint triples (|Full_t|, |C_t|, min) of leg-1/C1 exactly, plus the top set {7242080052479} (47 s). Plain mode at T=19 also matches (37 s). Two different sieve/candidate thresholds give the same level-10 and level-11 sets.
- Nothing is claimed about the LONG outcomes before they run.

## Claims
None new this leg. Status of the earlier claims this leg's LONGs will decide:
- leg-1/C2 (CONJECTURED: P(22) > 1.792e14). long_p22 recomputes R_21 ∩ (0, 2.17e14] and R_22 ∩ (0, 8.66e14] from scratch. It does not rely on deep/long_pyr21.
- P(22) itself. It is exact if long_p22 and long_p23 agree on min Full_22: the two runs use different A_t at every level, so they take different sieve/candidate code paths.

## Routes
- ROUTE: fresh rewrite of the refined pyramid (pyr.py; REFINED flag; Lemma R as in leg-1/C1) | OUTCOME: T=20, Y=7.36e12: all 19 checkpoint triples equal leg-1/C1's Data line, and the top set is {7242080052479}, in 47 s. Plain mode T=19, Y=1.84e12 gives the same Full sets (as it must, since A_t is the same) | BARRIER: P(22) at Y=8.66e14 is ~29× the per-level range, so it must be a LONG.
- ROUTE: memory control for the LONGs (release S_{t−1} before building the int64 array; uint32 per-segment offsets; block-wise gen_mult and Σ1/r; numpy chunks in place of Python lists of found primes) | OUTCOME: peak estimates ≈ 5 GB (long_p22) and ≈ 10 GB (long_p23); TEST modes unchanged | BARRIER: none.
- ROUTE (analysis): certify P(21) or leg-1/C2 inside one 120 s checker | OUTCOME: infeasible. C2 needs refined T=22 at Y=1.792e14, which is 6.1× the T=20 test: ≈ 290 s, with the dense sieve levels alone ≈ 160 s. Splitting across checkers fails because the next level needs the whole previous set (≥ 10^7 primes), which cannot be embedded | BARRIER: numpy sieve ≈ 5 ns per odd number, and candidate tests ≈ 1.1 µs each.
- ROUTE (analysis): a further refinement of Lemma R (tail words with ∏(m_i/2) < 4, i.e. one 4 or one 6 among 2's), to halve the Full ranges again | OUTCOME: not implemented. Each word needs its own wheel/sieve over (A_t, B_t] at the dense levels, which costs as much as the saving there; the gain is ≤ 2× | BARRIER: engineering cost vs a ≤ 2× gain; not needed for P(22).

## Next
NEXT: read the LONG RESULTs.
- (1) If long_p22 and long_p23 agree on min Full_22 = p*, record P(22) = p* with its witness chain. Check g(p*) (gpf iteration) for the A082449(21) identification (leg-1/C3 criterion), and Pocklington-certify the chain in a checker.
- (2) long_p23 either gives P(23) (if ≤ 3.465e15), or P(23) > 3.465e15.
- (3) The level-21 set printed by long_p22 settles leg-1/C2.
- (4) The extension lines give upper bounds for P(23..25) to plan any later run.

LONG: long_p22.py | 2 | P(22) exactly: refined pyramid (Lemma R), exhaustive over (0, 866284735109723], where the bound is the endpoint of the certified deep/C3 chain. It prints the checkpoint triples for t=2..22, the level sets R_18..R_22 (truncated), and the witness chain with exact H via the Pratt recursion. It also prints non-exhaustive extension upper bounds for P(23), P(24). TEST mode (T=20) reproduces leg-1/C1 in 47 s; the full run is estimated at ~35 min (cost ∝ Y^1.12, measured), with peak memory ≈ 5 GB.
LONG: long_p23.py | 2 | P(23) if P(23) ≤ 3465138940438892, else the lower bound P(23) > 3.465e15. Refined pyramid T=23 with Y = 4·866284735109723, so A_22 = 866284735109723 and the same run also gives Full_22 = R_22 ∩ (0, 8.66e14], i.e. P(22) again, as an independent determination at a different scale. Est. ~75 min, ≈ 10 GB. Same code as long_p22 (TEST mode verified).
LONG: long_p22b.py | 1.5 | lowest priority cross-check: plain pyramid (Lemma 1 only), different SEG, LQ and threshold, over R_22 ∩ (0, 433142367554861]. Its Full_t (t<22) must equal long_p22's exactly (same A_t). TEST mode (T=19) reproduces leg-1/C1 in 37 s.

## Data
- Per-level timing of pyr.py at T=20, Y=7.36e12: the dense sieve levels 2–10 take 26 s, level 11 (cand) 13 s, and levels ≥12 under 8 s. Candidate tests cost ~1.1 µs each and the sieve ~5 ns per odd number, so break-even is at EA/imax ≈ 0.005.
- Scaling test, T=20, Y=1.25e13 (1.70× range): 85 s, against 47 s at the base range, so cost ∝ Y^1.12. Counts (t, |Full_t|, |C_t|) with A_t = ⌊1.25e13/2^{21−t}⌋: (2,1497804,0) (3,2870281,0) (4,5509006,0) (5,10428581,0) (6,16522364,0) (7,18164838,0) (8,14144865,0) (9,8433462,0) (10,4075050,0) (11,1679847,0) (12,613064,0) (13,198669,0) (14,55452,0) (15,12981,0) (16,2543,1) (17,429,1) (18,77,1) (19,11,1) (20,1,0). The minima are P(t) as in leg-1/C1, and R_20 ∩ (0,1.25e13] = {7242080052479}.
- Extension from the T=20 test (300 smallest top/level-19 elements, m ≤ 3000), upper bounds only: P(21) ≤ 343763783538809 and P(22) ≤ 2347657944470459, both worse than the known values/bounds. This shows that the extension is weak when seeded from a small exact range.
