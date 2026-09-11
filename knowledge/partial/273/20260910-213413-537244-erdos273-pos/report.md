# Partial result — Erdős #273 (run 20260910-213413-537244, direction pos)

**Status: PARTIAL — the main theorem was NOT proved.** #273 is open; these sorry-free lemmas compiled
against the frozen statement and are kept for reuse. Not a resolution; requires human review before any
external claim.

> Recovered by hand: the run crashed in `stage_partial` (AttributeError on the declaration-name regex,
> now fixed in `harness.py` with `tests/test_decl_name.py`) after writing `partial.lean` but before this
> report, `state["partial"]` and the `partial/saved` event — so the run reported `infrastructure_error`
> and `lemmas=0` while the lemmas sat on disk. Independently recompiled and audited: sorry-free, axioms =
> [propext, Classical.choice, Quot.sound].

## Compiled lemmas
- `erdos_273_count_le`
- `erdos_273_density`
- `erdos_273_even`
- `erdos_273_pool_bound`
- `erdos_273_mem_allowed`
- `erdos_273_not_selfridge`
- `erdos_273_cast_sub`

The substantive ones:

- `erdos_273_density` — every finite covering system whose moduli divide `L` satisfies `Σ 1/mᵢ ≥ 1`.
  The standard density necessary condition, formalized; reusable for any covering-system problem.
- `erdos_273_pool_bound` — if the distinct moduli additionally lie in a finite pool `P`, then
  `Σ_{d ∈ P} 1/d ≥ 1`: the reciprocal screen that rules out a candidate lcm without exhibiting a covering.
- `erdos_273_not_selfridge` — no admissible covering has all moduli dividing 360, since the eligible
  moduli there are {4,6,10,12,18,30,36,40,60,72,180} with reciprocal sum 7/9 < 1. This certifies exactly
  why Selfridge's divisors-of-360 covering needs the modulus 2 = 3−1, which `p ≥ 5` forbids.
