# Erdős #488 — feasibility assessment (open problem, site class "falsifiable")

**Verdict: 2/10. Do not run as a search target.**

Statement: for finite A and B = {n ≥ 1 : some a ∈ A divides n}, is |B∩[1,m]|/m < 2·|B∩[1,n]|/n for every
m > n ≥ max(A)?

## Why searching is worse than useless here

A bounded search covering ~1.2×10^13 (A, n, m) triples over 13,870 sets found **zero violations**. That is
expected. The dangerous part is the shape of the near-misses:

| regime | max ratio found | witness | status |
|---|---|---|---|
| singletons A = {a} | 2 − 1/a → 2 | {399}, n=797, m=798 | **already proved safe** (Blair) |
| pairs {a, a+1} | 1.9966 | {299}, n=597, m=598 | **already proved safe** (Blair) |
| min(A) = 2 | 1.107 | {2,5,9,11} | **already proved safe** (MalekZ) |
| open regime, primitive \|A\|=3 | 1.9196 | {37,38,39} | open |
| open regime, primitive \|A\|=4 | 1.8077 | {23,24,25,26} | open |
| open regime, primitive \|A\|=5 | 1.6255 | {14,15,16,17,19} | open |

The supremum 2 is approached **only** along families that are already proved not to violate it. Any ranking
by proximity to the threshold walks up that family reporting 1.997, 1.9999, 1.999999 and looks like it is
converging on a counterexample while proving nothing. In the genuinely open regime the margin *grows* with
|A|, the opposite of what a search wants. Exhaustive reach of the harness's 90-second search stage is
max(A) ≈ 12–14; the region where a counterexample could live is astronomically beyond that.

## Expert signal against tractability

The site's forum has Terence Tao stating the problem stays difficult even after four simultaneous
weakenings; a contributor reporting 13 natural approaches killed by explicit counterexamples; and one clean
inclusion-exclusion reduction refuted by another contributor. Special cases |A| ≤ 2 and min(A) = 2 are proved.

## Unverified third-party resolution claim

The site's proof-claims page carries a **counterexample claim dated 2026-09-05** (Declan Gessel, credited to
a GPT-6/Codex pipeline), using smooth numbers in (T, 256T] with T from a pigeonhole argument, said to be
Lean-checked on a third-party host that marks the problem refuted. **Treat as unverified**: erdosproblems.com
still classes #488 as open/falsifiable, and its own claims page disclaims correctness. It is not a fact, but
it dominates the go/no-go: the problem may already be settled.

## Formalization

`google-deepmind/formal-conjectures` already contains a faithful Lean statement, so there is no novelty in
the formalization step. Mathlib has the needed counting primitives (`Nat.Ioc_filter_dvd_card_eq_div`,
`Finset.inclusion_exclusion_card_biUnion`). A certificate for a real counterexample is the crux and is hard:
`native_decide` is banned by this harness, kernel `decide` dies around m ≈ 10^3–10^4, and the claimed
counterexample's parameters are non-explicit, so no finite check applies.

## If pursued anyway

Best available value is formalizing the *proved* special cases (|A| ≤ 2, min(A) = 2) and the closed form
F(x) = Σ (−1)^(|I|+1) ⌊x / lcm I⌋. Real Lean infrastructure, but it does not resolve #488.

## Harness improvement this surfaced

Scouting reads the problem page but **not** `/forum/thread/{pid}/proof-claims`. That is why
`problems/erdos_488.json` missed a claimed full resolution. Worth fixing regardless of which problem is chosen.
