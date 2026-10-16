=== GOAL

Settle the formal statement by disproof. The statement quantifies over all k, so one counterexample at any single k ≥ 2 refutes it. I choose k = 3, and k ≥ 4 is also acceptable.

**Target (single-deletion strengthening, "DECIDE").** Construct an explicit set A ⊆ ℕ with two properties:
- A is an asymptotic basis of order k.
- For all but finitely many a ∈ A, the set A \ {a} is not an asymptotic basis of order k+1.

**Why this settles the problem.**
- Let B ⊆ A be infinite. Then B contains some bad a.
- Since A \ B ⊆ A \ {a}, we have (k+1)(A\B) ⊆ (k+1)(A\{a}). That set already misses infinitely many n, so A \ B is not a basis of order k+1.
- Minimality comes for free. Order k implies order k+1, so a deletion that fails order k+1 also fails order k.
- So A refutes `erdos_881` exactly as written, not just the informal wording.

If this works it is a complete negative answer. An expert would rate it 3, and it would be essentially final once formalized.

=== WHY THIS LINE
- **Where to look.** The single-deletion barrier (P3) forbids cofinite badness only for k = 2, because the bad set is Sidon there. Its proof uses that a 2-representation determines its partner, which fails for k ≥ 3. The statement lets us pick k, so we move to where that barrier does not apply.
- **Decidable by computation.** The target is first-order in each a. That escapes the logical barrier ("for every infinite B" is second-order). Candidate sets can be tested with exact sumset computations (bitset convolution up to about 10⁷), not with probabilistic heuristics.
- **No interaction analysis.** Each deleted element is handled on its own. That sidesteps the interaction barrier and the need for an adaptive B, which is where the forum's k = 2 write-up has its gaps.
- **Shape of a counterexample.** The barriers tell us what to build:
  - It cannot rest on residues (residue barrier), so rigidity must be Archimedean or digit-based.
  - It must be thin and concentrated (P1).
  - For each large a it needs a witness n_a. By the gap barrier with B = {a}, A ∩ (n_a − a, n_a − N₀] ⊆ {a}. So A needs nearly empty windows of length about a, placed at heights much larger than a, and one window can serve many a.
  - Elements must not split into two elements of A. This is the carry barrier, so digit sets must use non-downward-closed digit patterns or spacer blocks.
- **What we build on.** There are no validated team results; the previous run produced 0. We rely only on standard facts from the frontier map: k ≤ 1 is settled, order k implies order k+1, the gap inequality, and the carry obstruction.

=== PLAN
0. **Literature kill-check (≤ half a day).** Search Grekos, Erdős–Graham 1980, Plagne 2004, Deschamps–Farhi 2007 and Hegarty 2008 for any theorem of the form "for every basis A of order h, ord*(A\{a}) ≤ h+1 for infinitely many a."
   - If such a theorem exists for h = k, this line is dead.
   - In that case switch to the variant: a finite-set deletion family (bad pairs or triples) such that every infinite B contains a bad finite set. Ramsey reduces this to an infinite clique of bad pairs. This is still first-order per finite set.
   - Also confirm the exact Mathlib definition of `IsAsymptoticAddBasisOfOrder`: exactly k summands, repetition allowed, whether 0 ∈ A matters, and eventual cofinality.

1. **Pin down necessary conditions (prove, short).** For a bad a with witness n:
   - every element a' ≤ n − N₀ of A other than a satisfies n − a' ∈ kA;
   - every k-representation of n − a' contains a;
   - A ∩ (n − a, n − N₀] ⊆ {a}.

   Then write the "window-sharing" condition, under which one empty window (m, m+L] serves every a ≤ L via n_a = m + a. Not yet established.

2. **Design candidates.** Use thin, multi-scale, carry-blocked sets for k = 3:
   - base M with digit blocks separated by spacer zeros;
   - per-component digit sets D such that no element of D lies in D + D within a block;
   - scale-wise "reflected copies" of initial segments next to long empty windows, as the CORE predicts.

   Keep A(x) ≍ x^{1/3}. Use P1 as a filter: require max_{m≤x} r₃(m) ≥ c·A(x).

3. **Computational screen.** For each candidate, compute 3A and 4(A\{a}) for every a up to X (exact bitsets).
   - Record which a are bad, and whether the witnesses lie in the range where the 3-sums are already covered.
   - Iterate on the design until all a beyond a small threshold are bad, with witnesses that recur at every scale.
   - A SAT or ILP search over periodic block patterns can propose digit sets D for this step.

4. **Prove the two properties** for the surviving candidate:
   - (i) 3A ⊇ [N₀, ∞), by a block-by-block digit argument;
   - (ii) for each large a, an infinite family of witnesses n_{a,j} (one per scale j) with every 4-representation containing a. This is a carry analysis showing no 4-sum can reach n_{a,j} without a.

   Then have the work refereed adversarially, with specific attacks on carries and boundary blocks.

5. **Lean.** Define A explicitly and prove the two lemmas. Derive ¬erdos_881 by instantiating k = 3, using the reduction in GOAL, and getting minimality via order k implies order k+1.

=== PITFALLS
- **No team errors to inherit.** There are no team results yet. The relevant errors are the referee-flagged gaps in the forum write-up; do not import its claims unverified.
- **Residue barrier.** Any rigidity that factors through ℤ/m is doomed, because kW = G implies (k+1)W = G.
- **Carry/telescoping barrier.** Check that no large element equals a sum of two (or more) elements of A in a way that frees a summand. Downward-closed digit sets (E∪O-type) fail immediately.
- **Concentration barrier.** Random or probabilistic constructions cannot work. Any candidate with r = O(log) is dead.
- **Gap barrier.** Every bad a needs an almost-empty window of length about a. Bounded-gap or "smooth" sets fail. Make sure the windows do not destroy order-3 coverage.
- **Finite-range evidence.** Bad behaviour up to X proves nothing. Witnesses must come in a provable infinite family for every large a, not just for the a that were tested.
- **k = 2.** Cofinite badness is impossible there, so do not drift back to it. The bad set is Sidon.
- **Lean conventions.**
  - "Exactly k summands" with repetition, and with 0 ∈ A or not, changes small cases.
  - Order k implies order k+1 needs n − a₀ ≥ N₀.
  - The ∀k statement is refuted by a single k: do not over-prove.
- **Novelty.** Before claiming anything is new, check for prior claims (forum, 2026-05-03). A clean disproof of this kind might already exist in the literature under the name "essential elements of order h+1".
