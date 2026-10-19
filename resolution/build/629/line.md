=== GOAL

**Why no settling line exists.** The formal statement `n = TSMain.answer` asks for one explicit function ℕ → ℕ equal to n(k) for every k. That would pin down m(k) within a factor of 2 for all k, and so would resolve the property‑B gap (√(k/log k) versus k²) that has been open since 1964/2000. A "disproof" does not make sense either, because `answer` is a placeholder. No line can settle the problem as posed. What follows is the line with the best chance of major progress.

**Target: determine n(4) exactly, with machine‑checkable certificates.** Concretely:

- **(U) Upper bound.** Exhibit 4‑uniform multifamilies A, B on a colour set C that are cross‑bad, with |A|+|B| = N* as small as the search can reach, aiming well below 40.
  - Cross‑bad means: no S ⊆ C has S meeting every A‑set and C∖S meeting every B‑set.
  - This gives a K_{|A|,|B|} that is not 4‑choosable.
  - The certificate is an UNSAT proof (DRAT) for "a good S exists".
- **(L) Matching lower bound.** Prove that no cross‑bad pair has |A|+|B| ≤ N*−1. The proof is an exhaustive, pruned search with logged certificates.

An exact n(4) would be the first new exact value since HMT96, and the first beyond the m‑sandwich at k=4. It would also be the first data point on whether n(k)/m(k) ∈ [1,2] stays away from 2 for k ≥ 4. An expert would rate this significance 3. A large improvement of either bound alone, say n(4) ≤ 30 or n(4) ≥ 28, would rate 2.

=== WHY THIS LINE
**The barriers do not block it.**
- The factor‑2 sandwich and the first‑moment barrier stop asymptotic work. They say nothing about one exact small value.
- The Σ₂ barrier stops naive search over pairs. This line removes the outer quantifier on B entirely.

**Validated reductions it builds on.** All of these are standard or ERT80, and are re‑checked in step 0.
- Monotonicity gives n(k) = min{a+b : K_{a,b} not k‑choosable}.
- The pair formulation gives n(4) = min_A [|A| + cov₄(Tr A)].
- Cross‑badness forces τ(A), τ(B) ≥ 4.
- By symmetry we may assume |A| ≤ |B|, so |A| ≤ ⌊(N−1)/2⌋ ≤ 19.

**The inner problem is easy.**
- For fixed A, cov₄(Tr A) is a set‑cover ILP.
- Its universe is the minimal transversals of A, a few thousand sets for ≤ 23 edges.
- Its candidate columns are the 4‑subsets of those transversals.
- So the Σ₂ search collapses to a Σ₁ search over A (at most 19 edges, τ ≥ 4) plus an ILP oracle.

**The ILP oracle is monotone, which gives strong pruning.**
- If A′ ⊆ A, then Tr(A′) ⊇ Tr(A) as families of transversals, so cov(Tr A′) ≥ cov(Tr A).
- Hence every partial A yields a lower bound by LP duality.
- Families with τ ≥ 4 and few edges have huge transversal families. For example, 4 disjoint edges give 256 minimal transversals, each of which must itself be a B‑set. Such families are pruned immediately.

**A natural seed for (U).**
- Take A = an Östergård 23‑edge non‑2‑colourable 4‑graph, or a subfamily of one.
- Then cov ≤ |A|, which reproduces the bound 2m(4) = 46.
- The real search is over sub‑families and perturbations, trading |A| against cov.

**No team results exist yet.** The team has produced nothing, so nothing here rests on unvalidated work.

=== PLAN
None of these steps is established by the team.

0. **Verify the foundations in writing.**
   - Re‑derive the pair formulation and the ≤ / ≥ m(k) sandwich.
   - Check that the convention in `n` matches: Fin m, `Colorable 2`, strict `<` on `listChromaticNumber` (presumably ℕ∞‑valued).
   - Check n(0)=1, n(1)=2, n(2)=6 and n(3)=14 against the code.
   - Prove or discard the "strictness lemma" n(k) > m(k). The frontier map cites it from "T4", but the team has no validated output, so 24 is not yet established. Until it is proved, treat 23 as the lower bound.
1. **Build the oracle.** Given A, it should:
   - enumerate the minimal transversals with a Berge/FK dualization;
   - reject A if τ < 4;
   - solve the set‑cover ILP for cov₄ exactly (CP‑SAT or Gurobi);
   - emit (A, B) and a SAT UNSAT certificate for the cross‑bad check.

   Validate it by reproducing n(2)=6 (C₃ pairs), n(3)=14 (Fano/Fano), and the HMT bound 40.
2. **Upper‑bound search.**
   - Start from the seeds: Östergård's m(4) extremal graphs, the HMT96 construction, and designs such as complements of the 4‑(11,5,1) or S(3,4,8) blocks.
   - Run local search and simulated annealing over A, with objective |A|+cov₄(Tr A).
   - Re‑verify the best pairs independently with a second SAT solver.
3. **Pruning lemmas for (L).** Prove each on paper before using it:
   - colour‑merging for colours of degree 1 in A∪B;
   - no A‑set is contained in the union structure in a way that makes it redundant;
   - |A| ≤ |B|;
   - an LP‑duality lower bound on cov from fractional packings of transversals.
4. **Lower‑bound search.**
   - Use orderly generation (canonical augmentation, nauty) of 4‑uniform multifamilies A with τ ≥ 4 and |A| ≤ ⌊(N*−1)/2⌋.
   - At each node, prune when |A| + LPbound(cov(Tr A_partial)) ≥ N*. Monotonicity makes this bound valid for all extensions.
   - Log every leaf.
   - Raise the target N incrementally: 24, 25, …. Each completed level is a publishable lower bound even if the gap does not close.
5. **Cross‑checks.**
   - Run an independent reimplementation, or a randomized audit of leaves.
   - Optionally, give a Lean proof that the final explicit pair is not 4‑choosable (decide or SAT certificate). This proves only `n 4 ≤ N*`, not the theorem.

=== PITFALLS
- **Do not claim to settle `erdos_629`.** Only n(4) is targeted. Any result must be stated as a bound or value for n 4, not as the theorem.
- **Do not rely on the unverified claim n(k) ≤ m(k+1).** Do not rely on the "strictness" bound 24 until step 0 proves it.
- **Use multifamilies, not sets.** A and B may repeat sets, since different vertices can get equal lists. A search over simple families can miss optima, so allow multiplicity.
- **Get the cover condition right.** The condition is that every minimal transversal T of A contains some B‑set, which forces C∖T to miss it.
  - Do not cover only the minimum transversals.
  - Do not forget that B must also satisfy τ(B) ≥ 4. This holds automatically from cross‑badness, but check it in the verifier.
- **Do not walk into the Σ₂ wall** where sp4cerat stalled: never search jointly over (A, B) with a plain SAT encoding.
- **Do not attempt random constructions or asymptotic constants.** The first‑moment barrier and the factor‑2 sandwich defeat them.
- **Pruning bounds must be monotone‑valid.** Use LP lower bounds on cov for partial A only through the inclusion Tr(A′) ⊇ Tr(A). Never prune with heuristic ILP time‑outs.
- **Do not interpolate** from k = 2, 3 (the "no pattern" barrier).
