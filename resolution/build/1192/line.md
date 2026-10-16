=== GOAL

**There is no threshold to make explicit.** No known result of the form "for all r ≥ r₀" or "for all n ≥ N₀" reduces erdos_1192 to a finite check, and the prompt contains no DECIDE section. The formal statement asks, for every r ≥ 2, for an infinite set A ⊂ ℕ that is an eventual basis with Σ_{n≤x} f_r(n)² = O(x). The negation asks for a single r where no such set exists. Neither side has a "sufficiently large" theorem.

- **Settled so far:** only r = 2 (Ruzsa 1990; the team's Variant 2 reproof).
- **Best available extension:** the next value, r = 3. This line cannot settle the problem, because settling needs every r. So I choose the line with the best chance of the largest explicit range of r, and I say so here.

**Target statement (G₃ with the T3 escape hatch).** There are constants C, c > 0 and moduli m_k → ∞ with 2 ≤ m_{k+1}/m_k ≤ C, and sets S_k ⊂ ℤ_{m_k}, such that:
- (a) E₃^{ℤ_m}(S_k) ≤ C·m_k;
- (b) |ℤ_{m_k} \ 3S_k| ≤ m_k^{1/5}.

By T3 and the blackboard equivalence CORE ⇔ (G_r), this gives a basis of order 3 with Σ_{n≤x} f₃(n)² ≪ x.

**Why this is worth the budget.**
- Proving it is a genuine new theorem: Erdős–Tetali leaves a log² x loss for every r ≥ 3, and Ruzsa's method is stuck at r = 2. An expert would rate it 3.
- A construction whose mechanism visibly generalises to every r would settle the problem. That is the 0.01.
- Partial outcomes still have value:
  - an explicit algebraic S with hole set of dimension 0 for r = 3, without (b)'s exponent;
  - a computer-verified table of (G₃) witnesses for all m up to some explicit M.

  Each would be rated 2.

=== WHY THIS LINE
**Which barriers it avoids.**
- The Janson and covering-by-translates (BJR) barriers kill all randomness-based coverage. The CORE reduction moves the problem entirely into finite cyclic groups, where algebraic, dependent constructions are allowed and those barriers do not apply.
- The Galois splitting barrier is precise about what fails. A single Bose–Chowla B₃ set of size q in ℤ_{q³−1} covers exactly the targets whose associated monic cubic splits: the identity class of S₃, a 1/6 fraction.
- The barrier explicitly leaves open pattern families whose joint monodromy is *intersective*. For S₃ acting on the roots of the target cubic, that means:
  - one pattern detects the identity class (Bose–Chowla, three linear factors);
  - one detects transpositions (one rational root plus an irreducible quadratic factor);
  - one detects 3-cycles (irreducible cubic).
- For r = 3 the conjugacy classes are only three. This is the smallest case where the obstruction is a concrete group-theoretic covering problem rather than an analytic one.

**Why the endgame is cheap.** T3 means exact covering is not required. Exceptions of dimension 0 (O(1)·q^{O(1)} holes with exponent < 3/5 in q, since m ≍ q³) are patched for free by Hölder. So a construction covering all classes up to lower-dimensional degenerate loci is enough. The degeneracy barrier also allows those loci as long as the curves are non-degenerate.

**What it builds on.** Every ingredient is on the KNOWN list: Bose–Chowla, the forced-density bound |S| ≍ m^{1/3}, gluing, truncation, the CORE equivalence and T3. The team has no refereed results yet, so none of these blackboard reductions is validated. Step 1 must referee them.

=== PLAN
1. **Referee the reduction chain** (blackboard-established, not yet refereed). Write out and check four pieces:
   - (G_r) ⇒ CORE: coverage rA_k ⊇ [2r·m_k, rL·m_k] must overlap across scales. This needs L ≥ 2C, so that consecutive block ranges overlap.
   - CORE ⇒ (G_r).
   - T3: the Hölder bound on mixed energies, with E(P) ≤ |P|^{2r−1} for the patch set.
   - L^{2r}-Minkowski gluing.

   Then check the result against the Lean conventions: ordered tuples, 0 ∈ ℕ, the sum over range(x+1), and the eventual quantifier. Deliverable: a referee-passed proof that the target statement of GOAL implies erdos_1192 at r = 3.

2. **Coordinatise Bose–Chowla for r = 3.**
   - Setup: q a prime power, m = q³ − 1, θ a generator of F_{q³}^*, γ = θ, with minimal polynomial h.
   - For β ∈ ℤ_m, define its target cubic g_β: the monic cubic with g_β ≡ λ·θ^β mod h, for a unique scalar λ.
   - Determine exactly which β are hit by 3-sums: g_β splits over F_q. Allow repeated roots (r! counting), and account for the F_q^* scalar coset, so that β ranges over a coset structure of size q − 1.
   - Prove the energy bound E₃ ≤ 6q³ + O(q²).

3. **Build gadgets for the two missing classes.** Look for sets T₂, T₃ ⊂ ℤ_m, each of size O(q), with the following properties:
   - Patterns s + s′ + t (s, s′ ∈ B, t ∈ T₂) cover the β with g_β of type (linear)·(irreducible quadratic).
   - Patterns from T₃ cover the β with g_β irreducible.
   - The energy stays O(q³).

   Candidate sources:
   - logs of elements of subfields after moving to F_{q⁶} (m = q⁶ − 1), where quadratic and cubic irreducibles split;
   - Frobenius twists x ↦ x^{q^j};
   - several generators γ_i, as the sign-trick barrier leaves open.

   For each candidate, compute the monodromy group of the pattern's sum map and check that it is intersective over S₃. This is a pure Chebotarev / Galois computation.

4. **Run a computational search in parallel.** For r = 3 and all m ≤ M (target M ≈ 10⁵ with bitset sumsets), search structured ansätze:
   - unions of ≤ 6 Bose–Chowla-type sets with twists and dilates by units u ∈ ℤ_m^*;
   - Singer-type B₃[g] sets plus greedy patches restricted to ≤ m^{1/5} holes.

   Record min E₃/m and the hole count. Use this both to find the pattern of step 3 and to produce an explicit verified range "(G₃) witnesses with E₃ ≤ C·m exist for every m ≤ M". Log every witness so it can be re-checked independently.

5. **Bound the hole set.** If step 3 succeeds up to degenerate loci (repeated roots, g_β with special coefficients), show the exceptional β number O(q) = O(m^{1/3}). Then reduce the exponent below m^{1/5}, or prove a sharper T3 variant using the B₃-structure of S instead of the crude bound E(P) ≤ |P|^5.

6. **Generalise.** Express the construction in terms of the conjugacy classes (cycle types) of S_r and check whether the gadget count stays O_r(1). Only this step converts the line into a settlement.

=== PITFALLS
**From the team's work.** There are no referee findings yet: the team produced no claims. The only checks so far are the blackboard computations, and these are unrefereed. Treat T3, CORE ⇔ (G_r) and the gluing step as unverified until step 1 is done.

**Barriers this line must not walk into:**
- **Janson / BJR:** randomness may only *select among* algebraic gadgets. Any random or greedy patch of a positive-density, or even m^{1/3+ε}-size, hole set reintroduces the log² loss.
- **Galois splitting:** bounded unions of translates or dilates of one B₃ set behave independently by Chebotarev. They raise coverage from 1/6 toward 1 only geometrically, never to exceptions of dimension 0. Every candidate in step 3 must come with a monodromy computation, not just numerics.
- **Sign-trick ceiling and birational-elimination failure:** do not retry ± weights with polynomial g of degree ≥ 3 in characteristic 0. The open variants are char p, rational g, several γ, and Frobenius twists.
- **Degeneracy:** gadgets lying on lines, APs or hyperplanes give energy ≫ m through the "one piece used r times" pattern. Check E₃ on all mixed patterns, including s + s + t.
- **Analytic lower-bound methods:** any impossibility argument must fail at r = 2.

**Formal-statement traps:**
- f_r counts **ordered** tuples over ℕ, including 0. The bounds E ≥ (r!)²·x and E₃ ≤ 6q³ must use ordered counts.
- The sum is over range(x+1), and O is taken along atTop on ℕ.
- An eventual basis is enough; small n may be uncovered.

**Do not oversell:** a result for r = 3, or a verified range m ≤ M, does not settle erdos_1192. Before calling anything new, check prior claims, as with the #769 lesson.
