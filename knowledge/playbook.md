# Harness playbook

One lesson per bullet. Optional `[tags: ...]` steer retrieval (matched against the problem statement,
frozen theorem, and compiler errors); `always` forces inclusion. Entries are appended by
`python3 harness.py retrospect <run_dir>` (LLM-proposed, compiler-grounded) and by hand. Keep each
bullet self-contained and under ~300 characters.

- [tags: always] Copy the frozen theorem statement byte-for-byte (same binders, same goal, same name); put helper lemmas ABOVE it as `private lemma`. Reformatting the statement gets the attempt rejected before compiling.
- [tags: factorial, power, decide, numeral, big] `decide` cannot evaluate large closed terms (n! for n ≥ 10, x^x, 2^64): it times out or hits maxRecDepth. Use `norm_num [Nat.factorial]` for concrete factorials/powers, or keep witnesses in factored form (2^12 * 3^6) and reason with `mul_pow`, `pow_mul`, `pow_add` on the exponents (Erdős #674 lesson).
- [tags: finset, exhaustive, decide, subset, partition, counterexample] For exhaustive finite checks over subsets of a small explicit Finset (2^11 cases) use `decide +kernel`, not `decide` or `native_decide` (banned); state the check as `∀ B ⊆ A, ...` on a concrete `A : Finset ℕ` and raise `set_option maxRecDepth 10000 in` if needed (Erdős #316 shape).
- [tags: fin, vector, matrix, sum, prod, tuple] Witness functions `Fin k → ℤ` are easiest as `![a, b]`; unfold with `Fin.sum_univ_two`, `Fin.prod_univ_two`, `Fin.forall_fin_two`, and `Matrix.cons_val_zero`, `Matrix.cons_val_one`, `Matrix.head_cons` (needs `Mathlib.Data.Fin.VecNotation`) (Erdős #493 lesson).
- [tags: infinite, infinitely, family, set] To prove `S.Infinite` from an explicit infinite family, use `Set.infinite_of_injective_forall_mem (f := fun n => ...)` with an injectivity proof (often `StrictMono.injective` or `omega`/`nlinarith` on the parameter), or `Set.infinite_of_not_bddAbove`.
- [tags: subtraction, nat, truncated, integer] Natural-number subtraction truncates: encode statements with `-` over ℤ, or add the hypothesis `b ≤ a` before using `a - b` in ℕ; `omega` understands truncated subtraction, `ring` does not.
- [tags: cast, rational, real, division, binomial, ratio] Ratios of naturals: move to ℚ/ℝ with `push_cast`/`exact_mod_cast`, clear denominators with `field_simp` (needs nonzero facts, e.g. `Nat.centralBinom_ne_zero`, `positivity`), finish with `ring`/`nlinarith`.
- [tags: unknown, identifier, lemma, name] A compiler `unknown identifier` means the name does not exist as written: use the `-- CHECK:` directive or the DECLARATION CHECK block instead of guessing a variant; `sum_*` names are usually `to_additive` twins of `prod_*` lemmas with the same argument shape.
- [tags: colouring, coloring, bool, ramsey, monochromatic] Encode a 2-colouring as `c : ℕ → Bool` (or `Fin 2`) and monochromatic as equalities `c x = c y`; case-split with `cases h : c n` and close finite case analyses with `simp_all`/`omega`; unbounded arguments usually need an explicit `∀ n ≥ N` lemma proved by induction.
- [tags: sidon, arithmetic, progression, divides, dvd] Membership of an AP term in a factorial-based set: choose the index so the factorial is divisible by the difference (`Nat.dvd_factorial`), then close with `Nat.dvd_add_right`/`Nat.dvd_sub'`; use `Nat.factorial_lt`, `Nat.self_le_factorial` for growth/injectivity.

- [tags: colouring, bool, symmetry, wlog] For 2-colouring proofs with a colour-swap symmetry, prove one `private lemma key (c) (H …) (hc1 : c 1 = true) : False`, then for the other case apply it to `fun n => !c n`, transporting hypotheses with `Bool.not_inj` and closing `(!c 1) = true` by `simp [hc1]`.  <!-- from 20260907-193935-erdos645 -->

- [tags: omega, subst, hypothesis, arithmetic, colouring] When a hypothesis mentions `x + d`, `x + 2*d`, restate it as a lemma with extra variables `a b` and equations `ha : a = x + d`, `hb : b = x + 2*d` (proved by `subst ha hb`); then instantiate at awkward terms like `2*n - 1` with `(by omega)` side goals instead of rewriting.  <!-- from 20260907-193935-erdos645 -->

- [tags: bool, cases, induction, colouring] Case-split a Bool value with `cases h : c n with | true => … | false => …`, close monochromatic contradictions via `h1.trans h2.symm`, and prove `∀ j, c (n₀ + 2*j) = true` by `induction j` with `rw [show n₀ + 2*(j+1) = n₀ + 2*j + 2 by omega]` before applying the step lemma.  <!-- from 20260907-193935-erdos645 -->

- [tags: infinite, finset, sup, bounded, set] Alternative to an injective family for `Set.Infinite S`: `intro hfin`, `set N := hfin.toFinset.sup (fun p => p.1.sup id)`, exhibit a member whose entry exceeds N, then derive `≤ N` via `Finset.le_sup (f := …) (hfin.mem_toFinset.mpr hmem)` and `N+2 ≤ … .sup id` via `Finset.le_sup (f := id) (Finset.mem_insert_self _ _)`; close with `omega`.  <!-- from 20260907-194946-erdos397 -->

- [tags: centralbinom, binomial, recurrence, cancel, calc] For `Nat.centralBinom` identities use `Nat.succ_mul_centralBinom_succ n : (n+1) * centralBinom (n+1) = 2*(2n+1) * centralBinom n`; cancel a common positive factor with `apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < K)` and chain `calc` steps alternating `by ring` (regroup) and `by rw [h]` (apply recurrence).  <!-- from 20260907-194946-erdos397 -->

- [tags: finset, prod, insert, disjoint, explicit] Products over explicit `({a, b, c} : Finset ℕ)`: pre-prove `a ∉ ({b, c} : Finset ℕ)` by `simp only [Finset.mem_insert, Finset.mem_singleton]; omega`, then `rw [Finset.prod_insert h1, Finset.prod_insert h2, Finset.prod_singleton]`; prove disjointness via `rw [Finset.disjoint_left]; intro x hx hx'` + the same simp/omega.  <!-- from 20260907-194946-erdos397 -->

- [tags: finset, singleton, subset, colouring, witness] For a degenerate witness `A = {a}` where the goal quantifies over `B ⊆ A`, rewrite with `Finset.subset_singleton_iff` (gives `B = ∅ ∨ B = {a}`), then `rcases hB with rfl | rfl`; kill the empty case via `absurd rfl hne.ne_empty` and finish with `Finset.sum_singleton`/`Finset.prod_singleton`.  <!-- from sub-0 -->

- [tags: exists, refine, finset, card, witness] Supply all existential witnesses at once with `refine ⟨{1}, ?_, ?_, c 1, ?_⟩` then close side goals separately: `Finset.card_singleton` + `exact hk` for cardinality bounds, and `rw [Finset.mem_singleton] at ha; omega` for pointwise positivity; this pattern compiles first try for trivial small-k cases.  <!-- from sub-0 -->

- [tags: fin, colouring, degenerate, interval_cases] When a colour type is `Fin r` with `hr : r ≤ 1`, `interval_cases r` splits into `r = 0` (close by `exact Fin.elim0 (c 0)`, since any `c : ℕ → Fin 0` is absurd) and `r = 1` (every equality in `Fin 1` closes by `Subsingleton.elim _ _`).  <!-- from sub-1 -->

- [tags: finset, icc, card, omega] For a witness set of size ≥ k with positive elements use `Finset.Icc 1 k`: `rw [Nat.card_Icc]; omega` gives `k ≤ card` (card is `k + 1 - 1`), and `rw [Finset.mem_Icc] at ha; omega` gives `0 < a` for members.  <!-- from sub-1 -->

- [tags: colouring, fin, cast, monotone] To transfer a Ramsey-type statement from `Fin r` colours down to `Fin r'` (r' ≤ r), apply the hypothesis to `fun n => Fin.castLE h (c n)` and recover equalities in `Fin r'` with `Fin.castLE_injective h (h1.trans h2.symm)`; `Fin.castLE`/`Fin.castLE_injective` exist in Mathlib.  <!-- from sub-2 -->

- [tags: colouring, witness, finset, existential] When the obtained colour `i` lives in the wrong type, don't try to pull it back: pick the colour of a concrete member (`c a` for `a ∈ A`) as the new witness and compare via the singleton instance `hi {a} (Finset.singleton_subset_iff.mpr ha) (Finset.singleton_nonempty a)` after `rw [Finset.sum_singleton, Finset.prod_singleton]`.  <!-- from sub-2 -->

- [tags: finset, nonempty, empty, case-split] Split `rcases A.eq_empty_or_nonempty with hAe | ⟨a, ha⟩` when you need an element of `A`; in the empty branch, any `B ⊆ A` with `B.Nonempty` is absurd via `exact absurd hAe (hBne.mono hB).ne_empty`, so a dummy witness like `c 0` closes the goal.  <!-- from sub-2 -->

- [tags: finset, image, injective, sum, prod] To transport sums/products along an injective relabelling use witness `A = S.image f`; `Finset.card_image_of_injective _ hf`, and rewrite `∑ x ∈ B.image f, x` via `Finset.sum_image (fun x _ y _ hxy => hf hxy)` (same shape for `Finset.prod_image`).  <!-- from sub-3 -->

- [tags: finset, subset, image, preimage, filter] Given `B ⊆ S.image f`, recover a preimage as `B' := S.filter (fun j => f j ∈ B)`; prove `B'.image f = B` by `ext x; constructor` with `Finset.mem_image`/`Finset.mem_filter`, then `rw [← himg]` to pull hypotheses about `B'` over to `B`.  <!-- from sub-3 -->

- [tags: finset, set, rw, definitional] After `set B' := … with hB'`, unfold membership in the local definition with `rw [hB', Finset.mem_filter] at hj` rather than `simp`; `Finset.filter_subset _ _` gives `B' ⊆ S` directly, and `B.Nonempty` transfers through `mem_image` by `obtain ⟨j, hj, _⟩`.  <!-- from sub-3 -->

- [tags: colouring, decide, generalize, fin, finite] To finish a small colouring contradiction over `Fin 2` values, `revert` the inequalities, `generalize c 5 = a` (one per relevant point), `revert a b …`, then `decide`; this turns concrete `c n` terms into bounded variables that `decide` can exhaust.  <!-- from sub-4 -->

- [tags: existential, by_contra, push_neg, colouring, simpa] For `∃ x y, P ∧ … ∧ c a = c b`, use `by_contra h; push_neg at h` to get `∀ x y, … → c a ≠ c b`, then extract each needed pair with `have : c 6 ≠ c 5 := by simpa using h 1 5 (by norm_num) (by norm_num) (by norm_num)`; `simpa` normalises `1+5`, `1*5`.  <!-- from sub-4 -->
