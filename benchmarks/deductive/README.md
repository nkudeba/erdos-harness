# Deductive benchmark — solved problems whose proofs are arguments, not certificates

The deductive research loop (`docs/deductive-research-mode.md`) claims to *derive* a route rather than sample
one. The honest way to test that claim is on problems whose answer is already certified in this repository
(`knowledge/solved/`, 19 proofs), **with the resolution notes withheld**: the run sees the English statement,
the tags and the frozen Lean statement, and nothing else. `prepare.py` builds that blind run; `--benchmark`
guarantees it never overwrites the saved proof, harvests no lemmas and writes no brief.

A benchmark is judged by `programs/erdos_<n>/RESIDUAL.md`, in this order:

1. **Closed** (exit 0): the skeleton has no hypothesis left and passes final verification. Compare
   `Residual.lean` with `knowledge/solved/Erdos<n>.lean` by eye: same route, or a different one.
2. **Reduced to the known hard step**: the open hypotheses are exactly the step the saved proof leans on
   (a published theorem such as Hindman's, a finite check), everything else discharged and spliced.
3. **Stalled**: the residual is the frozen target, or a skeleton whose hypotheses are as hard as the target.
   Certified stepping-stone lemmas do not count.

## Classification of the 19 saved proofs

Profiled from the saved Lean (`knowledge/solved/Erdos<n>.lean`) and the frozen statements. "Deductive" means
the certified object is an argument about all inputs; "certificate" means the content is a finite object the
kernel checks; "construction" means an explicit infinite family plus a proof that it works.

| # | frozen goal | saved proof | class | benchmark order |
|---|---|---|---|---|
| 645 | ∀ 2-colouring of ℕ, ∃ monochromatic x, x+d, x+2d with d > x | finite case analysis, 99 lines, omega | deductive (reduces to a finite statement) | 1 |
| 275 | a system covering 2^r consecutive integers covers ℤ | induction on r, 116 lines | deductive | 2 |
| 499 | doubly stochastic matrix has a permutation with product ≥ n^−n | inequality argument, 154 lines | deductive | 3 |
| 532 | ∀ 2-colouring, ∃ infinite A with monochromatic finite subset sums | Mathlib Hindman + block grouping, 115 lines | deductive, but the hard step is **certified in Mathlib** (`Mathlib.Combinatorics.Hindman`), not a premise: #532 *is* the 2-colour Hindman theorem, so a `-- PUBLISHED:` Hindman premise is circular and the guard rejects it. What remains to derive is the block grouping | 4 |
| 350 | dissociated A ⇒ Σ 1/n < 2 | 22 lemmas, 407 lines | deductive | 5 |
| 476 | Erdős–Heilbronn: \|A +̂ A\| ≥ min(2\|A\|−3, p) | structural, 315 lines | deductive | 6 |
| 649 | ¬ ∀ primes p q, ∃ n with P(n)=p, P(n+1)=q | a pair (p,q) and a Diophantine argument that no n exists | deductive, negative direction | 7 |
| 16 | U ≠ (arithmetic progression) ∪ (density-0 set) | argument, 289 lines | deductive, negative direction | 8 |
| 370 | infinitely many n with P(n)² < n and P(n+1)² < n+1 | family (6t+8)(6t+10) plus smoothness proof | construction + argument | 9 |
| 198 | ∃ Sidon set meeting every infinite AP | explicit construction plus argument | construction + argument | 10 |
| 280 | ∃ sparse sequence with o(k) uncovered residues | construction plus asymptotics | construction + argument | 11 |
| 1193 | ∃ A, g with positive lower density of {n : 1_A∗1_A(n) = g(n)} | construction plus density argument | construction + argument | 12 |
| 397 | infinitely many products of central binomials that coincide | infinite family from an identity | construction | — |
| 363 | infinitely many interval collections with square product | infinite family | construction | — |
| 105 | ∃ point configuration (n points, n−3 blockers) | 9 points, nlinarith checks | certificate | — |
| 316 | ∃ finite A with no good partition | 2^11 exhaustive check | certificate (computational) | — |
| 399 | ∃ n, x, y, k with n! = x^k ± y^k | witness | certificate | — |
| 674 | ∃ x, y, z > 1 with x^x y^y = z^z | Ko's witness in factored form | certificate | — |
| 493 | ∃ k, N, every n ≥ N is ∏a − Σa | k = 2 | certificate (trivial) | — |

The eight deductive cases are the test set. The four construction cases are a secondary set: a deductive
run should at least state the family as a hypothesis and discharge the "it works" argument. The certificate
cases are not deductive benchmarks; the search stage owns them.

## Running one

```bash
python3 benchmarks/deductive/prepare.py --problem 645 --launch
```

Defaults: `--run-budget 8` (too little for a three-hypothesis problem: budget ~$4 setup + ~$4 per hypothesis + ~$5 per
sub-residual, so ~$20; see RESULTS.md), two cycles, three hypotheses per cycle, `--model claude-opus-5-5` (the CLI default
model hits its usage limit early, see `CLAUDE.md`; runs before 2026-09-23 used `claude-opus-5`). One lane at a time; `prepare.py --launch` refuses to start
if a `harness.py run` is live. Results land in `runs/<ts>-bench-erdos<n>/` and `programs/erdos_<n>/`; the
`RUN-SUMMARY` line carries `residual=open:k,published:p,certified:c`.

Record the outcome with `python3 atlas-data/record_finding.py --problem <n> --residual '<json>' ...` only
for open problems; benchmark outcomes on solved problems go in this directory's `RESULTS.md`, not the Atlas.

## Contamination, and the masked mode

The first #645 run closed along the reference route, and the transcript shows why that proved nothing about
derivation: the harness's own lemma store (`knowledge/lemmas.jsonl`, harvested from every verified proof)
matched on keywords and injected the reference proof's lemmas into the child's prove prompt. Two paths, two
answers:

- **Internal (closed).** `--benchmark` now excludes lemma-store fragments from every prompt. The playbook
  (generic tactic lessons) stays.
- **Model memory (cannot be closed, only reduced and measured).** `prepare.py --masked` builds a
  de-identified variant from `masks/<n>.json`: a synthetic problem id, a paraphrased statement with the
  attribution and the standard jargon removed, an alpha-renamed frozen theorem, no tags (so no cluster library
  and none of its `Erdos`-named declarations), and `--masked`, which scrubs the word Erdős and the site's domain
  from every outbound prompt including the agentic prover's. `probe.py` asks the model directly, before the
  run, whether it recognises the identified and the masked statement and what strategy it would try;
  `compare.py` measures the overlap between the produced proof and the reference. A masked run whose probe
  shows no recognition and whose proof takes a different route from the reference is the strongest evidence
  this setup can give; a run that reproduces the reference's distinctive machinery after a probe that recalled
  it is recall, whatever the exit code.

```bash
python3 benchmarks/deductive/probe.py --problem 275
python3 benchmarks/deductive/prepare.py --problem 275 --masked --launch
python3 benchmarks/deductive/compare.py --run runs/<ts>-bench-erdos80317 --reference knowledge/solved/Erdos275.lean
```

## Caveats

- Blind is harder than the original runs, which had the site's resolution notes; a stall here does not mean
  the original solve was lucky, and a close does not mean the loop would close an open problem.
- A mask is only alpha-renaming and paraphrase; the mathematics is the same, and a model that knows the theorem
  by its content rather than its name will still recognise it. The probe records whether it does.
- Every number in a benchmark report is an observation about this harness on a chosen problem, never a
  probability. Nineteen reference proofs were selected for being reconstructable; do not read a success rate
  on them as a base rate for open problems (`predict.py` deliberately refuses to).
