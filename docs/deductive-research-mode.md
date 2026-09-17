# Deductive research mode — design note (2026-09-16)

Operator session, no paid run. This note answers one question: how to make the harness *derive*
mathematics on an open problem instead of sampling it, and how to make that derivation the thing
that accumulates. It is grounded in the current code (`run_program`, `PLAN_PROMPT`,
`EXPERIMENTS_PROMPT`, `stage_reduce`, `stage_decompose`, `campaign.py`) and in what actually moved
#273 and #699.

## 1. Diagnosis: where the loop is inductive today

`run_program` (harness.py ~4136) runs, per cycle: numerical experiments → a plan with a conjecture
ledger → 3–5 sub-statements → each attacked by a child `fast` pipeline → certified ones appended to
`Lemmas.lean` → retrospect. Four things make this inductive rather than deductive:

1. **Conjectures are fitted, not derived.** `PLAN_PROMPT` asks for statuses *supported / refuted /
   open*, so the model reports support as a percentage. On #699 cycle 2 the headline Conjecture D was
   adopted on "99.824% of pairs n ≤ 150; 99.92% on random n ≤ 4000" and refuted on continuation at
   (10,3,5). The 0.2% that failed was never analysed first, and it contained the whole obstruction
   (the witness prime is p = i and comes from a higher Lucas digit).
2. **Progress is counted in lemmas, so the loop optimises for easy lemmas.** The ledger reports
   `lemmas=10`; nine of the ten are library-grade stepping stones (`n ∣ j·C(n,j)`, monotonicity,
   the Erdős–Szekeres identity). None reduced the residual. The one artifact that did — "#699 ⇐
   ∀i U(i)", a conditional theorem isolating the hard core — was produced by the operator by hand.
3. **Reductions are checked, not proved, and then travel as fact.** `stage_reduce` runs a sandbox
   script that prints `REDUCTION-OK` on small cases and `reduction_context()` feeds the claim to
   search and proof prompts. The deductive version is a certified lemma `T ↔ T'`, after which `T'`
   can legitimately replace the working target. (#273's parity split did eventually become certified
   library lemmas — but by hand, after the run.)
4. **Decomposition anchors on the first failing attempt.** `stage_decompose` seeds the skeleton from
   "the best compiling-with-sorries prove attempt", i.e. from whatever the model tried first, not from
   a derivation of what must be true.

Search, escalation and construction are not the problem: they are correct as futility gates and as
decision procedures for finite cases. They just cannot produce a universal statement, and the Atlas's
reachability arithmetic already pins search-based resolution probability to 0 for 602 of 639 open
problems.

What *did* move the two problems the harness has spent the most on was derivation from the target's
structure, checked afterwards: the parity split (every modulus p−1 is even), the fibre/Fourier
condition (derived, validated on known covers, then applied), the smoothness reduction (Lucas ⇒ a
counterexample forces a j-smooth block), and the units-digit system U(3). Each is a *necessary
condition on a hypothetical counterexample*, obtained by asking what the structure forces.

## 2. Principle: every step is a theorem, and the residual is the artifact

Make the working object a **conditional theorem**, certified in Lean:

```lean
theorem erdos_699_of (hU : ∀ i, UnitsDigitSystemUnsat i) : erdos_699_target := by
  -- glue from Formal.Library.BinomialCoefficients
```

Each hypothesis is one of three kinds, and the kind is recorded:

- **published** — a named theorem from the literature stated as a hypothesis (Rosser–Schoenfeld,
  Lucas, the BBMST distortion bound). *Hypotheses, never `axiom`*: the axiom audit stays
  `[propext, Classical.choice, Quot.sound]`, and the trust boundary is visible in the signature.
  This is what Tang's #306 development does with axioms and what `campaign.py`'s `conditional`
  scope was designed for.
- **certified** — a lemma in the library; discharged, so it disappears from the signature.
- **conjecture** — the residual. This is the object whose size and shape measure progress.

Progress = the residual gets smaller or more elementary: fewer quantifier alternations, no longer
mentions the original objects (U(3) mentions no binomial coefficients), becomes decidable, or splits
into a finite check plus a tail. A cycle that certifies ten lemmas and leaves the residual unchanged
made no progress; a cycle that certifies one glue theorem and replaces the residual with a strictly
weaker statement did.

## 3. The loop

1. **Freeze** the target `T`; import the cluster library `L`.
2. **Backward step.** Ask for statements `S` such that `T ← S` is provable *now* by glue from `L`.
   Certify the glue immediately. `S` becomes the working target only if the residual metric says it is
   more elementary than `T`. (On #699 this was `sub10_1`, the "master glue", listed fifth of five
   sub-goals; it should be the first and only mandatory artifact of a cycle.)
3. **Refute first.** Before any proof budget goes to `S`, spend the cheap numerical budget trying to
   *refute* `S`: smallest cases first, then the recorded near-miss families (the nine strict-variant
   failures on #699, the tight-slack candidates on #273). A counterexample is banked as a certified
   negative lemma (`theorem not_S : ¬ S := ⟨witness, by decide⟩`) and the witness drives the
   refinement of `S`. "Holds on 99.8% of cases" is not a status; the statuses are *proved*, *refuted
   (witness)*, *conditional on [list]*, *open (refutation attempts logged)*.
4. **Forward step.** From `L` and Mathlib, derive what a hypothetical counterexample must satisfy,
   certify each necessary condition, and add it to the counterexample's hypothesis list. This is the
   mode that produced everything of value on #699 (prime-free window → smooth block → U(i)) and it
   is currently done by hand.
5. **Certify reductions.** `stage_reduce` emits a Lean statement next to the sandbox check. Verdicts
   become *refuted / checked / certified*. Only a **certified** reduction rewrites the working target;
   a checked one is carried as a hypothesis of the conditional theorem, so it can never silently
   become fact.
6. **Define.** Allow a cycle to propose a *definition* that makes the residual statable (`U(i)`,
   `CongruenceFamily`), with lemmas connecting it to the target in both directions. New definitions
   are first-class library entries, tagged by cluster.
7. **Remember the argument, not just the lemmas.** `campaign.py` already has the right shape: nodes
   are statements with scope, edges are "used in the proof of", experiments and literature can only
   be `evidence_for` and never dependencies, contracts are compiled in a module that never imported
   the candidate, and `next()` prioritises by unlocked descendants. It is standalone today (one BSD
   example, `tests/test_campaign.py`). Bind each research program to a manifest so the DAG *is* the
   plan, and `PLAN.md` becomes a rendering of it.
8. **Report the residual.** Replace `lemmas=N` in the ledger and summary line with the current
   conditional theorem, its hypothesis list by kind, and the residual metric. The Atlas partial axis
   reads "residual shrank from A to B", not "N lemmas".

## 4. Concrete changes, by location

| where | change |
|---|---|
| `PLAN_PROMPT` (harness.py ~1417) | Mandatory first block: a conditional theorem `erdos_{pid}_of_<k>` with explicit named hypotheses, provable now from `Lemmas.lean`. For every conjecture: its *derivation* (why it should follow) or its *use* (what it yields), plus the smallest-failing-case result. Forbid percentage support as a status. |
| `EXPERIMENTS_PROMPT` (~1395) | Two roles only: (a) refutation of each plan statement, printing `MIN-WITNESS` or `MIN-CLEAR n`; (b) necessary-condition extraction for hypothetical counterexamples (invariants that hold on every near-miss). No "support" runs. |
| `run_program` (~4136) | Each cycle: certify the conditional theorem first; sub-statement attempts only on hypotheses of the *current* conditional theorem; a `refute` step (the search stage run on the lemma, not the problem) before `prove`; write `RESIDUAL.md`; replace the working target when a certified reduction or glue theorem allows it. |
| `stage_reduce` / `REDUCE_PROMPT` (~1177, ~3403) | Add a `lean` field: the reduction as `theorem reduction_Rk : T ↔ T'` (or counterexample-implies form). Attempt certification in a child run. Verdicts *refuted / checked / certified*; only certified rewrites the target. |
| `stage_decompose` (~2863) | When a program exists, seed the skeleton from the conditional theorem and DAG, not from the best failing attempt. |
| `campaign.py` | Add `kind: conjecture` (formal type, no proof, `refutation` evidence pointer) and a `residual()` report; add `harness.py run --campaign <manifest>` binding a program to a DAG. |
| `knowledge/refuted/<n>/` | Certified-false statements with witnesses, fed into `PLAN_PROMPT` as "do not re-propose". Today the Conjecture D refutation lives in prose and one library lemma (`residue_route_fails`); make that the rule. |
| literature stage | Published theorems become named hypotheses with a provenance ledger (paper, theorem number, statement hash), available to the backward step. Never `axiom`. |
| `record_finding.py` | `--residual` to record the hypothesis list; the partial axis tracks its shrinkage. |
| `SUMMARY.line` | Add `residual=<k hypotheses: p published, c conjectures>` beside `lemmas=`. |

## 5. What does not change

- The honesty gates: frozen statement, sorry/banned-construct screens, standard-axiom audit,
  `claimEligible=false` until human review, assistance recorded.
- Search floors as futility gates and SAT as the decision procedure for finite cases.
- Cluster libraries as the accumulation mechanism; they gain definitions and negative lemmas.
- One lane at a time; `--run-budget` as a real cap.

## 6. Acceptance test

The loop is deductive when, on #699 and with no operator notes beyond the frozen statement, it
re-derives *in Lean, on its own* the chain the operator produced by hand:

counterexample ⇒ every n−t (t < i) is j-smooth ⇒ the units-digit system U(i) ⇒ for i = 3: n odd is
impossible, 4 | n, j < n/2, A′² < 4.5h + 2.25,

ending the run with a certified `erdos_699_of (hU : ∀ i, U i) : erdos_699` and a residual report
naming `U` as the single open hypothesis. Every step in that chain is elementary; none of it is
search. If the harness cannot reproduce it, the loop is still inductive whatever the lemma count says.

Cost profile: spend moves from search scripts to proof glue. Conditional theorems are cheap to
certify, refutation searches are cheap, and expensive proof attempts happen only on hypotheses that
survived refutation and sit on the path to the target.

## 7. Implementation status (2026-09-16)

Implemented in `harness.py` (`run_program` dispatches on `--research-loop`, default `deductive`):

- `EXPERIMENTS_PROMPT` is refute-first (`REFUTED:` / `CLEAR:` / `INVARIANT:`; percentages banned);
  `PLAN_PROMPT` demands a residual skeleton plus a JSON hypothesis ledger; the legacy prompts survive as
  `*_LEMMA` for `--research-loop lemma`.
- Residual machinery: `split_decls`, `parse_residual`, `residual_improves`, `hypothesis_substatement`,
  `splice_hypothesis`, `parse_refutation_output`, `record_refutation` / `load_refutations` /
  `refuted_context` / `statement_refuted` (`knowledge/refuted/<n>/`), `render_residual_md`,
  `residual_campaign_manifest`.
- Loop: `_deductive_experiments`, `_consider_skeleton`, `_attack_substatement`, `_write_residual`,
  `_run_program_deductive`. A closed skeleton is routed through `stage_verify`; a published premise left
  open keeps the run at `partial` (exit 3), never `proved`.
- Reductions: `REDUCE_PROMPT` takes a `lean` statement; `_certify_reduction_statement` marks it
  `stated` / `certified` / `ill-typed`; `reduction_context()` labels certified vs unproved.
- Reporting: `residual=` on the summary line, `residual` in `collect_run_facts` and the brief's facts,
  a line in `report.md`; `record_finding.py --residual`; `campaign.py` gained `conjecture` nodes,
  `conditional_on`, and the `residual` action.
- Flags: `--research-loop {deductive,lemma}`, `--refute {auto,off}`, `--hyps-per-cycle N`.

Not yet done: routing `campaign.verify` through the harness's child runs (the manifest is a rendering,
verification still goes through `_attack_substatement`); a Lean-certified negation for a numerical
refutation (recorded as `certified: false`); `stage_decompose` seeding from the residual for non-program
runs. `benchmarks/deductive/prepare.py --problem N --launch` runs the blind re-derivation of a saved solve with
`--benchmark` (no knowledge/solved write, no lemma harvest, no brief); `benchmarks/deductive/README.md`
classifies the 19 saved proofs (8 deductive, 4 construction, 7 certificate) and fixes the judging order.
The §6 acceptance test on #699 itself has not been run. The first solved-problem benchmark (#645, blind)
closed in one cycle for $4.75, but the child prompt had been fed the reference proof by the harness's own
lemma store, so it validates the mechanics only; see `benchmarks/deductive/RESULTS.md` and the masked mode.

### Benchmark note (2026-09-16, #645 blind run, cycle 1)

The first blind run adopted a skeleton whose glue certified the colour-flip normalisation and an 'anchor'
lemma (the progression a, 2a+1, 3a+2), and whose single open hypothesis was a compactness statement: some N
bounds every witness. The refutation script had already shown witness-free colourings of [1,45] exist, so
that hypothesis cannot be certified by kernel enumeration and is as hard as the target; the reference proof
is instead four elementary lemmas about propagation of colours. Under the original count-first
`residual_improves` the four-lemma skeleton would have been rejected as 'more hypotheses'. The rule now
compares the hardest open conjecture first (`max_complexity`), then the count. The metric remains a crude
size proxy; a skeleton whose one hypothesis is a restatement of the target is the failure mode to watch.

### Benchmark note (2026-09-16, masked #275 run, cycle 1)

With the identity masked and the lemma store excluded, the loop took its OWN route, not the reference's: a
strong induction on the number of classes with a three-way split on the parity structure of the moduli
(certified as glue), leaving the all-odd case as the open residual — the case the probe had predicted naive
inductions cannot close, and one the reference's roots-of-unity argument never splits on. Two defects
surfaced and were fixed: attack order used syntactic complexity, so the shortest statement (the hard
all-odd case) went first; and the per-child budget share was below the cost of one prove call. The order
now follows the plan's `difficulty` rating, and `--min-child-budget` defers hypotheses instead of starving
them.

Also fixed from the same run: the cap is now enforced before every model call and never right after one
(a paid response was being discarded uncompiled), and the residual report is written however the loop
ends. Result row: `benchmarks/deductive/RESULTS.md`.

## 8. Added 2026-09-17: the first-principles machinery

- **Proof-failure feedback** (`failure_digest`, `failures.jsonl`, PROOF FAILURES in the plan, four moves
  recorded in `moves.jsonl`): a failed child is analysed, not discarded; repeat failures sink in the attack
  order (`attack_order(hyps, failure_counts)`).
- **Depth** (`--residual-depth`, default 2): a hypothesis that failed once or is rated hard runs the deductive
  loop itself as a sub-residual in its own program directory (`program_subdir`, module suffix `Sub<hash>`), with
  the hypothesis as its frozen target (`parse_residual(..., main=)`); its partial skeleton splices back as a
  refinement (`hypothesis_refined`), so the parent's frontier becomes the child's simpler sub-hypotheses.
- **Derive first, check second**: `DERIVATION:` precedes `INVARIANT:`; `OBSERVED:` marks undirected patterns;
  `parse_refutation_output` pairs them.
- **Definitions driven by failure**: the `define` move in the plan prompt, recorded and rendered.
- **Ratings survive**: a plan's ratings for hypotheses already in force are merged even when its skeleton is not
  adopted.
- **Prover calibration**: the masked #275 rerun at ~$15 with these features is the test; see RESULTS.md.

### Benchmark note (2026-09-17, funded masked #275 rerun with failure feedback and depth)

The calibration question — do elementary hypotheses discharge when funded? — is answered yes: `hyp_odd_all`
(elementary) proved for $3.45 and `hyp_step` (moderate) proved in its first round for $4.53. The second was
invisible to the run: `contains_frozen` required the frozen defs and theorem as one contiguous block and rejected
all three attempts unread for placing a helper between them. The same guard rejected the all-odd sub-residual's
skeleton before it could reach the compiler (where it would have failed honestly on `le_or_lt`). Fixes: per-
declaration frozen matching; rejected attempts keep their code and name the missing declaration; the per-call
budget is capped at what the run has left; a rejected skeleton is a `skeleton` failure fed to the next plan.
The two discarded proofs were recovered after the run with the harness's own checks and spliced, so the
program's residual is `open:1` (the all-odd core); the run's own summary line still says `open:2`, as it should.
The four failure moves worked as designed on this run: `define` introduced `Cov`/`Good`, `split` dissolved the
two parity cases into one descent lemma plus an elementary fact, `defer` kept the hard core.
