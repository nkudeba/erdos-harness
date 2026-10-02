# Time-split benchmark: resolved problems the model has never seen resolved

The harness is meant to attack open problems. Every earlier benchmark re-derived a problem the model might
remember, and the saved-solve pool is used up (`docs/HANDOVER-2026-09-23.md`). Two cases give ground truth
without that problem:

- a problem whose resolution **first appeared after the model's training data**; or
- an older resolution that the model, **asked directly, does not know**.

To the model either one is an open problem, but we know the answer. Any self-improvement loop should measure
itself here: a change to the harness counts only if it solves more of these.

## What an item is

An Erdős problem resolved on or after `--since` (default 2026-01-01) with a yes/no answer. Each item carries:

- **`statement_en`**: the question as the site poses it (from `atlas-data/parsed.json`, else the live page). The
  site's resolution notes never enter a problem file.
- **The frozen Lean statement P**: the question's YES reading. It is the main theorem of formal-conjectures'
  `ErdosProblems/<n>.lean` at a pinned commit, with `answer(True|False)` stripped. Every docstring and comment is
  removed (they state the resolution), and every identifier carrying the problem number is renamed:
  `Erdos884Prop` becomes `TSProp`.
- **`answer`**: the truth of P. It comes from `answer(...)`, or from the file's `research solved` category for a
  plain assertion. Where formal-conjectures has not recorded it, it comes from the teorth informal state.
- **`first_public`**: the earliest public appearance of the resolution found in the sources, with its evidence:
  - the site's record date;
  - the v1 date of each arXiv paper cited with the resolution;
  - an older citation year (the problem was already solved in the literature);
  - the AI-contributions wiki's dates.

  The site's date alone is not enough: #387 was recorded in July 2026, but its disproof is arXiv 2605.21221, a
  May preprint.
- **`probe`**: the model's own answer, before any run, to "is this open or resolved, which way, and how?"

Items are excluded, each with a stated reason, when:

- the answer is a value rather than yes or no;
- the formal-conjectures file has parts but no main theorem;
- the sources disagree on the answer;
- the site calls the resolution trivial (#280 and #1193 taught that a trivial recorded answer is no test);
- the frozen statement does not compile;
- the faithfulness judge rejects the statement;
- the probe shows recall.

## Splits

| split | rule | used for |
|---|---|---|
| `test` | `first_public` on or after the model's cutoff (Opus 5.5: 2026-07-01), and the probe shows no recall | reporting only; **never** used to accept or reject a change |
| `dev` | earlier resolution, the probe shows no recall, and the problem number hashes to dev | the acceptance gate |
| `train` | the same, hashing to train | what a change proposer may read: transcripts, failures |
| `unprobed` | earlier resolution, not probed yet | nothing, until `probe` runs |

Dev and train are fixed by the problem number alone, so the assignment survives rebuilds and pool growth. New
resolutions after the cutoff join `test` automatically on the next `build`.

**The probe is the contamination rule for everything before the cutoff.** Its verdicts:

- `recalled`: says resolved and gives the right answer. Excluded.
- `partial-recall`: knows it was resolved and names a source, without the answer. Excluded, because a long run
  can turn half a memory into the route.
- `misremembered`: says resolved but gives the wrong answer. Kept.
- `unaware`: kept.

A probe cannot prove absence of memory. It records what the model says when asked directly, with the full
identity as the strongest cue.

## Protocol for one item

`run` executes a fixed protocol, one lane, one item at a time, refusing to start while another
`harness.py run` is live:

- `--open`: both directions, so the answer is never given.
- The deductive research loop.
- `--masked`: "Erdős" and the site's domain are scrubbed from prompts. Tags are kept, so cluster libraries still
  load; they are part of the harness's capability.
- `--benchmark`: nothing is written to `knowledge/`.
- No web. The model-memory literature stage stays on by default, which is safe only because the probe screened
  the resolution.
- A fixed `--budget` per item (default $8, both directions together).

**Every evaluation uses a fresh synthetic id**, because `programs/erdos_<id>/` is keyed by id. A reused id would
resume the last evaluation's residual and lemmas. The harness also reads `atlas-data/reviewed.json` and
`research-guidance/<id>.md` by id, so the true number must never be the run's id. The problem file lives inside
the run directory.

Each result line in `results/<tag>.jsonl` records the protocol: git commit and dirty flag, SHA of
`harness.py`, SHA of the playbook, model, budget and flags. The default tag is `<date>-<commit>-<config hash>`.

## Scoring

- **Primary: `solved`.** The true direction closed and passed every mechanical gate (compiles, sorry-free,
  frozen match, standard axioms, no banned construct).
- **Never a solve: `contradiction`.** A verified proof of the *wrong* direction means the frozen statement or
  the recorded answer is wrong. Re-audit the item.
- **Dense: `pieces`**, the number of certified steps of the true direction's proof. It is measured on the final
  residual by `progress` (Lean only, no model calls, 1-2 minutes per run), and a hypothesis counts only if it is:
  - **closed**: nothing beneath it is open. A refinement whose sub-hypotheses are still open has no hole of its
    own, so the harness's `certified` counts it; `pieces` does not.
  - **used**: the frozen theorem's proof reaches it. A lemma an earlier plan certified, which the re-planned glue
    no longer calls, does not count. Baseline #419 had 3 of its 4 certified hypotheses in that state.
  - **non-trivial**: the free cascade does not prove it on its own, with the skeleton's definitions and `open`s in
    scope and all of Mathlib imported. The cascade is the harness's own plus `exact?`, and each alternative must
    close the goal. Full Mathlib, not the problem file's imports, because a run's header grows as the harness adds
    modules for unknown identifiers, and a lemma anywhere in Mathlib is free.
  - **maximal**: not beneath another closed hypothesis. A step proved through three certified sub-lemmas is one
    piece, the same as a step proved in one go, so the prover's internal structure cannot change the score.

  Reported beside it:
  - `certified_size`: non-whitespace characters, outside comments, of everything the pieces rest on (their
    proofs, helpers and sub-hypotheses), with the problem's own definitions counted as zero;
  - `closed_lemmas`: closed, used and non-trivial, at any depth;
  - `trivial` and `unused_closed`;
  - `open_conjectures` and `open_published`;
  - `harness_certified`, the harness's own count.

  **Known biases, and why an item needs both measures.** `pieces` depends on how the PLAN chunks the argument: a
  plan that states two steps where another states one gets two pieces for the same mathematics. `certified_size`
  depends on how verbose the proofs are. Each can move without the other, so the paired call below needs both.
  Neither measure says how close a problem is to resolution, and both ignore what is left open: two runs with the
  same open hypothesis can differ in `pieces` by how finely they certified the rest.

  Each run is measured when it finishes, and both directions' residuals are snapshotted to
  `results/residuals/<tag>/`, because a later resume of the run directory (a top-up) rewrites its program in place.
  Measurements are appended to `results/<tag>.progress.jsonl`, and the result lines are never rewritten.
- **Other dense signals:**
  - `true_certified`: the harness's own count, which the guards above correct;
  - `false_stopped`: the false direction's plan called its target false;
  - `true_abandoned`: the true direction's plan did.
- **Aggregates:** solve rate with a Jeffreys 90% interval, spend and $ per solve, total `pieces`.
- **Paired comparison with `--baseline`:**
  - exact McNemar on the discordant solves;
  - the dense comparison, item by item (`dense_outcome`). A solve outranks any partial result. Between two unsolved
    runs, a **win needs more `pieces` AND a larger `certified_size`**, a loss needs fewer of both, and anything else
    is a tie. It reports wins, losses, ties and a one-sided exact sign test, together with the naive `pieces`-only
    calls and the deltas, so a verdict that rests on chunking alone is visible.

## How a gate should read it

Solves are the verdict. At $8 per item they are too rare to steer by: three arms and 20 dev runs produced none.
So each iteration is gated on the dense key, and solves remain the final check.

**One baseline draw is not a baseline (2026-10-02).** On the 5-item dev screen, two draws of the same baseline harness
scored 10 and 4 pieces. The second draw lost to the first 0-3-2, the same score a candidate got against it.
- Screen against at least two baseline draws per item.
- Read a candidate against the range of those draws, never against one of them.
- Treat a 5-item screen as a check for breakage, not a verdict. RESULTS.md, "Baseline replicate", has the numbers.

A candidate change is kept when, paired item by item against the baseline on `dev` under the same protocol:

1. the saved-proof regression still passes;
2. it loses no solve the baseline had and produces no contradiction;
3. either it solves strictly more (McNemar p < 0.1 if it trades some), or the dense comparison favours it with a
   one-sided sign test p ≤ 0.05. With 18 items that means, for example, at least 7 wins against 1 loss, or 5 against
   0.

A kept candidate becomes the baseline for the next iteration. The solve count on `test`, which is never selected
on, is the final check and is reported with each kept candidate. If candidates keep passing on `pieces` and never
convert pieces into solves, the metric is being fed by plan shape rather than by proof; read `closed_lemmas` and
`open_conjectures` alongside it.

Both arms must have run the same items. The comparison leaves out any pair missing a measurement, and prints them.

**Quarantine what is learned.** Lessons, lemmas and library entries may be harvested from **train** runs only.
Anything learned from a dev or test run carries that item's solution into every later evaluation of it. The same
goes for the change proposer: it may read train transcripts and failures, never dev or test ones. `--benchmark`
already keeps runs from writing `knowledge/`; this rule covers what a loop does with their output. `pieces` is
an aggregate count, so gating on it reads no dev transcript.

Evaluation is the expensive part: about $8 per item. Screen a candidate change on a fixed small subset first,
then run the rest of dev only if it does not lose.

## Commands

```bash
python3 benchmarks/timesplit/timesplit.py build              # sources cached under cache/ (gitignored); no model calls
python3 benchmarks/timesplit/timesplit.py freeze --unprobed  # batched, nice'd compile check before any spend
python3 benchmarks/timesplit/timesplit.py probe --max-spend 10
python3 benchmarks/timesplit/timesplit.py judge              # back-translation + open-problem judge, kept items only
python3 benchmarks/timesplit/timesplit.py status
python3 benchmarks/timesplit/timesplit.py run --split dev --budget 8 --detach
python3 benchmarks/timesplit/timesplit.py progress --tag <tag>             # runs finished before it existed
python3 benchmarks/timesplit/timesplit.py score --tag <tag> --baseline <tag>
python3 benchmarks/timesplit/timesplit.py ideas --tag <tag> [--baseline <tag>]  # idea hits, train items only
python3 benchmarks/timesplit/timesplit.py calibrate --tag <tag> --rounds 3    # discovery's first round vs the truth
python3 benchmarks/timesplit/timesplit.py run --split train --candidate v3 ...  # the harness's discovery options
```

## Idea hits (train only)

`pieces` cannot see an idea that has not been formalised yet. For train items, `ideas/<n>.md` states the key idea
of the published resolution, what counts as a hit, and what counts as a partial hit. The notes were written from
the published record by an agent that read nothing of the harness's runs. `ideas` sends a blind judge the run's
notes and the reference, and records hit, partial or miss with the quoted evidence. The run's notes are its
exploration notebooks, informal attempts, computations, plan notes and final hypotheses. The metric screens changes
to the idea stages cheaply: no Lean, about $0.10-0.30 a run. Dev and test have no notes, because their solutions
must not inform harness design. An item whose route is unknown is not graded.

## Candidates

- `baseline`: the protocol above.
- `discover-v1` and `discover-v2`: informal attempts before the harness; see RESULTS.md.
- `v3`: no external discovery. The harness runs its own discovery options (`V3_FLAGS` in `timesplit.py`):
  - exploration in a Python sandbox, and exploration of the core after a stall;
  - empirical conjectures;
  - two routes per cycle with a route judge;
  - core-first attack;
  - high-effort plans;
  - the wide literature memo;
  - two-cycle sub-residuals.

  Its protocol records the flags (`harness_flags`). It needs a pin taken after 2026-09-24, since older pins lack
  the options, and a baseline on the same pin before any gain can be attributed.

## The pool as built on 2026-09-24

Built at formal-conjectures `077138338750` for `claude-opus-5-5`, with no harness runs. Model spend was $4.49:
$2.58 on 96 probes and $1.91 on 42 judge verdicts.

Of 225 problems the site records as resolved since 2026-01-01, 35 are usable: **test 2, dev 18, train 15**.
The 190 exclusions, each with its reason in `pool.json` (`status` prints them):

| count | reason |
|---|---|
| 61 | the frozen statement does not compile against our Mathlib (v4.32.0-rc1) |
| 54 | the probe shows recall (53 recalled, 1 partial) |
| 37 | no formal-conjectures file |
| 19 | multi-part problems with no main theorem |
| 8 | already solved by this harness (their proofs are in `knowledge/solved/`) |
| 7 | the judge rejects the frozen statement |
| 4 | other: 2 value questions, 1 trivial, 1 where the sources disagree |

The compile count is after all three repairs: added imports, 16 formal-conjectures definitions inlined, and
classical decidability. 6 kept items use inlined definitions; 4 use classical decidability. The judge's
rejections were reversed polarity, a narrowed domain, a different function, a weaker "infinitely often" form,
and an estimate replaced by the existence of a limit.

What the numbers say:

- **The stated cutoff protects little of 2026.** 35 of the 53 recalled problems were resolved in 2026 itself. For
  anything before the cutoff, the probe is the rule.
- **`test` is tiny: #193 and #547.** Only 9 problems were resolved after 1 July at all, and it grows only as the
  site does. Report `test`, but gate on `dev`.
- **The answer is easy to guess.** Kept items are 25 yes and 10 no, and the model's pre-run guess of the answer
  is right 26 times out of 31. Calling the direction is a weak signal; only `solved` means anything.
- **Composition:** 18 number theory, 6 graph theory. 23 were resolved in 2026; 12 are older results the model does
  not connect to the problem.

## Caveats

- **The agentic prover's reads are bounded by instruction, not by permission.** It runs in
  `run_dir/sandbox/<name>` with unrestricted `Read`/`Grep`/`Glob`, and its `TASK.md` asks it not to read reference
  material. Time-split runs write no `MASK.json` next to the sandbox; the alias map goes to
  `results/<tag>.aliases.jsonl`. But `pool.json` holds the answers inside the repo. Until the harness enforces the
  boundary, treat a solve whose transcript shows reads outside the sandbox as void.

- A stated knowledge cutoff is fuzzy. Opus 5.5's is June 2026, yet it did not know #90's May 2026 disproof. The
  date defines `test`; the probe governs everything else.
- The resolutions skew toward what was solvable in 2026, much of it elementary and found by AI. A rate here says
  how often the harness finds such steps. It is not a base rate for the problems still open (645 of them, which
  survived the same sweeps).
- The frozen statement is formal-conjectures' reading of the question, not the harness's own. Formalizing an
  open problem is a separate skill, and this benchmark holds it fixed on purpose.
