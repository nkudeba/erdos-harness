# BSD research campaign

This is an executable dependency and evidence ledger, not a proof of BSD or a claim of autonomous mathematical progress. The user-supplied *Validate a Math Solution.pdf* was reviewed, including the rank-two route on pages 6–11. Its SHA-256 and source location are recorded in `campaign.json`.

## Assessment and primary-source audit

The assessment's productive starting point is a restricted **CM analytic-rank-two** family. The missing analytic-rank-two → generalised-Kato-class-nonvanishing implication is separate from the known, hypothesis-dependent nonvanishing → Selmer-dimension-two theorem. Turning the latter into Mordell–Weil rank two still requires a rational rank lower bound or an appropriate result controlling the Sha contribution. These are separate unfinished nodes, not assumed facts.

[Castella, Theorem B](https://arxiv.org/html/2204.09608v3) refers explicitly to equation (1.5), Theorem A (i)–(ii), and the surrounding CM/prime/character setup. The campaign leaves the full hypothesis audit and formalization open. An abstract-level paraphrase is not a reusable theorem certificate.

[BKS](https://arxiv.org/html/1910.07404v2) studies a different derivative construction. Its Hypothesis 2.2 includes finiteness of the p-primary Sha group. Any use in the proposed route must track those assumptions and supply the comparison with generalised Kato classes. Neither is silently treated as solved.

[LMFDB 389.a1](https://www.lmfdb.org/EllipticCurve/Q/389/a/1) is a non-CM rank-two control. The coordinate fixture checks the proposed points against its equation only; it does not establish independence, analytic rank, or BSD. The CM family needs its own example. The initial discriminant and mod-5 fixtures concern the different curve y²=x³−x.

The installed Mathlib `EllipticCurve/LFunction.lean` defines an Euler product and L-series. A campaign must still establish the bridge to analytic continuation near s=1 before using an order of vanishing there. Numerical smallness, conjecturally computed Sha orders, and conditional rank calculations cannot discharge this obligation.

The general rank equality and full leading-coefficient formula remain separate roots. Even a successful restricted CM rank-two theorem would leave the general higher-rank and leading-term obligations open. See the [official BSD description](https://www.claymath.org/millennium/birch-and-swinnerton-dyer-conjecture/).

## Operation

From the repository root:

```sh
python3 harness.py campaign status --manifest campaigns/bsd/campaign.json
python3 harness.py campaign next --manifest campaigns/bsd/campaign.json
python3 harness.py campaign verify --manifest campaigns/bsd/campaign.json --node discriminant --candidate campaigns/bsd/fixtures/discriminant.lean
```

`verify` checks a supplied, assistant-authored fixture without a provider call. A model attempt uses `campaign run --node NODE --rounds 3 --backend claude-cli` with the same manifest. `next` ranks ready formal nodes by priority and downstream dependencies. Gaps must first receive reviewed exact formal contracts; they cannot run as vague prompts. A successful node unlocks its dependents. Repeating `run` resumes the most recent failed candidate and exact compiler feedback.

Record an external artifact with `campaign evidence --node NODE --candidate PATH --description TEXT`. This copies a content-addressed artifact into the campaign as **unverified evidence**, regardless of what the artifact says. There is no evidence-to-proof promotion shortcut.

## Verification and boundaries

* Contract, candidate, and audit compile as separate modules. The contract is elaborated before the candidate can introduce local notation or instances. The audit requires the exact `result` type, with implicit argument synthesis disabled at the application, and standard Lean axioms only.
* Certificates hash source and compiled artifacts, toolchain, package lock, verifier, harness, node specification, and dependency certificates. Changed input invalidates downstream work. This is a local reproducibility check, not authentication against a malicious workspace owner. Manifests and the installed standard libraries are trusted inputs; the candidate screen is not an operating-system sandbox.
* `formal_targets_verified` means the manifest's general formal roots passed these checks. It never means that a human statement was correctly formalized. `meaning_review` explicitly remains required. A conditional or special-case result cannot alone set general campaign completion.
* A file-locked ledger shares model-request counts, Lean-check counts, and reserved execution seconds across resumes and nodes. An interrupted reservation remains charged. These are invocation limits, not dollar limits; provider-internal retries are not separate model requests. Provider timeout behavior must be respected for the execution reservation to be a hard elapsed-time bound. The existing `program` command's budget behavior is unchanged.
* Prompt, response, failure, compiler feedback, and certificate artifacts are retained. A stale contract discards its repair checkpoint. Learned lemmas are reused only through fresh verified dependencies.

This adds persistent, checkable mathematical memory. It does not show an autonomous solve-rate improvement. The existing held-out learning gate should still require a completed before/after gain and saved-proof regressions before promoting general search changes. A successful infrastructure fixture is not a newly solved Erdős problem.
