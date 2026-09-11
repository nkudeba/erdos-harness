# Solution review milestones

Every state save derives `solution_review`; normal reports and completion records expose it. Open-mode parents retain each direction's review under `open_reviews`. Existing `all_clear`, outcome `proved`, and exit 0 retain their narrow pipeline meaning for benchmark compatibility: they do NOT authorize a mathematical discovery claim. Consumers must use `resolution_claim_eligible` for that purpose. Catalogue status is never automatically changed.

1. **candidate_solution**: a proof artifact exists, possibly unchecked.
2. **mechanically_verified**: the exact artifact passed compilation, frozen-statement, sorry, banned-feature and standard-axiom checks. Automated back-translation is tracked separately and cannot provide independent review.
3. **statement_independently_audited**: independent statement audit and clean-environment replay evidence are recorded.
4. **externally_reviewed**: adversarial-check evidence and a further external mathematical review are recorded. The external reviewer must differ from the statement auditor. A full resolution claim also requires automated faithfulness clearance and cannot be a program sublemma.

The digest binds the entire original problem record, formal statement, proof, direction, imports, Lean toolchain and dependency manifest/build configuration. Changes invalidate existing verification and review evidence. An interrupted re-verification clears the earlier verdict. Evidence files are content-hashed; deletion or alteration invalidates that attestation. Legacy success flags alone never populate the new verification milestone.

## Independent review procedure

Supply a readable proof and original references to reviewers. The statement audit must inspect all definitions, domains, quantifiers, exceptions, negation direction and every requested sub-question. The clean replay report must describe a fresh checkout, pinned dependencies, exact proof digest, commands, logs and complete axiom audit. Adversarial review should document boundary cases, searches, assumptions attacked, and their limits; absence of a counterexample is not a proof. External review should assess the mathematical argument, current problem formulation, scope and prior literature.

Record each completed review using:

```sh
python3 solution_review.py runs/RUN --kind statement_audit --reviewer 'Reviewer name' --evidence /absolute/path/review.md --attest-independent
```

Other kinds: `clean_replay`, `adversarial_checks`, `external_review`. Then resume harness verification to recompute milestones against the current artifacts. Use the direction child directory for open-mode proofs. Retain the evidence files at their recorded paths.

These are explicit operator attestations. The software checks linkage, content integrity and milestone prerequisites; it cannot authenticate a person's identity or judge whether a written review is competent or independent. Never let a proof-generating agent fabricate review evidence or invoke the attestation command to approve itself. No external reviews, clean replay, counterexample searches, or publication are automatically claimed or performed by this change.
