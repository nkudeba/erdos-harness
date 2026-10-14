# Verified results awaiting human review

Each entry is a Lean proof of an OPEN problem's formal statement that passed the harness's verification and audit. The honesty rules require independent human review before any claim of resolution; until then `claimEligible` stays false.

Check two things first. Does the proof settle the problem as Erdős posed it, or only the formal statement's wording (a gap in the formalization)? And is the result already published? The prescreen's highest scores were mostly one or the other (REPORT 3.10: #655's regular n-gon, #32's Ruzsa 1998).

## #769 — 2026-10-14 23:48 UTC
- Lean run: `runs/20261014-162417-471965-resolve-lean-erdos769`
- informal proof: `runs/20261010-025357-947738-erdos769` claim deep/C1
- summary: `RUN-SUMMARY problem=769 exit=0 outcome=proved directions=neg:proved verified=None spend=$6.85 llm_calls=23 lean_checks=109 lemmas=12 fatals=0 wall=204m mode=research dir=runs/20261014-162417-471965-resolve-lean-erdos769`
- **Withdrawn 2026-10-14: a known result, not new mathematics.** erdosproblems.com proof claims, both posted before this campaign's run and after the model's knowledge cutoff: Jeffrey Zeng (an OpenAI internal model; a sorry-free Lean formalization), 2026-07-24: for odd n, c(n) <= (S-1)(2^n-2)(S^n-1)+1 = o(n^n) with S = floor(sqrt(4n))+1, by the same subgroup and quadratic-nonresidue argument; Samuel Korsky (GPT-5.6 Pro), 2026-08-05: c(n) <= (C n^(1/(4 sqrt e)+eps))^n for odd n. The engine never saw either: its digest dropped the claims page (fixed 2026-10-14). Moved to STATEMENT-FINDINGS.md.
