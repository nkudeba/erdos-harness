# Findings about formal statements

Each entry is a Lean proof, verified and audited, that settles formal-conjectures' statement of an OPEN problem along a line its intent judges classified as a gap between the problem and its formalization, or as a known result. It is not a resolution of the problem as posed. A gap is worth reporting to formal-conjectures, and a known result to erdosproblems.com.

## #769 — known-result — 2026-10-14 23:52 UTC
- answer: false; statement: (a) For every odd n ≥ 253, gcd{aⁿ − 1 : 2 ≤ a ≤ L}=1 where L = ⌊n/4⌋+1. (b) Hence every k ≥ 1 + (2ⁿ−2)(Lⁿ−1) is admissible, and the cutoff c(n) (which exists and is unique) satisfies c(n) < (2L)ⁿ ≤ (n/2+2)ⁿ. (c) TSLowerBound is false: for all A, B > 0 and all N, there are an odd n ≥ N and a c with IsCutoff n c and B·c < A·nⁿ.
- source named by the judges: erdosproblems.com proof claims, both posted before this campaign's run and after the model's knowledge cutoff: Jeffrey Zeng (an OpenAI internal model; a sorry-free Lean formalization), 2026-07-24: for odd n, c(n) <= (S-1)(2^n-2)(S^n-1)+1 = o(n^n) with S = floor(sqrt(4n))+1, by the same subgroup and quadratic-nonresidue argument; Samuel Korsky (GPT-5.6 Pro), 2026-08-05: c(n) <= (C n^(1/(4 sqrt e)+eps))^n for odd n. The engine never saw either: its digest dropped the claims page (fixed 2026-10-14).
- Lean run: `runs/20261014-162417-471965-resolve-lean-erdos769`
- informal proof: `runs/20261010-025357-947738-erdos769` claim deep/C1
- summary: `RUN-SUMMARY problem=769 exit=0 outcome=proved directions=neg:proved verified=None spend=$6.85 llm_calls=23 lean_checks=109 lemmas=12 fatals=0 wall=204m mode=research dir=runs/20261014-162417-471965-resolve-lean-erdos769`
