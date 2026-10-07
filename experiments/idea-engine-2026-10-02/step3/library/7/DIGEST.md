# erdosproblems.com #7: problem page and forum thread (fetched 2026-10-06T16:06:42Z)

Comments are unverified; several withdraw earlier claims.

## Page


## Forum comments
Order by
 oldest first or
 newest first. (The most recent comments are highlighted in a red border.)
 I would like to share progress on the Erdős–Selfridge odd covering conjecture.
1. Prime divisors of the overall least common multiple. Three successive papers establish that any finite covering system with pairwise distinct odd moduli greater than one must satisfy\[ \omega\!\left(\operatorname{lcm}(m_1,\ldots,m_k)\right)\ge 7,\quad 8,\quad 9, \]respectively, where \(\omega(n)\) counts the distinct prime divisors of \(n\):
- Seven Prime Divisors in Odd Distinct Covering Systems.
- Eight Prime Divisors in Odd Distinct Covering Systems.
- Nine Prime Divisors in Odd Distinct Covering Systems.
The rank-nine result therefore excludes every candidate whose moduli collectively involve at most eight primes, regardless of their exponents. Its proof combines conditional reweighting, the joint geometry of the two smallest prime coordinates, and exact finite certificates with bounds for all omitted exponent ranges.
2. Prime divisors of each individual modulus. A separate paper, Noncoverage for Distinct Odd Moduli with at Most Three Prime Divisors, proves noncoverage whenever \(\omega(m_i)\le3\) for every modulus, under the same finiteness, oddness and distinctness assumptions. Here the total number of primes occurring across the family is unrestricted: different moduli may involve different triples. Equivalently, every hypothetical odd distinct covering must contain a modulus with at least four distinct prime divisors. The proof uses conditional convex comparison and a closed system of 28 factorial moments, together with exact arithmetic and a bound for the remaining primes.
The unrestricted conjecture remains open. You can find all four papers including their LEAN formalisation and supporting materials on my website my research page.
Best of luck to everyone working on this problem. Hope the above helps.
 MichaelSchroeder
 — 14:13 on 15 Sep 2026
 👍
 0
 📝
 0
 🤖
 0
 I have posted a preprint with some elementary computational progress on this problem:
https://www.researchgate.net/publication/412442828_Closed-form_nonexistence_certificates_for_odd_covering_systems
For odd M, let u(M) be the minimum number of uncovered residues in Z/MZ when one class
is chosen for every divisor d | M, d > 1; an odd covering with lcm M exists iff u(M) = 0.
The note builds a small hierarchy of closed-form certificates for u(M) >= 1 — a "peel"
threshold of the form sigma(M/p^k)/(M/p^k) < 2 - (1 - p^-k)/(p-1), and two volume bounds
on the CRT product grid formed by the survivors of the prime-power classes — all checkable
in exact rational arithmetic with no search. Main outcomes:
(1) No covering system with distinct odd moduli > 1 has lcm below 11,486,475 (extending an
earlier search-based 2*10^6 computation, now search-free).
(2) Multi-parameter covering-free families, e.g. u(3^a 5^b 7^c) >= 1 for all exponents;
these moduli are non-squarefree, so the squarefree theorem does not apply to them.
(3) The exact value u(qr) = qr - q - r for distinct odd primes q, r, with a matching
three-prime formula u(pqr) = pqr - pq - pr - qr + 1 verified on all computed cases
(conjectural).
The note also records precisely where certificates of this type must stop: the strongly
abundant smooth moduli (the first uncertified one is 11,486,475 = 3^3·5^2·7·11·13·17),
which is where the known hard core of the problem lives. Everything here is elementary
and this is a preprint by an undergraduate — corrections, and especially pointers to any
prior appearances of these components in the literature, are very welcome.
 egeozturk
 — 19:18 on 18 Aug 2026
 👍
 0
 📝
 0
 🤖
 0
 A proof of the Erdős–Selfridge conjecture via sieve monotonicity
I would like to share a proposed proof that no covering system with distinct odd moduli greater than 1 exists, extending the BBMST framework for square-free moduli to the general case.
The key observation is that non-square-free moduli make covering harder, not easier. Replacing a prime modulus p with p^e enlarges the block size from p−1 to p^e−1, which decreases the sieve product. Since BBMST proved the square-free sieve product is approximately 0.612 < 1, the sieve product for any configuration of odd moduli is also less than 1, and covering is impossible.
The argument has been formalized in Lean 4 with Mathlib. Three axioms reference published BBMST results; the monotonicity chain (block comparison + sieve product antitone) is proved sorry-free. The formalization was audited by the Aristotle verification system (7/7 checks passed).
Paper (5 pages, self-contained): https://github.com/axxen95/Lean-4-formalization-of-the-Erd-s-Selfridge-odd-covering-system-conjecture/blob/main/erdos_selfridge_paper.pdf
Lean 4 code + audit report: https://github.com/axxen95/Lean-4-formalization-of-the-Erd-s-Selfridge-odd-covering-system-conjecture
DOI: https://doi.org/10.5281/zenodo.19982394
I would very much appreciate feedback from anyone familiar with the BBMST sieve framework, particularly regarding whether the sieve construction for primes p ≤ 73 extends to non-square-free moduli without additional difficulty. This is the one aspect of the proof that relies on a structural argument rather than formal verification.
 jinooklee
 — 16:21 on 02 May 2026
 👍
 0
 📝
 0
 🤖
 0
 To clarify: you are claiming that your Lean code proves this result, which is sorry-free, but assumes three 'axioms', which you believe follow from the [BBMST] paper? Or are you saying at the end that there is still a gap in the proof even then? (I have not checked whether your Lean code is doing as you report.)
 Thomas Bloom
 — 12:33 on 06 May 2026
 👍
 0
 📝
 0
 🤖
 0
 To clarify: the Lean code is sorry-free, and the three axioms are intended to faithfully encode published results from BBMST (Theorems 1.1 and 3.1, and the sieve data construction from Sections 2–3). The monotonicity chain connecting these axioms — that actual block sizes are pointwise ≥ square-free block sizes, and that the sieve product is antitone in block sizes — is fully proved in Lean with no axioms beyond the three stated ones.
I am not claiming there is a gap in the proof itself. I believe the axioms correctly capture the BBMST results. The question I raised at the end is whether BBMST's sieve construction for primes p ≤ 73 (which involves LP optimization and explicit enumeration) carries over to non-square-free moduli without modification. Since the distortion parameters δ_k depend only on the prime index and not on the exponent, I believe it does, but I would welcome confirmation from someone familiar with the details of Sections 4–5 of the BBMST paper.
 jinooklee
 — 12:40 on 06 May 2026
 👍
 0
 📝
 0
 🤖
 0
 Thanks for clarifying. I had a quick look but it is hard to easily tell whether your formal statements of these three 'axioms' are indeed correct translations of the results from [BBMST19]. Your writeup is also extremely short, and it seems to claim that basically [BBMST19] already essentially proved this result (i.e. that the squarefree assumption can be dropped from their result with a trivial modification of their method); I would be surprised if this were the case, since I'm sure they did think quite hard at the time about whether the squarefree assumption can be removed! 
I will leave these comments in case others would like to peruse, but I assume that this proof is flawed, until either a trusted expert in this sort of number theory vouches that your observation is correct, or you provide a full Lean formalisation which is both sorry and axiom-free (i.e. formalise the [BBMST19] results also in Lean). (Or until I find the time to sit down and carefully read your PDF/the Lean code, but I don't know when this will be.)
 Thomas Bloom
 — 12:59 on 06 May 2026
 👍
 0
 📝
 0
 🤖
 0
 Thank you for the thoughtful response. You raise a fair point — if the square-free assumption could be removed trivially, one would expect BBMST to have done so.I should clarify: I am not claiming that the modification is trivial in a mathematical sense. What the argument does is isolate one specific structural observation — that non-square-free moduli produce larger block sizes, which makes the sieve product smaller — and show that this is sufficient to extend the result under the existing framework.It is possible that BBMST considered and dismissed this direction because the sieve construction for p ≤ 73 involves LP optimization that may not obviously carry over to non-square-free moduli. My argument relies on the claim that the distortion parameters δ_k depend only on the prime index, not on the exponent, so the monotonicity propagates through the δ-adjusted block sizes. Whether this is correct is exactly the point I would welcome expert verification on.I have written to Dr. Tiba to ask whether the BBMST framework does indeed extend in this way. I will report back if I hear from him.
 jinooklee
 — 13:51 on 06 May 2026
 👍
 0
 📝
 0
 🤖
 0
 I have written to Dr. T