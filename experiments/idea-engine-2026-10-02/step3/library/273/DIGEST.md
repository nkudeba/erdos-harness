# erdosproblems.com #273: problem page and forum thread (fetched 2026-10-06T16:07:06Z)

Comments are unverified; several withdraw earlier claims.

## Page


## Forum comments
Order by
 oldest first or
 newest first. (The most recent comments are highlighted in a red border.)
 A small observation and a computation, and a pointer to a stronger result. Every modulus $p-1$ is even, so the classes with even residues and those with odd residues form two separate coverings of $\mathbb{Z}$ after dividing by $2$: a covering with distinct moduli $p-1$ ($p\ge 5$) is the same as two coverings with disjoint sets of moduli of the form $q=(p-1)/2$, one of which cannot use $q=2$ and is therefore a covering with distinct moduli $q\ge 3$, $2q+1$ prime (a pool without $4,10,12,24,40$).
By an exact search (depth-first over the moduli with the bound "uncovered residues $\le$ sum over unused moduli of their largest uncovered class", run for every divisibility-maximal lcm $L'\le 15120$ whose pool has reciprocal sum $\ge 1$; $271$ lcms $L'\le 15120$ pass that counting test), no such modulus-$2$-free covering with $\operatorname{lcm}\le 15120$ exists. The programs reproduce Selfridge's covering from the divisors of $360$ when $p=3$ is allowed, and every reported covering is rechecked by direct enumeration.
For the whole system this gives only $\operatorname{lcm}>30240$, which is weaker than counting alone: the sum of $1/m$ over divisors $m$ of $L$ with $m+1$ prime is below $1$ for every $L<55440$. Much better, R. Zeraoulia (July 2026, doi:10.5281/zenodo.21613011, see the proof-claims thread) proves $\operatorname{lcm}\ge 393120$: $28$ values $L<393120$ pass the counting test, a parity-capacity argument with the forced moduli $4$ and $6$ removes $23$ of them, and a forced-residue-class certificate removes the remaining five. I re-implemented that certificate independently and reproduce all its numbers. 
Nothing is claimed about existence at larger lcm; as a rough gauge only, greedy placement with local search leaves between $10\%$ and $14\%$ of the integers uncovered with the full pool at lcm $55440$ to $1.66\cdot 10^6$.
Code and logs: https://github.com/veljjanoski/erdos273
AI-usage disclosure: Claude (Anthropic) was used as assistant.
 veljjanoski
 — 11:11 on 24 Sep 2026
 👍
 0
 📝
 0
 🤖
 0
 Update: no covering system with distinct moduli $p-1$ ($p\ge 5$) has $\operatorname{lcm}<4\cdot 10^6$ (previous bound: $\operatorname{lcm}\ge 393120$, Zeraoulia). A covering with $\operatorname{lcm}$ $L$ needs $\sum 1/m\ge 1$ over the divisors $m\ge 4$ of $L$ with $m+1$ prime, and every such $L<4\cdot 10^6$ divides one of the $213$ such values in $[2\cdot 10^6,4\cdot 10^6)$. For each of these, the exact search from my earlier comment (run on the moduli $p-1$) finds no covering, and a second, separately written search agrees.
 veljjanoski
 — 08:32 on 28 Sep 2026
 👍
 1
 📝
 0
 🤖
 0
 The same computation now gives $\operatorname{lcm}\ge 8\cdot 10^6$: for each of the $420$ candidates in $[4\cdot 10^6,8\cdot 10^6)$, both exact searches find no covering. 
Logs and code: https://github.com/veljjanoski/erdos273
 veljjanoski
 — 14:36 on 28 Sep 2026
 👍
 0
 📝
 0
 🤖
 0
 Hi 
I'm not a mathematician expert at all but I've been experimenting with AI assistants on some of these problems
so here is what came out for this one: 
Two necessary conditions on any covering with distinct moduli $p-1$, $p \geq 5$:
1. Every such covering must use a modulus with $p > 877$ — the 149 moduli with $p \leq 877$ cannot cover $\mathbb{Z}$ on their own. Proved with the BBMST distortion sieve (arXiv:1811.03547) applied to this pool; the final inequality is certified in exact rational arithmetic.
2. $\sum 1/(p-1) \geq 1 + \exp(-3.36 \times 10^{21})$. Apparently the first budget bound away from 1 here. It falls out of Filaseta–Kalogirou (arXiv:2407.15280) once you check that the 3-smooth moduli in this pool (the Pierpont primes $2^a 3^b + 1$) only sum to $\approx 0.706 < 11/12$.
There is a repo with the short paper, all scripts, the rational certificates, and a Lean-checked parity reduction: paper_273
The existence question stays open, probably yes, but a covering has to live at large moduli with forced overlaps, which is where all our searches died. Independent checking would be welcome.
I hope this helps
 ideal_ombrer
 — 16:08 on 12 Jul 2026
 👍
 0
 📝
 0
 🤖
 0