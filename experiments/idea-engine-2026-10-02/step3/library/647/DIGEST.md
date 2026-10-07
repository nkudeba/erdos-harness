# erdosproblems.com #647: problem page and forum thread (fetched 2026-10-06T16:07:40Z)

Comments are unverified; several withdraw earlier claims.

## Page


## Forum comments
Order by
 oldest first or
 newest first. (The most recent comments are highlighted in a red border.)
 We have verified in Lean 4 that there is no solution with $24 < n \le 10^8$. The proof is a chain of 891,554 witnesses $m$, each stored with its factorization into primes below 1024; the kernel recomputes a lower bound $t \le \tau(m)$ from each factorization and checks that the intervals $[m+1, m+t-3]$ cover $(24, 10^8]$ with no gap. The final theorem depends on exactly the three standard axioms (propext, Classical.choice, Quot.sound): no native_decide, no sorry. The statement follows the formal-conjectures formalization at a pinned commit.
This range is much smaller than the existing searches (Idén to $10^{12}$, Hughes and bentrd to about $9.17 \times 10^{18}$); the difference is that nothing below $10^8$ depends on unverified computation.
Repository and reproduction instructions: https://github.com/ibrahimmian36/decanus
Formal-conjectures issue: https://github.com/google-deepmind/formal-conjectures/issues/5021
AI-usage disclosure: Claude helped to develop the Lean proofs and the generation scripts. The generator is cross-checked by an independent implementation.
 IbbyMian
 — 21:17 on 17 Aug 2026
 👍
 0
 📝
 0
 🤖
 0
 Kernel-checked exclusion to 10^13, building on decanus
Following IbbyMian's decanus certificate (kernel-checked to 10^9, arXiv:2608.17880) and its suggestion to certify structure rather than length: I have a Lean 4 / Mathlib proof, checked by the kernel with axioms exactly {propext, Classical.choice, Quot.sound} and no native_decide, that no n in (24, 10^13] satisfies the condition, stated on the formal-conjectures predicate so it composes with decanus.
Method: four modular sieve stages proved inside the kernel (2520 | n for n > 1800; 360360 | n for n > 10^5; ScottHughes's 41-class reduction on (n mod 17, n mod 19), re-derived kernel-clean; a 4,431-class survivor list mod 17·19·23·29 for n > 10^11), then one factorization witness per surviving grid point: 866,484 witnesses in about 21 MB of Lean, versus 6.7 million for the contiguous 10^9 chain. 48.8 CPU-hours on one 8-core desktop.
Repository with source, certificates, generators, verification record and a 9-page writeup: https://github.com/fjordmindlabs/math/tree/main/erdos647-sparse
Two notes. (1) This is a certification result, nine orders of magnitude below veljjanoski's 10^22; it does not approach the unverified frontier. (2) A cost model in the writeup suggests the kernel-checked horizon of this family of methods is about 10^17–10^18 (period walk, about one CPU-year), and that no finite table of such sieve stages can prove the statement, since the divisor budget never excludes n ≡ 0 (mod L) for any L.
The Lean proofs and generators were written by an AI coding agent under my direction; the kernel checks them the same way. @IbbyMian: happy to open a PR adding this as a sibling library to decanus if you would like one, or to keep it as a companion repository, your call.
 eerot
 — 14:16 on 04 Oct 2026
 👍
 1
 📝
 0
 🤖
 0
 I have verified computationally that there is no solution with $24 < n \le 10^{20}$, extending the previous frontier of $\approx 9.17 \times 10^{18}$ (Hughes, bentrd).
Method: every solution $n > 40$ is a multiple of $2520$ (re-derived by a CRT lifting through $2^6 \cdot 3^4 \cdot 5^3 \cdot 7^3$). Candidates are further restricted to residue classes mod $2520 \cdot (11 \cdot 13 \cdot 17 \cdot 19)^2$ and then eliminated on a GPU using only two facts about $\tau$: $d \mid x \Rightarrow \tau(d) \le \tau(x)$, and multiplicativity. For a shift $k$, if a prime $p$ exactly divides $n-k$ with a cofactor $> 1$, then $\tau(n-k)$ is at least four times the divisor count of the $2520$-part of $n-k$, which exceeds $k+2$ for $k \in {1,2,3,4,5,6,8,9,10,12,18,20,24}$; these shifts are sieved as arithmetic progressions for all primes up to $1000$. Survivors (about $2.5 \cdot 10^{-5}$ of the candidates) are then checked with exact valuations for all primes below $65536$ and all shifts $k \le 64$, and finally by full factorisation. Nothing survived the second stage. Total time 1 h 54 min on an RTX 3090. This is an independent search: it does not build on the Hughes residue certificate, and it re-derives the $2520$ reduction and its own wheel.
Validation: with the budget relaxed to $\tau(n-k) \le k+2+\delta$ the condition has many small solutions, and for $\delta = 6$ and $\delta = 12$ the pipeline reproduces the exact sieve's solution set on $[1, 2 \cdot 10^8]$ ($868$ of them found purely by the GPU stages); the 128-bit kernel path was also unit-tested against a Python replica on candidates above $2^{64}$. This is an uncertified computation, not a Lean certificate.
Code, log and checkpoint: https://github.com/veljjanoski/erdos647
AI-usage disclosure: Claude (Anthropic) was used as a coding assistant.
 veljjanoski
 — 08:00 on 10 Sep 2026
 👍
 0
 📝
 0
 🤖
 0
 Update: the search is now complete to $10^{22}$. There is no solution with $24 < n \le 10^{22}$. Same method as above with two more wheel primes ($23$, $29$) applied inside the kernel; about 20 GPU-hours on an RTX 3090, zero survivors of the exact-valuation stage.
Logs and checkpoint are in the repository: https://github.com/veljjanoski/erdos647. Still an uncertified computation.
AI-usage disclosure: Claude (Anthropic) was used as a coding assistant.
 veljjanoski
 — 06:43 on 13 Sep 2026
 👍
 0
 📝
 0
 🤖
 0
 For what it's worth (arguably not much), here's a funny observation. Use $(\ast)$ to denote the equation $\tau(n-k)\le k+2$. Using modular constraints and elementary properties of $\tau$, it's not difficult to prove the following :-
1. If $n>5$ satisfies $(\ast)$, then $n$ is even.
2. If $n>10$ satisfies $(\ast)$, then $4\mid n$.
3. If $n>24$ satisfies $(\ast)$, then $6\mid n$.
4. If $n>54$ satisfies $(\ast)$, then $5\mid n$.
5. If $n>54$ satisfies $(\ast)$, then $7\mid n$.
6. If $n>36$ satisfies $(\ast)$, then $8\mid n$.
7. If $n>84$ satisfies $(\ast)$, then $9\mid n$.
So, any $n>84$ satisfies $(\ast)$, then $n=2520N$. Now, using
$$\tau(n-k) = \tau(k)\cdot \tau\!\left(\frac{2520N}{k}-1\right) \le k+2$$
with $k=1,2,3,4,6,8,12,24$ also gives that $2520N-1$ is either a prime or a prime square, and $1260N-1$, $840N-1$, $630N-1$, $420N-1$, $315N-1$, $210N-1$, $105N-1$ are primes.
Of course, all these constraints don't give any obvious contradiction by themselves.
 Sayan Dutta
 — 13:40 on 18 Jan 2026
 👍
 4
 📝
 1
 🤖
 0
 I really like these observations. Thanks for writing them up.
For example, they really help when sieving for "counterexamples". OEIS A087280 says that there are no more examples "< 10^10". With these observations, and with the big assumption of no implementation errors, I think there are no examples for several more orders of magnitude, up to $10^{16}$ or even more.
But let me check my understanding of the claims:
It seems to me that the second step, with $\tau(k)\cdot\tau\left(\frac{2520N}{k}-1\right)$ doesn't necessarily work for $k=8$ and $k=24$ because potentially all of the powers of $2$ have been divided out and $k$ and $\frac{2520N}{k}-1$ are not necessarily relatively prime? It seems to me that it's possible, for example, for $105N-1$ to be four times a prime. As a concrete case, consider $n=604517614941240$ which comes from $N=239887942437$. I find that $\tau(n-k)\le k+2$ for $1\le k\le 13$ and also $k=24$. However, $105N-1$ is four times a prime and $315N-1$ is twice a prime, so neither prime by themselves. Let me know if I'm missing something about the argument.
In the other direction, it seems to me that it's also possible to show that $11\mid n$ and $13\mid n$ with arguments as in the first part. I just needed to do a trick like ruling out $7\pmod{11}$ by thinking of it as $18\pmod{11}$ instead. Hopefully I was reasoning correctly there.
Oh, and $2520N-1$ can't be a square because it's $3\bmod 4$.
 BorisAlexeev
 — 00:50 on 19 Jan 2026
 👍
 4
 📝
 0
 🤖
 0
 Thanks for your reply - you are absolutely right about the co-primality issue. One can still salvage some constraints for $k=8,24$ by peeling off the $2$-adic valuation. For example, $315N-1 \in \{p,2p\}$ and $105N-1 \in \{p, p^2, 2p, 4p\}$ which is probably something you were also trying to hint at. About the $11\mid n$ and $13\mid n$ claims, I was also under the idea that they were true, but it just broke down into so many cases that I could not believe myself enough to claim it here.
Also good point: since $2520N-1\equiv 3\pmod 4$, it can’t be a square - combined with the observation in my previous comment, this upgrades the $k=1$ conclusion to $2520N-1$ being a prime.
(Everything in this comment is for large $N$)
 Sayan Dutta
 — 17:49 on 19 Jan 2026
 👍
 2
 📝
 0
 🤖
 0
 Since $2(1260N-1)+1=2520N-1$, infinitely many $N$ satisfying this would imply that there are infinitely many Sophie Germain primes.
 megahertz13
 — 21:15 on 02 Sep 2026
 👍
 1
 📝
 1
 🤖
 0
 Update to my earlier comment (June 13): an updated report (v2) is now available with ad