# erdosproblems.com #375: problem page and forum thread (fetched 2026-10-08T01:42:14Z)

Comments are unverified; several withdraw earlier claims.

## Page


## Forum comments
Order by
 oldest first or
 newest first. (The most recent comments are highlighted in a red border.)
 Grimm's conjecture has been verified computationally for every maximal run of consecutive composite integers whose closing prime is below $10^{13}$, extending the corresponding $10^{12}$ verification reported above by a factor of 10 (and the refereed bound $1.9\times 10^{10}$ of Laishram and Shorey [LaSh06] by a factor of about 500).
The computation started at $2$, so it is also an independent re-check of all such runs with closing prime below $10^{12}$.
- Primes seen: 346,065,536,839; composite runs checked: 346,065,536,837; failures: 0.
- Longest run: $k=673$ after $n=7177162611713$. Below $10^{12}$ the longest run is $k=539$ after $n=738832927927$, in agreement with the earlier report.
- Total compute: about 434 thread-hours.
Method. A segmented sieve with all primes up to $\sqrt{10^{13}}$ gives the largest prime factor (LPF) of every integer. If the LPFs in a run are pairwise distinct they already form a system of distinct representatives; two members can share an LPF $q$ only if $q<k$, so only those are compared. Otherwise the run is fully factored by trial division and decided by bipartite matching. 1,968 runs needed the matching step; all succeeded. The range is processed in 10,000 chunks of width at most $10^9$; each chunk sieves from 8192 below its start and aborts if no prime is found there, so no run is cut at a chunk boundary unnoticed.
Checks.
- An independent brute-force implementation (smallest-prime-factor table and networkx maximum matching, no shared code) agrees on $[2, 2\times 10^6)$: same counts of primes, runs, longest run and failures.
- A deliberately weakened mode (each member may use only its smallest prime factor) reports 134,060 failures on the same range, so the failure path is exercised.
- The sieve's prime counts match OEIS A006880 at $10^{10}$, $10^{12}$ and $10^{13}$, and the per-chunk longest runs match the record prime gaps of A005250/A002386 between $10^9$ and $10^{13}$ (one record shares a chunk with a larger one and is not visible in the per-chunk maximum).
Caveats. Above $2\times 10^6$ the result rests on a single implementation; the prime-count and record-gap checks test the sieve and the run bookkeeping, not the matching step on large runs. This is a finite verification, not a proof.
Code, per-chunk logs, SHA-256 checksums and reproduction instructions: https://doi.org/10.5281/zenodo.23073168
Disclosure: the code, the computation and this write-up were produced with AI assistance (Claude, Anthropic); all figures come from the executed runs recorded in the archive. This post was also reviewed with Codex (OpenAI).
 yygotm
 — 01:48 on 01 Oct 2026
 👍
 0
 📝
 0
 🤖
 0
 The first two page numbers are [Er72,p.84] and [Er73,p.136].
Grimm's conjecture also has a Wikipedia page here.
Using Hall's marriage theorem, one can show that Grimm's conjecture is equivalent to a seemingly-weaker statement: if $S \subseteq \mathbb{N}$ is contained in an interval of composite numbers, then the amount of elements in $S$ is less than or equal to the amount of primes that divide at least one element in $S$. This observation might be worth mentioning in the main text, though it already appears in the literature and thus should not be credited to me.
Feel free to delete this comment.
 DesmondWeisenberg
 — 21:52 on 02 Sep 2026
 👍
 0
 📝
 2
 🤖
 0
 Grimm's conjecture has been verified computationally to $10^{12}$, extending the $1.9\times 10^{10}$ bound of Laishram and Shorey [LaSh06] by a factor of 52.6.
Precisely: every maximal run of consecutive composite integers whose closing prime is below $10^{12}$ admits a system of distinct prime representatives. 37,607,912,844 prime gaps were checked with no counterexample and no truncation. The largest gap encountered was $k=539$ after $p=738832927927$. 166,597 runs required a nontrivial matching and 6,475 had three or more elements competing for the primes below the gap length.
Code, certificates and a reproduction script are at github.com/thebrockchain/grimm-conjecture-verification.
The computation is calibrated against a naive brute force sharing no code or reduction with the sweeper (0 missed, 0 extra, 0 verdict disagreements on $[2, 2\times 10^6)$), the sharding is checked row for row, and the sieve reproduces $\pi(10^8)$, $\pi(10^{10})$ and $\pi(10^{12})$ exactly, the last through the shard overlap accounting. A sample of the certificate, including every row where four or more elements competed, is re-derived from scratch by an independent checker. The script check.sh reruns the whole audit in about two minutes.
One caveat worth stating explicitly: the method dismisses run members having a prime factor above a smoothness bound $B$, and records a truncation rather than a success if a run needs a prime above $B$. Five maximal gaps below $10^{12}$ exceed 512, so $B=2048$ was used from $2.5\times 10^{11}$ onward. Truncations over the full range: 0.
This is a verification, not a proof. The conjecture remains open.
 thebrockchain
 — 05:17 on 27 Aug 2026
 👍
 0
 📝
 0
 🤖
 0
 The provenance of the claim that this conjecture implies $p_{n+1} - p_n < p_n^{1/2-c}$ is a little murky. Theorem 1 of the 1971 paper of Erdos and Selfridge gets the weaker bound $p_{n+1} -p_n \ll p_n^{1/2} / \log^{1/2} p_n$ (which is already enough to get Legendre's conjecture asymptotically) and assert without proof that the result of Ramachandra concerning the existence of non-smooth numbers in short intervals gets the power saving, but on page 15 they write "we do not give the details here".
Theorem 1 is proven by noting that if Grimm's conjecture held, then $\binom{n+k}{k}$ would have to be divisible by at least $k-\pi(k)$ primes larger than $k$, and this and standard prime number theorem and Stirling approximation estimates is enough to conclude. I guess Ramachandra's result would allow one to say that some of these primes are actually rather large, but the actual calculations seem to require some care (one needs a "positive density" version of Ramachandra's result, I think).
 TerenceTao
 — 16:46 on 16 Jan 2026
 👍
 0
 📝
 0
 🤖
 0
 More generally, Langevin conjectured that any sequence of consecutive numbers, all of which are composite, must form a set of multiplicatively independent numbers.
 Dogmachine
 — 22:23 on 06 Jan 2026
 👍
 1
 📝
 0
 🤖
 0
 In Grimm's conjecture on consecutive integers(2006), S. Laishram and T. N. Shorey have proved this conjecture for $n \leq 1.9 \times 10^{10}$ and for all k.
P. S. I believe the bound by [RST75] can be pushed further (under stronger conjectures like Elliot Halberstam Conjecture).
Edit: Earlier, there was an embarrassing careless mistake here.
(The site has been updated to address this comment.)
 Alfaiz
 — 11:30 on 03 Dec 2025
 👍
 0
 📝
 1
 🤖
 0
 Note; the cubic boune of RST75 is stronger than the quadratic bound.
By Cramer s conjecture, the bound of RST75 and the verification for small n, the answer to this problem should surely be positive.
 StijnC
 — 09:14 on 04 Dec 2025
 👍
 0
 📝
 0
 🤖
 0
 Show 1 more comments