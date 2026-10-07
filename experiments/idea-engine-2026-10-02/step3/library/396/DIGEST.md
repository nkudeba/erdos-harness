# erdosproblems.com #396: problem page and forum thread (fetched 2026-10-06T16:07:24Z)

Comments are unverified; several withdraw earlier claims.

## Page


## Forum comments
Order by
 oldest first or
 newest first. (The most recent comments are highlighted in a red border.)
 I looked at the theoretical side a little bit with GPT-5.4 Thinking.
Let $E_k := \{ n : n(n-1)\dots(n-k) \mid \binom{2n}{n} \}$. Let $d$ denote density and $\overline{d}$ denote upper density.
Pomerance proved $\overline{d}(E_0) < 1/3$. In fact his argument gave $\overline{d}(E_0) \le 1-\log 2 = 0.306\dots$. Nevertheless, Ford and Konyagin (2021) has completely settled this as $d(E_0) = c_1 := 0.114\dots$; in particular the density of the set exists.
It follows trivially that $\overline{d}(E_k) \le c_1$. But we were not able to even prove $\overline{d}(E_k) < c_1$ for $k > 0$. However, heuristically we do expect $\overline{d}(E_k) \approx c_1^{k+1}$. This is confirmed to line up well with the available computational evidence. In particular, the smallest $n$ for each $k$ should increase by about $1/c_1 \approx 8.75$ each time.
 Nat Sothanaphan
 — 15:50 on 05 Apr 2026
 👍
 1
 📝
 0
 🤖
 0
 Very interesting chat w/ GPT 5.4...thanks for sharing that link. I went through the entire chat you had, but was a bit surprised your LLM bailed out after 9 mins when you asked for the ordinary upper density proof for $d(E_k) < c_1$ for $k>0$.
I pushed it to think a bit harder on your last question using the Pro setting, and it ended up thinking for roughly an order of magnitude more compute than your earlier pass (~93 mins total). It seems it was able to at least get a genuine strict gap below $c_1$, but for logarithmic density rather than ordinary upper density.
Let
$$E_k := \left\{ n > k : \prod_{j=0}^k (n-j) \mid \binom{2n}{n} \right\},$$
and let $\overline{\delta}$ denote upper logarithmic density.
For any fixed $k \ge 1$, if $n \in E_k$, then in particular both $n \mid \binom{2n}{n}$ and $n-1 \mid \binom{2n}{n}$. Apply the same no-carry argument used by Pomerance: if $p \mid (n-j)$ with $p > \sqrt{2n}$, then $p \nmid \binom{2n}{n}$. Hence every $n \in E_k$ must satisfy
$$P^+(n) \le \sqrt{2n} \qquad \text{and} \qquad P^+(n-1) \le \sqrt{2n},$$
where $P^+$ is the largest prime factor.
So $E_k$ is contained in the set of consecutive $\sqrt{2x}$-smooth pairs up to $x$. Recent work of Tao-Teräväinen on consecutive smooth numbers then gives, on a set of $x$'s of logarithmic density $1$,
$$\#\left\{ m \le x : P^+(m) \le x^{1/u},\; P^+(m-1) \le x^{1/u} \right\} = (\rho(u)^2 + o(1))\,x.$$
Taking $u \to 2$ gives
$$\overline{\delta}(E_k) \le \rho(2)^2 = (1-\log 2)^2 \approx 0.09416.$$
Since Ford–Konyagin proved
$$d(E_0) = c_1 \approx 0.11424,$$
this yields the strict inequality
$$\overline{\delta}(E_k) \le (1-\log 2)^2 < c_1 \qquad (k \ge 1).$$
So while this may not prove $\overline{d}(E_k) < c_1$ in the ordinary sense, it does show that once you ask for even one backward step, the set is already strictly sparser than the governor set at the logarithmic-density level. In particular, if the ordinary density $d(E_k)$ happens to exist, then automatically
$$d(E_k) < c_1.$$
At least to me, that seems significant: it says the $k > 0$ problem is not just "the $k = 0$ problem with a bounded shift" but a genuinely more correlated/rarer pattern problem.
 Justin Dehorty
 — 09:43 on 07 Apr 2026
 👍
 1
 📝
 0
 🤖
 0
 Thanks. Different ways of interactions do give different results. For this particular one I wasn't trying to get results by any possible means but only trying to map out the landscape.
About the conclusion regarding correlation problem, this is already known by the heuristic $\overline{d}(E_k) \approx c_1^{k+1}$, although this seems not provable at present.
The new result $\overline{\delta}(E_k) \le \rho(2)^2$ for $k \ge 1$ regarding upper logarithmic density is interesting and appears to be correct.
For reference, the basic relationships are:
$$ \underline{d}(A) \le \underline{\delta}(A) \le \overline{\delta}(A) \le \overline{d}(A). $$
In particular, if the density $d(A)$ exists, then all four quantities are equal.
Unfortunately, I wasn't able to get any stronger upper bound than $\rho(2)^2$ on any of the quantities for $k > 1$. The Tao-Teräväinen input seems to top out at two-point correlations.
Credit to GPT-5.4 Thinking for discussion.
 Nat Sothanaphan
 — 16:16 on 07 Apr 2026
 👍
 1
 📝
 0
 🤖
 0
 I've been running Sharvil's computational search for a few days on my server (9800x3d processor, about 4x performance from his laptop) and the program has produced that $k=14$ does have a solution with minimal $n=359503904702190$.
This took about 2.5 days running to complete, and since the values are increasing by a factor of around 10 each time, the next values are increasingly impractical to calculate this with brute force approach. Around the end, the program was searching 1365.74 M candidates/s, which is still very fast but not for the size of these values. With a quick napkin estimate, I expect the next value to take at least a month with the current search program, which is a bit much for me to continue searching. In the past days Sharvil has done some optimisations to his program, which I will leave to him to detail, though they are all smaller than the order of magnitude appearing between these terms.
 wibble132
 — 14:28 on 03 Apr 2026
 👍
 2
 📝
 0
 🤖
 0
 Really awesome to see this result. This matches the exact result computed on April 1st by myself (using Rust and the algorithm Sharvil and I co-developed) and I understand from the ongoing OEIS discussion thread that Sharvil's friend also computed it on the same day (triple confirmation!)
Re: The recent optimizations you alluded to...
Moving forward, moderators have requested that we continue algorithmic discussions along those lines at a separate location so we don't spam the comments section of this problem. As such, I have set up a GitHub Gist for further discussion and have compiled all information exchanged on this thread and GitHub so that others may get up to speed and contribute to these recent advances more easily in the future:
Search Algorithm Optimizations for A375077
I have done my best to source everything and provide accurate sources/attributions, but mistakes or omissions are possible. @Sharvil and others - please let me know in the comments section of that Gist if there is anything there that needs to be adjusted or added.
 Justin Dehorty
 — 22:48 on 04 Apr 2026
 👍
 1
 📝
 0
 🤖
 0
 I really applaud all the computational progress here! Hopefully all this culminates in some kind of paper or visible accomplishment.
 Nat Sothanaphan
 — 15:19 on 05 Apr 2026
 👍
 1
 📝
 0
 🤖
 0
 $\largeExtending OEIS A375077 through k=13$
$Exhaustive search, validation, and a formally verified barrier theorem$
Over the past several months I have been running an exhaustive computational search for [396] witnesses, extending OEIS A375077 with 6 new terms at the initial time of discovery (2 new terms at the time of this post). The full codebase, validation certificates, and a machine-checked proof are publicly available at github.com/jdehorty/erdos396.
New values:
$\begin{array}{c|c|c|c}
k & a(k) & \text{Search range} & \text{Date found*} \\ \hline
8 & 339{,}949{,}252 & 0\text{–}340\text{M} & \text{2025-01-17} \\
9 & 1{,}019{,}547{,}844 & 0\text{–}17.6\text{B} & \text{2026-03-16 (corrected)} \\
10 & 17{,}609{,}764{,}994 & 0\text{–}17.6\text{B} & \text{2025-01-20} \\
11 & 1{,}070{,}858{,}041{,}585 & 0\text{–}2\text{T} & \text{2026-02-09} \\
12 & 5{,}048{,}891{,}644{,}646 & 0\text{–}6.15\text{T} & \text{2026-02-11} \\
13 & 18{,}253{,}129{,}921{,}842 & 0\text{–}25\text{T} & \text{2026-02-16}
\end{array}$
*Note: Dates reflect my own personal records of when each value was first found, not when results were submitted or published. The jumps in pace (particularly from k=11 onward) correspond to successive sieve improvements: the v1 prefilter (7x), the fused sieve pass (15x), and finally Kummer-based valuation for all primes (31x single-threaded throughput). 
Each value has a computational certificate of minimality: every integer below the claimed witness has been checked and ruled out.
Note on $k=9$: the original governor-run search found a witness at $17{,}609{,}764{,}993$. A subsequent full validation pass (checking every integer, not just governor-run candidates) found the true minimum at $1{,}019{,}547{,}844$.
$Method.$ The search is built around the Governor Set $G = \{n : n \mid \binom{2n}{n}\}$ (OEIS A014847, density $\approx 12.3\%$ by Ford-Konyagin). All known witnesses have every block term $n, n-1, \ldots, n-k$ in $G$. A fused segmented sieve strips small prime factors and checks the Kummer carry condition $\nu_p(n) \leq \nu_p\!\binom{2n}{n}$ inline, rejecting ${\sim}87\%$ of integers in a single pass. The $\sqrt{2n}$ large-prime-factor barrier provides additional fast rejection. Runs of $k+1$ consecutive governors are candidate witnesses, each verified by the full inequality $\sum_{i=0}^{k} \nu_p(n-i) \leq \nu_p\!\binom{2n}{n}$ at every prime $p$.
$The Small Prime Barrier Theorem.$ The governor-run search canno