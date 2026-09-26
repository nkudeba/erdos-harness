# Draft comment for erdosproblems.com/forum/thread/273

**Twenty of the twenty-nine candidate lcm values below 400,000 are eliminated without a search**

Following the comment reporting that "a covering has to live at large moduli with forced
overlaps, which is where all our searches died": here is an elementary test that clears a good
deal of that ground with no search at all.

**Setup.** Write a candidate system as classes $(a_m \bmod m)$ with distinct moduli $m = p-1$
($p \ge 5$ prime), all dividing $L = \mathrm{lcm}$, and let $k = \sum_m L/m - L$ be the total overlap.

**Claim.** For every $d \mid L$ with $d > 1$ and every primitive $d$-th root of unity $\zeta$,
$$\sum_{m \in U,\, d \mid m} \frac{L}{m}\,\zeta^{a_m} \;=\; \sum_{j \bmod d} e(j)\,\zeta^{j},$$
where $e(j) \ge 0$ is the excess on the fibre $j \bmod d$. In particular the left side has
modulus at most $k$.

*Proof.* Split $\mathbb{Z}/L$ into the $d$ fibres mod $d$. A modulus with $d \mid m$ lies inside a
single fibre and contributes $L/m$ to it. A modulus with $d \nmid m$ has $g = \gcd(m,d) < d$ and
spreads evenly over the fibres $j \equiv a_m \pmod g$; its transform is
$\zeta^{a_m}\sum_t \zeta^{gt} = 0$. Each fibre holds $L/d$ points covered at least once, and the
constant part has zero transform, so only the excess survives — and it carries only $k$ units of
mass. $\square$

This is the standard Mirsky–Newman argument applied at every $d$ rather than only at the largest
modulus; no novelty of technique is claimed.

**Screen.** By the reverse triangle inequality, with $W = \{L/m : m \in U,\ d \mid m\}$,
$$2\max(W) - \textstyle\sum(W) > k \quad\Longrightarrow\quad \text{no such system,}$$
with no reference to the residues.

**Tightest form.** For $\mu_d = \min\{m \in U : d \mid m\}$ the constraint taken at $d = \mu_d$ is
tighter, since the multiples of $\mu_d$ are a subset of the multiples of $d$. So the family
collapses to: for every $\mu \in U$,
$$\frac{L}{\mu} - \sum_{m \in U,\ \mu \mid m,\ m \neq \mu} \frac{L}{m} \;\le\; k .$$
Rearranged, the left-hand side is monotone in $U$, so a $\mu$ violating it under the maximal
admissible set violates under every subset containing it and can be deleted outright. Iterating
to a fixed point decides the whole family in polynomial time — no subset enumeration is needed.

**Results.** There are 29 values of $L \le 400{,}000$ whose admissible divisors have reciprocal
sum $\ge 1$. Twenty are eliminated:

> 55440, 65520, 100800, 131040, 151200, 181440, 196560, 201600, 205920, 226800, 231840,
> 241920, 257040, 308880, 327600, 342720, 347760, 360360, 362880, 378000

Nine survive: 110880, 166320, 221760, 262080, 277200, 302400, 332640, 388080, 393120.

**So no covering system of this form has lcm below 110,880.**

$L = 55{,}440$ dies at $d = 16$ by a margin of 16 ($|P| \ge 2437$ against $k \le 2421$), and
$L = 100{,}800$ at $d = 16$ by 1894 ($|P| \ge 1903$ against $k \le 9$). The modulus 16 does most of
the work: 17 is prime, so 16 is admissible, and it is forced in every one of these candidates
while the other admissible multiples of 16 are too sparse to cancel its weight.

**Where it stops, and why.** $k \le \mathrm{slack}\cdot L$ with
$\mathrm{slack} = \sum_{m \mid L \text{ admissible}} 1/m - 1$, so the inequality bites exactly when
the slack is tiny. The twenty eliminated are the tight candidates; the nine survivors all have
slack 0.02–0.08 and thousands of units of excess to absorb any imbalance. The closest survivor,
$L = 302{,}400$, misses by 1,944 against a budget of 6,700 — not a near miss.

**Validation.** The identity was checked numerically at every divisor of $L$ on genuine covering
systems whose residues were found by exhaustive search rather than guessed (worst residual
$10^{-14}$), and the screen was regression-tested against 3,130 genuine covering systems with
distinct moduli and lcm exactly $L$, built across $L = 12 \ldots 720$ — no false kills. The two
tightest eliminations were re-derived in exact rational arithmetic.

This eliminates candidates, not the problem. The 400,000 cap is compute rather than a theorem, and
a witness may have a much larger lcm.

*AI usage disclosure: this was prepared with assistance from Claude (Anthropic). Every numerical
claim comes from an executed run, and the borderline cases were re-checked in exact arithmetic.*
