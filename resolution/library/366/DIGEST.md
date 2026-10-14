# erdosproblems.com #366: problem page and forum thread (fetched 2026-10-08T15:20:20Z)

Comments and proof claims are unverified; several withdraw earlier claims.

## Page
Are there any $2$-full $n$ such that $n+1$ is $3$-full? That is, if $p\mid n$ then $p^2\mid n$ and if $p\mid n+1$ then $p^3\mid n+1$. 
#366: [Er76d,p.31][ErGr80,p.68]
number theory | 
powerful
Erdős originally asked Mahler whether there are infinitely many pairs of consecutive powerful numbers, but Mahler immediately observed that the answer is yes from the infinitely many solutions to the Pell equation $x^2=8y^2+1$. 
Note that $8$ is 3-full and $9$ is $2$-full. Erdős and Graham asked if this is the only pair of such consecutive integers. Stephan has observed that $12167=23^3$ and $12168=2^33^213^2$ (a pair already known to Golomb [Go70]) is another example, but (by OEIS A060355) there are no other examples for $n<10^{22}$.
In [Er76d] Erdős asks the weaker question of whether there are any consecutive pairs of $3$-full integers (which is also discussed in problem B16 of Guy's collection [Gu04]).
Turturean notes in the comments that the ABC conjecture implies there are only finitely many such $n$.
Additional thanks to: Stijn Cambie, David Turturean, Ralf Stephan, Wouter van Doorn, and Desmond Weisenberg

## Forum comments
Order by
 oldest first or
 newest first. (The most recent comments are highlighted in a red border.)
 The abc conjecture implies there are only finitely many solutions to this problem.
Suppose $n$ is 2-full and $n+1$ is 3-full (the other direction is identical, i.e if $n$ is 3-full and $n+1$ is 2-full, however that is beyond the scope of this problem).
Then:
$$\mathrm{rad}(n) \leq n^{1/2}, \qquad \mathrm{rad}(n+1) \leq (n+1)^{1/3}.$$
Since $\gcd(n, n+1) = 1$, applying abc to the triple $(n, 1, n+1)$ tells us that for any $\varepsilon > 0$, all but finitely many such $n$ satisfy
$$n + 1 \leq K_\varepsilon \cdot \mathrm{rad}(n(n+1))^{1+\varepsilon} \leq K_\varepsilon \cdot n^{(1+\varepsilon)/2} \cdot (n+1)^{(1+\varepsilon)/3}.$$
Dividing both sides by $(n+1)^{(1+\varepsilon)/3}$:
$$(n+1)^{(2-\varepsilon)/3} \leq K_\varepsilon \cdot n^{(1+\varepsilon)/2}.$$
Since $n+1 > n$, this gives $n^{(2-\varepsilon)/3 - (1+\varepsilon)/2} \leq K_\varepsilon$. The exponent is
$$\frac{2-\varepsilon}{3} - \frac{1+\varepsilon}{2} = \frac{1 - 5\varepsilon}{6},$$
which is positive for any $\varepsilon < 1/5$. So $n^{(1-5\varepsilon)/6} \leq K_\varepsilon$, hence $n \leq K_\varepsilon^{6/(1-5\varepsilon)}$. This bounds $n$ explicitly, so only finitely many such pairs can exist. $\square$
This appears to be a new observation; I could not find it stated in the existing literature, although adjacent problems also admit abc-conditional finiteness results. 
This observation was identified with AI assistance (an automated research pipeline exploring unconditional approaches to this problem, which eventually pointed towards the abc conjecture as a natural approach). The calculation above has been independently verified.
(The site has been updated to address this comment.)
 DavidTurturean
 — 22:00 on 14 Apr 2026
 👍
 2
 📝
 0
 🤖
 0
 Congrats. I ran standard check which confirmed this as correct, but the result *could* be folklore. For example, Aktaş and Murty has connected the abc conjecture to the quantities $S_d(N) := \#\{ n \le N: n, n+d \text{ are squarefull} \}$, although we did not find the exact literature connection of abc to consecutive $2$-full and $3$-full numbers.
 Nat Sothanaphan
 — 18:11 on 15 Apr 2026
 👍
 0
 📝
 0
 🤖
 0
 Wonderful! Can we obtain directly an explicit upper bound for $n$, even if massively large? For example, by using this paper?
 marinov
 — 23:42 on 14 Jul 2026
 👍
 0
 📝
 0
 🤖
 0

## Proof claims page
There is 1 proof claim (partial or full) for this problem.
 Appearing on this page is no guarantee of proof correctness, and does not mean that anyone associated with this site has examined any part of the proof.
 Submit your own proof claim
A proof 
claimed by Theofil Xeff (using GPT 5.6 Sol high, Fable 5 high).
 Summary:
 Assuming Baker’s explicit $abc$ conjecture, I prove that any $2$-full integer $n$ followed by a $3$-full integer $n+1$ must satisfy
$$n<10^{16136778163}.$$
This does not solve the problem, but it turns David Turturean’s earlier observation that $abc$ implies finitely many solutions into a concrete upper bound.
The intuition is that $2$-full and $3$-full numbers have unusually few distinct prime factors compared with their size. Thus the product of the distinct primes dividing $n(n+1)$ is much smaller than $n+1$. The $abc$ conjecture says that this cannot happen in the equation $n+1=(n)+1$ once $n$ becomes too large. Making that comparison explicit using Baker’s version of $abc$, together with estimates for prime factors and factorials, gives the bound above.
 Notes:
 The proof was fully developed by GPT 5.6 Sol high and formally verified in Lean using Fable 5 high and GPT 5.6 Sol high.
| 
 External link to proof
 |
 External link to formalisation
 |
 Submitted 2026-07-22 08:23:38 by 
 fefemath
 ▶
 Comments (1)