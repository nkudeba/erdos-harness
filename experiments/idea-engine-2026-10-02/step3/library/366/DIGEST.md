# erdosproblems.com #366: problem page and forum thread (fetched 2026-10-06T16:07:18Z)

Comments are unverified; several withdraw earlier claims.

## Page


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