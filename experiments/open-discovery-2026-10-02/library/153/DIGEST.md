# erdosproblems.com #153: problem page and forum thread (fetched 2026-10-02T01:20:19Z)

Comments are unverified; several withdraw earlier claims.

## Page
OPEN
This is open, and cannot be resolved with a finite computation.
Let $A$ be a finite Sidon set and $A+A=\{s_1<\cdots<s_t\}$. Is it true that\[\frac{1}{t}\sum_{1\leq i<t}(s_{i+1}-s_i)^2 \to \infty\]as $\lvert A\rvert\to \infty$?
#153: [ESS94]
sidon sets
A similar problem can be asked for infinite Sidon sets.

## Forum comments
Order by
 oldest first or
 newest first. (The most recent comments are highlighted in a red border.)
 A partial result survives for asymptotically maximum Sidon sets (those with $\operatorname{diam}(A) = (1+o(1))|A|^2$). Corrected writeup at https://leon2k2k2k.github.io/erdos153_corrected.pdf.
The idea: by Pikhurko's uniformity lemma, an asymptotically maximum Sidon set is equidistributed in its ambient interval, which forces $A+A$ to have triangular density $\varphi(u) = \min(u, 1-u)$ in $[0, 2D]$. Near the boundary this density vanishes linearly, so $A+A$ is sparse and the gaps grow. A localization inequality (Cauchy–Schwarz on disjoint windows) turns this sparsity into a lower bound on $\sum d_i^2$: the contribution from the edge is a Riemann sum for $\int_\varepsilon^{1/2} du/u = \log(1/(2\varepsilon)) \to \infty$.
The case $\liminf \operatorname{diam}(A_n)/n^2 > 1$ remains open — Pikhurko uniformity requires asymptotic maximality. Found with the help of GPT-5.5 + Rethlas; verified by hand.
 leon2k2k2k
 — 00:13 on 20 May 2026
 👍
 1
 📝
 0
 🤖
 0
 Edit: The proof below is incorrect. Here is a short proof of the statement using the shifted-intersection bound $|(A+A) \cap (A+A+d)| \leq 2|A|^{3/2}$ that Bloom extracted from the proof of Theorem 2 of [ESS94] on the #152 forum thread. 
Write $A+A = {s_1 < \cdots < s_t}$, $d_i = s_{i+1}-s_i$, $n = |A|$, so $t = n(n+1)/2$. Fix $R \geq 1$. Each index $i$ with $d_i = d$ gives a distinct element $s_{i+1} \in (A+A) \cap (A+A+d)$, so summing the Bloom–ESS94 bound over $d \in \{1, \ldots, R\}$ yields $\#\{i : 1 \leq d_i \leq R\} \leq 2R\,n^{3/2} = o(t)$ as $n \to \infty$. Hence at least $(1-o(1))\,t$ gaps satisfy $d_i > R$, so $Q(A) \geq R^2(1-o(1))$; taking $R \to \infty$ gives $Q(A_n) \to \infty$. 
Writeup at https://leon2k2k2k.github.io/erdos153.pdf. Found with the help of GPT-5.5 + Rethlas; verified by hand.
---
 leon2k2k2k
 — 00:34 on 16 May 2026
 👍
 0
 📝
 0
 🤖
 0
 So by taking $R = c\sqrt{|A|}$ we get that the sum in question is $\gg |A|$.
 Woett
 — 08:11 on 16 May 2026
 👍
 1
 📝
 0
 🤖
 0
 This would be correct, except that the bound I claimed in [152] is extremely (and obviously!) false. See my recent comment in that thread.
 Thomas Bloom
 — 13:33 on 16 May 2026
 👍
 2
 📝
 0
 🤖
 0
 Thank you for catching this! I've pulled the old note.
 leon2k2k2k
 — 23:59 on 19 May 2026
 👍
 0
 📝
 0
 🤖
 0
 Not sure if this is interesting enough to comment, but this conjecture is immediate in the “very sparse relative to its span” regime, and does not use the Sidon property at all. Let $A$ be any finite set of integers, $|A|=k$, and write $A+A=\{s_1<\dots<s_t\}$ with gaps $d_i=s_{i+1}-s_i$. Let $D:=\operatorname{Diam}(A)=\max(A)-\min(A)$. Then $s_t-s_1=2D$. We have
$$\frac1t\sum_{i=1}^{t-1} d_i^2 \ge \frac{16D^2}{k^2(k+1)^2}$$
by Cauchy–Schwarz. In particular, if $D\gg k^2$ (e.g. for $A\subset[1,n]$ with $\operatorname{Diam}(A)\asymp n$ and $k=o(\sqrt n)$), then the mean square consecutive gap $\to\infty$.
 Sayan Dutta
 — 16:13 on 15 Feb 2026
 👍
 0
 📝
 0
 🤖
 0
 Interesting. I guess when you wrote $D\gg k^2$, you meant $D/k^2\to\infty$ as $k\to\infty$. Since dense Sidon sets with $k$ elements have diameter about $k^2$, one needs to exploit more about the structure of $A+A$.
 Steve Fan
 — 18:37 on 15 Feb 2026
 👍
 1
 📝
 0
 🤖
 0