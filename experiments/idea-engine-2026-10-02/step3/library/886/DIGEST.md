# erdosproblems.com #886: problem page and forum thread (fetched 2026-10-06T16:08:28Z)

Comments are unverified; several withdraw earlier claims.

## Page


## Forum comments
Order by
 oldest first or
 newest first. (The most recent comments are highlighted in a red border.)
 Not a big issue but on page $358$ in EoRo97, asked the number of divisors in the $(\sqrt{n},\sqrt{n}+\sqrt{n}^{1-\varepsilon})$ interval.
An easy result on a wide range of $\varepsilon$: on $(\sqrt{n},\sqrt{n}+\sqrt[6]{n})$ interval we can not have three or more divisors.
Easily, if $d_{1},d_{2},d_{3}$ are divisors on this interval, then using inclusion exclusion principle the
$[1]:\quad \frac{d_{1}d_{2}d_{3}gcd(d_{1},d_{2},d_{3})}{gcd(d_{1},d_{2})gcd(d_{2},d_{3})gcd(d_{3},d_{1})}$ also divides $n$
Here $gcd(d_{1},d_{2}),gcd(d_{2},d_{3}),gcd(d_{3},d_{1})<\sqrt[6]{n}$, since for example $gcd(d_{1},d_{2})$ divides the $|d_{2}-d_{1}|<\sqrt[6]{n}$.
So using [1] and the above (strict) upper bounds, since the left side divides $n$ we get:
$n^{\frac{3}{2}-3\cdot\frac{1}{6}}<n$, it is a contradiction.
ps. after this asked chatgpt, and said that Imre Z. Ruzsa proved this in 2005 ( and behind journal paywalls ). Don't know what was his approach.
 RobertGerbicz
 — 21:08 on 31 Jan 2026
 👍
 0
 📝
 0
 🤖
 0
 Might there be a constant $c$ missing in the statement "Erdős and Rosenfeld [ErRo97] proved that there are infinitely many $n$ such that there are four divisors of $n$ in $(n^{1/2},n^{1/2}+n^{1/4})$."? From quickly looking at page 356 on https://eudml.org/doc/206983 it seems like it should be $(n^{1/2},n^{1/2}+cn^{1/4})$?
This was noticed in a pull request in attempting to formalise the problem: 
https://github.com/google-deepmind/formal-conjectures/pull/1942#discussion_r2749752508
The disproof there was found by AlphaProof
(The site has been updated to address this comment.)
 Moritz Firsching
 — 17:16 on 31 Jan 2026
 👍
 0
 📝
 1
 🤖
 0
 This indeed seems to be the case (with $c \approx 8$, although this is not stated explicitly). Proposition 4.1 of that paper also appears to be consistent with the AlphaProof result.
(The site has been updated to address this comment.)
 TerenceTao
 — 17:35 on 31 Jan 2026
 👍
 1
 📝
 1
 🤖
 0
 A recent formulation and discussion (including the case of intervals starting at $n^{1/2}$) appears as Conjecture~1 in Letendre's preprint https://arxiv.org/pdf/2503.12146. Letendre establishes upper bounds for\[
D_n(X,Y):=\#\{d\mid n:\ X\le d\le X+Y\}
\]in several parameter ranges and explains constraints on how a hypothetical uniform bound $k_\epsilon$ could depend on $\epsilon$ (in particular, it cannot stay small as $\epsilon\to 0$).
In particular, specializing Letendre's bounds to $\theta=\tfrac12$ yields a uniform estimate above the $n^{1/4}$ scale: for any $\delta\in(0,\tfrac14)$,\[
D_n\!\bigl(n^{1/2},\,n^{1/4-\delta}\bigr)\ \ll\ \frac1\delta
\]uniformly in $n$. Hence, if the interval length is $n^{1/2-\epsilon}$ with $\epsilon>\tfrac14$ (so $1/2-\epsilon=1/4-\delta$ where $\delta=\epsilon-\tfrac14>0$), one obtains\[
\#\{d\mid n:\ \sqrt n<d\le \sqrt n+n^{1/2-\epsilon}\}\ =\ O\!\left(\frac{1}{\epsilon-\tfrac14}\right),
\]i.e. the conjectured $O_\epsilon(1)$ bound is known for every $\epsilon>\tfrac14$. For $\epsilon\le\tfrac14$ the existence of a uniform bound remains open in general; at the endpoint $\epsilon=\tfrac14$, Erdős and Rosenfeld constructed infinitely many $n$ with four divisors in $(\sqrt n,\sqrt n+n^{1/4})$, showing any universal bound there (if true) must be at least $4$.
 Przemek Chojecki
 — 13:59 on 14 Jan 2026
 👍
 0
 📝
 0
 🤖
 0