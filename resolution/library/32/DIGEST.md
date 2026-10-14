# erdosproblems.com #32: problem page and forum thread (fetched 2026-10-10T14:57:35Z)

Comments and proof claims are unverified; several withdraw earlier claims.

## Page
$50
Is there a set $A\subset\mathbb{N}$ such that\[\lvert A\cap\{1,\ldots,N\}\rvert = o((\log N)^2)\]and such that every large integer can be written as $p+a$ for some prime $p$ and $a\in A$? 
Can the bound $O(\log N)$ be achieved? Must such an $A$ satisfy\[\liminf \frac{\lvert A\cap\{1,\ldots,N\}\rvert}{\log N}> 1?\]
#32: [Er56,p.132][Er57,p.295][Er59,p.117][Er61,p.229][Er65b,p.227][Er73,p.133][Er77c,p.62][Va99,1.9]
number theory | 
additive basis
Such a set is called an additive complement to the primes.
Erdős [Er54] proved that such a set $A$ exists with $\lvert A\cap\{1,\ldots,N\}\rvert\ll (\log N)^2$ (improving a previous result of Lorentz [Lo54] who achieved $\ll (\log N)^3$). 
Wolke [Wo96] has shown that such a bound is almost true, in that we can achieve $\ll (\log N)^{1+o(1)}$ if we only ask for almost all integers to be representable. Kolountzakis [Ko96] improved this to $\ll (\log N)(\log\log N)$, and Ruzsa [Ru98c] further improved this to $\ll \omega(N)\log N$ for any $\omega\to \infty$.
The answer to the third question is yes: Ruzsa [Ru98c] has shown that we must have\[\liminf \frac{\lvert A\cap\{1,\ldots,N\}\rvert}{\log N}\geq e^\gamma\approx 1.781.\]This is discussed in problem E1 of Guy's collection [Gu04], where it is stated that Erdős offered \$50 for determining whether $O(\log N)$ can be achieved.
Additional thanks to: Mark Sellke and Wouter van Doorn

## Forum comments
Order by
 oldest first or
 newest first. (The most recent comments are highlighted in a red border.)
 For the "almost all integers" case of the problem, the mentioned result of [Wo96] has been improved. Kolountzakis (On the additive complements of the primes and sets of similar growth; Acta Arith. 77 (1996), 1–8) showed an upper bound $O(\log(x)\log\log(x))$. A further improvement is in the paper [Ru98c] of Ruzsa mentioned already: Theorem 1 shows that one can achieve $O(\omega(x)\log x)$ for any function $\omega$ that diverges as $x\to\infty$.
Additionally, although Ruzsa confirms the third question, he notes that it remains unclear in the "almost all integers" setting, and leaves a few versions of this as conjectures.
(The reference was located by GPT-5.)
(The site has been updated to address this comment.)
 msellke
 — 00:38 on 13 Oct 2025
 👍
 0
 📝
 0
 🤖
 0