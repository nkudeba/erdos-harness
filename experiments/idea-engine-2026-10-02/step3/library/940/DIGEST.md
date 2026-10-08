# erdosproblems.com #940: problem page and forum thread (fetched 2026-10-08T01:42:28Z)

Comments are unverified; several withdraw earlier claims.

## Page


## Forum comments
Order by
 oldest first or
 newest first. (The most recent comments are highlighted in a red border.)
 Why is density $0$ 'easy' for $r = 2$? I know that Erdős claims this in the referenced paper, but for us mere mortals?
 Woett
 — 17:07 on 14 Oct 2025
 👍
 0
 📝
 0
 🤖
 0
 I believe it is more like classic than easy, in the sense that you probably could mimic the proof of Edmund Landau that set of numbers that are sums of two squares have density zero to prove the corresponding result here.
 Dogmachine
 — 17:36 on 14 Oct 2025
 👍
 0
 📝
 0
 🤖
 0
 I've been thinking, but I don't see anything easy. Even adapting Landau's proof is not obvious - what are the prime obstructions here? And given the negative solution to [1081] it can't be as simple as primes congruent to 3 mod 4.
 Thomas Bloom
 — 17:42 on 14 Oct 2025
 👍
 0
 📝
 0
 🤖
 0
 Presumably the references listed in #1081 answer this question?
 TerenceTao
 — 03:53 on 24 Oct 2025
 👍
 0
 📝
 0
 🤖
 0
 Blomer and Granville [BlGr06] does.
 StijnC
 — 04:25 on 24 Oct 2025
 👍
 0
 📝
 0
 🤖
 0
 Yes sorry, should have clarified - this is certainly known, and I believe was first proved by Baker and Brüdern [BaBr94]. Their proof was an application of the large sieve.
I meant that I'm not sure what the 'easy' proof of just zero density was that Erdős had in mind. Maybe it was something like this.
(I'll update the remarks to represent this.)
 Thomas Bloom
 — 05:02 on 24 Oct 2025
 👍
 0
 📝
 0
 🤖
 0
 OK, here is an "easy" proof. A powerful number is a product of a square and a cube, so one is asking to count $n \leq x$ of the form $n = c^3 a^2 + d^3 b^2$ for some $a,b,c,d$. This forces $a = O(x^{1/2}/c^{3/2})$ and $b = O(x^{1/2}/d^{3/2})$, so for any fixed $c,d$ the number of such $n$ is $O(x / c^{3/2} d^{3/2})$. This converges in $c,d$, so to get zero density one can restrict attention to the bounded case $c,d=O(1)$ (dominated convergence). But then one is essentially in the sum of two squares case (in a suitable number field).
Disclosure: I also tried asking ChatGPT Pro about this, but it confidently gave a hopelessly wrong answer (key error: assuming one could upper bound a ratio by upper bounding the denominator). These tools still focus too much on getting arguments that *look* right, and lack the sense of "smell" that their argument is going awry.
 TerenceTao
 — 14:19 on 24 Oct 2025
 👍
 1
 📝
 0
 🤖
 0
 Small typo i forgot. What Erdos claimed follows from a simple counting argument, is that NOT all large integers are the sum of at most $r$ $r$-powerful numbers.
(The site has been updated to address this comment.)
 Dogmachine
 — 13:37 on 14 Oct 2025
 👍
 0
 📝
 0
 🤖
 0