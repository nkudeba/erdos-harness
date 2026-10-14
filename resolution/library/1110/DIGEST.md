# erdosproblems.com #1110: problem page and forum thread (fetched 2026-10-14T22:12:05Z)

Comments are unverified; several withdraw earlier claims.

## Page


## Forum comments
Order by
 oldest first or
 newest first. (The most recent comments are highlighted in a red border.)
 Let $f(n)$ be the largest integer such that every integer $N \ge n$ can be written as a sum of distinct $3$-smooth integers, all larger than $f(n)$, and such that no two distinct elements divide each other. Then the remarks mention somewhat recent bounds on $f(n)$ by Yu-Chen and Yang-Zhao. However, essentially optimal bounds were already obtained back in $1998$ by Blecksmith, McCallum and Selfridge. 
R. Blecksmith, M. McCallum, J.L. Selfridge, 3-smooth representations of integers. The American Mathematical Monthly, Volume 105, No. 6, 529–543, 1998.
You can find their paper here. In particular, their Theorem $2$ states that every integer larger than or equal to $$2 \sum_{2^a3^b \le m} 2^a 3^b$$can be written as a sum of distinct $3$-smooth integers, all larger than $m$, and such that no two distinct elements divide each other. On the other hand, every such way of writing the integer $$2 \sum_{2^a3^b \le m} 2^a 3^b - 1$$contains an element smaller than or equal to $m$.
If I'm not mistaken, this gives $$f(n) = \left(\frac{\log 2 \log 3}{2} + o(1) \right) \frac{n}{\log n}.$$
(The site has been updated to address this comment.)
 Woett
 — 15:15 on 10 Mar 2026
 👍
 0
 📝
 2
 🤖
 0
 The statement should be 'Yu and Chen [YuCh22] prove that the set of representable numbers has density zero...'
instead of 'non-representable numbers'.
(The site has been updated to address this comment.)
 Adenwalla
 — 19:49 on 08 Dec 2025
 👍
 0
 📝
 1
 🤖
 0
 There is a paper 'A conjecture of Yu and Chen related to the Erdős–Lewin theorem' by Quan-Hui Yang and Lilu Zhao in Acta Arithmetica 217 (2025) which proves that there is a constant $c>0$ such that one can take $f(n)\gg\frac{cn}{\log n}$. A result in Yu and Chen's paper shows that this optimal up to the constant.
The Yu and Chen paper also proves that there are infinitely many coprime non-representable numbers when $\{p,q\}\neq \{2,3\},\{2,5\},\{2,9\},\{3,5\}$.
(The site has been updated to address this comment.)
 Adenwalla
 — 17:14 on 07 Dec 2025
 👍
 0
 📝
 1
 🤖
 0
 who proved that there are infinitely many non-representable numbers if and only if ...
probably should be
who proved that there are finitely many non-representable numbers if and only if
(The site has been updated to address this comment.)
 StijnC
 — 14:03 on 07 Dec 2025
 👍
 0
 📝
 0
 🤖
 0