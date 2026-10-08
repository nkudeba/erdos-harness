# erdosproblems.com #486: problem page and forum thread (fetched 2026-10-08T01:42:22Z)

Comments are unverified; several withdraw earlier claims.

## Page


## Forum comments
Order by
 oldest first or
 newest first. (The most recent comments are highlighted in a red border.)
 Is the statement correct as written, as GPT-5.2 claims to have a solution assuming there isn't some "activation threshold" like “n < n_i or avoid a residue class” similar to [25]?
 Liam Price
 — 17:08 on 11 Jan 2026
 👍
 2
 📝
 0
 🤖
 0
 On inspection of [Er61, p.236] there is indeed an "activation threshold" condition ($b \geq a_i$ in (I.26.1) of that paper, or one should replace "$m \notin X_n \pmod{n}$" with "$m<n$ or $m \notin X_n \pmod{n}$" in the current formulation) that is currently absent, and as GPT-5.2 claims, without this condition one can easily create sparse congruence conditions that occasionally disrupt the logarithmic density and provide a cheap negative answer to the question as currently stated.
EDIT: As a side note, I am glad that the discussion of AI-generated solutions on this site is maturing from just focusing on whether an Erdos problem as literally stated on this web site was solved by the AI tool, to also addressing more holistic questions of whether the statement proven was actually in the spirit of what Erdos was intending, and what the natural variants of that statement are and how they connect with the rest of the literature. (In particular I hope we resist efforts to "benchmax" the number of solved problems on this site at the expense of understanding the broader context of these problems.)
(The site has been updated to address this comment.)
 TerenceTao
 — 17:42 on 11 Jan 2026
 👍
 7
 📝
 1
 🤖
 0
 Got it, thanks for the insight.
 Liam Price
 — 17:48 on 11 Jan 2026
 👍
 0
 📝
 0
 🤖
 0
 On the edit, thanks! This is something I’m personally strongly advocating for as well. Me and Leeham are sure to ask if conditions seem off if the problem is quickly solved by GPT or if it claims for itself that there is likely something missing :)
 Kevin Barreto
 — 17:59 on 11 Jan 2026
 👍
 2
 📝
 0
 🤖
 0
 So is [25] the same as this question with the restriction that $|X_n|=1$ for all $n\in A$?
 Adenwalla
 — 18:58 on 11 Jan 2026
 👍
 1
 📝
 0
 🤖
 0
 If I understand both statements correctly I think that’s correct.
 Nat Sothanaphan
 — 21:37 on 11 Jan 2026
 👍
 0
 📝
 0
 🤖
 0
 [DaEr36] is not able to load any reference.
(The site has been updated to address this comment.)
 Alfaiz
 — 12:05 on 23 Nov 2025
 👍
 0
 📝
 1
 🤖
 0
 Some not so very deep thoughts: first, if this is true for a collection of sets $X_n$, then it is also true for the collection of their complements. Second, for finite sets $A = \{a_1, a_2, \ldots, a_k\}$, this reduces to the case $|A| = 1$ with the single element in $A$ taken to be the least common multiple of the $a_i$. In this case $B$ even has a natural density. Third, since it is known for $X_n = \{0\}$, it is also true for $X_n = \{c\}$ for any $c \in \mathbb{N}$. Finally, the logical next step would be to consider what happens if $|X_n| = 1$ for all $n$ and $X_n \subset X$ for some finite set $X$. Perhaps this isn't too difficult either.
 Woett
 — 17:54 on 16 Oct 2025
 👍
 0
 📝
 0
 🤖
 0