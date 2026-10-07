# erdosproblems.com #677: problem page and forum thread (fetched 2026-10-06T16:07:43Z)

Comments are unverified; several withdraw earlier claims.

## Page


## Forum comments
Order by
 oldest first or
 newest first. (The most recent comments are highlighted in a red border.)
 Additional examples for the variable-(k) equation M(n,k)=M(m,l):
M(8,4)=M(43,2)=1980 and M(153,3)=M(1363,2)=1,861,860
Also the known (420)-example has padded repeats
M(0,7)=M(1,6)=M(2,5)=M(3,4)=M(19,2)=420
 qrdl
 — 22:59 on 02 Apr 2026
 👍
 1
 📝
 0
 🤖
 0
 Here are some Aristotle formalizations and a high level walkthrough of the lean code by gpt5.4 This work was made with assistance from GPT5.4, Aristotle, and Gemini Pro 3.1
I also found this paper by Bakir FARHI and Daniel KANE which may be of interest.
 qrdl
 — 16:46 on 31 Mar 2026
 👍
 0
 📝
 0
 🤖
 0
 Thanks. I looked. The repo is likely too basic to attack the problem. The most interesting result is finiteness given fixed $d, k$, which is weaker than the Thue-Siegel result in the problem description. The proof of this is just that $M(n,k) = M(n+d,k)$ implies $n+1 \mid d(d+1)\cdots(d+k-1)$ (!).
I think your GPT may have some sycophancy problem. For example, this finiteness result is described in your chat like so:
"This is a big clue about how the project can close branches. Even if a proof does not fully solve Erdős 677 in one shot, any argument that gives a good bound on $d$, or reduces candidate $d$'s to a finite set, immediately converts the remaining work into a finite verification problem. So an outsider interested in rigorous computation can contribute by proving sharper bounds on $d$ or on bridge-slot occupancy."
which is a completely different sentiment from what it actually is.
Credit to GPT-5.4 Thinking for discussion (not shared here because some parts are too opinionated).
 Nat Sothanaphan
 — 18:23 on 31 Mar 2026
 👍
 0
 📝
 0
 🤖
 0
 Spend some real time on the problem, it's worth it and pretty interesting. I like the idea of signatures for disjoint sequences of integers. I can imagine some uses outside number theory.
 qrdl
 — 19:49 on 31 Mar 2026
 👍
 0
 📝
 0
 🤖
 0
 I am serious. To elaborate, this does not qualify to be on the AI wiki (which does not have a particular high bar), so I did not add it. Also, I am not sure what "uses outside of number theory" could be.
 Nat Sothanaphan
 — 19:59 on 31 Mar 2026
 👍
 0
 📝
 0
 🤖
 0
 What is the 'ai wiki'?
 qrdl
 — 20:17 on 31 Mar 2026
 👍
 0
 📝
 0
 🤖
 0
 It's the wiki you're interested in the your very first comment here. I won't further answer questions here; you can DM me though.
 Nat Sothanaphan
 — 20:24 on 31 Mar 2026
 👍
 0
 📝
 0
 🤖
 0
 No, that's fine. If you were referring to Tao's wiki, it honestly never occurred to me. I am just interested in the problem.
 qrdl
 — 20:37 on 31 Mar 2026
 👍
 0
 📝
 0
 🤖
 0