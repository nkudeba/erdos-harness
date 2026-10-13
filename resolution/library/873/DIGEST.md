# erdosproblems.com #873: problem page and forum thread (fetched 2026-10-08T19:26:22Z)

Comments are unverified; several withdraw earlier claims.

## Page


## Forum comments
Order by
 oldest first or
 newest first. (The most recent comments are highlighted in a red border.)
 I have submitted to Formal Conjectures a Lean-verified negative answer to the conjecture stated on this forum page: “There may be a sequence for which this holds for every $X$.” The submission is PR #5544.
The Lean formalization was prepared by Kenta Kitamura (KitaKen1).
GitHub: https://github.com/KitaKen1/erdos-873-lean
Formal Conjectures PR: https://github.com/google-deepmind/formal-conjectures/pull/5544
Lean4Web: open the standalone proof
Verification: no 'sorry' or 'admit'; '#print axioms' reports only 'propext', 'Classical.choice', and 'Quot.sound'.
AI Usage Disclosure: This formalization was developed with assistance from ChatGPT and OpenAI Codex, using GPT-6 (Astra).
 KentaKitamura
 — 09:45 on 11 Sep 2026
 👍
 0
 📝
 0
 🤖
 0
 It seems, Patrick Letendre has a paper (from before the AI-explosion), 
giving a positive (abstract) answer for all epsilon > 1/4:
https://arxiv.org/abs/2503.12146
eps = 1/4 seems to be a hard barrier.
 old-bielefelder
 — 04:17 on 30 Apr 2026
 👍
 2
 📝
 0
 🤖
 0
 Are you sure this paper has to do with #873? There does not seem to be any obvious relationship.
 TerenceTao
 — 05:31 on 30 Apr 2026
 👍
 0
 📝
 0
 🤖
 0
 I had a long chaotic session with ChatGPT 5.5 Thinking.
Somewhere in the middle the model wrote:
Quote:
> Letendre proves the essential divisor-clustering theorem; 
> the Erdo˝s–Szemereˊdi ϵ > 1/4 result is a short corollary 
> via packing.
> ​
> I would not say he literally wrote the proof of the Erdős–
> Szemerédi consequence, unless it appears elsewhere or in 
> a section I missed. His paper is framed around Dn(X,Y), 
> while the Erdős problem is the lcm-window problem F(A,X,k), 
> currently listed separately on Erdős Problems.
>
> But mathematically, yes: once one notices the packing reduction,
> Letendre’s Proposition 1 already gives the ϵ > 1/4 case.
And ChatGPT claimed to have noticed the packing reduction.
Here is link to ChatGPT's proof (in pdf): Click
When I saw the contribution by Ritvik Nayak, I thought there
should be a general result beyond special cases, and asked
ChatGPT to go for it. It came up with a proof based on Letendre's
paper and was able to repair it after some ciritcal question from
me. Then I tried at length to overcome the 1/4 barrier, but without 
success.
 old-bielefelder
 — 06:45 on 30 Apr 2026
 👍
 1
 📝
 0
 🤖
 0
 Congrats! Standard check found no issues in the writeup.
 Nat Sothanaphan
 — 15:41 on 30 Apr 2026
 👍
 1
 📝
 0
 🤖
 0
 Now I asked ChatGPT 5.6 Sol again for an elementary proof of the exponent $1/4$ $+$ $eps$, without using the 2025-result of Letendre. The model was successful:
Elementary Proof of Exponent 1/4 + eps for large k 
EDIT: Generalized Riemann Hypothesis does not 
help to achieve $1/4$ without epsilon or even better.
 old-bielefelder
 — 14:25 on 18 Aug 2026
 👍
 0
 📝
 0
 🤖
 0
 I would like to share my partial result on this problem.
This partial result proves two unconditional bounds that go beyond the usual triple-block exponent. In particular, it proves\[
F(A,X,11)\ll X^{223/676}\log X
\]and\[
F(A,X,6)\ll X^{437/1320}\log X.
\]Both exponents are strictly smaller than \(1/3\), so the result shows that the classical triple-block barrier can be crossed for longer consecutive blocks.
The main idea is to combine the Vandermonde lcm inequality with gcd structure forced inside compact near-critical blocks. Around the difficult scale \(a_i\asymp X^{1/2}\), a good block must contain substantial pairwise gcd structure. The argument organizes this information through incident-star and complete-edge configurations, which then give stronger span bounds and lead to the counting estimates above.
I view this as genuine partial progress on the problem, rather than a solution of the full \(X^\varepsilon\) question. I used GPT 5.4 Thinking for helping me with algebraic notation and verifying the contribution, and it passed. I would be very grateful for any corrections, comments, or references to related work that I may have missed.
 Ritvik Nayak
 — 07:10 on 29 Apr 2026
 👍
 3
 📝
 0
 🤖
 0
 Gpt 5.5 pro found slightly better bounds
$F(A,X,6)≪X 
^{22/67}
 logX$
$F(A,X,8)≪X ^{19/58}
 logX
$
 aditya
 — 11:39 on 29 Apr 2026
 👍
 2
 📝
 0
 🤖
 0
 Congrats. Standard check claimed some minor issues in the writeup.
 Nat Sothanaphan
 — 14:46 on 29 Apr 2026
 👍
 2
 📝
 0
 🤖
 0
 [Post deleted]
 Unknown
 — 12:10 on 08 Oct 2025
 👍
 0
 📝
 0
 🤖
 0
 I have not checked any of the mathematical content of this post, but it has an 'AI-feel' to it, as do several of your other recent comments. I've started a discussion on what the AI-related policy and measures should be over on the Miscellaneous thread, which you are encouraged to contribute to.
 Thomas Bloom
 — 12:30 on 08 Oct 2025
 👍
 0
 📝
 0
 🤖
 0