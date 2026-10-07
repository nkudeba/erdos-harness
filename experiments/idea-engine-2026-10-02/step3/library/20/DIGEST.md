# erdosproblems.com #20: problem page and forum thread (fetched 2026-10-06T16:06:48Z)

Comments are unverified; several withdraw earlier claims.

## Page


## Forum comments
Order by
 oldest first or
 newest first. (The most recent comments are highlighted in a red border.)
 This conjecture has been proved for families of bounded VC-dimension in [GWXZ26] by G. Ge, J. Wang, Z. Xu and X. Zhao.
 Alfaiz
 — 04:43 on 17 Sep 2026
 👍
 0
 📝
 1
 🤖
 0
 The sunflower conjecture (and a certain homological approach to it) was the subject of polymath15. It is a subject of a recent AI+ Math polymath project here: https://gilkalai.wordpress.com/projects/the-sunflower-conjecture/
 GilKalai
 — 08:30 on 17 Jul 2026
 👍
 0
 📝
 0
 🤖
 0
 Is there a dedicated collaboration webpage towards this project? It seems that no one is able to comment on the page you linked.
 jleng01
 — 19:54 on 17 Jul 2026
 👍
 0
 📝
 0
 🤖
 0
 I'd be happy to host a blog post here for which the comment section could serve as an informal collaboration space (since most polymath projects have mainly taken place in the comment sections of blogs anyway, and maybe there are a few more features available here than the standard WordPress comment section).
Gil, or anyone else, just let me know if you'd like to organise this.
 Thomas Bloom
 — 21:30 on 17 Jul 2026
 👍
 1
 📝
 0
 🤖
 0
 There is a reference that sheds some light on why this question might be very difficult, despite its harmless appearance. Namely, a paper by Noga Alon, Amir Shpilka, and Christopher Umans, titled "On Sunflowers and Matrix Multiplication", shows that this conjecture is not compatible with one in computer science asserting that multiplication of two $n×n$ matrices is possible in $n^{2+o(1)}$ time. Very strange, since both of them sound so plausible at first glance...
 Dogmachine
 — 12:32 on 30 Apr 2026
 👍
 1
 📝
 0
 🤖
 0
 This note grew out of extensive AI-assisted exploration over many sessions, numbering in the hundreds. AI contributed to the exploration of ideas, the synthesis of connections across intermediate results, proofs, and parts of the exposition. The mathematical claims I chose to record here, their final organization, and responsibility for any remaining errors are mine. I have done my best to ensure that the Lean formalizations and proofs are correct.
I’m posting a cleaned-up draft of a note on partial results for Erdős sunflower problem \#20. This is not a proof of the full exponential sunflower conjecture. Rather, the note isolates several exact reductions, solved model classes, and obstruction examples that seem worth separating from larger notes.
The main rigorous results I would currently foreground are as follows. First, there is an exact reduction to terminal kernels: if \(M_{\ker}(n,k)\) denotes the maximum size of a \(k\)-sunflower-free terminal family with edge sizes at most \(n\), then\[
M_{\ker}(n,k) \le M(n,k) \le (k-1)^n M_{\ker}(n,k).
\]Second, there is an exact trace recursion: for a support piece \(P\) of rank \(r\) in an \(m\)-uniform family \(\mathcal{G}\),\[
|\mathcal{G}| = \sum_{\tau \in \operatorname{Tr}_P^*(\mathcal{G})} |\mathcal{G} * \tau|,
\]and if the trace family is itself \(k\)-sunflower-free, then\[
|\mathcal{G}| \le f(r,k)\,f(m-r,k).
\]Third, several model classes are completely solved in this framework, including bounded-degree terminal kernels, degree-two kernels, and exact block products.
Fourth, there are fixed-alphabet transversal-code results, including an exact two-moment characterization of admissible \(5\)-columns over \(\mathbb{F}_5\), the value\[
F_{5,5}(2) = 16,
\]and an explicit construction showing\[
F_{4,4}(3) \ge 28 > 3^3.
\]Fifth, there are explicit obstruction families, including a zero-sum slice with all proper marginals uniform and a balanced multislice obstruction to naive positive-density box extraction.
From this, it seems that the exact preprocessing to terminal kernels is clean, several natural model classes are tractable, and some attractive inverse heuristics are genuinely false. What is missing is a global routing theorem forcing arbitrarily large terminal kernels either into one of the solved classes or into a profitable recursive decomposition.
I would especially appreciate overlap checks and references, particularly if any of the reductions, block-product results, obstruction examples, or small code-model values are already known in essentially this form. I would also appreciate criticism of the proofs or statements, as well as any other comments.
I also linked the GitHub/Lean companion repository. Formalization status varies by item and is summarized in the draft.
https://drive.google.com/file/d/11K2WF5dQEP92Syl3VVogswfrLudURJCL/view?usp=sharing
https://github.com/SamMausberg/lean-formalizations/tree/main/FormalConjectures/Problems/Erdos/E20
Note: In my quick posting of this, I noticed I need to re-verify that some of these theorems are not present in the literature, as this is a popular problem.
 sammausberg
 — 21:17 on 21 Apr 2026
 👍
 1
 📝
 0
 🤖
 0
 Thanks! I ran standard check which claimed 1 minor issue and assessed the contribution as plausibly new but modest.
 Nat Sothanaphan
 — 10:37 on 22 Apr 2026
 👍
 1
 📝
 0
 🤖
 0
 While working on Problem #857 I found the infrastructure also covers the uniform setting. Base cases f(1,3)=2 through f(6,3)=19 are formally certified in Lean 4. The conjecture statement ErdosProblem20 is formally defined. The general bound remains open.
Repo: https://github.com/SproutSeeds/sunflower-lean
*EDIT*
@Terrance Tao
Thank you for asking, happy to disclose fully.
The development was built collaboratively using intelligence systems, primarily OpenAI Codex (GPT-5.2, extra-high reasoning effort) via the Codex CLI, and Anthropic Claude (Opus 4.5 and 4.6) via the Claude CLI. When Codex 5.3 and Claude Opus 4.6 released on the same day, I migrated to both gradually over the following 24-48 hours and continued the work on the newer models.
Regarding the Aristotle references you noticed: early in the project I made one call to Aristotle to understand generally how it would lay out a Lean formalization. After seeing the general format, I took that as a starting point for the example files and then built everything else using Codex and Claude instead of the Aristotle API. The Aristotle files in the repo are those initial examples and nothing more. All substantive development was done with Codex and Claude.
Codex and Claude are web services and the models themselves are opaque. What was not opaque was the process around them. I operated a structured orchestration process manually throughout, with explicit theorem targets, explicit acceptance criteria, and explicit rollback on failure. All building and verification was done locally, running 'lake build' on my own machine rather than relying on any cloud-based verification service. This kept the iteration loop tight: generate a proof attempt, build locally, accept or reject within seconds, move to the next target. That local feedback cycle was a significant part of what made the monotonic discipline practical to enforce in real time.
The discovery process itself was also collaborative. Rather than arriving at theorem targets in isolation, I worked with the intelligence systems in an exploratory research mode first: discussing the mathematical landscape, identifying which lemmas were likely load-bearing, and understanding what the proof tree needed structurally before any Lean was written. The intelligence system would surface candidate directions, and I would evaluate them by asking more questions, to other intelligence systems and to myself. I am not separate from this process. I think of myself as a question-asking machine that happens to have good intelligence systems around it, always absorbing, always narrowing. The evaluation was not me sitting apart from the system doing mathematics independently. It was me as part of the system, using questions as the mechanism for narrowing toward a target. This adaptive layer is what guided the sequencing of proof passes. It did not generate results blindly. It nudged the direction of exploration based on what was already proved, what gaps remained, and what the most tractable next step looked like given the current state of the development.
The core discipline was a monotonic sorry-free machine: every commit was only accepted if 'lake build' passed with zero sorries. If a proof attempt introduced a sorry, the commit was rejected and rolled back. This meant the proof tree could only grow and never regress. No sorry was ever allowed to persist across a commit boundary.
The process worked like this: I would give the intelligence system a specific theorem target, it would produce a proof attempt, I would run the Lean kernel to verify it, and only accept it if it compiled sorry-free. The Lean kernel itself is completely independent of any intelligence system. It is the ground truth. The intelligence system generated candidates; the kernel decided validity. This separation was intentional and is the reason I trust the results.
I chose Lean specifically as the backbone to keep my system honest.
Over time th