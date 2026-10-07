# erdosproblems.com #951: problem page and forum thread (fetched 2026-10-06T16:08:33Z)

Comments are unverified; several withdraw earlier claims.

## Page


## Forum comments
Order by
 oldest first or
 newest first. (The most recent comments are highlighted in a red border.)
 This note by me+ChatGPT shows, for each $3 \le n \le 7$, existence of $n$ generators less than $p_n$, the $n$th prime, for a free multiplicative semigroup whose elements differ by at least $1$.
This is basically an operationalized version of Tao's probabilistic sketch in the comments.
By the Barreto-Price extension step, this shows that the inequality in the problem can fail for $x = 5-\varepsilon, 7-\varepsilon, 11-\varepsilon, 13-\varepsilon, 17-\varepsilon$ for small $\varepsilon > 0$. We think it can fail for arbitarily large $x$ but do not know how to prove.
 Nat Sothanaphan
 — 20:58 on 01 Feb 2026
 👍
 0
 📝
 0
 🤖
 0
 I+ChatGPT have obtained in this note that
$$ a_1 = 101/42 \approx 2.40, \quad a_2 = 367/103 \approx 3.56, \quad a_3 = 113/24 \approx 4.71 $$
generate a free multiplicative semigroup whose elements differ by at least $1$.
The approach here uses tools from computational Diophantine approximation, by Matveev + LLL reduction by de Weger.
By using the extension step in Barreto-Leeham, we can extend to an infinite sequence. Since $a_3 < p_3 = 5$, the primes are not everywhere minimal, which is the same version of the problem disproved by Barreto-Leeham. The eventually minimal version appears more difficult and cannot be directly tackled by this method.
 Nat Sothanaphan
 — 16:41 on 28 Jan 2026
 👍
 0
 📝
 0
 🤖
 0
 It occurs to me that a probabilistic construction, together with some brute force numerics, should also work here. Numerical trial and error should be able to generate intervals of values for candidate $a_i$ (e.g., to follow Nat's example, one could try $a_1 \in [2.40,2.41]$, $a_2 \in [3.56, 3.57]$, $a_3 \in [4.71, 4.72]$ which can be shown by interval arithmetic to avoid near-collisions $|\prod_i a_i^{k_i} - \prod_j a_j^{\ell_j}| < 1$ for all $k_i, \ell_j$ below a certain threshold, say $\sum_i k_i \log a_i \leq 50$ (I am taking a total guess with this threshold), regardless of where in the interval $a_1,a_2,a_3$ are (note that this also forces $\sum_j \ell_j \log a_j$ to be bounded by $50$ up to some negligible error). To handle the remaining cases when $\sum_i k_i \log a_i > 50$, one can try the probabilistic method, choosing $a_1,a_2,a_3$ randomly; the probability of a collision for any given $k_1,k_2,k_3,\ell_1,\ell_2,\ell_3$ should drop off exponentially in these parameters (in particular gaining a factor like $e^{-50}$ at some point) and so hopefully one can keep the total failure probability below 1, at which point one wins. On the one hand this is not as constructive an example as the other ones, but the numerical verification may be easier and so one might be able to explore what happens at other values of $x$ than $4.71$ or $10$.
EDIT: Ooh, I can set AlphaEvolve to work on this! I'll try it now.
SECOND EDIT (20 mins later): For the $x=7-\varepsilon = p_4-\varepsilon$ problem, AE has already produced the candidate
$$a_1 = 2.6728591026637005, a_2 = 3.733826126571687, a_3 = 4.841402115246144, a_4 := 5.999121968603969$$
which verifies the $1$-separation condition for all $\prod_{i=1}^4 a_i^{k_i} \leq e^{64.25}$ (this is about 230,000 numbers, or about $e^{12.34}$, so well below the threshold for the birthday paradox to trigger). I imagine almost any reasonable probabilistic analysis would show that some perturbation of this would show that one can break the inequality $\# \{ a_i \leq x\} \leq \pi(x)$ for $x=7-\varepsilon$ (or even $x=6$). It seems that counterexamples are in fact numerically plentiful.
THIRD EDIT: It may get significantly harder to produce counterexamples as $x$ increases by such probabilistic methods. Already the birthday paradox suggests that it will be hard to randomly produce $\ggg \sqrt{x}$ values of $a_i$ in $[1,x]$ whose pairwise products $a_i a_j$ are all $1$-separated, let alone $>\pi(x)$ many such values. Possibly a hybrid approach where one first finds a (log-)algebraic construction with good separation properties for small products, followed by a probabilistic perturbation to guarantee good separation for large products as well, may work.
FOURTH EDIT: Perhaps the theory of Sidon sets (and B_h[g] sets, etc.) can be used to provide good constructions?
 TerenceTao
 — 18:50 on 28 Jan 2026
 👍
 3
 📝
 0
 🤖
 0
 This seems perhaps most computationally promising among the 3 approaches. I’ll try to see if we can get $n$ generators below $p_n$ for a few small $n$ by this and will report back.
 Nat Sothanaphan
 — 08:55 on 30 Jan 2026
 👍
 1
 📝
 0
 🤖
 0
 Obtained $n$ generators below $p_n$ for each $3 \le n \le 7$! The case $n=7$ is becoming tricky to certify, so I choose to (arbitrarily) stop here.
Noteworthy: there are more details to work through than initially expected. Luckily, with the new GPT-based workflow, tried out for the first time here, we brought it to the finish line in 44 turns and more than 8 hours from GPT's side. If I were to work alone, it would've taken much longer (likely already abandoned).
Will write it up soon.
 Nat Sothanaphan
 — 21:52 on 31 Jan 2026
 👍
 2
 📝
 0
 🤖
 0
 After about 20 back-and-forth prompts of asking different GPT-5.2 Pro instances to come up with, and then double-check the argument the prior instance gave autonomously, Leeham managed to get GPT-5.2 Pro to disprove this essentially fully autonomously (his only involvement being to ask the previous instance to write a LaTeX prompt for an AI to fix the proof and passing that to the next instance, until nothing wrong was identified by the model). All credit goes to him for this one. It should be classified as a section 1(a) result assuming things are correct.
He asked that I have a look, and I personally think its construction is genuinely creative! Up to issues of floating point precision, it seems right and novel to me; I could not locate any prior resolution in the literature. We are waiting for Aristotle to come back with a formalisation, but in the meantime, I would appreciate others having a look here.
 Kevin Barreto
 — 20:20 on 27 Jan 2026
 👍
 5
 📝
 0
 🤖
 0
 Congratulations to Leeham! 
Questions out of curiosity:
* How long took the 20 rounds of pingpong?
* May Leeham provide either the 20 pdfs to give us a full impression or at least some proper diagrams showing the amounts of progress in each round? One diagram might show the thinking times of 5.2 in the different rounds.
* At which step was he sure to be "winning"?
 old-bielefelder
 — 20:34 on 27 Jan 2026
 👍
 2
 📝
 0
 🤖
 0
 Thanks for the kind words! I will be able to provide the chat links to each instance and I can potentially create a diagram showing what the workflow looked like, I will just wait for the formalisation to be finished.
Obviously they will be shown in the chat links, but the thinking times ranged from probably 50 to 100 minutes and took me around 2 - 3 days from start to finish. As Kevin noted, I myself didn't instruct 5.2 Pro to do anything other than what the other instances of 5.2 Pro believed needed to be fixed, so this is still essentially autonomous.
 Liam Price
 — 20:44 on 27 Jan 2026
 👍
 2
 📝
 0
 🤖
 0
 Didn't you sometimes have connection losses in these long thinking periods (50 - 100 minutes)? I even get them rather often in 10-20 minutes "processes".
 old-bielefelder
 — 20:50 on 27 Jan 2026
 👍
 0
 📝
 0
 🤖
 0
 That was the case for GPT-5.2 Thinking, but Leeham has since been given access to GPT-5.2 Pro, which is much more stable over long periods. Ever since the release of GPT-5.1, the Thinking model often times out after 15 minutes, and nothing has been done to fix this... only GPT-5 Thinking remains stable in this way for the non-Pro models.
 Kevin Barreto
 — 20:54 on 27 Jan 2026
 👍
 1
 📝
 0
 🤖
 0
 Very rarely; since using GPT-5.2 Pro on my personal account, I have had maybe 1 or 2 timeouts out of the probably 80-100 prompts, and because of the difficulty of the problems, it consistently thought for quite a while (perhaps maybe 1 or 2 instances of the 20 thought for 30 - 40 minutes).
 Liam Price
 — 20:55 on 27 Jan 2026
 👍
 1
 📝
 0
 🤖
 0
 This is perhaps the most complex arrangement of autonomy so far. Intuitively, it does speak to a real fundamental barrier in research: ideas take time to build, so it is inherently difficult for a single (say 90-minute) session to settle a big problem. Hence, one must find a way to "scale up" thinking time while still maintaining progress. In any case, congrats!
 Nat Sothanaphan
 — 20:58 on 27 Jan 2026
 👍
 2
 📝
 0
 🤖
 0
 Yes, I think this speaks to a difference in methodology: one-shot attempts are unlikely to succeed currently, leading to large databases of LLM attempts on all the Erdos problems being essentially full of entirely incorrect attempts. It is clear from this case that persistence is vital.
 Kevin Barreto
 — 21:02 on 27 Jan 2026
 👍
 0
 📝
 0
 🤖
 0
 Hmm, this looks like a nice idea, but if I'm reading it right it just disproves it for $x=10$? So this construction of a