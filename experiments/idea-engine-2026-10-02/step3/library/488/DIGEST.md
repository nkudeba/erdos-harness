# erdosproblems.com #488: problem page and forum thread (fetched 2026-10-06T16:07:31Z)

Comments are unverified; several withdraw earlier claims.

## Page


## Forum comments
Order by
 oldest first or
 newest first. (The most recent comments are highlighted in a red border.)
 A small addition to the existing remark about the [Er61] typo: the same slip appears in [Er80] as well.
On p.112 of [Er80], $B$ is defined as "the sequence of integers no one of which is the multiple of any of the $a$'s", which is the $a \nmid n$ reading, and the sharpness example given immediately afterwards ("The $a$'s consist only of $a_1$, $n = 2a_1 - 1$, $m = 2a_1$") only works for the multiples reading. With $A = \{a\}$, the multiples set gives $B(2a)/2a = 1/a$ against $B(2a-1)/(2a-1) = 1/(2a-1)$, a ratio of $2 - 1/a$; the non-multiples set gives a ratio below $1$, which witnesses nothing.
So both English sources carry the typo and only the Hungarian [Er66] has it right, where p.150 reads "legalabb egy a-nak tobbszorosei", multiples of at least one $a$. Guy's E5 is likewise titled "Sequence with members divisible by at least one of a given set".
Checked against the scans at users.renyi.hu/~p_erdos: 1961-22.pdf p.236, 1966-20.pdf p.150, 1980-03.pdf p.112.
Separately, and possibly more useful: [Er66] p.150 records a partial result that does not appear here. Erdos notes there is no constant $\alpha > 0$ with $B(m)/m > \alpha B(n)/n$ for all such sequences, taking the $a$'s to be the integers in $(n/2, n]$ and $m$ large, citing his own JLMS 10 (1935), 126-128.
 thebrockchain
 — 18:34 on 27 Aug 2026
 👍
 1
 📝
 0
 🤖
 0
 Here is a small observation on the corrected “multiples” version of #488. It may already be known, but I did not see it stated explicitly in the thread.
Let\[
F_A(x)=|\{1\le t\le x:\ a\mid t\text{ for some }a\in A\}|.
\]I claim that the conjectured inequality holds when \(A\) has two elements.
Write \(A=\{a,b\}\), where \(2\le a<b\). First suppose \(a\nmid b\). Then \(b\) is counted and is not a multiple of \(a\), so for every \(n\ge b\),\[
F_A(n)\ge \lfloor n/a\rfloor+1\ge (n+1)/a.
\]On the other hand \(F_A(m)\le m/a+m/b<2m/a\), and hence\[
\frac{F_A(m)}{m}<\frac{2}{a}\le \frac{2F_A(n)}{n+1}<\frac{2F_A(n)}{n}.
\]If \(a\mid b\), then the counted set is just the multiples of \(a\), so \(F_A(x)=\lfloor x/a\rfloor\). Since \(n\ge b\ge 2a\), we have \(\lfloor n/a\rfloor\ge2\). Thus\[
2mF_A(n)-nF_A(m)
\ge m\left(2\lfloor n/a\rfloor-\frac{n}{a}\right)>0,
\]which gives the desired strict inequality.
So #488 holds for every two-element set \(A\).
The near-sharp examples are already visible here: for \(A=\{a,a+1\}\), \(n=2a-1\), and \(m=a^2\),\[
\frac{F_A(m)/m}{F_A(n)/n}
=
\frac{(2a-1)^2}{2a^2},
\]which tends to \(2\) from below. This leaves the first genuinely nontrivial case at primitive sets of size at least \(3\), where the overlaps between multiple sets start to matter.
AI-usage disclosure: I found this while working with Codex/ChatGPT-style tools
 Will Blair
 — 02:15 on 06 Jun 2026
 👍
 0
 📝
 0
 🤖
 0
 For the split-core tripod family $A=\{2u,3v,uv\}$ with $\gcd(u,v)=1$, $v\geq 3$ odd, $u\geq 4$, and $3\nmid u$, EP-488 holds: $B_A(n,m) := 2m\,F_A(n) - n\,F_A(m) > 0$ for all integers $m > n \geq uv$. This includes every prime witness tripod $\{2p,3q,pq\}$ with distinct odd primes $p,q>3$. The family is primitive but not $2$-primitive, since $uv$ divides $(2u)(3v)$; a first-pass literature search located no explicit prior treatment of this exact family.
Note (PDF, 5 pages): note
Prepared with 5.5 Pro; the math has been verified by hand and by an independent audit script.
 MalekZ
 — 20:06 on 30 Apr 2026
 👍
 0
 📝
 0
 🤖
 0
 One notable thing about this problem - unusual for an Erdos problem - is that there are several ways to make the problem easier to prove, yet the problem remains difficult. For instance, here are four ways to reduce the difficulty level:
 Take the asymptotic limit $m \to \infty$.
 Take the asymptotic limit $\max(A) = o(n)$ (and perhaps replace $2$ by $(2+o(1))$ to be able to take advantage of this).
 Replace the factor $2$ by an unspecified constant $C$.
 Assume that $A$ consists entirely of primes.
What I find remarkable is that even when enabling multiple of these "cheats", the problem is still nontrivial. I can resolve the problem with Cheats 1, 3, and 4 enabled: that is to say I can show that
$$ \lim_{m \to \infty} \frac{|B \cap [1,m]|}{m} \ll \frac{|B \cap [1,n]}{n}$$
when $A$ consists entirely of primes. Here the left-hand side is $1 - \prod_{p \in A} (1-\frac{1}{p})$. When $\sum_p \frac{1}{p}$ is small the right-hand side is $\asymp \sum_p \frac{1}{p}$ by the Bonferroni inequalities, and then when $\sum_p \frac{1}{p}$ is large the RHS is $\asymp 1$ by monotonicity, so in either case thed claim follows. But I don't see a way to prove this version in a way that suggests how to remove more of the cheats.
 TerenceTao
 — 00:24 on 06 Apr 2026
 👍
 3
 📝
 0
 🤖
 0
 Progress on EP-488: \(a=2\) case proved, Chojecki reduction fails for \(a\geq3\)
Some results on the density-doubling conjecture, building on the pair-tail decomposition framework from Conjecture 4.8.
1. The \(a=2\) case. For every primitive set \(A\) with \(2 \in A\) (equivalently, \(\min(A)=2\)), the conjecture holds.
Since every element of \(A\) is \(\geq 2\), integer 1 is never counted, so \(F(m) \leq m-1\) and \(F(m)/m < 1\) for all \(m\).
If \(A \neq \{2\}\), choose \(b \in A \setminus \{2\}\). Since \(A\) is primitive and \(2 \in A\), this \(b\) is necessarily odd. For \(n \geq b\):\[
F(n) \geq \left\lfloor \frac{n}{2} \right\rfloor + \left\lfloor \frac{n}{b} \right\rfloor - \left\lfloor \frac{n}{2b} \right\rfloor = \left\lfloor \frac{n}{2} \right\rfloor + \#\{\text{odd multiples of } b \leq n\} > \frac{n}{2}.
\]Therefore \(2F(n)/n > 1 > F(m)/m\).
For the singleton \(A = \{2\}\): \(F(k) = \lfloor k/2 \rfloor\), so for all \(m > n \geq 2\),\[
\frac{2F(n)}{n} = \frac{2\lfloor n/2 \rfloor}{n} > \frac{1}{2} \geq \frac{\lfloor m/2 \rfloor}{m} = \frac{F(m)}{m}.
\]This covers all primitive sets with \(2 \in A\).
**2. The Chojecki reduction fails for \(a \geq 3\).** The reduction to a fixed threshold \(s\) (first integer with \(F(s) \geq 5\)) does not extend to \(a \geq 3\). Counterexample family:
For any \(a \geq 3\), take \(b = 5a+1\) and \(T = \{t \in \mathbb{Z} : 5a+1 < t \leq 10a+1,\; a \nmid t\}\). Then \(A = \{a,b\} \cup T\) is primitive: every element of \(\{b\} \cup T\) lies in \((5a,\, 10a+1]\), so each exceeds \((10a+1)/2\) and no two can divide each other; and \(a\) divides none of them by construction.
The first \(s\) with \(F(s) \geq 5\) is \(s = 5a\), since below \(5a\), only multiples of \(a\) contribute and there are exactly 4 of them (\(a, 2a, 3a, 4a\)). So \(F(s) = 5\) and \(2F(s)/s = 2/a\).
At \(m = 10a+1\): every integer in \([5a+1,\, 10a+1]\) is counted by \(A\) (divisible by \(a\) \(\to\) counted; not divisible by \(a\) \(\to\) in \(T\) or equals \(b\) \(\to\) counted). So \(F(10a+1) = 5 + (5a+1) = 5a+6\), giving\[
\frac{F(m)}{m} = \frac{5a+6}{10a+1} > \frac{2}{a} = \frac{2F(s)}{s}
\]since \(5a^2 - 14a - 2 > 0\) for all \(a \geq 3\).
Concrete: \(a=3\), \(A = \{3,16,17,19,20,22,23,25,26,28,29,31\}\), \(F(31)/31 \approx 0.677 > 2/3\).
Note: this does NOT disprove EP-488, since \(s = 5a < \max(A) = 10a+1\), so the counterexample lies outside the valid range \(n \geq \max(A)\).
3. What remains. The original EP-488 statement (all \(m > n \geq \max(A)\)) is checked computationally across 25,000+ primitive systems with zero failures and margins \(\geq 33\%\) (defined as \((2F(n)/n - F(m)/m) / (2F(n)/n)\) for the tightest \((n,m)\) pair). The reduction to sieve oscillation still works within the \(n \geq \max(A)\) regime, where the key inequality becomes: for any finite \(Q \subset \mathbb{Z}_{\geq 2}\) and \(x \geq \max(Q)\), is \(A_Q(x) < 2\delta_Q x\)?
For pairwise coprime \(Q\), Hall–Hildebrand type bounds on the complementary unsieved count operate at an \(e^\gamma\)-scale; translating that into the form \(A_Q(x) < 2\delta_Q x\) requires care. For non-coprime \(Q\), computational evidence shows strictly smaller oscillation — the lcm lattice produces 30–70% coefficient cancellation in the inclusion-exclusion.
 MalekZ
 — 21:13 on 31 Mar 2026
 👍
 0
 📝
 0
 🤖
 0
 The commentary gives an example where $A$ is a singleton of size around $n/2$, and the ratio is close to 2. There is a somewhat different example where $A$ now consists of numbers much smaller than $n$, and the ratio is about 1.03; nowhere near a counterexample, but still uniformly bounded away from 1, and indicative of the complexity of the problem.
The counterexample comes from taking $A$ to be the primes between $n^{1/3}$ and $n^{1/2}$, and $m$ to be extremely large compared to $n$. The density at $m$ is then about $1 - \prod_{n^{1/3} < p < n^{1/2}} (1-\frac{1}{p})$, which by Mertens' theorem is about $1/3 = 0.333\dots$. The density at $n$ can be computed by inclusion-exclusion to be about $\sum_{n^{1/3} < p < n^{1/2}} 1/p - \sum_{n^{1/3} < p_1 < p_2 < n^{1/2}} 1/p_1 p_2$ which computes to $\log(3/2) - \frac{1}{2} \log^2(3/2) = 0.32326413$. The ratio here is $1.03114853\