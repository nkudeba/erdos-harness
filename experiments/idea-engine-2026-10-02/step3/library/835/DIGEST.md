# erdosproblems.com #835: problem page and forum thread (fetched 2026-10-06T16:07:49Z)

Comments are unverified; several withdraw earlier claims.

## Page


## Forum comments
Order by
 oldest first or
 newest first. (The most recent comments are highlighted in a red border.)
 For the smallest open case $k=16$ we looked for a single Steiner system $S(15,16,32)$ with a prescribed automorphism group $G$, by the Kramer–Mesner method: a $G$-invariant system is a union of $G$-orbits of $16$-sets, and the $G$-orbits of $15$-sets give the linear conditions.
Result: there is no $S(15,16,32)$ invariant under $\mathrm{AGL}(5,2)$ ($38$ orbits of $16$-sets, $30$ of $15$-sets) or under $\mathrm{PGL}(2,31)$ ($20636$ and $19234$ orbits; here some orbit of $15$-sets admits no orbit of $16$-sets at all). For $\mathrm{PSL}(2,31)$, $\mathrm{A\Gamma L}(1,32)$ and $\mathrm{AGL}(1,32)$ the systems have $21213$, $60714$ and $304174$ variables after identifying each orbit with its complementary orbit, and our solvers (SAT, exact cover, LP/MIP) did not decide them.
The code was checked on $S(3,4,8)$, $S(3,4,16)$ and $S(5,6,12)$ with their known groups. We also checked that the block intersection numbers of a hypothetical $S(15,16,32)$ are nonnegative integers, so this classical test gives no obstruction. None of this says anything about an $S(15,16,32)$ without such symmetry, or about the $17$ disjoint copies a colouring would need.
Code, logs and the undecided systems: https://github.com/veljjanoski/erdos835
AI-usage disclosure: Claude (Anthropic) was used as a coding assistant.
 veljjanoski
 — 13:17 on 21 Sep 2026
 👍
 0
 📝
 0
 🤖
 0
 A simple addition: no proper $17$-colouring of $J(32,16)$ is invariant (colour classes mapped to colour classes) under a permutation $g$ of prime order $p\in\{19,23,29,31\}$. Such a $g$ must fix every colour class, since there are only $17<p$ classes, and it is one $p$-cycle $(x_1\dots x_p)$ plus fixed points. If $B$ is the set of fixed points together with $x_1,\dots,x_{p-16}$, then $|B\cap gB|=15$, so $B$ and $gB$ are adjacent but have the same colour. 
Every $2$-transitive group of degree $32$ contains an element of order $31$, so no colouring is invariant under any of the groups above. This does not decide the three open single-system cases.
 veljjanoski
 — 09:55 on 28 Sep 2026
 👍
 0
 📝
 0
 🤖
 0
 About edkirkby's comment at 18:53 on 14 Mar 2026, this post checks the following implication: 
if a proper $(k+1)$-colouring of $J(2k,k)$ exists in the remaining Ma--Tang cases, then every $k$-set has the same colour as its complement. 
The Walsh-Hadamard-transform idea is edkirkby's; I do not use it here, and instead give a separate Hoffman-bound/Johnson-scheme verification of the same claim.
The proof is as follows. By Ma--Tang [1], after the already excluded cases we may assume that $k+1$ is prime. Since $k>2$, this means that $k$ is even.
Let $v=\binom{2k}{k}$. The graph $J(2k,k)$ is $k^2$-regular, with least eigenvalue $-k$ on the last Johnson eigenspace $E_k$. Hoffman's ratio bound [2] gives $\alpha(J(2k,k))\le {v k\over k^2+k}={v\over k+1}$. Thus every colour class $C$ has size exactly $v/(k+1)$, and equality in the Hoffman-bound argument gives $1_C-\frac{1}{k+1}1\in E_k$.
Now the complement map $X\mapsto X^c$ is the adjacency operator of $K(2k,k)$, the distance-$k$ graph in the Johnson scheme [3,4]. By the Eberlein eigenvalue formula [3], this operator has eigenvalue $E_k(i)=(-1)^i$ on $E_i$; equivalently, substituting in the formula leaves only the $h=0$ term. Hence on $E_k$ it acts by $(-1)^k=1$. It also fixes the all-ones vector.
Therefore it fixes $1_C=\left(1_C-\frac{1}{k+1}1\right)+\frac{1}{k+1}1$. So $C$ is closed under complements: $X\in C \iff X^c\in C$. Thus, in any remaining possible colouring, every $k$-set has the same colour as its complement.
References.
[1] J. Ma and Q. Tang, short note on Erdős Problem #835, https://github.com/QuanyuTang/erdos-problem-835/blob/main/On_Problem_835.pdf
[2] A. Abiad, W. Bosma and T. van Veluw, Hoffman colorings of graphs, Linear Algebra Appl. 710 (2025), Theorem 1.1, https://doi.org/10.1016/j.laa.2025.01.036
[3] A. E. Brouwer, S. M. Cioabă, F. Ihringer and M. McGinnis, The smallest eigenvalues of Hamming graphs, Johnson graphs and other distance-regular graphs with classical parameters, JCTB 133 (2018), Section 1.2, https://arxiv.org/abs/1709.09011
[4] A. E. Brouwer, Kneser graphs / Johnson graphs, https://aeb.win.tue.nl/graphs/Kneser.html and https://aeb.win.tue.nl/graphs/Johnson.html
AI usage disclosure: This comment was prepared with assistance from Codex 5.5 using xhigh reasoning, and ChatGPT 5.5 Pro.
 KentaKitamura
 — 04:52 on 30 May 2026
 👍
 0
 📝
 0
 🤖
 0
 A small design-theoretic addendum for the first remaining cases with $k+1$ prime. I use $S(t,k,v)$ for a $t$-$(v,k,1)$ design.
If $J(2k,k)$ had a proper $(k+1)$-coloring $c$, fix any $(k-1)$-set $T \subset [2k]$. The $k+1$ vertices $T \cup \{x\}$, for $x \in [2k] \setminus T$, pairwise intersect in $T$, hence form a $K_{k+1}$. Therefore each color occurs exactly once among them. Thus, for each color $i$, the color class
$$C_i = \{X \in \tbinom{[2k]}{k} : c(X) = i\}$$
contains exactly one $k$-set through every $(k-1)$-set $T$. Hence each $C_i$ is an $S(k-1,k,2k)$, and the $k+1$ color classes form an $\mathrm{LS}(k-1,k,2k)$.
For $k=10$, this would give an $S(9,10,20)$. Deriving five times gives $S(4,5,15)$, which is known not to exist by Mendelsohn–Hung. Hence $\chi(J(20,10)) \geq 12$.
For $k=12$, this would give an $S(11,12,24)$. Deriving seven times gives $S(4,5,17)$, which is known not to exist by Östergård–Pottonen. Hence $\chi(J(24,12)) \geq 14$.
This gives no numerical improvement over the constant-weight-code bounds already mentioned, but it makes the concrete large-set obstruction explicit for these two $k+1$-prime cases. The same derivation for $k=16$ reaches $S(4,5,21)$, which appears to be the smallest $v$ for which the existence of an $S(4,5,v)$ is open.
 athvedt
 — 22:22 on 21 May 2026
 👍
 0
 📝
 0
 🤖
 0
 I believe I have a simple proof using Walsh-Hadamard transforms that if such a colouring exists, each set must have the same colour as its complement. Does anyone know if this is a known result, or if it may be useful for solving the problem itself?
 edkirkby
 — 18:53 on 14 Mar 2026
 👍
 1
 📝
 0
 🤖
 0
 Jie Ma and I wrote a short note on this problem. We prove that if \(k>2\) and \(k+1\) is not prime, then \(\chi(J(2k,k))\neq k+1\).
To fully resolve this problem, one may need to investigate the existence of a large set of Steiner system $S(2k,k,k−1)$.
(The site has been updated to address this comment.)
 Quanyu Tang
 — 14:41 on 31 Dec 2025
 👍
 1
 📝
 1
 🤖
 0
 Thanks, looks good. I had a quick look and it's surprising how little literature there is on lower bounds for the chromatic number of Johnson graphs (there is a fair bit more on upper bounds).
You might like to think about whether your argument can be generalised to say anything about lower bounds for the chromatic number of Johnson graphs in general, or even more generally 'token graphs' (see e.g. Section 5 of this paper).
It's annoying that you can't handle the case $k+1$ prime. Looking at the reason it's known for $k=4$, for example, this follows because the chromatic number of $J(6,3)$ is $6$ and hence the chromatic number of $J(7,4)\cong J(7,3)$ is also at least $6$, and so the chromatic number of $J(8,4)$ is also at least $6$. Perhaps a similar monotonicity trick would handle $k+1$ prime (e.g. if you can prove a lower bound of $k+3$ for all $k\neq p-1$ this would imply a lower bound of $k+2$ for all $k$).
PS - I appreciate the acknowledgement of this site, but please do also remember to cite the original paper(s) of Erdős as the actual source of the problem!
 Thomas Bloom
 — 15:33 on 31 Dec 2025
 👍
 1
 📝
 0
 🤖
 0
 AlphaProof (on 2025-12-26) found a proof that $J(18, 9) \ne 10$, which was the first result we marked as open in formal-conjectures (albeit it was in fact not, see below).
Then we realised this proof could easily be adapted to work for all odd $k$ (on 2025-12-27) and Lean agreed. We even thought it could be generalised to all $k$ such that $k + 1$ is composite, but did not pursue this further as we simultaneously realised that Johnson's bound along with the independence bound on the chromatic number of a graph gives the same value (or even better sometimes).
Concretely, Johnson proved that the independence number of $J(n, k)$ is at most $A(n, 4, k)$, which is recursively defined by $A(n, 4, 1) = 1$ and $A(n, 4, k) = \lfloor \frac nk A(n - 1, 4, k - 1)\rfloor$ for $k > 1$. The lower bound on the chromatic number is then $\lceil \binom{2k}k/ A(2k, 4, k)\rceil$, which is at least $k + 2$ precisely when $k + 1$ is composite.
We thought to mention here that the result is in fact not novel, although it does indeed seem no one in the coding theory literature bothered to evaluate $A(2k, 4, k)$ in relation to this problem.
The original Alphaproof proof is here, the human-powered generalisation is there, and the current state of the formal proof is in this PR to formal-conjectures .
 YaelDillies
 — 10:00 on 26 Jan 202