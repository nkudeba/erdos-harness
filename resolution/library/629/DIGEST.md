# erdosproblems.com #629: problem page and forum thread (fetched 2026-10-19T23:46:38Z)

Comments and proof claims are unverified; several withdraw earlier claims.

## Page
The list chromatic number $\chi_L(G)$ is defined to be the minimal $k$ such that for any assignment of a list of $k$ colours to each vertex of $G$ (perhaps different lists for different vertices) a colouring of each vertex by a colour on its list can be chosen such that adjacent vertices receive distinct colours.
Determine the minimal number of vertices $n(k)$ of a bipartite graph $G$ such that $\chi_L(G)>k$.
#629: [ERT80]
graph theory | 
chromatic number
A problem of Erdős, Rubin, and Taylor [ERT80], who proved that\[2^{k-1}<n(k) <k^22^{k+2}.\]They also prove that if $m(k)$ is the size of the smallest family of $k$-sets without property B (i.e. the smallest number of $k$-sets in a graph with chromatic number $3$) then $m(k)\leq n(k)\leq m(k+1)$. Bounds on $m(k)$ are the subject of [901]. The lower bounds on $m(k)$ by Radhakrishnan and Srinivasan [RaSr00] imply that\[2^k \left(\frac{k}{\log k}\right)^{1/2}\ll n(k).\]Erdős, Rubin, and Taylor [ERT80] proved $n(2)=6$ and Hanson, MacGillivray, and Toft [HMT96] proved $n(3)=14$ and\[n(k) \leq kn(k-2)+2^k.\]See also the entry in the graphs problem collection.
Additional thanks to: Zach Hunter and Quanyu Tang

## Forum comments
Order by
 oldest first or
 newest first. (The most recent comments are highlighted in a red border.)
 Some computational notes on n(4) (separator-free / property-B encoding)
I spent some time attacking the open value n(4) computationally, with help of opus 4.8 and gpt 5.5 thinking, and wanted to share what helped, what didn't, and where the wall is — in case it saves someone else the dead ends, or someone with more compute wants to push further. Code is public: https://github.com/sp4cerat/Wunderlampe-/tree/main/chromatic
 sp4cerat
 — 06:20 on 22 Jun 2026
 👍
 0
 📝
 0
 🤖
 0
 After some encounters with GPT 5.3 Thinking and Gemini 3 Pro, the upper bound has been improved to\[n(k) \leq (\frac{e \ln 2}{2}+o(1))k^22^k\]See here
 Alfaiz
 — 19:51 on 04 Apr 2026
 👍
 1
 📝
 0
 🤖
 0
 Congrats. Do you mean GPT-5.4 Thinking and Gemini 3.1 Pro, or are you really using old models?
Standard check finds no issues.
However, it seems this result is not new. Erdos in 1964 proved that $m(k) \le (e (\log 2)/4 + o(1) ) k^2 2^k$, and we also know that $n(k) \le 2 m(k)$. The result is a combination of these results. This is found by GPT-5.4 Thinking during the check.
 Nat Sothanaphan
 — 20:50 on 04 Apr 2026
 👍
 0
 📝
 0
 🤖
 0
 It seems that a sharper lower bound for $n(k)$ is available. By the results in [ERT80] (see also [HMT96, Section 1]), we know that $m(k)\le n(k)\le 2m(k)$, where $m(k)$ denote the minimum number of edges possible in a 3-chromatic $k$-uniform hypergraph.
With the current best lower bound $m(k)=\Omega \left(2^k\sqrt{k/\log k}\right)$ due to Radhakrishnan and Srinivasan [RaSr20] (see also [GLW24]), we obtain\[
n(k)=\Omega\left(2^k\sqrt{\frac{k}{\log k}}\right).
\]References.
[GLW24] Grill, Karl, Daniel Linzmayer, and T. U. Wien. "Improved Lower Bounds for Property B." arXiv:2403.05674v3. 
[RaSr20] Radhakrishnan, Jaikumar, and Aravind Srinivasan. "Improved bounds and algorithms for hypergraph 2-coloring." Random Structures & Algorithms 16.1 (2000): 4-32.
(The site has been updated to address this comment.)
 Quanyu Tang
 — 18:57 on 25 Oct 2025
 👍
 1
 📝
 2
 🤖
 0