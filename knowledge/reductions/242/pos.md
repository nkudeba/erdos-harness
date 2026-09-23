# Checked structural reductions — Erdős #242

Each claim below was proposed by the reduction stage and then **empirically checked** on small
cases by a script run in the sandbox. A check is evidence, not a proof.

## decomposition

**If 4/m = 1/x+1/y+1/z with 1<=x<y<z, then 4/(km) = 1/(kx)+1/(ky)+1/(kz) with kx<ky<kz for every k>=1; hence the statement for all n>2 follows from the statement for n=4 and for every odd prime n.**

Divide both sides of the identity by k; strict order and distinctness are preserved by multiplying by k>0. Every n>2 is divisible by 4 or by an odd prime p (p<=n), and n=4 has the solution 1 = 1/2+1/3+1/6.

*Consequence:* The search and proof need only treat n=4 (done) and odd primes p. A composite counterexample would give a prime (or 4) counterexample, so any minimal counterexample is prime.

*Lean:* stated

```lean
theorem reduction_1 : ∀ m k : ℕ, 0 < k → (∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (4 : ℚ) / (m : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)) → (∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (4 : ℚ) / ((k * m : ℕ) : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)) := by
  sorry
```

## parity

**Every odd prime p with p not congruent to 1 mod 24 has an explicit solution, so the whole conjecture reduces to primes p ≡ 1 (mod 24).**

The explicit solutions are:
- p=3: 4/3 = 1/1+1/4+1/12.
- p≡3 (mod 4), p>=7: with a=(p+1)/4, 4/p = 1/(a+1)+1/(a(a+1))+1/(ap).
- p≡2 (mod 3), p>=5: 4/p = 1/((p+1)/3)+1/p+1/(p(p+1)/3), since 3/(p+1)+3/(p(p+1)) = 3/p.
- p≡5 (mod 8), with k=(p-5)/8: 4/p = 1/(2k+2)+1/(p(k+1))+1/(2p(k+1)), since 3/(2t) = 1/t+1/(2t).
An odd prime not covered by these cases satisfies p≡1 (mod 4), p≡1 (mod 3) and p≡1 (mod 8), i.e. p≡1 (mod 24).

*Consequence:* Search for counterexamples only among primes p ≡ 1 (mod 24). The proof stage can discharge every other residue class by the four explicit identities; the open case is exactly primes ≡ 1 mod 24.

*Lean:* stated

```lean
theorem reduction_2 : ∀ p : ℕ, Nat.Prime p → 2 < p → p % 24 ≠ 1 → ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (4 : ℚ) / (p : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ) := by
  sorry
```

## forced

**In every solution 4/n = 1/x+1/y+1/z with x<y<z, we have n/4 < x < 3n/4; and given x, with r = 4/n - 1/x, we have 1/r < y < 2/r.**

Since 1/x < 4/n we get x > n/4. Since 4/n < 3/x (because y,z > x) we get x < 3n/4. Similarly r = 1/y+1/z with 1/y < r < 2/y.

*Consequence:* The search for each n is a finite box: x ranges over (n/4, 3n/4), y over (1/r, 2/r), and z is determined as 1/(r-1/y). A search can therefore certify non-existence for a single n.

*Lean:* stated

```lean
theorem reduction_3 : ∀ n x y z : ℕ, 2 < n → 1 ≤ x → x < y → y < z → (4 : ℚ) / (n : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ) → n < 4 * x ∧ 4 * x < 3 * n := by
  sorry
```
