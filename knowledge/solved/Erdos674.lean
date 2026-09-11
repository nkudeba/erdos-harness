import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Fin

set_option maxHeartbeats 1000000
set_option autoImplicit false

private lemma erdos_674_key (x y z : ℕ) (h1 : 12 * x + 8 * y = 11 * z)
    (h2 : 6 * x + 8 * y = 7 * z) :
    (2 ^ 12 * 3 ^ 6) ^ x * (2 ^ 8 * 3 ^ 8) ^ y = (2 ^ 11 * 3 ^ 7) ^ z := by
  have hx : (2 ^ 12 * 3 ^ 6 : ℕ) ^ x = 2 ^ (12 * x) * 3 ^ (6 * x) := by
    rw [mul_pow, ← pow_mul, ← pow_mul]
  have hy : (2 ^ 8 * 3 ^ 8 : ℕ) ^ y = 2 ^ (8 * y) * 3 ^ (8 * y) := by
    rw [mul_pow, ← pow_mul, ← pow_mul]
  have hz : (2 ^ 11 * 3 ^ 7 : ℕ) ^ z = 2 ^ (11 * z) * 3 ^ (7 * z) := by
    rw [mul_pow, ← pow_mul, ← pow_mul]
  rw [hx, hy, hz, mul_mul_mul_comm, ← pow_add, ← pow_add, h1, h2]

theorem erdos_674 : ∃ x y z : ℕ, 1 < x ∧ 1 < y ∧ 1 < z ∧ x ^ x * y ^ y = z ^ z := by
  refine ⟨2 ^ 12 * 3 ^ 6, 2 ^ 8 * 3 ^ 8, 2 ^ 11 * 3 ^ 7, by norm_num, by norm_num, by norm_num, ?_⟩
  have h1 : 12 * (2 ^ 12 * 3 ^ 6) + 8 * (2 ^ 8 * 3 ^ 8) = 11 * (2 ^ 11 * 3 ^ 7) := by norm_num
  have h2 : 6 * (2 ^ 12 * 3 ^ 6) + 8 * (2 ^ 8 * 3 ^ 8) = 7 * (2 ^ 11 * 3 ^ 7) := by norm_num
  exact erdos_674_key _ _ _ h1 h2
