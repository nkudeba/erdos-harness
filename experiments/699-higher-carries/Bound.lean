import Mathlib.Tactic

namespace Erdos699HigherCarries

/-- Algebraic localization bound. The connection to binomial coefficients is
    documented separately; this theorem does not assume or prove Erdős #699. -/
theorem localization_bound (n j c m k b e : ℤ)
    (hn : n = c*m) (hj : j = k*m) (hbe : b*e = n-1)
    (hk : 0 < k) (hkc : 2*k ≤ c) (he : 0 ≤ e)
    (hdj : b ∣ j*(j-1)) : 4*(n-1) ≤ e*c^2 := by
  have hid : k*(c-k) = (n-1)*((n+1)*k^2-c*k) - c^2*(j*(j-1)) := by
    rw [hn, hj]
    ring
  have hbn : b ∣ n-1 := ⟨e, hbe.symm⟩
  have hleft : b ∣ (n-1)*((n+1)*k^2-c*k) := dvd_mul_of_dvd_left hbn _
  have hright : b ∣ c^2*(j*(j-1)) := dvd_mul_of_dvd_right hdj _
  have hd : b ∣ k*(c-k) := hid ▸ dvd_sub hleft hright
  have hpos : 0 < k*(c-k) := mul_pos hk (by linarith)
  have hle : b ≤ k*(c-k) := Int.le_of_dvd hpos hd
  have h4 : 4*b ≤ c^2 := by nlinarith [sq_nonneg (c-2*k)]
  have hm := mul_le_mul_of_nonneg_left h4 he
  nlinarith

#print axioms localization_bound
end Erdos699HigherCarries
