import Mathlib.Tactic.NormNum
import Formal.Campaigns.R26266ed1bf7cf0517729c8cb.Contract
set_option autoImplicit false
namespace Formal.Campaigns.R26266ed1bf7cf0517729c8cb
theorem result : ((0 : ℚ)^2 + 0 = 0^3 + 0^2 - 2*0) ∧ ((0 : ℚ)^2 + 0 = 1^3 + 1^2 - 2*1) := by
  norm_num
end Formal.Campaigns.R26266ed1bf7cf0517729c8cb
