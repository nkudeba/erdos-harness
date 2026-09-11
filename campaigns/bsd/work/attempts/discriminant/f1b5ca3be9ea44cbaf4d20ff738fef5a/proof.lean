import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Tactic.NormNum
import Formal.Campaigns.R209f62a6cb4dd48d8e4c5713.Contract
set_option autoImplicit false
namespace Formal.Campaigns.R209f62a6cb4dd48d8e4c5713
theorem result : (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve ℚ).Δ = 64 := by
  norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
end Formal.Campaigns.R209f62a6cb4dd48d8e4c5713
