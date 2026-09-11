import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Tactic.NormNum
import Formal.Campaigns.R95c2c757175e1cf1720b4a2f.Contract
set_option autoImplicit false
namespace Formal.Campaigns.R95c2c757175e1cf1720b4a2f
theorem result : (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve ℚ).Δ = 64 := by
  norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
end Formal.Campaigns.R95c2c757175e1cf1720b4a2f
