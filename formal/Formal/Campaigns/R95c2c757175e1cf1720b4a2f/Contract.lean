import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Tactic.NormNum
set_option autoImplicit false
namespace Formal.Campaigns.R95c2c757175e1cf1720b4a2f
def Target : Prop :=
(⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve ℚ).Δ = 64
end Formal.Campaigns.R95c2c757175e1cf1720b4a2f
