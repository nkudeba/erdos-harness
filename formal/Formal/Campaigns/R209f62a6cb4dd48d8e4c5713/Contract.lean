import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Tactic.NormNum
set_option autoImplicit false
namespace Formal.Campaigns.R209f62a6cb4dd48d8e4c5713
def Target : Prop :=
(⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve ℚ).Δ = 64
end Formal.Campaigns.R209f62a6cb4dd48d8e4c5713
