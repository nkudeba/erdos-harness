import Mathlib.Tactic
set_option autoImplicit false
namespace Formal.Campaigns.Rac7a2183797d05b8e511c3e4
def Target : Prop :=
∀ rank selmer : ℕ, 2 ≤ rank → rank ≤ selmer → selmer = 2 → rank = 2
end Formal.Campaigns.Rac7a2183797d05b8e511c3e4
