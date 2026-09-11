import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic
set_option autoImplicit false
namespace Formal.Campaigns.Rc235b45e135427af9a0fde57
def Target : Prop :=
(Finset.univ.filter (fun xy : Fin 5 × Fin 5 => (xy.2.val ^ 2) % 5 = (xy.1.val ^ 3 + 5 - xy.1.val) % 5)).card = 7
end Formal.Campaigns.Rc235b45e135427af9a0fde57
