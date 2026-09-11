import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic
import Formal.Campaigns.Rc235b45e135427af9a0fde57.Contract
set_option autoImplicit false
namespace Formal.Campaigns.Rc235b45e135427af9a0fde57
theorem result : (Finset.univ.filter (fun xy : Fin 5 × Fin 5 => (xy.2.val ^ 2) % 5 = (xy.1.val ^ 3 + 5 - xy.1.val) % 5)).card = 7 := by
  decide +kernel
end Formal.Campaigns.Rc235b45e135427af9a0fde57
