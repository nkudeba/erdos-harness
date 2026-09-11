theorem result : (Finset.univ.filter (fun xy : Fin 5 × Fin 5 => (xy.2.val ^ 2) % 5 = (xy.1.val ^ 3 + 5 - xy.1.val) % 5)).card = 7 := by
  decide +kernel
