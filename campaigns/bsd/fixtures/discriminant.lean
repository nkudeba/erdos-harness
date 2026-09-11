theorem result : (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve ℚ).Δ = 64 := by
  norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
