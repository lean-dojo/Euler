module

public import Review.Definitions.Stability.Energy

/-! # Mixed derivative indices -/

@[expose] public noncomputable section

open Set

namespace Euler.Stability

/-- Three rows, each with all `k + 1` mixed derivatives of total order `k`. -/
abbrev MixedDerivativeIndex (k : ℕ) := Fin 3 × Fin (k + 1)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

end Euler.Stability

end
