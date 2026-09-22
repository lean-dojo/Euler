module

public import Review.Definitions.Linearization.Reference

/-! # Swirl evolution -/

@[expose] public noncomputable section

namespace Euler.Linearization

local notation "Dr" => partialDeriv (0 : Fin 2)

local notation "Dz" => partialDeriv (1 : Fin 2)

/-- The reduced-swirl evolution operator in S421: `∂τ u = swirlEvolution ...`.
Transport is subtracted because it has been moved to the right of the equation. -/
def swirlEvolution (lam C cu : ℝ) (u psi : ℝ^2 → ℝ) (x : ℝ^2) : ℝ :=
  2 * u x * Dz psi x + cu * u x
    - (lam * x 0 - x 0 * Dz psi x) * Dr u x
    - (lam * x 1 + C + 2 * psi x + x 0 * Dr psi x) * Dz u x

end Euler.Linearization

end
