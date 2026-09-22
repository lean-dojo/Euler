module

public import Review.Definitions.Scaling.Calculus
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Euler scaling -/

@[expose] public noncomputable section

namespace Euler.Cartesian

/-- The rescaled velocity in S387. -/
def scaledVelocity (η α : ℝ) (u : VectorField) : VectorField :=
  scaleVectorField (η ^ α) η (η ^ (α + 1)) u

/-- The rescaled pressure in S387. -/
def scaledPressure (η α : ℝ) (p : ScalarField) : ScalarField :=
  scaleScalarField (η ^ (2 * α)) η (η ^ (α + 1)) p

/-- The time domain sampled by the Euler scaling. -/
def scaledTimeSet (η α : ℝ) (I : Set ℝ) : Set ℝ :=
  pullbackTimeSet (η ^ (α + 1)) I

end Euler.Cartesian

end
