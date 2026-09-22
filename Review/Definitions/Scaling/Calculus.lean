module

public import Review.Definitions.Equations.Cartesian
public import Review.Definitions.Rescaling.Affine

/-! # Space-time scaling -/

@[expose] public noncomputable section

namespace Euler.Cartesian

open Euler.Similarity

/-- A scalar field pulled back by constant spatial and temporal dilations, with amplitude `A`. -/
def scaleScalarField (A η θ : ℝ) (f : ScalarField) : ScalarField :=
  fun x t ↦ A * f (η • x) (θ * t)

/-- A vector field pulled back by constant spatial and temporal dilations, with amplitude `A`. -/
def scaleVectorField (A η θ : ℝ) (u : VectorField) : VectorField :=
  fun x t ↦ WithLp.toLp 2 fun i ↦ A * u (η • x) (θ * t) i

/-- The time set on which a pullback by `t ↦ θt` samples a prescribed time set `I`. -/
def pullbackTimeSet (θ : ℝ) (I : Set ℝ) : Set ℝ :=
  (fun t ↦ θ * t) ⁻¹' I

end Euler.Cartesian

end
