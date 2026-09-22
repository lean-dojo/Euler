module

public import Review.Definitions.Equations.Cartesian
public import Review.Definitions.PhysicalTime.ContractingCenter

/-! # Velocity on the axis -/

@[expose] public noncomputable section

open MeasureTheory Set Filter

open Euler.PhysicalTime

open scoped Topology ENNReal

namespace Euler

open Cartesian

/-- A point on the Cartesian symmetry axis. -/
def axisPoint (z : ℝ) : ℝ^3 := vector 0 0 z

/-- Cartesian velocity with reduced swirl `b`; the axial component is `w`. -/
def axisymmetricVelocity (a b w : ScalarField) : VectorField :=
  fun x t ↦ vector
    (-(a x t * x 0) - b x t * x 1)
    (-(a x t * x 1) + b x t * x 0)
    (w x t)

end Euler

end
