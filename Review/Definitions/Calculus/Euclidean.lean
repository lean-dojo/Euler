module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Meridian coordinates -/

@[expose] public noncomputable section

/-- Real Euclidean space with `n` coordinates. -/
notation:arg "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

namespace Euler.Coordinates

/-- Radial coordinate on the meridian plane. -/
def meridianR (x : ℝ^2) : ℝ := x 0

/-- Axial coordinate on the meridian plane. -/
def meridianZ (x : ℝ^2) : ℝ := x 1

end Euler.Coordinates

end
