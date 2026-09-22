module

public import Review.Definitions.Calculus.Euclidean
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Similarity fields -/

@[expose] public noncomputable section

namespace Euler.Similarity

/-- Backward power about a candidate singular time. Analytic statements about
this scale are restricted to times strictly before `singularTime`. -/
def backwardPowerScale (alpha singularTime t : ℝ) : ℝ :=
  (singularTime - t) ^ (-alpha)

end Euler.Similarity

namespace Euler

open Euler.Similarity

/-- The moving meridian coordinates `R = r/(T-t)^λ`, `Z = (z-zc(t))/(T-t)^λ`. -/
def similarityCoordinates (lam singularTime : ℝ) (axialCenter : ℝ → ℝ)
    (x : ℝ^2) (t : ℝ) : ℝ^2 :=
  backwardPowerScale lam singularTime t •
    (x - axialCenter t • EuclideanSpace.single 1 1)

/-- A stationary scalar profile expressed in moving physical coordinates. -/
def similarityScalar (profile : ℝ^2 → ℝ) (alpha lam singularTime : ℝ)
    (axialCenter : ℝ → ℝ) (x : ℝ^2) (t : ℝ) : ℝ :=
  backwardPowerScale alpha singularTime t *
    profile (similarityCoordinates lam singularTime axialCenter x t)

end Euler

end
