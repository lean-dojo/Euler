module

public import Review.Definitions.Calculus.AxisymmetricProfile
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! # Computational coordinates -/

@[expose] public noncomputable section

open scoped Topology

open Euler.Calculus

namespace Euler.Coordinates

/-- The map `(ρ, ζ) ↦ (sinh ρ, sinh ζ)` from computational to profile coordinates. -/
def sinhCoordinates (x : (ℝ^2)) : (ℝ^2) :=
  EuclideanSpace.single 0 (Real.sinh (meridianR x)) +
    EuclideanSpace.single 1 (Real.sinh (meridianZ x))

/-- The coordinate identity: pull a physical profile back to computational coordinates. -/
def sinhPullback (f : (ℝ^2 → ℝ)) : (ℝ^2 → ℝ) :=
  fun x ↦ f (sinhCoordinates x)

/-- The computational version of `(∂R f)/R`, with its removable axis value selected. -/
def computationalDROverR (f : (ℝ^2 → ℝ)) : (ℝ^2 → ℝ) :=
  fun x ↦
    if meridianR x = 0 then profileDRR f x
    else profileDR f x /
      (Real.sinh (meridianR x) * Real.cosh (meridianR x))

/-- The transformed classical derivative package in `(ρ, ζ)` coordinates. -/
def computationalAxisymmetricDifferential : AxisymmetricDifferential where
  DR := fun f x ↦ profileDR f x / Real.cosh (meridianR x)
  DZ := fun f x ↦ profileDZ f x / Real.cosh (meridianZ x)
  DRR := fun f x ↦
    profileDRR f x / Real.cosh (meridianR x) ^ 2 -
      Real.sinh (meridianR x) / Real.cosh (meridianR x) ^ 3 * profileDR f x
  DZZ := fun f x ↦
    profileDZZ f x / Real.cosh (meridianZ x) ^ 2 -
      Real.sinh (meridianZ x) / Real.cosh (meridianZ x) ^ 3 * profileDZ f x
  dROverR := computationalDROverR

/-- The elliptic operator in computational coordinates, equation (S327). -/
def computationalElliptic (f : (ℝ^2 → ℝ)) : (ℝ^2 → ℝ) :=
  axisymmetricLaplacian computationalAxisymmetricDifferential f

end Euler.Coordinates

end
