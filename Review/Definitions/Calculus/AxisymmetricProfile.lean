module

public import Review.Definitions.Calculus.PartialDeriv

/-! # Axisymmetric operators -/

@[expose] public noncomputable section

open Euler.Coordinates (meridianR meridianZ)

namespace Euler.Calculus

/-- Meridian derivatives for the physical or computational coordinates.
`dROverR` includes the chosen value of `(∂R f)/R` on the axis. -/
structure AxisymmetricDifferential where
  /-- Radial first-derivative operator. -/
  DR : (ℝ^2 → ℝ) → (ℝ^2 → ℝ)
  /-- Axial first-derivative operator. -/
  DZ : (ℝ^2 → ℝ) → (ℝ^2 → ℝ)
  /-- Radial second-derivative operator. -/
  DRR : (ℝ^2 → ℝ) → (ℝ^2 → ℝ)
  /-- Axial second-derivative operator. -/
  DZZ : (ℝ^2 → ℝ) → (ℝ^2 → ℝ)
  /-- Operator representing `(∂R f)/R`, with its axis value supplied by the realization. -/
  dROverR : (ℝ^2 → ℝ) → (ℝ^2 → ℝ)

/-- Euclidean radial derivative `∂R` for a scalar profile. -/
def profileDR (f : (ℝ^2 → ℝ)) : (ℝ^2 → ℝ) :=
  fun x ↦ partialDeriv (n := 2) 0 f x

/-- Euclidean axial derivative `∂Z` for a scalar profile. -/
def profileDZ (f : (ℝ^2 → ℝ)) : (ℝ^2 → ℝ) :=
  fun x ↦ partialDeriv (n := 2) 1 f x

/-- Euclidean second radial derivative `∂RR` for a scalar profile. -/
def profileDRR (f : (ℝ^2 → ℝ)) : (ℝ^2 → ℝ) :=
  fun x ↦ partialDeriv (n := 2) 0 (profileDR f) x

/-- Euclidean second axial derivative `∂ZZ` for a scalar profile. -/
def profileDZZ (f : (ℝ^2 → ℝ)) : (ℝ^2 → ℝ) :=
  fun x ↦ partialDeriv (n := 2) 1 (profileDZ f) x

/-- The quotient `(∂R f)/R`, defined as `∂RR f` at the axis.
This is the limiting value for a C² profile whose radial derivative vanishes along the axis. -/
def regularizedProfileDROverR (f : (ℝ^2 → ℝ)) : (ℝ^2 → ℝ) :=
  fun x ↦
    if meridianR x = 0 then profileDRR f x
    else (meridianR x)⁻¹ * profileDR f x

/-- Concrete classical derivative package for axis-regular profile equations. -/
def classicalAxisymmetricDifferential : AxisymmetricDifferential where
  DR := profileDR
  DZ := profileDZ
  DRR := profileDRR
  DZZ := profileDZZ
  dROverR := regularizedProfileDROverR

/-- The unsigned axisymmetric elliptic operator `∂RR + (3/R)∂R + ∂ZZ`. -/
def axisymmetricLaplacian (D : AxisymmetricDifferential) (f : (ℝ^2 → ℝ)) : (ℝ^2 → ℝ) :=
  fun x ↦ D.DRR f x + 3 * D.dROverR f x + D.DZZ f x

/-- The signed elliptic operator with sign convention `-L_ax Ψ = Ω`. -/
def signedElliptic (D : AxisymmetricDifferential) (f : (ℝ^2 → ℝ)) : (ℝ^2 → ℝ) :=
  fun x ↦ -axisymmetricLaplacian D f x

end Euler.Calculus

end
