/-
Copyright (c) 2026 Robert Joseph George and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/

module

public import Euler.Calculus.PartialDeriv

/-!
# Static axisymmetric derivatives

The concrete package uses coordinate derivatives. The value assigned to
`∂r f / r` at the axis is a definition; identifying it with a limit requires
regularity and a vanishing radial derivative.
-/

@[expose] public section

noncomputable section

open Euler.Coordinates (meridianR meridianZ)

namespace Euler.Calculus

/--
Derivative operators for meridian profiles in either coordinate system.

Grouping the operators lets the same residual formula be used before and after
the `sinh` change of coordinates. `dROverR` represents `(∂R f)/R`, including
an explicitly chosen value at `R = 0`. A theorem using that value as a limit
must separately supply the required regularity and vanishing radial derivative.
-/
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

/--
Axis-regular realization of `(partial_R f) / R`.

Away from the axis this is the ordinary quotient. At `R = 0` it selects
`partial_RR f`. This selected branch is the removable value for a sufficiently
regular profile with vanishing first radial trace. Stronger evenness, such as
squared-radius factorization, is still needed for smooth three-dimensional
reconstruction.
-/
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

/-- Off the axis, the classical `dROverR` is the literal quotient `(∂_R f)/R`,
written with `(meridianR x)⁻¹`. -/
@[simp]
theorem regularizedProfileDROverR_of_ne_zero
    (f : (ℝ^2 → ℝ)) (x : (ℝ^2)) (hx : meridianR x ≠ 0) :
    classicalAxisymmetricDifferential.dROverR f x =
      (meridianR x)⁻¹ * classicalAxisymmetricDifferential.DR f x := by
  simp [classicalAxisymmetricDifferential, regularizedProfileDROverR, hx]

/-- On the axis, the classical `dROverR` is `∂_RR f`. This is the removable value of
`(∂_R f)/R` for a smooth profile whose radial derivative vanishes at `R = 0`; the lemma
records the choice of branch, not its justification. -/
@[simp]
theorem regularizedProfileDROverR_of_eq_zero
    (f : (ℝ^2 → ℝ)) (x : (ℝ^2)) (hx : meridianR x = 0) :
    classicalAxisymmetricDifferential.dROverR f x =
      classicalAxisymmetricDifferential.DRR f x := by
  simp [classicalAxisymmetricDifferential, regularizedProfileDROverR, hx]

/-- The unsigned axisymmetric elliptic operator `∂RR + (3/R)∂R + ∂ZZ`. -/
def axisymmetricLaplacian (D : AxisymmetricDifferential) (f : (ℝ^2 → ℝ)) : (ℝ^2 → ℝ) :=
  fun x ↦ D.DRR f x + 3 * D.dROverR f x + D.DZZ f x

/-- The signed elliptic operator with sign convention `-L_ax Ψ = Ω`. -/
def signedElliptic (D : AxisymmetricDifferential) (f : (ℝ^2 → ℝ)) : (ℝ^2 → ℝ) :=
  fun x ↦ -axisymmetricLaplacian D f x


end Euler.Calculus
