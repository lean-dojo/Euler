/-
Copyright (c) 2026 Robert Joseph George and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/

module

public import Euler.Calculus.ChainRule
public import Euler.Calculus.AxisymmetricProfile
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Reduced axisymmetric Euler operators

Meridian velocity and the swirl, vorticity and stream residuals use actual
coordinate derivatives. The axis extension is a piecewise expression; continuity
there requires separate regularity and parity.
-/

@[expose] public section

noncomputable section

open Euler.Calculus
open Euler.Coordinates (meridianR)

namespace Euler.Axisymmetric

/-- Open meridian half-plane. -/
def positiveRadiusMeridian : Set (ℝ^2) := {x | 0 < x (0 : Fin 2)}

/-- Membership in the positive-radius domain. -/
theorem mem_positiveRadiusMeridian_iff (x : ℝ^2) :
    x ∈ positiveRadiusMeridian ↔ 0 < x (0 : Fin 2) := Iff.rfl

/-- A point on the symmetry axis with axial coordinate `z`. -/
def axisPoint (z : ℝ) : ℝ^2 :=
  WithLp.toLp 2 ![0, z]

/-- The radial coordinate of an axis point is zero. -/
@[simp]
theorem axisPoint_apply_zero (z : ℝ) :
    axisPoint z (0 : Fin 2) = 0 := by
  simp [axisPoint]

/-- The axial coordinate of an axis point is its parameter. -/
@[simp]
theorem axisPoint_apply_one (z : ℝ) :
    axisPoint z (1 : Fin 2) = z := by
  simp [axisPoint]

/-- Package a radial and an axial scalar flux as a vector field on meridian space. -/
def meridianFlux (qR qZ : ℝ^2 → ℝ) (x : ℝ^2) : ℝ^2 :=
  WithLp.toLp 2 ![qR x, qZ x]

/-- The meridian operator corresponding to a Laplacian in four radial dimensions and one
axial dimension:
`∂_{rr}φ + 3r⁻¹∂_rφ + ∂_{zz}φ`. -/
def reducedLaplacian
    (φ : ℝ^2 → ℝ) (x : ℝ^2) : ℝ :=
  partialDeriv (0 : Fin 2)
      (fun y ↦ partialDeriv (0 : Fin 2) φ y) x +
    3 / x (0 : Fin 2) * partialDeriv (0 : Fin 2) φ x +
    partialDeriv (1 : Fin 2)
      (fun y ↦ partialDeriv (1 : Fin 2) φ y) x

/-- Reduced swirl, azimuthal vorticity, and streamfunction variables. -/
structure ReducedFields where
  /-- Desingularized swirl `u₁ = u_θ/r`. -/
  swirl : ℝ^2 → ℝ → ℝ
  /-- Desingularized azimuthal vorticity `ω₁ = ω_θ/r`. -/
  vorticity : ℝ^2 → ℝ → ℝ
  /-- Desingularized streamfunction `ψ₁`, with scalar Stokes streamfunction
  `ψ = r²ψ₁`. -/
  streamFunction : ℝ^2 → ℝ → ℝ

/-- Radial velocity `u_r = -r∂_zψ₁`. -/
def reducedRadialVelocity
    (fields : ReducedFields) (x : ℝ^2) (t : ℝ) : ℝ :=
  -x (0 : Fin 2) *
    partialDeriv (1 : Fin 2) (fun y ↦ fields.streamFunction y t) x

/-- Axial velocity `u_z = 2ψ₁ + r∂_rψ₁`. -/
def reducedAxialVelocity
    (fields : ReducedFields) (x : ℝ^2) (t : ℝ) : ℝ :=
  2 * fields.streamFunction x t +
    x (0 : Fin 2) *
      partialDeriv (0 : Fin 2) (fun y ↦ fields.streamFunction y t) x

/-- Meridian velocity `(u_r,u_z)` reconstructed from `ψ₁`. -/
def reducedMeridianVelocity
    (fields : ReducedFields) (x : ℝ^2) (t : ℝ) : ℝ^2 :=
  meridianFlux
    (fun y ↦ reducedRadialVelocity fields y t)
    (fun y ↦ reducedAxialVelocity fields y t) x

/-- Radial component of the reconstructed meridian velocity. -/
@[simp]
theorem reducedMeridianVelocity_radial
    (fields : ReducedFields) (x : ℝ^2) (t : ℝ) :
    reducedMeridianVelocity fields x t (0 : Fin 2) =
      reducedRadialVelocity fields x t := by
  simp [reducedMeridianVelocity, meridianFlux]

/-- Axial component of the reconstructed meridian velocity. -/
@[simp]
theorem reducedMeridianVelocity_axial
    (fields : ReducedFields) (x : ℝ^2) (t : ℝ) :
    reducedMeridianVelocity fields x t (1 : Fin 2) =
      reducedAxialVelocity fields x t := by
  simp [reducedMeridianVelocity, meridianFlux]

/-- The radial velocity vanishes on the symmetry axis. -/
@[simp]
theorem reducedRadialVelocity_axisPoint
    (fields : ReducedFields) (z t : ℝ) :
    reducedRadialVelocity fields (axisPoint z) t = 0 := by
  simp [reducedRadialVelocity]

/-- The axis value of the axial velocity is `2ψ₁`. -/
@[simp]
theorem reducedAxialVelocity_axisPoint
    (fields : ReducedFields) (z t : ℝ) :
    reducedAxialVelocity fields (axisPoint z) t =
      2 * fields.streamFunction (axisPoint z) t := by
  simp [reducedAxialVelocity]

/-- Axis-value extension of the radial-four-plus-axial Laplacian.

Away from the axis this is `∂_{rr} + 3r⁻¹∂_r + ∂_{zz}`. At the axis it
assigns `4∂_{rr} + ∂_{zz}`, the limiting value for a sufficiently smooth
radially even profile. This definition alone does not assert that the
piecewise expression is continuous; that interpretation also requires
radial parity and regularity hypotheses. -/
def axisExtendedLaplacian
    (f : ℝ^2 → ℝ) (x : ℝ^2) : ℝ :=
  if x (0 : Fin 2) = 0 then
    4 * partialDeriv (0 : Fin 2)
          (fun y ↦ partialDeriv (0 : Fin 2) f y) x +
      partialDeriv (1 : Fin 2)
          (fun y ↦ partialDeriv (1 : Fin 2) f y) x
  else
    reducedLaplacian f x

/-- Off the axis, the axis-extended operator is the ordinary reduced
Laplacian. -/
theorem axisExtendedLaplacian_of_ne_zero
    (f : ℝ^2 → ℝ) (x : ℝ^2)
    (hr : x (0 : Fin 2) ≠ 0) :
    axisExtendedLaplacian f x =
      reducedLaplacian f x := by
  simp [axisExtendedLaplacian, hr]

/-- On the axis, the axis-extended operator has coefficient four on the radial
second derivative. -/
theorem axisExtendedLaplacian_of_eq_zero
    (f : ℝ^2 → ℝ) (x : ℝ^2)
    (hr : x (0 : Fin 2) = 0) :
    axisExtendedLaplacian f x =
      4 * partialDeriv (0 : Fin 2)
          (fun y ↦ partialDeriv (0 : Fin 2) f y) x +
        partialDeriv (1 : Fin 2)
          (fun y ↦ partialDeriv (1 : Fin 2) f y) x := by
  simp [axisExtendedLaplacian, hr]

/-- Axis formula for the axis-extended operator. -/
@[simp]
theorem axisExtendedLaplacian_axisPoint
    (f : ℝ^2 → ℝ) (z : ℝ) :
    axisExtendedLaplacian f (axisPoint z) =
      4 * partialDeriv (0 : Fin 2)
          (fun y ↦ partialDeriv (0 : Fin 2) f y) (axisPoint z) +
        partialDeriv (1 : Fin 2)
          (fun y ↦ partialDeriv (1 : Fin 2) f y) (axisPoint z) := by
  exact axisExtendedLaplacian_of_eq_zero f (axisPoint z) (by simp)

/-- Pointwise transport of a scalar by the reduced meridian velocity. -/
def reducedAdvection
    (fields : ReducedFields) (f : ℝ^2 → ℝ)
    (x : ℝ^2) (t : ℝ) : ℝ :=
  advectiveDerivative
    (fun y ↦ reducedMeridianVelocity fields y t) f x

/-- Coordinate expansion of reduced meridian advection. -/
theorem reducedAdvection_eq_radial_add_axial
    (fields : ReducedFields) (f : ℝ^2 → ℝ)
    (x : ℝ^2) (t : ℝ) :
    reducedAdvection fields f x t =
      reducedRadialVelocity fields x t *
          partialDeriv (0 : Fin 2) f x +
        reducedAxialVelocity fields x t *
          partialDeriv (1 : Fin 2) f x := by
  rw [reducedAdvection, advectiveDerivative_eq_sum_mul_partialDeriv]
  simp [Fin.sum_univ_two]

/-- Stretching source `2u₁∂_zψ₁` in the reduced swirl equation. -/
def reducedSwirlSource
    (fields : ReducedFields) (x : ℝ^2) (t : ℝ) : ℝ :=
  2 * fields.swirl x t *
    partialDeriv (1 : Fin 2) (fun y ↦ fields.streamFunction y t) x

/-- Quadratic source `2u₁∂_z u₁` in the reduced vorticity equation. -/
def reducedVorticitySource
    (fields : ReducedFields) (x : ℝ^2) (t : ℝ) : ℝ :=
  2 * fields.swirl x t *
    partialDeriv (1 : Fin 2) (fun y ↦ fields.swirl y t) x

/-- Pointwise defect in the reduced streamfunction equation. -/
def reducedStreamFunctionResidual
    (fields : ReducedFields) (x : ℝ^2) (t : ℝ) : ℝ :=
  -reducedLaplacian
      (fun y ↦ fields.streamFunction y t) x -
    fields.vorticity x t

/-- Radial meridian velocity `uʳ = -r∂zψ₁`. -/
def radialVelocity (psiBullet : ℝ^2 → ℝ → ℝ) :
    ℝ^2 → ℝ → ℝ :=
  fun x t ↦ -meridianR x * partialDeriv 1 (fun y ↦ psiBullet y t) x

/-- Axial meridian velocity `uᶻ = 2ψ₁ + r∂rψ₁`. -/
def axialVelocity (psiBullet : ℝ^2 → ℝ → ℝ) :
    ℝ^2 → ℝ → ℝ :=
  fun x t ↦ 2 * psiBullet x t + meridianR x * partialDeriv 0 (fun y ↦ psiBullet y t) x

/-- Swirl residual `∂tu₁ + uʳ∂ru₁ + uᶻ∂zu₁ - 2u₁∂zψ₁`. -/
def axisymmetricSwirlResidual
    (uBullet psiBullet : ℝ^2 → ℝ → ℝ) : ℝ^2 → ℝ → ℝ :=
  fun x t ↦
    deriv (fun s ↦ uBullet x s) t
    + radialVelocity psiBullet x t * partialDeriv 0 (fun y ↦ uBullet y t) x
    + axialVelocity psiBullet x t * partialDeriv 1 (fun y ↦ uBullet y t) x
    - 2 * uBullet x t * partialDeriv 1 (fun y ↦ psiBullet y t) x

/-- Vorticity residual `∂tω₁ + uʳ∂rω₁ + uᶻ∂zω₁ - 2u₁∂zu₁`. -/
def axisymmetricVorticityResidual
    (uBullet omegaBullet psiBullet : ℝ^2 → ℝ → ℝ) : ℝ^2 → ℝ → ℝ :=
  fun x t ↦
    deriv (fun s ↦ omegaBullet x s) t
    + radialVelocity psiBullet x t * partialDeriv 0 (fun y ↦ omegaBullet y t) x
    + axialVelocity psiBullet x t * partialDeriv 1 (fun y ↦ omegaBullet y t) x
    - 2 * uBullet x t * partialDeriv 1 (fun y ↦ uBullet y t) x

/-- Stream-vorticity residual `-(∂rr + 3∂r/r + ∂zz)ψ₁ - ω₁`. -/
def axisymmetricStreamResidual
    (omegaBullet psiBullet : ℝ^2 → ℝ → ℝ) : ℝ^2 → ℝ → ℝ :=
  fun x t ↦
    signedElliptic classicalAxisymmetricDifferential (fun y ↦ psiBullet y t) x - omegaBullet x t

/-- The physical elliptic operator has the paper's radial formula, including
the assigned axis value. This is an algebraic identity, not an axis-limit theorem. -/
theorem axisymmetricLaplacian_eq_axisExtendedLaplacian (f : ℝ^2 → ℝ) (x : ℝ^2) :
    axisymmetricLaplacian classicalAxisymmetricDifferential f x =
      axisExtendedLaplacian f x := by
  dsimp only [axisymmetricLaplacian, classicalAxisymmetricDifferential,
    regularizedProfileDROverR, profileDRR, profileDZZ]
  unfold profileDR profileDZ axisExtendedLaplacian
    reducedLaplacian meridianR
  split_ifs with hx
  · ring
  · field_simp [hx]

namespace ReducedFields

/-- The complete reduced axisymmetric Euler system holds on `domain × I`. -/
def IsSolutionOn
    (F : ReducedFields)
    (domain : Set (ℝ^2)) (I : Set ℝ) : Prop :=
  (∀ x ∈ domain, ∀ t ∈ I,
    axisymmetricSwirlResidual F.swirl F.streamFunction x t = 0) ∧
  (∀ x ∈ domain, ∀ t ∈ I,
    axisymmetricVorticityResidual F.swirl F.vorticity F.streamFunction x t = 0) ∧
  (∀ x ∈ domain, ∀ t ∈ I,
    axisymmetricStreamResidual F.vorticity F.streamFunction x t = 0)

/-- A reduced-system solution restricts to any smaller spatial and temporal domains. -/
theorem IsSolutionOn.mono
    {F : ReducedFields}
    {domain domain' : Set (ℝ^2)} {I I' : Set ℝ}
    (hF : F.IsSolutionOn domain I)
    (hdomain : domain' ⊆ domain) (hI : I' ⊆ I) :
    F.IsSolutionOn domain' I' := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx t ht
    exact hF.1 x (hdomain hx) t (hI ht)
  · intro x hx t ht
    exact hF.2.1 x (hdomain hx) t (hI ht)
  · intro x hx t ht
    exact hF.2.2 x (hdomain hx) t (hI ht)

end ReducedFields

end Euler.Axisymmetric
