module

public import Review.Definitions.Calculus.Operators
public import Review.Definitions.Calculus.AxisymmetricProfile

/-! # Time-dependent reduced fields -/

@[expose] public noncomputable section

open Euler.Calculus

open Euler.Coordinates (meridianR)

namespace Euler.Axisymmetric

/-- Open meridian half-plane. -/
def positiveRadiusMeridian : Set (ℝ^2) := {x | 0 < x (0 : Fin 2)}

/-- A point on the symmetry axis with axial coordinate `z`. -/
def axisPoint (z : ℝ) : ℝ^2 :=
  WithLp.toLp 2 ![0, z]

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

/-- Pointwise transport of a scalar by the reduced meridian velocity. -/
def reducedAdvection
    (fields : ReducedFields) (f : ℝ^2 → ℝ)
    (x : ℝ^2) (t : ℝ) : ℝ :=
  advectiveDerivative
    (fun y ↦ reducedMeridianVelocity fields y t) f x

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

/-- Stream-vorticity residual `-(∂rr + 3∂r/r + ∂zz)ψ₁ - ω₁`. -/
def axisymmetricStreamResidual
    (omegaBullet psiBullet : ℝ^2 → ℝ → ℝ) : ℝ^2 → ℝ → ℝ :=
  fun x t ↦
    signedElliptic classicalAxisymmetricDifferential (fun y ↦ psiBullet y t) x - omegaBullet x t

end Euler.Axisymmetric

end
