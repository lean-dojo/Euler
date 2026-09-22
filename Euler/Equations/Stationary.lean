/-
Copyright (c) 2026 Robert Joseph George and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/

module

public import Euler.Calculus.AxisymmetricProfile

/-!
# Stationary profile equations

The stationary system consists of two transport equations and a signed Poisson
equation.
-/

@[expose] public section

open Euler.Calculus
open Euler.Coordinates

noncomputable section

namespace Euler

/-- The `Z`-transport coefficient shared by the two profile equations. -/
def axialTransport (eps lam C : ℝ) (D : AxisymmetricDifferential)
    (Ψ : (ℝ^2 → ℝ)) : (ℝ^2 → ℝ) :=
  fun x ↦ C + lam * meridianZ x + eps * (2 * Ψ x + meridianR x * D.DR Ψ x)

/-- The common coefficient `λ - ε Ψ_Z` multiplying `R ∂R`
in the swirl and vorticity profile equations. -/
def radialTransportFactor (eps lam : ℝ) (D : AxisymmetricDifferential)
    (Ψ : (ℝ^2 → ℝ)) : (ℝ^2 → ℝ) :=
  fun x ↦ lam - eps * D.DZ Ψ x

/--
Residual of the first stationary profile equation:

`U + R U_R (λ - ε Ψ_Z) + U_Z (c + λ Z + ε(2Ψ + R Ψ_R)) - 2 U Ψ_Z`.
-/
def swirlResidual (eps lam C : ℝ) (D : AxisymmetricDifferential)
    (U Ψ : (ℝ^2 → ℝ)) : (ℝ^2 → ℝ) :=
  fun x ↦
    U x
    + meridianR x * D.DR U x * radialTransportFactor eps lam D Ψ x
    + D.DZ U x * axialTransport eps lam C D Ψ x
    - 2 * U x * D.DZ Ψ x

/--
Residual of the second stationary profile equation:

`(λ+1)Ω + R Ω_R (λ - ε Ψ_Z) + Ω_Z (c + λ Z + ε(2Ψ + R Ψ_R)) - 2 U U_Z`.
-/
def vorticityResidual (eps lam C : ℝ) (D : AxisymmetricDifferential)
    (U Ψ Ω : (ℝ^2 → ℝ)) : (ℝ^2 → ℝ) :=
  fun x ↦
    (lam + 1) * Ω x
    + meridianR x * D.DR Ω x * radialTransportFactor eps lam D Ψ x
    + D.DZ Ω x * axialTransport eps lam C D Ψ x
    - 2 * U x * D.DZ U x

/-- The three scalar fields in a stationary profile. -/
structure Profile where
  /-- Stationary reduced swirl profile. -/
  U : (ℝ^2 → ℝ)
  /-- Stationary streamfunction profile. -/
  Ψ : (ℝ^2 → ℝ)
  /-- Stationary reduced vorticity profile. -/
  Ω : (ℝ^2 → ℝ)

namespace Profile

/-- All three stationary profile equations hold on `s`. -/
def IsStationaryOn
    (F : Profile) (eps lam C : ℝ)
    (D : AxisymmetricDifferential) (s : Set (ℝ^2)) : Prop :=
  (∀ x ∈ s, signedElliptic D F.Ψ x = F.Ω x) ∧
    (∀ x ∈ s, swirlResidual eps lam C D F.U F.Ψ x = 0) ∧
      (∀ x ∈ s, vorticityResidual eps lam C D F.U F.Ψ F.Ω x = 0)

end Profile

end Euler
