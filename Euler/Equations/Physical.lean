/-
Copyright (c) 2026 Robert Joseph George and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/

module

public import Euler.Equations.Reduced

/-!
# Convection-varied Euler equations

These are the reduced equations used in Appendices A and C. The parameter
`eps` multiplies transport; `eps = 1` gives the Euler equations.
`ReducedFields` contains the swirl, vorticity, and streamfunction. Regularity
assumptions appear in the theorems that differentiate these equations.
-/

@[expose] public section

noncomputable section

open Euler.Calculus
open Euler.Coordinates

namespace Euler

/-! ## Convection-varied axisymmetric Euler -/

/--
Convection-varied swirl residual, with `eps = 1` recovering the full axisymmetric Euler
transport strength.
-/
def convectionVariedSwirlResidual (eps : ℝ)
    (uBullet psiBullet : ℝ^2 → ℝ → ℝ) : ℝ^2 → ℝ → ℝ :=
  fun x t ↦
    deriv (fun s ↦ uBullet x s) t
    + eps * Euler.Axisymmetric.radialVelocity psiBullet x t * partialDeriv 0 (fun y ↦ uBullet y t) x
    + eps * Euler.Axisymmetric.axialVelocity psiBullet x t * partialDeriv 1 (fun y ↦ uBullet y t) x
    - 2 * uBullet x t * partialDeriv 1 (fun y ↦ psiBullet y t) x

/--
Convection-varied vorticity residual, with `eps = 1` recovering the full axisymmetric Euler
transport strength.
-/
def convectionVariedVorticityResidual (eps : ℝ)
    (uBullet omegaBullet psiBullet : ℝ^2 → ℝ → ℝ) : ℝ^2 → ℝ → ℝ :=
  fun x t ↦
    deriv (fun s ↦ omegaBullet x s) t
    + eps * Euler.Axisymmetric.radialVelocity psiBullet x t *
        partialDeriv 0 (fun y ↦ omegaBullet y t) x
    + eps * Euler.Axisymmetric.axialVelocity psiBullet x t *
        partialDeriv 1 (fun y ↦ omegaBullet y t) x
    - 2 * uBullet x t * partialDeriv 1 (fun y ↦ uBullet y t) x

end Euler

namespace Euler.Axisymmetric.ReducedFields

/-- The complete convection-varied system holds on `Omega x I`. -/
def IsConvectionVariedSolutionOn
    (F : Euler.Axisymmetric.ReducedFields) (eps : ℝ)
    (Omega : Set (ℝ^2)) (I : Set ℝ) : Prop :=
  (∀ x ∈ Omega, ∀ t ∈ I,
      convectionVariedSwirlResidual eps F.swirl F.streamFunction x t = 0) ∧
    (∀ x ∈ Omega, ∀ t ∈ I,
      convectionVariedVorticityResidual eps
        F.swirl F.vorticity F.streamFunction x t = 0) ∧
      (∀ x ∈ Omega, ∀ t ∈ I,
        axisymmetricStreamResidual F.vorticity F.streamFunction x t = 0)

/-- A convection-varied solution on `Ω ×ˢ I` is a solution on every smaller `Ω' ×ˢ I'`. -/
theorem IsConvectionVariedSolutionOn.mono
    {F : Euler.Axisymmetric.ReducedFields} {eps : ℝ}
    {Omega Omega' : Set (ℝ^2)} {I I' : Set ℝ}
    (hF : F.IsConvectionVariedSolutionOn eps Omega I)
    (hOmega : Omega' ⊆ Omega) (hI : I' ⊆ I) :
    F.IsConvectionVariedSolutionOn eps Omega' I' := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx t ht
    exact hF.1 x (hOmega hx) t (hI ht)
  · intro x hx t ht
    exact hF.2.1 x (hOmega hx) t (hI ht)
  · intro x hx t ht
    exact hF.2.2 x (hOmega hx) t (hI ht)

end Euler.Axisymmetric.ReducedFields

namespace Euler

/-- At `eps = 1`, the convection-varied swirl residual is the full axisymmetric residual. -/
theorem convectionVariedSwirlResidual_eps_one
    (uBullet psiBullet : ℝ^2 → ℝ → ℝ) :
    convectionVariedSwirlResidual 1 uBullet psiBullet
      = Euler.Axisymmetric.axisymmetricSwirlResidual uBullet psiBullet := by
  funext x t
  simp [convectionVariedSwirlResidual, Euler.Axisymmetric.axisymmetricSwirlResidual]

/-- At `eps = 1`, the convection-varied vorticity residual is the full axisymmetric residual. -/
theorem convectionVariedVorticityResidual_eps_one
    (uBullet omegaBullet psiBullet : ℝ^2 → ℝ → ℝ) :
    convectionVariedVorticityResidual 1 uBullet omegaBullet psiBullet
      = Euler.Axisymmetric.axisymmetricVorticityResidual uBullet omegaBullet psiBullet := by
  funext x t
  simp [convectionVariedVorticityResidual, Euler.Axisymmetric.axisymmetricVorticityResidual]

end Euler
