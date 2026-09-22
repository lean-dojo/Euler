module

public import Review.Definitions.Equations.Reduced

/-! # Physical equations -/

@[expose] public noncomputable section

open Euler.Calculus

open Euler.Coordinates

namespace Euler

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

end Euler.Axisymmetric.ReducedFields

end
