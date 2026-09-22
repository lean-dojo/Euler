/-
Copyright (c) 2026 Robert Joseph George and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/

module

public import Euler.Rescaling.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Differentiating at a fixed physical point

In Appendix D, a fixed physical point `X` has rescaled coordinate
`x = L⁻¹ (X - Z e_z)`. Its derivative in rescaled time is `λx + C e_z`.
We apply the chain rule, including the amplitude and time changes, to recover
the field's physical time derivative.
-/

@[expose] public section

namespace Euler.Axisymmetric

open Euler.Similarity

noncomputable section

/-- The rescaled coordinate of a fixed physical point. -/
def inverseRescalingMap
    (data : Rescaling) (X : ℝ^2) (τ : ℝ) : ℝ^2 :=
  (data.spatialScale τ)⁻¹ • (X - rescalingShift data τ)

/-- The inverse spatial map recovers the rescaled point. -/
theorem inverseRescalingMap_rescalingMap
    (data : Rescaling) (x : ℝ^2) (τ : ℝ)
    (hscale : data.spatialScale τ ≠ 0) :
    inverseRescalingMap data (rescalingMap data x τ) τ = x := by
  simp [inverseRescalingMap, rescalingMap, dynamicAffinePoint,
    affineDilation, smul_smul, hscale]

/-- The forward spatial map recovers the physical point. -/
theorem rescalingMap_inverseRescalingMap
    (data : Rescaling) (X : ℝ^2) (τ : ℝ)
    (hscale : data.spatialScale τ ≠ 0) :
    rescalingMap data (inverseRescalingMap data X τ) τ = X := by
  simp [inverseRescalingMap, rescalingMap, dynamicAffinePoint,
    affineDilation, smul_smul, hscale]

/-- At fixed physical coordinates, the rescaled coordinate velocity is `λx + C e_z`. -/
theorem hasDerivAt_inverseRescalingMap
    (data : Rescaling) (X : ℝ^2) (τ : ℝ)
    (hscale : data.spatialScale τ ≠ 0)
    (hlaws : Rescaling.SatisfiesScaleLawsAt data τ) :
    HasDerivAt (inverseRescalingMap data X)
      (data.spatialRate τ • inverseRescalingMap data X τ +
        data.axialDrift τ • axialUnit) τ := by
  have hshift : HasDerivAt (fun s ↦ X - rescalingShift data s)
      (0 - (-data.axialDrift τ * data.spatialScale τ) • axialUnit) τ :=
    (hasDerivAt_const τ X).sub hlaws.axialShift_hasDerivAt
  apply ((hlaws.spatialScale_hasDerivAt.inv hscale).smul hshift).congr_deriv
  ext i
  simp only [inverseRescalingMap, Pi.inv_apply, PiLp.add_apply, PiLp.smul_apply,
    PiLp.sub_apply, PiLp.zero_apply, smul_eq_mul]
  field_simp [hscale]
  ring

/-- The scalar chain rule at a fixed physical point gives the affine frame transport. -/
theorem hasDerivAt_comp_inverseRescalingMap
    (data : Rescaling) (field : ℝ^2 → ℝ → ℝ)
    (X : ℝ^2) (τ : ℝ)
    (hscale : data.spatialScale τ ≠ 0)
    (hlaws : Rescaling.SatisfiesScaleLawsAt data τ)
    (hfield : DifferentiableAt ℝ (Function.uncurry field)
      (inverseRescalingMap data X τ, τ)) :
    HasDerivAt (fun s ↦ field (inverseRescalingMap data X s) s)
      (deriv (field (inverseRescalingMap data X τ)) τ +
        (data.spatialRate τ * inverseRescalingMap data X τ 0) *
          partialDeriv 0 (fun y ↦ field y τ) (inverseRescalingMap data X τ) +
        (data.spatialRate τ * inverseRescalingMap data X τ 1 +
          data.axialDrift τ) *
          partialDeriv 1 (fun y ↦ field y τ) (inverseRescalingMap data X τ)) τ := by
  have hpath : HasDerivAt (fun s ↦ (inverseRescalingMap data X s, s))
      (data.spatialRate τ • inverseRescalingMap data X τ +
        data.axialDrift τ • axialUnit, 1) τ :=
    (hasDerivAt_inverseRescalingMap data X τ hscale hlaws).prodMk
      (hasDerivAt_id τ)
  apply (hfield.hasFDerivAt.comp_hasDerivAt
    (f := fun s ↦ (inverseRescalingMap data X s, s)) τ hpath).congr_deriv
  rw [fderiv_uncurry_apply_prod _ _ _ _ _ hfield,
    fderiv_apply_eq_sum_partialDeriv_mul, Fin.sum_univ_two]
  simp [smul_eq_mul]
  ring

/-- A scalar field reconstructed at a physical point and physical time. -/
def physicalScalarPullback
    (data : Rescaling) (field : ℝ^2 → ℝ → ℝ)
    (amplitude rescaledTime : ℝ → ℝ) (X : ℝ^2) (t : ℝ) : ℝ :=
  amplitude (rescaledTime t) *
    field (inverseRescalingMap data X (rescaledTime t)) (rescaledTime t)

/-- Amplitude normalization and the physical clock multiply the frame derivative.
Taking the amplitude to be `su` or `sω` gives the two physical time derivatives. -/
theorem hasDerivAt_physicalScalarPullback
    (data : Rescaling) (field : ℝ^2 → ℝ → ℝ)
    (amplitude rescaledTime : ℝ → ℝ) (X : ℝ^2) (t rate clockRate : ℝ)
    (hscale : data.spatialScale (rescaledTime t) ≠ 0)
    (hlaws : Rescaling.SatisfiesScaleLawsAt data (rescaledTime t))
    (hfield : DifferentiableAt ℝ (Function.uncurry field)
      (inverseRescalingMap data X (rescaledTime t), rescaledTime t))
    (hamplitude : HasDerivAt amplitude
      (-rate * amplitude (rescaledTime t)) (rescaledTime t))
    (hclock : HasDerivAt rescaledTime clockRate t) :
    HasDerivAt (physicalScalarPullback data field amplitude rescaledTime X)
      (amplitude (rescaledTime t) * clockRate *
        (deriv (field (inverseRescalingMap data X (rescaledTime t))) (rescaledTime t) +
          (data.spatialRate (rescaledTime t) *
              inverseRescalingMap data X (rescaledTime t) 0) *
            partialDeriv 0 (fun y ↦ field y (rescaledTime t))
              (inverseRescalingMap data X (rescaledTime t)) +
          (data.spatialRate (rescaledTime t) *
              inverseRescalingMap data X (rescaledTime t) 1 +
            data.axialDrift (rescaledTime t)) *
            partialDeriv 1 (fun y ↦ field y (rescaledTime t))
              (inverseRescalingMap data X (rescaledTime t)) -
          rate * field (inverseRescalingMap data X (rescaledTime t)) (rescaledTime t))) t := by
  have hframe := hasDerivAt_comp_inverseRescalingMap
    data field X (rescaledTime t) hscale hlaws hfield
  apply ((hamplitude.mul hframe).comp t hclock).congr_deriv
  ring

end

end Euler.Axisymmetric
