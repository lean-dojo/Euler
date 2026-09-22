/-
Copyright (c) 2026 Robert Joseph George and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/

module

public import Euler.Rescaling.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Derivatives of the rescaled fields

Here we work out the derivatives used in Proposition S8. Differentiating
the moving coordinates gives the extra transport terms. Spatial derivatives
give the scale factors in the velocity, nonlinear terms, and elliptic equation.
The elliptic calculation in this file is for nonzero radius.
-/

@[expose] public section

namespace Euler.Axisymmetric

open Euler.Similarity

noncomputable section

/-- A spatial derivative of dynamically rescaled swirl carries amplitude
`A` and one spatial-scale factor `L`. -/
theorem partialDeriv_rescaledSwirl
    (data : Rescaling) (fields : ReducedFields)
    (i : Fin 2) (x : ℝ^2) (τ : ℝ)
    (hswirl :
      DifferentiableAt ℝ
        (fun y ↦ fields.swirl y (data.physicalTime τ))
        (rescalingMap data x τ)) :
    partialDeriv i
        (fun y ↦ rescaledSwirl data fields y τ) x =
      data.swirlScale τ * data.spatialScale τ *
        partialDeriv i
          (fun y ↦ fields.swirl y (data.physicalTime τ))
          (rescalingMap data x τ) := by
  simpa [rescaledSwirl, dynamicAffinePullback,
    rescalingMap, dynamicAffinePoint, smul_eq_mul] using
    partialDeriv_const_mul_comp_affineDilation i
      (fun y ↦ fields.swirl y (data.physicalTime τ))
      (data.swirlScale τ) (data.spatialScale τ)
      (rescalingShift data τ) x hswirl

/-- A spatial derivative of dynamically rescaled vorticity carries amplitude
`Aω` and one spatial-scale factor `L`. -/
theorem partialDeriv_rescaledVorticity
    (data : Rescaling) (fields : ReducedFields)
    (i : Fin 2) (x : ℝ^2) (τ : ℝ)
    (hvorticity :
      DifferentiableAt ℝ
        (fun y ↦ fields.vorticity y (data.physicalTime τ))
        (rescalingMap data x τ)) :
    partialDeriv i
        (fun y ↦ rescaledVorticity data fields y τ) x =
      data.vorticityScale τ * data.spatialScale τ *
        partialDeriv i
          (fun y ↦ fields.vorticity y (data.physicalTime τ))
          (rescalingMap data x τ) := by
  simpa [rescaledVorticity, dynamicAffinePullback,
    rescalingMap, dynamicAffinePoint, smul_eq_mul] using
    partialDeriv_const_mul_comp_affineDilation i
      (fun y ↦ fields.vorticity y (data.physicalTime τ))
      (data.vorticityScale τ) (data.spatialScale τ)
      (rescalingShift data τ) x hvorticity

/-- A spatial derivative of the dynamically rescaled streamfunction carries
amplitude `A/L` and one spatial-scale factor `L`. -/
theorem partialDeriv_rescaledStreamFunction
    (data : Rescaling) (fields : ReducedFields)
    (i : Fin 2) (x : ℝ^2) (τ : ℝ)
    (hstream :
      DifferentiableAt ℝ
        (fun y ↦ fields.streamFunction y (data.physicalTime τ))
        (rescalingMap data x τ)) :
    partialDeriv i
        (fun y ↦ rescaledStreamFunction data fields y τ) x =
      (data.swirlScale τ / data.spatialScale τ) *
        data.spatialScale τ *
        partialDeriv i
          (fun y ↦ fields.streamFunction y (data.physicalTime τ))
          (rescalingMap data x τ) := by
  simpa [rescaledStreamFunction,
    rescalingMap, dynamicAffinePoint] using
    partialDeriv_const_mul_comp_affineDilation i
      (fun y ↦ fields.streamFunction y (data.physicalTime τ))
      (data.swirlScale τ / data.spatialScale τ)
      (data.spatialScale τ) (rescalingShift data τ) x hstream

/-- A first derivative of an amplitude-scaled dynamic reduced pullback
carries one spatial-scale factor. -/
theorem partialDeriv_const_mul_comp_rescalingMap
    (data : Rescaling) (profile : ℝ^2 → ℝ)
    (amplitude : ℝ) (i : Fin 2) (x : ℝ^2) (τ : ℝ)
    (hprofile :
      DifferentiableAt ℝ profile
        (rescalingMap data x τ)) :
    partialDeriv i
        (fun y ↦ amplitude *
          profile (rescalingMap data y τ)) x =
      amplitude * data.spatialScale τ *
        partialDeriv i profile
          (rescalingMap data x τ) := by
  simpa [rescalingMap, dynamicAffinePoint] using
    partialDeriv_const_mul_comp_affineDilation
      i profile amplitude (data.spatialScale τ)
      (rescalingShift data τ) x hprofile

/-- A second derivative of an amplitude-scaled dynamic affine pullback
carries two spatial-scale factors. -/
theorem partialDeriv_partialDeriv_const_mul_comp_rescalingMap
    (data : Rescaling) (profile : ℝ^2 → ℝ)
    (amplitude : ℝ) (i k : Fin 2) (x : ℝ^2) (τ : ℝ)
    (hprofile : ContDiff ℝ 2 profile) :
    partialDeriv i
        (fun y ↦ partialDeriv k
          (fun z ↦ amplitude *
            profile (rescalingMap data z τ)) y) x =
      amplitude * data.spatialScale τ ^ 2 *
        partialDeriv i (fun y ↦ partialDeriv k profile y)
          (rescalingMap data x τ) := by
  simpa [rescalingMap, dynamicAffinePoint] using
    partialDeriv_partialDeriv_const_mul_comp_affineDilation
      i k profile amplitude (data.spatialScale τ)
      (rescalingShift data τ) x hprofile

/-- Off the axis, the radial-four-plus-axial operator scales by
`amplitude * L²` under the dynamic affine similarity map. -/
theorem reducedLaplacian_const_mul_comp_rescalingMap
    (data : Rescaling) (profile : ℝ^2 → ℝ)
    (amplitude : ℝ) (x : ℝ^2) (τ : ℝ)
    (hprofile : ContDiff ℝ 2 profile)
    (hscale : data.spatialScale τ ≠ 0)
    (hr : x (0 : Fin 2) ≠ 0) :
    reducedLaplacian
        (fun y ↦ amplitude *
          profile (rescalingMap data y τ)) x =
      amplitude * data.spatialScale τ ^ 2 *
        reducedLaplacian profile
          (rescalingMap data x τ) := by
  have hdiff :
      DifferentiableAt ℝ profile
        (rescalingMap data x τ) :=
    (hprofile.differentiable (by norm_num)).differentiableAt
  unfold reducedLaplacian
  rw [partialDeriv_partialDeriv_const_mul_comp_rescalingMap
    data profile amplitude (0 : Fin 2) (0 : Fin 2) x τ hprofile]
  rw [partialDeriv_const_mul_comp_rescalingMap
    data profile amplitude (0 : Fin 2) x τ hdiff]
  rw [partialDeriv_partialDeriv_const_mul_comp_rescalingMap
    data profile amplitude (1 : Fin 2) (1 : Fin 2) x τ hprofile]
  rw [rescalingMap_radial]
  field_simp

/-- The dynamically rescaled radial velocity has amplitude `A/L`. -/
theorem reducedRadialVelocity_rescaledFields
    (data : Rescaling) (fields : ReducedFields)
    (x : ℝ^2) (τ : ℝ)
    (hstream :
      DifferentiableAt ℝ
        (fun y ↦ fields.streamFunction y (data.physicalTime τ))
        (rescalingMap data x τ)) :
    reducedRadialVelocity
        (rescaledFields data fields) x τ =
      (data.swirlScale τ / data.spatialScale τ) *
        reducedRadialVelocity fields
          (rescalingMap data x τ)
          (data.physicalTime τ) := by
  rw [reducedRadialVelocity]
  change
    -x (0 : Fin 2) *
        partialDeriv (1 : Fin 2)
          (fun y ↦ rescaledStreamFunction data fields y τ) x =
      _
  rw [partialDeriv_rescaledStreamFunction
    data fields (1 : Fin 2) x τ hstream]
  rw [reducedRadialVelocity, rescalingMap_radial]
  ring

/-- The dynamically rescaled axial velocity has amplitude `A/L`. -/
theorem reducedAxialVelocity_rescaledFields
    (data : Rescaling) (fields : ReducedFields)
    (x : ℝ^2) (τ : ℝ)
    (hstream :
      DifferentiableAt ℝ
        (fun y ↦ fields.streamFunction y (data.physicalTime τ))
        (rescalingMap data x τ)) :
    reducedAxialVelocity
        (rescaledFields data fields) x τ =
      (data.swirlScale τ / data.spatialScale τ) *
        reducedAxialVelocity fields
          (rescalingMap data x τ)
          (data.physicalTime τ) := by
  rw [reducedAxialVelocity]
  change
    2 * rescaledStreamFunction data fields x τ +
        x (0 : Fin 2) *
          partialDeriv (0 : Fin 2)
            (fun y ↦ rescaledStreamFunction data fields y τ) x =
      _
  rw [partialDeriv_rescaledStreamFunction
    data fields (0 : Fin 2) x τ hstream]
  rw [reducedAxialVelocity, rescalingMap_radial]
  simp only [rescaledStreamFunction]
  ring

/-- The dynamically reconstructed meridian velocity has amplitude `A/L`. -/
theorem reducedMeridianVelocity_rescaledFields
    (data : Rescaling) (fields : ReducedFields)
    (x : ℝ^2) (τ : ℝ)
    (hstream :
      DifferentiableAt ℝ
        (fun y ↦ fields.streamFunction y (data.physicalTime τ))
        (rescalingMap data x τ)) :
    reducedMeridianVelocity
        (rescaledFields data fields) x τ =
      (data.swirlScale τ / data.spatialScale τ) •
        reducedMeridianVelocity fields
          (rescalingMap data x τ)
          (data.physicalTime τ) := by
  ext i
  fin_cases i
  · simpa [smul_eq_mul] using
      reducedRadialVelocity_rescaledFields
        data fields x τ hstream
  · simpa [smul_eq_mul] using
      reducedAxialVelocity_rescaledFields
        data fields x τ hstream

/-- The reduced swirl source of the dynamically rescaled fields has
amplitude `A²`. -/
theorem reducedSwirlSource_rescaledFields
    (data : Rescaling) (fields : ReducedFields)
    (x : ℝ^2) (τ : ℝ)
    (hscale : data.spatialScale τ ≠ 0)
    (hstream :
      DifferentiableAt ℝ
        (fun y ↦ fields.streamFunction y (data.physicalTime τ))
        (rescalingMap data x τ)) :
    reducedSwirlSource
        (rescaledFields data fields) x τ =
      data.swirlScale τ ^ 2 *
        reducedSwirlSource fields
          (rescalingMap data x τ)
          (data.physicalTime τ) := by
  unfold reducedSwirlSource
  change
    2 * rescaledSwirl data fields x τ *
        partialDeriv (1 : Fin 2)
          (fun y ↦ rescaledStreamFunction data fields y τ) x =
      _
  rw [partialDeriv_rescaledStreamFunction
    data fields (1 : Fin 2) x τ hstream]
  simp only [rescaledSwirl, dynamicAffinePullback,
    rescalingMap, smul_eq_mul]
  field_simp

/-- The reduced vorticity source of the dynamically rescaled fields has
amplitude `A²L`. -/
theorem reducedVorticitySource_rescaledFields
    (data : Rescaling) (fields : ReducedFields)
    (x : ℝ^2) (τ : ℝ)
    (hswirl :
      DifferentiableAt ℝ
        (fun y ↦ fields.swirl y (data.physicalTime τ))
        (rescalingMap data x τ)) :
    reducedVorticitySource
        (rescaledFields data fields) x τ =
      data.swirlScale τ ^ 2 * data.spatialScale τ *
        reducedVorticitySource fields
          (rescalingMap data x τ)
          (data.physicalTime τ) := by
  unfold reducedVorticitySource
  change
    2 * rescaledSwirl data fields x τ *
        partialDeriv (1 : Fin 2)
          (fun y ↦ rescaledSwirl data fields y τ) x =
      _
  rw [partialDeriv_rescaledSwirl
    data fields (1 : Fin 2) x τ hswirl]
  simp only [rescaledSwirl, dynamicAffinePullback,
    rescalingMap, smul_eq_mul]
  ring

/-- Under `Aω = AL`, the dynamically rescaled vorticity source has the
time-derivative amplitude `A Aω`. -/
theorem reducedVorticitySource_rescaledFields_compatible
    (data : Rescaling) (fields : ReducedFields)
    (x : ℝ^2) (τ : ℝ)
    (hcompat :
      data.vorticityScale τ =
        data.swirlScale τ * data.spatialScale τ)
    (hswirl :
      DifferentiableAt ℝ
        (fun y ↦ fields.swirl y (data.physicalTime τ))
        (rescalingMap data x τ)) :
    reducedVorticitySource
        (rescaledFields data fields) x τ =
      (data.swirlScale τ * data.vorticityScale τ) *
        reducedVorticitySource fields
          (rescalingMap data x τ)
          (data.physicalTime τ) := by
  rw [reducedVorticitySource_rescaledFields
    data fields x τ hswirl, hcompat]
  ring

/-- Physical meridian advection of dynamically rescaled swirl has amplitude
`A²`. -/
theorem reducedAdvection_rescaledSwirl
    (data : Rescaling) (fields : ReducedFields)
    (x : ℝ^2) (τ : ℝ)
    (hscale : data.spatialScale τ ≠ 0)
    (hstream :
      DifferentiableAt ℝ
        (fun y ↦ fields.streamFunction y (data.physicalTime τ))
        (rescalingMap data x τ))
    (hswirl :
      DifferentiableAt ℝ
        (fun y ↦ fields.swirl y (data.physicalTime τ))
        (rescalingMap data x τ)) :
    reducedAdvection
        (rescaledFields data fields)
        (fun y ↦ rescaledSwirl data fields y τ) x τ =
      data.swirlScale τ ^ 2 *
        reducedAdvection fields
          (fun y ↦ fields.swirl y (data.physicalTime τ))
          (rescalingMap data x τ)
          (data.physicalTime τ) := by
  rw [reducedAdvection_eq_radial_add_axial, reducedAdvection_eq_radial_add_axial]
  rw [reducedRadialVelocity_rescaledFields
    data fields x τ hstream]
  rw [reducedAxialVelocity_rescaledFields
    data fields x τ hstream]
  rw [partialDeriv_rescaledSwirl
    data fields (0 : Fin 2) x τ hswirl]
  rw [partialDeriv_rescaledSwirl
    data fields (1 : Fin 2) x τ hswirl]
  field_simp

/-- Physical meridian advection of dynamically rescaled vorticity has
amplitude `A Aω`. -/
theorem reducedAdvection_rescaledVorticity
    (data : Rescaling) (fields : ReducedFields)
    (x : ℝ^2) (τ : ℝ)
    (hscale : data.spatialScale τ ≠ 0)
    (hstream :
      DifferentiableAt ℝ
        (fun y ↦ fields.streamFunction y (data.physicalTime τ))
        (rescalingMap data x τ))
    (hvorticity :
      DifferentiableAt ℝ
        (fun y ↦ fields.vorticity y (data.physicalTime τ))
        (rescalingMap data x τ)) :
    reducedAdvection
        (rescaledFields data fields)
        (fun y ↦ rescaledVorticity data fields y τ) x τ =
      (data.swirlScale τ * data.vorticityScale τ) *
        reducedAdvection fields
          (fun y ↦ fields.vorticity y (data.physicalTime τ))
          (rescalingMap data x τ)
          (data.physicalTime τ) := by
  rw [reducedAdvection_eq_radial_add_axial, reducedAdvection_eq_radial_add_axial]
  rw [reducedRadialVelocity_rescaledFields
    data fields x τ hstream]
  rw [reducedAxialVelocity_rescaledFields
    data fields x τ hstream]
  rw [partialDeriv_rescaledVorticity
    data fields (0 : Fin 2) x τ hvorticity]
  rw [partialDeriv_rescaledVorticity
    data fields (1 : Fin 2) x τ hvorticity]
  field_simp

/-- Off the axis, elliptic compatibility `Aω = AL` transports the reduced
streamfunction residual with amplitude `Aω`. -/
theorem reducedStreamFunctionResidual_rescaledFields
    (data : Rescaling) (fields : ReducedFields)
    (x : ℝ^2) (τ : ℝ)
    (hstream :
      ContDiff ℝ 2
        (fun y ↦ fields.streamFunction y (data.physicalTime τ)))
    (hscale : data.spatialScale τ ≠ 0)
    (hcompat :
      data.vorticityScale τ =
        data.swirlScale τ * data.spatialScale τ)
    (hr : x (0 : Fin 2) ≠ 0) :
    reducedStreamFunctionResidual
        (rescaledFields data fields) x τ =
      data.vorticityScale τ *
        reducedStreamFunctionResidual fields
          (rescalingMap data x τ)
          (data.physicalTime τ) := by
  unfold reducedStreamFunctionResidual
  change
    -reducedLaplacian
        (fun y ↦ rescaledStreamFunction data fields y τ) x -
      rescaledVorticity data fields x τ =
      _
  rw [show
      (fun y ↦ rescaledStreamFunction data fields y τ) =
        fun y ↦
          (data.swirlScale τ / data.spatialScale τ) *
            (fun z ↦ fields.streamFunction z (data.physicalTime τ))
              (rescalingMap data y τ) by rfl]
  rw [reducedLaplacian_const_mul_comp_rescalingMap
    data (fun y ↦ fields.streamFunction y (data.physicalTime τ))
    (data.swirlScale τ / data.spatialScale τ)
    x τ hstream hscale hr]
  simp only [rescaledVorticity, dynamicAffinePullback,
    rescalingMap, smul_eq_mul]
  rw [hcompat]
  field_simp

/-- The time chain rule cancels the affine modulation advection.

For a pullback with amplitude `B`, amplitude rate `c`, physical-time rate
`A`, spatial rate `L' = -λL`, and axial shift rate `-CL e_z`, the sum of
the rescaled time derivative and advection by `λx + Ce_z` is
`BA ∂_t f + c f̃`. -/
theorem deriv_rescaled_add_frame_advection
    (data : Rescaling)
    (field : ℝ^2 → ℝ → ℝ)
    (amplitudeScale rate : ℝ → ℝ)
    (x : ℝ^2) (τ : ℝ)
    (hfield :
      DifferentiableAt ℝ (Function.uncurry field)
        (rescalingMap data x τ, data.physicalTime τ))
    (hspatial :
      DifferentiableAt ℝ
        (fun y ↦ field y (data.physicalTime τ))
        (rescalingMap data x τ))
    (hamplitude :
      HasDerivAt amplitudeScale
        (rate τ * amplitudeScale τ) τ)
    (hlaws : Rescaling.SatisfiesScaleLawsAt data τ) :
    deriv
        (fun s ↦ dynamicAffinePullback field amplitudeScale
          data.spatialScale (rescalingShift data)
          data.physicalTime x s) τ +
      advectiveDerivative
        (fun y ↦
          data.spatialRate τ • y +
            data.axialDrift τ • axialUnit)
        (fun y ↦ dynamicAffinePullback field amplitudeScale
          data.spatialScale (rescalingShift data)
          data.physicalTime y τ) x =
      amplitudeScale τ * data.swirlScale τ *
          deriv (field (rescalingMap data x τ))
            (data.physicalTime τ) +
        rate τ *
          dynamicAffinePullback field amplitudeScale
            data.spatialScale (rescalingShift data)
            data.physicalTime x τ := by
  have hpartial (i : Fin 2) :
      partialDeriv i
          (fun y ↦ dynamicAffinePullback field amplitudeScale
            data.spatialScale (rescalingShift data)
            data.physicalTime y τ) x =
        amplitudeScale τ * data.spatialScale τ *
          partialDeriv i
            (fun y ↦ field y (data.physicalTime τ))
            (rescalingMap data x τ) := by
    simpa [dynamicAffinePullback, rescalingMap,
      dynamicAffinePoint, smul_eq_mul] using
      partialDeriv_const_mul_comp_affineDilation i
        (fun y ↦ field y (data.physicalTime τ))
        (amplitudeScale τ) (data.spatialScale τ)
        (rescalingShift data τ) x hspatial
  have hmodulation :
      advectiveDerivative
          (fun y ↦
            data.spatialRate τ • y +
              data.axialDrift τ • axialUnit)
          (fun y ↦ dynamicAffinePullback field amplitudeScale
            data.spatialScale (rescalingShift data)
            data.physicalTime y τ) x =
        amplitudeScale τ * data.spatialScale τ *
          ((data.spatialRate τ * x (0 : Fin 2)) *
              partialDeriv (0 : Fin 2)
                (fun y ↦ field y (data.physicalTime τ))
                (rescalingMap data x τ) +
            (data.spatialRate τ * x (1 : Fin 2) +
                data.axialDrift τ) *
              partialDeriv (1 : Fin 2)
                (fun y ↦ field y (data.physicalTime τ))
                (rescalingMap data x τ)) := by
    rw [advectiveDerivative_eq_sum_mul_partialDeriv]
    simp only [Fin.sum_univ_two]
    rw [hpartial (0 : Fin 2), hpartial (1 : Fin 2)]
    simp [smul_eq_mul]
    ring
  have hchain :=
    hasDerivAt_dynamicAffinePullback_expanded
      field amplitudeScale data.spatialScale
      (rescalingShift data) data.physicalTime x τ
      (rate τ * amplitudeScale τ)
      (-data.spatialRate τ * data.spatialScale τ)
      (data.swirlScale τ)
      ((-data.axialDrift τ * data.spatialScale τ) • axialUnit)
      hfield hamplitude hlaws.spatialScale_hasDerivAt
      hlaws.axialShift_hasDerivAt hlaws.physicalTime_hasDerivAt
  have hcoordinate_zero :
      ((-data.spatialRate τ * data.spatialScale τ) • x +
          (-data.axialDrift τ * data.spatialScale τ) • axialUnit)
          (0 : Fin 2) =
        (-data.spatialRate τ * data.spatialScale τ) *
          x (0 : Fin 2) := by
    simp [smul_eq_mul]
  have hcoordinate_one :
      ((-data.spatialRate τ * data.spatialScale τ) • x +
          (-data.axialDrift τ * data.spatialScale τ) • axialUnit)
          (1 : Fin 2) =
        (-data.spatialRate τ * data.spatialScale τ) *
            x (1 : Fin 2) +
          (-data.axialDrift τ * data.spatialScale τ) := by
    simp [smul_eq_mul]
  rw [hchain.deriv, hmodulation]
  rw [fderiv_apply_eq_sum_partialDeriv_mul, Fin.sum_univ_two]
  rw [hcoordinate_zero, hcoordinate_one]
  simp only [rescalingMap, smul_eq_mul,
    dynamicAffinePullback]
  ring

/-- The swirl time chain rule plus affine modulation advection has physical
time-derivative amplitude `A²` and leaves the linear rate `cᵤ ũ₁`. -/
theorem deriv_rescaledSwirl_add_modulationAdvection
    (data : Rescaling) (fields : ReducedFields)
    (x : ℝ^2) (τ : ℝ)
    (hfield :
      DifferentiableAt ℝ (Function.uncurry fields.swirl)
        (rescalingMap data x τ, data.physicalTime τ))
    (hspatial :
      DifferentiableAt ℝ
        (fun y ↦ fields.swirl y (data.physicalTime τ))
        (rescalingMap data x τ))
    (hlaws : Rescaling.SatisfiesScaleLawsAt data τ) :
    deriv (fun s ↦ rescaledSwirl data fields x s) τ +
      advectiveDerivative
        (fun y ↦
          data.spatialRate τ • y +
            data.axialDrift τ • axialUnit)
        (fun y ↦ rescaledSwirl data fields y τ) x =
      data.swirlScale τ ^ 2 *
          deriv
            (fields.swirl (rescalingMap data x τ))
            (data.physicalTime τ) +
        data.swirlRate τ *
          rescaledSwirl data fields x τ := by
  simpa [rescaledSwirl, pow_two, mul_assoc] using
    deriv_rescaled_add_frame_advection
      data fields.swirl data.swirlScale data.swirlRate x τ
      hfield hspatial hlaws.swirlScale_hasDerivAt hlaws

/-- The vorticity time chain rule plus affine modulation advection has
physical time-derivative amplitude `A Aω` and leaves the linear rate
`cω ω̃₁`. -/
theorem deriv_rescaledVorticity_add_modulationAdvection
    (data : Rescaling) (fields : ReducedFields)
    (x : ℝ^2) (τ : ℝ)
    (hfield :
      DifferentiableAt ℝ (Function.uncurry fields.vorticity)
        (rescalingMap data x τ, data.physicalTime τ))
    (hspatial :
      DifferentiableAt ℝ
        (fun y ↦ fields.vorticity y (data.physicalTime τ))
        (rescalingMap data x τ))
    (hlaws : Rescaling.SatisfiesScaleLawsAt data τ) :
    deriv (fun s ↦ rescaledVorticity data fields x s) τ +
      advectiveDerivative
        (fun y ↦
          data.spatialRate τ • y +
            data.axialDrift τ • axialUnit)
        (fun y ↦ rescaledVorticity data fields y τ) x =
      (data.swirlScale τ * data.vorticityScale τ) *
          deriv
            (fields.vorticity
              (rescalingMap data x τ))
            (data.physicalTime τ) +
        data.vorticityRate τ *
          rescaledVorticity data fields x τ := by
  simpa [rescaledVorticity, mul_comm, mul_left_comm,
    mul_assoc] using
    deriv_rescaled_add_frame_advection
      data fields.vorticity data.vorticityScale data.vorticityRate x τ
      hfield hspatial hlaws.vorticityScale_hasDerivAt hlaws

end

end Euler.Axisymmetric
