/-
Copyright (c) 2026 Robert Joseph George and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/

module

public import Euler.Calculus.ChainRule
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Ring

/-!
# Changing space and time

We differentiate a field after scaling its amplitude, scaling and translating
its spatial coordinates, and changing time. Each spatial derivative contributes
one coordinate-scale factor. The time derivative has a term from the moving
coordinates and a term from the original time dependence.

These chain rules are used in the rescaling calculation in Appendix D.
-/

@[expose] public section

namespace Euler.Similarity

noncomputable section

variable {V E : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Split the derivative of a jointly differentiable field into its spatial
and temporal slice derivatives. -/
theorem fderiv_uncurry_apply_prod
    (field : V → ℝ → E) (x v : V) (t s : ℝ)
    (hfield : DifferentiableAt ℝ (Function.uncurry field) (x, t)) :
    fderiv ℝ (Function.uncurry field) (x, t) (v, s) =
      fderiv ℝ (fun y ↦ field y t) x v +
        s • deriv (field x) t := by
  -- Restrict the joint derivative to each factor of space × time.
  have hspace := (hfield.hasFDerivAt.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t)).fderiv
  have htime := (hfield.hasFDerivAt.comp t (hasFDerivAt_prodMk_right (𝕜 := ℝ) x t)).fderiv
  rw [← ContinuousLinearMap.comp_inl_add_comp_inr _ (v, s), ← hspace, ← htime]
  simp [Function.comp_def, fderiv_eq_smul_deriv]

/-- A spatial dilation followed by a translation. -/
def affineDilation (scale : ℝ) (shift x : V) : V :=
  scale • x + shift

/-- The time-dependent affine similarity point `L(τ)x + b(τ)`. -/
def dynamicAffinePoint
    (spatialScale : ℝ → ℝ) (shift : ℝ → V)
    (x : V) (τ : ℝ) : V :=
  affineDilation (spatialScale τ) (shift τ) x

/-- Pull a time-dependent field back by an amplitude, an affine spatial map,
and a physical-time change. -/
def dynamicAffinePullback
    (field : V → ℝ → E)
    (amplitudeScale spatialScale : ℝ → ℝ)
    (shift : ℝ → V) (physicalTime : ℝ → ℝ)
    (x : V) (τ : ℝ) : E :=
  amplitudeScale τ •
    field (dynamicAffinePoint spatialScale shift x τ) (physicalTime τ)

/-- Derivative of a dynamic affine similarity point. -/
theorem hasDerivAt_dynamicAffinePoint
    (spatialScale : ℝ → ℝ) (shift : ℝ → V)
    (x : V) (τ spatialDerivative : ℝ) (shiftDerivative : V)
    (hspatial : HasDerivAt spatialScale spatialDerivative τ)
    (hshift : HasDerivAt shift shiftDerivative τ) :
    HasDerivAt
      (fun s ↦ dynamicAffinePoint spatialScale shift x s)
      (spatialDerivative • x + shiftDerivative) τ :=
  (hspatial.smul_const x).add hshift

/-- Chain rule for a dynamic affine pullback, stated through the joint
Fréchet derivative of the physical field. -/
theorem hasDerivAt_dynamicAffinePullback
    (field : V → ℝ → E)
    (amplitudeScale spatialScale : ℝ → ℝ)
    (shift : ℝ → V) (physicalTime : ℝ → ℝ)
    (x : V) (τ amplitudeDerivative spatialDerivative timeDerivative : ℝ)
    (shiftDerivative : V)
    (hfield : DifferentiableAt ℝ (Function.uncurry field)
      (dynamicAffinePoint spatialScale shift x τ, physicalTime τ))
    (hamplitude :
      HasDerivAt amplitudeScale amplitudeDerivative τ)
    (hspatial :
      HasDerivAt spatialScale spatialDerivative τ)
    (hshift :
      HasDerivAt shift shiftDerivative τ)
    (htime :
      HasDerivAt physicalTime timeDerivative τ) :
    HasDerivAt
      (fun s ↦ dynamicAffinePullback field amplitudeScale spatialScale
        shift physicalTime x s)
      (amplitudeScale τ •
          fderiv ℝ (Function.uncurry field)
            (dynamicAffinePoint spatialScale shift x τ, physicalTime τ)
            (spatialDerivative • x + shiftDerivative, timeDerivative) +
        amplitudeDerivative •
          field (dynamicAffinePoint spatialScale shift x τ)
            (physicalTime τ))
      τ := by
  have hcomp := hfield.hasFDerivAt.comp_hasDerivAt τ
    (((hspatial.smul_const x).add hshift).prodMk htime)
  exact hamplitude.smul hcomp

/-- Expanded dynamic-affine chain rule with separate spatial and temporal
slice derivatives. -/
theorem hasDerivAt_dynamicAffinePullback_expanded
    (field : V → ℝ → E)
    (amplitudeScale spatialScale : ℝ → ℝ)
    (shift : ℝ → V) (physicalTime : ℝ → ℝ)
    (x : V) (τ amplitudeDerivative spatialDerivative timeDerivative : ℝ)
    (shiftDerivative : V)
    (hfield : DifferentiableAt ℝ (Function.uncurry field)
      (dynamicAffinePoint spatialScale shift x τ, physicalTime τ))
    (hamplitude :
      HasDerivAt amplitudeScale amplitudeDerivative τ)
    (hspatial :
      HasDerivAt spatialScale spatialDerivative τ)
    (hshift :
      HasDerivAt shift shiftDerivative τ)
    (htime :
      HasDerivAt physicalTime timeDerivative τ) :
    HasDerivAt
      (fun s ↦ dynamicAffinePullback field amplitudeScale spatialScale
        shift physicalTime x s)
      (amplitudeScale τ •
          (fderiv ℝ
              (fun y ↦ field y (physicalTime τ))
              (dynamicAffinePoint spatialScale shift x τ)
              (spatialDerivative • x + shiftDerivative) +
            timeDerivative •
              deriv
                (field (dynamicAffinePoint spatialScale shift x τ))
                (physicalTime τ)) +
        amplitudeDerivative •
          field (dynamicAffinePoint spatialScale shift x τ)
            (physicalTime τ))
      τ := by
  apply
    (hasDerivAt_dynamicAffinePullback field amplitudeScale spatialScale
      shift physicalTime x τ amplitudeDerivative spatialDerivative
      timeDerivative shiftDerivative hfield hamplitude hspatial hshift
      htime).congr_deriv
  rw [fderiv_uncurry_apply_prod field
    (dynamicAffinePoint spatialScale shift x τ)
    (spatialDerivative • x + shiftDerivative)
    (physicalTime τ) timeDerivative hfield]

/-- The derivative of a fixed affine dilation is `scale` times the identity. -/
theorem hasFDerivAt_affineDilation
    {n : ℕ} (scale : ℝ) (shift x : ℝ^n) :
    HasFDerivAt (affineDilation scale shift)
      (scale • ContinuousLinearMap.id ℝ (ℝ^n)) x :=
  ((hasFDerivAt_id x).const_smul scale).add_const shift

/-- A fixed affine dilation is smooth to every order. -/
@[fun_prop]
theorem contDiff_affineDilation
    {n : ℕ} {k : WithTop ℕ∞} (scale : ℝ) (shift : ℝ^n) :
    ContDiff ℝ k (affineDilation scale shift) := by
  unfold affineDilation
  fun_prop

/-- Coordinate `j` of an affine dilation has derivative
`scale δᵢⱼ` in direction `i`. -/
theorem partialDeriv_affineDilation_apply
    {n : ℕ} (scale : ℝ) (shift x : ℝ^n) (i j : Fin n) :
    partialDeriv i (fun y ↦ affineDilation scale shift y j) x =
      scale * if i = j then 1 else 0 := by
  rw [← partialDeriv_apply i j
    (hasFDerivAt_affineDilation scale shift x).differentiableAt]
  rw [partialDeriv, (hasFDerivAt_affineDilation scale shift x).fderiv]
  simp [eq_comm]

/-- Pullback by a fixed affine dilation multiplies every first coordinate
derivative by the spatial scale. -/
theorem partialDeriv_comp_affineDilation
    {n : ℕ} (i : Fin n) (profile : ℝ^n → ℝ)
    (scale : ℝ) (shift x : ℝ^n)
    (hprofile :
      DifferentiableAt ℝ profile (affineDilation scale shift x)) :
    partialDeriv i
        (fun y ↦ profile (affineDilation scale shift y)) x =
      scale * partialDeriv i profile (affineDilation scale shift x) := by
  rw [partialDeriv_comp i profile (affineDilation scale shift) x hprofile
    (hasFDerivAt_affineDilation scale shift x).differentiableAt]
  simp [partialDeriv_affineDilation_apply, mul_comm]

/-- A constant amplitude and an affine spatial pullback contribute one
amplitude factor and one spatial-scale factor to a first derivative. -/
theorem partialDeriv_const_mul_comp_affineDilation
    {n : ℕ} (i : Fin n) (profile : ℝ^n → ℝ)
    (amplitude scale : ℝ) (shift x : ℝ^n)
    (hprofile :
      DifferentiableAt ℝ profile (affineDilation scale shift x)) :
    partialDeriv i
        (fun y ↦ amplitude *
          profile (affineDilation scale shift y)) x =
      amplitude * scale *
        partialDeriv i profile (affineDilation scale shift x) := by
  simp_rw [← smul_eq_mul, partialDeriv_const_smul]
  rw [partialDeriv_comp_affineDilation i profile scale shift x hprofile]
  simp [smul_eq_mul, mul_assoc]

/-- The second coordinate derivatives of an affine dilation vanish. -/
theorem partialDeriv_partialDeriv_affineDilation_apply
    {n : ℕ} (scale : ℝ) (shift x : ℝ^n) (i k j : Fin n) :
    partialDeriv i
        (fun y ↦ partialDeriv k
          (fun z ↦ affineDilation scale shift z j) y) x = 0 := by
  simp_rw [partialDeriv_affineDilation_apply]
  exact partialDeriv_const _

/-- Pullback by a fixed affine dilation multiplies every second coordinate
derivative by the square of the spatial scale. -/
theorem partialDeriv_partialDeriv_comp_affineDilation
    {n : ℕ} (i k : Fin n) (profile : ℝ^n → ℝ)
    (scale : ℝ) (shift x : ℝ^n)
    (hprofile : ContDiff ℝ 2 profile) :
    partialDeriv i
        (fun y ↦ partialDeriv k
          (fun z ↦ profile (affineDilation scale shift z)) y) x =
      scale ^ 2 *
        partialDeriv i (fun y ↦ partialDeriv k profile y)
          (affineDilation scale shift x) := by
  rw [partialDeriv_partialDeriv_comp i k profile
    (affineDilation scale shift) x hprofile
    (contDiff_affineDilation scale shift)]
  simp [partialDeriv_affineDilation_apply, pow_two]
  ring

/-- A constant amplitude and an affine spatial pullback contribute one
amplitude factor and two spatial-scale factors to a second derivative. -/
theorem partialDeriv_partialDeriv_const_mul_comp_affineDilation
    {n : ℕ} (i k : Fin n) (profile : ℝ^n → ℝ)
    (amplitude scale : ℝ) (shift x : ℝ^n)
    (hprofile : ContDiff ℝ 2 profile) :
    partialDeriv i
        (fun y ↦ partialDeriv k
          (fun z ↦ amplitude *
            profile (affineDilation scale shift z)) y) x =
      amplitude * scale ^ 2 *
        partialDeriv i (fun y ↦ partialDeriv k profile y)
          (affineDilation scale shift x) := by
  simp_rw [← smul_eq_mul, partialDeriv_const_smul]
  rw [partialDeriv_partialDeriv_comp_affineDilation
    i k profile scale shift x hprofile]
  simp [smul_eq_mul, mul_assoc]

/-- Advection of two fields pulled back by the same affine dilation gains the
product of their amplitudes and one spatial-scale factor. -/
theorem advectiveDerivative_smul_comp_affineDilation
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (advecting : ℝ^n → ℝ^n) (transported : ℝ^n → E)
    (advectingAmplitude transportedAmplitude scale : ℝ)
    (shift x : ℝ^n)
    (htransported :
      DifferentiableAt ℝ transported (affineDilation scale shift x)) :
    advectiveDerivative
        (fun y ↦ advectingAmplitude •
          advecting (affineDilation scale shift y))
        (fun y ↦ transportedAmplitude •
          transported (affineDilation scale shift y)) x =
      (advectingAmplitude * transportedAmplitude * scale) •
        advectiveDerivative advecting transported
          (affineDilation scale shift x) := by
  have hcomp :=
    htransported.hasFDerivAt.comp x
      (hasFDerivAt_affineDilation scale shift x)
  have hscaled := hcomp.const_smul transportedAmplitude
  unfold advectiveDerivative
  change
    (fderiv ℝ
      (transportedAmplitude • transported ∘ affineDilation scale shift) x)
        (advectingAmplitude • advecting (affineDilation scale shift x)) =
      _
  rw [hscaled.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, map_smul, smul_smul]
  simp [mul_assoc]

end

end Euler.Similarity
