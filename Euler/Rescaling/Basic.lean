/-
Copyright (c) 2026 Robert Joseph George and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/

module

public import Euler.Equations.Reduced
public import Euler.Rescaling.Affine
public import Euler.Rescaling.ScaleRates
import Mathlib.Tactic.FieldSimp

/-!
# The change of variables in Proposition S8

The physical point represented by `x` at rescaled time `τ` is `L(τ)x + Z(τ)e_z`.
The rescaled fields are `A u`, `Aω ω`, and `(A/L) ψ` at that physical point and
physical time. In the paper’s notation, `A = 1/su`, `L = sr`, and `Aω = 1/sω`.
Thus `Aω = A L` is the identity `su = sω sr`, and the clock law `t′ = A`
is reciprocal to `dτ/dt = su`.

Only the five differential scale and clock laws are included. Compatibility of
the vorticity rate is proved from local compatibility of the amplitudes.
-/

@[expose] public section

namespace Euler.Axisymmetric

open Euler.Similarity
open scoped Topology

noncomputable section

/-- Unit vector in the axial meridian direction. -/
def axialUnit : ℝ^2 :=
  WithLp.toLp 2 ![0, 1]

/-- The radial component of the axial unit vector is zero. -/
@[simp]
theorem axialUnit_apply_zero :
    axialUnit (0 : Fin 2) = 0 := by
  simp [axialUnit]

/-- The axial component of the axial unit vector is one. -/
@[simp]
theorem axialUnit_apply_one :
    axialUnit (1 : Fin 2) = 1 := by
  simp [axialUnit]

/-- The functions in the dynamic change of variables, S343–S348.

The five differential laws are stated separately in `SatisfiesScaleLawsAt`;
the amplitude relation `Aω = A L` is an additional hypothesis. -/
structure Rescaling where
  /-- Reduced-swirl amplitude `A`. -/
  swirlScale : ℝ → ℝ
  /-- Common meridian spatial scale `L`. -/
  spatialScale : ℝ → ℝ
  /-- Reduced-vorticity amplitude `Aω`. -/
  vorticityScale : ℝ → ℝ
  /-- Physical axial center `Z`. -/
  axialCenter : ℝ → ℝ
  /-- Physical time `t(τ)`. -/
  physicalTime : ℝ → ℝ
  /-- Logarithmic reduced-swirl rate `cᵤ`. -/
  swirlRate : ℝ → ℝ
  /-- Negative logarithmic spatial rate `λ`. -/
  spatialRate : ℝ → ℝ
  /-- Axial transport drift `C`. -/
  axialDrift : ℝ → ℝ
  /-- Logarithmic reduced-vorticity rate `cω`. -/
  vorticityRate : ℝ → ℝ

/-- Differential scale laws at one rescaled time. -/
structure Rescaling.SatisfiesScaleLawsAt
    (data : Rescaling) (τ : ℝ) : Prop where
  /-- `A' = cᵤ A`. -/
  swirlScale_hasDerivAt :
    HasDerivAt data.swirlScale
      (data.swirlRate τ * data.swirlScale τ) τ
  /-- `L' = -λL`. -/
  spatialScale_hasDerivAt :
    HasDerivAt data.spatialScale
      (-data.spatialRate τ * data.spatialScale τ) τ
  /-- `Aω' = cω Aω`. -/
  vorticityScale_hasDerivAt :
    HasDerivAt data.vorticityScale
      (data.vorticityRate τ * data.vorticityScale τ) τ
  /-- `(Ze_z)' = -CL e_z`; this sign produces `+C∂_z` in rescaled
  transport. -/
  axialShift_hasDerivAt :
    HasDerivAt (fun s ↦ data.axialCenter s • axialUnit)
      ((-data.axialDrift τ * data.spatialScale τ) • axialUnit) τ
  /-- `t' = A`. -/
  physicalTime_hasDerivAt :
    HasDerivAt data.physicalTime (data.swirlScale τ) τ

/-- Vector-valued axial shift `Z(τ)e_z`. -/
def rescalingShift
    (data : Rescaling) (τ : ℝ) : ℝ^2 :=
  data.axialCenter τ • axialUnit

/-- Physical similarity point `L(τ)x + Z(τ)e_z`. -/
def rescalingMap
    (data : Rescaling) (x : ℝ^2) (τ : ℝ) : ℝ^2 :=
  dynamicAffinePoint data.spatialScale (rescalingShift data) x τ

/-- The radial coordinate of the physical similarity point is `Lr`. -/
@[simp]
theorem rescalingMap_radial
    (data : Rescaling) (x : ℝ^2) (τ : ℝ) :
    rescalingMap data x τ (0 : Fin 2) =
      data.spatialScale τ * x (0 : Fin 2) := by
  simp [rescalingMap, dynamicAffinePoint,
    affineDilation, rescalingShift, smul_eq_mul]

/-- The axial coordinate of the physical similarity point is `Lz + Z`. -/
@[simp]
theorem rescalingMap_axial
    (data : Rescaling) (x : ℝ^2) (τ : ℝ) :
    rescalingMap data x τ (1 : Fin 2) =
      data.spatialScale τ * x (1 : Fin 2) + data.axialCenter τ := by
  simp [rescalingMap, dynamicAffinePoint,
    affineDilation, rescalingShift, smul_eq_mul]

/-- Positive spatial scaling and axial translation preserve the open
positive-radius meridian. -/
theorem rescalingMap_mem_positiveRadiusMeridian
    (data : Rescaling) {x : ℝ^2} {τ : ℝ}
    (hscale : 0 < data.spatialScale τ)
    (hx : x ∈ positiveRadiusMeridian) :
    rescalingMap data x τ ∈ positiveRadiusMeridian := by
  rw [mem_positiveRadiusMeridian_iff] at hx ⊢
  rw [rescalingMap_radial]
  exact mul_pos hscale hx

/-- Dynamically rescaled reduced swirl. -/
def rescaledSwirl
    (data : Rescaling) (fields : ReducedFields)
    (x : ℝ^2) (τ : ℝ) : ℝ :=
  dynamicAffinePullback fields.swirl data.swirlScale data.spatialScale
    (rescalingShift data) data.physicalTime x τ

/-- Dynamically rescaled reduced azimuthal vorticity. -/
def rescaledVorticity
    (data : Rescaling) (fields : ReducedFields)
    (x : ℝ^2) (τ : ℝ) : ℝ :=
  dynamicAffinePullback fields.vorticity data.vorticityScale
    data.spatialScale (rescalingShift data) data.physicalTime x τ

/-- Dynamically rescaled reduced streamfunction, with amplitude `A/L`. -/
def rescaledStreamFunction
    (data : Rescaling) (fields : ReducedFields)
    (x : ℝ^2) (τ : ℝ) : ℝ :=
  (data.swirlScale τ / data.spatialScale τ) *
    fields.streamFunction (rescalingMap data x τ)
      (data.physicalTime τ)

/-- All three dynamically rescaled reduced fields. -/
def rescaledFields
    (data : Rescaling)
    (fields : ReducedFields) : ReducedFields where
  swirl := rescaledSwirl data fields
  vorticity := rescaledVorticity data fields
  streamFunction := rescaledStreamFunction data fields

/-- Under amplitude compatibility, the streamfunction amplitude `A/L`
equals the elliptically natural amplitude `Aω/L²`. -/
theorem streamFunctionScale_eq_vorticityScale_div_sq
    (data : Rescaling) (τ : ℝ)
    (hscale : data.spatialScale τ ≠ 0)
    (hcompat :
      data.vorticityScale τ =
        data.swirlScale τ * data.spatialScale τ) :
    data.swirlScale τ / data.spatialScale τ =
      data.vorticityScale τ / data.spatialScale τ ^ 2 := by
  rw [hcompat]
  field_simp

/-- In the reciprocal-amplitude convention, differentiating `Aω = AL` determines `cω`.
No rate compatibility is assumed in `Rescaling.SatisfiesScaleLawsAt`. -/
theorem Rescaling.SatisfiesScaleLawsAt.vorticityRate_eq_of_scale_compatibility
    {data : Rescaling} {τ : ℝ}
    (hlaws : Rescaling.SatisfiesScaleLawsAt data τ)
    (hswirl_ne : data.swirlScale τ ≠ 0)
    (hspatial_ne : data.spatialScale τ ≠ 0)
    (hcompat : data.vorticityScale =ᶠ[𝓝 τ]
      fun t ↦ data.swirlScale t * data.spatialScale t) :
    data.vorticityRate τ = data.swirlRate τ - data.spatialRate τ := by
  have hvorticity_ne : data.vorticityScale τ ≠ 0 := by
    rw [hcompat.eq_of_nhds]
    exact mul_ne_zero hswirl_ne hspatial_ne
  simpa only [sub_eq_add_neg] using logarithmicRate_eq_add_of_eventuallyEq_mul
    hlaws.swirlScale_hasDerivAt hlaws.spatialScale_hasDerivAt
    hlaws.vorticityScale_hasDerivAt hvorticity_ne hcompat

end

end Euler.Axisymmetric
