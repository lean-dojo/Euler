module

public import Review.Definitions.Equations.Reduced
public import Review.Definitions.Rescaling.Affine

/-! # Dynamic rescaling -/

@[expose] public noncomputable section

namespace Euler.Axisymmetric

open Euler.Similarity

open scoped Topology

/-- Unit vector in the axial meridian direction. -/
def axialUnit : ℝ^2 :=
  WithLp.toLp 2 ![0, 1]

/-- Amplitudes, coordinates, and rates in the dynamic change of variables, S343–S348.
Their differential laws and the relation `Aω = A L` are hypotheses of the rescaling theorem. -/
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

/-- Vector-valued axial shift `Z(τ)e_z`. -/
def rescalingShift
    (data : Rescaling) (τ : ℝ) : ℝ^2 :=
  data.axialCenter τ • axialUnit

/-- Physical similarity point `L(τ)x + Z(τ)e_z`. -/
def rescalingMap
    (data : Rescaling) (x : ℝ^2) (τ : ℝ) : ℝ^2 :=
  dynamicAffinePoint data.spatialScale (rescalingShift data) x τ

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

end Euler.Axisymmetric

end
