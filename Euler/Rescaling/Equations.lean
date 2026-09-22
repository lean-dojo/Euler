/-
Copyright (c) 2026 Robert Joseph George and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/

module

public import Euler.Rescaling.Calculus
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Rescaled equations in Appendix D

Here we formalize Proposition S8. We substitute the rescaled fields into the
three equations and use the scale laws to simplify them. Differentiating the
amplitude compatibility relation also gives `cω = cu - λ`.

The parameter `eps` multiplies physical transport. The terms from the moving
coordinates, the nonlinear sources, and the elliptic equation keep their
original coefficients.
-/

@[expose] public section

namespace Euler.Axisymmetric

open scoped Topology

noncomputable section

/-- Advection by the moving frame plus `eps` times the reconstructed physical
meridian velocity. In coordinates its coefficients are `λr + eps*u_r` and
`λz + C + eps*u_z`. -/
def rescaledAdvection
    (eps : ℝ) (fields : ReducedFields)
    (spatialRate axialDrift : ℝ → ℝ)
    (f : ℝ^2 → ℝ) (x : ℝ^2) (τ : ℝ) : ℝ :=
  advectiveDerivative
      (fun y ↦ spatialRate τ • y + axialDrift τ • axialUnit) f x +
    eps * reducedAdvection fields f x τ

/-- The swirl pullback chain rule with arbitrary convection strength.
Only physical meridian advection acquires the coefficient `eps`. -/
theorem deriv_add_rescaledAdvection_rescaledSwirl
    (eps : ℝ) (data : Rescaling) (fields : ReducedFields)
    (x : ℝ^2) (τ : ℝ)
    (hscale : data.spatialScale τ ≠ 0)
    (hfield :
      DifferentiableAt ℝ (Function.uncurry fields.swirl)
        (rescalingMap data x τ, data.physicalTime τ))
    (hstream :
      DifferentiableAt ℝ
        (fun y ↦ fields.streamFunction y (data.physicalTime τ))
        (rescalingMap data x τ))
    (hlaws : Rescaling.SatisfiesScaleLawsAt data τ) :
    deriv (fun s ↦ rescaledSwirl data fields x s) τ +
      rescaledAdvection eps
        (rescaledFields data fields)
        data.spatialRate data.axialDrift
        (fun y ↦ rescaledSwirl data fields y τ) x τ =
      data.swirlScale τ ^ 2 *
          (deriv
              (fields.swirl (rescalingMap data x τ))
              (data.physicalTime τ) +
            eps * reducedAdvection fields
              (fun y ↦ fields.swirl y (data.physicalTime τ))
              (rescalingMap data x τ)
              (data.physicalTime τ)) +
        data.swirlRate τ * rescaledSwirl data fields x τ := by
  have hswirl :
      DifferentiableAt ℝ (fun y ↦ fields.swirl y (data.physicalTime τ))
        (rescalingMap data x τ) :=
    hfield.comp (f := fun y : ℝ^2 ↦ (y, data.physicalTime τ))
      (rescalingMap data x τ)
      (differentiableAt_id.prodMk (differentiableAt_const _))
  unfold rescaledAdvection
  rw [← add_assoc]
  rw [deriv_rescaledSwirl_add_modulationAdvection
    data fields x τ hfield hswirl hlaws]
  rw [reducedAdvection_rescaledSwirl
    data fields x τ hscale hstream hswirl]
  ring

/-- Coordinate form of transport: `eps` multiplies the reconstructed velocity,
while the coordinate-frame terms retain coefficients `λ` and `C`. -/
theorem rescaledAdvection_eq_radial_add_axial
    (eps : ℝ) (fields : ReducedFields)
    (spatialRate axialDrift : ℝ → ℝ)
    (f : ℝ^2 → ℝ) (x : ℝ^2) (τ : ℝ) :
    rescaledAdvection eps fields spatialRate axialDrift f x τ =
      (spatialRate τ * x (0 : Fin 2) +
          eps * reducedRadialVelocity fields x τ) *
          partialDeriv (0 : Fin 2) f x +
        (spatialRate τ * x (1 : Fin 2) + axialDrift τ +
          eps * reducedAxialVelocity fields x τ) *
          partialDeriv (1 : Fin 2) f x := by
  unfold rescaledAdvection
  rw [advectiveDerivative_eq_sum_mul_partialDeriv, reducedAdvection_eq_radial_add_axial]
  simp [Fin.sum_univ_two, smul_eq_mul]
  ring

/-- The vorticity pullback has transport amplitude `A Aω` for every convection
strength. The amplitude rate contributes the separate term `cω ω̃`. -/
theorem deriv_add_rescaledAdvection_rescaledVorticity
    (eps : ℝ) (data : Rescaling) (fields : ReducedFields)
    (x : ℝ^2) (τ : ℝ)
    (hscale : data.spatialScale τ ≠ 0)
    (hfield :
      DifferentiableAt ℝ (Function.uncurry fields.vorticity)
        (rescalingMap data x τ, data.physicalTime τ))
    (hstream :
      DifferentiableAt ℝ
        (fun y ↦ fields.streamFunction y (data.physicalTime τ))
        (rescalingMap data x τ))
    (hlaws : Rescaling.SatisfiesScaleLawsAt data τ) :
    deriv (fun s ↦ rescaledVorticity data fields x s) τ +
      rescaledAdvection eps
        (rescaledFields data fields)
        data.spatialRate data.axialDrift
        (fun y ↦ rescaledVorticity data fields y τ) x τ =
      (data.swirlScale τ * data.vorticityScale τ) *
          (deriv
              (fields.vorticity (rescalingMap data x τ))
              (data.physicalTime τ) +
            eps * reducedAdvection fields
              (fun y ↦ fields.vorticity y (data.physicalTime τ))
              (rescalingMap data x τ)
              (data.physicalTime τ)) +
        data.vorticityRate τ * rescaledVorticity data fields x τ := by
  have hvorticity :
      DifferentiableAt ℝ (fun y ↦ fields.vorticity y (data.physicalTime τ))
        (rescalingMap data x τ) :=
    hfield.comp (f := fun y : ℝ^2 ↦ (y, data.physicalTime τ))
      (rescalingMap data x τ)
      (differentiableAt_id.prodMk (differentiableAt_const _))
  unfold rescaledAdvection
  rw [← add_assoc]
  rw [deriv_rescaledVorticity_add_modulationAdvection
    data fields x τ hfield hvorticity hlaws]
  rw [reducedAdvection_rescaledVorticity
    data fields x τ hscale hstream hvorticity]
  ring

/-- Defect in `∂t u + eps (u_r ∂r u + u_z ∂z u) = 2u ∂z ψ`.
The stretching source is independent of `eps`. -/
def convectionReducedSwirlResidual
    (eps : ℝ) (fields : ReducedFields) (x : ℝ^2) (t : ℝ) : ℝ :=
  deriv (fields.swirl x) t +
      eps * reducedAdvection fields (fun y ↦ fields.swirl y t) x t -
    reducedSwirlSource fields x t

/-- Defect in `∂t ω + eps (u_r ∂r ω + u_z ∂z ω) = 2u ∂z u`. -/
def convectionReducedVorticityResidual
    (eps : ℝ) (fields : ReducedFields) (x : ℝ^2) (t : ℝ) : ℝ :=
  deriv (fields.vorticity x) t +
      eps * reducedAdvection fields (fun y ↦ fields.vorticity y t) x t -
    reducedVorticitySource fields x t

/-- Defect in the dynamically rescaled swirl equation, with stretching source
`2u ∂z ψ` and amplitude-rate term `cu u`. -/
def rescaledSwirlResidual
    (eps : ℝ) (fields : ReducedFields)
    (spatialRate axialDrift swirlRate : ℝ → ℝ)
    (x : ℝ^2) (τ : ℝ) : ℝ :=
  deriv (fields.swirl x) τ +
      rescaledAdvection eps fields spatialRate axialDrift
        (fun y ↦ fields.swirl y τ) x τ -
    (reducedSwirlSource fields x τ + swirlRate τ * fields.swirl x τ)

/-- Defect in the dynamically rescaled vorticity equation, with source
`2u ∂z u` and independently specified amplitude-rate term `cω ω`. -/
def rescaledVorticityResidual
    (eps : ℝ) (fields : ReducedFields)
    (spatialRate axialDrift vorticityRate : ℝ → ℝ)
    (x : ℝ^2) (τ : ℝ) : ℝ :=
  deriv (fields.vorticity x) τ +
      rescaledAdvection eps fields spatialRate axialDrift
        (fun y ↦ fields.vorticity y τ) x τ -
    (reducedVorticitySource fields x τ + vorticityRate τ * fields.vorticity x τ)

/-- The physical convection-varied equations with the ordinary stream operator. -/
def SatisfiesPhysicalEquationsOn
    (eps : ℝ) (fields : ReducedFields)
    (domain : Set (ℝ^2)) (times : Set ℝ) : Prop :=
  (∀ ⦃x : ℝ^2⦄ ⦃t : ℝ⦄, x ∈ domain → t ∈ times →
    convectionReducedSwirlResidual eps fields x t = 0) ∧
  (∀ ⦃x : ℝ^2⦄ ⦃t : ℝ⦄, x ∈ domain → t ∈ times →
    convectionReducedVorticityResidual eps fields x t = 0) ∧
  (∀ ⦃x : ℝ^2⦄ ⦃t : ℝ⦄, x ∈ domain → t ∈ times →
    reducedStreamFunctionResidual fields x t = 0)

/-- The dynamically rescaled equations with the ordinary stream operator. -/
def SatisfiesRescaledEquationsOn
    (eps : ℝ) (fields : ReducedFields)
    (spatialRate axialDrift swirlRate vorticityRate : ℝ → ℝ)
    (domain : Set (ℝ^2)) (times : Set ℝ) : Prop :=
  (∀ ⦃x : ℝ^2⦄ ⦃τ : ℝ⦄, x ∈ domain → τ ∈ times →
    rescaledSwirlResidual eps fields
      spatialRate axialDrift swirlRate x τ = 0) ∧
  (∀ ⦃x : ℝ^2⦄ ⦃τ : ℝ⦄, x ∈ domain → τ ∈ times →
    rescaledVorticityResidual eps fields
      spatialRate axialDrift vorticityRate x τ = 0) ∧
  (∀ ⦃x : ℝ^2⦄ ⦃t : ℝ⦄, x ∈ domain → t ∈ times →
    reducedStreamFunctionResidual fields x t = 0)

/-- The swirl residual of the pullback is `A²` times its physical
counterpart. No scale compatibility or physical PDE is assumed. -/
theorem rescaledSwirlResidual_rescaledFields
    (eps : ℝ) (data : Rescaling) (fields : ReducedFields)
    (x : ℝ^2) (τ : ℝ)
    (hscale : data.spatialScale τ ≠ 0)
    (hfield :
      DifferentiableAt ℝ (Function.uncurry fields.swirl)
        (rescalingMap data x τ, data.physicalTime τ))
    (hstream :
      DifferentiableAt ℝ
        (fun y ↦ fields.streamFunction y (data.physicalTime τ))
        (rescalingMap data x τ))
    (hlaws : Rescaling.SatisfiesScaleLawsAt data τ) :
    rescaledSwirlResidual eps
        (rescaledFields data fields)
        data.spatialRate data.axialDrift data.swirlRate x τ =
      data.swirlScale τ ^ 2 *
        convectionReducedSwirlResidual eps fields
          (rescalingMap data x τ) (data.physicalTime τ) := by
  unfold rescaledSwirlResidual convectionReducedSwirlResidual
  change
    deriv (fun s ↦ rescaledSwirl data fields x s) τ +
        rescaledAdvection eps
          (rescaledFields data fields)
          data.spatialRate data.axialDrift
          (fun y ↦ rescaledSwirl data fields y τ) x τ -
      (reducedSwirlSource (rescaledFields data fields) x τ +
        data.swirlRate τ * rescaledSwirl data fields x τ) = _
  rw [deriv_add_rescaledAdvection_rescaledSwirl
    eps data fields x τ hscale hfield hstream hlaws]
  rw [reducedSwirlSource_rescaledFields
    data fields x τ hscale hstream]
  ring

/-- Under `Aω = AL`, the vorticity residual of the pullback is
`A Aω` times the physical residual. This uses the source scaling as well as
the time and space chain rules. -/
theorem rescaledVorticityResidual_rescaledFields
    (eps : ℝ) (data : Rescaling) (fields : ReducedFields)
    (x : ℝ^2) (τ : ℝ)
    (hscale : data.spatialScale τ ≠ 0)
    (hcompat : data.vorticityScale τ = data.swirlScale τ * data.spatialScale τ)
    (hfield :
      DifferentiableAt ℝ (Function.uncurry fields.vorticity)
        (rescalingMap data x τ, data.physicalTime τ))
    (hswirl :
      DifferentiableAt ℝ
        (fun y ↦ fields.swirl y (data.physicalTime τ))
        (rescalingMap data x τ))
    (hstream :
      DifferentiableAt ℝ
        (fun y ↦ fields.streamFunction y (data.physicalTime τ))
        (rescalingMap data x τ))
    (hlaws : Rescaling.SatisfiesScaleLawsAt data τ) :
    rescaledVorticityResidual eps
        (rescaledFields data fields)
        data.spatialRate data.axialDrift data.vorticityRate x τ =
      (data.swirlScale τ * data.vorticityScale τ) *
        convectionReducedVorticityResidual eps fields
          (rescalingMap data x τ) (data.physicalTime τ) := by
  unfold rescaledVorticityResidual convectionReducedVorticityResidual
  change
    deriv (fun s ↦ rescaledVorticity data fields x s) τ +
        rescaledAdvection eps
          (rescaledFields data fields)
          data.spatialRate data.axialDrift
          (fun y ↦ rescaledVorticity data fields y τ) x τ -
      (reducedVorticitySource (rescaledFields data fields) x τ +
        data.vorticityRate τ * rescaledVorticity data fields x τ) = _
  rw [deriv_add_rescaledAdvection_rescaledVorticity
    eps data fields x τ hscale hfield hstream hlaws]
  rw [reducedVorticitySource_rescaledFields_compatible
    data fields x τ hcompat hswirl]
  ring

/-- The physical equations imply the dynamic equations and the rate identity.

Swirl and vorticity are jointly differentiable at the mapped points. The streamfunction
is spatially `C²`. The scale identity holds near each rescaled time, and the five
scale and clock laws hold there. The ordinary elliptic equation is used at positive radius. -/
theorem satisfiesRescaledEquationsOn_of_scale_compatibility
    (eps : ℝ) (data : Rescaling) (fields : ReducedFields)
    (physicalDomain rescaledDomain : Set (ℝ^2))
    (physicalTimes rescaledTimes : Set ℝ)
    (hphysical :
      SatisfiesPhysicalEquationsOn eps fields physicalDomain physicalTimes)
    (hdomain : rescaledDomain ⊆ positiveRadiusMeridian)
    (hmap :
      ∀ ⦃x : ℝ^2⦄ ⦃τ : ℝ⦄, x ∈ rescaledDomain → τ ∈ rescaledTimes →
        rescalingMap data x τ ∈ physicalDomain ∧
          data.physicalTime τ ∈ physicalTimes)
    (hswirl_pos :
      ∀ ⦃τ : ℝ⦄, τ ∈ rescaledTimes → 0 < data.swirlScale τ)
    (hspatial_pos :
      ∀ ⦃τ : ℝ⦄, τ ∈ rescaledTimes → 0 < data.spatialScale τ)
    (hswirlScale :
      ∀ ⦃τ : ℝ⦄, τ ∈ rescaledTimes →
        HasDerivAt data.swirlScale (data.swirlRate τ * data.swirlScale τ) τ)
    (hspatialScale :
      ∀ ⦃τ : ℝ⦄, τ ∈ rescaledTimes →
        HasDerivAt data.spatialScale (-data.spatialRate τ * data.spatialScale τ) τ)
    (hvorticityScale :
      ∀ ⦃τ : ℝ⦄, τ ∈ rescaledTimes →
        HasDerivAt data.vorticityScale (data.vorticityRate τ * data.vorticityScale τ) τ)
    (hcenter :
      ∀ ⦃τ : ℝ⦄, τ ∈ rescaledTimes →
        HasDerivAt (fun s ↦ data.axialCenter s • axialUnit)
          ((-data.axialDrift τ * data.spatialScale τ) • axialUnit) τ)
    (hclock :
      ∀ ⦃τ : ℝ⦄, τ ∈ rescaledTimes →
        HasDerivAt data.physicalTime (data.swirlScale τ) τ)
    (hcompat :
      ∀ ⦃τ : ℝ⦄, τ ∈ rescaledTimes →
        data.vorticityScale =ᶠ[𝓝 τ] fun s ↦ data.swirlScale s * data.spatialScale s)
    (hswirl :
      ∀ ⦃x : ℝ^2⦄ ⦃τ : ℝ⦄, x ∈ rescaledDomain → τ ∈ rescaledTimes →
        DifferentiableAt ℝ (Function.uncurry fields.swirl)
          (rescalingMap data x τ, data.physicalTime τ))
    (hvorticity :
      ∀ ⦃x : ℝ^2⦄ ⦃τ : ℝ⦄, x ∈ rescaledDomain → τ ∈ rescaledTimes →
        DifferentiableAt ℝ (Function.uncurry fields.vorticity)
          (rescalingMap data x τ, data.physicalTime τ))
    (hstream :
      ∀ ⦃τ : ℝ⦄, τ ∈ rescaledTimes →
        ContDiff ℝ 2 (fun y ↦ fields.streamFunction y (data.physicalTime τ))) :
    SatisfiesRescaledEquationsOn eps
        (rescaledFields data fields)
        data.spatialRate data.axialDrift data.swirlRate data.vorticityRate
        rescaledDomain rescaledTimes ∧
      ∀ ⦃τ : ℝ⦄, τ ∈ rescaledTimes →
        data.vorticityRate τ = data.swirlRate τ - data.spatialRate τ := by
  have hodes ⦃τ : ℝ⦄ (hτ : τ ∈ rescaledTimes) :
      Rescaling.SatisfiesScaleLawsAt data τ := by
    refine
      { swirlScale_hasDerivAt := hswirlScale hτ
        spatialScale_hasDerivAt := hspatialScale hτ
        vorticityScale_hasDerivAt := hvorticityScale hτ
        axialShift_hasDerivAt := hcenter hτ
        physicalTime_hasDerivAt := hclock hτ }
  have hrate ⦃τ : ℝ⦄ (hτ : τ ∈ rescaledTimes) :
      data.vorticityRate τ = data.swirlRate τ - data.spatialRate τ :=
    (hodes hτ).vorticityRate_eq_of_scale_compatibility
      (hswirl_pos hτ).ne' (hspatial_pos hτ).ne' (hcompat hτ)
  have hswirlSpatial ⦃x : ℝ^2⦄ ⦃τ : ℝ⦄
      (hx : x ∈ rescaledDomain) (hτ : τ ∈ rescaledTimes) :
      DifferentiableAt ℝ (fun y ↦ fields.swirl y (data.physicalTime τ))
        (rescalingMap data x τ) :=
    (hswirl hx hτ).comp (f := fun y : ℝ^2 ↦ (y, data.physicalTime τ))
      (rescalingMap data x τ)
      (differentiableAt_id.prodMk (differentiableAt_const _))
  rcases hphysical with ⟨hphysicalSwirl, hphysicalVorticity, hphysicalStream⟩
  refine ⟨⟨?_, ?_, ?_⟩, hrate⟩
  · intro x τ hx hτ
    have hmapped := hmap hx hτ
    have hresidual :=
      rescaledSwirlResidual_rescaledFields
        eps data fields x τ (hspatial_pos hτ).ne'
        (hswirl hx hτ)
        ((hstream hτ).differentiable (by norm_num)).differentiableAt (hodes hτ)
    change rescaledSwirlResidual eps
      (rescaledFields data fields)
      data.spatialRate data.axialDrift data.swirlRate x τ = 0
    rw [hresidual]
    rw [hphysicalSwirl hmapped.1 hmapped.2, mul_zero]
  · intro x τ hx hτ
    have hmapped := hmap hx hτ
    have hresidual :=
      rescaledVorticityResidual_rescaledFields
        eps data fields x τ (hspatial_pos hτ).ne' (hcompat hτ).eq_of_nhds
        (hvorticity hx hτ) (hswirlSpatial hx hτ)
        ((hstream hτ).differentiable (by norm_num)).differentiableAt (hodes hτ)
    change rescaledVorticityResidual eps
      (rescaledFields data fields)
      data.spatialRate data.axialDrift data.vorticityRate x τ = 0
    rw [hresidual]
    rw [hphysicalVorticity hmapped.1 hmapped.2, mul_zero]
  · intro x τ hx hτ
    have hmapped := hmap hx hτ
    rw [reducedStreamFunctionResidual_rescaledFields
      data fields x τ (hstream hτ) (hspatial_pos hτ).ne' (hcompat hτ).eq_of_nhds
      (ne_of_gt (hdomain hx))]
    rw [hphysicalStream hmapped.1 hmapped.2, mul_zero]

end

end Euler.Axisymmetric
