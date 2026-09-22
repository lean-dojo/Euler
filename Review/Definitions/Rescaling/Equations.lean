module

public import Review.Definitions.Rescaling.Basic

/-! # Rescaled equations -/

@[expose] public noncomputable section

namespace Euler.Axisymmetric

open scoped Topology

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

end Euler.Axisymmetric

end
