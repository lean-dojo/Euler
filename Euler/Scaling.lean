/-
Copyright (c) 2026 Robert Joseph George and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/

module

public import Euler.Scaling.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Euler scaling in Appendix F

Here we formalize S386–S417. For `η > 0`, scale velocity by `η^α`, pressure
by `η^(2α)`, and time by `η^(α+1)`. The time derivative, transport, and
pressure gradient then have the same factor `η^(2α+1)`, so the scaled fields
still satisfy the Euler equations.

The divergence, curl, and velocity gradient have factor `η^(α+1)`. Each
calculation assumes differentiability where the original fields are evaluated.
-/

@[expose] public section

noncomputable section

namespace Euler.Cartesian

/-- The rescaled velocity in S387. -/
def scaledVelocity (η α : ℝ) (u : VectorField) : VectorField :=
  scaleVectorField (η ^ α) η (η ^ (α + 1)) u

/-- The rescaled pressure in S387. -/
def scaledPressure (η α : ℝ) (p : ScalarField) : ScalarField :=
  scaleScalarField (η ^ (2 * α)) η (η ^ (α + 1)) p

/-- The time domain sampled by the Euler scaling. -/
def scaledTimeSet (η α : ℝ) (I : Set ℝ) : Set ℝ :=
  pullbackTimeSet (η ^ (α + 1)) I

private theorem velocity_mul_time {η α : ℝ} (hη : 0 < η) :
    η ^ α * η ^ (α + 1) = η ^ (2 * α + 1) := by
  rw [← Real.rpow_add hη]
  congr 1
  ring

/-- The velocity formula, S387. -/
theorem scaledVelocity_apply
    (η α : ℝ) (u : VectorField) (x : ℝ^3) (t : ℝ) :
    scaledVelocity η α u x t = η ^ α • u (η • x) (η ^ (α + 1) * t) := by
  rfl

/-- The pressure formula, S387. -/
theorem scaledPressure_apply
    (η α : ℝ) (p : ScalarField) (x : ℝ^3) (t : ℝ) :
    scaledPressure η α p x t = η ^ (2 * α) * p (η • x) (η ^ (α + 1) * t) := by
  rfl

/-- The time derivative of velocity scales by `η^(2α+1)`, S390–S391. -/
theorem vectorTimeDeriv_scaledVelocity
    {η α : ℝ} (hη : 0 < η) (u : VectorField) (x : ℝ^3) (t : ℝ)
    (hu : ∀ i, DifferentiableAt ℝ (fun s ↦ u (η • x) s i) (η ^ (α + 1) * t)) :
    vectorTimeDeriv (scaledVelocity η α u) x t =
      η ^ (2 * α + 1) • vectorTimeDeriv u (η • x) (η ^ (α + 1) * t) := by
  rw [scaledVelocity, vectorTimeDeriv_scaleVectorField
    (η ^ α) η (η ^ (α + 1)) u x t hu,
    velocity_mul_time hη]

/-- Each velocity partial scales by `η^(α+1)`, S392–S394 and S412–S414. -/
theorem partialDeriv_scaledVelocity_apply
    {η α : ℝ} (hη : 0 < η) (u : VectorField) (x : ℝ^3) (t : ℝ) (i j : Fin 3)
    (hu : DifferentiableAt ℝ (fun y ↦ u y (η ^ (α + 1) * t) i) (η • x)) :
    partialDeriv j (fun y ↦ scaledVelocity η α u y t i) x =
      η ^ (α + 1) * partialDeriv j (fun y ↦ u y (η ^ (α + 1) * t) i) (η • x) := by
  rw [scaledVelocity, partialDeriv_scaleVectorField_apply
    (η ^ α) η (η ^ (α + 1)) u x t i j hu,
    ← Real.rpow_add_one hη.ne' α]

/-- The velocity gradient scales by `η^(α+1)`, S411–S415. -/
theorem velocityGradient_scaledVelocity
    {η α : ℝ} (hη : 0 < η) (u : VectorField) (x : ℝ^3) (t : ℝ)
    (hu : ∀ i, DifferentiableAt ℝ (fun y ↦ u y (η ^ (α + 1) * t) i) (η • x)) :
    velocityGradient (scaledVelocity η α u) x t =
      η ^ (α + 1) • velocityGradient u (η • x) (η ^ (α + 1) * t) := by
  rw [scaledVelocity, velocityGradient_scaleVectorField
    (η ^ α) η (η ^ (α + 1)) u x t hu,
    ← Real.rpow_add_one hη.ne' α]

/-- The curl scales by `η^(α+1)`, S402–S410. -/
theorem curl_scaledVelocity
    {η α : ℝ} (hη : 0 < η) (u : VectorField) (x : ℝ^3) (t : ℝ)
    (hu : ∀ i, DifferentiableAt ℝ (fun y ↦ u y (η ^ (α + 1) * t) i) (η • x)) :
    curl (scaledVelocity η α u) x t =
      η ^ (α + 1) • curl u (η • x) (η ^ (α + 1) * t) := by
  rw [scaledVelocity, curl_scaleVectorField
    (η ^ α) η (η ^ (α + 1)) u x t hu,
    ← Real.rpow_add_one hη.ne' α]

/-- The divergence scales by `η^(α+1)`, S401. -/
theorem divergence_scaledVelocity
    {η α : ℝ} (hη : 0 < η) (u : VectorField) (x : ℝ^3) (t : ℝ)
    (hu : ∀ i, DifferentiableAt ℝ (fun y ↦ u y (η ^ (α + 1) * t) i) (η • x)) :
    divergence (scaledVelocity η α u) x t =
      η ^ (α + 1) * divergence u (η • x) (η ^ (α + 1) * t) := by
  rw [scaledVelocity, divergence_scaleVectorField
    (η ^ α) η (η ^ (α + 1)) u x t hu,
    ← Real.rpow_add_one hη.ne' α]

/-- The nonlinear transport scales by `η^(2α+1)`, S395. -/
theorem advection_scaledVelocity
    {η α : ℝ} (hη : 0 < η) (u : VectorField) (x : ℝ^3) (t : ℝ)
    (hu : ∀ i, DifferentiableAt ℝ (fun y ↦ u y (η ^ (α + 1) * t) i) (η • x)) :
    advection (scaledVelocity η α u) (scaledVelocity η α u) x t =
      η ^ (2 * α + 1) • advection u u (η • x) (η ^ (α + 1) * t) := by
  rw [scaledVelocity, advection_scaleVectorField
    (η ^ α) (η ^ α) η (η ^ (α + 1)) u u x t hu,
    ← Real.rpow_add_one hη.ne' α, velocity_mul_time hη]

/-- Each pressure partial scales by `η^(2α+1)`, S396–S397. -/
theorem spaceDeriv_scaledPressure
    {η α : ℝ} (hη : 0 < η) (p : ScalarField) (x : ℝ^3) (t : ℝ) (i : Fin 3)
    (hp : DifferentiableAt ℝ (fun y ↦ p y (η ^ (α + 1) * t)) (η • x)) :
    spaceDeriv i (scaledPressure η α p) x t =
      η ^ (2 * α + 1) * spaceDeriv i p (η • x) (η ^ (α + 1) * t) := by
  rw [scaledPressure, spaceDeriv_scaleScalarField
    (η ^ (2 * α)) η (η ^ (α + 1)) p x t i hp,
    ← Real.rpow_add_one hη.ne' (2 * α)]

/-- The pressure gradient scales by `η^(2α+1)`, S398. -/
theorem gradient_scaledPressure
    {η α : ℝ} (hη : 0 < η) (p : ScalarField) (x : ℝ^3) (t : ℝ)
    (hp : DifferentiableAt ℝ (fun y ↦ p y (η ^ (α + 1) * t)) (η • x)) :
    gradient (scaledPressure η α p) x t =
      η ^ (2 * α + 1) • gradient p (η • x) (η ^ (α + 1) * t) := by
  rw [scaledPressure, gradient_scaleScalarField
    (η ^ (2 * α)) η (η ^ (α + 1)) p x t hp,
    ← Real.rpow_add_one hη.ne' (2 * α)]

/-- All three terms of the Euler momentum residual have the same factor, S399. -/
theorem momentumResidual_scaling
    {η α : ℝ} (hη : 0 < η) (u : VectorField) (p : ScalarField) (x : ℝ^3) (t : ℝ)
    (ht : ∀ i, DifferentiableAt ℝ (fun s ↦ u (η • x) s i) (η ^ (α + 1) * t))
    (hx : ∀ i, DifferentiableAt ℝ (fun y ↦ u y (η ^ (α + 1) * t) i) (η • x))
    (hp : DifferentiableAt ℝ (fun y ↦ p y (η ^ (α + 1) * t)) (η • x)) :
    momentumResidual (scaledVelocity η α u) (scaledPressure η α p) x t =
      η ^ (2 * α + 1) • momentumResidual u p (η • x) (η ^ (α + 1) * t) := by
  unfold momentumResidual
  rw [vectorTimeDeriv_scaledVelocity hη u x t ht,
    advection_scaledVelocity hη u x t hx,
    gradient_scaledPressure hη p x t hp]
  ext i
  simp only [PiLp.smul_apply, smul_eq_mul]
  ring

/-- Scaling preserves the Euler momentum and incompressibility equations on the
preimage time domain. Only first derivatives of the velocity and pressure are used. -/
theorem scaling_preserves_equations
    {η α : ℝ} (hη : 0 < η) (u : VectorField) (p : ScalarField) (I : Set ℝ)
    (ht : ∀ x t, t ∈ I → ∀ i, DifferentiableAt ℝ (fun s ↦ u x s i) t)
    (hx : ∀ x t, t ∈ I → ∀ i, DifferentiableAt ℝ (fun y ↦ u y t i) x)
    (hp : ∀ x t, t ∈ I → DifferentiableAt ℝ (fun y ↦ p y t) x)
    (heuler : ∀ x t, t ∈ I →
      momentumResidual u p x t = 0 ∧ divergence u x t = 0) :
    ∀ x t, t ∈ scaledTimeSet η α I →
      momentumResidual (scaledVelocity η α u) (scaledPressure η α p) x t = 0 ∧
        divergence (scaledVelocity η α u) x t = 0 := by
  intro x t htime
  have hI : η ^ (α + 1) * t ∈ I := htime
  rw [momentumResidual_scaling hη u p x t (ht _ _ hI) (hx _ _ hI) (hp _ _ hI),
    divergence_scaledVelocity hη u x t (hx _ _ hI),
    (heuler _ _ hI).1, (heuler _ _ hI).2, smul_zero, mul_zero]
  exact ⟨rfl, rfl⟩

end Euler.Cartesian
