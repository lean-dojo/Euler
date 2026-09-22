/-
Copyright (c) 2026 Robert Joseph George and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/

module

public import Euler.Equations.Cartesian
public import Euler.Rescaling.Affine
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Derivatives of scaled fields

Here we prove the chain rules used in Appendix F, S390–S415. Scaling space,
time, and amplitude gives factors in the pressure gradient, divergence, curl,
and transport terms. The amplitudes remain parameters until `Scaling.lean`
chooses the powers required by the Euler equations.
-/

@[expose] public section

noncomputable section

namespace Euler.Cartesian

open Euler.Similarity

/-! ## Constant space-time pullbacks -/

/-- A scalar field pulled back by constant spatial and temporal dilations, with amplitude `A`. -/
def scaleScalarField (A η θ : ℝ) (f : ScalarField) : ScalarField :=
  fun x t ↦ A * f (η • x) (θ * t)

/-- A vector field pulled back by constant spatial and temporal dilations, with amplitude `A`. -/
def scaleVectorField (A η θ : ℝ) (u : VectorField) : VectorField :=
  fun x t ↦ WithLp.toLp 2 fun i ↦ A * u (η • x) (θ * t) i

/-- The time set on which a pullback by `t ↦ θt` samples a prescribed time set `I`. -/
def pullbackTimeSet (θ : ℝ) (I : Set ℝ) : Set ℝ :=
  (fun t ↦ θ * t) ⁻¹' I

/-- The one-dimensional chain rule for a constant-amplitude, constant-time-dilation pullback. -/
theorem scalarTimeDeriv_scaleScalarField
    (A η θ : ℝ) (f : ScalarField) (x : ℝ^3) (t : ℝ)
    (hf : DifferentiableAt ℝ (fun τ ↦ f (η • x) τ) (θ * t)) :
    scalarTimeDeriv (scaleScalarField A η θ f) x t =
      A * θ * scalarTimeDeriv f (η • x) (θ * t) := by
  simpa [scalarTimeDeriv, scaleScalarField, Function.comp_def, mul_assoc, mul_comm,
    mul_left_comm] using
    ((hf.hasDerivAt.comp t (hasDerivAt_const_mul θ)).const_mul A).deriv

/-- The componentwise time derivative of a scaled vector field gains amplitude and time factors. -/
theorem vectorTimeDeriv_scaleVectorField
    (A η θ : ℝ) (u : VectorField) (x : ℝ^3) (t : ℝ)
    (hu : ∀ i, DifferentiableAt ℝ (fun τ ↦ u (η • x) τ i) (θ * t)) :
    vectorTimeDeriv (scaleVectorField A η θ u) x t =
      (A * θ) • vectorTimeDeriv u (η • x) (θ * t) := by
  ext i
  change deriv (fun τ ↦ A * u (η • x) (θ * τ) i) t =
    A * θ * deriv (fun τ ↦ u (η • x) τ i) (θ * t)
  simpa [scalarTimeDeriv, scaleScalarField] using
    scalarTimeDeriv_scaleScalarField A η θ (fun y s ↦ u y s i) x t (hu i)

/-- The spatial partial operator on scalar fields obeys the constant-dilation chain rule. -/
theorem spaceDeriv_scaleScalarField
    (A η θ : ℝ) (f : ScalarField) (x : ℝ^3) (t : ℝ) (i : Fin 3)
    (hf : DifferentiableAt ℝ (fun y ↦ f y (θ * t)) (η • x)) :
    spaceDeriv i (scaleScalarField A η θ f) x t =
      A * η * spaceDeriv i f (η • x) (θ * t) := by
  have h :=
    partialDeriv_const_mul_comp_affineDilation i
      (fun y ↦ f y (θ * t)) A η (0 : ℝ^3) x
      (by simpa [affineDilation] using hf)
  simpa [spaceDeriv, scaleScalarField, affineDilation] using h

/-- The gradient of a scaled scalar field gains its amplitude and spatial factors. -/
theorem gradient_scaleScalarField
    (A η θ : ℝ) (f : ScalarField) (x : ℝ^3) (t : ℝ)
    (hf : DifferentiableAt ℝ (fun y ↦ f y (θ * t)) (η • x)) :
    gradient (scaleScalarField A η θ f) x t =
      (A * η) • gradient f (η • x) (θ * t) := by
  ext i
  simpa [gradient, spaceDeriv, smul_eq_mul] using
    spaceDeriv_scaleScalarField A η θ f x t i hf

/-- A componentwise spatial partial of a scaled vector field gains amplitude and spatial factors. -/
theorem partialDeriv_scaleVectorField_apply
    (A η θ : ℝ) (u : VectorField) (x : ℝ^3) (t : ℝ) (i j : Fin 3)
    (hu : DifferentiableAt ℝ (fun y ↦ u y (θ * t) i) (η • x)) :
    partialDeriv j (fun y ↦ scaleVectorField A η θ u y t i) x =
      A * η * partialDeriv j (fun y ↦ u y (θ * t) i) (η • x) := by
  have h :=
    partialDeriv_const_mul_comp_affineDilation j
      (fun y ↦ u y (θ * t) i) A η (0 : ℝ^3) x
      (by simpa [affineDilation] using hu)
  simpa [scaleVectorField, PiLp.toLp_apply, affineDilation] using h

/-- The velocity gradient of a scaled vector field gains amplitude and spatial factors. -/
theorem velocityGradient_scaleVectorField
    (A η θ : ℝ) (u : VectorField) (x : ℝ^3) (t : ℝ)
    (hu : ∀ i, DifferentiableAt ℝ (fun y ↦ u y (θ * t) i) (η • x)) :
    velocityGradient (scaleVectorField A η θ u) x t =
      (A * η) • velocityGradient u (η • x) (θ * t) := by
  ext ij
  rcases ij with ⟨i, j⟩
  simpa [velocityGradient, PiLp.toLp_apply, smul_eq_mul] using
    partialDeriv_scaleVectorField_apply A η θ u x t i j (hu i)

/-- The divergence of a scaled vector field gains amplitude and spatial factors. -/
theorem divergence_scaleVectorField
    (A η θ : ℝ) (u : VectorField) (x : ℝ^3) (t : ℝ)
    (hu : ∀ i, DifferentiableAt ℝ (fun y ↦ u y (θ * t) i) (η • x)) :
    divergence (scaleVectorField A η θ u) x t =
      A * η * divergence u (η • x) (θ * t) := by
  unfold divergence _root_.divergence
  simp_rw [partialDeriv_scaleVectorField_apply A η θ u x t _ _ (hu _)]
  rw [Finset.mul_sum]

/-- The curl of a scaled vector field gains amplitude and spatial factors. -/
theorem curl_scaleVectorField
    (A η θ : ℝ) (u : VectorField) (x : ℝ^3) (t : ℝ)
    (hu : ∀ i, DifferentiableAt ℝ (fun y ↦ u y (θ * t) i) (η • x)) :
    curl (scaleVectorField A η θ u) x t =
      (A * η) • curl u (η • x) (θ * t) := by
  have hpartial (i j : Fin 3) :
      partialDeriv j (fun y ↦ scaleVectorField A η θ u y t i) x =
        A * η * partialDeriv j (fun y ↦ u y (θ * t) i) (η • x) :=
    partialDeriv_scaleVectorField_apply A η θ u x t i j (hu i)
  -- Every curl component is a difference of two equally scaled first derivatives.
  ext i
  fin_cases i <;>
    simp [curl, hpartial, mul_sub]

/-- Advection of two scaled fields gains both amplitudes and one spatial factor. -/
theorem advection_scaleVectorField
    (A B η θ : ℝ) (u v : VectorField) (x : ℝ^3) (t : ℝ)
    (hv : ∀ i, DifferentiableAt ℝ (fun y ↦ v y (θ * t) i) (η • x)) :
    advection
        (scaleVectorField A η θ u) (scaleVectorField B η θ v) x t =
      (A * (B * η)) • advection u v (η • x) (θ * t) := by
  ext i
  simp only [advection, PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul]
  simp_rw [partialDeriv_scaleVectorField_apply B η θ v x t _ _ (hv _)]
  simp [scaleVectorField, Finset.mul_sum, mul_left_comm, mul_assoc]

end Euler.Cartesian
