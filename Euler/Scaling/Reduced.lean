/-
Copyright (c) 2026 Robert Joseph George and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/

module

public import Euler.Scaling
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.WithLp

/-!
# Scaling of reduced azimuthal variables

On the meridian half-plane `(r,0,z)` with `r > 0`, the second Cartesian
component is the azimuthal component. Dividing this component by `r`
defines the reduced variable. The same construction applied to the actual
curl defines reduced azimuthal vorticity.

The formulas S418–S420 follow from the full-field scaling and one more
factor of `η` for the radial denominator. For an axisymmetric field these
meridian traces are precisely the reduced fields used in the stability
equations. No axisymmetry assumption is needed for the trace identities.
-/

@[expose] public section

noncomputable section

namespace Euler

open Cartesian

open Euler.Similarity

/-- The meridian point `(r,z)` as the Cartesian point `(r,0,z)`. -/
def meridianEmbedding (x : ℝ^2) : ℝ^3 :=
  Euler.Cartesian.vector (x 0) 0 (x 1)

/-- Meridian embedding commutes with spatial dilation. -/
theorem meridianEmbedding_smul (η : ℝ) (x : ℝ^2) :
    meridianEmbedding (η • x) = η • meridianEmbedding x := by
  ext i
  fin_cases i <;> simp [meridianEmbedding, Euler.Cartesian.vector, smul_eq_mul]

/-- The meridian embedding is differentiable. -/
@[fun_prop]
theorem differentiable_meridianEmbedding : Differentiable ℝ meridianEmbedding := by
  apply (differentiable_piLp 2).mpr
  intro i
  fin_cases i
  · change Differentiable ℝ (fun x : ℝ^2 ↦ x 0)
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) 0).differentiable
  · change Differentiable ℝ (fun _ : ℝ^2 ↦ (0 : ℝ))
    fun_prop
  · change Differentiable ℝ (fun x : ℝ^2 ↦ x 1)
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) 1).differentiable

/-- The azimuthal component divided by radius, on the meridian half-plane.
At `r = 0` this expression uses Lean's totalized division; its physical use is at `r > 0`. -/
def reducedAzimuthalComponent (v : VectorField) (x : ℝ^2) (t : ℝ) : ℝ :=
  v (meridianEmbedding x) t 1 / x 0

/-- Reduced vorticity is obtained from the velocity curl, not independent data. -/
def reducedAzimuthalVorticity (u : VectorField) (x : ℝ^2) (t : ℝ) : ℝ :=
  reducedAzimuthalComponent (curl u) x t

/-- Dividing by radius contributes one spatial-scale factor. -/
theorem reducedAzimuthalComponent_scaleVectorField
    (A η θ : ℝ) (hη : η ≠ 0) (v : VectorField) (x : ℝ^2) (t : ℝ) :
    reducedAzimuthalComponent (scaleVectorField A η θ v) x t =
      (A * η) * reducedAzimuthalComponent v (η • x) (θ * t) := by
  simp only [reducedAzimuthalComponent, scaleVectorField, PiLp.toLp_apply,
    meridianEmbedding_smul, PiLp.smul_apply, smul_eq_mul]
  rw [mul_assoc, ← mul_div_assoc, mul_div_mul_left _ _ hη]
  ring

/-- The reduced velocity carries amplitude `η^(α+1)`, the first formula of S419. -/
theorem reducedAzimuthalComponent_scaledVelocity
    {η α : ℝ} (hη : 0 < η) (u : VectorField) (x : ℝ^2) (t : ℝ) :
    reducedAzimuthalComponent (scaledVelocity η α u) x t =
      η ^ (α + 1) * reducedAzimuthalComponent u (η • x) (η ^ (α + 1) * t) := by
  rw [scaledVelocity, reducedAzimuthalComponent_scaleVectorField _ _ _ hη.ne',
    ← Real.rpow_add_one hη.ne' α]

/-- The reduced curl carries amplitude `η^(α+2)`, the second formula of S419. -/
theorem reducedAzimuthalVorticity_scaledVelocity
    {η α : ℝ} (hη : 0 < η) (u : VectorField) (x : ℝ^2) (t : ℝ)
    (hu : ∀ i, DifferentiableAt ℝ
      (fun y ↦ u y (η ^ (α + 1) * t) i) (η • meridianEmbedding x)) :
    reducedAzimuthalVorticity (scaledVelocity η α u) x t =
      η ^ (α + 2) * reducedAzimuthalVorticity u (η • x) (η ^ (α + 1) * t) := by
  have hfactor : η ^ (α + 2) = η ^ (α + 1) * η := by
    rw [show α + 2 = (α + 1) + 1 by ring, Real.rpow_add hη, Real.rpow_one]
  unfold reducedAzimuthalVorticity reducedAzimuthalComponent
  rw [curl_scaledVelocity hη u (meridianEmbedding x) t hu]
  simp only [meridianEmbedding_smul, PiLp.smul_apply, smul_eq_mul]
  rw [hfactor, mul_assoc, ← mul_div_assoc, mul_div_mul_left _ _ hη.ne']
  ring

/-- The reduced component is differentiable off the axis when the corresponding
Cartesian velocity component is differentiable. -/
theorem differentiableAt_reducedAzimuthalComponent
    (u : VectorField) (x : ℝ^2) (t : ℝ) (hx : x 0 ≠ 0)
    (hu : DifferentiableAt ℝ (fun y ↦ u y t 1) (meridianEmbedding x)) :
    DifferentiableAt ℝ (fun y ↦ reducedAzimuthalComponent u y t) x := by
  simp only [reducedAzimuthalComponent, div_eq_mul_inv]
  exact (hu.comp x (differentiable_meridianEmbedding x)).mul
    (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) 0).differentiableAt).inv hx)

/-- The gradient of reduced velocity has amplitude `η^(α+2)`, S420.
Only the azimuthal velocity component needs one spatial derivative. -/
theorem gradient_reducedAzimuthalComponent_scaledVelocity
    {η α : ℝ} (hη : 0 < η) (u : VectorField) (x : ℝ^2) (t : ℝ)
    (hx : 0 < x 0)
    (hu : DifferentiableAt ℝ (fun y ↦ u y (η ^ (α + 1) * t) 1)
      (η • meridianEmbedding x)) :
    _root_.gradient (fun y ↦ reducedAzimuthalComponent (scaledVelocity η α u) y t) x =
      η ^ (α + 2) •
        _root_.gradient (fun y ↦ reducedAzimuthalComponent u y (η ^ (α + 1) * t)) (η • x) := by
  have hquot : DifferentiableAt ℝ
      (fun y ↦ reducedAzimuthalComponent u y (η ^ (α + 1) * t)) (η • x) :=
    differentiableAt_reducedAzimuthalComponent u (η • x) _ (by
      change η * x 0 ≠ 0
      exact (mul_pos hη hx).ne') (by simpa only [meridianEmbedding_smul] using hu)
  have hfun :
      (fun y ↦ reducedAzimuthalComponent (scaledVelocity η α u) y t) =
        fun y ↦ η ^ (α + 1) * reducedAzimuthalComponent u (η • y) (η ^ (α + 1) * t) := by
    funext y
    exact reducedAzimuthalComponent_scaledVelocity hη u y t
  rw [hfun]
  ext i
  simp only [gradient_apply_eq_partialDeriv, PiLp.smul_apply, smul_eq_mul]
  have hpartial := partialDeriv_const_mul_comp_affineDilation i
    (fun y ↦ reducedAzimuthalComponent u y (η ^ (α + 1) * t))
    (η ^ (α + 1)) η (0 : ℝ^2) x (by simpa only [affineDilation, add_zero] using hquot)
  have hfactor : η ^ (α + 1) * η = η ^ (α + 2) := by
    calc
      _ = η ^ ((α + 1) + 1) := by
        simpa only [Real.rpow_one] using (Real.rpow_add hη (α + 1) 1).symm
      _ = _ := by congr 1; ring
  simpa only [affineDilation, add_zero, hfactor] using hpartial

end Euler
