/-
Copyright (c) 2026 Robert Joseph George and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Ring

/-!
# Rates of compatible amplitudes

Differentiating the local scale identity gives the vorticity rate
`cω = cu - λ`. The identity is required on a neighborhood of the time,
so the product rule applies to the same scale functions.
-/

@[expose] public section

open scoped Topology

namespace Euler.Similarity

/-- The logarithmic rate of a nonzero product is the sum of the factor rates.
Compatibility is required near the time of differentiation, not just at that time. -/
theorem logarithmicRate_eq_add_of_eventuallyEq_mul
    {a b c : ℝ → ℝ} {aRate bRate cRate τ : ℝ}
    (ha : HasDerivAt a (aRate * a τ) τ)
    (hb : HasDerivAt b (bRate * b τ) τ)
    (hc : HasDerivAt c (cRate * c τ) τ)
    (hc_ne : c τ ≠ 0)
    (hcompat : c =ᶠ[𝓝 τ] fun t ↦ a t * b t) :
    cRate = aRate + bRate := by
  apply mul_right_cancel₀ hc_ne
  have hderiv := hc.unique ((ha.mul hb).congr_of_eventuallyEq hcompat)
  calc
    cRate * c τ = (aRate * a τ) * b τ + a τ * (bRate * b τ) := hderiv
    _ = (aRate + bRate) * (a τ * b τ) := by ring
    _ = (aRate + bRate) * c τ := by rw [hcompat.eq_of_nhds]

/-- A real solution of a constant-rate equation on a closed half-line is determined by
its initial value. Multiplication by the reciprocal exponential gives a constant function. -/
theorem eq_mul_exp_of_hasDerivAt_const_mul_on_Ici
    {f : ℝ → ℝ} {rate t₀ t : ℝ}
    (hf : ∀ s ∈ Set.Ici t₀, HasDerivAt f (rate * f s) s)
    (ht : t₀ ≤ t) :
    f t = f t₀ * Real.exp (rate * (t - t₀)) := by
  have hderiv : ∀ s ∈ Set.Ici t₀,
      HasDerivAt (fun y ↦ f y * Real.exp (-rate * (y - t₀))) 0 s := by
    intro s hs
    have hexp : HasDerivAt (fun y ↦ Real.exp (-rate * (y - t₀)))
        (Real.exp (-rate * (s - t₀)) * -rate) s := by
      simpa only [id_eq, mul_one] using (((hasDerivAt_id s).sub_const t₀).const_mul (-rate)).exp
    convert (hf s hs).mul hexp using 1
    ring
  -- The integrating factor makes the derivative zero on the whole interval.
  have hconst : f t * Real.exp (-rate * (t - t₀)) = f t₀ := by
    simpa using constant_of_has_deriv_right_zero
      (fun s hs ↦ (hderiv s hs.1).continuousAt.continuousWithinAt)
      (fun s hs ↦ (hderiv s hs.1).hasDerivWithinAt) t ⟨ht, le_rfl⟩
  calc
    f t = (f t * Real.exp (-rate * (t - t₀))) * Real.exp (rate * (t - t₀)) := by
      rw [mul_assoc, ← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero, mul_one]
    _ = f t₀ * Real.exp (rate * (t - t₀)) := by rw [hconst]

end Euler.Similarity

namespace Euler.Axisymmetric

open Euler.Similarity

/-- Differentiating the physical-amplitude identity `sᵤ = sω sᵣ` derives the vorticity rate.
Only nonvanishing of `sᵤ` is needed for cancellation. -/
theorem vorticityRate_eq_sub_of_physicalScale_compatibility
    {swirlScale vorticityScale spatialScale : ℝ → ℝ}
    {swirlRate vorticityRate spatialRate τ : ℝ}
    (hswirl : HasDerivAt swirlScale (-swirlRate * swirlScale τ) τ)
    (hvorticity : HasDerivAt vorticityScale (-vorticityRate * vorticityScale τ) τ)
    (hspatial : HasDerivAt spatialScale (-spatialRate * spatialScale τ) τ)
    (hswirl_ne : swirlScale τ ≠ 0)
    (hcompat : swirlScale =ᶠ[𝓝 τ] fun t ↦ vorticityScale t * spatialScale t) :
    vorticityRate = swirlRate - spatialRate := by
  have hrate := logarithmicRate_eq_add_of_eventuallyEq_mul
    hvorticity hspatial hswirl hswirl_ne hcompat
  have hsum : swirlRate = vorticityRate + spatialRate :=
    neg_inj.mp (by simpa only [neg_add] using hrate)
  exact eq_sub_iff_add_eq.mpr hsum.symm

/-- The physical convection and stretching coefficients match the clock normalization. -/
theorem physicalScale_coefficient_identities
    (su sw sr clockRate : ℝ) (hsr : sr ≠ 0)
    (hsu : su = sw * sr) (hclock : clockRate = sw * sr) :
    (sw * sr ^ 2) * (su / sr) = su * clockRate ∧
      (sw * sr ^ 2) * (sw / sr) = sw * clockRate ∧
      su ^ 2 / sr = sw * clockRate := by
  rw [hsu, hclock]
  constructor
  · field_simp
  · constructor <;> field_simp

end Euler.Axisymmetric
