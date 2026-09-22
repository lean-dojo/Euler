/-
Copyright (c) 2026 Robert Joseph George and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/
module

public import Euler.Stability.Energy
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Weighted integrals in Appendix I

Here we connect mathlib's L² inner product and norm to the weighted integrals
in Appendix I. Represent `f` by `f * √w`; its squared L² norm is then `∫ f²w`.
The hypotheses require these weighted fields to belong to L². The weights may
vanish or be unbounded, and the underlying measure need not be finite.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Euler.Stability

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

/-- Normalized L² representatives give an integrable weighted product and its
inner-product formula. This also justifies the integrals when weights are unbounded. -/
theorem weighted_pairing {u v : Lp ℝ 2 ν} {f g w : X → ℝ}
    (hu : (u : X → ℝ) =ᵐ[ν] fun x ↦ f x * Real.sqrt (w x))
    (hv : (v : X → ℝ) =ᵐ[ν] fun x ↦ g x * Real.sqrt (w x))
    (hw : 0 ≤ᵐ[ν] w) :
    Integrable (fun x ↦ f x * g x * w x) ν ∧
      inner ℝ u v = ∫ x, f x * g x * w x ∂ν := by
  have hproduct : (fun x ↦ inner ℝ (u x) (v x)) =ᵐ[ν] fun x ↦ f x * g x * w x := by
    filter_upwards [hu, hv, hw] with x hux hvx hwx
    rw [hux, hvx, Real.inner_apply, mul_mul_mul_comm, Real.mul_self_sqrt hwx]
  exact ⟨(L2.integrable_inner (𝕜 := ℝ) u v).congr hproduct,
    (L2.inner_def u v).trans (integral_congr_ae hproduct)⟩

/-- A normalized L² norm square equals the integral of the physical square times its weight. -/
theorem weighted_norm_sq {u : Lp ℝ 2 ν} {f w : X → ℝ}
    (hu : (u : X → ℝ) =ᵐ[ν] fun x ↦ f x * Real.sqrt (w x))
    (hw : 0 ≤ᵐ[ν] w) :
    Integrable (fun x ↦ f x ^ 2 * w x) ν ∧ ‖u‖ ^ 2 = ∫ x, f x ^ 2 * w x ∂ν := by
  simpa only [real_inner_self_eq_norm_sq, ← pow_two] using weighted_pairing hu hu hw

/-- The Hilbert energy is precisely `√(E₀² + μ H_k²)` formed from the weighted
physical integrals. Each low and high row has its own weight and representative. -/
theorem energy_eq_weighted_integrals {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ t : ℝ) (low : EnergyComponents ι (Lp ℝ 2 ν)) (high : EnergyComponents κ (Lp ℝ 2 ν))
    {f w : ι → X → ℝ} {g v : κ → X → ℝ}
    (hlow : ∀ i, (low.state i t : X → ℝ) =ᵐ[ν] fun x ↦ f i x * Real.sqrt (w i x))
    (hhigh : ∀ j, (high.state j t : X → ℝ) =ᵐ[ν] fun x ↦ g j x * Real.sqrt (v j x))
    (hw : ∀ i, 0 ≤ᵐ[ν] w i) (hv : ∀ j, 0 ≤ᵐ[ν] v j) :
    energy μ low high t =
      Real.sqrt ((∑ i, ∫ x, f i x ^ 2 * w i x ∂ν) +
        μ * ∑ j, ∫ x, g j x ^ 2 * v j x ∂ν) := by
  unfold energy EnergyComponents.normSq
  congr 1
  congr 1
  · exact Finset.sum_congr rfl fun i _ ↦ (weighted_norm_sq (hlow i) (hw i)).2
  · congr 1
    exact Finset.sum_congr rfl fun j _ ↦ (weighted_norm_sq (hhigh j) (hv j)).2

end Euler.Stability
