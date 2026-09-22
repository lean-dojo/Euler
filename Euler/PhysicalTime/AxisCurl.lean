/-
Copyright (c) 2026 Robert Joseph George and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/

module

public import Euler.Equations.Cartesian
public import Euler.Calculus.ChainRule
public import Euler.PhysicalTime.AmplitudeClock
public import Euler.PhysicalTime.ReciprocalClock
public import Euler.PhysicalTime.ContractingCenter
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Vorticity on the axis

For Appendix J, write the transverse velocity as `(-a x - b y, -a y + b x)`,
where `b` is the reduced swirl. At `x = y = 0`, the product rule gives
`curl_z = 2b`: the other terms contain a factor of `x` or `y` and vanish.

We combine this identity with the amplitude estimates to prove curl growth.
Differentiability of `a` and `b` gives the axis identity. Spatial continuity of
curl then gives growth of its essential supremum. These lemmas assume the
normalization and regularity; they do not require or prove the Euler equations.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Euler.PhysicalTime
open scoped Topology ENNReal

namespace Euler

open Cartesian

/-- A point on the Cartesian symmetry axis. -/
def axisPoint (z : ℝ) : ℝ^3 := vector 0 0 z

/-- Cartesian velocity with reduced swirl `b`; the axial component is `w`. -/
def axisymmetricVelocity (a b w : ScalarField) : VectorField :=
  fun x t ↦ vector
    (-(a x t * x 0) - b x t * x 1)
    (-(a x t * x 1) + b x t * x 0)
    (w x t)

/-- With azimuthal velocity `r * u r`, the radial expression for axial
vorticity expands as in (S553). The Cartesian theorem below supplies its
regular value on the axis, where this quotient is not used. -/
theorem radial_swirl_derivative_eq (u : ℝ → ℝ) {r : ℝ}
    (hr : r ≠ 0) (hu : DifferentiableAt ℝ u r) :
    r⁻¹ * deriv (fun s ↦ s * (s * u s)) r =
      2 * u r + r * deriv u r := by
  rw [deriv_fun_mul (c := fun s : ℝ ↦ s) (d := fun s ↦ s * u s)
    differentiableAt_id (differentiableAt_id.mul hu)]
  rw [deriv_fun_mul (c := fun s : ℝ ↦ s) differentiableAt_id hu]
  simp only [deriv_id'', one_mul]
  field_simp
  ring

/-- The regular axis value of the axial curl is twice the reduced swirl,
as in equation (S554). Only differentiability at the axis point is needed. -/
theorem curl_axisymmetricVelocity_axisPoint_two
    (a b w : ScalarField) (z t : ℝ)
    (ha : DifferentiableAt ℝ (fun x ↦ a x t) (axisPoint z))
    (hb : DifferentiableAt ℝ (fun x ↦ b x t) (axisPoint z)) :
    curl (axisymmetricVelocity a b w) (axisPoint z) t 2 =
      2 * b (axisPoint z) t := by
  have hc (i : Fin 3) :
      DifferentiableAt ℝ (fun x : ℝ^3 ↦ x i) (axisPoint z) :=
    (EuclideanSpace.proj i : ℝ^3 →L[ℝ] ℝ).differentiableAt
  simp only [curl, axisymmetricVelocity, vector_apply_two,
    vector_apply_one, vector_apply_zero]
  simp (discharger := fun_prop) only [partialDeriv_add, partialDeriv_sub,
    partialDeriv_mul, partialDeriv_coord]
  simp only [show (fun x : ℝ^3 ↦ -(a x t * x 1)) =
      -(fun x : ℝ^3 ↦ a x t * x 1) from rfl,
    show (fun x : ℝ^3 ↦ -(a x t * x 0)) =
      -(fun x : ℝ^3 ↦ a x t * x 0) from rfl,
    partialDeriv_neg]
  rw [partialDeriv_mul ha (hc 1), partialDeriv_mul ha (hc 0)]
  simp [partialDeriv_coord, axisPoint]
  ring

/-- Positive amplitude and a nonzero axis normalization make the magnitude
of the axial curl diverge, equation (S555). -/
theorem tendsto_abs_axis_curl_atTop
    (a b w : ScalarField) (clock center sU cU : ℝ → ℝ)
    (barU gamma : ℝ)
    (hgamma : 0 < gamma) (hsU0 : 0 < sU 0) (hbarU : barU ≠ 0)
    (hscale : ∀ τ ∈ Ici (0 : ℝ), HasDerivAt sU (-cU τ * sU τ) τ)
    (hrate : ∀ τ ∈ Ici (0 : ℝ), cU τ ≤ -gamma)
    (ha : ∀ τ ∈ Ici (0 : ℝ),
      DifferentiableAt ℝ (fun x ↦ a x (clock τ)) (axisPoint (center τ)))
    (hb : ∀ τ ∈ Ici (0 : ℝ),
      DifferentiableAt ℝ (fun x ↦ b x (clock τ)) (axisPoint (center τ)))
    (hnormalize : ∀ τ ∈ Ici (0 : ℝ),
      b (axisPoint (center τ)) (clock τ) = sU τ * barU) :
    Tendsto
      (fun τ ↦ |curl (axisymmetricVelocity a b w)
        (axisPoint (center τ)) (clock τ) 2|) atTop atTop := by
  apply tendsto_abs_axial_vorticity_atTop sU cU _ barU gamma
    hgamma hsU0 hbarU hscale hrate
  intro τ hτ
  rw [curl_axisymmetricVelocity_axisPoint_two a b w _ _ (ha τ hτ) (hb τ hτ),
    hnormalize τ hτ]

/-- A continuous vector field is bounded pointwise by its essential supremum.
Continuity is what permits evaluating an almost-everywhere bound on the axis. -/
theorem enorm_le_eLpNorm_top_of_continuous
    {f : ℝ^3 → ℝ^3} (hf : Continuous f) (x : ℝ^3) :
    ‖f x‖ₑ ≤ eLpNorm f (⊤ : ℝ≥0∞) volume := by
  rw [eLpNorm_exponent_top hf.aestronglyMeasurable]
  simpa only [closure_le_eq hf.enorm continuous_const, mem_ofPred_eq] using
    ((volume : Measure (ℝ^3)).dense_of_ae (ae_le_eLpNormEssSup (f := f)) x)

/-- Divergence of one curl component along the axis forces divergence of the
essential `L∞` norm of the full curl, equation (S548). -/
theorem tendsto_eLpNorm_curl_of_axis_growth
    (v : VectorField) (clock center : ℝ → ℝ)
    (hcontinuous : ∀ τ ∈ Ici (0 : ℝ),
      Continuous (fun x ↦ curl v x (clock τ)))
    (hgrowth : Tendsto
      (fun τ ↦ |curl v (axisPoint (center τ)) (clock τ) 2|)
      atTop atTop) :
    Tendsto (fun τ ↦ eLpNorm (fun x ↦ curl v x (clock τ))
      (⊤ : ℝ≥0∞) volume) atTop (𝓝 (⊤ : ℝ≥0∞)) := by
  apply tendsto_nhds_top_mono (ENNReal.tendsto_ofReal_atTop.comp hgrowth)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with τ hτ
  have hpoint := enorm_le_eLpNorm_top_of_continuous
    (hcontinuous τ hτ) (axisPoint (center τ))
  have hcomponent := PiLp.enorm_apply_le
    (curl v (axisPoint (center τ)) (clock τ)) (2 : Fin 3)
  simpa only [Function.comp_apply, ← Real.norm_eq_abs, ofReal_norm]
    using hcomponent.trans hpoint

/-- A diverging axial curl cannot agree with a continuous extension even
locally near the limiting spacetime point. A smooth continuation of the
velocity would supply such a continuous curl. -/
theorem not_exists_continuous_axis_curl_local_extension
    (v : VectorField) (clock center : ℝ → ℝ) (T zStar : ℝ)
    (hclock : Tendsto clock atTop (𝓝 T))
    (hcenter : Tendsto center atTop (𝓝 zStar))
    (hbefore : ∀ᶠ τ in atTop, clock τ < T)
    (hgrowth : Tendsto
      (fun τ ↦ |curl v (axisPoint (center τ)) (clock τ) 2|)
      atTop atTop) :
    ¬∃ extension : ℝ × ℝ → ℝ,
      (∀ᶠ p in 𝓝 (zStar, T),
        p.2 < T → extension p = curl v (axisPoint p.1) p.2 2) ∧
      ContinuousAt extension (zStar, T) := by
  rintro ⟨extension, hagree, hcontinuous⟩
  have hpath := hcenter.prodMk_nhds hclock
  have hlimit := hcontinuous.tendsto.comp hpath
  have hactual : Tendsto
      (fun τ ↦ curl v (axisPoint (center τ)) (clock τ) 2)
      atTop (𝓝 (extension (zStar, T))) := by
    apply hlimit.congr'
    filter_upwards [hpath.eventually hagree, hbefore] with τ hagreeτ hτ
    exact hagreeτ hτ
  exact not_tendsto_atTop_of_tendsto_nhds hactual.abs hgrowth

/-- In particular, no continuous extension can agree with the axial curl
throughout the preceding physical times. -/
theorem not_exists_continuous_axis_curl_extension
    (v : VectorField) (clock center : ℝ → ℝ) (T zStar : ℝ)
    (hclock : Tendsto clock atTop (𝓝 T))
    (hcenter : Tendsto center atTop (𝓝 zStar))
    (hbefore : ∀ᶠ τ in atTop, clock τ < T)
    (hgrowth : Tendsto
      (fun τ ↦ |curl v (axisPoint (center τ)) (clock τ) 2|)
      atTop atTop) :
    ¬∃ extension : ℝ × ℝ → ℝ,
      (∀ z t, t < T → extension (z, t) = curl v (axisPoint z) t 2) ∧
      ContinuousAt extension (zStar, T) := by
  rintro ⟨extension, hagree, hcontinuous⟩
  exact not_exists_continuous_axis_curl_local_extension
    v clock center T zStar hclock hcenter hbefore hgrowth
    ⟨extension, Eventually.of_forall (fun p hp ↦ hagree p.1 p.2 hp), hcontinuous⟩

end Euler
