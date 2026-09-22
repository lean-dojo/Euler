/-
Copyright (c) 2026 Robert Joseph George and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/

module

public import Euler.PhysicalTime.AxisCurl
public import Euler.Rescaling.Coordinates

/-!
# Returning to physical time in Appendix J

Here we formalize the estimates in Proposition S10. The scale laws and bounds
imply that physical time approaches a finite limit, the moving center converges,
and the axial curl grows without bound.

We use the inverse coordinate map from Appendix D and the Cartesian curl formula.
The theorem assumes the scale laws, normalization, and regularity; it does not
construct an Euler solution or check numerical bounds.
-/

@[expose] public section

noncomputable section

open Euler.Axisymmetric MeasureTheory Set Filter
open Euler.PhysicalTime
open scoped Topology ENNReal

namespace Euler

open Cartesian

/-- Inverse rescaling carries the normalized profile origin to the moving
physical center, equation (S552). -/
theorem physicalScalarPullback_at_center
    (data : Rescaling) (U : ℝ^2 → ℝ → ℝ)
    (sU inverseClock : ℝ → ℝ) (τ barU : ℝ)
    (hscale : data.spatialScale τ ≠ 0)
    (hclock : inverseClock (data.physicalTime τ) = τ)
    (hnormalize : U 0 τ = barU) :
    physicalScalarPullback data U sU inverseClock
      (rescalingMap data 0 τ) (data.physicalTime τ) =
      sU τ * barU := by
  simp only [physicalScalarPullback, hclock,
    inverseRescalingMap_rescalingMap data 0 τ hscale, hnormalize]

/-- The conclusions of Proposition S10 from the signed amplitude rate,
bounded center modulation, and normalization of the physical swirl.

Time is measured from the initial physical time. Adding that initial time
translates both the clock and lifetime by the same constant.
-/
theorem physical_reconstruction_estimates
    (a b w : ScalarField) (sU cU center C : ℝ → ℝ)
    (barU gamma sr₀ lam K : ℝ)
    (hgamma : 0 < gamma) (hsU0 : 0 < sU 0) (hbarU : barU ≠ 0)
    (hscale : ∀ τ ∈ Ici (0 : ℝ), HasDerivAt sU (-cU τ * sU τ) τ)
    (hrate : ∀ τ ∈ Ici (0 : ℝ), cU τ ≤ -gamma)
    (hsr : 0 ≤ sr₀) (hlam : 0 < lam)
    (hC : ContinuousOn C (Ici (0 : ℝ)))
    (hCbound : ∀ τ ∈ Ici (0 : ℝ), |C τ| ≤ K)
    (hcenter : ∀ τ ∈ Ici (0 : ℝ),
      HasDerivAt center (travelingCenterVelocity C sr₀ lam τ) τ)
    (ha : ∀ τ ∈ Ici (0 : ℝ),
      DifferentiableAt ℝ
        (fun x ↦ a x (∫ s in (0 : ℝ)..τ, (sU s)⁻¹)) (axisPoint (center τ)))
    (hb : ∀ τ ∈ Ici (0 : ℝ),
      DifferentiableAt ℝ
        (fun x ↦ b x (∫ s in (0 : ℝ)..τ, (sU s)⁻¹)) (axisPoint (center τ)))
    (hnormalize : ∀ τ ∈ Ici (0 : ℝ),
      b (axisPoint (center τ)) (∫ s in (0 : ℝ)..τ, (sU s)⁻¹) = sU τ * barU)
    (hcurl : ∀ τ ∈ Ici (0 : ℝ), Continuous
      (fun x ↦ curl (axisymmetricVelocity a b w)
        x (∫ s in (0 : ℝ)..τ, (sU s)⁻¹))) :
    let clock := fun τ ↦ ∫ s in (0 : ℝ)..τ, (sU s)⁻¹
    let T := ∫ s in Ioi (0 : ℝ), (sU s)⁻¹
    let zStar := center 0 + ∫ τ in Ioi (0 : ℝ), travelingCenterVelocity C sr₀ lam τ
    IntegrableOn (fun τ ↦ (sU τ)⁻¹) (Ioi (0 : ℝ)) ∧
      (∀ τ ∈ Ici (0 : ℝ),
        0 < T - clock τ ∧ T - clock τ ≤ (sU 0)⁻¹ * Real.exp (-gamma * τ) / gamma) ∧
      StrictMonoOn clock (Ici (0 : ℝ)) ∧
      clock '' Ici (0 : ℝ) = Ico 0 T ∧
      Tendsto clock atTop (𝓝 T) ∧
      Tendsto center atTop (𝓝 zStar) ∧
      Tendsto (fun τ ↦ |curl (axisymmetricVelocity a b w)
        (axisPoint (center τ)) (clock τ) 2|) atTop atTop ∧
      Tendsto (fun τ ↦ eLpNorm
        (fun x ↦ curl (axisymmetricVelocity a b w) x (clock τ))
        (⊤ : ℝ≥0∞) volume) atTop (𝓝 (⊤ : ℝ≥0∞)) ∧
      ¬∃ extension : ℝ × ℝ → ℝ,
        (∀ᶠ p in 𝓝 (zStar, T), p.2 < T →
          extension p = curl (axisymmetricVelocity a b w)
            (axisPoint p.1) p.2 2) ∧
        ContinuousAt extension (zStar, T) := by
  dsimp only
  have hint := integrableOn_reciprocal_amplitude sU cU gamma hsU0 hscale hrate hgamma
  have hclock := tendsto_physicalTimeIntegral_atTop _ hint
  have hlimit := tendsto_travelingCenter_atTop center C sr₀ lam K hsr hlam
    hC hCbound hcenter
  have hgrowth := tendsto_abs_axis_curl_atTop a b w
    (fun τ ↦ ∫ s in (0 : ℝ)..τ, (sU s)⁻¹) center sU cU barU gamma
    hgamma hsU0 hbarU hscale hrate ha hb hnormalize
  refine ⟨hint, ?_,
    (reciprocal_clock_continuous_strictMono sU cU gamma hsU0 hscale hrate).2,
    image_reciprocal_clock_Ici sU cU gamma hsU0 hscale hrate hgamma,
    hclock, hlimit, hgrowth,
    tendsto_eLpNorm_curl_of_axis_growth _ _ _ hcurl hgrowth, ?_⟩
  · intro τ hτ
    exact ⟨sub_pos.mpr (reciprocal_clock_lt_lifetime
      sU cU gamma hsU0 hscale hrate hgamma hτ),
      lifetime_sub_reciprocal_clock_le sU cU gamma hsU0 hscale hrate hgamma hτ⟩
  · apply not_exists_continuous_axis_curl_local_extension _ _ _ _ _ hclock hlimit
      _ hgrowth
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with τ hτ
    exact reciprocal_clock_lt_lifetime sU cU gamma hsU0 hscale hrate hgamma hτ

end Euler
