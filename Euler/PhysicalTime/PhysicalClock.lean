/-
Copyright (c) 2026 Robert Joseph George and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/

module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Positive clocks and finite lifetime

A clock with positive derivative is strictly increasing on its time interval.
If a continuous clock on the nonnegative half-line has a finite limit, its image
is the interval from its initial value up to, but excluding, that limit.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Euler.PhysicalTime

/-- A physical-time clock with a positive rate is strictly increasing on any
convex rescaled-time domain where its differential law holds.

Consequently the clock is injective there and
`StrictMonoOn.orderIso` supplies an order isomorphism from `rescaledTimes` to
its physical-time image. This isolates the inverse-clock argument from any
particular similarity ansatz or numerical estimate. -/
theorem strictMonoOn_physicalTime_of_hasDerivAt_pos
    (physicalTime clockRate : ℝ → ℝ) (rescaledTimes : Set ℝ)
    (hconvex : Convex ℝ rescaledTimes)
    (hclock : ∀ τ ∈ rescaledTimes,
      HasDerivAt physicalTime (clockRate τ) τ)
    (hclockRate : ∀ τ ∈ interior rescaledTimes, 0 < clockRate τ) :
    StrictMonoOn physicalTime rescaledTimes := by
  apply strictMonoOn_of_deriv_pos hconvex
  · intro τ hτ
    exact (hclock τ hτ).continuousAt.continuousWithinAt
  · intro τ hτ
    rw [(hclock τ (interior_subset hτ)).deriv]
    exact hclockRate τ hτ

/-- A continuous strictly increasing clock on a forward half-line whose
values converge to a finite lifetime parametrizes exactly the half-open
interval from its initial value to that lifetime.

In particular, the limiting lifetime is never attained at a finite rescaled
time. This is the order-topological step needed when a global rescaled
trajectory is reconstructed on a finite physical-time interval. -/
theorem image_Ici_eq_Ico_of_strictMonoOn_tendsto
    (physicalTime : ℝ → ℝ) (initialTime lifetime : ℝ)
    (hcontinuous : ContinuousOn physicalTime (Set.Ici initialTime))
    (hmono : StrictMonoOn physicalTime (Set.Ici initialTime))
    (hlifetime : Filter.Tendsto physicalTime Filter.atTop (nhds lifetime)) :
    physicalTime '' Set.Ici initialTime =
      Set.Ico (physicalTime initialTime) lifetime := by
  refine Subset.antisymm ?_ (isPreconnected_Ici.intermediate_value_Ico
    self_mem_Ici (le_principal_iff.mpr (eventually_ge_atTop initialTime)) hcontinuous hlifetime)
  rintro _ ⟨time, htime, rfl⟩
  refine ⟨hmono.monotoneOn self_mem_Ici htime htime, ?_⟩
  -- Every clock value is below a later value, which is at most the limit.
  have hnext : time + 1 ∈ Ici initialTime := htime.trans (show time ≤ time + 1 by linarith)
  have hstrict : physicalTime time < physicalTime (time + 1) :=
    hmono htime hnext (by linarith)
  refine hstrict.trans_le (ge_of_tendsto hlifetime ?_)
  filter_upwards [eventually_ge_atTop (time + 1)] with later hlater
  exact hmono.monotoneOn hnext (hnext.trans hlater) hlater

/-- The accumulated clock of an integrable rate on the positive half-line
converges to the total clock mass. -/
theorem tendsto_physicalTimeIntegral_atTop
    (clockRate : ℝ → ℝ)
    (hintegrable : MeasureTheory.IntegrableOn clockRate (Set.Ioi (0 : ℝ))) :
    Filter.Tendsto
      (fun time ↦ ∫ s in (0 : ℝ)..time, clockRate s)
      Filter.atTop
      (nhds (∫ s in Set.Ioi (0 : ℝ), clockRate s)) := by
  exact intervalIntegral_tendsto_integral_Ioi 0 hintegrable tendsto_id

/-- The accumulated clock of a continuous rate that is positive after the initial
time is strictly increasing on the closed half-line `[0, ∞)`. -/
theorem strictMonoOn_physicalTimeIntegral
    (clockRate : ℝ → ℝ)
    (hcontinuous : Continuous clockRate)
    (hpositive : ∀ time ∈ Set.Ioi (0 : ℝ), 0 < clockRate time) :
    StrictMonoOn (fun time ↦ ∫ s in (0 : ℝ)..time, clockRate s) (Set.Ici (0 : ℝ)) := by
  apply strictMonoOn_physicalTime_of_hasDerivAt_pos
    (fun time ↦ ∫ s in (0 : ℝ)..time, clockRate s) clockRate (Set.Ici (0 : ℝ)) (convex_Ici 0)
  · intro time _htime
    exact intervalIntegral.integral_hasDerivAt_right
      (hcontinuous.intervalIntegrable _ _)
      hcontinuous.aestronglyMeasurable.stronglyMeasurableAtFilter
      hcontinuous.continuousAt
  · simpa only [interior_Ici] using hpositive

/-- A continuous positive integrable clock rate parametrizes exactly the
half-open physical-time interval before its total lifetime. -/
theorem image_physicalTimeIntegral_Ici
    (clockRate : ℝ → ℝ)
    (hcontinuous : Continuous clockRate)
    (hpositive : ∀ time ∈ Set.Ioi (0 : ℝ), 0 < clockRate time)
    (hintegrable : MeasureTheory.IntegrableOn clockRate (Set.Ioi (0 : ℝ))) :
    (fun time ↦ ∫ s in (0 : ℝ)..time, clockRate s) '' Set.Ici (0 : ℝ) =
      Set.Ico 0 (∫ s in Set.Ioi (0 : ℝ), clockRate s) := by
  let physicalTime := fun time : ℝ ↦
    ∫ s in (0 : ℝ)..time, clockRate s
  have hmono : StrictMonoOn physicalTime (Set.Ici (0 : ℝ)) :=
    strictMonoOn_physicalTimeIntegral clockRate hcontinuous hpositive
  have himage := image_Ici_eq_Ico_of_strictMonoOn_tendsto
    physicalTime 0 (∫ s in Set.Ioi (0 : ℝ), clockRate s)
    ((intervalIntegral.differentiable_integral_of_continuous hcontinuous).continuous.continuousOn)
    hmono (tendsto_physicalTimeIntegral_atTop clockRate hintegrable)
  simpa [physicalTime] using himage

end Euler.PhysicalTime
