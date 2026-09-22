/-
Copyright (c) 2026 Robert Joseph George and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/

module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Euler.Stability.Barrier
public import Euler.PhysicalTime.PhysicalClock

/-!
# Amplitude growth and the remaining physical time

Here we prove the scalar estimates used in Appendix J. If
`sU' = -cU * sU`, `sU(0) > 0`, and `cU ≤ -gamma` with `gamma > 0`,
then `sU` stays positive and grows at least exponentially.

Its reciprocal is therefore bounded by a decaying exponential. Integrating
that bound estimates how much physical time remains.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open Euler.Stability
open scoped Topology

namespace Euler.PhysicalTime

/-- Positive initial amplitude stays positive when the rate has a constant upper bound.
No continuity or integrability of `cU` is required. The weighted amplitude
`sU(t) * exp ((1 - gamma) * t)` has strictly positive derivative at each positive level,
so it cannot reach half its initial value. -/
theorem amplitude_scale_pos
    (sU cU : ℝ → ℝ) (gamma : ℝ) (hsU0 : 0 < sU 0)
    (hscale : ∀ x ∈ Ici (0 : ℝ), HasDerivAt sU (-cU x * sU x) x)
    (hrate : ∀ x ∈ Ici (0 : ℝ), cU x ≤ -gamma)
    {t : ℝ} (ht : 0 ≤ t) : 0 < sU t := by
  let e := fun x : ℝ ↦ -(sU x * Real.exp ((1 - gamma) * x))
  have he (x : ℝ) (hx : 0 ≤ x) : HasDerivAt e
      ((cU x + gamma - 1) * (sU x * Real.exp ((1 - gamma) * x))) x := by
    have hexp : HasDerivAt (fun y : ℝ ↦ Real.exp ((1 - gamma) * y))
        ((1 - gamma) * Real.exp ((1 - gamma) * x)) x := by
      simpa [mul_comm] using ((hasDerivAt_id x).const_mul (1 - gamma)).exp
    exact ((hscale x hx).mul hexp).neg.congr_deriv (by ring)
  have hcont : ContinuousOn e (Icc 0 t) :=
    fun x hx ↦ (he x hx.1).continuousAt.continuousWithinAt
  have hlevel : e 0 < -(sU 0 / 2) := by
    simp only [e, mul_zero, Real.exp_zero, mul_one]
    linarith only [hsU0]
  have hbarrier : ∀ x ∈ Icc 0 t, e x = -(sU 0 / 2) → deriv e x < 0 := by
    intro x hx hxlevel
    have hw : sU x * Real.exp ((1 - gamma) * x) = sU 0 / 2 := by
      dsimp only [e] at hxlevel
      linarith only [hxlevel]
    rw [(he x hx.1).deriv, hw]
    have hc : cU x + gamma - 1 < 0 := by
      have hxrate := hrate x hx.1
      linarith only [hxrate]
    exact mul_neg_of_neg_of_pos hc (half_pos hsU0)
  have hstrict := strict_sublevel_invariant_of_deriv_neg_on_boundary
    hcont hlevel hbarrier t ⟨ht, le_rfl⟩
  have hweighted : 0 < sU t * Real.exp ((1 - gamma) * t) := by
    dsimp only [e] at hstrict
    linarith only [hstrict, hsU0]
  exact (mul_pos_iff_of_pos_right (Real.exp_pos _)).mp hweighted

/-- A uniformly negative amplitude rate forces exponential growth of the
amplitude scale.  The proof applies monotonicity to
`sU(t) * exp (-gamma * t)`.
-/
theorem amplitude_scale_lower_bound
    (sU cU : ℝ → ℝ) (gamma t : ℝ)
    (ht : 0 ≤ t)
    (hscale : ∀ x ∈ Ici (0 : ℝ), HasDerivAt sU (-cU x * sU x) x)
    (hscaleNonneg : ∀ x ∈ Ici (0 : ℝ), 0 ≤ sU x)
    (hrate : ∀ x ∈ Ici (0 : ℝ), cU x ≤ -gamma) :
    sU 0 * Real.exp (gamma * t) ≤ sU t := by
  let weightedScale := fun x : ℝ ↦ sU x * Real.exp (-gamma * x)
  have hweightedDeriv (x : ℝ) (hx : x ∈ Ici (0 : ℝ)) :
      HasDerivAt weightedScale
        ((-cU x - gamma) * sU x * Real.exp (-gamma * x)) x := by
    exact ((hscale x hx).mul (((hasDerivAt_id x).const_mul (-gamma)).exp)).congr_deriv
      (by dsimp; ring)
  have hmono : MonotoneOn weightedScale (Ici (0 : ℝ)) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun x hx ↦ (hweightedDeriv x hx).continuousAt.continuousWithinAt)
      (fun x hx ↦ (hweightedDeriv x (interior_subset hx)).hasDerivWithinAt)
      (fun x hx ↦ mul_nonneg
        (mul_nonneg (by linarith [hrate x (interior_subset hx)])
          (hscaleNonneg x (interior_subset hx))) (Real.exp_pos _).le)
  have hbound := mul_le_mul_of_nonneg_right
    (hmono self_mem_Ici ht ht) (Real.exp_pos (gamma * t)).le
  simpa [weightedScale, mul_assoc, ← Real.exp_add] using hbound

/-- An integrable nonnegative clock rate bounded by `A exp (-gamma s)` has tail
at most `A exp (-gamma t) / gamma` when `gamma > 0`. Integrability is assumed;
the rate need not be the reciprocal of an amplitude scale.

This is the improper-integral estimate in Appendix J, equation (S551).
-/
theorem physical_clock_tail_le
    (reciprocalScale : ℝ → ℝ) (amplitude gamma t : ℝ)
    (hgamma : 0 < gamma)
    (hintegrable : IntegrableOn reciprocalScale (Ioi t))
    (hbound : ∀ s ∈ Ioi t,
      0 ≤ reciprocalScale s ∧
        reciprocalScale s ≤ amplitude * Real.exp (-gamma * s)) :
    (∫ s in Ioi t, reciprocalScale s) ≤
      amplitude * Real.exp (-gamma * t) / gamma := by
  have hexpIntegrable :
      IntegrableOn (fun s : ℝ ↦ amplitude * Real.exp (-gamma * s))
        (Ioi t) := by
    exact (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hgamma) t).const_mul _
  calc
    (∫ s in Ioi t, reciprocalScale s) ≤
        ∫ s in Ioi t, amplitude * Real.exp (-gamma * s) :=
      setIntegral_mono_on hintegrable hexpIntegrable measurableSet_Ioi
        (fun s hs ↦ (hbound s hs).2)
    _ = amplitude * (∫ s in Ioi t, Real.exp (-gamma * s)) := by
      rw [integral_const_mul]
    _ = amplitude * Real.exp (-gamma * t) / gamma := by
      rw [integral_exp_mul_Ioi (neg_lt_zero.mpr hgamma)]
      field_simp [hgamma.ne']

/-- A continuous positive integrable clock approaches its finite lifetime
from below. This is the one-sided limit needed to transfer a rescaled-time
blowup statement to physical time. The clock parametrizes exactly `[0, T*)`
and approaches its right endpoint without reaching it.
-/
theorem tendsto_physical_clock_atTop_nhdsWithin_Iio
    (reciprocalScale : ℝ → ℝ)
    (hcontinuous : Continuous reciprocalScale)
    (hpositive : ∀ t ∈ Ioi (0 : ℝ), 0 < reciprocalScale t)
    (hintegrable : IntegrableOn reciprocalScale (Ioi (0 : ℝ))) :
    Filter.Tendsto
      (fun t ↦ ∫ s in (0 : ℝ)..t, reciprocalScale s)
      Filter.atTop
      (𝓝[<] (∫ s in Ioi (0 : ℝ), reciprocalScale s)) := by
  refine tendsto_nhdsWithin_iff.mpr
    ⟨Euler.PhysicalTime.tendsto_physicalTimeIntegral_atTop reciprocalScale hintegrable, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
  have hmem : (∫ s in (0 : ℝ)..t, reciprocalScale s) ∈
      Ico 0 (∫ s in Ioi (0 : ℝ), reciprocalScale s) := by
    rw [← Euler.PhysicalTime.image_physicalTimeIntegral_Ici reciprocalScale hcontinuous
      hpositive hintegrable]
    exact ⟨t, ht, rfl⟩
  exact hmem.2

/-- Taking the absolute value of a normalized axial amplitude separates its
positive scale from the sign of the reference value. -/
theorem abs_axial_vorticity_at_center
    (omegaZ barU amplitude : ℝ) (hamplitude : 0 ≤ amplitude)
    (haxis : omegaZ = 2 * (amplitude * barU)) :
    |omegaZ| = 2 * |barU| * amplitude := by
  rw [haxis, abs_mul, abs_mul, abs_of_nonneg hamplitude]
  norm_num
  ring

/-- A negative amplitude rate and nonzero normalization force the scalar axis
value to diverge. The Cartesian curl application is in `AxisCurl.lean`. -/
theorem tendsto_abs_axial_vorticity_atTop
    (sU cU omegaZ : ℝ → ℝ) (barU gamma : ℝ)
    (hgamma : 0 < gamma) (hsU0 : 0 < sU 0) (hbarU : barU ≠ 0)
    (hscale : ∀ x ∈ Ici (0 : ℝ), HasDerivAt sU (-cU x * sU x) x)
    (hrate : ∀ x ∈ Ici (0 : ℝ), cU x ≤ -gamma)
    (haxis : ∀ t ∈ Ici (0 : ℝ), omegaZ t = 2 * (sU t * barU)) :
    Filter.Tendsto (fun t ↦ |omegaZ t|) Filter.atTop Filter.atTop := by
  have hscaleNonneg : ∀ x ∈ Ici (0 : ℝ), 0 ≤ sU x :=
    fun x hx ↦ (amplitude_scale_pos sU cU gamma hsU0 hscale hrate hx).le
  let lower := fun t : ℝ => (2 * |barU| * sU 0) * Real.exp (gamma * t)
  have hcoefficient : 0 < 2 * |barU| * sU 0 :=
    mul_pos (mul_pos (by norm_num) (abs_pos.mpr hbarU)) hsU0
  have hlower : Filter.Tendsto lower Filter.atTop Filter.atTop := by
    exact (Real.tendsto_exp_atTop.comp
      (Filter.tendsto_id.const_mul_atTop hgamma)).const_mul_atTop hcoefficient
  apply Filter.tendsto_atTop_mono' Filter.atTop _ hlower
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
  have hsU := amplitude_scale_lower_bound sU cU gamma t ht
    hscale hscaleNonneg hrate
  have haxisAbs := abs_axial_vorticity_at_center
    (omegaZ t) barU (sU t) (hscaleNonneg t ht) (haxis t ht)
  rw [haxisAbs]
  dsimp [lower]
  calc
    2 * |barU| * sU 0 * Real.exp (gamma * t) =
        2 * |barU| * (sU 0 * Real.exp (gamma * t)) := by ring
    _ ≤ 2 * |barU| * sU t :=
      mul_le_mul_of_nonneg_left hsU (mul_nonneg (by norm_num) (abs_nonneg barU))

end Euler.PhysicalTime
