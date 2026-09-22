/-
Copyright (c) 2026 Robert Joseph George and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

/-!
# Staying below the energy bound

Here we formalize the argument in Appendix I, S542–S544. If the energy starts
below a bound and its derivative is negative whenever it reaches that bound,
then it stays below the bound.

We argue by contradiction: at the first time it reaches the bound, the slopes
from the left are nonnegative. Their limit cannot be a negative derivative.
The proof also works at the right endpoint of the given time interval.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace Euler.Stability

/-- If `f` starts below `R` and has a negative derivative whenever it reaches `R`,
then `f` stays below `R` throughout the interval. -/
theorem strict_sublevel_invariant
    {f : ℝ → ℝ} {a b R : ℝ}
    (hf : ContinuousOn f (Icc a b)) (ha : f a < R)
    (hboundary : ∀ t ∈ Ioc a b, f t = R →
      ∃ v < 0, HasDerivWithinAt f v (Icc a b) t) :
    ∀ t ∈ Icc a b, f t < R := by
  intro t ht
  by_contra hnot
  have hcont := hf.mono (Icc_subset_Icc_right ht.2)
  have hhit : (Icc a t ∩ f ⁻¹' {R}).Nonempty := by
    obtain ⟨s, hs, hsR⟩ := intermediate_value_Icc ht.1 hcont
      (show R ∈ Icc (f a) (f t) from ⟨ha.le, le_of_not_gt hnot⟩)
    exact ⟨s, hs, hsR⟩
  have hclosed : IsClosed (Icc a t ∩ f ⁻¹' {R}) :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  obtain ⟨τ, hτ, hleast⟩ :=
    (isCompact_Icc.of_isClosed_subset hclosed inter_subset_left).exists_isLeast hhit
  have hτR : f τ = R := hτ.2
  have haτ : a < τ := lt_of_le_of_ne hτ.1.1 (fun h ↦ ha.ne (h ▸ hτR))
  have hbefore : ∀ x ∈ Ico a τ, f x < R := by
    intro x hx
    by_contra hxR
    obtain ⟨y, hy, hyR⟩ := intermediate_value_Icc hx.1
      (hcont.mono (Icc_subset_Icc_right (hx.2.le.trans hτ.1.2)))
      (show R ∈ Icc (f a) (f x) from ⟨ha.le, le_of_not_gt hxR⟩)
    have hyhit : y ∈ Icc a t ∩ f ⁻¹' {R} :=
      ⟨⟨hy.1, hy.2.trans (hx.2.le.trans hτ.1.2)⟩, hyR⟩
    exact (not_lt_of_ge (hleast hyhit)) (hy.2.trans_lt hx.2)
  obtain ⟨v, hv, hd⟩ := hboundary τ ⟨haτ, hτ.1.2.trans ht.2⟩ hτR
  have hlimit : Tendsto (slope f τ) (𝓝[Ico a τ] τ) (𝓝 v) :=
    (hasDerivWithinAt_iff_tendsto_slope.mp hd).mono_left
      (nhdsWithin_mono _ fun x hx ↦
        ⟨⟨hx.1, hx.2.le.trans (hτ.1.2.trans ht.2)⟩, hx.2.ne⟩)
  have : NeBot (𝓝[Ico a τ] τ) := right_nhdsWithin_Ico_neBot haτ
  have hvnonneg : 0 ≤ v := by
    apply ge_of_tendsto hlimit
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [slope_def_field]
    exact div_nonneg_of_nonpos (by rw [hτR]; exact sub_nonpos.mpr (hbefore x hx).le)
      (sub_nonpos.mpr hx.2.le)
  exact hv.not_ge hvnonneg

/-- The same result stated using `deriv`, for use in the clock estimates.
In Lean, a negative value of `deriv` also implies differentiability at that point. -/
theorem strict_sublevel_invariant_of_deriv_neg_on_boundary
    {e : ℝ → ℝ} {a b R : ℝ}
    (he : ContinuousOn e (Icc a b)) (ha : e a < R)
    (hderiv : ∀ t ∈ Icc a b, e t = R → deriv e t < 0) :
    ∀ t ∈ Icc a b, e t < R := by
  apply Euler.Stability.strict_sublevel_invariant he ha
  intro t ht hboundary
  have hneg := hderiv t ⟨ht.1.le, ht.2⟩ hboundary
  exact ⟨_, hneg, (differentiableAt_of_deriv_ne_zero hneg.ne).hasDerivAt.hasDerivWithinAt⟩

end Euler.Stability
