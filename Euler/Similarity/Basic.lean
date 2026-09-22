/-
Copyright (c) 2026 Robert Joseph George and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/

module

public import Euler.Calculus.Euclidean
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Ring

/-!
# Moving similarity ansatz

These are the ansatz S13–S15 and the moving coordinates of Appendix A, S266. The
amplitude parameter `alpha` is the negative of the exponent printed there:
`similarityScalar profile alpha` multiplies by `(T - t) ^ (-alpha)`.
The time and spatial chain rules are proved in `Euler.Similarity.Coordinates`.
-/

@[expose] public section

noncomputable section

namespace Euler.Similarity

/-- Backward power about a candidate singular time. Analytic statements about
this scale are restricted to times strictly before `singularTime`. -/
def backwardPowerScale (alpha singularTime t : ℝ) : ℝ :=
  (singularTime - t) ^ (-alpha)

/-- Positivity of a backward scale before its singular time. -/
theorem backwardPowerScale_pos {alpha singularTime t : ℝ}
    (ht : t < singularTime) : 0 < backwardPowerScale alpha singularTime t := by
  exact Real.rpow_pos_of_pos (sub_pos.mpr ht) _

/-- Multiplication adds backward-power exponents. -/
theorem backwardPowerScale_mul {alpha beta singularTime t : ℝ}
    (ht : t < singularTime) :
    backwardPowerScale alpha singularTime t * backwardPowerScale beta singularTime t =
      backwardPowerScale (alpha + beta) singularTime t := by
  unfold backwardPowerScale
  rw [← Real.rpow_add (sub_pos.mpr ht)]
  congr 1
  ring

/-- The time derivative of `(T-t)^(-alpha)`, obtained from the real-power rule. -/
theorem hasDerivAt_backwardPowerScale {alpha singularTime t : ℝ}
    (ht : t < singularTime) :
    HasDerivAt (backwardPowerScale alpha singularTime)
      (alpha * backwardPowerScale (alpha + 1) singularTime t) t := by
  have h := ((hasDerivAt_const t singularTime).sub (hasDerivAt_id t)).rpow_const
    (p := -alpha) (Or.inl (ne_of_gt (sub_pos.mpr ht)))
  apply h.congr_deriv
  dsimp only [Pi.sub_apply, id_eq, backwardPowerScale]
  rw [show -alpha - 1 = -(alpha + 1) by ring]
  ring

/-- Matching powers in the transport, forcing, and elliptic equations gives
S21 and S281–S295. This assumes termwise matching; individual terms of an
arbitrary solution could vanish or cancel. -/
theorem exponent_matching_iff (lam cu cΩ cΨ : ℝ) :
    (cu - 1 = cu + cΨ - lam ∧ cΩ - 1 = 2 * cu - lam ∧ cΩ = cΨ - 2 * lam) ↔
      (cu = -1 ∧ cΩ = -(1 + lam) ∧ cΨ = lam - 1) := by
  grind

end Euler.Similarity

namespace Euler

open Euler.Similarity

/-- The moving meridian coordinates `R = r/(T-t)^λ`, `Z = (z-zc(t))/(T-t)^λ`. -/
def similarityCoordinates (lam singularTime : ℝ) (axialCenter : ℝ → ℝ)
    (x : ℝ^2) (t : ℝ) : ℝ^2 :=
  backwardPowerScale lam singularTime t •
    (x - axialCenter t • EuclideanSpace.single 1 1)

/-- A stationary scalar profile expressed in moving physical coordinates. -/
def similarityScalar (profile : ℝ^2 → ℝ) (alpha lam singularTime : ℝ)
    (axialCenter : ℝ → ℝ) (x : ℝ^2) (t : ℝ) : ℝ :=
  backwardPowerScale alpha singularTime t *
    profile (similarityCoordinates lam singularTime axialCenter x t)

end Euler
