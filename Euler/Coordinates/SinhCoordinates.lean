/-
Copyright (c) 2026 Robert Joseph George and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/

module

public import Euler.Calculus.AxisymmetricProfile
public import Euler.Calculus.ChainRule
public import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# The sinh coordinate change

The change of variables `R = sinh ρ`, `Z = sinh ζ` spreads a computational grid
over the meridian plane. Pulling a profile back along this map introduces `cosh`
factors in its first and second derivatives. The formulas below solve for the
physical derivatives and transfer the axisymmetric elliptic operator to the
computational coordinates.

The radial quotient needs a separate argument at the axis: for an even smooth
profile, its first radial derivative vanishes, and the quotient tends to the
second derivative. We prove that limit before identifying the regularized
operators.
-/

@[expose] public section

noncomputable section

open scoped Topology

open Euler.Calculus

namespace Euler.Coordinates

/-- The map `(ρ, ζ) ↦ (sinh ρ, sinh ζ)` from computational to profile coordinates. -/
def sinhCoordinates (x : (ℝ^2)) : (ℝ^2) :=
  EuclideanSpace.single 0 (Real.sinh (meridianR x)) +
    EuclideanSpace.single 1 (Real.sinh (meridianZ x))

/-- The radial component. -/
@[simp]
theorem sinhCoordinates_apply_zero (x : (ℝ^2)) :
    sinhCoordinates x 0 = Real.sinh (meridianR x) := by
  simp [sinhCoordinates]

/-- The axial component. -/
@[simp]
theorem sinhCoordinates_apply_one (x : (ℝ^2)) :
    sinhCoordinates x 1 = Real.sinh (meridianZ x) := by
  simp [sinhCoordinates]

/-- The physical radial coordinate after the computational coordinate map. -/
@[simp]
theorem meridianR_sinhCoordinates (x : (ℝ^2)) :
    meridianR (sinhCoordinates x) = Real.sinh (meridianR x) := by
  simp [meridianR]

/-- The physical axial coordinate after the computational coordinate map. -/
@[simp]
theorem meridianZ_sinhCoordinates (x : (ℝ^2)) :
    meridianZ (sinhCoordinates x) = Real.sinh (meridianZ x) := by
  simp [meridianZ]

/-- The hyperbolic computational coordinate map is smooth. -/
theorem contDiff_sinhCoordinates :
    ContDiff ℝ (⊤ : ℕ∞) sinhCoordinates := by
  apply (contDiff_piLp (2 : ENNReal)).2
  intro i
  fin_cases i
  · simpa [sinhCoordinates, meridianR] using
      (show ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ^2 ↦ Real.sinh (x 0)) by fun_prop)
  · simpa [sinhCoordinates, meridianZ] using
      (show ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ^2 ↦ Real.sinh (x 1)) by fun_prop)

/-- The coordinate identity: pull a physical profile back to computational coordinates. -/
def sinhPullback (f : (ℝ^2 → ℝ)) : (ℝ^2 → ℝ) :=
  fun x ↦ f (sinhCoordinates x)

/-- Computational pullback preserves every finite or infinite smoothness order. -/
theorem contDiff_sinhPullback {n : ℕ∞} {f : (ℝ^2 → ℝ)}
    (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (sinhPullback f) :=
  hf.comp (contDiff_sinhCoordinates.of_le (by simp))

-- Each coordinate changes independently, so the off-diagonal derivatives vanish.
private theorem partialDeriv_sinh_coord (i j : Fin 2) (x : ℝ^2) :
    partialDeriv i (fun y : ℝ^2 ↦ Real.sinh (y j)) x =
      if i = j then Real.cosh (x j) else 0 := by
  rw [partialDeriv_comp_real i Real.differentiableAt_sinh (by fun_prop)]
  simp [partialDeriv_coord, Real.deriv_sinh]

private theorem partialDeriv_cosh_coord (i j : Fin 2) (x : ℝ^2) :
    partialDeriv i (fun y : ℝ^2 ↦ Real.cosh (y j)) x =
      if i = j then Real.sinh (x j) else 0 := by
  rw [partialDeriv_comp_real i Real.differentiableAt_cosh (by fun_prop)]
  simp [partialDeriv_coord, Real.deriv_cosh]

private theorem partialDeriv_sinhPullback {f : ℝ^2 → ℝ}
    (hf : ContDiff ℝ 1 f) (i : Fin 2) (x : ℝ^2) :
    partialDeriv i (sinhPullback f) x =
      Real.cosh (x i) * partialDeriv i f (sinhCoordinates x) := by
  unfold sinhPullback
  rw [partialDeriv_comp i f sinhCoordinates x
    (hf.differentiable one_ne_zero).differentiableAt
    (contDiff_sinhCoordinates.differentiable (by simp)).differentiableAt]
  fin_cases i <;> simp [Fin.sum_univ_two, meridianR, meridianZ,
    partialDeriv_sinh_coord, mul_comm]

/-- The radial chain rule. -/
theorem profileDR_sinhPullback {f : (ℝ^2 → ℝ)}
    (hf : ContDiff ℝ 1 f) (x : (ℝ^2)) :
    profileDR (sinhPullback f) x =
      Real.cosh (meridianR x) * profileDR f (sinhCoordinates x) :=
  partialDeriv_sinhPullback hf 0 x

/-- The axial chain rule. -/
theorem profileDZ_sinhPullback {f : (ℝ^2 → ℝ)}
    (hf : ContDiff ℝ 1 f) (x : (ℝ^2)) :
    profileDZ (sinhPullback f) x =
      Real.cosh (meridianZ x) * profileDZ f (sinhCoordinates x) :=
  partialDeriv_sinhPullback hf 1 x

/-- The radial derivative solved for the physical derivative. -/
theorem profileDR_at_sinhCoordinates {f : (ℝ^2 → ℝ)}
    (hf : ContDiff ℝ 1 f) (x : (ℝ^2)) :
    profileDR f (sinhCoordinates x) =
      profileDR (sinhPullback f) x / Real.cosh (meridianR x) := by
  rw [profileDR_sinhPullback hf x]
  field_simp [(Real.cosh_pos _).ne']

/-- The axial derivative solved for the physical derivative. -/
theorem profileDZ_at_sinhCoordinates {f : (ℝ^2 → ℝ)}
    (hf : ContDiff ℝ 1 f) (x : (ℝ^2)) :
    profileDZ f (sinhCoordinates x) =
      profileDZ (sinhPullback f) x / Real.cosh (meridianZ x) := by
  rw [profileDZ_sinhPullback hf x]
  field_simp [(Real.cosh_pos _).ne']

-- Differentiating once more gives the same formula for either coordinate.
private theorem partialDeriv_partialDeriv_sinhPullback {f : ℝ^2 → ℝ}
    (hf : ContDiff ℝ 2 f) (i : Fin 2) (x : ℝ^2) :
    partialDeriv i (fun y ↦ partialDeriv i (sinhPullback f) y) x =
      Real.sinh (x i) * partialDeriv i f (sinhCoordinates x) +
        Real.cosh (x i) ^ 2 *
          partialDeriv i (fun y ↦ partialDeriv i f y) (sinhCoordinates x) := by
  have hpartial : ContDiff ℝ 1 (fun y ↦ partialDeriv i f y) :=
    contDiff_partialDeriv_of_succ hf
  have hcomp : DifferentiableAt ℝ (fun y ↦ partialDeriv i f (sinhCoordinates y)) x :=
    (hpartial.differentiable one_ne_zero).differentiableAt.comp x
      (contDiff_sinhCoordinates.differentiable (by simp)).differentiableAt
  simp_rw [partialDeriv_sinhPullback (hf.of_le (by norm_num))]
  rw [partialDeriv_mul (by fun_prop) hcomp,
    partialDeriv_cosh_coord, ite_eq_left rfl]
  change Real.sinh (x i) * partialDeriv i f (sinhCoordinates x) +
    Real.cosh (x i) * partialDeriv i (sinhPullback (fun y ↦ partialDeriv i f y)) x = _
  rw [partialDeriv_sinhPullback hpartial]
  ring

/-- The second radial chain rule:
`fρρ = sinh ρ fR + cosh² ρ fRR`. -/
theorem profileDRR_sinhPullback {f : (ℝ^2 → ℝ)}
    (hf : ContDiff ℝ 2 f) (x : (ℝ^2)) :
    profileDRR (sinhPullback f) x =
      Real.sinh (meridianR x) * profileDR f (sinhCoordinates x) +
        Real.cosh (meridianR x) ^ 2 *
          profileDRR f (sinhCoordinates x) :=
  partialDeriv_partialDeriv_sinhPullback hf 0 x

/-- The second axial chain rule:
`fζζ = sinh ζ fZ + cosh² ζ fZZ`. -/
theorem profileDZZ_sinhPullback {f : (ℝ^2 → ℝ)}
    (hf : ContDiff ℝ 2 f) (x : (ℝ^2)) :
    profileDZZ (sinhPullback f) x =
      Real.sinh (meridianZ x) * profileDZ f (sinhCoordinates x) +
        Real.cosh (meridianZ x) ^ 2 *
          profileDZZ f (sinhCoordinates x) :=
  partialDeriv_partialDeriv_sinhPullback hf 1 x

/-- The second radial derivative solved for the physical derivative. -/
theorem profileDRR_at_sinhCoordinates {f : (ℝ^2 → ℝ)}
    (hf : ContDiff ℝ 2 f) (x : (ℝ^2)) :
    profileDRR f (sinhCoordinates x) =
      profileDRR (sinhPullback f) x / Real.cosh (meridianR x) ^ 2 -
        Real.sinh (meridianR x) / Real.cosh (meridianR x) ^ 3 *
          profileDR (sinhPullback f) x := by
  have hfirst := profileDR_sinhPullback (hf.of_le (by norm_num)) x
  have hsecond := profileDRR_sinhPullback hf x
  have hcosh : Real.cosh (meridianR x) ≠ 0 := (Real.cosh_pos _).ne'
  rw [hsecond, hfirst]
  field_simp [hcosh]
  ring

/-- The second axial derivative solved for the physical derivative. -/
theorem profileDZZ_at_sinhCoordinates {f : (ℝ^2 → ℝ)}
    (hf : ContDiff ℝ 2 f) (x : (ℝ^2)) :
    profileDZZ f (sinhCoordinates x) =
      profileDZZ (sinhPullback f) x / Real.cosh (meridianZ x) ^ 2 -
        Real.sinh (meridianZ x) / Real.cosh (meridianZ x) ^ 3 *
          profileDZ (sinhPullback f) x := by
  have hfirst := profileDZ_sinhPullback (hf.of_le (by norm_num)) x
  have hsecond := profileDZZ_sinhPullback hf x
  have hcosh : Real.cosh (meridianZ x) ≠ 0 := (Real.cosh_pos _).ne'
  rw [hsecond, hfirst]
  field_simp [hcosh]
  ring

/-- The computational version of `(∂R f)/R`, with its removable axis value selected. -/
def computationalDROverR (f : (ℝ^2 → ℝ)) : (ℝ^2 → ℝ) :=
  fun x ↦
    if meridianR x = 0 then profileDRR f x
    else profileDR f x /
      (Real.sinh (meridianR x) * Real.cosh (meridianR x))

/-- The transformed classical derivative package in `(ρ, ζ)` coordinates. -/
def computationalAxisymmetricDifferential : AxisymmetricDifferential where
  DR := fun f x ↦ profileDR f x / Real.cosh (meridianR x)
  DZ := fun f x ↦ profileDZ f x / Real.cosh (meridianZ x)
  DRR := fun f x ↦
    profileDRR f x / Real.cosh (meridianR x) ^ 2 -
      Real.sinh (meridianR x) / Real.cosh (meridianR x) ^ 3 * profileDR f x
  DZZ := fun f x ↦
    profileDZZ f x / Real.cosh (meridianZ x) ^ 2 -
      Real.sinh (meridianZ x) / Real.cosh (meridianZ x) ^ 3 * profileDZ f x
  dROverR := computationalDROverR

/-- The elliptic operator in computational coordinates, equation (S327). -/
def computationalElliptic (f : (ℝ^2 → ℝ)) : (ℝ^2 → ℝ) :=
  axisymmetricLaplacian computationalAxisymmetricDifferential f

/-- Off the axis, `computationalElliptic` is exactly the displayed expression. -/
theorem computationalElliptic_of_ne_zero (f : (ℝ^2 → ℝ)) (x : (ℝ^2)) (hx : meridianR x ≠ 0) :
    computationalElliptic f x =
      profileDRR f x / Real.cosh (meridianR x) ^ 2 -
        Real.sinh (meridianR x) / Real.cosh (meridianR x) ^ 3 * profileDR f x +
        3 * profileDR f x /
          (Real.sinh (meridianR x) * Real.cosh (meridianR x)) +
        profileDZZ f x / Real.cosh (meridianZ x) ^ 2 -
        Real.sinh (meridianZ x) / Real.cosh (meridianZ x) ^ 3 * profileDZ f x := by
  simp [computationalElliptic, axisymmetricLaplacian, computationalAxisymmetricDifferential,
    computationalDROverR, hx]
  ring

/-- On the symmetry axis, the regularized radial part is `4 fρρ`. -/
theorem computationalElliptic_of_eq_zero (f : (ℝ^2 → ℝ)) (x : (ℝ^2)) (hx : meridianR x = 0) :
    computationalElliptic f x =
      4 * profileDRR f x +
        profileDZZ f x / Real.cosh (meridianZ x) ^ 2 -
        Real.sinh (meridianZ x) / Real.cosh (meridianZ x) ^ 3 * profileDZ f x := by
  simp [computationalElliptic, axisymmetricLaplacian, computationalAxisymmetricDifferential,
    computationalDROverR, hx]
  ring

/-- An even differentiable real function has zero derivative at the symmetry axis. -/
theorem deriv_eq_zero_of_even {f : ℝ → ℝ}
    (heven : Function.Even f) (hf : DifferentiableAt ℝ f 0) :
    deriv f 0 = 0 := by
  have hneg : HasDerivAt f (-deriv f 0) 0 := by
    simpa [Function.comp_def, heven.eq] using
      hf.hasDerivAt.comp_of_eq 0 (hasDerivAt_neg (𝕜 := ℝ) 0) (neg_zero.symm)
  linarith [hf.hasDerivAt.unique hneg]

/--
The removable singularity in the radial quotient.

If `g(0) = 0` and `g` is differentiable at zero with derivative `a`, then
`g(ρ)/(sinh ρ cosh ρ) → a`. Applied to `g = fρ`, radial evenness supplies
`g(0) = 0` and differentiability of the first derivative supplies `a = fρρ(0)`.
-/
theorem tendsto_div_sinh_mul_cosh {g : ℝ → ℝ} {a : ℝ}
    (hg0 : g 0 = 0) (hg : HasDerivAt g a 0) :
    Filter.Tendsto (fun ρ ↦ g ρ / (Real.sinh ρ * Real.cosh ρ))
      (𝓝[≠] 0) (𝓝 a) := by
  have hden : HasDerivAt (fun ρ ↦ Real.sinh ρ * Real.cosh ρ) 1 0 := by
    simpa using (Real.hasDerivAt_sinh 0).fun_mul (Real.hasDerivAt_cosh 0)
  have hratio := hg.tendsto_slope_zero.div hden.tendsto_slope_zero one_ne_zero
  simp only [div_one] at hratio
  apply hratio.congr'
  filter_upwards [self_mem_nhdsWithin] with ρ hρ
  simpa [hg0, smul_eq_mul] using
    mul_div_mul_left (g ρ) (Real.sinh ρ * Real.cosh ρ) (inv_ne_zero hρ)

/-- The removable radial quotient for the derivative of an even profile. -/
theorem tendsto_deriv_div_sinh_mul_cosh_of_even {f : ℝ → ℝ} {a : ℝ}
    (heven : Function.Even f) (hf : DifferentiableAt ℝ f 0)
    (hsecond : HasDerivAt (deriv f) a 0) :
    Filter.Tendsto (fun ρ ↦ deriv f ρ / (Real.sinh ρ * Real.cosh ρ))
      (𝓝[≠] 0) (𝓝 a) :=
  tendsto_div_sinh_mul_cosh (deriv_eq_zero_of_even heven hf) hsecond

/-- The regularized transformed quotient agrees with the physical one after pullback. -/
theorem computationalDROverR_sinhPullback {f : (ℝ^2 → ℝ)}
    (hf : ContDiff ℝ 2 f) (x : (ℝ^2)) :
    computationalDROverR (sinhPullback f) x =
      classicalAxisymmetricDifferential.dROverR f
        (sinhCoordinates x) := by
  by_cases hx : meridianR x = 0
  · rw [regularizedProfileDROverR_of_eq_zero f (sinhCoordinates x) (by simp [hx])]
    simp only [computationalDROverR, hx, ite_eq_left]
    simpa [hx, classicalAxisymmetricDifferential] using
      profileDRR_sinhPullback hf x
  · rw [regularizedProfileDROverR_of_ne_zero f (sinhCoordinates x)
      (by simpa using (Real.sinh_ne_zero.mpr hx))]
    simp only [computationalDROverR, hx, ite_false]
    rw [profileDR_sinhPullback (hf.of_le (by norm_num)) x]
    simp only [meridianR_sinhCoordinates]
    field_simp [(Real.sinh_ne_zero.mpr hx), (Real.cosh_pos _).ne']
    simp [classicalAxisymmetricDifferential]

/-- `computationalElliptic` is the physical axisymmetric elliptic operator after pullback. -/
theorem computationalElliptic_sinhPullback {f : (ℝ^2 → ℝ)}
    (hf : ContDiff ℝ 2 f) (x : (ℝ^2)) :
    computationalElliptic (sinhPullback f) x =
      axisymmetricLaplacian classicalAxisymmetricDifferential f
        (sinhCoordinates x) := by
  unfold computationalElliptic axisymmetricLaplacian
  dsimp only [computationalAxisymmetricDifferential]
  rw [← profileDRR_at_sinhCoordinates hf x]
  rw [← profileDZZ_at_sinhCoordinates hf x]
  rw [computationalDROverR_sinhPullback hf x]
  rfl

end Euler.Coordinates
