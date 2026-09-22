/-
Copyright (c) 2026 Robert Joseph George and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/

module

public import Euler.Similarity.Basic
public import Euler.Rescaling.Affine
public import Euler.Calculus.AxisymmetricProfile
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Derivatives in similarity coordinates

Here we prove the chain rules used in Appendices A and C. The center moves by
`zc' = -C (T-t)^(λ-1)`, which gives the coordinate derivatives S268 and S337.
Differentiating a profile in these coordinates gives S269, S276, S284, and
S291–S293.
-/

@[expose] public section

open Euler.Calculus Euler.Coordinates

noncomputable section

namespace Euler

open Euler.Similarity

/-- The centered similarity map is an affine dilation. -/
theorem similarityCoordinates_eq_affineDilation
    (lam singularTime : ℝ) (axialCenter : ℝ → ℝ)
    (x : (ℝ^2)) (t : ℝ) :
    similarityCoordinates lam singularTime axialCenter x t =
      affineDilation
        (backwardPowerScale lam singularTime t)
        ((-backwardPowerScale lam singularTime t) •
          (axialCenter t • (EuclideanSpace.single 1 1))) x := by
  ext i
  fin_cases i <;>
    simp [similarityCoordinates,
      affineDilation, smul_eq_mul]
  ring

/-- Radial similarity coordinate, equation S266. -/
@[simp]
theorem similarityCoordinates_radial
    (lam singularTime : ℝ) (axialCenter : ℝ → ℝ)
    (x : (ℝ^2)) (t : ℝ) :
    meridianR (similarityCoordinates lam singularTime axialCenter x t) =
      backwardPowerScale lam singularTime t * meridianR x :=
  by simp [similarityCoordinates, meridianR, PiLp.sub_apply, smul_eq_mul]

/-- Axial similarity coordinate, equation S266. -/
@[simp]
theorem similarityCoordinates_axial
    (lam singularTime : ℝ) (axialCenter : ℝ → ℝ)
    (x : (ℝ^2)) (t : ℝ) :
    meridianZ (similarityCoordinates lam singularTime axialCenter x t) =
      backwardPowerScale lam singularTime t *
        (meridianZ x - axialCenter t) :=
  by simp [similarityCoordinates, meridianZ, PiLp.sub_apply, smul_eq_mul]

/-- Time derivative of the radial similarity coordinate, equation S268. -/
theorem hasDerivAt_similarityCoordinates_radial
    {lam singularTime t : ℝ} (axialCenter : ℝ → ℝ)
    (x : (ℝ^2)) (ht : t < singularTime) :
    HasDerivAt
      (fun s ↦ meridianR (similarityCoordinates lam singularTime axialCenter x s))
      (lam * backwardPowerScale (lam + 1) singularTime t * meridianR x) t := by
  simpa only [similarityCoordinates_radial] using
    (hasDerivAt_backwardPowerScale (alpha := lam) ht).mul_const (meridianR x)

/-- Time derivative of the axial similarity coordinate, equation S268. -/
theorem hasDerivAt_similarityCoordinates_axial
    {lam axialDrift singularTime t : ℝ} {axialCenter : ℝ → ℝ}
    (x : (ℝ^2))
    (hcenter : HasDerivAt axialCenter
      (-axialDrift * backwardPowerScale (1 - lam) singularTime t) t)
    (ht : t < singularTime) :
    HasDerivAt
      (fun s ↦ meridianZ (similarityCoordinates lam singularTime axialCenter x s))
      (lam * backwardPowerScale (lam + 1) singularTime t *
          (meridianZ x - axialCenter t)
        + axialDrift * backwardPowerScale 1 singularTime t) t := by
  rw [show
    (fun s ↦ meridianZ (similarityCoordinates lam singularTime axialCenter x s)) =
      fun s ↦ backwardPowerScale lam singularTime s * (meridianZ x - axialCenter s) by
    funext s
    simp]
  have hproduct :=
    (hasDerivAt_backwardPowerScale (alpha := lam) ht).mul
      ((hasDerivAt_const t (meridianZ x)).sub hcenter)
  apply hproduct.congr_deriv
  have hscale :
      backwardPowerScale lam singularTime t *
          backwardPowerScale (1 - lam) singularTime t =
        backwardPowerScale 1 singularTime t := by
    rw [backwardPowerScale_mul ht]
    congr 1
    ring
  simp only [Pi.sub_apply, zero_sub]
  calc
    _ = lam * backwardPowerScale (lam + 1) singularTime t *
          (meridianZ x - axialCenter t) + axialDrift *
          (backwardPowerScale lam singularTime t *
            backwardPowerScale (1 - lam) singularTime t) := by ring
    _ = _ := by rw [hscale]

/-- Complete coordinate-path derivative, equations S268 and S337. -/
theorem hasDerivAt_similarityCoordinates
    {lam axialDrift singularTime t : ℝ} {axialCenter : ℝ → ℝ}
    (x : (ℝ^2))
    (hcenter : HasDerivAt axialCenter
      (-axialDrift * backwardPowerScale (1 - lam) singularTime t) t)
    (ht : t < singularTime) :
    HasDerivAt
      (fun s ↦ similarityCoordinates lam singularTime axialCenter x s)
      (backwardPowerScale 1 singularTime t •
        (lam • similarityCoordinates lam singularTime axialCenter x t +
          axialDrift • (EuclideanSpace.single 1 1))) t := by
  have hscale :
      backwardPowerScale 1 singularTime t * backwardPowerScale lam singularTime t =
        backwardPowerScale (lam + 1) singularTime t := by
    rw [backwardPowerScale_mul ht]
    congr 1
    ring
  let coordinates := EuclideanSpace.equiv (Fin 2) ℝ
  have hcoordinates :
      HasDerivAt
        (fun s ↦ coordinates (similarityCoordinates lam singularTime axialCenter x s))
        (coordinates (backwardPowerScale 1 singularTime t •
          (lam • similarityCoordinates lam singularTime axialCenter x t +
            axialDrift • (EuclideanSpace.single 1 1)))) t := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · have hrad := hasDerivAt_similarityCoordinates_radial (lam := lam) axialCenter x ht
      have hrad' : HasDerivAt
          (fun s ↦ meridianR (similarityCoordinates lam singularTime axialCenter x s))
          (backwardPowerScale 1 singularTime t * lam *
            meridianR (similarityCoordinates lam singularTime axialCenter x t)) t := by
        apply hrad.congr_deriv
        rw [similarityCoordinates_radial, ← hscale]
        ring
      simpa [coordinates, meridianR, PiLp.add_apply, smul_eq_mul, mul_assoc] using hrad'
    · have haxial := hasDerivAt_similarityCoordinates_axial x hcenter ht
      have haxial' : HasDerivAt
          (fun s ↦ meridianZ (similarityCoordinates lam singularTime axialCenter x s))
          (backwardPowerScale 1 singularTime t *
            (lam * meridianZ (similarityCoordinates lam singularTime axialCenter x t) +
              axialDrift)) t := by
        apply haxial.congr_deriv
        rw [similarityCoordinates_axial, ← hscale]
        ring
      simpa [coordinates, meridianZ, PiLp.add_apply, smul_eq_mul, mul_add, mul_assoc]
        using haxial'
  exact coordinates.symm.hasFDerivAt.comp_hasDerivAt t hcoordinates

/-! ## Scalar chain rules -/

/-- One spatial derivative contributes one factor `(T-t)^(-lambda)`,
equation S269. -/
theorem partialDeriv_similarityScalar
    (profile : (ℝ^2 → ℝ)) (alpha lam singularTime : ℝ)
    (axialCenter : ℝ → ℝ) (i : Fin 2) (x : (ℝ^2)) {t : ℝ}
    (hprofile : DifferentiableAt ℝ profile
      (similarityCoordinates lam singularTime axialCenter x t))
    (ht : t < singularTime) :
    partialDeriv i
        (fun y ↦ similarityScalar profile alpha lam singularTime axialCenter y t) x =
      backwardPowerScale (alpha + lam) singularTime t *
        partialDeriv i profile
          (similarityCoordinates lam singularTime axialCenter x t) := by
  -- The general affine chain rule already handles the translation by the moving center.
  simp only [similarityScalar, similarityCoordinates_eq_affineDilation] at hprofile ⊢
  rw [partialDeriv_const_mul_comp_affineDilation i profile _ _ _ x hprofile,
    backwardPowerScale_mul ht]

/-- Time differentiation produces the moving similarity generator,
equations S276 and S284. -/
theorem hasDerivAt_similarityScalar
    (profile : (ℝ^2 → ℝ)) (alpha lam axialDrift singularTime : ℝ)
    (axialCenter : ℝ → ℝ) (x : (ℝ^2)) {t : ℝ}
    (hprofile : DifferentiableAt ℝ profile
      (similarityCoordinates lam singularTime axialCenter x t))
    (hcenter : HasDerivAt axialCenter
      (-axialDrift * backwardPowerScale (1 - lam) singularTime t) t)
    (ht : t < singularTime) :
    HasDerivAt
      (fun s ↦ similarityScalar profile alpha lam singularTime axialCenter x s)
      (backwardPowerScale (alpha + 1) singularTime t *
        (alpha * profile
            (similarityCoordinates lam singularTime axialCenter x t)
          + lam * meridianR
              (similarityCoordinates lam singularTime axialCenter x t) *
              profileDR profile
                (similarityCoordinates lam singularTime axialCenter x t)
          + (axialDrift + lam * meridianZ
              (similarityCoordinates lam singularTime axialCenter x t)) *
              profileDZ profile
                (similarityCoordinates lam singularTime axialCenter x t))) t := by
  have hcomp := hprofile.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_similarityCoordinates x hcenter ht)
  have hproduct :=
    (hasDerivAt_backwardPowerScale (alpha := alpha) ht).mul hcomp
  apply hproduct.congr_deriv
  rw [fderiv_apply_eq_sum_partialDeriv_mul]
  simp only [Function.comp_apply, Fin.sum_univ_two, PiLp.smul_apply,
    PiLp.add_apply, PiLp.single_apply, Fin.zero_ne_one, ↓reduceIte,
    smul_eq_mul, mul_zero, mul_one, add_zero]
  -- Factor out the common amplitude-time scale from the product and chain rules.
  simp_rw [← backwardPowerScale_mul ht]
  simp only [profileDR, profileDZ, meridianR, meridianZ]
  ring

/-- Two spatial derivatives contribute two spatial-scale factors,
equations S291--S293. -/
theorem partialDeriv_partialDeriv_similarityScalar
    (profile : (ℝ^2 → ℝ)) (alpha lam singularTime : ℝ)
    (axialCenter : ℝ → ℝ) (i j : Fin 2) (x : (ℝ^2)) {t : ℝ}
    (hprofile : ContDiff ℝ 2 profile)
    (ht : t < singularTime) :
    partialDeriv i
        (fun y ↦
          partialDeriv j
            (fun z ↦
              similarityScalar profile alpha lam singularTime axialCenter z t) y) x =
      backwardPowerScale (alpha + 2 * lam) singularTime t *
        partialDeriv i (fun y ↦ partialDeriv j profile y)
          (similarityCoordinates lam singularTime axialCenter x t) := by
  simp only [similarityScalar, similarityCoordinates_eq_affineDilation]
  rw [partialDeriv_partialDeriv_const_mul_comp_affineDilation
    i j profile _ _ _ x hprofile, pow_two, backwardPowerScale_mul ht,
    backwardPowerScale_mul ht]
  congr 1
  ring_nf

end Euler
