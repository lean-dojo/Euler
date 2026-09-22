/-
Copyright (c) 2026 Robert Joseph George and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/

module

public import Euler.EnergyScaling.Measure
public import Euler.Similarity.Coordinates
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Weighted energy of the self-similar fields

Appendix E, S369–S385: the measure `r³ dr dz` contributes `(T-t)^(5λ)`;
both the reduced velocity and the streamfunction gradient contribute
`(T-t)^(-1)`. Consequently the weighted integral has factor
`(T-t)^(5λ-2)`.

The profiles are ordinary scalar functions. Integrability of the profile
density implies integrability of the physical density. Differentiability
of the streamfunction is needed only on the positive meridian, and the
center can be any function of time. Nonzero profile energy and eventual
boundedness of the absolute physical energy imply `λ ≥ 2/5`. Absolute
boundedness also covers the signed energy when `ε > 2`.
-/

@[expose] public section

noncomputable section

namespace Euler

open Filter MeasureTheory Euler.Similarity Set Topology

/-- Positive-radius meridian points used for the weighted integral. -/
abbrev PositiveMeridian := Ioi (0 : ℝ) × ℝ

/-- A positive meridian pair expressed in Euclidean coordinates. -/
def positiveMeridianPoint (q : PositiveMeridian) : ℝ^2 :=
  EuclideanSpace.single (0 : Fin 2) q.1.1 + EuclideanSpace.single (1 : Fin 2) q.2

/-- The measure `r³ dr dz` in S369–S376. -/
def weightedMeridianMeasure : Measure PositiveMeridian :=
  (Measure.volumeIoiPow 3).prod volume

/-- Profile energy density, with the Euclidean streamfunction gradient. -/
def profileEnergyDensity (eps : ℝ) (U Ψ : ℝ^2 → ℝ) (y : ℝ^2) : ℝ :=
  U y ^ 2 + (2 - eps) * ‖gradient Ψ y‖ ^ 2

/-- The weighted profile integral in S383. -/
def profileEnergy (eps : ℝ) (U Ψ : ℝ^2 → ℝ) : ℝ :=
  ∫ q : PositiveMeridian,
    profileEnergyDensity eps U Ψ (positiveMeridianPoint q) ∂weightedMeridianMeasure

/-- Physical energy density of scalar reduced velocity and streamfunction fields. -/
def physicalEnergyDensity (eps : ℝ) (u ψ : ℝ^2 → ℝ → ℝ) (x : ℝ^2) (t : ℝ) : ℝ :=
  u x t ^ 2 + (2 - eps) * ‖gradient (fun y ↦ ψ y t) x‖ ^ 2

/-- The weighted physical energy at a fixed time, S369. -/
def physicalEnergy (eps : ℝ) (u ψ : ℝ^2 → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ q : PositiveMeridian,
    physicalEnergyDensity eps u ψ (positiveMeridianPoint q) t ∂weightedMeridianMeasure

/-- The Euler specialization has coefficient one on the gradient energy, S370. -/
theorem physicalEnergy_one (u ψ : ℝ^2 → ℝ → ℝ) (t : ℝ) :
    physicalEnergy 1 u ψ t =
      ∫ q : PositiveMeridian,
        (u (positiveMeridianPoint q) t ^ 2 +
          ‖gradient (fun y ↦ ψ y t) (positiveMeridianPoint q)‖ ^ 2)
        ∂weightedMeridianMeasure := by
  norm_num [physicalEnergy, physicalEnergyDensity]

/-- The similarity map acts by positive radial dilation and an axial translation. -/
theorem similarityCoordinates_positiveMeridianPoint
    (lam singularTime : ℝ) (axialCenter : ℝ → ℝ) {t : ℝ}
    (ht : t < singularTime) (q : PositiveMeridian) :
    similarityCoordinates lam singularTime axialCenter (positiveMeridianPoint q) t =
      positiveMeridianPoint
        (⟨backwardPowerScale lam singularTime t * q.1.1,
          mul_pos (backwardPowerScale_pos ht) q.1.2⟩,
          backwardPowerScale lam singularTime t * (q.2 - axialCenter t)) := by
  ext i
  fin_cases i <;> simp [positiveMeridianPoint, similarityCoordinates, smul_eq_mul]

/-- The similarity pullback preserves integrability for the weighted measure. -/
theorem integrable_similarityCoordinates_positiveMeridian
    (g : ℝ^2 → ℝ) (lam singularTime : ℝ) (axialCenter : ℝ → ℝ) {t : ℝ}
    (hg : Integrable (fun q : PositiveMeridian ↦ g (positiveMeridianPoint q))
      weightedMeridianMeasure)
    (ht : t < singularTime) :
    Integrable
      (fun q : PositiveMeridian ↦
        g (similarityCoordinates lam singularTime axialCenter (positiveMeridianPoint q) t))
      weightedMeridianMeasure := by
  simp_rw [similarityCoordinates_positiveMeridianPoint lam singularTime axialCenter ht]
  exact hg.volumeIoiPow_prod_mul_sub 3 (backwardPowerScale_pos ht) (axialCenter t)

/-- The radial weight and both coordinates give the weighted Jacobian `(T-t)^(5λ)`. -/
theorem integral_similarityCoordinates_positiveMeridian
    (g : ℝ^2 → ℝ) (lam singularTime : ℝ) (axialCenter : ℝ → ℝ) {t : ℝ}
    (hg : Integrable (fun q : PositiveMeridian ↦ g (positiveMeridianPoint q))
      weightedMeridianMeasure)
    (ht : t < singularTime) :
    (∫ q : PositiveMeridian,
      g (similarityCoordinates lam singularTime axialCenter (positiveMeridianPoint q) t)
        ∂weightedMeridianMeasure) =
      (singularTime - t) ^ (5 * lam) *
        ∫ q : PositiveMeridian, g (positiveMeridianPoint q) ∂weightedMeridianMeasure := by
  have hscale : (backwardPowerScale lam singularTime t)⁻¹ ^ (3 + 2 : ℕ) =
      (singularTime - t) ^ (5 * lam) := by
    rw [backwardPowerScale, Real.rpow_neg (sub_pos.mpr ht).le, inv_inv]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (sub_pos.mpr ht).le]
    congr 1
    ring
  simp_rw [similarityCoordinates_positiveMeridianPoint lam singularTime axialCenter ht]
  simpa only [hscale, weightedMeridianMeasure] using
    integral_volumeIoiPow_prod_mul_sub 3 (backwardPowerScale_pos (alpha := lam) ht)
      (axialCenter t) hg

/-- The streamfunction gradient carries the amplitude `(T-t)^(-1)`, S377–S379. -/
theorem gradient_similarityStream
    (Ψ : ℝ^2 → ℝ) (lam singularTime : ℝ) (axialCenter : ℝ → ℝ) (x : ℝ^2) {t : ℝ}
    (hΨ : DifferentiableAt ℝ Ψ (similarityCoordinates lam singularTime axialCenter x t))
    (ht : t < singularTime) :
    gradient (fun y ↦ similarityScalar Ψ (1 - lam) lam singularTime axialCenter y t) x =
      backwardPowerScale 1 singularTime t •
        gradient Ψ (similarityCoordinates lam singularTime axialCenter x t) := by
  ext i
  simp only [gradient_apply_eq_partialDeriv, PiLp.smul_apply, smul_eq_mul]
  have h := partialDeriv_similarityScalar Ψ (1 - lam) lam singularTime axialCenter i x hΨ ht
  simpa only [sub_add_cancel] using h

/-- Both terms in the energy density have amplitude `(T-t)^(-2)`, S379–S381. -/
theorem physicalEnergyDensity_similarity
    (eps : ℝ) (U Ψ : ℝ^2 → ℝ) (lam singularTime : ℝ) (axialCenter : ℝ → ℝ)
    (x : ℝ^2) {t : ℝ}
    (hΨ : DifferentiableAt ℝ Ψ (similarityCoordinates lam singularTime axialCenter x t))
    (ht : t < singularTime) :
    physicalEnergyDensity eps
        (similarityScalar U 1 lam singularTime axialCenter)
        (similarityScalar Ψ (1 - lam) lam singularTime axialCenter) x t =
      backwardPowerScale 2 singularTime t *
        profileEnergyDensity eps U Ψ (similarityCoordinates lam singularTime axialCenter x t) := by
  have hsq : backwardPowerScale 1 singularTime t ^ 2 =
      backwardPowerScale 2 singularTime t := by
    simpa only [pow_two, one_add_one_eq_two] using
      (backwardPowerScale_mul (alpha := 1) (beta := 1) ht)
  unfold physicalEnergyDensity
  rw [gradient_similarityStream Ψ lam singularTime axialCenter x hΨ ht]
  simp only [similarityScalar, profileEnergyDensity, norm_smul, Real.norm_eq_abs,
    abs_of_pos (backwardPowerScale_pos ht), mul_pow, hsq]
  ring

/-- Finite profile energy gives an integrable physical energy density before the singular time. -/
theorem integrable_physicalEnergyDensity_similarity
    (eps : ℝ) (U Ψ : ℝ^2 → ℝ) (lam singularTime : ℝ) (axialCenter : ℝ → ℝ) {t : ℝ}
    (hΨ : ∀ q : PositiveMeridian, DifferentiableAt ℝ Ψ
      (similarityCoordinates lam singularTime axialCenter (positiveMeridianPoint q) t))
    (hintegrable : Integrable
      (fun q : PositiveMeridian ↦ profileEnergyDensity eps U Ψ (positiveMeridianPoint q))
      weightedMeridianMeasure)
    (ht : t < singularTime) :
    Integrable
      (fun q : PositiveMeridian ↦ physicalEnergyDensity eps
        (similarityScalar U 1 lam singularTime axialCenter)
        (similarityScalar Ψ (1 - lam) lam singularTime axialCenter) (positiveMeridianPoint q) t)
      weightedMeridianMeasure := by
  simp_rw [physicalEnergyDensity_similarity eps U Ψ lam singularTime axialCenter _ (hΨ _) ht]
  exact (integrable_similarityCoordinates_positiveMeridian
    (profileEnergyDensity eps U Ψ) lam singularTime axialCenter hintegrable ht).const_mul _

/-- Exact weighted energy scaling of the self-similar fields, Proposition S9 and S373/S382. -/
theorem physicalEnergy_similarity
    (eps : ℝ) (U Ψ : ℝ^2 → ℝ) (lam singularTime : ℝ) (axialCenter : ℝ → ℝ) {t : ℝ}
    (hΨ : ∀ q : PositiveMeridian, DifferentiableAt ℝ Ψ
      (similarityCoordinates lam singularTime axialCenter (positiveMeridianPoint q) t))
    (hintegrable : Integrable
      (fun q : PositiveMeridian ↦ profileEnergyDensity eps U Ψ (positiveMeridianPoint q))
      weightedMeridianMeasure)
    (ht : t < singularTime) :
    physicalEnergy eps (similarityScalar U 1 lam singularTime axialCenter)
        (similarityScalar Ψ (1 - lam) lam singularTime axialCenter) t =
      (singularTime - t) ^ (5 * lam - 2) * profileEnergy eps U Ψ := by
  unfold physicalEnergy
  simp_rw [physicalEnergyDensity_similarity eps U Ψ lam singularTime axialCenter _ (hΨ _) ht]
  rw [integral_const_mul,
    integral_similarityCoordinates_positiveMeridian
      (profileEnergyDensity eps U Ψ) lam singularTime axialCenter hintegrable ht,
    ← mul_assoc]
  change ((singularTime - t) ^ (-2 : ℝ) * (singularTime - t) ^ (5 * lam)) *
    profileEnergy eps U Ψ = _
  rw [← Real.rpow_add (sub_pos.mpr ht)]
  congr 2
  ring

private theorem tendsto_energyScale_atTop {lam singularTime : ℝ} (hlam : lam < 2 / 5) :
    Tendsto (fun t ↦ (singularTime - t) ^ (5 * lam - 2))
      (𝓝[<] singularTime) atTop := by
  have hbase_nhds : Tendsto (fun t : ℝ ↦ singularTime - t)
      (𝓝[<] singularTime) (𝓝 0) := by
    have hc : ContinuousAt (fun t : ℝ ↦ singularTime - t) singularTime := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hbase_pos : ∀ᶠ t in 𝓝[<] singularTime, 0 < singularTime - t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact sub_pos.mpr ht
  have hbase : Tendsto (fun t : ℝ ↦ singularTime - t)
      (𝓝[<] singularTime) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hbase_nhds, hbase_pos⟩
  exact (tendsto_rpow_neg_nhdsGT_zero (by linarith : 5 * lam - 2 < 0)).comp hbase

/-- A finite, nonzero profile energy and bounded absolute physical energy force
`λ ≥ 2/5`, S383–S385. The integral identity is proved above, not assumed. -/
theorem lam_ge_two_fifths_of_bounded_nonzero_profile_energy
    (eps : ℝ) (U Ψ : ℝ^2 → ℝ) (lam singularTime : ℝ) (axialCenter : ℝ → ℝ)
    (hΨ : ∀ q : PositiveMeridian, DifferentiableAt ℝ Ψ (positiveMeridianPoint q))
    (hintegrable : Integrable
      (fun q : PositiveMeridian ↦ profileEnergyDensity eps U Ψ (positiveMeridianPoint q))
      weightedMeridianMeasure)
    (hprofileEnergy : profileEnergy eps U Ψ ≠ 0)
    (hbounded : ∃ M : ℝ, ∀ᶠ t in 𝓝[<] singularTime,
      |physicalEnergy eps (similarityScalar U 1 lam singularTime axialCenter)
        (similarityScalar Ψ (1 - lam) lam singularTime axialCenter) t| ≤ M) :
    (2 / 5 : ℝ) ≤ lam := by
  by_contra hthreshold
  have hdiverge :
      Tendsto (fun t ↦ (singularTime - t) ^ (5 * lam - 2) * |profileEnergy eps U Ψ|)
        (𝓝[<] singularTime) atTop :=
    (tendsto_energyScale_atTop (lt_of_not_ge hthreshold)).atTop_mul_const
      (abs_pos.mpr hprofileEnergy)
  obtain ⟨M, hM⟩ := hbounded
  have hlarge : ∀ᶠ t in 𝓝[<] singularTime,
      M + 1 ≤ (singularTime - t) ^ (5 * lam - 2) * |profileEnergy eps U Ψ| :=
    tendsto_atTop.1 hdiverge (M + 1)
  have hbefore : ∀ᶠ t in 𝓝[<] singularTime, t ∈ Iio singularTime := self_mem_nhdsWithin
  obtain ⟨t, hMt, htM, ht⟩ := (hM.and (hlarge.and hbefore)).exists
  have hΨt (q : PositiveMeridian) : DifferentiableAt ℝ Ψ
      (similarityCoordinates lam singularTime axialCenter (positiveMeridianPoint q) t) := by
    rw [similarityCoordinates_positiveMeridianPoint lam singularTime axialCenter ht]
    exact hΨ _
  rw [physicalEnergy_similarity eps U Ψ lam singularTime axialCenter hΨt hintegrable ht,
    abs_mul, abs_of_pos (Real.rpow_pos_of_pos (sub_pos.mpr ht) _)] at hMt
  linarith

end Euler
