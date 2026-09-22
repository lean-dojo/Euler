/-
Copyright (c) 2026 Robert Joseph George and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/

module

public import Euler.Similarity.Derivation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Profile equations in Appendices A and C

Here we formalize Propositions S5 and S7. Substituting the similarity profile
into the physical equations gives the stationary equations after canceling
positive powers of `T-t`. Proposition S7 sets `ε = 1` and `λ = 1/2`.

The elliptic operator is `∂rr + 3/r ∂r + ∂zz` away from the axis. At the axis
we use `4∂rr + ∂zz`. This calculation uses that assigned value; proving
continuity across the axis requires the separate regularity and parity argument.
-/

@[expose] public section

open Euler.Calculus Euler.Coordinates

noncomputable section

namespace Euler

open Euler.Similarity

/-- Two spatial powers factor out of the elliptic operator, both off the
axis and at its assigned axis value. This proves S291–S294 directly from
the first and second coordinate chain rules. -/
theorem axisExtendedLaplacian_similarityScalar
    (profile : ℝ^2 → ℝ) (alpha lam singularTime : ℝ)
    (axialCenter : ℝ → ℝ) (x : ℝ^2) {t : ℝ}
    (hprofile : ContDiff ℝ 2 profile) (ht : t < singularTime) :
    Euler.Axisymmetric.axisExtendedLaplacian
        (fun y ↦ similarityScalar profile alpha lam singularTime axialCenter y t) x =
      backwardPowerScale (alpha + 2 * lam) singularTime t *
        Euler.Axisymmetric.axisExtendedLaplacian profile
          (similarityCoordinates lam singularTime axialCenter x t) := by
  have hrr := partialDeriv_partialDeriv_similarityScalar
    profile alpha lam singularTime axialCenter 0 0 x hprofile ht
  have hzz := partialDeriv_partialDeriv_similarityScalar
    profile alpha lam singularTime axialCenter 1 1 x hprofile ht
  have hradial :
      (similarityCoordinates lam singularTime axialCenter x t) 0 =
        backwardPowerScale lam singularTime t * x 0 :=
    similarityCoordinates_radial lam singularTime axialCenter x t
  by_cases hr : x 0 = 0
  · have hyr : (similarityCoordinates lam singularTime axialCenter x t) 0 = 0 := by
      rw [hradial, hr, mul_zero]
    rw [Euler.Axisymmetric.axisExtendedLaplacian_of_eq_zero _ _ hr,
      Euler.Axisymmetric.axisExtendedLaplacian_of_eq_zero _ _ hyr,
      hrr, hzz]
    ring
  · have hscale : backwardPowerScale lam singularTime t ≠ 0 :=
      ne_of_gt (backwardPowerScale_pos ht)
    have hyr : (similarityCoordinates lam singularTime axialCenter x t) 0 ≠ 0 := by
      rw [hradial]
      exact mul_ne_zero hscale hr
    have hfirst := partialDeriv_similarityScalar
      profile alpha lam singularTime axialCenter 0 x
      (hprofile.differentiable (by norm_num)).differentiableAt ht
    have hproduct :
        backwardPowerScale (alpha + lam) singularTime t *
            backwardPowerScale lam singularTime t =
          backwardPowerScale (alpha + 2 * lam) singularTime t := by
      rw [backwardPowerScale_mul ht]
      congr 1
      ring
    rw [Euler.Axisymmetric.axisExtendedLaplacian_of_ne_zero _ _ hr,
      Euler.Axisymmetric.axisExtendedLaplacian_of_ne_zero _ _ hyr]
    unfold Euler.Axisymmetric.reducedLaplacian
    rw [hrr, hzz, hfirst, hradial, ← hproduct]
    field_simp

/-- The physical elliptic residual is `(T-t)^(-1-lambda)` times the
stationary residual. No elliptic equation is assumed. -/
theorem axisymmetricStreamResidual_similarityFields
    (F : Profile) (lam singularTime : ℝ)
    (axialCenter : ℝ → ℝ) (x : (ℝ^2)) {t : ℝ}
    (hPsi : ContDiff ℝ 2 F.Ψ) (ht : t < singularTime) :
    Euler.Axisymmetric.axisymmetricStreamResidual
        (similarityFields F lam singularTime axialCenter).vorticity
        (similarityFields F lam singularTime axialCenter).streamFunction x t =
      backwardPowerScale (1 + lam) singularTime t *
        (signedElliptic classicalAxisymmetricDifferential F.Ψ
            (similarityCoordinates lam singularTime axialCenter x t) -
          F.Ω (similarityCoordinates lam singularTime axialCenter x t)) := by
  unfold Euler.Axisymmetric.axisymmetricStreamResidual signedElliptic
  rw [Euler.Axisymmetric.axisymmetricLaplacian_eq_axisExtendedLaplacian]
  change -Euler.Axisymmetric.axisExtendedLaplacian
      (fun y ↦ similarityScalar F.Ψ (1 - lam) lam singularTime axialCenter y t) x -
      backwardPowerScale (1 + lam) singularTime t *
        F.Ω (similarityCoordinates lam singularTime axialCenter x t) = _
  rw [axisExtendedLaplacian_similarityScalar
    F.Ψ (1 - lam) lam singularTime axialCenter x hPsi ht]
  rw [show 1 - lam + 2 * lam = 1 + lam by ring]
  have hoperator (y : (ℝ^2)) :
      Euler.Axisymmetric.axisExtendedLaplacian F.Ψ y =
        axisymmetricLaplacian classicalAxisymmetricDifferential F.Ψ y :=
    (Euler.Axisymmetric.axisymmetricLaplacian_eq_axisExtendedLaplacian F.Ψ y).symm
  rw [hoperator]
  ring

/-- All three physical equations at a point are equivalent to the three
stationary equations at its similarity coordinate. -/
theorem similarityFields_equations_iff
    (eps : ℝ) (F : Profile)
    (lam axialDrift singularTime : ℝ) (axialCenter : ℝ → ℝ)
    (x : (ℝ^2)) {t : ℝ}
    (hU : DifferentiableAt ℝ F.U
      (similarityCoordinates lam singularTime axialCenter x t))
    (hOmega : DifferentiableAt ℝ F.Ω
      (similarityCoordinates lam singularTime axialCenter x t))
    (hPsi : ContDiff ℝ 2 F.Ψ)
    (hcenter : HasDerivAt axialCenter
      (-axialDrift * backwardPowerScale (1 - lam) singularTime t) t)
    (ht : t < singularTime) :
    (convectionVariedSwirlResidual eps
        (similarityFields F lam singularTime axialCenter).swirl
        (similarityFields F lam singularTime axialCenter).streamFunction x t = 0 ∧
      convectionVariedVorticityResidual eps
        (similarityFields F lam singularTime axialCenter).swirl
        (similarityFields F lam singularTime axialCenter).vorticity
        (similarityFields F lam singularTime axialCenter).streamFunction x t = 0 ∧
      Euler.Axisymmetric.axisymmetricStreamResidual
        (similarityFields F lam singularTime axialCenter).vorticity
        (similarityFields F lam singularTime axialCenter).streamFunction x t = 0) ↔
    (swirlResidual eps lam axialDrift
        classicalAxisymmetricDifferential F.U F.Ψ
        (similarityCoordinates lam singularTime axialCenter x t) = 0 ∧
      vorticityResidual eps lam axialDrift
        classicalAxisymmetricDifferential F.U F.Ψ F.Ω
        (similarityCoordinates lam singularTime axialCenter x t) = 0 ∧
      signedElliptic classicalAxisymmetricDifferential F.Ψ
        (similarityCoordinates lam singularTime axialCenter x t) =
        F.Ω (similarityCoordinates lam singularTime axialCenter x t)) := by
  have hPsi' : DifferentiableAt ℝ F.Ψ
      (similarityCoordinates lam singularTime axialCenter x t) :=
    (hPsi.differentiable (by norm_num)).differentiableAt
  rw [convectionVariedSwirlResidual_similarityFields
    eps F lam axialDrift singularTime axialCenter x hU hPsi' hcenter ht]
  rw [convectionVariedVorticityResidual_similarityFields
    eps F lam axialDrift singularTime axialCenter x hU hPsi' hOmega hcenter ht]
  rw [axisymmetricStreamResidual_similarityFields
    F lam singularTime axialCenter x hPsi ht]
  have hscale (alpha : ℝ) : backwardPowerScale alpha singularTime t ≠ 0 :=
    ne_of_gt (backwardPowerScale_pos ht)
  simp only [mul_eq_zero, hscale, false_or, sub_eq_zero]

/-- Similarity coordinates reached from a physical space-time domain. -/
def travelingProfileDomain
    (lam singularTime : ℝ) (axialCenter : ℝ → ℝ)
    (Ωdom : Set (ℝ^2)) (I : Set ℝ) : Set (ℝ^2) :=
  (fun xt : (ℝ^2) × ℝ ↦
    similarityCoordinates lam singularTime axialCenter xt.1 xt.2) '' (Ωdom ×ˢ I)

/-- The complete convection-varied physical system is equivalent to the
stationary system on the image of its domain. The elliptic conjunct is
derived from the stream-residual transformation. -/
theorem isConvectionVariedSolutionOn_similarityFields_iff
    (eps : ℝ) (F : Profile)
    (lam axialDrift singularTime : ℝ) (axialCenter : ℝ → ℝ)
    (Ωdom : Set (ℝ^2)) (I : Set ℝ)
    (hU : ∀ x ∈ Ωdom, ∀ t ∈ I, DifferentiableAt ℝ F.U
      (similarityCoordinates lam singularTime axialCenter x t))
    (hOmega : ∀ x ∈ Ωdom, ∀ t ∈ I, DifferentiableAt ℝ F.Ω
      (similarityCoordinates lam singularTime axialCenter x t))
    (hPsi : ContDiff ℝ 2 F.Ψ)
    (hcenter : ∀ t ∈ I, HasDerivAt axialCenter
      (-axialDrift * backwardPowerScale (1 - lam) singularTime t) t)
    (htime : ∀ t ∈ I, t < singularTime) :
    (similarityFields F lam singularTime axialCenter).IsConvectionVariedSolutionOn
        eps Ωdom I ↔
      F.IsStationaryOn eps lam axialDrift
        classicalAxisymmetricDifferential
        (travelingProfileDomain lam singularTime axialCenter Ωdom I) := by
  have hpoint (x : (ℝ^2)) (hx : x ∈ Ωdom) (t : ℝ) (ht : t ∈ I) :=
    similarityFields_equations_iff eps F lam axialDrift singularTime axialCenter x
      (hU x hx t ht) (hOmega x hx t ht) hPsi (hcenter t ht) (htime t ht)
  constructor
  · intro h
    have hall (x : (ℝ^2)) (hx : x ∈ Ωdom) (t : ℝ) (ht : t ∈ I) :=
      (hpoint x hx t ht).mp ⟨h.1 x hx t ht, h.2.1 x hx t ht, h.2.2 x hx t ht⟩
    refine ⟨?_, ?_, ?_⟩
    · rintro y ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      exact (hall x hx t ht).2.2
    · rintro y ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      exact (hall x hx t ht).1
    · rintro y ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      exact (hall x hx t ht).2.1
  · intro h
    have hall (x : (ℝ^2)) (hx : x ∈ Ωdom) (t : ℝ) (ht : t ∈ I) := by
      have hy : similarityCoordinates lam singularTime axialCenter x t ∈
          travelingProfileDomain lam singularTime axialCenter Ωdom I :=
        ⟨(x, t), ⟨hx, ht⟩, rfl⟩
      exact (hpoint x hx t ht).mpr ⟨h.2.1 _ hy, h.2.2 _ hy, h.1 _ hy⟩
    exact ⟨fun x hx t ht ↦ (hall x hx t ht).1,
      fun x hx t ht ↦ (hall x hx t ht).2.1,
      fun x hx t ht ↦ (hall x hx t ht).2.2⟩

/-- The stationary system is exactly the displayed traveling-profile
equations after substituting `Uʳ = -r ∂_z Ψ` and `Uᶻ = 2Ψ + r ∂_r Ψ`.
The elliptic operator uses its assigned value at the axis; no continuity
of that extension is asserted. -/
theorem isStationaryOn_half_iff
    (eps lam axialDrift : ℝ) (F : Profile) (s : Set (ℝ^2)) :
    F.IsStationaryOn eps lam axialDrift
        classicalAxisymmetricDifferential s ↔
      ∀ x ∈ s,
        (F.U x + meridianR x * (lam - eps * partialDeriv 1 F.Ψ x) *
            partialDeriv 0 F.U x +
          (axialDrift + lam * meridianZ x +
              eps * (2 * F.Ψ x + meridianR x * partialDeriv 0 F.Ψ x)) *
            partialDeriv 1 F.U x = 2 * F.U x * partialDeriv 1 F.Ψ x) ∧
        ((1 + lam) * F.Ω x + meridianR x * (lam - eps * partialDeriv 1 F.Ψ x) *
            partialDeriv 0 F.Ω x +
          (axialDrift + lam * meridianZ x +
              eps * (2 * F.Ψ x + meridianR x * partialDeriv 0 F.Ψ x)) *
            partialDeriv 1 F.Ω x = 2 * F.U x * partialDeriv 1 F.U x) ∧
        -Euler.Axisymmetric.axisExtendedLaplacian F.Ψ x = F.Ω x := by
  have hu (x : (ℝ^2)) :
      swirlResidual eps lam axialDrift
          classicalAxisymmetricDifferential F.U F.Ψ x =
        F.U x + meridianR x * (lam - eps * partialDeriv 1 F.Ψ x) *
            partialDeriv 0 F.U x +
          (axialDrift + lam * meridianZ x +
              eps * (2 * F.Ψ x + meridianR x * partialDeriv 0 F.Ψ x)) *
            partialDeriv 1 F.U x - 2 * F.U x * partialDeriv 1 F.Ψ x := by
    unfold swirlResidual radialTransportFactor axialTransport
    simp only [classicalAxisymmetricDifferential, profileDR, profileDZ]
    ring
  have homega (x : (ℝ^2)) :
      vorticityResidual eps lam axialDrift
          classicalAxisymmetricDifferential F.U F.Ψ F.Ω x =
        (1 + lam) * F.Ω x + meridianR x * (lam - eps * partialDeriv 1 F.Ψ x) *
            partialDeriv 0 F.Ω x +
          (axialDrift + lam * meridianZ x +
              eps * (2 * F.Ψ x + meridianR x * partialDeriv 0 F.Ψ x)) *
            partialDeriv 1 F.Ω x - 2 * F.U x * partialDeriv 1 F.U x := by
    unfold vorticityResidual radialTransportFactor axialTransport
    simp only [classicalAxisymmetricDifferential, profileDR, profileDZ]
    ring
  have hpsi (x : (ℝ^2)) :
      signedElliptic classicalAxisymmetricDifferential F.Ψ x =
        -Euler.Axisymmetric.axisExtendedLaplacian F.Ψ x := by
    exact congrArg Neg.neg
      (Euler.Axisymmetric.axisymmetricLaplacian_eq_axisExtendedLaplacian F.Ψ x)
  constructor
  · intro h x hx
    exact ⟨sub_eq_zero.mp ((hu x).symm.trans (h.2.1 x hx)),
      sub_eq_zero.mp ((homega x).symm.trans (h.2.2 x hx)),
      (hpsi x).symm.trans (h.1 x hx)⟩
  · intro h
    exact ⟨fun x hx ↦ (hpsi x).trans (h x hx).2.2,
      fun x hx ↦ (hu x).trans (sub_eq_zero.mpr (h x hx).1),
      fun x hx ↦ (homega x).trans (sub_eq_zero.mpr (h x hx).2.1)⟩

/-- Appendix C, Proposition S7: the reduced Euler equations at
`ε = 1`, `λ = 1/2` are equivalent to S333–S335 on the similarity image.
The powers in the time, transport, and elliptic terms have already been
factored by the preceding chain-rule theorems. -/
theorem isSolutionOn_similarityFields_half_iff
    (F : Profile) (axialDrift singularTime : ℝ)
    (axialCenter : ℝ → ℝ) (s : Set (ℝ^2)) (I : Set ℝ)
    (hU : ∀ x ∈ s, ∀ t ∈ I, DifferentiableAt ℝ F.U
      (similarityCoordinates (1 / 2) singularTime axialCenter x t))
    (hOmega : ∀ x ∈ s, ∀ t ∈ I, DifferentiableAt ℝ F.Ω
      (similarityCoordinates (1 / 2) singularTime axialCenter x t))
    (hPsi : ContDiff ℝ 2 F.Ψ)
    (hcenter : ∀ t ∈ I, HasDerivAt axialCenter
      (-axialDrift * backwardPowerScale (1 - 1 / 2) singularTime t) t)
    (htime : ∀ t ∈ I, t < singularTime) :
    (similarityFields F (1 / 2) singularTime axialCenter).IsSolutionOn
        s I ↔
      ∀ x ∈ travelingProfileDomain (1 / 2) singularTime axialCenter s I,
        (F.U x + meridianR x * (1 / 2 - partialDeriv 1 F.Ψ x) *
            partialDeriv 0 F.U x +
          (axialDrift + 1 / 2 * meridianZ x +
              (2 * F.Ψ x + meridianR x * partialDeriv 0 F.Ψ x)) *
            partialDeriv 1 F.U x = 2 * F.U x * partialDeriv 1 F.Ψ x) ∧
        (3 / 2 * F.Ω x + meridianR x * (1 / 2 - partialDeriv 1 F.Ψ x) *
            partialDeriv 0 F.Ω x +
          (axialDrift + 1 / 2 * meridianZ x +
              (2 * F.Ψ x + meridianR x * partialDeriv 0 F.Ψ x)) *
            partialDeriv 1 F.Ω x = 2 * F.U x * partialDeriv 1 F.U x) ∧
        -Euler.Axisymmetric.axisExtendedLaplacian F.Ψ x = F.Ω x := by
  have h := (isConvectionVariedSolutionOn_similarityFields_iff
    1 F (1 / 2) axialDrift singularTime axialCenter s I hU hOmega hPsi hcenter htime).trans
      (isStationaryOn_half_iff 1 (1 / 2) axialDrift F
        (travelingProfileDomain (1 / 2) singularTime axialCenter s I))
  simpa only [Euler.Axisymmetric.ReducedFields.IsConvectionVariedSolutionOn,
    Euler.Axisymmetric.ReducedFields.IsSolutionOn,
    convectionVariedSwirlResidual_eps_one, convectionVariedVorticityResidual_eps_one,
    one_mul, show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num] using h

end Euler
