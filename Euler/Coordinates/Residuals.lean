/-
Copyright (c) 2026 Robert Joseph George and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/

module

public import Euler.Equations.Stationary
public import Euler.Coordinates.SinhCoordinates
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The profile equations in computational coordinates

Appendix B uses `R = sinh ρ` and `Z = sinh ζ` to spread the computational grid
across an unbounded meridian plane. The chain rules in `SinhCoordinates`
turn each physical residual into the corresponding computational residual.
Here we formalize the resulting equations, S324–S327.

At the axis the radial quotient takes its removable value. For an even smooth
profile, the first radial derivative vanishes there; the second derivative
supplies the limit.
-/

@[expose] public section

open Euler.Calculus
open Euler.Coordinates

noncomputable section

namespace Euler

open scoped Topology

/-- Equation (S324), the transformed reduced-swirl residual. -/
def computationalSwirlResidual
    (eps lam C : ℝ) (u psi : (ℝ^2 → ℝ)) : (ℝ^2 → ℝ) :=
  fun x ↦
    u x - 2 * u x * profileDZ psi x / Real.cosh (meridianZ x) +
      Real.sinh (meridianR x) / Real.cosh (meridianR x) * profileDR u x *
        (lam - eps * profileDZ psi x / Real.cosh (meridianZ x)) +
      profileDZ u x / Real.cosh (meridianZ x) *
        (C + lam * Real.sinh (meridianZ x) +
          eps * (2 * psi x +
            Real.sinh (meridianR x) / Real.cosh (meridianR x) * profileDR psi x))

/-- Equation (S325), the transformed reduced-vorticity residual. -/
def computationalVorticityResidual
    (eps lam C : ℝ) (u psi omega : (ℝ^2 → ℝ)) : (ℝ^2 → ℝ) :=
  fun x ↦
    (1 + lam) * omega x -
      2 * u x * profileDZ u x / Real.cosh (meridianZ x) +
      Real.sinh (meridianR x) / Real.cosh (meridianR x) * profileDR omega x *
        (lam - eps * profileDZ psi x / Real.cosh (meridianZ x)) +
      profileDZ omega x / Real.cosh (meridianZ x) *
        (C + lam * Real.sinh (meridianZ x) +
          eps * (2 * psi x +
            Real.sinh (meridianR x) / Real.cosh (meridianR x) * profileDR psi x))

/-- Equation (S326), the transformed stream-vorticity residual. -/
def computationalPoissonResidual (psi omega : (ℝ^2 → ℝ)) : (ℝ^2 → ℝ) :=
  fun x ↦ omega x + computationalElliptic psi x

/-- Formula (S324) is the pullback of the Euler `U` residual. -/
theorem computationalSwirlResidual_pullback
    (eps lam C : ℝ) {U Psi : (ℝ^2 → ℝ)}
    (hU : ContDiff ℝ 1 U) (hPsi : ContDiff ℝ 1 Psi) (x : (ℝ^2)) :
    computationalSwirlResidual eps lam C (sinhPullback U)
        (sinhPullback Psi) x =
      swirlResidual eps lam C classicalAxisymmetricDifferential U Psi
        (sinhCoordinates x) := by
  dsimp only [swirlResidual, radialTransportFactor, axialTransport]
  simp only [classicalAxisymmetricDifferential]
  unfold computationalSwirlResidual
  rw [profileDR_sinhPullback hU x, profileDZ_sinhPullback hU x]
  rw [profileDR_sinhPullback hPsi x, profileDZ_sinhPullback hPsi x]
  simp only [sinhPullback,
    meridianR_sinhCoordinates, meridianZ_sinhCoordinates]
  field_simp [(Real.cosh_pos (meridianR x)).ne', (Real.cosh_pos (meridianZ x)).ne']
  ring

/-- Formula (S325) is the pullback of the Euler `Ω` residual. -/
theorem computationalVorticityResidual_pullback
    (eps lam C : ℝ) {U Psi Omega : (ℝ^2 → ℝ)}
    (hU : ContDiff ℝ 1 U) (hPsi : ContDiff ℝ 1 Psi)
    (hOmega : ContDiff ℝ 1 Omega) (x : (ℝ^2)) :
    computationalVorticityResidual eps lam C (sinhPullback U)
        (sinhPullback Psi) (sinhPullback Omega) x =
      vorticityResidual eps lam C classicalAxisymmetricDifferential U Psi Omega
        (sinhCoordinates x) := by
  dsimp only [vorticityResidual, radialTransportFactor, axialTransport]
  simp only [classicalAxisymmetricDifferential]
  unfold computationalVorticityResidual
  rw [profileDR_sinhPullback hOmega x,
    profileDZ_sinhPullback hOmega x]
  rw [profileDR_sinhPullback hPsi x, profileDZ_sinhPullback hPsi x]
  rw [profileDZ_sinhPullback hU x]
  simp only [sinhPullback,
    meridianR_sinhCoordinates, meridianZ_sinhCoordinates]
  field_simp [(Real.cosh_pos (meridianR x)).ne', (Real.cosh_pos (meridianZ x)).ne']
  ring

/-- Formula (S326) is the pullback of the physical stream-vorticity residual. -/
theorem computationalPoissonResidual_pullback
    {Psi Omega : (ℝ^2 → ℝ)} (hPsi : ContDiff ℝ 2 Psi) (x : (ℝ^2)) :
    computationalPoissonResidual (sinhPullback Psi)
        (sinhPullback Omega) x =
      Omega (sinhCoordinates x) +
        axisymmetricLaplacian classicalAxisymmetricDifferential Psi
          (sinhCoordinates x) := by
  rw [computationalPoissonResidual, sinhPullback]
  rw [computationalElliptic_sinhPullback hPsi x]

end Euler
