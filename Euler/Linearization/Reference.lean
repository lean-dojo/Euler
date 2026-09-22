/-
Copyright (c) 2026 Robert Joseph George and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/
module

public import Euler.Calculus.ChainRule
import Mathlib.Tactic.Ring

/-!
# Recentered reference profiles and residual correction

Appendix G, equations S434–S443 and S452–S455, fixes the analysis origin at
a meridional fixed point and corrects the reference amplitude rate.

An axial shift by `a` also changes the constant transport coefficient from
`C` to `C + λ * a`. The root condition is a hypothesis; these identities
do not assert existence of a root of a numerical profile.

The amplitude correction divides by the nonzero reference value at the
origin. It makes the corrected scalar residual vanish there, while the
same correction must also be applied to the vorticity residual.
-/

@[expose] public noncomputable section

namespace Euler.Linearization

local notation "Point" => EuclideanSpace ℝ (Fin 2)

/-- Translation in the axial coordinate, with the radial coordinate unchanged. -/
def axialShift (a : ℝ) (x : Point) : Point :=
  x + EuclideanSpace.single 1 a

/-- A reference profile expressed relative to the new axial origin. -/
def recenter (a : ℝ) (f : Point → ℝ) (x : Point) : ℝ :=
  f (axialShift a x)

/-- The constant axial drift after changing coordinates by `z ↦ z + a`. -/
def recenteredDrift (lam C a : ℝ) : ℝ :=
  C + lam * a

/-- Axial translation preserves the radial coordinate. -/
@[simp]
theorem axialShift_radial (a : ℝ) (x : Point) :
    axialShift a x 0 = x 0 := by
  simp [axialShift]

/-- The axial coordinate acquires the chosen shift. -/
@[simp]
theorem axialShift_axial (a : ℝ) (x : Point) :
    axialShift a x 1 = x 1 + a := by
  simp [axialShift]

/-- The new origin is the chosen point on the old symmetry axis. -/
@[simp]
theorem axialShift_zero (a : ℝ) :
    axialShift a 0 = EuclideanSpace.single 1 a := by
  simp [axialShift]

/-- Recentered evaluation at the origin is evaluation at the chosen axial point. -/
@[simp]
theorem recenter_zero (a : ℝ) (f : Point → ℝ) :
    recenter a f 0 = f (EuclideanSpace.single 1 a) := by
  simp [recenter]

/-- Recentring preserves coordinate derivatives at points where the
original profile is differentiable. The translation has identity derivative. -/
theorem partialDeriv_recenter (a : ℝ) (f : Point → ℝ) (i : Fin 2) (x : Point)
    (hf : DifferentiableAt ℝ f (axialShift a x)) :
    partialDeriv i (recenter a f) x = partialDeriv i f (axialShift a x) := by
  change partialDeriv i (fun y ↦ f (axialShift a y)) x = _
  simpa [partialDeriv, Function.comp_def] using
    congrArg (fun L : Point →L[ℝ] ℝ ↦ L (EuclideanSpace.single i 1))
      (hf.hasFDerivAt.comp x ((hasFDerivAt_id x).add_const (EuclideanSpace.single 1 a))).fderiv

/-- The dilation and constant drift transform together under axial translation. -/
theorem recenteredDrift_transport (lam C a : ℝ) (x : Point) :
    lam * x 1 + recenteredDrift lam C a =
      lam * axialShift a x 1 + C := by
  simp only [recenteredDrift, axialShift_axial]
  ring

/-- S436 implies S439 with the translated drift constant retained. -/
theorem recentered_origin_fixed (lam C a : ℝ) (psi : Point → ℝ)
    (hroot : C + lam * a + 2 * psi (EuclideanSpace.single 1 a) = 0) :
    recenteredDrift lam C a + 2 * recenter a psi 0 = 0 := by
  simpa [recenteredDrift] using hroot

/-- The amplitude offset in S452, computed from the raw scalar residual. -/
def amplitudeOffset (u rawResidual : Point → ℝ) : ℝ :=
  -rawResidual 0 / u 0

/-- Adding an amplitude rate adds that rate times the corresponding reference field
to its stationary evolution residual. Both equations use the same rate correction. -/
def correctedResidual (offset : ℝ) (field rawResidual : Point → ℝ) (x : Point) : ℝ :=
  rawResidual x + offset * field x

/-- The scalar residual correction in S489–S490 vanishes at the origin. -/
theorem correctedResidual_origin (u rawResidual : Point → ℝ) (hu : u 0 ≠ 0) :
    correctedResidual (amplitudeOffset u rawResidual) u rawResidual 0 = 0 := by
  simp [correctedResidual, amplitudeOffset, div_mul_cancel₀ _ hu]

/-- Applying the correction to the reference vorticity preserves the same
amplitude offset as in the scalar equation, as required by S455. -/
theorem correctedResidual_vorticity (u omega rawU rawOmega : Point → ℝ) (x : Point) :
    correctedResidual (amplitudeOffset u rawU) omega rawOmega x =
      rawOmega x - rawU 0 / u 0 * omega x := by
  simp only [correctedResidual, amplitudeOffset]
  ring

end Euler.Linearization
