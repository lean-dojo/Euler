/-
Copyright (c) 2026 Robert Joseph George and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/
module

public import Euler.Linearization.Reference
public import Euler.Calculus.ChainRule
public import Euler.Calculus.AxisymmetricProfile
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Ring

/-!
# Perturbation equations in Appendix G

Here we expand S421–S424 around the reference profile to obtain S456–S470.
The dilation exponent stays fixed; the axial drift and amplitude rate may vary.
The reference profile's residual is kept in the equations.

`u`, `omega`, and `psi` denote reduced swirl, vorticity, and streamfunction.
`du`, `dw`, and `dp` denote perturbations, not derivatives. We write the radial
and axial derivatives as `Dr` and `Dz`; `dC` and `dcu` perturb the two rates.

The printed label `L_ω` in S457 should be `N_u`, the nonlinear swirl term.
We call it `nonlinearSwirl` and differentiate that expression in S471 and S478.
-/

@[expose] public noncomputable section

namespace Euler.Linearization

local notation "Dr" => partialDeriv (0 : Fin 2)
local notation "Dz" => partialDeriv (1 : Fin 2)

/-- The reduced-swirl evolution operator in S421: `∂τ u = swirlEvolution ...`.
Transport is subtracted because it has been moved to the right of the equation. -/
def swirlEvolution (lam C cu : ℝ) (u psi : ℝ^2 → ℝ) (x : ℝ^2) : ℝ :=
  2 * u x * Dz psi x + cu * u x
    - (lam * x 0 - x 0 * Dz psi x) * Dr u x
    - (lam * x 1 + C + 2 * psi x + x 0 * Dr psi x) * Dz u x

/-- The reduced-vorticity evolution operator in S422, with `c_ω = c_u - λ`. -/
def vorticityEvolution (lam C cu : ℝ) (u omega psi : ℝ^2 → ℝ) (x : ℝ^2) : ℝ :=
  2 * u x * Dz u x + (cu - lam) * omega x
    - (lam * x 0 - x 0 * Dz psi x) * Dr omega x
    - (lam * x 1 + C + 2 * psi x + x 0 * Dr psi x) * Dz omega x

/-- Linear scalar operator S456. The reference rate `cu` already includes the
residual correction; `dC` and `dcu` are spatially constant perturbations. -/
def linearSwirl (lam C cu : ℝ) (u psi du dp : ℝ^2 → ℝ)
    (dC dcu : ℝ) (x : ℝ^2) : ℝ :=
  (2 * Dz psi x + cu) * du x
    - (lam * x 0 - x 0 * Dz psi x) * Dr du x
    - (lam * x 1 + C + 2 * psi x + x 0 * Dr psi x) * Dz du x
    + (2 * u x + x 0 * Dr u x) * Dz dp x
    - x 0 * Dz u x * Dr dp x - 2 * Dz u x * dp x
    - Dz u x * dC + u x * dcu

/-- Quadratic scalar remainder S457, denoted `N_u` in the perturbation equation. -/
def nonlinearSwirl (du dp : ℝ^2 → ℝ) (dC dcu : ℝ) (x : ℝ^2) : ℝ :=
  x 0 * Dz dp x * Dr du x
    - (dC + 2 * dp x + x 0 * Dr dp x) * Dz du x
    + 2 * du x * Dz dp x + dcu * du x

/-- Linear vorticity operator S464. -/
def linearVorticity (lam C cu : ℝ) (u omega psi du dw dp : ℝ^2 → ℝ)
    (dC dcu : ℝ) (x : ℝ^2) : ℝ :=
  (cu - lam) * dw x
    - (lam * x 0 - x 0 * Dz psi x) * Dr dw x
    - (lam * x 1 + C + 2 * psi x + x 0 * Dr psi x) * Dz dw x
    + 2 * Dz u x * du x + 2 * u x * Dz du x
    - 2 * Dz omega x * dp x + x 0 * Dr omega x * Dz dp x
    - x 0 * Dz omega x * Dr dp x - Dz omega x * dC + omega x * dcu

/-- Quadratic vorticity remainder S465, with reconstructed perturbation velocity. -/
def nonlinearVorticity (du dw dp : ℝ^2 → ℝ) (dC dcu : ℝ) (x : ℝ^2) : ℝ :=
  x 0 * Dz dp x * Dr dw x
    - (dC + 2 * dp x + x 0 * Dr dp x) * Dz dw x
    + 2 * du x * Dz du x + dcu * dw x

/-- S432–S433: both reconstructed meridional velocity components split into
reference and perturbation velocities, by the sum rule for derivatives. -/
theorem meridional_velocity_add (psi dp : ℝ^2 → ℝ) (x : ℝ^2)
    (hp : DifferentiableAt ℝ psi x) (hdp : DifferentiableAt ℝ dp x) :
    -x 0 * Dz (fun y ↦ psi y + dp y) x =
        -x 0 * Dz psi x + (-x 0 * Dz dp x) ∧
      2 * (psi x + dp x) + x 0 * Dr (fun y ↦ psi y + dp y) x =
        (2 * psi x + x 0 * Dr psi x) + (2 * dp x + x 0 * Dr dp x) := by
  simp only [partialDeriv_add hp hdp]
  constructor <;> ring

/-- S453: changing the reference amplitude rate changes its scalar residual
by precisely the rate increment times the reference scalar. -/
theorem swirlEvolution_corrected (lam C cu offset : ℝ) (u psi : ℝ^2 → ℝ) (x : ℝ^2) :
    swirlEvolution lam C (cu + offset) u psi x =
      correctedResidual offset u (swirlEvolution lam C cu u psi) x := by
  unfold swirlEvolution correctedResidual
  ring

/-- S455: the same amplitude correction applies to the reference vorticity. -/
theorem vorticityEvolution_corrected (lam C cu offset : ℝ)
    (u omega psi : ℝ^2 → ℝ) (x : ℝ^2) :
    vorticityEvolution lam C (cu + offset) u omega psi x =
      correctedResidual offset omega (vorticityEvolution lam C cu u omega psi) x := by
  unfold vorticityEvolution correctedResidual
  ring

/-- S437–S438: translating both profiles and the drift preserves the scalar
equation's raw residual. In particular the drift must change by `λa`. -/
theorem swirlEvolution_recenter (lam C cu a : ℝ) (u psi : ℝ^2 → ℝ) (x : ℝ^2)
    (hu : DifferentiableAt ℝ u (axialShift a x))
    (hp : DifferentiableAt ℝ psi (axialShift a x)) :
    swirlEvolution lam (recenteredDrift lam C a) cu (recenter a u) (recenter a psi) x =
      recenter a (swirlEvolution lam C cu u psi) x := by
  simp only [swirlEvolution, partialDeriv_recenter a u _ x hu,
    partialDeriv_recenter a psi _ x hp, recenter, axialShift_radial, axialShift_axial,
    recenteredDrift]
  ring

/-- The vorticity residual transforms by the same axial recentering. -/
theorem vorticityEvolution_recenter (lam C cu a : ℝ) (u omega psi : ℝ^2 → ℝ) (x : ℝ^2)
    (hu : DifferentiableAt ℝ u (axialShift a x))
    (hw : DifferentiableAt ℝ omega (axialShift a x))
    (hp : DifferentiableAt ℝ psi (axialShift a x)) :
    vorticityEvolution lam (recenteredDrift lam C a) cu
        (recenter a u) (recenter a omega) (recenter a psi) x =
      recenter a (vorticityEvolution lam C cu u omega psi) x := by
  simp only [vorticityEvolution, partialDeriv_recenter a u _ x hu,
    partialDeriv_recenter a omega _ x hw, partialDeriv_recenter a psi _ x hp,
    recenter, axialShift_radial, axialShift_axial, recenteredDrift]
  ring

/-- S450–S457: the scalar right side splits into its linear term,
quadratic remainder, and corrected stationary reference residual. -/
theorem swirlEvolution_split (lam C cu dC dcu : ℝ) (u psi du dp : ℝ^2 → ℝ)
    (x : ℝ^2) (hu : DifferentiableAt ℝ u x) (hp : DifferentiableAt ℝ psi x)
    (hdu : DifferentiableAt ℝ du x) (hdp : DifferentiableAt ℝ dp x) :
    swirlEvolution lam (C + dC) (cu + dcu) (fun y ↦ u y + du y)
        (fun y ↦ psi y + dp y) x =
      linearSwirl lam C cu u psi du dp dC dcu x + nonlinearSwirl du dp dC dcu x
        + swirlEvolution lam C cu u psi x := by
  simp only [swirlEvolution, linearSwirl, nonlinearSwirl, partialDeriv_add hu hdu,
    partialDeriv_add hp hdp]
  ring

/-- S458–S465: the vorticity equation splits with the scalar source
`2u ∂z u`; no exact stationary evolution equation is assumed for the reference. -/
theorem vorticityEvolution_split (lam C cu dC dcu : ℝ)
    (u omega psi du dw dp : ℝ^2 → ℝ) (x : ℝ^2)
    (hu : DifferentiableAt ℝ u x) (hw : DifferentiableAt ℝ omega x)
    (hp : DifferentiableAt ℝ psi x) (hdu : DifferentiableAt ℝ du x)
    (hdw : DifferentiableAt ℝ dw x) (hdp : DifferentiableAt ℝ dp x) :
    vorticityEvolution lam (C + dC) (cu + dcu) (fun y ↦ u y + du y)
        (fun y ↦ omega y + dw y) (fun y ↦ psi y + dp y) x =
      linearVorticity lam C cu u omega psi du dw dp dC dcu x
        + nonlinearVorticity du dw dp dC dcu x
        + vorticityEvolution lam C cu u omega psi x := by
  simp only [vorticityEvolution, linearVorticity, nonlinearVorticity, partialDeriv_add hu hdu,
    partialDeriv_add hw hdw, partialDeriv_add hp hdp]
  ring

/-- The full scalar evolution equation yields the perturbation equation with
its corrected reference residual. `HasDerivAt` records the time derivative. -/
theorem swirl_perturbation_evolution (lam C cu offset dC dcu : ℝ)
    (u psi : ℝ^2 → ℝ) (du dp : ℝ^2 → ℝ → ℝ) (x : ℝ^2) (t : ℝ)
    (hu : DifferentiableAt ℝ u x) (hp : DifferentiableAt ℝ psi x)
    (hdu : DifferentiableAt ℝ (fun y ↦ du y t) x)
    (hdp : DifferentiableAt ℝ (fun y ↦ dp y t) x)
    (heq : HasDerivAt (fun s ↦ u x + du x s)
      (swirlEvolution lam (C + dC) (cu + offset + dcu)
        (fun y ↦ u y + du y t) (fun y ↦ psi y + dp y t) x) t) :
    HasDerivAt (fun s ↦ du x s)
      (linearSwirl lam C (cu + offset) u psi (fun y ↦ du y t) (fun y ↦ dp y t) dC dcu x
        + nonlinearSwirl (fun y ↦ du y t) (fun y ↦ dp y t) dC dcu x
        + correctedResidual offset u (swirlEvolution lam C cu u psi) x) t := by
  rw [swirlEvolution_split lam C (cu + offset) dC dcu u psi
    (fun y ↦ du y t) (fun y ↦ dp y t) x hu hp hdu hdp,
    swirlEvolution_corrected] at heq
  simpa using heq.sub_const (u x)

/-- The full vorticity evolution equation yields the perturbation equation
with the same amplitude correction as the scalar equation. -/
theorem vorticity_perturbation_evolution (lam C cu offset dC dcu : ℝ)
    (u omega psi : ℝ^2 → ℝ) (du dw dp : ℝ^2 → ℝ → ℝ) (x : ℝ^2) (t : ℝ)
    (hu : DifferentiableAt ℝ u x) (hw : DifferentiableAt ℝ omega x)
    (hp : DifferentiableAt ℝ psi x) (hdu : DifferentiableAt ℝ (fun y ↦ du y t) x)
    (hdw : DifferentiableAt ℝ (fun y ↦ dw y t) x)
    (hdp : DifferentiableAt ℝ (fun y ↦ dp y t) x)
    (heq : HasDerivAt (fun s ↦ omega x + dw x s)
      (vorticityEvolution lam (C + dC) (cu + offset + dcu)
        (fun y ↦ u y + du y t) (fun y ↦ omega y + dw y t)
        (fun y ↦ psi y + dp y t) x) t) :
    HasDerivAt (fun s ↦ dw x s)
      (linearVorticity lam C (cu + offset) u omega psi
        (fun y ↦ du y t) (fun y ↦ dw y t) (fun y ↦ dp y t) dC dcu x
        + nonlinearVorticity (fun y ↦ du y t) (fun y ↦ dw y t) (fun y ↦ dp y t) dC dcu x
        + correctedResidual offset omega (vorticityEvolution lam C cu u omega psi) x) t := by
  rw [vorticityEvolution_split lam C (cu + offset) dC dcu u omega psi
    (fun y ↦ du y t) (fun y ↦ dw y t) (fun y ↦ dp y t) x hu hw hp hdu hdw hdp,
    vorticityEvolution_corrected] at heq
  simpa using heq.sub_const (omega x)

/-- S467: the concrete signed stream operator is additive on `C²` germs.
At the axis this uses the selected regular extension `-4∂rr - ∂zz`;
identifying that extension with a radial limit requires the usual parity. -/
theorem signedElliptic_add (psi dp : ℝ^2 → ℝ) (x : ℝ^2)
    (hp : ContDiffAt ℝ 2 psi x) (hdp : ContDiffAt ℝ 2 dp x) :
    Euler.Calculus.signedElliptic Euler.Calculus.classicalAxisymmetricDifferential
        (fun y ↦ psi y + dp y) x =
      Euler.Calculus.signedElliptic Euler.Calculus.classicalAxisymmetricDifferential psi x
        + Euler.Calculus.signedElliptic Euler.Calculus.classicalAxisymmetricDifferential dp x := by
  have hp' := hp.differentiableAt (by norm_num)
  have hdp' := hdp.differentiableAt (by norm_num)
  dsimp only [Euler.Calculus.signedElliptic, Euler.Calculus.axisymmetricLaplacian,
    Euler.Calculus.classicalAxisymmetricDifferential, Euler.Calculus.profileDRR,
    Euler.Calculus.profileDZZ, Euler.Calculus.profileDR, Euler.Calculus.profileDZ,
    Euler.Calculus.regularizedProfileDROverR]
  unfold Euler.Calculus.profileDR Euler.Calculus.profileDZ
  simp only [partialDeriv_partialDeriv_add _ _ hp hdp, partialDeriv_add hp' hdp']
  split_ifs <;> ring

/-- S468–S469: exact elliptic compatibility of the reference and full fields
implies the homogeneous perturbation stream equation. Unlike the evolution
residuals, the reference elliptic residual is assumed to vanish. -/
theorem perturbation_stream_equation (psi dp : ℝ^2 → ℝ) (omega dw : ℝ)
    (x : ℝ^2) (hp : ContDiffAt ℝ 2 psi x) (hdp : ContDiffAt ℝ 2 dp x)
    (hfull : Euler.Calculus.signedElliptic Euler.Calculus.classicalAxisymmetricDifferential
      (fun y ↦ psi y + dp y) x = omega + dw)
    (href : Euler.Calculus.signedElliptic Euler.Calculus.classicalAxisymmetricDifferential
      psi x = omega) :
    Euler.Calculus.signedElliptic Euler.Calculus.classicalAxisymmetricDifferential dp x = dw := by
  rw [signedElliptic_add psi dp x hp hdp, href] at hfull
  exact add_left_cancel hfull

end Euler.Linearization
