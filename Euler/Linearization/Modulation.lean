/-
Copyright (c) 2026 Robert Joseph George and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/
module

public import Euler.Linearization.Equations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Keeping the profile normalized at the origin

Here we formalize S484–S493 in Appendix G. Keeping the origin fixed and the
swirl value there constant determines the modulation equations.

The reference profile may have a nonzero residual. We correct the amplitude
rate using that residual, dividing by the nonzero reference value at the origin.
-/

@[expose] public noncomputable section

namespace Euler.Linearization

local notation "Dz" => partialDeriv (1 : Fin 2)

/-- At a fixed meridional origin, both transport contributions to S421 vanish.
This uses the reconstructed velocity, whose radial value is zero
and whose axial value is `2ψ(0)`. -/
theorem swirlEvolution_origin (lam C cu : ℝ) (u psi : ℝ^2 → ℝ)
    (hfixed : C + 2 * psi 0 = 0) :
    swirlEvolution lam C cu u psi 0 = (2 * Dz psi 0 + cu) * u 0 := by
  simp only [swirlEvolution, PiLp.zero_apply, mul_zero, zero_mul, sub_zero, zero_add,
    hfixed]
  ring

/-- S489–S491: the corrected reference amplitude rate is the rate determined
by its origin stream derivative. This derives the vanishing reference
contribution from the explicit residual correction. -/
theorem corrected_amplitude_rate_eq (lam C cu : ℝ) (u psi : ℝ^2 → ℝ)
    (hu : u 0 ≠ 0) (hfixed : C + 2 * psi 0 = 0) :
    cu + amplitudeOffset u (swirlEvolution lam C cu u psi) = -2 * Dz psi 0 := by
  unfold amplitudeOffset
  rw [swirlEvolution_origin lam C cu u psi hfixed]
  field_simp
  ring

/-- S484–S486: subtracting the reference fixed-origin condition gives
the axial-drift modulation. -/
theorem drift_modulation (C dC : ℝ) (psi dp : ℝ^2 → ℝ)
    (href : C + 2 * psi 0 = 0)
    (hfull : C + dC + 2 * (psi 0 + dp 0) = 0) :
    dC = -2 * dp 0 := by
  linarith

/-- S443: keeping the full scalar trace equal to the reference trace
forces the perturbation trace to vanish. -/
theorem perturbation_origin_zero (u : ℝ^2 → ℝ) (du : ℝ^2 → ℝ → ℝ)
    (htrace : ∀ t, u 0 + du 0 t = u 0) (t : ℝ) :
    du 0 t = 0 := by
  linarith [htrace t]

/-- S444: the perturbation's origin trace has zero time derivative because
the normalization makes that entire trace identically zero. -/
theorem perturbation_origin_time_derivative_zero
    (u : ℝ^2 → ℝ) (du : ℝ^2 → ℝ → ℝ)
    (htrace : ∀ s, u 0 + du 0 s = u 0) (t : ℝ) :
    deriv (du 0) t = 0 := by
  have h : du 0 = fun _ ↦ (0 : ℝ) :=
    funext (perturbation_origin_zero u du htrace)
  rw [h, deriv_const]

/-- The normalization `u(0,t) = ū(0)` gives a zero time derivative,
without assuming that derivative as an additional equation. -/
theorem origin_time_derivative_zero (u : ℝ^2 → ℝ → ℝ) (value : ℝ)
    (htrace : ∀ t, u 0 t = value) (t : ℝ) :
    deriv (fun s ↦ u 0 s) t = 0 := by
  have h : (fun s ↦ u 0 s) = fun _ ↦ value := funext htrace
  rw [h, deriv_const]

/-- S487–S493: the scalar origin equation and the two normalizations determine
the amplitude modulation. The raw reference residual is the stationary
scalar right side, and its correction is constructed by `amplitudeOffset`.
The time derivative of the full trace vanishes by normalization, not by a
separate assumption. -/
theorem amplitude_modulation (lam C cu dC dcu : ℝ)
    (u psi : ℝ^2 → ℝ) (du dp : ℝ^2 → ℝ → ℝ) (t : ℝ)
    (hu : u 0 ≠ 0)
    (href : C + 2 * psi 0 = 0)
    (hfull : C + dC + 2 * (psi 0 + dp 0 t) = 0)
    (htrace : ∀ s, u 0 + du 0 s = u 0)
    (hp : DifferentiableAt ℝ psi 0)
    (hdp : DifferentiableAt ℝ (fun y ↦ dp y t) 0)
    (heq : deriv (fun s ↦ u 0 + du 0 s) t =
      swirlEvolution lam (C + dC)
        (cu + amplitudeOffset u (swirlEvolution lam C cu u psi) + dcu)
        (fun y ↦ u y + du y t) (fun y ↦ psi y + dp y t) 0) :
    dcu = -2 * Dz (fun y ↦ dp y t) 0 := by
  have ht : deriv (fun s ↦ u 0 + du 0 s) t = 0 :=
    origin_time_derivative_zero (fun y s ↦ u y + du y s) (u 0) htrace t
  rw [ht, swirlEvolution_origin lam (C + dC)
    (cu + amplitudeOffset u (swirlEvolution lam C cu u psi) + dcu)
    (fun y ↦ u y + du y t) (fun y ↦ psi y + dp y t) hfull,
    partialDeriv_add hp hdp, htrace t, corrected_amplitude_rate_eq lam C cu u psi hu href] at heq
  have hfactor := (mul_eq_zero.mp heq.symm).resolve_right hu
  linarith

end Euler.Linearization
