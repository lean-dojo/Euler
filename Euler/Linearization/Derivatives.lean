/-
Copyright (c) 2026 Robert Joseph George and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/
module

public import Euler.Linearization.Equations
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-!
# Differentiating the perturbation equations

Here we formalize S475, S476, S482, and S483 in Appendix G. We apply the product
rule to the linear and nonlinear swirl terms, then interchange mixed partials
using local C² regularity. The modulation coefficients are constant in space
but may depend on time.
-/

@[expose] public noncomputable section

namespace Euler.Linearization

local notation "Dr" => partialDeriv (0 : Fin 2)
local notation "Dz" => partialDeriv (1 : Fin 2)

/-- S475, with the reference velocity derivatives expanded using S424. -/
def linearSwirlAxial (lam C cu : ℝ) (u psi du dp : ℝ^2 → ℝ)
    (dC dcu : ℝ) (x : ℝ^2) : ℝ :=
  -(lam * x 0 - x 0 * Dz psi x) * Dr (Dz du) x
    - (lam * x 1 + C + 2 * psi x + x 0 * Dr psi x) * Dz (Dz du) x
    + (2 * Dz psi x + cu - lam - (2 * Dz psi x + x 0 * Dr (Dz psi) x)) * Dz du x
    + x 0 * Dz (Dz psi) x * Dr du x + 2 * Dz (Dz psi) x * du x
    + (2 * u x + x 0 * Dr u x) * Dz (Dz dp) x
    + x 0 * Dr (Dz u) x * Dz dp x
    - x 0 * Dz u x * Dr (Dz dp) x - x 0 * Dz (Dz u) x * Dr dp x
    - 2 * Dz (Dz u) x * dp x - Dz (Dz u) x * dC + Dz u x * dcu

/-- S482, with the reference velocity derivatives expanded using S424. -/
def linearSwirlRadial (lam C cu : ℝ) (u psi du dp : ℝ^2 → ℝ)
    (dC dcu : ℝ) (x : ℝ^2) : ℝ :=
  -(lam * x 0 - x 0 * Dz psi x) * Dr (Dr du) x
    - (lam * x 1 + C + 2 * psi x + x 0 * Dr psi x) * Dr (Dz du) x
    + (2 * Dz psi x + cu - lam + Dz psi x + x 0 * Dr (Dz psi) x) * Dr du x
    - (3 * Dr psi x + x 0 * Dr (Dr psi) x) * Dz du x
    + 2 * Dr (Dz psi) x * du x
    + (2 * u x + x 0 * Dr u x) * Dr (Dz dp) x
    + (3 * Dr u x + x 0 * Dr (Dr u) x) * Dz dp x
    - x 0 * Dz u x * Dr (Dr dp) x
    - (3 * Dz u x + x 0 * Dr (Dz u) x) * Dr dp x
    - 2 * Dr (Dz u) x * dp x - Dr (Dz u) x * dC + Dr u x * dcu

/-- S476: the axial derivative of the quadratic scalar remainder. -/
def nonlinearSwirlAxial (du dp : ℝ^2 → ℝ) (dC dcu : ℝ) (x : ℝ^2) : ℝ :=
  x 0 * Dz (Dz dp) x * Dr du x + x 0 * Dz dp x * Dr (Dz du) x
    - (2 * Dz dp x + x 0 * Dr (Dz dp) x) * Dz du x
    - (dC + 2 * dp x + x 0 * Dr dp x) * Dz (Dz du) x
    + 2 * Dz du x * Dz dp x + 2 * du x * Dz (Dz dp) x + dcu * Dz du x

/-- S483: the radial derivative of the quadratic scalar remainder. -/
def nonlinearSwirlRadial (du dp : ℝ^2 → ℝ) (dC dcu : ℝ) (x : ℝ^2) : ℝ :=
  (Dz dp x + x 0 * Dr (Dz dp) x) * Dr du x
    + x 0 * Dz dp x * Dr (Dr du) x
    - (3 * Dr dp x + x 0 * Dr (Dr dp) x) * Dz du x
    - (dC + 2 * dp x + x 0 * Dr dp x) * Dr (Dz du) x
    + 2 * Dr du x * Dz dp x + 2 * du x * Dr (Dz dp) x + dcu * Dr du x

attribute [local simp] partialDeriv_add partialDeriv_sub partialDeriv_mul
  partialDeriv_neg partialDeriv_coord

/-- The expressions S475 and S482 are the derivatives of S456.
Only the four local `C²` germs are used; derivative additivity and mixed-partial
symmetry follow from the calculus lemmas under the stated regularity. -/
theorem linearSwirl_spatial_derivatives (lam C cu : ℝ) (u psi du dp : ℝ^2 → ℝ)
    (dC dcu : ℝ) (x : ℝ^2)
    (hu : ContDiffAt ℝ 2 u x) (hp : ContDiffAt ℝ 2 psi x)
    (hdu : ContDiffAt ℝ 2 du x) (hdp : ContDiffAt ℝ 2 dp x) :
    DifferentiableAt ℝ (linearSwirl lam C cu u psi du dp dC dcu) x ∧
      Dr (linearSwirl lam C cu u psi du dp dC dcu) x =
        linearSwirlRadial lam C cu u psi du dp dC dcu x ∧
      Dz (linearSwirl lam C cu u psi du dp dC dcu) x =
        linearSwirlAxial lam C cu u psi du dp dC dcu x := by
  have hu' := hu.differentiableAt (by norm_num)
  have hp' := hp.differentiableAt (by norm_num)
  have hdu' := hdu.differentiableAt (by norm_num)
  have hdp' := hdp.differentiableAt (by norm_num)
  have hur := (contDiffAt_partialDeriv 1 hu 0).differentiableAt (by norm_num)
  have huz := (contDiffAt_partialDeriv 1 hu 1).differentiableAt (by norm_num)
  have hpr := (contDiffAt_partialDeriv 1 hp 0).differentiableAt (by norm_num)
  have hpz := (contDiffAt_partialDeriv 1 hp 1).differentiableAt (by norm_num)
  have hdur := (contDiffAt_partialDeriv 1 hdu 0).differentiableAt (by norm_num)
  have hduz := (contDiffAt_partialDeriv 1 hdu 1).differentiableAt (by norm_num)
  have hdpr := (contDiffAt_partialDeriv 1 hdp 0).differentiableAt (by norm_num)
  have hdpz := (contDiffAt_partialDeriv 1 hdp 1).differentiableAt (by norm_num)
  have hr : DifferentiableAt ℝ (fun y : ℝ^2 ↦ y 0) x :=
    (EuclideanSpace.proj (0 : Fin 2) : ℝ^2 →L[ℝ] ℝ).differentiableAt
  have hz : DifferentiableAt ℝ (fun y : ℝ^2 ↦ y 1) x :=
    (EuclideanSpace.proj (1 : Fin 2) : ℝ^2 →L[ℝ] ℝ).differentiableAt
  refine ⟨?_, ?_, ?_⟩
  · unfold linearSwirl
    fun_prop
  · unfold linearSwirl linearSwirlRadial
    simp (discharger := fun_prop) [*]
    ring
  · have hurz := partialDeriv_partialDeriv_comm_at (1 : Fin 2) 0 hu
    have hprz := partialDeriv_partialDeriv_comm_at (1 : Fin 2) 0 hp
    have hdurz := partialDeriv_partialDeriv_comm_at (1 : Fin 2) 0 hdu
    have hdprz := partialDeriv_partialDeriv_comm_at (1 : Fin 2) 0 hdp
    unfold linearSwirl linearSwirlAxial
    simp (discharger := fun_prop) [*]
    ring

/-- The expressions S476 and S483 are the derivatives of S457,
under local `C²` regularity of the perturbations. -/
theorem nonlinearSwirl_spatial_derivatives (du dp : ℝ^2 → ℝ) (dC dcu : ℝ)
    (x : ℝ^2) (hdu : ContDiffAt ℝ 2 du x) (hdp : ContDiffAt ℝ 2 dp x) :
    DifferentiableAt ℝ (nonlinearSwirl du dp dC dcu) x ∧
      Dr (nonlinearSwirl du dp dC dcu) x = nonlinearSwirlRadial du dp dC dcu x ∧
      Dz (nonlinearSwirl du dp dC dcu) x = nonlinearSwirlAxial du dp dC dcu x := by
  have hdu' := hdu.differentiableAt (by norm_num)
  have hdp' := hdp.differentiableAt (by norm_num)
  have hdur := (contDiffAt_partialDeriv 1 hdu 0).differentiableAt (by norm_num)
  have hduz := (contDiffAt_partialDeriv 1 hdu 1).differentiableAt (by norm_num)
  have hdpr := (contDiffAt_partialDeriv 1 hdp 0).differentiableAt (by norm_num)
  have hdpz := (contDiffAt_partialDeriv 1 hdp 1).differentiableAt (by norm_num)
  have hr : DifferentiableAt ℝ (fun y : ℝ^2 ↦ y 0) x :=
    (EuclideanSpace.proj (0 : Fin 2) : ℝ^2 →L[ℝ] ℝ).differentiableAt
  refine ⟨?_, ?_, ?_⟩
  · unfold nonlinearSwirl
    fun_prop
  · unfold nonlinearSwirl nonlinearSwirlRadial
    simp (discharger := fun_prop) [*]
    ring
  · have hdurz := partialDeriv_partialDeriv_comm_at (1 : Fin 2) 0 hdu
    have hdprz := partialDeriv_partialDeriv_comm_at (1 : Fin 2) 0 hdp
    unfold nonlinearSwirl nonlinearSwirlAxial
    simp (discharger := fun_prop) [*]
    ring

end Euler.Linearization
