/-
Copyright (c) 2026 Robert Joseph George and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Energy estimates in Appendix I

Here we formalize S529–S541: differentiate the squared energy, then bound the
linear, nonlinear, and residual terms using the five estimates in the paper.

We use mathlib's inner product spaces and derivative rules. To represent the
paper's weighted L² fields, multiply each field by the square root of its weight.
`EnergyComponents.EvolvesOn` assumes differentiation in that space, not just
pointwise differentiation. Working with squared energy also covers zero energy.

Only upper bounds are needed for the high-order nonlinear and combined residual
terms. `PairingBounds.of_abs` obtains them from the absolute-value bounds in
S532–S533 when the coupling is nonnegative. The constants remain parameters.
-/

@[expose] public section

noncomputable section

open Set
open scoped Topology

namespace Euler.Stability

variable {ι κ V : Type*} [Fintype ι] [Fintype κ]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A finite family of perturbation rows and its three additive evolution terms. -/
structure EnergyComponents (ι V : Type*) where
  /-- Perturbation components, with their spatial weights already included. -/
  state : ι → ℝ → V
  /-- Linearized terms, including modulation when present. -/
  linear : ι → ℝ → V
  /-- Nonlinear terms. -/
  nonlinear : ι → ℝ → V
  /-- Additive forcing in `∂t state = linear + nonlinear + residual`. -/
  residual : ι → ℝ → V

/-- Sum of the squared Hilbert norms of a row family. -/
def EnergyComponents.normSq (u : EnergyComponents ι V) (t : ℝ) : ℝ := ∑ i, ‖u.state i t‖ ^ 2

/-- Pairing of one evolution term against the perturbation rows. -/
def EnergyComponents.pairing (u : EnergyComponents ι V) (term : ι → ℝ → V) (t : ℝ) : ℝ :=
  ∑ i, inner ℝ (term i t) (u.state i t)

/-- Strong component evolution on a time set, using derivatives within that set. -/
def EnergyComponents.EvolvesOn (u : EnergyComponents ι V) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, ∀ i, HasDerivWithinAt (u.state i)
    (u.linear i t + u.nonlinear i t + u.residual i t) s t

/-- The combined energy `E_k = √(E₀² + μ H_k²)` of S539. -/
def energy (μ : ℝ) (low : EnergyComponents ι V) (high : EnergyComponents κ V) (t : ℝ) : ℝ :=
  Real.sqrt (low.normSq t + μ * high.normSq t)

omit [InnerProductSpace ℝ V] in
/-- Squared component norms are nonnegative, also for an empty index set. -/
theorem EnergyComponents.normSq_nonneg (u : EnergyComponents ι V) (t : ℝ) : 0 ≤ u.normSq t :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

omit [InnerProductSpace ℝ V] in
/-- Nonnegativity of the combined energy. -/
theorem energy_nonneg (μ : ℝ) (low : EnergyComponents ι V) (high : EnergyComponents κ V) (t : ℝ) :
    0 ≤ energy μ low high t := Real.sqrt_nonneg _

omit [InnerProductSpace ℝ V] in
/-- The squared energy is the weighted sum of the component norm squares. -/
theorem energy_sq {μ : ℝ} (hμ : 0 ≤ μ)
    (low : EnergyComponents ι V) (high : EnergyComponents κ V) (t : ℝ) :
    energy μ low high t ^ 2 = low.normSq t + μ * high.normSq t :=
  Real.sq_sqrt (add_nonneg (low.normSq_nonneg t) (mul_nonneg hμ (high.normSq_nonneg t)))

/-- Differentiating a finite sum of squared norms pairs each equation with its state. -/
theorem EnergyComponents.hasDerivWithinAt_normSq {u : EnergyComponents ι V} {s : Set ℝ} {t : ℝ}
    (hu : ∀ i, HasDerivWithinAt (u.state i)
      (u.linear i t + u.nonlinear i t + u.residual i t) s t) :
    HasDerivWithinAt u.normSq
      (2 * (u.pairing u.linear t + u.pairing u.nonlinear t + u.pairing u.residual t)) s t := by
  change HasDerivWithinAt (fun r ↦ ∑ i, ‖u.state i r‖ ^ 2) _ s t
  simpa [EnergyComponents.pairing, inner_add_right, mul_add,
    Finset.sum_add_distrib, ← Finset.mul_sum, real_inner_comm] using
    HasDerivWithinAt.fun_sum (u := Finset.univ) (fun i _ ↦ (hu i).norm_sq)

/-- Twice the signed total work is the derivative of the squared combined energy. -/
theorem hasDerivWithinAt_energy_sq {μ : ℝ} (hμ : 0 ≤ μ)
    {low : EnergyComponents ι V} {high : EnergyComponents κ V} {s : Set ℝ} {t : ℝ}
    (hlow : ∀ i, HasDerivWithinAt (low.state i)
      (low.linear i t + low.nonlinear i t + low.residual i t) s t)
    (hhigh : ∀ j, HasDerivWithinAt (high.state j)
      (high.linear j t + high.nonlinear j t + high.residual j t) s t) :
    HasDerivWithinAt (fun r ↦ energy μ low high r ^ 2)
      (2 * (low.pairing low.linear t + μ * high.pairing high.linear t +
        (low.pairing low.nonlinear t + μ * high.pairing high.nonlinear t) +
        (low.pairing low.residual t + μ * high.pairing high.residual t))) s t := by
  have h := (EnergyComponents.hasDerivWithinAt_normSq hlow).add
    ((EnergyComponents.hasDerivWithinAt_normSq hhigh).const_mul μ)
  simp only [energy_sq hμ]
  convert h using 1
  ring

/-- The seven finite constants in S529–S535; no values or signs are built in. -/
structure EnergyConstants where
  /-- `Λ_L^low`, the low-order damping. -/
  lowDamping : ℝ
  /-- `Λ_L^high`, the high-order loss in the low-order estimate. -/
  highLoss : ℝ
  /-- `Λ_{D^α L}^low`, the low-order loss in the high-order estimate. -/
  lowLoss : ℝ
  /-- `Λ_{D^α L}^high`, the high-order damping. -/
  highDamping : ℝ
  /-- `Λ_{N,3}`, bounding the absolute low-order nonlinear pairing. -/
  nonlinearLow : ℝ
  /-- `Λ_{D^α N,3}`, the high-order nonlinear coefficient. -/
  nonlinearHigh : ℝ
  /-- `Λ_R`, bounding the combined residual pairing. -/
  residual : ℝ

/-- The stability coefficient in S534, using the same coupling as the energy. -/
def EnergyConstants.damping (c : EnergyConstants) (μ : ℝ) : ℝ :=
  min (c.lowDamping - μ * c.lowLoss) (c.highDamping - c.highLoss / μ)

/-- The combined cubic coefficient in S535. -/
def EnergyConstants.cubic (c : EnergyConstants) : ℝ := c.nonlinearLow + c.nonlinearHigh

/-- A sufficient signed generalization of the five estimates S529–S533 at one time. -/
structure PairingBounds (c : EnergyConstants) (μ : ℝ)
    (low : EnergyComponents ι V) (high : EnergyComponents κ V) (t : ℝ) : Prop where
  /-- S529. -/
  linear_low : low.pairing low.linear t ≤
    -c.lowDamping * low.normSq t + c.highLoss * high.normSq t
  /-- S530. -/
  linear_high : high.pairing high.linear t ≤
    -c.highDamping * high.normSq t + c.lowLoss * low.normSq t
  /-- S531, bounding the absolute low-order nonlinear pairing. -/
  nonlinear_low : |low.pairing low.nonlinear t| ≤ c.nonlinearLow * energy μ low high t ^ 3
  /-- Signed consequence of S532; the coupling multiplies the entire high-order sum. -/
  nonlinear_high : μ * high.pairing high.nonlinear t ≤
    c.nonlinearHigh * energy μ low high t ^ 3
  /-- Signed consequence of S533 for the combined low- and high-order forcing. -/
  residual : low.pairing low.residual t + μ * high.pairing high.residual t ≤
    c.residual * energy μ low high t

/-- The paper's five estimates S529–S533 imply `PairingBounds` for nonnegative coupling.
In S532 the coupling multiplies the absolute high-order sum; in S533 the absolute
value encloses the combined residual work. -/
theorem PairingBounds.of_abs {c : EnergyConstants} {μ t : ℝ}
    {low : EnergyComponents ι V} {high : EnergyComponents κ V} (hμ : 0 ≤ μ)
    (hlinear_low : low.pairing low.linear t ≤
      -c.lowDamping * low.normSq t + c.highLoss * high.normSq t)
    (hlinear_high : high.pairing high.linear t ≤
      -c.highDamping * high.normSq t + c.lowLoss * low.normSq t)
    (hnonlinear_low : |low.pairing low.nonlinear t| ≤
      c.nonlinearLow * energy μ low high t ^ 3)
    (hnonlinear_high : μ * |high.pairing high.nonlinear t| ≤
      c.nonlinearHigh * energy μ low high t ^ 3)
    (hresidual : |low.pairing low.residual t + μ * high.pairing high.residual t| ≤
      c.residual * energy μ low high t) :
    PairingBounds c μ low high t := by
  refine ⟨hlinear_low, hlinear_high, hnonlinear_low, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_left (le_abs_self _) hμ).trans hnonlinear_high
  · exact (le_abs_self _).trans hresidual

/-- The two linear estimates combine with the minimum coefficient in S534. -/
theorem PairingBounds.linear_pairing_le {c : EnergyConstants} {μ t : ℝ}
    {low : EnergyComponents ι V} {high : EnergyComponents κ V}
    (h : PairingBounds c μ low high t) (hμ : 0 < μ) :
    low.pairing low.linear t + μ * high.pairing high.linear t ≤
      -c.damping μ * energy μ low high t ^ 2 := by
  have hlow : c.damping μ ≤ c.lowDamping - μ * c.lowLoss := min_le_left _ _
  have hhigh : μ * c.damping μ ≤ μ * c.highDamping - c.highLoss := by
    have hh := mul_le_mul_of_nonneg_left
      (show c.damping μ ≤ c.highDamping - c.highLoss / μ from min_le_right _ _) hμ.le
    rwa [mul_sub, mul_div_cancel₀ _ hμ.ne'] at hh
  have hsum := add_le_add h.linear_low (mul_le_mul_of_nonneg_left h.linear_high hμ.le)
  have hl := mul_le_mul_of_nonneg_right hlow (low.normSq_nonneg t)
  have hh := mul_le_mul_of_nonneg_right hhigh (high.normSq_nonneg t)
  rw [energy_sq hμ.le]
  nlinarith only [hsum, hl, hh]

/-- S537–S541: signed linear, nonlinear and residual work give the cubic energy bound. -/
theorem PairingBounds.total_pairing_le {c : EnergyConstants} {μ t : ℝ}
    {low : EnergyComponents ι V} {high : EnergyComponents κ V}
    (h : PairingBounds c μ low high t) (hμ : 0 < μ) :
    low.pairing low.linear t + μ * high.pairing high.linear t +
        (low.pairing low.nonlinear t + μ * high.pairing high.nonlinear t) +
        (low.pairing low.residual t + μ * high.pairing high.residual t) ≤
      -c.damping μ * energy μ low high t ^ 2 +
        c.cubic * energy μ low high t ^ 3 + c.residual * energy μ low high t := by
  have hn := add_le_add ((le_abs_self _).trans h.nonlinear_low) h.nonlinear_high
  have ht := add_le_add (add_le_add (h.linear_pairing_le hμ) hn) h.residual
  simpa only [EnergyConstants.cubic, add_mul] using ht

/-- The energy inequality S541 follows from strong row evolution and the
five pairing bounds. At interior times this is the ordinary derivative inequality. -/
theorem energy_sq_derivative_bound {c : EnergyConstants} {μ t : ℝ} {s : Set ℝ}
    {low : EnergyComponents ι V} {high : EnergyComponents κ V}
    (hμ : 0 < μ) (hlow : low.EvolvesOn s) (hhigh : high.EvolvesOn s)
    (ht : t ∈ s) (h : PairingBounds c μ low high t) :
    ∃ v, HasDerivWithinAt (fun r ↦ energy μ low high r ^ 2) v s t ∧
      (1 / 2 : ℝ) * v ≤ -c.damping μ * energy μ low high t ^ 2 +
        c.cubic * energy μ low high t ^ 3 + c.residual * energy μ low high t := by
  refine ⟨_, hasDerivWithinAt_energy_sq hμ.le (hlow t ht) (hhigh t ht), ?_⟩
  simpa only [← mul_assoc, one_div_mul_cancel (by norm_num : (2 : ℝ) ≠ 0), one_mul] using
    h.total_pairing_le hμ

/-- At an interior time the derived inequality is exactly the ordinary derivative
formulation S541, with the factor `1/2` from differentiating the squared norm. -/
theorem half_energy_sq_deriv_le {c : EnergyConstants} {μ t : ℝ} {s : Set ℝ}
    {low : EnergyComponents ι V} {high : EnergyComponents κ V}
    (hμ : 0 < μ) (hlow : low.EvolvesOn s) (hhigh : high.EvolvesOn s)
    (ht : s ∈ 𝓝 t) (h : PairingBounds c μ low high t) :
    (1 / 2 : ℝ) * deriv (fun r ↦ energy μ low high r ^ 2) t ≤
      -c.damping μ * energy μ low high t ^ 2 +
        c.cubic * energy μ low high t ^ 3 + c.residual * energy μ low high t := by
  obtain ⟨v, hv, hbound⟩ := energy_sq_derivative_bound hμ hlow hhigh (mem_of_mem_nhds ht) h
  rwa [(hv.hasDerivAt ht).deriv]

end Euler.Stability
