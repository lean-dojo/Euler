/-
Copyright (c) 2026 Robert Joseph George and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/
module

public import Euler.Stability.Barrier
public import Euler.Stability.Weighted
import Mathlib.Tactic.Linarith

/-!
# Stability in Appendix I

Here we formalize Theorem S3 in Appendix I, pp. 104–105. Starting from the
evolution equations and the five estimates S529–S533, we show that the
perturbation energy stays below the chosen radius.

The three low-order components are `(δω, ∂r δu, ∂z δu)`. At order `k`,
`MixedDerivativeIndex k` lists their derivatives `∂r^(k-j) ∂z^j` for `0 ≤ j ≤ k`.
For `k = 4`, this gives fifteen high-order components. Each weighted L² component
includes the square root of its time-independent weight.

The proof differentiates the squared energy to obtain S541. At the proposed
radius, S536 makes its derivative negative, so the energy cannot cross that
radius. The result holds on the given existence interval; the PDE evolution,
regularity, and estimates are hypotheses.
-/

@[expose] public section

noncomputable section

open Set

namespace Euler.Stability

/-- Three rows, each with all `k + 1` mixed derivatives of total order `k`. -/
abbrev MixedDerivativeIndex (k : ℕ) := Fin 3 × Fin (k + 1)

/-- Radial and axial derivative orders attached to the mixed index. -/
def mixedOrder (k : ℕ) (j : Fin (k + 1)) : ℕ × ℕ := (k - j.val, j.val)

/-- Every indexed mixed derivative has precisely the requested total order. -/
theorem mixedOrder_fst_add_snd (k : ℕ) (j : Fin (k + 1)) :
    (mixedOrder k j).1 + (mixedOrder k j).2 = k := by
  simp only [mixedOrder]
  omega

/-- Every pair of radial/axial orders summing to `k` occurs exactly once. -/
theorem existsUnique_mixedOrder {k nr nz : ℕ} (h : nr + nz = k) :
    ∃! j : Fin (k + 1), mixedOrder k j = (nr, nz) := by
  refine ⟨⟨nz, by omega⟩, ?_, ?_⟩
  · apply Prod.ext <;> simp only [mixedOrder]
    omega
  · intro j hj
    apply Fin.ext
    exact congrArg Prod.snd hj

/-- There are three low rows and `3(k+1)` high rows, hence fifteen high rows for `k=4`. -/
theorem card_mixedDerivativeIndex (k : ℕ) :
    Fintype.card (MixedDerivativeIndex k) = 3 * (k + 1) := by
  simp only [MixedDerivativeIndex, Fintype.card_prod, Fintype.card_fin]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Theorem S3: under S529–S536, energy initially below `δ` remains below `δ`.

The estimates are needed only while the energy is at most `δ`. `EvolvesOn`
requires derivatives in the normed space, so applying this theorem to the PDE
requires proving that its weighted components have those derivatives.
The conclusion is restricted to the given existence interval. -/
theorem energy_lt_of_initial_lt {k : ℕ} {c : EnergyConstants} {μ δ a : ℝ} {s : Set ℝ}
    {low : EnergyComponents (Fin 3) V} {high : EnergyComponents (MixedDerivativeIndex k) V}
    (hs : OrdConnected s) (ha : a ∈ s)
    (hlow : low.EvolvesOn s) (hhigh : high.EvolvesOn s)
    (hbound : ∀ t ∈ s, energy μ low high t ≤ δ → PairingBounds c μ low high t)
    (hμ : μ ∈ Ioc (0 : ℝ) 1) (_hdamping : 0 < c.damping μ) (hδ : 0 < δ)
    (hmargin : c.cubic * δ + c.residual / δ < c.damping μ)
    (hinitial : energy μ low high a < δ) :
    ∀ t ∈ s, a ≤ t → energy μ low high t < δ := by
  intro t ht hat
  have hinterval : Icc a t ⊆ s := hs.out ha ht
  have hcontinuous : ContinuousOn (fun r ↦ energy μ low high r ^ 2) (Icc a t) := by
    intro r hr
    exact ((hasDerivWithinAt_energy_sq hμ.1.le (hlow r (hinterval hr))
      (hhigh r (hinterval hr))).mono hinterval).continuousWithinAt
  have hinitialSq : energy μ low high a ^ 2 < δ ^ 2 :=
    pow_lt_pow_left₀ hinitial (energy_nonneg μ low high a) (by norm_num)
  have hball := strict_sublevel_invariant hcontinuous hinitialSq (fun r hr hcontact ↦ by
    have hrmem : r ∈ s := hinterval ⟨hr.1.le, hr.2⟩
    have henergy : energy μ low high r = δ := by
      nlinarith only [hcontact, energy_nonneg μ low high r, hδ]
    obtain ⟨v, hv, hrate⟩ := energy_sq_derivative_bound hμ.1 hlow hhigh hrmem
      (hbound r hrmem henergy.le)
    rw [henergy] at hrate
    refine ⟨v, ?_, hv.mono hinterval⟩
    -- At E = δ, multiply S536 by δ² to make the derivative bound negative.
    have hscaled := mul_lt_mul_of_pos_right
      ((div_lt_iff₀ hδ).mp
        (show c.residual / δ < c.damping μ - c.cubic * δ by linarith)) hδ
    nlinarith only [hrate, hscaled])
  have hsquare := hball t ⟨hat, le_rfl⟩
  nlinarith only [hsquare, hδ, energy_nonneg μ low high t]

end Euler.Stability
