module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Perturbation energy -/

@[expose] public noncomputable section

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

end Euler.Stability

end
