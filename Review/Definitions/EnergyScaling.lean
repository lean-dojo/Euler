module

public import Review.Definitions.Similarity.Basic
public import Review.Definitions.Calculus.Operators
public import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-! # Weighted energy -/

@[expose] public noncomputable section

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

end Euler

end
