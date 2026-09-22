module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Moving center -/

@[expose] public noncomputable section

open MeasureTheory Set

open scoped Topology

namespace Euler.PhysicalTime

/-- Center velocity for an exponentially contracting physical spatial scale. -/
def travelingCenterVelocity (C : ℝ → ℝ) (sr₀ lam : ℝ) (t : ℝ) : ℝ :=
  -C t * sr₀ * Real.exp (-lam * t)

end Euler.PhysicalTime

end
