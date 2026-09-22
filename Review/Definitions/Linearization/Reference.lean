module

public import Review.Definitions.Calculus.PartialDeriv

/-! # Amplitude correction -/

@[expose] public noncomputable section

namespace Euler.Linearization

local notation "Point" => EuclideanSpace ℝ (Fin 2)

/-- The amplitude offset in S452, computed from the raw scalar residual. -/
def amplitudeOffset (u rawResidual : Point → ℝ) : ℝ :=
  -rawResidual 0 / u 0

end Euler.Linearization

end
