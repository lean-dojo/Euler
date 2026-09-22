module

public import Review.Definitions.Similarity.Derivation

/-! # Similarity image domain -/

@[expose] public noncomputable section

open Euler.Calculus Euler.Coordinates

namespace Euler

open Euler.Similarity

/-- Similarity coordinates reached from a physical space-time domain. -/
def travelingProfileDomain
    (lam singularTime : ℝ) (axialCenter : ℝ → ℝ)
    (Ωdom : Set (ℝ^2)) (I : Set ℝ) : Set (ℝ^2) :=
  (fun xt : (ℝ^2) × ℝ ↦
    similarityCoordinates lam singularTime axialCenter xt.1 xt.2) '' (Ωdom ×ˢ I)

end Euler

end
