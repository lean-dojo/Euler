module

public import Review.Definitions.Calculus.Operators

/-! # Affine rescaling -/

@[expose] public noncomputable section

namespace Euler.Similarity

variable {V E : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A spatial dilation followed by a translation. -/
def affineDilation (scale : ℝ) (shift x : V) : V :=
  scale • x + shift

/-- The time-dependent affine similarity point `L(τ)x + b(τ)`. -/
def dynamicAffinePoint
    (spatialScale : ℝ → ℝ) (shift : ℝ → V)
    (x : V) (τ : ℝ) : V :=
  affineDilation (spatialScale τ) (shift τ) x

/-- Pull a time-dependent field back by an amplitude, an affine spatial map,
and a physical-time change. -/
def dynamicAffinePullback
    (field : V → ℝ → E)
    (amplitudeScale spatialScale : ℝ → ℝ)
    (shift : ℝ → V) (physicalTime : ℝ → ℝ)
    (x : V) (τ : ℝ) : E :=
  amplitudeScale τ •
    field (dynamicAffinePoint spatialScale shift x τ) (physicalTime τ)

end Euler.Similarity

end
