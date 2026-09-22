module

public import Review.Definitions.Calculus.Euclidean
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! # Coordinate derivatives -/

@[expose] public noncomputable section

variable {n : ℕ}

/-- Partial derivative expression `∂ᵢ f(x)` for a Euclidean-domain map.

This is total because it is defined using Mathlib's `fderiv`; it does not itself assert that `f` is
differentiable at `x`. -/
def partialDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin n) (f : ℝ^n → E) (x : ℝ^n) : E :=
  fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ))

namespace Euler.Calculus

/-- Partial derivative in coordinate `i`. -/
scoped notation "∂[" i "] " f:arg => _root_.partialDeriv i f

end Euler.Calculus

end
