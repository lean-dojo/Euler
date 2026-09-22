module

public import Review.Definitions.Calculus.PartialDeriv
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Laplacian

/-! # Transport and divergence -/

@[expose] public noncomputable section

variable {n : ℕ}

open scoped RealInnerProductSpace

/-- Advective derivative of a field `f` along a velocity field `u`.

At `x`, this is the Fréchet derivative of `f` applied to the local velocity
`u x`. The codomain is arbitrary, so the same operator covers transported
scalars and vector-valued momentum equations. As with `fderiv`, this is a
total Lean term; PDE statements must supply differentiability when they use
it as a classical directional derivative. -/
def advectiveDerivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : ℝ^n → ℝ^n) (f : ℝ^n → E) (x : ℝ^n) : E :=
  fderiv ℝ f x (u x)

/-- Divergence of a vector field, `∑ᵢ ∂ᵢ Fᵢ`.

Analytic use requires differentiability of the component functions. -/
def divergence (F : ℝ^n → ℝ^n)
    (x : ℝ^n) : ℝ :=
  ∑ i : Fin n, partialDeriv (n := n) i (fun y ↦ F y i) x

end
