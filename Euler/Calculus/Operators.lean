/-
Copyright (c) 2026 Robert Joseph George and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/

module

public import Euler.Calculus.PartialDeriv
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Laplacian

/-!
# Euclidean differential operators

The coordinate Laplacian agrees with Mathlib’s Laplacian under local `C²`
regularity. Scalar gradients use Mathlib’s gradient directly.
-/

@[expose] public section

variable {n : ℕ}

open scoped RealInnerProductSpace

/-- The `i`th coordinate of Mathlib's gradient is the `i`th partial derivative.

Both sides are totalized through `fderiv`; interpreting them as classical derivatives requires
the usual differentiability hypothesis. -/
@[simp]
theorem gradient_apply_eq_partialDeriv
    (f : ℝ^n → ℝ) (x : ℝ^n) (i : Fin n) :
    gradient f x i = partialDeriv (n := n) i f x := by
  rw [← EuclideanSpace.inner_basisFun_real (Fin n) (gradient f x) i,
    inner_gradient_left]
  simp only [partialDeriv, EuclideanSpace.basisFun_apply]

/-- Advective derivative of a field `f` along a velocity field `u`.

At `x`, this is the Fréchet derivative of `f` applied to the local velocity
`u x`. The codomain is arbitrary, so the same operator covers transported
scalars and vector-valued momentum equations. As with `fderiv`, this is a
total Lean term; PDE statements must supply differentiability when they use
it as a classical directional derivative. -/
noncomputable def advectiveDerivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : ℝ^n → ℝ^n) (f : ℝ^n → E) (x : ℝ^n) : E :=
  fderiv ℝ f x (u x)

/-- Divergence of a vector field, `∑ᵢ ∂ᵢ Fᵢ`.

Analytic use requires differentiability of the component functions. -/
noncomputable def divergence (F : ℝ^n → ℝ^n)
    (x : ℝ^n) : ℝ :=
  ∑ i : Fin n, partialDeriv (n := n) i (fun y ↦ F y i) x

/-- The iterated-coordinate Laplacian of a scalar function, `∑ᵢ ∂ᵢ(∂ᵢ f)`.

This is a total Lean term, but its totalization is not Mathlib's canonical
`Laplacian.laplacian`. They agree for `C²` functions by
`ContDiffAt.coordinate_laplacian_eq_laplacian`. -/
noncomputable def laplacian (f : ℝ^n → ℝ)
    (x : ℝ^n) : ℝ :=
  ∑ i : Fin n, partialDeriv (n := n) i (fun y ↦ partialDeriv (n := n) i f y) x

/-- Under local C² regularity, the coordinate Laplacian is mathlib's Laplacian. -/
theorem ContDiffAt.coordinate_laplacian_eq_laplacian
    {f : ℝ^n → ℝ} {x : ℝ^n} (hf : ContDiffAt ℝ 2 f x) :
    laplacian f x = Laplacian.laplacian f x := by
  -- Mathlib computes the trace in an orthonormal basis; use the coordinate basis.
  rw [congrFun
    (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
      (EuclideanSpace.basisFun (Fin n) ℝ)) x]
  unfold laplacian
  apply Finset.sum_congr rfl
  intro i _
  rw [partialDeriv_partialDeriv_eq_iteratedFDeriv i i hf]
  simp only [EuclideanSpace.basisFun_apply]

/-- The coordinate Laplacian is the divergence of Mathlib's gradient. -/
theorem laplacian_eq_divergence_gradient
    (f : ℝ^n → ℝ) (x : ℝ^n) :
    laplacian (n := n) f x = divergence (n := n) (gradient f) x := by
  simp only [laplacian, divergence, gradient_apply_eq_partialDeriv]

/-! ### Vector calculus identities -/

/-- The gradient of a sum is the sum of the gradients at a common differentiability point. -/
theorem gradient_add (f g : ℝ^n → ℝ) (x : ℝ^n)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    gradient (f + g) x = gradient f x + gradient g x := by
  simp only [gradient, fderiv_add hf hg, map_add]
