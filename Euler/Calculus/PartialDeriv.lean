/-
Copyright (c) 2026 Robert Joseph George and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/

module

public import Euler.Calculus.Euclidean
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Coordinate derivatives

Coordinate derivatives are evaluations of Mathlib’s Fréchet derivative.
Product and chain rules carry differentiability hypotheses; mixed partials
commute under local `C²` regularity.
-/

@[expose] public section

variable {n : ℕ}

noncomputable section

/-- Partial derivative expression `∂ᵢ f(x)` for a Euclidean-domain map.

This is total because it is defined using Mathlib's `fderiv`; it does not itself assert that `f` is
differentiable at `x`. -/
def partialDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin n) (f : ℝ^n → E) (x : ℝ^n) : E :=
  fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ))

namespace Euler.Calculus

/-- Write `(∂[i] f) x` with `open scoped Euler.Calculus`. -/
scoped notation "∂[" i "] " f:arg => _root_.partialDeriv i f

end Euler.Calculus

/-- Taking a coordinate partial derivative of a Euclidean-valued map and then projecting to one
component agrees with differentiating that scalar component. -/
theorem partialDeriv_apply
    {m : ℕ} {u : ℝ^n → ℝ^m} {x : ℝ^n}
    (i : Fin n) (j : Fin m) (hu : DifferentiableAt ℝ u x) :
    partialDeriv i u x j = partialDeriv i (fun y ↦ u y j) x := by
  simpa [partialDeriv, Function.comp_def] using
    congrArg (fun L : ℝ^n →L[ℝ] ℝ ↦ L (EuclideanSpace.single i 1))
      (((EuclideanSpace.proj j).hasFDerivAt.comp x hu.hasFDerivAt).fderiv.symm)

/-- Partial derivative of a sum is the sum of partial derivatives. -/
theorem partialDeriv_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {i : Fin n} {f g : ℝ^n → E}
    {x : ℝ^n}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    partialDeriv (n := n) i (fun y ↦ f y + g y) x =
      partialDeriv (n := n) i f x + partialDeriv (n := n) i g x := by
  change fderiv ℝ (f + g) x (EuclideanSpace.single i (1 : ℝ)) = _
  rw [fderiv_add hf hg]
  rfl

/-- A constant scalar can be pulled through a partial derivative.

Unlike the sum rule, this identity needs no differentiability hypothesis: Mathlib's total
Fréchet derivative commutes with scalar multiplication even at points where the derivative is
defined to be zero. -/
theorem partialDeriv_const_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) {i : Fin n} {f : ℝ^n → E} {x : ℝ^n} :
    partialDeriv (n := n) i (fun y ↦ c • f y) x =
      c • partialDeriv (n := n) i f x := by
  change fderiv ℝ (c • f) x (EuclideanSpace.single i (1 : ℝ)) = _
  rw [congrFun (fderiv_const_smul_field c) x]
  rfl

/-- Partial derivative of a product under pointwise differentiability. -/
theorem partialDeriv_mul {i : Fin n} {f g : ℝ^n → ℝ}
    {x : ℝ^n}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    partialDeriv (n := n) i (fun y ↦ f y * g y) x =
      partialDeriv (n := n) i f x * g x +
        f x * partialDeriv (n := n) i g x := by
  rw [show (fun y ↦ f y * g y) = f * g by rfl]
  have happ := congrArg (fun L ↦ L (EuclideanSpace.single i (1 : ℝ))) (fderiv_mul hf hg)
  simpa [partialDeriv, add_apply, smul_apply, smul_eq_mul, mul_assoc, mul_left_comm,
    mul_comm, add_assoc, add_left_comm, add_comm] using happ

/-- Partial derivative of a negation is the negation of the partial derivative. -/
theorem partialDeriv_neg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {i : Fin n} {f : ℝ^n → E}
    {x : ℝ^n} :
    partialDeriv (n := n) i (-f) x = -partialDeriv (n := n) i f x := by
  simpa [partialDeriv] using
    congrArg (fun L ↦ L (EuclideanSpace.single i (1 : ℝ)))
      (fderiv_neg (𝕜 := ℝ) (f := f) (x := x))

/-- Partial derivative of a difference is the difference of partial derivatives. -/
theorem partialDeriv_sub
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {i : Fin n} {f g : ℝ^n → E}
    {x : ℝ^n}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    partialDeriv (n := n) i (fun y ↦ f y - g y) x =
      partialDeriv (n := n) i f x - partialDeriv (n := n) i g x := by
  change fderiv ℝ (f - g) x (EuclideanSpace.single i (1 : ℝ)) = _
  rw [fderiv_sub hf hg]
  rfl

/-- Partial derivative of a constant function. -/
@[simp]
theorem partialDeriv_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {i : Fin n} {x : ℝ^n} (c : E) :
    partialDeriv (n := n) i (fun _ ↦ c) x = 0 := by
  simp [partialDeriv]

/-- Equal Fréchet derivatives have equal values in every coordinate direction. -/
theorem partialDeriv_eq_of_fderiv_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ^n → E} {x : ℝ^n}
    (h : fderiv ℝ f x = fderiv ℝ g x) (i : Fin n) :
    partialDeriv i f x = partialDeriv i g x := by
  simpa only [partialDeriv] using
    congrArg (fun D : ℝ^n →L[ℝ] E ↦ D (EuclideanSpace.single i (1 : ℝ))) h

/-! ## Second coordinate derivatives -/

/-- Differentiating the Fréchet derivative and then evaluating on two coordinate
directions gives the corresponding mixed coordinate derivative. -/
theorem partialDeriv_partialDeriv_eq_fderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ^n → E} (i j : Fin n) {x : ℝ^n}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) x) :
    partialDeriv i (partialDeriv j f) x =
      fderiv ℝ (fderiv ℝ f) x
        (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) := by
  unfold partialDeriv
  rw [fderiv_clm_apply hf (differentiableAt_const _)]
  simp

/-- A mixed second coordinate derivative is the second Fréchet derivative evaluated on the
corresponding coordinate directions. -/
theorem partialDeriv_partialDeriv_eq_iteratedFDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ^n → E} (i j : Fin n)
    {x : ℝ^n} (hf : ContDiffAt ℝ 2 f x) :
    partialDeriv i (fun y ↦ partialDeriv j f y) x =
      iteratedFDeriv ℝ 2 f x
        ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single j (1 : ℝ)] := by
  rw [partialDeriv_partialDeriv_eq_fderiv i j
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt_one),
    iteratedFDeriv_two_apply]
  rfl

/-- Mixed second coordinate derivatives distribute over addition under local `C²` hypotheses. -/
theorem partialDeriv_partialDeriv_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i j : Fin n) {f g : ℝ^n → E} {x : ℝ^n}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    partialDeriv i
        (fun y ↦ partialDeriv j (fun z ↦ f z + g z) y) x =
      partialDeriv i (fun y ↦ partialDeriv j f y) x +
        partialDeriv i (fun y ↦ partialDeriv j g y) x := by
  rw [partialDeriv_partialDeriv_eq_iteratedFDeriv i j (hf.add hg),
    partialDeriv_partialDeriv_eq_iteratedFDeriv i j hf,
    partialDeriv_partialDeriv_eq_iteratedFDeriv i j hg]
  change (iteratedFDeriv ℝ 2 (f + g) x) _ = _
  rw [iteratedFDeriv_add_apply hf hg]
  rfl

/-- Mixed second coordinate derivatives distribute over subtraction under local `C²` hypotheses. -/
theorem partialDeriv_partialDeriv_sub
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i j : Fin n) {f g : ℝ^n → E} {x : ℝ^n}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    partialDeriv i
        (fun y ↦ partialDeriv j (fun z ↦ f z - g z) y) x =
      partialDeriv i (fun y ↦ partialDeriv j f y) x -
        partialDeriv i (fun y ↦ partialDeriv j g y) x := by
  rw [partialDeriv_partialDeriv_eq_iteratedFDeriv i j (hf.sub hg),
    partialDeriv_partialDeriv_eq_iteratedFDeriv i j hf,
    partialDeriv_partialDeriv_eq_iteratedFDeriv i j hg]
  change (iteratedFDeriv ℝ 2 (f - g) x) _ = _
  rw [iteratedFDeriv_sub_apply hf hg]
  rfl

/-! ## Commutation of smooth coordinate derivatives -/

/-- Pointwise Clairaut theorem for Euclidean coordinate partials. A `C²` germ at `x` is enough;
the result follows from Mathlib's symmetry theorem for the second Fréchet derivative rather than
being postulated as a PDE-specific rule. -/
theorem partialDeriv_partialDeriv_comm_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ^n → E} (i j : Fin n)
    {x : ℝ^n} (hf : ContDiffAt ℝ 2 f x) :
    partialDeriv i (fun y ↦ partialDeriv j f y) x =
      partialDeriv j (fun y ↦ partialDeriv i f y) x := by
  rw [partialDeriv_partialDeriv_eq_iteratedFDeriv i j hf,
    partialDeriv_partialDeriv_eq_iteratedFDeriv j i hf]
  exact
    (hf.isSymmSndFDerivAt (by norm_num)).iteratedFDeriv_cons
      (v := EuclideanSpace.single i (1 : ℝ))
      (w := EuclideanSpace.single j (1 : ℝ))

/-- Global `C²` functions have commuting Euclidean coordinate partials. -/
theorem partialDeriv_partialDeriv_comm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ^n → E} (i j : Fin n)
    (hf : ContDiff ℝ 2 f) (x : ℝ^n) :
    partialDeriv i (fun y ↦ partialDeriv j f y) x =
      partialDeriv j (fun y ↦ partialDeriv i f y) x :=
  partialDeriv_partialDeriv_comm_at i j hf.contDiffAt

/-- Function-valued form of coordinate commutation for a `C²` function. -/
theorem partialDeriv_partialDeriv_comm_of_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ^n → E} (i j : Fin n)
    (hf : ContDiff ℝ 2 f) :
    (fun x ↦ partialDeriv i (fun y ↦ partialDeriv j f y) x) =
      fun x ↦ partialDeriv j (fun y ↦ partialDeriv i f y) x := by
  funext x
  exact partialDeriv_partialDeriv_comm i j hf x

/-- A smooth function remains smooth after taking one concrete coordinate
partial derivative.  This is the regularity bridge needed when a product rule
is iterated rather than used only once. -/
theorem contDiff_top_partialDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {i : Fin n} {f : ℝ^n → E}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ partialDeriv (n := n) i f x) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

/-- Taking one coordinate derivative lowers a finite differentiability order by one. -/
theorem contDiff_partialDeriv_of_succ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} {i : Fin n} {f : ℝ^n → E}
    (hf : ContDiff ℝ (m + 1) f) :
    ContDiff ℝ m (fun x ↦ partialDeriv (n := n) i f x) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const
