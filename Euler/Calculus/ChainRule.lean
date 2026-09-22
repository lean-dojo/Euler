/-
Copyright (c) 2026 Robert Joseph George and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/

module

public import Euler.Calculus.Operators

/-!
# Coordinate chain rules

First and second derivatives of a pullback are computed from the actual
Fréchet derivatives of the function and coordinate map.
-/

@[expose] public section

variable {n m : ℕ}

open scoped InnerProductSpace RealInnerProductSpace

/-- The derivative of coordinate `j` in coordinate direction `i` is the Kronecker delta. -/
theorem partialDeriv_coord (i j : Fin n)
    (x : ℝ^n) :
    partialDeriv (n := n) i (fun y ↦ y j) x = if i = j then 1 else 0 := by
  simpa [partialDeriv, EuclideanSpace.proj, eq_comm] using
    congrArg (fun L : ℝ^n →L[ℝ] ℝ ↦ L (EuclideanSpace.single i 1))
      (EuclideanSpace.proj j : ℝ^n →L[ℝ] ℝ).hasFDerivAt.fderiv

/-- Expand a Fréchet derivative in the Euclidean coordinate basis.

The codomain is an arbitrary real normed space.  This is the basis-free
directional derivative written in coordinates, and is therefore the common
calculus lemma behind scalar advection and vector-valued transport. -/
theorem fderiv_apply_eq_sum_smul_partialDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ^n → E) (x v : ℝ^n) :
    (fderiv ℝ f x) v =
      ∑ j : Fin n, v j • partialDeriv (n := n) j f x := by
  -- Expand the direction in the standard basis, then use linearity of the derivative.
  simpa [partialDeriv, EuclideanSpace.basisFun_apply] using
    (congrArg (fderiv ℝ f x) ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v)).symm

/-- Scalar specialization of `fderiv_apply_eq_sum_smul_partialDeriv`. -/
theorem fderiv_apply_eq_sum_partialDeriv_mul
    (f : ℝ^n → ℝ) (x v : ℝ^n) :
    (fderiv ℝ f x) v =
      ∑ j : Fin n, partialDeriv (n := n) j f x * v j := by
  simpa [smul_eq_mul, mul_comm] using fderiv_apply_eq_sum_smul_partialDeriv f x v

/-- Coordinate formula for scalar advection, requiring no differentiability hypothesis. -/
theorem advectiveDerivative_eq_sum_mul_partialDeriv
    (u : ℝ^n → ℝ^n) (f : ℝ^n → ℝ) (x : ℝ^n) :
    advectiveDerivative u f x =
      ∑ i : Fin n, u x i * partialDeriv (n := n) i f x := by
  simpa [advectiveDerivative, smul_eq_mul] using
    fderiv_apply_eq_sum_smul_partialDeriv f x (u x)

/-- Coordinate partial derivatives depend only on the germ of the function at the point. -/
theorem partialDeriv_congr_nhds (i : Fin n)
    {f g : ℝ^n → ℝ} {x : ℝ^n}
    (h : f =ᶠ[nhds x] g) :
    partialDeriv (n := n) i f x =
      partialDeriv (n := n) i g x := by
  exact partialDeriv_eq_of_fderiv_eq (h.fderiv_eq (𝕜 := ℝ)) i

/-- Taking one Euclidean coordinate derivative lowers finite local regularity by one order. -/
theorem contDiffAt_partialDeriv
    {f : ℝ^n → ℝ} {x : ℝ^n}
    (m : ℕ) (hf : ContDiffAt ℝ (m + 1) f x) (i : Fin n) :
    ContDiffAt ℝ m (fun y ↦ partialDeriv (n := n) i f y) x := by
  have hf' : ContDiffAt ℝ m (fderiv ℝ f) x :=
    hf.fderiv_right (m := (m : WithTop ℕ∞)) (by norm_num)
  exact hf'.clm_apply contDiffAt_const

/-- Coordinate chain rule for a real-valued function composed with a scalar Euclidean map. -/
theorem partialDeriv_comp_real
    (i : Fin n) {g : ℝ → ℝ} {u : ℝ^n → ℝ} {x : ℝ^n}
    (hg : DifferentiableAt ℝ g (u x)) (hu : DifferentiableAt ℝ u x) :
    partialDeriv (n := n) i (fun y ↦ g (u y)) x =
      partialDeriv (n := n) i u x * deriv g (u x) := by
  change partialDeriv (n := n) i (g ∘ u) x = _
  unfold partialDeriv
  rw [fderiv_comp x hg hu, ContinuousLinearMap.comp_apply, fderiv_eq_smul_deriv]
  simp [smul_eq_mul, mul_comm]

/-- First-order coordinate chain rule for a scalar function pulled back by a
Euclidean map. The formula is stated pointwise under local differentiability
assumptions. -/
theorem partialDeriv_comp
    (i : Fin n) (u : ℝ^n → ℝ)
    (Φ : ℝ^n → ℝ^n)
    (x : ℝ^n)
    (hu : DifferentiableAt ℝ u (Φ x)) (hΦ : DifferentiableAt ℝ Φ x) :
    partialDeriv (n := n) i (fun y ↦ u (Φ y)) x =
      ∑ j : Fin n,
        partialDeriv (n := n) j u (Φ x) *
          partialDeriv (n := n) i (fun y ↦ Φ y j) x := by
  change fderiv ℝ (u ∘ Φ) x (EuclideanSpace.single i 1) = _
  rw [fderiv_comp x hu hΦ, ContinuousLinearMap.comp_apply,
    fderiv_apply_eq_sum_partialDeriv_mul]
  exact Finset.sum_congr rfl fun j _ ↦ congrArg (_ * ·) (partialDeriv_apply i j hΦ)

/-- Second-order coordinate chain rule for a scalar function pulled back by a
`C²` Euclidean map. The first double sum is the Hessian of `u` contracted
against two chart derivatives; the second sum is the correction involving
the first derivatives of `u` and second derivatives of the chart. -/
theorem partialDeriv_partialDeriv_comp_at
    (i k : Fin n) (u : ℝ^n → ℝ)
    (Φ : ℝ^n → ℝ^n)
    (x : ℝ^n)
    (hu : ContDiffAt ℝ 2 u (Φ x)) (hΦ : ContDiffAt ℝ 2 Φ x) :
    partialDeriv (n := n) i
        (fun y ↦ partialDeriv (n := n) k (fun z ↦ u (Φ z)) y) x =
      (∑ j : Fin n, ∑ l : Fin n,
        partialDeriv (n := n) l
            (fun z ↦ partialDeriv (n := n) j u z) (Φ x) *
          partialDeriv (n := n) i (fun y ↦ Φ y l) x *
          partialDeriv (n := n) k (fun y ↦ Φ y j) x) +
      ∑ j : Fin n,
        partialDeriv (n := n) j u (Φ x) *
          partialDeriv (n := n) i
            (fun y ↦ partialDeriv (n := n) k (fun z ↦ Φ z j) y) x := by
  let A : Fin n → ℝ^n → ℝ := fun j y ↦ partialDeriv j u (Φ y)
  let B : Fin n → ℝ^n → ℝ := fun j y ↦ partialDeriv k (fun z ↦ Φ z j) y
  have huD (j : Fin n) : ContDiffAt ℝ 1 (fun z ↦ partialDeriv j u z) (Φ x) :=
    contDiffAt_partialDeriv 1 hu j
  have hΦcoord (j : Fin n) : ContDiffAt ℝ 2 (fun y ↦ Φ y j) x :=
    (EuclideanSpace.proj j : ℝ^n →L[ℝ] ℝ).contDiff.contDiffAt.comp x hΦ
  have hB (j : Fin n) : DifferentiableAt ℝ (B j) x :=
    (contDiffAt_partialDeriv 1 (hΦcoord j) k).differentiableAt (by norm_num)
  have hA (j : Fin n) : DifferentiableAt ℝ (A j) x :=
    ((huD j).differentiableAt (by norm_num)).comp x
      (hΦ.differentiableAt (by norm_num))
  have hfirst :
      (fun y ↦ partialDeriv k (fun z ↦ u (Φ z)) y) =ᶠ[nhds x]
        fun y ↦ ∑ j, A j y * B j y := by
    filter_upwards [hΦ.continuousAt.eventually (hu.eventually (by norm_num)),
      hΦ.eventually (by norm_num)] with y huy hΦy
    exact partialDeriv_comp k u Φ y
      (huy.differentiableAt (by norm_num)) (hΦy.differentiableAt (by norm_num))
  have hDA (j : Fin n) :
      partialDeriv i (A j) x =
        ∑ l, partialDeriv l (fun z ↦ partialDeriv j u z) (Φ x) *
          partialDeriv i (fun y ↦ Φ y l) x :=
    partialDeriv_comp i (fun z ↦ partialDeriv j u z) Φ x
      ((huD j).differentiableAt (by norm_num)) (hΦ.differentiableAt (by norm_num))
  -- Differentiate the first-order identity on a neighborhood, not just at one point.
  rw [partialDeriv_congr_nhds i hfirst]
  change fderiv ℝ (fun y ↦ ∑ j, A j y * B j y) x (EuclideanSpace.single i 1) = _
  rw [fderiv_fun_sum (A := fun j y ↦ A j y * B j y) (u := Finset.univ)
    (fun j _ ↦ (hA j).mul (hB j))]
  simp only [sum_apply]
  change (∑ j, partialDeriv i (fun y ↦ A j y * B j y) x) = _
  simp_rw [partialDeriv_mul (hA _) (hB _), hDA]
  simp only [Finset.sum_add_distrib, Finset.sum_mul, A, B]

/-- Global `C²` specialization of `partialDeriv_partialDeriv_comp_at`. -/
theorem partialDeriv_partialDeriv_comp
    (i k : Fin n) (u : ℝ^n → ℝ)
    (Φ : ℝ^n → ℝ^n)
    (x : ℝ^n)
    (hu : ContDiff ℝ 2 u) (hΦ : ContDiff ℝ 2 Φ) :
    partialDeriv (n := n) i
        (fun y ↦ partialDeriv (n := n) k (fun z ↦ u (Φ z)) y) x =
      (∑ j : Fin n, ∑ l : Fin n,
        partialDeriv (n := n) l
            (fun z ↦ partialDeriv (n := n) j u z) (Φ x) *
          partialDeriv (n := n) i (fun y ↦ Φ y l) x *
          partialDeriv (n := n) k (fun y ↦ Φ y j) x) +
      ∑ j : Fin n,
        partialDeriv (n := n) j u (Φ x) *
          partialDeriv (n := n) i
            (fun y ↦ partialDeriv (n := n) k (fun z ↦ Φ z j) y) x :=
  partialDeriv_partialDeriv_comp_at i k u Φ x hu.contDiffAt hΦ.contDiffAt
