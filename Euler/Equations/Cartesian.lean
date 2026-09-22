/-
Copyright (c) 2026 Robert Joseph George and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/

module

public import Euler.Calculus.Operators

/-!
# Cartesian Euler operators

Here we define velocity, curl, transport, and the momentum residual in Cartesian
coordinates. Spatial derivatives hold time fixed. The scaling results in
Appendix F use these definitions.
-/

@[expose] public section

noncomputable section

namespace Euler.Cartesian

/-- Package three scalar components as a Cartesian vector. -/
def vector (a b c : ℝ) : ℝ^3 :=
  WithLp.toLp 2 ![a, b, c]

/-- First component of `vector a b c`. -/
@[simp]
theorem vector_apply_zero (a b c : ℝ) :
    vector a b c 0 = a := by
  simp [vector]

/-- Second component of `vector a b c`. -/
@[simp]
theorem vector_apply_one (a b c : ℝ) :
    vector a b c 1 = b := by
  simp [vector]

/-- Third component of `vector a b c`. -/
@[simp]
theorem vector_apply_two (a b c : ℝ) :
    vector a b c 2 = c := by
  simp [vector]

/-- A time-dependent scalar field on `ℝ³`. -/
abbrev ScalarField := ℝ^3 → ℝ → ℝ

/-- A time-dependent vector field on `ℝ³`. -/
abbrev VectorField := ℝ^3 → ℝ → ℝ^3

/-- Time derivative of a scalar field at a fixed spatial point. -/
def scalarTimeDeriv (f : ScalarField) : ScalarField :=
  fun x t ↦ deriv (fun τ ↦ f x τ) t

/-- Time derivative of a vector field, componentwise in physical space. -/
def vectorTimeDeriv (u : VectorField) : VectorField :=
  fun x t ↦ WithLp.toLp 2 fun i ↦ deriv (fun τ ↦ u x τ i) t

/-- Euclidean spatial partial derivative `∂ᵢ f` at fixed time. -/
def spaceDeriv (i : Fin 3) (f : ScalarField) : ScalarField :=
  fun x t ↦ partialDeriv (n := 3) i (fun y : ℝ^3 ↦ f y t) x

/-- Euclidean spatial gradient at fixed time. -/
def gradient (f : ScalarField) : VectorField :=
  fun x t ↦ _root_.gradient (fun y : ℝ^3 ↦ f y t) x

/-- Fixed-time spatial velocity gradient, with entry `(i,j) = ∂ⱼuᵢ`. -/
def velocityGradient
    (u : VectorField) : ℝ^3 → ℝ → EuclideanSpace ℝ (Fin 3 × Fin 3) :=
  fun x t ↦ WithLp.toLp 2 fun ij ↦
    partialDeriv ij.2 (fun y ↦ u y t ij.1) x

/-- Coordinate formula for the fixed-time spatial velocity gradient. -/
@[simp]
theorem velocityGradient_apply
    (u : VectorField) (x : ℝ^3) (t : ℝ) (i j : Fin 3) :
    velocityGradient u x t (i, j) =
      partialDeriv j (fun y ↦ u y t i) x := by
  simp [velocityGradient, PiLp.toLp_apply]

/-- Euclidean spatial divergence at fixed time. -/
def divergence (u : VectorField) : ScalarField :=
  fun x t ↦ _root_.divergence (n := 3) (fun y : ℝ^3 ↦ u y t) x

/-- Curl in three dimensions, written with Euclidean partial derivatives. -/
def curl (u : VectorField) : VectorField :=
  fun x t ↦
    vector
      (partialDeriv (n := 3) 1 (fun y : ℝ^3 ↦ u y t 2) x
        - partialDeriv (n := 3) 2 (fun y : ℝ^3 ↦ u y t 1) x)
      (partialDeriv (n := 3) 2 (fun y : ℝ^3 ↦ u y t 0) x
        - partialDeriv (n := 3) 0 (fun y : ℝ^3 ↦ u y t 2) x)
      (partialDeriv (n := 3) 0 (fun y : ℝ^3 ↦ u y t 1) x
        - partialDeriv (n := 3) 1 (fun y : ℝ^3 ↦ u y t 0) x)

/-- `(u · ∇)v`, written componentwise using Euclidean partial derivatives. -/
def advection (u v : VectorField) : VectorField :=
  fun x t ↦ WithLp.toLp 2 fun i ↦
    ∑ j : Fin 3, u x t j
      * partialDeriv (n := 3) j (fun y : ℝ^3 ↦ v y t i) x

/--
Momentum residual for full 3D incompressible Euler:

`∂t u + (u · ∇)u = -∇p`.
-/
def momentumResidual (u : VectorField) (p : ScalarField) : VectorField :=
  fun x t ↦ WithLp.toLp 2 fun i ↦ vectorTimeDeriv u x t i + advection u u x t i
    + gradient p x t i

end Euler.Cartesian
