module

public import Review.Definitions.Calculus.Operators

/-! # Cartesian fields -/

@[expose] public noncomputable section

namespace Euler.Cartesian

/-- Package three scalar components as a Cartesian vector. -/
def vector (a b c : ℝ) : ℝ^3 :=
  WithLp.toLp 2 ![a, b, c]

/-- A time-dependent scalar field on `ℝ³`. -/
abbrev ScalarField := ℝ^3 → ℝ → ℝ

/-- A time-dependent vector field on `ℝ³`. -/
abbrev VectorField := ℝ^3 → ℝ → ℝ^3

/-- Time derivative of a vector field, componentwise in physical space. -/
def vectorTimeDeriv (u : VectorField) : VectorField :=
  fun x t ↦ WithLp.toLp 2 fun i ↦ deriv (fun τ ↦ u x τ i) t

/-- Euclidean spatial gradient at fixed time. -/
def gradient (f : ScalarField) : VectorField :=
  fun x t ↦ _root_.gradient (fun y : ℝ^3 ↦ f y t) x

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

end
