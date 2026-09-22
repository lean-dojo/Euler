/-
Copyright (c) 2026 Robert Joseph George and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Euclidean coordinates

The meridian coordinates are ordered as radial, axial.
-/

@[expose] public section

/-- Real Euclidean space with `n` coordinates. -/
notation:arg "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

namespace Euler.Coordinates

/-- Radial coordinate on the meridian plane. -/
def meridianR (x : ℝ^2) : ℝ := x 0

/-- Axial coordinate on the meridian plane. -/
def meridianZ (x : ℝ^2) : ℝ := x 1

end Euler.Coordinates
