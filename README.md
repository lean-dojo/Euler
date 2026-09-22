# Euler Singularity Analysis in Lean

In [this paper](https://arxiv.org/abs/2609.10867), the authors present evidence
for a stable singularity forming in finite time
for three-dimensional Euler flow on the whole space. A physics-informed neural
network produces an approximate self-similar profile with critical blowup rate
0.5, which the authors represent with splines for certification. Its transport
field provides evidence that linear damping may hold across the domain.
The authors also develop a nonlinear stability framework that reduces the
remaining analysis to finitely many explicit estimates and numerical constants. This repository formalizes selected derivations from the paper's main text and
appendices in Lean 4.

## Build

With Lean installed through elan, run these commands from this directory:

```sh
lake exe cache get
lake build
lake lint
```

Lean and mathlib are pinned to version 4.34.0.

## Formalized Results

[Euler.lean](Euler.lean) is the entry point.
Start with [the reduced axisymmetric operators](Euler/Equations/Reduced.lean),
then follow the arguments below. The `Calculus` folder contains derivative
lemmas shared by the coordinate and rescaling proofs.

| Appendix | Argument | Main file |
| --- | --- | --- |
| A, C | Substitute the similarity profile and obtain the stationary equations. | [Similarity/Traveling.lean](Euler/Similarity/Traveling.lean) |
| B | Change to `sinh` coordinates and handle the radial quotient at the axis. | [Coordinates/SinhCoordinates.lean](Euler/Coordinates/SinhCoordinates.lean), [Residuals.lean](Euler/Coordinates/Residuals.lean) |
| D | Derive the equations after changing space, time, and amplitude. | [Rescaling/Equations.lean](Euler/Rescaling/Equations.lean) |
| E | Compute how the weighted energy scales. | [EnergyScaling.lean](Euler/EnergyScaling.lean) |
| F | Check Euler scaling and the resulting curl and gradient formulas. | [Scaling.lean](Euler/Scaling.lean) |
| G | Expand around the reference profile and derive the perturbation equations. | [Linearization/Equations.lean](Euler/Linearization/Equations.lean), [Derivatives.lean](Euler/Linearization/Derivatives.lean), [Modulation.lean](Euler/Linearization/Modulation.lean) |
| I | Show that perturbation energy stays below a chosen radius. | [Stability.lean](Euler/Stability.lean) |
| J | Return to physical time and prove the clock, center, and curl estimates. | [PhysicalTime/Reconstruction.lean](Euler/PhysicalTime/Reconstruction.lean) |

## Notation

- `u`, `omega`, and `psi` mean reduced swirl, azimuthal vorticity, and streamfunction.
- `du`, `dw`, and `dp` mean perturbations of those fields, not derivatives.
  Radial and axial derivatives are written `Dr` and `Dz` in Appendix G.
- `eps`, `lam`, and `C` are the convection parameter, scaling exponent,
  and axial drift.

The rescaling convention is `A = 1/s_u`, `L = s_r`, and `A_omega = 1/s_omega`.
`partialDeriv` is mathlib's Fréchet derivative evaluated in a coordinate direction.

`Euler.Cartesian` contains the time-dependent fields on `ℝ³` and their operators:
`curl`, `divergence`, `gradient`, and `advection`. Spatial derivatives hold time fixed.
For example, `Euler.Cartesian.curl_scaledVelocity` gives the curl scaling law.

The Appendix I energy bound assumes the PDE evolution and five energy estimates.
The Appendix J reconstruction uses the stated scale laws, normalization, and regularity.

[formalization.yaml](formalization.yaml) lists the main theorems, axioms, and checks.

## Comparator

Comparator passed for all eight statements: the statements and definitions
matched, the axiom check passed, and Lean's kernel accepted the exported proofs.

[Review/README.md](Review/README.md) lists the checked statements.
To run the check again:

```sh
bash Review/run.sh
```

## Citation

Lean formalization by Robert Joseph George!

BibTeX for the [paper](https://arxiv.org/abs/2609.10867):

```bibtex
@misc{ganeshram2026stable,
  title         = {Stable Singularity of the {Euler} Equations on {$\mathbb{R}^3$}},
  author        = {Ganeshram, Adarsh and Duruisseaux, Valentin and Anandkumar, Anima},
  year          = {2026},
  eprint        = {2609.10867},
  archivePrefix = {arXiv},
  primaryClass  = {math.AP},
  doi           = {10.48550/arXiv.2609.10867},
  url           = {https://arxiv.org/abs/2609.10867}
}
```

Lean sources are licensed under [Apache 2.0](LICENSE).
