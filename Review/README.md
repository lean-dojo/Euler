# Comparator

All eight statements below passed Comparator. The statement,
definition, and axiom checks passed, and Lean's kernel accepted the proofs.
The run took about two minutes. `lake build` and `lake lint` also passed.

| Appendix | Checked statement |
| --- | --- |
| A/C | The similarity fields satisfy the physical equations exactly when the profile satisfies the stationary equations. |
| B | The elliptic operator transforms correctly under `sinh` coordinates. |
| D | Dynamic rescaling gives the rescaled equations and the scale-rate identity. |
| E | Physical energy equals `(T-t)^(5 lambda - 2)` times profile energy. |
| F | Euler's momentum and incompressibility equations are preserved by the stated scaling. |
| G | The origin normalization and evolution equation give `delta_cu = -2 partial_z(delta_psi)(0)`. |
| I, Theorem S3 | Under the five energy estimates and strict stability margin, energy initially below `delta` remains below it on the existence interval. |
| J, Proposition S10 | Under the scale laws, normalization, and regularity assumptions, physical time has a finite limit, the center converges, and the axial curl grows without bound. |

The full statements are in [Challenge.lean](Challenge.lean).
[comparator.json](../comparator.json) selects the eight theorems.
Their definitions are collected by [Definitions.lean](Definitions.lean), with
separate files in [Definitions/](Definitions/) matching the `Euler/` module layout.

## Run

From the repository root:

```sh
lake build
lake lint
bash Review/run.sh
```

A successful Comparator run ends with:

```text
Lean default kernel accepts the solution
Your solution is okay!
```
