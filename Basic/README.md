# Basic

General mathematics used by the formalization, independent of the paper's objects, filed by
field as Mathlib files it. Nothing here imports `External` or `SmoothedPolygons`.

| File | Content | Possible destination |
| --- | --- | --- |
| `Analysis/Calculus/MatrixEntrywise.lean` | entrywise derivatives and Lipschitz conditions for matrix-valued functions of a real variable; their algebra (sums, products, inverse, trace, `det` of `2 × 2`, transpose, chain rule), continuity entry by entry, and the bridge to `HasDerivAt` | Mathlib (`Mathlib/Analysis/Matrix/`, `Mathlib/Analysis/Calculus/Deriv/`) |
| `Analysis/Calculus/MatrixEntrywiseExp.lean` | the derivative of `t ↦ exp(tA)` for matrices, entry by entry, and identities for `exp(sA) exp(tA)` | Mathlib (`Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean`) |
| `Analysis/Calculus/MatrixFTC.lean` | fundamental theorem of calculus for matrix-valued curves with derivatives off a countable set; integral equations and back; zero derivative implies constant; Grönwall uniqueness for linear and affine matrix ODEs | Mathlib (`Mathlib/Analysis/ODE/`) |
| `Analysis/Complex/UpperHalfPlane/GeneralizedCircle.lean` | Möbius transformations of `SL(2, ℝ)` send generalized circles (`A\|z\|² + Bx + Cy + D = 0`) in the upper half-plane to generalized circles; rays through `0` | Mathlib (`Mathlib/Analysis/Complex/UpperHalfPlane/`) |
