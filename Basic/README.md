# Basic

General mathematics used by the formalization, independent of the paper's objects, filed by
field as Mathlib files it. Nothing here imports [`External`](../External) or [`SmoothedPolygons`](../SmoothedPolygons).

| File | Content | Possible destination |
| --- | --- | --- |
| `Algebra/Module/ZLattice/PlaneCritical.lean` | Mahler's compactness theorem in the plane, as the existence of critical lattices: for an open `U ∋ 0`, if some lattice has no nonzero point in `U`, one of least covolume among such lattices exists; Lagrange–Gauss reduced bases; the lattice `ℤa + ℤb` and its covolume `\|det(a, b)\|` | Mathlib (`Mathlib/Algebra/Module/ZLattice/`) |
| `Analysis/Calculus/DerivInverse.lean` | the inverse of a real function with positive derivative and periodic increments `ℓ(θ + p) = ℓ(θ) + L` (an arclength, the lift of a degree-one circle map): a continuous increasing bijection, differentiable with the reciprocal derivative, with increments `Θ(t + L) = Θ(t) + p` | Mathlib (`Mathlib/Analysis/Calculus/Deriv/Inverse.lean`) |
| `Analysis/Calculus/MatrixEntrywise.lean` | entrywise derivatives and Lipschitz conditions for matrix-valued functions of a real variable; their algebra (sums, products, inverse, trace, `det` of `2 × 2`, transpose, chain rule), continuity entry by entry, and the bridge to `HasDerivAt` | Mathlib (`Mathlib/Analysis/Matrix/`, `Mathlib/Analysis/Calculus/Deriv/`) |
| `Analysis/Calculus/MatrixEntrywiseExp.lean` | the derivative of `t ↦ exp(tA)` for matrices, entry by entry, and identities for `exp(sA) exp(tA)` | Mathlib (`Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean`) |
| `Analysis/Calculus/MatrixFTC.lean` | fundamental theorem of calculus for matrix-valued curves with derivatives off a countable set; integral equations and back; zero derivative implies constant; Grönwall uniqueness for linear and affine matrix ODEs | Mathlib (`Mathlib/Analysis/ODE/`) |
| `Analysis/Complex/UpperHalfPlane/GeneralizedCircle.lean` | Möbius transformations of `SL(2, ℝ)` send generalized circles (`A\|z\|² + Bx + Cy + D = 0`) in the upper half-plane to generalized circles; rays through `0` | Mathlib (`Mathlib/Analysis/Complex/UpperHalfPlane/`) |
| `Analysis/Convex/StarCurve.lean` | the region swept from the origin by a star-shaped closed `C¹` curve: area `½∫det(γ, γ')` (Green's formula for such regions, by the change of variables `(r, t) ↦ rγ(t)`), compactness, interior, frontier; the polar angle turns once | Mathlib (`Mathlib/Analysis/Convex/`, `Mathlib/MeasureTheory/`) |
| `Analysis/Convex/StarCurveConvex.lean` | such a region is convex when the tangent turns counterclockwise (`γ'` Lipschitz, `det(γ', γ'') ≥ 0` a.e.) | Mathlib (`Mathlib/Analysis/Convex/`) |
| `Analysis/Convex/CircumscribedPolygon.lean` | least-area circumscribed `k`-gons `t_K(k)`; Dowker's theorem (`t_K` convex in `k`; symmetric version), by an alternating merge of normal angles; invariance under motions | Mathlib (`Mathlib/Analysis/Convex/`) |
| `Analysis/Convex/HexagonLattice.lean` | a centrally symmetric hexagon (or parallelogram) of finite area tiles the plane by a lattice (Voronoi argument); normal form of circumscribed symmetric hexagons | Mathlib (`Mathlib/Analysis/Convex/`, `Mathlib/Algebra/Module/ZLattice/`) |
| `Analysis/Convex/PolygonAngle.lean` | the angle of a convex polygon at a point, measured by area; polar-cone duality; the angle sum `(N − 2)π` by the normal fan; the local area formula | Mathlib (`Mathlib/Analysis/Convex/`) |
| `Analysis/Convex/CellDecomposition.lean` and `CellDecomposition/` | Fejes Tóth's cell lemma: `n` non-overlapping convex disks in a convex `m`-gon lie in non-overlapping convex cells with `Σ sides + 6 ≤ 6n + m`; maximal cells, pinwheel holes (Böröczky), polygon recognition, the side count by angle sums | Mathlib (`Mathlib/Analysis/Convex/`) |
| `Analysis/Convex/TietzeNakajima.lean` | a closed connected locally convex subset of the plane is convex | Mathlib (`Mathlib/Analysis/Convex/`) |
| `Analysis/Convex/BoundaryArc.lean` | the boundary curve of a convex body with `0` inside: the radial projection `x ↦ x / g_K(x)` (gauge) onto the boundary, arcs between boundary points (boundary points in the cone of their ends) and the intermediate value theorem on arcs; chords (the part of `K` beyond a chord lies in the cone of its ends); a segment through a boundary point lies on the boundary, a line meets the boundary twice unless it contains a boundary segment; in the plane, an arc without extreme inner points is a segment (Krein–Milman) | Mathlib (`Mathlib/Analysis/Convex/`) |
| `Analysis/Convex/LatticePacking.lean` | a centrally symmetric convex body free of half-lattice points lies in a maximal one, which is cut out by at most three strips (a parallelogram or a hexagon); a packed convex body has area at most the covolume (Blichfeldt) | Mathlib (`Mathlib/Algebra/Module/ZLattice/`) |
| `MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean` | the fundamental theorem of calculus for absolutely continuous functions, in the integral form `f t = f a + ∫ₐᵗ v` of Carathéodory solutions: an absolutely continuous function with derivative `v` almost everywhere is `f a + ∫ₐᵗ v`, and conversely; such a function has derivative `v` almost everywhere (Lebesgue's differentiation theorem, with values in a Banach space) and is continuous; absolute continuity by comparison of increments, and of a `C¹` function along such a curve | Mathlib (`Mathlib/MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean`) |
| `MeasureTheory/SpecificCodomains/Pi.lean` | the components of an interval integral of a function with values in `ι → ℝ`, `ι` finite, are the interval integrals of its components | Mathlib (`Mathlib/MeasureTheory/SpecificCodomains/Pi.lean`) |

The general theory of control systems moved to the OptimalControl package
(`https://github.com/vltanh/lean4-optimal-control`), which the project requires at the commit
pinned in [`lakefile.toml`](../lakefile.toml): control systems with Carathéodory trajectories, Filippov's
compactness theorem and the existence of optimal controls (formerly
`Analysis/ODE/ControlSystem.lean`), measurable selection (formerly
`MeasureTheory/MeasurableSelection.lean`), Lebesgue points, Carathéodory theory, flows and needle
variations (formerly `Analysis/ODE/Control/`), and supporting cones and Agrachev–Sachkov's Lemma
12.1 (formerly `Analysis/Convex/Cone/`), together with the maximum principle (formerly
`External/Pontryagin/`).
