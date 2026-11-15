# The formalization's general mathematics

Part of the [audit report](../../REPORT.md).

- **[`Basic/`](../../Basic)** holds general mathematics that belongs in Mathlib ([`Basic/README.md`](../../Basic/README.md) says where):
  entrywise calculus for matrix-valued curves, the derivative of the matrix exponential, the
  fundamental theorem of calculus and Grönwall uniqueness for matrix ODEs; the action of `SL₂(ℝ)` on
  generalized circles; the area of a region bounded by a star-shaped closed curve and its convexity
  when the tangent turns one way; Dowker's theorem on least-area circumscribed polygons; the lattice
  tiling by a centrally symmetric hexagon; the angles and angle sum of convex polygons; Fejes Tóth's
  cell lemma for finite packings; the planar Tietze–Nakajima theorem; the existence of critical
  lattices; the structure of lattice-packed centrally symmetric convex bodies; the inverse of a
  function with positive derivative and periodic increments (the arclength of a closed curve);
  the fundamental theorem of calculus for absolutely continuous functions in the integral form of
  Carathéodory solutions, with interval integrals of functions with values in `ι → ℝ`; the sign
  of a cubic near `0⁺`, and the positive roots of real cubics for the sign patterns of Descartes's
  rule that Chapter 15 meets; the continuity of the least positive zero of a family of real
  functions and of a simple least positive root of a family of polynomials; the stability of
  fixed points of maps, with linearized stability (Lyapunov's first method for maps) and time
  reversal; the division of an analytic function by a power of a coordinate, and the analyticity
  of matrix exponentials and of the solutions of linear differential equations; the hyperbolic box
  at a fixed point; the mean value inequality for a map defined through an implicit root; and
  elementary bounds for the logarithm (`log s ≥ 2(s - 1)/(s + 1)`, `log(16/5) > 297/256`).
- **Three packages of their own** hold the general theory that this formalization needed and that
  others may import: OptimalControl
  ([github.com/vltanh/lean4-optimal-control](https://github.com/vltanh/lean4-optimal-control)),
  with control systems with Carathéodory trajectories (existence, uniqueness and differentiable
  dependence for measurable controls), Filippov's theorem and the existence of optimal controls
  (also under a closed state constraint, with a compact set of initial points and a closed endpoint
  relation), measurable selection, needle variations and the maximum principle; and FixedPoint
  ([github.com/vltanh/lean4-fixed-point](https://github.com/vltanh/lean4-fixed-point)), with
  Brouwer's fixed-point theorem; and StableManifold
  ([github.com/vltanh/lean4-stable-manifold](https://github.com/vltanh/lean4-stable-manifold)),
  with the stable manifold theorem for `Cⁿ` maps near a hyperbolic fixed point (`1 ≤ n ≤ ∞`), the
  local stable and unstable sets as graphs over the stable and unstable subspaces, by the
  Lyapunov–Perron method, and the hyperbolic splitting. The project requires OptimalControl and
  StableManifold at pinned commits, and OptimalControl requires FixedPoint.
- **Mathlib** lacks `det exp(A) = exp(tr A)` for matrices (a TODO in
  `Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean`), Jacobi's formula, Green's theorem for
  Jordan domains, the theory of regular elements of `𝔰𝔩₂`, any measurable selection theorem,
  Brouwer's fixed-point theorem, existence and uniqueness of Carathéodory solutions (its
  Picard–Lindelöf theorem needs continuity in time), any notion of stability of a fixed point
  of a map, with the linearized stability theorem, the two-sided continuity of the roots of a
  polynomial in its coefficients, the exact count of Descartes's rule for a real-rooted cubic,
  interval arithmetic, and the stable manifold theorem; each was a detour here, except interval
  arithmetic, which the analytic proofs of the computed facts made unnecessary. It
  also does not identify the bracket of its Lie algebra of left-invariant vector fields on
  `Mat₂(ℝ)ˣ` with the matrix commutator, so Propositions 3.6.1 and 6.4.1 are applied in matrix
  coordinates (Section 6).
- **Filippov's theorem** needs no smoothness of `f` in `q`: continuity, bounded velocities and the
  convexity hypotheses suffice, so the standing assumptions `hfq`, `hfq'` that the statement keeps
  from the source (Section 5) could be dropped, and the theorem holds for any finite-dimensional
  state space (`OptimalControl.ODE.ControlSystem`, in the OptimalControl package, is stated so).
  Its form with a state constraint, used in §6.1, needs no compact support either: continuity,
  bounded velocities and convexity on the constraint set suffice.
- **The computed facts.** The book's computations became exact arguments. In Chapters 13 and 15 the
  Mathematica eigenvalues of Lemma 13.5.5 became an exact Jacobian in `ℚ(√3, r_scale)` with sign
  changes of its characteristic polynomial at rational points (E68), and the coordinates and
  crossings of Remark 15.3.1 are certified in exact rational arithmetic (E75). In Chapters 14 and
  16 the four facts that the book reads off Mathematica plots needed neither interval enclosures on
  many boxes, feasible but slow, nor a validated integration of the unstable curve: at the switching root of the explicit Fuller–Poincaré map, exact identities and the signs
  of the switching functions decide every containment of Table 16.1, with no metric margin, and
  along an `e₂`-arc the Reinhardt flow has a closed form in which one step is an explicit map of four
  parameters, so that N4 is the invariance of an explicit region (E77, E78, E88). The Python
  reference in rigorous ball arithmetic ([`numerics/`](../../numerics)) found the margins and the regions that
  guided these proofs. Weierstrass preparation, which §16.4.2 invokes, turned out not to be needed
  (E90).
