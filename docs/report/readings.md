# How the formalization reads the paper

Part of the [audit report](../../REPORT.md).

- **Packings and densities (§2.1).** The book's disks `B_r` are Euclidean disks ([`euclidDisk`](../../Challenge.lean#L323);
  Mathlib's balls on `Fin 2 → ℝ` are squares). A packing is a set of convex disks with pairwise
  disjoint interiors; congruent copies are images under Euclidean motions, reflections included.
  The density ratios are taken in `[0, ∞]`; a density exists when the upper and lower densities are
  finite and equal; `δ(K)` and `δ_L(K)` are suprema of real numbers, over nonempty sets bounded by
  `1`. A lattice is a discrete `ℤ`-submodule of `ℝ²` spanning it, and its determinant is Mathlib's
  covolume, shown equal to `|det|` of any basis ([`definition2_3_2`](../../SmoothedPolygons/Ch2/Mahler.lean#L58)).
- **Critical lattices and hexagons (§2.3).** A critical lattice is admissible with determinant
  `Δ(K)` (E6). The critical hexagons of §2.2 are the least-area circumscribed centrally symmetric
  hexagons ([`IsLeastAreaHexagon`](../../SmoothedPolygons/Ch2/Reinhardt.lean#L66), compared among strictly convex hexagons centred at the origin,
  which gives the same minimum); those of Definition 2.3.8 come from Mahler's construction, and
  Theorem 2.3.9 identifies them. Two notions of irreducibility appear: Definition 2.3.5's (every
  boundary point on a critical lattice) and Mahler's original one (no proper subdomain with the same
  `Δ`), used in the proof of Lemma 2.2.5. In Mahler's notion the subdomains are read as centrally
  symmetric convex disks ([`External.MahlerIrreducible.IsIrreducible`](../../External/MahlerIrreducible.lean#L105)); Mahler admits all star domains, and
  paper A's Lemma 13 shows that for a convex `K` the two readings agree (Section 2). The remark after
  Definition 2.3.5, that the two notions agree, is proved for every `K ∈ 𝔎_ccs`
  ([`isIrreducible_iff_mahlerIrreducible`](../../SmoothedPolygons/Ch2/Mahler.lean#L99), from Mahler's Lemma 3,
  [`External.mahler_irreducible_iff`](../../External/MahlerIrreducible/Lemma3.lean#L367)).
- **Statements about `K_min` (§2.2–2.4).** Lemma 2.2.7's "the midpoints advance monotonically and
  continuously" is formalized with polar-angle lifts; Lemma 2.4.2 is read literally (any `C⁰`
  multi-curve on the boundary); Lemmas 2.4.5 and 2.4.6 assume the positive orientation of §2.4,
  without which they are false (time reversal). Remark 2.2.4's hyperbolic arc is the level set of a
  product of signed distances to the two adjacent edge lines. Problem 2.4.8 is a predicate on `K`.
- **The area formula (§3.2).** [`eqn_cost`](../../SmoothedPolygons/Ch3/AreaFormula.lean#L205) assumes, besides the balanced pair and `σ_j = g s_j*`,
  that `σ_j(t + t_f) = σ_{j+1}(t)`, which the book derives with its normalization of the
  parametrization (TeX ~3140–3160); without it the formula fails (a circle traversed at varying
  speed).
- **Matrices and the plane.** `2 × 2` real matrices are `Matrix (Fin 2) (Fin 2) ℝ`; points of the
  plane are `Fin 2 → ℝ`. Mathlib puts no norm on matrices, so derivatives and Lipschitz conditions
  of matrix-valued curves are taken entry by entry ([`Basic/Analysis/Calculus/MatrixEntrywise.lean`](../../Basic/Analysis/Calculus/MatrixEntrywise.lean)),
  which agrees with any norm. The trace form is `⟨X, Y⟩ = tr(XY)`; `R` is written out and shown
  equal to `exp(Jπ/3)` ([`definition3_1_5`](../../SmoothedPolygons/Ch3/StateDynamics.lean#L337)).
- **Controls.** `u = (u₀, u₁, u₂)` is `Fin 3 → ℝ`; the vertices `e₁, e₂, e₃` are `vertex 0`,
  `vertex 1`, `vertex 2`, and the switching functions `χ_ij` are indexed by `Fin 3` accordingly.
  `U_T` is defined as in Definition 3.3.3 ([`controlSimplex`](../../Challenge.lean#L137)).
- **Solutions of differential equations.** The state and costate equations with a measurable
  control are solved in Carathéodory's sense ([`IsIntegralCurve`](../../Challenge.lean#L187)): each entry of the solution is the
  indefinite integral of the corresponding entry of an integrable right-hand side. Results whose
  book proofs differentiate classically are stated with `HasDerivWithinAt` on closed intervals.
- **The state space.** By Theorem 4.4.1, a state trajectory ([`IsStateTrajectory`](../../Challenge.lean#L195)) takes values in
  `SL₂(ℝ) × 𝔥*`: `X(t)` is traceless with `det X = 1` and satisfies the star inequalities.
- **Pontryagin extremals.** The book defines a Pontryagin extremal as a lift satisfying the
  conditions of the maximum principle (§6.2), with the full costate `p = (Λ₁, Λ₂)`;
  [`IsPontryaginExtremal`](../../Challenge.lean#L214) states them in the reduced variables `(Λ₁, Λ_R)` of Problem 6.7.1: the
  costate equations; `Λ₁, Λ_R` traceless with `Λ_R ⊥ X`; `λ_cost ≤ 0` constant;
  `(λ_cost, Λ₁, Λ_R) ≠ 0` at every time; maximality of the control and `H = 0` for almost every
  time; and the transversality conditions of §6.6. The nontriviality condition is imposed on the
  reduced costate, because on the full costate it admits the spurious lift `λ_cost = 0`, `Λ₁ = 0`,
  `Λ₂ = X` of every trajectory (E21). "The Hamiltonian `H(q, p, u*)` vanishes identically" is read
  almost everywhere, as Agrachev and Sachkov state it ((12.15)) and as the maximum principle gives
  it for measurable controls.
- **The maximum principle (§6.2, §6.6).** [`External.pontryagin_maximum_principle`](../../External/Pontryagin.lean#L80) is stated on an
  open subset of a finite-dimensional real normed space, for a compact control set (the book's
  "closed"), dynamics and cost `C¹` in the state with `∂f/∂q` jointly continuous (the book's
  "smooth", with Agrachev and Sachkov's (10.4)), and strong local minimizers (more general than
  the global minimizers the book considers). Since `SL₂(ℝ)` is not open in `Mat₂(ℝ)`, the
  principle is applied, instead of on the book's manifold `SL₂(ℝ) × 𝔰𝔩₂(ℝ)`, on the
  open set `GL₂⁺(ℝ) × C` of `Mat₂(ℝ) × 𝔰𝔩₂(ℝ)` (a departure, Section 7) ([`matrixDomain`](../../SmoothedPolygons/Ch6/MatrixSystem.lean#L118)), `C` the open cone of the star
  inequalities, on which the dynamics are smooth, with `g(0) = I₂` and `det X(0) = 1` (§3.5) among
  the boundary conditions; `det g` and `det X` are first integrals, so the admissible pairs that
  satisfy the boundary conditions are the admissible trajectories of Problem 3.6.2 (E21). The book
  writes Hamilton's equations for the maximized Hamiltonian `H*`
  (eqn:hamiltons-equations); the formalization, as Agrachev and Sachkov, writes the adjoint
  equation of the control-dependent Hamiltonian `H(·, ·, u(t))` at the optimal control, in
  integral form, with a Lipschitz covector. The book states transversality in separated form, `p(0)`
  annihilating the tangent space of an initial manifold and `p(t_f)` that of a terminal one, and
  then says that for the Reinhardt problem "the initial and terminal submanifolds coincide after
  rotation by `R`"; the formalization uses the mixed form of Agrachev and Sachkov's Theorem 12.5,
  `(q(0), q(t_f)) ∈ N` with `(-p(0), p(t_f)) ⊥ T N`, which on the variations
  `(δX(0), δX(t_f)) = (Y, R⁻¹YR)` with `⟨X(0), Y⟩ = 0` gives `Λ_R(t_f) = R⁻¹Λ_R(0)R`
  ([`covectorΛR_transversality`](../../SmoothedPolygons/Ch6/MatrixCostate.lean#L477)). For `Λ₁` transversality gives nothing, since `g` is fixed at both ends;
  the condition `Λ₁(t_f) = R⁻¹Λ₁(0)R` of (6.6.1) comes from `g(t_f) = R` by Corollary 6.5.3, as
  Remark 6.6.1 says, and the formalization takes that route ([`remark6_6_1_lambda1`](../../SmoothedPolygons/Ch6/PeriodicExtension.lean#L86)). The costates of a covector `p` at `(g, X)` are `Λ₁ = pg` made traceless (the
  `g`-part of `p` as a matrix by the trace pairing, then the left trivialization of Proposition
  3.6.1, [`covectorΛ₁`](../../SmoothedPolygons/Ch6/MatrixCostate.lean#L65)), `Λ₂` the `X`-part identified with `𝔰𝔩₂(ℝ)` by the trace form, and
  `Λ_R = [Λ₂, X]` ([`covectorΛR`](../../SmoothedPolygons/Ch6/MatrixCostate.lean#L69)).
- **Propositions 3.6.1 and 6.4.1 in §6.2.** The trivialization of Proposition 3.6.1 and the
  identity `⟨p, gX⟩ = ⟨Λ₁, X⟩` of Proposition 6.4.1 are checked in matrix coordinates, where the
  identity is the associativity `tr(p(gX)) = tr((pg)X)`
  ([`controlHamiltonian_matrix_eq_fullHamiltonian`](../../SmoothedPolygons/Ch6/MatrixCostate.lean#L135)), rather than obtained from [`proposition6_4_1`](../../SmoothedPolygons/Ch6/LeftInvariant.lean#L91), which is
  stated for Mathlib's Lie groups: Mathlib makes `Mat₂(ℝ)ˣ` a Lie group only through a local
  choice of normed algebra, and does not identify the bracket of left-invariant vector fields with
  the matrix commutator, which the invariance hypothesis of the proposition needs.
- **Remark 6.6.1.** A "transversal trajectory" is a Pontryagin extremal on `[0, t_f]`, and the
  "periodic solution of the lifted trajectories" is a solution on `[0, ∞)` of the state–costate
  system with the conditions of the maximum principle ([`IsStateCostateSolution`](../../SmoothedPolygons/Ch6/PeriodicExtension.lean#L54): Problem 6.7.1
  without the boundary conditions) on every `[0, nt_f]`, equal to the extremal on `[0, t_f]`, whose
  control is rotated (its coordinates permuted cyclically) from one period to the next (E38).
- **Proposition 6.5.1.** "Hamilton's equations" are the hypotheses of [`proposition6_5_1`](../../SmoothedPolygons/Ch6/Hamiltonian.lean#L319): on
  `T*𝔰𝔩₂(ℝ)`, `X' = δH/δΛ₂` and `Λ₂' = -δH/δX`; on the cotangent bundle of the group, in canonical
  coordinates `(g, p)` of `T*GL₂(ℝ)` (the covector `p` acting by `v ↦ tr(p v)`), `g' = ∂H/∂p` and
  `p' = -∂H/∂g`, with `H` depending on `(g, p)` through the left-trivialized costate `Λ₁ = pg`. The
  Euler–Arnold equation that the book cites is then proved ([`External.euler_arnold`](../../External/EulerArnold.lean#L72)). The conclusion
  is the derivative of `Λ₁` and of `Λ_R` at `t`. In §6.2 these hypotheses are the adjoint
  equation of the maximum principle, at almost every time, with the momentum
  `p - (tr(pg)/2)g⁻¹` (whose left trivialization is `Λ₁`)
  ([`hasDerivAt_covectorΛ_of_adjoint`](../../SmoothedPolygons/Ch6/MatrixCostate.lean#L323)).
- **The smoothed `(6k+2)`-gon.** The book specifies it by its control mode sequence (eqn:3k+1), the
  switching time (eqn:t1), the initial point `z₀ = i y₀` with `4/(3y₀² + 1) = 2 cos θ_k`, and
  `g(0) = I₂`. The Challenge states Theorem 7.5.6 for every state trajectory with this control and
  these initial values, and proves that there is one; the library shows it is unique
  ([`polygon_trajectory_unique`](../../SmoothedPolygons/Ch7/SmoothedPolygon.lean#L226)) and equal to the spline of §7.4 ([`polygonG`](../../SmoothedPolygons/Ch7/Polygon.lean#L287), [`polygonX`](../../SmoothedPolygons/Ch7/Polygon.lean#L281)).
- **Bang-bang.** [`IsBangBang`](../../Challenge.lean#L234) asks that the control take values in the extreme points of `U_T`;
  the clause "with discontinuous switching" of Definition 7.3.2 describes the switching and is not
  a condition.
- **Area and density.** The smoothed `(6k+2)`-gon is the region swept from the origin by the
  spline's curve, extended periodically ([`smoothedPolygonDisk`](../../SmoothedPolygons/Ch7/SmoothedPolygonDisk.lean#L508)); it is a balanced disk in circle
  representation (E15), its area is the cost by the area formula of §3.2, and its greatest packing
  density is its area divided by `√12` (E12, through Theorem 2.2.2 and Fejes Tóth's theorem).
- **Tangent spaces.** The tangent space of an adjoint orbit (Lemma 4.2.3) is the set of velocities
  of curves in the orbit ([`curveTangentSpace`](../../SmoothedPolygons/Ch4/AdjointOrbit.lean#L295)); the cotangent space of Lemma 6.8.1 is the dual of
  `𝔰𝔩₂/ℝX`.
- **Proposition 3.6.1.** "`TG ≅ G × 𝔤`" is formalized as the bijections given by left translation,
  fiberwise linear isomorphisms; smoothness of the trivialization is not stated (the book's proof
  does not address it).
- **Proposition 3.1.9.** The book defines the reparameterized `X̃` by `g̃' = g̃X̃` with
  `g̃ = g ∘ s`, and derives `X̃ = s' X(s)` by the chain rule; the statement takes `X̃` in that
  derived form.
- **Lemma 6.8.1.** The cotangent space `T*_X O_X` is the dual of `T_X O_X ≅ 𝔰𝔩₂(ℝ)/ℝX`
  (Lemma 4.2.3); the formal statement is `X^⊥ = {[W, X]}` and `X^⊥ ≅ (𝔰𝔩₂(ℝ)/ℝX)*` by the trace
  form, for every nonzero traceless `X`. In the book `X = Φ(z) ∈ O_J` (TeX 5296–5301), so `X ≠ 0`
  is implicit.
- **Theorem 6.8.3.** "The ODE for `Λ_R` is transformed to the ODE `ν' = -dH`" (TeX 5386–5388),
  whose omitted proof calls the two "equivalent", is formalized in the direction of the statement:
  along a solution of the costate equation for `Λ_R`, `ν = T*Φ(-Λ_R)` satisfies `ν' = -dH`. (The
  book says that §6.8 is not used elsewhere.)
- **Lemma 3.1.8.** "The boundary is parametrized by a `C¹` multi-curve" is read as in §2.4: `σ`
  is a `C¹` multi-curve on `[0, t_f]` (Definition 2.4.1) whose points lie on `∂K` and whose arcs
  cover `∂K`, and its six curves are regular (E34). The lines along which `σ_{i±1}` move are given
  by a point and a direction; the conclusion is that they are not parallel and that `σ_i([a, b])`
  lies on one hyperbola `det(d₁, x - p₁)·det(d₂, x - p₂) = c` with `c ≠ 0`, the form of Remark
  2.2.4's hyperbolas. The proof measures areas by the signed (shoelace) area, for which the book's
  area bookkeeping holds without showing that the hexagon `H_K(t)` cut out by the tangent lines is
  convex; that `H_K(t)` is a critical hexagon, as the book calls it, is not needed, only that its
  edge midpoints are the `σ_j(t)` and its area is `√12`.
- **The ideal vertices (§4.6).** `ℝℙ¹` is Mathlib's `OnePoint ℝ`, on which `GL₂(ℝ)` acts by linear
  fractional transformations, and the dihedral group is the subgroup of `GL₂(ℝ)` generated by `R`
  and `S` ([`dihedralGroup`](../../SmoothedPolygons/Ch4/IdealVertices.lean#L48)). The formal statements give the action of the generators on
  `±1/√3` and `+∞` ([`dihedral_smul_idealVertices`](../../SmoothedPolygons/Ch4/IdealVertices.lean#L59)) and show that every element permutes these three
  points ([`dihedral_permutes_idealVertices`](../../SmoothedPolygons/Ch4/IdealVertices.lean#L89)).
- **The compactification (Chapter 5).** Points of the upper half-plane are pairs `(x, y)` with
  `y > 0`, as in the star domain ([`starDomain`](../../SmoothedPolygons/Ch4/StarDomain.lean#L22)); a real `2 × 2` matrix acts by its linear fractional
  transformation written in coordinates ([`lftAct`](../../SmoothedPolygons/Ch5/Compactification.lean#L110)), and the reflection `S` of §4.6 by
  `(x, y) ↦ (-x, y)` ([`reflAct`](../../SmoothedPolygons/Ch5/Compactification.lean#L117)). The horoballs and the "half-planes" (regions bounded by a line or
  a circle) of Definition 5.0.1 are open sets of such pairs ([`horoballAtInfty`](../../SmoothedPolygons/Ch5/Compactification.lean#L125),
  [`edgeHalfPlane`](../../SmoothedPolygons/Ch5/Compactification.lean#L129) and their images under `R` and `R²`), `𝔥**` is [`truncatedStarDomain`](../../SmoothedPolygons/Ch5/Compactification.lean#L135), and
  [`truncatedStarDomain_eq`](../../SmoothedPolygons/Ch5/Compactification.lean#L536) writes it by explicit inequalities. The fundamental domain of the proof of
  Theorem 5.0.2 is read as the sector `{x ≥ 0, (x - 1/√3)² + y² ≥ 4/3}` ([`fundamentalDomain`](../../SmoothedPolygons/Ch5/Compactification.lean#L143);
  E40, E45).
- **Lemmas 5.0.3–5.0.5 and Theorem 5.0.6.** The hexagon `H_K(z)` is given by its vertices `p_j`
  (eqn:hex-vertex with `det X = 1`, [`hexVertex`](../../SmoothedPolygons/Ch5/Hexagon.lean#L105)) and the points `q_j` of TeX 4131 ([`hexExtVertex`](../../SmoothedPolygons/Ch5/Hexagon.lean#L111));
  areas are Lebesgue measure. The exterior triangle `T₂^ext = △p₀q₀p₁` is represented by its
  reflection `△p₃q₃p₄`, which has the same area ([`outerTriangle`](../../SmoothedPolygons/Ch5/Hexagon.lean#L122)). "The critical hexagon" of `K`
  in Lemma 5.0.3 and Theorem 5.0.6 is read as a centrally symmetric hexagon of least area
  containing `K` ([`IsLeastAreaHexagon`](../../SmoothedPolygons/Ch2/Reinhardt.lean#L66), the critical hexagons of §2.2), which Theorem 2.3.9 identifies
  with the critical hexagon of Definition 2.3.8 (E42). "`z` constructed from the boundary
  parameterization of `K` at the multi-point `{s_j*}`" is read as `σ_j = g s_j*` with
  `g(0)⁻¹g'(0) = Φ(z)`.
- **Lemma 5.0.7 and Theorem 5.0.2.** `area_i` and `δ` are functions of pairs `(x, y)`
  ([`areaFn`](../../SmoothedPolygons/Ch5/Hexagon.lean#L138), [`densityBound`](../../SmoothedPolygons/Ch5/Hexagon.lean#L144)), and `I_i area_i` is `area_i` times the indicator of `h_i` ([`hRegion`](../../SmoothedPolygons/Ch5/Hexagon.lean#L133));
  parts (1) and (2) are stated on the book's open interval `0 < x < 1/√3` and proved on
  `[0, 1/√3)`. Theorem 5.0.2 takes a balanced pair with its boundary trajectory (`σ_j = g s_j*`,
  `σ_j(t + t_f) = σ_{j+1}(t)`, `X = g⁻¹g'`) and a curve `z` in `𝔥*` with `X = Φ ∘ z`. "The cost of
  the trajectory is strictly greater than the area of the smoothed octagon" is stated with the
  cost equal to `area(K)`, and "Hence `K` is not a global minimizer" as two conclusions: the
  smoothed octagon has a smaller greatest packing density (so `K` is not a `K_min`), and `(g, X)`
  is not a global minimizer of Problem 3.6.2 for any control. The dihedral reduction of the proof
  ("everything ... has been equivariant") is read as the invariance of the density bound `δ` under
  the dihedral group acting on `𝔥*` ([`densityBound_dihedralAct`](../../SmoothedPolygons/Ch5/Theorem502.lean#L149)); no action on disks or trajectories
  is needed.
- **Filippov's theorem (Theorem 6.1.1).** The state space is `ℝⁿ` instead of a manifold (for `f`
  smooth with compact support, the manifold case follows by an embedding in some `ℝᴺ`); a
  trajectory is a Carathéodory solution driven by a measurable control; "the support of `f` is a
  compact subset of `M × U`" is read as `f(q, u) = 0` for `q` outside a compact set; the attainable
  sets are those at time `T` and up to time `T`; and "an optimal control exists" is stated for fixed
  and for free terminal time (the book applies it with free terminal time `t_f ≤ π/3`, TeX 3207,
  4583), under the convexity of the extended velocity sets (E35).
- **Winding number (§3.5, §6.1).** An admissible trajectory has winding number one
  ([`IsWindingOne`](../../SmoothedPolygons/Ch6/Winding.lean#L82)) when the continuous angle `θ` of `σ₀(t) = g(t)s₀*` with `θ(0) = 0` ends at
  `θ(t_f) = π/3`, rather than `π/3 + 2πm` with `m ≥ 1`; the closed curve `σ₀` on `[0, 6t_f]`
  (extended by `g(t + t_f) = g(t)R`) then winds once around the origin. The converse of Problem
  3.6.2 (E15) is stated with that extension `G` of `g` to `ℝ`: `σ_j = G s_j*` is the multi-curve of
  a balanced pair `(K, σ)` in circle representation, and `area(K)` is the cost.
- **The existence of a minimizer and `K_min` (§6.1).** "An optimal control exists" is read as the
  existence of a global minimizer of Problem 3.6.2 ([`IsReinhardtMinimizer`](../../Challenge.lean#L392): an admissible
  trajectory whose cost is at most that of every admissible trajectory, of any terminal time).
  `K_min` is a centrally symmetric convex disk of least greatest packing density `δ_min`
  ([`IsWorstDisk`](../../Challenge.lean#L413), [`minimaxDensity`](../../Challenge.lean#L408)). The identification of the global minimizers with `K_min` (E47)
  is read as two statements: every `K_min` has an image under a linear map of positive determinant
  that is a balanced disk in circle representation whose boundary trajectory is a global
  minimizer; and every balanced disk whose boundary trajectory is a global minimizer is a `K_min`,
  with `δ_min = cost/√12`.
- **Definition 6.3.1 and Proposition 6.4.1.** They are stated on Mathlib's real Lie groups
  (`LieGroup I ∞ G`): `f(g, u)` is a tangent vector at `g`, `TL_h` is the tangent map `mfderiv`,
  the Lie algebra `𝔤` is `GroupLieAlgebra I G`, a cotangent vector at `g` is a linear form on
  `T_g G`, and "invariant" means invariant under the adjoint action. The left trivialization
  `p̃ = T*L_{g⁻¹}(p)` is part of the statement ([`leftTrivCovector`](../../SmoothedPolygons/Ch6/LeftInvariant.lean#L72)): the Hamiltonian
  `⟨p̃, f(g, u)⟩_*` at `p̃`, for `p ∈ 𝔤` identified with `⟨p, ·⟩`, is `⟨p, f(e, u)⟩`. That these
  coordinates cover `T*G` (Proposition 3.6.1) is not needed for the identity.
- **Remark 7.5.2.** "Monotonic increasing" is read as strictly increasing, which "the determinant
  uniquely determines the parameter `y₀`" needs. The remark is about the lift of Theorem 7.5.1
  normalized by `λ_cost = -1` (for `c(Λ₁, Λ_R, -1)` the determinant is `c²d(y₀)`), on `[0, t_sw]`.
- **Remark 7.6.4.** "When `k = 1`" is read as the limit `k → 1⁺` of the smoothed `(6k−2)`-gons with
  `k` real, since the closing condition has no solution at `k = 1` (E37). The claims are that the
  cost tends to `√12` and that the six arcs `σ_j([0, t_f(k)])` tend in the Hausdorff distance to the
  boundary of a rectangle of area `√12`, the image of `[-a, a] × [-b, b]` under a Euclidean motion
  (the proof takes `[-1, 1] × [-√3/2, √3/2]`; Hausdorff convergence does not depend on the norm of
  `ℝ²`, Mathlib's being the sup norm). The trajectories are quantified universally, and
  [`remark7_6_4_exists`](../../SmoothedPolygons/Ch7/Remarks.lean#L1900) shows that they exist.
- **Theorem 7.7.1.** "In some neighborhood of the set of initial conditions in the cotangent space"
  is read as a conic neighbourhood: some positive multiple of the costate `(Λ₁(0), Λ_R(0), λ_cost)`,
  with `X(0)`, lies in a neighbourhood of the octagon's initial condition normalized by
  `λ_cost = -1` (`g(0) = I₂` is a transversality condition). "The only extremal ... is that of the
  smoothed octagon" is read up to time translation and for terminal times near `t_f`; without these
  the statement is false (E32).
- **Extremals on an interval (Chapter 8).** "An extremal lifted trajectory on `[t₁, t₂]`" is the
  state–costate system of Problem 6.7.1 on that interval with the conditions of the maximum
  principle (`λ_cost ≤ 0` constant, nontriviality of `(λ_cost, Λ₁, Λ_R)`, the maximum condition
  and `H = 0` almost everywhere) and no boundary conditions ([`IsExtremalOn`](../../SmoothedPolygons/Ch8/Defs.lean#L60)); a Pontryagin
  extremal restricts to one on every subinterval. Normal and abnormal are as in Definition 6.2.1.
- **The edge control problem (§8.1).** Its state `(x, y, s)` is a point of `ℝ³` (`Fin 3 → ℝ`),
  its control `u_e ∈ [-½, ½]`, its state space `y > 0`, `|x| < 1/√3` (Definition 8.1.1), its
  dynamics (8.1.3) and its cost `∫x²/y` (8.1.5); its extremals ([`IsEdgeProblemExtremal`](../../SmoothedPolygons/Ch8/Defs.lean#L111)) are the
  conclusions of the maximum principle for it, with fixed endpoints (8.1.4), so that there are no
  transversality conditions. The book treats the edge `{u₀ = 0}` and the others "by rotational
  symmetry" (TeX 6774–6775); the formalization rotates explicitly: conjugation by `Rʲ`
  ([`edgeFrame`](../../SmoothedPolygons/Ch8/Defs.lean#L125)) takes a control in the edge `{u_j = 0}` to one in `{u₀ = 0}`, and is applied to `g`,
  `X`, `Λ₁` and `Λ_R`. The edge state of a Reinhardt trajectory ([`edgeState`](../../SmoothedPolygons/Ch8/Defs.lean#L136)) is `z = x + iy` with
  `Φ(z) = RʲXR⁻ʲ` (Lemma 4.2.1) and `s = ∫dt/y`, with `s = 0` at the start ("We can take
  `s₀ = 0`").
- **Edge extremality (Definition 8.1.2).** A trajectory is edge extremal on `[a, b]`
  ([`IsEdgeExtremalOn`](../../SmoothedPolygons/Ch8/Defs.lean#L149)) if on every subinterval on which some `u_j` vanishes almost everywhere, its
  edge state and edge control lift to an extremal of the `j`-th edge problem. The definition takes
  `u` and `X` only, since `g` is determined there by (8.1.1).
- **Maximizers and singular subarcs (§8.2).** `(X, Λ_R) ∈ ⋃_{I ⊆ {i,j}} (T*O_J)_I` is read as
  "the set of maximizers of the Hamiltonian over `U_T` ([`hamiltonianArgmax`](../../SmoothedPolygons/Ch8/Defs.lean#L159)) is contained in the
  edge `{i, j}` ([`controlEdge`](../../SmoothedPolygons/Ch8/Defs.lean#L165))". A singular subarc (Definition 6.2.1(3), [`IsSingularSubarc`](../../SmoothedPolygons/Ch6/Hamiltonian.lean#L255)) is an
  open interval at each time of which the Hamiltonian has at least two maximizers in `U_T`; a
  singular subarc of the edge problem ([`IsEdgeSingularSubarc`](../../SmoothedPolygons/Ch8/NoSingularArcs.lean#L217)) likewise, for the edge Hamiltonian
  (8.1.6) over `[-½, ½]`. Theorem 8.2.7 is read as E55 says. The singular locus (Definition 8.2.4,
  [`singularLocus`](../../SmoothedPolygons/Ch8/Defs.lean#L178)) is the printed set of quadruples `(g, Λ₁, X, Λ_R)`; along an extremal, the lift
  meets it at `t` exactly when `λ_cost ≠ 0`, `Λ₁(t) = (3/2)λ_cost J`, `X(t) = J` and `Λ_R(t) = 0`
  with the extremal's own `λ_cost`.
- **Lemma 8.2.1** is stated for `X` with `⟨X, Z_u⟩ ≠ 0` on `U_T` (E52), and **Theorem 8.1.4** for
  every extremal of the edge problem on a closed interval (E49). **Lemma 8.1.5**'s Landau notation
  is two-sided, as the book defines it (TeX 6903–6907), with the solutions continuous and in
  integral form. **Theorem 8.3.1** is read in its one-sided form (E56), and **Theorem 8.3.2** on a
  compact interval `[a, b]` (E57).
- **Bang-bang with finitely many switches.** [`IsFiniteBangBang`](../../Challenge.lean#L402) asks for a finite set of times off
  which the control is, near each time of `(a, b)`, almost everywhere constant at a vertex of
  `U_T`; the book's "adjusting the control on a set of measure zero" is this almost-everywhere
  formulation. A switching time ([`IsSwitchingTime`](../../SmoothedPolygons/Ch16/MahlerFirst.lean#L50)) is a time on each side of which the control is
  almost everywhere one vertex, the two vertices being different.
- **Smoothed polygons (Remark 8.3.3, Theorem 16.3.1).** A hyperbolic arc ([`IsHyperbolicArc`](../../Challenge.lean#L427)) is
  an injective continuous arc of a hyperbola `det(d₁, x - p₁)·det(d₂, x - p₂) = c`, `c ≠ 0`, with
  non-parallel asymptotes, the form of the conclusion of Lemma 3.1.8. The boundary of a smoothed
  polygon ([`IsSmoothedPolygonBoundary`](../../Challenge.lean#L438)) is the union of finitely many segments and finitely many
  hyperbolic arcs, each arc beginning and ending on segments and having as asymptotes the lines
  that extend two of the segments. "A finite-sided smoothed polygon with rounded hyperbolic arcs at
  each corner of the sort described by Reinhardt and Mahler", glossed as "no corners and the
  boundary alternates between straight edge segments and hyperbolic arcs, whose asymptotes are
  lines extending the straight edge segments" (TeX 12800–12804), is a centrally symmetric convex
  disk with a unique support line at each boundary point whose boundary is that of a smoothed
  polygon ([`IsSmoothedPolygon`](../../Challenge.lean#L452)): "no corners" is read as a unique support line at each boundary
  point, the form of Lemma 2.2.5, and "alternates" as each arc beginning and ending on a segment. "Defines a balanced disk `K(g, X)`" in Remark 8.3.3 is read as a
  hypothesis: a balanced pair `(K, σ)` with `σ_j = g s_j*` and `σ_j(t + t_f) = σ_{j+1}(t)` (E58).
- **The Fuller system (§13.2).** A point of `ℂ³` is `Fin 3 → ℂ` with `z 0 = z₁`, `z 1 = z₂`,
  `z 2 = z₃`. Trajectories with a measurable control are solved in Carathéodory's sense
  ([`TriFuller.IsTrajectory`](../../SmoothedPolygons/Ch13/Defs.lean#L170)), and the maximum condition (13.2.5) and `H_F = 0` (13.2.6), which the
  book writes for every `t`, are imposed almost everywhere ([`TriFuller.MaxCondition`](../../SmoothedPolygons/Ch13/Defs.lean#L179),
  [`TriFuller.IsExtremal`](../../SmoothedPolygons/Ch13/Defs.lean#L185), the solutions of Lemmas 13.2.1–13.2.3). The form `RR(a, b) = Re(āb)`
  ([`SmoothedPolygons.RR`](../../SmoothedPolygons/Ch13/Defs.lean#L97)) is the only coordinate of Chapters 10–11 that Chapter 13 uses.
- **The first control and the first switching time (TeX 10747–10753).** They are defined at every
  `z⁰` by the maximum condition along the constant-control trajectory, without choosing roots of
  the switching functions: `u ∈ V_T` is the first control ([`TriFuller.IsFirstControl`](../../SmoothedPolygons/Ch13/Defs.lean#L237)) if the
  constant control `u` is optimal along its own trajectory on some `[0, ε]`, and `t_sw`
  ([`TriFuller.firstSwitchTime`](../../SmoothedPolygons/Ch13/Defs.lean#L249)) is the time at which it stops being optimal. A double root of a
  switching function at which the control stays optimal (a tangency) is therefore not a switching
  time; there the extremal is unique and does not switch (E62). For `z⁰ ≠ 0` the first control
  exists and is unique, `0 < t_sw < ∞`, and every extremal with a measurable control from `z⁰`
  follows it up to `t_sw` ([`TriFuller.eq_flow_of_maxCondition`](../../SmoothedPolygons/Ch13/Extremals.lean#L424)); at `z⁰ = 0` the definitions take
  junk values. The most recent control and switching time (Lemma 13.2.5) are defined likewise.
- **Rotations.** Where the book rotates by `V_T` "without loss of generality" (to `i = 0` in
  Lemma 13.2.6, to `u = ζ` in Corollary 13.2.7, to `u = 1` in Lemma 13.3.1), the formal proofs
  compute for every vertex at once, through `RR(ua, ub) = RR(a, b)` for `|u| = 1`.
- **The blow-up and the Poincaré map (§13.4–13.5).** The identification `ℂ³ ∖ 0 ≅ ℝ_{>0} × Ξ` is
  a homeomorphism ([`TriFuller.blowup`](../../SmoothedPolygons/Ch13/Blowup.lean#L341)) with `φ` of class `C²`, smooth off `z₂ = 0` (E66). The
  Poincaré map `F(z⁰) = z(t_sw, z⁰, u)`, `u` the first control ([`TriFuller.poincare`](../../SmoothedPolygons/Ch13/PoincareMap.lean#L196)), is defined
  on `ℂ³ ∖ 0` rather than on `(ℝ_{>0} × Ξ)_𝒲`; on the section it is the book's map (E67). `F_ang`
  is defined on `Ξ_𝒲` and on `Ξ_𝒲/V_T` ([`TriFuller.poincareAng`](../../SmoothedPolygons/Ch13/PoincareMap.lean#L483), [`TriFuller.poincareAngQuot`](../../SmoothedPolygons/Ch13/PoincareMap.lean#L497)).
  `Ξ_{𝒲,0}/V_T`, which the book never defines formally (Remark 13.5.1 and Lemma 13.5.5 describe it
  in words), is the set where the maximized Hamiltonian `H_F⁺` vanishes ([`TriFuller.XiW0Quot`](../../SmoothedPolygons/Ch13/PoincareMap.lean#L516)), to
  which `F_ang` restricts ([`TriFuller.poincareAngZero`](../../SmoothedPolygons/Ch13/PoincareMap.lean#L539)); on a wall the two tied controls give the
  same value of `H_F`, so `H_F⁺` is the Hamiltonian there.
- **Lemma 13.5.2 and Remarks 13.5.3–13.5.4.** "Exactly two fixed points in `Ξ_𝒲/V_T` at which the
  Hamiltonian vanishes" is an equality of sets, `{x | F_ang(x) = x, H_F⁺(x) = 0} = {q_out, q_in}`,
  with `q_out ≠ q_in`. "`q_out ≡ (13.5.1) mod 𝒢`" is stated with a representative `q`
  ([`TriFuller.qOutCart`](../../SmoothedPolygons/Ch13/FixedPoints.lean#L70)) normalized by `Re z₁ = -1` and `z₃ ∈ ℝ_{<0}`, and the two spirals as
  `F(q) = ζ²·(rq₁, r²q₂, r³q₃)` with `r = r_scale`, and the same for `τ(q)` with `r = 1/r_scale`.
  `r_scale` ([`TriFuller.rScale`](../../SmoothedPolygons/Ch13/RScale.lean#L47)) is the unique real root greater than `1` of the palindromic
  polynomial, and the book's `≈ 6.27` and `≈ 7.4` are certified bounds, `6.27 < r_scale < 6.28`
  and `7.4 < t_sw < 7.41`. Remark 13.5.3 is stated for `q` and `τ(q)`; Remark 13.5.4 for its
  verifiable part (E69).
- **Lemma 13.5.5.** Stability is that of a fixed point of a map of a topological space
  ([`Function.IsLyapunovStable`](../../Basic/Dynamics/Stability.lean#L44), [`Function.IsAsymptoticallyStable`](../../Basic/Dynamics/Stability.lean#L49), [`Function.IsUnstable`](../../Basic/Dynamics/Stability.lean#L54), in
  [`Basic/`](../../Basic)): asymptotically stable means fixed, Lyapunov stable and attracting every point
  of a neighbourhood; unstable means fixed and not Lyapunov stable. The lemma is stated for `F_ang`
  on `Ξ_{𝒲,0}/V_T` with the quotient topology.
- **Lemma 10.1.1 and the coordinates of Chapters 10–11.** [`cayleyZ`](../../SmoothedPolygons/Ch14/LieChart.lean#L136) is the off-diagonal entry
  `z = (b + c)/2 + ia` of the Cayley transform of a traceless matrix ([`lemma10_1_1`](../../SmoothedPolygons/Ch14/LieChart.lean#L155), with the matrix
  of Appendix A.4). The Fuller coordinates of a phase point `(X, Λ₁, Λ_R)` are
  `ẑ = (w/ρ, -ib/(2ρ), c/(6ρ))`, with `w`, `b`, `c` the Cayley coordinates of `X`, `Λ₁/d₁` and
  `Λ_R` ((11.2.4), [`fullerCoords`](../../SmoothedPolygons/Ch14/LieChart.lean#L172)), in the normalization `λ_cost = -1`, `d₁ = 3/2`, `ε = 1`, `ρ = 2`
  of Chapters 11–16. The rotation `Ad_R` is multiplication by `ζ²` in these coordinates
  ([`fullerCoords_adR`](../../SmoothedPolygons/Ch14/LieChart.lean#L946)) for traceless phase points, which the book's are: the formalization's first
  statement of the identity, for every phase point, was false, and a counterexample is proved in
  Lean. The time reversal of Remark 10.2.3 is the Fuller `τ` ([`fullerCoords_reinTau`](../../SmoothedPolygons/Ch14/LieChart.lean#L954)).
- **The Lie algebra chart (§14.1).** A phase point near the singular locus is `lieChart (r, x̃)`,
  `x̃ = (x̃₂₁, ℓ̃₁₁, ℓ̃₂₁)`, normalized by `x̃₁₁ = 1`, with `Λ_R` the solution of (14.1.3); the points
  of the chart lie on the wall `χ₂₃ = 0`, and `H*` is [`lieChartDomain`](../../SmoothedPolygons/Ch14/LieChart.lean#L128), with `r > 0`. At `q_in`
  the chart is the mirrored chart `lieChartIn = τ ∘ lieChart` (E87).
- **The asymptotics (§14.2).** `z(x̃)` is defined by its explicit value
  `((x̃₂₁ + i)/2, (ℓ̃₁₁ - iℓ̃₂₁)/6, (ℓ̃₁₁ + ℓ̃₂₁x̃₂₁)/6)`, and [`tendsto_zhat_div`](../../SmoothedPolygons/Ch14/Asymptotics.lean#L373) states that it is
  the book's limit. In Lemma 14.2.3, `ẑ(r(s), x̃(s))`, along a trajectory that leaves the section,
  is read as the Fuller coordinates of the phase point at time `sr₀`; the lemma is stated for each
  `s` as `r₀ → 0⁺`, without "for each `s` such that `r(s) < 1`" (E84), with `O`-constants that
  depend on `s` and `x̃⁰`, as printed. Remark 14.2.1 is an enclosure within `0.01` of the printed
  values, with an exact identity (E82).
- **Lemma 14.3.1, Theorem 14.3.3 and Remark 14.3.4.** The Reinhardt–Poincaré map in the chart is
  [`reinChartMap`](../../SmoothedPolygons/Ch14/AnalyticExtension.lean#L137): the flow with the control `e₂` from the wall `χ₂₃ = 0` to the first zero of
  `χ₂₁`, then `Ad_{R⁻¹}`, read back in the chart. "`F` … extends to an analytic diffeomorphism in a
  neighborhood of the fixed point `(0, x̃_out) ∈ ℝ⁴` … such that `F` coincides with the
  Fuller-Poincaré map at `r = 0`" is an open partial homeomorphism `e` of `ℝ × ℝ³` with
  `IsReinhardtPoincareExtension e`: analytic, with analytic inverse, on its source, a neighbourhood
  of `(0, x̃_out)`, which it fixes; equal to [`reinChartMap`](../../SmoothedPolygons/Ch14/AnalyticExtension.lean#L137) for `r > 0` and to
  `(0, fullerChartMap x̃)` at `r = 0`. [`lemma14_3_1`](../../SmoothedPolygons/Ch14/AnalyticExtension.lean#L1217) says that one exists, and Theorem 14.3.3 and
  Remark 14.3.4 are stated for every such `e`. Their local stable and unstable manifolds are the
  local stable and unstable sets of the StableManifold package (the points whose forward orbit
  stays in `U` and tends to the fixed point; the points with a backward orbit in `U` tending to
  it), hyperbolic means that no complex eigenvalue of the derivative has modulus `1`, the `C^∞`
  curve is the graph of a `C^∞` map over the `r`-axis, and Remark 14.3.4 is stated in the mirrored
  chart, for `e⁻¹` (E87).
- **Theorem 14.4.1.** It is the named proposition [`Theorem14_4_1`](../../SmoothedPolygons/Ch14/NoReturn.lean#L108), in the normalization
  `λ_cost = -1`. "A trajectory of the Reinhardt system" is read as an extremal on an interval
  `[a, c]` that is bang-bang with finitely many switches on every compact subinterval of `(a, c)`:
  the proof speaks of its switches ("All switches must be on the unstable curve"), and without edge
  extremality Chapter 8 gives no such structure (E57). The added hypothesis weakens the statement,
  the assembly of Theorem 16.3.1 supplies it (Theorem 8.3.2), and with it Lemma 8.3.4 settles the
  interior of the interval, so that only an end point carries content. A trajectory that
  "emanates from the fixed point `(0, x_out)`" is a chattering arc out of the singular locus
  ([`IsChatteringArcOutOf`](../../SmoothedPolygons/Ch16/ClusterCoordinates.lean#L115)) whose switching points converge backward to `q_out` modulo `V_T`, and
  "returning to the exceptional divisor" is meeting the singular locus again; the second part is
  read likewise at `q_in`. The same reading of "a trajectory" is built into
  [`IsChatteringArcInto`](../../SmoothedPolygons/Ch16/ClusterCoordinates.lean#L106), so it concerns Theorem 16.4.1 too. In fact the added hypothesis is no restriction:
  the statement without it is equivalent ([`theorem14_4_1_iff_unrestricted`](../../SmoothedPolygons/Ch14/NoReturnReading.lean#L62)), since before the first
  return to the singular locus a normal extremal is edge extremal and so finitely bang-bang (Theorem
  8.3.2). The second part is stated at `q_in` without the chart (E87). The named proposition is
  proved ([`theorem14_4_1_unconditional`](../../SmoothedPolygons/Ch16/MahlerFirstArcRegion.lean#L51)).
- **N4 (Figure 14.2).** The fact that the proof of Theorem 14.4.1 reads off the figure is the named
  proposition [`UnstableCurveLeavesStarDomain`](../../SmoothedPolygons/Ch14/UnstableCurve.lean#L174), stated orbit-wise, as the proof uses it: for some
  extension `e` of Lemma 14.3.1 and some neighbourhood `U` of the fixed point, the forward orbit
  under the Reinhardt–Poincaré map of every point of the local unstable curve `W^u_loc(e, U)` with
  `r > 0` switches cyclically for some `K` steps ("the switching sequence is always cyclical", TeX
  11983–11985: after each switch the control is `e₂`, and along the `e₂`-arc `e₂` stays the strict
  maximizer up to the switch to `e₁`), and then the `e₂`-arc from the `K`-th point leaves the star
  domain before its next switch (TeX 11987–11991). These are the conditions under which the
  Reinhardt–Poincaré map gives the next switching point of an extremal, and the exit. With `∃ U`,
  `∃ e` and `∀ e` are equivalent; `U` must be existential, since for a large `U` the extension and
  the chart take junk values. N4 omits what the proof does not use: the figure's end point
  `(r, x̃₂₁) ≈ (0.21, -3.03)`, the threshold `r ≈ 0.065` beyond which one arc suffices (E94), and the
  claim that the switching points along the curve accumulate on the chart boundary
  `x̃₂₁ = √3 - 1/r` (Figure 14.2). Its proof gives more: every chart point with `r > 0` of a neighbourhood of `(0, x̃_out)` reaches the boundary of
  the star domain, not only the points of the curve.
- **The cells of Chapter 15 as charts.** The book works on "the domain given by the cells covering
  `Ξ_{𝒲,0}/V_T`" (TeX 12038–12041), a cell complex in which the faces of the two closed big cells
  are identified only in part (TeX 12149–12165), so that two of its points can be the same point
  of `Ξ_{𝒲,0}/V_T`. The formalization keeps the book's theorems on `Ξ_{𝒲,0}/V_T`
  ([`TriFuller.XiW0Quot`](../../SmoothedPolygons/Ch13/PoincareMap.lean#L516)) with the Poincaré map `F_ang`, and uses the cells as charts: the
  coordinates `p = (r₂, ψ, θ₂)` give the point
  `((1 - r₂)e^{i(θ₂ - ψ)}, r₂e^{iθ₂}, -2(1 - r₂)r₂ sin ψ)` ([`TriFuller.cellPoint`](../../SmoothedPolygons/Ch15/CellCoordinates.lean#L225)) and its class
  ([`TriFuller.cellClass`](../../SmoothedPolygons/Ch15/CellCoordinates.lean#L255)), which is continuous on the closed cells, onto from their union
  (Proposition 15.2.2) and injective on each open box ([`definition15_1_2`](../../SmoothedPolygons/Ch15/CellCoordinates.lean#L988)). The regions of the
  book's figures are images of sets of coordinates. In Proposition 15.2.2, "every point on every
  face of the cells that is not identified with a point in the domain" is read as a face point at
  which the cell's control is not the first control; there the switching time tends to `0` from the
  open cell, and the extended map is the identity of `Ξ_{𝒲,0}/V_T`, a change of representative
  ([`proposition15_2_2`](../../SmoothedPolygons/Ch15/SmallerCells.lean#L1385)).
- **(15.1.1) and the coordinates.** "Assume that the Hamiltonian vanishes at `z` for some control
  `u ∈ V_T`" is read as the vanishing of the maximized Hamiltonian `H_F⁺` (for `u = 1` the
  displayed formula fails), and "`ψ ∈ (0, π)` (modulo integer multiples of `2π`)" as `sin ψ > 0`
  ([`eqn15_1_1`](../../SmoothedPolygons/Ch15/CellCoordinates.lean#L912)). The second big cell is `θ₂ ∈ (-π, 0]`, its top face included, which is exactly
  the set of points with `x₃ < 0` and first control `ζ²` ([`TriFuller.cellTwoSet`](../../SmoothedPolygons/Ch15/CellCoordinates.lean#L260)). The time
  reversal in coordinates, `τ(r₂, ψ, θ₂) = (r₂, π - ψ, ±π - θ₂)` ([`TriFuller.cellTau`](../../SmoothedPolygons/Ch15/CellCoordinates.lean#L406)), takes `+π`
  at `θ₂ = 0`, where the book allows either sign; both give the same class. The closed 2-cell
  `𝒞₂(ζ, 1, 1)` has `θ₂ ∈ [π/3, π]`, as in the book (TeX 12256–12260), and its switching facts
  are stated on its relative interior `r₂ > 0`, `θ₂ ∈ (π/3, π)`, where
  `(m_A, m_B) = (1, 1)` (at `θ₂ = π`, `m_B = 3`; at `r₂ = 0`, `m_A = 2`); its coordinates are
  `(r₂, ψ, θ₂)` with `ψ ∈ {0, π}`, for the book's `r̃₁ = ±r₁` (E71).
- **The involution and the parts (§15.3).** `𝔦 = τ ∘ F` is defined on `Ξ_{𝒲,0}/V_T` with the
  Poincaré map ([`TriFuller.involution`](../../SmoothedPolygons/Ch15/Involution.lean#L402)), and two sets are in involution when `𝔦` maps each onto the
  other. The loci `∂_res` and `∂_A` are the images under `𝔦` of the 2-cell `𝒞₂(ζ, 1, 1)` and of the
  top face `𝒞₂(ζ, 0, 2)`, on which the Poincaré map is the book's map; `∂_{A,ζ²} = 𝔦(𝒞₂^A)` and
  `∂_B = 𝔦(𝒞₂^B)` are taken with the book's root-based maps `F_A` and `F_B` (E74), and "`Δ_{A,0}`
  vanishes along `∂_A`" (TeX 12426) is read with `∂_{A,ζ²}` (E71). The parts `𝒟₂`, `𝒟₃` and `𝒟₄`
  are defined by their active switching function, that is, by the control to which the Poincaré
  map switches on the open boxes (TeX 12428–12438; [`TriFuller.switchSet`](../../SmoothedPolygons/Ch15/Involution.lean#L823)), and `𝒟₁` as the closure
  of the connected components of the open first box minus the loci `∂_A ∪ ∂_res` whose closures
  meet the top face ([`TriFuller.partD1`](../../SmoothedPolygons/Ch15/Involution.lean#L834)); `𝒟₀` is the book's. That these are the book's parts
  (`𝔦(𝒟₃) = 𝒟₄`) and form geometric partitions is part of Proposition 15.3.2, which is not proved
  (E72).
- **Theorem 16.1.1.** The boxes `𝒟_ij` are read with `θ₂ ∈ [b_{j+1}, b_j]` (E76), as sets of
  `Ξ_{𝒲,0}/V_T` ([`TriFuller.boxSet`](../../SmoothedPolygons/Ch16/BasinHypotheses.lean#L103)); `𝒟_out` is `𝒟₀₀`, and `𝒟_in = 𝒟₁ ∩ 𝒟₂₂` is replaced by the
  box `𝒟₂₂`. The theorem is stated as printed, for the Poincaré map `F_ang` of `Ξ_{𝒲,0}/V_T`: for
  every `q ≠ q_in`, `F^k(q) → q_out` ([`theorem16_1_1`](../../SmoothedPolygons/Ch16/GlobalBasin.lean#L599)), from the three named facts, which are proved
  ([`theorem16_1_1_unconditional`](../../SmoothedPolygons/Ch16/BasinFacts.lean#L52); Section 2).
- **Theorem 16.2.1.** The Fuller–Poincaré dynamical system is the Poincaré map `F` on `ℂ³ ∖ 0`
  (TeX 12749–12752). An outward trajectory that emanates from the singular locus is a backward
  orbit, `z_k ≠ 0` with `F(z_{k+1}) = z_k` and `z_k → 0`; an inward trajectory to the singular
  locus is a forward orbit `F^k(z⁰) → 0` from a point `z⁰ ≠ 0` on a wall; and "in the set
  `ℝ_{>0} × {q}` modulo `V_T`" means that the point lies in the section and that its class in
  `Ξ_{𝒲,0}/V_T` is `q` ([`theorem16_2_1`](../../SmoothedPolygons/Ch16/OutwardFuller.lean#L567)). The book states the theorem on `(ℂ³ ∖ 0)/V_T`, so the
  vanishing of the Hamiltonian is derived, not assumed (E80).
- **Theorem 16.3.1.** "The global minimizer" is read as every global minimizer of Problem 3.6.2
  ([`IsReinhardtMinimizer`](../../Challenge.lean#L392)) and "the minimizer `K_min`" as every `K_min` ([`IsWorstDisk`](../../Challenge.lean#L413)); one of
  each exists (E46, E4), so the reading loses nothing. The theorem is stated as two conclusions:
  every global minimizer has a bang-bang control with finitely many switches on `[0, T]`, and every
  `K_min` is a smoothed polygon ([`theorem16_3_1_unconditional`](../../SmoothedPolygons/Ch16/MahlerFirstArcRegion.lean#L94); in the Challenge,
  [`SmoothedPolygonsChallenge.mahler_first_conjecture`](../../Challenge.lean#L468)). [`theorem16_3_1`](../../SmoothedPolygons/Ch16/MahlerFirst.lean#L349) states them under the
  hypothesis [`NoChatteringIntoSingularLocus`](../../SmoothedPolygons/Ch16/MahlerFirst.lean#L110) (E60), and [`theorem16_3_1_of_theorem14_4_1`](../../SmoothedPolygons/Ch16/NoChattering.lean#L387) under
  [`Theorem14_4_1`](../../SmoothedPolygons/Ch14/NoReturn.lean#L108) and the three numerical facts (E89); both are corollaries.
- **Theorem 16.4.1.** "A Pontryagin extremal Reinhardt trajectory" is an extremal on an interval
  `[a, b]` ([`IsExtremalOn`](../../SmoothedPolygons/Ch8/Defs.lean#L60), without boundary conditions), normalized by `λ_cost = -1`, which Lemma
  8.2.2 allows at the singular locus ([`IsExtremalOn.normalize`](../../SmoothedPolygons/Ch16/NoChattering.lean#L135)). "A cluster point on the
  exceptional divisor of the blow-up, reached in finite time", with "the switching points
  themselves … not on the exceptional divisor", is a chattering arc into the singular locus
  ([`IsChatteringArcInto`](../../SmoothedPolygons/Ch16/ClusterCoordinates.lean#L106): the lift meets `𝒮_sing` at `b` and only there, the control is bang-bang
  with finitely many switches on every compact subinterval of `(a, b)`, and the switching times
  increase to `b`). The switching points are compared with the fixed points through their angular
  components ([`switchAng`](../../SmoothedPolygons/Ch16/ClusterCoordinates.lean#L123)), modulo the diagonal action of `V_T`. "That cluster point is the fixed
  point `q_in`" is the convergence of the angular components to `q_in` modulo `V_T`, so that `q_in`
  is the only cluster point; and "the switching points lie on the stable curve `W^s(q_in)`" is: for
  every extension `e` of Lemma 14.3.1 and every neighbourhood `U` of the fixed point, eventually
  each switching point, rotated onto the section `χ₂₃ = 0`, is `lieChartIn p` with `p` in the local
  unstable set of `e` in `U`, the local stable set of `e⁻¹` at `q_in` ([`theorem16_4_1`](../../SmoothedPolygons/Ch16/ClusterPoint.lean#L1021); its time
  reversal, with `q_out` and the unstable curve, is [`theorem16_4_1_reverse`](../../SmoothedPolygons/Ch16/ClusterPoint.lean#L1042)).
- **Corollary A.1.3** is stated as printed, on `[0, t₁]` with the conclusion as `t → 0⁺`; the
  two-sided form that Chapter 8 uses is a separate statement (E61).
- **Theorem A.3.1.** The manifold is an open subset of a finite-dimensional real normed space (for
  Chapter 14, the chart `ℝ⁴ = ℝ × ℝ³`), the diffeomorphism an open partial homeomorphism `e`, `C^r`
  near the fixed point `p`. The local stable set of `f|_U` is the set of points whose forward orbit
  stays in `U` and tends to `p` (E92), and the local unstable set that of the points with a backward
  orbit in `U` tending to `p`; the stable and unstable summands are defined by the dynamics of
  `Df(p)`; and the submanifolds are graphs of `C^r` maps over the summands, over neighbourhoods of
  `0`, tangent to the summands at `p` ([`theoremA_3_1`](../../SmoothedPolygons/AppA/StableManifold.lean#L186)). The global part is not stated. "Unstable
  for `f` means stable for `f⁻¹`" is `Function.localStableSet_symm_eq_localUnstableSet` of the
  package.
- **Balanced pairs exist.** The unit disk, with `σ_j(t) = Rot(t) s_j*` and `t_f = π/3`, is a
  balanced pair ([`circle_isBalancedPair`](../../SmoothedPolygons/Ch2/BalancedCircle.lean#L241)), so the hypotheses of the results of Chapter 3 about
  balanced pairs can be met.
- **Corrections of statements.** E1 (Lemma 2.2.1 in its packing form, user-approved), E13
  (hypothesis, user-approved), E16 (misprint), E17 (`X ≠ 0`), E20 (misprint), E21 (nontriviality on
  the reduced costate, derived from the maximum principle with non-redundant boundary conditions),
  E26 (`⟨X, Z_u⟩ ≠ 0`), E32 (Theorem 7.7.1 up to time translation, with
  terminal time near `t_f`, user-approved), E34 (regularity, user-approved), E35 (the extended
  velocity sets, user-approved), E15 (the converse of Problem 3.6.2 for winding number one), E40
  and E45 (the fundamental domain), E51 (the signs of Remark 8.1.6), E52 (`⟨X, Z_u⟩ ≠ 0` in Lemma
  8.2.1), E55 (Theorem 8.2.7 in the authors' reading, user-approved), E56 (Theorem 8.3.1 in its
  one-sided form, user-approved), E57 (Theorem 8.3.2 as Chapter 8 states it), E58 (the disk of
  Remark 8.3.3 as a hypothesis), E65 (the type of `z_j` in Lemma 13.3.2), E66 (the identification
  of §13.4 as a homeomorphism with `φ` of class `C²`), E71 (ranges, a region and a reversed
  substitution in §15.1–15.2, and `∂_{A,ζ²}` for `∂_A` in §15.3), E73 (`F⁻¹ = τFτ` at switching
  points), E75 (the labels of Remark 15.3.1), E76 (the index of the boxes of §16.1), E81 (`X` for
  the matrix printed as `X̃`), E82 (the domain of `ξ(x̃)`), E87 (Remark 14.3.4 in a mirrored chart,
  and the second statement of Theorem 14.4.1 without the chart),
  E92 (the local stable set, with its orbit in `U`), and in proofs E14, E24, E44, E50, E59, E64,
  E65, E67, E74, E79, E80, E83, E85 and E88–E91.
