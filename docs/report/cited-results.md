# Results from prior work and how the paper uses them

Part of the [audit report](../../REPORT.md).

## Proved in `External/`

| Cited result | Source | Lean | Used by |
| --- | --- | --- | --- |
| Euler–Arnold equation for left-invariant Hamiltonians on matrix groups, `μ' = [μ, δh/δμ]` for `μ = pg` | Cushman–Bates, cited in the proof of Proposition 6.5.1 | [`External.euler_arnold`](../../External/EulerArnold.lean#L72) | [`proposition6_5_1`](../../SmoothedPolygons/Ch6/Hamiltonian.lean#L319) |
| Fejes Tóth's theorem: for a centrally symmetric convex disk, no packing of congruent copies is denser (even in upper density) than the best lattice packing | L. Fejes Tóth 1950; cited as Theorem 2.1.3 | [`External.fejes_toth`](../../External/FejesToth.lean#L882) | [`theorem2_1_3`](../../SmoothedPolygons/Ch2/Density.lean#L252) |
| The upper and lower densities of a lattice arrangement of a convex body are `V(C)/d(L)` | Gruber, *Convex and Discrete Geometry*, Cor. 30.1; cited in Definition 2.1.2 | [`External.gruber_corollary_30_1`](../../External/Gruber.lean#L320) | [`definition2_1_2`](../../SmoothedPolygons/Ch2/Density.lean#L86) |
| A critical lattice has a basis and a third point on the boundary forming a parallelogram of area `Δ(K)`, and conversely | Minkowski 1907, Mahler 1947 (Lemma 2); cited as Theorem 2.3.6, from Minkowski and Mahler 1946 (E33) | [`External.minkowski_mahler`](../../External/MinkowskiMahler.lean#L964) | [`theorem2_3_6`](../../SmoothedPolygons/Ch2/Mahler.lean#L113) |
| The circumscribed hexagon of a critical lattice: unique tac-lines, area `4Δ(K)`, sides bisected, least area | Mahler 1947, Theorems 1 and 2; cited as Theorem 2.3.7 | [`External.mahler_1947`](../../External/Mahler1947.lean#L1700) | [`theorem2_3_7`](../../SmoothedPolygons/Ch2/Mahler.lean#L182) |
| A symmetric convex domain is irreducible (no symmetric convex proper subdomain has the same `Δ`) if and only if every boundary point lies on a critical lattice; hence, in an irreducible domain, every tac-line contains a point of a critical lattice, one of the six boundary points of a configuration of Mahler's Lemma 2 | Mahler 1947, Lemma 3, stated there without proof; cited after Definition 2.3.5. Proved along Mahler's paper A and Mahler 1946 (below) | [`External.mahler_irreducible_iff`](../../External/MahlerIrreducible/Lemma3.lean#L367); [`External.mahler_irreducible`](../../External/MahlerIrreducible/Lemma3.lean#L383), derived from it | [`isIrreducible_iff_mahlerIrreducible`](../../SmoothedPolygons/Ch2/Mahler.lean#L99) (the remark after Definition 2.3.5); [`lemma2_2_5`](../../SmoothedPolygons/Ch2/Reinhardt.lean#L3749) |
| Filippov's theorem: for a control system on `ℝⁿ` with compact control set, convex velocity sets and `f` of compact support, the attainable sets (at time `T` and up to time `T`) are compact, and an optimal control exists for an integral cost when the velocity sets extended by the cost are convex, with fixed or free terminal time | Agrachev–Sachkov, *Control Theory from the Geometric Viewpoint*, Thm 10.1; cited as Theorem 6.1.1 without a source (E35) | [`External.filippov`](../../External/Filippov.lean#L153); for §6.1, its form with a closed state constraint, a compact set of initial points, a closed endpoint relation and a window of terminal times, `ControlSystem.exists_optimal_constrained` of the OptimalControl package (same proof) | Theorem 6.1.1; the form with a state constraint, in §6.1: [`exists_isReinhardtMinimizer`](../../SmoothedPolygons/Ch6/Existence.lean#L436) (E46) |
| The Pontryagin maximum principle with free terminal time, an integral cost and mixed boundary conditions `(q(0), q(t_f)) ∈ N` (`N` cut out near the end points by a `C¹` submersion), for strong local minimizers on an open subset of a finite-dimensional space with a compact control set: `ν ≤ 0` and a Lipschitz covector curve `p` with `(ν, p(t)) ≠ 0` for every `t`, the adjoint equation, the maximum condition and `H = 0` almost everywhere, and the transversality condition `(-p(0), p(t_f)) ⊥ T N` | Agrachev–Sachkov, *Control Theory from the Geometric Viewpoint*, Ch. 12, Theorem 12.5 with the remark after it (free time), read in the authors' draft; cited in §6.2 from the entry `zelikin2004control` (E33) | [`External.pontryagin_maximum_principle`](../../External/Pontryagin.lean#L80), proved in the OptimalControl package (`Pontryagin.maximum_principle`) | [`exists_isPontryaginExtremal_of_isReinhardtMinimizer`](../../SmoothedPolygons/Ch6/MatrixExtremal.lean#L564) (§6.2 and §6.6: every minimizer is an extremal); [`proposition8_1_3`](../../SmoothedPolygons/Ch8/EdgeExtremal.lean#L850) (Proposition 8.1.3: the minimizer is edge extremal, by the principle for the edge control problem, E48) |
| Sussmann's Noether theorem: for an optimal control system of class `C¹` and an infinitesimal group of symmetries that preserve the dynamics and the cost, the momentum map is constant along every lifted trajectory with the adjoint equation and the maximum condition | Sussmann, *Symmetries and integrals of motion in optimal control* (1995), Theorem 4.1; cited as the Noether–Sussmann theorem (Theorem 9.1.4), whose quotation drops the invariance of the cost (E95) | [`External.noether_sussmann`](../../External/NoetherSussmann.lean#L105); Sussmann's statement, [`External.sussmann_theorem4_1`](../../External/NoetherSussmann.lean#L87); the form for one symmetry, [`External.noether_sussmann_one_parameter`](../../External/NoetherSussmann.lean#L119); proved in the OptimalControl package (`Pontryagin.noether`) | the form for one symmetry: [`momentum_rotationField_eq`](../../SmoothedPolygons/Ch9/AngularMomentum.lean#L878), and through it [`theorem9_1_6`](../../SmoothedPolygons/Ch9/AngularMomentum.lean#L1689) and [`remark9_1_7`](../../SmoothedPolygons/Ch9/AngularMomentum.lean#L1703); [`remark9_1_7_rightAction`](../../SmoothedPolygons/Ch9/AngularMomentum.lean#L1759) |
| The stable manifold theorem: at a hyperbolic fixed point `p` of a `C^r` diffeomorphism (`r ≥ 1`), for some open neighbourhood `U` of `p`, the local stable set of `f\|_U` is a `C^r` embedded submanifold tangent at `p` to the stable summand; likewise the local unstable set | M. C. Irwin, *Smooth Dynamical Systems*, Ch. 6; cited in §14.3 and recalled as Theorem A.3.1 (Appendix A.3) | [`theoremA_3_1`](../../SmoothedPolygons/AppA/StableManifold.lean#L186), the book's Theorem A.3.1 (stated in [`SmoothedPolygons/AppA/StableManifold.lean`](../../SmoothedPolygons/AppA/StableManifold.lean), not in [`External/`](../../External), with the submanifolds as graphs over the summands; E92), proved from `Function.exists_localStableSet_localUnstableSet_eq_graph` of the StableManifold package | [`theorem14_3_3`](../../SmoothedPolygons/Ch14/FixedPointManifolds.lean#L694) (the `C^∞` unstable curve) and [`remark14_3_4`](../../SmoothedPolygons/Ch14/FixedPointManifolds.lean#L825), and through them [`theorem16_4_1`](../../SmoothedPolygons/Ch16/ClusterPoint.lean#L1021) and [`theorem16_4_1_reverse`](../../SmoothedPolygons/Ch16/ClusterPoint.lean#L1042) (the stable and unstable curves), and [`theorem14_4_1`](../../SmoothedPolygons/Ch14/NoReturnProof.lean#L170) (the switching points of a trajectory from `q_out` lie on the unstable curve), with it [`theorem16_3_1_unconditional`](../../SmoothedPolygons/Ch16/MahlerFirstArcRegion.lean#L94); not [`theorem16_3_1_of_theorem14_4_1`](../../SmoothedPolygons/Ch16/NoChattering.lean#L387) |

Mahler 1947 states Lemma 3 without proof and refers to Lemmas 8 and 12 of "paper A", Mahler's *On
irreducible convex domains* (Proc. KNAW 50 (1947) 98–107; the book does not cite it).

Paper A proves its Lemmas 1, 2, 5–7 and 13 and quotes Lemmas 8, 10, 11 and 12 from Theorems B–E of
Mahler's *Lattice points in n-dimensional star bodies II. Reducibility theorems I* (Proc. KNAW 49
(1946) 331–343, the book's entry `mahler1946lattice`).

We read both from scans of Mahler's collected works (CARMA archive, items 094 and 088), and the
proof follows them, down to the 1946 paper, as the user chose:

| Results | File |
| --- | --- |
| paper A's lemmas | [`External/MahlerIrreducible.lean`](../../External/MahlerIrreducible.lean) |
| Theorems B and C, with paper A's Lemmas 10 and 11 and the class-B case of its Lemma 13 | [`External/Mahler1946/TheoremC.lean`](../../External/Mahler1946/TheoremC.lean) |
| Theorems D and E, with paper A's Lemma 12 | [`External/Mahler1946/TheoremE.lean`](../../External/Mahler1946/TheoremE.lean) |
| Lemma 3 | [`External/MahlerIrreducible/Lemma3.lean`](../../External/MahlerIrreducible/Lemma3.lean) |

The proof of Lemma 3:

- "Only if" is the proof of paper A's Lemma 13:
  - extreme points of `K` through the proof of Theorem C (paper A's Lemma 10) and a cut by a line;
  - inner points of boundary segments through paper A's Lemmas 5–7, using that the boundary points
    on critical lattices form a closed set (Theorem B, paper A's Lemma 11).
- "If" is Theorems D and E with paper A's Corollary to Lemma 5 and Lemma 1.
- The form that Lemma 2.2.5 uses (each tac-line contains a point of a critical lattice) follows
  with paper A's Lemmas 3 and 4.

The errors and gaps of the sources, all repaired, and the two small departures from them are in
Section 7.

Filippov's theorem is proved by the standard argument:

- the trajectories are equi-Lipschitz;
- a limit is extracted by Tychonoff's theorem (pointwise convergence suffices, so Arzelà–Ascoli is
  not needed);
- its velocities lie in the closed convex velocity sets (by closed thickenings of them);
- a control realizing them is chosen measurably (a Kuratowski–Ryll-Nardzewski selection, proved in
  `OptimalControl.MeasureTheory.MeasurableSelection`, in the OptimalControl package; Mathlib has
  none);
- and optimal controls come from the system extended by the cost
  (`OptimalControl.ODE.ControlSystem`).

The proof was written before we had Agrachev and Sachkov's text and was not compared with theirs.
The statement is the book's, with the source's standing smoothness assumptions on `f` (Section 5)
and the correction of E35.

The form that §6.1 needs, for trajectories confined to a closed set `S`, starting in a compact set
and with endpoints in a closed relation (`OptimalControl.ODE.StateConstraint`, in the package), is
proved by the same argument.

A limit of trajectories that stay in `S` stays in `S`, so the dynamics need to be continuous, with
bounded velocities and convex velocity sets, only on `S × U`, and need not have compact support.

The maximum principle is proved in the OptimalControl package by Agrachev and Sachkov's own
argument (Chapter 12 of their book, read in the authors' draft, with preface dated September
2003, from the first author's home page; page numbers in this report are the draft's).

It works in coordinates on an open subset of a finite-dimensional space:

- needle variations at Lebesgue points of the reference control, transported by the resolvent of
  the variational equation;
- Lemma 12.1 (openness at the vertex of a cone, by Brouwer's fixed-point theorem);
- Lemma 12.2 and Theorem 12.1 (the geometric maximum principle, by a covector supporting the cone
  of variations);
- and Agrachev and Sachkov's auxiliary systems for free time, the cost and mixed boundary
  conditions (Theorems 12.2–12.5), applied together for free time with a cost, the case the book
  needs, which the source leaves to the reader.

Brouwer's theorem, which the source uses without reference and Mathlib lacks, is proved in the
FixedPoint package by the analytic argument of Milnor (1978) and Rogers (1980).

The Carathéodory theory beneath (existence, uniqueness and differentiable dependence of solutions
for measurable controls), which the source cites from Gamkrelidze, is proved by Picard iteration
and Gronwall's inequality.

[`External/Pontryagin.lean`](../../External/Pontryagin.lean) states the theorem as the book cites it and takes the proof from the
package. The departures from the source (D1–D11 of the package's README) and its three gaps are
in Section 7.

The book applies the maximum principle in §6.2 and §6.6 to the Reinhardt problem; the
formalization follows it ([`exists_isPontryaginExtremal_of_isReinhardtMinimizer`](../../SmoothedPolygons/Ch6/MatrixExtremal.lean#L564), in
[`SmoothedPolygons/Ch6/MatrixExtremal.lean`](../../SmoothedPolygons/Ch6/MatrixExtremal.lean)):

- the state `(g, X)` lies in the open set `GL₂⁺(ℝ) × C` of `Mat₂(ℝ) × 𝔰𝔩₂(ℝ)`, with `C` the open
  cone of the star inequalities (on which `⟨Z_u, X⟩ < 0` for `u ∈ U_T`, so the dynamics are
  smooth);
- a global minimizer of Problem 3.6.2 is a strong local minimizer there, since `det g` and `det X`
  are first integrals;
- the covector of the maximum principle gives the costates `Λ₁` (the left trivialization `pg`,
  made traceless) and `Λ_R = [Λ₂, X]`, whose equations follow from the adjoint equation by
  Proposition 6.5.1 (with the Euler–Arnold equation);
- and the transversality conditions are those of §6.6, the one for `Λ₁` from `g(t_f) = R` by
  Corollary 6.5.3, as Remark 6.6.1 says.

The one departure, in the boundary conditions, is E21 (Section 7).

The stable manifold theorem is proved in the StableManifold package
([github.com/vltanh/lean4-stable-manifold](https://github.com/vltanh/lean4-stable-manifold),
required like OptimalControl) by the Lyapunov–Perron method.

For a map of a finite-dimensional real normed space that is `Cⁿ` (`1 ≤ n ≤ ∞`) near a fixed point
`p` with invertible hyperbolic derivative:

- the bounded orbits of a cut-off of the map are the fixed points of a contraction on bounded
  sequences;
- in every small neighbourhood of `p` the local stable set is the graph of a `Cⁿ` map over the
  stable subspace, tangent to it, and the local unstable set a graph over the unstable subspace;
- smoothness of every order comes from the smoothness of composition operators on bounded
  sequences.

The package follows the standard argument rather than Irwin's text and was not compared with it
line by line.

Its stable and unstable subspaces are defined by the dynamics of `Df(p)` (the vectors whose
forward, respectively backward, orbit tends to `0`), where the book takes sums of generalized
eigenspaces; at a hyperbolic fixed point the two agree (E92).

[`theoremA_3_1`](../../SmoothedPolygons/AppA/StableManifold.lean#L186) states the theorem as the book recalls it, for an open partial homeomorphism of a
finite-dimensional space, with the local unstable statement. The global (immersed) part is not
stated, since no proof of the book uses it.

- The theorem gives the `C^∞` unstable curve of Theorem 14.3.3 and, through Remark 14.3.4, the
  stable curve in the second part of Theorem 16.4.1.
- Mahler's First conjecture uses it through Theorem 14.4.1, whose first step puts the switching
  points of a trajectory from `q_out` on the local unstable curve
  ([`IsChatteringArcOutOf.eventually_mem_localUnstableSet`](../../SmoothedPolygons/Ch16/ClusterPoint.lean#L921), the second part of Theorem 16.4.1
  time reversed, through Remark 14.3.4).
- The assembly from Theorem 14.4.1 ([`theorem16_3_1_of_theorem14_4_1`](../../SmoothedPolygons/Ch16/NoChattering.lean#L387)) does not: it needs only
  the first part of Theorem 16.4.1, which uses only the derivative of the extended map at `q_out`.
- A shorter route to Theorem 14.4.1 would free Mahler's First conjecture from the theorem
  (Section 11).

## Named hypotheses, all proved

Nothing is assumed: no result from prior work, and no result or computation of the book. The
following are named propositions, all proved:

- the facts that the book reads off computations;
- Theorem 14.4.1;
- and, for the last step of Theorem 16.3.1, a consequence of Theorems 16.4.1 and 14.4.1.

The four computed facts are each proved without computer assistance, by the user's decision
(Section 7):

| Fact | Where the paper uses it | The book's source | In the formalization | How it is proved |
| --- | --- | --- | --- | --- |
| N4: the forward orbit of every point of the local unstable curve over `q_out` with `r > 0` switches cyclically and then leaves the star domain before its next switch | the proof of Theorem 14.4.1 ("This does not happen, because the unstable curve hits the boundary of the star domain", TeX 12009–12010), and through it the last step of the proof of Theorem 16.3.1 (TeX 12828–12830) | Figure 14.2, the global unstable curve `W^u(q_out)` computed in Mathematica, and the running text read off it (TeX 11951–11991), not certified (E88) | [`UnstableCurveLeavesStarDomain`](../../SmoothedPolygons/Ch14/UnstableCurve.lean#L174), proved as [`unstableCurveLeavesStarDomain`](../../SmoothedPolygons/Ch14/ArcRegionInvariant.lean#L338); [`theorem14_4_1`](../../SmoothedPolygons/Ch14/NoReturnProof.lean#L170) derives Theorem 14.4.1 from it | the Reinhardt flow along an `e₂`-arc in closed form, the Reinhardt–Poincaré map as an explicit map of four parameters, and an explicit region of section points that one step keeps until an arc leaves the star domain ((INV), [`arcRegionInvariant`](../../SmoothedPolygons/Ch14/ArcRegionInvariant.lean#L326)) |
| `F` maps `𝒟_out = 𝒟₀₀` into itself, and an iterate `F^N` maps `𝒟₀₀` into a box `B` of the open first big cell on which `F`, in the cell coordinates, is a self-map with Lipschitz constant `κ < 1` | the row `𝒟_out` of Table 16.1, and steps (a) and (d) of the proof of Theorem 16.1.1 (TeX 12592–12607, 12728–12743) | the containment, by the boundary method and Figure 16.1 (Mathematica); the contraction is the repair of E78 (the book has only "the forward iterates `F₁^k(𝒟_out)` quickly shrink toward `q_out`") | [`TriFuller.DOutContracts`](../../SmoothedPolygons/Ch16/BasinHypotheses.lean#L236), proved as [`TriFuller.dOutContracts`](../../SmoothedPolygons/Ch16/DOutContraction.lean#L912), with `B ≈ [0.22, 0.30] × [0.080, 0.199] × [2.688, 3.009]`, `N = 2` and `κ = 3/4` | identities at the root of the switching function, polynomial inequalities on a polytope of rescaled variables, and the mean value inequality, with the partial derivatives bounded by an interval chain on one box |
| every point of the second big cell, its top face included, reaches `𝒟₀₀` within three steps | the rows `𝒟₂` and `𝒟₃` of Table 16.1 and `F²𝒟₃ ⊂ 𝒟₀₀`, in the descent of the proof of Theorem 16.1.1 (TeX 12614–12665, 12738–12741) | Figure 16.2 (the convex hull of a planar projection of sampled images of `𝒟₃`), with `𝔦(𝒟₂) = 𝒟₂` and `θ₂ ∈ [-π/3, 0]` on `𝒟₂`, read off Figure 15.3 | [`TriFuller.CellTwoEntersDOut`](../../SmoothedPolygons/Ch16/BasinHypotheses.lean#L260), proved as [`TriFuller.cellTwoEntersDOut`](../../SmoothedPolygons/Ch16/CellTwoEntersDOut.lean#L456) | identities and the signs of the two switching functions along `ζ²`, without the parts `𝒟₂`, `𝒟₃` and without the involution |
| from a box `𝒟_ij` of the first big cell, `(i, j) ≠ (0, 0), (2, 2)`, every point not in the second big cell is mapped into the second big cell or into a box `𝒟_kℓ` with `(k, ℓ)` lexicographically before `(i, j)` | the subclaims and the row `𝒟₄` of Table 16.1, in the descent (TeX 12612–12615, 12680–12726, 12738–12741) | Figures 16.3–16.4 (convex hulls of planar projections of sampled images), and `𝔦(𝒟₃) = 𝒟₄`, read off Figure 15.2 | [`TriFuller.BoxSubclaims`](../../SmoothedPolygons/Ch16/BasinHypotheses.lean#L278), proved as [`TriFuller.boxSubclaims`](../../SmoothedPolygons/Ch16/BoxSubclaims.lean#L526) | for each box, one identity at the root of the switching function, and signs |

The results that use the facts are also stated with them as hypotheses; the unconditional forms
apply them to the proofs:

| Result | Hypotheses | Unconditional form |
| --- | --- | --- |
| [`theorem16_1_1`](../../SmoothedPolygons/Ch16/GlobalBasin.lean#L599) | the three facts of Table 16.1 | [`theorem16_1_1_unconditional`](../../SmoothedPolygons/Ch16/BasinFacts.lean#L53), in [`SmoothedPolygons/Ch16/BasinFacts.lean`](../../SmoothedPolygons/Ch16/BasinFacts.lean) |
| [`theorem16_2_1`](../../SmoothedPolygons/Ch16/OutwardFuller.lean#L567) | the three facts of Table 16.1 | [`theorem16_2_1_unconditional`](../../SmoothedPolygons/Ch16/BasinFacts.lean#L60), in [`SmoothedPolygons/Ch16/BasinFacts.lean`](../../SmoothedPolygons/Ch16/BasinFacts.lean) |
| [`theorem16_4_1`](../../SmoothedPolygons/Ch16/ClusterPoint.lean#L1021) | the three facts of Table 16.1 | [`theorem16_4_1_unconditional`](../../SmoothedPolygons/Ch16/BasinFacts.lean#L71), in [`SmoothedPolygons/Ch16/BasinFacts.lean`](../../SmoothedPolygons/Ch16/BasinFacts.lean) |
| [`theorem14_4_1`](../../SmoothedPolygons/Ch14/NoReturnProof.lean#L170) | N4 | [`theorem14_4_1_unconditional`](../../SmoothedPolygons/Ch16/MahlerFirstArcRegion.lean#L51), in [`SmoothedPolygons/Ch16/MahlerFirstArcRegion.lean`](../../SmoothedPolygons/Ch16/MahlerFirstArcRegion.lean) |

Theorem 16.4.1 uses the three facts only through Theorem 16.1.1, which its proof cites
(TeX 13041, 13047).

The hypothesis of the conditional form of Theorem 16.3.1, [`NoChatteringIntoSingularLocus`](../../SmoothedPolygons/Ch16/MahlerFirst.lean#L110), the
hypothesis of [`theorem16_3_1`](../../SmoothedPolygons/Ch16/MahlerFirst.lean#L349), is proved ([`noChatteringIntoSingularLocus`](../../SmoothedPolygons/Ch16/MahlerFirstArcRegion.lean#L59)). It follows from Theorems
16.4.1 and 14.4.1 ([`noChatteringIntoSingularLocus_of_theorem14_4_1`](../../SmoothedPolygons/Ch16/NoChattering.lean#L376), E89), which are proved.

The hypothesis is stated for every Pontryagin extremal of the Reinhardt problem on `[0, T]`, with
the boundary conditions of Problem 3.6.2 and the transversality conditions, that is edge extremal,
and for every time `t ∈ (0, T]` at which its lift meets `𝒮_sing`.

It says that there is no interval `(t - δ, t)` with the three properties of
[`IsChatteringInto`](../../SmoothedPolygons/Ch16/MahlerFirst.lean#L60):

- the lift avoids `𝒮_sing` on it;
- the control is bang-bang on it, with finitely many switches on every compact subinterval;
- the switching times accumulate at `t`.

A switching time is a time on each side of which the control is almost everywhere constant at a
vertex, with different vertices ([`IsSwitchingTime`](../../SmoothedPolygons/Ch16/MahlerFirst.lean#L50)).

The derivation is the book's argument, made precise (E89):

1. at `t` the lift is in `𝒮_sing`, so the extremal is normal (Lemma 8.2.2) and its costate is
   normalized to `λ_cost = -1`;
2. the transversality conditions extend it periodically (Remark 6.6.1), so that it meets
   `𝒮_sing` again at `t + T` and chatters into it from the left;
3. after the last meeting time `e` before `t + T` the switching points form a chattering arc,
   finitely bang-bang by Theorem 8.3.2 on each period, glued at `T`;
4. by Theorem 16.4.1 their angular components converge to `q_in`;
5. and by Theorem 14.4.1, second part, on `[e, t +
   T]`, the lift does not meet `𝒮_sing` at `e`, a contradiction ("Thus, the trajectory is not
   periodic. This is contrary to the boundary conditions").

The restriction to edge-extremal extremals weakens the hypothesis:

- the book uses the argument only for the minimizer, which is edge extremal (Proposition 8.1.3);
- the proof of Theorem 14.4.1 needs the trajectory between two meetings to be bang-bang, which
  Chapter 8 gives only under edge extremality.

The boundary conditions matter: near `𝒮_sing`, trajectories that chatter into it exist (the
inward spirals along the stable curve of `q_in` in Chapters 13–16).

With Chapters 2–8 the hypothesis excludes every meeting of the minimizer's lift with `𝒮_sing`
(E60).

The three facts of Table 16.1 are stated in
[`SmoothedPolygons/Ch16/BasinHypotheses.lean`](../../SmoothedPolygons/Ch16/BasinHypotheses.lean), each with its TeX source, and proved in the
modules `DOut*`, `CellTwo*`, `CellOneToDOut` and `Box*` of [`SmoothedPolygons/Ch16/`](../../SmoothedPolygons/Ch16).

- They are about the Poincaré map `F_ang` of `Ξ_{𝒲,0}/V_T` ([`TriFuller.poincareAngZero`](../../SmoothedPolygons/Ch13/PoincareMap.lean#L539), which
  switches when the first control stops being optimal), at every point, faces included:
  - of the closed boxes `𝒟_ij` of the first big cell ([`TriFuller.boxSet`](../../SmoothedPolygons/Ch16/BasinHypotheses.lean#L103), with the index of
    E76);
  - and of the second big cell with its top face ([`TriFuller.cellTwoSet`](../../SmoothedPolygons/Ch15/CellCoordinates.lean#L260)).
- They merge rows of Table 16.1 so that the curved parts `𝒟₀, …, 𝒟₄` of Chapter 15 and
  Proposition 15.3.2 are not needed (E77, Section 7).
- The statement review found that they claim no more than the book: at a face point where the
  cell's control is not the first control, the map equals `F` at an equivalent point of a box no
  larger.
- Before the proofs, an independent implementation in mpmath (60 to 120 digits; about 1.1 million
  evaluations of the map, on the faces, at offsets down to `10⁻¹⁵` from them and on lines across
  the loci where the switch changes) found no violation.
- In it, the big cell in which an image lands was always decided by the control that beats the
  first control. The proofs decide it the same way, by signs of switching functions, so the walls
  between the two cells need no metric margin.
- One step does not suffice in `DOutContracts`: `F(𝒟₀₀)` lies in no compact box of the open cell
  (E78).
- Proposition 15.3.2 is a named proposition too ([`TriFuller.Proposition15_3_2`](../../SmoothedPolygons/Ch15/Involution.lean#L892)), proved in part,
  and no result uses it (Section 9).

N4 is stated in [`SmoothedPolygons/Ch14/UnstableCurve.lean`](../../SmoothedPolygons/Ch14/UnstableCurve.lean), orbit-wise, as the proof of Theorem
14.4.1 uses it (Section 6), and proved in the modules `Arc*` and `VertexPoissonBracket` of
[`SmoothedPolygons/Ch14/`](../../SmoothedPolygons/Ch14).

Their numbering of the steps is defined in the docstring of
[`SmoothedPolygons/Ch14/ArcRegionInvariant.lean`](../../SmoothedPolygons/Ch14/ArcRegionInvariant.lean):

- Proposition 1.1 … Theorem 5.2 for the reduction of N4 to the single-step statement (INV);
- INV Theorem 1 … INV Theorem 2 for the proof of (INV).

## Standard facts used without citation

| Fact | Where | In the formalization |
| --- | --- | --- |
| Iwasawa decomposition of `SL₂(ℝ)` | proof of Lemma 4.1.1 | proved for `SL₂(ℝ)` in the proof of [`lemma4_1_1`](../../SmoothedPolygons/Ch4/AdjointOrbit.lean#L134) |
| Orbit–stabilizer for `SL₂(ℝ)` acting on `𝔥` and on `O_J` | Lemma 4.2.1 | proof of [`lemma4_2_1`](../../SmoothedPolygons/Ch4/AdjointOrbit.lean#L254) |
| The tangent space of an adjoint orbit is spanned by the infinitesimal generators `[Y, X]` | Lemma 4.2.3 (E18) | [`orb_adImage_eq_perp`](../../SmoothedPolygons/Ch4/AdjointOrbit.lean#L388) and the proof of [`lemma4_2_3`](../../SmoothedPolygons/Ch4/AdjointOrbit.lean#L432) |
| Centralizer of a regular element of `𝔰𝔩₂` is one-dimensional | Lemma 4.2.3, Theorem 7.5.1 | [`orb_centralizer`](../../SmoothedPolygons/Ch4/AdjointOrbit.lean#L316), [`str_centralizer`](../../SmoothedPolygons/Ch7/StrongTransversality.lean#L665) |
| Rademacher's theorem | Corollary 3.1.10 | Mathlib (`LipschitzWith.ae_differentiableAt`) |
| `det exp(X) = exp(tr X)` | Lemma A.6.4 | proved for real `2 × 2` matrices (Mathlib lacks it) |
| Möbius transformations map generalized circles to generalized circles | discussion before Lemma 7.2.1 | [`UpperHalfPlane.genCircle_smul`](../../Basic/Analysis/Complex/UpperHalfPlane/GeneralizedCircle.lean#L72) in [`Basic/`](../../Basic) |
| Blaschke selection theorem | proof of Lemma 2.2.5 | Mathlib (`TopologicalSpace.NonemptyCompacts.isCompact_subsets_of_isCompact`) |
| Existence of a critical lattice (Mahler's compactness theorem) | proof of Theorem 2.3.9 (E7) | proved in the plane: [`PlaneLattice.exists_admissible_covolume_le`](../../Basic/Algebra/Module/ZLattice/PlaneCritical.lean#L288) in [`Basic/`](../../Basic) |
| Separating hyperplane theorem | proof of Lemma 2.2.1 | Mathlib (`geometric_hahn_banach_*`) |
| Uniqueness of solutions of linear ODEs | §7.1 general solutions, Theorem 7.5.1 | [`Matrix.ODE_solution_unique_of_bound`](../../Basic/Analysis/Calculus/MatrixFTC.lean#L281) and relatives in [`Basic/`](../../Basic) (Grönwall) |
| Implicit and inverse function theorems | proof of Theorem 7.7.1 (TeX 6588–6591, 6616); the smoothness of `F_ang` near `q_out` in Lemma 13.5.5 (E68) | Mathlib (`HasStrictFDerivAt.implicitFunctionOfProdDomain`; local injectivity from `ApproximatesLinearOn`; `ContDiffAt.implicitFunction`) |
| Parameterization by arclength of the boundary of a convex disk with a unique support line at each boundary point, as a regular `C¹` curve | §2.4, the standing assumption for `K_min` (TeX 2157–2158) | proved for worst disks in [`IsWorstDisk.exists_isBalancedPair`](../../SmoothedPolygons/Ch6/WdBoundaryParam.lean#L437), with the inverse of the arclength from [`exists_inverse_of_hasDerivAt_pos`](../../Basic/Analysis/Calculus/DerivInverse.lean#L29) in [`Basic/`](../../Basic) (E47) |
| The faces of a triangle other than itself are its vertices and its edges | Lemma 8.2.1 (TeX 7121–7123) | proved in the proof of [`lemma8_2_1`](../../SmoothedPolygons/Ch8/SingularLocus.lean#L586) |
| A plane curve with nonvanishing velocity and zero curvature lies on a line | §7.2 (TeX 5615–5621), in Remark 8.3.3 | proved in the proof of [`remark8_3_3`](../../SmoothedPolygons/Ch8/PolygonBoundary.lean#L846): `det(w(c), w)²/\|w\|²` has zero derivative, for the velocity `w` (Section 11) |
| Solutions of differential equations with analytic right-hand sides are analytic | proof of Lemma 8.3.4 (TeX 7637) | not used: Taylor expansions with remainder, by the mean value inequality, in the proof of [`lemma8_3_4`](../../SmoothedPolygons/Ch8/VertexControl.lean#L662) (E59) |
| Near `0⁺` a real polynomial has the sign of its lowest nonzero coefficient | proof of Lemma 13.2.6 (TeX 10978–11008), Corollary 13.2.7 | for cubics, [`exists_forall_Ioc_cubic_pos`](../../Basic/Analysis/Polynomial/SignNearZero.lean#L27) in [`Basic/`](../../Basic) |
| Linearized stability for maps (Lyapunov/Perron): a fixed point at which the derivative has all eigenvalues of modulus `< 1` is asymptotically stable | Lemma 13.5.5 (TeX 11443–11453) | [`Function.isAsymptoticallyStable_of_hasFDerivAt`](../../Basic/Dynamics/LinearizedStability.lean#L73) in [`Basic/`](../../Basic) (Mathlib has no stability theorem for maps) |
| Descartes's rule of signs: the number of positive roots of a real cubic | §15.2 and §15.3 (TeX 12229–12231, 12413–12415) | for the two sign patterns that occur: `a < 0 < c, d` (one positive root, a sign change, [`exists_pos_root_cubic_of_neg_of_pos_of_pos`](../../Basic/Analysis/Polynomial/CubicRoots.lean#L105)) and `a, d > 0 > c` with discriminant `≥ 0` (two positive roots, [`Polynomial.card_roots_filter_pos_eq_two`](../../Basic/Analysis/Polynomial/CubicRoots.lean#L281)), in [`Basic/`](../../Basic); Mathlib has the bound `Polynomial.roots_countP_pos_le_signVariations`, not the exact count for a real-rooted cubic |
| The roots of a polynomial depend continuously on its coefficients | §15.1–15.3, the continuity of the switching time and of `F_A`, `F_B` (TeX 12139–12143, 12233–12276, 12419–12422; E70) | the least positive sign change of a jointly continuous family of real functions depends continuously on the parameter ([`tendsto_sInf_pos_zeros_of_signChange`](../../Basic/Analysis/Polynomial/LeastPositiveRoot.lean#L60)), and so does a simple least positive root of a family of real polynomials ([`Polynomial.tendsto_sInf_pos_roots_of_simple`](../../Basic/Analysis/Polynomial/LeastPositiveRoot.lean#L118)), in [`Basic/`](../../Basic); Mathlib has only a one-sided form (`Polynomial.exists_roots_norm_sub_lt_of_norm_coeff_sub_lt`) |
| Division of a convergent power series by a power of one variable | Lemma 14.3.1, Steps 3 and 7 ("by division of power series", TeX 11800–11806; the divisibility of TeX 11845–11848) | [`AnalyticAt.exists_eq_pow_smul_of_isBigO`](../../Basic/Analysis/Analytic/DivisionByCoordinate.lean#L281) in [`Basic/`](../../Basic), for a complete space of values (the statement review found the lemma false without completeness, and it was corrected before the proofs) |
| The solutions of a linear differential equation with constant coefficients are matrix exponentials, analytic in the time and the initial data | Lemma 14.3.1, Step 2 ("given by matrix exponentials and are hence analytic", TeX 11793–11797) | [`analyticAt_matrix_exp_apply`](../../Basic/Analysis/Analytic/MatrixExp.lean#L47) and [`eq_exp_smul_apply_of_hasDerivAt`](../../Basic/Analysis/Analytic/MatrixExp.lean#L85) in [`Basic/`](../../Basic), from Mathlib's analyticity of the exponential (`NormedSpace.exp_analytic`) |
| The analytic implicit function theorem; the identity theorem for analytic maps | Lemma 14.3.1, Steps 5 and 10 (TeX 11814–11821, 11869–11870) | Mathlib (`ContDiffAt.implicitFunction` with `n = ω`; `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`) |
| Weierstrass preparation | §16.4.2 (TeX 12908–12942) | not used: the repair of §16.4.2 needs no Weierstrass polynomial (E90) |
| The local structure at a hyperbolic fixed point: a sequence that follows the map near the point, where a hyperplane through it is invariant, the map expands transversally and contracts along the hyperplane, and the transverse coordinate tends to `0`, does not cluster at the point | Theorem 16.4.1, steps (c) and (f) ("contradicts the local structure of the stable and unstable manifolds at `q_out`", TeX 13050–13052) | [`Function.not_mapClusterPt_of_transverse_expansion`](../../Basic/Dynamics/HyperbolicBox.lean#L117) in [`Basic/`](../../Basic), the hyperbolic box (E91) |
| Verified interval arithmetic | Table 16.1 (computed in Mathematica, E77) | not needed: the facts are proved analytically (Section 7). The derivative bounds behind the Lipschitz bound of `DOutContracts` ([`SmoothedPolygons/Ch16/DOutDerivativeBounds.lean`](../../SmoothedPolygons/Ch16/DOutDerivativeBounds.lean)) are written out by hand in its docstring: 47 products of two intervals with endpoints of at most four digits, and sums, each checked by `norm_num` or `linarith`; the mean value inequality for a map defined through an implicit root, which it feeds, is [`Basic/Analysis/Calculus/MeanValueImplicit.lean`](../../Basic/Analysis/Calculus/MeanValueImplicit.lean) in [`Basic/`](../../Basic). Mathlib has no interval arithmetic |

## Does the paper use each cited result correctly?

| Cited result | Where | Verdict |
| --- | --- | --- |
| Fejes Tóth's theorem | Theorem 2.1.3; proof of Theorem 2.2.2 | Correct. |
| Gruber, Cor. 30.1 | Definition 2.1.2 | Correct; the packing hypothesis is not needed (Section 5). |
| Minkowski, Mahler (critical lattices) | Theorem 2.3.6 | Correct, with the sources' definition of a critical lattice (E6); the cited paper of Mahler (1946) states only part of it, quoted from Minkowski (E33). |
| Mahler 1947, Theorems 1 and 2 | Theorem 2.3.7, proof of Theorem 2.3.9 | Correct. |
| Mahler 1947, Lemma 3 | remark after Definition 2.3.5 | Correct. Mahler states it without proof; the papers on which its proof rests (paper A and Mahler 1946) have errors and gaps, none fatal, repaired in the formalization, which proves the lemma in full (Section 7). |
| Blaschke selection theorem | proof of Lemma 2.2.5 | Correct, but not sufficient alone for the existence of `K_min` (E4). |
| Hales 2011, Lemmas 11, 17, 18 | proofs of Lemmas 2.4.2, 2.4.3 (recalled) | The recalled arguments have gaps (E8, E9), filled here. |
| Shifrin, Proposition 3.8 | proof of Lemma 2.4.6 | Applied outside its hypotheses (smooth curves); replaced by a direct argument (E11). |
| Pach–Agarwal, Exercise 3.2 and Theorem 2.5 | remarks in §2.1, §2.2 | Not used in proofs. |
| Euler–Arnold equations for left-invariant Hamiltonians (Cushman–Bates) | proof of Proposition 6.5.1 (TeX 5030–5040) | Correct conclusion `Λ₁' = [Λ₁, X]`; the identification of `ad*` with `-ad` is inconsistent with the book's own definition of `ad*` (E22). Proved here in the form the book uses ([`External.euler_arnold`](../../External/EulerArnold.lean#L72)). |
| Iwasawa decomposition | proof of Lemma 4.1.1 | Correct. |
| Rademacher's theorem | Corollary 3.1.10 | Correct. |
| Jurdjevic (attribution) | Definition 6.3.1, Proposition 6.4.1, Corollary 6.5.3 | The book proves Proposition 6.4.1 (in one line) and Corollary 6.5.3 (by differentiation); correct. |
| Pontryagin maximum principle (Agrachev–Sachkov; the bibliography names Zelikin first, E33) | §6.2, §6.6, Problem 6.7.1; the proof of Proposition 8.1.3 (TeX 6791) | Correct for the Reinhardt problem, with the readings of Section 6. The book's summary states it for a smooth manifold and a closed control set; its source needs `∂f/∂q` jointly continuous in `(q, u)` (Agrachev–Sachkov's (10.4), which the summary omits) and, tacitly, locally bounded velocities `f(q, u(t))`, which a compact control set gives. Both hold for the Reinhardt problem (smooth dynamics on `GL₂⁺(ℝ) × C`, compact `U_T`). Applied with the full boundary conditions, its conclusions hold for every admissible trajectory with a covector whose reduced costate vanishes (E21); applied with the boundary conditions written without the two equations that first integrals make redundant, it gives the extremal lift of a minimizer, with nontrivial reduced costate ([`exists_isPontryaginExtremal_of_isReinhardtMinimizer`](../../SmoothedPolygons/Ch6/MatrixExtremal.lean#L564)). The source's proof has three gaps, repaired in the formalization (Section 7). In Proposition 8.1.3 the principle is applied to the edge control problem (an open subset of `ℝ³`, fixed endpoints, free terminal time), which it covers; what the book leaves out is how the minimizer's edge arc minimizes, locally, the cost of the edge problem (E48). |
| Filippov's theorem (no source given; Agrachev–Sachkov, Thm 10.1) | Theorem 6.1.1, its application in §6.1 | The existence of an optimal control needs the convexity of the velocity sets extended by the cost, which holds for the Reinhardt problem, whose cost depends only on the state (E35). The application in §6.1 is outside the theorem as stated: the initial point `X(0)` is free and the endpoints are coupled, and the cut-off that gives the fields compact support changes the minimizers. The form with a closed state constraint, a compact set of initial points and a closed endpoint relation, proved by the same argument, applies (E46). |
| Gronwall's inequality (Appendix A.1, from Amann) | §6.1, the bound on `g` (TeX 4584–4586); through Corollary A.1.3, Lemma 8.1.5 (TeX 7008) and the proof of Theorem 8.3.1 (TeX 7539, 7572) | Correct. Corollary A.1.3, which the book derives from it without proof, is stated for `t ≥ 0` and applied on both sides of `0`; the case `t < 0` follows by reversing time (E61). The formal proofs use its case with constant coefficients, proved in the OptimalControl package (`ControlSystem.le_mul_exp_of_le_add_integral`). |
| Reinhardt 1934, existence of a minimizer | §6.1 (TeX 4569–4572) | Not what §6.1 needs: Reinhardt's theorem gives `K_min`, a disk, not a minimizer of the control problem, and the book does not prove that the two correspond (E47). The formal existence proof does not use it; the identification with `K_min` does, as proved with Lemma 2.2.5 (E4). |
| Sussmann's Noether theorem | Theorem 9.1.4; the proof of Theorem 9.1.6 (TeX 7963–7965) | Misquoted: Definition 9.1.1 drops Sussmann's condition (ii), the invariance of the cost, and the theorem as printed is false (E95). The application is correct: the rotations preserve the dynamics and the cost `-(3/2)⟨J, X⟩` of the circular problem and permute the controls of `U_C`. It is applied to the full costate of `T*(T SL₂(ℝ))`, which the formalization lifts from the reduced one (Section 7). |
| Irwin's stable manifold theorem (Theorem A.3.1) | Theorem 14.3.3 ("By general theory", TeX 11917–11918), Remark 14.3.4, the proof of Theorem 16.4.1 ("by the definition of the stable manifold", TeX 13002–13003) | Correct, in its local part, which is all the book uses. Appendix A.3's local stable set omits that the orbit stays in `U`, which the iterates of `f\|_U` require (E92). The theorem gives the `C^∞` unstable curve; that the local stable manifold is the exceptional divisor does not follow from it alone, is not argued in the book, and is proved directly (E86). The global (immersed) part is not used. Proved in the StableManifold package ([`theoremA_3_1`](../../SmoothedPolygons/AppA/StableManifold.lean#L186)). |

The other citations of the formalized chapters give context and are not used in proofs:

- Reinhardt 1934 apart from §6.1, Minkowski's other works, Hales 2017, Jurdjevic 2016, Perelomov,
  Babelon et al., Colombo–de Diego, Gay-Balmaz et al., Vajjha's thesis;
- in Chapter 8:
  - Hartl, Sethi and Vickson's survey of maximum principles with state constraints, cited in
    Remark 8.1.6;
  - Mahler's second-variation proof that the circle is not a local minimizer, cited before
    Theorem 8.2.7, whose proof gives its own computation;
- in Chapter 9, Abraham and Marsden's *Foundations of Mechanics*, for the general theory of
  momentum maps;
- in Chapter 14, the inverted pendulum paper of Manita and Ronzhina named in Remark 14.2.2, whose
  citation is commented out (E82).

Vajjha's thesis is cited for the omitted proof of Theorem 6.8.3. Lemma A.1.2 (Clarke) is not used.
