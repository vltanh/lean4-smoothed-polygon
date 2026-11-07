# Audit of the paper and the formalization

Paper: Thomas Hales and Koundinya Vajjha, *Packings of Smoothed Polygons*,
[arXiv:2405.04331v1](https://arxiv.org/abs/2405.04331) (7 May 2024, a 283-page book). The audit
was made against the arXiv LaTeX source of that version (the only one). Chapter, section, result
and equation numbers are the book's; TeX line numbers refer to its source file `chapter2.tex`.

Status of the formalization:

- **Scope.** The formalization covers the book's smoothed-polygon core and its geometric
  foundations, chosen with the user: the historical results on packings, lattices and the
  boundary of the minimizer (Chapter 2), the Reinhardt optimal control problem (Chapter 3), the
  upper half-plane model (Chapter 4), the Hamiltonian and costate equations (Chapter 6), the
  bang-bang solutions and the smoothed `(6k+2)`-gons (Chapter 7), and Appendix A.6 and A.11. A
  fourth round, the first layer of a plan for the book's remaining chapters (5 and 8–16), added
  the Pontryagin maximum principle, which the book cites in §6.2, and the claim of §6.2 that
  every minimizer of the Reinhardt problem lifts to a Pontryagin extremal. The book's main theorem,
  Mahler's First conjecture (Theorem 16.3.1), and Chapters 1, 5, 8–16 are not formalized
  (Section 9).
- **Proved.** Every numbered result of Chapters 2, 3, 4, 6 and 7 is formalized and proved, among
  them Filippov's theorem (Theorem 6.1.1, cited without a source), Proposition 6.4.1 with
  Definition 6.3.1 (general left-invariant systems, on Mathlib's Lie groups) and Theorem 7.7.1 (the
  smoothed octagon is an isolated extremal), whose proof the book only sketches. So are the remark
  after Definition 2.3.5 (the book's irreducibility is Mahler's), the action of the dihedral group
  on the ideal vertices of `𝔥*` (§4.6), Remarks 2.2.4, 6.6.1, 7.5.2 and 7.6.4, which the book states
  without proof, and the claim of §6.2 and §6.6, used in the proof of Proposition 8.1.3 ("We have
  seen that the global minimizer must be extremal", TeX 6791), that every minimizer of the
  Reinhardt control problem lifts to a Pontryagin extremal; that a minimizer exists rests on
  Chapter 5 and is not yet proved. Lemma 2.2.1 is false as printed and Theorem 7.7.1 is false
  read literally (E1, E32); Lemma 3.1.8 and the existence claim of Theorem 6.1.1 lack a hypothesis (E34, E35); all
  four are proved in corrected forms approved by the user. What is left within these chapters is
  conjectural or rests on Chapter 5 (Section 9). The main results are Theorem 7.5.6 (each smoothed
  `(6k+2)`-gon is a Pontryagin extremal of the Reinhardt control problem with bang-bang control),
  the smoothed octagon's packing density (the octagon's trajectory bounds a balanced disk `K` whose
  area is the cost `√12(8 - √32 - ln 2)/(√8 - 1)` and whose greatest packing density is
  `δ(K) = (8 - √32 - ln 2)/(√8 - 1)`), Theorem 7.7.1, and the lift of every minimizer to an
  extremal ([`exists_isPontryaginExtremal_of_isReinhardtMinimizer`](SmoothedPolygons/Ch6/MatrixExtremal.lean#L587)).
- **Nothing is assumed.** Every cited result that a proof uses is proved: Fejes
  Tóth's theorem (`δ = δ_L`), Gruber's lattice density formula, the theorems of Minkowski and
  Mahler on critical lattices and circumscribed hexagons, Mahler's Lemma 3 on irreducible domains
  (in full, along the two papers of Mahler on which its proof rests, with their errors and gaps
  repaired), the Euler–Arnold equation and the Pontryagin maximum principle (Section 2).
  Filippov's theorem, which no proof uses, is proved too. All are stated in [`External/`](External). The
  maximum principle and Filippov's theorem are proved in the OptimalControl package
  ([github.com/vltanh/lean4-optimal-control](https://github.com/vltanh/lean4-optimal-control),
  required at a pinned commit), the maximum principle by Agrachev and Sachkov's own argument, with
  Brouwer's fixed-point theorem from the FixedPoint package
  ([github.com/vltanh/lean4-fixed-point](https://github.com/vltanh/lean4-fixed-point)). A
  Pontryagin extremal is defined by the conditions of the maximum principle (Section 6), and the
  maximum principle shows that every minimizer is one. Theorem 3.1.4(3) keeps one hypothesis for a
  general convex disk (E13, approved by the user); for balanced disks it holds.
- **Build.** `lake build` succeeds; the only `sorry`s are the two statements of [`Challenge.lean`](Challenge.lean),
  by design. There is no `axiom`, `admit` or `native_decide`. [`scripts/Audit.lean`](scripts/Audit.lean) checks that every
  declaration of the library and the two Challenge theorems depend only on [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext),
  [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound). Palomar's Comparator accepts [`Solution.lean`](Solution.lean) against
  [`Challenge.lean`](Challenge.lean) under Lean's kernel and NanoDa.
- **Statements.** Two results of the book are false as stated and are formalized in corrected
  form, approved by the user: Lemma 2.2.1, with a machine-checked counterexample to the printed
  statement (E1), and Theorem 7.7.1, which holds only up to time translation and for terminal times
  near `t_f` (E32). Nine further statements and definitions are corrected: a definition missing a
  hypothesis (Definition 2.3.4, E6), two misprints in definitions (E16, E20), the nontriviality
  condition of a Pontryagin extremal, which the maximum principle yields only for boundary
  conditions written without two redundant equations (E21), and missing hypotheses in Theorem
  3.1.4(3) (E13), Lemma 3.1.8 (E34) and Theorem 6.1.1 (E35), each approved by the user, and in Lemma 4.2.3 (E17)
  and Lemma 7.3.1 (E26). Slips in proofs (E8, E14, E24) are corrected where they occur. Otherwise
  the Lean statements differ from the book's only by the omitted hypotheses of Section 5 and the
  readings of Section 6.
- **Proofs.** Every proof follows the book's argument, except the departures listed in Section 7,
  each forced by an error or gap of the book or by mathematics Mathlib lacks: Lemma 2.2.1 (its
  printed form is false), Lemma 2.2.5 (a gap the book's lines cannot close, closed by Mahler's
  lattice route, chosen by the user), one step each of Lemmas 2.4.2 and 2.4.6, the area formula of
  §3.2 (Green's theorem), Jacobi's formula (Lemma 3.1.12, approved by the user), Lemma 4.3.1, the
  boundary conditions to which §6.2 applies the maximum principle (E21), and one step of Theorem
  7.7.1 (the fixed points of the Poincaré map near the octagon's, which the book's argument does
  not give uniformly). The other gaps are filled along the book's lines. The maximum principle is
  proved by Agrachev and Sachkov's argument, with the departures and the three gaps of the source
  listed in Section 7.
  The route check ([`scripts/route_check.py`](scripts/route_check.py) against [`docs/paper_routes.tsv`](docs/paper_routes.tsv)) passes; its recorded differences are
  listed with their reasons in [`docs/route_differences.tsv`](docs/route_differences.tsv) (Section 8).
- **Redundant hypotheses.** Eight results of the book and one cited result hold without some of
  their hypotheses; the Lean statements omit them (Section 5). The Challenge keeps the book's
  hypotheses. Lemma 3.1.8, Proposition 6.4.1 and Filippov's theorem keep hypotheses of the book or
  of the source that their proofs do not use (Section 5).

## 1. Summary

- **Errors.** Lemma 2.2.1 (Reinhardt's tiling lemma) is false as printed: a lattice packing of a
  centrally symmetric disk need not be a tiling by a hexagon or parallelogram containing the disk
  (E1, refuted in Lean). The book uses only a weaker consequence, which holds, so Theorem 2.2.2 and
  everything after it stand. Two misprints change the meaning of a definition: the terminal
  condition of the Reinhardt control problem (E16) and the sign of the coefficient `a(u)` of the
  half-plane control problem (E20). The nontriviality condition of a Pontryagin extremal, imposed on
  the full costate `(Λ₁, Λ₂)`, makes every admissible trajectory an extremal (E21); it must be
  imposed on the reduced costate `(Λ₁, Λ_R)`, as the formalization does, for Theorem 7.5.6 to say
  anything. The maximum principle gives it for a minimizer once the redundancy that the first
  integrals `det X` (and, on the open set where the formalization applies it, `det g`) create in
  the boundary conditions is removed: the formalization leaves out the two redundant equations
  (posing the problem on the adjoint orbit, to which the book cuts the state space in Chapter 4,
  would be another way). Theorem 7.7.1 (the smoothed octagon is an isolated extremal) is false read literally:
  the octagon's lift started at another time, or run for several laps, is another extremal
  satisfying the transversality conditions with a nearby or the same initial condition; it holds up
  to time translation and for terminal times near `t_f` (E32). Slips that do not affect any result:
  the definition of a critical lattice omits admissibility (E6), an equation written too early in
  the proof of Theorem 2.3.9 (E7), a sign in the proof of Lemma 2.4.2 (E8), an index in the proof
  of Lemma 2.4.5 (E10), an index in the proof of Theorem 3.4.2 (E14), a sign convention in the
  proof of Proposition 6.5.1 (E22), the eigenvectors of §7.1 (E24), and the sign of the switching
  functions in the proof of Theorem 7.7.1 (E32).
- **Gaps.** The proof of Lemma 2.2.5 (the minimizer has no corners) has a gap that its shaving
  argument cannot close; the formalization closes it by Mahler's lattice route (E4). The smoothed
  octagon's density value rests on a fact the book never proves, that a balanced disk has least
  circumscribed hexagon of area `√12`; it is true and proved here (E12). The inequality on which the
  maximum principle for the smoothed polygons rests is left "as a tedious but elementary exercise"
  (Lemma 7.5.3, E29): it is true, tight at one corner, and proved here. Lemma 4.3.1 does not justify
  that the minimizer has area less than `π` (E19). Lemma 2.4.6 applies a theorem about smooth
  curves to curves that are only `C¹,¹` (E11). The proof of Theorem 7.7.1 is a sketch: it does not
  argue that nearby extremals switch as the octagon does, does not give the "direct calculation" of
  hyperbolicity, and applies the implicit function theorem in a way that does not give the
  uniformity its conclusion needs; the formalization supplies all three, the last by a different
  argument (E32). Remarks 7.5.2 and 7.6.4 are stated without proof (the second is read off a
  figure), and the smoothed `(6k−2)`-gons of Remark 7.6.2 without the condition that closes them;
  both remarks are true and proved here (E36, E37). So is Remark 6.6.1, that every extremal
  extends to a periodic one, which the book also states without proof (E38). Further gaps, all
  filled: E2, E3, E5, E7, E8, E9, E15, E18, E23, E30, E31, E34.
- **Missing hypotheses.** Theorem 3.1.4(3) is false for a general convex disk; it holds under the
  standing assumptions of §2.4 (E13). Lemma 3.1.8 is false unless the curves are regular, as §2.4
  assumes (E34). Filippov's theorem (Theorem 6.1.1) claims that an optimal control exists when
  the velocity sets are convex; this fails for costs that depend on the control, and holds when the
  velocity sets extended by the cost are convex (E35). Lemma 4.2.3 needs `X ≠ 0` (E17). Lemma
  7.3.1 needs `⟨X, Z_u⟩ ≠ 0` on the control set, which its proof uses (E26).
- **Redundant hypotheses.** Several hypotheses are not needed; the Lean statements drop them
  (Section 5). The most notable: Lemma 7.3.1 holds for every compact convex control set on which
  `⟨X, Z_u⟩ ≠ 0`, not only one in the plane `u₀ + u₁ + u₂ = 1`.
- **Use of cited results.** Chapter 2 rests on cited theorems: Fejes Tóth's `δ = δ_L`, Gruber's
  lattice density formula, Minkowski's and Mahler's theorems on critical lattices and circumscribed
  hexagons, and Shifrin's characterization of convex curves; the control-theoretic chapters cite
  the Pontryagin maximum principle (Agrachev–Sachkov), the Euler–Arnold equations (Cushman–Bates,
  with a sign slip, E22), the Iwasawa decomposition and Rademacher's theorem, and state Filippov's
  theorem without a source (Theorem 6.1.1, E35). All are proved here, in [`External/`](External) (with the
  OptimalControl package) or from Mathlib, except Shifrin's, which is applied outside its
  hypotheses and replaced by a direct argument (E11) (Section 2). The book's summary of the
  maximum principle omits one of its source's regularity hypotheses, which the Reinhardt problem
  satisfies. Agrachev and Sachkov's proof of the maximum principle has three gaps, all repaired
  (Section 7).
- **Literature.** Theorem 7.5.6 was announced in Hales's 2017 preprint, which also sketches another
  proof of Theorem 7.7.1 (Section 10). The book is still an unrefereed preprint, with no newer
  version or erratum. One date in its bibliography is wrong, two citations are to later editions,
  the entry cited for the maximum principle, Agrachev and Sachkov's book, names M. I. Zelikin as
  its first author, and the paper of Mahler cited with Minkowski for Theorem 2.3.6 states only
  part of it, quoted from Minkowski without proof (E33). The proof of the maximum principle in the
  OptimalControl package is, to our knowledge, its first complete formal proof (Section 10).

## 2. Results from prior work and how the paper uses them

### Proved in `External/`

| Cited result | Source | Lean | Used by |
| --- | --- | --- | --- |
| Euler–Arnold equation for left-invariant Hamiltonians on matrix groups, `μ' = [μ, δh/δμ]` for `μ = pg` | Cushman–Bates, cited in the proof of Proposition 6.5.1 | [`External.euler_arnold`](External/EulerArnold.lean#L72) | [`proposition6_5_1`](SmoothedPolygons/Ch6/Hamiltonian.lean#L319) |
| Fejes Tóth's theorem: for a centrally symmetric convex disk, no packing of congruent copies is denser (even in upper density) than the best lattice packing | L. Fejes Tóth 1950; cited as Theorem 2.1.3 | [`External.fejes_toth`](External/FejesToth.lean#L882) | [`theorem2_1_3`](SmoothedPolygons/Ch2/Density.lean#L252) |
| The upper and lower densities of a lattice arrangement of a convex body are `V(C)/d(L)` | Gruber, *Convex and Discrete Geometry*, Cor. 30.1; cited in Definition 2.1.2 | [`External.gruber_corollary_30_1`](External/Gruber.lean#L320) | [`definition2_1_2`](SmoothedPolygons/Ch2/Density.lean#L86) |
| A critical lattice has a basis and a third point on the boundary forming a parallelogram of area `Δ(K)`, and conversely | Minkowski 1907, Mahler 1947 (Lemma 2); cited as Theorem 2.3.6, from Minkowski and Mahler 1946 (E33) | [`External.minkowski_mahler`](External/MinkowskiMahler.lean#L964) | [`theorem2_3_6`](SmoothedPolygons/Ch2/Mahler.lean#L113) |
| The circumscribed hexagon of a critical lattice: unique tac-lines, area `4Δ(K)`, sides bisected, least area | Mahler 1947, Theorems 1 and 2; cited as Theorem 2.3.7 | [`External.mahler_1947`](External/Mahler1947.lean#L1700) | [`theorem2_3_7`](SmoothedPolygons/Ch2/Mahler.lean#L182) |
| A symmetric convex domain is irreducible (no symmetric convex proper subdomain has the same `Δ`) if and only if every boundary point lies on a critical lattice; hence, in an irreducible domain, every tac-line contains a point of a critical lattice, one of the six boundary points of a configuration of Mahler's Lemma 2 | Mahler 1947, Lemma 3, stated there without proof; cited after Definition 2.3.5. Proved along Mahler's paper A and Mahler 1946 (below) | [`External.mahler_irreducible_iff`](External/MahlerIrreducible/Lemma3.lean#L367); [`External.mahler_irreducible`](External/MahlerIrreducible/Lemma3.lean#L383), derived from it | [`isIrreducible_iff_mahlerIrreducible`](SmoothedPolygons/Ch2/Mahler.lean#L99) (the remark after Definition 2.3.5); [`lemma2_2_5`](SmoothedPolygons/Ch2/Reinhardt.lean#L3754) |
| Filippov's theorem: for a control system on `ℝⁿ` with compact control set, convex velocity sets and `f` of compact support, the attainable sets (at time `T` and up to time `T`) are compact, and an optimal control exists for an integral cost when the velocity sets extended by the cost are convex, with fixed or free terminal time | Agrachev–Sachkov, *Control Theory from the Geometric Viewpoint*, Thm 10.1; cited as Theorem 6.1.1 without a source (E35) | [`External.filippov`](External/Filippov.lean#L150) | none: it is Theorem 6.1.1 (its application in §6.1 needs Chapter 5) |
| The Pontryagin maximum principle with free terminal time, an integral cost and mixed boundary conditions `(q(0), q(t_f)) ∈ N` (`N` cut out near the end points by a `C¹` submersion), for strong local minimizers on an open subset of a finite-dimensional space with a compact control set: `ν ≤ 0` and a Lipschitz covector curve `p` with `(ν, p(t)) ≠ 0` for every `t`, the adjoint equation, the maximum condition and `H = 0` almost everywhere, and the transversality condition `(-p(0), p(t_f)) ⊥ T N` | Agrachev–Sachkov, *Control Theory from the Geometric Viewpoint*, Ch. 12, Theorem 12.5 with the remark after it (free time), read in the authors' draft; cited in §6.2 from the entry `zelikin2004control` (E33) | [`External.pontryagin_maximum_principle`](External/Pontryagin.lean#L80), proved in the OptimalControl package (`Pontryagin.maximum_principle`) | [`exists_isPontryaginExtremal_of_isReinhardtMinimizer`](SmoothedPolygons/Ch6/MatrixExtremal.lean#L587) (§6.2 and §6.6: every minimizer is an extremal) |

Mahler 1947 states Lemma 3 without proof and refers to Lemmas 8 and 12 of "paper A", Mahler's *On
irreducible convex domains* (Proc. KNAW 50 (1947) 98–107; the book does not cite it). Paper A
proves its Lemmas 1, 2, 5–7 and 13 and quotes Lemmas 8, 10, 11 and 12 from Theorems B–E of
Mahler's *Lattice points in n-dimensional star bodies II. Reducibility theorems I* (Proc. KNAW 49
(1946) 331–343, the book's entry `mahler1946lattice`). We read both from scans of Mahler's
collected works (CARMA archive, items 094 and 088), and the proof follows them, down to the 1946
paper, as the user chose: paper A's lemmas
are in [`External/MahlerIrreducible.lean`](External/MahlerIrreducible.lean); Theorems B and C, with paper A's Lemmas 10 and 11 and the
class-B case of its Lemma 13, in [`External/Mahler1946/TheoremC.lean`](External/Mahler1946/TheoremC.lean); Theorems D and E, with paper
A's Lemma 12, in [`External/Mahler1946/TheoremE.lean`](External/Mahler1946/TheoremE.lean); and Lemma 3 in
[`External/MahlerIrreducible/Lemma3.lean`](External/MahlerIrreducible/Lemma3.lean). "Only if" is the proof of paper A's Lemma 13: extreme
points of `K` through the proof of Theorem C (paper A's Lemma 10) and a cut by a line, inner points
of boundary segments through paper A's Lemmas 5–7, using that the boundary points on critical
lattices form a closed set (Theorem B, paper A's Lemma 11); "if" is Theorems D and E with paper A's
Corollary to Lemma 5 and Lemma 1. The form that Lemma 2.2.5 uses (each tac-line contains
a point of a critical lattice) follows with paper A's Lemmas 3 and 4. The errors and gaps of the
sources, all repaired, and the two small departures from them are in Section 7.

Filippov's theorem is proved by the standard argument: the trajectories are equi-Lipschitz, a
limit is extracted by Tychonoff's theorem (pointwise convergence suffices, so Arzelà–Ascoli is not
needed), its velocities lie in the closed convex velocity sets (by closed thickenings of them), a
control realizing them is chosen measurably (a Kuratowski–Ryll-Nardzewski selection, proved in
`OptimalControl.MeasureTheory.MeasurableSelection`, in the OptimalControl package; Mathlib has none), and optimal controls come from the
system extended by the cost (`OptimalControl.ODE.ControlSystem`). The proof was written before we
had Agrachev and Sachkov's text and was not compared with theirs; the statement is the book's,
with the source's standing smoothness assumptions on `f` (Section 5) and the correction of E35.

The maximum principle is proved in the OptimalControl package by Agrachev and Sachkov's own
argument (Chapter 12 of their book, read in the authors' draft, with preface dated September
2003, from the first author's home page; page numbers in this report are the draft's), in coordinates on an open
subset of a finite-dimensional space: needle variations at Lebesgue points of the reference
control, transported by the resolvent of the variational equation; Lemma 12.1 (openness at the
vertex of a cone, by Brouwer's fixed-point theorem); Lemma 12.2 and Theorem 12.1 (the geometric
maximum principle, by a covector supporting the cone of variations); and Agrachev and Sachkov's
auxiliary systems for free time, the cost and mixed boundary conditions (Theorems 12.2–12.5),
applied together for free time with a cost, the case the book needs, which the source leaves to
the reader. Brouwer's theorem, which the source uses without reference and Mathlib lacks, is
proved in the FixedPoint package by the analytic argument of Milnor (1978) and Rogers (1980). The
Carathéodory theory beneath (existence, uniqueness and differentiable dependence of solutions for
measurable controls), which the source cites from Gamkrelidze, is proved by Picard iteration and
Gronwall's inequality. [`External/Pontryagin.lean`](External/Pontryagin.lean) states the theorem as the book cites it and takes the
proof from the package; the departures from the source (D1–D11 of the package's README) and its
three gaps are in Section 7.

The book applies the maximum principle in §6.2 and §6.6 to the Reinhardt problem; the
formalization follows it ([`exists_isPontryaginExtremal_of_isReinhardtMinimizer`](SmoothedPolygons/Ch6/MatrixExtremal.lean#L587), in
[`SmoothedPolygons/Ch6/MatrixExtremal.lean`](SmoothedPolygons/Ch6/MatrixExtremal.lean)): the state `(g, X)` lies in the open set `GL₂⁺(ℝ) × C` of
`Mat₂(ℝ) × 𝔰𝔩₂(ℝ)`, with `C` the open cone of the star inequalities (on which `⟨Z_u, X⟩ < 0` for
`u ∈ U_T`, so the dynamics are smooth); a global minimizer of Problem 3.6.2 is a strong local minimizer
there, since `det g` and `det X` are first integrals; the covector of the maximum principle gives
the costates `Λ₁` (the left trivialization `pg`, made traceless) and `Λ_R = [Λ₂, X]`, whose
equations follow from the adjoint equation by Proposition 6.5.1 (with the Euler–Arnold equation);
and the transversality conditions are those of §6.6, the one for `Λ₁` from `g(t_f) = R` by
Corollary 6.5.3, as Remark 6.6.1 says. The one departure, in the boundary conditions, is E21
(Section 7).

### Assumed

None.

### Standard facts used without citation

| Fact | Where | In the formalization |
| --- | --- | --- |
| Iwasawa decomposition of `SL₂(ℝ)` | proof of Lemma 4.1.1 | proved for `SL₂(ℝ)` in the proof of [`lemma4_1_1`](SmoothedPolygons/Ch4/AdjointOrbit.lean#L134) |
| Orbit–stabilizer for `SL₂(ℝ)` acting on `𝔥` and on `O_J` | Lemma 4.2.1 | proof of [`lemma4_2_1`](SmoothedPolygons/Ch4/AdjointOrbit.lean#L254) |
| The tangent space of an adjoint orbit is spanned by the infinitesimal generators `[Y, X]` | Lemma 4.2.3 (E18) | [`orb_adImage_eq_perp`](SmoothedPolygons/Ch4/AdjointOrbit.lean#L388) and the proof of [`lemma4_2_3`](SmoothedPolygons/Ch4/AdjointOrbit.lean#L432) |
| Centralizer of a regular element of `𝔰𝔩₂` is one-dimensional | Lemma 4.2.3, Theorem 7.5.1 | [`orb_centralizer`](SmoothedPolygons/Ch4/AdjointOrbit.lean#L316), [`str_centralizer`](SmoothedPolygons/Ch7/StrongTransversality.lean#L665) |
| Rademacher's theorem | Corollary 3.1.10 | Mathlib (`LipschitzWith.ae_differentiableAt`) |
| `det exp(X) = exp(tr X)` | Lemma A.6.4 | proved for real `2 × 2` matrices (Mathlib lacks it) |
| Möbius transformations map generalized circles to generalized circles | discussion before Lemma 7.2.1 | [`UpperHalfPlane.genCircle_smul`](Basic/Analysis/Complex/UpperHalfPlane/GeneralizedCircle.lean#L72) in [`Basic/`](Basic) |
| Blaschke selection theorem | proof of Lemma 2.2.5 | Mathlib (`TopologicalSpace.NonemptyCompacts.isCompact_subsets_of_isCompact`) |
| Existence of a critical lattice (Mahler's compactness theorem) | proof of Theorem 2.3.9 (E7) | proved in the plane: [`PlaneLattice.exists_admissible_covolume_le`](Basic/Algebra/Module/ZLattice/PlaneCritical.lean#L288) in [`Basic/`](Basic) |
| Separating hyperplane theorem | proof of Lemma 2.2.1 | Mathlib (`geometric_hahn_banach_*`) |
| Uniqueness of solutions of linear ODEs | §7.1 general solutions, Theorem 7.5.1 | [`Matrix.ODE_solution_unique_of_bound`](Basic/Analysis/Calculus/MatrixFTC.lean#L281) and relatives in [`Basic/`](Basic) (Grönwall) |
| Implicit and inverse function theorems | proof of Theorem 7.7.1 (TeX 6588–6591, 6616) | Mathlib (`HasStrictFDerivAt.implicitFunctionOfProdDomain`; local injectivity from `ApproximatesLinearOn`) |

### Does the paper use each cited result correctly?

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
| Euler–Arnold equations for left-invariant Hamiltonians (Cushman–Bates) | proof of Proposition 6.5.1 (TeX 5030–5040) | Correct conclusion `Λ₁' = [Λ₁, X]`; the identification of `ad*` with `-ad` is inconsistent with the book's own definition of `ad*` (E22). Proved here in the form the book uses ([`External.euler_arnold`](External/EulerArnold.lean#L72)). |
| Iwasawa decomposition | proof of Lemma 4.1.1 | Correct. |
| Rademacher's theorem | Corollary 3.1.10 | Correct. |
| Jurdjevic (attribution) | Definition 6.3.1, Proposition 6.4.1, Corollary 6.5.3 | The book proves Proposition 6.4.1 (in one line) and Corollary 6.5.3 (by differentiation); correct. |
| Pontryagin maximum principle (Agrachev–Sachkov; the bibliography names Zelikin first, E33) | §6.2, §6.6, Problem 6.7.1; the proof of Proposition 8.1.3 (TeX 6791) | Correct for the Reinhardt problem, with the readings of Section 6. The book's summary states it for a smooth manifold and a closed control set; its source needs `∂f/∂q` jointly continuous in `(q, u)` (Agrachev–Sachkov's (10.4), which the summary omits) and, tacitly, locally bounded velocities `f(q, u(t))`, which a compact control set gives. Both hold for the Reinhardt problem (smooth dynamics on `GL₂⁺(ℝ) × C`, compact `U_T`). Applied with the full boundary conditions, its conclusions hold for every admissible trajectory with a covector whose reduced costate vanishes (E21); applied with the boundary conditions written without the two equations that first integrals make redundant, it gives the extremal lift of a minimizer, with nontrivial reduced costate ([`exists_isPontryaginExtremal_of_isReinhardtMinimizer`](SmoothedPolygons/Ch6/MatrixExtremal.lean#L587)). The source's proof has three gaps, repaired in the formalization (Section 7). |
| Filippov's theorem (no source given; Agrachev–Sachkov, Thm 10.1) | Theorem 6.1.1, its application in §6.1 | The existence of an optimal control needs the convexity of the velocity sets extended by the cost, which holds for the Reinhardt problem, whose cost depends only on the state (E35); the application also needs Chapter 5's compactification (not formalized). |

The other citations of the formalized chapters (Reinhardt 1934, Minkowski's other works, Hales 2017, Jurdjevic 2016,
Perelomov, Babelon et al., Colombo–de Diego, Gay-Balmaz et al., Vajjha's thesis) give context and
are not used in proofs; Vajjha's thesis is cited for the omitted proof of Theorem 6.8.3.

## 3. Errors and gaps in the paper

E1–E32 follow the order of the book and E33 concerns its bibliography. E34–E37, found when the
remaining results of the formalized chapters were formalized, follow, again in the book's order,
and then E38, found in the fourth round.

**E1. Lemma 2.2.1, §2.2 (TeX 1317–1351): false.** The lemma says that every lattice packing
`K + L` of a centrally symmetric convex disk is realized by a parallelogram or centrally symmetric
hexagon `H_K ⊇ K` whose translates by `L` tile the plane. Counterexample: `L = ℤ²` and
`K = {y | |2y₀ + y₁| ≤ 1, |2y₁ - y₀| ≤ 1}`, a parallelogram of area `4/5` whose translates pack. The
half-lattice points `(±½, 0)`, `(0, ±½)` lie in the relative interiors of the four edges of `K`;
a convex `H ⊇ K` whose translates pack has none of them in its interior, so its support lines
there are those of `K` and `H = K`, which does not tile (area `4/5 < 1 = det L`). The book's
expand–separate–crop process stops at `K` in this example. A hexagonal variant
(`K ∩ {|y₀| ≤ 11/20}`) fails the same way, so excluding parallelograms does not help. The refutation
is proved in Lean for every convex `H ⊇ K` ([`lemma2_2_1_false_as_printed`](SmoothedPolygons/Ch2/TilingCounterexample.lean#L297)). The book uses the lemma only in Theorem 2.2.2,
for which the classical form of Reinhardt's lemma suffices: there is such an `H ⊇ K` whose
translates by `L` form a packing (so `area(H) ≤ det L`). With the user's approval, the
formalization states and proves that form ([`lemma2_2_1`](SmoothedPolygons/Ch2/Reinhardt.lean#L2058), Section 7).

**E2. Theorem 2.2.2, §2.2 (TeX 1382–1392): gap.** The proof takes "a lattice that realizes"
`δ_L(K)` without showing that one exists. It exists: twice a critical lattice of `K` attains
`δ_L(K) = area(K)/(4Δ(K))`, and critical lattices exist (Mahler's compactness theorem in the plane,
proved here); with it the formalization follows the book's proof.

**E3. Remark 2.2.4, §2.2 (TeX ~1435): stated without proof.** That `K` contains an arc of the
hyperbola near each edge midpoint of a critical hexagon is observed, not proved. The formalization
proves it ([`remark2_2_4`](SmoothedPolygons/Ch2/Reinhardt.lean#L3060)): a hyperbola point outside `K` would give, by a separating line and an
AM–GM comparison of triangle areas, a circumscribed hexagon of smaller area.

**E4. Lemma 2.2.5, §2.2 (TeX 1507–1543): gaps; one not repairable along the book's lines.**
(a) The existence of `K_min` "by the Blaschke selection theorem" needs more than selection (a
normalization and the behaviour of `δ_L` in the limit); the formalization normalizes by linear maps
and proves the one-sided bound it needs. (b) The proof that `K_min` has no corners shaves `K` near a
boundary point that lies on no edge of a critical hexagon. This shows only that each face of `K` on a
support line meets the boundary of some critical hexagon. It gives nothing at an endpoint of a flat
boundary segment that lies on an edge of a critical hexagon away from its midpoint, which the proof
needs ("Each endpoint of the segment is the midpoint of an edge of a critical hexagon, for otherwise
it can be shaved as above"); the regular hexagon shows the soft argument cannot rule this out. The
statement is true: the formalization proves it by Mahler's lattice route (Section 7).

**E5. Lemmas 2.2.6 and 2.2.7, §2.2 (TeX 1545–1720): smaller gaps.** Lemma 2.2.6's proof does not
treat a midpoint at the tip `s_j* + s_{j+1}*` of the triangle `T_j`; Lemma 2.2.7's "picking the
interval to be as large as possible" uses the closedness of the set of critical hexagons, which the
book asserts without proof in the proof of Lemma 2.2.5 (TeX 1520–1521). The formalization fills
both along the book's lines.

**E6. Definition 2.3.4, §2.3 (TeX 1766–1770): slip.** A critical lattice is defined as a lattice
whose determinant equals `Δ(K)`, without requiring it to be `K`-admissible. Read literally,
Theorem 2.3.6 is false (for the unit disk and `0 < ε < √3/2`, the lattice spanned by `(ε, 0)` and `(0, √3/(2ε))` has
determinant `√3/2 = Δ` but no basis on the boundary). The sources (Minkowski, Mahler) require
admissibility; the formalization does.

**E7. Theorem 2.3.9, §2.3 (TeX 1888–1916): a tacit fact and a slip.** The proof takes a critical
lattice `L̃` without recalling that one exists (Mahler's compactness theorem; proved in the plane,
[`PlaneLattice.exists_admissible_covolume_le`](Basic/Algebra/Module/ZLattice/PlaneCritical.lean#L288)). It writes `4Δ(K) = det(2L) = area(H_K)` (TeX 1903)
before showing that `L` is critical; at that point only `4 det(L) = det(2L) = area(H_K)` is known,
and the next paragraph shows `det(L) = Δ(K)`. That `H̃_K` is a centrally symmetric hexagon is part of
Theorem 2.3.7 as the book states it, and parallelograms are excluded by the convention of TeX
1356–1357; the formalization proves both, the first because its statement of Theorem 2.3.7 omits it.

**E8. Lemma 2.4.2, §2.4 (TeX 2034–2085): a sign slip and a gap.** The proof says
"In fact, `det(σ₀'(t), σ₂(t)) < 0`" (TeX 2058); it is positive (`σ₁ = σ₀ + σ₂` lies in `K`, to the
left of the tangent at `σ₀`; for the circle it is `1/2`), and positivity is what makes the speed
`s₂` positive. The proof concludes `σ₂ = σ̃₂` for the integral curve `σ̃₂` without showing that `σ̃₂`
stays on the boundary; the formalization proves the differentiability of `σ₂` directly. The
statement allows any `C⁰` multi-curve on the boundary, which the proof identifies tacitly with the
critical-hexagon midpoints; the formalization proves the identification.

**E9. Lemma 2.4.3, §2.4 (TeX 2093–2148): proof sketch.** The proof recalls Hales 2011 in outline; a
comment in the TeX (line 2126) says the details of its final "now follows" are in handwritten notes.
The formalization fills it: the hyperbolic arc of Remark 2.2.4 bounds the turning of the tangent,
uniformly by compactness of the set of multi-points on the boundary with their support directions,
and local bounds give a global Lipschitz bound.

**E10. Lemma 2.4.5, §2.4 (TeX 2165–2202): index slip.** The bound on the side of the ray through
`s_j + s_{j+1}` is argued "Dually" (TeX 2181): pointing beyond it "would force `σ'_{j+2}(t)` to point
into `h_K`". The index should be `j+1` (equivalently `j−2`, as `σ_{j+4} = −σ_{j+1}`): writing
`σ_k' = α_k s_{k+2} + β_k s_{k+1}`, differentiating `det(σ_j, σ_{j+1}) = √3/2` gives `α_j = β_{j+1}`,
so the step follows from the first part at `j+1`. The formalization follows the book with the
corrected index.

**E11. Lemma 2.4.6, §2.4 (TeX 2214–2235): a citation applied outside its hypotheses.** The proof
applies Shifrin's Proposition 3.8, a theorem about simple closed curves with everywhere-defined
curvature (at least `C²`), to curves that are only `C¹` with Lipschitz derivative. The formalization proves the inequality directly (each tangent
line supports `K`; second-derivative test), so the citation is not used.

**E12. Problem 2.4.8 and the smoothed octagon's density (TeX 2289–2292, 6348): a fact used but not
proved.** The book normalizes the critical hexagon of `K_min` to area `√12` "by convention" and
then treats the area of any balanced disk divided by `√12` as its density (TeX 3994: "Also associated
with `K` is a critical hexagon `H_K` with midpoints at the points `{s_j*}`"; Lemma 5.0.3, TeX
4006–4008; the density bound at TeX 4341–4346; and the density of the smoothed octagon, TeX 6348 and
6355). That a balanced disk has least circumscribed hexagon of area
`√12`, so that `δ(K) = area(K)/√12`, is never shown. It is true: the formalization proves it for
every balanced pair ([`greatestPackingDensity_of_isBalancedPair`](SmoothedPolygons/Ch2/BalancedDensity.lean#L235); the chords of `K` parallel to a
boundary point `u` have a concave even length function of the height, so the parallelograms
inscribed on `u` all have the same area).

**E13. Theorem 3.1.4(3), §3.1 (TeX 2414–2442): missing hypothesis.** The theorem states that for
a convex disk whose boundary is parameterized by a regular `C¹` multi-curve `σ`, the curve
`X = g⁻¹g'` is Lipschitz. This is false in that generality: the unit disk with
`σ_j(t) = Rot(θ(t)) s_j*`, `θ(t) = t + t^{3/2}`, is such a parameterization, and
`X = θ'(t) J = (1 + (3/2)√t) J` is not Lipschitz at `0`. The proof cites Lemma 2.4.3, which
gives Lipschitz tangents for the minimizer `K_min` parameterized by arclength, the standing
assumption of §2.4. The "circle representation" hypothesis that a TeX comment says was removed
(TeX 2413–2415) would not help: the counterexample is in circle representation. The theorem
holds when the tangents `σ_j'` are Lipschitz, as for balanced disks (Definition 2.4.7, item 2),
and that is how the book uses it. The formalization proves parts (1) and (2) without the
hypotheses they do not need ([`theorem3_1_4`](SmoothedPolygons/Ch3/StateDynamics.lean#L258), Section 5) and part (3) under
the hypothesis that each `σ_j'` is Lipschitz ([`theorem3_1_4_lipschitz`](SmoothedPolygons/Ch3/StateDynamics.lean#L283)); the user approved this
reading.

**E14. Proof of Theorem 3.4.2, §3.4 (TeX 3055): index slip.** "Let `κ = κ₁ + κ₂ + κ₃`" should be
`κ₀ + κ₁ + κ₂` (Definition 3.3.2). The proof is otherwise correct.

**E15. Problem 3.6.2, §3.6 (TeX ~3205): a converse used but not proved.** "The convex disks in
`𝔎_bal` in circle representation arise via the following optimal control problem": the book does
not show that a solution of the control problem, such as the smoothed octagon's trajectory, bounds a
balanced disk; in particular that its curve is simple. For the smoothed `(6k+2)`-gons the
formalization proves it ([`smoothedPolygonDisk_spec`](SmoothedPolygons/Ch7/SmoothedPolygonDisk.lean#L1392); simplicity by a winding-number argument).

**E16. Problem 3.6.2, §3.6 (TeX 3235): misprint in a definition.** The terminal condition is
printed `X(t_f) = R X₀ R⁻¹`. The derivation just before (TeX 3152–3156), the half-plane form
(TeX 3606), the transversality conditions (TeX 5207) and the remark after them (TeX 5221) all give
`X(t_f) = R⁻¹ X₀ R`, and the two differ because `Ad_R` has order 3. For the smoothed octagon,
`X(t_f) = R⁻¹X₀R`, and `R⁻¹X₀R - RX₀R⁻¹ = diag(δ, -δ)` with `δ ≈ 0.433`. The formalization uses `R⁻¹X₀R`
([`IsReinhardtAdmissible`](SmoothedPolygons/Ch3/ControlProblem.lean#L96), [`IsPontryaginExtremal`](Challenge.lean#L171)).

**E17. Lemma 4.2.3, §4.2 (TeX 3382): missing hypothesis `X ≠ 0`.** Lemma 4.2.3 is stated "for
any `X ∈ 𝔰𝔩₂(ℝ)`": `T_X O_X = {[Y, X]} ≅ 𝔰𝔩₂(ℝ)/ℝX`. For `X = 0` the orbit is a point and
`𝔰𝔩₂/ℝ·0 = 𝔰𝔩₂` is three-dimensional. The proof uses that `X` is regular, which in `𝔰𝔩₂` means
`X ≠ 0`, and the lemma is applied to `X ∈ O_J`. The formalization adds `X ≠ 0` ([`lemma4_2_3`](SmoothedPolygons/Ch4/AdjointOrbit.lean#L432)).
It also states Lemma 6.8.1 for nonzero traceless `X` ([`lemma6_8_1`](SmoothedPolygons/Ch6/HalfPlane.lean#L34)); there the book's context
already has `X = Φ(z) ∈ O_J` (TeX 5296–5301), so this is a reading (Section 6), not an error.

**E18. Lemma 4.2.3, §4.2 (TeX 3394–3420): a standard fact used without proof.** The proof shows
that the vectors `[Y, X]` are tangent to the orbit ("this calculation is actually finding
infinitesimal generators of the adjoint action", TeX 3410), but not that every tangent vector is
of this form, which is the standard fact that the orbit map is a submersion onto the orbit. The
formalization proves it for its tangent space of velocities of curves: along a curve in the orbit
the trace and the determinant are constant, so the velocity `V` is traceless with `⟨V, X⟩ = 0`,
and `X^⊥ = {[Y, X]}` by a dimension count ([`orb_adImage_eq_perp`](SmoothedPolygons/Ch4/AdjointOrbit.lean#L388)).

**E19. Lemma 4.3.1, §4.3 (TeX 3514–3530): gap.** "The global minimizer has area less than the area
`π` of the unit circle" is not justified. The unit disk itself is an admissible trajectory
(`X ≡ J`, constant control `(1/3, 1/3, 1/3)`, `t_f = π/3`, cost `π`), so minimality gives only
`area ≤ π`, and the bound `t_f < π/3` needs the strict inequality. It follows from the smoothed
octagon, whose area `≈ 3.126 < π` the book computes in §7.5; the formalization uses that comparison
(Section 7). The lemma is true.

**E20. Problem 4.5.1, §4.5 (TeX 3631): sign misprint.** The coefficients of the half-plane control
problem are defined as "`a = a(u) = (u₂ - u₁)/√3`, `b = …`, `c = …`, the following affine functions
of the control (`eqn:trisystem-Z0`)". The entry of `Z_u` in `eqn:trisystem-Z0` is
`(u₁ - u₂)/√3`; with the printed sign the formulas for `x'` and `y'` are wrong and Lemma 4.5.2
fails (checked symbolically). The formalization uses the entries of `Z_u` ([`halfPlaneF₁`](SmoothedPolygons/Ch4/StarDomain.lean#L61),
[`halfPlaneF₂`](SmoothedPolygons/Ch4/StarDomain.lean#L69)).

**E21. §6.2 and Problem 6.7.1 (TeX 4764–4766, 4818–4820, 5248–5250): a degenerate nontriviality
condition.** The book poses the control problem on `M = SL₂(ℝ) × 𝔰𝔩₂(ℝ)`, with costate
`p = (Λ₁, Λ₂) ∈ 𝔰𝔩₂ × 𝔰𝔩₂`, and the maximum principle requires `(λ_cost, p(t)) ≠ 0`. With that
condition every admissible trajectory lifts to a Pontryagin extremal: `(λ_cost, Λ₁, Λ₂) = (0, 0, X)`
satisfies the costate equation `Λ₂' = -δH/δX = [P, X] = X'`, gives `Λ_R = [Λ₂, X] = 0` and hence
`H ≡ 0` for every control, so the maximum condition and the transversality conditions
(eqn:transversality) hold, and `(λ_cost, p) ≠ 0` because `det X = 1`. Read literally, Theorem 7.5.6
would then hold for every admissible trajectory. On the book's `M = SL₂(ℝ) × 𝔰𝔩₂(ℝ)` the
covector `Λ₂ = X` is not zero, but it vanishes on the tangent space `T_X O_J = X^⊥` of the orbit
on which `X` moves, so it says nothing about the trajectory; the book's reduced costate
`Λ_R = [Λ₂, X]` (Remark 6.5.2) discards exactly this part. The
formalization imposes nontriviality on `(λ_cost, Λ₁, Λ_R)` ([`IsPontryaginExtremal`](Challenge.lean#L171)), the only
reading under which Theorem 7.5.6 has content.
The same degeneracy blocks the derivation of this condition from the maximum principle (§6.2),
and there the repair is in the boundary conditions. Applied with `g(0) = I₂`, `g(t_f) = R` and
`X(t_f) = R⁻¹X(0)R` in full, the conclusions of the maximum principle hold, for every admissible
trajectory, with `λ_cost = 0` and `Λ₂ = cX` (from the first integral `det X`) and, on the open set
`GL₂⁺(ℝ) × C` of `Mat₂(ℝ) × 𝔰𝔩₂(ℝ)` on which the formalization applies it (Section 6), also with
`pg = kI₂` (from the first integral `det g`); the reduced costate of these covectors vanishes, so
the nontriviality of `(λ_cost, Λ₁, Λ_R)` cannot be derived. Because `det g` and `det X` are
constant, the equations `g(t_f)₁₁ = R₁₁` and `X(t_f)₁₀ = (R⁻¹X(0)R)₁₀` follow from the others
(with `det g(0) = det X(0) = 1`, `R₀₀ ≠ 0` and `X₀₁ < 0` on `C`), so leaving them out changes no
admissible trajectory ([`isReinhardtAdmissible_of_mem_matrixEndpoints`](SmoothedPolygons/Ch6/MatrixMinimizer.lean#L361)). The formalization applies the
maximum principle with the boundary condition without them ([`matrixBoundary`](SmoothedPolygons/Ch6/MatrixSystem.lean#L136)); transversality in the
two directions this frees gives `p(t_f)₁₁ = 0` and `Λ₂(t_f)₀₁ = 0`, which exclude these covectors
([`eq_zero_of_covectorΛ_eq_zero`](SmoothedPolygons/Ch6/MatrixCostate.lean#L526)), and the nontriviality of the reduced costate follows: if
`λ_cost = 0` and `Λ₁, Λ_R` vanish at one time, they vanish identically (Corollary 6.5.3 and the
linear `Λ_R` equation), so the covector vanishes at `t_f`
([`exists_isPontryaginExtremal_of_isReinhardtMinimizer`](SmoothedPolygons/Ch6/MatrixExtremal.lean#L587); Section 7).

**E22. Proof of Proposition 6.5.1, §6.5 (TeX 5030–5040): sign convention.** The proof writes the
Euler–Arnold equation as `Λ₁' = ad*_{δH/δΛ₁} Λ₁ = -ad_X Λ₁`, identifying `𝔰𝔩₂*` with `𝔰𝔩₂` by the
trace form "sending `ad*` to `ad`". With the book's definition of `ad*` (Appendix A.4, TeX 13314:
`⟨ad*_Z Y, X⟩ = ⟨Y, -ad_Z X⟩`) this identification sends `ad*_Z` to `+ad_Z`, which would give
`Λ₁' = [X, Λ₁]`. The equation `Λ₁' = [Λ₁, X]` that the book uses is the correct one: in matrix
coordinates on `T*GL₂`, `p' = -Xp` and `Λ₁ = pg` give `Λ₁' = [Λ₁, X]`, and it is the equation whose
solution is `Λ₁(t) = g(t)⁻¹ Λ₁(0) g(t)` (Corollary 6.5.3). The formalization proves the Euler–Arnold
equation in exactly this form, `μ' = [μ, δh/δμ]` for `μ = pg` ([`External.euler_arnold`](External/EulerArnold.lean#L72)), and
applies it in [`proposition6_5_1`](SmoothedPolygons/Ch6/Hamiltonian.lean#L319).

**E23. Theorem 6.8.3, §6.8 (TeX 5385–5402): omitted proof.** The book omits "the long direct
calculation" and refers to Vajjha's thesis. The formalization does the calculation
([`theorem6_8_3`](SmoothedPolygons/Ch6/HalfPlane.lean#L304)); the theorem is true (with the corrected sign of E20).

**E24. Discussion before Lemma 7.2.1, §7.1 (TeX 5550–5563): misprint.** The columns of
`A = (v₊, v₋)` are called the eigenvectors of `Z₀` "associated to the positive and negative
eigenvectors"; read "eigenvalues". Since `⟨Z₀, X₀⟩ < 0` (for `e₃` it is `-2/(3y₀)`), the
eigenvector of `P₀ = Z₀/⟨Z₀, X₀⟩` for its positive eigenvalue `λ` belongs to the negative eigenvalue
of `Z₀`, so `v₊` is the eigenvector of `P₀` (equivalently of `-Z₀`, as §7.2 uses) for `λ`. With the
eigenvectors listed in §7.2, `det(v₊, v₋)` is `-2/√3` for `(1, 0, 0)` and `-1` for `(0, 1, 0)`, so one
vector must be rescaled, by a negative factor, to get `A ∈ SL₂(ℝ)`; only the points `[v±]` are
used, and the argument is unaffected. The formalization rescales (`exists_eigenvector_matrix` in
the proof of [`lemma7_2_1`](SmoothedPolygons/Ch7/ConstantControl.lean#L349)).

**E25. Lemma 7.2.1, §7.2 (TeX 5747–5756): proof in the preceding discussion.** The proof
environment is empty; the argument is the discussion of §7.1–7.2 (Möbius images of rays). The
formalization follows that discussion, with the uniqueness of the constant-control solution,
which the discussion uses implicitly, proved.

**E26. Lemma 7.3.1, §7.3 (TeX 5771–5792): missing hypothesis `⟨X, Z_u⟩ ≠ 0` on `U`.** The lemma
takes any compact convex control set `U` in the plane `u₀ + u₁ + u₂ = 1`, but the Hamiltonian
`H = ⟨Λ₁ - (3/2)λ_cost J, X⟩ - ⟨Λ_R, Z_u⟩/⟨X, Z_u⟩` is undefined where `⟨X, Z_u⟩ = 0`, and the
proof uses a "nonzero denominator" (TeX 5792). For a star state `X`,
`⟨Z_u, X⟩ = -(2/√3)(ρ₂u₀ + ρ₁u₁ + ρ₀u₂)` with `ρᵢ = ρᵢ(X) > 0`: it is negative on `U_T`
(Lemma 3.3.4), but unless `ρ₀ = ρ₁ = ρ₂` it vanishes on a line of the plane, and on a segment `U`
crossing that line the Hamiltonian is undefined at the crossing point. For `U ⊆ U_T`, the case the
book uses, the condition holds. The formalization adds it (`hden` in [`lemma7_3_1`](SmoothedPolygons/Ch7/Faces.lean#L49)).

**E27. Theorem 7.5.1 and Lemma 7.5.3, §7.5 (TeX 6099, 6206–6214): notation.** The theorem requires
`χ₂₃(0) = 0`, the lemma speaks of `χ₃₂(0) = 0`. They are equivalent (`χ₂₃(0) = -χ₃₂(0)`).

**E28. Lemma 7.5.3, §7.5 (TeX 6230–6275): the discarded factor depends on `t`.** The book reduces
`χ₃₂ ≥ 0` to `f(y, r) ≥ 0` "discarding obviously positive multiplicative factors". The factor is
`χ₃₂/f = 2√3/(r(2y - r)(y - 1)^{3/2})`, which depends on `t` through `r = y e^{√3 y₀ t}` and is
positive because `r ≤ 4 < 2y` on the interval. Correct, but not obvious; the formalization proves
the identity ([`chi32_eq`](SmoothedPolygons/Ch7/StrongTransversality.lean#L1007)).

**E29. Lemma 7.5.3, §7.5 (TeX 6265–6273): gap.** The proof needs `∂²f/∂y² ≥ 0` on the triangle
`T = {2 ≤ y ≤ r ≤ 4}` and leaves it "as a tedious but elementary exercise". The inequality is true
but tight: `∂²f/∂y²` vanishes at the corner `(4, 4)`. The formalization proves it
([`hmax_deriv2_nonneg`](SmoothedPolygons/Ch7/HMaxInequality.lean#L234), [`hmax_deriv2_pos`](SmoothedPolygons/Ch7/HMaxInequality.lean#L156)): writing
`∂²f/∂y² = A(y) + r(c(y) + 4 ln(r/y))`, the case `y ∈ [3, 4]` follows from the tangent line of
`r ln r` at `r = 4` and the bound `ln u ≥ 2(u - 1)/(u + 1)`, which reduce it to
`(4 - r)y(10y - 24) + (r - y)(5y² - 10y + 8) ≥ 0`; the case `y ∈ [2, 3]` follows from the minimum in
`r` (at `r* = 2√y e^{(y-2)/(4y)}`), `e^x ≤ 1/(1 - x)`, `3√y ≤ y + 9/4`, the same bound on
`ln(4/y)`, and the certificate
`-77y³ + 364y² - 252y - 240 = 96(3 - y) + 201(y - 2) + (y - 2)(3 - y)(77y + 21) > 0`.
The lemma is true, with the strictness the book states. (Remark 7.5.4, TeX 6283, calls `(4, 4)`
"the corner `r = y = 4` of the disk"; read "triangle".)

**E30. Lemma 7.5.5, §7.5 (TeX 6287–6334): direction and a tacit step.** The lemma is stated as
"`g(t_f) = R`, provided `4/(3y₀² + 1) = 2 cos θ_k`"; the proof argues the other direction
(comparing eigenvalues, then choosing `ℓ = 0, -k`). The sufficiency follows from the same
eigenvalue comparison, run in the stated direction (with `sin θ_k ≠ 0`, the eigenvalues
`e^{±iθ_k}` are distinct, so `R⁻¹g_sw` is diagonalizable), and the formalization proves the
statement as printed in this way. The proof also takes for granted that a trajectory with the
given control and initial values is the spline; the formalization proves this uniqueness. The proof's formula `(R⁻¹ g_sw)^{3k+1}` and the
spline's `(g_sw R⁻¹)^{3k+1}` are conjugate; either works.

**E31. Theorem 7.5.6, §7.5 (TeX 6359–6372): gap.** The proof checks only the transversality
conditions at `t_f`. That the conjugated costates are continuous at the switching times, satisfy
the costate equations, keep `H = 0` and maximize the Hamiltonian on every switching interval
follows from the rotational symmetry and Lemma 7.5.3, and the reduction of the maximization over
`U_T` to its vertices from the form of the Hamiltonian (Lemma 7.3.1); the book leaves all of this
implicit. The formalization proves it ([`poly_isPontryaginExtremal`](SmoothedPolygons/Ch7/SmoothedPolygon.lean#L255)).

**E32. Theorem 7.7.1, §7.7 (TeX 6543–6623): false read literally; the proof is a sketch.**
(a) The theorem says that "in some neighborhood of the set of initial conditions in the cotangent
space, the only extremal trajectory satisfying the transversality conditions at the endpoints is
that of the smoothed octagon". Read literally, this fails in two ways. The octagon's lift started
at a time `s` (with `g(t) = g_oct(s)⁻¹g_oct(s + t)`) is another extremal satisfying all the
transversality conditions, and its initial condition tends to the octagon's as `s → 0`. The
octagon's lift on `[0, 28t_sw]` (seven turns) satisfies them too, with the same initial condition
as on `[0, t_f] = [0, 4t_sw]`. The costate is moreover determined only up to a positive factor.
With the user's approval, the formalization reads the theorem up to time translation, for terminal
times near `t_f`, and in a conic neighbourhood of the octagon's initial condition normalized by
`λ_cost = -1` ([`theorem7_7_1`](SmoothedPolygons/Ch7/Isolated.lean#L508)): an extremal with `|T - t_f| < ε` whose initial condition lies in
the cone over the neighbourhood is the octagon's lift started at some `s ∈ [0, 3t_sw)`, with
costate `-λ_cost` times the octagon's; in particular `T = t_f` and `λ_cost < 0`. The octagon's own
lift meets the hypotheses ([`theorem7_7_1_octagon`](SmoothedPolygons/Ch7/Isolated.lean#L633)), so the statement is not vacuous. The book's
proof also works up to time translation, on a Poincaré section, and only with four switching
intervals (eqn:fp).
(b) The proof is a "proof sketch". It considers the Poincaré map `f(q₀) = Ad(R)q(t_sw(q₀), q₀)`
on a section `χ_ij = 0` of the manifold `M_d` where `det Λ₁ = d` (the formalization takes
`χ₂₃ = 0`), rests on "Direct calculation shows that the fixed point `q_oct` is hyperbolic" (TeX
6612), which the book does not give, and leaves these gaps, all filled in the formalization (the
module docstring of [`SmoothedPolygons.Ch7.Isolated`](SmoothedPolygons/Ch7/Isolated.lean) lists them with the steps that fill them):
an extremal near the octagon need not start on the section, so it must be restarted where it
crosses it; that nearby
extremals are bang-bang with the octagon's switching sequence is not argued (it needs the strict
inequality of Lemma 7.5.3 at the third vertex, the exclusion of singular arcs and chattering at
the switching points, and continuous dependence for the discontinuous extremal dynamics);
Remark 7.5.4 asserts only that the slope of `χ₃₂` at `0` is positive, whereas the Poincaré time
needs the transversal zero of `χ₃₁` at `t_sw`, which follows from the symmetry
`χ₃₁(t_sw - t) = χ₃₂(t)` of the proof of Lemma 7.5.3 (TeX 6220); the parameter `y₀(d)` comes from
Remark 7.5.2, which the book does not prove (E36); and the last step, "the only fixed point
`q_fix(d)` satisfying (eqn:theta-k) is `q_oct`", uses Lemma 7.5.5 in the converse direction, which
follows from the eigenvalue comparison of its proof (E30), as in the formalization. The direct
calculation is supplied: on the four-dimensional tangent space of the section the derivative of
`f` has an explicit matrix whose characteristic polynomial is reciprocal, with multipliers
`≈ -7.7464, -2.1122, -0.4734, -0.1291`, and two certified inequalities show that none has modulus
`1`. The step "by the implicit function theorem, for each `d` near `d_oct`, the function `f_d⁴ - I`
can be inverted in an open neighborhood of the fixed point `q_fix(d)` ... Thus, the only fixed
points near `q_oct` are the fixed points `q_fix(d)`" (TeX 6615–6620) needs neighbourhoods uniform
in `d`, which a separate application for each `d` does not give; the formalization applies the
inverse function theorem once, at `q_oct` (Section 7). The proof writes the switching functions as
`χ_ij = ⟨Λ_R, P_i - P_j⟩` (TeX 6573), the opposite sign of eqn:switch (TeX 6072–6078); this is
harmless, as only their zeros are used.

**E33. Bibliography and history.** Tammela's bound is from 1970 (*Izv. Vyssh. Uchebn.
Zaved. Mat.* 1970, no. 12(103), 103–107); the bibliography prints 1969 and gives the running issue
number 103 as the volume. The text's "Ennola in 1961 and Tammela in 1969 showed
`inf δ ≥ 0.8926…`" (Chapter 1) credits Tammela's bound to both: Ennola proved about `0.88`. The
book cites the 1988 English translation of Nazarov's 1986 paper (*Zap. Nauchn. Sem. LOMI* 151)
and a 2017 reissue of Kupka's 1990 paper. The entry `zelikin2004control`, which the book cites for
the Pontryagin maximum principle (TeX 737, 4674), is A. A. Agrachev and Yu. L. Sachkov, *Control
Theory from the Geometric Viewpoint* (Springer, 2004); the bibliography lists M. I. Zelikin as its
first author and Sachkov twice. Theorem 2.3.6 is attributed to "Minkowski
[`minkowski1907diophantische`], Mahler [`mahler1946lattice`]" (TeX 1789). The cited communication
of Mahler (*Lattice points in n-dimensional star bodies II. Reducibility theorems I*, Proc. KNAW 49
(1946) 331–343) only quotes, without proof and crediting Minkowski, the six-point statement (A)
(p. 340): every critical lattice of a convex domain in the plane has at least six points on its
boundary, and in suitable coordinates exactly six are `(1, 0)`, `(0, 1)`, `(−1, 1)` and their
negatives. It states neither the theorem's form, with a basis and the area of the parallelogram,
nor its converse; the converse is asserted ("as is easily seen") in the second communication of
the series (p. 444). The book's wording matches Lemma 3 of Mahler's paper A (p. 101; Section 2).
The formalization follows Minkowski and Mahler 1947, Lemma 2
([`External.minkowski_mahler`](External/MinkowskiMahler.lean#L964)). These do not affect the
mathematics.

**E34. Lemma 3.1.8, §3.1 (TeX 2554–2579): missing hypothesis; two gaps.** The lemma assumes that
the boundary of `K` "is parameterized by a `C¹` multi-curve `σ`". Without regularity it is false:
for the square `[-λ, λ]²` with `λ² = √3/2`, there is a `C¹` multi-curve on the boundary in which
`σ₂ = (-λ, 0)` is constant while `σ₁` and `σ₃ = -σ₀` slide along the parallel edge lines `y = λ`
and `y = -λ` (continued around the square, one pair `±σ_j` at rest at a time, it parametrizes the
whole boundary), and no hyperbola has parallel asymptotes. §2.4 parameterizes the boundary "by a
regular `C¹` curve" (TeX 1945–1946); with the user's approval, the formalization assumes that
every `σ_j` is regular, `σ_j' ≠ 0` ([`lemma3_1_8`](SmoothedPolygons/Ch3/HyperbolicArc.lean#L772), Section 4). The proof then follows the book's
(the tangent lines at the multi-point cut out a hexagon `H_K(t)` with edge midpoints `σ_j(t)` and
area `√12`, the parallelogram `P_K` has constant area, and Reinhardt's observation on the pencil of
lines cutting a constant area), with two gaps filled: the book takes the lines traced by
`±σ_{i-1}` and `±σ_{i+1}` to bound a parallelogram, that is, the lines of `σ_{i-1}` and `σ_{i+1}`
not to be parallel, and does not show that the hyperbola is nondegenerate (its constant is not
`0`). Both follow from regularity: each line supports `K`, and in either degenerate case one of
the curves would be constant.

**E35. Theorem 6.1.1 (Filippov), §6.1 (TeX 4538–4546): missing hypothesis; no source.** For
`q' = f(q, u)` on a manifold, with compact control set `U`, convex velocity sets `f(q, U)` and `f`
of compact support, the theorem asserts that "the attainable sets are compact and an optimal
control exists" for the cost `∫φ(q, u) dt`. The second claim fails when `φ` depends on `u`: on
`ℝ`, with `q' = uψ(q)`, `U = [-1, 1]` and a bump `ψ` equal to `1` on `[-1, 1]`, the cost
`∫₀¹ (q² + 1 - u²) dt` from `q(0) = 0` to `q(1) = 0` has infimum `0` (chattering controls
`u = ±1`) and no minimizer (cost `0` forces `q = 0`, hence `u = 0` almost everywhere, of cost
`1`). It holds when the extended velocity sets `{(f(q, u), φ(q, u)) | u ∈ U}` are convex, which is
the book's hypothesis when `φ` depends only on the state, as the Reinhardt cost `-(3/2)⟨J, X⟩`
does; with the user's approval the formalization states it so, on `ℝⁿ`, for fixed and free
terminal time ([`External.filippov`](External/Filippov.lean#L150); Sections 4 and 6). §6.1 cites no source for the theorem; Hales's
2017 preprint cites it as Theorem 10.1 of Agrachev and Sachkov's book, the entry
`zelikin2004control` of the bibliography (E33).

**E36. Remark 7.5.2, §7.5 (TeX 6185–6203): stated without proof.** The remark says that
`d(y₀) = det Λ₁` is a constant of motion, given by an explicit formula, and that `d` is increasing
on `(1/√3, 1)` with range `(0, 9/4)`, so that it determines `y₀`; the proof of Theorem 7.7.1 uses
this to define `y₀(d)` (TeX 6581). The book gives no proof; a comment in the TeX source (TeX
6199–6201) says that "the derivative factors in a nice way". The formalization follows that hint:
`d' = E·F/(36y⁹)` with `E = 3 + 6y² - (1 + 3y²)ℓ`, `F = 2ℓ(3y⁴ - 1) + 9y⁶ - 9y⁴ - 6y² + 6` and
`ℓ = ln(4/(3y² + 1))`, and `E, F > 0` on the interval by the bounds `ln x ≤ x - 1` and
`ln x ≥ 2(x - 1)/(x + 1)` for `x ≥ 1` ([`remark7_5_2`](SmoothedPolygons/Ch7/Remarks.lean#L214)). The remark is true.

**E37. Remarks 7.6.2 and 7.6.4, §7.6 (TeX 6402–6438): a condition not stated, and a claim read
off a figure.** Remark 7.6.2 defines the smoothed `(6k−2)`-gons by their control mode sequence
(eqn:3k+2), switching time, initial point `z₀ = iy₀` with `y₀ > 1` and initial control `e₂` ("The
changes are minor"), but does not state the condition that fixes `y₀`, the analogue of
eqn:theta-k. The argument of Lemma 7.5.5 gives `4/(3y₀² + 1) = 2cos(πk/(3k − 1))`; that this
closes the curve, `g(t_f) = R`, was checked numerically for `k = 2, 3`, not in Lean. Remark 7.6.4
says that at `k = 1` the smoothed `(6k−2)`-gon "degenerates to a rectangle with corners and area
`√12`", which the book reads off a figure ("the shape appears to be tending to a rectangle of area
`√12` as `k ↦ 1`", TeX 6435–6438) and does not prove. At `k = 1` the closing condition has no solution
(`y₀ = ∞`), so the formalization reads the remark as the limit `k → 1⁺` of the `(6k−2)`-gons
interpolated to real `k` and proves it: the cost tends to `√12`, and the six arcs tend in the
Hausdorff distance to the boundary of a rectangle of area `√12` ([`remark7_6_4`](SmoothedPolygons/Ch7/Remarks.lean#L1719)); the
trajectories exist for every real `k > 1` ([`remark7_6_4_exists`](SmoothedPolygons/Ch7/Remarks.lean#L1900)), so the statement is not
vacuous. The remark is true in this reading.

**E38. Remark 6.6.1, §6.6 (TeX 5216–5242): a claim stated without proof.** The first item of the remark
says that the transversality conditions make every optimal solution, extended in time, periodic
up to rotation: `X(3t_f) = X₀`, `g(6t_f) = I₂`, and "every transversal trajectory determines a
periodic solution (with discrete rotational symmetry) of the lifted trajectories in the cotangent
bundle". The book gives no proof beyond "if we extend time, every optimal solution can be made into
a periodic one". The claim is true: the formalization extends
every Pontryagin extremal on `[0, t_f]` by `g(s + kt_f) = g(s)Rᵏ` and `Y(s + kt_f) = R⁻ᵏY(s)Rᵏ` for
`Y = X, Λ₁, Λ_R`, with the coordinates of the control permuted cyclically `k` times (so that
`Z_{u(s + kt_f)} = R⁻ᵏZ_{u(s)}Rᵏ`), and proves that the extension solves the state–costate system
of Problem 6.7.1, with the conditions of the maximum principle and the same `λ_cost`, on every
`[0, nt_f]`, with period `3t_f` for the control, `X`, `Λ₁`, `Λ_R` and `6t_f` for `g`
([`remark6_6_1`](SmoothedPolygons/Ch6/PeriodicExtension.lean#L352)). The pieces join by the transversality conditions (6.6.1), and since the controls
are only measurable they are glued as Carathéodory solutions. The second item, that the
transversality condition for `Λ₁` follows from the one for `g`, refers to Corollary 6.5.3 for the
proof and is proved so ([`remark6_6_1_lambda1`](SmoothedPolygons/Ch6/PeriodicExtension.lean#L86)); the proof that minimizers are extremals uses it.

## 4. Missing hypotheses

| Where | Missing hypothesis | Counterexample without it | In the formalization |
| --- | --- | --- | --- |
| Theorem 3.1.4(3) | `σ_j'` Lipschitz (the standing assumption of §2.4, through Lemma 2.4.3) | unit disk, `σ_j(t) = Rot(t + t^{3/2}) s_j*`, `X = (1 + (3/2)√t)J` | hypothesis of [`theorem3_1_4_lipschitz`](SmoothedPolygons/Ch3/StateDynamics.lean#L283) (approved by the user) |
| Lemma 3.1.8 | the curves `σ_j` are regular, `σ_j' ≠ 0` (§2.4, TeX 1945–1946: "a regular `C¹` curve") | the square `[-λ, λ]²`, `λ² = √3/2`: `σ₂ = (-λ, 0)` constant while `σ₁`, `σ₃` slide along the parallel lines `y = ±λ` (E34) | hypothesis `hreg` of [`lemma3_1_8`](SmoothedPolygons/Ch3/HyperbolicArc.lean#L772) (approved by the user) |
| Lemma 4.2.3 | `X ≠ 0` | `X = 0`: `T_0 O_0 = 0` but `𝔰𝔩₂/ℝ·0` has dimension 3 | hypothesis of [`lemma4_2_3`](SmoothedPolygons/Ch4/AdjointOrbit.lean#L432) |
| Theorem 6.1.1 (Filippov), "an optimal control exists" | the velocity sets extended by the cost, `{(f(q, u), φ(q, u)) \| u ∈ U}`, are convex (the book's hypothesis when `φ` does not depend on `u`) | on `ℝ`, `q' = uψ(q)`, `U = [-1, 1]`, a bump `ψ` with `ψ = 1` on `[-1, 1]`: `∫₀¹ (q² + 1 - u²) dt` from `q(0) = 0` to `q(1) = 0` has infimum `0` and no minimizer (E35) | hypothesis of the second part of [`External.filippov`](External/Filippov.lean#L150) (approved by the user) |
| Lemma 7.3.1 | `⟨X, Z_u⟩ ≠ 0` on `U` (used by the proof, TeX 5792) | a segment `U` of the plane `u₀ + u₁ + u₂ = 1` crossing the line where `⟨X, Z_u⟩ = 0`: the Hamiltonian is undefined there | hypothesis `hden` of [`lemma7_3_1`](SmoothedPolygons/Ch7/Faces.lean#L49) |

## 5. Redundant hypotheses

Each hypothesis in the table is omitted from the Lean statement, which is therefore more general
than the book's. The Challenge statements keep the book's hypotheses.

| Result | Hypothesis that is not needed | Why |
| --- | --- | --- |
| Theorem 3.1.4, parts (1), (2) ([`theorem3_1_4`](SmoothedPolygons/Ch3/StateDynamics.lean#L258)) | `K` a convex disk, `σ` regular, `σ` parameterizes `∂K` | the proof differentiates `σ_j = g s_j` and uses `det g = 1`; it holds for every `C¹` multi-curve induced by a curve in `SL₂(ℝ)` |
| Proposition 3.1.9 ([`proposition3_1_9`](SmoothedPolygons/Ch3/StateDynamics.lean#L570)) | `σ₀` parameterized by arclength | the proof uses that the tangents are Lipschitz (Definition 2.4.7, item 2), not the normalization |
| Corollary 3.1.10 ([`corollary3_1_10`](SmoothedPolygons/Ch3/StateDynamics.lean#L679)) | the same (the standing assumption of TeX 2157, not printed in the statement) | it applies Proposition 3.1.9 |
| Lemma 3.3.1 ([`lemma3_3_1`](SmoothedPolygons/Ch3/ControlSets.lean#L208)) | `g'` Lipschitz | the hypothesis `κ_j ≥ 0` almost everywhere already presupposes that `X'` exists almost everywhere; the first proof (if `κ₀ = κ₁ = 0` then `κ₂ = √3 det X/ρ₀(X) > 0`) uses only `tr X' = 0` where `X'` exists. (The formal `κ_j` is defined everywhere, through [`derivEntrywise`](Basic/Analysis/Calculus/MatrixEntrywise.lean#L113).) |
| Corollary 6.5.4 ([`corollary6_5_4`](SmoothedPolygons/Ch6/Hamiltonian.lean#L477)) | `Z = Z_u` is a control matrix | the Lean statement takes any matrix `Z` with `⟨X, Z⟩ ≠ 0`: the quotient rule does not use the form of `Z_u` |
| Theorem 6.8.2 ([`theorem6_8_2`](SmoothedPolygons/Ch6/HalfPlane.lean#L164)) | `Λ_R` traceless | `Λ_R` enters only through its trace form with traceless matrices |
| Lemma 7.1.2 ([`lemma7_1_2`](SmoothedPolygons/Ch7/ConstantControl.lean#L82)) | `u ∈ U_T` | the proof uses only that `P` is constant along the trajectory (Lemma 7.1.1), which holds for every constant `u` |
| Lemma 7.3.1 ([`lemma7_3_1`](SmoothedPolygons/Ch7/Faces.lean#L49)) | the control set lies in the plane `u₀ + u₁ + u₂ = 1` | `Z_u` is linear in `u`, so `H` is a linear-fractional function of `u` on any compact convex set on which `⟨X, Z_u⟩ ≠ 0` (hypothesis `hden`, E26) |
| Gruber, Cor. 30.1 ([`External.gruber_corollary_30_1`](External/Gruber.lean#L320), cited in Definition 2.1.2) | the translates form a packing | the lattice-point count bounds the sums of the areas of the translates meeting a disk, overlaps counted with multiplicity |

Three Lean statements keep hypotheses that their proofs do not use, because the book or the source
states them:
- Lemma 3.1.8 ([`lemma3_1_8`](SmoothedPolygons/Ch3/HyperbolicArc.lean#L772)) keeps `hcover`, that the arcs of `σ` cover `∂K` (part of "the
  boundary is parameterized by `σ`"); of that hypothesis the proof uses only `hbd`, that the curves
  lie on `∂K`.
- Proposition 6.4.1 ([`proposition6_4_1`](SmoothedPolygons/Ch6/LeftInvariant.lean#L91)) keeps the nondegeneracy, symmetry and invariance of the bilinear
  form: nondegeneracy is what makes `p ↦ ⟨p, ·⟩` the identification `𝔤 ≅ 𝔤*`, and the identity
  `H = ⟨p, f(e, u)⟩` holds for every bilinear form.
- Filippov's theorem ([`External.filippov`](External/Filippov.lean#L150)) keeps the source's standing assumptions that `f` is smooth
  in `q` with `∂f/∂q` jointly continuous (`hfq`, `hfq'`), which give existence and uniqueness of
  trajectories; the proof uses only the continuity of `f`, the compactness of `U`, the compact
  support of `f` and the convexity hypotheses.

## 6. How the formalization reads the paper

- **Packings and densities (§2.1).** The book's disks `B_r` are Euclidean disks ([`euclidDisk`](Challenge.lean#L280);
  Mathlib's balls on `Fin 2 → ℝ` are squares). A packing is a set of convex disks with pairwise
  disjoint interiors; congruent copies are images under Euclidean motions, reflections included.
  The density ratios are taken in `[0, ∞]`; a density exists when the upper and lower densities are
  finite and equal; `δ(K)` and `δ_L(K)` are suprema of real numbers, over nonempty sets bounded by
  `1`. A lattice is a discrete `ℤ`-submodule of `ℝ²` spanning it, and its determinant is Mathlib's
  covolume, shown equal to `|det|` of any basis ([`definition2_3_2`](SmoothedPolygons/Ch2/Mahler.lean#L58)).
- **Critical lattices and hexagons (§2.3).** A critical lattice is admissible with determinant
  `Δ(K)` (E6). The critical hexagons of §2.2 are the least-area circumscribed centrally symmetric
  hexagons ([`IsLeastAreaHexagon`](SmoothedPolygons/Ch2/Reinhardt.lean#L66), compared among strictly convex hexagons centred at the origin,
  which gives the same minimum); those of Definition 2.3.8 come from Mahler's construction, and
  Theorem 2.3.9 identifies them. Two notions of irreducibility appear: Definition 2.3.5's (every
  boundary point on a critical lattice) and Mahler's original one (no proper subdomain with the same
  `Δ`), used in the proof of Lemma 2.2.5. In Mahler's notion the subdomains are read as centrally
  symmetric convex disks ([`External.MahlerIrreducible.IsIrreducible`](External/MahlerIrreducible.lean#L105)); Mahler admits all star domains, and
  paper A's Lemma 13 shows that for a convex `K` the two readings agree (Section 2). The remark after
  Definition 2.3.5, that the two notions agree, is proved for every `K ∈ 𝔎_ccs`
  ([`isIrreducible_iff_mahlerIrreducible`](SmoothedPolygons/Ch2/Mahler.lean#L99), from Mahler's Lemma 3,
  [`External.mahler_irreducible_iff`](External/MahlerIrreducible/Lemma3.lean#L367)).
- **Statements about `K_min` (§2.2–2.4).** Lemma 2.2.7's "the midpoints advance monotonically and
  continuously" is formalized with polar-angle lifts; Lemma 2.4.2 is read literally (any `C⁰`
  multi-curve on the boundary); Lemmas 2.4.5 and 2.4.6 assume the positive orientation of §2.4,
  without which they are false (time reversal). Remark 2.2.4's hyperbolic arc is the level set of a
  product of signed distances to the two adjacent edge lines. Problem 2.4.8 is a predicate on `K`.
- **The area formula (§3.2).** [`eqn_cost`](SmoothedPolygons/Ch3/AreaFormula.lean#L205) assumes, besides the balanced pair and `σ_j = g s_j*`,
  that `σ_j(t + t_f) = σ_{j+1}(t)`, which the book derives with its normalization of the
  parametrization (TeX ~3140–3160); without it the formula fails (a circle traversed at varying
  speed).
- **Matrices and the plane.** `2 × 2` real matrices are `Matrix (Fin 2) (Fin 2) ℝ`; points of the
  plane are `Fin 2 → ℝ`. Mathlib puts no norm on matrices, so derivatives and Lipschitz conditions
  of matrix-valued curves are taken entry by entry ([`Basic/Analysis/Calculus/MatrixEntrywise.lean`](Basic/Analysis/Calculus/MatrixEntrywise.lean)),
  which agrees with any norm. The trace form is `⟨X, Y⟩ = tr(XY)`; `R` is written out and shown
  equal to `exp(Jπ/3)` ([`definition3_1_5`](SmoothedPolygons/Ch3/StateDynamics.lean#L337)).
- **Controls.** `u = (u₀, u₁, u₂)` is `Fin 3 → ℝ`; the vertices `e₁, e₂, e₃` are `vertex 0`,
  `vertex 1`, `vertex 2`, and the switching functions `χ_ij` are indexed by `Fin 3` accordingly.
  `U_T` is defined as in Definition 3.3.3 ([`controlSimplex`](Challenge.lean#L94)).
- **Solutions of differential equations.** The state and costate equations with a measurable
  control are solved in Carathéodory's sense ([`IsIntegralCurve`](Challenge.lean#L144)): each entry of the solution is the
  indefinite integral of the corresponding entry of an integrable right-hand side. Results whose
  book proofs differentiate classically are stated with `HasDerivWithinAt` on closed intervals.
- **The state space.** By Theorem 4.4.1, a state trajectory ([`IsStateTrajectory`](Challenge.lean#L152)) takes values in
  `SL₂(ℝ) × 𝔥*`: `X(t)` is traceless with `det X = 1` and satisfies the star inequalities.
- **Pontryagin extremals.** The book defines a Pontryagin extremal as a lift satisfying the
  conditions of the maximum principle (§6.2), with the full costate `p = (Λ₁, Λ₂)`;
  [`IsPontryaginExtremal`](Challenge.lean#L171) states them in the reduced variables `(Λ₁, Λ_R)` of Problem 6.7.1: the
  costate equations; `Λ₁, Λ_R` traceless with `Λ_R ⊥ X`; `λ_cost ≤ 0` constant;
  `(λ_cost, Λ₁, Λ_R) ≠ 0` at every time; maximality of the control and `H = 0` for almost every
  time; and the transversality conditions of §6.6. The nontriviality condition is imposed on the
  reduced costate, because on the full costate it admits the spurious lift `λ_cost = 0`, `Λ₁ = 0`,
  `Λ₂ = X` of every trajectory (E21). "The Hamiltonian `H(q, p, u*)` vanishes identically" is read
  almost everywhere, as Agrachev and Sachkov state it ((12.15)) and as the maximum principle gives
  it for measurable controls.
- **The maximum principle (§6.2, §6.6).** [`External.pontryagin_maximum_principle`](External/Pontryagin.lean#L80) is stated on an
  open subset of a finite-dimensional real normed space, for a compact control set (the book's
  "closed"), dynamics and cost `C¹` in the state with `∂f/∂q` jointly continuous (the book's
  "smooth", with Agrachev and Sachkov's (10.4)), and strong local minimizers (more general than
  the global minimizers the book considers). Since `SL₂(ℝ)` is not open in `Mat₂(ℝ)`, the
  principle is applied, instead of on the book's manifold `SL₂(ℝ) × 𝔰𝔩₂(ℝ)`, on the
  open set `GL₂⁺(ℝ) × C` of `Mat₂(ℝ) × 𝔰𝔩₂(ℝ)` (a departure, Section 7) ([`matrixDomain`](SmoothedPolygons/Ch6/MatrixSystem.lean#L118)), `C` the open cone of the star
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
  ([`covectorΛR_transversality`](SmoothedPolygons/Ch6/MatrixCostate.lean#L477)). For `Λ₁` transversality gives nothing, since `g` is fixed at both ends;
  the condition `Λ₁(t_f) = R⁻¹Λ₁(0)R` of (6.6.1) comes from `g(t_f) = R` by Corollary 6.5.3, as
  Remark 6.6.1 says, and the formalization takes that route ([`remark6_6_1_lambda1`](SmoothedPolygons/Ch6/PeriodicExtension.lean#L86)). The costates of a covector `p` at `(g, X)` are `Λ₁ = pg` made traceless (the
  `g`-part of `p` as a matrix by the trace pairing, then the left trivialization of Proposition
  3.6.1, [`covectorΛ₁`](SmoothedPolygons/Ch6/MatrixCostate.lean#L65)), `Λ₂` the `X`-part identified with `𝔰𝔩₂(ℝ)` by the trace form, and
  `Λ_R = [Λ₂, X]` ([`covectorΛR`](SmoothedPolygons/Ch6/MatrixCostate.lean#L69)).
- **Propositions 3.6.1 and 6.4.1 in §6.2.** The trivialization of Proposition 3.6.1 and the
  identity `⟨p, gX⟩ = ⟨Λ₁, X⟩` of Proposition 6.4.1 are checked in matrix coordinates, where the
  identity is the associativity `tr(p(gX)) = tr((pg)X)`
  ([`controlHamiltonian_matrix_eq_fullHamiltonian`](SmoothedPolygons/Ch6/MatrixCostate.lean#L135)), rather than obtained from [`proposition6_4_1`](SmoothedPolygons/Ch6/LeftInvariant.lean#L91), which is
  stated for Mathlib's Lie groups: Mathlib makes `Mat₂(ℝ)ˣ` a Lie group only through a local
  choice of normed algebra, and does not identify the bracket of left-invariant vector fields with
  the matrix commutator, which the invariance hypothesis of the proposition needs.
- **Remark 6.6.1.** A "transversal trajectory" is a Pontryagin extremal on `[0, t_f]`, and the
  "periodic solution of the lifted trajectories" is a solution on `[0, ∞)` of the state–costate
  system with the conditions of the maximum principle ([`IsStateCostateSolution`](SmoothedPolygons/Ch6/PeriodicExtension.lean#L54): Problem 6.7.1
  without the boundary conditions) on every `[0, nt_f]`, equal to the extremal on `[0, t_f]`, whose
  control is rotated (its coordinates permuted cyclically) from one period to the next (E38).
- **Proposition 6.5.1.** "Hamilton's equations" are the hypotheses of [`proposition6_5_1`](SmoothedPolygons/Ch6/Hamiltonian.lean#L319): on
  `T*𝔰𝔩₂(ℝ)`, `X' = δH/δΛ₂` and `Λ₂' = -δH/δX`; on the cotangent bundle of the group, in canonical
  coordinates `(g, p)` of `T*GL₂(ℝ)` (the covector `p` acting by `v ↦ tr(p v)`), `g' = ∂H/∂p` and
  `p' = -∂H/∂g`, with `H` depending on `(g, p)` through the left-trivialized costate `Λ₁ = pg`. The
  Euler–Arnold equation that the book cites is then proved ([`External.euler_arnold`](External/EulerArnold.lean#L72)). The conclusion
  is the derivative of `Λ₁` and of `Λ_R` at `t`. In §6.2 these hypotheses are the adjoint
  equation of the maximum principle, at almost every time, with the momentum
  `p - (tr(pg)/2)g⁻¹` (whose left trivialization is `Λ₁`)
  ([`hasDerivAt_covectorΛ_of_adjoint`](SmoothedPolygons/Ch6/MatrixCostate.lean#L323)).
- **The smoothed `(6k+2)`-gon.** The book specifies it by its control mode sequence (eqn:3k+1), the
  switching time (eqn:t1), the initial point `z₀ = i y₀` with `4/(3y₀² + 1) = 2 cos θ_k`, and
  `g(0) = I₂`. The Challenge states Theorem 7.5.6 for every state trajectory with this control and
  these initial values, and proves that there is one; the library shows it is unique
  ([`polygon_trajectory_unique`](SmoothedPolygons/Ch7/SmoothedPolygon.lean#L226)) and equal to the spline of §7.4 ([`polygonG`](SmoothedPolygons/Ch7/Polygon.lean#L287), [`polygonX`](SmoothedPolygons/Ch7/Polygon.lean#L281)).
- **Bang-bang.** [`IsBangBang`](Challenge.lean#L191) asks that the control take values in the extreme points of `U_T`;
  the clause "with discontinuous switching" of Definition 7.3.2 describes the switching and is not
  a condition.
- **Area and density.** The smoothed `(6k+2)`-gon is the region swept from the origin by the
  spline's curve, extended periodically ([`smoothedPolygonDisk`](SmoothedPolygons/Ch7/SmoothedPolygonDisk.lean#L508)); it is a balanced disk in circle
  representation (E15), its area is the cost by the area formula of §3.2, and its greatest packing
  density is its area divided by `√12` (E12, through Theorem 2.2.2 and Fejes Tóth's theorem).
- **Tangent spaces.** The tangent space of an adjoint orbit (Lemma 4.2.3) is the set of velocities
  of curves in the orbit ([`curveTangentSpace`](SmoothedPolygons/Ch4/AdjointOrbit.lean#L295)); the cotangent space of Lemma 6.8.1 is the dual of
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
  and `S` ([`dihedralGroup`](SmoothedPolygons/Ch4/IdealVertices.lean#L48)). The formal statements give the action of the generators on
  `±1/√3` and `+∞` ([`dihedral_smul_idealVertices`](SmoothedPolygons/Ch4/IdealVertices.lean#L59)) and show that every element permutes these three
  points ([`dihedral_permutes_idealVertices`](SmoothedPolygons/Ch4/IdealVertices.lean#L89)).
- **Filippov's theorem (Theorem 6.1.1).** The state space is `ℝⁿ` instead of a manifold (for `f`
  smooth with compact support, the manifold case follows by an embedding in some `ℝᴺ`); a
  trajectory is a Carathéodory solution driven by a measurable control; "the support of `f` is a
  compact subset of `M × U`" is read as `f(q, u) = 0` for `q` outside a compact set; the attainable
  sets are those at time `T` and up to time `T`; and "an optimal control exists" is stated for fixed
  and for free terminal time (the book applies it with free terminal time `t_f ≤ π/3`, TeX 3207,
  4583), under the convexity of the extended velocity sets (E35).
- **Definition 6.3.1 and Proposition 6.4.1.** They are stated on Mathlib's real Lie groups
  (`LieGroup I ∞ G`): `f(g, u)` is a tangent vector at `g`, `TL_h` is the tangent map `mfderiv`,
  the Lie algebra `𝔤` is `GroupLieAlgebra I G`, a cotangent vector at `g` is a linear form on
  `T_g G`, and "invariant" means invariant under the adjoint action. The left trivialization
  `p̃ = T*L_{g⁻¹}(p)` is part of the statement ([`leftTrivCovector`](SmoothedPolygons/Ch6/LeftInvariant.lean#L72)): the Hamiltonian
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
  [`remark7_6_4_exists`](SmoothedPolygons/Ch7/Remarks.lean#L1900) shows that they exist.
- **Theorem 7.7.1.** "In some neighborhood of the set of initial conditions in the cotangent space"
  is read as a conic neighbourhood: some positive multiple of the costate `(Λ₁(0), Λ_R(0), λ_cost)`,
  with `X(0)`, lies in a neighbourhood of the octagon's initial condition normalized by
  `λ_cost = -1` (`g(0) = I₂` is a transversality condition). "The only extremal ... is that of the
  smoothed octagon" is read up to time translation and for terminal times near `t_f`; without these
  the statement is false (E32).
- **Balanced pairs exist.** The unit disk, with `σ_j(t) = Rot(t) s_j*` and `t_f = π/3`, is a
  balanced pair ([`circle_isBalancedPair`](SmoothedPolygons/Ch2/BalancedCircle.lean#L241)), so the hypotheses of the results of Chapter 3 about
  balanced pairs can be met.
- **Corrections of statements.** E1 (Lemma 2.2.1 in its packing form, user-approved), E13
  (hypothesis, user-approved), E16 (misprint), E17 (`X ≠ 0`), E20 (misprint), E21 (nontriviality on
  the reduced costate, derived from the maximum principle with non-redundant boundary conditions),
  E26 (`⟨X, Z_u⟩ ≠ 0`), E32 (Theorem 7.7.1 up to time translation, with
  terminal time near `t_f`, user-approved), E34 (regularity, user-approved), E35 (the extended
  velocity sets, user-approved), and in proofs E14 and E24.

## 7. Departures from the paper's proofs

| Result | The paper's argument | The formalization's | Why it is necessary | E-item |
| --- | --- | --- | --- | --- |
| Lemma 2.2.1 (in its corrected form) | expand `K`, separate touching translates by lines, crop, repeat until the plane is tiled; at most six edges by Euler characteristic | a maximal centrally symmetric convex body `C ⊇ K` free of half-lattice points (Zorn; bounded by Blichfeldt) is cut out by at most three strips, whose unique support points pairwise form lattice bases ([`PlaneLattice.exists_halfLatticeFree_eq_strips`](Basic/Analysis/Convex/LatticePacking.lean#L998)) | the book's argument is aimed at the printed statement, which is false (E1): its termination ("the plane is tiled") and its edge count (Euler characteristic of a tiling) fail; the corrected statement needs another argument (approved by the user) | E1 |
| Lemma 2.2.5, no corners and critical edges | shave `K` near a boundary point lying on no edge of a critical hexagon; at endpoints of flat segments, "shave as above" | a worst disk is irreducible in Mahler's sense (no symmetric convex proper subdomain has the same `Δ`); by Mahler 1947, Lemma 3, which the book cites after Definition 2.3.5, its boundary points lie on critical lattices, so every support line contains a point of a critical lattice, one of the six boundary points of a configuration of Mahler's Lemma 2 ([`External.mahler_irreducible`](External/MahlerIrreducible/Lemma3.lean#L383)); there Mahler's Theorem 2 gives a unique support line and the edge of a least-area hexagon | the shaving argument cannot close the case of a segment endpoint on a critical edge off its midpoint (E4); the user chose Mahler's route, which rests on results the book itself cites (Mahler's Lemma 3, Theorems 2.3.6 and 2.3.7) | E4 |
| Lemma 2.4.2, one step | `σ₂` equals the integral curve `σ̃₂` with the same tangent direction and area relation | `σ₂` is differentiable because its chords lie between the tangent lines at their ends, so their directions converge, and the area relation fixes their lengths | the book does not show that `σ̃₂` stays on the boundary, which its identification needs (E8) | E8 |
| Lemma 2.4.6 | Shifrin's Proposition 3.8 (a simple closed regular curve is convex iff its curvature has one sign) | each tangent line supports `K`, so `f(t) = det(σ'(t₀), σ(t) − σ(t₀)) ≥ 0` with `f(t₀) = f'(t₀) = 0`, and the second-derivative test gives `det(σ', σ'') ≥ 0` | the cited proposition is about smooth curves; the curves here are only `C¹` with Lipschitz derivative (E11) | E11 |
| The area formula `eqn:cost` (§3.2) | Green's theorem, `area(K) = ½∮ x dy − y dx` | the polar-coordinates form of Green's formula for regions star-shaped about the origin, `area = ½∫ det(γ, γ')` ([`PlaneCurve.IsStarCurve.volume_radialHull`](Basic/Analysis/Convex/StarCurve.lean#L480), by the change of variables `(r, t) ↦ r γ(t)`) | Mathlib has no Green's theorem for regions bounded by `C¹` curves; only that step changes | – |
| Lemma 3.1.12 (Jacobi's formula) | verify the polynomial identity on the dense set of matrices with distinct nonzero eigenvalues, through a differentiable diagonalization `A = L⁻¹DL` | differentiate the Leibniz expansion of `det` and identify `Σᵢ det(A with column i replaced by A'ᵢ) = tr(adj(A) A')` through Cramer's rule | the step needs mathematics that Mathlib lacks (a differentiable eigen-decomposition and the density argument); the user approved the replacement | – |
| Lemma 4.3.1 | `area(K_min) < area(unit disk) = π` | `cost(K_min) ≤ cost(smoothed octagon) < π`, the octagon being admissible by Theorem 7.5.6 and its cost computed in the example of §7.5 | the paper's step has a gap that its own comparison cannot close: the unit disk is admissible, so it gives only `≤` (E19) | E19 |
| §6.2 and §6.6, every minimizer is a Pontryagin extremal | the maximum principle on `SL₂(ℝ) × 𝔰𝔩₂(ℝ)` with the boundary conditions `g(0) = I₂`, `g(t_f) = R`, `X(t_f) = R⁻¹X(0)R`; the Hamiltonian by Proposition 6.4.1, the costate equations by Proposition 6.5.1, the transversality conditions of §6.6 (for `Λ₁` by Corollary 6.5.3) | the same steps, with two changes. (1) The maximum principle is applied on the open set `GL₂⁺(ℝ) × C` of `Mat₂(ℝ) × 𝔰𝔩₂(ℝ)` ([`matrixDomain`](SmoothedPolygons/Ch6/MatrixSystem.lean#L118)), with `g(0) = I₂` and `det X(0) = 1` among the boundary conditions; this adds three steps: `det g` and `det X` are first integrals, so the competitors are Reinhardt trajectories; the adjoint equation meets the hypotheses of Proposition 6.5.1 through the momentum `p - (tr(pg)/2)g⁻¹`; and the covector `pg = kI₂` of (2). (2) The boundary condition is applied less the equations `g(t_f)₁₁ = R₁₁` and `X(t_f)₁₀ = (R⁻¹X(0)R)₁₀`, which the first integrals `det g` and `det X` make redundant ([`matrixBoundary`](SmoothedPolygons/Ch6/MatrixSystem.lean#L136)); transversality in the two directions this frees excludes the covectors whose reduced costate vanishes, and the nontriviality of `(λ_cost, Λ₁, Λ_R)`, which the book does not derive, is proved by Corollary 6.5.3, uniqueness for the linear `Λ_R` equation and transversality at `t_f` ([`exists_isPontryaginExtremal_of_isReinhardtMinimizer`](SmoothedPolygons/Ch6/MatrixExtremal.lean#L587)) | (1) the maximum principle available in Lean is stated on open subsets of a finite-dimensional space, and `SL₂(ℝ)` is not open in `Mat₂(ℝ)`; (2) with the full boundary conditions the conclusions of the maximum principle hold for every admissible trajectory with a covector whose reduced costate vanishes, so the nontriviality of `(λ_cost, Λ₁, Λ_R)` does not follow (E21) | E21 |
| Theorem 7.7.1, step 6 (the fixed points of `f⁴` near `q_oct`) | for each `d` near `d_oct`, `q_fix(d)` stays hyperbolic and the implicit function theorem inverts `f_d⁴ - I` near `q_fix(d)`; "thus, the only fixed points near `q_oct` are the fixed points `q_fix(d)`" (TeX 6612–6620) | the inverse function theorem applied once, at `q_oct`, to `Ψ = (section constraints, f⁴ - id)`, whose constraints include `d = det Λ₁`: its derivative is injective because `A⁴ - I` is invertible on the tangent space of the section (step 5), so `Ψ` is injective near `q_oct`, and a fixed point with `det Λ₁ = d` has the same image as `q_fix(y₀(d))`, with `y₀(d)` from Remark 7.5.2 as in the book ([`iso_fixedPoints`](SmoothedPolygons/Ch7/Isolated/FixedPoints.lean#L179)) | a separate application for each `d` gives a neighbourhood of each `q_fix(d)`, not one uniform in `d`, which the conclusion needs; the single application gives the uniformity, and the hyperbolicity of `q_fix(d)` for `d ≠ d_oct` is not needed | E32 |

Every other proof follows the book's argument. The gaps of Theorem 2.2.2 (E2), Theorem 2.3.9 (E7),
Lemmas 2.2.6, 2.2.7, 2.4.3 (E5, E9), Lemma 3.1.8 (E34), Lemma 7.5.5 (E30), Theorem 7.5.6 (E31) and
Theorem 7.7.1 apart from its step 6 (E32) are filled along the book's lines, and the index slip of
Lemma 2.4.5 (E10) is corrected. In Lemma 2.4.3 the formal proof bounds the turning of the tangent
by the hyperbolic arc of Remark 2.2.4 itself rather than by the osculating circle the book derives
from it, and treats the curves `j ≠ 0` through `σ₁` rather than the arclength reparametrization of
`σ₂`, a symmetric choice. Proposition 6.4.1 applies
left-invariance once, with `h = g⁻¹`, where the book writes `f(g, u) = TL_g f(e, u)` and cancels
`TL_{g⁻¹}TL_g`: the same identity in one step. The "direct calculation" of Theorem 7.7.1, which the
book does not give, splits each basis vector of the section's tangent space into the direction of
the flow (where the derivative of `f` is `0`), the tangent of the curve of fixed points `q_fix(y₀)`
(where it is the identity) and costate directions (where the flow is affine); since the book gives
no calculation to follow, this is not a departure. Remarks 6.6.1, 7.5.2 and 7.6.4 have no proof in
the book (E38, E36, E37); the proof of Remark 7.5.2 follows the hint of a TeX comment. In the proof
that minimizers are extremals (§6.2), the identity of Proposition 6.4.1 and the trivialization of
Proposition 3.6.1 are checked in matrix coordinates instead of being taken from their Lean
statements, which are about Mathlib's Lie groups (Section 6); the identity is the same.

The cited results that [`External/`](External) proves are proved by their sources' arguments, except:

| Cited result | The source's argument | The formalization's | Why |
| --- | --- | --- | --- |
| Mahler 1947, Theorem 2 (Theorem 2.3.7) | uses its own Lemma 5 (a convex hexagon `H` has `Δ(H) = V(H)/4` and a unique critical lattice, the midpoint lattice, justified by reference to the unique tiling by translates of `H` in another paper) and, in footnote 8, Lemma 5 of another paper (no arc between consecutive lattice points is a segment) | an exact formula for the area of the hexagon of tac-lines, `V(H) = (4 − p²/(D₀D₁D₂))Δ(K)`, gives the area and the bisection; the footnote is derived from Mahler's Theorem 1 | the uniqueness of the critical lattice of a hexagon rests on a uniqueness theory of lattice tilings that Lean lacks and that the source does not give; the exact formula avoids it |
| Mahler 1947, Lemma 3 | stated without proof, with a reference to Lemmas 8 and 12 of paper A, whose proof quotes Theorems B–E of Mahler 1946 (Section 2); paper A's Lemma 1 takes `Δ` of the square from Minkowski's theorem on linear forms, and Mahler 1946 quotes Theorems 2 (selection) and 8 (existence of critical lattices) of its Part I | Mahler's proofs throughout, with the repairs listed below, except that `Δ` of a parallelogram comes from Mahler's own example in §2 of paper A with its Lemmas 2 and 3 (and Lemma 1 is proved in the parallelogram's coordinates, not after an affine map to the square), and that Part I's Theorems 2 and 8 are proved in the plane, by reduced bases and Mahler's compactness theorem | these three results are quoted from works outside the three papers; in the plane Mahler's example and standard arguments give them directly |
| Fejes Tóth's theorem (Theorem 2.1.3) | Fejes Tóth: Dowker's theorem and the cell decomposition of a finite packing, counted with Euler's formula | Dowker's theorem by an alternating merge of normal angles; the cell lemma by maximal cells (Böröczky 2003, Lemma 5), the convexity of their holes by a counting argument on sides instead of Böröczky's walk around boundary cycles, and the side count by angle sums instead of Euler's formula | Mathlib has neither Euler's formula for planar maps nor the Jordan curve theorem, on which the cycle and Euler arguments rest; Dowker's area formula for polygons is likewise missing, and the merge argument needs only measure additivity |
| The Pontryagin maximum principle (§6.2; Agrachev–Sachkov, Theorem 12.5 with free time) | Agrachev and Sachkov's Chapter 12, on a smooth manifold, in the chronological calculus (operators on `C^∞(M)`), with complete smooth vector fields, the well-posedness of Carathéodory solutions cited from Gamkrelidze, and Brouwer's theorem without reference; free time with a cost left to the reader | the same argument in coordinates on an open subset of a finite-dimensional space, the chronological calculus read pointwise along trajectories (D1, D2); a cut-off near the reference trajectory instead of completeness, and well-posedness by Picard iteration and Gronwall's inequality (D11); time changes by measurable new times (D7); one supporting covector for all needle variations (D9); free time with a cost and mixed boundary conditions through one auxiliary system (D6); Brouwer's theorem from the FixedPoint package (D10) | Mathlib has no chronological calculus and no well-posedness for measurable controls; the source derives its reparametrization for a smooth new time and applies it to measurable ones (D7); its proof of Theorem 12.4 takes a covector for each finite needle variation, while the maximum condition at almost every time needs one for all (D9); the free-time case with a cost is left to the reader |

Mahler's Lemma 3 is otherwise proved by the arguments of paper A and Mahler 1946 (Section 2). They
have errors and gaps, all repaired; [`External/MahlerIrreducible/Lemma3.lean`](External/MahlerIrreducible/Lemma3.lean) lists them with the
Lean names:

- **Mahler 1946, proof of Theorem C (p. 337), error.** The function
  `G(X) = F(X){1 + (δ/σ) max(0, σ − ||X|⁻¹X − |P|⁻¹P|)}` is not even (`G(P) = (1 + δ)F(P)` but
  `G(−P) = F(P)`), so `H : G ≤ 1` is not a star body and contains `−P`, whereas paper A's Lemma 10
  asserts that `H` omits `±P` (proved in Lean,
  [`External.Mahler1946.m46c_mahlerG_not_distanceFunction`](External/Mahler1946/TheoremC.lean#L392)). Repaired by measuring the distance from
  `|X|⁻¹X` to the nearer of the two directions `±|P|⁻¹P`; the rest of the proof stands, except that
  in its last step one of the two points `±λQ_s`, not necessarily `λQ_s`, lies in the cone.
- **Mahler 1946, proof of Theorem E, gap.** "There exists a neighbouring lattice `Λ*` which is
  `K*`-admissible and of determinant `d(Λ*) < d(Λ)`" is asserted without argument; filled by the
  deformation that proves Minkowski's (A) ([`External.Mahler1946.m46e_turn`](External/Mahler1946/TheoremE.lean#L369)).
- **Mahler 1946, §4, gap.** That the points `P_k*` are the only points of `Λ*` on or near `C` for
  small `ε` is stated without proof; it is proved ([`External.Mahler1946.m46e_near`](External/Mahler1946/TheoremE.lean#L92)).
- **Paper A, proof of Lemma 1, error.** "`±θP₀` are its only points which are inner points of
  `K₀`" fails for `θ < 1/2`; the argument survives, since all such points are multiples of `θP₀`,
  none of them an inner point of `H`.
- **Paper A, proof of Lemma 5, slip.** "lies on `L**`" should read "lies on `C`".
- **Paper A, gaps.** The Corollary to Lemma 5 has no proof (supplied,
  [`External.MahlerIrreducible.ml5_lemma5_cor_six`](External/MahlerIrreducible.lean#L1474)); in class B of Lemma 13, the line `L′` through `P`
  missing `H′` is not justified (filled by a support line at the extreme point `P`, tilted
  slightly); and
  Lemma 12 does not follow from Theorems D and E alone, which need a dense set of boundary points
  on critical lattices with just six boundary points: paper A's Corollary to Lemma 5 supplies
  them when `K` is not a parallelogram, and its Lemma 1 settles parallelograms
  ([`External.Mahler1946.m46e_lemma12`](External/Mahler1946/TheoremE.lean#L759)). Smaller steps left to the reader (the reduction in Lemma 1,
  three steps of class A of Lemma 13, two details of Theorems D and E) are written out.

The readings: everything is in the plane; the domains are symmetric convex domains, whose gauge is
Mahler's distance function; the sup norm of `Fin 2 → ℝ` replaces the Euclidean length in the
direction `|X|⁻¹X` and in the neighbourhoods `|X − Q| ≤ ε` (only their continuity and homogeneity
are used); and irreducibility is tested against symmetric convex subdomains, where Mahler admits
all star domains (paper A's Lemma 13 bridges the two; Section 6).

The maximum principle is otherwise proved by Agrachev and Sachkov's argument (Section 2). The
README of the OptimalControl package lists the departures, D1–D11, to which its docstrings refer:
D1, the manifold is an open subset of a finite-dimensional real normed space; D2, the
chronological calculus is read pointwise along trajectories, in coordinates; D3, the system and
the cost are `C¹` in the state instead of `C^∞`; D4, the control set is compact (the source tacitly
needs `f(q, u(t))` locally bounded), and the auxiliary parameter sets of §§12.3–12.4 are compact
intervals; D5, strong local minimizers instead of optimal controls; D6, free time with a cost and
mixed boundary conditions, left to the reader (pp. 177, 179, 184), through one auxiliary system;
D7, measurable time changes; D8, Lemma 12.1 in the form of its Remark (1), on any convex cone, with
the map Lipschitz near the vertex on the cone and differentiable there within it; D9, one
supporting covector for all needle variations; D10, Brouwer's theorem from the FixedPoint package;
D11, well-posedness and differentiable dependence proved, with a cut-off. D3 and D5 generalize the
statement. The source's proof has three gaps, all repaired; an independent agent checked them
against the source:

- **Lemma 12.1, Remark (1).** The remark extends the lemma to any convex cone, but the proof takes
  points in the interior of the cone, which is empty for a cone with empty interior, a case the
  remark allows. The statement is true: the formal proof takes the points as combinations of
  points of the cone with positive coefficients and uses no interior
  (`HasFDerivWithinAt.zero_mem_interior_image_inter_cone`). For the cones to which the source
  applies the lemma, `ℝᵏ₊` and its product with a space of parameters, its step is valid as written.
- **A needle at `t₁`.** In the proof of Lemma 12.2 the set of Lebesgue points from which the needle
  times are taken may contain `t₁`, and a needle at `t₁` gives no variation on `[0, t₁]`. Such a
  time is moved to a nearby Lebesgue point of `(0, t₁)`, as the source moves repeated times.
- **The needle map.** That the end point of the needle variations is Lipschitz in their lengths and
  differentiable at `0`, with partial derivatives the vectors `g_{τᵢ,uᵢ}(q₁)` (p. 172), is stated
  without proof; it is proved (`ControlSystem.hasFDerivWithinAt_needle`).

Two points that might look like gaps are not: `t₁ > 0`, which Lemma 12.2 needs, is the source's
standing assumption ("Fix an arbitrary instant `t₁ > 0`", p. 163); and Theorem 12.5 states
nontriviality as `(λ_t, ν) ≢ (0, 0)`, which, by the uniqueness for the adjoint equation, the formal
statement strengthens to every `t`.

Filippov's theorem is proved by the standard argument; it was written before we had Agrachev and
Sachkov's text and was not compared with their proof (Section 2).

## 8. What each result depends on

The results from prior work that the proofs use are all proved (Section 2), stated in
[`External/`](External): Fejes Tóth's theorem (through Theorem 2.1.3, in Theorem 2.2.2 and the results after it), Gruber's
formula (Definition 2.1.2), the theorems of Minkowski and Mahler (Theorems 2.3.6, 2.3.7 and
everything that uses them), Mahler's Lemma 3 with the results of paper A and Mahler 1946 that
prove it (Lemma 2.2.5 and the remark after Definition 2.3.5), the Euler–Arnold equation
(Proposition 6.5.1 and the proof that minimizers are extremals), and the Pontryagin maximum
principle (that proof), which is proved in the OptimalControl package with Brouwer's theorem
from the FixedPoint package. Filippov's theorem is proved as Theorem 6.1.1 and used by no other
result. Every declaration depends only on [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound)
(`lake env lean scripts/Audit.lean`, which checks the 5163 declarations of the library and the
axioms of each numbered result, through the packages it uses).

The route check (`python3 scripts/route_check.py check docs/paper_routes.tsv --accept
docs/route_differences.tsv`) compares, for each of the 68 results of the book found in the Lean
code, the numbered results that the Lean proof uses with those that the book's proof cites. It
passes: every difference is recorded in [`docs/route_differences.tsv`](docs/route_differences.tsv) with its reason. The 61
differences are of these kinds:

- results the book uses without `\ref` ("by the previous lemma", "immediate from the previous
  proposition", an equation cited by number such as the transversality condition `eqn:theta-k` of
  Lemma 7.5.5 in Theorem 7.7.1, "the real number constructed in Section 7.5" for Remark 7.5.2's
  `y₀(d)`) or implicitly (for instance the star domain of Theorem 4.4.1 as the state space, in
  Lemma 4.5.2 and Theorems 7.5.6 and 7.7.1), and three basic facts used throughout (Lemma 7.1.1,
  Lemma A.6.4, Lemma 3.3.4); conversely, Lemma 2.4.2 cites Lemma 2.4.5 only by "Compare the proof
  of Lemma 2.4.5" and does not use it;
- citations whose content the formal statements take as hypotheses or definitions: Lemma 2.4.3
  (about `K_min` only; Theorem 3.1.4(3) is false without its conclusion, E13), Lemma 2.4.5 (item 5
  of a balanced pair), Lemma 5.0.4 (Chapter 5, out of scope) and Proposition 3.6.1 (the left
  trivialization is part of the statement of Proposition 6.4.1);
- in the proof that minimizers are extremals (`sec:PMP`, the label of §6.2), Propositions 3.6.1
  and 6.4.1, checked in matrix coordinates rather than applied in their Lean form, which is about
  Mathlib's Lie groups (Section 6), and Lemma 4.2.1, which §6.2 cites for the upper half-plane form
  of the costate equations (§6.8, which "will not be used elsewhere in the book"), while the proof, like
  Problem 6.7.1, works in the variables `(g, X, Λ₁, Λ_R)`;
- Theorem 2.1.3 converting statements about the worst packing density into the lattice arguments
  that prove them, as the book says it does (TeX 1226);
- statements that assume what the book derives from a cited result (the star inequalities in
  Lemma 3.3.1 and Theorem 4.4.1; the matrices `Y_z(r)` in Lemma A.11.1);
- Lemma 3.3.1, for which the book gives three proofs and the formalization follows the first;
- identities that the book takes from a result stated more generally or along trajectories, and
  that the formal proof checks at the point where they are needed (Lemma 4.2.4, Theorem 6.8.2);
- the repairs of gaps: Lemma 2.2.5 (E4), Theorem 2.3.9 (E7), Lemma 2.4.3 (E9), Lemma 4.3.1 (E19),
  and the added uniqueness step in Lemma 7.5.5 (E30);
- Theorem 7.5.6 uses the explicit lift constructed for Theorem 7.5.1 rather than the statement of
  Theorem 7.5.1, Lemma 7.5.3 identifies its switching functions with that lift, and Lemma 7.5.5
  uses the trace computed in the proof of Theorem 7.5.1;
- the last sentence of the proof of Theorem 7.5.1 ("Lemma 7.5.3 supplements the proof") concerns
  the maximum property, which belongs to Theorem 7.5.6.

## 9. Not formalized

- **Outside the chosen scope:** Chapter 1; Chapter 5 (compactification), the next layer of the
  plan for the remaining chapters (Section 11); Chapters 8–16, including the main theorem (Mahler's
  First conjecture, Theorem 16.3.1); Appendix A.1–A.5 and A.7–A.10; Appendix B.
- **Within the formalized chapters:**
  - The application of Filippov's theorem in §6.1 (an optimal control exists for the Reinhardt
    problem, TeX 4553–4600), which rests on the compactification theorem of Chapter 5
    (Theorem 5.0.2) and belongs to the next layer with it. Theorem 6.1.1 itself is proved (E35).
    The maximum principle and the claim of §6.2 that every minimizer is an extremal are proved
    (Section 2); the existence of a minimizer is what this application adds.
  - Remarks 7.6.1 and 7.6.3, which report numerical observations as conjectures: the area of the
    smoothed `(6k+2)`-gon "appears" to increase with `k` to `π`, and the smoothed `(6k−2)`-gons
    "seem" to satisfy every condition of an extremal except the sign of `λ_cost` (Section 11).
  - The other remarks are not stated as results, except Remarks 2.2.4, 6.6.1, 7.5.2 and 7.6.4 and
    the remark after Definition 2.3.5. Some of their content is proved where it is used: the hexagon of
    Remark 3.1.7, at a multi-point, in the proof of Lemma 3.1.8; the equivariance of `Φ` (Remark
    4.2.2); the positive slope of `χ₃₂` at `0` (Remark 7.5.4) in the proof of Theorem 7.7.1; the
    smoothed `(6k−2)`-gons of Remark 7.6.2 in Remark 7.6.4. Remark 4.3.2 (the cost in the disk and
    hyperboloid models) is not formalized; Remarks 3.1.2, 3.4.3, 4.1.2, 6.5.2 and 7.7.2 are
    commentary and pointers to the literature or to the appendices.

## 10. The paper in the literature

Searched on 2026-11-05: web search, the arXiv API, zbMATH Open, OpenAlex, Semantic Scholar,
Crossref, GitHub, and the Isabelle AFP index. Google Scholar could not be queried.

### Before the paper

- K. Reinhardt, *Über die dichteste gitterförmige Lagerung kongruenter Bereiche in der Ebene und
  eine besondere Art konvexer Kurven*, Abh. Math. Sem. Univ. Hamburg 10 (1934) 216–230: the
  smoothed octagon, the existence of a minimizer and the structure results that Chapter 2 recalls.
  Published.
- K. Mahler, *On irreducible convex domains* and *On the area and the densest packing of convex
  domains*, Proc. KNAW 50 (1947) 98–107, 108–118, and *On the minimum determinant and the
  circumscribed hexagons of a convex domain*, Proc. KNAW 50 (1947) 692–703: the construction of the
  smoothed octagon and the remark the book calls Mahler's First conjecture (the book cites the last
  two, and Proc. KNAW 49 (1946) 331–343). Published.
- V. Ennola, *On the lattice constant of a symmetric convex domain*, J. London Math. Soc. 36 (1961)
  135–138, and P. P. Tammela, Izv. Vyssh. Uchebn. Zaved. Mat. 1970, no. 12, 103–107: lower bounds
  for the least packing density, Tammela's `0.892656…`. Published.
- F. L. Nazarov, Zap. Nauchn. Sem. LOMI 151 (1986) 104–114 (English: J. Soviet Math. 43 (1988)
  2687–2693): the smoothed octagon is a local minimum. Published.
- T. C. Hales, [*On the Reinhardt conjecture*](https://arxiv.org/abs/1103.4518), Vietnam J. Math.
  39 (2011) 287–307: the problem as a problem of Bolza; a minimizer has a `C¹` boundary with
  Lipschitz derivative; a piecewise analytic minimizer is a smoothed polygon; and two conjectures
  (Five Link, Link Reduction, §7.6) that would reduce the problem for smoothed polygons to a
  finite-dimensional computation. Published.
- T. C. Hales, [*The Reinhardt conjecture as an optimal control problem*](https://arxiv.org/abs/1703.01352),
  preprint (3 March 2017; version 1 only, no journal version): the reformulation as an optimal
  control problem; it claims that the smoothed octagon and the smoothed `(6k+2)`-gons are
  Pontryagin extremals with bang-bang control (Theorem 7.5.6 of the book, whose full write-up is the
  book), and, in §4.5, that the smoothed octagon is isolated among extremals and a strict local
  minimum in a micro-local sense, by a sketch resting on interval-arithmetic computations (the
  "different proof" of Remark 7.7.2). Its remarks on the smoothed `(6k−2)`-gons are the book's
  Remarks 7.6.2–7.6.3.
- K. Vajjha, [*On the Reinhardt Conjecture and Formal Foundations of Optimal Control*](https://arxiv.org/abs/2208.04443),
  PhD thesis, University of Pittsburgh (2022): the Hamiltonian structure and Lax equation, the
  compactness of the region of extremals, and the Fuller system near the singular locus.
- Earlier work the book does not cite: Y. Kallus, [*Pessimal packing shapes*](https://arxiv.org/abs/1305.0289),
  Geom. Topol. 19 (2015) 343–363 (the regular heptagon is a local pessimum for double-lattice
  packing), and C. A. Rogers, *The closest packing of convex two-dimensional domains*, Acta Math.
  86 (1951) 309–321.

### Concurrent work

No other paper on the Reinhardt problem appeared within a year of the book. Undergraduate posters
by L. Song and S. Sluis-Cremer, mentored by Hales
([github.com/lark-song/smoothed-decagon](https://github.com/lark-song/smoothed-decagon): MAA
MathFest, 4 August 2023; JMM, 5 January 2024; an April 2023 poster with N. MacLachlan states only
conjectures), study the maximization of the area over balanced disks and state, without a
published proof, that every smoothed `(6k−2)`-gon is a Pontryagin extremal of it, as Hales's 2017
preprint and the book's Remark 7.6.3 suggest. Their area of the smoothed decagon, `3.22606`, does
not match the book's `3.15` (TeX 6510–6533), which we reproduce (`3.150855`).

### Since the paper

The book is still an unrefereed preprint: only version 1 (7 May 2024) exists, with no journal
reference and no erratum. Hales's blog post (13 May 2024) states that the Reinhardt conjecture
remains open; a Quanta Magazine article (28 June 2024) reports that the work had yet to be peer
reviewed and that H. Cohn and G. Kuperberg, who read it informally, were confident in it. No paper
claims progress on the Reinhardt conjecture since; the only claim we found is M. Ho's unreviewed
Lean repository below (lower bound `0.8950112`, above Tammela's `0.892656`). OpenAlex lists one work
citing the book (B. Grechuk, *One Hundred Open Problems*, in *Landscape of 21st Century
Mathematics*, Springer 2026, pp. 565–607), which we did not read; Semantic Scholar lists none.
Informal: J. Kim's expository notes on the book
([github.com/dylan0301/UnderstandingReinhardt](https://github.com/dylan0301/UnderstandingReinhardt),
August 2026) include a chapter of open problems.

### Formalizations

- This is, to our knowledge, the first formalization of Theorems 7.5.6 and 7.7.1 and of the
  Hamiltonian part of the book (Chapters 6–7: costates, switching functions, Pontryagin
  extremals, and the lift of a minimizer to an extremal). The state
  dynamics and the cost of Chapter 3 were formalized independently, three days earlier, in
  M. Ho's repository below.
- M. Ho, [github.com/sunfishho/reinhardt-density-bound](https://github.com/sunfishho/reinhardt-density-bound)
  (created 2 November 2026, three days before this search): an unreviewed, AI-assisted Lean 4
  development claiming the lower bound `0.8950112` for the packing density of every centrally
  symmetric convex disk, which would improve Tammela's `0.892656` (1970), with Lean proofs of
  results labelled after the book's Chapters 2, 3 and 5. Among them are the area identity of §3.2
  (`FrameBoundary.cost_eq_area`, proved by a radial-sector area formula rather than Green's
  theorem) and the easy half of Theorem 2.2.2 (`packingDensity_ge_hexagon`). Its README reports
  Comparator and NanoDa runs on 30 October 2026 and says that a clean `lake build` has not been
  validated. It has no Hamiltonian or costate, and does not formalize Theorem 7.5.6. This work did
  not consult or use it.
- The Pontryagin maximum principle has, to our knowledge, its first complete formal proof in the
  OptimalControl package that this formalization requires
  ([github.com/vltanh/lean4-optimal-control](https://github.com/vltanh/lean4-optimal-control),
  published 7 November 2026): free terminal time, an integral cost, mixed boundary conditions and
  strong local minimizers, by Agrachev and Sachkov's argument. The earlier attempt in Lean,
  [willcforte/pontryagin-lean](https://github.com/willcforte/pontryagin-lean) (13 May 2026),
  states its key steps as axioms; this work does not use it. Brouwer's fixed-point theorem, which
  the proof needs and Mathlib lacks, is proved in the FixedPoint package
  ([github.com/vltanh/lean4-fixed-point](https://github.com/vltanh/lean4-fixed-point)) by Milnor
  and Rogers' analytic argument; it has earlier formal proofs, in Lean among other proof
  assistants, and that proof was written without consulting them.
- Related formal developments: Green's theorem for elementary regions in Isabelle/HOL (Archive of
  Formal Proofs), and the Jordan curve theorem in HOL Light (Hales 2007).
- The classical results of Chapter 2 that this formalization proves — Fejes Tóth's theorem that
  lattice packings are densest for centrally symmetric disks, Dowker's theorem on circumscribed
  polygons, Minkowski's and Mahler's theorems on critical lattices and circumscribed hexagons, the
  existence of critical lattices in the plane, and the planar Tietze–Nakajima theorem — have, as far
  as we found, no earlier formal proof (web search and the pinned Mathlib, 6 November 2026; Mathlib
  has Minkowski's convex body theorem and Blichfeldt's lemma, which the proofs use).

## 11. What's next

Plans for follow-up papers are kept in `NEXT.md`, which is not published.

### Open directions

- **Toward the main theorem.** With Chapter 2 formalized, the reduction of the Reinhardt problem to
  the balanced Reinhardt problem in circle representation (Problem 2.4.8) is in place, and the
  control problem of Chapter 3 is its reformulation. What separates this from Mahler's First
  conjecture (Theorem 16.3.1) is Chapters 5 and 8–16, which a plan divides into layers, each ending
  in a releasable state whose remaining assumptions are explicit hypotheses. Layer 1, the
  maximum principle and the extremal lift of every minimizer, is done (Section 2). Layer 2, next,
  is the existence of a minimizer by the book's route: the compactification of Chapter 5
  (Theorem 5.0.2) and its application in §6.1 of Filippov's theorem (proved here on `ℝⁿ`, and to
  be extended to an initial set, coupled end points and the closed state constraint). Layer 3 is
  Chapter 8, with Proposition 8.1.3 (edge extremals, through the maximum principle for the edge
  problem), and the main theorem conditional on one named hypothesis: that the switching times of
  an extremal do not accumulate at a time where its lift meets the singular locus. The later
  layers discharge it: the triangular Fuller system of Chapter 13 and its global basin (Chapter 15,
  Theorem 16.1.1), the analytic extension of Chapter 14 with Theorem 16.4.1, and Theorem 14.4.1
  (no return), whose proof rests on a numerical computation of an unstable curve.
- **Local optimality of the octagon.** Theorem 7.7.1 is proved (E32): the octagon is isolated among
  extremals. Hales's 2017 preprint (§4.5) sketches another proof of the isolation, by an
  interval-arithmetic expansion of the cost along the one-parameter family of deformations
  satisfying the endpoint conditions (the "different proof" of Remark 7.7.2), and derives from the
  same expansion that the octagon is a strict local minimum in a micro-local sense. That
  computation is not published in checkable form; formalizing it would add local optimality to
  Theorem 7.7.1.
- **The other smoothed `(6k+2)`-gons.** Hales's 2017 preprint (Remark 49) asks whether the
  smoothed `(6k+2)`-gons with `k ≥ 2` are local minima in the sense in which it shows the octagon to
  be one; neither the preprint nor the book answers it. Their isolation among extremals, the
  analogue of Theorem 7.7.1, is not claimed either. The characteristic polynomial of the matrix of
  the Poincaré map on the section is computed in closed form for every `y₀`
  ([`iso_sectionMatrix_charpoly`](SmoothedPolygons/Ch7/Isolated/Hyperbolic.lean#L343)), but that matrix is identified with the derivative of the
  Poincaré map only at the octagon's `y₀` ([`iso_fderiv_basis`](SmoothedPolygons/Ch7/Isolated/Poincare.lean#L710)); extending the identification would
  reduce the hyperbolicity of the fixed points `q_fix(y₀(k))` to inequalities in `y₀`.
- **The smoothed `(6k−2)`-gons.** Remark 7.6.3 says they seem to satisfy every condition of an
  extremal except the sign of `λ_cost`, and the 2023–24 posters of Song and Sluis-Cremer
  (Section 10) state, without a published proof, that they are extremals of the area-maximization
  problem. The construction of §7.5 should adapt: control `e₂` from `z₀ = iy₀` with `y₀ > 1`,
  `t_sw = ln((3y₀² + 1)/4)/(√3y₀)`, boundary condition `z(z₀, t_sw) = R·z₀`, mode sequence
  eqn:3k+2, and the closing condition `4/(3y₀² + 1) = 2cos(πk/(3k − 1))`, which the book does not
  state (the 2017 preprint's `θ_k = πk/(3k − 2)` does not close). The new ingredient is the sign of
  the switching functions, in place of Lemma 7.5.3. Numerically, for `k = 2, 3`, the lift exists
  and has `λ_cost > 0`. The state trajectories are already constructed in Lean for every real
  `k > 1` ([`remark7_6_4_exists`](SmoothedPolygons/Ch7/Remarks.lean#L1900)); what is missing is the closing condition `g(t_f) = R` for integral
  `k` and the costate lift.

### Simpler proofs

- **Lemma 7.2.1.** By Lemma 7.1.1, `⟨Z_u, Φ(x + iy)⟩ = (2ax + b - c(x² + y²))/y` is a constant
  `κ` along a constant-control trajectory, so `c(x² + y²) - 2ax + κy - b = 0`: a circle, or a line
  when `c = u₀ = 0`. This replaces the Möbius-geometry discussion of §7.1–7.2; checked in Lean in a
  scratch file (about 45 lines against about 300 for the book's route).
- **Lemma 7.5.5.** For `A ∈ SL₂(ℝ)` with `tr A = 2 cos θ`, Cayley–Hamilton gives
  `A^n sin θ = sin(nθ) A - sin((n - 1)θ) I`; with `n = 3k + 1` and `θ = θ_k` this gives
  `(R⁻¹g_sw)^{3k+1} = (-1)^k I`, the direction the lemma states (E30), without eigenvalues.
- **Lemma 7.5.3**, case `y ∈ [2, 3]` of `∂²f/∂y² ≥ 0` (left as an exercise by the book, E29): with
  `b = 8y√y/(3y + 2)`,
  `∂²f/∂y² = A - 4b + 4(r ln(r/b) - (r - b)) + r(-1 + 2/y + 4 ln(4y/(3y + 2)))`, and both brackets
  are `≥ 0` by `ln u ≥ 1 - 1/u`. This avoids the formal proof's `r* = 2√y e^{(y-2)/(4y)}` and
  `e^x ≤ 1/(1 - x)`; the step `A - 4b > 0` is unchanged.
- **Proposition 3.1.9.** On a balanced disk `g = [σ₀ σ₂][s₀* s₂*]⁻¹` on `ℝ` with `σ_j`, `σ_j'`
  bounded and `σ_j'` Lipschitz, so the argument of Theorem 3.1.4(3) gives `X` Lipschitz on `ℝ`
  directly; this saves the formal proof's restriction to `[0, 2P]` and periodic extension. The
  reparameterization step is unchanged.
- **Lemma 3.1.8.** The formal proof follows the book (the hexagon `H_K(t)`, its area, the area of
  `P_K` and Reinhardt's observation). One identity does the same work: since
  `σ_i = σ_{i-1} + σ_{i+1}` and `det(σ_{i-1}, σ_{i+1}) = √3/2`, if `σ_{i-1}` and `σ_{i+1}` move on
  the lines `det(d₁, x - p₁) = 0` and `det(d₂, x - p₂) = 0`, then
  `det(d₁, σ_i - p₁)·det(d₂, σ_i - p₂) = det(d₁, p₁)det(d₂, p₂) - (√3/2)det(d₁, d₂)`, a constant
  (the left side is `det(d₁, σ_{i+1})det(d₂, σ_{i-1})`, and the plane identity
  `det(a, b)det(c, e) - det(a, e)det(c, b) = det(a, c)det(b, e)` evaluates it). The two gaps that
  need regularity (the lines are not parallel, the constant is not `0`, E34) remain.
- **Theorem 7.7.1, step 6.** The injectivity of `A⁴ - I` on the tangent space `T` of the section
  does not need the linear independence of the basis [`iso_sectionBasis`](SmoothedPolygons/Ch7/Isolated/Defs.lean#L206)
  ([`iso_sectionBasis_linearIndependent`](SmoothedPolygons/Ch7/Isolated/Hyperbolic.lean#L319)): the four vectors span `T` and `A` acts on their
  coefficients by [`iso_sectionMatrix`](SmoothedPolygons/Ch7/Isolated/Defs.lean#L220), whose `M⁴ - I` is invertible, so `A⁴ - I` maps `T` onto `T`
  and is injective because `T` is finite-dimensional.
- **Theorem 7.5.1.** Centralizing `h` only uses `h ≠ ±I` (immediate from `tr h ∈ (1, 2)`);
  ellipticity is not needed, and the 2017 preprint already argues so.

### The formalization

- **[`Basic/`](Basic)** holds general mathematics that belongs in Mathlib ([`Basic/README.md`](Basic/README.md) says where):
  entrywise calculus for matrix-valued curves, the derivative of the matrix exponential, the
  fundamental theorem of calculus and Grönwall uniqueness for matrix ODEs; the action of `SL₂(ℝ)` on
  generalized circles; the area of a region bounded by a star-shaped closed curve and its convexity
  when the tangent turns one way; Dowker's theorem on least-area circumscribed polygons; the lattice
  tiling by a centrally symmetric hexagon; the angles and angle sum of convex polygons; Fejes Tóth's
  cell lemma for finite packings; the planar Tietze–Nakajima theorem; the existence of critical
  lattices; and the structure of lattice-packed centrally symmetric convex bodies.
- **Two packages of their own** hold the general theory that this formalization needed and that
  others may import: OptimalControl
  ([github.com/vltanh/lean4-optimal-control](https://github.com/vltanh/lean4-optimal-control)),
  with control systems with Carathéodory trajectories (existence, uniqueness and differentiable
  dependence for measurable controls), Filippov's theorem and the existence of optimal controls,
  measurable selection, needle variations and the maximum principle; and FixedPoint
  ([github.com/vltanh/lean4-fixed-point](https://github.com/vltanh/lean4-fixed-point)), with
  Brouwer's fixed-point theorem. The project requires OptimalControl at a pinned commit, and
  OptimalControl requires FixedPoint.
- **Mathlib** lacks `det exp(A) = exp(tr A)` for matrices (a TODO in
  `Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean`), Jacobi's formula, Green's theorem for
  Jordan domains, the theory of regular elements of `𝔰𝔩₂`, any measurable selection theorem,
  Brouwer's fixed-point theorem, and existence and uniqueness of Carathéodory solutions (its
  Picard–Lindelöf theorem needs continuity in time); each was a detour here. It also does not identify the bracket of its Lie algebra of
  left-invariant vector fields on `Mat₂(ℝ)ˣ` with the matrix commutator, so Propositions 3.6.1 and
  6.4.1 are applied in matrix coordinates (Section 6).
- **Filippov's theorem** needs no smoothness of `f` in `q`: continuity, bounded velocities and the
  convexity hypotheses suffice, so the standing assumptions `hfq`, `hfq'` that the statement keeps
  from the source (Section 5) could be dropped, and the theorem holds for any finite-dimensional
  state space (`OptimalControl.ODE.ControlSystem`, in the OptimalControl package, is stated so).
- **Toward the main theorem.** With the maximum principle proved, Chapters 5 and 8–16 still need
  Filippov's theorem on the compactified state space of Chapter 5 (it is proved here on `ℝⁿ`), the
  stable manifold theorem, Weierstrass preparation, and a rigorous version of the numerical
  containments of the global basin theorem (Theorem 16.1.1), which the book checks from
  Mathematica plots.
