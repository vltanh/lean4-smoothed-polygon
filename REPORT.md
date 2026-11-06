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
  bang-bang solutions and the smoothed `(6k+2)`-gons (Chapter 7), and Appendix A.6 and A.11. The
  book's main theorem, Mahler's First conjecture (Theorem 16.3.1), and Chapters 1, 5, 8–16 are not
  formalized (Section 9).
- **Proved.** Every numbered result of Chapters 2, 3, 4, 6 and 7 is proved, except Lemma 3.1.8,
  Theorem 6.1.1 (Filippov, cited), Definition 6.3.1 and Proposition 6.4.1 (general left-invariant
  systems, unused by the rest) and Theorem 7.7.1 (whose proof the book only sketches); Section 9.
  Lemma 2.2.1 is false as printed and is proved in corrected form (E1). The main results are
  Theorem 7.5.6 (each smoothed `(6k+2)`-gon is a Pontryagin extremal of the Reinhardt control
  problem with bang-bang control) and the smoothed octagon's packing density: the octagon's
  trajectory bounds a balanced disk `K` whose area is the cost `√12(8 - √32 - ln 2)/(√8 - 1)` and
  whose greatest packing density is `δ(K) = (8 - √32 - ln 2)/(√8 - 1)`.
- **Nothing is assumed.** Every cited result that a proof uses is proved in [`External/`](External): Fejes
  Tóth's theorem (`δ = δ_L`), Gruber's lattice density formula, the theorems of Minkowski and
  Mahler on critical lattices and circumscribed hexagons, a weak form of one half of Mahler's
  Lemma 3 (all that is used), and the Euler–Arnold equation (Section 2). A Pontryagin extremal is defined by the
  conditions of the maximum principle (Section 6). Theorem 3.1.4(3) keeps one hypothesis for a
  general convex disk (E13, approved by the user); for balanced disks it holds.
- **Build.** `lake build` succeeds; the only `sorry`s are the two statements of [`Challenge.lean`](Challenge.lean),
  by design. There is no `axiom`, `admit` or `native_decide`. [`scripts/Audit.lean`](scripts/Audit.lean) checks that every
  declaration of the library and the two Challenge theorems depend only on [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext),
  [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound). Palomar's Comparator accepts [`Solution.lean`](Solution.lean) against
  [`Challenge.lean`](Challenge.lean) under Lean's kernel and NanoDa.
- **Statements.** One result of the book is false and is formalized in corrected form, with a
  machine-checked counterexample to the printed statement (Lemma 2.2.1, E1, approved by the user).
  Six statements and definitions are corrected for slips: a definition missing a hypothesis
  (Definition 2.3.4, E6), two misprints in definitions (E16, E20), the nontriviality condition of a
  Pontryagin extremal (E21), and missing hypotheses in Theorem 3.1.4(3) (E13, approved by the user),
  Lemma 4.2.3 (E17) and Lemma 7.3.1 (E26). Slips in proofs (E8, E14, E24) are corrected where they
  occur. Otherwise the Lean statements differ from the book's only by the omitted hypotheses of
  Section 5 and the readings of Section 6.
- **Proofs.** Every proof follows the book's argument, except the departures listed in Section 7,
  each forced by an error or gap of the book or by mathematics Mathlib lacks: Lemma 2.2.1 (its
  printed form is false), Lemma 2.2.5 (a gap the book's lines cannot close, closed by Mahler's
  lattice route, chosen by the user), one step each of Lemmas 2.4.2 and 2.4.6, the area formula of
  §3.2 (Green's theorem), Jacobi's formula (Lemma 3.1.12, approved by the user) and Lemma 4.3.1.
  The other gaps are filled along the book's lines. The route check
  ([`scripts/route_check.py`](scripts/route_check.py) against [`docs/paper_routes.tsv`](docs/paper_routes.tsv)) passes; its recorded differences are
  listed with their reasons in [`docs/route_differences.tsv`](docs/route_differences.tsv) (Section 8).
- **Redundant hypotheses.** Eight results of the book and one cited result hold without some of
  their hypotheses; the Lean statements omit them (Section 5). The Challenge keeps the book's
  hypotheses.

## 1. Summary

- **Errors.** Lemma 2.2.1 (Reinhardt's tiling lemma) is false as printed: a lattice packing of a
  centrally symmetric disk need not be a tiling by a hexagon or parallelogram containing the disk
  (E1, refuted in Lean). The book uses only a weaker consequence, which holds, so Theorem 2.2.2 and
  everything after it stand. Two misprints change the meaning of a definition: the terminal
  condition of the Reinhardt control problem (E16) and the sign of the coefficient `a(u)` of the
  half-plane control problem (E20). The nontriviality condition of a Pontryagin extremal, imposed on
  the full costate `(Λ₁, Λ₂)`, makes every admissible trajectory an extremal (E21); it must be
  imposed on the reduced costate `(Λ₁, Λ_R)`, as the formalization does, for Theorem 7.5.6 to say
  anything. Slips that do not affect any result: the definition of a critical lattice omits
  admissibility (E6), an equation written too early in the proof of Theorem 2.3.9 (E7), a sign in
  the proof of Lemma 2.4.2 (E8), an index in the proof of Lemma 2.4.5 (E10), an index in the proof
  of Theorem 3.4.2 (E14), a sign convention in the proof of Proposition 6.5.1 (E22), and the
  eigenvectors of §7.1 (E24).
- **Gaps.** The proof of Lemma 2.2.5 (the minimizer has no corners) has a gap that its shaving
  argument cannot close; the formalization closes it by Mahler's lattice route (E4). The smoothed
  octagon's density value rests on a fact the book never proves, that a balanced disk has least
  circumscribed hexagon of area `√12`; it is true and proved here (E12). The inequality on which the
  maximum principle for the smoothed polygons rests is left "as a tedious but elementary exercise"
  (Lemma 7.5.3, E29): it is true, tight at one corner, and proved here. Lemma 4.3.1 does not justify
  that the minimizer has area less than `π` (E19). Lemma 2.4.6 applies a theorem about smooth
  curves to curves that are only `C¹,¹` (E11). Further gaps, all filled: E2, E3, E5, E7, E8, E9,
  E15, E18, E23, E30, E31. Theorem 7.7.1 has only a proof sketch (E32).
- **Missing hypotheses.** Theorem 3.1.4(3) is false for a general convex disk; it holds under the
  standing assumptions of §2.4 (E13). Lemma 4.2.3 needs `X ≠ 0` (E17). Lemma 7.3.1 needs
  `⟨X, Z_u⟩ ≠ 0` on the control set, which its proof uses (E26).
- **Redundant hypotheses.** Several hypotheses are not needed; the Lean statements drop them
  (Section 5). The most notable: Lemma 7.3.1 holds for every compact convex control set on which
  `⟨X, Z_u⟩ ≠ 0`, not only one in the plane `u₀ + u₁ + u₂ = 1`.
- **Use of cited results.** Chapter 2 rests on cited theorems: Fejes Tóth's `δ = δ_L`, Gruber's
  lattice density formula, Minkowski's and Mahler's theorems on critical lattices and circumscribed
  hexagons, and Shifrin's characterization of convex curves; the control-theoretic chapters cite
  the Euler–Arnold equations (Cushman–Bates, with a sign slip, E22), the Iwasawa decomposition and
  Rademacher's theorem. All are proved here, in [`External/`](External) or from Mathlib, except Shifrin's, which
  is applied outside its hypotheses and replaced by a direct argument (E11) (Section 2).
- **Literature.** Theorem 7.5.6 was announced in Hales's 2017 preprint (Section 10). The book is
  still an unrefereed preprint, with no newer version or erratum. One date in its bibliography is
  wrong, and two citations are to later editions (E33).

## 2. Results from prior work and how the paper uses them

### Proved in `External/`

| Cited result | Source | Lean | Used by |
| --- | --- | --- | --- |
| Euler–Arnold equation for left-invariant Hamiltonians on matrix groups, `μ' = [μ, δh/δμ]` for `μ = pg` | Cushman–Bates, cited in the proof of Proposition 6.5.1 | [`External.euler_arnold`](External/EulerArnold.lean#L72) | [`proposition6_5_1`](SmoothedPolygons/Ch6/Hamiltonian.lean#L319) |
| Fejes Tóth's theorem: for a centrally symmetric convex disk, no packing of congruent copies is denser (even in upper density) than the best lattice packing | L. Fejes Tóth 1950; cited as Theorem 2.1.3 | [`External.fejes_toth`](External/FejesToth.lean#L882) | [`theorem2_1_3`](SmoothedPolygons/Ch2/Density.lean#L252) |
| The upper and lower densities of a lattice arrangement of a convex body are `V(C)/d(L)` | Gruber, *Convex and Discrete Geometry*, Cor. 30.1; cited in Definition 2.1.2 | [`External.gruber_corollary_30_1`](External/Gruber.lean#L320) | [`definition2_1_2`](SmoothedPolygons/Ch2/Density.lean#L86) |
| A critical lattice has a basis and a third point on the boundary forming a parallelogram of area `Δ(K)`, and conversely | Minkowski 1907, Mahler 1946/1947 (Lemma 2); cited as Theorem 2.3.6 | [`External.minkowski_mahler`](External/MinkowskiMahler.lean#L964) | [`theorem2_3_6`](SmoothedPolygons/Ch2/Mahler.lean#L100) |
| The circumscribed hexagon of a critical lattice: unique tac-lines, area `4Δ(K)`, sides bisected, least area | Mahler 1947, Theorems 1 and 2; cited as Theorem 2.3.7 | [`External.mahler_1947`](External/Mahler1947.lean#L1700) | [`theorem2_3_7`](SmoothedPolygons/Ch2/Mahler.lean#L169) |
| In an irreducible domain every tac-line contains a point of a critical lattice (a weak form of the "only if" half of Mahler's Lemma 3; all that is used) | Mahler 1947, Lemma 3; cited after Definition 2.3.5 | [`External.mahler_irreducible`](External/MahlerIrreducible.lean#L196) | [`lemma2_2_5`](SmoothedPolygons/Ch2/Reinhardt.lean#L3754) |

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

### Does the paper use each cited result correctly?

| Cited result | Where | Verdict |
| --- | --- | --- |
| Fejes Tóth's theorem | Theorem 2.1.3; proof of Theorem 2.2.2 | Correct. |
| Gruber, Cor. 30.1 | Definition 2.1.2 | Correct; the packing hypothesis is not needed (Section 5). |
| Minkowski, Mahler (critical lattices) | Theorem 2.3.6 | Correct, with the sources' definition of a critical lattice (E6). |
| Mahler 1947, Theorems 1 and 2 | Theorem 2.3.7, proof of Theorem 2.3.9 | Correct. |
| Mahler 1947, Lemma 3 | remark after Definition 2.3.5 | Correct; the formalization proves the weak form of one half that Lemma 2.2.5 needs. |
| Blaschke selection theorem | proof of Lemma 2.2.5 | Correct, but not sufficient alone for the existence of `K_min` (E4). |
| Hales 2011, Lemmas 11, 17, 18 | proofs of Lemmas 2.4.2, 2.4.3 (recalled) | The recalled arguments have gaps (E8, E9), filled here. |
| Shifrin, Proposition 3.8 | proof of Lemma 2.4.6 | Applied outside its hypotheses (smooth curves); replaced by a direct argument (E11). |
| Pach–Agarwal, Exercise 3.2 and Theorem 2.5 | remarks in §2.1, §2.2 | Not used in proofs. |
| Euler–Arnold equations for left-invariant Hamiltonians (Cushman–Bates) | proof of Proposition 6.5.1 (TeX 5030–5040) | Correct conclusion `Λ₁' = [Λ₁, X]`; the identification of `ad*` with `-ad` is inconsistent with the book's own definition of `ad*` (E22). Proved here in the form the book uses ([`External.euler_arnold`](External/EulerArnold.lean#L72)). |
| Iwasawa decomposition | proof of Lemma 4.1.1 | Correct. |
| Rademacher's theorem | Corollary 3.1.10 | Correct. |
| Jurdjevic (attribution) | Proposition 6.4.1, Corollary 6.5.3 | Corollary 6.5.3 is proved in the book by differentiation; correct. |
| Pontryagin maximum principle (Zelikin–Borisov) | §6.2 | Used as the definition of a Pontryagin extremal; no theorem about it is needed in the formalized chapters. |
| Filippov's theorem (Zelikin–Borisov) | Theorem 6.1.1 | Not formalized (outside the formalized results' proofs). |

The other citations of the formalized chapters (Reinhardt 1934, Minkowski's other works, Hales 2017, Jurdjevic 2016,
Perelomov, Babelon et al., Colombo–de Diego, Gay-Balmaz et al., Vajjha's thesis) give context and
are not used in proofs; Vajjha's thesis is cited for the omitted proof of Theorem 6.8.3.

## 3. Errors and gaps in the paper

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
would then hold for every admissible trajectory. Since `X` moves on the orbit `O_J`, the costate
`Λ₂` is only defined modulo `ℝX` (the annihilator of `T_X O_J = X^⊥`), and `Λ₂ = X` is the zero
covector; the book's reduced costate `Λ_R = [Λ₂, X]` (Remark 6.5.2) removes this ambiguity. The
formalization imposes nontriviality on `(λ_cost, Λ₁, Λ_R)` ([`IsPontryaginExtremal`](Challenge.lean#L171)), the only
reading under which Theorem 7.5.6 has content.

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

**E32. Theorem 7.7.1, §7.7 (TeX 6535–6630): proof sketch.** The proof that the smoothed octagon is
an isolated extremal is a sketch: it rests on "Direct calculation shows that the fixed point is
hyperbolic" for a Poincaré map defined through switching times, which the book does not give.
Not formalized.

**E33. Bibliography and history (Chapter 1).** Tammela's bound is from 1970 (*Izv. Vyssh. Uchebn.
Zaved. Mat.* 1970, no. 12(103), 103–107); the bibliography prints 1969 and gives the running issue
number 103 as the volume. The text's "Ennola in 1961 and Tammela in 1969 showed
`inf δ ≥ 0.8926…`" credits Tammela's bound to both: Ennola proved about `0.88`. The book cites the
1988 English translation of Nazarov's 1986 paper (*Zap. Nauchn. Sem. LOMI* 151) and a 2017
reissue of Kupka's 1990 paper. These do not affect the mathematics.

## 4. Missing hypotheses

| Where | Missing hypothesis | Counterexample without it | In the formalization |
| --- | --- | --- | --- |
| Theorem 3.1.4(3) | `σ_j'` Lipschitz (the standing assumption of §2.4, through Lemma 2.4.3) | unit disk, `σ_j(t) = Rot(t + t^{3/2}) s_j*`, `X = (1 + (3/2)√t)J` | hypothesis of [`theorem3_1_4_lipschitz`](SmoothedPolygons/Ch3/StateDynamics.lean#L283) (approved by the user) |
| Lemma 4.2.3 | `X ≠ 0` | `X = 0`: `T_0 O_0 = 0` but `𝔰𝔩₂/ℝ·0` has dimension 3 | hypothesis of [`lemma4_2_3`](SmoothedPolygons/Ch4/AdjointOrbit.lean#L432) |
| Lemma 7.3.1 | `⟨X, Z_u⟩ ≠ 0` on `U` (used by the proof, TeX 5792) | a segment `U` of the plane `u₀ + u₁ + u₂ = 1` crossing the line where `⟨X, Z_u⟩ = 0`: the Hamiltonian is undefined there | hypothesis `hden` of [`lemma7_3_1`](SmoothedPolygons/Ch7/Faces.lean#L49) |

## 5. Redundant hypotheses

Each hypothesis below is omitted from the Lean statement, which is therefore more general than the
book's. The Challenge statements keep the book's hypotheses.

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

## 6. How the formalization reads the paper

- **Packings and densities (§2.1).** The book's disks `B_r` are Euclidean disks ([`euclidDisk`](Challenge.lean#L280);
  Mathlib's balls on `Fin 2 → ℝ` are squares). A packing is a set of convex disks with pairwise
  disjoint interiors; congruent copies are images under Euclidean motions, reflections included.
  The density ratios are taken in `[0, ∞]`; a density exists when the upper and lower densities are
  finite and equal; `δ(K)` and `δ_L(K)` are suprema of real numbers, over nonempty sets bounded by
  `1`. A lattice is a discrete `ℤ`-submodule of `ℝ²` spanning it, and its determinant is Mathlib's
  covolume, shown equal to `|det|` of any basis ([`definition2_3_2`](SmoothedPolygons/Ch2/Mahler.lean#L57)).
- **Critical lattices and hexagons (§2.3).** A critical lattice is admissible with determinant
  `Δ(K)` (E6). The critical hexagons of §2.2 are the least-area circumscribed centrally symmetric
  hexagons ([`IsLeastAreaHexagon`](SmoothedPolygons/Ch2/Reinhardt.lean#L66), compared among strictly convex hexagons centred at the origin,
  which gives the same minimum); those of Definition 2.3.8 come from Mahler's construction, and
  Theorem 2.3.9 identifies them. Two notions of irreducibility appear: Definition 2.3.5's (every
  boundary point on a critical lattice) and Mahler's original one (no proper subdomain with the same
  `Δ`), used in the proof of Lemma 2.2.5.
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
  `Λ₂ = X` of every trajectory (E21).
- **Proposition 6.5.1.** "Hamilton's equations" are the hypotheses of [`proposition6_5_1`](SmoothedPolygons/Ch6/Hamiltonian.lean#L319): on
  `T*𝔰𝔩₂(ℝ)`, `X' = δH/δΛ₂` and `Λ₂' = -δH/δX`; on the cotangent bundle of the group, in canonical
  coordinates `(g, p)` of `T*GL₂(ℝ)` (the covector `p` acting by `v ↦ tr(p v)`), `g' = ∂H/∂p` and
  `p' = -∂H/∂g`, with `H` depending on `(g, p)` through the left-trivialized costate `Λ₁ = pg`. The
  Euler–Arnold equation that the book cites is then proved ([`External.euler_arnold`](External/EulerArnold.lean#L72)). The conclusion
  is the derivative of `Λ₁` and of `Λ_R` at `t`.
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
- **Balanced pairs exist.** The unit disk, with `σ_j(t) = Rot(t) s_j*` and `t_f = π/3`, is a
  balanced pair ([`circle_isBalancedPair`](SmoothedPolygons/Ch2/BalancedCircle.lean#L241)), so the hypotheses of the results of Chapter 3 about
  balanced pairs can be met.
- **Corrections of statements.** E13 (hypothesis, user-approved), E16 (misprint), E17 (`X ≠ 0`), E20
  (misprint), E21 (nontriviality on the reduced costate), E26 (`⟨X, Z_u⟩ ≠ 0`), and in proofs E14 and
  E24.

## 7. Departures from the paper's proofs

| Result | The paper's argument | The formalization's | Why it is necessary | E-item |
| --- | --- | --- | --- | --- |
| Lemma 2.2.1 (in its corrected form) | expand `K`, separate touching translates by lines, crop, repeat until the plane is tiled; at most six edges by Euler characteristic | a maximal centrally symmetric convex body `C ⊇ K` free of half-lattice points (Zorn; bounded by Blichfeldt) is cut out by at most three strips, whose unique support points pairwise form lattice bases ([`PlaneLattice.exists_halfLatticeFree_eq_strips`](Basic/Analysis/Convex/LatticePacking.lean#L998)) | the book's argument is aimed at the printed statement, which is false (E1): its termination ("the plane is tiled") and its edge count (Euler characteristic of a tiling) fail; the corrected statement needs another argument (approved by the user) | E1 |
| Lemma 2.2.5, no corners and critical edges | shave `K` near a boundary point lying on no edge of a critical hexagon; at endpoints of flat segments, "shave as above" | a worst disk is irreducible in Mahler's sense; every support line then contains a point of a critical lattice (a weak form of the "only if" half of Mahler 1947, Lemma 3: a critical-lattice point on each support line, not at each boundary point), where Mahler's Theorem 2 gives a unique support line and the edge of a least-area hexagon | the shaving argument cannot close the case of a segment endpoint on a critical edge off its midpoint (E4); the user chose Mahler's route | E4 |
| Lemma 2.4.2, one step | `σ₂` equals the integral curve `σ̃₂` with the same tangent direction and area relation | `σ₂` is differentiable because its chords lie between the tangent lines at their ends, so their directions converge, and the area relation fixes their lengths | the book does not show that `σ̃₂` stays on the boundary, which its identification needs (E8) | E8 |
| Lemma 2.4.6 | Shifrin's Proposition 3.8 (a simple closed regular curve is convex iff its curvature has one sign) | each tangent line supports `K`, so `f(t) = det(σ'(t₀), σ(t) − σ(t₀)) ≥ 0` with `f(t₀) = f'(t₀) = 0`, and the second-derivative test gives `det(σ', σ'') ≥ 0` | the cited proposition is about smooth curves; the curves here are only `C¹` with Lipschitz derivative (E11) | E11 |
| The area formula `eqn:cost` (§3.2) | Green's theorem, `area(K) = ½∮ x dy − y dx` | the polar-coordinates form of Green's formula for regions star-shaped about the origin, `area = ½∫ det(γ, γ')` ([`PlaneCurve.IsStarCurve.volume_radialHull`](Basic/Analysis/Convex/StarCurve.lean#L480), by the change of variables `(r, t) ↦ r γ(t)`) | Mathlib has no Green's theorem for regions bounded by `C¹` curves; only that step changes | – |
| Lemma 3.1.12 (Jacobi's formula) | verify the polynomial identity on the dense set of matrices with distinct nonzero eigenvalues, through a differentiable diagonalization `A = L⁻¹DL` | differentiate the Leibniz expansion of `det` and identify `Σᵢ det(A with column i replaced by A'ᵢ) = tr(adj(A) A')` through Cramer's rule | the step needs mathematics that Mathlib lacks (a differentiable eigen-decomposition and the density argument); the user approved the replacement | – |
| Lemma 4.3.1 | `area(K_min) < area(unit disk) = π` | `cost(K_min) ≤ cost(smoothed octagon) < π`, the octagon being admissible by Theorem 7.5.6 and its cost computed in the example of §7.5 | the paper's step has a gap that its own comparison cannot close: the unit disk is admissible, so it gives only `≤` (E19) | E19 |

Every other proof follows the book's argument. The gaps of Theorem 2.2.2 (E2), Theorem 2.3.9 (E7),
Lemmas 2.2.6, 2.2.7, 2.4.3 (E5, E9), Lemma 7.5.5 (E30) and Theorem 7.5.6 (E31) are filled along the
book's lines, and the index slip of Lemma 2.4.5 (E10) is corrected. In Lemma 2.4.3 the formal proof
bounds the turning of the tangent by the hyperbolic arc of Remark 2.2.4 itself rather than by the
osculating circle the book derives from it, and treats the curves `j ≠ 0` through `σ₁` rather than
the arclength reparametrization of `σ₂`, a symmetric choice.

The cited results that [`External/`](External) proves are proved by their sources' arguments, except:

| Cited result | The source's argument | The formalization's | Why |
| --- | --- | --- | --- |
| Mahler 1947, Theorem 2 (Theorem 2.3.7) | uses its own Lemma 5 (a convex hexagon `H` has `Δ(H) = V(H)/4` and a unique critical lattice, the midpoint lattice, justified by reference to the unique tiling by translates of `H` in another paper) and, in footnote 8, Lemma 5 of another paper (no arc between consecutive lattice points is a segment) | an exact formula for the area of the hexagon of tac-lines, `V(H) = (4 − p²/(D₀D₁D₂))Δ(K)`, gives the area and the bisection; the footnote is derived from Mahler's Theorem 1 | the uniqueness of the critical lattice of a hexagon rests on a uniqueness theory of lattice tilings that Lean lacks and that the source does not give; the exact formula avoids it |
| Mahler 1947, Lemma 3 | quoted from Lemmas 8 and 12 of another paper, which we did not have | a weak form of the "only if" half, proved by shaving along a support line: in an irreducible domain each support line contains a point of a critical lattice | the source gives no proof; only this form is used (Lemma 2.2.5) |
| Fejes Tóth's theorem (Theorem 2.1.3) | Fejes Tóth: Dowker's theorem and the cell decomposition of a finite packing, counted with Euler's formula | Dowker's theorem by an alternating merge of normal angles; the cell lemma by maximal cells (Böröczky 2003, Lemma 5), the convexity of their holes by a counting argument on sides instead of Böröczky's walk around boundary cycles, and the side count by angle sums instead of Euler's formula | Mathlib has neither Euler's formula for planar maps nor the Jordan curve theorem, on which the cycle and Euler arguments rest; Dowker's area formula for polygons is likewise missing, and the merge argument needs only measure additivity |

## 8. What each result depends on

The results from prior work that the proofs use are all proved in [`External/`](External) (Section 2):
Fejes Tóth's theorem (through Theorem 2.1.3, in Theorem 2.2.2 and the results after it), Gruber's
formula (Definition 2.1.2), the theorems of Minkowski and Mahler (Theorems 2.3.6, 2.3.7 and
everything that uses them, and Lemma 2.2.5), and the Euler–Arnold equation (Proposition 6.5.1).
Every
declaration depends only on [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound)
(`lake env lean scripts/Audit.lean`).

The route check (`python3 scripts/route_check.py check docs/paper_routes.tsv --accept
docs/route_differences.tsv`) compares, for each of the 58 formalized results that the book proves,
the numbered results that the Lean proof uses with those that the book's proof cites. It passes:
every difference is recorded in [`docs/route_differences.tsv`](docs/route_differences.tsv) with its reason. The 50 differences
are of these kinds:
- results the book uses without `\ref` ("by the previous lemma", "immediate from the previous
  proposition", an equation cited by number), and three basic facts used throughout (Lemma 7.1.1,
  Lemma A.6.4, Lemma 3.3.4);
- citations whose content the formal statements take as hypotheses or definitions: Lemma 2.4.3
  (about `K_min` only; Theorem 3.1.4(3) is false without its conclusion, E13), Lemma 2.4.5 (item 5
  of a balanced pair) and Lemma 5.0.4 (Chapter 5, out of scope);
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

- **Outside the chosen scope:** Chapter 1; Chapter 5 (compactification); Chapters 8–16, including
  the main theorem (Mahler's First conjecture, Theorem 16.3.1); Appendix A.1–A.5 and A.7–A.10;
  Appendix B.
- **Within the formalized chapters:**
  - Lemma 3.1.8 (hyperbolic arcs).
  - The "if" half of Mahler's Lemma 3 (cited after Definition 2.3.5), which no proof uses.
  - Theorem 6.1.1 (Filippov), cited, and its application in §6.1.
  - Definition 6.3.1 and Proposition 6.4.1 (Jurdjevic: Hamiltonians of left-invariant systems on a
    general Lie group), which the rest of the formalized chapters do not use.
  - Theorem 7.7.1 (the smoothed octagon is an isolated extremal), whose proof is a sketch (E32).
  - The remarks, among them Remark 7.5.2 (the determinant `d(y₀)` of `Λ₁` is monotone) and
    Remarks 7.6.1–7.6.4 on the smoothed `(6k - 2)`-gons.
  - The action of the dihedral group on the ideal vertices of `𝔥*` (§4.6): the formalization states
    the action on controls, star functions and `Φ`, but not on `ℝℙ¹`.

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

- This is, to our knowledge, the first formalization of Theorem 7.5.6 and of the Hamiltonian part
  of the book (Chapters 6–7: costates, switching functions, Pontryagin extremals). The state
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
- No formal proof of the Pontryagin maximum principle exists in any proof assistant (an attempt in
  Lean, [willcforte/pontryagin-lean](https://github.com/willcforte/pontryagin-lean), 13 May 2026,
  states its key steps as axioms). The formalization does not need one.
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
  conjecture (Theorem 16.3.1) is Chapters 5 and 8–16: the Pontryagin maximum principle (or at least
  the existence of an extremal lift of a minimizer), Filippov's existence theorem, the analysis of
  the singular locus and of chattering, and the numerical containments of the global basin theorem.
- **Theorem 7.7.1.** The isolation of the smoothed octagon among extremals needs a rigorous
  computation of the Jacobian of the Poincaré map at the octagon's fixed point (TeX 6612). Hales's
  2017 preprint (§4.5) claims the same isolation by another route, an interval-arithmetic expansion
  of the cost along the one-parameter family of deformations satisfying the endpoint conditions
  (Remark 7.7.2); neither computation is published in checkable form. The formalization gives the
  fixed point in closed form ([`costateΛR`](SmoothedPolygons/Ch7/StrongTransversality.lean#L111), [`strongL₁`](SmoothedPolygons/Ch7/StrongTransversality.lean#L64), [`strongLR`](SmoothedPolygons/Ch7/StrongTransversality.lean#L68)); the Jacobian also needs the
  general constant-control flow of §7.1 in every direction of the section, the implicit derivative
  of the switching time, and certified eigenvalue bounds.
- **The other smoothed `(6k+2)`-gons.** Hales's 2017 preprint (Remark 49) asks whether the
  smoothed `(6k+2)`-gons with `k ≥ 2` are local minima in the sense in which it shows the octagon to
  be one; neither the preprint nor the book answers it.
- **The smoothed `(6k−2)`-gons.** Remark 7.6.3 says they seem to satisfy every condition of an
  extremal except the sign of `λ_cost`, and the 2023–24 posters of Song and Sluis-Cremer
  (Section 10) state, without a published proof, that they are extremals of the area-maximization
  problem. The construction of §7.5 should adapt: control `e₂` from `z₀ = iy₀` with `y₀ > 1`,
  `t_sw = ln((3y₀² + 1)/4)/(√3y₀)`, boundary condition `z(z₀, t_sw) = R·z₀`, mode sequence
  eqn:3k+2, and the closing condition `4/(3y₀² + 1) = 2cos(πk/(3k − 1))`, which the book does not
  state (the 2017 preprint's `θ_k = πk/(3k − 2)` does not close). The new ingredient is the sign of
  the switching functions, in place of Lemma 7.5.3. Numerically, for `k = 2, 3`, the lift exists
  and has `λ_cost > 0`.

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
- **Lemma 3.1.8** (not formalized). The multi-point relations give `σ₀ = σ₁ + σ₋₁` and
  `det(σ₋₁, σ₁) = √3/2`. If `σ₁ = O + αv` and `σ₋₁ = O + βw` move on non-parallel lines and
  `O = pv + qw`, then `σ₀ - O = (α + p)v + (β + q)w` with `(α + p)(β + q) = √3/(2det(w, v)) + pq`
  constant: a hyperbola with center `O` and the two lines as asymptotes, without the envelope
  argument or the critical hexagons.
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
- **Mathlib** lacks `det exp(A) = exp(tr A)` for matrices (a TODO in
  `Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean`), Jacobi's formula, Green's theorem for
  Jordan domains, and the theory of regular elements of `𝔰𝔩₂`; each was a detour here.
- **Toward the main theorem.** Chapters 8–16 need the Pontryagin maximum principle (or at least the
  existence of an extremal lift of a minimizer), Filippov's theorem, the stable manifold theorem,
  Weierstrass preparation, and a rigorous version of the numerical containments of the global basin
  theorem (Theorem 16.1.1), which the book checks from Mathematica plots.
