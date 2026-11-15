# What each result depends on

Part of the [audit report](../../REPORT.md).

The results from prior work that the proofs use are all proved (Section 2), stated in [`External/`](../../External):
Fejes Tóth's theorem (through Theorem 2.1.3, in Theorem 2.2.2 and the results after it, among them
those of Chapter 5 and §6.1), Gruber's formula (Definition 2.1.2), the theorems of Minkowski and
Mahler (Theorems 2.3.6, 2.3.7 and everything that uses them, Chapter 5 through Theorem 2.3.9),
Mahler's Lemma 3 with the results of paper A and Mahler 1946 that prove it (Lemma 2.2.5, the remark
after Definition 2.3.5, and the identification of the minimizers with `K_min`), the Euler–Arnold
equation (Proposition 6.5.1 and the proof that minimizers are extremals), and the Pontryagin maximum
principle (that proof, and, through it and the maximum principle for the edge control problem,
Proposition 8.1.3, Theorem 8.2.7 and Theorem 16.3.1), which is proved in the OptimalControl package
with Brouwer's theorem from the FixedPoint package. The stable manifold theorem, proved in the
StableManifold package and stated as Theorem A.3.1 ([`theoremA_3_1`](../../SmoothedPolygons/AppA/StableManifold.lean#L186)), is used by Theorem 14.3.3 and
Remark 14.3.4 and, through them, by Theorem 16.4.1 and its time reversal and by Theorem 14.4.1,
whose first step puts the switching points of a trajectory from `q_out` on the local unstable curve
([`IsChatteringArcOutOf.eventually_mem_localUnstableSet`](../../SmoothedPolygons/Ch16/ClusterPoint.lean#L921), through Remark 14.3.4), and so by Mahler's
First conjecture; the import-all audit confirms it. Filippov's theorem is proved as Theorem 6.1.1,
which no other result uses; the existence of a minimizer (§6.1) uses its form with a state
constraint and Gronwall's inequality, both from the OptimalControl package, and Corollary A.1.3, in
Lemma 8.1.5 and Theorem 8.3.1, uses Gronwall's inequality too. The audit's row for Theorem 16.3.1
([`theorem16_3_1_unconditional`](../../SmoothedPolygons/Ch16/MahlerFirstArcRegion.lean#L94)) lists as results used [`External.euler_arnold`](../../External/EulerArnold.lean#L72),
[`External.fejes_toth`](../../External/FejesToth.lean#L882), [`External.gruber_corollary_30_1`](../../External/Gruber.lean#L320), [`External.mahler_1947`](../../External/Mahler1947.lean#L1700),
[`External.mahler_irreducible`](../../External/MahlerIrreducible/Lemma3.lean#L383), [`External.pontryagin_maximum_principle`](../../External/Pontryagin.lean#L80) and [`theoremA_3_1`](../../SmoothedPolygons/AppA/StableManifold.lean#L186), no
hypothesis, and as axioms [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound); the rows for
[`theorem14_4_1_unconditional`](../../SmoothedPolygons/Ch16/MahlerFirstArcRegion.lean#L51), [`theorem16_4_1_unconditional`](../../SmoothedPolygons/Ch16/BasinFacts.lean#L70) and N4 likewise list no hypothesis.
The conditional forms list their hypotheses among the results they use, for they are part of their
statements, not axioms: [`theorem16_3_1`](../../SmoothedPolygons/Ch16/MahlerFirst.lean#L349) lists [`SmoothedPolygons.NoChatteringIntoSingularLocus`](../../SmoothedPolygons/Ch16/MahlerFirst.lean#L110) (which
[`noChatteringIntoSingularLocus`](../../SmoothedPolygons/Ch16/MahlerFirstArcRegion.lean#L59) proves) and no other result uses that hypothesis, not even the
unconditional part of Theorem 16.3.1; [`theorem16_3_1_of_theorem14_4_1`](../../SmoothedPolygons/Ch16/NoChattering.lean#L387) lists the same results from
prior work and the three facts of Table 16.1, and not the stable manifold theorem, since the first
part of Theorem 16.4.1, which it uses, needs only the derivative of the extended map at `q_out`; and
[`theorem16_1_1`](../../SmoothedPolygons/Ch16/GlobalBasin.lean#L599), [`theorem16_2_1`](../../SmoothedPolygons/Ch16/OutwardFuller.lean#L567), [`theorem16_4_1`](../../SmoothedPolygons/Ch16/ClusterPoint.lean#L1021) and its time reversal list
[`TriFuller.DOutContracts`](../../SmoothedPolygons/Ch16/BasinHypotheses.lean#L236), [`TriFuller.CellTwoEntersDOut`](../../SmoothedPolygons/Ch16/BasinHypotheses.lean#L260) and [`TriFuller.BoxSubclaims`](../../SmoothedPolygons/Ch16/BasinHypotheses.lean#L278). The audit lists a
named proposition among the results that a theorem uses only when the theorem's statement assumes
it. The results of Chapters 13 and 15 and the four computed facts use no result from prior work;
Lemma 13.5.5 uses linearized stability for maps, and the continuity claims of Chapter 15 use the
continuity of a least positive root, both proved in [`Basic/`](../../Basic) (Section 2). Those of Chapter 14 use no
result from prior work except the stable manifold theorem, which Theorem 14.3.3, Remark 14.3.4 and
Theorem 14.4.1 use. Theorems 16.1.1 and 16.2.1 use no result from prior work either, and Theorem
16.4.1 only the stable manifold theorem. Every declaration depends only on [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext),
[`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound): `lake env lean scripts/Audit.lean`, which imports every module of
the library with `import all`, so that the proofs of module files are visible, reports "Checked
10734 declarations of the library: all use only the standard axioms", and checks the axioms of each
numbered result, through the packages it uses, and of the three Challenge theorems.

The route check (`python3 scripts/route_check.py check docs/paper_routes.tsv --accept
docs/route_differences.tsv`) compares, for each of the 140 results of the book found in the Lean
code, the numbered results that the Lean proof uses with those that the book's proof cites. It
passes: every difference is recorded in [`docs/route_differences.tsv`](../../docs/route_differences.tsv) with its reason ("185 route
differences, 185 of them recorded"). They are of these kinds (nine more, which the other route
explains, are shown by `--all`:
a result that the Lean proof uses directly where the book reaches it through a cited result, or
conversely):

- results the book uses without `\ref` ("by the previous lemma", "immediate from the previous
  proposition", an equation cited by number such as the transversality condition `eqn:theta-k` of
  Lemma 7.5.5 in Theorem 7.7.1, "the real number constructed in Section 7.5" for Remark 7.5.2's
  `y₀(d)`, Lemma 5.0.4 in Lemma 5.0.7, the compactness of `𝔥**` in §6.1, "We have seen that the
  global minimizer must be extremal" for §6.2 in Proposition 8.1.3, "The next lemma" for Lemma
  8.1.5 in Theorem 8.1.4, "By the lemma" for Lemma 8.2.2 in Theorem 8.2.3, "The previous theorem"
  for Theorem 8.2.6 in Theorem 8.2.7, "According to the theorem" for Theorem 8.3.1 in Theorem
  8.3.2, the sentence of Remark 8.3.3 and Lemma 2.2.5 ("no corners") in Theorem 16.3.1, "By the
  lemma" for Lemma 13.2.6 in Corollary 13.2.7) or
  implicitly (for instance the star domain of Theorem 4.4.1 as the state space, in Lemma 4.5.2,
  Chapter 5, §6.1, Theorems 7.5.6 and 7.7.1, (8.1.3) and Lemma 8.2.1, the half-plane coordinates of
  Lemmas 4.1.1 and 4.2.1 in §6.1, (8.1.3) in the cost identity of §8.1, Theorem 6.8.2 in Lemma
  8.2.1, the costate equations and the
  Hamiltonian of the edge problem in (8.1.8), Theorem 3.4.2 for the control of the deformed arc
  in Theorem 8.2.7, the existence and uniqueness of the first control (Lemma 13.2.6) in Lemma
  13.2.5 and wherever the Poincaré map is used, in Lemma 13.5.2, Remark 13.5.3 and Lemma 13.5.5,
  and the time reversal of Lemma 13.2.5 for `q_in = τ(q_out)` in Lemmas 13.5.2 and 13.5.5), and
  three basic facts used throughout (Lemma 7.1.1, Lemma A.6.4, Lemma 3.3.4); conversely, Lemma
  2.4.2 cites Lemma 2.4.5 only by "Compare the proof of Lemma 2.4.5" and does not use it;
- in Theorem 5.0.2, the cost of a trajectory as the area of its disk (the area formula of §3.2),
  and the smoothed octagon as a competitor ("Hence `K` is not a global minimizer"): its trajectory
  is admissible (Theorem 7.5.6, Lemma 7.5.5) and its area over `√12` is `δ_oct`, all of which the
  book takes for granted (§6.1 uses the octagon too, in the repair of its time bound, below);
- citations whose content the formal statements take as hypotheses or definitions: Lemma 2.4.3
  (about `K_min` only; Theorem 3.1.4(3) is false without its conclusion, E13), Lemma 2.4.5 (item 5
  of a balanced pair) and Proposition 3.6.1 (the left trivialization is part of the statement of
  Proposition 6.4.1);
- Lemma 6.1.2, which cites Lemma 5.0.4 for the positivity of the functions `ρ_j(z)`: the text
  before that lemma sets it up (`𝔥*` is defined by the star inequalities), and the formal proof
  reads it off the star domain;
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
  Lemma 5.0.3 (E42: Theorems 2.2.2 and 2.3.9), the existence of a minimizer in §6.1 (E46: the
  converse of Problem 3.6.2 for winding number one, E15, and the time bound by comparison with the
  smoothed octagon in place of Lemma 4.3.1), the added uniqueness step in Lemma 7.5.5 (E30), the
  principle of optimality in Proposition 8.1.3 (E48: (8.1.1), (8.1.3), the cost identity of §8.1
  and the star domain), in Theorem 16.3.1, the set of meeting times (E60: Theorem 8.2.3) and
  the passage from the control problem to `K_min` (E47), and in Lemma 13.2.5 the substitution of
  Lemma 13.2.3 redone for constant controls, since that lemma is about solutions with `H_F = 0`
  (E63);
- equations that the book displays inside a proof and the formalization states separately: (8.1.7)
  and (8.1.8) in the proof of Theorem 8.1.4, which also cites (8.1.6) by `\eqref`, which the route
  extraction does not read; the adjoint equation of the edge problem, written with the partial
  derivatives of the dynamics and the cost rather than of the Hamiltonian (8.1.6); and (13.3.1)
  and (13.3.2) in the proof of Lemma 13.3.2;
- the forced differences of the user's decisions and of Theorem 16.3.1: Theorem 8.2.7 in
  the authors' reading uses Proposition 8.1.3, (8.1.6)–(8.1.8) and Lemma 8.2.1 (E55); Theorem
  8.3.1 in its one-sided form does not use Theorem 8.1.4, which only its corollary needs (E56);
  Theorem 16.3.1 states its part away from the singular locus (Theorem 8.3.2 with Proposition
  8.1.3) separately (E60);
- Theorem 7.5.6 uses the explicit lift constructed for Theorem 7.5.1 rather than the statement of
  Theorem 7.5.1, Lemma 7.5.3 identifies its switching functions with that lift, and Lemma 7.5.5
  uses the trace computed in the proof of Theorem 7.5.1;
- the last sentence of the proof of Theorem 7.5.1 ("Lemma 7.5.3 supplements the proof") concerns
  the maximum property, which belongs to Theorem 7.5.6;
- in Chapters 15–16 (the block "Chapters 15–16" of the file), results the book uses without naming
  them: Lemma 13.2.6 for the first controls on the faces and 2-cells (Proposition 15.2.2) and in
  Theorems 16.1.1 and 16.2.1; Definition 15.1.2 (the cell coordinates are injective on the open
  first box) and Proposition 15.2.2 ("the representation of `Ξ_{𝒲,0}/V_T` as the union of two
  closed big cells", TeX 12519–12520) in Theorem 16.1.1; Remark 15.3.1 for "`q_in ∈ 𝒟_in`,
  `q_out ∈ 𝒟_out`" (TeX 12535–12537); Lemma 13.5.2 for the fixed points and `r_scale`; Lemma 13.2.5
  for the time reversals; and Theorem 16.1.1, "the Fuller basin theorem", in Theorem 16.2.1; and
  one forced difference: Lemma 15.1.1 takes (15.1.1) as its hypothesis, as printed ("For each
  `z ≠ 0` satisfying (15.1.1)"), so its proof does not use [`eqn15_1_1`](../../SmoothedPolygons/Ch15/CellCoordinates.lean#L912), which derives (15.1.1);
- in Chapter 14 and §16.3–16.4 (the block "Chapter 14 and section 16.4"), results the book uses
  without naming them: in Lemma 14.3.1, Lemma 14.2.3 ("The asymptotic formulas given above", and
  the divisibility of the switched state), the chart (14.1.1) and the uniqueness of the solution
  of (14.1.3), by which the image of a switching point is again a point of the chart (in the last
  step); Lemma 13.2.6,
  through the first control, wherever the Fuller–Poincaré map is used; Remark 14.2.1 for the fixed
  point `x̃_out`; in Theorem 14.3.3, Lemma 14.2.3 for `∂_r F₁ = r_scale` and Theorem A.3.1 ("By
  general theory"); in Theorem 16.3.1, Remark 6.6.1 for "Thus, the trajectory is not periodic"; and
  in Theorem 16.4.1, the chart and its linear system, the blow-up coordinates of Chapter 13 and its
  uniqueness of extremals (through (13.3.1) and (13.3.2)), Lemmas 14.2.3, 14.2.4 and 14.3.1, Theorem 14.3.3
  and Remark 14.3.4; and three forced differences: (14.1.3) is the definition of `Λ_R` in the
  chart, whose running claims come from its closed form; Theorem 14.3.3 is stated for every
  extension of Lemma 14.3.1, so it does not use the lemma; and it uses the eigenvalue bound behind
  Lemma 13.5.5, not the lemma's statement of stability;
- in the last two blocks of the file, on Theorem 14.4.1 and the analytic proofs and on N4, results
  that the proof of Theorem 14.4.1 uses without naming them: the
  second part of Theorem 16.4.1, time reversed, through the mirrored chart of Remark 14.3.4 ("All
  switches must be on the unstable curve"), the chart (14.1.1) and the uniqueness of the solution of
  (14.1.3), Lemma 8.3.4 ("must chatter"), and N4, read off Figure 14.2 ("because the unstable curve
  hits the boundary of the star domain"); Figure 14.2 again in Theorem 16.3.1, whose unconditional
  form discharges N4, and Table 16.1 in Theorem 16.2.1, whose unconditional form discharges the
  three facts. The routes of the proofs of the four facts themselves are not compared, since the
  book proves them by computation, and its Table 16.1 and Figure 14.2 have no proof to compare with
  (E77, E88).
