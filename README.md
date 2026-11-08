# Smoothed polygons in the Reinhardt control problem, in Lean

[![Lean Action CI](https://github.com/vltanh/lean4-smoothed-polygon/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/vltanh/lean4-smoothed-polygon/actions/workflows/lean_action_ci.yml)

A Lean 4 formalization of the smoothed-polygon core of Thomas Hales and Koundinya Vajjha,
*Packings of Smoothed Polygons* ([arXiv:2405.04331v1](https://arxiv.org/abs/2405.04331), 2024),
with its geometric foundations. The book reformulates the Reinhardt problem, which asks for the
centrally symmetric convex disk whose densest packing is least dense, as an optimal control problem
on `SL₂(ℝ)`, and studies its Pontryagin extremals. This project formalizes the historical results
on packings, critical lattices and the boundary of the minimizer (Chapter 2), the reformulation
(Chapters 3, 4, 6 and 7, with Appendix A.6 and A.11), and its main construction: **every smoothed
`(6k+2)`-gon, in particular Reinhardt's smoothed octagon, is a Pontryagin extremal of the
Reinhardt control problem with bang-bang control** (Theorem 7.5.6), **the smoothed octagon is a
centrally symmetric convex disk whose greatest packing density is
`(8 - √32 - ln 2)/(√8 - 1) ≈ 0.902414`**, and **the smoothed octagon is an isolated extremal**
(Theorem 7.7.1). A fourth round, the first layer of a plan for the book's remaining chapters,
proves that **every minimizer of the Reinhardt control problem lifts to a Pontryagin extremal**
(§6.2), through the Pontryagin maximum principle, which the separate package
[OptimalControl](https://github.com/vltanh/lean4-optimal-control) proves by Agrachev and
Sachkov's argument. A fifth round, the second layer, formalizes Chapter 5 (the compactification
of the star domain) and proves that **the Reinhardt control problem has a global minimizer, which
lifts to a Pontryagin extremal and bounds a centrally symmetric convex disk of least greatest
packing density** (§6.1, with the identification of the minimizers with Reinhardt's `K_min`,
which the book uses without proof). A sixth round, the third layer, formalizes Chapter 8 (the
edge control problem, singular subarcs, and finite bang-bang control away from the singular
locus). With it, the book's main theorem, Mahler's First conjecture (Theorem 16.3.1: the global
minimizer is bang-bang with finitely many switches, and every `K_min` is a finite-sided smoothed
polygon with hyperbolic arcs at its corners), is **proved only conditionally**, on one named
hypothesis, [`NoChatteringIntoSingularLocus`](SmoothedPolygons/Ch16/MahlerFirst.lean#L107), which stands for Theorems 16.4.1 and 14.4.1 of the
book's Chapters 13–16, not yet formalized. Mahler's First conjecture is therefore not proved
here.

## What is proved

- Every numbered result of the formalized chapters (2–8, with Appendix A.6 and A.11 and
  Corollary A.1.3), by the book's own arguments where they hold: among them Filippov's theorem
  (Theorem 6.1.1, cited),
  Proposition 6.4.1 on left-invariant systems, Theorem 5.0.2 (a balanced disk whose trajectory
  leaves the compact set `𝔥**` is worse than the smoothed octagon), Theorem 5.0.6, whose second
  case the book only sketches, and Theorem 7.7.1, whose proof the book only sketches; Remarks
  2.2.4, 6.6.1, 7.5.2 and 7.6.4, which the book states without proof; and three claims that the
  book uses in its later chapters: every minimizer of the Reinhardt problem is a Pontryagin
  extremal (§6.2), a global minimizer exists (§6.1), and the global minimizers are Reinhardt's
  `K_min` (stated without proof). In Chapter 8: the global minimizer is edge extremal
  (Proposition 8.1.3), extremals of the edge control problem are bang-bang with finitely many
  switches (Theorem 8.1.4), the singular subarcs on which the Hamiltonian does not depend on the
  control are circular arcs (Theorem 8.2.6), extremals that
  avoid the singular locus and are edge extremal are bang-bang with finitely many switches
  (Theorem 8.3.2) and bound smoothed polygons (Remark 8.3.3, stated without proof), and constant
  vertex control does not meet the singular locus (Lemma 8.3.4). What is left in these chapters
  (two conjectural remarks, and the printed Theorem 8.2.7 for abnormal lifts, which is open) is
  listed in [REPORT.md, Section 9](REPORT.md#9-not-formalized).
- **Conditional:** Theorem 16.3.1 (Mahler's First conjecture) is proved under the hypothesis
  [`NoChatteringIntoSingularLocus`](SmoothedPolygons/Ch16/MahlerFirst.lean#L107)
  ([`theorem16_3_1`](SmoothedPolygons/Ch16/MahlerFirst.lean#L343)): for every Pontryagin extremal of the Reinhardt problem, with its boundary
  conditions, that is edge extremal, the switching times of the control do not accumulate from the
  left at a time where its lift meets the singular locus, while it is bang-bang off the singular
  locus before that time. This is the consequence of Theorems 16.4.1 (cluster point) and 14.4.1
  (no return) that the last step of the book's proof uses. The hypothesis is not an axiom: it is
  a proposition in the statement of [`theorem16_3_1`](SmoothedPolygons/Ch16/MahlerFirst.lean#L343), which no other result assumes; the audit
  lists it among the results that [`theorem16_3_1`](SmoothedPolygons/Ch16/MahlerFirst.lean#L343) uses, and its axioms are the standard three.
  Without it, the formalization proves that the global minimizer is bang-bang with finitely many
  switches on every interval on which its lift avoids the singular locus
  ([`isFiniteBangBang_of_isReinhardtMinimizer_of_not_mem_singularLocus`](SmoothedPolygons/Ch16/MahlerFirst.lean#L165)). Later layers of the plan
  are to prove the hypothesis from Chapters 13–16 ([REPORT.md, Section 2](REPORT.md#assumed), E60).
- Lemma 2.2.1 is false as printed; it is refuted in Lean and proved in corrected form (E1).
  Theorem 7.7.1 is false read literally and holds up to time translation, for terminal times near
  `t_f` (E32); Lemma 3.1.8 and the existence of optimal controls in Filippov's theorem each lack
  a hypothesis (E34, E35). Theorem 8.3.1 is false as printed (at a time where `Λ_R` vanishes
  every control maximizes the Hamiltonian) and is proved in a one-sided form, from which the form
  that Theorem 8.3.2 quotes follows (E56). The user approved the five corrected statements, and
  chose the authors' reading of Theorem 8.2.7, whose proof covers only part of its statement:
  "singular" refers to the edge control problem on intervals where the control lies in an edge;
  the printed statement is proved for normal lifts and is open for abnormal ones (E55). The
  converse of the
  control problem that §6.1 uses, that an admissible trajectory bounds a balanced disk whose area
  is its cost, is false (the unit circle traversed seven times is admissible) and is proved for
  trajectories that wind once around the origin, as every trajectory cheaper than `7π/2` does
  (E15).
- No cited theorem is assumed; the one assumption of the formalization is the hypothesis of
  Theorem 16.3.1 above, which stands for results of the book itself. The cited results that the
  proofs use are proved in [`External/`](External): Fejes Tóth's theorem that lattice packings are densest for
  centrally symmetric disks, Gruber's lattice density formula, the theorems of Minkowski and Mahler
  on critical lattices and circumscribed hexagons, Mahler's characterization of irreducible domains
  (his Lemma 3, stated without proof, proved along the two earlier papers of Mahler on which it
  rests), the Euler–Arnold equation and the Pontryagin maximum principle; Filippov's
  theorem is proved there too ([External/README.md](External/README.md)). The maximum principle and Filippov's theorem are
  proved in the OptimalControl package, required at a pinned commit, which takes Brouwer's
  fixed-point theorem from the [FixedPoint](https://github.com/vltanh/lean4-fixed-point) package;
  the existence of a minimizer applies the package's form of Filippov's theorem with a closed
  state constraint, a compact set of initial points and a closed endpoint relation.
  A *Pontryagin extremal* is defined by the conditions of the maximum principle
  ([`IsPontryaginExtremal`](Challenge.lean#L171)); Theorem 7.5.6 shows that the smoothed polygons satisfy them, and the maximum
  principle shows that every minimizer does.
- `lake build` succeeds; the only `sorry`s are the statements of [`Challenge.lean`](Challenge.lean). There is no
  `axiom`. `lake env lean scripts/Audit.lean` checks that every declaration of the library and the
  Challenge theorems depend only on [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound).

## Main results

- [`SmoothedPolygonsChallenge.smoothed_polygon_extremal`](Challenge.lean#L335) (Theorem 7.5.6): for every `k ≥ 1`, the
  state trajectory with the control `e₃, e₁, e₂, e₃, …` on `3k+1` switching intervals of length
  `t_sw`, starting from `g(0) = I₂` and `X(0) = Φ(i y₀)` with `4/(3y₀² + 1) = 2 cos(πk/(3k+1))`,
  exists, is unique on `[0, t_f]`, has bang-bang control, and lifts to a Pontryagin extremal, with
  the nontriviality condition of the maximum principle imposed on the reduced costate
  `(λ_cost, Λ₁, Λ_R)` (on the book's full costate it would hold for every trajectory, E21).
- [`SmoothedPolygonsChallenge.smoothed_octagon_density`](Challenge.lean#L351) (the example before Theorem 7.5.6): for
  `k = 1`, `y₀ = √((√8 - 1)/3)` and `t_sw = ln 2/(2√(√8 - 1))`; the cost of the smoothed octagon's
  trajectory is `√12 (8 - √32 - ln 2)/(√8 - 1) ≈ 3.126 < π`; the trajectory bounds a balanced disk
  `K` in circle representation whose area is that cost; and the greatest packing density of `K`
  (Definition 2.1.1: the supremum of the densities of packings of congruent copies, measured in
  Euclidean disks) is `(8 - √32 - ln 2)/(√8 - 1)`. The book takes this density from a normalization
  it never checks for the octagon (E12); the formalization proves it for every balanced disk.

The library also proves Theorem 7.7.1 ([`theorem7_7_1`](SmoothedPolygons/Ch7/Isolated.lean#L508)), which is not part of the Challenge: there
are a neighbourhood `U` of the octagon's initial condition `(X(0), Λ₁(0), Λ_R(0), λ_cost = -1)`
and `ε > 0` such that every Pontryagin extremal with terminal time `|T - t_f| < ε` whose initial
condition lies in `U` after rescaling its costate by a positive factor is the octagon's lifted
trajectory started at some time `s`, with a proportional costate; in particular `T = t_f`.
Without the time shift and the bound on `T` the statement is false (E32); the octagon's own lift
meets the hypotheses ([`theorem7_7_1_octagon`](SmoothedPolygons/Ch7/Isolated.lean#L633)).

It also proves that every global minimizer of the Reinhardt control problem (Problem 3.6.2) lifts
to a Pontryagin extremal ([`exists_isPontryaginExtremal_of_isReinhardtMinimizer`](SmoothedPolygons/Ch6/MatrixExtremal.lean#L564)), the claim of §6.2
and §6.6 that the book uses in Chapter 8 ("We have seen that the global minimizer must be
extremal"). The proof follows the book: the maximum principle
([`External.pontryagin_maximum_principle`](External/Pontryagin.lean#L80)) on the open set `GL₂⁺(ℝ) × C` of `Mat₂(ℝ) × 𝔰𝔩₂(ℝ)`, `C`
the cone of the star inequalities; the costate equations through Proposition 6.5.1 (with the
Euler–Arnold equation) and Corollary 6.5.3; the transversality conditions of §6.6. One departure:
the boundary conditions are written without two equations that the first integrals `det g` and
`det X` make redundant, for with them the principle is satisfied by every trajectory with a
covector whose reduced costate vanishes (E21). Remark 6.6.1 is proved too ([`remark6_6_1`](SmoothedPolygons/Ch6/PeriodicExtension.lean#L352)): every extremal extends to a periodic
solution with discrete rotational symmetry, `X(3t_f) = X(0)` and `g(6t_f) = I₂` (E38).

The second layer proves that the Reinhardt control problem has a global minimizer, that it lifts
to a Pontryagin extremal, and that the balanced disk it bounds is a `K_min`, a centrally symmetric
convex disk of least greatest packing density `δ_min = cost/√12`
([`exists_isReinhardtMinimizer_isPontryaginExtremal_isWorstDisk`](SmoothedPolygons/Ch6/WorstDisk.lean#L250)); conversely, every `K_min`, after a
linear map, is the disk of a global minimizer ([`exists_isReinhardtMinimizer_of_isWorstDisk`](SmoothedPolygons/Ch6/WorstDisk.lean#L183)). The existence follows
§6.1 ([`exists_isReinhardtMinimizer`](SmoothedPolygons/Ch6/Existence.lean#L436)): Theorem 5.0.2 ([`theorem5_0_2`](SmoothedPolygons/Ch5/Theorem502.lean#L253)) confines the competitors that matter to the
compact set `𝔥**`, and Filippov's theorem gives a minimizer. The book's argument has gaps,
repaired along its lines (E46): Theorem 5.0.2 is about balanced disks, and the converse of the
control problem that applying it to trajectories needs holds only for trajectories that wind once
(E15; higher winding costs at least `7π/2`, by a bound not in the book); the book's cut-off of the
vector fields changes the problem, and Filippov's theorem as stated fixes the initial point, so the
formalization uses its form with a closed state constraint, a compact set of initial points and a
closed endpoint relation, from the OptimalControl package; and the terminal time is bounded by
`cost ≥ 3t_f` rather than by Lemma 4.3.1, which assumes a minimizer. The identification with
`K_min`, which the book uses without proof in Chapters 8 and 16, is E47.

The third layer formalizes Chapter 8. Every global minimizer is edge extremal
([`proposition8_1_3`](SmoothedPolygons/Ch8/EdgeExtremal.lean#L850): its arcs with the control in an edge of `U_T` are extremals of the edge
control problem; the principle of optimality, which the book invokes in one sentence, is made
precise by splicing in competitors close to the arc, E48); it has no singular subarc in the
authors' reading of Theorem 8.2.7 ([`theorem8_2_7`](SmoothedPolygons/Ch8/NoSingularArcs.lean#L375), E55), with the book's second variation of
the circle ([`exists_lt_reinhardtCost_of_circleArc`](SmoothedPolygons/Ch8/CircleVariation.lean#L1209)); and it is bang-bang with
finitely many switches on every interval on which its lift avoids the singular locus
(Theorem 8.3.2, [`theorem8_3_2`](SmoothedPolygons/Ch8/FiniteBangBang.lean#L1419)). Theorem 16.3.1 follows from these, Lemma 8.3.4 and Remark 8.3.3
under the hypothesis [`NoChatteringIntoSingularLocus`](SmoothedPolygons/Ch16/MahlerFirst.lean#L107) ([`theorem16_3_1`](SmoothedPolygons/Ch16/MahlerFirst.lean#L343)); the book's proof does not
handle the set of times at which the lift meets the singular locus, which the formal proof does
(E60). **Theorem 16.3.1 is conditional: Mahler's First conjecture is not proved until the
hypothesis is.**

The Reinhardt conjecture itself (that the smoothed octagon is the least dense) remains open, and
is not claimed here.

## Palomar

[`Challenge.lean`](Challenge.lean) states the two results of the list above with `sorry`; [`Solution.lean`](Solution.lean) restates them word for
word and proves them from the library. [`comparator.json`](comparator.json) configures Palomar's Comparator:

```sh
lake env lake comparator --config=comparator.json   # needs bubblewrap; expect "Your solution is okay!"
```

The definitions that the Challenge uses are kept in [`SmoothedPolygons/Defs.lean`](SmoothedPolygons/Defs.lean) between two
markers and copied into the Challenge by `python3 scripts/sync_challenge_defs.py` (CI checks the
copy with `--check`). [`formalization.yaml`](formalization.yaml) holds Palomar's metadata, and the workflow
[`palomar_preflight.yml`](.github/workflows/palomar_preflight.yml) runs Palomar's mechanical verification on demand.

## Audit summary

From [REPORT.md](REPORT.md), whose E-numbers are used here.

- **Errors:** Lemma 2.2.1 (Reinhardt's tiling lemma) is false as printed: a lattice packing need
  not be a tiling by a hexagon containing the disk (E1; counterexample `L = ℤ²`,
  `K = {|2y₀ + y₁| ≤ 1, |2y₁ - y₀| ≤ 1}`, refuted in Lean). The book only needs its classical
  packing form, which is proved, so nothing after it breaks. The terminal condition
  `X(t_f) = R X₀ R⁻¹` of the control problem should be `R⁻¹ X₀ R` (E16); the coefficient `a(u)` of
  the half-plane control problem has the wrong sign (E20). The nontriviality condition of a
  Pontryagin extremal, imposed on the full costate `(Λ₁, Λ₂)`, lets every admissible trajectory lift
  to an extremal; it must be imposed on the reduced costate `(Λ₁, Λ_R)`, and the maximum principle
  gives it for a minimizer only when the boundary conditions are written without the equations
  that first integrals make redundant (E21). Theorem 7.7.1 (the
  smoothed octagon is an isolated extremal) is false read literally: the octagon's lift started at
  another time, or run for several laps, is another such extremal (E32). The converse of the
  control problem that §6.1 uses (an admissible trajectory bounds a balanced disk whose area is its
  cost) is false: the unit circle traversed seven times is admissible (E15). The set that §4.6
  gives as a fundamental domain of the dihedral group is the union of two sectors, and the proof of
  Theorem 5.0.2 prints a curve in its place (E40, E45). Theorem 8.3.1 (the maximizers of the
  Hamiltonian lie in one edge of the control set near a time off the singular locus) is false as
  printed: at a time where `Λ_R` vanishes every control maximizes, and the maximizers may lie in
  different edges before and after it (E56). The restatement of Theorem 8.3.2 in Chapter 1 drops
  edge extremality and is false for extremals on an interval (E57); the abnormal costates of
  Remark 8.1.6 have the wrong sign (E51). Slips that do not affect any result: E6
  (the definition of a critical lattice omits admissibility), E7, E8, E10, E14, E22, E24, E44,
  E45, E50, E54, E59.
- **Gaps:** the proof that the minimizer has no corners (Lemma 2.2.5) has a gap its argument cannot
  close; it is closed here by Mahler's lattice route (E4). The octagon's density value rests on a
  fact the book never proves, that balanced disks have least circumscribed hexagon of area `√12`;
  it is true and proved here (E12). The inequality behind the maximum principle for the smoothed
  polygons is left "as a tedious but elementary exercise"; it is true, tight at one corner, and
  proved here (E29). Lemma 2.4.6 applies a theorem about smooth curves to curves that are only
  `C¹,¹` (E11). Lemma 4.3.1 does not justify that the minimizer has area `< π` (E19). The proof of
  Theorem 7.7.1 is a sketch: the switching structure of nearby extremals is not argued, the "direct
  calculation" of hyperbolicity is not given, and the uniformity in the parameter `d` that its
  conclusion needs is missing; all are supplied here (E32). Remarks 7.5.2 and 7.6.4 are stated
  without proof, the second read off a figure; both are proved (E36, E37), and so is Remark 6.6.1,
  the periodic extension of an extremal, also stated without proof (E38). Chapter 5 asserts that
  `𝔥**` is compact (E41), does not argue the second claim of Lemma 5.0.3 (E42) or the claim of
  Theorem 5.0.6's first case, and only sketches its second case (E43); steps of Lemma 5.0.7 and of
  the proof of Theorem 5.0.2 are missing, among them a one-variable bound read off a graph (E44,
  E45). The argument of §6.1 for the existence of a minimizer applies Theorem 5.0.2 to trajectories
  that need not bound balanced disks, cuts off the vector fields (which changes the minimizers),
  uses Filippov's theorem with a fixed initial point while the endpoints are coupled, and bounds the
  terminal time by a lemma that assumes a minimizer (E46). The book identifies the minimizers of
  the control problem with Reinhardt's `K_min` without proof (E47), and takes for granted a
  reparameterization in §3.5 (E39). In Chapter 8, the proof of Theorem 8.2.7 (the global minimizer
  has no singular subarcs) covers only the subarcs on which the Hamiltonian does not depend on the
  control; following the authors' comments, the formalization proves the theorem with the edge
  case left to the edge control problem, and the printed statement for normal lifts, while for
  abnormal lifts it is open (E55). Proposition 8.1.3 invokes the principle of optimality without a
  construction (E48); claim (b) of Theorem 8.3.1 is a sketch (E56); Remark 8.3.3 has no proof, and
  the disk it speaks of exists only for trajectories of winding number one (E58); the proof of
  Theorem 16.3.1 does not handle the set of times at which the lift meets the singular locus
  (E60). All are filled here except the abnormal case of E55, as are the further gaps E2, E3, E5,
  E8, E9, E18, E23, E30, E31, E34, E49, E52, E53 and E61.
- **Missing hypotheses:** Theorem 3.1.4(3) is false for a general convex disk and holds under the
  standing assumptions of §2.4 (E13, formalized with the hypothesis `σ_j'` Lipschitz, approved by
  the user); Lemma 3.1.8 (hyperbolic arcs) is false unless the curves are regular, as §2.4 assumes
  (E34, approved by the user); Filippov's theorem (Theorem 6.1.1, cited without a source) asserts
  that an optimal control exists when the velocity sets are convex, which fails for costs that
  depend on the control and holds when the velocity sets extended by the cost are convex (E35,
  approved by the user); Lemma 4.2.3 needs `X ≠ 0` (E17); Lemma 7.3.1 needs `⟨X, Z_u⟩ ≠ 0` on the
  control set (E26), and so does Lemma 8.2.1 (E52); the converse of the control problem that §6.1
  uses needs winding number one (E15); the restatement of Theorem 8.3.2 in Chapter 1 needs edge
  extremality (E57).
- **Redundant hypotheses:** nine results of the book and one cited result hold without some of
  their hypotheses, which the Lean statements omit
  ([Section 5](REPORT.md#5-redundant-hypotheses)); for instance Lemma 7.3.1 holds for every compact
  convex control set on which `⟨X, Z_u⟩ ≠ 0`, and Theorem 5.0.2 for balanced disks not in circle
  representation. The Challenge keeps the book's hypotheses. Some statements keep a hypothesis of
  the book that their proofs do not use, among them the edge extremality of Theorem 8.3.1.
- **Use of cited results:** all correct, except Shifrin's characterization of convex curves, which
  Lemma 2.4.6 applies outside its hypotheses (E11); Filippov's theorem is stated without a source
  and with an existence claim that is false in general, though not for the Reinhardt problem,
  whose cost depends only on the state (E35), and §6.1 applies it to a problem it does not cover,
  which its form with a closed state constraint does (E46); §6.1 recalls Reinhardt's existence
  theorem, which concerns `K_min`, not the control problem (E47); the book's summary of the
  maximum principle omits one regularity hypothesis of its source, which the Reinhardt problem
  satisfies
  ([Section 2](REPORT.md#2-results-from-prior-work-and-how-the-paper-uses-them)); Corollary A.1.3,
  the book's form of Gronwall's inequality, is stated for `t ≥ 0` and applied on both sides of `0`
  (E61). The source of the
  maximum principle, Agrachev and Sachkov's book, has three gaps in its proof, all repaired: the
  proof of its Lemma 12.1 on a convex cone uses interior points, which a cone may lack; a needle
  variation may be placed at the final time, where it varies nothing; and that the end-point map of
  the needle variations is Lipschitz and differentiable is stated without proof
  ([Section 7](REPORT.md#7-departures-from-the-papers-proofs)).
- **Proofs:** every proof follows the book's argument, except the departures of
  [Section 7](REPORT.md#7-departures-from-the-papers-proofs), each forced by an error or gap of the
  book or by mathematics Mathlib lacks, or, for the last step of Theorem 16.3.1, by the chapters not
  yet formalized: Lemma 2.2.1 (its printed form is false), Lemma 2.2.5 (by
  Mahler's lattice route, chosen by the user), one step each of Lemmas 2.4.2 and 2.4.6, the area
  formula of §3.2 (polar coordinates for Green's theorem), Jacobi's formula (approved by the
  user), Lemma 4.3.1, Theorem 5.0.6 (its first case's claim, by a support line, and its second
  case, corner by corner), Lemma 5.0.7 (3), the existence of a minimizer in §6.1 (Filippov's
  theorem under a closed state constraint instead of the book's cut-off, and a time bound that
  does not assume a minimizer), the boundary conditions to which §6.2 applies the maximum principle
  (E21), one step of Theorem 7.7.1 (the inverse function theorem applied once at
  the octagon's fixed point, which gives the uniformity the book's per-`d` argument lacks),
  Proposition 8.1.3 (competitors spliced in only near the edge arc, E48), two steps of Theorem
  8.1.4 (E49), Theorem 8.2.7 (the authors' reading, E55), Theorem 8.3.1 (its passage to the control
  moved to a corollary, E56), and Theorem 16.3.1 (its last step replaced by the named hypothesis,
  and the set of meeting times handled, E60). The
  cited results are proved by their sources' arguments, with the exceptions listed there (notably
  Fejes Tóth's theorem, through Böröczky's cell lemma, with angle sums in place of Euler's
  formula); Mahler's Lemma 3 follows his two earlier papers on which it rests, whose errors and
  gaps are repaired; the maximum principle follows Agrachev and Sachkov's proof, in coordinates and
  with the departures listed there; Filippov's theorem is proved by the standard argument, without
  comparison with its source.

## Credits

- Written by Claude (Opus 5.5, model `claude-opus-5-5`) in Claude Code, with parallel sub-agents,
  at the request of The-Anh Vu-Le, who chose the scope and approved the corrections, following the
  [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) skill.
- The statements and the proofs were checked against the book's TeX source by independent agents;
  no person has reviewed the proofs.
- Made on 5–7 November 2026 in six rounds (the control-theoretic chapters; then Chapter 2, its
  cited theorems and the octagon's packing density; then the rest of these chapters: Lemma 3.1.8,
  Filippov's theorem, Mahler's Lemma 3 in full, Proposition 6.4.1, Theorem 7.7.1 and the
  remarks; then the first layer of a plan for Chapters 5 and 8–16: the maximum principle, with
  Brouwer's fixed-point theorem, in two separate packages, the lift of every minimizer to a
  Pontryagin extremal, and Remark 6.6.1; then the second layer: Chapter 5, the existence of a
  minimizer (§6.1) with Filippov's theorem under a state constraint, the converse of Problem 3.6.2
  for winding number one, and the identification of the minimizers with `K_min`; then the third
  layer: Chapter 8, Corollary A.1.3, and Theorem 16.3.1 conditional on one named hypothesis).
  [CREDITS.md](CREDITS.md) has the procedure and the figures.

## Related work

- The reformulation as a control problem, the claim that the smoothed `(6k+2)`-gons are
  Pontryagin extremals, and a sketched proof that the smoothed octagon is an isolated extremal go
  back to Hales's 2017 preprint ([arXiv:1703.01352](https://arxiv.org/abs/1703.01352)); the book is
  still an unrefereed preprint, with one version and no erratum.
- An independent, unreviewed Lean development by M. Ho
  ([sunfishho/reinhardt-density-bound](https://github.com/sunfishho/reinhardt-density-bound),
  2 November 2026) claims the lower bound `0.8950112` for the least packing density, above
  Tammela's `0.892656`, and formalizes parts of the book's Chapters 2, 3 and 5, among them the
  state dynamics and the area–cost identity of §3.2; it has no Hamiltonian or costate and does not
  formalize Theorem 7.5.6. This work did not use it.
- We found no earlier formal proof of Fejes Tóth's packing theorem, Dowker's theorem, or Mahler's
  theorems on critical lattices and circumscribed hexagons, which this project proves on the way.
- The Pontryagin maximum principle is proved in the package
  [OptimalControl](https://github.com/vltanh/lean4-optimal-control), which this project requires;
  to our knowledge this is its first complete formal proof (an earlier Lean attempt,
  [willcforte/pontryagin-lean](https://github.com/willcforte/pontryagin-lean), states its key
  steps as axioms). Brouwer's fixed-point theorem, which the proof needs, is proved in the package
  [FixedPoint](https://github.com/vltanh/lean4-fixed-point) by Milnor and Rogers' analytic
  argument.
- More in [REPORT.md, Section 10](REPORT.md#10-the-paper-in-the-literature).

## What's next

The main theorem, Mahler's First conjecture, needs Chapters 8–16, which a plan divides into
layers. The first three are done: the maximum principle and the extremal lift of every minimizer;
Chapter 5, the existence of a minimizer by the book's route, and its identification with `K_min`;
and Chapter 8, with Theorem 16.3.1 proved conditionally on the hypothesis
[`NoChatteringIntoSingularLocus`](SmoothedPolygons/Ch16/MahlerFirst.lean#L107). The later layers are planned to discharge it: the triangular
Fuller system of Chapter 13; its global basin (Chapter 15 and Theorem 16.1.1), with certified
numerics; the analytic extension of Chapter 14 and the cluster point theorem 16.4.1; and the
no-return theorem 14.4.1, whose proof rests on a numerical computation of an unstable curve. The
printed Theorem 8.2.7 for abnormal lifts is open, and Theorem 16.3.1 does not need it.
Beyond Theorem 7.7.1, Hales's 2017 preprint claims that the smoothed octagon is a strict local
minimum in a micro-local sense, by an interval-arithmetic computation not published in checkable
form; the smoothed `(6k−2)`-gons, claimed to be extremals of the maximization problem in 2023–24
posters, need a new sign inequality. See [REPORT.md, Section 11](REPORT.md#11-whats-next).

## Building

```sh
lake exe cache get     # Mathlib's compiled files
lake build             # the library, the Challenge and the Solution
lake env lean scripts/Audit.lean                                            # axioms and routes
python3 scripts/route_check.py check docs/paper_routes.tsv --accept docs/route_differences.tsv
python3 scripts/sync_challenge_defs.py --check                              # the Challenge's definitions
python3 scripts/linkify_docs.py                                             # links from the documents to the code
```

Lean `v4.36.0-rc2`, Mathlib `v4.36.0-rc2`. Besides Mathlib, the project requires
[OptimalControl](https://github.com/vltanh/lean4-optimal-control) (control systems, Filippov's
theorem, also under a state constraint, measurable selection, the maximum principle) at the commit
pinned in [`lakefile.toml`](lakefile.toml), which requires [FixedPoint](https://github.com/vltanh/lean4-fixed-point) (Brouwer's
fixed-point theorem); `lake` fetches both.

## Layout

| Path | Content |
| --- | --- |
| [`Basic/`](Basic) | general mathematics, for Mathlib: matrix calculus and ODEs, generalized circles under `SL₂(ℝ)`, areas and convexity of star-shaped regions, Dowker's theorem, hexagon lattice tilings, polygon angles, Fejes Tóth's cell lemma, the Tietze–Nakajima theorem, critical lattices, lattice-packed bodies, the inverse of an arclength function, the fundamental theorem of calculus for absolutely continuous functions in integral form ([Basic/README.md](Basic/README.md)); control systems, Filippov's compactness theorem (also under a state constraint), measurable selection and the maximum principle are in the [OptimalControl](https://github.com/vltanh/lean4-optimal-control) package |
| [`External/`](External) | cited results, proved: Fejes Tóth, Gruber, Minkowski–Mahler, Mahler 1947 (Theorem 2; Lemma 3, with the lemmas of Mahler's *On irreducible convex domains* and Theorems B–E of Mahler 1946 that prove it), Euler–Arnold, Filippov and the Pontryagin maximum principle (the last two from the OptimalControl package) ([External/README.md](External/README.md)) |
| [`SmoothedPolygons/Defs.lean`](SmoothedPolygons/Defs.lean) | the definitions that the Challenge uses |
| [`SmoothedPolygons/Ch2/`](SmoothedPolygons/Ch2) | Chapter 2: packing densities and Fejes Tóth's theorem (§2.1), Reinhardt's lemmas and the minimizer (§2.2), critical lattices and hexagons (§2.3), the boundary of the minimizer and balanced disks (§2.4), the density of balanced disks, the refutation of the printed Lemma 2.2.1 |
| [`SmoothedPolygons/Ch3/`](SmoothedPolygons/Ch3) | the control problem: state dynamics, hyperbolic arcs (Lemma 3.1.8), Jacobi's formula, cost and the area formula of §3.2, controls, Lie algebra dynamics, Proposition 3.6.1, Problem 3.6.2 |
| [`SmoothedPolygons/Ch4/`](SmoothedPolygons/Ch4) | the adjoint orbit and the upper half-plane, the star domain, the half-plane control problem, Lemma 4.3.1 and the bound `cost ≥ 3t_f` for every trajectory, the dihedral group on the ideal vertices (§4.6) |
| [`SmoothedPolygons/Ch5/`](SmoothedPolygons/Ch5) | Chapter 5: the compactification `𝔥**`, its compactness and dihedral invariance, and the fundamental domain (Definition 5.0.1, Compactification); the hexagon of a point of `𝔥*` and Lemmas 5.0.3–5.0.5 (Hexagon); Theorem 5.0.6 (AreaBound); Lemma 5.0.7 (Monotonicity); the bound near the edge (EdgeBound); the re-centered disk (Recenter); Theorem 5.0.2 (Theorem502) |
| [`SmoothedPolygons/Ch6/`](SmoothedPolygons/Ch6) | left-invariant control systems on Lie groups (Definition 6.3.1, Proposition 6.4.1), the Hamiltonian, the costate equations, the half-plane Hamiltonian; the Reinhardt problem as a control system on `GL₂⁺(ℝ) × C` (MatrixSystem, MatrixMinimizer, MatrixCostate, MatrixExtremal: the system, its minimizers, the costates of the maximum principle, and the theorem that every minimizer is a Pontryagin extremal); the periodic extension of an extremal (Remark 6.6.1, PeriodicExtension); the winding number of an admissible trajectory and the bound on the cost of higher winding (Winding); the converse of Problem 3.6.2 for winding number one (AdmissibleDisk); the existence of a global minimizer (§6.1, Existence); `K_min` and the minimizers of the control problem (WorstDisk, with WdBoundaryParam and WdTrajectory: the boundary multi-curve and trajectory of a `K_min`) |
| [`SmoothedPolygons/Ch7/`](SmoothedPolygons/Ch7) | constant control, faces, the spline, Theorem 7.5.1, Lemma 7.5.3 and its inequality, Lemma 7.5.5, Theorem 7.5.6, the smoothed polygons as balanced disks, Remarks 7.5.2 and 7.6.4, Theorem 7.7.1 (`Isolated.lean` and `Isolated/`) |
| [`SmoothedPolygons/Ch8/`](SmoothedPolygons/Ch8) | Chapter 8: extremals on an interval, the edge control problem, edge extremality, the maximizing faces, the singular locus and finite bang-bang controls (Defs); the edge problem and the Reinhardt problem, (8.1.1)–(8.1.7) (EdgeProblem); Proposition 8.1.3 (EdgeExtremal); Theorem 8.1.4 and (8.1.8) (EdgeBangBang); Lemma 8.1.5 (EdgeLandau); Remark 8.1.6 (EdgeAbnormal); Lemmas 8.2.1–8.2.2 and Theorems 8.2.3 and 8.2.6 (SingularLocus); the second variation of the circle (CircleVariation); Theorem 8.2.7 (NoSingularArcs), with the Reinhardt costate pulled back to an edge (EdgePullback); Theorems 8.3.1 and 8.3.2 (FiniteBangBang); Remark 8.3.3 and smoothed polygons (PolygonBoundary); Lemma 8.3.4 (VertexControl) |
| [`SmoothedPolygons/Ch16/`](SmoothedPolygons/Ch16) | Theorem 16.3.1 (Mahler's First conjecture), conditional on the hypothesis [`NoChatteringIntoSingularLocus`](SmoothedPolygons/Ch16/MahlerFirst.lean#L107), and its unconditional part (MahlerFirst) |
| [`SmoothedPolygons/AppA/`](SmoothedPolygons/AppA) | Corollary A.1.3 of Gronwall's inequality, with the two-sided form that Chapter 8 uses; the functional derivative, matrix identities, the Riemannian metric |
| [`Challenge.lean`](Challenge.lean), [`Solution.lean`](Solution.lean), [`comparator.json`](comparator.json), [`formalization.yaml`](formalization.yaml) | Palomar |
| [`scripts/`](scripts) | the audit, the route check, the Challenge sync, the documentation checks |
| [`docs/`](docs) | the routes of the book's proofs and the recorded differences |
| `.github/workflows/` | CI and Palomar's preflight |

## GitHub configuration

- [`lean_action_ci.yml`](.github/workflows/lean_action_ci.yml) runs on every push: it builds the project, checks that the audit imports
  every module, runs the audit and the route check, and checks the Challenge's copy of the shared
  definitions, the documents' links to the code and their tables.
- [`palomar_preflight.yml`](.github/workflows/palomar_preflight.yml) runs only on demand (`gh workflow run palomar_preflight.yml`); it needs
  the repository to be public, and declares the authorization relationship for Palomar.

## License

Apache-2.0; see [LICENSE](LICENSE).
