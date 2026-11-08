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
  every minimizer of the Reinhardt problem lifts to a Pontryagin extremal. A fifth round, the
  second layer, added Chapter 5 (the compactification of the star domain) and §6.1 (the existence
  of a minimizer), with the converse of Problem 3.6.2 that §6.1 uses and the identification of the
  minimizers of the control problem with Reinhardt's `K_min`, which the later chapters use. A
  sixth round, the third layer, added Chapter 8 (the edge control problem, singular subarcs and
  finite bang-bang control away from the singular locus) and Corollary A.1.3 (the case of
  Gronwall's inequality that Chapter 8 uses), and proves the book's main theorem, Mahler's First
  conjecture (Theorem 16.3.1), **only conditionally**, on one named hypothesis that stands for
  Theorems 16.4.1 and 14.4.1 of Chapters 13–16 (below). A seventh round, the fourth layer, added
  Chapter 13 (the Fuller system for triangular control: its symmetries, the first control and the
  switching times, the singular locus, the blow-up, the Fuller–Poincaré map, and its fixed points
  `q_out` and `q_in` with their stability), the first of the chapters whose results are to
  discharge that hypothesis; the hypothesis is unchanged. Chapter 1, Chapters 9–12 and Chapters
  14–16 apart from that conditional theorem are not formalized (Section 9).
- **Proved.** Every numbered result of Chapters 2, 3, 4, 5, 6, 7, 8 and 13 and Corollary A.1.3 is
  formalized and proved, among them Filippov's theorem (Theorem 6.1.1, cited without a source), Proposition 6.4.1 with
  Definition 6.3.1 (general left-invariant systems, on Mathlib's Lie groups), Theorem 5.0.6, whose
  second case the book only sketches, and Theorem 7.7.1 (the smoothed octagon is an isolated
  extremal), whose proof the book only sketches, and Lemma 13.5.5 (the fixed point `q_out` of the
  Fuller–Poincaré map is asymptotically stable), which the book proves by a Mathematica
  computation (E68). So are the remark after Definition 2.3.5 (the
  book's irreducibility is Mahler's), the action of the dihedral group on the ideal vertices of
  `𝔥*` (§4.6), the compactness and dihedral invariance of `𝔥**` (Definition 5.0.1), Remarks 2.2.4,
  6.6.1, 7.5.2 and 7.6.4, which the book states without proof, and three claims of the running
  text that the book's later chapters use: that every minimizer of the Reinhardt control problem
  lifts to a Pontryagin extremal (§6.2 and §6.6; "We have seen that the global minimizer must be
  extremal", TeX 6791), that a global minimizer exists (§6.1, E46), and that the global minimizers
  are Reinhardt's `K_min` (E47). Lemma 2.2.1 and Theorem 8.3.1 are false as printed and Theorem
  7.7.1 is false read literally (E1, E56, E32); Lemma 3.1.8 and the existence claim of Theorem
  6.1.1 lack a hypothesis (E34, E35); all five are proved in corrected forms approved by the user.
  The proof of Theorem 8.2.7 covers only part of its statement; the theorem is proved in the
  authors' reading, the user's decision, in which "singular" refers to the edge control problem
  on intervals where the control lies in an edge; its printed statement is proved for normal lifts
  and is open for abnormal ones (E55). Remark 8.3.3, stated without proof, is proved, with the
  balanced disk it speaks of as a hypothesis (E58). The converse of
  Problem 3.6.2, which §6.1 uses without proof, is false for trajectories that wind more than once
  around the origin and is proved for winding number one, which every trajectory cheaper than
  `7π/2` has (E15). What is left within these chapters is two conjectural remarks, the printed
  Theorem 8.2.7 for abnormal lifts, and the interpretation in Remark 13.5.4, which rests on a
  Mathematica computation and a later chapter (E69) (Section 9). The main
  results are Theorem 7.5.6 (each smoothed `(6k+2)`-gon is a Pontryagin extremal of the Reinhardt
  control problem with bang-bang control), the smoothed octagon's packing density (the octagon's
  trajectory bounds a balanced disk `K` whose area is the cost `√12(8 - √32 - ln 2)/(√8 - 1)` and
  whose greatest packing density is `δ(K) = (8 - √32 - ln 2)/(√8 - 1)`), Theorem 7.7.1, the lift of
  every minimizer to an extremal
  ([`exists_isPontryaginExtremal_of_isReinhardtMinimizer`](SmoothedPolygons/Ch6/MatrixExtremal.lean#L564)), Theorem 5.0.2 (a balanced
  disk whose trajectory leaves `𝔥**` is worse than the smoothed octagon), the second layer's
  result: the Reinhardt control problem has a global minimizer, which lifts to a Pontryagin
  extremal and bounds a `K_min`
  ([`exists_isReinhardtMinimizer_isPontryaginExtremal_isWorstDisk`](SmoothedPolygons/Ch6/WorstDisk.lean#L250)), and the third layer's: a global minimizer
  is edge extremal (Proposition 8.1.3), has no singular subarc in the authors' reading of Theorem
  8.2.7, and is bang-bang with finitely many switches on every interval on which its lift avoids
  the singular locus `𝒮_sing`
  ([`isFiniteBangBang_of_isReinhardtMinimizer_of_not_mem_singularLocus`](SmoothedPolygons/Ch16/MahlerFirst.lean#L165), the unconditional part of
  Theorem 16.3.1), and the fourth layer's: the Fuller–Poincaré map has exactly two fixed points at
  which the Hamiltonian vanishes, `q_out` and `q_in = τ(q_out)`, with the exact scaling factor
  `r_scale` (Lemma 13.5.2, [`lemma13_5_2`](SmoothedPolygons/Ch13/FixedPointsClassification.lean#L571)), and `q_out` is asymptotically stable and `q_in`
  unstable (Lemma 13.5.5, [`lemma13_5_5`](SmoothedPolygons/Ch13/Stability.lean#L281)).
- **Conditional: Theorem 16.3.1.** Mahler's First conjecture, the book's main theorem (the global
  minimizer of the Reinhardt control problem is bang-bang with finitely many switches, and every
  `K_min` is a finite-sided smoothed polygon with hyperbolic arcs at its corners), is proved only
  under one named hypothesis, [`NoChatteringIntoSingularLocus`](SmoothedPolygons/Ch16/MahlerFirst.lean#L107) ([`theorem16_3_1`](SmoothedPolygons/Ch16/MahlerFirst.lean#L343)): for every
  Pontryagin extremal of the Reinhardt problem (with the boundary conditions of Problem 3.6.2)
  that is edge extremal, and every time `t ∈ (0, T]` at which its lift meets `𝒮_sing`, the
  switching times of the control do not accumulate at `t` from the left while the trajectory is
  bang-bang off `𝒮_sing` before `t`. The hypothesis stands for Theorems 16.4.1 (the cluster point
  theorem) and 14.4.1 (no return), with their time reversals and the periodicity of extremals, as
  the last step of the book's proof uses them (TeX 12820–12833). Chapters 13–16 prove them; of
  these, Chapter 13 is formalized (the fourth layer) and Chapters 14–16 are not, so the hypothesis
  is unchanged, and later layers of the plan are to prove it (Section 11).
  It is not an axiom: it is a proposition in the statement of [`theorem16_3_1`](SmoothedPolygons/Ch16/MahlerFirst.lean#L343), which reads
  "[`NoChatteringIntoSingularLocus`](SmoothedPolygons/Ch16/MahlerFirst.lean#L107) implies Mahler's First conjecture"; no other result assumes it;
  the audit lists it among the results that [`theorem16_3_1`](SmoothedPolygons/Ch16/MahlerFirst.lean#L343) uses, and the axioms of
  [`theorem16_3_1`](SmoothedPolygons/Ch16/MahlerFirst.lean#L343) are Lean's three standard ones. Theorem 16.3.1 is therefore not yet proved: it
  will follow once the hypothesis is. The book's proof also leaves out the set of times at which
  the lift meets `𝒮_sing`, which the formalization handles (E60).
- **No cited result is assumed.** Every cited result that a proof uses is proved: Fejes
  Tóth's theorem (`δ = δ_L`), Gruber's lattice density formula, the theorems of Minkowski and
  Mahler on critical lattices and circumscribed hexagons, Mahler's Lemma 3 on irreducible domains
  (in full, along the two papers of Mahler on which its proof rests, with their errors and gaps
  repaired), the Euler–Arnold equation and the Pontryagin maximum principle (Section 2).
  Filippov's theorem is proved too, and §6.1 applies its form with a closed state constraint, a
  compact set of initial points and a closed endpoint relation (E46). All are stated in [`External/`](External),
  except that form, which is applied directly from the package. The
  maximum principle and Filippov's theorem (in both forms) are proved in the OptimalControl package
  ([github.com/vltanh/lean4-optimal-control](https://github.com/vltanh/lean4-optimal-control),
  required at a pinned commit), the maximum principle by Agrachev and Sachkov's own argument, with
  Brouwer's fixed-point theorem from the FixedPoint package
  ([github.com/vltanh/lean4-fixed-point](https://github.com/vltanh/lean4-fixed-point)). The
  integral form of Gronwall's inequality, from which §6.1 and Corollary A.1.3 need only the case
  with constant coefficients, is proved in the package too. A
  Pontryagin extremal is defined by the conditions of the maximum principle (Section 6), and the
  maximum principle shows that every minimizer is one. Theorem 3.1.4(3) keeps one hypothesis for a
  general convex disk (E13, approved by the user); for balanced disks it holds. The only
  assumption of the formalization is the hypothesis of Theorem 16.3.1 above, which stands for
  results of the book itself, not for a cited result (Section 2).
- **Build.** `lake build` succeeds; the only `sorry`s are the two statements of [`Challenge.lean`](Challenge.lean),
  by design. There is no `axiom`, `admit` or `native_decide`. [`scripts/Audit.lean`](scripts/Audit.lean) checks that every
  declaration of the library and the two Challenge theorems depend only on [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext),
  [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound). Palomar's Comparator accepts [`Solution.lean`](Solution.lean) against
  [`Challenge.lean`](Challenge.lean) under Lean's kernel and NanoDa.
- **Statements.** Three results of the book are false as stated and are formalized in corrected
  form, approved by the user: Lemma 2.2.1, with a machine-checked counterexample to the printed
  statement (E1), Theorem 7.7.1, which holds only up to time translation and for terminal times
  near `t_f` (E32), and Theorem 8.3.1, whose conclusion fails at a time where `Λ_R` vanishes and
  which is proved in a one-sided form, from which the form that Theorem 8.3.2 quotes follows
  (E56). Theorem 8.2.7 is formalized in the authors' reading, also the user's decision (E55). The
  restatement of Theorem 8.3.2 in Chapter 1, without "edge extremal", is false and is not
  formalized; the statement of Chapter 8 is (E57). Remark 8.1.6 has the wrong signs (E51), Lemma
  8.2.1 needs `⟨X, Z_u⟩ ≠ 0` on `U_T` (E52), and Remark 8.3.3 is stated with its balanced disk as
  a hypothesis (E58). Nine further statements and definitions are corrected: a definition missing a
  hypothesis (Definition 2.3.4, E6), two misprints in definitions (E16, E20), the nontriviality
  condition of a Pontryagin extremal, which the maximum principle yields only for boundary
  conditions written without two redundant equations (E21), and missing hypotheses in Theorem
  3.1.4(3) (E13), Lemma 3.1.8 (E34) and Theorem 6.1.1 (E35), each approved by the user, and in Lemma 4.2.3 (E17)
  and Lemma 7.3.1 (E26). The converse of Problem 3.6.2, which §6.1 uses without stating it, is
  false in general and is stated and proved for winding number one (E15); the fundamental domain of
  the dihedral group is the sector that the proof of Theorem 5.0.2 needs, not the set that §4.6
  prints (E40, E45). The identification of §13.4 that the book calls a diffeomorphism is a
  homeomorphism with `φ` only of class `C²` and is stated so (E66). Slips in proofs (E8, E14, E24,
  E44, E50, E59, E64, E65, E67) are corrected where they occur. Otherwise
  the Lean statements differ from the book's only by the omitted hypotheses of Section 5 and the
  readings of Section 6.
- **Proofs.** Every proof follows the book's argument, except the departures listed in Section 7,
  each forced by an error or gap of the book or by mathematics Mathlib lacks, or, for the last step
  of Theorem 16.3.1, by the chapters not yet formalized: Lemma 2.2.1 (its
  printed form is false), Lemma 2.2.5 (a gap the book's lines cannot close, closed by Mahler's
  lattice route, chosen by the user), one step each of Lemmas 2.4.2 and 2.4.6, the area formula of
  §3.2 (Green's theorem), Jacobi's formula (Lemma 3.1.12, approved by the user), Lemma 4.3.1,
  Theorem 5.0.6 (the claim of its first case, which the book does not argue, and its second case,
  which the book only sketches, argued corner by corner), Lemma 5.0.7 (3) (a step the book does not
  argue), the existence of a minimizer in §6.1 (Filippov's theorem with a closed state constraint
  in place of the book's cut-off, which changes the problem, and a time bound that does not
  presuppose a minimizer), the boundary conditions to which §6.2 applies the maximum principle
  (E21), one step of Theorem 7.7.1 (the fixed points of the Poincaré map near the octagon's,
  which the book's argument does not give uniformly), Proposition 8.1.3 (the principle of
  optimality, made precise by splicing in only competitors close to the edge arc, E48), two steps
  of Theorem 8.1.4 (the derivative of the switching function only at its zeros, and a zero at an
  end of the interval, E49), Theorem 8.2.7 (the authors' reading, E55), Theorem 8.3.1 (its
  passage to the control moved to a corollary with the restatement, E56), Lemma 13.2.5 and the
  descent of the Fuller–Poincaré map (symmetries applied outside their hypothesis `H_F = 0`, E63),
  Lemma 13.2.6 (the direction of its argument, E62), Lemma 13.3.2 (a gap, E65), Lemma 13.5.2 (a
  garbled step and an omitted verification, E67), Lemma 13.5.5 (a Mathematica computation
  replaced by an exact Jacobian and a certified eigenvalue bound, E68), and Theorem 16.3.1 (its
  last step replaced by the named hypothesis, and the set of meeting times handled, E60). The
  other gaps are filled along the book's lines. The maximum principle is
  proved by Agrachev and Sachkov's argument, with the departures and the three gaps of the source
  listed in Section 7.
  The route check ([`scripts/route_check.py`](scripts/route_check.py) against [`docs/paper_routes.tsv`](docs/paper_routes.tsv)) passes; its recorded differences are
  listed with their reasons in [`docs/route_differences.tsv`](docs/route_differences.tsv) (Section 8).
- **Redundant hypotheses.** Nine results of the book and one cited result hold without some of
  their hypotheses; the Lean statements omit them (Section 5). The Challenge keeps the book's
  hypotheses. Lemma 3.1.8, Proposition 6.4.1, Lemma 8.1.5, Theorem 8.3.1, Lemmas 13.2.8, 13.3.1
  and 13.3.2, Corollary A.1.3 and Filippov's theorem keep hypotheses of the book or of the source
  that their proofs do not use (Section 5).

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
  to time translation and for terminal times near `t_f` (E32). The converse of Problem 3.6.2, that
  an admissible trajectory bounds a balanced disk whose area is its cost, which §6.1 needs to apply
  Theorem 5.0.2 to the control problem, is false: the unit circle traversed seven times is an
  admissible trajectory of cost `7π` and bounds no such disk (E15). It holds for trajectories of
  winding number one, and every trajectory cheaper than `7π/2` has winding number one, by a bound
  that is not in the book (the cost is at least `3/2` times the angle that `σ₀` sweeps). The set
  that §4.6 gives as a fundamental domain of the dihedral group on `𝔥*` is the union of two of the
  six sectors, and the proof of Theorem 5.0.2, citing it, prints a curve; the proof needs a third
  set, a sector, which the formalization uses (E40, E45). Theorem 8.3.1 is false as printed: at a
  time where `Λ_R` vanishes every control maximizes the Hamiltonian, and such times occur off the
  singular locus on edge-extremal extremals; its one-sided form holds, and so does the form about
  the control that the proof of Theorem 8.3.2 quotes (E56). The restatement of Theorem 8.3.2 in
  Chapter 1 drops edge extremality and is false for extremals on an interval (E57). The abnormal
  costates of Remark 8.1.6 have the wrong sign: as printed, the edge minimizes the Hamiltonian
  (E51). §13.4 calls the weighted spherical coordinates of the blow-up a diffeomorphism; they are
  only `C²` along `z₂ = 0` and smooth elsewhere, which is all that Chapter 13 uses (E66). Slips
  that do not affect any result:
  the definition of a critical lattice omits admissibility (E6), an equation written too early in
  the proof of Theorem 2.3.9 (E7), a sign in the proof of Lemma 2.4.2 (E8), an index in the proof
  of Lemma 2.4.5 (E10), an index in the proof of Theorem 3.4.2 (E14), the centres of two geodesics
  in §4.6 (E40), a region in the proof of Lemma 5.0.7 (3) (E44), the claim in the proof of Theorem
  5.0.2 that `Π₂⁺` misses the fundamental domain, which it meets inside `B(i∞)` (E45), a sign
  convention in the proof of Proposition 6.5.1 (E22), the eigenvectors of §7.1 (E24), the sign
  of the switching functions in the proof of Theorem 7.7.1 (E32), the constant of Lemma 8.1.5
  (E50), two typos in the proof of Theorem 8.2.6 (E54), slips in the second variation of Theorem
  8.2.7 (E55), a reference in Theorem 8.3.1 (E56), a sign in the proof of Lemma 8.3.4 (E59), a
  strict inequality in the proof of Corollary 13.2.7 (E64), two typos in Lemma 13.3.2 (E65), and a
  garbled display in the proof of Lemma 13.5.2 (E67).
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
  extends to a periodic one, which the book also states without proof (E38). Chapter 5 asserts
  the compactness of `𝔥**` (E41) and gives no argument for the second claim of Lemma 5.0.3 (E42),
  the claim of the first case of Theorem 5.0.6 and its whole second case (E43), steps of Lemma
  5.0.7 (3) and (4) (E44), and, in the proof of Theorem 5.0.2, the application of Theorem 5.0.6 at
  an arbitrary time and a one-variable bound read off a graph (E45); all are true and proved. The
  argument of §6.1 for the existence of a minimizer does not hold as written: it applies Theorem
  5.0.2 to all admissible trajectories (which needs E15), changes the problem by a cut-off, applies
  Filippov's theorem with a fixed initial point while `X(0)` is free and the endpoints are coupled,
  and bounds the terminal time by Lemma 4.3.1, which assumes a minimizer; the formalization
  repairs it along its lines, with Filippov's theorem under a closed state constraint (E46). The
  book identifies the minimizers of the control problem with Reinhardt's `K_min` without proof;
  both directions are proved (E47), with the reparameterization of §3.5 that the book takes for
  granted (E39). In Chapter 8, the proof of Theorem 8.2.7 covers only the singular subarcs on
  which the Hamiltonian does not depend on the control; the edge case is left to the edge control
  problem in the authors' comments, and the formalization proves the theorem in that reading, with
  the printed statement for normal lifts, while for abnormal lifts it is open (E55). Proposition
  8.1.3 invokes the principle of optimality without saying how a competitor of the edge problem,
  whose state space is larger than the star domain, gives one of the Reinhardt problem (E48).
  Claim (b) of the proof of Theorem 8.3.1 is a sketch (E56); Remark 8.3.3 has no proof, and the
  disk it speaks of exists only for trajectories of winding number one (E58); the proof of Theorem
  16.3.1 does not handle the set of times at which the lift meets the singular locus (E60).
  Smaller gaps of Chapter 8: E49, E52, E53 (the Hamiltonian vanishes at a given time, which the
  maximum principle gives only almost everywhere), E54, E59, and Corollary A.1.3, stated for
  `t ≥ 0` but applied on both sides of `0` (E61). In Chapter 13, the book promises that the first
  control is well defined, but the proof of Lemma 13.2.6 argues only that a first control, if it
  exists, is the lexicographic maximizer, and the constancy of the Hamiltonian along extremals is
  asserted (E62); the symmetries of Lemmas 13.2.1–13.2.3 are applied outside their hypothesis
  `H_F = 0` (E63); the proof of Lemma 13.3.2 assumes the maximizing face constant in time (E65);
  the proof of Lemma 13.5.2 uses the well-definedness of the Poincaré map silently, asserts the
  passage to its three cases, the real roots of the palindromic polynomial and the coordinates
  (13.5.1), and does not check that its solutions are fixed points with `H_F = 0` (E67); and
  Lemma 13.5.5 is proved by a Mathematica computation with no chart, matrix or eigenvalues, with
  two steps not argued (E68). All of these are filled, except the abnormal case
  of the printed Theorem 8.2.7, and so are the further gaps E2, E3, E5, E7, E8, E9, E18, E23, E30,
  E31 and E34. Remark 13.5.4's interpretation of a fixed point, stated without proof, is not
  formalized (E69).
- **Missing hypotheses.** Theorem 3.1.4(3) is false for a general convex disk; it holds under the
  standing assumptions of §2.4 (E13). Lemma 3.1.8 is false unless the curves are regular, as §2.4
  assumes (E34). Filippov's theorem (Theorem 6.1.1) claims that an optimal control exists when
  the velocity sets are convex; this fails for costs that depend on the control, and holds when the
  velocity sets extended by the cost are convex (E35). Lemma 4.2.3 needs `X ≠ 0` (E17). Lemma
  7.3.1 needs `⟨X, Z_u⟩ ≠ 0` on the control set, which its proof uses (E26), and so does Lemma
  8.2.1 (E52). The converse of Problem 3.6.2 that §6.1 uses needs the trajectory to wind once
  around the origin (E15). Chapter 1's restatement of Theorem 8.3.2 needs edge extremality (E57).
- **Redundant hypotheses.** Several hypotheses are not needed; the Lean statements drop them
  (Section 5). The most notable: Lemma 7.3.1 holds for every compact convex control set on which
  `⟨X, Z_u⟩ ≠ 0`, not only one in the plane `u₀ + u₁ + u₂ = 1`. Some Lean statements keep a
  hypothesis of the book that their proofs do not use, among them the edge extremality of Theorem
  8.3.1, which the book needs only to pass to the control (E56), and the wall condition of Lemma
  13.2.8 (E64).
- **Use of cited results.** Chapter 2 rests on cited theorems: Fejes Tóth's `δ = δ_L`, Gruber's
  lattice density formula, Minkowski's and Mahler's theorems on critical lattices and circumscribed
  hexagons, and Shifrin's characterization of convex curves; the control-theoretic chapters cite
  the Pontryagin maximum principle (Agrachev–Sachkov), the Euler–Arnold equations (Cushman–Bates,
  with a sign slip, E22), the Iwasawa decomposition, Rademacher's theorem and Gronwall's
  inequality, and state Filippov's theorem without a source (Theorem 6.1.1, E35). All are proved
  here (Gronwall's inequality in the cases that §6.1 and Corollary A.1.3 use), in [`External/`](External) (with the
  OptimalControl package) or from Mathlib, except Shifrin's, which is applied outside its
  hypotheses and replaced by a direct argument (E11) (Section 2). §6.1 applies Filippov's theorem
  to a problem it does not cover (a free initial point, coupled endpoints, and a cut-off that
  changes the minimizers); its form with a closed state constraint, proved in the OptimalControl
  package by the same argument, does (E46). §6.1 also recalls Reinhardt's existence theorem, which
  concerns `K_min` and not the control problem (E47). The book's summary of the
  maximum principle omits one of its source's regularity hypotheses, which the Reinhardt problem
  satisfies. Proposition 8.1.3 applies the maximum principle to the edge control problem, which it
  covers, but does not say how minimality for the edge problem follows from minimality for the
  Reinhardt problem (E48). Chapter 8 applies Gronwall's inequality through Corollary A.1.3, which
  is stated for `t ≥ 0` and applied on both sides of `0` (E61). Agrachev and Sachkov's proof of
  the maximum principle has three gaps, all repaired (Section 7).
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
| Filippov's theorem: for a control system on `ℝⁿ` with compact control set, convex velocity sets and `f` of compact support, the attainable sets (at time `T` and up to time `T`) are compact, and an optimal control exists for an integral cost when the velocity sets extended by the cost are convex, with fixed or free terminal time | Agrachev–Sachkov, *Control Theory from the Geometric Viewpoint*, Thm 10.1; cited as Theorem 6.1.1 without a source (E35) | [`External.filippov`](External/Filippov.lean#L153); for §6.1, its form with a closed state constraint, a compact set of initial points, a closed endpoint relation and a window of terminal times, `ControlSystem.exists_optimal_constrained` of the OptimalControl package (same proof) | Theorem 6.1.1; the form with a state constraint, in §6.1: [`exists_isReinhardtMinimizer`](SmoothedPolygons/Ch6/Existence.lean#L436) (E46) |
| The Pontryagin maximum principle with free terminal time, an integral cost and mixed boundary conditions `(q(0), q(t_f)) ∈ N` (`N` cut out near the end points by a `C¹` submersion), for strong local minimizers on an open subset of a finite-dimensional space with a compact control set: `ν ≤ 0` and a Lipschitz covector curve `p` with `(ν, p(t)) ≠ 0` for every `t`, the adjoint equation, the maximum condition and `H = 0` almost everywhere, and the transversality condition `(-p(0), p(t_f)) ⊥ T N` | Agrachev–Sachkov, *Control Theory from the Geometric Viewpoint*, Ch. 12, Theorem 12.5 with the remark after it (free time), read in the authors' draft; cited in §6.2 from the entry `zelikin2004control` (E33) | [`External.pontryagin_maximum_principle`](External/Pontryagin.lean#L80), proved in the OptimalControl package (`Pontryagin.maximum_principle`) | [`exists_isPontryaginExtremal_of_isReinhardtMinimizer`](SmoothedPolygons/Ch6/MatrixExtremal.lean#L564) (§6.2 and §6.6: every minimizer is an extremal); [`proposition8_1_3`](SmoothedPolygons/Ch8/EdgeExtremal.lean#L850) (Proposition 8.1.3: the minimizer is edge extremal, by the principle for the edge control problem, E48) |

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
The form that §6.1 needs, for trajectories confined to a closed set `S`, starting in a compact set
and with endpoints in a closed relation (`OptimalControl.ODE.StateConstraint`, in the package), is
proved by the same argument: a limit of trajectories that stay in `S` stays in `S`, so the
dynamics need to be continuous, with bounded velocities and convex velocity sets, only on `S × U`,
and need not have compact support.

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
formalization follows it ([`exists_isPontryaginExtremal_of_isReinhardtMinimizer`](SmoothedPolygons/Ch6/MatrixExtremal.lean#L564), in
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

No result from prior work is assumed. One theorem, Theorem 16.3.1, is proved conditionally on a
hypothesis that stands for results of the book itself, from chapters not yet formalized:

| Result | Where the paper uses it | Source | Hypothesis in the formalization | What Lean lacks | Plan |
| --- | --- | --- | --- | --- | --- |
| No chattering into the singular locus: the switching times of a Pontryagin extremal do not accumulate at a time where its lift meets `𝒮_sing` | the last step of the proof of Theorem 16.3.1 (TeX 12820–12833) | the book: Theorem 16.4.1 (the cluster point theorem, with §16.4.2) and Theorem 14.4.1 (no return), with their time reversals and the periodicity of extremals (Remark 6.6.1) | [`NoChatteringIntoSingularLocus`](SmoothedPolygons/Ch16/MahlerFirst.lean#L107), a hypothesis of [`theorem16_3_1`](SmoothedPolygons/Ch16/MahlerFirst.lean#L343) and of no other result | Chapters 14–16 are not formalized: the blow-up of `𝒮_sing`, the analytic extension of Chapter 14 with a stable manifold theorem and Weierstrass preparation, and certified versions of the book's numerical computations (the global basin of Chapter 15, the unstable curve of Theorem 14.4.1). Chapter 13, the triangular Fuller system, is formalized (the fourth layer) | later layers of the plan (Section 11) |

The hypothesis is stated for every Pontryagin extremal of the Reinhardt problem on `[0, T]`, with
the boundary conditions of Problem 3.6.2 and the transversality conditions, that is edge extremal,
and for every time `t ∈ (0, T]` at which its lift meets `𝒮_sing`: there is no interval
`(t - δ, t)` on which the lift avoids `𝒮_sing`, the control is bang-bang with finitely many
switches on every compact subinterval, and the switching times accumulate at `t`
([`IsChatteringInto`](SmoothedPolygons/Ch16/MahlerFirst.lean#L58); a switching time is a time on each side of which the control is almost
everywhere constant at a vertex, with different vertices, [`IsSwitchingTime`](SmoothedPolygons/Ch16/MahlerFirst.lean#L48)). Its
docstring checks it against the book's argument: at `t` the lift is in `𝒮_sing`, so the extremal
is normal (Lemma 8.2.2) and its costate may be normalized to `λ_cost = -1`; in the blow-up of
`𝒮_sing` the switching points have a cluster point on the compact exceptional divisor, reached at
the finite time `t`; by Theorem 16.4.1 it is the fixed point `q_in`, approached along its stable
curve; by Theorem 14.4.1 and its time reversal, such a trajectory did not come from the divisor
at an earlier time; and the transversality conditions make the extremal periodic (Remark 6.6.1),
so that it meets `𝒮_sing` one period later and chatters into it again, a contradiction ("Thus,
the trajectory is not periodic. This is contrary to the boundary conditions"). The restriction to
edge-extremal extremals weakens the hypothesis: the book uses the argument only for the
minimizer, which is edge extremal (Proposition 8.1.3), and the proof of Theorem 14.4.1 needs the
trajectory between two meetings to be bang-bang, which Chapter 8 gives only under edge
extremality. The boundary conditions matter: near `𝒮_sing`, trajectories that chatter into it
exist (the inward spirals along the stable curve of `q_in` in Chapters 13–16). With Chapters 2–8
the hypothesis excludes every meeting of the minimizer's lift with `𝒮_sing` (E60).

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
| Implicit and inverse function theorems | proof of Theorem 7.7.1 (TeX 6588–6591, 6616); the smoothness of `F_ang` near `q_out` in Lemma 13.5.5 (E68) | Mathlib (`HasStrictFDerivAt.implicitFunctionOfProdDomain`; local injectivity from `ApproximatesLinearOn`; `ContDiffAt.implicitFunction`) |
| Parameterization by arclength of the boundary of a convex disk with a unique support line at each boundary point, as a regular `C¹` curve | §2.4, the standing assumption for `K_min` (TeX 2157–2158) | proved for worst disks in [`IsWorstDisk.exists_isBalancedPair`](SmoothedPolygons/Ch6/WdBoundaryParam.lean#L437), with the inverse of the arclength from [`exists_inverse_of_hasDerivAt_pos`](Basic/Analysis/Calculus/DerivInverse.lean#L29) in [`Basic/`](Basic) (E47) |
| The faces of a triangle other than itself are its vertices and its edges | Lemma 8.2.1 (TeX 7121–7123) | proved in the proof of [`lemma8_2_1`](SmoothedPolygons/Ch8/SingularLocus.lean#L586) |
| A plane curve with nonvanishing velocity and zero curvature lies on a line | §7.2 (TeX 5615–5621), in Remark 8.3.3 | proved in the proof of [`remark8_3_3`](SmoothedPolygons/Ch8/PolygonBoundary.lean#L877): `det(w(c), w)²/\|w\|²` has zero derivative, for the velocity `w` (Section 11) |
| Solutions of differential equations with analytic right-hand sides are analytic | proof of Lemma 8.3.4 (TeX 7637) | not used: Taylor expansions with remainder, by the mean value inequality, in the proof of [`lemma8_3_4`](SmoothedPolygons/Ch8/VertexControl.lean#L662) (E59) |
| Near `0⁺` a real polynomial has the sign of its lowest nonzero coefficient | proof of Lemma 13.2.6 (TeX 10978–11008), Corollary 13.2.7 | for cubics, [`exists_forall_Ioc_cubic_pos`](Basic/Analysis/Polynomial/SignNearZero.lean#L27) in [`Basic/`](Basic) |
| Linearized stability for maps (Lyapunov/Perron): a fixed point at which the derivative has all eigenvalues of modulus `< 1` is asymptotically stable | Lemma 13.5.5 (TeX 11443–11453) | [`Function.isAsymptoticallyStable_of_hasFDerivAt`](Basic/Dynamics/LinearizedStability.lean#L146) in [`Basic/`](Basic) (Mathlib has no stability theorem for maps) |

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
| Pontryagin maximum principle (Agrachev–Sachkov; the bibliography names Zelikin first, E33) | §6.2, §6.6, Problem 6.7.1; the proof of Proposition 8.1.3 (TeX 6791) | Correct for the Reinhardt problem, with the readings of Section 6. The book's summary states it for a smooth manifold and a closed control set; its source needs `∂f/∂q` jointly continuous in `(q, u)` (Agrachev–Sachkov's (10.4), which the summary omits) and, tacitly, locally bounded velocities `f(q, u(t))`, which a compact control set gives. Both hold for the Reinhardt problem (smooth dynamics on `GL₂⁺(ℝ) × C`, compact `U_T`). Applied with the full boundary conditions, its conclusions hold for every admissible trajectory with a covector whose reduced costate vanishes (E21); applied with the boundary conditions written without the two equations that first integrals make redundant, it gives the extremal lift of a minimizer, with nontrivial reduced costate ([`exists_isPontryaginExtremal_of_isReinhardtMinimizer`](SmoothedPolygons/Ch6/MatrixExtremal.lean#L564)). The source's proof has three gaps, repaired in the formalization (Section 7). In Proposition 8.1.3 the principle is applied to the edge control problem (an open subset of `ℝ³`, fixed endpoints, free terminal time), which it covers; what the book leaves out is how the minimizer's edge arc minimizes, locally, the cost of the edge problem (E48). |
| Filippov's theorem (no source given; Agrachev–Sachkov, Thm 10.1) | Theorem 6.1.1, its application in §6.1 | The existence of an optimal control needs the convexity of the velocity sets extended by the cost, which holds for the Reinhardt problem, whose cost depends only on the state (E35). The application in §6.1 is outside the theorem as stated: the initial point `X(0)` is free and the endpoints are coupled, and the cut-off that gives the fields compact support changes the minimizers. The form with a closed state constraint, a compact set of initial points and a closed endpoint relation, proved by the same argument, applies (E46). |
| Gronwall's inequality (Appendix A.1, from Amann) | §6.1, the bound on `g` (TeX 4584–4586); through Corollary A.1.3, Lemma 8.1.5 (TeX 7008) and the proof of Theorem 8.3.1 (TeX 7539, 7572) | Correct. Corollary A.1.3, which the book derives from it without proof, is stated for `t ≥ 0` and applied on both sides of `0`; the case `t < 0` follows by reversing time (E61). The formal proofs use its case with constant coefficients, proved in the OptimalControl package (`ControlSystem.le_mul_exp_of_le_add_integral`). |
| Reinhardt 1934, existence of a minimizer | §6.1 (TeX 4569–4572) | Not what §6.1 needs: Reinhardt's theorem gives `K_min`, a disk, not a minimizer of the control problem, and the book does not prove that the two correspond (E47). The formal existence proof does not use it; the identification with `K_min` does, as proved with Lemma 2.2.5 (E4). |

The other citations of the formalized chapters (Reinhardt 1934 apart from §6.1, Minkowski's other works, Hales 2017, Jurdjevic 2016,
Perelomov, Babelon et al., Colombo–de Diego, Gay-Balmaz et al., Vajjha's thesis, and in Chapter 8
Hartl, Sethi and Vickson's survey of maximum principles with state constraints, cited in Remark
8.1.6, and Mahler's second-variation proof that the circle is not a local minimizer, cited before
Theorem 8.2.7, whose proof gives its own computation) give context and are not used in proofs;
Vajjha's thesis is cited for the omitted proof of Theorem 6.8.3. Lemma A.1.2 (Clarke) is not used.

## 3. Errors and gaps in the paper

E1–E32 follow the order of the book and E33 concerns its bibliography. E34–E37, found when the
remaining results of the formalized chapters were formalized, follow, again in the book's order,
then E38, found in the fourth round, E39–E47, found in the fifth round (Chapter 5 and §6.1),
E48–E61, found in the sixth round (Chapter 8, Theorem 16.3.1 and Corollary A.1.3), and E62–E69,
found in the seventh round (Chapter 13), each group in the book's order. E15 was revised in the
fifth round; E15, E21 and E47 were extended in the sixth.

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
inscribed on `u` all have the same area). Chapter 5 and the identification with `K_min` use it
too (E42, E47).

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

**E15. Problem 3.6.2, §3.6 (TeX ~3205), and §6.1 (TeX 4579): a converse used but not proved, and
false in general.** "The convex disks in `𝔎_bal` in circle representation arise via the following
optimal control problem": the book derives the problem from balanced disks and does not show the
converse, that an admissible trajectory bounds a balanced disk whose area is its cost; in
particular that its curve is simple. §6.1 needs the converse to apply Theorem 5.0.2, a statement
about balanced disks, to the trajectories of the control problem (E46). It is false: the boundary
conditions, chosen so that "the curves `σ_j` close up seamlessly to form a simple closed curve"
(TeX 3135–3139), do not force simplicity, and an admissible trajectory may wind `1 + 6m` times
around the origin. The unit circle traversed seven times (`X ≡ J`, `u ≡ (1/3, 1/3, 1/3)`,
`t_f = 7π/3`) is admissible, has cost `7π`, and is not the boundary trajectory of any balanced pair
([`exists_isReinhardtAdmissible_not_isWindingOne`](SmoothedPolygons/Ch6/Winding.lean#L550)). The book meets the phenomenon in the proof of
Lemma 7.5.5, where other eigenvalues "will produce the right boundary conditions, but the
corresponding multi-curves `σ_i` will have the wrong winding number around the origin" (TeX
6323–6326). The converse holds for trajectories of winding number one ([`IsWindingOne`](SmoothedPolygons/Ch6/Winding.lean#L82);
[`exists_isBalancedPair_of_isReinhardtAdmissible`](SmoothedPolygons/Ch6/AdmissibleDisk.lean#L937)), by the argument that proves it for the smoothed
`(6k+2)`-gons ([`smoothedPolygonDisk_spec`](SmoothedPolygons/Ch7/SmoothedPolygonDisk.lean#L1392); simplicity by a winding-number argument), generalized to any
measurable control. Higher winding costs more: the cost is at least `3/2` times the angle swept
by `σ₀ = g s₀*`, so a trajectory of winding number `1 + 6m` costs at least `π/2 + 3πm`
([`three_halves_mul_angle_le_reinhardtCost`](SmoothedPolygons/Ch6/Winding.lean#L447)). This bound is not in the book; its proof is a pointwise
inequality: with `ψ` the polar angle of the bottom row `(g₁₁, g₁₀)` of `g`, which ends where the
angle of `σ₀` ends, `κ = -tr(JX)` (the cost is `(3/2)∫κ`) satisfies `κ ≥ ψ'` because
`c(κ - ψ')(p² + q²) = (cp - aq)² + q² det X` for `X = [[a, b], [c, -a]]`, `(p, q) = (g₁₀, g₁₁)`,
and `c > 0` on star states. So
every admissible trajectory cheaper than `7π/2` has winding number one
([`isWindingOne_of_reinhardtCost_lt`](SmoothedPolygons/Ch6/Winding.lean#L497)), in particular every one at most as costly as the smoothed
octagon, which is all §6.1 needs. Remark 8.3.3 takes the converse for granted again, for
extremals that avoid the singular locus, and the formalization takes the disk there as a
hypothesis; it exists for the global minimizer (E58).

**E16. Problem 3.6.2, §3.6 (TeX 3235): misprint in a definition.** The terminal condition is
printed `X(t_f) = R X₀ R⁻¹`. The derivation just before (TeX 3152–3156), the half-plane form
(TeX 3606), the transversality conditions (TeX 5207) and the remark after them (TeX 5221) all give
`X(t_f) = R⁻¹ X₀ R`, and the two differ because `Ad_R` has order 3. For the smoothed octagon,
`X(t_f) = R⁻¹X₀R`, and `R⁻¹X₀R - RX₀R⁻¹ = diag(δ, -δ)` with `δ ≈ 0.433`. The formalization uses `R⁻¹X₀R`
([`IsReinhardtAdmissible`](SmoothedPolygons/Ch3/ControlProblem.lean#L110), [`IsPontryaginExtremal`](Challenge.lean#L171)).

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
(Section 7). The lemma is true. §6.1 uses it to bound the terminal time of every competitor before
a minimizer is known to exist; the formalization uses instead the lemma's other step, that the
cost density is at least `3` on star states, stated for every state trajectory
([`three_mul_le_reinhardtCost`](SmoothedPolygons/Ch4/TerminalTime.lean#L71); E46).

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
admissible trajectory ([`isReinhardtAdmissible_of_mem_matrixEndpoints`](SmoothedPolygons/Ch6/MatrixMinimizer.lean#L297)). The formalization applies the
maximum principle with the boundary condition without them ([`matrixBoundary`](SmoothedPolygons/Ch6/MatrixSystem.lean#L136)); transversality in the
two directions this frees gives `p(t_f)₁₁ = 0` and `Λ₂(t_f)₀₁ = 0`, which exclude these covectors
([`eq_zero_of_covectorΛ_eq_zero`](SmoothedPolygons/Ch6/MatrixCostate.lean#L526)), and the nontriviality of the reduced costate follows: if
`λ_cost = 0` and `Λ₁, Λ_R` vanish at one time, they vanish identically (Corollary 6.5.3 and the
linear `Λ_R` equation), so the covector vanishes at `t_f`
([`exists_isPontryaginExtremal_of_isReinhardtMinimizer`](SmoothedPolygons/Ch6/MatrixExtremal.lean#L564); Section 7).
Chapter 8 depends on this reading. Lemma 8.2.2 (TeX 7163–7166) and the proof of Theorem 8.3.1
(TeX 7583–7584) obtain `λ_cost ≠ 0` at a time where `Λ_R = Λ_R' = 0` from "the non-vanishing of
the costate variables in the maximum principle", that is, from the nontriviality of
`(λ_cost, Λ₁, Λ_R)`. Under the book's condition on `(λ_cost, Λ₁, Λ₂)` this step fails: the
spurious lift `(0, 0, X)` above has `Λ_R ≡ 0` and `λ_cost = 0`, so Lemma 8.2.2 would be false,
and Theorem 8.2.3 would make every admissible trajectory a circular arc. Under the formalization's
condition both hold as printed ([`lemma8_2_2`](SmoothedPolygons/Ch8/SingularLocus.lean#L783), [`theorem8_3_1`](SmoothedPolygons/Ch8/FiniteBangBang.lean#L1288)). The corresponding step for the edge
control problem (the proof of Theorem 8.1.4, TeX 6871–6874) concerns that problem's own costate
`(λ₁, λ₂, λ₃)`, and holds as printed.

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
terminal time ([`External.filippov`](External/Filippov.lean#L153); Sections 4 and 6). §6.1 cites no source for the theorem; Hales's
2017 preprint cites it as Theorem 10.1 of Agrachev and Sachkov's book, the entry
`zelikin2004control` of the bibliography (E33). The problem to which §6.1 applies the theorem is
not covered by it, even corrected; a form with a closed state constraint is (E46).

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

**E39. §3.5 (TeX 3140–3156): a reparameterization taken for granted.** To derive the terminal
condition `X(t_f) = R⁻¹X₀R`, the book writes `g(t + t_f) = g(s(t))R` "for some
orientation-preserving reparameterization `s(t)` such that `s(0) = 0`", obtained "by the remark
following Theorem 3.1.1"; that remark (TeX 2378–2390) does not contain it. Differentiating and
using `det X = 1` then gives `s' = 1`. For a `K_min` parameterized as in §2.4 the
reparameterization exists: the multi-point through a boundary point is unique (Lemma 2.2.7), so
`σ_{j+1}(t) = σ_j(h(t))` for a function `h`, which is `C¹` by the inverse function theorem applied
to the polar angles; differentiating `g(h(t)) = g(t)R` gives `h'(t)² det X(h(t)) = det X(t)`, so
`h' = 1` in the parameterization with `det X = 1`, and counting the turning of the polar angle
(`σ_{j+3} = -σ_j`) gives `h(0) = t_f`. The formalization proves `σ_j(t + t_f) = σ_{j+1}(t)` in this
way ([`IsWorstDisk.shift_of_det_one`](SmoothedPolygons/Ch6/WdTrajectory.lean#L537)) and follows the book's derivation from there; the
identification with `K_min` needs it (E47).

**E40. §4.6 (TeX 3797–3808): the fundamental domain is not one.** The three geodesics through `i`
that the dihedral group permutes (the medians: the imaginary axis and the circles
`(x ∓ 1/√3)² + y² = 4/3`) cut `𝔥*` into six sectors, which the group permutes simply transitively,
so each sector is a fundamental domain, as the book says. The set it then gives as one,
`{x ≥ 0, (x - 1/√3)² + y² ≤ 4/3}` (TeX 3807), is the union of two sectors, split by the median
`(x + 1/√3)² + y² = 4/3`, and contains two points of each generic orbit. A single sector is
`{x ≥ 0, (x + 1/√3)² + y² ≤ 4/3}`, or `{x ≥ 0, (x - 1/√3)² + y² ≥ 4/3}`, the one that the proof of
Theorem 5.0.2 needs (E45). The text also puts the centres of the two circles at "the two cusps
`(0, ±1/√3)` on the real axis" (TeX 3802), for `(±1/√3, 0)`. The formalization proves that every
orbit meets the last sector ([`exists_dihedralAct_mem_fundamentalDomain`](SmoothedPolygons/Ch5/Compactification.lean#L773)), which is what the proof
uses.

**E41. Definition 5.0.1 (TeX 3900–3978): three facts asserted.** "The set `𝔥** ⊂ 𝔥*` is
compact" (TeX 3975) is not immediate: `𝔥*` is open, and the closed versions of the inequalities
that define `𝔥**` also admit the cusps `(±1/√3, 0)`, as isolated points. The formalization proves
it ([`isCompact_truncatedStarDomain`](SmoothedPolygons/Ch5/Compactification.lean#L556)): the conditions of `Π₀⁺`, `Π₁⁺`, `Π₂⁺` give
`y ≥ (4/(15√3))(225/226) > 0.15` on `𝔥**`, so `𝔥**` is the set of the closed inequalities and
`y ≥ 0.15`. The image of a horoball under a linear fractional transformation (TeX 3903–3915) and
the invariance of `𝔥**` under the dihedral group (TeX 3977–3978) are also stated without proof;
both are proved ([`lftAct_image_horoball`](SmoothedPolygons/Ch5/Compactification.lean#L422), [`image_lftAct_R_truncatedStarDomain`](SmoothedPolygons/Ch5/Compactification.lean#L740),
[`image_reflAct_truncatedStarDomain`](SmoothedPolygons/Ch5/Compactification.lean#L746)).

**E42. Lemma 5.0.3 (TeX 4000–4015): the second claim is not argued.** The lemma says that the
hexagon `H_K(z)` built from `z ∈ 𝔥*` by Remark 3.1.7 is "the critical hexagon at the multi-point
`{s_j*}` of `K`" when `z` comes from a balanced disk `K` in circle representation; the proof only
reconstructs the hexagon. The same identification, at every time, is asserted after Lemma 3.1.8
(TeX 2583–2587). It is true, and the formalization proves it ([`lemma5_0_3`](SmoothedPolygons/Ch5/Hexagon.lean#L498)): the edge lines of
`H_K(z)` are the tangents of the boundary curves at the `s_j*`, hence support lines, so
`K ⊆ H_K(z)`; `area(H_K(z)) = 4 det(s₁*, s₂*) = √12`; and every centrally symmetric hexagon
containing `K` has area at least `√12`, since one of least area exists and has area
`area(K)/δ(K)` by Theorem 2.2.2, which is `√12` by E12. Theorem 2.3.9 identifies it with the
critical hexagon of Definition 2.3.8.

**E43. Theorem 5.0.6 (TeX 4203–4317): a claim not argued, and a case only sketched.** In Case 1
(`z ∈ h₀`, `z ∉ h₁ ∪ h₂`) the proof cuts the corner `p₀` of the critical hexagon by a segment
`[r₀, r̃₀] ∥ s₀s₁` with `area(△r₀p₀r̃₀) = T₀^ext` and claims that it meets `∂K`: "Otherwise ... the
convex disk `K` would be contained in the centrally symmetric hexagon with vertices `r₀, r̃₀, q₁`,
and their reflections", which has the area of `H_K(z)`, and an inward shift of the cut would give a
smaller one (TeX 4271–4281). It does not say why `K` would lie in that hexagon, nor that these six
points bound a convex hexagon. Case 2 (`z ∈ h₀ ∩ h₁`) says only that "the above argument
can also be adapted" (TeX 4301–4312). Both are true. The formalization shifts the cut line at once
to the support line of `K` parallel to `s₀s₁`: if that line lies strictly inside the cut, the
hexagon cut at it contains `K`, is centrally symmetric and convex, and has area
`area(H_K(z)) + 2T₀^ext - 2μ²T₀ < area(H_K(z))` (`μ > √(T₀^ext/T₀)` the ratio of the line),
contradicting minimality; otherwise the extreme point of `K` on the cut line lies on `[r̃₀, r₀]`
([`exists_mem_frontier_segment_cut`](SmoothedPolygons/Ch5/AreaBound.lean#L519)). The construction changes `H_K(z)` only near the corners `p_i`,
`p_{i+3}` and the edges beyond them, so the claim holds at each corner `i` with `z ∈ h_i`
separately; the triangles `±△s_i r_i s_{i+1}` then lie beyond distinct edges of `conv{s_j*}`,
with pairwise disjoint interiors, which gives the bound in all cases at once ([`theorem5_0_6`](SmoothedPolygons/Ch5/AreaBound.lean#L777);
Section 7). The step `h₀ ∩ h₁ ∩ h₂ = ∅` of the book's proof ([`inter_hRegion_eq_empty`](SmoothedPolygons/Ch5/AreaBound.lean#L492)) is then
not needed.

**E44. Lemma 5.0.7 (TeX 4432–4465): gaps in (3) and (4), and a slip.** (3) says that
`I₀area₀ + I₂area₂` is least at `x = 0` on each line `y = const ≥ √3`. The proof shows that the
sum (5.0.1) over all `i` is continuous, that it increases in `x` on `h₀ ∖ h₂` and on `h₀ ∩ h₂`, and
concludes that it increases on `h₀ ∩ {x > 0, y ≥ √3}`; it never shows that the points with
`x > 0`, `y ≥ √3` lie in `h₀`, and its mirror statement, decrease "on `h₀ ∩ {x < 0, y ≥ √3}`" (TeX
4447), should read `h₂ ∩ {x < 0, y ≥ √3}`. The inclusion holds: with `s = √3x ≥ 0` and `y ≥ √3`,
`T₀ ≥ T₀^ext` reads `(1 + s)(s² + 3y² - 1) ≥ 8(1 - s)²`, and the difference is at least
`s(s² - 7s + 24) ≥ 0`. Then, since `I_i area_i = max(area_i, 0)` on `𝔥*`,
`I₀area₀ + I₂area₂ = max(area₀ + area₂, area₀)` for `x ≥ 0`, the maximum of two functions that (2)
and (1) show increasing, which makes the book's "increasing on each piece, and continuous" precise
([`lemma5_0_7_3`](SmoothedPolygons/Ch5/Monotonicity.lean#L541)). (4) says that `δ(x, y) ≥ δ(0, y) ≥ δ(0, 4.5) > δ_oct` for `y ≥ 4.5`. The first
inequality does not follow from (3), since `δ` also contains `I₁area₁`; it holds because
`I₁area₁ ≥ 0` and `(0, y) ∉ h₁` (on the imaginary axis `T₁ < T₁^ext`, as `(3y² - 1)² > 1`). The
second takes `area₀(0, y) = (√3/4)√(ρ₀ρ₂)(√(ρ₀ρ₂) - 2ρ₁)` increasing because both factors increase;
that also needs `√(ρ₀ρ₂) - 2ρ₁ ≥ 0`, true for `y ≥ √3`. Both are filled ([`lemma5_0_7_4`](SmoothedPolygons/Ch5/Monotonicity.lean#L693)).

**E45. Proof of Theorem 5.0.2 (TeX 4469–4513): a misprinted domain, a false remark, a tacit step and
two assertions.** (a) The fundamental domain is printed `{x ≥ 0, (x - 1/√3)² + y² = 4/3}` (TeX
4479), a curve, and attributed to §4.6, which prints another set that is not a fundamental domain
(E40). The proof needs the sector `{x ≥ 0, (x - 1/√3)² + y² ≥ 4/3}`, which lies in
`{x ≥ 0, y ≥ 1}` as the proof says (TeX 4481–4482); with §4.6's `≤ 4/3`, the half-plane `Π₁⁺`
would meet the domain (at `(0.1, 0.58)`, for instance). The formalization uses `≥ 4/3`. (b) "The
only half-plane meeting this set is `Π₀⁺`" and "the regions `Π₁⁺` and `Π₂⁺` do not meet the
fundamental domain" (TeX 4483–4484, 4501) are false for `Π₂⁺ = {y > 15(x + 1/√3)}`, which meets
`{x ≥ 0, y ≥ 1}` where `y > 15/√3 ≈ 8.66`. Those points lie in `B(i∞)`, so the proof is unaffected
([`mem_horoball_or_edgeHalfPlane_of_mem_fundamentalDomain`](SmoothedPolygons/Ch5/Compactification.lean#L848) states what it uses). (c) Theorem 5.0.6 is
about the multi-point at time `0` of a disk in circle representation, but the proof applies it at
any time where the trajectory leaves `𝔥**` ("If any point of the trajectory `(g, X)` passes through
a point `X = Φ(z)`", TeX 4486). That needs the re-centered pair `g(t₀)⁻¹K`, `g(t₀)⁻¹σ_j(· + t₀)`,
which is balanced, in circle representation, of the same area, with `X(0) = X(t₀)`
([`IsBalancedPair.recenter`](SmoothedPolygons/Ch5/Recenter.lean#L147)). (d) The inclusion `𝔥* ∩ Π₀⁺ ∩ {1 ≤ y ≤ 4.5} ⊆ h₀` (TeX 4499) is
asserted; it holds because there `ρ₁ < 1/15` and `ρ₀ρ₂ ≥ 1/3` ([`edgeSlab_subset_hRegion`](SmoothedPolygons/Ch5/EdgeBound.lean#L91)). The
bound `δ₀ > δ_oct` on the line `y = 15(1/√3 - x)`, `1 ≤ y ≤ 4.5`, is left to "a single variable
calculation" and "the graph" (TeX 4507–4512). `δ₀` is not monotone along the line (it increases
for `y ∈ [1, 1.152]`), but there `ρ₁ = 1/15` exactly and `6yρ₀ρ₂` is a concave quadratic in `y`, so
the bound reduces to the endpoints; the margin is `0.0018` (the minimum is `0.904209`, at
`y = 4.5`, against `δ_oct = 0.902414`) ([`octagonDensity_lt_edgeLine`](SmoothedPolygons/Ch5/EdgeBound.lean#L129)).

**E46. §6.1 (TeX 4520–4602): the existence of a minimizer.** The book argues that the Reinhardt
control problem has an optimal control by Filippov's theorem (Theorem 6.1.1): the control set
`U_T` is compact; the velocity sets are convex (Lemma 6.1.2); by Theorem 5.0.2 "we may assume that
`z` lies in the compact set `𝔥**`" (TeX 4579), `t_f ≤ π/3` by Lemma 4.3.1, and Gronwall's
inequality bounds `g`; and the vector fields, multiplied by a smooth cut-off `ψ` with `ψ = 1` on
`𝔥**`, have compact support. Four steps fail as written. (a) Theorem 5.0.2 is about balanced
disks; applying it to the trajectories of the control problem needs the converse of Problem
3.6.2, which is false for trajectories of higher winding number and true for those of winding
number one, among them every trajectory cheaper than `7π/2` (E15). (b) The cut-off changes the
dynamics outside `𝔥**`, so a minimizer of the cut-off problem need not be a trajectory of the
Reinhardt problem. (c) Theorem 6.1.1 concerns the attainable sets from a fixed initial point,
while `X(0)` is free and the endpoints are coupled (`X(t_f) = R⁻¹X(0)R`). (d) Lemma 4.3.1 bounds
the terminal time of a minimizer, whose existence is what is being proved. The formalization
repairs all four along the book's lines ([`exists_isReinhardtMinimizer`](SmoothedPolygons/Ch6/Existence.lean#L436)): it imposes `z ∈ 𝔥**` as a
closed state constraint, as the book's "we may assume" says, with a compact set of initial
points and the closed endpoint relation of the problem, and applies Filippov's theorem in that
form (`ControlSystem.exists_optimal_constrained`, proved in the OptimalControl package by the
argument of Theorem 6.1.1, and needing no compact support) to the matrix system of §6.2; the
terminal time is bounded by the argument of Lemma 4.3.1 for every state trajectory, the cost
being at least `3t_f` ([`three_mul_le_reinhardtCost`](SmoothedPolygons/Ch4/TerminalTime.lean#L71)), so a competitor cheaper than the smoothed octagon
(cost `< π`) has `t_f < π/3`. The smoothed octagon belongs to the constrained class, so
costlier competitors do not matter, and cheaper ones stay in `𝔥**` by (a) and Theorem 5.0.2
([`IsReinhardtAdmissible.forall_mem_truncatedStarDomain`](SmoothedPolygons/Ch6/Existence.lean#L322)). With §6.2 the minimizer lifts to a Pontryagin
extremal ([`exists_isReinhardtMinimizer_isPontryaginExtremal`](SmoothedPolygons/Ch6/Existence.lean#L511)), the premise of Proposition 8.1.3 (TeX
6791).

**E47. §6.1 (TeX 4571–4572), Proposition 8.1.3 (TeX 6786) and Theorem 16.3.1 (TeX 12789–12795):
the minimizer of the control problem is identified with `K_min` without proof.** "Recall that
Reinhardt has proved the existence of a optimal solution to the Reinhardt problem" (TeX 4571)
concerns Reinhardt's `K_min`, a centrally symmetric convex disk of least greatest packing density;
Proposition 8.1.3 speaks of "the global solution of the Reinhardt problem", and Theorem 16.3.1
passes from "the global minimizer of the Reinhardt optimal control problem" to "the minimizer
`K_min` of the Reinhardt problem". The book derives the control problem from `K_min` (Chapters
2–3) but does not show that the two minimizers correspond. They do, in both directions. Every
`K_min`, after a linear map of positive determinant, is a balanced disk in circle representation
whose boundary trajectory is admissible with cost its area (Chapters 2–3, with the arclength
parameterization of `∂K_min`, which §2.4 assumes, constructed from Lemma 2.2.5, and the
reparameterization of E39), and that trajectory is a global minimizer: a competitor cheaper than
`7π/2` bounds a balanced disk of area its cost (E15), whose density is at least `δ_min`, and a
costlier one costs more than the area `π` of the unit disk, hence more than `√12 δ_min`
([`exists_isReinhardtMinimizer_of_isWorstDisk`](SmoothedPolygons/Ch6/WorstDisk.lean#L183)).
Conversely, the disk bounded by a global minimizer is a `K_min`, with `δ_min = cost/√12` (E12;
[`isWorstDisk_of_isReinhardtMinimizer`](SmoothedPolygons/Ch6/WorstDisk.lean#L217)). With E46 and §6.2: the Reinhardt control problem has a global
minimizer, which lifts to a Pontryagin extremal and bounds a `K_min`
([`exists_isReinhardtMinimizer_isPontryaginExtremal_isWorstDisk`](SmoothedPolygons/Ch6/WorstDisk.lean#L250)). The second sentence of Theorem 16.3.1, about `K_min`, rests on this
identification (E60). The definite articles of "the global solution", "the global minimizer"
(Proposition 8.1.3, Theorem 8.2.7, Theorem 16.3.1) and "the minimizer `K_min`" presuppose a
uniqueness that is not known; the formalization states these results for every global minimizer
and every `K_min` (E48, E55, E60).

**E48. Proposition 8.1.3, §8.1 (TeX 6785–6798): the principle of optimality, invoked without a
construction.** The proof says that on a subinterval where the control lies in an edge of `U_T`,
"the globally minimizing trajectory must minimize cost among all trajectories with the same
endpoint conditions on the subinterval and that have their control function similarly restricted
to the edge. Thus, the global minimizer is also edge extremal." Two steps are left out. The first
is how a competitor of the edge control problem (Definition 8.1.1) gives a competitor of the
Reinhardt problem: the running text of §8.1 relates the two problems through (8.1.1) and a cost
identity, but the proof does not use them, and the state space of the edge problem (`y > 0`,
`|x| < 1/√3`) is larger than the star domain, so a competitor may leave the state space of the
Reinhardt problem and give no admissible trajectory. The second is the maximum principle for the
edge problem, which turns minimality into edge extremality. Both are supplied along the book's
lines ([`proposition8_1_3`](SmoothedPolygons/Ch8/EdgeExtremal.lean#L850)). Only competitors uniformly close to the minimizer's edge arc are
spliced in, so that they stay in the star domain (strong local minimality, which is all the
maximum principle needs); a competitor's trajectory is rebuilt from `(x, y, s)` by (8.1.1)
([`eqn_g_edge`](SmoothedPolygons/Ch8/EdgeProblem.lean#L494)), so that it ends at the minimizer's `g(d)` and `X(d)`; the rest of the minimizer is
shifted in time (the terminal time is free); and the costs differ by `3/2` times the difference of
the edge costs, by the cost identity `(3/2)((s + x)| + ∫x²/y)` of §8.1 ([`edgeCost_identity`](SmoothedPolygons/Ch8/EdgeProblem.lean#L601)). The
maximum principle for the edge problem (an open subset of `ℝ³`, fixed endpoints, free terminal
time, an integral cost) is [`External.pontryagin_maximum_principle`](External/Pontryagin.lean#L80). "We have seen that the global
minimizer must be extremal" (TeX 6791) is §6.1–§6.2 (E46,
[`exists_isPontryaginExtremal_of_isReinhardtMinimizer`](SmoothedPolygons/Ch6/MatrixExtremal.lean#L564)), and "the global solution" presupposes
uniqueness (E47).

**E49. Theorem 8.1.4, §8.1 (TeX 6807–6894): "optimal" in the statement, and three steps of the
proof.** The theorem concerns "an extremal lifted trajectory in the edge control system" but
says "Then the optimal control function `u_e` is bang-bang"; the proof uses extremality only, and
Theorems 8.2.7 and 8.3.2 apply the theorem to extremals that need not be optimal. The
formalization states it for every extremal, normal or abnormal ([`theorem8_1_4`](SmoothedPolygons/Ch8/EdgeBangBang.lean#L823)). In the proof:
(a) "The function `λ₂'` is also continuous by the form of the ODE it satisfies" (TeX 6846–6852):
the right-hand side of (8.1.7) contains the measurable control, so `λ₂` is only absolutely
continuous, and its derivative is continuous only after the control is changed on a null set,
which the book does at the end of the proof. The proof uses `λ₂'` only at the zeros of `λ₂`, where
the control-dependent term, `λ₂` times a bounded function, tends to `0`; the formalization proves
the derivative there and nothing more (Section 7). (b) At a zero `t₂` with `λ₂(t₂) = λ₂'(t₂) = 0`
the proof solves `H = ∂H/∂y = 0` (TeX 6866–6869), but the maximum principle gives `H = 0` only
almost everywhere; at `t₂` it holds by continuity, for the same reason (E53). (c) "The next lemma
shows that even at times when the conditions of (8.1.8) are met, the zeros of the switching
function `λ₂` are isolated" (TeX 6884–6886): Lemma 8.1.5 assumes solutions on an interval
`(-t₁, t₁)` around the zero, which can be an end of `[t₀, t₁]`. The formalization continues the
state and the costate past the end with the control `u_e = 0`, for which the solution is
explicit (with `λ_cost = -1`: `x = x₀ + y₀t`, `y = y₀`, `λ₁ = 2x₀t/y₀ + t²`,
`λ₂ = -2x₀t²/y₀ - 2t³/3`). The count of the zeros at which `λ₂' = 0` ("at most two times", TeX
6875–6879, since `x' = y > 0`) is proved
([`IsEdgeProblemExtremal.exists_tangentialZeros_subset_pair`](SmoothedPolygons/Ch8/EdgeBangBang.lean#L414)). The theorem is true.

**E50. Lemma 8.1.5, §8.1 (TeX 6908–7015): a wrong constant.** For `x₀ ≠ 0` the proof sets
`C = -x₀(1 + y₀)/y₀²` (TeX 6934) and integrates `2x₀(1 + y₀)τ/y₀²` (TeX 6973). Its own preceding
lines give `(x² - x₀²)/y² = 2x₀t/y₀ + O(t²)` (TeX 6970) and `λ̃₁ = 2x₀t/y₀ + O(t²)`, so
`λ̃₂ = -∫₀ᵗ 4x₀τ/y₀ dτ + O(t³) = -2x₀t²/y₀ + O(t³)`, and `C = -2x₀/y₀`. The statement claims only
`C ≠ 0`, which holds with the correct value, and for `x₀ = 0` the book's `C = -2/3` is right; the
formalization proves the lemma with `C = -2x₀/y₀` ([`lemma8_1_5`](SmoothedPolygons/Ch8/EdgeLandau.lean#L504)). The book's Landau notation is
two-sided (TeX 6903–6907), and the Gronwall step applies Corollary A.1.3, stated for `t ≥ 0`, on
both sides of `0` (E61).

**E51. Remark 8.1.6, §8.1 (TeX 7035–7070): wrong signs.** With `λ_cost = 0` and the printed
`Λ_R = [[x, y² - x²], [1, -x]]`, `Λ₁ = [[-x, x²], [-1, x]]`, the costate equations hold and
`H ≡ 0` on the edge `{u₀ = 0}` ("It can be checked", MCA:4647835), but
`H(u) = 6u₀y³/D` with `D = -3y⟨X, Z_u⟩ > 0` on the star domain (Lemma 3.3.4), so the edge is the
set of *minimizers* of the Hamiltonian over `U_T`, and "any measurable control function
`u_e(t) ∈ [-1/2, 1/2]` maximizes the Hamiltonian" fails. Reversing the sign of both costates,
which the linear costate equations allow when `λ_cost = 0`, gives `H(u) = -6u₀y³/D ≤ 0`, with
equality exactly on the edge (checked with sympy). With these signs the remark is true, and the
formalization proves it ([`remark8_1_6`](SmoothedPolygons/Ch8/EdgeAbnormal.lean#L214)). These abnormal costates belong to a two-parameter
family, the costates conormal to the edge submanifold of (8.1.1), which E55 and E57 meet again.

**E52. Lemma 8.2.1, §8.2 (TeX 7095–7126): a quantifier too broad, and a step left implicit.** The
lemma is stated "for all `X ∈ 𝔰𝔩₂(ℝ)` and all `Λ ∈ X^⊥`", but the control-dependent term
`H₂ = -⟨Λ, Z_u⟩/⟨X, Z_u⟩` of the Hamiltonian is defined only when `⟨X, Z_u⟩ ≠ 0` for every
`u ∈ U_T`, and for `X = 0` the statement has no meaning. The condition holds on the state space
(Lemma 3.3.4), where the lemma is used, and Lemma 7.3.1 needs it too (E26); the formalization
adds it (`hden` in [`lemma8_2_1`](SmoothedPolygons/Ch8/SingularLocus.lean#L586)). In the proof, the step from the independence of the control to
`Λ = 0` is one sentence, "The value of `H₂` must then be zero, and `Λ` must lie in the orthogonal
complement `{0}` of the entire tangent space" (TeX 7117–7119). What it needs is that the linear
form `ν = T*Φ(-Λ)` (Theorem 6.8.2), constant on the velocities `f(z; u)`, `u ∈ U_T`, whose affine
hull is the tangent space, vanishes on their span, the whole tangent space; the formalization
fills the step so.

**E53. Lemma 8.2.2 and Theorem 8.2.3, §8.2 (TeX 7128–7216): the Hamiltonian at one time, and a
closed interval.** The proof of Lemma 8.2.2 uses `H = 0` at the time `t₀` where `Λ_R(t₀) = 0`:
"The maximum principle states that the Hamiltonian vanishes identically along the lifted
extremal" (TeX 7140–7141). The maximum principle gives `H = 0` only almost everywhere (Section 6),
and `t₀` is a single time. It holds there by continuity: the control-dependent term
`-⟨Λ_R, Z_u⟩/⟨X, Z_u⟩` tends to `0` with `Λ_R`, uniformly in `u ∈ U_T`, and the rest of `H` is
continuous; the book does not say so. The proofs of Theorem 8.1.4 (TeX 6866–6869, at a zero of
`λ₂`; E49) and Theorem 8.3.1 (TeX 7533–7535; E56) take the same step, and the formalization
proves the vanishing at the given time by this continuity in each case ([`eqn_edge_zero`](SmoothedPolygons/Ch8/EdgeBangBang.lean#L342),
[`lemma8_2_2`](SmoothedPolygons/Ch8/SingularLocus.lean#L783), [`theorem8_3_1`](SmoothedPolygons/Ch8/FiniteBangBang.lean#L1288)). The
nontriviality of the costate that the lemma then uses is E21's. The proof of Theorem 8.2.3 assumes
`Λ_R ≡ 0` on the closed interval `[t₁, t₂]` (TeX 7189), while the statement assumes it on
`(t₁, t₂)`; by continuity the two are the same ([`theorem8_2_3`](SmoothedPolygons/Ch8/SingularLocus.lean#L924)).

**E54. Theorem 8.2.6, §8.2 (TeX 7259–7298): a converse argued by necessary conditions, and two
typos.** "Conversely, the lifted trajectory attached to a multi-curve of circular arcs is a
Pontryagin extremal singular subarc" is argued by deriving what a lift must satisfy (the control
is the centre of `U_T`, `Λ_R = 0` by Lemma 8.2.1, `Λ₁ = (3/2)λ_cost J` by Lemma 8.2.2), not by
exhibiting one. A lift exists: `λ_cost = -1`, `Λ₁ = -(3/2)J`, `Λ_R = 0` solve the costate
equations, with `H ≡ 0` and a nontrivial reduced costate, and the formalization exhibits it
([`theorem8_2_6`](SmoothedPolygons/Ch8/SingularLocus.lean#L1022)). In the proof, `g' = Xg` (TeX 7288) should be `g' = gX`, and
"Lemma~\ref{thm:circle-singular}" (TeX 7290) refers to Theorem 8.2.3.

**E55. Theorem 8.2.7, §8.2 (TeX 7300–7391): the proof covers one kind of singular subarc; slips in
the second variation.** The theorem says that "the global minimizer of the Reinhardt problem does
not contain any singular subarcs", and by Definition 6.2.1(3) these include the intervals on
which the maximizers of the Hamiltonian form an edge of `U_T` at every time. The proof ("The
previous theorem shows that the singular subarc comes from a multi-curve of circular arcs")
covers only the subarcs on which the Hamiltonian does not depend on the control, through Theorem
8.2.6, and shows by a second variation that a circular arc is not a local minimizer. The
authors' comments leave the edge case to the edge control problem: "Theorem is only true if we
include secondary edge optimal control problem" (TeX 7300–7302), "We say Reinhardt problem here
rather than Reinhardt control problem because we want to include the edge control problem" (TeX
7312–7313), and Chapter 1 (TeX 806–821). With the user's approval, the formalization states the
theorem in this reading ([`theorem8_2_7`](SmoothedPolygons/Ch8/NoSingularArcs.lean#L375)): on an interval where the control lies in an edge, the
minimizer's edge arc has edge costates (Proposition 8.1.3), none of which has a singular subarc of
the edge problem (by the argument of Theorem 8.1.4: on such a subarc `λ₂ ≡ 0`, and (8.1.8) makes
`x²` constant, against `x' = y > 0`); on an interval no subinterval of which has the control in an
edge, no lift is a singular subarc (the circle argument, after a localization: near a time where
`Λ_R ≠ 0` the maximizers on a singular subarc are one edge, by Lemma 8.2.1, and the control lies
in it). For normal lifts the theorem holds as printed
([`not_isSingularSubarc_of_isReinhardtMinimizer_of_isNormalExtremal`](SmoothedPolygons/Ch8/NoSingularArcs.lean#L418)): on an edge interval, the
Reinhardt costate pulled back to the edge submanifold of (8.1.1) and shifted by
`(3/2)λ_cost d(s + x)` is a costate of the edge problem with the same Hamiltonian
([`IsExtremalOn.isEdgeProblemExtremal_edgePullback`](SmoothedPolygons/Ch8/EdgePullback.lean#L870)), so a singular subarc there would be one of
the edge problem. For abnormal lifts the printed statement is open, neither proved nor refuted.
Along every edge arc there is a two-parameter family of abnormal costates conormal to the edge
submanifold of (8.1.1), which contains those of Remark 8.1.6 with the signs of E51, and whose
pull-back vanishes; excluding a global abnormal lift of the minimizer that is conormal on some
interval needs an argument the book does not give. No counterexample is known, and Theorem 16.3.1
does not depend on it (E60). Two other readings are not provable. Reading "elsewhere" as "on an
interval on which the control does not lie in a single edge" brings the abnormal case back (the
control may alternate between the vertices of the edge `{u₀ = 0}` and then stay at the third
vertex, with a lift conormal to one edge submanifold and then to another). Reading singularity
at a time `t` of an edge interval through *some* edge costate on *some* edge interval containing
`t` makes every edge arc with `x > 0` singular: on an arc with `u_e ≡ ½`, the covector
`(λ₁, λ₂, λ₃) = (0, 0, x(t)²)` with `λ_cost = -1` at `t`, continued by (8.1.7), has
`λ₂(t) = λ₂'(t) = 0` and `λ₂''(t) = -4x(t)/y(t) < 0`, so it is an edge costate near `t` whose
Hamiltonian does not depend on the control at `t`.
The second variation has slips. `cost(g₀) = π` (TeX 7382) holds only on an interval of length
`π/3`; on `[t₁, t₂]` the arc costs `3(t₂ - t₁)`. The condition "`ψ₁'(t) > 0` and `ψ₂'(t) < 0` on
their common support" (TeX 7376–7378) cannot hold literally for smooth nonnegative functions with
compact support (where `ψᵢ` vanishes, so does `ψᵢ'`); it is read on the interior of the overlap
of the supports, which is what the sign of `ψ₁'ψ₂ - ψ₁ψ₂'` needs. `σ_i = g_s e_i` (TeX 7385) should
be `g_s s_i*`. The admissibility of the competitor is asserted in two sentences (TeX 7384–7390).
The formalization follows the book's route ([`exists_lt_reinhardtCost_of_circleArc`](SmoothedPolygons/Ch8/CircleVariation.lean#L1209)). With
`L = t₂ - t₁` and `ρ = |ψ|`, the cost of the deformed arc is exactly
`3L - 3∫₀ᴸ (sinh(sρ)/ρ)²(ψ₁'ψ₂ - ψ₁ψ₂') dt`, whose second-order truncation is the book's
expansion, so the cost drops for every `s ≠ 0`; smallness of `s` is needed only for the
admissibility, which is carried out (positive curvatures, the reparameterization to `det X = 1`,
the control through Theorem 3.4.2, and the splice into the trajectory). In Remark 8.2.8, the
conditions of the three cases of `ψ₁` are commented out in the TeX (TeX 7397–7405).

**E56. Theorem 8.3.1, §8.3 (TeX 7448–7586): false as printed; one claim sketched.** (a) The
theorem says that if an edge-extremal extremal lifted trajectory on `[t₁, t₂]` does not meet
`𝒮_sing` at `t₀`, then "there exists an edge `{i, j}` and a neighborhood of `t₀` in `[t₁, t₂]` on
which `(X(t), Λ_R(t)) ∈ ⋃_{I ⊆ {i,j}} (T*O_J)_I`": the maximizers of the Hamiltonian lie in one
edge at every time of a neighbourhood of `t₀`. This is false. At a time `t₀` where `Λ_R(t₀) = 0`,
every control maximizes, and such times occur off `𝒮_sing` on edge-extremal extremals. A normal
example (checked numerically): `λ_cost = -1`, `X(0) = Φ(0.1 + 0.9i)`, `Λ_R(0) = 0`,
`Λ₁(0) = -(3/2)J + L` with `0 ≠ L ⊥ X(0)`; with `e_a`, `e_b` the vertices that maximize and
minimize `⟨[L, X(0)], P_u⟩`, the control `e_b` on `(-ε, 0)` and `e_a` on `(0, ε)` gives, for small
`ε`, an edge-extremal extremal that does not meet `𝒮_sing`, and all of `U_T` maximizes at `0`.
Reading the conclusion off `t₀`, or almost everywhere, does not save it: along an abnormal costate
conormal to the edge submanifold of `{u₀ = 0}` (the family of E51) with `Λ_R(t₀) = 0`, the control
`e₂` before `t₀` and `e₁` after gives
an edge-extremal extremal off `𝒮_sing` whose maximizers are the edge `{e₂, e₃}` before `t₀` and
the vertex `e₁` after, which no edge contains. The proof's claim (a) finds exactly this ("If the
set of maximizers is an edge when `t` has one sign, then the maximizer is the complementary vertex
of `U_T` when `t` has the other sign", TeX 7555–7557), which does not contradict the assumption of
its contrapositive; and it passes, through Theorem 8.1.4, to a conclusion about the control,
while that assumption is about the maximizers. With the user's approval, the formalization proves
the one-sided form ([`theorem8_3_1`](SmoothedPolygons/Ch8/FiniteBangBang.lean#L1288)): there are `ε > 0` and edges `k₋`, `k₊` such that the
maximizers lie in `k₋` at every time of `(t₀ - ε, t₀)` and in `k₊` at every time of
`(t₀, t₀ + ε)` (within `[t₁, t₂]`); both examples satisfy it. The form that the proof of Theorem
8.3.2 quotes, that the control lies in a single edge almost everywhere on a neighbourhood of
`t₀`, is true, and follows from the one-sided form with edge extremality and Theorem 8.1.4
([`IsExtremalOn.exists_ae_mem_controlEdge_of_isEdgeExtremalOn`](SmoothedPolygons/Ch8/FiniteBangBang.lean#L1349)): on each side the control is
eventually one vertex, and any two vertices lie in a common edge. Edge extremality, a hypothesis
of the theorem, is used only there (Section 5).
(b) Claim (b) is "a brief sketch" (TeX 7565–7575). It is carried out as a second-order expansion:
if `[Λ_{1,cost}(t₀), X(t₀)] = 0` and `W' = [Λ_{1,cost}'(t₀), X(t₀)] ≠ 0`, then
`Λ_R(t) = -(t - t₀)²W'/2 + o((t - t₀)²)`, with the same leading direction on both sides of `t₀`.
(c) Smaller points. "Edge-extremal \eqref{def:edge-extremal}" (TeX 7452) points to Definition
8.1.1, the edge control problem, and prints "(8.1.1)", the number of an equation; Definition
8.1.2, which has no label, is meant. "Reparameterizing by a time translation, we may assume that
`t₀ = 0`" (TeX 7472–7473) overlooks that `t₀` may be an end of `[t₁, t₂]`, where the Gronwall
step on a two-sided neighbourhood needs the functions beyond the end (the formalization extends
them by their value there). The proof uses `H = 0` at `t₀` (TeX 7533–7535; E53), the
nontriviality of the reduced costate (TeX 7583–7584; E21) and Corollary A.1.3 on both sides of
`t₀` (TeX 7539, 7572; E61), and "the hypothesis of the lemma" (TeX 7575) means the theorem's.

**E57. Theorem 8.3.2, §8.3 (TeX 7590–7605), and its restatement in Chapter 1 (TeX 851–856).** The
statement has no interval ("Consider a controlled extremal lifted trajectory"), and the proof uses
`[t₁, t₂]` without introducing it; "According to the theorem" means Theorem 8.3.1, quoted in its
form about the control (E56). The formalization states the theorem on a compact interval
([`theorem8_3_2`](SmoothedPolygons/Ch8/FiniteBangBang.lean#L1419)). Chapter 1 restates it as "Every Pontryagin extremal of the Reinhardt control
problem which does not meet the singular locus is given by a bang-bang control function with
finitely many switches", without edge extremality. For extremals on an interval this is false: by
Remark 8.1.6, with the signs of E51, every trajectory with an arbitrary measurable control in an
edge lifts to an abnormal extremal, which never meets `𝒮_sing` (its `Λ_R` never vanishes) and
need not be bang-bang (the midpoint of the edge as control, for instance). For normal extremals
the restatement follows from Theorem 8.3.2, since every normal extremal is edge extremal: the
pulled-back costate of E55 is an edge costate ([`IsNormalExtremal.isEdgeExtremalOn`](SmoothedPolygons/Ch8/EdgePullback.lean#L903),
[`IsExtremalOn.isEdgeExtremalOn_of_ne_zero`](SmoothedPolygons/Ch8/EdgePullback.lean#L895)), as a comment of the authors in the TeX expects ("a
normal extremal solution should also be edge extremal", TeX 6664–6666). Whether the restatement
fails for extremals with the boundary conditions of Problem 3.6.2 is not settled: the costates of
Remark 8.1.6 are tied to one edge and need not satisfy the transversality conditions. The
formalization states Theorem 8.3.2 as Chapter 8 does.

**E58. Remark 8.3.3, §8.3 (TeX 7610–7616): a disk that need not exist, and no proof.** The remark
says that a trajectory that is extremal and edge extremal and does not meet `𝒮_sing` "defines a
balanced disk `K(g, X) ∈ 𝔎_bal` whose boundary is a smoothed polygon, consisting of finitely many
straight edges and hyperbolic arcs". That the trajectory bounds a balanced disk is the converse of
Problem 3.6.2, which holds only for trajectories of winding number one (E15), and the book does
not show it for extremals. The formalization takes the disk as a hypothesis (a balanced pair with
`σ_j = g s_j*` and `σ_j(t + t_f) = σ_{j+1}(t)`); it exists for the global minimizer, whose cost
is below `7π/2`. The remark has no proof. Its content is Theorem 8.3.2 with the discussion of §7.2
(on an interval of constant vertex control, two of the state-dependent curvatures vanish, so two
pairs of the curves move along straight lines, TeX 5613–5621) and Lemma 3.1.8 (the third pair
moves along hyperbolic arcs whose asymptotes are those lines); the formalization proves it so
([`remark8_3_3`](SmoothedPolygons/Ch8/PolygonBoundary.lean#L877)), with the smoothed polygon defined as in the gloss of Theorem 16.3.1 (Section 6).

**E59. Lemma 8.3.4, §8.3 (TeX 7619–7670): a sign and a garbled display.** With
`P_i = Z_{e_i}/⟨J, Z_{e_i}⟩`, `Λ_R'''(0) = +6λ_cost[J, P₃]`, not `-6λ_cost[J, P₃]` (TeX 7648;
checked with sympy), and the display at TeX 7657–7660 lacks an `=` and the factor `λ_cost`. The
leading terms of the control-dependent term `-⟨Λ_R(t), P_i⟩` at `e₁`, `e₂`, `e₃` are
`(2√3, -2√3, 0)λ_cost t³`, opposite and nonzero at `e₁` and `e₂` as the book says, so the
conclusion is unaffected. The argument works on either side of the meeting time, which covers a
meeting at an end of the interval, the case that Theorem 16.3.1 needs ("A trajectory cannot reach
the singular locus with finitely many switches", TeX 12817–12819). The formalization proves the
lemma ([`lemma8_3_4`](SmoothedPolygons/Ch8/VertexControl.lean#L662)) with Taylor expansions with remainder in place of "The solutions are
analytic" (TeX 7637), and treats the three vertices alike where the book treats `e₃`, "(say)".

**E60. Theorem 16.3.1, §16.3 (TeX 12789–12833): the set of meeting times is not handled; the last
step rests on Chapters 13–16.** (a) After Proposition 8.1.3 and Theorem 8.3.2 (finite bang-bang
away from `𝒮_sing`), Theorem 8.2.7 ("A trajectory cannot remain on the singular locus for any
positive interval of time") and Lemma 8.3.4 ("A trajectory cannot reach the singular locus with
finitely many switches"), the proof goes on: "The proof then reduces to the consideration of a
trajectory such that the infinite sequence of switching points has a subsequence tending to the
singular locus" (TeX 12821–12823). It does not handle the set of times at which the lift meets
`𝒮_sing`, which is closed but may a priori be infinite and contain `0`. The formalization repairs
the step. The meeting set has empty interior (Theorem 8.2.7 in its part without edges, through
Theorem 8.2.3: on an interval of `𝒮_sing` the control is the centre of `U_T`); a meeting at `0`
gives one at `T`, by the transversality conditions and `R⁻¹JR = J`; take a meeting time `z > 0`,
a time `p < z` off the meeting set, and the first meeting time `d` after `p`. On `(p, d)` the
control is bang-bang with finitely many switches on every compact subinterval (Theorem 8.3.2).
Either the switching times accumulate at `d`, the configuration that the book excludes by
Theorems 16.4.1 and 14.4.1, or the control is one vertex just before `d`, which Lemma 8.3.4,
applied at the end of an interval, excludes (E59). (b) The second sentence ("In particular, the
minimizer `K_min` of the Reinhardt problem is a finite-sided smoothed polygon …") follows from the
first by Remark 8.3.3 ("A bang-bang trajectory with finitely many switches is a polygon with
rounded corners", TeX 12807–12808), with the identification of the minimizers with `K_min` (E47)
and Lemma 2.2.5 for "no corners"; the book takes the passage from the control problem to `K_min`
for granted. (c) "The global minimizer" and "the minimizer `K_min`" presuppose uniqueness; the
theorem is formalized for every global minimizer and every `K_min` (E47). The formalization proves
the theorem conditionally, on one named hypothesis, [`NoChatteringIntoSingularLocus`](SmoothedPolygons/Ch16/MahlerFirst.lean#L107): the
consequence of Theorems 16.4.1 and 14.4.1 that the last step uses, that the switching times of a
Pontryagin extremal do not accumulate, from the left, at a time where its lift meets `𝒮_sing`
([`theorem16_3_1`](SmoothedPolygons/Ch16/MahlerFirst.lean#L343); Sections 2 and 9). Without the hypothesis it proves the first sentence on every
interval on which the lift avoids `𝒮_sing`
([`isFiniteBangBang_of_isReinhardtMinimizer_of_not_mem_singularLocus`](SmoothedPolygons/Ch16/MahlerFirst.lean#L165)). (The proof also has a typo,
"is is an extremal", TeX 12812.)

**E61. Corollary A.1.3, Appendix A.1 (TeX 13134–13142): stated for `t ≥ 0`, applied on both sides
of `0`; no proof.** The corollary is stated on `[0, t₁]`, with the conclusion "`x(t) = O(tⁿ)` for
`t` nonnegative", but Lemma 8.1.5 (TeX 7008) and the proof of Theorem 8.3.1 (TeX 7539, 7572) apply
it on `(-t₁, t₁)`, where the book's Landau notation is two-sided (TeX 6903–6907). The case `t < 0`
follows by applying the corollary to `t ↦ x(-t)` ([`corollaryA_1_3_two_sided`](SmoothedPolygons/AppA/Gronwall.lean#L76)). The corollary has
no proof; it follows from Lemma A.1.1 with constant data, and the formalization proves it so,
through the integral form of Gronwall's inequality in the OptimalControl package
([`corollaryA_1_3`](SmoothedPolygons/AppA/Gronwall.lean#L46)). The hypothesis that `n` is positive is not needed (Section 5), and
`∫₀ᵗ x(t) dt` uses `t` both as the bound and as the variable of integration.

**E62. §13.2 and Lemma 13.2.6 (TeX 10740–10753, 10972–11009): the first control, promised well
defined, argued only as a necessary condition; the Hamiltonian asserted constant.** The book
defines the first control of `z⁰ ≠ 0` as "the optimal control starting at switching time `t = 0`
until the first positive switching time `t_sw > 0`" and defers its justification: "It will become
clear from the proof of Lemma 13.2.6 that `t = 0` is an isolated zero of the relevant switching
function, and that the notion of first control is well-defined" (TeX 10747–10753). That proof
shows only that a first control, if one exists, is the lexicographic maximizer with the tie rule,
and it treats the control as constant on `(0, ε)`. Three facts are asserted or left implicit:
that the lexicographic maximizer is optimal on some `[0, ε]`; that every extremal with a
measurable control from `z⁰ ≠ 0` follows it up to `t_sw`; and that the Hamiltonian is constant
along such extremals ("if `u` is chosen according to the maximum principle, then `H_F` is
constant along trajectories", TeX 10741–10742). All three hold. The formalization proves the
first two with the book's Taylor expansion ([`lemma13_2_6`](SmoothedPolygons/Ch13/FirstControl.lean#L539), [`TriFuller.IsFirstControl.unique`](SmoothedPolygons/Ch13/FirstControl.lean#L330),
[`TriFuller.eq_flow_of_maxCondition`](SmoothedPolygons/Ch13/Extremals.lean#L424); Section 7) and the third by absolute continuity
([`TriFuller.hamMax_eq_of_maxCondition`](SmoothedPolygons/Ch13/Extremals.lean#L140)). It reads `t_sw` as the time at which the first control
stops being optimal: at a double root of a switching function at which the control stays optimal,
the extremal is unique and does not switch, so such a tangency is not a switching time (Section
6).

**E63. Lemmas 13.2.1–13.2.3 and 13.2.5, §13.5 (TeX 10794–10906, 11246–11260): symmetries applied
outside their hypothesis.** Lemmas 13.2.1–13.2.3 (rescaling, rotation by `ζ`, time reversal) are
stated for solutions that satisfy the maximum condition and `H_F = 0` ((13.2.5), (13.2.6)). The
proof of Lemma 13.2.5 ("The lemma follows from the time-reversal symmetry (Lemma 13.2.3)", TeX
10905–10906) and the descent of `F` to `(ℝ_{>0} × Ξ)_𝒲/V_T` and to `F_ang` ("By the equivariance
of the construction", "By the scaling symmetries", TeX 11246–11260) apply them at every `z⁰`,
where `H_F` need not vanish. The substitutions never use `H_F = 0`, and the formalization redoes
them for constant controls ([`TriFuller.tau_flow_neg`](SmoothedPolygons/Ch13/Symmetry.lean#L172), [`TriFuller.ham_tau`](SmoothedPolygons/Ch13/Symmetry.lean#L192),
[`TriFuller.poincare_smul`](SmoothedPolygons/Ch13/PoincareMap.lean#L293), [`TriFuller.poincare_scale`](SmoothedPolygons/Ch13/PoincareMap.lean#L327); Section 7).

**E64. Corollary 13.2.7, Lemma 13.2.8 and the remark after it, §13.2 (TeX 11011–11067): slips.**
In the bound of the proof of Corollary 13.2.7 (TeX 11039–11040) the first `<` should be `≤`:
equality holds when `t = 10r` and `|z_j| = r^j`. The final strict inequality,
`√3 Σ 10^{k-3}/k! < 1/(4√3)`, holds, so the corollary stands ([`corollary13_2_7`](SmoothedPolygons/Ch13/FirstControl.lean#L750)). Lemma 13.2.8
does not need its hypotheses `z₃⁰ ∈ ℝ_{≤0}` and `z⁰ ≠ 0`: the two cubics differ only in their
`t³` terms, whose sum is `RR(ζ - ζ², -i(ζ - ζ²))t³/(6√3) = 0` ([`lemma13_2_8`](SmoothedPolygons/Ch13/FirstControl.lean#L885), which keeps them as
printed; Section 5). The corollary after the lemma (TeX 11063–11067: switching back and forth
between `ζ` and `ζ²` happens at consecutive roots of one cubic, and after its largest root the
control switches to `1`) is stated without proof and is not used later; it is not formalized
(Section 9).

**E65. Lemma 13.3.2, §13.3 (TeX 11108–11156): a gap and two typos.** The proof treats two cases,
each on all of `[0, t₂]`: the Hamiltonian independent of the control in `U_T` (the whole triangle
maximizing), and independent of the control in the edge `[ζ, ζ²]` "(say)" (TeX 11136–11155). The
hypothesis lets the maximizing face change with `t`, which the two cases do not cover. The lemma
is true, and the formalization repairs the proof along its lines ([`lemma13_3_2`](SmoothedPolygons/Ch13/SingularLocus.lean#L710); Section 7): a
maximizing face that is not a vertex means `z₃(t) ∈ 𝒲`; if `z₃(t₀) ≠ 0`, then by continuity
`z₃` stays on one open ray of `𝒲` on an interval around `t₀`, where the maximizing face is one
edge and the book's second case gives a contradiction; so `z₃ ≡ 0`, and the book's first case
applies. On the ray `ℝ_{<0}c` the argument uses `RR(z₃, ic)`, which for `c = 1` is the book's
`RR(z₃, ζ - ζ²)` divided by `√3`. The statement types `z_j : [t₁, t₂] → ℂ³` for `ℂ` (TeX
11109), and the proof writes `u(0) = u'(0) = u''(0) = 0` for the initial conditions of `u₃` (TeX
11122).

**E66. §13.4 (TeX 11161–11177): "diffeomorphism".** The book calls the identification
`ℂ³ ∖ 0 ↔ ℝ_{>0} × Ξ`, `z ↦ (φ(z), (z₁/φ, z₂/φ², z₃/φ³))`, a diffeomorphism (TeX 11171). The
function `φ⁶ = |z₁|⁶ + |z₂|³ + |z₃|²` is `C²` but not `C³` where `z₂ = 0` (the term `|z₂|³`), so
`Ξ` is a `C²` hypersurface and the identification is a `C²` diffeomorphism, smooth only off
`{z₂ = 0}`. The formalization states it as a homeomorphism ([`TriFuller.blowup`](SmoothedPolygons/Ch13/Blowup.lean#L313)) with `φ` of class
`C²`, and smooth off `{z₂ = 0}` ([`TriFuller.contDiffOn_weightedNorm`](SmoothedPolygons/Ch13/Blowup.lean#L340),
[`TriFuller.contDiffOn_weightedNorm_infty`](SmoothedPolygons/Ch13/Blowup.lean#L349)). The book uses the identification as coordinates, and
its smoothness only near `q_out` (Lemma 13.5.5), where `z₂ ≠ 0`.

**E67. §13.5 and Lemma 13.5.2 (TeX 11236–11251, 11298–11387): silent steps, a garbled display,
an omitted verification.** (a) `F` is well defined on the section because `0 < t_sw < 10φ(z⁰)`
(Lemma 13.2.6, Corollary 13.2.7), `z(t_sw) ≠ 0` (Lemma 13.3.1) and `z₃(t_sw) ∈ 𝒲`; the definition
cites none of this. The formalization proves all three: the bound
([`TriFuller.firstSwitchTime_lt`](SmoothedPolygons/Ch13/PoincareMap.lean#L214)), `z(t_sw) ≠ 0` for every `z⁰ ≠ 0` and not only on the section
([`TriFuller.poincare_ne_zero`](SmoothedPolygons/Ch13/PoincareMap.lean#L223)), and the landing on the walls. (b) The display of the maximum
principle at `t = 0, t_sw` (TeX 11363–11370) uses a one-argument `RR`, drops a factor `ū`, and
names a dummy `ζ₂` that clashes with `ζ²`. Its final condition, `z₃⁰ūζ₁² ∈ ℝ_{≤0}`, is right, but
it follows only when `ζ₁ ≠ 1`: for `ζ₁ = 1` the conditions at `0` and at `t_sw` coincide and do not
give it. The case `ζ₁ = 1` is impossible because the control switches at `t_sw`, while by
equivariance the control after `t_sw` would be `ζ₁u = u`; the book does not say so. Three things
are asserted without proof: the passage from the final condition to the three cases `(r, ζ₁)`,
that `r_s` and `1/r_s` are the only real roots of the palindromic polynomial
([`TriFuller.rScalePoly_eq_zero_iff`](SmoothedPolygons/Ch13/RScale.lean#L147)), and the coordinates (13.5.1), which are computer-generated.
(c) The proof does not check that `t_sw` is the first switching time of (13.5.1), that is, that
the control `ζ` stays optimal on `(0, t_sw)`, nor that `H_F = 0` there, which the statement
asserts; along (13.5.1), `H_F = (r² + r + 1)P(r)/(9(r + 1)²(1 + r³ + r⁶))`. Both hold, and the
formalization proves them exactly ([`TriFuller.firstSwitchTime_qOutCart`](SmoothedPolygons/Ch13/FixedPoints.lean#L496),
[`TriFuller.hamMax_qOutCart`](SmoothedPolygons/Ch13/FixedPoints.lean#L526); Section 7).

**E68. Lemma 13.5.5, §13.5 (TeX 11433–11453): a numerical proof, and two steps not argued.** The
proof gives no chart, matrix or eigenvalues: "An explicit calculation of the eigenvalues of the
Jacobian matrix in terms of local coordinates centered at `q_out` gives the result. Numerically,
the three eigenvalues have absolute value less than `0.1`. The calculations were made in
Mathematica." It does not argue that `F_ang` is `C¹` near `q_out`, which holds by the implicit
function theorem since `t_sw` is a simple root of the switching function there; nor that
`τ ∘ F_ang` is an involution near `q_out` and `q_in`, which "the second assertion follows from
the first, because `q_in` is obtained by time reversal from `q_out`" needs, and which holds because
the nearby points are genuine switching points (Lemma 13.2.5). The lemma is true. The
formalization fixes the chart `Re z₁ = -1`, `z₃ ∈ ℝ_{<0}`, `H_F = 0`, computes the Jacobian
exactly in `ℚ(√3, r_scale)` ([`TriFuller.jacobianOut`](SmoothedPolygons/Ch13/Jacobian.lean#L136)), certifies by sign changes of its
characteristic polynomial that its eigenvalues (`≈ -0.0800`, `-0.0081`, `0.00065`) lie in
`(-0.1, 0.1)` ([`TriFuller.norm_lt_of_aeval_charpoly_jacobianOut_eq_zero`](SmoothedPolygons/Ch13/Jacobian.lean#L1919)), and proves linearized
stability for maps and the time-reversal step ([`lemma13_5_5`](SmoothedPolygons/Ch13/Stability.lean#L281); Sections 2 and 7).

**E69. Remark 13.5.4, §13.5 (TeX 11402–11428): stated without proof.** The remark interprets
`q_fix = (1, -i/2, -1/2) mod 𝒢`, the fixed point for `(r, ζ₁) = (1, ζ)` in the proof of Lemma
13.5.2, as the limit, by the procedure of §14.2, of the one-parameter family of extremals of §7.5
that contains the smoothed `(6k+2)`-gons. This rests on a Mathematica computation (`MCA:zfix1`)
and a forward reference, is not used later, and is not formalized. The verifiable part holds and
is proved ([`remark13_5_4`](SmoothedPolygons/Ch13/FixedPoints.lean#L732)): from `q_fix` the first control is `ζ²`, `t_sw = √3`,
`F(q_fix) = ζ q_fix`, and `H_F⁺(q_fix) = 3/4`, so that, as the remark says, "the Fuller-system
Hamiltonian is not zero at `q_fix`".

## 4. Missing hypotheses

| Where | Missing hypothesis | Counterexample without it | In the formalization |
| --- | --- | --- | --- |
| Theorem 3.1.4(3) | `σ_j'` Lipschitz (the standing assumption of §2.4, through Lemma 2.4.3) | unit disk, `σ_j(t) = Rot(t + t^{3/2}) s_j*`, `X = (1 + (3/2)√t)J` | hypothesis of [`theorem3_1_4_lipschitz`](SmoothedPolygons/Ch3/StateDynamics.lean#L283) (approved by the user) |
| Lemma 3.1.8 | the curves `σ_j` are regular, `σ_j' ≠ 0` (§2.4, TeX 1945–1946: "a regular `C¹` curve") | the square `[-λ, λ]²`, `λ² = √3/2`: `σ₂ = (-λ, 0)` constant while `σ₁`, `σ₃` slide along the parallel lines `y = ±λ` (E34) | hypothesis `hreg` of [`lemma3_1_8`](SmoothedPolygons/Ch3/HyperbolicArc.lean#L772) (approved by the user) |
| The converse of Problem 3.6.2 (an admissible trajectory bounds a balanced disk whose area is its cost), used in §6.1 (TeX 4579) | the curve `g s₀*` winds once around the origin ([`IsWindingOne`](SmoothedPolygons/Ch6/Winding.lean#L82)), as it does when the cost is below `7π/2` | the unit circle traversed seven times: `X ≡ J`, `u ≡ (1/3, 1/3, 1/3)`, `t_f = 7π/3`, cost `7π` (E15) | hypothesis `hw` of [`exists_isBalancedPair_of_isReinhardtAdmissible`](SmoothedPolygons/Ch6/AdmissibleDisk.lean#L937) |
| Lemma 4.2.3 | `X ≠ 0` | `X = 0`: `T_0 O_0 = 0` but `𝔰𝔩₂/ℝ·0` has dimension 3 | hypothesis of [`lemma4_2_3`](SmoothedPolygons/Ch4/AdjointOrbit.lean#L432) |
| Theorem 6.1.1 (Filippov), "an optimal control exists" | the velocity sets extended by the cost, `{(f(q, u), φ(q, u)) \| u ∈ U}`, are convex (the book's hypothesis when `φ` does not depend on `u`) | on `ℝ`, `q' = uψ(q)`, `U = [-1, 1]`, a bump `ψ` with `ψ = 1` on `[-1, 1]`: `∫₀¹ (q² + 1 - u²) dt` from `q(0) = 0` to `q(1) = 0` has infimum `0` and no minimizer (E35) | hypothesis of the second part of [`External.filippov`](External/Filippov.lean#L153) (approved by the user) |
| Lemma 7.3.1 | `⟨X, Z_u⟩ ≠ 0` on `U` (used by the proof, TeX 5792) | a segment `U` of the plane `u₀ + u₁ + u₂ = 1` crossing the line where `⟨X, Z_u⟩ = 0`: the Hamiltonian is undefined there | hypothesis `hden` of [`lemma7_3_1`](SmoothedPolygons/Ch7/Faces.lean#L49) |
| Lemma 8.2.1 | `⟨X, Z_u⟩ ≠ 0` for every `u ∈ U_T` (true on the state space, Lemma 3.3.4) | `X = 0`, or any `X` with `⟨X, Z_u⟩ = 0` for some `u ∈ U_T`: the control-dependent term `H₂` is undefined there (E52) | hypothesis `hden` of [`lemma8_2_1`](SmoothedPolygons/Ch8/SingularLocus.lean#L586) |
| Theorem 8.3.2 as restated in Chapter 1 (TeX 851–856) | the trajectory is edge extremal, as in Chapter 8 | an abnormal extremal of Remark 8.1.6 (with the signs of E51) whose control is the midpoint of an edge: it never meets `𝒮_sing` and is not bang-bang (E57) | hypothesis `hedge` of [`theorem8_3_2`](SmoothedPolygons/Ch8/FiniteBangBang.lean#L1419), the statement of Chapter 8 |

## 5. Redundant hypotheses

Each hypothesis in the table is omitted from the Lean statement, which is therefore more general
than the book's. The Challenge statements keep the book's hypotheses.

| Result | Hypothesis that is not needed | Why |
| --- | --- | --- |
| Theorem 3.1.4, parts (1), (2) ([`theorem3_1_4`](SmoothedPolygons/Ch3/StateDynamics.lean#L258)) | `K` a convex disk, `σ` regular, `σ` parameterizes `∂K` | the proof differentiates `σ_j = g s_j` and uses `det g = 1`; it holds for every `C¹` multi-curve induced by a curve in `SL₂(ℝ)` |
| Proposition 3.1.9 ([`proposition3_1_9`](SmoothedPolygons/Ch3/StateDynamics.lean#L570)) | `σ₀` parameterized by arclength | the proof uses that the tangents are Lipschitz (Definition 2.4.7, item 2), not the normalization |
| Corollary 3.1.10 ([`corollary3_1_10`](SmoothedPolygons/Ch3/StateDynamics.lean#L679)) | the same (the standing assumption of TeX 2157, not printed in the statement) | it applies Proposition 3.1.9 |
| Lemma 3.3.1 ([`lemma3_3_1`](SmoothedPolygons/Ch3/ControlSets.lean#L208)) | `g'` Lipschitz | the hypothesis `κ_j ≥ 0` almost everywhere already presupposes that `X'` exists almost everywhere; the first proof (if `κ₀ = κ₁ = 0` then `κ₂ = √3 det X/ρ₀(X) > 0`) uses only `tr X' = 0` where `X'` exists. (The formal `κ_j` is defined everywhere, through [`derivEntrywise`](Basic/Analysis/Calculus/MatrixEntrywise.lean#L113).) |
| Theorem 5.0.2 ([`theorem5_0_2`](SmoothedPolygons/Ch5/Theorem502.lean#L253)) | `K` in circle representation, `g(0) = I₂` (the boundary trajectory of Problem 3.6.2, and the paragraph after the statement, TeX 3991–3994) | the proof re-centers `K` at the time `t₀` where the trajectory leaves `𝔥**` ([`IsBalancedPair.recenter`](SmoothedPolygons/Ch5/Recenter.lean#L147), E45), and the re-centered disk `g(t₀)⁻¹K` is in circle representation whatever `g(0)` is |
| Corollary 6.5.4 ([`corollary6_5_4`](SmoothedPolygons/Ch6/Hamiltonian.lean#L477)) | `Z = Z_u` is a control matrix | the Lean statement takes any matrix `Z` with `⟨X, Z⟩ ≠ 0`: the quotient rule does not use the form of `Z_u` |
| Theorem 6.8.2 ([`theorem6_8_2`](SmoothedPolygons/Ch6/HalfPlane.lean#L164)) | `Λ_R` traceless | `Λ_R` enters only through its trace form with traceless matrices |
| Lemma 7.1.2 ([`lemma7_1_2`](SmoothedPolygons/Ch7/ConstantControl.lean#L82)) | `u ∈ U_T` | the proof uses only that `P` is constant along the trajectory (Lemma 7.1.1), which holds for every constant `u` |
| Lemma 7.3.1 ([`lemma7_3_1`](SmoothedPolygons/Ch7/Faces.lean#L49)) | the control set lies in the plane `u₀ + u₁ + u₂ = 1` | `Z_u` is linear in `u`, so `H` is a linear-fractional function of `u` on any compact convex set on which `⟨X, Z_u⟩ ≠ 0` (hypothesis `hden`, E26) |
| Gruber, Cor. 30.1 ([`External.gruber_corollary_30_1`](External/Gruber.lean#L320), cited in Definition 2.1.2) | the translates form a packing | the lattice-point count bounds the sums of the areas of the translates meeting a disk, overlaps counted with multiplicity |

Nine Lean statements keep hypotheses that their proofs do not use, because the book or the source
states them:
- Lemma 3.1.8 ([`lemma3_1_8`](SmoothedPolygons/Ch3/HyperbolicArc.lean#L772)) keeps `hcover`, that the arcs of `σ` cover `∂K` (part of "the
  boundary is parameterized by `σ`"); of that hypothesis the proof uses only `hbd`, that the curves
  lie on `∂K`.
- Proposition 6.4.1 ([`proposition6_4_1`](SmoothedPolygons/Ch6/LeftInvariant.lean#L91)) keeps the nondegeneracy, symmetry and invariance of the bilinear
  form: nondegeneracy is what makes `p ↦ ⟨p, ·⟩` the identification `𝔤 ≅ 𝔤*`, and the identity
  `H = ⟨p, f(e, u)⟩` holds for every bilinear form.
- Lemma 8.1.5 ([`lemma8_1_5`](SmoothedPolygons/Ch8/EdgeLandau.lean#L504)) keeps the hypothesis that the state stays in the state space of the
  edge problem (`y > 0`, `|x| < 1/√3`) on all of `(-t₁, t₁)`, as the book's solutions of the edge
  problem do; the proof works on a smaller interval around `0`, where continuity gives it.
- Theorem 8.3.1 ([`theorem8_3_1`](SmoothedPolygons/Ch8/FiniteBangBang.lean#L1288)) keeps edge extremality, which the book uses only to pass from the
  maximizers to the control through Theorem 8.1.4; the one-sided form about the maximizers does
  not need it, and the form about the control, its corollary, does (E56).
- Lemma 13.2.8 ([`lemma13_2_8`](SmoothedPolygons/Ch13/FirstControl.lean#L885)) keeps `z⁰ ≠ 0` and `z₃⁰ ∈ ℝ_{≤0}`: the identity
  `χ_{ζ,ζ²} + χ_{ζ²,ζ} = 0` holds for every `z⁰`, since the two cubics differ only in their `t³`
  terms, which cancel (E64).
- Lemma 13.3.1 ([`lemma13_3_1`](SmoothedPolygons/Ch13/SingularLocus.lean#L150)) is stated, as printed, for the constant control given by the
  maximum principle (the first control) and `z₃⁰ ∈ 𝒲`; the proof uses the wall condition but not
  that the control is the first control, and holds for every vertex control `u ∈ V_T`.
- Lemma 13.3.2 ([`lemma13_3_2`](SmoothedPolygons/Ch13/SingularLocus.lean#L710)) keeps "the set of controls maximizing the Hamiltonian is a face":
  the maximizers of `v ↦ H_F(z, v)`, which is affine in `v`, always form a face of `U_T`, and the
  proof uses only that they are not a single vertex.
- Corollary A.1.3 ([`corollaryA_1_3`](SmoothedPolygons/AppA/Gronwall.lean#L46), and its two-sided form) keeps "`n` a positive integer": the
  bound holds for `n = 0` as well (E61).
- Filippov's theorem ([`External.filippov`](External/Filippov.lean#L153)) keeps the source's standing assumptions that `f` is smooth
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
- **The compactification (Chapter 5).** Points of the upper half-plane are pairs `(x, y)` with
  `y > 0`, as in the star domain ([`starDomain`](SmoothedPolygons/Ch4/StarDomain.lean#L22)); a real `2 × 2` matrix acts by its linear fractional
  transformation written in coordinates ([`lftAct`](SmoothedPolygons/Ch5/Compactification.lean#L110)), and the reflection `S` of §4.6 by
  `(x, y) ↦ (-x, y)` ([`reflAct`](SmoothedPolygons/Ch5/Compactification.lean#L117)). The horoballs and the "half-planes" (regions bounded by a line or
  a circle) of Definition 5.0.1 are open sets of such pairs ([`horoballAtInfty`](SmoothedPolygons/Ch5/Compactification.lean#L125),
  [`edgeHalfPlane`](SmoothedPolygons/Ch5/Compactification.lean#L129) and their images under `R` and `R²`), `𝔥**` is [`truncatedStarDomain`](SmoothedPolygons/Ch5/Compactification.lean#L135), and
  [`truncatedStarDomain_eq`](SmoothedPolygons/Ch5/Compactification.lean#L536) writes it by explicit inequalities. The fundamental domain of the proof of
  Theorem 5.0.2 is read as the sector `{x ≥ 0, (x - 1/√3)² + y² ≥ 4/3}` ([`fundamentalDomain`](SmoothedPolygons/Ch5/Compactification.lean#L143);
  E40, E45).
- **Lemmas 5.0.3–5.0.5 and Theorem 5.0.6.** The hexagon `H_K(z)` is given by its vertices `p_j`
  (eqn:hex-vertex with `det X = 1`, [`hexVertex`](SmoothedPolygons/Ch5/Hexagon.lean#L105)) and the points `q_j` of TeX 4131 ([`hexExtVertex`](SmoothedPolygons/Ch5/Hexagon.lean#L111));
  areas are Lebesgue measure. The exterior triangle `T₂^ext = △p₀q₀p₁` is represented by its
  reflection `△p₃q₃p₄`, which has the same area ([`outerTriangle`](SmoothedPolygons/Ch5/Hexagon.lean#L122)). "The critical hexagon" of `K`
  in Lemma 5.0.3 and Theorem 5.0.6 is read as a centrally symmetric hexagon of least area
  containing `K` ([`IsLeastAreaHexagon`](SmoothedPolygons/Ch2/Reinhardt.lean#L66), the critical hexagons of §2.2), which Theorem 2.3.9 identifies
  with the critical hexagon of Definition 2.3.8 (E42). "`z` constructed from the boundary
  parameterization of `K` at the multi-point `{s_j*}`" is read as `σ_j = g s_j*` with
  `g(0)⁻¹g'(0) = Φ(z)`.
- **Lemma 5.0.7 and Theorem 5.0.2.** `area_i` and `δ` are functions of pairs `(x, y)`
  ([`areaFn`](SmoothedPolygons/Ch5/Hexagon.lean#L138), [`densityBound`](SmoothedPolygons/Ch5/Hexagon.lean#L144)), and `I_i area_i` is `area_i` times the indicator of `h_i` ([`hRegion`](SmoothedPolygons/Ch5/Hexagon.lean#L133));
  parts (1) and (2) are stated on the book's open interval `0 < x < 1/√3` and proved on
  `[0, 1/√3)`. Theorem 5.0.2 takes a balanced pair with its boundary trajectory (`σ_j = g s_j*`,
  `σ_j(t + t_f) = σ_{j+1}(t)`, `X = g⁻¹g'`) and a curve `z` in `𝔥*` with `X = Φ ∘ z`. "The cost of
  the trajectory is strictly greater than the area of the smoothed octagon" is stated with the
  cost equal to `area(K)`, and "Hence `K` is not a global minimizer" as two conclusions: the
  smoothed octagon has a smaller greatest packing density (so `K` is not a `K_min`), and `(g, X)`
  is not a global minimizer of Problem 3.6.2 for any control. The dihedral reduction of the proof
  ("everything ... has been equivariant") is read as the invariance of the density bound `δ` under
  the dihedral group acting on `𝔥*` ([`densityBound_dihedralAct`](SmoothedPolygons/Ch5/Theorem502.lean#L149)); no action on disks or trajectories
  is needed.
- **Filippov's theorem (Theorem 6.1.1).** The state space is `ℝⁿ` instead of a manifold (for `f`
  smooth with compact support, the manifold case follows by an embedding in some `ℝᴺ`); a
  trajectory is a Carathéodory solution driven by a measurable control; "the support of `f` is a
  compact subset of `M × U`" is read as `f(q, u) = 0` for `q` outside a compact set; the attainable
  sets are those at time `T` and up to time `T`; and "an optimal control exists" is stated for fixed
  and for free terminal time (the book applies it with free terminal time `t_f ≤ π/3`, TeX 3207,
  4583), under the convexity of the extended velocity sets (E35).
- **Winding number (§3.5, §6.1).** An admissible trajectory has winding number one
  ([`IsWindingOne`](SmoothedPolygons/Ch6/Winding.lean#L82)) when the continuous angle `θ` of `σ₀(t) = g(t)s₀*` with `θ(0) = 0` ends at
  `θ(t_f) = π/3`, rather than `π/3 + 2πm` with `m ≥ 1`; the closed curve `σ₀` on `[0, 6t_f]`
  (extended by `g(t + t_f) = g(t)R`) then winds once around the origin. The converse of Problem
  3.6.2 (E15) is stated with that extension `G` of `g` to `ℝ`: `σ_j = G s_j*` is the multi-curve of
  a balanced pair `(K, σ)` in circle representation, and `area(K)` is the cost.
- **The existence of a minimizer and `K_min` (§6.1).** "An optimal control exists" is read as the
  existence of a global minimizer of Problem 3.6.2 ([`IsReinhardtMinimizer`](SmoothedPolygons/Ch3/ControlProblem.lean#L115): an admissible
  trajectory whose cost is at most that of every admissible trajectory, of any terminal time).
  `K_min` is a centrally symmetric convex disk of least greatest packing density `δ_min`
  ([`IsWorstDisk`](SmoothedPolygons/Ch2/Density.lean#L326), [`minimaxDensity`](SmoothedPolygons/Ch2/Density.lean#L321)). The identification of the global minimizers with `K_min` (E47)
  is read as two statements: every `K_min` has an image under a linear map of positive determinant
  that is a balanced disk in circle representation whose boundary trajectory is a global
  minimizer; and every balanced disk whose boundary trajectory is a global minimizer is a `K_min`,
  with `δ_min = cost/√12`.
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
- **Extremals on an interval (Chapter 8).** "An extremal lifted trajectory on `[t₁, t₂]`" is the
  state–costate system of Problem 6.7.1 on that interval with the conditions of the maximum
  principle (`λ_cost ≤ 0` constant, nontriviality of `(λ_cost, Λ₁, Λ_R)`, the maximum condition
  and `H = 0` almost everywhere) and no boundary conditions ([`IsExtremalOn`](SmoothedPolygons/Ch8/Defs.lean#L59)); a Pontryagin
  extremal restricts to one on every subinterval. Normal and abnormal are as in Definition 6.2.1.
- **The edge control problem (§8.1).** Its state `(x, y, s)` is a point of `ℝ³` (`Fin 3 → ℝ`),
  its control `u_e ∈ [-½, ½]`, its state space `y > 0`, `|x| < 1/√3` (Definition 8.1.1), its
  dynamics (8.1.3) and its cost `∫x²/y` (8.1.5); its extremals ([`IsEdgeProblemExtremal`](SmoothedPolygons/Ch8/Defs.lean#L110)) are the
  conclusions of the maximum principle for it, with fixed endpoints (8.1.4), so that there are no
  transversality conditions. The book treats the edge `{u₀ = 0}` and the others "by rotational
  symmetry" (TeX 6774–6775); the formalization rotates explicitly: conjugation by `Rʲ`
  ([`edgeFrame`](SmoothedPolygons/Ch8/Defs.lean#L124)) takes a control in the edge `{u_j = 0}` to one in `{u₀ = 0}`, and is applied to `g`,
  `X`, `Λ₁` and `Λ_R`. The edge state of a Reinhardt trajectory ([`edgeState`](SmoothedPolygons/Ch8/Defs.lean#L135)) is `z = x + iy` with
  `Φ(z) = RʲXR⁻ʲ` (Lemma 4.2.1) and `s = ∫dt/y`, with `s = 0` at the start ("We can take
  `s₀ = 0`").
- **Edge extremality (Definition 8.1.2).** A trajectory is edge extremal on `[a, b]`
  ([`IsEdgeExtremalOn`](SmoothedPolygons/Ch8/Defs.lean#L148)) if on every subinterval on which some `u_j` vanishes almost everywhere, its
  edge state and edge control lift to an extremal of the `j`-th edge problem. The definition takes
  `u` and `X` only, since `g` is determined there by (8.1.1).
- **Maximizers and singular subarcs (§8.2).** `(X, Λ_R) ∈ ⋃_{I ⊆ {i,j}} (T*O_J)_I` is read as
  "the set of maximizers of the Hamiltonian over `U_T` ([`hamiltonianArgmax`](SmoothedPolygons/Ch8/Defs.lean#L158)) is contained in the
  edge `{i, j}` ([`controlEdge`](SmoothedPolygons/Ch8/Defs.lean#L164))". A singular subarc (Definition 6.2.1(3), [`IsSingularSubarc`](SmoothedPolygons/Ch6/Hamiltonian.lean#L255)) is an
  open interval at each time of which the Hamiltonian has at least two maximizers in `U_T`; a
  singular subarc of the edge problem ([`IsEdgeSingularSubarc`](SmoothedPolygons/Ch8/NoSingularArcs.lean#L217)) likewise, for the edge Hamiltonian
  (8.1.6) over `[-½, ½]`. Theorem 8.2.7 is read as E55 says. The singular locus (Definition 8.2.4,
  [`singularLocus`](SmoothedPolygons/Ch8/Defs.lean#L177)) is the printed set of quadruples `(g, Λ₁, X, Λ_R)`; along an extremal, the lift
  meets it at `t` exactly when `λ_cost ≠ 0`, `Λ₁(t) = (3/2)λ_cost J`, `X(t) = J` and `Λ_R(t) = 0`
  with the extremal's own `λ_cost`.
- **Lemma 8.2.1** is stated for `X` with `⟨X, Z_u⟩ ≠ 0` on `U_T` (E52), and **Theorem 8.1.4** for
  every extremal of the edge problem on a closed interval (E49). **Lemma 8.1.5**'s Landau notation
  is two-sided, as the book defines it (TeX 6903–6907), with the solutions continuous and in
  integral form. **Theorem 8.3.1** is read in its one-sided form (E56), and **Theorem 8.3.2** on a
  compact interval `[a, b]` (E57).
- **Bang-bang with finitely many switches.** [`IsFiniteBangBang`](SmoothedPolygons/Ch8/Defs.lean#L195) asks for a finite set of times off
  which the control is, near each time of `(a, b)`, almost everywhere constant at a vertex of
  `U_T`; the book's "adjusting the control on a set of measure zero" is this almost-everywhere
  formulation. A switching time ([`IsSwitchingTime`](SmoothedPolygons/Ch16/MahlerFirst.lean#L48)) is a time on each side of which the control is
  almost everywhere one vertex, the two vertices being different.
- **Smoothed polygons (Remark 8.3.3, Theorem 16.3.1).** A hyperbolic arc ([`IsHyperbolicArc`](SmoothedPolygons/Ch8/PolygonBoundary.lean#L47)) is
  an injective continuous arc of a hyperbola `det(d₁, x - p₁)·det(d₂, x - p₂) = c`, `c ≠ 0`, with
  non-parallel asymptotes, the form of the conclusion of Lemma 3.1.8. The boundary of a smoothed
  polygon ([`IsSmoothedPolygonBoundary`](SmoothedPolygons/Ch8/PolygonBoundary.lean#L58)) is the union of finitely many segments and finitely many
  hyperbolic arcs, each arc beginning and ending on segments and having as asymptotes the lines
  that extend two of the segments. "A finite-sided smoothed polygon with rounded hyperbolic arcs at
  each corner of the sort described by Reinhardt and Mahler", glossed as "no corners and the
  boundary alternates between straight edge segments and hyperbolic arcs, whose asymptotes are
  lines extending the straight edge segments" (TeX 12800–12804), is a centrally symmetric convex
  disk with a unique support line at each boundary point whose boundary is that of a smoothed
  polygon ([`IsSmoothedPolygon`](SmoothedPolygons/Ch8/PolygonBoundary.lean#L72)). "Defines a balanced disk `K(g, X)`" in Remark 8.3.3 is read as a
  hypothesis: a balanced pair `(K, σ)` with `σ_j = g s_j*` and `σ_j(t + t_f) = σ_{j+1}(t)` (E58).
- **The Fuller system (§13.2).** A point of `ℂ³` is `Fin 3 → ℂ` with `z 0 = z₁`, `z 1 = z₂`,
  `z 2 = z₃`. Trajectories with a measurable control are solved in Carathéodory's sense
  ([`TriFuller.IsTrajectory`](SmoothedPolygons/Ch13/Defs.lean#L170)), and the maximum condition (13.2.5) and `H_F = 0` (13.2.6), which the
  book writes for every `t`, are imposed almost everywhere ([`TriFuller.MaxCondition`](SmoothedPolygons/Ch13/Defs.lean#L179),
  [`TriFuller.IsExtremal`](SmoothedPolygons/Ch13/Defs.lean#L185), the solutions of Lemmas 13.2.1–13.2.3). The form `RR(a, b) = Re(āb)`
  ([`SmoothedPolygons.RR`](SmoothedPolygons/Ch13/Defs.lean#L97)) is the only coordinate of Chapters 10–11 that Chapter 13 uses.
- **The first control and the first switching time (TeX 10747–10753).** They are defined at every
  `z⁰` by the maximum condition along the constant-control trajectory, without choosing roots of
  the switching functions: `u ∈ V_T` is the first control ([`TriFuller.IsFirstControl`](SmoothedPolygons/Ch13/Defs.lean#L237)) if the
  constant control `u` is optimal along its own trajectory on some `[0, ε]`, and `t_sw`
  ([`TriFuller.firstSwitchTime`](SmoothedPolygons/Ch13/Defs.lean#L249)) is the time at which it stops being optimal. A double root of a
  switching function at which the control stays optimal (a tangency) is therefore not a switching
  time; there the extremal is unique and does not switch (E62). For `z⁰ ≠ 0` the first control
  exists and is unique, `0 < t_sw < ∞`, and every extremal with a measurable control from `z⁰`
  follows it up to `t_sw` ([`TriFuller.eq_flow_of_maxCondition`](SmoothedPolygons/Ch13/Extremals.lean#L424)); at `z⁰ = 0` the definitions take
  junk values. The most recent control and switching time (Lemma 13.2.5) are defined likewise.
- **Rotations.** Where the book rotates by `V_T` "without loss of generality" (to `i = 0` in
  Lemma 13.2.6, to `u = ζ` in Corollary 13.2.7, to `u = 1` in Lemma 13.3.1), the formal proofs
  compute for every vertex at once, through `RR(ua, ub) = RR(a, b)` for `|u| = 1`.
- **The blow-up and the Poincaré map (§13.4–13.5).** The identification `ℂ³ ∖ 0 ≅ ℝ_{>0} × Ξ` is
  a homeomorphism ([`TriFuller.blowup`](SmoothedPolygons/Ch13/Blowup.lean#L313)) with `φ` of class `C²`, smooth off `z₂ = 0` (E66). The
  Poincaré map `F(z⁰) = z(t_sw, z⁰, u)`, `u` the first control ([`TriFuller.poincare`](SmoothedPolygons/Ch13/PoincareMap.lean#L208)), is defined
  on `ℂ³ ∖ 0` rather than on `(ℝ_{>0} × Ξ)_𝒲`; on the section it is the book's map (E67). `F_ang`
  is defined on `Ξ_𝒲` and on `Ξ_𝒲/V_T` ([`TriFuller.poincareAng`](SmoothedPolygons/Ch13/PoincareMap.lean#L495), [`TriFuller.poincareAngQuot`](SmoothedPolygons/Ch13/PoincareMap.lean#L509)).
  `Ξ_{𝒲,0}/V_T`, which the book never defines formally (Remark 13.5.1 and Lemma 13.5.5 describe it
  in words), is the set where the maximized Hamiltonian `H_F⁺` vanishes ([`TriFuller.XiW0Quot`](SmoothedPolygons/Ch13/PoincareMap.lean#L528)), to
  which `F_ang` restricts ([`TriFuller.poincareAngZero`](SmoothedPolygons/Ch13/PoincareMap.lean#L551)); on a wall the two tied controls give the
  same value of `H_F`, so `H_F⁺` is the Hamiltonian there.
- **Lemma 13.5.2 and Remarks 13.5.3–13.5.4.** "Exactly two fixed points in `Ξ_𝒲/V_T` at which the
  Hamiltonian vanishes" is an equality of sets, `{x | F_ang(x) = x, H_F⁺(x) = 0} = {q_out, q_in}`,
  with `q_out ≠ q_in`. "`q_out ≡ (13.5.1) mod 𝒢`" is stated with a representative `q`
  ([`TriFuller.qOutCart`](SmoothedPolygons/Ch13/FixedPoints.lean#L69)) normalized by `Re z₁ = -1` and `z₃ ∈ ℝ_{<0}`, and the two spirals as
  `F(q) = ζ²·(rq₁, r²q₂, r³q₃)` with `r = r_scale`, and the same for `τ(q)` with `r = 1/r_scale`.
  `r_scale` ([`TriFuller.rScale`](SmoothedPolygons/Ch13/RScale.lean#L47)) is the unique real root greater than `1` of the palindromic
  polynomial, and the book's `≈ 6.27` and `≈ 7.4` are certified bounds, `6.27 < r_scale < 6.28`
  and `7.4 < t_sw < 7.41`. Remark 13.5.3 is stated for `q` and `τ(q)`; Remark 13.5.4 for its
  verifiable part (E69).
- **Lemma 13.5.5.** Stability is that of a fixed point of a map of a topological space
  ([`Function.IsLyapunovStable`](Basic/Dynamics/Stability.lean#L44), [`Function.IsAsymptoticallyStable`](Basic/Dynamics/Stability.lean#L49), [`Function.IsUnstable`](Basic/Dynamics/Stability.lean#L54), in
  [`Basic/`](Basic)): asymptotically stable means fixed, Lyapunov stable and attracting every point
  of a neighbourhood; unstable means fixed and not Lyapunov stable. The lemma is stated for `F_ang`
  on `Ξ_{𝒲,0}/V_T` with the quotient topology.
- **Theorem 16.3.1.** "The global minimizer" is read as every global minimizer of Problem 3.6.2
  ([`IsReinhardtMinimizer`](SmoothedPolygons/Ch3/ControlProblem.lean#L115)) and "the minimizer `K_min`" as every `K_min` ([`IsWorstDisk`](SmoothedPolygons/Ch2/Density.lean#L326)); one of
  each exists (E46, E4). The theorem is stated as two conclusions under the hypothesis
  [`NoChatteringIntoSingularLocus`](SmoothedPolygons/Ch16/MahlerFirst.lean#L107) (Section 2): every global minimizer has a bang-bang control with
  finitely many switches on `[0, T]`, and every `K_min` is a smoothed polygon (E60).
- **Corollary A.1.3** is stated as printed, on `[0, t₁]` with the conclusion as `t → 0⁺`; the
  two-sided form that Chapter 8 uses is a separate statement (E61).
- **Balanced pairs exist.** The unit disk, with `σ_j(t) = Rot(t) s_j*` and `t_f = π/3`, is a
  balanced pair ([`circle_isBalancedPair`](SmoothedPolygons/Ch2/BalancedCircle.lean#L241)), so the hypotheses of the results of Chapter 3 about
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
  of §13.4 as a homeomorphism with `φ` of class `C²`), and in proofs E14, E24, E44, E50, E59,
  E64, E65 and E67.

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
| Theorem 5.0.6, the claim of Case 1 | if no point of `[r₀, r̃₀]` lies on `∂K`, then `K` lies in the centrally symmetric hexagon `r₀, r̃₀, q₁, …`, of the area of `H_K(z)`; shifting its cut edges inward until they meet `K` gives a smaller one | the line parallel to `s₀s₁` is shifted at once to the support line of `K`: if it lies strictly inside the cut, the hexagon cut at that line contains `K`, is centrally symmetric and convex, and has area `area(H_K(z)) + 2T₀^ext - 2μ²T₀ < area(H_K(z))`; otherwise the extreme point of `K` on the cut line lies on `[r̃₀, r₀]` ([`exists_mem_frontier_segment_cut`](SmoothedPolygons/Ch5/AreaBound.lean#L519)) | the book does not argue that `K` lies in its hexagon, nor that the hexagon is convex (E43) | E43 |
| Theorem 5.0.6, Case 2 and the area bound | Case 1 for `z ∈ h₀ ∖ (h₁ ∪ h₂)`, with `area(K) ≥ area(conv{s_j*, ±r})`; Case 2, `z ∈ h₀ ∩ h₁`, "adapted"; `h₀ ∩ h₁ ∩ h₂ = ∅` leaves no other case | the claim at each corner `i` with `z ∈ h_i` separately (the construction changes `H_K(z)` only near `p_i` and `p_{i+3}`); `area(K)` bounded below by the measure of the union of `conv{s_j*}` and the triangles `±△s_i r_i s_{i+1}`, `z ∈ h_i`, which have pairwise disjoint interiors ([`theorem5_0_6`](SmoothedPolygons/Ch5/AreaBound.lean#L777)) | Case 2 is only sketched (E43); the corner-by-corner argument covers it, Case 1 and `z ∉ h₀ ∪ h₁ ∪ h₂` at once, and in Case 1 the union has the area of the book's convex hull; `h₀ ∩ h₁ ∩ h₂ = ∅` is then not used | E43 |
| Lemma 5.0.7 (3) | the sum (5.0.1) is continuous and increases in `x` on `h₀ ∖ h₂` and on `h₀ ∩ h₂`, hence on `h₀ ∩ {x > 0, y ≥ √3}`; it is even, so least at `x = 0` | `{x ≥ 0, y ≥ √3} ⊆ h₀`, and there `I₀area₀ + I₂area₂ = max(area₀ + area₂, area₀)`, the maximum of the functions that (2) and (1) show increasing; even in `x` ([`lemma5_0_7_3`](SmoothedPolygons/Ch5/Monotonicity.lean#L541)) | the book does not show that the points with `x > 0`, `y ≥ √3` lie in `h₀`; the maximum makes its "increasing on each piece, and continuous" precise (E44) | E44 |
| §6.1, the existence of a minimizer | Filippov's theorem (Theorem 6.1.1) applied to the half-plane system (Problem 4.5.1), with the vector fields multiplied by a cut-off `ψ`, `ψ = 1` on `𝔥**`; `t_f ≤ π/3` by Lemma 4.3.1 | Filippov's theorem with the closed state constraint `z ∈ 𝔥**`, a compact set of initial points, the closed endpoint relation of Problem 3.6.2 and the window `[0, π/3]` (`ControlSystem.exists_optimal_constrained`, OptimalControl package), applied to the matrix system of §6.2 (Lemma 6.1.2 carried over by Lemma 4.5.2); `t_f < π/3` for competitors cheaper than the smoothed octagon from `cost ≥ 3t_f` ([`three_mul_le_reinhardtCost`](SmoothedPolygons/Ch4/TerminalTime.lean#L71)); the octagon is in the class ([`exists_isReinhardtMinimizer`](SmoothedPolygons/Ch6/Existence.lean#L436)) | the cut-off changes the dynamics outside `𝔥**`, so a minimizer of the cut-off problem need not be a Reinhardt trajectory; Theorem 6.1.1 fixes the initial point, while `X(0)` is free and the endpoints are coupled; Lemma 4.3.1 assumes the minimizer whose existence is proved (E46). The matrix system is the one whose admissible pairs §6.2 already identifies with the trajectories of Problem 3.6.2 | E46 |
| §6.2 and §6.6, every minimizer is a Pontryagin extremal | the maximum principle on `SL₂(ℝ) × 𝔰𝔩₂(ℝ)` with the boundary conditions `g(0) = I₂`, `g(t_f) = R`, `X(t_f) = R⁻¹X(0)R`; the Hamiltonian by Proposition 6.4.1, the costate equations by Proposition 6.5.1, the transversality conditions of §6.6 (for `Λ₁` by Corollary 6.5.3) | the same steps, with two changes. (1) The maximum principle is applied on the open set `GL₂⁺(ℝ) × C` of `Mat₂(ℝ) × 𝔰𝔩₂(ℝ)` ([`matrixDomain`](SmoothedPolygons/Ch6/MatrixSystem.lean#L118)), with `g(0) = I₂` and `det X(0) = 1` among the boundary conditions; this adds three steps: `det g` and `det X` are first integrals, so the competitors are Reinhardt trajectories; the adjoint equation meets the hypotheses of Proposition 6.5.1 through the momentum `p - (tr(pg)/2)g⁻¹`; and the covector `pg = kI₂` of (2). (2) The boundary condition is applied less the equations `g(t_f)₁₁ = R₁₁` and `X(t_f)₁₀ = (R⁻¹X(0)R)₁₀`, which the first integrals `det g` and `det X` make redundant ([`matrixBoundary`](SmoothedPolygons/Ch6/MatrixSystem.lean#L136)); transversality in the two directions this frees excludes the covectors whose reduced costate vanishes, and the nontriviality of `(λ_cost, Λ₁, Λ_R)`, which the book does not derive, is proved by Corollary 6.5.3, uniqueness for the linear `Λ_R` equation and transversality at `t_f` ([`exists_isPontryaginExtremal_of_isReinhardtMinimizer`](SmoothedPolygons/Ch6/MatrixExtremal.lean#L564)) | (1) the maximum principle available in Lean is stated on open subsets of a finite-dimensional space, and `SL₂(ℝ)` is not open in `Mat₂(ℝ)`; (2) with the full boundary conditions the conclusions of the maximum principle hold for every admissible trajectory with a covector whose reduced costate vanishes, so the nontriviality of `(λ_cost, Λ₁, Λ_R)` does not follow (E21) | E21 |
| Theorem 7.7.1, step 6 (the fixed points of `f⁴` near `q_oct`) | for each `d` near `d_oct`, `q_fix(d)` stays hyperbolic and the implicit function theorem inverts `f_d⁴ - I` near `q_fix(d)`; "thus, the only fixed points near `q_oct` are the fixed points `q_fix(d)`" (TeX 6612–6620) | the inverse function theorem applied once, at `q_oct`, to `Ψ = (section constraints, f⁴ - id)`, whose constraints include `d = det Λ₁`: its derivative is injective because `A⁴ - I` is invertible on the tangent space of the section (step 5), so `Ψ` is injective near `q_oct`, and a fixed point with `det Λ₁ = d` has the same image as `q_fix(y₀(d))`, with `y₀(d)` from Remark 7.5.2 as in the book ([`iso_fixedPoints`](SmoothedPolygons/Ch7/Isolated/FixedPoints.lean#L179)) | a separate application for each `d` gives a neighbourhood of each `q_fix(d)`, not one uniform in `d`, which the conclusion needs; the single application gives the uniformity, and the hyperbolicity of `q_fix(d)` for `d ≠ d_oct` is not needed | E32 |
| Proposition 8.1.3, edge extremality | "the globally minimizing trajectory must minimize cost among all trajectories with the same endpoint conditions on the subinterval and that have their control function similarly restricted to the edge" (TeX 6793–6797) | competitors of the edge problem uniformly close to the minimizer's edge arc are spliced into the minimizer: the middle arc rebuilt from `(x, y, s)` by (8.1.1), the rest of the minimizer shifted in time, the costs compared by the cost identity of §8.1; the edge arc is then a strong local minimizer of the edge problem, to which the maximum principle applies ([`proposition8_1_3`](SmoothedPolygons/Ch8/EdgeExtremal.lean#L850)) | the state space of the edge problem is larger than the star domain, so a competitor far from the arc may give no Reinhardt trajectory, and the book gives no construction (E48) | E48 |
| Theorem 8.1.4, two steps | "The function `λ₂'` is also continuous" (TeX 6846–6852); Lemma 8.1.5 applied at every zero of `λ₂` with `λ₂' = 0` (TeX 6884–6886) | the derivative of `λ₂` is proved to exist at each zero of `λ₂`, equal there to the right-hand side of (8.1.7), and only that is used; at a zero at an end of the interval, the state and the costate are continued beyond it with the control `u_e = 0`, where they are explicit, before Lemma 8.1.5 is applied ([`theorem8_1_4`](SmoothedPolygons/Ch8/EdgeBangBang.lean#L823)) | `λ₂'` is continuous only after a change of the control on a null set; Lemma 8.1.5 needs a solution on both sides of the zero (E49) | E49 |
| Theorem 8.2.7 | Theorem 8.2.6 makes a singular subarc a circular arc, which the second variation excludes | the authors' reading (the user's decision): on an interval with the control in an edge, the costates of the edge arc (Proposition 8.1.3) have no singular subarc of the edge problem, by the argument of Theorem 8.1.4; elsewhere a localization by Lemma 8.2.1 leaves the subarcs with `Λ_R ≡ 0`, which the book's argument excludes (Theorems 8.2.6 and 8.2.3 and the second variation) ([`theorem8_2_7`](SmoothedPolygons/Ch8/NoSingularArcs.lean#L375)); for normal lifts the printed statement, through the pull-back of the costate to the edge ([`not_isSingularSubarc_of_isReinhardtMinimizer_of_isNormalExtremal`](SmoothedPolygons/Ch8/NoSingularArcs.lean#L418)) | the book's proof covers only the subarcs on which the Hamiltonian does not depend on the control (E55) | E55 |
| Theorem 8.3.1 (in its one-sided form) | in the contrapositive: if the maximizers are not confined to one edge near `t₀`, claims (a)–(c) put the lift in `𝒮_sing` at `t₀`; claim (a) passes to the control through Theorem 8.1.4 | claims (a)–(c) run directly, on each side of `t₀` separately, and give an edge containing the maximizers on each side ([`theorem8_3_1`](SmoothedPolygons/Ch8/FiniteBangBang.lean#L1288)); the passage to the control, with edge extremality and Theorem 8.1.4, is the corollary that the proof of Theorem 8.3.2 quotes ([`IsExtremalOn.exists_ae_mem_controlEdge_of_isEdgeExtremalOn`](SmoothedPolygons/Ch8/FiniteBangBang.lean#L1349)); at an end of the interval the Gronwall step uses the functions extended by their values there | the printed statement is false, and the form the user chose needs no passage to the control (E56) | E56 |
| Lemma 13.2.5, and the descent of the Poincaré map to `Ξ_𝒲/V_T` and `F_ang` (§13.5) | "The lemma follows from the time-reversal symmetry (Lemma 13.2.3)" (TeX 10905–10906); `F` descends "by the equivariance of the construction" and "by the scaling symmetries" (TeX 11246–11260), that is, by Lemmas 13.2.1 and 13.2.2 | the substitutions behind Lemmas 13.2.1–13.2.3 redone for constant controls at every `z⁰` ([`TriFuller.tau_flow_neg`](SmoothedPolygons/Ch13/Symmetry.lean#L172), [`TriFuller.ham_tau`](SmoothedPolygons/Ch13/Symmetry.lean#L192), [`TriFuller.poincare_smul`](SmoothedPolygons/Ch13/PoincareMap.lean#L293), [`TriFuller.poincare_scale`](SmoothedPolygons/Ch13/PoincareMap.lean#L327); [`lemma13_2_5`](SmoothedPolygons/Ch13/FirstControl.lean#L918)) | Lemmas 13.2.1–13.2.3 are about solutions with `H_F = 0`, which need not hold at `z⁰` (E63) | E63 |
| Lemma 13.2.6 | a necessary condition: the first control, if it exists, maximizes the lexicographic order, and in a tie `{ζ^i, ζ^{i+1}}` it is not `ζ^{i+1}`, by contradiction from the sign of the cubic term (TeX 10978–11008) | the sufficient direction, which the statement asserts: the lexicographic maximizer, with the tie rule, is optimal along its own trajectory on some `[0, ε]`, by the same Taylor expansion and the same cubic coefficient; the necessary direction is [`TriFuller.firstControl_mem_lexMaxControls`](SmoothedPolygons/Ch13/FirstControl.lean#L636), and the uniqueness of the first control is proved generically ([`TriFuller.IsFirstControl.unique`](SmoothedPolygons/Ch13/FirstControl.lean#L330); [`lemma13_2_6`](SmoothedPolygons/Ch13/FirstControl.lean#L539)) | the first control is the control that is optimal on some `[0, ε]`, and the book never shows that the maximizer is (E62) | E62 |
| Lemma 13.3.2 | two cases, each on all of `[0, t₂]`: the Hamiltonian independent of the control in `U_T` (then `z ≡ 0`), or in the edge `[ζ, ζ²]` (then `0 = RR(z₃(t), ζ - ζ²) = (√3/2)t³/3! + (quadratic in t)`, absurd) | the maximizers are not a vertex, so `z₃(t) ∈ 𝒲` for every `t`; if `z₃(t₀) ≠ 0`, `z₃` stays on one open ray `ℝ_{<0}c` of `𝒲` on an interval around `t₀`, where the book's second case runs with `RR(z₃, ic)` in place of `RR(z₃, ζ - ζ²)` (for `c = 1`, the book's quantity divided by `√3`) and gives a contradiction; so `z₃ ≡ 0`, and the book's first case applies ([`lemma13_3_2`](SmoothedPolygons/Ch13/SingularLocus.lean#L710)) | the hypothesis lets the maximizing face change with `t`, which the book's two cases do not cover (E65) | E65 |
| Lemma 13.5.2, step 3 (the three cases `(r, ζ₁)`) | "at times `t = 0, t_sw` we must have by the maximum principle" a chain of inequalities ending in `z₃⁰ūζ₁² ∈ ℝ_{≤0}`, from which the three cases are asserted (TeX 11361–11380) | the maximum condition at `t = t_sw` for the outgoing control `u` and the incoming control `ζ₁u`, which by (13.5.2) and the equivariance of `F` is the book's condition at `t = 0`; `ζ₁ = 1` excluded, since the control switches at `t_sw` while the first control of `F(z⁰)` is `ζ₁u`; the three cases derived from the wall condition by identities in `ℤ[r, ζ]`: the imaginary part gives `(r - 1)P(r) = 0`, and the real part a sign through `Q₆ = P + 4r⁵ + 6r⁴ + 4r³ + 6r² + 4r` ([`lemma13_5_2`](SmoothedPolygons/Ch13/FixedPointsClassification.lean#L571)) | the book's display is garbled, its final condition follows only when `ζ₁ ≠ 1`, which the book does not exclude, and the passage to the three cases is asserted (E67) | E67 |
| Lemma 13.5.2, the solutions as fixed points (step 5 and the verification of (13.5.1)) | "The coordinates in the statement of the lemma have been rotated by `V_T`, choosing the first control `u = ζ₁²`, to make the third coordinate real and negative" (TeX 11384–11386); (13.5.1) is not derived, and that it gives fixed points with `H_F = 0` is not checked | the representative of `q_out` satisfies the fixed-point equation, so by step 2 it is the candidate for its own first control and switching time, and the candidates, homogeneous in `(u, t_sw)`, agree up to the virial group; its first control `ζ` is shown from the definition (`ζ` is optimal on `[0, t_sw]`) and uniqueness; `t_sw` is the first switch because the switching function to `ζ²` is `√3t(Im z₂⁰ + Im z₁⁰t/2 + t²/12)`, with positive coefficients, and the one to `1` has the signs `+ + + −` and vanishes at `t_sw`; and `H_F = (r² + r + 1)P(r)/(9(r + 1)²(1 + r³ + r⁶))` along (13.5.1), all exact in `ℚ(√3)(r)` modulo `P` ([`TriFuller.poincare_qOutCart`](SmoothedPolygons/Ch13/FixedPoints.lean#L517), [`TriFuller.firstSwitchTime_qOutCart`](SmoothedPolygons/Ch13/FixedPoints.lean#L496), [`TriFuller.hamMax_qOutCart`](SmoothedPolygons/Ch13/FixedPoints.lean#L526)) | (13.5.1) is computer-generated in the book, and the facts that make its solutions fixed points of `F` with `H_F = 0` are not shown (E67) | E67 |
| Lemma 13.5.5 | time reversal for `q_in`; for `q_out`, "An explicit calculation of the eigenvalues of the Jacobian matrix in terms of local coordinates centered at `q_out` gives the result. Numerically, the three eigenvalues have absolute value less than `0.1`. The calculations were made in Mathematica" (TeX 11443–11453) | the same three steps, certified: the chart `Re z₁ = -1`, `z₃ ∈ ℝ_{<0}`, `H_F = 0`, with coordinates `(Im z₁, Re z₂, Im z₂)` ([`TriFuller.exists_chart`](SmoothedPolygons/Ch13/Jacobian.lean#L1638)); the map in the chart, smooth near `q_out` by the implicit function theorem (`t_sw` is a simple root there); its Jacobian, exact in `ℚ(√3, r_scale)` ([`TriFuller.jacobianOut`](SmoothedPolygons/Ch13/Jacobian.lean#L136)); sign changes of the characteristic polynomial at rational points, which put the three eigenvalues in `(-1/10, 1/10)` ([`TriFuller.norm_lt_of_aeval_charpoly_jacobianOut_eq_zero`](SmoothedPolygons/Ch13/Jacobian.lean#L1919)); linearized stability for maps ([`Function.isAsymptoticallyStable_of_hasFDerivAt`](Basic/Dynamics/LinearizedStability.lean#L146)); and time reversal: `τ ∘ F_ang` is an involution near `q_out` and `q_in`, which carries asymptotic stability to instability ([`Function.IsAsymptoticallyStable.isUnstable_of_involutive`](Basic/Dynamics/Stability.lean#L130); [`lemma13_5_5`](SmoothedPolygons/Ch13/Stability.lean#L281)) | the book's proof is a numerical computation with no chart, matrix or values; it does not argue that `F_ang` is `C¹` near `q_out` or that `τ ∘ F_ang` is an involution there; and Mathlib has no stability theorem for maps (E68) | E68 |
| Theorem 16.3.1, the last step | after Theorems 8.2.7 and 8.3.2 and Lemma 8.3.4, "the proof then reduces to" switching points accumulating at the singular locus, which the blow-up, Theorems 16.4.1 and 14.4.1 and periodicity exclude (TeX 12820–12833) | the set of meeting times is handled (empty interior, a meeting at `0` moved to `T`, the first meeting time `d` after a time off the set); switching times accumulating at `d` are excluded by the hypothesis [`NoChatteringIntoSingularLocus`](SmoothedPolygons/Ch16/MahlerFirst.lean#L107), and a vertex control just before `d` by Lemma 8.3.4 ([`theorem16_3_1`](SmoothedPolygons/Ch16/MahlerFirst.lean#L343)) | Chapters 13–16 are not formalized, so the consequence of their theorems that the step uses is a named hypothesis; the book does not handle the set of meeting times (E60) | E60 |

Every other proof follows the book's argument. The gaps of Theorem 2.2.2 (E2), Theorem 2.3.9 (E7),
Lemmas 2.2.6, 2.2.7, 2.4.3 (E5, E9), Lemma 3.1.8 (E34), the shift of §3.5 (E39), Definition 5.0.1
(E41), Lemma 5.0.3 (E42, through Theorem 2.2.2, E12 and Theorem 2.3.9), Lemma 5.0.7 (4) (E44),
Theorem 5.0.2 (E45), Lemma 7.5.5 (E30), Theorem 7.5.6 (E31) and Theorem 7.7.1 apart from its step
6 (E32) are filled along the book's lines, and the index slips of Lemma 2.4.5 (E10) and Lemma
5.0.7 (3) (E44) are corrected. The converse of Problem 3.6.2 for winding number one (E15) and the
identification of the minimizers with `K_min` (E47) have no proof in the book: the first
generalizes the formalization's argument for the smoothed polygons, and the second assembles the
results of Chapters 2–3 that derive the control problem from `K_min`. The bound on the cost of
trajectories of higher winding number (E15) is a new argument, a pointwise inequality between the
cost density and the turning of the bottom row of `g`. In Lemma 2.4.3 the formal proof bounds the turning of the tangent
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

In Chapter 8 and Appendix A.1, the gaps of Lemma 8.2.1 (E52), the vanishing of the Hamiltonian at
a single time in Theorem 8.1.4, Lemma 8.2.2 and Theorem 8.3.1 (E53), the converse of Theorem
8.2.6 (E54), the second variation of Theorem 8.2.7 (E55), claim (b) of Theorem 8.3.1 (E56) and
Corollary A.1.3 (E61) are filled along the book's lines, and the slips of Lemma 8.1.5 (E50) and
Lemma 8.3.4 (E59) are corrected. The second variation follows the book's route, with its condition on `ψ` read on the
interior of the overlap of the supports; the formal proof computes the cost of the deformed arc
exactly, and the book's expansion is the second-order truncation of that formula (E55). Remark
8.3.3 has no proof in the book; its proof assembles Theorem 8.3.2, the discussion of §7.2 and
Lemma 3.1.8 (E58). Three changes are inessential. In Lemma 8.1.5 the norm of the error `v` is
`|v₁| + |v₂|` instead of the Euclidean one, and `‖v‖' ≤ ‖v'‖` is used in its integrated form
`‖v(t)‖ ≤ |∫₀ᵗ ‖v'‖|`, which avoids differentiating the norm; the estimates of Theorem 8.3.1 use
the entrywise `ℓ¹` norm on `2 × 2` matrices likewise (the book's Euclidean norm on `𝔰𝔩₂(ℝ)`; any
norm does). In Lemma 8.3.4, "The solutions are analytic" is replaced by Taylor expansions with
remainder, obtained from the mean value inequality, which need only the first derivatives of the
solutions, and the three vertices are computed alike where the book treats `e₃` "(say)" (E59).
In Theorem 8.1.4, the count of the zeros at which `λ₂' = 0` (at most two) is proved and used as
the book uses it, although finiteness would follow from the isolation of every zero alone
(Section 11).

In Chapter 13 the other proofs follow the book's: Lemmas 13.2.1–13.2.4 and (13.2.7) by direct
substitution, which for measurable controls is a change of variables in the integral equations
and the image of a null set; Corollary 13.2.7 and Lemma 13.2.8, with the slips of E64; Lemma
13.3.1, computed for every vertex at once; and steps 1, 2 and 4 of Lemma 13.5.2 and Remark
13.5.3. Where the book only asserts, the formalization supplies standard or certified arguments:
the constancy of the Hamiltonian along extremals with measurable controls and the uniqueness of
extremals up to the first switching time (E62); the well-definedness of the Poincaré map and the
constancy of the Hamiltonian under it (E67), and its time reversal at genuine switching points
(E68); the facts about `r_scale`, by sign changes of the palindromic polynomial at rational points
(E67); and the verifiable part of Remark 13.5.4 (E69).

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
Sachkov's text and was not compared with their proof (Section 2). Its form with a state
constraint, which §6.1 uses, is proved by the same argument.

## 8. What each result depends on

The results from prior work that the proofs use are all proved (Section 2), stated in
[`External/`](External): Fejes Tóth's theorem (through Theorem 2.1.3, in Theorem 2.2.2 and the results after it,
among them those of Chapter 5 and §6.1), Gruber's formula (Definition 2.1.2), the theorems of
Minkowski and Mahler (Theorems 2.3.6, 2.3.7 and everything that uses them, Chapter 5 through
Theorem 2.3.9), Mahler's Lemma 3 with the results of paper A and Mahler 1946 that prove it
(Lemma 2.2.5, the remark after Definition 2.3.5, and the identification of the minimizers with
`K_min`), the Euler–Arnold equation (Proposition 6.5.1 and the proof that minimizers are
extremals), and the Pontryagin maximum principle (that proof, and, through it and the maximum
principle for the edge control problem, Proposition 8.1.3, Theorem 8.2.7 and Theorem 16.3.1), which
is proved in the OptimalControl package with Brouwer's theorem from the FixedPoint package.
Filippov's theorem is proved as Theorem 6.1.1, which no other result uses; the existence of a
minimizer (§6.1) uses its form with a state constraint and Gronwall's inequality, both from the
OptimalControl package, and Corollary A.1.3, in Lemma 8.1.5 and Theorem 8.3.1, uses Gronwall's
inequality too. Theorem 16.3.1 ([`theorem16_3_1`](SmoothedPolygons/Ch16/MahlerFirst.lean#L343)) uses, besides results from prior work, its
hypothesis [`NoChatteringIntoSingularLocus`](SmoothedPolygons/Ch16/MahlerFirst.lean#L107), which the audit lists among the results it uses: a
hypothesis of its statement, not an axiom (Section 2). The audit's row for it lists as results
used [`External.euler_arnold`](External/EulerArnold.lean#L72), [`External.fejes_toth`](External/FejesToth.lean#L882), [`External.gruber_corollary_30_1`](External/Gruber.lean#L320),
[`External.mahler_1947`](External/Mahler1947.lean#L1700), [`External.mahler_irreducible`](External/MahlerIrreducible/Lemma3.lean#L383), [`External.pontryagin_maximum_principle`](External/Pontryagin.lean#L80) and
[`SmoothedPolygons.NoChatteringIntoSingularLocus`](SmoothedPolygons/Ch16/MahlerFirst.lean#L107), and as axioms [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and
[`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound). No other result uses the hypothesis, not even the unconditional part of Theorem
16.3.1. The results of Chapter 13 use no result from prior work and no hypothesis; Lemma 13.5.5
uses linearized stability for maps, proved in [`Basic/`](Basic) (Section 2).
Every declaration depends only on [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound)
(`lake env lean scripts/Audit.lean`, which checks the 7434 declarations of the library and the
axioms of each numbered result, through the packages it uses); [`theorem16_3_1`](SmoothedPolygons/Ch16/MahlerFirst.lean#L343) too, since its
hypothesis is part of its statement.

The route check (`python3 scripts/route_check.py check docs/paper_routes.tsv --accept
docs/route_differences.tsv`) compares, for each of the 118 results of the book found in the Lean
code, the numbered results that the Lean proof uses with those that the book's proof cites. It
passes: every difference is recorded in [`docs/route_differences.tsv`](docs/route_differences.tsv) with its reason. The 138
differences are of these kinds (seven more, which the other route explains, are shown by `--all`:
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
- the forced differences of the user's decisions and of the conditional theorem: Theorem 8.2.7 in
  the authors' reading uses Proposition 8.1.3, (8.1.6)–(8.1.8) and Lemma 8.2.1 (E55); Theorem
  8.3.1 in its one-sided form does not use Theorem 8.1.4, which only its corollary needs (E56);
  Theorem 16.3.1 does not use Theorems 16.4.1 and 14.4.1, which its hypothesis replaces, and states
  its unconditional part (Theorem 8.3.2 with Proposition 8.1.3) separately (E60);
- Theorem 7.5.6 uses the explicit lift constructed for Theorem 7.5.1 rather than the statement of
  Theorem 7.5.1, Lemma 7.5.3 identifies its switching functions with that lift, and Lemma 7.5.5
  uses the trace computed in the proof of Theorem 7.5.1;
- the last sentence of the proof of Theorem 7.5.1 ("Lemma 7.5.3 supplements the proof") concerns
  the maximum property, which belongs to Theorem 7.5.6.

## 9. Not formalized

- **Proved only conditionally:** Theorem 16.3.1, the main theorem (Mahler's First conjecture), on
  the hypothesis [`NoChatteringIntoSingularLocus`](SmoothedPolygons/Ch16/MahlerFirst.lean#L107), which stands for Theorems 16.4.1 and 14.4.1
  (Section 2, E60). Those two theorems, and the rest of Chapters 14–16 on which they rest, are the
  later layers of the plan (Section 11); Chapter 13, on which they also rest, is formalized.
- **Outside the chosen scope:** Chapter 1 (its restatements of results of the later chapters among
  them; the restatement of Theorem 8.3.2 is false, E57); Chapters 9–12 (circular control, off the
  path to the main theorem; Chapter 13 uses only the form `RR` of Chapter 10) and Chapters 14–16,
  apart from the conditional Theorem 16.3.1; Appendix A.1 apart from Corollary A.1.3 (Lemmas A.1.1 and A.1.2, cited from
  Amann and Clarke, are not stated; the case of Lemma A.1.1 that §6.1 and Corollary A.1.3 use is
  proved in the OptimalControl package), Appendix A.2–A.5 and A.7–A.10; Appendix B.
- **Open within the formalized chapters:** the printed Theorem 8.2.7 for abnormal lifts of the
  global minimizer, which is neither proved nor refuted (E55); the formalization proves the
  authors' reading and the printed statement for normal lifts.
- **Within the formalized chapters:**
  - Remarks 7.6.1 and 7.6.3, which report numerical observations as conjectures: the area of the
    smoothed `(6k+2)`-gon "appears" to increase with `k` to `π`, and the smoothed `(6k−2)`-gons
    "seem" to satisfy every condition of an extremal except the sign of `λ_cost` (Section 11).
  - The other remarks are not stated as results, except Remarks 2.2.4, 6.6.1, 7.5.2 and 7.6.4 and
    the remark after Definition 2.3.5. Some of their content is proved where it is used: the hexagon of
    Remark 3.1.7, at a multi-point, in the proof of Lemma 3.1.8, and from a point of `𝔥*` in
    Lemma 5.0.3; the equivariance of `Φ` (Remark
    4.2.2); the positive slope of `χ₃₂` at `0` (Remark 7.5.4) in the proof of Theorem 7.7.1; the
    smoothed `(6k−2)`-gons of Remark 7.6.2 in Remark 7.6.4. Remark 4.3.2 (the cost in the disk and
    hyperboloid models) is not formalized; Remarks 3.1.2, 3.4.3, 4.1.2, 6.5.2 and 7.7.2 are
    commentary and pointers to the literature or to the appendices. In Chapter 8, Remarks 8.1.6
    and 8.3.3 are proved (E51, E58); Remarks 8.1.7 (on the 2017 preprint) and 8.2.5 (the singular
    locus gives the initial conditions of the circle) are commentary, and Remark 8.2.8, a numerical
    illustration of the deformation of Theorem 8.2.7 with a figure, is not formalized. The
    explicit solutions with constant edge control after Lemma 8.1.5, computed "in Mathematica" and
    not recorded, are not stated.
  - In Chapter 13, Remark 13.5.3 and the verifiable part of Remark 13.5.4 are proved, and Remark
    13.5.1 fixes notation. Not formalized: the interpretation in Remark 13.5.4 of the fixed point
    `q_fix` as a limit of the extremals of §7.5, which rests on Mathematica and §14.2 (E69); the
    informal corollary after Lemma 13.2.8, on consecutive switching times (E64); the singular arc
    `z ≡ 0`, `u ≡ 0` (TeX 11100–11104), an obvious solution; and the description of the blow-up as
    an oriented weighted real blowup (TeX 11198–11206). None of these is used later in the
    chapter.

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
  Hamiltonian part of the book (Chapters 6–8: costates, switching functions, Pontryagin
  extremals, the lift of a minimizer to an extremal, the edge control problem, singular subarcs
  and finite bang-bang control), and of Mahler's First conjecture conditionally on one named
  hypothesis (the search of 5 November found no formalization of Chapter 8 or of Theorem 16.3.1
  either). The state
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
  conjecture (Theorem 16.3.1) is Chapters 8–16, which a plan divides into layers, each ending in a
  releasable state whose remaining assumptions are explicit hypotheses. Layers 1–4 are done.
  Layer 1 is the maximum principle and the extremal lift of every minimizer; Layer 2, Chapter 5
  and the existence of a minimizer by the book's route (§6.1, with Filippov's theorem under a
  closed state constraint, E46), with the identification of the minimizers with `K_min` (E47):
  the Reinhardt control problem has a global minimizer, which is a Pontryagin extremal and bounds a
  `K_min`
  ([`exists_isReinhardtMinimizer_isPontryaginExtremal_isWorstDisk`](SmoothedPolygons/Ch6/WorstDisk.lean#L250)). Layer 3 is Chapter 8 and
  Corollary A.1.3, with Theorem 16.3.1 conditional on one named hypothesis,
  [`NoChatteringIntoSingularLocus`](SmoothedPolygons/Ch16/MahlerFirst.lean#L107): the switching times of a Pontryagin extremal do not accumulate
  at a time where its lift meets the singular locus ([`theorem16_3_1`](SmoothedPolygons/Ch16/MahlerFirst.lean#L343); Section 2). It also derives
  the second sentence of Theorem 16.3.1, that `K_min` is a smoothed polygon, from the first,
  through the identification of E47 and the shape of a trajectory with finitely many switches
  (Remark 8.3.3, with Lemmas 7.2.1 and 3.1.8). Layer 4 is Chapter 13, the triangular Fuller
  system: its symmetries, the first control and the switching times, the singular locus, the
  blow-up, the Fuller–Poincaré map, its two fixed points with vanishing Hamiltonian (Lemma
  13.5.2) and the stability of `q_out` and instability of `q_in` (Lemma 13.5.5, [`lemma13_5_5`](SmoothedPolygons/Ch13/Stability.lean#L281)),
  with an exact Jacobian and a certified eigenvalue bound in place of the book's Mathematica
  computation (E68). It is the first of the chapters whose results discharge the hypothesis, which
  is unchanged. The later layers, planned, are to discharge it: Layer 5, the global basin of the
  Fuller system (Chapter 15 and Theorem 16.1.1), whose containments the book reads off computer
  plots, with its numerical facts stated first as named hypotheses and certified later; Layer 6,
  the analytic extension of Chapter 14 with the cluster point theorem 16.4.1, which needs a stable
  manifold theorem and Weierstrass preparation; and Layer 7, Theorem 14.4.1 (no return), whose
  proof rests on a numerical computation of an unstable curve, to be certified, and the final
  assembly. Once they are done, [`theorem16_3_1`](SmoothedPolygons/Ch16/MahlerFirst.lean#L343) applied to a proof of the hypothesis gives Mahler's First
  conjecture without hypotheses. The printed Theorem 8.2.7 for abnormal lifts (E55) is open and
  is not needed for it.
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
- **The reflection invariance of `𝔥*` (§4.6, Definition 5.0.1).** It can be read off the
  inequalities `|x| < 1/√3`, `x² + y² > 1/3` of the star domain, which are even in `x`. The formal
  proof, like §4.6, goes through the star functions (`S` permutes them) and Theorem 4.4.1, as it
  must for `R`.
- **Theorem 5.0.6.** Once the claim is applied corner by corner (Section 7), the step
  `h₀ ∩ h₁ ∩ h₂ = ∅` of the book's proof is not used; the formalization proves it
  ([`inter_hRegion_eq_empty`](SmoothedPolygons/Ch5/AreaBound.lean#L492)) but could drop it.
- **Lemma 5.0.7 (2).** No derivatives are needed. With `s = √3x`, `c = 3y² - 1`,
  `f(s) = (1 + s)(1 - s)²(s² + c)` and `w = √(1 - s²)`,
  `(√(2f(s)) + √(2f(-s)))² = 4w²(1 + c - w²)(1 + w)`, which increases with `w` for `c ≥ 1`, so
  `√(ρ₀ρ₁²ρ₂) + √(ρ₀²ρ₁ρ₂)` decreases in `x ≥ 0` while `(ρ₀ + ρ₁)ρ₂` increases. This proves (2) for
  `y² ≥ 2/3`, not only `y ≥ √3`. The formal proof follows the book's sign analysis of the
  derivatives, with its split at `x = 1/4`.
- **Lemma 6.1.2 in §6.1.** The convexity of the velocity sets, extended by the cost, can be seen
  directly: `[Z_u, X]/⟨Z_u, X⟩` is a linear-fractional function of `u` whose denominator is
  negative on `U_T` (Lemma 3.3.4), so it maps the convex `U_T` onto a convex set, and neither `gX`
  nor the cost depends on `u`. The formal proof follows the book (Lemma 6.1.2, carried to the
  matrix system by Lemma 4.5.2).
- **Lemma 8.2.1.** `Z_{e₁}`, `Z_{e₂}`, `Z_{e₃}` span `𝔰𝔩₂(ℝ)`, so if `⟨Λ, Z_u⟩/⟨X, Z_u⟩` is a
  constant `c` on `U_T`, then `⟨Λ - cX, Z_{e_i}⟩ = 0` for each `i` and `Λ = cX`; with `⟨Λ, X⟩ = 0`
  and `⟨X, X⟩ = -2 det X ≠ 0`, `c = 0` and `Λ = 0`. This needs neither the plane velocities nor
  Theorem 6.8.2; the formal proof follows the book's route through them (E52).
- **Theorem 8.1.4.** Finiteness of the switches needs no count of the zeros at which `λ₂' = 0`:
  every zero of `λ₂` is isolated (by `λ₂' ≠ 0`, or by Lemma 8.1.5), so the zero set, closed in the
  compact interval, is finite. The book's "at most two times", from `x' = y > 0`, is proved and
  used as the book uses it.
- **Theorem 8.3.1, claim (a).** Lemma 8.2.2 already gives the derivative of `Λ_R` at a zero:
  `Λ_R'(t₀) = -[Λ_{1,cost}(t₀), X(t₀)]`, so `Λ_R(t) = -(t - t₀)[Λ_{1,cost}(t₀), X(t₀)] +
  o(t - t₀)` without the Gronwall step (8.3.1), which only claim (b) needs. The formal proof
  follows the book, with the Gronwall step in both claims.
- **Straight edges in Remark 8.3.3.** That a plane curve with nonvanishing velocity `w` and zero
  curvature, `det(w, w') = 0`, lies on a line, which §7.2 uses without proof, has a proof without
  angle functions: `det(w(c), w)²/|w|²` has derivative
  `2 det(w(c), w)⟨w(c), w⟩ det(w, w')/|w|⁴ = 0`, so `det(w(c), w) = 0`, and then
  `det(w(c), σ - σ(c))` has derivative `0`. The formal proof uses it.
- **The first control of `q_out` (Lemma 13.5.2).** Lemma 13.2.6 gives it at once: at (13.5.1)
  `z₃⁰ < 0`, so `RR(z₃⁰, ζ) = RR(z₃⁰, ζ²) = -z₃⁰/2 > z₃⁰ = RR(z₃⁰, 1)`, and the tie is broken by
  `RR(z₂⁰, ζ) - RR(z₂⁰, ζ²) = √3 Im z₂⁰ > 0`, so `V_{T,max} = {ζ}`. The formal proof reads it off
  the signs of the switching functions on `[0, t_sw]`, which it needs anyway to show that `t_sw`
  is the first switching time (E67).

### The formalization

- **[`Basic/`](Basic)** holds general mathematics that belongs in Mathlib ([`Basic/README.md`](Basic/README.md) says where):
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
  of a cubic near `0⁺`; and the stability of fixed points of maps, with linearized stability
  (Lyapunov's first method for maps) and time reversal.
- **Two packages of their own** hold the general theory that this formalization needed and that
  others may import: OptimalControl
  ([github.com/vltanh/lean4-optimal-control](https://github.com/vltanh/lean4-optimal-control)),
  with control systems with Carathéodory trajectories (existence, uniqueness and differentiable
  dependence for measurable controls), Filippov's theorem and the existence of optimal controls
  (also under a closed state constraint, with a compact set of initial points and a closed endpoint
  relation), measurable selection, needle variations and the maximum principle; and FixedPoint
  ([github.com/vltanh/lean4-fixed-point](https://github.com/vltanh/lean4-fixed-point)), with
  Brouwer's fixed-point theorem. The project requires OptimalControl at a pinned commit, and
  OptimalControl requires FixedPoint.
- **Mathlib** lacks `det exp(A) = exp(tr A)` for matrices (a TODO in
  `Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean`), Jacobi's formula, Green's theorem for
  Jordan domains, the theory of regular elements of `𝔰𝔩₂`, any measurable selection theorem,
  Brouwer's fixed-point theorem, existence and uniqueness of Carathéodory solutions (its
  Picard–Lindelöf theorem needs continuity in time), and any notion of stability of a fixed point
  of a map, with the linearized stability theorem; each was a detour here. It also does not identify the bracket of its Lie algebra of
  left-invariant vector fields on `Mat₂(ℝ)ˣ` with the matrix commutator, so Propositions 3.6.1 and
  6.4.1 are applied in matrix coordinates (Section 6).
- **Filippov's theorem** needs no smoothness of `f` in `q`: continuity, bounded velocities and the
  convexity hypotheses suffice, so the standing assumptions `hfq`, `hfq'` that the statement keeps
  from the source (Section 5) could be dropped, and the theorem holds for any finite-dimensional
  state space (`OptimalControl.ODE.ControlSystem`, in the OptimalControl package, is stated so).
  Its form with a state constraint, used in §6.1, needs no compact support either: continuity,
  bounded velocities and convexity on the constraint set suffice.
- **Toward the main theorem.** With the maximum principle, the existence of a minimizer, Chapter 8
  and Chapter 13 proved, Chapters 14–16 still need the stable manifold theorem, Weierstrass
  preparation, and rigorous versions of the numerical containments of the global basin theorem
  (Theorem 16.1.1), which the book checks from Mathematica plots, and of the unstable curve of
  Theorem 14.4.1. Chapter 13 shows the pattern for the numerics: the book's Mathematica
  eigenvalues of Lemma 13.5.5 became an exact Jacobian in `ℚ(√3, r_scale)` with sign changes of its
  characteristic polynomial at rational points (E68).
