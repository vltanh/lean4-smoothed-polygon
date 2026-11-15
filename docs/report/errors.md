# Errors and gaps in the paper, missing and redundant hypotheses

Part of the [audit report](../../REPORT.md).

## Errors and gaps in the paper

The items come in groups, each in the book's order:

| Items | Where in the book |
| --- | --- |
| E1–E32 | Chapters 2–7 |
| E33 | the bibliography |
| E34–E37 | Chapters 3–7 |
| E38 | §6.6 |
| E39–E47 | §3.5, §4.6, Chapter 5 and §6.1 |
| E48–E61 | Chapter 8, Theorem 16.3.1 and Corollary A.1.3 |
| E62–E69 | Chapter 13 |
| E70–E80 | Chapter 15 and §16.1–16.2 |
| E81–E92 | Chapter 14, §16.3–16.4 and Appendix A.3 |
| E93–E94 | §14.4 |

[REPORT.md, Section 3](../../REPORT.md#3-errors-and-gaps-in-the-paper) indexes them by chapter.
"Section N" refers to the sections of [REPORT.md](../../REPORT.md), whose details are in the
other files of this directory.

### E1

**E1. Lemma 2.2.1, §2.2 (TeX 1317–1351): false.**

- **The book:** every lattice packing `K + L` of a centrally symmetric convex disk is realized by
  a parallelogram or centrally symmetric hexagon `H_K ⊇ K` whose translates by `L` tile the plane.
- **Counterexample:** `L = ℤ²` and `K = {y | |2y₀ + y₁| ≤ 1, |2y₁ - y₀| ≤ 1}`, a parallelogram of
  area `4/5` whose translates pack.
  - The half-lattice points `(±½, 0)`, `(0, ±½)` lie in the relative interiors of the four edges
    of `K`.
  - A convex `H ⊇ K` whose translates pack has none of them in its interior, so its support lines
    there are those of `K` and `H = K`, which does not tile (area `4/5 < 1 = det L`).
  - The book's expand–separate–crop process stops at `K` in this example.
  - A hexagonal variant (`K ∩ {|y₀| ≤ 11/20}`) fails the same way, so excluding parallelograms
    does not help.
  - The refutation is proved in Lean for every convex `H ⊇ K`
    ([`lemma2_2_1_false_as_printed`](../../SmoothedPolygons/Ch2/TilingCounterexample.lean#L297)).
- **Here:** the book uses the lemma only in Theorem 2.2.2, for which the classical form of
  Reinhardt's lemma suffices: there is such an `H ⊇ K` whose translates by `L` form a packing (so
  `area(H) ≤ det L`). With the user's approval, the formalization states and proves that form
  ([`lemma2_2_1`](../../SmoothedPolygons/Ch2/Reinhardt.lean#L2058), Section 7).

### E2

**E2. Theorem 2.2.2, §2.2 (TeX 1382–1392): gap.** The proof takes "a lattice that realizes"
`δ_L(K)` without showing that one exists. It exists: twice a critical lattice of `K` attains
`δ_L(K) = area(K)/(4Δ(K))`, and critical lattices exist (Mahler's compactness theorem in the plane,
proved here); with it the formalization follows the book's proof.

### E3

**E3. Remark 2.2.4, §2.2 (TeX ~1435): stated without proof.** That `K` contains an arc of the
hyperbola near each edge midpoint of a critical hexagon is observed, not proved. The formalization
proves it ([`remark2_2_4`](../../SmoothedPolygons/Ch2/Reinhardt.lean#L3055)): a hyperbola point outside `K` would give, by a separating line and an
AM–GM comparison of triangle areas, a circumscribed hexagon of smaller area.

### E4

**E4. Lemma 2.2.5, §2.2 (TeX 1507–1543): gaps; one not repairable along the book's lines.**

- **(a)** The existence of `K_min` "by the Blaschke selection theorem" needs more than selection
  (a normalization and the behaviour of `δ_L` in the limit). The formalization normalizes by
  linear maps and proves the one-sided bound it needs.
- **(b)** The proof that `K_min` has no corners shaves `K` near a boundary point that lies on no
  edge of a critical hexagon. This shows only that each face of `K` on a support line meets the
  boundary of some critical hexagon.
  - It gives nothing at an endpoint of a flat boundary segment that lies on an edge of a critical
    hexagon away from its midpoint, which the proof needs ("Each endpoint of the segment is the
    midpoint of an edge of a critical hexagon, for otherwise it can be shaved as above").
  - The regular hexagon shows the soft argument cannot rule this out.
  - The statement is true: the formalization proves it by Mahler's lattice route (Section 7).

### E5

**E5. Lemmas 2.2.6 and 2.2.7, §2.2 (TeX 1545–1720): smaller gaps.** Lemma 2.2.6's proof does not
treat a midpoint at the tip `s_j* + s_{j+1}*` of the triangle `T_j`; Lemma 2.2.7's "picking the
interval to be as large as possible" uses the closedness of the set of critical hexagons, which the
book asserts without proof in the proof of Lemma 2.2.5 (TeX 1520–1521).

The formalization fills both along the book's lines.

### E6

**E6. Definition 2.3.4, §2.3 (TeX 1766–1770): slip.** A critical lattice is defined as a lattice
whose determinant equals `Δ(K)`, without requiring it to be `K`-admissible. Read literally,
Theorem 2.3.6 is false (for the unit disk and `0 < ε < √3/2`, the lattice spanned by `(ε, 0)` and `(0, √3/(2ε))` has
determinant `√3/2 = Δ` but no basis on the boundary).

The sources (Minkowski, Mahler) require admissibility; the formalization does.

### E7

**E7. Theorem 2.3.9, §2.3 (TeX 1888–1916): a tacit fact and a slip.**

- **Tacit fact:** the proof takes a critical lattice `L̃` without recalling that one exists
  (Mahler's compactness theorem; proved in the plane,
  [`PlaneLattice.exists_admissible_covolume_le`](../../Basic/Algebra/Module/ZLattice/PlaneCritical.lean#L288)).
- **Slip:** it writes `4Δ(K) = det(2L) = area(H_K)` (TeX 1903) before showing that `L` is
  critical. At that point only `4 det(L) = det(2L) = area(H_K)` is known, and the next paragraph
  shows `det(L) = Δ(K)`.

That `H̃_K` is a centrally symmetric hexagon is part of Theorem 2.3.7 as the book states it, and
parallelograms are excluded by the convention of TeX 1356–1357. The formalization proves both, the
first because its statement of Theorem 2.3.7 omits it.

### E8

**E8. Lemma 2.4.2, §2.4 (TeX 2034–2085): a sign slip and a gap.**

- **Sign slip:** the proof says "In fact, `det(σ₀'(t), σ₂(t)) < 0`" (TeX 2058). It is positive
  (`σ₁ = σ₀ + σ₂` lies in `K`, to the left of the tangent at `σ₀`; for the circle it is `1/2`),
  and positivity is what makes the speed `s₂` positive.
- **Gap:** the proof concludes `σ₂ = σ̃₂` for the integral curve `σ̃₂` without showing that `σ̃₂`
  stays on the boundary; the formalization proves the differentiability of `σ₂` directly.

The statement allows any `C⁰` multi-curve on the boundary, which the proof identifies tacitly with
the critical-hexagon midpoints; the formalization proves the identification.

### E9

**E9. Lemma 2.4.3, §2.4 (TeX 2093–2148): proof sketch.** The proof recalls Hales 2011 in outline; a
comment in the TeX (line 2126) says the details of its final "now follows" are in handwritten notes.

The formalization fills it: the hyperbolic arc of Remark 2.2.4 bounds the turning of the tangent,
uniformly by compactness of the set of multi-points on the boundary with their support directions,
and local bounds give a global Lipschitz bound.

### E10

**E10. Lemma 2.4.5, §2.4 (TeX 2165–2202): index slip.** The bound on the side of the ray through
`s_j + s_{j+1}` is argued "Dually" (TeX 2181): pointing beyond it "would force `σ'_{j+2}(t)` to
point into `h_K`".

The index should be `j+1` (equivalently `j−2`, as `σ_{j+4} = −σ_{j+1}`): writing
`σ_k' = α_k s_{k+2} + β_k s_{k+1}`, differentiating `det(σ_j, σ_{j+1}) = √3/2` gives
`α_j = β_{j+1}`, so the step follows from the first part at `j+1`. The formalization follows the
book with the corrected index.

### E11

**E11. Lemma 2.4.6, §2.4 (TeX 2214–2235): a citation applied outside its hypotheses.** The proof
applies Shifrin's Proposition 3.8, a theorem about simple closed curves with everywhere-defined
curvature (at least `C²`), to curves that are only `C¹` with Lipschitz derivative. The formalization proves the inequality directly (each tangent
line supports `K`; second-derivative test), so the citation is not used.

### E12

**E12. Problem 2.4.8 and the smoothed octagon's density (TeX 2289–2292, 6348): a fact used but not
proved.**

- **The book:** it normalizes the critical hexagon of `K_min` to area `√12` "by convention" and
  then treats the area of any balanced disk divided by `√12` as its density:
  - TeX 3994: "Also associated with `K` is a critical hexagon `H_K` with midpoints at the points
    `{s_j*}`";
  - Lemma 5.0.3, TeX 4006–4008;
  - the density bound at TeX 4341–4346;
  - the density of the smoothed octagon, TeX 6348 and 6355.
- **The gap:** that a balanced disk has least circumscribed hexagon of area `√12`, so that
  `δ(K) = area(K)/√12`, is never shown.
- **Here:** it is true: the formalization proves it for every balanced pair
  ([`greatestPackingDensity_of_isBalancedPair`](../../SmoothedPolygons/Ch2/BalancedDensity.lean#L235)). The chords of `K` parallel to a boundary point `u`
  have a concave even length function of the height, so the parallelograms inscribed on `u` all
  have the same area.

Chapter 5 and the identification with `K_min` use it too (E42, E47).

### E13

**E13. Theorem 3.1.4(3), §3.1 (TeX 2414–2442): missing hypothesis.**

- **The book:** for a convex disk whose boundary is parameterized by a regular `C¹` multi-curve
  `σ`, the curve `X = g⁻¹g'` is Lipschitz.
- **Counterexample:** this is false in that generality. The unit disk with
  `σ_j(t) = Rot(θ(t)) s_j*`, `θ(t) = t + t^{3/2}`, is such a parameterization, and
  `X = θ'(t) J = (1 + (3/2)√t) J` is not Lipschitz at `0`.
- **The gap:** the proof cites Lemma 2.4.3, which gives Lipschitz tangents for the minimizer
  `K_min` parameterized by arclength, the standing assumption of §2.4. The "circle representation"
  hypothesis that a TeX comment says was removed (TeX 2413–2415) would not help: the counterexample
  is in circle representation.
- **Here:** the theorem holds when the tangents `σ_j'` are Lipschitz, as for balanced disks
  (Definition 2.4.7, item 2), and that is how the book uses it. The formalization proves (the user
  approved this reading):
  - parts (1) and (2) without the hypotheses they do not need
    ([`theorem3_1_4`](../../SmoothedPolygons/Ch3/StateDynamics.lean#L258), Section 5);
  - part (3) under the hypothesis that each `σ_j'` is Lipschitz
    ([`theorem3_1_4_lipschitz`](../../SmoothedPolygons/Ch3/StateDynamics.lean#L283)).

### E14

**E14. Proof of Theorem 3.4.2, §3.4 (TeX 3055): index slip.** "Let `κ = κ₁ + κ₂ + κ₃`" should be
`κ₀ + κ₁ + κ₂` (Definition 3.3.2). The proof is otherwise correct.

### E15

**E15. Problem 3.6.2, §3.6 (TeX ~3205), and §6.1 (TeX 4579): a converse used but not proved, and
false in general.**

- **The book:** "The convex disks in `𝔎_bal` in circle representation arise via the following
  optimal control problem". It derives the problem from balanced disks and does not show the
  converse, that an admissible trajectory bounds a balanced disk whose area is its cost; in
  particular that its curve is simple.
- **Where it is used:** §6.1 needs the converse to apply Theorem 5.0.2, a statement about balanced
  disks, to the trajectories of the control problem (E46).
- **It is false:** the boundary conditions, chosen so that "the curves `σ_j` close up seamlessly to
  form a simple closed curve" (TeX 3135–3139), do not force simplicity, and an admissible trajectory
  may wind `1 + 6m` times around the origin.
  - The unit circle traversed seven times (`X ≡ J`, `u ≡ (1/3, 1/3, 1/3)`, `t_f = 7π/3`) is
    admissible, has cost `7π`, and is not the boundary trajectory of any balanced pair
    ([`exists_isReinhardtAdmissible_not_isWindingOne`](../../SmoothedPolygons/Ch6/Winding.lean#L550)).
  - The book meets the phenomenon in the proof of Lemma 7.5.5, where other eigenvalues "will
    produce the right boundary conditions, but the corresponding multi-curves `σ_i` will have the
    wrong winding number around the origin" (TeX 6323–6326).
- **Winding number one:** the converse holds for trajectories of winding number one
  ([`IsWindingOne`](../../SmoothedPolygons/Ch6/Winding.lean#L82); [`exists_isBalancedPair_of_isReinhardtAdmissible`](../../SmoothedPolygons/Ch6/AdmissibleDisk.lean#L937)). The argument is the one that
  proves it for the smoothed `(6k+2)`-gons ([`smoothedPolygonDisk_spec`](../../SmoothedPolygons/Ch7/SmoothedPolygonDisk.lean#L1392); simplicity by a
  winding-number argument), generalized to any measurable control.
- **Higher winding costs more:** the cost is at least `3/2` times the angle swept by
  `σ₀ = g s₀*`, so a trajectory of winding number `1 + 6m` costs at least `π/2 + 3πm`
  ([`three_halves_mul_angle_le_reinhardtCost`](../../SmoothedPolygons/Ch6/Winding.lean#L447)). This bound is not in the book; its proof is a pointwise
  inequality.
  - Let `ψ` be the polar angle of the bottom row `(g₁₁, g₁₀)` of `g`, which ends where the angle
    of `σ₀` ends.
  - Then `κ = -tr(JX)` (the cost is `(3/2)∫κ`) satisfies `κ ≥ ψ'`, because
    `c(κ - ψ')(p² + q²) = (cp - aq)² + q² det X` for `X = [[a, b], [c, -a]]`,
    `(p, q) = (g₁₀, g₁₁)`, and `c > 0` on star states.
  - So every admissible trajectory cheaper than `7π/2` has winding number one
    ([`isWindingOne_of_reinhardtCost_lt`](../../SmoothedPolygons/Ch6/Winding.lean#L497)), in particular every one at most as costly as the
    smoothed octagon, which is all §6.1 needs.

Remark 8.3.3 takes the converse for granted again, for extremals that avoid the singular locus, and
the formalization takes the disk there as a hypothesis; it exists for the global minimizer (E58).

### E16

**E16. Problem 3.6.2, §3.6 (TeX 3235): misprint in a definition.** The terminal condition is
printed `X(t_f) = R X₀ R⁻¹`.

- The derivation just before (TeX 3152–3156), the half-plane form (TeX 3606), the transversality
  conditions (TeX 5207) and the remark after them (TeX 5221) all give `X(t_f) = R⁻¹ X₀ R`, and the
  two differ because `Ad_R` has order 3.
- For the smoothed octagon, `X(t_f) = R⁻¹X₀R`, and `R⁻¹X₀R - RX₀R⁻¹ = diag(δ, -δ)` with
  `δ ≈ 0.433`.
- The formalization uses `R⁻¹X₀R` ([`IsReinhardtAdmissible`](../../Challenge.lean#L387),
  [`IsPontryaginExtremal`](../../Challenge.lean#L214)).

### E17

**E17. Lemma 4.2.3, §4.2 (TeX 3382): missing hypothesis `X ≠ 0`.** Lemma 4.2.3 is stated "for
any `X ∈ 𝔰𝔩₂(ℝ)`": `T_X O_X = {[Y, X]} ≅ 𝔰𝔩₂(ℝ)/ℝX`. For `X = 0` the orbit is a point and
`𝔰𝔩₂/ℝ·0 = 𝔰𝔩₂` is three-dimensional.

The proof uses that `X` is regular, which in `𝔰𝔩₂` means `X ≠ 0`, and the lemma is applied to
`X ∈ O_J`. The formalization adds `X ≠ 0` ([`lemma4_2_3`](../../SmoothedPolygons/Ch4/AdjointOrbit.lean#L432)).

It also states Lemma 6.8.1 for nonzero traceless `X` ([`lemma6_8_1`](../../SmoothedPolygons/Ch6/HalfPlane.lean#L34)); there the book's
context already has `X = Φ(z) ∈ O_J` (TeX 5296–5301), so this is a reading (Section 6), not an
error.

### E18

**E18. Lemma 4.2.3, §4.2 (TeX 3394–3420): a standard fact used without proof.**

- **The gap:** the proof shows that the vectors `[Y, X]` are tangent to the orbit ("this
  calculation is actually finding infinitesimal generators of the adjoint action", TeX 3410), but
  not that every tangent vector is of this form. That is the standard fact that the orbit map is a
  submersion onto the orbit.
- **Here:** the formalization proves it for its tangent space of velocities of curves. Along a
  curve in the orbit the trace and the determinant are constant, so the velocity `V` is traceless
  with `⟨V, X⟩ = 0`, and `X^⊥ = {[Y, X]}` by a dimension count ([`orb_adImage_eq_perp`](../../SmoothedPolygons/Ch4/AdjointOrbit.lean#L388)).

### E19

**E19. Lemma 4.3.1, §4.3 (TeX 3514–3530): gap.** "The global minimizer has area less than the
area `π` of the unit circle" is not justified.

- The unit disk itself is an admissible trajectory (`X ≡ J`, constant control `(1/3, 1/3, 1/3)`,
  `t_f = π/3`, cost `π`), so minimality gives only `area ≤ π`, and the bound `t_f < π/3` needs the
  strict inequality.
- It follows from the smoothed octagon, whose area `≈ 3.126 < π` the book computes in §7.5; the
  formalization uses that comparison (Section 7). The lemma is true.
- §6.1 uses it to bound the terminal time of every competitor before a minimizer is known to
  exist. The formalization uses instead the lemma's other step, that the cost density is at least
  `3` on star states, stated for every state trajectory
  ([`three_mul_le_reinhardtCost`](../../SmoothedPolygons/Ch4/TerminalTime.lean#L71); E46).

### E20

**E20. Problem 4.5.1, §4.5 (TeX 3631): sign misprint.** The coefficients of the half-plane control
problem are defined as "`a = a(u) = (u₂ - u₁)/√3`, `b = …`, `c = …`, the following affine
functions of the control (`eqn:trisystem-Z0`)".

The entry of `Z_u` in `eqn:trisystem-Z0` is `(u₁ - u₂)/√3`; with the printed sign the formulas for
`x'` and `y'` are wrong and Lemma 4.5.2 fails (checked symbolically). The formalization uses the
entries of `Z_u` ([`halfPlaneF₁`](../../SmoothedPolygons/Ch4/StarDomain.lean#L61), [`halfPlaneF₂`](../../SmoothedPolygons/Ch4/StarDomain.lean#L69)).

### E21

**E21. §6.2 and Problem 6.7.1 (TeX 4764–4766, 4818–4820, 5248–5250): a degenerate nontriviality
condition.**

**The book's condition.** The book poses the control problem on `M = SL₂(ℝ) × 𝔰𝔩₂(ℝ)`, with
costate `p = (Λ₁, Λ₂) ∈ 𝔰𝔩₂ × 𝔰𝔩₂`, and the maximum principle requires `(λ_cost, p(t)) ≠ 0`.

- With that condition every admissible trajectory lifts to a Pontryagin extremal:
  `(λ_cost, Λ₁, Λ₂) = (0, 0, X)` satisfies the costate equation `Λ₂' = -δH/δX = [P, X] = X'`,
  gives `Λ_R = [Λ₂, X] = 0` and hence `H ≡ 0` for every control.
- So the maximum condition and the transversality conditions (eqn:transversality) hold, and
  `(λ_cost, p) ≠ 0` because `det X = 1`. Read literally, Theorem 7.5.6 would then hold for every
  admissible trajectory.
- On the book's `M = SL₂(ℝ) × 𝔰𝔩₂(ℝ)` the covector `Λ₂ = X` is not zero, but it vanishes on the
  tangent space `T_X O_J = X^⊥` of the orbit on which `X` moves, so it says nothing about the
  trajectory. The book's reduced costate `Λ_R = [Λ₂, X]` (Remark 6.5.2) discards exactly this part.
- **Here:** the formalization imposes nontriviality on `(λ_cost, Λ₁, Λ_R)`
  ([`IsPontryaginExtremal`](../../Challenge.lean#L214)), the only reading under which Theorem 7.5.6 has content.

**The derivation.** The same degeneracy blocks the derivation of this condition from the maximum
principle (§6.2), and there the repair is in the boundary conditions.

- Applied with `g(0) = I₂`, `g(t_f) = R` and `X(t_f) = R⁻¹X(0)R` in full, the conclusions of the
  maximum principle hold, for every admissible trajectory, with `λ_cost = 0` and `Λ₂ = cX` (from
  the first integral `det X`).
- On the open set `GL₂⁺(ℝ) × C` of `Mat₂(ℝ) × 𝔰𝔩₂(ℝ)` on which the formalization applies it
  (Section 6), they also hold with `pg = kI₂` (from the first integral `det g`).
- The reduced costate of these covectors vanishes, so the nontriviality of `(λ_cost, Λ₁, Λ_R)`
  cannot be derived.
- Because `det g` and `det X` are constant, the equations `g(t_f)₁₁ = R₁₁` and
  `X(t_f)₁₀ = (R⁻¹X(0)R)₁₀` follow from the others (with `det g(0) = det X(0) = 1`, `R₀₀ ≠ 0` and
  `X₀₁ < 0` on `C`), so leaving them out changes no admissible trajectory
  ([`isReinhardtAdmissible_of_mem_matrixEndpoints`](../../SmoothedPolygons/Ch6/MatrixMinimizer.lean#L297)).
- The formalization applies the maximum principle with the boundary condition without them
  ([`matrixBoundary`](../../SmoothedPolygons/Ch6/MatrixSystem.lean#L136)). Transversality in the two directions this frees gives `p(t_f)₁₁ = 0` and
  `Λ₂(t_f)₀₁ = 0`, which exclude these covectors ([`eq_zero_of_covectorΛ_eq_zero`](../../SmoothedPolygons/Ch6/MatrixCostate.lean#L526)).
- The nontriviality of the reduced costate follows: if `λ_cost = 0` and `Λ₁, Λ_R` vanish at one
  time, they vanish identically (Corollary 6.5.3 and the linear `Λ_R` equation), so the covector
  vanishes at `t_f` ([`exists_isPontryaginExtremal_of_isReinhardtMinimizer`](../../SmoothedPolygons/Ch6/MatrixExtremal.lean#L564); Section 7).

**Chapter 8 depends on this reading.**

- Lemma 8.2.2 (TeX 7163–7166) and the proof of Theorem 8.3.1 (TeX 7583–7584) obtain `λ_cost ≠ 0`
  at a time where `Λ_R = Λ_R' = 0` from "the non-vanishing of the costate variables in the maximum
  principle", that is, from the nontriviality of `(λ_cost, Λ₁, Λ_R)`.
- Under the book's condition on `(λ_cost, Λ₁, Λ₂)` this step fails: the spurious lift `(0, 0, X)`
  above has `Λ_R ≡ 0` and `λ_cost = 0`, so Lemma 8.2.2 would be false, and Theorem 8.2.3 would make
  every admissible trajectory a circular arc.
- Under the formalization's condition both hold as printed ([`lemma8_2_2`](../../SmoothedPolygons/Ch8/SingularLocus.lean#L783),
  [`theorem8_3_1`](../../SmoothedPolygons/Ch8/FiniteBangBang.lean#L1288)).
- The corresponding step for the edge control problem (the proof of Theorem 8.1.4, TeX 6871–6874)
  concerns that problem's own costate `(λ₁, λ₂, λ₃)`, and holds as printed.

### E22

**E22. Proof of Proposition 6.5.1, §6.5 (TeX 5030–5040): sign convention.**

- **The book:** the proof writes the Euler–Arnold equation as `Λ₁' = ad*_{δH/δΛ₁} Λ₁ = -ad_X Λ₁`,
  identifying `𝔰𝔩₂*` with `𝔰𝔩₂` by the trace form "sending `ad*` to `ad`".
- **The slip:** with the book's definition of `ad*` (Appendix A.4, TeX 13314:
  `⟨ad*_Z Y, X⟩ = ⟨Y, -ad_Z X⟩`) this identification sends `ad*_Z` to `+ad_Z`, which would give
  `Λ₁' = [X, Λ₁]`.
- **The equation is right:** the equation `Λ₁' = [Λ₁, X]` that the book uses is the correct one.
  In matrix coordinates on `T*GL₂`, `p' = -Xp` and `Λ₁ = pg` give `Λ₁' = [Λ₁, X]`, and it is the
  equation whose solution is `Λ₁(t) = g(t)⁻¹ Λ₁(0) g(t)` (Corollary 6.5.3).
- **Here:** the formalization proves the Euler–Arnold equation in exactly this form,
  `μ' = [μ, δh/δμ]` for `μ = pg` ([`External.euler_arnold`](../../External/EulerArnold.lean#L72)), and applies it in
  [`proposition6_5_1`](../../SmoothedPolygons/Ch6/Hamiltonian.lean#L319).

### E23

**E23. Theorem 6.8.3, §6.8 (TeX 5385–5402): omitted proof.** The book omits "the long direct
calculation" and refers to Vajjha's thesis. The formalization does the calculation
([`theorem6_8_3`](../../SmoothedPolygons/Ch6/HalfPlane.lean#L304)); the theorem is true (with the corrected sign of E20).

### E24

**E24. Discussion before Lemma 7.2.1, §7.1 (TeX 5550–5563): misprint.** The columns of
`A = (v₊, v₋)` are called the eigenvectors of `Z₀` "associated to the positive and negative
eigenvectors"; read "eigenvalues".

- Since `⟨Z₀, X₀⟩ < 0` (for `e₃` it is `-2/(3y₀)`), the eigenvector of `P₀ = Z₀/⟨Z₀, X₀⟩` for its
  positive eigenvalue `λ` belongs to the negative eigenvalue of `Z₀`. So `v₊` is the eigenvector of
  `P₀` (equivalently of `-Z₀`, as §7.2 uses) for `λ`.
- With the eigenvectors listed in §7.2, `det(v₊, v₋)` is `-2/√3` for `(1, 0, 0)` and `-1` for
  `(0, 1, 0)`, so one vector must be rescaled, by a negative factor, to get `A ∈ SL₂(ℝ)`. Only the
  points `[v±]` are used, and the argument is unaffected.
- The formalization rescales (`exists_eigenvector_matrix` in the proof of
  [`lemma7_2_1`](../../SmoothedPolygons/Ch7/ConstantControl.lean#L349)).

### E25

**E25. Lemma 7.2.1, §7.2 (TeX 5747–5756): proof in the preceding discussion.** The proof
environment is empty; the argument is the discussion of §7.1–7.2 (Möbius images of rays). The
formalization follows that discussion, with the uniqueness of the constant-control solution,
which the discussion uses implicitly, proved.

### E26

**E26. Lemma 7.3.1, §7.3 (TeX 5771–5792): missing hypothesis `⟨X, Z_u⟩ ≠ 0` on `U`.**

- **The book:** the lemma takes any compact convex control set `U` in the plane
  `u₀ + u₁ + u₂ = 1`, but the Hamiltonian `H = ⟨Λ₁ - (3/2)λ_cost J, X⟩ - ⟨Λ_R, Z_u⟩/⟨X, Z_u⟩` is
  undefined where `⟨X, Z_u⟩ = 0`, and the proof uses a "nonzero denominator" (TeX 5792).
- **The gap:** for a star state `X`, `⟨Z_u, X⟩ = -(2/√3)(ρ₂u₀ + ρ₁u₁ + ρ₀u₂)` with
  `ρᵢ = ρᵢ(X) > 0`. It is negative on `U_T` (Lemma 3.3.4), but unless `ρ₀ = ρ₁ = ρ₂` it vanishes
  on a line of the plane, and on a segment `U` crossing that line the Hamiltonian is undefined at
  the crossing point.
- **Here:** for `U ⊆ U_T`, the case the book uses, the condition holds. The formalization adds it
  (`hden` in [`lemma7_3_1`](../../SmoothedPolygons/Ch7/Faces.lean#L49)).

### E27

**E27. Theorem 7.5.1 and Lemma 7.5.3, §7.5 (TeX 6099, 6206–6214): notation.** The theorem requires
`χ₂₃(0) = 0`, the lemma speaks of `χ₃₂(0) = 0`. They are equivalent (`χ₂₃(0) = -χ₃₂(0)`).

### E28

**E28. Lemma 7.5.3, §7.5 (TeX 6230–6275): the discarded factor depends on `t`.** The book reduces
`χ₃₂ ≥ 0` to `f(y, r) ≥ 0` "discarding obviously positive multiplicative factors". The factor is
`χ₃₂/f = 2√3/(r(2y - r)(y - 1)^{3/2})`, which depends on `t` through `r = y e^{√3 y₀ t}` and is
positive because `r ≤ 4 < 2y` on the interval.

Correct, but not obvious; the formalization proves the identity ([`chi32_eq`](../../SmoothedPolygons/Ch7/StrongTransversality.lean#L1007)).

### E29

**E29. Lemma 7.5.3, §7.5 (TeX 6265–6273): gap.** The proof needs `∂²f/∂y² ≥ 0` on the triangle
`T = {2 ≤ y ≤ r ≤ 4}` and leaves it "as a tedious but elementary exercise". The inequality is true
but tight: `∂²f/∂y²` vanishes at the corner `(4, 4)`.

The formalization proves it ([`hmax_deriv2_nonneg`](../../SmoothedPolygons/Ch7/HMaxInequality.lean#L234), [`hmax_deriv2_pos`](../../SmoothedPolygons/Ch7/HMaxInequality.lean#L156)), writing
`∂²f/∂y² = A(y) + r(c(y) + 4 ln(r/y))`:

- the case `y ∈ [3, 4]` follows from the tangent line of `r ln r` at `r = 4` and the bound
  `ln u ≥ 2(u - 1)/(u + 1)`, which reduce it to
  `(4 - r)y(10y - 24) + (r - y)(5y² - 10y + 8) ≥ 0`;
- the case `y ∈ [2, 3]` follows from the minimum in `r` (at `r* = 2√y e^{(y-2)/(4y)}`),
  `e^x ≤ 1/(1 - x)`, `3√y ≤ y + 9/4`, the same bound on `ln(4/y)`, and the certificate
  `-77y³ + 364y² - 252y - 240 = 96(3 - y) + 201(y - 2) + (y - 2)(3 - y)(77y + 21) > 0`.

The lemma is true, with the strictness the book states. (Remark 7.5.4, TeX 6283, calls `(4, 4)`
"the corner `r = y = 4` of the disk"; read "triangle".)

### E30

**E30. Lemma 7.5.5, §7.5 (TeX 6287–6334): direction and a tacit step.**

- **Direction:** the lemma is stated as "`g(t_f) = R`, provided `4/(3y₀² + 1) = 2 cos θ_k`"; the
  proof argues the other direction (comparing eigenvalues, then choosing `ℓ = 0, -k`).
- The sufficiency follows from the same eigenvalue comparison, run in the stated direction (with
  `sin θ_k ≠ 0`, the eigenvalues `e^{±iθ_k}` are distinct, so `R⁻¹g_sw` is diagonalizable), and the
  formalization proves the statement as printed in this way.
- **Tacit step:** the proof also takes for granted that a trajectory with the given control and
  initial values is the spline; the formalization proves this uniqueness.

The proof's formula `(R⁻¹ g_sw)^{3k+1}` and the spline's `(g_sw R⁻¹)^{3k+1}` are conjugate; either
works.

### E31

**E31. Theorem 7.5.6, §7.5 (TeX 6359–6372): gap.** The proof checks only the transversality
conditions at `t_f`. The book leaves the rest implicit:

- that the conjugated costates are continuous at the switching times, satisfy the costate
  equations, keep `H = 0` and maximize the Hamiltonian on every switching interval follows from the
  rotational symmetry and Lemma 7.5.3;
- the reduction of the maximization over `U_T` to its vertices follows from the form of the
  Hamiltonian (Lemma 7.3.1).

The formalization proves all of this ([`poly_isPontryaginExtremal`](../../SmoothedPolygons/Ch7/SmoothedPolygon.lean#L255)).

### E32

**E32. Theorem 7.7.1, §7.7 (TeX 6543–6623): false read literally; the proof is a sketch.**

**(a) The statement.** The theorem says that "in some neighborhood of the set of initial
conditions in the cotangent space, the only extremal trajectory satisfying the transversality
conditions at the endpoints is that of the smoothed octagon". Read literally, this fails in two
ways:

- The octagon's lift started at a time `s` (with `g(t) = g_oct(s)⁻¹g_oct(s + t)`) is another
  extremal satisfying all the transversality conditions, and its initial condition tends to the
  octagon's as `s → 0`.
- The octagon's lift on `[0, 28t_sw]` (seven turns) satisfies them too, with the same initial
  condition as on `[0, t_f] = [0, 4t_sw]`.

The costate is moreover determined only up to a positive factor.

- **Here:** with the user's approval, the formalization reads the theorem up to time translation,
  for terminal times near `t_f`, and in a conic neighbourhood of the octagon's initial condition
  normalized by `λ_cost = -1` ([`theorem7_7_1`](../../SmoothedPolygons/Ch7/Isolated.lean#L508)).
- An extremal with `|T - t_f| < ε` whose initial condition lies in the cone over the neighbourhood
  is the octagon's lift started at some `s ∈ [0, 3t_sw)`, with costate `-λ_cost` times the
  octagon's; in particular `T = t_f` and `λ_cost < 0`.
- The octagon's own lift meets the hypotheses ([`theorem7_7_1_octagon`](../../SmoothedPolygons/Ch7/Isolated.lean#L633)), so the statement is not
  vacuous.
- The book's proof also works up to time translation, on a Poincaré section, and only with four
  switching intervals (eqn:fp).

**(b) The proof is a "proof sketch".**

- It considers the Poincaré map `f(q₀) = Ad(R)q(t_sw(q₀), q₀)` on a section `χ_ij = 0` of the
  manifold `M_d` where `det Λ₁ = d` (the formalization takes `χ₂₃ = 0`).
- It rests on "Direct calculation shows that the fixed point `q_oct` is hyperbolic" (TeX 6612),
  which the book does not give.
- It leaves these gaps, all filled in the formalization (the module docstring of
  [`SmoothedPolygons.Ch7.Isolated`](../../SmoothedPolygons/Ch7/Isolated.lean) lists them with the steps that fill them):
  - an extremal near the octagon need not start on the section, so it must be restarted where it
    crosses it;
  - that nearby extremals are bang-bang with the octagon's switching sequence is not argued (it
    needs the strict inequality of Lemma 7.5.3 at the third vertex, the exclusion of singular arcs
    and chattering at the switching points, and continuous dependence for the discontinuous
    extremal dynamics);
  - Remark 7.5.4 asserts only that the slope of `χ₃₂` at `0` is positive, whereas the Poincaré
    time needs the transversal zero of `χ₃₁` at `t_sw`, which follows from the symmetry
    `χ₃₁(t_sw - t) = χ₃₂(t)` of the proof of Lemma 7.5.3 (TeX 6220);
  - the parameter `y₀(d)` comes from Remark 7.5.2, which the book does not prove (E36);
  - the last step, "the only fixed point `q_fix(d)` satisfying (eqn:theta-k) is `q_oct`", uses
    Lemma 7.5.5 in the converse direction, which follows from the eigenvalue comparison of its
    proof (E30), as in the formalization.
- **The direct calculation is supplied:** on the four-dimensional tangent space of the section the
  derivative of `f` has an explicit matrix whose characteristic polynomial is reciprocal, with
  multipliers `≈ -7.7464, -2.1122, -0.4734, -0.1291`, and two certified inequalities show that none
  has modulus `1`.
- **Uniformity in `d`:** the step "by the implicit function theorem, for each `d` near `d_oct`, the
  function `f_d⁴ - I` can be inverted in an open neighborhood of the fixed point `q_fix(d)` ...
  Thus, the only fixed points near `q_oct` are the fixed points `q_fix(d)`" (TeX 6615–6620) needs
  neighbourhoods uniform in `d`, which a separate application for each `d` does not give.
  - The formalization applies the inverse function theorem once, at `q_oct` (Section 7).
- **Sign:** the proof writes the switching functions as `χ_ij = ⟨Λ_R, P_i - P_j⟩` (TeX 6573), the
  opposite sign of eqn:switch (TeX 6072–6078); this is harmless, as only their zeros are used.

### E33

**E33. Bibliography and history.**

- **Tammela:** Tammela's bound is from 1970 (*Izv. Vyssh. Uchebn. Zaved. Mat.* 1970, no. 12(103),
  103–107); the bibliography prints 1969 and gives the running issue number 103 as the volume.
- **Ennola:** the text's "Ennola in 1961 and Tammela in 1969 showed `inf δ ≥ 0.8926…`" (Chapter 1)
  credits Tammela's bound to both: Ennola proved about `0.88`.
- **Nazarov and Kupka:** the book cites the 1988 English translation of Nazarov's 1986 paper
  (*Zap. Nauchn. Sem. LOMI* 151) and a 2017 reissue of Kupka's 1990 paper.
- **Agrachev and Sachkov:** the entry `zelikin2004control`, which the book cites for the Pontryagin
  maximum principle (TeX 737, 4674), is A. A. Agrachev and Yu. L. Sachkov, *Control Theory from the
  Geometric Viewpoint* (Springer, 2004); the bibliography lists M. I. Zelikin as its first author
  and Sachkov twice.
- **Minkowski and Mahler:** Theorem 2.3.6 is attributed to "Minkowski
  [`minkowski1907diophantische`], Mahler [`mahler1946lattice`]" (TeX 1789).
  - The cited communication of Mahler (*Lattice points in n-dimensional star bodies II.
    Reducibility theorems I*, Proc. KNAW 49 (1946) 331–343) only quotes, without proof and
    crediting Minkowski, the six-point statement (A) (p. 340).
  - Statement (A): every critical lattice of a convex domain in the plane has at least six points
    on its boundary, and in suitable coordinates exactly six are `(1, 0)`, `(0, 1)`, `(−1, 1)` and
    their negatives.
  - It states neither the theorem's form, with a basis and the area of the parallelogram, nor its
    converse; the converse is asserted ("as is easily seen") in the second communication of the
    series (p. 444).
  - The book's wording matches Lemma 3 of Mahler's paper A (p. 101; Section 2).
  - The formalization follows Minkowski and Mahler 1947, Lemma 2
    ([`External.minkowski_mahler`](../../External/MinkowskiMahler.lean#L964)).

These do not affect the mathematics.

### E34

**E34. Lemma 3.1.8, §3.1 (TeX 2554–2579): missing hypothesis; two gaps.**

- **The book:** the lemma assumes that the boundary of `K` "is parameterized by a `C¹` multi-curve
  `σ`".
- **Counterexample:** without regularity it is false, for the square `[-λ, λ]²` with `λ² = √3/2`.
  - There is a `C¹` multi-curve on the boundary in which `σ₂ = (-λ, 0)` is constant while `σ₁` and
    `σ₃ = -σ₀` slide along the parallel edge lines `y = λ` and `y = -λ`.
  - Continued around the square, one pair `±σ_j` at rest at a time, it parametrizes the whole
    boundary.
  - No hyperbola has parallel asymptotes.
- **Here:** §2.4 parameterizes the boundary "by a regular `C¹` curve" (TeX 1945–1946); with the
  user's approval, the formalization assumes that every `σ_j` is regular, `σ_j' ≠ 0`
  ([`lemma3_1_8`](../../SmoothedPolygons/Ch3/HyperbolicArc.lean#L772), Section 4).
- **The proof** then follows the book's: the tangent lines at the multi-point cut out a hexagon
  `H_K(t)` with edge midpoints `σ_j(t)` and area `√12`, the parallelogram `P_K` has constant area,
  and Reinhardt's observation on the pencil of lines cutting a constant area.
- **Two gaps filled:**
  - the book takes the lines traced by `±σ_{i-1}` and `±σ_{i+1}` to bound a parallelogram, that
    is, the lines of `σ_{i-1}` and `σ_{i+1}` not to be parallel;
  - it does not show that the hyperbola is nondegenerate (its constant is not `0`).

  Both follow from regularity: each line supports `K`, and in either degenerate case one of the
  curves would be constant.

### E35

**E35. Theorem 6.1.1 (Filippov), §6.1 (TeX 4538–4546): missing hypothesis; no source.**

- **The book:** for `q' = f(q, u)` on a manifold, with compact control set `U`, convex velocity
  sets `f(q, U)` and `f` of compact support, the theorem asserts that "the attainable sets are
  compact and an optimal control exists" for the cost `∫φ(q, u) dt`.
- **Counterexample:** the second claim fails when `φ` depends on `u`. On `ℝ`, take `q' = uψ(q)`,
  `U = [-1, 1]` and a bump `ψ` equal to `1` on `[-1, 1]`.
  - The cost `∫₀¹ (q² + 1 - u²) dt` from `q(0) = 0` to `q(1) = 0` has infimum `0` (chattering
    controls `u = ±1`).
  - It has no minimizer: cost `0` forces `q = 0`, hence `u = 0` almost everywhere, of cost `1`.
- **Here:** it holds when the extended velocity sets `{(f(q, u), φ(q, u)) | u ∈ U}` are convex,
  which is the book's hypothesis when `φ` depends only on the state, as the Reinhardt cost
  `-(3/2)⟨J, X⟩` does. With the user's approval the formalization states it so, on `ℝⁿ`, for fixed
  and free terminal time ([`External.filippov`](../../External/Filippov.lean#L153); Sections 4 and 6).
- **No source:** §6.1 cites no source for the theorem; Hales's 2017 preprint cites it as Theorem
  10.1 of Agrachev and Sachkov's book, the entry `zelikin2004control` of the bibliography (E33).

The problem to which §6.1 applies the theorem is not covered by it, even corrected; a form with a
closed state constraint is (E46).

### E36

**E36. Remark 7.5.2, §7.5 (TeX 6185–6203): stated without proof.**

- **The book:** the remark says that `d(y₀) = det Λ₁` is a constant of motion, given by an explicit
  formula, and that `d` is increasing on `(1/√3, 1)` with range `(0, 9/4)`, so that it determines
  `y₀`. The proof of Theorem 7.7.1 uses this to define `y₀(d)` (TeX 6581).
- **The gap:** the book gives no proof; a comment in the TeX source (TeX 6199–6201) says that "the
  derivative factors in a nice way".
- **Here:** the formalization follows that hint ([`remark7_5_2`](../../SmoothedPolygons/Ch7/Remarks.lean#L214)): `d' = E·F/(36y⁹)` with
  `E = 3 + 6y² - (1 + 3y²)ℓ`, `F = 2ℓ(3y⁴ - 1) + 9y⁶ - 9y⁴ - 6y² + 6` and `ℓ = ln(4/(3y² + 1))`,
  and `E, F > 0` on the interval by the bounds `ln x ≤ x - 1` and `ln x ≥ 2(x - 1)/(x + 1)` for
  `x ≥ 1`.

The remark is true.

### E37

**E37. Remarks 7.6.2 and 7.6.4, §7.6 (TeX 6402–6438): a condition not stated, and a claim read
off a figure.**

- **Remark 7.6.2** defines the smoothed `(6k−2)`-gons by their control mode sequence (eqn:3k+2),
  switching time, initial point `z₀ = iy₀` with `y₀ > 1` and initial control `e₂` ("The changes
  are minor"), but does not state the condition that fixes `y₀`, the analogue of eqn:theta-k.
  - The argument of Lemma 7.5.5 gives `4/(3y₀² + 1) = 2cos(πk/(3k − 1))`; that this closes the
    curve, `g(t_f) = R`, was checked numerically for `k = 2, 3`, not in Lean.
- **Remark 7.6.4** says that at `k = 1` the smoothed `(6k−2)`-gon "degenerates to a rectangle with
  corners and area `√12`", which the book reads off a figure ("the shape appears to be tending to a
  rectangle of area `√12` as `k ↦ 1`", TeX 6435–6438) and does not prove.
  - At `k = 1` the closing condition has no solution (`y₀ = ∞`), so the formalization reads the
    remark as the limit `k → 1⁺` of the `(6k−2)`-gons interpolated to real `k` and proves it.
  - The cost tends to `√12`, and the six arcs tend in the Hausdorff distance to the boundary of a
    rectangle of area `√12` ([`remark7_6_4`](../../SmoothedPolygons/Ch7/Remarks.lean#L1719)).
  - The trajectories exist for every real `k > 1` ([`remark7_6_4_exists`](../../SmoothedPolygons/Ch7/Remarks.lean#L1900)), so the statement is
    not vacuous.
  - The remark is true in this reading.

### E38

**E38. Remark 6.6.1, §6.6 (TeX 5216–5242): a claim stated without proof.**

- **The book:** the first item of the remark says that the transversality conditions make every
  optimal solution, extended in time, periodic up to rotation: `X(3t_f) = X₀`, `g(6t_f) = I₂`, and
  "every transversal trajectory determines a periodic solution (with discrete rotational symmetry)
  of the lifted trajectories in the cotangent bundle".
- **The gap:** the book gives no proof beyond "if we extend time, every optimal solution can be made
  into a periodic one".
- **Here:** the claim is true. The formalization extends every Pontryagin extremal on `[0, t_f]` by
  `g(s + kt_f) = g(s)Rᵏ` and `Y(s + kt_f) = R⁻ᵏY(s)Rᵏ` for `Y = X, Λ₁, Λ_R`, with the coordinates
  of the control permuted cyclically `k` times (so that `Z_{u(s + kt_f)} = R⁻ᵏZ_{u(s)}Rᵏ`).
  - It proves that the extension solves the state–costate system of Problem 6.7.1, with the
    conditions of the maximum principle and the same `λ_cost`, on every `[0, nt_f]`, with period
    `3t_f` for the control, `X`, `Λ₁`, `Λ_R` and `6t_f` for `g` ([`remark6_6_1`](../../SmoothedPolygons/Ch6/PeriodicExtension.lean#L352)).
  - The pieces join by the transversality conditions (6.6.1), and since the controls are only
    measurable they are glued as Carathéodory solutions.
- **The second item,** that the transversality condition for `Λ₁` follows from the one for `g`,
  refers to Corollary 6.5.3 for the proof and is proved so ([`remark6_6_1_lambda1`](../../SmoothedPolygons/Ch6/PeriodicExtension.lean#L86)); the proof
  that minimizers are extremals uses it.

### E39

**E39. §3.5 (TeX 3140–3156): a reparameterization taken for granted.**

- **The book:** to derive the terminal condition `X(t_f) = R⁻¹X₀R`, the book writes
  `g(t + t_f) = g(s(t))R` "for some orientation-preserving reparameterization `s(t)` such that
  `s(0) = 0`", obtained "by the remark following Theorem 3.1.1". Differentiating and using
  `det X = 1` then gives `s' = 1`.
- **The gap:** that remark (TeX 2378–2390) does not contain it.
- **Here:** for a `K_min` parameterized as in §2.4 the reparameterization exists:
  - the multi-point through a boundary point is unique (Lemma 2.2.7), so `σ_{j+1}(t) = σ_j(h(t))`
    for a function `h`, which is `C¹` by the inverse function theorem applied to the polar angles;
  - differentiating `g(h(t)) = g(t)R` gives `h'(t)² det X(h(t)) = det X(t)`, so `h' = 1` in the
    parameterization with `det X = 1`;
  - counting the turning of the polar angle (`σ_{j+3} = -σ_j`) gives `h(0) = t_f`.

The formalization proves `σ_j(t + t_f) = σ_{j+1}(t)` in this way
([`IsWorstDisk.shift_of_det_one`](../../SmoothedPolygons/Ch6/WdTrajectory.lean#L537)) and follows the book's derivation from there; the
identification with `K_min` needs it (E47).

### E40

**E40. §4.6 (TeX 3797–3808): the fundamental domain is not one.**

- **Sectors:** the three geodesics through `i` that the dihedral group permutes (the medians: the
  imaginary axis and the circles `(x ∓ 1/√3)² + y² = 4/3`) cut `𝔥*` into six sectors, which the
  group permutes simply transitively, so each sector is a fundamental domain, as the book says.
- **The error:** the set it then gives as one, `{x ≥ 0, (x - 1/√3)² + y² ≤ 4/3}` (TeX 3807), is
  the union of two sectors, split by the median `(x + 1/√3)² + y² = 4/3`, and contains two points
  of each generic orbit.
- A single sector is `{x ≥ 0, (x + 1/√3)² + y² ≤ 4/3}`, or `{x ≥ 0, (x - 1/√3)² + y² ≥ 4/3}`, the
  one that the proof of Theorem 5.0.2 needs (E45).
- The text also puts the centres of the two circles at "the two cusps `(0, ±1/√3)` on the real
  axis" (TeX 3802), for `(±1/√3, 0)`.
- **Here:** the formalization proves that every orbit meets the last sector
  ([`exists_dihedralAct_mem_fundamentalDomain`](../../SmoothedPolygons/Ch5/Compactification.lean#L773)), which is what the proof uses.

### E41

**E41. Definition 5.0.1 (TeX 3900–3978): three facts asserted.**

- **Compactness:** "The set `𝔥** ⊂ 𝔥*` is compact" (TeX 3975) is not immediate: `𝔥*` is open,
  and the closed versions of the inequalities that define `𝔥**` also admit the cusps
  `(±1/√3, 0)`, as isolated points.
- The formalization proves it ([`isCompact_truncatedStarDomain`](../../SmoothedPolygons/Ch5/Compactification.lean#L556)): the conditions of `Π₀⁺`, `Π₁⁺`, `Π₂⁺`
  give `y ≥ (4/(15√3))(225/226) > 0.15` on `𝔥**`, so `𝔥**` is the set of the closed inequalities
  and `y ≥ 0.15`.
- **Horoballs and symmetry:** the image of a horoball under a linear fractional transformation
  (TeX 3903–3915) and the invariance of `𝔥**` under the dihedral group (TeX 3977–3978) are also
  stated without proof. Both are proved ([`lftAct_image_horoball`](../../SmoothedPolygons/Ch5/Compactification.lean#L422),
  [`image_lftAct_R_truncatedStarDomain`](../../SmoothedPolygons/Ch5/Compactification.lean#L740), [`image_reflAct_truncatedStarDomain`](../../SmoothedPolygons/Ch5/Compactification.lean#L746)).

### E42

**E42. Lemma 5.0.3 (TeX 4000–4015): the second claim is not argued.**

- **The book:** the lemma says that the hexagon `H_K(z)` built from `z ∈ 𝔥*` by Remark 3.1.7 is
  "the critical hexagon at the multi-point `{s_j*}` of `K`" when `z` comes from a balanced disk `K`
  in circle representation; the proof only reconstructs the hexagon.
- The same identification, at every time, is asserted after Lemma 3.1.8 (TeX 2583–2587).
- **Here:** it is true, and the formalization proves it ([`lemma5_0_3`](../../SmoothedPolygons/Ch5/Hexagon.lean#L498)):
  - the edge lines of `H_K(z)` are the tangents of the boundary curves at the `s_j*`, hence
    support lines, so `K ⊆ H_K(z)`;
  - `area(H_K(z)) = 4 det(s₁*, s₂*) = √12`;
  - every centrally symmetric hexagon containing `K` has area at least `√12`, since one of least
    area exists and has area `area(K)/δ(K)` by Theorem 2.2.2, which is `√12` by E12.

Theorem 2.3.9 identifies it with the critical hexagon of Definition 2.3.8.

### E43

**E43. Theorem 5.0.6 (TeX 4203–4317): a claim not argued, and a case only sketched.**

- **Case 1** (`z ∈ h₀`, `z ∉ h₁ ∪ h₂`): the proof cuts the corner `p₀` of the critical hexagon by
  a segment `[r₀, r̃₀] ∥ s₀s₁` with `area(△r₀p₀r̃₀) = T₀^ext` and claims that it meets `∂K`.
  - "Otherwise ... the convex disk `K` would be contained in the centrally symmetric hexagon with
    vertices `r₀, r̃₀, q₁`, and their reflections", which has the area of `H_K(z)`, and an inward
    shift of the cut would give a smaller one (TeX 4271–4281).
  - It does not say why `K` would lie in that hexagon, nor that these six points bound a convex
    hexagon.
- **Case 2** (`z ∈ h₀ ∩ h₁`) says only that "the above argument can also be adapted"
  (TeX 4301–4312).
- **Here:** both are true. The formalization shifts the cut line at once to the support line of `K`
  parallel to `s₀s₁`:
  - if that line lies strictly inside the cut, the hexagon cut at it contains `K`, is centrally
    symmetric and convex, and has area `area(H_K(z)) + 2T₀^ext - 2μ²T₀ < area(H_K(z))`
    (`μ > √(T₀^ext/T₀)` the ratio of the line), contradicting minimality;
  - otherwise the extreme point of `K` on the cut line lies on `[r̃₀, r₀]`
    ([`exists_mem_frontier_segment_cut`](../../SmoothedPolygons/Ch5/AreaBound.lean#L519)).
- **All cases at once:** the construction changes `H_K(z)` only near the corners `p_i`, `p_{i+3}`
  and the edges beyond them, so the claim holds at each corner `i` with `z ∈ h_i` separately.
  - The triangles `±△s_i r_i s_{i+1}` then lie beyond distinct edges of `conv{s_j*}`, with
    pairwise disjoint interiors, which gives the bound in all cases at once
    ([`theorem5_0_6`](../../SmoothedPolygons/Ch5/AreaBound.lean#L777); Section 7).
  - The step `h₀ ∩ h₁ ∩ h₂ = ∅` of the book's proof ([`inter_hRegion_eq_empty`](../../SmoothedPolygons/Ch5/AreaBound.lean#L492)) is then not
    needed.

### E44

**E44. Lemma 5.0.7 (TeX 4432–4465): gaps in (3) and (4), and a slip.**

**Part (3)** says that `I₀area₀ + I₂area₂` is least at `x = 0` on each line `y = const ≥ √3`.

- The proof shows that the sum (5.0.1) over all `i` is continuous, that it increases in `x` on
  `h₀ ∖ h₂` and on `h₀ ∩ h₂`, and concludes that it increases on `h₀ ∩ {x > 0, y ≥ √3}`.
- **The gap:** it never shows that the points with `x > 0`, `y ≥ √3` lie in `h₀`.
- **The slip:** its mirror statement, decrease "on `h₀ ∩ {x < 0, y ≥ √3}`" (TeX 4447), should read
  `h₂ ∩ {x < 0, y ≥ √3}`.
- **Here:** the inclusion holds: with `s = √3x ≥ 0` and `y ≥ √3`, `T₀ ≥ T₀^ext` reads
  `(1 + s)(s² + 3y² - 1) ≥ 8(1 - s)²`, and the difference is at least `s(s² - 7s + 24) ≥ 0`.
- Then, since `I_i area_i = max(area_i, 0)` on `𝔥*`, `I₀area₀ + I₂area₂ = max(area₀ + area₂, area₀)`
  for `x ≥ 0`, the maximum of two functions that (2) and (1) show increasing. This makes the book's
  "increasing on each piece, and continuous" precise ([`lemma5_0_7_3`](../../SmoothedPolygons/Ch5/Monotonicity.lean#L541)).

**Part (4)** says that `δ(x, y) ≥ δ(0, y) ≥ δ(0, 4.5) > δ_oct` for `y ≥ 4.5`.

- The first inequality does not follow from (3), since `δ` also contains `I₁area₁`; it holds
  because `I₁area₁ ≥ 0` and `(0, y) ∉ h₁` (on the imaginary axis `T₁ < T₁^ext`, as
  `(3y² - 1)² > 1`).
- The second takes `area₀(0, y) = (√3/4)√(ρ₀ρ₂)(√(ρ₀ρ₂) - 2ρ₁)` increasing because both factors
  increase; that also needs `√(ρ₀ρ₂) - 2ρ₁ ≥ 0`, true for `y ≥ √3`.
- Both are filled ([`lemma5_0_7_4`](../../SmoothedPolygons/Ch5/Monotonicity.lean#L693)).

### E45

**E45. Proof of Theorem 5.0.2 (TeX 4469–4513): a misprinted domain, a false remark, a tacit step and
two assertions.**

- **(a) The domain:** the fundamental domain is printed `{x ≥ 0, (x - 1/√3)² + y² = 4/3}`
  (TeX 4479), a curve, and attributed to §4.6, which prints another set that is not a fundamental
  domain (E40).
  - The proof needs the sector `{x ≥ 0, (x - 1/√3)² + y² ≥ 4/3}`, which lies in `{x ≥ 0, y ≥ 1}`
    as the proof says (TeX 4481–4482).
  - With §4.6's `≤ 4/3`, the half-plane `Π₁⁺` would meet the domain (at `(0.1, 0.58)`, for
    instance). The formalization uses `≥ 4/3`.
- **(b) The remark:** "The only half-plane meeting this set is `Π₀⁺`" and "the regions `Π₁⁺` and
  `Π₂⁺` do not meet the fundamental domain" (TeX 4483–4484, 4501) are false for
  `Π₂⁺ = {y > 15(x + 1/√3)}`, which meets `{x ≥ 0, y ≥ 1}` where `y > 15/√3 ≈ 8.66`.
  - Those points lie in `B(i∞)`, so the proof is unaffected
    ([`mem_horoball_or_edgeHalfPlane_of_mem_fundamentalDomain`](../../SmoothedPolygons/Ch5/Compactification.lean#L848) states what it uses).
- **(c) The tacit step:** Theorem 5.0.6 is about the multi-point at time `0` of a disk in circle
  representation, but the proof applies it at any time where the trajectory leaves `𝔥**` ("If any
  point of the trajectory `(g, X)` passes through a point `X = Φ(z)`", TeX 4486).
  - That needs the re-centered pair `g(t₀)⁻¹K`, `g(t₀)⁻¹σ_j(· + t₀)`, which is balanced, in circle
    representation, of the same area, with `X(0) = X(t₀)` ([`IsBalancedPair.recenter`](../../SmoothedPolygons/Ch5/Recenter.lean#L147)).
- **(d) The two assertions:** the inclusion `𝔥* ∩ Π₀⁺ ∩ {1 ≤ y ≤ 4.5} ⊆ h₀` (TeX 4499) is
  asserted; it holds because there `ρ₁ < 1/15` and `ρ₀ρ₂ ≥ 1/3` ([`edgeSlab_subset_hRegion`](../../SmoothedPolygons/Ch5/EdgeBound.lean#L91)).
  - The bound `δ₀ > δ_oct` on the line `y = 15(1/√3 - x)`, `1 ≤ y ≤ 4.5`, is left to "a single
    variable calculation" and "the graph" (TeX 4507–4512).
  - `δ₀` is not monotone along the line (it increases for `y ∈ [1, 1.152]`), but there `ρ₁ = 1/15`
    exactly and `6yρ₀ρ₂` is a concave quadratic in `y`, so the bound reduces to the endpoints.
  - The margin is `0.0018` (the minimum is `0.904209`, at `y = 4.5`, against `δ_oct = 0.902414`)
    ([`octagonDensity_lt_edgeLine`](../../SmoothedPolygons/Ch5/EdgeBound.lean#L129)).

### E46

**E46. §6.1 (TeX 4520–4602): the existence of a minimizer.**

**The book** argues that the Reinhardt control problem has an optimal control by Filippov's
theorem (Theorem 6.1.1):

- the control set `U_T` is compact;
- the velocity sets are convex (Lemma 6.1.2);
- by Theorem 5.0.2 "we may assume that `z` lies in the compact set `𝔥**`" (TeX 4579), `t_f ≤ π/3`
  by Lemma 4.3.1, and Gronwall's inequality bounds `g`;
- the vector fields, multiplied by a smooth cut-off `ψ` with `ψ = 1` on `𝔥**`, have compact
  support.

**Four steps fail as written.**

- **(a)** Theorem 5.0.2 is about balanced disks; applying it to the trajectories of the control
  problem needs the converse of Problem 3.6.2. That converse is false for trajectories of higher
  winding number and true for those of winding number one, among them every trajectory cheaper
  than `7π/2` (E15).
- **(b)** The cut-off changes the dynamics outside `𝔥**`, so a minimizer of the cut-off problem
  need not be a trajectory of the Reinhardt problem.
- **(c)** Theorem 6.1.1 concerns the attainable sets from a fixed initial point, while `X(0)` is
  free and the endpoints are coupled (`X(t_f) = R⁻¹X(0)R`).
- **(d)** Lemma 4.3.1 bounds the terminal time of a minimizer, whose existence is what is being
  proved.

**Here:** the formalization repairs all four along the book's lines
([`exists_isReinhardtMinimizer`](../../SmoothedPolygons/Ch6/Existence.lean#L436)).

- It imposes `z ∈ 𝔥**` as a closed state constraint, as the book's "we may assume" says, with a
  compact set of initial points and the closed endpoint relation of the problem.
- It applies Filippov's theorem in that form (`ControlSystem.exists_optimal_constrained`, proved in
  the OptimalControl package by the argument of Theorem 6.1.1, and needing no compact support) to
  the matrix system of §6.2.
- The terminal time is bounded by the argument of Lemma 4.3.1 for every state trajectory, the cost
  being at least `3t_f` ([`three_mul_le_reinhardtCost`](../../SmoothedPolygons/Ch4/TerminalTime.lean#L71)), so a competitor cheaper than the smoothed
  octagon (cost `< π`) has `t_f < π/3`.
- The smoothed octagon belongs to the constrained class, so costlier competitors do not matter, and
  cheaper ones stay in `𝔥**` by (a) and Theorem 5.0.2
  ([`IsReinhardtAdmissible.forall_mem_truncatedStarDomain`](../../SmoothedPolygons/Ch6/Existence.lean#L322)).
- With §6.2 the minimizer lifts to a Pontryagin extremal
  ([`exists_isReinhardtMinimizer_isPontryaginExtremal`](../../SmoothedPolygons/Ch6/Existence.lean#L511)), the premise of Proposition 8.1.3 (TeX 6791).

### E47

**E47. §6.1 (TeX 4571–4572), Proposition 8.1.3 (TeX 6786) and Theorem 16.3.1 (TeX 12789–12795):
the minimizer of the control problem is identified with `K_min` without proof.**

- **The book:** "Recall that Reinhardt has proved the existence of a optimal solution to the
  Reinhardt problem" (TeX 4571) concerns Reinhardt's `K_min`, a centrally symmetric convex disk of
  least greatest packing density.
  - Proposition 8.1.3 speaks of "the global solution of the Reinhardt problem".
  - Theorem 16.3.1 passes from "the global minimizer of the Reinhardt optimal control problem" to
    "the minimizer `K_min` of the Reinhardt problem".
- **The gap:** the book derives the control problem from `K_min` (Chapters 2–3) but does not show
  that the two minimizers correspond.
- **Here:** they do, in both directions.
  - Every `K_min`, after a linear map of positive determinant, is a balanced disk in circle
    representation whose boundary trajectory is admissible with cost its area (Chapters 2–3, with
    the arclength parameterization of `∂K_min`, which §2.4 assumes, constructed from Lemma 2.2.5,
    and the reparameterization of E39).
  - That trajectory is a global minimizer: a competitor cheaper than `7π/2` bounds a balanced disk
    of area its cost (E15), whose density is at least `δ_min`, and a costlier one costs more than
    the area `π` of the unit disk, hence more than `√12 δ_min`
    ([`exists_isReinhardtMinimizer_of_isWorstDisk`](../../SmoothedPolygons/Ch6/WorstDisk.lean#L183)).
  - Conversely, the disk bounded by a global minimizer is a `K_min`, with `δ_min = cost/√12` (E12;
    [`isWorstDisk_of_isReinhardtMinimizer`](../../SmoothedPolygons/Ch6/WorstDisk.lean#L217)).
  - With E46 and §6.2: the Reinhardt control problem has a global minimizer, which lifts to a
    Pontryagin extremal and bounds a `K_min`
    ([`exists_isReinhardtMinimizer_isPontryaginExtremal_isWorstDisk`](../../SmoothedPolygons/Ch6/WorstDisk.lean#L250)).
- The second sentence of Theorem 16.3.1, about `K_min`, rests on this identification (E60).
- **Uniqueness:** the definite articles of "the global solution", "the global minimizer"
  (Proposition 8.1.3, Theorem 8.2.7, Theorem 16.3.1) and "the minimizer `K_min`" presuppose a
  uniqueness that is not known; the formalization states these results for every global minimizer
  and every `K_min` (E48, E55, E60).

### E48

**E48. Proposition 8.1.3, §8.1 (TeX 6785–6798): the principle of optimality, invoked without a
construction.**

- **The book:** the proof says that on a subinterval where the control lies in an edge of `U_T`,
  "the globally minimizing trajectory must minimize cost among all trajectories with the same
  endpoint conditions on the subinterval and that have their control function similarly
  restricted to the edge. Thus, the global minimizer is also edge extremal."
- **Two steps are left out.**
  - The first is how a competitor of the edge control problem (Definition 8.1.1) gives a
    competitor of the Reinhardt problem. The running text of §8.1 relates the two problems through
    (8.1.1) and a cost identity, but the proof does not use them.
  - The state space of the edge problem (`y > 0`, `|x| < 1/√3`) is larger than the star domain, so
    a competitor may leave the state space of the Reinhardt problem and give no admissible
    trajectory.
  - The second is the maximum principle for the edge problem, which turns minimality into edge
    extremality.
- **Here:** both are supplied along the book's lines ([`proposition8_1_3`](../../SmoothedPolygons/Ch8/EdgeExtremal.lean#L850)).
  - Only competitors uniformly close to the minimizer's edge arc are spliced in, so that they stay
    in the star domain (strong local minimality, which is all the maximum principle needs).
  - A competitor's trajectory is rebuilt from `(x, y, s)` by (8.1.1) ([`eqn_g_edge`](../../SmoothedPolygons/Ch8/EdgeProblem.lean#L494)), so that it
    ends at the minimizer's `g(d)` and `X(d)`; the rest of the minimizer is shifted in time (the
    terminal time is free).
  - The costs differ by `3/2` times the difference of the edge costs, by the cost identity
    `(3/2)((s + x)| + ∫x²/y)` of §8.1 ([`edgeCost_identity`](../../SmoothedPolygons/Ch8/EdgeProblem.lean#L601)).
  - The maximum principle for the edge problem (an open subset of `ℝ³`, fixed endpoints, free
    terminal time, an integral cost) is [`External.pontryagin_maximum_principle`](../../External/Pontryagin.lean#L80).

"We have seen that the global minimizer must be extremal" (TeX 6791) is §6.1–§6.2 (E46,
[`exists_isPontryaginExtremal_of_isReinhardtMinimizer`](../../SmoothedPolygons/Ch6/MatrixExtremal.lean#L564)), and "the global solution" presupposes
uniqueness (E47).

### E49

**E49. Theorem 8.1.4, §8.1 (TeX 6807–6894): "optimal" in the statement, and three steps of the
proof.**

- **The statement:** the theorem concerns "an extremal lifted trajectory in the edge control
  system" but says "Then the optimal control function `u_e` is bang-bang". The proof uses
  extremality only, and Theorems 8.2.7 and 8.3.2 apply the theorem to extremals that need not be
  optimal.
- **Here:** the formalization states it for every extremal, normal or abnormal
  ([`theorem8_1_4`](../../SmoothedPolygons/Ch8/EdgeBangBang.lean#L823)).

In the proof:

- **(a)** "The function `λ₂'` is also continuous by the form of the ODE it satisfies"
  (TeX 6846–6852).
  - The right-hand side of (8.1.7) contains the measurable control, so `λ₂` is only absolutely
    continuous, and its derivative is continuous only after the control is changed on a null set,
    which the book does at the end of the proof.
  - The proof uses `λ₂'` only at the zeros of `λ₂`, where the control-dependent term, `λ₂` times a
    bounded function, tends to `0`; the formalization proves the derivative there and nothing more
    (Section 7).
- **(b)** At a zero `t₂` with `λ₂(t₂) = λ₂'(t₂) = 0` the proof solves `H = ∂H/∂y = 0`
  (TeX 6866–6869), but the maximum principle gives `H = 0` only almost everywhere; at `t₂` it holds
  by continuity, for the same reason (E53).
- **(c)** "The next lemma shows that even at times when the conditions of (8.1.8) are met, the
  zeros of the switching function `λ₂` are isolated" (TeX 6884–6886).
  - Lemma 8.1.5 assumes solutions on an interval `(-t₁, t₁)` around the zero, which can be an end
    of `[t₀, t₁]`.
  - The formalization continues the state and the costate past the end with the control
    `u_e = 0`, for which the solution is explicit (with `λ_cost = -1`: `x = x₀ + y₀t`, `y = y₀`,
    `λ₁ = 2x₀t/y₀ + t²`, `λ₂ = -2x₀t²/y₀ - 2t³/3`).

The count of the zeros at which `λ₂' = 0` ("at most two times", TeX 6875–6879, since `x' = y > 0`)
is proved ([`IsEdgeProblemExtremal.exists_tangentialZeros_subset_pair`](../../SmoothedPolygons/Ch8/EdgeBangBang.lean#L414)). The theorem is true.

### E50

**E50. Lemma 8.1.5, §8.1 (TeX 6908–7015): a wrong constant.**

- **The book:** for `x₀ ≠ 0` the proof sets `C = -x₀(1 + y₀)/y₀²` (TeX 6934) and integrates
  `2x₀(1 + y₀)τ/y₀²` (TeX 6973).
- **The error:** its own preceding lines give `(x² - x₀²)/y² = 2x₀t/y₀ + O(t²)` (TeX 6970) and
  `λ̃₁ = 2x₀t/y₀ + O(t²)`, so `λ̃₂ = -∫₀ᵗ 4x₀τ/y₀ dτ + O(t³) = -2x₀t²/y₀ + O(t³)`, and
  `C = -2x₀/y₀`.
- **Here:** the statement claims only `C ≠ 0`, which holds with the correct value, and for
  `x₀ = 0` the book's `C = -2/3` is right; the formalization proves the lemma with `C = -2x₀/y₀`
  ([`lemma8_1_5`](../../SmoothedPolygons/Ch8/EdgeLandau.lean#L504)).

The book's Landau notation is two-sided (TeX 6903–6907), and the Gronwall step applies Corollary
A.1.3, stated for `t ≥ 0`, on both sides of `0` (E61).

### E51

**E51. Remark 8.1.6, §8.1 (TeX 7035–7070): wrong signs.**

- **The book:** with `λ_cost = 0` and the printed `Λ_R = [[x, y² - x²], [1, -x]]`,
  `Λ₁ = [[-x, x²], [-1, x]]`, the costate equations hold and `H ≡ 0` on the edge `{u₀ = 0}` ("It
  can be checked", MCA:4647835).
- **The error:** `H(u) = 6u₀y³/D` with `D = -3y⟨X, Z_u⟩ > 0` on the star domain (Lemma 3.3.4), so
  the edge is the set of *minimizers* of the Hamiltonian over `U_T`, and "any measurable control
  function `u_e(t) ∈ [-1/2, 1/2]` maximizes the Hamiltonian" fails.
- **Here:** reversing the sign of both costates, which the linear costate equations allow when
  `λ_cost = 0`, gives `H(u) = -6u₀y³/D ≤ 0`, with equality exactly on the edge (checked with
  sympy). With these signs the remark is true, and the formalization proves it
  ([`remark8_1_6`](../../SmoothedPolygons/Ch8/EdgeAbnormal.lean#L214)).

These abnormal costates belong to a two-parameter family, the costates conormal to the edge
submanifold of (8.1.1), which E55 and E57 meet again.

### E52

**E52. Lemma 8.2.1, §8.2 (TeX 7095–7126): a quantifier too broad, and a step left implicit.**

- **The quantifier:** the lemma is stated "for all `X ∈ 𝔰𝔩₂(ℝ)` and all `Λ ∈ X^⊥`", but the
  control-dependent term `H₂ = -⟨Λ, Z_u⟩/⟨X, Z_u⟩` of the Hamiltonian is defined only when
  `⟨X, Z_u⟩ ≠ 0` for every `u ∈ U_T`, and for `X = 0` the statement has no meaning.
  - The condition holds on the state space (Lemma 3.3.4), where the lemma is used, and Lemma 7.3.1
    needs it too (E26); the formalization adds it (`hden` in [`lemma8_2_1`](../../SmoothedPolygons/Ch8/SingularLocus.lean#L586)).
- **The implicit step:** in the proof, the step from the independence of the control to `Λ = 0`
  is one sentence, "The value of `H₂` must then be zero, and `Λ` must lie in the orthogonal
  complement `{0}` of the entire tangent space" (TeX 7117–7119).
  - What it needs is that the linear form `ν = T*Φ(-Λ)` (Theorem 6.8.2), constant on the
    velocities `f(z; u)`, `u ∈ U_T`, whose affine hull is the tangent space, vanishes on their
    span, the whole tangent space; the formalization fills the step so.

### E53

**E53. Lemma 8.2.2 and Theorem 8.2.3, §8.2 (TeX 7128–7216): the Hamiltonian at one time, and a
closed interval.**

- **The book:** the proof of Lemma 8.2.2 uses `H = 0` at the time `t₀` where `Λ_R(t₀) = 0`: "The
  maximum principle states that the Hamiltonian vanishes identically along the lifted extremal"
  (TeX 7140–7141).
- **The gap:** the maximum principle gives `H = 0` only almost everywhere (Section 6), and `t₀` is
  a single time.
- **Here:** it holds there by continuity: the control-dependent term `-⟨Λ_R, Z_u⟩/⟨X, Z_u⟩` tends
  to `0` with `Λ_R`, uniformly in `u ∈ U_T`, and the rest of `H` is continuous; the book does not
  say so.
- **The same step elsewhere:** the proofs of Theorem 8.1.4 (TeX 6866–6869, at a zero of `λ₂`;
  E49) and Theorem 8.3.1 (TeX 7533–7535; E56) take the same step. The formalization proves the
  vanishing at the given time by this continuity in each case ([`eqn_edge_zero`](../../SmoothedPolygons/Ch8/EdgeBangBang.lean#L342),
  [`lemma8_2_2`](../../SmoothedPolygons/Ch8/SingularLocus.lean#L783), [`theorem8_3_1`](../../SmoothedPolygons/Ch8/FiniteBangBang.lean#L1288)).
- The nontriviality of the costate that the lemma then uses is E21's.
- **The closed interval:** the proof of Theorem 8.2.3 assumes `Λ_R ≡ 0` on the closed interval
  `[t₁, t₂]` (TeX 7189), while the statement assumes it on `(t₁, t₂)`; by continuity the two are
  the same ([`theorem8_2_3`](../../SmoothedPolygons/Ch8/SingularLocus.lean#L924)).

### E54

**E54. Theorem 8.2.6, §8.2 (TeX 7259–7298): a converse argued by necessary conditions, and two
typos.**

- **The converse:** "Conversely, the lifted trajectory attached to a multi-curve of circular arcs
  is a Pontryagin extremal singular subarc" is argued by deriving what a lift must satisfy (the
  control is the centre of `U_T`, `Λ_R = 0` by Lemma 8.2.1, `Λ₁ = (3/2)λ_cost J` by Lemma 8.2.2),
  not by exhibiting one.
- **Here:** a lift exists: `λ_cost = -1`, `Λ₁ = -(3/2)J`, `Λ_R = 0` solve the costate equations,
  with `H ≡ 0` and a nontrivial reduced costate, and the formalization exhibits it
  ([`theorem8_2_6`](../../SmoothedPolygons/Ch8/SingularLocus.lean#L1022)).
- **The typos:** in the proof, `g' = Xg` (TeX 7288) should be `g' = gX`, and
  "Lemma~\ref{thm:circle-singular}" (TeX 7290) refers to Theorem 8.2.3.

### E55

**E55. Theorem 8.2.7, §8.2 (TeX 7300–7391): the proof covers one kind of singular subarc; slips in
the second variation.**

**The statement and the proof.**

- The theorem says that "the global minimizer of the Reinhardt problem does not contain any
  singular subarcs", and by Definition 6.2.1(3) these include the intervals on which the
  maximizers of the Hamiltonian form an edge of `U_T` at every time.
- The proof ("The previous theorem shows that the singular subarc comes from a multi-curve of
  circular arcs") covers only the subarcs on which the Hamiltonian does not depend on the control,
  through Theorem 8.2.6, and shows by a second variation that a circular arc is not a local
  minimizer.
- The authors' comments leave the edge case to the edge control problem:
  - "Theorem is only true if we include secondary edge optimal control problem" (TeX 7300–7302);
  - "We say Reinhardt problem here rather than Reinhardt control problem because we want to
    include the edge control problem" (TeX 7312–7313);
  - Chapter 1 (TeX 806–821).

**The reading.** With the user's approval, the formalization states the theorem in this reading
([`theorem8_2_7`](../../SmoothedPolygons/Ch8/NoSingularArcs.lean#L375)):

- on an interval where the control lies in an edge, the minimizer's edge arc has edge costates
  (Proposition 8.1.3), none of which has a singular subarc of the edge problem (by the argument of
  Theorem 8.1.4: on such a subarc `λ₂ ≡ 0`, and (8.1.8) makes `x²` constant, against `x' = y > 0`);
- on an interval no subinterval of which has the control in an edge, no lift is a singular subarc
  (the circle argument, after a localization: near a time where `Λ_R ≠ 0` the maximizers on a
  singular subarc are one edge, by Lemma 8.2.1, and the control lies in it).

**Normal lifts.** For normal lifts the theorem holds as printed
([`not_isSingularSubarc_of_isReinhardtMinimizer_of_isNormalExtremal`](../../SmoothedPolygons/Ch8/NoSingularArcs.lean#L418)):

- on an edge interval, the Reinhardt costate pulled back to the edge submanifold of (8.1.1) and
  shifted by `(3/2)λ_cost d(s + x)` is a costate of the edge problem with the same Hamiltonian
  ([`IsExtremalOn.isEdgeProblemExtremal_edgePullback`](../../SmoothedPolygons/Ch8/EdgePullback.lean#L870)),
- so a singular subarc there would be one of the edge problem.

**Abnormal lifts.** For abnormal lifts the printed statement is open, neither proved nor refuted.

- Along every edge arc there is a two-parameter family of abnormal costates conormal to the edge
  submanifold of (8.1.1), which contains those of Remark 8.1.6 with the signs of E51, and whose
  pull-back vanishes.
- Excluding a global abnormal lift of the minimizer that is conormal on some interval needs an
  argument the book does not give.
- No counterexample is known, and Theorem 16.3.1 does not depend on it (E60).

**Two other readings are not provable.**

- Reading "elsewhere" as "on an interval on which the control does not lie in a single edge"
  brings the abnormal case back (the control may alternate between the vertices of the edge
  `{u₀ = 0}` and then stay at the third vertex, with a lift conormal to one edge submanifold and
  then to another).
- Reading singularity at a time `t` of an edge interval through *some* edge costate on *some* edge
  interval containing `t` makes every edge arc with `x > 0` singular.
  - On an arc with `u_e ≡ ½`, the covector `(λ₁, λ₂, λ₃) = (0, 0, x(t)²)` with `λ_cost = -1` at
    `t`, continued by (8.1.7), has `λ₂(t) = λ₂'(t) = 0` and `λ₂''(t) = -4x(t)/y(t) < 0`.
  - So it is an edge costate near `t` whose Hamiltonian does not depend on the control at `t`.

**The second variation has slips.**

- `cost(g₀) = π` (TeX 7382) holds only on an interval of length `π/3`; on `[t₁, t₂]` the arc costs
  `3(t₂ - t₁)`.
- The condition "`ψ₁'(t) > 0` and `ψ₂'(t) < 0` on their common support" (TeX 7376–7378) cannot hold
  literally for smooth nonnegative functions with compact support (where `ψᵢ` vanishes, so does
  `ψᵢ'`). It is read on the interior of the overlap of the supports, which is what the sign of
  `ψ₁'ψ₂ - ψ₁ψ₂'` needs.
- `σ_i = g_s e_i` (TeX 7385) should be `g_s s_i*`.
- The admissibility of the competitor is asserted in two sentences (TeX 7384–7390).

**Here:** the formalization follows the book's route ([`exists_lt_reinhardtCost_of_circleArc`](../../SmoothedPolygons/Ch8/CircleVariation.lean#L1209)).

- With `L = t₂ - t₁` and `ρ = |ψ|`, the cost of the deformed arc is exactly
  `3L - 3∫₀ᴸ (sinh(sρ)/ρ)²(ψ₁'ψ₂ - ψ₁ψ₂') dt`, whose second-order truncation is the book's
  expansion, so the cost drops for every `s ≠ 0`.
- Smallness of `s` is needed only for the admissibility, which is carried out (positive
  curvatures, the reparameterization to `det X = 1`, the control through Theorem 3.4.2, and the
  splice into the trajectory).

In Remark 8.2.8, the conditions of the three cases of `ψ₁` are commented out in the TeX
(TeX 7397–7405).

### E56

**E56. Theorem 8.3.1, §8.3 (TeX 7448–7586): false as printed; one claim sketched.**

**(a) False as printed.** The theorem says that if an edge-extremal extremal lifted trajectory on
`[t₁, t₂]` does not meet `𝒮_sing` at `t₀`, then "there exists an edge `{i, j}` and a neighborhood
of `t₀` in `[t₁, t₂]` on which `(X(t), Λ_R(t)) ∈ ⋃_{I ⊆ {i,j}} (T*O_J)_I`": the maximizers of the
Hamiltonian lie in one edge at every time of a neighbourhood of `t₀`. This is false.

- **Why:** at a time `t₀` where `Λ_R(t₀) = 0`, every control maximizes, and such times occur off
  `𝒮_sing` on edge-extremal extremals.
- **A normal example** (checked numerically): `λ_cost = -1`, `X(0) = Φ(0.1 + 0.9i)`,
  `Λ_R(0) = 0`, `Λ₁(0) = -(3/2)J + L` with `0 ≠ L ⊥ X(0)`.
  - With `e_a`, `e_b` the vertices that maximize and minimize `⟨[L, X(0)], P_u⟩`, the control
    `e_b` on `(-ε, 0)` and `e_a` on `(0, ε)` gives, for small `ε`, an edge-extremal extremal that
    does not meet `𝒮_sing`, and all of `U_T` maximizes at `0`.
- **Weaker readings fail too:** reading the conclusion off `t₀`, or almost everywhere, does not
  save it.
  - Take an abnormal costate conormal to the edge submanifold of `{u₀ = 0}` (the family of E51)
    with `Λ_R(t₀) = 0`, and the control `e₂` before `t₀` and `e₁` after.
  - This gives an edge-extremal extremal off `𝒮_sing` whose maximizers are the edge `{e₂, e₃}`
    before `t₀` and the vertex `e₁` after, which no edge contains.
- **The proof:** its claim (a) finds exactly this ("If the set of maximizers is an edge when `t`
  has one sign, then the maximizer is the complementary vertex of `U_T` when `t` has the other
  sign", TeX 7555–7557), which does not contradict the assumption of its contrapositive.
  - It also passes, through Theorem 8.1.4, to a conclusion about the control, while that
    assumption is about the maximizers.
- **Here:** with the user's approval, the formalization proves the one-sided form
  ([`theorem8_3_1`](../../SmoothedPolygons/Ch8/FiniteBangBang.lean#L1288)): there are `ε > 0` and edges `k₋`, `k₊` such that the maximizers lie in
  `k₋` at every time of `(t₀ - ε, t₀)` and in `k₊` at every time of `(t₀, t₀ + ε)` (within
  `[t₁, t₂]`). Both examples satisfy it.
- **The form Theorem 8.3.2 quotes:** that the control lies in a single edge almost everywhere on a
  neighbourhood of `t₀`. It is true, and follows from the one-sided form with edge extremality and
  Theorem 8.1.4 ([`IsExtremalOn.exists_ae_mem_controlEdge_of_isEdgeExtremalOn`](../../SmoothedPolygons/Ch8/FiniteBangBang.lean#L1349)).
  - On each side the control is eventually one vertex, and any two vertices lie in a common edge.
  - Edge extremality, a hypothesis of the theorem, is used only there (Section 5).

**(b) Claim (b)** is "a brief sketch" (TeX 7565–7575). It is carried out as a second-order
expansion: if `[Λ_{1,cost}(t₀), X(t₀)] = 0` and `W' = [Λ_{1,cost}'(t₀), X(t₀)] ≠ 0`, then
`Λ_R(t) = -(t - t₀)²W'/2 + o((t - t₀)²)`, with the same leading direction on both sides of `t₀`.

**(c) Smaller points.**

- "Edge-extremal \eqref{def:edge-extremal}" (TeX 7452) points to Definition 8.1.1, the edge
  control problem, and prints "(8.1.1)", the number of an equation; Definition 8.1.2, which has no
  label, is meant.
- "Reparameterizing by a time translation, we may assume that `t₀ = 0`" (TeX 7472–7473) overlooks
  that `t₀` may be an end of `[t₁, t₂]`, where the Gronwall step on a two-sided neighbourhood
  needs the functions beyond the end (the formalization extends them by their value there).
- The proof uses `H = 0` at `t₀` (TeX 7533–7535; E53), the nontriviality of the reduced costate
  (TeX 7583–7584; E21) and Corollary A.1.3 on both sides of `t₀` (TeX 7539, 7572; E61).
- "The hypothesis of the lemma" (TeX 7575) means the theorem's.

### E57

**E57. Theorem 8.3.2, §8.3 (TeX 7590–7605), and its restatement in Chapter 1 (TeX 851–856).**

- **No interval:** the statement has no interval ("Consider a controlled extremal lifted
  trajectory"), and the proof uses `[t₁, t₂]` without introducing it. The formalization states
  the theorem on a compact interval ([`theorem8_3_2`](../../SmoothedPolygons/Ch8/FiniteBangBang.lean#L1419)).
- "According to the theorem" means Theorem 8.3.1, quoted in its form about the control (E56).
- **The restatement:** Chapter 1 restates it as "Every Pontryagin extremal of the Reinhardt
  control problem which does not meet the singular locus is given by a bang-bang control function
  with finitely many switches", without edge extremality.
  - For extremals on an interval this is false: by Remark 8.1.6, with the signs of E51, every
    trajectory with an arbitrary measurable control in an edge lifts to an abnormal extremal, which
    never meets `𝒮_sing` (its `Λ_R` never vanishes) and need not be bang-bang (the midpoint of the
    edge as control, for instance).
  - For normal extremals the restatement follows from Theorem 8.3.2, since every normal extremal
    is edge extremal: the pulled-back costate of E55 is an edge costate
    ([`IsNormalExtremal.isEdgeExtremalOn`](../../SmoothedPolygons/Ch8/EdgePullback.lean#L903), [`IsExtremalOn.isEdgeExtremalOn_of_ne_zero`](../../SmoothedPolygons/Ch8/EdgePullback.lean#L895)).
  - A comment of the authors in the TeX expects this ("a normal extremal solution should also be
    edge extremal", TeX 6664–6666).
  - Whether the restatement fails for extremals with the boundary conditions of Problem 3.6.2 is
    not settled: the costates of Remark 8.1.6 are tied to one edge and need not satisfy the
    transversality conditions.

The formalization states Theorem 8.3.2 as Chapter 8 does.

### E58

**E58. Remark 8.3.3, §8.3 (TeX 7610–7616): a disk that need not exist, and no proof.**

- **The book:** the remark says that a trajectory that is extremal and edge extremal and does not
  meet `𝒮_sing` "defines a balanced disk `K(g, X) ∈ 𝔎_bal` whose boundary is a smoothed polygon,
  consisting of finitely many straight edges and hyperbolic arcs".
- **The disk:** that the trajectory bounds a balanced disk is the converse of Problem 3.6.2, which
  holds only for trajectories of winding number one (E15), and the book does not show it for
  extremals.
  - The formalization takes the disk as a hypothesis (a balanced pair with `σ_j = g s_j*` and
    `σ_j(t + t_f) = σ_{j+1}(t)`); it exists for the global minimizer, whose cost is below `7π/2`.
- **No proof:** the remark has no proof. Its content is:
  - Theorem 8.3.2 with the discussion of §7.2 (on an interval of constant vertex control, two of
    the state-dependent curvatures vanish, so two pairs of the curves move along straight lines,
    TeX 5613–5621);
  - and Lemma 3.1.8 (the third pair moves along hyperbolic arcs whose asymptotes are those lines).
- **Here:** the formalization proves it so ([`remark8_3_3`](../../SmoothedPolygons/Ch8/PolygonBoundary.lean#L846)), with the smoothed polygon defined as in
  the gloss of Theorem 16.3.1 (Section 6).

### E59

**E59. Lemma 8.3.4, §8.3 (TeX 7619–7670): a sign and a garbled display.**

- **The sign:** with `P_i = Z_{e_i}/⟨J, Z_{e_i}⟩`, `Λ_R'''(0) = +6λ_cost[J, P₃]`, not
  `-6λ_cost[J, P₃]` (TeX 7648; checked with sympy).
- **The display** at TeX 7657–7660 lacks an `=` and the factor `λ_cost`.
- **Unaffected:** the leading terms of the control-dependent term `-⟨Λ_R(t), P_i⟩` at `e₁`, `e₂`,
  `e₃` are `(2√3, -2√3, 0)λ_cost t³`, opposite and nonzero at `e₁` and `e₂` as the book says, so the
  conclusion is unaffected.
- The argument works on either side of the meeting time, which covers a meeting at an end of the
  interval, the case that Theorem 16.3.1 needs ("A trajectory cannot reach the singular locus with
  finitely many switches", TeX 12817–12819).
- **Here:** the formalization proves the lemma ([`lemma8_3_4`](../../SmoothedPolygons/Ch8/VertexControl.lean#L662)) with Taylor expansions with
  remainder in place of "The solutions are analytic" (TeX 7637), and treats the three vertices
  alike where the book treats `e₃`, "(say)".

### E60

**E60. Theorem 16.3.1, §16.3 (TeX 12789–12833): the set of meeting times is not handled; the last
step rests on Chapters 13–16.**

**(a) The meeting times.** The proof invokes, in turn:

- Proposition 8.1.3 and Theorem 8.3.2 (finite bang-bang away from `𝒮_sing`);
- Theorem 8.2.7 ("A trajectory cannot remain on the singular locus for any positive interval of
  time");
- Lemma 8.3.4 ("A trajectory cannot reach the singular locus with finitely many switches").

Then it goes on: "The proof then reduces to the consideration of a trajectory such that the
infinite sequence of switching points has a subsequence tending to the singular locus"
(TeX 12821–12823). It does not handle the set of times at which the lift meets `𝒮_sing`, which is
closed but may a priori be infinite and contain `0`.

The formalization repairs the step:

- The meeting set has empty interior (Theorem 8.2.7 in its part without edges, through Theorem
  8.2.3: on an interval of `𝒮_sing` the control is the centre of `U_T`).
- A meeting at `0` gives one at `T`, by the transversality conditions and `R⁻¹JR = J`.
- Take a meeting time `z > 0`, a time `p < z` off the meeting set, and the first meeting time `d`
  after `p`. On `(p, d)` the control is bang-bang with finitely many switches on every compact
  subinterval (Theorem 8.3.2).
- Either the switching times accumulate at `d`, the configuration that the book excludes by
  Theorems 16.4.1 and 14.4.1, or the control is one vertex just before `d`, which Lemma 8.3.4,
  applied at the end of an interval, excludes (E59).

**(b) The second sentence** ("In particular, the minimizer `K_min` of the Reinhardt problem is a
finite-sided smoothed polygon …") follows from the first:

- by Remark 8.3.3 ("A bang-bang trajectory with finitely many switches is a polygon with rounded
  corners", TeX 12807–12808),
- with the identification of the minimizers with `K_min` (E47),
- and Lemma 2.2.5 for "no corners".

The book takes the passage from the control problem to `K_min` for granted.

**(c) Uniqueness.** "The global minimizer" and "the minimizer `K_min`" presuppose uniqueness; the
theorem is formalized for every global minimizer and every `K_min` (E47).

**The hypothesis.** The formalization also states the theorem on one named hypothesis,
[`NoChatteringIntoSingularLocus`](../../SmoothedPolygons/Ch16/MahlerFirst.lean#L110): the consequence of Theorems 16.4.1 and 14.4.1 that the last step uses,
that the switching times of a Pontryagin extremal do not accumulate, from the left, at a time
where its lift meets `𝒮_sing` ([`theorem16_3_1`](../../SmoothedPolygons/Ch16/MahlerFirst.lean#L349); Section 2).

- Without the hypothesis it proves the first sentence on every interval on which the lift avoids
  `𝒮_sing` ([`isFiniteBangBang_of_isReinhardtMinimizer_of_not_mem_singularLocus`](../../SmoothedPolygons/Ch16/MahlerFirst.lean#L169)).
- The hypothesis is derived along the book's last step from Theorems 16.4.1 and 14.4.1 (E89;
  [`theorem16_3_1_of_theorem14_4_1`](../../SmoothedPolygons/Ch16/NoChattering.lean#L387)).
- Both are proved, with the facts that the book reads off computations, so that the hypothesis
  holds ([`noChatteringIntoSingularLocus`](../../SmoothedPolygons/Ch16/MahlerFirstArcRegion.lean#L59)) and so does the theorem
  ([`theorem16_3_1_unconditional`](../../SmoothedPolygons/Ch16/MahlerFirstArcRegion.lean#L94)).

(The proof also has a typo, "is is an extremal", TeX 12812.)

### E61

**E61. Corollary A.1.3, Appendix A.1 (TeX 13134–13142): stated for `t ≥ 0`, applied on both sides
of `0`; no proof.**

- **Both sides:** the corollary is stated on `[0, t₁]`, with the conclusion "`x(t) = O(tⁿ)` for
  `t` nonnegative", but Lemma 8.1.5 (TeX 7008) and the proof of Theorem 8.3.1 (TeX 7539, 7572)
  apply it on `(-t₁, t₁)`, where the book's Landau notation is two-sided (TeX 6903–6907).
- **Here:** the case `t < 0` follows by applying the corollary to `t ↦ x(-t)`
  ([`corollaryA_1_3_two_sided`](../../SmoothedPolygons/AppA/Gronwall.lean#L76)).
- **No proof:** the corollary has no proof; it follows from Lemma A.1.1 with constant data, and the
  formalization proves it so, through the integral form of Gronwall's inequality in the
  OptimalControl package ([`corollaryA_1_3`](../../SmoothedPolygons/AppA/Gronwall.lean#L46)).
- The hypothesis that `n` is positive is not needed (Section 5), and `∫₀ᵗ x(t) dt` uses `t` both as
  the bound and as the variable of integration.

### E62

**E62. §13.2 and Lemma 13.2.6 (TeX 10740–10753, 10972–11009): the first control, promised well
defined, argued only as a necessary condition; the Hamiltonian asserted constant.**

- **The definition:** the book defines the first control of `z⁰ ≠ 0` as "the optimal control
  starting at switching time `t = 0` until the first positive switching time `t_sw > 0`".
- **The promise:** it defers its justification: "It will become clear from the proof of Lemma
  13.2.6 that `t = 0` is an isolated zero of the relevant switching function, and that the notion
  of first control is well-defined" (TeX 10747–10753).
- **The proof:** that proof shows only that a first control, if one exists, is the lexicographic
  maximizer with the tie rule, and it treats the control as constant on `(0, ε)`.
- **Three facts are asserted or left implicit:**
  - that the lexicographic maximizer is optimal on some `[0, ε]`;
  - that every extremal with a measurable control from `z⁰ ≠ 0` follows it up to `t_sw`;
  - that the Hamiltonian is constant along such extremals ("if `u` is chosen according to the
    maximum principle, then `H_F` is constant along trajectories", TeX 10741–10742).
- **Here:** all three hold. The formalization proves the first two with the book's Taylor
  expansion ([`lemma13_2_6`](../../SmoothedPolygons/Ch13/FirstControl.lean#L539), [`TriFuller.IsFirstControl.unique`](../../SmoothedPolygons/Ch13/FirstControl.lean#L330),
  [`TriFuller.eq_flow_of_maxCondition`](../../SmoothedPolygons/Ch13/Extremals.lean#L424); Section 7) and the third by absolute continuity
  ([`TriFuller.hamMax_eq_of_maxCondition`](../../SmoothedPolygons/Ch13/Extremals.lean#L140)).
- **The switching time:** it reads `t_sw` as the time at which the first control stops being
  optimal. At a double root of a switching function at which the control stays optimal, the
  extremal is unique and does not switch, so such a tangency is not a switching time (Section 6).

### E63

**E63. Lemmas 13.2.1–13.2.3 and 13.2.5, §13.5 (TeX 10794–10906, 11246–11260): symmetries applied
outside their hypothesis.**

- **The book:** Lemmas 13.2.1–13.2.3 (rescaling, rotation by `ζ`, time reversal) are stated for
  solutions that satisfy the maximum condition and `H_F = 0` ((13.2.5), (13.2.6)).
- **Applied outside it:** these apply them at every `z⁰`, where `H_F` need not vanish:
  - the proof of Lemma 13.2.5 ("The lemma follows from the time-reversal symmetry (Lemma
    13.2.3)", TeX 10905–10906);
  - the descent of `F` to `(ℝ_{>0} × Ξ)_𝒲/V_T` and to `F_ang` ("By the equivariance of the
    construction", "By the scaling symmetries", TeX 11246–11260).
- **Here:** the substitutions never use `H_F = 0`, and the formalization redoes them for constant
  controls ([`TriFuller.tau_flow_neg`](../../SmoothedPolygons/Ch13/Symmetry.lean#L172), [`TriFuller.ham_tau`](../../SmoothedPolygons/Ch13/Symmetry.lean#L192),
  [`TriFuller.poincare_smul`](../../SmoothedPolygons/Ch13/PoincareMap.lean#L281), [`TriFuller.poincare_scale`](../../SmoothedPolygons/Ch13/PoincareMap.lean#L315); Section 7).

### E64

**E64. Corollary 13.2.7, Lemma 13.2.8 and the remark after it, §13.2 (TeX 11011–11067): slips.**

- **Corollary 13.2.7:** in the bound of its proof (TeX 11039–11040) the first `<` should be `≤`:
  equality holds when `t = 10r` and `|z_j| = r^j`. The final strict inequality,
  `√3 Σ 10^{k-3}/k! < 1/(4√3)`, holds, so the corollary stands ([`corollary13_2_7`](../../SmoothedPolygons/Ch13/FirstControl.lean#L750)).
- **Lemma 13.2.8** does not need its hypotheses `z₃⁰ ∈ ℝ_{≤0}` and `z⁰ ≠ 0`: the two cubics differ
  only in their `t³` terms, whose sum is `RR(ζ - ζ², -i(ζ - ζ²))t³/(6√3) = 0`
  ([`lemma13_2_8`](../../SmoothedPolygons/Ch13/FirstControl.lean#L885), which keeps them as printed; Section 5).
- **The corollary after the lemma** (TeX 11063–11067: switching back and forth between `ζ` and
  `ζ²` happens at consecutive roots of one cubic, and after its largest root the control switches
  to `1`) is stated without proof and is not used later; it is not formalized (Section 9).

### E65

**E65. Lemma 13.3.2, §13.3 (TeX 11108–11156): a gap and two typos.**

- **The book:** the proof treats two cases, each on all of `[0, t₂]`: the Hamiltonian independent
  of the control in `U_T` (the whole triangle maximizing), and independent of the control in the
  edge `[ζ, ζ²]` "(say)" (TeX 11136–11155).
- **The gap:** the hypothesis lets the maximizing face change with `t`, which the two cases do not
  cover.
- **Here:** the lemma is true, and the formalization repairs the proof along its lines
  ([`lemma13_3_2`](../../SmoothedPolygons/Ch13/SingularLocus.lean#L715); Section 7):
  - a maximizing face that is not a vertex means `z₃(t) ∈ 𝒲`;
  - if `z₃(t₀) ≠ 0`, then by continuity `z₃` stays on one open ray of `𝒲` on an interval around
    `t₀`, where the maximizing face is one edge and the book's second case gives a contradiction;
  - so `z₃ ≡ 0`, and the book's first case applies.
  - On the ray `ℝ_{<0}c` the argument uses `RR(z₃, ic)`, which for `c = 1` is the book's
    `RR(z₃, ζ - ζ²)` divided by `√3`.
- **The typos:** the statement types `z_j : [t₁, t₂] → ℂ³` for `ℂ` (TeX 11109), and the proof
  writes `u(0) = u'(0) = u''(0) = 0` for the initial conditions of `u₃` (TeX 11122).

### E66

**E66. §13.4 (TeX 11161–11177): "diffeomorphism".** The book calls the identification
`ℂ³ ∖ 0 ↔ ℝ_{>0} × Ξ`, `z ↦ (φ(z), (z₁/φ, z₂/φ², z₃/φ³))`, a diffeomorphism (TeX 11171).

- The function `φ⁶ = |z₁|⁶ + |z₂|³ + |z₃|²` is `C²` but not `C³` where `z₂ = 0` (the term
  `|z₂|³`), so `Ξ` is a `C²` hypersurface and the identification is a `C²` diffeomorphism, smooth
  only off `{z₂ = 0}`.
- The formalization states it as a homeomorphism ([`TriFuller.blowup`](../../SmoothedPolygons/Ch13/Blowup.lean#L341)) with `φ` of class `C²`,
  and smooth off `{z₂ = 0}` ([`TriFuller.contDiffOn_weightedNorm`](../../SmoothedPolygons/Ch13/Blowup.lean#L368),
  [`TriFuller.contDiffOn_weightedNorm_infty`](../../SmoothedPolygons/Ch13/Blowup.lean#L377)).
- The book uses the identification as coordinates, and its smoothness only near `q_out` (Lemma
  13.5.5), where `z₂ ≠ 0`.

### E67

**E67. §13.5 and Lemma 13.5.2 (TeX 11236–11251, 11298–11387): silent steps, a garbled display,
an omitted verification.**

- **(a)** `F` is well defined on the section because `0 < t_sw < 10φ(z⁰)` (Lemma 13.2.6,
  Corollary 13.2.7), `z(t_sw) ≠ 0` (Lemma 13.3.1) and `z₃(t_sw) ∈ 𝒲`; the definition cites none of
  this.
  - The formalization proves all three: the bound ([`TriFuller.firstSwitchTime_lt`](../../SmoothedPolygons/Ch13/PoincareMap.lean#L202)), `z(t_sw) ≠ 0`
    for every `z⁰ ≠ 0` and not only on the section ([`TriFuller.poincare_ne_zero`](../../SmoothedPolygons/Ch13/PoincareMap.lean#L211)), and the
    landing on the walls.
- **(b)** The display of the maximum principle at `t = 0, t_sw` (TeX 11363–11370) uses a
  one-argument `RR`, drops a factor `ū`, and names a dummy `ζ₂` that clashes with `ζ²`.
  - Its final condition, `z₃⁰ūζ₁² ∈ ℝ_{≤0}`, is right, but it follows only when `ζ₁ ≠ 1`: for
    `ζ₁ = 1` the conditions at `0` and at `t_sw` coincide and do not give it.
  - The case `ζ₁ = 1` is impossible because the control switches at `t_sw`, while by equivariance
    the control after `t_sw` would be `ζ₁u = u`; the book does not say so.
  - Three things are asserted without proof: the passage from the final condition to the three
    cases `(r, ζ₁)`, that `r_s` and `1/r_s` are the only real roots of the palindromic polynomial
    ([`TriFuller.rScalePoly_eq_zero_iff`](../../SmoothedPolygons/Ch13/RScale.lean#L147)), and the coordinates (13.5.1), which are computer-generated.
- **(c)** The proof does not check that `t_sw` is the first switching time of (13.5.1), that is,
  that the control `ζ` stays optimal on `(0, t_sw)`, nor that `H_F = 0` there, which the statement
  asserts.
  - Along (13.5.1), `H_F = (r² + r + 1)P(r)/(9(r + 1)²(1 + r³ + r⁶))`.
  - Both hold, and the formalization proves them exactly
    ([`TriFuller.firstSwitchTime_qOutCart`](../../SmoothedPolygons/Ch13/FixedPoints.lean#L462), [`TriFuller.hamMax_qOutCart`](../../SmoothedPolygons/Ch13/FixedPoints.lean#L492); Section 7).

### E68

**E68. Lemma 13.5.5, §13.5 (TeX 11433–11453): a numerical proof, and two steps not argued.**

- **The proof** gives no chart, matrix or eigenvalues: "An explicit calculation of the eigenvalues
  of the Jacobian matrix in terms of local coordinates centered at `q_out` gives the result.
  Numerically, the three eigenvalues have absolute value less than `0.1`. The calculations were
  made in Mathematica."
- **It does not argue:**
  - that `F_ang` is `C¹` near `q_out`, which holds by the implicit function theorem since `t_sw` is
    a simple root of the switching function there;
  - that `τ ∘ F_ang` is an involution near `q_out` and `q_in`, which "the second assertion follows
    from the first, because `q_in` is obtained by time reversal from `q_out`" needs, and which
    holds because the nearby points are genuine switching points (Lemma 13.2.5).
- **Here:** the lemma is true. The formalization:
  - fixes the chart `Re z₁ = -1`, `z₃ ∈ ℝ_{<0}`, `H_F = 0`;
  - computes the Jacobian exactly in `ℚ(√3, r_scale)` ([`TriFuller.jacobianOut`](../../SmoothedPolygons/Ch13/Jacobian.lean#L136));
  - certifies by sign changes of its characteristic polynomial that its eigenvalues (`≈ -0.0800`,
    `-0.0081`, `0.00065`) lie in `(-0.1, 0.1)`
    ([`TriFuller.norm_lt_of_aeval_charpoly_jacobianOut_eq_zero`](../../SmoothedPolygons/Ch13/Jacobian.lean#L1919));
  - proves linearized stability for maps and the time-reversal step ([`lemma13_5_5`](../../SmoothedPolygons/Ch13/Stability.lean#L281);
    Sections 2 and 7).

### E69

**E69. Remark 13.5.4, §13.5 (TeX 11402–11428): stated without proof.**

- **The book:** the remark interprets `q_fix = (1, -i/2, -1/2) mod 𝒢`, the fixed point for
  `(r, ζ₁) = (1, ζ)` in the proof of Lemma 13.5.2, as the limit, by the procedure of §14.2, of the
  one-parameter family of extremals of §7.5 that contains the smoothed `(6k+2)`-gons.
- This rests on a Mathematica computation (`MCA:zfix1`) and a forward reference, is not used
  later, and is not formalized.
- **Here:** the verifiable part holds and is proved ([`remark13_5_4`](../../SmoothedPolygons/Ch13/FixedPoints.lean#L698)): from `q_fix` the first
  control is `ζ²`, `t_sw = √3`, `F(q_fix) = ζ q_fix`, and `H_F⁺(q_fix) = 3/4`, so that, as the
  remark says, "the Fuller-system Hamiltonian is not zero at `q_fix`".

### E70

**E70. §15.1–15.3 (TeX 12139–12143, 12233–12276, 12419–12422): continuity asserted.**

**The book** asserts, without argument:

- that on the big open cells the first switching time is continuous off the loci `Δ_{A,0} = 0`,
  `Δ_{B,1} = 0` and `res_AB = 0`;
- that the dynamics extends continuously from the open cells to their top faces
  `𝒞₂(ζ^{±1}, 0, 2)` and to the 2-cell `𝒞₂(ζ, 1, 1)` on the front and back faces;
- that `F_A` and `F_B` are continuous on `𝒞₂^A` and `𝒞₂^B`.

These hold where the map of the face or of the 2-cell is itself continuous, which is not
everywhere on the 2-cell `𝒞₂(ζ, 1, 1)`, although the book claims continuity on all of it. On the
faces where the switching time tends to `0` the extension only changes the representative
(Proposition 15.2.2).

**Here:** the formalization proves each claim where it holds, by the continuity of a least
positive sign change of a family of functions, proved in [`Basic/`](../../Basic) (Section 2):

- off the three loci on the open cells
  ([`TriFuller.continuousAt_firstSwitchTime_of_ne_zero`](../../SmoothedPolygons/Ch15/Continuity.lean#L421));
- on the whole top face of the first cell ([`TriFuller.continuousWithinAt_topFaceOne`](../../SmoothedPolygons/Ch15/Continuity.lean#L484));
- on the top face of the second off `Δ_{A,0} = 0` ([`TriFuller.continuousWithinAt_topFaceTwo`](../../SmoothedPolygons/Ch15/Continuity.lean#L932));
- on the front and back faces where `Δ_{A,1}` and `Δ_{B,1}` do not vanish, a sufficient condition
  rather than a minimal one ([`TriFuller.continuousWithinAt_frontBackOne`](../../SmoothedPolygons/Ch15/Continuity.lean#L552));
- `F_A` and `F_B` on `{Δ_{A,0} ≥ 0}` and `{Δ_{A,0} ≤ 0}` ([`TriFuller.continuousOn_cellMapA_cellMapB`](../../SmoothedPolygons/Ch15/Continuity.lean#L892); at a
  double root of `χ_{A,0}`, through the shape of the cubic on the face).

**The resultant.** In `Ξ_{𝒲,0}/V_T` the locus `res_AB = 0` does not matter: a common simple root
of `χ_{A,0}` and `χ_{B,1}` is still a sign change of one of them, and the discontinuity along
`∂_res` of Remark 15.2.1 exists only in the cell complex, where `𝒞₂(ζ, 1, 1)` and `𝒞₂(ζ², 1, 1)`
are kept apart. The statement keeps the hypothesis `res_AB ≠ 0` (Section 5).

### E71

**E71. §15.1–15.3 (TeX 12038–12442): slips.**

- "Throughout this section" (TeX 12038) means this chapter.
- The face `r₂ = 0` of the second cell is identified through `f(ψ, θ₂) = θ₂ - ψ = θ₁`, whose
  domain is printed `[-π, 0] × [0, π]` and range `[0, 2π]` (TeX 12152–12153); on that cell
  `(ψ, θ₂) ∈ [0, π] × [-π, 0]` and `θ₁ ∈ [-2π, 0]`.
- The boundary region `ψ ∈ {0, π}`, `θ₂ ∈ [-π/3, 0]` lies on the second big cell, not the first
  (TeX 12186–12188), and its endpoint `θ₂ = -π/3` is not red: there the tie rule of Lemma 13.2.6
  makes `ζ²` the first control ([`boundary_maps_red_faces`](../../SmoothedPolygons/Ch15/SmallerCells.lean#L1498)).
- "Setting `r₁ = r̃₁e^{iψ}`" is reversed: `r̃₁ = r₁e^{iψ} = ±r₁` (TeX 12265).
- Proposition 15.2.2 is announced as "the following lemma" (TeX 12298).
- "The discriminant `Δ_{A,0}` vanishes along `∂_A`" (TeX 12426) should read `∂_{A,ζ²}`.
- A parenthesis opened at TeX 12439 is not closed, and `𝒞₂^B` is typeset `C_2^B` (TeX 12442).

The formalization uses the coordinates `(r₂, ψ, θ₂)` throughout and states each claim in its
intended form.

### E72

**E72. Propositions 15.2.2 and 15.3.2, §15.2–15.3 (TeX 12300–12314, 12467–12491): proved by the
discussion and by figures.**

The proofs are "See the discussion leading up to the statement of the proposition" (TeX 12312)
and "The proof is contained in the discussion leading up to the proposition" (TeX 12477–12478).

**Proposition 15.2.2.** The discussion suffices, except for its last claim, that every face point
not identified with a point of the domain has vanishing limiting switching time, which the book
reads off Figure 15.1 (TeX 12167–12195).

- The formalization assembles the discussion and proves that claim by semicontinuity: the cell's
  control is beaten at times arbitrarily close to `0` at the face point, hence, strict
  inequalities being open, at nearby points ([`proposition15_2_2`](../../SmoothedPolygons/Ch15/SmallerCells.lean#L1385), [`boundary_maps_red_faces`](../../SmoothedPolygons/Ch15/SmallerCells.lean#L1498)).

**Proposition 15.3.2** (the parts `𝒟₀, …, 𝒟₄` are geometric partitions of the two big cells, `F`
extends continuously to each, and `𝔦` exchanges `𝒟₃` and `𝒟₄` and maps `𝒟₀`, `𝒟₁` and `𝒟₂` to
themselves) rests on Figures 15.2–15.3 for its topology:

- that `∂_res ∪ ∂_A` cuts the first big cell into the parts described;
- that these are regular closed;
- that `𝒟₀` is "a very small bubble" attached to `∂_A` (TeX 12387).

The discussion does not say that `𝒟₀` is in self-involution. The formalization states the
proposition as a named proposition ([`TriFuller.Proposition15_3_2`](../../SmoothedPolygons/Ch15/Involution.lean#L892)), and the proof of Theorem 16.1.1
does not use it (E77). It proves part of it:

- the clauses that follow from the definitions of the parts (`𝒟₀` and `𝒟₁` are regular closed,
  `𝒟₀`, `𝒟₁` and `𝒟₄` cover the first cell, and the interior of `𝒟₀` meets neither that of `𝒟₁`
  nor that of `𝒟₄`; [`SmoothedPolygons/Ch15/PartitionTopology.lean`](../../SmoothedPolygons/Ch15/PartitionTopology.lean));
- the second clause, that `𝒟₂` and `𝒟₃` geometrically partition the second cell, which the book
  reads off Figure 15.3 (TeX 12392–12409) and the formalization proves by an exact deformation
  ([`TriFuller.isGeometricPartition_closedBoxTwo`](../../SmoothedPolygons/Ch15/PartitionCellTwo.lean#L570), Section 7);
- the continuous extensions of `F` to `𝒟₃` and `𝒟₄`, which are explicit
  ([`TriFuller.continuousOn_extD3`](../../SmoothedPolygons/Ch15/PartExtensions.lean#L384), [`TriFuller.continuousOn_extD4`](../../SmoothedPolygons/Ch15/PartExtensions.lean#L610)).

The rest is reduced to four statements ([`TriFuller.proposition15_3_2_of_remaining`](../../SmoothedPolygons/Ch15/PartitionCellTwo.lean#L595)):

- that `𝒟₄` is regular closed;
- that the interiors of `𝒟₁` and `𝒟₄` are disjoint;
- continuous extensions to `𝒟₀`, `𝒟₁` and `𝒟₂`;
- the action of `𝔦` on the parts.

An exact computation of the parts, checked numerically, found no counterexample (Section 9).

### E73

**E73. §15.3 (TeX 12324–12328, 12333–12344): `F⁻¹ = τFτ` only at switching points.**

- **The book:** "Since `F⁻¹ = τ∘F∘τ` and `τ = τ⁻¹`, it follows that `𝔦 := τ∘F` is an involution"
  (TeX 12324–12328) uses Lemma 13.2.5 without citing it, on the closed big cells.
- **Where it holds:** the identity holds at the switching points, the points whose first control
  is not also their most recent control, and every image `F(z)` is one.
- **Where it fails:** the points of the top faces `𝒞₂(ζ^{±1}, 0, 2)` are not switching points, and
  there it fails: for `z = (-0.3 + 0.7i, -0.6, -0.84) ∈ 𝒞₂(ζ, 0, 2)`, `t_sw(z) = 5.18584` while
  `t_sw(τFz) = 9.38584`.
  - So "By construction `∂_A` and `𝒞₂(ζ)` are in involution" (TeX 12344), where `𝒞₂(ζ, 0, 2)` is
    meant (the book's `𝒞₂(ζ)` is `𝒞₂(ζ, 1, 1)`), fails for `𝔦 = τF`: `𝔦(𝔦(x)) ≠ x` at the points
    of the top face.
- **Here:** the formalization proves the identity exactly at the switching points
  ([`TriFuller.poincare_tau_poincare_eq_tau_iff`](../../SmoothedPolygons/Ch15/Involution.lean#L237), [`TriFuller.not_isSwitchingPoint_of_mem_topFace`](../../SmoothedPolygons/Ch15/Involution.lean#L259); on
  `Ξ_{𝒲,0}/V_T`, [`TriFuller.involution_involution`](../../SmoothedPolygons/Ch15/Involution.lean#L406)).
  - It also proves it branch-wise for the book's root-based maps, which switch at a root of a
    switching function whether or not the control changes there ([`TriFuller.tau_flow_tau_flow`](../../SmoothedPolygons/Ch15/Involution.lean#L250)).
- Only the definitions of the loci `∂_res = 𝔦(𝒞₂(ζ, 1, 1))` and `∂_A = 𝔦(𝒞₂(ζ, 0, 2))` are used,
  with the vanishing of the resultant and the discriminants along the loci, which the book derives
  from Lemma 13.2.4 ([`TriFuller.discr_resAB_eq_zero_of_mem_bd`](../../SmoothedPolygons/Ch15/Involution.lean#L632)).

### E74

**E74. §15.3 (TeX 12411–12422): the switch on `𝒞₂^A`.** On the part `𝒞₂^A = {Δ_{A,0} ≥ 0}` of
the top face of the second cell, "The first switching time is a root of `χ_{A,0}` and is
continuous on `𝒞₂^A`" (TeX 12415–12416). Two things are left out.

- **The order of the roots:** that the least positive root `t₁` of `χ_{A,0}` comes before
  `t_B = -6y₁`, where `χ_B` changes sign and the control `ζ` takes over, is not argued.
  - It holds: `χ_A` decreases and then increases, so `t₁ > t_B` would give `χ_A(t_B) > 0` and
    `χ_A'(t_B) < 0`, which are incompatible in the coordinates of the face
    ([`TriFuller.leastPosRoot_chiA_le_of_mem_topFaceTwo`](../../SmoothedPolygons/Ch15/SmallerCells.lean#L1201); numerically `t₁ ≤ 2t_B/3`).
- **The double root:** on `Δ_{A,0} = 0` the root is double, a tangency at which the control `ζ²`
  stays optimal, so the dynamics does not switch there and switches at `t_B` instead.
  - For `r₂ = 1/2`, `ψ = 1.0548151712321…`, the double root is `t = 1.30848` and the switch is at
    `t_B = 2.60943`.
  - The book's `F_A` is thus the continuous extension of `F` from `{Δ_{A,0} > 0}`, not `F` itself.
- **Here:** the formalization defines both root-based maps ([`TriFuller.cellMapA`](../../SmoothedPolygons/Ch15/SmallerCells.lean#L465),
  [`TriFuller.cellMapB`](../../SmoothedPolygons/Ch15/SmallerCells.lean#L470)), proves that the Poincaré map is `F_A` on `{Δ_{A,0} > 0}` and `F_B` on
  `{Δ_{A,0} ≤ 0}` ([`TriFuller.firstSwitchTime_topFaceTwo`](../../SmoothedPolygons/Ch15/SmallerCells.lean#L1096)), and that both are continuous (E70).

### E75

**E75. Remark 15.3.1, §15.3 (TeX 12445–12461): `q_in` and `q_out` swapped.**

- **The book:** the remark gives "The fixed point `q_in ∈ 𝒟₁`" the coordinates
  `(r₂, ψ, θ₂) ≈ (0.267949, 0.1705935, 2.91574)` and "`q_out`" the coordinates
  `(r₂, π - ψ_in, π - θ_{2in})`.
- **The labels are swapped:** the printed point is the attracting fixed point `q_out` of Lemma
  13.5.2, the cell coordinates of (13.5.1), at which the Jacobian has eigenvalues of modulus
  `< 0.1` (Lemma 13.5.5).
  - Chapter 16 places `q_out` in `𝒟₀₀` and `q_in` in `𝒟₂₂` (TeX 12536–12537), which contain the
    printed point and its image under `τ`.
- **Here:** with the labels corrected, `q_out ≈ (0.267949, 0.1705935, 2.91574)` with `r₂ = 2 - √3`
  exactly, and `q_in = τ(q_out) ≈ (0.267949, 2.9709992, 0.2258527)` ([`remark15_3_1`](../../SmoothedPolygons/Ch15/FixedPointCells.lean#L287)).
- **The rest of the remark** then holds at `q_in`, along the segment `r₂ ↦ (r₂, ψ_in, θ_{2in})`:
  - `Δ_{B,1}` changes sign and the switch changes from `ζ²` to `1` (the boundary `∂_B`) between
    `r₂ = 0.26775` and `0.26777`;
  - `Δ_{A,0}` changes sign while the switching time jumps from above `0.95` to below `0.86` (the
    boundary `∂_A`) between `0.26790` and `0.26791`;
  - both before the fixed point at `2 - √3 ≈ 0.2679492` ([`remark15_3_1_segment`](../../SmoothedPolygons/Ch15/FixedPointCells.lean#L791)).
- Along the segment through the printed point nothing changes near `r₂ = 0.2679`.
- All the numbers are certified in exact rational arithmetic.
- That `q_in` and `q_out` lie in `𝒟₁` and that `q_out` is "far from the other parts `𝒟₀, 𝒟₄`" are
  read off Figure 15.2 and are not formalized (Section 9).

### E76

**E76. Theorem 16.1.1, §16.1 (TeX 12526–12537, 12680): the boxes.**

- **The index:** the boxes are printed
  `𝒟_ij = {r₂ ∈ [0, 1], ψ ∈ [a_i, a_{i+1}], θ₂ ∈ [b_{i+1}, b_i]}` (TeX 12529–12530), which do not
  depend on `j`.
  - `θ₂ ∈ [b_{j+1}, b_j]` is meant, and with it `q_out ∈ 𝒟₀₀` and `q_in ∈ 𝒟₂₂`, as the proof says
    (TeX 12536–12537, with the labels of E75; [`TriFuller.pOut_mem_cellBox_pIn_mem_cellBox`](../../SmoothedPolygons/Ch16/GlobalBasin.lean#L87)).
- "The cases `(i, j) = (0, 0), (2, 2)` are the cases `𝒟_in, 𝒟_out`" (TeX 12680) lists them in the
  wrong order.
- "`𝒟_{1,00} = 𝒟₀₀`" (TeX 12537) asserts `𝒟₀₀ ⊂ 𝒟₁`, which rests on Figure 15.2.
- **Here:** the formalization uses the boxes with the corrected index ([`TriFuller.cellBox`](../../SmoothedPolygons/Ch16/BasinHypotheses.lean#L97),
  [`TriFuller.boxSet`](../../SmoothedPolygons/Ch16/BasinHypotheses.lean#L103)), `𝒟_out = 𝒟₀₀`, and the whole box `𝒟₂₂` in place of `𝒟_in = 𝒟₁ ∩ 𝒟₂₂`, so
  that `𝒟₀₀ ⊂ 𝒟₁` is not needed.

### E77

**E77. Theorem 16.1.1, §16.1 (TeX 12541–12726): numerical containments by an unproved method.**

- **The book:** the proof rests on Table 16.1, a list of containments `F_i(𝒟) ⊂ ⋃ 𝒟*` among the
  parts `𝒟₀, …, 𝒟₄` of Proposition 15.3.2 and the boxes, justified by:
  - Mathematica computations (Figures 16.1–16.4: one image, and convex hulls of planar
    projections of sampled images);
  - a "boundary method": for a closed ball `𝒟 ⊂ 𝒟_i` and a closed convex `𝒟̃`, `F_i(∂𝒟) ⊂ 𝒟̃`
    "is enough" for `F_i(𝒟) ⊂ 𝒟̃` (TeX 12577–12587).
- **The gaps:** the method needs `F_i` continuous and injective on `𝒟` (then invariance of domain
  gives `∂F_i(𝒟) ⊆ F_i(∂𝒟)`), which the book does not state, and the images of the curved faces of
  the parts.
  - Some rows rest on facts read off Figures 15.2–15.3 (`𝔦(𝒟₂) = 𝒟₂`, `θ₂ ∈ [-π/3, 0]` on `𝒟₂`,
    `θ₁ ≤ 0` on `𝒟₄`, `𝒟₀` and `𝒟_in`).
  - The boundary method also needs the target `𝒟̃` convex (TeX 12579–12581), while the targets of
    the subclaims for `(i, j) = (1, 1), (1, 2), (2, 1)`, the unions of the boxes before `(i, j)`,
    are L-shaped in `(ψ, θ₂)`.
  - There it applies only through the convex hull of the image, which is what Figure 16.3
    compares with the target (TeX 12693–12713).
- **Here:** the formalization states what the proof needs as three named facts about the Poincaré
  map on whole boxes, [`TriFuller.DOutContracts`](../../SmoothedPolygons/Ch16/BasinHypotheses.lean#L236), [`TriFuller.CellTwoEntersDOut`](../../SmoothedPolygons/Ch16/BasinHypotheses.lean#L260) and
  [`TriFuller.BoxSubclaims`](../../SmoothedPolygons/Ch16/BasinHypotheses.lean#L278) (Section 2).
  - They merge rows of the table so that the curved parts and Proposition 15.3.2 are not needed.
  - By the user's decision, it proves them without computer assistance, by the exact structure of
    the map, which needs neither injectivity nor the curved faces (Section 7).
  - Theorems 16.1.1 and 16.2.1 are proved from them ([`theorem16_1_1`](../../SmoothedPolygons/Ch16/GlobalBasin.lean#L599), [`theorem16_2_1`](../../SmoothedPolygons/Ch16/OutwardFuller.lean#L567)), and
    so with no hypothesis ([`theorem16_1_1_unconditional`](../../SmoothedPolygons/Ch16/BasinFacts.lean#L52), [`theorem16_2_1_unconditional`](../../SmoothedPolygons/Ch16/BasinFacts.lean#L59)).

### E78

**E78. Theorem 16.1.1, §16.1 (TeX 12592–12607, 12728–12743): convergence in `𝒟_out`.**

- **The book:** the proof shows `F₁(𝒟_out) ⊂ 𝒟_out` and cites the local stability of `q_out`
  (Lemma 13.5.5) for "the iterates rapidly converge to the fixed point `q_out`" (TeX 12742–12743).
- **The gap:** the two give neither the convergence of every orbit in `𝒟_out` nor
  `⋂_k F^k(𝒟_out) = {q_out}`, which step (a) needs ("the iterates `F^{-k}(τq)` exit `𝒟_out` for
  all sufficiently large `k`", TeX 12731–12732).
  - "The forward iterates `F₁^k(𝒟_out)` quickly shrink toward `q_out`" (TeX 12595–12596) is read
    off one image (Figure 16.1).
- **Here:** the formalization adds a contraction to the first named fact: an iterate `F^N` maps
  `𝒟₀₀` into a box `B` of the open first cell on which `F`, in coordinates, is a self-map with
  Lipschitz constant `κ < 1` ([`TriFuller.DOutContracts`](../../SmoothedPolygons/Ch16/BasinHypotheses.lean#L236); proved with `N = 2`, `κ = 3/4` and
  `B ≈ [0.22, 0.30] × [0.080, 0.199] × [2.688, 3.009]`, [`TriFuller.dOutContracts`](../../SmoothedPolygons/Ch16/DOutContraction.lean#L1006)).
  - One step does not suffice: `𝒟₀₀` contains the edge `r₂ = 0`, `θ₁ = θ₂ - ψ ∈ [0.9944, π/3)`,
    where the first control is `1`; at nearby points the switching time tends to `0` and the image
    has `r₂` near `0`, so `F(𝒟₀₀)` lies in no compact box of the open cell.
  - Banach's fixed point theorem then gives the convergence on `𝒟₀₀` and makes every backward
    orbit inside `𝒟₀₀` constant at `q_out`, which is what step (a) uses.
- **Step (a) also needs** `F⁻¹(q_in) = {q_in}` at the points that are not switching points (E73),
  which the theorem's statement implies and the book does not mention; it is proved from the arc
  of the inward spiral ([`TriFuller.poincareAngZero_eq_qIn0_iff`](../../SmoothedPolygons/Ch16/GlobalBasin.lean#L305),
  [`TriFuller.flow_tau_qOutCart_not_mem_walls`](../../SmoothedPolygons/Ch16/GlobalBasin.lean#L177)).

### E79

**E79. Theorem 16.1.1, §16.1 (TeX 12668–12676, 12733–12737): the last row.**

- **The book:** the last row of Table 16.1, `F₁(𝒟₁ ∖ 𝒟_in) ⊂ 𝒟₁ ∖ 𝒟_in`, is derived from the
  subclaims by exclusion: "using facts `𝒞₃(ζ) = 𝒟₀ ∪ 𝒟₁ ∪ 𝒟₄` and `𝒟₀ ⊂ 𝒟_in` and
  `𝒟₄ ⊂ F𝒟₂₂ ∌ F(q₁)`, we get `F₁(q₁) ∈ 𝒟₁ ∖ 𝒟_in`" (TeX 12671–12676).
- **Three steps fail as written:**
  - `𝒟₀ ⊂ 𝒟_in` cannot hold: `𝒟_in ⊆ 𝒟₁`, and `𝒟₀` and `𝒟₁` are parts of a geometric partition,
    with disjoint interiors; `𝒟₀ ⊂ 𝒟₂₂` is presumably meant.
  - `F(q₁) ∉ F(𝒟₂₂)` for `q₁ ∉ 𝒟₂₂` needs `F` injective, which holds only at switching points
    (E73).
  - The boxes are closed, so the subclaims allow images on the faces that smaller boxes share with
    `𝒟₂₂` (for instance `ψ = 2π/3`), and do not exclude `𝒟_in`.
- **Here:** the formalization states the subclaims on whole boxes, merged with the row `𝒟₄`, with
  the target "the second big cell or a smaller box" ([`TriFuller.BoxSubclaims`](../../SmoothedPolygons/Ch16/BasinHypotheses.lean#L278)), and tracks the box
  indices in the descent.
  - It proves that no orbit re-enters `𝒟₂₂` by the time reversal of step (a): for a switching
    point `x`, `F(x) ∈ 𝒟₂₂` implies `x ∈ 𝒟₂₂`, since `τ(𝒟₂₂) = 𝒟₀₀`, `F(τF(x)) = τ(x)` and
    `F(𝒟₀₀) ⊆ 𝒟₀₀` ([`theorem16_1_1`](../../SmoothedPolygons/Ch16/GlobalBasin.lean#L599); Section 7).
- The claim at TeX 12670 also has an unbalanced parenthesis.

### E80

**E80. Theorem 16.2.1, §16.2 (TeX 12763–12778): details left implicit.**

- **The book:** the proof reduces the outward case to the inward one by time reversal.
- It argues that for a switching point `q ≠ q_in`, "by the Fuller basin theorem and by the
  stability calculation near `q_in`", the iterates approach the outward spiral, which "moves away
  from the singular locus (because of the scaling factor `r_scale > 1`), and the Fuller trajectory
  must then also move away".
- **Three details are left implicit.**
  - Theorem 16.1.1 is about `Ξ_{𝒲,0}`, while the proof takes "`q ∈ Ξ_𝒲/V_T`" (TeX 12765); along a
    trajectory tending to `0` the Hamiltonian `H_F⁺` vanishes, because it is invariant under `F`,
    continuous and `0` at `0` ([`TriFuller.hamMax_eq_zero_of_tendsto_zero`](../../SmoothedPolygons/Ch16/OutwardFuller.lean#L472)).
  - "Must also move away" needs the factor by which one step multiplies the weighted norm `φ` to
    tend to `r_scale > 1`. It does, by its continuity at `q_out`, which the formalization proves in
    the chart of Lemma 13.5.5 ([`TriFuller.continuousAt_radialFactor_qOut0`](../../SmoothedPolygons/Ch16/OutwardFuller.lean#L404)), so that the weighted
    norms eventually grow geometrically.
  - The time reversal applies `F⁻¹ = τFτ` at the points `z_{k+1} = F(z_{k+2})` of the trajectory,
    which are switching points (E73).
- "The stability calculation near `q_in`" is not needed, since Theorem 16.1.1 covers every
  `q ≠ q_in`.
- The proof calls the theorem "the lemma" (TeX 12764).
- **Here:** the theorem is proved from the three named facts of Theorem 16.1.1
  ([`theorem16_2_1`](../../SmoothedPolygons/Ch16/OutwardFuller.lean#L567)), which are proved ([`theorem16_2_1_unconditional`](../../SmoothedPolygons/Ch16/BasinFacts.lean#L59)).

### E81

**E81. §14.1 (TeX 11561–11602): slips and assertions.**

- The matrix displayed as `X̃` (TeX 11582) is `X = J + rX̃`, as its entries show: `X₁₁ = r` and
  `X₂₁ = 1 + r x̃₂₁` ([`lieX`](../../SmoothedPolygons/Ch14/LieChart.lean#L89)).
- `H*` (TeX 11566–11567) imposes only the boundary `x = 1/√3` of the star domain, not
  `x² + y² > 1/3`, which is harmless near `r = 0` ([`lieX_starBoundary_iff`](../../SmoothedPolygons/Ch14/LieChart.lean#L408)).
- **Asserted:** that the linear system (14.1.3) for `Λ_R` is "always a full rank system" and that
  the diagonal and the off-diagonal entries of `Λ_R` have orders `O(r⁴)` and `O(r³)`
  (TeX 11595–11597) are asserted without proof. Both hold on `H*`.
- **Here:** the formalization solves (14.1.3) in closed form: for traceless `X` with `X₂₁ ≠ 0`,
  `Λ_R = hK(X)`, with `h = ⟨Λ₁ + (3/2)J, X⟩` and `K(X)` the matrix `X` with its `(1, 2)` entry
  changed so that `⟨X, K(X)⟩ = 0` ([`lieΛR_eq_reducedHam_smul`](../../SmoothedPolygons/Ch14/LieChart.lean#L256)).
  - The system has determinant `-(8/(3√3))X₂₁`, so it has full rank exactly when `X₂₁ ≠ 0`, which
    holds on `H*`, where `X₂₁ = 1 + r x̃₂₁ ≥ √3 r > 0` (TeX 11575–11578).
  - `h = r³g(r)` with `g` continuous at `0` gives the orders ([`lieChart_lieChartInv`](../../SmoothedPolygons/Ch14/LieChart.lean#L440),
    [`isBigO_lieΛR`](../../SmoothedPolygons/Ch14/LieChart.lean#L535)).

### E82

**E82. §14.2 (TeX 11612–11701): slips.**

- "We construct a uniquely determined element `ξ(x̃) ∈ Ξ_{𝒲,0}`" (TeX 11616–11617, for every
  `x̃ ∈ ℝ³`) holds only when `ℓ̃₁₁ + ℓ̃₂₁x̃₂₁ ≤ 0`: the third coordinate of `z(x̃)` is the real
  number `(ℓ̃₁₁ + ℓ̃₂₁x̃₂₁)/6`, which lies on the walls `𝒲` only when it is `≤ 0` ([`xiOfChart`](../../SmoothedPolygons/Ch14/Asymptotics.lean#L126)).
  - The chart is used near `x̃_out`, where the sum is `≈ -2.21`.
- The arguments of `H_F` appear in both orders (TeX 11654, 11665; Chapter 13 writes `H_F(z, u)`).
- Remark 14.2.1 prints `x̃_out ≈ (-2.39, -4.90, -1.12)`; the third entry is `-1.1264…`, `-1.13` to
  two decimals.
- Its normalization `x̃₁₁ = 1` and that of Lemma 13.5.2, `Re z₁ = -1`, differ by the virial
  rescaling by `1/(2 Im q_out,₁) ≈ 1.1944`, so that `s_sw,out ≈ 8.84` in Lemma 14.3.1 and
  `t_sw ≈ 7.40` in Lemma 13.5.2 are the same switching time; the book does not say so.
- Remark 14.2.2 names "Manita and Ronzhina in their inverted pendulum paper" without a citation:
  the `\cite` is commented out in the source (TeX 11698–11701).
- **Here:** the formalization states Remark 14.2.1 as an enclosure of `x̃_out` within `0.01` of the
  printed values, with the exact identity that `z(x̃_out)` is the virial rescaling of `q_out` by
  `1/(2 Im q_out,₁)` ([`remark14_2_1`](../../SmoothedPolygons/Ch14/Asymptotics.lean#L578)).

### E83

**E83. §14.2 and Lemma 14.3.1 (TeX 11706–11718, 11835–11836): the first control.**

- **The book:** "For a given `x̃`, the first control of `(X(r, x̃), Λ₁(r, x̃), Λ_R(r, x̃))` is
  `u = e₂` for all sufficiently small `r > 0`, provided we assume `ℓ̃₁₁ + ℓ̃₂₁x̃₂₁ < 0` and
  `ℓ̃₂₁ < 0`" (TeX 11710–11717) is stated without proof (and with an unbalanced parenthesis).
- **A stronger form:** the proof of Lemma 14.3.1 uses it in a stronger form: that an extremal
  through a chart point near `(0, x̃_out)` leaves it with the control `e₂` and switches next where
  the `e₂`-flow does ("These functions give the value of the Reinhardt–Poincaré map",
  TeX 11835–11836).
- **It holds,** by the two signs that the book names. On the section, for `X = [[a, b], [c, -a]]`:
  - `H(e₁) = 6h/(3 + 3a² - c²)` with `h = r³G(r, x̃)` and `G(0, x̃) = 2(ℓ̃₁₁ + ℓ̃₂₁x̃₂₁) < 0`, so
    `e₁` is not a maximizer;
  - the slope of `χ₃₂` along the fields of `e₂` and of `e₃` is
    `4√3r²(crG + ℓ̃₂₁)/(c² - 3r²) < 0`, so `e₃` would leave the maximum at once.
- **Here:** the formalization proves the claim:
  - for the `e₂`-flow, for each `x̃` ([`eventually_firstControl_lieChart`](../../SmoothedPolygons/Ch14/Asymptotics.lean#L615));
  - for every extremal through a chart point near `(0, x̃_out)`, uniformly: the control after the
    point is `e₂`, and the next switch is at the switching time of the `e₂`-flow
    ([`eventually_switchStructure`](../../SmoothedPolygons/Ch16/SwitchStructure.lean#L389), [`IsChatteringArcInto.next_switchPoint_eq_reinPoincare`](../../SmoothedPolygons/Ch16/NextSwitch.lean#L388)).
- The proof of Theorem 16.4.1 uses the second form (Section 7).

### E84

**E84. Lemmas 14.2.3–14.2.4 (TeX 11720–11758): Mathematica sketches.**

- **The book:** the proofs are "Use the explicit solutions on both sides and expand as a series in
  the parameter `r₀`" and "Expand both sides in an explicit series", with the Mathematica cell
  `MCA:2446603`.
- **The condition:** "For each `s` such that `r(s) < 1`" (TeX 11727) is not the condition that
  matters: for fixed `s` it holds for all small `r₀`, since the chart coordinate along the flow
  tends to `0`, while the uniformity in `s` that the proof of Lemma 14.3.1 needs is not stated.
- **Here:** both lemmas are true. The formalization drops the condition and compares differential
  equations instead of series:
  - with the weights `(r₀, r₀², r₀³)` of `X - J`, `Λ₁ + (3/2)J` and `Λ_R`, the extremal equations
    along `e₂` have a leading part whose solution, a matrix polynomial in `(r₀, t)`, is in Cayley
    coordinates the Fuller flow with control `ζ`;
  - three Grönwall steps bound the errors by `O(r₀²)`, `O(r₀³)`, `O(r₀⁴)` uniformly for
    `|t| ≤ Sr₀` ([`chartFlow_estimates`](../../SmoothedPolygons/Ch14/ChartFlow.lean#L777)).
  - One estimate covers every pair of switching functions, so the "similar formulas" for the other
    switching functions (TeX 11754) are proved too ([`lemma14_2_3`](../../SmoothedPolygons/Ch14/Asymptotics.lean#L733), [`lemma14_2_4`](../../SmoothedPolygons/Ch14/Asymptotics.lean#L744),
    [`lemma14_2_4_chi23`](../../SmoothedPolygons/Ch14/Asymptotics.lean#L756)).
  - The uniformity that Lemma 14.3.1 needs comes from analyticity
    ([`analyticAt_rescaledChi`](../../SmoothedPolygons/Ch14/AnalyticExtension.lean#L373); Section 7).

### E85

**E85. Lemma 14.3.1 (TeX 11784–11872): steps asserted or sketched.** Three steps of the proof are
incomplete, and one has a slip.

- **(a)** The switching time is the least positive zero of `χ̃₂₁` (TeX 11807–11821); that the
  switching function `χ₂₃`, which vanishes on the wall at `s = 0`, has no zero in `(0, s_sw]`, so
  that the control `e₂` stays optimal up to the switch, is not argued.
- **(b)** "`ad_{R⁻¹}`" (TeX 11826, 11829) is the group action `Ad_{R⁻¹}`.
- **(c)** The divisibility of `X_sw - J` by `r₀` and of `Λ₁sw + (3/2)J` by `r₀²`, "regardless of
  the precise form of `s_sw`" (TeX 11841–11848), is asserted.
- **(d)** The last step is a sketch: "In similar way to what we have done, we can show analyticity
  and analytic continuation of the Reinhardt–Poincaré map `F⁻¹` that moves backwards in time … By
  analytic continuation, they are inverse functions in a neighborhood of the fixed point. Hence,
  `F` is a diffeomorphism" (TeX 11864–11871).

**Here:** the lemma is true, and the formalization proves it along the book's lines
([`lemma14_3_1`](../../SmoothedPolygons/Ch14/AnalyticExtension.lean#L1217)):

- (a) by one more division by `s`, `χ̃₂₃ = sH` with `H > 0` near the divisor point
  ([`exists_extChi23_eq_mul`](../../SmoothedPolygons/Ch14/ExtensionConstruction.lean#L1330), [`eventually_extChi23_pos`](../../SmoothedPolygons/Ch14/ExtensionConstruction.lean#L1377));
- (c) from Lemma 14.2.3 with `det X = 1` and `det Λ₁ = 9/4`;
- the zero structure at the fixed point (the book's `s_sw,out ≈ 8.84`, a simple zero, and `s = 0`
  not a zero, TeX 11811–11813) exactly, by factoring the Fuller cubic
  ([`extSwitchTime_zero_structure`](../../SmoothedPolygons/Ch14/ExtensionConstruction.lean#L1418));
- and (d) by the book's route.

**One construction, applied twice.** The construction of the analytic map (the switching time by
the analytic implicit function theorem, the switched state, its chart coordinates) is stated once,
for a divisor point with its Fuller data on either side of the divisor, and applied twice:

- to `F` at `(0, x̃_out)`;
- to `F⁻¹`, which the time reversal turns into the forward map at the reflected point
  `(0, x̃_in)` from the side `r < 0`, with Fuller data derived from those at `x̃_out`, not
  estimated at `q_in` ([`fullerSwitchData_out`](../../SmoothedPolygons/Ch14/ExtensionConstruction.lean#L938), [`fullerSwitchData_in`](../../SmoothedPolygons/Ch14/ExtensionConstruction.lean#L1094)).

For `r > 0` the two maps are inverse by the time reversal of trajectories
([`reinPoincare_reinTau_reinPoincare`](../../SmoothedPolygons/Ch14/AnalyticExtension.lean#L990)), and by the identity theorem they are inverse on a
neighbourhood of the fixed point. Section 11 gives a shorter argument for (d).

### E86

**E86. Theorem 14.3.3 (TeX 11891–11919): implicit steps.**

- **Which map:** "The Fuller-Poincaré map is therefore hyperbolic, with three eigenvalues
  `|λ| < 1` and one eigenvalue `|λ| > 1`" (TeX 11915–11917) is about the extended map `F`, not
  the Fuller–Poincaré map.
- **The block form:** it rests on the block-triangular form of `DF` at the fixed point, which
  follows from the two facts that the proof names (the divisor `r = 0` is invariant, and the
  radial scaling factor is `r_scale`) but is not stated.
- **The stable manifold:** that near the fixed point the local stable manifold is the exceptional
  divisor is not argued either: it needs that the divisor points near `x̃_out` tend to it and that
  no other point does.
- **Here:** the theorem is true. The formalization proves:
  - the block form and the spectrum (`r_scale`, a simple root of the characteristic polynomial,
    and three eigenvalues of modulus `< 1/10`; [`hasStrictFDerivAt_extension`](../../SmoothedPolygons/Ch14/FixedPointManifolds.lean#L126),
    [`theorem14_3_3`](../../SmoothedPolygons/Ch14/FixedPointManifolds.lean#L694));
  - the local stable set directly: near the fixed point `|F₁(r, x̃)| ≥ |r|` (by the mean value
    theorem, `∂_r F₁ > 1` and `F₁(0, ·) = 0`), so no orbit with `r ≠ 0` tends to the fixed point,
  - and the divisor has an open neighbourhood of `x̃_out` that is forward invariant and attracted
    to it (linearized stability);
  - the `C^∞` unstable curve, a graph over the `r`-axis, from Theorem A.3.1 (Section 7).

### E87

**E87. Remark 14.3.4 (TeX 11898–11902) and Theorem 14.4.1 (TeX 11999–12001): outside the
chart.**

- The chart (14.1.1)–(14.1.2) normalizes `x̃₁₁ = 1`, so that `Im ẑ₁ > 0` on it
  (`z(x̃)₁ = (x̃₂₁ + i)/2`), and the book chose `x̃₁₁ > 0` on purpose (a TeX comment, 11543–11546).
- But the representatives of `q_in = τ(q_out)` on the wall `𝒲₀` have `Im z₁ < 0`. So
  "`(0, x_in) ∈ ℝ⁴`" is not a point of the chart, and the remark, whose proof is "By time
  reversal", needs another chart.
- **Here:** the formalization states it in the mirrored chart `lieChartIn = τ ∘ lieChart`, which
  normalizes `x̃₁₁ = -1` and in which `(0, x̃_out)` lies over `q_in`.
  - There the Reinhardt–Poincaré map is the inverse of the extended map `e` near the fixed point
    (it is `F⁻¹ = τFτ`, the backward map of Lemma 14.3.1, whose switching structure is the second
    instance of the construction, E85).
  - So `e⁻¹` has a hyperbolic fixed point whose local stable manifold is the curve of Theorem
    14.3.3 and whose local unstable manifold is the divisor ([`remark14_3_4`](../../SmoothedPolygons/Ch14/FixedPointManifolds.lean#L825)).
- **Theorem 14.4.1:** its second statement ("A trajectory … that tends to the fixed point
  `(r, x̃) = (0, x_in)`") places `q_in` in the chart too. The formalization states it with the
  switching points converging to `q_in = τ(q_out)` modulo `V_T`, without a chart
  ([`Theorem14_4_1`](../../SmoothedPolygons/Ch14/NoReturn.lean#L108)).

### E88

**E88. Theorem 14.4.1, §14.4 (TeX 11951–12013): a numerical proof, and steps not cited.**

**The numerical proof.** The proof (TeX 12004–12012) rests on the global unstable curve
`W^u(q_out)`, computed in Mathematica and shown in Figure 14.2 ("a piecewise linear curve joining
434 data points").

The authors write that these calculations "might be repeated using more rigorous numerical
methods such as interval arithmetic", which they have not done (TeX 11951–11955).

**Steps not cited.** The proof also uses steps that it does not cite:

- "All switches must be on the unstable curve" (TeX 12004–12005) is the time reversal of the
  second part of Theorem 16.4.1, for a trajectory that emanates from the divisor;
- "Any trajectory that returns to the singular locus must chatter" (TeX 12005–12007) is Lemma
  8.3.4 at the first return;
- that the forward iterates of a point of the curve cannot tend to the divisor "because the
  unstable curve hits the boundary of the star domain" (TeX 12009–12010) needs every orbit on the
  curve to switch cyclically until an arc from it leaves the star domain before its next switch,
  which the running text reads off the computation (TeX 11983–11991).

**Here:** by the user's decision the formalization proves the computed fact instead of computing
it: N4 ([`UnstableCurveLeavesStarDomain`](../../SmoothedPolygons/Ch14/UnstableCurve.lean#L174), Section 6) is [`unstableCurveLeavesStarDomain`](../../SmoothedPolygons/Ch14/ArcRegionInvariant.lean#L338), proved
without locating the curve.

- Along an `e₂`-arc `ρ₁ = ε` is constant and the flow is hyperbolic with rate `1/(2ε)`, so the
  state, the exit time `T = ε log Y` (through `ρ₂ = 0`, with `Y = 1 + ρ₂(0)/ε`) and the cleared
  switching functions are explicit, the latter exponential sums with four terms.
- One step of the Reinhardt–Poincaré map is then an explicit map of four parameters.
- An explicit region `𝒢*` of section points, which contains every chart point near the fixed
  point, is kept by that step until an arc leaves the star domain, while `r` grows and `ρ₁` drops
  by `2r` at each step.
- So every orbit in `𝒢*` leaves the star domain ([`arcRegionInvariant`](../../SmoothedPolygons/Ch14/ArcRegionInvariant.lean#L326), by polynomial identities,
  three Bernstein certificates with nonnegative rational coefficients and inequalities for `log`;
  Section 7).
- The uncited steps are proved ([`IsChatteringArcOutOf.eventually_mem_localUnstableSet`](../../SmoothedPolygons/Ch16/ClusterPoint.lean#L921), which
  needs no numerical fact, and [`exists_isChatteringArcInto`](../../SmoothedPolygons/Ch16/ClusterCoordinates.lean#L376)).
- With N4 the book's proof gives Theorem 14.4.1 ([`theorem14_4_1`](../../SmoothedPolygons/Ch14/NoReturnProof.lean#L170),
  [`theorem14_4_1_unconditional`](../../SmoothedPolygons/Ch16/MahlerFirstArcRegion.lean#L51)) and Mahler's First conjecture
  ([`theorem16_3_1_unconditional`](../../SmoothedPolygons/Ch16/MahlerFirstArcRegion.lean#L94)).

The computation of the curve is not repeated in Lean, and the figure's numbers are not stated
(Section 6).

### E89

**E89. Theorem 16.3.1, the last step (TeX 12820–12833): "the trajectory is not periodic".** The
contradiction is compressed.

- Theorem 16.4.1 is about trajectories with `λ_cost = -1`, which at `𝒮_sing` needs Lemma 8.2.2
  and a rescaling of the costate.
- "By Theorem 14.4.1 and its time reversal, the stable curve `W^s(q_in)` did not come from the
  exceptional divisor at an earlier time. Thus, the trajectory is not periodic" needs an earlier
  meeting with `𝒮_sing`, and a trajectory between the two meetings that is bang-bang with finitely
  many switches.

**Here:** the formalization makes the step precise
([`noChatteringIntoSingularLocus_of_theorem14_4_1`](../../SmoothedPolygons/Ch16/NoChattering.lean#L376)):

- it normalizes `λ_cost = -1` ([`IsExtremalOn.normalize`](../../SmoothedPolygons/Ch16/NoChattering.lean#L135));
- extends the extremal periodically (Remark 6.6.1), so that, by `R⁻¹JR = J`, its lift meets
  `𝒮_sing` again at `t + T`, chattering into it from the left;
- takes the last meeting time `e` before `t + T`;
- glues at `T` the finite bang-bang structure that Theorem 8.3.2 gives on each period (the
  extension is not edge extremal across `T`);
- and applies the first part of Theorem 16.4.1 and the second part of Theorem 14.4.1 on
  `[e, t + T]`, which contradicts the meeting at `e`.

Theorem 16.3.1 then follows from Theorem 14.4.1 and the three numerical facts of Theorem 16.1.1
([`theorem16_3_1_of_theorem14_4_1`](../../SmoothedPolygons/Ch16/NoChattering.lean#L387)), all of which are proved ([`theorem16_3_1_unconditional`](../../SmoothedPolygons/Ch16/MahlerFirstArcRegion.lean#L94)); the
second part of Theorem 16.4.1, the stable curve, is not used.

This complements E60, which handles the set of meeting times.

### E90

**E90. §16.4 and Theorem 16.4.1, steps (d)–(f) (TeX 12862–12987, 13028–13055): Reinhardt cells
asserted.**

**The book.** §16.4.2 argues that near the divisor the rescaled Reinhardt switching functions
"behave qualitatively like a monic cubic polynomial" and makes this precise by Weierstrass
preparation.

It concludes: "All of these defining conditions can be carried over to the Reinhardt dynamical
system … We obtain a geometric partition of the two big cells into five regular closed sets
`𝒟_i^R` … and a continuous extension `F_i` of the Reinhardt-Poincaré map" (TeX 12956–12976).

Here and in E91 the proof of Theorem 16.4.1, TeX 12991–13056, is cited in six steps, in the order
of the text:

| Step | Content |
| --- | --- |
| (a) | the switching sequence is injective |
| (b) | a cluster point at `q_in` is a limit |
| (c) | `q_out` is not a cluster point |
| (d) | the cluster points are assigned to parts |
| (e) | the descent |
| (f) | the conclusion |

Steps (d)–(f) run the descent of Table 16.1 through these parts, to a cluster point in `𝒟_out^R`.

**Several claims are unsupported.**

- The parts `𝒟_i^R` and the continuous branches `F_i` are asserted; they rest on Proposition
  15.3.2, read off figures (E72), and on control of the Reinhardt switching functions uniform near
  the whole divisor, the faces where `t_sw → 0` included.
- The zero count ("at most three zeros", TeX 12894–12902) bounds one constant-control piece of a
  trajectory, not the number of pieces: the third derivative changes sign with the control.
- `χ_W` "captures all real roots of `χ`" (TeX 12939–12941) only for `s` in a bounded range.
- The descent ignores the diagonal rows of Table 16.1, so a cluster point in `𝒟_in` may map into
  `𝒟_in`.
- `𝒟_out^R` is called "the local stable manifold", with "The dynamics are analytic on `𝒟_out^R`"
  (TeX 13050–13053), which is not shown: Lemma 14.3.1 is local at the fixed point.

(§16.4.1 also prints `c/6ρ` for `c/(6ρ)`, TeX 12862.)

**Here:** the formalization proves the one property that the descent serves, that the image of a
cluster point is a cluster point: the set `Ω` of cluster classes of the switching points is mapped
into itself by the Fuller–Poincaré map `F_ang` ([`clusterSetForwardInvariant`](../../SmoothedPolygons/Ch16/ReinhardtShadowing.lean#L802)). The proof uses:

- the uniform convergence of the rescaled Reinhardt vector field and Hamiltonians on the control
  triangle `U_T` ([`tendstoUniformlyOn_rescaledField`](../../SmoothedPolygons/Ch16/RescaledDynamics.lean#L529), [`tendstoUniformlyOn_rescaledHam`](../../SmoothedPolygons/Ch16/RescaledDynamics.lean#L539));
- relaxed limits of the rescaled controls ([`exists_tendsto_rescaledArc`](../../SmoothedPolygons/Ch16/RescaledLimits.lean#L1302),
  [`TriFuller.eq_flow_of_maxCondition_UT`](../../SmoothedPolygons/Ch16/RelaxedFuller.lean#L291), [`TriFuller.firstControl_beaten_UT`](../../SmoothedPolygons/Ch16/RelaxedFuller.lean#L355)).

It then concludes as the book's last paragraph does: for `ω ∈ Ω ∖ {q_in}`, Theorem 16.1.1 gives
`F^k(ω) → q_out`, so `q_out ∈ Ω`, since `Ω` is closed and invariant, which E91 excludes; hence
`Ω = {q_in}` ([`tendstoModVT_switchAng_of_clusterSetForwardInvariant`](../../SmoothedPolygons/Ch16/ClusterPoint.lean#L967)).

No Reinhardt cells, parts, branch maps or Weierstrass polynomials are needed, and the three
numerical facts of Theorem 16.1.1 suffice (Section 7).

### E91

**E91. Theorem 16.4.1, steps (b)–(c) (TeX 13001–13026): from a cluster point to a limit.**

- **The book:** if `q_in` is a cluster point, "the finite time hypothesis implies that the limit
  of the sequence exists and equals `q_in`, because of the time required to travel from outside an
  `ε`-ball with center `q_in` to a point inside an `ε/r_scale`-ball" (TeX 13006–13014).
- The same argument is invoked to exclude `q_out` (TeX 13022–13023).
- **The gap:** it does not show that a cluster point at a hyperbolic fixed point is a limit: such a
  point repels along its unstable direction.
- Step (c) also uses that `W^s(q_out)` lies in the divisor globally, while Theorem 14.3.3 is local.
- **Here:** the formalization replaces both steps.
  - The lift converges at the finite time `b`, so the radial coordinates of the switching points
    tend to `0` along the whole sequence.
  - `q_out` is excluded as a cluster point by a hyperbolic box, which uses only the derivative of
    the extended map at the fixed point (the transverse expansion by `r_scale` and the contraction
    along the divisor; [`Function.not_mapClusterPt_of_transverse_expansion`](../../Basic/Dynamics/HyperbolicBox.lean#L117),
    [`qOut0_not_mem_switchClusterSet`](../../SmoothedPolygons/Ch16/ClusterPoint.lean#L631)).
  - The convergence to `q_in` follows from `Ω = {q_in}` (E90).
  - The switching points then lie on the local stable curve at `q_in`, by the definition of the
    local unstable set of the extended map `e`, which Remark 14.3.4 makes the local stable set of
    `e⁻¹` at `q_in` ([`theorem16_4_1`](../../SmoothedPolygons/Ch16/ClusterPoint.lean#L1021)).

### E92

**E92. Appendix A.3 (TeX 13183–13210): definitions.**

- **The local stable set** is "the set of all `q ∈ U` such that `lim_{n→∞} fⁿ(q) = p`"
  (TeX 13187–13189), which omits that the orbit stays in `U`, as the iterates of `f|_U` in Theorem
  A.3.1 require.
- **The summands:** the stable and unstable summands are defined "according to the factorization
  of the characteristic polynomial" (TeX 13193–13197). The formalization defines them by the
  dynamics (the vectors whose forward, respectively backward, orbit under `Df(p)` tends to `0`),
  and the two agree at a hyperbolic fixed point.
- **Theorem A.3.1** is formalized in its local part, for an open partial homeomorphism of a
  finite-dimensional space, with the submanifolds as graphs over the summands and with the unstable
  statement ("There are corresponding statements for local and global unstable manifolds",
  TeX 13209–13210).
  - The proof applies the package's theorem for one neighbourhood, which gives some open
    neighbourhood `U` of `p`, not necessarily inside the source, to the map cut off outside the
    source.
  - That map sends every other point to a point outside the source, so that the local sets of the
    map on `U ∩ source` are those of the cut-off map on `U` ([`theoremA_3_1`](../../SmoothedPolygons/AppA/StableManifold.lean#L186); Section 7).
  - The package's form for every small neighbourhood makes the cut-off unnecessary (Section 11).
  - The global (immersed) part is not stated: no proof of the book uses it (Section 9).

### E93

**E93. §14.4 (TeX 11924–11932, 11966–11977): the global unstable curve.**

- **The book:** "The previous theorem shows the existence of a `C^∞` curve (the global unstable
  manifold around the fixed point `(0, x_out)`) … `t ≥ 0`, for some local parameter `t`"
  (TeX 11925–11931).
- **The gap:** Theorem 14.3.3 gives only the local unstable curve. The global one is the union of
  its images under the Reinhardt–Poincaré map, which is defined only while the `e₂`-arc from a
  point switches inside the star domain.
  - So how far the curve extends is what Figure 14.2 is meant to show, not something the theorem
    gives.
- **The parameter:** the figure also draws the curve as a graph `r ↦ x̃₂₁(r)` up to `r ≈ 0.21`
  (TeX 11969–11972, 11985–11987), while `t = r` is introduced only as a local parameter
  (TeX 11931–11932).
- **Here:** the formalization needs neither: N4 is stated on the local curve, for the forward
  orbits of the Reinhardt–Poincaré map, and its proof shows that `r` increases along every orbit in
  `𝒢*` ([`radius_lt_of_mem_arcRegion`](../../SmoothedPolygons/Ch14/ArcConditions.lean#L409); E88).

### E94

**E94. §14.4 (TeX 11951–11955, 11987–11993): the threshold is degenerate.**

- **The threshold:** at `r* ≈ 0.0649` on the curve (the book's "about 0.065"; a TeX comment, 11993,
  gives `0.0641`) the switching time and the exit time of the arc coincide, and the cleared
  switching function at the exit tends to `0`.
- **No margin:** so no uniform margin decides "switch, then exit" against "exit first" near `r*`,
  and the repetition by interval arithmetic that the book suggests (TeX 11951–11955) cannot settle
  a neighbourhood of `r*` without a local asymptotic argument.
  - Just below `r*` the next arc starts near the side `ρ₁ = 0` and runs into a cusp of `𝔥*`.
- **Here:** the formalization does not decide the order: the proof of N4 (E88) treats "switch" and
  "exit" as the two signs of an explicit function of the arc's parameters, `F(log Y)`, each case
  proved on the whole region `𝒢*`, so the threshold needs no margin.

## Missing hypotheses

| Where | Missing hypothesis | Counterexample without it | In the formalization |
| --- | --- | --- | --- |
| Theorem 3.1.4(3) | `σ_j'` Lipschitz (the standing assumption of §2.4, through Lemma 2.4.3) | unit disk, `σ_j(t) = Rot(t + t^{3/2}) s_j*`, `X = (1 + (3/2)√t)J` | hypothesis of [`theorem3_1_4_lipschitz`](../../SmoothedPolygons/Ch3/StateDynamics.lean#L283) (approved by the user) |
| Lemma 3.1.8 | the curves `σ_j` are regular, `σ_j' ≠ 0` (§2.4, TeX 1945–1946: "a regular `C¹` curve") | the square `[-λ, λ]²`, `λ² = √3/2`: `σ₂ = (-λ, 0)` constant while `σ₁`, `σ₃` slide along the parallel lines `y = ±λ` (E34) | hypothesis `hreg` of [`lemma3_1_8`](../../SmoothedPolygons/Ch3/HyperbolicArc.lean#L772) (approved by the user) |
| The converse of Problem 3.6.2 (an admissible trajectory bounds a balanced disk whose area is its cost), used in §6.1 (TeX 4579) | the curve `g s₀*` winds once around the origin ([`IsWindingOne`](../../SmoothedPolygons/Ch6/Winding.lean#L82)), as it does when the cost is below `7π/2` | the unit circle traversed seven times: `X ≡ J`, `u ≡ (1/3, 1/3, 1/3)`, `t_f = 7π/3`, cost `7π` (E15) | hypothesis `hw` of [`exists_isBalancedPair_of_isReinhardtAdmissible`](../../SmoothedPolygons/Ch6/AdmissibleDisk.lean#L937) |
| Lemma 4.2.3 | `X ≠ 0` | `X = 0`: `T_0 O_0 = 0` but `𝔰𝔩₂/ℝ·0` has dimension 3 | hypothesis of [`lemma4_2_3`](../../SmoothedPolygons/Ch4/AdjointOrbit.lean#L432) |
| Theorem 6.1.1 (Filippov), "an optimal control exists" | the velocity sets extended by the cost, `{(f(q, u), φ(q, u)) \| u ∈ U}`, are convex (the book's hypothesis when `φ` does not depend on `u`) | on `ℝ`, `q' = uψ(q)`, `U = [-1, 1]`, a bump `ψ` with `ψ = 1` on `[-1, 1]`: `∫₀¹ (q² + 1 - u²) dt` from `q(0) = 0` to `q(1) = 0` has infimum `0` and no minimizer (E35) | hypothesis of the second part of [`External.filippov`](../../External/Filippov.lean#L153) (approved by the user) |
| Lemma 7.3.1 | `⟨X, Z_u⟩ ≠ 0` on `U` (used by the proof, TeX 5792) | a segment `U` of the plane `u₀ + u₁ + u₂ = 1` crossing the line where `⟨X, Z_u⟩ = 0`: the Hamiltonian is undefined there | hypothesis `hden` of [`lemma7_3_1`](../../SmoothedPolygons/Ch7/Faces.lean#L49) |
| Lemma 8.2.1 | `⟨X, Z_u⟩ ≠ 0` for every `u ∈ U_T` (true on the state space, Lemma 3.3.4) | `X = 0`, or any `X` with `⟨X, Z_u⟩ = 0` for some `u ∈ U_T`: the control-dependent term `H₂` is undefined there (E52) | hypothesis `hden` of [`lemma8_2_1`](../../SmoothedPolygons/Ch8/SingularLocus.lean#L586) |
| Theorem 8.3.2 as restated in Chapter 1 (TeX 851–856) | the trajectory is edge extremal, as in Chapter 8 | an abnormal extremal of Remark 8.1.6 (with the signs of E51) whose control is the midpoint of an edge: it never meets `𝒮_sing` and is not bang-bang (E57) | hypothesis `hedge` of [`theorem8_3_2`](../../SmoothedPolygons/Ch8/FiniteBangBang.lean#L1419), the statement of Chapter 8 |

## Redundant hypotheses

Each hypothesis in the table is omitted from the Lean statement, which is therefore more general
than the book's. The Challenge statements keep the book's hypotheses.

| Result | Hypothesis that is not needed | Why |
| --- | --- | --- |
| Theorem 3.1.4, parts (1), (2) ([`theorem3_1_4`](../../SmoothedPolygons/Ch3/StateDynamics.lean#L258)) | `K` a convex disk, `σ` regular, `σ` parameterizes `∂K` | the proof differentiates `σ_j = g s_j` and uses `det g = 1`; it holds for every `C¹` multi-curve induced by a curve in `SL₂(ℝ)` |
| Proposition 3.1.9 ([`proposition3_1_9`](../../SmoothedPolygons/Ch3/StateDynamics.lean#L570)) | `σ₀` parameterized by arclength | the proof uses that the tangents are Lipschitz (Definition 2.4.7, item 2), not the normalization |
| Corollary 3.1.10 ([`corollary3_1_10`](../../SmoothedPolygons/Ch3/StateDynamics.lean#L679)) | the same (the standing assumption of TeX 2157, not printed in the statement) | it applies Proposition 3.1.9 |
| Lemma 3.3.1 ([`lemma3_3_1`](../../SmoothedPolygons/Ch3/ControlSets.lean#L205)) | `g'` Lipschitz | the hypothesis `κ_j ≥ 0` almost everywhere already presupposes that `X'` exists almost everywhere; the first proof (if `κ₀ = κ₁ = 0` then `κ₂ = √3 det X/ρ₀(X) > 0`) uses only `tr X' = 0` where `X'` exists. (The formal `κ_j` is defined everywhere, through [`derivEntrywise`](../../Basic/Analysis/Calculus/MatrixEntrywise.lean#L113).) |
| Theorem 5.0.2 ([`theorem5_0_2`](../../SmoothedPolygons/Ch5/Theorem502.lean#L253)) | `K` in circle representation, `g(0) = I₂` (the boundary trajectory of Problem 3.6.2, and the paragraph after the statement, TeX 3991–3994) | the proof re-centers `K` at the time `t₀` where the trajectory leaves `𝔥**` ([`IsBalancedPair.recenter`](../../SmoothedPolygons/Ch5/Recenter.lean#L147), E45), and the re-centered disk `g(t₀)⁻¹K` is in circle representation whatever `g(0)` is |
| Corollary 6.5.4 ([`corollary6_5_4`](../../SmoothedPolygons/Ch6/Hamiltonian.lean#L477)) | `Z = Z_u` is a control matrix | the Lean statement takes any matrix `Z` with `⟨X, Z⟩ ≠ 0`: the quotient rule does not use the form of `Z_u` |
| Theorem 6.8.2 ([`theorem6_8_2`](../../SmoothedPolygons/Ch6/HalfPlane.lean#L164)) | `Λ_R` traceless | `Λ_R` enters only through its trace form with traceless matrices |
| Lemma 7.1.2 ([`lemma7_1_2`](../../SmoothedPolygons/Ch7/ConstantControl.lean#L82)) | `u ∈ U_T` | the proof uses only that `P` is constant along the trajectory (Lemma 7.1.1), which holds for every constant `u` |
| Lemma 7.3.1 ([`lemma7_3_1`](../../SmoothedPolygons/Ch7/Faces.lean#L49)) | the control set lies in the plane `u₀ + u₁ + u₂ = 1` | `Z_u` is linear in `u`, so `H` is a linear-fractional function of `u` on any compact convex set on which `⟨X, Z_u⟩ ≠ 0` (hypothesis `hden`, E26) |
| Gruber, Cor. 30.1 ([`External.gruber_corollary_30_1`](../../External/Gruber.lean#L320), cited in Definition 2.1.2) | the translates form a packing | the lattice-point count bounds the sums of the areas of the translates meeting a disk, overlaps counted with multiplicity |

Eleven Lean statements keep hypotheses that their proofs do not use, because the book or the source
states them:

- Lemma 3.1.8 ([`lemma3_1_8`](../../SmoothedPolygons/Ch3/HyperbolicArc.lean#L772)) keeps `hcover`, that the arcs of `σ` cover `∂K` (part of "the
  boundary is parameterized by `σ`"); of that hypothesis the proof uses only `hbd`, that the curves
  lie on `∂K`.
- Proposition 6.4.1 ([`proposition6_4_1`](../../SmoothedPolygons/Ch6/LeftInvariant.lean#L91)) keeps the nondegeneracy, symmetry and invariance of the bilinear
  form: nondegeneracy is what makes `p ↦ ⟨p, ·⟩` the identification `𝔤 ≅ 𝔤*`, and the identity
  `H = ⟨p, f(e, u)⟩` holds for every bilinear form.
- Lemma 8.1.5 ([`lemma8_1_5`](../../SmoothedPolygons/Ch8/EdgeLandau.lean#L504)) keeps the hypothesis that the state stays in the state space of the
  edge problem (`y > 0`, `|x| < 1/√3`) on all of `(-t₁, t₁)`, as the book's solutions of the edge
  problem do; the proof works on a smaller interval around `0`, where continuity gives it.
- Theorem 8.3.1 ([`theorem8_3_1`](../../SmoothedPolygons/Ch8/FiniteBangBang.lean#L1288)) keeps edge extremality, which the book uses only to pass from the
  maximizers to the control through Theorem 8.1.4; the one-sided form about the maximizers does
  not need it, and the form about the control, its corollary, does (E56).
- Lemma 13.2.8 ([`lemma13_2_8`](../../SmoothedPolygons/Ch13/FirstControl.lean#L885)) keeps `z⁰ ≠ 0` and `z₃⁰ ∈ ℝ_{≤0}`: the identity
  `χ_{ζ,ζ²} + χ_{ζ²,ζ} = 0` holds for every `z⁰`, since the two cubics differ only in their `t³`
  terms, which cancel (E64).
- Lemma 13.3.1 ([`lemma13_3_1`](../../SmoothedPolygons/Ch13/SingularLocus.lean#L152)) is stated, as printed, for the constant control given by the
  maximum principle (the first control) and `z₃⁰ ∈ 𝒲`; the proof uses the wall condition but not
  that the control is the first control, and holds for every vertex control `u ∈ V_T`.
- Lemma 13.3.2 ([`lemma13_3_2`](../../SmoothedPolygons/Ch13/SingularLocus.lean#L715)) keeps "the set of controls maximizing the Hamiltonian is a face":
  the maximizers of `v ↦ H_F(z, v)`, which is affine in `v`, always form a face of `U_T`, and the
  proof uses only that they are not a single vertex.
- The continuity of the first switching time on the big open cells (§15.1,
  [`TriFuller.continuousAt_firstSwitchTime_of_ne_zero`](../../SmoothedPolygons/Ch15/Continuity.lean#L421)) keeps `res_AB ≠ 0`, one of the three loci
  off which the book claims it (TeX 12141–12142).
  - The switching time is the least time at which `χ_A < 0` or `χ_B < 0`, and a common simple root
    of `χ_{A,0}` and `χ_{B,1}` is still a sign change of one of them (E70).
- The impossibility of `(m_A, m_B) = (0, 3)` (§15.2, [`TriFuller.multB_eq_three`](../../SmoothedPolygons/Ch15/SmallerCells.lean#L569)) keeps the
  hypothesis that the point has cell coordinates, the standing assumption of §15.2 (TeX
  12214–12216): the book's argument (`m_B = 3` forces `y₁ = y₂ = 0`, hence `x₃ = 0` by (15.1.1) and
  `m_A > 0`) holds for every point.
- Corollary A.1.3 ([`corollaryA_1_3`](../../SmoothedPolygons/AppA/Gronwall.lean#L46), and its two-sided form) keeps "`n` a positive integer": the
  bound holds for `n = 0` as well (E61).
- Filippov's theorem ([`External.filippov`](../../External/Filippov.lean#L153)) keeps the source's standing assumptions that `f` is smooth
  in `q` with `∂f/∂q` jointly continuous (`hfq`, `hfq'`), which give existence and uniqueness of
  trajectories; the proof uses only the continuity of `f`, the compactness of `U`, the compact
  support of `f` and the convexity hypotheses.

The lemmas of the proof of N4 (E88), which are not results of the book, are stated without the
hypotheses that their proofs turned out not to need: for instance INV Proposition 3
([`ArcParams.Phi_nonpos`](../../SmoothedPolygons/Ch14/ArcStepRegion.lean#L361)), whose written proof assumes `f₀ ≥ 0`, needs no sign of `f₀`, since the
terms in `f₀` cancel in its identity (Section 7).
