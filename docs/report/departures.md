# Departures from the paper's proofs

Part of the [audit report](../../REPORT.md).

| Result | The paper's argument | The formalization's | Why it is necessary | E-item |
| --- | --- | --- | --- | --- |
| Lemma 2.2.1 (in its corrected form) | expand `K`, separate touching translates by lines, crop, repeat until the plane is tiled; at most six edges by Euler characteristic | a maximal centrally symmetric convex body `C ⊇ K` free of half-lattice points (Zorn; bounded by Blichfeldt) is cut out by at most three strips, whose unique support points pairwise form lattice bases ([`PlaneLattice.exists_halfLatticeFree_eq_strips`](../../Basic/Analysis/Convex/LatticePacking.lean#L998)) | the book's argument is aimed at the printed statement, which is false (E1): its termination ("the plane is tiled") and its edge count (Euler characteristic of a tiling) fail; the corrected statement needs another argument (approved by the user) | E1 |
| Lemma 2.2.5, no corners and critical edges | shave `K` near a boundary point lying on no edge of a critical hexagon; at endpoints of flat segments, "shave as above" | a worst disk is irreducible in Mahler's sense (no symmetric convex proper subdomain has the same `Δ`); by Mahler 1947, Lemma 3, which the book cites after Definition 2.3.5, its boundary points lie on critical lattices, so every support line contains a point of a critical lattice, one of the six boundary points of a configuration of Mahler's Lemma 2 ([`External.mahler_irreducible`](../../External/MahlerIrreducible/Lemma3.lean#L383)); there Mahler's Theorem 2 gives a unique support line and the edge of a least-area hexagon | the shaving argument cannot close the case of a segment endpoint on a critical edge off its midpoint (E4); the user chose Mahler's route, which rests on results the book itself cites (Mahler's Lemma 3, Theorems 2.3.6 and 2.3.7) | E4 |
| Lemma 2.4.2, one step | `σ₂` equals the integral curve `σ̃₂` with the same tangent direction and area relation | `σ₂` is differentiable because its chords lie between the tangent lines at their ends, so their directions converge, and the area relation fixes their lengths | the book does not show that `σ̃₂` stays on the boundary, which its identification needs (E8) | E8 |
| Lemma 2.4.6 | Shifrin's Proposition 3.8 (a simple closed regular curve is convex iff its curvature has one sign) | each tangent line supports `K`, so `f(t) = det(σ'(t₀), σ(t) − σ(t₀)) ≥ 0` with `f(t₀) = f'(t₀) = 0`, and the second-derivative test gives `det(σ', σ'') ≥ 0` | the cited proposition is about smooth curves; the curves here are only `C¹` with Lipschitz derivative (E11) | E11 |
| The area formula `eqn:cost` (§3.2) | Green's theorem, `area(K) = ½∮ x dy − y dx` | the polar-coordinates form of Green's formula for regions star-shaped about the origin, `area = ½∫ det(γ, γ')` ([`PlaneCurve.IsStarCurve.volume_radialHull`](../../Basic/Analysis/Convex/StarCurve.lean#L480), by the change of variables `(r, t) ↦ r γ(t)`) | Mathlib has no Green's theorem for regions bounded by `C¹` curves; only that step changes | – |
| Lemma 3.1.12 (Jacobi's formula) | verify the polynomial identity on the dense set of matrices with distinct nonzero eigenvalues, through a differentiable diagonalization `A = L⁻¹DL` | differentiate the Leibniz expansion of `det` and identify `Σᵢ det(A with column i replaced by A'ᵢ) = tr(adj(A) A')` through Cramer's rule | the step needs mathematics that Mathlib lacks (a differentiable eigen-decomposition and the density argument); the user approved the replacement | – |
| Lemma 4.3.1 | `area(K_min) < area(unit disk) = π` | `cost(K_min) ≤ cost(smoothed octagon) < π`, the octagon being admissible by Theorem 7.5.6 and its cost computed in the example of §7.5 | the paper's step has a gap that its own comparison cannot close: the unit disk is admissible, so it gives only `≤` (E19) | E19 |
| Theorem 5.0.6, the claim of Case 1 | if no point of `[r₀, r̃₀]` lies on `∂K`, then `K` lies in the centrally symmetric hexagon `r₀, r̃₀, q₁, …`, of the area of `H_K(z)`; shifting its cut edges inward until they meet `K` gives a smaller one | the line parallel to `s₀s₁` is shifted at once to the support line of `K`: if it lies strictly inside the cut, the hexagon cut at that line contains `K`, is centrally symmetric and convex, and has area `area(H_K(z)) + 2T₀^ext - 2μ²T₀ < area(H_K(z))`; otherwise the extreme point of `K` on the cut line lies on `[r̃₀, r₀]` ([`exists_mem_frontier_segment_cut`](../../SmoothedPolygons/Ch5/AreaBound.lean#L519)) | the book does not argue that `K` lies in its hexagon, nor that the hexagon is convex (E43) | E43 |
| Theorem 5.0.6, Case 2 and the area bound | Case 1 for `z ∈ h₀ ∖ (h₁ ∪ h₂)`, with `area(K) ≥ area(conv{s_j*, ±r})`; Case 2, `z ∈ h₀ ∩ h₁`, "adapted"; `h₀ ∩ h₁ ∩ h₂ = ∅` leaves no other case | the claim at each corner `i` with `z ∈ h_i` separately (the construction changes `H_K(z)` only near `p_i` and `p_{i+3}`); `area(K)` bounded below by the measure of the union of `conv{s_j*}` and the triangles `±△s_i r_i s_{i+1}`, `z ∈ h_i`, which have pairwise disjoint interiors ([`theorem5_0_6`](../../SmoothedPolygons/Ch5/AreaBound.lean#L777)) | Case 2 is only sketched (E43); the corner-by-corner argument covers it, Case 1 and `z ∉ h₀ ∪ h₁ ∪ h₂` at once, and in Case 1 the union has the area of the book's convex hull; `h₀ ∩ h₁ ∩ h₂ = ∅` is then not used | E43 |
| Lemma 5.0.7 (3) | the sum (5.0.1) is continuous and increases in `x` on `h₀ ∖ h₂` and on `h₀ ∩ h₂`, hence on `h₀ ∩ {x > 0, y ≥ √3}`; it is even, so least at `x = 0` | `{x ≥ 0, y ≥ √3} ⊆ h₀`, and there `I₀area₀ + I₂area₂ = max(area₀ + area₂, area₀)`, the maximum of the functions that (2) and (1) show increasing; even in `x` ([`lemma5_0_7_3`](../../SmoothedPolygons/Ch5/Monotonicity.lean#L541)) | the book does not show that the points with `x > 0`, `y ≥ √3` lie in `h₀`; the maximum makes its "increasing on each piece, and continuous" precise (E44) | E44 |
| §6.1, the existence of a minimizer | Filippov's theorem (Theorem 6.1.1) applied to the half-plane system (Problem 4.5.1), with the vector fields multiplied by a cut-off `ψ`, `ψ = 1` on `𝔥**`; `t_f ≤ π/3` by Lemma 4.3.1 | Filippov's theorem with the closed state constraint `z ∈ 𝔥**`, a compact set of initial points, the closed endpoint relation of Problem 3.6.2 and the window `[0, π/3]` (`ControlSystem.exists_optimal_constrained`, OptimalControl package), applied to the matrix system of §6.2 (Lemma 6.1.2 carried over by Lemma 4.5.2); `t_f < π/3` for competitors cheaper than the smoothed octagon from `cost ≥ 3t_f` ([`three_mul_le_reinhardtCost`](../../SmoothedPolygons/Ch4/TerminalTime.lean#L71)); the octagon is in the class ([`exists_isReinhardtMinimizer`](../../SmoothedPolygons/Ch6/Existence.lean#L436)) | the cut-off changes the dynamics outside `𝔥**`, so a minimizer of the cut-off problem need not be a Reinhardt trajectory; Theorem 6.1.1 fixes the initial point, while `X(0)` is free and the endpoints are coupled; Lemma 4.3.1 assumes the minimizer whose existence is proved (E46). The matrix system is the one whose admissible pairs §6.2 already identifies with the trajectories of Problem 3.6.2 | E46 |
| §6.2 and §6.6, every minimizer is a Pontryagin extremal | the maximum principle on `SL₂(ℝ) × 𝔰𝔩₂(ℝ)` with the boundary conditions `g(0) = I₂`, `g(t_f) = R`, `X(t_f) = R⁻¹X(0)R`; the Hamiltonian by Proposition 6.4.1, the costate equations by Proposition 6.5.1, the transversality conditions of §6.6 (for `Λ₁` by Corollary 6.5.3) | the same steps, with two changes. (1) The maximum principle is applied on the open set `GL₂⁺(ℝ) × C` of `Mat₂(ℝ) × 𝔰𝔩₂(ℝ)` ([`matrixDomain`](../../SmoothedPolygons/Ch6/MatrixSystem.lean#L118)), with `g(0) = I₂` and `det X(0) = 1` among the boundary conditions; this adds three steps: `det g` and `det X` are first integrals, so the competitors are Reinhardt trajectories; the adjoint equation meets the hypotheses of Proposition 6.5.1 through the momentum `p - (tr(pg)/2)g⁻¹`; and the covector `pg = kI₂` of (2). (2) The boundary condition is applied less the equations `g(t_f)₁₁ = R₁₁` and `X(t_f)₁₀ = (R⁻¹X(0)R)₁₀`, which the first integrals `det g` and `det X` make redundant ([`matrixBoundary`](../../SmoothedPolygons/Ch6/MatrixSystem.lean#L136)); transversality in the two directions this frees excludes the covectors whose reduced costate vanishes, and the nontriviality of `(λ_cost, Λ₁, Λ_R)`, which the book does not derive, is proved by Corollary 6.5.3, uniqueness for the linear `Λ_R` equation and transversality at `t_f` ([`exists_isPontryaginExtremal_of_isReinhardtMinimizer`](../../SmoothedPolygons/Ch6/MatrixExtremal.lean#L564)) | (1) the maximum principle available in Lean is stated on open subsets of a finite-dimensional space, and `SL₂(ℝ)` is not open in `Mat₂(ℝ)`; (2) with the full boundary conditions the conclusions of the maximum principle hold for every admissible trajectory with a covector whose reduced costate vanishes, so the nontriviality of `(λ_cost, Λ₁, Λ_R)` does not follow (E21) | E21 |
| Theorem 7.7.1, step 6 (the fixed points of `f⁴` near `q_oct`) | for each `d` near `d_oct`, `q_fix(d)` stays hyperbolic and the implicit function theorem inverts `f_d⁴ - I` near `q_fix(d)`; "thus, the only fixed points near `q_oct` are the fixed points `q_fix(d)`" (TeX 6612–6620) | the inverse function theorem applied once, at `q_oct`, to `Ψ = (section constraints, f⁴ - id)`, whose constraints include `d = det Λ₁`: its derivative is injective because `A⁴ - I` is invertible on the tangent space of the section (step 5), so `Ψ` is injective near `q_oct`, and a fixed point with `det Λ₁ = d` has the same image as `q_fix(y₀(d))`, with `y₀(d)` from Remark 7.5.2 as in the book ([`iso_fixedPoints`](../../SmoothedPolygons/Ch7/Isolated/FixedPoints.lean#L179)) | a separate application for each `d` gives a neighbourhood of each `q_fix(d)`, not one uniform in `d`, which the conclusion needs; the single application gives the uniformity, and the hyperbolicity of `q_fix(d)` for `d ≠ d_oct` is not needed | E32 |
| Proposition 8.1.3, edge extremality | "the globally minimizing trajectory must minimize cost among all trajectories with the same endpoint conditions on the subinterval and that have their control function similarly restricted to the edge" (TeX 6793–6797) | competitors of the edge problem uniformly close to the minimizer's edge arc are spliced into the minimizer: the middle arc rebuilt from `(x, y, s)` by (8.1.1), the rest of the minimizer shifted in time, the costs compared by the cost identity of §8.1; the edge arc is then a strong local minimizer of the edge problem, to which the maximum principle applies ([`proposition8_1_3`](../../SmoothedPolygons/Ch8/EdgeExtremal.lean#L850)) | the state space of the edge problem is larger than the star domain, so a competitor far from the arc may give no Reinhardt trajectory, and the book gives no construction (E48) | E48 |
| Theorem 8.1.4, two steps | "The function `λ₂'` is also continuous" (TeX 6846–6852); Lemma 8.1.5 applied at every zero of `λ₂` with `λ₂' = 0` (TeX 6884–6886) | the derivative of `λ₂` is proved to exist at each zero of `λ₂`, equal there to the right-hand side of (8.1.7), and only that is used; at a zero at an end of the interval, the state and the costate are continued beyond it with the control `u_e = 0`, where they are explicit, before Lemma 8.1.5 is applied ([`theorem8_1_4`](../../SmoothedPolygons/Ch8/EdgeBangBang.lean#L823)) | `λ₂'` is continuous only after a change of the control on a null set; Lemma 8.1.5 needs a solution on both sides of the zero (E49) | E49 |
| Theorem 8.2.7 | Theorem 8.2.6 makes a singular subarc a circular arc, which the second variation excludes | the authors' reading (the user's decision): on an interval with the control in an edge, the costates of the edge arc (Proposition 8.1.3) have no singular subarc of the edge problem, by the argument of Theorem 8.1.4; elsewhere a localization by Lemma 8.2.1 leaves the subarcs with `Λ_R ≡ 0`, which the book's argument excludes (Theorems 8.2.6 and 8.2.3 and the second variation) ([`theorem8_2_7`](../../SmoothedPolygons/Ch8/NoSingularArcs.lean#L375)); for normal lifts the printed statement, through the pull-back of the costate to the edge ([`not_isSingularSubarc_of_isReinhardtMinimizer_of_isNormalExtremal`](../../SmoothedPolygons/Ch8/NoSingularArcs.lean#L418)) | the book's proof covers only the subarcs on which the Hamiltonian does not depend on the control (E55) | E55 |
| Theorem 8.3.1 (in its one-sided form) | in the contrapositive: if the maximizers are not confined to one edge near `t₀`, claims (a)–(c) put the lift in `𝒮_sing` at `t₀`; claim (a) passes to the control through Theorem 8.1.4 | claims (a)–(c) run directly, on each side of `t₀` separately, and give an edge containing the maximizers on each side ([`theorem8_3_1`](../../SmoothedPolygons/Ch8/FiniteBangBang.lean#L1288)); the passage to the control, with edge extremality and Theorem 8.1.4, is the corollary that the proof of Theorem 8.3.2 quotes ([`IsExtremalOn.exists_ae_mem_controlEdge_of_isEdgeExtremalOn`](../../SmoothedPolygons/Ch8/FiniteBangBang.lean#L1349)); at an end of the interval the Gronwall step uses the functions extended by their values there | the printed statement is false, and the form the user chose needs no passage to the control (E56) | E56 |
| Lemma 13.2.5, and the descent of the Poincaré map to `Ξ_𝒲/V_T` and `F_ang` (§13.5) | "The lemma follows from the time-reversal symmetry (Lemma 13.2.3)" (TeX 10905–10906); `F` descends "by the equivariance of the construction" and "by the scaling symmetries" (TeX 11246–11260), that is, by Lemmas 13.2.1 and 13.2.2 | the substitutions behind Lemmas 13.2.1–13.2.3 redone for constant controls at every `z⁰` ([`TriFuller.tau_flow_neg`](../../SmoothedPolygons/Ch13/Symmetry.lean#L172), [`TriFuller.ham_tau`](../../SmoothedPolygons/Ch13/Symmetry.lean#L192), [`TriFuller.poincare_smul`](../../SmoothedPolygons/Ch13/PoincareMap.lean#L281), [`TriFuller.poincare_scale`](../../SmoothedPolygons/Ch13/PoincareMap.lean#L315); [`lemma13_2_5`](../../SmoothedPolygons/Ch13/FirstControl.lean#L918)) | Lemmas 13.2.1–13.2.3 are about solutions with `H_F = 0`, which need not hold at `z⁰` (E63) | E63 |
| Lemma 13.2.6 | a necessary condition: the first control, if it exists, maximizes the lexicographic order, and in a tie `{ζ^i, ζ^{i+1}}` it is not `ζ^{i+1}`, by contradiction from the sign of the cubic term (TeX 10978–11008) | the sufficient direction, which the statement asserts: the lexicographic maximizer, with the tie rule, is optimal along its own trajectory on some `[0, ε]`, by the same Taylor expansion and the same cubic coefficient; the necessary direction is [`TriFuller.firstControl_mem_lexMaxControls`](../../SmoothedPolygons/Ch13/FirstControl.lean#L636), and the uniqueness of the first control is proved generically ([`TriFuller.IsFirstControl.unique`](../../SmoothedPolygons/Ch13/FirstControl.lean#L330); [`lemma13_2_6`](../../SmoothedPolygons/Ch13/FirstControl.lean#L539)) | the first control is the control that is optimal on some `[0, ε]`, and the book never shows that the maximizer is (E62) | E62 |
| Lemma 13.3.2 | two cases, each on all of `[0, t₂]`: the Hamiltonian independent of the control in `U_T` (then `z ≡ 0`), or in the edge `[ζ, ζ²]` (then `0 = RR(z₃(t), ζ - ζ²) = (√3/2)t³/3! + (quadratic in t)`, absurd) | the maximizers are not a vertex, so `z₃(t) ∈ 𝒲` for every `t`; if `z₃(t₀) ≠ 0`, `z₃` stays on one open ray `ℝ_{<0}c` of `𝒲` on an interval around `t₀`, where the book's second case runs with `RR(z₃, ic)` in place of `RR(z₃, ζ - ζ²)` (for `c = 1`, the book's quantity divided by `√3`) and gives a contradiction; so `z₃ ≡ 0`, and the book's first case applies ([`lemma13_3_2`](../../SmoothedPolygons/Ch13/SingularLocus.lean#L715)) | the hypothesis lets the maximizing face change with `t`, which the book's two cases do not cover (E65) | E65 |
| Lemma 13.5.2, step 3 (the three cases `(r, ζ₁)`) | "at times `t = 0, t_sw` we must have by the maximum principle" a chain of inequalities ending in `z₃⁰ūζ₁² ∈ ℝ_{≤0}`, from which the three cases are asserted (TeX 11361–11380) | the maximum condition at `t = t_sw` for the outgoing control `u` and the incoming control `ζ₁u`, which by (13.5.2) and the equivariance of `F` is the book's condition at `t = 0`; `ζ₁ = 1` excluded, since the control switches at `t_sw` while the first control of `F(z⁰)` is `ζ₁u`; the three cases derived from the wall condition by identities in `ℤ[r, ζ]`: the imaginary part gives `(r - 1)P(r) = 0`, and the real part a sign through `Q₆ = P + 4r⁵ + 6r⁴ + 4r³ + 6r² + 4r` ([`lemma13_5_2`](../../SmoothedPolygons/Ch13/FixedPointsClassification.lean#L572)) | the book's display is garbled, its final condition follows only when `ζ₁ ≠ 1`, which the book does not exclude, and the passage to the three cases is asserted (E67) | E67 |
| Lemma 13.5.2, the solutions as fixed points (step 5 and the verification of (13.5.1)) | "The coordinates in the statement of the lemma have been rotated by `V_T`, choosing the first control `u = ζ₁²`, to make the third coordinate real and negative" (TeX 11384–11386); (13.5.1) is not derived, and that it gives fixed points with `H_F = 0` is not checked | the representative of `q_out` satisfies the fixed-point equation, so by step 2 it is the candidate for its own first control and switching time, and the candidates, homogeneous in `(u, t_sw)`, agree up to the virial group; its first control `ζ` is shown from the definition (`ζ` is optimal on `[0, t_sw]`) and uniqueness; `t_sw` is the first switch because the switching function to `ζ²` is `√3t(Im z₂⁰ + Im z₁⁰t/2 + t²/12)`, with positive coefficients, and the one to `1` has the signs `+ + + −` and vanishes at `t_sw`; and `H_F = (r² + r + 1)P(r)/(9(r + 1)²(1 + r³ + r⁶))` along (13.5.1), all exact in `ℚ(√3)(r)` modulo `P` ([`TriFuller.poincare_qOutCart`](../../SmoothedPolygons/Ch13/FixedPoints.lean#L483), [`TriFuller.firstSwitchTime_qOutCart`](../../SmoothedPolygons/Ch13/FixedPoints.lean#L462), [`TriFuller.hamMax_qOutCart`](../../SmoothedPolygons/Ch13/FixedPoints.lean#L492)) | (13.5.1) is computer-generated in the book, and the facts that make its solutions fixed points of `F` with `H_F = 0` are not shown (E67) | E67 |
| Lemma 13.5.5 | time reversal for `q_in`; for `q_out`, "An explicit calculation of the eigenvalues of the Jacobian matrix in terms of local coordinates centered at `q_out` gives the result. Numerically, the three eigenvalues have absolute value less than `0.1`. The calculations were made in Mathematica" (TeX 11443–11453) | the same three steps, certified: the chart `Re z₁ = -1`, `z₃ ∈ ℝ_{<0}`, `H_F = 0`, with coordinates `(Im z₁, Re z₂, Im z₂)` ([`TriFuller.exists_chart`](../../SmoothedPolygons/Ch13/Jacobian.lean#L1638)); the map in the chart, smooth near `q_out` by the implicit function theorem (`t_sw` is a simple root there); its Jacobian, exact in `ℚ(√3, r_scale)` ([`TriFuller.jacobianOut`](../../SmoothedPolygons/Ch13/Jacobian.lean#L136)); sign changes of the characteristic polynomial at rational points, which put the three eigenvalues in `(-1/10, 1/10)` ([`TriFuller.norm_lt_of_aeval_charpoly_jacobianOut_eq_zero`](../../SmoothedPolygons/Ch13/Jacobian.lean#L1919)); linearized stability for maps ([`Function.isAsymptoticallyStable_of_hasFDerivAt`](../../Basic/Dynamics/LinearizedStability.lean#L73)); and time reversal: `τ ∘ F_ang` is an involution near `q_out` and `q_in`, which carries asymptotic stability to instability ([`Function.IsAsymptoticallyStable.isUnstable_of_involutive`](../../Basic/Dynamics/Stability.lean#L130); [`lemma13_5_5`](../../SmoothedPolygons/Ch13/Stability.lean#L281)) | the book's proof is a numerical computation with no chart, matrix or values; it does not argue that `F_ang` is `C¹` near `q_out` or that `τ ∘ F_ang` is an involution there; and Mathlib has no stability theorem for maps (E68) | E68 |
| §14.2 and Lemma 14.3.1, the first control near the singular locus | "the first control … is `u = e₂` for all sufficiently small `r > 0`, provided … `ℓ̃₁₁ + ℓ̃₂₁x̃₂₁ < 0` and `ℓ̃₂₁ < 0`", asserted (TeX 11710–11717), and used in the proof of Lemma 14.3.1 for every extremal through a chart point ("These functions give the value of the Reinhardt-Poincaré map", TeX 11835–11836) | proved from the two signs that the book names: on the section `H(e₁) = 6h/(3 + 3a² - c²)` with `h = r³G`, `G(0, x̃) = 2(ℓ̃₁₁ + ℓ̃₂₁x̃₂₁) < 0`, and the slope of `χ₃₂` along the fields of `e₂` and `e₃` is `4√3r²(crG + ℓ̃₂₁)/(c² - 3r²) < 0`; so an extremal through a chart point near `(0, x̃_out)` leaves it with `e₂` and switches next where the `e₂`-flow does ([`eventually_firstControl_lieChart`](../../SmoothedPolygons/Ch14/Asymptotics.lean#L615), [`eventually_switchStructure`](../../SmoothedPolygons/Ch16/SwitchStructure.lean#L389), [`IsChatteringArcInto.next_switchPoint_eq_reinPoincare`](../../SmoothedPolygons/Ch16/NextSwitch.lean#L388)) | the book states the claim without proof (E83) | E83 |
| Lemmas 14.2.3–14.2.4 | "Use the explicit solutions on both sides and expand as a series in the parameter `r₀`", in Mathematica (`MCA:2446603`; TeX 11737–11758) | a comparison of differential equations: the leading part of the extremal equations along `e₂`, with the weights `(r₀, r₀², r₀³)`, has a matrix polynomial solution, which in Cayley coordinates is the Fuller flow with control `ζ`, and three Grönwall steps bound the errors by `O(r₀²)`, `O(r₀³)`, `O(r₀⁴)` uniformly for `\|t\| ≤ Sr₀`, for every pair of switching functions ([`chartFlow_estimates`](../../SmoothedPolygons/Ch14/ChartFlow.lean#L777); [`lemma14_2_3`](../../SmoothedPolygons/Ch14/Asymptotics.lean#L733), [`lemma14_2_4`](../../SmoothedPolygons/Ch14/Asymptotics.lean#L744), [`lemma14_2_4_chi23`](../../SmoothedPolygons/Ch14/Asymptotics.lean#L756)); the closed forms of the chart are used as in the book | the book's proof is a sketch resting on a computer-algebra expansion, and expanding the quadratures of the closed-form flow to order `r₀⁴` with a uniform remainder is heavy in Lean; the comparison gives the same leading terms with a remainder bound (E84) | E84 |
| Lemma 14.3.1, Step 2 (the analyticity of the flow) | the constant-control solutions "are given by matrix exponentials and are hence analytic in time `t` and initial conditions" (TeX 11793–11797) | `X(t)` and `Λ₁(t)` are products of matrix exponentials; `Λ_R(t)`, whose closed form in Chapter 7 has quadratures, is `exp(t L(X₀, P))` applied to the initial value, for a linear equation in the frame that rotates with `e^{tP}`; then the analyticity of the exponential ([`entrywiseAnalyticAt_vertexFlow`](../../SmoothedPolygons/Ch14/VertexFlowAnalytic.lean#L332)) | Chapter 7's closed form for `Λ_R` uses quadratures, and Mathlib has no analyticity of integrals depending on a parameter; the rotating frame makes the book's sentence literally true | – |
| Theorem 14.3.3, the local stable manifold | "In a neighborhood of the fixed point, the local stable manifold coincides with the three-dimensional exceptional divisor", not argued (TeX 11894–11895, 11905–11919) | directly, without the stable manifold theorem: near the fixed point `\|F₁(r, x̃)\| ≥ \|r\|` (mean value theorem, with `∂_r F₁ > 1` and `F₁(0, ·) = 0`), so no orbit with `r ≠ 0` tends to the fixed point, and the divisor has an open neighbourhood of `x̃_out` that is forward invariant and attracted to it (linearized stability) ([`theorem14_3_3`](../../SmoothedPolygons/Ch14/FixedPointManifolds.lean#L694)) | the book does not argue the claim; the stable manifold theorem would need the same two facts (E86) | E86 |
| N4, [`UnstableCurveLeavesStarDomain`](../../SmoothedPolygons/Ch14/UnstableCurve.lean#L174) (the fact of Figure 14.2 that the proof of Theorem 14.4.1 uses) | the global unstable curve computed in Mathematica, and the cyclic switching and the exit read off it (TeX 11951–11991) | without locating the curve ([`unstableCurveLeavesStarDomain`](../../SmoothedPolygons/Ch14/ArcRegionInvariant.lean#L338)), in the numbering of [`SmoothedPolygons/Ch14/ArcRegionInvariant.lean`](../../SmoothedPolygons/Ch14/ArcRegionInvariant.lean): (1) the `e₂`-arc in closed form: `ρ₁ = ε` is constant, `ρ₂(t) = ε(Ye^{-t/ε} - 1)`, the exit time is `T = ε log Y`, through `ρ₂ = 0` (Proposition 1.1), and each cleared switching numerator is an exponential sum with four terms (Theorem 1.3); (2) the Reinhardt–Poincaré map as an explicit map of four parameters `(ε, Y, f₀, p)`, with `q` on a quadric `R = 0` and `q_new = Φ(s)/(Y - s)²` in closed form (Theorem 2.1, INV Theorem 1), and the radii telescoping, `r_{n+1} = (ρ₁(q_n) - ρ₁(q_{n+1}))/2` (Corollary 2.4); (3) an explicit region `𝒢*` (`r > 0`, `f₀ > 0`, `q ≤ 0`, `p > 0`, `(Y - 1)(Y′ - 2) ≤ Y - 2`) that contains every chart point near `(0, x̃_out)` with `r > 0` (Lemma 5.1) and from which one step either stays in `𝒢*` or lands on a point whose arc leaves the star domain ((INV), INV Theorem 2: a dichotomy by the sign of a cubic `ψ(s)` at the image, the relation `R = 0` written as a sum of nonnegative terms, three Bernstein certificates and inequalities for `log`); so every orbit in `𝒢*` leaves the star domain (Theorem 5.2). The certificates found by computer, checked by `ring`, `linarith` and `positivity`: a degree-6 Bernstein expansion on a triangle (26 nonnegative rationals, INV Proposition 3), two in the exit criterion (42 and 80 coefficients, INV Proposition 5), the cofactors of `√3² = 3` in the relation (dozens of monomials) and in the normal form (15 terms), and a few of at most five terms | the user's decision: the book's fact is a computation, which its authors did not certify (E88) | E88, E93, E94 |
| §15.3, the involution `𝔦 = τF` | "Since `F⁻¹ = τ∘F∘τ` and `τ = τ⁻¹`, it follows that `𝔦 := τ∘F` is an involution", on the closed big cells (TeX 12324–12328) | `F(τF(z)) = τ(z)` exactly at the switching points ([`TriFuller.poincare_tau_poincare_eq_tau_iff`](../../SmoothedPolygons/Ch15/Involution.lean#L237)), where `𝔦` is an involution ([`TriFuller.involution_involution`](../../SmoothedPolygons/Ch15/Involution.lean#L406)), and branch-wise for the root-based maps ([`TriFuller.tau_flow_tau_flow`](../../SmoothedPolygons/Ch15/Involution.lean#L250)); the later proofs apply it only at images `F(y)`, which are switching points | the identity fails at the points of the top faces, which are not switching points (E73) | E73 |
| §15.3, the map `F_A` on `𝒞₂^A` | "The first switching time is a root of `χ_{A,0}`" on `𝒞₂^A = {Δ_{A,0} ≥ 0}`, and `F_A` its continuous extension (TeX 12413–12422) | `F_A` is the root-based map at the least positive root of `χ_{A,0}` ([`TriFuller.cellMapA`](../../SmoothedPolygons/Ch15/SmallerCells.lean#L465)); the Poincaré map is `F_A` on `{Δ_{A,0} > 0}` and `F_B` on `{Δ_{A,0} ≤ 0}` ([`TriFuller.firstSwitchTime_topFaceTwo`](../../SmoothedPolygons/Ch15/SmallerCells.lean#L1096)), with `t₁ ≤ t_B` proved ([`TriFuller.leastPosRoot_chiA_le_of_mem_topFaceTwo`](../../SmoothedPolygons/Ch15/SmallerCells.lean#L1201)); `∂_{A,ζ²}` is defined with `F_A` | at `Δ_{A,0} = 0` the root is double, a tangency at which the dynamics does not switch (E74) | E74 |
| Remark 15.3.1 | the coordinates of `q_out`, printed as those of `q_in`, and the segment through them (TeX 12445–12461) | the labels swapped back: `q_out` at the printed coordinates, with `r₂ = 2 - √3`, and `q_in = τ(q_out)`; the crossings of `∂_B` and `∂_A` certified along the segment through `q_in`, in exact rational arithmetic ([`remark15_3_1`](../../SmoothedPolygons/Ch15/FixedPointCells.lean#L287), [`remark15_3_1_segment`](../../SmoothedPolygons/Ch15/FixedPointCells.lean#L791)) | the printed labels are swapped, and along the segment through the printed point the remark's crossings do not occur (E75) | E75 |
| Proposition 15.3.2, the second clause (`𝒟₂` and `𝒟₃` geometrically partition the second big cell) | read off Figure 15.3 (TeX 12392–12409) | an exact deformation ([`TriFuller.isGeometricPartition_closedBoxTwo`](../../SmoothedPolygons/Ch15/PartitionCellTwo.lean#L570)): moving `z₁` by a real `ε` and restoring `H_F = 0` keeps the root at which `ζ` takes over and changes the gain of `1` over `ζ²` by `-3ε(t²/4 - y₂)`, of one sign at every `t` since `y₂ < 0`, so each part is the closure of an open set and their interiors are disjoint | the user's decision; the rest of the proposition is not proved, and no result uses it (E72) | E72 |
| Theorem 16.1.1, Table 16.1 | containments between the parts `𝒟₀, …, 𝒟₄` of Proposition 15.3.2 and the boxes, by the boundary method from Mathematica images of faces, some rows derived with `𝔦` from facts read off Figures 15.2–15.3 (TeX 12541–12726) | three named facts about the Poincaré map on whole boxes and on the second cell, which merge the rows `𝒟_out`, `𝒟₂`, `𝒟₃`, `𝒟₄`, the subclaims and `F²𝒟₃ ⊂ 𝒟₀₀` ([`TriFuller.DOutContracts`](../../SmoothedPolygons/Ch16/BasinHypotheses.lean#L236), [`TriFuller.CellTwoEntersDOut`](../../SmoothedPolygons/Ch16/BasinHypotheses.lean#L260), [`TriFuller.BoxSubclaims`](../../SmoothedPolygons/Ch16/BasinHypotheses.lean#L278)): three named facts, proved without computer assistance (the next three rows) | the boundary method needs injectivity, invariance of domain and the images of the curved faces, none of which the book establishes, and the curved parts rest on Proposition 15.3.2, read off figures; whole boxes avoid both (E77) | E77 |
| [`TriFuller.DOutContracts`](../../SmoothedPolygons/Ch16/BasinHypotheses.lean#L236) (the row `𝒟_out` of Table 16.1, with the contraction of E78) | `F₁(𝒟_out) ⊂ 𝒟_out` by the boundary method from a Mathematica image of the faces (Figure 16.1), and "the forward iterates `F₁^k(𝒟_out)` quickly shrink toward `q_out`", read off it (TeX 12592–12598) | analytically ([`TriFuller.dOutContracts`](../../SmoothedPolygons/Ch16/DOutContraction.lean#L912)): at a point of `𝒟₀₀` the first switch is at the unique positive root `τ` of a switching function `D` (by the intermediate value theorem), and two identities that hold at `D = 0`, `C₂ = -2 Im z₂(τ)` and one for `√3C₁ + 10D`, have right-hand sides of fixed sign on `𝒟₀₀`, which gives `F(𝒟₀₀) ⊆ 𝒟₀₀` ([`TriFuller.DOutAnalytic.mapsTo_boxSet_zero_zero`](../../SmoothedPolygons/Ch16/DOutInvariant.lean#L309)); two more put `F(𝒟₀₀)` in a region `D₁` ([`TriFuller.DOutAnalytic.image_mem_regionD1`](../../SmoothedPolygons/Ch16/DOutImages.lean#L192)); in rescaled variables in which the image is affine, polynomial inequalities on a polytope put `F(D₁)` in the box `B ≈ [0.22, 0.30] × [0.080, 0.199] × [2.688, 3.009]` ([`TriFuller.DOutAnalytic.image_mem_box`](../../SmoothedPolygons/Ch16/DOutImages.lean#L617); two of them with 17 products of the constraints, chosen by a linear program, as hints for `nlinarith`); and `F` is `3/4`-Lipschitz on `B` by the mean value inequality through the implicit root, with the partial derivatives bounded by an one-page argument written out by hand on the single box `B × [0.185, 0.221]` ([`SmoothedPolygons/Ch16/DOutDerivativeBounds.lean`](../../SmoothedPolygons/Ch16/DOutDerivativeBounds.lean)): ranges of a few quantities from products of two intervals, then the logarithmic derivatives of `w₁/τ` and `w₂/τ²` (whose imaginary and real parts are the derivatives of `θ₂'`, `ψ'` and `log H(r₂')`) bounded by `(\|dv\| + (M/m)\|du\|)/m`, with row sums 0.594, 0.699, 0.699 ([`TriFuller.DOutAnalytic.lipschitzOnWith_gmap`](../../SmoothedPolygons/Ch16/DOutContraction.lean#L840)); `N = 2` | the user's decision: the book's containment is a computation, and the contraction is not in the book (E78); no step enumerates boxes | E77, E78 |
| [`TriFuller.CellTwoEntersDOut`](../../SmoothedPolygons/Ch16/BasinHypotheses.lean#L260) (the rows `𝒟₂` and `𝒟₃` of Table 16.1 and `F²𝒟₃ ⊂ 𝒟₀₀`) | the rows from the involution, with facts read off Figure 15.3, and `F²𝒟₃ ⊂ 𝒟₀₀` from a plot of sampled images (Figure 16.2; TeX 12614–12665) | analytically ([`TriFuller.cellTwoEntersDOut`](../../SmoothedPolygons/Ch16/CellTwoEntersDOut.lean#L456)), without the parts `𝒟₂`, `𝒟₃` and the involution: along the first control `ζ²` the switch to `ζ` is at the positive root `T` of `t q(t)`, `q` a convex quadratic; if the switching function `A` to `1` stays `≤ 0` on `(0, T)` (the book's `𝒟₃`), the image lies in the region `0 < θ₁ < θ₂ ≤ π`, which `F` maps into `𝒟₀₀` ([`TriFuller.CellTwoAnalytic.poincareAngZero_mem_of_regionR0`](../../SmoothedPolygons/Ch16/CellOneToDOut.lean#L219)): two steps; otherwise (`𝒟₂`) the switch is to `1`, and the image has `θ₂ = π` or lies in the second cell with `θ₂ ≤ -π/2`, where the first case applies: three steps. Each step is an exact identity (`linear_combination`, with cofactors found by computer algebra) and signs; the bounds used are weaker than the book's (`θ₂ > -π/2` on the book's `𝒟₂` instead of `θ₂ ∈ [-π/3, 0]`, and image angles `θ₂′ ≤ -π/2` instead of `≤ -2π/3`) | the user's decision: the book's step is a plot; and the rows from the involution rest on Proposition 15.3.2 (E72) and on `F⁻¹ = τFτ`, which holds only at switching points (E73) | E77 |
| [`TriFuller.BoxSubclaims`](../../SmoothedPolygons/Ch16/BasinHypotheses.lean#L278) (the subclaims and the row `𝒟₄`) | the boundary method, with convex hulls of planar projections of sampled images (Figures 16.3–16.4; TeX 12680–12726) | analytically ([`TriFuller.boxSubclaims`](../../SmoothedPolygons/Ch16/BoxSubclaims.lean#L526)): face points whose first control is not `ζ` are classes of points of `𝒟₀₀`, which `F` maps into `𝒟₀₀`; elsewhere the switch to `1` is at the unique positive root of `D`, and either `Im z₃` turns negative first, and the image lies in the second cell, or the image has explicit cell coordinates; then, for each box, one identity at `D = 0` (with a multiplier that depends on `τ` for `𝒟₁₀` and `𝒟₂₀`) gives `ψ′ < π/3` or the bound on `θ₂′` that the target needs, and `𝒟₂₁` needs none (`Im w₁ > 0` gives `ψ′ < θ₂′`); the cofactors were found by computer algebra | the user's decision: the book reads the subclaims off plots, by a method whose hypotheses it does not establish (E77) | E77 |
| Theorem 16.1.1, steps (a) and (d) | `F₁(𝒟_out) ⊂ 𝒟_out` and the local stability of `q_out` (Lemma 13.5.5) give the convergence in `𝒟_out`, and by time reversal the exit from `𝒟_in` (TeX 12592–12598, 12728–12743) | an iterate `F^N` maps `𝒟₀₀` into a box `B` on which `F` is a contraction in coordinates (part of [`TriFuller.DOutContracts`](../../SmoothedPolygons/Ch16/BasinHypotheses.lean#L236)), so Banach's fixed point theorem gives the convergence, and every backward orbit in `𝒟₀₀` is constant at `q_out`; if the iterates of `q` stay in `𝒟₂₂`, the points `τF^{j+1}(q)` form such a backward orbit, so `F(q) = q_in`, and `F⁻¹(q_in) = {q_in}` ([`TriFuller.poincareAngZero_eq_qIn0_iff`](../../SmoothedPolygons/Ch16/GlobalBasin.lean#L305)) gives `q = q_in` | containment and local stability give neither the convergence of every orbit in `𝒟_out` nor `⋂_k F^k(𝒟_out) = {q_out}`, and `F⁻¹ = τFτ` fails at points that are not switching points (E78, E73) | E78 |
| Theorem 16.1.1, the last row and step (b) | the last row of Table 16.1 by exclusion, from `𝒟₀ ⊂ 𝒟_in`, `𝒟₄ ⊂ F(𝒟₂₂)` and `F(q₁) ∉ F(𝒟₂₂)`; then the triangular structure keeps the orbit out of `𝒟_in` (TeX 12668–12676, 12733–12737) | the subclaims on whole boxes, with the target "the second big cell or a smaller box" ([`TriFuller.BoxSubclaims`](../../SmoothedPolygons/Ch16/BasinHypotheses.lean#L278)), a descent on the box indices, and no re-entry into `𝒟₂₂`: for a switching point `x`, `F(x) ∈ 𝒟₂₂` implies `x ∈ 𝒟₂₂`, by `τ(𝒟₂₂) = 𝒟₀₀`, `F(τF(x)) = τ(x)` and `F(𝒟₀₀) ⊆ 𝒟₀₀` ([`theorem16_1_1`](../../SmoothedPolygons/Ch16/GlobalBasin.lean#L599)) | `𝒟₀ ⊂ 𝒟_in` cannot hold, `F(q₁) ∉ F(𝒟₂₂)` needs an injectivity that fails off the switching points, and the closed boxes share faces with `𝒟₂₂` (E79) | E79 |
| Theorem 16.2.1 | the iterates of a switching point `q ≠ q_in` approach the outward spiral, which moves away from the singular locus "because of the scaling factor `r_scale > 1`" (TeX 12768–12777) | the same argument, with `H_F⁺ = 0` along a trajectory tending to `0` derived by invariance and continuity, and the factor by which one step multiplies the weighted norm, continuous at `q_out` with value `r_scale`, proved in the chart of Lemma 13.5.5 rather than in the cell coordinates ([`TriFuller.continuousAt_radialFactor_qOut0`](../../SmoothedPolygons/Ch16/OutwardFuller.lean#L404), [`theorem16_2_1`](../../SmoothedPolygons/Ch16/OutwardFuller.lean#L567)) | the book does not argue the continuity of the radial factor or the vanishing of the Hamiltonian (E80); the chart of Lemma 13.5.5, in which `F_ang` is `C¹` near `q_out`, gives the continuity at once | E80 |
| Theorem 16.3.1, the last step | after Theorems 8.2.7 and 8.3.2 and Lemma 8.3.4, "the proof then reduces to" switching points accumulating at the singular locus, which the blow-up, Theorems 16.4.1 and 14.4.1 and periodicity exclude (TeX 12820–12833) | the set of meeting times is handled (empty interior, a meeting at `0` moved to `T`, the first meeting time `d` after a time off the set); switching times accumulating at `d` are excluded by the hypothesis [`NoChatteringIntoSingularLocus`](../../SmoothedPolygons/Ch16/MahlerFirst.lean#L110), and a vertex control just before `d` by Lemma 8.3.4 ([`theorem16_3_1`](../../SmoothedPolygons/Ch16/MahlerFirst.lean#L349)); the hypothesis is derived along the book's lines from Theorems 16.4.1 and 14.4.1, both proved ([`noChatteringIntoSingularLocus`](../../SmoothedPolygons/Ch16/MahlerFirstArcRegion.lean#L59), [`noChatteringIntoSingularLocus_of_theorem14_4_1`](../../SmoothedPolygons/Ch16/NoChattering.lean#L376), [`theorem16_3_1_of_theorem14_4_1`](../../SmoothedPolygons/Ch16/NoChattering.lean#L387); E89) | the book does not handle the set of meeting times (E60) and compresses the contradiction (E89) | E60, E89 |
| Theorem 16.4.1, §16.4.2 and steps (d)–(f) | the Reinhardt cells `𝒞_k^R`, parts `𝒟_i^R` and continuous branch maps `F_i` near the divisor, from Weierstrass preparation (asserted, TeX 12887–12987), and the descent of Table 16.1 through them to a cluster point in `𝒟_out^R`, whose existence makes `q_out` a cluster point (TeX 13028–13055) | the one property that the descent serves: the cluster set `Ω` of the switching points is mapped into itself by the Fuller–Poincaré map `F_ang` ([`clusterSetForwardInvariant`](../../SmoothedPolygons/Ch16/ReinhardtShadowing.lean#L802)), from the uniform convergence of the rescaled Reinhardt vector field and Hamiltonians on `U_T` ([`tendstoUniformlyOn_rescaledField`](../../SmoothedPolygons/Ch16/RescaledDynamics.lean#L529), [`tendstoUniformlyOn_rescaledHam`](../../SmoothedPolygons/Ch16/RescaledDynamics.lean#L539)) and relaxed limits of the rescaled controls ([`exists_tendsto_rescaledArc`](../../SmoothedPolygons/Ch16/RescaledLimits.lean#L1302), [`TriFuller.eq_flow_of_maxCondition_UT`](../../SmoothedPolygons/Ch16/RelaxedFuller.lean#L291), [`TriFuller.firstControl_beaten_UT`](../../SmoothedPolygons/Ch16/RelaxedFuller.lean#L355)); then, as in the book's last paragraph, Theorem 16.1.1 at a cluster point `ω ≠ q_in` and the closedness of `Ω` put `q_out` in `Ω` ([`tendstoModVT_switchAng_of_clusterSetForwardInvariant`](../../SmoothedPolygons/Ch16/ClusterPoint.lean#L967)) | the parts and branch maps are asserted and rest on Proposition 15.3.2, read off figures (E72); the zero count bounds one constant-control piece, not the number of pieces; `χ_W` captures the real roots only for bounded `s`; and the descent ignores the diagonal rows of Table 16.1 (E90) | E90 |
| Theorem 16.4.1, steps (b)–(c) | a cluster point at `q_in` or at `q_out` is a limit "because of the time required to travel from outside an `ε`-ball … to a point inside an `ε/r_scale`-ball" (TeX 13006–13014, 13022–13023); `q_out` is excluded because `W^s(q_out)` lies in the divisor | the lift converges at the finite time `b`, so the radial coordinates of the switching points tend to `0` along the whole sequence; `q_out` is excluded as a cluster point by a hyperbolic box, which uses only the derivative of the extended map at the fixed point ([`Function.not_mapClusterPt_of_transverse_expansion`](../../Basic/Dynamics/HyperbolicBox.lean#L117), [`hasStrictFDerivAt_extension`](../../SmoothedPolygons/Ch14/FixedPointManifolds.lean#L126), [`qOut0_not_mem_switchClusterSet`](../../SmoothedPolygons/Ch16/ClusterPoint.lean#L631)); the convergence to `q_in` follows from `Ω = {q_in}`, and the switching points lie on the local stable curve at `q_in` by definition, through Remark 14.3.4 ([`theorem16_4_1`](../../SmoothedPolygons/Ch16/ClusterPoint.lean#L1021)) | the `ε/r_scale` argument does not show that a cluster point at a hyperbolic fixed point is a limit, and `W^s(q_out)` lies in the divisor only locally (Theorem 14.3.3) (E91) | E91 |
| Theorem A.3.1 | Irwin's theorem, for some open neighbourhood `U` of `p` (TeX 13200–13207) | the StableManifold package's theorem (`Function.exists_localStableSet_localUnstableSet_eq_graph`), applied to the map cut off outside the source of `e`: `e` on the source and a point outside the source elsewhere, so that the local sets of `e` on `U ∩ source` are those of the cut-off map on `U` ([`theoremA_3_1`](../../SmoothedPolygons/AppA/StableManifold.lean#L186)) | the package's theorem for one neighbourhood, against which the proof was written, gives some open `U`, not necessarily inside the source of an open partial homeomorphism; its form for every small neighbourhood makes the cut-off unnecessary (Section 11) | E92 |

## The other proofs

Every other proof follows the book's argument.

### Chapters 2–7

- **Filled along the book's lines:** the gaps of Theorem 2.2.2 (E2), Theorem 2.3.9 (E7), Lemmas
  2.2.6, 2.2.7, 2.4.3 (E5, E9), Lemma 3.1.8 (E34), the shift of §3.5 (E39), Definition 5.0.1 (E41),
  Lemma 5.0.3 (E42, through Theorem 2.2.2, E12 and Theorem 2.3.9), Lemma 5.0.7 (4) (E44), Theorem
  5.0.2 (E45), Lemma 7.5.5 (E30), Theorem 7.5.6 (E31) and Theorem 7.7.1 apart from its step 6 (E32).
- **Corrected:** the index slips of Lemma 2.4.5 (E10) and Lemma 5.0.7 (3) (E44).
- **No proof in the book:**
  - the converse of Problem 3.6.2 for winding number one (E15): the formal proof generalizes the
    formalization's argument for the smoothed polygons;
  - the identification of the minimizers with `K_min` (E47): the formal proof assembles the results
    of Chapters 2–3 that derive the control problem from `K_min`;
  - Remarks 6.6.1, 7.5.2 and 7.6.4 (E38, E36, E37); the proof of Remark 7.5.2 follows the hint of a
    TeX comment.
- **A new argument:** the bound on the cost of trajectories of higher winding number (E15), a
  pointwise inequality between the cost density and the turning of the bottom row of `g`.
- **Lemma 2.4.3.** The formal proof bounds the turning of the tangent by the hyperbolic arc of
  Remark 2.2.4 itself rather than by the osculating circle the book derives from it. It treats the
  curves `j ≠ 0` through `σ₁` rather than the arclength reparametrization of `σ₂`, a symmetric
  choice.
- **Proposition 6.4.1** applies left-invariance once, with `h = g⁻¹`, where the book writes
  `f(g, u) = TL_g f(e, u)` and cancels `TL_{g⁻¹}TL_g`: the same identity in one step.
- **Theorem 7.7.1.** The book does not give its "direct calculation"; since the book gives no
  calculation to follow, the formal one is not a departure. It splits each basis vector of the
  section's tangent space into:
  - the direction of the flow, where the derivative of `f` is `0`;
  - the tangent of the curve of fixed points `q_fix(y₀)`, where it is the identity;
  - costate directions, where the flow is affine.
- **§6.2.** In the proof that minimizers are extremals, the identity of Proposition 6.4.1 and the
  trivialization of Proposition 3.6.1 are checked in matrix coordinates instead of being taken from
  their Lean statements, which are about Mathlib's Lie groups (Section 6); the identity is the same.

### Chapter 8 and Appendix A.1

- **Filled along the book's lines:** the gaps of Lemma 8.2.1 (E52), the vanishing of the Hamiltonian
  at a single time in Theorem 8.1.4, Lemma 8.2.2 and Theorem 8.3.1 (E53), the converse of Theorem
  8.2.6 (E54), the second variation of Theorem 8.2.7 (E55), claim (b) of Theorem 8.3.1 (E56) and
  Corollary A.1.3 (E61).
- **Corrected:** the slips of Lemma 8.1.5 (E50) and Lemma 8.3.4 (E59).
- **The second variation** follows the book's route, with its condition on `ψ` read on the interior
  of the overlap of the supports. The formal proof computes the cost of the deformed arc exactly,
  and the book's expansion is the second-order truncation of that formula (E55).
- **Remark 8.3.3** has no proof in the book; its proof assembles Theorem 8.3.2, the discussion of
  §7.2 and Lemma 3.1.8 (E58).

Three changes are inessential:

- In Lemma 8.1.5 the norm of the error `v` is `|v₁| + |v₂|` instead of the Euclidean one, and
  `‖v‖' ≤ ‖v'‖` is used in its integrated form `‖v(t)‖ ≤ |∫₀ᵗ ‖v'‖|`, which avoids differentiating
  the norm.
  - The estimates of Theorem 8.3.1 use the entrywise `ℓ¹` norm on `2 × 2` matrices likewise (the
    book's Euclidean norm on `𝔰𝔩₂(ℝ)`; any norm does).
- In Lemma 8.3.4, "The solutions are analytic" is replaced by Taylor expansions with remainder,
  obtained from the mean value inequality, which need only the first derivatives of the solutions.
- In Lemma 8.3.4, the three vertices are computed alike where the book treats `e₃` "(say)" (E59).

In Theorem 8.1.4, the count of the zeros at which `λ₂' = 0` (at most two) is proved and used as the
book uses it, although finiteness would follow from the isolation of every zero alone (Section 11).

### Chapter 13

The other proofs follow the book's:

- Lemmas 13.2.1–13.2.4 and (13.2.7), by direct substitution, which for measurable controls is a
  change of variables in the integral equations and the image of a null set;
- Corollary 13.2.7 and Lemma 13.2.8, with the slips of E64;
- Lemma 13.3.1, computed for every vertex at once;
- steps 1, 2 and 4 of Lemma 13.5.2 and Remark 13.5.3.

Where the book only asserts, the formalization supplies standard or certified arguments:

- the constancy of the Hamiltonian along extremals with measurable controls, and the uniqueness of
  extremals up to the first switching time (E62);
- the well-definedness of the Poincaré map and the constancy of the Hamiltonian under it (E67), and
  its time reversal at genuine switching points (E68);
- the facts about `r_scale`, by sign changes of the palindromic polynomial at rational points (E67);
- the verifiable part of Remark 13.5.4 (E69).

### Chapter 15 and §16.1–16.2

The other proofs follow the book's:

- (15.1.1), Lemma 15.1.1 and the facts after Definition 15.1.2, by the book's computations;
- the 2-cells, with their root counts by Descartes's rule of signs (proved for the two sign patterns
  that occur, Section 2) and the impossibility of `(m_A, m_B) = (0, 3)`;
- Proposition 15.2.2, assembled from the discussion (E72);
- the vanishing of the discriminants along the `∂`-loci:
  - by Lemma 13.2.4, with the rotation that relates the two cell points read off the third
    coordinates on `∂_{A,ζ²}`, a step the book leaves out;
  - along `∂_res`, by the trajectory reversal of Lemma 13.2.5, which gives the common root of the
    resultant directly ([`TriFuller.discr_resAB_eq_zero_of_mem_bd`](../../SmoothedPolygons/Ch15/Involution.lean#L632));
- the time reversal and the lexicographic descent of the proof of Theorem 16.1.1;
- the time reversal and the scaling factor `r_scale` of the proof of Theorem 16.2.1.

Where the book only asserts, the formalization supplies standard arguments:

- the continuity of the switching time and of the cell maps, by the continuity of a least positive
  sign change, with the shape of the cubic on the face where `Δ_{A,0} = 0` (E70);
- the estimate `t₁ ≤ t_B` on `𝒞₂^A` (E74);
- the vanishing limiting switching time on the red faces, by semicontinuity (E72);
- the details of the proof of Theorem 16.2.1 (E80).

### Chapter 14, §16.3–16.4 and Appendix A.3

The other proofs follow the book's:

- the chart and its running claims, with (14.1.3) solved in closed form (E81);
- the asymptotics of §14.2 and Remark 14.2.1;
- Lemma 14.3.1 step by step, with the `χ₂₃` check, the divisibility and the zero structure of the
  switching time supplied (E85);
- the last step of Lemma 14.3.1, by the book's route: the backward map built by the same lemmas at
  the reflected point, the two maps inverse for `r > 0` by the time reversal of trajectories, and on
  a neighbourhood by analytic continuation;
- the hyperbolicity in Theorem 14.3.3, from the three facts that the book names (E86);
- Remark 14.3.4 by time reversal, `F_in = τF⁻¹τ`, in the mirrored chart (E87);
- Theorem 14.4.1, by its four sentences from N4, with the steps it does not cite proved (E88):
  - the switching points of a trajectory from `q_out` lie eventually on the local unstable curve
    ([`IsChatteringArcOutOf.eventually_mem_localUnstableSet`](../../SmoothedPolygons/Ch16/ClusterPoint.lean#L921));
  - a first return chatters (Lemma 8.3.4, [`exists_isChatteringArcInto`](../../SmoothedPolygons/Ch16/ClusterCoordinates.lean#L376));
  - the iterates follow the Reinhardt–Poincaré map while they switch cyclically, and an arc that
    leaves the star domain contradicts the state constraint
    ([`IsChatteringArcInto.not_reachesStarBoundary`](../../SmoothedPolygons/Ch14/UnstableCurveSwitches.lean#L108));
  - the second statement by time reversal;
- the last step of Theorem 16.3.1, made precise (E89);
- steps (a) and (f) of the proof of Theorem 16.4.1 (the switching sequence is injective; the cluster
  set is closed, and Theorem 16.1.1 applies to it, as the book says).

## The proof of N4

The proof of N4 was first written as a mathematical argument, in the numbering of
[`SmoothedPolygons/Ch14/ArcRegionInvariant.lean`](../../SmoothedPolygons/Ch14/ArcRegionInvariant.lean), which an independent review checked before the Lean
proofs. The Lean proofs depart from it in three places, with the same statements:

- INV Lemma 6 (an arc with `Y ≥ 16/5` leaves the star domain before it switches) replaces two
  monotonicity arguments by three inequalities for `log`: `log t ≥ 1 - 1/t`,
  `log y ≥ 2(y - 1)/(y + 1)` and `log t ≤ sinh(log t)` ([`ArcParams.f_pos_of_Y_ge`](../../SmoothedPolygons/Ch14/ArcStepExit.lean#L316)).
- Steps 2–4 of INV Proposition 3 are one identity modulo `R̃ = 0`, in which the terms in `f₀`
  cancel, so that `f₀ ≥ 0` is not needed ([`ArcParams.Phi_nonpos`](../../SmoothedPolygons/Ch14/ArcStepRegion.lean#L361), Section 5).
- The update rules of Theorem 2.1 for `f₀` and `p` come from the closed form INV (1.4) of the
  costate along the arc instead of the Poisson brackets of Lemma 2.3 ([`arcParams_reinPoincare`](../../SmoothedPolygons/Ch14/ArcPoincareMap.lean#L600)).
  Lemma 2.3 is used only for the first control after a switch ([`SwitchEntersE2`](../../SmoothedPolygons/Ch14/UnstableCurve.lean#L127), Proposition 3.4).

## The numerical reference

The computations that the four facts replace are kept as a reference, outside the trusted proofs.
[`numerics/`](../../numerics) is a Python implementation of the Fuller–Poincaré map and of the Reinhardt flow along an
`e₂`-arc, exactly as the Lean definitions say. It checks the facts in rigorous ball arithmetic
(python-flint/Arb):

- by adaptive subdivision of boxes for Table 16.1 (for `CellTwoEntersDOut` on part of the cell
  only);
- along sampled orbits of the unstable curve for N4.

It reproduces the book's numbers: for N4, the threshold `r* ≈ 0.0649` and the end point
`(0.2098, -3.0333)` of the curve, against the book's `0.065` and `(0.21, -3.03)`. It gave the
analytic proofs their margins and regions, and re-checks the certificates of the proof of N4
exactly; its results are in [numerics/README.md](../../numerics/README.md).

It wrote no Lean code: the derivative bounds of `DOutContracts` were once an interval chain that
its generator wrote, and are now argued by hand ([`SmoothedPolygons/Ch16/DOutDerivativeBounds.lean`](../../SmoothedPolygons/Ch16/DOutDerivativeBounds.lean)).

## Cited results

The cited results that [`External/`](../../External) proves are proved by their sources' arguments, except:

| Cited result | The source's argument | The formalization's | Why |
| --- | --- | --- | --- |
| Mahler 1947, Theorem 2 (Theorem 2.3.7) | uses its own Lemma 5 (a convex hexagon `H` has `Δ(H) = V(H)/4` and a unique critical lattice, the midpoint lattice, justified by reference to the unique tiling by translates of `H` in another paper) and, in footnote 8, Lemma 5 of another paper (no arc between consecutive lattice points is a segment) | an exact formula for the area of the hexagon of tac-lines, `V(H) = (4 − p²/(D₀D₁D₂))Δ(K)`, gives the area and the bisection; the footnote is derived from Mahler's Theorem 1 | the uniqueness of the critical lattice of a hexagon rests on a uniqueness theory of lattice tilings that Lean lacks and that the source does not give; the exact formula avoids it |
| Mahler 1947, Lemma 3 | stated without proof, with a reference to Lemmas 8 and 12 of paper A, whose proof quotes Theorems B–E of Mahler 1946 (Section 2); paper A's Lemma 1 takes `Δ` of the square from Minkowski's theorem on linear forms, and Mahler 1946 quotes Theorems 2 (selection) and 8 (existence of critical lattices) of its Part I | Mahler's proofs throughout, with the repairs listed below, except that `Δ` of a parallelogram comes from Mahler's own example in §2 of paper A with its Lemmas 2 and 3 (and Lemma 1 is proved in the parallelogram's coordinates, not after an affine map to the square), and that Part I's Theorems 2 and 8 are proved in the plane, by reduced bases and Mahler's compactness theorem | these three results are quoted from works outside the three papers; in the plane Mahler's example and standard arguments give them directly |
| Fejes Tóth's theorem (Theorem 2.1.3) | Fejes Tóth: Dowker's theorem and the cell decomposition of a finite packing, counted with Euler's formula | Dowker's theorem by an alternating merge of normal angles; the cell lemma by maximal cells (Böröczky 2003, Lemma 5), the convexity of their holes by a counting argument on sides instead of Böröczky's walk around boundary cycles, and the side count by angle sums instead of Euler's formula | Mathlib has neither Euler's formula for planar maps nor the Jordan curve theorem, on which the cycle and Euler arguments rest; Dowker's area formula for polygons is likewise missing, and the merge argument needs only measure additivity |
| The Pontryagin maximum principle (§6.2; Agrachev–Sachkov, Theorem 12.5 with free time) | Agrachev and Sachkov's Chapter 12, on a smooth manifold, in the chronological calculus (operators on `C^∞(M)`), with complete smooth vector fields, the well-posedness of Carathéodory solutions cited from Gamkrelidze, and Brouwer's theorem without reference; free time with a cost left to the reader | the same argument in coordinates on an open subset of a finite-dimensional space, the chronological calculus read pointwise along trajectories (D1, D2); a cut-off near the reference trajectory instead of completeness, and well-posedness by Picard iteration and Gronwall's inequality (D11); time changes by measurable new times (D7); one supporting covector for all needle variations (D9); free time with a cost and mixed boundary conditions through one auxiliary system (D6); Brouwer's theorem from the FixedPoint package (D10) | Mathlib has no chronological calculus and no well-posedness for measurable controls; the source derives its reparametrization for a smooth new time and applies it to measurable ones (D7); its proof of Theorem 12.4 takes a covector for each finite needle variation, while the maximum condition at almost every time needs one for all (D9); the free-time case with a cost is left to the reader |

### Mahler's Lemma 3

Mahler's Lemma 3 is otherwise proved by the arguments of paper A and Mahler 1946 (Section 2). They
have errors and gaps, all repaired; [`External/MahlerIrreducible/Lemma3.lean`](../../External/MahlerIrreducible/Lemma3.lean) lists them with the
Lean names:

- **Mahler 1946, proof of Theorem C (p. 337), error.** The function
  `G(X) = F(X){1 + (δ/σ) max(0, σ − ||X|⁻¹X − |P|⁻¹P|)}` is not even (`G(P) = (1 + δ)F(P)` but
  `G(−P) = F(P)`).
  - So `H : G ≤ 1` is not a star body and contains `−P`, whereas paper A's Lemma 10 asserts that `H`
    omits `±P` (proved in Lean, [`External.Mahler1946.m46c_mahlerG_not_distanceFunction`](../../External/Mahler1946/TheoremC.lean#L392)).
  - Repaired by measuring the distance from `|X|⁻¹X` to the nearer of the two directions `±|P|⁻¹P`.
    The rest of the proof stands, except that in its last step one of the two points `±λQ_s`, not
    necessarily `λQ_s`, lies in the cone.
- **Mahler 1946, proof of Theorem E, gap.** "There exists a neighbouring lattice `Λ*` which is
  `K*`-admissible and of determinant `d(Λ*) < d(Λ)`" is asserted without argument; filled by the
  deformation that proves Minkowski's (A) ([`External.Mahler1946.m46e_turn`](../../External/Mahler1946/TheoremE.lean#L369)).
- **Mahler 1946, §4, gap.** That the points `P_k*` are the only points of `Λ*` on or near `C` for
  small `ε` is stated without proof; it is proved ([`External.Mahler1946.m46e_near`](../../External/Mahler1946/TheoremE.lean#L92)).
- **Paper A, proof of Lemma 1, error.** "`±θP₀` are its only points which are inner points of `K₀`"
  fails for `θ < 1/2`; the argument survives, since all such points are multiples of `θP₀`, none of
  them an inner point of `H`.
- **Paper A, proof of Lemma 5, slip.** "lies on `L**`" should read "lies on `C`".
- **Paper A, gaps.**
  - The Corollary to Lemma 5 has no proof (supplied,
    [`External.MahlerIrreducible.ml5_lemma5_cor_six`](../../External/MahlerIrreducible.lean#L1474)).
  - In class B of Lemma 13, the line `L′` through `P` missing `H′` is not justified (filled by a
    support line at the extreme point `P`, tilted slightly).
  - Lemma 12 does not follow from Theorems D and E alone, which need a dense set of boundary points
    on critical lattices with just six boundary points. Paper A's Corollary to Lemma 5 supplies them
    when `K` is not a parallelogram, and its Lemma 1 settles parallelograms
    ([`External.Mahler1946.m46e_lemma12`](../../External/Mahler1946/TheoremE.lean#L759)).
  - Smaller steps left to the reader (the reduction in Lemma 1, three steps of class A of Lemma 13,
    two details of Theorems D and E) are written out.

The readings:

- everything is in the plane;
- the domains are symmetric convex domains, whose gauge is Mahler's distance function;
- the sup norm of `Fin 2 → ℝ` replaces the Euclidean length in the direction `|X|⁻¹X` and in the
  neighbourhoods `|X − Q| ≤ ε` (only their continuity and homogeneity are used);
- irreducibility is tested against symmetric convex subdomains, where Mahler admits all star domains
  (paper A's Lemma 13 bridges the two; Section 6).

### The maximum principle

The maximum principle is otherwise proved by Agrachev and Sachkov's argument (Section 2). The
OptimalControl package's [`docs/AGRACHEV_SACHKOV.md`](https://github.com/vltanh/lean4-optimal-control/blob/main/docs/AGRACHEV_SACHKOV.md) lists the departures, D1–D11, to which its
docstrings refer:

| Item | Departure |
| --- | --- |
| D1 | the manifold is an open subset of a finite-dimensional real normed space |
| D2 | the chronological calculus is read pointwise along trajectories, in coordinates |
| D3 | the system and the cost are `C¹` in the state instead of `C^∞` |
| D4 | the control set is compact (the source tacitly needs `f(q, u(t))` locally bounded), and the auxiliary parameter sets of §§12.3–12.4 are compact intervals |
| D5 | strong local minimizers instead of optimal controls |
| D6 | free time with a cost and mixed boundary conditions, left to the reader (pp. 177, 179, 184), through one auxiliary system |
| D7 | measurable time changes |
| D8 | Lemma 12.1 in the form of its Remark (1), on any convex cone, with the map Lipschitz near the vertex on the cone and differentiable there within it |
| D9 | one supporting covector for all needle variations |
| D10 | Brouwer's theorem from the FixedPoint package |
| D11 | well-posedness and differentiable dependence proved, with a cut-off |

D3 and D5 generalize the statement. The source's proof has three gaps, all repaired; an independent
agent checked them against the source:

- **Lemma 12.1, Remark (1).** The remark extends the lemma to any convex cone, but the proof takes
  points in the interior of the cone, which is empty for a cone with empty interior, a case the
  remark allows.
  - The statement is true: the formal proof takes the points as combinations of points of the cone
    with positive coefficients and uses no interior
    (`HasFDerivWithinAt.zero_mem_interior_image_inter_cone`).
  - For the cones to which the source applies the lemma, `ℝᵏ₊` and its product with a space of
    parameters, its step is valid as written.
- **A needle at `t₁`.** In the proof of Lemma 12.2 the set of Lebesgue points from which the needle
  times are taken may contain `t₁`, and a needle at `t₁` gives no variation on `[0, t₁]`. Such a time
  is moved to a nearby Lebesgue point of `(0, t₁)`, as the source moves repeated times.
- **The needle map.** That the end point of the needle variations is Lipschitz in their lengths and
  differentiable at `0`, with partial derivatives the vectors `g_{τᵢ,uᵢ}(q₁)` (p. 172), is stated
  without proof; it is proved (`ControlSystem.hasFDerivWithinAt_needle`).

Two points that might look like gaps are not:

- `t₁ > 0`, which Lemma 12.2 needs, is the source's standing assumption ("Fix an arbitrary instant
  `t₁ > 0`", p. 163);
- Theorem 12.5 states nontriviality as `(λ_t, ν) ≢ (0, 0)`, which, by the uniqueness for the adjoint
  equation, the formal statement strengthens to every `t`.

### Filippov's theorem

Filippov's theorem is proved by the standard argument; it was written before we had Agrachev and
Sachkov's text and was not compared with their proof (Section 2). Its form with a state constraint,
which §6.1 uses, is proved by the same argument.
