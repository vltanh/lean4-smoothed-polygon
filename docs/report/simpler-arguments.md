# Simpler arguments

Part of the [audit report](../../REPORT.md).

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
  are `≥ 0` by `ln u ≥ 1 - 1/u`.
  - This avoids the formal proof's `r* = 2√y e^{(y-2)/(4y)}` and `e^x ≤ 1/(1 - x)`; the step
    `A - 4b > 0` is unchanged.
- **Proposition 3.1.9.** On a balanced disk `g = [σ₀ σ₂][s₀* s₂*]⁻¹` on `ℝ` with `σ_j`, `σ_j'`
  bounded and `σ_j'` Lipschitz, so the argument of Theorem 3.1.4(3) gives `X` Lipschitz on `ℝ`
  directly; this saves the formal proof's restriction to `[0, 2P]` and periodic extension. The
  reparameterization step is unchanged.
- **Lemma 3.1.8.** The formal proof follows the book (the hexagon `H_K(t)`, its area, the area of
  `P_K` and Reinhardt's observation).
  - One identity does the same work. Since `σ_i = σ_{i-1} + σ_{i+1}` and
    `det(σ_{i-1}, σ_{i+1}) = √3/2`, if `σ_{i-1}` and `σ_{i+1}` move on the lines
    `det(d₁, x - p₁) = 0` and `det(d₂, x - p₂) = 0`, then
    `det(d₁, σ_i - p₁)·det(d₂, σ_i - p₂) = det(d₁, p₁)det(d₂, p₂) - (√3/2)det(d₁, d₂)`, a constant.
  - The left side is `det(d₁, σ_{i+1})det(d₂, σ_{i-1})`, and the plane identity
    `det(a, b)det(c, e) - det(a, e)det(c, b) = det(a, c)det(b, e)` evaluates it.
  - The two gaps that need regularity (the lines are not parallel, the constant is not `0`, E34)
    remain.
- **Theorem 7.7.1, step 6.** The injectivity of `A⁴ - I` on the tangent space `T` of the section
  does not need the linear independence of the basis [`iso_sectionBasis`](../../SmoothedPolygons/Ch7/Isolated/Defs.lean#L206)
  ([`iso_sectionBasis_linearIndependent`](../../SmoothedPolygons/Ch7/Isolated/Hyperbolic.lean#L319)).
  - The four vectors span `T` and `A` acts on their coefficients by
    [`iso_sectionMatrix`](../../SmoothedPolygons/Ch7/Isolated/Defs.lean#L220), whose `M⁴ - I` is invertible.
  - So `A⁴ - I` maps `T` onto `T` and is injective because `T` is finite-dimensional.
- **Theorem 7.5.1.** Centralizing `h` only uses `h ≠ ±I` (immediate from `tr h ∈ (1, 2)`);
  ellipticity is not needed, and the 2017 preprint already argues so.
- **The reflection invariance of `𝔥*` (§4.6, Definition 5.0.1).** It can be read off the
  inequalities `|x| < 1/√3`, `x² + y² > 1/3` of the star domain, which are even in `x`. The formal
  proof, like §4.6, goes through the star functions (`S` permutes them) and Theorem 4.4.1, as it
  must for `R`.
- **Theorem 5.0.6.** Once the claim is applied corner by corner (Section 7), the step
  `h₀ ∩ h₁ ∩ h₂ = ∅` of the book's proof is not used; the formalization proves it
  ([`inter_hRegion_eq_empty`](../../SmoothedPolygons/Ch5/AreaBound.lean#L492)) but could drop it.
- **Lemma 5.0.7 (2).** No derivatives are needed. With `s = √3x`, `c = 3y² - 1`,
  `f(s) = (1 + s)(1 - s)²(s² + c)` and `w = √(1 - s²)`,
  `(√(2f(s)) + √(2f(-s)))² = 4w²(1 + c - w²)(1 + w)`, which increases with `w` for `c ≥ 1`.
  - So `√(ρ₀ρ₁²ρ₂) + √(ρ₀²ρ₁ρ₂)` decreases in `x ≥ 0` while `(ρ₀ + ρ₁)ρ₂` increases. This proves
    (2) for `y² ≥ 2/3`, not only `y ≥ √3`.
  - The formal proof follows the book's sign analysis of the derivatives, with its split at
    `x = 1/4`.
- **Lemma 6.1.2 in §6.1.** The convexity of the velocity sets, extended by the cost, can be seen
  directly: `[Z_u, X]/⟨Z_u, X⟩` is a linear-fractional function of `u` whose denominator is
  negative on `U_T` (Lemma 3.3.4), so it maps the convex `U_T` onto a convex set, and neither `gX`
  nor the cost depends on `u`.
  - The formal proof follows the book (Lemma 6.1.2, carried to the matrix system by Lemma 4.5.2).
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
  angle functions.
  - `det(w(c), w)²/|w|²` has derivative `2 det(w(c), w)⟨w(c), w⟩ det(w, w')/|w|⁴ = 0`, so
    `det(w(c), w) = 0`, and then `det(w(c), σ - σ(c))` has derivative `0`.
  - The formal proof uses it.
- **The first control of `q_out` (Lemma 13.5.2).** Lemma 13.2.6 gives it at once.
  - At (13.5.1) `z₃⁰ < 0`, so `RR(z₃⁰, ζ) = RR(z₃⁰, ζ²) = -z₃⁰/2 > z₃⁰ = RR(z₃⁰, 1)`, and the tie is
    broken by `RR(z₂⁰, ζ) - RR(z₂⁰, ζ²) = √3 Im z₂⁰ > 0`, so `V_{T,max} = {ζ}`.
  - The formal proof reads it off the signs of the switching functions on `[0, t_sw]`, which it
    needs anyway to show that `t_sw` is the first switching time (E67).
- **Convergence in `𝒟_out` (Theorem 16.1.1).** The existence part of Banach's fixed point theorem
  is not needed: `q_out ∈ 𝒟₀₀` is a fixed point already, and the contraction gives
  `dist(gᵏ(p), p_out) ≤ κᵏ dist(p, p_out)` directly. The formal proof applies Mathlib's
  `ContractingWith` and then identifies its fixed point with `q_out` (E78).
- **The `∂`-loci of §15.3.** The vanishing of the discriminants needs only that `χ_B` vanishes to
  second order at `0` on the top faces (on `𝒞₂(ζ², 0, 2)`, `χ_B = -t²(t/12 + y₁/2)`), which Lemma
  13.2.4 carries to a double root at the switching time.
  - The multiplicities `m_A`, `m_B` of the cell notation need not be introduced, as the formal
    proof, following the book, does.
  - Along `∂_res` the trajectory reversal alone (`τ` of the reversed trajectory returns to the
    point, whose `z₃` is `0`) gives the common root of `χ_{A,0}` and `χ_{B,1}`, without Lemma
    13.2.4; the formal proof does this ([`TriFuller.discr_resAB_eq_zero_of_mem_bd`](../../SmoothedPolygons/Ch15/Involution.lean#L632)).
- **The continuity of `F_A` (§15.3).** Mathlib's one-sided continuity of roots,
  `Polynomial.exists_roots_norm_sub_lt_of_norm_coeff_sub_lt` (every root of a polynomial has a
  nearby root of a close monic polynomial that splits), applies, since a nearby `χ_{A,0}` with
  `Δ_{A,0} ≥ 0` splits over `ℝ`.
  - It is the more standard route at a double root.
  - The formal proof uses the shape of the cubic on the face instead
    ([`TriFuller.continuousOn_cellMapA_cellMapB`](../../SmoothedPolygons/Ch15/Continuity.lean#L892), E70).
- **(14.1.3) in closed form.** Since `Z_{e₂}` and `Z_{e₃}` have zero `(2, 1)` entry, the last two
  equations of (14.1.3) force `(Λ_R)₁₁ = hX₁₁` and `(Λ_R)₂₁ = hX₂₁`, with
  `h = ⟨Λ₁ + (3/2)J, X⟩`, and `⟨X, Λ_R⟩ = 0` then fixes `(Λ_R)₁₂`.
  - So the book's bare assertions follow at once (E81):
    - `Λ_R = hK(X)`;
    - the system has determinant `-(8/(3√3))X₂₁` and full rank exactly when `X₂₁ ≠ 0`;
    - the orders of the entries of `Λ_R` follow from `h = r³g(r)`.
  - The formal proof uses it ([`lieΛR_eq_reducedHam_smul`](../../SmoothedPolygons/Ch14/LieChart.lean#L256)), in place of the dual-basis identities by
    which the chart defines `Λ_R`.
- **Lemma 14.3.1, Step 10, by the inverse function theorem.** `DF(0, x̃_out)` is block triangular,
  `(r_scale, 0; *, D fullerChartMap(x̃_out))` (`∂_r F₁ = r_scale`; `∂_{x̃} F₁ = 0` and
  `∂_{x̃} F₂ = D fullerChartMap` because the divisor is invariant).
  - It is invertible: `D
    fullerChartMap(x̃_out)` is conjugate to Chapter 13's certified Jacobian `jacobianOut r_scale`,
    whose determinant `D(r_scale) ≈ 4.16 × 10⁻⁷` is positive by an exact Taylor certificate.
  - The certificate: `D(r) = d₀ - (e₁s + ⋯ + e₅s⁵)` with `s = r - c` at the convergent
    `c = 3961388236/631380705` of `r_scale` (`|r_scale - c| ≤ 10⁻¹⁸`), `d₀ ≈ 4.1626 × 10⁻⁷` and
    `0 < e_k ≤ 6.1 × 10⁸`.
  - Mathlib's `HasStrictFDerivAt.toOpenPartialHomeomorph` and
    `OpenPartialHomeomorph.analyticAt_symm` then give an analytic inverse, with no backward map.
  - Remark 14.3.4, which identifies the inverse with the backward Reinhardt–Poincaré map, then
    needs the time reversal of trajectories on its own.
  - The formal proof follows the book's route (E85).
- **Theorem 14.4.1 without the unstable curve.** The proof of N4 gives more than N4: Lemma 5.1 and
  [`ArcRegionInvariant.reachesStarBoundary`](../../SmoothedPolygons/Ch14/ArcRegionInvariant.lean#L221) show that every chart point with `r > 0` of a
  neighbourhood `V` of `(0, x̃_out)` reaches the boundary of the star domain.
  - With this form, the second step of [`theorem14_4_1_out`](../../SmoothedPolygons/Ch14/NoReturnProof.lean#L95) needs only that the rotated
    switching points of the arc out of `q_out` eventually lie in `V` with `r > 0`, the convergence
    half of [`IsChatteringArcOutOf.eventually_mem_localUnstableSet`](../../SmoothedPolygons/Ch16/ClusterPoint.lean#L921), and not the backward
    orbits of Remark 14.3.4.
  - By the import-all audit, [`theorem14_4_1`](../../SmoothedPolygons/Ch14/NoReturnProof.lean#L170) reaches Theorem A.3.1, Remark 14.3.4 and
    [`hasStrictFDerivAt_extension`](../../SmoothedPolygons/Ch14/FixedPointManifolds.lean#L126) only through that lemma, so this route would free Mahler's First
    conjecture from the stable manifold theorem.
  - The assembly from Theorem 14.4.1, [`theorem16_3_1_of_theorem14_4_1`](../../SmoothedPolygons/Ch16/NoChattering.lean#L387), does not use it: the
    first part of Theorem 16.4.1 needs at `q_out` only the derivative of the extended map (E91).
  - The book argues through the curve ("All switches must be on the unstable curve"), and the
    formal proof follows it.
- **`q_out` is not a cluster point, from the same fact.** If `q_out` were a cluster class of the
  switching points of a chattering arc into the singular locus (step (c) of Theorem 16.4.1, E91),
  infinitely many rotated switching points would be chart points of `V` with `r > 0`
  ([`qOut0_not_mem_switchClusterSet`](../../SmoothedPolygons/Ch16/ClusterPoint.lean#L631) builds them).
  - Then [`IsChatteringArcInto.not_reachesStarBoundary`](../../SmoothedPolygons/Ch14/UnstableCurveSwitches.lean#L108) would give a contradiction, in place of
    the hyperbolic box.
  - With the previous item, Mahler's First conjecture would use nothing from §14.3; but it would
    depart from the book's argument at `q_out` and tie Theorem 16.4.1 to N4.
- **The two large cofactors of the proof of N4.** Both come from `√3² = 3` only.
  - The cofactor-free device that [`SmoothedPolygons/Ch14/ArcRelation.lean`](../../SmoothedPolygons/Ch14/ArcRelation.lean) documents and
    [`SmoothedPolygons/Ch14/ArcPoincareMap.lean`](../../SmoothedPolygons/Ch14/ArcPoincareMap.lean) uses (the frame components divided by `√3`, then
    `field_simp; ring`) applies to the relation ([`arcParams_rel_identity`](../../SmoothedPolygons/Ch14/ArcRelation.lean#L180)) and to the `N₂₃`
    half of the normal form ([`arc_normalForm`](../../SmoothedPolygons/Ch14/ArcNormalForm.lean#L225)) as well.
  - The three Bernstein lists would then be the only certificates of the proof that a computer
    found.
- **Lemma 3.1 of the proof of N4 without derivatives.** With `G(0) = 0`,
  `G(τ) = (1 - e^{-τ}) - (e^τ - 1) + Y′(e^τ - 1 - τ) + p(e^τ - 1)`, and `Y′ ≥ 2` gives
  `G(τ) ≥ 2 sinh τ - 2τ + p(e^τ - 1) > 0` for `τ > 0`. The formal proof ([`ArcParams.g_pos`](../../SmoothedPolygons/Ch14/ArcParams.lean#L353)) shows
  that `G` increases, from the sign of `G′`.
- **`F(R₀) ⊆ 𝒟₀₀` (Table 16.1).** The lemma that the proof of `CellTwoEntersDOut` proves for the
  region `R₀ = {0 < θ₁ < θ₂ ≤ π}` ([`TriFuller.CellTwoAnalytic.poincareAngZero_mem_of_regionR0`](../../SmoothedPolygons/Ch16/CellOneToDOut.lean#L219)) contains the first half of
  `DOutContracts` off the faces `r₂ ∈ {0, 1}` and `ψ = 0`, since `θ₁ = θ₂ - ψ ≥ 2π/3 - 1.1 > 0` on
  `𝒟₀₀`.
  - The proof of `DOutContracts`, written before it, proves that half on `𝒟₀₀` separately
    ([`TriFuller.DOutAnalytic.mapsTo_boxSet_zero_zero`](../../SmoothedPolygons/Ch16/DOutInvariant.lean#L309)), from the same identities
    [`TriFuller.DOutAnalytic.C₁_eq`](../../SmoothedPolygons/Ch16/DOutInvariant.lean#L78) and [`TriFuller.DOutAnalytic.C₂_eq`](../../SmoothedPolygons/Ch16/DOutInvariant.lean#L67).
- **The reading of Theorem 14.4.1.** In the direction from [`Theorem14_4_1`](../../SmoothedPolygons/Ch14/NoReturn.lean#L108) to the unrestricted
  statement ([`theorem14_4_1_iff_unrestricted`](../../SmoothedPolygons/Ch14/NoReturnReading.lean#L62)), the second part of the hypothesis is not used: the
  first part gives both unrestricted parts, the second by time reversal.
- **Theorem A.3.1 without the cut-off.** The StableManifold package also has the theorem for every
  neighbourhood `U` of `p` inside a fixed one
  (`Function.exists_nhds_localStableSet_localUnstableSet_eq_graph`), which applies with `U` inside
  the source of `e` directly.
  - The formal proof, written against the form for one neighbourhood, cuts the map off outside its
    source instead (E92).
