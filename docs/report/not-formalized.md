# Not formalized

Part of the [audit report](../../REPORT.md).

Nothing on the path of the main theorem is left: Theorem 16.3.1 and the results it uses are proved
with no hypothesis, the four facts that the book reads off computations included (Section 2).

- **Outside the scope, by the user's decision** (15 November 2026: formalize what the main results
  need): Chapter 1 (its restatements of results of the later chapters
  among them; the restatement of Theorem 8.3.2 is false, E57); Chapters 9–12 (circular control, off
  the path to the main theorem; Chapter 13 uses only the form `RR` of Chapter 10, and Chapters 14
  and 16 only Lemma 10.1.1 and the coordinates of Chapters 10–11, which are formalized); Appendix
  A.1 apart from Corollary A.1.3 (Lemmas A.1.1 and A.1.2, cited from Amann and Clarke, are not
  stated; the case of Lemma A.1.1 that §6.1 and Corollary A.1.3 use is proved in the OptimalControl
  package), Appendix A.2, A.4 (whose Cayley transform Lemma 10.1.1 uses), A.5 and A.7–A.10; Appendix
  B; and, within the formalized chapters, the remarks and claims of the running text that no main
  result uses (below).
- **Open within the formalized chapters:** the printed Theorem 8.2.7 for abnormal lifts of the
  global minimizer, which is neither proved nor refuted (E55); the formalization proves the
  authors' reading and the printed statement for normal lifts.
- **Within the formalized chapters:**
  - Remarks 7.6.1 and 7.6.3, which report numerical observations as conjectures: the area of the
    smoothed `(6k+2)`-gon "appears" to increase with `k` to `π`, and the smoothed `(6k−2)`-gons
    "seem" to satisfy every condition of an extremal except the sign of `λ_cost`.
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
  - In Chapter 15, Proposition 15.3.2 is stated as a named proposition, with the parts
    `𝒟₀, …, 𝒟₄` ([`TriFuller.Proposition15_3_2`](../../SmoothedPolygons/Ch15/Involution.lean#L892)), and proved in part: the clauses that follow from the
    definitions of the parts, its second clause (`𝒟₂` and `𝒟₃` partition the second cell) and the
    continuous extensions to `𝒟₃` and `𝒟₄` (E72). The rest, which the book reads off Figures
    15.2–15.3, is reduced to four statements ([`TriFuller.proposition15_3_2_of_remaining`](../../SmoothedPolygons/Ch15/PartitionCellTwo.lean#L595)) and not
    proved: that `𝒟₄` is regular closed (the deformation that proves the second clause has no
    analogue in the first cell, where `y₂ > 0`), that the interiors of `𝒟₁` and `𝒟₄` are disjoint
    (which needs an explicit set separating them, with a priori bounds on the small part `𝒟₀`),
    continuous extensions to `𝒟₀`, `𝒟₁` and `𝒟₂`, and the action of `𝔦` on the parts. No result
    uses it, and an exact numerical computation of the parts found it true (for `𝔦`, on 200,000
    random points of each box). Remark 15.2.1 is proved for its first sentence; its
    second, that `F⁻¹(𝒞₂(ζ))` and `F⁻¹(𝒞₂(ζ²))` are the two sides of the hypersurface `∂_res`, is
    read off Figure 15.2. The 2-cell `𝒞₂(ζ², 1, 1)` is defined, but its attachment to the second
    big cell "in a way that agrees with the dynamics" (TeX 12278–12285) is not formalized. The
    proofs of Theorems 16.1.1 and 16.2.1 do not use the following claims of the running text,
    which are not formalized either: that `q_in` and `q_out` lie in `𝒟₁` (TeX 12364–12365,
    12446, 12458) and that `𝒟₀₀ ⊂ 𝒟₁` (12537); that `q_out` is far from `𝒟₀` and `𝒟₄`
    (12458–12460); that `∂_res` and `∂_A` are in involution with the 2-cells (12338–12339, 12344;
    the second fails for `𝔦 = τF`, E73); that `F` is discontinuous along `∂_A` (12342–12343), of
    which a jump on one segment is proved ([`remark15_3_1_segment`](../../SmoothedPolygons/Ch15/FixedPointCells.lean#L791)); that `F₂` restricted to `𝒞₂^A`
    is `F_A` (12431); that the angle `θ₂ ∈ (π/3, π]` to which a point is equivalent is unique
    (12256–12257); and, in the proof of Theorem 16.1.1, `𝒟₄ ⊂ F(𝒟₂₂)` (12644), `θ₁ ≤ 0` on `𝒟₄`,
    `𝒟₀` and `𝒟_in` (12632–12633), `θ₂ ∈ [-π/3, 0]` on `𝒟₂` (12616), and the rows `𝒟₀` and `𝒟₃`
    of Table 16.1 taken separately (12620–12638).
  - In Chapter 14, Remarks 14.2.2 and 14.3.2, which make no precise claim (a pointer to the method
    of Manita and Ronzhina, and a caution about analytic extensions at other points), and the
    figures (the schematic picture of Figure 14.1, the unstable curve of Figure 14.2 and the
    outward spirals of Figure 14.3) are not formalized. Of Figure 14.2, what the proof of Theorem
    14.4.1 uses is N4, which is proved (E88); the figure's numbers (the end point near
    `(0.21, -3.03)`, the threshold `0.065`), the switching points accumulating on the chart boundary
    and the global curve itself (E93) are not stated. In
    §16.4, the claims of §16.4.2 that the repaired proof of Theorem 16.4.1 does not use are not
    formalized either: that the rescaled switching functions behave like cubics, their Weierstrass
    polynomials, and the Reinhardt cells, parts and branch maps (E90). In Appendix A.3 the global
    (immersed) part of Theorem A.3.1 is not stated; no proof of the book uses it (E92).
