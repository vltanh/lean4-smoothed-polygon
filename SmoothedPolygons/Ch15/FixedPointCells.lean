module

public import SmoothedPolygons.Ch15.Involution

/-!
# Chapter 15: Remark 15.3.1, the fixed points in cell coordinates

Remark 15.3.1 of Hales–Vajjha, *Packings of Smoothed Polygons* (TeX 12445–12461), with `q_in` and
`q_out` corrected (gap G15.1): the cell coordinates of the fixed points of Lemma 13.5.2,
`pOut ≈ (0.267949, 0.1705935, 2.91574)` with `r₂ = 2 - √3` exactly, and `pIn = τ(pOut) ≈ (0.267949,
2.9709992, 0.2258527)` (`remark15_3_1`), and the closeness of `q_in` to the triple juncture of
`𝒟₀, 𝒟₁, 𝒟₄` along the segment `r₂ ↦ (r₂, ψ_in, θ_{2in})` (`remark15_3_1_segment`, a numerical
statement to be certified with the other numerical facts, layer 5b).
-/

@[expose] public section

namespace SmoothedPolygons

open Complex Set Filter Topology
open scoped Real

open TriFuller

/-- **Remark 15.3.1** (TeX 12445–12461), **with `q_in` and `q_out` corrected** (gap G15.1). The book
prints "The fixed point `q_in ∈ 𝒟₁` is given by coordinates `(r_{2in}, ψ_in, θ_{2in}) ≈ (0.267949,
0.1705935, 2.91574)`" and "The fixed point `q_out ∈ 𝒟₁` with coordinates
`(r₂, π - ψ_in, π - θ_{2in})`". The labels are swapped: the printed point is `q_out`, the cell
coordinates of (13.5.1) (Lemma 13.5.2, labelled `q_out` there; Chapter 16 places `q_out` in
`𝒟_out = 𝒟₀₀`, which contains the printed point, and `q_in` in `𝒟_in = 𝒟_{1,22}`, which contains
its image `(r₂, π - ψ, π - θ₂)`; the Jacobian at the printed point has eigenvalues of modulus
`< 0.1`, so it is the attracting fixed point, Lemma 13.5.5). This is a slip with one reading: the
corrected remark reads "`q_out` has coordinates `≈ (0.267949, 0.1705935, 2.91574)` and `q_in`
has coordinates `(r₂, π - ψ_out, π - θ_{2out}) ≈ (0.267949, 2.9709992, 0.2258527)`".

Formalized: the coordinates `pOut` of `q_out`, with `r₂ = 2 - √3` exactly (the book's `0.267949`;
equivalently `|z₁|² = 2|z₂|` at (13.5.1)) and the printed angles to `10⁻⁷`; `pIn = τ(pOut)` are the
coordinates of `q_in`, and `𝔦(q_out) = q_in`. The closeness of `q_in` to the triple juncture of
`𝒟₀, 𝒟₁, 𝒟₄` is `remark15_3_1_segment`; "`q_out` is far from the other parts `𝒟₀, 𝒟₄`" and
"`q_in ∈ 𝒟₁`" are read off Figure 15.2 and are not formalized.

Proof route: `pOut = cellCoords qOutCart` (`cellClass_cellCoords`, `classOf_qOutCart`);
`r₂ = 2 - √3` is the identity `(1 + b²)² = 4(x² + y²)` for `qOutCart = (-1 + ib, x + iy, ·)`, a
polynomial identity in `ℚ(√3)[r]` modulo `P(r_scale) = 0` (as in
`SmoothedPolygons/Ch13/FixedPoints.lean`); the angles from `rScale_fine_bounds` and bounds on
`arctan`. -/
theorem remark15_3_1 :
    pOut ∈ openBoxOne ∧ cellClass pOut = qOut0 ∧ pOut 0 = 2 - √3 ∧
      |pOut 1 - 0.1705935| < 1e-7 ∧ |pOut 2 - 2.91574| < 1e-7 ∧
      pIn = ![pOut 0, π - pOut 1, π - pOut 2] ∧ pIn ∈ openBoxOne ∧ cellClass pIn = qIn0 ∧
      involution qOut0 = qIn0 := by
  sorry

/-- **Remark 15.3.1, the segment through `q_in`** (TeX 12452–12458), corrected (gap G15.1): "The
fixed point is remarkably close to the triple juncture of `𝒟₀, 𝒟₁`, and `𝒟₄`. In fact, the line
segment `r₂ ↦ (r₂, ψ_in, θ_{2in})`, `r₂ ∈ [0, 1]` meets the boundary `∂_B` (separating `𝒟₄` from
`𝒟₀`) at `r₂ ≈ 0.2677`, then meets the boundary `∂_A` (separating `𝒟₀` from `𝒟₁`) at
`r₂ ≈ 0.267905`, then reaches the fixed point at `r₂ ≈ 0.267949`." With the true angles of `q_in`
(`pIn`), the crossings are checked through what characterizes them:
* `∂_B` between `r₂ = 0.26775` and `0.26777`: `Δ_{B,1}` changes sign from `+` to `-` and the switch
  changes from `ζ²` (`χ_B` active, `𝒟₄`) to `1` (`χ_A` active, `𝒟₀`);
* `∂_A` between `r₂ = 0.26790` and `0.26791`: `Δ_{A,0}` changes sign from `-` to `+` and the first
  switching time jumps from `≈ 0.984` to `≈ 0.824` (the discontinuity of `F` along `∂_A`);
* the fixed point at `r₂ = 2 - √3 ≈ 0.2679492` (`remark15_3_1`).
(Along the segment through the printed point, the book's "`q_in`", neither discriminant vanishes
near `r₂ = 0.2679`.)

Numerical: a 5b item. Certification plan: enclose `pIn 1`, `pIn 2` (arguments of explicit algebraic
numbers in `ℚ(√3, r_scale)`) to `10⁻¹⁴`, then the discriminants (`|Δ| ≈ 2·10⁻¹⁰` at `r₂ = 0.2679`,
`0.26791`) and the switching times by interval arithmetic; the switch type by the sign of the
switching cubics at the enclosed roots. An independent check found `Δ_{A,0}` going from about
`-2.6·10⁻¹¹` to `+2.0·10⁻¹¹` across `∂_A`, so the enclosures need high precision there. -/
theorem remark15_3_1_segment :
    let seg : ℝ → Fin 3 → ℝ := fun r ↦ ![r, pIn 1, pIn 2]
    (0 < discrB ζ (cellPoint (seg 0.26775)) ∧ discrB ζ (cellPoint (seg 0.26777)) < 0 ∧
      firstControl (poincare (cellPoint (seg 0.26775))) = ζ ^ 2 ∧
      firstControl (poincare (cellPoint (seg 0.26777))) = 1) ∧
    (discrA ζ (cellPoint (seg 0.26790)) < 0 ∧ 0 < discrA ζ (cellPoint (seg 0.26791)) ∧
      0.95 < firstSwitchTime (cellPoint (seg 0.26790)) ∧
      firstSwitchTime (cellPoint (seg 0.26791)) < 0.86) ∧
    0.26791 < 2 - √3 := by
  sorry

end SmoothedPolygons
