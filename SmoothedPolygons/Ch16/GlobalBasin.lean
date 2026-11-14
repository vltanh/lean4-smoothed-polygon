module

public import SmoothedPolygons.Ch16.BasinHypotheses
public import SmoothedPolygons.Ch15.FixedPointCells

/-!
# Chapter 16: Theorem 16.1.1, the global basin of attraction of `q_out`

Theorem 16.1.1 (`thm:basin`) of Hales–Vajjha, *Packings of Smoothed Polygons* (TeX 12505–12744):
every orbit of the Fuller–Poincaré map `F_ang` on `Ξ_{𝒲,0}/V_T` other than the fixed point `q_in`
tends to the fixed point `q_out`. It is proved here from the three named numerical facts of
`SmoothedPolygons/Ch16/BasinHypotheses.lean` (Table 16.1 and the contraction on `𝒟_out`), which are
explicit hypotheses of `theorem16_1_1`.

## The book's proof, and this proof

The book (TeX 12511–12744): partition the two closed big cells into `𝒟₀, …, 𝒟₄` with continuous
branches `F_i`, and `𝒟₁` further into the boxes `𝒟_{1,ij}`; Table 16.1 lists the containments
`F_i(𝒟) ⊆ ⋃ 𝒟*` ("upper triangular", with diagonal entries only for `𝒟_in`, `𝒟_out` and
`𝒟₁ ∖ 𝒟_in`); then (a) a point `q ≠ q_in` of `𝒟_in` eventually leaves `𝒟_in`, "because the
iterates `F^{-k}(τ q)` exit `𝒟_out`", (b) by the triangular structure the orbit eventually stays in
`𝒟₁ ∖ 𝒟_in`, (c) the subclaims make the boxes `𝒟_{1,ij}` strictly decrease in the lexicographic
order until `𝒟_{1,00} = 𝒟_out`, and (d) "once in the small rectangle `𝒟_out` containing `q_out`,
the iterates rapidly converge to the fixed point `q_out`".

This proof follows the same steps with the box regions of `BasinHypotheses.lean`:
1. **Convergence in `𝒟_out`** (step (d); gap G16.3): from `DOutContracts`, `F^N(𝒟₀₀) ⊆ B` and `F`
   is a contraction `g` of the box `B` in coordinates; the contraction mapping theorem gives
   `F^k(x) → q_out` for `x ∈ 𝒟₀₀` (`l5st_tendsto_qOut0_of_mem_boxSet`), and a backward orbit inside
   `𝒟₀₀` is constant at `q_out` (`l5st_eq_qOut0_of_backward_orbit`).
2. **`𝒟₂₂` is never re-entered** (replacing (b) and the last row's exclusion argument, gap G16.5):
   for a switching point `x` (every `F(y)` is one), `F(x) ∈ 𝒟₂₂` implies `x ∈ 𝒟₂₂`, because
   `τ(𝒟₂₂) = 𝒟₀₀`, `F(τ F(x)) = τ(x)` (`F⁻¹ = τ F τ` at switching points) and `F(𝒟₀₀) ⊆ 𝒟₀₀`
   (`l5st_mem_boxSet_22_of_poincareAngZero_mem`).
3. **Leaving `𝒟₂₂`** (step (a)): if `F^n(q) ∈ 𝒟₂₂` for all `n ≥ 1`, then `w_j := τ F^{j+1}(q)` is a
   backward orbit in `𝒟₀₀` (`F(w_{j+1}) = w_j` by `F⁻¹ = τ F τ`), so `w₀ = q_out` by step 1 and
   `F(q) = q_in`; and `F⁻¹(q_in) = {q_in}` (`poincareAngZero_eq_qIn0_iff`), so `q = q_in`.
4. **Descent** (step (c), with the rows `𝒟₄`, `𝒟₂`, `𝒟₃`): outside `𝒟₂₂`, a point of the second
   cell reaches `𝒟₀₀` within three steps (`CellTwoEntersDOut`), and a point of a box `𝒟_{ij}` of the
   first cell goes to the second cell or to a smaller box (`BoxSubclaims`); by induction on the
   lexicographic order the orbit reaches `𝒟₀₀` (`l5st_exists_iterate_mem_boxSet_00`).

Departures from the paper (all forced by gaps of the book's argument, and recorded in
`BasinHypotheses.lean`): the boundary method (gap G16.2) is replaced by containments to be
certified by direct enclosure; the convergence in `𝒟_out` uses a contraction hypothesis
(gap G16.3); `𝒟_in` is the whole box `𝒟₂₂` and the exclusion argument for the last row
(`𝒟₀ ⊂ 𝒟_in`, `𝒟₄ ⊂ F(𝒟₂₂)` and the injectivity of the multi-valued `F`, gap G16.5) is replaced by
step 2, which uses the time reversal as the book's step (a) does; the map is the Poincaré map of
`Ξ_{𝒲,0}/V_T`, at whose non-switching points `F⁻¹ = τ F τ` fails (gap G15.6), which steps 2–3
handle (every image is a switching point; `F⁻¹(q_in) = {q_in}`).
-/

@[expose] public section

namespace SmoothedPolygons

open Set Filter Topology
open scoped Real

namespace TriFuller

/-- `q_out` and `q_in` are fixed points of `F` on `Ξ_{𝒲,0}/V_T` (Lemma 13.5.2, `lemma13_5_2`), and
`τ` exchanges them (`tauQuot_qOut`). -/
theorem poincareAngZero_qOut0_qIn0 :
    poincareAngZero qOut0 = qOut0 ∧ poincareAngZero qIn0 = qIn0 ∧ tauZero qOut0 = qIn0 ∧
      tauZero qIn0 = qOut0 := by
  sorry

/-- "We have `q_in ∈ 𝒟_in := 𝒟_{1,22}` and `q_out ∈ 𝒟_out := 𝒟_{1,00} = 𝒟₀₀`" (TeX 12536–12537),
for the boxes: `pOut ≈ (0.2679, 0.1706, 2.9157) ∈ 𝒟₀₀` and `pIn ≈ (0.2679, 2.9710, 0.2259) ∈ 𝒟₂₂`
(Remark 15.3.1 corrected; from the enclosures of `remark15_3_1`). -/
theorem pOut_mem_cellBox_pIn_mem_cellBox : pOut ∈ cellBox 0 0 ∧ pIn ∈ cellBox 2 2 := by
  sorry

/-- **The arc of the inward spiral does not meet the walls in its interior**: along
`t ↦ z(t, τ(qOutCart), u)` with `u` the first control of `τ(qOutCart)`, `z₃(t) ∉ 𝒲` for
`0 < t < t_sw`. By Lemma 13.2.4 the switching functions along this arc are those along the arc of
`qOutCart` reversed in time, and along that arc `χ_{ζ→ζ²}(t) = √3 t (y + bt/2 + t²/12) > 0` and
`χ_{ζ→1} > 0` on `(0, t_sw)` (the computation of `firstSwitchTime_qOutCart`, TeX 11340–11344;
`SmoothedPolygons/Ch13/FixedPoints.lean`), so `z₃(t)` stays in the open sector where `ζ` is the
only maximizer, which contains no point of `𝒲`. The reduction is to `τ` of the rotated and
rescaled copy `ζ · scale(1/r_scale)` of the arc of `qOutCart`. Prove it by this symmetry, not by a
direct numerical bound: along the arc of `τ(qOutCart)` the polynomial `χ_{ζ→ζ²}/t` has
discriminant about `-5.45·10⁻⁵` and minimum about `2.8·10⁻⁴` at `t ≈ 1.256`, just after the
switch at `t_sw ≈ 1.180`. -/
theorem flow_tau_qOutCart_not_mem_walls :
    ∀ t ∈ Ioo 0 (firstSwitchTime (tau qOutCart)),
      flow t (tau qOutCart) (firstControl (tau qOutCart)) 2 ∉ walls := by
  sorry

/-- **`F⁻¹(q_in) = {q_in}`** on `Ξ_{𝒲,0}/V_T` (implicit in the book's statement of Theorem 16.1.1:
an orbit that reached `q_in` would stay there). If `x` is a switching point,
`τ(x) = F(τ F(x)) = F(τ q_in) = F(q_out) = q_out`; otherwise `x` lies in the interior of the arc
that ends at `F(x) = q_in` and starts at a switching point `w` with `F(w) = q_in`
(`exists_isSwitchingPoint_of_not`), so `w = q_in` and `x` is an interior point of the arc of `q_in`,
which does not meet the walls (`flow_tau_qOutCart_not_mem_walls`), against `x ∈ Ξ_𝒲`. -/
theorem poincareAngZero_eq_qIn0_iff (x : XiW0Quot) : poincareAngZero x = qIn0 ↔ x = qIn0 := by
  sorry

/-- Every point of `Ξ_{𝒲,0}/V_T` lies in the second big cell or in one of the nine boxes of the
first (Proposition 15.2.2 and `closedBoxOne_eq_iUnion_cellBox`). -/
theorem mem_cellTwoSet_or_exists_mem_boxSet (x : XiW0Quot) :
    x ∈ cellTwoSet ∨ ∃ i j : Fin 3, x ∈ boxSet i j := by
  sorry

/-- **Convergence in `𝒟_out`** (TeX 12594–12598, 12742–12743; gap G16.3): under `DOutContracts`,
every orbit starting in `𝒟₀₀` tends to `q_out`. Proof route: `F^N(x) = cellClass p` with `p ∈ B`,
`F^{N+k}(x) = cellClass (g^k p)`; `g` is a contraction of the complete box `B`, so `g^k p → p*`
(`ContractingWith`, Banach's fixed point theorem); `cellClass` is continuous
(`continuousOn_cellClass`); and `cellClass p* = q_out`: `q_out ∈ 𝒟₀₀`
(`pOut_mem_cellBox_pIn_mem_cellBox`) is fixed, so `q_out = cellClass p₀` with `p₀ ∈ B`, `g p₀ = p₀`
by the injectivity of `cellClass` on the open first box (`definition15_1_2`). -/
theorem l5st_tendsto_qOut0_of_mem_boxSet (h : DOutContracts) {x : XiW0Quot}
    (hx : x ∈ boxSet 0 0) : Tendsto (fun k : ℕ ↦ poincareAngZero^[k] x) atTop (𝓝 qOut0) := by
  sorry

/-- **A backward orbit inside `𝒟_out` is `q_out`** (the book's "the iterates `F^{-k}(τ q)` exit
`𝒟_out`", TeX 12729–12732; gap G16.3): if `w_j ∈ 𝒟₀₀` and `F(w_{j+1}) = w_j` for all `j`, then
`w₀ = q_out`. Proof route: `w_j = F^N(w_{j+N}) ∈ cellClass '' B`, say `w_j = cellClass p_j`; by the
injectivity of `cellClass` on `B`, `g(p_{j+1}) = p_j`; so `p₀ = g^k(p_k)` and
`dist(p₀, p*) ≤ κ^k diam B → 0`. -/
theorem l5st_eq_qOut0_of_backward_orbit (h : DOutContracts) (w : ℕ → XiW0Quot)
    (hw : ∀ j, w j ∈ boxSet 0 0) (hF : ∀ j, poincareAngZero (w (j + 1)) = w j) : w 0 = qOut0 := by
  sorry

/-- **`𝒟₂₂` is backward invariant for switching points**: if `x` is a switching point and
`F(x) ∈ 𝒟₂₂`, then `x ∈ 𝒟₂₂`. Proof route: `τ F(x) ∈ τ(𝒟₂₂) = 𝒟₀₀` (`tauZero_image_boxSet`),
`F(τ F(x)) = τ(x)` (`poincareAngZero_tauZero_poincareAngZero`), so `τ(x) ∈ F(𝒟₀₀) ⊆ 𝒟₀₀`
(`DOutContracts`) and `x = τ τ x ∈ 𝒟₂₂`. -/
theorem l5st_mem_boxSet_22_of_poincareAngZero_mem (h : DOutContracts) {x : XiW0Quot}
    (hx : IsSwitchingPointQ x) (hFx : poincareAngZero x ∈ boxSet 2 2) : x ∈ boxSet 2 2 := by
  sorry

/-- **An orbit staying in `𝒟₂₂` is `q_in`** (the book's step for `𝒟_in`, TeX 12728–12733): if `x`
is a switching point and `F^n(x) ∈ 𝒟₂₂` for every `n`, then `x = q_in`. Proof route:
`w_j := τ F^j(x) ∈ 𝒟₀₀` and `F(w_{j+1}) = F(τ F(F^j x)) = τ F^j(x) = w_j` (`F^j(x)` is a switching
point), so `τ(x) = w₀ = q_out` (`l5st_eq_qOut0_of_backward_orbit`). -/
theorem l5st_eq_qIn0_of_forall_iterate_mem_boxSet_22 (h : DOutContracts) {x : XiW0Quot}
    (hx : IsSwitchingPointQ x) (hin : ∀ n, poincareAngZero^[n] x ∈ boxSet 2 2) : x = qIn0 := by
  sorry

/-- **Descent to `𝒟_out`** (TeX 12734–12743, with the rows `𝒟₄`, `𝒟₂`, `𝒟₃` of Table 16.1): an orbit
that never meets `𝒟₂₂` reaches `𝒟₀₀`. Proof route: by well-founded induction on the least box (in
the lexicographic order) containing the current point when it is not in the second cell: a point
of the second cell reaches `𝒟₀₀` within three steps (`CellTwoEntersDOut`); a point of a box
`(i, j) ≠ (0, 0)` (and `≠ (2, 2)`, the orbit avoiding `𝒟₂₂`) goes to the second cell or to a
smaller box (`BoxSubclaims`); every point is in one of these regions
(`mem_cellTwoSet_or_exists_mem_boxSet`). -/
theorem l5st_exists_iterate_mem_boxSet_00 (h₂ : CellTwoEntersDOut) (h₃ : BoxSubclaims)
    {x : XiW0Quot} (hin : ∀ n, poincareAngZero^[n] x ∉ boxSet 2 2) :
    ∃ n, poincareAngZero^[n] x ∈ boxSet 0 0 := by
  sorry

end TriFuller

open TriFuller

/-- **Theorem 16.1.1 (Global Basin)** (`thm:basin`, TeX 12505–12509). "Let `q ≠ q_in` be a point in
`Ξ_{𝒲,0}/V_T`. Then the iterates `F^k q` under the Fuller–Poincaré map tend to the fixed point
`q_out`."

Here `F` is the Poincaré map `poincareAngZero` of `Ξ_{𝒲,0}/V_T` (Lemma 13.5.5), and the numerical
facts the book takes from Mathematica (Table 16.1, Figures 16.1–16.4) and the contraction on
`𝒟_out` that it does not prove (gap G16.3) are the explicit hypotheses `DOutContracts`,
`CellTwoEntersDOut`, `BoxSubclaims` (`SmoothedPolygons/Ch16/BasinHypotheses.lean`, each with its
TeX source and a certification plan).

Proof (the book's steps, module docstring): if some `F^n(q)`, `n ≥ 1`, is outside `𝒟₂₂`, then every
later iterate is (`l5st_mem_boxSet_22_of_poincareAngZero_mem`, the iterates being switching points,
`isSwitchingPointQ_poincareAngZero`), the orbit reaches `𝒟₀₀` (`l5st_exists_iterate_mem_boxSet_00`)
and converges to `q_out` (`l5st_tendsto_qOut0_of_mem_boxSet`); otherwise `F(q) = q_in`
(`l5st_eq_qIn0_of_forall_iterate_mem_boxSet_22`), so `q = q_in` (`poincareAngZero_eq_qIn0_iff`),
excluded.

Departures from the paper: see the module docstring (gaps G16.2, G16.3, G16.5, G15.6). -/
theorem theorem16_1_1 (h₁ : DOutContracts) (h₂ : CellTwoEntersDOut) (h₃ : BoxSubclaims)
    (q : XiW0Quot) (hq : q ≠ qIn0) :
    Tendsto (fun k : ℕ ↦ poincareAngZero^[k] q) atTop (𝓝 qOut0) := by
  sorry

end SmoothedPolygons
