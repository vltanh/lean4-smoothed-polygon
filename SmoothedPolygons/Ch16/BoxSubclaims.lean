module

public import SmoothedPolygons.Ch16.BoxInequalities
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# `BoxSubclaims` without computer assistance

The hypothesis `BoxSubclaims` of Theorem 16.1.1 (`SmoothedPolygons/Ch16/BasinHypotheses.lean`;
the subclaims `subclaim_{ij}` of Hales–Vajjha, TeX 12680–12726, Figures 16.3–16.4, merged with the
row `𝒟₄` of Table 16.1): for `(i, j) ∉ {(0, 0), (2, 2)}`, every point of the box `𝒟_{ij}` that is
not in the second big cell is mapped into the second big cell or into a box `𝒟_{kℓ}` with
`(k, ℓ) ≺ (i, j)` (`boxSubclaims`).

## The proof

A point `x = cellClass p`, `p ∈ 𝒟_{ij}`, `x ∉ cellTwoSet`, is one of:

* **a face point whose first control is not `ζ`**: the edge `r₂ = 0`, or `ψ = 0` or `r₂ = 1` over
  `θ₂ ∈ [0, π/3]`. As classes these lie in `𝒟₀₀` (`cellClass_mem_boxSet_zero_zero_of_r_zero`,
  `cellClass_mem_boxSet_zero_zero_of_rot`), which `F` maps into itself (`mapsTo_boxSet_zero_zero`,
  part of `DOutContracts`), and `(0, 0) ≺ (i, j)`. (The face `θ₂ = 0` with `r₂ ∈ (0, 1)`,
  `ψ ∈ (0, π)` is the top face of the second cell, excluded by `x ∉ cellTwoSet`.)
* **a point with first control `ζ`** (`generic_image`): the switch to `1` is the root `τ` of `D`
  (`exists_root_of_signs`), and either the trajectory switches to `ζ²` before it and `F(x)` lies
  in the second cell, or the image is `w = ζ F(z)` with `w₁ = U₀ + i V₀`, `w₂ = U₁ + i V₁`,
  `w₃ ≤ 0` real and `Y(τ) ≥ 0` (`image_dichotomy`). The cell of the image is then decided by exact
  signs (`cellCoords_spec_of_re_nonpos`), and the box by:
  * `ψ' < π/3` (`C₁ < 0`): `C₁_neg_of_three` on `𝒟₀₁`, `𝒟₀₂`, `𝒟₁₁`, `𝒟₁₂` and
    `C₁_neg_of_four` on `𝒟₁₀`, `𝒟₂₀`; the image is in a box `𝒟_{0ℓ}`;
  * on `𝒟₀₁` also `θ₂' > 2π/3 ≥ π - 1.1` (`C₂_neg_of_sin_nonneg`), so the image is in `𝒟₀₀`; on
    `𝒟₀₂` also `θ₂' ≥ 1.1` (`twoU₁_sub_V₁_neg`, which uses `Y(τ) ≥ 0`), so it is in `𝒟₀₀ ∪ 𝒟₀₁`;
  * on `𝒟₂₁` no inequality: `y₁ = r₁ sin(θ₁ + 2π/3) ≥ 0` there, so `Im w₁ = V₀ > 0` and the image
    angle `θ₁' = arg w₁ ∈ (0, π)`; then `ψ' = θ₂' - θ₁' < θ₂'`, so `ψ' > 2π/3` forces
    `θ₂' > 2π/3 > π - 1.1`: the image is in a box `𝒟_{kℓ}` with `k ≤ 1` or in `𝒟₂₀`.

At a tie of the two switches (`w₃ = 0`, the surface `∂_res`) the same signs give `ψ' = 0`.

Departure from the paper: the book reads the subclaims off computer plots by the boundary method
(Figures 16.3–16.4, TeX 12680–12726); the formalization proves them analytically, by the root
structure of the switching cubics, the exact identities of
`SmoothedPolygons/Ch16/BoxInequalities.lean` (signs of explicit polynomials in the switching time,
`r₂` and the sines and cosines of the cell angles, and one discriminant), and the convex-cone
position of `w₁ = r₁ e^{iφ₁} + τ e^{5πi/6}` on `𝒟₂₁`. No numerical evaluation of the map is used;
the constants are `cos 1.1 > 9/20`, `sin 1.1 < 9/10`, `cos(1.1 - π/6) ≥ 3/4`.
-/

@[expose] public section

namespace SmoothedPolygons.TriFuller.BoxAnalytic

open Set DOutAnalytic

/-! ### Sign facts -/

private theorem cy₂_neg {p : Fin 3 → ℝ} (hr : 0 < p 0) (h1 : Real.pi / 3 < p 2)
    (h2 : p 2 ≤ Real.pi) : cy₂ p < 0 := by
  unfold cy₂
  have : 0 < Real.sin (p 2 + 2 / 3 * Real.pi - Real.pi) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  rw [Real.sin_sub_pi] at this
  exact mul_neg_of_pos_of_neg hr (by linarith)

private theorem cy₂_nonneg {p : Fin 3 → ℝ} (hr : 0 ≤ p 0) (h1 : 0 ≤ p 2)
    (h2 : p 2 ≤ Real.pi / 3) : 0 ≤ cy₂ p := by
  unfold cy₂
  have : 0 ≤ Real.sin (p 2 + 2 / 3 * Real.pi) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [Real.pi_pos]) (by linarith)
  positivity

private theorem cy₁_nonneg {p : Fin 3 → ℝ} (hr : p 0 ≤ 1) (h1 : -(2 * Real.pi / 3) ≤ p 2 - p 1)
    (h2 : p 2 - p 1 ≤ Real.pi / 3) : 0 ≤ cy₁ p := by
  unfold cy₁
  have : 0 ≤ Real.sin (p 2 - p 1 + 2 / 3 * Real.pi) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have : 0 ≤ 1 - p 0 := by linarith
  positivity

private theorem cκ_nonneg {p : Fin 3 → ℝ} (h0 : 0 ≤ p 0) (h0' : p 0 ≤ 1) (h1 : 0 ≤ p 1)
    (h1' : p 1 ≤ Real.pi) : 0 ≤ cκ p := by
  unfold cκ
  have := Real.sin_nonneg_of_nonneg_of_le_pi h1 h1'
  have : 0 ≤ 1 - p 0 := by linarith
  positivity

private theorem cκ_pos {p : Fin 3 → ℝ} (h0 : 0 < p 0) (h0' : p 0 < 1) (h1 : 0 < p 1)
    (h1' : p 1 < Real.pi) : 0 < cκ p := by
  unfold cκ
  have := Real.sin_pos_of_pos_of_lt_pi h1 h1'
  have : 0 < 1 - p 0 := by linarith
  positivity

/-- `3 cos ψ + 2√3 sin ψ ≥ 0` on `[0, 2π/3]` (`√3 cos ψ + sin ψ = 2 sin(ψ + π/3) ≥ 0`). -/
private theorem three_psi {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 2 * Real.pi / 3) :
    0 ≤ 3 * Real.cos x + 2 * √3 * Real.sin x := by
  have hq : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hq0 : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos])
  have h := Real.sin_nonneg_of_nonneg_of_le_pi (x := x + Real.pi / 3) (by linarith [Real.pi_pos])
    (by linarith)
  rw [Real.sin_add, Real.cos_pi_div_three, Real.sin_pi_div_three] at h
  nlinarith

/-- `cos θ + √3 sin θ = 2 sin(θ + π/6) ≥ 0` on `[0, 5π/6]`. -/
private theorem three_theta {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 5 * Real.pi / 6) :
    0 ≤ Real.cos x + √3 * Real.sin x := by
  have h := Real.sin_nonneg_of_nonneg_of_le_pi (x := x + Real.pi / 6) (by linarith [Real.pi_pos])
    (by linarith)
  rw [Real.sin_add, Real.cos_pi_div_six, Real.sin_pi_div_six] at h
  linarith

/-! ### The image in cell coordinates -/

/-- **A point with first control `ζ`**: under the sign conditions of `exists_root_of_signs` and of
`image_dichotomy`, either `F(x)` is in the second big cell or the switch to `1` at `τ` gives the
rotated image `w`. -/
private theorem generic_image {p : Fin 3 → ℝ} (hp : p ∈ closedBoxOne)
    (hroot : (cy₂ p ≤ 0 ∧ 0 ≤ cκ p ∧ (0 < cκ p ∨ cy₂ p < 0)) ∨
      (0 ≤ cy₂ p ∧ 0 ≤ cy₁ p ∧ 0 < cκ p))
    (hB : (0 < p 0 ∧ 0 < Real.sin (p 2)) ∨ ∀ t, 0 < t → 0 ≤ imZ₃ p t) :
    poincareAngZero (cellClass p) ∈ cellTwoSet ∨
      ∃ τ, 0 < τ ∧ V₂ p τ = 0 ∧ 0 < V₁ p τ ∧ 0 ≤ imZ₃ p τ ∧ ∃ w : Fin 3 → ℂ,
        w ∈ sectionZero ∧ poincareAngZero (cellClass p) = classOf w ∧
        (w 0).re = U₀ p τ ∧ (w 0).im = V₀ p τ ∧ (w 1).re = U₁ p τ ∧ (w 1).im = V₁ p τ ∧
        (w 2).im = 0 ∧ (w 2).re ≤ 0 := by
  obtain ⟨⟨h0, h0'⟩, ⟨h1, h1'⟩, ⟨h2, h2'⟩⟩ := hp
  have hdom : p ∈ cellDomain := ⟨⟨h0, h0'⟩, ⟨h1, h1'⟩, ⟨by linarith [Real.pi_pos], h2'⟩⟩
  have hk : 0 ≤ cκ p := by
    rcases hroot with ⟨-, hk, -⟩ | ⟨-, -, hk⟩
    · exact hk
    · exact hk.le
  obtain ⟨τ, hτ, hτ0, hneg, hpos, hV1⟩ := exists_root_of_signs h0 h0' hroot
  rcases image_dichotomy hdom hk hτ hτ0 hneg hpos hB with h | ⟨hY, w, hw⟩
  · exact Or.inl h
  · exact Or.inr ⟨τ, hτ, hτ0, hV1, hY, w, hw⟩

/-- The image `w` in cell coordinates, when `Im w₂ > 0` and `w₁ ≠ 0`. -/
private theorem image_coords {w : Fin 3 → ℂ} (hw : w ∈ sectionZero) (h2i : (w 2).im = 0)
    (h2r : (w 2).re ≤ 0) (hw0 : w 0 ≠ 0) (hw1 : 0 < (w 1).im) :
    classOf w = cellClass (cellCoords w) ∧ cellCoords w 0 ∈ Icc 0 1 ∧
      cellCoords w 1 ∈ Icc 0 Real.pi ∧
      cellCoords w 1 = toIcoMod Real.two_pi_pos 0 (Complex.arg (w 1) - Complex.arg (w 0)) ∧
      cellCoords w 2 = Complex.arg (w 1) ∧ Complex.arg (w 1) ∈ Ioo 0 Real.pi := by
  have hw1' : w 1 ≠ 0 := by rintro h; rw [h] at hw1; simp at hw1
  obtain ⟨c0, c1, c1e, c2, hcl⟩ := cellCoords_spec_of_re_nonpos hw h2i h2r hw0 hw1'
  exact ⟨hcl.symm, Ioo_subset_Icc_self c0, c1, c1e, c2, arg_mem_Ioo_of_im_pos hw1⟩

/-- **`ψ' < π/3`**: when `C₁ < 0` at `τ` the image is the class of a point `q` with
`r₂ ∈ [0, 1]`, `ψ ∈ [0, π/3]`, `θ₂ = arg w₂ ∈ (0, π)`. -/
private theorem image_psi_lt {p : Fin 3 → ℝ} {τ : ℝ} {w : Fin 3 → ℂ} (hw : w ∈ sectionZero)
    (hcl : poincareAngZero (cellClass p) = classOf w) (e0r : (w 0).re = U₀ p τ)
    (e0i : (w 0).im = V₀ p τ) (e1r : (w 1).re = U₁ p τ) (e1i : (w 1).im = V₁ p τ)
    (h2i : (w 2).im = 0) (h2r : (w 2).re ≤ 0) (hV1 : 0 < V₁ p τ)
    (hC : U₀ p τ * (V₁ p τ - √3 * U₁ p τ) - V₀ p τ * (U₁ p τ + √3 * V₁ p τ) < 0) :
    ∃ q : Fin 3 → ℝ, poincareAngZero (cellClass p) = cellClass q ∧ q 0 ∈ Icc 0 1 ∧
      q 1 ∈ Icc 0 (Real.pi / 3) ∧ q 2 ∈ Icc 0 Real.pi ∧ q 2 = Complex.arg (w 1) := by
  have hw0 : w 0 ≠ 0 := by
    intro h
    have h1 : U₀ p τ = 0 := by rw [← e0r, h]; simp
    have h2 : V₀ p τ = 0 := by rw [← e0i, h]; simp
    rw [h1, h2] at hC
    simp at hC
  obtain ⟨hcc, c0, c1, c1e, c2, harg⟩ := image_coords hw h2i h2r hw0 (by rw [e1i]; exact hV1)
  refine ⟨cellCoords w, hcl.trans hcc, c0, ⟨c1.1, ?_⟩, ⟨?_, ?_⟩, c2⟩
  · rw [c1e]
    refine (toIcoMod_lt_pi_div_three (by rw [← c1e]; exact c1) ?_).le
    rw [e0r, e0i, e1r, e1i]
    exact hC
  · rw [c2]; exact harg.1.le
  · rw [c2]; exact harg.2.le

/-! ### The target boxes -/

private theorem exists_theta_index (k : Fin 3) {q : Fin 3 → ℝ} (h0 : q 0 ∈ Icc 0 1)
    (h1 : q 1 ∈ Icc (basinA k.castSucc) (basinA k.succ)) (h2 : q 2 ∈ Icc 0 Real.pi) :
    ∃ l : Fin 3, q ∈ cellBox k l := by
  refine (fun hl ↦ ?_) (show ∃ l : Fin 3, q 2 ∈ Icc (basinB l.succ) (basinB l.castSucc) from ?_)
  · obtain ⟨l, hl⟩ := hl
    exact ⟨l, h0, h1, hl⟩
  rcases le_total (Real.pi - 1.1) (q 2) with h | h
  · exact ⟨0, by simp [basinB, h, h2.2]⟩
  rcases le_total 1.1 (q 2) with h' | h'
  · exact ⟨1, by simp [basinB, h, h']⟩
  · exact ⟨2, by simp [basinB, h2.1, h']⟩

private theorem boxLexLt_zero_zero {i j : Fin 3} (h : (i, j) ≠ (0, 0)) : BoxLexLt 0 0 i j := by
  fin_cases i <;> fin_cases j <;> simp_all [BoxLexLt]

/-- The faces whose first control is not `ζ` (`r₂ = 0`; `ψ = 0` or `r₂ = 1` over `θ₂ ≤ π/3`) are
in `𝒟₀₀`, which `F` maps into itself; so it suffices to treat the other points of a box. -/
private theorem box_of {i j : Fin 3} (hij : (i, j) ≠ (0, 0))
    (hgen : ∀ p ∈ cellBox i j, 0 < p 0 → ¬(p 2 ≤ Real.pi / 3 ∧ (p 1 = 0 ∨ p 0 = 1)) →
      cellClass p ∉ cellTwoSet → poincareAngZero (cellClass p) ∈ cellTwoSet ∨
        ∃ k l : Fin 3, BoxLexLt k l i j ∧ poincareAngZero (cellClass p) ∈ boxSet k l) :
    ∀ x ∈ boxSet i j, x ∉ cellTwoSet →
      poincareAngZero x ∈ cellTwoSet ∨
        ∃ k l : Fin 3, BoxLexLt k l i j ∧ poincareAngZero x ∈ boxSet k l := by
  rintro x ⟨p, hp, rfl⟩ hx
  have hcl1 : p ∈ closedBoxOne := (closedBoxOne_eq_iUnion_cellBox ▸
    mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨j, hp⟩⟩ : p ∈ closedBoxOne)
  obtain ⟨⟨h0, h0'⟩, -, ⟨h2, -⟩⟩ := id hcl1
  by_cases hr0 : p 0 = 0
  · exact Or.inr ⟨0, 0, boxLexLt_zero_zero hij,
      mapsTo_boxSet_zero_zero (cellClass_mem_boxSet_zero_zero_of_r_zero hcl1 hr0)⟩
  have hr : 0 < p 0 := lt_of_le_of_ne h0 (Ne.symm hr0)
  by_cases hrot : p 2 ≤ Real.pi / 3 ∧ (p 1 = 0 ∨ p 0 = 1)
  · exact Or.inr ⟨0, 0, boxLexLt_zero_zero hij,
      mapsTo_boxSet_zero_zero (cellClass_mem_boxSet_zero_zero_of_rot ⟨hr, h0'⟩ hrot.2 ⟨h2, hrot.1⟩)⟩
  exact hgen p hp hr hrot hx

/-- The top face `θ₂ = 0` of the second cell: excluded by `x ∉ cellTwoSet` (for the points with
`r₂ < 1`, `ψ ∈ (0, π)`). -/
private theorem theta_pos {p : Fin 3 → ℝ} (hr : 0 < p 0) (hr1 : p 0 ≠ 1) (h0' : p 0 ≤ 1)
    (h1 : 0 < p 1) (h1' : p 1 < Real.pi) (h2 : 0 ≤ p 2) (hx : cellClass p ∉ cellTwoSet) :
    0 < p 2 := by
  rcases h2.lt_or_eq with h | h
  · exact h
  · exfalso
    exact hx ⟨p, ⟨⟨hr, lt_of_le_of_ne h0' hr1⟩, ⟨h1, h1'⟩, ⟨by linarith [Real.pi_pos], h.ge⟩⟩,
      rfl⟩

/-! ### The seven boxes -/

/-- **`subclaim₀₁`**: `F(𝒟₀₁ ∖ cell two) ⊆ 𝒟₀₀ ∪ cell two` (`ψ' < π/3`, `θ₂' > 2π/3`). -/
private theorem box_01 : ∀ x ∈ boxSet 0 1, x ∉ cellTwoSet →
    poincareAngZero x ∈ cellTwoSet ∨
      ∃ k l : Fin 3, BoxLexLt k l 0 1 ∧ poincareAngZero x ∈ boxSet k l := by
  refine box_of (by simp) fun p hp hr hrot hx ↦ ?_
  have hpm : p 0 ∈ Icc 0 1 ∧ p 1 ∈ Icc 0 (Real.pi / 3) ∧ p 2 ∈ Icc 1.1 (Real.pi - 1.1) := by
    simpa [cellBox, basinA, basinB] using hp
  obtain ⟨⟨h0, h0'⟩, ⟨h1, h1'⟩, ⟨h2, h2'⟩⟩ := hpm
  have hpi := Real.pi_gt_three
  have hpi' := Real.pi_lt_d2
  have h11 : Real.pi / 3 < 1.1 := by norm_num; linarith
  have hcl1 : p ∈ closedBoxOne := ⟨⟨h0, h0'⟩, ⟨h1, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hroot : (cy₂ p ≤ 0 ∧ 0 ≤ cκ p ∧ (0 < cκ p ∨ cy₂ p < 0)) ∨
      (0 ≤ cy₂ p ∧ 0 ≤ cy₁ p ∧ 0 < cκ p) :=
    Or.inl ⟨(cy₂_neg hr (by linarith) (by linarith)).le,
      cκ_nonneg h0 h0' h1 (by linarith), Or.inr (cy₂_neg hr (by linarith) (by linarith))⟩
  have hs2 : 0 < Real.sin (p 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  rcases generic_image hcl1 hroot (Or.inl ⟨hr, hs2⟩) with h |
    ⟨τ, hτ, hτ0, hV1, -, w, hw, hcl, e0r, e0i, e1r, e1i, h2i, h2r⟩
  · exact Or.inl h
  right
  have hC := C₁_neg_of_three h0 h0' (three_psi h1 (by linarith))
    (three_theta (by linarith) (by linarith)) hτ hτ0
  obtain ⟨q, hq, hq0, hq1, -, hq2⟩ := image_psi_lt hw hcl e0r e0i e1r e1i h2i h2r hV1 hC
  have hs1 : 0 ≤ Real.sin (p 2 - p 1) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hC2 := C₂_neg_of_sin_nonneg h0 h0' hs1 hs2.le hτ
  have hθ := two_pi_div_three_lt_arg (w := w 1) (by rw [e1i]; exact hV1)
    (by rw [e1i, e1r]; exact hC2)
  refine ⟨0, 0, by simp [BoxLexLt], ⟨q, ?_, hq.symm⟩⟩
  rw [mem_cellBox_zero_zero]
  refine ⟨hq0, hq1, ⟨by rw [hq2]; norm_num; linarith, ?_⟩⟩
  rw [hq2]; exact Complex.arg_le_pi _

/-- **`subclaim₀₂`**: `F(𝒟₀₂ ∖ cell two) ⊆ 𝒟₀₀ ∪ 𝒟₀₁ ∪ cell two` (`ψ' < π/3`, `θ₂' ≥ 1.1`). -/
private theorem box_02 : ∀ x ∈ boxSet 0 2, x ∉ cellTwoSet →
    poincareAngZero x ∈ cellTwoSet ∨
      ∃ k l : Fin 3, BoxLexLt k l 0 2 ∧ poincareAngZero x ∈ boxSet k l := by
  refine box_of (by simp) fun p hp hr hrot hx ↦ ?_
  have hpm : p 0 ∈ Icc 0 1 ∧ p 1 ∈ Icc 0 (Real.pi / 3) ∧ p 2 ∈ Icc 0 1.1 := by
    simpa [cellBox, basinA, basinB] using hp
  obtain ⟨⟨h0, h0'⟩, ⟨h1, h1'⟩, ⟨h2, h2'⟩⟩ := hpm
  have hpi := Real.pi_gt_three
  have hpi' := Real.pi_lt_d2
  have h11 : Real.pi / 3 < 1.1 := by norm_num; linarith
  have hcl1 : p ∈ closedBoxOne := ⟨⟨h0, h0'⟩, ⟨h1, by linarith⟩, ⟨h2, by linarith⟩⟩
  -- off the rotated faces: `θ₂ > 0`, and `r₂ < 1`, `ψ > 0` over `θ₂ ≤ π/3`
  have hface : p 2 ≤ Real.pi / 3 → p 1 ≠ 0 ∧ p 0 ≠ 1 := fun h ↦
    ⟨fun h' ↦ hrot ⟨h, Or.inl h'⟩, fun h' ↦ hrot ⟨h, Or.inr h'⟩⟩
  have h2pos : 0 < p 2 := by
    rcases h2.lt_or_eq with h | h
    · exact h
    · obtain ⟨hψ, hr1⟩ := hface (by rw [← h]; positivity)
      exact theta_pos hr hr1 h0' (lt_of_le_of_ne h1 (Ne.symm hψ)) (by linarith) h2 hx
  have hroot : (cy₂ p ≤ 0 ∧ 0 ≤ cκ p ∧ (0 < cκ p ∨ cy₂ p < 0)) ∨
      (0 ≤ cy₂ p ∧ 0 ≤ cy₁ p ∧ 0 < cκ p) := by
    rcases le_or_gt (p 2) (Real.pi / 3) with h | h
    · obtain ⟨hψ, hr1⟩ := hface h
      exact Or.inr ⟨cy₂_nonneg h0 h2 h, cy₁_nonneg h0' (by linarith) (by linarith),
        cκ_pos hr (lt_of_le_of_ne h0' hr1) (lt_of_le_of_ne h1 (Ne.symm hψ)) (by linarith)⟩
    · exact Or.inl ⟨(cy₂_neg hr h (by linarith)).le, cκ_nonneg h0 h0' h1 (by linarith),
        Or.inr (cy₂_neg hr h (by linarith))⟩
  have hs2 : 0 < Real.sin (p 2) := Real.sin_pos_of_pos_of_lt_pi h2pos (by linarith)
  rcases generic_image hcl1 hroot (Or.inl ⟨hr, hs2⟩) with h |
    ⟨τ, hτ, hτ0, hV1, hY, w, hw, hcl, e0r, e0i, e1r, e1i, h2i, h2r⟩
  · exact Or.inl h
  right
  have hC := C₁_neg_of_three h0 h0' (three_psi h1 (by linarith))
    (three_theta h2 (by linarith)) hτ hτ0
  obtain ⟨q, hq, hq0, hq1, hq2', hq2⟩ := image_psi_lt hw hcl e0r e0i e1r e1i h2i h2r hV1 hC
  -- `θ₂' > 1.1`
  have hq3 : √3 < 1.7321 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hq3' : 1.732 < √3 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hcos2 : 9 / 20 < Real.cos (p 2) := by
    have := Real.cos_le_cos_of_nonneg_of_le_pi h2 (by linarith) h2'
    linarith [lt_cos_eleven_tenths]
  have hT2 : 0 ≤ (1 + √3 / 2) * Real.cos (p 2) - (5 / 2 - √3) * Real.sin (p 2) := by
    have := Real.sin_le_one (p 2)
    nlinarith
  have hcos1 : 9 / 20 < Real.cos (p 2 - p 1) := by
    rcases le_total 0 (p 2 - p 1) with h | h
    · have := Real.cos_le_cos_of_nonneg_of_le_pi h (by linarith) (by linarith : p 2 - p 1 ≤ 1.1)
      linarith [lt_cos_eleven_tenths]
    · rw [← Real.cos_neg]
      have := Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith)
        (by linarith : -(p 2 - p 1) ≤ Real.pi / 3)
      rw [Real.cos_pi_div_three] at this
      linarith
  have hT1 : 0 ≤ (1 + √3 / 2) * Real.cos (p 2 - p 1) + (√3 - 3 / 2) * Real.sin (p 2 - p 1) := by
    have := Real.neg_one_le_sin (p 2 - p 1)
    nlinarith
  have hT := twoU₁_sub_V₁_neg h0 h0' hT2 hT1 hτ hY
  have hθ := eleven_tenths_le_arg (w := w 1) (by rw [e1i]; exact hV1)
    (by rw [e1i, e1r]; exact hT)
  rcases le_total (Real.pi - 1.1) (q 2) with h | h
  · refine ⟨0, 0, by simp [BoxLexLt], ⟨q, ?_, hq.symm⟩⟩
    rw [mem_cellBox_zero_zero]
    exact ⟨hq0, hq1, ⟨h, hq2'.2⟩⟩
  · refine ⟨0, 1, by simp [BoxLexLt], ⟨q, ?_, hq.symm⟩⟩
    have : q 0 ∈ Icc 0 1 ∧ q 1 ∈ Icc 0 (Real.pi / 3) ∧ q 2 ∈ Icc 1.1 (Real.pi - 1.1) :=
      ⟨hq0, hq1, ⟨by rw [hq2]; exact hθ, h⟩⟩
    simpa [cellBox, basinA, basinB] using this

/-- `ψ' < π/3` sends the image to a box `𝒟_{0ℓ}`, which precedes every box `𝒟_{iℓ'}` with
`i ≥ 1`. -/
private theorem target_of_psi {i j : Fin 3} (hi : 0 < i) {p : Fin 3 → ℝ} {q : Fin 3 → ℝ}
    (hq : poincareAngZero (cellClass p) = cellClass q) (hq0 : q 0 ∈ Icc 0 1)
    (hq1 : q 1 ∈ Icc 0 (Real.pi / 3)) (hq2 : q 2 ∈ Icc 0 Real.pi) :
    ∃ k l : Fin 3, BoxLexLt k l i j ∧ poincareAngZero (cellClass p) ∈ boxSet k l := by
  obtain ⟨l, hl⟩ := exists_theta_index 0 hq0 (by simpa [basinA] using hq1) hq2
  exact ⟨0, l, Or.inl hi, ⟨q, hl, hq.symm⟩⟩

/-- **`subclaim_{1j}` and `subclaim₂₀` for `θ₂ ∈ [π - 1.1, π]`** (the boxes `𝒟₁₀`, `𝒟₂₀`):
`ψ' < π/3` by `C₁_neg_of_four`. -/
private theorem box_j0 {i : Fin 3} (hi : 0 < i) :
    ∀ x ∈ boxSet i 0, x ∉ cellTwoSet →
      poincareAngZero x ∈ cellTwoSet ∨
        ∃ k l : Fin 3, BoxLexLt k l i 0 ∧ poincareAngZero x ∈ boxSet k l := by
  refine box_of (by simp [hi.ne']) fun p hp hr hrot hx ↦ ?_
  have hpi := Real.pi_gt_three
  have hpi' := Real.pi_lt_d2
  have hpm : p 0 ∈ Icc 0 1 ∧ p 1 ∈ Icc (Real.pi / 3) Real.pi ∧
      p 2 ∈ Icc (Real.pi - 1.1) Real.pi := by
    have hb : p 0 ∈ Icc 0 1 ∧ p 1 ∈ Icc (basinA i.castSucc) (basinA i.succ) ∧
        p 2 ∈ Icc (Real.pi - 1.1) Real.pi := by simpa [cellBox, basinB] using hp
    refine ⟨hb.1, ⟨?_, ?_⟩, hb.2.2⟩
    · have := hb.2.1.1
      fin_cases i
      · simp at hi
      · simpa [basinA] using this
      · simp [basinA] at this ⊢; linarith
    · have := hb.2.1.2
      fin_cases i
      · simp at hi
      · simp [basinA] at this ⊢; linarith
      · simpa [basinA] using this
  obtain ⟨⟨h0, h0'⟩, ⟨h1, h1'⟩, ⟨h2, h2'⟩⟩ := hpm
  have h11 : Real.pi / 3 < 1.1 := by norm_num; linarith
  have hcl1 : p ∈ closedBoxOne := ⟨⟨h0, h0'⟩, ⟨by linarith, h1'⟩, ⟨by linarith, h2'⟩⟩
  have hθ3 : Real.pi / 3 < p 2 := by norm_num at h2 ⊢; linarith
  have hroot : (cy₂ p ≤ 0 ∧ 0 ≤ cκ p ∧ (0 < cκ p ∨ cy₂ p < 0)) ∨
      (0 ≤ cy₂ p ∧ 0 ≤ cy₁ p ∧ 0 < cκ p) :=
    Or.inl ⟨(cy₂_neg hr hθ3 h2').le, cκ_nonneg h0 h0' (by linarith) h1',
      Or.inr (cy₂_neg hr hθ3 h2')⟩
  have hB : (0 < p 0 ∧ 0 < Real.sin (p 2)) ∨ ∀ t, 0 < t → 0 ≤ imZ₃ p t := by
    rcases h2'.lt_or_eq with h | h
    · exact Or.inl ⟨hr, Real.sin_pos_of_pos_of_lt_pi (by linarith) h⟩
    · right
      intro t ht
      unfold imZ₃
      rw [h, Real.sin_pi, Real.sin_pi_sub]
      have := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith : 0 ≤ p 1) h1'
      have : 0 ≤ 1 - p 0 := by linarith
      positivity
  rcases generic_image hcl1 hroot hB with h |
    ⟨τ, hτ, hτ0, hV1, -, w, hw, hcl, e0r, e0i, e1r, e1i, h2i, h2r⟩
  · exact Or.inl h
  right
  have hθ₁lo : -1.1 ≤ p 2 - p 1 := by linarith
  have hθ₁hi : p 2 - p 1 ≤ 2 * Real.pi / 3 := by linarith
  have hc1 : -(1 / 2) ≤ Real.cos (p 2 - p 1) := by
    rcases le_total 0 (p 2 - p 1) with h | h
    · have := Real.cos_le_cos_of_nonneg_of_le_pi h (by linarith) hθ₁hi
      have e : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
        rw [show 2 * Real.pi / 3 = 2 / 3 * Real.pi by ring, cos_two_thirds_pi]; ring
      linarith
    · have := (cos_sin_bounds_of_mem_neg hθ₁lo h).1
      linarith
  have hneg : Real.sin (p 2 - p 1) < 0 →
      9 / 20 < Real.cos (p 2 - p 1) ∧ -(9 / 10) < Real.sin (p 2 - p 1) := by
    intro hs
    have : p 2 - p 1 < 0 := by
      by_contra hc
      push Not at hc
      have := Real.sin_nonneg_of_nonneg_of_le_pi hc (by linarith)
      linarith
    exact cos_sin_bounds_of_mem_neg hθ₁lo this.le
  have hC := C₁_neg_of_four h0 h0' (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) h2')
    (sqrt_three_mul_cos_sub_sin_le h2 h2') (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) h1')
    hc1 hneg hτ hτ0
  obtain ⟨q, hq, hq0, hq1, hq2, -⟩ := image_psi_lt hw hcl e0r e0i e1r e1i h2i h2r hV1 hC
  exact target_of_psi hi hq hq0 hq1 hq2

/-- **`subclaim₁₁` and `subclaim₁₂`** (`θ₂ ∈ [0, π - 1.1]`, `ψ ∈ [π/3, 2π/3]`): `ψ' < π/3` by
`C₁_neg_of_three`. -/
private theorem box_1j {j : Fin 3} (hj : 0 < j) :
    ∀ x ∈ boxSet 1 j, x ∉ cellTwoSet →
      poincareAngZero x ∈ cellTwoSet ∨
        ∃ k l : Fin 3, BoxLexLt k l 1 j ∧ poincareAngZero x ∈ boxSet k l := by
  refine box_of (by simp) fun p hp hr hrot hx ↦ ?_
  have hpi := Real.pi_gt_three
  have hpi' := Real.pi_lt_d2
  have hpm : p 0 ∈ Icc 0 1 ∧ p 1 ∈ Icc (Real.pi / 3) (2 * Real.pi / 3) ∧
      p 2 ∈ Icc 0 (Real.pi - 1.1) := by
    have hb : p 0 ∈ Icc 0 1 ∧ p 1 ∈ Icc (Real.pi / 3) (2 * Real.pi / 3) ∧
        p 2 ∈ Icc (basinB j.succ) (basinB j.castSucc) := by simpa [cellBox, basinA] using hp
    refine ⟨hb.1, hb.2.1, ⟨?_, ?_⟩⟩
    · have := hb.2.2.1
      fin_cases j
      · simp at hj
      · simp [basinB] at this ⊢; linarith
      · simpa [basinB] using this
    · have := hb.2.2.2
      fin_cases j
      · simp at hj
      · simpa [basinB] using this
      · simp [basinB] at this ⊢; linarith
  obtain ⟨⟨h0, h0'⟩, ⟨h1, h1'⟩, ⟨h2, h2'⟩⟩ := hpm
  have hcl1 : p ∈ closedBoxOne := ⟨⟨h0, h0'⟩, ⟨by linarith, by linarith⟩, ⟨h2, by linarith⟩⟩
  have hface : p 2 ≤ Real.pi / 3 → p 0 ≠ 1 := fun h h' ↦ hrot ⟨h, Or.inr h'⟩
  have h2pos : 0 < p 2 := by
    rcases h2.lt_or_eq with h | h
    · exact h
    · exact theta_pos hr (hface (by rw [← h]; positivity)) h0' (by linarith) (by linarith)
        h2 hx
  have hroot : (cy₂ p ≤ 0 ∧ 0 ≤ cκ p ∧ (0 < cκ p ∨ cy₂ p < 0)) ∨
      (0 ≤ cy₂ p ∧ 0 ≤ cy₁ p ∧ 0 < cκ p) := by
    rcases le_or_gt (p 2) (Real.pi / 3) with h | h
    · exact Or.inr ⟨cy₂_nonneg h0 h2 h, cy₁_nonneg h0' (by linarith) (by linarith),
        cκ_pos hr (lt_of_le_of_ne h0' (hface h)) (by linarith) (by linarith)⟩
    · exact Or.inl ⟨(cy₂_neg hr h (by linarith)).le,
        cκ_nonneg h0 h0' (by linarith) (by linarith),
        Or.inr (cy₂_neg hr h (by linarith))⟩
  have hs2 : 0 < Real.sin (p 2) := Real.sin_pos_of_pos_of_lt_pi h2pos (by linarith)
  rcases generic_image hcl1 hroot (Or.inl ⟨hr, hs2⟩) with h |
    ⟨τ, hτ, hτ0, hV1, -, w, hw, hcl, e0r, e0i, e1r, e1i, h2i, h2r⟩
  · exact Or.inl h
  right
  have hC := C₁_neg_of_three h0 h0' (three_psi (by linarith) h1')
    (three_theta h2 (by norm_num at h2' ⊢; linarith)) hτ hτ0
  obtain ⟨q, hq, hq0, hq1, hq2, -⟩ := image_psi_lt hw hcl e0r e0i e1r e1i h2i h2r hV1 hC
  exact target_of_psi (by simp) hq hq0 hq1 hq2

/-- **`subclaim₂₁`**: `F(𝒟₂₁ ∖ cell two)` lies in the second cell, in a box `𝒟_{kℓ}` with
`k ≤ 1`, or in `𝒟₂₀`: `Im w₁ = V₀ > 0` (`y₁ ≥ 0` on `𝒟₂₁`), so `ψ' = θ₂' - θ₁' < θ₂'`. -/
private theorem box_21 : ∀ x ∈ boxSet 2 1, x ∉ cellTwoSet →
    poincareAngZero x ∈ cellTwoSet ∨
      ∃ k l : Fin 3, BoxLexLt k l 2 1 ∧ poincareAngZero x ∈ boxSet k l := by
  refine box_of (by simp) fun p hp hr hrot hx ↦ ?_
  have hpm : p 0 ∈ Icc 0 1 ∧ p 1 ∈ Icc (2 * Real.pi / 3) Real.pi ∧
      p 2 ∈ Icc 1.1 (Real.pi - 1.1) := by
    simpa [cellBox, basinA, basinB] using hp
  obtain ⟨⟨h0, h0'⟩, ⟨h1, h1'⟩, ⟨h2, h2'⟩⟩ := hpm
  have hpi := Real.pi_gt_three
  have hpi' := Real.pi_lt_d2
  have h11 : Real.pi / 3 < 1.1 := by norm_num; linarith
  have hcl1 : p ∈ closedBoxOne := ⟨⟨h0, h0'⟩, ⟨by linarith, h1'⟩, ⟨by linarith, by linarith⟩⟩
  have hroot : (cy₂ p ≤ 0 ∧ 0 ≤ cκ p ∧ (0 < cκ p ∨ cy₂ p < 0)) ∨
      (0 ≤ cy₂ p ∧ 0 ≤ cy₁ p ∧ 0 < cκ p) :=
    Or.inl ⟨(cy₂_neg hr (by linarith) (by linarith)).le,
      cκ_nonneg h0 h0' (by linarith) h1', Or.inr (cy₂_neg hr (by linarith) (by linarith))⟩
  have hs2 : 0 < Real.sin (p 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  rcases generic_image hcl1 hroot (Or.inl ⟨hr, hs2⟩) with h |
    ⟨τ, hτ, hτ0, hV1, -, w, hw, hcl, e0r, e0i, e1r, e1i, h2i, h2r⟩
  · exact Or.inl h
  right
  -- `Im w₁ = y₁ + τ/2 > 0`
  have hy1 := cy₁_nonneg h0' (by linarith) (by linarith)
  have hV0 : 0 < (w 0).im := by rw [e0i]; unfold V₀; linarith
  have hw0 : w 0 ≠ 0 := by rintro h; rw [h] at hV0; simp at hV0
  obtain ⟨hcc, c0, c1, c1e, c2, harg⟩ := image_coords hw h2i h2r hw0 (by rw [e1i]; exact hV1)
  have hsub := toIcoMod_eq_sub_of_im_pos hV0 (by rw [e1i]; exact hV1) (by rw [← c1e]; exact c1.2)
  have ha0 := (arg_mem_Ioo_of_im_pos hV0).1
  -- `ψ' = θ₂' - θ₁' < θ₂'`
  have hψθ : cellCoords w 1 < cellCoords w 2 := by
    rw [c1e, hsub, c2]; linarith
  have hcl' := hcl.trans hcc
  rcases le_total (cellCoords w 1) (2 * Real.pi / 3) with h | h
  · rcases le_total (cellCoords w 1) (Real.pi / 3) with h' | h'
    · obtain ⟨l, hl⟩ := exists_theta_index 0 c0 (by simpa [basinA] using ⟨c1.1, h'⟩)
        ⟨by rw [c2]; exact harg.1.le, by rw [c2]; exact harg.2.le⟩
      exact ⟨0, l, by simp [BoxLexLt], ⟨_, hl, hcl'.symm⟩⟩
    · obtain ⟨l, hl⟩ := exists_theta_index 1 c0 (by simpa [basinA] using ⟨h', h⟩)
        ⟨by rw [c2]; exact harg.1.le, by rw [c2]; exact harg.2.le⟩
      exact ⟨1, l, by simp [BoxLexLt], ⟨_, hl, hcl'.symm⟩⟩
  · refine ⟨2, 0, by simp [BoxLexLt], ⟨_, ?_, hcl'.symm⟩⟩
    have : cellCoords w 0 ∈ Icc 0 1 ∧ cellCoords w 1 ∈ Icc (2 * Real.pi / 3) Real.pi ∧
        cellCoords w 2 ∈ Icc (Real.pi - 1.1) Real.pi :=
      ⟨c0, ⟨h, c1.2⟩, ⟨by norm_num; linarith, by rw [c2]; exact harg.2.le⟩⟩
    simpa [cellBox, basinA, basinB] using this

end SmoothedPolygons.TriFuller.BoxAnalytic

namespace SmoothedPolygons.TriFuller

open BoxAnalytic

/-- **Table 16.1, the subclaims `subclaim_{ij}` with the row `𝒟₄`** (`tab:diag`, Figures
16.3–16.4): `BoxSubclaims` (`SmoothedPolygons/Ch16/BasinHypotheses.lean`) holds, without computer
assistance: for `(i, j) ∉ {(0, 0), (2, 2)}`, a point of `𝒟_{ij}` outside the second big cell is
mapped into the second big cell or into a box `𝒟_{kℓ}`, `(k, ℓ) ≺ (i, j)`.

Departure from the paper: the book reads the subclaims `subclaim_{ij}` off computer plots by the
boundary method (Figures 16.3–16.4, TeX 12680–12726); the formalization proves them analytically
(`SmoothedPolygons/Ch16/BoxSubclaims.lean`): the switch as the root of an explicit cubic
(`exists_root_of_signs`), the alternative switch to `ζ²` from the sign of `Im z₃`
(`image_dichotomy`), the image's angle `ψ' < π/3` from exact identities with sign-definite terms
(`C₁_neg_of_three`, `C₁_neg_of_four`), `θ₂'` from `C₂_neg_of_sin_nonneg` and `twoU₁_sub_V₁_neg`,
and on `𝒟₂₁` from the sign of `Im w₁` alone; the faces where the first control is not `ζ` are
classes of `𝒟₀₀`. -/
theorem boxSubclaims : BoxSubclaims := by
  intro i j h00 h22
  fin_cases i <;> fin_cases j
  · exact absurd rfl h00
  · exact box_01
  · exact box_02
  · exact box_j0 (by simp)
  · exact box_1j (by simp)
  · exact box_1j (by simp)
  · exact box_j0 (by simp)
  · exact box_21
  · exact absurd rfl h22

end SmoothedPolygons.TriFuller
