module

public import SmoothedPolygons.Ch16.DOutImages
public import SmoothedPolygons.Ch16.DOutDerivativeBounds
public import Basic.Analysis.Calculus.MeanValueImplicit
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# `DOutContracts` without computer assistance

`theorem dOutContracts : DOutContracts` (`SmoothedPolygons/Ch16/BasinHypotheses.lean`), with the
witnesses `B = Icc boxLo boxHi` (`SmoothedPolygons/Ch16/DOutImages.lean`), `N = 2`, `κ = 3/4` and
`g p = cellCoords (ζ F(z))`:

* `F(𝒟₀₀) ⊆ 𝒟₀₀`: `mapsTo_boxSet_zero_zero` (`SmoothedPolygons/Ch16/DOutInvariant.lean`);
* `F²(𝒟₀₀) ⊆ B`: `F(𝒟₀₀) ⊆ D₁` and `F(D₁) ⊆ B` (`image_mem_regionD1`, `image_mem_box`);
* `g(B) ⊆ B`: `B ⊆ D₁`;
* `g` is `3/4`-Lipschitz on `B` (`lipschitzOnWith_gmap`): with `σ = 1/τ` the root of
  `nF = √3 κ σ³ - y₁ σ/2 - y₂ σ² - 1/12` in `[0.185, 0.221]` (`sig_spec`), the coordinates of
  `g p` are `θ₂' = arctan (v₁/u₁) + π`, `ψ' = arctan (v₁/u₁) - arctan (v₀/u₀)` and
  `log H(r₂') = log (u₁² + v₁²) - 2 log (u₀² + v₀²)`, `H(r) = (r/(1 - r)²)²`, at `σ(p)`
  (`gmap_spec`, `log_MM`): explicit functions of `(p, σ)` (`GG2`, `GG1`, `LM`). The implicit mean
  value theorem (`abs_sub_le_sum_of_implicit`, no differentiability of `σ` needed), with the
  partial derivatives of these functions and of `nF` bounded on `B × [0.185, 0.221]` by the
  argument of `SmoothedPolygons/Ch16/DOutDerivativeBounds.lean` (ranges of a few quantities, the
  logarithmic derivatives of `w₁/τ` and `w₂/τ²`, and the signs of their angular parts), gives
  entrywise bounds with row sums `≤ 0.699` (`θ₂'` and `ψ'`) and, for `r₂'` through
  `|r - r'| ≤ (1/10) |log H(r) - log H(r')|` (`abs_sub_le_radius`), `≤ 0.594`.

Departure from the paper: the book only states that the forward iterates of `𝒟_out` shrink toward
`q_out` (TeX 12592–12607, unproved; REPORT.md, E78); the contraction hypothesis that repairs this is
proved here analytically: the derivative of the map is bounded by explicit estimates on a single
box, after the normalisation `τ = 1` that makes the image an affine function of small quantities.
This replaced an earlier kernel-checked interval certificate (54 boxes, since removed), the
unproved `F²(𝒟₀₀) ⊆ B`, and a generated interval chain for the derivative bounds.
-/

@[expose] public section

namespace SmoothedPolygons.TriFuller.DOutAnalytic

open Set

/-! ### The trigonometric functions on `B` -/

/-- `cos (arctan (a/b)) = b/c`, `sin (arctan (a/b)) = a/c` when `a² + b² = c²`. -/
theorem arctan_pyth {a b c : ℝ} (hb : 0 < b) (hc : 0 < c) (h : a ^ 2 + b ^ 2 = c ^ 2) :
    Real.cos (Real.arctan (a / b)) = b / c ∧ Real.sin (Real.arctan (a / b)) = a / c := by
  have e : √(1 + (a / b) ^ 2) = c / b := by
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by positivity)]
    field_simp
    linarith
  rw [Real.cos_arctan, Real.sin_arctan, e]
  constructor <;> field_simp

theorem cos_add_two_thirds_pi_eq (x : ℝ) :
    Real.cos (x + 2 / 3 * Real.pi) = Real.sin (x - 5 * Real.pi / 6) := by
  rw [show x + 2 / 3 * Real.pi = (x - 5 * Real.pi / 6 + Real.pi) + Real.pi / 2 by ring,
    Real.cos_add_pi_div_two, Real.sin_add_pi]
  ring

theorem sin_add_two_thirds_pi_eq (x : ℝ) :
    Real.sin (x + 2 / 3 * Real.pi) = -Real.cos (x - 5 * Real.pi / 6) := by
  rw [show x + 2 / 3 * Real.pi = (x - 5 * Real.pi / 6 + Real.pi) + Real.pi / 2 by ring,
    Real.sin_add_pi_div_two, Real.cos_add_pi]

/-- The values at the corners of `B`. -/
theorem box_corner_values :
    (Real.cos (Real.arctan (39 / 80)) = 80 / 89 ∧ Real.sin (Real.arctan (39 / 80)) = 39 / 89) ∧
    (Real.cos (Real.arctan (15 / 112)) = 112 / 113 ∧
      Real.sin (Real.arctan (15 / 112)) = 15 / 113) ∧
    (Real.cos (Real.arctan (20 / 99)) = 99 / 101 ∧ Real.sin (Real.arctan (20 / 99)) = 20 / 101) ∧
    (Real.cos (Real.arctan (25 / 312)) = 312 / 313 ∧
      Real.sin (Real.arctan (25 / 312)) = 25 / 313) := by
  refine ⟨arctan_pyth (by norm_num) (by norm_num) (by norm_num),
    arctan_pyth (by norm_num) (by norm_num) (by norm_num),
    arctan_pyth (by norm_num) (by norm_num) (by norm_num),
    arctan_pyth (by norm_num) (by norm_num) (by norm_num)⟩

/-- **The trigonometric intervals on `B`**: `r₂`, `cos φ₁`, `sin φ₁`, `cos φ₂`, `sin φ₂`, `sin ψ`,
`cos ψ` (`φ₁ = θ₂ - ψ + 2π/3`, `φ₂ = θ₂ + 2π/3`). -/
theorem box_trig {p : Fin 3 → ℝ} (hp : p ∈ Icc boxLo boxHi) :
    p 0 ∈ Icc (11 / 50 : ℝ) (3 / 10) ∧
    Real.cos (p 2 - p 1 + 2 / 3 * Real.pi) ∈ Icc (-0.129 : ℝ) 0.3056 ∧
    Real.sin (p 2 - p 1 + 2 / 3 * Real.pi) ∈ Icc (-1 : ℝ) (-0.952) ∧
    Real.cos (p 2 + 2 / 3 * Real.pi) ∈ Icc (0.0699 : ℝ) 0.3807 ∧
    Real.sin (p 2 + 2 / 3 * Real.pi) ∈ Icc (-0.9976 : ℝ) (-0.9247) ∧
    Real.sin (p 1) ∈ Icc (25 / 313 : ℝ) (20 / 101) ∧
    Real.cos (p 1) ∈ Icc (99 / 101 : ℝ) (312 / 313) := by
  obtain ⟨hr, ⟨a1, b1⟩, ⟨a2, b2⟩⟩ := mem_box_iff.1 hp
  obtain ⟨⟨cX, sX⟩, ⟨cX', sX'⟩, ⟨cY, sY⟩, ⟨cY', sY'⟩⟩ := box_corner_values
  have hpi := Real.pi_gt_three
  have hpi' := Real.pi_lt_d2
  obtain ⟨q1, q2⟩ := sqrt_three_bounds
  set X := Real.arctan (39 / 80)
  set X' := Real.arctan (15 / 112)
  set Y := Real.arctan (20 / 99)
  set Y' := Real.arctan (25 / 312)
  have hX : X < Real.pi / 6 := arctan_bounds.2.2.1
  have hX0 : 0 < X := Real.arctan_pos.2 (by norm_num)
  have hX'0 : 0 < X' := Real.arctan_pos.2 (by norm_num)
  have hY0 : 0 < Y := Real.arctan_pos.2 (by norm_num)
  have hY'0 : 0 < Y' := Real.arctan_pos.2 (by norm_num)
  have hXX' : X' ≤ X := Real.arctan_le_arctan_iff.2 (by norm_num)
  have hYY' : Y' ≤ Y := Real.arctan_le_arctan_iff.2 (by norm_num)
  have hY : Y < 1 / 4 := (Real.arctan_lt_arctan_iff.2 (by norm_num : (20 : ℝ) / 99 < 1 / 4)).trans
    arctan_quarter_lt
  have hc6 := Real.cos_pi_div_six
  have hs6 := Real.sin_pi_div_six
  refine ⟨hr, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · -- `cos φ₁ = sin (θ₁ - 5π/6)`, increasing
    rw [cos_add_two_thirds_pi_eq]
    have h := Real.sin_le_sin_of_le_of_le_pi_div_two (x := Real.pi / 6 - (X + Y))
      (y := p 2 - p 1 - 5 * Real.pi / 6) (by linarith) (by linarith) (by linarith)
    have e : Real.sin (Real.pi / 6 - (X + Y)) = (7140 - 5461 * √3) / 17978 := by
      rw [Real.sin_sub, Real.cos_add, Real.sin_add, hc6, hs6, cX, sX, cY, sY]; ring
    rw [e] at h
    have : (-0.129 : ℝ) ≤ (7140 - 5461 * √3) / 17978 := by
      rw [le_div_iff₀ (by norm_num)]; linarith
    linarith
  · rw [cos_add_two_thirds_pi_eq]
    have h := Real.sin_le_sin_of_le_of_le_pi_div_two (x := p 2 - p 1 - 5 * Real.pi / 6)
      (y := Real.pi / 6 - (X' + Y')) (by linarith) (by linarith) (by linarith)
    have e : Real.sin (Real.pi / 6 - (X' + Y')) = (34569 - 7480 * √3) / 70738 := by
      rw [Real.sin_sub, Real.cos_add, Real.sin_add, hc6, hs6, cX', sX', cY', sY']; ring
    rw [e] at h
    have : (34569 - 7480 * √3) / 70738 ≤ (0.3056 : ℝ) := by
      rw [div_le_iff₀ (by norm_num)]; linarith
    linarith
  · rw [sin_add_two_thirds_pi_eq]
    linarith [Real.cos_le_one (p 2 - p 1 - 5 * Real.pi / 6)]
  · -- `sin φ₁ = -cos (θ₁ - 5π/6)`, `|θ₁ - 5π/6| ≤ π/6 - X' - Y'`
    rw [sin_add_two_thirds_pi_eq]
    have e1 : X < 39 / 80 := Real.arctan_lt_self (by norm_num)
    have e2 : X' < 15 / 112 := Real.arctan_lt_self (by norm_num)
    have e3 : Y < 20 / 99 := Real.arctan_lt_self (by norm_num)
    have e4 : Y' < 25 / 312 := Real.arctan_lt_self (by norm_num)
    have habs : |p 2 - p 1 - 5 * Real.pi / 6| ≤ Real.pi / 6 - (X' + Y') := by
      rw [abs_le]; constructor <;> linarith
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (p 2 - p 1 - 5 * Real.pi / 6))
      (by linarith) habs
    rw [Real.cos_abs] at h
    have e : Real.cos (Real.pi / 6 - (X' + Y')) = (34569 * √3 + 7480) / 70738 := by
      rw [Real.cos_sub, Real.cos_add, Real.sin_add, hc6, hs6, cX', sX', cY', sY']; ring
    rw [e] at h
    have : (0.952 : ℝ) ≤ (34569 * √3 + 7480) / 70738 := by
      rw [le_div_iff₀ (by norm_num)]; linarith
    linarith
  · -- `cos φ₂ = sin (θ₂ - 5π/6)`
    rw [cos_add_two_thirds_pi_eq]
    have h := Real.sin_le_sin_of_le_of_le_pi_div_two (x := Real.pi / 6 - X)
      (y := p 2 - 5 * Real.pi / 6) (by linarith) (by linarith) (by linarith)
    have e : Real.sin (Real.pi / 6 - X) = (80 - 39 * √3) / 178 := by
      rw [Real.sin_sub, hc6, hs6, cX, sX]; ring
    rw [e] at h
    have : (0.0699 : ℝ) ≤ (80 - 39 * √3) / 178 := by
      rw [le_div_iff₀ (by norm_num)]; linarith
    linarith
  · rw [cos_add_two_thirds_pi_eq]
    have h := Real.sin_le_sin_of_le_of_le_pi_div_two (x := p 2 - 5 * Real.pi / 6)
      (y := Real.pi / 6 - X') (by linarith) (by linarith) (by linarith)
    have e : Real.sin (Real.pi / 6 - X') = (112 - 15 * √3) / 226 := by
      rw [Real.sin_sub, hc6, hs6, cX', sX']; ring
    rw [e] at h
    have : (112 - 15 * √3) / 226 ≤ (0.3807 : ℝ) := by
      rw [div_le_iff₀ (by norm_num)]; linarith
    linarith
  · -- `sin φ₂ = -cos (θ₂ - 5π/6)`, increasing
    rw [sin_add_two_thirds_pi_eq]
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := Real.pi / 6 - X)
      (y := p 2 - 5 * Real.pi / 6) (by linarith) (by linarith) (by linarith)
    have e : Real.cos (Real.pi / 6 - X) = (80 * √3 + 39) / 178 := by
      rw [Real.cos_sub, hc6, hs6, cX, sX]; ring
    rw [e] at h
    have : (80 * √3 + 39) / 178 ≤ (0.9976 : ℝ) := by
      rw [div_le_iff₀ (by norm_num)]; linarith
    linarith
  · rw [sin_add_two_thirds_pi_eq]
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := p 2 - 5 * Real.pi / 6)
      (y := Real.pi / 6 - X') (by linarith) (by linarith) (by linarith)
    have e : Real.cos (Real.pi / 6 - X') = (112 * √3 + 15) / 226 := by
      rw [Real.cos_sub, hc6, hs6, cX', sX']; ring
    rw [e] at h
    have : (0.9247 : ℝ) ≤ (112 * √3 + 15) / 226 := by
      rw [le_div_iff₀ (by norm_num)]; linarith
    linarith
  · have h := Real.sin_le_sin_of_le_of_le_pi_div_two (x := Y') (y := p 1) (by linarith)
      (by linarith) a1
    rw [sY'] at h; exact h
  · have h := Real.sin_le_sin_of_le_of_le_pi_div_two (x := p 1) (y := Y) (by linarith)
      (by linarith) b1
    rw [sY] at h; exact h
  · have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := p 1) (y := Y) (by linarith)
      (by linarith) b1
    rw [cY] at h; exact h
  · have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := Y') (y := p 1) (by linarith)
      (by linarith) a1
    rw [cY'] at h; exact h

/-! ### Derivatives along the coordinate lines -/

/-- The partial derivatives of `x₁ = r₁ cos φ₁` in the directions `r₂, ψ, θ₂`. -/
noncomputable def dcx₁ (w : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![-Real.cos (w 2 - w 1 + 2 / 3 * Real.pi), cy₁ w, -cy₁ w]

/-- The partial derivatives of `y₁ = r₁ sin φ₁`. -/
noncomputable def dcy₁ (w : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![-Real.sin (w 2 - w 1 + 2 / 3 * Real.pi), -cx₁ w, cx₁ w]

/-- The partial derivatives of `x₂ = r₂ cos φ₂`. -/
noncomputable def dcx₂ (w : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![Real.cos (w 2 + 2 / 3 * Real.pi), 0, -cy₂ w]

/-- The partial derivatives of `y₂ = r₂ sin φ₂`. -/
noncomputable def dcy₂ (w : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![Real.sin (w 2 + 2 / 3 * Real.pi), 0, cx₂ w]

/-- The partial derivatives of `κ = r₁ r₂ sin ψ`. -/
noncomputable def dcκ (w : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![(1 - 2 * w 0) * Real.sin (w 1), (1 - w 0) * w 0 * Real.cos (w 1), 0]

theorem update_zero (w : Fin 3 → ℝ) (s : ℝ) :
    Function.update w 0 s 0 = s ∧ Function.update w 0 s 1 = w 1 ∧
      Function.update w 0 s 2 = w 2 := by
  simp [Function.update]

theorem update_one (w : Fin 3 → ℝ) (s : ℝ) :
    Function.update w 1 s 0 = w 0 ∧ Function.update w 1 s 1 = s ∧
      Function.update w 1 s 2 = w 2 := by
  simp [Function.update]

theorem update_two (w : Fin 3 → ℝ) (s : ℝ) :
    Function.update w 2 s 0 = w 0 ∧ Function.update w 2 s 1 = w 1 ∧
      Function.update w 2 s 2 = s := by
  simp [Function.update]

/-- `s ↦ (a - s) + c` and its relatives along a line. -/
theorem hasDerivAt_angle_lines (x a : ℝ) :
    HasDerivAt (fun s ↦ a - s + 2 / 3 * Real.pi) (-1) x ∧
      HasDerivAt (fun s ↦ s - a + 2 / 3 * Real.pi) 1 x ∧
      HasDerivAt (fun s ↦ s + 2 / 3 * Real.pi) 1 x := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using ((hasDerivAt_id x).const_sub a).add_const (2 / 3 * Real.pi)
  · simpa using ((hasDerivAt_id x).sub_const a).add_const (2 / 3 * Real.pi)
  · simpa using (hasDerivAt_id x).add_const (2 / 3 * Real.pi)

theorem hasDerivAt_cx₁ (w : Fin 3 → ℝ) (j : Fin 3) :
    HasDerivAt (fun s ↦ cx₁ (Function.update w j s)) (dcx₁ w j) (w j) := by
  fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, cx₁, update_zero, dcx₁, Matrix.cons_val_zero]
    exact (((hasDerivAt_id' (w 0)).const_sub 1).mul_const
      (Real.cos (w 2 - w 1 + 2 / 3 * Real.pi))).congr_deriv (by ring)
  · simp only [Fin.mk_one, Fin.isValue, cx₁, update_one, dcx₁, Matrix.cons_val_one,
      Matrix.cons_val_zero, cy₁]
    convert ((hasDerivAt_angle_lines (w 1) (w 2)).1.cos).const_mul (1 - w 0) using 1; ring
  · simp only [Fin.reduceFinMk, Fin.isValue, cx₁, update_two, dcx₁, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons, cy₁]
    convert ((hasDerivAt_angle_lines (w 2) (w 1)).2.1.cos).const_mul (1 - w 0) using 1; ring

theorem hasDerivAt_cy₁ (w : Fin 3 → ℝ) (j : Fin 3) :
    HasDerivAt (fun s ↦ cy₁ (Function.update w j s)) (dcy₁ w j) (w j) := by
  fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, cy₁, update_zero, dcy₁, Matrix.cons_val_zero]
    exact (((hasDerivAt_id' (w 0)).const_sub 1).mul_const
      (Real.sin (w 2 - w 1 + 2 / 3 * Real.pi))).congr_deriv (by ring)
  · simp only [Fin.mk_one, Fin.isValue, cy₁, update_one, dcy₁, Matrix.cons_val_one,
      Matrix.cons_val_zero, cx₁]
    convert ((hasDerivAt_angle_lines (w 1) (w 2)).1.sin).const_mul (1 - w 0) using 1; ring
  · simp only [Fin.reduceFinMk, Fin.isValue, cy₁, update_two, dcy₁, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons, cx₁]
    convert ((hasDerivAt_angle_lines (w 2) (w 1)).2.1.sin).const_mul (1 - w 0) using 1; ring

theorem hasDerivAt_cx₂ (w : Fin 3 → ℝ) (j : Fin 3) :
    HasDerivAt (fun s ↦ cx₂ (Function.update w j s)) (dcx₂ w j) (w j) := by
  fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, cx₂, update_zero, dcx₂, Matrix.cons_val_zero]
    exact ((hasDerivAt_id' (w 0)).mul_const (Real.cos (w 2 + 2 / 3 * Real.pi))).congr_deriv
      (by ring)
  · simp only [Fin.mk_one, Fin.isValue, cx₂, update_one, dcx₂, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    exact hasDerivAt_const _ _
  · simp only [Fin.reduceFinMk, Fin.isValue, cx₂, update_two, dcx₂, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons, cy₂]
    convert ((hasDerivAt_angle_lines (w 2) 0).2.2.cos).const_mul (w 0) using 1; ring

theorem hasDerivAt_cy₂ (w : Fin 3 → ℝ) (j : Fin 3) :
    HasDerivAt (fun s ↦ cy₂ (Function.update w j s)) (dcy₂ w j) (w j) := by
  fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, cy₂, update_zero, dcy₂, Matrix.cons_val_zero]
    exact ((hasDerivAt_id' (w 0)).mul_const (Real.sin (w 2 + 2 / 3 * Real.pi))).congr_deriv
      (by ring)
  · simp only [Fin.mk_one, Fin.isValue, cy₂, update_one, dcy₂, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    exact hasDerivAt_const _ _
  · simp only [Fin.reduceFinMk, Fin.isValue, cy₂, update_two, dcy₂, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons, cx₂]
    convert ((hasDerivAt_angle_lines (w 2) 0).2.2.sin).const_mul (w 0) using 1; ring

theorem hasDerivAt_cκ (w : Fin 3 → ℝ) (j : Fin 3) :
    HasDerivAt (fun s ↦ cκ (Function.update w j s)) (dcκ w j) (w j) := by
  fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, cκ, update_zero, dcκ, Matrix.cons_val_zero]
    exact ((((hasDerivAt_id' (w 0)).const_sub 1).mul (hasDerivAt_id' (w 0))).mul_const
      (Real.sin (w 1))).congr_deriv (by ring)
  · simp only [Fin.mk_one, Fin.isValue, cκ, update_one, dcκ, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    convert (Real.hasDerivAt_sin (w 1)).const_mul ((1 - w 0) * w 0) using 1
  · simp only [Fin.reduceFinMk, Fin.isValue, cκ, update_two, dcκ, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons]
    exact hasDerivAt_const _ _

/-! ### The functions of `(p, σ)` and their derivatives -/

/-- `θ₂' - π = arctan (v₁/u₁)` as a function of `(p, σ)`. -/
noncomputable def GG2 (p : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  Real.arctan (nv1 (cy₂ p) (cκ p) t / nu1 (cx₁ p) (cx₂ p) t)

/-- `arctan (v₀/u₀)` as a function of `(p, σ)`. -/
noncomputable def GA0 (p : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  Real.arctan (nv0 (cy₂ p) (cκ p) t / nu0 (cx₁ p) t)

/-- `ψ' = arctan (v₁/u₁) - arctan (v₀/u₀)` as a function of `(p, σ)`. -/
noncomputable def GG1 (p : Fin 3 → ℝ) (t : ℝ) : ℝ := GG2 p t - GA0 p t

/-- `(r₂'/(1 - r₂')²)² = (u₁² + v₁²)/(u₀² + v₀²)²` as a function of `(p, σ)`. -/
noncomputable def MM (p : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  (nu1 (cx₁ p) (cx₂ p) t ^ 2 + nv1 (cy₂ p) (cκ p) t ^ 2) /
    (nu0 (cx₁ p) t ^ 2 + nv0 (cy₂ p) (cκ p) t ^ 2) ^ 2

/-- The root equation `nF = 0` of `σ = 1/τ`, as a function of `(p, σ)`. -/
noncomputable def FF (p : Fin 3 → ℝ) (t : ℝ) : ℝ := nF (cy₁ p) (cy₂ p) (cκ p) t

/-- `log H(r₂') = log (u₁² + v₁²) - 2 log (u₀² + v₀²)` as a function of `(p, σ)`
(`H(r) = (r/(1 - r)²)²`; `log_MM`). -/
noncomputable def LM (p : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  Real.log (nu1 (cx₁ p) (cx₂ p) t ^ 2 + nv1 (cy₂ p) (cκ p) t ^ 2) -
    2 * Real.log (nu0 (cx₁ p) t ^ 2 + nv0 (cy₂ p) (cκ p) t ^ 2)

/-- `log MM = LM` where `|a|²` and `|b|²` are positive. -/
theorem log_MM {p : Fin 3 → ℝ} {t : ℝ} (h0 : 0 < nu0 (cx₁ p) t ^ 2 + nv0 (cy₂ p) (cκ p) t ^ 2)
    (h1 : 0 < nu1 (cx₁ p) (cx₂ p) t ^ 2 + nv1 (cy₂ p) (cκ p) t ^ 2) :
    Real.log (MM p t) = LM p t := by
  unfold MM LM
  rw [Real.log_div h1.ne' (pow_ne_zero 2 h0.ne'), Real.log_pow]
  push_cast
  ring

theorem hasDerivAt_arctan_div {f g : ℝ → ℝ} {f' g' x : ℝ} (hf : HasDerivAt f f' x)
    (hg : HasDerivAt g g' x) (hg0 : g x ≠ 0) :
    HasDerivAt (fun s ↦ Real.arctan (f s / g s)) (angD (g x) (f x) g' f') x := by
  refine ((hf.div hg hg0).arctan).congr_deriv ?_
  unfold angD
  simp only [Pi.div_apply]
  have : g x ^ 2 + f x ^ 2 ≠ 0 := by positivity
  field_simp

/-- `s ↦ log (u² + v²)` has derivative `2 Re (δ/z) = 2 (u du + v dv)/(u² + v²)`. -/
theorem hasDerivAt_log_normSq {u v : ℝ → ℝ} {du dv x : ℝ} (hu : HasDerivAt u du x)
    (hv : HasDerivAt v dv x) (hn : u x ^ 2 + v x ^ 2 ≠ 0) :
    HasDerivAt (fun s ↦ Real.log (u s ^ 2 + v s ^ 2)) (2 * radD (u x) (v x) du dv) x := by
  refine (((hu.pow 2).add (hv.pow 2)).log hn).congr_deriv ?_
  unfold radD
  simp only [Pi.add_apply, Pi.pow_apply, Nat.cast_ofNat]
  field_simp
  ring

/-- The normalized coordinates along a coordinate line, at fixed `σ`. -/
theorem hasDerivAt_uv_dir (w : Fin 3 → ℝ) (j : Fin 3) (t : ℝ) :
    HasDerivAt (fun s ↦ nu0 (cx₁ (Function.update w j s)) t) (dcx₁ w j * t) (w j) ∧
    HasDerivAt (fun s ↦ nv0 (cy₂ (Function.update w j s)) (cκ (Function.update w j s)) t)
      (2 * √3 * dcκ w j * t ^ 3 - 2 * dcy₂ w j * t ^ 2) (w j) ∧
    HasDerivAt (fun s ↦ nu1 (cx₁ (Function.update w j s)) (cx₂ (Function.update w j s)) t)
      (dcx₁ w j * t + dcx₂ w j * t ^ 2) (w j) ∧
    HasDerivAt (fun s ↦ nv1 (cy₂ (Function.update w j s)) (cκ (Function.update w j s)) t)
      (2 * √3 * dcκ w j * t ^ 3 - dcy₂ w j * t ^ 2) (w j) ∧
    HasDerivAt (fun s ↦ nF (cy₁ (Function.update w j s)) (cy₂ (Function.update w j s))
      (cκ (Function.update w j s)) t)
      (√3 * dcκ w j * t ^ 3 - dcy₁ w j * t / 2 - dcy₂ w j * t ^ 2) (w j) := by
  have hx1 := hasDerivAt_cx₁ w j
  have hy1 := hasDerivAt_cy₁ w j
  have hx2 := hasDerivAt_cx₂ w j
  have hy2 := hasDerivAt_cy₂ w j
  have hk := hasDerivAt_cκ w j
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (hx1.mul_const t).sub_const _
  · exact ((((hy2.const_mul 2).mul_const (t ^ 2)).const_sub (1 / 3)).add
      ((hk.const_mul (2 * √3)).mul_const (t ^ 3))).congr_deriv (by ring)
  · exact ((hx1.mul_const t).add (hx2.mul_const (t ^ 2))).sub_const _
  · exact (((hy2.mul_const (t ^ 2)).const_sub (1 / 12)).add
      ((hk.const_mul (2 * √3)).mul_const (t ^ 3))).congr_deriv (by ring)
  · exact (((((hk.const_mul √3).mul_const (t ^ 3)).sub ((hy1.mul_const t).div_const 2)).sub
      (hy2.mul_const (t ^ 2))).sub_const (1 / 12)).congr_deriv (by ring)

/-- The normalized coordinates in the time variable `σ`, at fixed `p`. -/
theorem hasDerivAt_uv_time (p : Fin 3 → ℝ) (t : ℝ) :
    HasDerivAt (fun s ↦ nu0 (cx₁ p) s) (cx₁ p) t ∧
    HasDerivAt (fun s ↦ nv0 (cy₂ p) (cκ p) s) (6 * √3 * cκ p * t ^ 2 - 4 * cy₂ p * t) t ∧
    HasDerivAt (fun s ↦ nu1 (cx₁ p) (cx₂ p) s) (cx₁ p + 2 * cx₂ p * t) t ∧
    HasDerivAt (fun s ↦ nv1 (cy₂ p) (cκ p) s) (6 * √3 * cκ p * t ^ 2 - 2 * cy₂ p * t) t ∧
    HasDerivAt (fun s ↦ nF (cy₁ p) (cy₂ p) (cκ p) s)
      (3 * √3 * cκ p * t ^ 2 - cy₁ p / 2 - 2 * cy₂ p * t) t := by
  have h1 := hasDerivAt_id' t
  have h2 := hasDerivAt_pow 2 t
  have h3 := hasDerivAt_pow 3 t
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ((h1.const_mul (cx₁ p)).sub_const (√3 / 2)).congr_deriv (by ring)
  · exact (((h2.const_mul (2 * cy₂ p)).const_sub (1 / 3)).add
      (h3.const_mul (2 * √3 * cκ p))).congr_deriv (by norm_num; ring)
  · exact (((h1.const_mul (cx₁ p)).add (h2.const_mul (cx₂ p))).sub_const (√3 / 4)).congr_deriv
      (by norm_num; ring)
  · exact (((h2.const_mul (cy₂ p)).const_sub (1 / 12)).add
      (h3.const_mul (2 * √3 * cκ p))).congr_deriv (by norm_num; ring)
  · exact ((((h3.const_mul (√3 * cκ p)).sub ((h1.const_mul (cy₁ p)).div_const 2)).sub
      (h2.const_mul (cy₂ p))).sub_const (1 / 12)).congr_deriv (by norm_num; ring)

/-! ### The switch and the map on `B` -/

/-- At a positive root `τ` of `D` on `𝒟₀₀`, the first switching time is `τ`. -/
theorem firstSwitchTime_eq_root {p : Fin 3 → ℝ} (hp : p ∈ cellBox 0 0) {τ : ℝ} (hτ0 : 0 < τ)
    (h0 : V₂ p τ = 0) : firstSwitchTime (cellPoint p) = τ := by
  obtain ⟨hy, hk, hs2, hs21, hdom⟩ := cellBox_facts hp
  obtain ⟨hr, -, -⟩ := mem_cellBox_zero_zero.1 hp
  have hneg : ∀ t, 0 < t → t < τ → V₂ p t < 0 := fun t ht htτ ↦
    V₂_neg_of_nonpos hy hk ht htτ h0.le
  have hpos : ∀ t, τ < t → 0 < V₂ p t := fun t htτ ↦ V₂_pos_of_nonneg hy hk hτ0 htτ h0.ge
  have hY : ∀ t, 0 < t → 0 < (flow t (cellPoint p) ζ 2).im := by
    intro t ht
    rw [flow_two_im]
    have : 0 ≤ 1 - p 0 := by linarith [hr.2]
    have : 0 ≤ p 0 * Real.sin (p 2) * t := by have := hr.1; positivity
    have : 0 ≤ (1 - p 0) * Real.sin (p 2 - p 1) * t ^ 2 / 2 := by positivity
    have : 0 < t ^ 3 / 12 := by positivity
    linarith
  have hz := cellPoint_mem_sectionZero hdom
  exact (firstControl_firstSwitchTime hz.1 hk hY hτ0 hneg hpos h0).2

/-- The normalized coordinates at the root, with `y₁` eliminated. -/
theorem normalized_eqs' {p : Fin 3 → ℝ} {τ : ℝ} (hτ : 0 < τ) (h0 : V₂ p τ = 0) :
    U₀ p τ = τ * nu0 (cx₁ p) τ⁻¹ ∧ V₀ p τ = τ * nv0 (cy₂ p) (cκ p) τ⁻¹ ∧
    U₁ p τ = τ ^ 2 * nu1 (cx₁ p) (cx₂ p) τ⁻¹ ∧ V₁ p τ = τ ^ 2 * nv1 (cy₂ p) (cκ p) τ⁻¹ ∧
    FF p τ⁻¹ = 0 := by
  have hτ' := hτ.ne'
  have hk : √3 * cκ p = cy₂ p * τ + cy₁ p * τ ^ 2 / 2 + τ ^ 3 / 12 := by unfold V₂ at h0; linarith
  have hk' : cκ p = (cy₂ p * τ + cy₁ p * τ ^ 2 / 2 + τ ^ 3 / 12) / √3 := by
    rw [← hk]; field_simp
  have hq : √3 ≠ 0 := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold U₀ nu0; field_simp
  · unfold V₀ nv0; rw [hk']; field_simp; try ring
  · unfold U₁ nu1; field_simp; try ring
  · unfold V₁ nv1; rw [hk']; field_simp; try ring
  · unfold FF nF; rw [hk']; field_simp; try ring

/-- The cell coordinates of the image, `g p = cellCoords (ζ F(z))`. -/
noncomputable def gmap (p : Fin 3 → ℝ) : Fin 3 → ℝ := cellCoords (ζ • poincare (cellPoint p))

/-- `σ(p) = 1/τ(p)`, the reciprocal of the first switching time. -/
noncomputable def sig (p : Fin 3 → ℝ) : ℝ := (firstSwitchTime (cellPoint p))⁻¹

/-- The coefficients on `B` (`coef_ranges`). -/
theorem box_coef {p : Fin 3 → ℝ} (hp : p ∈ Icc boxLo boxHi) :
    cx₁ p ∈ Icc (-0.101 : ℝ) 0.239 ∧ cy₁ p ∈ Icc (-0.78 : ℝ) (-0.666) ∧
    cx₂ p ∈ Icc (0.0153 : ℝ) 0.115 ∧ cy₂ p ∈ Icc (-0.3 : ℝ) (-0.203) ∧
    cκ p ∈ Icc (0.0137 : ℝ) 0.0416 ∧ dcκ p 0 ∈ Icc (0.0319 : ℝ) 0.111 ∧
    dcκ p 1 ∈ Icc (0 : ℝ) 0.21 := by
  obtain ⟨hr, hc1, hs1, hc2, hs2, hsψ, hcψ⟩ := box_trig hp
  exact coef_ranges hr hc1 hs1 hc2 hs2 hsψ hcψ

/-- `nF` is increasing in `σ ≥ 0` when its coefficients have the signs they have on `B`. -/
theorem nF_mono {y1 y2 k s t : ℝ} (hy1 : y1 < 0) (hy2 : y2 ≤ 0) (hk : 0 ≤ k) (hs : 0 ≤ s)
    (hst : s < t) : nF y1 y2 k s < nF y1 y2 k t := by
  unfold nF
  have h3 : 0 ≤ √3 * k := mul_nonneg (Real.sqrt_nonneg 3) hk
  have e3 : 0 ≤ t ^ 3 - s ^ 3 := sub_nonneg.2 (pow_le_pow_left₀ hs hst.le 3)
  have e2 : 0 ≤ t ^ 2 - s ^ 2 := sub_nonneg.2 (pow_le_pow_left₀ hs hst.le 2)
  nlinarith [mul_nonneg h3 e3, mul_nonneg (neg_nonneg.2 hy2) e2,
    mul_pos (neg_pos.2 hy1) (sub_pos.2 hst)]

/-- **The switch on `B`**: `τ = firstSwitchTime (cellPoint p)` is a positive root of `D`, and
`σ = 1/τ ∈ [0.185, 0.221]` is the root of `nF` (`sigma_bracket`). -/
theorem sig_spec {p : Fin 3 → ℝ} (hp : p ∈ Icc boxLo boxHi) :
    0 < firstSwitchTime (cellPoint p) ∧ V₂ p (firstSwitchTime (cellPoint p)) = 0 ∧
      sig p ∈ Icc (0.185 : ℝ) 0.221 ∧ FF p (sig p) = 0 := by
  have hD1 := box_subset_regionD1 hp
  have hp0 := regionD1_subset hD1
  obtain ⟨τ, hτ0, h0, -, -⟩ := exists_root hp0 (not_face_of_mem_regionD1 hD1)
  have hτe := firstSwitchTime_eq_root hp0 hτ0 h0
  have hsig : sig p = τ⁻¹ := by rw [sig, hτe]
  rw [hτe, hsig]
  obtain ⟨-, -, -, -, hF⟩ := normalized_eqs' hτ0 h0
  obtain ⟨-, hy1, -, hy2, hk, -, -⟩ := box_coef hp
  obtain ⟨b1, b2⟩ := sigma_bracket hy1 hy2 hk
  unfold FF at hF
  refine ⟨hτ0, h0, ⟨?_, ?_⟩, hF⟩
  · by_contra hc
    push Not at hc
    have := nF_mono (y1 := cy₁ p) (y2 := cy₂ p) (k := cκ p) (by linarith [hy1.2])
      (by linarith [hy2.2]) (by linarith [hk.1]) (inv_pos.2 hτ0).le hc
    linarith
  · by_contra hc
    push Not at hc
    have := nF_mono (y1 := cy₁ p) (y2 := cy₂ p) (k := cκ p) (by linarith [hy1.2])
      (by linarith [hy2.2]) (by linarith [hk.1]) (by norm_num) hc
    linarith

/-- The reduction of an angle in `(-π, π)` whose reduction modulo `2π` lies in `(0, π)`. -/
theorem toIcoMod_eq_self_of {x : ℝ} (hx : x ∈ Ioo (-Real.pi) Real.pi)
    (h : toIcoMod Real.two_pi_pos 0 x ∈ Ioo 0 Real.pi) : toIcoMod Real.two_pi_pos 0 x = x := by
  have e : toIcoMod Real.two_pi_pos 0 x =
      x - (toIcoDiv Real.two_pi_pos 0 x : ℝ) * (2 * Real.pi) := by
    rw [← zsmul_eq_mul]
    exact eq_sub_of_add_eq (toIcoMod_add_toIcoDiv_zsmul _ _ _)
  set n := toIcoDiv Real.two_pi_pos 0 x
  have hpi := Real.pi_pos
  have h1 : (n : ℝ) * (2 * Real.pi) < Real.pi := by rw [e] at h; linarith [h.1, hx.2]
  have h2 : -(2 * Real.pi) < (n : ℝ) * (2 * Real.pi) := by rw [e] at h; linarith [h.2, hx.1]
  have hn1 : (n : ℝ) < 1 := by nlinarith
  have hn2 : (-1 : ℝ) < n := by nlinarith
  have : n = 0 := by
    have a : n < 1 := by exact_mod_cast hn1
    have b : -1 < n := by exact_mod_cast hn2
    omega
  rw [e, this]; simp

/-- **The map on `B` in terms of `(p, σ)`**: `θ₂' = GG2 + π`, `ψ' = GG1` and
`(r₂'/(1 - r₂')²)² = MM` at `σ = sig p`. -/
theorem gmap_spec {p : Fin 3 → ℝ} (hp : p ∈ Icc boxLo boxHi) :
    gmap p 2 = GG2 p (sig p) + Real.pi ∧ gmap p 1 = GG1 p (sig p) ∧
      (gmap p 0 / (1 - gmap p 0) ^ 2) ^ 2 = MM p (sig p) := by
  obtain ⟨hτ0, h0, hsig, -⟩ := sig_spec hp
  have hp0 := regionD1_subset (box_subset_regionD1 hp)
  set τ := firstSwitchTime (cellPoint p) with hτdef
  have hs : sig p = τ⁻¹ := rfl
  obtain ⟨hV₁, w, hw, -, e0r, e0i, e1r, e1i, c0, c1, h1, h2⟩ := image_spec hp0 hτ0 h0
  obtain ⟨eU0, eV0, eU1, eV1, -⟩ := normalized_eqs' hτ0 h0
  have hg : gmap p = cellCoords w := by rw [hw]; rfl
  obtain ⟨hx1, -, hx2, hy2, hk, -, -⟩ := box_coef hp
  obtain ⟨hu0, hv0, hu1, hv1⟩ := uv_ranges hx1 hx2 hy2 hk hsig
  rw [← hs] at eU0 eV0 eU1 eV1
  have ht2 : 0 < τ ^ 2 := by positivity
  have hu0n : nu0 (cx₁ p) (sig p) < 0 := by linarith [hu0.2]
  have hu1n : nu1 (cx₁ p) (cx₂ p) (sig p) < 0 := by linarith [hu1.2]
  have hv0p : 0 < nv0 (cy₂ p) (cκ p) (sig p) := by linarith [hv0.1]
  have hv1p : 0 < nv1 (cy₂ p) (cκ p) (sig p) := by linarith [hv1.1]
  have hre1 : (w 1).re < 0 := by rw [e1r, eU1]; exact mul_neg_of_pos_of_neg ht2 hu1n
  have him1 : 0 ≤ (w 1).im := by rw [e1i, eV1]; positivity
  have hre0 : (w 0).re < 0 := by rw [e0r, eU0]; exact mul_neg_of_pos_of_neg hτ0 hu0n
  have him0 : 0 ≤ (w 0).im := by rw [e0i, eV0]; positivity
  have ha1 : Complex.arg (w 1) = GG2 p (sig p) + Real.pi := by
    rw [arg_eq_arctan_add_pi hre1 him1, e1i, e1r, eU1, eV1, GG2]
    congr 2
    field_simp
  have ha0 : Complex.arg (w 0) = GA0 p (sig p) + Real.pi := by
    rw [arg_eq_arctan_add_pi hre0 him0, e0i, e0r, eU0, eV0, GA0]
    congr 2
    field_simp
  refine ⟨by rw [hg, h2, ha1], ?_, ?_⟩
  · rw [hg, h1]
    have hdiff : Complex.arg (w 1) - Complex.arg (w 0) = GG1 p (sig p) := by
      rw [ha1, ha0, GG1]; ring
    rw [hdiff] at c1 ⊢
    refine toIcoMod_eq_self_of ⟨?_, ?_⟩ c1
    · unfold GG1 GG2 GA0
      linarith [Real.neg_pi_div_two_lt_arctan (nv1 (cy₂ p) (cκ p) (sig p) /
        nu1 (cx₁ p) (cx₂ p) (sig p)), Real.arctan_lt_pi_div_two (nv0 (cy₂ p) (cκ p) (sig p) /
        nu0 (cx₁ p) (sig p))]
    · unfold GG1 GG2 GA0
      linarith [Real.arctan_lt_pi_div_two (nv1 (cy₂ p) (cκ p) (sig p) /
        nu1 (cx₁ p) (cx₂ p) (sig p)), Real.neg_pi_div_two_lt_arctan (nv0 (cy₂ p) (cκ p) (sig p) /
        nu0 (cx₁ p) (sig p))]
  · have hw1 : w 1 ≠ 0 := fun h ↦ by rw [h] at e1i; simp at e1i; linarith
    have key := cellCoords_zero_mul hw1
    rw [← hg] at key
    have hr1 : 0 < 1 - gmap p 0 := by rw [hg]; linarith [c0.2]
    set r := gmap p 0
    rw [norm_sq_eq, e0r, e0i, eU0, eV0, norm_eq_sqrt, e1r, e1i, eU1, eV1] at key
    set a0 := nu0 (cx₁ p) (sig p)
    set b0 := nv0 (cy₂ p) (cκ p) (sig p)
    set a1 := nu1 (cx₁ p) (cx₂ p) (sig p)
    set b1 := nv1 (cy₂ p) (cκ p) (sig p)
    have hsq : √((τ ^ 2 * a1) ^ 2 + (τ ^ 2 * b1) ^ 2) = τ ^ 2 * √(a1 ^ 2 + b1 ^ 2) := by
      rw [show (τ ^ 2 * a1) ^ 2 + (τ ^ 2 * b1) ^ 2 = (τ ^ 2) ^ 2 * (a1 ^ 2 + b1 ^ 2) by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq ht2.le]
    rw [hsq] at key
    have key' : r * (a0 ^ 2 + b0 ^ 2) = √(a1 ^ 2 + b1 ^ 2) * (1 - r) ^ 2 := by
      have : τ ^ 2 * (r * (a0 ^ 2 + b0 ^ 2)) = τ ^ 2 * (√(a1 ^ 2 + b1 ^ 2) * (1 - r) ^ 2) := by
        linarith
      exact mul_left_cancel₀ ht2.ne' this
    have hn0 : 0 < a0 ^ 2 + b0 ^ 2 := by positivity
    have : r / (1 - r) ^ 2 = √(a1 ^ 2 + b1 ^ 2) / (a0 ^ 2 + b0 ^ 2) := by
      rw [div_eq_div_iff (by positivity) hn0.ne']; linarith
    rw [this, div_pow, Real.sq_sqrt (by positivity), MM]

/-! ### The derivative bounds on `B × [0.185, 0.221]` -/

section Bounds

variable {w : Fin 3 → ℝ} {t : ℝ}

theorem uv_bounds (hw : w ∈ Icc boxLo boxHi) (ht : t ∈ Icc (0.185 : ℝ) 0.221) :
    UVBox (nu0 (cx₁ w) t) (nv0 (cy₂ w) (cκ w) t) (nu1 (cx₁ w) (cx₂ w) t)
      (nv1 (cy₂ w) (cκ w) t) := by
  obtain ⟨hx1, -, hx2, hy2, hk, -, -⟩ := box_coef hw
  exact uv_ranges hx1 hx2 hy2 hk ht

/-- The bounds `A` of the angular parts in the directions `r, ψ, θ`. -/
noncomputable def Aθ : Fin 3 → ℝ := ![0.19, 0.145, 0.15]
/-- The bounds `R` of the radial combinations in the directions `r, ψ, θ`. -/
noncomputable def Ar : Fin 3 → ℝ := ![1, 1.8, 1.9]
/-- The bounds of `|∂_j F|`. -/
noncomputable def PF : Fin 3 → ℝ := ![0.0786, 0.0304, 0.0322]

/-- **The derivative bounds in the directions `r, ψ, θ`** (`dir_r`, `dir_psi`, `dir_theta`). -/
theorem dir_bounds (hw : w ∈ Icc boxLo boxHi) (ht : t ∈ Icc (0.185 : ℝ) 0.221) (j : Fin 3) :
    |angD (nu1 (cx₁ w) (cx₂ w) t) (nv1 (cy₂ w) (cκ w) t) (dcx₁ w j * t + dcx₂ w j * t ^ 2)
      (2 * √3 * dcκ w j * t ^ 3 - dcy₂ w j * t ^ 2)| ≤ Aθ j ∧
    |angD (nu1 (cx₁ w) (cx₂ w) t) (nv1 (cy₂ w) (cκ w) t) (dcx₁ w j * t + dcx₂ w j * t ^ 2)
      (2 * √3 * dcκ w j * t ^ 3 - dcy₂ w j * t ^ 2) -
      angD (nu0 (cx₁ w) t) (nv0 (cy₂ w) (cκ w) t) (dcx₁ w j * t)
      (2 * √3 * dcκ w j * t ^ 3 - 2 * dcy₂ w j * t ^ 2)| ≤ Aθ j ∧
    |2 * radD (nu1 (cx₁ w) (cx₂ w) t) (nv1 (cy₂ w) (cκ w) t) (dcx₁ w j * t + dcx₂ w j * t ^ 2)
      (2 * √3 * dcκ w j * t ^ 3 - dcy₂ w j * t ^ 2) -
      4 * radD (nu0 (cx₁ w) t) (nv0 (cy₂ w) (cκ w) t) (dcx₁ w j * t)
      (2 * √3 * dcκ w j * t ^ 3 - 2 * dcy₂ w j * t ^ 2)| ≤ Ar j ∧
    |√3 * dcκ w j * t ^ 3 - dcy₁ w j * t / 2 - dcy₂ w j * t ^ 2| ≤ PF j := by
  have huv := uv_bounds hw ht
  obtain ⟨-, hc1, hs1, hc2, hs2, -, -⟩ := box_trig hw
  obtain ⟨hx1, hy1, hx2, hy2, -, hk0, hk1⟩ := box_coef hw
  fin_cases j
  · simp only [Aθ, Ar, PF, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    have hdx1 : dcx₁ w 0 ∈ Icc (-0.3056 : ℝ) 0.129 := by
      simp only [dcx₁, Matrix.cons_val_zero]; exact ⟨by linarith [hc1.2], by linarith [hc1.1]⟩
    have hdy1 : dcy₁ w 0 ∈ Icc (0.952 : ℝ) 1 := by
      simp only [dcy₁, Matrix.cons_val_zero]; exact ⟨by linarith [hs1.2], by linarith [hs1.1]⟩
    exact dir_r huv ht hdx1 hdy1 hc2 hs2 hk0
  · simp only [Aθ, Ar, PF, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    have hdy1 : dcy₁ w 1 ∈ Icc (-0.239 : ℝ) 0.101 := by
      simp only [dcy₁, Matrix.cons_val_one, Matrix.cons_val_zero]
      exact ⟨by linarith [hx1.2], by linarith [hx1.1]⟩
    exact dir_psi huv ht hy1 hdy1 (by simp [dcx₂]) (by simp [dcy₂]) hk1
  · simp only [Aθ, Ar, PF, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    have hdx1 : dcx₁ w 2 ∈ Icc (0.666 : ℝ) 0.78 := by
      simp only [dcx₁, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      exact ⟨by linarith [hy1.2], by linarith [hy1.1]⟩
    have hdx2 : dcx₂ w 2 ∈ Icc (0.203 : ℝ) 0.3 := by
      simp only [dcx₂, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      exact ⟨by linarith [hy2.2], by linarith [hy2.1]⟩
    exact dir_theta huv ht hdx1 hx1 hdx2 hx2 (by simp [dcκ])

/-- **The derivative bounds in the direction `σ`** (`dir_sigma`). -/
theorem time_bounds (hw : w ∈ Icc boxLo boxHi) (ht : t ∈ Icc (0.185 : ℝ) 0.221) :
    |angD (nu1 (cx₁ w) (cx₂ w) t) (nv1 (cy₂ w) (cκ w) t) (cx₁ w + 2 * cx₂ w * t)
      (6 * √3 * cκ w * t ^ 2 - 2 * cy₂ w * t)| ≤ 0.62 ∧
    |angD (nu1 (cx₁ w) (cx₂ w) t) (nv1 (cy₂ w) (cκ w) t) (cx₁ w + 2 * cx₂ w * t)
      (6 * √3 * cκ w * t ^ 2 - 2 * cy₂ w * t) -
      angD (nu0 (cx₁ w) t) (nv0 (cy₂ w) (cκ w) t) (cx₁ w)
      (6 * √3 * cκ w * t ^ 2 - 4 * cy₂ w * t)| ≤ 0.62 ∧
    |2 * radD (nu1 (cx₁ w) (cx₂ w) t) (nv1 (cy₂ w) (cκ w) t) (cx₁ w + 2 * cx₂ w * t)
      (6 * √3 * cκ w * t ^ 2 - 2 * cy₂ w * t) -
      4 * radD (nu0 (cx₁ w) t) (nv0 (cy₂ w) (cκ w) t) (cx₁ w)
      (6 * √3 * cκ w * t ^ 2 - 4 * cy₂ w * t)| ≤ 3.6 ∧
    0.41 ≤ 3 * √3 * cκ w * t ^ 2 - cy₁ w / 2 - 2 * cy₂ w * t := by
  obtain ⟨hx1, hy1, hx2, hy2, hk, -, -⟩ := box_coef hw
  exact dir_sigma (uv_bounds hw ht) ht hx1 hy1 hx2 hy2 hk

end Bounds

/-! ### The partial derivatives of `GG2`, `GA0`, `LM`, `FF` -/

section Derivs

variable {w : Fin 3 → ℝ} {t : ℝ}

theorem normSq_pos_of_uv {u0 v0 u1 v1 : ℝ} (h : UVBox u0 v0 u1 v1) :
    0 < u0 ^ 2 + v0 ^ 2 ∧ 0 < u1 ^ 2 + v1 ^ 2 := by
  obtain ⟨⟨-, hu0⟩, -, ⟨-, hu1⟩, -⟩ := h
  constructor <;> nlinarith

theorem hasDerivAt_dir (hw : w ∈ Icc boxLo boxHi) (ht : t ∈ Icc (0.185 : ℝ) 0.221) (j : Fin 3) :
    HasDerivAt (fun s ↦ GG2 (Function.update w j s) t)
      (angD (nu1 (cx₁ w) (cx₂ w) t) (nv1 (cy₂ w) (cκ w) t) (dcx₁ w j * t + dcx₂ w j * t ^ 2)
        (2 * √3 * dcκ w j * t ^ 3 - dcy₂ w j * t ^ 2)) (w j) ∧
    HasDerivAt (fun s ↦ GA0 (Function.update w j s) t)
      (angD (nu0 (cx₁ w) t) (nv0 (cy₂ w) (cκ w) t) (dcx₁ w j * t)
        (2 * √3 * dcκ w j * t ^ 3 - 2 * dcy₂ w j * t ^ 2)) (w j) ∧
    HasDerivAt (fun s ↦ LM (Function.update w j s) t)
      (2 * radD (nu1 (cx₁ w) (cx₂ w) t) (nv1 (cy₂ w) (cκ w) t) (dcx₁ w j * t + dcx₂ w j * t ^ 2)
        (2 * √3 * dcκ w j * t ^ 3 - dcy₂ w j * t ^ 2) -
        4 * radD (nu0 (cx₁ w) t) (nv0 (cy₂ w) (cκ w) t) (dcx₁ w j * t)
        (2 * √3 * dcκ w j * t ^ 3 - 2 * dcy₂ w j * t ^ 2)) (w j) ∧
    HasDerivAt (fun s ↦ FF (Function.update w j s) t)
      (√3 * dcκ w j * t ^ 3 - dcy₁ w j * t / 2 - dcy₂ w j * t ^ 2) (w j) := by
  obtain ⟨hu0, hv0, hu1, hv1, hF⟩ := hasDerivAt_uv_dir w j t
  have huv := uv_bounds hw ht
  obtain ⟨n0, n1⟩ := normSq_pos_of_uv huv
  have n1' : nu1 (cx₁ w) (cx₂ w) t ≠ 0 := by linarith [huv.2.2.1.2]
  have n0' : nu0 (cx₁ w) t ≠ 0 := by linarith [huv.1.2]
  refine ⟨?_, ?_, ?_, hF⟩
  · have h := hasDerivAt_arctan_div hv1 hu1 (by simpa only [Function.update_eq_self] using n1')
    simp only [Function.update_eq_self] at h
    exact h
  · have h := hasDerivAt_arctan_div hv0 hu0 (by simpa only [Function.update_eq_self] using n0')
    simp only [Function.update_eq_self] at h
    exact h
  · have h1 := hasDerivAt_log_normSq hu1 hv1
      (by simpa only [Function.update_eq_self] using n1.ne')
    have h0 := hasDerivAt_log_normSq hu0 hv0
      (by simpa only [Function.update_eq_self] using n0.ne')
    simp only [Function.update_eq_self] at h1 h0
    exact (h1.sub (h0.const_mul 2)).congr_deriv (by ring)

theorem hasDerivAt_time (hw : w ∈ Icc boxLo boxHi) (ht : t ∈ Icc (0.185 : ℝ) 0.221) :
    HasDerivAt (GG2 w) (angD (nu1 (cx₁ w) (cx₂ w) t) (nv1 (cy₂ w) (cκ w) t)
      (cx₁ w + 2 * cx₂ w * t) (6 * √3 * cκ w * t ^ 2 - 2 * cy₂ w * t)) t ∧
    HasDerivAt (GA0 w) (angD (nu0 (cx₁ w) t) (nv0 (cy₂ w) (cκ w) t) (cx₁ w)
      (6 * √3 * cκ w * t ^ 2 - 4 * cy₂ w * t)) t ∧
    HasDerivAt (LM w) (2 * radD (nu1 (cx₁ w) (cx₂ w) t) (nv1 (cy₂ w) (cκ w) t)
      (cx₁ w + 2 * cx₂ w * t) (6 * √3 * cκ w * t ^ 2 - 2 * cy₂ w * t) -
      4 * radD (nu0 (cx₁ w) t) (nv0 (cy₂ w) (cκ w) t) (cx₁ w)
      (6 * √3 * cκ w * t ^ 2 - 4 * cy₂ w * t)) t ∧
    HasDerivAt (FF w) (3 * √3 * cκ w * t ^ 2 - cy₁ w / 2 - 2 * cy₂ w * t) t := by
  obtain ⟨hu0, hv0, hu1, hv1, hF⟩ := hasDerivAt_uv_time w t
  have huv := uv_bounds hw ht
  obtain ⟨n0, n1⟩ := normSq_pos_of_uv huv
  have n1' : nu1 (cx₁ w) (cx₂ w) t ≠ 0 := by linarith [huv.2.2.1.2]
  have n0' : nu0 (cx₁ w) t ≠ 0 := by linarith [huv.1.2]
  refine ⟨hasDerivAt_arctan_div hv1 hu1 n1', hasDerivAt_arctan_div hv0 hu0 n0', ?_, hF⟩
  exact ((hasDerivAt_log_normSq hu1 hv1 n1.ne').sub
    ((hasDerivAt_log_normSq hu0 hv0 n0.ne').const_mul 2)).congr_deriv (by ring)

end Derivs

/-! ### The entrywise bounds by the implicit mean value theorem -/

/-- The Lipschitz bounds of the rows `θ₂` and `ψ`: `A_j + 0.62 |∂_j F|/0.41`. -/
noncomputable def Lθ (j : Fin 3) : ℝ := Aθ j + 0.62 * PF j / 0.41
/-- The Lipschitz bounds of `log H(r₂')`: `R_j + 3.6 |∂_j F|/0.41`. -/
noncomputable def Lr (j : Fin 3) : ℝ := Ar j + 3.6 * PF j / 0.41

section Rows

theorem hF_all : ∀ w ∈ Icc boxLo boxHi, ∀ t ∈ Icc (0.185 : ℝ) 0.221, ∀ j,
    ∃ d, HasDerivAt (fun s ↦ FF (Function.update w j s) t) d (w j) ∧ d ∈ {α | |α| ≤ PF j} :=
  fun _ hw _ ht j ↦ ⟨_, (hasDerivAt_dir hw ht j).2.2.2, (dir_bounds hw ht j).2.2.2⟩

theorem hFt_all : ∀ w ∈ Icc boxLo boxHi, ∀ t ∈ Icc (0.185 : ℝ) 0.221,
    ∃ d, HasDerivAt (FF w) d t ∧ d ∈ {β : ℝ | 0.41 ≤ β} :=
  fun _ hw _ ht ↦ ⟨_, (hasDerivAt_time hw ht).2.2.2, (time_bounds hw ht).2.2.2⟩

theorem hPt_all : ∀ β ∈ {β : ℝ | 0.41 ≤ β}, β ≠ 0 :=
  fun β hβ ↦ ne_of_gt (lt_of_lt_of_le (by norm_num) hβ)

theorem hsig_all : ∀ w ∈ Icc boxLo boxHi, sig w ∈ Icc (0.185 : ℝ) 0.221 ∧ FF w (sig w) = 0 :=
  fun _ hw ↦ ⟨(sig_spec hw).2.2.1, (sig_spec hw).2.2.2⟩

/-- **The row `θ₂`**: `|GG2 v σ(v) - GG2 u σ(u)| ≤ Σ_j Lθ_j |v_j - u_j|` on `B`. -/
theorem row_theta : ∀ u ∈ Icc boxLo boxHi, ∀ v ∈ Icc boxLo boxHi,
    |GG2 v (sig v) - GG2 u (sig u)| ≤ ∑ j, Lθ j * |v j - u j| := by
  refine abs_sub_le_sum_of_implicit (Q := fun j ↦ {q | |q| ≤ Aθ j}) (Qt := {e | |e| ≤ 0.62})
    hF_all hFt_all (fun _ hw _ ht j ↦ ⟨_, (hasDerivAt_dir hw ht j).1, (dir_bounds hw ht j).1⟩)
    (fun _ hw _ ht ↦ ⟨_, (hasDerivAt_time hw ht).1, (time_bounds hw ht).1⟩) ?_ hPt_all hsig_all
  exact fun j q hq e he α hα β hβ ↦ abs_sub_mul_div_le hq he hα (by norm_num) hβ

/-- **The row `ψ`**: the two angles move the same way in each direction, so the bounds of the
row `θ₂` hold. -/
theorem row_psi : ∀ u ∈ Icc boxLo boxHi, ∀ v ∈ Icc boxLo boxHi,
    |GG1 v (sig v) - GG1 u (sig u)| ≤ ∑ j, Lθ j * |v j - u j| := by
  refine abs_sub_le_sum_of_implicit (Q := fun j ↦ {q | |q| ≤ Aθ j}) (Qt := {e | |e| ≤ 0.62})
    hF_all hFt_all (fun _ hw _ ht j ↦ ⟨_, (hasDerivAt_dir hw ht j).1.sub
      (hasDerivAt_dir hw ht j).2.1, (dir_bounds hw ht j).2.1⟩)
    (fun _ hw _ ht ↦ ⟨_, (hasDerivAt_time hw ht).1.sub (hasDerivAt_time hw ht).2.1,
      (time_bounds hw ht).2.1⟩) ?_ hPt_all hsig_all
  exact fun j q hq e he α hα β hβ ↦ abs_sub_mul_div_le hq he hα (by norm_num) hβ

/-- **The row of the radius function `LM = log H(r₂')`**. -/
theorem row_radius : ∀ u ∈ Icc boxLo boxHi, ∀ v ∈ Icc boxLo boxHi,
    |LM v (sig v) - LM u (sig u)| ≤ ∑ j, Lr j * |v j - u j| := by
  refine abs_sub_le_sum_of_implicit (Q := fun j ↦ {q | |q| ≤ Ar j}) (Qt := {e | |e| ≤ 3.6})
    hF_all hFt_all
    (fun _ hw _ ht j ↦ ⟨_, (hasDerivAt_dir hw ht j).2.2.1, (dir_bounds hw ht j).2.2.1⟩)
    (fun _ hw _ ht ↦ ⟨_, (hasDerivAt_time hw ht).2.2.1, (time_bounds hw ht).2.2.1⟩) ?_ hPt_all
    hsig_all
  exact fun j q hq e he α hα β hβ ↦ abs_sub_mul_div_le hq he hα (by norm_num) hβ

end Rows

/-! ### The Lipschitz bound and `DOutContracts` -/

/-- `|r - r'| ≤ (1/10) |log H(r) - log H(r')|` for `H(r) = (r/(1 - r)²)²` and
`r, r' ∈ [11/50, 3/10]`: `log H(r) = 2 log r - 4 log (1 - r)` has derivative
`2/r + 4/(1 - r) ≥ 6 + 4`. -/
theorem abs_sub_le_radius {r r' : ℝ} (hr : r ∈ Icc (11 / 50 : ℝ) (3 / 10))
    (hr' : r' ∈ Icc (11 / 50 : ℝ) (3 / 10)) :
    |r - r'| ≤
      1 / 10 * |Real.log ((r / (1 - r) ^ 2) ^ 2) - Real.log ((r' / (1 - r') ^ 2) ^ 2)| := by
  have key : ∀ s ∈ Icc (11 / 50 : ℝ) (3 / 10),
      Real.log ((s / (1 - s) ^ 2) ^ 2) = 2 * Real.log s - 4 * Real.log (1 - s) := by
    intro s hs
    have h0 : s ≠ 0 := by linarith [hs.1]
    have h1 : (1 - s) ^ 2 ≠ 0 := pow_ne_zero 2 (by linarith [hs.2])
    rw [Real.log_pow, Real.log_div h0 h1, Real.log_pow]
    push_cast
    ring
  rw [key r hr, key r' hr']
  obtain ⟨d, hd, e⟩ := exists_eq_mul_sub_of_hasDerivAt
    (f := fun s ↦ 2 * Real.log s - 4 * Real.log (1 - s)) (a := r') (b := r)
    (P := fun d ↦ 10 ≤ d) fun s hs ↦ by
      obtain ⟨a, b⟩ := uIcc_subset_Icc hr' hr hs
      have hs0 : 0 < s := by linarith
      have hs1 : 0 < 1 - s := by linarith
      refine ⟨2 / s + 4 / (1 - s), ?_, ?_⟩
      · have h := ((Real.hasDerivAt_log hs0.ne').const_mul 2).sub
          ((((hasDerivAt_id s).const_sub 1).log hs1.ne').const_mul 4)
        refine h.congr_deriv ?_
        simp only [id]
        field_simp
        ring
      · have : 6 ≤ 2 / s := by rw [le_div_iff₀ hs0]; linarith
        have : 4 ≤ 4 / (1 - s) := by rw [le_div_iff₀ hs1]; linarith
        linarith
  have e' : 2 * Real.log r - 4 * Real.log (1 - r) - (2 * Real.log r' - 4 * Real.log (1 - r')) =
      d * (r - r') := e
  rw [e', abs_mul, abs_of_pos (by linarith : (0 : ℝ) < d)]
  nlinarith [abs_nonneg (r - r')]

/-- The entrywise Lipschitz bounds of `gmap`: the rows `r₂` (`1/10` of the bounds of `LM`), `ψ`,
`θ₂`. -/
noncomputable def Lmat : Fin 3 → Fin 3 → ℝ := ![fun j ↦ 1 / 10 * Lr j, Lθ, Lθ]

/-- **`g` is `3/4`-Lipschitz on `B`** (sup metric of the coordinates `(r₂, ψ, θ₂)`), with the row
sums `≤ 0.594`, `≤ 0.699`, `≤ 0.699`.

Departure from the paper: the book does not prove a contraction (it observes that the iterates of
`𝒟_out` shrink toward `q_out`, TeX 12592–12598, and computes the Jacobian at `q_out` only); the
formalization bounds the partial derivatives of the map on all of `B` by a short argument written
out by hand (`SmoothedPolygons/Ch16/DOutDerivativeBounds.lean`: ranges of a few quantities on the
single box `B × [0.185, 0.221]`, the logarithmic derivatives of `w₁/τ` and `w₂/τ²`, and the signs
of the angular parts) and applies the implicit mean value theorem. -/
theorem lipschitzOnWith_gmap : LipschitzOnWith (3 / 4) gmap (Icc boxLo boxHi) := by
  refine lipschitzOnWith_of_abs_sub_le (L := Lmat) ?_ ?_ ?_
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [Lmat, Lr, Lθ, Aθ, Ar, PF] <;> norm_num
  · intro i
    have h34 : ((3 / 4 : NNReal) : ℝ) = 3 / 4 := by norm_num
    rw [h34]
    fin_cases i <;> simp [Lmat, Lr, Lθ, Aθ, Ar, PF, Fin.sum_univ_three] <;> norm_num
  · intro p hp q hq i
    obtain ⟨g2p, g1p, g0p⟩ := gmap_spec hp
    obtain ⟨g2q, g1q, g0q⟩ := gmap_spec hq
    fin_cases i
    · -- `r₂`
      have hrp := (mem_box_iff.1 (image_mem_box (box_subset_regionD1 hp)).1).1
      have hrq := (mem_box_iff.1 (image_mem_box (box_subset_regionD1 hq)).1).1
      have h := abs_sub_le_radius hrp hrq
      change |gmap p 0 - gmap q 0| ≤ ∑ j, Lmat 0 j * |p j - q j|
      have lp : Real.log ((gmap p 0 / (1 - gmap p 0) ^ 2) ^ 2) = LM p (sig p) := by
        rw [g0p, log_MM (normSq_pos_of_uv (uv_bounds hp (sig_spec hp).2.2.1)).1
          (normSq_pos_of_uv (uv_bounds hp (sig_spec hp).2.2.1)).2]
      have lq : Real.log ((gmap q 0 / (1 - gmap q 0) ^ 2) ^ 2) = LM q (sig q) := by
        rw [g0q, log_MM (normSq_pos_of_uv (uv_bounds hq (sig_spec hq).2.2.1)).1
          (normSq_pos_of_uv (uv_bounds hq (sig_spec hq).2.2.1)).2]
      change |gmap p 0 - gmap q 0| ≤ 1 / 10 * |Real.log ((gmap p 0 / (1 - gmap p 0) ^ 2) ^ 2) -
        Real.log ((gmap q 0 / (1 - gmap q 0) ^ 2) ^ 2)| at h
      rw [lp, lq] at h
      have hsum : ∑ j, Lmat 0 j * |p j - q j| = 1 / 10 * ∑ j, Lr j * |p j - q j| := by
        simp only [Lmat, Fin.sum_univ_three, Matrix.cons_val_zero]; ring
      rw [hsum]
      calc |gmap p 0 - gmap q 0| ≤ 1 / 10 * |LM p (sig p) - LM q (sig q)| := h
        _ ≤ 1 / 10 * ∑ j, Lr j * |p j - q j| := by gcongr; exact row_radius q hq p hp
    · -- `ψ`
      change |gmap p 1 - gmap q 1| ≤ ∑ j, Lmat 1 j * |p j - q j|
      rw [g1p, g1q]
      simpa [Lmat] using row_psi q hq p hp
    · -- `θ₂`
      change |gmap p 2 - gmap q 2| ≤ ∑ j, Lmat 2 j * |p j - q j|
      rw [g2p, g2q, show GG2 p (sig p) + Real.pi - (GG2 q (sig q) + Real.pi) =
        GG2 p (sig p) - GG2 q (sig q) by ring]
      simpa [Lmat] using row_theta q hq p hp

/-- `g(B) ⊆ B`. -/
theorem mapsTo_gmap : MapsTo gmap (Icc boxLo boxHi) (Icc boxLo boxHi) :=
  fun _ hp ↦ (image_mem_box (box_subset_regionD1 hp)).1

/-- `F² (𝒟₀₀) ⊆ B` (classes). -/
theorem iterate_two_mem {x : XiW0Quot} (hx : x ∈ boxSet 0 0) :
    poincareAngZero^[2] x ∈ cellClass '' Icc boxLo boxHi := by
  obtain ⟨p, hp, rfl⟩ := hx
  obtain ⟨q, hq, hpq⟩ := image_mem_regionD1 hp
  rw [Function.iterate_succ_apply', Function.iterate_one, ← hpq]
  exact ⟨_, (image_mem_box hq).1, (image_mem_box hq).2.symm⟩

/-- **`DOutContracts`** (`SmoothedPolygons/Ch16/BasinHypotheses.lean`), without computer
assistance: `F(𝒟₀₀) ⊆ 𝒟₀₀`, and with `B = Icc boxLo boxHi`, `N = 2`, `κ = 3/4`, `g = gmap`:
`F²(𝒟₀₀) ⊆ B`, `g(B) ⊆ B`, `g` is `3/4`-Lipschitz on `B` and represents `F` there.

Departure from the paper: the book takes `F₁(𝒟_out) ⊂ 𝒟_out` and the shrinking of the iterates
from Mathematica (Figure 16.1, TeX 12592–12607); the formalization proves both analytically
(`mapsTo_boxSet_zero_zero`, `iterate_two_mem`, `lipschitzOnWith_gmap`), with no kernel-checked
enumeration of boxes. -/
theorem dOutContracts : DOutContracts :=
  ⟨mapsTo_boxSet_zero_zero, boxLo, boxHi, 2, 3 / 4, by norm_num, box_subset_openBoxOne,
    fun _ hx ↦ iterate_two_mem hx, gmap, mapsTo_gmap, lipschitzOnWith_gmap,
    fun _ hp ↦ (image_mem_box (box_subset_regionD1 hp)).2⟩

end SmoothedPolygons.TriFuller.DOutAnalytic

namespace SmoothedPolygons.TriFuller

/-- **Table 16.1, row `𝒟_out`, with the contraction** (`tab:diag`, Figure 16.1; REPORT.md, E78):
`DOutContracts` holds, without computer assistance (`DOutAnalytic.dOutContracts`). -/
theorem dOutContracts : DOutContracts := DOutAnalytic.dOutContracts

end SmoothedPolygons.TriFuller
