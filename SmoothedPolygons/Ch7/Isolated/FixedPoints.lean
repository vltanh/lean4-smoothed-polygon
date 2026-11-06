module

public import SmoothedPolygons.Ch7.Isolated.Defs
public import SmoothedPolygons.Ch7.SmoothedPolygon

/-!
# Theorem 7.7.1, steps 6–7: the implicit function theorem and the final transversality

Step 6: near the octagon's point, the fixed points of the fourth iterate of the Poincaré map on the
section are the points `q_fix(y₀)`. Step 7: the condition `g(t_f) = R` picks `y₀ = y_oct` in this
family (the converse direction of Lemma 7.5.5 for `k = 1`).
-/

@[expose] public section

namespace SmoothedPolygons

open Matrix Set Filter Topology MeasureTheory

/-! ### Step 6: the implicit function theorem -/

/-- Near `q_oct`, the fixed points of `f⁴` on the section are the `q_fix(y₀)`. In coordinates
`(d, ξ)` on `N = ⋃_d N_d` (or with `X₁₀ = 1/y₀` as the parameter), `f⁴ - id` has an invertible
partial derivative `A⁴ - I` in `ξ` (by `iso_hyperbolic` with `θ ∈ {0, π/2, π}`), so its zero set
is a graph over the parameter (`HasStrictFDerivAt.implicitFunctionOfProdDomain`), which the
family `q_fix(y₀)` (`iso_poincareMap_qFix`) fills. -/
theorem iso_fixedPoints :
    ∃ V ∈ 𝓝 (iso_qFix (y₀ 1)), ∀ q ∈ V, iso_IsSectionPt q → iso_poincareMap^[4] q = q →
      ∃ y0 ∈ Ioo (1 / √3) 1, q = iso_qFix y0 := by
  sorry

/-! ### Step 7: the final transversality condition -/

/-- If `A ∈ SL₂(ℝ)` and `A⁴ = -I` then `(tr A)² = 2`: by Cayley–Hamilton `A⁴ + I =
(t² - 2)(tA - I)`, `t = tr A`; if `t² ≠ 2` then `tA = I` and `t² = t(a + d) = 2` anyway. -/
theorem iso_trace_sq_of_pow_four (A : Mat2) (hdet : A.det = 1) (h4 : A ^ 4 = -1) :
    A.trace ^ 2 = 2 := by
  have hd : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by rw [← Matrix.det_fin_two]; exact hdet
  have h00 : (A ^ 4) 0 0 = -1 := by rw [h4]; simp
  have h11 : (A ^ 4) 1 1 = -1 := by rw [h4]; simp
  simp only [pow_succ, pow_zero, one_mul, Matrix.mul_apply, Fin.sum_univ_two] at h00 h11
  rw [Matrix.trace_fin_two]
  set a := A 0 0
  set b := A 0 1
  set c := A 1 0
  set d := A 1 1
  have e00 : ((a + d) ^ 2 - 2) * ((a + d) * a - 1) = 0 := by
    linear_combination h00 - (-3 * a ^ 2 - 3 * a * d - b * c - d ^ 2 + 1) * hd
  have e11 : ((a + d) ^ 2 - 2) * ((a + d) * d - 1) = 0 := by
    linear_combination h11 - (-a ^ 2 - 3 * a * d - b * c - 3 * d ^ 2 + 1) * hd
  by_contra hne
  have h2 : (a + d) ^ 2 - 2 ≠ 0 := sub_ne_zero.mpr hne
  have ha : (a + d) * a - 1 = 0 := (mul_eq_zero.mp e00).resolve_left h2
  have hd' : (a + d) * d - 1 = 0 := (mul_eq_zero.mp e11).resolve_left h2
  exact hne (by linear_combination ha + hd')

/-- The final transversality condition picks the octagon in the family: if the trajectory from
`q_fix(y₀)` with four switching intervals ends at `g(4 t_sw) = R`, then `y₀ = y_oct`
(`g(4t_sw) = h⁴R⁴` with `h = g_sw R⁻¹`, so `h⁴ = R⁻³ = -I`, `(tr h)² = 2`, `tr h = 4/(1 + 3y₀²)`;
the converse direction of Lemma 7.5.5 for `k = 1`). -/
theorem iso_y0_of_closing (y0 : ℝ) (hy0 : 1 / √3 < y0) (hy1 : y0 < 1)
    (h : polygonG y0 (switchTime y0) (4 * switchTime y0) = R) : y0 = y₀ 1 := by
  have hy : 0 < y0 := poly_y0_pos hy0
  have hτ := str_switchTime_pos y0 hy0 hy1
  set hh := segG y0 (switchTime y0) * R⁻¹ with hhdef
  -- `g(4 t_sw) = h⁴ R⁴ = -h⁴ R`
  have hfl : ⌊4 * switchTime y0 / switchTime y0⌋₊ = 4 := by
    rw [mul_div_cancel_right₀ _ hτ.ne']
    exact_mod_cast Nat.floor_natCast 4
  have hR4 : R ^ 4 = -R := by rw [pow_succ, poly_R_pow_three, neg_one_mul]
  rw [polygonG, hfl, show 4 * switchTime y0 - ((4 : ℕ) : ℝ) * switchTime y0 = 0 by push_cast; ring,
    str_segG_zero y0 hy, mul_one, hR4, ← hhdef] at h
  have h4 : hh ^ 4 = -1 := by
    have := congrArg (· * R⁻¹) h
    simp only [Matrix.mul_neg, Matrix.neg_mul, mul_assoc, poly_R_mul_inv, mul_one] at this
    rw [← neg_neg (hh ^ 4), this]
  have hdet : hh.det = 1 := by
    rw [hhdef, Matrix.det_mul, (seg_solution y0 0 hy).2.2.2.2 _, poly_det_Rinv, one_mul]
  have htr := iso_trace_sq_of_pow_four hh hdet h4
  rw [hhdef, trace_segG_switchTime y0 hy0] at htr
  -- `4/(1 + 3y₀²) = √2`, so `3y₀² = 2√2 - 1 = 3 y_oct²`
  have hpos : 0 < 4 / (1 + 3 * y0 ^ 2) := by positivity
  have hsq : 4 / (1 + 3 * y0 ^ 2) = √2 := by rw [← htr, Real.sqrt_sq hpos.le]
  have hs2 : √2 ^ 2 = 2 := poly_sqrt_two_sq
  have h3 : 3 * y0 ^ 2 = 3 * y₀ 1 ^ 2 := by
    rw [poly_three_y₀_one_sq, poly_sqrt8]
    rw [div_eq_iff (by positivity)] at hsq
    nlinarith
  have hy1' : 0 < y₀ 1 := poly_y0_pos (poly_y₀_mem le_rfl).1
  have hprod : (y0 - y₀ 1) * (y0 + y₀ 1) = 0 := by linear_combination h3 / 3
  rcases mul_eq_zero.mp hprod with h' | h'
  · linarith
  · linarith

end SmoothedPolygons
