module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Chapter 13: the scaling factor `r_scale`

The scaling factor `r_scale ≈ 6.27` of the triangular spirals of Hales–Vajjha, *Packings of
Smoothed Polygons*, Lemma 13.5.2 (TeX 11331–11335, 11374–11380): the unique real root greater than
`1` of the palindromic polynomial `P(r) = 1 - 5r - 7r² - 5r³ - 7r⁴ - 5r⁵ + r⁶`. The book's
"`r_s` and `1/r_s` are the only two real roots" is `l4st_rScalePoly_eq_zero_iff`.

Certified bounds replace the book's numerical values (`≈ 6.27`): `l4st_rScale_bounds` (the
statement of Lemma 13.5.2 uses `6.27 < r_scale < 6.28`) and a fine enclosure for the certified
eigenvalue computation of Lemma 13.5.5.

Proof route (inventory, §13.5): `P(r) = r³ Q(r + 1/r)` with `Q(y) = y³ - 5y² - 10y + 5`
(`l4st_rScalePoly_eq`); `Q` has one root `y_s ≈ 6.4336 > 2` and two roots in `(-2, -1)` and
`(0, 1)`, which give no real `r` (`|r + 1/r| ≥ 2`); so the real roots of `P` are the two roots
`r_s > 1 > 1/r_s` of `r + 1/r = y_s`. The bounds are sign changes of `P` at rational points
(`norm_num`).
-/

@[expose] public section

namespace SmoothedPolygons

namespace TriFuller

/-- The palindromic polynomial `P(r) = 1 - 5r - 7r² - 5r³ - 7r⁴ - 5r⁵ + r⁶` of Lemma 13.5.2
(TeX 11331–11335). -/
def rScalePoly (r : ℝ) : ℝ := 1 - 5 * r - 7 * r ^ 2 - 5 * r ^ 3 - 7 * r ^ 4 - 5 * r ^ 5 + r ^ 6

/-- The scaling factor `r_scale` (TeX 11331–11335): the unique real root greater than `1` of the
palindromic polynomial (defined as the supremum of the real roots greater than `1`;
`l4st_rScale_spec`, `l4st_rScale_unique`). -/
noncomputable def rScale : ℝ := sSup {r : ℝ | 1 < r ∧ rScalePoly r = 0}

/-- `P(r) = r³ Q(r + 1/r)` with `Q(y) = y³ - 5y² - 10y + 5`. -/
theorem l4st_rScalePoly_eq {r : ℝ} (hr : r ≠ 0) :
    rScalePoly r = r ^ 3 * ((r + r⁻¹) ^ 3 - 5 * (r + r⁻¹) ^ 2 - 10 * (r + r⁻¹) + 5) := by
  sorry

/-- `r_scale > 1` is a root of `P`. -/
theorem l4st_rScale_spec : 1 < rScale ∧ rScalePoly rScale = 0 := by
  sorry

/-- `r_scale` is the only real root of `P` greater than `1`. -/
theorem l4st_rScale_unique {r : ℝ} (hr : 1 < r) (h : rScalePoly r = 0) : r = rScale := by
  sorry

/-- The real roots of `P` are exactly `r_scale` and `1/r_scale` (TeX 11378–11380). -/
theorem l4st_rScalePoly_eq_zero_iff (r : ℝ) : rScalePoly r = 0 ↔ r = rScale ∨ r = rScale⁻¹ := by
  sorry

/-- `6.27 < r_scale < 6.28` (the book's `r_scale ≈ 6.27`). -/
theorem l4st_rScale_bounds : 6.27 < rScale ∧ rScale < 6.28 := by
  sorry

/-- A fine enclosure of `r_scale = 6.274167399524823932993…`, as needed for the certified
eigenvalue bound of Lemma 13.5.5 (whose characteristic polynomial has coefficients in `ℚ(r_scale)`
with large cancellations; see `SmoothedPolygons/Ch13/Jacobian.lean`). -/
theorem l4st_rScale_fine_bounds :
    (6.2741673995248239329 : ℝ) < rScale ∧ rScale < 6.2741673995248239330 := by
  sorry

end TriFuller

end SmoothedPolygons
