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

In the proofs: a root `r > 1` gives a root `y = r + 1/r ≥ 2` of `Q`; `Q < 0` on `[2, 6]`, so
`y > 6`, and two roots `y₁, y₂ > 6` coincide because
`Q(y₁) - Q(y₂) = (y₁ - y₂)(y₁² + y₁y₂ + y₂² - 5y₁ - 5y₂ - 10)` with a positive second factor; and
`r ↦ r + 1/r` is injective on `(1, ∞)`. For `r < 0`, `y ≤ -2` and `Q(y) < 0`; `P(1) = -27`; and
`r⁶ P(1/r) = P(r)` takes the roots in `(0, 1)` to roots in `(1, ∞)`. Existence and the enclosures
are the intermediate value theorem between two rational points.
-/

@[expose] public section

namespace SmoothedPolygons

open Set

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
  unfold rScalePoly
  field_simp
  ring

/-- `P` is palindromic: `r⁶ P(1/r) = P(r)`. -/
private lemma l4g_rScalePoly_inv {r : ℝ} (hr : r ≠ 0) :
    r ^ 6 * rScalePoly r⁻¹ = rScalePoly r := by
  unfold rScalePoly
  field_simp
  ring

/-- `P` is continuous. -/
private lemma l4g_continuous_rScalePoly : Continuous rScalePoly := by
  unfold rScalePoly
  fun_prop

/-- A root `r > 0` of `P` gives a root `y = r + 1/r` of `Q(y) = y³ - 5y² - 10y + 5`. -/
private lemma l4g_Q_eq_zero {r : ℝ} (hr : r ≠ 0) (h : rScalePoly r = 0) :
    (r + r⁻¹) ^ 3 - 5 * (r + r⁻¹) ^ 2 - 10 * (r + r⁻¹) + 5 = 0 := by
  rw [l4st_rScalePoly_eq hr] at h
  exact (mul_eq_zero.1 h).resolve_left (pow_ne_zero 3 hr)

/-- `r + 1/r ≥ 2` for `r > 0`. -/
private lemma l4g_two_le_add_inv {r : ℝ} (hr : 0 < r) : 2 ≤ r + r⁻¹ := by
  have h : r * r⁻¹ = 1 := mul_inv_cancel₀ hr.ne'
  nlinarith [sq_nonneg (r - 1), inv_pos.2 hr]

/-- The roots `y ≥ 2` of `Q` are greater than `6` (`Q < 0` on `[2, 6]`). -/
private lemma l4g_six_lt_of_Q {y : ℝ} (hy : 2 ≤ y) (h : y ^ 3 - 5 * y ^ 2 - 10 * y + 5 = 0) :
    6 < y := by
  by_contra hy6
  replace hy6 := not_lt.1 hy6
  nlinarith [mul_nonneg (sub_nonneg.2 hy) (sub_nonneg.2 hy6),
    mul_nonneg (mul_nonneg (sub_nonneg.2 hy) (sub_nonneg.2 hy6)) (sub_nonneg.2 hy)]

/-- **Uniqueness of the root greater than `1`** (inventory, §13.5): `Q` has one root `y > 2`
(`Q < 0` on `[2, 6]` and `Q` is increasing on `[6, ∞)`), and `r ↦ r + 1/r` is injective on
`(1, ∞)`. -/
private lemma l4g_root_unique {r₁ r₂ : ℝ} (h₁ : 1 < r₁) (h₂ : 1 < r₂) (hP₁ : rScalePoly r₁ = 0)
    (hP₂ : rScalePoly r₂ = 0) : r₁ = r₂ := by
  have hr₁ : (0 : ℝ) < r₁ := by linarith
  have hr₂ : (0 : ℝ) < r₂ := by linarith
  have hQ₁ := l4g_Q_eq_zero hr₁.ne' hP₁
  have hQ₂ := l4g_Q_eq_zero hr₂.ne' hP₂
  have hy₁ := l4g_six_lt_of_Q (l4g_two_le_add_inv hr₁) hQ₁
  have hy₂ := l4g_six_lt_of_Q (l4g_two_le_add_inv hr₂) hQ₂
  set y₁ := r₁ + r₁⁻¹ with hy₁def
  set y₂ := r₂ + r₂⁻¹ with hy₂def
  have hy : y₁ = y₂ := by
    have hfac : (y₁ - y₂) * (y₁ ^ 2 + y₁ * y₂ + y₂ ^ 2 - 5 * y₁ - 5 * y₂ - 10) = 0 := by
      linear_combination hQ₁ - hQ₂
    have hpos : 0 < y₁ ^ 2 + y₁ * y₂ + y₂ ^ 2 - 5 * y₁ - 5 * y₂ - 10 := by nlinarith
    linarith [(mul_eq_zero.1 hfac).resolve_right hpos.ne']
  have hi₁ : r₁ * r₁⁻¹ = 1 := mul_inv_cancel₀ hr₁.ne'
  have hi₂ : r₂ * r₂⁻¹ = 1 := mul_inv_cancel₀ hr₂.ne'
  have hfac : (r₁ - r₂) * (r₁ * r₂ - 1) = 0 := by
    have : r₁ + r₁⁻¹ = r₂ + r₂⁻¹ := hy
    have e : (r₁ + r₁⁻¹) * (r₁ * r₂) = (r₂ + r₂⁻¹) * (r₁ * r₂) := by rw [this]
    linear_combination e - r₂ * hi₁ + r₁ * hi₂
  have hpos : r₁ * r₂ - 1 ≠ 0 := by nlinarith
  linarith [(mul_eq_zero.1 hfac).resolve_right hpos]

/-- A sign change of `P` on `[a, b]` gives a root in `(a, b)`. -/
private lemma l4g_exists_root {a b : ℝ} (hab : a ≤ b) (ha : rScalePoly a < 0)
    (hb : 0 < rScalePoly b) : ∃ c ∈ Ioo a b, rScalePoly c = 0 :=
  intermediate_value_Ioo hab l4g_continuous_rScalePoly.continuousOn ⟨ha, hb⟩

/-- `rScale` is any root greater than `1`. -/
private lemma l4g_rScale_eq {c : ℝ} (hc : 1 < c) (h : rScalePoly c = 0) : rScale = c := by
  have : {r : ℝ | 1 < r ∧ rScalePoly r = 0} = {c} := by
    ext r
    change (1 < r ∧ rScalePoly r = 0) ↔ r = c
    exact ⟨fun hr ↦ l4g_root_unique hr.1 hc hr.2 h, fun hr ↦ hr ▸ ⟨hc, h⟩⟩
  rw [rScale, this, csSup_singleton]

/-- A sign change of `P` on `[a, b]` with `a ≥ 1` encloses `r_scale`. -/
private lemma l4g_rScale_mem {a b : ℝ} (ha1 : 1 ≤ a) (hab : a ≤ b) (ha : rScalePoly a < 0)
    (hb : 0 < rScalePoly b) : a < rScale ∧ rScale < b := by
  obtain ⟨c, hc, hPc⟩ := l4g_exists_root hab ha hb
  rw [l4g_rScale_eq (by linarith [hc.1]) hPc]
  exact hc

/-- `r_scale > 1` is a root of `P`. -/
theorem l4st_rScale_spec : 1 < rScale ∧ rScalePoly rScale = 0 := by
  obtain ⟨c, hc, hPc⟩ := l4g_exists_root (a := 6.27) (b := 6.28) (by norm_num)
    (by unfold rScalePoly; norm_num) (by unfold rScalePoly; norm_num)
  have hc1 : 1 < c := by linarith [hc.1]
  rw [l4g_rScale_eq hc1 hPc]
  exact ⟨hc1, hPc⟩

/-- `r_scale` is the only real root of `P` greater than `1`. -/
theorem l4st_rScale_unique {r : ℝ} (hr : 1 < r) (h : rScalePoly r = 0) : r = rScale :=
  (l4g_rScale_eq hr h).symm

/-- The real roots of `P` are exactly `r_scale` and `1/r_scale` (TeX 11378–11380). -/
theorem l4st_rScalePoly_eq_zero_iff (r : ℝ) : rScalePoly r = 0 ↔ r = rScale ∨ r = rScale⁻¹ := by
  obtain ⟨hs1, hsP⟩ := l4st_rScale_spec
  have hs0 : rScale ≠ 0 := by positivity
  constructor
  · intro h
    have hr0 : r ≠ 0 := by
      rintro rfl
      norm_num [rScalePoly] at h
    rcases lt_trichotomy r 0 with hneg | hzero | hpos
    · -- `r < 0`: then `y = r + 1/r ≤ -2`, and `Q < 0` there
      exfalso
      have hQ := l4g_Q_eq_zero hr0 h
      have hi : r * r⁻¹ = 1 := mul_inv_cancel₀ hr0
      have hy : r + r⁻¹ ≤ -2 := by nlinarith [sq_nonneg (r + 1), inv_lt_zero.2 hneg]
      nlinarith [sq_nonneg (r + r⁻¹ + 2)]
    · exact absurd hzero hr0
    · rcases lt_trichotomy r 1 with hlt | heq | hgt
      · -- `0 < r < 1`: `1/r > 1` is a root
        right
        have hinv : rScalePoly r⁻¹ = 0 := by
          have := l4g_rScalePoly_inv hr0
          rw [h] at this
          exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero 6 hr0)
        rw [l4g_rScale_eq (one_lt_inv₀ hpos |>.2 hlt) hinv, inv_inv]
      · subst heq
        norm_num [rScalePoly] at h
      · exact Or.inl (l4st_rScale_unique hgt h)
  · rintro (rfl | rfl)
    · exact hsP
    · have := l4g_rScalePoly_inv (inv_ne_zero hs0)
      rw [inv_inv, hsP, mul_zero] at this
      exact this.symm

/-- `6.27 < r_scale < 6.28` (the book's `r_scale ≈ 6.27`). -/
theorem l4st_rScale_bounds : 6.27 < rScale ∧ rScale < 6.28 :=
  l4g_rScale_mem (by norm_num) (by norm_num) (by unfold rScalePoly; norm_num)
    (by unfold rScalePoly; norm_num)

/-- A fine enclosure of `r_scale = 6.274167399524823932993…`, as needed for the certified
eigenvalue bound of Lemma 13.5.5 (whose characteristic polynomial has coefficients in `ℚ(r_scale)`
with large cancellations; see `SmoothedPolygons/Ch13/Jacobian.lean`). -/
theorem l4st_rScale_fine_bounds :
    (6.2741673995248239329 : ℝ) < rScale ∧ rScale < 6.2741673995248239330 :=
  l4g_rScale_mem (by norm_num) (by norm_num) (by unfold rScalePoly; norm_num)
    (by unfold rScalePoly; norm_num)

end TriFuller

end SmoothedPolygons
