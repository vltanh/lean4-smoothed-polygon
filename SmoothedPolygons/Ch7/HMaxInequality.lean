module

public import SmoothedPolygons.Ch7.StrongTransversality
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The inequality `f ≥ 0` of Lemma 7.5.3

We prove the inequality used in the proof of Lemma 7.5.3 (`lem:H-max-6k+2`): the function
`f = hmaxF` is nonnegative on the triangle `T = {(y, r) ∈ [2, 4]² | y ≤ r}`, and it vanishes there
only on the diagonal `y = r`.

We follow the book's route. Fix `r` and put `φ(y) = f(y, r)`.
* `f(y, y) = 0` (`hmaxF_diag`);
* on the diagonal, `∂f/∂y = y((y - 4) + y log(4/y)) ≤ 0` (`hmax_deriv_diag`,
  `hmax_deriv_diag_nonpos`);
* `∂²f/∂y² ≥ 0` on `T`, and `> 0` away from the corner `(4, 4)` (`hmax_deriv2_pos`,
  `hmax_deriv2_nonneg`).
So `φ'` is strictly increasing on `[y, r]`, hence `φ' < φ'(r) ≤ 0` on `[y, r)`, hence `φ` is
strictly decreasing on `[y, r]` and `φ(y) > φ(r) = 0`.

The bound on the second derivative is left by the book as a "tedious but elementary exercise";
here it is proved as follows (`ℓ = log(4/y)`, `F = ∂²f/∂y²`).
* `log u ≥ 2(u - 1)/(u + 1)` for `u ≥ 1` (`hmax_log_ge`), so `(4 + y) ℓ ≥ 2(4 - y)`.
* `a - b ≤ a (log a - log b)` for `a, b > 0` (`hmax_sub_le_mul_log_sub`).
* For `y ∈ [3, 4)`: with `a = r`, `b = 4`,
  `F ≥ -26 - r + 2r/y + 7y + (2r + 6y) ℓ`, and the bound on `ℓ` reduces the right side (times
  `y (4 + y)`) to `(4 - r) y (10y - 24) + (r - y)(5y² - 10y + 8) > 0`.
* For `y ∈ [2, 3]`: with `a = r`, `b = r* = 2 √y exp((y - 2)/(4y))` (the minimizer of `F` in `r`),
  `F ≥ -10 + 7y + 6yℓ - 4r*`; then `exp x ≤ 1/(1 - x)`, `3√y ≤ y + 9/4` and the bound on `ℓ`
  reduce this (times `3 (4 + y)(3y + 2)`) to the cubic
  `-77y³ + 364y² - 252y - 240 = 96(3 - y) + 201(y - 2) + (y - 2)(3 - y)(77y + 21) > 0`.
-/

@[expose] public section

namespace SmoothedPolygons

open Real Set

/-- The partial derivative `∂f/∂y` of `f = hmaxF` (see `hmax_hasDerivAt`). -/
noncomputable def hmaxFDeriv (y r : ℝ) : ℝ :=
  -r ^ 2 - 3 * r * y + 6 * r - 10 * y + 5 * y ^ 2 + 2 * r * (2 * y - 1) * (log r - log y) +
    (3 * y ^ 2 - 2 * r * y) * log (4 / y)

/-- The second partial derivative `∂²f/∂y²` of `f = hmaxF`, in the form of the book (see
`hmax_hasDerivAt_deriv`). -/
noncomputable def hmaxFDeriv2 (y r : ℝ) : ℝ :=
  -10 - 5 * r + 2 * r / y + 7 * y + 4 * r * log r - 2 * (r - 3 * y) * log (4 / y) -
    4 * r * log y

/-- `d/dy log(4/y) = -1/y`. -/
lemma hmax_hasDerivAt_log_four_div {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y => log (4 / y)) (-1 / y) y := by
  have h := ((hasDerivAt_const y (4 : ℝ)).fun_div (hasDerivAt_id' (x := y)) hy.ne').log
    (div_pos four_pos hy).ne'
  convert h using 1
  field_simp
  ring

/-- `∂f/∂y = hmaxFDeriv` for `y > 0`. -/
lemma hmax_hasDerivAt (r : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y => hmaxF y r) (hmaxFDeriv y r) y := by
  have hid : HasDerivAt (fun y : ℝ => y) 1 y := hasDerivAt_id' y
  have hlog : HasDerivAt log y⁻¹ y := hasDerivAt_log hy.ne'
  have hL := hmax_hasDerivAt_log_four_div hy
  have h := ((((hid.sub_const 1).const_mul (2 * r)).fun_mul hid).mul_const (log r)).fun_sub
      (((hasDerivAt_const y r).fun_sub hid).fun_mul
        ((((hasDerivAt_const y r).fun_mul (hid.sub_const 1)).fun_add
          (hid.fun_mul ((hasDerivAt_const y (-5 : ℝ)).fun_add (hid.const_mul 2)))).fun_add
            ((hid.fun_pow 2).fun_mul hL))) |>.fun_sub
      ((((hid.sub_const 1).const_mul (2 * r)).fun_mul hid).fun_mul hlog)
  unfold hmaxF
  convert h using 1
  unfold hmaxFDeriv
  field_simp
  ring

/-- `∂²f/∂y² = hmaxFDeriv2` for `y > 0`. -/
lemma hmax_hasDerivAt_deriv (r : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y => hmaxFDeriv y r) (hmaxFDeriv2 y r) y := by
  have hid : HasDerivAt (fun y : ℝ => y) 1 y := hasDerivAt_id' y
  have hlog : HasDerivAt log y⁻¹ y := hasDerivAt_log hy.ne'
  have hL := hmax_hasDerivAt_log_four_div hy
  have h := (((((hasDerivAt_const y (-r ^ 2)).fun_sub (hid.const_mul (3 * r))).add_const
      (6 * r)).fun_sub (hid.const_mul 10)).fun_add ((hid.fun_pow 2).const_mul 5)).fun_add
        ((((hid.const_mul 2).sub_const 1).const_mul (2 * r)).fun_mul
          ((hasDerivAt_const y (log r)).fun_sub hlog)) |>.fun_add
        ((((hid.fun_pow 2).const_mul 3).fun_sub (hid.const_mul (2 * r))).fun_mul hL)
  unfold hmaxFDeriv
  convert h using 1
  unfold hmaxFDeriv2
  field_simp
  ring

/-- `log u ≥ 2(u - 1)/(u + 1)` for `u ≥ 1`. -/
lemma hmax_log_ge {u : ℝ} (hu : 1 ≤ u) : 2 * (u - 1) / (u + 1) ≤ log u := by
  have hd : ∀ v : ℝ, 0 < v → HasDerivAt (fun v => log v - 2 * (v - 1) / (v + 1))
      (v⁻¹ - ((2 * 1) * (v + 1) - 2 * (v - 1) * 1) / (v + 1) ^ 2) v := fun v hv =>
    (hasDerivAt_log hv.ne').sub ((((hasDerivAt_id' (x := v)).sub_const 1).const_mul 2).fun_div
      ((hasDerivAt_id' (x := v)).add_const 1) (by positivity))
  have hmono : MonotoneOn (fun v => log v - 2 * (v - 1) / (v + 1)) (Ici 1) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 1)
      (fun v hv => (hd v (by simp at hv; linarith)).continuousAt.continuousWithinAt)
      (fun v hv => (hd v ?_).hasDerivWithinAt) (fun v hv => ?_)
    · rw [interior_Ici] at hv
      exact zero_lt_one.trans hv
    · rw [interior_Ici] at hv
      have hv0 : 0 < v := zero_lt_one.trans hv
      have e : v⁻¹ - ((2 * 1) * (v + 1) - 2 * (v - 1) * 1) / (v + 1) ^ 2 =
          (v - 1) ^ 2 / (v * (v + 1) ^ 2) := by
        field_simp
        ring
      rw [e]
      positivity
  have := hmono self_mem_Ici hu hu
  simp only [sub_self, mul_zero, zero_div, log_one] at this
  linarith

/-- `a - b ≤ a (log a - log b)` for `a, b > 0` (from `log x ≥ 1 - 1/x`). -/
lemma hmax_sub_le_mul_log_sub {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a - b ≤ a * (log a - log b) := by
  have h := one_sub_inv_le_log_of_pos (div_pos ha hb)
  rw [log_div ha.ne' hb.ne', inv_div] at h
  calc a - b = a * (1 - b / a) := by field_simp
    _ ≤ a * (log a - log b) := mul_le_mul_of_nonneg_left h ha.le

/-- The bound `(4 + y) log(4/y) ≥ 2(4 - y)` for `0 < y ≤ 4`. -/
lemma hmax_log_four_div_ge {y : ℝ} (hy : 0 < y) (hy4 : y ≤ 4) :
    2 * (4 - y) ≤ (4 + y) * log (4 / y) := by
  have h := hmax_log_ge (u := 4 / y) (by rw [le_div_iff₀ hy]; linarith [hy4])
  have e : 2 * (4 / y - 1) / (4 / y + 1) = 2 * (4 - y) / (4 + y) := by
    field_simp
  rw [e, div_le_iff₀ (by positivity)] at h
  linarith

/-- The derivative `∂f/∂y` on the diagonal (equation `eqn:f'` of the book). -/
lemma hmax_deriv_diag (y : ℝ) : hmaxFDeriv y y = y * ((y - 4) + y * log (4 / y)) := by
  unfold hmaxFDeriv
  ring

/-- The derivative `∂f/∂y` is `≤ 0` on the diagonal (for all `y > 0`; the book needs
`y ∈ [2, 4]`), since `y log(4/y) ≤ 4 - y`. -/
lemma hmax_deriv_diag_nonpos {y : ℝ} (hy : 0 < y) : hmaxFDeriv y y ≤ 0 := by
  rw [hmax_deriv_diag]
  have h := log_le_sub_one_of_pos (div_pos four_pos hy)
  have h' : y * log (4 / y) ≤ 4 - y := by
    calc y * log (4 / y) ≤ y * (4 / y - 1) := mul_le_mul_of_nonneg_left h hy.le
      _ = 4 - y := by field_simp
  exact mul_nonpos_of_nonneg_of_nonpos hy.le (by linarith)

/-- The second derivative `∂²f/∂y²` is positive on `T` minus the corner `(4, 4)`: the
"tedious but elementary exercise" of the proof of Lemma 7.5.3. -/
lemma hmax_deriv2_pos {y r : ℝ} (hy : 2 ≤ y) (hy4 : y < 4) (hyr : y ≤ r) (hr : r ≤ 4) :
    0 < hmaxFDeriv2 y r := by
  have hy0 : 0 < y := by linarith
  have hr0 : 0 < r := by linarith
  have hℓ : log (4 / y) = log 4 - log y := log_div (by norm_num) hy0.ne'
  have hℓb := hmax_log_four_div_ge hy0 hy4.le
  rcases le_total 3 y with h3 | h3
  · -- `y ∈ [3, 4)`: compare `log r` with `log 4`.
    have hk := hmax_sub_le_mul_log_sub hr0 four_pos
    have e : hmaxFDeriv2 y r = -26 - r + 2 * r / y + 7 * y + (2 * r + 6 * y) * log (4 / y) +
        4 * (r * (log r - log 4) - (r - 4)) := by
      unfold hmaxFDeriv2
      rw [hℓ]
      ring
    suffices 0 < -26 - r + 2 * r / y + 7 * y + (2 * r + 6 * y) * log (4 / y) by
      rw [e]; linarith
    have e2 : y * (4 + y) * (-26 - r + 2 * r / y + 7 * y + (2 * r + 6 * y) * log (4 / y)) =
        (4 + y) * (-26 * y - r * y + 2 * r + 7 * y ^ 2) +
          (2 * r + 6 * y) * y * ((4 + y) * log (4 / y)) := by
      field_simp
    refine pos_of_mul_pos_right (a := y * (4 + y)) ?_ (by positivity)
    rw [e2]
    nlinarith [mul_le_mul_of_nonneg_left hℓb (by positivity : 0 ≤ (2 * r + 6 * y) * y),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 4 - r) (by nlinarith : (0 : ℝ) ≤ y * (10 * y - 24) - 18),
      mul_nonneg (by linarith : (0 : ℝ) ≤ r - y)
        (by nlinarith : (0 : ℝ) ≤ 5 * y ^ 2 - 10 * y + 8 - 23)]
  · -- `y ∈ [2, 3]`: compare `log r` with `log r*`, `r* = 2 √y exp((y - 2)/(4y))`.
    set s := √y with hs_def
    have hs0 : 0 < s := Real.sqrt_pos.2 hy0
    have hs2 : s ^ 2 = y := Real.sq_sqrt hy0.le
    set x := (y - 2) / (4 * y) with hx_def
    set rs := 2 * s * exp x with hrs_def
    have hrs0 : 0 < rs := by positivity
    have hlogrs : log rs = log 2 + log s + x := by
      rw [hrs_def, log_mul (by positivity) (exp_pos _).ne', log_mul (by norm_num) hs0.ne',
        log_exp]
    have hly : log y = 2 * log s := by
      rw [← hs2, log_pow]
      norm_num
    have hl4 : log 4 = 2 * log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
      norm_num
    have hk := hmax_sub_le_mul_log_sub hr0 hrs0
    have e : hmaxFDeriv2 y r = -10 + 7 * y + 6 * y * log (4 / y) - 4 * rs +
        4 * (r * (log r - log rs) - (r - rs)) := by
      unfold hmaxFDeriv2
      rw [hlogrs, hℓ, hly, hl4, hx_def]
      field_simp
      ring
    suffices 0 < -10 + 7 * y + 6 * y * log (4 / y) - 4 * rs by
      rw [e]; linarith
    -- `exp x ≤ 1 / (1 - x) = 4y / (3y + 2)`.
    have hexp : exp x * (3 * y + 2) ≤ 4 * y := by
      have h1 := add_one_le_exp (-x)
      have h2 : exp x * exp (-x) = 1 := by rw [← exp_add]; simp
      have h3 : exp x * (1 - x) ≤ 1 := by
        rw [← h2]
        exact mul_le_mul_of_nonneg_left (by linarith) (exp_pos x).le
      have e3 : exp x * (3 * y + 2) = 4 * y * (exp x * (1 - x)) := by
        rw [hx_def]
        field_simp
        ring
      rw [e3]
      nlinarith
    have hrsb : rs * (3 * y + 2) ≤ 8 * y * s := by
      have := mul_le_mul_of_nonneg_left hexp (by positivity : (0 : ℝ) ≤ 2 * s)
      rw [hrs_def]
      nlinarith
    have hsb : 3 * s ≤ y + 9 / 4 := by nlinarith [sq_nonneg (s - 3 / 2)]
    refine pos_of_mul_pos_right (a := (4 + y) * (3 * y + 2)) ?_ (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hℓb (by positivity : 0 ≤ 6 * y * (3 * y + 2)),
      mul_le_mul_of_nonneg_left hrsb (by positivity : 0 ≤ 4 * (4 + y)),
      mul_le_mul_of_nonneg_left hsb (by positivity : 0 ≤ 32 * y * (4 + y)),
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ y - 2) (by linarith : (0 : ℝ) ≤ 3 - y))
        (by linarith : (0 : ℝ) ≤ 77 * y + 21)]

/-- The second derivative `∂²f/∂y²` is nonnegative on the triangle `T` (it vanishes at the
corner `(4, 4)`). -/
lemma hmax_deriv2_nonneg {y r : ℝ} (hy : 2 ≤ y) (hyr : y ≤ r) (hr : r ≤ 4) :
    0 ≤ hmaxFDeriv2 y r := by
  rcases (hyr.trans hr).lt_or_eq with hy4 | rfl
  · exact (hmax_deriv2_pos hy hy4 hyr hr).le
  · obtain rfl : r = 4 := le_antisymm hr hyr
    unfold hmaxFDeriv2
    norm_num

/-- `f(y, y) = 0`: the diagonal `y = r` of `T` (the time `t = 0`) is a zero of `f`. -/
theorem hmaxF_diag (y : ℝ) (_hy : 0 < y) : hmaxF y y = 0 := by
  unfold hmaxF
  ring

/-- `f(y, r) > 0` on the triangle `T = {(y, r) ∈ [2, 4]² | y ≤ r}` off the diagonal `y = r`
(proof of Lemma 7.5.3). For fixed `r`, `φ = f(·, r)` has `φ'' > 0` on `(y, r)`, so `φ'` is
strictly increasing on `[y, r]` with `φ'(r) ≤ 0`; hence `φ` is strictly decreasing on `[y, r]`
and `φ(y) > φ(r) = 0`. -/
theorem hmaxF_pos {y r : ℝ} (hy : 2 ≤ y) (hyr : y < r) (hr : r ≤ 4) : 0 < hmaxF y r := by
  have hpos : ∀ z ∈ Icc y r, 0 < z := fun z hz => by linarith [hz.1]
  have hD1 : ∀ z ∈ Icc y r, HasDerivAt (fun z => hmaxF z r) (hmaxFDeriv z r) z :=
    fun z hz => hmax_hasDerivAt r (hpos z hz)
  have hD2 : ∀ z ∈ Icc y r, HasDerivAt (fun z => hmaxFDeriv z r) (hmaxFDeriv2 z r) z :=
    fun z hz => hmax_hasDerivAt_deriv r (hpos z hz)
  have hmono : StrictMonoOn (fun z => hmaxFDeriv z r) (Icc y r) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc y r)
      (fun z hz => (hD2 z hz).continuousAt.continuousWithinAt) (fun z hz => ?_)
    rw [interior_Icc] at hz
    rw [(hD2 z (Ioo_subset_Icc_self hz)).deriv]
    exact hmax_deriv2_pos (by linarith [hz.1]) (by linarith [hz.2]) hz.2.le hr
  have hdiag : hmaxFDeriv r r ≤ 0 := hmax_deriv_diag_nonpos (by linarith)
  have hanti : StrictAntiOn (fun z => hmaxF z r) (Icc y r) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc y r)
      (fun z hz => (hD1 z hz).continuousAt.continuousWithinAt) (fun z hz => ?_)
    rw [interior_Icc] at hz
    rw [(hD1 z (Ioo_subset_Icc_self hz)).deriv]
    exact (hmono (Ioo_subset_Icc_self hz) (right_mem_Icc.2 hyr.le) hz.2).trans_le hdiag
  have h : hmaxF r r < hmaxF y r := hanti (left_mem_Icc.2 hyr.le) (right_mem_Icc.2 hyr.le) hyr
  rwa [hmaxF_diag r (by linarith)] at h

/-- **The inequality of Lemma 7.5.3**: `f(y, r) ≥ 0` on the triangle
`T = {(y, r) ∈ [2, 4]² | y ≤ r}`. -/
theorem hmaxF_nonneg {y r : ℝ} (hy : 2 ≤ y) (hyr : y ≤ r) (hr : r ≤ 4) : 0 ≤ hmaxF y r := by
  rcases hyr.lt_or_eq with hyr | rfl
  · exact (hmaxF_pos hy hyr hr).le
  · exact (hmaxF_diag y (by linarith)).ge

end SmoothedPolygons
