module

public import SmoothedPolygons.Ch7.ConstantControl
public import SmoothedPolygons.AppA.MatrixIdentities

/-!
# Constant control splines and the smoothed `(6k+2)`-gons (§7.4, §7.5)

The trajectory of the smoothed `(6k+2)`-gon is the spline (`eqn:gamma-bang-bang`) with the control
mode sequence `((0, t_sw), (-1, t_sw), …, (-3k, t_sw))` (`eqn:3k+1`), initial control
`u₀ = e₃ = (0, 0, 1)` and initial point `z₀ = i y₀`. On the `i`-th switching interval
`[i t_sw, (i+1) t_sw]` the control is `R⁻ⁱ · e₃` and the trajectory is the conjugate by `R⁻ⁱ` of
the `e₃`-trajectory from `z₀`; by the strong boundary condition `z(z₀, t_sw) = R⁻¹ · z₀`
(`eqn:poly-z`) every switching interval starts again from `z₀`.
-/

@[expose] public section

namespace SmoothedPolygons

open Matrix

/-- The switching time `t_sw(y₀) = ln(4/(3y₀² + 1))/(√3 y₀)` (`eqn:t1`). -/
noncomputable def switchTime (y0 : ℝ) : ℝ := Real.log (4 / (3 * y0 ^ 2 + 1)) / (√3 * y0)

theorem tsw_eq_switchTime (k : ℕ) : tsw k = switchTime (y₀ k) := rfl

/-- The control of the spline with switching time `τ`: `R⁻ⁱ · e₃` on `[iτ, (i+1)τ)`, that is,
`e₃, e₁, e₂, e₃, …` (`eqn:3k+1`). -/
noncomputable def polygonControlAt (τ t : ℝ) : Fin 3 → ℝ :=
  Pi.single (⟨(2 + ⌊t / τ⌋₊) % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3) 1

theorem polygonControl_eq (k : ℕ) : polygonControl k = polygonControlAt (tsw k) := rfl

/-- `P₀ = Z_{e₃}/⟨Z_{e₃}, Φ(i y₀)⟩` for the first switching interval. -/
noncomputable def segP (y0 : ℝ) : Mat2 := controlP (vertex 2) (Φ 0 y0)

/-- The group trajectory `g₀(z₀, t)` with constant control `e₃` from `z₀ = i y₀`
(`eqn:const-control-g`). -/
noncomputable def segG (y0 t : ℝ) : Mat2 := constControlG (Φ 0 y0) (segP y0) t

/-- The Lie algebra trajectory `X(z₀, t)` with constant control `e₃` from `X₀ = Φ(i y₀)`
(`eqn:const-control-z-X`). -/
noncomputable def segX (y0 t : ℝ) : Mat2 := constControlX (Φ 0 y0) (segP y0) t

/-! ### Helpers: `P₀`, `X₀ + P₀` and their exponentials -/

lemma str_sqrt3_sq : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
lemma str_sqrt3_pow3 : √3 ^ 3 = 3 * √3 := by rw [pow_succ, str_sqrt3_sq]
lemma str_sqrt3_pow4 : √3 ^ 4 = 9 := by rw [show 4 = 2 * 2 by rfl, pow_mul, str_sqrt3_sq]; norm_num
lemma str_sqrt3_pow5 : √3 ^ 5 = 9 * √3 := by rw [pow_succ, str_sqrt3_pow4]
lemma str_sqrt3_pow6 : √3 ^ 6 = 27 := by rw [show 6 = 2 * 3 by rfl, pow_mul, str_sqrt3_sq]; norm_num
lemma str_sqrt3_pow7 : √3 ^ 7 = 27 * √3 := by rw [pow_succ, str_sqrt3_pow6]
lemma str_sqrt3_pow8 : √3 ^ 8 = 81 := by rw [show 8 = 2 * 4 by rfl, pow_mul, str_sqrt3_sq]; norm_num

/-- `⟨Z_{e₃}, Φ(x + iy)⟩ = -2(1 + √3 x)/(3y)`. -/
lemma str_traceForm_Z3_Φ (x y : ℝ) :
    traceForm (controlMatrix (vertex 2)) (Φ x y) = -(2 * (1 + √3 * x)) / (3 * y) := by
  have h3 : (0 : ℝ) < √3 := by positivity
  simp [traceForm, controlMatrix, vertex, Φ, Matrix.trace_fin_two]
  field_simp
  linear_combination (2 * x * y⁻¹) * str_sqrt3_sq

/-- `exp(tA) = cosh(ct) I + sinh(ct)/c A` for traceless `A` with `det A = -c²` (Lemma A.6.4),
written with `exp(ct)`. -/
private lemma str_exp_smul_of_det_neg (A : Mat2) (hA : A.trace = 0) {c : ℝ} (hc : 0 < c)
    (hdet : A.det = -c ^ 2) (t : ℝ) :
    NormedSpace.exp (t • A) =
      ((Real.exp (c * t) + (Real.exp (c * t))⁻¹) / 2) • (1 : Mat2) +
        ((Real.exp (c * t) - (Real.exp (c * t))⁻¹) / (2 * c)) • A := by
  have hneg : A.det < 0 := by rw [hdet]; nlinarith [sq_pos_of_pos hc]
  have hs : √(-A.det) = c := by rw [hdet, neg_neg, Real.sqrt_sq hc.le]
  rw [((lemmaA_6_4 A hA).2 t).1 hneg, hs, Real.cosh_eq, Real.sinh_eq, mul_comm t c,
    Real.exp_neg, div_div]

/-- `P₀ = Z_{e₃}/⟨Z_{e₃}, X₀⟩ = [[√3y₀/2, y₀], [0, -√3y₀/2]]`. -/
lemma str_segP_eq (y0 : ℝ) (hy0 : y0 ≠ 0) :
    segP y0 = !![√3 * y0 / 2, y0; 0, -(√3 * y0 / 2)] := by
  have h3 : (0 : ℝ) < √3 := by positivity
  rw [segP, controlP, str_traceForm_Z3_Φ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [controlMatrix, vertex] <;> field_simp <;>
    nlinarith [str_sqrt3_sq]

/-- `exp(tP₀) = [[w, (w - w⁻¹)/√3], [0, w⁻¹]]`, `w = exp(√3y₀t/2)`. -/
private lemma str_exp_segP (y0 : ℝ) (hy0 : 0 < y0) (t : ℝ) :
    NormedSpace.exp (t • segP y0) =
      !![Real.exp (√3 * y0 / 2 * t),
        (Real.exp (√3 * y0 / 2 * t) - (Real.exp (√3 * y0 / 2 * t))⁻¹) / √3;
        0, (Real.exp (√3 * y0 / 2 * t))⁻¹] := by
  have h3 : (0 : ℝ) < √3 := by positivity
  rw [str_exp_smul_of_det_neg (segP y0) ?_ (c := √3 * y0 / 2) (by positivity) ?_ t,
    str_segP_eq y0 hy0.ne']
  · ext i j
    fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring
  · simp [str_segP_eq y0 hy0.ne', Matrix.trace_fin_two]
  · simp [str_segP_eq y0 hy0.ne', Matrix.det_fin_two]
    ring

/-- `X₀ + P₀ = [[√3y₀/2, 0], [1/y₀, -√3y₀/2]]` and
`exp(t(X₀ + P₀)) = [[w, 0], [(w - w⁻¹)/(√3y₀²), w⁻¹]]`, `w = exp(√3y₀t/2)`. -/
private lemma str_exp_XP (y0 : ℝ) (hy0 : 0 < y0) (t : ℝ) :
    NormedSpace.exp (t • (Φ 0 y0 + segP y0)) =
      !![Real.exp (√3 * y0 / 2 * t), 0;
        (Real.exp (√3 * y0 / 2 * t) - (Real.exp (√3 * y0 / 2 * t))⁻¹) / (√3 * y0 ^ 2),
        (Real.exp (√3 * y0 / 2 * t))⁻¹] := by
  have h3 : (0 : ℝ) < √3 := by positivity
  have hXP : Φ 0 y0 + segP y0 = !![√3 * y0 / 2, 0; 1 / y0, -(√3 * y0 / 2)] := by
    rw [str_segP_eq y0 hy0.ne']
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Φ]
    field_simp
    ring
  rw [str_exp_smul_of_det_neg _ ?_ (c := √3 * y0 / 2) (by positivity) ?_ t, hXP]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring
  · simp [hXP, Matrix.trace_fin_two]
  · simp [hXP, Matrix.det_fin_two]
    field_simp

/-! ### The `e₃`-trajectory from `z₀ = i y₀` in closed form -/

/-- `X(z₀, t) = Φ(z(t))` with `z(t) = (W - 1)/√3 + i y₀ W`, `W = exp(√3 y₀ t)`: the trajectory moves
along the straight line from the ideal vertex `-1/√3` (§7.2). -/
theorem segX_eq (y0 t : ℝ) (hy0 : 0 < y0) :
    segX y0 t = Φ ((Real.exp (√3 * y0 * t) - 1) / √3) (y0 * Real.exp (√3 * y0 * t)) := by
  have h3 : (0 : ℝ) < √3 := by positivity
  have hw : 0 < Real.exp (√3 * y0 / 2 * t) := Real.exp_pos _
  have hW : Real.exp (√3 * y0 * t) = Real.exp (√3 * y0 / 2 * t) ^ 2 := by
    rw [sq, ← Real.exp_add]; ring_nf
  have hneg : Real.exp (√3 * y0 / 2 * -t) = (Real.exp (√3 * y0 / 2 * t))⁻¹ := by
    rw [mul_neg, Real.exp_neg]
  rw [segX, constControlX, str_exp_segP y0 hy0, str_exp_segP y0 hy0, hneg, hW]
  generalize Real.exp (√3 * y0 / 2 * t) = w at hw ⊢
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Φ] <;> field_simp <;> ring_nf

/-- `g₀(z₀, t)` in closed form, `W = exp(√3 y₀ t)`. -/
theorem segG_eq (y0 t : ℝ) (hy0 : 0 < y0) :
    segG y0 t = !![1, -(Real.exp (√3 * y0 * t) - 1) / √3;
      (1 - (Real.exp (√3 * y0 * t))⁻¹) / (√3 * y0 ^ 2),
      1 - (Real.exp (√3 * y0 * t) - 2 + (Real.exp (√3 * y0 * t))⁻¹) / (3 * y0 ^ 2)] := by
  have h3 : (0 : ℝ) < √3 := by positivity
  have hw : 0 < Real.exp (√3 * y0 / 2 * t) := Real.exp_pos _
  have hW : Real.exp (√3 * y0 * t) = Real.exp (√3 * y0 / 2 * t) ^ 2 := by
    rw [sq, ← Real.exp_add]; ring_nf
  have hneg : Real.exp (√3 * y0 / 2 * -t) = (Real.exp (√3 * y0 / 2 * t))⁻¹ := by
    rw [mul_neg, Real.exp_neg]
  rw [segG, constControlG, str_exp_XP y0 hy0, str_exp_segP y0 hy0, hneg, hW]
  generalize Real.exp (√3 * y0 / 2 * t) = w at hw ⊢
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp
  ring_nf
  simp only [str_sqrt3_sq]
  ring

/-- The `e₃`-trajectory solves the state equations with constant control `e₃`. -/
theorem seg_solution (y0 t : ℝ) (hy0 : 0 < y0) :
    HasDerivAtEntrywise (segG y0) (segG y0 t * segX y0 t) t ∧
      HasDerivAtEntrywise (segX y0)
        (controlP (vertex 2) (segX y0 t) * segX y0 t -
          segX y0 t * controlP (vertex 2) (segX y0 t)) t ∧
      segG y0 0 = 1 ∧ segX y0 0 = Φ 0 y0 ∧ ∀ s, (segG y0 s).det = 1 := by
  have hX₀ : (Φ 0 y0).trace = 0 := by simp [Φ, Matrix.trace_fin_two]
  have hden : traceForm (controlMatrix (vertex 2)) (Φ 0 y0) ≠ 0 := by
    rw [str_traceForm_Z3_Φ]; simp [hy0.ne']
  obtain ⟨h1, h2, h3, h4⟩ := constControl_solution (vertex 2) (Φ 0 y0) hX₀ hden t
  refine ⟨h1, h2, h3, h4, fun s ↦ ?_⟩
  have h3 : (0 : ℝ) < √3 := by positivity
  have hW := Real.exp_pos (√3 * y0 * s)
  rw [segG_eq y0 s hy0, Matrix.det_fin_two_of]
  generalize Real.exp (√3 * y0 * s) = W at hW ⊢
  field_simp
  ring_nf
  simp only [str_sqrt3_sq]
  ring

/-- `y₀ > 1/√3` means `y₀² > 1/3`. -/
lemma str_one_third_lt_sq {y0 : ℝ} (hy0 : 1 / √3 < y0) : 1 / 3 < y0 ^ 2 := by
  have h3 : (0 : ℝ) < √3 := by positivity
  have : (1 / √3) ^ 2 = 1 / 3 := by rw [div_pow, str_sqrt3_sq]; norm_num
  rw [← this]
  exact pow_lt_pow_left₀ hy0 (by positivity) (by norm_num)

/-- `√3 y₀ t_sw = ℓ = ln(4/(3y₀² + 1))`. -/
lemma str_mul_switchTime {y0 : ℝ} (hy0 : 0 < y0) :
    √3 * y0 * switchTime y0 = Real.log (4 / (3 * y0 ^ 2 + 1)) := by
  have h3 : (0 : ℝ) < √3 := by positivity
  rw [switchTime]
  field_simp

/-- `W(t_sw) = exp(√3 y₀ t_sw) = 4/(3y₀² + 1)`. -/
lemma str_exp_switchTime {y0 : ℝ} (hy0 : 0 < y0) :
    Real.exp (√3 * y0 * switchTime y0) = 4 / (3 * y0 ^ 2 + 1) := by
  rw [str_mul_switchTime hy0, Real.exp_log (by positivity)]

/-- On `[0, t_sw]`, `1 ≤ W = exp(√3 y₀ t) ≤ 4/(3y₀² + 1)`. -/
lemma str_W_mem {y0 : ℝ} (hy0 : 0 < y0) {t : ℝ} (ht : t ∈ Set.Icc 0 (switchTime y0)) :
    1 ≤ Real.exp (√3 * y0 * t) ∧ Real.exp (√3 * y0 * t) ≤ 4 / (3 * y0 ^ 2 + 1) := by
  have h3 : (0 : ℝ) < √3 := by positivity
  constructor
  · exact Real.one_le_exp (by have := ht.1; positivity)
  · rw [← str_exp_switchTime hy0]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 (by positivity))

/-- On `[0, t_sw]` the `e₃`-trajectory stays in the star domain. -/
theorem segX_star (y0 : ℝ) (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) (t : ℝ)
    (ht : t ∈ Set.Icc 0 (switchTime y0)) : IsStarState (segX y0 t) := by
  have h3 : (0 : ℝ) < √3 := by positivity
  have hy0' : 0 < y0 := lt_trans (by positivity) hy0
  have hsq := str_one_third_lt_sq hy0
  obtain ⟨hW1, hW2⟩ := str_W_mem hy0' ht
  rw [segX_eq y0 t hy0', theorem4_4_1 _ _ (by positivity)]
  generalize Real.exp (√3 * y0 * t) = W at hW1 hW2
  have hW2' : W < 2 := by
    refine lt_of_le_of_lt hW2 ?_
    rw [div_lt_iff₀ (by positivity)]
    linarith
  refine ⟨by positivity, ?_, ?_, ?_⟩ <;> dsimp only
  · rw [show -(1 / √3) = (-1) / √3 by ring, div_lt_div_iff_of_pos_right h3]; linarith
  · rw [div_lt_div_iff_of_pos_right h3]; linarith
  · have hW' : 1 ≤ W ^ 2 := by nlinarith
    have : y0 ^ 2 ≤ (y0 * W) ^ 2 := by
      rw [mul_pow]; nlinarith [mul_le_mul_of_nonneg_left hW' (sq_nonneg y0)]
    nlinarith [sq_nonneg ((W - 1) / √3)]

/-- `R⁻¹ = [[1/2, √3/2], [-√3/2, 1/2]]`. -/
lemma str_R_inv : R⁻¹ = !![1 / 2, √3 / 2; -(√3 / 2), 1 / 2] := by
  refine Matrix.inv_eq_left_inv ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [R] <;> ring_nf <;> simp <;> norm_num

lemma str_det_R : R.det = 1 := by
  simp [R, Matrix.det_fin_two]
  ring_nf
  simp
  norm_num

private lemma str_R_mul_R_inv : R * R⁻¹ = 1 :=
  Matrix.mul_nonsing_inv R (by rw [str_det_R]; exact isUnit_one)

private lemma str_pow_R_mul (n : ℕ) : R ^ n * (R⁻¹) ^ n = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ', mul_assoc, ← mul_assoc R, str_R_mul_R_inv, one_mul, ih]

private lemma str_pow_mul_R_inv (A : Mat2) (n : ℕ) :
    (A * R⁻¹) ^ n = ((List.range n).map fun m ↦ (R⁻¹) ^ m * A * R ^ m).prod * (R⁻¹) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ (A * R⁻¹) n, ih, List.range_succ, List.map_append, List.prod_append,
      pow_succ (R⁻¹) n]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
    rw [← mul_assoc (R ^ n), str_pow_R_mul, one_mul]

/-- The strong boundary condition `z(z₀, t_sw) = R⁻¹ · z₀` (`eqn:poly-z`), in the Lie algebra:
`X(z₀, t_sw) = R⁻¹ X₀ R`. -/
theorem segX_switchTime (y0 : ℝ) (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) :
    segX y0 (switchTime y0) = R⁻¹ * Φ 0 y0 * R := by
  have h3 : (0 : ℝ) < √3 := by positivity
  have hy0' : 0 < y0 := lt_trans (by positivity) hy0
  rw [segX_eq _ _ hy0', str_exp_switchTime hy0', str_R_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Φ, R] <;> field_simp <;> ring_nf <;>
    simp only [str_sqrt3_sq, str_sqrt3_pow4] <;> ring

/-- The trace of `h = g(t_sw) R⁻¹` is `4/(1 + 3y₀²)` (proof of Theorem 7.5.1). -/
theorem trace_segG_switchTime (y0 : ℝ) (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) :
    (segG y0 (switchTime y0) * R⁻¹).trace = 4 / (1 + 3 * y0 ^ 2) := by
  have h3 : (0 : ℝ) < √3 := by positivity
  have hy0' : 0 < y0 := lt_trans (by positivity) hy0
  rw [segG_eq _ _ hy0', str_exp_switchTime hy0', str_R_inv]
  simp [Matrix.trace_fin_two]
  field_simp
  ring_nf

/-- The Lie algebra trajectory of the spline: `R⁻ⁱ X(z₀, t - iτ) Rⁱ` on `[iτ, (i+1)τ)`. -/
noncomputable def polygonX (y0 τ t : ℝ) : Mat2 :=
  (R⁻¹) ^ ⌊t / τ⌋₊ * segX y0 (t - ⌊t / τ⌋₊ * τ) * R ^ ⌊t / τ⌋₊

/-- The group trajectory of the spline (`eqn:gamma-bang-bang`):
`g(t) = g_sw (R⁻¹ g_sw R) ⋯ (R^{-(i-1)} g_sw R^{i-1}) · R⁻ⁱ g₀(z₀, t - iτ) Rⁱ` on `[iτ, (i+1)τ)`,
written as `(g_sw R⁻¹)ⁱ g₀(z₀, t - iτ) Rⁱ`, where `g_sw = g₀(z₀, τ)`. -/
noncomputable def polygonG (y0 τ t : ℝ) : Mat2 :=
  (segG y0 τ * R⁻¹) ^ ⌊t / τ⌋₊ * segG y0 (t - ⌊t / τ⌋₊ * τ) * R ^ ⌊t / τ⌋₊

/-- The product form of the spline (`eqn:gamma-bang-bang`): on the `i`-th switching interval,
`g(t) = (∏_{m < i} R^{-m} g_sw R^m) · R^{-i} g₀(z₀, t - iτ) R^i`. -/
theorem polygonG_eq_prod (y0 τ t : ℝ) :
    polygonG y0 τ t =
      ((List.range ⌊t / τ⌋₊).map fun m ↦ (R⁻¹) ^ m * segG y0 τ * R ^ m).prod *
        ((R⁻¹) ^ ⌊t / τ⌋₊ * segG y0 (t - ⌊t / τ⌋₊ * τ) * R ^ ⌊t / τ⌋₊) := by
  rw [polygonG, str_pow_mul_R_inv]
  simp only [mul_assoc]

end SmoothedPolygons
