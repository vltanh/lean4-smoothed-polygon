module

public import SmoothedPolygons.Ch7.HMaxInequality

/-!
# The maximum property of the Hamiltonian on one edge (Lemma 7.5.3)

We follow the proof of the book. By the uniqueness part of Theorem 7.5.1 (`strongLift_unique`),
a strong lift with `λ_cost = -1` is the explicit lift `strongΛR`. The symmetry
`χ₃₁(t_sw - t) = χ₃₂(t)` (`chi31_eq_chi32`) reduces everything to `χ₃₂`. In the variables
`y = 1 + 3y₀² ∈ (2, 4)` and `r = yW`, `W = exp(√3 y₀ t) ∈ [1, 4/y]`, the switching function is
`χ₃₂(t) = 2 f(y, r) / (3 y² W y₀³ (2 - W))` (`chi32_eq`) with a positive denominator (`W < 2`),
and `(y, r)` lies in the triangle `T = {(y, r) ∈ [2, 4]² | y ≤ r}`. So `χ₃₂ ≥ 0` by
`hmaxF_nonneg`, and `χ₃₂(t) > 0` for `t > 0` (then `r > y`) by `hmaxF_pos`.
-/

@[expose] public section

namespace SmoothedPolygons

open Set Real

/-- `1 < √3 y₀` for `y₀ > 1/√3`. -/
lemma hmax_one_lt_sqrt3_mul {y0 : ℝ} (hy0 : 1 / √3 < y0) : 1 < √3 * y0 := by
  rwa [div_lt_iff₀ (by positivity), mul_comm] at hy0

/-- `y = 1 + 3y₀² ∈ (2, 4)` for `y₀ ∈ (1/√3, 1)`. -/
lemma hmax_y_mem {y0 : ℝ} (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) :
    2 < 1 + 3 * y0 ^ 2 ∧ 1 + 3 * y0 ^ 2 < 4 := by
  have h := hmax_one_lt_sqrt3_mul hy0
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < y0 := lt_trans (by positivity) hy0
  constructor <;> nlinarith [mul_pos hpos hpos]

/-- For `t ∈ [0, t_sw]`, `W = exp(√3 y₀ t)` satisfies `1 ≤ W` and `y W ≤ 4`, `y = 1 + 3y₀²`
(since `exp(√3 y₀ t_sw) = 4/y`). -/
lemma hmax_W_mem {y0 : ℝ} (hy0 : 1 / √3 < y0) {t : ℝ} (ht : t ∈ Icc 0 (switchTime y0)) :
    1 ≤ exp (√3 * y0 * t) ∧ (1 + 3 * y0 ^ 2) * exp (√3 * y0 * t) ≤ 4 := by
  have ha := hmax_one_lt_sqrt3_mul hy0
  refine ⟨one_le_exp (mul_nonneg (by linarith) ht.1), ?_⟩
  have hne : y0 ≠ 0 := (lt_trans (by positivity) hy0).ne'
  have hsw : √3 * y0 * switchTime y0 = log (4 / (3 * y0 ^ 2 + 1)) := by
    unfold switchTime
    field_simp
  have hle : exp (√3 * y0 * t) ≤ 4 / (3 * y0 ^ 2 + 1) := by
    calc exp (√3 * y0 * t) ≤ exp (√3 * y0 * switchTime y0) :=
          exp_le_exp_of_le (mul_le_mul_of_nonneg_left ht.2 (by linarith))
      _ = 4 / (3 * y0 ^ 2 + 1) := by rw [hsw, exp_log (by positivity)]
  rw [le_div_iff₀ (by positivity)] at hle
  linarith

/-- The switching function `χ₃₂` of the explicit lift is `≥ 0` on `[0, t_sw]`, via `f ≥ 0`. -/
lemma hmax_chi32_nonneg {y0 : ℝ} (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) {t : ℝ}
    (ht : t ∈ Icc 0 (switchTime y0)) : 0 ≤ switchingFn 2 1 (strongΛR y0 t) (segX y0 t) := by
  obtain ⟨hy2, hy4⟩ := hmax_y_mem hy0 hy1
  obtain ⟨hW1, hW4⟩ := hmax_W_mem hy0 ht
  have hpos : 0 < y0 := lt_trans (by positivity) hy0
  rw [chi32_eq y0 hy0 hy1 t ht]
  have h2W : 0 < 2 - exp (√3 * y0 * t) := by nlinarith
  refine div_nonneg (mul_nonneg zero_le_two (hmaxF_nonneg hy2.le ?_ hW4)) (by positivity)
  nlinarith

/-- The switching function `χ₃₂` of the explicit lift is `> 0` on `(0, t_sw]`, via `f > 0` off
the diagonal. -/
lemma hmax_chi32_pos {y0 : ℝ} (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) {t : ℝ}
    (ht : t ∈ Icc 0 (switchTime y0)) (ht0 : 0 < t) :
    0 < switchingFn 2 1 (strongΛR y0 t) (segX y0 t) := by
  obtain ⟨hy2, hy4⟩ := hmax_y_mem hy0 hy1
  obtain ⟨-, hW4⟩ := hmax_W_mem hy0 ht
  have hpos : 0 < y0 := lt_trans (by positivity) hy0
  have hW1 : 1 < exp (√3 * y0 * t) :=
    one_lt_exp_iff.2 (mul_pos (by linarith [hmax_one_lt_sqrt3_mul hy0]) ht0)
  rw [chi32_eq y0 hy0 hy1 t ht]
  have h2W : 0 < 2 - exp (√3 * y0 * t) := by nlinarith
  refine div_pos (mul_pos two_pos (hmaxF_pos hy2.le ?_ hW4)) (by positivity)
  nlinarith

/-- **Lemma 7.5.3** (`lem:H-max-6k+2`). Fix `y₀ ∈ (1/√3, 1)` and `t_sw`, and let `χ_ij` be the
switching functions of the costate trajectory of Theorem 7.5.1 (normalized by `λ_cost = -1`),
with constant control `e₃`. Then the maximum principle holds: `χ₃₁(t) ≥ 0` and `χ₃₂(t) ≥ 0` for
`t ∈ [0, t_sw]`, and they vanish only at `χ₃₂(0) = 0` and `χ₃₁(t_sw) = 0`. (`χ₃₁` is
`switchingFn 2 0`, `χ₃₂` is `switchingFn 2 1`.) -/
theorem lemma7_5_3 (y0 : ℝ) (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) (Λ₁ ΛR : ℝ → Mat2)
    (h : IsStrongLift y0 Λ₁ ΛR (-1)) :
    ∀ t ∈ Set.Icc 0 (switchTime y0),
      0 ≤ switchingFn 2 0 (ΛR t) (segX y0 t) ∧ 0 ≤ switchingFn 2 1 (ΛR t) (segX y0 t) ∧
        (switchingFn 2 0 (ΛR t) (segX y0 t) = 0 → t = switchTime y0) ∧
        (switchingFn 2 1 (ΛR t) (segX y0 t) = 0 → t = 0) := by
  -- The lift is the explicit one.
  have hΛ : ∀ t ∈ Icc 0 (switchTime y0), ΛR t = strongΛR y0 t := fun t ht => by
    simpa using (strongLift_unique y0 hy0 hy1 Λ₁ ΛR (-1) h t ht).2
  -- The symmetry `χ₃₁(t) = χ₃₂(t_sw - t)`.
  have hsym : ∀ t ∈ Icc 0 (switchTime y0),
      switchingFn 2 0 (strongΛR y0 t) (segX y0 t) =
        switchingFn 2 1 (strongΛR y0 (switchTime y0 - t)) (segX y0 (switchTime y0 - t)) := by
    intro t ht
    have := chi31_eq_chi32 y0 hy0 hy1 (switchTime y0 - t)
      ⟨by linarith [ht.2], by linarith [ht.1]⟩
    rwa [sub_sub_cancel] at this
  intro t ht
  have ht' : switchTime y0 - t ∈ Icc 0 (switchTime y0) :=
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  rw [hΛ t ht, hsym t ht]
  refine ⟨hmax_chi32_nonneg hy0 hy1 ht', hmax_chi32_nonneg hy0 hy1 ht, fun h0 => ?_, fun h0 => ?_⟩
  · by_contra hne
    have hlt : t < switchTime y0 := lt_of_le_of_ne ht.2 hne
    exact (hmax_chi32_pos hy0 hy1 ht' (by linarith)).ne' h0
  · by_contra hne
    exact (hmax_chi32_pos hy0 hy1 ht (lt_of_le_of_ne ht.1 (Ne.symm hne))).ne' h0

end SmoothedPolygons
