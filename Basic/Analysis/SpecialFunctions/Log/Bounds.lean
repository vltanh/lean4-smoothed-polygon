module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Two lower bounds for the real logarithm

* `Real.two_mul_sub_one_div_add_one_le_log`: `2(s - 1)/(s + 1) ≤ log s` for `s ≥ 1`;
* `Real.log_sixteen_div_five_gt`: `297/256 < log(16/5)`.

Both are partial sums of the series `log(1 + 1/a) = Σ_k 2/(2k + 1) · (1/(2a + 1))^{2k + 1}`
(`Real.hasSum_log_one_add_inv`), whose terms are nonnegative for `a > 0`.
-/

@[expose] public section

namespace Real

/-- **`log s ≥ 2(s - 1)/(s + 1)` for `s ≥ 1`.**

Proof: for `s = 1` both sides are `0`. For `s > 1`, `Real.hasSum_log_one_add_inv` with
`a = 1/(s - 1)` (`1 + a⁻¹ = s`, `1/(2a + 1) = (s - 1)/(s + 1)`) writes `log s` as a series of
nonnegative terms `2/(2k + 1) · ((s - 1)/(s + 1))^{2k + 1}` whose first term is the bound
(`sum_le_hasSum (Finset.range 1)`). Alternatively: `h(s) = log s - 2(s - 1)/(s + 1)` has `h(1) = 0`
and `h'(s) = (s - 1)²/(s (s + 1)²) ≥ 0`. -/
theorem two_mul_sub_one_div_add_one_le_log {s : ℝ} (hs : 1 ≤ s) :
    2 * (s - 1) / (s + 1) ≤ Real.log s := by
  rcases hs.lt_or_eq with hs | rfl
  · have ha : 0 < 1 / (s - 1) := one_div_pos.2 (by linarith)
    have h := Real.hasSum_log_one_add_inv ha
    rw [show 1 + (1 / (s - 1))⁻¹ = s by field_simp; ring] at h
    have h0 := sum_le_hasSum (Finset.range 1) (fun k _ => by positivity) h
    rw [Finset.sum_range_one] at h0
    have e2 : 2 * (1 / (s - 1)) + 1 = (s + 1) / (s - 1) := by
      have : s - 1 ≠ 0 := by linarith
      field_simp
      ring
    rw [e2, one_div_div] at h0
    norm_num at h0
    rw [mul_div_assoc]
    linarith
  · simp

/-- **`log(16/5) > 297/256`** (`297/256 = 1.16016`; the true value is `1.16315`).

Proof: `Real.hasSum_log_one_add_inv` with `a = 5/11` (`1 + a⁻¹ = 16/5`, `1/(2a + 1) = 11/21`;
this is `log(16/5) = 2 atanh(11/21)`); the terms are nonnegative, so the partial sum of the first
four, `2 (x + x³/3 + x⁵/5 + x⁷/7)` at `x = 11/21`, which is `73269045344/63038098935 = 1.16230`,
is a lower bound (`sum_le_hasSum (Finset.range 4)`, then `norm_num [Finset.sum_range_succ]`). -/
theorem log_sixteen_div_five_gt : 297 / 256 < Real.log (16 / 5) := by
  have h := Real.hasSum_log_one_add_inv (by norm_num : (0 : ℝ) < 5 / 11)
  rw [show (1 : ℝ) + (5 / 11)⁻¹ = 16 / 5 by norm_num] at h
  have h0 := sum_le_hasSum (Finset.range 4) (fun k _ => by positivity) h
  norm_num [Finset.sum_range_succ] at h0
  linarith

end Real
