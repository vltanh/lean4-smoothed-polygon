module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# A lower bound for the real logarithm

* `Real.log_sixteen_div_five_gt`: `297/256 < log(16/5)`.

It is a partial sum of the series `log(1 + 1/a) = Σ_k 2/(2k + 1) · (1/(2a + 1))^{2k + 1}`
(`Real.hasSum_log_one_add_inv`), whose terms are nonnegative for `a > 0`.
-/

@[expose] public section

namespace Real

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
