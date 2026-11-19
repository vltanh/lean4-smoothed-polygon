module

public import Basic.Analysis.SpecialFunctions.Log.Bounds
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import SmoothedPolygons.Ch14.ArcStepClosed

/-!
# Chapter 14, the unstable curve: the exit criterion (Lemma 6.4 of the note)

Part of the formalization's proof, without computer assistance, of the fact behind Figure 14.2
(`UnstableCurveLeavesStarDomain`, `SmoothedPolygons/Ch14/UnstableCurve.lean`). **Departure from
the paper**, by the user's decision: the book reads the fact off a computed figure (Figure 14.2,
TeX 11951–11991; REPORT.md E88). The proof is written up in `docs/unstable-curve.pdf` (the
note).

This file is the parameter part of **Lemma 6.4** of the note: if `Y ≥ 16/5`, `f₀ > 0` and
`f₀ ≥ q (1 - 1/Y)`, then `f > 0` on `[0, log Y)`, so the arc does not switch before it leaves the
star domain (`f_pos_of_Y_ge`; on the flow, `arcLeavesStarDomain_of_Y_ge`,
`SmoothedPolygons/Ch14/ArcConditions.lean`). The switching function in the variable `y = e^τ` is
`φ(y) = y f(log y) = f₀ + β_Y(y) - q (y - 1)/y`, where the bare part
`β_Y(y) = Y log y - (y - 1) - (Y - 1)(y - 1)/y` does not involve the costate. The proof shows
`β_Y ≥ 0` on `[1, Y]` by monotonicity:
* `Y ↦ β_Y(Y)` increases on `[16/5, ∞)` (its derivative is `log Y - 1 + 1/Y² > 0` there, as
  `log Y ≥ log(16/5) > 1`), and `β_Y(Y) > 0` at `Y = 16/5` because `log(16/5) > 297/256`
  (`Real.log_sixteen_div_five_gt`, four terms of the series of `2 artanh(11/21)`);
* `β_Y(1) = 0`, and `β_Y'(y) = -(y - 1)(y - (Y - 1))/y²`, so `β_Y` increases on `[1, Y - 1]` and
  decreases on `[Y - 1, Y]`.
Then `φ(y) ≥ f₀ - q (y - 1)/y > 0` on `[1, Y)` by a case split on the sign of `q`.
-/

@[expose] public section

namespace SmoothedPolygons

open Set

/-! ### The bare switching function `β_Y` -/

/-- The derivative of `β_Y(y) = Y log y - y + 2 - Y + (Y - 1)/y` (this is
`Y log y - (y - 1) - (Y - 1)(y - 1)/y` for `y ≠ 0`): `-(y - 1)(y - (Y - 1))/y²`. -/
private theorem hasDerivAt_betaY (Y : ℝ) {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (fun t ↦ Y * Real.log t - t + 2 - Y + (Y - 1) * t⁻¹)
      (-(y - 1) * (y - (Y - 1)) / y ^ 2) y := by
  have h := ((((Real.hasDerivAt_log hy).const_mul Y).sub (hasDerivAt_id' y)).add_const
    (2 - Y)).add ((hasDerivAt_inv hy).const_mul (Y - 1))
  convert h using 1
  · funext t
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  · field_simp
    ring

/-- `β_Y(Y) > 0` for `Y ≥ 16/5`: `G(t) = t log t - 2t + 3 - 1/t` (which is `β_t(t)`) has derivative
`log t - 1 + 1/t² > 0` on `(16/5, ∞)`, and `G(16/5) = (16/5)(log(16/5) - 297/256) > 0`. -/
private theorem betaY_self_pos {Y : ℝ} (hY : 16 / 5 ≤ Y) :
    0 < Y * Real.log Y - Y + 2 - Y + (Y - 1) * Y⁻¹ := by
  set G : ℝ → ℝ := fun t ↦ t * Real.log t - 2 * t + 3 - t⁻¹ with hG
  have hd : ∀ t : ℝ, t ≠ 0 → HasDerivAt G (Real.log t - 1 + (t ^ 2)⁻¹) t := by
    intro t ht
    have h := ((((hasDerivAt_id' t).mul (Real.hasDerivAt_log ht)).sub
      ((hasDerivAt_id' t).const_mul 2)).add_const 3).sub (hasDerivAt_inv ht)
    convert h using 1
    rw [mul_inv_cancel₀ ht]
    ring
  have hmono : MonotoneOn G (Ici (16 / 5)) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t ↦ Real.log t - 1 + (t ^ 2)⁻¹)
      (convex_Ici _)
      (fun t ht ↦ (hd t (by linarith [mem_Ici.1 ht])).continuousAt.continuousWithinAt)
      (fun t ht ↦ ?_) (fun t ht ↦ ?_)
    · rw [interior_Ici] at ht
      exact (hd t (by linarith [mem_Ioi.1 ht])).hasDerivWithinAt
    · rw [interior_Ici] at ht
      have hl : Real.log (16 / 5) < Real.log t := Real.log_lt_log (by norm_num) (mem_Ioi.1 ht)
      have := Real.log_sixteen_div_five_gt
      have := inv_nonneg.2 (sq_nonneg t)
      linarith
  have h0 : 0 < G (16 / 5) := by
    simp only [hG]
    have := Real.log_sixteen_div_five_gt
    rw [show ((16 : ℝ) / 5)⁻¹ = 5 / 16 by norm_num]
    linarith
  have hle := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 hY) hY
  have e : Y * Real.log Y - Y + 2 - Y + (Y - 1) * Y⁻¹ = G Y := by
    simp only [hG]
    field_simp
    ring
  rw [e]
  linarith

/-- `β_Y ≥ 0` on `[1, Y]` when `Y ≥ 2` and `β_Y(Y) ≥ 0`: `β_Y(1) = 0`, `β_Y` increases on
`[1, Y - 1]` and decreases on `[Y - 1, Y]` (`hasDerivAt_betaY`). -/
private theorem betaY_nonneg {Y y : ℝ} (hY : 2 ≤ Y)
    (hYY : 0 ≤ Y * Real.log Y - Y + 2 - Y + (Y - 1) * Y⁻¹) (hy1 : 1 ≤ y) (hyY : y ≤ Y) :
    0 ≤ Y * Real.log y - y + 2 - Y + (Y - 1) * y⁻¹ := by
  set B : ℝ → ℝ := fun t ↦ Y * Real.log t - t + 2 - Y + (Y - 1) * t⁻¹ with hB
  have hcont : ∀ D : Set ℝ, (∀ t ∈ D, 0 < t) → ContinuousOn B D := fun D hD t ht ↦
    (hasDerivAt_betaY Y (hD t ht).ne').continuousAt.continuousWithinAt
  rcases le_total y (Y - 1) with h | h
  · have hmono : MonotoneOn B (Icc 1 (Y - 1)) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg
        (f' := fun t ↦ -(t - 1) * (t - (Y - 1)) / t ^ 2) (convex_Icc _ _)
        (hcont _ fun t ht ↦ by linarith [ht.1]) (fun t ht ↦ ?_) (fun t ht ↦ ?_)
      · rw [interior_Icc] at ht
        exact (hasDerivAt_betaY Y (by linarith [ht.1] : (0:ℝ) < t).ne').hasDerivWithinAt
      · rw [interior_Icc] at ht
        apply div_nonneg _ (sq_nonneg _)
        nlinarith [ht.1, ht.2]
    have h1 : B 1 = 0 := by
      simp only [hB, Real.log_one, inv_one]
      ring
    have hle := hmono ⟨le_refl 1, by linarith⟩ ⟨hy1, h⟩ hy1
    rw [h1] at hle
    exact hle
  · have hanti : AntitoneOn B (Icc (Y - 1) Y) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos
        (f' := fun t ↦ -(t - 1) * (t - (Y - 1)) / t ^ 2) (convex_Icc _ _)
        (hcont _ fun t ht ↦ by linarith [ht.1]) (fun t ht ↦ ?_) (fun t ht ↦ ?_)
      · rw [interior_Icc] at ht
        exact (hasDerivAt_betaY Y (by linarith [ht.1] : (0:ℝ) < t).ne').hasDerivWithinAt
      · rw [interior_Icc] at ht
        apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
        nlinarith [ht.1, ht.2]
    exact le_trans hYY (hanti ⟨h, hyY⟩ ⟨by linarith, le_refl Y⟩ hyY)

namespace ArcParams

variable (a : ArcParams)

/-- **Lemma 6.4** of the note, the parameter part (the exit criterion). If `Y ≥ 16/5`, `f₀ > 0` and
`f₀ ≥ q (1 - 1/Y)` (no sign condition on `q`), then `f > 0` on `[0, log Y)`: the arc does not
switch before it leaves the star domain.

Route: for `τ ∈ [0, log Y)` put `y = e^{τ} ∈ [1, Y)`; then
`y f(τ) = φ(y) = f₀ + β_Y(y) - q (y - 1)/y`.
`β_Y(y) ≥ 0` (`betaY_nonneg`, `betaY_self_pos`, see the module docstring). If `q ≤ 0`,
`φ(y) ≥ f₀ > 0`. If `q > 0`, `(y - 1)/y = 1 - 1/y < 1 - 1/Y`, so `φ(y) > f₀ - q (1 - 1/Y) ≥ 0`. -/
theorem f_pos_of_Y_ge (hY : 16 / 5 ≤ a.Y) (h1 : 0 < a.f0) (hq : a.q * (1 - 1 / a.Y) ≤ a.f0)
    {τ : ℝ} (hτ : τ ∈ Ico 0 (Real.log a.Y)) : 0 < a.f τ := by
  obtain ⟨hτ0, hτY⟩ := hτ
  have hY0 : 0 < a.Y := by linarith
  set y := Real.exp τ with hydef
  have hy1 : 1 ≤ y := Real.one_le_exp hτ0
  have hyY : y < a.Y := by rw [← Real.exp_log hY0]; exact Real.exp_lt_exp.2 hτY
  have hy0 : 0 < y := by positivity
  have hτlog : Real.log y = τ := Real.log_exp τ
  -- `f(τ) = (f₀ + β_Y(y) - q (y - 1)/y)/y`, `β_Y(y) = Y τ - (y - 1) - (Y - 1)(y - 1)/y`
  have e : a.f τ = (a.f0 + (a.Y * τ * y - (y - 1) * y - (a.Y - 1) * (y - 1)) / y -
      a.q * (y - 1) / y) / y := by
    unfold f A B
    rw [Real.exp_neg, show -2 * τ = -(2 * τ) by ring, Real.exp_neg, two_mul, Real.exp_add]
    field_simp
    ring
  -- `β_Y ≥ 0` on `[1, Y]` (Lemma 6.4: monotonicity)
  have hβ := betaY_nonneg (by linarith : (2:ℝ) ≤ a.Y) (betaY_self_pos hY).le hy1 hyY.le
  rw [hτlog] at hβ
  have hb : 0 ≤ a.Y * τ * y - (y - 1) * y - (a.Y - 1) * (y - 1) := by
    have e2 : a.Y * τ * y - (y - 1) * y - (a.Y - 1) * (y - 1) =
        y * (a.Y * τ - y + 2 - a.Y + (a.Y - 1) * y⁻¹) := by
      field_simp
      ring
    rw [e2]
    exact mul_nonneg hy0.le hβ
  rw [e]
  apply div_pos _ hy0
  rcases le_or_gt a.q 0 with hq0 | hq0
  · have : 0 ≤ -a.q * (y - 1) / y := div_nonneg (mul_nonneg (by linarith) (by linarith)) hy0.le
    have : 0 ≤ (a.Y * τ * y - (y - 1) * y - (a.Y - 1) * (y - 1)) / y := div_nonneg hb hy0.le
    have e2 : -a.q * (y - 1) / y = -(a.q * (y - 1) / y) := by ring
    linarith
  · -- `(y - 1)/y = 1 - 1/y < 1 - 1/Y`
    have hlt : a.q * (y - 1) / y < a.q * (1 - 1 / a.Y) := by
      rw [mul_div_assoc]
      apply mul_lt_mul_of_pos_left _ hq0
      rw [div_lt_iff₀ hy0]
      have : 1 / a.Y * y < 1 := by rw [div_mul_eq_mul_div, one_mul, div_lt_one hY0]; exact hyY
      nlinarith
    have : 0 ≤ (a.Y * τ * y - (y - 1) * y - (a.Y - 1) * (y - 1)) / y := div_nonneg hb hy0.le
    linarith

end ArcParams

end SmoothedPolygons
