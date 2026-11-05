module

public import SmoothedPolygons.Ch7.ConstantControl

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

/-! ### The `e₃`-trajectory from `z₀ = i y₀` in closed form -/

/-- `X(z₀, t) = Φ(z(t))` with `z(t) = (W - 1)/√3 + i y₀ W`, `W = exp(√3 y₀ t)`: the trajectory moves
along the straight line from the ideal vertex `-1/√3` (§7.2). -/
theorem segX_eq (y0 t : ℝ) (hy0 : 0 < y0) :
    segX y0 t = Φ ((Real.exp (√3 * y0 * t) - 1) / √3) (y0 * Real.exp (√3 * y0 * t)) := by
  sorry

/-- `g₀(z₀, t)` in closed form, `W = exp(√3 y₀ t)`. -/
theorem segG_eq (y0 t : ℝ) (hy0 : 0 < y0) :
    segG y0 t = !![1, -(Real.exp (√3 * y0 * t) - 1) / √3;
      (1 - (Real.exp (√3 * y0 * t))⁻¹) / (√3 * y0 ^ 2),
      1 - (Real.exp (√3 * y0 * t) - 2 + (Real.exp (√3 * y0 * t))⁻¹) / (3 * y0 ^ 2)] := by
  sorry

/-- The `e₃`-trajectory solves the state equations with constant control `e₃`. -/
theorem seg_solution (y0 t : ℝ) (hy0 : 0 < y0) :
    HasDerivAtEntrywise (segG y0) (segG y0 t * segX y0 t) t ∧
      HasDerivAtEntrywise (segX y0)
        (controlP (vertex 2) (segX y0 t) * segX y0 t -
          segX y0 t * controlP (vertex 2) (segX y0 t)) t ∧
      segG y0 0 = 1 ∧ segX y0 0 = Φ 0 y0 ∧ ∀ s, (segG y0 s).det = 1 := by
  sorry

/-- On `[0, t_sw]` the `e₃`-trajectory stays in the star domain. -/
theorem segX_star (y0 : ℝ) (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) (t : ℝ)
    (ht : t ∈ Set.Icc 0 (switchTime y0)) : IsStarState (segX y0 t) := by
  sorry

/-- The strong boundary condition `z(z₀, t_sw) = R⁻¹ · z₀` (`eqn:poly-z`), in the Lie algebra:
`X(z₀, t_sw) = R⁻¹ X₀ R`. -/
theorem segX_switchTime (y0 : ℝ) (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) :
    segX y0 (switchTime y0) = R⁻¹ * Φ 0 y0 * R := by
  sorry

/-- The trace of `h = g(t_sw) R⁻¹` is `4/(1 + 3y₀²)` (proof of Theorem 7.5.1). -/
theorem trace_segG_switchTime (y0 : ℝ) (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) :
    (segG y0 (switchTime y0) * R⁻¹).trace = 4 / (1 + 3 * y0 ^ 2) := by
  sorry

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
  sorry

end SmoothedPolygons
