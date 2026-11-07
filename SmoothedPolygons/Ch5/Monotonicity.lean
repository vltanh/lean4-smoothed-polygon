module

public import SmoothedPolygons.Ch5.Hexagon

/-!
# Monotonicity of the area bounds (Lemma 5.0.7)

Lemma 5.0.7 (`lem:compactification-lemma`, TeX 4353–4466) studies the functions `area_i(x, y)` and
the density bound `δ(x, y)` of `SmoothedPolygons.Ch5.Hexagon` on the star domain, in the
coordinates `z = x + iy`. By Lemma 5.0.4 and Theorem 4.4.1, with
`ρ₀ = (1 + √3x)/(√3y)`, `ρ₁ = (1 - √3x)/(√3y)`, `ρ₂ = (3(x² + y²) - 1)/(2√3y)` (`ρⱼ(Φ(x, y))`):

  `area₀ = (√3/4)(ρ₀ρ₂ - 2√(ρ₀ρ₁²ρ₂))`  (`areaFn_zero_eq`, TeX 4379),
  `area₂(x, y) = area₀(-x, y)`, since `ρ₀(-x, y) = ρ₁(x, y)` (`areaFn_two_eq`, TeX 4442).

## Statements and the book's proofs

The book uses `ρ₀,ₓ > 0`, `ρ₁,ₓ < 0` and `ρ₂,ₓ = √3x/y` throughout.

* (1) `lemma5_0_7_1` (TeX 4377–4398): `∂ₓ area₀ > 0` on `{y ≥ 1, 0 < x < 1/√3}`, because
  `ρ₀,ₓ ρ₂ > 0`, `ρ₀ ρ₂,ₓ > 0` and `-(ρ₀ρ₁²ρ₂)ₓ > 0`, "a polynomial inequality in `x` and `y`,
  which is easily checked". (With `s = √3x ∈ (0, 1)` and `c = 3y² - 1 ≥ 2`, `ρ₀ρ₁²ρ₂` is a positive
  multiple of `f(s) = (1 + s)(1 - s)²(s² + c)` and `f'(s) = (s - 1)(5s³ + s² + (3c - 2)s + c) < 0`.)
* (2) `lemma5_0_7_2` (TeX 4410–4430): `(ρ₀ + ρ₁)ρ₂` has `x`-derivative `2x/y² > 0`, and
  `(ρ₀ρ₁²ρ₂)ₓ/√ρ₁ + (ρ₀²ρ₁ρ₂)ₓ/√ρ₀ < 0` for `x > 0`, `y ≥ √3`: both numerators are negative for
  `x ≥ 1/4`; for `0 ≤ x ≤ 1/4` both terms decrease in `x` and their sum vanishes at `x = 0`
  ("routine polynomial checks").
* (3) `lemma5_0_7_3` (TeX 4432–4448): the function (5.0.1) `Σ_i I_i area_i` is continuous on `𝔥*`
  (`continuousOn_sum_indicator_areaFn`: `area_i = 0` on the boundary of `h_i`, where `I_i`
  jumps); it is increasing in `x ∈ (0, 1/√3)` on `h₀ \ h₂` (by (1)) and on `h₀ ∩ h₂` (by (2)),
  hence on `h₀ ∩ {x > 0, y ≥ √3}`; it is even in `x` (`areaFn_two_eq`), so it is least at `x = 0`.
  **Gap (inventory, Part I §6):** the book treats only `h₀ ∩ {x > 0, y ≥ √3}` and does not show
  that the points with `x > 0` lie in `h₀`, nor how `I₁area₁` enters. Repair along its lines: for
  `y ≥ √3`, `x ≥ 0`, `T₀ - T₀^ext` has the sign of
  `(1 + √3x)(3x² + 3y² - 1) - 8(1 - √3x)² ≥ x(3√3x² - 21x + 24√3) ≥ 0` (the quadratic has negative
  discriminant), so `{x ≥ 0, y ≥ √3} ⊆ h₀`, and symmetrically `{x ≤ 0, y ≥ √3} ⊆ h₂`; the statement
  of (3) involves only `I₀area₀ + I₂area₂`, so `h₁` does not enter.
* (4) `lemma5_0_7_4` (TeX 4450–4465): `area₀(0, y) = area₂(0, y) = (√3/4)√(ρ₀ρ₂)(√(ρ₀ρ₂) - 2ρ₁)`
  is increasing in `y` (`ρ₀ρ₂ = (y² - 1/3)/(2y²)` and `√(ρ₀ρ₂) - 2ρ₁` increase), so by (3) and
  `I₁area₁ ≥ 0`, `δ(x, y) ≥ δ(0, y) ≥ δ(0, 4.5) = 0.9059… > δ_oct = 0.9024…`. Proof to write:
  certified rational bounds on `√3`, `√(ρ₀ρ₂)` at `y = 4.5` and on `ln 2` (`Real.log_two_gt_d9`,
  `Real.log_two_lt_d9`); the margin is `0.0035`.

The inventory's numeric checks (`notes/plan_ch5_8_16/scripts/ch5check*.py`) found no violation of
(1)–(3) on grids. Size: 600–1,200 lines (polynomial inequalities after clearing square roots;
`nlinarith`/`positivity`, and sign arguments for the derivatives).
-/

@[expose] public section

namespace SmoothedPolygons

open MeasureTheory Set

/-- `area₀` in terms of the star functions (TeX 4379): on `𝔥*`,
`area₀(x, y) = (√3/4)(ρ₀ρ₂ - 2√(ρ₀ρ₁²ρ₂))` with `ρⱼ = ρⱼ(Φ(x, y))`. -/
theorem areaFn_zero_eq {x y : ℝ} (hz : (x, y) ∈ starDomain) :
    areaFn 0 (x, y) = √3 / 4 * (ρ₀ (Φ x y) * ρ₂ (Φ x y) -
      2 * √(ρ₀ (Φ x y) * ρ₁ (Φ x y) ^ 2 * ρ₂ (Φ x y))) := by
  sorry

/-- The reflection symmetry of the areas (TeX 4442): `area₂(x, y) = area₀(-x, y)` and
`(x, y) ∈ h₂ ↔ (-x, y) ∈ h₀`, since `ρ₀(-x, y) = ρ₁(x, y)` and `ρ₂(-x, y) = ρ₂(x, y)`. -/
theorem areaFn_two_eq {x y : ℝ} (hz : (x, y) ∈ starDomain) :
    areaFn 2 (x, y) = areaFn 0 (-x, y) ∧ ((x, y) ∈ hRegion 2 ↔ (-x, y) ∈ hRegion 0) := by
  sorry

/-- **Equation (5.0.1)** (`eqn:area0-area2`, TeX 4433–4437): `Σ_i I_i area_i` is continuous on
`𝔥*`, because `area_i = 0` on the boundary of `h_i`, where `I_i` jumps. -/
theorem continuousOn_sum_indicator_areaFn :
    ContinuousOn (fun z ↦ ∑ i : Fin 3, (hRegion i).indicator (areaFn i) z) starDomain := by
  sorry

/-- **Lemma 5.0.7 (1)** (`lem:compactification-lemma`). For all `y ≥ 1`, `area₀(x, y)` is
monotonically increasing in `x` on `0 < x < 1/√3`. -/
theorem lemma5_0_7_1 {y : ℝ} (hy : 1 ≤ y) :
    MonotoneOn (fun x ↦ areaFn 0 (x, y)) (Ioo 0 (1 / √3)) := by
  sorry

/-- **Lemma 5.0.7 (2)** (`lem:compactification-lemma`). For all `y ≥ √3`,
`area₀(x, y) + area₂(x, y)` is monotonically increasing in `x` on `0 < x < 1/√3`. -/
theorem lemma5_0_7_2 {y : ℝ} (hy : √3 ≤ y) :
    MonotoneOn (fun x ↦ areaFn 0 (x, y) + areaFn 2 (x, y)) (Ioo 0 (1 / √3)) := by
  sorry

/-- **Lemma 5.0.7 (3)** (`lem:compactification-lemma`). For every fixed `y ≥ √3`, the function
`I₀(x, y) area₀(x, y) + I₂(x, y) area₂(x, y)` is minimized at `x = 0` on `x ∈ (-1/√3, 1/√3)`.
(The book's proof is incomplete; see the module docstring.) -/
theorem lemma5_0_7_3 {y : ℝ} (hy : √3 ≤ y) {x : ℝ} (hx : x ∈ Ioo (-(1 / √3)) (1 / √3)) :
    (hRegion 0).indicator (areaFn 0) (0, y) + (hRegion 2).indicator (areaFn 2) (0, y) ≤
      (hRegion 0).indicator (areaFn 0) (x, y) + (hRegion 2).indicator (areaFn 2) (x, y) := by
  sorry

/-- **Lemma 5.0.7 (4)** (`lem:compactification-lemma`). For all `x ∈ (-1/√3, 1/√3)` and all
`y ≥ 4.5`, `δ(x, y) > δ_oct`. -/
theorem lemma5_0_7_4 {x y : ℝ} (hx : x ∈ Ioo (-(1 / √3)) (1 / √3)) (hy : 9 / 2 ≤ y) :
    octagonDensity < densityBound (x, y) := by
  sorry

end SmoothedPolygons
