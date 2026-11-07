module

public import SmoothedPolygons.Ch5.Compactification
public import SmoothedPolygons.Ch5.Monotonicity

/-!
# The density bound near the edge `x = 1/√3` (proof of Theorem 5.0.2, the half-plane `Π₀⁺`)

The proof of Theorem 5.0.2 (TeX 4491–4512) excludes the points of the half-plane
`Π₀⁺ = {y > 15(1/√3 - x)}` with `1 ≤ y ≤ 4.5`: there

  `δ(z) ≥ δ₀(z) := 3/4 + area₀(z)/√3 > δ_oct`

for all `z ∈ 𝔥* ∩ Π₀⁺ ∩ {1 ≤ y ≤ 4.5} ⊆ h₀`.

## Statements and the book's proof

* `edgeSlab_subset_hRegion`: `𝔥* ∩ Π₀⁺ ∩ {1 ≤ y ≤ 4.5} ⊆ h₀` (asserted at TeX 4498). The
  inventory's check finds `T₀ - T₀^ext ≥ 0.31` on the line `y = 15(1/√3 - x)`; with
  Lemma 5.0.4 it is a polynomial inequality in `x, y` (increasing in `x`).
* `octagonDensity_lt_edgeLine` (TeX 4502–4509): by Lemma 5.0.7 (1) (`lemma5_0_7_1`), `area₀` is
  increasing in `x` on each horizontal line `y = y₀ ≥ 1`, so it suffices to check the inequality on
  the line `y = 15(1/√3 - x)`, `y ∈ [1, 4.5]`, i.e. `x ∈ [0.277, 0.511]`: "On this domain, we have
  `δ₀(x, y(x)) > δ_oct`" (a source comment calls it "a single variable calculation"; "the graph is
  clear"). The inventory's check: the minimum is `0.904209` at `y = 4.5`, a margin of `0.0018`
  over `δ_oct = 0.902414`. Proof to write: a certified one-variable bound, either by showing that
  `δ₀` decreases along the line in `y` and checking `y = 4.5`, or by subdividing `[1, 4.5]` with
  rational bounds on `√3` and on the square root in `area₀` (`areaFn_zero_eq`), and
  `Real.log_two_gt_d9`, `Real.log_two_lt_d9` for `δ_oct`.
* `octagonDensity_lt_densityBound_of_mem_edgeHalfPlane`: the conclusion, from the two statements
  above, `lemma5_0_7_1`, `areaFn_nonneg_of_mem_hRegion` (the other terms of `δ` are `≥ 0`) and
  `densityBound_eq`.

Size: 300–800 lines (mostly the certified one-variable bound).
-/

@[expose] public section

namespace SmoothedPolygons

open Set

/-- `𝔥* ∩ Π₀⁺ ∩ {1 ≤ y ≤ 4.5} ⊆ h₀` (proof of Theorem 5.0.2, TeX 4498). -/
theorem edgeSlab_subset_hRegion :
    starDomain ∩ edgeHalfPlane ∩ {z | 1 ≤ z.2 ∧ z.2 ≤ 9 / 2} ⊆ hRegion 0 := by
  sorry

/-- **The one-variable estimate of the proof of Theorem 5.0.2** (TeX 4502–4509): along the line
`y = 15(1/√3 - x)` bounding `Π₀⁺`, for `1 ≤ y ≤ 4.5`, `δ₀(x, y) = 3/4 + area₀(x, y)/√3 > δ_oct`. -/
theorem octagonDensity_lt_edgeLine {y : ℝ} (hy : y ∈ Icc 1 (9 / 2)) :
    octagonDensity < 3 / 4 + areaFn 0 (1 / √3 - y / 15, y) / √3 := by
  sorry

/-- **The half-plane `Π₀⁺` in the proof of Theorem 5.0.2** (TeX 4491–4512): for
`z ∈ 𝔥* ∩ Π₀⁺` with `1 ≤ y ≤ 4.5`, `δ(z) ≥ δ₀(z) > δ_oct`. -/
theorem octagonDensity_lt_densityBound_of_mem_edgeHalfPlane {z : ℝ × ℝ} (hz : z ∈ starDomain)
    (hP : z ∈ edgeHalfPlane) (hy₁ : 1 ≤ z.2) (hy₂ : z.2 ≤ 9 / 2) :
    octagonDensity < densityBound z := by
  sorry

end SmoothedPolygons
