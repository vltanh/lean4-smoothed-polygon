module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import SmoothedPolygons.Ch5.Compactification
public import SmoothedPolygons.Ch5.Monotonicity

/-!
# The density bound near the edge `x = 1/√3` (proof of Theorem 5.0.2, the half-plane `Π₀⁺`)

The proof of Theorem 5.0.2 (TeX 4491–4512) excludes the points of the half-plane
`Π₀⁺ = {y > 15(1/√3 - x)}` with `1 ≤ y ≤ 4.5`: there

  `δ(z) ≥ δ₀(z) := 3/4 + area₀(z)/√3 > δ_oct`

for all `z ∈ 𝔥* ∩ Π₀⁺ ∩ {1 ≤ y ≤ 4.5} ⊆ h₀`.

## Statements and proofs

* `edgeSlab_subset_hRegion`: `𝔥* ∩ Π₀⁺ ∩ {1 ≤ y ≤ 4.5} ⊆ h₀` (asserted at TeX 4499). By
  Lemma 5.0.4, `z ∈ h₀` iff `4ρ₁² ≤ ρ₀ρ₂`. On `Π₀⁺`, `0 < ρ₁ = (1 - √3x)/(√3y) < 1/15`; with
  `y ≤ 4.5` also `x > 1/√3 - 0.3 > 0`, so `ρ₀ ≥ 1/(√3y)`, and `y ≥ 1` gives `ρ₂ ≥ y/√3`; hence
  `ρ₀ρ₂ ≥ 1/3 > 4/225 > 4ρ₁²`.
* `octagonDensity_lt_edgeLine` (TeX 4502–4509): by Lemma 5.0.7 (1) (`lemma5_0_7_1`), `area₀` is
  increasing in `x` on each horizontal line `y = y₀ ≥ 1`, so it suffices to check the inequality on
  the line `y = 15(1/√3 - x)`, `y ∈ [1, 4.5]`, i.e. `x ∈ [0.277, 0.511]`: "On this domain, we have
  `δ₀(x, y(x)) > δ_oct`" (a source comment calls it "a single variable calculation"; "the graph is
  clear"). The certified bound: on the line `√3x = 1 - √3y/15`, so `ρ₁ = 1/15` exactly, and
  `6y ρ₀ρ₂ = (2 - √3y/15)(226y/75 - 2√3/15)`, so `ρ₀ρ₂ - 0.7268` is, after multiplication by
  `6y`, a concave quadratic in `y` (with `√3 < 1.7321`) that is positive at `y = 1` and at
  `y = 4.5`, hence on `[1, 4.5]`. Then `δ₀ = 3/4 + (ρ₀ρ₂ - (2/15)√(ρ₀ρ₂))/4`
  (`areaFn_zero_eq`), and `√(ρ₀ρ₂) ≥ 0.8525` gives `δ₀ ≥ 0.903`, while `δ_oct < 0.903` from
  `√2 > 1.4142` and `ln 2 > 0.6931471803` (`Real.log_two_gt_d9`). Numerically the minimum of `δ₀`
  on the line is `0.904209` at `y = 4.5`, a margin of `0.0018` over `δ_oct = 0.902414`. (`δ₀` is
  not monotone along the line: `ρ₀ρ₂` increases on `[1, 2/√(226/75)] ≈ [1, 1.152]`; concavity is
  what reduces the check to the endpoints.)
* `octagonDensity_lt_densityBound_of_mem_edgeHalfPlane`: the conclusion, from the two statements
  above, `lemma5_0_7_1`, `areaFn_nonneg_of_mem_hRegion` (the other terms of `δ` are `≥ 0`) and
  `densityBound_eq`.
-/

@[expose] public section

namespace SmoothedPolygons

open Set

/-- `1.732 < √3 < 1.7321`. -/
private lemma eb_sqrt3_bounds : (1732 / 1000 : ℝ) < √3 ∧ √3 < 17321 / 10000 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- `ρ₀(Φ(x, y)) = (1 + √3x)/(√3y)`. -/
private lemma eb_ρ₀ (x : ℝ) {y : ℝ} (hy : 0 < y) : ρ₀ (Φ x y) = (1 + √3 * x) / (√3 * y) := by
  have hy0 : y ≠ 0 := hy.ne'
  simp [ρ₀, Φ]; field_simp

/-- `ρ₁(Φ(x, y)) = (1 - √3x)/(√3y)`. -/
private lemma eb_ρ₁ (x : ℝ) {y : ℝ} (hy : 0 < y) : ρ₁ (Φ x y) = (1 - √3 * x) / (√3 * y) := by
  have hy0 : y ≠ 0 := hy.ne'
  simp [ρ₁, Φ]; field_simp

/-- `ρ₂(Φ(x, y)) = (3(x² + y²) - 1)/(2√3y)`. -/
private lemma eb_ρ₂ (x : ℝ) {y : ℝ} (hy : 0 < y) :
    ρ₂ (Φ x y) = (3 * (x ^ 2 + y ^ 2) - 1) / (2 * √3 * y) := by
  have hy0 : y ≠ 0 := hy.ne'
  simp [ρ₂, Φ]; field_simp; ring

/-- `1/√3 = √3/3`. -/
private lemma eb_inv_sqrt3 : 1 / √3 = √3 / 3 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3pos : 0 < √3 := by positivity
  field_simp
  linarith

/-- `δ_oct < 0.903`, from `√2 > 1.4142` and `ln 2 > 0.6931471803`. -/
private lemma eb_octagonDensity_lt : octagonDensity < 903 / 1000 := by
  have h2 : (14142 / 10000 : ℝ) < √2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hl := Real.log_two_gt_d9
  have e8 : √8 = 2 * √2 := by
    rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  have e32 : √32 = 4 * √2 := by
    rw [show (32 : ℝ) = 4 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  rw [octagonDensity, e8, e32, div_lt_iff₀ (by linarith)]
  norm_num at hl ⊢
  linarith

/-- `𝔥* ∩ Π₀⁺ ∩ {1 ≤ y ≤ 4.5} ⊆ h₀` (proof of Theorem 5.0.2, TeX 4499). -/
theorem edgeSlab_subset_hRegion :
    starDomain ∩ edgeHalfPlane ∩ {z | 1 ≤ z.2 ∧ z.2 ≤ 9 / 2} ⊆ hRegion 0 := by
  rintro ⟨x, y⟩ ⟨⟨hz, -, hP⟩, hy1, hy2⟩
  refine ⟨hz, ?_⟩
  simp only at hP hy1 hy2 ⊢
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3pos : 0 < √3 := by positivity
  obtain ⟨h3lo, h3hi⟩ := eb_sqrt3_bounds
  have hy : 0 < y := by linarith
  obtain ⟨h0, -, -, hext0, -, -, -⟩ := lemma5_0_4 hz
  rw [h0, hext0]
  rw [eb_inv_sqrt3] at hP
  -- `0 < ρ₁ < 1/15` on `Π₀⁺`
  have hb0 : 0 < ρ₁ (Φ x y) := ((theorem4_4_1 x y hy).2 hz).2.2.2.1
  have hb : ρ₁ (Φ x y) < 1 / 15 := by
    rw [eb_ρ₁ x hy, div_lt_iff₀ (by positivity)]
    nlinarith [mul_lt_mul_of_pos_left hP h3pos]
  -- `ρ₀ ≥ 1/(√3y)` (as `x ≥ 0`) and `ρ₂ ≥ y/√3` (as `y ≥ 1`), so `ρ₀ρ₂ ≥ 1/3`
  have hx : 0 ≤ x := by nlinarith
  have ha : 1 / (√3 * y) ≤ ρ₀ (Φ x y) := by
    rw [eb_ρ₀ x hy]
    gcongr
    nlinarith
  have hc : y / √3 ≤ ρ₂ (Φ x y) := by
    rw [eb_ρ₂ x hy, div_le_div_iff₀ h3pos (by positivity)]
    nlinarith [sq_nonneg x]
  have hac : 1 / 3 ≤ ρ₀ (Φ x y) * ρ₂ (Φ x y) := by
    calc (1 / 3 : ℝ) = 1 / (√3 * y) * (y / √3) := by field_simp; linarith
      _ ≤ ρ₀ (Φ x y) * ρ₂ (Φ x y) := mul_le_mul ha hc (by positivity) (le_trans (by positivity) ha)
  nlinarith

/-- **The one-variable estimate of the proof of Theorem 5.0.2** (TeX 4502–4509): along the line
`y = 15(1/√3 - x)` bounding `Π₀⁺`, for `1 ≤ y ≤ 4.5`, `δ₀(x, y) = 3/4 + area₀(x, y)/√3 > δ_oct`.

Proof (the book only says "the graph is clear"): on the line, `√3x = 1 - √3y/15`, so
`ρ₁ = 1/15` and `6y ρ₀ρ₂ = (2 - √3y/15)(226y/75 - 2√3/15)`, which is concave in `y`; with
`√3 < 1.7321` it exceeds `6y · 0.7268` at `y = 1` and at `y = 4.5`, hence on `[1, 4.5]`. Then
`δ₀ = 3/4 + (ρ₀ρ₂ - (2/15)√(ρ₀ρ₂))/4 ≥ 3/4 + 0.153 = 0.903 > δ_oct` (`eb_octagonDensity_lt`). -/
theorem octagonDensity_lt_edgeLine {y : ℝ} (hy : y ∈ Icc 1 (9 / 2)) :
    octagonDensity < 3 / 4 + areaFn 0 (1 / √3 - y / 15, y) / √3 := by
  obtain ⟨hy1, hy2⟩ := hy
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3pos : 0 < √3 := by positivity
  obtain ⟨h3lo, h3hi⟩ := eb_sqrt3_bounds
  have hy0 : 0 < y := by linarith
  set x := 1 / √3 - y / 15 with hx
  have hsx : √3 * x = 1 - √3 * y / 15 := by
    rw [hx, mul_sub, mul_one_div_cancel h3pos.ne']; ring
  have hz : (x, y) ∈ starDomain := by
    refine ⟨hy0, ?_, ?_, ?_⟩
    · rw [hx, eb_inv_sqrt3]; nlinarith
    · rw [hx]; linarith
    · nlinarith [sq_nonneg x]
  rw [areaFn_zero_eq hz]
  -- `ρ₁ = 1/15` on the line
  have hb : ρ₁ (Φ x y) = 1 / 15 := by
    rw [eb_ρ₁ x hy0, hsx]; field_simp; ring
  -- `ρ₀ρ₂ ≥ 0.7268` on the line
  have hP : 1817 / 2500 ≤ ρ₀ (Φ x y) * ρ₂ (Φ x y) := by
    rw [eb_ρ₀ x hy0, eb_ρ₂ x hy0, div_mul_div_comm, le_div_iff₀ (by positivity)]
    have e : 3 * (x ^ 2 + y ^ 2) - 1 = (√3 * x) ^ 2 + 3 * y ^ 2 - 1 := by
      rw [mul_pow, h3]; ring
    rw [e, hsx]
    -- the concave function `f(y) = 6y(ρ₀ρ₂ - 0.7268)/y`
    have hf : 0 ≤ (454 / 75 - 1817 / 2500 * 6) * y - √3 * (4 / 15 + 226 * y ^ 2 / 1125) := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 17321 / 10000 - √3)
        (by positivity : (0 : ℝ) ≤ 4 / 15 + 226 * y ^ 2 / 1125),
        mul_nonneg (by linarith : (0 : ℝ) ≤ y - 1) (by linarith : (0 : ℝ) ≤ 9 / 2 - y)]
    have key : (1 + (1 - √3 * y / 15)) * ((1 - √3 * y / 15) ^ 2 + 3 * y ^ 2 - 1) -
        1817 / 2500 * (√3 * y * (2 * √3 * y)) =
        y * ((454 / 75 - 1817 / 2500 * 6) * y - √3 * (4 / 15 + 226 * y ^ 2 / 1125)) := by
      linear_combination (4 * y ^ 2 / 225 - √3 * y ^ 3 / 3375 - 1817 / 2500 * 2 * y ^ 2) * h3
    nlinarith [mul_nonneg hy0.le hf]
  -- reduce to `s = √(ρ₀ρ₂)`
  set P := ρ₀ (Φ x y) * ρ₂ (Φ x y) with hPdef
  have hP0 : 0 ≤ P := by linarith
  have hQ : ρ₀ (Φ x y) * ρ₁ (Φ x y) ^ 2 * ρ₂ (Φ x y) = (1 / 15) ^ 2 * P := by
    rw [hb, hPdef]; ring
  rw [hQ, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  set s := √P with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = P := Real.sq_sqrt hP0
  have hslo : 341 / 400 ≤ s := by nlinarith
  have hδ := eb_octagonDensity_lt
  have e : √3 / 4 * (P - 2 * (1 / 15 * s)) / √3 = (P - 2 / 15 * s) / 4 := by
    field_simp
  rw [e]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ s - 341 / 400)
    (by linarith : (0 : ℝ) ≤ s + 341 / 400 - 2 / 15)]

/-- **The half-plane `Π₀⁺` in the proof of Theorem 5.0.2** (TeX 4491–4512): for
`z ∈ 𝔥* ∩ Π₀⁺` with `1 ≤ y ≤ 4.5`, `δ(z) ≥ δ₀(z) > δ_oct`. -/
theorem octagonDensity_lt_densityBound_of_mem_edgeHalfPlane {z : ℝ × ℝ} (hz : z ∈ starDomain)
    (hP : z ∈ edgeHalfPlane) (hy₁ : 1 ≤ z.2) (hy₂ : z.2 ≤ 9 / 2) :
    octagonDensity < densityBound z := by
  obtain ⟨x, y⟩ := z
  simp only at hy₁ hy₂
  have h3pos : 0 < √3 := by positivity
  obtain ⟨h3lo, h3hi⟩ := eb_sqrt3_bounds
  -- `z ∈ h₀`, and the other terms of `δ` are `≥ 0`
  have h0 : (x, y) ∈ hRegion 0 := edgeSlab_subset_hRegion ⟨⟨hz, hP⟩, hy₁, hy₂⟩
  have hnn : ∀ i, 0 ≤ (hRegion i).indicator (areaFn i) (x, y) :=
    fun i ↦ Set.indicator_nonneg (fun w hw ↦ areaFn_nonneg_of_mem_hRegion hw) _
  have hsum : areaFn 0 (x, y) ≤ ∑ i : Fin 3, (hRegion i).indicator (areaFn i) (x, y) := by
    rw [Fin.sum_univ_three, Set.indicator_of_mem h0]
    linarith [hnn 1, hnn 2]
  -- Lemma 5.0.7 (1): `area₀` increases in `x`, so `area₀(z) ≥ area₀` on the line
  have hxlt : x < 1 / √3 := hz.2.2.1
  have hx' : 1 / √3 - y / 15 < x := by have := hP.2; simp only at this; linarith
  have hx'0 : 0 < 1 / √3 - y / 15 := by rw [eb_inv_sqrt3]; linarith
  have hmono : areaFn 0 (1 / √3 - y / 15, y) ≤ areaFn 0 (x, y) :=
    lemma5_0_7_1 hy₁ ⟨hx'0, by linarith⟩ ⟨by linarith, hxlt⟩ hx'.le
  rw [densityBound_eq]
  calc octagonDensity < 3 / 4 + areaFn 0 (1 / √3 - y / 15, y) / √3 :=
        octagonDensity_lt_edgeLine ⟨hy₁, hy₂⟩
    _ ≤ 3 / 4 + (∑ i : Fin 3, (hRegion i).indicator (areaFn i) (x, y)) / √3 := by
        gcongr
        exact hmono.trans hsum

end SmoothedPolygons
