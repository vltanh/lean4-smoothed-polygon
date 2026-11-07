module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import SmoothedPolygons.Ch5.Hexagon

/-!
# Monotonicity of the area bounds (Lemma 5.0.7)

Lemma 5.0.7 (`lem:compactification-lemma`, TeX 4353–4466) studies the functions `area_i(x, y)` and
the density bound `δ(x, y)` of `SmoothedPolygons.Ch5.Hexagon` on the star domain, in the
coordinates `z = x + iy`. By Lemma 5.0.4 and Theorem 4.4.1, with
`ρ₀ = (1 + √3x)/(√3y)`, `ρ₁ = (1 - √3x)/(√3y)`, `ρ₂ = (3(x² + y²) - 1)/(2√3y)` (`ρⱼ(Φ(x, y))`):

  `area₀ = (√3/4)(ρ₀ρ₂ - 2√(ρ₀ρ₁²ρ₂))`  (`areaFn_zero_eq`, TeX 4386–4391),
  `area₂(x, y) = area₀(-x, y)`, since `ρ₀(-x, y) = ρ₁(x, y)` (`areaFn_two_eq`, TeX 4443).

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
  (TeX 4447's "monotonic decreasing in `x` on `h₀ ∩ {x < 0, y ≥ √3}`" should read
  `h₂ ∩ {x < 0, y ≥ √3}`: the mirror image of `h₀ ∩ {x > 0}` under `x ↦ -x` is in `h₂`.)
  **Gap (inventory, Part I §6):** the book treats only `h₀ ∩ {x > 0, y ≥ √3}` and does not show
  that the points with `x > 0` lie in `h₀`, nor how `I₁area₁` enters. Repair along its lines: for
  `y ≥ √3`, `x ≥ 0`, `T₀ - T₀^ext` has the sign of
  `(1 + √3x)(3x² + 3y² - 1) - 8(1 - √3x)² ≥ x(3√3x² - 21x + 24√3) ≥ 0` (the quadratic has negative
  discriminant), so `{x ≥ 0, y ≥ √3} ⊆ h₀`, and symmetrically `{x ≤ 0, y ≥ √3} ⊆ h₂`; the statement
  of (3) involves only `I₀area₀ + I₂area₂`, so `h₁` does not enter.
* (4) `lemma5_0_7_4` (TeX 4450–4465): `area₀(0, y) = area₂(0, y) = (√3/4)√(ρ₀ρ₂)(√(ρ₀ρ₂) - 2ρ₁)`
  is increasing in `y` (`ρ₀ρ₂ = (y² - 1/3)/(2y²)` and `√(ρ₀ρ₂) - 2ρ₁` increase), and
  `δ(x, y) ≥ δ(0, y) ≥ δ(0, 4.5) = 0.9059… > δ_oct = 0.9024…`. **Gap:** the first inequality does
  not follow from (3) alone, which does not control `I₁area₁`; it also needs
  `I₁area₁(x, y) ≥ 0 = I₁area₁(0, y)`, that is, `(0, y) ∉ h₁` (on the imaginary axis
  `T₁ < T₁^ext`, as `(3y² - 1)² > 1`), which the book does not state.

## How the proofs are written

The one-variable work is done in `s = √3x ∈ [0, 1)`, with `k = √3y` and `c = 3y² - 1`, where
`ρ₀ = (1 + s)/k`, `ρ₁ = (1 - s)/k`, `ρ₂ = (s² + c)/(2k)` and
`area₀ = (√3/(8k²))((1 + s)(s² + c) - 2√(2f(s)))`, `f(s) = (1 + s)(1 - s)²(s² + c)`,
`f'(s) = -(1 - s)P(s)`, `(f(-s))' = (1 + s)Q(s)`, `Q(s) = P(-s)`. Monotonicity follows from the
sign of a derivative by the mean value theorem (`antitoneOn_of_hasDerivWithinAt_nonpos`).

* (1): term by term: `(1 + s)(s² + c)` (`∝ ρ₀ρ₂`) is a product of positive increasing factors (the
  book's `ρ₀,ₓρ₂ > 0`, `ρ₀ρ₂,ₓ > 0`), and `f` decreases since `f' = -(1 - s)P ≤ 0` (the book's
  `-(ρ₀ρ₁²ρ₂)ₓ > 0`), so `-2√(2f)` increases.
* (2): `s² + c` (`∝ (ρ₀ + ρ₁)ρ₂`) increases, and `√(2f(s)) + √(2f(-s))` (`∝ √(ρ₀ρ₁²ρ₂) +
  √(ρ₀²ρ₁ρ₂)`) has derivative `(φ₁ + φ₂)/√(2(1 - s²)(s² + c))`, where `φ₁ = -√(1 - s)P(s)` and
  `φ₂ = √(1 + s)Q(s)` are positive multiples of the book's `(ρ₀ρ₁²ρ₂)ₓ/√ρ₁` and `(ρ₀²ρ₁ρ₂)ₓ/√ρ₀`.
  `φ₁ + φ₂ ≤ 0` by the book's split at `x = 1/4` (`s = √3/4`): for `s ≥ √3/4`, `P > 0 ≥ Q` (here
  `c ≥ 8`, i.e. `y ≥ √3`, is used); for `s ≤ √3/4`, `φ₁' = (P - 2(1 - s)P')/(2√(1 - s)) ≤ 0`,
  `φ₂' = (Q + 2(1 + s)Q')/(2√(1 + s)) ≤ 0`, and `φ₁(0) + φ₂(0) = -c + c = 0`.
* (1) and (2) are proved on `[0, 1/√3)`, since (3) compares with `x = 0`; the statements are the
  book's, on the open interval.
* (3): on `𝔥*`, `I_i area_i = max(area_i, 0)`: this is why (5.0.1) is continuous. For `x ≥ 0`,
  `y ≥ √3`, as `(x, y) ∈ h₀` (the repair above), `I₀area₀ + I₂area₂ = max(area₀ + area₂, area₀)`,
  which is `area₀ + area₂` on `h₀ ∩ h₂` and `area₀` on `h₀ ∖ h₂`; it increases as the maximum of the
  increasing functions of (2) and (1). This is the book's "increasing on each piece, and
  continuous" in one step.
* (4): the book's chain. `δ(x, y) ≥ δ(0, y)` by (3), `I₁area₁(x, y) ≥ 0` and
  `(0, y) ∉ h₁` (`l2c_not_mem_hRegion_one_axis`); `δ(0, y) = 3/4 + 2area₀(0, y)/√3`
  (`l2c_densityBound_axis`: `(0, y) ∈ h₀ ∩ h₂`) increases with `y ≥ √3`
  (`mo_areaFn_zero_axis_mono`: `√u` increases, `v` decreases, and `√u - 2v ≥ 0` for `y ≥ √3`).
  Numerics with exact rational bounds: `√32 > 5.656854`, `√8 > 2.828427` and
  `ln 2 > 0.6931471803` (`Real.log_two_gt_d9`) give `δ_oct < 0.9025`; at `y = 4.5`,
  `u = ρ₀ρ₂ = 239/486`, `v = ρ₁`, `2area₀/√3 = u/2 - v√u` and `(v√u)² = 956/118098 < 0.0905²`, so
  `δ ≥ 3/4 + 239/972 - 0.0905 > 0.9053`.
-/

@[expose] public section

namespace SmoothedPolygons

open MeasureTheory Set

/-! ### The star functions of `Φ(x, y)` and the area formulas -/

/-- The star functions of `Φ(x, y)` (Theorem 4.4.1), in the variables `s = √3x` and `k = √3y`:
`ρ₀ = (1 + s)/k`, `ρ₁ = (1 - s)/k`, `ρ₂ = (s² + 3y² - 1)/(2k)`. -/
private lemma mo_ρ (x y : ℝ) (hy : 0 < y) :
    ρ₀ (Φ x y) = (1 + √3 * x) / (√3 * y) ∧ ρ₁ (Φ x y) = (1 - √3 * x) / (√3 * y) ∧
      ρ₂ (Φ x y) = ((√3 * x) ^ 2 + (3 * y ^ 2 - 1)) / (2 * (√3 * y)) := by
  have h3 : 0 < √3 := by positivity
  have h3sq : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · simp [ρ₀, Φ]; field_simp
  · simp [ρ₁, Φ]; field_simp
  · simp [ρ₂, Φ]; field_simp; rw [h3sq]; ring

/-- `ρ₀(-x, y) = ρ₁(x, y)`, `ρ₁(-x, y) = ρ₀(x, y)`, `ρ₂(-x, y) = ρ₂(x, y)` (TeX 4443). -/
private lemma mo_ρ_neg (x y : ℝ) :
    ρ₀ (Φ (-x) y) = ρ₁ (Φ x y) ∧ ρ₁ (Φ (-x) y) = ρ₀ (Φ x y) ∧ ρ₂ (Φ (-x) y) = ρ₂ (Φ x y) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [ρ₀, ρ₁, ρ₂, Φ] <;> ring

/-- The star domain is symmetric under `x ↦ -x`. -/
private lemma mo_neg_mem_starDomain {x y : ℝ} (hz : (x, y) ∈ starDomain) :
    (-x, y) ∈ starDomain := by
  obtain ⟨h1, h2, h3, h4⟩ := hz
  exact ⟨h1, by linarith, by linarith, by simpa using h4⟩

/-- The points `(x, y)` with `y ≥ 1` and `|x| < 1/√3` lie in `𝔥*`. -/
private lemma mo_mem_starDomain {x y : ℝ} (hy : 1 ≤ y) (hx : x ∈ Ioo (-(1 / √3)) (1 / √3)) :
    (x, y) ∈ starDomain :=
  ⟨by linarith, hx.1, hx.2, by nlinarith [sq_nonneg x]⟩

/-- `√(√3 a² · (√3/4) b c) = (√3/2) √(b a² c)`: the square root in `area_i` (Lemma 5.0.4). -/
private lemma mo_sqrt_ext_mul (a b c : ℝ) :
    √(√3 * a ^ 2 * (√3 / 4 * b * c)) = √3 / 2 * √(b * a ^ 2 * c) := by
  have : √3 * a ^ 2 * (√3 / 4 * b * c) = (√3 / 2) ^ 2 * (b * a ^ 2 * c) := by ring
  rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]

/-- `area₀` in terms of the star functions (TeX 4386–4391): on `𝔥*`,
`area₀(x, y) = (√3/4)(ρ₀ρ₂ - 2√(ρ₀ρ₁²ρ₂))` with `ρⱼ = ρⱼ(Φ(x, y))`. -/
theorem areaFn_zero_eq {x y : ℝ} (hz : (x, y) ∈ starDomain) :
    areaFn 0 (x, y) = √3 / 4 * (ρ₀ (Φ x y) * ρ₂ (Φ x y) -
      2 * √(ρ₀ (Φ x y) * ρ₁ (Φ x y) ^ 2 * ρ₂ (Φ x y))) := by
  obtain ⟨h0, -, -, he0, -, -, -⟩ := lemma5_0_4 hz
  simp only [areaFn, h0, he0, mo_sqrt_ext_mul]
  ring

/-- The reflection symmetry of the areas (TeX 4443): `area₂(x, y) = area₀(-x, y)` and
`(x, y) ∈ h₂ ↔ (-x, y) ∈ h₀`, since `ρ₀(-x, y) = ρ₁(x, y)` and `ρ₂(-x, y) = ρ₂(x, y)`. -/
theorem areaFn_two_eq {x y : ℝ} (hz : (x, y) ∈ starDomain) :
    areaFn 2 (x, y) = areaFn 0 (-x, y) ∧ ((x, y) ∈ hRegion 2 ↔ (-x, y) ∈ hRegion 0) := by
  have hz' := mo_neg_mem_starDomain hz
  obtain ⟨-, -, h2, -, -, he2, -⟩ := lemma5_0_4 hz
  obtain ⟨h0', -, -, he0', -, -, -⟩ := lemma5_0_4 hz'
  obtain ⟨n0, n1, n2⟩ := mo_ρ_neg x y
  simp only [n0, n1, n2] at h0' he0'
  refine ⟨?_, ?_⟩
  · simp only [areaFn, h2, he2, h0', he0']
  · simp only [hRegion, mem_ofPred_eq, h2, he2, h0', he0', hz, hz', true_and]

/-! ### Equation (5.0.1): continuity of `Σ I_i area_i` -/

/-- On `𝔥*`, `I_i area_i = max(area_i, 0)`: `area_i ≥ 0` on `h_i` (where `T_i^ext ≤ T_i`) and
`area_i ≤ 0` off `h_i` (where `T_i < T_i^ext`). So `area_i = 0` where `I_i` jumps. -/
private lemma mo_indicator_eq_max {i : Fin 3} {z : ℝ × ℝ} (hz : z ∈ starDomain) :
    (hRegion i).indicator (areaFn i) z = max (areaFn i z) 0 := by
  have ht : 0 ≤ triArea z.1 z.2 i := measureReal_nonneg
  have he : 0 ≤ extTriArea z.1 z.2 i := measureReal_nonneg
  by_cases h : z ∈ hRegion i
  · rw [indicator_of_mem h, max_eq_left]
    have hle : extTriArea z.1 z.2 i ≤ triArea z.1 z.2 i := h.2
    have : √(extTriArea z.1 z.2 i * triArea z.1 z.2 i) ≤ triArea z.1 z.2 i := by
      rw [Real.sqrt_le_left ht]; nlinarith
    simp only [areaFn]; linarith
  · rw [indicator_of_notMem h, max_eq_right]
    have hlt : triArea z.1 z.2 i < extTriArea z.1 z.2 i := by
      by_contra h'
      exact h ⟨hz, not_lt.mp h'⟩
    have : triArea z.1 z.2 i ≤ √(extTriArea z.1 z.2 i * triArea z.1 z.2 i) := by
      rw [Real.le_sqrt ht (by positivity)]; nlinarith
    simp only [areaFn]; linarith

/-- The star functions `ρⱼ(Φ(x, y))` are continuous on `𝔥*`. -/
private lemma mo_continuousOn_ρ :
    ContinuousOn (fun z : ℝ × ℝ => ρ₀ (Φ z.1 z.2)) starDomain ∧
    ContinuousOn (fun z : ℝ × ℝ => ρ₁ (Φ z.1 z.2)) starDomain ∧
    ContinuousOn (fun z : ℝ × ℝ => ρ₂ (Φ z.1 z.2)) starDomain := by
  have hne : ∀ z ∈ starDomain, z.2 ≠ 0 := fun z hz => hz.1.ne'
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [ρ₀, ρ₁, ρ₂, Φ, neg_add_rev, one_div, Fin.isValue, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one] <;>
    fun_prop (disch := exact hne)

/-- The triangle areas `T_i`, `T_i^ext` are continuous on `𝔥*`: by Lemma 5.0.4 they are
polynomials in the `ρⱼ`. -/
private lemma mo_continuousOn_areas (i : Fin 3) :
    ContinuousOn (fun z : ℝ × ℝ => triArea z.1 z.2 i) starDomain ∧
    ContinuousOn (fun z : ℝ × ℝ => extTriArea z.1 z.2 i) starDomain := by
  obtain ⟨c0, c1, c2⟩ := mo_continuousOn_ρ
  have key : ∀ z ∈ starDomain, _ := fun z (hz : z ∈ starDomain) =>
    lemma5_0_4 (x := z.1) (y := z.2) hz
  fin_cases i
  · exact ⟨((continuousOn_const.mul c0).mul c2).congr fun z hz => (key z hz).1,
      (continuousOn_const.mul (c1.pow 2)).congr fun z hz => (key z hz).2.2.2.1⟩
  · exact ⟨((continuousOn_const.mul c0).mul c1).congr fun z hz => (key z hz).2.1,
      (continuousOn_const.mul (c2.pow 2)).congr fun z hz => (key z hz).2.2.2.2.1⟩
  · exact ⟨((continuousOn_const.mul c1).mul c2).congr fun z hz => (key z hz).2.2.1,
      (continuousOn_const.mul (c0.pow 2)).congr fun z hz => (key z hz).2.2.2.2.2.1⟩

/-- **Equation (5.0.1)** (`eqn:area0-area2`, TeX 4433–4437): `Σ_i I_i area_i` is continuous on
`𝔥*`, because `area_i = 0` on the boundary of `h_i`, where `I_i` jumps. -/
theorem continuousOn_sum_indicator_areaFn :
    ContinuousOn (fun z ↦ ∑ i : Fin 3, (hRegion i).indicator (areaFn i) z) starDomain := by
  have hi : ∀ i : Fin 3,
      ContinuousOn (fun z ↦ (hRegion i).indicator (areaFn i) z) starDomain := by
    intro i
    obtain ⟨ht, he⟩ := mo_continuousOn_areas i
    have ha : ContinuousOn (areaFn i) starDomain := ht.sub ((he.mul ht).sqrt)
    exact (ha.sup continuousOn_const).congr fun z hz => mo_indicator_eq_max hz
  simp only [Fin.sum_univ_three]
  exact ((hi 0).add (hi 1)).add (hi 2)

/-! ### The one-variable inequalities, in the variable `s = √3x`

With `s = √3x ∈ [0, 1)`, `k = √3y` and `c = 3y² - 1`, the star functions are `ρ₀ = (1 + s)/k`,
`ρ₁ = (1 - s)/k`, `ρ₂ = (s² + c)/(2k)`, so `ρ₀ρ₁²ρ₂ = f(s)/(2k⁴)` and `ρ₀²ρ₁ρ₂ = f(-s)/(2k⁴)` with
`f(s) = (1 + s)(1 - s)²(s² + c)`, `f'(s) = -(1 - s)P(s)` and `(f(-s))' = (1 + s)Q(s)`. -/

/-- `f(s) = (1 + s)(1 - s)²(s² + c)`, a positive multiple of `ρ₀ρ₁²ρ₂`; `f(-s)` is one of
`ρ₀²ρ₁ρ₂`. -/
private def mo_f (c s : ℝ) : ℝ := (1 + s) * (1 - s) ^ 2 * (s ^ 2 + c)

/-- `P(s) = 5s³ + s² + (3c - 2)s + c`, with `f'(s) = -(1 - s)P(s)`. -/
private def mo_P (c s : ℝ) : ℝ := 5 * s ^ 3 + s ^ 2 + (3 * c - 2) * s + c

/-- `Q(s) = P(-s) = -5s³ + s² - (3c - 2)s + c`, with `(f(-s))' = (1 + s)Q(s)`. -/
private def mo_Q (c s : ℝ) : ℝ := -5 * s ^ 3 + s ^ 2 - (3 * c - 2) * s + c

/-- `area₀ = (√3/(8k²)) · ((1 + s)(s² + c) - 2√(2f(s)))` (`mo_areaFn_zero_eq_s`). -/
private noncomputable def mo_area (c s : ℝ) : ℝ := (1 + s) * (s ^ 2 + c) - 2 * √(2 * mo_f c s)

/-- `f'(s) = -(1 - s)P(s)`. -/
private lemma mo_hasDerivAt_f (c s : ℝ) : HasDerivAt (mo_f c) (-((1 - s) * mo_P c s)) s := by
  have h1 : HasDerivAt (fun s : ℝ => 1 + s) 1 s := (hasDerivAt_id' s).const_add 1
  have h2 := ((hasDerivAt_id' s).const_sub 1).fun_pow 2
  have h3 := (hasDerivAt_pow 2 s).add_const c
  exact ((h1.fun_mul h2).fun_mul h3).congr_deriv (by unfold mo_P; push_cast; ring)

/-- `(f(-s))' = (1 + s)Q(s)`. -/
private lemma mo_hasDerivAt_f_neg (c s : ℝ) :
    HasDerivAt (fun s => mo_f c (-s)) ((1 + s) * mo_Q c s) s :=
  ((mo_hasDerivAt_f c (-s)).comp s (hasDerivAt_neg s)).congr_deriv (by unfold mo_P mo_Q; ring)

/-- `P'(s) = 15s² + 2s + 3c - 2`. -/
private lemma mo_hasDerivAt_P (c s : ℝ) :
    HasDerivAt (mo_P c) (15 * s ^ 2 + 2 * s + (3 * c - 2)) s :=
  ((((hasDerivAt_pow 3 s).const_mul 5).fun_add (hasDerivAt_pow 2 s)).fun_add
    ((hasDerivAt_id' s).const_mul (3 * c - 2))).add_const c |>.congr_deriv (by push_cast; ring)

/-- `Q'(s) = -15s² + 2s - (3c - 2)`. -/
private lemma mo_hasDerivAt_Q (c s : ℝ) :
    HasDerivAt (mo_Q c) (-15 * s ^ 2 + 2 * s - (3 * c - 2)) s :=
  ((((hasDerivAt_pow 3 s).const_mul (-5)).fun_add (hasDerivAt_pow 2 s)).fun_sub
    ((hasDerivAt_id' s).const_mul (3 * c - 2))).add_const c |>.congr_deriv (by push_cast; ring)

/-- `f` is decreasing on `[0, 1]`: `f'(s) = -(1 - s)P(s) ≤ 0`. -/
private lemma mo_f_antitoneOn {c : ℝ} (hc : 2 ≤ c) : AntitoneOn (mo_f c) (Icc 0 1) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
    (by unfold mo_f; fun_prop) (fun s _ => (mo_hasDerivAt_f c s).hasDerivWithinAt) ?_
  intro s hs
  rw [interior_Icc] at hs
  have hP : 0 ≤ mo_P c s := by
    unfold mo_P; have := hs.1.le; nlinarith [pow_nonneg this 3]
  nlinarith [hs.2]

/-- **(1) in the variable `s`**: `(1 + s)(s² + c) - 2√(2f(s))` is increasing on `[0, 1]`. -/
private lemma mo_area_monotoneOn {c : ℝ} (hc : 2 ≤ c) : MonotoneOn (mo_area c) (Icc 0 1) := by
  intro a ha b hb hab
  have h1 : (1 + a) * (a ^ 2 + c) ≤ (1 + b) * (b ^ 2 + c) :=
    mul_le_mul (by linarith) (by nlinarith [ha.1]) (by positivity) (by linarith [hb.1])
  have h2 : √(2 * mo_f c b) ≤ √(2 * mo_f c a) :=
    Real.sqrt_le_sqrt (by linarith [mo_f_antitoneOn hc ha hb hab])
  unfold mo_area; linarith

/-- The book's first term `-(ρ₀ρ₁²ρ₂)ₓ/√ρ₁` in the variable `s`: `φ₁(s) = -√(1 - s) P(s)`. -/
private lemma mo_phi₁_antitoneOn {c : ℝ} (hc : 8 ≤ c) :
    AntitoneOn (fun s => -(√(1 - s) * mo_P c s)) (Icc 0 (√3 / 4)) := by
  have h3 : √3 < 1.7321 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 (√3 / 4)) (by unfold mo_P; fun_prop)
    (f' := fun s => -(-1 / (2 * √(1 - s)) * mo_P c s +
      √(1 - s) * (15 * s ^ 2 + 2 * s + (3 * c - 2)))) (fun s hs => ?_) ?_
  · rw [interior_Icc] at hs
    have hs1 : 1 - s ≠ 0 := by linarith [hs.2]
    exact ((((hasDerivAt_id' s).const_sub 1).sqrt hs1).fun_mul (mo_hasDerivAt_P c s)).fun_neg
      |>.hasDerivWithinAt
  · intro s hs
    rw [interior_Icc] at hs
    have hs1 : 0 < 1 - s := by linarith [hs.2]
    have ha : 0 < √(1 - s) := Real.sqrt_pos.mpr hs1
    have ha2 : √(1 - s) ^ 2 = 1 - s := Real.sq_sqrt hs1.le
    -- `φ₁' = (P - 2(1 - s)P')/(2√(1 - s))` and `P - 2(1 - s)P' = 9cs - 5c + 35s³ - 25s² - 10s + 4`
    have key : mo_P c s - 2 * (1 - s) * (15 * s ^ 2 + 2 * s + (3 * c - 2)) ≤ 0 := by
      unfold mo_P
      have hs0 := hs.1.le
      have hsl : s < 0.4331 := by linarith [hs.2]
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ c - 8) (by linarith : (0:ℝ) ≤ 5 - 9 * s),
        mul_nonneg hs0 hs0, mul_nonneg (mul_nonneg hs0 hs0) hs0]
    have : -(-1 / (2 * √(1 - s)) * mo_P c s + √(1 - s) * (15 * s ^ 2 + 2 * s + (3 * c - 2))) =
        (mo_P c s - 2 * (1 - s) * (15 * s ^ 2 + 2 * s + (3 * c - 2))) / (2 * √(1 - s)) := by
      field_simp; rw [ha2]; ring
    rw [this]
    exact div_nonpos_of_nonpos_of_nonneg key (by positivity)

/-- The book's second term `(ρ₀²ρ₁ρ₂)ₓ/√ρ₀` in the variable `s`: `φ₂(s) = √(1 + s) Q(s)`. -/
private lemma mo_phi₂_antitoneOn {c : ℝ} (hc : 8 ≤ c) :
    AntitoneOn (fun s => √(1 + s) * mo_Q c s) (Icc 0 (√3 / 4)) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 (√3 / 4)) (by unfold mo_Q; fun_prop)
    (f' := fun s => 1 / (2 * √(1 + s)) * mo_Q c s +
      √(1 + s) * (-15 * s ^ 2 + 2 * s - (3 * c - 2))) (fun s hs => ?_) ?_
  · rw [interior_Icc] at hs
    have hs1 : 1 + s ≠ 0 := by linarith [hs.1]
    exact (((hasDerivAt_id' s).const_add 1).sqrt hs1).fun_mul (mo_hasDerivAt_Q c s)
      |>.hasDerivWithinAt
  · intro s hs
    rw [interior_Icc] at hs
    have hs1 : 0 < 1 + s := by linarith [hs.1]
    have hb : 0 < √(1 + s) := Real.sqrt_pos.mpr hs1
    have hb2 : √(1 + s) ^ 2 = 1 + s := Real.sq_sqrt hs1.le
    -- `φ₂' = (Q + 2(1 + s)Q')/(2√(1 + s))` and `Q + 2(1 + s)Q' = -9cs - 5c - 35s³ - 25s² + 10s + 4`
    have key : mo_Q c s + 2 * (1 + s) * (-15 * s ^ 2 + 2 * s - (3 * c - 2)) ≤ 0 := by
      unfold mo_Q
      have hs0 := hs.1.le
      have hsl : s < 1 / 2 := by
        have : √3 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
        linarith [hs.2]
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ c - 8) hs0,
        mul_nonneg hs0 hs0, mul_nonneg (mul_nonneg hs0 hs0) hs0]
    have : 1 / (2 * √(1 + s)) * mo_Q c s + √(1 + s) * (-15 * s ^ 2 + 2 * s - (3 * c - 2)) =
        (mo_Q c s + 2 * (1 + s) * (-15 * s ^ 2 + 2 * s - (3 * c - 2))) / (2 * √(1 + s)) := by
      field_simp; rw [hb2]
    rw [this]
    exact div_nonpos_of_nonpos_of_nonneg key (by positivity)

/-- The book's inequality `(ρ₀ρ₁²ρ₂)ₓ/√ρ₁ + (ρ₀²ρ₁ρ₂)ₓ/√ρ₀ ≤ 0` (TeX 4421–4429) in the variable
`s = √3x ∈ [0, 1)`: `-√(1 - s)P(s) + √(1 + s)Q(s) ≤ 0`. For `x ≥ 1/4` both numerators are negative;
for `0 ≤ x ≤ 1/4` both terms decrease and their sum vanishes at `x = 0`. -/
private lemma mo_phi_sum_nonpos {c s : ℝ} (hc : 8 ≤ c) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    -(√(1 - s) * mo_P c s) + √(1 + s) * mo_Q c s ≤ 0 := by
  rcases le_total s (√3 / 4) with hs | hs
  · -- `0 ≤ x ≤ 1/4`: both terms decrease, and their sum is `-c + c = 0` at `s = 0`
    have h0 : (0 : ℝ) ∈ Icc 0 (√3 / 4) := ⟨le_rfl, by positivity⟩
    have hs' : s ∈ Icc 0 (√3 / 4) := ⟨hs0, hs⟩
    have e1 := mo_phi₁_antitoneOn hc h0 hs' hs0
    have e2 := mo_phi₂_antitoneOn hc h0 hs' hs0
    simp only [sub_zero, add_zero, Real.sqrt_one, one_mul, mo_P, mo_Q] at e1 e2
    norm_num at e1 e2
    unfold mo_P mo_Q
    linarith
  · -- `x ≥ 1/4`: `P(s) > 0` and `Q(s) < 0`
    have h3 : 1.732 < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
    have hP : 0 ≤ mo_P c s := by unfold mo_P; nlinarith [pow_nonneg hs0 3]
    have hQ : mo_Q c s ≤ 0 := by
      unfold mo_Q
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ c - 8) (by linarith : (0:ℝ) ≤ 3 * s - 1),
        pow_nonneg hs0 3, mul_nonneg hs0 (by linarith : (0:ℝ) ≤ 1 - s)]
    have := mul_nonneg (Real.sqrt_nonneg (1 - s)) hP
    have := mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg (1 + s)) hQ
    linarith

/-- `√(2f(s)) + √(2f(-s))`, a positive multiple of `√(ρ₀ρ₁²ρ₂) + √(ρ₀²ρ₁ρ₂)`, is decreasing on
`[0, 1)` (Lemma 5.0.7 (2)): its derivative is `(φ₁ + φ₂)/√(2(1 - s²)(s² + c)) ≤ 0`. -/
private lemma mo_sqrt_sum_antitoneOn {c : ℝ} (hc : 8 ≤ c) :
    AntitoneOn (fun s => √(2 * mo_f c s) + √(2 * mo_f c (-s))) (Ico 0 1) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ico 0 1)
    (by unfold mo_f; fun_prop)
    (f' := fun s => 2 * -((1 - s) * mo_P c s) / (2 * √(2 * mo_f c s)) +
      2 * ((1 + s) * mo_Q c s) / (2 * √(2 * mo_f c (-s)))) (fun s hs => ?_) ?_
  · rw [interior_Ico] at hs
    have hf : 0 < mo_f c s := by
      unfold mo_f
      exact mul_pos (mul_pos (by linarith [hs.1]) (pow_pos (by linarith [hs.2]) 2)) (by positivity)
    have hg : 0 < mo_f c (-s) := by
      unfold mo_f
      exact mul_pos (mul_pos (by linarith [hs.2]) (pow_pos (by linarith [hs.1]) 2)) (by positivity)
    exact (((mo_hasDerivAt_f c s).const_mul 2).sqrt (by positivity)).fun_add
      (((mo_hasDerivAt_f_neg c s).const_mul 2).sqrt (by positivity)) |>.hasDerivWithinAt
  · intro s hs
    rw [interior_Ico] at hs
    obtain ⟨hs0, hs1⟩ := hs
    -- `2f(s) = (1 - s)·2H`, `2f(-s) = (1 + s)·2H`, `H = (1 - s²)(s² + c)`
    set H := 2 * ((1 + s) * (1 - s) * (s ^ 2 + c)) with hH
    have hHpos : 0 < H := by
      have : 0 < (1 + s) * (1 - s) := mul_pos (by linarith) (by linarith)
      positivity
    have hfH : 2 * mo_f c s = (1 - s) * H := by unfold mo_f; ring
    have hgH : 2 * mo_f c (-s) = (1 + s) * H := by unfold mo_f; ring
    have ha : 0 < √(1 - s) := Real.sqrt_pos.mpr (by linarith)
    have hb : 0 < √(1 + s) := Real.sqrt_pos.mpr (by linarith)
    have hh : 0 < √H := Real.sqrt_pos.mpr hHpos
    have ha2 : √(1 - s) ^ 2 = 1 - s := Real.sq_sqrt (by linarith)
    have hb2 : √(1 + s) ^ 2 = 1 + s := Real.sq_sqrt (by linarith)
    rw [hfH, hgH, Real.sqrt_mul (x := 1 - s) (by linarith) H,
      Real.sqrt_mul (x := 1 + s) (by linarith) H]
    have : 2 * -((1 - s) * mo_P c s) / (2 * (√(1 - s) * √H)) +
        2 * ((1 + s) * mo_Q c s) / (2 * (√(1 + s) * √H)) =
        (-(√(1 - s) * mo_P c s) + √(1 + s) * mo_Q c s) / √H := by
      field_simp
      linear_combination (mo_P c s * √(1 + s)) * ha2 - (mo_Q c s * √(1 - s)) * hb2
    rw [this]
    exact div_nonpos_of_nonpos_of_nonneg (mo_phi_sum_nonpos hc hs0.le hs1) hh.le

/-- **(2) in the variable `s`**: `area₀ + area₂` is a positive multiple of
`mo_area c s + mo_area c (-s) = 2(s² + c) - 2(√(2f(s)) + √(2f(-s)))`, increasing on `[0, 1)`. -/
private lemma mo_area_add_monotoneOn {c : ℝ} (hc : 8 ≤ c) :
    MonotoneOn (fun s => mo_area c s + mo_area c (-s)) (Ico 0 1) := by
  intro a ha b hb hab
  have h1 : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha.1 hab 2
  have h2 := mo_sqrt_sum_antitoneOn hc ha hb hab
  simp only at h2 ⊢
  unfold mo_area
  nlinarith

/-! ### Lemma 5.0.7 (1) and (2) -/

/-- `area₀` in the variable `s = √3x` (with `k = √3y`, `c = 3y² - 1`):
`area₀(x, y) = (√3/(8k²))((1 + s)(s² + c) - 2√(2f(s)))`, from `areaFn_zero_eq`. -/
private lemma mo_areaFn_zero_eq_s {x y : ℝ} (hz : (x, y) ∈ starDomain) :
    areaFn 0 (x, y) = √3 / (8 * (√3 * y) ^ 2) * mo_area (3 * y ^ 2 - 1) (√3 * x) := by
  obtain ⟨r0, r1, r2⟩ := mo_ρ x y hz.1
  have hk : 0 < √3 * y := by have := hz.1; positivity
  rw [areaFn_zero_eq hz, r0, r1, r2]
  generalize √3 * x = s
  generalize √3 * y = k at hk ⊢
  have harg : (1 + s) / k * ((1 - s) / k) ^ 2 * ((s ^ 2 + (3 * y ^ 2 - 1)) / (2 * k)) =
      (1 / (2 * k ^ 2)) ^ 2 * (2 * mo_f (3 * y ^ 2 - 1) s) := by
    unfold mo_f; field_simp
  rw [harg, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  unfold mo_area; field_simp; ring

/-- `area₀ + area₂` in the variable `s = √3x`: `area₂(x, y) = area₀(-x, y)` (`areaFn_two_eq`). -/
private lemma mo_areaFn_add_eq_s {x y : ℝ} (hz : (x, y) ∈ starDomain) :
    areaFn 0 (x, y) + areaFn 2 (x, y) = √3 / (8 * (√3 * y) ^ 2) *
      (mo_area (3 * y ^ 2 - 1) (√3 * x) + mo_area (3 * y ^ 2 - 1) (-(√3 * x))) := by
  rw [(areaFn_two_eq hz).1, mo_areaFn_zero_eq_s hz, mo_areaFn_zero_eq_s (mo_neg_mem_starDomain hz),
    mul_neg]
  ring

/-- `x ∈ [0, 1/√3)` gives `s = √3x ∈ [0, 1)` and `(x, y) ∈ 𝔥*` for `y ≥ 1`. -/
private lemma mo_mem_Ico {x : ℝ} (hx : x ∈ Ico 0 (1 / √3)) :
    √3 * x ∈ Ico (0 : ℝ) 1 ∧ x ∈ Ioo (-(1 / √3)) (1 / √3) := by
  have h3 : 0 < √3 := by positivity
  have := (lt_div_iff₀ h3).mp hx.2
  exact ⟨⟨by have := hx.1; positivity, by linarith⟩,
    ⟨by have : 0 < 1 / √3 := by positivity
        linarith [hx.1], hx.2⟩⟩

/-- `1 ≤ √3`. -/
private lemma mo_one_le_sqrt_three : 1 ≤ √3 := by
  rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num

/-- `y ≥ √3` gives `c = 3y² - 1 ≥ 8`. -/
private lemma mo_c_ge {y : ℝ} (hy : √3 ≤ y) : 8 ≤ 3 * y ^ 2 - 1 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg 3]

/-- Lemma 5.0.7 (1) on `[0, 1/√3)`: for `y ≥ 1`, `area₀(x, y)` is increasing in `x`. -/
private lemma mo_monotoneOn_areaFn_zero {y : ℝ} (hy : 1 ≤ y) :
    MonotoneOn (fun x ↦ areaFn 0 (x, y)) (Ico 0 (1 / √3)) := by
  have hc : 2 ≤ 3 * y ^ 2 - 1 := by nlinarith
  intro a ha b hb hab
  obtain ⟨hsa, hxa⟩ := mo_mem_Ico ha
  obtain ⟨hsb, hxb⟩ := mo_mem_Ico hb
  simp only
  rw [mo_areaFn_zero_eq_s (mo_mem_starDomain hy hxa),
    mo_areaFn_zero_eq_s (mo_mem_starDomain hy hxb)]
  exact mul_le_mul_of_nonneg_left
    (mo_area_monotoneOn hc (Ico_subset_Icc_self hsa) (Ico_subset_Icc_self hsb)
      (mul_le_mul_of_nonneg_left hab (Real.sqrt_nonneg 3))) (by positivity)

/-- **Lemma 5.0.7 (1)** (`lem:compactification-lemma`). For all `y ≥ 1`, `area₀(x, y)` is
monotonically increasing in `x` on `0 < x < 1/√3`. -/
theorem lemma5_0_7_1 {y : ℝ} (hy : 1 ≤ y) :
    MonotoneOn (fun x ↦ areaFn 0 (x, y)) (Ioo 0 (1 / √3)) :=
  (mo_monotoneOn_areaFn_zero hy).mono Ioo_subset_Ico_self

/-- Lemma 5.0.7 (2) on `[0, 1/√3)`: for `y ≥ √3`, `area₀ + area₂` is increasing in `x`. -/
private lemma mo_monotoneOn_areaFn_add {y : ℝ} (hy : √3 ≤ y) :
    MonotoneOn (fun x ↦ areaFn 0 (x, y) + areaFn 2 (x, y)) (Ico 0 (1 / √3)) := by
  have hy1 : 1 ≤ y := mo_one_le_sqrt_three.trans hy
  intro a ha b hb hab
  obtain ⟨hsa, hxa⟩ := mo_mem_Ico ha
  obtain ⟨hsb, hxb⟩ := mo_mem_Ico hb
  simp only
  rw [mo_areaFn_add_eq_s (mo_mem_starDomain hy1 hxa),
    mo_areaFn_add_eq_s (mo_mem_starDomain hy1 hxb)]
  exact mul_le_mul_of_nonneg_left
    (mo_area_add_monotoneOn (mo_c_ge hy) hsa hsb
      (mul_le_mul_of_nonneg_left hab (Real.sqrt_nonneg 3))) (by positivity)

/-- **Lemma 5.0.7 (2)** (`lem:compactification-lemma`). For all `y ≥ √3`,
`area₀(x, y) + area₂(x, y)` is monotonically increasing in `x` on `0 < x < 1/√3`. -/
theorem lemma5_0_7_2 {y : ℝ} (hy : √3 ≤ y) :
    MonotoneOn (fun x ↦ areaFn 0 (x, y) + areaFn 2 (x, y)) (Ioo 0 (1 / √3)) :=
  (mo_monotoneOn_areaFn_add hy).mono Ioo_subset_Ico_self

/-! ### Lemma 5.0.7 (3) -/

/-- **Repair of the book's proof of (3).** For `y ≥ √3` and `x ≥ 0`, `(x, y) ∈ h₀`:
`T₀ - T₀^ext = (√3/(8k²))((1 + s)(s² + c) - 8(1 - s)²)` and, as `c ≥ 8`,
`(1 + s)(s² + c) - 8(1 - s)² ≥ s(s² - 7s + 24) ≥ 0` (the quadratic has negative discriminant). -/
private lemma mo_mem_hRegion_zero {x y : ℝ} (hz : (x, y) ∈ starDomain) (hy : √3 ≤ y)
    (hx : 0 ≤ x) : (x, y) ∈ hRegion 0 := by
  obtain ⟨h0, -, -, he0, -, -, -⟩ := lemma5_0_4 hz
  obtain ⟨r0, r1, r2⟩ := mo_ρ x y hz.1
  refine ⟨hz, ?_⟩
  change extTriArea x y 0 ≤ triArea x y 0
  rw [h0, he0, r0, r1, r2]
  have hc := mo_c_ge hy
  have hs : 0 ≤ √3 * x := by positivity
  have hk : 0 < √3 * y := by have := hz.1; positivity
  generalize √3 * x = s at hs ⊢
  generalize √3 * y = k at hk ⊢
  generalize 3 * y ^ 2 - 1 = c at hc ⊢
  have key : 0 ≤ (1 + s) * (s ^ 2 + c) - 8 * (1 - s) ^ 2 := by
    nlinarith [mul_nonneg hs (sq_nonneg (s - 7 / 2)),
      mul_nonneg (by linarith : 0 ≤ 1 + s) (by linarith : 0 ≤ c - 8)]
  have : √3 / 4 * ((1 + s) / k) * ((s ^ 2 + c) / (2 * k)) - √3 * ((1 - s) / k) ^ 2 =
      √3 / (8 * k ^ 2) * ((1 + s) * (s ^ 2 + c) - 8 * (1 - s) ^ 2) := by
    field_simp; ring
  nlinarith [mul_nonneg (by positivity : 0 ≤ √3 / (8 * k ^ 2)) key]

/-- Transport of an indicator along a correspondence of points. -/
private lemma mo_indicator_congr {α : Type*} {s t : Set α} {f g : α → ℝ} {a b : α}
    (hm : a ∈ s ↔ b ∈ t) (he : f a = g b) : s.indicator f a = t.indicator g b := by
  by_cases h : a ∈ s
  · rw [indicator_of_mem h, indicator_of_mem (hm.mp h), he]
  · rw [indicator_of_notMem h, indicator_of_notMem (mt hm.mpr h)]

/-- The function `I₀ area₀ + I₂ area₂` on the horizontal line at height `y`. -/
private noncomputable def mo_S (y x : ℝ) : ℝ :=
  (hRegion 0).indicator (areaFn 0) (x, y) + (hRegion 2).indicator (areaFn 2) (x, y)

/-- On `x ≥ 0`, `y ≥ √3`: `I₀ area₀ + I₂ area₂ = area₀ + max(area₂, 0) = max(area₀ + area₂, area₀)`
(`(x, y) ∈ h₀`, and `I₂area₂ = max(area₂, 0)` as in the continuity of (5.0.1)): it equals
`area₀ + area₂` on `h₀ ∩ h₂` and `area₀` on `h₀ ∖ h₂`. -/
private lemma mo_S_eq_max {y x : ℝ} (hy : √3 ≤ y) (hx : x ∈ Ico 0 (1 / √3)) :
    mo_S y x = max (areaFn 0 (x, y) + areaFn 2 (x, y)) (areaFn 0 (x, y)) := by
  have hz := mo_mem_starDomain (mo_one_le_sqrt_three.trans hy) (mo_mem_Ico hx).2
  rw [mo_S, indicator_of_mem (mo_mem_hRegion_zero hz hy hx.1), mo_indicator_eq_max hz,
    ← max_add_add_left, add_zero]

/-- **Lemma 5.0.7 (3)** (`lem:compactification-lemma`). For every fixed `y ≥ √3`, the function
`I₀(x, y) area₀(x, y) + I₂(x, y) area₂(x, y)` is minimized at `x = 0` on `x ∈ (-1/√3, 1/√3)`.
(The book's proof is incomplete; see the module docstring.) -/
theorem lemma5_0_7_3 {y : ℝ} (hy : √3 ≤ y) {x : ℝ} (hx : x ∈ Ioo (-(1 / √3)) (1 / √3)) :
    (hRegion 0).indicator (areaFn 0) (0, y) + (hRegion 2).indicator (areaFn 2) (0, y) ≤
      (hRegion 0).indicator (areaFn 0) (x, y) + (hRegion 2).indicator (areaFn 2) (x, y) := by
  change mo_S y 0 ≤ mo_S y x
  have hy1 : 1 ≤ y := mo_one_le_sqrt_three.trans hy
  -- increasing on `[0, 1/√3)`: the maximum of the increasing functions of (2) and (1)
  have hmono : MonotoneOn (mo_S y) (Ico 0 (1 / √3)) := by
    intro a ha b hb hab
    rw [mo_S_eq_max hy ha, mo_S_eq_max hy hb]
    exact ((mo_monotoneOn_areaFn_add hy).max (mo_monotoneOn_areaFn_zero hy1)) ha hb hab
  -- even in `x`, since `area₂(x, y) = area₀(-x, y)` and `(x, y) ∈ h₂ ↔ (-x, y) ∈ h₀`
  have heven : ∀ t ∈ Ioo (-(1 / √3)) (1 / √3), mo_S y (-t) = mo_S y t := by
    intro t ht
    have hz := mo_mem_starDomain hy1 ht
    obtain ⟨e2, m2⟩ := areaFn_two_eq hz
    obtain ⟨e2', m2'⟩ := areaFn_two_eq (mo_neg_mem_starDomain hz)
    rw [neg_neg] at e2' m2'
    rw [mo_S, mo_S, mo_indicator_congr m2' e2', ← mo_indicator_congr m2 e2, add_comm]
  have h0 : (0 : ℝ) ∈ Ico 0 (1 / √3) := ⟨le_rfl, by positivity⟩
  rcases le_total 0 x with hx0 | hx0
  · exact hmono h0 ⟨hx0, hx.2⟩ hx0
  · rw [← heven x hx]
    exact hmono h0 ⟨neg_nonneg.mpr hx0, by linarith [hx.1]⟩ (neg_nonneg.mpr hx0)

/-! ### Lemma 5.0.7 (4) -/

/-- On the imaginary axis (TeX 4450–4457): `area₀(0, y) = (√3/4)(u - 2v√u)
= (√3/4)√u(√u - 2v)` with `u = ρ₀ρ₂ = (3y² - 1)/(6y²)` and `v = ρ₁ = 1/(√3y)`. -/
private lemma mo_areaFn_zero_axis {y : ℝ} (hy : 1 ≤ y) :
    areaFn 0 (0, y) = √3 / 4 * ((3 * y ^ 2 - 1) / (6 * y ^ 2) -
      2 * (1 / (√3 * y) * √((3 * y ^ 2 - 1) / (6 * y ^ 2)))) := by
  have hz : ((0 : ℝ), y) ∈ starDomain :=
    mo_mem_starDomain hy ⟨neg_lt_zero.mpr (by positivity), by positivity⟩
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hy0 : 0 < y := by linarith
  obtain ⟨r0, r1, r2⟩ := mo_ρ 0 y hy0
  rw [areaFn_zero_eq hz, r0, r1, r2]
  have hk : 0 < √3 * y := by positivity
  have hu : (1 + √3 * 0) / (√3 * y) * (((√3 * 0) ^ 2 + (3 * y ^ 2 - 1)) / (2 * (√3 * y))) =
      (3 * y ^ 2 - 1) / (6 * y ^ 2) := by
    field_simp; rw [h3]; ring
  have hF : (1 + √3 * 0) / (√3 * y) * ((1 - √3 * 0) / (√3 * y)) ^ 2 *
      (((√3 * 0) ^ 2 + (3 * y ^ 2 - 1)) / (2 * (√3 * y))) =
      (1 / (√3 * y)) ^ 2 * ((3 * y ^ 2 - 1) / (6 * y ^ 2)) := by
    rw [← hu]; ring
  rw [hu, hF, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]

/-- `area₀(0, y)` is increasing in `y ≥ √3` (TeX 4458–4460): `u = ρ₀ρ₂` increases, `v = ρ₁`
decreases, and `√u - 2v ≥ 0` for `y ≥ √3`. -/
private lemma mo_areaFn_zero_axis_mono {y₁ y₂ : ℝ} (h1 : √3 ≤ y₁) (h12 : y₁ ≤ y₂) :
    areaFn 0 (0, y₁) ≤ areaFn 0 (0, y₂) := by
  have hy1 : 1 ≤ y₁ := mo_one_le_sqrt_three.trans h1
  have hy2 : 1 ≤ y₂ := hy1.trans h12
  have hc := mo_c_ge h1
  rw [mo_areaFn_zero_axis hy1, mo_areaFn_zero_axis hy2]
  set u₁ := (3 * y₁ ^ 2 - 1) / (6 * y₁ ^ 2) with hu₁
  set u₂ := (3 * y₂ ^ 2 - 1) / (6 * y₂ ^ 2) with hu₂
  set v₁ := 1 / (√3 * y₁) with hv₁
  set v₂ := 1 / (√3 * y₂) with hv₂
  have hu1 : 0 ≤ u₁ := div_nonneg (by linarith) (by positivity)
  have hu2 : 0 ≤ u₂ := div_nonneg (by nlinarith) (by positivity)
  have hu12 : u₁ ≤ u₂ := by
    rw [hu₁, hu₂, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul h12 h12 (by linarith) (by linarith)]
  have hv12 : v₂ ≤ v₁ := one_div_le_one_div_of_le (by positivity)
    (mul_le_mul_of_nonneg_left h12 (Real.sqrt_nonneg 3))
  have hv1 : 2 * v₁ ≤ √u₁ := by
    have h3sq : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hv : (2 * v₁) ^ 2 = 4 / (3 * y₁ ^ 2) := by
      rw [hv₁, mul_pow, div_pow, mul_pow, h3sq]; ring
    rw [Real.le_sqrt (by positivity) hu1, hv, hu₁, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg y₁]
  have hsq1 : √u₁ * √u₁ = u₁ := Real.mul_self_sqrt hu1
  have hsq2 : √u₂ * √u₂ = u₂ := Real.mul_self_sqrt hu2
  have key : √u₁ * (√u₁ - 2 * v₁) ≤ √u₂ * (√u₂ - 2 * v₂) :=
    mul_le_mul (Real.sqrt_le_sqrt hu12) (by linarith [Real.sqrt_le_sqrt hu12])
      (by linarith) (Real.sqrt_nonneg _)
  have h34 : 0 < √3 / 4 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left key h34.le]

/-- `δ_oct < 0.9025`, from `√32 > 5.656854`, `√8 > 2.828427` and `ln 2 > 0.6931471803`. -/
private lemma mo_octagonDensity_lt : octagonDensity < 0.9025 := by
  unfold octagonDensity
  have h32 : 5.656854 < √32 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h8 : 2.828427 < √8 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hl := Real.log_two_gt_d9
  rw [div_lt_iff₀ (by linarith)]
  norm_num at hl ⊢
  linarith

/-- `δ(0, 4.5) ≥ 3/4 + 2 area₀(0, 4.5)/√3 = 0.9059… > 0.9025`: with `u = 239/486` and
`v = 2/(9√3)`, `2 area₀(0, 4.5)/√3 = u/2 - v√u` and `(v√u)² = 956/118098 < 0.0905²`. -/
private lemma mo_axis_value : 0.9025 < 3 / 4 + 2 * areaFn 0 (0, 9 / 2) / √3 := by
  rw [mo_areaFn_zero_axis (by norm_num)]
  have h3p : 0 < √3 := by positivity
  have h3sq : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hu : (3 * (9 / 2 : ℝ) ^ 2 - 1) / (6 * (9 / 2) ^ 2) = 239 / 486 := by norm_num
  rw [hu]
  set w := 1 / (√3 * (9 / 2)) * √(239 / 486 : ℝ) with hw
  have hw0 : 0 ≤ w := by positivity
  have hw2 : w ^ 2 = 956 / 118098 := by
    have hsq : √(239 / 486 : ℝ) ^ 2 = 239 / 486 := Real.sq_sqrt (by norm_num)
    rw [hw, mul_pow, div_pow, mul_pow, h3sq, hsq]; norm_num
  have hwlt : w < 0.0905 := by nlinarith
  have : 2 * (√3 / 4 * (239 / 486 - 2 * w)) / √3 = 239 / 972 - w := by field_simp; ring
  rw [this]; norm_num; linarith

/-- `(0, y) ∉ h₁` for `y ≥ 1`, so `I₁ area₁(0, y) = 0`: on the imaginary axis
`T₁ = (√3/4)ρ₀ρ₁ = √3/(4k²)` and `T₁^ext = √3ρ₂² = √3c²/(4k²)` with `k = √3y`, `c = 3y² - 1 ≥ 2`,
so `T₁ < T₁^ext`. (The book's step `δ(x, y) ≥ δ(0, y)` of (4) uses this without stating it.) -/
private lemma l2c_not_mem_hRegion_one_axis {y : ℝ} (hy : 1 ≤ y) : ((0 : ℝ), y) ∉ hRegion 1 := by
  have hz0 : ((0 : ℝ), y) ∈ starDomain :=
    mo_mem_starDomain hy ⟨neg_lt_zero.mpr (by positivity), by positivity⟩
  obtain ⟨-, h1, -, -, he1, -, -⟩ := lemma5_0_4 hz0
  obtain ⟨r0, r1, r2⟩ := mo_ρ 0 y (by linarith)
  rintro ⟨-, hle⟩
  change extTriArea 0 y 1 ≤ triArea 0 y 1 at hle
  rw [h1, he1, r0, r1, r2] at hle
  have hc : 2 ≤ 3 * y ^ 2 - 1 := by nlinarith
  have hk : 0 < √3 * y := by positivity
  have h3 : 0 < √3 := by positivity
  simp only [mul_zero, add_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_add] at hle
  generalize √3 * y = k at hk hle
  generalize 3 * y ^ 2 - 1 = c at hc hle
  have e : √3 * (c / (2 * k)) ^ 2 - √3 / 4 * (1 / k) * (1 / k) =
      √3 / (4 * k ^ 2) * (c ^ 2 - 1) := by
    field_simp; ring
  nlinarith [mul_pos (by positivity : 0 < √3 / (4 * k ^ 2)) (by nlinarith : (0 : ℝ) < c ^ 2 - 1)]

/-- The density bound on the imaginary axis: for `y ≥ √3`, `(0, y) ∈ h₀ ∩ h₂ \ h₁` and
`area₂(0, y) = area₀(0, y)`, so `δ(0, y) = 3/4 + 2 area₀(0, y)/√3`. -/
private lemma l2c_densityBound_axis {y : ℝ} (hy : √3 ≤ y) :
    densityBound (0, y) = 3 / 4 + 2 * areaFn 0 (0, y) / √3 := by
  have hy1 : 1 ≤ y := mo_one_le_sqrt_three.trans hy
  have hz0 : ((0 : ℝ), y) ∈ starDomain :=
    mo_mem_starDomain hy1 ⟨neg_lt_zero.mpr (by positivity), by positivity⟩
  have hm0 : ((0 : ℝ), y) ∈ hRegion 0 := mo_mem_hRegion_zero hz0 hy le_rfl
  obtain ⟨e2, m2⟩ := areaFn_two_eq hz0
  rw [neg_zero] at e2 m2
  rw [densityBound_eq, Fin.sum_univ_three, indicator_of_mem hm0,
    indicator_of_notMem (l2c_not_mem_hRegion_one_axis hy1), indicator_of_mem (m2.mpr hm0), e2]
  ring

/-- **Lemma 5.0.7 (4)** (`lem:compactification-lemma`). For all `x ∈ (-1/√3, 1/√3)` and all
`y ≥ 4.5`, `δ(x, y) > δ_oct`.

The book's proof (TeX 4450–4465): `δ(x, y) ≥ δ(0, y) ≥ δ(0, 4.5) = 0.9059… > δ_oct`. The first
inequality is (3) for `I₀area₀ + I₂area₂`, together with `I₁area₁(x, y) ≥ 0 = I₁area₁(0, y)`: (3)
does not control `I₁area₁`, and the fact that `(0, y) ∉ h₁` (`T₁ < T₁^ext` on the imaginary axis,
`l2c_not_mem_hRegion_one_axis`) is unstated in the book. The second is the monotonicity of
`δ(0, y) = 3/4 + 2area₀(0, y)/√3` in `y ≥ √3` (`area₀(0, y)` is increasing). -/
theorem lemma5_0_7_4 {x y : ℝ} (hx : x ∈ Ioo (-(1 / √3)) (1 / √3)) (hy : 9 / 2 ≤ y) :
    octagonDensity < densityBound (x, y) := by
  have h3lt : √3 < 9 / 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hy3 : √3 ≤ y := by linarith
  have hy1 : 1 ≤ y := mo_one_le_sqrt_three.trans hy3
  have hz := mo_mem_starDomain hy1 hx
  -- `δ(x, y) ≥ δ(0, y)`: (3), and `I₁area₁(x, y) ≥ 0 = I₁area₁(0, y)` as `(0, y) ∉ h₁`
  have hδ0 : densityBound (0, y) ≤ densityBound (x, y) := by
    have hS := lemma5_0_7_3 hy3 hx
    have hI1 : 0 ≤ (hRegion 1).indicator (areaFn 1) (x, y) := by
      rw [mo_indicator_eq_max hz]; exact le_max_right _ _
    rw [densityBound_eq, densityBound_eq, Fin.sum_univ_three, Fin.sum_univ_three,
      indicator_of_notMem (l2c_not_mem_hRegion_one_axis hy1)]
    gcongr 3 / 4 + ?_ / _
    linarith
  -- `δ(0, y) = 3/4 + 2area₀(0, y)/√3` is increasing in `y ≥ √3`: `δ(0, y) ≥ δ(0, 4.5)`
  have hδy : densityBound (0, 9 / 2) ≤ densityBound (0, y) := by
    rw [l2c_densityBound_axis h3lt.le, l2c_densityBound_axis hy3]
    have := mo_areaFn_zero_axis_mono (y₁ := 9 / 2) h3lt.le hy
    gcongr
  -- `δ(0, 4.5) = 0.9059… > 0.9025 > δ_oct`
  have hval : octagonDensity < densityBound (0, 9 / 2) := by
    rw [l2c_densityBound_axis h3lt.le]
    exact mo_octagonDensity_lt.trans mo_axis_value
  exact hval.trans_le (hδy.trans hδ0)

end SmoothedPolygons
