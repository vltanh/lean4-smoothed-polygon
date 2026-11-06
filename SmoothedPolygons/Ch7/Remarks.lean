module

public import SmoothedPolygons.Ch7.StrongTransversality
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import SmoothedPolygons.Ch7.SmoothedPolygon
public import SmoothedPolygons.Ch3.AreaFormula

/-!
# Remarks on the smoothed polygons (Remarks 7.5.2 and 7.6.4)

* Remark 7.5.2: along the strong lift of Theorem 7.5.1 (normalized by `λ_cost = -1`),
  `d(y₀) = det Λ₁(t) = λ₁² det Λ₁₀` is a constant of motion with an explicit formula; it is strictly
  increasing in `y₀ ∈ (1/√3, 1)` with range `(0, 9/4)`, so it determines `y₀`.
* Remark 7.6.4: the smoothed `(6k - 2)`-gons of Remark 7.6.2, with `k` allowed to be real, tend to a
  rectangle of area `√12` as `k → 1⁺`.

## The smoothed `(6k - 2)`-gons (Remark 7.6.2)

The book specifies them by the control mode sequence `((1, t_sw), (2, t_sw), …, (3k - 1, t_sw))`
(`eqn:3k+2`), the initial point `z₀ = i y₀` with `y₀ > 1`, the switching time
`t_sw = -ln(4/(3y₀² + 1))/(√3 y₀)` and the initial control `e₂`. As in `eqn:3k+1` (where the mode
`-i` is the control `R⁻ⁱ · e₃`), the mode `m` is the control `R^m · e₃`; so the controls are
`e₂, e₁, e₃, e₂, …` (`R · e₃ = e₂`, `R · e₂ = e₁`, `R · e₁ = e₃`, `R_conj_controlMatrix_vertex`),
and the terminal time is `t_f = (3k - 1) t_sw`.

The book does not display the condition that fixes `y₀` in terms of `k` ("the changes are minor").
It is the analogue of Lemma 7.5.5 (`eqn:theta-k`): with control `e₂`, `z(t_sw) = R · z₀`, the
trajectory is `g(t) = (g_sw R)ⁱ g₀(t - i t_sw) R⁻ⁱ` on the `i`-th switching interval, and
`g(t_f) = R` reads `(g_sw R)^{3k-1} = R^{3k} = (-1)ᵏ`; since `tr(g_sw R) = 4/(3y₀² + 1)`, the choice
of eigenvalues of Lemma 7.5.5 gives `4/(3y₀² + 1) = 2 cos(πk/(3k - 1))` (checked numerically:
`g(t_f) = R` for `k = 2, 3`). For real `k > 1` this defines `y₀(k) > 1`; as `k → 1⁺`,
`y₀(k) → ∞`, which is how the `(6k - 2)`-gon "degenerates" at `k = 1`. For non-integral `k`, the
trajectory on `[0, t_f]` does not satisfy the boundary condition `g(t_f) = R` ("smoothed rectangles
that do not quite satisfy the boundary conditions").
-/

@[expose] public section

namespace SmoothedPolygons

open Filter Topology Matrix

/-! ### Remark 7.5.2 -/

/-- The constant of motion of Remark 7.5.2,
`d(y₀) = (-1 + 2y₀² + 3y₀⁴)(3 + 6y₀² - (1 + 3y₀²) ℓ(y₀))² / (144 y₀⁸)`, where
`ℓ(y₀) = ln(4/(3y₀² + 1))`. -/
noncomputable def detConstOfMotion (y0 : ℝ) : ℝ :=
  (-1 + 2 * y0 ^ 2 + 3 * y0 ^ 4) *
    (3 + 6 * y0 ^ 2 - (1 + 3 * y0 ^ 2) * Real.log (4 / (3 * y0 ^ 2 + 1))) ^ 2 / (144 * y0 ^ 8)

/-- `det(λ₁ Λ₁₀) = d(y₀)`: the algebra of Remark 7.5.2. -/
private lemma r3_strongL₁_sq_det (y0 : ℝ) (hy0 : 0 < y0) :
    strongL₁ y0 ^ 2 * (Λ₁₀ y0).det = detConstOfMotion y0 := by
  have h3' : √3 ≠ 0 := by positivity
  have hy : y0 ≠ 0 := hy0.ne'
  have h13 : 1 + 3 * y0 ^ 2 ≠ 0 := by positivity
  simp only [strongL₁, ellSw, Λ₁₀, detConstOfMotion, Matrix.det_smul, Matrix.det_fin_two_of,
    Fintype.card_fin]
  field_simp
  ring_nf

/-! #### Monotonicity of `d(y₀)`: the factored derivative -/

/-- The factor `E(y) = 3 + 6y² - (1 + 3y²) ℓ(y)` of `d` and of `d'`. -/
private noncomputable def sm_E (y : ℝ) : ℝ :=
  3 + 6 * y ^ 2 - (1 + 3 * y ^ 2) * Real.log (4 / (3 * y ^ 2 + 1))

/-- The second factor `F(y) = 2ℓ(y)(3y⁴ - 1) + 9y⁶ - 9y⁴ - 6y² + 6` of `d'`. -/
private noncomputable def sm_F (y : ℝ) : ℝ :=
  2 * Real.log (4 / (3 * y ^ 2 + 1)) * (3 * y ^ 4 - 1) + 9 * y ^ 6 - 9 * y ^ 4 - 6 * y ^ 2 + 6

/-- The derivative of `d` factors: `d'(y) = E(y) F(y)/(36 y⁹)`. -/
private theorem sm_hasDerivAt_detConstOfMotion {y : ℝ} (hy : 0 < y) :
    HasDerivAt detConstOfMotion (sm_E y * sm_F y / (36 * y ^ 9)) y := by
  have hq : 0 < 3 * y ^ 2 + 1 := by positivity
  have h1 : HasDerivAt (fun y : ℝ ↦ 3 * y ^ 2 + 1) (3 * (2 * y ^ 1)) y := by
    simpa using ((hasDerivAt_pow 2 y).const_mul 3).add_const 1
  have h2 : HasDerivAt (fun y : ℝ ↦ 4 / (3 * y ^ 2 + 1))
      ((0 * (3 * y ^ 2 + 1) - 4 * (3 * (2 * y ^ 1))) / (3 * y ^ 2 + 1) ^ 2) y :=
    (hasDerivAt_const y (4 : ℝ)).div h1 hq.ne'
  have h3 := h2.log (by positivity)
  have hp : HasDerivAt (fun y : ℝ ↦ -1 + 2 * y ^ 2 + 3 * y ^ 4)
      (2 * ((2 : ℕ) * y ^ 1) + 3 * ((4 : ℕ) * y ^ 3)) y :=
    (((hasDerivAt_pow 2 y).const_mul 2).const_add (-1)).add ((hasDerivAt_pow 4 y).const_mul 3)
  have he := ((hasDerivAt_pow 2 y).const_mul 6).const_add 3 |>.sub
    ((((hasDerivAt_pow 2 y).const_mul 3).const_add 1).mul h3)
  have h8 : HasDerivAt (fun y : ℝ ↦ 144 * y ^ 8) (144 * ((8 : ℕ) * y ^ 7)) y :=
    (hasDerivAt_pow 8 y).const_mul 144
  have key := (hp.mul (he.pow 2)).div h8 (by positivity)
  unfold detConstOfMotion
  convert key using 1
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, Nat.cast_ofNat, Nat.add_one_sub_one,
    pow_one]
  unfold sm_E sm_F
  field_simp
  ring

/-- `E(y) > 0` for `y > 0`: by `ℓ ≤ 4/(3y² + 1) - 1`, `(1 + 3y²) ℓ ≤ 3 - 3y²`. -/
private theorem sm_E_pos {y : ℝ} (hy : 0 < y) : 0 < sm_E y := by
  have hq : 0 < 3 * y ^ 2 + 1 := by positivity
  have hL := Real.log_le_sub_one_of_pos (show 0 < 4 / (3 * y ^ 2 + 1) by positivity)
  have : (1 + 3 * y ^ 2) * Real.log (4 / (3 * y ^ 2 + 1)) ≤ 3 - 3 * y ^ 2 :=
    calc _ ≤ (1 + 3 * y ^ 2) * (4 / (3 * y ^ 2 + 1) - 1) :=
          mul_le_mul_of_nonneg_left hL (by positivity)
      _ = 3 - 3 * y ^ 2 := by field_simp; ring
  unfold sm_E
  nlinarith

/-- `2(x - 1)/(x + 1) ≤ ln x` for `x ≥ 1` (first term of the series of `ln x`). -/
private theorem sm_two_mul_div_le_log {x : ℝ} (hx : 1 ≤ x) :
    2 * (x - 1) / (x + 1) ≤ Real.log x := by
  have h := Real.hasSum_log_one_add (show 0 ≤ x - 1 by linarith)
  have h0 := le_hasSum h 0 fun j _ ↦
    mul_nonneg (by positivity) (pow_nonneg (div_nonneg (by linarith) (by linarith)) _)
  rw [show (1 : ℝ) + (x - 1) = x by ring, show x - 1 + 2 = x + 1 by ring] at h0
  norm_num at h0
  convert h0 using 1
  ring

/-- `F(y) > 0` for `y ∈ (1/√3, 1)` (it has a double zero at `y = 1`). With `s = y²`:
`F = 2(3s² - 1)(ℓ - 6(1 - s)/(3s + 5)) + 3(1 - s)²(9s² + 12s + 6)/(3s + 5)` and
`F = 2(3s² - 1)(ℓ - 3(1 - s)/(3s + 1)) + 9s(1 - s)²(3s + 2)/(3s + 1)`; the first form is used
when `3s² ≥ 1` (with `ℓ ≥ 2(x - 1)/(x + 1)`, `x = 4/(3s + 1)`), the second when `3s² < 1` (with
`ℓ ≤ x - 1`). -/
private theorem sm_F_pos {y : ℝ} (hy0 : 1 / √3 < y) (hy1 : y < 1) : 0 < sm_F y := by
  have hy : 0 < y := lt_trans (by positivity) hy0
  have hs := str_one_third_lt_sq hy0
  have hs1 : y ^ 2 < 1 := by nlinarith
  set L := Real.log (4 / (3 * y ^ 2 + 1)) with hL
  have hq : 0 < 3 * y ^ 2 + 1 := by positivity
  have hq5 : 0 < 3 * y ^ 2 + 5 := by positivity
  have h1s : 0 < 1 - y ^ 2 := by linarith
  rcases le_or_gt 1 (3 * y ^ 4) with h | h
  · have hlb : 6 * (1 - y ^ 2) / (3 * y ^ 2 + 5) ≤ L := by
      have hx : 1 ≤ 4 / (3 * y ^ 2 + 1) := by rw [le_div_iff₀ hq]; linarith
      have := sm_two_mul_div_le_log hx
      convert this using 1
      field_simp
      ring
    have key : sm_F y = 2 * (3 * y ^ 4 - 1) * (L - 6 * (1 - y ^ 2) / (3 * y ^ 2 + 5)) +
        3 * (1 - y ^ 2) ^ 2 * (9 * y ^ 4 + 12 * y ^ 2 + 6) / (3 * y ^ 2 + 5) := by
      unfold sm_F
      rw [← hL]
      field_simp
      ring
    rw [key]
    refine add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) (by linarith)) ?_
    exact div_pos (mul_pos (by positivity) (by positivity)) hq5
  · have hub : L ≤ 3 * (1 - y ^ 2) / (3 * y ^ 2 + 1) := by
      have := Real.log_le_sub_one_of_pos (show 0 < 4 / (3 * y ^ 2 + 1) by positivity)
      convert this using 1
      field_simp
      ring
    have key : sm_F y = 2 * (3 * y ^ 4 - 1) * (L - 3 * (1 - y ^ 2) / (3 * y ^ 2 + 1)) +
        9 * y ^ 2 * (1 - y ^ 2) ^ 2 * (3 * y ^ 2 + 2) / (3 * y ^ 2 + 1) := by
      unfold sm_F
      rw [← hL]
      field_simp
      ring
    rw [key]
    refine add_pos_of_nonneg_of_pos (mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)) ?_
    exact div_pos (mul_pos (mul_pos (by positivity) (by positivity)) (by positivity)) hq

/-- `d` is strictly increasing on `[1/√3, 1]` (its derivative `E F/(36 y⁹)` is positive inside). -/
private theorem sm_detConstOfMotion_strictMonoOn :
    StrictMonoOn detConstOfMotion (Set.Icc (1 / √3) 1) := by
  have hpos : (0 : ℝ) < 1 / √3 := by positivity
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _) (fun y hy ↦
    (sm_hasDerivAt_detConstOfMotion (lt_of_lt_of_le hpos hy.1)).continuousAt.continuousWithinAt)
    fun y hy ↦ ?_
  rw [interior_Icc] at hy
  have hy0 : 0 < y := lt_trans hpos hy.1
  rw [(sm_hasDerivAt_detConstOfMotion hy0).deriv]
  exact div_pos (mul_pos (sm_E_pos hy0) (sm_F_pos hy.1 hy.2)) (by positivity)

private theorem sm_detConstOfMotion_left : detConstOfMotion (1 / √3) = 0 := by
  have h : -1 + 2 * (1 / √3) ^ 2 + 3 * (1 / √3) ^ 4 = 0 := by
    rw [div_pow, div_pow, str_sqrt3_sq, str_sqrt3_pow4]; norm_num
  unfold detConstOfMotion
  rw [h, zero_mul, zero_div]

private theorem sm_detConstOfMotion_right : detConstOfMotion 1 = 9 / 4 := by
  unfold detConstOfMotion
  norm_num [Real.log_one]

/-- **Remark 7.5.2** (`rem:det-lambda1`, label of this formalization). Let `y₀ ∈ (1/√3, 1)` and
let `(Λ₁, Λ_R, λ_cost = -1)` be the costate lift of Theorem 7.5.1 (`IsStrongLift`). Then
`d = d(y₀) := det Λ₁(t) = λ₁² det Λ₁₀` is a constant of motion, equal to
`(-1 + 2y₀² + 3y₀⁴)(3 + 6y₀² - (1 + 3y₀²) ℓ(y₀))² / (144 y₀⁸)` with `ℓ(y₀) = ln(4/(3y₀² + 1))`, for
all times `t ∈ [0, t_sw]`. The function `d` is monotonic increasing in `y₀ ∈ (1/√3, 1)` with range
`(0, 9/4)`; thus the determinant uniquely determines the parameter `y₀` of the triangle.

Reading: "monotonic increasing" is strict monotonicity (`StrictMonoOn`), which is what the last
sentence (`d` determines `y₀`, `Set.InjOn`) needs; the remark is about the lift normalized by
`λ_cost = -1` (for the lift `c (Λ₁, Λ_R, -1)` the determinant is `c² d(y₀)`).

Proof of monotonicity and range (the book: "the derivative factors in a nice way"):
`d'(y) = E(y) F(y)/(36 y⁹)` with `E = 3 + 6y² - (1 + 3y²) ℓ` and
`F = 2ℓ(3y⁴ - 1) + 9y⁶ - 9y⁴ - 6y² + 6` (`sm_hasDerivAt_detConstOfMotion`). On `(1/√3, 1)`,
`E > 0` (by `ℓ ≤ x - 1`) and `F > 0` (`F` has a double zero at `y = 1`; with `s = y²` it is
bounded below using `ℓ ≥ 2(x - 1)/(x + 1)` when `3s² ≥ 1` and `ℓ ≤ x - 1` when `3s² < 1`,
`x = 4/(3s + 1)`), so `d` is strictly increasing on `[1/√3, 1]`; `d(1/√3) = 0`, `d(1) = 9/4`, and
the range follows by continuity and the intermediate value theorem. -/
theorem remark7_5_2 :
    (∀ y0 : ℝ, 1 / √3 < y0 → y0 < 1 → ∀ Λ₁ ΛR : ℝ → Mat2, IsStrongLift y0 Λ₁ ΛR (-1) →
      ∀ t ∈ Set.Icc 0 (switchTime y0),
        (Λ₁ t).det = strongL₁ y0 ^ 2 * (Λ₁₀ y0).det ∧ (Λ₁ t).det = detConstOfMotion y0) ∧
    StrictMonoOn detConstOfMotion (Set.Ioo (1 / √3) 1) ∧
    detConstOfMotion '' Set.Ioo (1 / √3) 1 = Set.Ioo 0 (9 / 4) ∧
    Set.InjOn detConstOfMotion (Set.Ioo (1 / √3) 1) := by
  have hmono : StrictMonoOn detConstOfMotion (Set.Ioo (1 / √3) 1) :=
    sm_detConstOfMotion_strictMonoOn.mono Set.Ioo_subset_Icc_self
  refine ⟨fun y0 hy0 hy1 Λ₁ ΛR h t ht ↦ ?_, hmono, ?_, hmono.injOn⟩
  · have hy0' : 0 < y0 := lt_trans (by positivity) hy0
    have hdet1 : (segG y0 t).det = 1 := (seg_solution y0 0 hy0').2.2.2.2 t
    have hΛ : (Λ₁ t).det = strongL₁ y0 ^ 2 * (Λ₁₀ y0).det := by
      rw [(strongLift_unique y0 hy0 hy1 Λ₁ ΛR (-1) h t ht).1, neg_neg, one_smul, strongΛ₁,
        Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, hdet1, Ring.inverse_one,
        Matrix.det_smul, Fintype.card_fin]
      ring
    exact ⟨hΛ, hΛ.trans (r3_strongL₁_sq_det y0 hy0')⟩
  · -- the range: `d(1/√3) = 0`, `d(1) = 9/4`, strict monotonicity and the intermediate value
    -- theorem
    have hlt : 1 / √3 < (1 : ℝ) := by
      rw [div_lt_one (by positivity), Real.lt_sqrt (by norm_num)]; norm_num
    have hm := sm_detConstOfMotion_strictMonoOn
    have hcont : ContinuousOn detConstOfMotion (Set.Icc (1 / √3) 1) := fun y hy ↦
      (sm_hasDerivAt_detConstOfMotion (lt_of_lt_of_le (by positivity) hy.1)).continuousAt
        |>.continuousWithinAt
    have hl : (1 / √3 : ℝ) ∈ Set.Icc (1 / √3) 1 := ⟨le_rfl, hlt.le⟩
    have hr : (1 : ℝ) ∈ Set.Icc (1 / √3) 1 := ⟨hlt.le, le_rfl⟩
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      have hy' := Set.Ioo_subset_Icc_self hy
      rw [← sm_detConstOfMotion_left, ← sm_detConstOfMotion_right]
      exact ⟨hm hl hy' hy.1, hm hy' hr hy.2⟩
    · have := intermediate_value_Ioo hlt.le hcont
      rwa [sm_detConstOfMotion_left, sm_detConstOfMotion_right] at this

/-! ### The smoothed `(6k - 2)`-gons (Remark 7.6.2) and Remark 7.6.4 -/

/-- The switching time `t_sw = -ln(4/(3y₀² + 1))/(√3 y₀)` of the smoothed `(6k - 2)`-gon
(Remark 7.6.2; positive for `y₀ > 1`). -/
noncomputable def minusSwitchTime (y0 : ℝ) : ℝ := -Real.log (4 / (3 * y0 ^ 2 + 1)) / (√3 * y0)

/-- The control of the smoothed `(6k - 2)`-gon with switching time `τ` (`eqn:3k+2`): on the
`i`-th switching interval `[iτ, (i+1)τ)` it is the mode `i + 1`, the vertex `R^{i+1} · e₃ = Rⁱ · e₂`
of `U_T`; so the controls are `e₂, e₁, e₃, e₂, …`, that is, `Pi.single ((1 + 2i) mod 3) 1`. -/
noncomputable def minusPolygonControlAt (τ t : ℝ) : Fin 3 → ℝ :=
  Pi.single (⟨(1 + 2 * ⌊t / τ⌋₊) % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3) 1

/-- The angle `πk/(3k - 1)` of the smoothed `(6k - 2)`-gon, for real `k`. -/
noncomputable def minusθ (k : ℝ) : ℝ := Real.pi * k / (3 * k - 1)

/-- The height `y₀(k)` of the initial point `z₀ = i y₀` of the smoothed `(6k - 2)`-gon, for real
`k > 1`: the positive solution of `4/(3y₀² + 1) = 2 cos(πk/(3k - 1))` (the analogue of
`eqn:theta-k`, see the module docstring). -/
noncomputable def minusY₀ (k : ℝ) : ℝ := √((2 / Real.cos (minusθ k) - 1) / 3)

/-- The terminal time `t_f = (3k - 1) t_sw` of the smoothed `(6k - 2)`-gon, for real `k`. -/
noncomputable def minusTf (k : ℝ) : ℝ := (3 * k - 1) * minusSwitchTime (minusY₀ k)

/-! ### The `e₂`-arc of the smoothed `(6k - 2)`-gon in closed form

With control `e₂` from `X₀ = Φ(i y₀)`: `P₀ = Z_{e₂}/⟨Z_{e₂}, X₀⟩ = [[-√3y₀/2, y₀], [0, √3y₀/2]]`,
`X(t) = Φ(z(t))` with `z(t) = (1 - W)/√3 + i y₀ W`, `W = exp(-√3 y₀ t)` (the mirror image of the
`e₃`-arc of `segX_eq`), and `z(t_sw) = R · z₀`. -/

/-- `P₀ = Z_{e₂}/⟨Z_{e₂}, Φ(i y₀)⟩`. -/
private noncomputable def sm_mP (y0 : ℝ) : Mat2 := controlP (vertex 1) (Φ 0 y0)

/-- The group trajectory with constant control `e₂` from `z₀ = i y₀`. -/
private noncomputable def sm_mG (y0 t : ℝ) : Mat2 := constControlG (Φ 0 y0) (sm_mP y0) t

/-- The Lie algebra trajectory with constant control `e₂` from `X₀ = Φ(i y₀)`. -/
private noncomputable def sm_mX (y0 t : ℝ) : Mat2 := constControlX (Φ 0 y0) (sm_mP y0) t

/-- `exp(tA) = cosh(ct) I + sinh(ct)/c A` for traceless `A` with `det A = -c²` (Lemma A.6.4). -/
private lemma sm_exp_smul_of_det_neg (A : Mat2) (hA : A.trace = 0) {c : ℝ} (hc : 0 < c)
    (hdet : A.det = -c ^ 2) (t : ℝ) :
    NormedSpace.exp (t • A) =
      ((Real.exp (c * t) + (Real.exp (c * t))⁻¹) / 2) • (1 : Mat2) +
        ((Real.exp (c * t) - (Real.exp (c * t))⁻¹) / (2 * c)) • A := by
  have hneg : A.det < 0 := by rw [hdet]; nlinarith [sq_pos_of_pos hc]
  have hs : √(-A.det) = c := by rw [hdet, neg_neg, Real.sqrt_sq hc.le]
  rw [((lemmaA_6_4 A hA).2 t).1 hneg, hs, Real.cosh_eq, Real.sinh_eq, mul_comm t c,
    Real.exp_neg, div_div]

private lemma sm_mP_eq (y0 : ℝ) (hy0 : y0 ≠ 0) :
    sm_mP y0 = !![-(√3 * y0 / 2), y0; 0, √3 * y0 / 2] := by
  have h3 : (0 : ℝ) < √3 := by positivity
  rw [sm_mP, controlP, str_traceForm_Z2_Φ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [controlMatrix, vertex] <;> field_simp <;>
    nlinarith [str_sqrt3_sq]

private lemma sm_exp_mP (y0 : ℝ) (hy0 : 0 < y0) (t : ℝ) :
    NormedSpace.exp (t • sm_mP y0) =
      !![(Real.exp (√3 * y0 / 2 * t))⁻¹,
        (Real.exp (√3 * y0 / 2 * t) - (Real.exp (√3 * y0 / 2 * t))⁻¹) / √3;
        0, Real.exp (√3 * y0 / 2 * t)] := by
  have h3 : (0 : ℝ) < √3 := by positivity
  rw [sm_exp_smul_of_det_neg (sm_mP y0) ?_ (c := √3 * y0 / 2) (by positivity) ?_ t,
    sm_mP_eq y0 hy0.ne']
  · ext i j
    fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring
  · simp [sm_mP_eq y0 hy0.ne', Matrix.trace_fin_two]
  · simp [sm_mP_eq y0 hy0.ne', Matrix.det_fin_two]
    ring

private lemma sm_exp_XP (y0 : ℝ) (hy0 : 0 < y0) (t : ℝ) :
    NormedSpace.exp (t • (Φ 0 y0 + sm_mP y0)) =
      !![(Real.exp (√3 * y0 / 2 * t))⁻¹, 0;
        (Real.exp (√3 * y0 / 2 * t) - (Real.exp (√3 * y0 / 2 * t))⁻¹) / (√3 * y0 ^ 2),
        Real.exp (√3 * y0 / 2 * t)] := by
  have h3 : (0 : ℝ) < √3 := by positivity
  have hXP : Φ 0 y0 + sm_mP y0 = !![-(√3 * y0 / 2), 0; 1 / y0, √3 * y0 / 2] := by
    rw [sm_mP_eq y0 hy0.ne']
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Φ]
    field_simp
    ring
  rw [sm_exp_smul_of_det_neg _ ?_ (c := √3 * y0 / 2) (by positivity) ?_ t, hXP]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring
  · simp [hXP, Matrix.trace_fin_two]
  · simp [hXP, Matrix.det_fin_two]
    field_simp

/-- `X(z₀, t) = Φ(z(t))`, `z(t) = (1 - W)/√3 + i y₀ W`, `W = exp(-√3 y₀ t)`. -/
private theorem sm_mX_eq (y0 t : ℝ) (hy0 : 0 < y0) :
    sm_mX y0 t =
      Φ ((1 - Real.exp (-(√3 * y0 * t))) / √3) (y0 * Real.exp (-(√3 * y0 * t))) := by
  have h3 : (0 : ℝ) < √3 := by positivity
  have hw : 0 < Real.exp (√3 * y0 / 2 * t) := Real.exp_pos _
  have hW : Real.exp (-(√3 * y0 * t)) = (Real.exp (√3 * y0 / 2 * t) ^ 2)⁻¹ := by
    rw [sq, ← Real.exp_add, ← Real.exp_neg]; ring_nf
  have hneg : Real.exp (√3 * y0 / 2 * -t) = (Real.exp (√3 * y0 / 2 * t))⁻¹ := by
    rw [mul_neg, Real.exp_neg]
  rw [sm_mX, constControlX, sm_exp_mP y0 hy0, sm_exp_mP y0 hy0, hneg, hW]
  generalize Real.exp (√3 * y0 / 2 * t) = w at hw ⊢
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Φ] <;> field_simp <;> ring_nf

/-- `g₀(z₀, t)` in closed form, `W = exp(-√3 y₀ t)`. -/
private theorem sm_mG_eq (y0 t : ℝ) (hy0 : 0 < y0) :
    sm_mG y0 t = !![1, (Real.exp (-(√3 * y0 * t)) - 1) / √3;
      ((Real.exp (-(√3 * y0 * t)))⁻¹ - 1) / (√3 * y0 ^ 2),
      1 - (Real.exp (-(√3 * y0 * t)) - 2 + (Real.exp (-(√3 * y0 * t)))⁻¹) / (3 * y0 ^ 2)] := by
  have h3 : (0 : ℝ) < √3 := by positivity
  have hw : 0 < Real.exp (√3 * y0 / 2 * t) := Real.exp_pos _
  have hW : Real.exp (-(√3 * y0 * t)) = (Real.exp (√3 * y0 / 2 * t) ^ 2)⁻¹ := by
    rw [sq, ← Real.exp_add, ← Real.exp_neg]; ring_nf
  have hneg : Real.exp (√3 * y0 / 2 * -t) = (Real.exp (√3 * y0 / 2 * t))⁻¹ := by
    rw [mul_neg, Real.exp_neg]
  rw [sm_mG, constControlG, sm_exp_XP y0 hy0, sm_exp_mP y0 hy0, hneg, hW]
  generalize Real.exp (√3 * y0 / 2 * t) = w at hw ⊢
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp
  ring_nf
  simp only [str_sqrt3_sq]
  ring

/-- The `e₂`-arc solves the state equations with constant control `e₂`. -/
private theorem sm_m_solution (y0 t : ℝ) :
    HasDerivAtEntrywise (sm_mG y0) (sm_mG y0 t * sm_mX y0 t) t ∧
      HasDerivAtEntrywise (sm_mX y0)
        (controlP (vertex 1) (sm_mX y0 t) * sm_mX y0 t -
          sm_mX y0 t * controlP (vertex 1) (sm_mX y0 t)) t ∧
      sm_mG y0 0 = 1 ∧ sm_mX y0 0 = Φ 0 y0 :=
  constControl_solution (vertex 1) (Φ 0 y0) t

private lemma sm_mX_continuous (y0 : ℝ) : Continuous (sm_mX y0) :=
  continuous_iff_continuousAt.2 fun t ↦ (sm_m_solution y0 t).2.1.continuousAt

private lemma sm_mG_continuous (y0 : ℝ) : Continuous (sm_mG y0) :=
  continuous_iff_continuousAt.2 fun t ↦ (sm_m_solution y0 t).1.continuousAt

/-- `-√3 y₀ t_sw = ln(4/(3y₀² + 1))`, so `W(t_sw) = 4/(3y₀² + 1)`. -/
private lemma sm_exp_switchTime {y0 : ℝ} (hy0 : 0 < y0) :
    Real.exp (-(√3 * y0 * minusSwitchTime y0)) = 4 / (3 * y0 ^ 2 + 1) := by
  have h3 : (0 : ℝ) < √3 := by positivity
  rw [show -(√3 * y0 * minusSwitchTime y0) = Real.log (4 / (3 * y0 ^ 2 + 1)) by
    rw [minusSwitchTime]; field_simp, Real.exp_log (by positivity)]

/-- The gluing condition `z(z₀, t_sw) = R · z₀`: `X(z₀, t_sw) = R X₀ R⁻¹`. -/
private theorem sm_mX_switchTime {y0 : ℝ} (hy0 : 0 < y0) :
    sm_mX y0 (minusSwitchTime y0) = R * Φ 0 y0 * R⁻¹ := by
  have h3 : (0 : ℝ) < √3 := by positivity
  rw [sm_mX_eq _ _ hy0, sm_exp_switchTime hy0, str_R_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Φ, R] <;> field_simp <;> ring_nf <;>
    simp only [str_sqrt3_sq, str_sqrt3_pow4] <;> ring

/-! ### The spline of the smoothed `(6k - 2)`-gon on three switching intervals

On the `i`-th switching interval the trajectory is `X = Rⁱ X(z₀, t - i t_sw) R⁻ⁱ` and
`g = (g_sw R)ⁱ g₀(z₀, t - i t_sw) R⁻ⁱ` (Remark 7.6.2, `eqn:gamma-bang-bang`); for `k ∈ (1, 4/3)`
the terminal time `t_f = (3k - 1) t_sw` lies in `(2 t_sw, 3 t_sw)`, so three intervals are used. -/

/-- `R Z_{e₂} R⁻¹ = Z_{e₁}`. -/
private lemma sm_R_conj_vertex_one :
    R * controlMatrix (vertex 1) * R⁻¹ = controlMatrix (vertex 0) := by
  have h := poly_Rinv_conj_vertex 0
  rw [show (0 : Fin 3) + 1 = 1 from rfl] at h
  rw [← h, show R * (R⁻¹ * controlMatrix (vertex 0) * R) * R⁻¹ =
    (R * R⁻¹) * controlMatrix (vertex 0) * (R * R⁻¹) by simp only [Matrix.mul_assoc],
    poly_R_mul_inv, Matrix.one_mul, Matrix.mul_one]

/-- `R Z_{e₁} R⁻¹ = Z_{e₃}`. -/
private lemma sm_R_conj_vertex_zero :
    R * controlMatrix (vertex 0) * R⁻¹ = controlMatrix (vertex 2) := by
  have h := poly_Rinv_conj_vertex 2
  rw [show (2 : Fin 3) + 1 = 0 from rfl] at h
  rw [← h, show R * (R⁻¹ * controlMatrix (vertex 2) * R) * R⁻¹ =
    (R * R⁻¹) * controlMatrix (vertex 2) * (R * R⁻¹) by simp only [Matrix.mul_assoc],
    poly_R_mul_inv, Matrix.one_mul, Matrix.mul_one]

/-- Shifting a solution with control `e_m` in time and conjugating it by `R` gives a solution with
control `e_{m'}`, where `R Z_{e_m} R⁻¹ = Z_{e_{m'}}`. -/
private lemma sm_shift_conj {G Y : ℝ → Mat2} {m m' : Fin 3}
    (hZ : R * controlMatrix (vertex m) * R⁻¹ = controlMatrix (vertex m')) (A : Mat2) (τ : ℝ)
    (hY : ∀ t, HasDerivAtEntrywise Y
      (controlP (vertex m) (Y t) * Y t - Y t * controlP (vertex m) (Y t)) t)
    (hG : ∀ t, HasDerivAtEntrywise G (G t * Y t) t) (t : ℝ) :
    HasDerivAtEntrywise (fun s ↦ R * Y (s - τ) * R⁻¹)
      (controlP (vertex m') (R * Y (t - τ) * R⁻¹) * (R * Y (t - τ) * R⁻¹) -
        (R * Y (t - τ) * R⁻¹) * controlP (vertex m') (R * Y (t - τ) * R⁻¹)) t ∧
    HasDerivAtEntrywise (fun s ↦ A * R * G (s - τ) * R⁻¹)
      ((A * R * G (t - τ) * R⁻¹) * (R * Y (t - τ) * R⁻¹)) t := by
  have h1 := HasDerivAtEntrywise.scomp (h := fun s ↦ s - τ) (hY (t - τ))
    ((hasDerivAt_id' t).sub_const τ)
  have h2 := (h1.const_mul R).mul_const R⁻¹
  rw [one_smul, poly_conj_bracket poly_inv_mul_R, poly_controlP_conj poly_inv_mul_R hZ] at h2
  have g1 := HasDerivAtEntrywise.scomp (h := fun s ↦ s - τ) (hG (t - τ))
    ((hasDerivAt_id' t).sub_const τ)
  have g2 := (g1.const_mul (A * R)).mul_const R⁻¹
  rw [one_smul] at g2
  refine ⟨h2, ?_⟩
  convert g2 using 1
  simp only [Matrix.mul_assoc, poly_Rinv_cancel]

/-- **Uniqueness on one switching interval.** A state trajectory whose control is the vertex `e_m`
on `[α, β)` agrees on `[α, β]` with any solution `(G, Y)` of the state equations with control `e_m`
that it agrees with at `α`: `⟨X, Z_u⟩` is constant (Lemma 7.1.1), so `X' = [P, X]` is linear with
constant `P`, and then `g' = gX` (as in `poly_trajectory_unique`). -/
private theorem sm_seg_unique {T α β : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsStateTrajectory T u g X) (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ T) {m : Fin 3}
    (hu : ∀ t ∈ Set.Ico α β, u t = vertex m) {G Y : ℝ → Mat2} (hYc : Continuous Y)
    (hGc : Continuous G)
    (hY : ∀ t, HasDerivAtEntrywise Y
      (controlP (vertex m) (Y t) * Y t - Y t * controlP (vertex m) (Y t)) t)
    (hG : ∀ t, HasDerivAtEntrywise G (G t * Y t) t) (hX0 : X α = Y α) (hg0 : g α = G α) :
    ∀ t ∈ Set.Icc α β, g t = G t ∧ X t = Y t := by
  obtain ⟨hT, -, -, hst, hgI, hXI⟩ := h
  have hXc : ContinuousOn X (Set.Icc 0 T) := Matrix.continuousOn_of_eq_add_integral hXI
  have hgc : ContinuousOn g (Set.Icc 0 T) := Matrix.continuousOn_of_eq_add_integral hgI
  have hsub : Set.Icc α β ⊆ Set.Icc 0 T := Set.Icc_subset_Icc hα hβ
  have hPc : ContinuousOn (fun t ↦ controlP (vertex m) (X t)) (Set.Icc α β) :=
    poly_controlP_continuousOn (hXc.mono hsub) (poly_vertex_mem m) fun t ht ↦ (hst t (hsub ht)).2
  have hwc : ContinuousOn (fun t ↦ controlP (vertex m) (X t) * X t -
      X t * controlP (vertex m) (X t)) (Set.Icc α β) :=
    (hPc.mul (hXc.mono hsub)).sub ((hXc.mono hsub).mul hPc)
  have hform := poly_integral_form_restrict hXI hα hαβ hβ hwc fun t ht ↦ by
    simp only [hu t ht]
  have hXd := fun t (ht : t ∈ Set.Icc α β) ↦
    Matrix.hasDerivWithinAtEntrywise_of_eq_add_integral hform ht (hwc t ht)
  have hconst := lemma7_1_1 _ X _ _ hXd
  have hP : ∀ t ∈ Set.Icc α β, controlP (vertex m) (X t) = controlP (vertex m) (X α) := by
    intro t ht
    unfold controlP
    rw [poly_traceForm_comm _ (X t), hconst t ht, poly_traceForm_comm (X _)]
  have hYd := fun t (_ : t ∈ Set.Icc α β) ↦ (hY t).hasDerivWithinAtEntrywise (s := Set.Icc α β)
  have hconstY := lemma7_1_1 _ Y _ _ hYd
  have hPY : ∀ t ∈ Set.Icc α β, controlP (vertex m) (Y t) = controlP (vertex m) (X α) := by
    intro t ht
    unfold controlP
    rw [poly_traceForm_comm _ (Y t), hconstY t ht, ← hX0, poly_traceForm_comm (X _)]
  have hXY : Set.EqOn X Y (Set.Icc α β) := by
    refine Matrix.ODE_solution_unique_of_bound_Icc
      (G := fun _ M ↦ controlP (vertex m) (X α) * M - M * controlP (vertex m) (X α))
      (K := 4 * ∑ k, ∑ l, |controlP (vertex m) (X α) k l|)
      (fun _ _ P Q k l ↦ ?_) (hXc.mono hsub) (fun t ht ↦ ?_) hYc.continuousOn (fun t ht ↦ ?_) hX0
    · rw [← Matrix.sub_apply, show ∀ P0 : Mat2, P0 * P - P * P0 - (P0 * Q - Q * P0) =
          P0 * (P - Q) - (P - Q) * P0 from fun P0 ↦ by noncomm_ring]
      simpa only [Matrix.sub_apply] using poly_abs_bracket_le _ (P - Q) k l
    · have := hXd t (Set.Ico_subset_Icc_self ht)
      rwa [hP t (Set.Ico_subset_Icc_self ht)] at this
    · have := hYd t (Set.Ico_subset_Icc_self ht)
      rwa [hPY t (Set.Ico_subset_Icc_self ht)] at this
  have hgd : ∀ t ∈ Set.Ico α β, HasDerivWithinAtEntrywise g (g t * Y t) (Set.Icc α β) t := by
    intro t ht
    have ht' := Set.Ico_subset_Icc_self ht
    rw [← hXY ht']
    exact (Matrix.hasDerivWithinAtEntrywise_of_eq_add_integral hgI (hsub ht')
      ((hgc.mul hXc) t (hsub ht'))).mono hsub
  have hgG : Set.EqOn g G (Set.Icc α β) :=
    Matrix.ODE_solution_unique_mul_right hYc.continuousOn (hgc.mono hsub) hgd hGc.continuousOn
      (fun t _ ↦ (hG t).hasDerivWithinAtEntrywise) hg0
  exact fun t ht ↦ ⟨hgG ht, hXY ht⟩

/-- `X` on the second switching interval: `R X(z₀, t - t_sw) R⁻¹`. -/
private noncomputable def sm_Y1 (y0 t : ℝ) : Mat2 := R * sm_mX y0 (t - minusSwitchTime y0) * R⁻¹

/-- `X` on the third switching interval: `R² X(z₀, t - 2t_sw) R⁻²`. -/
private noncomputable def sm_Y2 (y0 t : ℝ) : Mat2 := R * sm_Y1 y0 (t - minusSwitchTime y0) * R⁻¹

/-- `g` on the second switching interval: `g_sw R g₀(z₀, t - t_sw) R⁻¹`. -/
private noncomputable def sm_G1 (y0 t : ℝ) : Mat2 :=
  sm_mG y0 (minusSwitchTime y0) * R * sm_mG y0 (t - minusSwitchTime y0) * R⁻¹

/-- `g` on the third switching interval: `(g_sw R)² g₀(z₀, t - 2t_sw) R⁻²`. -/
private noncomputable def sm_G2 (y0 t : ℝ) : Mat2 :=
  sm_mG y0 (minusSwitchTime y0) * R * sm_G1 y0 (t - minusSwitchTime y0) * R⁻¹

private lemma sm_minusSwitchTime_pos {y0 : ℝ} (hy : 1 < y0) : 0 < minusSwitchTime y0 := by
  have hy0 : 0 < y0 := by linarith
  unfold minusSwitchTime
  refine div_pos (neg_pos.2 (Real.log_neg (by positivity) ?_)) (by positivity)
  rw [div_lt_one (by positivity)]
  nlinarith

private lemma sm_minus_control {τ t : ℝ} (hτ : 0 < τ) {i : ℕ} (h1 : i * τ ≤ t)
    (h2 : t < (i + 1) * τ) :
    minusPolygonControlAt τ t =
      vertex ⟨(1 + 2 * i) % 3, Nat.mod_lt _ (by norm_num)⟩ := by
  simp only [minusPolygonControlAt, vertex, poly_floor_eq hτ h1 h2]

/-- **Uniqueness of the `(6k - 2)`-spline** on three switching intervals: a state trajectory on
`[0, T]`, `2t_sw ≤ T ≤ 3t_sw`, with the control `e₂, e₁, e₃` of `eqn:3k+2` and the initial values
`g(0) = I₂`, `X(0) = Φ(i y₀)`, is the spline. -/
private theorem sm_minus_unique {y0 T : ℝ} (hy : 1 < y0) (hT2 : 2 * minusSwitchTime y0 ≤ T)
    (hT3 : T ≤ 3 * minusSwitchTime y0) {g X : ℝ → Mat2}
    (h : IsStateTrajectory T (minusPolygonControlAt (minusSwitchTime y0)) g X)
    (hg0 : g 0 = 1) (hX0 : X 0 = Φ 0 y0) :
    (∀ t ∈ Set.Icc 0 (minusSwitchTime y0), g t = sm_mG y0 t ∧ X t = sm_mX y0 t) ∧
    (∀ t ∈ Set.Icc (minusSwitchTime y0) (2 * minusSwitchTime y0),
      g t = sm_G1 y0 t ∧ X t = sm_Y1 y0 t) ∧
    (∀ t ∈ Set.Icc (2 * minusSwitchTime y0) T, g t = sm_G2 y0 t ∧ X t = sm_Y2 y0 t) := by
  set τ := minusSwitchTime y0 with hτdef
  have hτ : 0 < τ := sm_minusSwitchTime_pos hy
  have hy0 : 0 < y0 := by linarith
  have hsol := sm_m_solution y0
  -- the first interval
  have h0 := sm_seg_unique h (α := 0) (β := τ) le_rfl hτ.le (by linarith) (m := 1)
    (fun t ht ↦ sm_minus_control hτ (i := 0) (by push_cast; linarith [ht.1])
      (by push_cast; linarith [ht.2]))
    (sm_mX_continuous y0) (sm_mG_continuous y0) (fun t ↦ (hsol t).2.1) (fun t ↦ (hsol t).1)
    (by rw [hX0, (hsol 0).2.2.2]) (by rw [hg0, (hsol 0).2.2.1])
  -- the second interval
  have hY1 := fun t ↦ sm_shift_conj sm_R_conj_vertex_one (sm_mG y0 τ) τ (fun t ↦ (hsol t).2.1)
    (fun t ↦ (hsol t).1) t
  have hY1c : Continuous (sm_Y1 y0) :=
    (continuous_const.mul ((sm_mX_continuous y0).comp (continuous_sub_right _))).mul
      continuous_const
  have hG1c : Continuous (sm_G1 y0) :=
    (continuous_const.mul ((sm_mG_continuous y0).comp (continuous_sub_right _))).mul
      continuous_const
  have hτmem : τ ∈ Set.Icc 0 τ := ⟨hτ.le, le_rfl⟩
  have h1 := sm_seg_unique h (α := τ) (β := 2 * τ) hτ.le (by linarith) (by linarith) (m := 0)
    (fun t ht ↦ sm_minus_control hτ (i := 1) (by push_cast; linarith [ht.1])
      (by push_cast; linarith [ht.2]))
    hY1c hG1c (fun t ↦ (hY1 t).1) (fun t ↦ (hY1 t).2)
    (by rw [(h0 τ hτmem).2, sm_Y1, sub_self, (hsol 0).2.2.2, hτdef, sm_mX_switchTime hy0])
    (by rw [(h0 τ hτmem).1, sm_G1, sub_self, (hsol 0).2.2.1, Matrix.mul_one,
      Matrix.mul_assoc, poly_R_mul_inv, Matrix.mul_one])
  -- the third interval
  have hY2 := fun t ↦ sm_shift_conj (G := sm_G1 y0) (Y := sm_Y1 y0) sm_R_conj_vertex_zero
    (sm_mG y0 τ) τ (fun t ↦ (hY1 t).1) (fun t ↦ (hY1 t).2) t
  have hY2c : Continuous (sm_Y2 y0) :=
    (continuous_const.mul (hY1c.comp (continuous_sub_right _))).mul continuous_const
  have hG2c : Continuous (sm_G2 y0) :=
    (continuous_const.mul (hG1c.comp (continuous_sub_right _))).mul continuous_const
  have h2τmem : 2 * τ ∈ Set.Icc τ (2 * τ) := ⟨by linarith, le_rfl⟩
  have h2 := sm_seg_unique h (α := 2 * τ) (β := T) (by linarith) hT2 le_rfl (m := 2)
    (fun t ht ↦ sm_minus_control hτ (i := 2) (by push_cast; linarith [ht.1])
      (by push_cast; linarith [ht.2]))
    hY2c hG2c (fun t ↦ (hY2 t).1) (fun t ↦ (hY2 t).2)
    (by rw [(h1 _ h2τmem).2, sm_Y2, show 2 * τ - τ = τ by ring, sm_Y1, sm_Y1,
      show 2 * τ - τ = τ by ring, sub_self, (hsol 0).2.2.2, sm_mX_switchTime hy0])
    (by rw [(h1 _ h2τmem).1, sm_G2, show 2 * τ - τ = τ by ring, sm_G1, sm_G1,
      show 2 * τ - τ = τ by ring, sub_self, (hsol 0).2.2.1, Matrix.mul_one,
      Matrix.mul_assoc _ R R⁻¹,
      poly_R_mul_inv, Matrix.mul_one])
  exact ⟨h0, h1, h2⟩

/-! ### The cost of the `(6k - 2)`-spline -/

/-- `⟨J, R M R⁻¹⟩ = ⟨J, M⟩` (`J` commutes with `R`). -/
private lemma sm_traceForm_J_conj (M : Mat2) : traceForm J (R * M * R⁻¹) = traceForm J M := by
  have hJ : R * J * R⁻¹ = J := by
    rw [← poly_J_mul_R, Matrix.mul_assoc, poly_R_mul_inv, Matrix.mul_one]
  conv_lhs => rw [← hJ]
  exact poly_traceForm_conj poly_inv_mul_R J M

/-- Along the `e₂`-arc, `⟨J, X⟩ = -((1 + 3y₀²) W - 2 + 4/W)/(3y₀)`, `W = exp(-√3 y₀ t)`. -/
private lemma sm_traceForm_J_mX {y0 : ℝ} (hy : 0 < y0) (t : ℝ) :
    traceForm J (sm_mX y0 t) = -((1 + 3 * y0 ^ 2) * Real.exp (-(√3 * y0 * t)) - 2 +
      4 * Real.exp (√3 * y0 * t)) / (3 * y0) := by
  have hW := Real.exp_pos (-(√3 * y0 * t))
  have hWi : Real.exp (√3 * y0 * t) = (Real.exp (-(√3 * y0 * t)))⁻¹ := by
    rw [Real.exp_neg, inv_inv]
  rw [sm_mX_eq y0 t hy, poly_traceForm_J_Φ _ _ (by positivity), hWi]
  generalize Real.exp (-(√3 * y0 * t)) = W at hW ⊢
  have h3 : (0 : ℝ) < √3 := by positivity
  field_simp
  rw [poly_sqrt3_sq]
  ring

/-- An antiderivative of `t ↦ ⟨J, X(z₀, t)⟩` along the `e₂`-arc. -/
private noncomputable def sm_costPrim (y0 t : ℝ) : ℝ :=
  -(-(1 + 3 * y0 ^ 2) * Real.exp (-(√3 * y0 * t)) / (√3 * y0) - 2 * t +
    4 * Real.exp (√3 * y0 * t) / (√3 * y0)) / (3 * y0)

private lemma sm_costPrim_hasDerivAt {y0 : ℝ} (hy : 0 < y0) (t : ℝ) :
    HasDerivAt (sm_costPrim y0) (traceForm J (sm_mX y0 t)) t := by
  rw [sm_traceForm_J_mX hy]
  have h1 : HasDerivAt (fun t ↦ Real.exp (√3 * y0 * t))
      (Real.exp (√3 * y0 * t) * (√3 * y0 * 1)) t :=
    ((hasDerivAt_id' t).const_mul (√3 * y0)).exp
  have h2 : HasDerivAt (fun t ↦ Real.exp (-(√3 * y0 * t)))
      (Real.exp (-(√3 * y0 * t)) * -(√3 * y0 * 1)) t :=
    ((hasDerivAt_id' t).const_mul (√3 * y0)).neg.exp
  have := ((((h2.const_mul (-(1 + 3 * y0 ^ 2))).div_const (√3 * y0)).sub
    ((hasDerivAt_id' t).const_mul 2)).add ((h1.const_mul 4).div_const (√3 * y0))).neg.div_const
      (3 * y0)
  unfold sm_costPrim
  convert this using 1
  have h3 : (0 : ℝ) < √3 := by positivity
  field_simp

/-- `∫₀ˢ ⟨J, X(z₀, t)⟩ dt` along the `e₂`-arc. -/
private lemma sm_integral_J_mX {y0 : ℝ} (hy : 0 < y0) (s : ℝ) :
    ∫ t in (0 : ℝ)..s, traceForm J (sm_mX y0 t) = sm_costPrim y0 s - sm_costPrim y0 0 :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ sm_costPrim_hasDerivAt hy t)
    ((continuous_const.matrix_mul (sm_mX_continuous y0)).matrix_trace.intervalIntegrable _ _)

/-- `∫₀ˢ ⟨J, X(z₀, t)⟩ dt = -((1 + 3y₀²)(1 - e^{-cs}) - 2cs + 4(e^{cs} - 1))/(3√3 y₀²)`,
`c = √3 y₀`. -/
private lemma sm_costPrim_sub {y0 : ℝ} (hy : 0 < y0) (s : ℝ) :
    sm_costPrim y0 s - sm_costPrim y0 0 =
      -((1 + 3 * y0 ^ 2) * (1 - Real.exp (-(√3 * y0 * s))) - 2 * (√3 * y0 * s) +
        4 * (Real.exp (√3 * y0 * s) - 1)) / (3 * √3 * y0 ^ 2) := by
  have h3 : (0 : ℝ) < √3 := by positivity
  unfold sm_costPrim
  simp only [mul_zero, neg_zero, Real.exp_zero]
  field_simp
  ring

/-- **The cost of the `(6k - 2)`-spline on three switching intervals**: with `q = 4/(3y₀² + 1)`,
`ε = √3 y₀ (T - 2t_sw)`, `a = 1/y₀²` and `b = -ln q / y₀²`,
`-(3/2) ∫₀ᵀ ⟨J, X⟩ = (6 - 6a - 2b)/√3 + ((a + 3)(1 - e^{-ε}) - 2εa + 4a(e^ε - 1))/(2√3)`:
two full arcs of cost `(6 - 6a - 2b)/(2√3)` each (the cost per arc
`√3(y₀² - 1 + ln q/3)/y₀²`, the analogue of `√3(1 - y₀² - ℓ/3)/y₀²` for the `(6k + 2)`-gon), and a
partial arc. -/
private theorem sm_minus_cost {y0 T : ℝ} (hy : 1 < y0) (hT2 : 2 * minusSwitchTime y0 ≤ T)
    (hT3 : T ≤ 3 * minusSwitchTime y0) {g X : ℝ → Mat2}
    (h : IsStateTrajectory T (minusPolygonControlAt (minusSwitchTime y0)) g X)
    (hg0 : g 0 = 1) (hX0 : X 0 = Φ 0 y0) :
    reinhardtCost T X =
      (6 - 6 * (1 / y0 ^ 2) - 2 * (-Real.log (4 / (3 * y0 ^ 2 + 1)) / y0 ^ 2)) / √3 +
        ((1 / y0 ^ 2 + 3) * (1 - Real.exp (-(√3 * y0 * (T - 2 * minusSwitchTime y0)))) -
          2 * (√3 * y0 * (T - 2 * minusSwitchTime y0)) * (1 / y0 ^ 2) +
          4 * (1 / y0 ^ 2) * (Real.exp (√3 * y0 * (T - 2 * minusSwitchTime y0)) - 1)) /
          (2 * √3) := by
  set τ := minusSwitchTime y0 with hτdef
  have hτ : 0 < τ := sm_minusSwitchTime_pos hy
  have hy0 : 0 < y0 := by linarith
  have h3 : (0 : ℝ) < √3 := by positivity
  obtain ⟨h0, h1, h2⟩ := sm_minus_unique hy hT2 hT3 h hg0 hX0
  have hXc : ContinuousOn X (Set.Icc 0 T) := Matrix.continuousOn_of_eq_add_integral h.2.2.2.2.2
  have hfc : ContinuousOn (fun t ↦ traceForm J (X t)) (Set.Icc 0 T) :=
    (continuous_const.matrix_mul continuous_id).matrix_trace.comp_continuousOn hXc
  have hint : ∀ α β, 0 ≤ α → α ≤ β → β ≤ T →
      IntervalIntegrable (fun t ↦ traceForm J (X t)) MeasureTheory.volume α β :=
    fun α β hα hαβ hβ ↦ (hfc.mono (Set.Icc_subset_Icc hα hβ)).intervalIntegrable_of_Icc hαβ
  have hsplit : ∫ t in (0 : ℝ)..T, traceForm J (X t) =
      (∫ t in (0 : ℝ)..τ, traceForm J (X t)) + (∫ t in τ..2 * τ, traceForm J (X t)) +
        ∫ t in 2 * τ..T, traceForm J (X t) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hint 0 τ le_rfl hτ.le (by linarith))
        (hint τ (2 * τ) hτ.le (by linarith) hT2),
      intervalIntegral.integral_add_adjacent_intervals (hint 0 (2 * τ) le_rfl (by linarith) hT2)
        (hint (2 * τ) T (by linarith) hT2 le_rfl)]
  have e0 : ∫ t in (0 : ℝ)..τ, traceForm J (X t) = ∫ t in (0 : ℝ)..τ, traceForm J (sm_mX y0 t) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hτ.le] at ht
    simp only [(h0 t ht).2]
  have e1 : ∫ t in τ..2 * τ, traceForm J (X t) = ∫ t in (0 : ℝ)..τ, traceForm J (sm_mX y0 t) := by
    rw [intervalIntegral.integral_congr (g := fun t ↦ traceForm J (sm_mX y0 (t - τ))) ?_,
      intervalIntegral.integral_comp_sub_right (fun t ↦ traceForm J (sm_mX y0 t)), sub_self,
      show 2 * τ - τ = τ by ring]
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    simp only [(h1 t ht).2, sm_Y1, sm_traceForm_J_conj, ← hτdef]
  have e2 : ∫ t in 2 * τ..T, traceForm J (X t) =
      ∫ t in (0 : ℝ)..T - 2 * τ, traceForm J (sm_mX y0 t) := by
    rw [intervalIntegral.integral_congr (g := fun t ↦ traceForm J (sm_mX y0 (t - 2 * τ))) ?_,
      intervalIntegral.integral_comp_sub_right (fun t ↦ traceForm J (sm_mX y0 t)), sub_self]
    intro t ht
    rw [Set.uIcc_of_le hT2] at ht
    simp only [(h2 t ht).2, sm_Y2, sm_Y1, sm_traceForm_J_conj, sub_sub, ← two_mul, ← hτdef]
  have hq := sm_exp_switchTime hy0
  have hq' : Real.exp (√3 * y0 * τ) = (3 * y0 ^ 2 + 1) / 4 := by
    rw [show √3 * y0 * τ = -(-(√3 * y0 * τ)) by ring, Real.exp_neg, hq, inv_div]
  have hlog : √3 * y0 * τ = -Real.log (4 / (3 * y0 ^ 2 + 1)) := by
    rw [← hq, Real.log_exp]; ring
  rw [reinhardtCost, hsplit, e0, e1, e2, sm_integral_J_mX hy0, sm_integral_J_mX hy0,
    sm_costPrim_sub hy0, sm_costPrim_sub hy0, hq, hq', hlog]
  generalize √3 * y0 * (T - 2 * τ) = ε
  field_simp
  ring

/-! ### The parameters of the `(6k - 2)`-gon as `k → 1⁺` -/

private lemma sm_minusθ_bounds {k : ℝ} (hk : 1 < k) :
    Real.pi / 3 < minusθ k ∧ minusθ k < Real.pi / 2 := by
  unfold minusθ
  have hπ := Real.pi_pos
  have h3k : 0 < 3 * k - 1 := by linarith
  constructor
  · rw [lt_div_iff₀ h3k]; nlinarith
  · rw [div_lt_iff₀ h3k]; nlinarith

/-- `0 < cos θ < 1/2` and Jordan's inequality `cos θ = sin(π/2 - θ) ≥ (k - 1)/(3k - 1)`. -/
private lemma sm_cos_minusθ {k : ℝ} (hk : 1 < k) :
    0 < Real.cos (minusθ k) ∧ Real.cos (minusθ k) < 1 / 2 ∧
      (k - 1) / (3 * k - 1) ≤ Real.cos (minusθ k) := by
  obtain ⟨h1, h2⟩ := sm_minusθ_bounds hk
  have hπ := Real.pi_pos
  have h3k : 0 < 3 * k - 1 := by linarith
  refine ⟨Real.cos_pos_of_mem_Ioo ⟨by linarith, h2⟩, ?_, ?_⟩
  · rw [← Real.cos_pi_div_three]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) (by linarith) h1
  · rw [← Real.sin_pi_div_two_sub]
    have hx : Real.pi / 2 - minusθ k = Real.pi * (k - 1) / (2 * (3 * k - 1)) := by
      unfold minusθ
      have e : Real.pi * k / (3 * k - 1) * (2 * (3 * k - 1)) = 2 * Real.pi * k := by
        rw [div_mul_eq_mul_div, div_eq_iff h3k.ne']; ring
      rw [eq_div_iff (by positivity), sub_mul, e]
      ring
    have := Real.mul_le_sin (x := Real.pi / 2 - minusθ k) (by linarith) (by linarith)
    rw [hx] at this ⊢
    convert this using 1
    field_simp

private lemma sm_minusY₀_sq {k : ℝ} (hk : 1 < k) :
    minusY₀ k ^ 2 = (2 / Real.cos (minusθ k) - 1) / 3 := by
  obtain ⟨h0, h1, -⟩ := sm_cos_minusθ hk
  have : 4 < 2 / Real.cos (minusθ k) := by rw [lt_div_iff₀ h0]; linarith
  rw [minusY₀, Real.sq_sqrt (by linarith)]

private lemma sm_one_lt_minusY₀ {k : ℝ} (hk : 1 < k) : 1 < minusY₀ k := by
  obtain ⟨h0, h1, -⟩ := sm_cos_minusθ hk
  have : 4 < 2 / Real.cos (minusθ k) := by rw [lt_div_iff₀ h0]; linarith
  rw [minusY₀, Real.lt_sqrt (by norm_num)]
  linarith

/-- The closing condition `4/(3y₀² + 1) = 2 cos(πk/(3k - 1))`. -/
private lemma sm_four_div {k : ℝ} (hk : 1 < k) :
    4 / (3 * minusY₀ k ^ 2 + 1) = 2 * Real.cos (minusθ k) := by
  obtain ⟨h0, -, -⟩ := sm_cos_minusθ hk
  rw [sm_minusY₀_sq hk]
  field_simp
  ring

/-- `x(k) = cos(πk/(3k - 1)) → cos(π/2) = 0` as `k → 1⁺`. -/
private lemma sm_cosθ_tendsto : Tendsto (fun k ↦ Real.cos (minusθ k)) (𝓝[>] 1) (𝓝 0) := by
  have hθc : ContinuousAt minusθ 1 := by
    unfold minusθ
    exact (continuousAt_const.mul continuousAt_id).div
      ((continuousAt_const.mul continuousAt_id).sub continuousAt_const) (by norm_num)
  have hθ1 : minusθ 1 = Real.pi / 2 := by unfold minusθ; ring
  have := (Real.continuous_cos.continuousAt.comp hθc).tendsto
  simp only [Function.comp_apply, hθ1, Real.cos_pi_div_two] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- `1/y₀(k)² = 3x/(2 - x) → 0` as `k → 1⁺` (so `y₀(k) → ∞`). -/
private lemma sm_inv_sq_tendsto : Tendsto (fun k ↦ 1 / minusY₀ k ^ 2) (𝓝[>] 1) (𝓝 0) := by
  have hev : ∀ᶠ k in 𝓝[>] (1 : ℝ), k ∈ Set.Ioo 1 (4 / 3) := Ioo_mem_nhdsGT (by norm_num)
  have hx := sm_cosθ_tendsto
  have h := ((hx.const_mul 3).div ((tendsto_const_nhds (x := (2 : ℝ))).sub hx) (by norm_num))
  simp only [mul_zero, zero_div] at h
  refine h.congr' ?_
  filter_upwards [hev] with k hk
  obtain ⟨h0, h1, -⟩ := sm_cos_minusθ hk.1
  have h2 : 2 - Real.cos (minusθ k) ≠ 0 := by linarith
  simp only [Pi.div_apply]
  rw [sm_minusY₀_sq hk.1]
  field_simp

/-- `1/y₀(k) → 0` as `k → 1⁺`. -/
private lemma sm_inv_tendsto : Tendsto (fun k ↦ 1 / minusY₀ k) (𝓝[>] 1) (𝓝 0) := by
  have h := (Real.continuous_sqrt.tendsto 0).comp sm_inv_sq_tendsto
  rw [Real.sqrt_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with k hk
  have hy : 0 < minusY₀ k := by linarith [sm_one_lt_minusY₀ (Set.mem_Ioi.1 hk)]
  simp only [Function.comp_apply]
  rw [← _root_.one_div_pow, Real.sqrt_sq (by positivity)]

/-- The continuous function of `(1/y₀², -ln q/y₀², ε)` giving the cost (`sm_minus_cost`). -/
private noncomputable def sm_Ψ (p : ℝ × ℝ × ℝ) : ℝ :=
  (6 - 6 * p.1 - 2 * p.2.1) / √3 +
    ((p.1 + 3) * (1 - Real.exp (-p.2.2)) - 2 * p.2.2 * p.1 + 4 * p.1 * (Real.exp p.2.2 - 1)) /
      (2 * √3)

/-- **The cost limit** of Remark 7.6.4: `cost → √12` as `k → 1⁺`. -/
private theorem sm_cost_tendsto (g X : ℝ → ℝ → Mat2)
    (hgX : ∀ k : ℝ, 1 < k →
      IsStateTrajectory (minusTf k) (minusPolygonControlAt (minusSwitchTime (minusY₀ k)))
        (g k) (X k) ∧ g k 0 = 1 ∧ X k 0 = Φ 0 (minusY₀ k)) :
    Tendsto (fun k ↦ reinhardtCost (minusTf k) (X k)) (𝓝[>] 1) (𝓝 √12) := by
  have hπ := Real.pi_pos
  have hev : ∀ᶠ k in 𝓝[>] (1 : ℝ), k ∈ Set.Ioo 1 (4 / 3) := Ioo_mem_nhdsGT (by norm_num)
  set x : ℝ → ℝ := fun k ↦ Real.cos (minusθ k) with hxdef
  have hx : Tendsto x (𝓝[>] 1) (𝓝 0) := sm_cosθ_tendsto
  have ha : Tendsto (fun k ↦ 1 / minusY₀ k ^ 2) (𝓝[>] 1) (𝓝 0) := sm_inv_sq_tendsto
  -- `-ln q/y₀² = -(3/2)(2x ln 2x)/(2 - x) → 0`
  have hb : Tendsto (fun k ↦ -Real.log (4 / (3 * minusY₀ k ^ 2 + 1)) / minusY₀ k ^ 2)
      (𝓝[>] 1) (𝓝 0) := by
    have h2x : Tendsto (fun k ↦ 2 * x k) (𝓝[>] 1) (𝓝 0) := by simpa using hx.const_mul 2
    have hml := (Real.continuous_mul_log.tendsto 0).comp h2x
    simp only [zero_mul, Function.comp_def] at hml
    have h := ((hml.const_mul (-(3 / 2))).div ((tendsto_const_nhds (x := (2 : ℝ))).sub hx)
      (by norm_num))
    simp only [mul_zero, zero_div] at h
    refine h.congr' ?_
    filter_upwards [hev] with k hk
    obtain ⟨h0, h1, -⟩ := sm_cos_minusθ hk.1
    have h2 : 2 - Real.cos (minusθ k) ≠ 0 := by linarith
    simp only [Pi.div_apply, hxdef]
    rw [sm_four_div hk.1, sm_minusY₀_sq hk.1]
    field_simp
  -- `ε = √3 y₀ (t_f - 2t_sw) = -(3k - 3) ln(2x) → 0`, squeezed by Jordan's inequality
  have hε : Tendsto (fun k ↦ √3 * minusY₀ k * (minusTf k - 2 * minusSwitchTime (minusY₀ k)))
      (𝓝[>] 1) (𝓝 0) := by
    set U : ℝ → ℝ := fun k ↦ -(3 / 2) * ((2 * (k - 1)) * Real.log (2 * (k - 1))) +
      3 * (k - 1) * Real.log (3 * k - 1) with hU
    have hUc : ContinuousAt U 1 := by
      have : Continuous fun k : ℝ ↦ 2 * (k - 1) := by fun_prop
      refine ContinuousAt.add
        (continuousAt_const.mul (Real.continuous_mul_log.comp this).continuousAt)
        ((continuousAt_const.mul (continuousAt_id.sub continuousAt_const)).mul ?_)
      exact (Real.continuousAt_log (by norm_num)).comp
        ((continuousAt_const.mul continuousAt_id).sub continuousAt_const)
    have hU1 : U 1 = 0 := by simp [hU]
    have hUt : Tendsto U (𝓝[>] 1) (𝓝 0) := by
      have := hUc.tendsto; rw [hU1] at this; exact this.mono_left nhdsWithin_le_nhds
    have heq : ∀ k ∈ Set.Ioo (1 : ℝ) (4 / 3),
        √3 * minusY₀ k * (minusTf k - 2 * minusSwitchTime (minusY₀ k)) =
          -(3 * k - 3) * Real.log (2 * x k) := by
      intro k hk
      simp only [hxdef]
      have hy0 : 0 < minusY₀ k := by linarith [sm_one_lt_minusY₀ hk.1]
      have h3 : (0 : ℝ) < √3 := by positivity
      rw [minusTf, show (3 * k - 1) * minusSwitchTime (minusY₀ k) -
        2 * minusSwitchTime (minusY₀ k) = (3 * k - 3) * minusSwitchTime (minusY₀ k) by ring,
        minusSwitchTime, sm_four_div hk.1]
      field_simp
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUt ?_ ?_
    · filter_upwards [hev] with k hk
      rw [heq k hk]
      obtain ⟨h0, h1, -⟩ := sm_cos_minusθ hk.1
      have : Real.log (2 * x k) ≤ 0 :=
        Real.log_nonpos (by positivity) (by simp only [hxdef]; linarith)
      nlinarith [hk.1]
    · filter_upwards [hev] with k hk
      rw [heq k hk]
      obtain ⟨h0, h1, h2⟩ := sm_cos_minusθ hk.1
      have hk1 : 0 < k - 1 := by linarith [hk.1]
      have h3k : 0 < 3 * k - 1 := by linarith [hk.1]
      have hlog : Real.log (2 * ((k - 1) / (3 * k - 1))) ≤ Real.log (2 * x k) :=
        Real.log_le_log (by positivity) (by simp only [hxdef]; linarith)
      rw [show 2 * ((k - 1) / (3 * k - 1)) = 2 * (k - 1) / (3 * k - 1) by ring,
        Real.log_div (by positivity) (by positivity)] at hlog
      simp only [hU]
      nlinarith
  -- the cost is `Ψ(1/y₀², -ln q/y₀², ε)`
  have hΨc : Continuous sm_Ψ := by unfold sm_Ψ; fun_prop
  have hΨ0 : sm_Ψ (0, 0, 0) = √12 := by
    have h3 : (0 : ℝ) < √3 := by positivity
    simp [sm_Ψ, poly_sqrt12]
    field_simp
    rw [poly_sqrt3_sq]
    norm_num
  have hlim := (hΨc.tendsto (0, 0, 0)).comp (ha.prodMk_nhds (hb.prodMk_nhds hε))
  rw [hΨ0] at hlim
  refine hlim.congr' ?_
  filter_upwards [hev] with k hk
  obtain ⟨hk1, hk2⟩ := hk
  have hy := sm_one_lt_minusY₀ hk1
  have hτ := sm_minusSwitchTime_pos hy
  obtain ⟨htraj, hg0, hX0⟩ := hgX k hk1
  rw [Function.comp_apply, sm_minus_cost hy (by rw [minusTf]; nlinarith)
    (by rw [minusTf]; nlinarith) htraj hg0 hX0]
  rfl

/-! ### Hausdorff convergence of the six arcs to the boundary of `[-1, 1] × [-√3/2, √3/2]`

The six arcs are compared with the rectangle boundary `F` in the sup metric of `Fin 2 → ℝ`. With
`r = 1/y₀ → 0`: every arc point lies in the shell `sm_Ann δ` (`1 - δ ≤ N(p) ≤ 1 + δ` for the gauge
`N` of the rectangle) with `δ = O(r)`, hence within `δ` of `F`; conversely every point of `F` is
within `O(r)` of an explicit arc point. On the first switching interval the arcs are
`σ_j = g₀ s_j*` with `g₀` explicit (`sm_mG_eq`); on the second they are `M₁ σ_{j-1}` with
`M₁ = g_sw R → [[0, -2/√3], [√3/2, 0]]`, a map of `F` onto itself; on the (short) third they are
`M₁² σ_{j-2}`. -/

/-- The boundary of the rectangle `[-1, 1] × [-√3/2, √3/2]`. -/
private def sm_Fr : Set (Fin 2 → ℝ) :=
  {x | (|x 0| = 1 ∧ |x 1| ≤ √3 / 2) ∨ (|x 0| ≤ 1 ∧ |x 1| = √3 / 2)}

private lemma sm_frontier_rect :
    frontier ((fun x ↦ (1 : Mat2) *ᵥ x + 0) '' {x : Fin 2 → ℝ | |x 0| ≤ 1 ∧ |x 1| ≤ √3 / 2}) =
      sm_Fr := by
  have hS : {x : Fin 2 → ℝ | |x 0| ≤ 1 ∧ |x 1| ≤ √3 / 2} =
      Set.univ.pi fun i ↦ Set.Icc (-(![1, √3 / 2] i)) (![1, √3 / 2] i) := by
    ext x
    rw [Set.mem_univ_pi, Fin.forall_fin_two]
    simp [abs_le]
  simp only [Matrix.one_mulVec, add_zero, Set.image_id']
  rw [hS, frontier, (isClosed_set_pi fun i _ ↦ isClosed_Icc).closure_eq,
    interior_pi_set Set.finite_univ]
  ext x
  simp only [interior_Icc, Set.mem_sdiff, Set.mem_univ_pi, Set.mem_Icc, Set.mem_Ioo,
    Fin.forall_fin_two, ← abs_le, ← abs_lt, sm_Fr, Set.mem_ofPred_eq, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  constructor
  · rintro ⟨⟨hA, hB⟩, hn⟩
    rcases hA.lt_or_eq with hA' | hA'
    · exact Or.inr ⟨hA, hB.lt_or_eq.resolve_left fun h ↦ hn ⟨hA', h⟩⟩
    · exact Or.inl ⟨hA', hB⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨⟨h1.le, h2⟩, fun h ↦ h.1.ne h1⟩
    · exact ⟨⟨h1, h2.le⟩, fun h ↦ h.2.ne h2⟩

/-- The shell `1 - δ ≤ N(p) ≤ 1 + δ` around the rectangle boundary. -/
private def sm_Ann (δ : ℝ) (p : Fin 2 → ℝ) : Prop :=
  |p 0| ≤ 1 + δ ∧ |p 1| ≤ √3 / 2 + δ ∧ (1 - δ ≤ |p 0| ∨ √3 / 2 - δ ≤ |p 1|)

private lemma sm_dist_le {x y : Fin 2 → ℝ} {ε : ℝ} (h0 : |x 0 - y 0| ≤ ε) (h1 : |x 1 - y 1| ≤ ε) :
    dist x y ≤ ε := by
  refine (dist_pi_le_iff ((abs_nonneg _).trans h0)).2 fun i ↦ ?_
  fin_cases i
  · rw [Real.dist_eq]; exact h0
  · rw [Real.dist_eq]; exact h1

/-- Clamping `x` to `[-b, b]` moves it by at most `δ` if `|x| ≤ b + δ`. -/
private lemma sm_clamp {b δ x : ℝ} (hb : 0 ≤ b) (hδ : 0 ≤ δ) (hx : |x| ≤ b + δ) :
    |max (-b) (min b x)| ≤ b ∧ |x - max (-b) (min b x)| ≤ δ := by
  rw [abs_le] at hx
  constructor
  · rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  · rw [abs_le]
    rcases le_total x b with h | h
    · rw [min_eq_right h]
      rcases le_total (-b) x with h' | h'
      · rw [max_eq_right h']; constructor <;> linarith
      · rw [max_eq_left h']; constructor <;> linarith
    · rw [min_eq_left h, max_eq_right (by linarith)]
      constructor <;> linarith

/-- A point of the shell is `δ`-close to the rectangle boundary. -/
private lemma sm_Ann_near {δ : ℝ} {p : Fin 2 → ℝ} (hδ : 0 ≤ δ) (h : sm_Ann δ p) :
    ∃ f ∈ sm_Fr, dist p f ≤ δ := by
  have h3 : (1 : ℝ) < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  obtain ⟨h0, h1, h2 | h2⟩ := h
  · obtain ⟨c1, c2⟩ := sm_clamp (b := √3 / 2) (by positivity) hδ h1
    refine ⟨![if 0 ≤ p 0 then 1 else -1, max (-(√3 / 2)) (min (√3 / 2) (p 1))],
      Or.inl ⟨?_, c1⟩, sm_dist_le ?_ c2⟩
    · simp only [Matrix.cons_val_zero]
      split_ifs <;> simp
    · simp only [Matrix.cons_val_zero]
      split_ifs with hp
      · rw [abs_of_nonneg hp] at h0 h2
        rw [abs_le]; constructor <;> linarith
      · rw [abs_of_neg (not_le.1 hp)] at h0 h2
        rw [abs_le]; constructor <;> linarith
  · obtain ⟨c1, c2⟩ := sm_clamp (b := 1) zero_le_one hδ h0
    refine ⟨![max (-1) (min 1 (p 0)), if 0 ≤ p 1 then √3 / 2 else -(√3 / 2)],
      Or.inr ⟨c1, ?_⟩, sm_dist_le c2 ?_⟩
    · simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]
      split_ifs <;> simp [abs_of_pos (show (0 : ℝ) < √3 / 2 by positivity)]
    · simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]
      split_ifs with hp
      · rw [abs_of_nonneg hp] at h1 h2
        rw [abs_le]; constructor <;> linarith
      · rw [abs_of_neg (not_le.1 hp)] at h1 h2
        rw [abs_le]; constructor <;> linarith

private lemma sm_Ann_neg {δ : ℝ} {p : Fin 2 → ℝ} (h : sm_Ann δ p) : sm_Ann δ (-p) := by
  simpa [sm_Ann, abs_neg] using h

private lemma sm_Ann_mono {δ δ' : ℝ} (hδ : δ ≤ δ') {p : Fin 2 → ℝ} (h : sm_Ann δ p) :
    sm_Ann δ' p := by
  obtain ⟨h0, h1, h2 | h2⟩ := h
  · exact ⟨by linarith, by linarith, Or.inl (by linarith)⟩
  · exact ⟨by linarith, by linarith, Or.inr (by linarith)⟩

/-- A perturbation by `ε` in each coordinate enlarges the shell by `ε`. -/
private lemma sm_Ann_pert {δ ε : ℝ} {p p' : Fin 2 → ℝ} (h : sm_Ann δ p) (h0 : |p' 0 - p 0| ≤ ε)
    (h1 : |p' 1 - p 1| ≤ ε) : sm_Ann (δ + ε) p' := by
  have e0 := abs_sub_abs_le_abs_sub (p' 0) (p 0)
  have e0' := abs_sub_abs_le_abs_sub (p 0) (p' 0)
  have e1 := abs_sub_abs_le_abs_sub (p' 1) (p 1)
  have e1' := abs_sub_abs_le_abs_sub (p 1) (p' 1)
  rw [abs_sub_comm] at e0' e1'
  obtain ⟨g0, g1, g2 | g2⟩ := h
  · exact ⟨by linarith, by linarith, Or.inl (by linarith)⟩
  · exact ⟨by linarith, by linarith, Or.inr (by linarith)⟩

/-- The limit `M = [[0, -2/√3], [√3/2, 0]]` of `M₁ = g_sw R` maps the shell `δ` into the shell
`2δ` (and the rectangle boundary onto itself). -/
private lemma sm_Ann_Mlim {δ : ℝ} (hδ : 0 ≤ δ) {p : Fin 2 → ℝ} (h : sm_Ann δ p) :
    sm_Ann (2 * δ) ![-(2 / √3 * p 1), √3 / 2 * p 0] := by
  have h3 : (1 : ℝ) < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h3' : (0 : ℝ) < √3 := by positivity
  have hc : 2 / √3 * (√3 / 2) = 1 := by field_simp
  have hc2 : 2 / √3 ≤ 2 := by rw [div_le_iff₀ h3']; linarith
  have hc0 : 0 < 2 / √3 := by positivity
  simp only [sm_Ann, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, abs_neg,
    abs_mul, abs_of_pos hc0, abs_of_pos (show (0 : ℝ) < √3 / 2 by positivity)]
  have hc1 : √3 / 2 ≤ 2 := by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have hcδ : √3 / 2 * δ ≤ 2 * δ := mul_le_mul_of_nonneg_right hc1 hδ
  have hdδ : 2 / √3 * δ ≤ 2 * δ := mul_le_mul_of_nonneg_right hc2 hδ
  have hcp : 0 ≤ √3 / 2 := by positivity
  obtain ⟨g0, g1, g2 | g2⟩ := h
  · have a0 := mul_le_mul_of_nonneg_left g0 hcp
    have a1 := mul_le_mul_of_nonneg_left g1 hc0.le
    have a2 := mul_le_mul_of_nonneg_left g2 hcp
    refine ⟨by nlinarith, by nlinarith, Or.inr (by nlinarith)⟩
  · have a0 := mul_le_mul_of_nonneg_left g0 hcp
    have a1 := mul_le_mul_of_nonneg_left g1 hc0.le
    have a2 := mul_le_mul_of_nonneg_left g2 hc0.le
    refine ⟨by nlinarith, by nlinarith, Or.inl (by nlinarith)⟩

private lemma sm_Fr_Mlim {f : Fin 2 → ℝ} (hf : f ∈ sm_Fr) :
    ![-(2 / √3 * f 1), √3 / 2 * f 0] ∈ sm_Fr := by
  have h3' : (0 : ℝ) < √3 := by positivity
  have hc : 2 / √3 * (√3 / 2) = 1 := by field_simp
  have hc0 : 0 < 2 / √3 := by positivity
  simp only [sm_Fr, Set.mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, abs_neg, abs_mul, abs_of_pos hc0,
    abs_of_pos (show (0 : ℝ) < √3 / 2 by positivity)] at hf ⊢
  rcases hf with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · right; rw [h0]; exact ⟨by nlinarith, by ring⟩
  · left; rw [h1]; exact ⟨hc, by nlinarith⟩

private lemma sm_Fr_neg {f : Fin 2 → ℝ} (hf : f ∈ sm_Fr) : -f ∈ sm_Fr := by
  simpa [sm_Fr, abs_neg] using hf

/-- `g₀(z₀, t)` as a function of `W = exp(-√3 y₀ t)` (`sm_mG_eq`). -/
private noncomputable def sm_GW (y0 W : ℝ) : Mat2 :=
  !![1, (W - 1) / √3; (W⁻¹ - 1) / (√3 * y0 ^ 2), 1 - (W - 2 + W⁻¹) / (3 * y0 ^ 2)]

private lemma sm_mG_eq_GW {y0 : ℝ} (hy0 : 0 < y0) (t : ℝ) :
    sm_mG y0 t = sm_GW y0 (Real.exp (-(√3 * y0 * t))) := by
  rw [sm_mG_eq y0 t hy0, sm_GW]

/-- A property of the six points `s_j*` that is stable under `v ↦ -v` holds for all of them once
it holds for `s₀*, s₁*, s₂*` (`s_{j+3}* = -s_j*`). -/
private lemma sm_sixthRoot_ind {P : (Fin 2 → ℝ) → Prop} (hneg : ∀ v, P v → P (-v))
    (h0 : P (sixthRoot 0)) (h1 : P (sixthRoot 1)) (h2 : P (sixthRoot 2)) (j : ZMod 6) :
    P (sixthRoot j) := by
  have h3 := fun m ↦ (algA_isMultiPoint_sixthRoot m).2.1
  fin_cases j
  · exact h0
  · exact h1
  · exact h2
  · change P (sixthRoot 3)
    rw [show (3 : ZMod 6) = 0 + 3 from rfl, h3]; exact hneg _ h0
  · change P (sixthRoot 4)
    rw [show (4 : ZMod 6) = 1 + 3 from rfl, h3]; exact hneg _ h1
  · change P (sixthRoot 5)
    rw [show (5 : ZMod 6) = 2 + 3 from rfl, h3]; exact hneg _ h2

private lemma sm_Rinv_sixthRoot (j : ZMod 6) : R⁻¹ *ᵥ sixthRoot (j + 1) = sixthRoot j := by
  rw [← oct_R_mulVec_sixthRoot, Matrix.mulVec_mulVec, poly_inv_mul_R, Matrix.one_mulVec]

private lemma sm_GW_s0 (y0 W : ℝ) :
    sm_GW y0 W *ᵥ sixthRoot 0 = ![1, (W⁻¹ - 1) / (√3 * y0 ^ 2)] := by
  rw [algA_sixthRoot_zero]
  ext i
  fin_cases i <;> simp [sm_GW, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private lemma sm_GW_s1 {y0 W : ℝ} (hy : y0 ≠ 0) (hW : W ≠ 0) :
    sm_GW y0 W *ᵥ sixthRoot 1 = ![W / 2, √3 / 2 + √3 * (1 - W) / (6 * y0 ^ 2)] := by
  have h3 : (0 : ℝ) < √3 := by positivity
  rw [algA_sixthRoot_one]
  ext i
  fin_cases i <;> simp [sm_GW, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> field_simp <;>
    ring_nf
  simp only [poly_sqrt3_sq]
  ring

private lemma sm_GW_s2 {y0 W : ℝ} (hy : y0 ≠ 0) (hW : W ≠ 0) :
    sm_GW y0 W *ᵥ sixthRoot 2 = ![-1 + W / 2,
      √3 / 2 + √3 * (1 - W) / (6 * y0 ^ 2) - (W⁻¹ - 1) / (√3 * y0 ^ 2)] := by
  have h3 : (0 : ℝ) < √3 := by positivity
  rw [algA_sixthRoot_two]
  ext i
  fin_cases i <;> simp [sm_GW, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> field_simp <;>
    ring_nf
  simp only [poly_sqrt3_sq]
  ring

/-- Bounds on the coordinates `β = (W⁻¹ - 1)/(√3y₀²)` and `γ = √3(1 - W)/(6y₀²)` of the arcs. -/
private lemma sm_beta_gamma {y0 W : ℝ} (hy : 2 ≤ y0) (hW1 : W ≤ 1)
    (hWq : 4 / (3 * y0 ^ 2 + 1) ≤ W) :
    0 < W ∧ 0 ≤ (W⁻¹ - 1) / (√3 * y0 ^ 2) ∧ (W⁻¹ - 1) / (√3 * y0 ^ 2) ≤ √3 / 4 ∧
      0 ≤ √3 * (1 - W) / (6 * y0 ^ 2) ∧ √3 * (1 - W) / (6 * y0 ^ 2) ≤ 1 / y0 ∧
      (4 / y0 < W → (W⁻¹ - 1) / (√3 * y0 ^ 2) ≤ 1 / y0) := by
  have h3 : (0 : ℝ) < √3 := by positivity
  have h33 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h32 : √3 < 2 := by nlinarith
  have hy0 : 0 < y0 := by linarith
  have hq : 0 < 4 / (3 * y0 ^ 2 + 1) := by positivity
  have hW0 : 0 < W := lt_of_lt_of_le hq hWq
  have hV1 : 1 ≤ W⁻¹ := one_le_inv₀ hW0 |>.2 hW1
  have hVq : W⁻¹ ≤ (3 * y0 ^ 2 + 1) / 4 := by
    rw [← inv_div]; exact inv_anti₀ hq hWq
  refine ⟨hW0, div_nonneg (by linarith) (by positivity), ?_, div_nonneg (by nlinarith)
    (by positivity), ?_, fun hW ↦ ?_⟩
  · rw [div_le_iff₀ (by positivity)]
    nlinarith
  · rw [div_le_div_iff₀ (by positivity) hy0]
    have e : √3 * (1 - W) ≤ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right e hy0.le]
  · have hV : W⁻¹ < y0 / 4 := by
      rw [inv_lt_comm₀ hW0 (by positivity), inv_div]; exact hW
    rw [div_le_div_iff₀ (by positivity) hy0]
    have e := mul_le_mul_of_nonneg_right (show W⁻¹ - 1 ≤ y0 / 4 by linarith) hy0.le
    nlinarith

/-- On the first switching interval every arc point lies in the shell `2/y₀`. -/
private lemma sm_GW_Ann {y0 W : ℝ} (hy : 2 ≤ y0) (hW1 : W ≤ 1) (hWq : 4 / (3 * y0 ^ 2 + 1) ≤ W)
    (j : ZMod 6) : sm_Ann (2 / y0) (sm_GW y0 W *ᵥ sixthRoot j) := by
  obtain ⟨hW0, hb0, hb1, hg0, hg1, hb2⟩ := sm_beta_gamma hy hW1 hWq
  have hy0 : 0 < y0 := by linarith
  have hδ : 0 < 2 / y0 := by positivity
  have hr : 1 / y0 ≤ 2 / y0 := by gcongr; norm_num
  have h34 : √3 / 4 ≤ √3 / 2 := by have : (0 : ℝ) ≤ √3 := Real.sqrt_nonneg 3; linarith
  refine sm_sixthRoot_ind (P := fun v ↦ sm_Ann (2 / y0) (sm_GW y0 W *ᵥ v))
    (fun v hv ↦ by simpa [Matrix.mulVec_neg] using sm_Ann_neg hv) ?_ ?_ ?_ j
  · simp only [sm_GW_s0, sm_Ann, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, abs_one, abs_of_nonneg hb0]
    exact ⟨by linarith, by linarith, Or.inl (by linarith)⟩
  · simp only [sm_GW_s1 hy0.ne' hW0.ne', sm_Ann, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, abs_of_pos (half_pos hW0),
      abs_of_nonneg (show 0 ≤ √3 / 2 + √3 * (1 - W) / (6 * y0 ^ 2) by positivity)]
    exact ⟨by linarith, by linarith, Or.inr (by linarith)⟩
  · simp only [sm_GW_s2 hy0.ne' hW0.ne', sm_Ann, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
    refine ⟨by linarith, by linarith, ?_⟩
    rcases le_or_gt W (4 / y0) with h | h
    · left
      have e : 4 / y0 = 2 * (2 / y0) := by ring
      linarith
    · right; linarith [hb2 h]

/-- `M₁ = g_sw R` in closed form (`q = 4/(3y₀² + 1)`, `a = 1/y₀²`):
`M₁ p = (q/2 p₀ + (q - 4)/(2√3) p₁, (√3/2 + √3 a (1 - q)/6) p₀ + a (4 - q)/6 p₁)`. -/
private lemma sm_M1_mulVec {y0 : ℝ} (hy : 0 < y0) (p : Fin 2 → ℝ) :
    (sm_mG y0 (minusSwitchTime y0) * R) *ᵥ p =
      ![4 / (3 * y0 ^ 2 + 1) / 2 * p 0 + (4 / (3 * y0 ^ 2 + 1) - 4) / (2 * √3) * p 1,
        (√3 / 2 + √3 * (1 / y0 ^ 2) * (1 - 4 / (3 * y0 ^ 2 + 1)) / 6) * p 0 +
          1 / y0 ^ 2 * (4 - 4 / (3 * y0 ^ 2 + 1)) / 6 * p 1] := by
  have h3 : (0 : ℝ) < √3 := by positivity
  rw [sm_mG_eq _ _ hy, sm_exp_switchTime hy]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, R, Matrix.mul_apply] <;>
    field_simp <;> ring_nf <;> simp only [poly_sqrt3_sq] <;> ring

/-- The perturbation `M₁ - M` is `O(1/y₀)` on points of size `≤ 3/2`. -/
private lemma sm_pert_bound {q a r p0 p1 : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ r) (hq1 : q ≤ 1) (ha0 : 0 ≤ a)
    (ha : a ≤ r) (hp0 : |p0| ≤ 3 / 2) (hp1 : |p1| ≤ 3 / 2) :
    |q / 2 * p0 + q / (2 * √3) * p1| ≤ 2 * r ∧
      |√3 * a * (1 - q) / 6 * p0 + a * (4 - q) / 6 * p1| ≤ 2 * r := by
  have h33 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have h3 : (1 : ℝ) ≤ √3 := by nlinarith [Real.sqrt_nonneg 3]
  have h32 : √3 ≤ 2 := by nlinarith [Real.sqrt_nonneg 3]
  have hc : q / (2 * √3) ≤ q / 2 := div_le_div_of_nonneg_left hq0 (by norm_num) (by linarith)
  have hc0 : 0 ≤ q / (2 * √3) := by positivity
  have hd : √3 * a * (1 - q) / 6 ≤ a / 3 := by
    rw [div_le_iff₀ (by norm_num)]; nlinarith [mul_nonneg ha0 hq0]
  have hd0 : 0 ≤ √3 * a * (1 - q) / 6 := by
    have : 0 ≤ 1 - q := by linarith
    positivity
  have he : a * (4 - q) / 6 ≤ 2 * a / 3 := by
    rw [div_le_iff₀ (by norm_num)]; nlinarith
  have he0 : 0 ≤ a * (4 - q) / 6 := by
    have : 0 ≤ 4 - q := by linarith
    positivity
  constructor
  · refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ q / 2), abs_of_nonneg hc0]
    have := mul_le_mul hc hp1 (abs_nonneg _) (by positivity)
    have := mul_le_mul_of_nonneg_left hp0 (by positivity : 0 ≤ q / 2)
    nlinarith
  · refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hd0, abs_of_nonneg he0]
    have := mul_le_mul hd hp0 (abs_nonneg _) (by positivity)
    have := mul_le_mul he hp1 (abs_nonneg _) (by positivity)
    nlinarith

/-- `M₁` maps the shell `δ` into the shell `2δ + 2/y₀`. -/
private lemma sm_M1_Ann {y0 δ : ℝ} (hy : 2 ≤ y0) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) {p : Fin 2 → ℝ}
    (h : sm_Ann δ p) :
    sm_Ann (2 * δ + 2 / y0) ((sm_mG y0 (minusSwitchTime y0) * R) *ᵥ p) := by
  have hy0 : 0 < y0 := by linarith
  have h3 : (0 : ℝ) < √3 := by positivity
  have h33 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hq0 : 0 ≤ 4 / (3 * y0 ^ 2 + 1) := by positivity
  have hq : 4 / (3 * y0 ^ 2 + 1) ≤ 1 / y0 := by
    rw [div_le_div_iff₀ (by positivity) hy0]; nlinarith
  have hq1 : 4 / (3 * y0 ^ 2 + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  have ha : 1 / y0 ^ 2 ≤ 1 / y0 := by
    rw [div_le_div_iff₀ (by positivity) hy0]; nlinarith
  have hp0 : |p 0| ≤ 3 / 2 := by linarith [h.1]
  have hp1 : |p 1| ≤ 3 / 2 := by
    have : √3 / 2 ≤ 1 := by nlinarith
    linarith [h.2.1]
  obtain ⟨b0, b1⟩ := sm_pert_bound hq0 hq hq1 (by positivity) ha hp0 hp1
  rw [sm_M1_mulVec hy0]
  refine sm_Ann_pert (sm_Ann_Mlim hδ h) ?_ ?_
  · simp only [Matrix.cons_val_zero]
    have e : 4 / (3 * y0 ^ 2 + 1) / 2 * p 0 + (4 / (3 * y0 ^ 2 + 1) - 4) / (2 * √3) * p 1 -
        -(2 / √3 * p 1) =
        4 / (3 * y0 ^ 2 + 1) / 2 * p 0 + 4 / (3 * y0 ^ 2 + 1) / (2 * √3) * p 1 := by ring
    rw [e]; exact b0.trans_eq (by ring)
  · simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]
    have e : (√3 / 2 + √3 * (1 / y0 ^ 2) * (1 - 4 / (3 * y0 ^ 2 + 1)) / 6) * p 0 +
        1 / y0 ^ 2 * (4 - 4 / (3 * y0 ^ 2 + 1)) / 6 * p 1 - √3 / 2 * p 0 =
        √3 * (1 / y0 ^ 2) * (1 - 4 / (3 * y0 ^ 2 + 1)) / 6 * p 0 +
          1 / y0 ^ 2 * (4 - 4 / (3 * y0 ^ 2 + 1)) / 6 * p 1 := by ring
    rw [e]; exact b1.trans_eq (by ring)

private lemma sm_q_le {y0 : ℝ} (hy : 2 ≤ y0) :
    0 < 4 / (3 * y0 ^ 2 + 1) ∧ 4 / (3 * y0 ^ 2 + 1) ≤ 1 / y0 ∧ 1 / y0 ≤ 1 / 2 := by
  have hy0 : 0 < y0 := by linarith
  refine ⟨by positivity, ?_, ?_⟩
  · rw [div_le_div_iff₀ (by positivity) hy0]; nlinarith
  · rw [div_le_div_iff₀ hy0 (by norm_num)]; linarith

/-- `β(W) ≤ 1/y₀` once `W ≥ 1/y₀`. -/
private lemma sm_beta_le {y0 W : ℝ} (hy : 2 ≤ y0) (hW : 1 / y0 ≤ W) :
    (W⁻¹ - 1) / (√3 * y0 ^ 2) ≤ 1 / y0 := by
  have hy0 : 0 < y0 := by linarith
  have h33 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have h3 : (1 : ℝ) ≤ √3 := by nlinarith [Real.sqrt_nonneg 3]
  have hWi : W⁻¹ ≤ y0 := by
    have := inv_anti₀ (by positivity) hW
    rwa [one_div, inv_inv] at this
  rw [div_le_div_iff₀ (by positivity) hy0]
  have := mul_le_mul_of_nonneg_right hWi hy0.le
  nlinarith [mul_le_mul_of_nonneg_right h3 (sq_nonneg y0)]

/-- `β(q) ≥ √3/4 - 1/y₀` at the switching time. -/
private lemma sm_beta_q {y0 : ℝ} (hy : 2 ≤ y0) :
    √3 / 4 - 1 / y0 ≤ ((4 / (3 * y0 ^ 2 + 1))⁻¹ - 1) / (√3 * y0 ^ 2) := by
  have hy0 : 0 < y0 := by linarith
  have h33 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have h3 : (1 : ℝ) ≤ √3 := by nlinarith [Real.sqrt_nonneg 3]
  rw [inv_div, le_div_iff₀ (by positivity)]
  have e : (√3 / 4 - 1 / y0) * (√3 * y0 ^ 2) = √3 ^ 2 * y0 ^ 2 / 4 - √3 * y0 := by
    field_simp
  rw [e, h33]
  nlinarith

/-- The arc point `g₀ s_j*` at parameter `W`, or its image under `M₁ = g_sw R`, is within `8/y₀`
of `f`. -/
private def sm_good (y0 : ℝ) (f : Fin 2 → ℝ) : Prop :=
  ∃ W, 4 / (3 * y0 ^ 2 + 1) ≤ W ∧ W ≤ 1 ∧ ∃ j : ZMod 6,
    dist (sm_GW y0 W *ᵥ sixthRoot j) f ≤ 8 / y0 ∨
      dist ((sm_mG y0 (minusSwitchTime y0) * R) *ᵥ (sm_GW y0 W *ᵥ sixthRoot j)) f ≤ 8 / y0

private lemma sm_good_neg {y0 : ℝ} {f : Fin 2 → ℝ} (h : sm_good y0 f) : sm_good y0 (-f) := by
  obtain ⟨W, h1, h2, j, hd⟩ := h
  refine ⟨W, h1, h2, j + 3, ?_⟩
  rwa [(algA_isMultiPoint_sixthRoot j).2.1, Matrix.mulVec_neg, Matrix.mulVec_neg, dist_neg_neg,
    dist_neg_neg]

/-- A point `f'` that is `3/y₀`-close to an arc point of the first switching interval is good, and
so is its image `M f'` under the limit `M = [[0, -2/√3], [√3/2, 0]]` of `M₁`. -/
private lemma sm_good_base {y0 W : ℝ} (hy : 4 ≤ y0) (hW1 : W ≤ 1) (hWq : 4 / (3 * y0 ^ 2 + 1) ≤ W)
    {j : ZMod 6} {f' : Fin 2 → ℝ} (hd : dist (sm_GW y0 W *ᵥ sixthRoot j) f' ≤ 3 / y0) :
    sm_good y0 f' ∧ sm_good y0 ![-(2 / √3 * f' 1), √3 / 2 * f' 0] := by
  have hy0 : 0 < y0 := by linarith
  have h38 : 3 / y0 ≤ 8 / y0 := by gcongr; norm_num
  refine ⟨⟨W, hWq, hW1, j, Or.inl (hd.trans h38)⟩, W, hWq, hW1, j, Or.inr ?_⟩
  set p := sm_GW y0 W *ᵥ sixthRoot j with hp
  have hA := sm_GW_Ann (by linarith) hW1 hWq j
  rw [← hp] at hA
  have h2 : 2 / y0 ≤ 1 / 2 := by rw [div_le_div_iff₀ hy0 (by norm_num)]; linarith
  -- the coordinates of `M₁ p - M p` (as in `sm_M1_Ann`) and of `M p - M f'`
  have hd0 : |p 0 - f' 0| ≤ 3 / y0 := by
    rw [← Real.dist_eq]; exact (dist_le_pi_dist p f' 0).trans hd
  have hd1 : |p 1 - f' 1| ≤ 3 / y0 := by
    rw [← Real.dist_eq]; exact (dist_le_pi_dist p f' 1).trans hd
  have h3 : (0 : ℝ) < √3 := by positivity
  have h33 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hc2 : 2 / √3 ≤ 2 := by rw [div_le_iff₀ h3]; nlinarith
  have hc1 : √3 / 2 ≤ 1 := by nlinarith
  have hq := sm_q_le (show 2 ≤ y0 by linarith)
  have ha : 1 / y0 ^ 2 ≤ 1 / y0 := by
    rw [div_le_div_iff₀ (by positivity) hy0]; nlinarith
  have hp0 : |p 0| ≤ 3 / 2 := by linarith [hA.1]
  have hp1 : |p 1| ≤ 3 / 2 := by linarith [hA.2.1]
  obtain ⟨b0, b1⟩ := sm_pert_bound hq.1.le hq.2.1 (by linarith [hq.2.1, hq.2.2]) (by positivity)
    ha hp0 hp1
  rw [sm_M1_mulVec hy0]
  refine sm_dist_le ?_ ?_ <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  · have e : 4 / (3 * y0 ^ 2 + 1) / 2 * p 0 + (4 / (3 * y0 ^ 2 + 1) - 4) / (2 * √3) * p 1 -
        -(2 / √3 * f' 1) =
        (4 / (3 * y0 ^ 2 + 1) / 2 * p 0 + 4 / (3 * y0 ^ 2 + 1) / (2 * √3) * p 1) -
          2 / √3 * (p 1 - f' 1) := by ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / √3)]
    have := mul_le_mul hc2 hd1 (abs_nonneg _) (by norm_num)
    have e2 : 2 * (1 / y0) = 2 / y0 := by ring
    have e3 : 8 / y0 = 2 / y0 + 2 * (3 / y0) := by ring
    linarith
  · have e : (√3 / 2 + √3 * (1 / y0 ^ 2) * (1 - 4 / (3 * y0 ^ 2 + 1)) / 6) * p 0 +
        1 / y0 ^ 2 * (4 - 4 / (3 * y0 ^ 2 + 1)) / 6 * p 1 - √3 / 2 * f' 0 =
        (√3 * (1 / y0 ^ 2) * (1 - 4 / (3 * y0 ^ 2 + 1)) / 6 * p 0 +
          1 / y0 ^ 2 * (4 - 4 / (3 * y0 ^ 2 + 1)) / 6 * p 1) + √3 / 2 * (p 0 - f' 0) := by
      ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < √3 / 2)]
    have := mul_le_mul hc1 hd0 (abs_nonneg _) (by norm_num)
    have e2 : 2 * (1 / y0) = 2 / y0 := by ring
    have e3 : 8 / y0 = 2 / y0 + 2 * (3 / y0) := by ring
    have : 0 ≤ 3 / y0 := by positivity
    linarith

/-! The four pieces of the rectangle boundary traced (up to `O(1/y₀)`) on the first switching
interval: `{1} × [0, √3/4]` (by `σ₀`), `[0, 1/2] × {√3/2}` (by `σ₁`), and the corner
`[-1, -1/2] × {√3/2} ∪ {-1} × [√3/4, √3/2]` (by `σ₂`). -/

private lemma sm_base_R0 {y0 y : ℝ} (hy : 2 ≤ y0) (h0 : 0 ≤ y) (h1 : y ≤ √3 / 4) :
    ∃ W, 4 / (3 * y0 ^ 2 + 1) ≤ W ∧ W ≤ 1 ∧
      dist (sm_GW y0 W *ᵥ sixthRoot 0) ![1, y] ≤ 3 / y0 := by
  have hy0 : 0 < y0 := by linarith
  have h3 : (0 : ℝ) < √3 := by positivity
  obtain ⟨hq0, hqr, hr2⟩ := sm_q_le hy
  have hr3 : 1 / y0 ≤ 3 / y0 := by gcongr; norm_num
  set c := √3 * y0 ^ 2 * y with hc
  have hc0 : 0 ≤ c := by positivity
  by_cases hcase : 4 / (3 * y0 ^ 2 + 1) ≤ 1 / (1 + c)
  · refine ⟨1 / (1 + c), hcase, by rw [div_le_one (by linarith)]; linarith, ?_⟩
    have hβ : ((1 / (1 + c))⁻¹ - 1) / (√3 * y0 ^ 2) = y := by
      rw [one_div, inv_inv, add_sub_cancel_left, hc]; field_simp
    rw [sm_GW_s0, hβ, dist_self]
    positivity
  · push Not at hcase
    refine ⟨_, le_rfl, by linarith, ?_⟩
    rw [sm_GW_s0]
    refine sm_dist_le ?_ ?_ <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    · simp only [sub_self, abs_zero]; positivity
    · have hlt : (4 / (3 * y0 ^ 2 + 1))⁻¹ < 1 + c := by
        rw [one_div] at hcase
        exact (inv_lt_comm₀ (by positivity) hq0).1 hcase
      have hβy : ((4 / (3 * y0 ^ 2 + 1))⁻¹ - 1) / (√3 * y0 ^ 2) ≤ y := by
        rw [div_le_iff₀ (by positivity)]; linarith
      have hβq := sm_beta_q hy
      rw [abs_sub_le_iff]
      constructor <;> linarith

private lemma sm_base_T0 {y0 x : ℝ} (hy : 2 ≤ y0) (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) :
    ∃ W, 4 / (3 * y0 ^ 2 + 1) ≤ W ∧ W ≤ 1 ∧
      dist (sm_GW y0 W *ᵥ sixthRoot 1) ![x, √3 / 2] ≤ 3 / y0 := by
  have hy0 : 0 < y0 := by linarith
  obtain ⟨hq0, hqr, hr2⟩ := sm_q_le hy
  have hr3 : 1 / y0 ≤ 3 / y0 := by gcongr; norm_num
  by_cases hcase : 4 / (3 * y0 ^ 2 + 1) ≤ 2 * x
  · have hW1 : 2 * x ≤ 1 := by linarith
    obtain ⟨hW0, -, -, hg0, hg1, -⟩ := sm_beta_gamma hy hW1 hcase
    refine ⟨2 * x, hcase, hW1, ?_⟩
    rw [sm_GW_s1 hy0.ne' hW0.ne']
    refine sm_dist_le ?_ ?_ <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    · rw [show 2 * x / 2 - x = 0 by ring, abs_zero]; positivity
    · rw [add_sub_cancel_left, abs_of_nonneg hg0]; linarith
  · push Not at hcase
    have hW1 : 4 / (3 * y0 ^ 2 + 1) ≤ 1 := by linarith
    obtain ⟨hW0, -, -, hg0, hg1, -⟩ := sm_beta_gamma hy hW1 le_rfl
    refine ⟨_, le_rfl, hW1, ?_⟩
    rw [sm_GW_s1 hy0.ne' hW0.ne']
    refine sm_dist_le ?_ ?_ <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    · rw [abs_sub_le_iff]; constructor <;> linarith
    · rw [add_sub_cancel_left, abs_of_nonneg hg0]; linarith

private lemma sm_base_C0t {y0 x : ℝ} (hy : 2 ≤ y0) (h0 : -1 ≤ x) (h1 : x ≤ -(1 / 2)) :
    ∃ W, 4 / (3 * y0 ^ 2 + 1) ≤ W ∧ W ≤ 1 ∧
      dist (sm_GW y0 W *ᵥ sixthRoot 2) ![x, √3 / 2] ≤ 3 / y0 := by
  have hy0 : 0 < y0 := by linarith
  obtain ⟨hq0, hqr, hr2⟩ := sm_q_le hy
  have hr3 : 2 / y0 ≤ 3 / y0 := by gcongr; norm_num
  have e3 : 3 / y0 = 3 * (1 / y0) := by ring
  have hr' : 1 / y0 ≤ max (1 / y0) (2 * (x + 1)) := le_max_left _ _
  have hW1 : max (1 / y0) (2 * (x + 1)) ≤ 1 := max_le (by linarith) (by linarith)
  have hWq : 4 / (3 * y0 ^ 2 + 1) ≤ max (1 / y0) (2 * (x + 1)) := hqr.trans hr'
  obtain ⟨hW0, hb0, -, hg0, hg1, -⟩ := sm_beta_gamma hy hW1 hWq
  have hb := sm_beta_le hy hr'
  refine ⟨_, hWq, hW1, ?_⟩
  rw [sm_GW_s2 hy0.ne' hW0.ne']
  refine sm_dist_le ?_ ?_ <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  · have h2 : 2 * (x + 1) ≤ max (1 / y0) (2 * (x + 1)) := le_max_right _ _
    have h3 : max (1 / y0) (2 * (x + 1)) ≤ 2 * (x + 1) + 1 / y0 :=
      max_le (by linarith) (by linarith)
    rw [abs_sub_le_iff]; constructor <;> linarith
  · rw [abs_sub_le_iff]; constructor <;> linarith

private lemma sm_base_C0l {y0 y : ℝ} (hy : 2 ≤ y0) (h0 : √3 / 4 ≤ y) (h1 : y ≤ √3 / 2) :
    ∃ W, 4 / (3 * y0 ^ 2 + 1) ≤ W ∧ W ≤ 1 ∧
      dist (sm_GW y0 W *ᵥ sixthRoot 2) ![-1, y] ≤ 3 / y0 := by
  have hy0 : 0 < y0 := by linarith
  have h3 : (0 : ℝ) < √3 := by positivity
  have h33 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have h31 : (1 : ℝ) ≤ √3 := by nlinarith [Real.sqrt_nonneg 3]
  obtain ⟨hq0, hqr, hr2⟩ := sm_q_le hy
  have hr3 : 1 / y0 ≤ 3 / y0 := by gcongr; norm_num
  have e3 : 3 / y0 = 3 * (1 / y0) := by ring
  set z := √3 / 2 - y with hz
  set c := √3 * y0 ^ 2 * z with hc
  have hz0 : 0 ≤ z := by linarith
  have hc0 : 0 ≤ c := by positivity
  have hzc : z = c / (√3 * y0 ^ 2) := by rw [hc]; field_simp
  rcases le_or_gt (1 + c) y0 with hA | hA
  · -- near the corner: `W = 1/y₀`
    have hW1 : 1 / y0 ≤ 1 := by linarith
    obtain ⟨hW0, hb0, -, hg0, hg1, -⟩ := sm_beta_gamma hy hW1 hqr
    have hb := sm_beta_le hy (le_refl (1 / y0))
    have hzr : z ≤ 1 / y0 := by
      rw [hzc, div_le_div_iff₀ (by positivity) hy0]
      nlinarith [mul_le_mul_of_nonneg_right h31 (sq_nonneg y0)]
    refine ⟨1 / y0, hqr, hW1, ?_⟩
    rw [sm_GW_s2 hy0.ne' hW0.ne']
    refine sm_dist_le ?_ ?_ <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    · rw [abs_sub_le_iff]; constructor <;> linarith
    · rw [abs_sub_le_iff]; constructor <;> linarith
  · by_cases hB : 4 / (3 * y0 ^ 2 + 1) ≤ 1 / (1 + c)
    · -- `β(W) = z` exactly
      have hW1 : 1 / (1 + c) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      have hWr : 1 / (1 + c) ≤ 1 / y0 := by
        rw [div_le_div_iff₀ (by linarith) hy0]; linarith
      obtain ⟨hW0, hb0, -, hg0, hg1, -⟩ := sm_beta_gamma hy hW1 hB
      refine ⟨1 / (1 + c), hB, hW1, ?_⟩
      rw [sm_GW_s2 hy0.ne' hW0.ne']
      have hβ : ((1 / (1 + c))⁻¹ - 1) / (√3 * y0 ^ 2) = z := by
        rw [one_div, inv_inv, add_sub_cancel_left, hzc]
      refine sm_dist_le ?_ ?_ <;>
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      · rw [abs_sub_le_iff]; constructor <;> linarith
      · rw [hβ, abs_sub_le_iff]; constructor <;> linarith
    · -- `W = q`
      push Not at hB
      have hW1 : 4 / (3 * y0 ^ 2 + 1) ≤ 1 := by linarith
      obtain ⟨hW0, hb0, -, hg0, hg1, -⟩ := sm_beta_gamma hy hW1 le_rfl
      have hlt : (4 / (3 * y0 ^ 2 + 1))⁻¹ < 1 + c := by
        rw [one_div] at hB
        exact (inv_lt_comm₀ (by positivity) hq0).1 hB
      have hβz : ((4 / (3 * y0 ^ 2 + 1))⁻¹ - 1) / (√3 * y0 ^ 2) ≤ z := by
        rw [hzc]; gcongr; linarith
      have hβq := sm_beta_q hy
      refine ⟨_, le_rfl, hW1, ?_⟩
      rw [sm_GW_s2 hy0.ne' hW0.ne']
      refine sm_dist_le ?_ ?_ <;>
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      · rw [abs_sub_le_iff]; constructor <;> linarith
      · rw [abs_sub_le_iff]; constructor <;> linarith

/-- The left edge `{-1} × [-√3/2, √3/2]` is good: its four quarters come from `σ₂`, `M σ₁`,
`-σ₀` and `M σ₂`. -/
private lemma sm_good_left {y0 y : ℝ} (hy : 4 ≤ y0) (h0 : -(√3 / 2) ≤ y) (h1 : y ≤ √3 / 2) :
    sm_good y0 ![-1, y] := by
  have hy2 : 2 ≤ y0 := by linarith
  have h3 : (0 : ℝ) < √3 := by positivity
  have hM : ![-1, y] =
      ![-(2 / √3 * ![2 * y / √3, √3 / 2] 1), √3 / 2 * ![2 * y / √3, √3 / 2] 0] := by
    ext i; fin_cases i <;> simp
  rcases le_total (√3 / 4) y with hA | hA
  · obtain ⟨W, hWq, hW1, hd⟩ := sm_base_C0l hy2 hA h1
    exact (sm_good_base hy hW1 hWq hd).1
  rcases le_total 0 y with hB | hB
  · obtain ⟨W, hWq, hW1, hd⟩ := sm_base_T0 hy2 (x := 2 * y / √3) (div_nonneg (by linarith) h3.le)
      (by rw [div_le_iff₀ h3]; linarith)
    rw [hM]; exact (sm_good_base hy hW1 hWq hd).2
  rcases le_total (-(√3 / 4)) y with hC | hC
  · obtain ⟨W, hWq, hW1, hd⟩ := sm_base_R0 hy2 (y := -y) (by linarith) (by linarith)
    have := sm_good_neg (sm_good_base hy hW1 hWq hd).1
    convert this using 1
    ext i; fin_cases i <;> simp
  · obtain ⟨W, hWq, hW1, hd⟩ := sm_base_C0t hy2 (x := 2 * y / √3)
      (by rw [le_div_iff₀ h3]; linarith) (by rw [div_le_iff₀ h3]; linarith)
    rw [hM]; exact (sm_good_base hy hW1 hWq hd).2

/-- The top edge `[-1, 1] × {√3/2}` is good: its four quarters come from `σ₂`, `M σ₀`, `σ₁` and
`-M σ₂`. -/
private lemma sm_good_top {y0 x : ℝ} (hy : 4 ≤ y0) (h0 : -1 ≤ x) (h1 : x ≤ 1) :
    sm_good y0 ![x, √3 / 2] := by
  have hy2 : 2 ≤ y0 := by linarith
  have h3 : (0 : ℝ) < √3 := by positivity
  rcases le_total x (-(1 / 2)) with hA | hA
  · obtain ⟨W, hWq, hW1, hd⟩ := sm_base_C0t hy2 h0 hA
    exact (sm_good_base hy hW1 hWq hd).1
  rcases le_total x 0 with hB | hB
  · obtain ⟨W, hWq, hW1, hd⟩ := sm_base_R0 hy2 (y := -(√3 * x / 2)) (by
      have : 0 ≤ √3 * -x := mul_nonneg h3.le (by linarith)
      linarith) (by nlinarith)
    have := (sm_good_base hy hW1 hWq hd).2
    convert this using 1
    ext i; fin_cases i <;> simp
  rcases le_total x (1 / 2) with hC | hC
  · obtain ⟨W, hWq, hW1, hd⟩ := sm_base_T0 hy2 hB hC
    exact (sm_good_base hy hW1 hWq hd).1
  · obtain ⟨W, hWq, hW1, hd⟩ := sm_base_C0l hy2 (y := √3 * x / 2) (by nlinarith) (by nlinarith)
    have := sm_good_neg (sm_good_base hy hW1 hWq hd).2
    convert this using 1
    ext i; fin_cases i <;> simp

/-- Every point of the rectangle boundary is good (`O(1/y₀)`-close to an arc point). -/
private lemma sm_good_Fr {y0 : ℝ} (hy : 4 ≤ y0) {f : Fin 2 → ℝ} (hf : f ∈ sm_Fr) :
    sm_good y0 f := by
  have hb : (0 : ℝ) ≤ √3 / 2 := by positivity
  have hf2 : f = ![f 0, f 1] := by ext i; fin_cases i <;> rfl
  have hneg : ∀ g : Fin 2 → ℝ, sm_good y0 (-g) → sm_good y0 g := fun g hg ↦ by
    simpa using sm_good_neg hg
  rcases hf with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rw [abs_le] at h1
    rcases (abs_eq zero_le_one).1 h0 with e | e
    · refine hneg f ?_
      have : -f = ![-1, -f 1] := by rw [hf2]; ext i; fin_cases i <;> simp [e]
      rw [this]; exact sm_good_left hy (by linarith) (by linarith)
    · rw [hf2, e]; exact sm_good_left hy h1.1 h1.2
  · rw [abs_le] at h0
    rcases (abs_eq hb).1 h1 with e | e
    · rw [hf2, e]; exact sm_good_top hy h0.1 h0.2
    · refine hneg f ?_
      have : -f = ![-f 0, √3 / 2] := by rw [hf2]; ext i; fin_cases i <;> simp [e]
      rw [this]; exact sm_good_top hy (by linarith) (by linarith)

/-- On `[0, t_sw]` the parameter `W = exp(-√3 y₀ t)` lies in `[q, 1]`, `q = 4/(3y₀² + 1)`. -/
private lemma sm_W_mem {y0 t : ℝ} (hy : 1 < y0) (ht : t ∈ Set.Icc 0 (minusSwitchTime y0)) :
    4 / (3 * y0 ^ 2 + 1) ≤ Real.exp (-(√3 * y0 * t)) ∧ Real.exp (-(√3 * y0 * t)) ≤ 1 := by
  have hy0 : 0 < y0 := by linarith
  constructor
  · rw [← sm_exp_switchTime hy0]
    exact Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left ht.2 (by positivity)))
  · exact Real.exp_le_one_iff.2 (neg_nonpos.2 (by have := ht.1; positivity))

/-- Every `W ∈ [q, 1]` is `exp(-√3 y₀ s)` for some `s ∈ [0, t_sw]`. -/
private lemma sm_exists_time {y0 W : ℝ} (hy : 1 < y0) (hWq : 4 / (3 * y0 ^ 2 + 1) ≤ W)
    (hW1 : W ≤ 1) :
    ∃ s ∈ Set.Icc 0 (minusSwitchTime y0), Real.exp (-(√3 * y0 * s)) = W := by
  have hy0 : 0 < y0 := by linarith
  have h3 : (0 : ℝ) < √3 := by positivity
  have hq : 0 < 4 / (3 * y0 ^ 2 + 1) := by positivity
  have hW0 : 0 < W := lt_of_lt_of_le hq hWq
  refine ⟨-Real.log W / (√3 * y0), ⟨div_nonneg (neg_nonneg.2 (Real.log_nonpos hW0.le hW1))
    (by positivity), ?_⟩, ?_⟩
  · rw [minusSwitchTime]
    exact div_le_div_of_nonneg_right (neg_le_neg (Real.log_le_log hq hWq)) (by positivity)
  · rw [show -(√3 * y0 * (-Real.log W / (√3 * y0))) = Real.log W by field_simp,
      Real.exp_log hW0]

private lemma sm_G1_mulVec (y0 t : ℝ) (v : Fin 2 → ℝ) :
    sm_G1 y0 t *ᵥ v = (sm_mG y0 (minusSwitchTime y0) * R) *ᵥ
      (sm_mG y0 (t - minusSwitchTime y0) *ᵥ (R⁻¹ *ᵥ v)) := by
  rw [sm_G1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

private lemma sm_G2_mulVec (y0 t : ℝ) (v : Fin 2 → ℝ) :
    sm_G2 y0 t *ᵥ v = (sm_mG y0 (minusSwitchTime y0) * R) *ᵥ
      (sm_G1 y0 (t - minusSwitchTime y0) *ᵥ (R⁻¹ *ᵥ v)) := by
  rw [sm_G2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

/-- **Hausdorff convergence** of the six arcs to the boundary of `[-1, 1] × [-√3/2, √3/2]`: for
`k ∈ (1, 4/3)` with `y₀(k) ≥ 28`, the Hausdorff distance is at most `14/y₀(k)`. -/
private theorem sm_hausdorff_tendsto (g X : ℝ → ℝ → Mat2)
    (hgX : ∀ k : ℝ, 1 < k →
      IsStateTrajectory (minusTf k) (minusPolygonControlAt (minusSwitchTime (minusY₀ k)))
        (g k) (X k) ∧ g k 0 = 1 ∧ X k 0 = Φ 0 (minusY₀ k)) :
    Tendsto (fun k ↦ Metric.hausdorffEDist
        (⋃ j : ZMod 6, (fun t ↦ g k t *ᵥ sixthRoot j) '' Set.Icc 0 (minusTf k)) sm_Fr)
      (𝓝[>] 1) (𝓝 0) := by
  have hev : ∀ᶠ k in 𝓝[>] (1 : ℝ), k ∈ Set.Ioo 1 (4 / 3) := Ioo_mem_nhdsGT (by norm_num)
  have hlim := sm_inv_tendsto
  have hev2 : ∀ᶠ k in 𝓝[>] (1 : ℝ), 1 / minusY₀ k < 1 / 28 :=
    hlim.eventually (gt_mem_nhds (by norm_num))
  have hup : Tendsto (fun k ↦ ENNReal.ofReal (14 * (1 / minusY₀ k))) (𝓝[>] 1) (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (hlim.const_mul 14)
    rwa [mul_zero, ENNReal.ofReal_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Filter.Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [hev, hev2] with k hk hk2
  obtain ⟨hk1, hk3⟩ := hk
  set y0 := minusY₀ k with hy0def
  have hy1 : 1 < y0 := sm_one_lt_minusY₀ hk1
  have hy0 : 0 < y0 := by linarith
  have hy : 28 ≤ y0 := by
    rw [div_lt_div_iff₀ hy0 (by norm_num)] at hk2; linarith
  set τ := minusSwitchTime y0 with hτdef
  have hτ : 0 < τ := sm_minusSwitchTime_pos hy1
  have hT2 : 2 * τ ≤ minusTf k := by rw [minusTf]; nlinarith
  have hT3 : minusTf k ≤ 3 * τ := by rw [minusTf]; nlinarith
  obtain ⟨htraj, hg0, hX0⟩ := hgX k hk1
  obtain ⟨h0, h1, h2⟩ := sm_minus_unique hy1 hT2 hT3 htraj hg0 hX0
  have hτT : τ ≤ minusTf k := by linarith
  have e14 : 14 * (1 / y0) = 14 / y0 := by ring
  rw [e14]
  have hδ : (0 : ℝ) ≤ 14 / y0 := by positivity
  have hd2 : 2 / y0 ≤ 1 / 2 := by rw [div_le_div_iff₀ hy0 (by norm_num)]; linarith
  have hd6 : 2 * (2 / y0) + 2 / y0 ≤ 1 / 2 := by
    have : 2 * (2 / y0) + 2 / y0 = 6 / y0 := by ring
    rw [this, div_le_div_iff₀ hy0 (by norm_num)]; linarith
  -- the arc points on the three switching intervals
  have harc0 : ∀ s ∈ Set.Icc 0 τ, ∀ j : ZMod 6, sm_Ann (2 / y0) (sm_mG y0 s *ᵥ sixthRoot j) :=
    fun s hs j ↦ by
      obtain ⟨hW1, hW2⟩ := sm_W_mem hy1 hs
      rw [sm_mG_eq_GW hy0]
      exact sm_GW_Ann (by linarith) hW2 hW1 j
  refine Metric.hausdorffEDist_le_of_mem_edist ?_ ?_
  · intro p hp
    simp only [Set.mem_iUnion, Set.mem_image] at hp
    obtain ⟨j, t, ht, rfl⟩ := hp
    suffices hA : sm_Ann (14 / y0) (g k t *ᵥ sixthRoot j) by
      obtain ⟨f, hf, hd⟩ := sm_Ann_near hδ hA
      exact ⟨f, hf, (edist_le_ofReal hδ).2 hd⟩
    rcases le_or_gt t τ with hA | hA
    · rw [(h0 t ⟨ht.1, hA⟩).1]
      exact sm_Ann_mono (by gcongr; norm_num) (harc0 t ⟨ht.1, hA⟩ j)
    rcases le_or_gt t (2 * τ) with hB | hB
    · rw [(h1 t ⟨hA.le, hB⟩).1, sm_G1_mulVec, show j = j - 1 + 1 by ring, sm_Rinv_sixthRoot]
      have := sm_M1_Ann (y0 := y0) (by linarith) (by positivity) hd2
        (harc0 (t - τ) ⟨by linarith, by linarith⟩ (j - 1))
      refine sm_Ann_mono ?_ this
      have e : 2 * (2 / y0) + 2 / y0 = 6 / y0 := by ring
      rw [e]; gcongr; norm_num
    · rw [(h2 t ⟨hB.le, ht.2⟩).1, sm_G2_mulVec, show j = j - 1 + 1 by ring, sm_Rinv_sixthRoot,
        sm_G1_mulVec, show j - 1 = j - 1 - 1 + 1 by ring, sm_Rinv_sixthRoot,
        show t - minusSwitchTime y0 - minusSwitchTime y0 = t - 2 * τ by ring]
      have hin := harc0 (t - 2 * τ) ⟨by linarith, by linarith [ht.2]⟩ (j - 1 - 1)
      have h6 := sm_M1_Ann (y0 := y0) (by linarith) (by positivity) hd2 hin
      have h14 := sm_M1_Ann (y0 := y0) (by linarith) (by positivity) hd6 h6
      refine sm_Ann_mono ?_ h14
      have : 2 * (2 * (2 / y0) + 2 / y0) + 2 / y0 = 14 / y0 := by ring
      rw [this]
  · intro f hf
    obtain ⟨W, hWq, hW1, j, hd | hd⟩ := sm_good_Fr (y0 := y0) (by linarith) hf
    · obtain ⟨s, hs, hWs⟩ := sm_exists_time hy1 hWq hW1
      refine ⟨g k s *ᵥ sixthRoot j, ?_, ?_⟩
      · simp only [Set.mem_iUnion, Set.mem_image]
        exact ⟨j, s, ⟨hs.1, hs.2.trans hτT⟩, rfl⟩
      · rw [(h0 s hs).1, sm_mG_eq_GW hy0 s, hWs, edist_comm, edist_le_ofReal hδ]
        exact hd.trans (by gcongr; norm_num)
    · obtain ⟨s, hs, hWs⟩ := sm_exists_time hy1 hWq hW1
      have hst : s + τ ∈ Set.Icc τ (2 * τ) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
      refine ⟨g k (s + τ) *ᵥ sixthRoot (j + 1), ?_, ?_⟩
      · simp only [Set.mem_iUnion, Set.mem_image]
        exact ⟨j + 1, s + τ, ⟨by linarith [hst.1], hst.2.trans hT2⟩, rfl⟩
      · rw [(h1 _ hst).1, sm_G1_mulVec, sm_Rinv_sixthRoot, add_sub_cancel_right,
          sm_mG_eq_GW hy0 s, hWs, edist_comm,
          edist_le_ofReal hδ]
        exact hd.trans (by gcongr; norm_num)

/-- **Remark 7.6.4** (`rem:6k-2-rectangle`, label of this formalization). When `k = 1`, the
smoothed `(6k - 2)`-gon degenerates to a rectangle with corners and area `√12`. Allowing `k` to be
non-integral, for small values of `k > 1`, we obtain smoothed rectangles (that do not quite
satisfy the boundary conditions); the figure (TeX 6435: "the shape appears to be tending to a
rectangle of area `√12` as `k ↦ 1`").

Reading. At `k = 1` the closing condition `4/(3y₀² + 1) = 2 cos(π/2) = 0` has no solution
(`y₀ = ∞`), so "when `k = 1`" is read as the limit `k → 1⁺` of the interpolated `(6k - 2)`-gons:
for real `k > 1`, the state trajectory `(g_k, X_k)` on `[0, t_f(k)]` with the control of
`eqn:3k+2`, switching time `t_sw(y₀(k))`, `g_k(0) = I` and `X_k(0) = Φ(i y₀(k))` (Remark 7.6.2).
The claims: (1) its cost, the area of §3.2, tends to `√12`; (2) its six arcs
`σ_j([0, t_f(k)])`, `σ_j(t) = g_k(t) s_j*`, tend in the Hausdorff distance to the boundary of a
rectangle (image of `[-a, a] × [-b, b]` under a Euclidean motion) of area `4ab = √12`. (The
rectangle is `[-1, 1] × [-√3/2, √3/2]`, by the figure; the statement only asserts a rectangle, as
the remark does. Hausdorff convergence does not depend on the metric of `ℝ²`, Mathlib's being the
sup metric.) The trajectories are quantified universally; they exist and are unique.

Proof (the book gives none; the remark reports a numerical figure). For `k ∈ (1, 4/3)` the
terminal time `(3k - 1) t_sw` lies in `(2t_sw, 3t_sw)`, and the trajectory is the spline: the
closed-form `e₂`-arc `X(t) = Φ((1 - W)/√3 + i y₀ W)`, `W = e^{-√3 y₀ t}` (the mirror image of the
`e₃`-arc of §7.5, with `z(t_sw) = R · z₀`), followed by its conjugates by `R` and `R²`
(`sm_minus_unique`, by Lemma 7.1.1 and uniqueness for the linear equations on each interval).
(1) The cost is `2 · √3(y₀² - 1 + ln q/3)/y₀²` for the two full arcs (`q = 4/(3y₀² + 1)`; the
analogue of the cost `√3(1 - y₀² - ℓ/3)/y₀²` per arc of the `(6k + 2)`-gon) plus the cost of the
partial third arc (`sm_minus_cost`); as `k → 1⁺`, `cos(πk/(3k - 1)) → 0`, so `1/y₀² → 0`,
`ln q/y₀² → 0` and, by Jordan's inequality, `(k - 1) ln q → 0`, and the cost tends to `2√3 = √12`.
(2) With `r = 1/y₀`, every arc point lies within `14 r` of the boundary of
`[-1, 1] × [-√3/2, √3/2]`, and every point of that boundary lies within `8 r` of an arc point of
the first two switching intervals (the explicit arcs of `g₀ = sm_mG`, and their images under
`g_sw R → [[0, -2/√3], [√3/2, 0]]`, a map of the rectangle boundary onto itself). -/
theorem remark7_6_4 (g X : ℝ → ℝ → Mat2)
    (hgX : ∀ k : ℝ, 1 < k →
      IsStateTrajectory (minusTf k) (minusPolygonControlAt (minusSwitchTime (minusY₀ k)))
        (g k) (X k) ∧ g k 0 = 1 ∧ X k 0 = Φ 0 (minusY₀ k)) :
    Tendsto (fun k ↦ reinhardtCost (minusTf k) (X k)) (𝓝[>] 1) (𝓝 √12) ∧
      ∃ (A : Mat2) (c : Fin 2 → ℝ) (a b : ℝ), A ∈ Matrix.orthogonalGroup (Fin 2) ℝ ∧
        0 < a ∧ 0 < b ∧ 4 * a * b = √12 ∧
        Tendsto (fun k ↦ Metric.hausdorffEDist
            (⋃ j : ZMod 6, (fun t ↦ g k t *ᵥ sixthRoot j) '' Set.Icc 0 (minusTf k))
            (frontier ((fun x ↦ A *ᵥ x + c) '' {x : Fin 2 → ℝ | |x 0| ≤ a ∧ |x 1| ≤ b})))
          (𝓝[>] 1) (𝓝 0) := by
  refine ⟨sm_cost_tendsto g X hgX, 1, 0, 1, √3 / 2, (Matrix.orthogonalGroup (Fin 2) ℝ).one_mem,
    one_pos, by positivity, by rw [poly_sqrt12]; ring, ?_⟩
  rw [sm_frontier_rect]
  exact sm_hausdorff_tendsto g X hgX

end SmoothedPolygons
