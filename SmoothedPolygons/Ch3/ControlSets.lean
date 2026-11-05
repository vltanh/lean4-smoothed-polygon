module

public import SmoothedPolygons.Ch2.MultiCurve
public import Basic.Analysis.Calculus.MatrixEntrywise
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Control sets (§3.3)

The state-dependent curvatures `κ_j` (`eqn:state-dep-curvature`), their positivity
(Lemma 3.3.1), the control variables (Definition 3.3.2), the control simplex `U_T`
(Definition 3.3.3, `controlSimplex` in `SmoothedPolygons.Defs`), the control matrix `Z_u`
(`eqn:Z0`, `eqn:def-Z0`) and the star condition in terms of `Z_u` (Lemma 3.3.4).
-/

@[expose] public section

namespace SmoothedPolygons

open MeasureTheory Matrix
open scoped Topology

/-! ### The sixth roots of unity -/

private lemma algA_sixthRoot_eq (k : ZMod 6) (n : ℕ) (hn : k.val = n) :
    sixthRoot k = ![Real.cos (Real.pi * n / 3), Real.sin (Real.pi * n / 3)] := by
  rw [sixthRoot, hn]

lemma algA_sixthRoot_zero : sixthRoot 0 = ![1, 0] := by
  rw [algA_sixthRoot_eq 0 0 rfl]; simp

lemma algA_sixthRoot_one : sixthRoot 1 = ![1 / 2, √3 / 2] := by
  rw [algA_sixthRoot_eq 1 1 rfl]; simp

lemma algA_sixthRoot_two : sixthRoot 2 = ![-(1 / 2), √3 / 2] := by
  rw [algA_sixthRoot_eq 2 2 rfl]
  have : Real.pi * (2 : ℕ) / 3 = Real.pi - Real.pi / 3 := by push_cast; ring
  rw [this, Real.cos_pi_sub, Real.sin_pi_sub]; simp

lemma algA_sixthRoot_three : sixthRoot 3 = ![-1, 0] := by
  rw [algA_sixthRoot_eq 3 3 rfl]
  have : Real.pi * (3 : ℕ) / 3 = Real.pi := by push_cast; ring
  rw [this]; simp

lemma algA_sixthRoot_four : sixthRoot 4 = ![-(1 / 2), -(√3 / 2)] := by
  rw [algA_sixthRoot_eq 4 4 rfl]
  have : Real.pi * (4 : ℕ) / 3 = Real.pi / 3 + Real.pi := by push_cast; ring
  rw [this, Real.cos_add_pi, Real.sin_add_pi]; simp

lemma algA_sixthRoot_five : sixthRoot 5 = ![1 / 2, -(√3 / 2)] := by
  rw [algA_sixthRoot_eq 5 5 rfl]
  have : Real.pi * (5 : ℕ) / 3 = -(Real.pi / 3) + 2 * Real.pi := by push_cast; ring
  rw [this, Real.cos_add_two_pi, Real.sin_add_two_pi, Real.cos_neg, Real.sin_neg]; simp

/-- The sixth roots of unity form a multi-point. -/
lemma algA_isMultiPoint_sixthRoot : IsMultiPoint sixthRoot := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  intro j
  fin_cases j
  on_goal 1 => change sixthRoot 0 + sixthRoot 2 + sixthRoot 4 = 0 ∧ sixthRoot 3 = -sixthRoot 0 ∧
                    det2 (sixthRoot 0) (sixthRoot 1) = √3 / 2
  on_goal 2 => change sixthRoot 1 + sixthRoot 3 + sixthRoot 5 = 0 ∧ sixthRoot 4 = -sixthRoot 1 ∧
                    det2 (sixthRoot 1) (sixthRoot 2) = √3 / 2
  on_goal 3 => change sixthRoot 2 + sixthRoot 4 + sixthRoot 0 = 0 ∧ sixthRoot 5 = -sixthRoot 2 ∧
                    det2 (sixthRoot 2) (sixthRoot 3) = √3 / 2
  on_goal 4 => change sixthRoot 3 + sixthRoot 5 + sixthRoot 1 = 0 ∧ sixthRoot 0 = -sixthRoot 3 ∧
                    det2 (sixthRoot 3) (sixthRoot 4) = √3 / 2
  on_goal 5 => change sixthRoot 4 + sixthRoot 0 + sixthRoot 2 = 0 ∧ sixthRoot 1 = -sixthRoot 4 ∧
                    det2 (sixthRoot 4) (sixthRoot 5) = √3 / 2
  on_goal 6 => change sixthRoot 5 + sixthRoot 1 + sixthRoot 3 = 0 ∧ sixthRoot 2 = -sixthRoot 5 ∧
                    det2 (sixthRoot 5) (sixthRoot 0) = √3 / 2
  all_goals
    simp only [algA_sixthRoot_zero, algA_sixthRoot_one, algA_sixthRoot_two, algA_sixthRoot_three,
      algA_sixthRoot_four, algA_sixthRoot_five, det2]
    refine ⟨?_, ?_, ?_⟩
    · ext i; fin_cases i <;> norm_num
    · ext i; fin_cases i <;> simp
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; linarith [h3]

/-- The points `s_{2j}* = s₀*, s₂*, s₄*` (`j = 0, 1, 2`) of the state-dependent curvatures. -/
lemma algA_sixthRoot_two_mul (j : Fin 3) :
    sixthRoot (2 * (j.val : ZMod 6)) =
      ![![1, 0], ![-(1 / 2), √3 / 2], ![-(1 / 2), -(√3 / 2)]] j := by
  fin_cases j
  · exact algA_sixthRoot_zero
  · exact algA_sixthRoot_two
  · exact algA_sixthRoot_four

/-- The quadratic form `v ↦ det(v, Yv)` in coordinates. -/
lemma algA_det2_mulVec (Y : Mat2) (v : Fin 2 → ℝ) :
    det2 v (Y *ᵥ v) = Y 1 0 * v 0 ^ 2 + (Y 1 1 - Y 0 0) * v 0 * v 1 - Y 0 1 * v 1 ^ 2 := by
  simp [det2, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- `det(s₀*, Y s₀*) = Y₁₀`. -/
lemma algA_det2_sixthRoot_zero (Y : Mat2) :
    det2 (sixthRoot (2 * ((0 : Fin 3).val : ZMod 6)))
      (Y *ᵥ sixthRoot (2 * ((0 : Fin 3).val : ZMod 6))) = Y 1 0 := by
  rw [algA_sixthRoot_two_mul, algA_det2_mulVec]; simp

/-- `det(s₂*, Y s₂*) = Y₁₀/4 - (√3/4)(Y₁₁ - Y₀₀) - (3/4)Y₀₁`. -/
lemma algA_det2_sixthRoot_two (Y : Mat2) :
    det2 (sixthRoot (2 * ((1 : Fin 3).val : ZMod 6)))
      (Y *ᵥ sixthRoot (2 * ((1 : Fin 3).val : ZMod 6))) =
      Y 1 0 / 4 - √3 / 4 * (Y 1 1 - Y 0 0) - 3 / 4 * Y 0 1 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [algA_sixthRoot_two_mul, algA_det2_mulVec]; simp
  linear_combination (-(Y 0 1) / 4) * h3

/-- `det(s₄*, Y s₄*) = Y₁₀/4 + (√3/4)(Y₁₁ - Y₀₀) - (3/4)Y₀₁`. -/
lemma algA_det2_sixthRoot_four (Y : Mat2) :
    det2 (sixthRoot (2 * ((2 : Fin 3).val : ZMod 6)))
      (Y *ᵥ sixthRoot (2 * ((2 : Fin 3).val : ZMod 6))) =
      Y 1 0 / 4 + √3 / 4 * (Y 1 1 - Y 0 0) - 3 / 4 * Y 0 1 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [algA_sixthRoot_two_mul, algA_det2_mulVec]; simp
  linear_combination (-(Y 0 1) / 4) * h3

/-- A traceless `2 × 2` matrix is `[[a, b], [c, -a]]`. -/
lemma algA_eta_of_trace_eq_zero (X : Mat2) (hX : X.trace = 0) :
    X = !![X 0 0, X 0 1; X 1 0, -X 0 0] := by
  rw [Matrix.trace_fin_two] at hX
  ext i j; fin_cases i <;> fin_cases j <;> simp; linear_combination hX

/-- Equation `eqn:det-rho`: `det X = ρ₀ρ₁ + ρ₁ρ₂ + ρ₂ρ₀` for `X ∈ 𝔰𝔩₂(ℝ)`. -/
lemma algA_det_eq_rho (X : Mat2) (hX : X.trace = 0) :
    X.det = ρ₀ X * ρ₁ X + ρ₁ X * ρ₂ X + ρ₂ X * ρ₀ X := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3' : √3 ≠ 0 := by positivity
  rw [algA_eta_of_trace_eq_zero X hX]
  simp [ρ₀, ρ₁, ρ₂, Matrix.det_fin_two]
  field_simp
  linear_combination (-2 * X 0 1 * X 1 0) * h3

/-- The vertex `e_{i+1}` of the control simplex `U_T`: `vertex 0 = e₁ = (1, 0, 0)`,
`vertex 1 = e₂ = (0, 1, 0)`, `vertex 2 = e₃ = (0, 0, 1)`. -/
noncomputable def vertex (i : Fin 3) : Fin 3 → ℝ := Pi.single i 1

/-- The state-dependent curvature `κ_j = det(s_{2j}*, (X + X⁻¹X') s_{2j}*)`, `j = 0, 1, 2`
(`eqn:state-dep-curvature`), as a function of `X` and its derivative `X'`. -/
noncomputable def stateCurvature (X X' : Mat2) (j : Fin 3) : ℝ :=
  det2 (sixthRoot (2 * (j.val : ZMod 6))) ((X + X⁻¹ * X') *ᵥ sixthRoot (2 * (j.val : ZMod 6)))

/-- `X = g⁻¹g'` is traceless on `[0, t_f]` when `det g = 1` there: the derivative
`tr(adj(g) g') = tr(g⁻¹g')` of `det g` vanishes. -/
lemma algA_trace_inv_mul_eq_zero {tf : ℝ} (htf : 0 < tf) {g g' : ℝ → Mat2}
    (hg : ∀ t ∈ Set.Icc 0 tf, HasDerivWithinAtEntrywise g (g' t) (Set.Icc 0 tf) t)
    (hdet : ∀ t ∈ Set.Icc 0 tf, (g t).det = 1) (t : ℝ) (ht : t ∈ Set.Icc 0 tf) :
    ((g t)⁻¹ * g' t).trace = 0 := by
  have h1 := (hg t ht).det_fin_two
  have h2 : HasDerivWithinAt (fun s ↦ (g s).det) 0 (Set.Icc 0 tf) t :=
    (hasDerivWithinAt_const t _ (1 : ℝ)).congr (fun s hs ↦ hdet s hs) (hdet t ht)
  have h := (uniqueDiffOn_Icc htf t ht).eq_deriv _ h1 h2
  rw [Matrix.inv_def, hdet t ht, Ring.inverse_one, one_smul, Matrix.adjugate_fin_two,
    Matrix.trace_fin_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  linear_combination h

/-- The derivative of a curve of traceless matrices is traceless (for `derivEntrywise`, which is
defined everywhere, this holds at every interior point, with no differentiability needed). -/
lemma algA_trace_derivEntrywise_eq_zero {X : ℝ → Mat2} {s : Set ℝ} {t : ℝ} (hs : s ∈ 𝓝 t)
    (hX : ∀ τ ∈ s, (X τ).trace = 0) : (derivEntrywise X t).trace = 0 := by
  have : (fun τ ↦ X τ 1 1) =ᶠ[𝓝 t] fun τ ↦ -X τ 0 0 :=
    Filter.eventually_of_mem hs fun τ hτ ↦ by
      have := hX τ hτ; rw [Matrix.trace_fin_two] at this; linear_combination this
  rw [Matrix.trace_fin_two]
  simp only [derivEntrywise, Matrix.of_apply]
  rw [this.deriv_eq, deriv.fun_neg]; ring

/-- The short calculation of Lemma 3.3.1: for `X, X' ∈ 𝔰𝔩₂(ℝ)` with `X` invertible, if
`κ₀ = κ₁ = 0` then `κ₂ = √3 det(X)/ρ₀(X)`. -/
lemma algA_stateCurvature_two_eq (X X' : Mat2) (hX : X.trace = 0) (hX' : X'.trace = 0)
    (hdet : X.det ≠ 0) (hρ : ρ₀ X ≠ 0) (h0 : stateCurvature X X' 0 = 0)
    (h1 : stateCurvature X X' 1 = 0) :
    stateCurvature X X' 2 = √3 * X.det / ρ₀ X := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3' : √3 ≠ 0 := by positivity
  set Y := X + X⁻¹ * X' with hY
  -- `⟨X, Y⟩ = ⟨X, X⟩ + tr X' = -2 det X`
  have htr : (X * Y).trace = -2 * X.det := by
    have : X * Y = X * X + X' := by
      rw [hY, Matrix.mul_add, ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet), Matrix.one_mul]
    rw [this, Matrix.trace_add, hX', add_zero, algA_eta_of_trace_eq_zero X hX]
    simp [Matrix.trace_fin_two, Matrix.det_fin_two]; ring
  simp only [stateCurvature] at h0 h1 ⊢
  rw [← hY] at h0 h1 ⊢
  rw [algA_det2_sixthRoot_zero] at h0
  rw [algA_det2_sixthRoot_two] at h1
  rw [algA_det2_sixthRoot_four, eq_div_iff hρ]
  have hX11 : X 1 1 = -X 0 0 := by
    rw [Matrix.trace_fin_two] at hX; linear_combination hX
  simp only [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two,
    hX11] at htr
  rw [Matrix.det_fin_two, hX11]
  have key : (Y 1 0 / 4 + √3 / 4 * (Y 1 1 - Y 0 0) - 3 / 4 * Y 0 1) * (X 1 0 + √3 * X 0 0) =
      √3 * √3 * (X 0 0 * -X 0 0 - X 0 1 * X 1 0) := by
    linear_combination (√3 * X 0 0 - X 1 0) * h1 + (X 1 0 / 2 + √3 ^ 2 * X 0 1 / 2) * h0 +
      (X 1 0 * Y 0 1 / 2) * h3 - (√3 ^ 2 / 2) * htr
  rw [ρ₀, mul_div_assoc', div_eq_iff h3']
  linear_combination key

/-- **Lemma 3.3.1** (`lem:curvature-pos`). Let `g : [0, t_f] → SL₂(ℝ)` be `C¹` with Lipschitz
derivative, and let `X = g⁻¹g'` satisfy the star inequalities and the curvature conditions
`κ_j ≥ 0` (`eqn:state-dep-curvature`) almost everywhere. Then almost everywhere some
`κ_j(t) > 0`. -/
theorem lemma3_3_1 (tf : ℝ) (g g' : ℝ → Mat2)
    (hg : ∀ t ∈ Set.Icc 0 tf, HasDerivWithinAtEntrywise g (g' t) (Set.Icc 0 tf) t)
    (hdet : ∀ t ∈ Set.Icc 0 tf, (g t).det = 1) (hLip : LipschitzOnEntrywise g' (Set.Icc 0 tf))
    (X : ℝ → Mat2) (hX : ∀ t, X t = (g t)⁻¹ * g' t)
    (hstar : ∀ t ∈ Set.Icc 0 tf, 0 < ρ₀ (X t) ∧ 0 < ρ₁ (X t) ∧ 0 < ρ₂ (X t))
    (hcurv : ∀ᵐ t, t ∈ Set.Ioo 0 tf → ∀ j, 0 ≤ stateCurvature (X t) (derivEntrywise X t) j) :
    ∀ᵐ t, t ∈ Set.Ioo 0 tf → ∃ j, 0 < stateCurvature (X t) (derivEntrywise X t) j := by
  -- The Lipschitz hypothesis `hLip` (which makes `X` differentiable almost everywhere) is not
  -- needed here: `tr X' = 0` holds at every interior point for the entrywise `deriv`.
  rcases le_or_gt tf 0 with htf | htf
  · exact Filter.Eventually.of_forall fun t ht ↦ absurd (ht.1.trans ht.2) (not_lt.2 htf)
  filter_upwards [hcurv] with t hκ ht
  have htI : t ∈ Set.Icc 0 tf := Set.Ioo_subset_Icc_self ht
  -- `X = g⁻¹g'` is traceless since `det g = 1`, hence so is `X'`
  have htrX : ∀ τ ∈ Set.Icc 0 tf, (X τ).trace = 0 := fun τ hτ ↦ by
    rw [hX]; exact algA_trace_inv_mul_eq_zero htf hg hdet τ hτ
  have htrX' : (derivEntrywise X t).trace = 0 :=
    algA_trace_derivEntrywise_eq_zero (Icc_mem_nhds ht.1 ht.2) htrX
  obtain ⟨h0, -, -⟩ := hstar t htI
  -- `det X = ρ₀ρ₁ + ρ₁ρ₂ + ρ₂ρ₀ > 0` (`eqn:det-rho`)
  have hdetpos : 0 < (X t).det := by
    obtain ⟨h0, h1, h2⟩ := hstar t htI
    rw [algA_det_eq_rho _ (htrX t htI)]; positivity
  by_contra hne
  simp only [not_exists, not_lt] at hne
  -- if `κ₀ = κ₁ = 0`, then `κ₂ = √3 det(X)/ρ₀(X) > 0`
  have k2 := algA_stateCurvature_two_eq _ _ (htrX t htI) htrX' hdetpos.ne' h0.ne'
    (le_antisymm (hne 0) (hκ ht 0)) (le_antisymm (hne 1) (hκ ht 1))
  have : 0 < stateCurvature (X t) (derivEntrywise X t) 2 := by
    rw [k2]; exact div_pos (mul_pos (by positivity) hdetpos) h0
  linarith [hne 2]

/-- **Definition 3.3.2** (`def:control-variables`). The control variables
`u_j = κ_j / (κ₀ + κ₁ + κ₂)`, the normalized state-dependent curvatures. -/
noncomputable def controlVariables (κ : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun j ↦ κ j / (κ 0 + κ 1 + κ 2)

/-- The control matrix is determined by `u_j = det(s_{2j}*, Z_u s_{2j}*)`, `j = 0, 1, 2`
(`eqn:def-Z0`): `Z_u` satisfies these equations, and it is the only traceless matrix that does. -/
theorem controlMatrix_spec (u : Fin 3 → ℝ) :
    (controlMatrix u).trace = 0 ∧
      (∀ j : Fin 3, u j = det2 (sixthRoot (2 * (j.val : ZMod 6)))
        (controlMatrix u *ᵥ sixthRoot (2 * (j.val : ZMod 6)))) ∧
      ∀ Z : Mat2, Z.trace = 0 → (∀ j : Fin 3, u j = det2 (sixthRoot (2 * (j.val : ZMod 6)))
        (Z *ᵥ sixthRoot (2 * (j.val : ZMod 6)))) → Z = controlMatrix u := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3' : √3 ≠ 0 := by positivity
  refine ⟨?_, fun j ↦ ?_, fun Z hZ hu ↦ ?_⟩
  · simp [controlMatrix, Matrix.trace_fin_two]; ring
  · rw [algA_sixthRoot_two_mul, algA_det2_mulVec]
    fin_cases j <;> simp [controlMatrix] <;> field_simp <;>
      linear_combination (u 0 - 2 * u 1 - 2 * u 2) * h3
  · -- the three linear equations determine the entries of a traceless `Z`
    have e0 := hu 0
    have e1 := hu 1
    have e2 := hu 2
    rw [algA_det2_sixthRoot_zero] at e0
    rw [algA_det2_sixthRoot_two] at e1
    rw [algA_det2_sixthRoot_four] at e2
    have hZ11 : Z 1 1 = -Z 0 0 := by
      rw [Matrix.trace_fin_two] at hZ; linear_combination hZ
    rw [hZ11] at e1 e2
    have ha : Z 0 0 = (u 1 - u 2) / √3 := by
      rw [eq_div_iff h3']; linear_combination e2 - e1
    have hb : Z 0 1 = (u 0 - 2 * u 1 - 2 * u 2) / 3 := by
      linear_combination (2 / 3) * e1 + (2 / 3) * e2 - (1 / 3) * e0
    have hd : Z 1 1 = (u 2 - u 1) / √3 := by rw [hZ11, ha]; ring
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [controlMatrix] using ha
    · simpa [controlMatrix] using hb
    · simpa [controlMatrix] using e0.symm
    · simpa [controlMatrix] using hd

/-- **Lemma 3.3.4** (`lem:sl2-star-condition`). For `X ∈ 𝔰𝔩₂(ℝ)`, the star inequalities hold if
and only if `⟨Z_u, X⟩ < 0` for all controls `u ∈ U_T`. -/
theorem lemma3_3_4 (X : Mat2) (hX : X.trace = 0) :
    (0 < ρ₀ X ∧ 0 < ρ₁ X ∧ 0 < ρ₂ X) ↔ ∀ u ∈ controlSimplex, traceForm (controlMatrix u) X < 0 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3' : √3 ≠ 0 := by positivity
  -- `⟨Z_u, X⟩ = -(2/√3)(ρ₂(X)u₀ + ρ₁(X)u₁ + ρ₀(X)u₂)`
  have key : ∀ u : Fin 3 → ℝ, traceForm (controlMatrix u) X =
      -(2 / √3) * (ρ₂ X * u 0 + ρ₁ X * u 1 + ρ₀ X * u 2) := by
    intro u
    have hX11 : X 1 1 = -X 0 0 := by
      rw [Matrix.trace_fin_two] at hX; linear_combination hX
    rw [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Fin.sum_univ_two]
    simp [controlMatrix, ρ₀, ρ₁, ρ₂, hX11]
    field_simp
    linear_combination (u 0 * X 1 0 + 3 * u 0 * X 0 1 - 2 * u 1 * X 1 0 - 2 * u 2 * X 1 0) * h3
  have h23 : 0 < 2 / √3 := by positivity
  constructor
  · -- the right-hand side is negative on `U_T` if all `ρ_j(X) > 0`
    rintro ⟨h0, h1, h2⟩ u ⟨hu, hsum⟩
    rw [key]
    set m := min (ρ₀ X) (min (ρ₁ X) (ρ₂ X))
    have hm : 0 < m := lt_min h0 (lt_min h1 h2)
    have hm0 : m ≤ ρ₀ X := min_le_left _ _
    have hm1 : m ≤ ρ₁ X := (min_le_right _ _).trans (min_le_left _ _)
    have hm2 : m ≤ ρ₂ X := (min_le_right _ _).trans (min_le_right _ _)
    have : 0 < ρ₂ X * u 0 + ρ₁ X * u 1 + ρ₀ X * u 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hm2 (hu 0).1,
        mul_le_mul_of_nonneg_right hm1 (hu 1).1, mul_le_mul_of_nonneg_right hm0 (hu 2).1]
    nlinarith
  · -- conversely, evaluate at the vertices of `U_T`
    intro h
    have hv : ∀ i : Fin 3, vertex i ∈ controlSimplex := by
      intro i
      refine ⟨fun k ↦ ?_, ?_⟩
      · by_cases hk : k = i
        · subst hk; simp [vertex]
        · simp [vertex, hk]
      · fin_cases i <;> simp [vertex]
    have e0 := h _ (hv 2)
    have e1 := h _ (hv 1)
    have e2 := h _ (hv 0)
    rw [key] at e0 e1 e2
    simp [vertex] at e0 e1 e2
    refine ⟨?_, ?_, ?_⟩ <;> nlinarith

end SmoothedPolygons
