module

public import SmoothedPolygons.Ch6.MatrixSystem
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Reinhardt trajectories and the matrix system (§3.5, §6.2)

The admissible pairs of the matrix system (`SmoothedPolygons/Ch6/MatrixSystem.lean`) that satisfy
its boundary condition `matrixEndpoints` are the admissible trajectories of the Reinhardt control
problem (Problem 3.6.2, TeX 3203), with the same cost:

* a Reinhardt state trajectory `(g, X)` is an admissible pair `t ↦ (g(t), X(t))` of the matrix
  system in `GL₂⁺(ℝ) × C` (`IsStateTrajectory.isAdmissibleIn_matrix`);
* along an admissible pair, `det g` and `det X` are constant (`det_stateG_eq_of_isAdmissibleIn`,
  `det_stateX_eq_of_isAdmissibleIn`): `(det g)' = det g · tr X = 0` and
  `(det X)' = -⟨X, [P, X]⟩ = 0`, for the absolutely continuous solutions of Carathéodory's sense;
* hence an admissible pair with `(q(0), q(t_f)) ∈ matrixEndpoints` is an admissible trajectory of
  Problem 3.6.2 (`isReinhardtAdmissible_of_mem_matrixEndpoints`): `g(t) ∈ SL₂(ℝ)`,
  `X(t)` is a star state, and the two boundary equations left out of `matrixBoundary` hold
  (`det g(t_f) = 1` with `R₀₀ = 1/2 ≠ 0`; `det X(t_f) = 1` with `X(t_f)₀₁ < 0`);
* the costs agree (`cost_matrixCost`), so a global minimizer of Problem 3.6.2 is a strong local
  minimizer of the matrix system (`IsReinhardtMinimizer.isStrongLocalMinimizer_matrix`).
-/

@[expose] public section

namespace SmoothedPolygons

open Set MeasureTheory Pontryagin ControlSystem Filter

/-- The cost of a pair of the matrix system is the Reinhardt cost of its `X`. -/
theorem cost_matrixCost (T : ℝ) (u : ℝ → Fin 3 → ℝ) (q : ℝ → MatrixState) :
    cost matrixCost T u q = reinhardtCost T (fun t ↦ stateX (q t)) := by
  simp [cost, matrixCost, reinhardtCost, intervalIntegral.integral_const_mul]

/-! ### Carathéodory curves

A curve in integral form `x(t) = x(0) + ∫₀ᵗ v` is absolutely continuous, has derivative `v(t)` at
almost every time (Lebesgue's differentiation theorem), and a `C¹` function of it is again
absolutely continuous; such a function with derivative `0` almost everywhere is constant. (The
first three facts are proved as in `SmoothedPolygons/Ch6/IwasawaChart.lean`, whose `iw_` lemmas
are copied here.) -/

section Caratheodory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- A curve in integral form `x(t) = x(0) + ∫₀ᵗ v` is continuous on `[0, T]`. -/
private lemma mxb_continuousOn_of_eq_add_integral {T : ℝ} (hT : 0 ≤ T) {x v : ℝ → E}
    (hv : IntervalIntegrable v volume 0 T)
    (hx : ∀ t ∈ Icc 0 T, x t = x 0 + ∫ s in (0 : ℝ)..t, v s) : ContinuousOn x (Icc 0 T) := by
  have hc := intervalIntegral.continuousOn_primitive_interval' hv left_mem_uIcc
  rw [uIcc_of_le hT] at hc
  exact (continuousOn_const.add hc).congr hx

/-- A curve in integral form `x(t) = x(0) + ∫₀ᵗ v` has derivative `v(t)` at almost every
`t ∈ (0, T)` (Lebesgue's differentiation theorem). -/
private lemma mxb_ae_hasDerivAt_of_eq_add_integral {T : ℝ} {x v : ℝ → E}
    (hv : IntervalIntegrable v volume 0 T)
    (hx : ∀ t ∈ Icc 0 T, x t = x 0 + ∫ s in (0 : ℝ)..t, v s) :
    ∀ᵐ t, t ∈ Ioo 0 T → HasDerivAt x (v t) t := by
  filter_upwards [IntervalIntegrable.ae_hasDerivAt_integral hv] with t ht htT
  have hT : 0 ≤ T := (htT.1.trans htT.2).le
  have h0 : (0 : ℝ) ∈ uIcc 0 T := left_mem_uIcc
  have htm : t ∈ uIcc 0 T := by rw [uIcc_of_le hT]; exact Ioo_subset_Icc_self htT
  have hd := (ht htm 0 h0).const_add (x 0)
  exact hd.congr_of_eventuallyEq
    (Filter.eventually_of_mem (Icc_mem_nhds htT.1 htT.2) fun s hs ↦ hx s hs)

/-- Absolute continuity by comparison: if `dist (f s) (f t) ≤ dist (g s) (g t)` on `[a, b]` and
`g` is absolutely continuous, so is `f`. -/
private lemma mxb_absolutelyContinuousOnInterval_of_dist_le {X : Type*} [PseudoMetricSpace X]
    {f : ℝ → X} {g : ℝ → ℝ} {a b : ℝ} (hg : AbsolutelyContinuousOnInterval g a b)
    (h : ∀ s ∈ uIcc a b, ∀ t ∈ uIcc a b, dist (f s) (f t) ≤ dist (g s) (g t)) :
    AbsolutelyContinuousOnInterval f a b := by
  apply squeeze_zero' ?_ ?_ hg
  · exact .of_forall fun _ ↦ Finset.sum_nonneg fun _ _ ↦ dist_nonneg
  rw [Filter.eventually_inf_principal]
  filter_upwards with E hE
  exact Finset.sum_le_sum fun i hi ↦ h _ (hE.left i hi).left _ (hE.left i hi).right

omit [CompleteSpace E] in
/-- If `F` is `C¹` and `x(t) = x(0) + ∫₀ᵗ v`, then `F ∘ x` is absolutely continuous on `[0, T]`:
`F` is Lipschitz on the compact set `x([0, T])`, and `‖x(t) - x(s)‖ ≤ |∫ₛᵗ ‖v‖|`. -/
private lemma mxb_absolutelyContinuousOnInterval_comp {F : E → ℝ} (hF : ContDiff ℝ 1 F)
    {T : ℝ} (hT : 0 ≤ T) {x v : ℝ → E} (hv : IntervalIntegrable v volume 0 T)
    (hx : ∀ t ∈ Icc 0 T, x t = x 0 + ∫ s in (0 : ℝ)..t, v s) :
    AbsolutelyContinuousOnInterval (fun t ↦ F (x t)) 0 T := by
  have hxc := mxb_continuousOn_of_eq_add_integral hT hv hx
  have hK : IsCompact (x '' Icc 0 T) := isCompact_Icc.image_of_continuousOn hxc
  have hloc : LocallyLipschitzOn (x '' Icc 0 T) F := by
    rintro _ ⟨t, -, rfl⟩
    obtain ⟨K, U, hU, hKU⟩ := hF.contDiffAt.exists_lipschitzOnWith
    exact ⟨K, U, nhdsWithin_le_nhds hU, hKU⟩
  obtain ⟨L, hL⟩ := hloc.exists_lipschitzOnWith_of_compact hK
  have hN := (hv.norm.absolutelyContinuousOnInterval_intervalIntegral
    (c := 0) left_mem_uIcc).const_mul (L : ℝ)
  refine mxb_absolutelyContinuousOnInterval_of_dist_le hN fun s hs t ht ↦ ?_
  rw [uIcc_of_le hT] at hs ht
  have hvs : IntervalIntegrable v volume 0 s := hv.mono_set (by
    rw [uIcc_of_le hT, uIcc_of_le hs.1]; exact Icc_subset_Icc_right hs.2)
  have hvt : IntervalIntegrable v volume 0 t := hv.mono_set (by
    rw [uIcc_of_le hT, uIcc_of_le ht.1]; exact Icc_subset_Icc_right ht.2)
  calc dist (F (x s)) (F (x t)) ≤ L * dist (x s) (x t) :=
        hL.dist_le_mul _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    _ = L * ‖∫ r in t..s, v r‖ := by
        rw [dist_eq_norm, hx s hs, hx t ht, add_sub_add_left_eq_sub,
          intervalIntegral.integral_interval_sub_left hvs hvt]
    _ ≤ L * |∫ r in t..s, ‖v r‖| := by
        gcongr; exact intervalIntegral.norm_integral_le_abs_integral_norm
    _ = dist (L * ∫ r in (0 : ℝ)..s, ‖v r‖) (L * ∫ r in (0 : ℝ)..t, ‖v r‖) := by
        rw [Real.dist_eq, ← mul_sub, abs_mul, NNReal.abs_eq,
          intervalIntegral.integral_interval_sub_left hvs.norm hvt.norm]

/-- **First integrals of Carathéodory curves.** If `F` is `C¹`, `x(t) = x(0) + ∫₀ᵗ v` on
`[0, T]`, and `F ∘ x` has derivative `0` wherever `x` has derivative `v`, then `F ∘ x` is constant
on `[0, T]` (`F ∘ x` is absolutely continuous with derivative `0` almost everywhere). -/
private lemma mxb_comp_eq_of_hasDerivAt_zero {F : E → ℝ} (hF : ContDiff ℝ 1 F) {T : ℝ}
    (hT : 0 ≤ T) {x v : ℝ → E} (hv : IntervalIntegrable v volume 0 T)
    (hx : ∀ t ∈ Icc 0 T, x t = x 0 + ∫ s in (0 : ℝ)..t, v s)
    (h0 : ∀ t, HasDerivAt x (v t) t → HasDerivAt (fun s ↦ F (x s)) 0 t) :
    ∀ t ∈ Icc 0 T, F (x t) = F (x 0) := by
  have hne0 : ∀ᵐ t : ℝ, t ≠ 0 := by simp [ae_iff, measure_singleton]
  have hneT : ∀ᵐ t : ℝ, t ≠ T := by simp [ae_iff, measure_singleton]
  have hac := mxb_absolutelyContinuousOnInterval_comp hF hT hv hx
  obtain ⟨C, hC⟩ := hac.const_of_ae_hasDerivAt_zero (by
      filter_upwards [mxb_ae_hasDerivAt_of_eq_add_integral hv hx, hne0, hneT] with t ht h1 h2 htm
      rw [uIcc_of_le hT] at htm
      exact h0 t (ht ⟨lt_of_le_of_ne htm.1 (Ne.symm h1), lt_of_le_of_ne htm.2 h2⟩))
  intro t ht
  rw [hC t (by rw [uIcc_of_le hT]; exact ht), hC 0 left_mem_uIcc]

/-- A continuous linear image of a curve in integral form is in integral form. -/
private lemma mxb_clm_eq_add_integral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (L : E →L[ℝ] F) {T : ℝ} (hT : 0 ≤ T) {x v : ℝ → E}
    (hv : IntervalIntegrable v volume 0 T)
    (hx : ∀ t ∈ Icc 0 T, x t = x 0 + ∫ s in (0 : ℝ)..t, v s) :
    IntervalIntegrable (fun s ↦ L (v s)) volume 0 T ∧
      ∀ t ∈ Icc 0 T, L (x t) = L (x 0) + ∫ s in (0 : ℝ)..t, L (v s) := by
  refine ⟨⟨L.integrable_comp hv.1, L.integrable_comp hv.2⟩, fun t ht ↦ ?_⟩
  have hvt : IntervalIntegrable v volume 0 t := hv.mono_set (by
    rw [uIcc_of_le hT, uIcc_of_le ht.1]; exact Icc_subset_Icc_right ht.2)
  rw [hx t ht, map_add, L.intervalIntegral_comp_comm hvt]

end Caratheodory

/-! ### Coordinates of the state space -/

/-- The entry `g_{ij}` of a state, as a continuous linear map. -/
private noncomputable def mxb_gCoord (i j : Fin 2) : MatrixState →L[ℝ] ℝ :=
  ((ContinuousLinearMap.proj j : (Fin 2 → ℝ) →L[ℝ] ℝ).comp
    (ContinuousLinearMap.proj i : (Fin 2 → Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ))).comp
    (ContinuousLinearMap.fst ℝ (Fin 2 → Fin 2 → ℝ) (Fin 3 → ℝ))

/-- The coordinate `x_k` of the Lie-algebra variable of a state, as a continuous linear map. -/
private noncomputable def mxb_xCoord (k : Fin 3) : MatrixState →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj k : (Fin 3 → ℝ) →L[ℝ] ℝ).comp
    (ContinuousLinearMap.snd ℝ (Fin 2 → Fin 2 → ℝ) (Fin 3 → ℝ))

private lemma mxb_gCoord_apply (i j : Fin 2) (q : MatrixState) : mxb_gCoord i j q = q.1 i j :=
  rfl

private lemma mxb_xCoord_apply (k : Fin 3) (q : MatrixState) : mxb_xCoord k q = q.2 k := rfl

/-- A curve in `MatrixState` is in integral form if its coordinates are. -/
private lemma mxb_eq_add_integral_of_coords {T : ℝ} (hT : 0 ≤ T) {x v : ℝ → MatrixState}
    (hg : ∀ i j, IntervalIntegrable (fun s ↦ (v s).1 i j) volume 0 T ∧
      ∀ t ∈ Icc 0 T, (x t).1 i j = (x 0).1 i j + ∫ s in (0 : ℝ)..t, (v s).1 i j)
    (hX : ∀ k, IntervalIntegrable (fun s ↦ (v s).2 k) volume 0 T ∧
      ∀ t ∈ Icc 0 T, (x t).2 k = (x 0).2 k + ∫ s in (0 : ℝ)..t, (v s).2 k) :
    IntervalIntegrable v volume 0 T ∧ ∀ t ∈ Icc 0 T, x t = x 0 + ∫ s in (0 : ℝ)..t, v s := by
  have hv : IntervalIntegrable v volume 0 T :=
    ⟨(Integrable.of_eval fun i ↦ Integrable.of_eval fun j ↦ (hg i j).1.1).prodMk
        (Integrable.of_eval fun k ↦ (hX k).1.1),
      (Integrable.of_eval fun i ↦ Integrable.of_eval fun j ↦ (hg i j).1.2).prodMk
        (Integrable.of_eval fun k ↦ (hX k).1.2)⟩
  refine ⟨hv, fun t ht ↦ ?_⟩
  have hvt : IntervalIntegrable v volume 0 t := hv.mono_set (by
    rw [uIcc_of_le hT, uIcc_of_le ht.1]; exact Icc_subset_Icc_right ht.2)
  refine Prod.ext (funext fun i ↦ funext fun j ↦ ?_) (funext fun k ↦ ?_)
  · have e := (mxb_gCoord i j).intervalIntegral_comp_comm hvt
    simp only [mxb_gCoord_apply] at e
    rw [(hg i j).2 t ht, e]
    rfl
  · have e := (mxb_xCoord k).intervalIntegral_comp_comm hvt
    simp only [mxb_xCoord_apply] at e
    rw [(hX k).2 t ht, e]
    rfl

/-- The entries of `X = slMatrix x` and of `[P, X]` are coordinates of the state and of the
matrix field (the entry `(1, 1)` of the commutator is minus its entry `(0, 0)`). -/
private lemma mxb_stateX_coord (i j : Fin 2) : ∃ L : MatrixState →L[ℝ] ℝ,
    (∀ q, stateX q i j = L q) ∧ ∀ q u, (controlP u (stateX q) * stateX q -
      stateX q * controlP u (stateX q)) i j = L (matrixField q u) := by
  fin_cases i <;> fin_cases j
  · exact ⟨mxb_xCoord 0, fun q ↦ rfl, fun q u ↦ rfl⟩
  · exact ⟨mxb_xCoord 1, fun q ↦ rfl, fun q u ↦ rfl⟩
  · exact ⟨mxb_xCoord 2, fun q ↦ rfl, fun q u ↦ rfl⟩
  · refine ⟨-mxb_xCoord 0, fun q ↦ rfl, fun q u ↦ ?_⟩
    change (controlP u (stateX q) * stateX q - stateX q * controlP u (stateX q)) 1 1 =
      -(slCoords (controlP u (stateX q) * stateX q - stateX q * controlP u (stateX q)) 0)
    simp only [slCoords]
    generalize controlP u (stateX q) = P
    generalize stateX q = Y
    simp only [Matrix.cons_val_zero, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]
    ring

/-- Where a curve `q` of states has derivative `w`, its matrix `g` has derivative `stateG w`. -/
private lemma mxb_hasDerivAtEntrywise_stateG {q : ℝ → MatrixState} {w : MatrixState} {t : ℝ}
    (hd : HasDerivAt q w t) : Matrix.HasDerivAtEntrywise (fun s ↦ stateG (q s)) (stateG w) t := by
  intro i j
  have := (mxb_gCoord i j).hasFDerivAt.comp_hasDerivAt t hd
  simp only [Function.comp_def, mxb_gCoord_apply] at this
  exact this

/-- Where a curve `q` of states has derivative `f(q(t), u)` (the matrix field), its matrix `X`
has derivative `[P, X]`. -/
private lemma mxb_hasDerivAtEntrywise_stateX {q : ℝ → MatrixState} {u : Fin 3 → ℝ} {t : ℝ}
    (hd : HasDerivAt q (matrixField (q t) u) t) :
    Matrix.HasDerivAtEntrywise (fun s ↦ stateX (q s))
      (controlP u (stateX (q t)) * stateX (q t) - stateX (q t) * controlP u (stateX (q t))) t := by
  intro i j
  obtain ⟨L, hL1, hL2⟩ := mxb_stateX_coord i j
  have := L.hasFDerivAt.comp_hasDerivAt t hd
  rw [← hL2] at this
  convert this using 1
  funext s
  exact hL1 (q s)

/-- `⟨X, [P, X]⟩ = tr(XPX) - tr(XXP) = 0`. -/
private lemma mxb_traceForm_commutator (P X : Mat2) : traceForm X (P * X - X * P) = 0 := by
  rw [traceForm, Matrix.mul_sub, Matrix.trace_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.trace_mul_cycle, sub_self]

/-- A Reinhardt state trajectory is an admissible pair of the matrix system in `GL₂⁺(ℝ) × C`
(the entrywise integral equations of `IsStateTrajectory` are the integral equation of the pair;
`det g = 1 > 0`, and the star conditions put `X` in `C`). -/
theorem IsStateTrajectory.isAdmissibleIn_matrix {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsStateTrajectory T u g X) :
    IsAdmissibleIn matrixField matrixDomain controlSimplex (toMatrixState (g 0) (X 0)) T u
      (fun t ↦ toMatrixState (g t) (X t)) := by
  obtain ⟨hT, hmeas, hU, hstate, hgI, hXI⟩ := h
  have hXq : ∀ t ∈ Icc 0 T, stateX (toMatrixState (g t) (X t)) = X t := fun t ht ↦
    stateX_toMatrixState _ (hstate t ht).2.1
  -- the matrix field along the pair: `(gX, slCoords [P, X])`
  have hv : ∀ s ∈ Icc 0 T, matrixField (toMatrixState (g s) (X s)) (u s) =
      (fun i j ↦ (g s * X s) i j,
        slCoords (controlP (u s) (X s) * X s - X s * controlP (u s) (X s))) := by
    intro s hs
    simp only [matrixField, hXq s hs, stateG_toMatrixState]
  -- the coordinates of `slCoords M` are entries of `M`
  have hsl : ∀ k : Fin 3, ∃ a b : Fin 2, ∀ M : Mat2, slCoords M k = M a b := by
    intro k
    fin_cases k
    exacts [⟨0, 0, fun _ ↦ rfl⟩, ⟨0, 1, fun _ ↦ rfl⟩, ⟨1, 0, fun _ ↦ rfl⟩]
  have hint := mxb_eq_add_integral_of_coords (x := fun t ↦ toMatrixState (g t) (X t))
    (v := fun s ↦ matrixField (toMatrixState (g s) (X s)) (u s)) hT.le ?_ ?_
  · refine ⟨⟨hmeas, hU, mxb_continuousOn_of_eq_add_integral hT.le hint.1 hint.2, hint.1,
      hint.2⟩, fun t ht ↦ ?_⟩
    obtain ⟨hdet, -, -, h0, h1, h2⟩ := hstate t ht
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [stateG_toMatrixState, hdet]; exact one_pos
    · rw [hXq t ht]; exact h0
    · rw [hXq t ht]; exact h1
    · rw [hXq t ht]; exact h2
  · intro i j
    refine ⟨(intervalIntegrable_congr fun s hs ↦ ?_).2 (hgI i j).1, fun t ht ↦ ?_⟩
    · rw [uIoc_of_le hT.le] at hs
      simp only [hv s (Ioc_subset_Icc_self hs)]
    · change g t i j = g 0 i j + _
      rw [(hgI i j).2 t ht]
      congr 1
      refine intervalIntegral.integral_congr fun s hs ↦ ?_
      rw [uIcc_of_le ht.1] at hs
      simp only [hv s ⟨hs.1, hs.2.trans ht.2⟩]
  · intro k
    obtain ⟨a, b, hab⟩ := hsl k
    refine ⟨(intervalIntegrable_congr fun s hs ↦ ?_).2 (hXI a b).1, fun t ht ↦ ?_⟩
    · rw [uIoc_of_le hT.le] at hs
      simp only [hv s (Ioc_subset_Icc_self hs), hab]
    · change slCoords (X t) k = slCoords (X 0) k + _
      rw [hab, hab, (hXI a b).2 t ht]
      congr 1
      refine intervalIntegral.integral_congr fun s hs ↦ ?_
      rw [uIcc_of_le ht.1] at hs
      simp only [hv s ⟨hs.1, hs.2.trans ht.2⟩, hab]

/-- **`det g` is a first integral**: along an admissible pair of the matrix system,
`(det g)' = det g · tr X = 0`. -/
theorem det_stateG_eq_of_isAdmissibleIn {T : ℝ} (hT : 0 ≤ T) {u : ℝ → Fin 3 → ℝ}
    {q : ℝ → MatrixState} (h : IsAdmissibleIn matrixField matrixDomain controlSimplex (q 0) T u q) :
    ∀ t ∈ Icc 0 T, (stateG (q t)).det = (stateG (q 0)).det := by
  obtain ⟨⟨-, -, -, hint, heq⟩, -⟩ := h
  have hF : ContDiff ℝ 1 fun q : MatrixState ↦ (stateG q).det := by
    have e : (fun q : MatrixState ↦ (stateG q).det) = fun q ↦
        mxb_gCoord 0 0 q * mxb_gCoord 1 1 q - mxb_gCoord 0 1 q * mxb_gCoord 1 0 q := by
      funext q; simp [stateG, Matrix.det_fin_two, mxb_gCoord_apply]
    rw [e]
    fun_prop
  refine mxb_comp_eq_of_hasDerivAt_zero hF hT hint heq fun t hd ↦ ?_
  -- Jacobi's formula for `2 × 2` matrices: `(det g)' = det g · tr(g⁻¹g') = det g · tr X`
  have hJ : HasDerivAt (fun s ↦ (stateG (q s)).det)
      ((stateG (q t)).det * (stateX (q t)).trace) t := by
    convert (mxb_hasDerivAtEntrywise_stateG hd).det_fin_two using 1
    simp only [stateG, matrixField, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_two]
    simp [stateX, slMatrix, Matrix.det_fin_two, Matrix.trace_fin_two]
    ring
  have htr : (stateX (q t)).trace = 0 := trace_slMatrix _
  rwa [htr, mul_zero] at hJ

/-- **`det X` is a first integral**: along an admissible pair of the matrix system,
`(det X)' = -⟨X, X'⟩ = -⟨X, [P, X]⟩ = 0` (`X' = [P, X]` is isospectral). -/
theorem det_stateX_eq_of_isAdmissibleIn {T : ℝ} (hT : 0 ≤ T) {u : ℝ → Fin 3 → ℝ}
    {q : ℝ → MatrixState} (h : IsAdmissibleIn matrixField matrixDomain controlSimplex (q 0) T u q) :
    ∀ t ∈ Icc 0 T, (stateX (q t)).det = (stateX (q 0)).det := by
  obtain ⟨⟨-, -, -, hint, heq⟩, -⟩ := h
  have hF : ContDiff ℝ 1 fun q : MatrixState ↦ (stateX q).det := by
    have e : (fun q : MatrixState ↦ (stateX q).det) = fun q ↦
        mxb_xCoord 0 q * -mxb_xCoord 0 q - mxb_xCoord 1 q * mxb_xCoord 2 q := by
      funext q; simp [stateX, slMatrix, Matrix.det_fin_two, mxb_xCoord_apply]
    rw [e]
    fun_prop
  refine mxb_comp_eq_of_hasDerivAt_zero hF hT hint heq fun t hd ↦ ?_
  -- for traceless `X` and `X' = [P, X]`, `(det X)' = -⟨X, X'⟩`, and `⟨X, [P, X]⟩ = 0`
  have hJ : HasDerivAt (fun s ↦ (stateX (q s)).det)
      (-traceForm (stateX (q t)) (controlP (u t) (stateX (q t)) * stateX (q t) -
        stateX (q t) * controlP (u t) (stateX (q t)))) t := by
    convert (mxb_hasDerivAtEntrywise_stateX hd).det_fin_two using 1
    simp only [traceForm]
    generalize controlP (u t) (stateX (q t)) = P
    simp only [Matrix.trace_fin_two, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]
    simp [stateX, slMatrix]
    ring
  rwa [mxb_traceForm_commutator, neg_zero] at hJ

/-- An admissible pair of the matrix system with `det g(0) = 1` and `det X(0) = 1` projects to a
Reinhardt state trajectory (the first integrals keep `g` in `SL₂(ℝ)` and `X` among the star
states). -/
theorem isStateTrajectory_of_isAdmissibleIn_matrix {T : ℝ} (hT : 0 < T) {u : ℝ → Fin 3 → ℝ}
    {q : ℝ → MatrixState} (h : IsAdmissibleIn matrixField matrixDomain controlSimplex (q 0) T u q)
    (hg : (stateG (q 0)).det = 1) (hX : (stateX (q 0)).det = 1) :
    IsStateTrajectory T u (fun t ↦ stateG (q t)) (fun t ↦ stateX (q t)) := by
  have hdg := det_stateG_eq_of_isAdmissibleIn hT.le h
  have hdX := det_stateX_eq_of_isAdmissibleIn hT.le h
  obtain ⟨⟨hmeas, hU, -, hint, heq⟩, hdom⟩ := h
  refine ⟨hT, hmeas, hU, fun t ht ↦ ⟨by rw [hdg t ht, hg], trace_slMatrix _,
    by rw [hdX t ht, hX], (hdom t ht).2.1, (hdom t ht).2.2.1, (hdom t ht).2.2.2⟩, ?_, ?_⟩
  -- `g' = gX`: the entries of `g` are coordinates of the state
  · intro i j
    have := mxb_clm_eq_add_integral (mxb_gCoord i j) hT.le hint heq
    simp only [mxb_gCoord_apply] at this
    exact this
  -- `X' = [P, X]`: the entries of `X` are coordinates (or minus a coordinate) of the state
  · intro i j
    obtain ⟨L, hL1, hL2⟩ := mxb_stateX_coord i j
    simp only [hL1, hL2]
    exact mxb_clm_eq_add_integral L hT.le hint heq

/-- **Competitors are Reinhardt-admissible**: an admissible pair of the matrix system satisfying
the boundary condition `matrixEndpoints` projects to an admissible trajectory of Problem 3.6.2.
The two boundary equations left out of `matrixBoundary` hold: `det g(t_f) = 1` and
`g(t_f)₀₀ = R₀₀ = 1/2 ≠ 0` give `g(t_f)₁₁ = R₁₁`; `det X(t_f) = 1 = det(R⁻¹X(0)R)` and
`X(t_f)₀₁ < 0` (on `C`: `ρ₀ + ρ₁ > 0` gives `X₁₀ > 0`, and `ρ₂ > 0` gives `3X₀₁ + X₁₀ < 0`) give
`X(t_f)₁₀ = -(1 + X(t_f)₀₀²)/X(t_f)₀₁ = (R⁻¹X(0)R)₁₀`. -/
theorem isReinhardtAdmissible_of_mem_matrixEndpoints {T : ℝ} (hT : 0 < T) {u : ℝ → Fin 3 → ℝ}
    {q : ℝ → MatrixState} (h : IsAdmissibleIn matrixField matrixDomain controlSimplex (q 0) T u q)
    (hN : (q 0, q T) ∈ matrixEndpoints) :
    IsReinhardtAdmissible T u (fun t ↦ stateG (q t)) (fun t ↦ stateX (q t)) := by
  have hb : matrixBoundary (q 0, q T) = 0 := hN
  simp only [matrixBoundary, Prod.mk_eq_zero] at hb
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
  have hTm : T ∈ Icc 0 T := ⟨hT.le, le_rfl⟩
  -- `g(0) = I₂`, `det X(0) = 1`
  have hg0 : stateG (q 0) = 1 := by
    ext i j
    have := congrFun (congrFun hb1 i) j
    simpa [sub_eq_zero] using this
  have hX0 : (stateX (q 0)).det = 1 := by linarith
  have hst := isStateTrajectory_of_isAdmissibleIn_matrix hT h (by rw [hg0, Matrix.det_one]) hX0
  refine ⟨hst, hg0, ?_, ?_⟩
  -- `g(t_f) = R`: three entries from the boundary condition, the fourth from `det g(t_f) = 1`
  · have e0 := congrFun hb2 0
    have e1 := congrFun hb2 1
    have e2 := congrFun hb2 2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Pi.zero_apply,
      sub_eq_zero, Matrix.head_cons, Matrix.tail_cons] at e0 e1 e2
    have h11 : stateG (q T) 1 1 = R 1 1 := by
      have hdet := (hst.2.2.2.1 T hTm).1
      have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
      simp only [Matrix.det_fin_two] at hdet
      rw [e0, e1, e2] at hdet
      simp only [R, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one] at hdet ⊢
      linear_combination 2 * hdet - h3 / 2
    ext i j
    fin_cases i <;> fin_cases j
    exacts [e0, e1, e2, h11]
  -- `X(t_f) = R⁻¹X(0)R`: two entries from the boundary condition, the entry `(1, 1)` from
  -- `tr = 0`, the entry `(1, 0)` from `det X(t_f) = 1 = det(R⁻¹X(0)R)` and `X(t_f)₀₁ < 0`
  · set M := R⁻¹ * stateX (q 0) * R with hM
    have htrM : M.trace = 0 := by
      rw [hM, Matrix.trace_mul_cycle, mx_R_mul_R_inv, Matrix.one_mul]
      exact trace_slMatrix _
    have hdetM : M.det = 1 := by
      rw [hM, Matrix.det_mul, Matrix.det_mul, mul_comm (R⁻¹.det), mul_assoc, ← Matrix.det_mul,
        mx_R_inv_mul_R, Matrix.det_one, mul_one, hX0]
    have e0 := congrFun hb4 0
    have e1 := congrFun hb4 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, sub_eq_zero,
      Matrix.cons_val_fin_one] at e0 e1
    have hdet := (hst.2.2.2.1 T hTm).2.2.1
    have hneg := stateX_zero_one_neg (h.2 T hTm)
    rw [Matrix.trace_fin_two] at htrM
    rw [Matrix.det_fin_two] at hdetM
    simp only [Matrix.det_fin_two] at hdet
    have h11 : stateX (q T) 1 1 = -stateX (q T) 0 0 := by simp [stateX, slMatrix]
    have h10 : stateX (q T) 1 0 = M 1 0 := by
      refine mul_left_cancel₀ hneg.ne ?_
      rw [e1] at hneg ⊢
      rw [h11, e0, e1] at hdet
      linear_combination -hdet + hdetM - M 0 0 * htrM
    ext i j
    fin_cases i <;> fin_cases j
    · exact e0
    · exact e1
    · exact h10
    · change stateX (q T) 1 1 = M 1 1
      rw [h11, e0]
      linarith

/-- **A Reinhardt minimizer is a strong local minimizer of the matrix system**: the pair
`t ↦ (g(t), X(t))` satisfies the boundary condition `matrixEndpoints`, and every competitor
projects to an admissible trajectory of Problem 3.6.2 with the same cost
(`isReinhardtAdmissible_of_mem_matrixEndpoints`, `cost_matrixCost`), so it minimizes the cost
among all of them. -/
theorem IsReinhardtMinimizer.isStrongLocalMinimizer_matrix {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X : ℝ → Mat2} (h : IsReinhardtMinimizer T u g X) :
    IsStrongLocalMinimizer matrixField matrixCost matrixDomain controlSimplex matrixEndpoints T u
      (fun t ↦ toMatrixState (g t) (X t)) := by
  obtain ⟨⟨hst, hg0, hgT, hXT⟩, hmin⟩ := h
  have hT : 0 < T := hst.1
  have h0m : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hTm : T ∈ Icc 0 T := ⟨hT.le, le_rfl⟩
  have hXq : ∀ t ∈ Icc 0 T, stateX (toMatrixState (g t) (X t)) = X t := fun t ht ↦
    stateX_toMatrixState _ (hst.2.2.2.1 t ht).2.1
  refine ⟨hT, hst.isAdmissibleIn_matrix, ?_, 1, one_pos, ?_⟩
  -- the boundary condition
  · change matrixBoundary (toMatrixState (g 0) (X 0), toMatrixState (g T) (X T)) = 0
    simp only [matrixBoundary, stateG_toMatrixState, hXq 0 h0m, hXq T hTm]
    rw [hg0, hgT, hXT, (hst.2.2.2.1 0 h0m).2.2.1]
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
    · funext i j; simp
    · funext k; fin_cases k <;> simp
    · simp
    · funext k; fin_cases k <;> simp
  -- a competitor projects to an admissible trajectory of Problem 3.6.2 with the same cost
  · intro T' u' q' hT' hadm' hbd _ _
    rw [cost_matrixCost, cost_matrixCost]
    calc reinhardtCost T (fun t ↦ stateX (toMatrixState (g t) (X t))) = reinhardtCost T X := by
          simp only [reinhardtCost]
          congr 1
          refine intervalIntegral.integral_congr fun t ht ↦ ?_
          rw [uIcc_of_le hT.le] at ht
          simp only [hXq t ht]
      _ ≤ _ := hmin T' u' _ _ (isReinhardtAdmissible_of_mem_matrixEndpoints hT' hadm' hbd)

end SmoothedPolygons
