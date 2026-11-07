module

public import SmoothedPolygons.Ch7.Isolated.VertexFlow
public import SmoothedPolygons.Ch7.Isolated.Switching
public import SmoothedPolygons.Ch7.Isolated.IpcFlow
public import SmoothedPolygons.Ch7.Isolated.IpcAlgebra
public import SmoothedPolygons.Ch7.HMax
public import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain

/-!
# Theorem 7.7.1, step 4: the Poincaré map

The points `q_fix(y₀)` lie on the section, their Poincaré time is `t_sw(y₀)` and they are fixed
points of the Poincaré map; the Poincaré map is strictly differentiable at the octagon's point,
and its derivative maps the basis `iso_sectionBasis` of the section's tangent space by the explicit
matrix `iso_sectionMatrix` (the book's "direct calculation", used in step 5).

## Strict differentiability (`iso_poincareMapCoords_hasStrictFDerivAt`)

Near `q_fix(y₀)` the vertex flow equals its integral-free closed form `ipc_cf`
(`SmoothedPolygons.Ch7.Isolated.IpcFlow`), which is `C¹` in `(v, t)` (`ipc_CD_cf`: the matrix
exponential is analytic). So `G(v, t) = χ₃₁(q(t, q(v)))` and `F(v, t) = Ad(R) q(t, q(v))` are
strictly differentiable at `(v₀, t_sw)`, with `∂_t G = -iso_chi32Slope y₀ ≠ 0`
(`iso_chi31_hasDerivAt`, `iso_chi32Slope_pos`). The implicit function theorem
(`HasStrictFDerivAt.implicitFunctionOfProdDomain`) gives a zero `ψ` of `G` near `v₀`, strictly
differentiable at `v₀`; it is the *first* positive zero (`iso_poincareTime`) near `v₀`, because
`χ₃₁ > 0` on `[0, t_sw - ε/2]` along the octagon's arc (Lemma 7.5.3), hence near `v₀` uniformly
by compactness (`IsCompact.eventually_forall_of_forall_eventually`), and the zeros near `t_sw`
are exactly `ψ v` (`ipc_poincareTime_ift`). Then `f(v) = F(v, ψ v)` near `v₀`, so `f` is strictly
differentiable at `v₀` (this is all that is proved: not that `f` is `C¹` near `v₀`).

## The direct calculation (`iso_fderiv_basis`)

The book does not give it. With `Df = F' ∘ (id, ψ')` and `G' ∘ (id, ψ') = 0`
(`ipc_fderiv_structure`, `ipc_fderiv_apply`), `Df` is computed on the basis in three kinds of
directions, which avoids differentiating the flow in `X₀`:
* the tangent `ipc_Fam` of the curve `y₀ ↦ q_fix(y₀)` of fixed points: `Df(Fam) = Fam`
  (`ipc_fderiv_Fam`, from `iso_poincareMap_qFix`);
* the vector field `ipc_Vq` at `q_oct`: `Df(Vq) = 0` (`ipc_fderiv_Vq`), since the Poincaré map is
  constant along the octagon's arc (`ipc_poincareMap_flow_octagon`, from `iso_arc_eq_vertexFlow`
  applied to the octagon's lifted extremal and Lemma 7.5.3);
* the costate directions (zero `X`-part), where the flow is affine in `(Λ₁(0), Λ_R(0))`
  (`ipc_cf_add_smul`), so `F'(w, 0)` and `G'(w, 0)` are explicit (`ipc_dir_costate`, from the
  closed forms of `SmoothedPolygons.Ch7.Isolated.IpcOctagon`).
The basis vectors decompose along these directions and the resulting columns are those of
`iso_sectionMatrix` (`SmoothedPolygons.Ch7.Isolated.IpcAlgebra`): identities of rational
functions in `(y₀, ℓ, √3)`, `ℓ = ln(4/(3y₀² + 1))`. This is the scratch computation of the plan
organized differently (the plan differentiates the closed-form flow in all nine directions).
-/

@[expose] public section

namespace SmoothedPolygons

open Matrix Set Filter Topology MeasureTheory

/-! ### Step 4: the Poincaré map -/

/-- `q_fix(y₀)` lies on the section (Theorem 7.5.1: `Λ_R(0) ⊥ X(0)`, `χ₂₃(0) = 0`, `H = 0`). -/
theorem iso_qFix_isSectionPt (y0 : ℝ) (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) :
    iso_IsSectionPt (iso_qFix y0) := by
  have hy : 0 < y0 := poly_y0_pos hy0
  obtain ⟨htr, -, -, hperp, hchi23, hH, -, -, -⟩ := strongLift_isStrongLift y0 hy0
  have h0 : (0 : ℝ) ∈ Icc 0 (switchTime y0) := ⟨le_rfl, (str_switchTime_pos y0 hy0 hy1).le⟩
  rw [str_segX_zero y0 hy] at hperp hchi23 hH
  refine ⟨by simp [iso_qFix, Φ, Matrix.trace_fin_two], (htr 0 h0).1, (htr 0 h0).2, ?_, ?_, hH,
    hchi23⟩
  · simp only [iso_qFix, Φ, Matrix.det_fin_two_of]
    field_simp
    ring
  · rw [poly_traceForm_comm]
    exact hperp

/-- The Poincaré time of `q_fix(y₀)` is `t_sw(y₀)`: by Lemma 7.5.3, `χ₃₁ > 0` on `[0, t_sw)` and
`χ₃₁(t_sw) = 0`. -/
theorem iso_poincareTime_qFix (y0 : ℝ) (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) :
    iso_poincareTime (iso_qFix y0) = switchTime y0 := by
  have hτ := str_switchTime_pos y0 hy0 hy1
  have hχ := lemma7_5_3 y0 hy0 hy1 _ _ (strongLift_isStrongLift y0 hy0)
  obtain ⟨-, -, -, -, -, -, hchi31, -, -⟩ := strongLift_isStrongLift y0 hy0
  refine IsLeast.csInf_eq ⟨⟨hτ, ?_⟩, fun t ht ↦ ?_⟩
  · rw [iso_vertexFlow_qFix y0 hy0]
    exact hchi31
  · obtain ⟨ht0, ht⟩ := ht
    rw [iso_vertexFlow_qFix y0 hy0] at ht
    refine le_of_not_gt fun hlt ↦ ?_
    exact hlt.ne ((hχ t ⟨ht0.le, hlt.le⟩).2.2.1 ht)

/-- Every `q_fix(y₀)` is a fixed point of the Poincaré map: the strong transversality conditions
of Theorem 7.5.1 and `X(z₀, t_sw) = R⁻¹ X₀ R` (`segX_switchTime`). -/
theorem iso_poincareMap_qFix (y0 : ℝ) (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) :
    iso_poincareMap (iso_qFix y0) = iso_qFix y0 := by
  obtain ⟨-, -, -, -, -, -, -, hR, h1⟩ := strongLift_isStrongLift y0 hy0
  have hc : ∀ A : Mat2, R * (R⁻¹ * A * R) * R⁻¹ = A := fun A ↦ by
    rw [← mul_assoc, ← mul_assoc, poly_R_mul_inv, one_mul, mul_assoc, poly_R_mul_inv, mul_one]
  rw [iso_poincareMap, iso_poincareTime_qFix y0 hy0 hy1, iso_vertexFlow_qFix y0 hy0, iso_adR]
  simp only [segX_switchTime y0 hy0, hR, h1, hc, iso_qFix]


/-! ### Step 4: the implicit function theorem for the Poincaré time -/

/-- The coordinates of `q_fix(y₀)`. -/
noncomputable def ipc_v0 (y : ℝ) : Fin 9 → ℝ := iso_phaseCoords (iso_qFix y)

lemma ipc_phaseOfCoords_phaseCoords (q : iso_PhasePt) (h1 : q.1.trace = 0) (h2 : q.2.1.trace = 0)
    (h3 : q.2.2.trace = 0) : iso_phaseOfCoords (iso_phaseCoords q) = q := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · conv_rhs => rw [ipc_eta h1]
    simp [iso_phaseOfCoords, iso_phaseCoords]
  · conv_rhs => rw [ipc_eta h2]
    simp [iso_phaseOfCoords, iso_phaseCoords]
  · conv_rhs => rw [ipc_eta h3]
    simp [iso_phaseOfCoords, iso_phaseCoords]

lemma ipc_phaseOfCoords_v0 (y : ℝ) (hy0 : 1 / √3 < y) (hy1 : y < 1) :
    iso_phaseOfCoords (ipc_v0 y) = iso_qFix y := by
  obtain ⟨h1, h2, h3, -⟩ := iso_qFix_isSectionPt y hy0 hy1
  exact ipc_phaseOfCoords_phaseCoords _ h1 h2 h3

lemma ipc_trace_phaseOfCoords (v : Fin 9 → ℝ) :
    (iso_phaseOfCoords v).1.trace = 0 ∧ (iso_phaseOfCoords v).2.1.trace = 0 ∧
      (iso_phaseOfCoords v).2.2.trace = 0 := by
  simp [iso_phaseOfCoords, Matrix.trace_fin_two]

lemma ipc_good_v0 (y : ℝ) (hy0 : 1 / √3 < y) (hy1 : y < 1) : ipc_Good (ipc_v0 y) := by
  have hy : 0 < y := poly_y0_pos hy0
  have h3 : (0 : ℝ) < √3 := by positivity
  rw [ipc_Good, ipc_phaseOfCoords_v0 y hy0 hy1]
  refine ⟨?_, ?_⟩
  · change traceForm (controlMatrix (vertex 2)) (Φ 0 y) ≠ 0
    rw [str_traceForm_Z3_Φ]
    simp [hy.ne']
  · have hY : ipc_Y (iso_qFix y) = !![√3 * y / 2, 0; 1 / y, -(√3 * y / 2)] := by
      change Φ 0 y + segP y = _
      rw [str_segP_eq y hy.ne']
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Φ]
      field_simp
      ring
    have e : traceForm !![√3 * y / 2, 0; 1 / y, -(√3 * y / 2)]
        !![√3 * y / 2, 0; 1 / y, -(√3 * y / 2)] = 3 * y ^ 2 / 2 := by
      simp [traceForm, Matrix.trace_fin_two]
      ring_nf
      rw [str_sqrt3_sq]; ring
    rw [hY, e]; positivity

/-- The closed form is the flow near `q_fix(y₀)`. -/
lemma ipc_good_nhds (y : ℝ) (hy0 : 1 / √3 < y) (hy1 : y < 1) :
    ∀ᶠ v in 𝓝 (ipc_v0 y), ipc_Good v := by
  obtain ⟨hc, hY⟩ := ipc_good_v0 y hy0 hy1
  have hi : Continuous fun v : Fin 9 → ℝ ↦ ((v, (0 : ℝ)) : ipc_E) :=
    continuous_id.prodMk continuous_const
  have h1 : ContinuousAt (fun v : Fin 9 → ℝ ↦
      traceForm (controlMatrix (vertex 2)) (iso_phaseOfCoords v).1) (ipc_v0 y) :=
    (((ipc_CD.const _ ((ipc_v0 y, 0) : ipc_E)).tf (ipc_CD_X _)).continuousAt).comp
      (f := fun v : Fin 9 → ℝ ↦ ((v, (0 : ℝ)) : ipc_E)) hi.continuousAt
  have h2 : ContinuousAt (fun v : Fin 9 → ℝ ↦
      traceForm (ipc_Y (iso_phaseOfCoords v)) (ipc_Y (iso_phaseOfCoords v))) (ipc_v0 y) :=
    (((ipc_CD_Y ((ipc_v0 y, 0) : ipc_E) hc).tf (ipc_CD_Y _ hc)).continuousAt).comp
      (f := fun v : Fin 9 → ℝ ↦ ((v, (0 : ℝ)) : ipc_E)) hi.continuousAt
  filter_upwards [h1.eventually_ne hc, h2.eventually_ne hY] with v h1 h2 using ⟨h1, h2⟩

/-- `χ₃₁` along the `e₃`-flow from `q(v)`, as a function of `(v, t)`. -/
noncomputable def ipc_G (p : ipc_E) : ℝ :=
  switchingFn 2 0 (iso_vertexFlow 2 (iso_phaseOfCoords p.1) p.2).2.2
    (iso_vertexFlow 2 (iso_phaseOfCoords p.1) p.2).1

/-- `ipc_G` with the closed form of the flow. -/
noncomputable def ipc_Gcf (p : ipc_E) : ℝ :=
  switchingFn 2 0 (ipc_cf (iso_phaseOfCoords p.1) p.2).2.2 (ipc_cf (iso_phaseOfCoords p.1) p.2).1

/-- `Ad(R) q(t, q(v))` in coordinates, as a function of `(v, t)`. -/
noncomputable def ipc_F (p : ipc_E) : Fin 9 → ℝ :=
  iso_phaseCoords (iso_adR (iso_vertexFlow 2 (iso_phaseOfCoords p.1) p.2))

/-- `ipc_F` with the closed form of the flow. -/
noncomputable def ipc_Fcf (p : ipc_E) : Fin 9 → ℝ :=
  iso_phaseCoords (iso_adR (ipc_cf (iso_phaseOfCoords p.1) p.2))

lemma ipc_flow_eq_cf {v : Fin 9 → ℝ} (hv : ipc_Good v) (t : ℝ) :
    iso_vertexFlow 2 (iso_phaseOfCoords v) t = ipc_cf (iso_phaseOfCoords v) t :=
  ipc_vertexFlow_eq_cf _ (ipc_trace_phaseOfCoords v).1 (ipc_trace_phaseOfCoords v).2.1 hv.1 hv.2 t

lemma ipc_G_eventuallyEq (y : ℝ) (hy0 : 1 / √3 < y) (hy1 : y < 1) (t : ℝ) :
    ipc_G =ᶠ[𝓝 ((ipc_v0 y, t) : ipc_E)] ipc_Gcf := by
  filter_upwards [(ipc_good_nhds y hy0 hy1).prod_inl_nhds t] with p hp
  simp only [ipc_G, ipc_Gcf, ipc_flow_eq_cf hp]

lemma ipc_F_eventuallyEq (y : ℝ) (hy0 : 1 / √3 < y) (hy1 : y < 1) (t : ℝ) :
    ipc_F =ᶠ[𝓝 ((ipc_v0 y, t) : ipc_E)] ipc_Fcf := by
  filter_upwards [(ipc_good_nhds y hy0 hy1).prod_inl_nhds t] with p hp
  simp only [ipc_F, ipc_Fcf, ipc_flow_eq_cf hp]

lemma ipc_CD_controlP {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {X : E → Mat2} {x : E}
    (hX : ipc_CD X x) (u : Fin 3 → ℝ) (h : traceForm (controlMatrix u) (X x) ≠ 0) :
    ipc_CD (fun y ↦ controlP u (X y)) x :=
  ipc_CD.smul (((ipc_CD.const _ x).tf hX).inv h) (ipc_CD.const _ x)

lemma ipc_contDiffAt_Gcf (p : ipc_E) (hp : ipc_Good p.1)
    (h0 : traceForm (controlMatrix (vertex 0)) (ipc_cf (iso_phaseOfCoords p.1) p.2).1 ≠ 0)
    (h2 : traceForm (controlMatrix (vertex 2)) (ipc_cf (iso_phaseOfCoords p.1) p.2).1 ≠ 0) :
    ContDiffAt ℝ 1 ipc_Gcf p := by
  obtain ⟨hX, -, hR⟩ := ipc_CD_cf p hp
  exact hR.tf ((ipc_CD_controlP hX _ h0).sub (ipc_CD_controlP hX _ h2))

lemma ipc_contDiffAt_phaseCoords {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E → iso_PhasePt) (x : E) (h1 : ipc_CD (fun p ↦ (A p).1) x)
    (h2 : ipc_CD (fun p ↦ (A p).2.1) x) (h3 : ipc_CD (fun p ↦ (A p).2.2) x) :
    ContDiffAt ℝ 1 (fun p ↦ iso_phaseCoords (A p)) x := by
  refine contDiffAt_pi' fun k ↦ ?_
  fin_cases k
  exacts [h1 0 0, h1 0 1, h1 1 0, h2 0 0, h2 0 1, h2 1 0, h3 0 0, h3 0 1, h3 1 0]

lemma ipc_contDiffAt_Fcf (p : ipc_E) (hp : ipc_Good p.1) : ContDiffAt ℝ 1 ipc_Fcf p := by
  obtain ⟨hX, hL, hR⟩ := ipc_CD_cf p hp
  have hc : ∀ {A : ipc_E → Mat2}, ipc_CD A p → ipc_CD (fun p ↦ R * A p * R⁻¹) p :=
    fun hA ↦ ((ipc_CD.const R p).mul hA).mul (ipc_CD.const _ p)
  exact ipc_contDiffAt_phaseCoords _ p (hc hX) (hc hL) (hc hR)

/-- Along `q_fix(y₀)` the flow is the strong lift. -/
lemma ipc_flow_v0 (y : ℝ) (hy0 : 1 / √3 < y) (hy1 : y < 1) (t : ℝ) :
    iso_vertexFlow 2 (iso_phaseOfCoords (ipc_v0 y)) t = (segX y t, strongΛ₁ y t, strongΛR y t) := by
  rw [ipc_phaseOfCoords_v0 y hy0 hy1, iso_vertexFlow_qFix y hy0]

lemma ipc_cf_v0 (y : ℝ) (hy0 : 1 / √3 < y) (hy1 : y < 1) (t : ℝ) :
    ipc_cf (iso_phaseOfCoords (ipc_v0 y)) t = (segX y t, strongΛ₁ y t, strongΛR y t) := by
  rw [← ipc_flow_eq_cf (ipc_good_v0 y hy0 hy1), ipc_flow_v0 y hy0 hy1]

lemma ipc_G_v0 (y : ℝ) (hy0 : 1 / √3 < y) (hy1 : y < 1) (t : ℝ) :
    ipc_G (ipc_v0 y, t) = switchingFn 2 0 (strongΛR y t) (segX y t) := by
  simp only [ipc_G, ipc_flow_v0 y hy0 hy1]

/-- `⟨Z_{e₁}, X(t)⟩ < 0` for `t ≥ 0` along the `e₃`-trajectory. -/
lemma ipc_traceForm_Z1_segX_ne (y : ℝ) (hy0 : 1 / √3 < y) {t : ℝ} (ht : 0 ≤ t) :
    traceForm (controlMatrix (vertex 0)) (segX y t) ≠ 0 := by
  have hy : 0 < y := poly_y0_pos hy0
  have hy2 := str_one_third_lt_sq hy0
  rw [(str_traceForm_segX y t hy).1]
  have hW : 1 ≤ Real.exp (√3 * y * t) := Real.one_le_exp (by positivity)
  refine div_ne_zero ?_ (by positivity)
  nlinarith [sq_nonneg (Real.exp (√3 * y * t) - 1)]

lemma ipc_contDiffAt_Gcf_v0 (y : ℝ) (hy0 : 1 / √3 < y) (hy1 : y < 1) {t : ℝ} (ht : 0 ≤ t) :
    ContDiffAt ℝ 1 ipc_Gcf ((ipc_v0 y, t) : ipc_E) := by
  have hy : 0 < y := poly_y0_pos hy0
  refine ipc_contDiffAt_Gcf _ (ipc_good_v0 y hy0 hy1) ?_ ?_ <;>
    simp only [ipc_cf_v0 y hy0 hy1]
  · exact ipc_traceForm_Z1_segX_ne y hy0 ht
  · rw [(str_traceForm_segX y t hy).2.2]
    simp [hy.ne']

/-- **Step 4.** The implicit function theorem for the Poincaré time near `q_fix(y₀)`: near
`q_fix(y₀)` the Poincaré time is a function `ψ` strictly differentiable at `q_fix(y₀)`, and the
Poincaré map is `v ↦ ipc_F (v, ψ v)` there. -/
theorem ipc_poincareTime_ift (y : ℝ) (hy0 : 1 / √3 < y) (hy1 : y < 1) :
    ∃ ψ : (Fin 9 → ℝ) → ℝ, ∃ ψ' : (Fin 9 → ℝ) →L[ℝ] ℝ,
      HasStrictFDerivAt ψ ψ' (ipc_v0 y) ∧ ψ (ipc_v0 y) = switchTime y ∧
      (∀ᶠ v in 𝓝 (ipc_v0 y), iso_poincareMapCoords v = ipc_F (v, ψ v)) ∧
      (∀ᶠ v in 𝓝 (ipc_v0 y), ipc_G (v, ψ v) = 0) := by
  have hy : 0 < y := poly_y0_pos hy0
  set v0 := ipc_v0 y
  set τ := switchTime y
  have hτ : 0 < τ := str_switchTime_pos y hy0 hy1
  obtain ⟨-, -, -, -, -, -, hzero, -, -⟩ := strongLift_isStrongLift y hy0
  have hG0 : ipc_G (v0, τ) = 0 := by rw [ipc_G_v0 y hy0 hy1]; exact hzero
  -- strict differentiability of `G` at `(v₀, t_sw)`
  have hG : HasStrictFDerivAt ipc_G (fderiv ℝ ipc_Gcf (v0, τ)) (v0, τ) :=
    ((ipc_contDiffAt_Gcf_v0 y hy0 hy1 hτ.le).hasStrictFDerivAt one_ne_zero).congr_of_eventuallyEq
      (ipc_G_eventuallyEq y hy0 hy1 τ).symm
  set G' := fderiv ℝ ipc_Gcf (v0, τ)
  -- the partial derivative in `t` is the slope of `χ₃₁` at `t_sw`
  have hline : HasDerivAt (fun t ↦ ipc_G (v0, t)) (G' (0, 1)) τ := by
    have := hG.hasFDerivAt.comp_hasDerivAt τ ((hasDerivAt_const τ v0).prodMk (hasDerivAt_id τ))
    simpa [Function.comp_def] using this
  have hG01 : G' (0, 1) = -iso_chi32Slope y := by
    refine hline.unique ?_
    have e : (fun t ↦ ipc_G (v0, t)) = fun t ↦ switchingFn 2 0 (strongΛR y t) (segX y t) :=
      funext (ipc_G_v0 y hy0 hy1)
    rw [e]
    exact iso_chi31_hasDerivAt y hy0
  have hG01ne : G' (0, 1) ≠ 0 := by
    rw [hG01]; exact neg_ne_zero.2 (iso_chi32Slope_pos y hy0 hy1).ne'
  have hinv : (G' ∘L ContinuousLinearMap.inr ℝ (Fin 9 → ℝ) ℝ).IsInvertible := by
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 _ hG01ne), ?_⟩
    refine ContinuousLinearMap.ext_ring ?_
    simp [ContinuousLinearEquiv.unitsEquivAut_apply]
  -- the implicit function
  set ψ := HasStrictFDerivAt.implicitFunctionOfProdDomain hG hinv
  have hψ := HasStrictFDerivAt.hasStrictFDerivAt_implicitFunctionOfProdDomain hG hinv
  have hiff := HasStrictFDerivAt.eventually_apply_eq_iff_implicitFunctionOfProdDomain hG hinv
  have hψ0 : ψ v0 = τ := (hiff.self_of_nhds).1 rfl
  rw [hG0] at hiff
  refine ⟨ψ, _, hψ, hψ0, ?_, ?_⟩
  swap
  · have h := HasStrictFDerivAt.eventually_apply_implicitFunctionOfProdDomain hG hinv
    rw [hG0] at h
    exact h
  -- `ψ` is the first positive zero of `χ₃₁`
  rw [nhds_prod_eq] at hiff
  obtain ⟨pa, hpa, pb, hpb, hpab⟩ := Filter.eventually_prod_iff.1 hiff
  obtain ⟨ε₀, hε₀, hε₀b⟩ := Metric.eventually_nhds_iff.1 hpb
  set ε := min ε₀ τ
  have hε : 0 < ε := lt_min hε₀ hτ
  have hεb : ∀ t, |t - τ| < ε → pb t := fun t ht ↦
    hε₀b (by rw [Real.dist_eq]; exact lt_of_lt_of_le ht (min_le_left _ _))
  -- positivity of `χ₃₁` on `[0, t_sw - ε/2]`, uniformly near `v₀`
  have hK : ∀ᶠ v in 𝓝 v0, ∀ t ∈ Icc 0 (τ - ε / 2), 0 < ipc_G (v, t) := by
    refine isCompact_Icc.eventually_forall_of_forall_eventually fun t ht ↦ ?_
    have hcont : ContinuousAt ipc_G (v0, t) :=
      (ipc_contDiffAt_Gcf_v0 y hy0 hy1 ht.1).continuousAt.congr
        (ipc_G_eventuallyEq y hy0 hy1 t).symm
    have hpos : 0 < ipc_G (v0, t) := by
      have htτ : t < τ := by linarith [ht.2, min_le_right ε₀ τ]
      obtain ⟨hnn, -, hz, -⟩ := lemma7_5_3 y hy0 hy1 _ _ (strongLift_isStrongLift y hy0) t
        ⟨ht.1, htτ.le⟩
      rw [ipc_G_v0 y hy0 hy1]
      exact lt_of_le_of_ne hnn fun h ↦ htτ.ne (hz h.symm)
    exact hcont.eventually (Ioi_mem_nhds hpos)
  have hψc : ∀ᶠ v in 𝓝 v0, |ψ v - τ| < ε / 2 := by
    have hψc' : ContinuousAt ψ v0 := hψ.continuousAt
    have := hψc'.eventually (by rw [hψ0]; exact Metric.ball_mem_nhds τ (half_pos hε))
    filter_upwards [this] with v hv
    rwa [Real.dist_eq] at hv
  filter_upwards [hpa, hK, hψc] with v hva hvK hvψ
  have hψpos : 0 < ψ v := by
    have := abs_lt.1 hvψ
    linarith [min_le_right ε₀ τ]
  have htime : iso_poincareTime (iso_phaseOfCoords v) = ψ v := by
    have hvψ' : |ψ v - τ| < ε := by linarith
    refine IsLeast.csInf_eq ⟨⟨hψpos, (hpab hva (hεb (ψ v) hvψ')).2 rfl⟩, fun t ht ↦ ?_⟩
    obtain ⟨ht0, htz⟩ := ht
    change ipc_G (v, t) = 0 at htz
    by_contra hlt
    rw [not_le] at hlt
    by_cases htK : t ≤ τ - ε / 2
    · exact (hvK t ⟨ht0.le, htK⟩).ne' htz
    · rw [not_le] at htK
      have hb : |t - τ| < ε := abs_lt.2 ⟨by linarith, by linarith [abs_lt.1 hvψ]⟩
      exact hlt.ne ((hpab hva (hεb t hb)).1 htz).symm
  simp only [iso_poincareMapCoords, iso_poincareMap, htime, ipc_F]


lemma ipc_hasStrictFDerivAt_F (y : ℝ) (hy0 : 1 / √3 < y) (hy1 : y < 1) (t : ℝ) :
    HasStrictFDerivAt ipc_F (fderiv ℝ ipc_F ((ipc_v0 y, t) : ipc_E)) (ipc_v0 y, t) := by
  have h1 : HasStrictFDerivAt ipc_Fcf (fderiv ℝ ipc_Fcf ((ipc_v0 y, t) : ipc_E)) (ipc_v0 y, t) :=
    (ipc_contDiffAt_Fcf (ipc_v0 y, t) (ipc_good_v0 y hy0 hy1)).hasStrictFDerivAt one_ne_zero
  have h2 : HasStrictFDerivAt ipc_F (fderiv ℝ ipc_Fcf ((ipc_v0 y, t) : ipc_E)) (ipc_v0 y, t) :=
    h1.congr_of_eventuallyEq (ipc_F_eventuallyEq y hy0 hy1 t).symm
  rw [h2.hasFDerivAt.fderiv]
  exact h2

lemma ipc_hasStrictFDerivAt_G (y : ℝ) (hy0 : 1 / √3 < y) (hy1 : y < 1) {t : ℝ} (ht : 0 ≤ t) :
    HasStrictFDerivAt ipc_G (fderiv ℝ ipc_G ((ipc_v0 y, t) : ipc_E)) (ipc_v0 y, t) := by
  have h1 : HasStrictFDerivAt ipc_Gcf (fderiv ℝ ipc_Gcf ((ipc_v0 y, t) : ipc_E)) (ipc_v0 y, t) :=
    (ipc_contDiffAt_Gcf_v0 y hy0 hy1 ht).hasStrictFDerivAt one_ne_zero
  have h2 : HasStrictFDerivAt ipc_G (fderiv ℝ ipc_Gcf ((ipc_v0 y, t) : ipc_E)) (ipc_v0 y, t) :=
    h1.congr_of_eventuallyEq (ipc_G_eventuallyEq y hy0 hy1 t).symm
  rw [h2.hasFDerivAt.fderiv]
  exact h2

/-- The derivative of the Poincaré map at `q_fix(y₀)`: `Df = F' ∘ (id, ψ')` with
`G' ∘ (id, ψ') = 0` (`F = Ad(R) q(t, q)`, `G = χ₃₁(q(t, q))`, `ψ` the Poincaré time). -/
theorem ipc_fderiv_structure (y : ℝ) (hy0 : 1 / √3 < y) (hy1 : y < 1) :
    ∃ ψ' : (Fin 9 → ℝ) →L[ℝ] ℝ,
      HasStrictFDerivAt iso_poincareMapCoords
        ((fderiv ℝ ipc_F ((ipc_v0 y, switchTime y) : ipc_E)).comp
          ((ContinuousLinearMap.id ℝ (Fin 9 → ℝ)).prod ψ')) (ipc_v0 y) ∧
      (fderiv ℝ ipc_G ((ipc_v0 y, switchTime y) : ipc_E)).comp
          ((ContinuousLinearMap.id ℝ (Fin 9 → ℝ)).prod ψ') = 0 := by
  obtain ⟨ψ, ψ', hψ, hψ0, hf, hG⟩ := ipc_poincareTime_ift y hy0 hy1
  have hτ := str_switchTime_pos y hy0 hy1
  have hid := (hasStrictFDerivAt_id (𝕜 := ℝ) (ipc_v0 y)).prodMk hψ
  have hF := ipc_hasStrictFDerivAt_F y hy0 hy1 (switchTime y)
  have hG' := ipc_hasStrictFDerivAt_G y hy0 hy1 hτ.le
  have hF' : HasStrictFDerivAt ipc_F (fderiv ℝ ipc_F ((ipc_v0 y, switchTime y) : ipc_E))
      (ipc_v0 y, ψ (ipc_v0 y)) := by rw [hψ0]; exact hF
  have hG'' : HasStrictFDerivAt ipc_G (fderiv ℝ ipc_G ((ipc_v0 y, switchTime y) : ipc_E))
      (ipc_v0 y, ψ (ipc_v0 y)) := by rw [hψ0]; exact hG'
  refine ⟨ψ', ?_, ?_⟩
  · have hc := hF'.comp (ipc_v0 y) hid
    refine hc.congr_of_eventuallyEq ?_
    filter_upwards [hf] with v hv
    rw [hv]
    rfl
  · have hc := hG''.comp (ipc_v0 y) hid
    have h0 : HasFDerivAt (fun v ↦ ipc_G (v, ψ v)) (0 : (Fin 9 → ℝ) →L[ℝ] ℝ) (ipc_v0 y) :=
      (hasFDerivAt_const (0 : ℝ) (ipc_v0 y)).congr_of_eventuallyEq hG
    exact hc.hasFDerivAt.unique h0


/-! ### The direct calculation: the derivative in the directions of the plan -/

lemma ipc_G'01 (y : ℝ) (hy0 : 1 / √3 < y) (hy1 : y < 1) :
    fderiv ℝ ipc_G ((ipc_v0 y, switchTime y) : ipc_E) (0, 1) = -iso_chi32Slope y := by
  have hτ := str_switchTime_pos y hy0 hy1
  have hline : HasDerivAt (fun t ↦ ipc_G (ipc_v0 y, t))
      (fderiv ℝ ipc_G ((ipc_v0 y, switchTime y) : ipc_E) (0, 1)) (switchTime y) := by
    have := (ipc_hasStrictFDerivAt_G y hy0 hy1 hτ.le).hasFDerivAt.comp_hasDerivAt (switchTime y)
      ((hasDerivAt_const (switchTime y) (ipc_v0 y)).prodMk (hasDerivAt_id (switchTime y)))
    simpa [Function.comp_def] using this
  refine hline.unique ?_
  have e : (fun t ↦ ipc_G (ipc_v0 y, t)) = fun t ↦ switchingFn 2 0 (strongΛR y t) (segX y t) :=
    funext (ipc_G_v0 y hy0 hy1)
  rw [e]
  exact iso_chi31_hasDerivAt y hy0

/-- The time derivative of `Ad(R) q(t, q)` in coordinates. -/
lemma ipc_hasDerivAt_phaseCoords_adR_flow (q : iso_PhasePt) (t : ℝ) :
    HasDerivAt (fun s ↦ iso_phaseCoords (iso_adR (iso_vertexFlow 2 q s)))
      (iso_phaseCoords (iso_adR
        (controlP (vertex 2) (iso_vfX 2 q t) * iso_vfX 2 q t -
            iso_vfX 2 q t * controlP (vertex 2) (iso_vfX 2 q t),
          iso_vfΛ₁ 2 q t * iso_vfX 2 q t - iso_vfX 2 q t * iso_vfΛ₁ 2 q t,
          costateRHS (-1) (iso_vfΛ₁ 2 q t) (iso_vfΛR 2 q t) (iso_vfX 2 q t) (vertex 2)))) t := by
  have hX := ((ivf_vfX_hasDerivAt 2 q t).const_mul R).mul_const R⁻¹
  have hL := ((ivf_vfΛ₁_hasDerivAt 2 q t).const_mul R).mul_const R⁻¹
  have hR := ((ivf_vfΛR_hasDerivAt 2 q t).const_mul R).mul_const R⁻¹
  refine hasDerivAt_pi.2 fun k ↦ ?_
  fin_cases k
  exacts [hX 0 0, hX 0 1, hX 1 0, hL 0 0, hL 0 1, hL 1 0, hR 0 0, hR 0 1, hR 1 0]

/-- The time derivative of `q(t, q)` in coordinates. -/
lemma ipc_hasDerivAt_phaseCoords_flow (q : iso_PhasePt) (t : ℝ) :
    HasDerivAt (fun s ↦ iso_phaseCoords (iso_vertexFlow 2 q s))
      (iso_phaseCoords
        (controlP (vertex 2) (iso_vfX 2 q t) * iso_vfX 2 q t -
            iso_vfX 2 q t * controlP (vertex 2) (iso_vfX 2 q t),
          iso_vfΛ₁ 2 q t * iso_vfX 2 q t - iso_vfX 2 q t * iso_vfΛ₁ 2 q t,
          costateRHS (-1) (iso_vfΛ₁ 2 q t) (iso_vfΛR 2 q t) (iso_vfX 2 q t) (vertex 2))) t := by
  have hX := ivf_vfX_hasDerivAt 2 q t
  have hL := ivf_vfΛ₁_hasDerivAt 2 q t
  have hR := ivf_vfΛR_hasDerivAt 2 q t
  refine hasDerivAt_pi.2 fun k ↦ ?_
  fin_cases k
  exacts [hX 0 0, hX 0 1, hX 1 0, hL 0 0, hL 0 1, hL 1 0, hR 0 0, hR 0 1, hR 1 0]

lemma ipc_vf_qFix (y : ℝ) (hy0 : 1 / √3 < y) (t : ℝ) :
    iso_vfX 2 (iso_qFix y) t = segX y t ∧ iso_vfΛ₁ 2 (iso_qFix y) t = strongΛ₁ y t ∧
      iso_vfΛR 2 (iso_qFix y) t = strongΛR y t := by
  have h := iso_vertexFlow_qFix y hy0 t
  exact ⟨congrArg Prod.fst h, congrArg (fun p : iso_PhasePt ↦ p.2.1) h,
    congrArg (fun p : iso_PhasePt ↦ p.2.2) h⟩

lemma ipc_F'01 (y : ℝ) (hy0 : 1 / √3 < y) (hy1 : y < 1) :
    fderiv ℝ ipc_F ((ipc_v0 y, switchTime y) : ipc_E) (0, 1) = ipc_Ft y (ellSw y) := by
  have hline : HasDerivAt (fun t ↦ ipc_F (ipc_v0 y, t))
      (fderiv ℝ ipc_F ((ipc_v0 y, switchTime y) : ipc_E) (0, 1)) (switchTime y) := by
    have := (ipc_hasStrictFDerivAt_F y hy0 hy1 (switchTime y)).hasFDerivAt.comp_hasDerivAt
      (switchTime y)
      ((hasDerivAt_const (switchTime y) (ipc_v0 y)).prodMk (hasDerivAt_id (switchTime y)))
    simpa [Function.comp_def] using this
  refine hline.unique ?_
  have e : (fun t ↦ ipc_F (ipc_v0 y, t)) =
      fun t ↦ iso_phaseCoords (iso_adR (iso_vertexFlow 2 (iso_qFix y) t)) := by
    funext t; simp only [ipc_F, ipc_phaseOfCoords_v0 y hy0 hy1]
  rw [e, ← ipc_Ft_eq y hy0]
  obtain ⟨h1, h2, h3⟩ := ipc_vf_qFix y hy0 (switchTime y)
  have := ipc_hasDerivAt_phaseCoords_adR_flow (iso_qFix y) (switchTime y)
  rwa [h1, h2, h3] at this

lemma ipc_phaseOfCoords_add_smul (v w : Fin 9 → ℝ) (s : ℝ) :
    iso_phaseOfCoords (v + s • w) =
      ((iso_phaseOfCoords v).1 + s • (iso_phaseOfCoords w).1,
        (iso_phaseOfCoords v).2.1 + s • (iso_phaseOfCoords w).2.1,
        (iso_phaseOfCoords v).2.2 + s • (iso_phaseOfCoords w).2.2) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [iso_phaseOfCoords] <;> ring

lemma ipc_phaseCoords_adR_add_smul (X A B C D : Mat2) (s : ℝ) :
    iso_phaseCoords (iso_adR (X, A + s • B, C + s • D)) =
      iso_phaseCoords (iso_adR (X, A, C)) + s • iso_phaseCoords (iso_adR (0, B, D)) := by
  funext k
  fin_cases k <;>
    simp [iso_phaseCoords, iso_adR, Matrix.mul_add, Matrix.add_mul]

lemma ipc_switchingFn_add_smul (i j : Fin 3) (A B X : Mat2) (s : ℝ) :
    switchingFn i j (A + s • B) X = switchingFn i j A X + s * switchingFn i j B X := by
  simp only [switchingFn, traceForm, Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add,
    Matrix.trace_smul, smul_eq_mul]

/-- The derivative in the costate directions (`w` with zero `X`-part). -/
lemma ipc_dir_costate (y : ℝ) (hy0 : 1 / √3 < y) (hy1 : y < 1) (w : Fin 9 → ℝ)
    (hw : w 0 = 0 ∧ w 1 = 0 ∧ w 2 = 0) :
    fderiv ℝ ipc_F ((ipc_v0 y, switchTime y) : ipc_E) (w, 0) =
        ipc_linVec y (ellSw y) (w 3) (w 4) (w 5) (w 6) (w 7) (w 8) ∧
      fderiv ℝ ipc_G ((ipc_v0 y, switchTime y) : ipc_E) (w, 0) =
        ipc_Glin y (ellSw y) (w 3) (w 4) (w 5) (w 6) (w 7) (w 8) := by
  have hy : 0 < y := poly_y0_pos hy0
  have hτ := str_switchTime_pos y hy0 hy1
  set τ := switchTime y
  set q0 := iso_phaseOfCoords (ipc_v0 y)
  have hq0 : q0 = iso_qFix y := ipc_phaseOfCoords_v0 y hy0 hy1
  have hw0 : (iso_phaseOfCoords w).1 = 0 := by
    obtain ⟨h0, h1, h2⟩ := hw
    ext i j; fin_cases i <;> fin_cases j <;> simp [iso_phaseOfCoords, h0, h1, h2]
  have hcurve : HasDerivAt (fun s : ℝ ↦ ((ipc_v0 y + s • w, τ) : ipc_E)) (w, 0) 0 := by
    have h1 := ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add (ipc_v0 y)
    rw [one_smul] at h1
    exact h1.prodMk (hasDerivAt_const 0 τ)
  have hpt : ((ipc_v0 y, τ) : ipc_E) = (ipc_v0 y + (0 : ℝ) • w, τ) := by simp
  have hq : ∀ s : ℝ, iso_phaseOfCoords (ipc_v0 y + s • w) =
      (q0.1, q0.2.1 + s • (iso_phaseOfCoords w).2.1, q0.2.2 + s • (iso_phaseOfCoords w).2.2) := by
    intro s
    rw [ipc_phaseOfCoords_add_smul, hw0, smul_zero, add_zero]
  have hgood : ∀ s : ℝ, ipc_Good (ipc_v0 y + s • w) := by
    intro s
    have := ipc_good_v0 y hy0 hy1
    unfold ipc_Good at this ⊢
    rw [hq s]
    exact this
  have hcf : ∀ s : ℝ, ipc_cf (iso_phaseOfCoords (ipc_v0 y + s • w)) τ =
      ((ipc_cf q0 τ).1, (ipc_cf q0 τ).2.1 + s • ipc_cfΛ₁ (q0.1, (iso_phaseOfCoords w).2.1,
        (iso_phaseOfCoords w).2.2) τ,
        (ipc_cf q0 τ).2.2 + s • ipc_linΛR (q0.1, (iso_phaseOfCoords w).2.1,
          (iso_phaseOfCoords w).2.2) τ) := fun s ↦ by
    rw [hq s, ipc_cf_add_smul]
  have hX : q0.1 = Φ 0 y := by rw [hq0]; rfl
  have hδ : (iso_phaseOfCoords w).2.1 = !![w 3, w 4; w 5, -w 3] ∧
      (iso_phaseOfCoords w).2.2 = !![w 6, w 7; w 8, -w 6] := ⟨rfl, rfl⟩
  constructor
  · have h1 := (ipc_hasStrictFDerivAt_F y hy0 hy1 τ).hasFDerivAt.comp_hasDerivAt_of_eq 0 hcurve hpt
    have e : ipc_F ∘ (fun s : ℝ ↦ ((ipc_v0 y + s • w, τ) : ipc_E)) = fun s ↦
        ipc_F (ipc_v0 y, τ) + s • ipc_linVec y (ellSw y) (w 3) (w 4) (w 5) (w 6) (w 7) (w 8) := by
      funext s
      simp only [Function.comp_apply, ipc_F, ipc_flow_eq_cf (hgood s), hcf s,
        ipc_phaseCoords_adR_add_smul, ipc_flow_eq_cf (ipc_good_v0 y hy0 hy1)]
      rw [hX, hδ.1, hδ.2, ipc_linVec_eq y hy0]
    rw [e] at h1
    have h2 := ((hasDerivAt_id (0 : ℝ)).smul_const
      (ipc_linVec y (ellSw y) (w 3) (w 4) (w 5) (w 6) (w 7) (w 8))).const_add (ipc_F (ipc_v0 y, τ))
    rw [one_smul] at h2
    exact h1.unique h2
  · have h1 := (ipc_hasStrictFDerivAt_G y hy0 hy1 hτ.le).hasFDerivAt.comp_hasDerivAt_of_eq 0
      hcurve hpt
    have e : ipc_G ∘ (fun s : ℝ ↦ ((ipc_v0 y + s • w, τ) : ipc_E)) = fun s ↦
        ipc_G (ipc_v0 y, τ) + s * ipc_Glin y (ellSw y) (w 3) (w 4) (w 5) (w 6) (w 7) (w 8) := by
      funext s
      simp only [Function.comp_apply, ipc_G, ipc_flow_eq_cf (hgood s), hcf s,
        ipc_switchingFn_add_smul, ipc_flow_eq_cf (ipc_good_v0 y hy0 hy1)]
      have hXτ : (ipc_cf q0 τ).1 = segX y τ := by
        rw [show q0 = iso_phaseOfCoords (ipc_v0 y) from rfl, ipc_cf_v0 y hy0 hy1]
      rw [hX, hδ.1, hδ.2, hXτ, ipc_Glin_eq y hy0]
    rw [e] at h1
    have h2 := ((hasDerivAt_id (0 : ℝ)).mul_const
      (ipc_Glin y (ellSw y) (w 3) (w 4) (w 5) (w 6) (w 7) (w 8))).const_add (ipc_G (ipc_v0 y, τ))
    rw [one_mul] at h2
    exact h1.unique h2

/-- `D f = F' ∘ (id, ψ')` with `G' ∘ (id, ψ') = 0`: in every direction `w`,
`Df w = F'(w, 0) - (G'(w, 0)/G'(0, 1)) F'(0, 1)`. -/
lemma ipc_fderiv_apply (y : ℝ) (hy0 : 1 / √3 < y) (hy1 : y < 1) (w : Fin 9 → ℝ) :
    fderiv ℝ iso_poincareMapCoords (ipc_v0 y) w =
      fderiv ℝ ipc_F ((ipc_v0 y, switchTime y) : ipc_E) (w, 0) -
        (fderiv ℝ ipc_G ((ipc_v0 y, switchTime y) : ipc_E) (w, 0) /
          fderiv ℝ ipc_G ((ipc_v0 y, switchTime y) : ipc_E) (0, 1)) •
          fderiv ℝ ipc_F ((ipc_v0 y, switchTime y) : ipc_E) (0, 1) := by
  obtain ⟨ψ', h, hG⟩ := ipc_fderiv_structure y hy0 hy1
  have hG01 : fderiv ℝ ipc_G ((ipc_v0 y, switchTime y) : ipc_E) (0, 1) ≠ 0 := by
    rw [ipc_G'01 y hy0 hy1]; exact neg_ne_zero.2 (iso_chi32Slope_pos y hy0 hy1).ne'
  set F' := fderiv ℝ ipc_F ((ipc_v0 y, switchTime y) : ipc_E)
  set G' := fderiv ℝ ipc_G ((ipc_v0 y, switchTime y) : ipc_E)
  have hsplit : ((w, ψ' w) : ipc_E) = (w, 0) + ψ' w • ((0, 1) : ipc_E) := by
    ext <;> simp
  have hGw : G' (w, 0) + ψ' w * G' (0, 1) = 0 := by
    have := congrArg (fun L ↦ L w) hG
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply, zero_apply] at this
    rw [hsplit, map_add, map_smul, smul_eq_mul] at this
    exact this
  have hψ : ψ' w = -(G' (w, 0) / G' (0, 1)) := by
    field_simp
    linarith
  rw [h.hasFDerivAt.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, hsplit, map_add, map_smul, hψ, neg_smul, ← sub_eq_add_neg]


lemma ipc_hasFDerivAt (y : ℝ) (hy0 : 1 / √3 < y) (hy1 : y < 1) :
    HasFDerivAt iso_poincareMapCoords (fderiv ℝ iso_poincareMapCoords (ipc_v0 y)) (ipc_v0 y) := by
  obtain ⟨ψ', h, -⟩ := ipc_fderiv_structure y hy0 hy1
  exact h.hasFDerivAt.differentiableAt.hasFDerivAt

/-- The fixed points `q_fix(y₀)` form a curve of fixed points: `Df` fixes its tangent. -/
lemma ipc_fderiv_Fam (y : ℝ) (hy0 : 1 / √3 < y) (hy1 : y < 1) :
    fderiv ℝ iso_poincareMapCoords (ipc_v0 y) (ipc_Fam y (ellSw y)) = ipc_Fam y (ellSw y) := by
  have hy : 0 < y := poly_y0_pos hy0
  have hγ : HasDerivAt ipc_v0 (ipc_Fam y (ellSw y)) y := ipc_hasDerivAt_qFix y hy
  have h1 := (ipc_hasFDerivAt y hy0 hy1).comp_hasDerivAt y hγ
  have hev : iso_poincareMapCoords ∘ ipc_v0 =ᶠ[𝓝 y] ipc_v0 := by
    filter_upwards [Ioo_mem_nhds hy0 hy1] with x hx
    change iso_poincareMapCoords (ipc_v0 x) = ipc_v0 x
    rw [iso_poincareMapCoords, ipc_phaseOfCoords_v0 x hx.1 hx.2, iso_poincareMap_qFix x hx.1 hx.2]
    rfl
  exact h1.unique (hγ.congr_of_eventuallyEq hev)

/-- Restarting the octagon's arc at `ε ∈ [0, t_sw)` does not change the Poincaré map: by the
octagon's lifted trajectory (`theorem7_7_1_octagon`) and `iso_arc_eq_vertexFlow`, the flow from
`q(ε)` is the strong lift shifted by `ε`, whose first switching time is `t_sw - ε`. -/
lemma ipc_poincareMap_flow_octagon {ε : ℝ} (h0 : 0 ≤ ε) (hε : ε < switchTime (y₀ 1)) :
    iso_poincareMapCoords (iso_phaseCoords (iso_vertexFlow 2 (iso_qFix (y₀ 1)) ε)) =
      ipc_v0 (y₀ 1) := by
  obtain ⟨hy0, hy1⟩ := poly_y₀_mem (le_refl 1)
  set y := y₀ 1
  have hy : 0 < y := poly_y0_pos hy0
  set τ := switchTime y with hτdef
  have hτ : 0 < τ := str_switchTime_pos y hy0 hy1
  obtain ⟨htr, -, -, -, -, -, hzero, hRτ, h1τ⟩ := strongLift_isStrongLift y hy0
  obtain ⟨hst, hg0, hX0⟩ := poly_isStateTrajectory y hy0 hy1 4 (by norm_num)
  have hT : ((4 : ℕ) : ℝ) * τ = (3 * ((1 : ℕ) : ℝ) + 1) * τ := by norm_num
  rw [hT] at hst
  have hext := poly_isPontryaginExtremal 1 le_rfl y hy0 hy1 (poly_y₀_trace le_rfl) _ _ hst hg0 hX0
  -- the octagon's lift on `[0, t_sw]` is the strong lift
  have hpw : ∀ {f : ℝ → Mat2}, f τ = R⁻¹ * f 0 * R → ∀ t ∈ Icc 0 τ,
      poly_pw R⁻¹ R τ f t = f t := by
    intro f hf t ht
    rw [poly_pw_of_mem_Icc hτ hf (i := 0) (by simpa using ht)]
    simp
  have hX : ∀ t ∈ Icc 0 τ, polygonX y τ t = segX y t := fun t ht ↦ by
    rw [poly_polygonX_eq]
    exact hpw (by rw [segX_switchTime y hy0, str_segX_zero y hy]) t ht
  have h1 : ∀ t ∈ Icc 0 τ, poly_pw R⁻¹ R τ (strongΛ₁ y) t = strongΛ₁ y t :=
    fun t ht ↦ hpw h1τ t ht
  have hR : ∀ t ∈ Icc 0 τ, poly_pw R⁻¹ R τ (strongΛR y) t = strongΛR y t :=
    fun t ht ↦ hpw hRτ t ht
  have hu : ∀ᵐ t, t ∈ Ioo ε τ → polygonControlAt τ t = vertex 2 := by
    refine Filter.Eventually.of_forall fun t ht ↦ ?_
    rw [poly_polygonControlAt_eq,
      poly_floor_eq hτ (i := 0) (by simp; linarith [ht.1]) (by simpa using ht.2)]
    rfl
  have harc := iso_arc_eq_vertexFlow hext h0 hε.le (by push_cast; linarith) 2 hu
  set qε := iso_vertexFlow 2 (iso_qFix y) ε
  have hqε : qε = (segX y ε, strongΛ₁ y ε, strongΛR y ε) := iso_vertexFlow_qFix y hy0 ε
  have hεI : ε ∈ Icc 0 τ := ⟨h0, hε.le⟩
  have hshift : ∀ s ∈ Icc 0 (τ - ε),
      iso_vertexFlow 2 qε s = (segX y (ε + s), strongΛ₁ y (ε + s), strongΛR y (ε + s)) := by
    intro s hs
    have hm : ε + s ∈ Icc 0 τ := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have := harc (ε + s) ⟨by linarith [hs.1], by linarith [hs.2]⟩
    rw [hX _ hm, h1 _ hm, hR _ hm, hX _ hεI, h1 _ hεI, hR _ hεI, add_sub_cancel_left] at this
    rw [hqε]
    exact this.symm
  -- the first switching time from `q(ε)` is `t_sw - ε`
  have htime : iso_poincareTime qε = τ - ε := by
    refine IsLeast.csInf_eq ⟨⟨by linarith, ?_⟩, fun t ht ↦ ?_⟩
    · rw [hshift _ ⟨by linarith, le_rfl⟩, add_sub_cancel]
      exact hzero
    · obtain ⟨ht0, htz⟩ := ht
      refine le_of_not_gt fun hlt ↦ ?_
      rw [hshift t ⟨ht0.le, hlt.le⟩] at htz
      have hm : ε + t ∈ Icc 0 τ := ⟨by linarith, by linarith⟩
      have := (lemma7_5_3 y hy0 hy1 _ _ (strongLift_isStrongLift y hy0) (ε + t) hm).2.2.1 htz
      linarith
  have hmap : iso_poincareMap qε = iso_qFix y := by
    rw [iso_poincareMap, htime, hshift _ ⟨by linarith, le_rfl⟩, add_sub_cancel,
      ← iso_vertexFlow_qFix y hy0]
    have := iso_poincareMap_qFix y hy0 hy1
    rwa [iso_poincareMap, iso_poincareTime_qFix y hy0 hy1] at this
  have hq : iso_phaseOfCoords (iso_phaseCoords qε) = qε := by
    rw [hqε]
    exact ipc_phaseOfCoords_phaseCoords _ (segX_star y hy0 hy1 ε hεI).1 (htr ε hεI).1
      (htr ε hεI).2
  rw [iso_poincareMapCoords, hq, hmap]
  rfl

/-- The time direction: `Df` annihilates the vector field at `q_oct` (the Poincaré map is
constant along the octagon's orbit). -/
lemma ipc_fderiv_Vq :
    fderiv ℝ iso_poincareMapCoords (ipc_v0 (y₀ 1)) (ipc_Vq (y₀ 1) (ellSw (y₀ 1))) = 0 := by
  obtain ⟨hy0, hy1⟩ := poly_y₀_mem (le_refl 1)
  set y := y₀ 1
  have hy : 0 < y := poly_y0_pos hy0
  have hτ : 0 < switchTime y := str_switchTime_pos y hy0 hy1
  set q0 := iso_qFix y
  have hc :
      HasDerivAt (fun s ↦ iso_phaseCoords (iso_vertexFlow 2 q0 s)) (ipc_Vq y (ellSw y)) 0 := by
    have h := ipc_hasDerivAt_phaseCoords_flow q0 0
    obtain ⟨h1, h2, h3⟩ := ipc_vf_qFix y hy0 0
    rw [h1, h2, h3, str_segX_zero y hy, ipc_strongΛ₁_zero y hy, ipc_strongΛR_zero y hy,
      ipc_Vq_eq y hy] at h
    exact h
  have hc0 : ipc_v0 y = iso_phaseCoords (iso_vertexFlow 2 q0 0) := by
    rw [ivf_vertexFlow_zero]; rfl
  have h1 := ((ipc_hasFDerivAt y hy0 hy1).comp_hasDerivAt_of_eq 0 hc hc0).hasDerivWithinAt
    (s := Ici 0)
  have hev : (iso_poincareMapCoords ∘ fun s ↦ iso_phaseCoords (iso_vertexFlow 2 q0 s)) =ᶠ[𝓝[≥] 0]
      fun _ ↦ ipc_v0 y := by
    filter_upwards [Ico_mem_nhdsGE hτ] with s hs
    exact ipc_poincareMap_flow_octagon hs.1 hs.2
  have h2 : HasDerivWithinAt (iso_poincareMapCoords ∘ fun s ↦ iso_phaseCoords
      (iso_vertexFlow 2 q0 s)) 0 (Ici 0) 0 :=
    (hasDerivWithinAt_const _ _ _).congr_of_eventuallyEq hev (hev.self_of_nhdsWithin le_rfl)
  exact (uniqueDiffWithinAt_Ici 0).eq_deriv _ h1 h2

/-- The Poincaré map is strictly differentiable at `q_oct` (in coordinates): the closed form of
the vertex flow is `C¹` in `(q, t)` near the octagon's arc, and by `iso_chi31_hasDerivAt` and the
implicit function theorem, near `q_oct` the Poincaré time is a function of `q` strictly
differentiable at `q_oct` (`ipc_fderiv_structure`). -/
theorem iso_poincareMapCoords_hasStrictFDerivAt :
    HasStrictFDerivAt iso_poincareMapCoords
      (fderiv ℝ iso_poincareMapCoords (iso_phaseCoords (iso_qFix (y₀ 1))))
      (iso_phaseCoords (iso_qFix (y₀ 1))) := by
  obtain ⟨hy0, hy1⟩ := poly_y₀_mem (le_refl 1)
  obtain ⟨ψ', h, -⟩ := ipc_fderiv_structure (y₀ 1) hy0 hy1
  rw [ipc_v0] at h
  rwa [h.hasFDerivAt.fderiv]

/-- **The direct calculation.** The derivative of the Poincaré map at `q_oct` maps the basis
vectors by the matrix `iso_sectionMatrix`: decompose `b_j = α_j Vq + β_j Fam + w_j`
(`ipc_basis_decomp0`, …), use `Df(Vq) = 0`, `Df(Fam) = Fam` and the explicit derivative in the
costate directions (`ipc_dir_costate`), and compare with the columns (`ipc_column0`, …). -/
theorem iso_fderiv_basis (j : Fin 4) :
    fderiv ℝ iso_poincareMapCoords (iso_phaseCoords (iso_qFix (y₀ 1)))
        (iso_sectionBasis (y₀ 1) (ellSw (y₀ 1)) j) =
      ∑ i, iso_sectionMatrix (y₀ 1 ^ 2) (ellSw (y₀ 1)) i j •
        iso_sectionBasis (y₀ 1) (ellSw (y₀ 1)) i := by
  obtain ⟨hy0, hy1⟩ := poly_y₀_mem (le_refl 1)
  set y := y₀ 1
  have hy : 0 < y := poly_y0_pos hy0
  have hD : 3 * ellSw y * y ^ 2 + ellSw y + 3 * y ^ 2 - 3 ≠ 0 := by
    have h := iso_chi32Slope_pos y hy0 hy1
    rw [iso_chi32Slope] at h
    have h3 : (0 : ℝ) < √3 := by positivity
    have : 0 < 4 - (1 + 3 * y ^ 2) - (1 + 3 * y ^ 2) * ellSw y := by
      by_contra hc
      rw [not_lt] at hc
      have : 2 * √3 * (4 - (1 + 3 * y ^ 2) - (1 + 3 * y ^ 2) * ellSw y) / (3 * y ^ 2) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by positivity) hc)
          (by positivity)
      linarith
    intro h0
    linarith
  have hDw : ∀ w : Fin 9 → ℝ, w 0 = 0 ∧ w 1 = 0 ∧ w 2 = 0 →
      fderiv ℝ iso_poincareMapCoords (ipc_v0 y) w = ipc_Dw y (ellSw y) w := by
    intro w hw
    obtain ⟨hF, hG⟩ := ipc_dir_costate y hy0 hy1 w hw
    rw [ipc_fderiv_apply y hy0 hy1, hF, hG, ipc_G'01 y hy0 hy1, ipc_F'01 y hy0 hy1, ipc_Dw,
      ipc_G01_eq]
  change fderiv ℝ iso_poincareMapCoords (ipc_v0 y) _ = _
  have c0 : fderiv ℝ iso_poincareMapCoords (ipc_v0 y) (iso_sectionBasis y (ellSw y) 0) =
      ∑ i, iso_sectionMatrix (y ^ 2) (ellSw y) i 0 • iso_sectionBasis y (ellSw y) i := by
    rw [ipc_basis_decomp0 y _ hy, map_add, map_add, map_smul, ipc_fderiv_Vq,
      ipc_fderiv_Fam y hy0 hy1, hDw _ (by simp [ipc_w0]), zero_add]
    exact ipc_column0 y _ hy hD
  have c1 : fderiv ℝ iso_poincareMapCoords (ipc_v0 y) (iso_sectionBasis y (ellSw y) 1) =
      ∑ i, iso_sectionMatrix (y ^ 2) (ellSw y) i 1 • iso_sectionBasis y (ellSw y) i := by
    rw [ipc_basis_decomp1 y _ hy, map_add, map_smul, ipc_fderiv_Fam y hy0 hy1,
      hDw _ (by simp [ipc_w1])]
    exact ipc_column1 y _ hy hD
  have c2 : fderiv ℝ iso_poincareMapCoords (ipc_v0 y) (iso_sectionBasis y (ellSw y) 2) =
      ∑ i, iso_sectionMatrix (y ^ 2) (ellSw y) i 2 • iso_sectionBasis y (ellSw y) i := by
    rw [ipc_basis_decomp2, hDw _ (by simp [ipc_w2])]
    exact ipc_column2 y _ hy hD
  have c3 : fderiv ℝ iso_poincareMapCoords (ipc_v0 y) (iso_sectionBasis y (ellSw y) 3) =
      ∑ i, iso_sectionMatrix (y ^ 2) (ellSw y) i 3 • iso_sectionBasis y (ellSw y) i := by
    rw [ipc_basis_decomp3, hDw _ (by simp [ipc_w3])]
    exact ipc_column3 y _ hy hD
  fin_cases j
  exacts [c0, c1, c2, c3]

end SmoothedPolygons
