module

public import SmoothedPolygons.Ch14.Asymptotics
public import SmoothedPolygons.Ch14.l6d_Extension
public import SmoothedPolygons.Ch13.Jacobian
public import Basic.Analysis.Analytic.DivisionByCoordinate
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Topology.OpenPartialHomeomorph.Defs
public import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import SmoothedPolygons.Ch7.Isolated.Return

/-!
# Chapter 14: the analytic extension of the Reinhardt–Poincaré map (Lemma 14.3.1)

§14.3 of Hales–Vajjha, *Packings of Smoothed Polygons* ("Analytic Extension of the Reinhardt
system", TeX 11760–11880): near the fixed point `(0, x̃_out)` the Reinhardt–Poincaré map, written in
the Lie algebra chart `(r, x̃)` and initially defined for `r > 0`, extends to an analytic
diffeomorphism of a neighborhood in `ℝ⁴ = ℝ × ℝ³` (`r ≤ 0` included) whose restriction to the
exceptional divisor `r = 0` is the Fuller–Poincaré map.

* `reinSwitchTime q`: the least positive zero of `χ₂₁` along the flow with the control `e₂` from `q`
  (the switching time, TeX 11807–11811); `reinPoincare q = Ad_{R⁻¹}(q(t_sw))` (the book writes
  `ad_{R⁻¹}`, G14.6; "The rotation is chosen to make the fixed point property hold exactly",
  TeX 11826–11838); `reinChartMap`, the map in the chart (TeX 11683–11686: "We can write the
  Reinhardt–Poincaré map `F` in local coordinates `(r, x̃) ↦ F(r, x̃)`");
* `fullerChartMap`: the Fuller–Poincaré map in the chart `x̃` of the divisor (rotation by `ζ` to the
  wall `𝒲₀`, rescaling to `Im z₁ = 1/2`), with the fixed point `x̃_out` and its linearization, whose
  eigenvalues have modulus `< 1/10` (transferred from Lemma 13.5.5's certified Jacobian);
* `analyticAt_rescaledChi`: the first step of the proof, "`χ₂₁(X(s r₀), Λ₁(s r₀), Λ_R(s r₀))/r₀³`
  extends to an analytic function `χ̃₂₁(s, r₀, x̃₀)` in a neighborhood of `r₀ = 0`";
* `eventually_isSwitch_reinSwitchTime`: near the fixed point, with `r > 0`, the control `e₂` is
  optimal on `[0, t_sw]` and is beaten by `e₁` right after (the χ₂₃ check, G14.5: the book examines
  only `χ₂₁`), so `reinPoincare` is the map of consecutive switching points of extremals;
* `IsReinhardtPoincareExtension`, `lemma14_3_1`: **Lemma 14.3.1**.

## The book's proof (TeX 11784–11872), step by step, as formalized

1. The chart is rational in `(r₀, x̃₀)` and `(1 + r₀ x̃₂₁)⁻¹` with nonzero denominators near the
   fixed point, hence analytic (`l6d_MatAn_lieChart`, in
   `SmoothedPolygons/Ch14/l6d_FlowAnalytic.lean`).
2. The vertex flow is analytic in `(t, q)` (`l6d_analyticAt_vertexFlow`): `X(t)` and `Λ₁(t)` are
   products of matrix exponentials; for `Λ_R(t)` the quadratures of the closed form are replaced by
   `exp (t • L(X₀, P))` of a linear ODE in the frame rotating with `e^{tP}` (`l6d_rotCurve`,
   `l6d_vfΛR_eq_exp`); Mathlib's `NormedSpace.exp_analytic` does the rest
   (`Basic/Analysis/Analytic/l6d_MatrixAnalytic.lean`). Substitute `t = s r₀` (`l6d_flowPt`).
3. Lemma 14.2.4 and division of power series: `χ̃₂₁ = χ₂₁/r₀³` (`l6d_chi21`) is analytic near
   `r₀ = 0` (`l6d_analyticAt_divR`, from `AnalyticAt.exists_eq_pow_smul_of_isBigO`; the
   one-sided `O(r₀³)` of Lemma 14.2.4 becomes two-sided by `l6d_isBigO_nhds_of_isBigO_nhdsGT`),
   with value `24 RR(ζ - 1, z₃(s))` at `r₀ = 0` (`analyticAt_rescaledChi`).
4. At `(0, x̃_out)` the Fuller cubic is `24 λ³ g(s/λ)`, `g(τ) = a₀ + a₁τ + a₂τ² + a₃τ³` with
   `a₀, a₁, a₂ > 0 > a₃` (`qOutCart_signs`) and `g(t_sw) = 0` (`poincare_qOutCart`): exactly,
   `t_sw³ g(τ) = (t_sw - τ) B(τ)` with `B > 0` on `[0, ∞)`, so `g > 0` on `[0, t_sw)`, `g < 0`
   after, and `g'(t_sw) < 0` (no numerics).
5. The analytic implicit function theorem (`ContDiffAt.implicitFunction`, `n = ω`) gives the
   analytic `s_sw` (`l6d_sSw`); the IFT uniqueness box and compactness of `[0, s_sw,out]` show that
   `s_sw(r₀, x̃₀)` is the least positive zero (`l6d_zero_structure`), so
   `reinSwitchTime (lieChart p) = r s_sw(p)` for `r > 0` (`l6d_reinSwitchTime_eq`).
6. Rotate by `Ad_{R⁻¹}` (`l6d_Xi`).
7. G14.7: the entries of `X_sw - J` and `Λ₁sw + (3/2) J` read by the chart are `O(r₀)`, `O(r₀²)`
   (Lemma 14.2.3, rotated by `fullerCoords_adR`, with the determinant relations `det X = 1`,
   `det Λ₁ = 9/4`, `l6d_det_relations`, for the entries `cayleyZ` does not see), so they are
   divisible by `r₀`, `r₀²` (`l6d_qa`, `l6d_qb`, `l6d_qc`, `l6d_qd`), with limits
   `2 Im w₁, 2 Re w₁, 6 Re w₂, -6 Im w₂`, `w = ζ z(s)`.
8. The `(1, 1)` entry of `(X_sw - J)/r₀` at the fixed point is `r_scale` (`l6d_qa_base`), so
   `l6d_E (r, x̃) = (r a₁, b₁/a₁, c₂/a₁², d₂/a₁²)` is analytic at `(0, x̃_out)` (`l6d_analyticAt_E`)
   and equals `reinChartMap` for `r > 0` (`l6d_reinChartMap_eq`).
9. At `r = 0` the Fuller switching structure (Steps 4–5 and the χ₂₃ check at `r₀ = 0`) gives
   `F(z(x̃)) = z(s_sw(0, x̃), z(x̃), ζ)` (`l6d_poincare_eq`), so `l6d_E (0, x̃) =
   (0, fullerChartMap x̃)` (`l6d_eventually_E_divisor`).
10. **Departure from the paper.** The book builds `F⁻¹` "in similar way" backward in time and
   continues `F ∘ F⁻¹ = id` from `r₀ > 0`; that needs backward-time analogues of Lemmas
   14.2.3–14.2.4 which the book does not state. Instead: `DF(0, x̃_out)` is block triangular,
   `(r_scale, 0; *, D fullerChartMap)`, and invertible, because `det D fullerChartMap =
   D(r_scale) ≈ 4.16 × 10⁻⁷ > 0` (`l6d_jacDet_pos`, a Taylor certificate at a convergent of
   `r_scale`, as in Chapter 13); the inverse function theorem
   (`HasStrictFDerivAt.toOpenPartialHomeomorph`) and `OpenPartialHomeomorph.analyticAt_symm` give
   the analytic inverse (`lemma14_3_1`).

The χ₂₃ check missing from the book (G14.5): `χ₂₃ = r³ χ̃₂₃` with `χ̃₂₃(s, 0, x̃_out) =
24 RR(ζ - ζ², z₃(s)) = s Q(s)`, `Q > 0` (`l6d_v23_xTildeOut`); `χ̃₂₃` vanishes at `s = 0` (the chart
lies on `χ₂₃ = 0` for every sign of `r`, `l6d_switchingFn12_lieChart`), so one more division by `s`
and compactness give `χ̃₂₃ > 0` on `(0, B]` near the fixed point (`l6d_eventually_chi23_pos`).

For `hasStrictFDerivAt_extension` (FixedPointManifolds.lean): `l6d_tendsto_reinChartMap_fst_div`,
`(reinChartMap (r, x̃_out)).1 / r → r_scale` as `r → 0⁺`.
-/

@[expose] public section

namespace SmoothedPolygons

open Complex Set Filter Topology Asymptotics
open TriFuller
open scoped ContDiff

/-- The Hamiltonian `H(Z_v, X, Λ₁, Λ_R)` (`λ_cost = -1`) at a phase point `q = (X, Λ₁, Λ_R)`. -/
noncomputable def phaseHam (q : iso_PhasePt) (v : Fin 3 → ℝ) : ℝ :=
  hamiltonian (-1) q.2.1 q.2.2 q.1 v

/-- The switching time from the section `χ₂₃ = 0` with the control `e₂` (TeX 11807–11811): the least
positive zero of `χ₂₁` along the flow `t ↦ q(t)` with the control `e₂`. -/
noncomputable def reinSwitchTime (q : iso_PhasePt) : ℝ :=
  sInf {t : ℝ | 0 < t ∧ switchingFn 1 0 (iso_vertexFlow 1 q t).2.2 (iso_vertexFlow 1 q t).1 = 0}

/-- **The Reinhardt–Poincaré map** on the section `χ₂₃ = 0` (TeX 11822–11838): flow with the
control `e₂` up to the switching time and rotate by `Ad_{R⁻¹}`, which brings the wall `χ₂₁ = 0`
back to `χ₂₃ = 0` and the new control `e₁` to `e₂` (`R⁻¹ Z_{e_m} R = Z_{e_{m+1}}`). -/
noncomputable def reinPoincare (q : iso_PhasePt) : iso_PhasePt :=
  iso_adRinvPow 1 (iso_vertexFlow 1 q (reinSwitchTime q))

/-- The Reinhardt–Poincaré map in the Lie algebra chart (TeX 11683–11686), for `r > 0`. -/
noncomputable def reinChartMap (p : ℝ × (Fin 3 → ℝ)) : ℝ × (Fin 3 → ℝ) :=
  lieChartInv (reinPoincare (lieChart p))

/-- The Fuller–Poincaré map in the chart `x̃` of the exceptional divisor: `x̃ ↦ z(x̃)`, the
Fuller–Poincaré map `F` (`poincare`, landing on the wall `𝒲₂`), the rotation by `ζ` back to `𝒲₀`,
and the chart coordinates (`fullerChartInv`, invariant under the virial rescaling). -/
noncomputable def fullerChartMap (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fullerChartInv (ζ • poincare (fullerOfChart x))

/-- The fixed point `(0, x̃_out) ∈ ℝ⁴` of the extended map (Lemma 14.3.1). -/
noncomputable def chartPtOut : ℝ × (Fin 3 → ℝ) := (0, xTildeOut)

/-! ### The Fuller–Poincaré map in the chart `x̃`: conjugate to Chapter 13's `chartMap`

`x̃ ↦ (p, c, d) = l6d_ψ x̃` changes the normalization `Im z₁ = 1/2` of `fullerOfChart` to the
normalization `Re z₁ = -1` of `chartCart`: `chartCart (l6d_ψ x̃) = scale (-2/x̃₂₁) (z(x̃))`, an
algebraic identity. With the virial equivariance of `F` (`poincare_scale`) and the invariance of
`fullerChartInv` under rescalings, `fullerChartMap = l6d_φ ∘ chartMap ∘ l6d_ψ` near `x̃_out`
(`l6d_φ = l6d_ψ⁻¹`), so `x̃_out` is fixed (`chartMap_xOut`) and the derivative is conjugate to
`jacobianOut r_scale` (`hasFDerivAt_chartMap`). -/

private noncomputable def l6d_ψ (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![-1 / x 0, 2 * x 1 / (3 * x 0 ^ 2), -(2 * x 2) / (3 * x 0 ^ 2)]

private noncomputable def l6d_φ (y : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![-1 / y 0, 3 * y 1 / (2 * y 0 ^ 2), -(3 * y 2) / (2 * y 0 ^ 2)]

private lemma l6d_φ_ψ {x : Fin 3 → ℝ} (hx : x 0 ≠ 0) : l6d_φ (l6d_ψ x) = x := by
  funext i
  fin_cases i <;> simp [l6d_φ, l6d_ψ] <;> field_simp

private lemma l6d_ψ_φ {y : Fin 3 → ℝ} (hy : y 0 ≠ 0) : l6d_ψ (l6d_φ y) = y := by
  funext i
  fin_cases i <;> simp [l6d_φ, l6d_ψ] <;> field_simp

private lemma l6d_chartCart_ψ {x : Fin 3 → ℝ} (hx : x 0 ≠ 0) :
    chartCart (l6d_ψ x) = scale (-2 / x 0) (fullerOfChart x) := by
  have hx' : (x 0 : ℂ) ≠ 0 := by exact_mod_cast hx
  funext i
  fin_cases i
  · simp only [chartCart, scale, fullerOfChart, l6d_ψ]
    simp
    field_simp
    ring
  · simp only [chartCart, scale, fullerOfChart, l6d_ψ]
    simp
    field_simp
    ring
  · simp only [chartCart, scale, fullerOfChart, l6d_ψ]
    simp only [Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]
    rw [← ofReal_pow, ← ofReal_mul]
    congr 1
    field_simp
    ring

private lemma l6d_fullerChartInv_scale (z : Fin 3 → ℂ) {s : ℝ} (hs : s ≠ 0) :
    fullerChartInv (scale s z) = fullerChartInv z := by
  funext i
  fin_cases i <;>
    simp only [fullerChartInv, scale, Fin.isValue, ← ofReal_pow, Matrix.cons_val_zero, mul_re,
      ofReal_re, ofReal_im, zero_mul, sub_zero, mul_im, add_zero, Matrix.cons_val_one, Fin.zero_eta,
      Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val] <;>
  · rcases eq_or_ne (z 0).im 0 with h | h
    · simp [h]
    · field_simp

private noncomputable def l6d_N (w : Fin 3 → ℂ) : Fin 3 → ℝ :=
  ![-((w 0).re)⁻¹ * (w 0).im, (-((w 0).re)⁻¹) ^ 2 * (w 1).re, (-((w 0).re)⁻¹) ^ 2 * (w 1).im]

private lemma l6d_chartMap_eq (y : Fin 3 → ℝ) :
    chartMap y = l6d_N (ζ • poincare (chartCart y)) := rfl

private lemma l6d_fullerChartInv_eq_φ (w : Fin 3 → ℂ) (h : l6d_N w 0 ≠ 0) :
    fullerChartInv w = l6d_φ (l6d_N w) := by
  have h' : -((w 0).re)⁻¹ * (w 0).im ≠ 0 := h
  have hre : (w 0).re ≠ 0 := fun h0 ↦ h' (by simp [h0])
  have him : (w 0).im ≠ 0 := fun h0 ↦ h' (by simp [h0])
  funext i
  fin_cases i <;> simp [fullerChartInv, l6d_φ, l6d_N] <;> field_simp

private lemma l6d_fullerChartMap_eq {x : Fin 3 → ℝ} (hx : x 0 < 0) (h : chartMap (l6d_ψ x) 0 ≠ 0) :
    fullerChartMap x = l6d_φ (chartMap (l6d_ψ x)) := by
  have hs : 0 < -2 / x 0 := div_pos_of_neg_of_neg (by norm_num) hx
  rw [l6d_chartMap_eq] at h ⊢
  rw [← l6d_fullerChartInv_eq_φ _ h, l6d_chartCart_ψ hx.ne,
    (poincare_scale hs (l6d_fullerOfChart_ne_zero x)).2.2, ← scale_smul,
    l6d_fullerChartInv_scale _ hs.ne']
  rfl

private lemma l6d_xTildeOut_zero : xTildeOut 0 = -1 / (qOutCart 0).im := by
  simp [xTildeOut, fullerChartInv, qOutCart_normalization.1]

private lemma l6d_xTildeOut_zero_neg : xTildeOut 0 < 0 := by
  rw [l6d_xTildeOut_zero]
  exact div_neg_of_neg_of_pos (by norm_num) qOutCart_signs.1

private lemma l6d_ψ_xTildeOut : l6d_ψ xTildeOut = xOut := by
  have h0 := qOutCart_signs.1.ne'
  funext i
  fin_cases i <;> simp [l6d_ψ, xOut, xTildeOut, fullerChartInv, qOutCart_normalization.1] <;>
    field_simp

private lemma l6d_xOut_zero_pos : 0 < xOut 0 := qOutCart_signs.1

private lemma l6d_φ_xOut : l6d_φ xOut = xTildeOut := by
  rw [← l6d_ψ_xTildeOut, l6d_φ_ψ l6d_xTildeOut_zero_neg.ne]

/-- `x̃_out` is a fixed point of the Fuller–Poincaré map in the chart (Lemma 13.5.2: `F(q_out) =
ζ² (r_scale q_out,₁, r_scale² q_out,₂, r_scale³ q_out,₃)`, `poincare_qOutCart`, with
`fullerChartInv` invariant under rescalings). -/
theorem fullerChartMap_xTildeOut : fullerChartMap xTildeOut = xTildeOut := by
  have h0 : chartMap (l6d_ψ xTildeOut) 0 ≠ 0 := by
    rw [l6d_ψ_xTildeOut, chartMap_xOut]
    exact qOutCart_signs.1.ne'
  rw [l6d_fullerChartMap_eq l6d_xTildeOut_zero_neg h0, l6d_ψ_xTildeOut, chartMap_xOut,
    l6d_φ_xOut]

private lemma l6d_differentiableAt_ψ {x : Fin 3 → ℝ} (hx : x 0 ≠ 0) :
    DifferentiableAt ℝ l6d_ψ x := by
  rw [differentiableAt_pi]
  intro i
  fin_cases i <;>
    simp only [l6d_ψ, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val] <;>
    fun_prop (disch := simp [hx])

private lemma l6d_differentiableAt_φ {y : Fin 3 → ℝ} (hy : y 0 ≠ 0) :
    DifferentiableAt ℝ l6d_φ y := by
  rw [differentiableAt_pi]
  intro i
  fin_cases i <;>
    simp only [l6d_φ, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val] <;>
    fun_prop (disch := simp [hy])

private lemma l6d_fullerChartMap_eventuallyEq :
    fullerChartMap =ᶠ[𝓝 xTildeOut] l6d_φ ∘ chartMap ∘ l6d_ψ := by
  have hψc : ContinuousAt l6d_ψ xTildeOut :=
    (l6d_differentiableAt_ψ l6d_xTildeOut_zero_neg.ne).continuousAt
  have hc : ContinuousAt (fun x ↦ chartMap (l6d_ψ x) 0) xTildeOut := by
    have hJ : ContinuousAt chartMap (l6d_ψ xTildeOut) := by
      rw [l6d_ψ_xTildeOut]; exact hasFDerivAt_chartMap.continuousAt
    exact (continuous_apply 0).continuousAt.comp (hJ.comp hψc)
  have h0 : chartMap (l6d_ψ xTildeOut) 0 ≠ 0 := by
    rw [l6d_ψ_xTildeOut, chartMap_xOut]
    exact qOutCart_signs.1.ne'
  filter_upwards [hc.eventually_ne h0,
    (continuous_apply 0).continuousAt.eventually_lt continuousAt_const l6d_xTildeOut_zero_neg]
    with x hx hneg
  exact l6d_fullerChartMap_eq hneg hx


/-- The derivative of the Fuller–Poincaré map in the chart, conjugate to `jacobianOut r_scale`. -/
private lemma l6d_fullerChartMap_deriv :
    HasFDerivAt fullerChartMap ((fderiv ℝ l6d_φ xOut).comp
      ((Matrix.toLin' (jacobianOut rScale)).toContinuousLinearMap.comp
        (fderiv ℝ l6d_ψ xTildeOut))) xTildeOut ∧
      (fderiv ℝ l6d_φ xOut).comp (fderiv ℝ l6d_ψ xTildeOut) = ContinuousLinearMap.id ℝ _ ∧
      (fderiv ℝ l6d_ψ xTildeOut).comp (fderiv ℝ l6d_φ xOut) = ContinuousLinearMap.id ℝ _ := by
  set Dψ := fderiv ℝ l6d_ψ xTildeOut
  set Dφ := fderiv ℝ l6d_φ xOut
  set JL := (Matrix.toLin' (jacobianOut rScale)).toContinuousLinearMap
  have hψ : HasFDerivAt l6d_ψ Dψ xTildeOut :=
    (l6d_differentiableAt_ψ l6d_xTildeOut_zero_neg.ne).hasFDerivAt
  have hφ : HasFDerivAt l6d_φ Dφ xOut :=
    (l6d_differentiableAt_φ l6d_xOut_zero_pos.ne').hasFDerivAt
  have hJ : HasFDerivAt chartMap JL (l6d_ψ xTildeOut) := by
    rw [l6d_ψ_xTildeOut]; exact hasFDerivAt_chartMap
  have hφ' : HasFDerivAt l6d_φ Dφ (chartMap (l6d_ψ xTildeOut)) := by
    rw [l6d_ψ_xTildeOut, chartMap_xOut]; exact hφ
  have hcomp : HasFDerivAt (l6d_φ ∘ chartMap ∘ l6d_ψ) (Dφ.comp (JL.comp Dψ)) xTildeOut :=
    hφ'.comp xTildeOut (hJ.comp xTildeOut hψ)
  refine ⟨hcomp.congr_of_eventuallyEq l6d_fullerChartMap_eventuallyEq, ?_, ?_⟩
  · have hφ1 : HasFDerivAt l6d_φ Dφ (l6d_ψ xTildeOut) := by rw [l6d_ψ_xTildeOut]; exact hφ
    refine (hφ1.comp xTildeOut hψ).unique ((hasFDerivAt_id _).congr_of_eventuallyEq ?_)
    filter_upwards [(continuous_apply 0).continuousAt.eventually_ne
      (l6d_xTildeOut_zero_neg.ne : xTildeOut 0 ≠ 0)] with x hx
    exact l6d_φ_ψ hx
  · have hψ1 : HasFDerivAt l6d_ψ Dψ (l6d_φ xOut) := by rw [l6d_φ_xOut]; exact hψ
    refine (hψ1.comp xOut hφ).unique ((hasFDerivAt_id _).congr_of_eventuallyEq ?_)
    filter_upwards [(continuous_apply 0).continuousAt.eventually_ne
      (l6d_xOut_zero_pos.ne' : xOut 0 ≠ 0)] with y hy
    exact l6d_ψ_φ hy

/-- **The linearization of the Fuller–Poincaré map at `q_out` is a contraction** ("We have seen
that the linearization of the Fuller–Poincaré map `F` near the fixed point is a contraction on the
three dimensional exceptional divisor", TeX 11912–11914): `fullerChartMap` is differentiable at
`x̃_out` and every complex eigenvalue of its derivative has modulus `< 1/10` (the bound quoted at
TeX 11960–11961). Proof: the change of normalization `l6d_ψ` (`Im z₁ = 1/2` to `Re z₁ = -1`,
`chartCart (l6d_ψ x̃) = scale (-2/x̃₂₁) z(x̃)`) is rational with rational inverse `l6d_φ` and
conjugates `fullerChartMap` to Chapter 13's `chartMap` near `x̃_out` (`poincare_scale`, the
rescaling invariance of `fullerChartInv`; `chartOf` is not needed); the eigenvalues are those of
`jacobianOut r_scale` (`hasFDerivAt_chartMap`, `LinearEquiv.charpoly_conj`,
`norm_lt_of_aeval_charpoly_jacobianOut_eq_zero`). -/
theorem hasFDerivAt_fullerChartMap :
    ∃ D : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ), HasFDerivAt fullerChartMap D xTildeOut ∧
      ∀ μ : ℂ, Polynomial.aeval μ (LinearMap.charpoly (D : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ))) = 0 →
        ‖μ‖ < 1 / 10 := by
  obtain ⟨hD, h1, h2⟩ := l6d_fullerChartMap_deriv
  set Dψ := fderiv ℝ l6d_ψ xTildeOut
  set Dφ := fderiv ℝ l6d_φ xOut
  set JL := (Matrix.toLin' (jacobianOut rScale)).toContinuousLinearMap
  refine ⟨Dφ.comp (JL.comp Dψ), hD, ?_⟩
  let e : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ) :=
    LinearEquiv.ofLinearMap (Dψ : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) Dφ
      (LinearMap.ext fun v ↦ by
        simpa using congrArg (fun L : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) ↦ L v) h2)
      (LinearMap.ext fun v ↦ by
        simpa using congrArg (fun L : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) ↦ L v) h1)
  have hconj : ((Dφ.comp (JL.comp Dψ) : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)) :
      (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) = e.symm.conj (Matrix.toLin' (jacobianOut rScale)) := by
    refine LinearMap.ext fun v ↦ ?_
    simp [LinearEquiv.conj_apply, e, JL]
  intro μ hμ
  rw [hconj, LinearEquiv.charpoly_conj, Matrix.charpoly_toLin'] at hμ
  exact norm_lt_of_aeval_charpoly_jacobianOut_eq_zero μ hμ

/-! ### The derivative of the Fuller–Poincaré map in the chart is invertible

`det DF = D(r_scale) ≈ 4.16 × 10⁻⁷ > 0` (`jacDet`): a Taylor certificate at the convergent
`c = 3961388236/631380705` of `r_scale` (`|r_scale - c| ≤ 10⁻¹⁸`, from `rScale_fine_bounds`), as
in the eigenvalue certificate of Chapter 13: `D(r) = d₀ - (e₁ s + ⋯ + e₅ s⁵)`, `s = r - c`, with
`d₀ ≈ 4.1626 × 10⁻⁷` and `0 < e_k ≤ 6.1 × 10⁸`. -/

private lemma l6d_rScale_near : |rScale - 3961388236 / 631380705| ≤ 1 / 10 ^ 18 := by
  obtain ⟨h₁, h₂⟩ := rScale_fine_bounds
  rw [abs_le]
  constructor <;> norm_num at h₁ h₂ ⊢ <;> linarith

private lemma l6d_jacDet_pos : 0 < jacDet rScale := by
  set s := rScale - 3961388236 / 631380705 with hs
  have key : jacDet rScale =
      (8353169621850975361426051648127994871 / 20067188224173096038624268051085539385438125 : ℝ)
      - ((3868275290048577909729808245973544531917091 / 6356604839285703556184621780954025 : ℝ)
          * s
        + (3666401634777128046521203452420181 / 10067784442804129651356105 : ℝ) * s ^ 2
        + (1307777183502845285012875 / 15945663785851881 : ℝ) * s ^ 3
        + (1039194778489585 / 126276141 : ℝ) * s ^ 4 + 310195 * s ^ 5) := by
    rw [hs]; unfold jacDet; ring
  have hsb : |s| ≤ 1 / 10 ^ 18 := l6d_rScale_near
  have hs1 : |s| ≤ 1 := hsb.trans (by norm_num)
  have hk : ∀ k : ℕ, k ≠ 0 → s ^ k ≤ 1 / 10 ^ 18 := fun k hk ↦ (le_abs_self _).trans (by
    rw [abs_pow]; exact (pow_le_of_le_one (abs_nonneg s) hs1 hk).trans hsb)
  have b1 := hk 1 one_ne_zero
  have b2 := hk 2 two_ne_zero
  have b3 := hk 3 three_ne_zero
  have b4 := hk 4 four_ne_zero
  have b5 := hk 5 (by norm_num)
  rw [pow_one] at b1
  rw [key]
  nlinarith

private lemma l6d_det_jacobianOut_ne_zero : (jacobianOut rScale).det ≠ 0 := by
  rw [Matrix.det_eq_sign_charpoly_coeff, charpoly_jacobianOut]
  simp only [Fintype.card_fin, Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_X_pow,
    OfNat.zero_ne_ofNat, ↓reduceIte, Polynomial.mul_coeff_zero, Polynomial.coeff_C_zero, mul_zero,
    sub_self, Polynomial.coeff_X, one_ne_zero, add_zero, zero_sub, mul_neg]
  norm_num
  exact l6d_jacDet_pos.ne'

/-- The derivative of the Fuller–Poincaré map at `x̃_out` is injective (`det ≠ 0`). -/
private lemma l6d_fderiv_fullerChartMap_injective :
    Function.Injective (fderiv ℝ fullerChartMap xTildeOut) := by
  obtain ⟨hD, h1, h2⟩ := l6d_fullerChartMap_deriv
  rw [hD.fderiv]
  intro v w hvw
  have hψ : ∀ u, fderiv ℝ l6d_ψ xTildeOut (fderiv ℝ l6d_φ xOut u) = u := fun u ↦ by
    simpa using congrArg (fun L : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) ↦ L u) h2
  have hφ : ∀ u, fderiv ℝ l6d_φ xOut (fderiv ℝ l6d_ψ xTildeOut u) = u := fun u ↦ by
    simpa using congrArg (fun L : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) ↦ L u) h1
  have h3 := congrArg (fderiv ℝ l6d_ψ xTildeOut) hvw
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, hψ,
    LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply] at h3
  have h4 : (jacobianOut rScale).mulVec
      (fderiv ℝ l6d_ψ xTildeOut v - fderiv ℝ l6d_ψ xTildeOut w) = 0 := by
    rw [Matrix.mulVec_sub, h3, sub_self]
  have h5 := Matrix.eq_zero_of_mulVec_eq_zero l6d_det_jacobianOut_ne_zero h4
  rw [sub_eq_zero] at h5
  rw [← hφ v, ← hφ w, h5]

/-- **Step 3 of the proof of Lemma 14.3.1** (TeX 11800–11806): "By Lemma 14.2.4, by division of
power series, the function `χ₂₁(X(s r₀), Λ₁(s r₀), Λ_R(s r₀))/r₀³` extends to an analytic function
`χ̃₂₁(s, r₀, x̃₀)` in a neighborhood of `r₀ = 0`", whose value at `r₀ = 0` is the Fuller switching
function `24 RR(ζ - 1, z₃(s))` of Lemma 14.2.4.

Proof: `(s, r₀, x̃) ↦ χ₂₁(X(s r₀), Λ₁(s r₀), Λ_R(s r₀))` is analytic near `(s, 0, x̃)` (steps 1–2 of
the module docstring) and `O(r₀³)` for each fixed `(s, x̃)` (Lemma 14.2.4, `lemma14_2_4`, and the
continuity in `r₀` of the right side); `AnalyticAt.exists_eq_pow_smul_of_isBigO` with `k = 3`
(coordinates reordered to `(r₀, (s, x̃))`) gives the analytic `χ̃₂₁`, and its value at `r₀ = 0` is
the limit of Lemma 14.2.4. -/
theorem analyticAt_rescaledChi :
    ∃ χ : ℝ × ℝ × (Fin 3 → ℝ) → ℝ, ∀ (s : ℝ) (x : Fin 3 → ℝ),
      AnalyticAt ℝ χ (s, 0, x) ∧
      χ (s, 0, x) = 24 * RR (ζ - 1) (flow s (fullerOfChart x) ζ 2) ∧
      ∀ᶠ p in 𝓝 (s, (0 : ℝ), x), p.2.1 ≠ 0 →
        χ p = switchingFn 1 0 (iso_vertexFlow 1 (lieChart (p.2.1, p.2.2)) (p.1 * p.2.1)).2.2
          (iso_vertexFlow 1 (lieChart (p.2.1, p.2.2)) (p.1 * p.2.1)).1 / p.2.1 ^ 3 := by
  have hv : ∀ s x, (fun r ↦ l6d_chiRaw 1 0 (s, r, x) -
      r ^ 3 * (24 * RR (ζ - 1) (flow s (fullerOfChart x) ζ 2))) =O[𝓝[>] 0] (fun r ↦ r ^ 4) := by
    intro s x
    refine (lemma14_2_4 x s).congr_left fun r ↦ ?_
    simp only [l6d_chiRaw, l6d_flowPt]
    ring
  refine ⟨l6d_chiT 1 0 (fun p ↦ 24 * RR (ζ - 1) (flow p.1 (fullerOfChart p.2) ζ 2)),
    fun s x ↦ ⟨l6d_analyticAt_chiT 1 0 hv s x, by simp [l6d_chiT], ?_⟩⟩
  refine Eventually.of_forall fun p hp ↦ ?_
  simp only [l6d_chiT, hp, ite_false, l6d_chiRaw, l6d_flowPt]

/-! ### The Reinhardt–Poincaré map near the fixed point (Steps 5–8)

For `r > 0` near the fixed point the switching time of `reinPoincare` is `r s_sw(r, x̃)`
(`l6d_reinSwitchTime_eq`: `χ₂₁ = r³ χ̃₂₁(t/r, r, x̃)`, whose least positive zero is `s_sw`), so the
Reinhardt–Poincaré map in the chart is the analytic map `l6d_E` (`l6d_reinChartMap_eq`). -/

attribute [local fun_prop] analyticAt_fst analyticAt_snd l6d_analyticAt_pi_apply

private lemma l6d_switchingFn_flow_eq {i j : Fin 3} {q : ℝ × (Fin 3 → ℝ)} (hr : q.1 ≠ 0)
    (t : ℝ) : switchingFn i j (iso_vertexFlow 1 (lieChart q) t).2.2
      (iso_vertexFlow 1 (lieChart q) t).1 = l6d_chiRaw i j (t / q.1, q.1, q.2) := by
  simp only [l6d_chiRaw, l6d_flowPt, div_mul_cancel₀ t hr]

/-- The switching time of the Reinhardt–Poincaré map is `r s_sw(r, x̃)` for `r > 0` near the fixed
point (TeX 11807–11811). -/
private lemma l6d_reinSwitchTime_eq : ∃ δ > 0, δ < l6d_S ∧ ∀ᶠ q in 𝓝 chartPtOut, 0 < q.1 →
    reinSwitchTime (lieChart q) = q.1 * l6d_sSw q ∧
      l6d_sSw q ∈ Ioo (l6d_S - δ) (l6d_S + δ) ∧ l6d_Φ (q, l6d_sSw q) = 0 ∧
      (∀ s ∈ Ico 0 (l6d_sSw q), 0 < l6d_Φ (q, s)) ∧
      (∀ s ∈ Ioc (l6d_sSw q) (l6d_S + δ), l6d_Φ (q, s) < 0) := by
  obtain ⟨δ, hδ, hδS, hZ⟩ := l6d_zero_structure
  refine ⟨δ, hδ, hδS, ?_⟩
  filter_upwards [hZ] with q ⟨hσ, hz, hpos, hneg⟩ hr
  refine ⟨?_, hσ, hz, hpos, hneg⟩
  have hσ0 : 0 < l6d_sSw q := by linarith [hσ.1]
  have hval : ∀ t, switchingFn 1 0 (iso_vertexFlow 1 (lieChart q) t).2.2
      (iso_vertexFlow 1 (lieChart q) t).1 = q.1 ^ 3 * l6d_Φ (q, t / q.1) := by
    intro t
    rw [l6d_switchingFn_flow_eq hr.ne', l6d_chiRaw_eq_chi21 hr.ne']
    rfl
  refine IsLeast.csInf_eq ⟨⟨mul_pos hr hσ0, ?_⟩, ?_⟩
  · rw [hval, mul_div_cancel_left₀ _ hr.ne', hz, mul_zero]
  · rintro t ⟨ht0, ht⟩
    by_contra hlt
    push Not at hlt
    have hs : t / q.1 ∈ Ico 0 (l6d_sSw q) :=
      ⟨div_nonneg ht0.le hr.le, by rw [div_lt_iff₀ hr]; linarith⟩
    have := hpos _ hs
    rw [hval] at ht
    exact (mul_pos (pow_pos hr 3) this).ne' ht

/-- For `r > 0` near the fixed point the Reinhardt–Poincaré map is `Ad_{R⁻¹}` of the flow point at
the switching time. -/
private lemma l6d_reinPoincare_eq {q : ℝ × (Fin 3 → ℝ)}
    (h : reinSwitchTime (lieChart q) = q.1 * l6d_sSw q) :
    reinPoincare (lieChart q) = l6d_Xi (l6d_sSw q, q.1, q.2) := by
  simp only [reinPoincare, h, l6d_Xi, l6d_flowPt, mul_comm (l6d_sSw q)]

private lemma l6d_reinChartMap_eq {q : ℝ × (Fin 3 → ℝ)} (hr : 0 < q.1)
    (h : reinSwitchTime (lieChart q) = q.1 * l6d_sSw q) : reinChartMap q = l6d_E q := by
  rw [reinChartMap, l6d_reinPoincare_eq h, l6d_E_eq_lieChartInv hr.ne']

/-- **The radial scaling factor** (TeX 11849–11856): `(F(r, x̃_out))₁ / r → r_scale` as `r → 0⁺`
(the `(1, 1)` entry of `(X_sw - J)/r₀` at the fixed point). This gives `∂_r F₁ = r_scale` at the
fixed point for every analytic extension (`hasStrictFDerivAt_extension`). -/
theorem l6d_tendsto_reinChartMap_fst_div :
    Tendsto (fun r ↦ (reinChartMap (r, xTildeOut)).1 / r) (𝓝[>] 0) (𝓝 rScale) := by
  obtain ⟨δ, -, -, hev⟩ := l6d_reinSwitchTime_eq
  have hc : ContinuousAt (fun r : ℝ ↦ (r, xTildeOut)) 0 := by fun_prop
  have hev' : ∀ᶠ r in 𝓝[>] (0 : ℝ), (reinChartMap (r, xTildeOut)).1 / r =
      l6d_qa (l6d_sSw (r, xTildeOut), r, xTildeOut) := by
    filter_upwards [nhdsWithin_le_nhds (hc.eventually hev), self_mem_nhdsWithin] with r hr hr0
    have hr0' : (0 : ℝ) < r := hr0
    rw [l6d_reinChartMap_eq hr0' (hr hr0').1, l6d_E]
    field_simp
  have hqa : ContinuousAt (fun r : ℝ ↦ l6d_qa (l6d_sSw (r, xTildeOut), r, xTildeOut)) 0 := by
    have h1 := ((l6d_analyticAt_divided l6d_S xTildeOut).1.comp_of_eq
      l6d_analyticAt_sSw_triple l6d_sSw_triple_base).continuousAt
    exact h1.comp_of_eq hc rfl
  have hval : l6d_qa (l6d_sSw (0, xTildeOut), 0, xTildeOut) = rScale := by
    rw [l6d_sSw_base, l6d_qa_base]
  rw [← hval]
  exact (hqa.tendsto.mono_left nhdsWithin_le_nhds).congr' (hev'.mono fun r h ↦ h.symm)

/-- The Hamiltonian under `Ad_{R⁻¹}`: `H(e₂)(Ad_{R⁻¹} q) = H(e₁)(q)` (`R⁻¹ Z_{e₁} R = Z_{e₂}`,
`R⁻¹ J R = J`). -/
private lemma l6d_hamiltonian_adRinv (q : iso_PhasePt) :
    hamiltonian (-1) (iso_adRinvPow 1 q).2.1 (iso_adRinvPow 1 q).2.2 (iso_adRinvPow 1 q).1
      (vertex 1) = hamiltonian (-1) q.2.1 q.2.2 q.1 (vertex 0) := by
  have hZ : R⁻¹ ^ 1 * controlMatrix (vertex 0) * R ^ 1 = controlMatrix (vertex 1) := by
    rw [poly_conj_pow_vertex 1 0]; rfl
  have hC : R ^ 1 * R⁻¹ ^ 1 = 1 := poly_Rpow_mul_Rinvpow 1
  simp only [l6d_hamiltonian_eq, iso_adRinvPow]
  rw [← poly_controlP_conj hC hZ, poly_traceForm_conj hC]
  congr 1
  rw [← poly_traceForm_conj hC (q.2.1 + (3 / 2 : ℝ) • J) q.1, poly_conj_add, poly_conj_smul]
  simp only [pow_one, l6d_Rinv_J_R]

/-- `χ₂₃(Ad_{R⁻¹} q) = -χ₂₁(q)`. -/
private lemma l6d_switchingFn12_adRinv (q : iso_PhasePt) :
    switchingFn 1 2 (iso_adRinvPow 1 q).2.2 (iso_adRinvPow 1 q).1 = -switchingFn 1 0 q.2.2 q.1 := by
  have h := irt_chi_conj 1 0 1 q
  have h1 : ((0 : Fin 3) + ⟨1 % 3, Nat.mod_lt _ (by norm_num)⟩) = 1 := by decide
  have h2 : ((1 : Fin 3) + ⟨1 % 3, Nat.mod_lt _ (by norm_num)⟩) = 2 := by decide
  rw [h1, h2] at h
  rw [show switchingFn 1 2 (iso_adRinvPow 1 q).2.2 (iso_adRinvPow 1 q).1 =
    irt_chi 1 2 (iso_adRinvPow 1 q) from rfl, h, irt_chi_antisymm]
  rfl

/-- The image point of a chart point of `H*` is a phase point of the blow-up up to the sheet
conditions (traceless, `det X = 1`, `det Λ₁ = 9/4`, `⟨X, Λ_R⟩ = 0`). -/
private lemma l6d_Xi_constraints {q : ℝ × (Fin 3 → ℝ)} (hq : q ∈ lieChartDomain) (σ : ℝ) :
    (l6d_Xi (σ, q.1, q.2)).1.trace = 0 ∧ (l6d_Xi (σ, q.1, q.2)).2.1.trace = 0 ∧
      (l6d_Xi (σ, q.1, q.2)).2.2.trace = 0 ∧ (l6d_Xi (σ, q.1, q.2)).1.det = 1 ∧
      (l6d_Xi (σ, q.1, q.2)).2.1.det = 9 / 4 ∧
      traceForm (l6d_Xi (σ, q.1, q.2)).1 (l6d_Xi (σ, q.1, q.2)).2.2 = 0 := by
  obtain ⟨⟨-, -, -, hdX, hdL, hXR, -, -⟩, -⟩ := lieChart_spec hq
  obtain ⟨t1, t2, t3⟩ := l6d_flowPt_traceless (σ, q.1, q.2)
  have hC : R ^ 1 * R⁻¹ ^ 1 = 1 := poly_Rpow_mul_Rinvpow 1
  simp only [l6d_Xi, iso_adRinvPow]
  refine ⟨by rw [poly_trace_conj hC, t1], by rw [poly_trace_conj hC, t2],
    by rw [poly_trace_conj hC, t3], ?_, ?_, ?_⟩
  · rw [poly_det_conj hC, l6d_flowPt, l6d_vertexFlow_det_fst]; exact hdX
  · rw [poly_det_conj hC, l6d_flowPt, l6d_vertexFlow_det_snd]; exact hdL
  · rw [poly_traceForm_conj hC, l6d_flowPt, l6d_vertexFlow_traceForm]; exact hXR

/-- The image point, as a function of the chart point. -/
private noncomputable def l6d_img (q : ℝ × (Fin 3 → ℝ)) : iso_PhasePt :=
  l6d_Xi (l6d_sSw q, q.1, q.2)

private lemma l6d_continuousAt_img_entries (i j : Fin 2) :
    ContinuousAt (fun q ↦ (l6d_img q).1 i j) chartPtOut ∧
      ContinuousAt (fun q ↦ (l6d_img q).2.1 i j) chartPtOut := by
  obtain ⟨h1, h2⟩ := l6d_MatAn_Xi l6d_S xTildeOut
  exact ⟨((h1 i j).comp_of_eq l6d_analyticAt_sSw_triple l6d_sSw_triple_base).continuousAt,
    ((h2 i j).comp_of_eq l6d_analyticAt_sSw_triple l6d_sSw_triple_base).continuousAt⟩

private lemma l6d_img_base : l6d_img chartPtOut = (J, (-(3 / 2) : ℝ) • J, 0) := by
  rw [l6d_img, chartPtOut]
  simp only [l6d_sSw_base, l6d_Xi_zero]

/-- Near the fixed point the image point is near `(J, -(3/2) J)`: the sheet conditions and the
star inequalities hold, and its `(1, 1)` entry is `r a₁` with `a₁` near `r_scale`. -/
private lemma l6d_eventually_img :
    ∀ᶠ q in 𝓝 chartPtOut, (l6d_img q).1 0 1 < (l6d_img q).1 1 0 ∧
      (l6d_img q).2.1 1 0 < (l6d_img q).2.1 0 1 ∧ 0 < ρ₀ (l6d_img q).1 ∧
      0 < ρ₁ (l6d_img q).1 ∧ 0 < ρ₂ (l6d_img q).1 ∧
      0 < l6d_qa (l6d_sSw q, q.1, q.2) := by
  have h3 : (0 : ℝ) < √3 := by positivity
  have c01 := (l6d_continuousAt_img_entries 0 1).1
  have c10 := (l6d_continuousAt_img_entries 1 0).1
  have c00 := (l6d_continuousAt_img_entries 0 0).1
  have d01 := (l6d_continuousAt_img_entries 0 1).2
  have d10 := (l6d_continuousAt_img_entries 1 0).2
  have hb := l6d_img_base
  have v01 : (l6d_img chartPtOut).1 0 1 = -1 := by rw [hb]; simp [J]
  have v10 : (l6d_img chartPtOut).1 1 0 = 1 := by rw [hb]; simp [J]
  have v00 : (l6d_img chartPtOut).1 0 0 = 0 := by rw [hb]; simp [J]
  have w01 : (l6d_img chartPtOut).2.1 0 1 = 3 / 2 := by rw [hb]; simp [J]
  have w10 : (l6d_img chartPtOut).2.1 1 0 = -(3 / 2) := by rw [hb]; simp [J]
  have hqa : ContinuousAt (fun q : ℝ × (Fin 3 → ℝ) ↦ l6d_qa (l6d_sSw q, q.1, q.2)) chartPtOut :=
    ((l6d_analyticAt_divided l6d_S xTildeOut).1.comp_of_eq l6d_analyticAt_sSw_triple
      l6d_sSw_triple_base).continuousAt
  have hqa0 : l6d_qa (l6d_sSw chartPtOut, chartPtOut.1, chartPtOut.2) = rScale := by
    rw [chartPtOut, l6d_sSw_base, l6d_qa_base]
  have hρ₀ : ContinuousAt (fun q ↦ ρ₀ (l6d_img q).1) chartPtOut := by
    unfold ρ₀; exact (c10.add (continuousAt_const.mul c00)).div_const _
  have hρ₁ : ContinuousAt (fun q ↦ ρ₁ (l6d_img q).1) chartPtOut := by
    unfold ρ₁; exact (c10.sub (continuousAt_const.mul c00)).div_const _
  have hρ₂ : ContinuousAt (fun q ↦ ρ₂ (l6d_img q).1) chartPtOut := by
    unfold ρ₂; exact ((continuousAt_const.mul c01).add c10).neg.div_const _
  have e1 : (l6d_img chartPtOut).1 0 1 < (l6d_img chartPtOut).1 1 0 := by rw [v01, v10]; norm_num
  have e2 : (l6d_img chartPtOut).2.1 1 0 < (l6d_img chartPtOut).2.1 0 1 := by
    rw [w01, w10]; norm_num
  have e3 : (0 : ℝ) < ρ₀ (l6d_img chartPtOut).1 := by simp only [ρ₀, v10, v00]; positivity
  have e4 : (0 : ℝ) < ρ₁ (l6d_img chartPtOut).1 := by
    simp only [ρ₁, v10, v00, mul_zero, sub_zero]; positivity
  have e5 : (0 : ℝ) < ρ₂ (l6d_img chartPtOut).1 := by
    simp only [ρ₂, v10, v01]; norm_num
  have e6 : (0 : ℝ) < l6d_qa (l6d_sSw chartPtOut, chartPtOut.1, chartPtOut.2) := by
    rw [hqa0]; linarith [rScale_spec.1]
  filter_upwards [c01.eventually_lt c10 e1, d10.eventually_lt d01 e2,
    continuousAt_const.eventually_lt hρ₀ e3, continuousAt_const.eventually_lt hρ₁ e4,
    continuousAt_const.eventually_lt hρ₂ e5, continuousAt_const.eventually_lt hqa e6]
    with q h1 h2 h3 h4 h5 h6
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- Chart points with small `r > 0` near `x̃_out` lie in `H*`. -/
private lemma l6d_eventually_mem_lieChartDomain :
    ∀ᶠ q in 𝓝 chartPtOut, 0 < q.1 → q ∈ lieChartDomain := by
  have hc0 : ContinuousAt (fun q : ℝ × (Fin 3 → ℝ) ↦ q.2 0) chartPtOut := by fun_prop
  have hc2 : ContinuousAt (fun q : ℝ × (Fin 3 → ℝ) ↦ q.1 ^ 2 * q.2 2) chartPtOut := by fun_prop
  set ρ := 1 / (√3 - xTildeOut 0 + 1)
  have hx := l6d_xTildeOut_zero_neg
  have h3' : (0 : ℝ) < √3 := by positivity
  have hρ : 0 < ρ := one_div_pos.2 (by linarith)
  have e1 : (chartPtOut).1 < ρ := by simpa [chartPtOut] using hρ
  have e2 : xTildeOut 0 - 1 < (chartPtOut).2 0 := by simp [chartPtOut]
  have e3 : (chartPtOut).1 ^ 2 * (chartPtOut).2 2 < 3 / 2 := by simp [chartPtOut]
  have hr : ∀ᶠ q in 𝓝 chartPtOut, q.1 < ρ :=
    (by fun_prop : ContinuousAt (fun q : ℝ × (Fin 3 → ℝ) ↦ q.1) chartPtOut).eventually_lt
      continuousAt_const e1
  filter_upwards [hr, continuousAt_const.eventually_lt hc0 e2,
    hc2.eventually_lt continuousAt_const e3] with q hq1 hq3 hq4 hpos
  refine ⟨hpos, ?_, by linarith [hq4]⟩
  have h3 : (0 : ℝ) < √3 := by positivity
  have hden : 0 < √3 - xTildeOut 0 + 1 := by linarith
  have : √3 - xTildeOut 0 + 1 < 1 / q.1 := by
    rw [lt_one_div hden hpos]
    simpa [ρ] using hq1
  linarith

/-- **The switching structure near the fixed point** (TeX 11807–11813, with the χ₂₃ check of
G14.5): for chart points `p` near `(0, x̃_out)` with `r > 0`, along the flow with the control `e₂`
from `q = lieChart p` the control `e₂` is the strict maximizer of the Hamiltonian among the
vertices on `(0, t_sw(q))` (so it is optimal on `[0, t_sw(q)]`), `t_sw(q) > 0`, `e₁` beats it at
times arbitrarily close to `t_sw(q)` on the right, and the image `reinPoincare q` is again a
chart point of `H*` (so `reinChartMap p` is its chart coordinate). Hence an extremal through `q`
on the section switches next at `q(t_sw)`, and `reinPoincare` maps consecutive switching
points. -/
theorem eventually_isSwitch_reinSwitchTime :
    ∀ᶠ p in 𝓝[{p | 0 < p.1}] chartPtOut,
      0 < reinSwitchTime (lieChart p) ∧
      (∀ t ∈ Ioo 0 (reinSwitchTime (lieChart p)), ∀ j : Fin 3, j ≠ 1 →
        phaseHam (iso_vertexFlow 1 (lieChart p) t) (vertex j) <
          phaseHam (iso_vertexFlow 1 (lieChart p) t) (vertex 1)) ∧
      (∀ ε > 0, ∃ t ∈ Ioo (reinSwitchTime (lieChart p)) (reinSwitchTime (lieChart p) + ε),
        phaseHam (iso_vertexFlow 1 (lieChart p) t) (vertex 1) <
          phaseHam (iso_vertexFlow 1 (lieChart p) t) (vertex 0)) ∧
      reinChartMap p ∈ lieChartDomain ∧ lieChart (reinChartMap p) = reinPoincare (lieChart p) := by
  obtain ⟨δ, hδ, hδS, hev⟩ := l6d_reinSwitchTime_eq
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hev, l6d_eventually_chi23_pos (l6d_S + δ), l6d_eventually_img,
    l6d_eventually_mem_lieChartDomain] with q hq h23q himg hdom hr
  have hr : 0 < q.1 := hr
  obtain ⟨hsw, hσ, hz, hpos, hneg⟩ := hq hr
  have hdom' := hdom hr
  set σ := l6d_sSw q with hσdef
  have hσ0 : 0 < σ := by linarith [hσ.1]
  have hr0 : q.1 ≠ 0 := hr.ne'
  -- the switching functions along the flow, in rescaled time
  have h21 : ∀ t, switchingFn 1 0 (iso_vertexFlow 1 (lieChart q) t).2.2
      (iso_vertexFlow 1 (lieChart q) t).1 = q.1 ^ 3 * l6d_Φ (q, t / q.1) := fun t ↦ by
    rw [l6d_switchingFn_flow_eq hr0, l6d_chiRaw_eq_chi21 hr0]; rfl
  have h23 : ∀ t, switchingFn 1 2 (iso_vertexFlow 1 (lieChart q) t).2.2
      (iso_vertexFlow 1 (lieChart q) t).1 = q.1 ^ 3 * l6d_chi23 (t / q.1, q.1, q.2) := fun t ↦ by
    rw [l6d_switchingFn_flow_eq hr0, l6d_chiRaw_eq_chi23 hr0]
  have hH : ∀ (y : iso_PhasePt) (i j : Fin 3), phaseHam y (vertex i) - phaseHam y (vertex j) =
      switchingFn i j y.2.2 y.1 := fun y i j ↦ l6d_hamiltonian_sub _ _ _ i j
  have hr3 : 0 < q.1 ^ 3 := pow_pos hr 3
  refine ⟨by rw [hsw]; positivity, ?_, ?_, ?_⟩
  · intro t ht j hj
    rw [hsw] at ht
    have hs0 : 0 < t / q.1 := div_pos ht.1 hr
    have hs1 : t / q.1 < σ := by rw [div_lt_iff₀ hr]; linarith [ht.2]
    fin_cases j
    · have h1 := hH (iso_vertexFlow 1 (lieChart q) t) 1 0
      rw [h21] at h1
      have := hpos (t / q.1) ⟨hs0.le, hs1⟩
      have := mul_pos hr3 this
      simp only [Fin.zero_eta, Fin.isValue]
      linarith
    · exact absurd rfl hj
    · have h1 := hH (iso_vertexFlow 1 (lieChart q) t) 1 2
      rw [h23] at h1
      have := h23q (t / q.1) ⟨hs0, by linarith [hσ.2]⟩
      have := mul_pos hr3 this
      simp only [Fin.reduceFinMk, Fin.isValue]
      linarith
  · intro ε hε
    rw [hsw]
    set s := σ + min (ε / q.1) (l6d_S + δ - σ) / 2 with hs
    have hm : 0 < min (ε / q.1) (l6d_S + δ - σ) := lt_min (div_pos hε hr) (by linarith [hσ.2])
    have hs1 : σ < s := by rw [hs]; linarith
    have hs2 : s ≤ l6d_S + δ := by
      have := min_le_right (ε / q.1) (l6d_S + δ - σ); rw [hs]; linarith
    have hs3 : q.1 * s < q.1 * σ + ε := by
      have := min_le_left (ε / q.1) (l6d_S + δ - σ)
      have h' : q.1 * (min (ε / q.1) (l6d_S + δ - σ) / 2) < ε := by
        have : q.1 * (ε / q.1) = ε := by field_simp
        nlinarith
      rw [hs]; nlinarith
    refine ⟨q.1 * s, ⟨mul_lt_mul_of_pos_left hs1 hr, hs3⟩, ?_⟩
    have h1 := hH (iso_vertexFlow 1 (lieChart q) (q.1 * s)) 1 0
    rw [h21, mul_div_cancel_left₀ _ hr0] at h1
    have := mul_neg_of_pos_of_neg hr3 (hneg s ⟨hs1, hs2⟩)
    linarith
  · -- the image lies on the section, in `H*`
    have hP := l6d_reinPoincare_eq hsw
    obtain ⟨t1, t2, t3, d1, d2, tf⟩ := l6d_Xi_constraints hdom' σ
    obtain ⟨h01, h10, hρ₀, hρ₁, hρ₂, hqa⟩ := himg
    obtain ⟨-, hH0, -, -, -, -⟩ := lieChart_spec hdom'
    set y := l6d_flowPt (σ, q.1, q.2) with hy
    have hyq : y = iso_vertexFlow 1 (lieChart q) (q.1 * σ) := by
      rw [hy, l6d_flowPt, mul_comm]
    have hsw0 : switchingFn 1 0 y.2.2 y.1 = 0 := by
      rw [hyq, h21, mul_div_cancel_left₀ _ hr0, hz, mul_zero]
    have hq' : reinPoincare (lieChart q) = iso_adRinvPow 1 y := hP
    have hHq : hamiltonian (-1) (reinPoincare (lieChart q)).2.1 (reinPoincare (lieChart q)).2.2
        (reinPoincare (lieChart q)).1 (vertex 1) = 0 := by
      rw [hq', l6d_hamiltonian_adRinv]
      have h1 := hH y 1 0
      rw [hsw0] at h1
      have h2 : phaseHam y (vertex 1) = 0 := by
        rw [phaseHam, hyq, l6d_vertexFlow_hamiltonian]; exact hH0
      simp only [phaseHam] at h1 h2
      linarith
    have hχq :
        switchingFn 1 2 (reinPoincare (lieChart q)).2.2 (reinPoincare (lieChart q)).1 = 0 := by
      rw [hq', l6d_switchingFn12_adRinv, hsw0, neg_zero]
    have h00 : 0 < (reinPoincare (lieChart q)).1 0 0 := by
      rw [hP]
      have := l6d_eq_pow_mul_divR l6d_fa 1 l6d_va (p := (σ, q.1, q.2)) hr0
      simp only [l6d_fa] at this
      rw [this, pow_one]
      exact mul_pos hr hqa
    have hb : IsBlowupPhasePt (reinPoincare (lieChart q)) := by
      rw [hP]; exact ⟨t1, t2, t3, d1, d2, tf, h01, h10⟩
    have hst : IsStarState (reinPoincare (lieChart q)).1 := by
      rw [hP]; exact ⟨t1, d1, hρ₀, hρ₁, hρ₂⟩
    exact lieChart_lieChartInv hb hst hHq hχq h00


/-- The properties of Lemma 14.3.1 for an open partial homeomorphism `e` of `ℝ⁴ = ℝ × ℝ³`: its
source contains the fixed point `(0, x̃_out)`, which it fixes; `e` and its inverse are analytic on
their domains (an analytic diffeomorphism); on the source, `e` is the Reinhardt–Poincaré map in the
chart for `r > 0` and the Fuller–Poincaré map for `r = 0` ("such that `F` coincides with the
Fuller–Poincaré map at `r = 0`"). -/
def IsReinhardtPoincareExtension (e : OpenPartialHomeomorph (ℝ × (Fin 3 → ℝ)) (ℝ × (Fin 3 → ℝ))) :
    Prop :=
  chartPtOut ∈ e.source ∧ e chartPtOut = chartPtOut ∧ AnalyticOnNhd ℝ e e.source ∧
    AnalyticOnNhd ℝ e.symm e.target ∧ (∀ p ∈ e.source, 0 < p.1 → e p = reinChartMap p) ∧
    ∀ p ∈ e.source, p.1 = 0 → e p = (0, fullerChartMap p.2)

/-! ### Lemma 14.3.1: the analytic diffeomorphism (Step 10)

The derivative of the extended map at the fixed point is block triangular: `∂_r E₁ = r_scale`,
`∂_{x̃} E₁ = 0` (the divisor is invariant) and `∂_{x̃} E₂ = D fullerChartMap(x̃_out)`, which is
invertible (`det = D(r_scale) > 0`). Departure from the book (step 10): the book builds the
backward map `F⁻¹` "in similar way" and continues `F ∘ F⁻¹ = id` analytically; that construction
needs backward-time versions of Lemmas 14.2.3–14.2.4 that the book does not state. The inverse
function theorem (`HasStrictFDerivAt.toOpenPartialHomeomorph`, analytic inverse by
`OpenPartialHomeomorph.analyticAt_symm`) gives the analytic inverse directly. -/

private lemma l6d_E_chartPtOut : l6d_E chartPtOut = chartPtOut := by
  have h := l6d_eventually_E_divisor.self_of_nhds
  rw [chartPtOut, h]
  exact congrArg (Prod.mk 0) fullerChartMap_xTildeOut

private lemma l6d_hasFDerivAt_E :
    HasFDerivAt l6d_E (fderiv ℝ l6d_E chartPtOut) chartPtOut :=
  l6d_analyticAt_E.differentiableAt.hasFDerivAt

private lemma l6d_fderiv_E_fst (v : ℝ × (Fin 3 → ℝ)) :
    (fderiv ℝ l6d_E chartPtOut v).1 = rScale * v.1 := by
  set g : ℝ × (Fin 3 → ℝ) → ℝ := fun q ↦ l6d_qa (l6d_sSw q, q.1, q.2) with hg
  have hga : AnalyticAt ℝ g chartPtOut :=
    (l6d_analyticAt_divided l6d_S xTildeOut).1.comp_of_eq l6d_analyticAt_sSw_triple
      l6d_sSw_triple_base
  have hg0 : g chartPtOut = rScale := by
    simp only [hg, chartPtOut, l6d_sSw_base, l6d_qa_base]
  have h1 := l6d_hasFDerivAt_E.fst
  have h2 := (hasFDerivAt_fst (p := chartPtOut)).mul hga.differentiableAt.hasFDerivAt
  have h12 := h1.unique h2
  have := congrArg (fun L : (ℝ × (Fin 3 → ℝ)) →L[ℝ] ℝ ↦ L v) h12
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_fst',
    add_apply, smul_apply, smul_eq_mul, hg0] at this
  rw [this, chartPtOut]
  simp

private lemma l6d_fderiv_E_snd (v : Fin 3 → ℝ) :
    fderiv ℝ l6d_E chartPtOut (0, v) = (0, fderiv ℝ fullerChartMap xTildeOut v) := by
  obtain ⟨D, hD, -⟩ := hasFDerivAt_fullerChartMap
  have h1 : HasFDerivAt (fun x ↦ l6d_E (0, x))
      ((fderiv ℝ l6d_E chartPtOut).comp (ContinuousLinearMap.inr ℝ ℝ (Fin 3 → ℝ))) xTildeOut :=
    l6d_hasFDerivAt_E.comp xTildeOut (hasFDerivAt_prodMk_right (0 : ℝ) xTildeOut)
  have h2 : HasFDerivAt (fun x ↦ ((0 : ℝ), fullerChartMap x))
      ((0 : (Fin 3 → ℝ) →L[ℝ] ℝ).prod D) xTildeOut :=
    (hasFDerivAt_const (0 : ℝ) xTildeOut).prodMk hD
  have h3 := h1.unique (h2.congr_of_eventuallyEq l6d_eventually_E_divisor)
  have := congrArg (fun L : (Fin 3 → ℝ) →L[ℝ] (ℝ × (Fin 3 → ℝ)) ↦ L v) h3
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.inr_apply,
    ContinuousLinearMap.prod_apply, zero_apply] at this
  rw [this, hD.fderiv]

private lemma l6d_fderiv_E_injective : Function.Injective (fderiv ℝ l6d_E chartPtOut) := by
  intro v w h
  set d := v - w with hd
  have hlin : fderiv ℝ l6d_E chartPtOut d = 0 := by rw [hd, map_sub, h, sub_self]
  have h1 : d.1 = 0 := by
    have := congrArg Prod.fst hlin
    rw [l6d_fderiv_E_fst] at this
    exact (mul_eq_zero.1 this).resolve_left (by linarith [rScale_spec.1])
  have hd' : d = (0, d.2) := Prod.ext h1 rfl
  have h2 : d.2 = 0 := by
    have := congrArg Prod.snd hlin
    rw [hd', l6d_fderiv_E_snd] at this
    exact l6d_fderiv_fullerChartMap_injective (this.trans (map_zero _).symm)
  have : d = 0 := Prod.ext h1 h2
  rwa [hd, sub_eq_zero] at this

/-- **Lemma 14.3.1** (TeX 11766–11772). The Reinhardt–Poincaré map `F` (initially defined for
`r > 0`) extends to an analytic diffeomorphism in a neighborhood of the fixed point
`(0, x̃_out) ∈ ℝ⁴` (including non-positive values of `r`), such that `F` coincides with the
Fuller–Poincaré map at `r = 0`. (Proof: the module docstring.) -/
theorem lemma14_3_1 :
    ∃ e : OpenPartialHomeomorph (ℝ × (Fin 3 → ℝ)) (ℝ × (Fin 3 → ℝ)),
      IsReinhardtPoincareExtension e := by
  set L := fderiv ℝ l6d_E chartPtOut with hL
  let Le : (ℝ × (Fin 3 → ℝ)) ≃L[ℝ] (ℝ × (Fin 3 → ℝ)) :=
    (LinearEquiv.ofInjectiveEndo (L : (ℝ × (Fin 3 → ℝ)) →ₗ[ℝ] (ℝ × (Fin 3 → ℝ)))
      l6d_fderiv_E_injective).toContinuousLinearEquiv
  have hLe : (Le : (ℝ × (Fin 3 → ℝ)) →L[ℝ] (ℝ × (Fin 3 → ℝ))) = L :=
    ContinuousLinearMap.ext fun v ↦ rfl
  have hstrict : HasStrictFDerivAt l6d_E (Le : (ℝ × (Fin 3 → ℝ)) →L[ℝ] (ℝ × (Fin 3 → ℝ)))
      chartPtOut := by
    rw [hLe]; exact l6d_analyticAt_E.hasStrictFDerivAt
  set e₀ := hstrict.toOpenPartialHomeomorph l6d_E with he₀
  -- the open set where `E` is analytic with invertible derivative
  set U := {q | AnalyticAt ℝ l6d_E q} ∩ fderiv ℝ l6d_E ⁻¹'
    range ((↑) : ((ℝ × (Fin 3 → ℝ)) ≃L[ℝ] (ℝ × (Fin 3 → ℝ))) →
      (ℝ × (Fin 3 → ℝ)) →L[ℝ] (ℝ × (Fin 3 → ℝ))) with hUdef
  have hU : IsOpen U := by
    have hcont : ContinuousOn (fderiv ℝ l6d_E) {q | AnalyticAt ℝ l6d_E q} := fun q hq ↦
      (AnalyticOnNhd.fderiv (fun q hq ↦ hq : AnalyticOnNhd ℝ l6d_E {q | AnalyticAt ℝ l6d_E q})
        q hq).continuousAt.continuousWithinAt
    exact hcont.isOpen_inter_preimage (isOpen_analyticAt ℝ l6d_E) ContinuousLinearEquiv.isOpen
  -- the open set where `E` is the Reinhardt–Poincaré map (`r > 0`) and the Fuller map (`r = 0`)
  obtain ⟨δ, -, -, hev⟩ := l6d_reinSwitchTime_eq
  have h3 : ∀ᶠ q in 𝓝 chartPtOut, 0 < q.1 → l6d_E q = reinChartMap q :=
    hev.mono fun q h hr ↦ (l6d_reinChartMap_eq hr (h hr).1).symm
  have h4 : ∀ᶠ q in 𝓝 chartPtOut, q.1 = 0 → l6d_E q = (0, fullerChartMap q.2) := by
    have hc : ContinuousAt (fun q : ℝ × (Fin 3 → ℝ) ↦ q.2) chartPtOut := continuousAt_snd
    have := hc.eventually l6d_eventually_E_divisor
    filter_upwards [this] with q hq h0
    rw [show q = (0, q.2) from Prod.ext h0 rfl]
    exact hq
  obtain ⟨T, hTsub, hTo, hT0⟩ := eventually_nhds_iff.1 (h3.and h4)
  have hW : IsOpen (U ∩ T) := hU.inter hTo
  set e := e₀.restrOpen (U ∩ T) hW with he
  have hcoe : (e : ℝ × (Fin 3 → ℝ) → ℝ × (Fin 3 → ℝ)) = l6d_E := rfl
  have hsrc : e.source = e₀.source ∩ (U ∩ T) := e₀.restrOpen_source _ hW
  refine ⟨e, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsrc]
    exact ⟨hstrict.mem_toOpenPartialHomeomorph_source, ⟨l6d_analyticAt_E, Le, hLe⟩, hT0⟩
  · rw [hcoe]; exact l6d_E_chartPtOut
  · intro q hq
    rw [hsrc] at hq
    rw [hcoe]
    exact hq.2.1.1
  · intro b hb
    have ha := e.map_target hb
    rw [hsrc] at ha
    obtain ⟨i, hi⟩ := ha.2.1.2
    refine e.analyticAt_symm (i := i) hb ?_ ?_
    · rw [hcoe]; exact ha.2.1.1
    · rw [hcoe]; exact hi.symm
  · intro q hq hr
    rw [hsrc] at hq
    rw [hcoe]
    exact (hTsub q hq.2.2).1 hr
  · intro q hq h0
    rw [hsrc] at hq
    rw [hcoe]
    exact (hTsub q hq.2.2).2 h0

end SmoothedPolygons
