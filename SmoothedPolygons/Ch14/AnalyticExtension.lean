module

public import SmoothedPolygons.Ch14.Asymptotics
public import SmoothedPolygons.Ch14.ExtensionConstruction
public import SmoothedPolygons.Ch13.Jacobian
public import Basic.Analysis.Analytic.DivisionByCoordinate
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Topology.OpenPartialHomeomorph.Defs
public import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.Analysis.Analytic.Uniqueness
import SmoothedPolygons.Ch7.Isolated.VertexFlow
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
  TeX 11826–11838); `reinChartMap`, the map `F` in the chart (TeX 11683–11686: "We can write the
  Reinhardt–Poincaré map `F` in local coordinates `(r, x̃) ↦ F(r, x̃)`"); `reinChartMapIn`, the map
  `F⁻¹` that moves backwards in time, in the same chart (`τ F τ`, `reinChartMapIn_eq`);
* `fullerChartMap`: the Fuller–Poincaré map in the chart `x̃` of the divisor (rotation by `ζ` to the
  wall `𝒲₀`, rescaling to `Im z₁ = 1/2`), with the fixed point `x̃_out` and its linearization, whose
  eigenvalues have modulus `< 1/10` (transferred from Lemma 13.5.5's certified Jacobian);
* `analyticAt_rescaledChi`: the first step of the proof, "`χ₂₁(X(s r₀), Λ₁(s r₀), Λ_R(s r₀))/r₀³`
  extends to an analytic function `χ̃₂₁(s, r₀, x̃₀)` in a neighborhood of `r₀ = 0`";
* `eventually_isSwitch_reinSwitchTime`: near the fixed point, with `r > 0`, the control `e₂` is
  optimal on `[0, t_sw]` and is beaten by `e₁` right after (the χ₂₃ check, G14.5: the book examines
  only `χ₂₁`), so `reinPoincare` is the map of consecutive switching points of extremals;
  `eventually_isSwitch_reinSwitchTime_in`, the same for the backward map;
* `IsReinhardtPoincareExtension`, `lemma14_3_1`: **Lemma 14.3.1**.

## The book's proof (TeX 11784–11872), step by step, as formalized

Steps 1–9 are stated once (`SmoothedPolygons/Ch14/ExtensionConstruction.lean`): for a divisor point
`(0, x̃₀)` with Fuller data `h : FullerSwitchData κ x₀ u₀` (`κ = ±1` is the side `κ r > 0`), they
build the analytic map `extMap h` near `(0, x̃₀)` that is the Reinhardt–Poincaré map `reinChartMap`
on the side `κ r > 0` (`eventually_reinChartMap_eq_extMap h`), with the switching structure of
`eventually_isSwitch_of_fullerSwitchData h`. They are applied twice: to `F` at `x̃_out`
(`fullerSwitchData_out`) and, for Step 10, to `F⁻¹` (`fullerSwitchData_in`).

1. The chart is rational in `(r₀, x̃₀)` and `(1 + r₀ x̃₂₁)⁻¹` with nonzero denominators near the
   divisor, hence analytic (`entrywiseAnalyticAt_lieChart`, in
   `SmoothedPolygons/Ch14/VertexFlowAnalytic.lean`).
2. The vertex flow is analytic in `(t, q)` (`entrywiseAnalyticAt_vertexFlow`): `X(t)` and `Λ₁(t)`
   are products of matrix exponentials; for `Λ_R(t)` the quadratures of the closed form are replaced
   by `exp (t • L(X₀, P))` of a linear ODE in the frame rotating with `e^{tP}` (`l6d_rotCurve`,
   `l6d_vfΛR_eq_exp`); Mathlib's `NormedSpace.exp_analytic` does the rest
   (`Basic/Analysis/Analytic/MatrixExp.lean`). Substitute `t = s r₀` (`extFlowPt`).
3. Lemma 14.2.4 and division of power series: `χ̃₂₁ = χ₂₁/r₀³` (`extChi21`) is analytic near
   `r₀ = 0` (`l6d_analyticAt_divR`, from `AnalyticAt.exists_eq_pow_smul_of_isBigO`; the
   one-sided `O(r₀³)` of Lemma 14.2.4 becomes two-sided by
   `AnalyticAt.isBigO_nhds_of_isBigO_nhdsGT`), with value `24 RR(ζ - 1, z₃(s))` at `r₀ = 0`
   (`analyticAt_rescaledChi`).
4. The Fuller data at the divisor point (`FullerSwitchData`). At `(0, x̃_out)` the Fuller cubic is
   `24 λ³ g(s/λ)`, `g(τ) = a₀ + a₁τ + a₂τ² + a₃τ³` with `a₀, a₁, a₂ > 0 > a₃` (`qOutCart_signs`)
   and `g(t_sw) = 0` (`poincare_qOutCart`): exactly, `t_sw³ g(τ) = (t_sw - τ) B(τ)` with `B > 0`
   on `[0, ∞)`, so `g > 0` on `[0, t_sw)`, `g < 0` after, and `g'(t_sw) < 0` (no numerics).
5. The analytic implicit function theorem (`ContDiffAt.implicitFunction`, `n = ω`) gives the
   analytic switching time (`extSwitchTime h`); its uniqueness box and compactness of `[0, u₀]`
   show that it is the least positive zero (`extSwitchTime_zero_structure`), so
   `reinSwitchTime (lieChart q) = |r| u_sw(q)` for `κ r > 0` (`l6s_reinSwitchTime_eq`).
6. Rotate by `Ad_{R⁻¹}` (`extSwitchPt`).
7. G14.7: the entries of `X_sw - J` and `Λ₁sw + (3/2) J` read by the chart are `O(r₀)`, `O(r₀²)`
   (Lemma 14.2.3, rotated by `fullerCoords_adR`, with the determinant relations `det X = 1`,
   `det Λ₁ = 9/4`, `l6d_det_relations`, for the entries `cayleyZ` does not see), so they are
   divisible by `r₀`, `r₀²` (`extDivA`, `extDivB`, `extDivC`, `extDivD`), with limits
   `2 Im w₁, 2 Re w₁, 6 Re w₂, -6 Im w₂`, `w = ζ z(s)`.
8. The `(1, 1)` entry of `(X_sw - J)/r₀` at the divisor point is nonzero (`r_scale` at `x̃_out`,
   `extDivA_base`), so `extMap h (r, x̃) = (r a₁, b₁/a₁, c₂/a₁², d₂/a₁²)` is analytic there
   (`analyticAt_extMap`) and equals `reinChartMap` for `κ r > 0`
   (`eventually_reinChartMap_eq_extMap`).
9. At `r = 0`, for `F`, the Fuller switching structure (Steps 4–5 and the χ₂₃ check at `r₀ = 0`)
   gives `F(z(x̃)) = z(s_sw(0, x̃), z(x̃), ζ)` (`l6d_poincare_eq`), so `extMap h (0, x̃) =
   (0, fullerChartMap x̃)` (`eventually_extMap_divisor`).
10. **F is a diffeomorphism, the book's way** (TeX 11864–11871). "In similar way to what we have
   done, we can show analyticity and analytic continuation of the Reinhardt–Poincaré map `F⁻¹` that
   moves backwards in time": `F⁻¹` flows `e₃` backwards from the wall `χ₂₃ = 0` and rotates by
   `Ad_R`; by the time reversal (`iso_vertexFlow_reinTau`, `lieChart_chartReflect`) it is
   `F⁻¹ = τ F τ`, which in the chart is `σ F σ` (`reinChartMapIn_eq`), the forward map near the
   reflected point `(0, x̃_in)` from the side `r < 0`; Steps 1–9 there are the second instance
   `fullerSwitchData_in`, whose Fuller data come from those at `x̃_out`
   (`ExtensionConstruction.lean`), and `extMapBack = σ ∘ extMap fullerSwitchData_in ∘ σ` is the
   analytic `F⁻¹` (`analyticAt_extMapBack`, `eventually_extMapBack_eq`). "When the parameter `r₀`
   is positive and in a sufficiently small neighborhood of the fixed point, we have that `F` and
   `F⁻¹` are inverse functions": both are the true Reinhardt maps there, and the arc of one is the
   time reversal of the arc of the other (`reinPoincare_reinTau_reinPoincare`), applied to each
   instance (`eventually_reinChartMapIn_reinChartMap_out`,
   `eventually_reinChartMap_reinChartMapIn`). "By analytic continuation, they are inverse functions
   in a neighborhood of the fixed point" (the identity theorem on a ball,
   `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`, `l6s_eventually_comp_eq`). "Hence, `F` is
   a diffeomorphism" (`lemma14_3_1`).

The χ₂₃ check missing from the book (G14.5): `χ₂₃ = r³ χ̃₂₃` with
`χ̃₂₃(s, 0, x̃_out) = 24 RR(ζ - ζ², z₃(s)) = s Q(s)`, `Q > 0` (`extChi23Zero_xTildeOut`); `χ̃₂₃`
vanishes at `s = 0` (the chart lies on `χ₂₃ = 0` for every sign of `r`,
`l6d_switchingFn12_lieChart`), so one more division by `s` (`exists_extChi23_eq_mul`) and
compactness give `χ̃₂₃ > 0` on `(0, B]` near the divisor point (`eventually_extChi23_pos`).

For `hasStrictFDerivAt_extension` (FixedPointManifolds.lean): `tendsto_reinChartMap_fst_div`,
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

/-- **The Reinhardt–Poincaré map `F⁻¹` that moves backwards in time** (Lemma 14.3.1, Step 10), in
the chart at `q_out`; equivalently, the Reinhardt–Poincaré map in the mirrored chart at `q_in`
(Remark 14.3.4, G14.9). The forward dynamics near `q_in` follows the same rule as near `q_out`
(control `e₂` from the wall `χ₂₃ = 0`, switch at `χ₂₁ = 0`, rotation `Ad_{R⁻¹}`): the time reversal
maps the cyclic switching sequence `3 → 2 → 1 → 3` to itself. In the chart it is `σ F σ`
(`reinChartMapIn_eq`). -/
noncomputable def reinChartMapIn (p : ℝ × (Fin 3 → ℝ)) : ℝ × (Fin 3 → ℝ) :=
  lieChartInInv (reinPoincare (lieChartIn p))

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
    (poincare_scale hs (fullerOfChart_ne_zero x)).2.2, ← scale_smul,
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
  have hv : ∀ s x, (fun r ↦ extChi 1 0 (s, r, x) -
      r ^ 3 * (24 * RR (ζ - 1) (flow s (fullerOfChart x) ζ 2))) =O[𝓝[>] 0] (fun r ↦ r ^ 4) := by
    intro s x
    refine (lemma14_2_4 x s).congr_left fun r ↦ ?_
    simp only [extChi, extFlowPt]
    ring
  refine ⟨extChiDiv 1 0 (fun p ↦ 24 * RR (ζ - 1) (flow p.1 (fullerOfChart p.2) ζ 2)),
    fun s x ↦ ⟨analyticAt_extChiDiv 1 0 hv s x, by simp [extChiDiv], ?_⟩⟩
  refine Eventually.of_forall fun p hp ↦ ?_
  simp only [extChiDiv, hp, ite_false, extChi, extFlowPt]

/-! ### The Reinhardt–Poincaré map near a divisor point with Fuller data (Steps 5–8)

Stated once, for `h : FullerSwitchData κ x₀ u₀`: for `κ r > 0` near `(0, x̃₀)` the switching time
of `reinPoincare` is `|r| u_sw(r, x̃)` (`l6s_reinSwitchTime_eq`: along the flow
`χ₂₁(t) = |r|³ κ χ̃₂₁(κ t/|r|, r, x̃)`, whose least positive zero is `t/|r| = u_sw`), so the
Reinhardt–Poincaré map in the chart is the analytic map `extMap h`
(`eventually_reinChartMap_eq_extMap`), and the switching structure holds
(`eventually_isSwitch_of_fullerSwitchData`). -/

attribute [local fun_prop] analyticAt_fst analyticAt_snd analyticAt_pi_apply

variable {κ : ℝ} {x₀ : Fin 3 → ℝ} {u₀ : ℝ}

private lemma l6d_switchingFn_flow_eq {i j : Fin 3} {q : ℝ × (Fin 3 → ℝ)} (hr : q.1 ≠ 0)
    (t : ℝ) : switchingFn i j (iso_vertexFlow 1 (lieChart q) t).2.2
      (iso_vertexFlow 1 (lieChart q) t).1 = extChi i j (t / q.1, q.1, q.2) := by
  simp only [extChi, extFlowPt, div_mul_cancel₀ t hr]

/-- Along the flow from `lieChart q`, `χ₂₁(t) = |r|³ κ χ̃₂₁(κ t/|r|, r, x̃)` and
`χ₂₃(t) = |r|³ κ χ̃₂₃(κ t/|r|, r, x̃)`, with `|r| = κ r`. -/
private lemma l6s_chi_flow (h : FullerSwitchData κ x₀ u₀) {q : ℝ × (Fin 3 → ℝ)} (hr : q.1 ≠ 0)
    (t : ℝ) :
    switchingFn 1 0 (iso_vertexFlow 1 (lieChart q) t).2.2 (iso_vertexFlow 1 (lieChart q) t).1 =
        (κ * q.1) ^ 3 * extImplicitFn κ (q, t / (κ * q.1)) ∧
      switchingFn 1 2 (iso_vertexFlow 1 (lieChart q) t).2.2 (iso_vertexFlow 1 (lieChart q) t).1 =
        (κ * q.1) ^ 3 * (κ * extChi23 (κ * (t / (κ * q.1)), q.1, q.2)) := by
  have hκ := h.mul_self
  have hκ0 : κ ≠ 0 := by rintro rfl; simp at hκ
  have hdiv : κ * (t / (κ * q.1)) = t / q.1 := by
    rw [← mul_div_assoc, mul_div_mul_left _ _ hκ0]
  refine ⟨?_, ?_⟩
  · rw [l6d_switchingFn_flow_eq hr, extChi_eq_extChi21 hr]
    simp only [extImplicitFn, hdiv]
    linear_combination (-(q.1 ^ 3 * extChi21 (t / q.1, q.1, q.2)) * (κ * κ + 1)) * hκ
  · rw [l6d_switchingFn_flow_eq hr, extChi_eq_extChi23 hr, hdiv]
    linear_combination (-(q.1 ^ 3 * extChi23 (t / q.1, q.1, q.2)) * (κ * κ + 1)) * hκ

private lemma l6s_ne_zero_of_pos {q : ℝ × (Fin 3 → ℝ)} (hq : 0 < κ * q.1) : q.1 ≠ 0 := by
  rintro h0
  rw [h0, mul_zero] at hq
  exact lt_irrefl _ hq

/-- The switching time of the Reinhardt–Poincaré map is `|r| u_sw(r, x̃)` for `κ r > 0` near the
divisor point (TeX 11807–11811). -/
private lemma l6s_reinSwitchTime_eq (h : FullerSwitchData κ x₀ u₀) : ∃ δ > 0, δ < u₀ ∧
    ∀ᶠ q in 𝓝 ((0 : ℝ), x₀), 0 < κ * q.1 →
      reinSwitchTime (lieChart q) = κ * q.1 * extSwitchTime h q ∧
      extSwitchTime h q ∈ Ioo (u₀ - δ) (u₀ + δ) ∧ extImplicitFn κ (q, extSwitchTime h q) = 0 ∧
      (∀ u ∈ Ico 0 (extSwitchTime h q), 0 < extImplicitFn κ (q, u)) ∧
      (∀ u ∈ Ioc (extSwitchTime h q) (u₀ + δ), extImplicitFn κ (q, u) < 0) ∧
      ∀ u ∈ Ioc 0 (u₀ + δ), 0 < κ * extChi23 (κ * u, q.1, q.2) := by
  obtain ⟨δ, hδ, hδS, hZ⟩ := extSwitchTime_zero_structure h
  refine ⟨δ, hδ, hδS, ?_⟩
  filter_upwards [hZ] with q ⟨hσ, hz, hpos, hneg, h23⟩ hr
  refine ⟨?_, hσ, hz, hpos, hneg, h23⟩
  have hr0 := l6s_ne_zero_of_pos hr
  have hσ0 : 0 < extSwitchTime h q := by linarith [hσ.1]
  have hval := fun t ↦ (l6s_chi_flow h hr0 t).1
  refine IsLeast.csInf_eq ⟨⟨mul_pos hr hσ0, ?_⟩, ?_⟩
  · rw [hval, mul_div_cancel_left₀ _ hr.ne', hz, mul_zero]
  · rintro t ⟨ht0, ht⟩
    by_contra hlt
    push Not at hlt
    have hs : t / (κ * q.1) ∈ Ico 0 (extSwitchTime h q) :=
      ⟨div_nonneg ht0.le hr.le, by rw [div_lt_iff₀ hr]; linarith⟩
    have := hpos _ hs
    rw [hval] at ht
    exact (mul_pos (pow_pos hr 3) this).ne' ht

/-- For `κ r > 0` near the divisor point the Reinhardt–Poincaré map is `Ad_{R⁻¹}` of the flow point
at the switching time. -/
private lemma l6s_reinPoincare_eq (h : FullerSwitchData κ x₀ u₀) {q : ℝ × (Fin 3 → ℝ)}
    (hT : reinSwitchTime (lieChart q) = κ * q.1 * extSwitchTime h q) :
    reinPoincare (lieChart q) = extSwitchPt (extSwitchArg h q) := by
  rw [reinPoincare, hT]
  change iso_adRinvPow 1 (iso_vertexFlow 1 (lieChart q) (κ * q.1 * extSwitchTime h q)) =
    iso_adRinvPow 1 (iso_vertexFlow 1 (lieChart q) (κ * extSwitchTime h q * q.1))
  rw [mul_right_comm]

/-- **The Reinhardt–Poincaré map is the extended map on the side `κ r > 0`** (Step 8). -/
theorem eventually_reinChartMap_eq_extMap (h : FullerSwitchData κ x₀ u₀) :
    ∀ᶠ q in 𝓝 ((0 : ℝ), x₀), 0 < κ * q.1 → reinChartMap q = extMap h q := by
  obtain ⟨δ, -, -, hev⟩ := l6s_reinSwitchTime_eq h
  filter_upwards [hev] with q hq hr
  rw [reinChartMap, l6s_reinPoincare_eq h (hq hr).1,
    extMap_eq_lieChartInv h (l6s_ne_zero_of_pos hr)]

/-- **The radial scaling factor** (TeX 11849–11856): `(F(r, x̃_out))₁ / r → r_scale` as `r → 0⁺`
(the `(1, 1)` entry of `(X_sw - J)/r₀` at the fixed point). This gives `∂_r F₁ = r_scale` at the
fixed point for every analytic extension (`hasStrictFDerivAt_extension`). -/
theorem tendsto_reinChartMap_fst_div :
    Tendsto (fun r ↦ (reinChartMap (r, xTildeOut)).1 / r) (𝓝[>] 0) (𝓝 rScale) := by
  have h := fullerSwitchData_out
  have hc : ContinuousAt (fun r : ℝ ↦ (r, xTildeOut)) 0 := by fun_prop
  have hev' : ∀ᶠ r in 𝓝[>] (0 : ℝ), (reinChartMap (r, xTildeOut)).1 / r =
      extDivA (extSwitchArg h (r, xTildeOut)) := by
    filter_upwards [nhdsWithin_le_nhds (hc.eventually (eventually_reinChartMap_eq_extMap h)),
      self_mem_nhdsWithin] with r hr hr0
    have hr0' : (0 : ℝ) < r := hr0
    rw [hr (by simpa using hr0'), extMap]
    field_simp
  have hqa : ContinuousAt (fun r : ℝ ↦ extDivA (extSwitchArg h (r, xTildeOut))) 0 := by
    have h1 := ((analyticAt_extDiv (1 * sSwOut) xTildeOut).1.comp_of_eq
      (analyticAt_extSwitchArg h) (extSwitchArg_base h)).continuousAt
    exact h1.comp_of_eq hc rfl
  have hval : extDivA (extSwitchArg h (0, xTildeOut)) = rScale := by
    rw [extSwitchArg_base, one_mul, extDivA_base]
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
  simp only [hamiltonian_eq_traceForm_sub, iso_adRinvPow]
  rw [← poly_controlP_conj hC hZ, poly_traceForm_conj hC]
  congr 1
  rw [← poly_traceForm_conj hC (q.2.1 + (3 / 2 : ℝ) • J) q.1, poly_conj_add, poly_conj_smul]
  simp only [pow_one, Rinv_mul_J_mul_R]

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

/-- The image point of a chart point of the blow-up is a phase point of the blow-up up to the sheet
conditions (traceless, `det X = 1`, `det Λ₁ = 9/4`, `⟨X, Λ_R⟩ = 0`). -/
private lemma l6s_Xi_constraints {q : ℝ × (Fin 3 → ℝ)} (hb : IsBlowupPhasePt (lieChart q))
    (σ : ℝ) :
    (extSwitchPt (σ, q.1, q.2)).1.trace = 0 ∧ (extSwitchPt (σ, q.1, q.2)).2.1.trace = 0 ∧
      (extSwitchPt (σ, q.1, q.2)).2.2.trace = 0 ∧ (extSwitchPt (σ, q.1, q.2)).1.det = 1 ∧
      (extSwitchPt (σ, q.1, q.2)).2.1.det = 9 / 4 ∧
      traceForm (extSwitchPt (σ, q.1, q.2)).1 (extSwitchPt (σ, q.1, q.2)).2.2 = 0 := by
  obtain ⟨-, -, -, hdX, hdL, hXR, -, -⟩ := hb
  obtain ⟨t1, t2, t3⟩ := extFlowPt_traceless (σ, q.1, q.2)
  have hC : R ^ 1 * R⁻¹ ^ 1 = 1 := poly_Rpow_mul_Rinvpow 1
  simp only [extSwitchPt, iso_adRinvPow]
  refine ⟨by rw [poly_trace_conj hC, t1], by rw [poly_trace_conj hC, t2],
    by rw [poly_trace_conj hC, t3], ?_, ?_, ?_⟩
  · rw [poly_det_conj hC, extFlowPt, det_vertexFlow_fst]; exact hdX
  · rw [poly_det_conj hC, extFlowPt, det_vertexFlow_snd]; exact hdL
  · rw [poly_traceForm_conj hC, extFlowPt, traceForm_vertexFlow]; exact hXR

/-- The image point, as a function of the chart point. -/
private noncomputable def l6s_img (h : FullerSwitchData κ x₀ u₀) (q : ℝ × (Fin 3 → ℝ)) :
    iso_PhasePt :=
  extSwitchPt (extSwitchArg h q)

private lemma l6s_continuousAt_img_entries (h : FullerSwitchData κ x₀ u₀) (i j : Fin 2) :
    ContinuousAt (fun q ↦ (l6s_img h q).1 i j) ((0 : ℝ), x₀) ∧
      ContinuousAt (fun q ↦ (l6s_img h q).2.1 i j) ((0 : ℝ), x₀) := by
  obtain ⟨h1, h2⟩ := entrywiseAnalyticAt_extSwitchPt (κ * u₀) x₀
  exact ⟨((h1 i j).comp_of_eq (analyticAt_extSwitchArg h) (extSwitchArg_base h)).continuousAt,
    ((h2 i j).comp_of_eq (analyticAt_extSwitchArg h) (extSwitchArg_base h)).continuousAt⟩

private lemma l6s_img_base (h : FullerSwitchData κ x₀ u₀) :
    l6s_img h ((0 : ℝ), x₀) = (J, (-(3 / 2) : ℝ) • J, 0) := by
  rw [l6s_img, extSwitchArg_base, extSwitchPt_zero]

/-- Near the divisor point the image point is near `(J, -(3/2) J)`: the sheet conditions and the
star inequalities hold, and its `(1, 1)` entry is `r a₁` with `a₁ > 0`. -/
private lemma l6s_eventually_img (h : FullerSwitchData κ x₀ u₀) :
    ∀ᶠ q in 𝓝 ((0 : ℝ), x₀), (l6s_img h q).1 0 1 < (l6s_img h q).1 1 0 ∧
      (l6s_img h q).2.1 1 0 < (l6s_img h q).2.1 0 1 ∧ 0 < ρ₀ (l6s_img h q).1 ∧
      0 < ρ₁ (l6s_img h q).1 ∧ 0 < ρ₂ (l6s_img h q).1 ∧ 0 < extDivA (extSwitchArg h q) := by
  have c01 := (l6s_continuousAt_img_entries h 0 1).1
  have c10 := (l6s_continuousAt_img_entries h 1 0).1
  have c00 := (l6s_continuousAt_img_entries h 0 0).1
  have d01 := (l6s_continuousAt_img_entries h 0 1).2
  have d10 := (l6s_continuousAt_img_entries h 1 0).2
  have hb := l6s_img_base h
  have v01 : (l6s_img h ((0 : ℝ), x₀)).1 0 1 = -1 := by rw [hb]; simp [J]
  have v10 : (l6s_img h ((0 : ℝ), x₀)).1 1 0 = 1 := by rw [hb]; simp [J]
  have v00 : (l6s_img h ((0 : ℝ), x₀)).1 0 0 = 0 := by rw [hb]; simp [J]
  have w01 : (l6s_img h ((0 : ℝ), x₀)).2.1 0 1 = 3 / 2 := by rw [hb]; simp [J]
  have w10 : (l6s_img h ((0 : ℝ), x₀)).2.1 1 0 = -(3 / 2) := by rw [hb]; simp [J]
  have hqa : ContinuousAt (fun q : ℝ × (Fin 3 → ℝ) ↦ extDivA (extSwitchArg h q)) ((0 : ℝ), x₀) :=
    ((analyticAt_extDiv (κ * u₀) x₀).1.comp_of_eq (analyticAt_extSwitchArg h)
      (extSwitchArg_base h)).continuousAt
  have hρ₀ : ContinuousAt (fun q ↦ ρ₀ (l6s_img h q).1) ((0 : ℝ), x₀) := by
    unfold ρ₀; exact (c10.add (continuousAt_const.mul c00)).div_const _
  have hρ₁ : ContinuousAt (fun q ↦ ρ₁ (l6s_img h q).1) ((0 : ℝ), x₀) := by
    unfold ρ₁; exact (c10.sub (continuousAt_const.mul c00)).div_const _
  have hρ₂ : ContinuousAt (fun q ↦ ρ₂ (l6s_img h q).1) ((0 : ℝ), x₀) := by
    unfold ρ₂; exact ((continuousAt_const.mul c01).add c10).neg.div_const _
  have e1 : (l6s_img h ((0 : ℝ), x₀)).1 0 1 < (l6s_img h ((0 : ℝ), x₀)).1 1 0 := by
    rw [v01, v10]; norm_num
  have e2 : (l6s_img h ((0 : ℝ), x₀)).2.1 1 0 < (l6s_img h ((0 : ℝ), x₀)).2.1 0 1 := by
    rw [w01, w10]; norm_num
  have e3 : (0 : ℝ) < ρ₀ (l6s_img h ((0 : ℝ), x₀)).1 := by simp only [ρ₀, v10, v00]; positivity
  have e4 : (0 : ℝ) < ρ₁ (l6s_img h ((0 : ℝ), x₀)).1 := by
    simp only [ρ₁, v10, v00, mul_zero, sub_zero]; positivity
  have e5 : (0 : ℝ) < ρ₂ (l6s_img h ((0 : ℝ), x₀)).1 := by
    simp only [ρ₂, v10, v01]; norm_num
  have e6 : (0 : ℝ) < extDivA (extSwitchArg h ((0 : ℝ), x₀)) := by
    rw [extDivA_extSwitchArg_base]; exact h.scale_pos
  filter_upwards [c01.eventually_lt c10 e1, d10.eventually_lt d01 e2,
    continuousAt_const.eventually_lt hρ₀ e3, continuousAt_const.eventually_lt hρ₁ e4,
    continuousAt_const.eventually_lt hρ₂ e5, continuousAt_const.eventually_lt hqa e6]
    with q h1 h2 h3 h4 h5 h6
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- Chart points with small `r > 0` near a divisor point lie in `H*`. -/
private lemma l6s_eventually_mem_lieChartDomain {p₀ : ℝ × (Fin 3 → ℝ)} (hp₀ : p₀.1 = 0) :
    ∀ᶠ q in 𝓝 p₀, 0 < q.1 → q ∈ lieChartDomain := by
  have hc0 : ContinuousAt (fun q : ℝ × (Fin 3 → ℝ) ↦ q.2 0) p₀ := by fun_prop
  have hc2 : ContinuousAt (fun q : ℝ × (Fin 3 → ℝ) ↦ q.1 ^ 2 * q.2 2) p₀ := by fun_prop
  have h3 : (0 : ℝ) < √3 := by positivity
  set ρ := 1 / (√3 + |p₀.2 0| + 1) with hρdef
  have hden : 0 < √3 + |p₀.2 0| + 1 := by positivity
  have hρ : 0 < ρ := one_div_pos.2 hden
  have hr : ∀ᶠ q in 𝓝 p₀, q.1 < ρ :=
    (by fun_prop : ContinuousAt (fun q : ℝ × (Fin 3 → ℝ) ↦ q.1) p₀).eventually_lt
      continuousAt_const (by rw [hp₀]; exact hρ)
  have e2 : p₀.2 0 - 1 < p₀.2 0 := by linarith
  have e3 : p₀.1 ^ 2 * p₀.2 2 < 3 / 2 := by rw [hp₀]; norm_num
  filter_upwards [hr, continuousAt_const.eventually_lt hc0 e2,
    hc2.eventually_lt continuousAt_const e3] with q hq1 hq3 hq4 hpos
  refine ⟨hpos, ?_, by linarith [hq4]⟩
  have : √3 + |p₀.2 0| + 1 < 1 / q.1 := by
    rw [lt_one_div hden hpos]
    simpa [ρ] using hq1
  have := neg_abs_le (p₀.2 0)
  linarith

/-- Chart points with small `r > 0` near `x̃_out` lie in `H*`. -/
lemma eventually_mem_lieChartDomain :
    ∀ᶠ q in 𝓝 chartPtOut, 0 < q.1 → q ∈ lieChartDomain :=
  l6s_eventually_mem_lieChartDomain rfl

/-- The reflection `σ` of the chart is linear, hence analytic. -/
private lemma l6s_analyticAt_chartReflect (p : ℝ × (Fin 3 → ℝ)) :
    AnalyticAt ℝ chartReflect p := by
  unfold chartReflect
  refine analyticAt_fst.neg.prod (AnalyticAt.pi fun i ↦ ?_)
  fin_cases i
  · change AnalyticAt ℝ (fun x : ℝ × (Fin 3 → ℝ) ↦ -x.2 0) p; fun_prop
  · change AnalyticAt ℝ (fun x : ℝ × (Fin 3 → ℝ) ↦ -x.2 1) p; fun_prop
  · change AnalyticAt ℝ (fun x : ℝ × (Fin 3 → ℝ) ↦ x.2 2) p; fun_prop

private lemma l6s_continuous_chartReflect : Continuous chartReflect :=
  continuous_iff_continuousAt.2 fun p ↦ (l6s_analyticAt_chartReflect p).continuousAt

/-- The section conditions are invariant under the time reversal (`τ` exchanges `e₂` and `e₃`). -/
private lemma l6s_section_reinTau {Y : iso_PhasePt}
    (hH : hamiltonian (-1) Y.2.1 Y.2.2 Y.1 (vertex 1) = 0) (hχ : switchingFn 1 2 Y.2.2 Y.1 = 0) :
    hamiltonian (-1) (reinTau Y).2.1 (reinTau Y).2.2 (reinTau Y).1 (vertex 1) = 0 ∧
      switchingFn 1 2 (reinTau Y).2.2 (reinTau Y).1 = 0 := by
  have h12 := hamiltonian_sub_eq_switchingFn Y.2.1 Y.2.2 Y.1 1 2
  have h21 := hamiltonian_sub_eq_switchingFn Y.2.1 Y.2.2 Y.1 2 1
  refine ⟨?_, ?_⟩
  · rw [(switchingFn_reinTau 1 0 Y).2]
    change hamiltonian (-1) Y.2.1 Y.2.2 Y.1 (vertex 2) = 0
    linarith
  · rw [(switchingFn_reinTau 1 2 Y).1]
    change switchingFn 2 1 Y.2.2 Y.1 = 0
    linarith

/-- Near a divisor point the chart points on the side `κ r > 0` are phase points of the blow-up on
the section (`H(e₂) = 0`, `χ₂₃ = 0`): for `κ = 1` by `lieChart_spec`; for `κ = -1` through
`lieChart (σ q) = τ(lieChart q)`. -/
private lemma l6s_eventually_lieChart_section (h : FullerSwitchData κ x₀ u₀) :
    ∀ᶠ q in 𝓝 ((0 : ℝ), x₀), 0 < κ * q.1 → IsBlowupPhasePt (lieChart q) ∧
      hamiltonian (-1) (lieChart q).2.1 (lieChart q).2.2 (lieChart q).1 (vertex 1) = 0 ∧
      switchingFn 1 2 (lieChart q).2.2 (lieChart q).1 = 0 := by
  rcases h.sign with rfl | rfl
  · filter_upwards [l6s_eventually_mem_lieChartDomain (p₀ := ((0 : ℝ), x₀)) rfl] with q hq hr
    obtain ⟨hb, hH, hχ, -⟩ := lieChart_spec (hq (by simpa using hr))
    exact ⟨hb, hH, hχ⟩
  · have hc : ContinuousAt chartReflect ((0 : ℝ), x₀) := l6s_continuous_chartReflect.continuousAt
    filter_upwards [hc.eventually (l6s_eventually_mem_lieChartDomain
      (p₀ := chartReflect ((0 : ℝ), x₀)) (by simp [chartReflect]))] with q hq hr
    have hr' : 0 < (chartReflect q).1 := by simp only [chartReflect]; linarith
    obtain ⟨hb, hH, hχ, -⟩ := lieChart_spec (hq hr')
    have e : lieChart q = reinTau (lieChart (chartReflect q)) := by
      rw [lieChart_chartReflect, reinTau_spec.1]
    rw [e]
    exact ⟨reinTau_spec.2.1 _ hb, l6s_section_reinTau hH hχ⟩

/-- A phase point of the blow-up on the section with `X₁₁ ≠ 0`, of either sign, is the chart point
of its chart coordinates (`lieChart_lieChartInv`; for `X₁₁ < 0` through `τ`,
`lieChartInv_reinTau`). -/
private lemma l6s_lieChart_lieChartInv {Y : iso_PhasePt} (hb : IsBlowupPhasePt Y)
    (hst : IsStarState Y.1) (hH : hamiltonian (-1) Y.2.1 Y.2.2 Y.1 (vertex 1) = 0)
    (hχ : switchingFn 1 2 Y.2.2 Y.1 = 0) (h00 : Y.1 0 0 ≠ 0) : lieChart (lieChartInv Y) = Y := by
  rcases lt_or_gt_of_ne h00 with hneg | hpos
  · obtain ⟨hH', hχ'⟩ := l6s_section_reinTau hH hχ
    have h1 := (lieChart_lieChartInv (reinTau_spec.2.1 Y hb) (isStarState_matTau hst) hH' hχ'
      (by simp only [reinTau, matTau, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.empty_val', Matrix.cons_val_fin_one]; linarith)).2
    rw [lieChartInv_reinTau, lieChart_chartReflect] at h1
    have := congrArg reinTau h1
    rwa [reinTau_spec.1, reinTau_spec.1] at this
  · exact (lieChart_lieChartInv hb hst hH hχ hpos).2

/-- **The switching structure near a divisor point with Fuller data** (TeX 11807–11813, with the
χ₂₃ check of G14.5), stated once: for chart points `q` near `(0, x̃₀)` on the side `κ r > 0`, along
the flow with the control `e₂` from `lieChart q` (a point of the wall `χ₂₃ = 0`), `e₂` is the strict
maximizer of the Hamiltonian among the vertices on `(0, t_sw)`, `t_sw > 0`, `e₁` beats it at times
arbitrarily close to `t_sw` on the right, and the image `reinPoincare (lieChart q)` is the chart
point `lieChart (reinChartMap q)`, on the side `κ r > 0`. -/
theorem eventually_isSwitch_of_fullerSwitchData (h : FullerSwitchData κ x₀ u₀) :
    ∀ᶠ q in 𝓝[{q | 0 < κ * q.1}] ((0 : ℝ), x₀),
      0 < reinSwitchTime (lieChart q) ∧
      (∀ t ∈ Ioo 0 (reinSwitchTime (lieChart q)), ∀ j : Fin 3, j ≠ 1 →
        phaseHam (iso_vertexFlow 1 (lieChart q) t) (vertex j) <
          phaseHam (iso_vertexFlow 1 (lieChart q) t) (vertex 1)) ∧
      (∀ ε > 0, ∃ t ∈ Ioo (reinSwitchTime (lieChart q)) (reinSwitchTime (lieChart q) + ε),
        phaseHam (iso_vertexFlow 1 (lieChart q) t) (vertex 1) <
          phaseHam (iso_vertexFlow 1 (lieChart q) t) (vertex 0)) ∧
      switchingFn 1 2 (lieChart q).2.2 (lieChart q).1 = 0 ∧
      0 < κ * (reinChartMap q).1 ∧ lieChart (reinChartMap q) = reinPoincare (lieChart q) := by
  obtain ⟨δ, hδ, hδS, hev⟩ := l6s_reinSwitchTime_eq h
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hev, l6s_eventually_img h, l6s_eventually_lieChart_section h] with q hq himg
    hsec hr
  have hr : 0 < κ * q.1 := hr
  obtain ⟨hsw, hσ, hz, hpos, hneg, h23q⟩ := hq hr
  obtain ⟨hb, hH0, hχ0⟩ := hsec hr
  have hr0 := l6s_ne_zero_of_pos hr
  have h21 := fun t ↦ (l6s_chi_flow h hr0 t).1
  have h23 := fun t ↦ (l6s_chi_flow h hr0 t).2
  set σ := extSwitchTime h q with hσdef
  set ρ := κ * q.1 with hρ
  have hσ0 : 0 < σ := by linarith [hσ.1]
  have hH : ∀ (y : iso_PhasePt) (i j : Fin 3), phaseHam y (vertex i) - phaseHam y (vertex j) =
      switchingFn i j y.2.2 y.1 := fun y i j ↦ hamiltonian_sub_eq_switchingFn _ _ _ i j
  have hr3 : 0 < ρ ^ 3 := pow_pos hr 3
  refine ⟨by rw [hsw]; positivity, ?_, ?_, hχ0, ?_⟩
  · intro t ht j hj
    rw [hsw] at ht
    have hs0 : 0 < t / ρ := div_pos ht.1 hr
    have hs1 : t / ρ < σ := by rw [div_lt_iff₀ hr]; linarith [ht.2]
    fin_cases j
    · have h1 := hH (iso_vertexFlow 1 (lieChart q) t) 1 0
      rw [h21] at h1
      have := mul_pos hr3 (hpos (t / ρ) ⟨hs0.le, hs1⟩)
      simp only [Fin.zero_eta, Fin.isValue]
      linarith
    · exact absurd rfl hj
    · have h1 := hH (iso_vertexFlow 1 (lieChart q) t) 1 2
      rw [h23] at h1
      have := mul_pos hr3 (h23q (t / ρ) ⟨hs0, by linarith [hσ.2]⟩)
      simp only [Fin.reduceFinMk, Fin.isValue]
      linarith
  · intro ε hε
    rw [hsw]
    set s := σ + min (ε / ρ) (u₀ + δ - σ) / 2 with hs
    have hm : 0 < min (ε / ρ) (u₀ + δ - σ) := lt_min (div_pos hε hr) (by linarith [hσ.2])
    have hs1 : σ < s := by rw [hs]; linarith
    have hs2 : s ≤ u₀ + δ := by
      have := min_le_right (ε / ρ) (u₀ + δ - σ); rw [hs]; linarith
    have hs3 : ρ * s < ρ * σ + ε := by
      have := min_le_left (ε / ρ) (u₀ + δ - σ)
      have h' : ρ * (min (ε / ρ) (u₀ + δ - σ) / 2) < ε := by
        have : ρ * (ε / ρ) = ε := mul_div_cancel₀ ε hr.ne'
        nlinarith
      rw [hs]; nlinarith
    refine ⟨ρ * s, ⟨mul_lt_mul_of_pos_left hs1 hr, hs3⟩, ?_⟩
    have h1 := hH (iso_vertexFlow 1 (lieChart q) (ρ * s)) 1 0
    rw [h21, mul_div_cancel_left₀ _ hr.ne'] at h1
    have := mul_neg_of_pos_of_neg hr3 (hneg s ⟨hs1, hs2⟩)
    linarith
  · -- the image lies on the section and is a chart point
    have hP := l6s_reinPoincare_eq h hsw
    obtain ⟨t1, t2, t3, d1, d2, tf⟩ := l6s_Xi_constraints hb (κ * σ)
    obtain ⟨h01, h10, hρ₀, hρ₁, hρ₂, hqa⟩ := himg
    set y := extFlowPt (extSwitchArg h q) with hy
    have hyq : y = iso_vertexFlow 1 (lieChart q) (ρ * σ) := by
      rw [hy]
      change iso_vertexFlow 1 (lieChart q) (κ * σ * q.1) = _
      rw [mul_right_comm]
    have hsw0 : switchingFn 1 0 y.2.2 y.1 = 0 := by
      rw [hyq, h21, mul_div_cancel_left₀ _ hr.ne', hz, mul_zero]
    have hq' : reinPoincare (lieChart q) = iso_adRinvPow 1 y := hP
    have hHq : hamiltonian (-1) (reinPoincare (lieChart q)).2.1 (reinPoincare (lieChart q)).2.2
        (reinPoincare (lieChart q)).1 (vertex 1) = 0 := by
      rw [hq', l6d_hamiltonian_adRinv]
      have h1 := hH y 1 0
      rw [hsw0] at h1
      have h2 : phaseHam y (vertex 1) = 0 := by
        rw [phaseHam, hyq, hamiltonian_vertexFlow]; exact hH0
      simp only [phaseHam] at h1 h2
      linarith
    have hχq :
        switchingFn 1 2 (reinPoincare (lieChart q)).2.2 (reinPoincare (lieChart q)).1 = 0 := by
      rw [hq', l6d_switchingFn12_adRinv, hsw0, neg_zero]
    have h00 : (reinPoincare (lieChart q)).1 0 0 = q.1 * extDivA (extSwitchArg h q) := by
      rw [hP]
      have := eq_pow_mul_extDivPow extEntryA 1 extLimitA (p := extSwitchArg h q) hr0
      simp only [extEntryA] at this
      rw [this, pow_one]
      rfl
    have hb' : IsBlowupPhasePt (reinPoincare (lieChart q)) := by
      rw [hP]; exact ⟨t1, t2, t3, d1, d2, tf, h01, h10⟩
    have hst : IsStarState (reinPoincare (lieChart q)).1 := by
      rw [hP]; exact ⟨t1, d1, hρ₀, hρ₁, hρ₂⟩
    have hpos' : 0 < κ * (reinPoincare (lieChart q)).1 0 0 := by
      rw [h00, ← mul_assoc]; exact mul_pos hr hqa
    refine ⟨hpos', l6s_lieChart_lieChartInv hb' hst hHq hχq ?_⟩
    rintro h0
    rw [h0, mul_zero] at hpos'
    exact lt_irrefl _ hpos'

/-! ### The forward instance at the fixed point -/

private lemma l6d_E_chartPtOut : extMap fullerSwitchData_out chartPtOut = chartPtOut := by
  have h := eventually_extMap_divisor.self_of_nhds
  rw [chartPtOut, h]
  exact congrArg (Prod.mk 0) fullerChartMap_xTildeOut

/-- **The switching structure near the fixed point** (TeX 11807–11813, with the χ₂₃ check of
G14.5; the forward instance of `eventually_isSwitch_of_fullerSwitchData`): for chart points `p`
near `(0, x̃_out)` with `r > 0`, along the flow with the control `e₂` from `q = lieChart p` the
control `e₂` is the strict maximizer of the Hamiltonian among the vertices on `(0, t_sw(q))` (so it
is optimal on `[0, t_sw(q)]`), `t_sw(q) > 0`, `e₁` beats it at times arbitrarily close to `t_sw(q)`
on the right, and the image `reinPoincare q` is again a chart point of `H*` (so `reinChartMap p` is
its chart coordinate). Hence an extremal through `q` on the section switches next at `q(t_sw)`, and
`reinPoincare` maps consecutive switching points. -/
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
  have hs := eventually_isSwitch_of_fullerSwitchData fullerSwitchData_out
  simp only [one_mul] at hs
  -- the image is near the fixed point (continuity of the extension), so in `H*`
  have hE : Tendsto (extMap fullerSwitchData_out) (𝓝 chartPtOut) (𝓝 chartPtOut) := by
    have := (analyticAt_extMap fullerSwitchData_out).continuousAt.tendsto
    rwa [show extMap fullerSwitchData_out ((0 : ℝ), xTildeOut) = chartPtOut from
      l6d_E_chartPtOut] at this
  have hdom := hE.eventually eventually_mem_lieChartDomain
  filter_upwards [hs, nhdsWithin_le_nhds
    (hdom.and (eventually_reinChartMap_eq_extMap fullerSwitchData_out)), self_mem_nhdsWithin]
    with p ⟨h1, h2, h3, _, h5, h6⟩ ⟨hd, heq⟩ hp0
  refine ⟨h1, h2, h3, ?_, h6⟩
  have hp0 : 0 < p.1 := hp0
  have he := heq (by simpa using hp0)
  rw [he] at h5 ⊢
  exact hd h5

/-! ### Time reversal of trajectories (Step 10)

"When the parameter `r₀` is positive and in a sufficiently small neighborhood of the fixed point,
we have that `F` and `F⁻¹` are inverse functions" (TeX 11866–11868): the arc of `F⁻¹` is the arc of
`F` run backwards, by the time reversal of the vertex flows (`iso_vertexFlow_reinTau`), their
rotation by `Ad_{R⁻¹}` and their flow property (uniqueness of solutions, Grönwall). -/

/-- A curve solving the state–costate equations with the control `e_m` (`λ_cost = -1`, with
`P = Z_{e_m}/⟨Z_{e_m}, X(0)⟩` in the state equation) is the vertex flow from its value at `0`
(Grönwall, forward and backward in time, as in `iso_vertexFlow_qFix`). -/
private lemma l6s_eq_vertexFlow (m : Fin 3) (Y : ℝ → iso_PhasePt)
    (hX : ∀ s, Matrix.HasDerivAtEntrywise (fun s ↦ (Y s).1)
      (controlP (vertex m) (Y 0).1 * (Y s).1 - (Y s).1 * controlP (vertex m) (Y 0).1) s)
    (hL : ∀ s, Matrix.HasDerivAtEntrywise (fun s ↦ (Y s).2.1)
      ((Y s).2.1 * (Y s).1 - (Y s).1 * (Y s).2.1) s)
    (hR : ∀ s, Matrix.HasDerivAtEntrywise (fun s ↦ (Y s).2.2)
      (costateRHS (-1) (Y s).2.1 (Y s).2.2 (Y s).1 (vertex m)) s) (t : ℝ) :
    Y t = iso_vertexFlow m (Y 0) t := by
  set q := Y 0 with hq
  set P := controlP (vertex m) q.1 with hP
  have hXeq : ∀ t, (Y t).1 = iso_vfX m q t := by
    intro t
    refine ivf_eq_of_hasDerivAt (a := 0) (f := fun s ↦ (Y s).1) (g := iso_vfX m q)
      (G := fun _ M ↦ P * M - M * P)
      (K := 4 * ∑ k, ∑ l, |P k l|) (fun s _ M N i j ↦ ?_) hX (fun s ↦ ?_)
      (congrArg Prod.fst (ivf_vertexFlow_zero m q)).symm
    · rw [← Matrix.sub_apply, show P * M - M * P - (P * N - N * P) =
        P * (M - N) - (M - N) * P by noncomm_ring]
      simpa only [Matrix.sub_apply] using poly_abs_bracket_le P (M - N) i j
    · have := ivf_vfX_hasDerivAt m q s
      rwa [ivf_controlP_vfX] at this
  have hLeq : ∀ t, (Y t).2.1 = iso_vfΛ₁ m q t := by
    intro t
    obtain ⟨K, hK⟩ := ivf_lax_lipschitz (isCompact_uIcc (a := 0) (b := t))
      (ivf_vfX_continuous m q).continuousOn
    exact ivf_eq_of_hasDerivAt (a := 0) (f := fun s ↦ (Y s).2.1) (g := iso_vfΛ₁ m q)
      (G := fun s M ↦ M * iso_vfX m q s - iso_vfX m q s * M) hK
      (fun s ↦ by have := hL s; rwa [hXeq s] at this) (ivf_vfΛ₁_hasDerivAt m q)
      (congrArg (fun y : iso_PhasePt ↦ y.2.1) (ivf_vertexFlow_zero m q)).symm
  have hReq : ∀ t, (Y t).2.2 = iso_vfΛR m q t := by
    intro t
    obtain ⟨K, hK⟩ := ivf_costateRHS_lipschitz (isCompact_uIcc (a := 0) (b := t))
      (ivf_vfX_continuous m q).continuousOn P
    exact ivf_eq_of_hasDerivAt (a := 0) (f := fun s ↦ (Y s).2.2) (g := iso_vfΛR m q)
      (G := fun s M ↦ costateRHS (-1) (iso_vfΛ₁ m q s) M (iso_vfX m q s) (vertex m))
      (fun s hs M N i j ↦ hK s hs (-1) _ (vertex m) (ivf_controlP_vfX m q s) M N i j)
      (fun s ↦ by have := hR s; rwa [hXeq s, hLeq s] at this) (ivf_vfΛR_hasDerivAt m q)
      (congrArg (fun y : iso_PhasePt ↦ y.2.2) (ivf_vertexFlow_zero m q)).symm
  exact Prod.ext (hXeq t) (Prod.ext (hLeq t) (hReq t))

/-- **The flow property** of the vertex flows: `q(a + t) = (q(a))(t)`. -/
private lemma l6s_vertexFlow_add (m : Fin 3) (q : iso_PhasePt) (a t : ℝ) :
    iso_vertexFlow m q (a + t) = iso_vertexFlow m (iso_vertexFlow m q a) t := by
  have hsh : ∀ s, HasDerivAt (fun s : ℝ ↦ a + s) 1 s := fun s ↦ (hasDerivAt_id' s).const_add a
  have h := l6s_eq_vertexFlow m (fun s ↦ iso_vertexFlow m q (a + s)) (fun s ↦ ?_) (fun s ↦ ?_)
    (fun s ↦ ?_) t
  · simpa using h
  · have := (ivf_vfX_hasDerivAt m q (a + s)).scomp (hsh s)
    rw [one_smul, ivf_controlP_vfX] at this
    refine this.congr_deriv ?_
    simp only [add_zero]
    rw [show controlP (vertex m) (iso_vertexFlow m q a).1 = iso_vfP m q from
      ivf_controlP_vfX m q a]
    rfl
  · have := (ivf_vfΛ₁_hasDerivAt m q (a + s)).scomp (hsh s)
    rw [one_smul] at this
    exact this
  · have := (ivf_vfΛR_hasDerivAt m q (a + s)).scomp (hsh s)
    rw [one_smul] at this
    exact this

/-- **The rotation conjugates the vertex flows** (`R⁻¹ Z_{e_m} R = Z_{e_{m+1}}`, `R⁻¹ J R = J`, the
equations are equivariant): `Ad_{R⁻¹}` of the `e_m`-flow from `q` is the `e_{m+1}`-flow from
`Ad_{R⁻¹} q`. -/
private lemma l6s_adRinv_vertexFlow (m : Fin 3) (q : iso_PhasePt) (t : ℝ) :
    iso_adRinvPow 1 (iso_vertexFlow m q t) = iso_vertexFlow (m + 1) (iso_adRinvPow 1 q) t := by
  have hC : R ^ 1 * R⁻¹ ^ 1 = 1 := poly_Rpow_mul_Rinvpow 1
  have hZ : R⁻¹ ^ 1 * controlMatrix (vertex m) * R ^ 1 = controlMatrix (vertex (m + 1)) := by
    simpa only [pow_one] using poly_Rinv_conj_vertex m
  have hJ : R⁻¹ ^ 1 * J * R ^ 1 = J := poly_conj_pow_J 1
  have hY0 : iso_adRinvPow 1 (iso_vertexFlow m q 0) = iso_adRinvPow 1 q := by
    rw [ivf_vertexFlow_zero]
  have h := l6s_eq_vertexFlow (m + 1) (fun s ↦ iso_adRinvPow 1 (iso_vertexFlow m q s))
    (fun s ↦ ?_) (fun s ↦ ?_) (fun s ↦ ?_) t
  · rw [hY0] at h
    exact h
  · have := ((ivf_vfX_hasDerivAt m q s).const_mul (R⁻¹ ^ 1)).mul_const (R ^ 1)
    refine this.congr_deriv ?_
    simp only [iso_adRinvPow, iso_vertexFlow]
    rw [poly_conj_bracket hC, ← poly_controlP_conj hC hZ, ivf_controlP_vfX, ivf_controlP_vfX]
  · have := ((ivf_vfΛ₁_hasDerivAt m q s).const_mul (R⁻¹ ^ 1)).mul_const (R ^ 1)
    refine this.congr_deriv ?_
    simp only [iso_adRinvPow, iso_vertexFlow]
    rw [poly_conj_bracket hC]
  · have := ((ivf_vfΛR_hasDerivAt m q s).const_mul (R⁻¹ ^ 1)).mul_const (R ^ 1)
    refine this.congr_deriv ?_
    simp only [iso_adRinvPow, iso_vertexFlow]
    rw [poly_costateRHS_conj hC hJ hZ]

/-- The Hamiltonians under `Ad_{R⁻¹}`: `H(e_{m+1})(Ad_{R⁻¹} q) = H(e_m)(q)`. -/
private lemma l6s_phaseHam_adRinv (q : iso_PhasePt) (m : Fin 3) :
    phaseHam (iso_adRinvPow 1 q) (vertex (m + 1)) = phaseHam q (vertex m) := by
  have hC : R ^ 1 * R⁻¹ ^ 1 = 1 := poly_Rpow_mul_Rinvpow 1
  have hZ : R⁻¹ ^ 1 * controlMatrix (vertex m) * R ^ 1 = controlMatrix (vertex (m + 1)) := by
    simpa only [pow_one] using poly_Rinv_conj_vertex m
  exact poly_hamiltonian_conj hC (poly_conj_pow_J 1) hZ (-1) _ _ _

/-- The Hamiltonians at the time reversal of a rotated point: `e₂` is fixed and `e₁ ↔ e₃`
(`τ` exchanges `e₂, e₃`, `Ad_{R⁻¹}` shifts the indices). -/
private lemma l6s_phaseHam_mirror (y : iso_PhasePt) :
    phaseHam (reinTau (iso_adRinvPow 1 y)) (vertex 0) = phaseHam y (vertex 2) ∧
      phaseHam (reinTau (iso_adRinvPow 1 y)) (vertex 1) = phaseHam y (vertex 1) ∧
      phaseHam (reinTau (iso_adRinvPow 1 y)) (vertex 2) = phaseHam y (vertex 0) := by
  have h := fun j ↦ (switchingFn_reinTau j 0 (iso_adRinvPow 1 y)).2
  refine ⟨?_, ?_, ?_⟩
  · have := l6s_phaseHam_adRinv y 2
    rw [show (2 : Fin 3) + 1 = 0 from rfl] at this
    exact (h 0).trans this
  · have := l6s_phaseHam_adRinv y 1
    rw [show (1 : Fin 3) + 1 = 2 from rfl] at this
    exact (h 1).trans this
  · have := l6s_phaseHam_adRinv y 0
    rw [show (0 : Fin 3) + 1 = 1 from rfl] at this
    exact (h 2).trans this


/-- `Ad_{R⁻¹} ∘ τ ∘ Ad_{R⁻¹} = τ` (`τ Ad_R = Ad_{R⁻¹} τ`, `reinTau_spec`). -/
private lemma l6s_adRinv_reinTau_adRinv (x : iso_PhasePt) :
    iso_adRinvPow 1 (reinTau (iso_adRinvPow 1 x)) = reinTau x := by
  have h : iso_adR (iso_adRinvPow 1 x) = x :=
    irt_adRinvPow_injective 1 (irt_adRinvPow_one_adR (iso_adRinvPow 1 x))
  have := reinTau_spec.2.2.2 (iso_adRinvPow 1 x)
  rw [h] at this
  exact this.symm


/-- **Time reversal of trajectories** (Step 10: "the Reinhardt–Poincaré map `F⁻¹` that moves
backwards in time"; the Reinhardt form of Lemma 13.2.5): if `Q` lies on the wall `χ₂₃ = 0` and
along the flow with the control `e₂` from `Q` the control `e₂` beats `e₃` on `(0, T)`,
`T = t_sw(Q) > 0`, then the flow with `e₂` from `τ F(Q)` is the reversed arc
`t ↦ τ Ad_{R⁻¹} Q(T - t)` (`iso_vertexFlow_reinTau`, the rotation and the flow property of the
vertex flows), with `χ₂₁` and `χ₂₃` exchanged; so its switching time is `T` and `F(τ F(Q)) = τ Q`.
-/
theorem reinPoincare_reinTau_reinPoincare {Q : iso_PhasePt} (hT : 0 < reinSwitchTime Q)
    (hQ : switchingFn 1 2 Q.2.2 Q.1 = 0)
    (hmax : ∀ t ∈ Ioo 0 (reinSwitchTime Q), phaseHam (iso_vertexFlow 1 Q t) (vertex 2) <
      phaseHam (iso_vertexFlow 1 Q t) (vertex 1)) :
    reinSwitchTime (reinTau (reinPoincare Q)) = reinSwitchTime Q ∧
      reinPoincare (reinTau (reinPoincare Q)) = reinTau Q := by
  set T := reinSwitchTime Q with hTdef
  set y : ℝ → iso_PhasePt := fun s ↦ iso_vertexFlow 1 Q s with hy
  have hP : reinPoincare Q = iso_adRinvPow 1 (y T) := rfl
  -- the flow from `τ F(Q)` with `e₂` is the reversed arc from `Q`, rotated and reflected
  have hM : ∀ t, iso_vertexFlow 1 (reinTau (reinPoincare Q)) t =
      reinTau (iso_adRinvPow 1 (y (T - t))) := by
    intro t
    have h2 : iso_vertexFlow 2 (iso_adRinvPow 1 (y T)) (-t) =
        iso_adRinvPow 1 (iso_vertexFlow 1 (y T) (-t)) := (l6s_adRinv_vertexFlow 1 (y T) (-t)).symm
    rw [iso_vertexFlow_reinTau, show vertexSwap 1 = 2 from rfl, hP, h2, hy,
      ← l6s_vertexFlow_add, sub_eq_add_neg]
  have hsf : ∀ t, switchingFn 1 0 (iso_vertexFlow 1 (reinTau (reinPoincare Q)) t).2.2
      (iso_vertexFlow 1 (reinTau (reinPoincare Q)) t).1 =
        switchingFn 1 2 (y (T - t)).2.2 (y (T - t)).1 := by
    intro t
    obtain ⟨h0, h1, -⟩ := l6s_phaseHam_mirror (y (T - t))
    rw [← hamiltonian_sub_eq_switchingFn (iso_vertexFlow 1 (reinTau (reinPoincare Q)) t).2.1,
      ← hamiltonian_sub_eq_switchingFn (y (T - t)).2.1, hM t]
    simp only [phaseHam] at h0 h1
    rw [h0, h1]
  -- its switching time is that of the arc from `Q`
  have hT' : reinSwitchTime (reinTau (reinPoincare Q)) = T := by
    refine IsLeast.csInf_eq ⟨⟨hT, ?_⟩, ?_⟩
    · rw [hsf, sub_self, hy]
      simp only [ivf_vertexFlow_zero]
      exact hQ
    · rintro t ⟨ht0, ht⟩
      by_contra hlt
      push Not at hlt
      rw [hsf, ← hamiltonian_sub_eq_switchingFn (y (T - t)).2.1] at ht
      have := hmax (T - t) ⟨by linarith, by linarith⟩
      simp only [phaseHam] at this
      linarith
  refine ⟨hT', ?_⟩
  rw [reinPoincare, hT', hM T, sub_self, l6s_adRinv_reinTau_adRinv, hy]
  simp only [ivf_vertexFlow_zero]

/-- `F⁻¹` in the chart is the forward map at the reflected point: `reinChartMapIn = σ ∘ F ∘ σ`
(`lieChart_chartReflect`, `lieChartInv_reinTau`). -/
theorem reinChartMapIn_eq (p : ℝ × (Fin 3 → ℝ)) :
    reinChartMapIn p = chartReflect (reinChartMap (chartReflect p)) := by
  rw [reinChartMapIn, lieChartInInv, lieChartIn, ← lieChart_chartReflect, lieChartInv_reinTau,
    reinChartMap]

/-- **`F⁻¹ ∘ F = id` near a divisor point with Fuller data**, on the side `κ r > 0` (time reversal
of trajectories, `reinPoincare_reinTau_reinPoincare`, at the switching structure of
`eventually_isSwitch_of_fullerSwitchData`). Applied to the two instances it gives
`F⁻¹ ∘ F = id` and `F ∘ F⁻¹ = id` for `r > 0` near the fixed point. -/
theorem eventually_reinChartMapIn_reinChartMap (h : FullerSwitchData κ x₀ u₀) :
    ∀ᶠ q in 𝓝[{q | 0 < κ * q.1}] ((0 : ℝ), x₀), reinChartMapIn (reinChartMap q) = q := by
  filter_upwards [eventually_isSwitch_of_fullerSwitchData h, self_mem_nhdsWithin] with q
    ⟨hT, hmax, _, hχ, _, himg⟩ hq
  have hr0 := l6s_ne_zero_of_pos (κ := κ) hq
  obtain ⟨-, hP⟩ := reinPoincare_reinTau_reinPoincare hT hχ fun t ht ↦ hmax t ht 2 (by decide)
  rw [reinChartMapIn, lieChartIn, himg, hP, lieChartInInv, reinTau_spec.1,
    lieChartInv_lieChart_of_ne hr0]

/-! ### The backward instance at the fixed point: the analytic `F⁻¹`

The second application of Steps 1–9: at the reflected point `(0, x̃_in) = σ(0, x̃_out)` from the
side `r < 0` (`fullerSwitchData_in`), read in the chart at `q_out` through `σ`. -/

private lemma l6s_tendsto_chartReflect : Tendsto chartReflect (𝓝[{p | 0 < p.1}] chartPtOut)
    (𝓝[{q | 0 < -1 * q.1}] ((0 : ℝ), xTildeIn)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have := l6s_continuous_chartReflect.continuousAt (x := chartPtOut)
    rw [ContinuousAt, chartPtOut, chartReflect_zero_xTildeOut] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with p hp
    simpa [chartReflect] using hp

/-- **The analytic extension of `F⁻¹`** (Step 10, TeX 11864–11866: "In similar way to what we have
done, we can show analyticity and analytic continuation of the Reinhardt–Poincaré map `F⁻¹` that
moves backwards in time"): the second instance of Steps 1–9, `σ ∘ extMap fullerSwitchData_in ∘ σ`,
at the reflected point `(0, x̃_in)` from the side `r < 0`. -/
noncomputable def extMapBack (p : ℝ × (Fin 3 → ℝ)) : ℝ × (Fin 3 → ℝ) :=
  chartReflect (extMap fullerSwitchData_in (chartReflect p))

lemma analyticAt_extMapBack : AnalyticAt ℝ extMapBack chartPtOut := by
  have h1 : AnalyticAt ℝ (extMap fullerSwitchData_in) (chartReflect chartPtOut) := by
    rw [chartPtOut, chartReflect_zero_xTildeOut]
    exact analyticAt_extMap fullerSwitchData_in
  exact (l6s_analyticAt_chartReflect _).comp (h1.comp (l6s_analyticAt_chartReflect _))

lemma extMapBack_chartPtOut : extMapBack chartPtOut = chartPtOut := by
  rw [extMapBack, chartPtOut, chartReflect_zero_xTildeOut, extMap_in_base,
    ← chartReflect_zero_xTildeOut, chartReflect_chartReflect]

/-- For `r > 0` near the fixed point, the analytic `F⁻¹` is the backward Reinhardt–Poincaré map. -/
lemma eventually_extMapBack_eq :
    ∀ᶠ p in 𝓝 chartPtOut, 0 < p.1 → extMapBack p = reinChartMapIn p := by
  have hc : Tendsto chartReflect (𝓝 chartPtOut) (𝓝 ((0 : ℝ), xTildeIn)) := by
    have := l6s_continuous_chartReflect.continuousAt (x := chartPtOut)
    rwa [ContinuousAt, chartPtOut, chartReflect_zero_xTildeOut] at this
  filter_upwards [hc.eventually (eventually_reinChartMap_eq_extMap fullerSwitchData_in)] with p hp
    hp1
  rw [reinChartMapIn_eq, extMapBack, hp (by simpa [chartReflect] using hp1)]

/-- **The switching structure from `lieChartIn p`** (the backward instance of
`eventually_isSwitch_of_fullerSwitchData`): for `p` near `(0, x̃_out)` with `r > 0`, along the flow
with the control `e₂` from `lieChartIn p = lieChart (σ p)` the control `e₂` is the strict maximizer
on `(0, t_sw)`, then beaten by `e₁`, and the image is the point `lieChartIn (reinChartMapIn p)` of
the mirrored chart, with `r > 0`. -/
theorem eventually_isSwitch_reinSwitchTime_in :
    ∀ᶠ p in 𝓝[{p | 0 < p.1}] chartPtOut,
      0 < reinSwitchTime (lieChartIn p) ∧
      (∀ t ∈ Ioo 0 (reinSwitchTime (lieChartIn p)), ∀ j : Fin 3, j ≠ 1 →
        phaseHam (iso_vertexFlow 1 (lieChartIn p) t) (vertex j) <
          phaseHam (iso_vertexFlow 1 (lieChartIn p) t) (vertex 1)) ∧
      (∀ ε > 0, ∃ t ∈ Ioo (reinSwitchTime (lieChartIn p)) (reinSwitchTime (lieChartIn p) + ε),
        phaseHam (iso_vertexFlow 1 (lieChartIn p) t) (vertex 1) <
          phaseHam (iso_vertexFlow 1 (lieChartIn p) t) (vertex 0)) ∧
      0 < (reinChartMapIn p).1 ∧ lieChartIn (reinChartMapIn p) = reinPoincare (lieChartIn p) := by
  filter_upwards [l6s_tendsto_chartReflect.eventually
    (eventually_isSwitch_of_fullerSwitchData fullerSwitchData_in)] with p ⟨h1, h2, h3, _, h5, h6⟩
  have e : lieChartIn p = lieChart (chartReflect p) := (lieChart_chartReflect p).symm
  rw [e]
  refine ⟨h1, h2, h3, ?_, ?_⟩
  · rw [reinChartMapIn_eq]
    simpa [chartReflect] using h5
  · rw [reinChartMapIn_eq, lieChartIn, lieChart_chartReflect, reinTau_spec.1, h6]

/-- **`F ∘ F⁻¹ = id` for `r > 0` near the fixed point** (time reversal of trajectories, the backward
instance of `eventually_reinChartMapIn_reinChartMap`). -/
theorem eventually_reinChartMap_reinChartMapIn :
    ∀ᶠ p in 𝓝[{p | 0 < p.1}] chartPtOut, reinChartMap (reinChartMapIn p) = p := by
  filter_upwards [l6s_tendsto_chartReflect.eventually
    (eventually_reinChartMapIn_reinChartMap fullerSwitchData_in)] with p hp
  rw [reinChartMapIn_eq] at hp
  have := congrArg chartReflect hp
  rwa [chartReflect_chartReflect, chartReflect_chartReflect, ← reinChartMapIn_eq] at this

/-- **`F⁻¹ ∘ F = id` for `r > 0` near the fixed point** (time reversal of trajectories, the forward
instance of `eventually_reinChartMapIn_reinChartMap`). -/
theorem eventually_reinChartMapIn_reinChartMap_out :
    ∀ᶠ p in 𝓝[{p | 0 < p.1}] chartPtOut, reinChartMapIn (reinChartMap p) = p := by
  have h := eventually_reinChartMapIn_reinChartMap fullerSwitchData_out
  simp only [one_mul] at h
  exact h

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

/-! ### Lemma 14.3.1: the analytic diffeomorphism (Step 10, the book's way)

`F` and `F⁻¹` are analytic at the fixed point, which they fix, and inverse for `r > 0` near it; by
the identity theorem they are inverse on a ball around it, which gives the open partial
homeomorphism. -/

/-- **Analytic continuation of an inverse** (the identity theorem on a ball,
`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`): if `f` and `g` are analytic at `c = f c` and
`g (f p) = p` for `p` near `c` in an open set `S` whose closure contains `c`, then `g (f p) = p` on
a neighborhood of `c`. -/
private lemma l6s_eventually_comp_eq {f g : ℝ × (Fin 3 → ℝ) → ℝ × (Fin 3 → ℝ)}
    {c : ℝ × (Fin 3 → ℝ)} {S : Set (ℝ × (Fin 3 → ℝ))} (hS : IsOpen S) (hcS : c ∈ closure S)
    (hf : AnalyticAt ℝ f c) (hg : AnalyticAt ℝ g c) (hfc : f c = c)
    (h : ∀ᶠ p in 𝓝[S] c, g (f p) = p) : ∀ᶠ p in 𝓝 c, g (f p) = p := by
  obtain ⟨ε₁, hε₁, hg₁⟩ := Metric.eventually_nhds_iff_ball.1 hg.eventually_analyticAt
  have hf₁ : ∀ᶠ p in 𝓝 c, AnalyticAt ℝ f p ∧ f p ∈ Metric.ball c ε₁ := by
    refine hf.eventually_analyticAt.and ?_
    have := hf.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds (f c) hε₁)
    rw [hfc] at this
    exact this
  obtain ⟨ε₂, hε₂, hf₂⟩ := Metric.eventually_nhds_iff_ball.1 hf₁
  have hgf : AnalyticOnNhd ℝ (g ∘ f) (Metric.ball c ε₂) := fun p hp ↦
    (hg₁ _ (hf₂ p hp).2).comp (hf₂ p hp).1
  have hid : AnalyticOnNhd ℝ id (Metric.ball c ε₂) := fun _ _ ↦ analyticAt_id
  -- a point of `S` near `c` around which `g ∘ f = id`
  obtain ⟨V, hVo, hcV, hVS⟩ := mem_nhdsWithin.1 h
  have hW : IsOpen (V ∩ Metric.ball c ε₂ ∩ S) := (hVo.inter Metric.isOpen_ball).inter hS
  obtain ⟨z₀, hz₀⟩ : (V ∩ Metric.ball c ε₂ ∩ S).Nonempty :=
    mem_closure_iff.1 hcS _ (hVo.inter Metric.isOpen_ball) ⟨hcV, Metric.mem_ball_self hε₂⟩
  have hz : (g ∘ f) =ᶠ[𝓝 z₀] id := by
    filter_upwards [hW.mem_nhds hz₀] with p hp
    exact hVS ⟨hp.1.1, hp.2⟩
  have heq := hgf.eqOn_of_preconnected_of_eventuallyEq hid (convex_ball c ε₂).isPreconnected
    hz₀.1.2 hz
  filter_upwards [Metric.ball_mem_nhds c hε₂] with p hp
  exact heq hp

private lemma l6s_mem_closure : chartPtOut ∈ closure {p : ℝ × (Fin 3 → ℝ) | 0 < p.1} := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  refine ⟨(ε / 2, xTildeOut), show (0 : ℝ) < ε / 2 by linarith, ?_⟩
  rw [chartPtOut, Prod.dist_eq, dist_self, Real.dist_eq, zero_sub, abs_neg,
    abs_of_pos (by linarith : (0 : ℝ) < ε / 2), max_eq_left (by linarith)]
  linarith

/-- **Lemma 14.3.1** (`lem:analytic-extension`, TeX 11766–11772). The Reinhardt–Poincaré map `F`
(initially defined for `r > 0`) extends to an analytic diffeomorphism in a neighborhood of the fixed
point `(0, x̃_out) ∈ ℝ⁴` (including non-positive values of `r`), such that `F` coincides with the
Fuller–Poincaré map at `r = 0`.

Proof, the book's (module docstring, Steps 1–10): `F = extMap fullerSwitchData_out` (Steps 1–9 at
`x̃_out`) and `F⁻¹ = extMapBack` (the same lemmas at the reflected point, `fullerSwitchData_in`) are
analytic at the fixed point and fix it; for `r > 0` near it they are the forward and backward
Reinhardt–Poincaré maps, which are inverse there by the time reversal of trajectories
(`eventually_reinChartMapIn_reinChartMap_out`, `eventually_reinChartMap_reinChartMapIn`); by
analytic continuation (`l6s_eventually_comp_eq`) they are inverse on a neighborhood `W`, and `F` on
`W ∩ F⁻¹ W` with inverse `F⁻¹` on `W ∩ (F⁻¹)⁻¹ W` is the analytic diffeomorphism.

A shorter argument: the inverse function theorem. `DF(0, x̃_out)` is block triangular,
`(r_scale, 0; *, D fullerChartMap(x̃_out))` (`∂_r F₁ = r_scale` from `extDivA_base`; `∂_{x̃} F₁ = 0`
and `∂_{x̃} F₂ = D fullerChartMap` because the divisor `r = 0` is invariant,
`eventually_extMap_divisor`), and it is invertible because `det D fullerChartMap(x̃_out) =
D(r_scale) ≈ 4.16 × 10⁻⁷ > 0`: the Jacobian determinant `jacDet` of Chapter 13's certified
Jacobian `jacobianOut r_scale`, conjugate to `D fullerChartMap` (`hasFDerivAt_fullerChartMap`),
has the exact Taylor certificate `D(r) = d₀ - (e₁ s + ⋯ + e₅ s⁵)`, `s = r - c`, at the convergent
`c = 3961388236/631380705` of `r_scale` (`|r_scale - c| ≤ 10⁻¹⁸`, from `rScale_fine_bounds`), with
`d₀ ≈ 4.1626 × 10⁻⁷` and `0 < e_k ≤ 6.1 × 10⁸`. Then `HasStrictFDerivAt.toOpenPartialHomeomorph`
and `OpenPartialHomeomorph.analyticAt_symm` give the analytic inverse directly, with no backward
construction (Remark 14.3.4, which identifies that inverse with the backward Reinhardt–Poincaré map,
then needs the time reversal of trajectories on its own). -/
theorem lemma14_3_1 :
    ∃ e : OpenPartialHomeomorph (ℝ × (Fin 3 → ℝ)) (ℝ × (Fin 3 → ℝ)),
      IsReinhardtPoincareExtension e := by
  set F := extMap fullerSwitchData_out with hFdef
  set G := extMapBack with hGdef
  have hFa : AnalyticAt ℝ F chartPtOut := analyticAt_extMap fullerSwitchData_out
  have hGa : AnalyticAt ℝ G chartPtOut := analyticAt_extMapBack
  have hFc : F chartPtOut = chartPtOut := l6d_E_chartPtOut
  have hGc : G chartPtOut = chartPtOut := extMapBack_chartPtOut
  -- `F` and `F⁻¹` are the Reinhardt–Poincaré maps for `r > 0`; `F` is the Fuller map at `r = 0`
  have hF : ∀ᶠ p in 𝓝 chartPtOut, 0 < p.1 → F p = reinChartMap p := by
    filter_upwards [eventually_reinChartMap_eq_extMap fullerSwitchData_out] with p hp hp1
    exact (hp (by simpa using hp1)).symm
  have hG : ∀ᶠ p in 𝓝 chartPtOut, 0 < p.1 → G p = reinChartMapIn p := eventually_extMapBack_eq
  have hdiv : ∀ᶠ p in 𝓝 chartPtOut, p.1 = 0 → F p = (0, fullerChartMap p.2) := by
    have hc : ContinuousAt (fun q : ℝ × (Fin 3 → ℝ) ↦ q.2) chartPtOut := continuousAt_snd
    filter_upwards [hc.eventually eventually_extMap_divisor] with q hq h0
    rw [show q = (0, q.2) from Prod.ext h0 rfl]
    exact hq
  -- both preserve `r > 0` near the fixed point
  set S := {p : ℝ × (Fin 3 → ℝ) | 0 < p.1} with hSdef
  have hSo : IsOpen S := isOpen_lt continuous_const continuous_fst
  have hFt : Tendsto F (𝓝[S] chartPtOut) (𝓝[S] chartPtOut) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := hFa.continuousAt.tendsto
      rw [hFc] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [eventually_isSwitch_reinSwitchTime, nhdsWithin_le_nhds hF,
        self_mem_nhdsWithin] with p ⟨_, _, _, hdom, _⟩ hFp hp
      change 0 < (F p).1
      rw [hFp hp]
      exact hdom.1
  have hGt : Tendsto G (𝓝[S] chartPtOut) (𝓝[S] chartPtOut) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := hGa.continuousAt.tendsto
      rw [hGc] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [eventually_isSwitch_reinSwitchTime_in, nhdsWithin_le_nhds hG,
        self_mem_nhdsWithin] with p ⟨_, _, _, hpos, _⟩ hGp hp
      change 0 < (G p).1
      rw [hGp hp]
      exact hpos
  -- `F` and `F⁻¹` are inverse for `r > 0` near the fixed point (time reversal of trajectories)
  have hGF : ∀ᶠ p in 𝓝[S] chartPtOut, G (F p) = p := by
    filter_upwards [hFt.eventually (nhdsWithin_le_nhds hG), hFt.eventually self_mem_nhdsWithin,
      nhdsWithin_le_nhds hF, self_mem_nhdsWithin, eventually_reinChartMapIn_reinChartMap_out]
      with p h1 h2 h3 h4 h5
    rw [h1 h2, h3 h4, h5]
  have hFG : ∀ᶠ p in 𝓝[S] chartPtOut, F (G p) = p := by
    filter_upwards [hGt.eventually (nhdsWithin_le_nhds hF), hGt.eventually self_mem_nhdsWithin,
      nhdsWithin_le_nhds hG, self_mem_nhdsWithin, eventually_reinChartMap_reinChartMapIn]
      with p h1 h2 h3 h4 h5
    rw [h1 h2, h3 h4, h5]
  -- by analytic continuation, they are inverse on a neighborhood of the fixed point
  have hGF' := l6s_eventually_comp_eq hSo l6s_mem_closure hFa hGa hFc hGF
  have hFG' := l6s_eventually_comp_eq hSo l6s_mem_closure hGa hFa hGc hFG
  obtain ⟨W, hWsub, hWo, hcW⟩ := eventually_nhds_iff.1 (hFa.eventually_analyticAt.and
    (hGa.eventually_analyticAt.and (hGF'.and (hFG'.and (hF.and hdiv)))))
  have hFW : ContinuousOn F W := fun p hp ↦ (hWsub p hp).1.continuousAt.continuousWithinAt
  have hGW : ContinuousOn G W := fun p hp ↦ (hWsub p hp).2.1.continuousAt.continuousWithinAt
  -- hence `F` is a diffeomorphism
  let e : OpenPartialHomeomorph (ℝ × (Fin 3 → ℝ)) (ℝ × (Fin 3 → ℝ)) :=
    { toFun := F
      invFun := G
      source := W ∩ F ⁻¹' W
      target := W ∩ G ⁻¹' W
      map_source' := fun p hp ↦ ⟨hp.2, by
        change G (F p) ∈ W
        rw [(hWsub p hp.1).2.2.1]
        exact hp.1⟩
      map_target' := fun p hp ↦ ⟨hp.2, by
        change F (G p) ∈ W
        rw [(hWsub p hp.1).2.2.2.1]
        exact hp.1⟩
      left_inv' := fun p hp ↦ (hWsub p hp.1).2.2.1
      right_inv' := fun p hp ↦ (hWsub p hp.1).2.2.2.1
      open_source := hFW.isOpen_inter_preimage hWo hWo
      open_target := hGW.isOpen_inter_preimage hWo hWo
      continuousOn_toFun := hFW.mono inter_subset_left
      continuousOn_invFun := hGW.mono inter_subset_left }
  refine ⟨e, ⟨hcW, ?_⟩, hFc, fun p hp ↦ (hWsub p hp.1).1, fun p hp ↦ (hWsub p hp.1).2.1,
    fun p hp hp1 ↦ (hWsub p hp.1).2.2.2.2.1 hp1, fun p hp hp0 ↦ (hWsub p hp.1).2.2.2.2.2 hp0⟩
  change F chartPtOut ∈ W
  rw [hFc]
  exact hcW

end SmoothedPolygons
