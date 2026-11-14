module

public import SmoothedPolygons.Ch14.Asymptotics
public import SmoothedPolygons.Ch13.Jacobian
public import Basic.Analysis.Analytic.DivisionByCoordinate
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Topology.OpenPartialHomeomorph.Defs
public import Mathlib.LinearAlgebra.Charpoly.Basic

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

## The book's proof (TeX 11784–11872), step by step

1. The chart is rational in `(r₀, x̃₀)` and `(1 + r₀ x̃₂₁)⁻¹` with nonzero denominators near the
   fixed point, hence analytic (real or complex values).
2. The vertex flow is given by matrix exponentials (`iso_vertexFlow`), analytic in `t` and in the
   initial data; substitute `t = s r₀`.
3. Lemma 14.2.4 and division of power series (`AnalyticAt.exists_eq_pow_smul_of_isBigO`,
   `Basic/Analysis/Analytic/DivisionByCoordinate.lean`): `χ̃₂₁ = χ₂₁/r₀³` is analytic near
   `r₀ = 0` (`analyticAt_rescaledChi`). (The book uses the pointwise Lemma 14.2.4; the division
   lemma needs `O(r₀³)` for each fixed `(s, x̃₀)`, which is what Lemma 14.2.4 gives.)
4. At `(0, x̃_out)` the least positive zero `s_{sw,out} ≈ 8.84` of `χ̃₂₁(·, 0, x̃_out)` (the Fuller
   cubic `24 RR(ζ - 1, z₃(s))`) is simple and `s = 0` is not a zero: exact, from Chapter 13
   (`firstSwitchTime_qOutCart`, rescaled by `λ = 1/(2 Im q_out,₁)`, G14.12; the simple root is the
   one of `SmoothedPolygons/Ch13/Jacobian.lean`).
5. The analytic implicit function theorem (Mathlib's `ContDiffAt.implicitFunction` with `n = ω`)
   extends `s_sw` analytically to a neighborhood of the fixed point, `r₀ ≤ 0` included.
6. Rotate by `Ad_{R⁻¹}` (`Y_sw = Ad_{R⁻¹} Y(r₀ s_sw)` for `Y = X, Λ₁, Λ_R`).
7. `X_sw - J` and `Λ₁sw + (3/2) J` are divisible by `r₀` and `r₀²` (G14.7: asserted "regardless of
   the precise form of `s_sw`"; true because the rescaled flow `ẑ/r₀^k` of Lemma 14.2.3 is
   analytic, step 3 applied to `fullerCoords`, and `phaseOfFuller` is analytic).
8. Divide by the `(1, 1)` entry of `(X_sw - J)/r₀`, which is `r_scale ≈ 6.27 ≠ 0` at the fixed point
   (`rScale_spec`); its reciprocal is analytic. This gives `F` on a neighborhood, analytic.
9. On `r = 0`, `F` is the Fuller–Poincaré map (Lemmas 14.2.3–14.2.4 at `r₀ = 0`).
10. The backward map `F⁻¹` is built the same way (time reversal, `iso_vertexFlow_reinTau`); `F ∘ F⁻¹
   = id` for `r₀ > 0`, hence near the fixed point by the identity theorem
   (`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`), so `F` is a diffeomorphism.
The χ₂₃ check missing from the book (G14.5): at `(0, x̃_out)` the Fuller switching function for
`ζ → ζ²` is `√3 s (y₂ + y₁ s/2 + s²/12)` with `y₁, y₂ > 0` (`qOutCart_signs`), positive on
`(0, s_sw]`; after one more division by `s` (`χ₂₃` vanishes at `s = 0`) it is positive on
`[0, s_sw]`, hence so is the rescaled Reinhardt `χ₂₃/(s r₀³)` near the fixed point (compactness of
`[0, s_sw]`). A simpler route to the diffeomorphism property: `DF(0, x̃_out)` is invertible (its
eigenvalues are `r_scale` and those of Lemma 13.5.5, all nonzero), so the inverse function theorem
(`HasStrictFDerivAt.localInverse`, analytic by `ContDiffAt.to_localInverse` with `n = ω`) gives the
analytic inverse without the backward map; the book's route is the one to follow.

Size: 1,500–3,000 lines (the analyticity of the closed-form flow in `(t, q)`, including its
quadratures, is the bulk; the rest is the implicit function theorem and bookkeeping).
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

/-- `x̃_out` is a fixed point of the Fuller–Poincaré map in the chart (Lemma 13.5.2: `F(q_out) =
ζ² (r_scale q_out,₁, r_scale² q_out,₂, r_scale³ q_out,₃)`, `poincare_qOutCart`, with
`fullerChartInv` invariant under rescalings). -/
theorem fullerChartMap_xTildeOut : fullerChartMap xTildeOut = xTildeOut := by
  sorry

/-- **The linearization of the Fuller–Poincaré map at `q_out` is a contraction** ("We have seen
that the linearization of the Fuller–Poincaré map `F` near the fixed point is a contraction on the
three dimensional exceptional divisor", TeX 11912–11914): `fullerChartMap` is differentiable at
`x̃_out` and every complex eigenvalue of its derivative has modulus `< 1/10` (the bound quoted at
TeX 11960–11961). Proof: the change of normalization `x̃ ↦ chartOf (z(x̃))` (`Im z₁ = 1/2` to
`Re z₁ = -1`) is smooth near `x̃_out` with smooth inverse (`chartCart`, rescaled) and conjugates
`fullerChartMap` to Chapter 13's `chartMap` (`chartMap_eventuallyEq_chartOf`,
`eventually_contDiffAt_chartOf`); the eigenvalues are those of `jacobianOut r_scale`
(`hasFDerivAt_chartMap`, `norm_lt_of_aeval_charpoly_jacobianOut_eq_zero`). -/
theorem hasFDerivAt_fullerChartMap :
    ∃ D : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ), HasFDerivAt fullerChartMap D xTildeOut ∧
      ∀ μ : ℂ, Polynomial.aeval μ (LinearMap.charpoly (D : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ))) = 0 →
        ‖μ‖ < 1 / 10 := by
  sorry

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
  sorry

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
  sorry

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

/-- **Lemma 14.3.1** (TeX 11766–11772). The Reinhardt–Poincaré map `F` (initially defined for
`r > 0`) extends to an analytic diffeomorphism in a neighborhood of the fixed point
`(0, x̃_out) ∈ ℝ⁴` (including non-positive values of `r`), such that `F` coincides with the
Fuller–Poincaré map at `r = 0`. (Proof: the module docstring.) -/
theorem lemma14_3_1 :
    ∃ e : OpenPartialHomeomorph (ℝ × (Fin 3 → ℝ)) (ℝ × (Fin 3 → ℝ)),
      IsReinhardtPoincareExtension e := by
  sorry

end SmoothedPolygons
