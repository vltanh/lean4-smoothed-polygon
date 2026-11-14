module

public import SmoothedPolygons.Ch14.AnalyticExtension
public import SmoothedPolygons.AppA.StableManifold

/-!
# Chapter 14: stable and unstable manifolds at `q_out` and `q_in` (Thm 14.3.3, Remark 14.3.4)

§14.3 of Hales–Vajjha, *Packings of Smoothed Polygons* (TeX 11874–11919), after Lemma 14.3.1: the
fixed point `(0, x̃_out)` of the extended Reinhardt–Poincaré map `F` is hyperbolic, its local
unstable manifold is a `C^∞` curve, and near the fixed point its local stable manifold is the
exceptional divisor `r = 0` (Theorem 14.3.3); by time reversal the fixed point `q_in` has a
one-dimensional local stable manifold and the divisor as its local unstable manifold
(Remark 14.3.4).

* `theorem14_3_3`, for every analytic extension `e` of Lemma 14.3.1
  (`IsReinhardtPoincareExtension e`);
* `reinChartMapIn`: the Reinhardt–Poincaré map in the mirrored chart `lieChartIn` at `q_in` (G14.9:
  the chart (14.1.1)–(14.1.2) does not contain `q_in`, whose representatives have `Im z₁ < 0`);
* `remark14_3_4`: in the mirrored chart the point `(0, x̃_out)` is `q_in`, the Reinhardt–Poincaré
  map there is the inverse of `e` near the fixed point (time reversal, `F⁻¹ = τ F τ`), and `e⁻¹` has
  a hyperbolic fixed point whose local stable manifold is the curve of Theorem 14.3.3 and whose
  local unstable manifold is the divisor.

## The book's proof of Theorem 14.3.3 (TeX 11905–11919), and what is added

"Near the fixed point, the analytic continuation `F` … agrees with the Fuller–Poincaré map, when
`r = 0` … The exceptional divisor `r = 0` is a three-dimensional invariant subset … the
linearization of the Fuller–Poincaré map `F` near the fixed point is a contraction on the three
dimensional exceptional divisor. Moving away from the exceptional divisor in the radial direction,
the Reinhardt–Poincaré map has scaling factor `r_scale > 1`. The Fuller–Poincaré map [read: the
extended map, G14.8] is therefore hyperbolic, with three eigenvalues `|λ| < 1` and one eigenvalue
`|λ| > 1`. By general theory, the unstable curve is `C^∞`, because the diffeomorphism is `C^∞`."

1. Invariance of `r = 0` (`IsReinhardtPoincareExtension`: `e (0, x̃) = (0, fullerChartMap x̃)`), so
   `DF(0, x̃_out)` is block triangular: first row `(r_scale, 0)` (`∂_r F.1 = (1, 1)` entry of
   `(X_sw - J)/r₀` at the fixed point, which is `r_scale`, TeX 11849–11856), lower-right block
   `D fullerChartMap(x̃_out)` (`hasFDerivAt_fullerChartMap`, eigenvalues of modulus `< 1/10`):
   `hasStrictFDerivAt_extension`.
2. Hence the characteristic polynomial is `(X - r_scale) χ_F` (block triangular), the eigenvalues
   are `r_scale > 1` (`rScale_spec`), simple since `χ_F(r_scale) ≠ 0`, and three of modulus
   `< 1/10`: hyperbolic.
3. Theorem A.3.1 (`theoremA_3_1`, with `r = ∞`; `e` is analytic, hence `C^∞`): the local unstable
   set is a `C^∞` curve tangent to the `r_scale`-eigenvector `(1, v)`, so a graph over the
   `r`-axis ("we use `t = r` as the local parameter", TeX 11931–11932).
4. `W^s_loc = {r = 0}` near the fixed point (implicit in the book, G14.8): by Theorem A.3.1 the
   local stable set is a 3-dimensional graph over the stable summand `{0} × ℝ³`, and the divisor
   points near `x̃_out` are in it (the Fuller map contracts there, `hasFDerivAt_fullerChartMap` and
   linearized stability), so the two coincide near the fixed point; alternatively and more simply
   (no stable manifold theorem): `F.1(r, x̃) = r m(r, x̃)` with `m ≥ λ > 1` near the fixed point, so
   no orbit with `r ≠ 0` stays in a small box, and a box can be chosen forward invariant for the
   Fuller part (adapted norm).
Size: Theorem 14.3.3, 400–800 lines given Theorem A.3.1.

Remark 14.3.4 (no proof in the book, "By time reversal"): `iso_vertexFlow_reinTau`,
`switchingFn_reinTau` and `reinTau_spec` give `reinPoincare (τ (reinPoincare q)) = τ q` at the
switching points near `q_out` (the Reinhardt form of `F⁻¹ = τ F τ`, Lemma 13.2.5), so the map in
the mirrored chart is `F_in = τ F⁻¹ τ`, i.e. `e⁻¹` in the chart; then Theorem 14.3.3 for `e` is
the remark for `e⁻¹` (with `Function.localStableSet_symm_eq_localUnstableSet`). The point
`(0, x̃_out)` of the mirrored chart is `q_in` (`fullerCoords_reinTau`, `tauQuot_qOut`).

All the claims at `q_in`, including the switching structure from `lieChartIn p`, are to be proved
through `F_in = τ F⁻¹ τ` (the arc from `τ q` is the time reversal of the arc of `F⁻¹` ending at
`q`, with the controls relabelled), **not** by direct estimates at `q_in`: there the Fuller
switching functions from `τ(q_out)` have two near-degenerate pairs of roots just after the switch
at `s = 1.409426…` (`= s_{sw,out}/r_scale`), namely `1.648502… ± 0.008433… i` (`χ_{ζ→1}`) and a
near-tangency of `χ₂₃` at `1.5 ± 0.0529 i`; both are images under `s ↦ (s_{sw,out} - s')/r_scale`
of roots at `q_out` (of the quadratic factor of `χ_{ζ→ζ²}` at `s' ≈ -1.5 ± 0.054 i`, and of
`χ_{ζ→1}` at `s' ≈ -0.568 ± 0.332 i`), where they are far from the real axis. Size: 300–600
lines.
-/

@[expose] public section

namespace SmoothedPolygons

open Complex Set Filter Topology
open TriFuller
open scoped ContDiff

/-- The Reinhardt–Poincaré map in the mirrored chart at `q_in` (Remark 14.3.4). The forward
dynamics near `q_in` follows the same rule as near `q_out` (control `e₂` from the wall `χ₂₃ = 0`,
switch at `χ₂₁ = 0`, rotation `Ad_{R⁻¹}`): the time reversal maps the cyclic switching sequence
`3 → 2 → 1 → 3` to itself. -/
noncomputable def reinChartMapIn (p : ℝ × (Fin 3 → ℝ)) : ℝ × (Fin 3 → ℝ) :=
  lieChartInInv (reinPoincare (lieChartIn p))

/-- **The derivative of the extended map at the fixed point** (TeX 11905–11917: "The exceptional
divisor `r = 0` is a three-dimensional invariant subset … the linearization of the Fuller–Poincaré
map … is a contraction on the three dimensional exceptional divisor. Moving away from the
exceptional divisor in the radial direction, the Reinhardt–Poincaré map has scaling factor
`r_scale`"): for every analytic extension `e` of Lemma 14.3.1, `e` is strictly differentiable at
`(0, x̃_out)` (it is analytic), `∂_r e₁ = r_scale` (the `(1, 1)` entry of `(X_sw - J)/r₀` at the
fixed point, TeX 11849–11856), `∂_{x̃} e₁ = 0` (the divisor `r = 0` is invariant), and
`∂_{x̃} e₂` is the derivative of the Fuller–Poincaré map in the chart (`e (0, x̃) =
(0, fullerChartMap x̃)`), whose eigenvalues have modulus `< 1/10` (`hasFDerivAt_fullerChartMap`).

These derivative facts are all that Theorem 16.4.1 and the assembly of Theorem 16.3.1 use at
`q_out` (the hyperbolic box, `qOut0_not_mem_switchClusterSet`): no stable manifold theorem is
needed there. Proof: `AnalyticAt.hasStrictFDerivAt`; the invariance of `{r = 0}` gives the zero
block; `IsReinhardtPoincareExtension` gives `e (0, x̃) = (0, fullerChartMap x̃)` on the source;
`∂_r e₁` from `reinChartMap` (`r' = X'₁₁ = r · (X_sw - J)₁₁/r₀`) and the Fuller fixed point
(`poincare_qOutCart`: the first coordinate of `ζ F(z(x̃_out))` is `r_scale` times that of
`z(x̃_out)`). -/
theorem hasStrictFDerivAt_extension
    {e : OpenPartialHomeomorph (ℝ × (Fin 3 → ℝ)) (ℝ × (Fin 3 → ℝ))}
    (he : IsReinhardtPoincareExtension e) :
    HasStrictFDerivAt e (fderiv ℝ e chartPtOut) chartPtOut ∧
      (fderiv ℝ e chartPtOut ((1 : ℝ), (0 : Fin 3 → ℝ))).1 = rScale ∧
      (∀ v : Fin 3 → ℝ, (fderiv ℝ e chartPtOut ((0 : ℝ), v)).1 = 0) ∧
      HasFDerivAt fullerChartMap (fderiv ℝ fullerChartMap xTildeOut) xTildeOut ∧
      ∀ v : Fin 3 → ℝ, (fderiv ℝ e chartPtOut ((0 : ℝ), v)).2 =
        fderiv ℝ fullerChartMap xTildeOut v := by
  sorry

/-- **Theorem 14.3.3** (TeX 11891–11895). The fixed point `(0, x̃_out)` of the diffeomorphism `F`
(any analytic extension `e` of the Reinhardt–Poincaré map, Lemma 14.3.1) is hyperbolic: the
eigenvalues of `DF(0, x̃_out)` are `r_scale > 1`, a simple root of the characteristic polynomial,
and three of modulus `< 1/10`; the derivative is block triangular, so the characteristic polynomial
is `(X - r_scale)` times that of the Fuller–Poincaré map in the chart. The local unstable
manifold is a `C^∞` curve, the graph `r ↦ (r, γ(r))` of a `C^∞` map with `γ(0) = x̃_out`. In a
neighborhood of the fixed point, the local stable manifold coincides with the three-dimensional
exceptional divisor `r = 0`. -/
theorem theorem14_3_3 {e : OpenPartialHomeomorph (ℝ × (Fin 3 → ℝ)) (ℝ × (Fin 3 → ℝ))}
    (he : IsReinhardtPoincareExtension e) :
    (fderiv ℝ e chartPtOut).IsHyperbolic ∧
      LinearMap.charpoly (fderiv ℝ e chartPtOut : (ℝ × (Fin 3 → ℝ)) →ₗ[ℝ] (ℝ × (Fin 3 → ℝ))) =
        (Polynomial.X - Polynomial.C rScale) * LinearMap.charpoly
          (fderiv ℝ fullerChartMap xTildeOut : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) ∧
      (LinearMap.charpoly (fderiv ℝ e chartPtOut :
        (ℝ × (Fin 3 → ℝ)) →ₗ[ℝ] (ℝ × (Fin 3 → ℝ)))).rootMultiplicity rScale = 1 ∧
      Polynomial.aeval (rScale : ℂ) (LinearMap.charpoly
        (fderiv ℝ e chartPtOut : (ℝ × (Fin 3 → ℝ)) →ₗ[ℝ] (ℝ × (Fin 3 → ℝ)))) = 0 ∧
      (∀ μ : ℂ, Polynomial.aeval μ (LinearMap.charpoly
        (fderiv ℝ e chartPtOut : (ℝ × (Fin 3 → ℝ)) →ₗ[ℝ] (ℝ × (Fin 3 → ℝ)))) = 0 →
          μ = rScale ∨ ‖μ‖ < 1 / 10) ∧
      ∃ U ∈ 𝓝 chartPtOut, IsOpen U ∧ U ⊆ e.source ∧
        Function.localStableSet e chartPtOut U = {p ∈ U | p.1 = 0} ∧
        ∃ δ > 0, ∃ γ : ℝ → (Fin 3 → ℝ), ContDiffOn ℝ ∞ γ (Ioo (-δ) δ) ∧ γ 0 = xTildeOut ∧
          Function.localUnstableSet e chartPtOut U = (fun r ↦ (r, γ r)) '' Ioo (-δ) δ := by
  sorry

/-- **Remark 14.3.4** (TeX 11898–11902), in the mirrored chart (G14.9). "By time reversal, the
Reinhardt–Poincaré map `F` has a hyperbolic fixed point at `(0, x_in) ∈ ℝ⁴`, its local stable
manifold is one-dimensional, and its local unstable manifold is the three-dimensional exceptional
divisor." For an analytic extension `e` of Lemma 14.3.1:
* the point `(0, x̃_out)` of the mirrored chart lies over `q_in`: the class of
  `τ(z(x̃_out))` is `q_in`;
* near `(0, x̃_out)`, with `r > 0`, the switching structure from `lieChartIn p` is that of
  `eventually_isSwitch_reinSwitchTime` (the control `e₂` is the strict maximizer on `(0, t_sw)`,
  then beaten by `e₁`), and the Reinhardt–Poincaré map in the mirrored chart is the inverse of `e`:
  `e (reinChartMapIn p) = p`;
* `e⁻¹` has the hyperbolic fixed point `(0, x̃_out)`; its local stable manifold is the curve of
  Theorem 14.3.3 (the local unstable set of `e`) and its local unstable manifold is the divisor. -/
theorem remark14_3_4 {e : OpenPartialHomeomorph (ℝ × (Fin 3 → ℝ)) (ℝ × (Fin 3 → ℝ))}
    (he : IsReinhardtPoincareExtension e) :
    classOf (tau (fullerOfChart xTildeOut)) = qIn0 ∧
      (∀ᶠ p in 𝓝[{p | 0 < p.1}] chartPtOut,
        0 < reinSwitchTime (lieChartIn p) ∧
        (∀ t ∈ Ioo 0 (reinSwitchTime (lieChartIn p)), ∀ j : Fin 3, j ≠ 1 →
          phaseHam (iso_vertexFlow 1 (lieChartIn p) t) (vertex j) <
            phaseHam (iso_vertexFlow 1 (lieChartIn p) t) (vertex 1)) ∧
        (∀ ε > 0, ∃ t ∈ Ioo (reinSwitchTime (lieChartIn p)) (reinSwitchTime (lieChartIn p) + ε),
          phaseHam (iso_vertexFlow 1 (lieChartIn p) t) (vertex 1) <
            phaseHam (iso_vertexFlow 1 (lieChartIn p) t) (vertex 0)) ∧
        0 < (reinChartMapIn p).1 ∧ lieChartIn (reinChartMapIn p) = reinPoincare (lieChartIn p) ∧
        reinChartMapIn p ∈ e.source ∧ e (reinChartMapIn p) = p) ∧
      (fderiv ℝ e.symm chartPtOut).IsHyperbolic ∧
      ∃ U ∈ 𝓝 chartPtOut, IsOpen U ∧ U ⊆ e.source ∩ e.target ∧
        Function.localStableSet e.symm chartPtOut U = Function.localUnstableSet e chartPtOut U ∧
        Function.localUnstableSet e.symm chartPtOut U = {p ∈ U | p.1 = 0} ∧
        ∃ δ > 0, ∃ γ : ℝ → (Fin 3 → ℝ), ContDiffOn ℝ ∞ γ (Ioo (-δ) δ) ∧ γ 0 = xTildeOut ∧
          Function.localStableSet e.symm chartPtOut U = (fun r ↦ (r, γ r)) '' Ioo (-δ) δ := by
  sorry

end SmoothedPolygons
