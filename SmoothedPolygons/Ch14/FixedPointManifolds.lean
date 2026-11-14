module

public import SmoothedPolygons.Ch14.AnalyticExtension
public import SmoothedPolygons.AppA.StableManifold
import SmoothedPolygons.Ch7.Isolated.VertexFlow
import SmoothedPolygons.Ch7.Isolated.Return

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

## Status

Everything is proved; the only `sorry`s used are those of the general stable manifold theorem
(`Basic/Dynamics/StableManifold.lean`, proved in a separate package), through `theoremA_3_1`.

* `hasStrictFDerivAt_extension`: as planned (`l6d_tendsto_reinChartMap_fst_div` for `∂_r F₁`; the
  divisor `{r = 0}` for the `x̃`-derivatives).
* `theorem14_3_3`: the block form gives the characteristic polynomial (a `1 + 3` block matrix in the
  basis `(1, 0), (0, e_k)`, `Matrix.charpoly_fromBlocks_zero₁₂`) and the eigenvalues. The local
  sets are taken on a box `U = (-δ, δ) × N` (`l6j_main`). The stable set is the divisor by the
  direct argument of step 4 (no stable manifold theorem): on a ball, `t ↦ F₁(t, x̃) - t` is monotone
  (`∂_r F₁ > 1` near the fixed point, mean value theorem), so `|F₁| ≥ |r|` and an orbit with
  `r ≠ 0` cannot tend to the fixed point; `N` is an open forward invariant neighborhood of `x̃_out`
  attracted to it (linearized stability, `Function.isAsymptoticallyStable_of_hasFDerivAt`, and the
  points whose orbit stays in a small open set until it enters a Lyapunov neighborhood). The
  unstable set is Theorem A.3.1's graph over the unstable summand, which is the line `ℝ u` with
  `u₁ = 1` (the stable summand lies in `{0} × ℝ³`, the unstable one meets it only in `0` because
  some power of `D fullerChartMap` has norm `< 1`); a backward orbit from a point of the curve in
  `U` stays in `U` because `e⁻¹` maps `U` into the ball where `|F₁| ≥ |r|`.
* `remark14_3_4`, through `F_in = τ F⁻¹ τ` as planned: for `p` near the fixed point with `r > 0`,
  `p' = e⁻¹(p)` has `r > 0` (`F₁` preserves the sign of `r` on the ball) and `e(p') = p` is the
  Reinhardt–Poincaré map from `lieChart p'`; by the time reversal (`iso_vertexFlow_reinTau`), the
  rotation of the vertex flows (`l6j_adRinv_vertexFlow`, Grönwall uniqueness) and the flow property
  (`l6j_vertexFlow_add`), the `e₂`-flow from `lieChartIn p` is `t ↦ τ Ad_{R⁻¹}(q'(t_sw - t))` along
  the arc `q'` from `lieChart p'`, with `H(e₁) ↔ H(e₃)` exchanged. So the switching time is that of
  `q'`, the maximality on `(0, t_sw)` is that of `q'`, and the image is `lieChartIn p'`, i.e.
  `F_in(p) = p'`. The clause "`e₁` beats `e₂` right after `t_sw`" becomes `χ₂₃ < 0` on the
  `e₂`-flow from `lieChart p'` at small negative times, which `eventually_isSwitch_reinSwitchTime`
  does not give: it is the χ₂₃ check before the wall, `χ̃₂₃ = s H` with `H(0, 0, x̃_out) = Q(0) > 0`
  (`l6j_chi23_neg`, the division of `l6d_eventually_chi23_pos`). Hyperbolicity of `D(e⁻¹)`: its
  eigenvalues are the inverses of those of `DF` (complexified matrices, `spectrum.inv_mem_iff`).
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
  obtain ⟨hp, hfix, han, -, hrein, hful⟩ := he
  have hD : HasFDerivAt e (fderiv ℝ e chartPtOut) chartPtOut :=
    (han _ hp).differentiableAt.hasFDerivAt
  set D := fderiv ℝ e chartPtOut with hDdef
  -- the divisor through the fixed point
  have hpt : chartPtOut = ((0 : ℝ), xTildeOut) := rfl
  have hsrc : ∀ᶠ x in 𝓝 xTildeOut, ((0 : ℝ), x) ∈ e.source := by
    have hc : ContinuousAt (fun x : Fin 3 → ℝ ↦ ((0 : ℝ), x)) xTildeOut := by fun_prop
    exact hc.preimage_mem_nhds (e.open_source.mem_nhds hp)
  have hcomp : HasFDerivAt (fun x : Fin 3 → ℝ ↦ e ((0 : ℝ), x))
      (D.comp (ContinuousLinearMap.inr ℝ ℝ (Fin 3 → ℝ))) xTildeOut :=
    hD.comp xTildeOut (hasFDerivAt_prodMk_right (0 : ℝ) xTildeOut)
  have heq : (fun x : Fin 3 → ℝ ↦ e ((0 : ℝ), x)) =ᶠ[𝓝 xTildeOut]
      fun x ↦ ((0 : ℝ), fullerChartMap x) :=
    hsrc.mono fun x hx ↦ hful _ hx rfl
  have h1 : HasFDerivAt (fun x : Fin 3 → ℝ ↦ (e ((0 : ℝ), x)).1)
      (0 : (Fin 3 → ℝ) →L[ℝ] ℝ) xTildeOut :=
    (hasFDerivAt_const (0 : ℝ) xTildeOut).congr_of_eventuallyEq
      (heq.mono fun x hx ↦ by simp [hx])
  have h1' := hcomp.fst.unique h1
  have h2 : HasFDerivAt fullerChartMap ((ContinuousLinearMap.snd ℝ ℝ (Fin 3 → ℝ)).comp
      (D.comp (ContinuousLinearMap.inr ℝ ℝ (Fin 3 → ℝ)))) xTildeOut :=
    hcomp.snd.congr_of_eventuallyEq (heq.mono fun x hx ↦ by simp [hx])
  -- the radial derivative
  have hr : HasDerivAt (fun r : ℝ ↦ (e (r, xTildeOut)).1) (D ((1 : ℝ), (0 : Fin 3 → ℝ))).1 0 := by
    have hpath : HasDerivAt (fun r : ℝ ↦ (r, xTildeOut)) ((1 : ℝ), (0 : Fin 3 → ℝ)) 0 :=
      (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 xTildeOut)
    exact hD.fst.comp_hasDerivAt (0 : ℝ) hpath
  have hslope : Tendsto (fun r ↦ (reinChartMap (r, xTildeOut)).1 / r) (𝓝[>] 0)
      (𝓝 (D ((1 : ℝ), (0 : Fin 3 → ℝ))).1) := by
    have ht := (hasDerivAt_iff_tendsto_slope.1 hr).mono_left
      (nhdsWithin_mono (0 : ℝ) (show Ioi (0 : ℝ) ⊆ {0}ᶜ from fun r hr ↦ ne_of_gt hr))
    have hc : ContinuousAt (fun r : ℝ ↦ (r, xTildeOut)) 0 := by fun_prop
    have hsrc' : ∀ᶠ r in 𝓝[>] (0 : ℝ), (r, xTildeOut) ∈ e.source :=
      nhdsWithin_le_nhds (hc.preimage_mem_nhds (e.open_source.mem_nhds hp))
    refine ht.congr' ?_
    filter_upwards [hsrc', self_mem_nhdsWithin] with r hrs hr0
    have h0 : (e (0, xTildeOut)).1 = 0 := by rw [← hpt, hfix]; rfl
    rw [slope_def_field, h0, sub_zero, sub_zero, hrein _ hrs hr0]
  refine ⟨(han _ hp).hasStrictFDerivAt, tendsto_nhds_unique hslope
    l6d_tendsto_reinChartMap_fst_div, fun v ↦ ?_, h2.differentiableAt.hasFDerivAt, fun v ↦ ?_⟩
  · simpa using congrArg (fun L : (Fin 3 → ℝ) →L[ℝ] ℝ ↦ L v) h1'
  · rw [h2.fderiv]
    rfl


/-! ### The derivative at the fixed point: block form, characteristic polynomial, spectrum -/

/-- `DF(0, x̃_out)` is block triangular: `(a, v) ↦ (r_scale a, a w₀ + D fullerChartMap v)`. -/
private lemma l6j_fderiv_apply {e : OpenPartialHomeomorph (ℝ × (Fin 3 → ℝ)) (ℝ × (Fin 3 → ℝ))}
    (he : IsReinhardtPoincareExtension e) : ∃ w₀ : Fin 3 → ℝ, ∀ x : ℝ × (Fin 3 → ℝ),
      fderiv ℝ e chartPtOut x =
        (rScale * x.1, x.1 • w₀ + fderiv ℝ fullerChartMap xTildeOut x.2) := by
  obtain ⟨-, h1, h2, -, h3⟩ := hasStrictFDerivAt_extension he
  refine ⟨(fderiv ℝ e chartPtOut ((1 : ℝ), 0)).2, fun x ↦ ?_⟩
  have hx : x = x.1 • ((1 : ℝ), (0 : Fin 3 → ℝ)) + ((0 : ℝ), x.2) := by
    refine Prod.ext ?_ ?_ <;> simp
  conv_lhs => rw [hx]
  rw [map_add, map_smul]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.smul_fst, h1, h2, smul_eq_mul, add_zero, mul_comm]
  · simp only [Prod.snd_add, Prod.smul_snd, h3]

/-- The eigenvalues of the Fuller–Poincaré map in the chart have modulus `< 1/10`. -/
private lemma l6j_DF_spec (μ : ℂ) (hμ : Polynomial.aeval μ (LinearMap.charpoly
    (fderiv ℝ fullerChartMap xTildeOut : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ))) = 0) : ‖μ‖ < 1 / 10 := by
  obtain ⟨D, hD, hspec⟩ := hasFDerivAt_fullerChartMap
  rw [hD.fderiv] at hμ
  exact hspec μ hμ

/-- The characteristic polynomial of the block triangular derivative. -/
private lemma l6j_charpoly {e : OpenPartialHomeomorph (ℝ × (Fin 3 → ℝ)) (ℝ × (Fin 3 → ℝ))}
    (he : IsReinhardtPoincareExtension e) :
    LinearMap.charpoly (fderiv ℝ e chartPtOut : (ℝ × (Fin 3 → ℝ)) →ₗ[ℝ] (ℝ × (Fin 3 → ℝ))) =
      (Polynomial.X - Polynomial.C rScale) * LinearMap.charpoly
        (fderiv ℝ fullerChartMap xTildeOut : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) := by
  classical
  obtain ⟨w₀, hD⟩ := l6j_fderiv_apply he
  let b := (Module.Basis.singleton Unit ℝ).prod (Pi.basisFun ℝ (Fin 3))
  have hb1 : ∀ i, b (Sum.inl i) = ((1 : ℝ), (0 : Fin 3 → ℝ)) := fun i ↦ by
    refine Prod.ext ?_ ?_
    · rw [Module.Basis.prod_apply_inl_fst, Module.Basis.singleton_apply]
    · rw [Module.Basis.prod_apply_inl_snd]
  have hb2 : ∀ i, b (Sum.inr i) = ((0 : ℝ), Pi.single i (1 : ℝ)) := fun i ↦ by
    refine Prod.ext ?_ ?_
    · rw [Module.Basis.prod_apply_inr_fst]
    · rw [Module.Basis.prod_apply_inr_snd, Pi.basisFun_apply]
  have hr1 : ∀ x i, b.repr x (Sum.inl i) = x.1 := fun x i ↦ by
    rw [Module.Basis.prod_repr_inl, Module.Basis.singleton_repr]
  have hr2 : ∀ x i, b.repr x (Sum.inr i) = x.2 i := fun x i ↦ by
    rw [Module.Basis.prod_repr_inr, Pi.basisFun_repr]
  rw [← LinearMap.charpoly_toMatrix _ b, ← LinearMap.charpoly_toMatrix _ (Pi.basisFun ℝ (Fin 3))]
  have hM : LinearMap.toMatrix b b (fderiv ℝ e chartPtOut : _ →ₗ[ℝ] _) =
      Matrix.fromBlocks (Matrix.of fun _ _ ↦ rScale) 0
        (Matrix.of fun i _ ↦ w₀ i)
        (LinearMap.toMatrix (Pi.basisFun ℝ (Fin 3)) (Pi.basisFun ℝ (Fin 3))
          (fderiv ℝ fullerChartMap xTildeOut : _ →ₗ[ℝ] _)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [LinearMap.toMatrix_apply, ContinuousLinearMap.coe_coe, hb1, hb2, hr1, hr2,
        hD, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.of_apply,
        Matrix.zero_apply, Pi.basisFun_apply, Pi.basisFun_repr] <;> simp
  rw [hM, Matrix.charpoly_fromBlocks_zero₁₂]
  congr 1
  simp [Matrix.charpoly, Matrix.det_unique, Matrix.charmatrix_apply_eq]

/-- The eigenvalues of `DF(0, x̃_out)`: `r_scale` and those of the Fuller–Poincaré map. -/
private lemma l6j_roots {e : OpenPartialHomeomorph (ℝ × (Fin 3 → ℝ)) (ℝ × (Fin 3 → ℝ))}
    (he : IsReinhardtPoincareExtension e) (μ : ℂ) (hμ : Polynomial.aeval μ (LinearMap.charpoly
      (fderiv ℝ e chartPtOut : (ℝ × (Fin 3 → ℝ)) →ₗ[ℝ] (ℝ × (Fin 3 → ℝ)))) = 0) :
    μ = rScale ∨ ‖μ‖ < 1 / 10 := by
  rw [l6j_charpoly he, map_mul, mul_eq_zero] at hμ
  rcases hμ with h | h
  · left
    simpa [sub_eq_zero] using h
  · exact Or.inr (l6j_DF_spec μ h)

private lemma l6j_isHyperbolic {e : OpenPartialHomeomorph (ℝ × (Fin 3 → ℝ)) (ℝ × (Fin 3 → ℝ))}
    (he : IsReinhardtPoincareExtension e) : (fderiv ℝ e chartPtOut).IsHyperbolic := by
  intro μ hμ
  rcases l6j_roots he μ hμ with h | h
  · rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [rScale_spec.1])]
    exact (rScale_spec.1).ne'
  · intro h1
    rw [h1] at h
    norm_num at h


/-! ### Near the fixed point `e` moves points away from the divisor -/

/-- On a ball around the fixed point, `F₁(r, x̃) ≥ r` for `r ≥ 0` and `F₁(r, x̃) ≤ r` for `r ≤ 0`
(TeX 11915–11916, "Moving away from the exceptional divisor in the radial direction, the
Reinhardt–Poincaré map has scaling factor `r_scale`"): `∂_r F₁ > 1` near the fixed point
(`∂_r F₁ = r_scale` there) and `F₁(0, x̃) = 0`, so `t ↦ F₁(t, x̃) - t` is monotone (mean value
theorem). -/
private lemma l6j_expand {e : OpenPartialHomeomorph (ℝ × (Fin 3 → ℝ)) (ℝ × (Fin 3 → ℝ))}
    (he : IsReinhardtPoincareExtension e) :
    ∃ ρ > 0, Metric.ball chartPtOut ρ ⊆ e.source ∧ ∀ q ∈ Metric.ball chartPtOut ρ,
      (0 ≤ q.1 → q.1 ≤ (e q).1) ∧ (q.1 ≤ 0 → (e q).1 ≤ q.1) := by
  have hval := (hasStrictFDerivAt_extension he).2.1
  obtain ⟨hp, -, han, -, -, hful⟩ := he
  have hcont : ContinuousAt (fun q ↦ (fderiv ℝ e q ((1 : ℝ), (0 : Fin 3 → ℝ))).1) chartPtOut :=
    continuous_fst.continuousAt.comp ((han _ hp).fderiv.continuousAt.clm_apply continuousAt_const)
  have hev : ∀ᶠ q in 𝓝 chartPtOut,
      1 < (fderiv ℝ e q ((1 : ℝ), (0 : Fin 3 → ℝ))).1 ∧ q ∈ e.source := by
    refine (continuousAt_const.eventually_lt hcont ?_).and (e.open_source.mem_nhds hp)
    rw [hval]
    exact rScale_spec.1
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  refine ⟨ρ, hρ, fun q hq ↦ (hball q hq).2, fun q hq ↦ ?_⟩
  have hmem : ∀ t ∈ Metric.ball (0 : ℝ) ρ, (t, q.2) ∈ Metric.ball chartPtOut ρ := by
    intro t ht
    rw [chartPtOut, ← ball_prod_same] at hq ⊢
    exact ⟨ht, hq.2⟩
  have hq1 : q.1 ∈ Metric.ball (0 : ℝ) ρ := by
    rw [chartPtOut, ← ball_prod_same] at hq
    exact hq.1
  -- `ψ(t) = F₁(t, x̃) - t` is monotone on `(-ρ, ρ)`
  set ψ : ℝ → ℝ := fun t ↦ (e (t, q.2)).1 - t with hψ
  have hd : ∀ t ∈ Metric.ball (0 : ℝ) ρ,
      HasDerivAt ψ ((fderiv ℝ e (t, q.2) ((1 : ℝ), (0 : Fin 3 → ℝ))).1 - 1) t := by
    intro t ht
    have hs := (hball _ (hmem t ht)).2
    have hD : HasFDerivAt e (fderiv ℝ e (t, q.2)) (t, q.2) :=
      (han _ hs).differentiableAt.hasFDerivAt
    have hpath : HasDerivAt (fun r : ℝ ↦ (r, q.2)) ((1 : ℝ), (0 : Fin 3 → ℝ)) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t q.2)
    exact (hD.fst.comp_hasDerivAt t hpath).sub (hasDerivAt_id t)
  have hmono : MonotoneOn ψ (Metric.ball (0 : ℝ) ρ) := by
    refine monotoneOn_of_deriv_nonneg (convex_ball 0 ρ) ?_ ?_ ?_
    · exact fun t ht ↦ (hd t ht).continuousAt.continuousWithinAt
    · rw [Metric.isOpen_ball.interior_eq]
      exact fun t ht ↦ (hd t ht).differentiableAt.differentiableWithinAt
    · rw [Metric.isOpen_ball.interior_eq]
      intro t ht
      rw [(hd t ht).deriv]
      linarith [(hball _ (hmem t ht)).1]
  have h0 : ψ 0 = 0 := by
    have hs := (hball _ (hmem 0 (Metric.mem_ball_self hρ))).2
    simp only [hψ, hful _ hs rfl, sub_zero]
  have hq' : (q.1, q.2) = q := rfl
  constructor
  · intro h
    have := hmono (Metric.mem_ball_self hρ) hq1 h
    rw [h0] at this
    simp only [hψ, hq'] at this
    linarith
  · intro h
    have := hmono hq1 (Metric.mem_ball_self hρ) h
    rw [h0] at this
    simp only [hψ, hq'] at this
    linarith


/-! ### A forward invariant attracting neighborhood for the Fuller–Poincaré map -/

/-- An asymptotically stable fixed point of a map continuous near it has arbitrarily small open
forward invariant neighborhoods attracted to it: the points whose orbit stays in a small open set
`W₀` until it enters the interior of a Lyapunov neighborhood. -/
private lemma l6j_exists_invariant {X : Type*} [TopologicalSpace X] {f : X → X} {x₀ : X}
    (hf : Function.IsAsymptoticallyStable f x₀) {O : Set X} (hO : IsOpen O) (hx₀ : x₀ ∈ O)
    (hfc : ContinuousOn f O) {W : Set X} (hW : W ∈ 𝓝 x₀) :
    ∃ N, IsOpen N ∧ x₀ ∈ N ∧ N ⊆ W ∧ MapsTo f N N ∧
      ∀ x ∈ N, Tendsto (fun n ↦ f^[n] x) atTop (𝓝 x₀) := by
  obtain ⟨-, hL, Va, hVa, hatt⟩ := hf
  obtain ⟨W₀, hW₀s, hW₀o, hx₀W₀⟩ :=
    mem_nhds_iff.1 (inter_mem (inter_mem hW hVa) (hO.mem_nhds hx₀))
  obtain ⟨V, hV, hVorb⟩ := hL W₀ (hW₀o.mem_nhds hx₀W₀)
  have hfc' : ContinuousOn f W₀ := hfc.mono fun x hx ↦ (hW₀s hx).2
  let T : ℕ → Set X → Set X := fun m O' ↦ {x | f^[m] x ∈ O' ∧ ∀ k ≤ m, f^[k] x ∈ W₀}
  have hT : ∀ m O', IsOpen O' → IsOpen (T m O') := by
    intro m
    induction m with
    | zero =>
      intro O' hO'
      have : T 0 O' = O' ∩ W₀ := by
        ext x
        simp only [T, mem_ofPred_eq, mem_inter_iff, Nat.le_zero, forall_eq,
          Function.iterate_zero, id_eq]
      rw [this]
      exact hO'.inter hW₀o
    | succ m ih =>
      intro O' hO'
      have : T (m + 1) O' = W₀ ∩ f ⁻¹' (T m O') := by
        ext x
        simp only [T, mem_ofPred_eq, mem_inter_iff, mem_preimage, Function.iterate_succ_apply]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h2 0 (Nat.zero_le _), h1, fun k hk ↦ by
            simpa [Function.iterate_succ_apply] using h2 (k + 1) (by omega)⟩
        · rintro ⟨h0, h1, h2⟩
          refine ⟨h1, fun k hk ↦ ?_⟩
          cases k with
          | zero => exact h0
          | succ k => simpa [Function.iterate_succ_apply] using h2 k (by omega)
      rw [this]
      exact hfc'.isOpen_inter_preimage hW₀o (ih O' hO')
  have horb : ∀ m x, x ∈ T m (interior V) → ∀ k, f^[k] x ∈ W₀ := by
    intro m x ⟨h1, h2⟩ k
    by_cases hk : k ≤ m
    · exact h2 k hk
    · have : k = (k - m) + m := by omega
      rw [this, Function.iterate_add_apply]
      exact hVorb _ (interior_subset h1) _
  refine ⟨⋃ m, T m (interior V), isOpen_iUnion fun m ↦ hT m _ isOpen_interior,
    mem_iUnion.2 ⟨0, mem_interior_iff_mem_nhds.2 hV, fun k hk ↦ by
      rw [Nat.le_zero.1 hk]; exact hx₀W₀⟩, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨m, hm⟩ := mem_iUnion.1 hx
    exact (hW₀s (horb m x hm 0)).1.1
  · intro x hx
    obtain ⟨m, hm⟩ := mem_iUnion.1 hx
    have ht := hatt x (hW₀s (horb m x hm 0)).1.2
    obtain ⟨n₀, hn₀⟩ := (ht.eventually (interior_mem_nhds.2 hV)).exists_forall_of_atTop
    refine mem_iUnion.2 ⟨n₀, ?_, fun k _ ↦ ?_⟩
    · rw [← Function.iterate_succ_apply]
      exact hn₀ _ (Nat.le_succ n₀)
    · rw [← Function.iterate_succ_apply]
      exact horb m x hm _
  · intro x hx
    obtain ⟨m, hm⟩ := mem_iUnion.1 hx
    exact hatt x (hW₀s (horb m x hm 0)).1.2

/-- **Linearized stability of the Fuller–Poincaré map at `x̃_out`** in the chart
(`hasFDerivAt_fullerChartMap`, `Function.isAsymptoticallyStable_of_hasFDerivAt`): arbitrarily
small open forward invariant neighborhoods of `x̃_out` are attracted to it. -/
private lemma l6j_fuller_invariant {e : OpenPartialHomeomorph (ℝ × (Fin 3 → ℝ)) (ℝ × (Fin 3 → ℝ))}
    (he : IsReinhardtPoincareExtension e) {W : Set (Fin 3 → ℝ)} (hW : W ∈ 𝓝 xTildeOut) :
    ∃ N, IsOpen N ∧ xTildeOut ∈ N ∧ N ⊆ W ∧ MapsTo fullerChartMap N N ∧
      ∀ x ∈ N, Tendsto (fun n ↦ fullerChartMap^[n] x) atTop (𝓝 xTildeOut) := by
  obtain ⟨hp, -, -, -, -, hful⟩ := he
  obtain ⟨D, hD, hspec⟩ := hasFDerivAt_fullerChartMap
  have hst : Function.IsAsymptoticallyStable fullerChartMap xTildeOut :=
    Function.isAsymptoticallyStable_of_hasFDerivAt fullerChartMap_xTildeOut hD
      fun μ hμ ↦ (hspec μ hμ).trans (by norm_num)
  have hc : Continuous fun x : Fin 3 → ℝ ↦ ((0 : ℝ), x) := by fun_prop
  set O := (fun x : Fin 3 → ℝ ↦ ((0 : ℝ), x)) ⁻¹' e.source
  have hO : IsOpen O := e.open_source.preimage hc
  have hfc : ContinuousOn fullerChartMap O := by
    have : ContinuousOn (fun x : Fin 3 → ℝ ↦ (e ((0 : ℝ), x)).2) O :=
      continuous_snd.comp_continuousOn (e.continuousOn.comp hc.continuousOn fun x hx ↦ hx)
    refine this.congr fun x hx ↦ ?_
    simp [hful _ hx rfl]
  exact l6j_exists_invariant hst hO hp hfc hW

/-! ### The stable and unstable subspaces of `DF(0, x̃_out)` -/

/-- The stable subspace lies in the divisor direction `{0} × ℝ³`; the unstable subspace meets it
only in `0` and contains a vector `u` with `u₁ = 1` (so it is the line `ℝ u`). -/
private lemma l6j_subspaces {e : OpenPartialHomeomorph (ℝ × (Fin 3 → ℝ)) (ℝ × (Fin 3 → ℝ))}
    (he : IsReinhardtPoincareExtension e) :
    (∀ x ∈ (fderiv ℝ e chartPtOut).stableSubspace, x.1 = 0) ∧
      (∀ y ∈ (fderiv ℝ e chartPtOut).unstableSubspace, y.1 = 0 → y = 0) ∧
      ∃ u ∈ (fderiv ℝ e chartPtOut).unstableSubspace, u.1 = 1 := by
  obtain ⟨w₀, hD⟩ := l6j_fderiv_apply he
  set A := fderiv ℝ e chartPtOut with hA
  have hr1 : 1 < rScale := rScale_spec.1
  have hpow : ∀ n x, ((A ^ n) x).1 = rScale ^ n * x.1 := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih => intro x; rw [pow_succ', mul_apply_eq_comp, hD, ih, pow_succ']; ring
  have hstab : ∀ x ∈ A.stableSubspace, x.1 = 0 := by
    intro x hx
    have h1 : Tendsto (fun n : ℕ ↦ |rScale ^ n * x.1|) atTop (𝓝 0) := by
      have h := (continuous_abs.tendsto 0).comp ((continuous_fst.tendsto 0).comp hx)
      simpa [Function.comp_def, hpow] using h
    have h2 : |x.1| ≤ 0 := by
      refine ge_of_tendsto' h1 fun n ↦ ?_
      rw [abs_mul, abs_pow, abs_of_pos (by linarith : (0 : ℝ) < rScale)]
      exact le_mul_of_one_le_left (abs_nonneg _) (one_le_pow₀ hr1.le)
    exact abs_nonpos_iff.1 h2
  refine ⟨hstab, ?_, ?_⟩
  · rintro y ⟨w, rfl, hwA, hwt⟩ hy
    have h1 : ∀ n, (w n).1 = 0 := by
      intro n
      induction n with
      | zero => exact hy
      | succ n ih =>
        have := congrArg Prod.fst (hwA n)
        rw [hD, ih] at this
        exact (mul_eq_zero.1 this).resolve_left (by linarith)
    have h2 : ∀ n, (w n).2 = fderiv ℝ fullerChartMap xTildeOut (w (n + 1)).2 := by
      intro n
      have := congrArg Prod.snd (hwA n)
      rw [hD, h1, zero_smul, zero_add] at this
      exact this.symm
    set DF := fderiv ℝ fullerChartMap xTildeOut
    have h3 : ∀ k, (w 0).2 = (DF ^ k) (w k).2 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [ih, h2 k, pow_succ, mul_apply_eq_comp]
    obtain ⟨N, hN0, hN⟩ := DF.exists_norm_pow_lt_one fun μ hμ ↦
      (l6j_DF_spec μ hμ).trans (by norm_num)
    have h4 : ∀ k, ‖(w 0).2‖ ≤ ‖(w (N * (k + 1))).2‖ := by
      intro k
      rw [h3 (N * (k + 1)), pow_mul]
      refine (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_of_le_one_left (norm_nonneg _) ?_)
      exact (norm_pow_le' _ (Nat.succ_pos k)).trans (pow_le_one₀ (norm_nonneg _) hN.le)
    have h5 : Tendsto (fun k : ℕ ↦ ‖(w (N * (k + 1))).2‖) atTop (𝓝 0) := by
      have hk : Tendsto (fun k : ℕ ↦ N * (k + 1)) atTop atTop :=
        (tendsto_add_atTop_nat 1).const_mul_atTop' hN0
      have := (continuous_norm.tendsto _).comp ((continuous_snd.tendsto 0).comp (hwt.comp hk))
      simpa [Function.comp_def] using this
    have h6 : ‖(w 0).2‖ ≤ 0 := ge_of_tendsto' h5 h4
    exact Prod.ext (h1 0) (norm_le_zero_iff.1 h6)
  · have htop : A.stableSubspace ⊔ A.unstableSubspace = ⊤ :=
      (ContinuousLinearMap.isCompl_stableSubspace_unstableSubspace (l6j_isHyperbolic he)).sup_eq_top
    have hmem : ((1 : ℝ), (0 : Fin 3 → ℝ)) ∈ A.stableSubspace ⊔ A.unstableSubspace := by
      rw [htop]; exact Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hmem
    refine ⟨z, hz, ?_⟩
    have := congrArg Prod.fst hyz
    simp only [Prod.fst_add, hstab y hy, zero_add] at this
    exact this


/-! ### The local stable and unstable sets on a box -/

/-- **The local stable and unstable sets of `e` at `(0, x̃_out)`** on a box `U = (-δ, δ) × N` inside
the source and the target: the stable set is the divisor `{r = 0} ∩ U` (the Fuller part contracts
on the forward invariant `N`, the radial part expands), and the unstable set is the graph of a
`C^∞` curve `r ↦ (r, γ(r))` over `(-δ, δ)` (Theorem A.3.1, the unstable summand being the line of
the `r_scale`-eigenvector). -/
private lemma l6j_main {e : OpenPartialHomeomorph (ℝ × (Fin 3 → ℝ)) (ℝ × (Fin 3 → ℝ))}
    (he : IsReinhardtPoincareExtension e) :
    ∃ U ∈ 𝓝 chartPtOut, IsOpen U ∧ U ⊆ e.source ∩ e.target ∧
      Function.localStableSet e chartPtOut U = {p ∈ U | p.1 = 0} ∧
      ∃ δ > 0, ∃ γ : ℝ → (Fin 3 → ℝ), ContDiffOn ℝ ∞ γ (Ioo (-δ) δ) ∧ γ 0 = xTildeOut ∧
        Function.localUnstableSet e chartPtOut U = (fun r ↦ (r, γ r)) '' Ioo (-δ) δ := by
  obtain ⟨hp, hfix, han, hans, -, hful⟩ := id he
  have hpt : chartPtOut ∈ e.target := hfix ▸ e.map_source hp
  have hsp : e.symm chartPtOut = chartPtOut := by simpa [hfix] using e.left_inv hp
  -- Theorem A.3.1 (`e` is analytic, hence `C^∞`)
  have hC : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) e e.source :=
    han.contDiffOn e.open_source.uniqueDiffOn
  have hC' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) e.symm e.target :=
    hans.contDiffOn e.open_target.uniqueDiffOn
  obtain ⟨U₀, hU₀, -, hU₀s, -, Vu, hVu, hu, huC, hu0, -, huU⟩ :=
    theoremA_3_1 e hp hfix le_top hC hC' (l6j_isHyperbolic he)
  obtain ⟨hstab, hinj, u, huE, hu1⟩ := l6j_subspaces he
  set u' : (fderiv ℝ e chartPtOut).unstableSubspace := ⟨u, huE⟩ with hu'
  set g : (fderiv ℝ e chartPtOut).unstableSubspace → ℝ × (Fin 3 → ℝ) :=
    fun y ↦ chartPtOut + ↑y + ↑(hu y) with hg
  set γ : ℝ → (Fin 3 → ℝ) := fun r ↦ (g (r • u')).2 with hγ
  -- every point of the unstable graph is `(r, γ r)`
  have hgy : ∀ y : (fderiv ℝ e chartPtOut).unstableSubspace,
      g y = ((y : ℝ × (Fin 3 → ℝ)).1, γ (y : ℝ × (Fin 3 → ℝ)).1) := by
    intro y
    have hy : y = (y : ℝ × (Fin 3 → ℝ)).1 • u' := by
      apply Subtype.ext
      have h := hinj ((y : ℝ × (Fin 3 → ℝ)) - (y : ℝ × (Fin 3 → ℝ)).1 • u)
        (Submodule.sub_mem _ y.2 (Submodule.smul_mem _ _ huE)) (by simp [hu1])
      rw [sub_eq_zero] at h
      simpa [hu'] using h
    refine Prod.ext ?_ ?_
    · simp [hg, hstab _ (hu y).2, chartPtOut]
    · simp only [hγ]
      conv_lhs => rw [hy]
  have hgr : ∀ r : ℝ, g (r • u') = (r, γ r) := by
    intro r
    rw [hgy]
    simp [hu', hu1]
  -- the expansion ball
  obtain ⟨ρ₀, hρ₀, -, hB₀⟩ := l6j_expand he
  have habs : ∀ q ∈ Metric.ball chartPtOut ρ₀, |q.1| ≤ |(e q).1| := by
    intro q hq
    rcases le_total 0 q.1 with h | h
    · have := (hB₀ q hq).1 h
      rw [abs_of_nonneg h, abs_of_nonneg (h.trans this)]
      exact this
    · have := (hB₀ q hq).2 h
      rw [abs_of_nonpos h, abs_of_nonpos (this.trans h)]
      linarith
  -- a ball where everything happens
  have hW : Metric.ball chartPtOut ρ₀ ∩ U₀ ∩ e.target ∩
      e.symm ⁻¹' Metric.ball chartPtOut ρ₀ ∈ 𝓝 chartPtOut := by
    refine inter_mem (inter_mem (inter_mem (Metric.ball_mem_nhds _ hρ₀) hU₀)
      (e.open_target.mem_nhds hpt)) ?_
    exact (e.continuousAt_symm hpt).preimage_mem_nhds
      (by rw [hsp]; exact Metric.ball_mem_nhds _ hρ₀)
  obtain ⟨ρ₁, hρ₁, hρ₁W⟩ := Metric.mem_nhds_iff.1 hW
  -- the forward invariant neighborhood of `x̃_out` for the Fuller map
  obtain ⟨N, hNo, hN0, hNs, hNmaps, hNatt⟩ :=
    l6j_fuller_invariant he (Metric.ball_mem_nhds xTildeOut hρ₁)
  -- the radius `δ`: the curve stays in `V_u` and in `N`
  have hsmul : Continuous fun r : ℝ ↦ r • u' := continuous_id.smul continuous_const
  have hgc : ContinuousAt g 0 := by
    have : ContinuousAt hu 0 := huC.continuousOn.continuousAt hVu
    exact (continuous_const.add continuous_subtype_val).continuousAt.add
      (continuous_subtype_val.continuousAt.comp this)
  have hγc : ContinuousAt γ 0 :=
    continuous_snd.continuousAt.comp (hgc.comp_of_eq hsmul.continuousAt (zero_smul ℝ u'))
  have hγ0 : γ 0 = xTildeOut := by
    simp only [hγ, hg]
    rw [zero_smul, hu0]
    simp [chartPtOut]
  have hev : ∀ᶠ r in 𝓝 (0 : ℝ), r • u' ∈ Vu ∧ γ r ∈ N := by
    refine Filter.Eventually.and (hsmul.continuousAt.preimage_mem_nhds (x := 0) ?_) ?_
    · rw [zero_smul]; exact hVu
    · exact hγc.preimage_mem_nhds (by rw [hγ0]; exact hNo.mem_nhds hN0)
  obtain ⟨δ', hδ', hδ'ev⟩ := Metric.eventually_nhds_iff_ball.1 hev
  set δ := min δ' ρ₁ with hδ
  have hδ0 : 0 < δ := lt_min hδ' hρ₁
  have hIoo : ∀ r ∈ Ioo (-δ) δ, r • u' ∈ Vu ∧ γ r ∈ N := by
    intro r hr
    refine hδ'ev r ?_
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact ⟨by linarith [hr.1, min_le_left δ' ρ₁], by linarith [hr.2, min_le_left δ' ρ₁]⟩
  -- the box
  set U := Ioo (-δ) δ ×ˢ N with hU
  have hUo : IsOpen U := isOpen_Ioo.prod hNo
  have hp0U : chartPtOut ∈ U := ⟨⟨by simp [chartPtOut]; linarith, by simpa [chartPtOut] using hδ0⟩,
    hN0⟩
  have hUW : U ⊆ Metric.ball chartPtOut ρ₁ := by
    rintro q ⟨hq1, hq2⟩
    rw [chartPtOut, ← ball_prod_same]
    refine ⟨?_, hNs hq2⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact ⟨by linarith [hq1.1, min_le_right δ' ρ₁], by linarith [hq1.2, min_le_right δ' ρ₁]⟩
  have hUB : U ⊆ Metric.ball chartPtOut ρ₀ := fun q hq ↦ (hρ₁W (hUW hq)).1.1.1
  have hUU₀ : U ⊆ U₀ := fun q hq ↦ (hρ₁W (hUW hq)).1.1.2
  have hUt : U ⊆ e.target := fun q hq ↦ (hρ₁W (hUW hq)).1.2
  have hUsymm : ∀ q ∈ U, e.symm q ∈ Metric.ball chartPtOut ρ₀ := fun q hq ↦ (hρ₁W (hUW hq)).2
  refine ⟨U, hUo.mem_nhds hp0U, hUo, fun q hq ↦ ⟨hU₀s (hUU₀ hq), hUt hq⟩, ?_, δ, hδ0, γ, ?_, hγ0,
    ?_⟩
  · -- the local stable set is the divisor
    ext x
    constructor
    · rintro ⟨hxU, hxt⟩
      refine ⟨by simpa using hxU 0, ?_⟩
      have hmono : ∀ n, |x.1| ≤ |(e^[n] x).1| := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          rw [Function.iterate_succ_apply']
          exact ih.trans (habs _ (hUB (hxU n)))
      have ht : Tendsto (fun n ↦ |(e^[n] x).1|) atTop (𝓝 0) := by
        have := (continuous_abs.tendsto _).comp ((continuous_fst.tendsto _).comp hxt)
        simpa [Function.comp_def, chartPtOut] using this
      exact abs_nonpos_iff.1 (ge_of_tendsto' ht hmono)
    · rintro ⟨hxU, hx1⟩
      have hx : x = ((0 : ℝ), x.2) := Prod.ext hx1 rfl
      have hit : ∀ n, e^[n] x = ((0 : ℝ), fullerChartMap^[n] x.2) := by
        intro n
        induction n with
        | zero => exact hx
        | succ n ih =>
          rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
          refine hful _ (hU₀s (hUU₀ ⟨⟨by linarith, hδ0⟩, hNmaps.iterate n hxU.2⟩)) rfl
      refine ⟨fun n ↦ ?_, ?_⟩
      · rw [hit]
        exact ⟨⟨by linarith, hδ0⟩, hNmaps.iterate n hxU.2⟩
      · simp only [hit]
        exact tendsto_const_nhds.prodMk_nhds (hNatt _ hxU.2)
  · -- the curve is `C^∞`
    have hgC : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g Vu :=
      (contDiffOn_const.add (Submodule.subtypeL _).contDiff.contDiffOn).add
        ((Submodule.subtypeL _).contDiff.comp_contDiffOn huC)
    exact contDiff_snd.comp_contDiffOn
      (hgC.comp (contDiff_id.smul contDiff_const).contDiffOn fun r hr ↦ (hIoo r hr).1)
  · -- the local unstable set is the curve
    ext x
    constructor
    · intro hx
      have hx₀ : x ∈ Function.localUnstableSet e chartPtOut U₀ := by
        obtain ⟨y, hy0, hy, hyt⟩ := hx
        exact ⟨y, hy0, fun n ↦ ⟨hUU₀ (hy n).1, (hy n).2⟩, hyt⟩
      rw [huU] at hx₀
      obtain ⟨z, -, rfl⟩ := hx₀
      have hzU := Function.mem_of_mem_localUnstableSet hx
      change g z ∈ U at hzU
      rw [hgy] at hzU ⊢
      exact ⟨_, hzU.1, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      have hx₀ : (r, γ r) ∈ Function.localUnstableSet e chartPtOut U₀ := by
        rw [huU, ← hgr]
        exact ⟨_, (hIoo r hr).1, rfl⟩
      obtain ⟨y, hy0, hy, hyt⟩ := hx₀
      have hyU : ∀ n, y n ∈ U := by
        intro n
        induction n with
        | zero => rw [hy0]; exact ⟨hr, (hIoo r hr).2⟩
        | succ n ih =>
          have hsrc : y (n + 1) ∈ e.source := hU₀s (hy (n + 1)).1
          have hyy : e.symm (y n) = y (n + 1) := by rw [← (hy n).2, e.left_inv hsrc]
          have hB : y (n + 1) ∈ Metric.ball chartPtOut ρ₀ := hyy ▸ hUsymm _ ih
          have h1 : |(y (n + 1)).1| ≤ |(y n).1| := by
            have := habs _ hB
            rwa [(hy n).2] at this
          have h1' : (y (n + 1)).1 ∈ Ioo (-δ) δ := by
            have := ih.1
            rw [mem_Ioo, ← abs_lt] at this ⊢
            exact h1.trans_lt this
          -- `y (n + 1)` lies on the curve
          have htail : y (n + 1) ∈ Function.localUnstableSet e chartPtOut U₀ := by
            refine ⟨fun k ↦ y (k + (n + 1)), by simp, fun k ↦ ⟨(hy _).1, ?_⟩,
              hyt.comp (tendsto_add_atTop_nat (n + 1))⟩
            have := (hy (k + (n + 1))).2
            rwa [show k + (n + 1) + 1 = k + 1 + (n + 1) by ring] at this
          rw [huU] at htail
          obtain ⟨z, -, hz⟩ := htail
          rw [hgy] at hz
          rw [← hz] at h1' ⊢
          exact ⟨h1', (hIoo _ h1').2⟩
      exact ⟨y, hy0, fun n ↦ ⟨hyU n, (hy n).2⟩, hyt⟩

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
  have hr1 : 1 < rScale := rScale_spec.1
  refine ⟨l6j_isHyperbolic he, l6j_charpoly he, ?_, ?_, l6j_roots he, ?_⟩
  · -- `r_scale` is a simple root: it is not a root of the Fuller factor
    have hnot : ¬ (LinearMap.charpoly (fderiv ℝ fullerChartMap xTildeOut :
        (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ))).IsRoot rScale := by
      intro h
      have h' := l6j_DF_spec rScale (by
        rw [← Complex.coe_algebraMap, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval,
          h.eq_zero, map_zero])
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at h'
      linarith
    have hne : (Polynomial.X - Polynomial.C rScale) * LinearMap.charpoly
        (fderiv ℝ fullerChartMap xTildeOut : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) ≠ 0 :=
      mul_ne_zero (Polynomial.X_sub_C_ne_zero _) (LinearMap.charpoly_monic _).ne_zero
    rw [l6j_charpoly he, Polynomial.rootMultiplicity_mul hne,
      Polynomial.rootMultiplicity_X_sub_C_self, Polynomial.rootMultiplicity_eq_zero hnot]
  · rw [l6j_charpoly he]
    simp
  · obtain ⟨U, hU, hUo, hUs, hst, hun⟩ := l6j_main he
    exact ⟨U, hU, hUo, fun q hq ↦ (hUs hq).1, hst, hun⟩


/-! ### The vertex flows: uniqueness, the flow property, the rotation, the time reversal -/

/-- A curve solving the state–costate equations with the control `e_m` (`λ_cost = -1`, with
`P = Z_{e_m}/⟨Z_{e_m}, X(0)⟩` in the state equation) is the vertex flow from its value at `0`
(Grönwall, forward and backward in time, as in `iso_vertexFlow_qFix`). -/
private lemma l6j_eq_vertexFlow (m : Fin 3) (Y : ℝ → iso_PhasePt)
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
private lemma l6j_vertexFlow_add (m : Fin 3) (q : iso_PhasePt) (a t : ℝ) :
    iso_vertexFlow m q (a + t) = iso_vertexFlow m (iso_vertexFlow m q a) t := by
  have hsh : ∀ s, HasDerivAt (fun s : ℝ ↦ a + s) 1 s := fun s ↦ (hasDerivAt_id' s).const_add a
  have h := l6j_eq_vertexFlow m (fun s ↦ iso_vertexFlow m q (a + s)) (fun s ↦ ?_) (fun s ↦ ?_)
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
private lemma l6j_adRinv_vertexFlow (m : Fin 3) (q : iso_PhasePt) (t : ℝ) :
    iso_adRinvPow 1 (iso_vertexFlow m q t) = iso_vertexFlow (m + 1) (iso_adRinvPow 1 q) t := by
  have hC : R ^ 1 * R⁻¹ ^ 1 = 1 := poly_Rpow_mul_Rinvpow 1
  have hZ : R⁻¹ ^ 1 * controlMatrix (vertex m) * R ^ 1 = controlMatrix (vertex (m + 1)) := by
    simpa only [pow_one] using poly_Rinv_conj_vertex m
  have hJ : R⁻¹ ^ 1 * J * R ^ 1 = J := poly_conj_pow_J 1
  have hY0 : iso_adRinvPow 1 (iso_vertexFlow m q 0) = iso_adRinvPow 1 q := by
    rw [ivf_vertexFlow_zero]
  have h := l6j_eq_vertexFlow (m + 1) (fun s ↦ iso_adRinvPow 1 (iso_vertexFlow m q s))
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
private lemma l6j_phaseHam_adRinv (q : iso_PhasePt) (m : Fin 3) :
    phaseHam (iso_adRinvPow 1 q) (vertex (m + 1)) = phaseHam q (vertex m) := by
  have hC : R ^ 1 * R⁻¹ ^ 1 = 1 := poly_Rpow_mul_Rinvpow 1
  have hZ : R⁻¹ ^ 1 * controlMatrix (vertex m) * R ^ 1 = controlMatrix (vertex (m + 1)) := by
    simpa only [pow_one] using poly_Rinv_conj_vertex m
  exact poly_hamiltonian_conj hC (poly_conj_pow_J 1) hZ (-1) _ _ _

/-- The Hamiltonians at the time reversal of a rotated point: `e₂` is fixed and `e₁ ↔ e₃`
(`τ` exchanges `e₂, e₃`, `Ad_{R⁻¹}` shifts the indices). -/
private lemma l6j_phaseHam_mirror (y : iso_PhasePt) :
    phaseHam (reinTau (iso_adRinvPow 1 y)) (vertex 0) = phaseHam y (vertex 2) ∧
      phaseHam (reinTau (iso_adRinvPow 1 y)) (vertex 1) = phaseHam y (vertex 1) ∧
      phaseHam (reinTau (iso_adRinvPow 1 y)) (vertex 2) = phaseHam y (vertex 0) := by
  have h := fun j ↦ (switchingFn_reinTau j 0 (iso_adRinvPow 1 y)).2
  refine ⟨?_, ?_, ?_⟩
  · have := l6j_phaseHam_adRinv y 2
    rw [show (2 : Fin 3) + 1 = 0 from rfl] at this
    exact (h 0).trans this
  · have := l6j_phaseHam_adRinv y 1
    rw [show (1 : Fin 3) + 1 = 2 from rfl] at this
    exact (h 1).trans this
  · have := l6j_phaseHam_adRinv y 0
    rw [show (0 : Fin 3) + 1 = 1 from rfl] at this
    exact (h 2).trans this


/-! ### The χ₂₃ check before the wall, the chart domain, the inverse derivative -/

open Asymptotics in
/-- **`χ₂₃ < 0` just before the wall** (the χ₂₃ check of G14.5 at negative times): near the fixed
point, `χ̃₂₃(s, r, x̃) < 0` for small `s < 0`. At `(0, x̃_out)` it is `s Q(s)` with `Q(0) > 0`
(`l6d_v23_xTildeOut`), and `χ̃₂₃(0, r, x̃) = 0` near the fixed point (`l6d_eventually_chi23_zero`),
so `χ̃₂₃ = s H` with `H` analytic and `H(0, 0, x̃_out) = Q(0) > 0` (division by `s`, as in
`l6d_eventually_chi23_pos`). -/
private lemma l6j_chi23_neg : ∃ ε > 0, ∀ᶠ q in 𝓝 chartPtOut, ∀ s, -ε < s → s < 0 →
    l6d_chi23 (s, q.1, q.2) < 0 := by
  set p₀ : ℝ × (Fin 3 → ℝ) := ((0 : ℝ), xTildeOut) with hp₀
  have han : AnalyticAt ℝ l6d_chi23 ((0 : ℝ), p₀) := l6d_analyticAt_chi23 0 xTildeOut
  have hk : ∀ᶠ y in 𝓝 p₀, (fun s : ℝ ↦ l6d_chi23 (s, y)) =O[𝓝 0] (fun s ↦ s ^ 1) := by
    have hev : ∀ᶠ y in 𝓝 p₀, AnalyticAt ℝ l6d_chi23 ((0 : ℝ), y) := by
      have := han.eventually_analyticAt
      exact (by fun_prop : ContinuousAt (fun y : ℝ × (Fin 3 → ℝ) ↦ ((0 : ℝ), y)) p₀).eventually
        this
    filter_upwards [hev, l6d_eventually_chi23_zero] with y hy hy0
    have hd : HasDerivAt (fun s : ℝ ↦ l6d_chi23 (s, y)) _ 0 :=
      (hy.comp_of_eq (by fun_prop : AnalyticAt ℝ (fun s : ℝ ↦ (s, y)) 0) rfl
        ).differentiableAt.hasDerivAt
    have := hd.isBigO_sub
    simp only [sub_zero] at this
    have hy0' : l6d_chi23 (0, y) = 0 := hy0
    simpa [hy0'] using this
  obtain ⟨H, hH, hHeq⟩ := AnalyticAt.exists_eq_pow_smul_of_isBigO han hk
  have hH0 : 0 < H ((0 : ℝ), p₀) := by
    have hcont : ContinuousAt (fun s : ℝ ↦ H (s, p₀)) 0 :=
      hH.continuousAt.comp_of_eq (by fun_prop : ContinuousAt (fun s : ℝ ↦ (s, p₀)) 0) rfl
    have hev : ∀ᶠ s in 𝓝[≠] (0 : ℝ), H (s, p₀) = l6d_Q s := by
      have h1 : ∀ᶠ s in 𝓝 (0 : ℝ), l6d_chi23 (s, p₀) = s ^ 1 • H (s, p₀) :=
        (by fun_prop : ContinuousAt (fun s : ℝ ↦ (s, p₀)) 0).eventually hHeq
      filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with s hs hs0
      rw [hp₀, l6d_chi23_zero, l6d_v23_xTildeOut, pow_one, smul_eq_mul] at hs
      exact (mul_left_cancel₀ hs0 hs).symm
    have hQc : ContinuousAt l6d_Q 0 := by unfold l6d_Q; fun_prop
    have hlim := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ))
    have hlim2 := (hQc.tendsto.mono_left (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ))).congr'
      (hev.mono fun s h ↦ h.symm)
    rw [tendsto_nhds_unique hlim hlim2]
    exact l6d_Q_pos le_rfl
  have hnear : ∀ᶠ v in 𝓝 ((0 : ℝ), p₀), l6d_chi23 v = v.1 * H v ∧ 0 < H v := by
    filter_upwards [hHeq, continuousAt_const.eventually_lt hH.continuousAt hH0] with v h1 h2
    exact ⟨by simpa using h1, h2⟩
  rw [nhds_prod_eq] at hnear
  obtain ⟨pa, hpa, pb, hpb, hall⟩ := Filter.eventually_prod_iff.1 hnear
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff.1 hpa
  refine ⟨ε, hε, ?_⟩
  filter_upwards [hpb] with q hq s hs1 hs2
  have hs : pa s := hεb (by rw [Real.dist_eq, sub_zero, abs_lt]; constructor <;> linarith)
  obtain ⟨h1, h2⟩ := hall hs hq
  rw [h1]
  exact mul_neg_of_neg_of_pos hs2 h2

/-- Chart points with small `r > 0` near `x̃_out` lie in `H*`. -/
private lemma l6j_eventually_mem_lieChartDomain :
    ∀ᶠ q in 𝓝 chartPtOut, 0 < q.1 → q ∈ lieChartDomain := by
  set c := |√3 - xTildeOut 0| + 2 with hc
  have hc0 : 0 < c := by positivity
  have hr : ∀ᶠ q in 𝓝 chartPtOut, q.1 < 1 / c :=
    (by fun_prop : ContinuousAt (fun q : ℝ × (Fin 3 → ℝ) ↦ q.1) chartPtOut).eventually_lt
      continuousAt_const (by simp only [chartPtOut]; positivity)
  have h0 : ∀ᶠ q in 𝓝 chartPtOut, xTildeOut 0 - 1 < q.2 0 :=
    continuousAt_const.eventually_lt
      (by fun_prop : ContinuousAt (fun q : ℝ × (Fin 3 → ℝ) ↦ q.2 0) chartPtOut)
      (by simp [chartPtOut])
  have h2 : ∀ᶠ q in 𝓝 chartPtOut, q.2 2 * q.1 ^ 2 < 3 / 2 :=
    (by fun_prop : ContinuousAt (fun q : ℝ × (Fin 3 → ℝ) ↦ q.2 2 * q.1 ^ 2)
      chartPtOut).eventually_lt continuousAt_const (by simp [chartPtOut])
  filter_upwards [hr, h0, h2] with q hq1 hq0 hq2 hpos
  refine ⟨hpos, ?_, hq2⟩
  have h1 : c < 1 / q.1 := (lt_one_div hc0 hpos).2 hq1
  have := le_abs_self (√3 - xTildeOut 0)
  linarith

/-- If `A B = B A = 1`, the eigenvalues of `B` are the inverses of those of `A`. -/
private lemma l6j_aeval_charpoly_inv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {A B : E →L[ℝ] E} (hAB : A.comp B = ContinuousLinearMap.id ℝ E)
    (hBA : B.comp A = ContinuousLinearMap.id ℝ E) {μ : ℂ}
    (hμ : Polynomial.aeval μ (LinearMap.charpoly (B : E →ₗ[ℝ] E)) = 0) :
    μ ≠ 0 ∧ Polynomial.aeval μ⁻¹ (LinearMap.charpoly (A : E →ₗ[ℝ] E)) = 0 := by
  classical
  let b := Module.finBasis ℝ E
  let φ : (E →L[ℝ] E) → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℂ :=
    fun C ↦ (LinearMap.toMatrix b b (C : E →ₗ[ℝ] E)).map (algebraMap ℝ ℂ)
  have hroot : ∀ (C : E →L[ℝ] E) (ν : ℂ),
      Polynomial.aeval ν (LinearMap.charpoly (C : E →ₗ[ℝ] E)) = 0 ↔ ν ∈ spectrum ℂ (φ C) := by
    intro C ν
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot.def, Matrix.charpoly_map,
      LinearMap.charpoly_toMatrix, Polynomial.eval_map_algebraMap]
  have hmul : ∀ C D : E →L[ℝ] E, φ (C.comp D) = φ C * φ D := by
    intro C D
    change ((LinearMap.toMatrix b b) ((C : E →ₗ[ℝ] E) ∘ₗ (D : E →ₗ[ℝ] E))).map _ = _
    rw [LinearMap.toMatrix_comp b b b, Matrix.map_mul]
  have hid : φ (ContinuousLinearMap.id ℝ E) = 1 := by
    simp [φ]
  let u : (Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℂ)ˣ :=
    ⟨φ A, φ B, by rw [← hmul, hAB, hid], by rw [← hmul, hBA, hid]⟩
  have hμB : μ ∈ spectrum ℂ (φ B) := (hroot B μ).1 hμ
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    exact (spectrum.zero_mem_iff ℂ).1 hμB ⟨u⁻¹, rfl⟩
  refine ⟨hμ0, (hroot A μ⁻¹).2 ?_⟩
  have hval : ((Units.mk0 μ⁻¹ (inv_ne_zero hμ0))⁻¹ : ℂˣ).val = μ := by simp
  have := (spectrum.inv_mem_iff (r := Units.mk0 μ⁻¹ (inv_ne_zero hμ0)) (a := u)).2 (by
    rw [hval]; exact hμB)
  exact this

/-- The derivative of `e⁻¹` at the fixed point is the inverse of `DF(0, x̃_out)`, and it is
hyperbolic (its eigenvalues are `1/r_scale` and the inverses of those of the Fuller map). -/
private lemma l6j_isHyperbolic_symm
    {e : OpenPartialHomeomorph (ℝ × (Fin 3 → ℝ)) (ℝ × (Fin 3 → ℝ))}
    (he : IsReinhardtPoincareExtension e) : (fderiv ℝ e.symm chartPtOut).IsHyperbolic := by
  obtain ⟨hp, hfix, han, hans, -, -⟩ := id he
  have hpt : chartPtOut ∈ e.target := hfix ▸ e.map_source hp
  have hsp : e.symm chartPtOut = chartPtOut := by simpa [hfix] using e.left_inv hp
  have hd : HasFDerivAt e (fderiv ℝ e chartPtOut) chartPtOut :=
    (han _ hp).differentiableAt.hasFDerivAt
  have hd' : HasFDerivAt e.symm (fderiv ℝ e.symm chartPtOut) chartPtOut :=
    (hans _ hpt).differentiableAt.hasFDerivAt
  have h1 : (fderiv ℝ e chartPtOut).comp (fderiv ℝ e.symm chartPtOut) =
      ContinuousLinearMap.id ℝ _ := by
    have hc : HasFDerivAt (e ∘ e.symm)
        ((fderiv ℝ e chartPtOut).comp (fderiv ℝ e.symm chartPtOut)) chartPtOut := by
      refine HasFDerivAt.comp chartPtOut ?_ hd'
      rw [hsp]
      exact hd
    exact hc.unique ((hasFDerivAt_id _).congr_of_eventuallyEq (e.eventually_right_inverse hpt))
  have h2 : (fderiv ℝ e.symm chartPtOut).comp (fderiv ℝ e chartPtOut) =
      ContinuousLinearMap.id ℝ _ := by
    have hc : HasFDerivAt (e.symm ∘ e)
        ((fderiv ℝ e.symm chartPtOut).comp (fderiv ℝ e chartPtOut)) chartPtOut := by
      refine HasFDerivAt.comp chartPtOut ?_ hd
      rw [hfix]
      exact hd'
    exact hc.unique ((hasFDerivAt_id _).congr_of_eventuallyEq (e.eventually_left_inverse hp))
  intro μ hμ hμ1
  obtain ⟨hμ0, hinv⟩ := l6j_aeval_charpoly_inv h1 h2 hμ
  exact l6j_isHyperbolic he μ⁻¹ hinv (by rw [norm_inv, hμ1, inv_one])

/-- `τ(z(x̃_out))` represents `q_in` (`z(x̃_out)` is a rescaling of `q_out`'s representative). -/
private lemma l6j_classOf_in : classOf (tau (fullerOfChart xTildeOut)) = qIn0 := by
  obtain ⟨-, -, h', hc⟩ := classOf_qOutCart
  rw [l6d_fullerOfChart_xTildeOut, tau_scale, ← one_smul ℂ (scale l6d_lam (tau qOutCart)),
    classOf_smul_scale one_mem_VT l6d_lam_pos h', hc]


/-- `Ad_{R⁻¹} ∘ τ ∘ Ad_{R⁻¹} = τ` (`τ Ad_R = Ad_{R⁻¹} τ`, `reinTau_spec`). -/
private lemma l6j_adRinv_reinTau_adRinv (x : iso_PhasePt) :
    iso_adRinvPow 1 (reinTau (iso_adRinvPow 1 x)) = reinTau x := by
  have h : iso_adR (iso_adRinvPow 1 x) = x :=
    irt_adRinvPow_injective 1 (irt_adRinvPow_one_adR (iso_adRinvPow 1 x))
  have := reinTau_spec.2.2.2 (iso_adRinvPow 1 x)
  rw [h] at this
  exact this.symm

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
  obtain ⟨hp, hfix, -, -, hrein, -⟩ := id he
  have hpt : chartPtOut ∈ e.target := hfix ▸ e.map_source hp
  have hsp : e.symm chartPtOut = chartPtOut := by simpa [hfix] using e.left_inv hp
  refine ⟨l6j_classOf_in, ?_, l6j_isHyperbolic_symm he, ?_⟩
  swap
  · -- the local sets of `e⁻¹`: unstable for `e` is stable for `e⁻¹`
    obtain ⟨U, hU, hUo, hUs, hst, δ, hδ, γ, hγC, hγ0, hun⟩ := l6j_main he
    obtain ⟨h1, h2⟩ := Function.localStableSet_symm_eq_localUnstableSet e hUs
    exact ⟨U, hU, hUo, hUs, h1, h2.trans hst, δ, hδ, γ, hγC, hγ0, h1.trans hun⟩
  -- the switching structure, through `F_in = τ F⁻¹ τ`
  obtain ⟨ρ₀, hρ₀, -, hB₀⟩ := l6j_expand he
  obtain ⟨ε₀, hε₀, hχ⟩ := l6j_chi23_neg
  have hsw := eventually_isSwitch_reinSwitchTime
  rw [eventually_nhdsWithin_iff] at hsw
  have hball : ∀ᶠ q in 𝓝 chartPtOut, q ∈ Metric.ball chartPtOut ρ₀ :=
    Metric.ball_mem_nhds chartPtOut hρ₀
  have hgood := ((hball.and hsw).and hχ).and l6j_eventually_mem_lieChartDomain
  have htgt : ∀ᶠ q in 𝓝 chartPtOut, q ∈ e.target := e.open_target.mem_nhds hpt
  have hgood' := htgt.and ((e.continuousAt_symm hpt).eventually (by rw [hsp]; exact hgood))
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hgood'] with p ⟨hpt', ⟨⟨hB, hP⟩, hneg⟩, hdom⟩ hp1
  have hp1 : 0 < p.1 := hp1
  -- the preimage `p' = e⁻¹ p`, a chart point with `r > 0`
  set p' := e.symm p with hp'
  have hs' : p' ∈ e.source := e.map_target hpt'
  have hep : e p' = p := e.right_inv hpt'
  have hp'1 : 0 < p'.1 := by
    by_contra h
    push Not at h
    have := (hB₀ p' hB).2 h
    rw [hep] at this
    linarith
  obtain ⟨hT0, hmax, -, -, himg⟩ := hP hp'1
  have hdom' := lieChart_spec (hdom hp'1)
  set T := reinSwitchTime (lieChart p') with hTdef
  set y : ℝ → iso_PhasePt := fun s ↦ iso_vertexFlow 1 (lieChart p') s with hy
  have hlc : lieChart p = iso_adRinvPow 1 (y T) := by
    rw [← hep, hrein p' hs' hp'1, himg]
    rfl
  -- the flow from `τ(q)` with `e₂` is the reversed arc from `q'`, rotated and reflected
  have hM : ∀ t, iso_vertexFlow 1 (lieChartIn p) t = reinTau (iso_adRinvPow 1 (y (T - t))) := by
    intro t
    have h2 : iso_vertexFlow 2 (iso_adRinvPow 1 (y T)) (-t) =
        iso_adRinvPow 1 (iso_vertexFlow 1 (y T) (-t)) := (l6j_adRinv_vertexFlow 1 (y T) (-t)).symm
    rw [lieChartIn, iso_vertexFlow_reinTau, show vertexSwap 1 = 2 from rfl, hlc, h2, hy,
      ← l6j_vertexFlow_add, sub_eq_add_neg]
  have hsf : ∀ t, switchingFn 1 0 (iso_vertexFlow 1 (lieChartIn p) t).2.2
      (iso_vertexFlow 1 (lieChartIn p) t).1 = switchingFn 1 2 (y (T - t)).2.2 (y (T - t)).1 := by
    intro t
    obtain ⟨h0, h1, -⟩ := l6j_phaseHam_mirror (y (T - t))
    rw [← l6d_hamiltonian_sub (iso_vertexFlow 1 (lieChartIn p) t).2.1,
      ← l6d_hamiltonian_sub (y (T - t)).2.1, hM t]
    simp only [phaseHam] at h0 h1
    rw [h0, h1]
  -- the switching time of the mirrored arc is that of the arc from `q'`
  have hT : reinSwitchTime (lieChartIn p) = T := by
    refine IsLeast.csInf_eq ⟨⟨hT0, ?_⟩, ?_⟩
    · rw [hsf, sub_self, hy]
      simp only [ivf_vertexFlow_zero]
      exact hdom'.2.2.1
    · rintro t ⟨ht0, ht⟩
      by_contra hlt
      push Not at hlt
      rw [hsf, ← l6d_hamiltonian_sub (y (T - t)).2.1] at ht
      have := hmax (T - t) ⟨by linarith, by linarith⟩ 2 (by decide)
      simp only [phaseHam] at this
      linarith
  -- the image of the mirrored map is `p'`
  have hRP : reinPoincare (lieChartIn p) = lieChartIn p' := by
    rw [reinPoincare, hT, hM T, sub_self, l6j_adRinv_reinTau_adRinv, hy]
    simp only [ivf_vertexFlow_zero]
    rfl
  have hcm : reinChartMapIn p = p' := by
    rw [reinChartMapIn, hRP, lieChartIn, lieChartInInv, reinTau_spec.1, hdom'.2.2.2.2.2]
  refine ⟨by rw [hT]; exact hT0, ?_, ?_, by rw [hcm]; exact hp'1, by rw [hcm, hRP],
    by rw [hcm]; exact hs', by rw [hcm, hep]⟩
  · -- `e₂` is the strict maximizer on `(0, t_sw)`
    intro t ht j hj
    rw [hT] at ht
    obtain ⟨h0, h1, h2⟩ := l6j_phaseHam_mirror (y (T - t))
    have hs : T - t ∈ Ioo 0 T := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    rw [hM t]
    obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp
    · rw [h0, h1]
      exact hmax (T - t) hs 2 (by decide)
    · exact absurd rfl hj
    · rw [h2, h1]
      exact hmax (T - t) hs 0 (by decide)
  · -- `e₁` beats `e₂` right after `t_sw`: `χ₂₃ < 0` just before the wall on the arc from `q'`
    intro ε hε
    rw [hT]
    set r := p'.1 with hr
    set s := -(min ε (r * ε₀)) / 2 with hs
    have hm : 0 < min ε (r * ε₀) := lt_min hε (mul_pos hp'1 hε₀)
    have hs0 : s < 0 := by rw [hs]; linarith
    have hsε : -ε < s := by
      have := min_le_left ε (r * ε₀)
      rw [hs]; linarith
    have hsr : -ε₀ < s / r := by
      rw [lt_div_iff₀ hp'1]
      have := min_le_right ε (r * ε₀)
      rw [hs]; nlinarith
    have hsr0 : s / r < 0 := div_neg_of_neg_of_pos hs0 hp'1
    refine ⟨T - s, ⟨by linarith, by linarith⟩, ?_⟩
    obtain ⟨h0, h1, -⟩ := l6j_phaseHam_mirror (y (T - (T - s)))
    rw [hM, h0, h1, sub_sub_cancel]
    have hchi : switchingFn 1 2 (y s).2.2 (y s).1 = r ^ 3 * l6d_chi23 (s / r, r, p'.2) := by
      rw [← l6d_chiRaw_eq_chi23 (p := (s / r, r, p'.2)) hp'1.ne']
      simp only [l6d_chiRaw, l6d_flowPt, hy, div_mul_cancel₀ s hp'1.ne']
      rfl
    have hneg' := hneg (s / r) hsr hsr0
    have := l6d_hamiltonian_sub (y s).2.1 (y s).2.2 (y s).1 1 2
    rw [hchi] at this
    simp only [phaseHam]
    nlinarith [pow_pos hp'1 3]

end SmoothedPolygons
