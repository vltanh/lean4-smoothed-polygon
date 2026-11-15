module

public import SmoothedPolygons.Ch14.ArcPoincareMap
public import SmoothedPolygons.Ch14.UnstableCurve

/-!
# Chapter 14, N4: the conditions on one arc (Proposition 3.4) and the region `𝒢*`

`notes/n4/proof.md` §3: four sign conditions on the arc parameters of a section point decide the
three predicates of N4 (`SmoothedPolygons/Ch14/UnstableCurve.lean`) on one arc,

  **P1** `f₀ > 0`, **P2** `q ≤ 0`, **P4** `p > 0`, and the sign of `F(log Y)`
  (`F(log Y) = A - Y + B/Y + Y log Y`, `ArcParams.F_log`),

and P1, P4 carry over to the next point by themselves, `ρ₁` decreases and the radius expands by at
least `λ_lb = (Y - 2)/((Y - 1)(Y' - 2))`. The region `𝒢*` (`arcRegion`) is the set of section
points with `r > 0`, P1, P2, P4 and **E** (`λ_lb ≥ 1`, i.e. `(Y - 1)(Y' - 2) ≤ Y - 2`): five
explicit inequalities, no logarithm. Part of the reduction of N4 to (INV)
(`ArcRegionInvariant`, `SmoothedPolygons/Ch14/ArcRegionInvariant.lean`).

**Departure from the paper.** The book checks along the computed unstable curve that "the other
switching functions `χ_ij` remain positive" and that the curve reaches the star boundary
(Figure 14.2, TeX 11951–11991); the formalization proves these on one arc from P1–P4 and the sign
of `F(log Y)`, by the exact structure of the arcs (see `SmoothedPolygons/Ch14/ArcParams.lean`).

## Statements

* `hasDerivAt_e3_sub_e2`: the slope of `H(e₃) - H(e₂)` along the `e₃`-flow at a section point is
  `-2√3 p/(Y' - 1)`.
* **Proposition 3.4**:
  (1) `switchEntersE2_of_arc`: P1 ∧ P4 ⟹ `SwitchEntersE2 q`;
  `switchesBeforeExit_of_arc`: P1 ∧ P2 ∧ `F(log Y) < 0` ⟹ the arc switches at `t_sw = ε τ_sw`
  inside the star domain;
  (2) `arcSwitchesToE1_of_arc`: `r > 0` ∧ P1 ∧ P2 ∧ P4 ∧ `F(log Y) < 0` ⟹ `ArcSwitchesToE1 q`;
  (3) `arcLeavesStarDomain_of_arc`: `r > 0` ∧ P1 ∧ P2 ∧ P4 ∧ `F(log Y) ≥ 0` ⟹
  `ArcLeavesStarDomain q` (with `T = ε log Y`), and `arcLeavesStarDomain_of_cusp`:
  `r > 0` ∧ P4 ∧ (the cusp criterion `A + min(B, 0) > Y`) ⟹ `ArcLeavesStarDomain q`;
  (4) `arc_propagation` (with (3.1)): in case (2), `F(q)` is a section point with P1 and P4,
  `ε_new < ε`, `r(F q) > 0` and `r(F q)/r(q) > λ_lb`.
* `arcRegion` (`𝒢*`) and `radius_lt_of_mem_arcRegion`: on `𝒢*`, in case (2), `r(F q) > r(q)`.

## Proofs (the route, proof.md §3)

Throughout, `q` is a section point (`IsArcSectionPt`), so `H(e₂) = H(e₃) = 0`, `g₀ = 0`
(`arcG0_eq_zero`), and Theorem 1.3 (`arc_normalForm`) gives `N₂₁ = (8ε³/√3) f(t/ε)`,
`N₂₃ = (8ε³/√3) g(t/ε)`; for `0 ≤ t < T = ε log Y` the state is a star state
(`isStarState_iso_vfX_one_iff`), so `χ₂₁`, `χ₂₃` have the signs of `f`, `g` there
(`switchingFn_pos_iff`, `switchingFn_neg_iff`); `r > 0` is `Y' > 2` (`X00_eq_arcRadius`).

1. `hasDerivAt_e3_sub_e2`: `hasDerivAt_phaseHam_vertexFlow` (for `e₃` and `e₂`) and
   `phaseHamSlope_e3`: the slope is `-L_{V₂} χ₂₃`. Along the `e₂`-flow `χ₂₃ =
   N₂₃/(⟨X, Z_{e₂}⟩⟨X, Z_{e₃}⟩)` with `N₂₃(0) = 0`, so `L_{V₂} χ₂₃ = N₂₃'(0)/((4/3) ρ₁ ρ₀)`
   ((1.1)), and `N₂₃'(0) = (8ε²/√3) g'(0) = (8ε²/√3) p` (`ArcParams.hasDerivAt_g_zero`); with
   `ρ₀ = ε(Y' - 1)` this is `2√3 p/(Y' - 1)`.
2. (1): `H(e₁) < H(e₂)` is `χ₂₁ > 0`, i.e. `N₂₁(q) > 0`, i.e. `f₀ > 0`. Step 1 and `p > 0`:
   `H(e₃) - H(e₂)` vanishes at `0` (section) with negative slope, so it is negative on some
   `(0, δ)` (`HasDerivAt` and the definition of the derivative, e.g. via
   `hasDerivAt_iff_tendsto_slope` and `Filter.Tendsto.eventually_lt`).
3. `switchesBeforeExit_of_arc`: `τ_sw < log Y` (`ArcParams.tauSw_lt_log_iff`); on `(0, τ_sw)`
   `f > 0`, at `τ_sw` it vanishes (`ArcParams.tauSw_spec`); so the zero set of `χ₂₁` on
   `(0, T)` starts at `ε τ_sw` and `reinSwitchTime q = ε τ_sw ∈ (0, T)` (as in
   `reinSwitchTime_eq_tauSw`).
4. (2): `t_sw = ε τ_sw` (step 3); for `t ∈ (0, t_sw)`, `χ₂₁ > 0` (`f > 0`) and `χ₂₃ > 0`
   (`g > 0` by `ArcParams.g_pos`, using `Y' > 2`, `p > 0`, `g₀ = 0`); right after `t_sw`, still
   inside the star domain, `f < 0` (`ArcParams.tauSw_spec`), so `H(e₁) > H(e₂)`.
5. (3): `T = ε log Y > 0` (`arcExitTime_pos`), `X(T)` is not a star state
   (`ρ₂_iso_vfX_one_arcExitTime`); on `(0, T)`, `f > 0` by `ArcParams.f_pos_of_F_log_nonneg`
   (resp. `ArcParams.f_pos_of_cusp`) and `g > 0` by `ArcParams.g_pos`.
6. (4): `arcParams_reinPoincare`, `radius_reinPoincare` (Theorem 2.1, with step 3 for
   `SwitchesBeforeExit`) and `ArcParams.step_spec` (`Y > 1` by `one_lt_arcY`, `Y' > 2` from
   `r > 0`, `g₀ = 0`); `arcParams_radius` translates `radius` to `X₁₁`.
7. `radius_lt_of_mem_arcRegion`: E gives `λ_lb ≥ 1` (`(Y - 1)(Y' - 2) > 0`), and (4).
-/

@[expose] public section

namespace SmoothedPolygons

open Set Filter Topology

/-- **The region `𝒢*`** (proof.md §5.2): the section points with `r > 0` and
**P1** `f₀ > 0`, **P2** `q ≤ 0`, **P4** `p > 0`, **E** `(Y - 1)(Y' - 2) ≤ Y - 2` (`λ_lb ≥ 1`):
five explicit inequalities between algebraic functions of the chart coordinates. -/
def arcRegion : Set iso_PhasePt :=
  {q | IsArcSectionPt q ∧ 0 < q.1 0 0 ∧ 0 < arcF0 q ∧ arcQ q ≤ 0 ∧ 0 < arcP q ∧
    (arcY q - 1) * (arcY' q - 2) ≤ arcY q - 2}

variable {q : iso_PhasePt}

/-- The slope of `H(e₃) - H(e₂)` along the `e₃`-flow at a section point is `-2√3 p/(Y' - 1)`
(Lemma 2.3 and Theorem 1.3). -/
theorem hasDerivAt_e3_sub_e2 (hq : IsArcSectionPt q) :
    HasDerivAt (fun t ↦ phaseHam (iso_vertexFlow 2 q t) (vertex 2) -
      phaseHam (iso_vertexFlow 2 q t) (vertex 1)) (-(2 * √3 * arcP q / (arcY' q - 1))) 0 := by
  sorry

/-- **Proposition 3.4 (1)**: P1 ∧ P4 ⟹ `SwitchEntersE2 q` (`H(e₁) < H(e₂)` is `f₀ > 0`; `e₃` drops
below `e₂` along its own flow because `p > 0`). -/
theorem switchEntersE2_of_arc (hq : IsArcSectionPt q) (h1 : 0 < arcF0 q) (h4 : 0 < arcP q) :
    SwitchEntersE2 q := by
  sorry

/-- **Proposition 3.4**, the switch: P1 ∧ P2 ∧ `F(log Y) < 0` ⟹ the `e₂`-arc switches inside the
star domain, at `t_sw = ε τ_sw`. -/
theorem switchesBeforeExit_of_arc (hq : IsArcSectionPt q) (h1 : 0 < arcF0 q) (h2 : arcQ q ≤ 0)
    (hF : (arcParams q).F (Real.log (arcY q)) < 0) :
    SwitchesBeforeExit q ∧ reinSwitchTime q = arcEps q * (arcParams q).tauSw := by
  sorry

/-- **Proposition 3.4 (2)**: `r > 0` ∧ P1 ∧ P2 ∧ P4 ∧ `F(log Y) < 0` ⟹ `ArcSwitchesToE1 q`. -/
theorem arcSwitchesToE1_of_arc (hq : IsArcSectionPt q) (hr : 0 < q.1 0 0) (h1 : 0 < arcF0 q)
    (h2 : arcQ q ≤ 0) (h4 : 0 < arcP q) (hF : (arcParams q).F (Real.log (arcY q)) < 0) :
    ArcSwitchesToE1 q := by
  sorry

/-- **Proposition 3.4 (3)**: `r > 0` ∧ P1 ∧ P2 ∧ P4 ∧ `F(log Y) ≥ 0` ⟹ `ArcLeavesStarDomain q`,
with `T = ε log Y`. -/
theorem arcLeavesStarDomain_of_arc (hq : IsArcSectionPt q) (hr : 0 < q.1 0 0)
    (h1 : 0 < arcF0 q) (h2 : arcQ q ≤ 0) (h4 : 0 < arcP q)
    (hF : 0 ≤ (arcParams q).F (Real.log (arcY q))) :
    ArcLeavesStarDomain q := by
  sorry

/-- **Proposition 3.4 (3)**, the cusp case: `r > 0` ∧ P4 ∧ (the cusp criterion, Lemma 3.3,
`A + min(B, 0) > Y`) ⟹ `ArcLeavesStarDomain q`. -/
theorem arcLeavesStarDomain_of_cusp (hq : IsArcSectionPt q) (hr : 0 < q.1 0 0)
    (h4 : 0 < arcP q) (hc : arcY q < (arcParams q).A + min (arcParams q).B 0) :
    ArcLeavesStarDomain q := by
  sorry

/-- **Proposition 3.4 (4)** (propagation) and (3.1): in case (2), `F(q)` is a section point with
P1 and P4, `ε_new < ε`, `r(F q) > 0` and `r(F q)/r(q) > λ_lb = (Y - 2)/((Y - 1)(Y' - 2))`. So
`SwitchEntersE2` never has to be checked along an orbit after its first point. -/
theorem arc_propagation (hq : IsArcSectionPt q) (hr : 0 < q.1 0 0) (h1 : 0 < arcF0 q)
    (h2 : arcQ q ≤ 0) (h4 : 0 < arcP q) (hF : (arcParams q).F (Real.log (arcY q)) < 0) :
    IsArcSectionPt (reinPoincare q) ∧ 0 < arcF0 (reinPoincare q) ∧ 0 < arcP (reinPoincare q) ∧
      arcEps (reinPoincare q) < arcEps q ∧ 0 < (reinPoincare q).1 0 0 ∧
      (arcY q - 2) / ((arcY q - 1) * (arcY' q - 2)) < (reinPoincare q).1 0 0 / q.1 0 0 := by
  sorry

/-- **Expansion on `𝒢*`** (proof.md §5.2): for `q ∈ 𝒢*` whose arc switches inside the star domain,
`r(F q) > r(q)` (E gives `λ_lb ≥ 1`). -/
theorem radius_lt_of_mem_arcRegion (hq : q ∈ arcRegion)
    (hF : (arcParams q).F (Real.log (arcY q)) < 0) : q.1 0 0 < (reinPoincare q).1 0 0 := by
  sorry

end SmoothedPolygons
