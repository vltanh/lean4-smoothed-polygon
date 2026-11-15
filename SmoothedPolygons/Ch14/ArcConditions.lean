module

public import SmoothedPolygons.Ch14.ArcPoincareMap
public import SmoothedPolygons.Ch14.ArcStepExit
public import SmoothedPolygons.Ch14.UnstableCurve
import SmoothedPolygons.Ch7.Isolated.VertexFlow

/-!
# Chapter 14, N4: the conditions on one arc (Proposition 3.4) and the region `𝒢*`

Part of the formalization's proof of N4 (`UnstableCurveLeavesStarDomain`, Figure 14.2) without
computer assistance. **Departure from the paper**, by the user's decision: the book checks along
the computed unstable curve that "the other switching functions `χ_ij` remain positive" and that
the curve reaches the star boundary (Figure 14.2, TeX 11951–11991; REPORT.md E88); the
formalization proves these on one arc from P1–P4 and the sign of `F(log Y)`, by the exact
structure of the Reinhardt flow along an `e₂`-arc (see `SmoothedPolygons/Ch14/ArcParams.lean`, and
`SmoothedPolygons/Ch14/ArcRegionInvariant.lean` for the numbering of the steps).

This file is §3: four sign conditions on the arc parameters of a section point decide the three
predicates of N4 (`SmoothedPolygons/Ch14/UnstableCurve.lean`) on one arc,

  **P1** `f₀ > 0`, **P2** `q ≤ 0`, **P4** `p > 0`, and the sign of `F(log Y)`
  (`F(log Y) = A - Y + B/Y + Y log Y`, `ArcParams.F_log`),

and P1, P4 carry over to the next point by themselves, `ρ₁` decreases and the radius expands by at
least `λ_lb = (Y - 2)/((Y - 1)(Y' - 2))`. The region `𝒢*` (`arcRegion`, §5.2) is the set of
section points with `r > 0`, P1, P2, P4 and **E** (`λ_lb ≥ 1`, i.e. `(Y - 1)(Y' - 2) ≤ Y - 2`):
five explicit inequalities, no logarithm.

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
  `arcLeavesStarDomain_of_Y_ge` (INV Lemma 6, the exit criterion of the proof of (INV)):
  `r > 0` ∧ P1 ∧ P4 ∧ `Y ≥ 16/5` ∧ `f₀ ≥ q (1 - 1/Y)` ⟹ `ArcLeavesStarDomain q` (no sign
  condition on `q`);
  (4) `arc_propagation` (with (3.1)): in case (2), `F(q)` is a section point with P1 and P4,
  `ε_new < ε`, `r(F q) > 0` and `r(F q)/r(q) > λ_lb`.
* `arcRegion` (`𝒢*`) and `radius_lt_of_mem_arcRegion`: on `𝒢*`, in case (2), `r(F q) > r(q)`.

## Proofs (the route, §3)

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
   `(0, δ)` (`HasDerivWithinAt.limsup_slope_le'` on `Ioi 0`: the slopes are eventually below a
   negative number; then `mem_nhdsGT_iff_exists_Ioo_subset`).
3. `switchesBeforeExit_of_arc`: `τ_sw < log Y` (`ArcParams.tauSw_lt_log_iff`); on `(0, τ_sw)`
   `f > 0`, at `τ_sw` it vanishes (`ArcParams.tauSw_spec`); so the zero set of `χ₂₁` on
   `(0, T)` starts at `ε τ_sw` and `reinSwitchTime q = ε τ_sw ∈ (0, T)` (as in
   `reinSwitchTime_eq_tauSw`).
4. (2): `t_sw = ε τ_sw` (step 3); for `t ∈ (0, t_sw)`, `χ₂₁ > 0` (`f > 0`) and `χ₂₃ > 0`
   (`g > 0` by `ArcParams.g_pos`, using `Y' > 2`, `p > 0`, `g₀ = 0`); right after `t_sw`, still
   inside the star domain, `f < 0` (`ArcParams.tauSw_spec`), so `H(e₁) > H(e₂)`.
5. (3): `T = ε log Y > 0` (`arcExitTime_pos`), `X(T)` is not a star state
   (`ρ₂_iso_vfX_one_arcExitTime`); on `(0, T)`, `f > 0` by `ArcParams.f_pos_of_F_log_nonneg`
   (resp. `ArcParams.f_pos_of_cusp`, resp. `ArcParams.f_pos_of_Y_ge` for
   `arcLeavesStarDomain_of_Y_ge`) and `g > 0` by `ArcParams.g_pos`.
6. (4): `arcParams_reinPoincare`, `radius_reinPoincare` (Theorem 2.1, with step 3 for
   `SwitchesBeforeExit`) and `ArcParams.step_spec` (`Y > 1` by `one_lt_arcY`, `Y' > 2` from
   `r > 0`, `g₀ = 0`); `arcParams_radius` translates `radius` to `X₁₁`.
7. `radius_lt_of_mem_arcRegion`: E gives `λ_lb ≥ 1` (`(Y - 1)(Y' - 2) > 0`), and (4).
-/

@[expose] public section

namespace SmoothedPolygons

open Set Filter Topology

/-- **The region `𝒢*`** (§5.2): the section points with `r > 0` and
**P1** `f₀ > 0`, **P2** `q ≤ 0`, **P4** `p > 0`, **E** `(Y - 1)(Y' - 2) ≤ Y - 2` (`λ_lb ≥ 1`):
five explicit inequalities between algebraic functions of the chart coordinates. -/
def arcRegion : Set iso_PhasePt :=
  {q | IsArcSectionPt q ∧ 0 < q.1 0 0 ∧ 0 < arcF0 q ∧ arcQ q ≤ 0 ∧ 0 < arcP q ∧
    (arcY q - 1) * (arcY' q - 2) ≤ arcY q - 2}

variable {q : iso_PhasePt}

/-- The facts of a section point used below: a star state, traceless costates and
`H(e₂) = H(e₃) = 0` (`H(e₂) = H(e₃) + χ₂₃`). -/
private theorem isStarState_trace_phaseHam_of_isArcSectionPt (hq : IsArcSectionPt q) :
    IsStarState q.1 ∧ q.2.1.trace = 0 ∧ q.2.2.trace = 0 ∧ phaseHam q (vertex 1) = 0 ∧
      phaseHam q (vertex 2) = 0 := by
  obtain ⟨⟨⟨-, hL, hR, -, -, hH, hχ⟩, -⟩, hX⟩ := hq
  have h := hamiltonian_sub_eq_switchingFn q.2.1 q.2.2 q.1 1 2
  refine ⟨hX, hL, hR, ?_, hH⟩
  change hamiltonian (-1) q.2.1 q.2.2 q.1 (vertex 1) = 0
  linarith

/-- Multiplication by a positive constant keeps the sign. -/
private theorem sign_mul_iff_of_pos {c N : ℝ} (hc : 0 < c) :
    (0 < c * N ↔ 0 < N) ∧ (c * N < 0 ↔ N < 0) ∧ (c * N = 0 ↔ N = 0) := by
  refine ⟨mul_pos_iff_of_pos_left hc, ⟨fun h ↦ ?_, fun h ↦ mul_neg_of_pos_of_neg hc h⟩, ?_⟩
  · by_contra h'
    linarith [mul_nonneg hc.le (not_lt.1 h')]
  · rw [mul_eq_zero]
    exact ⟨fun h ↦ h.resolve_left hc.ne', Or.inr⟩

/-- **The signs along the arc** (step 2 of the route): for `0 ≤ t < T`, the state is a star state,
so `χ₂₁` has the sign of `N₂₁`, i.e. of `f(t/ε)`, and `χ₂₃` that of `N₂₃`, i.e. of `g(t/ε)`
(Theorem 1.3). -/
private theorem phaseHam_signs_along_arc (hq : IsArcSectionPt q) {t : ℝ} (ht0 : 0 ≤ t)
    (htT : t < arcExitTime q) :
    (phaseHam (iso_vertexFlow 1 q t) (vertex 0) < phaseHam (iso_vertexFlow 1 q t) (vertex 1) ↔
        0 < (arcParams q).f (t / arcEps q)) ∧
      (phaseHam (iso_vertexFlow 1 q t) (vertex 1) < phaseHam (iso_vertexFlow 1 q t) (vertex 0) ↔
        (arcParams q).f (t / arcEps q) < 0) ∧
      (switchingFn 1 0 (iso_vertexFlow 1 q t).2.2 (iso_vertexFlow 1 q t).1 = 0 ↔
        (arcParams q).f (t / arcEps q) = 0) ∧
      (phaseHam (iso_vertexFlow 1 q t) (vertex 2) < phaseHam (iso_vertexFlow 1 q t) (vertex 1) ↔
        0 < (arcParams q).g (t / arcEps q)) := by
  obtain ⟨hX, -, hR, hH, -⟩ := isStarState_trace_phaseHam_of_isArcSectionPt hq
  have hXt : IsStarState (iso_vertexFlow 1 q t).1 := (isStarState_iso_vfX_one_iff hX ht0).2 htT
  obtain ⟨hf, hg⟩ := arc_normalForm hX hR hH t
  have hc : 0 < √3 / (8 * arcEps q ^ 3) := by have := arcEps_pos hX; positivity
  obtain ⟨p1, n1, z1⟩ := sign_mul_iff_of_pos (N := switchingNum 1 0 (iso_vertexFlow 1 q t)) hc
  obtain ⟨p2, -, -⟩ := sign_mul_iff_of_pos (N := switchingNum 1 2 (iso_vertexFlow 1 q t)) hc
  set Q := iso_vertexFlow 1 q t
  have e10 := hamiltonian_sub_eq_switchingFn Q.2.1 Q.2.2 Q.1 1 0
  have e12 := hamiltonian_sub_eq_switchingFn Q.2.1 Q.2.2 Q.1 1 2
  rw [← hf, ← hg, p1, n1, z1, p2, ← switchingFn_pos_iff 1 0 hXt, ← switchingFn_neg_iff 1 0 hXt,
    ← switchingFn_eq_zero_iff 1 0 hXt, ← switchingFn_pos_iff 1 2 hXt]
  unfold phaseHam
  refine ⟨⟨fun h ↦ ?_, fun h ↦ ?_⟩, ⟨fun h ↦ ?_, fun h ↦ ?_⟩, Iff.rfl, ⟨fun h ↦ ?_, fun h ↦ ?_⟩⟩ <;>
    linarith

/-- On a section point, `r > 0` is `Y' > 2` (`r = ε (Y' - 2)/2`). -/
private theorem two_lt_arcParams_Y' (hq : IsArcSectionPt q) (hr : 0 < q.1 0 0) :
    2 < (arcParams q).Y' := by
  have hX := hq.2
  have hε := arcEps_pos hX
  rw [arcParams_Y' hX]
  have h := X00_eq_arcRadius hε.ne'
  by_contra h'
  have : arcEps q * (arcY' q - 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hε.le (by linarith [not_lt.1 h'])
  linarith

/-- **`χ₂₃` along the `e₂`-flow near `t = 0`** (step 1 of the route): by (1.1) and Theorem 1.3,
`χ₂₃(t) = N₂₃/(⟨X, Z_{e₂}⟩⟨X, Z_{e₃}⟩) = 2√3 ε g(t/ε)/(Y' e^{t/ε} - 1)`, so its slope at `0`
is `2√3 g'(0)/(Y' - 1) = 2√3 p/(Y' - 1)` (`g(0) = g₀ = 0`). -/
private theorem hasDerivAt_switchingFn_one_two_vertexFlow (hq : IsArcSectionPt q) :
    HasDerivAt (fun t ↦ switchingFn 1 2 (iso_vertexFlow 1 q t).2.2 (iso_vertexFlow 1 q t).1)
      (2 * √3 * arcP q / (arcY' q - 1)) 0 := by
  obtain ⟨hX, -, hR, hH, -⟩ := isStarState_trace_phaseHam_of_isArcSectionPt hq
  have hε : 0 < arcEps q := arcEps_pos hX
  have hY'1 : 1 < arcY' q := one_lt_arcY' hX
  have hg0 : (arcParams q).g0 = 0 := arcG0_eq_zero hq
  have hD : HasDerivAt (fun t ↦ arcY' q * Real.exp (t / arcEps q) - 1)
      (arcY' q * (Real.exp (0 / arcEps q) * (1 / arcEps q))) 0 :=
    ((((hasDerivAt_id (0 : ℝ)).div_const (arcEps q)).exp).const_mul (arcY' q)).sub_const 1
  have hD0 : arcY' q * Real.exp (0 / arcEps q) - 1 ≠ 0 := by
    rw [zero_div, Real.exp_zero, mul_one]; linarith
  have hg : HasDerivAt (fun t ↦ (arcParams q).g (t / arcEps q))
      (((arcParams q).g0 + (arcParams q).p) * (1 / arcEps q)) 0 := by
    have h0 : HasDerivAt (arcParams q).g ((arcParams q).g0 + (arcParams q).p) (0 / arcEps q) := by
      rw [zero_div]; exact (arcParams q).hasDerivAt_g_zero
    exact h0.comp 0 ((hasDerivAt_id (0 : ℝ)).div_const (arcEps q))
  have hφ := (hg.const_mul (2 * √3 * arcEps q)).div hD hD0
  have heq : (fun t ↦ 2 * √3 * arcEps q * (arcParams q).g (t / arcEps q) /
      (arcY' q * Real.exp (t / arcEps q) - 1)) =ᶠ[𝓝 0]
      (fun t ↦ switchingFn 1 2 (iso_vertexFlow 1 q t).2.2 (iso_vertexFlow 1 q t).1) := by
    filter_upwards [hD.continuousAt.eventually_ne hD0] with t ht
    have htr : (iso_vfX 1 q t).trace = 0 := by
      rw [iso_vfX_one_eq hX]; exact trace_ofFrame _ _ _
    obtain ⟨-, t1, t2⟩ := traceForm_controlMatrix_vertex htr
    obtain ⟨r1, -, r0⟩ := ρ_iso_vfX_one hX t
    rw [r1] at t1
    rw [r0] at t2
    have hc : -(2 / √3) ≠ 0 := neg_ne_zero.2 (by positivity)
    have n1 : traceForm (iso_vertexFlow 1 q t).1 (controlMatrix (vertex 1)) ≠ 0 := by
      change traceForm (iso_vfX 1 q t) _ ≠ 0
      rw [t1]; exact mul_ne_zero hc hε.ne'
    have n2 : traceForm (iso_vertexFlow 1 q t).1 (controlMatrix (vertex 2)) ≠ 0 := by
      change traceForm (iso_vfX 1 q t) _ ≠ 0
      rw [t2]; exact mul_ne_zero hc (mul_ne_zero hε.ne' ht)
    have hN := switchingNum_eq 1 2 (iso_vertexFlow 1 q t) n1 n2
    change _ = _ * (traceForm (iso_vfX 1 q t) _ * traceForm (iso_vfX 1 q t) _) at hN
    rw [t1, t2] at hN
    have hnf := (arc_normalForm hX hR hH t).2
    rw [hN] at hnf
    rw [← hnf]
    field_simp
    ring
  have hp : (arcParams q).p = arcP q := rfl
  have hY1 : arcY' q - 1 ≠ 0 := by linarith
  have h := hφ.congr_of_eventuallyEq heq.symm
  convert h using 1
  simp only [zero_div, Real.exp_zero, mul_one, (arcParams q).g_zero, hg0, hp, zero_add, mul_zero,
    zero_mul, sub_zero]
  field_simp

/-- **The exit** (step 5 of the route): if `r > 0`, P4 and `f > 0` on `(0, log Y)`, the arc leaves
the star domain at `T = ε log Y` with `e₂` the strict maximizer on `(0, T)`. -/
private theorem arcLeavesStarDomain_of_f_pos (hq : IsArcSectionPt q) (hr : 0 < q.1 0 0)
    (h4 : 0 < arcP q) (hf : ∀ τ ∈ Ioo 0 (Real.log (arcY q)), 0 < (arcParams q).f τ) :
    ArcLeavesStarDomain q := by
  have hX := hq.2
  have hε := arcEps_pos hX
  have hY' := two_lt_arcParams_Y' hq hr
  have hg0 : (arcParams q).g0 = 0 := arcG0_eq_zero hq
  refine ⟨arcExitTime q, arcExitTime_pos hX, fun h ↦ ?_, fun t ht j hj ↦ ?_⟩
  · have h2 := h.2.2.2.2
    rw [ρ₂_iso_vfX_one_arcExitTime hX] at h2
    exact lt_irrefl _ h2
  · obtain ⟨s1, -, -, s4⟩ := phaseHam_signs_along_arc hq ht.1.le ht.2
    rcases (show j = 0 ∨ j = 2 by fin_cases j <;> simp_all) with rfl | rfl
    · refine s1.2 (hf _ ⟨div_pos ht.1 hε, ?_⟩)
      rw [div_lt_iff₀' hε]
      exact ht.2
    · exact s4.2 ((arcParams q).g_pos hg0 h4 hY'.le (div_pos ht.1 hε))

/-- The slope of `H(e₃) - H(e₂)` along the `e₃`-flow at a section point is `-2√3 p/(Y' - 1)`
(Lemma 2.3 and Theorem 1.3). -/
theorem hasDerivAt_e3_sub_e2 (hq : IsArcSectionPt q) :
    HasDerivAt (fun t ↦ phaseHam (iso_vertexFlow 2 q t) (vertex 2) -
      phaseHam (iso_vertexFlow 2 q t) (vertex 1)) (-(2 * √3 * arcP q / (arcY' q - 1))) 0 := by
  obtain ⟨hX, -, -, -, -⟩ := isStarState_trace_phaseHam_of_isArcSectionPt hq
  obtain ⟨-, t1, t2⟩ := traceForm_controlMatrix_vertex hX.1
  have hc : -(2 / √3) ≠ 0 := neg_ne_zero.2 (by positivity)
  have n1 : traceForm q.1 (controlMatrix (vertex 1)) ≠ 0 := by
    rw [t1]; exact mul_ne_zero hc hX.2.2.2.1.ne'
  have n2 : traceForm q.1 (controlMatrix (vertex 2)) ≠ 0 := by
    rw [t2]; exact mul_ne_zero hc hX.2.2.1.ne'
  have d22 := hasDerivAt_phaseHam_vertexFlow 2 2 q 0 (by rw [ivf_vertexFlow_zero]; exact n2)
  have d21 := hasDerivAt_phaseHam_vertexFlow 2 1 q 0 (by rw [ivf_vertexFlow_zero]; exact n1)
  have d11 := hasDerivAt_phaseHam_vertexFlow 1 1 q 0 (by rw [ivf_vertexFlow_zero]; exact n1)
  have d12 := hasDerivAt_phaseHam_vertexFlow 1 2 q 0 (by rw [ivf_vertexFlow_zero]; exact n2)
  rw [ivf_vertexFlow_zero] at d22 d21 d11 d12
  have hchi : HasDerivAt
      (fun t ↦ switchingFn 1 2 (iso_vertexFlow 1 q t).2.2 (iso_vertexFlow 1 q t).1)
      (phaseHamSlope 1 1 q - phaseHamSlope 1 2 q) 0 := by
    convert d11.sub d12 using 1
    funext t
    exact (hamiltonian_sub_eq_switchingFn _ _ _ 1 2).symm
  have hu := hchi.unique (hasDerivAt_switchingFn_one_two_vertexFlow hq)
  convert d22.sub d21 using 1
  rw [phaseHamSlope_e3 q n1 n2, hu]

/-- **Proposition 3.4 (1)**: P1 ∧ P4 ⟹ `SwitchEntersE2 q` (`H(e₁) < H(e₂)` is `f₀ > 0`; `e₃` drops
below `e₂` along its own flow because `p > 0`). -/
theorem switchEntersE2_of_arc (hq : IsArcSectionPt q) (h1 : 0 < arcF0 q) (h4 : 0 < arcP q) :
    SwitchEntersE2 q := by
  obtain ⟨hX, -, -, hH, hH2⟩ := isStarState_trace_phaseHam_of_isArcSectionPt hq
  have hε := arcEps_pos hX
  refine ⟨?_, ?_⟩
  · have hc : 0 < √3 / (8 * arcEps q ^ 3) := by positivity
    have hN : 0 < switchingNum 1 0 q := (mul_pos_iff_of_pos_left hc).1 h1
    have := (switchingFn_pos_iff 1 0 hX).2 hN
    have e := hamiltonian_sub_eq_switchingFn q.2.1 q.2.2 q.1 1 0
    unfold phaseHam
    linarith
  · have hY' := one_lt_arcY' hX
    have hneg : -(2 * √3 * arcP q / (arcY' q - 1)) < 0 := by
      have : 0 < arcY' q - 1 := by linarith
      exact neg_neg_of_pos (by positivity)
    have hev := ((hasDerivAt_e3_sub_e2 hq).hasDerivWithinAt (s := Ioi 0)).limsup_slope_le'
      (lt_irrefl 0) hneg
    obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
    refine ⟨δ, hδ, fun t ht ↦ ?_⟩
    have h : slope (fun t ↦ phaseHam (iso_vertexFlow 2 q t) (vertex 2) -
        phaseHam (iso_vertexFlow 2 q t) (vertex 1)) 0 t < 0 := hsub ht
    rw [slope_def_field] at h
    simp only [ivf_vertexFlow_zero, hH, hH2, sub_zero] at h
    by_contra hc
    linarith [div_nonneg (sub_nonneg.2 (not_lt.1 hc)) ht.1.le]

/-- **Proposition 3.4**, the switch: P1 ∧ P2 ∧ `F(log Y) < 0` ⟹ the `e₂`-arc switches inside the
star domain, at `t_sw = ε τ_sw`. -/
theorem switchesBeforeExit_of_arc (hq : IsArcSectionPt q) (h1 : 0 < arcF0 q) (h2 : arcQ q ≤ 0)
    (hF : (arcParams q).F (Real.log (arcY q)) < 0) :
    SwitchesBeforeExit q ∧ reinSwitchTime q = arcEps q * (arcParams q).tauSw := by
  have hX := hq.2
  have hε := arcEps_pos hX
  obtain ⟨hτ0, -, hfz, -, hpos, -⟩ := (arcParams q).tauSw_spec h1 h2
  have hlt : (arcParams q).tauSw < Real.log (arcY q) :=
    ((arcParams q).tauSw_lt_log_iff h1 h2 (one_lt_arcY hX).le).2 hF
  have hT : arcEps q * (arcParams q).tauSw < arcExitTime q := mul_lt_mul_of_pos_left hlt hε
  have h0 : 0 < arcEps q * (arcParams q).tauSw := mul_pos hε hτ0
  have key : reinSwitchTime q = arcEps q * (arcParams q).tauSw := by
    apply IsLeast.csInf_eq
    refine ⟨⟨h0, ?_⟩, ?_⟩
    · rw [(phaseHam_signs_along_arc hq h0.le hT).2.2.1, mul_div_cancel_left₀ _ hε.ne']
      exact hfz
    · rintro t ⟨ht0, hz⟩
      by_contra hlt'
      replace hlt' := not_le.1 hlt'
      have hf0 := (phaseHam_signs_along_arc hq ht0.le (hlt'.trans hT)).2.2.1.1 hz
      have hτ : t / arcEps q ∈ Ico 0 (arcParams q).tauSw :=
        ⟨div_nonneg ht0.le hε.le, (div_lt_iff₀' hε).2 hlt'⟩
      exact (hpos _ hτ).ne' hf0
  exact ⟨⟨key ▸ h0, key ▸ hT⟩, key⟩

/-- **Proposition 3.4 (2)**: `r > 0` ∧ P1 ∧ P2 ∧ P4 ∧ `F(log Y) < 0` ⟹ `ArcSwitchesToE1 q`. -/
theorem arcSwitchesToE1_of_arc (hq : IsArcSectionPt q) (hr : 0 < q.1 0 0) (h1 : 0 < arcF0 q)
    (h2 : arcQ q ≤ 0) (h4 : 0 < arcP q) (hF : (arcParams q).F (Real.log (arcY q)) < 0) :
    ArcSwitchesToE1 q := by
  have hX := hq.2
  have hε := arcEps_pos hX
  obtain ⟨⟨hs0, hsT⟩, key⟩ := switchesBeforeExit_of_arc hq h1 h2 hF
  obtain ⟨-, -, -, -, hpos, hneg⟩ := (arcParams q).tauSw_spec h1 h2
  have hY' := two_lt_arcParams_Y' hq hr
  have hg0 : (arcParams q).g0 = 0 := arcG0_eq_zero hq
  refine ⟨hs0, fun t ht j hj ↦ ?_, fun δ hδ ↦ ?_⟩
  · obtain ⟨s1, -, -, s4⟩ := phaseHam_signs_along_arc hq ht.1.le (ht.2.trans hsT)
    rcases (show j = 0 ∨ j = 2 by fin_cases j <;> simp_all) with rfl | rfl
    · refine s1.2 (hpos _ ⟨div_nonneg ht.1.le hε.le, ?_⟩)
      rw [div_lt_iff₀' hε, ← key]
      exact ht.2
    · exact s4.2 ((arcParams q).g_pos hg0 h4 hY'.le (div_pos ht.1 hε))
  · have hm : 0 < min δ (arcExitTime q - reinSwitchTime q) := lt_min hδ (by linarith)
    have hm1 := min_le_left δ (arcExitTime q - reinSwitchTime q)
    have hm2 := min_le_right δ (arcExitTime q - reinSwitchTime q)
    refine ⟨reinSwitchTime q + min δ (arcExitTime q - reinSwitchTime q) / 2,
      ⟨by linarith, by linarith⟩, ?_⟩
    refine (phaseHam_signs_along_arc hq (by linarith) (by linarith)).2.1.2 (hneg _ ?_)
    rw [lt_div_iff₀' hε, ← key]
    linarith

/-- **Proposition 3.4 (3)**: `r > 0` ∧ P1 ∧ P2 ∧ P4 ∧ `F(log Y) ≥ 0` ⟹ `ArcLeavesStarDomain q`,
with `T = ε log Y`. -/
theorem arcLeavesStarDomain_of_arc (hq : IsArcSectionPt q) (hr : 0 < q.1 0 0)
    (h1 : 0 < arcF0 q) (h2 : arcQ q ≤ 0) (h4 : 0 < arcP q)
    (hF : 0 ≤ (arcParams q).F (Real.log (arcY q))) :
    ArcLeavesStarDomain q := by
  exact arcLeavesStarDomain_of_f_pos hq hr h4 fun τ hτ ↦
    (arcParams q).f_pos_of_F_log_nonneg h1 h2 (one_lt_arcY hq.2).le hF ⟨hτ.1.le, hτ.2⟩

/-- **Proposition 3.4 (3)**, the cusp case: `r > 0` ∧ P4 ∧ (the cusp criterion, Lemma 3.3,
`A + min(B, 0) > Y`) ⟹ `ArcLeavesStarDomain q`. -/
theorem arcLeavesStarDomain_of_cusp (hq : IsArcSectionPt q) (hr : 0 < q.1 0 0)
    (h4 : 0 < arcP q) (hc : arcY q < (arcParams q).A + min (arcParams q).B 0) :
    ArcLeavesStarDomain q := by
  exact arcLeavesStarDomain_of_f_pos hq hr h4 fun τ hτ ↦
    (arcParams q).f_pos_of_cusp (one_lt_arcY hq.2) hc ⟨hτ.1.le, hτ.2.le⟩

/-- **INV Lemma 6** (the exit criterion): `r > 0` ∧ P1 ∧ P4 ∧ `Y ≥ 16/5` ∧
`f₀ ≥ q (1 - 1/Y)` ⟹ `ArcLeavesStarDomain q`, with `T = ε log Y`. No sign condition on `q` (the
point is an image `F(q₀)`, where P2 may fail). In the proof of (INV) it is applied at `F(q₀)` when E
fails there: then `Y ≥ 16/5` by INV Proposition 4 (`ArcParams.YNew_ge`) and `f₀ ≥ q (1 - 1/Y)`
by INV Proposition 5 (`ArcParams.qNew_le_f0New`).

Route: as `arcLeavesStarDomain_of_arc` (step 5 of the module docstring), with
`ArcParams.f_pos_of_Y_ge` (`f > 0` on `[0, log Y)`) in place of `f_pos_of_F_log_nonneg`:
`T = ε log Y > 0`, `X(T)` is not a star state (`ρ₂ = 0`), and on `(0, T)` the state is a star
state (`isStarState_iso_vfX_one_iff`), `N₂₁ = (8ε³/√3) f(t/ε) > 0` and
`N₂₃ = (8ε³/√3) g(t/ε) > 0` (`arc_normalForm`, `ArcParams.g_pos` with `g₀ = 0`, `p > 0`,
`Y' > 2` from `r > 0`), so `χ₂₁, χ₂₃ > 0` (`switchingFn_pos_iff`), i.e. `e₂` is the strict
maximizer. -/
theorem arcLeavesStarDomain_of_Y_ge (hq : IsArcSectionPt q) (hr : 0 < q.1 0 0)
    (h1 : 0 < arcF0 q) (h4 : 0 < arcP q) (hY : 16 / 5 ≤ arcY q)
    (hfq : arcQ q * (1 - 1 / arcY q) ≤ arcF0 q) : ArcLeavesStarDomain q := by
  exact arcLeavesStarDomain_of_f_pos hq hr h4 fun τ hτ ↦
    (arcParams q).f_pos_of_Y_ge hY h1 hfq ⟨hτ.1.le, hτ.2⟩

/-- **Proposition 3.4 (4)** (propagation) and (3.1): in case (2), `F(q)` is a section point with
P1 and P4, `ε_new < ε`, `r(F q) > 0` and `r(F q)/r(q) > λ_lb = (Y - 2)/((Y - 1)(Y' - 2))`. So
`SwitchEntersE2` never has to be checked along an orbit after its first point. -/
theorem arc_propagation (hq : IsArcSectionPt q) (hr : 0 < q.1 0 0) (h1 : 0 < arcF0 q)
    (h2 : arcQ q ≤ 0) (h4 : 0 < arcP q) (hF : (arcParams q).F (Real.log (arcY q)) < 0) :
    IsArcSectionPt (reinPoincare q) ∧ 0 < arcF0 (reinPoincare q) ∧ 0 < arcP (reinPoincare q) ∧
      arcEps (reinPoincare q) < arcEps q ∧ 0 < (reinPoincare q).1 0 0 ∧
      (arcY q - 2) / ((arcY q - 1) * (arcY' q - 2)) < (reinPoincare q).1 0 0 / q.1 0 0 := by
  have hX := hq.2
  have hε := arcEps_pos hX
  obtain ⟨hs, -⟩ := switchesBeforeExit_of_arc hq h1 h2 hF
  have hFq := isArcSectionPt_reinPoincare hq hs
  obtain ⟨-, hpar⟩ := arcParams_reinPoincare hq hs
  obtain ⟨-, -, -, hf0, hp, -, heps, -, hrad, hexp⟩ :=
    (arcParams q).step_spec hε (one_lt_arcY hX) (two_lt_arcParams_Y' hq hr) (arcG0_eq_zero hq) h1 h2
      h4 hF (arcQ (reinPoincare q))
  have hr' : (reinPoincare q).1 0 0 = ((arcParams q).step (arcQ (reinPoincare q))).radius := by
    rw [← hpar, arcParams_radius hFq.2]
  have hrq : (arcParams q).radius = q.1 0 0 := arcParams_radius hX
  have hb : (arcParams q).expansionBound = (arcY q - 2) / ((arcY q - 1) * (arcY' q - 2)) := by
    rw [ArcParams.expansionBound, arcParams_Y' hX]
    rfl
  refine ⟨hFq, ?_, ?_, ?_, hr' ▸ hrad, ?_⟩
  · change 0 < (arcParams (reinPoincare q)).f0
    rw [hpar]; exact hf0
  · change 0 < (arcParams (reinPoincare q)).p
    rw [hpar]; exact hp
  · change (arcParams (reinPoincare q)).eps < (arcParams q).eps
    rw [hpar]; exact heps
  · rw [lt_div_iff₀ hr, hr', ← hrq, ← hb]
    exact hexp

/-- **Expansion on `𝒢*`** (§5.2): for `q ∈ 𝒢*` whose arc switches inside the star domain,
`r(F q) > r(q)` (E gives `λ_lb ≥ 1`). -/
theorem radius_lt_of_mem_arcRegion (hq : q ∈ arcRegion)
    (hF : (arcParams q).F (Real.log (arcY q)) < 0) : q.1 0 0 < (reinPoincare q).1 0 0 := by
  obtain ⟨hs, hr, h1, h2, h4, hE⟩ := hq
  obtain ⟨-, -, -, -, -, hlam⟩ := arc_propagation hs hr h1 h2 h4 hF
  have hY := one_lt_arcY hs.2
  have hY' : 2 < arcY' q := by rw [← arcParams_Y' hs.2]; exact two_lt_arcParams_Y' hs hr
  have hpos : 0 < (arcY q - 1) * (arcY' q - 2) := mul_pos (by linarith) (by linarith)
  have h1le : 1 ≤ (arcY q - 2) / ((arcY q - 1) * (arcY' q - 2)) := (one_le_div hpos).2 hE
  have h := lt_of_le_of_lt h1le hlam
  rwa [one_lt_div hr] at h

end SmoothedPolygons
