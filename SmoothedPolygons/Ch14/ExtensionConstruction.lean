module

public import SmoothedPolygons.Ch14.Asymptotics
public import SmoothedPolygons.Ch14.VertexFlowAnalytic
public import Basic.Analysis.Analytic.DivisionByCoordinate
public import Mathlib.Analysis.Calculus.ImplicitContDiff
import SmoothedPolygons.Ch7.Isolated.VertexFlow
import SmoothedPolygons.Ch7.Isolated.Return

/-!
# Chapter 14: the analytic construction behind Lemma 14.3.1, stated once for both directions

Steps 1–9 of the proof of Lemma 14.3.1 of Hales–Vajjha, *Packings of Smoothed Polygons*
(TeX 11784–11860), with the χ₂₃ check (REPORT.md, E85), in the coordinates `(s, r₀, x̃₀)` (rescaled
time `s = t/r₀` and the initial chart point). The statements of the book are in
`SmoothedPolygons/Ch14/AnalyticExtension.lean`, which uses this file; its module docstring gives
the route step by step.

## One construction, two instances

The construction is stated once: near a divisor point `(0, x̃₀)` it extends the
Reinhardt–Poincaré map in the chart (flow with the control `e₂` from the wall `χ₂₃ = 0` to the wall
`χ₂₁ = 0`, then `Ad_{R⁻¹}`) analytically across `r₀ = 0`, from the side `κ r₀ > 0` (`κ = ±1`), given
the Fuller data at `x̃₀` (`FullerSwitchData κ x₀ u₀`, in the physical rescaled time
`u = t/|r₀| = κ s`): the Fuller switching function `κ χ̃₂₁(κ u, 0, x̃₀)` is positive on `[0, u₀)`
and has a simple zero at `u₀ > 0`, the χ₂₃ check `κ χ̃₂₃(κ u, 0, x̃₀) > 0` holds on `(0, B]` for
some `B > u₀` with a positive slope at `u = 0`, and the `(1, 1)` coefficient of the image is
positive. "In similar way to what we have done" (Step 10, TeX 11864–11866) is a second
application of the same lemmas:

* **the forward map `F`** at `q_out`: `κ = 1`, `x̃₀ = x̃_out`, `u₀ = s_sw,out ≈ 8.84`
  (`fullerSwitchData_out`, from the exact Fuller cubic at `q_out`);
* **the backward map `F⁻¹`** at `q_out` ("the Reinhardt–Poincaré map `F⁻¹` that moves backwards in
  time"): by the time reversal, flowing `e₃` backwards from `lieChart (r, x̃)` is `τ` of flowing
  `e₂` forwards from `τ(lieChart (r, x̃)) = lieChart (-r, σ x̃)` (`iso_vertexFlow_reinTau`,
  `lieChart_chartReflect`), so `F⁻¹ = σ F σ` in the chart, and `F` near `(0, x̃_in)`,
  `x̃_in = σ x̃_out`, from the side `r < 0` is the instance `κ = -1`, `x̃₀ = x̃_in`,
  `u₀ = s_sw,out / r_scale ≈ 1.4094` (`fullerSwitchData_in`).

The Fuller data of the backward instance are derived from the forward ones, with no estimate at
`q_in`: `z(x̃_in) = -conj z(x̃_out)`, so the Fuller arc from `z(x̃_in)` is `-conj` of the backward
arc from `z(x̃_out)` with the control `ζ²`, which by the fixed point equation (13.5.2) is the
forward arc from `z(x̃_out)` read backwards from `s_sw,out` and rescaled by `1/r_scale`
(`flow_neg_xTildeOut`). Hence (`extChi21Zero_xTildeIn`, `extChi23Zero_xTildeIn`)
`-χ̃₂₁(-u, 0, x̃_in) = r_scale⁻³ χ̃₂₃(s_sw,out - r_scale u, 0, x̃_out)` and
`-χ̃₂₃(-u, 0, x̃_in) = r_scale⁻³ χ̃₂₁(s_sw,out - r_scale u, 0, x̃_out)`: the root `s = 0` of the
forward `χ̃₂₃ = s Q(s)` gives the simple root `u₀ = s_sw,out/r_scale` at `x̃_in`, and the simple
root `s_sw,out` of the forward `χ̃₂₁` gives the χ₂₃ check there. (The near-degenerate pairs of
roots of the Fuller switching functions from `τ(q_out)`, `1.6485 ± 0.0084 i` and the χ₂₃
near-tangency `1.5 ± 0.0529 i`, are the images under `s = (s_sw,out - s')/r_scale` of roots at
`q_out` at negative times, `-1.5 ± 0.054 i` and `-0.568 ± 0.332 i`; the construction needs the
signs only on `(0, u₀ + δ]`, where they come from the forward arc on `[-r_scale δ, s_sw,out]`.)

## Contents

* Steps 1–3, at every divisor point: `extFlowPt p`, the flow with the control `e₂` from the chart
  point `(r₀, x̃₀)` at time `s r₀`; `extChi i j p`, the switching function `χ_ij` there, analytic
  near `r₀ = 0` (`l6d_analyticAt_chiRaw`); `extDivPow f k v`, `f/r₀^k` extended by `v` at `r₀ = 0`,
  analytic when `f = r₀^k v + O(r₀^{k+1})` (`l6d_analyticAt_divR`, division of power series);
  `extChi21`, `extChi23` (`k = 3`, Lemma 14.2.4 and its χ₂₃ companion).
* Steps 6–7, at every divisor point: `extSwitchPt`, the image point `Ad_{R⁻¹} Y(s r₀)`; its divided
  entries `extDivA`, …, `extDivD` (from Lemma 14.2.3 and the determinant relations).
* Step 4: `FullerSwitchData`; the forward instance `fullerSwitchData_out` (the Fuller cubic at
  `x̃_out`: `l6d_g`, `l6d_g_factor`, `l6d_g'_T_neg`, `l6d_v21_xTildeOut`, `extChi23Zero_xTildeOut`,
  exact) and the backward instance `fullerSwitchData_in` (from the forward one, as above).
* Step 5, generic: `extSwitchTime h`, the analytic switching time (the analytic implicit function
  theorem), `extSwitchTime_zero_structure h` (it is the least positive zero near the divisor point;
  the χ₂₃ check `exists_extChi23_eq_mul h`, `eventually_extChi23_pos h`).
* Step 8, generic: the extended map `extMap h`, analytic at the divisor point
  (`analyticAt_extMap`), `lieChartInv` of the image point for `r₀ ≠ 0` (`extMap_eq_lieChartInv`),
  and its values on the divisor (`extMap_zero`).
* Step 9: for the forward instance, the Fuller–Poincaré map on the divisor
  (`eventually_extMap_divisor`, via `l6d_poincare_eq`); the backward instance fixes its base point
  (`extMap_in_base`).
-/

@[expose] public section

namespace SmoothedPolygons

open Complex Set Filter Topology Asymptotics
open TriFuller

attribute [local fun_prop] analyticAt_fst analyticAt_snd analyticAt_pi_apply

@[simp] lemma _root_.Complex.re_ofReal_pow (r : ℝ) (n : ℕ) : ((r : ℂ) ^ n).re = r ^ n := by
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

@[simp] lemma _root_.Complex.im_ofReal_pow (r : ℝ) (n : ℕ) : ((r : ℂ) ^ n).im = 0 := by
  rw [← Complex.ofReal_pow, Complex.ofReal_im]

/-! ### The flow from the chart, in rescaled time -/

/-- The flow with the control `e₂` from the chart point `(r₀, x̃₀)` at time `s r₀`
(`p = (s, r₀, x̃₀)`). -/
noncomputable def extFlowPt (p : ℝ × ℝ × (Fin 3 → ℝ)) : iso_PhasePt :=
  iso_vertexFlow 1 (lieChart (p.2.1, p.2.2)) (p.1 * p.2.1)

/-- The switching function `χ_ij` along the flow, at `extFlowPt p`. -/
noncomputable def extChi (i j : Fin 3) (p : ℝ × ℝ × (Fin 3 → ℝ)) : ℝ :=
  switchingFn i j (extFlowPt p).2.2 (extFlowPt p).1

private lemma l6d_lieChart_zero (x : Fin 3 → ℝ) :
    lieChart (0, x) = (J, (-(3 / 2) : ℝ) • J, 0) := by
  have hX : lieX 0 (x 0) = J := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [lieX, J]
  have hΛ : lieΛ₁ 0 (x 1) (x 2) = (-(3 / 2) : ℝ) • J := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [lieΛ₁, J]
  have hh : reducedHam ((-(3 / 2) : ℝ) • J) J = 0 := by
    simp [reducedHam, traceForm, J, Matrix.trace_fin_two]
  simp only [lieChart, hX, hΛ, lieΛR, sl2Dual, hh, mul_zero, zero_smul, add_zero, smul_zero]

private lemma l6d_flowPt_zero (s : ℝ) (x : Fin 3 → ℝ) :
    extFlowPt (s, 0, x) = (J, (-(3 / 2) : ℝ) • J, 0) := by
  simp only [extFlowPt, mul_zero, ivf_vertexFlow_zero, l6d_lieChart_zero]

/-- The coordinates `(s, r₀, x̃₀) ↦ (r₀, x̃₀)` are analytic. -/
private lemma l6d_analyticAt_chartCoord (p : ℝ × ℝ × (Fin 3 → ℝ)) :
    AnalyticAt ℝ (fun p : ℝ × ℝ × (Fin 3 → ℝ) ↦ (p.2.1, p.2.2)) p := by
  fun_prop

/-- The flow from the chart is analytic near `r₀ = 0` (Steps 1–2 of Lemma 14.3.1). -/
private lemma l6d_MatAn_flowPt (s : ℝ) (x : Fin 3 → ℝ) :
    EntrywiseAnalyticAt (fun p ↦ (extFlowPt p).1) (s, 0, x) ∧
      EntrywiseAnalyticAt (fun p ↦ (extFlowPt p).2.1) (s, 0, x) ∧
      EntrywiseAnalyticAt (fun p ↦ (extFlowPt p).2.2) (s, 0, x) := by
  obtain ⟨h1, h2, h3⟩ := entrywiseAnalyticAt_lieChart (l6d_analyticAt_chartCoord (s, 0, x))
    (by simp) (by norm_num)
  refine entrywiseAnalyticAt_vertexFlow 1 h1 h2 h3 (by fun_prop) ?_
  simp only [l6d_lieChart_zero, traceForm_controlMatrix_vertex_J]
  norm_num

/-- The switching functions along the flow from the chart are analytic near `r₀ = 0`. -/
private lemma l6d_analyticAt_chiRaw (i j : Fin 3) (s : ℝ) (x : Fin 3 → ℝ) :
    AnalyticAt ℝ (extChi i j) (s, 0, x) := by
  obtain ⟨h1, -, h3⟩ := l6d_MatAn_flowPt s x
  have hZ : ∀ k : Fin 3, traceForm (controlMatrix (vertex k)) (extFlowPt (s, 0, x)).1 ≠ 0 := by
    intro k; rw [l6d_flowPt_zero, traceForm_controlMatrix_vertex_J]; norm_num
  exact h3.traceForm ((EntrywiseAnalyticAt.controlP j h1 (hZ j)).sub (EntrywiseAnalyticAt.controlP i
      h1 (hZ i)))

/-! ### Division by `r₀³` (Step 3) -/

/-- `χ_ij/r₀³`, extended at `r₀ = 0` by the value `v (s, x̃₀)`. -/
noncomputable def extChiDiv (i j : Fin 3) (v : ℝ × (Fin 3 → ℝ) → ℝ)
    (p : ℝ × ℝ × (Fin 3 → ℝ)) : ℝ :=
  if p.2.1 = 0 then v (p.1, p.2.2) else extChi i j p / p.2.1 ^ 3

/-- The reordering `(r₀, (s, x̃₀)) ↦ (s, r₀, x̃₀)` of the coordinates. -/
private def l6d_swap (p : ℝ × ℝ × (Fin 3 → ℝ)) : ℝ × ℝ × (Fin 3 → ℝ) := (p.2.1, p.1, p.2.2)

private lemma l6d_analyticAt_swap (p : ℝ × ℝ × (Fin 3 → ℝ)) : AnalyticAt ℝ l6d_swap p := by
  unfold l6d_swap; fun_prop

private lemma l6d_swap_swap (p : ℝ × ℝ × (Fin 3 → ℝ)) : l6d_swap (l6d_swap p) = p := rfl

/-- If `f(r) = r^k c + O(r^{k+1})` as `r → 0⁺`, then `f(r)/r^k → c`. -/
private lemma l6d_tendsto_div_pow {f : ℝ → ℝ} {c : ℝ} {k : ℕ}
    (h : (fun r ↦ f r - r ^ k * c) =O[𝓝[>] 0] (fun r ↦ r ^ (k + 1))) :
    Tendsto (fun r ↦ f r / r ^ k) (𝓝[>] 0) (𝓝 c) := by
  rw [← tendsto_sub_nhds_zero_iff]
  have h1 : (fun r ↦ (f r - r ^ k * c) * (r ^ k)⁻¹) =O[𝓝[>] 0]
      (fun r ↦ r ^ (k + 1) * (r ^ k)⁻¹) :=
    h.mul (isBigO_refl _ _)
  have h2 : (fun r : ℝ ↦ r ^ (k + 1) * (r ^ k)⁻¹) =ᶠ[𝓝[>] 0] fun r ↦ r := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr' : r ≠ 0 := ne_of_gt hr
    field_simp
    ring
  have h3 : (fun r ↦ f r / r ^ k - c) =ᶠ[𝓝[>] 0] fun r ↦ (f r - r ^ k * c) * (r ^ k)⁻¹ := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr' : r ≠ 0 := ne_of_gt hr
    field_simp
  refine ((h1.congr' h3.symm h2).trans_tendsto ?_)
  exact tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto' 0 0 rfl)

/-- `f/r₀^k`, extended at `r₀ = 0` by the value `v (s, x̃₀)`. -/
noncomputable def extDivPow (f : ℝ × ℝ × (Fin 3 → ℝ) → ℝ) (k : ℕ) (v : ℝ × (Fin 3 → ℝ) → ℝ)
    (p : ℝ × ℝ × (Fin 3 → ℝ)) : ℝ :=
  if p.2.1 = 0 then v (p.1, p.2.2) else f p / p.2.1 ^ k

private lemma l6d_divR_zero (f : ℝ × ℝ × (Fin 3 → ℝ) → ℝ) (k : ℕ) (v : ℝ × (Fin 3 → ℝ) → ℝ) (s : ℝ)
    (x : Fin 3 → ℝ) : extDivPow f k v (s, 0, x) = v (s, x) := by
  simp [extDivPow]

lemma eq_pow_mul_extDivPow (f : ℝ × ℝ × (Fin 3 → ℝ) → ℝ) (k : ℕ) (v : ℝ × (Fin 3 → ℝ) → ℝ)
    {p : ℝ × ℝ × (Fin 3 → ℝ)} (hp : p.2.1 ≠ 0) : f p = p.2.1 ^ k * extDivPow f k v p := by
  simp only [extDivPow, hp, ite_false]
  field_simp

/-- **Division of power series** (Step 3 of Lemma 14.3.1, TeX 11800–11806, and Step 7,
TeX 11846–11848): if `f` is analytic near `r₀ = 0` and `f(s, r₀, x̃₀) = r₀^k v(s, x̃₀) +
O(r₀^{k+1})` as `r₀ → 0⁺` for each `(s, x̃₀)`, then `f/r₀^k`, extended by `v` at `r₀ = 0`, is
analytic near every point of `r₀ = 0`. -/
private lemma l6d_analyticAt_divR {f : ℝ × ℝ × (Fin 3 → ℝ) → ℝ} (hf : ∀ s x, AnalyticAt ℝ f (s, 0,
    x))
    (k : ℕ) {v : ℝ × (Fin 3 → ℝ) → ℝ}
    (hv : ∀ s x, (fun r ↦ f (s, r, x) - r ^ k * v (s, x)) =O[𝓝[>] 0] (fun r ↦ r ^ (k + 1)))
    (s : ℝ) (x : Fin 3 → ℝ) :
    AnalyticAt ℝ (extDivPow f k v) (s, 0, x) := by
  -- the function with the coordinate `r₀` first
  set F : ℝ × ℝ × (Fin 3 → ℝ) → ℝ := fun p ↦ f (l6d_swap p) with hFdef
  have hF : ∀ s' x', AnalyticAt ℝ F (0, s', x') := fun s' x' ↦
    (hf s' x').comp_of_eq (l6d_analyticAt_swap _) rfl
  have hO : ∀ s' x', (fun r ↦ F (r, s', x')) =O[𝓝 0] (fun r ↦ r ^ k) := by
    intro s' x'
    have han : AnalyticAt ℝ (fun r ↦ F (r, s', x')) 0 :=
      (hF s' x').comp_of_eq (by fun_prop : AnalyticAt ℝ (fun r : ℝ ↦ (r, s', x')) 0) rfl
    refine AnalyticAt.isBigO_nhds_of_isBigO_nhdsGT han ?_
    have h4 : (fun r : ℝ ↦ r ^ (k + 1)) =O[𝓝[>] 0] (fun r ↦ r ^ k) :=
      ((isLittleO_pow_pow (by omega : k < k + 1)).isBigO).mono nhdsWithin_le_nhds
    have h3 : (fun r : ℝ ↦ r ^ k * v (s', x')) =O[𝓝[>] 0] (fun r ↦ r ^ k) := by
      simpa [mul_comm] using
        (isBigO_refl (fun r : ℝ ↦ r ^ k) (𝓝[>] 0)).const_mul_left (v (s', x'))
    simpa [F, l6d_swap] using ((hv s' x').trans h4).add h3
  obtain ⟨g, hg, hfg⟩ := AnalyticAt.exists_eq_pow_smul_of_isBigO (hF s x)
    (Eventually.of_forall fun y ↦ hO y.1 y.2)
  obtain ⟨U, hUsub, hUo, hU0⟩ := eventually_nhds_iff.1 (hfg.and hg.eventually_analyticAt)
  -- the value at `r₀ = 0`
  have hval : ∀ s' x', ((0 : ℝ), s', x') ∈ U → g (0, s', x') = v (s', x') := by
    intro s' x' hmem
    have hc : ContinuousAt (fun r : ℝ ↦ g (r, s', x')) 0 :=
      ((hUsub _ hmem).2.continuousAt).comp_of_eq
        (by fun_prop : ContinuousAt (fun r : ℝ ↦ (r, s', x')) 0) rfl
    have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), g (r, s', x') = f (s', r, x') / r ^ k := by
      have hU' : ∀ᶠ r in 𝓝 (0 : ℝ), (r, s', x') ∈ U :=
        (by fun_prop : ContinuousAt (fun r : ℝ ↦ (r, s', x')) 0).preimage_mem_nhds
          (hUo.mem_nhds hmem)
      filter_upwards [nhdsWithin_le_nhds hU', self_mem_nhdsWithin] with r hr hr0
      have hr0' : r ≠ 0 := ne_of_gt hr0
      have := (hUsub _ hr).1
      simp only [F, l6d_swap, smul_eq_mul] at this
      rw [this]
      field_simp
    have hlim := (l6d_tendsto_div_pow (hv s' x')).congr' (hev.mono fun r h ↦ h.symm)
    exact tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds) hlim
  have hev : extDivPow f k v =ᶠ[𝓝 (s, 0, x)] fun p ↦ g (l6d_swap p) := by
    have hpre : l6d_swap ⁻¹' U ∈ 𝓝 (s, 0, x) :=
      (l6d_analyticAt_swap (s, 0, x)).continuousAt.preimage_mem_nhds (hUo.mem_nhds hU0)
    filter_upwards [hpre] with p hp
    obtain ⟨s', r', x'⟩ := p
    simp only [mem_preimage, l6d_swap] at hp
    by_cases hr : r' = 0
    · subst hr
      simp only [extDivPow, l6d_swap, ite_true]
      exact (hval s' x' hp).symm
    · have := (hUsub _ hp).1
      simp only [F, l6d_swap, smul_eq_mul] at this
      simp only [extDivPow, hr, ite_false, l6d_swap, this]
      field_simp
  exact (hg.comp_of_eq (l6d_analyticAt_swap _) rfl).congr hev.symm

lemma analyticAt_extChiDiv (i j : Fin 3) {v : ℝ × (Fin 3 → ℝ) → ℝ}
    (hv : ∀ s x, (fun r ↦ extChi i j (s, r, x) - r ^ 3 * v (s, x)) =O[𝓝[>] 0]
      (fun r ↦ r ^ 4)) (s : ℝ) (x : Fin 3 → ℝ) :
    AnalyticAt ℝ (extChiDiv i j v) (s, 0, x) :=
  l6d_analyticAt_divR (l6d_analyticAt_chiRaw i j) 3 hv s x

/-! ### The rescaled switching functions `χ̃₂₁`, `χ̃₂₃` -/

/-- The limit `24 RR(ζ - 1, z₃(s))` of `χ₂₁/r₀³` (Lemma 14.2.4). -/
noncomputable def extChi21Zero (p : ℝ × (Fin 3 → ℝ)) : ℝ :=
  24 * RR (ζ - 1) (flow p.1 (fullerOfChart p.2) ζ 2)

/-- The limit `24 RR(ζ - ζ², z₃(s))` of `χ₂₃/r₀³` (the χ₂₃ companion of Lemma 14.2.4). -/
noncomputable def extChi23Zero (p : ℝ × (Fin 3 → ℝ)) : ℝ :=
  24 * RR (ζ - ζ ^ 2) (flow p.1 (fullerOfChart p.2) ζ 2)

/-- `χ̃₂₁(s, r₀, x̃₀) = χ₂₁/r₀³`, extended analytically to `r₀ = 0`. -/
noncomputable def extChi21 : ℝ × ℝ × (Fin 3 → ℝ) → ℝ := extChiDiv 1 0 extChi21Zero

/-- `χ̃₂₃(s, r₀, x̃₀) = χ₂₃/r₀³`, extended analytically to `r₀ = 0`. -/
noncomputable def extChi23 : ℝ × ℝ × (Fin 3 → ℝ) → ℝ := extChiDiv 1 2 extChi23Zero

private lemma l6d_analyticAt_chi21 (s : ℝ) (x : Fin 3 → ℝ) : AnalyticAt ℝ extChi21 (s, 0, x) := by
  refine analyticAt_extChiDiv 1 0 (fun s x ↦ ?_) s x
  refine (lemma14_2_4 x s).congr_left fun r ↦ ?_
  simp only [extChi, extFlowPt, extChi21Zero]
  ring

lemma analyticAt_extChi23 (s : ℝ) (x : Fin 3 → ℝ) : AnalyticAt ℝ extChi23 (s, 0, x) := by
  refine analyticAt_extChiDiv 1 2 (fun s x ↦ ?_) s x
  refine (lemma14_2_4_chi23 x s).congr_left fun r ↦ ?_
  simp only [extChi, extFlowPt, extChi23Zero]
  ring

private lemma l6d_chi21_zero (s : ℝ) (x : Fin 3 → ℝ) : extChi21 (s, 0, x) = extChi21Zero (s, x) :=
    by
  simp [extChi21, extChiDiv]

lemma extChi23_zero (s : ℝ) (x : Fin 3 → ℝ) : extChi23 (s, 0, x) = extChi23Zero (s, x) := by
  simp [extChi23, extChiDiv]

lemma extChi_eq_extChi21 {p : ℝ × ℝ × (Fin 3 → ℝ)} (hp : p.2.1 ≠ 0) :
    extChi 1 0 p = p.2.1 ^ 3 * extChi21 p := by
  simp only [extChi21, extChiDiv, hp, ite_false]
  field_simp

lemma extChi_eq_extChi23 {p : ℝ × ℝ × (Fin 3 → ℝ)} (hp : p.2.1 ≠ 0) :
    extChi 1 2 p = p.2.1 ^ 3 * extChi23 p := by
  simp only [extChi23, extChiDiv, hp, ite_false]
  field_simp

/-! ### The image point and its divided entries (Steps 6–7) -/

/-- The flow point rotated by `Ad_{R⁻¹}`, `Y_sw = Ad_{R⁻¹} Y(s r₀)` at `s = s_sw` (Step 6). -/
noncomputable def extSwitchPt (p : ℝ × ℝ × (Fin 3 → ℝ)) : iso_PhasePt :=
  iso_adRinvPow 1 (extFlowPt p)

/-- The entries of `X_sw - J` and `Λ₁sw + (3/2) J` read off by the chart and the determinant
relations. -/
noncomputable def extEntryA (p : ℝ × ℝ × (Fin 3 → ℝ)) : ℝ := (extSwitchPt p).1 0 0
noncomputable def extEntryB (p : ℝ × ℝ × (Fin 3 → ℝ)) : ℝ := (extSwitchPt p).1 1 0 - 1
private noncomputable def l6d_fe (p : ℝ × ℝ × (Fin 3 → ℝ)) : ℝ := (extSwitchPt p).1 0 1 + 1
noncomputable def extEntryC (p : ℝ × ℝ × (Fin 3 → ℝ)) : ℝ := (extSwitchPt p).2.1 0 0
noncomputable def extEntryD (p : ℝ × ℝ × (Fin 3 → ℝ)) : ℝ := (extSwitchPt p).2.1 1 0 + 3 / 2
private noncomputable def l6d_ff (p : ℝ × ℝ × (Fin 3 → ℝ)) : ℝ := (extSwitchPt p).2.1 0 1 - 3 / 2

/-- `w(s, x̃) = ζ z(s, z(x̃), ζ)`, the rotated Fuller flow. -/
noncomputable def extFullerFlow (q : ℝ × (Fin 3 → ℝ)) : Fin 3 → ℂ :=
    ζ • flow q.1 (fullerOfChart q.2) ζ

/-- The limits of the divided entries: `2 Im w₁`, `2 Re w₁`, `6 Re w₂`, `-6 Im w₂`. -/
noncomputable def extLimitA (q : ℝ × (Fin 3 → ℝ)) : ℝ := 2 * (extFullerFlow q 0).im
noncomputable def extLimitB (q : ℝ × (Fin 3 → ℝ)) : ℝ := 2 * (extFullerFlow q 0).re
noncomputable def extLimitC (q : ℝ × (Fin 3 → ℝ)) : ℝ := 6 * (extFullerFlow q 1).re
noncomputable def extLimitD (q : ℝ × (Fin 3 → ℝ)) : ℝ := -(6 * (extFullerFlow q 1).im)

lemma entrywiseAnalyticAt_extSwitchPt (s : ℝ) (x : Fin 3 → ℝ) :
    EntrywiseAnalyticAt (fun p ↦ (extSwitchPt p).1) (s, 0, x) ∧ EntrywiseAnalyticAt (fun p ↦
        (extSwitchPt p).2.1) (s, 0, x) := by
  obtain ⟨h1, h2, -⟩ := l6d_MatAn_flowPt s x
  simp only [extSwitchPt, iso_adRinvPow, pow_one]
  exact ⟨((EntrywiseAnalyticAt.const _).mul h1).mul (EntrywiseAnalyticAt.const _),
    ((EntrywiseAnalyticAt.const _).mul h2).mul (EntrywiseAnalyticAt.const _)⟩

lemma Rinv_mul_J_mul_R : R⁻¹ * J * R = J := by
  rw [Matrix.mul_assoc, poly_J_mul_R, ← Matrix.mul_assoc, poly_inv_mul_R, Matrix.one_mul]

lemma extSwitchPt_zero (s : ℝ) (x : Fin 3 → ℝ) :
    extSwitchPt (s, 0, x) = (J, (-(3 / 2) : ℝ) • J, 0) := by
  simp only [extSwitchPt, l6d_flowPt_zero, iso_adRinvPow, pow_one, Matrix.mul_smul, Matrix.smul_mul,
    Rinv_mul_J_mul_R, Matrix.mul_zero, Matrix.zero_mul]

private lemma l6d_analyticAt_entries (s : ℝ) (x : Fin 3 → ℝ) :
    AnalyticAt ℝ extEntryA (s, 0, x) ∧ AnalyticAt ℝ extEntryB (s, 0, x) ∧
      AnalyticAt ℝ l6d_fe (s, 0, x) ∧ AnalyticAt ℝ extEntryC (s, 0, x) ∧
      AnalyticAt ℝ extEntryD (s, 0, x) ∧ AnalyticAt ℝ l6d_ff (s, 0, x) := by
  obtain ⟨h1, h2⟩ := entrywiseAnalyticAt_extSwitchPt s x
  exact ⟨h1 0 0, (h1 1 0).sub analyticAt_const, (h1 0 1).add analyticAt_const, h2 0 0,
    (h2 1 0).add analyticAt_const, (h2 0 1).sub analyticAt_const⟩

private lemma l6d_entries_zero (s : ℝ) (x : Fin 3 → ℝ) :
    extEntryA (s, 0, x) = 0 ∧ extEntryB (s, 0, x) = 0 ∧ l6d_fe (s, 0, x) = 0 ∧
      extEntryC (s, 0, x) = 0 ∧ extEntryD (s, 0, x) = 0 ∧ l6d_ff (s, 0, x) = 0 := by
  simp only [extEntryA, extEntryB, l6d_fe, extEntryC, extEntryD, l6d_ff, extSwitchPt_zero]
  simp [J]

/-- The chart takes values in `𝔰𝔩₂(ℝ)³`. -/
private lemma l6d_lieChart_traceless (p : ℝ × (Fin 3 → ℝ)) :
    (lieChart p).1.trace = 0 ∧ (lieChart p).2.1.trace = 0 ∧ (lieChart p).2.2.trace = 0 := by
  refine ⟨by simp [lieChart, lieX, Matrix.trace_fin_two], by simp [lieChart, lieΛ₁,
    Matrix.trace_fin_two], ?_⟩
  simp only [lieChart, lieΛR, sl2Dual, Matrix.trace_smul, Matrix.trace_add, irt_trace_bracket,
    smul_zero, add_zero]

lemma extFlowPt_traceless (p : ℝ × ℝ × (Fin 3 → ℝ)) :
    (extFlowPt p).1.trace = 0 ∧ (extFlowPt p).2.1.trace = 0 ∧ (extFlowPt p).2.2.trace = 0 := by
  obtain ⟨h1, h2, h3⟩ := l6d_lieChart_traceless (p.2.1, p.2.2)
  exact irt_vertexFlow_traceless 1 h1 h2 h3 _

/-- The Fuller coordinates of the image point: `ẑ(Y_sw) = ζ ẑ(Y(s r₀))`. -/
private lemma l6d_fullerCoords_Xi (p : ℝ × ℝ × (Fin 3 → ℝ)) :
    fullerCoords (extSwitchPt p) = ζ • fullerCoords (extFlowPt p) := by
  obtain ⟨h1, h2, h3⟩ := extFlowPt_traceless p
  exact (fullerCoords_adR (extFlowPt p) h1 h2 h3).2

private lemma l6d_fullerCoords_Xi_zero (p : ℝ × ℝ × (Fin 3 → ℝ)) :
    (fullerCoords (extSwitchPt p) 0).im = extEntryA p / 2 ∧
      (fullerCoords (extSwitchPt p) 0).re = (l6d_fe p + extEntryB p) / 4 := by
  constructor
  · simp only [fullerCoords, cayleyZ, Fin.isValue, neg_mul, Matrix.cons_val_zero, div_ofNat_im,
      extEntryA]
  · simp only [fullerCoords, cayleyZ, Fin.isValue, neg_mul, Matrix.cons_val_zero, div_ofNat_re,
      l6d_fe, extEntryB, add_add_sub_cancel]
    ring

private lemma l6d_fullerCoords_Xi_one (p : ℝ × ℝ × (Fin 3 → ℝ)) :
    (fullerCoords (extSwitchPt p) 1).re = extEntryC p / 6 ∧
      (fullerCoords (extSwitchPt p) 1).im = -(l6d_ff p + extEntryD p) / 12 := by
  constructor
  · simp only [fullerCoords, cayleyZ, Fin.isValue, neg_mul, Matrix.cons_val_one,
      Matrix.cons_val_zero, div_ofNat_re, neg_re, mul_re, I_re, zero_mul, I_im, one_mul, zero_sub,
      neg_neg, extEntryC]
  · simp only [fullerCoords, cayleyZ, Fin.isValue, neg_mul, Matrix.cons_val_one,
      Matrix.cons_val_zero, div_ofNat_im, neg_im, mul_im, I_re, zero_mul, I_im, one_mul, zero_add,
      l6d_ff, extEntryD, sub_add_add_cancel, neg_add_rev]
    ring

/-- Lemma 14.2.3, rotated: `ẑ_k(Y_sw) = r₀^{k+1} w_k(s) + O(r₀^{k+2})`. -/
private lemma l6d_isBigO_fullerCoords_Xi (s : ℝ) (x : Fin 3 → ℝ) (k : Fin 3) :
    (fun r : ℝ ↦ fullerCoords (extSwitchPt (s, r, x)) k - (r : ℂ) ^ (k.val + 1) * extFullerFlow (s,
        x) k)
      =O[𝓝[>] 0] (fun r ↦ r ^ (k.val + 2)) := by
  have h := (lemma14_2_3 x s k).const_mul_left ζ
  refine h.congr_left fun r ↦ ?_
  simp only [l6d_fullerCoords_Xi, extFullerFlow, Pi.smul_apply, smul_eq_mul, extFlowPt]
  ring

/-- A real part (or imaginary part) of `O(g)` is `O(g)`. -/
private lemma l6d_isBigO_re {f : ℝ → ℂ} {g : ℝ → ℝ} {l : Filter ℝ} (h : f =O[l] g) :
    (fun r ↦ (f r).re) =O[l] g :=
  (isBigO_of_le l fun r ↦ by
    simpa [Real.norm_eq_abs] using Complex.abs_re_le_norm (f r)).trans h

private lemma l6d_isBigO_im {f : ℝ → ℂ} {g : ℝ → ℝ} {l : Filter ℝ} (h : f =O[l] g) :
    (fun r ↦ (f r).im) =O[l] g :=
  (isBigO_of_le l fun r ↦ by
    simpa [Real.norm_eq_abs] using Complex.abs_im_le_norm (f r)).trans h

private lemma l6d_isBigO_fa (s : ℝ) (x : Fin 3 → ℝ) :
    (fun r ↦ extEntryA (s, r, x) - r ^ 1 * extLimitA (s, x)) =O[𝓝[>] 0] (fun r ↦ r ^ 2) := by
  have h := (l6d_isBigO_im (l6d_isBigO_fullerCoords_Xi s x 0)).const_mul_left 2
  refine h.congr_left fun r ↦ ?_
  have := (l6d_fullerCoords_Xi_zero (s, r, x)).1
  simp only [Fin.val_zero, zero_add, pow_one, Complex.sub_im, Complex.im_ofReal_mul] at this ⊢
  rw [this, extLimitA]
  ring

private lemma l6d_isBigO_feb (s : ℝ) (x : Fin 3 → ℝ) :
    (fun r ↦ l6d_fe (s, r, x) + extEntryB (s, r, x) - r * (2 * extLimitB (s, x))) =O[𝓝[>] 0]
      (fun r ↦ r ^ 2) := by
  have h := (l6d_isBigO_re (l6d_isBigO_fullerCoords_Xi s x 0)).const_mul_left 4
  refine h.congr_left fun r ↦ ?_
  have := (l6d_fullerCoords_Xi_zero (s, r, x)).2
  simp only [Fin.val_zero, zero_add, pow_one, Complex.sub_re, Complex.re_ofReal_mul] at this ⊢
  rw [this, extLimitB]
  ring

private lemma l6d_isBigO_fc (s : ℝ) (x : Fin 3 → ℝ) :
    (fun r ↦ extEntryC (s, r, x) - r ^ 2 * extLimitC (s, x)) =O[𝓝[>] 0] (fun r ↦ r ^ 3) := by
  have h := (l6d_isBigO_re (l6d_isBigO_fullerCoords_Xi s x 1)).const_mul_left 6
  refine h.congr_left fun r ↦ ?_
  have := (l6d_fullerCoords_Xi_one (s, r, x)).1
  simp only [Fin.val_one, Complex.sub_re] at this ⊢
  rw [← Complex.ofReal_pow, Complex.re_ofReal_mul, this, extLimitC]
  ring

private lemma l6d_isBigO_ffd (s : ℝ) (x : Fin 3 → ℝ) :
    (fun r ↦ l6d_ff (s, r, x) + extEntryD (s, r, x) - r ^ 2 * (2 * extLimitD (s, x))) =O[𝓝[>] 0]
      (fun r ↦ r ^ 3) := by
  have h := (l6d_isBigO_im (l6d_isBigO_fullerCoords_Xi s x 1)).const_mul_left (-12)
  refine h.congr_left fun r ↦ ?_
  have := (l6d_fullerCoords_Xi_one (s, r, x)).2
  simp only [Fin.val_one, Complex.sub_im] at this ⊢
  rw [← Complex.ofReal_pow, Complex.im_ofReal_mul, this, extLimitD]
  ring

/-- The determinant relations on the image point (`det X = 1`, `det Λ₁ = 9/4`, traceless). -/
private lemma l6d_det_relations (p : ℝ × ℝ × (Fin 3 → ℝ)) (h1 : 1 + p.2.1 * p.2.2 0 ≠ 0)
    (h2 : 3 / 2 - p.2.1 ^ 2 * p.2.2 2 ≠ 0) :
    extEntryB p - l6d_fe p = extEntryA p ^ 2 + l6d_fe p * extEntryB p ∧
      3 / 2 * (l6d_ff p - extEntryD p) = extEntryC p ^ 2 + l6d_ff p * extEntryD p := by
  obtain ⟨t1, t2, -⟩ := extFlowPt_traceless p
  have hdX : (extSwitchPt p).1.det = 1 := by
    simp only [extSwitchPt, iso_adRinvPow, pow_one]
    rw [poly_det_conj poly_R_mul_inv, extFlowPt, det_vertexFlow_fst]
    simp only [lieChart, lieX, Matrix.det_fin_two_of]
    field_simp
    ring
  have hdΛ : (extSwitchPt p).2.1.det = 9 / 4 := by
    simp only [extSwitchPt, iso_adRinvPow, pow_one]
    rw [poly_det_conj poly_R_mul_inv, extFlowPt, det_vertexFlow_snd]
    simp only [lieChart, lieΛ₁, Matrix.det_fin_two_of]
    rw [show (-(3 / 2) + p.2.1 ^ 2 * p.2.2 2) = -(3 / 2 - p.2.1 ^ 2 * p.2.2 2) by ring]
    generalize 3 / 2 - p.2.1 ^ 2 * p.2.2 2 = D at h2 ⊢
    field_simp
    ring
  have htX : (extSwitchPt p).1.trace = 0 := by
    simp only [extSwitchPt, iso_adRinvPow, pow_one]
    rw [poly_trace_conj poly_R_mul_inv, t1]
  have htΛ : (extSwitchPt p).2.1.trace = 0 := by
    simp only [extSwitchPt, iso_adRinvPow, pow_one]
    rw [poly_trace_conj poly_R_mul_inv, t2]
  rw [Matrix.trace_fin_two] at htX htΛ
  rw [Matrix.det_fin_two] at hdX hdΛ
  simp only [extEntryA, extEntryB, l6d_fe, extEntryC, extEntryD, l6d_ff]
  constructor
  · have : (extSwitchPt p).1 1 1 = -(extSwitchPt p).1 0 0 := by linarith
    rw [this] at hdX
    linear_combination hdX
  · have : (extSwitchPt p).2.1 1 1 = -(extSwitchPt p).2.1 0 0 := by linarith
    rw [this] at hdΛ
    linear_combination hdΛ

/-- If `v (κ + v/4) = w` with `v → 0` and `w = O(g)`, then `v = O(g)`. -/
private lemma l6d_isBigO_of_quad {v w g : ℝ → ℝ} {κ : ℝ} (hκ : 0 < κ) (hv :
    Tendsto v (𝓝[>] 0) (𝓝 0))
    (h : ∀ᶠ r in 𝓝[>] 0, v r * (κ + v r / 4) = w r) (hw : w =O[𝓝[>] 0] g) :
    v =O[𝓝[>] 0] g := by
  refine (IsBigO.of_bound (2 / κ) ?_).trans hw
  filter_upwards [Metric.tendsto_nhds.1 hv (2 * κ) (by positivity), h] with r hr hrw
  rw [Real.dist_eq, sub_zero] at hr
  simp only [Real.norm_eq_abs]
  rw [← hrw, abs_mul]
  have hk : κ / 2 ≤ |κ + v r / 4| := by
    rw [abs_of_pos (by linarith [neg_abs_le (v r)])]
    linarith [neg_abs_le (v r)]
  calc |v r| = 2 / κ * (|v r| * (κ / 2)) := by field_simp
    _ ≤ 2 / κ * (|v r| * |κ + v r / 4|) := by gcongr

/-- `f = r^k c + O(r^{k+1})` implies `f = O(r^k)` as `r → 0⁺`. -/
private lemma l6d_isBigO_of_sub {f : ℝ → ℝ} {c : ℝ} {k : ℕ}
    (h : (fun r ↦ f r - r ^ k * c) =O[𝓝[>] 0] (fun r ↦ r ^ (k + 1))) :
    f =O[𝓝[>] 0] (fun r ↦ r ^ k) := by
  have h4 : (fun r : ℝ ↦ r ^ (k + 1)) =O[𝓝[>] 0] (fun r ↦ r ^ k) :=
    ((isLittleO_pow_pow (by omega : k < k + 1)).isBigO).mono nhdsWithin_le_nhds
  have h3 : (fun r : ℝ ↦ r ^ k * c) =O[𝓝[>] 0] (fun r ↦ r ^ k) := by
    simpa [mul_comm] using (isBigO_refl (fun r : ℝ ↦ r ^ k) (𝓝[>] 0)).const_mul_left c
  simpa using (h.trans h4).add h3

private lemma l6d_eventually_den (x : Fin 3 → ℝ) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), 1 + r * x 0 ≠ 0 ∧ 3 / 2 - r ^ 2 * x 2 ≠ 0 := by
  have h1 : ∀ᶠ r in 𝓝 (0 : ℝ), 1 + r * x 0 ≠ 0 :=
    (by fun_prop : ContinuousAt (fun r : ℝ ↦ 1 + r * x 0) 0).eventually_ne (by simp)
  have h2 : ∀ᶠ r in 𝓝 (0 : ℝ), 3 / 2 - r ^ 2 * x 2 ≠ 0 :=
    (by fun_prop : ContinuousAt (fun r : ℝ ↦ 3 / 2 - r ^ 2 * x 2) 0).eventually_ne (by norm_num)
  exact nhdsWithin_le_nhds (h1.and h2)

/-- An entry vanishing at `r₀ = 0` tends to `0` as `r₀ → 0⁺`. -/
private lemma l6d_tendsto_entry {f : ℝ × ℝ × (Fin 3 → ℝ) → ℝ} {s : ℝ} {x : Fin 3 → ℝ}
    (hf : AnalyticAt ℝ f (s, 0, x)) (h0 : f (s, 0, x) = 0) :
    Tendsto (fun r ↦ f (s, r, x)) (𝓝[>] 0) (𝓝 0) := by
  have hc : ContinuousAt (fun r : ℝ ↦ f (s, r, x)) 0 :=
    hf.continuousAt.comp_of_eq (by fun_prop) rfl
  have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  rwa [h0] at this

private lemma l6d_isBigO_fb (s : ℝ) (x : Fin 3 → ℝ) :
    (fun r ↦ extEntryB (s, r, x) - r ^ 1 * extLimitB (s, x)) =O[𝓝[>] 0] (fun r ↦ r ^ 2) := by
  obtain ⟨ha, hb, he, -, -, -⟩ := l6d_analyticAt_entries s x
  obtain ⟨ha0, hb0, he0, -, -, -⟩ := l6d_entries_zero s x
  have hu := l6d_isBigO_feb s x
  have hfa : (fun r ↦ extEntryA (s, r, x)) =O[𝓝[>] 0] (fun r ↦ r ^ 1) :=
    l6d_isBigO_of_sub (l6d_isBigO_fa s x)
  have hu1 : (fun r ↦ l6d_fe (s, r, x) + extEntryB (s, r, x)) =O[𝓝[>] 0] (fun r ↦ r ^ 1) :=
    l6d_isBigO_of_sub (c := 2 * extLimitB (s, x)) (by simpa using hu)
  have hw : (fun r ↦ extEntryA (s, r, x) ^ 2 + (l6d_fe (s, r, x) + extEntryB (s, r, x)) ^ 2 / 4)
      =O[𝓝[>] 0] (fun r ↦ r ^ 2) := by
    have h1 := hfa.mul hfa
    have h2 := (hu1.mul hu1).const_mul_left (1 / 4)
    refine (h1.add h2).congr (fun r ↦ by ring) (fun r ↦ by ring)
  have hv : Tendsto (fun r ↦ extEntryB (s, r, x) - l6d_fe (s, r, x)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (l6d_tendsto_entry hb hb0).sub (l6d_tendsto_entry he he0)
  have hq : ∀ᶠ r in 𝓝[>] (0 : ℝ), (extEntryB (s, r, x) - l6d_fe (s, r, x)) *
      (1 + (extEntryB (s, r, x) - l6d_fe (s, r, x)) / 4) =
        extEntryA (s, r, x) ^ 2 + (l6d_fe (s, r, x) + extEntryB (s, r, x)) ^ 2 / 4 := by
    filter_upwards [l6d_eventually_den x] with r ⟨h1, h2⟩
    have := (l6d_det_relations (s, r, x) h1 h2).1
    linear_combination this
  have hvO := l6d_isBigO_of_quad one_pos hv hq hw
  refine ((hu.const_mul_left (1 / 2)).add (hvO.const_mul_left (1 / 2))).congr_left fun r ↦ ?_
  ring

private lemma l6d_isBigO_fd (s : ℝ) (x : Fin 3 → ℝ) :
    (fun r ↦ extEntryD (s, r, x) - r ^ 2 * extLimitD (s, x)) =O[𝓝[>] 0] (fun r ↦ r ^ 3) := by
  obtain ⟨-, -, -, -, hd, hf⟩ := l6d_analyticAt_entries s x
  obtain ⟨-, -, -, -, hd0, hf0⟩ := l6d_entries_zero s x
  have hu := l6d_isBigO_ffd s x
  have hfc : (fun r ↦ extEntryC (s, r, x)) =O[𝓝[>] 0] (fun r ↦ r ^ 2) :=
    l6d_isBigO_of_sub (l6d_isBigO_fc s x)
  have hu1 : (fun r ↦ l6d_ff (s, r, x) + extEntryD (s, r, x)) =O[𝓝[>] 0] (fun r ↦ r ^ 2) :=
    l6d_isBigO_of_sub (c := 2 * extLimitD (s, x)) (by simpa using hu)
  have h43 : (fun r : ℝ ↦ r ^ 2 * r ^ 2) =O[𝓝[>] 0] (fun r ↦ r ^ 3) := by
    refine ((isLittleO_pow_pow (by norm_num : 3 < 4)).isBigO.mono nhdsWithin_le_nhds).congr_left
      fun r ↦ by ring
  have hw : (fun r ↦ extEntryC (s, r, x) ^ 2 + (l6d_ff (s, r, x) + extEntryD (s, r, x)) ^ 2 / 4)
      =O[𝓝[>] 0] (fun r ↦ r ^ 3) := by
    have h1 := (hfc.mul hfc).trans h43
    have h2 := ((hu1.mul hu1).trans h43).const_mul_left (1 / 4)
    refine (h1.add h2).congr_left (fun r ↦ by ring)
  have hv : Tendsto (fun r ↦ l6d_ff (s, r, x) - extEntryD (s, r, x)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (l6d_tendsto_entry hf hf0).sub (l6d_tendsto_entry hd hd0)
  have hq : ∀ᶠ r in 𝓝[>] (0 : ℝ), (l6d_ff (s, r, x) - extEntryD (s, r, x)) *
      (3 / 2 + (l6d_ff (s, r, x) - extEntryD (s, r, x)) / 4) =
        extEntryC (s, r, x) ^ 2 + (l6d_ff (s, r, x) + extEntryD (s, r, x)) ^ 2 / 4 := by
    filter_upwards [l6d_eventually_den x] with r ⟨h1, h2⟩
    have := (l6d_det_relations (s, r, x) h1 h2).2
    linear_combination this
  have hvO := l6d_isBigO_of_quad (by norm_num) hv hq hw
  refine ((hu.const_mul_left (1 / 2)).add (hvO.const_mul_left (-(1 / 2)))).congr_left fun r ↦ ?_
  ring

/-- The divided entries `(X_sw - J)₁₁/r₀`, `(X_sw - J)₂₁/r₀`, `(Λ₁sw + (3/2) J)₁₁/r₀²`,
`(Λ₁sw + (3/2) J)₂₁/r₀²` (Step 7, E85), analytic near `r₀ = 0`. -/
noncomputable def extDivA : ℝ × ℝ × (Fin 3 → ℝ) → ℝ := extDivPow extEntryA 1 extLimitA
noncomputable def extDivB : ℝ × ℝ × (Fin 3 → ℝ) → ℝ := extDivPow extEntryB 1 extLimitB
noncomputable def extDivC : ℝ × ℝ × (Fin 3 → ℝ) → ℝ := extDivPow extEntryC 2 extLimitC
noncomputable def extDivD : ℝ × ℝ × (Fin 3 → ℝ) → ℝ := extDivPow extEntryD 2 extLimitD

lemma analyticAt_extDiv (s : ℝ) (x : Fin 3 → ℝ) :
    AnalyticAt ℝ extDivA (s, 0, x) ∧ AnalyticAt ℝ extDivB (s, 0, x) ∧
      AnalyticAt ℝ extDivC (s, 0, x) ∧ AnalyticAt ℝ extDivD (s, 0, x) := by
  have h := l6d_analyticAt_entries
  exact ⟨l6d_analyticAt_divR (fun s x ↦ (h s x).1) 1 l6d_isBigO_fa s x,
    l6d_analyticAt_divR (fun s x ↦ (h s x).2.1) 1 l6d_isBigO_fb s x,
    l6d_analyticAt_divR (fun s x ↦ (h s x).2.2.2.1) 2 l6d_isBigO_fc s x,
    l6d_analyticAt_divR (fun s x ↦ (h s x).2.2.2.2.1) 2 l6d_isBigO_fd s x⟩

/-! ### The Fuller data at a divisor point (Step 4)

What Steps 5–9 use about the Fuller system at a divisor point `(0, x̃₀)`, on the side `κ r₀ > 0`
(`κ = ±1`), in the physical rescaled time `u = t/|r₀| = κ s`. -/

/-- `χ̃₂₃(0, 0, x̃) = 0`: `z(x̃)` lies on the wall between `ζ` and `ζ²` (`z₃(x̃)` is real). -/
lemma extChi23Zero_zero (x : Fin 3 → ℝ) : extChi23Zero (0, x) = 0 := by
  simp only [extChi23Zero, flow_zero]
  have : (fullerOfChart x 2).im = 0 := by simp [fullerOfChart]
  rw [RR_eq_re_mul_add_im_mul]
  simp [this, ζ_re, ζ_sq_re]

/-- **The Fuller switching data at a divisor point** `(0, x̃₀)` (Step 4, TeX 11807–11813: "the
least positive zero `s_sw,out ≈ 8.84 > 0` is a simple zero, and `s = 0` is not a zero"; the χ₂₃
check, E85; the scaling factor, TeX 11849–11856), on the side `κ r₀ > 0` (`κ = ±1`), in the
physical rescaled time `u = κ s`: the Fuller switching function `κ χ̃₂₁(κ u, 0, x̃₀)` is positive on
`[0, u₀)` and has a simple zero at `u₀ > 0` (derivative `< 0`); `κ χ̃₂₃(κ u, 0, x̃₀)` is positive on
`(0, B]` for some `B > u₀`, with a positive slope at `u = 0`; and the `(1, 1)` coefficient
`2 Im w₁` of the image, `w = ζ z(κ u₀, z(x̃₀), ζ)`, is positive. -/
structure FullerSwitchData (κ : ℝ) (x₀ : Fin 3 → ℝ) (u₀ : ℝ) : Prop where
  sign : κ = 1 ∨ κ = -1
  root_pos : 0 < u₀
  chi21_pos : ∀ u ∈ Ico 0 u₀, 0 < κ * extChi21Zero (κ * u, x₀)
  chi21_root : extChi21Zero (κ * u₀, x₀) = 0
  chi21_simple : ∃ D < 0, HasDerivAt (fun u ↦ κ * extChi21Zero (κ * u, x₀)) D u₀
  chi23_pos : ∃ B > u₀, ∀ u ∈ Ioc 0 B, 0 < κ * extChi23Zero (κ * u, x₀)
  chi23_slope : ∃ D > 0, HasDerivAt (fun u ↦ κ * extChi23Zero (κ * u, x₀)) D 0
  scale_pos : 0 < extLimitA (κ * u₀, x₀)

variable {κ : ℝ} {x₀ : Fin 3 → ℝ} {u₀ : ℝ}

lemma FullerSwitchData.mul_self (h : FullerSwitchData κ x₀ u₀) : κ * κ = 1 := by
  rcases h.sign with rfl | rfl <;> norm_num

private lemma l6s_ne_zero (hκ : κ * κ = 1) : κ ≠ 0 := by
  rintro rfl
  simp at hκ

private lemma l6s_mul_div (hκ : κ * κ = 1) (t r : ℝ) : κ * (t / (κ * r)) = t / r := by
  rw [← mul_div_assoc, mul_div_mul_left _ _ (l6s_ne_zero hκ)]

/-- A derivative in the physical time `u = κ s` is the derivative in `s` at `κ u`. -/
private lemma l6s_hasDerivAt_unsign (hκ : κ * κ = 1) {g : ℝ → ℝ} {D u : ℝ}
    (h : HasDerivAt (fun u ↦ κ * g (κ * u)) D u) : HasDerivAt g D (κ * u) := by
  have h1 : HasDerivAt (fun s : ℝ ↦ κ * s) κ (κ * u) := by
    simpa using (hasDerivAt_id (κ * u)).const_mul κ
  have h2 : HasDerivAt (fun u ↦ κ * g (κ * u)) D (κ * (κ * u)) := by
    rwa [← mul_assoc, hκ, one_mul]
  have h3 := (h2.comp (κ * u) h1).const_mul κ
  convert h3 using 1
  · funext s
    simp only [Function.comp, ← mul_assoc, hκ, one_mul]
  · linear_combination -D * hκ

/-! ### The forward instance: the Fuller cubic at `x̃_out` -/

/-- The virial equivariance of the Fuller flow with a constant control:
`z(λ τ, (λ z₁, λ² z₂, λ³ z₃), u) = (λ z₁(τ), λ² z₂(τ), λ³ z₃(τ))`. -/
private lemma l6d_flow_scale (l τ : ℝ) (z : Fin 3 → ℂ) (u : ℂ) :
    flow (l * τ) (scale l z) u = scale l (flow τ z u) := by
  funext i
  fin_cases i <;> simp [flow, scale] <;> ring

/-- The rescaling factor `λ = 1/(2 Im q_out,₁)` of Remark 14.2.1, between the normalizations of
Chapters 13 and 14 (E82). -/
noncomputable def virialScaleOut : ℝ := (2 * (qOutCart 0).im)⁻¹

lemma virialScaleOut_pos : 0 < virialScaleOut := inv_pos.2 (by linarith [qOutCart_signs.1])

/-- The first switching time `t_sw ≈ 7.40` of `q_out`. -/
noncomputable def tSwOut : ℝ := firstSwitchTime qOutCart

private lemma l6d_T_pos : 0 < tSwOut := by
  have := firstSwitchTime_qOutCart_bounds.1
  unfold tSwOut; linarith

/-- The rescaled switching time `s_sw,out = λ t_sw ≈ 8.84` at `x̃_out`. -/
noncomputable def sSwOut : ℝ := virialScaleOut * tSwOut

private lemma l6d_S_pos : 0 < sSwOut := mul_pos virialScaleOut_pos l6d_T_pos

/-- The coefficients of the cubic `g(τ) = RR(ζ - 1, z₃(τ, q_out, ζ))`. -/
noncomputable def outCubicCoeff0 : ℝ := -(3 / 2) * (qOutCart 2).re
private noncomputable def l6d_a1 : ℝ := -(3 / 2) * (qOutCart 1).re + √3 / 2 * (qOutCart 1).im
private noncomputable def l6d_a2 : ℝ := 3 / 4 + √3 / 4 * (qOutCart 0).im
noncomputable def outCubicCoeff3 : ℝ := -(√3 / 12)

/-- The Fuller switching function from `ζ` to `1` along the flow from `q_out` with control `ζ`. -/
private noncomputable def l6d_g (τ : ℝ) : ℝ :=
  outCubicCoeff0 + l6d_a1 * τ + l6d_a2 * τ ^ 2 + outCubicCoeff3 * τ ^ 3

private lemma l6d_RR_flow_qOut (τ : ℝ) : RR (ζ - 1) (flow τ qOutCart ζ 2) = l6d_g τ := by
  obtain ⟨h0, h2, -⟩ := qOutCart_normalization
  have hs : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [RR_eq_re_mul_add_im_mul]
  simp [flow, l6d_g, outCubicCoeff0, l6d_a1, l6d_a2, outCubicCoeff3, ζ_re, ζ_im, h0, h2]
  ring_nf

private lemma l6d_coeff_signs : 0 < outCubicCoeff0 ∧ 0 < l6d_a1 ∧ 0 < l6d_a2 ∧ outCubicCoeff3 < 0 :=
    by
  obtain ⟨-, -, h2⟩ := qOutCart_normalization
  obtain ⟨hy1, hx2, hy2⟩ := qOutCart_signs
  have hs : 0 < √3 := by positivity
  refine ⟨by unfold outCubicCoeff0; linarith, by unfold l6d_a1; nlinarith, by
      unfold l6d_a2; nlinarith,
    by unfold outCubicCoeff3; linarith⟩

private lemma l6d_g_T : l6d_g tSwOut = 0 := by
  have h := poincare_qOutCart
  rw [poincare, firstControl_qOutCart] at h
  have h2 := congrFun h 2
  rw [← l6d_RR_flow_qOut, tSwOut, h2]
  obtain ⟨-, hi, -⟩ := qOutCart_normalization
  have hs : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [RR_eq_re_mul_add_im_mul]
  simp [scale, ζ_re, ζ_im, ζ_sq_re, ζ_sq_im, hi]
  ring_nf
  rw [hs]
  ring

/-- `T³ g(τ) = (T - τ) B(τ)` with `B(τ) > 0` for `τ ≥ 0`. -/
private lemma l6d_g_factor (τ : ℝ) : tSwOut ^ 3 * l6d_g τ = (tSwOut - τ) * (outCubicCoeff0 *
    (tSwOut ^ 2 + tSwOut * τ + τ ^ 2) + l6d_a1 * τ * tSwOut * (tSwOut + τ) +
      l6d_a2 * τ ^ 2 * tSwOut ^ 2) := by
  have h := l6d_g_T
  unfold l6d_g at h ⊢
  linear_combination τ ^ 3 * h

private lemma l6d_g_factor_pos {τ : ℝ} (hτ : 0 ≤ τ) : 0 < outCubicCoeff0 *
    (tSwOut ^ 2 + tSwOut * τ + τ ^ 2) + l6d_a1 * τ * tSwOut * (tSwOut + τ) +
      l6d_a2 * τ ^ 2 * tSwOut ^ 2 := by
  obtain ⟨h0, h1, h2, -⟩ := l6d_coeff_signs
  have hT := l6d_T_pos
  have : 0 < tSwOut ^ 2 + tSwOut * τ + τ ^ 2 := by positivity
  have : 0 ≤ l6d_a1 * τ * tSwOut * (tSwOut + τ) := by positivity
  have : 0 ≤ l6d_a2 * τ ^ 2 * tSwOut ^ 2 := by positivity
  nlinarith

private lemma l6d_g_pos {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ < tSwOut) : 0 < l6d_g τ := by
  have h := l6d_g_factor τ
  have hB := l6d_g_factor_pos h0
  have hT3 : 0 < tSwOut ^ 3 := pow_pos l6d_T_pos 3
  have : 0 < tSwOut ^ 3 * l6d_g τ := by rw [h]; exact mul_pos (by linarith) hB
  exact pos_of_mul_pos_right this hT3.le

private lemma l6d_g_neg {τ : ℝ} (h1 : tSwOut < τ) : l6d_g τ < 0 := by
  have h := l6d_g_factor τ
  have hB := l6d_g_factor_pos (l6d_T_pos.le.trans h1.le)
  have hT3 : 0 < tSwOut ^ 3 := pow_pos l6d_T_pos 3
  have : tSwOut ^ 3 * l6d_g τ < 0 := by rw [h]; exact mul_neg_of_neg_of_pos (by linarith) hB
  exact neg_of_mul_neg_right this hT3.le

/-- The derivative of the cubic. -/
private noncomputable def l6d_g' (τ : ℝ) : ℝ := l6d_a1 + 2 * l6d_a2 * τ + 3 * outCubicCoeff3 * τ ^ 2

private lemma l6d_hasDerivAt_g (τ : ℝ) : HasDerivAt l6d_g (l6d_g' τ) τ := by
  have h := ((((hasDerivAt_id τ).const_mul l6d_a1).const_add outCubicCoeff0).add
    (((hasDerivAt_id τ).pow 2).const_mul l6d_a2)).add (((hasDerivAt_id τ).pow 3).const_mul
        outCubicCoeff3)
  convert h using 1
  · funext x; simp [l6d_g]
  · simp [l6d_g']; ring

/-- The root `t_sw` of the cubic is simple: `g'(t_sw) < 0`. -/
private lemma l6d_g'_T_neg : l6d_g' tSwOut < 0 := by
  have h := l6d_g_T
  obtain ⟨h0, h1, h2, -⟩ := l6d_coeff_signs
  have hT := l6d_T_pos
  unfold l6d_g at h
  have key : tSwOut * l6d_g' tSwOut = -3 * outCubicCoeff0 - 2 * l6d_a1 * tSwOut - l6d_a2 * tSwOut ^
      2 := by
    unfold l6d_g'; linear_combination 3 * h
  have : tSwOut * l6d_g' tSwOut < 0 := by rw [key]; nlinarith
  exact neg_of_mul_neg_right this hT.le

/-- `z(x̃_out)` is the virial rescaling of `q_out` by `λ` (Remark 14.2.1). -/
lemma fullerOfChart_xTildeOut : fullerOfChart xTildeOut = scale virialScaleOut qOutCart :=
  remark14_2_1.2.2.2.1

/-- `χ̃₂₁(s, 0, x̃_out) = 24 λ³ g(s/λ)`. -/
private lemma l6d_v21_xTildeOut (s : ℝ) :
    extChi21Zero (s, xTildeOut) = 24 * virialScaleOut ^ 3 * l6d_g (s / virialScaleOut) := by
  have hl := virialScaleOut_pos.ne'
  have h := l6d_flow_scale virialScaleOut (s / virialScaleOut) qOutCart ζ
  rw [mul_div_cancel₀ s hl] at h
  simp only [extChi21Zero, fullerOfChart_xTildeOut, h, ← l6d_RR_flow_qOut]
  simp only [scale, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  rw [← Complex.ofReal_pow, RR_ofReal_mul_right]
  ring

private lemma l6d_v21_xTildeOut_pos {s : ℝ} (h0 : 0 ≤ s) (h1 : s < sSwOut) :
    0 < extChi21Zero (s, xTildeOut) := by
  have hl := virialScaleOut_pos
  rw [l6d_v21_xTildeOut]
  have : s / virialScaleOut < tSwOut := by
    rw [div_lt_iff₀ hl]; unfold sSwOut at h1; linarith
  exact mul_pos (by positivity) (l6d_g_pos (div_nonneg h0 hl.le) this)

private lemma l6d_v21_xTildeOut_neg {s : ℝ} (h1 : sSwOut < s) : extChi21Zero (s, xTildeOut) < 0 :=
    by
  have hl := virialScaleOut_pos
  rw [l6d_v21_xTildeOut]
  have : tSwOut < s / virialScaleOut := by
    rw [lt_div_iff₀ hl]; unfold sSwOut at h1; linarith
  exact mul_neg_of_pos_of_neg (by positivity) (l6d_g_neg this)

private lemma l6d_v21_xTildeOut_S : extChi21Zero (sSwOut, xTildeOut) = 0 := by
  rw [l6d_v21_xTildeOut, sSwOut, mul_div_cancel_left₀ _ virialScaleOut_pos.ne', l6d_g_T, mul_zero]

/-- The derivative `24 λ² g'(t_sw) < 0` of `s ↦ χ̃₂₁(s, 0, x̃_out)` at `s_sw,out`. -/
private noncomputable def l6d_D : ℝ := 24 * virialScaleOut ^ 2 * l6d_g' tSwOut

private lemma l6d_D_neg : l6d_D < 0 :=
  mul_neg_of_pos_of_neg (by have := virialScaleOut_pos; positivity) l6d_g'_T_neg

private lemma l6d_hasDerivAt_v21_xTildeOut :
    HasDerivAt (fun s ↦ extChi21Zero (s, xTildeOut)) l6d_D sSwOut := by
  have hl := virialScaleOut_pos.ne'
  have hg := l6d_hasDerivAt_g (sSwOut / virialScaleOut)
  have hdiv : HasDerivAt (fun s ↦ s / virialScaleOut) (1 / virialScaleOut) sSwOut :=
    (hasDerivAt_id _).div_const _
  have h := (hg.comp sSwOut hdiv).const_mul (24 * virialScaleOut ^ 3)
  convert h using 1
  · funext s; simp [l6d_v21_xTildeOut]
  · rw [sSwOut, mul_div_cancel_left₀ _ hl]; simp only [l6d_D]; field_simp

/-- The Fuller switching function from `ζ` to `ζ²` along the flow from `q_out`:
`√3 τ (y₂ + y₁ τ/2 + τ²/12)`. -/
private lemma l6d_RR23_flow_qOut (τ : ℝ) : RR (ζ - ζ ^ 2) (flow τ qOutCart ζ 2) =
    √3 * τ * ((qOutCart 1).im + (qOutCart 0).im * τ / 2 + τ ^ 2 / 12) := by
  obtain ⟨-, h2, -⟩ := qOutCart_normalization
  rw [RR_eq_re_mul_add_im_mul]
  simp [flow, ζ_re, ζ_im, ζ_sq_re, ζ_sq_im, h2]
  ring

/-- `χ̃₂₃(s, 0, x̃_out) = s Q(s)` with `Q > 0` on `[0, ∞)`. -/
noncomputable def extChi23Factor (s : ℝ) : ℝ :=
  24 * virialScaleOut ^ 2 * √3 * ((qOutCart 1).im + (qOutCart 0).im * (s / virialScaleOut) / 2 +
    (s / virialScaleOut) ^ 2 / 12)

lemma extChi23Zero_xTildeOut (s : ℝ) : extChi23Zero (s, xTildeOut) = s * extChi23Factor s := by
  have hl := virialScaleOut_pos.ne'
  have h := l6d_flow_scale virialScaleOut (s / virialScaleOut) qOutCart ζ
  rw [mul_div_cancel₀ s hl] at h
  simp only [extChi23Zero, fullerOfChart_xTildeOut, h]
  simp only [scale, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  rw [← Complex.ofReal_pow, RR_ofReal_mul_right, l6d_RR23_flow_qOut, extChi23Factor]
  field_simp

lemma extChi23Factor_pos {s : ℝ} (hs : 0 ≤ s) : 0 < extChi23Factor s := by
  obtain ⟨hy1, -, hy2⟩ := qOutCart_signs
  have hl := virialScaleOut_pos
  unfold extChi23Factor
  have : 0 ≤ (qOutCart 0).im * (s / virialScaleOut) / 2 := by positivity
  have : 0 < (qOutCart 1).im + (qOutCart 0).im * (s / virialScaleOut) / 2 + (s / virialScaleOut) ^ 2
      / 12 := by
    positivity
  positivity

/-- `w(s_sw,out, x̃_out) = λ r_scale q_out` (the fixed point equation (13.5.2), rescaled). -/
private lemma l6d_w_base : extFullerFlow (sSwOut, xTildeOut) 0 = (virialScaleOut * rScale :
    ℝ) * qOutCart 0 := by
  have h := poincare_qOutCart
  rw [poincare, firstControl_qOutCart] at h
  have hl := l6d_flow_scale virialScaleOut tSwOut qOutCart ζ
  rw [extFullerFlow, sSwOut, fullerOfChart_xTildeOut, hl, show tSwOut = firstSwitchTime qOutCart
      from rfl,
    h]
  simp only [Pi.smul_apply, scale, Matrix.cons_val_zero, smul_eq_mul]
  have h3 : ζ * (ζ ^ 2 * ((rScale : ℂ) * qOutCart 0)) = ζ ^ 3 * ((rScale : ℂ) * qOutCart 0) := by
    ring
  rw [show ζ * (↑virialScaleOut * (ζ ^ 2 * (↑rScale * qOutCart 0))) =
    ↑virialScaleOut * (ζ * (ζ ^ 2 * (↑rScale * qOutCart 0))) by ring, h3, ζ_pow_three]
  push_cast
  ring

private lemma l6d_va_base : extLimitA (sSwOut, xTildeOut) = rScale := by
  have hq := qOutCart_signs.1.ne'
  rw [extLimitA, l6d_w_base, Complex.im_ofReal_mul, virialScaleOut]
  field_simp

lemma extDivA_base : extDivA (sSwOut, 0, xTildeOut) = rScale := by
  rw [extDivA, l6d_divR_zero, l6d_va_base]

/-! ### The forward instance: the Fuller data at `x̃_out` -/

/-- `g > 0` on `(-a₀/a₁, 0]` (there `a₂ τ² ≥ 0` and `a₃ τ³ ≥ 0`). -/
private lemma l6s_g_pos_of_nonpos {τ : ℝ} (h0 : -(outCubicCoeff0 / l6d_a1) < τ) (h1 : τ ≤ 0) :
    0 < l6d_g τ := by
  obtain ⟨c0, c1, c2, c3⟩ := l6d_coeff_signs
  have ht : -outCubicCoeff0 < l6d_a1 * τ := by
    have := mul_lt_mul_of_pos_left h0 c1
    rwa [mul_neg, mul_div_cancel₀ _ c1.ne'] at this
  have h2 : 0 ≤ l6d_a2 * τ ^ 2 := by positivity
  have h3 : 0 ≤ outCubicCoeff3 * τ ^ 3 :=
    mul_nonneg_of_nonpos_of_nonpos c3.le (Odd.pow_nonpos (by decide) h1)
  unfold l6d_g
  linarith

/-- `χ̃₂₁(s, 0, x̃_out) > 0` on `(-λ a₀/a₁, s_sw,out)`: the backward instance's χ₂₃ check reads it
slightly before `s = 0`. -/
private lemma l6s_v21_xTildeOut_pos' {s : ℝ}
    (h0 : -(virialScaleOut * (outCubicCoeff0 / l6d_a1)) < s) (h1 : s < sSwOut) :
    0 < extChi21Zero (s, xTildeOut) := by
  rcases le_or_gt 0 s with hs | hs
  · exact l6d_v21_xTildeOut_pos hs h1
  · have hl := virialScaleOut_pos
    rw [l6d_v21_xTildeOut]
    refine mul_pos (by positivity) (l6s_g_pos_of_nonpos ?_ (div_nonpos_of_nonpos_of_nonneg hs.le
      hl.le))
    rw [lt_div_iff₀ hl]
    linarith

/-- The slope `Q(0) > 0` of `s ↦ χ̃₂₃(s, 0, x̃_out) = s Q(s)` at `s = 0`. -/
private lemma l6s_hasDerivAt_chi23Zero_out :
    HasDerivAt (fun s ↦ extChi23Zero (s, xTildeOut)) (extChi23Factor 0) 0 := by
  have hQ : DifferentiableAt ℝ extChi23Factor 0 := by unfold extChi23Factor; fun_prop
  have h := (hasDerivAt_id (0 : ℝ)).mul hQ.hasDerivAt
  convert h using 1
  · funext s
    rw [extChi23Zero_xTildeOut]
    rfl
  · simp

/-- **The Fuller data at `x̃_out`** (the forward instance of Step 4): `χ̃₂₁(s, 0, x̃_out) = 24 λ³
g(s/λ)` is positive on `[0, s_sw,out)` with the simple root `s_sw,out` (`l6d_g_factor`,
`l6d_g'_T_neg`), `χ̃₂₃(s, 0, x̃_out) = s Q(s)` with `Q > 0` on `[0, ∞)`
(`extChi23Zero_xTildeOut`), and the `(1, 1)` coefficient is `r_scale > 0`. -/
theorem fullerSwitchData_out : FullerSwitchData 1 xTildeOut sSwOut where
  sign := Or.inl rfl
  root_pos := l6d_S_pos
  chi21_pos u hu := by
    rw [one_mul, one_mul]
    exact l6d_v21_xTildeOut_pos hu.1 hu.2
  chi21_root := by rw [one_mul]; exact l6d_v21_xTildeOut_S
  chi21_simple := ⟨l6d_D, l6d_D_neg, by simpa using l6d_hasDerivAt_v21_xTildeOut⟩
  chi23_pos := ⟨sSwOut + 1, by linarith, fun u hu ↦ by
    rw [one_mul, one_mul, extChi23Zero_xTildeOut]
    exact mul_pos hu.1 (extChi23Factor_pos hu.1.le)⟩
  chi23_slope := ⟨extChi23Factor 0, extChi23Factor_pos le_rfl,
    by simpa using l6s_hasDerivAt_chi23Zero_out⟩
  scale_pos := by rw [one_mul, l6d_va_base]; linarith [rScale_spec.1]

/-! ### The backward instance: the Fuller data at `x̃_in`, from those at `x̃_out`

`x̃_in = σ x̃_out` is the divisor point of the chart that `τ` maps to `(0, x̃_out)`
(`lieChart_chartReflect`). Its Fuller data are read off the forward arc from `z(x̃_out)` (with the
fixed point equation), not estimated at `q_in`. -/

/-- The divisor point of the backward instance, `x̃_in = σ x̃_out = (-x̃₂₁, -ℓ̃₁₁, ℓ̃₂₁)` at
`x̃_out`: `chartReflect (0, x̃_out) = (0, x̃_in)`. -/
noncomputable def xTildeIn : Fin 3 → ℝ := ![-xTildeOut 0, -xTildeOut 1, xTildeOut 2]

/-- The switching time `s_sw,out / r_scale ≈ 1.4094` of the backward instance (in the physical
rescaled time). -/
noncomputable def sSwIn : ℝ := sSwOut / rScale

private lemma l6s_rScale_pos : 0 < rScale := by linarith [rScale_spec.1]

private lemma l6s_sSwIn_sub : sSwOut - rScale * sSwIn = 0 := by
  rw [sSwIn, mul_div_cancel₀ _ l6s_rScale_pos.ne', sub_self]

lemma chartReflect_zero_xTildeOut : chartReflect ((0 : ℝ), xTildeOut) = ((0 : ℝ), xTildeIn) := by
  simp [chartReflect, xTildeIn]

/-- `z(σ x̃) = -conj z(x̃)`, componentwise. -/
private lemma l6s_fullerOfChart_reflect (x : Fin 3 → ℝ) :
    fullerOfChart ![-x 0, -x 1, x 2] = fun i ↦ -starRingEnd ℂ (fullerOfChart x i) := by
  funext i
  fin_cases i <;> apply Complex.ext <;> simp [fullerOfChart, map_ofNat, map_div₀] <;> ring

/-- The Fuller flow commutes with `z ↦ -conj z`, the control being conjugated. -/
private lemma l6s_flow_negConj (t : ℝ) (z : Fin 3 → ℂ) (u : ℂ) :
    flow t (fun i ↦ -starRingEnd ℂ (z i)) u =
      fun i ↦ -starRingEnd ℂ (flow t z (starRingEnd ℂ u) i) := by
  funext i
  fin_cases i <;> simp [flow, map_ofNat, map_div₀] <;> ring

/-- The rotation equivariance of the Fuller flow. -/
private lemma l6s_smul_flow (v : ℂ) (t : ℝ) (z : Fin 3 → ℂ) (u : ℂ) :
    v • flow t z u = flow t (v • z) (v * u) := by
  funext i
  fin_cases i <;> simp [flow] <;> ring

/-- **The fixed point equation at `z(x̃_out)`** ((13.5.2), virially rescaled):
`ζ z(s_sw,out, z(x̃_out), ζ) = r_scale · z(x̃_out)` (`poincare_qOutCart`). -/
lemma smul_flow_sSwOut :
    ζ • flow sSwOut (fullerOfChart xTildeOut) ζ = scale rScale (fullerOfChart xTildeOut) := by
  have h := poincare_qOutCart
  rw [poincare, firstControl_qOutCart] at h
  rw [sSwOut, fullerOfChart_xTildeOut, l6d_flow_scale, show tSwOut = firstSwitchTime qOutCart from
    rfl, h, scale_smul, smul_smul, ← pow_succ', ζ_pow_three, one_smul, scale_scale, scale_scale,
    mul_comm]

/-- **The backward Fuller arc from `z(x̃_out)`** with the control `ζ²` is the forward arc with the
control `ζ`, read backwards from `s_sw,out` and rescaled by `1/r_scale`:
`z(-u, z(x̃_out), ζ²) = r_scale⁻¹ · ζ z(s_sw,out - r_scale u, z(x̃_out), ζ)` (the rotation, the flow
property and the virial rescaling, from `smul_flow_sSwOut`). -/
lemma flow_neg_xTildeOut (u : ℝ) :
    flow (-u) (fullerOfChart xTildeOut) (ζ ^ 2) =
      scale rScale⁻¹ (ζ • flow (sSwOut - rScale * u) (fullerOfChart xTildeOut) ζ) := by
  have key : ζ • flow (sSwOut - rScale * u) (fullerOfChart xTildeOut) ζ =
      scale rScale (flow (-u) (fullerOfChart xTildeOut) (ζ ^ 2)) := by
    calc ζ • flow (sSwOut - rScale * u) (fullerOfChart xTildeOut) ζ
        = flow (sSwOut - rScale * u) (ζ • fullerOfChart xTildeOut) (ζ * ζ) :=
          l6s_smul_flow ζ _ _ ζ
      _ = flow (rScale * -u) (flow sSwOut (ζ • fullerOfChart xTildeOut) (ζ * ζ)) (ζ * ζ) := by
          rw [← flow_add]; congr 1; ring
      _ = flow (rScale * -u) (ζ • flow sSwOut (fullerOfChart xTildeOut) ζ) (ζ ^ 2) := by
          rw [l6s_smul_flow, sq]
      _ = flow (rScale * -u) (scale rScale (fullerOfChart xTildeOut)) (ζ ^ 2) := by
          rw [smul_flow_sSwOut]
      _ = scale rScale (flow (-u) (fullerOfChart xTildeOut) (ζ ^ 2)) := l6d_flow_scale _ _ _ _
  rw [key, scale_scale, inv_mul_cancel₀ l6s_rScale_pos.ne', scale_one]

/-- The Fuller arc from `z(x̃_in)` with the control `ζ`, at negative times, is `-conj` of the
rescaled forward arc from `z(x̃_out)`. -/
private lemma l6s_flow_in (u : ℝ) :
    flow (-u) (fullerOfChart xTildeIn) ζ = fun i ↦ -starRingEnd ℂ
      (scale rScale⁻¹ (ζ • flow (sSwOut - rScale * u) (fullerOfChart xTildeOut) ζ) i) := by
  rw [xTildeIn, l6s_fullerOfChart_reflect, l6s_flow_negConj, conj_ζ, flow_neg_xTildeOut]

private lemma l6s_flow_in_two (u : ℝ) :
    flow (-u) (fullerOfChart xTildeIn) ζ 2 = ((-(rScale⁻¹ ^ 3) : ℝ) : ℂ) *
      starRingEnd ℂ (ζ * flow (sSwOut - rScale * u) (fullerOfChart xTildeOut) ζ 2) := by
  rw [l6s_flow_in]
  simp only [scale, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons, map_mul, map_pow, Complex.conj_ofReal]
  push_cast
  ring

private lemma l6s_RR_one_conj (w : ℂ) : RR (ζ - 1) (starRingEnd ℂ (ζ * w)) = RR (ζ - ζ ^ 2) w := by
  have hs : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  simp only [RR_eq_re_mul_add_im_mul, Complex.sub_re, Complex.sub_im, Complex.conj_re,
    Complex.conj_im, Complex.mul_re, Complex.mul_im, ζ_re, ζ_im, ζ_sq_re, ζ_sq_im,
    Complex.one_re, Complex.one_im]
  linear_combination (-w.re / 4) * hs

private lemma l6s_RR_sq_conj (w : ℂ) : RR (ζ - ζ ^ 2) (starRingEnd ℂ (ζ * w)) = RR (ζ - 1) w := by
  have hs : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  simp only [RR_eq_re_mul_add_im_mul, Complex.sub_re, Complex.sub_im, Complex.conj_re,
    Complex.conj_im, Complex.mul_re, Complex.mul_im, ζ_re, ζ_im, ζ_sq_re, ζ_sq_im,
    Complex.one_re, Complex.one_im]
  linear_combination (-w.re / 2) * hs

/-- **The switching functions at `x̃_in` are those at `x̃_out`, reversed** (`κ = -1`):
`κ χ̃₂₁(κ u, 0, x̃_in) = r_scale⁻³ χ̃₂₃(s_sw,out - r_scale u, 0, x̃_out)`. -/
lemma extChi21Zero_xTildeIn (u : ℝ) : -1 * extChi21Zero (-1 * u, xTildeIn) =
    rScale⁻¹ ^ 3 * extChi23Zero (sSwOut - rScale * u, xTildeOut) := by
  simp only [extChi21Zero, extChi23Zero, neg_one_mul]
  rw [l6s_flow_in_two, RR_ofReal_mul_right, l6s_RR_one_conj]
  ring

/-- `κ χ̃₂₃(κ u, 0, x̃_in) = r_scale⁻³ χ̃₂₁(s_sw,out - r_scale u, 0, x̃_out)` (`κ = -1`). -/
lemma extChi23Zero_xTildeIn (u : ℝ) : -1 * extChi23Zero (-1 * u, xTildeIn) =
    rScale⁻¹ ^ 3 * extChi21Zero (sSwOut - rScale * u, xTildeOut) := by
  simp only [extChi21Zero, extChi23Zero, neg_one_mul]
  rw [l6s_flow_in_two, RR_ofReal_mul_right, l6s_RR_sq_conj]
  ring

private lemma l6s_scale_negConj (c : ℝ) (z : Fin 3 → ℂ) :
    scale c (fun i ↦ -starRingEnd ℂ (z i)) = fun i ↦ -starRingEnd ℂ (scale c z i) := by
  funext i
  fin_cases i <;> simp [scale]

/-- The image of the backward instance at its base point: `w = r_scale⁻¹ · z(x̃_in)`. -/
lemma extFullerFlow_xTildeIn :
    extFullerFlow (-1 * sSwIn, xTildeIn) = scale rScale⁻¹ (fullerOfChart xTildeIn) := by
  simp only [extFullerFlow]
  rw [neg_one_mul, l6s_flow_in, l6s_sSwIn_sub, flow_zero, scale_smul]
  conv_rhs => rw [xTildeIn, l6s_fullerOfChart_reflect, l6s_scale_negConj]
  have hζ : ζ * ζ ^ 2 = 1 := by rw [← pow_succ', ζ_pow_three]
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, conj_ζ]
  linear_combination (-(starRingEnd ℂ (scale rScale⁻¹ (fullerOfChart xTildeOut) i))) * hζ

/-- **The Fuller data at `x̃_in`** (the backward instance of Step 4), from those at `x̃_out`:
`κ χ̃₂₁(κ u, 0, x̃_in) = r_scale⁻³ s' Q(s')` and
`κ χ̃₂₃(κ u, 0, x̃_in) = r_scale⁻³ χ̃₂₁(s', 0, x̃_out)` with `s' = s_sw,out - r_scale u`
(`extChi21Zero_xTildeIn`, `extChi23Zero_xTildeIn`), so: positive on `[0, s_sw,out/r_scale)`
(`s' ∈ (0, s_sw,out]`), the simple root `u₀ = s_sw,out/r_scale` (`s' = 0`, slope
`-r_scale⁻² Q(0) < 0`), the χ₂₃ check on `(0, B]` (`s' ≥ -λ a₀/(2 a₁)`, where the forward cubic is
still positive) with the slope `-r_scale⁻² χ̃₂₁'(s_sw,out) > 0` at `u = 0`; and the `(1, 1)`
coefficient `r_scale⁻¹ > 0` (`extFullerFlow_xTildeIn`). -/
theorem fullerSwitchData_in : FullerSwitchData (-1) xTildeIn sSwIn where
  sign := Or.inr rfl
  root_pos := div_pos l6d_S_pos l6s_rScale_pos
  chi21_pos u hu := by
    have hr := l6s_rScale_pos
    rw [extChi21Zero_xTildeIn, extChi23Zero_xTildeOut]
    have h1 : 0 < sSwOut - rScale * u := by
      have := hu.2
      rw [sSwIn, lt_div_iff₀ hr] at this
      linarith
    exact mul_pos (by positivity) (mul_pos h1 (extChi23Factor_pos h1.le))
  chi21_root := by
    have h := extChi21Zero_xTildeIn sSwIn
    rw [l6s_sSwIn_sub, extChi23Zero_zero, mul_zero] at h
    linarith
  chi21_simple := by
    have hr := l6s_rScale_pos
    refine ⟨rScale⁻¹ ^ 3 * (extChi23Factor 0 * -rScale), ?_, ?_⟩
    · have h1 := extChi23Factor_pos le_rfl
      have h2 : 0 < rScale⁻¹ ^ 3 := by positivity
      exact mul_neg_of_pos_of_neg h2 (mul_neg_of_pos_of_neg h1 (by linarith))
    · rw [show (fun u ↦ -1 * extChi21Zero (-1 * u, xTildeIn)) = fun u ↦
          rScale⁻¹ ^ 3 * extChi23Zero (sSwOut - rScale * u, xTildeOut) from
          funext extChi21Zero_xTildeIn]
      have hin : HasDerivAt (fun u : ℝ ↦ sSwOut - rScale * u) (-rScale) sSwIn := by
        simpa using ((hasDerivAt_id sSwIn).const_mul rScale).const_sub sSwOut
      have hg : HasDerivAt (fun s ↦ extChi23Zero (s, xTildeOut)) (extChi23Factor 0)
          (sSwOut - rScale * sSwIn) := by
        rw [l6s_sSwIn_sub]; exact l6s_hasDerivAt_chi23Zero_out
      exact (hg.comp sSwIn hin).const_mul _
  chi23_pos := by
    have hr := l6s_rScale_pos
    obtain ⟨c0, c1, -, -⟩ := l6d_coeff_signs
    have hl := virialScaleOut_pos
    set c := virialScaleOut * (outCubicCoeff0 / l6d_a1) with hc
    have hc0 : 0 < c := by positivity
    refine ⟨(sSwOut + c / 2) / rScale, ?_, fun u hu ↦ ?_⟩
    · rw [sSwIn]
      exact (div_lt_div_iff_of_pos_right hr).2 (by linarith)
    · rw [extChi23Zero_xTildeIn]
      refine mul_pos (by positivity) (l6s_v21_xTildeOut_pos' ?_ ?_)
      · have := hu.2
        rw [le_div_iff₀ hr] at this
        linarith
      · have := mul_pos hr hu.1
        linarith
  chi23_slope := by
    have hr := l6s_rScale_pos
    refine ⟨rScale⁻¹ ^ 3 * (l6d_D * -rScale), ?_, ?_⟩
    · have h2 : 0 < rScale⁻¹ ^ 3 := by positivity
      exact mul_pos h2 (mul_pos_of_neg_of_neg l6d_D_neg (by linarith))
    · rw [show (fun u ↦ -1 * extChi23Zero (-1 * u, xTildeIn)) = fun u ↦
          rScale⁻¹ ^ 3 * extChi21Zero (sSwOut - rScale * u, xTildeOut) from
          funext extChi23Zero_xTildeIn]
      have hin : HasDerivAt (fun u : ℝ ↦ sSwOut - rScale * u) (-rScale) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_mul rScale).const_sub sSwOut
      have hg : HasDerivAt (fun s ↦ extChi21Zero (s, xTildeOut)) l6d_D (sSwOut - rScale * 0) := by
        rw [mul_zero, sub_zero]; exact l6d_hasDerivAt_v21_xTildeOut
      exact (hg.comp 0 hin).const_mul _
  scale_pos := by
    rw [extLimitA, extFullerFlow_xTildeIn]
    have hr := l6s_rScale_pos
    rw [show (scale rScale⁻¹ (fullerOfChart xTildeIn) 0).im = rScale⁻¹ * (1 / 2) by
      simp [scale, fullerOfChart]]
    positivity

/-! ### The analytic switching time (Step 5), at a divisor point with Fuller data -/

open scoped ContDiff

/-- The implicit equation of the switching time in the physical rescaled time `u = t/|r₀|` on the
side `κ r₀ > 0`, `κ χ̃₂₁(κ u, r₀, x̃₀) = 0` (along the flow, `χ₂₁ = |r₀|³ κ χ̃₂₁(κ u, r₀, x̃₀)` at
`t = |r₀| u`), as a function of `((r₀, x̃₀), u)`. -/
noncomputable def extImplicitFn (κ : ℝ) (v : (ℝ × (Fin 3 → ℝ)) × ℝ) : ℝ :=
  κ * extChi21 (κ * v.2, v.1.1, v.1.2)

lemma analyticAt_extImplicitFn (κ : ℝ) (x : Fin 3 → ℝ) (u : ℝ) :
    AnalyticAt ℝ (extImplicitFn κ) (((0 : ℝ), x), u) := by
  have h : AnalyticAt ℝ (fun v : (ℝ × (Fin 3 → ℝ)) × ℝ ↦ (κ * v.2, v.1.1, v.1.2))
      (((0 : ℝ), x), u) := by fun_prop
  exact analyticAt_const.mul ((l6d_analyticAt_chi21 (κ * u) x).comp_of_eq h rfl)

lemma extImplicitFn_zero (κ : ℝ) (x : Fin 3 → ℝ) (u : ℝ) :
    extImplicitFn κ (((0 : ℝ), x), u) = κ * extChi21Zero (κ * u, x) := by
  simp only [extImplicitFn, l6d_chi21_zero]

lemma contDiffAt_extImplicitFn (κ : ℝ) (x₀ : Fin 3 → ℝ) (u₀ : ℝ) :
    ContDiffAt ℝ ω (extImplicitFn κ) (((0 : ℝ), x₀), u₀) :=
  (analyticAt_extImplicitFn κ x₀ u₀).contDiffAt

private lemma l6s_fderiv_inr (h : FullerSwitchData κ x₀ u₀) :
    ∃ D ≠ 0, fderiv ℝ (extImplicitFn κ) (((0 : ℝ), x₀), u₀) ∘L .inr ℝ (ℝ × (Fin 3 → ℝ)) ℝ =
      (1 : ℝ →L[ℝ] ℝ).smulRight D := by
  obtain ⟨D, hD, hd⟩ := h.chi21_simple
  refine ⟨D, hD.ne, ?_⟩
  have hF : HasFDerivAt (extImplicitFn κ) (fderiv ℝ (extImplicitFn κ) (((0 : ℝ), x₀), u₀))
      (((0 : ℝ), x₀), u₀) :=
    (analyticAt_extImplicitFn κ x₀ u₀).differentiableAt.hasFDerivAt
  have hin : HasFDerivAt (fun u : ℝ ↦ (((0 : ℝ), x₀), u))
      (ContinuousLinearMap.inr ℝ (ℝ × (Fin 3 → ℝ)) ℝ) u₀ :=
    (hasFDerivAt_const _ _).prodMk (hasFDerivAt_id _)
  have h1 := hF.comp u₀ hin
  have h2 : HasFDerivAt (fun u : ℝ ↦ extImplicitFn κ (((0 : ℝ), x₀), u))
      ((1 : ℝ →L[ℝ] ℝ).smulRight D) u₀ :=
    hd.hasFDerivAt.congr_of_eventuallyEq
      (Eventually.of_forall fun u ↦ extImplicitFn_zero κ x₀ u)
  exact h1.unique h2

lemma isInvertible_extImplicitFn (h : FullerSwitchData κ x₀ u₀) :
    (fderiv ℝ (extImplicitFn κ) (((0 : ℝ), x₀), u₀) ∘L
      .inr ℝ (ℝ × (Fin 3 → ℝ)) ℝ).IsInvertible := by
  obtain ⟨D, hD, hfd⟩ := l6s_fderiv_inr h
  rw [hfd]
  refine ContinuousLinearMap.IsInvertible.of_inverse (g := (1 : ℝ →L[ℝ] ℝ).smulRight D⁻¹)
    ?_ ?_ <;> ext <;> simp [hD]

lemma extImplicitFn_base (h : FullerSwitchData κ x₀ u₀) :
    extImplicitFn κ (((0 : ℝ), x₀), u₀) = 0 := by
  rw [extImplicitFn_zero, h.chi21_root, mul_zero]

/-- **The analytic switching time** `u_sw(r₀, x̃₀)` (Step 5, TeX 11813–11821), in the physical
rescaled time: the implicit function of `κ χ̃₂₁(κ u, r₀, x̃₀) = 0` near `((0, x̃₀), u₀)` (the
analytic implicit function theorem, `ContDiffAt.implicitFunction` with `n = ω`; the root `u₀` is
simple). The switching time in the coordinate `s = t/r₀` is `κ u_sw` (`extSwitchArg`). -/
noncomputable def extSwitchTime (h : FullerSwitchData κ x₀ u₀) : ℝ × (Fin 3 → ℝ) → ℝ :=
  (contDiffAt_extImplicitFn κ x₀ u₀).implicitFunction (by simp) (isInvertible_extImplicitFn h)

lemma extSwitchTime_base (h : FullerSwitchData κ x₀ u₀) : extSwitchTime h ((0 : ℝ), x₀) = u₀ :=
  (contDiffAt_extImplicitFn κ x₀ u₀).implicitFunction_apply_self (by simp)
    (isInvertible_extImplicitFn h)

private lemma l6s_eventually_implicit (h : FullerSwitchData κ x₀ u₀) :
    ∀ᶠ p in 𝓝 ((0 : ℝ), x₀), extImplicitFn κ (p, extSwitchTime h p) = 0 := by
  have h1 := (contDiffAt_extImplicitFn κ x₀ u₀).eventually_apply_implicitFunction (by simp)
      (isInvertible_extImplicitFn h)
  rw [extImplicitFn_base h] at h1
  exact h1

private lemma l6s_eventually_implicit_iff (h : FullerSwitchData κ x₀ u₀) :
    ∀ᶠ v in 𝓝 (((0 : ℝ), x₀), u₀), extImplicitFn κ v = 0 ↔ extSwitchTime h v.1 = v.2 := by
  have h1 := (contDiffAt_extImplicitFn κ x₀ u₀).eventually_apply_eq_iff_implicitFunction
    (by simp) (isInvertible_extImplicitFn h)
  rw [extImplicitFn_base h] at h1
  exact h1

lemma analyticAt_extSwitchTime (h : FullerSwitchData κ x₀ u₀) :
    AnalyticAt ℝ (extSwitchTime h) ((0 : ℝ), x₀) :=
  ((contDiffAt_extImplicitFn κ x₀ u₀).contDiffAt_implicitFunction (by simp)
      (isInvertible_extImplicitFn h)).analyticAt

/-! ### The χ₂₃ check (E85) -/

/-- The dual basis property of `sl2Dual`: `⟨sl2Dual M₁ M₂ M₃ c₁ c₂ c₃, M_k⟩ = c_k` (`k = 2, 3`)
when `T = ⟨M₁, [M₂, M₃]⟩ ≠ 0`. -/
private lemma l6d_traceForm_sl2Dual (M₁ M₂ M₃ : Mat2) (c₁ c₂ c₃ : ℝ)
    (hT : traceForm M₁ (M₂ * M₃ - M₃ * M₂) ≠ 0) :
    traceForm (sl2Dual M₁ M₂ M₃ c₁ c₂ c₃) M₂ = c₂ ∧
      traceForm (sl2Dual M₁ M₂ M₃ c₁ c₂ c₃) M₃ = c₃ := by
  set T := traceForm M₁ (M₂ * M₃ - M₃ * M₂) with hTdef
  have hs : ∀ (A B : Mat2) (c : ℝ), traceForm (c • A) B = c * traceForm A B := fun A B c ↦ by
    simp [traceForm, Matrix.trace_smul]
  have e2 : traceForm (c₁ • (M₂ * M₃ - M₃ * M₂) + c₂ • (M₃ * M₁ - M₁ * M₃) +
      c₃ • (M₁ * M₂ - M₂ * M₁)) M₂ = c₂ * T := by
    simp only [hTdef, traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
    ring
  have e3 : traceForm (c₁ • (M₂ * M₃ - M₃ * M₂) + c₂ • (M₃ * M₁ - M₁ * M₃) +
      c₃ • (M₁ * M₂ - M₂ * M₁)) M₃ = c₃ * T := by
    simp only [hTdef, traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
    ring
  simp only [sl2Dual, ← hTdef, hs, e2, e3]
  constructor <;> field_simp

/-- The chart lies on the wall `χ₂₃ = 0` (whenever the linear system (14.1.3) is
nondegenerate and the denominators `⟨Z_{e₂}, X⟩`, `⟨Z_{e₃}, X⟩` are nonzero; for every sign of
`r`). -/
private lemma l6d_switchingFn12_lieChart {p : ℝ × (Fin 3 → ℝ)} (h1 : 1 + p.1 * p.2 0 ≠ 0)
    (hZ1 : traceForm (controlMatrix (vertex 1)) (lieChart p).1 ≠ 0)
    (hZ2 : traceForm (controlMatrix (vertex 2)) (lieChart p).1 ≠ 0) :
    switchingFn 1 2 (lieChart p).2.2 (lieChart p).1 = 0 := by
  have hT : traceForm (lieChart p).1 (controlMatrix (vertex 1) * controlMatrix (vertex 2) -
      controlMatrix (vertex 2) * controlMatrix (vertex 1)) ≠ 0 := by
    rw [show (lieChart p).1 = lieX p.1 (p.2 0) from rfl, traceForm_lieX_controlMatrix_bracket]
    have h3 : (0 : ℝ) < √3 := by positivity
    exact mul_ne_zero (by rw [neg_ne_zero]; positivity) h1
  obtain ⟨hd1, hd2⟩ := l6d_traceForm_sl2Dual (lieChart p).1 (controlMatrix (vertex 1))
    (controlMatrix (vertex 2)) 0
    (traceForm (lieChart p).1 (controlMatrix (vertex 1)) *
      reducedHam (lieChart p).2.1 (lieChart p).1)
    (traceForm (lieChart p).1 (controlMatrix (vertex 2)) *
      reducedHam (lieChart p).2.1 (lieChart p).1) hT
  have hR : (lieChart p).2.2 = sl2Dual (lieChart p).1 (controlMatrix (vertex 1))
      (controlMatrix (vertex 2)) 0
      (traceForm (lieChart p).1 (controlMatrix (vertex 1)) *
        reducedHam (lieChart p).2.1 (lieChart p).1)
      (traceForm (lieChart p).1 (controlMatrix (vertex 2)) *
        reducedHam (lieChart p).2.1 (lieChart p).1) := rfl
  have hc : ∀ A B : Mat2, traceForm A B = traceForm B A := fun A B ↦ Matrix.trace_mul_comm A B
  have hsub : ∀ A B C : Mat2, traceForm A (B - C) = traceForm A B - traceForm A C := fun A B C ↦ by
    simp [traceForm, Matrix.mul_sub, Matrix.trace_sub]
  have hsm : ∀ (A B : Mat2) (c : ℝ), traceForm A (c • B) = c * traceForm A B := fun A B c ↦ by
    simp [traceForm, Matrix.trace_smul]
  rw [switchingFn, controlP, controlP, hsub, hsm, hsm, hR, hd1, hd2, hc (lieChart p).1,
    hc (lieChart p).1]
  field_simp
  ring


/-- The chart lies on the wall near every divisor point: `χ̃₂₃(0, r₀, x̃₀) = 0` near `(0, x̃₀)`. -/
lemma eventually_extChi23_zero (x₀ : Fin 3 → ℝ) :
    ∀ᶠ p in 𝓝 ((0 : ℝ), x₀), extChi23 (0, p.1, p.2) = 0 := by
  -- the denominators at the singular locus
  have hc : ∀ k : Fin 3, ContinuousAt (fun p : ℝ × (Fin 3 → ℝ) ↦
      traceForm (controlMatrix (vertex k)) (lieChart p).1) ((0 : ℝ), x₀) := by
    intro k
    obtain ⟨h1, -, -⟩ := entrywiseAnalyticAt_lieChart (E := ℝ × (Fin 3 → ℝ)) (g := id)
      (x := ((0 : ℝ), x₀)) analyticAt_id (by simp) (by norm_num)
    exact ((EntrywiseAnalyticAt.const _).traceForm h1).continuousAt
  have h0 : ∀ k : Fin 3, traceForm (controlMatrix (vertex k)) (lieChart (0, x₀)).1 ≠ 0 := by
    intro k; rw [l6d_lieChart_zero, traceForm_controlMatrix_vertex_J]; norm_num
  have h1c : ContinuousAt (fun p : ℝ × (Fin 3 → ℝ) ↦ 1 + p.1 * p.2 0) ((0 : ℝ), x₀) := by
    fun_prop
  filter_upwards [(hc 1).eventually_ne (h0 1), (hc 2).eventually_ne (h0 2),
    h1c.eventually_ne (by simp : 1 + (0 : ℝ) * x₀ 0 ≠ 0)] with p hp1 hp2 hp3
  by_cases hr : p.1 = 0
  · simp only [extChi23, extChiDiv, hr, ite_true]
    exact extChi23Zero_zero p.2
  · simp only [extChi23, extChiDiv, hr, ite_false, extChi, extFlowPt, zero_mul,
      ivf_vertexFlow_zero]
    rw [l6d_switchingFn12_lieChart hp3 hp1 hp2, zero_div]

/-- **`χ̃₂₃ = s H` with `H > 0` near `(0, 0, x̃₀)`** (the division by `s` of the χ₂₃ check, E85):
`χ̃₂₃(0, r₀, x̃₀) = 0` near the divisor point (`eventually_extChi23_zero`), so `χ̃₂₃ = s H` with `H`
analytic (division of power series), and `H(0, 0, x̃₀)` is the slope of `χ̃₂₃(·, 0, x̃₀)` at `0`,
positive by the Fuller data. -/
lemma exists_extChi23_eq_mul (h : FullerSwitchData κ x₀ u₀) : ∃ H : ℝ × ℝ × (Fin 3 → ℝ) → ℝ,
    ∀ᶠ v in 𝓝 ((0 : ℝ), ((0 : ℝ), x₀)), extChi23 v = v.1 * H v ∧ 0 < H v := by
  set p₀ : ℝ × (Fin 3 → ℝ) := ((0 : ℝ), x₀) with hp₀
  have han : AnalyticAt ℝ extChi23 ((0 : ℝ), p₀) := analyticAt_extChi23 0 x₀
  -- division by `s`
  have hk : ∀ᶠ y in 𝓝 p₀, (fun s : ℝ ↦ extChi23 (s, y)) =O[𝓝 0] (fun s ↦ s ^ 1) := by
    have hev : ∀ᶠ y in 𝓝 p₀, AnalyticAt ℝ extChi23 ((0 : ℝ), y) := by
      have := han.eventually_analyticAt
      exact (by fun_prop : ContinuousAt (fun y : ℝ × (Fin 3 → ℝ) ↦ ((0 : ℝ), y)) p₀).eventually
        this
    filter_upwards [hev, eventually_extChi23_zero x₀] with y hy hy0
    have hd : HasDerivAt (fun s : ℝ ↦ extChi23 (s, y)) _ 0 :=
      (hy.comp_of_eq (by fun_prop : AnalyticAt ℝ (fun s : ℝ ↦ (s, y)) 0) rfl
        ).differentiableAt.hasDerivAt
    have := hd.isBigO_sub
    simp only [sub_zero] at this
    have hy0' : extChi23 (0, y) = 0 := hy0
    simpa [hy0'] using this
  obtain ⟨H, hH, hHeq⟩ := AnalyticAt.exists_eq_pow_smul_of_isBigO han hk
  -- `H(0, p₀)` is the slope of `χ̃₂₃(·, 0, x̃₀)` at `0`
  obtain ⟨D, hD, hd⟩ := h.chi23_slope
  have hg : HasDerivAt (fun s ↦ extChi23Zero (s, x₀)) D 0 := by
    have := l6s_hasDerivAt_unsign (g := fun s ↦ extChi23Zero (s, x₀)) h.mul_self hd
    rwa [mul_zero] at this
  have hH0 : 0 < H ((0 : ℝ), p₀) := by
    have hcont : ContinuousAt (fun s : ℝ ↦ H (s, p₀)) 0 :=
      hH.continuousAt.comp_of_eq (by fun_prop : ContinuousAt (fun s : ℝ ↦ (s, p₀)) 0) rfl
    have hev : ∀ᶠ s in 𝓝[≠] (0 : ℝ), H (s, p₀) = slope (fun s ↦ extChi23Zero (s, x₀)) 0 s := by
      have h1 : ∀ᶠ s in 𝓝 (0 : ℝ), extChi23 (s, p₀) = s ^ 1 • H (s, p₀) :=
        (by fun_prop : ContinuousAt (fun s : ℝ ↦ (s, p₀)) 0).eventually hHeq
      filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with s hs hs0
      have hs0' : s ≠ 0 := hs0
      have hs' : extChi23Zero (s, x₀) = s * H (s, p₀) := by
        rw [← extChi23_zero, hs, pow_one, smul_eq_mul]
      simp only [slope_def_field, extChi23Zero_zero, sub_zero]
      rw [hs', mul_div_cancel_left₀ _ hs0']
    have hlim := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ))
    have hlim2 := (hasDerivAt_iff_tendsto_slope.1 hg).congr' (hev.mono fun s h ↦ h.symm)
    rw [tendsto_nhds_unique hlim hlim2]
    exact hD
  refine ⟨H, ?_⟩
  filter_upwards [hHeq, continuousAt_const.eventually_lt hH.continuousAt hH0] with v h1 h2
  exact ⟨by simpa using h1, h2⟩

/-- **The χ₂₃ check** (E85): if `κ χ̃₂₃(κ u, 0, x̃₀) > 0` for `0 < u ≤ B`, then near the divisor
point `κ χ̃₂₃(κ u, r₀, x̃₀) > 0` for `0 < u ≤ B` (one more division by `s` handles small `u`,
`exists_extChi23_eq_mul`, and compactness the rest). -/
lemma eventually_extChi23_pos (h : FullerSwitchData κ x₀ u₀) {B : ℝ}
    (hB : ∀ u ∈ Ioc 0 B, 0 < κ * extChi23Zero (κ * u, x₀)) :
    ∀ᶠ p in 𝓝 ((0 : ℝ), x₀), ∀ u ∈ Ioc 0 B, 0 < κ * extChi23 (κ * u, p.1, p.2) := by
  set p₀ : ℝ × (Fin 3 → ℝ) := ((0 : ℝ), x₀) with hp₀
  have hκ := h.mul_self
  obtain ⟨H, hnear⟩ := exists_extChi23_eq_mul h
  rw [← hp₀, nhds_prod_eq] at hnear
  obtain ⟨pa, hpa, pb, hpb, hall⟩ := Filter.eventually_prod_iff.1 hnear
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff.1 hpa
  -- compactness on `[ε/2, B]`
  have htube : ∀ᶠ p in 𝓝 p₀, ∀ u ∈ Icc (ε / 2) B, 0 < κ * extChi23 (κ * u, p.1, p.2) := by
    refine isCompact_Icc.eventually_forall_of_forall_eventually fun u hu ↦ ?_
    have hca : ContinuousAt (fun z : (ℝ × (Fin 3 → ℝ)) × ℝ ↦ κ * extChi23 (κ * z.2, z.1.1, z.1.2))
        (p₀, u) :=
      (analyticAt_const.mul ((analyticAt_extChi23 (κ * u) x₀).comp_of_eq (by fun_prop :
        AnalyticAt ℝ (fun z : (ℝ × (Fin 3 → ℝ)) × ℝ ↦ (κ * z.2, z.1.1, z.1.2)) (p₀, u)) rfl)
        ).continuousAt
    have hpos : 0 < κ * extChi23 (κ * u, p₀.1, p₀.2) := by
      rw [hp₀, extChi23_zero]
      exact hB u ⟨by linarith [hu.1], hu.2⟩
    exact continuousAt_const.eventually_lt hca hpos
  filter_upwards [hpb, htube] with p hp hpt u hu
  by_cases huε : u < ε / 2
  · have habs : |κ| = 1 := by
      rcases h.sign with rfl | rfl <;> norm_num
    have hs' : pa (κ * u) := hεb (by
      rw [Real.dist_eq, sub_zero, abs_mul, habs, one_mul, abs_of_pos hu.1]; linarith)
    obtain ⟨h1, h2⟩ := hall hs' hp
    rw [h1]
    have : κ * (κ * u * H (κ * u, p)) = u * H (κ * u, p) := by
      rw [← mul_assoc, ← mul_assoc, hκ, one_mul]
    rw [this]
    exact mul_pos hu.1 h2
  · exact hpt u ⟨not_lt.1 huε, hu.2⟩

/-- **The least positive zero of `χ̃₂₁` near the divisor point** (TeX 11807–11821): there is
`δ ∈ (0, u₀)` such that for `(r₀, x̃₀)` near `(0, x̃₀)`, `u_sw(r₀, x̃₀) ∈ (u₀ - δ, u₀ + δ)` is a
zero of `κ χ̃₂₁(κ ·, r₀, x̃₀)`, which is positive on `[0, u_sw)` and negative on `(u_sw, u₀ + δ]`,
and `κ χ̃₂₃(κ ·, r₀, x̃₀)` is positive on `(0, u₀ + δ]` (at the divisor point: `u = 0` is not a
zero and the least positive zero `u₀` is simple; the implicit function theorem, compactness of
`[0, u₀]` and the χ₂₃ check). -/
lemma extSwitchTime_zero_structure (h : FullerSwitchData κ x₀ u₀) :
    ∃ δ > 0, δ < u₀ ∧ ∀ᶠ p in 𝓝 ((0 : ℝ), x₀),
      extSwitchTime h p ∈ Ioo (u₀ - δ) (u₀ + δ) ∧ extImplicitFn κ (p, extSwitchTime h p) = 0 ∧
      (∀ u ∈ Ico 0 (extSwitchTime h p), 0 < extImplicitFn κ (p, u)) ∧
      (∀ u ∈ Ioc (extSwitchTime h p) (u₀ + δ), extImplicitFn κ (p, u) < 0) ∧
      ∀ u ∈ Ioc 0 (u₀ + δ), 0 < κ * extChi23 (κ * u, p.1, p.2) := by
  set p₀ : ℝ × (Fin 3 → ℝ) := ((0 : ℝ), x₀) with hp₀
  have hS := h.root_pos
  -- the sign just after the simple root
  obtain ⟨D, hD, hd⟩ := h.chi21_simple
  obtain ⟨b, hb, hbneg⟩ : ∃ b > u₀, ∀ u ∈ Ioo u₀ b, κ * extChi21Zero (κ * u, x₀) < 0 := by
    have h1 := (hasDerivAt_iff_tendsto_slope.1 hd).eventually (gt_mem_nhds hD)
    have h2 : ∀ᶠ u in 𝓝[>] u₀, slope (fun u ↦ κ * extChi21Zero (κ * u, x₀)) u₀ u < 0 :=
      nhdsWithin_mono _ (fun u hu ↦ ne_of_gt hu) h1
    obtain ⟨b, hb, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h2
    refine ⟨b, hb, fun u hu ↦ ?_⟩
    have h3 : slope (fun u ↦ κ * extChi21Zero (κ * u, x₀)) u₀ u < 0 := hsub hu
    simp only [slope_def_field, h.chi21_root, mul_zero, sub_zero] at h3
    have h4 : 0 < u - u₀ := by linarith [hu.1]
    by_contra hc
    push Not at hc
    exact absurd h3 (not_lt.2 (div_nonneg hc h4.le))
  obtain ⟨B, hB, hBpos⟩ := h.chi23_pos
  -- the uniqueness box of the implicit function theorem
  have hbox := l6s_eventually_implicit_iff h
  rw [nhds_prod_eq] at hbox
  obtain ⟨pa, hpa, pb, hpb, hall⟩ := Filter.eventually_prod_iff.1 hbox
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff.1 hpb
  set δ := min (min (ε / 2) (u₀ / 2)) (min ((b - u₀) / 2) ((B - u₀) / 2)) with hδ
  have hδ0 : 0 < δ := lt_min (lt_min (by linarith) (by linarith)) (lt_min (by linarith)
    (by linarith))
  have hδε : δ < ε := (min_le_left _ _).trans_lt ((min_le_left _ _).trans_lt (by linarith))
  have hδS : δ < u₀ := (min_le_left _ _).trans_lt ((min_le_right _ _).trans_lt (by linarith))
  have hδb : u₀ + δ < b := by
    have : δ ≤ (b - u₀) / 2 := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hδB : u₀ + δ ≤ B := by
    have : δ ≤ (B - u₀) / 2 := (min_le_right _ _).trans (min_le_right _ _)
    linarith
  have hin : ∀ u ∈ Icc (u₀ - δ) (u₀ + δ), pb u := fun u hu ↦
    hεb (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hu.1, hu.2])
  refine ⟨δ, hδ0, hδS, ?_⟩
  have hjoint : ∀ u, ContinuousAt (extImplicitFn κ) (p₀, u) := fun u ↦
    (analyticAt_extImplicitFn κ x₀ u).continuousAt
  -- positivity on `[0, u₀ - δ]`
  have hpos : ∀ᶠ p in 𝓝 p₀, ∀ u ∈ Icc 0 (u₀ - δ), 0 < extImplicitFn κ (p, u) := by
    refine isCompact_Icc.eventually_forall_of_forall_eventually fun u hu ↦ ?_
    have h0 : 0 < extImplicitFn κ (p₀, u) := by
      rw [hp₀, extImplicitFn_zero]
      exact h.chi21_pos u ⟨hu.1, by linarith [hu.2]⟩
    exact continuousAt_const.eventually_lt (hjoint u) h0
  -- negativity at `u₀ + δ`
  have hneg : ∀ᶠ p in 𝓝 p₀, extImplicitFn κ (p, u₀ + δ) < 0 := by
    have h0 : extImplicitFn κ (p₀, u₀ + δ) < 0 := by
      rw [hp₀, extImplicitFn_zero]
      exact hbneg _ ⟨by linarith, hδb⟩
    have hc : ContinuousAt (fun p ↦ extImplicitFn κ (p, u₀ + δ)) p₀ :=
      (hjoint _).comp_of_eq (by fun_prop) rfl
    exact hc.eventually_lt continuousAt_const h0
  -- continuity on `[u₀ - δ, u₀ + δ]`
  have hcont : ∀ᶠ p in 𝓝 p₀, ∀ u ∈ Icc (u₀ - δ) (u₀ + δ),
      AnalyticAt ℝ (extImplicitFn κ) (p, u) := by
    refine isCompact_Icc.eventually_forall_of_forall_eventually fun u _ ↦ ?_
    exact (analyticAt_extImplicitFn κ x₀ u).eventually_analyticAt
  have hsw : ∀ᶠ p in 𝓝 p₀, extSwitchTime h p ∈ Ioo (u₀ - δ) (u₀ + δ) := by
    have hc := (analyticAt_extSwitchTime h).continuousAt
    rw [← hp₀] at hc
    refine hc.preimage_mem_nhds (isOpen_Ioo.mem_nhds ?_)
    rw [hp₀, extSwitchTime_base]
    constructor <;> linarith
  have h23 := eventually_extChi23_pos h (B := u₀ + δ) fun u hu ↦ hBpos u ⟨hu.1, hu.2.trans hδB⟩
  filter_upwards [hpa, hpos, hneg, hcont, hsw, l6s_eventually_implicit h, h23] with p hpa' hp1 hp2
    hp3 hp4 hp5 hp6
  have hcon : ContinuousOn (fun u ↦ extImplicitFn κ (p, u)) (Icc (u₀ - δ) (u₀ + δ)) :=
    fun u hu ↦ ((hp3 u hu).continuousAt.comp_of_eq (by fun_prop) rfl).continuousWithinAt
  -- a zero in the box is `u_sw`
  have huniq : ∀ u ∈ Icc (u₀ - δ) (u₀ + δ), extImplicitFn κ (p, u) = 0 →
      extSwitchTime h p = u :=
    fun u hu hz ↦ (hall hpa' (hin u hu)).1 hz
  refine ⟨hp4, hp5, fun u hu ↦ ?_, fun u hu ↦ ?_, hp6⟩
  · by_cases huδ : u ≤ u₀ - δ
    · exact hp1 u ⟨hu.1, huδ⟩
    by_contra hle
    push Not at hle huδ
    have hsub : Icc (u₀ - δ) u ⊆ Icc (u₀ - δ) (u₀ + δ) :=
      Icc_subset_Icc le_rfl (by linarith [hu.2, hp4.2])
    have hS0 : 0 < extImplicitFn κ (p, u₀ - δ) := hp1 _ ⟨by linarith, le_rfl⟩
    obtain ⟨u', hu', hu'0⟩ := intermediate_value_Icc' huδ.le (hcon.mono hsub) ⟨hle, hS0.le⟩
    have := huniq u' (hsub hu') hu'0
    linarith [hu'.2, hu.2]
  · by_contra hle
    push Not at hle
    have hsub : Icc u (u₀ + δ) ⊆ Icc (u₀ - δ) (u₀ + δ) :=
      Icc_subset_Icc (by linarith [hu.1, hp4.1]) le_rfl
    obtain ⟨u', hu', hu'0⟩ := intermediate_value_Icc' hu.2 (hcon.mono hsub) ⟨hp2.le, hle⟩
    have := huniq u' (hsub hu') hu'0
    linarith [hu'.1, hu.1]

/-! ### The extended map in the chart (Step 8), at a divisor point with Fuller data -/

/-- The point `(s_sw, r₀, x̃₀) = (κ u_sw(r₀, x̃₀), r₀, x̃₀)` at which the image point and its
divided entries are evaluated. -/
noncomputable def extSwitchArg (h : FullerSwitchData κ x₀ u₀) (q : ℝ × (Fin 3 → ℝ)) :
    ℝ × ℝ × (Fin 3 → ℝ) :=
  (κ * extSwitchTime h q, q.1, q.2)

lemma analyticAt_extSwitchArg (h : FullerSwitchData κ x₀ u₀) :
    AnalyticAt ℝ (extSwitchArg h) ((0 : ℝ), x₀) := by
  have := analyticAt_extSwitchTime h
  unfold extSwitchArg
  fun_prop

lemma extSwitchArg_base (h : FullerSwitchData κ x₀ u₀) :
    extSwitchArg h ((0 : ℝ), x₀) = (κ * u₀, 0, x₀) := by
  simp [extSwitchArg, extSwitchTime_base]

/-- **The extended Reinhardt–Poincaré map in the chart** (Step 8, TeX 11843–11856): with the divided
entries `a, b, c, d` at `(s_sw, r₀, x̃₀)`, `(r₀, x̃₀) ↦ (r₀ a, b/a, c/a², d/a²)`. -/
noncomputable def extMap (h : FullerSwitchData κ x₀ u₀) (q : ℝ × (Fin 3 → ℝ)) :
    ℝ × (Fin 3 → ℝ) :=
  (q.1 * extDivA (extSwitchArg h q),
    ![extDivB (extSwitchArg h q) / extDivA (extSwitchArg h q),
      extDivC (extSwitchArg h q) / extDivA (extSwitchArg h q) ^ 2,
      extDivD (extSwitchArg h q) / extDivA (extSwitchArg h q) ^ 2])

/-- **The extended map is analytic at the divisor point** (TeX 11856–11860: "Since this `(1, 1)`
matrix coefficient is an analytic function that is nonzero in a neighborhood of the fixed point,
its reciprocal is an analytic function"). -/
theorem analyticAt_extMap (h : FullerSwitchData κ x₀ u₀) :
    AnalyticAt ℝ (extMap h) ((0 : ℝ), x₀) := by
  obtain ⟨ha, hb, hc, hd⟩ := analyticAt_extDiv (κ * u₀) x₀
  have ht := analyticAt_extSwitchArg h
  have hb0 := extSwitchArg_base h
  have hta : AnalyticAt ℝ (fun q ↦ extDivA (extSwitchArg h q)) ((0 : ℝ), x₀) :=
    ha.comp_of_eq ht hb0
  have htb : AnalyticAt ℝ (fun q ↦ extDivB (extSwitchArg h q)) ((0 : ℝ), x₀) :=
    hb.comp_of_eq ht hb0
  have htc : AnalyticAt ℝ (fun q ↦ extDivC (extSwitchArg h q)) ((0 : ℝ), x₀) :=
    hc.comp_of_eq ht hb0
  have htd : AnalyticAt ℝ (fun q ↦ extDivD (extSwitchArg h q)) ((0 : ℝ), x₀) :=
    hd.comp_of_eq ht hb0
  have h0 : extDivA (extSwitchArg h ((0 : ℝ), x₀)) ≠ 0 := by
    rw [hb0, extDivA, l6d_divR_zero]
    exact h.scale_pos.ne'
  have h1 : AnalyticAt ℝ (fun q : ℝ × (Fin 3 → ℝ) ↦ q.1 * extDivA (extSwitchArg h q))
      ((0 : ℝ), x₀) := by fun_prop
  refine h1.prod (AnalyticAt.pi fun i ↦ ?_)
  fin_cases i
  · exact htb.fun_div hta h0
  · exact htc.fun_div (hta.fun_pow 2) (pow_ne_zero 2 h0)
  · exact htd.fun_div (hta.fun_pow 2) (pow_ne_zero 2 h0)

/-- The `(1, 1)` coefficient `a = (X_sw - J)₁₁/r₀` at the divisor point is the Fuller value. -/
lemma extDivA_extSwitchArg_base (h : FullerSwitchData κ x₀ u₀) :
    extDivA (extSwitchArg h ((0 : ℝ), x₀)) = extLimitA (κ * u₀, x₀) := by
  rw [extSwitchArg_base, extDivA, l6d_divR_zero]

/-- For `r ≠ 0` the extended map is `lieChartInv` of the image point (TeX 11849–11856). -/
lemma extMap_eq_lieChartInv (h : FullerSwitchData κ x₀ u₀) {q : ℝ × (Fin 3 → ℝ)}
    (hq : q.1 ≠ 0) : extMap h q = lieChartInv (extSwitchPt (extSwitchArg h q)) := by
  set p : ℝ × ℝ × (Fin 3 → ℝ) := extSwitchArg h q with hp
  have hp1 : p.2.1 ≠ 0 := hq
  have ha := eq_pow_mul_extDivPow extEntryA 1 extLimitA hp1
  have hb := eq_pow_mul_extDivPow extEntryB 1 extLimitB hp1
  have hc := eq_pow_mul_extDivPow extEntryC 2 extLimitC hp1
  have hd := eq_pow_mul_extDivPow extEntryD 2 extLimitD hp1
  simp only [extEntryA, extEntryB, extEntryC, extEntryD] at ha hb hc hd
  have hb' : (extSwitchPt p).1 1 0 = 1 + p.2.1 ^ 1 * extDivB p := by
    simp only [extDivB]; linarith
  have hd' : (extSwitchPt p).2.1 1 0 = -(3 / 2) + p.2.1 ^ 2 * extDivD p := by
    simp only [extDivD]; linarith
  have hpq : p.2.1 = q.1 := rfl
  simp only [extMap, lieChartInv, ← hp]
  rw [ha, hb', hc, hd']
  simp only [extDivA, extDivC, pow_one, Prod.mk.injEq, hpq, true_and]
  funext i
  fin_cases i <;>
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, add_sub_cancel_left,
      neg_add_cancel_comm] <;>
    field_simp

/-- **The extended map on the divisor** (TeX 11858–11860): `E(0, x̃) = (0, fullerChartInv w)` with
`w = ζ z(s_sw(0, x̃), z(x̃), ζ)` (the limits of the divided entries are read off `w`). -/
lemma extMap_zero (h : FullerSwitchData κ x₀ u₀) (x : Fin 3 → ℝ) :
    extMap h (0, x) = (0, fullerChartInv (extFullerFlow (κ * extSwitchTime h (0, x), x))) := by
  simp only [extMap, extSwitchArg, zero_mul, extDivA, extDivB, extDivC, extDivD, l6d_divR_zero,
    Prod.mk.injEq, true_and, extLimitA, extLimitB, extLimitC, extLimitD]
  generalize extFullerFlow (κ * extSwitchTime h (0, x), x) = w
  funext i
  fin_cases i <;> simp [fullerChartInv] <;> ring

lemma fullerOfChart_ne_zero (x : Fin 3 → ℝ) : fullerOfChart x ≠ 0 := by
  intro h
  have := congrArg (fun z : Fin 3 → ℂ ↦ (z 0).im) h
  simp [fullerOfChart] at this

private lemma l6d_ham_sub (z : Fin 3 → ℂ) (u v : ℂ) : ham z u - ham z v = RR (u - v) (z 2) := by
  simp only [ham, RR_eq_re_mul_add_im_mul, Complex.sub_re, Complex.sub_im]
  ring

/-- **The Fuller–Poincaré map from `z(x̃)`** (Step 9): if along the flow with control `ζ` from
`z(x̃)` the switching function to `1` is positive on `[0, σ)`, vanishes at `σ` and is negative
just after, and the one to `ζ²` is positive on `(0, B]`, then the first control of `z(x̃)` is
`ζ`, its first switching time is `σ`, and `F(z(x̃)) = z(σ, z(x̃), ζ)`. -/
private lemma l6d_poincare_eq {x : Fin 3 → ℝ} {σ B : ℝ} (hσ : 0 < σ) (hσB : σ < B)
    (h21pos : ∀ s ∈ Ico 0 σ, 0 < extChi21Zero (s, x)) (h21zero : extChi21Zero (σ, x) = 0)
    (h21neg : ∀ s ∈ Ioc σ B, extChi21Zero (s, x) < 0) (h23 : ∀ s ∈ Ioc 0 B, 0 < extChi23Zero (s,
        x)) :
    poincare (fullerOfChart x) = flow σ (fullerOfChart x) ζ := by
  set z := fullerOfChart x with hz
  have hz0 : z ≠ 0 := fullerOfChart_ne_zero x
  have h1 : ∀ t, ham (flow t z ζ) ζ - ham (flow t z ζ) 1 = extChi21Zero (t, x) / 24 := fun t ↦ by
    rw [l6d_ham_sub, extChi21Zero]; ring
  have h2 : ∀ t, ham (flow t z ζ) ζ - ham (flow t z ζ) (ζ ^ 2) = extChi23Zero (t, x) / 24 :=
      fun t ↦ by
    rw [l6d_ham_sub, extChi23Zero]; ring
  have h23zero : extChi23Zero (0, x) = 0 := by
    simp only [extChi23Zero, flow_zero]
    have : (fullerOfChart x 2).im = 0 := by simp [fullerOfChart]
    rw [RR_eq_re_mul_add_im_mul]
    simp [this, ζ_re, ζ_sq_re]
  -- `ζ` is optimal on `[0, σ]`
  have hopt : ∀ t ∈ Icc 0 σ, ∀ v ∈ VT, ham (flow t z ζ) v ≤ ham (flow t z ζ) ζ := by
    intro t ht v hv
    rcases mem_VT.1 hv with rfl | rfl | rfl
    · have : 0 ≤ extChi21Zero (t, x) := by
        rcases eq_or_lt_of_le ht.2 with h | h
        · rw [h, h21zero]
        · exact (h21pos t ⟨ht.1, h⟩).le
      linarith [h1 t]
    · exact le_rfl
    · have : 0 ≤ extChi23Zero (t, x) := by
        rcases eq_or_lt_of_le ht.1 with h | h
        · rw [← h, h23zero]
        · exact (h23 t ⟨h, ht.2.trans hσB.le⟩).le
      linarith [h2 t]
  have hfc : firstControl z = ζ :=
    (firstControl_eq_iff hz0).2 ⟨ζ_mem_VT, σ, hσ, hopt⟩
  have hfs : firstSwitchTime z = σ := by
    rw [firstSwitchTime, hfc]
    refine csInf_eq_of_forall_ge_of_forall_gt_exists_lt ?_ ?_ ?_
    · refine ⟨(σ + B) / 2, by linarith, 1, one_mem_VT, ?_⟩
      have := h21neg ((σ + B) / 2) ⟨by linarith, by linarith⟩
      linarith [h1 ((σ + B) / 2)]
    · rintro t ⟨ht0, v, hv, hlt⟩
      by_contra hle
      push Not at hle
      exact absurd (hopt t ⟨ht0.le, hle.le⟩ v hv) (not_le.2 hlt)
    · intro w hw
      set t := (σ + min w B) / 2
      have ht1 : σ < t := by have := lt_min hw hσB; simp only [t]; linarith
      have ht2 : t < min w B := by have := lt_min hw hσB; simp only [t]; linarith
      refine ⟨t, ⟨by linarith, 1, one_mem_VT, ?_⟩, ht2.trans_le (min_le_left _ _)⟩
      have := h21neg t ⟨ht1, (ht2.trans_le (min_le_right _ _)).le⟩
      linarith [h1 t]
  rw [poincare, hfs, hfc]

/-- **On the divisor the forward instance is the Fuller–Poincaré map** (Step 9, TeX 11861–11862):
`E(0, x̃) = (0, fullerChartInv (ζ F(z(x̃))))` for `x̃` near `x̃_out` (the Fuller switching structure
at `z(x̃)`: the zero structure and the χ₂₃ check at `r₀ = 0`, `l6d_poincare_eq`). -/
lemma eventually_extMap_divisor : ∀ᶠ x in 𝓝 xTildeOut,
    extMap fullerSwitchData_out (0, x) = (0, fullerChartInv (ζ • poincare (fullerOfChart x))) := by
  obtain ⟨δ, hδ, hδS, hZ⟩ := extSwitchTime_zero_structure fullerSwitchData_out
  have hc : ContinuousAt (fun x : Fin 3 → ℝ ↦ ((0 : ℝ), x)) xTildeOut := by fun_prop
  filter_upwards [hc.eventually hZ] with x ⟨hσ, hz, hpos, hneg, h23⟩
  set σ := extSwitchTime fullerSwitchData_out ((0 : ℝ), x) with hσdef
  have hP : poincare (fullerOfChart x) = flow σ (fullerOfChart x) ζ := by
    refine l6d_poincare_eq (B := sSwOut + δ) (by linarith [hσ.1]) hσ.2 (fun s hs ↦ ?_) ?_
      (fun s hs ↦ ?_) (fun s hs ↦ ?_)
    · simpa [extImplicitFn_zero] using hpos s hs
    · simpa [extImplicitFn_zero] using hz
    · simpa [extImplicitFn_zero] using hneg s hs
    · simpa [extChi23_zero] using h23 s hs
  rw [extMap_zero, one_mul, ← hσdef, hP]
  rfl

/-- **The backward instance fixes its base point**: `E_in(0, x̃_in) = (0, x̃_in)` (its image there
is `w = r_scale⁻¹ · z(x̃_in)`, `extFullerFlow_xTildeIn`, and `fullerChartInv` inverts
`fullerOfChart` and ignores the virial rescaling). -/
lemma extMap_in_base : extMap fullerSwitchData_in (0, xTildeIn) = (0, xTildeIn) := by
  rw [extMap_zero, extSwitchTime_base, extFullerFlow_xTildeIn,
    fullerChartInv_spec.2.1 _ _ (inv_pos.2 l6s_rScale_pos), fullerChartInv_spec.1]

end SmoothedPolygons
