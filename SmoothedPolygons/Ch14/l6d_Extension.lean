module

public import SmoothedPolygons.Ch14.Asymptotics
public import SmoothedPolygons.Ch14.l6d_FlowAnalytic
public import Basic.Analysis.Analytic.DivisionByCoordinate
public import Mathlib.Analysis.Calculus.ImplicitContDiff
import SmoothedPolygons.Ch7.Isolated.VertexFlow
import SmoothedPolygons.Ch7.Isolated.Return

/-!
# Chapter 14: the analytic construction behind Lemma 14.3.1

Steps 1–9 of the proof of Lemma 14.3.1 of Hales–Vajjha, *Packings of Smoothed Polygons*
(TeX 11784–11860), with the χ₂₃ check (G14.5), in the coordinates `(s, r₀, x̃₀)` (rescaled time
`s = t/r₀` and the initial chart point). The statements of the book are in
`SmoothedPolygons/Ch14/AnalyticExtension.lean`, which uses this file; its module docstring gives
the route step by step.

* `l6d_flowPt p`: the flow with the control `e₂` from the chart point `(r₀, x̃₀)` at time `s r₀`;
  `l6d_chiRaw i j p`: the switching function `χ_ij` there, analytic near `r₀ = 0`
  (`l6d_analyticAt_chiRaw`);
* `l6d_divR f k v`: `f/r₀^k` extended by `v` at `r₀ = 0`, analytic when `f = r₀^k v + O(r₀^{k+1})`
  (`l6d_analyticAt_divR`, division of power series); `l6d_chi21`, `l6d_chi23` (`k = 3`, Lemma
  14.2.4 and its χ₂₃ companion);
* the Fuller cubic at `x̃_out` (`l6d_g`, `l6d_g_factor`, `l6d_g'_T_neg`, `l6d_v21_xTildeOut`,
  `l6d_v23_xTildeOut`), exact;
* `l6d_sSw`: the analytic switching time (implicit function theorem), `l6d_zero_structure` (it is
  the least positive zero near the fixed point), `l6d_eventually_chi23_pos` (the χ₂₃ check);
* `l6d_Xi`: the image point `Ad_{R⁻¹} Y(s r₀)`; its divided entries `l6d_qa`, …, `l6d_qd` (Step 7,
  from Lemma 14.2.3 and the determinant relations); the extended map `l6d_E`, analytic at the fixed
  point (`l6d_analyticAt_E`), `lieChartInv` of the image point for `r₀ ≠ 0`
  (`l6d_E_eq_lieChartInv`), the Fuller–Poincaré map on the divisor (`l6d_eventually_E_divisor`,
  via `l6d_poincare_eq`).
-/

@[expose] public section

namespace SmoothedPolygons

open Complex Set Filter Topology Asymptotics
open TriFuller

attribute [local fun_prop] analyticAt_fst analyticAt_snd l6d_analyticAt_pi_apply

@[simp] lemma l6d_ofReal_pow_re (r : ℝ) (n : ℕ) : ((r : ℂ) ^ n).re = r ^ n := by
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

@[simp] lemma l6d_ofReal_pow_im (r : ℝ) (n : ℕ) : ((r : ℂ) ^ n).im = 0 := by
  rw [← Complex.ofReal_pow, Complex.ofReal_im]

/-! ### The flow from the chart, in rescaled time -/

/-- The flow with the control `e₂` from the chart point `(r₀, x̃₀)` at time `s r₀`
(`p = (s, r₀, x̃₀)`). -/
noncomputable def l6d_flowPt (p : ℝ × ℝ × (Fin 3 → ℝ)) : iso_PhasePt :=
  iso_vertexFlow 1 (lieChart (p.2.1, p.2.2)) (p.1 * p.2.1)

/-- The switching function `χ_ij` along the flow, at `l6d_flowPt p`. -/
noncomputable def l6d_chiRaw (i j : Fin 3) (p : ℝ × ℝ × (Fin 3 → ℝ)) : ℝ :=
  switchingFn i j (l6d_flowPt p).2.2 (l6d_flowPt p).1

lemma l6d_lieChart_zero (x : Fin 3 → ℝ) :
    lieChart (0, x) = (J, (-(3 / 2) : ℝ) • J, 0) := by
  have hX : lieX 0 (x 0) = J := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [lieX, J]
  have hΛ : lieΛ₁ 0 (x 1) (x 2) = (-(3 / 2) : ℝ) • J := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [lieΛ₁, J]
  have hh : reducedHam ((-(3 / 2) : ℝ) • J) J = 0 := by
    simp [reducedHam, traceForm, J, Matrix.trace_fin_two]
  simp only [lieChart, hX, hΛ, lieΛR, sl2Dual, hh, mul_zero, zero_smul, add_zero, smul_zero]

lemma l6d_flowPt_zero (s : ℝ) (x : Fin 3 → ℝ) :
    l6d_flowPt (s, 0, x) = (J, (-(3 / 2) : ℝ) • J, 0) := by
  simp only [l6d_flowPt, mul_zero, ivf_vertexFlow_zero, l6d_lieChart_zero]

/-- The coordinates `(s, r₀, x̃₀) ↦ (r₀, x̃₀)` are analytic. -/
lemma l6d_analyticAt_chartCoord (p : ℝ × ℝ × (Fin 3 → ℝ)) :
    AnalyticAt ℝ (fun p : ℝ × ℝ × (Fin 3 → ℝ) ↦ (p.2.1, p.2.2)) p := by
  fun_prop

/-- The flow from the chart is analytic near `r₀ = 0` (Steps 1–2 of Lemma 14.3.1). -/
lemma l6d_MatAn_flowPt (s : ℝ) (x : Fin 3 → ℝ) :
    l6d_MatAn (fun p ↦ (l6d_flowPt p).1) (s, 0, x) ∧
      l6d_MatAn (fun p ↦ (l6d_flowPt p).2.1) (s, 0, x) ∧
      l6d_MatAn (fun p ↦ (l6d_flowPt p).2.2) (s, 0, x) := by
  obtain ⟨h1, h2, h3⟩ := l6d_MatAn_lieChart (l6d_analyticAt_chartCoord (s, 0, x))
    (by simp) (by norm_num)
  refine l6d_analyticAt_vertexFlow 1 h1 h2 h3 (by fun_prop) ?_
  simp only [l6d_lieChart_zero, l6d_traceForm_controlMatrix_J]
  norm_num

/-- The switching functions along the flow from the chart are analytic near `r₀ = 0`. -/
lemma l6d_analyticAt_chiRaw (i j : Fin 3) (s : ℝ) (x : Fin 3 → ℝ) :
    AnalyticAt ℝ (l6d_chiRaw i j) (s, 0, x) := by
  obtain ⟨h1, -, h3⟩ := l6d_MatAn_flowPt s x
  have hZ : ∀ k : Fin 3, traceForm (controlMatrix (vertex k)) (l6d_flowPt (s, 0, x)).1 ≠ 0 := by
    intro k; rw [l6d_flowPt_zero, l6d_traceForm_controlMatrix_J]; norm_num
  exact h3.traceForm ((l6d_MatAn.controlP j h1 (hZ j)).sub (l6d_MatAn.controlP i h1 (hZ i)))

/-! ### Division by `r₀³` (Step 3) -/

/-- `χ_ij/r₀³`, extended at `r₀ = 0` by the value `v (s, x̃₀)`. -/
noncomputable def l6d_chiT (i j : Fin 3) (v : ℝ × (Fin 3 → ℝ) → ℝ)
    (p : ℝ × ℝ × (Fin 3 → ℝ)) : ℝ :=
  if p.2.1 = 0 then v (p.1, p.2.2) else l6d_chiRaw i j p / p.2.1 ^ 3

/-- The reordering `(r₀, (s, x̃₀)) ↦ (s, r₀, x̃₀)` of the coordinates. -/
def l6d_swap (p : ℝ × ℝ × (Fin 3 → ℝ)) : ℝ × ℝ × (Fin 3 → ℝ) := (p.2.1, p.1, p.2.2)

lemma l6d_analyticAt_swap (p : ℝ × ℝ × (Fin 3 → ℝ)) : AnalyticAt ℝ l6d_swap p := by
  unfold l6d_swap; fun_prop

lemma l6d_swap_swap (p : ℝ × ℝ × (Fin 3 → ℝ)) : l6d_swap (l6d_swap p) = p := rfl

/-- If `f(r) = r^k c + O(r^{k+1})` as `r → 0⁺`, then `f(r)/r^k → c`. -/
lemma l6d_tendsto_div_pow {f : ℝ → ℝ} {c : ℝ} {k : ℕ}
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
noncomputable def l6d_divR (f : ℝ × ℝ × (Fin 3 → ℝ) → ℝ) (k : ℕ) (v : ℝ × (Fin 3 → ℝ) → ℝ)
    (p : ℝ × ℝ × (Fin 3 → ℝ)) : ℝ :=
  if p.2.1 = 0 then v (p.1, p.2.2) else f p / p.2.1 ^ k

lemma l6d_divR_zero (f : ℝ × ℝ × (Fin 3 → ℝ) → ℝ) (k : ℕ) (v : ℝ × (Fin 3 → ℝ) → ℝ) (s : ℝ)
    (x : Fin 3 → ℝ) : l6d_divR f k v (s, 0, x) = v (s, x) := by
  simp [l6d_divR]

lemma l6d_eq_pow_mul_divR (f : ℝ × ℝ × (Fin 3 → ℝ) → ℝ) (k : ℕ) (v : ℝ × (Fin 3 → ℝ) → ℝ)
    {p : ℝ × ℝ × (Fin 3 → ℝ)} (hp : p.2.1 ≠ 0) : f p = p.2.1 ^ k * l6d_divR f k v p := by
  simp only [l6d_divR, hp, ite_false]
  field_simp

/-- **Division of power series** (Step 3 of Lemma 14.3.1, TeX 11800–11806, and Step 7,
TeX 11846–11848): if `f` is analytic near `r₀ = 0` and `f(s, r₀, x̃₀) = r₀^k v(s, x̃₀) +
O(r₀^{k+1})` as `r₀ → 0⁺` for each `(s, x̃₀)`, then `f/r₀^k`, extended by `v` at `r₀ = 0`, is
analytic near every point of `r₀ = 0`. -/
lemma l6d_analyticAt_divR {f : ℝ × ℝ × (Fin 3 → ℝ) → ℝ} (hf : ∀ s x, AnalyticAt ℝ f (s, 0, x))
    (k : ℕ) {v : ℝ × (Fin 3 → ℝ) → ℝ}
    (hv : ∀ s x, (fun r ↦ f (s, r, x) - r ^ k * v (s, x)) =O[𝓝[>] 0] (fun r ↦ r ^ (k + 1)))
    (s : ℝ) (x : Fin 3 → ℝ) :
    AnalyticAt ℝ (l6d_divR f k v) (s, 0, x) := by
  -- the function with the coordinate `r₀` first
  set F : ℝ × ℝ × (Fin 3 → ℝ) → ℝ := fun p ↦ f (l6d_swap p) with hFdef
  have hF : ∀ s' x', AnalyticAt ℝ F (0, s', x') := fun s' x' ↦
    (hf s' x').comp_of_eq (l6d_analyticAt_swap _) rfl
  have hO : ∀ s' x', (fun r ↦ F (r, s', x')) =O[𝓝 0] (fun r ↦ r ^ k) := by
    intro s' x'
    have han : AnalyticAt ℝ (fun r ↦ F (r, s', x')) 0 :=
      (hF s' x').comp_of_eq (by fun_prop : AnalyticAt ℝ (fun r : ℝ ↦ (r, s', x')) 0) rfl
    refine l6d_isBigO_nhds_of_isBigO_nhdsGT han ?_
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
  have hev : l6d_divR f k v =ᶠ[𝓝 (s, 0, x)] fun p ↦ g (l6d_swap p) := by
    have hpre : l6d_swap ⁻¹' U ∈ 𝓝 (s, 0, x) :=
      (l6d_analyticAt_swap (s, 0, x)).continuousAt.preimage_mem_nhds (hUo.mem_nhds hU0)
    filter_upwards [hpre] with p hp
    obtain ⟨s', r', x'⟩ := p
    simp only [mem_preimage, l6d_swap] at hp
    by_cases hr : r' = 0
    · subst hr
      simp only [l6d_divR, l6d_swap, ite_true]
      exact (hval s' x' hp).symm
    · have := (hUsub _ hp).1
      simp only [F, l6d_swap, smul_eq_mul] at this
      simp only [l6d_divR, hr, ite_false, l6d_swap, this]
      field_simp
  exact (hg.comp_of_eq (l6d_analyticAt_swap _) rfl).congr hev.symm

lemma l6d_analyticAt_chiT (i j : Fin 3) {v : ℝ × (Fin 3 → ℝ) → ℝ}
    (hv : ∀ s x, (fun r ↦ l6d_chiRaw i j (s, r, x) - r ^ 3 * v (s, x)) =O[𝓝[>] 0]
      (fun r ↦ r ^ 4)) (s : ℝ) (x : Fin 3 → ℝ) :
    AnalyticAt ℝ (l6d_chiT i j v) (s, 0, x) :=
  l6d_analyticAt_divR (l6d_analyticAt_chiRaw i j) 3 hv s x

/-! ### The rescaled switching functions `χ̃₂₁`, `χ̃₂₃` -/

/-- The limit `24 RR(ζ - 1, z₃(s))` of `χ₂₁/r₀³` (Lemma 14.2.4). -/
noncomputable def l6d_v21 (p : ℝ × (Fin 3 → ℝ)) : ℝ :=
  24 * RR (ζ - 1) (flow p.1 (fullerOfChart p.2) ζ 2)

/-- The limit `24 RR(ζ - ζ², z₃(s))` of `χ₂₃/r₀³` (the χ₂₃ companion of Lemma 14.2.4). -/
noncomputable def l6d_v23 (p : ℝ × (Fin 3 → ℝ)) : ℝ :=
  24 * RR (ζ - ζ ^ 2) (flow p.1 (fullerOfChart p.2) ζ 2)

/-- `χ̃₂₁(s, r₀, x̃₀) = χ₂₁/r₀³`, extended analytically to `r₀ = 0`. -/
noncomputable def l6d_chi21 : ℝ × ℝ × (Fin 3 → ℝ) → ℝ := l6d_chiT 1 0 l6d_v21

/-- `χ̃₂₃(s, r₀, x̃₀) = χ₂₃/r₀³`, extended analytically to `r₀ = 0`. -/
noncomputable def l6d_chi23 : ℝ × ℝ × (Fin 3 → ℝ) → ℝ := l6d_chiT 1 2 l6d_v23

lemma l6d_analyticAt_chi21 (s : ℝ) (x : Fin 3 → ℝ) : AnalyticAt ℝ l6d_chi21 (s, 0, x) := by
  refine l6d_analyticAt_chiT 1 0 (fun s x ↦ ?_) s x
  refine (lemma14_2_4 x s).congr_left fun r ↦ ?_
  simp only [l6d_chiRaw, l6d_flowPt, l6d_v21]
  ring

lemma l6d_analyticAt_chi23 (s : ℝ) (x : Fin 3 → ℝ) : AnalyticAt ℝ l6d_chi23 (s, 0, x) := by
  refine l6d_analyticAt_chiT 1 2 (fun s x ↦ ?_) s x
  refine (lemma14_2_4_chi23 x s).congr_left fun r ↦ ?_
  simp only [l6d_chiRaw, l6d_flowPt, l6d_v23]
  ring

lemma l6d_chi21_zero (s : ℝ) (x : Fin 3 → ℝ) : l6d_chi21 (s, 0, x) = l6d_v21 (s, x) := by
  simp [l6d_chi21, l6d_chiT]

lemma l6d_chi23_zero (s : ℝ) (x : Fin 3 → ℝ) : l6d_chi23 (s, 0, x) = l6d_v23 (s, x) := by
  simp [l6d_chi23, l6d_chiT]

lemma l6d_chiRaw_eq_chi21 {p : ℝ × ℝ × (Fin 3 → ℝ)} (hp : p.2.1 ≠ 0) :
    l6d_chiRaw 1 0 p = p.2.1 ^ 3 * l6d_chi21 p := by
  simp only [l6d_chi21, l6d_chiT, hp, ite_false]
  field_simp

lemma l6d_chiRaw_eq_chi23 {p : ℝ × ℝ × (Fin 3 → ℝ)} (hp : p.2.1 ≠ 0) :
    l6d_chiRaw 1 2 p = p.2.1 ^ 3 * l6d_chi23 p := by
  simp only [l6d_chi23, l6d_chiT, hp, ite_false]
  field_simp

/-! ### The Fuller cubic at `x̃_out` (Step 4) -/

/-- The virial equivariance of the Fuller flow with a constant control:
`z(λ τ, (λ z₁, λ² z₂, λ³ z₃), u) = (λ z₁(τ), λ² z₂(τ), λ³ z₃(τ))`. -/
lemma l6d_flow_scale (l τ : ℝ) (z : Fin 3 → ℂ) (u : ℂ) :
    flow (l * τ) (scale l z) u = scale l (flow τ z u) := by
  funext i
  fin_cases i <;> simp [flow, scale] <;> ring

/-- The rescaling factor `λ = 1/(2 Im q_out,₁)` of Remark 14.2.1 (G14.12). -/
noncomputable def l6d_lam : ℝ := (2 * (qOutCart 0).im)⁻¹

lemma l6d_lam_pos : 0 < l6d_lam := inv_pos.2 (by linarith [qOutCart_signs.1])

/-- The first switching time `t_sw ≈ 7.40` of `q_out`. -/
noncomputable def l6d_T : ℝ := firstSwitchTime qOutCart

lemma l6d_T_pos : 0 < l6d_T := by
  have := firstSwitchTime_qOutCart_bounds.1
  unfold l6d_T; linarith

/-- The rescaled switching time `s_sw,out = λ t_sw ≈ 8.84` at `x̃_out`. -/
noncomputable def l6d_S : ℝ := l6d_lam * l6d_T

lemma l6d_S_pos : 0 < l6d_S := mul_pos l6d_lam_pos l6d_T_pos

/-- The coefficients of the cubic `g(τ) = RR(ζ - 1, z₃(τ, q_out, ζ))`. -/
noncomputable def l6d_a0 : ℝ := -(3 / 2) * (qOutCart 2).re
noncomputable def l6d_a1 : ℝ := -(3 / 2) * (qOutCart 1).re + √3 / 2 * (qOutCart 1).im
noncomputable def l6d_a2 : ℝ := 3 / 4 + √3 / 4 * (qOutCart 0).im
noncomputable def l6d_a3 : ℝ := -(√3 / 12)

/-- The Fuller switching function from `ζ` to `1` along the flow from `q_out` with control `ζ`. -/
noncomputable def l6d_g (τ : ℝ) : ℝ :=
  l6d_a0 + l6d_a1 * τ + l6d_a2 * τ ^ 2 + l6d_a3 * τ ^ 3

lemma l6d_RR_flow_qOut (τ : ℝ) : RR (ζ - 1) (flow τ qOutCart ζ 2) = l6d_g τ := by
  obtain ⟨h0, h2, -⟩ := qOutCart_normalization
  have hs : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [RR_eq_re_mul_add_im_mul]
  simp [flow, l6d_g, l6d_a0, l6d_a1, l6d_a2, l6d_a3, ζ_re, ζ_im, h0, h2]
  ring_nf

lemma l6d_coeff_signs : 0 < l6d_a0 ∧ 0 < l6d_a1 ∧ 0 < l6d_a2 ∧ l6d_a3 < 0 := by
  obtain ⟨-, -, h2⟩ := qOutCart_normalization
  obtain ⟨hy1, hx2, hy2⟩ := qOutCart_signs
  have hs : 0 < √3 := by positivity
  refine ⟨by unfold l6d_a0; linarith, by unfold l6d_a1; nlinarith, by unfold l6d_a2; nlinarith,
    by unfold l6d_a3; linarith⟩

lemma l6d_g_T : l6d_g l6d_T = 0 := by
  have h := poincare_qOutCart
  rw [poincare, firstControl_qOutCart] at h
  have h2 := congrFun h 2
  rw [← l6d_RR_flow_qOut, l6d_T, h2]
  obtain ⟨-, hi, -⟩ := qOutCart_normalization
  have hs : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [RR_eq_re_mul_add_im_mul]
  simp [scale, ζ_re, ζ_im, ζ_sq_re, ζ_sq_im, hi]
  ring_nf
  rw [hs]
  ring

/-- `T³ g(τ) = (T - τ) B(τ)` with `B(τ) > 0` for `τ ≥ 0`. -/
lemma l6d_g_factor (τ : ℝ) : l6d_T ^ 3 * l6d_g τ = (l6d_T - τ) * (l6d_a0 *
    (l6d_T ^ 2 + l6d_T * τ + τ ^ 2) + l6d_a1 * τ * l6d_T * (l6d_T + τ) +
      l6d_a2 * τ ^ 2 * l6d_T ^ 2) := by
  have h := l6d_g_T
  unfold l6d_g at h ⊢
  linear_combination τ ^ 3 * h

lemma l6d_g_factor_pos {τ : ℝ} (hτ : 0 ≤ τ) : 0 < l6d_a0 *
    (l6d_T ^ 2 + l6d_T * τ + τ ^ 2) + l6d_a1 * τ * l6d_T * (l6d_T + τ) +
      l6d_a2 * τ ^ 2 * l6d_T ^ 2 := by
  obtain ⟨h0, h1, h2, -⟩ := l6d_coeff_signs
  have hT := l6d_T_pos
  have : 0 < l6d_T ^ 2 + l6d_T * τ + τ ^ 2 := by positivity
  have : 0 ≤ l6d_a1 * τ * l6d_T * (l6d_T + τ) := by positivity
  have : 0 ≤ l6d_a2 * τ ^ 2 * l6d_T ^ 2 := by positivity
  nlinarith

lemma l6d_g_pos {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ < l6d_T) : 0 < l6d_g τ := by
  have h := l6d_g_factor τ
  have hB := l6d_g_factor_pos h0
  have hT3 : 0 < l6d_T ^ 3 := pow_pos l6d_T_pos 3
  have : 0 < l6d_T ^ 3 * l6d_g τ := by rw [h]; exact mul_pos (by linarith) hB
  exact pos_of_mul_pos_right this hT3.le

lemma l6d_g_neg {τ : ℝ} (h1 : l6d_T < τ) : l6d_g τ < 0 := by
  have h := l6d_g_factor τ
  have hB := l6d_g_factor_pos (l6d_T_pos.le.trans h1.le)
  have hT3 : 0 < l6d_T ^ 3 := pow_pos l6d_T_pos 3
  have : l6d_T ^ 3 * l6d_g τ < 0 := by rw [h]; exact mul_neg_of_neg_of_pos (by linarith) hB
  exact neg_of_mul_neg_right this hT3.le

/-- The derivative of the cubic. -/
noncomputable def l6d_g' (τ : ℝ) : ℝ := l6d_a1 + 2 * l6d_a2 * τ + 3 * l6d_a3 * τ ^ 2

lemma l6d_hasDerivAt_g (τ : ℝ) : HasDerivAt l6d_g (l6d_g' τ) τ := by
  have h := ((((hasDerivAt_id τ).const_mul l6d_a1).const_add l6d_a0).add
    (((hasDerivAt_id τ).pow 2).const_mul l6d_a2)).add (((hasDerivAt_id τ).pow 3).const_mul l6d_a3)
  convert h using 1
  · funext x; simp [l6d_g]
  · simp [l6d_g']; ring

/-- The root `t_sw` of the cubic is simple: `g'(t_sw) < 0`. -/
lemma l6d_g'_T_neg : l6d_g' l6d_T < 0 := by
  have h := l6d_g_T
  obtain ⟨h0, h1, h2, -⟩ := l6d_coeff_signs
  have hT := l6d_T_pos
  unfold l6d_g at h
  have key : l6d_T * l6d_g' l6d_T = -3 * l6d_a0 - 2 * l6d_a1 * l6d_T - l6d_a2 * l6d_T ^ 2 := by
    unfold l6d_g'; linear_combination 3 * h
  have : l6d_T * l6d_g' l6d_T < 0 := by rw [key]; nlinarith
  exact neg_of_mul_neg_right this hT.le

/-- `z(x̃_out)` is the virial rescaling of `q_out` by `λ` (Remark 14.2.1). -/
lemma l6d_fullerOfChart_xTildeOut : fullerOfChart xTildeOut = scale l6d_lam qOutCart :=
  remark14_2_1.2.2.2.1

/-- `χ̃₂₁(s, 0, x̃_out) = 24 λ³ g(s/λ)`. -/
lemma l6d_v21_xTildeOut (s : ℝ) :
    l6d_v21 (s, xTildeOut) = 24 * l6d_lam ^ 3 * l6d_g (s / l6d_lam) := by
  have hl := l6d_lam_pos.ne'
  have h := l6d_flow_scale l6d_lam (s / l6d_lam) qOutCart ζ
  rw [mul_div_cancel₀ s hl] at h
  simp only [l6d_v21, l6d_fullerOfChart_xTildeOut, h, ← l6d_RR_flow_qOut]
  simp only [scale, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  rw [← Complex.ofReal_pow, RR_ofReal_mul_right]
  ring

lemma l6d_v21_xTildeOut_pos {s : ℝ} (h0 : 0 ≤ s) (h1 : s < l6d_S) :
    0 < l6d_v21 (s, xTildeOut) := by
  have hl := l6d_lam_pos
  rw [l6d_v21_xTildeOut]
  have : s / l6d_lam < l6d_T := by
    rw [div_lt_iff₀ hl]; unfold l6d_S at h1; linarith
  exact mul_pos (by positivity) (l6d_g_pos (div_nonneg h0 hl.le) this)

lemma l6d_v21_xTildeOut_neg {s : ℝ} (h1 : l6d_S < s) : l6d_v21 (s, xTildeOut) < 0 := by
  have hl := l6d_lam_pos
  rw [l6d_v21_xTildeOut]
  have : l6d_T < s / l6d_lam := by
    rw [lt_div_iff₀ hl]; unfold l6d_S at h1; linarith
  exact mul_neg_of_pos_of_neg (by positivity) (l6d_g_neg this)

lemma l6d_v21_xTildeOut_S : l6d_v21 (l6d_S, xTildeOut) = 0 := by
  rw [l6d_v21_xTildeOut, l6d_S, mul_div_cancel_left₀ _ l6d_lam_pos.ne', l6d_g_T, mul_zero]

/-- The derivative `24 λ² g'(t_sw) < 0` of `s ↦ χ̃₂₁(s, 0, x̃_out)` at `s_sw,out`. -/
noncomputable def l6d_D : ℝ := 24 * l6d_lam ^ 2 * l6d_g' l6d_T

lemma l6d_D_neg : l6d_D < 0 :=
  mul_neg_of_pos_of_neg (by have := l6d_lam_pos; positivity) l6d_g'_T_neg

lemma l6d_hasDerivAt_v21_xTildeOut :
    HasDerivAt (fun s ↦ l6d_v21 (s, xTildeOut)) l6d_D l6d_S := by
  have hl := l6d_lam_pos.ne'
  have hg := l6d_hasDerivAt_g (l6d_S / l6d_lam)
  have hdiv : HasDerivAt (fun s ↦ s / l6d_lam) (1 / l6d_lam) l6d_S :=
    (hasDerivAt_id _).div_const _
  have h := (hg.comp l6d_S hdiv).const_mul (24 * l6d_lam ^ 3)
  convert h using 1
  · funext s; simp [l6d_v21_xTildeOut]
  · rw [l6d_S, mul_div_cancel_left₀ _ hl]; simp only [l6d_D]; field_simp

/-- The Fuller switching function from `ζ` to `ζ²` along the flow from `q_out`:
`√3 τ (y₂ + y₁ τ/2 + τ²/12)`. -/
lemma l6d_RR23_flow_qOut (τ : ℝ) : RR (ζ - ζ ^ 2) (flow τ qOutCart ζ 2) =
    √3 * τ * ((qOutCart 1).im + (qOutCart 0).im * τ / 2 + τ ^ 2 / 12) := by
  obtain ⟨-, h2, -⟩ := qOutCart_normalization
  rw [RR_eq_re_mul_add_im_mul]
  simp [flow, ζ_re, ζ_im, ζ_sq_re, ζ_sq_im, h2]
  ring

/-- `χ̃₂₃(s, 0, x̃_out) = s Q(s)` with `Q > 0` on `[0, ∞)`. -/
noncomputable def l6d_Q (s : ℝ) : ℝ :=
  24 * l6d_lam ^ 2 * √3 * ((qOutCart 1).im + (qOutCart 0).im * (s / l6d_lam) / 2 +
    (s / l6d_lam) ^ 2 / 12)

lemma l6d_v23_xTildeOut (s : ℝ) : l6d_v23 (s, xTildeOut) = s * l6d_Q s := by
  have hl := l6d_lam_pos.ne'
  have h := l6d_flow_scale l6d_lam (s / l6d_lam) qOutCart ζ
  rw [mul_div_cancel₀ s hl] at h
  simp only [l6d_v23, l6d_fullerOfChart_xTildeOut, h]
  simp only [scale, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  rw [← Complex.ofReal_pow, RR_ofReal_mul_right, l6d_RR23_flow_qOut, l6d_Q]
  field_simp

lemma l6d_Q_pos {s : ℝ} (hs : 0 ≤ s) : 0 < l6d_Q s := by
  obtain ⟨hy1, -, hy2⟩ := qOutCart_signs
  have hl := l6d_lam_pos
  unfold l6d_Q
  have : 0 ≤ (qOutCart 0).im * (s / l6d_lam) / 2 := by positivity
  have : 0 < (qOutCart 1).im + (qOutCart 0).im * (s / l6d_lam) / 2 + (s / l6d_lam) ^ 2 / 12 := by
    positivity
  positivity

/-! ### The analytic switching time (Step 5) -/

open scoped ContDiff

/-- The implicit equation `χ̃₂₁(s, r₀, x̃₀) = 0` for the unknown `s`, as a function of
`((r₀, x̃₀), s)`. -/
noncomputable def l6d_Φ (v : (ℝ × (Fin 3 → ℝ)) × ℝ) : ℝ := l6d_chi21 (v.2, v.1.1, v.1.2)

/-- The base point `((0, x̃_out), s_sw,out)` of the implicit equation. -/
noncomputable def l6d_u0 : (ℝ × (Fin 3 → ℝ)) × ℝ := ((0, xTildeOut), l6d_S)

lemma l6d_analyticAt_Φ (x : Fin 3 → ℝ) (s : ℝ) : AnalyticAt ℝ l6d_Φ (((0 : ℝ), x), s) := by
  have h : AnalyticAt ℝ (fun v : (ℝ × (Fin 3 → ℝ)) × ℝ ↦ (v.2, v.1.1, v.1.2)) (((0 : ℝ), x), s) :=
    by fun_prop
  exact (l6d_analyticAt_chi21 s x).comp_of_eq h rfl

lemma l6d_Φ_u0 : l6d_Φ l6d_u0 = 0 := by
  simp only [l6d_Φ, l6d_u0, l6d_chi21_zero, l6d_v21_xTildeOut_S]

lemma l6d_contDiffAt_Φ : ContDiffAt ℝ ω l6d_Φ l6d_u0 :=
  (l6d_analyticAt_Φ xTildeOut l6d_S).contDiffAt

lemma l6d_fderiv_Φ_inr :
    fderiv ℝ l6d_Φ l6d_u0 ∘L .inr ℝ (ℝ × (Fin 3 → ℝ)) ℝ = (1 : ℝ →L[ℝ] ℝ).smulRight l6d_D := by
  have hF : HasFDerivAt l6d_Φ (fderiv ℝ l6d_Φ l6d_u0) l6d_u0 :=
    (l6d_analyticAt_Φ xTildeOut l6d_S).differentiableAt.hasFDerivAt
  have hin : HasFDerivAt (fun s : ℝ ↦ (((0 : ℝ), xTildeOut), s))
      (ContinuousLinearMap.inr ℝ (ℝ × (Fin 3 → ℝ)) ℝ) l6d_S :=
    (hasFDerivAt_const _ _).prodMk (hasFDerivAt_id _)
  have h1 := hF.comp l6d_S hin
  have h2 : HasFDerivAt (fun s : ℝ ↦ l6d_Φ (((0 : ℝ), xTildeOut), s))
      ((1 : ℝ →L[ℝ] ℝ).smulRight l6d_D) l6d_S := by
    have := l6d_hasDerivAt_v21_xTildeOut.hasFDerivAt
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun s ↦ ?_)
    simp [l6d_Φ, l6d_chi21_zero]
  exact h1.unique h2

lemma l6d_isInvertible_Φ :
    (fderiv ℝ l6d_Φ l6d_u0 ∘L .inr ℝ (ℝ × (Fin 3 → ℝ)) ℝ).IsInvertible := by
  rw [l6d_fderiv_Φ_inr]
  have hD := l6d_D_neg.ne
  refine ContinuousLinearMap.IsInvertible.of_inverse (g := (1 : ℝ →L[ℝ] ℝ).smulRight l6d_D⁻¹)
    ?_ ?_ <;> ext <;> simp [hD]

/-- **The analytic switching time** `s_sw(r₀, x̃₀)` (Step 5, TeX 11813–11821): the implicit function
of `χ̃₂₁(s, r₀, x̃₀) = 0` near `((0, x̃_out), s_sw,out)` (the analytic implicit function theorem,
`ContDiffAt.implicitFunction` with `n = ω`). -/
noncomputable def l6d_sSw : ℝ × (Fin 3 → ℝ) → ℝ :=
  l6d_contDiffAt_Φ.implicitFunction (by simp) l6d_isInvertible_Φ

lemma l6d_sSw_base : l6d_sSw (0, xTildeOut) = l6d_S :=
  l6d_contDiffAt_Φ.implicitFunction_apply_self (by simp) l6d_isInvertible_Φ

lemma l6d_eventually_chi21_sSw :
    ∀ᶠ p in 𝓝 ((0 : ℝ), xTildeOut), l6d_chi21 (l6d_sSw p, p.1, p.2) = 0 := by
  have h := l6d_contDiffAt_Φ.eventually_apply_implicitFunction (by simp) l6d_isInvertible_Φ
  rw [l6d_Φ_u0] at h
  exact h

lemma l6d_eventually_chi21_eq_zero_iff :
    ∀ᶠ v in 𝓝 l6d_u0, l6d_Φ v = 0 ↔ l6d_sSw v.1 = v.2 := by
  have h := l6d_contDiffAt_Φ.eventually_apply_eq_iff_implicitFunction (by simp)
    l6d_isInvertible_Φ
  rw [l6d_Φ_u0] at h
  exact h

lemma l6d_analyticAt_sSw : AnalyticAt ℝ l6d_sSw ((0 : ℝ), xTildeOut) :=
  (l6d_contDiffAt_Φ.contDiffAt_implicitFunction (by simp) l6d_isInvertible_Φ).analyticAt

/-! ### The switching structure near the fixed point -/

/-- The dual basis property of `sl2Dual`: `⟨sl2Dual M₁ M₂ M₃ c₁ c₂ c₃, M_k⟩ = c_k` (`k = 2, 3`)
when `T = ⟨M₁, [M₂, M₃]⟩ ≠ 0`. -/
lemma l6d_traceForm_sl2Dual (M₁ M₂ M₃ : Mat2) (c₁ c₂ c₃ : ℝ)
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
lemma l6d_switchingFn12_lieChart {p : ℝ × (Fin 3 → ℝ)} (h1 : 1 + p.1 * p.2 0 ≠ 0)
    (hZ1 : traceForm (controlMatrix (vertex 1)) (lieChart p).1 ≠ 0)
    (hZ2 : traceForm (controlMatrix (vertex 2)) (lieChart p).1 ≠ 0) :
    switchingFn 1 2 (lieChart p).2.2 (lieChart p).1 = 0 := by
  have hT : traceForm (lieChart p).1 (controlMatrix (vertex 1) * controlMatrix (vertex 2) -
      controlMatrix (vertex 2) * controlMatrix (vertex 1)) ≠ 0 := by
    rw [show (lieChart p).1 = lieX p.1 (p.2 0) from rfl, l6d_traceForm_lieX_bracket]
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

lemma l6d_eventually_chi23_zero :
    ∀ᶠ p in 𝓝 ((0 : ℝ), xTildeOut), l6d_chi23 (0, p.1, p.2) = 0 := by
  -- the denominators at the singular locus
  have hc : ∀ k : Fin 3, ContinuousAt (fun p : ℝ × (Fin 3 → ℝ) ↦
      traceForm (controlMatrix (vertex k)) (lieChart p).1) ((0 : ℝ), xTildeOut) := by
    intro k
    obtain ⟨h1, -, -⟩ := l6d_MatAn_lieChart (E := ℝ × (Fin 3 → ℝ)) (g := id)
      (x := ((0 : ℝ), xTildeOut)) analyticAt_id (by simp) (by norm_num)
    exact ((l6d_MatAn.const _).traceForm h1).continuousAt
  have h0 : ∀ k : Fin 3, traceForm (controlMatrix (vertex k)) (lieChart (0, xTildeOut)).1 ≠ 0 := by
    intro k; rw [l6d_lieChart_zero, l6d_traceForm_controlMatrix_J]; norm_num
  have h1c : ContinuousAt (fun p : ℝ × (Fin 3 → ℝ) ↦ 1 + p.1 * p.2 0) ((0 : ℝ), xTildeOut) := by
    fun_prop
  filter_upwards [(hc 1).eventually_ne (h0 1), (hc 2).eventually_ne (h0 2),
    h1c.eventually_ne (by simp : 1 + (0 : ℝ) * xTildeOut 0 ≠ 0)] with p hp1 hp2 hp3
  by_cases hr : p.1 = 0
  · simp only [l6d_chi23, l6d_chiT, hr, ite_true, l6d_v23, flow_zero]
    have : (fullerOfChart p.2 2).im = 0 := by simp [fullerOfChart]
    rw [RR_eq_re_mul_add_im_mul]
    simp [this, ζ_re, ζ_sq_re]
  · simp only [l6d_chi23, l6d_chiT, hr, ite_false, l6d_chiRaw, l6d_flowPt, zero_mul,
      ivf_vertexFlow_zero]
    rw [l6d_switchingFn12_lieChart hp3 hp1 hp2, zero_div]

/-- **The χ₂₃ check** (G14.5): for every `B > 0`, near the fixed point `χ̃₂₃(s, r₀, x̃₀) > 0` for
`0 < s ≤ B` (at `(0, x̃_out)` it is `s Q(s)` with `Q > 0`; one more division by `s` handles small
`s`, and compactness the rest). -/
lemma l6d_eventually_chi23_pos (B : ℝ) :
    ∀ᶠ p in 𝓝 ((0 : ℝ), xTildeOut), ∀ s ∈ Ioc 0 B, 0 < l6d_chi23 (s, p.1, p.2) := by
  set p₀ : ℝ × (Fin 3 → ℝ) := ((0 : ℝ), xTildeOut) with hp₀
  have han : AnalyticAt ℝ l6d_chi23 ((0 : ℝ), p₀) := l6d_analyticAt_chi23 0 xTildeOut
  -- division by `s`
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
  -- `H(0, p₀) = Q(0) > 0`
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
  -- near `(0, p₀)`: `χ̃₂₃ = s H` with `H > 0`
  have hnear : ∀ᶠ v in 𝓝 ((0 : ℝ), p₀), l6d_chi23 v = v.1 * H v ∧ 0 < H v := by
    filter_upwards [hHeq, continuousAt_const.eventually_lt hH.continuousAt hH0] with v h1 h2
    exact ⟨by simpa using h1, h2⟩
  rw [nhds_prod_eq] at hnear
  obtain ⟨pa, hpa, pb, hpb, hall⟩ := Filter.eventually_prod_iff.1 hnear
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff.1 hpa
  -- compactness on `[ε/2, B]`
  have htube : ∀ᶠ p in 𝓝 p₀, ∀ s ∈ Icc (ε / 2) B, 0 < l6d_chi23 (s, p.1, p.2) := by
    refine (isCompact_Icc).eventually_forall_of_forall_eventually fun s hs ↦ ?_
    have hca : ContinuousAt (fun z : (ℝ × (Fin 3 → ℝ)) × ℝ ↦ l6d_chi23 (z.2, z.1.1, z.1.2))
        (p₀, s) :=
      ((l6d_analyticAt_chi23 s xTildeOut).comp_of_eq (by fun_prop :
        AnalyticAt ℝ (fun z : (ℝ × (Fin 3 → ℝ)) × ℝ ↦ (z.2, z.1.1, z.1.2)) (p₀, s)) rfl
        ).continuousAt
    have hpos : 0 < l6d_chi23 (s, p₀.1, p₀.2) := by
      rw [hp₀, l6d_chi23_zero, l6d_v23_xTildeOut]
      exact mul_pos (by linarith [hs.1]) (l6d_Q_pos (by linarith [hs.1]))
    exact continuousAt_const.eventually_lt hca hpos
  filter_upwards [hpb, htube] with p hp hpt s hs
  by_cases hsε : s < ε / 2
  · have hs' : pa s := hεb (by rw [Real.dist_eq, sub_zero, abs_of_pos hs.1]; linarith)
    obtain ⟨h1, h2⟩ := hall hs' hp
    rw [h1]
    exact mul_pos hs.1 h2
  · exact hpt s ⟨not_lt.1 hsε, hs.2⟩

/-- **The least positive zero of `χ̃₂₁` near the fixed point** (TeX 11807–11821): there is
`δ ∈ (0, s_sw,out)` such that for `(r₀, x̃₀)` near `(0, x̃_out)`, `s_sw(r₀, x̃₀) ∈ (s_sw,out - δ,
s_sw,out + δ)` is a zero of `χ̃₂₁(·, r₀, x̃₀)`, which is positive on `[0, s_sw)` and negative on
`(s_sw, s_sw,out + δ]` (at the fixed point: `s = 0` is not a zero and the least positive zero
`s_sw,out` is simple; the implicit function theorem and compactness of `[0, s_sw,out]`). -/
lemma l6d_zero_structure : ∃ δ > 0, δ < l6d_S ∧ ∀ᶠ p in 𝓝 ((0 : ℝ), xTildeOut),
    l6d_sSw p ∈ Ioo (l6d_S - δ) (l6d_S + δ) ∧ l6d_Φ (p, l6d_sSw p) = 0 ∧
      (∀ s ∈ Ico 0 (l6d_sSw p), 0 < l6d_Φ (p, s)) ∧
      ∀ s ∈ Ioc (l6d_sSw p) (l6d_S + δ), l6d_Φ (p, s) < 0 := by
  set p₀ : ℝ × (Fin 3 → ℝ) := ((0 : ℝ), xTildeOut) with hp₀
  have hS := l6d_S_pos
  -- the uniqueness box of the implicit function theorem
  have hbox := l6d_eventually_chi21_eq_zero_iff
  rw [l6d_u0, nhds_prod_eq] at hbox
  obtain ⟨pa, hpa, pb, hpb, hall⟩ := Filter.eventually_prod_iff.1 hbox
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff.1 hpb
  set δ := min (ε / 2) (l6d_S / 2) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by linarith)
  have hδε : δ < ε := (min_le_left _ _).trans_lt (by linarith)
  have hδS : δ < l6d_S := (min_le_right _ _).trans_lt (by linarith)
  have hin : ∀ s ∈ Icc (l6d_S - δ) (l6d_S + δ), pb s := fun s hs ↦
    hεb (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hs.1, hs.2])
  refine ⟨δ, hδ0, hδS, ?_⟩
  have hjoint : ∀ s, ContinuousAt l6d_Φ (p₀, s) := fun s ↦
    (l6d_analyticAt_Φ xTildeOut s).continuousAt
  -- positivity on `[0, S - δ]`
  have hpos : ∀ᶠ p in 𝓝 p₀, ∀ s ∈ Icc 0 (l6d_S - δ), 0 < l6d_Φ (p, s) := by
    refine isCompact_Icc.eventually_forall_of_forall_eventually fun s hs ↦ ?_
    have h0 : 0 < l6d_Φ (p₀, s) := by
      simp only [l6d_Φ, hp₀, l6d_chi21_zero]
      exact l6d_v21_xTildeOut_pos hs.1 (by linarith [hs.2])
    exact continuousAt_const.eventually_lt (hjoint s) h0
  -- negativity at `S + δ`
  have hneg : ∀ᶠ p in 𝓝 p₀, l6d_Φ (p, l6d_S + δ) < 0 := by
    have h0 : l6d_Φ (p₀, l6d_S + δ) < 0 := by
      simp only [l6d_Φ, hp₀, l6d_chi21_zero]
      exact l6d_v21_xTildeOut_neg (by linarith)
    have hc : ContinuousAt (fun p ↦ l6d_Φ (p, l6d_S + δ)) p₀ :=
      (hjoint _).comp_of_eq (by fun_prop) rfl
    exact hc.eventually_lt continuousAt_const h0
  -- continuity on `[S - δ, S + δ]`
  have hcont : ∀ᶠ p in 𝓝 p₀, ∀ s ∈ Icc (l6d_S - δ) (l6d_S + δ), AnalyticAt ℝ l6d_Φ (p, s) := by
    refine isCompact_Icc.eventually_forall_of_forall_eventually fun s _ ↦ ?_
    exact (l6d_analyticAt_Φ xTildeOut s).eventually_analyticAt
  have hsw : ∀ᶠ p in 𝓝 p₀, l6d_sSw p ∈ Ioo (l6d_S - δ) (l6d_S + δ) := by
    have hc := l6d_analyticAt_sSw.continuousAt
    rw [← hp₀] at hc
    refine hc.preimage_mem_nhds (isOpen_Ioo.mem_nhds ?_)
    rw [hp₀, l6d_sSw_base]
    constructor <;> linarith
  filter_upwards [hpa, hpos, hneg, hcont, hsw, l6d_eventually_chi21_sSw] with p hpa' hp1 hp2 hp3
    hp4 hp5
  have hz : l6d_Φ (p, l6d_sSw p) = 0 := hp5
  have hcon : ContinuousOn (fun s ↦ l6d_Φ (p, s)) (Icc (l6d_S - δ) (l6d_S + δ)) := fun s hs ↦
    ((hp3 s hs).continuousAt.comp_of_eq (by fun_prop) rfl).continuousWithinAt
  -- a zero in the box is `s_sw`
  have huniq : ∀ s ∈ Icc (l6d_S - δ) (l6d_S + δ), l6d_Φ (p, s) = 0 → l6d_sSw p = s :=
    fun s hs h ↦ (hall hpa' (hin s hs)).1 h
  refine ⟨hp4, hz, fun s hs ↦ ?_, fun s hs ↦ ?_⟩
  · by_cases hsδ : s ≤ l6d_S - δ
    · exact hp1 s ⟨hs.1, hsδ⟩
    by_contra hle
    push Not at hle hsδ
    have hsub : Icc (l6d_S - δ) s ⊆ Icc (l6d_S - δ) (l6d_S + δ) :=
      Icc_subset_Icc le_rfl (by linarith [hs.2, hp4.2])
    have hS0 : 0 < l6d_Φ (p, l6d_S - δ) := hp1 _ ⟨by linarith, le_rfl⟩
    obtain ⟨s', hs', hs'0⟩ := intermediate_value_Icc' hsδ.le (hcon.mono hsub) ⟨hle, hS0.le⟩
    have := huniq s' (hsub hs') hs'0
    linarith [hs'.2, hs.2]
  · by_contra hle
    push Not at hle
    have hsub : Icc s (l6d_S + δ) ⊆ Icc (l6d_S - δ) (l6d_S + δ) :=
      Icc_subset_Icc (by linarith [hs.1, hp4.1]) le_rfl
    obtain ⟨s', hs', hs'0⟩ := intermediate_value_Icc' hs.2 (hcon.mono hsub) ⟨hp2.le, hle⟩
    have := huniq s' (hsub hs') hs'0
    linarith [hs'.1, hs.1]

/-! ### The image point and its divided entries (Steps 6–7) -/

/-- The flow point rotated by `Ad_{R⁻¹}`, `Y_sw = Ad_{R⁻¹} Y(s r₀)` at `s = s_sw` (Step 6). -/
noncomputable def l6d_Xi (p : ℝ × ℝ × (Fin 3 → ℝ)) : iso_PhasePt :=
  iso_adRinvPow 1 (l6d_flowPt p)

/-- The entries of `X_sw - J` and `Λ₁sw + (3/2) J` read off by the chart and the determinant
relations. -/
noncomputable def l6d_fa (p : ℝ × ℝ × (Fin 3 → ℝ)) : ℝ := (l6d_Xi p).1 0 0
noncomputable def l6d_fb (p : ℝ × ℝ × (Fin 3 → ℝ)) : ℝ := (l6d_Xi p).1 1 0 - 1
noncomputable def l6d_fe (p : ℝ × ℝ × (Fin 3 → ℝ)) : ℝ := (l6d_Xi p).1 0 1 + 1
noncomputable def l6d_fc (p : ℝ × ℝ × (Fin 3 → ℝ)) : ℝ := (l6d_Xi p).2.1 0 0
noncomputable def l6d_fd (p : ℝ × ℝ × (Fin 3 → ℝ)) : ℝ := (l6d_Xi p).2.1 1 0 + 3 / 2
noncomputable def l6d_ff (p : ℝ × ℝ × (Fin 3 → ℝ)) : ℝ := (l6d_Xi p).2.1 0 1 - 3 / 2

/-- `w(s, x̃) = ζ z(s, z(x̃), ζ)`, the rotated Fuller flow. -/
noncomputable def l6d_w (q : ℝ × (Fin 3 → ℝ)) : Fin 3 → ℂ := ζ • flow q.1 (fullerOfChart q.2) ζ

/-- The limits of the divided entries: `2 Im w₁`, `2 Re w₁`, `6 Re w₂`, `-6 Im w₂`. -/
noncomputable def l6d_va (q : ℝ × (Fin 3 → ℝ)) : ℝ := 2 * (l6d_w q 0).im
noncomputable def l6d_vb (q : ℝ × (Fin 3 → ℝ)) : ℝ := 2 * (l6d_w q 0).re
noncomputable def l6d_vc (q : ℝ × (Fin 3 → ℝ)) : ℝ := 6 * (l6d_w q 1).re
noncomputable def l6d_vd (q : ℝ × (Fin 3 → ℝ)) : ℝ := -(6 * (l6d_w q 1).im)

lemma l6d_MatAn_Xi (s : ℝ) (x : Fin 3 → ℝ) :
    l6d_MatAn (fun p ↦ (l6d_Xi p).1) (s, 0, x) ∧ l6d_MatAn (fun p ↦ (l6d_Xi p).2.1) (s, 0, x) := by
  obtain ⟨h1, h2, -⟩ := l6d_MatAn_flowPt s x
  simp only [l6d_Xi, iso_adRinvPow, pow_one]
  exact ⟨((l6d_MatAn.const _).mul h1).mul (l6d_MatAn.const _),
    ((l6d_MatAn.const _).mul h2).mul (l6d_MatAn.const _)⟩

lemma l6d_Rinv_J_R : R⁻¹ * J * R = J := by
  rw [Matrix.mul_assoc, poly_J_mul_R, ← Matrix.mul_assoc, poly_inv_mul_R, Matrix.one_mul]

lemma l6d_Xi_zero (s : ℝ) (x : Fin 3 → ℝ) :
    l6d_Xi (s, 0, x) = (J, (-(3 / 2) : ℝ) • J, 0) := by
  simp only [l6d_Xi, l6d_flowPt_zero, iso_adRinvPow, pow_one, Matrix.mul_smul, Matrix.smul_mul,
    l6d_Rinv_J_R, Matrix.mul_zero, Matrix.zero_mul]

lemma l6d_analyticAt_entries (s : ℝ) (x : Fin 3 → ℝ) :
    AnalyticAt ℝ l6d_fa (s, 0, x) ∧ AnalyticAt ℝ l6d_fb (s, 0, x) ∧
      AnalyticAt ℝ l6d_fe (s, 0, x) ∧ AnalyticAt ℝ l6d_fc (s, 0, x) ∧
      AnalyticAt ℝ l6d_fd (s, 0, x) ∧ AnalyticAt ℝ l6d_ff (s, 0, x) := by
  obtain ⟨h1, h2⟩ := l6d_MatAn_Xi s x
  exact ⟨h1 0 0, (h1 1 0).sub analyticAt_const, (h1 0 1).add analyticAt_const, h2 0 0,
    (h2 1 0).add analyticAt_const, (h2 0 1).sub analyticAt_const⟩

lemma l6d_entries_zero (s : ℝ) (x : Fin 3 → ℝ) :
    l6d_fa (s, 0, x) = 0 ∧ l6d_fb (s, 0, x) = 0 ∧ l6d_fe (s, 0, x) = 0 ∧
      l6d_fc (s, 0, x) = 0 ∧ l6d_fd (s, 0, x) = 0 ∧ l6d_ff (s, 0, x) = 0 := by
  simp only [l6d_fa, l6d_fb, l6d_fe, l6d_fc, l6d_fd, l6d_ff, l6d_Xi_zero]
  simp [J]

/-- The chart takes values in `𝔰𝔩₂(ℝ)³`. -/
lemma l6d_lieChart_traceless (p : ℝ × (Fin 3 → ℝ)) :
    (lieChart p).1.trace = 0 ∧ (lieChart p).2.1.trace = 0 ∧ (lieChart p).2.2.trace = 0 := by
  refine ⟨by simp [lieChart, lieX, Matrix.trace_fin_two], by simp [lieChart, lieΛ₁,
    Matrix.trace_fin_two], ?_⟩
  simp only [lieChart, lieΛR, sl2Dual, Matrix.trace_smul, Matrix.trace_add, irt_trace_bracket,
    smul_zero, add_zero]

lemma l6d_flowPt_traceless (p : ℝ × ℝ × (Fin 3 → ℝ)) :
    (l6d_flowPt p).1.trace = 0 ∧ (l6d_flowPt p).2.1.trace = 0 ∧ (l6d_flowPt p).2.2.trace = 0 := by
  obtain ⟨h1, h2, h3⟩ := l6d_lieChart_traceless (p.2.1, p.2.2)
  exact irt_vertexFlow_traceless 1 h1 h2 h3 _

/-- The Fuller coordinates of the image point: `ẑ(Y_sw) = ζ ẑ(Y(s r₀))`. -/
lemma l6d_fullerCoords_Xi (p : ℝ × ℝ × (Fin 3 → ℝ)) :
    fullerCoords (l6d_Xi p) = ζ • fullerCoords (l6d_flowPt p) := by
  obtain ⟨h1, h2, h3⟩ := l6d_flowPt_traceless p
  exact (fullerCoords_adR (l6d_flowPt p) h1 h2 h3).2

lemma l6d_fullerCoords_Xi_zero (p : ℝ × ℝ × (Fin 3 → ℝ)) :
    (fullerCoords (l6d_Xi p) 0).im = l6d_fa p / 2 ∧
      (fullerCoords (l6d_Xi p) 0).re = (l6d_fe p + l6d_fb p) / 4 := by
  constructor
  · simp only [fullerCoords, cayleyZ, Fin.isValue, neg_mul, Matrix.cons_val_zero, div_ofNat_im,
      l6d_fa]
  · simp only [fullerCoords, cayleyZ, Fin.isValue, neg_mul, Matrix.cons_val_zero, div_ofNat_re,
      l6d_fe, l6d_fb, add_add_sub_cancel]
    ring

lemma l6d_fullerCoords_Xi_one (p : ℝ × ℝ × (Fin 3 → ℝ)) :
    (fullerCoords (l6d_Xi p) 1).re = l6d_fc p / 6 ∧
      (fullerCoords (l6d_Xi p) 1).im = -(l6d_ff p + l6d_fd p) / 12 := by
  constructor
  · simp only [fullerCoords, cayleyZ, Fin.isValue, neg_mul, Matrix.cons_val_one,
      Matrix.cons_val_zero, div_ofNat_re, neg_re, mul_re, I_re, zero_mul, I_im, one_mul, zero_sub,
      neg_neg, l6d_fc]
  · simp only [fullerCoords, cayleyZ, Fin.isValue, neg_mul, Matrix.cons_val_one,
      Matrix.cons_val_zero, div_ofNat_im, neg_im, mul_im, I_re, zero_mul, I_im, one_mul, zero_add,
      l6d_ff, l6d_fd, sub_add_add_cancel, neg_add_rev]
    ring

/-- Lemma 14.2.3, rotated: `ẑ_k(Y_sw) = r₀^{k+1} w_k(s) + O(r₀^{k+2})`. -/
lemma l6d_isBigO_fullerCoords_Xi (s : ℝ) (x : Fin 3 → ℝ) (k : Fin 3) :
    (fun r : ℝ ↦ fullerCoords (l6d_Xi (s, r, x)) k - (r : ℂ) ^ (k.val + 1) * l6d_w (s, x) k)
      =O[𝓝[>] 0] (fun r ↦ r ^ (k.val + 2)) := by
  have h := (lemma14_2_3 x s k).const_mul_left ζ
  refine h.congr_left fun r ↦ ?_
  simp only [l6d_fullerCoords_Xi, l6d_w, Pi.smul_apply, smul_eq_mul, l6d_flowPt]
  ring

/-- A real part (or imaginary part) of `O(g)` is `O(g)`. -/
lemma l6d_isBigO_re {f : ℝ → ℂ} {g : ℝ → ℝ} {l : Filter ℝ} (h : f =O[l] g) :
    (fun r ↦ (f r).re) =O[l] g :=
  (isBigO_of_le l fun r ↦ by
    simpa [Real.norm_eq_abs] using Complex.abs_re_le_norm (f r)).trans h

lemma l6d_isBigO_im {f : ℝ → ℂ} {g : ℝ → ℝ} {l : Filter ℝ} (h : f =O[l] g) :
    (fun r ↦ (f r).im) =O[l] g :=
  (isBigO_of_le l fun r ↦ by
    simpa [Real.norm_eq_abs] using Complex.abs_im_le_norm (f r)).trans h

lemma l6d_isBigO_fa (s : ℝ) (x : Fin 3 → ℝ) :
    (fun r ↦ l6d_fa (s, r, x) - r ^ 1 * l6d_va (s, x)) =O[𝓝[>] 0] (fun r ↦ r ^ 2) := by
  have h := (l6d_isBigO_im (l6d_isBigO_fullerCoords_Xi s x 0)).const_mul_left 2
  refine h.congr_left fun r ↦ ?_
  have := (l6d_fullerCoords_Xi_zero (s, r, x)).1
  simp only [Fin.val_zero, zero_add, pow_one, Complex.sub_im, Complex.im_ofReal_mul] at this ⊢
  rw [this, l6d_va]
  ring

lemma l6d_isBigO_feb (s : ℝ) (x : Fin 3 → ℝ) :
    (fun r ↦ l6d_fe (s, r, x) + l6d_fb (s, r, x) - r * (2 * l6d_vb (s, x))) =O[𝓝[>] 0]
      (fun r ↦ r ^ 2) := by
  have h := (l6d_isBigO_re (l6d_isBigO_fullerCoords_Xi s x 0)).const_mul_left 4
  refine h.congr_left fun r ↦ ?_
  have := (l6d_fullerCoords_Xi_zero (s, r, x)).2
  simp only [Fin.val_zero, zero_add, pow_one, Complex.sub_re, Complex.re_ofReal_mul] at this ⊢
  rw [this, l6d_vb]
  ring

lemma l6d_isBigO_fc (s : ℝ) (x : Fin 3 → ℝ) :
    (fun r ↦ l6d_fc (s, r, x) - r ^ 2 * l6d_vc (s, x)) =O[𝓝[>] 0] (fun r ↦ r ^ 3) := by
  have h := (l6d_isBigO_re (l6d_isBigO_fullerCoords_Xi s x 1)).const_mul_left 6
  refine h.congr_left fun r ↦ ?_
  have := (l6d_fullerCoords_Xi_one (s, r, x)).1
  simp only [Fin.val_one, Complex.sub_re] at this ⊢
  rw [← Complex.ofReal_pow, Complex.re_ofReal_mul, this, l6d_vc]
  ring

lemma l6d_isBigO_ffd (s : ℝ) (x : Fin 3 → ℝ) :
    (fun r ↦ l6d_ff (s, r, x) + l6d_fd (s, r, x) - r ^ 2 * (2 * l6d_vd (s, x))) =O[𝓝[>] 0]
      (fun r ↦ r ^ 3) := by
  have h := (l6d_isBigO_im (l6d_isBigO_fullerCoords_Xi s x 1)).const_mul_left (-12)
  refine h.congr_left fun r ↦ ?_
  have := (l6d_fullerCoords_Xi_one (s, r, x)).2
  simp only [Fin.val_one, Complex.sub_im] at this ⊢
  rw [← Complex.ofReal_pow, Complex.im_ofReal_mul, this, l6d_vd]
  ring

/-- The determinant relations on the image point (`det X = 1`, `det Λ₁ = 9/4`, traceless). -/
lemma l6d_det_relations (p : ℝ × ℝ × (Fin 3 → ℝ)) (h1 : 1 + p.2.1 * p.2.2 0 ≠ 0)
    (h2 : 3 / 2 - p.2.1 ^ 2 * p.2.2 2 ≠ 0) :
    l6d_fb p - l6d_fe p = l6d_fa p ^ 2 + l6d_fe p * l6d_fb p ∧
      3 / 2 * (l6d_ff p - l6d_fd p) = l6d_fc p ^ 2 + l6d_ff p * l6d_fd p := by
  obtain ⟨t1, t2, -⟩ := l6d_flowPt_traceless p
  have hdX : (l6d_Xi p).1.det = 1 := by
    simp only [l6d_Xi, iso_adRinvPow, pow_one]
    rw [poly_det_conj poly_R_mul_inv, l6d_flowPt, l6d_vertexFlow_det_fst]
    simp only [lieChart, lieX, Matrix.det_fin_two_of]
    field_simp
    ring
  have hdΛ : (l6d_Xi p).2.1.det = 9 / 4 := by
    simp only [l6d_Xi, iso_adRinvPow, pow_one]
    rw [poly_det_conj poly_R_mul_inv, l6d_flowPt, l6d_vertexFlow_det_snd]
    simp only [lieChart, lieΛ₁, Matrix.det_fin_two_of]
    rw [show (-(3 / 2) + p.2.1 ^ 2 * p.2.2 2) = -(3 / 2 - p.2.1 ^ 2 * p.2.2 2) by ring]
    generalize 3 / 2 - p.2.1 ^ 2 * p.2.2 2 = D at h2 ⊢
    field_simp
    ring
  have htX : (l6d_Xi p).1.trace = 0 := by
    simp only [l6d_Xi, iso_adRinvPow, pow_one]
    rw [poly_trace_conj poly_R_mul_inv, t1]
  have htΛ : (l6d_Xi p).2.1.trace = 0 := by
    simp only [l6d_Xi, iso_adRinvPow, pow_one]
    rw [poly_trace_conj poly_R_mul_inv, t2]
  rw [Matrix.trace_fin_two] at htX htΛ
  rw [Matrix.det_fin_two] at hdX hdΛ
  simp only [l6d_fa, l6d_fb, l6d_fe, l6d_fc, l6d_fd, l6d_ff]
  constructor
  · have : (l6d_Xi p).1 1 1 = -(l6d_Xi p).1 0 0 := by linarith
    rw [this] at hdX
    linear_combination hdX
  · have : (l6d_Xi p).2.1 1 1 = -(l6d_Xi p).2.1 0 0 := by linarith
    rw [this] at hdΛ
    linear_combination hdΛ

/-- If `v (κ + v/4) = w` with `v → 0` and `w = O(g)`, then `v = O(g)`. -/
lemma l6d_isBigO_of_quad {v w g : ℝ → ℝ} {κ : ℝ} (hκ : 0 < κ) (hv : Tendsto v (𝓝[>] 0) (𝓝 0))
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
lemma l6d_isBigO_of_sub {f : ℝ → ℝ} {c : ℝ} {k : ℕ}
    (h : (fun r ↦ f r - r ^ k * c) =O[𝓝[>] 0] (fun r ↦ r ^ (k + 1))) :
    f =O[𝓝[>] 0] (fun r ↦ r ^ k) := by
  have h4 : (fun r : ℝ ↦ r ^ (k + 1)) =O[𝓝[>] 0] (fun r ↦ r ^ k) :=
    ((isLittleO_pow_pow (by omega : k < k + 1)).isBigO).mono nhdsWithin_le_nhds
  have h3 : (fun r : ℝ ↦ r ^ k * c) =O[𝓝[>] 0] (fun r ↦ r ^ k) := by
    simpa [mul_comm] using (isBigO_refl (fun r : ℝ ↦ r ^ k) (𝓝[>] 0)).const_mul_left c
  simpa using (h.trans h4).add h3

lemma l6d_eventually_den (x : Fin 3 → ℝ) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), 1 + r * x 0 ≠ 0 ∧ 3 / 2 - r ^ 2 * x 2 ≠ 0 := by
  have h1 : ∀ᶠ r in 𝓝 (0 : ℝ), 1 + r * x 0 ≠ 0 :=
    (by fun_prop : ContinuousAt (fun r : ℝ ↦ 1 + r * x 0) 0).eventually_ne (by simp)
  have h2 : ∀ᶠ r in 𝓝 (0 : ℝ), 3 / 2 - r ^ 2 * x 2 ≠ 0 :=
    (by fun_prop : ContinuousAt (fun r : ℝ ↦ 3 / 2 - r ^ 2 * x 2) 0).eventually_ne (by norm_num)
  exact nhdsWithin_le_nhds (h1.and h2)

/-- An entry vanishing at `r₀ = 0` tends to `0` as `r₀ → 0⁺`. -/
lemma l6d_tendsto_entry {f : ℝ × ℝ × (Fin 3 → ℝ) → ℝ} {s : ℝ} {x : Fin 3 → ℝ}
    (hf : AnalyticAt ℝ f (s, 0, x)) (h0 : f (s, 0, x) = 0) :
    Tendsto (fun r ↦ f (s, r, x)) (𝓝[>] 0) (𝓝 0) := by
  have hc : ContinuousAt (fun r : ℝ ↦ f (s, r, x)) 0 :=
    hf.continuousAt.comp_of_eq (by fun_prop) rfl
  have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  rwa [h0] at this

lemma l6d_isBigO_fb (s : ℝ) (x : Fin 3 → ℝ) :
    (fun r ↦ l6d_fb (s, r, x) - r ^ 1 * l6d_vb (s, x)) =O[𝓝[>] 0] (fun r ↦ r ^ 2) := by
  obtain ⟨ha, hb, he, -, -, -⟩ := l6d_analyticAt_entries s x
  obtain ⟨ha0, hb0, he0, -, -, -⟩ := l6d_entries_zero s x
  have hu := l6d_isBigO_feb s x
  have hfa : (fun r ↦ l6d_fa (s, r, x)) =O[𝓝[>] 0] (fun r ↦ r ^ 1) :=
    l6d_isBigO_of_sub (l6d_isBigO_fa s x)
  have hu1 : (fun r ↦ l6d_fe (s, r, x) + l6d_fb (s, r, x)) =O[𝓝[>] 0] (fun r ↦ r ^ 1) :=
    l6d_isBigO_of_sub (c := 2 * l6d_vb (s, x)) (by simpa using hu)
  have hw : (fun r ↦ l6d_fa (s, r, x) ^ 2 + (l6d_fe (s, r, x) + l6d_fb (s, r, x)) ^ 2 / 4)
      =O[𝓝[>] 0] (fun r ↦ r ^ 2) := by
    have h1 := hfa.mul hfa
    have h2 := (hu1.mul hu1).const_mul_left (1 / 4)
    refine (h1.add h2).congr (fun r ↦ by ring) (fun r ↦ by ring)
  have hv : Tendsto (fun r ↦ l6d_fb (s, r, x) - l6d_fe (s, r, x)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (l6d_tendsto_entry hb hb0).sub (l6d_tendsto_entry he he0)
  have hq : ∀ᶠ r in 𝓝[>] (0 : ℝ), (l6d_fb (s, r, x) - l6d_fe (s, r, x)) *
      (1 + (l6d_fb (s, r, x) - l6d_fe (s, r, x)) / 4) =
        l6d_fa (s, r, x) ^ 2 + (l6d_fe (s, r, x) + l6d_fb (s, r, x)) ^ 2 / 4 := by
    filter_upwards [l6d_eventually_den x] with r ⟨h1, h2⟩
    have := (l6d_det_relations (s, r, x) h1 h2).1
    linear_combination this
  have hvO := l6d_isBigO_of_quad one_pos hv hq hw
  refine ((hu.const_mul_left (1 / 2)).add (hvO.const_mul_left (1 / 2))).congr_left fun r ↦ ?_
  ring

lemma l6d_isBigO_fd (s : ℝ) (x : Fin 3 → ℝ) :
    (fun r ↦ l6d_fd (s, r, x) - r ^ 2 * l6d_vd (s, x)) =O[𝓝[>] 0] (fun r ↦ r ^ 3) := by
  obtain ⟨-, -, -, -, hd, hf⟩ := l6d_analyticAt_entries s x
  obtain ⟨-, -, -, -, hd0, hf0⟩ := l6d_entries_zero s x
  have hu := l6d_isBigO_ffd s x
  have hfc : (fun r ↦ l6d_fc (s, r, x)) =O[𝓝[>] 0] (fun r ↦ r ^ 2) :=
    l6d_isBigO_of_sub (l6d_isBigO_fc s x)
  have hu1 : (fun r ↦ l6d_ff (s, r, x) + l6d_fd (s, r, x)) =O[𝓝[>] 0] (fun r ↦ r ^ 2) :=
    l6d_isBigO_of_sub (c := 2 * l6d_vd (s, x)) (by simpa using hu)
  have h43 : (fun r : ℝ ↦ r ^ 2 * r ^ 2) =O[𝓝[>] 0] (fun r ↦ r ^ 3) := by
    refine ((isLittleO_pow_pow (by norm_num : 3 < 4)).isBigO.mono nhdsWithin_le_nhds).congr_left
      fun r ↦ by ring
  have hw : (fun r ↦ l6d_fc (s, r, x) ^ 2 + (l6d_ff (s, r, x) + l6d_fd (s, r, x)) ^ 2 / 4)
      =O[𝓝[>] 0] (fun r ↦ r ^ 3) := by
    have h1 := (hfc.mul hfc).trans h43
    have h2 := ((hu1.mul hu1).trans h43).const_mul_left (1 / 4)
    refine (h1.add h2).congr_left (fun r ↦ by ring)
  have hv : Tendsto (fun r ↦ l6d_ff (s, r, x) - l6d_fd (s, r, x)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (l6d_tendsto_entry hf hf0).sub (l6d_tendsto_entry hd hd0)
  have hq : ∀ᶠ r in 𝓝[>] (0 : ℝ), (l6d_ff (s, r, x) - l6d_fd (s, r, x)) *
      (3 / 2 + (l6d_ff (s, r, x) - l6d_fd (s, r, x)) / 4) =
        l6d_fc (s, r, x) ^ 2 + (l6d_ff (s, r, x) + l6d_fd (s, r, x)) ^ 2 / 4 := by
    filter_upwards [l6d_eventually_den x] with r ⟨h1, h2⟩
    have := (l6d_det_relations (s, r, x) h1 h2).2
    linear_combination this
  have hvO := l6d_isBigO_of_quad (by norm_num) hv hq hw
  refine ((hu.const_mul_left (1 / 2)).add (hvO.const_mul_left (-(1 / 2)))).congr_left fun r ↦ ?_
  ring

/-- The divided entries `(X_sw - J)₁₁/r₀`, `(X_sw - J)₂₁/r₀`, `(Λ₁sw + (3/2) J)₁₁/r₀²`,
`(Λ₁sw + (3/2) J)₂₁/r₀²` (Step 7, G14.7), analytic near `r₀ = 0`. -/
noncomputable def l6d_qa : ℝ × ℝ × (Fin 3 → ℝ) → ℝ := l6d_divR l6d_fa 1 l6d_va
noncomputable def l6d_qb : ℝ × ℝ × (Fin 3 → ℝ) → ℝ := l6d_divR l6d_fb 1 l6d_vb
noncomputable def l6d_qc : ℝ × ℝ × (Fin 3 → ℝ) → ℝ := l6d_divR l6d_fc 2 l6d_vc
noncomputable def l6d_qd : ℝ × ℝ × (Fin 3 → ℝ) → ℝ := l6d_divR l6d_fd 2 l6d_vd

lemma l6d_analyticAt_divided (s : ℝ) (x : Fin 3 → ℝ) :
    AnalyticAt ℝ l6d_qa (s, 0, x) ∧ AnalyticAt ℝ l6d_qb (s, 0, x) ∧
      AnalyticAt ℝ l6d_qc (s, 0, x) ∧ AnalyticAt ℝ l6d_qd (s, 0, x) := by
  have h := l6d_analyticAt_entries
  exact ⟨l6d_analyticAt_divR (fun s x ↦ (h s x).1) 1 l6d_isBigO_fa s x,
    l6d_analyticAt_divR (fun s x ↦ (h s x).2.1) 1 l6d_isBigO_fb s x,
    l6d_analyticAt_divR (fun s x ↦ (h s x).2.2.2.1) 2 l6d_isBigO_fc s x,
    l6d_analyticAt_divR (fun s x ↦ (h s x).2.2.2.2.1) 2 l6d_isBigO_fd s x⟩

/-! ### The extended map in the chart (Steps 8–9) -/

lemma l6d_fullerOfChart_ne_zero (x : Fin 3 → ℝ) : fullerOfChart x ≠ 0 := by
  intro h
  have := congrArg (fun z : Fin 3 → ℂ ↦ (z 0).im) h
  simp [fullerOfChart] at this

lemma l6d_ham_sub (z : Fin 3 → ℂ) (u v : ℂ) : ham z u - ham z v = RR (u - v) (z 2) := by
  simp only [ham, RR_eq_re_mul_add_im_mul, Complex.sub_re, Complex.sub_im]
  ring

/-- **The Fuller–Poincaré map from `z(x̃)`** (Step 9): if along the flow with control `ζ` from
`z(x̃)` the switching function to `1` is positive on `[0, σ)`, vanishes at `σ` and is negative
just after, and the one to `ζ²` is positive on `(0, B]`, then the first control of `z(x̃)` is
`ζ`, its first switching time is `σ`, and `F(z(x̃)) = z(σ, z(x̃), ζ)`. -/
lemma l6d_poincare_eq {x : Fin 3 → ℝ} {σ B : ℝ} (hσ : 0 < σ) (hσB : σ < B)
    (h21pos : ∀ s ∈ Ico 0 σ, 0 < l6d_v21 (s, x)) (h21zero : l6d_v21 (σ, x) = 0)
    (h21neg : ∀ s ∈ Ioc σ B, l6d_v21 (s, x) < 0) (h23 : ∀ s ∈ Ioc 0 B, 0 < l6d_v23 (s, x)) :
    poincare (fullerOfChart x) = flow σ (fullerOfChart x) ζ := by
  set z := fullerOfChart x with hz
  have hz0 : z ≠ 0 := l6d_fullerOfChart_ne_zero x
  have h1 : ∀ t, ham (flow t z ζ) ζ - ham (flow t z ζ) 1 = l6d_v21 (t, x) / 24 := fun t ↦ by
    rw [l6d_ham_sub, l6d_v21]; ring
  have h2 : ∀ t, ham (flow t z ζ) ζ - ham (flow t z ζ) (ζ ^ 2) = l6d_v23 (t, x) / 24 := fun t ↦ by
    rw [l6d_ham_sub, l6d_v23]; ring
  have h23zero : l6d_v23 (0, x) = 0 := by
    simp only [l6d_v23, flow_zero]
    have : (fullerOfChart x 2).im = 0 := by simp [fullerOfChart]
    rw [RR_eq_re_mul_add_im_mul]
    simp [this, ζ_re, ζ_sq_re]
  -- `ζ` is optimal on `[0, σ]`
  have hopt : ∀ t ∈ Icc 0 σ, ∀ v ∈ VT, ham (flow t z ζ) v ≤ ham (flow t z ζ) ζ := by
    intro t ht v hv
    rcases mem_VT.1 hv with rfl | rfl | rfl
    · have : 0 ≤ l6d_v21 (t, x) := by
        rcases eq_or_lt_of_le ht.2 with h | h
        · rw [h, h21zero]
        · exact (h21pos t ⟨ht.1, h⟩).le
      linarith [h1 t]
    · exact le_rfl
    · have : 0 ≤ l6d_v23 (t, x) := by
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

/-- **The extended Reinhardt–Poincaré map in the chart** (Steps 8–9): with
`σ = s_sw(r, x̃)` and the divided entries at `(σ, r, x̃)`,
`(r, x̃) ↦ (r a₁, b₁/a₁, c₂/a₁², d₂/a₁²)`. -/
noncomputable def l6d_E (q : ℝ × (Fin 3 → ℝ)) : ℝ × (Fin 3 → ℝ) :=
  (q.1 * l6d_qa (l6d_sSw q, q.1, q.2),
    ![l6d_qb (l6d_sSw q, q.1, q.2) / l6d_qa (l6d_sSw q, q.1, q.2),
      l6d_qc (l6d_sSw q, q.1, q.2) / l6d_qa (l6d_sSw q, q.1, q.2) ^ 2,
      l6d_qd (l6d_sSw q, q.1, q.2) / l6d_qa (l6d_sSw q, q.1, q.2) ^ 2])

/-- `w(s_sw,out, x̃_out) = λ r_scale q_out` (the fixed point equation (13.5.2), rescaled). -/
lemma l6d_w_base : l6d_w (l6d_S, xTildeOut) 0 = (l6d_lam * rScale : ℝ) * qOutCart 0 := by
  have h := poincare_qOutCart
  rw [poincare, firstControl_qOutCart] at h
  have hl := l6d_flow_scale l6d_lam l6d_T qOutCart ζ
  rw [l6d_w, l6d_S, l6d_fullerOfChart_xTildeOut, hl, show l6d_T = firstSwitchTime qOutCart from rfl,
    h]
  simp only [Pi.smul_apply, scale, Matrix.cons_val_zero, smul_eq_mul]
  have h3 : ζ * (ζ ^ 2 * ((rScale : ℂ) * qOutCart 0)) = ζ ^ 3 * ((rScale : ℂ) * qOutCart 0) := by
    ring
  rw [show ζ * (↑l6d_lam * (ζ ^ 2 * (↑rScale * qOutCart 0))) =
    ↑l6d_lam * (ζ * (ζ ^ 2 * (↑rScale * qOutCart 0))) by ring, h3, ζ_pow_three]
  push_cast
  ring

lemma l6d_va_base : l6d_va (l6d_S, xTildeOut) = rScale := by
  have hq := qOutCart_signs.1.ne'
  rw [l6d_va, l6d_w_base, Complex.im_ofReal_mul, l6d_lam]
  field_simp

lemma l6d_qa_base : l6d_qa (l6d_S, 0, xTildeOut) = rScale := by
  rw [l6d_qa, l6d_divR_zero, l6d_va_base]

lemma l6d_analyticAt_sSw_triple :
    AnalyticAt ℝ (fun q : ℝ × (Fin 3 → ℝ) ↦ (l6d_sSw q, q.1, q.2)) ((0 : ℝ), xTildeOut) := by
  have h := l6d_analyticAt_sSw
  fun_prop

lemma l6d_sSw_triple_base :
    (fun q : ℝ × (Fin 3 → ℝ) ↦ (l6d_sSw q, q.1, q.2)) ((0 : ℝ), xTildeOut) =
      (l6d_S, 0, xTildeOut) := by
  simp [l6d_sSw_base]

/-- The extended map is analytic at the fixed point. -/
lemma l6d_analyticAt_E : AnalyticAt ℝ l6d_E ((0 : ℝ), xTildeOut) := by
  obtain ⟨ha, hb, hc, hd⟩ := l6d_analyticAt_divided l6d_S xTildeOut
  have ht := l6d_analyticAt_sSw_triple
  have hta : AnalyticAt ℝ (fun q : ℝ × (Fin 3 → ℝ) ↦ l6d_qa (l6d_sSw q, q.1, q.2))
      ((0 : ℝ), xTildeOut) := ha.comp_of_eq ht l6d_sSw_triple_base
  have htb : AnalyticAt ℝ (fun q : ℝ × (Fin 3 → ℝ) ↦ l6d_qb (l6d_sSw q, q.1, q.2))
      ((0 : ℝ), xTildeOut) := hb.comp_of_eq ht l6d_sSw_triple_base
  have htc : AnalyticAt ℝ (fun q : ℝ × (Fin 3 → ℝ) ↦ l6d_qc (l6d_sSw q, q.1, q.2))
      ((0 : ℝ), xTildeOut) := hc.comp_of_eq ht l6d_sSw_triple_base
  have htd : AnalyticAt ℝ (fun q : ℝ × (Fin 3 → ℝ) ↦ l6d_qd (l6d_sSw q, q.1, q.2))
      ((0 : ℝ), xTildeOut) := hd.comp_of_eq ht l6d_sSw_triple_base
  have h0 : l6d_qa (l6d_sSw ((0 : ℝ), xTildeOut), ((0 : ℝ), xTildeOut).1,
      ((0 : ℝ), xTildeOut).2) ≠ 0 := by
    rw [l6d_sSw_base, l6d_qa_base]; linarith [rScale_spec.1]
  have h1 : AnalyticAt ℝ (fun q : ℝ × (Fin 3 → ℝ) ↦ q.1 * l6d_qa (l6d_sSw q, q.1, q.2))
      ((0 : ℝ), xTildeOut) := by fun_prop
  refine h1.prod (AnalyticAt.pi fun i ↦ ?_)
  fin_cases i
  · exact htb.fun_div hta h0
  · exact htc.fun_div (hta.fun_pow 2) (pow_ne_zero 2 h0)
  · exact htd.fun_div (hta.fun_pow 2) (pow_ne_zero 2 h0)

/-- For `r ≠ 0` the extended map is `lieChartInv` of the image point (TeX 11849–11856). -/
lemma l6d_E_eq_lieChartInv {q : ℝ × (Fin 3 → ℝ)} (hq : q.1 ≠ 0) :
    l6d_E q = lieChartInv (l6d_Xi (l6d_sSw q, q.1, q.2)) := by
  set p : ℝ × ℝ × (Fin 3 → ℝ) := (l6d_sSw q, q.1, q.2) with hp
  have hp1 : p.2.1 ≠ 0 := hq
  have ha := l6d_eq_pow_mul_divR l6d_fa 1 l6d_va hp1
  have hb := l6d_eq_pow_mul_divR l6d_fb 1 l6d_vb hp1
  have hc := l6d_eq_pow_mul_divR l6d_fc 2 l6d_vc hp1
  have hd := l6d_eq_pow_mul_divR l6d_fd 2 l6d_vd hp1
  simp only [l6d_fa, l6d_fb, l6d_fc, l6d_fd] at ha hb hc hd
  have hb' : (l6d_Xi p).1 1 0 = 1 + p.2.1 ^ 1 * l6d_qb p := by
    simp only [l6d_qb]; linarith
  have hd' : (l6d_Xi p).2.1 1 0 = -(3 / 2) + p.2.1 ^ 2 * l6d_qd p := by
    simp only [l6d_qd]; linarith
  simp only [l6d_E, lieChartInv, ← hp]
  rw [ha, hb', hc, hd']
  simp only [l6d_qa, l6d_qc, pow_one, Prod.mk.injEq]
  refine ⟨rfl, ?_⟩
  funext i
  fin_cases i <;>
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, add_sub_cancel_left,
      neg_add_cancel_comm] <;>
    field_simp

/-- **On the divisor the extended map is the Fuller–Poincaré map** (Step 9, TeX 11858–11860):
`E(0, x̃) = (0, fullerChartInv (ζ F(z(x̃))))` for `x̃` near `x̃_out`. -/
lemma l6d_eventually_E_divisor : ∀ᶠ x in 𝓝 xTildeOut,
    l6d_E (0, x) = (0, fullerChartInv (ζ • poincare (fullerOfChart x))) := by
  obtain ⟨δ, hδ, hδS, hZ⟩ := l6d_zero_structure
  have h23 := l6d_eventually_chi23_pos (l6d_S + δ)
  have hc : ContinuousAt (fun x : Fin 3 → ℝ ↦ ((0 : ℝ), x)) xTildeOut := by fun_prop
  filter_upwards [hc.eventually hZ, hc.eventually h23] with x ⟨hσ, hz, hpos, hneg⟩ h23x
  set σ := l6d_sSw ((0 : ℝ), x) with hσdef
  have hP : poincare (fullerOfChart x) = flow σ (fullerOfChart x) ζ := by
    refine l6d_poincare_eq (B := l6d_S + δ) (by linarith [hσ.1]) hσ.2 (fun s hs ↦ ?_) ?_
      (fun s hs ↦ ?_) (fun s hs ↦ ?_)
    · have := hpos s hs; simpa [l6d_Φ, l6d_chi21_zero] using this
    · simpa [l6d_Φ, l6d_chi21_zero] using hz
    · have := hneg s hs; simpa [l6d_Φ, l6d_chi21_zero] using this
    · have := h23x s hs; simpa [l6d_chi23_zero] using this
  simp only [l6d_E, zero_mul, l6d_qa, l6d_qb, l6d_qc, l6d_qd, l6d_divR_zero, Prod.mk.injEq,
    true_and, ← hσdef, hP]
  rw [show ζ • flow σ (fullerOfChart x) ζ = l6d_w (σ, x) from rfl]
  simp only [l6d_va, l6d_vb, l6d_vc, l6d_vd]
  generalize l6d_w (σ, x) = w
  funext i
  fin_cases i <;> simp [fullerChartInv] <;> ring

end SmoothedPolygons
