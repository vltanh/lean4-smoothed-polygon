module

public import SmoothedPolygons.Ch16.RescaledDynamics
public import SmoothedPolygons.Ch16.RelaxedFuller
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# Chapter 16: limits of rescaled Reinhardt arcs are relaxed Fuller extremals (§16.4.2, part 2)

The compactness step of the proof of N5 (`clusterSetForwardInvariant`,
`SmoothedPolygons/Ch16/ReinhardtShadowing.lean`). Along a chattering arc into the singular locus,
after the `n`-th switching time `τ_n`, with the radius `ρ_n = φ(ẑ(q_n))` of the switching point:

* `switchRadius n = ρ_n`, `rescaledArc n s = scale ρ_n⁻¹ ẑ(q(τ_n + s ρ_n))` (so
  `rescaledArc n 0 = ξ_n`, the angular component of the switching point), and
  `rescaledControl n s = simplexToUT (u(τ_n + s ρ_n))`, the rescaled control in `U_T`;
* `rescaledArc_eq_integral`: the rescaled arc solves the rescaled Reinhardt equation
  `y' = rescaledField ρ_n v(s) y` in integral form (the extremal equations of Problem 6.7.1,
  `fullerCoords` being `ℝ`-linear, and the change of variables `t = τ_n + s ρ_n`), as long as the
  window `[τ_n, τ_n + S ρ_n]` stays before `b`;
* `exists_tendsto_rescaledArc`: along a subsequence with `ξ_{n_k} → ξ`, on a window `[0, S]` that
  stays before `b`, a further subsequence of the rescaled arcs converges uniformly to a trajectory
  `y` of the Fuller system with a relaxed control `w ∈ U_T` satisfying the maximum condition, with
  `y(0) = ξ`, and the integrated rescaled controls converge to `∫ w`.

## Proofs

`rescaledArc_eq_integral` (`l6g_arc`): the entries of `X, Λ₁, Λ_R` solve the extremal equations in
integral form (`IsIntegralCurve`, after the time shift), so their Cayley coordinates and the Fuller
coordinates `ẑ` do (`l6g_fuller_eq`); in blow-up coordinates the rescaled arc is the lifted
trajectory (`phaseOfFuller_fullerCoords`, `l6g_phase`), so along it `rescaledField` is
`ρ · scale ρ⁻¹ ẑ(q')`, and the change of variables `t = τ_n + σ ρ_n` gives the equation, with the
integrability of the rescaled field (`l6g_arc_core`).

`exists_tendsto_rescaledArc`: the thresholds (the window before `b`, and the rescaled field within
`1` of the Fuller field on the ball of the a priori bound, `tendstoUniformlyOn_rescaledField` with
`ρ_n → 0⁺`) hold from some `K₀` on; the shifted sequence `φ(k + K₀)` goes to the abstract form
`l6g_limit`, which follows the book's route in four steps.
1. Bounds (`l6g_apriori`): `|ξ_n| ≤ 1` on `Ξ`; the triangular structure of the Fuller field gives
   the bounds `1 + 2S`, `1 + S(2 + 2S)`, `B = 1 + S(2 + S(2 + 2S))` on the three components in
   turn (this is the "Grönwall-type bound"; no Grönwall inequality is needed), and a continuity
   argument at the first time `|y| = B + 1` keeps the arcs in the ball of radius `B`. So the
   rescaled arcs are `(B + 1)`-Lipschitz and the integrated controls `W_n` are `1`-Lipschitz
   (`l6g_dist_le`).
2. Arzelà–Ascoli (`l6g_arzela`, `BoundedContinuousFunction.arzela_ascoli` on `C([0, S], ℂ³ × ℂ)`)
   for the pairs `(rescaledArc n, W_n)`; the limit `W` has difference quotients in `U_T` (averages
   of controls in `U_T`, `Convex.set_average_mem`), so it is `1`-Lipschitz, differentiable a.e.
   (Rademacher, `LipschitzWith.ae_differentiableAt_real`) with derivative in `U_T`, and the
   fundamental theorem of calculus for absolutely continuous functions
   (`AbsolutelyContinuousOnInterval.const_of_ae_hasDerivAt_zero`, Lebesgue's differentiation
   theorem) gives `W = ∫ w` for a measurable `w` with values in `U_T` (`l6g_control_limit`).
3. The limit equations: in the integral equation the error `rescaledField - fullerField` tends to
   `0` uniformly on `[0, S]`; `∫ -i·simplexToUT v_n = -i W_n → -i W`, and the other components
   converge by dominated convergence (`l6g_tendsto_integral`).
4. The maximum condition: the maximum condition of the extremal holds a.e. in rescaled time
   (`l6g_arc_max`); divided by `ρ³` (`tendstoUniformlyOn_rescaledHam`) it gives, for each vertex
   `v`, `RR(v - simplexToUT v_n, y_{n,3}) ≤ ε` a.e. on `[0, S]` for large `n`; integrated over
   `[s₁, s₂] ⊆ [0, S]` and passed to the limit (`H_F` is affine in the control, and
   `∫ RR(w_n, y₃) → ∫ RR(w, y₃)` by integration by parts against the uniformly convergent `W_n`,
   `l6g_ibp`) it gives `∫_{s₁}^{s₂} RR(v - w, y₃) ≤ 0`, and Lebesgue's differentiation theorem
   (`l6g_ae_nonpos`) turns these integral inequalities into the a.e. maximum condition at the
   vertices, hence on `U_T` (`l6g_ham_le_of_VT`).
-/

@[expose] public section

namespace SmoothedPolygons

open Complex Set Filter Topology MeasureTheory
open TriFuller

/-! ### Helpers: the triangle `U_T`, the simplex and the weighted sphere -/

private theorem l6g_isClosed_UT : IsClosed UT := (finite_VT.isCompact_convexHull ℝ).isClosed

private theorem l6g_convex_UT : Convex ℝ UT := convex_convexHull ℝ VT

private theorem l6g_one_mem_UT : (1 : ℂ) ∈ UT := VT_subset_UT one_mem_VT

/-- `U_T` lies in the closed unit disk. -/
private theorem l6g_norm_le_one_of_mem_UT {v : ℂ} (hv : v ∈ UT) : ‖v‖ ≤ 1 := by
  have hsub : UT ⊆ Metric.closedBall (0 : ℂ) 1 :=
    convexHull_min (fun x hx ↦ by simp [norm_eq_one_of_mem_VT hx]) (convex_closedBall 0 1)
  simpa using hsub hv

/-- `|RR(x, y)| ≤ |x||y|`. -/
private theorem l6g_abs_RR_le (x y : ℂ) : |RR x y| ≤ ‖x‖ * ‖y‖ := by
  rw [RR]
  calc |(starRingEnd ℂ x * y).re| ≤ ‖starRingEnd ℂ x * y‖ := Complex.abs_re_le_norm _
    _ = ‖x‖ * ‖y‖ := by rw [norm_mul, Complex.norm_conj]

private theorem l6g_RR_sub_left (a b c : ℂ) : RR (a - b) c = RR a c - RR b c := by
  simp only [RR_eq_re_mul_add_im_mul, Complex.sub_re, Complex.sub_im]; ring

private theorem l6g_RR_sub_right (a b c : ℂ) : RR a (b - c) = RR a b - RR a c := by
  simp only [RR_eq_re_mul_add_im_mul, Complex.sub_re, Complex.sub_im]; ring

/-- The simplex is mapped into `U_T`. -/
private theorem l6g_simplexToUT_mem {v : Fin 3 → ℝ} (hv : v ∈ controlSimplex) :
    simplexToUT v ∈ UT := by
  have h : simplexToUT v = ∑ m : Fin 3, v m • ζ ^ (m : ℕ) := by
    simp only [simplexToUT, Complex.real_smul]
  rw [h]
  refine l6g_convex_UT.sum_mem (fun m _ ↦ (hv.1 m).1) ?_ fun m _ ↦ ?_
  · rw [Fin.sum_univ_three]; exact hv.2
  · fin_cases m
    · simpa using VT_subset_UT one_mem_VT
    · simpa using VT_subset_UT ζ_mem_VT
    · simpa using VT_subset_UT ζ_sq_mem_VT

private theorem l6g_norm_simplexToUT_le {v : Fin 3 → ℝ} (hv : v ∈ controlSimplex) :
    ‖simplexToUT v‖ ≤ 1 :=
  l6g_norm_le_one_of_mem_UT (l6g_simplexToUT_mem hv)

private theorem l6g_simplexToUT_vertex (m : Fin 3) : simplexToUT (vertex m) = ζ ^ (m : ℕ) := by
  fin_cases m <;> simp [simplexToUT, vertex, Fin.sum_univ_three]

private theorem l6g_vertex_mem (m : Fin 3) : vertex m ∈ controlSimplex := by
  refine ⟨fun i ↦ ?_, ?_⟩
  · by_cases h : i = m
    · subst h; simp [vertex]
    · simp [vertex, h]
  · fin_cases m <;> simp [vertex]

/-- The maximum condition over `U_T` from the vertices (`H_F` is affine in the control). -/
private theorem l6g_ham_le_of_VT {z : Fin 3 → ℂ} {u : ℂ} (h : ∀ v ∈ VT, ham z v ≤ ham z u) :
    ∀ v ∈ UT, ham z v ≤ ham z u := by
  have hc : Convex ℝ {v : ℂ | ham z v ≤ ham z u} := by
    intro x hx y hy p q hp hq hpq
    simp only [mem_ofPred_eq, ham] at hx hy ⊢
    rw [RR_add_left, Complex.real_smul, Complex.real_smul, RR_ofReal_mul_left,
      RR_ofReal_mul_left]
    have e : q = 1 - p := by linarith
    subst e
    nlinarith [mul_nonneg hp (sub_nonneg.2 hx), mul_nonneg hq (sub_nonneg.2 hy)]
  exact convexHull_min (fun v hv ↦ h v hv) hc

/-- The points of the weighted sphere `Ξ` have norm at most `1`. -/
private theorem l6g_norm_le_one_of_mem_Xi {ξ : Fin 3 → ℂ} (hξ : ξ ∈ Xi) : ‖ξ‖ ≤ 1 := by
  have h1 : weightedNorm ξ = 1 := hξ
  have hA : ‖ξ 0‖ ^ 6 + ‖ξ 1‖ ^ 3 + ‖ξ 2‖ ^ 2 = 1 := by
    have hnn : 0 ≤ ‖ξ 0‖ ^ 6 + ‖ξ 1‖ ^ 3 + ‖ξ 2‖ ^ 2 := by positivity
    have := congrArg (fun x : ℝ ↦ x ^ (6 : ℕ)) h1
    simp only [weightedNorm, one_pow] at this
    rwa [← Real.rpow_natCast, ← Real.rpow_mul hnn, show (1 / 6 : ℝ) * ((6 : ℕ) : ℝ) = 1 by
      norm_num, Real.rpow_one] at this
  have a0 := pow_nonneg (norm_nonneg (ξ 0)) 6
  have a1 := pow_nonneg (norm_nonneg (ξ 1)) 3
  have a2 := pow_nonneg (norm_nonneg (ξ 2)) 2
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j ↦ ?_
  fin_cases j
  · exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (by norm_num : (6 : ℕ) ≠ 0)).1 (by
      simp only [Fin.zero_eta] at *; linarith)
  · exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (by norm_num : (3 : ℕ) ≠ 0)).1 (by
      simp only [Fin.mk_one] at *; linarith)
  · exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (by norm_num : (2 : ℕ) ≠ 0)).1 (by
      simp only [Fin.reduceFinMk] at *; linarith)

/-- The components of the virial rescaling. -/
private theorem l6g_scale_apply (r : ℝ) (z : Fin 3 → ℂ) (j : Fin 3) :
    scale r z j = (r : ℂ) ^ ((j : ℕ) + 1) * z j := by
  fin_cases j <;> simp [scale]

/-- The norm of the Fuller vector field. -/
private theorem l6g_norm_fullerField_le {c : ℂ} (hc : ‖c‖ ≤ 1) (y : Fin 3 → ℂ) :
    ‖fullerField c y‖ ≤ max 1 ‖y‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j ↦ ?_
  fin_cases j
  · simp only [fullerField, Fin.zero_eta, Matrix.cons_val_zero, norm_mul, norm_neg,
      Complex.norm_I, one_mul]
    exact hc.trans (le_max_left _ _)
  · simpa [fullerField] using (norm_le_pi_norm y 0).trans (le_max_right _ _)
  · simpa [fullerField] using (norm_le_pi_norm y 1).trans (le_max_right _ _)

/-! ### Helpers: integrals on intervals -/

/-- Componentwise integrability gives integrability of a curve in `ℂ³`. -/
private theorem l6g_intervalIntegrable_pi {f : ℝ → Fin 3 → ℂ} {a b : ℝ}
    (hf : ∀ j, IntervalIntegrable (fun s ↦ f s j) volume a b) : IntervalIntegrable f volume a b :=
  ⟨Integrable.of_eval fun j ↦ (hf j).1, Integrable.of_eval fun j ↦ (hf j).2⟩

private theorem l6g_intervalIntegrable_eval {f : ℝ → Fin 3 → ℂ} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) (j : Fin 3) :
    IntervalIntegrable (fun s ↦ f s j) volume a b :=
  ⟨integrable_pi_iff.1 hf.1 j, integrable_pi_iff.1 hf.2 j⟩

/-- The components of the integral of a curve in `ℂ³`. -/
private theorem l6g_integral_apply {f : ℝ → Fin 3 → ℂ} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) (j : Fin 3) :
    (∫ s in a..b, f s) j = ∫ s in a..b, f s j := by
  have := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 ↦ ℂ) j).intervalIntegral_comp_comm
    hf
  simpa using this.symm

private theorem l6g_intervalIntegrable_re {w : ℝ → ℂ} {a b : ℝ}
    (hw : IntervalIntegrable w volume a b) : IntervalIntegrable (fun s ↦ (w s).re) volume a b :=
  ⟨Complex.reCLM.integrable_comp hw.1, Complex.reCLM.integrable_comp hw.2⟩

private theorem l6g_intervalIntegrable_im {w : ℝ → ℂ} {a b : ℝ}
    (hw : IntervalIntegrable w volume a b) : IntervalIntegrable (fun s ↦ (w s).im) volume a b :=
  ⟨Complex.imCLM.integrable_comp hw.1, Complex.imCLM.integrable_comp hw.2⟩

private theorem l6g_integral_re {w : ℝ → ℂ} {a b : ℝ} (hw : IntervalIntegrable w volume a b) :
    (∫ s in a..b, w s).re = ∫ s in a..b, (w s).re := by
  have := Complex.reCLM.intervalIntegral_comp_comm hw
  simpa using this.symm

private theorem l6g_integral_im {w : ℝ → ℂ} {a b : ℝ} (hw : IntervalIntegrable w volume a b) :
    (∫ s in a..b, w s).im = ∫ s in a..b, (w s).im := by
  have := Complex.imCLM.intervalIntegral_comp_comm hw
  simpa using this.symm

private theorem l6g_intervalIntegrable_ofReal {f : ℝ → ℝ} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun s ↦ ((f s : ℝ) : ℂ)) volume a b :=
  ⟨hf.1.ofReal, hf.2.ofReal⟩

/-- A measurable function bounded on `[a, b]` is integrable on every subinterval. -/
private theorem l6g_intervalIntegrable_of_bound {E : Type*} [NormedAddCommGroup E]
    {u : ℝ → E} (hu : AEStronglyMeasurable u volume) {a b C : ℝ}
    (hb : ∀ t ∈ Icc a b, ‖u t‖ ≤ C) {c d : ℝ} (hc : c ∈ Icc a b) (hd : d ∈ Icc a b) :
    IntervalIntegrable u volume c d := by
  have hab : a ≤ b := hc.1.trans hc.2
  have h : IntervalIntegrable u volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
      (Measure.integrableOn_of_bounded (by simp [Real.volume_Ioc]) hu
        (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht ↦ hb t (Ioc_subset_Icc_self ht)))
  exact h.mono_set (by rw [uIcc_of_le hab]; exact uIcc_subset_Icc hc hd)

/-- Integrability on a subinterval. -/
private theorem l6g_intervalIntegrable_mono {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    {a b c d : ℝ} (hf : IntervalIntegrable f volume a b) (hab : a ≤ b) (hc : c ∈ Icc a b)
    (hd : d ∈ Icc a b) : IntervalIntegrable f volume c d :=
  hf.mono_set (by rw [uIcc_of_le hab]; exact uIcc_subset_Icc hc hd)

/-- The affine change of variables `t = τ + σ ρ`. -/
private theorem l6g_integral_affine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (τ : ℝ) {ρ : ℝ} (hρ : ρ ≠ 0) (s : ℝ) :
    ∫ σ in (0 : ℝ)..s, f (τ + σ * ρ) = ρ⁻¹ • ∫ t in τ..τ + s * ρ, f t := by
  have e : (fun σ ↦ f (τ + σ * ρ)) = fun σ ↦ f (ρ * σ + τ) := by
    funext σ; rw [add_comm, mul_comm]
  rw [e, intervalIntegral.integral_comp_mul_add f hρ τ, mul_zero, zero_add, add_comm (ρ * s),
    mul_comm ρ s]

private theorem l6g_intervalIntegrable_affine {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {τ ρ s : ℝ} (hρ : 0 < ρ) (hf : IntervalIntegrable f volume τ (τ + s * ρ)) :
    IntervalIntegrable (fun σ ↦ f (τ + σ * ρ)) volume 0 s := by
  have h1 := (hf.comp_add_right τ).comp_mul_left (c := ρ)
  have e1 : (τ - τ) / ρ = 0 := by simp
  have e2 : (τ + s * ρ - τ) / ρ = s := by field_simp; ring
  rw [e1, e2] at h1
  have e : (fun σ ↦ f (τ + σ * ρ)) = fun x ↦ f (ρ * x + τ) := by
    funext σ; rw [add_comm, mul_comm]
  rw [e]
  exact h1

/-- A property holding almost everywhere holds almost everywhere after an affine change of
variables. -/
private theorem l6g_ae_affine {P : ℝ → Prop} (h : ∀ᵐ t, P t) (τ : ℝ) {ρ : ℝ} (hρ : ρ ≠ 0) :
    ∀ᵐ σ, P (τ + σ * ρ) := by
  rw [ae_iff] at h ⊢
  have e : {σ | ¬ P (τ + σ * ρ)} = (fun x ↦ x * ρ) ⁻¹' ((fun x ↦ τ + x) ⁻¹' {t | ¬ P t}) := rfl
  rw [e, Real.volume_preimage_mul_right hρ, measure_preimage_add, h, mul_zero]

/-- A primitive of a function bounded by `L` is `L`-Lipschitz. -/
private theorem l6g_dist_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {S L : ℝ}
    {y F : ℝ → E} (hF : IntervalIntegrable F volume 0 S)
    (hy : ∀ s ∈ Icc 0 S, y s = y 0 + ∫ σ in (0 : ℝ)..s, F σ) (hb : ∀ σ ∈ Icc 0 S, ‖F σ‖ ≤ L) :
    ∀ s ∈ Icc 0 S, ∀ s' ∈ Icc 0 S, dist (y s) (y s') ≤ L * dist s s' := by
  intro s hs s' hs'
  have hS : 0 ≤ S := hs.1.trans hs.2
  have h0 : (0 : ℝ) ∈ Icc 0 S := ⟨le_rfl, hS⟩
  rw [dist_eq_norm, hy s hs, hy s' hs', add_sub_add_left_eq_sub,
    intervalIntegral.integral_interval_sub_left (l6g_intervalIntegrable_mono hF hS h0 hs)
      (l6g_intervalIntegrable_mono hF hS h0 hs'), Real.dist_eq]
  exact intervalIntegral.norm_integral_le_of_norm_le_const fun x hx ↦
    hb x (uIcc_subset_Icc hs' hs (uIoc_subset_uIcc hx))

/-- The real and imaginary parts of a primitive are absolutely continuous. -/
private theorem l6g_ac_re_im {w W : ℝ → ℂ} {s₁ s₂ : ℝ} (hs : s₁ ≤ s₂)
    (hw : IntervalIntegrable w volume s₁ s₂)
    (hW : ∀ s ∈ Icc s₁ s₂, W s = W s₁ + ∫ σ in s₁..s, w σ) :
    AbsolutelyContinuousOnInterval (fun σ ↦ (W σ).re) s₁ s₂ ∧
      AbsolutelyContinuousOnInterval (fun σ ↦ (W σ).im) s₁ s₂ := by
  have hsub : ∀ s ∈ Icc s₁ s₂, IntervalIntegrable w volume s₁ s :=
    fun s hs' ↦ l6g_intervalIntegrable_mono hw hs ⟨le_rfl, hs⟩ hs'
  refine ⟨absolutelyContinuousOnInterval_of_eq_add_integral hs (l6g_intervalIntegrable_re hw)
    fun s hs' ↦ ?_, absolutelyContinuousOnInterval_of_eq_add_integral hs
      (l6g_intervalIntegrable_im hw) fun s hs' ↦ ?_⟩
  · rw [hW s hs', Complex.add_re, l6g_integral_re (hsub s hs')]
  · rw [hW s hs', Complex.add_im, l6g_integral_im (hsub s hs')]

/-- **Integration by parts** for `RR(w, g)` with `w = W'` integrable and `g' = h` continuous, in
integral form (absolutely continuous functions; Lebesgue's differentiation theorem). -/
private theorem l6g_ibp {w W g h : ℝ → ℂ} {s₁ s₂ : ℝ} (hs : s₁ ≤ s₂)
    (hw : IntervalIntegrable w volume s₁ s₂)
    (hW : ∀ s ∈ Icc s₁ s₂, W s = W s₁ + ∫ σ in s₁..s, w σ)
    (hh : ContinuousOn h (Icc s₁ s₂)) (hg : ∀ s ∈ Icc s₁ s₂, g s = g s₁ + ∫ σ in s₁..s, h σ) :
    ∫ σ in s₁..s₂, RR (w σ) (g σ) =
      RR (W s₂) (g s₂) - RR (W s₁) (g s₁) - ∫ σ in s₁..s₂, RR (W σ) (h σ) := by
  have hhi : IntervalIntegrable h volume s₁ s₂ := hh.intervalIntegrable_of_Icc hs
  have hWc : ContinuousOn W (Icc s₁ s₂) := continuousOn_Icc_of_eq_add_integral hs hw hW
  have hgc : ContinuousOn g (Icc s₁ s₂) := continuousOn_Icc_of_eq_add_integral hs hhi hg
  obtain ⟨hWre, hWim⟩ := l6g_ac_re_im hs hw hW
  obtain ⟨hgre, hgim⟩ := l6g_ac_re_im hs hhi hg
  have hac : AbsolutelyContinuousOnInterval (fun σ ↦ RR (W σ) (g σ)) s₁ s₂ := by
    have := (hWre.fun_mul hgre).fun_add (hWim.fun_mul hgim)
    simpa only [RR_eq_re_mul_add_im_mul] using this
  have hdW := ae_hasDerivAt_of_eq_add_integral hw ⟨le_rfl, hs⟩ hW
  have hdg := ae_hasDerivAt_of_eq_add_integral hhi ⟨le_rfl, hs⟩ hg
  have hd : ∀ᵐ t, t ∈ Ioo s₁ s₂ → HasDerivAt (fun σ ↦ RR (W σ) (g σ))
      (RR (w t) (g t) + RR (W t) (h t)) t := by
    filter_upwards [hdW, hdg] with t h1 h2 ht
    exact hasDerivAt_RR (h1 ht) (h2 ht)
  obtain ⟨hint, heq⟩ := hac.eq_add_integral_of_ae_hasDerivAt hs hd
  have hc2 : IntervalIntegrable (fun σ ↦ RR (W σ) (h σ)) volume s₁ s₂ := by
    refine ContinuousOn.intervalIntegrable_of_Icc hs ?_
    simp only [RR_eq_re_mul_add_im_mul]
    exact ((Complex.continuous_re.comp_continuousOn hWc).mul
      (Complex.continuous_re.comp_continuousOn hh)).add
      ((Complex.continuous_im.comp_continuousOn hWc).mul
      (Complex.continuous_im.comp_continuousOn hh))
  have hc1 : IntervalIntegrable (fun σ ↦ RR (w σ) (g σ)) volume s₁ s₂ := by
    have := hint.sub hc2
    simpa only [add_sub_cancel_right] using this
  have e := heq s₂ ⟨hs, le_rfl⟩
  rw [intervalIntegral.integral_add hc1 hc2] at e
  linarith

/-- **Lebesgue's differentiation theorem** in the form used for the maximum condition: an
integrable function with nonpositive integrals over all subintervals of `[0, S]` is nonpositive
almost everywhere on `[0, S]`. -/
private theorem l6g_ae_nonpos {S : ℝ} {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 S)
    (h : ∀ s₁ s₂, 0 ≤ s₁ → s₁ ≤ s₂ → s₂ ≤ S → ∫ σ in s₁..s₂, f σ ≤ 0) :
    ∀ᵐ σ, σ ∈ Icc 0 S → f σ ≤ 0 := by
  rcases le_or_gt 0 S with hS | hS
  swap
  · exact ae_of_all _ fun σ hσ ↦ absurd (hσ.1.trans hσ.2) (not_le.2 hS)
  have h0S : (0 : ℝ) ∈ Icc 0 S := ⟨le_rfl, hS⟩
  have hd := ae_hasDerivAt_of_eq_add_integral (x := fun t ↦ ∫ σ in (0 : ℝ)..t, f σ) (x₀ := 0)
    hf h0S fun t _ ↦ (zero_add _).symm
  have h0 : ∀ᵐ σ : ℝ, σ ≠ 0 := by simp [ae_iff, measure_singleton]
  have hSn : ∀ᵐ σ : ℝ, σ ≠ S := by simp [ae_iff, measure_singleton]
  filter_upwards [hd, h0, hSn] with x hx hx0 hxS hxI
  have hxI' : x ∈ Ioo 0 S := ⟨lt_of_le_of_ne hxI.1 (Ne.symm hx0), lt_of_le_of_ne hxI.2 hxS⟩
  have ht := (hasDerivWithinAt_iff_tendsto_slope' (s := Ioi x) (lt_irrefl x)).1
    (hx hxI').hasDerivWithinAt
  refine le_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsGT hxI'.2] with z hz
  have hxz : x ≤ z := hz.1.le
  rw [slope_def_field, intervalIntegral.integral_interval_sub_left
    (l6g_intervalIntegrable_mono hf hS h0S ⟨hxI.1.trans hxz, hz.2.le⟩)
    (l6g_intervalIntegrable_mono hf hS h0S hxI)]
  exact div_nonpos_of_nonpos_of_nonneg (h x z hxI.1 hxz hz.2.le) (sub_nonneg.2 hxz)

/-! ### Helpers: relaxed limits of controls and the Arzelà–Ascoli theorem -/

/-- **The weak-* limit of controls in `U_T`**: if the primitives `∫₀ˢ c_k` of measurable controls
with values in `U_T` on `[0, S]` converge pointwise on `[0, S]` to `W`, then `W` is the primitive of
a measurable control `w` with values in `U_T` on `[0, S]`: the difference quotients of `W` lie in
`U_T` (averages of `c_k`, `U_T` convex and closed), so `W` is `1`-Lipschitz, differentiable almost
everywhere (Rademacher) with derivative in `U_T`, and the fundamental theorem of calculus for
absolutely continuous functions gives `W = ∫ w`. -/
private theorem l6g_control_limit {S : ℝ} (hS : 0 < S) {c : ℕ → ℝ → ℂ} {W : ℝ → ℂ}
    (hcm : ∀ k, Measurable (c k)) (hcU : ∀ k, ∀ σ ∈ Icc 0 S, c k σ ∈ UT)
    (hlim : ∀ s ∈ Icc 0 S, Tendsto (fun k ↦ ∫ σ in (0 : ℝ)..s, c k σ) atTop (𝓝 (W s))) :
    ∃ w : ℝ → ℂ, Measurable w ∧ (∀ σ ∈ Icc 0 S, w σ ∈ UT) ∧
      ∀ s ∈ Icc 0 S, ∫ σ in (0 : ℝ)..s, w σ = W s := by
  classical
  have h0S : (0 : ℝ) ∈ Icc 0 S := ⟨le_rfl, hS.le⟩
  have hint : ∀ k, ∀ s ∈ Icc 0 S, ∀ s' ∈ Icc 0 S, IntervalIntegrable (c k) volume s s' :=
    fun k s hs s' hs' ↦ l6g_intervalIntegrable_of_bound (hcm k).aestronglyMeasurable
      (fun σ hσ ↦ l6g_norm_le_one_of_mem_UT (hcU k σ hσ)) hs hs'
  -- `W 0 = 0`
  have hW0 : W 0 = 0 := by
    have := hlim 0 h0S
    simp only [intervalIntegral.integral_same] at this
    exact tendsto_nhds_unique this tendsto_const_nhds
  -- the difference quotients lie in `U_T`
  have hslope : ∀ s' ∈ Icc 0 S, ∀ s ∈ Icc 0 S, s' < s → (s - s')⁻¹ • (W s - W s') ∈ UT := by
    intro s' hs' s hs hlt
    have hmem : ∀ k,
        (s - s')⁻¹ • ((∫ σ in (0 : ℝ)..s, c k σ) - ∫ σ in (0 : ℝ)..s', c k σ) ∈ UT := by
      intro k
      rw [intervalIntegral.integral_interval_sub_left (hint k 0 h0S s hs) (hint k 0 h0S s' hs'),
        intervalIntegral.integral_of_le hlt.le]
      have hav := l6g_convex_UT.set_average_mem l6g_isClosed_UT (μ := volume) (t := Ioc s' s)
        (f := c k) (by simp [Real.volume_Ioc, hlt]) (by simp [Real.volume_Ioc])
        (ae_restrict_of_forall_mem measurableSet_Ioc fun σ hσ ↦
          hcU k σ ⟨hs'.1.trans hσ.1.le, hσ.2.trans hs.2⟩)
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le hlt.le).1 (hint k s' hs' s hs))
      rwa [setAverage_eq, Real.volume_real_Ioc_of_le hlt.le] at hav
    exact l6g_isClosed_UT.mem_of_tendsto (((hlim s hs).sub (hlim s' hs')).const_smul _)
      (Eventually.of_forall hmem)
  -- `W` is `1`-Lipschitz on `[0, S]`
  have hWlip : ∀ s ∈ Icc 0 S, ∀ s' ∈ Icc 0 S, dist (W s) (W s') ≤ dist s s' := by
    have key : ∀ s' ∈ Icc 0 S, ∀ s ∈ Icc 0 S, s' < s → dist (W s) (W s') ≤ dist s s' := by
      intro s' hs' s hs hlt
      have h1 := l6g_norm_le_one_of_mem_UT (hslope s' hs' s hs hlt)
      have hpos : 0 < s - s' := sub_pos.2 hlt
      rw [norm_smul, norm_inv, Real.norm_of_nonneg hpos.le, inv_mul_le_iff₀ hpos, mul_one] at h1
      rw [dist_eq_norm, Real.dist_eq, abs_of_pos hpos]
      exact h1
    intro s hs s' hs'
    rcases lt_trichotomy s' s with hlt | heq | hgt
    · exact key s' hs' s hs hlt
    · simp [heq]
    · rw [dist_comm, dist_comm s]; exact key s hs s' hs' hgt
  -- the extension `W̃ = W ∘ proj_{[0, S]}`
  set Wt : ℝ → ℂ := fun x ↦ W (projIcc 0 S hS.le x) with hWt
  have hWt_eq : ∀ x ∈ Icc 0 S, Wt x = W x := fun x hx ↦ by
    simp only [hWt, projIcc_of_mem hS.le hx]
  have hWt_lip : LipschitzWith 1 Wt := by
    refine LipschitzWith.of_dist_le_mul fun x x' ↦ ?_
    simp only [NNReal.coe_one, one_mul, hWt]
    exact (hWlip _ (projIcc 0 S hS.le x).2 _ (projIcc 0 S hS.le x').2).trans
      (by simpa [Subtype.dist_eq, one_mul] using (LipschitzWith.projIcc hS.le).dist_le_mul x x')
  -- the control: the derivative of `W̃` where it lies in `U_T`
  set w : ℝ → ℂ := fun x ↦ if deriv Wt x ∈ UT then deriv Wt x else 1 with hw
  have hwm : Measurable w :=
    Measurable.ite (l6g_isClosed_UT.measurableSet.preimage (measurable_deriv Wt))
      (measurable_deriv Wt) measurable_const
  have hwU : ∀ σ ∈ Icc 0 S, w σ ∈ UT := fun σ _ ↦ by
    simp only [hw]; split_ifs with h; exacts [h, l6g_one_mem_UT]
  -- at interior points of differentiability, `w` is the derivative of `W̃`
  have hderiv : ∀ x ∈ Ioo 0 S, DifferentiableAt ℝ Wt x → deriv Wt x ∈ UT := by
    intro x hx hdiff
    have ht := (hasDerivWithinAt_iff_tendsto_slope' (s := Ioi x) (lt_irrefl x)).1
      hdiff.hasDerivAt.hasDerivWithinAt
    refine l6g_isClosed_UT.mem_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsGT hx.2] with z hz
    rw [slope_def_module, hWt_eq z ⟨hx.1.le.trans hz.1.le, hz.2.le⟩,
      hWt_eq x (Ioo_subset_Icc_self hx)]
    exact hslope x (Ioo_subset_Icc_self hx) z ⟨hx.1.le.trans hz.1.le, hz.2.le⟩ hz.1
  -- the primitive of `w`
  have hwint : IntervalIntegrable w volume 0 S :=
    l6g_intervalIntegrable_of_bound hwm.aestronglyMeasurable
      (fun σ hσ ↦ l6g_norm_le_one_of_mem_UT (hwU σ hσ)) h0S ⟨hS.le, le_rfl⟩
  have hprim : ∀ s ∈ Icc 0 S, (fun t ↦ ∫ σ in (0 : ℝ)..t, w σ) s =
      (fun t ↦ ∫ σ in (0 : ℝ)..t, w σ) 0 + ∫ σ in (0 : ℝ)..s, w σ := fun s _ ↦ by simp
  have hplip := l6g_dist_le hwint hprim fun σ hσ ↦ l6g_norm_le_one_of_mem_UT (hwU σ hσ)
  have hac : AbsolutelyContinuousOnInterval (fun x ↦ Wt x - ∫ σ in (0 : ℝ)..x, w σ) 0 S := by
    have h1 : AbsolutelyContinuousOnInterval Wt 0 S :=
      (hWt_lip.lipschitzOnWith (s := uIcc 0 S)).absolutelyContinuousOnInterval
    have h2 : AbsolutelyContinuousOnInterval (fun t ↦ ∫ σ in (0 : ℝ)..t, w σ) 0 S := by
      refine LipschitzOnWith.absolutelyContinuousOnInterval (K := 1) ?_
      refine LipschitzOnWith.of_dist_le_mul fun x hx x' hx' ↦ ?_
      rw [uIcc_of_le hS.le] at hx hx'
      simpa using hplip x hx x' hx'
    exact h1.sub h2
  have hd0 : ∀ᵐ x, x ∈ uIcc 0 S → HasDerivAt (fun x ↦ Wt x - ∫ σ in (0 : ℝ)..x, w σ) 0 x := by
    have hdw := ae_hasDerivAt_of_eq_add_integral (x := fun t ↦ ∫ σ in (0 : ℝ)..t, w σ) (x₀ := 0)
      hwint h0S fun t _ ↦ (zero_add _).symm
    have h0 : ∀ᵐ σ : ℝ, σ ≠ 0 := by simp [ae_iff, measure_singleton]
    have hSn : ∀ᵐ σ : ℝ, σ ≠ S := by simp [ae_iff, measure_singleton]
    filter_upwards [hWt_lip.ae_differentiableAt_real, hdw, h0, hSn] with x hdx hx hx0 hxS hxI
    rw [uIcc_of_le hS.le] at hxI
    have hxI' : x ∈ Ioo 0 S := ⟨lt_of_le_of_ne hxI.1 (Ne.symm hx0), lt_of_le_of_ne hxI.2 hxS⟩
    have hwx : w x = deriv Wt x := by simp only [hw, hderiv x hxI' hdx, ite_true]
    have := hdx.hasDerivAt.sub (hx hxI')
    rwa [hwx, sub_self] at this
  obtain ⟨C, hC⟩ := hac.const_of_ae_hasDerivAt_zero hd0
  have hC0 : C = 0 := by
    have := hC 0 left_mem_uIcc
    rw [hWt_eq 0 h0S, hW0, intervalIntegral.integral_same, sub_zero] at this
    exact this.symm
  refine ⟨w, hwm, hwU, fun s hs ↦ ?_⟩
  have := hC s (by rw [uIcc_of_le hS.le]; exact hs)
  rw [hC0, hWt_eq s hs, sub_eq_zero] at this
  exact this.symm

/-- **The Arzelà–Ascoli theorem** for pairs of uniformly bounded, uniformly Lipschitz curves on
`[0, S]` (`BoundedContinuousFunction.arzela_ascoli` on `C([0, S], ℂ³ × ℂ)`): a subsequence
converges uniformly on `[0, S]`, to continuous limits. -/
private theorem l6g_arzela {S L M : ℝ} (hS : 0 ≤ S) {Y : ℕ → ℝ → Fin 3 → ℂ} {V : ℕ → ℝ → ℂ}
    (hYL : ∀ k, ∀ s ∈ Icc 0 S, ∀ s' ∈ Icc 0 S, dist (Y k s) (Y k s') ≤ L * dist s s')
    (hVL : ∀ k, ∀ s ∈ Icc 0 S, ∀ s' ∈ Icc 0 S, dist (V k s) (V k s') ≤ L * dist s s')
    (hYM : ∀ k, ∀ s ∈ Icc 0 S, ‖Y k s‖ ≤ M) (hVM : ∀ k, ∀ s ∈ Icc 0 S, ‖V k s‖ ≤ M) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ (y : ℝ → Fin 3 → ℂ) (W : ℝ → ℂ), Continuous y ∧
      Continuous W ∧ TendstoUniformlyOn (fun k ↦ Y (ψ k)) y atTop (Icc 0 S) ∧
      TendstoUniformlyOn (fun k ↦ V (ψ k)) W atTop (Icc 0 S) := by
  set L' : NNReal := Real.toNNReal L
  have hL : L ≤ (L' : ℝ) := Real.le_coe_toNNReal L
  have hlip : ∀ k, LipschitzWith L' (fun x : Icc (0 : ℝ) S ↦ (Y k x, V k x)) := by
    intro k
    refine LipschitzWith.of_dist_le_mul fun x x' ↦ ?_
    rw [Prod.dist_eq, Subtype.dist_eq]
    exact max_le ((hYL k x x.2 x' x'.2).trans (by gcongr))
      ((hVL k x x.2 x' x'.2).trans (by gcongr))
  let F : ℕ → BoundedContinuousFunction (Icc (0 : ℝ) S) ((Fin 3 → ℂ) × ℂ) := fun k ↦
    BoundedContinuousFunction.mkOfCompact ⟨_, (hlip k).continuous⟩
  have hFapp : ∀ k x, F k x = (Y k x, V k x) := fun k x ↦ rfl
  have hA := BoundedContinuousFunction.arzela_ascoli
    (Metric.closedBall (0 : (Fin 3 → ℂ) × ℂ) M) (isCompact_closedBall _ _) (range F)
    (by
      rintro f x ⟨k, rfl⟩
      rw [mem_closedBall_zero_iff, hFapp, Prod.norm_def]
      exact max_le (hYM k x x.2) (hVM k x x.2))
    (by
      refine (LipschitzWith.uniformEquicontinuous _ L' fun f ↦ ?_).equicontinuous
      obtain ⟨k, hk⟩ := f.2
      rw [← hk]
      exact hlip k)
  obtain ⟨f, -, ψ, hψ, hlim⟩ := hA.tendsto_subseq (x := F)
    fun k ↦ subset_closure (mem_range_self k)
  have hu := Metric.tendstoUniformly_iff.1
    (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.1 hlim)
  refine ⟨ψ, hψ, fun s ↦ (f (projIcc 0 S hS s)).1, fun s ↦ (f (projIcc 0 S hS s)).2,
    (continuous_fst.comp (f.continuous.comp continuous_projIcc)),
    (continuous_snd.comp (f.continuous.comp continuous_projIcc)), ?_, ?_⟩
  · refine Metric.tendstoUniformlyOn_iff.2 fun ε hε ↦ ?_
    filter_upwards [hu ε hε] with k hk s hs
    have h1 := hk ⟨s, hs⟩
    simp only [Function.comp_apply, hFapp] at h1
    rw [projIcc_of_mem hS hs]
    rw [Prod.dist_eq] at h1
    exact lt_of_le_of_lt (le_max_left _ _) h1
  · refine Metric.tendstoUniformlyOn_iff.2 fun ε hε ↦ ?_
    filter_upwards [hu ε hε] with k hk s hs
    have h1 := hk ⟨s, hs⟩
    simp only [Function.comp_apply, hFapp] at h1
    rw [projIcc_of_mem hS hs]
    rw [Prod.dist_eq] at h1
    exact lt_of_le_of_lt (le_max_right _ _) h1

/-! ### Helpers: the Reinhardt arc in Fuller coordinates -/

/-- Each entry of a solution of `M' = V` on `[a, b]`, written after the time shift `t ↦ a + t`. -/
private theorem l6g_entry {M V : ℝ → Mat2} {a b : ℝ}
    (hI : IsIntegralCurve (fun t ↦ M (a + t)) (fun t ↦ V (a + t)) (b - a)) (i j : Fin 2) :
    IntervalIntegrable (fun t ↦ V t i j) volume a b ∧
      ∀ t ∈ Icc a b, M t i j = M a i j + ∫ s in a..t, V s i j := by
  obtain ⟨h1, h2⟩ := hI i j
  refine ⟨?_, fun t ht ↦ ?_⟩
  · have := h1.comp_sub_right a
    simp only [add_sub_cancel, zero_add, sub_add_cancel] at this
    exact this
  · have := h2 (t - a) ⟨sub_nonneg.2 ht.1, sub_le_sub_right ht.2 a⟩
    rw [intervalIntegral.integral_comp_add_left (fun s ↦ V s i j) a] at this
    simpa only [add_sub_cancel, add_zero] using this

/-- The Cayley coordinate of a solution of `M' = V`, in integral form. -/
private theorem l6g_cayley {M V : ℝ → Mat2} {a b : ℝ}
    (h : ∀ i j, IntervalIntegrable (fun t ↦ V t i j) volume a b ∧
      ∀ t ∈ Icc a b, M t i j = M a i j + ∫ s in a..t, V s i j) :
    IntervalIntegrable (fun t ↦ cayleyZ (V t)) volume a b ∧
      ∀ t ∈ Icc a b, cayleyZ (M t) = cayleyZ (M a) + ∫ s in a..t, cayleyZ (V s) := by
  have e : ∀ N : Mat2, cayleyZ N = (((N 0 1 + N 1 0) / 2 : ℝ) : ℂ) + ((N 0 0 : ℝ) : ℂ) * I :=
    fun N ↦ by rw [cayleyZ, Complex.mk_eq_add_mul_I]
  have h01 := h 0 1
  have h10 := h 1 0
  have h00 := h 0 0
  have hi1 : IntervalIntegrable (fun t ↦ (((V t 0 1 + V t 1 0) / 2 : ℝ) : ℂ)) volume a b :=
    l6g_intervalIntegrable_ofReal ((h01.1.add h10.1).div_const 2)
  have hi2 : IntervalIntegrable (fun t ↦ ((V t 0 0 : ℝ) : ℂ) * I) volume a b :=
    (l6g_intervalIntegrable_ofReal h00.1).mul_const I
  refine ⟨?_, fun t ht ↦ ?_⟩
  · simp only [e]; exact hi1.add hi2
  · have hsub : ∀ {f : ℝ → ℝ}, IntervalIntegrable f volume a b →
        IntervalIntegrable f volume a t := fun hf ↦
      l6g_intervalIntegrable_mono hf (ht.1.trans ht.2) ⟨le_rfl, ht.1.trans ht.2⟩ ht
    simp only [e]
    rw [intervalIntegral.integral_add (l6g_intervalIntegrable_ofReal
        (((hsub h01.1).add (hsub h10.1)).div_const 2))
      ((l6g_intervalIntegrable_ofReal (hsub h00.1)).mul_const I),
      intervalIntegral.integral_ofReal, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_ofReal, intervalIntegral.integral_div,
      intervalIntegral.integral_add (hsub h01.1) (hsub h10.1), h01.2 t ht, h10.2 t ht,
      h00.2 t ht]
    push_cast
    ring

/-- The velocity `ẑ(q'(t))` of the Fuller coordinates along a lifted trajectory (`ẑ` is
`ℝ`-linear). -/
private noncomputable def l6g_vel (u : ℝ → Fin 3 → ℝ) (X Λ₁ ΛR : ℝ → Mat2) (t : ℝ) :
    Fin 3 → ℂ :=
  fullerCoords (iso_extremalField (u t) (phaseAt X Λ₁ ΛR t))

/-- **The Fuller coordinates along an extremal** (`λ_cost = -1`) solve `ẑ' = ẑ(q')` (the
extremal equations of Problem 6.7.1, `fullerCoords` being `ℝ`-linear), in integral form. -/
private theorem l6g_fuller_eq {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    (hext : IsExtremalOn a b u g X Λ₁ ΛR (-1)) (j : Fin 3) :
    IntervalIntegrable (fun t ↦ l6g_vel u X Λ₁ ΛR t j) volume a b ∧
      ∀ t ∈ Icc a b, fullerCoords (phaseAt X Λ₁ ΛR t) j =
        fullerCoords (phaseAt X Λ₁ ΛR a) j + ∫ s in a..t, l6g_vel u X Λ₁ ΛR s j := by
  obtain ⟨⟨-, -, -, -, -, hX⟩, -, -, hΛ₁, hΛR, -⟩ := hext
  have cX := l6g_cayley (l6g_entry (M := X)
    (V := fun t ↦ controlP (u t) (X t) * X t - X t * controlP (u t) (X t)) hX)
  have cΛ₁ := l6g_cayley (l6g_entry (M := Λ₁) (V := fun t ↦ Λ₁ t * X t - X t * Λ₁ t) hΛ₁)
  have cΛR := l6g_cayley (l6g_entry (M := ΛR)
    (V := fun t ↦ costateRHS (-1) (Λ₁ t) (ΛR t) (X t) (u t)) hΛR)
  fin_cases j
  · refine ⟨cX.1.div_const 2, fun t ht ↦ ?_⟩
    simp only [l6g_vel, fullerCoords, phaseAt, iso_extremalField, Fin.zero_eta,
      Matrix.cons_val_zero]
    rw [intervalIntegral.integral_div, cX.2 t ht, add_div]
  · refine ⟨(cΛ₁.1.const_mul (-I)).div_const 6, fun t ht ↦ ?_⟩
    simp only [l6g_vel, fullerCoords, phaseAt, iso_extremalField, Fin.mk_one,
      Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, cΛ₁.2 t ht]
    ring
  · refine ⟨cΛR.1.div_const 12, fun t ht ↦ ?_⟩
    simp only [l6g_vel, fullerCoords, phaseAt, iso_extremalField, Fin.reduceFinMk,
      Matrix.cons_val]
    rw [intervalIntegral.integral_div, cΛR.2 t ht, add_div]

/-! ### Helpers: the a priori bound and limits of integrals -/

/-- The a priori bound `1 + S(2 + S(2 + 2S))` on the rescaled arcs over `[0, S]`. -/
private noncomputable def l6g_bd (S : ℝ) : ℝ := 1 + S * (2 + S * (2 + 2 * S))

private theorem l6g_one_le_bd {S : ℝ} (hS : 0 ≤ S) : 1 ≤ l6g_bd S := by
  have : 0 ≤ S * (2 + S * (2 + 2 * S)) := by positivity
  unfold l6g_bd; linarith

/-- **A priori bound** for curves close to the Fuller field: if `y = y(0) + ∫ F` on `[0, S]` with
`|y(0)| ≤ 1`, and `F` is within `1` of the Fuller field `fullerField c y` (`|c| ≤ 1`) wherever
`|y| ≤ B + 1`, `B = 1 + S(2 + S(2 + 2S))`, then `|y| ≤ B` on `[0, S]`. The triangular structure
`(z₁, z₂, z₃)' = (-iu, z₁, z₂)` gives the bounds `1 + 2S`, `1 + S(2 + 2S)`, `B` on the three
components in turn (no Grönwall inequality is needed), and a continuity argument (at the first
time `|y| = B + 1`) removes the proviso. -/
private theorem l6g_apriori {S : ℝ} (hS : 0 ≤ S) {y F : ℝ → Fin 3 → ℂ} {c : ℝ → ℂ}
    (hF : IntervalIntegrable F volume 0 S)
    (hy : ∀ s ∈ Icc 0 S, y s = y 0 + ∫ σ in (0 : ℝ)..s, F σ) (hy0 : ‖y 0‖ ≤ 1)
    (hc : ∀ σ ∈ Icc 0 S, ‖c σ‖ ≤ 1)
    (hclose : ∀ σ ∈ Icc 0 S, ‖y σ‖ ≤ l6g_bd S + 1 → ‖F σ - fullerField (c σ) (y σ)‖ ≤ 1) :
    ∀ s ∈ Icc 0 S, ‖y s‖ ≤ l6g_bd S := by
  have hB1 := l6g_one_le_bd hS
  have h0S : (0 : ℝ) ∈ Icc 0 S := ⟨le_rfl, hS⟩
  have hFs : ∀ s ∈ Icc 0 S, IntervalIntegrable F volume 0 s := fun s hs ↦
    l6g_intervalIntegrable_mono hF hS h0S hs
  have hyj : ∀ s ∈ Icc 0 S, ∀ j, y s j = y 0 j + ∫ σ in (0 : ℝ)..s, F σ j := fun s hs j ↦ by
    rw [← l6g_integral_apply (hFs s hs) j, ← Pi.add_apply, ← hy s hs]
  -- a bound on a component from a bound on its derivative
  have hcomp : ∀ s ∈ Icc 0 S, ∀ j : Fin 3, ∀ C : ℝ, (∀ σ ∈ Ico 0 s, ‖F σ j‖ ≤ C) →
      ‖y s j‖ ≤ 1 + C * s := by
    intro s hs j C hC
    rw [hyj s hs j]
    have h1 : ‖y 0 j‖ ≤ 1 := (norm_le_pi_norm (y 0) j).trans hy0
    have h2 : ‖∫ σ in (0 : ℝ)..s, F σ j‖ ≤ C * |s - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const_ae
      have hsn : ∀ᵐ σ : ℝ, σ ≠ s := by simp [ae_iff, measure_singleton]
      filter_upwards [hsn] with σ hσs hσ
      rw [uIoc_of_le hs.1] at hσ
      exact hC σ ⟨hσ.1.le, lt_of_le_of_ne hσ.2 hσs⟩
    rw [sub_zero, abs_of_nonneg hs.1] at h2
    exact (norm_add_le _ _).trans (by linarith)
  -- the bound at `s`, if `y` stays in the ball of radius `B + 1` before `s`
  have key : ∀ s ∈ Icc 0 S, (∀ σ ∈ Ico 0 s, ‖y σ‖ ≤ l6g_bd S + 1) → ‖y s‖ ≤ l6g_bd S := by
    intro s hs hR
    have hσS : ∀ σ ∈ Icc 0 s, σ ∈ Icc 0 S := fun σ hσ ↦ ⟨hσ.1, hσ.2.trans hs.2⟩
    have herr : ∀ σ ∈ Ico 0 s, ∀ j, ‖F σ j‖ ≤ ‖fullerField (c σ) (y σ) j‖ + 1 := by
      intro σ hσ j
      have hσ' : σ ∈ Icc 0 S := ⟨hσ.1, hσ.2.le.trans hs.2⟩
      have h1 := (norm_le_pi_norm (F σ - fullerField (c σ) (y σ)) j).trans
        (hclose σ hσ' (hR σ hσ))
      have h2 := norm_sub_norm_le (F σ j) (fullerField (c σ) (y σ) j)
      rw [Pi.sub_apply] at h1
      linarith
    have b0 : ∀ σ ∈ Icc 0 s, ‖y σ 0‖ ≤ 1 + 2 * S := by
      intro σ hσ
      have := hcomp σ (hσS σ hσ) 0 2 fun σ' hσ' ↦ by
        have h1 := herr σ' ⟨hσ'.1, hσ'.2.trans_le hσ.2⟩ 0
        have hcn := hc σ' ⟨hσ'.1, (hσ'.2.le.trans hσ.2).trans hs.2⟩
        simp only [fullerField, Matrix.cons_val_zero, norm_mul, norm_neg, Complex.norm_I,
          one_mul] at h1
        linarith
      nlinarith [hσ.2, hs.2]
    have b1 : ∀ σ ∈ Icc 0 s, ‖y σ 1‖ ≤ 1 + S * (2 + 2 * S) := by
      intro σ hσ
      have := hcomp σ (hσS σ hσ) 1 (2 + 2 * S) fun σ' hσ' ↦ by
        have h1 := herr σ' ⟨hσ'.1, hσ'.2.trans_le hσ.2⟩ 1
        have hb := b0 σ' ⟨hσ'.1, hσ'.2.le.trans hσ.2⟩
        simp only [fullerField, Matrix.cons_val_one, Matrix.cons_val_zero] at h1
        linarith
      have : (2 + 2 * S) * σ ≤ (2 + 2 * S) * S :=
        mul_le_mul_of_nonneg_left (hσ.2.trans hs.2) (by linarith)
      linarith
    have b2 : ∀ σ ∈ Icc 0 s, ‖y σ 2‖ ≤ l6g_bd S := by
      intro σ hσ
      have := hcomp σ (hσS σ hσ) 2 (2 + S * (2 + 2 * S)) fun σ' hσ' ↦ by
        have h1 := herr σ' ⟨hσ'.1, hσ'.2.trans_le hσ.2⟩ 2
        have hb := b1 σ' ⟨hσ'.1, hσ'.2.le.trans hσ.2⟩
        rw [show fullerField (c σ') (y σ') 2 = y σ' 1 from rfl] at h1
        linarith
      have : (2 + S * (2 + 2 * S)) * σ ≤ (2 + S * (2 + 2 * S)) * S :=
        mul_le_mul_of_nonneg_left (hσ.2.trans hs.2) (by positivity)
      unfold l6g_bd; linarith
    have hs' : s ∈ Icc 0 s := ⟨hs.1, le_rfl⟩
    refine (pi_norm_le_iff_of_nonneg (by linarith)).2 fun j ↦ ?_
    fin_cases j
    · have := b0 s hs'
      have : 0 ≤ S * (S * (2 + 2 * S)) := by positivity
      unfold l6g_bd; simp only [Fin.zero_eta]; nlinarith
    · have := b1 s hs'
      have : S * (2 + 2 * S) ≤ S * (2 + S * (2 + 2 * S)) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hS
      unfold l6g_bd; simp only [Fin.mk_one]; linarith
    · exact b2 s hs'
  -- the continuity argument
  have hcont : ContinuousOn y (Icc 0 S) := continuousOn_Icc_of_eq_add_integral hS hF hy
  have hlt : ∀ s ∈ Icc 0 S, ‖y s‖ < l6g_bd S + 1 := by
    by_contra hne
    push Not at hne
    obtain ⟨s₀, hs₀, hs₀R⟩ := hne
    have hAc : IsClosed (Icc 0 S ∩ (fun s ↦ ‖y s‖) ⁻¹' Ici (l6g_bd S + 1)) :=
      (continuous_norm.comp_continuousOn hcont).preimage_isClosed_of_isClosed isClosed_Icc
        isClosed_Ici
    have hAb : BddBelow (Icc 0 S ∩ (fun s ↦ ‖y s‖) ⁻¹' Ici (l6g_bd S + 1)) :=
      ⟨0, fun x hx ↦ hx.1.1⟩
    have hmem := hAc.csInf_mem ⟨s₀, hs₀, hs₀R⟩ hAb
    have hbefore : ∀ σ ∈ Ico 0 (sInf (Icc 0 S ∩ (fun s ↦ ‖y s‖) ⁻¹' Ici (l6g_bd S + 1))),
        ‖y σ‖ ≤ l6g_bd S + 1 := fun σ hσ ↦ by
      by_contra hσR
      push Not at hσR
      exact absurd (csInf_le hAb ⟨⟨hσ.1, hσ.2.le.trans hmem.1.2⟩, hσR.le⟩) (not_le.2 hσ.2)
    have h1 := key _ hmem.1 hbefore
    have h2 : l6g_bd S + 1 ≤ ‖y (sInf (Icc 0 S ∩ (fun s ↦ ‖y s‖) ⁻¹' Ici (l6g_bd S + 1)))‖ :=
      hmem.2
    linarith
  intro s hs
  exact key s hs fun σ hσ ↦ (hlt σ ⟨hσ.1, hσ.2.le.trans hs.2⟩).le

/-- A function a.e.-strongly measurable and bounded on `[0, S]` is integrable on every
subinterval. -/
private theorem l6g_intervalIntegrable_of_aesm {E : Type*} [NormedAddCommGroup E] {S C : ℝ}
    {f : ℝ → E} (hf : AEStronglyMeasurable f (volume.restrict (Icc 0 S)))
    (hb : ∀ σ ∈ Icc 0 S, ‖f σ‖ ≤ C) {s₁ s₂ : ℝ} (hs₁ : s₁ ∈ Icc 0 S) (hs₂ : s₂ ∈ Icc 0 S) :
    IntervalIntegrable f volume s₁ s₂ := by
  have hS : 0 ≤ S := hs₁.1.trans hs₁.2
  have h : IntegrableOn f (Icc 0 S) volume :=
    Integrable.of_bound hf C (ae_restrict_of_forall_mem measurableSet_Icc hb)
  have h' : IntervalIntegrable f volume 0 S :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hS).2 h
  exact l6g_intervalIntegrable_mono h' hS hs₁ hs₂

/-- **Dominated convergence** on subintervals of `[0, S]`. -/
private theorem l6g_tendsto_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S C : ℝ} {f : ℕ → ℝ → E} {f₀ : ℝ → E}
    (hfm : ∀ k, AEStronglyMeasurable (f k) (volume.restrict (Icc 0 S)))
    (hb : ∀ k, ∀ σ ∈ Icc 0 S, ‖f k σ‖ ≤ C)
    (hlim : ∀ σ ∈ Icc 0 S, Tendsto (fun k ↦ f k σ) atTop (𝓝 (f₀ σ))) {s₁ s₂ : ℝ}
    (hs₁ : s₁ ∈ Icc 0 S) (hs₂ : s₂ ∈ Icc 0 S) :
    Tendsto (fun k ↦ ∫ σ in s₁..s₂, f k σ) atTop (𝓝 (∫ σ in s₁..s₂, f₀ σ)) := by
  have hsub : uIoc s₁ s₂ ⊆ Icc 0 S := (uIoc_subset_uIcc).trans (uIcc_subset_Icc hs₁ hs₂)
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ ↦ C)
    (Eventually.of_forall fun k ↦ (hfm k).mono_measure (Measure.restrict_mono hsub le_rfl))
    (Eventually.of_forall fun k ↦ ae_of_all _ fun σ hσ ↦ hb k σ (hsub hσ))
    intervalIntegrable_const (ae_of_all _ fun σ hσ ↦ hlim σ (hsub hσ))

private theorem l6g_continuous_RR : Continuous fun p : ℂ × ℂ ↦ RR p.1 p.2 := by
  simp only [RR_eq_re_mul_add_im_mul]
  fun_prop

private theorem l6g_aesm_RR {μ : Measure ℝ} {f g : ℝ → ℂ} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) : AEStronglyMeasurable (fun σ ↦ RR (f σ) (g σ)) μ :=
  l6g_continuous_RR.comp_aestronglyMeasurable (hf.prodMk hg)

/-- Restarting a primitive at an interior point. -/
private theorem l6g_restart {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : ℝ}
    {f g : ℝ → E} (hg : IntervalIntegrable g volume 0 S)
    (hf : ∀ t ∈ Icc 0 S, f t = f 0 + ∫ σ in (0 : ℝ)..t, g σ) {s₁ s₂ : ℝ} (hs₁ : s₁ ∈ Icc 0 S)
    (hs₂ : s₂ ∈ Icc 0 S) : ∀ t ∈ Icc s₁ s₂, f t = f s₁ + ∫ σ in s₁..t, g σ := by
  intro t ht
  have hS : 0 ≤ S := hs₁.1.trans hs₁.2
  have h0 : (0 : ℝ) ∈ Icc 0 S := ⟨le_rfl, hS⟩
  have htS : t ∈ Icc 0 S := ⟨hs₁.1.trans ht.1, ht.2.trans hs₂.2⟩
  rw [hf t htS, hf s₁ hs₁, add_assoc, ← intervalIntegral.integral_add_adjacent_intervals
    (l6g_intervalIntegrable_mono hg hS h0 hs₁) (l6g_intervalIntegrable_mono hg hS hs₁ htS)]

private theorem l6g_exists_vertex {v₀ : ℂ} (hv₀ : v₀ ∈ VT) :
    ∃ m : Fin 3, simplexToUT (vertex m) = v₀ := by
  rcases mem_VT.1 hv₀ with rfl | rfl | rfl
  · exact ⟨0, by simp [l6g_simplexToUT_vertex]⟩
  · exact ⟨1, by simp [l6g_simplexToUT_vertex]⟩
  · exact ⟨2, by simp [l6g_simplexToUT_vertex]⟩

/-- **Relaxed limits of rescaled arcs** (the abstract form of `exists_tendsto_rescaledArc`): curves
`Y_k = Y_k(0) + ∫ F_k` on `[0, S]`, with `F_k = rescaledField ρ_k v_k Y_k`, controls `v_k` in the
simplex, `ρ_k → 0⁺`, `Y_k(0) → ξ`, `|Y_k(0)| ≤ 1`, the maximum condition of the Reinhardt
Hamiltonian along `Y_k`, and the rescaled field within `1` of the Fuller field on the ball of the
a priori bound. Along a subsequence, `Y_k → y` uniformly and `∫ simplexToUT v_k → ∫ w`, where
`(y, w)` is a trajectory of the Fuller system from `ξ` with controls in `U_T` satisfying the maximum
condition. Steps 1–4 of the plan in the module docstring. -/
private theorem l6g_limit {S : ℝ} (hS : 0 < S) {ξ : Fin 3 → ℂ} {ρ : ℕ → ℝ}
    (hρ : Tendsto ρ atTop (𝓝[>] 0)) {Y F : ℕ → ℝ → Fin 3 → ℂ} {v : ℕ → ℝ → Fin 3 → ℝ}
    (hF : ∀ k, IntervalIntegrable (F k) volume 0 S)
    (hY : ∀ k, ∀ s ∈ Icc 0 S, Y k s = Y k 0 + ∫ σ in (0 : ℝ)..s, F k σ)
    (hFv : ∀ k, ∀ σ ∈ Icc 0 S, F k σ = rescaledField (ρ k) (v k σ) (Y k σ))
    (hv : ∀ k, ∀ σ ∈ Icc 0 S, v k σ ∈ controlSimplex)
    (hvm : ∀ k, Measurable fun σ ↦ simplexToUT (v k σ))
    (hY0 : Tendsto (fun k ↦ Y k 0) atTop (𝓝 ξ)) (hY0n : ∀ k, ‖Y k 0‖ ≤ 1)
    (hmax : ∀ k, ∀ᵐ σ, σ ∈ Icc 0 S → ∀ v' ∈ controlSimplex,
      phaseHam (phaseOfFuller (scale (ρ k) (Y k σ))) v' ≤
        phaseHam (phaseOfFuller (scale (ρ k) (Y k σ))) (v k σ))
    (hclose : ∀ k, ∀ p ∈ controlSimplex ×ˢ Metric.closedBall (0 : Fin 3 → ℂ) (l6g_bd S + 1),
      dist (fullerField (simplexToUT p.1) p.2) (rescaledField (ρ k) p.1 p.2) < 1) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ (y : ℝ → Fin 3 → ℂ) (w : ℝ → ℂ),
      IsTrajectory UT 0 S y w ∧ MaxCondition UT 0 S y w ∧ y 0 = ξ ∧
      TendstoUniformlyOn (fun k ↦ Y (ψ k)) y atTop (Icc 0 S) ∧
      ∀ s ∈ Icc 0 S, Tendsto (fun k ↦ ∫ σ in (0 : ℝ)..s, simplexToUT (v (ψ k) σ)) atTop
        (𝓝 (∫ σ in (0 : ℝ)..s, w σ)) := by
  have h0S : (0 : ℝ) ∈ Icc 0 S := ⟨le_rfl, hS.le⟩
  have hSS : S ∈ Icc 0 S := ⟨hS.le, le_rfl⟩
  have hB1 := l6g_one_le_bd hS.le
  /- Step 1: bounds. -/
  have hcU : ∀ k, ∀ σ ∈ Icc 0 S, simplexToUT (v k σ) ∈ UT := fun k σ hσ ↦
    l6g_simplexToUT_mem (hv k σ hσ)
  have hcn : ∀ k, ∀ σ ∈ Icc 0 S, ‖simplexToUT (v k σ)‖ ≤ 1 := fun k σ hσ ↦
    l6g_norm_simplexToUT_le (hv k σ hσ)
  have hcint : ∀ k, ∀ s ∈ Icc 0 S, ∀ s' ∈ Icc 0 S,
      IntervalIntegrable (fun σ ↦ simplexToUT (v k σ)) volume s s' := fun k s hs s' hs' ↦
    l6g_intervalIntegrable_of_bound (hvm k).aestronglyMeasurable (hcn k) hs hs'
  have hball : ∀ k, ∀ σ ∈ Icc 0 S, ‖Y k σ‖ ≤ l6g_bd S + 1 →
      ‖F k σ - fullerField (simplexToUT (v k σ)) (Y k σ)‖ < 1 := fun k σ hσ hσB ↦ by
    have := hclose k (v k σ, Y k σ) ⟨hv k σ hσ, mem_closedBall_zero_iff.2 hσB⟩
    rwa [dist_comm, dist_eq_norm, ← hFv k σ hσ] at this
  have hYB : ∀ k, ∀ s ∈ Icc 0 S, ‖Y k s‖ ≤ l6g_bd S := fun k ↦
    l6g_apriori hS.le (hF k) (hY k) (hY0n k) (hcn k) fun σ hσ hσB ↦ (hball k σ hσ hσB).le
  have hFB : ∀ k, ∀ σ ∈ Icc 0 S, ‖F k σ‖ ≤ l6g_bd S + 1 := by
    intro k σ hσ
    have h1 := hball k σ hσ ((hYB k σ hσ).trans (by linarith))
    have h2 := l6g_norm_fullerField_le (hcn k σ hσ) (Y k σ)
    have h3 := norm_le_insert' (F k σ) (fullerField (simplexToUT (v k σ)) (Y k σ))
    have h4 : max 1 ‖Y k σ‖ ≤ l6g_bd S := max_le hB1 (hYB k σ hσ)
    linarith
  have hYL : ∀ k, ∀ s ∈ Icc 0 S, ∀ s' ∈ Icc 0 S,
      dist (Y k s) (Y k s') ≤ (l6g_bd S + 1) * dist s s' := fun k ↦
    l6g_dist_le (hF k) (hY k) (hFB k)
  have hVeq : ∀ k, ∀ s ∈ Icc 0 S, (fun t ↦ ∫ σ in (0 : ℝ)..t, simplexToUT (v k σ)) s =
      (fun t ↦ ∫ σ in (0 : ℝ)..t, simplexToUT (v k σ)) 0 +
        ∫ σ in (0 : ℝ)..s, simplexToUT (v k σ) := fun k s _ ↦ by simp
  have hVL1 := fun k ↦ l6g_dist_le (hcint k 0 h0S S hSS) (hVeq k) (hcn k)
  have hVL : ∀ k, ∀ s ∈ Icc 0 S, ∀ s' ∈ Icc 0 S,
      dist (∫ σ in (0 : ℝ)..s, simplexToUT (v k σ)) (∫ σ in (0 : ℝ)..s', simplexToUT (v k σ)) ≤
        (l6g_bd S + 1) * dist s s' := fun k s hs s' hs' ↦
    (hVL1 k s hs s' hs').trans (mul_le_mul_of_nonneg_right (by linarith) dist_nonneg)
  have hVM : ∀ k, ∀ s ∈ Icc 0 S, ‖∫ σ in (0 : ℝ)..s, simplexToUT (v k σ)‖ ≤ l6g_bd S + S := by
    intro k s hs
    have := hVL1 k s hs 0 h0S
    simp only [intervalIntegral.integral_same, dist_zero_right, one_mul] at this
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1] at this
    linarith [hs.2]
  have hYM : ∀ k, ∀ s ∈ Icc 0 S, ‖Y k s‖ ≤ l6g_bd S + S := fun k s hs ↦
    (hYB k s hs).trans (by linarith)
  /- Step 2: Arzelà–Ascoli, and the relaxed control. -/
  obtain ⟨ψ, hψ, y, W, hyc, -, hYu, hVu⟩ :=
    l6g_arzela (V := fun k s ↦ ∫ σ in (0 : ℝ)..s, simplexToUT (v k σ)) hS.le hYL hVL hYM hVM
  have hψt : Tendsto ψ atTop atTop := hψ.tendsto_atTop
  have hρψ : Tendsto (fun k ↦ ρ (ψ k)) atTop (𝓝[>] 0) := hρ.comp hψt
  have hVt : ∀ s ∈ Icc 0 S, Tendsto (fun k ↦ ∫ σ in (0 : ℝ)..s, simplexToUT (v (ψ k) σ)) atTop
      (𝓝 (W s)) := fun s hs ↦ hVu.tendsto_at hs
  obtain ⟨w, hwm, hwU, hwW⟩ := l6g_control_limit hS
    (c := fun k σ ↦ simplexToUT (v (ψ k) σ)) (fun k ↦ hvm (ψ k)) (fun k ↦ hcU (ψ k)) hVt
  have hwn : ∀ σ ∈ Icc 0 S, ‖w σ‖ ≤ 1 := fun σ hσ ↦ l6g_norm_le_one_of_mem_UT (hwU σ hσ)
  have hwint : ∀ s ∈ Icc 0 S, ∀ s' ∈ Icc 0 S, IntervalIntegrable w volume s s' :=
    fun s hs s' hs' ↦ l6g_intervalIntegrable_of_bound hwm.aestronglyMeasurable hwn hs hs'
  have hy0 : y 0 = ξ := tendsto_nhds_unique (hYu.tendsto_at h0S) (hY0.comp hψt)
  have hyB : ∀ σ ∈ Icc 0 S, ‖y σ‖ ≤ l6g_bd S := fun σ hσ ↦
    le_of_tendsto (hYu.tendsto_at hσ).norm (Eventually.of_forall fun k ↦ hYB (ψ k) σ hσ)
  have hYc : ∀ k, ContinuousOn (Y k) (Icc 0 S) := fun k ↦
    continuousOn_Icc_of_eq_add_integral hS.le (hF k) (hY k)
  have hYcj : ∀ k (j : Fin 3), ContinuousOn (fun σ ↦ Y k σ j) (Icc 0 S) := fun k j ↦
    (continuous_apply j).comp_continuousOn (hYc k)
  have hycj : ∀ j : Fin 3, Continuous fun σ ↦ y σ j := fun j ↦ (continuous_apply j).comp hyc
  have hYt : ∀ σ ∈ Icc 0 S, ∀ j : Fin 3, Tendsto (fun k ↦ Y (ψ k) σ j) atTop (𝓝 (y σ j)) :=
    fun σ hσ j ↦ ((continuous_apply j).tendsto _).comp (hYu.tendsto_at hσ)
  /- Step 3: the limit equations. -/
  have herr : ∀ ε > 0, ∀ᶠ k in atTop, ∀ σ ∈ Icc 0 S,
      ‖F (ψ k) σ - fullerField (simplexToUT (v (ψ k) σ)) (Y (ψ k) σ)‖ < ε := by
    intro ε hε
    have hu := Metric.tendstoUniformlyOn_iff.1
      (tendstoUniformlyOn_rescaledField (isCompact_closedBall (0 : Fin 3 → ℂ) (l6g_bd S + 1)))
      ε hε
    filter_upwards [hρψ.eventually hu] with k hk σ hσ
    have := hk (v (ψ k) σ, Y (ψ k) σ)
      ⟨hv _ σ hσ, mem_closedBall_zero_iff.2 ((hYB _ σ hσ).trans (by linarith))⟩
    rwa [dist_comm, dist_eq_norm, ← hFv _ σ hσ] at this
  have hlimeq : ∀ s ∈ Icc 0 S, ∀ j : Fin 3, ∀ (G : ℕ → ℂ) (G₀ : ℂ),
      (∀ k, IntervalIntegrable (fun σ ↦ fullerField (simplexToUT (v k σ)) (Y k σ) j)
        volume 0 s) →
      (∀ k, ∫ σ in (0 : ℝ)..s, fullerField (simplexToUT (v k σ)) (Y k σ) j = G k) →
      Tendsto (fun k ↦ G (ψ k)) atTop (𝓝 G₀) → y s j = y 0 j + G₀ := by
    intro s hs j G G₀ hGi hG hGt
    have hFs : ∀ k, IntervalIntegrable (F k) volume 0 s := fun k ↦
      l6g_intervalIntegrable_mono (hF k) hS.le h0S hs
    have hA : ∀ k, Y k s j - Y k 0 j - G k = ∫ σ in (0 : ℝ)..s,
        (F k σ j - fullerField (simplexToUT (v k σ)) (Y k σ) j) := by
      intro k
      rw [intervalIntegral.integral_sub (l6g_intervalIntegrable_eval (hFs k) j) (hGi k), hG k,
        ← l6g_integral_apply (hFs k) j, hY k s hs, Pi.add_apply]
      ring
    have h1 : Tendsto (fun k ↦ Y (ψ k) s j - Y (ψ k) 0 j - G (ψ k)) atTop
        (𝓝 (y s j - y 0 j - G₀)) := ((hYt s hs j).sub (hYt 0 h0S j)).sub hGt
    have h2 : Tendsto (fun k ↦ Y (ψ k) s j - Y (ψ k) 0 j - G (ψ k)) atTop (𝓝 0) := by
      refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
      have hδ : 0 < ε / (S + 1) := by positivity
      filter_upwards [herr _ hδ] with k hk
      rw [dist_zero_right, hA]
      have hb : ‖∫ σ in (0 : ℝ)..s,
          (F (ψ k) σ j - fullerField (simplexToUT (v (ψ k) σ)) (Y (ψ k) σ) j)‖ ≤
          ε / (S + 1) * |s - 0| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const fun σ hσ ↦ ?_
        have hσ' : σ ∈ Icc 0 S := uIcc_subset_Icc h0S hs (uIoc_subset_uIcc hσ)
        have := (norm_le_pi_norm (F (ψ k) σ -
          fullerField (simplexToUT (v (ψ k) σ)) (Y (ψ k) σ)) j).trans (hk σ hσ').le
        rwa [Pi.sub_apply] at this
      rw [sub_zero, abs_of_nonneg hs.1] at hb
      have : ε / (S + 1) * s < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
        nlinarith [hs.2]
      linarith
    have := tendsto_nhds_unique h1 h2
    linear_combination this
  have heq0 : ∀ s ∈ Icc 0 S, y s 0 = y 0 0 + ∫ σ in (0 : ℝ)..s, -I * w σ := by
    intro s hs
    rw [intervalIntegral.integral_const_mul, hwW s hs]
    exact hlimeq s hs 0 (fun k ↦ -I * ∫ σ in (0 : ℝ)..s, simplexToUT (v k σ)) (-I * W s)
      (fun k ↦ (hcint k 0 h0S s hs).const_mul (-I))
      (fun k ↦ intervalIntegral.integral_const_mul _ _) ((hVt s hs).const_mul (-I))
  have heqj : ∀ s ∈ Icc 0 S, ∀ j : Fin 2,
      y s j.succ = y 0 j.succ + ∫ σ in (0 : ℝ)..s, y σ j.castSucc := by
    intro s hs j
    refine hlimeq s hs j.succ (fun k ↦ ∫ σ in (0 : ℝ)..s, Y k σ j.castSucc) _
      (fun k ↦ ?_) (fun k ↦ ?_) ?_
    · refine ((hYcj k j.castSucc).mono (Icc_subset_Icc_right hs.2)).intervalIntegrable_of_Icc
        hs.1 |>.congr fun σ _ ↦ ?_
      fin_cases j <;> rfl
    · refine intervalIntegral.integral_congr fun σ _ ↦ ?_
      fin_cases j <;> rfl
    · exact l6g_tendsto_integral (C := l6g_bd S)
        (fun k ↦ (hYcj (ψ k) j.castSucc).aestronglyMeasurable measurableSet_Icc)
        (fun k σ hσ ↦ (norm_le_pi_norm _ _).trans (hYB _ σ hσ)) (fun σ hσ ↦ hYt σ hσ _) h0S hs
  have htraj : IsTrajectory UT 0 S y w := by
    refine ⟨hS, hwm, hwU, fun t ht ↦ ⟨heq0 t ht, heqj t ht 0, heqj t ht 1⟩⟩
  /- Step 4: the maximum condition. -/
  have hham : ∀ ε > 0, ∀ᶠ k in atTop, ∀ σ ∈ Icc 0 S, ∀ v' ∈ controlSimplex,
      |24 * ham (Y (ψ k) σ) (simplexToUT v') -
        phaseHam (phaseOfFuller (scale (ρ (ψ k)) (Y (ψ k) σ))) v' / ρ (ψ k) ^ 3| < ε := by
    intro ε hε
    have hu := Metric.tendstoUniformlyOn_iff.1
      (tendstoUniformlyOn_rescaledHam (isCompact_closedBall (0 : Fin 3 → ℂ) (l6g_bd S + 1)))
      ε hε
    filter_upwards [hρψ.eventually hu] with k hk σ hσ v' hv'
    have := hk (v', Y (ψ k) σ)
      ⟨hv', mem_closedBall_zero_iff.2 ((hYB _ σ hσ).trans (by linarith))⟩
    rwa [Real.dist_eq] at this
  have hρpos : ∀ᶠ k in atTop, 0 < ρ (ψ k) := hρψ.eventually self_mem_nhdsWithin
  have hint_le : ∀ v₀ ∈ VT, ∀ s₁ s₂, 0 ≤ s₁ → s₁ ≤ s₂ → s₂ ≤ S →
      ∫ σ in s₁..s₂, (RR v₀ (y σ 2) - RR (w σ) (y σ 2)) ≤ 0 := by
    intro v₀ hv₀ s₁ s₂ h1 h12 h2
    obtain ⟨m, hm⟩ := l6g_exists_vertex hv₀
    have hs₁ : s₁ ∈ Icc 0 S := ⟨h1, h12.trans h2⟩
    have hs₂ : s₂ ∈ Icc 0 S := ⟨h1.trans h12, h2⟩
    have hsub : Icc s₁ s₂ ⊆ Icc 0 S := Icc_subset_Icc h1 h2
    have hv₀n : ‖v₀‖ = 1 := norm_eq_one_of_mem_VT hv₀
    -- integrability
    have hPm : ∀ k, AEStronglyMeasurable (fun σ ↦ RR v₀ (Y (ψ k) σ 2))
        (volume.restrict (Icc 0 S)) := fun k ↦
      l6g_aesm_RR aestronglyMeasurable_const
        ((hYcj (ψ k) 2).aestronglyMeasurable measurableSet_Icc)
    have hPb : ∀ k, ∀ σ ∈ Icc 0 S, ‖RR v₀ (Y (ψ k) σ 2)‖ ≤ l6g_bd S := fun k σ hσ ↦ by
      rw [Real.norm_eq_abs]
      exact (l6g_abs_RR_le _ _).trans (by
        rw [hv₀n, one_mul]; exact (norm_le_pi_norm _ _).trans (hYB _ σ hσ))
    have hQm : ∀ k, AEStronglyMeasurable (fun σ ↦ RR (simplexToUT (v (ψ k) σ)) (Y (ψ k) σ 2))
        (volume.restrict (Icc 0 S)) := fun k ↦
      l6g_aesm_RR (hvm (ψ k)).aestronglyMeasurable.restrict
        ((hYcj (ψ k) 2).aestronglyMeasurable measurableSet_Icc)
    have hQb : ∀ k, ∀ σ ∈ Icc 0 S,
        ‖RR (simplexToUT (v (ψ k) σ)) (Y (ψ k) σ 2)‖ ≤ l6g_bd S := fun k σ hσ ↦ by
      rw [Real.norm_eq_abs]
      exact (l6g_abs_RR_le _ _).trans (by
        nlinarith [hcn (ψ k) σ hσ, (norm_le_pi_norm (Y (ψ k) σ) 2).trans (hYB _ σ hσ),
          norm_nonneg (simplexToUT (v (ψ k) σ)), norm_nonneg (Y (ψ k) σ 2)])
    have hPi : ∀ k, IntervalIntegrable (fun σ ↦ RR v₀ (Y (ψ k) σ 2)) volume s₁ s₂ := fun k ↦
      l6g_intervalIntegrable_of_aesm (hPm k) (hPb k) hs₁ hs₂
    have hQi : ∀ k, IntervalIntegrable (fun σ ↦ RR (simplexToUT (v (ψ k) σ)) (Y (ψ k) σ 2))
        volume s₁ s₂ := fun k ↦ l6g_intervalIntegrable_of_aesm (hQm k) (hQb k) hs₁ hs₂
    -- Claim A: the integrals along the rescaled arcs are almost nonpositive
    have hA : ∀ ε > 0, ∀ᶠ k in atTop,
        ∫ σ in s₁..s₂, (RR v₀ (Y (ψ k) σ 2) - RR (simplexToUT (v (ψ k) σ)) (Y (ψ k) σ 2)) ≤
          ε := by
      intro ε hε
      have hδ : 0 < ε / (S + 1) := by positivity
      filter_upwards [hham (12 * (ε / (S + 1))) (by positivity), hρpos] with k hk hρk
      have hpt : ∀ᵐ σ, σ ∈ Icc 0 S →
          RR v₀ (Y (ψ k) σ 2) - RR (simplexToUT (v (ψ k) σ)) (Y (ψ k) σ 2) ≤ ε / (S + 1) := by
        filter_upwards [hmax (ψ k)] with σ hσmax hσ
        have hd := div_le_div_of_nonneg_right (hσmax hσ (vertex m) (l6g_vertex_mem m))
          (pow_pos hρk 3).le
        have e1 := hk σ hσ (vertex m) (l6g_vertex_mem m)
        have e2 := hk σ hσ (v (ψ k) σ) (hv _ σ hσ)
        rw [hm] at e1
        rw [abs_lt] at e1 e2
        have e3 : ham (Y (ψ k) σ) v₀ - ham (Y (ψ k) σ) (simplexToUT (v (ψ k) σ)) =
            RR v₀ (Y (ψ k) σ 2) - RR (simplexToUT (v (ψ k) σ)) (Y (ψ k) σ 2) := by
          simp only [ham]; ring
        linarith [e1.1, e1.2, e2.1, e2.2]
      calc ∫ σ in s₁..s₂, (RR v₀ (Y (ψ k) σ 2) - RR (simplexToUT (v (ψ k) σ)) (Y (ψ k) σ 2))
          ≤ ∫ σ in s₁..s₂, ε / (S + 1) := by
            refine intervalIntegral.integral_mono_ae_restrict h12 ((hPi k).sub (hQi k))
              intervalIntegrable_const ?_
            refine (ae_restrict_iff' measurableSet_Icc).2 ?_
            filter_upwards [hpt] with σ hσ hσI using hσ (hsub hσI)
        _ = (s₂ - s₁) * (ε / (S + 1)) := by rw [intervalIntegral.integral_const, smul_eq_mul]
        _ ≤ ε := by
            rw [mul_div_assoc', div_le_iff₀ (by linarith)]
            nlinarith
    -- Claim B: the integrals converge
    have hPt : Tendsto (fun k ↦ ∫ σ in s₁..s₂, RR v₀ (Y (ψ k) σ 2)) atTop
        (𝓝 (∫ σ in s₁..s₂, RR v₀ (y σ 2))) :=
      l6g_tendsto_integral hPm hPb (fun σ hσ ↦
        ((l6g_continuous_RR.comp (Continuous.prodMk continuous_const continuous_id)).tendsto
          _).comp (hYt σ hσ 2)) hs₁ hs₂
    -- the control term: integration by parts
    have hy2 := l6g_restart (f := fun σ ↦ y σ 2) (g := fun σ ↦ y σ 1)
      ((hycj 1).continuousOn.intervalIntegrable_of_Icc hS.le) (fun t ht ↦ heqj t ht 1) hs₁ hs₂
    have hy1c : ContinuousOn (fun σ ↦ y σ 1) (Icc s₁ s₂) := (hycj 1).continuousOn
    have hIBPk : ∀ k, ∫ σ in s₁..s₂, RR (simplexToUT (v (ψ k) σ)) (y σ 2) =
        RR (∫ σ in (0 : ℝ)..s₂, simplexToUT (v (ψ k) σ)) (y s₂ 2) -
          RR (∫ σ in (0 : ℝ)..s₁, simplexToUT (v (ψ k) σ)) (y s₁ 2) -
          ∫ σ in s₁..s₂, RR (∫ τ in (0 : ℝ)..σ, simplexToUT (v (ψ k) τ)) (y σ 1) := fun k ↦
      l6g_ibp h12 (hcint _ s₁ hs₁ s₂ hs₂)
        (l6g_restart (hcint (ψ k) 0 h0S S hSS) (hVeq (ψ k)) hs₁ hs₂) hy1c hy2
    have hW : ∀ t ∈ Icc 0 S, W t = W 0 + ∫ σ in (0 : ℝ)..t, w σ := fun t ht ↦ by
      rw [← hwW t ht, ← hwW 0 h0S, intervalIntegral.integral_same, zero_add]
    have hIBP : ∫ σ in s₁..s₂, RR (w σ) (y σ 2) =
        RR (W s₂) (y s₂ 2) - RR (W s₁) (y s₁ 2) - ∫ σ in s₁..s₂, RR (W σ) (y σ 1) :=
      l6g_ibp h12 (hwint s₁ hs₁ s₂ hs₂) (l6g_restart (hwint 0 h0S S hSS) hW hs₁ hs₂) hy1c hy2
    have hy1B : ∀ σ ∈ Icc 0 S, ‖y σ 1‖ ≤ l6g_bd S := fun σ hσ ↦
      (norm_le_pi_norm _ _).trans (hyB σ hσ)
    have hVc : ∀ k, ContinuousOn (fun t ↦ ∫ σ in (0 : ℝ)..t, simplexToUT (v k σ)) (Icc 0 S) :=
      fun k ↦ continuousOn_Icc_of_eq_add_integral hS.le (hcint k 0 h0S S hSS) (hVeq k)
    have hRt : Tendsto (fun k ↦ ∫ σ in s₁..s₂,
        RR (∫ τ in (0 : ℝ)..σ, simplexToUT (v (ψ k) τ)) (y σ 1)) atTop
        (𝓝 (∫ σ in s₁..s₂, RR (W σ) (y σ 1))) := by
      refine l6g_tendsto_integral (C := (l6g_bd S + S) * l6g_bd S)
        (fun k ↦ l6g_aesm_RR ((hVc (ψ k)).aestronglyMeasurable measurableSet_Icc)
          ((hycj 1).aestronglyMeasurable.restrict)) (fun k σ hσ ↦ ?_)
        (fun σ hσ ↦ (l6g_continuous_RR.tendsto _).comp ((hVt σ hσ).prodMk_nhds
          tendsto_const_nhds)) hs₁ hs₂
      rw [Real.norm_eq_abs]
      exact (l6g_abs_RR_le _ _).trans (mul_le_mul (hVM _ σ hσ) (hy1B σ hσ) (norm_nonneg _)
        (by linarith))
    have hCt : Tendsto (fun k ↦ ∫ σ in s₁..s₂, RR (simplexToUT (v (ψ k) σ)) (y σ 2)) atTop
        (𝓝 (∫ σ in s₁..s₂, RR (w σ) (y σ 2))) := by
      simp only [hIBPk, hIBP]
      refine (((l6g_continuous_RR.tendsto _).comp ((hVt s₂ hs₂).prodMk_nhds
        tendsto_const_nhds)).sub ((l6g_continuous_RR.tendsto _).comp ((hVt s₁ hs₁).prodMk_nhds
        tendsto_const_nhds))).sub hRt
    -- the defect `RR(c_k, Y_k - y)`
    have hDt : Tendsto (fun k ↦ ∫ σ in s₁..s₂,
        RR (simplexToUT (v (ψ k) σ)) (Y (ψ k) σ 2 - y σ 2)) atTop (𝓝 (∫ σ in s₁..s₂, (0 : ℝ))) := by
      refine l6g_tendsto_integral (C := 2 * l6g_bd S)
        (fun k ↦ l6g_aesm_RR (hvm (ψ k)).aestronglyMeasurable.restrict
          (((hYcj (ψ k) 2).sub (hycj 2).continuousOn).aestronglyMeasurable measurableSet_Icc))
        (fun k σ hσ ↦ ?_) (fun σ hσ ↦ ?_) hs₁ hs₂
      · simp only [Pi.sub_apply]
        rw [Real.norm_eq_abs]
        refine (l6g_abs_RR_le _ _).trans ?_
        have := norm_sub_le (Y (ψ k) σ 2) (y σ 2)
        have h3 := (norm_le_pi_norm (Y (ψ k) σ) 2).trans (hYB _ σ hσ)
        have h4 := (norm_le_pi_norm (y σ) 2).trans (hyB σ hσ)
        nlinarith [hcn (ψ k) σ hσ, norm_nonneg (simplexToUT (v (ψ k) σ)),
          norm_nonneg (Y (ψ k) σ 2 - y σ 2)]
      · simp only [Pi.sub_apply]
        refine squeeze_zero_norm (a := fun k ↦ ‖Y (ψ k) σ 2 - y σ 2‖) (fun k ↦ ?_) ?_
        · rw [Real.norm_eq_abs]
          refine (l6g_abs_RR_le _ _).trans ?_
          have := hcn (ψ k) σ hσ
          nlinarith [norm_nonneg (Y (ψ k) σ 2 - y σ 2), norm_nonneg (simplexToUT (v (ψ k) σ))]
        · have := (tendsto_iff_norm_sub_tendsto_zero.1 (hYt σ hσ 2))
          exact this
    have hDi : ∀ k, IntervalIntegrable
        (fun σ ↦ RR (simplexToUT (v (ψ k) σ)) (Y (ψ k) σ 2 - y σ 2)) volume s₁ s₂ := fun k ↦ by
      have h := (hQi k).sub (l6g_intervalIntegrable_of_aesm (C := l6g_bd S)
        (l6g_aesm_RR (hvm (ψ k)).aestronglyMeasurable.restrict
          ((hycj 2).aestronglyMeasurable.restrict)) (fun σ hσ ↦ by
            rw [Real.norm_eq_abs]
            refine (l6g_abs_RR_le _ _).trans ?_
            nlinarith [hcn (ψ k) σ hσ, (norm_le_pi_norm (y σ) 2).trans (hyB σ hσ),
              norm_nonneg (simplexToUT (v (ψ k) σ)), norm_nonneg (y σ 2)]) hs₁ hs₂)
      refine h.congr fun σ _ ↦ ?_
      simp only [l6g_RR_sub_right]
    have hCi : ∀ k, IntervalIntegrable (fun σ ↦ RR (simplexToUT (v (ψ k) σ)) (y σ 2))
        volume s₁ s₂ := fun k ↦ by
      refine ((hQi k).sub (hDi k)).congr fun σ _ ↦ ?_
      simp only [l6g_RR_sub_right]; ring
    have hIt : Tendsto (fun k ↦ ∫ σ in s₁..s₂,
        (RR v₀ (Y (ψ k) σ 2) - RR (simplexToUT (v (ψ k) σ)) (Y (ψ k) σ 2))) atTop
        (𝓝 (∫ σ in s₁..s₂, (RR v₀ (y σ 2) - RR (w σ) (y σ 2)))) := by
      have e : ∀ k, ∫ σ in s₁..s₂,
          (RR v₀ (Y (ψ k) σ 2) - RR (simplexToUT (v (ψ k) σ)) (Y (ψ k) σ 2)) =
          (∫ σ in s₁..s₂, RR v₀ (Y (ψ k) σ 2)) -
            ((∫ σ in s₁..s₂, RR (simplexToUT (v (ψ k) σ)) (Y (ψ k) σ 2 - y σ 2)) +
              ∫ σ in s₁..s₂, RR (simplexToUT (v (ψ k) σ)) (y σ 2)) := fun k ↦ by
        rw [intervalIntegral.integral_sub (hPi k) (hQi k), ← intervalIntegral.integral_add
          (hDi k) (hCi k)]
        congr 1
        refine intervalIntegral.integral_congr fun σ _ ↦ ?_
        simp only [l6g_RR_sub_right]; ring
      have e₀ : ∫ σ in s₁..s₂, (RR v₀ (y σ 2) - RR (w σ) (y σ 2)) =
          (∫ σ in s₁..s₂, RR v₀ (y σ 2)) - ((∫ σ in s₁..s₂, (0 : ℝ)) +
            ∫ σ in s₁..s₂, RR (w σ) (y σ 2)) := by
        rw [intervalIntegral.integral_zero, zero_add, intervalIntegral.integral_sub]
        · exact ((l6g_continuous_RR.comp (Continuous.prodMk continuous_const
            (hycj 2))).continuousOn).intervalIntegrable
        · exact l6g_intervalIntegrable_of_aesm (C := l6g_bd S)
            (l6g_aesm_RR hwm.aestronglyMeasurable.restrict
              ((hycj 2).aestronglyMeasurable.restrict)) (fun σ hσ ↦ by
                rw [Real.norm_eq_abs]
                refine (l6g_abs_RR_le _ _).trans ?_
                nlinarith [hwn σ hσ, (norm_le_pi_norm (y σ) 2).trans (hyB σ hσ),
                  norm_nonneg (w σ), norm_nonneg (y σ 2)]) hs₁ hs₂
      simp only [e, e₀]
      exact hPt.sub (hDt.add hCt)
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    rw [zero_add]
    exact le_of_tendsto hIt (hA ε hε)
  have hmaxc : MaxCondition UT 0 S y w := by
    have hae : ∀ v₀ ∈ VT, ∀ᵐ σ, σ ∈ Icc 0 S → RR v₀ (y σ 2) - RR (w σ) (y σ 2) ≤ 0 := by
      intro v₀ hv₀
      refine l6g_ae_nonpos ?_ (hint_le v₀ hv₀)
      refine l6g_intervalIntegrable_of_aesm (C := 2 * l6g_bd S)
        (l6g_aesm_RR aestronglyMeasurable_const (hycj 2).aestronglyMeasurable.restrict |>.sub
          (l6g_aesm_RR hwm.aestronglyMeasurable.restrict
            (hycj 2).aestronglyMeasurable.restrict)) (fun σ hσ ↦ ?_) h0S hSS
      have h3 := (norm_le_pi_norm (y σ) 2).trans (hyB σ hσ)
      have a1 := l6g_abs_RR_le v₀ (y σ 2)
      have a2 := l6g_abs_RR_le (w σ) (y σ 2)
      rw [norm_eq_one_of_mem_VT hv₀] at a1
      rw [Real.norm_eq_abs]
      refine (abs_sub _ _).trans ?_
      nlinarith [hwn σ hσ, norm_nonneg (w σ), norm_nonneg (y σ 2)]
    filter_upwards [hae 1 one_mem_VT, hae ζ ζ_mem_VT, hae (ζ ^ 2) ζ_sq_mem_VT] with σ h1 h2 h3 hσ
    refine l6g_ham_le_of_VT fun v' hv' ↦ ?_
    have key : ∀ v₀ : ℂ, RR v₀ (y σ 2) - RR (w σ) (y σ 2) ≤ 0 → ham (y σ) v₀ ≤ ham (y σ) (w σ) :=
      fun v₀ hv₀ ↦ by simp only [ham]; linarith
    rcases mem_VT.1 hv' with rfl | rfl | rfl
    exacts [key _ (h1 hσ), key _ (h2 hσ), key _ (h3 hσ)]
  refine ⟨ψ, hψ, y, w, htraj, hmaxc, hy0, hYu, fun s hs ↦ ?_⟩
  rw [hwW s hs]
  exact hVt s hs

/-- The radius `ρ_n = φ(ẑ(q_n))` of the `n`-th switching point in blow-up coordinates. -/
noncomputable def switchRadius (X Λ₁ ΛR : ℝ → Mat2) (τ : ℕ → ℝ) (n : ℕ) : ℝ :=
  weightedNorm (fullerCoords (phaseAt X Λ₁ ΛR (τ n)))

/-- The rescaled arc after the `n`-th switching time: `s ↦ scale ρ_n⁻¹ ẑ(q(τ_n + s ρ_n))`
(rescaled coordinates and rescaled time `s = t/ρ_n`, TeX 12908–12912). At `s = 0` it is the
angular component `ξ_n` of the switching point. -/
noncomputable def rescaledArc (X Λ₁ ΛR : ℝ → Mat2) (τ : ℕ → ℝ) (n : ℕ) (s : ℝ) : Fin 3 → ℂ :=
  scale (switchRadius X Λ₁ ΛR τ n)⁻¹
    (fullerCoords (phaseAt X Λ₁ ΛR (τ n + s * switchRadius X Λ₁ ΛR τ n)))

/-- The rescaled control after the `n`-th switching time, as a point of `U_T`. -/
noncomputable def rescaledControl (u : ℝ → Fin 3 → ℝ) (X Λ₁ ΛR : ℝ → Mat2) (τ : ℕ → ℝ) (n : ℕ)
    (s : ℝ) : ℂ :=
  simplexToUT (u (τ n + s * switchRadius X Λ₁ ΛR τ n))

/-! ### The rescaled arcs -/

/-- The rescaled arc of a solution of `ẑ' = ẑ(q')`, in integral form (the change of variables
`t = τ + s ρ`, with `scale ρ⁻¹` linear). -/
private theorem l6g_arc_core {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {X Λ₁ ΛR : ℝ → Mat2}
    (hfe : ∀ j : Fin 3, IntervalIntegrable (fun t ↦ l6g_vel u X Λ₁ ΛR t j) volume a b ∧
      ∀ t ∈ Icc a b, fullerCoords (phaseAt X Λ₁ ΛR t) j =
        fullerCoords (phaseAt X Λ₁ ΛR a) j + ∫ s in a..t, l6g_vel u X Λ₁ ΛR s j)
    {τ ρ S : ℝ} (hρ : 0 < ρ) (hτ : a ≤ τ) (hS0 : 0 ≤ S) (hS : τ + S * ρ ≤ b)
    {y F : ℝ → Fin 3 → ℂ}
    (hy : ∀ σ, y σ = scale ρ⁻¹ (fullerCoords (phaseAt X Λ₁ ΛR (τ + σ * ρ))))
    (hF : ∀ σ ∈ Icc 0 S, F σ = ρ • scale ρ⁻¹ (l6g_vel u X Λ₁ ΛR (τ + σ * ρ))) :
    IntervalIntegrable F volume 0 S ∧ ∀ s ∈ Icc 0 S, y s = y 0 + ∫ σ in (0 : ℝ)..s, F σ := by
  have hab : a ≤ b := hτ.trans (by nlinarith)
  have hmem : ∀ σ ∈ Icc 0 S, τ + σ * ρ ∈ Icc a b := fun σ hσ ↦
    ⟨by nlinarith [hσ.1], by nlinarith [hσ.2]⟩
  have hτm : τ ∈ Icc a b := by simpa using hmem 0 ⟨le_rfl, hS0⟩
  have hFj : ∀ σ ∈ Icc 0 S, ∀ j : Fin 3,
      F σ j = (ρ : ℂ) * ((ρ⁻¹ : ℝ) : ℂ) ^ ((j : ℕ) + 1) * l6g_vel u X Λ₁ ΛR (τ + σ * ρ) j := by
    intro σ hσ j
    rw [hF σ hσ, Pi.smul_apply, l6g_scale_apply, Complex.real_smul]
    ring
  have hint : ∀ s ∈ Icc 0 S, ∀ j : Fin 3,
      IntervalIntegrable (fun σ ↦ l6g_vel u X Λ₁ ΛR (τ + σ * ρ) j) volume 0 s := by
    intro s hs j
    exact l6g_intervalIntegrable_affine hρ
      (l6g_intervalIntegrable_mono (hfe j).1 hab hτm (hmem s hs))
  have hFint : ∀ s ∈ Icc 0 S, IntervalIntegrable F volume 0 s := by
    intro s hs
    refine l6g_intervalIntegrable_pi fun j ↦ ((hint s hs j).const_mul
      ((ρ : ℂ) * ((ρ⁻¹ : ℝ) : ℂ) ^ ((j : ℕ) + 1))).congr fun σ hσ ↦ ?_
    have hσ' : σ ∈ Icc 0 S := by
      rw [uIoc_of_le hs.1] at hσ; exact ⟨hσ.1.le, hσ.2.trans hs.2⟩
    exact (hFj σ hσ' j).symm
  refine ⟨hFint S ⟨hS0, le_rfl⟩, fun s hs ↦ ?_⟩
  funext j
  rw [Pi.add_apply, l6g_integral_apply (hFint s hs) j, hy s, hy 0]
  have hcongr : ∫ σ in (0 : ℝ)..s, F σ j =
      ∫ σ in (0 : ℝ)..s, (ρ : ℂ) * ((ρ⁻¹ : ℝ) : ℂ) ^ ((j : ℕ) + 1) *
        l6g_vel u X Λ₁ ΛR (τ + σ * ρ) j := by
    refine intervalIntegral.integral_congr fun σ hσ ↦ ?_
    rw [uIcc_of_le hs.1] at hσ
    exact hFj σ ⟨hσ.1, hσ.2.trans hs.2⟩ j
  have hZ : fullerCoords (phaseAt X Λ₁ ΛR (τ + s * ρ)) j =
      fullerCoords (phaseAt X Λ₁ ΛR τ) j + ∫ t in τ..τ + s * ρ, l6g_vel u X Λ₁ ΛR t j := by
    rw [(hfe j).2 _ (hmem s hs), (hfe j).2 _ hτm, add_assoc,
      ← intervalIntegral.integral_add_adjacent_intervals
      (l6g_intervalIntegrable_mono (hfe j).1 hab ⟨le_rfl, hab⟩ hτm)
      (l6g_intervalIntegrable_mono (hfe j).1 hab hτm (hmem s hs))]
  rw [hcongr, intervalIntegral.integral_const_mul,
    l6g_integral_affine (fun t ↦ l6g_vel u X Λ₁ ΛR t j) τ hρ.ne' s, l6g_scale_apply,
    l6g_scale_apply, zero_mul, add_zero, hZ, Complex.real_smul]
  have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  push_cast
  field_simp

section Arc

variable {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {τ : ℕ → ℝ}

private theorem l6g_rescaledArc_zero (X Λ₁ ΛR : ℝ → Mat2) (τ : ℕ → ℝ) (n : ℕ) :
    rescaledArc X Λ₁ ΛR τ n 0 = switchAng X Λ₁ ΛR τ n := by
  simp [rescaledArc, switchAng, ang, switchRadius]

private theorem l6g_switchRadius_pos (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) (n : ℕ) :
    0 < switchRadius X Λ₁ ΛR τ n :=
  weightedNorm_pos (h.switchPoints.2.2.1 n)

/-- `ρ_n → 0⁺`. -/
private theorem l6g_tendsto_switchRadius (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) :
    Tendsto (switchRadius X Λ₁ ΛR τ) atTop (𝓝[>] 0) := by
  have h1 : Tendsto (switchRadius X Λ₁ ΛR τ) atTop (𝓝 0) := by
    have := (continuous_weightedNorm.tendsto 0).comp h.switchPoints.2.2.2.1
    rwa [weightedNorm_zero] at this
  exact tendsto_nhdsWithin_iff.2 ⟨h1, Eventually.of_forall fun n ↦ l6g_switchRadius_pos h n⟩

private theorem l6g_time_mem (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) (n : ℕ) {S σ : ℝ}
    (hS : τ n + S * switchRadius X Λ₁ ΛR τ n ≤ b) (hσ : σ ∈ Icc 0 S) :
    τ n + σ * switchRadius X Λ₁ ΛR τ n ∈ Icc a b := by
  have hρ := l6g_switchRadius_pos h n
  have hτ := (h.2.2.2.2.2.1 n).1
  exact ⟨by nlinarith [hσ.1], by nlinarith [hσ.2]⟩

/-- In blow-up coordinates the rescaled arc is the lifted trajectory. -/
private theorem l6g_phase (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) (n : ℕ) {σ : ℝ}
    (hσ : τ n + σ * switchRadius X Λ₁ ΛR τ n ∈ Icc a b) :
    phaseOfFuller (scale (switchRadius X Λ₁ ΛR τ n) (rescaledArc X Λ₁ ΛR τ n σ)) =
      phaseAt X Λ₁ ΛR (τ n + σ * switchRadius X Λ₁ ΛR τ n) := by
  rw [rescaledArc, scale_scale, mul_inv_cancel₀ (l6g_switchRadius_pos h n).ne', scale_one]
  exact phaseOfFuller_fullerCoords (h.switchPoints.1 _ hσ)

/-- The integral equation of the rescaled arc, with the integrability of the rescaled field
along it. -/
private theorem l6g_arc (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) (n : ℕ) {S : ℝ}
    (hS0 : 0 ≤ S) (hS : τ n + S * switchRadius X Λ₁ ΛR τ n ≤ b) :
    IntervalIntegrable (fun σ ↦ rescaledField (switchRadius X Λ₁ ΛR τ n)
      (u (τ n + σ * switchRadius X Λ₁ ΛR τ n)) (rescaledArc X Λ₁ ΛR τ n σ)) volume 0 S ∧
    ∀ s ∈ Icc 0 S, rescaledArc X Λ₁ ΛR τ n s = rescaledArc X Λ₁ ΛR τ n 0 +
      ∫ σ in (0 : ℝ)..s, rescaledField (switchRadius X Λ₁ ΛR τ n)
        (u (τ n + σ * switchRadius X Λ₁ ΛR τ n)) (rescaledArc X Λ₁ ΛR τ n σ) :=
  l6g_arc_core (l6g_fuller_eq h.1) (l6g_switchRadius_pos h n) (h.2.2.2.2.2.1 n).1.le hS0 hS
    (fun σ ↦ rfl) fun σ hσ ↦ by rw [rescaledField, l6g_phase h n (l6g_time_mem h n hS hσ)]; rfl

/-- The controls along the rescaled arc. -/
private theorem l6g_control_mem (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) (n : ℕ) {S σ : ℝ}
    (hS : τ n + S * switchRadius X Λ₁ ΛR τ n ≤ b) (hσ : σ ∈ Icc 0 S) :
    u (τ n + σ * switchRadius X Λ₁ ΛR τ n) ∈ controlSimplex := by
  have ht := l6g_time_mem h n hS hσ
  have := h.1.1.2.2.1 (τ n + σ * switchRadius X Λ₁ ΛR τ n - a) ⟨by linarith [ht.1],
    by linarith [ht.2]⟩
  simpa only [add_sub_cancel] using this

private theorem l6g_measurable_u (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) : Measurable u := by
  have := h.1.1.2.1.comp (measurable_id.sub_const a)
  simpa only [Function.comp_def, id, add_sub_cancel] using this

private theorem l6g_measurable_rescaledControl (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ)
    (n : ℕ) : Measurable (rescaledControl u X Λ₁ ΛR τ n) := by
  have hc : Continuous simplexToUT := by unfold simplexToUT; fun_prop
  exact hc.measurable.comp ((l6g_measurable_u h).comp
    (measurable_const.add (measurable_id.mul_const _)))

/-- The maximum condition along the rescaled arc. -/
private theorem l6g_arc_max (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) (n : ℕ) {S : ℝ}
    (hS : τ n + S * switchRadius X Λ₁ ΛR τ n < b) :
    ∀ᵐ σ, σ ∈ Icc 0 S → ∀ v ∈ controlSimplex,
      phaseHam (phaseOfFuller (scale (switchRadius X Λ₁ ΛR τ n) (rescaledArc X Λ₁ ΛR τ n σ))) v ≤
        phaseHam (phaseOfFuller (scale (switchRadius X Λ₁ ΛR τ n) (rescaledArc X Λ₁ ΛR τ n σ)))
          (u (τ n + σ * switchRadius X Λ₁ ΛR τ n)) := by
  have hρ := l6g_switchRadius_pos h n
  have hτ := (h.2.2.2.2.2.1 n).1
  have hmax := h.1.2.2.2.2.2
  have h1 : ∀ᵐ t, t ∈ Ioo a b → ∀ v ∈ controlSimplex, phaseHam (phaseAt X Λ₁ ΛR t) v ≤
      phaseHam (phaseAt X Λ₁ ΛR t) (u t) := by
    have := l6g_ae_affine hmax (-a) (ρ := 1) one_ne_zero
    filter_upwards [this] with t ht htI
    have := (ht ⟨by linarith [htI.1], by linarith [htI.2]⟩).2
    simpa only [mul_one, add_neg_cancel_left, neg_add_cancel_left, phaseHam, phaseAt,
      show a + (-a + t) = t by ring] using this
  filter_upwards [l6g_ae_affine h1 (τ n) hρ.ne'] with σ hσ hσI v hv
  have ht := l6g_time_mem h n hS.le hσI
  rw [l6g_phase h n ht]
  exact hσ ⟨by nlinarith [hσI.1], by nlinarith [hσI.2]⟩ v hv

end Arc

/-- **The rescaled arc solves the rescaled Reinhardt equation**: along a chattering arc, if the
window `[τ_n, τ_n + S ρ_n]` stays before `b`, then for `s ∈ [0, S]`,
`rescaledArc n s = ξ_n + ∫₀ˢ rescaledField ρ_n (u(τ_n + σ ρ_n)) (rescaledArc n σ) dσ`, and
`rescaledArc n 0 = ξ_n`. -/
theorem rescaledArc_eq_integral {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    {τ : ℕ → ℝ} (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) (n : ℕ) {S : ℝ}
    (hS : τ n + S * switchRadius X Λ₁ ΛR τ n ≤ b) :
    rescaledArc X Λ₁ ΛR τ n 0 = switchAng X Λ₁ ΛR τ n ∧
      ∀ s ∈ Icc 0 S, rescaledArc X Λ₁ ΛR τ n s = rescaledArc X Λ₁ ΛR τ n 0 +
        ∫ σ in (0 : ℝ)..s, rescaledField (switchRadius X Λ₁ ΛR τ n)
          (u (τ n + σ * switchRadius X Λ₁ ΛR τ n)) (rescaledArc X Λ₁ ΛR τ n σ) :=
  ⟨l6g_rescaledArc_zero X Λ₁ ΛR τ n, fun s hs ↦ (l6g_arc h n (hs.1.trans hs.2) hS).2 s hs⟩

/-- **Limits of rescaled Reinhardt arcs are relaxed Fuller extremals** (the precise form of "By the
earlier asymptotic formulas … When `r = 0`, the Reinhardt switching function agrees with the Fuller
switching function", TeX 12912–12918, for whole arcs): along a chattering arc, let `n_k = φ k`
with `ξ_{n_k} → ξ`, and let `S > 0` be such that the windows `[τ_{n_k}, τ_{n_k} + S ρ_{n_k}]` stay
before `b` for large `k`. Then along a further subsequence the rescaled arcs converge uniformly on
`[0, S]` to a trajectory `y` of the Fuller system from `ξ` with a control `w` in `U_T` satisfying
the maximum condition, and the integrals of the rescaled controls converge to those of `w`. -/
theorem exists_tendsto_rescaledArc {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    {τ : ℕ → ℝ} (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {ξ : Fin 3 → ℂ} (hξ : Tendsto (fun k ↦ switchAng X Λ₁ ΛR τ (φ k)) atTop (𝓝 ξ)) {S : ℝ}
    (hS : 0 < S) (hwin : ∀ᶠ k in atTop, τ (φ k) + S * switchRadius X Λ₁ ΛR τ (φ k) < b) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ (y : ℝ → Fin 3 → ℂ) (w : ℝ → ℂ),
      IsTrajectory UT 0 S y w ∧ MaxCondition UT 0 S y w ∧ y 0 = ξ ∧
      TendstoUniformlyOn (fun k s ↦ rescaledArc X Λ₁ ΛR τ (φ (ψ k)) s) y atTop (Icc 0 S) ∧
      ∀ s ∈ Icc 0 S, Tendsto
        (fun k ↦ ∫ σ in (0 : ℝ)..s, rescaledControl u X Λ₁ ΛR τ (φ (ψ k)) σ) atTop
        (𝓝 (∫ σ in (0 : ℝ)..s, w σ)) := by
  have hρ := l6g_tendsto_switchRadius h
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  -- the thresholds: the window, and the rescaled field within `1` of the Fuller field
  have hclose : ∀ᶠ k in atTop,
      ∀ p ∈ controlSimplex ×ˢ Metric.closedBall (0 : Fin 3 → ℂ) (l6g_bd S + 1),
        dist (fullerField (simplexToUT p.1) p.2)
          (rescaledField (switchRadius X Λ₁ ΛR τ (φ k)) p.1 p.2) < 1 :=
    (hρ.comp hφt).eventually (Metric.tendstoUniformlyOn_iff.1
      (tendstoUniformlyOn_rescaledField (isCompact_closedBall _ _)) 1 one_pos)
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.1 (hwin.and hclose)
  have hK : ∀ k, τ (φ (k + K₀)) + S * switchRadius X Λ₁ ΛR τ (φ (k + K₀)) < b ∧
      ∀ p ∈ controlSimplex ×ˢ Metric.closedBall (0 : Fin 3 → ℂ) (l6g_bd S + 1),
        dist (fullerField (simplexToUT p.1) p.2)
          (rescaledField (switchRadius X Λ₁ ΛR τ (φ (k + K₀))) p.1 p.2) < 1 :=
    fun k ↦ hK₀ (k + K₀) (Nat.le_add_left K₀ k)
  have hshift : Tendsto (fun k ↦ φ (k + K₀)) atTop atTop := hφt.comp (tendsto_add_atTop_nat K₀)
  obtain ⟨ψ, hψ, y, w, htraj, hmax, hy0, hu, hint⟩ := l6g_limit hS
    (ρ := fun k ↦ switchRadius X Λ₁ ΛR τ (φ (k + K₀)))
    (Y := fun k ↦ rescaledArc X Λ₁ ΛR τ (φ (k + K₀)))
    (F := fun k σ ↦ rescaledField (switchRadius X Λ₁ ΛR τ (φ (k + K₀)))
      (u (τ (φ (k + K₀)) + σ * switchRadius X Λ₁ ΛR τ (φ (k + K₀))))
      (rescaledArc X Λ₁ ΛR τ (φ (k + K₀)) σ))
    (v := fun k σ ↦ u (τ (φ (k + K₀)) + σ * switchRadius X Λ₁ ΛR τ (φ (k + K₀))))
    (hρ.comp hshift)
    (fun k ↦ (l6g_arc h (φ (k + K₀)) hS.le (hK k).1.le).1)
    (fun k ↦ (l6g_arc h (φ (k + K₀)) hS.le (hK k).1.le).2)
    (fun k σ _ ↦ rfl)
    (fun k σ hσ ↦ l6g_control_mem h (φ (k + K₀)) (hK k).1.le hσ)
    (fun k ↦ l6g_measurable_rescaledControl h (φ (k + K₀)))
    (by simpa only [l6g_rescaledArc_zero, Function.comp_def] using
      hξ.comp (tendsto_add_atTop_nat K₀))
    (fun k ↦ by
      rw [l6g_rescaledArc_zero]
      exact l6g_norm_le_one_of_mem_Xi (h.switchPoints.2.2.2.2 _))
    (fun k ↦ l6g_arc_max h (φ (k + K₀)) (hK k).1)
    (fun k ↦ (hK k).2)
  exact ⟨fun k ↦ ψ k + K₀, hψ.add_const K₀, y, w, htraj, hmax, hy0, hu, hint⟩

end SmoothedPolygons
