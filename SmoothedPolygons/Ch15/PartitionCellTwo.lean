module

public import SmoothedPolygons.Ch15.PartExtensions
public import Basic.Analysis.Polynomial.LeastPositiveRoot

/-!
# Chapter 15: `𝒟₂, 𝒟₃` geometrically partition the second big cell (Proposition 15.3.2)

The second clause of Proposition 15.3.2 (`Proposition15_3_2`,
`SmoothedPolygons/Ch15/Involution.lean`; TeX 12424–12438): `𝒟₂` (the closure of the points of the
open second box switching to `1`) and `𝒟₃` (switching to `ζ`) are regular closed and have disjoint
interiors (`isGeometricPartition_closedBoxTwo`). The book reads this off Figure 15.3 (TeX
12392–12409); the formalization proves it by an exact deformation. The file ends with the
reduction of Proposition 15.3.2 to its remaining clauses (`proposition15_3_2_of_remaining`).

## Proof

Along `ζ²` from `cellPoint p` the control `ζ` beats `ζ²` exactly after the root `hi` of `q`, and `1`
beats `ζ²` where `gainOneSq p t > 0`. Let `U` be the open set of points of the open box where `1`
beats `ζ²` before `hi`, and `V` the open set where `1` stays strictly worse than `ζ²` on `[0, hi]`
(`isOpen_switchOneSet`, `isOpen_switchZetaSet`). Points of `U` switch to `1`, points of `V` to `ζ`
(`switchOneSet_subset`, `switchZetaSet_subset`).

**The deformation.** Move `z₁` to `z₁ - ε` (`ε` real), keep `z₂`, and restore `H_F = 0` with the
real `z₃ = -2(κ - ε y₂)` (`deformTwo`): the gain of `ζ` over `ζ²` does not change (only real parts
moved), so neither does `hi`, while the gain of `1` over `ζ²` changes by `-3ε(t²/4 - y₂)`, of the
sign of `-ε` at every `t` because `y₂ < 0` (`gain_deformTwo`). The cell coordinates of the deformed
point tend to `p` (`tendsto_cellCoords_deformTwo`; `ψ` through `arccos`), and its cell point is a
rescaling of it (`cellPoint_cellCoords_deformTwo`), which rescales time and gains
(`ham_flow_scale_sub`). Hence a point not in `U` is a limit of points of `V` (`ε > 0`), and a point
not in `V` a limit of points of `U` (`ε < 0`) (`mem_closure_switchZetaSet`,
`mem_closure_switchOneSet`). So `𝒟₂ = closure U`, `𝒟₃ = closure V`, and the interiors of the
closures of the disjoint open sets `U`, `V` are disjoint.
-/

@[expose] public section

namespace SmoothedPolygons

open Complex Set Filter Topology
open scoped Real

namespace TriFuller

/-! ### Real parts of a cell point and `κ = r₁ r₂ sin ψ` -/

/-- `κ = r₁ r₂ sin ψ`, so that `z₃ = -2κ` at `cellPoint p`. -/
noncomputable def cellKappa (p : Fin 3 → ℝ) : ℝ := (1 - p 0) * p 0 * Real.sin (p 1)

theorem cellPoint_re_eq (p : Fin 3 → ℝ) :
    (cellPoint p 0).re = (1 - p 0) * Real.cos (p 2 - p 1) ∧
      (cellPoint p 1).re = p 0 * Real.cos (p 2) ∧ (cellPoint p 2).re = -2 * cellKappa p := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [cellPoint, Matrix.cons_val_zero, Complex.re_ofReal_mul,
      Complex.exp_ofReal_mul_I_re]
  · simp only [cellPoint, Matrix.cons_val_one, Matrix.cons_val_zero, Complex.re_ofReal_mul,
      Complex.exp_ofReal_mul_I_re]
  · simp only [cellPoint, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
      Complex.ofReal_re, cellKappa]
    ring

/-- `κ = x₁ y₂ - y₁ x₂` (`sin ψ = sin(θ₂ - θ₁)`). -/
theorem cellKappa_eq (p : Fin 3 → ℝ) :
    cellKappa p = (cellPoint p 0).re * cellY₂ p - cellY₁ p * (cellPoint p 1).re := by
  obtain ⟨e0, e1, -⟩ := cellPoint_re_eq p
  rw [e0, e1]
  have h := Real.sin_sub (p 2) (p 2 - p 1)
  rw [sub_sub_cancel] at h
  unfold cellKappa cellY₁ cellY₂
  rw [h]
  ring

theorem cellPoint_two_eq (p : Fin 3 → ℝ) : cellPoint p 2 = ((-2 * cellKappa p : ℝ) : ℂ) := by
  simp only [cellPoint, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, cellKappa]
  congr 1
  ring

theorem cellKappa_pos {p : Fin 3 → ℝ} (hp : p ∈ openBoxTwo) : 0 < cellKappa p := by
  have : 0 < 1 - p 0 := by linarith [hp.1.2]
  have := Real.sin_pos_of_pos_of_lt_pi hp.2.1.1 hp.2.1.2
  unfold cellKappa
  have := hp.1.1
  positivity

/-! ### Gains under rescaling, and the gain at `t = 0` -/

/-- **Rescaling rescales the gains** (Lemma 13.2.1): `H_F(z(rt, (r w₁, r² w₂, r³ w₃), u), v) -
H_F(·, v') = r³ (H_F(z(t, w, u), v) - H_F(·, v'))`. -/
theorem ham_flow_scale_sub (w : Fin 3 → ℂ) (r t : ℝ) (u v v' : ℂ) :
    ham (flow (r * t) (scale r w) u) v - ham (flow (r * t) (scale r w) u) v' =
      r ^ 3 * (ham (flow t w u) v - ham (flow t w u) v') := by
  rw [ham_flow_sub_ham_flow, ham_flow_sub_ham_flow]
  simp only [scale, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons, ← Complex.ofReal_pow, RR_ofReal_mul_right]
  ring

theorem gainOneSq_zero (p : Fin 3 → ℝ) : gainOneSq p 0 = -3 * cellKappa p := by
  unfold gainOneSq
  rw [ham_flow_sub_ham_flow, cellPoint_two_eq]
  simp only [RR_eq_re_mul_add_im_mul, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, ζ_sq_re, ζ_sq_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem continuous_gainOneSq_uncurry :
    Continuous fun x : (Fin 3 → ℝ) × ℝ ↦ gainOneSq x.1 x.2 := by
  unfold gainOneSq
  have hw := continuous_flow_comp continuous_snd (continuous_cellPoint.comp continuous_fst)
    (ζ ^ 2)
  unfold ham RR
  fun_prop

/-! ### The two open switch sets -/

/-- The points of the open second box where `1` beats `ζ²` before `hi`. -/
def switchOneSet : Set (Fin 3 → ℝ) :=
  {p | p ∈ openBoxTwo ∧ ∃ t ∈ Ioo 0 (switchQuadHi p), 0 < gainOneSq p t}

/-- The points of the open second box where `1` stays strictly worse than `ζ²` on `[0, hi]`. -/
def switchZetaSet : Set (Fin 3 → ℝ) :=
  {p | p ∈ openBoxTwo ∧ ∀ s ∈ Icc (0 : ℝ) 1, gainOneSq p (s * switchQuadHi p) < 0}

theorem isOpen_switchOneSet : IsOpen switchOneSet := by
  rw [isOpen_iff_mem_nhds]
  rintro p ⟨hp, t, ht, hg⟩
  have h1 : ∀ᶠ q in 𝓝 p, t < switchQuadHi q :=
    continuous_switchQuadHi.continuousAt.eventually (lt_mem_nhds ht.2)
  have h2 : ∀ᶠ q in 𝓝 p, 0 < gainOneSq q t :=
    (continuous_gainOneSq_uncurry.comp (continuous_id.prodMk continuous_const)).continuousAt
      |>.eventually (lt_mem_nhds hg)
  filter_upwards [h1, h2, isOpen_openBoxTwo.mem_nhds hp] with q hq1 hq2 hq3
  exact ⟨hq3, t, ⟨ht.1, hq1⟩, hq2⟩

theorem isOpen_switchZetaSet : IsOpen switchZetaSet := by
  rw [isOpen_iff_mem_nhds]
  rintro p ⟨hp, hneg⟩
  have hc : Continuous fun x : (Fin 3 → ℝ) × ℝ ↦ -gainOneSq x.1 (x.2 * switchQuadHi x.1) :=
    (continuous_gainOneSq_uncurry.comp (continuous_fst.prodMk
      (continuous_snd.mul (continuous_switchQuadHi.comp continuous_fst)))).neg
  have h := eventually_forall_pos_of_isCompact (f := fun q s ↦ -gainOneSq q (s * switchQuadHi q))
    isCompact_Icc (fun s _ ↦ hc.continuousAt) (fun s hs ↦ neg_pos.2 (hneg s hs))
  filter_upwards [h, isOpen_openBoxTwo.mem_nhds hp] with q hq hq'
  exact ⟨hq', fun s hs ↦ neg_pos.1 (hq s hs)⟩

/-- Points of `switchOneSet` switch to `1`: a switch to `ζ` happens at `hi` with `1` never better
before (`switchSet_openBoxTwo_ζ_subset`). -/
theorem switchOneSet_subset : switchOneSet ⊆ switchSet openBoxTwo 1 := by
  rintro p ⟨hp, t, ht, hg⟩
  refine ⟨hp, (firstControl_poincare_openBoxTwo hp).resolve_right fun h ↦ ?_⟩
  have hA := switchSet_openBoxTwo_ζ_subset ⟨hp, h⟩
  have hhi : 0 < switchQuadHi p := ht.1.trans ht.2
  have := hA.2 (t / switchQuadHi p) ⟨div_nonneg ht.1.le hhi.le, (div_le_one hhi).2 ht.2.le⟩
  rw [div_mul_cancel₀ _ hhi.ne'] at this
  linarith

/-- Points of `switchZetaSet` switch to `ζ`: the switch is at `hi`
(`firstSwitchTime_of_mem_cellTwoNoA`) and there `1` is strictly worse than `ζ²`, so it is not the
new first control. -/
theorem switchZetaSet_subset : switchZetaSet ⊆ switchSet openBoxTwo ζ := by
  rintro p ⟨hp, hneg⟩
  refine ⟨hp, (firstControl_poincare_openBoxTwo hp).resolve_left fun h ↦ ?_⟩
  have hA : p ∈ cellTwoNoA := ⟨openBoxTwo_subset_closedBoxTwo hp, fun s hs ↦ (hneg s hs).le⟩
  have hz := (cellPoint_mem_sectionZero
    (mem_cellDomain_of_mem_closedBoxTwo (openBoxTwo_subset_closedBoxTwo hp))).1
  obtain ⟨hfc, hT⟩ := firstSwitchTime_of_mem_cellTwoNoA hA hp
  have hle := ham_le_of_firstControl_poincare hz (ζ ^ 2) ζ_sq_mem_VT
  rw [h, poincare, hfc, hT] at hle
  have := hneg 1 ⟨zero_le_one, le_rfl⟩
  rw [one_mul, gainOneSq] at this
  linarith

theorem disjoint_switchOneSet_switchZetaSet : Disjoint switchOneSet switchZetaSet := by
  rw [Set.disjoint_left]
  intro p h1 h2
  have e1 := (switchOneSet_subset h1).2
  have e2 := (switchZetaSet_subset h2).2
  rw [e1] at e2
  exact ζ_ne_one e2.symm

/-! ### The deformation `z₁ ↦ z₁ - ε` -/

/-- The deformed point `(z₁ - ε, z₂, -2(κ - ε y₂))` of `cellPoint p`. -/
noncomputable def deformTwo (p : Fin 3 → ℝ) (ε : ℝ) : Fin 3 → ℂ :=
  ![cellPoint p 0 - (ε : ℂ), cellPoint p 1, ((-2 * (cellKappa p - ε * cellY₂ p) : ℝ) : ℂ)]

theorem deformTwo_zero (p : Fin 3 → ℝ) : deformTwo p 0 = cellPoint p := by
  funext j
  fin_cases j
  · simp [deformTwo]
  · simp [deformTwo]
  · change ((-2 * (cellKappa p - 0 * cellY₂ p) : ℝ) : ℂ) = cellPoint p 2
    rw [cellPoint_two_eq, zero_mul, sub_zero]

/-- The deformed point lies on the section with `z₃ < 0` real while `κ - ε y₂ > 0`. -/
theorem deformTwo_mem {p : Fin 3 → ℝ} (hp : p ∈ openBoxTwo) {ε : ℝ}
    (hε : 0 < cellKappa p - ε * cellY₂ p) :
    deformTwo p ε ∈ sectionZero ∧ (deformTwo p ε 2).im = 0 ∧ (deformTwo p ε 2).re < 0 := by
  set c := cellKappa p - ε * cellY₂ p with hc
  have h2 : deformTwo p ε 2 = ((-2 * c : ℝ) : ℂ) := rfl
  have h0 : deformTwo p ε 0 = cellPoint p 0 - (ε : ℂ) := rfl
  have h1 : deformTwo p ε 1 = cellPoint p 1 := rfl
  obtain ⟨i0, i1, -⟩ := cellPoint_im_eq p
  obtain ⟨r0, r1, -⟩ := cellPoint_re_eq p
  have hk := cellKappa_eq p
  refine ⟨⟨fun h ↦ ?_, ?_, ?_⟩, by rw [h2, Complex.ofReal_im], by
    rw [h2, Complex.ofReal_re]; linarith⟩
  · have := congrArg (fun w ↦ ‖w 1‖) h
    simp only [h1, Pi.zero_apply, norm_zero, cellPoint, Matrix.cons_val_one, Matrix.cons_val_zero,
      norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at this
    rw [abs_eq_zero] at this
    exact absurd this hp.1.1.ne'
  · left; left
    exact ⟨-2 * c, by linarith, by rw [h2, pow_zero, mul_one]⟩
  · -- `H_F(w, ζ²) = 0` is the maximum
    have hham : ∀ v : ℂ, ham (deformTwo p ε) v = -c + v.re * (-2 * c) := by
      intro v
      simp only [ham, RR_eq_re_mul_add_im_mul, h0, h1, h2, Complex.sub_re, Complex.sub_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, i0, i1, r0, r1]
      rw [hc, hk, r0, r1]
      ring
    have hmax : ∀ x ∈ VT, ham (deformTwo p ε) x ≤ ham (deformTwo p ε) (ζ ^ 2) := by
      intro x hx
      rw [hham, hham]
      rcases mem_VT.1 hx with rfl | rfl | rfl
      · rw [Complex.one_re, ζ_sq_re]; linarith
      · rw [ζ_re, ζ_sq_re]
      · exact le_rfl
    rw [hamMax_eq_of_forall_le ζ_sq_mem_VT hmax, hham, ζ_sq_re]
    ring

/-- **The gains of the deformed point**: the gain of `1` over `ζ²` drops by `3ε(t²/4 - y₂)`. -/
theorem gain_deformTwo (p : Fin 3 → ℝ) (ε t : ℝ) :
    ham (flow t (deformTwo p ε) (ζ ^ 2)) 1 - ham (flow t (deformTwo p ε) (ζ ^ 2)) (ζ ^ 2) =
      gainOneSq p t - 3 * ε * (t ^ 2 / 4 - cellY₂ p) := by
  unfold gainOneSq
  rw [ham_flow_sub_ham_flow, ham_flow_sub_ham_flow, cellPoint_two_eq]
  have h0 : deformTwo p ε 0 = cellPoint p 0 - (ε : ℂ) := rfl
  have h1 : deformTwo p ε 1 = cellPoint p 1 := rfl
  have h2 : deformTwo p ε 2 = ((-2 * (cellKappa p - ε * cellY₂ p) : ℝ) : ℂ) := rfl
  rw [h0, h1, h2]
  simp only [RR_eq_re_mul_add_im_mul, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, ζ_sq_re, ζ_sq_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The gain of `ζ` over `ζ²` does not change: `Im z₃(t) = t q(t)` for the deformed point too. -/
theorem im_flow_deformTwo (p : Fin 3 → ℝ) (ε t : ℝ) :
    (flow t (deformTwo p ε) (ζ ^ 2) 2).im = (flow t (cellPoint p) (ζ ^ 2) 2).im := by
  have f : ∀ w : Fin 3 → ℂ, flow t w (ζ ^ 2) 2 =
      w 2 + w 1 * t + w 0 * t ^ 2 / 2 - I * t ^ 3 * ζ ^ 2 / 6 := fun w ↦ rfl
  rw [f, f, cellPoint_two_eq]
  have h0 : deformTwo p ε 0 = cellPoint p 0 - (ε : ℂ) := rfl
  have h1 : deformTwo p ε 1 = cellPoint p 1 := rfl
  have h2 : deformTwo p ε 2 = ((-2 * (cellKappa p - ε * cellY₂ p) : ℝ) : ℂ) := rfl
  rw [h0, h1, h2]
  simp only [← Complex.ofReal_pow, Complex.sub_im, Complex.add_im, Complex.mul_im,
    Complex.div_im, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  norm_num

/-! ### The cell coordinates of the deformed point -/

private lemma p15_kappa_eventually {p : Fin 3 → ℝ} (hp : p ∈ openBoxTwo) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < cellKappa p - ε * cellY₂ p := by
  have hc : Continuous fun ε : ℝ ↦ cellKappa p - ε * cellY₂ p := by fun_prop
  exact hc.continuousAt.eventually (lt_mem_nhds (by simpa using cellKappa_pos hp))

private lemma p15_cellPoint_one_ne {p : Fin 3 → ℝ} (hp : p ∈ openBoxTwo) : cellPoint p 1 ≠ 0 := by
  intro h
  have := congrArg norm h
  simp only [cellPoint, Matrix.cons_val_one, Matrix.cons_val_zero, norm_mul,
    Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs, norm_zero] at this
  rw [abs_eq_zero] at this
  exact hp.1.1.ne' this

/-- **The cell coordinates of the deformed point tend to `p`**: `r₂` through the norms (Lemma
15.1.1), `θ₂ = arg z₂` does not move, and `ψ ∈ (0, π)` is the `arccos` of
`cos(arg z₂ - arg z₁) = (x₁ x₂ + y₁ y₂)/(|z₁| |z₂|)`. -/
theorem tendsto_cellCoords_deformTwo {p : Fin 3 → ℝ} (hp : p ∈ openBoxTwo) :
    Tendsto (fun ε ↦ cellCoords (deformTwo p ε)) (𝓝 0) (𝓝 p) := by
  have hpc : cellCoords (cellPoint p) = p :=
    cellCoords_cellPoint ⟨hp.1, hp.2.1, ⟨hp.2.2.1, by linarith [hp.2.2.2, Real.pi_pos]⟩⟩
  have hb := p15_cellPoint_one_ne hp
  have hb' : ‖cellPoint p 1‖ ≠ 0 := norm_ne_zero_iff.2 hb
  have hz0 : cellPoint p 0 ≠ 0 := by
    intro h
    have := cellKappa_pos hp
    rw [cellKappa_eq, show (cellPoint p 0).re = 0 by rw [h]; rfl,
      show cellY₁ p = 0 by rw [← (cellPoint_im_eq p).1, h]; rfl] at this
    simp at this
  -- the components
  have hcomp : ∀ ε, cellCoords (deformTwo p ε) =
      ![(if ‖cellPoint p 1‖ = 0 then ‖cellPoint p 0 - (ε : ℂ)‖⁻¹ else
          (-‖cellPoint p 0 - (ε : ℂ)‖ + √(‖cellPoint p 0 - (ε : ℂ)‖ ^ 2 + 4 * ‖cellPoint p 1‖)) /
            (2 * ‖cellPoint p 1‖)) ^ 2 * ‖cellPoint p 1‖,
        toIcoMod Real.two_pi_pos 0 (arg (cellPoint p 1) - arg (cellPoint p 0 - (ε : ℂ))),
        arg (cellPoint p 1)] := fun ε ↦ rfl
  rw [tendsto_pi_nhds]
  intro j
  have hval : ∀ j, (cellCoords (deformTwo p 0)) j = p j := by
    intro j; rw [deformTwo_zero, hpc]
  fin_cases j
  · -- `r₂`
    change Tendsto (fun ε ↦ cellCoords (deformTwo p ε) 0) (𝓝 0) (𝓝 (p 0))
    rw [← hval 0]
    have hc : Continuous fun ε : ℝ ↦ cellCoords (deformTwo p ε) 0 := by
      simp only [hcomp, Matrix.cons_val_zero, hb', ↓reduceIte]
      fun_prop
    exact hc.continuousAt
  · -- `ψ`, through `arccos`
    change Tendsto (fun ε ↦ cellCoords (deformTwo p ε) 1) (𝓝 0) (𝓝 (p 1))
    set h : ℝ → ℝ := fun ε ↦ ((cellPoint p 1).re * (cellPoint p 0 - (ε : ℂ)).re +
      (cellPoint p 1).im * (cellPoint p 0 - (ε : ℂ)).im) /
        (‖cellPoint p 1‖ * ‖cellPoint p 0 - (ε : ℂ)‖) with hh
    have hne : ∀ᶠ ε : ℝ in 𝓝 0, cellPoint p 0 - (ε : ℂ) ≠ 0 := by
      have hc : Continuous fun ε : ℝ ↦ cellPoint p 0 - (ε : ℂ) := by fun_prop
      exact (hc.continuousAt (x := (0 : ℝ))).eventually_ne (y := 0) (by simpa using hz0)
    have heq : ∀ᶠ ε in 𝓝 (0 : ℝ), cellCoords (deformTwo p ε) 1 = Real.arccos (h ε) := by
      filter_upwards [p15_kappa_eventually hp, hne] with ε hε hne
      obtain ⟨hz, him, hre⟩ := deformTwo_mem hp hε
      obtain ⟨⟨-, hψ, -⟩, -⟩ := cellClass_cellCoords hz him hre
      rw [← Real.arccos_cos hψ.1.le hψ.2.le]
      congr 1
      rw [hcomp]
      change Real.cos (toIcoMod Real.two_pi_pos 0
        (arg (cellPoint p 1) - arg (cellPoint p 0 - (ε : ℂ)))) = h ε
      rw [← self_sub_toIcoDiv_zsmul, zsmul_eq_mul, Real.cos_sub_int_mul_two_pi, Real.cos_sub,
        Complex.cos_arg hb, Complex.cos_arg hne, Complex.sin_arg, Complex.sin_arg, hh]
      field_simp
    have hcont : ContinuousAt (fun ε ↦ Real.arccos (h ε)) 0 := by
      refine Real.continuous_arccos.continuousAt.comp ?_
      have hc : Continuous fun ε : ℝ ↦ cellPoint p 0 - (ε : ℂ) := by fun_prop
      refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
      exact mul_ne_zero hb' (norm_ne_zero_iff.2 (by simpa using hz0))
    rw [← hval 1, heq.self_of_nhds]
    exact hcont.tendsto.congr' (heq.mono fun ε hε ↦ hε.symm)
  · -- `θ₂` does not move
    change Tendsto (fun ε ↦ cellCoords (deformTwo p ε) 2) (𝓝 0) (𝓝 (p 2))
    rw [← hval 2]
    simp only [hcomp, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    exact tendsto_const_nhds

/-- **The deformed coordinates**: for `ε` near `0` the cell coordinates of the deformed point lie in
the open second box, and its cell point is a rescaling `scale r` of the deformed point. -/
theorem cellPoint_cellCoords_deformTwo {p : Fin 3 → ℝ} (hp : p ∈ openBoxTwo) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), cellCoords (deformTwo p ε) ∈ openBoxTwo ∧
      ∃ r : ℝ, 0 < r ∧ cellPoint (cellCoords (deformTwo p ε)) = scale r (deformTwo p ε) := by
  have hpc : cellCoords (cellPoint p) = p :=
    cellCoords_cellPoint ⟨hp.1, hp.2.1, ⟨hp.2.2.1, by linarith [hp.2.2.2, Real.pi_pos]⟩⟩
  filter_upwards [p15_kappa_eventually hp] with ε hε
  obtain ⟨hz, him, hre⟩ := deformTwo_mem hp hε
  obtain ⟨⟨h0, h1, -⟩, hcl⟩ := cellClass_cellCoords hz him hre
  set q := cellCoords (deformTwo p ε) with hq
  have h2 : q 2 = p 2 := by
    have e : q 2 = arg (deformTwo p ε 1) := rfl
    have e' : p 2 = arg (cellPoint p 1) := by
      conv_lhs => rw [← hpc]
      rfl
    rw [e, e']
    rfl
  have hqbox : q ∈ openBoxTwo := ⟨h0, h1, by rw [h2]; exact hp.2.2⟩
  refine ⟨hqbox, ?_⟩
  have hqs := cellPoint_mem_sectionZero
    (mem_cellDomain_of_mem_closedBoxTwo (openBoxTwo_subset_closedBoxTwo hqbox))
  obtain ⟨v, hv, r, hr, hvr⟩ := (classOf_eq_classOf_iff hz hqs).1 hcl.symm
  refine ⟨r, hr, ?_⟩
  -- `v = 1`: both third coordinates are real and negative
  have hv1 : v = 1 := by
    have e := congrArg (fun w ↦ w 2) hvr
    simp only [Pi.smul_apply, smul_eq_mul, scale, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons] at e
    have hq2 := cellPoint_two_eq q
    have hw2 : deformTwo p ε 2 = (((deformTwo p ε 2).re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [him]
    rw [hq2, hw2, ← Complex.ofReal_pow, ← Complex.ofReal_mul] at e
    have him' := congrArg Complex.im e
    simp only [Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re] at him'
    have hne : r ^ 3 * (deformTwo p ε 2).re ≠ 0 := mul_ne_zero (by positivity) hre.ne
    have hvim : v.im = 0 := by
      have : v.im * (r ^ 3 * (deformTwo p ε 2).re) = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_right hne
    rcases mem_VT.1 hv with h | h | h
    · exact h
    · rw [h, ζ_im] at hvim
      have : 0 < √3 := by positivity
      linarith
    · rw [h, ζ_sq_im] at hvim
      have : 0 < √3 := by positivity
      linarith
  rw [hvr, hv1, one_smul]

/-! ### Limits of the two switch sets -/

/-- The rescaled data at a deformed point: `y₁, y₂` scale like `z₁, z₂`, so `hi` scales by `r`. -/
private lemma p15_hi_scale {p q : Fin 3 → ℝ} {ε r : ℝ} (hr : 0 < r)
    (h : cellPoint q = scale r (deformTwo p ε)) :
    switchQuadHi q = r * switchQuadHi p := by
  have e1 : cellY₁ q = r * cellY₁ p := by
    rw [← (cellPoint_im_eq q).1, ← (cellPoint_im_eq p).1, h]
    simp only [scale, deformTwo, Matrix.cons_val_zero, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_im]
    ring
  have e2 : cellY₂ q = r ^ 2 * cellY₂ p := by
    rw [← (cellPoint_im_eq q).2.1, ← (cellPoint_im_eq p).2.1, h]
    simp only [scale, deformTwo, Matrix.cons_val_one, Matrix.cons_val_zero, ← Complex.ofReal_pow,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  unfold switchQuadHi switchQuadDiscr
  rw [e1, e2, show 9 * (r * cellY₁ p) ^ 2 - 12 * (r ^ 2 * cellY₂ p) =
    r ^ 2 * (9 * cellY₁ p ^ 2 - 12 * cellY₂ p) by ring, Real.sqrt_mul (by positivity),
    Real.sqrt_sq hr.le]
  ring

/-- The gain at a deformed point, rescaled. -/
private lemma p15_gain_scale {p q : Fin 3 → ℝ} {ε r : ℝ}
    (h : cellPoint q = scale r (deformTwo p ε)) (t : ℝ) :
    gainOneSq q (r * t) = r ^ 3 * (gainOneSq p t - 3 * ε * (t ^ 2 / 4 - cellY₂ p)) := by
  rw [gainOneSq, h, ham_flow_scale_sub, gain_deformTwo]

/-- **A point of the open second box where `1` never beats `ζ²` before `hi` is a limit of points of
`switchZetaSet`** (deform with `ε > 0`). -/
theorem mem_closure_switchZetaSet {p : Fin 3 → ℝ} (hp : p ∈ openBoxTwo)
    (h : ∀ t ∈ Icc 0 (switchQuadHi p), gainOneSq p t ≤ 0) : p ∈ closure switchZetaSet := by
  have hy := cellY₂_neg_of_mem_openBoxTwo hp
  refine mem_closure_of_tendsto ((tendsto_cellCoords_deformTwo hp).mono_left
    (nhdsWithin_le_nhds (s := Ioi 0))) ?_
  filter_upwards [nhdsWithin_le_nhds (cellPoint_cellCoords_deformTwo hp),
    self_mem_nhdsWithin] with ε ⟨hq, r, hr, hcp⟩ (hε : 0 < ε)
  refine ⟨hq, fun s hs ↦ ?_⟩
  have hhi0 := (switchQuad_roots_of_mem_closedBoxTwo (openBoxTwo_subset_closedBoxTwo hp)).2.2
  rw [p15_hi_scale hr hcp, show s * (r * switchQuadHi p) = r * (s * switchQuadHi p) by ring,
    p15_gain_scale hcp]
  have hg := h (s * switchQuadHi p) ⟨mul_nonneg hs.1 hhi0, by nlinarith [hs.2]⟩
  have : 0 < 3 * ε * ((s * switchQuadHi p) ^ 2 / 4 - cellY₂ p) := by
    have : 0 < (s * switchQuadHi p) ^ 2 / 4 - cellY₂ p := by
      nlinarith [sq_nonneg (s * switchQuadHi p)]
    positivity
  have : 0 < r ^ 3 := by positivity
  nlinarith

/-- **A point of the open second box where `1` ties with or beats `ζ²` somewhere in `(0, hi]` is a
limit of points of `switchOneSet`** (deform with `ε < 0`). -/
theorem mem_closure_switchOneSet {p : Fin 3 → ℝ} (hp : p ∈ openBoxTwo) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioc 0 (switchQuadHi p)) (hg : 0 ≤ gainOneSq p t₀) :
    p ∈ closure switchOneSet := by
  have hy := cellY₂_neg_of_mem_openBoxTwo hp
  refine mem_closure_of_tendsto ((tendsto_cellCoords_deformTwo hp).mono_left
    (nhdsWithin_le_nhds (s := Iio 0))) ?_
  filter_upwards [nhdsWithin_le_nhds (cellPoint_cellCoords_deformTwo hp),
    self_mem_nhdsWithin] with ε ⟨hq, r, hr, hcp⟩ (hε : ε < 0)
  -- a time `t ∈ (0, t₀)` with `gain(t) > 3ε(-y₂)`, by continuity at `t₀`
  have hδ : 0 < 3 * (-ε) * (-cellY₂ p) := by
    have : 0 < -ε := by linarith
    have : 0 < -cellY₂ p := by linarith
    positivity
  have hc : ContinuousAt (fun t ↦ gainOneSq p t) t₀ :=
    (continuous_gainOneSq_uncurry.comp (continuous_const.prodMk continuous_id)).continuousAt
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.1
    (hc.eventually (lt_mem_nhds (show gainOneSq p t₀ - 3 * (-ε) * (-cellY₂ p) <
      gainOneSq p t₀ by linarith)))
  set t := t₀ - min η t₀ / 2 with htdef
  have hm1 := min_le_left η t₀
  have hm2 := min_le_right η t₀
  have hm0 : 0 < min η t₀ := lt_min hη ht₀.1
  have ht0 : 0 < t := by simp only [htdef]; linarith
  have htt : t < t₀ := by simp only [htdef]; linarith
  have hgt : gainOneSq p t₀ - 3 * (-ε) * (-cellY₂ p) < gainOneSq p t := hball (by
    rw [Real.dist_eq, abs_lt]; constructor <;> simp only [htdef] <;> linarith)
  refine ⟨hq, r * t, ⟨by positivity, ?_⟩, ?_⟩
  · rw [p15_hi_scale hr hcp]
    exact mul_lt_mul_of_pos_left (htt.trans_le ht₀.2) hr
  · rw [p15_gain_scale hcp]
    have : 0 < gainOneSq p t - 3 * ε * (t ^ 2 / 4 - cellY₂ p) := by
      have : 0 ≤ -3 * ε * (t ^ 2 / 4) := by
        have h1 : 0 ≤ -ε := by linarith
        have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) h1)
          (by positivity : (0 : ℝ) ≤ t ^ 2 / 4)
        linarith
      nlinarith
    exact mul_pos (by positivity) this

/-! ### The partition of the second big cell -/

/-- Every point of the open second box outside `switchOneSet` is a limit of `switchZetaSet`. -/
theorem mem_closure_switchZetaSet_of_not {p : Fin 3 → ℝ} (hp : p ∈ openBoxTwo)
    (h : p ∉ switchOneSet) : p ∈ closure switchZetaSet := by
  refine mem_closure_switchZetaSet hp fun t ht ↦ ?_
  have hle : ∀ t ∈ Ioo 0 (switchQuadHi p), gainOneSq p t ≤ 0 := by
    intro t ht
    by_contra hlt
    exact h ⟨hp, t, ht, not_le.1 hlt⟩
  rcases ht.1.eq_or_lt with rfl | ht0
  · rw [gainOneSq_zero]; linarith [cellKappa_pos hp]
  rcases ht.2.lt_or_eq with htlt | rfl
  · exact hle t ⟨ht0, htlt⟩
  · -- the endpoint, by continuity
    have hc : ContinuousAt (fun t ↦ gainOneSq p t) (switchQuadHi p) :=
      (continuous_gainOneSq_uncurry.comp (continuous_const.prodMk continuous_id)).continuousAt
    exact le_of_tendsto (hc.tendsto.mono_left nhdsWithin_le_nhds)
      (Filter.mem_of_superset (Ioo_mem_nhdsLT ht0) hle)

/-- Every point of the open second box outside `switchZetaSet` is a limit of `switchOneSet`. -/
theorem mem_closure_switchOneSet_of_not {p : Fin 3 → ℝ} (hp : p ∈ openBoxTwo)
    (h : p ∉ switchZetaSet) : p ∈ closure switchOneSet := by
  have : ∃ s ∈ Icc (0 : ℝ) 1, 0 ≤ gainOneSq p (s * switchQuadHi p) := by
    by_contra hc
    push Not at hc
    exact h ⟨hp, hc⟩
  obtain ⟨s, hs, hg⟩ := this
  have hhi0 := (switchQuad_roots_of_mem_closedBoxTwo (openBoxTwo_subset_closedBoxTwo hp)).2.2
  have hpos : 0 < s * switchQuadHi p := by
    rcases (mul_nonneg hs.1 hhi0).lt_or_eq with h' | h'
    · exact h'
    · rw [← h', gainOneSq_zero] at hg
      linarith [cellKappa_pos hp]
  exact mem_closure_switchOneSet hp ⟨hpos, by nlinarith [hs.2]⟩ hg

theorem partD2_eq_closure : partD2 = closure switchOneSet := by
  apply Subset.antisymm
  · refine closure_minimal (fun p hp ↦ ?_) isClosed_closure
    by_cases h : p ∈ switchOneSet
    · exact subset_closure h
    · refine mem_closure_switchOneSet_of_not hp.1 fun h' ↦ ?_
      have e1 := hp.2
      have e2 := (switchZetaSet_subset h').2
      rw [e1] at e2
      exact ζ_ne_one e2.symm
  · exact closure_mono switchOneSet_subset

theorem partD3_eq_closure : partD3 = closure switchZetaSet := by
  apply Subset.antisymm
  · refine closure_minimal (fun p hp ↦ ?_) isClosed_closure
    by_cases h : p ∈ switchZetaSet
    · exact subset_closure h
    · refine mem_closure_switchZetaSet_of_not hp.1 fun h' ↦ ?_
      have e1 := hp.2
      have e2 := (switchOneSet_subset h').2
      rw [e1] at e2
      exact ζ_ne_one e2
  · exact closure_mono switchZetaSet_subset

/-- **`𝒟₂` is regular closed**: it is the closure of the open set `switchOneSet`. -/
theorem closure_interior_partD2 : closure (interior partD2) = partD2 := by
  rw [partD2_eq_closure]
  apply Subset.antisymm
  · exact closure_minimal interior_subset isClosed_closure
  · exact closure_mono (isOpen_switchOneSet.subset_interior_iff.2 subset_closure)

/-- **`𝒟₃` is regular closed**: it is the closure of the open set `switchZetaSet`. -/
theorem closure_interior_partD3 : closure (interior partD3) = partD3 := by
  rw [partD3_eq_closure]
  apply Subset.antisymm
  · exact closure_minimal interior_subset isClosed_closure
  · exact closure_mono (isOpen_switchZetaSet.subset_interior_iff.2 subset_closure)

/-- **The interiors of `𝒟₂` and `𝒟₃` are disjoint**: the closures of two disjoint open sets have
disjoint interiors. -/
theorem disjoint_interior_partD2_partD3 : Disjoint (interior partD2) (interior partD3) := by
  rw [partD2_eq_closure, partD3_eq_closure, Set.disjoint_iff_inter_eq_empty, ← interior_inter,
    Set.eq_empty_iff_forall_notMem]
  intro p hp
  set N := interior (closure switchOneSet ∩ closure switchZetaSet)
  have hNo : IsOpen N := isOpen_interior
  obtain ⟨q, hqN, hqU⟩ := mem_closure_iff.1 (interior_subset hp).1 N hNo hp
  obtain ⟨y, hyW, hyV⟩ := mem_closure_iff.1 (interior_subset hqN).2 _
    (hNo.inter isOpen_switchOneSet) ⟨hqN, hqU⟩
  exact Set.disjoint_left.1 disjoint_switchOneSet_switchZetaSet hyW.2 hyV

/-- **`𝒟₂, 𝒟₃` geometrically partition the closed second big cell** (the second clause of
Proposition 15.3.2). Departure from the paper: the book reads this off Figure 15.3 (TeX
12392–12409); the formalization proves it by the exact deformation of the module docstring. -/
theorem isGeometricPartition_closedBoxTwo :
    IsGeometricPartition closedBoxTwo [partD2, partD3] := by
  refine ⟨?_, ?_, ?_⟩
  · intro D hD
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hD
    rcases hD with rfl | rfl
    · exact closure_interior_partD2
    · exact closure_interior_partD3
  · intro x
    simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
    rw [← partD2_union_partD3]
    rfl
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨disjoint_interior_partD2_partD3, fun _ h ↦ h.elim⟩

/-! ### What remains of Proposition 15.3.2 -/

/-- **Proposition 15.3.2 from its remaining clauses.** Given the regularity of `𝒟₄`, the
disjointness of the interiors of `𝒟₁` and `𝒟₄`, continuous extensions on `𝒟₀, 𝒟₁, 𝒟₂`, and the
action of the involution for any choice of extensions, `Proposition15_3_2` holds. The other
clauses are proved: `closure_interior_partD0`, `closure_interior_partD1`,
`closedBoxOne_subset_partD`, `disjoint_interior_partD0_partD1`, `disjoint_interior_partD0_partD4`
(`SmoothedPolygons/Ch15/PartitionTopology.lean`), `isGeometricPartition_closedBoxTwo`, and the
extensions `extD3`, `extD4` (`SmoothedPolygons/Ch15/PartExtensions.lean`). -/
theorem proposition15_3_2_of_remaining
    (hD4 : closure (interior partD4) = partD4)
    (h14 : Disjoint (interior partD1) (interior partD4))
    (hext : ∀ i : Fin 5, i ≤ 2 → ∃ g : (Fin 3 → ℝ) → XiW0Quot, ContinuousOn g (partD i) ∧
      ∀ p ∈ interior (partD i), g p = poincareAngZero (cellClass p))
    (himg : ∀ G : Fin 5 → (Fin 3 → ℝ) → XiW0Quot, (∀ i, ContinuousOn (G i) (partD i) ∧
        ∀ p ∈ interior (partD i), G i p = poincareAngZero (cellClass p)) →
      (fun p ↦ tauZero (G 3 p)) '' partD 3 = cellClass '' partD 4 ∧
      (fun p ↦ tauZero (G 4 p)) '' partD 4 = cellClass '' partD 3 ∧
      ∀ i : Fin 5, i ≤ 2 → (fun p ↦ tauZero (G i p)) '' partD i = cellClass '' partD i) :
    Proposition15_3_2 := by
  obtain ⟨g0, hg0, hg0'⟩ := hext 0 (by decide)
  obtain ⟨g1, hg1, hg1'⟩ := hext 1 (by decide)
  obtain ⟨g2, hg2, hg2'⟩ := hext 2 (by decide)
  have hG : ∀ i, ContinuousOn (![g0, g1, g2, extD3, extD4] i) (partD i) ∧
      ∀ p ∈ interior (partD i),
        (![g0, g1, g2, extD3, extD4] i) p = poincareAngZero (cellClass p) := by
    intro i
    fin_cases i
    · exact ⟨hg0, hg0'⟩
    · exact ⟨hg1, hg1'⟩
    · exact ⟨hg2, hg2'⟩
    · exact ⟨continuousOn_extD3, fun p hp ↦
        extD3_eq (interior_subset hp) (interior_subset_openBoxTwo partD3_subset hp)⟩
    · exact ⟨continuousOn_extD4, fun p hp ↦ extD4_eq hp⟩
  refine ⟨⟨?_, ?_, ?_⟩, isGeometricPartition_closedBoxTwo, ⟨_, hG, himg _ hG⟩⟩
  · intro D hD
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hD
    rcases hD with rfl | rfl | rfl
    · exact closure_interior_partD0
    · exact closure_interior_partD1
    · exact hD4
  · intro x
    simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
    constructor
    · exact closedBoxOne_subset_partD
    · rintro (h | h | h)
      · exact partD0_subset h
      · exact partD1_subset h
      · exact partD4_subset h
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨⟨disjoint_interior_partD0_partD1, disjoint_interior_partD0_partD4⟩, h14,
      fun _ h ↦ h.elim⟩

end TriFuller

end SmoothedPolygons
