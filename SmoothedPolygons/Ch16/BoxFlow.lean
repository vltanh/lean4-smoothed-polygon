module

public import SmoothedPolygons.Ch16.DOutInvariant
public import SmoothedPolygons.Ch15.SmallerCells
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The Fuller–Poincaré map on the boxes `𝒟_{ij}`: the exact structure

Exact (non-numerical) facts about the Fuller–Poincaré map `poincareAngZero` at a point
`p = (r₂, ψ, θ₂)` of the closed first big cell where the first control is `ζ`, used by the analytic
proof of `BoxSubclaims` (`SmoothedPolygons/Ch16/BasinHypotheses.lean`) in
`SmoothedPolygons/Ch16/BoxSubclaims.lean`. They extend those of
`SmoothedPolygons/Ch16/DOutFlow.lean` (the box `𝒟₀₀`) to the other boxes, where two new things
happen: the switching function of `ζ → ζ²`, `Y = Im z₃(t)`, can become negative (the trajectory
then switches to `ζ²` and the image lies in the second big cell), and the image can have `z₃ = 0`
(at a tie of the two switches, the surface `∂_res`).

* **The switch to `1`** (`an2_root`): the switching function `D = V₂ = -√3 κ + y₂ t + y₁ t²/2 +
  t³/12` of `ζ → 1` (in the coordinates `x_j + i y_j = ζ z_j` of `DOutFlow.lean`) has a unique
  positive root `τ`, with `D < 0` before it and `D > 0` after it, when either `y₂ ≤ 0 ≤ κ` (then
  `D/t²` is increasing, `V₂_mul_sq_lt`) or `y₁, y₂ ≥ 0 < κ` (then `D` is increasing).
* **The first switch** (`an2_firstControl_of`): the control `ζ` is beaten by `1` when `D > 0` and
  by `ζ²` when `Y < 0`; the first control is `ζ` and the first switch is at `T` when neither
  happens on `(0, T]` and one of them happens at times arbitrarily close to `T` from the right.
* **The dichotomy** (`an2_dichotomy`): either `Y < 0` somewhere on `(0, τ]`, and then the first
  switch is at the least root `T_B < τ` of `Y/t` (a convex quadratic), where `Im z₂ < 0`: the
  trajectory switches to `ζ²` on the wall `𝒲₀` and the image lies in the second big cell
  (`mem_cellTwoSet_iff`); or `Y ≥ 0` on `(0, τ]`, the first switch is at `τ`, and the rotated
  image `w = ζ F(z)` has `w₁ = U₀ + i V₀`, `w₂ = U₁ + i V₁` and `w₃ = U₂ ≤ 0` real.
* **The cell coordinates of the image** (`an2_cellCoords_spec`): for a point `w` of the section
  with `w₃ ∈ ℝ_{≤0}` (the tie `w₃ = 0` included) and `w₁, w₂ ≠ 0`, the class of `w` is the class
  of `cellCoords w`, with `r₂ ∈ (0, 1)`, `ψ ∈ [0, π]` (the vanishing of the Hamiltonian,
  (15.1.1)) and `θ₂ = arg w₂`.
* **The faces where the first control is not `ζ`** (`an2_mem_boxSet_zero_zero_of_r_zero`,
  `an2_mem_boxSet_zero_zero_of_rot`): the edge `r₂ = 0` and the faces `ψ = 0`, `r₂ = 1` with
  `θ₂ ∈ [0, π/3]` are, as classes, in the box `𝒟₀₀` (the `V_T`-equivariance).
-/

@[expose] public section

namespace SmoothedPolygons.TriFuller.BoxAnalytic

open Set DOutAnalytic
open Complex (I)

/-! ### The switching function of `ζ → ζ²` -/

/-- `Y = Im z₃(t) = r₂ sin θ₂ t + r₁ sin θ₁ t²/2 + t³/12` along the control `ζ`; `ζ²` beats `ζ`
exactly when `Y < 0` (`ham_ζ_sq_sub_ham_ζ`). -/
noncomputable def an2_Y (p : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  p 0 * Real.sin (p 2) * t + (1 - p 0) * Real.sin (p 2 - p 1) * t ^ 2 / 2 + t ^ 3 / 12

/-- `Y/t = r₂ sin θ₂ + r₁ sin θ₁ t/2 + t²/12`, a convex quadratic. -/
noncomputable def an2_Q (p : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  p 0 * Real.sin (p 2) + (1 - p 0) * Real.sin (p 2 - p 1) * t / 2 + t ^ 2 / 12

theorem an2_Y_eq (p : Fin 3 → ℝ) (t : ℝ) : an2_Y p t = t * an2_Q p t := by
  unfold an2_Y an2_Q; ring

theorem an2_flow_two_im (p : Fin 3 → ℝ) (t : ℝ) :
    (flow t (cellPoint p) ζ 2).im = an2_Y p t := flow_two_im p t

/-- `Im z₂(t) = r₂ sin θ₂ + r₁ sin θ₁ t + t²/4 = Y'(t)`. -/
theorem an2_flow_one_im (p : Fin 3 → ℝ) (t : ℝ) :
    (flow t (cellPoint p) ζ 1).im =
      p 0 * Real.sin (p 2) + (1 - p 0) * Real.sin (p 2 - p 1) * t + t ^ 2 / 4 := by
  obtain ⟨c0, c1, c2, c3, -, -⟩ := cellPoint_reim p
  have f1 : flow t (cellPoint p) ζ 1 = cellPoint p 1 + cellPoint p 0 * t - I * t ^ 2 * ζ / 2 :=
    rfl
  rw [f1]
  simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.mul_im, Complex.sub_im, Complex.add_im,
    Complex.div_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, ζ_re, ζ_im,
    c0, c1, c3]
  norm_num
  ring

/-- `Y = -(√3/2) U₂ - V₂/2`. -/
theorem an2_Y_eq_U₂ (p : Fin 3 → ℝ) (t : ℝ) : an2_Y p t = -(√3 / 2) * U₂ p t - V₂ p t / 2 := by
  rw [← an2_flow_two_im]; exact flow_two_im_eq t

theorem an2_continuous_Q (p : Fin 3 → ℝ) : Continuous (an2_Q p) := by
  unfold an2_Q; fun_prop

theorem an2_continuous_V₂ (p : Fin 3 → ℝ) : Continuous (V₂ p) := by
  unfold V₂; fun_prop

/-! ### The switch to `1` -/

/-- `|y₁| ≤ r₁`, `|y₂| ≤ r₂` and `κ ≤ 1/4` for `r₂ ∈ [0, 1]`. -/
theorem an2_coeff_bounds {p : Fin 3 → ℝ} (h0 : 0 ≤ p 0) (h0' : p 0 ≤ 1) :
    -(1 - p 0) ≤ cy₁ p ∧ cy₁ p ≤ 1 - p 0 ∧ -p 0 ≤ cy₂ p ∧ cκ p ≤ 1 / 4 := by
  have hr1 : 0 ≤ 1 - p 0 := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold cy₁; nlinarith [Real.neg_one_le_sin (p 2 - p 1 + 2 / 3 * Real.pi)]
  · unfold cy₁; nlinarith [Real.sin_le_one (p 2 - p 1 + 2 / 3 * Real.pi)]
  · unfold cy₂; nlinarith [Real.neg_one_le_sin (p 2 + 2 / 3 * Real.pi)]
  · unfold cκ
    have := Real.sin_le_one (p 1)
    have := Real.neg_one_le_sin (p 1)
    have : 0 ≤ (1 - p 0) * p 0 := mul_nonneg hr1 h0
    nlinarith [sq_nonneg (p 0 - 1 / 2)]

/-- `D(7) > 0` for `r₂ ∈ [0, 1]` (`|y_j| ≤ r_j`, `κ ≤ 1/4`). -/
theorem an2_V₂_seven_pos {p : Fin 3 → ℝ} (h0 : 0 ≤ p 0) (h0' : p 0 ≤ 1) : 0 < V₂ p 7 := by
  obtain ⟨a1, -, a2, a3⟩ := an2_coeff_bounds h0 h0'
  have h3 : √3 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h3' : 0 ≤ √3 := Real.sqrt_nonneg 3
  unfold V₂
  nlinarith [mul_le_mul_of_nonneg_left a3 h3']

/-- `D < 0` at some `t > 0` when `y₂ < 0 ≤ κ` (`r₂ ∈ [0, 1]`). -/
theorem an2_exists_V₂_neg_of_cy₂ {p : Fin 3 → ℝ} (h0 : 0 ≤ p 0) (h0' : p 0 ≤ 1)
    (hy : cy₂ p < 0) (hk : 0 ≤ cκ p) : ∃ s, 0 < s ∧ V₂ p s < 0 := by
  obtain ⟨a1, a1', -, -⟩ := an2_coeff_bounds h0 h0'
  have h3 : 0 ≤ √3 := Real.sqrt_nonneg 3
  refine ⟨min 1 (-cy₂ p), lt_min one_pos (by linarith), ?_⟩
  set s := min 1 (-cy₂ p)
  have hs1 : s ≤ 1 := min_le_left _ _
  have hs2 : s ≤ -cy₂ p := min_le_right _ _
  have hs0 : 0 < s := lt_min one_pos (by linarith)
  have e1 : cy₁ p * s ^ 2 / 2 ≤ s ^ 2 / 2 := by nlinarith [sq_nonneg s]
  have e2 : s ^ 3 / 12 ≤ s ^ 2 / 12 := by nlinarith [sq_nonneg s]
  have e3 : 0 ≤ √3 * cκ p := mul_nonneg h3 hk
  have e4 : s ^ 2 * (7 / 12) + cy₂ p * s ≤ s * (5 / 12 * cy₂ p) := by nlinarith
  unfold V₂
  nlinarith

/-- `D < 0` at some `t > 0` when `κ > 0` (`D(0) = -√3 κ`). -/
theorem an2_exists_V₂_neg_of_cκ {p : Fin 3 → ℝ} (hk : 0 < cκ p) : ∃ s, 0 < s ∧ V₂ p s < 0 := by
  have hc := (an2_continuous_V₂ p).continuousAt (x := 0)
  have h00 : V₂ p 0 < 0 := by
    have e : V₂ p 0 = -(√3 * cκ p) := by unfold V₂; ring
    rw [e]
    have : 0 < √3 * cκ p := mul_pos (Real.sqrt_pos.2 (by norm_num)) hk
    linarith
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hc.eventually (gt_mem_nhds h00))
  refine ⟨ε / 2, by linarith, hball ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]
  linarith

/-- `D` is strictly increasing on `[0, ∞)` when `y₁, y₂ ≥ 0`. -/
theorem an2_V₂_lt_of_mono {p : Fin 3 → ℝ} (hy2 : 0 ≤ cy₂ p) (hy1 : 0 ≤ cy₁ p) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s < t) : V₂ p s < V₂ p t := by
  have e : V₂ p t - V₂ p s =
      (t - s) * (cy₂ p + cy₁ p * (t + s) / 2 + (t ^ 2 + t * s + s ^ 2) / 12) := by
    unfold V₂; ring
  have ht : 0 < t := lt_of_le_of_lt hs hst
  have : 0 < (t - s) * (cy₂ p + cy₁ p * (t + s) / 2 + (t ^ 2 + t * s + s ^ 2) / 12) := by
    apply mul_pos (by linarith)
    have : 0 ≤ cy₁ p * (t + s) / 2 := by positivity
    have : 0 < t ^ 2 := by positivity
    nlinarith
  linarith

/-- **The switching time to `1`**: under either sign condition, `D` has a positive root `τ`, with
`D < 0` on `(0, τ)` and `D > 0` after it, and `V₁ = D' > 0` at `τ`. -/
theorem an2_root {p : Fin 3 → ℝ} (h0 : 0 ≤ p 0) (h0' : p 0 ≤ 1)
    (h : (cy₂ p ≤ 0 ∧ 0 ≤ cκ p ∧ (0 < cκ p ∨ cy₂ p < 0)) ∨
      (0 ≤ cy₂ p ∧ 0 ≤ cy₁ p ∧ 0 < cκ p)) :
    ∃ τ, 0 < τ ∧ V₂ p τ = 0 ∧ (∀ t, 0 < t → t < τ → V₂ p t < 0) ∧
      (∀ t, τ < t → 0 < V₂ p t) ∧ 0 < V₁ p τ := by
  have h7 := an2_V₂_seven_pos h0 h0'
  have hcont : ContinuousOn (V₂ p) (Icc 0 7) := (an2_continuous_V₂ p).continuousOn
  rcases h with ⟨hy, hk, hk'⟩ | ⟨hy2, hy1, hk⟩
  · obtain ⟨s, hs, hVs⟩ : ∃ s, 0 < s ∧ V₂ p s < 0 := by
      rcases hk' with hk' | hk'
      · exact an2_exists_V₂_neg_of_cκ hk'
      · exact an2_exists_V₂_neg_of_cy₂ h0 h0' hk' hk
    have hs7 : s < 7 := by
      by_contra hc
      push Not at hc
      rcases hc.lt_or_eq with h | h
      · linarith [V₂_pos_of_nonneg hy hk (by norm_num) h h7.le]
      · rw [← h] at hVs; linarith
    obtain ⟨τ, hτ, hτ0⟩ := intermediate_value_Ioo hs7.le
      ((an2_continuous_V₂ p).continuousOn) ⟨hVs, h7⟩
    have hτ0' : 0 < τ := hs.trans hτ.1
    exact ⟨τ, hτ0', hτ0, fun t ht htτ ↦ V₂_neg_of_nonpos hy hk ht htτ hτ0.le,
      fun t htτ ↦ V₂_pos_of_nonneg hy hk hτ0' htτ hτ0.ge, V₁_pos_of_root hy hk hτ0' hτ0⟩
  · have h00 : V₂ p 0 < 0 := by
      have e : V₂ p 0 = -(√3 * cκ p) := by unfold V₂; ring
      rw [e]
      have : 0 < √3 * cκ p := mul_pos (Real.sqrt_pos.2 (by norm_num)) hk
      linarith
    obtain ⟨τ, hτ, hτ0⟩ := intermediate_value_Ioo (by norm_num : (0 : ℝ) ≤ 7) hcont ⟨h00, h7⟩
    refine ⟨τ, hτ.1, hτ0, fun t ht htτ ↦ ?_, fun t htτ ↦ ?_, ?_⟩
    · have := an2_V₂_lt_of_mono hy2 hy1 ht.le htτ; linarith
    · have := an2_V₂_lt_of_mono hy2 hy1 hτ.1.le htτ; linarith
    · unfold V₁
      have := hτ.1
      have : 0 ≤ cy₁ p * τ := by positivity
      nlinarith

/-! ### The first switch -/

/-- `ζ` is beaten at `t` exactly when `D(t) > 0` (by `1`) or `Y(t) < 0` (by `ζ²`). -/
theorem an2_beaten_iff (p : Fin 3 → ℝ) (t : ℝ) :
    (∃ v ∈ VT, ham (flow t (cellPoint p) ζ) ζ < ham (flow t (cellPoint p) ζ) v) ↔
      0 < V₂ p t ∨ an2_Y p t < 0 := by
  have hs3 : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  have e1 := ham_one_sub_ham_ζ p t
  have e2 := ham_ζ_sq_sub_ham_ζ p t
  rw [an2_flow_two_im] at e2
  constructor
  · rintro ⟨v, hv, hlt⟩
    rcases mem_VT.1 hv with rfl | rfl | rfl
    · left
      by_contra hc
      push Not at hc
      nlinarith
    · exact absurd hlt (lt_irrefl _)
    · right
      by_contra hc
      push Not at hc
      nlinarith
  · rintro (h | h)
    · exact ⟨1, one_mem_VT, by nlinarith [mul_pos hs3 h]⟩
    · exact ⟨ζ ^ 2, ζ_sq_mem_VT, by nlinarith [mul_pos hs3 (neg_pos.2 h)]⟩

/-- **The first control and the first switch**: if `D ≤ 0 ≤ Y` on `[0, T]` and `ζ` is beaten at
times arbitrarily close to `T` from the right, then the first control is `ζ` and the first
switching time is `T`. -/
theorem an2_firstControl_of {p : Fin 3 → ℝ} (hz : cellPoint p ≠ 0) {T : ℝ} (hT : 0 < T)
    (hok : ∀ t ∈ Icc 0 T, V₂ p t ≤ 0 ∧ 0 ≤ an2_Y p t)
    (hbeat : ∀ ε, 0 < ε → ∃ t ∈ Ioo T (T + ε), 0 < V₂ p t ∨ an2_Y p t < 0) :
    firstControl (cellPoint p) = ζ ∧ firstSwitchTime (cellPoint p) = T := by
  have hs3 : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  have hfc : firstControl (cellPoint p) = ζ := by
    refine (firstControl_eq_iff hz).2 ⟨ζ_mem_VT, T, hT, fun t ht v hv ↦ ?_⟩
    obtain ⟨hD, hY⟩ := hok t ht
    have e1 := ham_one_sub_ham_ζ p t
    have e2 := ham_ζ_sq_sub_ham_ζ p t
    rw [an2_flow_two_im] at e2
    rcases mem_VT.1 hv with rfl | rfl | rfl
    · nlinarith
    · exact le_rfl
    · nlinarith
  refine ⟨hfc, ?_⟩
  unfold firstSwitchTime
  rw [hfc]
  apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
  · obtain ⟨t, ht, hb⟩ := hbeat 1 one_pos
    exact ⟨t, lt_trans hT ht.1, (an2_beaten_iff p t).2 hb⟩
  · rintro a ⟨ha, hbeat'⟩
    have hb := (an2_beaten_iff p a).1 hbeat'
    by_contra hlt
    push Not at hlt
    obtain ⟨hD, hY⟩ := hok a ⟨ha.le, hlt.le⟩
    rcases hb with hb | hb <;> linarith
  · intro w hw
    obtain ⟨t, ht, hb⟩ := hbeat (w - T) (by linarith)
    exact ⟨t, ⟨lt_trans hT ht.1, (an2_beaten_iff p t).2 hb⟩, by linarith [ht.2]⟩

/-! ### The image at the first switch -/

/-- **The switch to `ζ²`**: if `Y < 0` at some `t₁ ∈ (0, τ]` (before the switch to `1`) and
`r₂ sin θ₂ > 0`, the first switch is at the least root `T_B` of `Y/t` (a convex quadratic, positive
at `0`), where `Im z₂ = T_B (Y/t)'(T_B) < 0`; the image lies on `𝒲₀` with `x₃ < 0` and first
control `ζ²`, so it is in the second big cell (`mem_cellTwoSet_iff`). -/
theorem an2_image_B {p : Fin 3 → ℝ} (hdom : p ∈ cellDomain) (hr : 0 < p 0)
    (hs2 : 0 < Real.sin (p 2)) (hk : 0 ≤ cκ p) {τ : ℝ} (hneg : ∀ t, 0 < t → t < τ → V₂ p t < 0)
    {t₁ : ℝ} (ht₁ : 0 < t₁) (ht₁τ : t₁ ≤ τ) (hY : an2_Y p t₁ < 0) :
    poincareAngZero (cellClass p) ∈ cellTwoSet := by
  have hs3 : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  have hQ0 : 0 < an2_Q p 0 := by
    have e : an2_Q p 0 = p 0 * Real.sin (p 2) := by unfold an2_Q; ring
    rw [e]; positivity
  have hQ1 : an2_Q p t₁ < 0 := by
    rw [an2_Y_eq] at hY
    by_contra hc; push Not at hc
    nlinarith
  -- the least root `T` of `Q` on `[0, t₁]`
  set S := {t | t ∈ Icc 0 t₁ ∧ an2_Q p t ≤ 0} with hS
  have hSc : IsCompact S := by
    refine isCompact_Icc.of_isClosed_subset ?_ (fun t ht ↦ ht.1)
    exact isClosed_Icc.inter (isClosed_le (an2_continuous_Q p) continuous_const)
  have hSne : S.Nonempty := ⟨t₁, ⟨⟨ht₁.le, le_rfl⟩, hQ1.le⟩⟩
  have hTS := hSc.sInf_mem hSne
  set T := sInf S with hT
  have hSbdd : BddBelow S := ⟨0, fun t ht ↦ ht.1.1⟩
  have hpos_before : ∀ t, 0 ≤ t → t < T → 0 < an2_Q p t := by
    intro t ht htT
    by_contra hc
    push Not at hc
    have : T ≤ t := csInf_le hSbdd ⟨⟨ht, by linarith [hTS.1.2]⟩, hc⟩
    linarith
  have hT0 : 0 < T := by
    rcases hTS.1.1.lt_or_eq with h | h
    · exact h
    · exfalso; have := hTS.2; rw [← h] at this; linarith
  have hQT : an2_Q p T = 0 := by
    rcases hTS.2.lt_or_eq with h | h
    · exfalso
      obtain ⟨s, hs, hs0⟩ := intermediate_value_Ioo' hT0.le
        ((an2_continuous_Q p).continuousOn) ⟨h, hQ0⟩
      linarith [hpos_before s hs.1.le hs.2]
    · exact h
  have hTt₁ : T < t₁ := by
    rcases hTS.1.2.lt_or_eq with h | h
    · exact h
    · exfalso; rw [h] at hQT; linarith
  -- the slope `d = (Y/t)'(T) < 0`
  set d := (1 - p 0) * Real.sin (p 2 - p 1) / 2 + T / 6 with hd
  have hexp : ∀ t, an2_Q p t = an2_Q p T + (t - T) * (d + (t - T) / 12) := by
    intro t; unfold an2_Q; rw [hd]; ring
  have hd0 : d < 0 := by
    have := hexp t₁
    rw [hQT] at this
    have h1 : 0 < t₁ - T := by linarith
    by_contra hc
    push Not at hc
    nlinarith
  have hz := cellPoint_mem_sectionZero hdom
  -- the first control and the first switch
  have hok : ∀ t ∈ Icc 0 T, V₂ p t ≤ 0 ∧ 0 ≤ an2_Y p t := by
    intro t ht
    refine ⟨?_, ?_⟩
    · rcases ht.1.lt_or_eq with h | h
      · exact (hneg t h (by linarith [ht.2])).le
      · rw [← h]
        have e : V₂ p 0 = -(√3 * cκ p) := by unfold V₂; ring
        rw [e]; linarith [mul_nonneg hs3.le hk]
    · rw [an2_Y_eq]
      rcases ht.2.lt_or_eq with h | h
      · exact mul_nonneg ht.1 (hpos_before t ht.1 h).le
      · rw [h, hQT, mul_zero]
  have hbeat : ∀ ε, 0 < ε → ∃ t ∈ Ioo T (T + ε), 0 < V₂ p t ∨ an2_Y p t < 0 := by
    intro ε hε
    set δ := min ε (-12 * d) / 2 with hδ
    have hδ0 : 0 < δ := by
      have : 0 < min ε (-12 * d) := lt_min hε (by linarith)
      linarith
    have hδ1 : δ < ε := by
      have := min_le_left ε (-12 * d); linarith
    have hδ2 : δ < -12 * d := by
      have := min_le_right ε (-12 * d); linarith
    refine ⟨T + δ, ⟨by linarith, by linarith⟩, Or.inr ?_⟩
    rw [an2_Y_eq, hexp, hQT, show T + δ - T = δ by ring]
    have : d + δ / 12 < 0 := by linarith
    have : δ * (d + δ / 12) < 0 := mul_neg_of_pos_of_neg hδ0 this
    have hTδ : 0 < T + δ := by linarith
    nlinarith
  obtain ⟨hfc, hsw⟩ := an2_firstControl_of hz.1 hT0 hok hbeat
  set z' := poincare (cellPoint p) with hz'
  have hz'e : z' = flow T (cellPoint p) ζ := by rw [hz', poincare, hfc, hsw]
  have hz'S : z' ∈ sectionZero := poincare_mem_sectionZero hz
  obtain ⟨-, -, -, -, -, e2i⟩ := zeta_flow p T
  have him : (z' 2).im = 0 := by
    rw [hz'e, an2_flow_two_im, an2_Y_eq, hQT, mul_zero]
  have hre : (z' 2).re < 0 := by
    have hV : V₂ p T < 0 := hneg T hT0 (by linarith)
    rw [← e2i, Complex.mul_im, ← hz'e, him, ζ_re, ζ_im, mul_zero, zero_add] at hV
    nlinarith
  have him1 : (z' 1).im < 0 := by
    rw [hz'e, an2_flow_one_im]
    have e : p 0 * Real.sin (p 2) + (1 - p 0) * Real.sin (p 2 - p 1) * T + T ^ 2 / 4 =
        an2_Q p T + T * d := by unfold an2_Q; rw [hd]; ring
    rw [e, hQT, zero_add]
    exact mul_neg_of_pos_of_neg hT0 hd0
  have hz2 : z' 2 = (((z' 2).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
  have hfc' : firstControl z' = ζ ^ 2 :=
    (firstControl_eq_of_ofReal_neg hz2 hre).2 (Or.inl him1)
  have hcl : poincareAngZero (cellClass p) = classOf z' := poincareAngZero_classOf hz
  exact (mem_cellTwoSet_iff _).2 ⟨z', hz'S, hcl.symm, him, hre, hfc'⟩

/-- **The switch to `1`**: if `Y ≥ 0` on `(0, τ]`, the first switch is at the root `τ` of `D`, and
the rotated image `w = ζ F(z)` lies on the section, has the class of the image, `w₁ = U₀ + i V₀`,
`w₂ = U₁ + i V₁` and `w₃ = U₂ ∈ ℝ`. -/
theorem an2_image_A {p : Fin 3 → ℝ} (hdom : p ∈ cellDomain) (hk : 0 ≤ cκ p) {τ : ℝ} (hτ : 0 < τ)
    (h0 : V₂ p τ = 0) (hneg : ∀ t, 0 < t → t < τ → V₂ p t < 0) (hpos : ∀ t, τ < t → 0 < V₂ p t)
    (hY : ∀ t ∈ Ioc 0 τ, 0 ≤ an2_Y p t) :
    ∃ w : Fin 3 → ℂ, w ∈ sectionZero ∧ poincareAngZero (cellClass p) = classOf w ∧
      (w 0).re = U₀ p τ ∧ (w 0).im = V₀ p τ ∧ (w 1).re = U₁ p τ ∧ (w 1).im = V₁ p τ ∧
      (w 2).im = 0 ∧ (w 2).re = U₂ p τ := by
  have hs3 : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  have hz := cellPoint_mem_sectionZero hdom
  have hok : ∀ t ∈ Icc 0 τ, V₂ p t ≤ 0 ∧ 0 ≤ an2_Y p t := by
    intro t ht
    rcases ht.1.lt_or_eq with h | h
    · refine ⟨?_, hY t ⟨h, ht.2⟩⟩
      rcases ht.2.lt_or_eq with h' | h'
      · exact (hneg t h h').le
      · rw [h', h0]
    · rw [← h]
      have e : V₂ p 0 = -(√3 * cκ p) := by unfold V₂; ring
      have e' : an2_Y p 0 = 0 := by unfold an2_Y; ring
      rw [e, e']
      exact ⟨by linarith [mul_nonneg hs3.le hk], le_rfl⟩
  have hbeat : ∀ ε, 0 < ε → ∃ t ∈ Ioo τ (τ + ε), 0 < V₂ p t ∨ an2_Y p t < 0 := fun ε hε ↦
    ⟨τ + ε / 2, ⟨by linarith, by linarith⟩, Or.inl (hpos _ (by linarith))⟩
  obtain ⟨hfc, hsw⟩ := an2_firstControl_of hz.1 hτ hok hbeat
  have hw := poincare_mem_sectionZero hz
  have hpw : poincare (cellPoint p) = flow τ (cellPoint p) ζ := by rw [poincare, hfc, hsw]
  obtain ⟨e0r, e0i, e1r, e1i, e2r, e2i⟩ := zeta_flow p τ
  set w := ζ • poincare (cellPoint p) with hw_def
  have hζw : w ∈ sectionZero := by
    refine ⟨fun h ↦ hw.1 ?_, ?_, ?_⟩
    · have := congrArg (fun z ↦ ζ⁻¹ • z) h
      simp only [hw_def, smul_zero, inv_smul_smul₀ (show ζ ≠ 0 from fun h ↦ by
        simpa [h] using norm_ζ)] at this
      exact this
    · exact mul_mem_walls ζ_mem_VT hw.2.1
    · have := (hamMax_smul_scale_and_tau ζ_mem_VT one_pos (poincare (cellPoint p))).1
      rw [scale_one, one_pow, one_mul] at this
      rw [hw_def, this, hw.2.2]
  have hwj : ∀ j, w j = ζ * flow τ (cellPoint p) ζ j := by
    intro j; rw [hw_def, Pi.smul_apply, smul_eq_mul, hpw]
  have hcls := classOf_smul_scale ζ_mem_VT one_pos hw
  rw [scale_one] at hcls
  refine ⟨w, hζw, ?_, by rw [hwj, e0r], by rw [hwj, e0i], by rw [hwj, e1r], by rw [hwj, e1i],
    by rw [hwj, e2i, h0], by rw [hwj, e2r]⟩
  change poincareAngZero (classOf (cellPoint p)) = _
  rw [poincareAngZero_classOf hz, hw_def, hcls]

/-- **The dichotomy at the switch**: either the image lies in the second big cell, or `Y ≥ 0` on
`(0, τ]` and the image is the rotated `w = ζ F(z)` of `an2_image_A` (with `w₃ = U₂(τ) ≤ 0`). The
hypothesis `hB` excludes a switch to `ζ²` at `t = 0`. -/
theorem an2_dichotomy {p : Fin 3 → ℝ} (hdom : p ∈ cellDomain) (hk : 0 ≤ cκ p) {τ : ℝ}
    (hτ : 0 < τ) (h0 : V₂ p τ = 0) (hneg : ∀ t, 0 < t → t < τ → V₂ p t < 0)
    (hpos : ∀ t, τ < t → 0 < V₂ p t)
    (hB : (0 < p 0 ∧ 0 < Real.sin (p 2)) ∨ ∀ t, 0 < t → 0 ≤ an2_Y p t) :
    poincareAngZero (cellClass p) ∈ cellTwoSet ∨
      (0 ≤ an2_Y p τ ∧ ∃ w : Fin 3 → ℂ, w ∈ sectionZero ∧
        poincareAngZero (cellClass p) = classOf w ∧
        (w 0).re = U₀ p τ ∧ (w 0).im = V₀ p τ ∧ (w 1).re = U₁ p τ ∧ (w 1).im = V₁ p τ ∧
        (w 2).im = 0 ∧ (w 2).re ≤ 0) := by
  by_cases h : ∀ t ∈ Ioc 0 τ, 0 ≤ an2_Y p t
  · right
    have hYτ := h τ ⟨hτ, le_rfl⟩
    obtain ⟨w, hw, hcl, e0r, e0i, e1r, e1i, e2i, e2r⟩ := an2_image_A hdom hk hτ h0 hneg hpos h
    refine ⟨hYτ, w, hw, hcl, e0r, e0i, e1r, e1i, e2i, ?_⟩
    have e := an2_Y_eq_U₂ p τ
    rw [h0] at e
    have hs3 : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
    rw [e2r]
    nlinarith
  · left
    push Not at h
    obtain ⟨t₁, ⟨ht₁, ht₁τ⟩, hY⟩ := h
    rcases hB with ⟨hr, hs2⟩ | hB
    · exact an2_image_B hdom hr hs2 hk hneg ht₁ ht₁τ hY
    · exact absurd (hB t₁ ht₁) (not_le.2 hY)

/-! ### The cell coordinates of the image -/

/-- On the wall `𝒲₀` (`z₃ = x₃ ≤ 0`): `H_F⁺(z) = RR(z₁, i z₂) - x₃/2`. -/
theorem an2_hamMax_wall {z : Fin 3 → ℂ} {x₃ : ℝ} (h2 : z 2 = x₃) (hx : x₃ ≤ 0) :
    hamMax z = RR (z 0) (z 1 * I) - x₃ / 2 := by
  have hR : ∀ u : ℂ, ham z u = RR (z 0) (z 1 * I) + u.re * x₃ := by
    intro u
    rw [ham, h2, RR_eq_re_mul_add_im_mul u]
    simp
  rw [hamMax, hR, hR, hR, Complex.one_re, ζ_re, ζ_sq_re, max_self, max_eq_right (by linarith)]
  ring

/-- `RR(r₁ e^{iθ₁}, i r₂ e^{iθ₂}) = r₁ r₂ sin(θ₁ - θ₂)`. -/
theorem an2_RR_polar (r₁ r₂ θ₁ θ₂ : ℝ) :
    RR ((r₁ : ℂ) * Complex.exp ((θ₁ : ℂ) * I)) ((r₂ : ℂ) * Complex.exp ((θ₂ : ℂ) * I) * I) =
      r₁ * r₂ * Real.sin (θ₁ - θ₂) := by
  rw [RR_eq_re_mul_add_im_mul, Real.sin_sub]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.I_re, Complex.I_im]
  ring

/-- **The cell coordinates of a point of the section on `𝒲₀`** (`w₃ ∈ ℝ_{≤0}`, the tie `w₃ = 0`
included) with `w₁, w₂ ≠ 0`: `cellPoint (cellCoords w)` is the rescaling of `w` with
`r₁ + r₂ = 1` (Lemma 15.1.1), so it has the class of `w`; `r₂ ∈ (0, 1)`, `θ₂ = arg w₂`, and
`ψ = arg w₂ - arg w₁` reduced to `[0, 2π)` lies in `[0, π]`, since `sin ψ ≥ 0` by the vanishing of
the Hamiltonian (`x₃ = 2 r₁ r₂ sin(θ₁ - θ₂)`, (15.1.1)). This is `cellClass_cellCoords`
(`x₃ < 0`) with the face `x₃ = 0` added. -/
theorem an2_cellCoords_spec {w : Fin 3 → ℂ} (hw : w ∈ sectionZero) (h3 : (w 2).im = 0)
    (h3' : (w 2).re ≤ 0) (h0 : w 0 ≠ 0) (h1 : w 1 ≠ 0) :
    cellCoords w 0 ∈ Ioo 0 1 ∧ cellCoords w 1 ∈ Icc 0 Real.pi ∧
      cellCoords w 1 = toIcoMod Real.two_pi_pos 0 (Complex.arg (w 1) - Complex.arg (w 0)) ∧
      cellCoords w 2 = Complex.arg (w 1) ∧ cellClass (cellCoords w) = classOf w := by
  set a := ‖w 0‖ with ha_def
  set b := ‖w 1‖ with hb_def
  set θ₁ := Complex.arg (w 0) with hθ₁
  set θ₂ := Complex.arg (w 1) with hθ₂
  set x₃ := (w 2).re with hx₃
  have hz2 : w 2 = (x₃ : ℂ) := Complex.ext (by simp [x₃]) (by simp [h3])
  have hz0 : w 0 = (a : ℂ) * Complex.exp ((θ₁ : ℂ) * I) :=
    (Complex.norm_mul_exp_arg_mul_I _).symm
  have hz1 : w 1 = (b : ℂ) * Complex.exp ((θ₂ : ℂ) * I) :=
    (Complex.norm_mul_exp_arg_mul_I _).symm
  have hH : a * b * Real.sin (θ₁ - θ₂) - x₃ / 2 = 0 := by
    have h := hw.2.2
    rwa [an2_hamMax_wall hz2 h3', hz0, hz1, an2_RR_polar] at h
  have ha : 0 < a := norm_pos_iff.2 h0
  have hb : 0 < b := norm_pos_iff.2 h1
  have hsin : 0 ≤ Real.sin (θ₂ - θ₁) := by
    have : Real.sin (θ₁ - θ₂) ≤ 0 := by
      by_contra hc
      push Not at hc
      have := mul_pos (mul_pos ha hb) hc
      linarith
    rw [show θ₂ - θ₁ = -(θ₁ - θ₂) by ring, Real.sin_neg]
    linarith
  -- Lemma 15.1.1: the rescaling `s` with `r₁ + r₂ = 1`
  set s := (-a + √(a ^ 2 + 4 * b)) / (2 * b) with hs_def
  have hd : 0 ≤ a ^ 2 + 4 * b := by positivity
  have hsq := Real.sq_sqrt hd
  have hlt : a < √(a ^ 2 + 4 * b) := by
    rw [Real.lt_sqrt ha.le]; linarith
  have hs : 0 < s := div_pos (by linarith) (by positivity)
  have hroot : a * s + b * s ^ 2 = 1 := by
    rw [hs_def]
    field_simp
    linear_combination hsq
  -- `ψ`
  set ψ := toIcoMod Real.two_pi_pos 0 (θ₂ - θ₁) with hψ_def
  have hψ : ψ = θ₂ - θ₁ - toIcoDiv Real.two_pi_pos 0 (θ₂ - θ₁) • (2 * Real.pi) :=
    eq_sub_of_add_eq (toIcoMod_add_toIcoDiv_zsmul _ _ _)
  set n := toIcoDiv Real.two_pi_pos 0 (θ₂ - θ₁)
  have hψmem : ψ ∈ Ico 0 (0 + 2 * Real.pi) := toIcoMod_mem_Ico _ _ _
  have hsinψ : Real.sin ψ = Real.sin (θ₂ - θ₁) := by
    rw [hψ, zsmul_eq_mul, Real.sin_sub_int_mul_two_pi]
  have hψlt : ψ ≤ Real.pi := by
    by_contra hc
    push Not at hc
    have h1 : 0 < Real.sin (ψ - Real.pi) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hψmem.2])
    rw [Real.sin_sub_pi] at h1
    linarith
  have hc : cellCoords w = ![s ^ 2 * b, ψ, θ₂] := by
    have e : (if b = 0 then a⁻¹ else (-a + √(a ^ 2 + 4 * b)) / (2 * b)) = s :=
      ite_eq_right_iff.2 fun h ↦ absurd h hb.ne'
    exact congrArg (fun t ↦ ![t ^ 2 * b, ψ, θ₂]) e
  have has : 1 - s ^ 2 * b = a * s := by linarith
  rw [hc]
  refine ⟨?_, ⟨hψmem.1, hψlt⟩, rfl, rfl, ?_⟩
  · change s ^ 2 * b ∈ Ioo 0 1
    have : 0 < a * s := mul_pos ha hs
    constructor
    · positivity
    · linarith
  change classOf (cellPoint ![s ^ 2 * b, ψ, θ₂]) = classOf w
  have e : cellPoint ![s ^ 2 * b, ψ, θ₂] = (1 : ℂ) • scale s w := by
    funext j
    fin_cases j
    · change ((1 - s ^ 2 * b : ℝ) : ℂ) * Complex.exp (((θ₂ - ψ : ℝ) : ℂ) * I) =
        1 * ((s : ℂ) * w 0)
      have h2π : Complex.exp ((((n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * I) = 1 := by
        rw [← Complex.exp_int_mul_two_pi_mul_I n]
        push_cast
        ring_nf
      have hadd : ∀ x y : ℝ, Complex.exp (((x + y : ℝ) : ℂ) * I) =
          Complex.exp ((x : ℂ) * I) * Complex.exp ((y : ℂ) * I) := by
        intro x y; push_cast; rw [add_mul, Complex.exp_add]
      rw [show θ₂ - ψ = θ₁ + (n : ℝ) * (2 * Real.pi) by rw [hψ, zsmul_eq_mul]; ring, hadd,
        h2π, hz0, has]
      push_cast
      ring
    · change ((s ^ 2 * b : ℝ) : ℂ) * Complex.exp ((θ₂ : ℂ) * I) = 1 * ((s : ℂ) ^ 2 * w 1)
      rw [hz1]
      push_cast
      ring
    · change ((-2 * (1 - s ^ 2 * b) * (s ^ 2 * b) * Real.sin ψ : ℝ) : ℂ) =
        1 * ((s : ℂ) ^ 3 * w 2)
      have h : -2 * (1 - s ^ 2 * b) * (s ^ 2 * b) * Real.sin ψ = s ^ 3 * x₃ := by
        rw [hsinψ, has, show θ₂ - θ₁ = -(θ₁ - θ₂) by ring, Real.sin_neg]
        linear_combination (2 * s ^ 3) * hH
      rw [h, hz2]
      push_cast
      ring
  rw [e, classOf_smul_scale one_mem_VT hs hw]

/-! ### The angles of the image -/

/-- `ψ < π/3` for the angle `ψ ∈ [0, π]` from `w₀` to `w₁` when `Im(w̄₀ w₁ e^{-iπ/3}) < 0`
(`toIcoMod_lt_pi_div_three`, with the faces `ψ ∈ {0, π}`). -/
theorem an2_toIcoMod_lt_pi_div_three {w₀ w₁ : ℂ}
    (hψ : toIcoMod Real.two_pi_pos 0 (Complex.arg w₁ - Complex.arg w₀) ∈ Icc 0 Real.pi)
    (h : w₀.re * (w₁.im - √3 * w₁.re) - w₀.im * (w₁.re + √3 * w₁.im) < 0) :
    toIcoMod Real.two_pi_pos 0 (Complex.arg w₁ - Complex.arg w₀) < Real.pi / 3 := by
  set ψ := toIcoMod Real.two_pi_pos 0 (Complex.arg w₁ - Complex.arg w₀) with hψdef
  have hw₀ : w₀ ≠ 0 := by rintro rfl; simp at h
  have hw₁ : w₁ ≠ 0 := by rintro rfl; simp at h
  obtain ⟨es, ec⟩ := sin_cos_toIcoMod hw₀ hw₁
  rw [← hψdef] at es ec
  have hN : 0 < ‖w₀‖ * ‖w₁‖ := mul_pos (norm_pos_iff.2 hw₀) (norm_pos_iff.2 hw₁)
  have key : Real.sin ψ - √3 * Real.cos ψ < 0 := by
    have : (Real.sin ψ - √3 * Real.cos ψ) * (‖w₀‖ * ‖w₁‖) < 0 := by
      rw [sub_mul, mul_assoc, es, ec]; linarith
    exact neg_of_mul_neg_left this hN.le
  by_contra hge
  push Not at hge
  have hpos : 0 ≤ Real.sin (ψ - Real.pi / 3) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hψ.2])
  rw [Real.sin_sub, Real.cos_pi_div_three, Real.sin_pi_div_three] at hpos
  linarith

/-- `b ≤ arg w` for `b ∈ [0, π)` when `Im w > 0` and `Re w sin b ≤ Im w cos b`
(`sin (arg w - b) ≥ 0`). -/
theorem an2_le_arg {w : ℂ} (him : 0 < w.im) {b : ℝ} (hbπ : b < Real.pi)
    (h : w.re * Real.sin b ≤ w.im * Real.cos b) : b ≤ Complex.arg w := by
  have hw : w ≠ 0 := by rintro rfl; simp at him
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hpos : 0 < Complex.arg w := by
    rcases (Complex.arg_nonneg_iff.2 him.le).lt_or_eq with h' | h'
    · exact h'
    · exfalso
      have := Complex.sin_arg w
      rw [← h', Real.sin_zero] at this
      have : w.im = 0 := by
        have h2 := (div_eq_zero_iff.1 this.symm).resolve_right hn.ne'
        exact h2
      linarith
  have hle := Complex.arg_le_pi w
  have key : 0 ≤ Real.sin (Complex.arg w - b) := by
    rw [Real.sin_sub, Complex.sin_arg, Complex.cos_arg hw]
    have : w.im / ‖w‖ * Real.cos b - w.re / ‖w‖ * Real.sin b =
        (w.im * Real.cos b - w.re * Real.sin b) / ‖w‖ := by ring
    rw [this]
    exact div_nonneg (by linarith) hn.le
  by_contra hc
  push Not at hc
  have : Real.sin (Complex.arg w - b) < 0 :=
    Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)
  linarith

/-- `arg w ∈ (0, π)` when `Im w > 0`. -/
theorem an2_arg_mem_Ioo {w : ℂ} (him : 0 < w.im) : Complex.arg w ∈ Ioo 0 Real.pi := by
  have h := an2_le_arg him Real.pi_pos (by simp [Real.sin_zero, Real.cos_zero, him.le])
  refine ⟨?_, ?_⟩
  · rcases h.lt_or_eq with h | h
    · exact h
    · exfalso
      have hw : w ≠ 0 := by rintro rfl; simp at him
      have := Complex.sin_arg w
      rw [← h, Real.sin_zero] at this
      have := (div_eq_zero_iff.1 this.symm).resolve_right (norm_pos_iff.2 hw).ne'
      linarith
  · exact (Complex.arg_lt_pi_iff.2 (Or.inr him.ne'))

/-- When `Im w₀, Im w₁ > 0` and the angle `ψ ∈ [0, 2π)` from `w₀` to `w₁` is at most `π`, it is
`arg w₁ - arg w₀` (no reduction). -/
theorem an2_toIcoMod_eq_sub {w₀ w₁ : ℂ} (h0 : 0 < w₀.im) (h1 : 0 < w₁.im)
    (hψ : toIcoMod Real.two_pi_pos 0 (Complex.arg w₁ - Complex.arg w₀) ≤ Real.pi) :
    toIcoMod Real.two_pi_pos 0 (Complex.arg w₁ - Complex.arg w₀) =
      Complex.arg w₁ - Complex.arg w₀ := by
  obtain ⟨a0, a0'⟩ := an2_arg_mem_Ioo h0
  obtain ⟨a1, a1'⟩ := an2_arg_mem_Ioo h1
  rcases le_or_gt 0 (Complex.arg w₁ - Complex.arg w₀) with h | h
  · rw [toIcoMod_eq_self]
    constructor <;> linarith
  · exfalso
    have e : toIcoMod Real.two_pi_pos 0 (Complex.arg w₁ - Complex.arg w₀) =
        Complex.arg w₁ - Complex.arg w₀ + 2 * Real.pi := by
      rw [← toIcoMod_add_right Real.two_pi_pos 0 (Complex.arg w₁ - Complex.arg w₀),
        toIcoMod_eq_self]
      constructor <;> linarith
    rw [e] at hψ
    linarith

/-! ### The faces where the first control is not `ζ` -/

/-- A rotation by `ζ^k` of a point of the edge `r₂ = 0`: `cellPoint (0, ψ', θ₂') = ζ^k cellPoint p`
when `θ₂' - ψ' = θ₁ + 2πk/3`. -/
theorem an2_cellPoint_r_zero_rot {p : Fin 3 → ℝ} (h0 : p 0 = 0) (k : ℕ) {ψ' θ' : ℝ}
    (h : θ' - ψ' = p 2 - p 1 + 2 * Real.pi * k / 3) :
    cellPoint ![0, ψ', θ'] = ζ ^ k • cellPoint p := by
  have hζ : ζ ^ k = Complex.exp (((2 * Real.pi * k / 3 : ℝ) : ℂ) * I) := by
    rw [ζ, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  funext j
  fin_cases j
  · simp only [cellPoint, Pi.smul_apply, smul_eq_mul, h0, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.zero_eta]
    rw [h, hζ, sub_zero, Complex.ofReal_one, one_mul, one_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  · simp [cellPoint, h0]
  · simp [cellPoint, h0]

/-- **The edge `r₂ = 0` lies in `𝒟₀₀`**: `cellPoint p = (e^{iθ₁}, 0, 0)` depends only on
`θ₁ = θ₂ - ψ`, and a rotation by `ζ^k` brings `θ₁` into `[π/3, π]`, which is `θ₂ - ψ` for a point
of `𝒟₀₀` (`ψ ∈ [0, π/3]`, `θ₂ ∈ [π - 1.1, π]`). -/
theorem an2_mem_boxSet_zero_zero_of_r_zero {p : Fin 3 → ℝ} (hp : p ∈ closedBoxOne)
    (h0 : p 0 = 0) : cellClass p ∈ boxSet 0 0 := by
  obtain ⟨-, ⟨h1, h1'⟩, ⟨h2, h2'⟩⟩ := hp
  have hpi := Real.pi_gt_three
  have hdom : p ∈ cellDomain := ⟨by rw [h0]; exact ⟨le_rfl, zero_le_one⟩, ⟨h1, h1'⟩,
    ⟨by linarith, h2'⟩⟩
  have hz := cellPoint_mem_sectionZero hdom
  have hvk : ∀ k : ℕ, ζ ^ k ∈ VT := by
    intro k
    induction k with
    | zero => rw [pow_zero]; exact one_mem_VT
    | succ m ih => rw [pow_succ]; exact mul_mem_VT ih ζ_mem_VT
  -- the class of `(0, ψ', θ')` for `θ' - ψ' = θ₁ + 2πk/3`
  have key : ∀ (k : ℕ) (ψ' θ' : ℝ), θ' - ψ' = p 2 - p 1 + 2 * Real.pi * k / 3 →
      ψ' ∈ Icc 0 (Real.pi / 3) → θ' ∈ Icc (Real.pi - 1.1) Real.pi → cellClass p ∈ boxSet 0 0 := by
    intro k ψ' θ' h hψ' hθ'
    refine ⟨![0, ψ', θ'], ?_, ?_⟩
    · rw [mem_cellBox_zero_zero]
      exact ⟨⟨le_rfl, zero_le_one⟩, hψ', hθ'⟩
    · have := classOf_smul_scale (hvk k) one_pos hz
      rw [scale_one, ← an2_cellPoint_r_zero_rot h0 k h] at this
      exact this
  -- the four arcs of `θ₁ ∈ [-π, π]`
  set θ₁ := p 2 - p 1 with hθ₁
  have hθ₁lo : -Real.pi ≤ θ₁ := by linarith
  have hθ₁hi : θ₁ ≤ Real.pi := by linarith
  have hb : Real.pi - 1.1 ≤ 2 * Real.pi / 3 := by norm_num; linarith [Real.pi_lt_d2]
  have arc : ∀ (k : ℕ), Real.pi / 3 ≤ θ₁ + 2 * Real.pi * k / 3 →
      θ₁ + 2 * Real.pi * k / 3 ≤ Real.pi → cellClass p ∈ boxSet 0 0 := by
    intro k hlo hhi
    rcases le_total (θ₁ + 2 * Real.pi * k / 3) (2 * Real.pi / 3) with h | h
    · exact key k (Real.pi / 3) (θ₁ + 2 * Real.pi * k / 3 + Real.pi / 3) (by ring)
        ⟨by positivity, le_rfl⟩ ⟨by linarith, by linarith⟩
    · exact key k (Real.pi - (θ₁ + 2 * Real.pi * k / 3)) Real.pi (by ring)
        ⟨by linarith, by linarith⟩ ⟨by linarith [Real.pi_pos], le_rfl⟩
  rcases le_total (Real.pi / 3) θ₁ with h | h
  · exact arc 0 (by simpa using h) (by simpa using hθ₁hi)
  rcases le_total (-(Real.pi / 3)) θ₁ with h' | h'
  · exact arc 1 (by push_cast; linarith) (by push_cast; linarith)
  · exact arc 2 (by push_cast; linarith) (by push_cast; linarith)

/-- **The faces `ψ = 0` and `r₂ = 1` over `θ₂ ∈ [0, π/3]` lie in `𝒟₀₀`**: there `z₃ = 0` and the
rotation by `ζ` gives the point `(r₂, 0, θ₂ + 2π/3)` of `𝒟₀₀` (`boundary_maps_red_faces`; on
`r₂ = 1` the point does not depend on `ψ`). -/
theorem an2_mem_boxSet_zero_zero_of_rot {p : Fin 3 → ℝ} (h0 : p 0 ∈ Ioc 0 1)
    (hface : p 1 = 0 ∨ p 0 = 1) (h2 : p 2 ∈ Icc 0 (Real.pi / 3)) : cellClass p ∈ boxSet 0 0 := by
  have hpi := Real.pi_gt_three
  have hq : cellClass p = cellClass ![p 0, 0, p 2] := by
    rw [cellClass, cellClass]
    congr 1
    rcases hface with h | h
    · funext j
      fin_cases j <;> simp [cellPoint, h]
    · funext j
      fin_cases j <;> simp [cellPoint, h]
  have hrot := (boundary_maps_red_faces.2.2.1 ![p 0, 0, p 2] (by simpa using h0) (Or.inl rfl)
    (by simpa using h2)).2
  rw [hq, hrot]
  refine ⟨_, ?_, rfl⟩
  rw [mem_cellBox_zero_zero]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  refine ⟨⟨h0.1.le, h0.2⟩, ⟨le_rfl, by positivity⟩, ⟨?_, by linarith [h2.2]⟩⟩
  have := Real.pi_lt_d2
  norm_num at this ⊢
  linarith [h2.1]

end SmoothedPolygons.TriFuller.BoxAnalytic
