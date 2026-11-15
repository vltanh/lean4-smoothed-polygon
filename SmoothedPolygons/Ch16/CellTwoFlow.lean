module

public import SmoothedPolygons.Ch16.DOutInvariant
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The Fuller–Poincaré map on the second big cell: the exact structure

Exact (non-numerical) facts about the first arc of the Fuller system from a point of the second
big cell `cellTwoDomain` (`r₂ ∈ (0, 1)`, `ψ ∈ (0, π)`, `θ₂ ∈ (-π, 0]`, first control `ζ²`), used by
the analytic proof of `CellTwoEntersDOut` (`SmoothedPolygons/Ch16/BasinHypotheses.lean`) in
`SmoothedPolygons/Ch16/CellTwoEntersDOut.lean`.

* **The flow along `ζ²`** (`sq_flow`): with `z₁ = x₁ + i y₁ = r₁ e^{iθ₁}`, `z₂ = x₂ + i y₂ =
  r₂ e^{iθ₂}` (`θ₁ = θ₂ - ψ`) and `κ = r₁ r₂ sin ψ = x₁ y₂ - y₁ x₂` (`cκ_eq`), the coordinates of
  `z(t) = z(t, z, ζ²)` are `P_k + i Q_k`, polynomial in `t`. The switching function of `ζ² → ζ` is
  `Y = Q₂ = Im z₃ = t q(t)`, `q(t) = y₂ + y₁ t/2 + t²/12` (`ham_ζ_sub_ham_sq`, `Q₂_eq`); that of
  `ζ² → 1` is `A = -Im (ζ² z₃) = (√3/2) P₂ + Q₂/2 = -√3 κ + … - t³/12` (`ham_one_sub_ham_sq`).
* **The root of `q`** (`rootT_spec`): `q` is a convex quadratic with `q(0) = y₂ ≤ 0`; its positive
  root `T = -3 y₁ + √(9 y₁² - 12 y₂)` is the time at which `ζ` beats `ζ²` unless `1` does first.
* **The first control and the first switch** (`firstControl_sq`): `ζ²` is the first control and
  `t_sw = T*` as soon as `A ≤ 0` and `Y ≤ 0` on `[0, T*]` and one of them is positive at times
  arbitrarily close to `T*` from the right.
* Two facts about a function that is `≤ 0` to the left of a zero (`le_zero_of_nonpos_left`,
  `deriv_nonneg_of_nonpos_left`), for the switch at the first sign change of `A`.
-/

@[expose] public section

namespace SmoothedPolygons.TriFuller.CellTwoAnalytic

open Set Filter Topology
open Complex (I)
open DOutAnalytic (cκ cellPoint_reim sin_one_eq)

/-! ### The coefficients and the flow along `ζ²` -/

/-- `x₁ = r₁ cos θ₁`, `r₁ = 1 - r₂`, `θ₁ = θ₂ - ψ`. -/
noncomputable def bx₁ (p : Fin 3 → ℝ) : ℝ := (1 - p 0) * Real.cos (p 2 - p 1)

/-- `y₁ = r₁ sin θ₁`. -/
noncomputable def by₁ (p : Fin 3 → ℝ) : ℝ := (1 - p 0) * Real.sin (p 2 - p 1)

/-- `x₂ = r₂ cos θ₂`. -/
noncomputable def bx₂ (p : Fin 3 → ℝ) : ℝ := p 0 * Real.cos (p 2)

/-- `y₂ = r₂ sin θ₂`. -/
noncomputable def by₂ (p : Fin 3 → ℝ) : ℝ := p 0 * Real.sin (p 2)

/-- `P₀ = Re z₁(t) = x₁ - √3 t/2`. -/
noncomputable def P₀ (p : Fin 3 → ℝ) (t : ℝ) : ℝ := bx₁ p - √3 / 2 * t

/-- `Q₀ = Im z₁(t) = y₁ + t/2`. -/
noncomputable def Q₀ (p : Fin 3 → ℝ) (t : ℝ) : ℝ := by₁ p + t / 2

/-- `P₁ = Re z₂(t) = x₂ + x₁ t - √3 t²/4`. -/
noncomputable def P₁ (p : Fin 3 → ℝ) (t : ℝ) : ℝ := bx₂ p + bx₁ p * t - √3 / 4 * t ^ 2

/-- `Q₁ = Im z₂(t) = y₂ + y₁ t + t²/4`. -/
noncomputable def Q₁ (p : Fin 3 → ℝ) (t : ℝ) : ℝ := by₂ p + by₁ p * t + t ^ 2 / 4

/-- `P₂ = Re z₃(t) = -2κ + x₂ t + x₁ t²/2 - √3 t³/12`. -/
noncomputable def P₂ (p : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  -2 * cκ p + bx₂ p * t + bx₁ p * t ^ 2 / 2 - √3 / 12 * t ^ 3

/-- `Q₂ = Im z₃(t) = y₂ t + y₁ t²/2 + t³/12`: the switching function `Y` of `ζ² → ζ`. -/
noncomputable def Q₂ (p : Fin 3 → ℝ) (t : ℝ) : ℝ := by₂ p * t + by₁ p * t ^ 2 / 2 + t ^ 3 / 12

/-- `A = -Im (ζ² z₃(t)) = (√3/2) P₂ + Q₂/2`: the switching function of `ζ² → 1`. -/
noncomputable def Acub (p : Fin 3 → ℝ) (t : ℝ) : ℝ := √3 / 2 * P₂ p t + Q₂ p t / 2

/-- `q(t) = y₂ + y₁ t/2 + t²/12`, with `Q₂ = t q(t)`. -/
noncomputable def qY (p : Fin 3 → ℝ) (t : ℝ) : ℝ := by₂ p + by₁ p * t / 2 + t ^ 2 / 12

theorem Q₂_eq (p : Fin 3 → ℝ) (t : ℝ) : Q₂ p t = t * qY p t := by
  unfold Q₂ qY; ring

/-- `κ = r₁ r₂ sin ψ = x₁ y₂ - y₁ x₂`. -/
theorem cκ_eq (p : Fin 3 → ℝ) : cκ p = bx₁ p * by₂ p - by₁ p * bx₂ p := by
  unfold cκ bx₁ by₂ by₁ bx₂
  rw [sin_one_eq p]
  ring

/-- The coordinates of `z(t, z, ζ²)` for `z = cellPoint p`. -/
theorem sq_flow (p : Fin 3 → ℝ) (t : ℝ) :
    (flow t (cellPoint p) (ζ ^ 2) 0).re = P₀ p t ∧ (flow t (cellPoint p) (ζ ^ 2) 0).im = Q₀ p t ∧
    (flow t (cellPoint p) (ζ ^ 2) 1).re = P₁ p t ∧ (flow t (cellPoint p) (ζ ^ 2) 1).im = Q₁ p t ∧
    (flow t (cellPoint p) (ζ ^ 2) 2).re = P₂ p t ∧
      (flow t (cellPoint p) (ζ ^ 2) 2).im = Q₂ p t := by
  obtain ⟨c0, c1, c2, c3, c4, c5⟩ := cellPoint_reim p
  have f0 : flow t (cellPoint p) (ζ ^ 2) 0 = cellPoint p 0 - I * t * ζ ^ 2 := rfl
  have f1 : flow t (cellPoint p) (ζ ^ 2) 1 =
      cellPoint p 1 + cellPoint p 0 * t - I * t ^ 2 * ζ ^ 2 / 2 := rfl
  have f2 : flow t (cellPoint p) (ζ ^ 2) 2 =
      cellPoint p 2 + cellPoint p 1 * t + cellPoint p 0 * t ^ 2 / 2 - I * t ^ 3 * ζ ^ 2 / 6 := rfl
  rw [f0, f1, f2]
  simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.div_re, Complex.div_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, ζ_sq_re, ζ_sq_im, c0, c1, c2, c3, c4, c5, P₀, Q₀, P₁,
    Q₁, P₂, Q₂, bx₁, by₁, bx₂, by₂, cκ]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals norm_num
  all_goals ring

/-- The gain of `1` over `ζ²` along `ζ²`: `H_F(z(t), 1) - H_F(z(t), ζ²) = √3 A`. -/
theorem ham_one_sub_ham_sq (p : Fin 3 → ℝ) (t : ℝ) :
    ham (flow t (cellPoint p) (ζ ^ 2)) 1 - ham (flow t (cellPoint p) (ζ ^ 2)) (ζ ^ 2) =
      √3 * Acub p t := by
  obtain ⟨-, -, -, -, e2r, e2i⟩ := sq_flow p t
  have hs3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [ham, RR_eq_re_mul_add_im_mul, ζ_sq_re, ζ_sq_im, Complex.one_re, Complex.one_im, e2r,
    e2i, Acub]
  linear_combination (-(P₂ p t) / 2) * hs3

/-- The gain of `ζ` over `ζ²` along `ζ²`: `H_F(z(t), ζ) - H_F(z(t), ζ²) = √3 Y`. -/
theorem ham_ζ_sub_ham_sq (p : Fin 3 → ℝ) (t : ℝ) :
    ham (flow t (cellPoint p) (ζ ^ 2)) ζ - ham (flow t (cellPoint p) (ζ ^ 2)) (ζ ^ 2) =
      √3 * Q₂ p t := by
  obtain ⟨-, -, -, -, -, e2i⟩ := sq_flow p t
  simp only [ham, RR_eq_re_mul_add_im_mul, ζ_re, ζ_im, ζ_sq_re, ζ_sq_im, e2i]
  ring

/-- `A` at `t = 0`: `A(0) = -√3 κ`. -/
theorem Acub_zero (p : Fin 3 → ℝ) : Acub p 0 = -(√3 * cκ p) := by
  unfold Acub P₂ Q₂; ring

/-- `A' = (√3/2) P₁ + Q₁/2`. -/
theorem hasDerivAt_Acub (p : Fin 3 → ℝ) (t : ℝ) :
    HasDerivAt (Acub p) (√3 / 2 * P₁ p t + Q₁ p t / 2) t := by
  have hs3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have e : Acub p = fun s ↦ -(√3 * cκ p) + (√3 / 2 * bx₂ p + by₂ p / 2) * s +
      (√3 / 4 * bx₁ p + by₁ p / 4) * s ^ 2 + (-1 / 12) * s ^ 3 := by
    funext s; unfold Acub P₂ Q₂; linear_combination (-(s ^ 3) / 24) * hs3
  rw [e]
  have h1 := hasDerivAt_id t
  have h2 := hasDerivAt_pow 2 t
  have h3 := hasDerivAt_pow 3 t
  have := (((h1.const_mul (√3 / 2 * bx₂ p + by₂ p / 2)).const_add (-(√3 * cκ p))).add
    (h2.const_mul (√3 / 4 * bx₁ p + by₁ p / 4))).add (h3.const_mul (-1 / 12 : ℝ))
  convert this using 1
  · funext s; simp only [Pi.add_apply, id]
  · unfold P₁ Q₁; push_cast; linear_combination (-(t ^ 2) / 8) * hs3

theorem continuous_Acub (p : Fin 3 → ℝ) : Continuous (Acub p) := by
  unfold Acub P₂ Q₂; fun_prop

/-! ### The first control `ζ²` and the first switch -/

/-- **The first control is `ζ²` and the first switch is at `T*`** when `A ≤ 0` and `Y ≤ 0` on
`[0, T*]` (`ζ²` maximizes the Hamiltonian, `ham_one_sub_ham_sq`, `ham_ζ_sub_ham_sq`) and `A > 0`
or `Y > 0` at times arbitrarily close to `T*` from the right. -/
theorem firstControl_sq {p : Fin 3 → ℝ} (hz : cellPoint p ≠ 0) {T : ℝ} (hT : 0 < T)
    (hmax : ∀ t ∈ Icc 0 T, Acub p t ≤ 0 ∧ Q₂ p t ≤ 0)
    (hbeat : ∀ ε > 0, ∃ t ∈ Ioo T (T + ε), 0 < Acub p t ∨ 0 < Q₂ p t) :
    firstControl (cellPoint p) = ζ ^ 2 ∧ firstSwitchTime (cellPoint p) = T := by
  have hs3 : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  -- `ζ²` maximizes on `[0, T]`
  have hfc : firstControl (cellPoint p) = ζ ^ 2 := by
    refine (firstControl_eq_iff hz).2 ⟨ζ_sq_mem_VT, T, hT, fun t ht v hv ↦ ?_⟩
    obtain ⟨hA, hY⟩ := hmax t ht
    rcases mem_VT.1 hv with rfl | rfl | rfl
    · have := ham_one_sub_ham_sq p t
      nlinarith
    · have := ham_ζ_sub_ham_sq p t
      nlinarith
    · exact le_rfl
  refine ⟨hfc, ?_⟩
  -- the beaten times are the times with `A > 0` or `Y > 0`
  have key : ∀ t, ((∃ v ∈ VT, ham (flow t (cellPoint p) (ζ ^ 2)) (ζ ^ 2) <
      ham (flow t (cellPoint p) (ζ ^ 2)) v) ↔ (0 < Acub p t ∨ 0 < Q₂ p t)) := by
    intro t
    have e1 := ham_one_sub_ham_sq p t
    have e2 := ham_ζ_sub_ham_sq p t
    constructor
    · rintro ⟨v, hv, hlt⟩
      rcases mem_VT.1 hv with rfl | rfl | rfl
      · left
        by_contra hc
        push Not at hc
        nlinarith
      · right
        by_contra hc
        push Not at hc
        nlinarith
      · exact absurd hlt (lt_irrefl _)
    · rintro (h | h)
      · exact ⟨1, one_mem_VT, by nlinarith [mul_pos hs3 h]⟩
      · exact ⟨ζ, ζ_mem_VT, by nlinarith [mul_pos hs3 h]⟩
  unfold firstSwitchTime
  rw [hfc]
  apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
  · obtain ⟨t, ht, h⟩ := hbeat 1 one_pos
    exact ⟨t, hT.trans ht.1, (key t).2 h⟩
  · rintro a ⟨ha, hbeat'⟩
    have h := (key a).1 hbeat'
    by_contra hlt
    push Not at hlt
    obtain ⟨hA, hY⟩ := hmax a ⟨ha.le, hlt.le⟩
    rcases h with h | h <;> linarith
  · intro w hw
    obtain ⟨t, ht, h⟩ := hbeat (w - T) (by linarith)
    exact ⟨t, ⟨hT.trans ht.1, (key t).2 h⟩, by linarith [ht.2]⟩

/-! ### The root of `q` -/

/-- The positive root `T = -3 y₁ + √(9 y₁² - 12 y₂)` of `12 q(t) = t² + 6 y₁ t + 12 y₂`. -/
noncomputable def rootT (p : Fin 3 → ℝ) : ℝ := -3 * by₁ p + √(9 * by₁ p ^ 2 - 12 * by₂ p)

/-- The signs on the second cell: `y₂ ≤ 0 < κ`, and `y₂ < 0` or `y₁ < 0`. -/
theorem cellTwo_facts {p : Fin 3 → ℝ} (hp : p ∈ cellTwoDomain) :
    by₂ p ≤ 0 ∧ 0 < cκ p ∧ (by₂ p < 0 ∨ by₁ p < 0) ∧ p ∈ cellDomain := by
  obtain ⟨⟨h0, h0'⟩, ⟨h1, h1'⟩, ⟨h2, h2'⟩⟩ := hp
  have hpi := Real.pi_gt_three
  have hs1 : 0 < Real.sin (p 1) := Real.sin_pos_of_pos_of_lt_pi h1 h1'
  refine ⟨?_, ?_, ?_, ⟨⟨h0.le, h0'.le⟩, ⟨h1.le, h1'.le⟩, ⟨h2.le, by linarith⟩⟩⟩
  · unfold by₂
    exact mul_nonpos_of_nonneg_of_nonpos h0.le
      (Real.sin_nonpos_of_nonpos_of_neg_pi_le h2' h2.le)
  · unfold cκ
    have : 0 < 1 - p 0 := by linarith
    positivity
  · rcases h2'.lt_or_eq with h | h
    · left
      unfold by₂
      exact mul_neg_of_pos_of_neg h0 (Real.sin_neg_of_neg_of_neg_pi_lt h h2)
    · right
      unfold by₁
      rw [h, zero_sub, Real.sin_neg]
      have : 0 < 1 - p 0 := by linarith
      nlinarith

/-- **The root of `q`**: `T > 0`, `q(T) = 0`, `q < 0` on `(0, T)` and `q > 0` after `T`. -/
theorem rootT_spec {p : Fin 3 → ℝ} (hp : p ∈ cellTwoDomain) :
    0 < rootT p ∧ qY p (rootT p) = 0 ∧ (∀ t, 0 < t → t < rootT p → qY p t < 0) ∧
      ∀ t, rootT p < t → 0 < qY p t := by
  obtain ⟨hy2, -, hor, -⟩ := cellTwo_facts hp
  have hd : 0 ≤ 9 * by₁ p ^ 2 - 12 * by₂ p := by nlinarith [sq_nonneg (by₁ p)]
  have hss : √(9 * by₁ p ^ 2 - 12 * by₂ p) ^ 2 = 9 * by₁ p ^ 2 - 12 * by₂ p := Real.sq_sqrt hd
  have hs0 : 0 ≤ √(9 * by₁ p ^ 2 - 12 * by₂ p) := Real.sqrt_nonneg _
  obtain ⟨s, hs⟩ : ∃ s, s = √(9 * by₁ p ^ 2 - 12 * by₂ p) := ⟨_, rfl⟩
  rw [← hs] at hss hs0
  have hR : rootT p = -3 * by₁ p + s := by rw [rootT, hs]
  rw [hR]
  -- the other root `T' = -3 y₁ - s ≤ 0`
  have hT' : -3 * by₁ p - s ≤ 0 := by nlinarith [sq_nonneg (3 * by₁ p + s)]
  have hT : 0 < -3 * by₁ p + s := by
    rcases hor with h | h
    · nlinarith
    · linarith
  have hfac : ∀ t, 12 * qY p t = (t - (-3 * by₁ p + s)) * (t - (-3 * by₁ p - s)) := by
    intro t; unfold qY; linear_combination (1 : ℝ) * hss
  refine ⟨hT, ?_, fun t ht htT ↦ ?_, fun t ht ↦ ?_⟩
  · have := hfac (-3 * by₁ p + s); rw [sub_self, zero_mul] at this; linarith
  · have := hfac t
    have : (t - (-3 * by₁ p + s)) * (t - (-3 * by₁ p - s)) < 0 :=
      mul_neg_of_neg_of_pos (by linarith) (by linarith)
    linarith
  · have := hfac t
    have : 0 < (t - (-3 * by₁ p + s)) * (t - (-3 * by₁ p - s)) :=
      mul_pos (by linarith) (by linarith)
    linarith

/-! ### A function that is `≤ 0` to the left of a point -/

/-- A continuous function that is `≤ 0` on `(a, b)` is `≤ 0` at `b`. -/
theorem le_zero_of_nonpos_left {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hf : ContinuousAt f b)
    (h : ∀ t ∈ Ioo a b, f t ≤ 0) : f b ≤ 0 :=
  le_of_tendsto (hf.tendsto.mono_left nhdsWithin_le_nhds)
    (Filter.mem_of_superset (Ioo_mem_nhdsLT hab) h)

/-- A function that is `≤ 0` on `(a, b)` and vanishes at `b` has a nonnegative derivative there. -/
theorem deriv_nonneg_of_nonpos_left {f : ℝ → ℝ} {f' a b : ℝ} (hab : a < b)
    (hf : HasDerivAt f f' b) (hb : f b = 0) (h : ∀ t ∈ Ioo a b, f t ≤ 0) : 0 ≤ f' := by
  have hs := (hasDerivAt_iff_tendsto_slope.1 hf).mono_left
    (nhdsWithin_mono b fun t (ht : t ∈ Iio b) ↦ mem_compl_singleton_iff.2 (ne_of_lt ht))
  refine ge_of_tendsto hs (Filter.mem_of_superset (Ioo_mem_nhdsLT hab) fun t ht ↦ ?_)
  change 0 ≤ slope f b t
  rw [slope_def_field, hb, sub_zero]
  exact div_nonneg_of_nonpos (h t ht) (by linarith [ht.2])

end SmoothedPolygons.TriFuller.CellTwoAnalytic
