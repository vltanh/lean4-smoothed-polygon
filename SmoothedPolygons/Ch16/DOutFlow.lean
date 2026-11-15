module

public import SmoothedPolygons.Ch16.BasinHypotheses
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The Fuller–Poincaré map on `𝒟₀₀`: the exact structure

Exact (non-numerical) facts about the Fuller–Poincaré map `poincareAngZero` on the box
`𝒟₀₀ = 𝒟_out` of cell coordinates `p = (r₂, ψ, θ₂)` (`cellBox 0 0`, TeX 12526–12537), used by the
analytic proofs of `DOutContracts` (`SmoothedPolygons/Ch16/BasinHypotheses.lean`) in
`SmoothedPolygons/Ch16/DOutInvariant.lean`, `DOutImages.lean` and `DOutContraction.lean`. The
statements and proofs are those of the certification step (`DOutMaps`, `ContractionBox`,
`DOutIter` in `SmoothedPolygons/Ch16/Certificates/`), collected here without the interval
certificates so that the analytic proofs import no kernel computation.

* **The flow along `ζ`, rotated by `ζ`** (`zeta_flow`): with `ζ z₁ = x₁ + i y₁ = r₁ e^{iφ₁}`,
  `ζ z₂ = x₂ + i y₂ = r₂ e^{iφ₂}` (`φ₁ = θ₂ - ψ + 2π/3`, `φ₂ = θ₂ + 2π/3`) and
  `κ = r₁ r₂ sin ψ`, the coordinates of `ζ z(t)` are `U_k + i V_k`, polynomial in `t`; the
  switching function of `ζ → 1` is `D = V₂ = -√3 κ + y₂ t + y₁ t²/2 + t³/12`
  (`ham_one_sub_ham_ζ`), that of `ζ → ζ²` is `-√3 Im z₃` (`ham_ζ_sq_sub_ham_ζ`).
* **The switch** (`V₂_mul_sq_lt`, `firstControl_firstSwitchTime`): on `𝒟₀₀`, `y₂ ≤ 0 ≤ κ`, so
  `D(t)/t²` is strictly increasing on `t > 0`; off the face piece `{r₂ = 0, θ₁ ≤ π/3}` the root
  `τ` of `D` exists (`exists_V₂_neg`), the first control is `ζ` and the first switch is `τ`.
* **The image** (`image_spec`): `ζ F(z)` lies on the wall `𝒲₀` with `x₃ < 0` and `V₁ > 0`, and
  the class of the image is the class of the cell coordinates of `w = ζ F(z)`, with
  `w₁ = U₀ + i V₀`, `w₂ = U₁ + i V₁` at `τ`.
* **The face piece** (`cellClass_face`): the `V_T`-equivariance.
* **The cell coordinates of `w` from polynomial conditions**: the angles (`toIcoMod_lt_arctan`,
  `arctan_lt_toIcoMod`, `pi_sub_arctan_lt_arg`, `arg_lt_pi_sub_arctan`) and the radius
  (`cellCoords_zero_mul`: `r₂ |w₁|² = |w₂| (1 - r₂)²`, Lemma 15.1.1).
-/

@[expose] public section

namespace SmoothedPolygons.TriFuller.DOutAnalytic

open Set
open Complex (I)

/-! ### The coefficients and the flow along `ζ` -/

/-- `x₁ = r₁ cos φ₁`, with `r₁ = 1 - r₂` and `φ₁ = θ₂ - ψ + 2π/3`. -/
noncomputable def cx₁ (p : Fin 3 → ℝ) : ℝ := (1 - p 0) * Real.cos (p 2 - p 1 + 2 / 3 * Real.pi)

/-- `y₁ = r₁ sin φ₁`. -/
noncomputable def cy₁ (p : Fin 3 → ℝ) : ℝ := (1 - p 0) * Real.sin (p 2 - p 1 + 2 / 3 * Real.pi)

/-- `x₂ = r₂ cos φ₂`, `φ₂ = θ₂ + 2π/3`. -/
noncomputable def cx₂ (p : Fin 3 → ℝ) : ℝ := p 0 * Real.cos (p 2 + 2 / 3 * Real.pi)

/-- `y₂ = r₂ sin φ₂`. -/
noncomputable def cy₂ (p : Fin 3 → ℝ) : ℝ := p 0 * Real.sin (p 2 + 2 / 3 * Real.pi)

/-- `κ = r₁ r₂ sin ψ`. -/
noncomputable def cκ (p : Fin 3 → ℝ) : ℝ := (1 - p 0) * p 0 * Real.sin (p 1)

/-- `U₀ = x₁ - √3 t/2` (`Re (ζ z₁(t))`). -/
noncomputable def U₀ (p : Fin 3 → ℝ) (t : ℝ) : ℝ := cx₁ p - √3 / 2 * t

/-- `V₀ = y₁ + t/2`. -/
noncomputable def V₀ (p : Fin 3 → ℝ) (t : ℝ) : ℝ := cy₁ p + t / 2

/-- `U₁ = x₂ + x₁ t - √3 t²/4`. -/
noncomputable def U₁ (p : Fin 3 → ℝ) (t : ℝ) : ℝ := cx₂ p + cx₁ p * t - √3 / 4 * t ^ 2

/-- `V₁ = y₂ + y₁ t + t²/4`. -/
noncomputable def V₁ (p : Fin 3 → ℝ) (t : ℝ) : ℝ := cy₂ p + cy₁ p * t + t ^ 2 / 4

/-- `U₂ = κ + x₂ t + x₁ t²/2 - √3 t³/12`. -/
noncomputable def U₂ (p : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  cκ p + cx₂ p * t + cx₁ p * t ^ 2 / 2 - √3 / 12 * t ^ 3

/-- `V₂ = -√3 κ + y₂ t + y₁ t²/2 + t³/12`: the switching function `D`. -/
noncomputable def V₂ (p : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  -(√3 * cκ p) + cy₂ p * t + cy₁ p * t ^ 2 / 2 + t ^ 3 / 12

/-! ### The Fuller flow along the control `ζ`, rotated by `ζ` -/

theorem cos_two_thirds_pi : Real.cos (2 / 3 * Real.pi) = -1 / 2 := by
  rw [show 2 / 3 * Real.pi = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]
  norm_num

theorem sin_two_thirds_pi : Real.sin (2 / 3 * Real.pi) = √3 / 2 := by
  rw [show 2 / 3 * Real.pi = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub, Real.sin_pi_div_three]

theorem cellPoint_reim (p : Fin 3 → ℝ) :
    (cellPoint p 0).re = (1 - p 0) * Real.cos (p 2 - p 1) ∧
    (cellPoint p 0).im = (1 - p 0) * Real.sin (p 2 - p 1) ∧
    (cellPoint p 1).re = p 0 * Real.cos (p 2) ∧
    (cellPoint p 1).im = p 0 * Real.sin (p 2) ∧
    (cellPoint p 2).re = -2 * (1 - p 0) * p 0 * Real.sin (p 1) ∧
    (cellPoint p 2).im = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [cellPoint, Matrix.cons_val_zero, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  · simp only [cellPoint, Matrix.cons_val_zero, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  · simp only [cellPoint, Matrix.cons_val_one, Matrix.cons_val_zero, Complex.re_ofReal_mul,
      Complex.exp_ofReal_mul_I_re]
  · simp only [cellPoint, Matrix.cons_val_one, Matrix.cons_val_zero, Complex.im_ofReal_mul,
      Complex.exp_ofReal_mul_I_im]
  · exact Complex.ofReal_re _
  · exact Complex.ofReal_im _

theorem zeta_flow (p : Fin 3 → ℝ) (t : ℝ) :
    (ζ * flow t (cellPoint p) ζ 0).re = U₀ p t ∧ (ζ * flow t (cellPoint p) ζ 0).im = V₀ p t ∧
    (ζ * flow t (cellPoint p) ζ 1).re = U₁ p t ∧ (ζ * flow t (cellPoint p) ζ 1).im = V₁ p t ∧
    (ζ * flow t (cellPoint p) ζ 2).re = U₂ p t ∧ (ζ * flow t (cellPoint p) ζ 2).im = V₂ p t := by
  obtain ⟨c0, c1, c2, c3, c4, c5⟩ := cellPoint_reim p
  have hs3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have e1 : Real.cos (p 2 - p 1 + 2 / 3 * Real.pi) =
      Real.cos (p 2 - p 1) * (-1 / 2) - Real.sin (p 2 - p 1) * (√3 / 2) := by
    rw [Real.cos_add, cos_two_thirds_pi, sin_two_thirds_pi]
  have e2 : Real.sin (p 2 - p 1 + 2 / 3 * Real.pi) =
      Real.sin (p 2 - p 1) * (-1 / 2) + Real.cos (p 2 - p 1) * (√3 / 2) := by
    rw [Real.sin_add, cos_two_thirds_pi, sin_two_thirds_pi]
  have e3 : Real.cos (p 2 + 2 / 3 * Real.pi) =
      Real.cos (p 2) * (-1 / 2) - Real.sin (p 2) * (√3 / 2) := by
    rw [Real.cos_add, cos_two_thirds_pi, sin_two_thirds_pi]
  have e4 : Real.sin (p 2 + 2 / 3 * Real.pi) =
      Real.sin (p 2) * (-1 / 2) + Real.cos (p 2) * (√3 / 2) := by
    rw [Real.sin_add, cos_two_thirds_pi, sin_two_thirds_pi]
  have f0 : flow t (cellPoint p) ζ 0 = cellPoint p 0 - I * t * ζ := rfl
  have f1 : flow t (cellPoint p) ζ 1 = cellPoint p 1 + cellPoint p 0 * t - I * t ^ 2 * ζ / 2 := rfl
  have f2 : flow t (cellPoint p) ζ 2 =
      cellPoint p 2 + cellPoint p 1 * t + cellPoint p 0 * t ^ 2 / 2 - I * t ^ 3 * ζ / 6 := rfl
  rw [f0, f1, f2]
  simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.div_re, Complex.div_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, ζ_re, ζ_im, c0, c1, c2, c3, c4, c5, U₀, V₀, U₁, V₁, U₂,
    V₂, cx₁, cy₁, cx₂, cy₂, cκ, e1, e2, e3, e4]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals norm_num
  all_goals ring_nf
  all_goals (try simp only [hs3])
  all_goals ring_nf

/-- The imaginary part `Y₂ = r₂ sin θ₂ t + r₁ sin θ₁ t²/2 + t³/12` of `z₃(t)`. -/
theorem flow_two_im (p : Fin 3 → ℝ) (t : ℝ) :
    (flow t (cellPoint p) ζ 2).im = p 0 * Real.sin (p 2) * t +
      (1 - p 0) * Real.sin (p 2 - p 1) * t ^ 2 / 2 + t ^ 3 / 12 := by
  obtain ⟨c0, c1, c2, c3, c4, c5⟩ := cellPoint_reim p
  have f2 : flow t (cellPoint p) ζ 2 =
      cellPoint p 2 + cellPoint p 1 * t + cellPoint p 0 * t ^ 2 / 2 - Complex.I * t ^ 3 * ζ / 6 :=
    rfl
  rw [f2]
  simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.mul_im, Complex.sub_im, Complex.add_im,
    Complex.div_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, ζ_re, ζ_im, c0, c1, c2, c3, c5]
  norm_num
  ring

/-- The Hamiltonian gain of the control `1` over `ζ` along the control `ζ`:
`H_F(z(t), 1) - H_F(z(t), ζ) = √3 V₂`. -/
theorem ham_one_sub_ham_ζ (p : Fin 3 → ℝ) (t : ℝ) :
    ham (flow t (cellPoint p) ζ) 1 - ham (flow t (cellPoint p) ζ) ζ = √3 * V₂ p t := by
  obtain ⟨-, -, -, -, -, h⟩ := zeta_flow p t
  rw [← h]
  have hs3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [ham, RR_eq_re_mul_add_im_mul, Complex.mul_im, ζ_re, ζ_im, Complex.one_re,
    Complex.one_im]
  ring_nf
  rw [hs3]
  ring

/-- The gain of `ζ²` over `ζ`: `H_F(z(t), ζ²) - H_F(z(t), ζ) = -√3 Y₂`. -/
theorem ham_ζ_sq_sub_ham_ζ (p : Fin 3 → ℝ) (t : ℝ) :
    ham (flow t (cellPoint p) ζ) (ζ ^ 2) - ham (flow t (cellPoint p) ζ) ζ =
      -(√3 * (flow t (cellPoint p) ζ 2).im) := by
  simp only [ham, RR_eq_re_mul_add_im_mul, ζ_re, ζ_im, ζ_sq_re, ζ_sq_im]
  ring


theorem arg_eq_arctan_add_pi {z : ℂ} (hre : z.re < 0) (him : 0 ≤ z.im) :
    Complex.arg z = Real.arctan (z.im / z.re) + Real.pi := by
  have h1 : Real.pi / 2 < Complex.arg z := by
    have hn : ¬ |Complex.arg z| ≤ Real.pi / 2 := fun h ↦
      (not_le.2 hre) (Complex.abs_arg_le_pi_div_two_iff.1 h)
    push Not at hn
    rwa [abs_of_nonneg (Complex.arg_nonneg_iff.2 him)] at hn
  have h2 := Complex.arg_le_pi z
  have ht : Real.tan (Complex.arg z - Real.pi) = z.im / z.re := by
    rw [Real.tan_periodic.sub_eq, Complex.tan_arg]
  have := Real.arctan_tan (x := Complex.arg z - Real.pi) (by linarith) (by linarith)
  rw [ht] at this
  linarith

theorem norm_eq_sqrt (z : ℂ) : ‖z‖ = √(z.re ^ 2 + z.im ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_apply]; ring_nf


/-! ### The switching cubic on `𝒟₀₀` -/

section Cubic

variable {p : Fin 3 → ℝ}

/-- `D(t)/t²` is strictly increasing when `y₂ ≤ 0 ≤ κ` (one sign change of the coefficients). -/
theorem V₂_mul_sq_lt (hy : cy₂ p ≤ 0) (hk : 0 ≤ cκ p) {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    V₂ p s * t ^ 2 < V₂ p t * s ^ 2 := by
  have e : V₂ p t * s ^ 2 - V₂ p s * t ^ 2 =
      (t - s) * (√3 * cκ p * (t + s) - cy₂ p * s * t + s ^ 2 * t ^ 2 / 12) := by
    unfold V₂; ring
  have h3 : 0 ≤ √3 := Real.sqrt_nonneg 3
  have ht : 0 < t := hs.trans hst
  have : 0 < (t - s) * (√3 * cκ p * (t + s) - cy₂ p * s * t + s ^ 2 * t ^ 2 / 12) := by
    apply mul_pos (by linarith)
    have : 0 ≤ √3 * cκ p * (t + s) := by positivity
    have : 0 ≤ -cy₂ p * s * t := by
      have := mul_pos hs ht
      nlinarith
    have : 0 < s ^ 2 * t ^ 2 / 12 := by positivity
    linarith
  linarith

theorem V₂_pos_of_nonneg (hy : cy₂ p ≤ 0) (hk : 0 ≤ cκ p) {s t : ℝ} (hs : 0 < s) (hst : s < t)
    (h : 0 ≤ V₂ p s) : 0 < V₂ p t := by
  have := V₂_mul_sq_lt hy hk hs hst
  have h2 : 0 ≤ V₂ p s * t ^ 2 := mul_nonneg h (sq_nonneg t)
  have hs2 : 0 < s ^ 2 := by positivity
  by_contra hc
  push Not at hc
  nlinarith

theorem V₂_neg_of_nonpos (hy : cy₂ p ≤ 0) (hk : 0 ≤ cκ p) {s t : ℝ} (hs : 0 < s) (hst : s < t)
    (h : V₂ p t ≤ 0) : V₂ p s < 0 := by
  by_contra hc
  push Not at hc
  linarith [V₂_pos_of_nonneg hy hk hs hst hc]

/-- At a positive root of `D`, `V₁ = Im ζ z₂ = D'` is positive:
`τ V₁(τ) = τ³/12 - y₂ τ + 2√3 κ`. -/
theorem V₁_pos_of_root (hy : cy₂ p ≤ 0) (hk : 0 ≤ cκ p) {τ : ℝ} (hτ : 0 < τ)
    (h0 : V₂ p τ = 0) : 0 < V₁ p τ := by
  have e : τ * V₁ p τ = τ ^ 3 / 12 - cy₂ p * τ + 2 * (√3 * cκ p) + 2 * V₂ p τ := by
    unfold V₁ V₂; ring
  rw [h0, mul_zero, add_zero] at e
  have : 0 ≤ √3 * cκ p := mul_nonneg (Real.sqrt_nonneg 3) hk
  have : 0 < τ ^ 3 / 12 := by positivity
  have : 0 ≤ -cy₂ p * τ := mul_nonneg (by linarith) hτ.le
  have : 0 < τ * V₁ p τ := by linarith
  exact pos_of_mul_pos_right this hτ.le

/-- `Im z₃(t) = -(√3/2) U₂ - V₂/2` (`ζ z₃ = U₂ + i V₂`, `z₃ = ζ² (ζ z₃)`). -/
theorem flow_two_im_eq (t : ℝ) :
    (flow t (cellPoint p) ζ 2).im = -(√3 / 2) * U₂ p t - V₂ p t / 2 := by
  obtain ⟨-, -, -, -, e1, e2⟩ := zeta_flow p t
  have e : flow t (cellPoint p) ζ 2 = ζ ^ 2 * (ζ * flow t (cellPoint p) ζ 2) := by
    rw [← mul_assoc, ← pow_succ, ζ_pow_three, one_mul]
  rw [e, Complex.mul_im, e1, e2, ζ_sq_re, ζ_sq_im]
  ring

end Cubic

/-! ### The angles of the image -/

/-- `arg w ≥ 2π/3` when `Im w > 0` and `Im w + √3 Re w < 0`. -/
theorem two_pi_div_three_lt_arg {w : ℂ} (h1 : 0 < w.im) (h2 : w.im + √3 * w.re < 0) :
    2 * Real.pi / 3 < Complex.arg w := by
  have h3 : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  have hre : w.re < 0 := by nlinarith
  rw [arg_eq_arctan_add_pi hre h1.le]
  have hq : -√3 < w.im / w.re := by
    rw [lt_div_iff_of_neg hre]; linarith
  have harc : Real.arctan (√3) = Real.pi / 3 := by
    rw [← Real.tan_pi_div_three, Real.arctan_tan (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])]
  have := Real.arctan_strictMono hq
  rw [Real.arctan_neg, harc] at this
  linarith

/-- `ψ' < π/3` for the angle `ψ' ∈ (0, π)` from `w₀` to `w₁` when
`(Re w₀ Im w₁ - Im w₀ Re w₁) - √3 (Re w₀ Re w₁ + Im w₀ Im w₁) < 0`. -/
theorem toIcoMod_lt_pi_div_three {w₀ w₁ : ℂ}
    (hψ : toIcoMod Real.two_pi_pos 0 (Complex.arg w₁ - Complex.arg w₀) ∈ Ioo 0 Real.pi)
    (h : w₀.re * (w₁.im - √3 * w₁.re) - w₀.im * (w₁.re + √3 * w₁.im) < 0) :
    toIcoMod Real.two_pi_pos 0 (Complex.arg w₁ - Complex.arg w₀) < Real.pi / 3 := by
  set ψ := toIcoMod Real.two_pi_pos 0 (Complex.arg w₁ - Complex.arg w₀) with hψdef
  have hw₀ : w₀ ≠ 0 := by
    rintro rfl; simp at h
  have hw₁ : w₁ ≠ 0 := by
    rintro rfl; simp at h
  have e : ψ = Complex.arg w₁ - Complex.arg w₀ -
      (toIcoDiv Real.two_pi_pos 0 (Complex.arg w₁ - Complex.arg w₀) : ℝ) * (2 * Real.pi) := by
    rw [hψdef, ← zsmul_eq_mul]
    exact eq_sub_of_add_eq (toIcoMod_add_toIcoDiv_zsmul _ _ _)
  have hs : Real.sin ψ = Real.sin (Complex.arg w₁ - Complex.arg w₀) := by
    rw [e, Real.sin_sub_int_mul_two_pi]
  have hc : Real.cos ψ = Real.cos (Complex.arg w₁ - Complex.arg w₀) := by
    rw [e, Real.cos_sub_int_mul_two_pi]
  have n0 : 0 < ‖w₀‖ := norm_pos_iff.2 hw₀
  have n1 : 0 < ‖w₁‖ := norm_pos_iff.2 hw₁
  have key : Real.sin ψ - √3 * Real.cos ψ < 0 := by
    rw [hs, hc, Real.sin_sub, Real.cos_sub, Complex.sin_arg, Complex.sin_arg,
      Complex.cos_arg hw₀, Complex.cos_arg hw₁]
    have e2 : w₁.im / ‖w₁‖ * (w₀.re / ‖w₀‖) - w₁.re / ‖w₁‖ * (w₀.im / ‖w₀‖) -
        √3 * (w₁.re / ‖w₁‖ * (w₀.re / ‖w₀‖) + w₁.im / ‖w₁‖ * (w₀.im / ‖w₀‖)) =
        (w₀.re * (w₁.im - √3 * w₁.re) - w₀.im * (w₁.re + √3 * w₁.im)) / (‖w₀‖ * ‖w₁‖) := by
      field_simp
      ring
    rw [e2]
    exact div_neg_of_neg_of_pos h (mul_pos n0 n1)
  by_contra hge
  push Not at hge
  have hpos : 0 ≤ Real.sin (ψ - Real.pi / 3) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hψ.2])
  rw [Real.sin_sub, Real.cos_pi_div_three, Real.sin_pi_div_three] at hpos
  linarith

theorem mem_cellBox_zero_zero {p : Fin 3 → ℝ} : p ∈ cellBox 0 0 ↔
    p 0 ∈ Icc 0 1 ∧ p 1 ∈ Icc 0 (Real.pi / 3) ∧ p 2 ∈ Icc (Real.pi - 1.1) Real.pi := by
  simp [cellBox, basinA, basinB]

/-- The signs on `𝒟₀₀`: `y₂ ≤ 0 ≤ κ`, `sin θ₂ ≥ 0`, `sin θ₁ ≥ 0`. -/
theorem cellBox_facts {p : Fin 3 → ℝ} (hp : p ∈ cellBox 0 0) :
    cy₂ p ≤ 0 ∧ 0 ≤ cκ p ∧ 0 ≤ Real.sin (p 2) ∧ 0 ≤ Real.sin (p 2 - p 1) ∧ p ∈ cellDomain := by
  obtain ⟨⟨h0, h0'⟩, ⟨h1, h1'⟩, ⟨h2, h2'⟩⟩ := mem_cellBox_zero_zero.1 hp
  have hpi := Real.pi_gt_three
  refine ⟨?_, ?_, Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) h2',
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith), ⟨⟨h0, h0'⟩,
      ⟨h1, by linarith⟩, ⟨by linarith, h2'⟩⟩⟩
  · have : 0 ≤ Real.sin (p 2 + 2 / 3 * Real.pi - Real.pi) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    rw [Real.sin_sub_pi] at this
    unfold cy₂
    nlinarith
  · unfold cκ
    have := Real.sin_nonneg_of_nonneg_of_le_pi h1 (by linarith)
    have : 0 ≤ 1 - p 0 := by linarith
    positivity

/-- Off the face piece `r₂ = 0, θ₁ ≤ π/3`, the switching cubic is negative somewhere on
`t > 0`. -/
theorem exists_V₂_neg {p : Fin 3 → ℝ} (hp : p ∈ cellBox 0 0)
    (hB : ¬(p 0 = 0 ∧ p 2 - p 1 ≤ Real.pi / 3)) : ∃ s, 0 < s ∧ V₂ p s < 0 := by
  obtain ⟨⟨h0, h0'⟩, ⟨h1, h1'⟩, ⟨h2, h2'⟩⟩ := mem_cellBox_zero_zero.1 hp
  obtain ⟨hy, hk, -, -, -⟩ := cellBox_facts hp
  have hpi := Real.pi_gt_three
  have h3 : 0 ≤ √3 := Real.sqrt_nonneg 3
  have hy1 : |cy₁ p| ≤ 1 := by
    unfold cy₁
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - p 0)]
    have := Real.abs_sin_le_one (p 2 - p 1 + 2 / 3 * Real.pi)
    nlinarith [abs_nonneg (Real.sin (p 2 - p 1 + 2 / 3 * Real.pi))]
  rcases h0.lt_or_eq with h0 | h0
  · -- `r₂ > 0`: `y₂ < 0`
    have hs : 0 < Real.sin (p 2 + 2 / 3 * Real.pi - Real.pi) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    rw [Real.sin_sub_pi] at hs
    have hy' : cy₂ p < 0 := by unfold cy₂; nlinarith
    refine ⟨min 1 (-cy₂ p), lt_min one_pos (by linarith), ?_⟩
    set s := min 1 (-cy₂ p)
    have hs1 : s ≤ 1 := min_le_left _ _
    have hs2 : s ≤ -cy₂ p := min_le_right _ _
    have hs0 : 0 < s := lt_min one_pos (by linarith)
    have e1 : cy₁ p * s ^ 2 / 2 ≤ s ^ 2 / 2 := by
      have := (abs_le.1 hy1).2
      nlinarith [sq_nonneg s]
    have e2 : s ^ 3 / 12 ≤ s ^ 2 / 12 := by nlinarith [sq_nonneg s]
    have e3 : 0 ≤ √3 * cκ p := mul_nonneg h3 hk
    have e4 : s ^ 2 * (7 / 12) + cy₂ p * s ≤ s * (5 / 12 * cy₂ p) := by nlinarith
    unfold V₂
    nlinarith
  · -- `r₂ = 0`: `θ₁ > π/3`, `y₁ < 0`
    have hθ : Real.pi / 3 < p 2 - p 1 := by
      by_contra hc; push Not at hc; exact hB ⟨h0.symm, hc⟩
    have hs : 0 < Real.sin (p 2 - p 1 + 2 / 3 * Real.pi - Real.pi) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    rw [Real.sin_sub_pi] at hs
    have hy1' : cy₁ p < 0 := by unfold cy₁; rw [← h0]; linarith
    have e0 : cy₂ p = 0 := by unfold cy₂; rw [← h0]; ring
    have ek : cκ p = 0 := by unfold cκ; rw [← h0]; ring
    refine ⟨-3 * cy₁ p, by linarith, ?_⟩
    have e : V₂ p (-3 * cy₁ p) = 9 / 4 * cy₁ p ^ 3 := by unfold V₂; rw [e0, ek]; ring
    rw [e]
    have : cy₁ p ^ 3 < 0 := Odd.pow_neg ⟨1, by norm_num⟩ hy1'
    linarith

/-- The first control is `ζ` and the first switch is at the root `τ` of `D`, when `D < 0` on
`(0, τ)`, `D > 0` on `(τ, ∞)` and `Im z₃(t) > 0` for `t > 0` (the control `1` beats `ζ` exactly
when `D > 0`, `ham_one_sub_ham_ζ`, and `ζ²` never does, `ham_ζ_sq_sub_ham_ζ`). -/
theorem firstControl_firstSwitchTime {p : Fin 3 → ℝ} (hz : cellPoint p ≠ 0) (hk : 0 ≤ cκ p)
    (hY : ∀ t, 0 < t → 0 < (flow t (cellPoint p) ζ 2).im) {τ : ℝ} (hτ : 0 < τ)
    (hneg : ∀ t, 0 < t → t < τ → V₂ p t < 0) (hpos : ∀ t, τ < t → 0 < V₂ p t)
    (h0 : V₂ p τ = 0) : firstControl (cellPoint p) = ζ ∧ firstSwitchTime (cellPoint p) = τ := by
  have hs3 : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  have hY0 : 0 ≤ (flow 0 (cellPoint p) ζ 2).im := by rw [flow_two_im]; simp
  -- `ζ` maximizes on `[0, τ]`
  have hfc : firstControl (cellPoint p) = ζ := by
    refine (firstControl_eq_iff hz).2 ⟨ζ_mem_VT, τ, hτ, fun t ht v hv ↦ ?_⟩
    have hD : V₂ p t ≤ 0 := by
      rcases ht.1.lt_or_eq with h | h
      · rcases ht.2.lt_or_eq with h' | h'
        · exact (hneg t h h').le
        · rw [h', h0]
      · have e : V₂ p 0 = -(√3 * cκ p) := by unfold V₂; ring
        rw [← h, e]
        linarith [mul_nonneg (Real.sqrt_nonneg 3) hk]
    have hYt : 0 ≤ (flow t (cellPoint p) ζ 2).im := by
      rcases ht.1.lt_or_eq with h | h
      · exact (hY t h).le
      · rw [← h]; exact hY0
    rcases mem_VT.1 hv with rfl | rfl | rfl
    · have := ham_one_sub_ham_ζ p t
      nlinarith
    · exact le_rfl
    · have := ham_ζ_sq_sub_ham_ζ p t
      nlinarith
  refine ⟨hfc, ?_⟩
  -- the beaten times are the times with `D > 0`
  have key : ∀ t, 0 < t → ((∃ v ∈ VT, ham (flow t (cellPoint p) ζ) ζ <
      ham (flow t (cellPoint p) ζ) v) ↔ 0 < V₂ p t) := by
    intro t ht
    constructor
    · rintro ⟨v, hv, hlt⟩
      rcases mem_VT.1 hv with rfl | rfl | rfl
      · have := ham_one_sub_ham_ζ p t
        by_contra hc
        push Not at hc
        nlinarith
      · exact absurd hlt (lt_irrefl _)
      · have := ham_ζ_sq_sub_ham_ζ p t
        have hy := hY t ht
        nlinarith
    · intro hD
      refine ⟨1, one_mem_VT, ?_⟩
      have := ham_one_sub_ham_ζ p t
      nlinarith [mul_pos hs3 hD]
  unfold firstSwitchTime
  rw [hfc]
  apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
  · exact ⟨τ + 1, by linarith, (key _ (by linarith)).2 (hpos _ (by linarith))⟩
  · rintro a ⟨ha, hbeat⟩
    have hD := (key a ha).1 hbeat
    by_contra hlt
    push Not at hlt
    linarith [hneg a ha hlt]
  · intro w hw
    exact ⟨(τ + w) / 2, ⟨by linarith, (key _ (by linarith)).2 (hpos _ (by linarith))⟩,
      by linarith⟩

/-- **The image of a point of `𝒟₀₀` at a positive root `τ` of `D`** (the switching cubic of
`ζ → 1`): `D < 0` on `(0, τ)` and `D > 0` after `τ` (`V₂_mul_sq_lt`), `Im z₃ > 0`, so the first
control is `ζ` and the first switch is at `τ` (`firstControl_firstSwitchTime`); the rotated image
`w = ζ F(z)` has `ζ z₁(τ) = U₀ + i V₀`, `ζ z₂(τ) = U₁ + i V₁` with `V₁ > 0`, lies on the wall
`𝒲₀` with `x₃ < 0`, and the class of `p`'s image is the class of the cell coordinates of `w`. (A
point of the face piece `r₂ = 0, θ₁ ≤ π/3` has no positive root.) -/
theorem image_spec {p : Fin 3 → ℝ} (hp : p ∈ cellBox 0 0) {τ : ℝ} (hτ0 : 0 < τ)
    (h0 : V₂ p τ = 0) :
    0 < V₁ p τ ∧ ∃ w : Fin 3 → ℂ, w = ζ • poincare (cellPoint p) ∧
      poincareAngZero (cellClass p) = cellClass (cellCoords w) ∧
      (w 0).re = U₀ p τ ∧ (w 0).im = V₀ p τ ∧ (w 1).re = U₁ p τ ∧ (w 1).im = V₁ p τ ∧
      cellCoords w 0 ∈ Ioo 0 1 ∧
      toIcoMod Real.two_pi_pos 0 (Complex.arg (w 1) - Complex.arg (w 0)) ∈ Ioo 0 Real.pi ∧
      cellCoords w 1 = toIcoMod Real.two_pi_pos 0 (Complex.arg (w 1) - Complex.arg (w 0)) ∧
      cellCoords w 2 = Complex.arg (w 1) := by
  obtain ⟨hy, hk, hs2, hs21, hdom⟩ := cellBox_facts hp
  obtain ⟨hr, -, -⟩ := mem_cellBox_zero_zero.1 hp
  have hs3 : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  have hneg : ∀ t, 0 < t → t < τ → V₂ p t < 0 := fun t ht htτ ↦
    V₂_neg_of_nonpos hy hk ht htτ h0.le
  have hpos : ∀ t, τ < t → 0 < V₂ p t := fun t htτ ↦ V₂_pos_of_nonneg hy hk hτ0 htτ h0.ge
  -- the first control and the first switch
  have hY : ∀ t, 0 < t → 0 < (flow t (cellPoint p) ζ 2).im := by
    intro t ht
    rw [flow_two_im]
    have : 0 ≤ 1 - p 0 := by linarith [hr.2]
    have : 0 ≤ p 0 * Real.sin (p 2) * t := by have := hr.1; positivity
    have : 0 ≤ (1 - p 0) * Real.sin (p 2 - p 1) * t ^ 2 / 2 := by positivity
    have : 0 < t ^ 3 / 12 := by positivity
    linarith
  have hz := cellPoint_mem_sectionZero hdom
  obtain ⟨hfc, hτe⟩ := firstControl_firstSwitchTime hz.1 hk hY hτ0 hneg hpos h0
  have hw := poincare_mem_sectionZero hz
  have hpw : poincare (cellPoint p) = flow τ (cellPoint p) ζ := by rw [poincare, hfc, hτe]
  obtain ⟨e0r, e0i, e1r, e1i, e2r, e2i⟩ := zeta_flow p τ
  have hV₁ := V₁_pos_of_root hy hk hτ0 h0
  have hU₂ : U₂ p τ < 0 := by
    have e := flow_two_im_eq (p := p) τ
    rw [h0] at e
    have := hY τ hτ0
    nlinarith
  -- the rotated image `w = ζ F(z)`, on the wall `𝒲₀`
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
  have hw0 : w 0 = ζ * flow τ (cellPoint p) ζ 0 := by
    rw [hw_def, Pi.smul_apply, smul_eq_mul, hpw]
  have hw1 : w 1 = ζ * flow τ (cellPoint p) ζ 1 := by
    rw [hw_def, Pi.smul_apply, smul_eq_mul, hpw]
  have hw2 : w 2 = ζ * flow τ (cellPoint p) ζ 2 := by
    rw [hw_def, Pi.smul_apply, smul_eq_mul, hpw]
  have him : (w 2).im = 0 := by rw [hw2, e2i, h0]
  have hre : (w 2).re < 0 := by rw [hw2, e2r]; exact hU₂
  obtain ⟨⟨c0, c1, -⟩, hcl⟩ := cellClass_cellCoords hζw him hre
  have hcls := classOf_smul_scale ζ_mem_VT one_pos hw
  rw [scale_one] at hcls
  have himage : poincareAngZero (cellClass p) = cellClass (cellCoords w) := by
    change poincareAngZero (classOf (cellPoint p)) = _
    rw [poincareAngZero_classOf hz, hcl, hw_def, hcls]
  exact ⟨hV₁, w, hw_def, himage, by rw [hw0, e0r], by rw [hw0, e0i], by rw [hw1, e1r],
    by rw [hw1, e1i], c0, c1, rfl, rfl⟩

/-- On the face piece `r₂ = 0`, `θ₁ = θ₂ - ψ ≤ π/3` (first control `1`), the point
`(e^{iθ₁}, 0, 0)` has the same class as its rotation `ζ (e^{iθ₁}, 0, 0) = (e^{i(θ₁ + 2π/3)}, 0, 0)`
(the `V_T`-equivariance), the cell point `(0, 0, θ₁ + 2π/3)` of `𝒟₀₀`. -/
theorem cellClass_face {p : Fin 3 → ℝ} (hp : p ∈ cellBox 0 0) (h0 : p 0 = 0) :
    cellClass p = cellClass ![0, 0, p 2 - p 1 + 2 * Real.pi / 3] := by
  obtain ⟨-, -, -, -, hdom⟩ := cellBox_facts hp
  have hz := cellPoint_mem_sectionZero hdom
  have e : cellPoint ![0, 0, p 2 - p 1 + 2 * Real.pi / 3] = ζ • scale 1 (cellPoint p) := by
    rw [scale_one]
    funext j
    fin_cases j
    · simp only [cellPoint, Pi.smul_apply, smul_eq_mul, h0, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
        Fin.zero_eta]
      rw [ζ, sub_zero, Complex.ofReal_one, one_mul, one_mul, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    · simp [cellPoint, h0]
    · simp [cellPoint, h0]
  rw [cellClass, cellClass, e, classOf_smul_scale ζ_mem_VT one_pos hz]



/-! ### The angles -/

/-- The angle `ψ ∈ [0, 2π)` from `w₀` to `w₁`: `|w₀| |w₁| sin ψ = Im (w̄₀ w₁)`,
`|w₀| |w₁| cos ψ = Re (w̄₀ w₁)`. -/
theorem sin_cos_toIcoMod {w₀ w₁ : ℂ} (hw₀ : w₀ ≠ 0) (hw₁ : w₁ ≠ 0) :
    Real.sin (toIcoMod Real.two_pi_pos 0 (Complex.arg w₁ - Complex.arg w₀)) * (‖w₀‖ * ‖w₁‖) =
      w₀.re * w₁.im - w₀.im * w₁.re ∧
    Real.cos (toIcoMod Real.two_pi_pos 0 (Complex.arg w₁ - Complex.arg w₀)) * (‖w₀‖ * ‖w₁‖) =
      w₀.re * w₁.re + w₀.im * w₁.im := by
  set ψ := toIcoMod Real.two_pi_pos 0 (Complex.arg w₁ - Complex.arg w₀) with hψdef
  have e : ψ = Complex.arg w₁ - Complex.arg w₀ -
      (toIcoDiv Real.two_pi_pos 0 (Complex.arg w₁ - Complex.arg w₀) : ℝ) * (2 * Real.pi) := by
    rw [hψdef, ← zsmul_eq_mul]
    exact eq_sub_of_add_eq (toIcoMod_add_toIcoDiv_zsmul _ _ _)
  have hs : Real.sin ψ = Real.sin (Complex.arg w₁ - Complex.arg w₀) := by
    rw [e, Real.sin_sub_int_mul_two_pi]
  have hc : Real.cos ψ = Real.cos (Complex.arg w₁ - Complex.arg w₀) := by
    rw [e, Real.cos_sub_int_mul_two_pi]
  have n0 : 0 < ‖w₀‖ := norm_pos_iff.2 hw₀
  have n1 : 0 < ‖w₁‖ := norm_pos_iff.2 hw₁
  rw [hs, hc, Real.sin_sub, Real.cos_sub, Complex.sin_arg, Complex.sin_arg, Complex.cos_arg hw₀,
    Complex.cos_arg hw₁]
  constructor
  · field_simp
  · field_simp

/-- `ψ < arctan T` for the angle `ψ ∈ (0, π)` from `w₀` to `w₁` when `B - T A < 0`, `T > 0`
(`A + i B = w̄₀ w₁`); then also `cos ψ > 0`. -/
theorem toIcoMod_lt_arctan {w₀ w₁ : ℂ} {T : ℝ} (hT : 0 < T)
    (hψ : toIcoMod Real.two_pi_pos 0 (Complex.arg w₁ - Complex.arg w₀) ∈ Ioo 0 Real.pi)
    (h : (w₀.re * w₁.im - w₀.im * w₁.re) - T * (w₀.re * w₁.re + w₀.im * w₁.im) < 0) :
    toIcoMod Real.two_pi_pos 0 (Complex.arg w₁ - Complex.arg w₀) < Real.arctan T ∧
      0 < Real.cos (toIcoMod Real.two_pi_pos 0 (Complex.arg w₁ - Complex.arg w₀)) := by
  set ψ := toIcoMod Real.two_pi_pos 0 (Complex.arg w₁ - Complex.arg w₀) with hψdef
  have hw₀ : w₀ ≠ 0 := by rintro rfl; simp at h
  have hw₁ : w₁ ≠ 0 := by rintro rfl; simp at h
  obtain ⟨es, ec⟩ := sin_cos_toIcoMod hw₀ hw₁
  rw [← hψdef] at es ec
  have hN : 0 < ‖w₀‖ * ‖w₁‖ := mul_pos (norm_pos_iff.2 hw₀) (norm_pos_iff.2 hw₁)
  have hsin : 0 < Real.sin ψ := Real.sin_pos_of_pos_of_lt_pi hψ.1 hψ.2
  have key : Real.sin ψ < T * Real.cos ψ := by
    rw [← es, ← ec] at h
    nlinarith
  have hcos : 0 < Real.cos ψ := by
    by_contra hc
    push Not at hc
    nlinarith
  have hψ2 : ψ < Real.pi / 2 := by
    by_contra hc
    push Not at hc
    linarith [Real.cos_nonpos_of_pi_div_two_le_of_le hc (by linarith [hψ.2])]
  have htan : Real.tan ψ < T := by
    rw [Real.tan_eq_sin_div_cos, div_lt_iff₀ hcos]; linarith
  refine ⟨?_, hcos⟩
  have := Real.arctan_strictMono htan
  rwa [Real.arctan_tan (by linarith [hψ.1]) hψ2] at this

/-- `ψ > arctan T` when `T A - B < 0` and `cos ψ > 0`. -/
theorem arctan_lt_toIcoMod {w₀ w₁ : ℂ} {T : ℝ}
    (hψ : toIcoMod Real.two_pi_pos 0 (Complex.arg w₁ - Complex.arg w₀) ∈ Ioo 0 Real.pi)
    (hcos : 0 < Real.cos (toIcoMod Real.two_pi_pos 0 (Complex.arg w₁ - Complex.arg w₀)))
    (h : T * (w₀.re * w₁.re + w₀.im * w₁.im) - (w₀.re * w₁.im - w₀.im * w₁.re) < 0) :
    Real.arctan T < toIcoMod Real.two_pi_pos 0 (Complex.arg w₁ - Complex.arg w₀) := by
  set ψ := toIcoMod Real.two_pi_pos 0 (Complex.arg w₁ - Complex.arg w₀) with hψdef
  have hw₀ : w₀ ≠ 0 := by rintro rfl; simp at h
  have hw₁ : w₁ ≠ 0 := by rintro rfl; simp at h
  obtain ⟨es, ec⟩ := sin_cos_toIcoMod hw₀ hw₁
  rw [← hψdef] at es ec
  have hN : 0 < ‖w₀‖ * ‖w₁‖ := mul_pos (norm_pos_iff.2 hw₀) (norm_pos_iff.2 hw₁)
  have key : T * Real.cos ψ < Real.sin ψ := by
    rw [← es, ← ec] at h
    nlinarith
  have hψ2 : ψ < Real.pi / 2 := by
    by_contra hc
    push Not at hc
    linarith [Real.cos_nonpos_of_pi_div_two_le_of_le hc (by linarith [hψ.2])]
  have htan : T < Real.tan ψ := by
    rw [Real.tan_eq_sin_div_cos, lt_div_iff₀ hcos]; linarith
  have := Real.arctan_strictMono htan
  rwa [Real.arctan_tan (by linarith [hψ.1]) hψ2] at this

/-- `arg w > π - arctan K` when `Im w > 0` and `Im w + K Re w < 0`, `K > 0` (then `Re w < 0`). -/
theorem pi_sub_arctan_lt_arg {w : ℂ} {K : ℝ} (hK : 0 < K) (h1 : 0 < w.im)
    (h2 : w.im + K * w.re < 0) : Real.pi - Real.arctan K < Complex.arg w ∧ w.re < 0 := by
  have hre : w.re < 0 := by nlinarith
  refine ⟨?_, hre⟩
  rw [arg_eq_arctan_add_pi hre h1.le]
  have hq : -K < w.im / w.re := by
    rw [lt_div_iff_of_neg hre]; linarith
  have := Real.arctan_strictMono hq
  rw [Real.arctan_neg] at this
  linarith

/-- `arg w < π - arctan K` when `Re w < 0 ≤ Im w` and `-K Re w - Im w < 0`. -/
theorem arg_lt_pi_sub_arctan {w : ℂ} {K : ℝ} (hre : w.re < 0) (h1 : 0 ≤ w.im)
    (h2 : -(K * w.re) - w.im < 0) : Complex.arg w < Real.pi - Real.arctan K := by
  rw [arg_eq_arctan_add_pi hre h1]
  have hq : w.im / w.re < -K := by
    rw [div_lt_iff_of_neg hre]; linarith
  have := Real.arctan_strictMono hq
  rw [Real.arctan_neg] at this
  linarith

/-! ### The radius `r₂` -/

/-- `r₂/(1 - r₂)² = |w₂|/|w₁|²` for `r₂ = cellCoords w 0` (Lemma 15.1.1: `r₁ = s |w₁|`,
`r₂ = s² |w₂|`, `r₁ + r₂ = 1`), as `r₂ |w₁|² = |w₂| (1 - r₂)²`. -/
theorem cellCoords_zero_mul {w : Fin 3 → ℂ} (h1 : w 1 ≠ 0) :
    cellCoords w 0 * ‖w 0‖ ^ 2 = ‖w 1‖ * (1 - cellCoords w 0) ^ 2 := by
  have hb : 0 < ‖w 1‖ := norm_pos_iff.2 h1
  have ha : 0 ≤ ‖w 0‖ := norm_nonneg _
  set a := ‖w 0‖
  set b := ‖w 1‖
  have hd : 0 ≤ a ^ 2 + 4 * b := by positivity
  have hsq := Real.sq_sqrt hd
  set s := (-a + √(a ^ 2 + 4 * b)) / (2 * b) with hs
  have e : cellCoords w 0 = s ^ 2 * b := by
    change (if b = 0 then a⁻¹ else (-a + √(a ^ 2 + 4 * b)) / (2 * b)) ^ 2 * b = s ^ 2 * b
    rw [ite_eq_right_iff.2 fun h ↦ absurd h hb.ne']
  -- `a s + b s² = 1`
  have hroot : a * s + b * s ^ 2 = 1 := by
    rw [hs]
    field_simp
    linear_combination hsq
  rw [e]
  have : 1 - s ^ 2 * b = a * s := by linarith
  rw [this]
  ring

/-- `x/(1 - x)²` is increasing on `[0, 1)`: `x (1 - y)² - y (1 - x)² = (x - y) (1 - x y)`. -/
theorem mul_one_sub_sq_lt {x y : ℝ} (hx : 0 ≤ x) (hy1 : y < 1) (hxy : x < y) :
    x * (1 - y) ^ 2 < y * (1 - x) ^ 2 := by
  have e : y * (1 - x) ^ 2 - x * (1 - y) ^ 2 = (y - x) * (1 - x * y) := by ring
  have : 0 < (y - x) * (1 - x * y) := mul_pos (by linarith) (by nlinarith)
  linarith

/-- `r₂ < R` when `|w₂|² < (R/(1 - R)²)² |w₁|⁴`. -/
theorem cellCoords_zero_lt {w : Fin 3 → ℂ} {R : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1)
    (hr : cellCoords w 0 ∈ Ioo 0 1) (h1 : w 1 ≠ 0)
    (h : ‖w 1‖ ^ 2 - (R / (1 - R) ^ 2) ^ 2 * (‖w 0‖ ^ 2) ^ 2 < 0) : cellCoords w 0 < R := by
  set r := cellCoords w 0
  have key : r * ‖w 0‖ ^ 2 = ‖w 1‖ * (1 - r) ^ 2 := cellCoords_zero_mul h1
  have hb : 0 < ‖w 1‖ := norm_pos_iff.2 h1
  have hR : 0 < (1 - R) ^ 2 := by nlinarith
  have hb' : ‖w 1‖ * (1 - R) ^ 2 < R * ‖w 0‖ ^ 2 := by
    have e : (R / (1 - R) ^ 2) ^ 2 * (‖w 0‖ ^ 2) ^ 2 = (R * ‖w 0‖ ^ 2 / (1 - R) ^ 2) ^ 2 := by ring
    rw [e] at h
    have h0 : 0 ≤ R * ‖w 0‖ ^ 2 / (1 - R) ^ 2 := by positivity
    have : ‖w 1‖ < R * ‖w 0‖ ^ 2 / (1 - R) ^ 2 := by nlinarith
    rwa [lt_div_iff₀ hR] at this
  by_contra hc
  push Not at hc
  rcases hc.lt_or_eq with hc | hc
  · have := mul_one_sub_sq_lt hR0 hr.2 hc
    have h2 : 0 < (1 - r) ^ 2 := by nlinarith [hr.2]
    nlinarith [sq_nonneg ‖w 0‖]
  · rw [← hc] at key
    linarith

/-- `r₂ > R` when `(R/(1 - R)²)² |w₁|⁴ < |w₂|²`. -/
theorem lt_cellCoords_zero {w : Fin 3 → ℂ} {R : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1)
    (hr : cellCoords w 0 ∈ Ioo 0 1) (h1 : w 1 ≠ 0)
    (h : (R / (1 - R) ^ 2) ^ 2 * (‖w 0‖ ^ 2) ^ 2 - ‖w 1‖ ^ 2 < 0) : R < cellCoords w 0 := by
  set r := cellCoords w 0
  have key : r * ‖w 0‖ ^ 2 = ‖w 1‖ * (1 - r) ^ 2 := cellCoords_zero_mul h1
  have hb : 0 < ‖w 1‖ := norm_pos_iff.2 h1
  have hR : 0 < (1 - R) ^ 2 := by nlinarith
  have hb' : R * ‖w 0‖ ^ 2 < ‖w 1‖ * (1 - R) ^ 2 := by
    have e : (R / (1 - R) ^ 2) ^ 2 * (‖w 0‖ ^ 2) ^ 2 = (R * ‖w 0‖ ^ 2 / (1 - R) ^ 2) ^ 2 := by ring
    rw [e] at h
    have h0 : 0 ≤ R * ‖w 0‖ ^ 2 / (1 - R) ^ 2 := by positivity
    have : R * ‖w 0‖ ^ 2 / (1 - R) ^ 2 < ‖w 1‖ := by nlinarith
    rwa [div_lt_iff₀ hR] at this
  by_contra hc
  push Not at hc
  rcases hc.lt_or_eq with hc | hc
  · have := mul_one_sub_sq_lt hr.1.le hR1 hc
    have h2 : 0 < (1 - r) ^ 2 := by nlinarith [hr.2]
    nlinarith [sq_nonneg ‖w 0‖]
  · rw [hc] at key
    linarith

/-- `|z|² = Re z² + Im z²`. -/
theorem norm_sq_eq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring


end SmoothedPolygons.TriFuller.DOutAnalytic
