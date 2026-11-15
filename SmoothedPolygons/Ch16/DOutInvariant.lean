module

public import SmoothedPolygons.Ch16.DOutFlow
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# `F(𝒟₀₀) ⊆ 𝒟₀₀` without computer assistance

The first conjunct of `DOutContracts` (`SmoothedPolygons/Ch16/BasinHypotheses.lean`):
`MapsTo poincareAngZero (boxSet 0 0) (boxSet 0 0)` (`mapsTo_boxSet_zero_zero`), for the box
`𝒟₀₀ = {r₂ ∈ [0, 1], ψ ∈ [0, π/3], θ₂ ∈ [π - 1.1, π]}`, faces included.

The structure is that of `SmoothedPolygons/Ch16/DOutFlow.lean`: off the face piece
`{r₂ = 0, θ₁ ≤ π/3}` the first control is `ζ`, the switch is the unique positive root `τ` of
`D = V₂` (`exists_root`), and the class of the image is the class of the cell coordinates of
`w = ζ F(z)`, `w₁ = U₀ + i V₀`, `w₂ = U₁ + i V₁` (`image_spec`); on the face piece the class is
changed by the `V_T`-equivariance (`cellClass_face`). What is left are the two inequalities
`ψ' < π/3` and `θ₂' > 2π/3 ≥ π - 1.1` for the cell coordinates `(r₂', ψ', θ₂')` of `w`, which
follow from `C₁ = U₀ (V₁ - √3 U₁) - V₀ (U₁ + √3 V₁) < 0` and `C₂ = V₁ + √3 U₁ < 0`
(`toIcoMod_lt_pi_div_three`, `two_pi_div_three_lt_arg`). Both are proved by exact algebra:

* `C₂ = -2 Im z₂(τ) = -2 (r₁ sin θ₁ τ + r₂ sin θ₂ + τ²/4)` (`C₂_eq`), negative because
  `sin θ₁, sin θ₂ ≥ 0` on `𝒟₀₀`;
* `√3 C₁ + 10 D(τ) = -r₁ r₂ (9√3 sin ψ + 3 cos ψ) - 3 r₁² τ - 4 r₁ τ² sin θ₁
  + r₂ τ (3√3 cos θ₂ - 5 sin θ₂) - (2/3) τ³` (`C₁_eq`, an identity of polynomials in `τ`,
  `r₂`, `cos θ_j`, `sin θ_j` and `√3`); at the root `D(τ) = 0`, and every term on the right is
  `≤ 0` on `𝒟₀₀` (`sin ψ, cos ψ, sin θ₁, sin θ₂ ≥ 0 ≥ cos θ₂`), the last one `< 0`.

Departure from the paper: the book reads the containment `F₁(𝒟_out) ⊂ 𝒟_out` off a computer
calculation by the boundary method (Figure 16.1, TeX 12592–12607); the formalization proves it
analytically, by the root structure of the switching cubic and the two identities above (the
multiplier `10` of `D` makes every coefficient of `√3 C₁ + 10 D` sign-definite on `𝒟₀₀`). This
replaces the interval certificate of `SmoothedPolygons/Ch16/Certificates/DOutMapsTo.lean`
(248 kernel-checked boxes).
-/

@[expose] public section

namespace SmoothedPolygons.TriFuller.DOutAnalytic

open Set

/-! ### Exact identities -/

theorem cos_add_two_thirds_pi (x : ℝ) :
    Real.cos (x + 2 / 3 * Real.pi) = Real.cos x * (-1 / 2) - Real.sin x * (√3 / 2) := by
  rw [Real.cos_add, cos_two_thirds_pi, sin_two_thirds_pi]

theorem sin_add_two_thirds_pi (x : ℝ) :
    Real.sin (x + 2 / 3 * Real.pi) = Real.sin x * (-1 / 2) + Real.cos x * (√3 / 2) := by
  rw [Real.sin_add, cos_two_thirds_pi, sin_two_thirds_pi]

/-- `sin ψ = sin (θ₂ - θ₁)`. -/
theorem sin_one_eq (p : Fin 3 → ℝ) : Real.sin (p 1) =
    Real.sin (p 2) * Real.cos (p 2 - p 1) - Real.cos (p 2) * Real.sin (p 2 - p 1) := by
  rw [← Real.sin_sub]; congr 1; ring

/-- `cos ψ = cos (θ₂ - θ₁)`. -/
theorem cos_one_eq (p : Fin 3 → ℝ) : Real.cos (p 1) =
    Real.cos (p 2) * Real.cos (p 2 - p 1) + Real.sin (p 2) * Real.sin (p 2 - p 1) := by
  rw [← Real.cos_sub]; congr 1; ring

/-- **`C₂ = -2 Im z₂(t)`**: `V₁ + √3 U₁ = -2 (r₁ sin θ₁ t + r₂ sin θ₂ + t²/4)`. -/
theorem C₂_eq (p : Fin 3 → ℝ) (t : ℝ) : V₁ p t + √3 * U₁ p t =
    -2 * ((1 - p 0) * Real.sin (p 2 - p 1) * t + p 0 * Real.sin (p 2) + t ^ 2 / 4) := by
  have hq : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [V₁, U₁, cx₁, cy₁, cx₂, cy₂, cos_add_two_thirds_pi, sin_add_two_thirds_pi]
  set q := √3
  set s1 := Real.sin (p 2 - p 1)
  set s2 := Real.sin (p 2)
  set r := p 0
  linear_combination (r * s1 * t / 2 - r * s2 / 2 - s1 * t / 2 - t ^ 2 / 4) * hq

/-- **The identity for `C₁`**: `√3 C₁ + 10 D` is a sum of terms of fixed sign on `𝒟₀₀`. -/
theorem C₁_eq (p : Fin 3 → ℝ) (t : ℝ) :
    √3 * (U₀ p t * (V₁ p t - √3 * U₁ p t) - V₀ p t * (U₁ p t + √3 * V₁ p t)) + 10 * V₂ p t =
      -((1 - p 0) * p 0 * (9 * √3 * Real.sin (p 1) + 3 * Real.cos (p 1))) -
        3 * (1 - p 0) ^ 2 * t - 4 * (1 - p 0) * t ^ 2 * Real.sin (p 2 - p 1) +
        p 0 * t * (3 * √3 * Real.cos (p 2) - 5 * Real.sin (p 2)) - 2 / 3 * t ^ 3 := by
  have hq : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs : Real.cos (p 2 - p 1) ^ 2 + Real.sin (p 2 - p 1) ^ 2 = 1 := Real.cos_sq_add_sin_sq _
  simp only [U₀, V₀, U₁, V₁, V₂, cx₁, cy₁, cx₂, cy₂, cκ, cos_add_two_thirds_pi,
    sin_add_two_thirds_pi, sin_one_eq p, cos_one_eq p]
  set q := √3
  set c1 := Real.cos (p 2 - p 1)
  set s1 := Real.sin (p 2 - p 1)
  set c2 := Real.cos (p 2)
  set s2 := Real.sin (p 2)
  set r := p 0
  linear_combination (-c1^2*q^2*r^2*t/4 + c1^2*q^2*r*t/2 - c1^2*q^2*t/4 - c1^2*r^2*t +
    2*c1^2*r*t - c1^2*t + c1*c2*q^2*r^2/4 - c1*c2*q^2*r/4 + c1*c2*r^2 - c1*c2*r -
    c1*q*r^2*s2/4 + c1*q*r*s2/4 + 7*c1*q*r*t^2/8 - 7*c1*q*t^2/8 + c2*q*r^2*s1/4 -
    c2*q*r*s1/4 - 3*c2*q*r*t/4 - q^2*r^2*s1^2*t/4 + q^2*r^2*s1*s2/4 + q^2*r*s1^2*t/2 -
    q^2*r*s1*s2/4 + 3*q^2*r*s1*t^2/8 - q^2*r*s2*t/4 - q^2*s1^2*t/4 - 3*q^2*s1*t^2/8 -
    q^2*t^3/8 - r^2*s1^2*t + r^2*s1*s2 + 2*r*s1^2*t - r*s1*s2 + r*s1*t^2/2 - s1^2*t -
    s1*t^2/2 - t^3/2) * hq + (-3 * t * (r - 1) ^ 2) * hs

/-! ### The switch -/

/-- `D(7) > 0` on `𝒟₀₀` (`|y_j| ≤ r_j`, `κ ≤ 1/4`). -/
theorem V₂_seven_pos {p : Fin 3 → ℝ} (hp : p ∈ cellBox 0 0) : 0 < V₂ p 7 := by
  obtain ⟨⟨h0, h0'⟩, -, -⟩ := mem_cellBox_zero_zero.1 hp
  have hr1 : 0 ≤ 1 - p 0 := by linarith
  have a1 : -(1 - p 0) ≤ cy₁ p := by
    unfold cy₁; nlinarith [Real.neg_one_le_sin (p 2 - p 1 + 2 / 3 * Real.pi)]
  have a2 : -p 0 ≤ cy₂ p := by
    unfold cy₂; nlinarith [Real.neg_one_le_sin (p 2 + 2 / 3 * Real.pi)]
  have a3 : cκ p ≤ 1 / 4 := by
    unfold cκ
    have := Real.sin_le_one (p 1)
    have : 0 ≤ (1 - p 0) * p 0 := mul_nonneg hr1 h0
    nlinarith [sq_nonneg (p 0 - 1 / 2)]
  have h3 : √3 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h3' : 0 ≤ √3 := Real.sqrt_nonneg 3
  unfold V₂
  nlinarith [mul_le_mul_of_nonneg_left a3 h3']

/-- **The switching time**: off the face piece `r₂ = 0, θ₁ ≤ π/3`, `D` has a positive root `τ`,
with `D < 0` on `(0, τ)` and `D > 0` after it. -/
theorem exists_root {p : Fin 3 → ℝ} (hp : p ∈ cellBox 0 0)
    (hB : ¬(p 0 = 0 ∧ p 2 - p 1 ≤ Real.pi / 3)) :
    ∃ τ, 0 < τ ∧ V₂ p τ = 0 ∧ (∀ t, 0 < t → t < τ → V₂ p t < 0) ∧ ∀ t, τ < t → 0 < V₂ p t := by
  obtain ⟨hy, hk, -, -, -⟩ := cellBox_facts hp
  obtain ⟨s, hs, hVs⟩ := exists_V₂_neg hp hB
  have h7 := V₂_seven_pos hp
  have hs7 : s < 7 := by
    by_contra hc
    push Not at hc
    rcases hc.lt_or_eq with h | h
    · linarith [V₂_pos_of_nonneg hy hk (by norm_num) h h7.le]
    · rw [← h] at hVs; linarith
  have hcont : ContinuousOn (V₂ p) (Icc s 7) := by
    unfold V₂; fun_prop
  obtain ⟨τ, hτ, h0⟩ := intermediate_value_Ioo hs7.le hcont ⟨hVs, h7⟩
  have hτ0 : 0 < τ := hs.trans hτ.1
  exact ⟨τ, hτ0, h0, fun t ht htτ ↦ V₂_neg_of_nonpos hy hk ht htτ h0.le,
    fun t htτ ↦ V₂_pos_of_nonneg hy hk hτ0 htτ h0.ge⟩

/-! ### The image -/

/-- `C₂ < 0` at every `t > 0` on `𝒟₀₀`. -/
theorem C₂_neg {p : Fin 3 → ℝ} (hp : p ∈ cellBox 0 0) {t : ℝ} (ht : 0 < t) :
    V₁ p t + √3 * U₁ p t < 0 := by
  obtain ⟨-, -, hs2, hs21, -⟩ := cellBox_facts hp
  obtain ⟨⟨h0, h0'⟩, -, -⟩ := mem_cellBox_zero_zero.1 hp
  rw [C₂_eq]
  have : 0 ≤ (1 - p 0) * Real.sin (p 2 - p 1) * t :=
    mul_nonneg (mul_nonneg (by linarith) hs21) ht.le
  have : 0 ≤ p 0 * Real.sin (p 2) := mul_nonneg h0 hs2
  nlinarith [sq_pos_of_pos ht]

/-- `C₁ < 0` at a positive root of `D` on `𝒟₀₀`. -/
theorem C₁_neg {p : Fin 3 → ℝ} (hp : p ∈ cellBox 0 0) {τ : ℝ} (hτ : 0 < τ) (h0 : V₂ p τ = 0) :
    U₀ p τ * (V₁ p τ - √3 * U₁ p τ) - V₀ p τ * (U₁ p τ + √3 * V₁ p τ) < 0 := by
  obtain ⟨-, -, hs2, hs21, -⟩ := cellBox_facts hp
  obtain ⟨⟨h0r, h0r'⟩, ⟨h1, h1'⟩, ⟨h2, h2'⟩⟩ := mem_cellBox_zero_zero.1 hp
  have hpi := Real.pi_gt_three
  have hq : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  have e := C₁_eq p τ
  rw [h0, mul_zero, add_zero] at e
  have hsψ : 0 ≤ Real.sin (p 1) := Real.sin_nonneg_of_nonneg_of_le_pi h1 (by linarith)
  have hcψ : 0 ≤ Real.cos (p 1) :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) (by linarith)
  have hc2 : Real.cos (p 2) ≤ 0 :=
    Real.cos_nonpos_of_pi_div_two_le_of_le (by norm_num at h2 ⊢; linarith) (by linarith)
  have hr1 : 0 ≤ 1 - p 0 := by linarith
  have t1 : 0 ≤ (1 - p 0) * p 0 * (9 * √3 * Real.sin (p 1) + 3 * Real.cos (p 1)) := by
    positivity
  have t2 : 0 ≤ 3 * (1 - p 0) ^ 2 * τ := by positivity
  have t3 : 0 ≤ 4 * (1 - p 0) * τ ^ 2 * Real.sin (p 2 - p 1) := by positivity
  have t4 : p 0 * τ * (3 * √3 * Real.cos (p 2) - 5 * Real.sin (p 2)) ≤ 0 := by
    have : 3 * √3 * Real.cos (p 2) - 5 * Real.sin (p 2) ≤ 0 := by nlinarith
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg h0r hτ.le) this
  have t5 : 0 < 2 / 3 * τ ^ 3 := by positivity
  have : √3 * (U₀ p τ * (V₁ p τ - √3 * U₁ p τ) - V₀ p τ * (U₁ p τ + √3 * V₁ p τ)) < 0 := by
    linarith
  exact neg_of_mul_neg_right this hq.le

/-- **The image of a point of `𝒟₀₀` off the face piece `r₂ = 0, θ₁ ≤ π/3`**: its cell coordinates
satisfy `ψ < π/3` and `θ₂ > 2π/3 ≥ π - 1.1`. -/
theorem poincareAngZero_mem_of_not_face {p : Fin 3 → ℝ} (hp : p ∈ cellBox 0 0)
    (hB : ¬(p 0 = 0 ∧ p 2 - p 1 ≤ Real.pi / 3)) : poincareAngZero (cellClass p) ∈ boxSet 0 0 := by
  obtain ⟨τ, hτ0, h0, -, -⟩ := exists_root hp hB
  have hC2 := C₂_neg hp hτ0
  have hC1 := C₁_neg hp hτ0 h0
  obtain ⟨hV₁, w, -, himage, e0r, e0i, e1r, e1i, c0, c1, h1, h2⟩ := image_spec hp hτ0 h0
  rw [himage]
  refine ⟨cellCoords w, ?_, rfl⟩
  rw [mem_cellBox_zero_zero]
  refine ⟨⟨c0.1.le, c0.2.le⟩, ⟨by rw [h1]; exact c1.1.le, ?_⟩, ⟨?_, by
    rw [h2]; exact Complex.arg_le_pi _⟩⟩
  · -- `ψ < π/3`
    have := toIcoMod_lt_pi_div_three (w₀ := w 0) (w₁ := w 1) c1
      (by rw [e0r, e0i, e1r, e1i]; exact hC1)
    rw [h1]
    exact this.le
  · -- `θ₂ > 2π/3 ≥ π - 1.1`
    have := two_pi_div_three_lt_arg (w := w 1) (by rw [e1i]; exact hV₁)
      (by rw [e1i, e1r]; exact hC2)
    rw [h2]
    have := Real.pi_lt_d2
    norm_num at this ⊢
    linarith

/-- **`F(𝒟₀₀) ⊆ 𝒟₀₀`**, the first conjunct of `DOutContracts`
(`SmoothedPolygons/Ch16/BasinHypotheses.lean`), without computer assistance.

Departure from the paper: the book reads this off a Mathematica computation by the boundary method
(Figure 16.1, TeX 12592–12597); the formalization proves it analytically, by the root structure of
the switching cubic (`exists_root`, `image_spec`) and the identities `C₂_eq`, `C₁_eq` (signs of
explicit polynomials in `τ`, `r₂` and the sines and cosines of the cell angles). -/
theorem mapsTo_boxSet_zero_zero : MapsTo poincareAngZero (boxSet 0 0) (boxSet 0 0) := by
  rintro x ⟨p, hp, rfl⟩
  by_cases hA : p 0 = 0 ∧ p 2 - p 1 ≤ Real.pi / 3
  · -- the face piece: change of representative
    obtain ⟨⟨h0, h0'⟩, ⟨h1, h1'⟩, ⟨h2, h2'⟩⟩ := mem_cellBox_zero_zero.1 hp
    have hpi := Real.pi_gt_three
    have hp' : ![0, 0, p 2 - p 1 + 2 * Real.pi / 3] ∈ cellBox 0 0 := by
      rw [mem_cellBox_zero_zero]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      refine ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, by positivity⟩, ⟨?_, ?_⟩⟩
      · norm_num at h2 ⊢; linarith
      · linarith [hA.2]
    rw [cellClass_face hp hA.1]
    refine poincareAngZero_mem_of_not_face hp' fun h ↦ ?_
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at h
    linarith [h.2]
  · exact poincareAngZero_mem_of_not_face hp hA

end SmoothedPolygons.TriFuller.DOutAnalytic
