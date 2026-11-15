module

public import SmoothedPolygons.Ch16.DOutInvariant
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# `F²(𝒟₀₀) ⊆ B` without computer assistance

Two steps of the Fuller–Poincaré map on `𝒟₀₀`, for the contraction part of `DOutContracts`
(`SmoothedPolygons/Ch16/BasinHypotheses.lean`): through the region
`D₁ = {r₂ ∈ [0, 1], ψ ∈ [0, arctan (1/4)], θ₂ ∈ [5π/6, π]}` (`regionD1`) into the box
`B = [11/50, 3/10] × [arctan (25/312), arctan (20/99)] × [π - arctan (39/80), π - arctan (15/112)]`
(`boxLo`, `boxHi`; about `[0.22, 0.3] × [0.080, 0.199] × [2.688, 3.009]`):

* `F(𝒟₀₀) ⊆ D₁` (`image_mem_regionD1`): `θ₂' > 5π/6` because
  `√3 V₁ + U₁ = -2 (r₂ sin (θ₂ - π/6) + r₁ τ sin (θ₁ - π/6))` (`theta_cond`), and
  `ψ' < arctan (1/4)` because `(B - A/4) + (7/5) D(τ)` (`A + i B = w̄₁ w₂`) has coefficients of
  fixed sign on `𝒟₀₀` as a polynomial in `r₁, r₂, τ` (`psi_cond`);
* `F(D₁) ⊆ B` (`image_mem_box`): with `σ = 1/τ`, the root equation `D(τ) = 0` reads
  `W₁ + W₂ + W₃ = 1/12` with `W₁ = -y₁ σ/2`, `W₂ = -y₂ σ²`, `W₃ = √3 κ σ³`, all `≥ 0` on `D₁`, and
  `w₁/τ = (-√3/2 + X₁) + i (1/2 - 2 W₁)`, `w₂/τ² = (-√3/4 + X₁ + X₂) + i (1/6 - W₁ + W₃)` with
  `X₁ = x₁ σ`, `X₂ = x₂ σ²` (`normalized_eqs`): the image is an affine function of
  `(W₁, W₃, X₁, X₂)`, which on `D₁` lie in an explicit polytope (`W₃ ≤ 1/480`,
  `-3/5 W₁ ≤ X₁ ≤ 1.155 W₁`, `0 ≤ X₂ ≤ 0.578 W₂`; `omega_facts`, from the signs of `sin`, `cos` on
  `D₁`), and the six inequalities that place the image in `B` (`omega_conds`) are explicit
  polynomial inequalities on that polytope, proved by `linarith`/`nlinarith` (the two of degree
  four with products of the constraints found by a linear program).

Departure from the paper: the book does not prove that the iterates of `𝒟_out` converge (REPORT.md,
E78); the formalization's contraction hypothesis needs `F^N(𝒟₀₀) ⊆ B`, and the numerical facts
behind it (Figure 16.1, TeX 12592–12607: computed in Mathematica) are proved here analytically,
by the root structure of the switching cubic and the normalisation `τ = 1`, which makes the image
an affine function of four small quantities.
-/

@[expose] public section

namespace SmoothedPolygons.TriFuller.DOutAnalytic

open Set

/-! ### Trigonometric facts -/

theorem sin_sub_pi_div_six (x : ℝ) :
    Real.sin (x - Real.pi / 6) = √3 / 2 * Real.sin x - 1 / 2 * Real.cos x := by
  rw [Real.sin_sub, Real.cos_pi_div_six, Real.sin_pi_div_six]; ring

theorem sqrt_three_bounds : 1.732 < √3 ∧ √3 < 1.7321 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-! ### `F(𝒟₀₀) ⊆ D₁` -/

/-- The region `D₁ = {r₂ ∈ [0, 1], ψ ∈ [0, arctan (1/4)], θ₂ ∈ [5π/6, π]}`. -/
def regionD1 : Set (Fin 3 → ℝ) :=
  {p | p 0 ∈ Icc 0 1 ∧ p 1 ∈ Icc 0 (Real.arctan (1 / 4)) ∧ p 2 ∈ Icc (5 * Real.pi / 6) Real.pi}

theorem arctan_quarter_lt : Real.arctan (1 / 4) < 1 / 4 := Real.arctan_lt_self (by norm_num)

theorem regionD1_subset : regionD1 ⊆ cellBox 0 0 := by
  intro p ⟨h0, ⟨h1, h1'⟩, ⟨h2, h2'⟩⟩
  have := arctan_quarter_lt
  have hpi := Real.pi_gt_three
  have hpi' := Real.pi_lt_d2
  rw [mem_cellBox_zero_zero]
  refine ⟨h0, ⟨h1, by linarith⟩, ⟨by norm_num; linarith, h2'⟩⟩

theorem not_face_of_mem_regionD1 {p : Fin 3 → ℝ} (hp : p ∈ regionD1) :
    ¬(p 0 = 0 ∧ p 2 - p 1 ≤ Real.pi / 3) := by
  obtain ⟨-, ⟨-, h1'⟩, ⟨h2, -⟩⟩ := hp
  have := arctan_quarter_lt
  have hpi := Real.pi_gt_three
  rintro ⟨-, h⟩
  linarith

/-- **`θ₂' > 5π/6`**: `√3 V₁ + U₁ = -2 (r₂ sin (θ₂ - π/6) + r₁ t sin (θ₁ - π/6)) < 0`. -/
theorem theta_cond {p : Fin 3 → ℝ} (hp : p ∈ cellBox 0 0) {t : ℝ} (ht : 0 < t) :
    √3 * V₁ p t + U₁ p t < 0 := by
  obtain ⟨⟨h0, h0'⟩, ⟨h1, h1'⟩, ⟨h2, h2'⟩⟩ := mem_cellBox_zero_zero.1 hp
  have hpi := Real.pi_gt_three
  have hpi' := Real.pi_lt_d2
  have hq : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have e : √3 * V₁ p t + U₁ p t = -2 * (p 0 * Real.sin (p 2 - Real.pi / 6) +
      (1 - p 0) * t * Real.sin (p 2 - p 1 - Real.pi / 6)) := by
    simp only [V₁, U₁, cx₁, cy₁, cx₂, cy₂, cos_add_two_thirds_pi, sin_add_two_thirds_pi,
      sin_sub_pi_div_six]
    set q := √3
    set c1 := Real.cos (p 2 - p 1)
    set c2 := Real.cos (p 2)
    set r := p 0
    linear_combination (-c1 * r * t / 2 + c1 * t / 2 + c2 * r / 2) * hq
  have s2 : 0 < Real.sin (p 2 - Real.pi / 6) :=
    Real.sin_pos_of_pos_of_lt_pi (by norm_num at h2; linarith) (by linarith)
  have s1 : 0 < Real.sin (p 2 - p 1 - Real.pi / 6) :=
    Real.sin_pos_of_pos_of_lt_pi (by norm_num at h2; linarith) (by linarith)
  rw [e]
  have : 0 < p 0 * Real.sin (p 2 - Real.pi / 6) +
      (1 - p 0) * t * Real.sin (p 2 - p 1 - Real.pi / 6) := by
    rcases h0'.lt_or_eq with h | h
    · have : 0 < (1 - p 0) * t * Real.sin (p 2 - p 1 - Real.pi / 6) :=
        mul_pos (mul_pos (by linarith) ht) s1
      have : 0 ≤ p 0 * Real.sin (p 2 - Real.pi / 6) := mul_nonneg h0 s2.le
      linarith
    · rw [h]; simp [s2]
  linarith

/-- `sin x ≥ cos x` for `x ∈ [π/4, π]`. -/
theorem cos_le_sin_of {x : ℝ} (h1 : Real.pi / 4 ≤ x) (h2 : x ≤ Real.pi) :
    Real.cos x ≤ Real.sin x := by
  have hpi := Real.pi_gt_three
  have := Real.sin_nonneg_of_nonneg_of_le_pi (x := x - Real.pi / 4) (by linarith) (by linarith)
  rw [Real.sin_sub, Real.cos_pi_div_four, Real.sin_pi_div_four] at this
  have h2 : 0 < √2 := Real.sqrt_pos.2 (by norm_num)
  nlinarith

/-- `-cos θ₂ ≥ 2/5` for `θ₂ ∈ [π - 1.1, π]`. -/
theorem neg_cos_ge {x : ℝ} (h1 : Real.pi - 1.1 ≤ x) (h2 : x ≤ Real.pi) : 2 / 5 ≤ -Real.cos x := by
  have hpi := Real.pi_gt_d2
  have e : -Real.cos x = Real.sin (x - Real.pi / 2) := by
    rw [Real.sin_sub_pi_div_two]
  rw [e]
  have hm : Real.sin (Real.pi / 2 - 1.1) ≤ Real.sin (x - Real.pi / 2) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
  have hl := Real.sin_gt_sub_cube (x := Real.pi / 2 - 1.1) (by linarith)
  have hpi' := Real.pi_lt_d2
  have hx1 : (47 : ℝ) / 100 ≤ Real.pi / 2 - 1.1 := by norm_num at hpi ⊢; linarith
  have hx2 : Real.pi / 2 - 1.1 ≤ (48 : ℝ) / 100 := by norm_num at hpi' ⊢; linarith
  have hx3 : (Real.pi / 2 - 1.1) ^ 3 ≤ ((48 : ℝ) / 100) ^ 3 :=
    pow_le_pow_left₀ (by linarith) hx2 3
  have : (2 : ℝ) / 5 ≤ (Real.pi / 2 - 1.1) - (Real.pi / 2 - 1.1) ^ 3 / 6 := by
    norm_num at hx3 ⊢; linarith
  linarith

/-- **`ψ' < arctan (1/4)`**: `(B - A/4) + (7/5) D` has coefficients of fixed sign on `𝒟₀₀`. -/
theorem psi_cond {p : Fin 3 → ℝ} (hp : p ∈ cellBox 0 0) {t : ℝ} (ht : 0 < t) (h0 : V₂ p t = 0) :
    (U₀ p t * V₁ p t - V₀ p t * U₁ p t) - 1 / 4 * (U₀ p t * U₁ p t + V₀ p t * V₁ p t) < 0 := by
  obtain ⟨-, -, hs2, hs21, -⟩ := cellBox_facts hp
  obtain ⟨⟨h0r, h0r'⟩, ⟨h1, h1'⟩, ⟨h2, h2'⟩⟩ := mem_cellBox_zero_zero.1 hp
  have hpi := Real.pi_gt_three
  have hq : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs : Real.cos (p 2 - p 1) ^ 2 + Real.sin (p 2 - p 1) ^ 2 = 1 := Real.cos_sq_add_sin_sq _
  obtain ⟨q1, q2⟩ := sqrt_three_bounds
  have e : (U₀ p t * V₁ p t - V₀ p t * U₁ p t) - 1 / 4 * (U₀ p t * U₁ p t + V₀ p t * V₁ p t) +
      7 / 5 * V₂ p t =
      (1 - p 0) * p 0 * ((1 - 7 * √3 / 5) * Real.sin (p 1) - 1 / 4 * Real.cos (p 1)) -
      1 / 4 * (1 - p 0) ^ 2 * t +
      (1 - p 0) * t ^ 2 * (Real.sin (p 2 - p 1) * (√3 / 4 - 3 / 16 - 7 / 20) +
        Real.cos (p 2 - p 1) * (-1 / 4 - 3 * √3 / 16 + 7 * √3 / 20)) +
      p 0 * t * (Real.sin (p 2) * (√3 / 2 - 1 / 8 - 7 / 10) +
        Real.cos (p 2) * (-1 / 2 - √3 / 8 + 7 * √3 / 10)) - t ^ 3 / 120 := by
    simp only [U₀, V₀, U₁, V₁, V₂, cx₁, cy₁, cx₂, cy₂, cκ, cos_add_two_thirds_pi,
      sin_add_two_thirds_pi, sin_one_eq p, cos_one_eq p]
    set q := √3
    set c1 := Real.cos (p 2 - p 1)
    set s1 := Real.sin (p 2 - p 1)
    set c2 := Real.cos (p 2)
    set s2 := Real.sin (p 2)
    set r := p 0
    linear_combination (-c1^2*r^2*t/16 + c1^2*r*t/8 - c1^2*t/16 + c1*c2*r^2/16 - c1*c2*r/16 -
      c1*r^2*s2/4 + c1*r*s2/4 + c1*r*t^2/8 - c1*t^2/8 + c2*r^2*s1/4 - c2*r*s1/4 - c2*r*t/4 -
      r^2*s1^2*t/16 + r^2*s1*s2/16 + r*s1^2*t/8 - r*s1*s2/16 + 3*r*s1*t^2/32 - r*s2*t/16 -
      s1^2*t/16 - 3*s1*t^2/32 - t^3/32) * hq + (-r^2*t/4 + r*t/2 - t/4) * hs
  rw [h0, mul_zero, add_zero] at e
  rw [e]
  have hsψ : 0 ≤ Real.sin (p 1) := Real.sin_nonneg_of_nonneg_of_le_pi h1 (by linarith)
  have hcψ : 0 ≤ Real.cos (p 1) :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) (by linarith)
  have hr1 : 0 ≤ 1 - p 0 := by linarith
  have hc1 : Real.cos (p 2 - p 1) ≤ Real.sin (p 2 - p 1) :=
    cos_le_sin_of (by norm_num at h2; linarith) (by linarith)
  have hc2 := neg_cos_ge h2 h2'
  have hs2' := Real.sin_le_one (p 2)
  have t1 : (1 - p 0) * p 0 * ((1 - 7 * √3 / 5) * Real.sin (p 1) - 1 / 4 * Real.cos (p 1)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hr1 h0r) (by nlinarith)
  have t2 : 0 ≤ 1 / 4 * (1 - p 0) ^ 2 * t := by positivity
  have t3 : (1 - p 0) * t ^ 2 * (Real.sin (p 2 - p 1) * (√3 / 4 - 3 / 16 - 7 / 20) +
      Real.cos (p 2 - p 1) * (-1 / 4 - 3 * √3 / 16 + 7 * √3 / 20)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (by nlinarith)
  have t4 : p 0 * t * (Real.sin (p 2) * (√3 / 2 - 1 / 8 - 7 / 10) +
      Real.cos (p 2) * (-1 / 2 - √3 / 8 + 7 * √3 / 10)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg h0r ht.le) (by nlinarith)
  have t5 : 0 < t ^ 3 / 120 := by positivity
  linarith

/-- **`F(𝒟₀₀) ⊆ D₁`** (classes).

Departure from the paper: the book reads the image of `𝒟_out` off a Mathematica plot (Figure 16.1,
TeX 12592–12607); the formalization proves `ψ' < arctan (1/4)` and `θ₂' > 5π/6` analytically
(`psi_cond`: `(B - A/4) + (7/5) D` is a polynomial in `r₁, r₂, τ` with coefficients of fixed sign;
`theta_cond`: an identity with positive terms). -/
theorem image_mem_regionD1 {p : Fin 3 → ℝ} (hp : p ∈ cellBox 0 0) :
    poincareAngZero (cellClass p) ∈ cellClass '' regionD1 := by
  -- off the face piece
  have key : ∀ p ∈ cellBox 0 0, ¬(p 0 = 0 ∧ p 2 - p 1 ≤ Real.pi / 3) →
      poincareAngZero (cellClass p) ∈ cellClass '' regionD1 := by
    intro p hp hB
    obtain ⟨τ, hτ0, h0, -, -⟩ := exists_root hp hB
    have hθ := theta_cond hp hτ0
    have hψ := psi_cond hp hτ0 h0
    obtain ⟨hV₁, w, -, himage, e0r, e0i, e1r, e1i, c0, c1, h1, h2⟩ := image_spec hp hτ0 h0
    rw [himage]
    refine ⟨cellCoords w, ⟨⟨c0.1.le, c0.2.le⟩, ⟨by rw [h1]; exact c1.1.le, ?_⟩, ⟨?_, by
      rw [h2]; exact Complex.arg_le_pi _⟩⟩, rfl⟩
    · obtain ⟨h, -⟩ := toIcoMod_lt_arctan (w₀ := w 0) (w₁ := w 1) (T := 1 / 4) (by norm_num) c1
        (by rw [e0r, e0i, e1r, e1i]; exact hψ)
      rw [h1]; exact h.le
    · have hq : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
      obtain ⟨h, -⟩ := pi_sub_arctan_lt_arg (w := w 1) (K := (√3)⁻¹) (by positivity)
        (by rw [e1i]; exact hV₁) (by
          rw [e1i, e1r]
          have : V₁ p τ + (√3)⁻¹ * U₁ p τ = (√3)⁻¹ * (√3 * V₁ p τ + U₁ p τ) := by
            field_simp
          rw [this]
          exact mul_neg_of_pos_of_neg (by positivity) hθ)
      rw [Real.arctan_inv_sqrt_three] at h
      rw [h2]; linarith
  by_cases hA : p 0 = 0 ∧ p 2 - p 1 ≤ Real.pi / 3
  · obtain ⟨⟨h0, h0'⟩, ⟨h1, h1'⟩, ⟨h2, h2'⟩⟩ := mem_cellBox_zero_zero.1 hp
    have hpi := Real.pi_gt_three
    have hp' : ![0, 0, p 2 - p 1 + 2 * Real.pi / 3] ∈ cellBox 0 0 := by
      rw [mem_cellBox_zero_zero]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      refine ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, by positivity⟩, ⟨?_, ?_⟩⟩
      · norm_num at h2 ⊢; linarith
      · linarith [hA.2]
    rw [cellClass_face hp hA.1]
    refine key _ hp' fun h ↦ ?_
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at h
    linarith [h.2]
  · exact key p hp hA

/-! ### The image in normalized form -/

/-- **The normalisation `τ = 1`**: at a root `τ > 0` of `D`, with `s = 1/τ`, the coordinates of
`w = ζ F(z)` are `w₁ = τ ((-√3/2 + x₁ s) + i (1/2 + y₁ s))`,
`w₂ = τ² ((-√3/4 + x₁ s + x₂ s²) + i (1/6 + y₁ s/2 + √3 κ s³))`, and
`-y₁ s/2 - y₂ s² + √3 κ s³ = 1/12`. -/
theorem normalized_eqs {p : Fin 3 → ℝ} {τ : ℝ} (hτ : 0 < τ) (h0 : V₂ p τ = 0) :
    U₀ p τ = τ * (-√3 / 2 + cx₁ p * τ⁻¹) ∧ V₀ p τ = τ * (1 / 2 + cy₁ p * τ⁻¹) ∧
    U₁ p τ = τ ^ 2 * (-√3 / 4 + cx₁ p * τ⁻¹ + cx₂ p * τ⁻¹ ^ 2) ∧
    V₁ p τ = τ ^ 2 * (1 / 6 + cy₁ p * τ⁻¹ / 2 + √3 * cκ p * τ⁻¹ ^ 3) ∧
    -(cy₁ p * τ⁻¹) / 2 - cy₂ p * τ⁻¹ ^ 2 + √3 * cκ p * τ⁻¹ ^ 3 = 1 / 12 := by
  have hτ' := hτ.ne'
  unfold V₂ at h0
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold U₀; field_simp; ring
  · unfold V₀; field_simp; ring
  · unfold U₁; field_simp; ring
  · have hk : √3 * cκ p = cy₂ p * τ + cy₁ p * τ ^ 2 / 2 + τ ^ 3 / 12 := by linarith
    unfold V₁
    rw [show √3 * cκ p * τ⁻¹ ^ 3 = (cy₂ p * τ + cy₁ p * τ ^ 2 / 2 + τ ^ 3 / 12) * τ⁻¹ ^ 3 by
      rw [hk]]
    field_simp
    ring
  · have hk : √3 * cκ p = cy₂ p * τ + cy₁ p * τ ^ 2 / 2 + τ ^ 3 / 12 := by linarith
    rw [show √3 * cκ p * τ⁻¹ ^ 3 = (cy₂ p * τ + cy₁ p * τ ^ 2 / 2 + τ ^ 3 / 12) * τ⁻¹ ^ 3 by
      rw [hk]]
    field_simp
    ring

/-- The signs of the trigonometric functions on `D₁`: `0 ≤ sin θ₂`, `√3 sin θ₂ ≤ -cos θ₂`,
`0 ≤ sin ψ`, `4 sin ψ ≤ cos ψ`. -/
theorem regionD1_trig {p : Fin 3 → ℝ} (hp : p ∈ regionD1) :
    0 ≤ Real.sin (p 2) ∧ Real.cos (p 2) ≤ 0 ∧ √3 * Real.sin (p 2) ≤ -Real.cos (p 2) ∧
      0 ≤ Real.sin (p 1) ∧ 0 < Real.cos (p 1) ∧ 4 * Real.sin (p 1) ≤ Real.cos (p 1) := by
  obtain ⟨-, ⟨h1, h1'⟩, ⟨h2, h2'⟩⟩ := hp
  have hpi := Real.pi_gt_three
  have ha := arctan_quarter_lt
  have hcψ : 0 < Real.cos (p 1) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  refine ⟨Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) h2',
    Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith), ?_,
    Real.sin_nonneg_of_nonneg_of_le_pi h1 (by linarith), hcψ, ?_⟩
  · have := Real.cos_nonpos_of_pi_div_two_le_of_le (x := p 2 - Real.pi / 3) (by linarith)
      (by linarith)
    rw [Real.cos_sub, Real.cos_pi_div_three, Real.sin_pi_div_three] at this
    linarith
  · have ht : Real.tan (p 1) ≤ 1 / 4 := by
      rw [← Real.tan_arctan (1 / 4)]
      exact Real.strictMonoOn_tan.monotoneOn ⟨by linarith, by linarith⟩
        ⟨by linarith [Real.neg_pi_div_two_lt_arctan (1 / 4)], Real.arctan_lt_pi_div_two _⟩ h1'
    rw [Real.tan_eq_sin_div_cos, div_le_iff₀ hcψ] at ht
    linarith

/-- `sin θ₂/2 - (√3/2) cos θ₂ ≥ √3/2` when `√3 sin θ₂ ≤ -cos θ₂`, `0 ≤ sin θ₂`. -/
theorem sin_sub_pi_div_three_ge {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (hs : 0 ≤ s)
    (h : √3 * s ≤ -c) : √3 / 2 ≤ s / 2 - √3 / 2 * c := by
  obtain ⟨q1, q2⟩ := sqrt_three_bounds
  have hq : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3s : 3 * s ^ 2 ≤ c ^ 2 := by
    have := mul_le_mul h h (by positivity) (by linarith [mul_nonneg (Real.sqrt_nonneg 3) hs])
    nlinarith
  have hs2 : s ≤ 1 / 2 := by nlinarith
  -- `-c ≥ 1 - s/√3`, by squaring
  have hc : 0 ≤ -c := by nlinarith
  have key : (√3 - s) ^ 2 ≤ 3 * c ^ 2 := by nlinarith
  have : √3 - s ≤ √3 * -c := by
    have h1 : 0 ≤ √3 - s := by linarith
    have h2 : 0 ≤ √3 * -c := by positivity
    nlinarith [sq_nonneg (√3 - s - √3 * -c), sq_nonneg (√3 - s + √3 * -c)]
  linarith

/-- The angle `θ₁ = θ₂ - ψ` on `D₁`: `cos θ₁ ≤ 0 ≤ sin θ₁`. -/
theorem regionD1_theta1 {p : Fin 3 → ℝ} (hp : p ∈ regionD1) :
    Real.cos (p 2 - p 1) ≤ 0 ∧ 0 ≤ Real.sin (p 2 - p 1) := by
  obtain ⟨hs2, hc2, h23, hsψ, hcψ, h4ψ⟩ := regionD1_trig hp
  obtain ⟨q1, -⟩ := sqrt_three_bounds
  rw [Real.cos_sub, Real.sin_sub]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right h23 hcψ.le, mul_le_mul_of_nonneg_left h4ψ hs2,
      mul_le_mul_of_nonneg_right q1.le (mul_nonneg hs2 hcψ.le)]
  · nlinarith [mul_nonneg hs2 hcψ.le, mul_nonneg (neg_nonneg.2 hc2) hsψ]

/-- The rotated angles `φ₁ = θ₁ + 2π/3`, `φ₂ = θ₂ + 2π/3` on `D₁`: the signs of `sin φ_j`, and
`-sin φ₁ ≥ (√3/2) cos ψ`, `-sin φ₂ ≥ √3/2`. -/
theorem regionD1_sin_phi {p : Fin 3 → ℝ} (hp : p ∈ regionD1) :
    Real.sin (p 2 - p 1 + 2 / 3 * Real.pi) ≤ 0 ∧ Real.sin (p 2 + 2 / 3 * Real.pi) ≤ 0 ∧
      √3 / 2 * Real.cos (p 1) ≤ -Real.sin (p 2 - p 1 + 2 / 3 * Real.pi) ∧
      √3 / 2 ≤ -Real.sin (p 2 + 2 / 3 * Real.pi) := by
  obtain ⟨hs2, hc2, h23, hsψ, hcψ, -⟩ := regionD1_trig hp
  obtain ⟨hc1, hs1⟩ := regionD1_theta1 hp
  have hcs2 : Real.cos (p 2) ^ 2 + Real.sin (p 2) ^ 2 = 1 := Real.cos_sq_add_sin_sq _
  have h := sin_sub_pi_div_three_ge hcs2 hs2 h23
  rw [sin_add_two_thirds_pi, sin_add_two_thirds_pi]
  refine ⟨by nlinarith [mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg 3) hc1],
    by nlinarith [mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg 3) hc2], ?_, by linarith⟩
  rw [Real.cos_sub, Real.sin_sub]
  have : 0 ≤ Real.sin (p 1) * (-Real.cos (p 2) / 2 - √3 / 2 * Real.sin (p 2)) :=
    mul_nonneg hsψ (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left h hcψ.le]

/-- The cosines of the rotated angles on `D₁`, against their sines. -/
theorem regionD1_cos_phi {p : Fin 3 → ℝ} (hp : p ∈ regionD1) :
    0 ≤ Real.cos (p 2 - p 1 + 2 / 3 * Real.pi) - 3 / 10 * Real.sin (p 2 - p 1 + 2 / 3 * Real.pi) ∧
      Real.cos (p 2 - p 1 + 2 / 3 * Real.pi) +
        1155 / 2000 * Real.sin (p 2 - p 1 + 2 / 3 * Real.pi) ≤ 0 ∧
      0 ≤ Real.cos (p 2 + 2 / 3 * Real.pi) ∧
      Real.cos (p 2 + 2 / 3 * Real.pi) + 578 / 1000 * Real.sin (p 2 + 2 / 3 * Real.pi) ≤ 0 := by
  obtain ⟨hs2, hc2, h23, hsψ, hcψ, h4ψ⟩ := regionD1_trig hp
  obtain ⟨hc1, hs1⟩ := regionD1_theta1 hp
  obtain ⟨q1, q2⟩ := sqrt_three_bounds
  rw [cos_add_two_thirds_pi, sin_add_two_thirds_pi, cos_add_two_thirds_pi, sin_add_two_thirds_pi]
  refine ⟨?_, ?_, by linarith, ?_⟩
  · rw [Real.cos_sub, Real.sin_sub]
    have e1 : 0 ≤ -Real.cos (p 2) - √3 * Real.sin (p 2) := by linarith
    have e2 : 0 ≤ Real.cos (p 1) - 4 * Real.sin (p 1) := by linarith
    have hq : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have f1 : 0 ≤ Real.cos (p 1) * (1 / 2 + 3 * √3 / 20) - Real.sin (p 1) * (√3 / 2 - 3 / 20) := by
      nlinarith [mul_nonneg (Real.sqrt_nonneg 3) e2, mul_nonneg (Real.sqrt_nonneg 3) hsψ]
    have f2 : 0 ≤ 3 / 5 * (Real.cos (p 1) - 4 * Real.sin (p 1)) + 2 / 5 * Real.sin (p 1) := by
      linarith
    have key : (Real.cos (p 2) * Real.cos (p 1) + Real.sin (p 2) * Real.sin (p 1)) * (-1 / 2) -
        (Real.sin (p 2) * Real.cos (p 1) - Real.cos (p 2) * Real.sin (p 1)) * (√3 / 2) -
        3 / 10 * ((Real.sin (p 2) * Real.cos (p 1) - Real.cos (p 2) * Real.sin (p 1)) * (-1 / 2) +
          (Real.cos (p 2) * Real.cos (p 1) + Real.sin (p 2) * Real.sin (p 1)) * (√3 / 2)) =
        (-Real.cos (p 2) - √3 * Real.sin (p 2)) * (Real.cos (p 1) * (1 / 2 + 3 * √3 / 20) -
          Real.sin (p 1) * (√3 / 2 - 3 / 20)) +
        Real.sin (p 2) * (3 / 5 * (Real.cos (p 1) - 4 * Real.sin (p 1)) +
          2 / 5 * Real.sin (p 1)) := by
      linear_combination (3 / 20 * Real.sin (p 2) * Real.cos (p 1) -
        1 / 2 * Real.sin (p 2) * Real.sin (p 1)) * hq
    rw [key]
    exact add_nonneg (mul_nonneg e1 f1) (mul_nonneg hs2 f2)
  · nlinarith [mul_le_mul_of_nonpos_left q1.le hc1, mul_nonneg (Real.sqrt_nonneg 3) hs1]
  · nlinarith [mul_le_mul_of_nonpos_left q1.le hc2, mul_nonneg (Real.sqrt_nonneg 3) hs2]

/-- `W₃ ≤ (2√3/3) W₁ W₂`: `W₃ sin φ₁ sin φ₂ = 2√3 sin ψ W₁ W₂`. -/
theorem weight_three_le {p : Fin 3 → ℝ} (hp : p ∈ regionD1) {s : ℝ} (hs : 0 < s) :
    √3 * cκ p * s ^ 3 ≤ 2 * √3 / 3 * ((-(cy₁ p * s) / 2) * (-(cy₂ p * s ^ 2))) := by
  obtain ⟨-, -, -, hsψ, hcψ, h4ψ⟩ := regionD1_trig hp
  obtain ⟨sφ1, sφ2, sφ1', sφ2'⟩ := regionD1_sin_phi hp
  have hr := hp.1
  have hk : 0 ≤ cκ p := mul_nonneg (mul_nonneg (by linarith [hr.2]) hr.1) hsψ
  have hW3 : 0 ≤ √3 * cκ p * s ^ 3 := by positivity
  have hWW : 0 ≤ (-(cy₁ p * s) / 2) * (-(cy₂ p * s ^ 2)) := by
    have e : (-(cy₁ p * s) / 2) * (-(cy₂ p * s ^ 2)) = (1 - p 0) * p 0 * s ^ 3 / 2 *
        (Real.sin (p 2 - p 1 + 2 / 3 * Real.pi) * Real.sin (p 2 + 2 / 3 * Real.pi)) := by
      simp only [cy₁, cy₂]; ring
    rw [e]
    have : 0 ≤ (1 - p 0) * p 0 * s ^ 3 / 2 := by
      have := hr.1; have : 0 ≤ 1 - p 0 := by linarith [hr.2]
      positivity
    exact mul_nonneg this (mul_nonneg_of_nonpos_of_nonpos sφ1 sφ2)
  have eW : √3 * cκ p * s ^ 3 *
      (Real.sin (p 2 - p 1 + 2 / 3 * Real.pi) * Real.sin (p 2 + 2 / 3 * Real.pi)) =
      2 * √3 * Real.sin (p 1) * ((-(cy₁ p * s) / 2) * (-(cy₂ p * s ^ 2))) := by
    simp only [cκ, cy₁, cy₂]; ring
  have hprod : 3 / 4 * Real.cos (p 1) ≤ Real.sin (p 2 - p 1 + 2 / 3 * Real.pi) *
      Real.sin (p 2 + 2 / 3 * Real.pi) := by
    have h1 : 0 ≤ -Real.sin (p 2 - p 1 + 2 / 3 * Real.pi) := neg_nonneg.2 sφ1
    have h0 : (0 : ℝ) ≤ √3 / 2 := by positivity
    have := mul_le_mul sφ1' sφ2' h0 h1
    have hq3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
    nlinarith
  have h1 : √3 * cκ p * s ^ 3 * (3 / 4 * Real.cos (p 1)) ≤
      2 * √3 * (Real.cos (p 1) / 4) * ((-(cy₁ p * s) / 2) * (-(cy₂ p * s ^ 2))) := by
    calc √3 * cκ p * s ^ 3 * (3 / 4 * Real.cos (p 1))
        ≤ √3 * cκ p * s ^ 3 * (Real.sin (p 2 - p 1 + 2 / 3 * Real.pi) *
          Real.sin (p 2 + 2 / 3 * Real.pi)) := mul_le_mul_of_nonneg_left hprod hW3
      _ = 2 * √3 * Real.sin (p 1) * ((-(cy₁ p * s) / 2) * (-(cy₂ p * s ^ 2))) := eW
      _ ≤ 2 * √3 * (Real.cos (p 1) / 4) * ((-(cy₁ p * s) / 2) * (-(cy₂ p * s ^ 2))) := by
        apply mul_le_mul_of_nonneg_right _ hWW
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
  have e : 2 * √3 * (Real.cos (p 1) / 4) * ((-(cy₁ p * s) / 2) * (-(cy₂ p * s ^ 2))) =
      (2 * √3 / 3 * ((-(cy₁ p * s) / 2) * (-(cy₂ p * s ^ 2)))) * (3 / 4 * Real.cos (p 1)) := by
    ring
  rw [e] at h1
  exact le_of_mul_le_mul_right h1 (by positivity)

/-- **The polytope of the normalized image on `D₁`**: the facts on `W₁ = -y₁ s/2`,
`W₃ = √3 κ s³`, `X₁ = x₁ s`, `X₂ = x₂ s²` (`W₂ = 1/12 - W₁ - W₃ = -y₂ s²`). -/
theorem omega_facts {p : Fin 3 → ℝ} (hp : p ∈ regionD1) {s : ℝ} (hs : 0 < s)
    (hsum : -(cy₁ p * s) / 2 - cy₂ p * s ^ 2 + √3 * cκ p * s ^ 3 = 1 / 12) :
    0 ≤ -(cy₁ p * s) / 2 ∧ 0 ≤ √3 * cκ p * s ^ 3 ∧ √3 * cκ p * s ^ 3 ≤ 1 / 480 ∧
    0 ≤ 1 / 12 - -(cy₁ p * s) / 2 - √3 * cκ p * s ^ 3 ∧
    0 ≤ cx₁ p * s + 3 / 5 * (-(cy₁ p * s) / 2) ∧
    0 ≤ 1155 / 1000 * (-(cy₁ p * s) / 2) - cx₁ p * s ∧ 0 ≤ cx₂ p * s ^ 2 ∧
    0 ≤ 578 / 1000 * (1 / 12 - -(cy₁ p * s) / 2 - √3 * cκ p * s ^ 3) - cx₂ p * s ^ 2 := by
  obtain ⟨-, -, -, hsψ, -, -⟩ := regionD1_trig hp
  obtain ⟨sφ1, sφ2, -, -⟩ := regionD1_sin_phi hp
  obtain ⟨cφ1a, cφ1b, cφ2a, cφ2b⟩ := regionD1_cos_phi hp
  have hW := weight_three_le hp hs
  obtain ⟨-, q2⟩ := sqrt_three_bounds
  have hr := hp.1
  have hr1 : 0 ≤ 1 - p 0 := by linarith [hr.2]
  have hr0 : 0 ≤ p 0 := hr.1
  have hy1 : cy₁ p ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hr1 sφ1
  have hy2 : cy₂ p ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hr0 sφ2
  have hk : 0 ≤ cκ p := mul_nonneg (mul_nonneg hr1 hr0) hsψ
  have hW1 : 0 ≤ -(cy₁ p * s) / 2 := by
    have := mul_nonpos_of_nonpos_of_nonneg hy1 hs.le
    linarith
  have hW2 : 0 ≤ -(cy₂ p * s ^ 2) := by
    have := mul_nonpos_of_nonpos_of_nonneg hy2 (sq_nonneg s)
    linarith
  have hW3 : 0 ≤ √3 * cκ p * s ^ 3 := by positivity
  have hW2' : 1 / 12 - -(cy₁ p * s) / 2 - √3 * cκ p * s ^ 3 = -(cy₂ p * s ^ 2) := by linarith
  have hWW : 0 ≤ (-(cy₁ p * s) / 2) * (-(cy₂ p * s ^ 2)) := mul_nonneg hW1 hW2
  have hWW' : (-(cy₁ p * s) / 2) * (-(cy₂ p * s ^ 2)) ≤ 1 / 576 := by
    have : -(cy₁ p * s) / 2 + -(cy₂ p * s ^ 2) ≤ 1 / 12 := by linarith
    nlinarith [sq_nonneg (-(cy₁ p * s) / 2 - -(cy₂ p * s ^ 2))]
  have hW3' : √3 * cκ p * s ^ 3 ≤ 1 / 480 := by
    have : 2 * √3 / 3 * ((-(cy₁ p * s) / 2) * (-(cy₂ p * s ^ 2))) ≤ 2 * 1.7321 / 3 * (1 / 576) :=
      mul_le_mul (by linarith) hWW' hWW (by norm_num)
    linarith
  refine ⟨hW1, hW3, hW3', by rw [hW2']; exact hW2, ?_, ?_, ?_, ?_⟩
  · have e : cx₁ p * s + 3 / 5 * (-(cy₁ p * s) / 2) = (1 - p 0) * s *
        (Real.cos (p 2 - p 1 + 2 / 3 * Real.pi) - 3 / 10 * Real.sin (p 2 - p 1 + 2 / 3 * Real.pi))
        := by
      simp only [cx₁, cy₁]; ring
    rw [e]; positivity
  · have : (1 - p 0) * s * (Real.cos (p 2 - p 1 + 2 / 3 * Real.pi) +
      1155 / 2000 * Real.sin (p 2 - p 1 + 2 / 3 * Real.pi)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) cφ1b
    have e : 1155 / 1000 * (-(cy₁ p * s) / 2) - cx₁ p * s = -((1 - p 0) * s *
        (Real.cos (p 2 - p 1 + 2 / 3 * Real.pi) +
          1155 / 2000 * Real.sin (p 2 - p 1 + 2 / 3 * Real.pi))) := by
      simp only [cx₁, cy₁]; ring
    rw [e]; linarith
  · exact mul_nonneg (mul_nonneg hr0 cφ2a) (sq_nonneg s)
  · rw [hW2']
    have : p 0 * s ^ 2 * (Real.cos (p 2 + 2 / 3 * Real.pi) +
      578 / 1000 * Real.sin (p 2 + 2 / 3 * Real.pi)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) cφ2b
    have e : 578 / 1000 * -(cy₂ p * s ^ 2) - cx₂ p * s ^ 2 = -(p 0 * s ^ 2 *
        (Real.cos (p 2 + 2 / 3 * Real.pi) + 578 / 1000 * Real.sin (p 2 + 2 / 3 * Real.pi))) := by
      simp only [cx₂, cy₂]; ring
    rw [e]; linarith

/-! ### The six inequalities on the polytope -/

section Omega

variable {q W₁ W₃ X₁ X₂ : ℝ}

/-- The hypotheses: the polytope of `(W₁, W₃, X₁, X₂)` and `q = √3`. -/
structure OmegaHyp (q W₁ W₃ X₁ X₂ : ℝ) : Prop where
  hq : q ^ 2 = 3
  g0 : 0 ≤ W₁
  g1 : 0 ≤ W₃
  g2 : 0 ≤ 1 / 480 - W₃
  g3 : 0 ≤ 1 / 12 - W₁ - W₃
  g4 : 0 ≤ X₁ + 3 / 5 * W₁
  g5 : 0 ≤ 1155 / 1000 * W₁ - X₁
  g6 : 0 ≤ X₂
  g7 : 0 ≤ 578 / 1000 * (1 / 12 - W₁ - W₃) - X₂
  g8 : 0 ≤ q - 1732 / 1000
  g9 : 0 ≤ 1 / 10000 - (q - 1732 / 1000)

theorem omega_theta_lo (h : OmegaHyp q W₁ W₃ X₁ X₂) :
    (1 / 6 - W₁ + W₃) + 39 / 80 * (-q / 4 + X₁ + X₂) < 0 := by
  obtain ⟨-, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := h
  linarith

theorem omega_theta_hi (h : OmegaHyp q W₁ W₃ X₁ X₂) :
    -(15 / 112 * (-q / 4 + X₁ + X₂)) - (1 / 6 - W₁ + W₃) < 0 := by
  obtain ⟨-, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := h
  linarith

theorem omega_psi_hi (h : OmegaHyp q W₁ W₃ X₁ X₂) :
    ((-q / 2 + X₁) * (1 / 6 - W₁ + W₃) - (1 / 2 - 2 * W₁) * (-q / 4 + X₁ + X₂)) -
      20 / 99 * ((-q / 2 + X₁) * (-q / 4 + X₁ + X₂) + (1 / 2 - 2 * W₁) * (1 / 6 - W₁ + W₃))
      < 0 := by
  obtain ⟨hq, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := h
  nlinarith [mul_nonneg g0 g1, mul_nonneg g0 g6, mul_nonneg g0 g3, mul_nonneg g6 g1,
    sq_nonneg (X₁ - 3 / 100), mul_nonneg g4 g0, mul_nonneg g5 g0, mul_nonneg g8 g0,
    mul_nonneg g9 g0]

theorem omega_psi_lo (h : OmegaHyp q W₁ W₃ X₁ X₂) :
    25 / 312 * ((-q / 2 + X₁) * (-q / 4 + X₁ + X₂) + (1 / 2 - 2 * W₁) * (1 / 6 - W₁ + W₃)) -
      ((-q / 2 + X₁) * (1 / 6 - W₁ + W₃) - (1 / 2 - 2 * W₁) * (-q / 4 + X₁ + X₂)) < 0 := by
  obtain ⟨hq, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := h
  nlinarith [mul_nonneg g0 g1, mul_nonneg g0 g6, mul_nonneg g0 g3, mul_nonneg g6 g1,
    mul_nonneg g4 g0, mul_nonneg g5 g0, mul_nonneg g8 g0, mul_nonneg g9 g0]

theorem omega_r_hi (h : OmegaHyp q W₁ W₃ X₁ X₂) :
    ((-q / 4 + X₁ + X₂) ^ 2 + (1 / 6 - W₁ + W₃) ^ 2) -
      (30 / 49) ^ 2 * ((-q / 2 + X₁) ^ 2 + (1 / 2 - 2 * W₁) ^ 2) ^ 2 < 0 := by
  obtain ⟨hq, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := h
  have tang := sq_nonneg ((-q / 2 + X₁) ^ 2 + (1 / 2 - 2 * W₁) ^ 2 - 7 / 10)
  have : ((-q / 4 + X₁ + X₂) ^ 2 + (1 / 6 - W₁ + W₃) ^ 2) -
      (30 / 49) ^ 2 * (2 * (7 / 10) * ((-q / 2 + X₁) ^ 2 + (1 / 2 - 2 * W₁) ^ 2) - (7 / 10) ^ 2)
      < 0 := by
    nlinarith [mul_nonneg g0 g5, mul_nonneg g1 g1, mul_nonneg g1 g3, mul_nonneg g1 g4,
      mul_nonneg g1 g5, mul_nonneg g2 g7, mul_nonneg g3 g4, mul_nonneg g3 g5, mul_nonneg g3 g6,
      mul_nonneg g3 g7, mul_nonneg g4 g5, mul_nonneg g4 g6, mul_nonneg g4 g9, mul_nonneg g5 g6,
      mul_nonneg g5 g8, mul_nonneg g6 g7, mul_nonneg g6 g8]
  nlinarith

theorem omega_n1_bounds (h : OmegaHyp q W₁ W₃ X₁ X₂) :
    7 / 10 ≤ (-q / 2 + X₁) ^ 2 + (1 / 2 - 2 * W₁) ^ 2 ∧
      (-q / 2 + X₁) ^ 2 + (1 / 2 - 2 * W₁) ^ 2 ≤ 1 := by
  obtain ⟨hq, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := h
  constructor
  · nlinarith [mul_nonneg g0 g0, mul_nonneg g5 g0, mul_nonneg g8 g0]
  · nlinarith [mul_nonneg g0 g0, mul_nonneg g4 g0, mul_nonneg g5 g0, mul_nonneg g8 g0,
      mul_nonneg g9 g0, mul_nonneg g4 g5]

theorem omega_r_lo (h : OmegaHyp q W₁ W₃ X₁ X₂) :
    (550 / 1521) ^ 2 * ((-q / 2 + X₁) ^ 2 + (1 / 2 - 2 * W₁) ^ 2) ^ 2 -
      ((-q / 4 + X₁ + X₂) ^ 2 + (1 / 6 - W₁ + W₃) ^ 2) < 0 := by
  obtain ⟨n0, n1⟩ := omega_n1_bounds h
  obtain ⟨hq, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := h
  have sec : ((-q / 2 + X₁) ^ 2 + (1 / 2 - 2 * W₁) ^ 2) ^ 2 ≤
      (7 / 10 + 1) * ((-q / 2 + X₁) ^ 2 + (1 / 2 - 2 * W₁) ^ 2) - 7 / 10 := by nlinarith
  have : (550 / 1521) ^ 2 * ((7 / 10 + 1) * ((-q / 2 + X₁) ^ 2 + (1 / 2 - 2 * W₁) ^ 2) - 7 / 10) -
      ((-q / 4 + X₁ + X₂) ^ 2 + (1 / 6 - W₁ + W₃) ^ 2) < 0 := by
    nlinarith [mul_nonneg g1 g1, mul_nonneg g1 g4, mul_nonneg g1 g5, mul_nonneg g1 g6,
      mul_nonneg g1 g7, mul_nonneg g3 g4, mul_nonneg g3 g5, mul_nonneg g3 g7, mul_nonneg g4 g4,
      mul_nonneg g4 g5, mul_nonneg g4 g7, mul_nonneg g4 g9, mul_nonneg g5 g5, mul_nonneg g5 g7,
      mul_nonneg g5 g8, mul_nonneg g6 g9, mul_nonneg g7 g7]
  nlinarith

end Omega

/-! ### `F(D₁) ⊆ B` -/

/-- The lower corner `(11/50, arctan (25/312), π - arctan (39/80))` of `B`. -/
noncomputable def boxLo : Fin 3 → ℝ :=
  ![11 / 50, Real.arctan (25 / 312), Real.pi - Real.arctan (39 / 80)]

/-- The upper corner `(3/10, arctan (20/99), π - arctan (15/112))` of `B`. -/
noncomputable def boxHi : Fin 3 → ℝ :=
  ![3 / 10, Real.arctan (20 / 99), Real.pi - Real.arctan (15 / 112)]

theorem mem_box_iff {p : Fin 3 → ℝ} : p ∈ Icc boxLo boxHi ↔
    p 0 ∈ Icc (11 / 50) (3 / 10) ∧ p 1 ∈ Icc (Real.arctan (25 / 312)) (Real.arctan (20 / 99)) ∧
      p 2 ∈ Icc (Real.pi - Real.arctan (39 / 80)) (Real.pi - Real.arctan (15 / 112)) := by
  simp only [mem_Icc, Pi.le_def, Fin.forall_fin_succ, boxLo, boxHi]
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
  constructor
  · rintro ⟨⟨a0, a1, a2, -⟩, ⟨b0, b1, b2, -⟩⟩
    exact ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩⟩
  · rintro ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩⟩
    exact ⟨⟨a0, a1, a2, fun i ↦ i.elim0⟩, ⟨b0, b1, b2, fun i ↦ i.elim0⟩⟩

theorem arctan_bounds : 0 < Real.arctan (25 / 312) ∧ Real.arctan (20 / 99) < Real.arctan (1 / 4) ∧
    Real.arctan (39 / 80) < Real.pi / 6 ∧ 0 < Real.arctan (15 / 112) := by
  refine ⟨Real.arctan_pos.2 (by norm_num), Real.arctan_lt_arctan_iff.2 (by norm_num), ?_,
    Real.arctan_pos.2 (by norm_num)⟩
  rw [← Real.arctan_inv_sqrt_three, Real.arctan_lt_arctan_iff]
  rw [lt_inv_comm₀ (by norm_num) (by positivity)]
  rw [Real.sqrt_lt' (by norm_num)]
  norm_num

/-- `B ⊆ D₁`. -/
theorem box_subset_regionD1 : Icc boxLo boxHi ⊆ regionD1 := by
  intro p hp
  obtain ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩⟩ := mem_box_iff.1 hp
  obtain ⟨h1, h2, h3, h4⟩ := arctan_bounds
  have hpi := Real.pi_gt_three
  refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- `B` lies in the open first big cell. -/
theorem box_subset_openBoxOne : Icc boxLo boxHi ⊆ openBoxOne := by
  intro p hp
  obtain ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩⟩ := mem_box_iff.1 hp
  obtain ⟨h1, h2, h3, h4⟩ := arctan_bounds
  have := arctan_quarter_lt
  have hpi := Real.pi_gt_three
  have h5 := Real.arctan_pos.2 (show (0 : ℝ) < 39 / 80 by norm_num)
  refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- **`F(D₁) ⊆ B`**: for `p ∈ D₁`, the cell coordinates of `ζ F(z)` lie in `B` and represent the
image class.

Departure from the paper: the book states that the forward iterates of `𝒟_out` shrink toward
`q_out` from a Mathematica computation (TeX 12592–12598); the formalization proves the step
`F(D₁) ⊆ B` analytically: in the normalisation `τ = 1` (`normalized_eqs`) the image is an affine
function of `(W₁, W₃, X₁, X₂)`, which lie in an explicit polytope on `D₁` (`omega_facts`, signs of
sines and cosines), and the six inequalities of `B` are polynomial inequalities on that polytope
(`omega_theta_lo`, …, `omega_r_lo`, by `linarith`/`nlinarith`). -/
theorem image_mem_box {p : Fin 3 → ℝ} (hp : p ∈ regionD1) :
    cellCoords (ζ • poincare (cellPoint p)) ∈ Icc boxLo boxHi ∧
      poincareAngZero (cellClass p) = cellClass (cellCoords (ζ • poincare (cellPoint p))) := by
  have hp0 := regionD1_subset hp
  obtain ⟨τ, hτ0, h0, -, -⟩ := exists_root hp0 (not_face_of_mem_regionD1 hp)
  obtain ⟨hV₁, w, hw, himage, e0r, e0i, e1r, e1i, c0, c1, h1, h2⟩ := image_spec hp0 hτ0 h0
  rw [← hw]
  refine ⟨?_, himage⟩
  obtain ⟨eU0, eV0, eU1, eV1, hsum⟩ := normalized_eqs hτ0 h0
  have hs : 0 < τ⁻¹ := inv_pos.2 hτ0
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ := omega_facts hp hs hsum
  obtain ⟨q1, q2⟩ := sqrt_three_bounds
  have H : OmegaHyp √3 (-(cy₁ p * τ⁻¹) / 2) (√3 * cκ p * τ⁻¹ ^ 3) (cx₁ p * τ⁻¹)
      (cx₂ p * τ⁻¹ ^ 2) :=
    ⟨Real.sq_sqrt (by norm_num), g0, g1, by linarith, g3, g4, g5, g6, g7, by linarith,
      by linarith⟩
  -- the normalized coordinates
  have ev0 : 1 / 2 + cy₁ p * τ⁻¹ = 1 / 2 - 2 * (-(cy₁ p * τ⁻¹) / 2) := by ring
  have ev1 : 1 / 6 + cy₁ p * τ⁻¹ / 2 + √3 * cκ p * τ⁻¹ ^ 3 =
      1 / 6 - -(cy₁ p * τ⁻¹) / 2 + √3 * cκ p * τ⁻¹ ^ 3 := by ring
  rw [ev0] at eV0
  rw [ev1] at eV1
  set u0 := -√3 / 2 + cx₁ p * τ⁻¹ with hu0
  set v0 := 1 / 2 - 2 * (-(cy₁ p * τ⁻¹) / 2) with hv0
  set u1 := -√3 / 4 + cx₁ p * τ⁻¹ + cx₂ p * τ⁻¹ ^ 2 with hu1
  set v1 := 1 / 6 - -(cy₁ p * τ⁻¹) / 2 + √3 * cκ p * τ⁻¹ ^ 3 with hv1
  have k1 := omega_theta_lo H
  have k2 := omega_theta_hi H
  have k3 := omega_psi_hi H
  have k4 := omega_psi_lo H
  have k5 := omega_r_hi H
  have k6 := omega_r_lo H
  have ht2 : 0 < τ ^ 2 := by positivity
  have ht3 : 0 < τ ^ 3 := by positivity
  have ht4 : 0 < τ ^ 4 := by positivity
  rw [mem_box_iff]
  have hw1 : w 1 ≠ 0 := fun h ↦ by rw [h] at e1i; simp at e1i; linarith
  -- `θ₂`
  obtain ⟨t1, hre⟩ := pi_sub_arctan_lt_arg (w := w 1) (K := 39 / 80) (by norm_num)
    (by rw [e1i]; exact hV₁) (by
      rw [e1i, e1r, eU1, eV1]
      have : τ ^ 2 * v1 + 39 / 80 * (τ ^ 2 * u1) = τ ^ 2 * (v1 + 39 / 80 * u1) := by ring
      rw [this]; exact mul_neg_of_pos_of_neg ht2 k1)
  have t2 := arg_lt_pi_sub_arctan (w := w 1) (K := 15 / 112) hre (by rw [e1i]; exact hV₁.le) (by
    rw [e1i, e1r, eU1, eV1]
    have : -(15 / 112 * (τ ^ 2 * u1)) - τ ^ 2 * v1 = τ ^ 2 * (-(15 / 112 * u1) - v1) := by ring
    rw [this]; exact mul_neg_of_pos_of_neg ht2 k2)
  -- `ψ`
  obtain ⟨p1, hcos⟩ := toIcoMod_lt_arctan (w₀ := w 0) (w₁ := w 1) (T := 20 / 99) (by norm_num) c1
    (by
      rw [e0r, e0i, e1r, e1i, eU0, eV0, eU1, eV1]
      have : (τ * u0 * (τ ^ 2 * v1) - τ * v0 * (τ ^ 2 * u1)) -
          20 / 99 * (τ * u0 * (τ ^ 2 * u1) + τ * v0 * (τ ^ 2 * v1)) =
          τ ^ 3 * ((u0 * v1 - v0 * u1) - 20 / 99 * (u0 * u1 + v0 * v1)) := by ring
      rw [this]; exact mul_neg_of_pos_of_neg ht3 k3)
  have p2 := arctan_lt_toIcoMod (w₀ := w 0) (w₁ := w 1) (T := 25 / 312) c1 hcos (by
    rw [e0r, e0i, e1r, e1i, eU0, eV0, eU1, eV1]
    have : 25 / 312 * (τ * u0 * (τ ^ 2 * u1) + τ * v0 * (τ ^ 2 * v1)) -
        (τ * u0 * (τ ^ 2 * v1) - τ * v0 * (τ ^ 2 * u1)) =
        τ ^ 3 * (25 / 312 * (u0 * u1 + v0 * v1) - (u0 * v1 - v0 * u1)) := by ring
    rw [this]; exact mul_neg_of_pos_of_neg ht3 k4)
  -- `r₂`
  have r1 := cellCoords_zero_lt (w := w) (R := 3 / 10) (by norm_num) (by norm_num) c0 hw1 (by
    rw [norm_sq_eq, norm_sq_eq, e0r, e0i, e1r, e1i, eU0, eV0, eU1, eV1]
    have : (3 / 10 : ℝ) / (1 - 3 / 10) ^ 2 = 30 / 49 := by norm_num
    rw [this]
    have : (τ ^ 2 * u1) ^ 2 + (τ ^ 2 * v1) ^ 2 - (30 / 49) ^ 2 * ((τ * u0) ^ 2 + (τ * v0) ^ 2) ^ 2 =
        τ ^ 4 * ((u1 ^ 2 + v1 ^ 2) - (30 / 49) ^ 2 * (u0 ^ 2 + v0 ^ 2) ^ 2) := by ring
    rw [this]; exact mul_neg_of_pos_of_neg ht4 k5)
  have r0 := lt_cellCoords_zero (w := w) (R := 11 / 50) (by norm_num) (by norm_num) c0 hw1 (by
    rw [norm_sq_eq, norm_sq_eq, e0r, e0i, e1r, e1i, eU0, eV0, eU1, eV1]
    have : (11 / 50 : ℝ) / (1 - 11 / 50) ^ 2 = 550 / 1521 := by norm_num
    rw [this]
    have : (550 / 1521) ^ 2 * ((τ * u0) ^ 2 + (τ * v0) ^ 2) ^ 2 -
        ((τ ^ 2 * u1) ^ 2 + (τ ^ 2 * v1) ^ 2) =
        τ ^ 4 * ((550 / 1521) ^ 2 * (u0 ^ 2 + v0 ^ 2) ^ 2 - (u1 ^ 2 + v1 ^ 2)) := by ring
    rw [this]; exact mul_neg_of_pos_of_neg ht4 k6)
  refine ⟨⟨r0.le, r1.le⟩, ⟨by rw [h1]; exact p2.le, by rw [h1]; exact p1.le⟩,
    ⟨by rw [h2]; exact t1.le, by rw [h2]; exact t2.le⟩⟩

end SmoothedPolygons.TriFuller.DOutAnalytic
