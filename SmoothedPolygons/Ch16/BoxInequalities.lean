module

public import SmoothedPolygons.Ch16.BoxFlow
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The image inequalities on the boxes `𝒟_{ij}`, without computer assistance

At the switch to `1` (the root `τ` of `D = V₂`, `SmoothedPolygons/Ch16/BoxFlow.lean`) the rotated
image `w = ζ F(z)` has `w₁ = U₀ + i V₀`, `w₂ = U₁ + i V₁`; its angle `ψ' < π/3` exactly when
`C₁ = U₀ (V₁ - √3 U₁) - V₀ (U₁ + √3 V₁) < 0` (`toIcoMod_lt_pi_div_three`). The inequalities
`C₁ < 0` needed by `BoxSubclaims` are proved by **exact identities**: a multiple of `C₁` plus a
multiple of `D` (which vanishes at `τ`) is a sum of terms of fixed sign on the box, a quadratic
form in `(r₁, τ)` being bounded by the discriminant.

* `C₁_eq_three`: `√3 C₁ + 3 D = -r₁ r₂ (3 cos ψ + 2√3 sin ψ) - √3 r₂ τ sin(θ₂ + π/6)
  + τ (-3 r₁² + e r₁ τ - (5/4) τ²)` with `e = -(7√3 cos θ₁ + 9 sin θ₁)/4`; since `e² ≤ 57/4 <
  15`, `C₁ < 0` whenever `3 cos ψ + 2√3 sin ψ ≥ 0` and `sin(θ₂ + π/6) ≥ 0`
  (`C₁_neg_of_three`): the boxes `𝒟₀₁`, `𝒟₀₂`, `𝒟₁₁`, `𝒟₁₂`.
* `C₁_eq_four`: `τ √3 C₁ + (5 τ + (9/2) r₁) D = τ² (γ τ² + β r₁ τ + α r₁²)
  + r₂ (e τ² + m r₁ τ + n r₁²)`, with `γ = -13/12`, `α = -3 + (9/8)(√3 cos θ₁ - sin θ₁)`,
  `β = -(5√3/4) cos θ₁ - (11/4) sin θ₁ + 3/8`, `e = (√3/2) cos θ₂ - (5/2) sin θ₂`,
  `m = -3 cos ψ - 4√3 sin ψ + (9/4)(√3 cos θ₂ - sin θ₂)`, `n = -(9/2)√3 sin ψ`
  (`C₁_neg_of_four`): the boxes `𝒟₁₀`, `𝒟₂₀` (`θ₂ ∈ [π - 1.1, π]`), where `ψ` reaches `π`
  and no identity of the first kind exists (the coefficient of `r₁ r₂` in `√3 C₁ + λ D` is `3` at
  `ψ = π` for every `λ`).
* `twoU₁_sub_V₁_eq`: `τ (2 U₁ - V₁) + 2 Y = -(√3/2 + 1/12) τ³ - r₂ τ ((1 + √3/2) cos θ₂ - (5/2 - √3)
  sin θ₂) - r₁ τ² ((1 + √3/2) cos θ₁ + (√3 - 3/2) sin θ₁)`: on `𝒟₀₂`, where `Y(τ) ≥ 0` (no switch
  to `ζ²` before `τ`), `2 U₁ < V₁`, so `θ₂' > π/2 - arctan(1/2) > 1.1`.
* `C₂_eq` (`DOutInvariant.lean`) gives `θ₂' > 2π/3` on `𝒟₀₁`.

The numerical constants are `cos 1.1 > 9/20`, `sin 1.1 < 9/10` and `cos(1.1 - π/6) ≥ 3/4`, from
`1.1 = π/3 + δ`, `δ < 0.053`, and `cos x ≥ 1 - x²/2`, `sin x ≤ x`.
-/

@[expose] public section

namespace SmoothedPolygons.TriFuller.BoxAnalytic

open Set DOutAnalytic

/-! ### Numerical constants -/

theorem lt_cos_eleven_tenths : 9 / 20 < Real.cos 1.1 := by
  have hpi := Real.pi_gt_d4
  have h3 : √3 < 1.7321 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  set δ := (1.1 : ℝ) - Real.pi / 3 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith [Real.pi_lt_d2]
  have hδ1 : δ < 0.0529 := by rw [hδ]; norm_num at hpi ⊢; linarith
  have e : (1.1 : ℝ) = Real.pi / 3 + δ := by rw [hδ]; ring
  rw [e, Real.cos_add, Real.cos_pi_div_three, Real.sin_pi_div_three]
  have hc := Real.one_sub_sq_div_two_le_cos (x := δ)
  have hs := (Real.sin_lt hδ0).le
  have hs0 : 0 ≤ Real.sin δ := Real.sin_nonneg_of_nonneg_of_le_pi hδ0.le (by linarith)
  have : √3 / 2 * Real.sin δ ≤ 1.7321 / 2 * δ := by
    have := Real.sqrt_nonneg 3
    nlinarith
  norm_num at this hδ1 ⊢
  nlinarith

private theorem sin_eleven_tenths_lt : Real.sin 1.1 < 9 / 10 := by
  have hpi := Real.pi_gt_d4
  have h3 : √3 < 1.7321 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  set δ := (1.1 : ℝ) - Real.pi / 3 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith [Real.pi_lt_d2]
  have hδ1 : δ < 0.0529 := by rw [hδ]; norm_num at hpi ⊢; linarith
  have e : (1.1 : ℝ) = Real.pi / 3 + δ := by rw [hδ]; ring
  rw [e, Real.sin_add, Real.cos_pi_div_three, Real.sin_pi_div_three]
  have hc := Real.cos_le_one δ
  have hs := (Real.sin_lt hδ0).le
  have : √3 / 2 * Real.cos δ ≤ 1.7321 / 2 := by
    have := Real.sqrt_nonneg 3
    have := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (x := δ) (by linarith [Real.pi_pos])
      (by linarith [Real.pi_gt_three])
    nlinarith
  norm_num at this hδ1 ⊢
  nlinarith

/-- `cos x ≥ cos 1.1 > 9/20` and `sin x ≥ -sin 1.1 > -9/10` for `x ∈ [-1.1, 0]`. -/
theorem cos_sin_bounds_of_mem_neg {x : ℝ} (h1 : -1.1 ≤ x) (h2 : x ≤ 0) :
    9 / 20 < Real.cos x ∧ -(9 / 10) < Real.sin x := by
  have hpi := Real.pi_gt_three
  have hc := lt_cos_eleven_tenths
  have hs := sin_eleven_tenths_lt
  constructor
  · rw [← Real.cos_neg x]
    have : Real.cos 1.1 ≤ Real.cos (-x) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by norm_num; linarith) (by linarith)
    linarith
  · have : Real.sin (-1.1) ≤ Real.sin x :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by norm_num; linarith) (by linarith) h1
    rw [Real.sin_neg] at this
    linarith

/-- `cos(θ + π/6) ≤ -3/4` on `θ ∈ [π - 1.1, π]`, as `√3 cos θ - sin θ ≤ -3/2`. -/
theorem sqrt_three_mul_cos_sub_sin_le {θ : ℝ} (h1 : Real.pi - 1.1 ≤ θ) (h2 : θ ≤ Real.pi) :
    √3 * Real.cos θ - Real.sin θ ≤ -(3 / 2) := by
  have hpi := Real.pi_gt_d4
  have hpi' := Real.pi_lt_d4
  -- `cos (θ - 5π/6) = -(√3/2) cos θ + (1/2) sin θ ≥ cos 0.577 ≥ 3/4`
  have e : Real.cos (θ - 5 * Real.pi / 6) = -(√3 / 2) * Real.cos θ + 1 / 2 * Real.sin θ := by
    rw [Real.cos_sub, show 5 * Real.pi / 6 = Real.pi - Real.pi / 6 by ring, Real.cos_pi_sub,
      Real.sin_pi_sub, Real.cos_pi_div_six, Real.sin_pi_div_six]
    ring
  have hb : 3 / 4 ≤ Real.cos (θ - 5 * Real.pi / 6) := by
    have hx : |θ - 5 * Real.pi / 6| ≤ 0.577 := by
      rw [abs_le]; norm_num at h1 hpi hpi' ⊢; constructor <;> linarith
    have := Real.one_sub_sq_div_two_le_cos (x := θ - 5 * Real.pi / 6)
    have : (θ - 5 * Real.pi / 6) ^ 2 ≤ 0.577 ^ 2 := by
      rw [← sq_abs]
      have := abs_nonneg (θ - 5 * Real.pi / 6)
      nlinarith
    norm_num at this ⊢
    linarith
  rw [e] at hb
  linarith

/-! ### `C₁ < 0` by the multiplier `3` -/

/-- **The identity for `C₁` with the multiplier `3`.** -/
private theorem C₁_eq_three (p : Fin 3 → ℝ) (t : ℝ) :
    √3 * (U₀ p t * (V₁ p t - √3 * U₁ p t) - V₀ p t * (U₁ p t + √3 * V₁ p t)) + 3 * V₂ p t =
      -((1 - p 0) * p 0 * (3 * Real.cos (p 1) + 2 * √3 * Real.sin (p 1))) -
        √3 * p 0 * t * (Real.cos (p 2) / 2 + √3 * Real.sin (p 2) / 2) +
        t * (-3 * (1 - p 0) ^ 2 +
          (-(7 * √3 * Real.cos (p 2 - p 1) + 9 * Real.sin (p 2 - p 1)) / 4) * (1 - p 0) * t -
          5 / 4 * t ^ 2) := by
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
    q^2*t^3/8 - r^2*s1^2*t + r^2*s1*s2 + 2*r*s1^2*t - r*s1*s2 + r*s1*t^2/2 + r*s2*t/2 -
    s1^2*t - s1*t^2/2 - t^3/2) * hq + (-3*r^2*t + 6*r*t - 3*t) * hs

/-- **`C₁ < 0` at a positive root of `D`** when `3 cos ψ + 2√3 sin ψ ≥ 0` and
`cos θ₂ + √3 sin θ₂ ≥ 0` (`r₂ ∈ [0, 1]`). -/
theorem C₁_neg_of_three {p : Fin 3 → ℝ} (h0 : 0 ≤ p 0) (h0' : p 0 ≤ 1)
    (hψ : 0 ≤ 3 * Real.cos (p 1) + 2 * √3 * Real.sin (p 1))
    (hθ : 0 ≤ Real.cos (p 2) + √3 * Real.sin (p 2)) {τ : ℝ} (hτ : 0 < τ) (h : V₂ p τ = 0) :
    U₀ p τ * (V₁ p τ - √3 * U₁ p τ) - V₀ p τ * (U₁ p τ + √3 * V₁ p τ) < 0 := by
  have hq : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  have hq2 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have e := C₁_eq_three p τ
  rw [h, mul_zero, add_zero] at e
  have hr1 : 0 ≤ 1 - p 0 := by linarith
  set e1 := -(7 * √3 * Real.cos (p 2 - p 1) + 9 * Real.sin (p 2 - p 1)) / 4 with he1
  have he1sq : e1 ^ 2 ≤ 57 / 4 := by
    have hs : Real.cos (p 2 - p 1) ^ 2 + Real.sin (p 2 - p 1) ^ 2 = 1 :=
      Real.cos_sq_add_sin_sq _
    have : (7 * √3 * Real.cos (p 2 - p 1) + 9 * Real.sin (p 2 - p 1)) ^ 2 +
        (9 * Real.cos (p 2 - p 1) - 7 * √3 * Real.sin (p 2 - p 1)) ^ 2 = 228 := by
      linear_combination (49 * Real.cos (p 2 - p 1) ^ 2 + 49 * Real.sin (p 2 - p 1) ^ 2) * hq2 +
        228 * hs
    rw [he1]
    nlinarith [sq_nonneg (9 * Real.cos (p 2 - p 1) - 7 * √3 * Real.sin (p 2 - p 1))]
  have t1 : 0 ≤ (1 - p 0) * p 0 * (3 * Real.cos (p 1) + 2 * √3 * Real.sin (p 1)) := by positivity
  have t2 : 0 ≤ √3 * p 0 * τ * (Real.cos (p 2) / 2 + √3 * Real.sin (p 2) / 2) := by
    have : 0 ≤ Real.cos (p 2) / 2 + √3 * Real.sin (p 2) / 2 := by linarith
    positivity
  have t3 : -3 * (1 - p 0) ^ 2 + e1 * (1 - p 0) * τ - 5 / 4 * τ ^ 2 < 0 := by
    nlinarith [sq_nonneg (6 * (1 - p 0) - e1 * τ), sq_pos_of_pos hτ]
  have : √3 * (U₀ p τ * (V₁ p τ - √3 * U₁ p τ) - V₀ p τ * (U₁ p τ + √3 * V₁ p τ)) < 0 := by
    rw [e]; nlinarith [mul_neg_of_pos_of_neg hτ t3]
  exact neg_of_mul_neg_right this hq.le

/-! ### `C₁ < 0` by a multiplier of weight one -/

/-- **The identity for `C₁` with the multiplier `5 τ + (9/2) r₁`.** -/
private theorem C₁_eq_four (p : Fin 3 → ℝ) (t : ℝ) :
    t * √3 * (U₀ p t * (V₁ p t - √3 * U₁ p t) - V₀ p t * (U₁ p t + √3 * V₁ p t)) +
        (5 * t + 9 / 2 * (1 - p 0)) * V₂ p t =
      t ^ 2 * (-(13 / 12) * t ^ 2 +
          (-(5 * √3 / 4) * Real.cos (p 2 - p 1) - 11 / 4 * Real.sin (p 2 - p 1) + 3 / 8) *
            (1 - p 0) * t +
          (-3 + 9 / 8 * (√3 * Real.cos (p 2 - p 1) - Real.sin (p 2 - p 1))) * (1 - p 0) ^ 2) +
        p 0 * ((√3 / 2 * Real.cos (p 2) - 5 / 2 * Real.sin (p 2)) * t ^ 2 +
          (-3 * Real.cos (p 1) - 4 * √3 * Real.sin (p 1) +
            9 / 4 * (√3 * Real.cos (p 2) - Real.sin (p 2))) * (1 - p 0) * t +
          (-(9 / 2) * √3 * Real.sin (p 1)) * (1 - p 0) ^ 2) := by
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
  linear_combination (-c1^2*q^2*r^2*t^2/4 + c1^2*q^2*r*t^2/2 - c1^2*q^2*t^2/4 - c1^2*r^2*t^2 +
    2*c1^2*r*t^2 - c1^2*t^2 + c1*c2*q^2*r^2*t/4 - c1*c2*q^2*r*t/4 + c1*c2*r^2*t - c1*c2*r*t -
    c1*q*r^2*s2*t/4 + c1*q*r*s2*t/4 + 7*c1*q*r*t^3/8 - 7*c1*q*t^3/8 + c2*q*r^2*s1*t/4 -
    c2*q*r*s1*t/4 - 3*c2*q*r*t^2/4 - q^2*r^2*s1^2*t^2/4 + q^2*r^2*s1*s2*t/4 +
    q^2*r*s1^2*t^2/2 - q^2*r*s1*s2*t/4 + 3*q^2*r*s1*t^3/8 - q^2*r*s2*t^2/4 - q^2*s1^2*t^2/4 -
    3*q^2*s1*t^3/8 - q^2*t^4/8 - r^2*s1^2*t^2 + r^2*s1*s2*t + 2*r*s1^2*t^2 - r*s1*s2*t +
    r*s1*t^3/2 - s1^2*t^2 - s1*t^3/2 - t^4/2) * hq + (-3*r^2*t^2 + 6*r*t^2 - 3*t^2) * hs

/-- The quadratic form `γ τ² + β r₁ τ + α r₁²` of `C₁_eq_four` is negative for `τ > 0` when
`θ₁ ∈ [-1.1, 2π/3]`: for `sin θ₁ ≥ 0` all its coefficients are `≤ 0`; for `sin θ₁ < 0`
(`cos θ₁ > 9/20`, `sin θ₁ > -9/10`) its discriminant is negative. -/
private theorem quad_neg {c s r t : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (hc : -(1 / 2) ≤ c)
    (hneg : s < 0 → 9 / 20 < c ∧ -(9 / 10) < s) (hr : 0 ≤ r) (ht : 0 < t) :
    -(13 / 12) * t ^ 2 + (-(5 * √3 / 4) * c - 11 / 4 * s + 3 / 8) * r * t +
      (-3 + 9 / 8 * (√3 * c - s)) * r ^ 2 < 0 := by
  have hq : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hq1 : 1.732 < √3 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hq2 : √3 < 1.7321 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  -- `√3 c - s ≤ 2`, so `α ≤ -3/4`
  have hα : √3 * c - s ≤ 2 := by
    nlinarith [sq_nonneg (c + √3 * s), sq_nonneg (√3 * c - s - 2)]
  rcases le_or_gt 0 s with hs | hs
  · -- `β ≤ 0`
    have hβ : -(5 * √3 / 4) * c - 11 / 4 * s + 3 / 8 ≤ 0 := by
      rcases le_or_gt 0 c with hc0 | hc0
      · nlinarith [sq_nonneg (c - s)]
      · have : 3 / 4 ≤ s ^ 2 := by nlinarith
        have : √3 / 2 ≤ s := by nlinarith [sq_nonneg (s - √3 / 2)]
        nlinarith
    have : (-(5 * √3 / 4) * c - 11 / 4 * s + 3 / 8) * r * t ≤ 0 := by
      have := mul_nonneg hr ht.le
      nlinarith
    have : (-3 + 9 / 8 * (√3 * c - s)) * r ^ 2 ≤ 0 := by
      have := sq_nonneg r
      nlinarith
    nlinarith [sq_pos_of_pos ht]
  · obtain ⟨hc', hs'⟩ := hneg hs
    set β := -(5 * √3 / 4) * c - 11 / 4 * s + 3 / 8 with hβ
    set α := -3 + 9 / 8 * (√3 * c - s) with hαdef
    have hα0 : α ≤ -(3 / 4) := by rw [hαdef]; linarith
    -- the discriminant: `β² < (13/3) (-α)`
    have hdisc : β ^ 2 + 1 ≤ 13 / 3 * -α := by
      rw [hβ, hαdef]
      nlinarith [mul_pos (by linarith : (0 : ℝ) < c - 9 / 20) (by linarith : (0 : ℝ) < -s),
        mul_pos (by linarith : (0 : ℝ) < s + 9 / 10) (by linarith : (0 : ℝ) < -s),
        mul_pos (by linarith : (0 : ℝ) < c - 9 / 20) (by linarith : (0 : ℝ) < s + 9 / 10)]
    -- `-4α Q = -(2α r + β t)² - (4αγ - β²) t²`
    have key : -4 * α * (-(13 / 12) * t ^ 2 + β * r * t + α * r ^ 2) =
        -(2 * α * r + β * t) ^ 2 - (13 / 3 * -α - β ^ 2) * t ^ 2 := by ring
    have : -4 * α * (-(13 / 12) * t ^ 2 + β * r * t + α * r ^ 2) < 0 := by
      rw [key]; nlinarith [sq_nonneg (2 * α * r + β * t), sq_pos_of_pos ht]
    nlinarith

/-- **`C₁ < 0` at a positive root of `D` on `θ₂ ∈ [π - 1.1, π]`, `ψ ∈ [π/3, π]`** (the boxes
`𝒟₁₀`, `𝒟₂₀`), from `C₁_eq_four`: `e, m, n ≤ 0` (`sin θ₂ ≥ 0`,
`cos(θ₂ + π/6) ≤ -3/4`, `sin ψ ≥ 0`) and the quadratic form of `quad_neg`
(`θ₁ ∈ [-1.1, 2π/3]`). -/
theorem C₁_neg_of_four {p : Fin 3 → ℝ} (h0 : 0 ≤ p 0) (h0' : p 0 ≤ 1)
    (hs2 : 0 ≤ Real.sin (p 2))
    (hcB : √3 * Real.cos (p 2) - Real.sin (p 2) ≤ -(3 / 2)) (hsψ : 0 ≤ Real.sin (p 1))
    (hc1 : -(1 / 2) ≤ Real.cos (p 2 - p 1))
    (hneg : Real.sin (p 2 - p 1) < 0 →
      9 / 20 < Real.cos (p 2 - p 1) ∧ -(9 / 10) < Real.sin (p 2 - p 1))
    {τ : ℝ} (hτ : 0 < τ) (h : V₂ p τ = 0) :
    U₀ p τ * (V₁ p τ - √3 * U₁ p τ) - V₀ p τ * (U₁ p τ + √3 * V₁ p τ) < 0 := by
  have hq : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  have e := C₁_eq_four p τ
  rw [h, mul_zero, add_zero] at e
  have hr1 : 0 ≤ 1 - p 0 := by linarith
  have hQ := quad_neg (Real.cos_sq_add_sin_sq (p 2 - p 1)) hc1 hneg hr1 hτ
  have hcψ := Real.neg_one_le_cos (p 1)
  have he : √3 / 2 * Real.cos (p 2) - 5 / 2 * Real.sin (p 2) ≤ 0 := by nlinarith
  have hm : -3 * Real.cos (p 1) - 4 * √3 * Real.sin (p 1) +
      9 / 4 * (√3 * Real.cos (p 2) - Real.sin (p 2)) ≤ 0 := by nlinarith
  have hn : -(9 / 2) * √3 * Real.sin (p 1) ≤ 0 := by nlinarith
  have hR : p 0 * ((√3 / 2 * Real.cos (p 2) - 5 / 2 * Real.sin (p 2)) * τ ^ 2 +
      (-3 * Real.cos (p 1) - 4 * √3 * Real.sin (p 1) +
        9 / 4 * (√3 * Real.cos (p 2) - Real.sin (p 2))) * (1 - p 0) * τ +
      (-(9 / 2) * √3 * Real.sin (p 1)) * (1 - p 0) ^ 2) ≤ 0 := by
    apply mul_nonpos_of_nonneg_of_nonpos h0
    have : 0 ≤ (1 - p 0) * τ := mul_nonneg hr1 hτ.le
    nlinarith [sq_nonneg τ, sq_nonneg (1 - p 0)]
  have : τ * √3 * (U₀ p τ * (V₁ p τ - √3 * U₁ p τ) - V₀ p τ * (U₁ p τ + √3 * V₁ p τ)) < 0 := by
    rw [e]; nlinarith [mul_neg_of_pos_of_neg (sq_pos_of_pos hτ) hQ]
  have := neg_of_mul_neg_right this (mul_pos hτ hq).le
  exact this

/-! ### `θ₂' > 1.1` on `𝒟₀₂` -/

private theorem twoU₁_sub_V₁_eq (p : Fin 3 → ℝ) (t : ℝ) :
    t * (2 * U₁ p t - V₁ p t) + 2 * imZ₃ p t =
      -(√3 / 2 + 1 / 12) * t ^ 3 -
        p 0 * t * ((1 + √3 / 2) * Real.cos (p 2) - (5 / 2 - √3) * Real.sin (p 2)) -
        (1 - p 0) * t ^ 2 * ((1 + √3 / 2) * Real.cos (p 2 - p 1) +
          (√3 - 3 / 2) * Real.sin (p 2 - p 1)) := by
  simp only [U₁, V₁, imZ₃, cx₁, cy₁, cx₂, cy₂, cos_add_two_thirds_pi, sin_add_two_thirds_pi]
  ring

/-- **`2 U₁ < V₁` at the switch to `1`** when `Y(τ) ≥ 0` and the coefficients of
`twoU₁_sub_V₁_eq` are `≥ 0`. -/
theorem twoU₁_sub_V₁_neg {p : Fin 3 → ℝ} (h0 : 0 ≤ p 0) (h0' : p 0 ≤ 1)
    (h2 : 0 ≤ (1 + √3 / 2) * Real.cos (p 2) - (5 / 2 - √3) * Real.sin (p 2))
    (h1 : 0 ≤ (1 + √3 / 2) * Real.cos (p 2 - p 1) + (√3 - 3 / 2) * Real.sin (p 2 - p 1))
    {τ : ℝ} (hτ : 0 < τ) (hY : 0 ≤ imZ₃ p τ) : 2 * U₁ p τ - V₁ p τ < 0 := by
  have hq : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  have e := twoU₁_sub_V₁_eq p τ
  have hr1 : 0 ≤ 1 - p 0 := by linarith
  have t1 : 0 ≤ p 0 * τ * ((1 + √3 / 2) * Real.cos (p 2) - (5 / 2 - √3) * Real.sin (p 2)) := by
    positivity
  have t2 : 0 ≤ (1 - p 0) * τ ^ 2 * ((1 + √3 / 2) * Real.cos (p 2 - p 1) +
      (√3 - 3 / 2) * Real.sin (p 2 - p 1)) := by positivity
  have t3 : 0 < (√3 / 2 + 1 / 12) * τ ^ 3 := by positivity
  have : τ * (2 * U₁ p τ - V₁ p τ) < 0 := by linarith
  exact neg_of_mul_neg_right this hτ.le

/-- `θ₂' = arg w ≥ 1.1` when `Im w > 0` and `2 Re w < Im w` (`cot 1.1 > 1/2`). -/
theorem eleven_tenths_le_arg {w : ℂ} (him : 0 < w.im) (h : 2 * w.re - w.im < 0) :
    1.1 ≤ Complex.arg w := by
  have hc := lt_cos_eleven_tenths
  have hs := sin_eleven_tenths_lt
  have hs0 : 0 < Real.sin 1.1 :=
    Real.sin_pos_of_pos_of_lt_pi (by norm_num) (by linarith [Real.pi_gt_three])
  refine le_arg_of_im_pos him (by linarith [Real.pi_gt_three]) ?_
  nlinarith

/-- `C₂ = V₁ + √3 U₁ < 0` for `t > 0` when `sin θ₁, sin θ₂ ≥ 0` (`C₂_eq`). -/
theorem C₂_neg_of_sin_nonneg {p : Fin 3 → ℝ} (h0 : 0 ≤ p 0) (h0' : p 0 ≤ 1)
    (hs1 : 0 ≤ Real.sin (p 2 - p 1)) (hs2 : 0 ≤ Real.sin (p 2)) {t : ℝ} (ht : 0 < t) :
    V₁ p t + √3 * U₁ p t < 0 := by
  rw [C₂_eq]
  have : 0 ≤ (1 - p 0) * Real.sin (p 2 - p 1) * t :=
    mul_nonneg (mul_nonneg (by linarith) hs1) ht.le
  have : 0 ≤ p 0 * Real.sin (p 2) := mul_nonneg h0 hs2
  nlinarith [sq_pos_of_pos ht]

end SmoothedPolygons.TriFuller.BoxAnalytic
