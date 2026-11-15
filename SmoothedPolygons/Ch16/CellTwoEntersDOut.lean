module

public import SmoothedPolygons.Ch16.CellOneToDOut
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# `CellTwoEntersDOut` without computer assistance

Every point of the second big cell reaches `𝒟₀₀` within three steps (`cellTwoEntersDOut`, the
named fact `CellTwoEntersDOut` of `SmoothedPolygons/Ch16/BasinHypotheses.lean`).

## The route

Let `p ∈ cellTwoDomain` (first control `ζ²`). Along `ζ²` the switching function of `ζ² → ζ` is
`Y = t q(t)` with `q` a convex quadratic, `q(0) = r₂ sin θ₂ ≤ 0`, and positive root `T`
(`rootT_spec`); that of `ζ² → 1` is the cubic `A`, `A(0) = -√3 κ < 0`
(`SmoothedPolygons/Ch16/CellTwoFlow.lean`). Two cases:

* **`A ≤ 0` on `(0, T)`** (the book's `𝒟₃`, `S3_image`): then `A(T) < 0` (`S3_no_tie`), the first
  switch is `ζ² → ζ` at `T`, the image `z(T)` is on `𝒲₀` with `Im z₁(T) = T/3 - 2 r₂ sin θ₂/T > 0`
  and `Im z₂(T) = T²/12 - r₂ sin θ₂ > 0`, so its cell coordinates satisfy `0 < θ₁ < θ₂ < π`: it
  lies in `R₀` (`regionR0`), which `F` maps into `𝒟₀₀` (`poincareAngZero_mem_of_regionR0`,
  `SmoothedPolygons/Ch16/CellOneToDOut.lean`). Two steps.
* **`A > 0` somewhere on `(0, T)`** (the book's `𝒟₂`, `S2_image`): the first switch is `ζ² → 1` at
  the first sign change `T_A < T` of `A`, where `A' ≥ 0`; the image `w = ζ² z(T_A)` is on `𝒲₀`
  with `Im w₂ = -A'(T_A) ≤ 0` and `Re w₂ < 0` (`E_eq`), so `θ₂' ∈ (-π, -π/2)` or `θ₂' = π`. In the
  second case the image lies in `R₀` (two steps); in the first it lies in the second cell with
  `θ₂' ≤ -π/2`, where `A < 0` on `(0, T)` (`acub_neg_of_le`), so the next step is the first case.
  Three steps.

## The inequalities

All are exact: identities of polynomials in `t`, `r₂` and the sines and cosines of the cell angles
(certified by `linear_combination` with `√3² = 3`), and signs.

* `acub_neg_of_le` (`θ₂ ≤ -π/2 ⇒ A < 0` on `(0, T)`): `-y₂ A(t) = -√3 κ (t²/4 - y₂)
  - (√3/2) x₂ t (q(t) - t²/12) - y₂ (t/2)(q(t) - t²/4)` (`L2_identity`), every term `< 0` or `≤ 0`
  when `x₂ ≤ 0 > y₂` and `q(t) ≤ 0`.
* `S3_no_tie` (`A(T) < 0` when `A ≤ 0` on `(0, T)`): at a common root `T` of `q` and `A` (then
  `z₃(T) = 0`), with `m₁ = -Im (ζ² z₁(T)) = (Q₀ + √3 P₀)/2`, the identities
  `Q₀ A'(T) - Q₁ m₁ = A(T)/2 + (T/2) q(T)` and
  `Q₀ A(0) - (T³/12)(m₁ + Q₀) = y₁ A(T) - (T/2)(√3 x₁ + y₁) q(T)` (`S3_f1`, `S3_f2`) and
  `Q₀ = Im z₁(T) > 0`, `Q₁ = Im z₂(T) > 0` show that `A'(T) ≥ 0` (forced by `A ≤ 0` before `T`)
  gives `m₁ ≥ 0` and then `A(0) > 0`, against `A(0) = -√3 κ < 0`.
* `E_eq` (`Re w₂ < 0` at the switch to `1`):
  `-√3 κ_w (T_A²/4 + A') - (√3/2) Re w₂ (√3 κ + T_A³/12) - A' (√3 κ/2 + T_A³/8)` is a multiple of
  `A(T_A) = 0`, where `√3 κ_w = -Y(T_A) > 0` (`H_eq`, the Hamiltonian along the arc). This is the
  time reversal of `L2_identity` at the point `τ(w)`, whose arc of length `T_A` ends on the wall
  `ζ · 𝒲₀`.

Departure from the paper: the book takes the rows `𝒟₂`, `𝒟₃` of Table 16.1 from the involution
(`F₂(𝒟₂) = τ(𝒟₂) ⊂ 𝒟₃` with `θ₂ ∈ [-π/3, 0]` on `𝒟₂`, `F₃(𝒟₃) = τ(𝒟₄)` in the first cell, TeX
12616–12638) and the containment `F²𝒟₃ ⊂ 𝒟₀₀` from a Mathematica plot (Figure 16.2, TeX
12640–12665); the formalization proves the three-step statement analytically, by the sign
structure of the switching functions above and the one-step map `R₀ → 𝒟₀₀`, without the partition
`𝒟₂ | 𝒟₃` along `∂_{A,ζ²}` and without the involution.
-/

@[expose] public section

namespace SmoothedPolygons.TriFuller.CellTwoAnalytic

open Set Filter Topology
open Complex (I)
open DOutAnalytic (cκ)

/-! ### Exact identities -/

/-- `6 T Q₀(T) = 2 T² - 12 y₂ + 12 q(T)`: at the root of `q`, `Im z₁(T) = T/3 - 2 y₂/T`. -/
theorem six_mul_Q₀ (p : Fin 3 → ℝ) (t : ℝ) :
    6 * t * Q₀ p t = 2 * t ^ 2 - 12 * by₂ p + 12 * qY p t := by
  unfold Q₀ qY; ring

/-- `Q₁(T) = T²/12 - y₂ + 2 q(T)`: at the root of `q`, `Im z₂(T) = T²/12 - y₂`. -/
theorem Q₁_eq_qY (p : Fin 3 → ℝ) (t : ℝ) : Q₁ p t = t ^ 2 / 12 - by₂ p + 2 * qY p t := by
  unfold Q₁ qY; ring

/-- **The identity for `θ₂ ≤ -π/2`**: `-y₂ A(t) = -√3 κ (t²/4 - y₂) - (√3/2) x₂ t (q - t²/12)
- y₂ (t/2) (q - t²/4)`. -/
theorem L2_identity (p : Fin 3 → ℝ) (t : ℝ) :
    -by₂ p * Acub p t = -(√3 * cκ p * (t ^ 2 / 4 - by₂ p)) -
      √3 / 2 * bx₂ p * t * (qY p t - t ^ 2 / 12) - by₂ p * (t / 2) * (qY p t - t ^ 2 / 4) := by
  have hq : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [Acub, P₂, Q₂, qY]
  rw [cκ_eq]
  linear_combination (t ^ 3 * by₂ p / 24) * hq

/-- The Hamiltonian along `ζ²`: `√3 Im(z̄₁(t) z₂(t)) + Y + A = 0`. -/
theorem H_eq (p : Fin 3 → ℝ) (t : ℝ) :
    √3 * (P₀ p t * Q₁ p t - Q₀ p t * P₁ p t) + Q₂ p t + Acub p t = 0 := by
  have hq : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [Acub, P₀, Q₀, P₁, Q₁, P₂, Q₂]
  rw [cκ_eq]
  linear_combination (-t ^ 3 / 24 - t ^ 2 * by₁ p / 4 - t * by₂ p / 2) * hq

/-- The first identity at a common root of `q` and `A` (`m₁ = (Q₀ + √3 P₀)/2`). -/
theorem S3_f1 (p : Fin 3 → ℝ) (t : ℝ) :
    Q₀ p t * (√3 / 2 * P₁ p t + Q₁ p t / 2) - Q₁ p t * ((Q₀ p t + √3 * P₀ p t) / 2) =
      Acub p t / 2 + t / 2 * qY p t := by
  have hq : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [Acub, P₀, Q₀, P₁, Q₁, P₂, Q₂, qY]
  rw [cκ_eq]
  linear_combination (t ^ 3 / 48 + t ^ 2 * by₁ p / 8 + t * by₂ p / 4) * hq

/-- The second identity at a common root of `q` and `A`. -/
theorem S3_f2 (p : Fin 3 → ℝ) (t : ℝ) :
    Q₀ p t * -(√3 * cκ p) - t ^ 3 / 12 * ((Q₀ p t + √3 * P₀ p t) / 2 + Q₀ p t) =
      by₁ p * Acub p t - t / 2 * (√3 * bx₁ p + by₁ p) * qY p t := by
  have hq : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [Acub, P₀, Q₀, P₂, Q₂, qY]
  rw [cκ_eq]
  linear_combination (t ^ 4 / 48 + t ^ 3 * by₁ p / 24) * hq

/-- **The identity for `Re w₂`** at the switch `ζ² → 1` (`w = ζ² z(t)`, `Re w₂ = -P₁/2 + (√3/2) Q₁`,
`A' = (√3/2) P₁ + Q₁/2`): a multiple of `A(t)`. -/
theorem E_eq (p : Fin 3 → ℝ) (t : ℝ) :
    -(√3 * (P₀ p t * Q₁ p t - Q₀ p t * P₁ p t)) * (t ^ 2 / 4 + (√3 / 2 * P₁ p t + Q₁ p t / 2)) -
        √3 / 2 * (-P₁ p t / 2 + √3 / 2 * Q₁ p t) * (√3 * cκ p + t ^ 3 / 12) -
        (√3 / 2 * P₁ p t + Q₁ p t / 2) * (√3 * cκ p / 2 + t ^ 3 / 8) =
      (√3 / 2 * (bx₁ p * t + bx₂ p) + 3 / 2 * (by₁ p * t + by₂ p)) * Acub p t := by
  have hq : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [Acub, P₀, Q₀, P₁, Q₁, P₂, Q₂]
  rw [cκ_eq]
  linear_combination (t^5/192 - t^4*(bx₁ p)*√3/96 - t^4*(by₁ p)*√3^2/32 + t^4*(by₁ p)/24 +
    t^3*(bx₁ p)*(by₁ p)*√3/8 - t^3*(bx₂ p)*√3/24 + t^3*(by₁ p)^2/8 - t^3*(by₂ p)*√3^2/16 +
    t^3*(by₂ p)/24 + 5*t^2*(bx₁ p)*(by₂ p)*√3/16 + t^2*(bx₂ p)*(by₁ p)*√3/16 +
    3*t^2*(by₁ p)*(by₂ p)/8 - t*(bx₁ p)*(by₁ p)*(by₂ p)*√3/4 + t*(bx₂ p)*(by₁ p)^2*√3/4 +
    t*(bx₂ p)*(by₂ p)*√3/4 + t*(by₂ p)^2/4 - (bx₁ p)*(by₂ p)^2*√3/4 +
    (bx₂ p)*(by₁ p)*(by₂ p)*√3/4) * hq

/-! ### The two cases on the second cell -/

/-- **For `θ₂ ≤ -π/2`, `A < 0` on `(0, T)`**: `x₂ ≤ 0`, `y₂ < 0` and `L2_identity`. -/
theorem acub_neg_of_le {p : Fin 3 → ℝ} (hp : p ∈ cellTwoDomain) (h2 : p 2 ≤ -(Real.pi / 2)) :
    ∀ t ∈ Ioo 0 (rootT p), Acub p t ≤ 0 := by
  obtain ⟨-, hk, -, -⟩ := cellTwo_facts hp
  obtain ⟨-, hqT, hqneg, -⟩ := rootT_spec hp
  obtain ⟨⟨h0, h0'⟩, -, ⟨h2l, -⟩⟩ := hp
  have hpi := Real.pi_gt_three
  have hs3 : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  have hy2 : by₂ p < 0 :=
    mul_neg_of_pos_of_neg h0 (Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) h2l)
  have hx2 : bx₂ p ≤ 0 := by
    have := Real.cos_nonpos_of_pi_div_two_le_of_le (x := -p 2) (by linarith) (by linarith)
    rw [Real.cos_neg] at this
    exact mul_nonpos_of_nonneg_of_nonpos h0.le this
  intro t ht
  have hq := hqneg t ht.1 ht.2
  have t1 : 0 < √3 * cκ p * (t ^ 2 / 4 - by₂ p) := by
    have : 0 < t ^ 2 / 4 - by₂ p := by nlinarith [sq_nonneg t]
    positivity
  have t2 : 0 ≤ √3 / 2 * bx₂ p * t * (qY p t - t ^ 2 / 12) := by
    have : bx₂ p * (qY p t - t ^ 2 / 12) ≥ 0 :=
      mul_nonneg_of_nonpos_of_nonpos hx2 (by nlinarith [sq_nonneg t])
    have : 0 ≤ √3 / 2 * t * (bx₂ p * (qY p t - t ^ 2 / 12)) := by
      have := ht.1; positivity
    linarith [show √3 / 2 * bx₂ p * t * (qY p t - t ^ 2 / 12) =
      √3 / 2 * t * (bx₂ p * (qY p t - t ^ 2 / 12)) by ring]
  have t3 : 0 < -by₂ p * (t / 2) * (qY p t - t ^ 2 / 4) * -1 := by
    have : qY p t - t ^ 2 / 4 < 0 := by nlinarith [sq_nonneg t]
    have : 0 < -by₂ p * (t / 2) := mul_pos (by linarith) (by linarith [ht.1])
    nlinarith
  have e := L2_identity p t
  have : -by₂ p * Acub p t < 0 := by linarith
  exact (neg_of_mul_neg_right this (by linarith)).le

/-- **A common root of `q` and `A` is impossible when `A' ≥ 0` there**: at such a root `T`,
`S3_f1` gives `Q₁ m₁ = Q₀ A'(T) ≥ 0`, so `m₁ ≥ 0`, and `S3_f2` gives
`Q₀ A(0) = (T³/12)(m₁ + Q₀) > 0`, against `A(0) = -√3 κ < 0`. -/
theorem S3_no_tie {p : Fin 3 → ℝ} (hp : p ∈ cellTwoDomain) {T : ℝ} (hT : 0 < T)
    (hq : qY p T = 0) (hA : Acub p T = 0) (hd : 0 ≤ √3 / 2 * P₁ p T + Q₁ p T / 2) : False := by
  obtain ⟨hy2, hk, -, -⟩ := cellTwo_facts hp
  have hs3 : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  have hQ0 : 0 < Q₀ p T := by
    have e := six_mul_Q₀ p T
    rw [hq] at e
    have : 0 < 6 * T * Q₀ p T := by rw [e]; nlinarith
    exact pos_of_mul_pos_right this (by linarith)
  have hQ1 : 0 < Q₁ p T := by
    rw [Q₁_eq_qY, hq]; nlinarith
  have f1 := S3_f1 p T
  have f2 := S3_f2 p T
  rw [hA, hq] at f1 f2
  have hm1 : 0 ≤ (Q₀ p T + √3 * P₀ p T) / 2 := by
    by_contra h
    push Not at h
    have := mul_neg_of_pos_of_neg hQ1 h
    have := mul_nonneg hQ0.le hd
    linarith
  have h3 : 0 < T ^ 3 / 12 * ((Q₀ p T + √3 * P₀ p T) / 2 + Q₀ p T) :=
    mul_pos (by positivity) (by linarith)
  have h4 : Q₀ p T * -(√3 * cκ p) < 0 :=
    mul_neg_of_pos_of_neg hQ0 (by nlinarith [mul_pos hs3 hk])
  linarith

/-- The argument of a point of the open upper half plane lies in `(0, π)`. -/
theorem arg_mem_Ioo_of_im_pos {z : ℂ} (h : 0 < z.im) :
    0 < Complex.arg z ∧ Complex.arg z < Real.pi :=
  ⟨lt_of_le_of_ne (Complex.arg_nonneg_iff.2 h.le) fun e ↦ by
      have := (Complex.arg_eq_zero_iff.1 e.symm).2; linarith,
    Complex.arg_lt_pi_iff.2 (Or.inr h.ne')⟩

/-- **The case `A ≤ 0` on `(0, T)`** (the book's `𝒟₃`): the first switch is `ζ² → ζ` at `T`, and
the image lies in `R₀ = {0 < θ₁ < θ₂ ≤ π}`. -/
theorem S3_image {p : Fin 3 → ℝ} (hp : p ∈ cellTwoDomain)
    (hA : ∀ t ∈ Ioo 0 (rootT p), Acub p t ≤ 0) :
    ∃ q ∈ regionR0, poincareAngZero (cellClass p) = cellClass q := by
  obtain ⟨hy2, hk, -, hdom⟩ := cellTwo_facts hp
  obtain ⟨hT, hqT, hqneg, hqpos⟩ := rootT_spec hp
  have hs3 : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  have hcont := continuous_Acub p
  have hA0 : Acub p 0 < 0 := by rw [Acub_zero]; nlinarith [mul_pos hs3 hk]
  -- `A(T) < 0`
  have hAle : Acub p (rootT p) ≤ 0 := le_zero_of_nonpos_left hT hcont.continuousAt hA
  have hAT : Acub p (rootT p) < 0 := by
    refine lt_of_le_of_ne hAle fun h ↦ ?_
    exact S3_no_tie hp hT hqT h (deriv_nonneg_of_nonpos_left hT (hasDerivAt_Acub p _) h hA)
  -- the first control `ζ²` and the switch at `T`
  have hmax : ∀ t ∈ Icc 0 (rootT p), Acub p t ≤ 0 ∧ Q₂ p t ≤ 0 := by
    intro t ht
    rcases ht.1.lt_or_eq with h | h
    · rcases ht.2.lt_or_eq with h' | h'
      · exact ⟨hA t ⟨h, h'⟩, by rw [Q₂_eq]; exact (mul_neg_of_pos_of_neg h (hqneg t h h')).le⟩
      · rw [h', Q₂_eq, hqT, mul_zero]; exact ⟨hAT.le, le_rfl⟩
    · rw [← h, Q₂_eq, zero_mul]; exact ⟨hA0.le, le_rfl⟩
  have hbeat : ∀ ε > 0, ∃ t ∈ Ioo (rootT p) (rootT p + ε), 0 < Acub p t ∨ 0 < Q₂ p t :=
    fun ε hε ↦ ⟨rootT p + ε / 2, ⟨by linarith, by linarith⟩, Or.inr (by
      rw [Q₂_eq]; exact mul_pos (by linarith) (hqpos _ (by linarith)))⟩
  have hz := cellPoint_mem_sectionZero hdom
  obtain ⟨hfc, hτe⟩ := firstControl_sq hz.1 hT hmax hbeat
  have hw := poincare_mem_sectionZero hz
  have hpw : poincare (cellPoint p) = flow (rootT p) (cellPoint p) (ζ ^ 2) := by
    rw [poincare, hfc, hτe]
  obtain ⟨e0r, e0i, e1r, e1i, e2r, e2i⟩ := sq_flow p (rootT p)
  -- the image `w = z(T)` lies on `𝒲₀` with `x₃ < 0`
  have h2im : (poincare (cellPoint p) 2).im = 0 := by rw [hpw, e2i, Q₂_eq, hqT, mul_zero]
  have h2re : (poincare (cellPoint p) 2).re < 0 := by
    rw [hpw, e2r]
    unfold Acub at hAT
    rw [Q₂_eq, hqT, mul_zero] at hAT
    nlinarith
  obtain ⟨⟨c0, c1, -⟩, hcl⟩ := cellClass_cellCoords hw h2im h2re
  have himage :
      poincareAngZero (cellClass p) = cellClass (cellCoords (poincare (cellPoint p))) := by
    change poincareAngZero (classOf (cellPoint p)) = _
    rw [poincareAngZero_classOf hz, hcl]
  refine ⟨_, ?_, himage⟩
  -- `Im z₁(T) > 0` and `Im z₂(T) > 0`
  have hQ0 : 0 < (poincare (cellPoint p) 0).im := by
    rw [hpw, e0i]
    have e := six_mul_Q₀ p (rootT p)
    rw [hqT] at e
    have : 0 < 6 * rootT p * Q₀ p (rootT p) := by rw [e]; nlinarith
    exact pos_of_mul_pos_right this (by linarith)
  have hQ1 : 0 < (poincare (cellPoint p) 1).im := by
    rw [hpw, e1i, Q₁_eq_qY, hqT]; nlinarith
  obtain ⟨a0, a0'⟩ := arg_mem_Ioo_of_im_pos hQ0
  obtain ⟨a1, a1'⟩ := arg_mem_Ioo_of_im_pos hQ1
  set w := poincare (cellPoint p)
  have hc1 : cellCoords w 1 =
      toIcoMod Real.two_pi_pos 0 (Complex.arg (w 1) - Complex.arg (w 0)) := rfl
  have hc2 : cellCoords w 2 = Complex.arg (w 1) := rfl
  -- `ψ' = arg z₂(T) - arg z₁(T)`, so `θ₁' = arg z₁(T) > 0`
  have hψ : cellCoords w 1 = Complex.arg (w 1) - Complex.arg (w 0) := by
    have hlo := Complex.neg_pi_lt_arg (w 1)
    have hhi := Complex.arg_le_pi (w 0)
    rcases le_or_gt 0 (Complex.arg (w 1) - Complex.arg (w 0)) with hd | hd
    · rw [hc1]
      exact (toIcoMod_eq_self _).2 ⟨hd, by linarith⟩
    · exfalso
      have e : toIcoMod Real.two_pi_pos 0 (Complex.arg (w 1) - Complex.arg (w 0)) =
          Complex.arg (w 1) - Complex.arg (w 0) + 2 * Real.pi :=
        (toIcoMod_eq_iff _).2 ⟨⟨by linarith, by linarith⟩, -1, by simp⟩
      have := c1.2
      rw [hc1, e] at this
      linarith
  exact ⟨c0, c1, by rw [hc2]; exact a1'.le, by rw [hc2, hψ]; linarith⟩

/-- **The case `A > 0` somewhere on `(0, T)`** (the book's `𝒟₂`): the first switch is `ζ² → 1` at
the first sign change `T_A` of `A`, and the image has `θ₂' = π` (it lies in `R₀`) or lies in the
second cell with `θ₂' < -π/2`. -/
theorem S2_image {p : Fin 3 → ℝ} (hp : p ∈ cellTwoDomain)
    (hA : ∃ t ∈ Ioo 0 (rootT p), 0 < Acub p t) :
    ∃ q, poincareAngZero (cellClass p) = cellClass q ∧
      (q ∈ regionR0 ∨ (q ∈ cellTwoDomain ∧ q 2 ≤ -(Real.pi / 2))) := by
  obtain ⟨hy2, hk, -, hdom⟩ := cellTwo_facts hp
  obtain ⟨hT, hqT, hqneg, hqpos⟩ := rootT_spec hp
  obtain ⟨t₀, ht₀, hAt₀⟩ := hA
  have hpi := Real.pi_gt_three
  have hs3 : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  have hcont := continuous_Acub p
  have hA0 : Acub p 0 < 0 := by rw [Acub_zero]; nlinarith [mul_pos hs3 hk]
  -- the first sign change `T_A = inf {t > 0 | A(t) > 0}`
  set S := {t : ℝ | 0 < t ∧ 0 < Acub p t} with hS
  have hne : S.Nonempty := ⟨t₀, ht₀.1, hAt₀⟩
  have hbdd : BddBelow S := ⟨0, fun t ht ↦ ht.1.le⟩
  set TA := sInf S with hTA
  have hTAt₀ : TA ≤ t₀ := csInf_le hbdd ⟨ht₀.1, hAt₀⟩
  obtain ⟨δ, hδ, hδA⟩ : ∃ δ > 0, ∀ t, dist t 0 < δ → Acub p t < 0 :=
    Metric.eventually_nhds_iff.1 ((hcont.tendsto 0).eventually (gt_mem_nhds hA0))
  have hTApos : 0 < TA := by
    have : δ ≤ TA := le_csInf hne fun t ht ↦ by
      by_contra hlt
      push Not at hlt
      have := hδA t (by rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]; exact hlt)
      linarith [ht.2]
    linarith
  have hle : ∀ t ∈ Ioo 0 TA, Acub p t ≤ 0 := by
    intro t ht
    by_contra hc
    push Not at hc
    exact notMem_of_lt_csInf ht.2 hbdd ⟨ht.1, hc⟩
  have hAeq : Acub p TA = 0 := by
    refine le_antisymm (le_zero_of_nonpos_left hTApos hcont.continuousAt hle) ?_
    by_contra hc
    push Not at hc
    obtain ⟨ε, hε, h⟩ :=
      Metric.eventually_nhds_iff.1 ((hcont.tendsto TA).eventually (gt_mem_nhds hc))
    have : TA + ε ≤ TA := le_csInf hne fun t ht ↦ by
      by_contra hlt
      push Not at hlt
      have h1 : TA ≤ t := csInf_le hbdd ht
      have := h (show dist t TA < ε by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
      linarith [ht.2]
    linarith
  have hd := deriv_nonneg_of_nonpos_left hTApos (hasDerivAt_Acub p TA) hAeq hle
  have hTAT : TA < rootT p := lt_of_le_of_lt hTAt₀ ht₀.2
  have hQ2 : ∀ t ∈ Ioc 0 TA, Q₂ p t < 0 := fun t ht ↦ by
    rw [Q₂_eq]; exact mul_neg_of_pos_of_neg ht.1 (hqneg t ht.1 (by linarith [ht.2]))
  -- the first control `ζ²` and the switch at `T_A`
  have hmax : ∀ t ∈ Icc 0 TA, Acub p t ≤ 0 ∧ Q₂ p t ≤ 0 := by
    intro t ht
    rcases ht.1.lt_or_eq with h | h
    · refine ⟨?_, (hQ2 t ⟨h, ht.2⟩).le⟩
      rcases ht.2.lt_or_eq with h' | h'
      · exact hle t ⟨h, h'⟩
      · rw [h', hAeq]
    · rw [← h, Q₂_eq, zero_mul]; exact ⟨hA0.le, le_rfl⟩
  have hbeat : ∀ ε > 0, ∃ t ∈ Ioo TA (TA + ε), 0 < Acub p t ∨ 0 < Q₂ p t := by
    intro ε hε
    obtain ⟨t, ht, htlt⟩ := exists_lt_of_csInf_lt hne (show TA < TA + ε by linarith)
    have h1 : TA ≤ t := csInf_le hbdd ht
    have h2 : TA ≠ t := fun h ↦ by
      have := ht.2
      rw [← h, hAeq] at this
      exact lt_irrefl _ this
    exact ⟨t, ⟨lt_of_le_of_ne h1 h2, htlt⟩, Or.inl ht.2⟩
  have hz := cellPoint_mem_sectionZero hdom
  obtain ⟨hfc, hτe⟩ := firstControl_sq hz.1 hTApos hmax hbeat
  have hw := poincare_mem_sectionZero hz
  have hpw : poincare (cellPoint p) = flow TA (cellPoint p) (ζ ^ 2) := by
    rw [poincare, hfc, hτe]
  obtain ⟨e0r, e0i, e1r, e1i, e2r, e2i⟩ := sq_flow p TA
  -- the rotated image `w = ζ² F(z)`, on the wall `𝒲₀`
  have hζ2 : (ζ ^ 2 : ℂ) ≠ 0 := pow_ne_zero 2 fun h ↦ by simpa [h] using norm_ζ
  set w := (ζ ^ 2) • poincare (cellPoint p) with hw_def
  have hζw : w ∈ sectionZero := by
    refine ⟨fun h ↦ hw.1 ?_, ?_, ?_⟩
    · have := congrArg (fun z ↦ (ζ ^ 2)⁻¹ • z) h
      simp only [hw_def, smul_zero, inv_smul_smul₀ hζ2] at this
      exact this
    · exact mul_mem_walls ζ_sq_mem_VT hw.2.1
    · have := (hamMax_smul_scale_and_tau ζ_sq_mem_VT one_pos (poincare (cellPoint p))).1
      rw [scale_one, one_pow, one_mul] at this
      rw [hw_def, this, hw.2.2]
  have hwj : ∀ j, w j = ζ ^ 2 * flow TA (cellPoint p) (ζ ^ 2) j := fun j ↦ by
    rw [hw_def, Pi.smul_apply, smul_eq_mul, hpw]
  have hre : ∀ z : ℂ, (ζ ^ 2 * z).re = -z.re / 2 + √3 / 2 * z.im := by
    intro z; rw [Complex.mul_re, ζ_sq_re, ζ_sq_im]; ring
  have him : ∀ z : ℂ, (ζ ^ 2 * z).im = -z.im / 2 - √3 / 2 * z.re := by
    intro z; rw [Complex.mul_im, ζ_sq_re, ζ_sq_im]; ring
  have hQ2TA := hQ2 TA ⟨hTApos, le_rfl⟩
  have h2im : (w 2).im = 0 := by
    rw [hwj, him, e2r, e2i]; unfold Acub at hAeq; linarith
  have h2re : (w 2).re < 0 := by
    rw [hwj, hre, e2r, e2i]
    have hs3' : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have key : √3 * (-P₂ p TA / 2 + √3 / 2 * Q₂ p TA) = 2 * Q₂ p TA - Acub p TA := by
      unfold Acub; linear_combination (Q₂ p TA / 2) * hs3'
    rw [hAeq, sub_zero] at key
    exact neg_of_mul_neg_right (by rw [key]; linarith) hs3.le
  obtain ⟨⟨c0, c1, -⟩, hcl⟩ := cellClass_cellCoords hζw h2im h2re
  have hcls := classOf_smul_scale ζ_sq_mem_VT one_pos hw
  rw [scale_one] at hcls
  have himage : poincareAngZero (cellClass p) = cellClass (cellCoords w) := by
    change poincareAngZero (classOf (cellPoint p)) = _
    rw [poincareAngZero_classOf hz, hcl, hw_def, hcls]
  refine ⟨cellCoords w, himage, ?_⟩
  -- `w₂ = ζ² z₂(T_A)`: `Im w₂ = -A'(T_A) ≤ 0` and `Re w₂ < 0`
  have hw1re : (w 1).re = -P₁ p TA / 2 + √3 / 2 * Q₁ p TA := by rw [hwj, hre, e1r, e1i]
  have hw1im : (w 1).im = -(√3 / 2 * P₁ p TA + Q₁ p TA / 2) := by
    rw [hwj, him, e1r, e1i]; ring
  have hkw : 0 < √3 * (P₀ p TA * Q₁ p TA - Q₀ p TA * P₁ p TA) := by
    have := H_eq p TA
    rw [hAeq] at this
    linarith
  have hRe : (w 1).re < 0 := by
    rw [hw1re]
    by_contra hc
    push Not at hc
    have e := E_eq p TA
    rw [hAeq, mul_zero] at e
    have g1 : 0 < √3 * cκ p + TA ^ 3 / 12 := by have := mul_pos hs3 hk; positivity
    have g2 : 0 < √3 * cκ p / 2 + TA ^ 3 / 8 := by have := mul_pos hs3 hk; positivity
    have t1 : 0 < √3 * (P₀ p TA * Q₁ p TA - Q₀ p TA * P₁ p TA) *
        (TA ^ 2 / 4 + (√3 / 2 * P₁ p TA + Q₁ p TA / 2)) := mul_pos hkw (by positivity)
    have t2 : 0 ≤ √3 / 2 * (-P₁ p TA / 2 + √3 / 2 * Q₁ p TA) * (√3 * cκ p + TA ^ 3 / 12) :=
      mul_nonneg (mul_nonneg (by positivity) hc) g1.le
    have t3 : 0 ≤ (√3 / 2 * P₁ p TA + Q₁ p TA / 2) * (√3 * cκ p / 2 + TA ^ 3 / 8) :=
      mul_nonneg hd g2.le
    linarith
  have hc2 : cellCoords w 2 = Complex.arg (w 1) := rfl
  rcases hd.lt_or_eq with hd' | hd'
  · -- `Im w₂ < 0`: `θ₂' ∈ (-π, -π/2)`
    have hIm : (w 1).im < 0 := by rw [hw1im]; linarith
    have h1 := Complex.arg_neg_iff.2 hIm
    have h2 : ¬ |Complex.arg (w 1)| ≤ Real.pi / 2 := fun h ↦
      (not_le.2 hRe) (Complex.abs_arg_le_pi_div_two_iff.1 h)
    push Not at h2
    rw [abs_of_neg h1] at h2
    right
    exact ⟨⟨c0, c1, ⟨by rw [hc2]; exact Complex.neg_pi_lt_arg _, by rw [hc2]; linarith⟩⟩,
      by rw [hc2]; linarith⟩
  · -- `Im w₂ = 0`: `θ₂' = π`
    have hIm : (w 1).im = 0 := by rw [hw1im, ← hd']; ring
    have harg : Complex.arg (w 1) = Real.pi := Complex.arg_eq_pi_iff.2 ⟨hRe, hIm⟩
    left
    exact ⟨c0, c1, by rw [hc2, harg], by rw [hc2, harg]; linarith [c1.2]⟩

/-- **Every point of the second big cell reaches `𝒟₀₀` within three steps**: two steps for the
points switching to `ζ` (`S3_image`) and for those switching to `1` with image at `θ₂ = π`, three
for the others (`S2_image`, `acub_neg_of_le`, `S3_image`), the last step by
`poincareAngZero_mem_of_regionR0`.

Departure from the paper: the book reads `F²𝒟₃ ⊂ 𝒟₀₀` off a Mathematica plot (Figure 16.2, TeX
12640–12665) and the rows `𝒟₂`, `𝒟₃` from the involution (TeX 12616–12638); the formalization
proves the statement analytically (module docstring). -/
theorem cellTwoEntersDOut : CellTwoEntersDOut := by
  rintro x ⟨p, hp, rfl⟩
  by_cases hA : ∀ t ∈ Ioo 0 (rootT p), Acub p t ≤ 0
  · obtain ⟨q, hq, e⟩ := S3_image hp hA
    refine ⟨2, by norm_num, ?_⟩
    rw [Function.iterate_succ_apply', Function.iterate_one, e]
    exact poincareAngZero_mem_of_regionR0 hq
  · push Not at hA
    obtain ⟨q, e, hq | ⟨hq, hq2⟩⟩ := S2_image hp hA
    · refine ⟨2, by norm_num, ?_⟩
      rw [Function.iterate_succ_apply', Function.iterate_one, e]
      exact poincareAngZero_mem_of_regionR0 hq
    · obtain ⟨q', hq', e'⟩ := S3_image hq (acub_neg_of_le hq hq2)
      refine ⟨3, le_rfl, ?_⟩
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_one, e,
        e']
      exact poincareAngZero_mem_of_regionR0 hq'

end SmoothedPolygons.TriFuller.CellTwoAnalytic

namespace SmoothedPolygons.TriFuller

/-- **`CellTwoEntersDOut`** (`SmoothedPolygons/Ch16/BasinHypotheses.lean`), without computer
assistance (`CellTwoAnalytic.cellTwoEntersDOut`). -/
theorem cellTwoEntersDOut : CellTwoEntersDOut := CellTwoAnalytic.cellTwoEntersDOut

end SmoothedPolygons.TriFuller
