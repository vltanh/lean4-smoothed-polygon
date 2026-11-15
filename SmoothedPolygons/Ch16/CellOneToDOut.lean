module

public import SmoothedPolygons.Ch16.CellTwoFlow
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# One step from the region `0 < θ₁ < θ₂ ≤ π` of the first big cell into `𝒟₀₀`

The region `R₀ = {r₂ ∈ (0, 1), ψ ∈ (0, π), θ₂ ≤ π, θ₁ = θ₂ - ψ > 0}` of the first big cell (the
points whose two arguments `θ₁ < θ₂` lie in `(0, π]`; `regionR0`) is mapped by the Fuller–Poincaré
map into `𝒟₀₀ = 𝒟_out` (`poincareAngZero_mem_of_regionR0`), with `ψ' < π/3` and `θ₂' > 2π/3`.
This is the last step of every orbit of the second big cell in the proof of `CellTwoEntersDOut`
(`SmoothedPolygons/Ch16/CellTwoEntersDOut.lean`): the image of a point of the second cell whose
first switch is to `ζ` lies in `R₀`.

The proof is that of `F(𝒟₀₀) ⊆ 𝒟₀₀` (`SmoothedPolygons/Ch16/DOutInvariant.lean`), on a larger
region:

* **The switch** (`regionR0_root`): `Im z₃(t) > 0` along `ζ` (`sin θ₁ > 0`, `sin θ₂ ≥ 0`), so
  `ζ²` never beats `ζ`; the switching function `D = V₂` of `ζ → 1` has exactly one positive root
  `τ`: for `θ₂ ≥ π/3`, `y₂ ≤ 0 ≤ κ` and `D/t²` is increasing (`V₂_mul_sq_lt`); for `θ₂ < π/3`,
  `y₁, y₂ ≥ 0` and `D` itself is increasing. In both cases `V₁(τ) = D'(τ) > 0`.
* **`θ₂' > 2π/3`**: `C₂ = V₁ + √3 U₁ = -2 Im z₂(τ) < 0` (`C₂_eq`).
* **`ψ' < π/3`**: `C₁ < 0` at the root, by one of two identities: for `θ₁ ≥ π/2`, the identity
  `C₁_eq` of `DOutInvariant.lean` (`√3 C₁ + 10 D` is a sum of terms `≤ 0`: there `cos ψ ≥ 0`,
  `cos θ₂ ≤ 0`); for `θ₁ ≤ π/2`, the new identity `C₁_eq'`:
  `τ √3 C₁ + (4τ + 2√3 r₁) D = -6 r₁² r₂ sin ψ
    + τ r₁ r₂ (3 (cos θ₂ - cos ψ) - 3√3 sin ψ - √3 sin θ₂)
    + τ² (r₁² (-3 + (3/2) cos θ₁ - (√3/2) sin θ₁) - 2 r₂ sin θ₂)
    + τ³ r₁ (√3/6 - (3√3/2) cos θ₁ - (5/2) sin θ₁) - (7/6) τ⁴`,
  every term `≤ 0` there (`cos θ₂ ≤ cos ψ` as `0 < ψ < θ₂ ≤ π`, and
  `(3√3/2) cos θ₁ + (5/2) sin θ₁ ≥ (5/2)(cos θ₁ + sin θ₁) ≥ 5/2`). The constant term of `C₁` is
  positive for `ψ > π/3`, so near `ψ = π` no multiple of `D` by a constant suffices; the
  multiplier `4τ + 2√3 r₁` uses the root relation at order `τ`.
-/

@[expose] public section

namespace SmoothedPolygons.TriFuller.CellTwoAnalytic

open Set
open Complex (I)
open DOutAnalytic

/-- The region `R₀ = {0 < θ₁ < θ₂ ≤ π}` of the first big cell: `r₂ ∈ (0, 1)`, `ψ ∈ (0, π)`,
`θ₂ ≤ π` and `θ₁ = θ₂ - ψ > 0`. -/
def regionR0 : Set (Fin 3 → ℝ) :=
  {p | p 0 ∈ Ioo 0 1 ∧ p 1 ∈ Ioo 0 Real.pi ∧ p 2 ≤ Real.pi ∧ 0 < p 2 - p 1}

/-- The signs on `R₀`: `sin θ₁ > 0`, `sin θ₂ ≥ 0`, `κ > 0`. -/
theorem regionR0_facts {p : Fin 3 → ℝ} (hp : p ∈ regionR0) :
    0 < Real.sin (p 2 - p 1) ∧ 0 ≤ Real.sin (p 2) ∧ 0 < cκ p ∧ p ∈ cellDomain := by
  obtain ⟨⟨h0, h0'⟩, ⟨h1, h1'⟩, h2, h21⟩ := hp
  have hpi := Real.pi_gt_three
  refine ⟨Real.sin_pos_of_pos_of_lt_pi h21 (by linarith),
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) h2, ?_,
    ⟨⟨h0.le, h0'.le⟩, ⟨h1.le, h1'.le⟩, ⟨by linarith, h2⟩⟩⟩
  unfold cκ
  have := Real.sin_pos_of_pos_of_lt_pi h1 h1'
  have : 0 < 1 - p 0 := by linarith
  positivity

/-- Along `ζ`, `Im z₃(t) = r₂ sin θ₂ t + r₁ sin θ₁ t²/2 + t³/12 > 0`: `ζ²` never beats `ζ`. -/
theorem regionR0_flow_im {p : Fin 3 → ℝ} (hp : p ∈ regionR0) :
    ∀ t, 0 < t → 0 < (flow t (cellPoint p) ζ 2).im := by
  obtain ⟨hs1, hs2, -, -⟩ := regionR0_facts hp
  obtain ⟨⟨h0, h0'⟩, -, -, -⟩ := hp
  intro t ht
  rw [flow_two_im]
  have : 0 < 1 - p 0 := by linarith
  have : 0 ≤ p 0 * Real.sin (p 2) * t := by positivity
  have : 0 < (1 - p 0) * Real.sin (p 2 - p 1) * t ^ 2 / 2 := by positivity
  have : 0 < t ^ 3 / 12 := by positivity
  linarith

/-- `D(7) > 0` for `r₂ ∈ [0, 1]` (`|y_j| ≤ r_j`, `κ ≤ 1/4`). -/
theorem V₂_seven_pos' {p : Fin 3 → ℝ} (h0 : 0 ≤ p 0) (h0' : p 0 ≤ 1) : 0 < V₂ p 7 := by
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

/-- **The switch on `R₀`**: `D` has exactly one positive root `τ`, `D < 0` before it, `D > 0` after
it, and `V₁(τ) > 0`. -/
theorem regionR0_root {p : Fin 3 → ℝ} (hp : p ∈ regionR0) :
    ∃ τ, 0 < τ ∧ V₂ p τ = 0 ∧ (∀ t, 0 < t → t < τ → V₂ p t < 0) ∧
      (∀ t, τ < t → 0 < V₂ p t) ∧ 0 < V₁ p τ := by
  obtain ⟨hs1, hs2, hk, -⟩ := regionR0_facts hp
  obtain ⟨⟨h0, h0'⟩, ⟨h1, h1'⟩, h2, h21⟩ := hp
  have hpi := Real.pi_gt_three
  have h3 : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  have hV0 : V₂ p 0 < 0 := by
    have : V₂ p 0 = -(√3 * cκ p) := by unfold V₂; ring
    rw [this]; nlinarith [mul_pos h3 hk]
  have h7 := V₂_seven_pos' h0.le h0'.le
  have hcont : ContinuousOn (V₂ p) (Icc 0 7) := by unfold V₂; fun_prop
  obtain ⟨τ, hτ, hτ0⟩ := intermediate_value_Ioo (by norm_num : (0 : ℝ) ≤ 7) hcont ⟨hV0, h7⟩
  refine ⟨τ, hτ.1, hτ0, ?_⟩
  rcases le_or_gt (Real.pi / 3) (p 2) with hθ | hθ
  · -- `y₂ ≤ 0`: `D(t)/t²` is increasing
    have hy : cy₂ p ≤ 0 := by
      have : 0 ≤ Real.sin (p 2 + 2 / 3 * Real.pi - Real.pi) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
      rw [Real.sin_sub_pi] at this
      unfold cy₂; nlinarith
    exact ⟨fun t ht htτ ↦ V₂_neg_of_nonpos hy hk.le ht htτ hτ0.le,
      fun t htτ ↦ V₂_pos_of_nonneg hy hk.le hτ.1 htτ hτ0.ge, V₁_pos_of_root hy hk.le hτ.1 hτ0⟩
  · -- `θ₁ < θ₂ < π/3`: `y₁, y₂ ≥ 0`, and `D` is increasing
    have hy2 : 0 ≤ cy₂ p := by
      unfold cy₂
      exact mul_nonneg h0.le (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))
    have hy1 : 0 ≤ cy₁ p := by
      have : 0 < 1 - p 0 := by linarith
      unfold cy₁
      exact mul_nonneg this.le (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))
    have hmono : ∀ s t, 0 ≤ s → s < t → V₂ p s < V₂ p t := by
      intro s t hs hst
      have e : V₂ p t - V₂ p s =
          (t - s) * (cy₂ p + cy₁ p * (t + s) / 2 + (t ^ 2 + t * s + s ^ 2) / 12) := by
        unfold V₂; ring
      have : 0 < (t - s) * (cy₂ p + cy₁ p * (t + s) / 2 + (t ^ 2 + t * s + s ^ 2) / 12) := by
        apply mul_pos (by linarith)
        have : 0 ≤ cy₁ p * (t + s) / 2 := div_nonneg (mul_nonneg hy1 (by linarith)) (by norm_num)
        have : 0 < (t ^ 2 + t * s + s ^ 2) / 12 := by nlinarith
        linarith
      linarith
    refine ⟨fun t ht htτ ↦ ?_, fun t htτ ↦ ?_, ?_⟩
    · have := hmono t τ ht.le htτ; rwa [hτ0] at this
    · have := hmono τ t hτ.1.le htτ; rwa [hτ0] at this
    · unfold V₁
      have : 0 ≤ cy₁ p * τ := mul_nonneg hy1 hτ.1.le
      have : 0 < τ ^ 2 / 4 := by have := hτ.1; positivity
      linarith

/-- **The second identity for `C₁`**: `τ √3 C₁ + (4τ + 2√3 r₁) D` is a sum of terms of fixed sign
on `R₀ ∩ {θ₁ ≤ π/2}`. -/
theorem C₁_eq' (p : Fin 3 → ℝ) (t : ℝ) :
    t * (√3 * (U₀ p t * (V₁ p t - √3 * U₁ p t) - V₀ p t * (U₁ p t + √3 * V₁ p t))) +
        (4 * t + 2 * √3 * (1 - p 0)) * V₂ p t =
      -6 * (1 - p 0) ^ 2 * p 0 * Real.sin (p 1) +
        t * (1 - p 0) * p 0 * (-3 * √3 * Real.sin (p 1) - 3 * Real.cos (p 1) -
          √3 * Real.sin (p 2) + 3 * Real.cos (p 2)) +
        t ^ 2 * ((1 - p 0) ^ 2 * (-3 + 3 / 2 * Real.cos (p 2 - p 1) -
          √3 / 2 * Real.sin (p 2 - p 1)) - 2 * p 0 * Real.sin (p 2)) +
        t ^ 3 * (1 - p 0) * (-(3 * √3 / 2) * Real.cos (p 2 - p 1) -
          5 / 2 * Real.sin (p 2 - p 1) + √3 / 6) - 7 / 6 * t ^ 4 := by
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
    c1*q*r^2*s2*t/4 + c1*q*r*s2*t/4 + 7*c1*q*r*t^3/8 - 7*c1*q*t^3/8 - 2*c1*r^3*s2 +
    4*c1*r^2*s2 + c1*r^2*t^2/2 - 2*c1*r*s2 - c1*r*t^2 + c1*t^2/2 + c2*q*r^2*s1*t/4 -
    c2*q*r*s1*t/4 - 3*c2*q*r*t^2/4 + 2*c2*r^3*s1 - 4*c2*r^2*s1 - c2*r^2*t + 2*c2*r*s1 +
    c2*r*t - q^2*r^2*s1^2*t^2/4 + q^2*r^2*s1*s2*t/4 + q^2*r*s1^2*t^2/2 - q^2*r*s1*s2*t/4 +
    3*q^2*r*s1*t^3/8 - q^2*r*s2*t^2/4 - q^2*s1^2*t^2/4 - 3*q^2*s1*t^3/8 - q^2*t^4/8 -
    r^2*s1^2*t^2 + r^2*s1*s2*t + 2*r*s1^2*t^2 - r*s1*s2*t + r*s1*t^3/2 - s1^2*t^2 - s1*t^3/2 -
    t^4/2) * hq + (-3 * t ^ 2 * (r - 1) ^ 2) * hs

/-- **`C₁ < 0` at the root of `D` on `R₀`**, by `C₁_eq` for `θ₁ ≥ π/2` and `C₁_eq'` for
`θ₁ ≤ π/2`. -/
theorem C₁_neg_R0 {p : Fin 3 → ℝ} (hp : p ∈ regionR0) {τ : ℝ} (hτ : 0 < τ) (h0 : V₂ p τ = 0) :
    U₀ p τ * (V₁ p τ - √3 * U₁ p τ) - V₀ p τ * (U₁ p τ + √3 * V₁ p τ) < 0 := by
  obtain ⟨hs1, hs2, hk, -⟩ := regionR0_facts hp
  obtain ⟨⟨h0r, h0r'⟩, ⟨h1, h1'⟩, h2, h21⟩ := hp
  have hpi := Real.pi_gt_three
  have hq : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  have hq2 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsψ : 0 < Real.sin (p 1) := Real.sin_pos_of_pos_of_lt_pi h1 h1'
  have hr1 : 0 < 1 - p 0 := by linarith
  rcases le_total (p 2 - p 1) (Real.pi / 2) with hθ | hθ
  · -- `θ₁ ≤ π/2`: the identity `C₁_eq'`
    have hc1 : 0 ≤ Real.cos (p 2 - p 1) :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) hθ
    have hcs : 1 ≤ Real.cos (p 2 - p 1) + Real.sin (p 2 - p 1) := by
      have := Real.cos_sq_add_sin_sq (p 2 - p 1)
      nlinarith [mul_nonneg hc1 hs1.le]
    have hc1' : Real.cos (p 2 - p 1) ≤ 1 := Real.cos_le_one _
    have hcmp : Real.cos (p 2) ≤ Real.cos (p 1) :=
      Real.cos_le_cos_of_nonneg_of_le_pi h1.le h2 (by linarith)
    have hq5 : 5 ≤ 3 * √3 := by nlinarith
    have t1 : -6 * (1 - p 0) ^ 2 * p 0 * Real.sin (p 1) ≤ 0 := by
      have : 0 ≤ (1 - p 0) ^ 2 * p 0 * Real.sin (p 1) := by positivity
      linarith
    have t2 : τ * (1 - p 0) * p 0 * (-3 * √3 * Real.sin (p 1) - 3 * Real.cos (p 1) -
        √3 * Real.sin (p 2) + 3 * Real.cos (p 2)) ≤ 0 := by
      have : -3 * √3 * Real.sin (p 1) - 3 * Real.cos (p 1) - √3 * Real.sin (p 2) +
          3 * Real.cos (p 2) ≤ 0 := by nlinarith [mul_nonneg hq.le hs2]
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) this
    have t3 : τ ^ 2 * ((1 - p 0) ^ 2 * (-3 + 3 / 2 * Real.cos (p 2 - p 1) -
        √3 / 2 * Real.sin (p 2 - p 1)) - 2 * p 0 * Real.sin (p 2)) ≤ 0 := by
      have : -3 + 3 / 2 * Real.cos (p 2 - p 1) - √3 / 2 * Real.sin (p 2 - p 1) ≤ 0 := by
        nlinarith [mul_nonneg hq.le hs1.le]
      have : (1 - p 0) ^ 2 * (-3 + 3 / 2 * Real.cos (p 2 - p 1) -
          √3 / 2 * Real.sin (p 2 - p 1)) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) this
      have : 0 ≤ p 0 * Real.sin (p 2) := mul_nonneg h0r.le hs2
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    have t4 : τ ^ 3 * (1 - p 0) * (-(3 * √3 / 2) * Real.cos (p 2 - p 1) -
        5 / 2 * Real.sin (p 2 - p 1) + √3 / 6) ≤ 0 := by
      have h5 := mul_le_mul_of_nonneg_right hq5 hc1
      have h3 : √3 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
      have : -(3 * √3 / 2) * Real.cos (p 2 - p 1) - 5 / 2 * Real.sin (p 2 - p 1) + √3 / 6 ≤ 0 := by
        linarith
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) this
    have t5 : 0 < 7 / 6 * τ ^ 4 := by positivity
    have e := C₁_eq' p τ
    rw [h0, mul_zero, add_zero] at e
    have key : ∀ X a b c d f : ℝ, X = a + b + c + d - f → a ≤ 0 → b ≤ 0 → c ≤ 0 → d ≤ 0 →
        0 < f → X < 0 := by intros; linarith
    have := key _ _ _ _ _ _ e t1 t2 t3 t4 t5
    exact neg_of_mul_neg_right (neg_of_mul_neg_right this hτ.le) hq.le
  · -- `θ₁ ≥ π/2`: the identity `C₁_eq`
    have hcψ : 0 ≤ Real.cos (p 1) :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) (by linarith)
    have hc2 : Real.cos (p 2) ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith)
    have t1 : 0 ≤ (1 - p 0) * p 0 * (9 * √3 * Real.sin (p 1) + 3 * Real.cos (p 1)) := by
      positivity
    have t2 : 0 ≤ 3 * (1 - p 0) ^ 2 * τ := by positivity
    have t3 : 0 ≤ 4 * (1 - p 0) * τ ^ 2 * Real.sin (p 2 - p 1) := by positivity
    have t4 : p 0 * τ * (3 * √3 * Real.cos (p 2) - 5 * Real.sin (p 2)) ≤ 0 := by
      have := mul_nonpos_of_nonneg_of_nonpos (by positivity : (0 : ℝ) ≤ 3 * √3) hc2
      have : 3 * √3 * Real.cos (p 2) - 5 * Real.sin (p 2) ≤ 0 := by linarith
      exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg h0r.le hτ.le) this
    have t5 : 0 < 2 / 3 * τ ^ 3 := by positivity
    have e := C₁_eq p τ
    rw [h0, mul_zero, add_zero] at e
    have key : ∀ X a b c d f : ℝ, X = -a - b - c + d - f → 0 ≤ a → 0 ≤ b → 0 ≤ c → d ≤ 0 →
        0 < f → X < 0 := by intros; linarith
    exact neg_of_mul_neg_right (key _ _ _ _ _ _ e t1 t2 t3 t4 t5) hq.le

/-- **The image of a point at a simple switch `ζ → 1`**, for any point of the closed cells at
which `ζ²` never beats `ζ` and `D` has a unique positive root `τ` (the proof of `image_spec`,
`SmoothedPolygons/Ch16/DOutFlow.lean`, without the box): the class of the image is the class of
the cell coordinates of `w = ζ F(z)`, with `w₁ = U₀ + i V₀`, `w₂ = U₁ + i V₁` at `τ`. -/
theorem image_spec_gen {p : Fin 3 → ℝ} (hdom : p ∈ cellDomain) (hk : 0 ≤ cκ p)
    (hY : ∀ t, 0 < t → 0 < (flow t (cellPoint p) ζ 2).im) {τ : ℝ} (hτ0 : 0 < τ)
    (hneg : ∀ t, 0 < t → t < τ → V₂ p t < 0) (hpos : ∀ t, τ < t → 0 < V₂ p t)
    (h0 : V₂ p τ = 0) :
    ∃ w : Fin 3 → ℂ, poincareAngZero (cellClass p) = cellClass (cellCoords w) ∧
      (w 0).re = U₀ p τ ∧ (w 0).im = V₀ p τ ∧ (w 1).re = U₁ p τ ∧ (w 1).im = V₁ p τ ∧
      cellCoords w 0 ∈ Ioo 0 1 ∧
      toIcoMod Real.two_pi_pos 0 (Complex.arg (w 1) - Complex.arg (w 0)) ∈ Ioo 0 Real.pi ∧
      cellCoords w 1 = toIcoMod Real.two_pi_pos 0 (Complex.arg (w 1) - Complex.arg (w 0)) ∧
      cellCoords w 2 = Complex.arg (w 1) := by
  have hz := cellPoint_mem_sectionZero hdom
  obtain ⟨hfc, hτe⟩ := firstControl_firstSwitchTime hz.1 hk hY hτ0 hneg hpos h0
  have hw := poincare_mem_sectionZero hz
  have hpw : poincare (cellPoint p) = flow τ (cellPoint p) ζ := by rw [poincare, hfc, hτe]
  obtain ⟨e0r, e0i, e1r, e1i, e2r, e2i⟩ := zeta_flow p τ
  have hU₂ : U₂ p τ < 0 := by
    have e := flow_two_im_eq (p := p) τ
    rw [h0] at e
    have := hY τ hτ0
    have h3 : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
    nlinarith
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
  exact ⟨w, himage, by rw [hw0, e0r], by rw [hw0, e0i], by rw [hw1, e1r], by rw [hw1, e1i], c0,
    c1, rfl, rfl⟩

/-- **`F(R₀) ⊆ 𝒟₀₀`**: the image of a point of `R₀` has `ψ' < π/3` and `θ₂' > 2π/3 > π - 1.1`.

Departure from the paper: the book obtains the last step of the orbits of the second big cell from
the containment `F²𝒟₃ ⊂ 𝒟₀₀` read off a Mathematica plot (Figure 16.2, TeX 12640–12665) and the
exclusion argument `τ(𝒟₄) ⊆ 𝒟₁ ∖ 𝒟_in` (TeX 12629–12638); the formalization proves analytically
that the whole region `0 < θ₁ < θ₂ ≤ π`, which contains the image of every point of the second cell
switching to `ζ`, is mapped into `𝒟₀₀`, by the root structure of the switching cubic
(`regionR0_root`) and the sign identities `C₂_eq`, `C₁_eq`, `C₁_eq'`. -/
theorem poincareAngZero_mem_of_regionR0 {p : Fin 3 → ℝ} (hp : p ∈ regionR0) :
    poincareAngZero (cellClass p) ∈ boxSet 0 0 := by
  obtain ⟨hs1, hs2, hk, hdom⟩ := regionR0_facts hp
  obtain ⟨τ, hτ0, h0, hneg, hpos, hV₁⟩ := regionR0_root hp
  obtain ⟨w, himage, e0r, e0i, e1r, e1i, c0, c1, h1, h2⟩ :=
    image_spec_gen hdom hk.le (regionR0_flow_im hp) hτ0 hneg hpos h0
  have hC2 : V₁ p τ + √3 * U₁ p τ < 0 := by
    obtain ⟨⟨h0r, h0r'⟩, -, -, -⟩ := hp
    rw [C₂_eq]
    have : 0 ≤ (1 - p 0) * Real.sin (p 2 - p 1) * τ :=
      mul_nonneg (mul_nonneg (by linarith) hs1.le) hτ0.le
    have : 0 ≤ p 0 * Real.sin (p 2) := mul_nonneg h0r.le hs2
    nlinarith [sq_pos_of_pos hτ0]
  have hC1 := C₁_neg_R0 hp hτ0 h0
  rw [himage]
  refine ⟨cellCoords w, ?_, rfl⟩
  rw [mem_cellBox_zero_zero]
  refine ⟨⟨c0.1.le, c0.2.le⟩, ⟨by rw [h1]; exact c1.1.le, ?_⟩, ⟨?_, by
    rw [h2]; exact Complex.arg_le_pi _⟩⟩
  · -- `ψ' < π/3`
    have := toIcoMod_lt_pi_div_three (w₀ := w 0) (w₁ := w 1) c1
      (by rw [e0r, e0i, e1r, e1i]; exact hC1)
    rw [h1]
    exact this.le
  · -- `θ₂' > 2π/3 ≥ π - 1.1`
    have := two_pi_div_three_lt_arg (w := w 1) (by rw [e1i]; exact hV₁)
      (by rw [e1i, e1r]; exact hC2)
    rw [h2]
    have := Real.pi_lt_d2
    norm_num at this ⊢
    linarith

end SmoothedPolygons.TriFuller.CellTwoAnalytic
