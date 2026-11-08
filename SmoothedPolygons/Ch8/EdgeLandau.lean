module

public import SmoothedPolygons.Ch8.EdgeProblem
public import SmoothedPolygons.AppA.Gronwall

/-!
# The switching function of the edge problem at a double zero (Lemma 8.1.5)

Lemma 8.1.5 (`lem:lambda2-Landau`, TeX 6908–7015): at a zero of the switching function `λ₂` of the
edge problem where also `λ₂' = 0` (normalized as in (8.1.8)), `λ₂(t) = C tⁿ + O(tⁿ⁺¹)` with
`C ≠ 0` and `n ∈ {2, 3}`, whatever the control; so that zero is isolated. Used by Theorem 8.1.4.

Notes on the statement:
* The book's Landau notation is two-sided (TeX 6903–6907): `f₁ = O(f₂)` on some `(-t₁, t₁)`, i.e.
  `Asymptotics.IsBigO` at `𝓝 0`. The proof applies Corollary A.1.3 on both sides of `0`
  (gap G14; `l3st_corollaryA_1_3_two_sided`).
* The constant `C` printed for `x₀ ≠ 0`, `-x₀(1 + y₀)/y₀²` (TeX 6934, 6973), is wrong: the
  computation gives `C = -2x₀/y₀` (gap G5; the intermediate line TeX 6970 already gives
  `(x² - x₀²)/y² = 2x₀t/y₀ + O(t²)`). The statement only claims `C ≠ 0`, which holds with the
  correct value.
-/

@[expose] public section

namespace SmoothedPolygons

open Set MeasureTheory Filter Topology Asymptotics

/-- **Lemma 8.1.5** (`lem:lambda2-Landau`). Fix `λ_cost = -1`, `λ₃ = -λ_cost x₀² = x₀²` with
`|x₀| < 1/√3`, and `y₀ > 0`. Let `t₁ > 0`, let `u_e : (-t₁, t₁) → [-½, ½]` be any measurable
function, and let `x, y, λ₁, λ₂` solve the state equations (8.1.3) and the costate equations
(8.1.7) on `(-t₁, t₁)` with `(x, y)(0) = (x₀, y₀)` and `(λ₁, λ₂)(0) = (0, 0)` (continuous
solutions in integral form, with the state in the state space `y > 0`, `|x| < 1/√3` of
Definition 8.1.1). Then there are an integer `n ≥ 2` and a real `C ≠ 0`, depending on `(x₀, y₀)`
but not on the control `u_e`, such that `λ₂(t) = C tⁿ + O(tⁿ⁺¹)` (two-sided, TeX 6903–6907). In
particular `t = 0` is an isolated zero of `λ₂`.

Proof (the book's, TeX 6932–7015):
1. `n = 2` if `x₀ ≠ 0`, `n = 3` if `x₀ = 0`; `C = -2x₀/y₀` if `x₀ ≠ 0` (gap G5: the printed
   `-x₀(1 + y₀)/y₀²` is a slip) and `C = -2/3` if `x₀ = 0`.
2. Comparison functions `λ̃₁(t) = ∫₀ᵗ 2x/y`, `λ̃₂(t) = -∫₀ᵗ ((x² - x₀²)/y² + λ̃₁)`.
3. The Taylor expansions `y = y₀ + O(t)` (`y'` is bounded), `x = x₀ + y₀ t + O(t²)` give
   `λ̃₂ = C tⁿ + O(tⁿ⁺¹)`.
4. The error `v = (λ₁ - λ̃₁, λ₂ - λ̃₂)` solves `v' = -A v - λ̃₂ b` with
   `A = [[0, f₂ₓ], [1, f₂ᵧ]]`, `b = (f₂ₓ, f₂ᵧ)` evaluated along the trajectory; `‖A‖ ≤ C₀` near
   `0` (the denominator `-1 + 2√3 x u_e` stays away from `0`), so `‖v‖' ≤ ‖v'‖ ≤ C₁|t|ⁿ + C₀‖v‖`
   (Cauchy–Schwarz) and `‖v‖ ≤ C₁|t|ⁿ⁺¹/(n + 1) + C₀|∫₀ᵗ ‖v‖|`.
5. Gronwall (Corollary A.1.3, two-sided, `l3st_corollaryA_1_3_two_sided`): `‖v‖ = O(tⁿ⁺¹)`, so
   `|λ₂ - C tⁿ| ≤ ‖v‖ + |λ̃₂ - C tⁿ| = O(tⁿ⁺¹)`.
6. `C ≠ 0` and `λ₂ = C tⁿ + O(tⁿ⁺¹)` give `λ₂(t) ≠ 0` for small `t ≠ 0`.
Expected size: 300–500 lines. -/
theorem lemma8_1_5 {x₀ y₀ : ℝ} (hx₀ : |x₀| < 1 / √3) (hy₀ : 0 < y₀) :
    ∃ n : ℕ, 2 ≤ n ∧ ∃ C : ℝ, C ≠ 0 ∧
      ∀ (t₁ : ℝ) (ue x y l₁ l₂ : ℝ → ℝ), 0 < t₁ → Measurable ue →
        (∀ t ∈ Ioo (-t₁) t₁, ue t ∈ edgeControlSet) →
        (∀ t ∈ Ioo (-t₁) t₁, 0 < y t ∧ |x t| < 1 / √3) →
        ContinuousOn x (Ioo (-t₁) t₁) → ContinuousOn y (Ioo (-t₁) t₁) →
        ContinuousOn l₁ (Ioo (-t₁) t₁) → ContinuousOn l₂ (Ioo (-t₁) t₁) →
        (∀ t ∈ Ioo (-t₁) t₁, x t = x₀ + ∫ s in (0 : ℝ)..t, y s) →
        (∀ t ∈ Ioo (-t₁) t₁, y t = y₀ + ∫ s in (0 : ℝ)..t, edgeF₂ (x s) (y s) (ue s)) →
        (∀ t ∈ Ioo (-t₁) t₁,
          l₁ t = ∫ s in (0 : ℝ)..t, edgeCostateRHS₁ (-1) (l₂ s) (x s) (y s) (ue s)) →
        (∀ t ∈ Ioo (-t₁) t₁,
          l₂ t = ∫ s in (0 : ℝ)..t,
            edgeCostateRHS₂ (-1) (l₁ s) (l₂ s) (x₀ ^ 2) (x s) (y s) (ue s)) →
        (fun t ↦ l₂ t - C * t ^ n) =O[𝓝 0] (fun t ↦ t ^ (n + 1)) ∧
          ∀ᶠ t in 𝓝[≠] 0, l₂ t ≠ 0 := by
  sorry

end SmoothedPolygons
