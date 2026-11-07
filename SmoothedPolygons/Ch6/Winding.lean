module

public import SmoothedPolygons.Ch3.ControlProblem
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The winding number of an admissible trajectory

Problem 3.6.2 asks for `g(0) = I`, `g(t_f) = R` and `X(t_f) = R⁻¹X(0)R`. The book derives these
conditions so that "the curves `σ_j` close up seamlessly to form a simple closed curve" (§3.5,
TeX 3134–3139), but they do not force simplicity. Along an admissible trajectory the curve
`σ₀(t) = g(t) s₀*` turns counterclockwise about the origin (`det(s₀*, X s₀*) = X₁₀ > 0`), and
its continuous angle `θ` with `θ(0) = 0` ends at `θ(t_f) = π/3 + 2πm` for some `m ∈ ℕ`
(`g(t_f) s₀* = R s₀* = s₁*`); extended by `g(t + t_f) = g(t) R`, the closed curve `σ₀` on
`[0, 6t_f]` winds `1 + 6m` times around the origin. The book's construction (Chapters 2–3) only
produces `m = 0`; it notes in the proof of Lemma 7.5.5 (TeX 6322–6326) that other choices of
eigenvalues "will produce the right boundary conditions, but the corresponding multi-curves will
have the wrong winding number around the origin".

* `IsWindingOne T g`: the angle of `g(t) s₀*` increases by exactly `π/3` on `[0, T]` (`m = 0`).
* `exists_isReinhardtAdmissible_not_isWindingOne` (**the answer to the winding-number question**):
  admissible trajectories of higher winding exist. The unit circle traversed seven times
  (`X ≡ J`, `u ≡ (1/3, 1/3, 1/3)`, `g(t) = exp(tJ)`, `t_f = 7π/3`) is admissible, has winding
  number `7` and cost `7π`, and bounds no balanced disk with `σ_j = g s_j*`
  (`σ₀(0) = σ₀(2π)`, so `σ₀` is not injective on `[0, 6t_f)`). Hence the converse of
  Problem 3.6.2 (E15) is false for all admissible trajectories, and holds only for those of
  winding number one (`exists_isBalancedPair_of_isReinhardtAdmissible`,
  `SmoothedPolygons/Ch6/AdmissibleDisk.lean`).
* `three_halves_mul_angle_le_reinhardtCost`: **higher winding costs more**: the cost is at least
  `(3/2)θ(t_f) = π/2 + 3πm`. Hence an admissible trajectory with cost `< 7π/2` (for instance one
  cheaper than the smoothed octagon, of cost `≈ 3.126`) has winding number one
  (`isWindingOne_of_reinhardtCost_lt`). So the existence of a global minimizer is not affected by
  the higher-winding trajectories, and Theorem 5.0.2 can be applied to every competitor that
  matters.

## Proof of the cost bound (to be written; not in the book)

Write `g = n(ν) a(ρ) k(ψ)` (Iwasawa decomposition `NAK`: `n(ν) = [[1, ν], [0, 1]]`,
`a(ρ) = diag(e^ρ, e^{-ρ})`, `k(ψ)` the rotation by `ψ`), so `(g₁₁, g₁₀) = e^{-ρ}(cos ψ, sin ψ)`,
and let `w = g · i = ν + i e^{2ρ}` (`X_h + iY_h`) in the upper half-plane, a closed loop
(`g(0) · i = R · i = i`). With `X = g⁻¹g'` (almost everywhere):

1. `-tr(JX) = 2ψ' - X_h'/Y_h` (from `X = k⁻¹(B⁻¹B')k + ψ'J`, `B = n a`, `tr(J k⁻¹ Y k) = tr(JY)`
   and `tr(J B⁻¹B') = ν' e^{-2ρ}`).
2. `|X_h'|/Y_h ≤ |w'|/Y_h = √((b + c)² + 4a²) = √(κ² - 4) ≤ κ`, where `X = [[a, b], [c, -a]]`,
   `κ = c - b = -tr(JX)` and `det X = 1` (the hyperbolic speed of `g · i` is that of
   `exp(sX) · i` at `i`).
3. Integrating, `∫κ = 2Δψ - ∫X_h'/Y_h ≥ 2Δψ - ∫κ`, so `cost = (3/2)∫κ ≥ (3/2)Δψ`.
4. `Δψ = θ(t_f) - θ(0)`: the vectors `(g₀₀, g₁₀)` (angle `θ`) and `(g₁₁, g₁₀)` (angle `ψ`) lie in
   the same open half-plane `{v₁ > 0}` or `{v₁ < 0}`, or both on the `x`-axis with the same sign
   (`det g = 1`), so `|θ - ψ| < π` along the path; at `t = 0` and `t = t_f` (`g = I`, `g = R`)
   the two vectors coincide.

Steps 1–3 are a Gauss–Bonnet formula for the loop `g · i`: `cost = 3Δψ - (3/2)∮ dX_h/Y_h`, and
`∮ dX_h/Y_h` is the hyperbolic area enclosed, bounded by the hyperbolic length
`∫√(κ² - 4) < (2/3) cost`. Size: 500–900 lines (angle lifts, a.e. derivatives of
absolutely continuous curves, the algebra of steps 1–2).
-/

@[expose] public section

namespace SmoothedPolygons

open MeasureTheory Set Matrix

/-- An admissible trajectory has **winding number one** on `[0, T]`: the continuous angle `θ` of
`σ₀(t) = g(t) s₀*` with `θ(0) = 0` ends at `θ(T) = π/3` (rather than `π/3 + 2πm`, `m ≥ 1`), so
that the closed curve `σ₀` on `[0, 6T]` (extended by `g(t + T) = g(t) R`) winds once around the
origin. -/
def IsWindingOne (T : ℝ) (g : ℝ → Mat2) : Prop :=
  ∃ θ : ℝ → ℝ, ContinuousOn θ (Icc 0 T) ∧ θ 0 = 0 ∧ θ T = Real.pi / 3 ∧
    ∀ t ∈ Icc 0 T, ∃ r : ℝ, 0 < r ∧
      g t *ᵥ sixthRoot 0 = r • ![Real.cos (θ t), Real.sin (θ t)]

/-- Along an admissible trajectory, `σ₀ = g s₀*` turns counterclockwise about the origin, and its
continuous angle `θ` with `θ(0) = 0` ends at `θ(T) = π/3 + 2πm` for some `m ∈ ℕ`. -/
theorem exists_angle_of_isReinhardtAdmissible {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsReinhardtAdmissible T u g X) :
    ∃ θ : ℝ → ℝ, ContinuousOn θ (Icc 0 T) ∧ θ 0 = 0 ∧ StrictMonoOn θ (Icc 0 T) ∧
      (∃ m : ℕ, θ T = Real.pi / 3 + 2 * Real.pi * m) ∧
      ∀ t ∈ Icc 0 T, ∃ r : ℝ, 0 < r ∧
        g t *ᵥ sixthRoot 0 = r • ![Real.cos (θ t), Real.sin (θ t)] := by
  sorry

/-- **Higher winding costs more.** For an admissible trajectory and the continuous angle `θ` of
`g(t) s₀*` with `θ(0) = 0`, the cost is at least `(3/2) θ(T)`; with `θ(T) = π/3 + 2πm`, at least
`π/2 + 3πm`. (Not in the book; see the module docstring for the proof.) -/
theorem three_halves_mul_angle_le_reinhardtCost {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsReinhardtAdmissible T u g X) {θ : ℝ → ℝ} (hθc : ContinuousOn θ (Icc 0 T))
    (hθ0 : θ 0 = 0)
    (hθ : ∀ t ∈ Icc 0 T, ∃ r : ℝ, 0 < r ∧
      g t *ᵥ sixthRoot 0 = r • ![Real.cos (θ t), Real.sin (θ t)]) :
    3 / 2 * θ T ≤ reinhardtCost T X := by
  sorry

/-- An admissible trajectory of cost less than `7π/2` has winding number one. -/
theorem isWindingOne_of_reinhardtCost_lt {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsReinhardtAdmissible T u g X) (hc : reinhardtCost T X < 7 * Real.pi / 2) :
    IsWindingOne T g := by
  sorry

/-- **Admissible trajectories of higher winding exist** (the winding-number question of the
inventory, Part I §3.5, item 6). The unit circle traversed seven times, `X ≡ J`,
`u ≡ (1/3, 1/3, 1/3)`, `g(t) = exp(tJ)` on `[0, 7π/3]`, is admissible for Problem 3.6.2, does not
have winding number one, costs `7π`, and bounds no balanced disk with `σ_j = g s_j*` on
`[0, t_f]`: so the converse of Problem 3.6.2 (E15) fails for it. -/
theorem exists_isReinhardtAdmissible_not_isWindingOne :
    ∃ (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X : ℝ → Mat2), IsReinhardtAdmissible T u g X ∧
      ¬ IsWindingOne T g ∧ reinhardtCost T X = 7 * Real.pi ∧
      ¬ ∃ (K : Set (Fin 2 → ℝ)) (σ : ZMod 6 → ℝ → Fin 2 → ℝ), IsBalancedPair K σ T ∧
        ∀ j, ∀ t ∈ Icc 0 T, σ j t = g t *ᵥ sixthRoot j := by
  sorry

end SmoothedPolygons
