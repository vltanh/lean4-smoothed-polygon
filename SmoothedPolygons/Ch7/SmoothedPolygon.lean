module

public import SmoothedPolygons.Ch7.HMax
public import SmoothedPolygons.Ch7.DiscreteK
public import SmoothedPolygons.Ch7.Faces

/-!
# The smoothed `(6k+2)`-gons are Pontryagin extremals (Theorem 7.5.6)

The trajectory of the smoothed `(6k+2)`-gon is the state trajectory with the control
`polygonControl k` (`e₃, e₁, e₂, …` on `3k+1` switching intervals of length `t_sw`), `g(0) = I₂`
and `X(0) = Φ(i y₀)`, where `4/(3y₀² + 1) = 2 cos θ_k`. It exists and is unique; it is a bang-bang
Pontryagin extremal (Theorem 7.5.6). For `k = 1` it is the smoothed octagon, whose cost (the area
of the disk in circle representation) gives Reinhardt's density `(8 - √32 - ln 2)/(√8 - 1)`
(the example before Theorem 7.5.6).
-/

@[expose] public section

namespace SmoothedPolygons

/-- The state trajectory of the smoothed `(6k+2)`-gon is unique: any two state trajectories with
the control `polygonControl k` and the initial values `g(0) = I₂`, `X(0) = Φ(i y₀)` agree on
`[0, t_f]` with the spline `(polygonG, polygonX)`. -/
theorem polygon_trajectory_unique (k : ℕ) (hk : 1 ≤ k) (g X : ℝ → Mat2)
    (h : IsStateTrajectory (tf k) (polygonControl k) g X) (hg0 : g 0 = 1) (hX0 : X 0 = Φ 0 (y₀ k)) :
    ∀ t ∈ Set.Icc 0 (tf k), g t = polygonG (y₀ k) (tsw k) t ∧ X t = polygonX (y₀ k) (tsw k) t := by
  sorry

/-- **Theorem 7.5.6** (`thm:6k+2`). For each positive integer `k`, the smoothed `(6k+2)`-gon is a
Pontryagin extremal given by a bang-bang control: the state trajectory with the control
`polygonControl k` and `g(0) = I₂`, `X(0) = Φ(i y₀)` exists, its control is bang-bang, and it lifts
to a Pontryagin extremal. -/
theorem theorem7_5_6 (k : ℕ) (hk : 1 ≤ k) :
    (∃ g X : ℝ → Mat2, IsStateTrajectory (tf k) (polygonControl k) g X ∧ g 0 = 1 ∧
      X 0 = Φ 0 (y₀ k)) ∧
    ∀ g X : ℝ → Mat2, IsStateTrajectory (tf k) (polygonControl k) g X → g 0 = 1 →
      X 0 = Φ 0 (y₀ k) →
      IsBangBang (tf k) (polygonControl k) ∧
        ∃ (Λ₁ ΛR : ℝ → Mat2) (lam : ℝ),
          IsPontryaginExtremal (tf k) (polygonControl k) g X Λ₁ ΛR lam := by
  sorry

/-- **Example** (the smoothed octagon, before Theorem 7.5.6; label `ex:smoothed-octagon` here).
For `k = 1`: `θ₁ = π/4`, the trace of `R⁻¹ g_sw` is `√2`, `y₀ = √((√8 - 1)/3)`,
`t_sw = ln 2/(2√(√8 - 1))`, and for the trajectory of the smoothed octagon (`t_f = 4 t_sw`)
`area(K_oct) = -6 ∫₀^{t_sw} ⟨J, X⟩ dt = √12 (8 - √32 - ln 2)/(√8 - 1) ≈ 3.126 < π`, so the density
`δ = area(K_oct)/√12` is `(8 - √32 - ln 2)/(√8 - 1)` (`eqn:density-formula`). The area is the
cost `-(3/2) ∫₀^{t_f} ⟨J, X⟩ dt` (`eqn:cost`). -/
theorem example7_5_smoothedOctagon :
    θ 1 = Real.pi / 4 ∧ (R⁻¹ * segG (y₀ 1) (tsw 1)).trace = √2 ∧
      y₀ 1 = √((√8 - 1) / 3) ∧ tsw 1 = Real.log 2 / (2 * √(√8 - 1)) ∧
      ∀ g X : ℝ → Mat2, IsStateTrajectory (tf 1) (polygonControl 1) g X → g 0 = 1 →
        X 0 = Φ 0 (y₀ 1) →
        reinhardtCost (tf 1) X = -6 * ∫ t in (0 : ℝ)..tsw 1, traceForm J (X t) ∧
          reinhardtCost (tf 1) X = √12 * (8 - √32 - Real.log 2) / (√8 - 1) ∧
          reinhardtCost (tf 1) X < Real.pi ∧
          reinhardtCost (tf 1) X / √12 = (8 - √32 - Real.log 2) / (√8 - 1) := by
  sorry

end SmoothedPolygons
