module

public import SmoothedPolygons.Ch7.Polygon

/-!
# The discreteness condition (Lemma 7.5.5)
-/

@[expose] public section

namespace SmoothedPolygons

/-- **Lemma 7.5.5** (`lem:discrete-k`). Consider a trajectory `g : [0, t_f] → SL₂(ℝ)` with
`g(0) = I₂` following the spline with `3k+1` control mode parts of equal duration `t_sw`
(`eqn:3k+1`), from `z₀ = i y₀`. The trajectory reaches `g(t_f) = R` at `t_f = (3k+1) t_sw`,
provided `4/(3y₀² + 1) = 2 cos θ_k` with `θ_k = πk/(3k+1)` (`eqn:theta-k`). -/
theorem lemma7_5_5 (k : ℕ) (hk : 1 ≤ k) (y0 : ℝ) (hy0 : 1 / √3 < y0) (hy1 : y0 < 1)
    (hθ : 4 / (3 * y0 ^ 2 + 1) = 2 * Real.cos (θ k)) (g X : ℝ → Mat2)
    (h : IsStateTrajectory ((3 * k + 1) * switchTime y0) (polygonControlAt (switchTime y0)) g X)
    (hg0 : g 0 = 1) (hX0 : X 0 = Φ 0 y0) :
    g ((3 * k + 1) * switchTime y0) = R := by
  sorry

end SmoothedPolygons
