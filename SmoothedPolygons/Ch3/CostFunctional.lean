module

public import SmoothedPolygons.Ch2.MultiCurve
public import Basic.Analysis.Calculus.MatrixEntrywise

/-!
# The cost functional (§3.2)

The pullback of the one-form `θ = x dy - y dx` along a curve `γ(t) = g(t) u` (Lemma 3.2.1) and an
averaging identity over the rotations `R²`, `R⁴` (Lemma 3.2.2), which together give the area
formula `area(K) = -(3/2) ∫ tr(JX) dt` (`eqn:cost`).
-/

@[expose] public section

namespace SmoothedPolygons

open Matrix

/-- **Lemma 3.2.1** (`lem:area-helper-1`). Let `g' = gX` with `det g = 1`, let `u ∈ ℝ²` and
`γ(t) = g(t) u`. Then the pullback of `θ = x dy - y dx` is `γ*θ = -uᵀ J X u dt`. The pullback is
represented by its coefficient `γ₁ γ₂' - γ₂ γ₁' = det(γ, γ')`. -/
theorem lemma3_2_1 (g X : ℝ → Mat2) (t : ℝ) (hg : HasDerivAtEntrywise g (g t * X t) t)
    (hdet : (g t).det = 1) (u : Fin 2 → ℝ) :
    HasDerivAt (fun s ↦ g s *ᵥ u) ((g t * X t) *ᵥ u) t ∧
      det2 (g t *ᵥ u) ((g t * X t) *ᵥ u) = -(u ⬝ᵥ ((J * X t) *ᵥ u)) := by
  sorry

/-- **Lemma 3.2.2** (`lem:area-helper-2`). For `Y ∈ 𝔰𝔩₂(ℝ)`,
`JY + (R²)ᵀ J Y R² + (R⁴)ᵀ J Y R⁴ = (3 tr(JY)/2) I₂`. -/
theorem lemma3_2_2 (Y : Mat2) (hY : Y.trace = 0) :
    J * Y + (R ^ 2)ᵀ * J * Y * R ^ 2 + (R ^ 4)ᵀ * J * Y * R ^ 4 =
      (3 * (J * Y).trace / 2) • (1 : Mat2) := by
  sorry

end SmoothedPolygons
