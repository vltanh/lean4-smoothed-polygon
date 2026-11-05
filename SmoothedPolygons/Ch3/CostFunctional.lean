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
  refine ⟨hg.mulVec_const u, ?_⟩
  -- `det(gu, gXu) = det(g) det(u, Xu) = det(u, Xu)`
  have h1 : det2 (g t *ᵥ u) ((g t * X t) *ᵥ u) = (g t).det * det2 u (X t *ᵥ u) := by
    rw [← Matrix.mulVec_mulVec]
    simp only [det2, Matrix.det_fin_two, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  -- `eqn:wedge-inner`: `det(u, Xv) = -uᵀ J X v`
  have h2 : det2 u (X t *ᵥ u) = -(u ⬝ᵥ ((J * X t) *ᵥ u)) := by
    simp [det2, J, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.mul_apply]
    ring
  rw [h1, hdet, one_mul, h2]

/-- **Lemma 3.2.2** (`lem:area-helper-2`). For `Y ∈ 𝔰𝔩₂(ℝ)`,
`JY + (R²)ᵀ J Y R² + (R⁴)ᵀ J Y R⁴ = (3 tr(JY)/2) I₂`. -/
theorem lemma3_2_2 (Y : Mat2) (hY : Y.trace = 0) :
    J * Y + (R ^ 2)ᵀ * J * Y * R ^ 2 + (R ^ 4)ᵀ * J * Y * R ^ 4 =
      (3 * (J * Y).trace / 2) • (1 : Mat2) := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h3sq : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hR2 : R ^ 2 = !![-(1 / 2), -(√3 / 2); √3 / 2, -(1 / 2)] := by
    rw [pow_two, R]
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> linarith [h3]
  have hR4 : R ^ 4 = !![-(1 / 2), √3 / 2; -(√3 / 2), -(1 / 2)] := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, hR2, pow_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> linarith [h3]
  have hY11 : Y 1 1 = -Y 0 0 := by
    rw [Matrix.trace_fin_two] at hY; linear_combination hY
  rw [hR2, hR4]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, hY11, Matrix.vecMul,
      dotProduct] <;>
    ring_nf <;> simp only [h3sq] <;> ring

end SmoothedPolygons
