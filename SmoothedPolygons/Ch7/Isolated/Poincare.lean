module

public import SmoothedPolygons.Ch7.Isolated.VertexFlow
public import SmoothedPolygons.Ch7.HMax

/-!
# Theorem 7.7.1, step 4: the Poincaré map

The points `q_fix(y₀)` lie on the section, their Poincaré time is `t_sw(y₀)` and they are fixed
points of the Poincaré map; the Poincaré map is strictly differentiable at the octagon's point.
-/

@[expose] public section

namespace SmoothedPolygons

open Matrix Set Filter Topology MeasureTheory

/-! ### Step 4: the Poincaré map -/

/-- `q_fix(y₀)` lies on the section (Theorem 7.5.1: `Λ_R(0) ⊥ X(0)`, `χ₂₃(0) = 0`, `H = 0`). -/
theorem iso_qFix_isSectionPt (y0 : ℝ) (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) :
    iso_IsSectionPt (iso_qFix y0) := by
  have hy : 0 < y0 := poly_y0_pos hy0
  obtain ⟨htr, -, -, hperp, hchi23, hH, -, -, -⟩ := strongLift_isStrongLift y0 hy0
  have h0 : (0 : ℝ) ∈ Icc 0 (switchTime y0) := ⟨le_rfl, (str_switchTime_pos y0 hy0 hy1).le⟩
  rw [str_segX_zero y0 hy] at hperp hchi23 hH
  refine ⟨by simp [iso_qFix, Φ, Matrix.trace_fin_two], (htr 0 h0).1, (htr 0 h0).2, ?_, ?_, hH,
    hchi23⟩
  · simp only [iso_qFix, Φ, Matrix.det_fin_two_of]
    field_simp
    ring
  · rw [poly_traceForm_comm]
    exact hperp

/-- The Poincaré time of `q_fix(y₀)` is `t_sw(y₀)`: by Lemma 7.5.3, `χ₃₁ > 0` on `[0, t_sw)` and
`χ₃₁(t_sw) = 0`. -/
theorem iso_poincareTime_qFix (y0 : ℝ) (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) :
    iso_poincareTime (iso_qFix y0) = switchTime y0 := by
  have hτ := str_switchTime_pos y0 hy0 hy1
  have hχ := lemma7_5_3 y0 hy0 hy1 _ _ (strongLift_isStrongLift y0 hy0)
  obtain ⟨-, -, -, -, -, -, hchi31, -, -⟩ := strongLift_isStrongLift y0 hy0
  refine IsLeast.csInf_eq ⟨⟨hτ, ?_⟩, fun t ht ↦ ?_⟩
  · rw [iso_vertexFlow_qFix y0 hy0]
    exact hchi31
  · obtain ⟨ht0, ht⟩ := ht
    rw [iso_vertexFlow_qFix y0 hy0] at ht
    refine le_of_not_gt fun hlt ↦ ?_
    exact hlt.ne ((hχ t ⟨ht0.le, hlt.le⟩).2.2.1 ht)

/-- Every `q_fix(y₀)` is a fixed point of the Poincaré map: the strong transversality conditions
of Theorem 7.5.1 and `X(z₀, t_sw) = R⁻¹ X₀ R` (`segX_switchTime`). -/
theorem iso_poincareMap_qFix (y0 : ℝ) (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) :
    iso_poincareMap (iso_qFix y0) = iso_qFix y0 := by
  obtain ⟨-, -, -, -, -, -, -, hR, h1⟩ := strongLift_isStrongLift y0 hy0
  have hc : ∀ A : Mat2, R * (R⁻¹ * A * R) * R⁻¹ = A := fun A ↦ by
    rw [← mul_assoc, ← mul_assoc, poly_R_mul_inv, one_mul, mul_assoc, poly_R_mul_inv, mul_one]
  rw [iso_poincareMap, iso_poincareTime_qFix y0 hy0 hy1, iso_vertexFlow_qFix y0 hy0, iso_adR]
  simp only [segX_switchTime y0 hy0, hR, h1, hc, iso_qFix]

/-- The Poincaré map is strictly differentiable at `q_oct` (in coordinates): the vertex flow is
smooth in `(q, t)`, and by `iso_chi31_hasDerivAt` and the implicit function theorem the Poincaré
time is a `C¹` function of `q` near `q_oct`. -/
theorem iso_poincareMapCoords_hasStrictFDerivAt :
    HasStrictFDerivAt iso_poincareMapCoords
      (fderiv ℝ iso_poincareMapCoords (iso_phaseCoords (iso_qFix (y₀ 1))))
      (iso_phaseCoords (iso_qFix (y₀ 1))) := by
  sorry

end SmoothedPolygons
