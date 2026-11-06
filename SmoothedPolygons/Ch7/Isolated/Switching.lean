module

public import SmoothedPolygons.Ch7.Isolated.Defs
public import SmoothedPolygons.Ch7.HMax

/-!
# Theorem 7.7.1, step 2: transversality of the switching times

Step 2: the slopes of `χ₃₂` at `0` and of `χ₃₁` at `t_sw` along the strong lift (the remark after
Lemma 7.5.3), their sign, and the independence of the slope of `χ₃₂` on the switching surface from
the control on the edge `[e₂, e₃]`.
-/

@[expose] public section

namespace SmoothedPolygons

open Matrix Set Filter Topology MeasureTheory

/-! ### Step 2: transversality of the switching times -/

/-- The remark after Lemma 7.5.3: `χ₃₂` vanishes at `t = 0` with slope `iso_chi32Slope y₀`
(`∂f/∂r = -∂f/∂y = y((4 - y) - y ln(4/y))` on the diagonal, eqn:f'). -/
theorem iso_chi32_hasDerivAt (y0 : ℝ) (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) :
    HasDerivAt (fun t ↦ switchingFn 2 1 (strongΛR y0 t) (segX y0 t)) (iso_chi32Slope y0) 0 := by
  sorry

/-- By the symmetry `χ₃₁(t_sw - t) = χ₃₂(t)` (proof of Lemma 7.5.3), `χ₃₁` vanishes at `t_sw`
with slope `-iso_chi32Slope y₀`: the end of the first arc is a transversal switching time, the
hypothesis of the implicit function theorem for the Poincaré time. -/
theorem iso_chi31_hasDerivAt (y0 : ℝ) (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) :
    HasDerivAt (fun t ↦ switchingFn 2 0 (strongΛR y0 t) (segX y0 t)) (-iso_chi32Slope y0)
      (switchTime y0) := by
  sorry

/-- On the switching surface `χ₂₃ = 0`, the derivative of `χ₃₂` along the state–costate vector
field is the same for every control `u` on the edge `[e₂, e₃]` of `U_T` (it is the Poisson
bracket `{H₃, H₂}`: the Hamiltonian vector field of `H_u` is a convex combination of those of
`H₂` and `H₃` where `H₂ = H₃`). With `iso_chi32_hasDerivAt` this excludes singular arcs and
chattering near the octagon's switching points. -/
theorem iso_edge_slope (q : iso_PhasePt) (hX : q.1.trace = 0) (hR : q.2.2.trace = 0)
    (hstar : IsStarState q.1) (hχ : switchingFn 1 2 q.2.2 q.1 = 0) (u : Fin 3 → ℝ)
    (hu : u ∈ controlSimplex) (hu0 : u 0 = 0) :
    HasDerivAt (fun s : ℝ ↦ switchingFn 2 1 (q.2.2 + s • (iso_extremalField u q).2.2)
        (q.1 + s • (iso_extremalField u q).1))
      (deriv (fun s : ℝ ↦ switchingFn 2 1 (q.2.2 + s • (iso_extremalField (vertex 2) q).2.2)
        (q.1 + s • (iso_extremalField (vertex 2) q).1)) 0) 0 := by
  sorry

/-- The slope of the remark after Lemma 7.5.3 is positive: `4 - Y - Y ln(4/Y) > 0` for
`Y = 1 + 3y₀² ∈ (2, 4)`, by `ln x < x - 1` (`x = 4/Y ≠ 1`). -/
theorem iso_chi32Slope_pos (y0 : ℝ) (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) : 0 < iso_chi32Slope y0 := by
  obtain ⟨hY2, hY4⟩ := hmax_y_mem hy0 hy1
  have hy : 0 < y0 := poly_y0_pos hy0
  have hYpos : 0 < 1 + 3 * y0 ^ 2 := by linarith
  have hlog : ellSw y0 < 4 / (1 + 3 * y0 ^ 2) - 1 := by
    rw [ellSw, show 3 * y0 ^ 2 + 1 = 1 + 3 * y0 ^ 2 by ring]
    refine Real.log_lt_sub_one_of_pos (by positivity) fun h ↦ ?_
    rw [div_eq_one_iff_eq hYpos.ne'] at h
    linarith
  have hkey : 0 < 4 - (1 + 3 * y0 ^ 2) - (1 + 3 * y0 ^ 2) * ellSw y0 := by
    have h' := mul_lt_mul_of_pos_left hlog hYpos
    rw [mul_sub, mul_div_cancel₀ _ hYpos.ne', mul_one] at h'
    linarith
  unfold iso_chi32Slope
  positivity

end SmoothedPolygons
