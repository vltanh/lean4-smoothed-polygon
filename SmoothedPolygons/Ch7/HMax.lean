module

public import SmoothedPolygons.Ch7.StrongTransversality

/-!
# The maximum property of the Hamiltonian on one edge (Lemma 7.5.3)
-/

@[expose] public section

namespace SmoothedPolygons

/-- **Lemma 7.5.3** (`lem:H-max-6k+2`). Fix `y₀ ∈ (1/√3, 1)` and `t_sw`, and let `χ_ij` be the
switching functions of the costate trajectory of Theorem 7.5.1 (normalized by `λ_cost = -1`),
with constant control `e₃`. Then the maximum principle holds: `χ₃₁(t) ≥ 0` and `χ₃₂(t) ≥ 0` for
`t ∈ [0, t_sw]`, and they vanish only at `χ₃₂(0) = 0` and `χ₃₁(t_sw) = 0`. (`χ₃₁` is
`switchingFn 2 0`, `χ₃₂` is `switchingFn 2 1`.) -/
theorem lemma7_5_3 (y0 : ℝ) (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) (Λ₁ ΛR : ℝ → Mat2)
    (h : IsStrongLift y0 Λ₁ ΛR (-1)) :
    ∀ t ∈ Set.Icc 0 (switchTime y0),
      0 ≤ switchingFn 2 0 (ΛR t) (segX y0 t) ∧ 0 ≤ switchingFn 2 1 (ΛR t) (segX y0 t) ∧
        (switchingFn 2 0 (ΛR t) (segX y0 t) = 0 → t = switchTime y0) ∧
        (switchingFn 2 1 (ΛR t) (segX y0 t) = 0 → t = 0) := by
  sorry

end SmoothedPolygons
