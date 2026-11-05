module

public import SmoothedPolygons.Ch2.MultiCurve
public import Basic.Analysis.Calculus.MatrixEntrywise
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Control sets (§3.3)

The state-dependent curvatures `κ_j` (`eqn:state-dep-curvature`), their positivity
(Lemma 3.3.1), the control variables (Definition 3.3.2), the control simplex `U_T`
(Definition 3.3.3, `controlSimplex` in `SmoothedPolygons.Defs`), the control matrix `Z_u`
(`eqn:Z0`, `eqn:def-Z0`) and the star condition in terms of `Z_u` (Lemma 3.3.4).
-/

@[expose] public section

namespace SmoothedPolygons

open MeasureTheory Matrix

/-- The vertex `e_{i+1}` of the control simplex `U_T`: `vertex 0 = e₁ = (1, 0, 0)`,
`vertex 1 = e₂ = (0, 1, 0)`, `vertex 2 = e₃ = (0, 0, 1)`. -/
noncomputable def vertex (i : Fin 3) : Fin 3 → ℝ := Pi.single i 1

/-- The state-dependent curvature `κ_j = det(s_{2j}*, (X + X⁻¹X') s_{2j}*)`, `j = 0, 1, 2`
(`eqn:state-dep-curvature`), as a function of `X` and its derivative `X'`. -/
noncomputable def stateCurvature (X X' : Mat2) (j : Fin 3) : ℝ :=
  det2 (sixthRoot (2 * (j.val : ZMod 6))) ((X + X⁻¹ * X') *ᵥ sixthRoot (2 * (j.val : ZMod 6)))

/-- **Lemma 3.3.1** (`lem:curvature-pos`). Let `g : [0, t_f] → SL₂(ℝ)` be `C¹` with Lipschitz
derivative, and let `X = g⁻¹g'` satisfy the star inequalities and the curvature conditions
`κ_j ≥ 0` (`eqn:state-dep-curvature`) almost everywhere. Then almost everywhere some
`κ_j(t) > 0`. -/
theorem lemma3_3_1 (tf : ℝ) (g g' : ℝ → Mat2)
    (hg : ∀ t ∈ Set.Icc 0 tf, HasDerivWithinAtEntrywise g (g' t) (Set.Icc 0 tf) t)
    (hdet : ∀ t ∈ Set.Icc 0 tf, (g t).det = 1) (hLip : LipschitzOnEntrywise g' (Set.Icc 0 tf))
    (X : ℝ → Mat2) (hX : ∀ t, X t = (g t)⁻¹ * g' t)
    (hstar : ∀ t ∈ Set.Icc 0 tf, 0 < ρ₀ (X t) ∧ 0 < ρ₁ (X t) ∧ 0 < ρ₂ (X t))
    (hcurv : ∀ᵐ t, t ∈ Set.Ioo 0 tf → ∀ j, 0 ≤ stateCurvature (X t) (derivEntrywise X t) j) :
    ∀ᵐ t, t ∈ Set.Ioo 0 tf → ∃ j, 0 < stateCurvature (X t) (derivEntrywise X t) j := by
  sorry

/-- **Definition 3.3.2** (`def:control-variables`). The control variables
`u_j = κ_j / (κ₀ + κ₁ + κ₂)`, the normalized state-dependent curvatures. -/
noncomputable def controlVariables (κ : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun j ↦ κ j / (κ 0 + κ 1 + κ 2)

/-- The control matrix is determined by `u_j = det(s_{2j}*, Z_u s_{2j}*)`, `j = 0, 1, 2`
(`eqn:def-Z0`): `Z_u` satisfies these equations, and it is the only traceless matrix that does. -/
theorem controlMatrix_spec (u : Fin 3 → ℝ) :
    (controlMatrix u).trace = 0 ∧
      (∀ j : Fin 3, u j = det2 (sixthRoot (2 * (j.val : ZMod 6)))
        (controlMatrix u *ᵥ sixthRoot (2 * (j.val : ZMod 6)))) ∧
      ∀ Z : Mat2, Z.trace = 0 → (∀ j : Fin 3, u j = det2 (sixthRoot (2 * (j.val : ZMod 6)))
        (Z *ᵥ sixthRoot (2 * (j.val : ZMod 6)))) → Z = controlMatrix u := by
  sorry

/-- **Lemma 3.3.4** (`lem:sl2-star-condition`). For `X ∈ 𝔰𝔩₂(ℝ)`, the star inequalities hold if
and only if `⟨Z_u, X⟩ < 0` for all controls `u ∈ U_T`. -/
theorem lemma3_3_4 (X : Mat2) (hX : X.trace = 0) :
    (0 < ρ₀ X ∧ 0 < ρ₁ X ∧ 0 < ρ₂ X) ↔ ∀ u ∈ controlSimplex, traceForm (controlMatrix u) X < 0 := by
  sorry

end SmoothedPolygons
