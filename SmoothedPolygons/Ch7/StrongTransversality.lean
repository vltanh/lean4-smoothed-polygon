module

public import SmoothedPolygons.Ch7.Polygon

/-!
# One edge of the triangle: the strong transversality conditions (Theorem 7.5.1)

On the first switching interval `[0, t_sw]`, with constant control `e₃` from `z₀ = i y₀`, the state
trajectory lifts, uniquely up to a scalar, to a costate trajectory `(Λ₁, Λ_R, λ_cost)` with
`Λ_R(0) ⊥ X(0)`, `χ₂₃(0) = 0`, `H = 0`, `χ₃₁(t_sw) = 0` and the strong transversality conditions
`Λ_R(t_sw) = R⁻¹Λ_R(0)R`, `Λ₁(t_sw) = R⁻¹Λ₁(0)R`; the lift is normal.

The switching functions `χ_ij` of the book (`eqn:switch`) are indexed by the vertices `e₁, e₂, e₃`
of `U_T`; here they are indexed by `Fin 3`, with `e₁, e₂, e₃` as `0, 1, 2`.
-/

@[expose] public section

namespace SmoothedPolygons

open Matrix

/-- The switching function `χ_ij = ⟨Λ_R, P_j - P_i⟩` (`eqn:switch`), with
`P_k = Z_{e_k}/⟨Z_{e_k}, X⟩`; `χ_ij = H(e_i) - H(e_j)`. Indices: `0, 1, 2` stand for the book's
`1, 2, 3`. The book evaluates `P_{i,i}` at the initial `X₀`; along the constant control `e_i` it
is constant (Lemma 7.1.1), so both forms agree. -/
noncomputable def switchingFn (i j : Fin 3) (ΛR X : Mat2) : ℝ :=
  traceForm ΛR (controlP (vertex j) X - controlP (vertex i) X)

/-- The conditions of Theorem 7.5.1 on a costate lift `(Λ₁, Λ_R, λ_cost)` of the `e₃`-trajectory
`X(t) = X(z₀, t)` on `[0, t_sw]`, `z₀ = i y₀`: traceless costates solving the costate equations
with control `e₃`; `Λ_R(0) ∈ X(0)^⊥` and `χ₂₃(0) = 0` (`eqn:init-lambdaR`); `H_{u=e₃} = 0` and
`χ₃₁(t_sw) = 0` (`eqn:init-H-chi`); and the strong transversality conditions
`Λ_R(t_sw) = R⁻¹Λ_R(0)R`, `Λ₁(t_sw) = R⁻¹Λ₁(0)R`. -/
def IsStrongLift (y0 : ℝ) (Λ₁ ΛR : ℝ → Mat2) (lam : ℝ) : Prop :=
  (∀ t ∈ Set.Icc 0 (switchTime y0), (Λ₁ t).trace = 0 ∧ (ΛR t).trace = 0) ∧
    (∀ t ∈ Set.Icc 0 (switchTime y0), HasDerivWithinAtEntrywise Λ₁
      (Λ₁ t * segX y0 t - segX y0 t * Λ₁ t) (Set.Icc 0 (switchTime y0)) t) ∧
    (∀ t ∈ Set.Icc 0 (switchTime y0), HasDerivWithinAtEntrywise ΛR
      (costateRHS lam (Λ₁ t) (ΛR t) (segX y0 t) (vertex 2)) (Set.Icc 0 (switchTime y0)) t) ∧
    traceForm (ΛR 0) (segX y0 0) = 0 ∧ switchingFn 1 2 (ΛR 0) (segX y0 0) = 0 ∧
    hamiltonian lam (Λ₁ 0) (ΛR 0) (segX y0 0) (vertex 2) = 0 ∧
    switchingFn 2 0 (ΛR (switchTime y0)) (segX y0 (switchTime y0)) = 0 ∧
    ΛR (switchTime y0) = R⁻¹ * ΛR 0 * R ∧ Λ₁ (switchTime y0) = R⁻¹ * Λ₁ 0 * R

/-- **Theorem 7.5.1** (`thm:strong-transversality`). Let `y₀ ∈ (1/√3, 1)`, `z₀ = i y₀`, `t_sw`
given by `eqn:t1`, and let `z(z₀, t)`, `g(t) = g₀(z₀, t)` be the solutions of the state equations
with constant control `e₃` on `[0, t_sw]`. These solutions lift uniquely, up to a scalar factor, to
a costate trajectory `(Λ₁, Λ_R, λ_cost)` with `Λ_R(0) ∈ X(0)^⊥`, `χ₂₃(0) = 0`, `H_{u=e₃} = 0`,
`χ₃₁(t_sw) = 0` and the strong transversality conditions; the trajectory is normal,
`λ_cost ≠ 0`. Here: there is such a lift with `λ_cost = -1`, and the lifts are exactly its scalar
multiples `c • (Λ₁, Λ_R, -1)`, so a nonzero lift has `λ_cost = -c ≠ 0`. -/
theorem theorem7_5_1 (y0 : ℝ) (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) :
    ∃ Λ₁ ΛR : ℝ → Mat2, IsStrongLift y0 Λ₁ ΛR (-1) ∧
      ∀ (Λ₁' ΛR' : ℝ → Mat2) (lam : ℝ), IsStrongLift y0 Λ₁' ΛR' lam ↔
        ∃ c : ℝ, lam = -c ∧
          ∀ t ∈ Set.Icc 0 (switchTime y0), Λ₁' t = c • Λ₁ t ∧ ΛR' t = c • ΛR t := by
  sorry

/-- The values found in the proof of Theorem 7.5.1: a strong lift with `λ_cost = -1` has
`Λ₁(0) = λ₁ Λ₁₀` and `Λ_R(0) = λ_R [[0, y₀²], [1, 0]]`, where `ℓ = ln(4/(3y₀² + 1))`,
`Λ₁₀ = [[0, 4√3 y₀⁴], [-√3(1 + y₀²)(3y₀² - 1), 0]]/(2y₀²(1 + 3y₀²))`,
`λ₁ = -(1 + 3y₀²)(-3 - 6y₀² + (1 + 3y₀²)ℓ)/(12√3 y₀⁴)` and
`λ_R = -(3 - 12y₀² - 9y₀⁴ + 18y₀⁶ + (-1 + 3y₀² + 21y₀⁴ + 9y₀⁶)ℓ)/(24y₀⁶)`. -/
theorem strongLift_initial (y0 : ℝ) (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) (Λ₁ ΛR : ℝ → Mat2)
    (h : IsStrongLift y0 Λ₁ ΛR (-1)) :
    Λ₁ 0 = (-(1 + 3 * y0 ^ 2) * (-3 - 6 * y0 ^ 2 + (1 + 3 * y0 ^ 2) *
        Real.log (4 / (3 * y0 ^ 2 + 1))) / (12 * √3 * y0 ^ 4)) •
        ((2 * y0 ^ 2 * (1 + 3 * y0 ^ 2))⁻¹ •
          !![0, 4 * √3 * y0 ^ 4; -(√3 * (1 + y0 ^ 2) * (3 * y0 ^ 2 - 1)), 0]) ∧
      ΛR 0 = (-(3 - 12 * y0 ^ 2 - 9 * y0 ^ 4 + 18 * y0 ^ 6 +
        (-1 + 3 * y0 ^ 2 + 21 * y0 ^ 4 + 9 * y0 ^ 6) * Real.log (4 / (3 * y0 ^ 2 + 1))) /
          (24 * y0 ^ 6)) • !![0, y0 ^ 2; 1, 0] := by
  sorry

end SmoothedPolygons
