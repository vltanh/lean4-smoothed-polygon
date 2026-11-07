module

public import SmoothedPolygons.Ch6.MatrixSystem

/-!
# Reinhardt trajectories and the matrix system (§3.5, §6.2)

The admissible pairs of the matrix system (`SmoothedPolygons/Ch6/MatrixSystem.lean`) that satisfy
its boundary condition `matrixEndpoints` are the admissible trajectories of the Reinhardt control
problem (Problem 3.6.2, TeX 3203), with the same cost:

* a Reinhardt state trajectory `(g, X)` is an admissible pair `t ↦ (g(t), X(t))` of the matrix
  system in `GL₂⁺(ℝ) × C` (`IsStateTrajectory.isAdmissibleIn_matrix`);
* along an admissible pair, `det g` and `det X` are constant (`det_stateG_eq_of_isAdmissibleIn`,
  `det_stateX_eq_of_isAdmissibleIn`): `(det g)' = det g · tr X = 0` and
  `(det X)' = -⟨X, [P, X]⟩ = 0`, for the absolutely continuous solutions of Carathéodory's sense;
* hence an admissible pair with `(q(0), q(t_f)) ∈ matrixEndpoints` is an admissible trajectory of
  Problem 3.6.2 (`isReinhardtAdmissible_of_mem_matrixEndpoints`): `g(t) ∈ SL₂(ℝ)`,
  `X(t)` is a star state, and the two boundary equations left out of `matrixBoundary` hold
  (`det g(t_f) = 1` with `R₀₀ = 1/2 ≠ 0`; `det X(t_f) = 1` with `X(t_f)₀₁ < 0`);
* the costs agree (`cost_matrixCost`), so a global minimizer of Problem 3.6.2 is a strong local
  minimizer of the matrix system (`IsReinhardtMinimizer.isStrongLocalMinimizer_matrix`).
-/

@[expose] public section

namespace SmoothedPolygons

open Set MeasureTheory Pontryagin ControlSystem

/-- The cost of a pair of the matrix system is the Reinhardt cost of its `X`. -/
theorem cost_matrixCost (T : ℝ) (u : ℝ → Fin 3 → ℝ) (q : ℝ → MatrixState) :
    cost matrixCost T u q = reinhardtCost T (fun t ↦ stateX (q t)) := by
  simp [cost, matrixCost, reinhardtCost, intervalIntegral.integral_const_mul]

/-- A Reinhardt state trajectory is an admissible pair of the matrix system in `GL₂⁺(ℝ) × C`
(the entrywise integral equations of `IsStateTrajectory` are the integral equation of the pair;
`det g = 1 > 0`, and the star conditions put `X` in `C`). -/
theorem IsStateTrajectory.isAdmissibleIn_matrix {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsStateTrajectory T u g X) :
    IsAdmissibleIn matrixField matrixDomain controlSimplex (toMatrixState (g 0) (X 0)) T u
      (fun t ↦ toMatrixState (g t) (X t)) := by
  sorry

/-- **`det g` is a first integral**: along an admissible pair of the matrix system,
`(det g)' = det g · tr X = 0`. -/
theorem det_stateG_eq_of_isAdmissibleIn {T : ℝ} (hT : 0 ≤ T) {u : ℝ → Fin 3 → ℝ}
    {q : ℝ → MatrixState} (h : IsAdmissibleIn matrixField matrixDomain controlSimplex (q 0) T u q) :
    ∀ t ∈ Icc 0 T, (stateG (q t)).det = (stateG (q 0)).det := by
  sorry

/-- **`det X` is a first integral**: along an admissible pair of the matrix system,
`(det X)' = -⟨X, X'⟩ = -⟨X, [P, X]⟩ = 0` (`X' = [P, X]` is isospectral). -/
theorem det_stateX_eq_of_isAdmissibleIn {T : ℝ} (hT : 0 ≤ T) {u : ℝ → Fin 3 → ℝ}
    {q : ℝ → MatrixState} (h : IsAdmissibleIn matrixField matrixDomain controlSimplex (q 0) T u q) :
    ∀ t ∈ Icc 0 T, (stateX (q t)).det = (stateX (q 0)).det := by
  sorry

/-- An admissible pair of the matrix system with `det g(0) = 1` and `det X(0) = 1` projects to a
Reinhardt state trajectory (the first integrals keep `g` in `SL₂(ℝ)` and `X` among the star
states). -/
theorem isStateTrajectory_of_isAdmissibleIn_matrix {T : ℝ} (hT : 0 < T) {u : ℝ → Fin 3 → ℝ}
    {q : ℝ → MatrixState} (h : IsAdmissibleIn matrixField matrixDomain controlSimplex (q 0) T u q)
    (hg : (stateG (q 0)).det = 1) (hX : (stateX (q 0)).det = 1) :
    IsStateTrajectory T u (fun t ↦ stateG (q t)) (fun t ↦ stateX (q t)) := by
  sorry

/-- **Competitors are Reinhardt-admissible**: an admissible pair of the matrix system satisfying
the boundary condition `matrixEndpoints` projects to an admissible trajectory of Problem 3.6.2.
The two boundary equations left out of `matrixBoundary` hold: `det g(t_f) = 1` and
`g(t_f)₀₀ = R₀₀ = 1/2 ≠ 0` give `g(t_f)₁₁ = R₁₁`; `det X(t_f) = 1 = det(R⁻¹X(0)R)` and
`X(t_f)₀₁ < 0` (on `C`: `ρ₀ + ρ₁ > 0` gives `X₁₀ > 0`, and `ρ₂ > 0` gives `3X₀₁ + X₁₀ < 0`) give
`X(t_f)₁₀ = -(1 + X(t_f)₀₀²)/X(t_f)₀₁ = (R⁻¹X(0)R)₁₀`. -/
theorem isReinhardtAdmissible_of_mem_matrixEndpoints {T : ℝ} (hT : 0 < T) {u : ℝ → Fin 3 → ℝ}
    {q : ℝ → MatrixState} (h : IsAdmissibleIn matrixField matrixDomain controlSimplex (q 0) T u q)
    (hN : (q 0, q T) ∈ matrixEndpoints) :
    IsReinhardtAdmissible T u (fun t ↦ stateG (q t)) (fun t ↦ stateX (q t)) := by
  sorry

/-- **A Reinhardt minimizer is a strong local minimizer of the matrix system**: the pair
`t ↦ (g(t), X(t))` satisfies the boundary condition `matrixEndpoints`, and every competitor
projects to an admissible trajectory of Problem 3.6.2 with the same cost
(`isReinhardtAdmissible_of_mem_matrixEndpoints`, `cost_matrixCost`), so it minimizes the cost
among all of them. -/
theorem IsReinhardtMinimizer.isStrongLocalMinimizer_matrix {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X : ℝ → Mat2} (h : IsReinhardtMinimizer T u g X) :
    IsStrongLocalMinimizer matrixField matrixCost matrixDomain controlSimplex matrixEndpoints T u
      (fun t ↦ toMatrixState (g t) (X t)) := by
  sorry

end SmoothedPolygons
