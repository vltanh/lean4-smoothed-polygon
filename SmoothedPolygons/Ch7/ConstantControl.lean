module

public import SmoothedPolygons.Ch6.Hamiltonian
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Algebra.Polynomial.Roots

/-!
# Solutions for constant control (§7.1, §7.2)

For a constant control `u`, `⟨X, Z_u⟩` is a constant of motion (Lemma 7.1.1), the speed of `X` is
constant (Lemma 7.1.2), the state equations are solved by matrix exponentials
(`eqn:const-control-g`, `eqn:const-control-z-X`), `P₀` and `X₀ + P₀` have the same characteristic
polynomial (Lemma 7.1.3), and for a vertex control the trajectories in the star domain are arcs of
generalized circles (Lemma 7.2.1).
-/

@[expose] public section

namespace SmoothedPolygons

open Matrix

/-- **Lemma 7.1.1** (`cor:X-det-const`). For a fixed control matrix `Z_u`, `⟨X, Z_u⟩` is a constant
of motion along `X' = [Z_u, X]/⟨Z_u, X⟩`. -/
theorem lemma7_1_1 (u : Fin 3 → ℝ) (X : ℝ → Mat2) (a b : ℝ)
    (hX : ∀ t ∈ Set.Icc a b, HasDerivWithinAtEntrywise X
      (controlP u (X t) * X t - X t * controlP u (X t)) (Set.Icc a b) t) :
    ∀ t ∈ Set.Icc a b, traceForm (X t) (controlMatrix u) = traceForm (X a) (controlMatrix u) := by
  sorry

/-- **Lemma 7.1.2** (`lem:Riemannian-speed`). For a constant control `u ∈ U_T`, the speed
`⟨X', X'⟩^{1/2}` of `X` is constant, and the trajectory `z = x + iy` with `X = Φ(z)` has constant
speed `(x'² + y'²)^{1/2}/y` for the invariant Riemannian metric of the upper half-plane. -/
theorem lemma7_1_2 (u : Fin 3 → ℝ) (hu : u ∈ controlSimplex) (X : ℝ → Mat2) (a b : ℝ)
    (hstar : ∀ t ∈ Set.Icc a b, IsStarState (X t))
    (hX : ∀ t ∈ Set.Icc a b, HasDerivWithinAtEntrywise X
      (controlP u (X t) * X t - X t * controlP u (X t)) (Set.Icc a b) t) :
    (∀ t ∈ Set.Icc a b,
      traceForm (controlP u (X t) * X t - X t * controlP u (X t))
          (controlP u (X t) * X t - X t * controlP u (X t)) =
        traceForm (controlP u (X a) * X a - X a * controlP u (X a))
          (controlP u (X a) * X a - X a * controlP u (X a))) ∧
      ∀ x y x' y' : ℝ → ℝ, (∀ t ∈ Set.Icc a b, X t = Φ (x t) (y t) ∧ 0 < y t ∧
          HasDerivWithinAt x (x' t) (Set.Icc a b) t ∧ HasDerivWithinAt y (y' t) (Set.Icc a b) t) →
        ∀ t ∈ Set.Icc a b, (x' t ^ 2 + y' t ^ 2) / y t ^ 2 = (x' a ^ 2 + y' a ^ 2) / y a ^ 2 := by
  sorry

/-- The general solution `g(t) = exp(t(X₀ + P₀)) exp(-tP₀)` of the state equation for `g` with
constant control (`eqn:const-control-g`), `P₀ = Z_u/⟨Z_u, X₀⟩`. -/
noncomputable def constControlG (X₀ P₀ : Mat2) (t : ℝ) : Mat2 :=
  NormedSpace.exp (t • (X₀ + P₀)) * NormedSpace.exp (-t • P₀)

/-- The general solution `X(t) = exp(tP₀) X₀ exp(-tP₀) = Ad_{exp(tP₀)} X₀` of the state equation
for `X` with constant control (`eqn:const-control-z-X`). -/
noncomputable def constControlX (X₀ P₀ : Mat2) (t : ℝ) : Mat2 :=
  NormedSpace.exp (t • P₀) * X₀ * NormedSpace.exp (-t • P₀)

/-- The general solutions for constant control (`eqn:const-control-g`, `eqn:const-control-z-X`):
with `P₀ = Z_u/⟨Z_u, X₀⟩`, `g(t) = exp(t(X₀ + P₀)) exp(-tP₀)` and `X(t) = exp(tP₀) X₀ exp(-tP₀)`
solve `g' = gX`, `X' = [Z_u, X]/⟨Z_u, X⟩` with `g(0) = I₂`, `X(0) = X₀`. -/
theorem constControl_solution (u : Fin 3 → ℝ) (X₀ : Mat2) (hX₀ : X₀.trace = 0)
    (hden : traceForm (controlMatrix u) X₀ ≠ 0) (t : ℝ) :
    HasDerivAtEntrywise (constControlG X₀ (controlP u X₀))
        (constControlG X₀ (controlP u X₀) t * constControlX X₀ (controlP u X₀) t) t ∧
      HasDerivAtEntrywise (constControlX X₀ (controlP u X₀))
        (controlP u (constControlX X₀ (controlP u X₀) t) * constControlX X₀ (controlP u X₀) t -
          constControlX X₀ (controlP u X₀) t * controlP u (constControlX X₀ (controlP u X₀) t)) t ∧
      constControlG X₀ (controlP u X₀) 0 = 1 ∧ constControlX X₀ (controlP u X₀) 0 = X₀ := by
  sorry

/-- **Lemma 7.1.3** (unlabelled in the book; label `lem:P0-charpoly` here). With `det X₀ = 1` and
`P₀ = Z_u/⟨Z_u, X₀⟩`, the matrices `P₀` and `X₀ + P₀` have the same characteristic polynomial. If
`det Z_u < 0`, the eigenvalues are real: `±√(-det Z_u)/⟨X₀, Z_u⟩`. -/
theorem lemma7_1_3 (X₀ Z : Mat2) (hX : X₀.trace = 0) (hZ : Z.trace = 0) (hdet : X₀.det = 1)
    (hXZ : traceForm X₀ Z ≠ 0) :
    ((traceForm Z X₀)⁻¹ • Z).charpoly = (X₀ + (traceForm Z X₀)⁻¹ • Z).charpoly ∧
      (Z.det < 0 → ((traceForm Z X₀)⁻¹ • Z).charpoly.roots =
        {√(-Z.det) / traceForm X₀ Z, -(√(-Z.det) / traceForm X₀ Z)}) := by
  sorry

/-- **Lemma 7.2.1** (`lem:const-control-trajectories`). If the control is constant at a vertex of
`U_T`, then the trajectories `z = x + iy` in the star domain are arcs of generalized circles
(`A(x² + y²) + Bx + Cy + D = 0` with `(A, B, C) ≠ 0`). If the control is `(0, 0, 1)` or
`(0, 1, 0)`, each trajectory moves along a Euclidean straight line (`A = 0`). -/
theorem lemma7_2_1 (i : Fin 3) (X : ℝ → Mat2) (x y : ℝ → ℝ) (a b : ℝ)
    (hX : ∀ t ∈ Set.Icc a b, HasDerivWithinAtEntrywise X
      (controlP (vertex i) (X t) * X t - X t * controlP (vertex i) (X t)) (Set.Icc a b) t)
    (hxy : ∀ t ∈ Set.Icc a b, X t = Φ (x t) (y t) ∧ (x t, y t) ∈ starDomain) :
    ∃ A B C D : ℝ, (A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0) ∧ (i ≠ 0 → A = 0) ∧
      ∀ t ∈ Set.Icc a b, A * (x t ^ 2 + y t ^ 2) + B * x t + C * y t + D = 0 := by
  sorry

end SmoothedPolygons
