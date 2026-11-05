module

public import SmoothedPolygons.Ch3.ControlSets
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Topology.Defs.Basic

/-!
# The partition of the cotangent space by faces of the control set (§7.3)
-/

@[expose] public section

namespace SmoothedPolygons

/-- **Lemma 7.3.1** (`lem:control-face-lemma`). Let the control set `U` be a compact convex set in
the affine plane `u₀ + u₁ + u₂ = 1`. At each point `(g, X, Λ₁, Λ_R)` of the cotangent space (with
`⟨X, Z_u⟩ ≠ 0` on `U`, as on the state space), the set of controls `u ∈ U` maximizing the
Hamiltonian `H(Λ₁, Λ_R, X; Z_u)` is a face of `U`: a nonempty convex subset `F` such that
`tx + (1-t)y ∈ F` with `x, y ∈ U`, `t ∈ (0, 1)` implies `x, y ∈ F`. -/
theorem lemma7_3_1 (U : Set (Fin 3 → ℝ)) (hU : IsCompact U) (hconv : Convex ℝ U)
    (hne : U.Nonempty) (hplane : ∀ u ∈ U, u 0 + u 1 + u 2 = 1) (lam : ℝ) (Λ₁ ΛR X : Mat2)
    (hden : ∀ u ∈ U, traceForm X (controlMatrix u) ≠ 0) :
    {u ∈ U | ∀ v ∈ U, hamiltonian lam Λ₁ ΛR X v ≤ hamiltonian lam Λ₁ ΛR X u}.Nonempty ∧
      Convex ℝ {u ∈ U | ∀ v ∈ U, hamiltonian lam Λ₁ ΛR X v ≤ hamiltonian lam Λ₁ ΛR X u} ∧
      IsExtreme ℝ U {u ∈ U | ∀ v ∈ U, hamiltonian lam Λ₁ ΛR X v ≤ hamiltonian lam Λ₁ ΛR X u} := by
  sorry

end SmoothedPolygons
