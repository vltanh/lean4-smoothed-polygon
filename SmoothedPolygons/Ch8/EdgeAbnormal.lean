module

public import SmoothedPolygons.Ch8.EdgeProblem

/-!
# Abnormal extremals with arbitrary edge control (Remark 8.1.6)

Remark 8.1.6 (`rem:edge-abnormal`, TeX 7035–7070): along every Reinhardt trajectory with control in
the edge `{u₀ = 0}`, an explicit abnormal costate (`λ_cost = 0`) makes every edge control a
maximizer of the Hamiltonian, so the Reinhardt problem has "unnecessarily many extremals"
(TeX 6645–6653); the edge control problem removes them (Theorem 8.1.4), which is why Chapter 8
assumes edge extremality. With the signs as printed the edge is the face of *minimizers* (gap G4),
and the signs of both costates are reversed here.

These abnormal extremals also show that the restatement of Theorem 8.3.2 in Chapter 1 (TeX
851–856), which drops the hypothesis "edge extremal", is false for extremal lifted trajectories on
an interval, the sense of Theorem 8.3.2 (gap G12): they never meet the singular locus (`Λ_R ≠ 0`),
and their control is any measurable edge control (e.g. the midpoint of the edge, which is not
bang-bang). Whether it also fails for extremals with the boundary conditions of Problem 3.6.2 is
not settled here (the costate of the remark is tied to one edge and need not satisfy the
transversality conditions).
-/

@[expose] public section

namespace SmoothedPolygons

open Set MeasureTheory Filter Topology Matrix

/-- The costate `Λ₁ = -[[-x, x²], [-1, x]]` of Remark 8.1.6, with the sign reversed (gap G4), as
a function of `X = Φ(x + iy)` (`x = X₀₀/X₁₀`). -/
noncomputable def abnormalEdgeΛ₁ (X : Mat2) : Mat2 :=
  -!![-(X 0 0 / X 1 0), (X 0 0 / X 1 0) ^ 2; -1, X 0 0 / X 1 0]

/-- The costate `Λ_R = -[[x, y² - x²], [1, -x]]` of Remark 8.1.6, with the sign reversed
(gap G4), as a function of `X = Φ(x + iy)` (`x = X₀₀/X₁₀`, `y = 1/X₁₀`). -/
noncomputable def abnormalEdgeΛR (X : Mat2) : Mat2 :=
  -!![X 0 0 / X 1 0, (1 / X 1 0) ^ 2 - (X 0 0 / X 1 0) ^ 2; 1, -(X 0 0 / X 1 0)]

/-- **Remark 8.1.6** (`rem:edge-abnormal`; abnormal extremals with arbitrary edge control). Let
`(g, X)` be a state trajectory of the Reinhardt problem on `[0, T]` whose control lies in the
edge `{u₀ = 0}` almost everywhere, with any measurable edge control `u_e ∈ [-½, ½]` (so `g` is
given by (8.1.1) and `X = Φ(z)` with `z` given by (8.1.3)). With `λ_cost = 0`,
`Λ_R = -[[x, y² - x²], [1, -x]]` and `Λ₁ = -[[-x, x²], [-1, x]]` solve the costate equations of
§6.5, `Λ_R ⊥ X`, the Hamiltonian vanishes identically on the edge, and every control of the edge
maximizes it: the set of maximizers over `U_T` is the edge `{u₀ = 0}` at every time. So
`(Λ₁, Λ_R, 0)` lifts the trajectory to an abnormal extremal (`IsStateCostateSolution`, no boundary
conditions) whatever the edge control.

Statement correction (gap G4): the book prints `Λ_R = [[x, y² - x²], [1, -x]]`,
`Λ₁ = [[-x, x²], [-1, x]]`. With these signs the costate equations hold and `H ≡ 0` on the edge,
but `H(u) = 6 u₀ y³/D` with `D = -3y⟨X, Z_u⟩ > 0` on the star domain (Lemma 3.3.4), so the edge
is the set of *minimizers* of `H` over `U_T` and the claim "any measurable control maximizes the
Hamiltonian" fails. Both costates are reversed here (the costate equations are linear and
`λ_cost = 0`), which makes `H(u) = -6 u₀ y³/D ≤ 0`, with equality exactly on the edge (checked
with sympy).

Proof (the book: "It can be checked", MCA:4647835): with `x' = y`, `y' = f₂` (`eqn_xy_edge`,
`j = 0`, `edgeFrame 0 = id`) the derivatives of the explicit `Λ₁`, `Λ_R` are rational functions
of `x, y, u_e`; `Λ₁' = [Λ₁, X]` and
`Λ_R' = [P, Λ_R] - ⟨Λ_R, P⟩[P, X] + [-Λ₁, X]` are identities (field_simp; ring), as are
`⟨Λ_R, X⟩ = 0` and `H(u) = -6 u₀ y³/D`; the integral form follows by the fundamental theorem of
calculus. `Λ_R ≠ 0` (its `(1, 0)` entry is `-1`) gives nontriviality. Expected size: 200–350
lines. -/
theorem remark8_1_6 {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2} (h : IsStateTrajectory T u g X)
    (hu : ∀ᵐ t, t ∈ Ioo 0 T → u t 0 = 0) :
    IsStateCostateSolution T u g X (fun t ↦ abnormalEdgeΛ₁ (X t)) (fun t ↦ abnormalEdgeΛR (X t))
        0 ∧
      ∀ t ∈ Icc 0 T,
        (∀ v ∈ controlEdge 0, hamiltonian 0 (abnormalEdgeΛ₁ (X t)) (abnormalEdgeΛR (X t)) (X t) v =
          0) ∧
        hamiltonianArgmax 0 (abnormalEdgeΛ₁ (X t)) (abnormalEdgeΛR (X t)) (X t) =
          controlEdge 0 := by
  sorry

end SmoothedPolygons
