module

public import SmoothedPolygons.Ch8.EdgeLandau

/-!
# Extremals of the edge control problem are bang-bang (Theorem 8.1.4)

Theorem 8.1.4 (`thm:edge`): every extremal lifted trajectory of the edge control problem on a
closed interval, normal or abnormal, has a bang-bang control `u_e = ±½` with finitely many
switches. The switching function is `λ₂` (the costate dual to `y`), and the proof shows that its
zeros are isolated: a zero with `λ₂' ≠ 0` is transversal; at a zero with `λ₂' = 0` the costate is
given by (8.1.8) (`eqn_edge_zero`: the extremal is normal there and `x = ±√(-λ₃/λ_cost)`, which
happens at most twice since `x' = y > 0`), and such a zero is isolated by Lemma 8.1.5
(`lem:lambda2-Landau`: `λ₂(t) = C tⁿ + O(tⁿ⁺¹)` with `C ≠ 0`, by Gronwall, Corollary A.1.3).

Lemma 8.1.5 is in `SmoothedPolygons/Ch8/EdgeLandau.lean`.
-/

@[expose] public section

namespace SmoothedPolygons

open Set MeasureTheory Filter Topology Asymptotics

/-- **The maximization rule of the edge problem** (proof of Theorem 8.1.4, TeX 6840–6845): the
only term of the Hamiltonian (8.1.6) depending on the control is `λ₂ f₂`, and `f₂` is strictly
decreasing in `u_e` (`∂f₂/∂u_e = -2√3 y²/(-1 + 2√3 x u_e)² < 0` on the state space), so at
almost every time `λ₂ > 0` forces `u_e = -½` and `λ₂ < 0` forces `u_e = ½`: `λ₂` is the
switching function. Proof: `Pontryagin.IsMaximal` with `eqn_edge_ham`, and the strict
monotonicity of `f₂` in `u_e`. Expected size: 40–80 lines. -/
theorem l3st_edge_max_rule {T : ℝ} {ue : ℝ → ℝ} {q : ℝ → Fin 3 → ℝ} {ν : ℝ}
    {p : ℝ → StrongDual ℝ (Fin 3 → ℝ)} (h : IsEdgeProblemExtremal T ue q ν p) :
    ∀ᵐ t, t ∈ Icc 0 T →
      (0 < edgeCostate (p t) 1 → ue t = -(1 / 2)) ∧ (edgeCostate (p t) 1 < 0 → ue t = 1 / 2) := by
  sorry

/-- **Equation (8.1.8)** (`eqn:edge-zero`, the claim in the proof of Theorem 8.1.4, TeX
6854–6874). At a time `t₂` where the switching function `λ₂` and its derivative vanish, the
costate is `λ₃ = -x(t₂)² λ_cost`, `λ₁(t₂) = 0`, and `λ_cost ≠ 0` (the extremal is normal there).
So `-λ₃/λ_cost ≥ 0` and `x(t₂) = ±√(-λ₃/λ_cost)`.

The derivative of `λ₂` at its zero exists: the right-hand side of (8.1.7) for `λ₂` is continuous
at a zero of `λ₂` (its control-dependent term is a bounded multiple of `λ₂`, TeX 6846–6852;
the hypothesis is stated with the derivative within `[0, T]`, which covers the endpoints).

Proof (the book's): `H = 0` at `t₂` (from `H = 0` almost everywhere, by continuity, since at
`λ₂ = 0` the Hamiltonian does not depend on the control) and `λ₂' = -∂H/∂y = 0` at `t₂`
(`eqn_costate_edge`) form the linear system `λ₁ y + λ₃/y + λ_cost x²/y = 0`,
`λ₃/y² - λ₁ + λ_cost x²/y² = 0` in `(λ₁, λ₃)`, of determinant `2/y ≠ 0`, whose solution is the
one displayed. If `λ_cost = 0`, then `(λ_cost, λ₁, λ₂, λ₃) = 0` at `t₂`, against the
nontriviality of the maximum principle. Expected size: 100–200 lines. -/
theorem eqn_edge_zero {T : ℝ} {ue : ℝ → ℝ} {q : ℝ → Fin 3 → ℝ} {ν : ℝ}
    {p : ℝ → StrongDual ℝ (Fin 3 → ℝ)} (h : IsEdgeProblemExtremal T ue q ν p) {t₂ : ℝ}
    (ht₂ : t₂ ∈ Icc 0 T) (hz : edgeCostate (p t₂) 1 = 0)
    (hd : HasDerivWithinAt (fun t ↦ edgeCostate (p t) 1) 0 (Icc 0 T) t₂) :
    edgeCostate (p t₂) 2 = -(q t₂ 0) ^ 2 * ν ∧ edgeCostate (p t₂) 0 = 0 ∧ ν ≠ 0 := by
  sorry

/-- **Theorem 8.1.4** (`thm:edge`). Consider an extremal lifted trajectory of the edge control
system on a closed interval `[0, T]` (normal or abnormal). Then the control `u_e` is bang-bang
with finitely many switches: it is equal almost everywhere to a piecewise constant function with
values `±½` and finitely many switches on `[0, T]`.

(The book says "the optimal control function"; the statement and the proof concern any extremal,
gap G13.)

Proof (the book's, TeX 6820–6894):
1. The costate equations (8.1.7) (`eqn_costate_edge`); `λ₃` is constant.
2. `λ₂` is the switching function (`l3st_edge_max_rule`).
3. `λ₂` is differentiable at each of its zeros, with derivative the right-hand side of (8.1.7) at
   that time (its control-dependent term `λ₂ · (bounded)` tends to `0` with `λ₂`; the book's
   "`λ₂'` is continuous", TeX 6846–6852).
4. At a zero with `λ₂' = 0`, (8.1.8) holds (`eqn_edge_zero`): `λ_cost ≠ 0` and
   `x = ±√(-λ₃/λ_cost)`; since `x' = y > 0`, `x` is strictly increasing, so there are at most two
   such zeros. Every other zero is transversal (`λ₂' ≠ 0`), hence isolated.
5. After the time translation `t₂ = 0` and the normalization `λ_cost = -1` (the costate equations
   are linear in `(λ_cost, λ)`), Lemma 8.1.5 (`lemma8_1_5`) shows that the zeros of the second
   kind are isolated too (at an endpoint of `[0, T]`, extend the state and costate beyond it with
   any control, e.g. by `ControlSystem.exists_isSolution`, since the lemma holds for every
   measurable control).
6. `λ₂` does not vanish on any interval (that would make every point a zero of the second kind).
   Isolated zeros of the continuous `λ₂` on the compact `[0, T]` are finitely many; between them
   `λ₂` has a constant sign, and the control is a.e. the constant `∓½` there (step 2). The book's
   "adjusting `u_e` on a set of measure zero" is the almost-everywhere formulation.
Expected size: 300–500 lines. -/
theorem theorem8_1_4 {T : ℝ} {ue : ℝ → ℝ} {q : ℝ → Fin 3 → ℝ} {ν : ℝ}
    {p : ℝ → StrongDual ℝ (Fin 3 → ℝ)} (h : IsEdgeProblemExtremal T ue q ν p) :
    ∃ S : Finset ℝ, ∀ t ∈ Ioo 0 T, t ∉ S → ∃ c ∈ ({-(1 / 2), 1 / 2} : Set ℝ), ∃ ε > 0,
      ∀ᵐ τ, τ ∈ Ioo (t - ε) (t + ε) → ue τ = c := by
  sorry

end SmoothedPolygons
