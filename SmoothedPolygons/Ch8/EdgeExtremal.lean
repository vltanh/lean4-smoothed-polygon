module

public import SmoothedPolygons.Ch8.EdgeProblem
public import SmoothedPolygons.Ch6.MatrixExtremal

/-!
# The global minimizer is extremal and edge extremal (Proposition 8.1.3)

Proposition 8.1.3 (`prop:edge-extremal`): the global minimizer of the Reinhardt problem is a
Pontryagin extremal of the Reinhardt control problem, and it is edge extremal (Definition 8.1.2).
The book's proof (TeX 6791–6798) has two sentences:

1. "We have seen that the global minimizer must be extremal": §6.1–§6.2, formalized in Layers 1–2
   as `exists_isPontryaginExtremal_of_isReinhardtMinimizer`.
2. The principle of optimality: on a subinterval where the control lies in an edge of `U_T`, the
   minimizer minimizes the cost among trajectories with the same endpoint conditions whose control
   lies in that edge; hence it is extremal for the edge control problem.

The second sentence needs (inventory, gap G10): the maximum principle for the edge problem (an
open subset of `ℝ³`, fixed endpoints, free terminal time, integral cost), which is
`External.pontryagin_maximum_principle`; and the principle of optimality made precise. A
competitor of the edge problem with the same endpoints is spliced into the minimizer: its
Reinhardt trajectory is rebuilt from `(s, x, y)` by (8.1.1) (`eqn_g_edge`), so it ends at the
minimizer's `g(d)` and `X(d)`; the rest of the minimizer is shifted in time (free terminal time),
and the cost changes by `3/2` times the change of the edge cost (`edgeCost_identity`). The edge
problem's state space `y > 0`, `|x| < 1/√3` is larger than the star domain, so a competitor could
leave the Reinhardt state space: only competitors uniformly close to the minimizer's edge arc are
spliced (strong local minimality, which is all the maximum principle needs). This is
`l3st_isStrongLocalMinimizer_edgeState`.
-/

@[expose] public section

namespace SmoothedPolygons

open Set MeasureTheory Filter Topology Matrix

/-- The edge control system is `C¹` on its state space in the sense of the maximum principle
(`ControlSystem.IsC1On`, conditions (10.2)–(10.4) of Agrachev–Sachkov): on
`{y > 0, |x| < 1/√3} × [-½, ½]` we have `|2√3 x u_e| < 1`, so the denominator `-1 + 2√3 x u_e`
of `f₂` is negative and `edgeField` is a rational function with nonvanishing denominators there.
Expected size: 60–120 lines. -/
theorem l3st_isC1On_edgeField : ControlSystem.IsC1On edgeField edgeDomain edgeControlSet := by
  sorry

/-- The edge cost `x²/y` is `C¹` on the state space of the edge problem. Expected size: 20–40
lines. -/
theorem l3st_isC1On_edgeCost : ControlSystem.IsC1On edgeCost edgeDomain edgeControlSet := by
  sorry

/-- **The principle of optimality for an edge arc** (proof of Proposition 8.1.3, TeX 6793–6797,
with gap G10 repaired). Let `(T, u, g, X)` be a global minimizer of the Reinhardt problem and let
`u_j = 0` almost everywhere on `[c, d] ⊆ [0, T]`. Then the edge arc `(u_e, (x, y, s))` of the
minimizer on `[c, d]` (`edgeParam j u`, `edgeState j X c`) is a strong local minimizer of the
`j`-th edge control problem with fixed endpoints (8.1.4) and free terminal time.

Proof: let `(u_e', q')` be an admissible pair of the edge problem on `[0, T']` with the same
endpoints, `|T' - (d - c)| < ε` and `‖q'(σT') - q(σ(d - c))‖ < ε`. For `ε` small, `(x', y')`
stays in a compact neighbourhood of the minimizer's arc inside the star domain (`eqn_xy_edge`:
the arc is in `𝔥*`, which is open). Splice: on `[0, c]` the minimizer; on `[c, c + T']` the
trajectory `X' = R⁻ʲ Φ(x', y') Rʲ`, `g' = R⁻ʲ (g̃(c) h(q'(0))⁻¹ h(q'(t - c))) Rʲ` (8.1.1), with
the control `R⁻ʲ`-rotated from `(0, ½ + u_e', ½ - u_e')`, which solves the Reinhardt state
equations (`eqn_xy_edge`, `eqn_g_edge` read backwards: `h⁻¹h' = Φ`); on
`[c + T', T + T' - (d - c)]` the minimizer shifted by `T' - (d - c)`. Equal endpoints of `(x, y, s)`
give `X'(c + T') = X(d)` and `g'(c + T') = g(d)` by (8.1.1), so the splice is admissible for
Problem 3.6.2 (the boundary conditions at `0` and at the terminal time are the minimizer's;
Carathéodory solutions glue, as `ct_pw_isIntegralCurve` in `Ch6/PeriodicExtension`). By
`edgeCost_identity` its cost minus the minimizer's is `(3/2)(cost_edge(u_e', q') -
cost_edge(u_e, q))`, the boundary terms `(s + x)|` being equal; minimality gives the inequality.
Expected size: 400–700 lines. -/
theorem l3st_isStrongLocalMinimizer_edgeState {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (hmin : IsReinhardtMinimizer T u g X) {j : Fin 3} {c d : ℝ} (hc : 0 ≤ c) (hcd : c < d)
    (hd : d ≤ T) (hu : ∀ᵐ t, t ∈ Ioo c d → u t j = 0) :
    Pontryagin.IsStrongLocalMinimizer edgeField edgeCost edgeDomain edgeControlSet
      {w | w = (edgeState j X c 0, edgeState j X c (d - c))} (d - c)
      (fun t ↦ edgeParam j (u (c + t))) (edgeState j X c) := by
  sorry

/-- **Proposition 8.1.3** (`prop:edge-extremal`). The global minimizer of the Reinhardt problem
is an extremal of the Reinhardt control problem, and it is also edge extremal (Definition 8.1.2)
on its whole domain `[0, T]`.

"The global solution" presupposes existence and uniqueness; the statement is for every global
minimizer (`IsReinhardtMinimizer`), and one exists (`exists_isReinhardtMinimizer`).

Proof (the book's, TeX 6791–6798, with gap G10 repaired):
1. Extremal: `exists_isPontryaginExtremal_of_isReinhardtMinimizer` ("We have seen that the global
   minimizer must be extremal", §6.1–§6.2).
2. Edge extremal: for `j`, `[c, d]` with `u_j = 0` a.e., the edge arc is a strong local minimizer
   of the edge problem (`l3st_isStrongLocalMinimizer_edgeState`, the principle of optimality);
   the maximum principle `External.pontryagin_maximum_principle` (with `l3st_isC1On_edgeField`,
   `l3st_isC1On_edgeCost`, the compact control set `[-½, ½]`, and the boundary map
   `G(q₀, q₁) = (q₀ - q(0), q₁ - q(d - c))`, a submersion whose zero set is the fixed endpoints)
   gives `ν ≤ 0` and `p` with the conclusions of `IsEdgeProblemExtremal`; admissibility is
   `eqn_xy_edge`.
Expected size: 80–150 lines. -/
theorem proposition8_1_3 {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (hmin : IsReinhardtMinimizer T u g X) :
    (∃ (Λ₁ ΛR : ℝ → Mat2) (lam : ℝ), IsPontryaginExtremal T u g X Λ₁ ΛR lam) ∧
      IsEdgeExtremalOn 0 T u X := by
  sorry

end SmoothedPolygons
