module

public import SmoothedPolygons.Ch8.SingularLocus
public import SmoothedPolygons.Ch8.EdgeBangBang

/-!
# Non-chattering away from the singular locus (§8.3: Theorems 8.3.1, 8.3.2)

Theorem 8.3.2 (`thm:finite-bang-bang`): an extremal lifted trajectory on a compact interval that
does not meet the singular locus and is edge extremal has a bang-bang control with finitely many
switches. Its proof (TeX 7598–7605) quotes Theorem 8.3.1 in the form "for every
`t₀ ∈ [t₁, t₂]`, there exists a neighborhood of `t₀` on which the control takes values in a single
edge of `U_T` almost everywhere", applies Theorem 8.1.4 on each such neighbourhood, and concludes
by compactness.

## Theorem 8.3.1 as printed is false (gap G2, restated)

Theorem 8.3.1 (`thm:avoid-singular`, TeX 7448–7458) is printed about the *maximizers*: near `t₀`,
`(X(t), Λ_R(t)) ∈ ⋃_{I ⊆ {i, j}} (T*O_J)_I`, i.e. the set of maximizers of the Hamiltonian is
contained in one edge `{i, j}` of `U_T` at every time of a neighbourhood of `t₀`. This is false,
and is not formalized here (the user decides on a restatement):

* At a time `t₀` with `Λ_R(t₀) = 0` the Hamiltonian does not depend on the control, so the set of
  maximizers at `t₀` itself is all of `U_T`. Such `t₀` off `𝒮_sing` occur on edge-extremal
  extremals. Counterexample (normal; checked numerically): `λ_cost = -1`, `X(0) = Φ(0.1 + 0.9i)`
  (not `J`), `Λ_R(0) = 0`, `Λ₁(0) = -(3/2) J + L` with `0 ≠ L ⊥ X(0)`, so
  `W = [L, X(0)] ≠ 0` and `H(0) = 0`; let `e_a`, `e_b` be the vertices maximizing and minimizing
  `⟨W, P_u⟩` on `U_T` (unique for generic `L`); the control `e_b` on `(-ε, 0)` and `e_a` on
  `(0, ε)` with the solutions of the state and costate equations is, for small `ε`, an extremal
  lifted trajectory (`Λ_R(t) = -Wt + O(t²)`, so the control is the unique maximizer for `t ≠ 0`;
  `H ≡ 0` by conservation on each side and continuity at `0`), it is edge extremal (the control
  lies in the edge spanned by `e_a, e_b`, where an abnormal edge costate with `λ₂(0) = 0`,
  `λ₃ = -λ₁(0) y(0)²`, `λ₂'(0) = -2λ₁(0) ≠ 0` switches once at `0`; constant controls on the two
  halves are edge extremal for the other edges), and it does not meet `𝒮_sing` (`X(0) ≠ J`), yet
  every neighbourhood of `0` contains the time `0` at which all of `U_T` maximizes.
* Reading the conclusion off `t₀`, or almost everywhere, does not save it: along the abnormal
  costate of the edge `{u₀ = 0}` (the conormal family containing Remark 8.1.6's) with
  `Λ_R(t₀) = 0` (take `Λ₁(t₀) = [[1, -2x], [0, -1]]`, `X(t₀) = Φ(x + iy)`, `λ_cost = 0`), the
  control `e₂` on `(t₀ - ε, t₀)` and `e₁` on `(t₀, t₀ + ε)` gives an edge-extremal extremal off
  `𝒮_sing` whose maximizers are the edge `{e₂, e₃}` at every `t < t₀` and the vertex `e₁` at every
  `t > t₀` (checked numerically): no single edge contains them on any two-sided neighbourhood.
* The inventory's diagnosis of G2 (two-sided statement, one-sided proof) concerns the maximizers;
  for the *control* the two-sided statement holds, because on each side of `t₀` the control is
  eventually constant at a vertex and any two vertices lie in a common edge.

What the proof of Theorem 8.3.2 uses is the control form, which the book's proof of Theorem 8.3.1
establishes (with the repairs listed in `l3st_exists_controlEdge_ae_nhds`); it is stated here as a
helper, not as Theorem 8.3.1.
-/

@[expose] public section

namespace SmoothedPolygons

open Set MeasureTheory Filter Topology Matrix

/-- **The control form of Theorem 8.3.1**, as the proof of Theorem 8.3.2 quotes it (TeX 7600–7602:
"for every `t₀ ∈ [t₁, t₂]`, there exists a neighborhood of `t₀` on which the control takes values
in a single edge of `U_T` almost everywhere"). Let an extremal lifted trajectory on `[a, b]` be
edge extremal, and let its lift not meet `𝒮_sing` at `t₀ ∈ [a, b]`. Then for some edge
`{u_k = 0}` of `U_T` and some `ε > 0`, the control lies in that edge at almost every time of
`(t₀ - ε, t₀ + ε) ∩ [a, b]`.

This is not Theorem 8.3.1 as printed, which is false (module docstring); it is the statement that
the book's proof of Theorem 8.3.1 proves and that Theorem 8.3.2 uses.

Proof (the book's proof of Theorem 8.3.1, TeX 7469–7586, in the contrapositive, with repairs):
0. Time shift `t₀ = 0`. If `Λ_R(0) ≠ 0`, the maximizers at `0` form a vertex or an edge
   (Lemma 8.2.1, `lemma8_2_1`); by continuity of `(X, Λ_R)` and of the Hamiltonian on the compact
   `U_T`, the maximizers near `0` stay inside that face, and the maximum condition puts the
   control there a.e. So assume `Λ_R(0) = 0` (the book's "by the continuity of the Hamiltonian").
1. `Λ_{1,cost} = Λ₁ - (3/2) λ_cost J` (8.2.1) solves `Λ_{1,cost}' = [Λ_{1,cost}, X] +
   (3/2) λ_cost [J, X]` (Problem 6.7.1), so it is `C¹` with Lipschitz derivative.
2. `Y(t) = -∫₀ᵗ [Λ_{1,cost}, X]`, `Λ = Λ_R - Y`: `Λ' = A(Λ, t) + A(Y, t)` with
   `A(Λ, t) = [P, Λ] - ⟨Λ, P⟩[P, X]` bounded; Gronwall–Bellman (8.3.1) (`eqn:Lambda-bellman`) and
   Corollary A.1.3 two-sided (`l3st_corollaryA_1_3_two_sided`; gap G14).
3. Claim (a): `W = [Λ_{1,cost}(0), X(0)] ≠ 0` gives `Λ_R = -Wt + O(t²)` and the control term
   `t ⟨W, Z_u/⟨X(0), Z_u⟩⟩ + O(t²)`. By Lemma 8.2.1 (with `W ∈ X(0)^⊥ ∖ 0`) its maximizers for
   `t > 0` and for `t < 0` are each a vertex or an edge (if an edge for one sign, the complementary
   vertex for the other). On a side where they form an edge, the control lies in that edge a.e.,
   the trajectory is edge extremal there (Definition 8.1.2), and Theorem 8.1.4 (`theorem8_1_4`)
   makes the control a.e. constant at a vertex near `0` on that side. So on each side the control
   is a.e. constant at a vertex near `0`, and the two vertices lie in a common edge. (The book
   argues this side by side; the observation that two vertices span an edge is the repair.)
4. Claim (b) (a "brief sketch" in the book, gap G3): if `W = 0` but
   `W' = [Λ_{1,cost}'(0), X(0)] ≠ 0`, then `Λ_R = -(t²/2) W' + O(t³)` (step 2 with `‖Y‖ = O(t²)`,
   using the `C^{1,1}` regularity of step 1); the leading term has the same sign on both sides, so
   the maximizers near `0` lie in the vertex or edge maximizing `⟨W', P_u⟩` (Lemma 8.2.1), on both
   sides.
5. Claim (c): `W = W' = 0`. `Λ_{1,cost}(0) ∈ X(0)^⊥` (`H(0) = 0`) and `[Λ_{1,cost}(0), X(0)] = 0`
   give `Λ_{1,cost}(0) = 0`; then `Λ_{1,cost}'(0) = (3/2) λ_cost [J, X(0)] ⊥ X(0)` and `W' = 0`
   give `Λ_{1,cost}'(0) = 0`, so `0 = Λ₁'(0) = (3/2) λ_cost [J, X(0)]`; nontriviality gives
   `λ_cost ≠ 0` (G1), so `X(0) ∈ ℝJ ∩ O_J = {J}`: the lift is in `𝒮_sing` at `0`, a contradiction.
Expected size: 500–800 lines. -/
theorem l3st_exists_controlEdge_ae_nhds {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    {lam : ℝ} (h : IsExtremalOn a b u g X Λ₁ ΛR lam) (hedge : IsEdgeExtremalOn a b u X)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b) (hS : (g t₀, Λ₁ t₀, X t₀, ΛR t₀) ∉ singularLocus) :
    ∃ k : Fin 3, ∃ ε > 0, ∀ᵐ t, t ∈ Ioo (t₀ - ε) (t₀ + ε) → t ∈ Icc a b → u t ∈ controlEdge k := by
  sorry

/-- **Theorem 8.3.2** (`thm:finite-bang-bang`). Consider an extremal lifted trajectory on a compact
interval `[a, b]` that does not meet the singular locus `𝒮_sing`, and assume that the trajectory
`(g, X)` is also edge extremal. Then the control is bang-bang with finitely many switches on
`[a, b]`.

Chapter 1 restates this theorem (TeX 851–856) without the hypothesis "edge extremal"; that
restatement is false for extremal lifted trajectories on an interval (gap G12): by Remark 8.1.6
(`remark8_1_6`, with the sign of G4), every trajectory with an arbitrary measurable control in an
edge of `U_T` lifts to an abnormal extremal lifted trajectory, which does not meet `𝒮_sing`
(`Λ_R ≠ 0`) and need not be bang-bang. The Chapter 8 statement is formalized.

Proof (the book's, TeX 7598–7605): for every `t₀ ∈ [a, b]`, the control form of Theorem 8.3.1
(`l3st_exists_controlEdge_ae_nhds`) gives a neighbourhood of `t₀` on which the control lies in a
single edge a.e.; on it the trajectory is edge extremal (Definition 8.1.2), so Theorem 8.1.4
(`theorem8_1_4`) makes the control bang-bang with finitely many switches there (`u_e = ±½` are
the two vertices of the edge, `edgeParam`); compactness of `[a, b]` (finitely many such
neighbourhoods) gives finitely many switches on `[a, b]`. Expected size: 100–200 lines. -/
theorem theorem8_3_2 {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (h : IsExtremalOn a b u g X Λ₁ ΛR lam) (hedge : IsEdgeExtremalOn a b u X)
    (hS : ∀ t ∈ Icc a b, (g t, Λ₁ t, X t, ΛR t) ∉ singularLocus) :
    IsFiniteBangBang a b u := by
  sorry

end SmoothedPolygons
