module

public import SmoothedPolygons.Ch8.SingularLocus
public import SmoothedPolygons.Ch8.EdgeBangBang

/-!
# Non-chattering away from the singular locus (§8.3: Theorems 8.3.1, 8.3.2)

* `theorem8_3_1`: Theorem 8.3.1 (`thm:avoid-singular`) in the one-sided form below. Near a time
  `t₀` at which the lift avoids `𝒮_sing`, the maximizers of the Hamiltonian lie in one edge of
  `U_T` at every time just before `t₀`, and in one (possibly different) edge at every time just
  after `t₀`.
* `IsExtremalOn.exists_ae_mem_controlEdge_of_isEdgeExtremalOn`: the control form of Theorem 8.3.1
  that the proof of Theorem 8.3.2 quotes, which is two-sided: the control lies in a single edge
  almost everywhere on a neighbourhood of `t₀` (from `theorem8_3_1`, edge extremality and
  Theorem 8.1.4).
* `theorem8_3_2`: Theorem 8.3.2 (`thm:finite-bang-bang`). An extremal lifted trajectory on a
  compact interval that does not meet the singular locus and is edge extremal has a bang-bang
  control with finitely many switches. Its proof (TeX 7598–7605) quotes Theorem 8.3.1 in the form
  "for every `t₀ ∈ [t₁, t₂]`, there exists a neighborhood of `t₀` on which the control takes
  values in a single edge of `U_T` almost everywhere", applies Theorem 8.1.4 on each such
  neighbourhood, and concludes by compactness.

## Theorem 8.3.1 as printed is false (gap G2)

Theorem 8.3.1 (TeX 7448–7458) is printed about the *maximizers*: there are an edge `{i, j}` and a
neighbourhood of `t₀` in `[t₁, t₂]` on which `(X(t), Λ_R(t)) ∈ ⋃_{I ⊆ {i, j}} (T*O_J)_I`, i.e. the
set of maximizers of the Hamiltonian is contained in the edge `{i, j}` of `U_T` at every time of
the neighbourhood. This is false:

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

## The restatement (the user's decision)

Theorem 8.3.1 is formalized in the *one-sided maximizer form* (`theorem8_3_1`): under the book's
hypotheses there are `ε > 0` and edges `k₋`, `k₊` (`kₗ`, `kᵣ` in Lean) such that the maximizers
lie in the edge `k₋` at every time of `(t₀ - ε, t₀) ∩ [a, b]` and in the edge `k₊` at every time
of `(t₀, t₀ + ε) ∩ [a, b]`. The time `t₀` itself is excluded, and the two edges may differ; both
counterexamples satisfy this form (the first with the vertices `e_b` before and `e_a` after `0`,
the second with the edge `{e₂, e₃}` before and the vertex `e₁` after `t₀`). This is the
inventory's repair of G2 ("restate it with one-sided neighbourhoods; Thm 8.3.2 survives"). The
book's hypotheses are kept, edge extremality included, although the proof of the maximizer form
does not use it (the book uses it, through Theorem 8.1.4, only to pass to the control).

The control form that the proof of Theorem 8.3.2 quotes is two-sided and true: on each side of
`t₀` the control lies in one edge almost everywhere (maximum condition), so by edge extremality
and Theorem 8.1.4 it is eventually constant at a vertex, and any two vertices lie in a common
edge. It is the corollary `IsExtremalOn.exists_ae_mem_controlEdge_of_isEdgeExtremalOn`.
-/

@[expose] public section

namespace SmoothedPolygons

open Set MeasureTheory Filter Topology Matrix

/-- **Theorem 8.3.1** (`thm:avoid-singular`), in the one-sided maximizer form. Consider an
extremal lifted trajectory on `[a, b]` and `t₀ ∈ [a, b]` such that the lifted trajectory does not
meet the singular locus at time `t₀`, and assume that the trajectory is also edge extremal
(Definition 8.1.2). Then there are `ε > 0` and edges `k₋ = kₗ`, `k₊ = kᵣ` of `U_T` such that at
every time `t ∈ [a, b]` with `t₀ - ε < t < t₀` the set of maximizers of the Hamiltonian
`hamiltonianArgmax λ_cost Λ₁(t) Λ_R(t) X(t)` is contained in the edge `{u_{kₗ} = 0}`, and at every
time `t ∈ [a, b]` with `t₀ < t < t₀ + ε` it is contained in the edge `{u_{kᵣ} = 0}`.

**Restatement.** The book prints (TeX 7448–7458): "there exists an edge `{i, j}` and a
neighborhood of `t₀` in `[t₁, t₂]` on which `(X(t), Λ_R(t)) ∈ ⋃_{I ⊆ {i,j}} (T*O_J)_I`", i.e. the
maximizers lie in one edge at every time of a two-sided neighbourhood of `t₀`. That is false
(gap G2; module docstring): at a time `t₀` off `𝒮_sing` with `Λ_R(t₀) = 0` all of `U_T` maximizes,
which happens on edge-extremal extremals (normal counterexample `λ_cost = -1`,
`X(0) = Φ(0.1 + 0.9i)`, `Λ_R(0) = 0`, `Λ₁(0) = -(3/2) J + L`, `0 ≠ L ⊥ X(0)`), and the maximizers
can lie in different edges before and after `t₀` (abnormal counterexample on the edge
`{u₀ = 0}`: the edge `{e₂, e₃}` before, the vertex `e₁` after). The user decided to formalize the
one-sided maximizer form stated here, keeping the book's hypotheses; edge extremality is not used
by the proof. The control form used by Theorem 8.3.2 is the corollary
`IsExtremalOn.exists_ae_mem_controlEdge_of_isEdgeExtremalOn`.

Proof (the book's proof, TeX 7469–7586, run directly instead of in the contrapositive):
0. If `Λ_R(t₀) ≠ 0`, the maximizers at `t₀` form a vertex or an edge `F` (Lemma 8.2.1,
   `lemma8_2_1`, at the star state `X(t₀)`, Lemma 3.3.4). The values of the Hamiltonian at the
   three vertices are continuous in `t` (`l3st_continuousOn_lift`, `⟨X, Z_{e_i}⟩ ≠ 0`); a vertex
   outside `F` stays strictly below the maximum near `t₀`. The maximizers at each time form a face
   of `U_T` (Lemma 7.3.1, `lemma7_3_1`) spanned by maximizing vertices, so they lie in `F`; take
   `kₗ = kᵣ` an edge containing `F`. (The book's "by the continuity of the Hamiltonian, … By
   Lemma 8.2.1, `Λ_R(0) = 0`".) So assume `Λ_R(t₀) = 0`; then `H(t₀) = 0` (by continuity, as in
   Lemma 8.2.2) puts `Λ_{1,cost}(t₀)` in `X(t₀)^⊥`.
1. `Λ_{1,cost} = Λ₁ - (3/2) λ_cost J` (8.2.1) solves `Λ_{1,cost}' = [Λ_{1,cost}, X] +
   (3/2) λ_cost [J, X]` (Problem 6.7.1), with a continuous right-hand side, so it is `C¹`.
2. `Y(t) = -∫_{t₀}^t [Λ_{1,cost}, X]`, `Λ = Λ_R - Y`: `Λ' = A(Λ, t) + A(Y, t)` with
   `A(Λ, t) = [P, Λ] - ⟨Λ, P⟩[P, X]` bounded near `t₀` (`P = Z_u/⟨Z_u, X⟩`, Lemma 3.3.4), so
   `‖Λ‖ ≤ C₀ |∫ ‖Y‖| + C₀ |∫ ‖Λ‖|` (8.3.1, `eqn:Lambda-bellman`), and Corollary A.1.3 two-sided
   (`l3st_corollaryA_1_3_two_sided`, gap G14; one-sided `corollaryA_1_3` at an endpoint of
   `[a, b]`) gives `‖Λ‖ = O(|t - t₀|^{n+1})` when `‖Y‖ = O(|t - t₀|ⁿ)`.
3. Claim (a): `W = [Λ_{1,cost}(t₀), X(t₀)] ≠ 0`. Then `Λ_R = -W (t - t₀) + O((t - t₀)²)`, and the
   control-dependent term of the Hamiltonian at the vertex `e_i` is
   `(t - t₀) c_i + O((t - t₀)²)` with `c_i = ⟨W, Z_{e_i}⟩/⟨X(t₀), Z_{e_i}⟩`. Since
   `W ∈ X(t₀)^⊥ ∖ 0`, the `c_i` are not all equal (Lemma 8.2.1), so for `t > t₀` near `t₀` the
   maximizers lie in the face spanned by the vertices maximizing `c_i`, and for `t < t₀` in the
   face spanned by the vertices minimizing `c_i` (a vertex or an edge each; the book: "if the set
   of maximizers is an edge when `t` has one sign, then the maximizer is the complementary vertex
   … when `t` has the other sign"). The book goes on through Theorem 8.1.4 to the control; the
   maximizer form stops here, and that step is the corollary.
4. Claim (b) (a "brief sketch" in the book, gap G3): `W = 0`, so `Λ_{1,cost}(t₀) = 0` (it lies in
   `X(t₀)^⊥` and in the centralizer `ℝ X(t₀)`, and `⟨X, X⟩ = -2`), and
   `W' = [Λ_{1,cost}'(t₀), X(t₀)] ≠ 0`. Then `[Λ_{1,cost}, X] = (t - t₀) W' + o(t - t₀)`,
   `Y = -((t - t₀)²/2) W' + o((t - t₀)²)`, step 2 gives `‖Λ‖ = O(|t - t₀|³)`, so
   `Λ_R = -((t - t₀)²/2) W' + o((t - t₀)²)`: the control term at `e_i` is
   `((t - t₀)²/2) c'_i + o((t - t₀)²)` with `c'_i = ⟨W', Z_{e_i}⟩/⟨X(t₀), Z_{e_i}⟩`, of the same
   sign on both sides. The `c'_i` are not all equal (Lemma 8.2.1, `W' ∈ X(t₀)^⊥ ∖ 0`), and on both
   sides the maximizers lie in the face spanned by the vertices maximizing `c'_i`: `kₗ = kᵣ`. (The
   book: "`Λ_R` has an isolated zero at `t = 0`".)
5. Claim (c): `W = W' = 0`. Then `Λ_{1,cost}(t₀) = 0` and
   `Λ_{1,cost}'(t₀) = (3/2) λ_cost [J, X(t₀)] ∈ X(t₀)^⊥ ∩ ℝ X(t₀) = 0`; nontriviality of
   `(λ_cost, Λ₁, Λ_R)` at `t₀` (gap G1) gives `λ_cost ≠ 0`, so `[J, X(t₀)] = 0` and
   `X(t₀) ∈ ℝ J ∩ O_J = {J}`: the lift is in `𝒮_sing` at `t₀` (`l3st_mem_singularLocus_iff`),
   against the hypothesis.
Expected size: 500–800 lines. -/
theorem theorem8_3_1 {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (h : IsExtremalOn a b u g X Λ₁ ΛR lam) (hedge : IsEdgeExtremalOn a b u X)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b) (hS : (g t₀, Λ₁ t₀, X t₀, ΛR t₀) ∉ singularLocus) :
    ∃ ε > 0, ∃ kₗ kᵣ : Fin 3,
      (∀ t ∈ Icc a b, t₀ - ε < t → t < t₀ →
        hamiltonianArgmax lam (Λ₁ t) (ΛR t) (X t) ⊆ controlEdge kₗ) ∧
      ∀ t ∈ Icc a b, t₀ < t → t < t₀ + ε →
        hamiltonianArgmax lam (Λ₁ t) (ΛR t) (X t) ⊆ controlEdge kᵣ := by
  sorry

/-- **The control form of Theorem 8.3.1**, as the proof of Theorem 8.3.2 quotes it (TeX 7600–7602:
"for every `t₀ ∈ [t₁, t₂]`, there exists a neighborhood of `t₀` on which the control takes values
in a single edge of `U_T` almost everywhere"). Let an extremal lifted trajectory on `[a, b]` be
edge extremal, and let its lift not meet `𝒮_sing` at `t₀ ∈ [a, b]`. Then for some edge
`{u_k = 0}` of `U_T` and some `ε > 0`, the control lies in that edge at almost every time of
`(t₀ - ε, t₀ + ε) ∩ [a, b]`.

Proof (a corollary of `theorem8_3_1`, with the step of the book's claim (a) that passes to the
control: "by the results of Theorem 8.1.4, the control function has finite bang-bang switching
near `t = 0`", TeX 7558–7560):
1. `theorem8_3_1` gives `ε`, `kₗ`, `kᵣ`. The maximum condition (`IsExtremalOn`: `u(t)` maximizes
   the Hamiltonian for almost every `t`) puts `u(t)` in the edge `kₗ` for almost every
   `t ∈ (t₀ - ε, t₀) ∩ [a, b]`, and in the edge `kᵣ` for almost every `t ∈ (t₀, t₀ + ε) ∩ [a, b]`.
2. Left side (if `a < t₀`): with `c = max a (t₀ - ε/2)`, `u_{kₗ} = 0` almost everywhere on
   `(c, t₀)`, so edge extremality (Definition 8.1.2, `IsEdgeExtremalOn`) on `[c, t₀]` gives an
   extremal of the edge control problem with control `edgeParam kₗ u`, and Theorem 8.1.4
   (`theorem8_1_4`) makes it almost everywhere locally constant `±½` off a finite set. Between the
   last point of that set and `t₀` it is almost everywhere one constant (the interval is
   connected), so `u` is almost everywhere one vertex there (in the edge `kₗ`, `edgeParam = ±½`
   means `vertex (kₗ + 1)` or `vertex (kₗ + 2)`). The right side likewise.
3. Any two vertices lie in a common edge (`vertex i`, `vertex j` lie in `controlEdge k` for
   `k ∉ {i, j}`); shrink `ε`. The time `t₀` is a null set.
(If `kₗ = kᵣ`, step 1 already gives the conclusion.) Expected size: 120–250 lines. -/
theorem IsExtremalOn.exists_ae_mem_controlEdge_of_isEdgeExtremalOn {a b : ℝ}
    {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ} (h : IsExtremalOn a b u g X Λ₁ ΛR lam)
    (hedge : IsEdgeExtremalOn a b u X) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b)
    (hS : (g t₀, Λ₁ t₀, X t₀, ΛR t₀) ∉ singularLocus) :
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
(`IsExtremalOn.exists_ae_mem_controlEdge_of_isEdgeExtremalOn`, the corollary of `theorem8_3_1`)
gives a neighbourhood of `t₀` on which the control lies in a single edge a.e.; on it the
trajectory is edge extremal (Definition 8.1.2), so Theorem 8.1.4 (`theorem8_1_4`) makes the
control bang-bang with finitely many switches there (`u_e = ±½` are the two vertices of the edge,
`edgeParam`); compactness of `[a, b]` (finitely many such neighbourhoods) gives finitely many
switches on `[a, b]`. Expected size: 100–200 lines. -/
theorem theorem8_3_2 {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (h : IsExtremalOn a b u g X Λ₁ ΛR lam) (hedge : IsEdgeExtremalOn a b u X)
    (hS : ∀ t ∈ Icc a b, (g t, Λ₁ t, X t, ΛR t) ∉ singularLocus) :
    IsFiniteBangBang a b u := by
  sorry

end SmoothedPolygons
