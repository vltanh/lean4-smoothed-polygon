module

public import SmoothedPolygons.Ch8.EdgeProblem

/-!
# The Reinhardt costate pulled back to an edge arc

Let an extremal lifted trajectory of the Reinhardt problem have its control in the edge
`{u_j = 0}` of `U_T` on `[c, d]`. In the frame `edgeFrame j` (tildes) the trajectory lies on the
edge submanifold of (8.1.1) (`eqn_g_edge`): `g̃ = g̃(c) h(q(0))⁻¹ h(q)`, `X̃ = Φ(x, y)`, with
`h = edgeH q = [[1, -x], [s, 1 - s x]]` and `q = (x, y, s)` the edge state (`eqn_xy_edge`). The
Reinhardt costate `(Λ₁, Λ₂)` (`Λ₂` the costate of `X`, `Λ_R = [Λ₂, X]`, so `Λ̃₂ = ¼[X̃, Λ̃_R]`
since `X̃² = -I` and `Λ̃_R ⊥ X̃`) pulls back along `q ↦ (g̃, X̃)` to the covector
`⟨Λ̃₁, h⁻¹ dh⟩ + ⟨Λ̃₂, dΦ⟩` on the edge state space. Shifted by `(3/2) λ_cost d(s + x)` (the cost
identity `edgeCost_identity`: the Reinhardt running cost is `(3/2)(s' + x' + x²/y)`), it is the
covector `edgePullback`,

* `λ_x = ⟨Λ̃₁, h⁻¹ ∂ₓh⟩ + ⟨Λ̃₂, ∂ₓΦ⟩ + (3/2) λ_cost`,
* `λ_y = ⟨Λ̃₂, ∂_yΦ⟩`,
* `λ_s = ⟨Λ̃₁, h⁻¹ ∂ₛh⟩ + (3/2) λ_cost`,

and with `ν = (3/2) λ_cost` it is a costate of the edge control problem (Definition 8.1.1):

* `IsExtremalOn.controlHamiltonian_edgePullback`: the edge Hamiltonian (8.1.6) of the pulled-back
  covector equals the Reinhardt Hamiltonian at the corresponding control of the edge, at every time
  and for every edge control (`H_e = H_R`);
* `IsExtremalOn.isAdjoint_edgePullback`: it solves the adjoint equation of the edge problem;
* `IsExtremalOn.isMaximal_edgePullback`: it satisfies the maximum condition of the edge problem;
* `IsExtremalOn.isEdgeProblemExtremal_edgePullback`: for a normal extremal (`λ_cost ≠ 0`) it lifts
  the edge arc to an extremal of the edge control problem (`IsEdgeProblemExtremal`);
* `IsExtremalOn.isEdgeExtremalOn_of_ne_zero`, `IsNormalExtremal.isEdgeExtremalOn`: every normal
  extremal is edge extremal (Definition 8.1.2).

This is the repair, along the book's lines, of the edge case of Theorem 8.2.7 for normal lifts
(`SmoothedPolygons/Ch8/NoSingularArcs.lean`, gap G8): the book connects the two problems through
(8.1.1) and the cost identity (TeX 6704–6754) and says that edges are handled by the edge problem
(TeX 7253–7258, 806–821), without relating the costates. For abnormal lifts (`λ_cost = 0`) the
pulled-back covector can vanish identically: exactly when the Reinhardt costate is conormal to the
edge submanifold (the family that contains Remark 8.1.6's, `remark8_1_6`); then it gives no edge
costate. The formulas were checked numerically along a normal extremal
(scratchpad `l3rev_pullback.py`: `H_e = H_R`, the adjoint equation (8.1.7), the maximum
condition).
-/

@[expose] public section

namespace SmoothedPolygons

open Set MeasureTheory Filter Topology Matrix

/-- The covector `l₁ dx + l₂ dy + l₃ ds` on the state space `(x, y, s)` of the edge control
problem: `edgeCostate (edgeCovector l₁ l₂ l₃) = ![l₁, l₂, l₃]`. -/
noncomputable def edgeCovector (l₁ l₂ l₃ : ℝ) : StrongDual ℝ (Fin 3 → ℝ) :=
  l₁ • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 ↦ ℝ) 0 +
    l₂ • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 ↦ ℝ) 1 +
    l₃ • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 ↦ ℝ) 2

/-- The control of the edge `{u_j = 0}` of `U_T` with edge parameter `v`: `u_j = 0`,
`u_{j+1} = ½ + v`, `u_{j+2} = ½ - v`. After the rotation `edgeFrame j` it is
`edgeControl v = (0, ½ + v, ½ - v)` (TeX 6684–6689), and `edgeParam j (edgeControlIn j v) = v`. -/
noncomputable def edgeControlIn (j : Fin 3) (v : ℝ) : Fin 3 → ℝ := fun m ↦ edgeControl v (m - j)

/-- The costate `Λ̃₂ = ¼ [X̃, Λ̃_R]` of the Lie-algebra variable in the frame `edgeFrame j`
(`X̃ = edgeFrame j X`, `Λ̃_R = edgeFrame j Λ_R`): for `X̃` with `det X̃ = 1`, `tr X̃ = 0` and
`Λ̃_R` traceless with `⟨Λ̃_R, X̃⟩ = 0`, it satisfies `[Λ̃₂, X̃] = Λ̃_R` (§6.4: `Λ_R = [Λ₂, X]`;
`Λ₂` is determined modulo `ℝX`, which the pairing with tangent vectors of the orbit does not
see). -/
noncomputable def edgeΛ₂ (j : Fin 3) (ΛR X : Mat2) : Mat2 :=
  (1 / 4 : ℝ) • (edgeFrame j X * edgeFrame j ΛR - edgeFrame j ΛR * edgeFrame j X)

/-- **The pulled-back costate** on the state space of the `j`-th edge control problem: the
covector `(λ_x, λ_y, λ_s)` with

* `λ_x = ⟨Λ̃₁, h⁻¹ ∂ₓh⟩ + ⟨Λ̃₂, ∂ₓΦ⟩ + (3/2) λ_cost`,
* `λ_y = ⟨Λ̃₂, ∂_yΦ⟩`,
* `λ_s = ⟨Λ̃₁, h⁻¹ ∂ₛh⟩ + (3/2) λ_cost`,

where the tildes are `edgeFrame j`, `h = edgeH q = [[1, -x], [s, 1 - s x]]` (8.1.1), so
`∂ₓh = [[0, -1], [0, -s]]` and `∂ₛh = [[0, 0], [1, -x]]`, `Λ̃₂ = edgeΛ₂ j Λ_R X`, and
`∂ₓΦ = [[1/y, -2x/y], [0, -1/y]]`, `∂_yΦ = [[-x/y², (x² - y²)/y²], [-1/y², x/y²]]` are the partial
derivatives of `Φ(x, y)` (Lemma 4.2.1), at `q = (x, y, s)`. It is the pullback of `(Λ₁, Λ₂)` along
the edge submanifold `q ↦ (g̃(c) h(q(0))⁻¹ h(q), Φ(x, y))` shifted by `(3/2) λ_cost d(x + s)`. -/
noncomputable def edgePullback (j : Fin 3) (lam : ℝ) (Λ₁ ΛR X : Mat2) (q : Fin 3 → ℝ) :
    StrongDual ℝ (Fin 3 → ℝ) :=
  edgeCovector
    (traceForm (edgeFrame j Λ₁) ((edgeH q)⁻¹ * !![0, -1; 0, -q 2]) +
      traceForm (edgeΛ₂ j ΛR X) !![1 / q 1, -(2 * q 0 / q 1); 0, -(1 / q 1)] + 3 / 2 * lam)
    (traceForm (edgeΛ₂ j ΛR X)
      !![-(q 0 / q 1 ^ 2), (q 0 ^ 2 - q 1 ^ 2) / q 1 ^ 2; -(1 / q 1 ^ 2), q 0 / q 1 ^ 2])
    (traceForm (edgeFrame j Λ₁) ((edgeH q)⁻¹ * !![0, 0; 1, -q 0]) + 3 / 2 * lam)

/-- **`H_e = H_R` for the pulled-back costate.** Along an extremal lifted trajectory on `[c, d]`
whose control lies in the edge `{u_j = 0}` almost everywhere, at every time `t ∈ [0, d - c]` and
for every edge control `v ∈ [-½, ½]`, the Hamiltonian of the edge problem (8.1.6) with
`ν = (3/2) λ_cost` and the pulled-back costate equals the Reinhardt Hamiltonian at the control
`edgeControlIn j v` of the edge.

Proof: `H_R` is invariant under the rotation `edgeFrame j` (`R` commutes with `J`, the trace form
is conjugation invariant, `edgeFrame j (Z_{edgeControlIn j v}) = Z_{edgeControl v}`). With
`X̃ = Φ(x, y)` (`eqn_xy_edge`), the edge velocity `(x', y', s') = (y, f₂, 1/y)` satisfies
`h⁻¹ (∂ₓh y + ∂ₛh / y) = Φ(x, y)` and `∂ₓΦ y + ∂_yΦ f₂ = [P̃, Φ]` with
`P̃ = Z_{edgeControl v}/⟨Z_{edgeControl v}, Φ⟩` (Lemma 4.5.2 on the edge); so
`⟨p, f_e⟩ = ⟨Λ̃₁, X̃⟩ + ⟨Λ̃₂, [P̃, X̃]⟩ + (3/2) λ_cost (y + 1/y)`, and
`⟨Λ̃₂, [P̃, X̃]⟩ = -⟨[Λ̃₂, X̃], P̃⟩ = -⟨Λ̃_R, P̃⟩` (`[Λ̃₂, X̃] = Λ̃_R` from `X̃² = -I` and
`⟨Λ̃_R, X̃⟩ = 0`), while `(3/2) λ_cost (y + 1/y + x²/y) = -(3/2) λ_cost ⟨J, Φ(x, y)⟩` (4.3.1).
Matrix algebra (`ext`, `field_simp`, `ring`). Expected size: 120–220 lines. -/
theorem IsExtremalOn.controlHamiltonian_edgePullback {c d : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ} (h : IsExtremalOn c d u g X Λ₁ ΛR lam) {j : Fin 3}
    (hu : ∀ᵐ t, t ∈ Ioo c d → u t j = 0) :
    ∀ t ∈ Icc 0 (d - c), ∀ v ∈ edgeControlSet,
      Pontryagin.controlHamiltonian edgeField edgeCost (3 / 2 * lam) (edgeState j X c t)
          (edgePullback j lam (Λ₁ (c + t)) (ΛR (c + t)) (X (c + t)) (edgeState j X c t)) v =
        hamiltonian lam (Λ₁ (c + t)) (ΛR (c + t)) (X (c + t)) (edgeControlIn j v) := by
  sorry

/-- **The pulled-back costate solves the adjoint equation of the edge problem** (with
`ν = (3/2) λ_cost`, `Pontryagin.IsAdjoint`, the costate equations (8.1.7)), along an extremal
lifted trajectory on `[c, d]` whose control lies in the edge `{u_j = 0}` almost everywhere.

Proof: the pulled-back costate is absolutely continuous (its entries are polynomial in the
entries of `Λ₁, Λ_R, X` and rational in `q`, all absolutely continuous, with `y` bounded below on
`[0, d - c]`). At almost every time, with `u = edgeControlIn j u_e`, the costate equations
`Λ₁' = [Λ₁, X]`, `Λ_R' = [P, Λ_R] - ⟨Λ_R, P⟩[P, X] + [-Λ₁ + (3/2) λ_cost J, X]` (rotated by
`edgeFrame j`) and the state equations (`eqn_xy_edge`) give its derivative; that it equals
`-p ∘ ∂_q f_e - ν ∂_q φ_e` is an identity of rational functions (the pullback of a Hamiltonian
system along an invariant submanifold on which the Hamiltonians agree, `H_e = H_R`), checked by
`field_simp; ring` on the three components. The integral form on `[0, d - c]` follows by the
fundamental theorem of calculus for absolutely continuous functions. Expected size: 250–450
lines. -/
theorem IsExtremalOn.isAdjoint_edgePullback {c d : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ} (h : IsExtremalOn c d u g X Λ₁ ΛR lam) {j : Fin 3}
    (hu : ∀ᵐ t, t ∈ Ioo c d → u t j = 0) :
    Pontryagin.IsAdjoint edgeField edgeCost (3 / 2 * lam) (fun t ↦ edgeParam j (u (c + t)))
      (edgeState j X c) (d - c)
      (fun t ↦ edgePullback j lam (Λ₁ (c + t)) (ΛR (c + t)) (X (c + t)) (edgeState j X c t)) := by
  sorry

/-- **The pulled-back costate satisfies the maximum condition of the edge problem**
(`Pontryagin.IsMaximal`, with `ν = (3/2) λ_cost` and controls in `[-½, ½]`), along an extremal
lifted trajectory on `[c, d]` whose control lies in the edge `{u_j = 0}` almost everywhere.

Proof: at almost every time the control is `edgeControlIn j u_e` (`u_j = 0`, `Σ u = 1`) and
maximizes the Reinhardt Hamiltonian over `U_T ⊇ controlEdge j`; by
`IsExtremalOn.controlHamiltonian_edgePullback` the edge Hamiltonian at `v ∈ [-½, ½]` is the
Reinhardt Hamiltonian at `edgeControlIn j v ∈ U_T`. Expected size: 40–80 lines. -/
theorem IsExtremalOn.isMaximal_edgePullback {c d : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ} (h : IsExtremalOn c d u g X Λ₁ ΛR lam) {j : Fin 3}
    (hu : ∀ᵐ t, t ∈ Ioo c d → u t j = 0) :
    Pontryagin.IsMaximal edgeField edgeCost (3 / 2 * lam) edgeControlSet
      (fun t ↦ edgeParam j (u (c + t))) (edgeState j X c) (d - c)
      (fun t ↦ edgePullback j lam (Λ₁ (c + t)) (ΛR (c + t)) (X (c + t)) (edgeState j X c t)) := by
  sorry

/-- **A normal extremal lifts its edge arcs to extremals of the edge problem.** Along an extremal
lifted trajectory on `[c, d]` with `λ_cost ≠ 0` whose control lies in the edge `{u_j = 0}` almost
everywhere, the pulled-back costate with `ν = (3/2) λ_cost` lifts the edge arc
`(edgeParam j u, edgeState j X c)` to an extremal of the `j`-th edge control problem.

Proof: `IsEdgeProblemExtremal` item by item: `0 < d - c`; admissibility (`eqn_xy_edge`, after the
time shift of `IsExtremalOn`); `ν = (3/2) λ_cost ≤ 0`; `(ν, p(t)) ≠ 0` because `ν ≠ 0`;
`IsExtremalOn.isAdjoint_edgePullback`; `IsExtremalOn.isMaximal_edgePullback`; and `H_e = 0`
almost everywhere from `H_R = 0` almost everywhere with
`IsExtremalOn.controlHamiltonian_edgePullback` at `v = u_e(t)`. Expected size: 40–80 lines. -/
theorem IsExtremalOn.isEdgeProblemExtremal_edgePullback {c d : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ} (h : IsExtremalOn c d u g X Λ₁ ΛR lam) (hlam : lam ≠ 0)
    {j : Fin 3} (hu : ∀ᵐ t, t ∈ Ioo c d → u t j = 0) :
    IsEdgeProblemExtremal (d - c) (fun t ↦ edgeParam j (u (c + t))) (edgeState j X c)
      (3 / 2 * lam)
      (fun t ↦ edgePullback j lam (Λ₁ (c + t)) (ΛR (c + t)) (X (c + t)) (edgeState j X c t)) := by
  sorry

/-- **A normal extremal lifted trajectory is edge extremal** (Definition 8.1.2): on every
subinterval on which the control lies in an edge, the pulled-back costate is an edge costate
(`IsExtremalOn.isEdgeProblemExtremal_edgePullback` on the subinterval, `l3st_isExtremalOn_mono`).
Expected size: 10–20 lines. -/
theorem IsExtremalOn.isEdgeExtremalOn_of_ne_zero {a b : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ} (h : IsExtremalOn a b u g X Λ₁ ΛR lam) (hlam : lam ≠ 0) :
    IsEdgeExtremalOn a b u X := by
  sorry

/-- **Every normal Pontryagin extremal is edge extremal** on `[0, T]` (Definition 6.2.1(2),
Definition 8.1.2): `IsExtremalOn.isEdgeExtremalOn_of_ne_zero` on each subinterval
(`l3st_isExtremalOn_of_isPontryaginExtremal`). Expected size: 10–20 lines. -/
theorem IsNormalExtremal.isEdgeExtremalOn {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    {lam : ℝ} (h : IsNormalExtremal T u g X Λ₁ ΛR lam) : IsEdgeExtremalOn 0 T u X := by
  sorry

end SmoothedPolygons
