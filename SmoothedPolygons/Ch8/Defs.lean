module

public import SmoothedPolygons.Ch6.PeriodicExtension
public import External.Pontryagin

/-!
# Chapter 8: definitions

The objects of Chapter 8 (Singular Locus, TeX 6631–7674) and the vocabulary its statements share:

* extremal lifted trajectories on a time interval `[a, b]` (`IsExtremalOn`): Chapter 8 works with
  "an extremal lifted trajectory on `[t₁, t₂]`" (Theorems 8.3.1, 8.3.2), the state–costate system
  of Problem 6.7.1 with the conditions of the maximum principle (§6.2) and no boundary
  conditions; `IsPontryaginExtremal` is such a trajectory on `[0, T]` with the transversality
  conditions (6.6.1), and restricts to every subinterval
  (`l3st_isExtremalOn_of_isPontryaginExtremal`);
* the edge control problem (Definition 8.1.1): its state `(x, y, s)`, control `u_e ∈ [-½, ½]`,
  dynamics (8.1.3), state space and cost (8.1.5), and its extremals (`IsEdgeProblemExtremal`), the
  lifted trajectories satisfying the conclusions of the maximum principle (§6.2: Hamilton's
  equations, the maximum condition, `H ≡ 0` for the free terminal time, `(λ_cost, λ) ≠ 0`,
  `λ_cost ≤ 0` constant), with the objects of `External.pontryagin_maximum_principle`;
* the edge coordinates of a Reinhardt trajectory whose control lies in an edge of `U_T`
  (TeX 6678–6730, "by rotational symmetry" for the other edges, TeX 6774–6775), and edge
  extremals (Definition 8.1.2, `IsEdgeExtremalOn`);
* the faces of `U_T` maximizing the Hamiltonian (§7.3, `hamiltonianArgmax`; the regions
  `(T*O_J)_I`), the edges of `U_T` (`controlEdge`);
* the singular locus (Definition 8.2.4, `singularLocus`);
* bang-bang controls with finitely many switches (`IsFiniteBangBang`; Definition 7.3.2 with the
  finiteness of Theorems 8.1.4, 8.3.2 and 16.3.1).

Conventions. Controls `u = (u₀, u₁, u₂)` are `Fin 3 → ℝ`, `vertex i` is the vertex `e_{i+1}`
(`Pi.single i 1`). The edge `{u_k = 0}` of `U_T` is the segment from `vertex (k + 1)` to
`vertex (k + 2)`. The state of the edge problem is `q = (x, y, s) : Fin 3 → ℝ` (indices `0, 1, 2`),
so that the costate `(λ₁, λ₂, λ₃)` dual to `(x, y, s)` (TeX 6761–6764) is `p(e₀), p(e₁), p(e₂)`
(`edgeCostate p 0`, `edgeCostate p 1`, `edgeCostate p 2`). The rotation by `R` (conjugation)
takes `Z_u` to `Z_{u'}` with the coordinates of `u` permuted cyclically
(`R⁻¹ Z_{e_m} R = Z_{e_{m+1}}`, `poly_Rinv_conj_vertex`); `X ↦ Rʲ X R⁻ʲ` takes a control in the
edge `{u_j = 0}` to a control in the edge `{u₀ = 0}`, which is the edge the book treats.
-/

@[expose] public section

namespace SmoothedPolygons

open Set MeasureTheory Filter Topology Matrix

/-! ### Extremal lifted trajectories on an interval -/

/-- An **extremal lifted trajectory on `[a, b]`** of the Reinhardt control problem (Chapter 8:
"Consider an extremal lifted trajectory on `[t₁, t₂]`", TeX 7449; "along a lifted extremal",
TeX 7129, 7176): the state–costate system of Problem 6.7.1 on `[a, b]` with the conditions of the
maximum principle of §6.2 (`λ_cost ≤ 0` constant, nontriviality of the reduced costate
`(λ_cost, Λ₁, Λ_R)`, the maximum condition and `H = 0` almost everywhere) and no boundary
conditions, written after the time shift `t ↦ a + t` as `IsStateCostateSolution` on
`[0, b - a]`. It includes `a < b`.

Nontriviality is imposed on the reduced costate, as Chapter 8 uses it (TeX 7163–7166, 7583;
inventory, gap G1); `IsPontryaginExtremal` imposes the same condition. -/
def IsExtremalOn (a b : ℝ) (u : ℝ → Fin 3 → ℝ) (g X Λ₁ ΛR : ℝ → Mat2) (lam : ℝ) : Prop :=
  IsStateCostateSolution (b - a) (fun t ↦ u (a + t)) (fun t ↦ g (a + t)) (fun t ↦ X (a + t))
    (fun t ↦ Λ₁ (a + t)) (fun t ↦ ΛR (a + t)) lam

/-! ### The edge control problem (Definition 8.1.1) -/

/-- The control `u = (0, ½ + u_e, ½ - u_e)` on the edge `{u₀ = 0}` of `U_T` with parameter
`u_e ∈ [-½, ½]` (TeX 6684–6689). -/
noncomputable def edgeControl (ue : ℝ) : Fin 3 → ℝ := ![0, 1 / 2 + ue, 1 / 2 - ue]

/-- The right-hand side `f₂(x, y, u_e) = 2√3 y² u_e / (-1 + 2√3 x u_e)` of `y' = f₂` on the edge
`{u₀ = 0}` (TeX 6697–6700; the specialization of Lemma 4.5.2 to `u = (0, ½ + u_e, ½ - u_e)`). -/
noncomputable def edgeF₂ (x y ue : ℝ) : ℝ := 2 * √3 * y ^ 2 * ue / (-1 + 2 * √3 * x * ue)

/-- The state space of the edge control problem (Definition 8.1.1): the open set of
`(x, y, s) ∈ ℝ³` with `y > 0` and `-1/√3 < x < 1/√3`. It contains the star domain (in the
coordinates `x, y`). -/
def edgeDomain : Set (Fin 3 → ℝ) := {q | 0 < q 1 ∧ -(1 / √3) < q 0 ∧ q 0 < 1 / √3}

/-- The control set `[-½, ½]` of the edge control problem (Definition 8.1.1). -/
noncomputable def edgeControlSet : Set ℝ := Icc (-(1 / 2)) (1 / 2)

/-- The state equations (8.1.3) (`eqn:xy-edge`) of the edge control problem, for the state
`q = (x, y, s)`: `x' = y`, `y' = f₂(x, y, u_e)`, `s' = 1/y`. -/
noncomputable def edgeField (q : Fin 3 → ℝ) (ue : ℝ) : Fin 3 → ℝ :=
  ![q 1, edgeF₂ (q 0) (q 1) ue, 1 / q 1]

/-- The cost integrand `φ_edge(x, y) = x²/y` of the edge control problem (8.1.5)
(`eqn:edge:cost`). -/
noncomputable def edgeCost (q : Fin 3 → ℝ) (_ue : ℝ) : ℝ := q 0 ^ 2 / q 1

/-- The costate `λ_{i+1} = p(e_i)` dual to the state coordinate `i` of the edge problem: `λ₁`,
`λ₂`, `λ₃` dual to `x`, `y`, `s` (TeX 6761–6764). -/
noncomputable def edgeCostate (p : StrongDual ℝ (Fin 3 → ℝ)) (i : Fin 3) : ℝ :=
  p (Pi.single i 1)

/-- An **extremal lifted trajectory of the edge control problem** on `[0, T]`
(Definition 8.1.1, `def:edge-extremal`, with the conditions of the maximum principle of §6.2):
the pair `(u_e, q)` is admissible in the state space `edgeDomain` with controls in `[-½, ½]`
(the state equations (8.1.3) in Carathéodory's sense, measurable control), and the covector curve
`p` with the constant `λ_cost = ν` satisfies

* `ν ≤ 0` and `(ν, p(t)) ≠ 0` for every `t ∈ [0, T]`;
* Hamilton's equations for the costate, `p' = -∂H/∂q` (`Pontryagin.IsAdjoint`, integral form);
* the maximum condition for the Hamiltonian (8.1.6) (`eqn:edge:ham`)
  `H = λ₁ y + λ₂ f₂(x, y, u_e) + λ₃/y + λ_cost x²/y` (`Pontryagin.controlHamiltonian`) over
  `[-½, ½]`, almost everywhere;
* `H = 0` almost everywhere (free terminal time).

With fixed endpoints (8.1.4) the transversality conditions are empty. These are the conclusions
of `External.pontryagin_maximum_principle` for the edge problem. -/
def IsEdgeProblemExtremal (T : ℝ) (ue : ℝ → ℝ) (q : ℝ → Fin 3 → ℝ) (ν : ℝ)
    (p : ℝ → StrongDual ℝ (Fin 3 → ℝ)) : Prop :=
  0 < T ∧ Pontryagin.IsAdmissibleIn edgeField edgeDomain edgeControlSet (q 0) T ue q ∧ ν ≤ 0 ∧
    (∀ t ∈ Icc 0 T, (ν, p t) ≠ 0) ∧ Pontryagin.IsAdjoint edgeField edgeCost ν ue q T p ∧
    Pontryagin.IsMaximal edgeField edgeCost ν edgeControlSet ue q T p ∧
    ∀ᵐ t ∂(volume.restrict (Icc 0 T)),
      Pontryagin.controlHamiltonian edgeField edgeCost ν (q t) (p t) (ue t) = 0

/-! ### Edge coordinates of a Reinhardt trajectory -/

/-- The rotation `X ↦ Rʲ X R⁻ʲ` that takes a control in the edge `{u_j = 0}` of `U_T` to a control
in the edge `{u₀ = 0}` treated by the book ("By rotational symmetry, we obtain edge control
systems likewise for the other edges of `U_T`", TeX 6774–6775): `Rʲ Z_u R⁻ʲ = Z_{u'}` with
`u'_m = u_{m+j}`. It is also applied to `g`, `Λ₁` and `Λ_R`. -/
noncomputable def edgeFrame (j : Fin 3) (M : Mat2) : Mat2 := R ^ (j : ℕ) * M * R⁻¹ ^ (j : ℕ)

/-- The edge parameter `u_e = (u_{j+1} - u_{j+2})/2` of a control `u` in the edge `{u_j = 0}`:
after the rotation `edgeFrame j`, `u = (0, ½ + u_e, ½ - u_e)` (TeX 6684–6689). -/
noncomputable def edgeParam (j : Fin 3) (u : Fin 3 → ℝ) : ℝ := (u (j + 1) - u (j + 2)) / 2

/-- The state `(x, y, s)` of the `j`-th edge control problem attached to the Reinhardt trajectory
`X` from the time `a`, as a function of the elapsed time `t` (TeX 6690–6730): `z = x + iy` is the
point of the upper half-plane with `Φ(z) = Rʲ X(a + t) R⁻ʲ` (so `x = X̃₀₀/X̃₁₀` and `y = 1/X̃₁₀`
for `X̃ = Rʲ X R⁻ʲ`, Lemma 4.2.1), and `s(t) = ∫ₐ^{a+t} dτ/y(τ)`, with `s(0) = 0` ("We can take
`s₀ = 0`", TeX 6732). -/
noncomputable def edgeState (j : Fin 3) (X : ℝ → Mat2) (a t : ℝ) : Fin 3 → ℝ :=
  ![edgeFrame j (X (a + t)) 0 0 / edgeFrame j (X (a + t)) 1 0, 1 / edgeFrame j (X (a + t)) 1 0,
    ∫ τ in a..a + t, edgeFrame j (X τ) 1 0]

/-- **Definition 8.1.2** (edge extremal). A Reinhardt trajectory `(g, X)` with control `u` is
*edge extremal* on `[a, b]` if on every subinterval `[c, d] ⊆ [a, b]` on which some component
`u_j` of the control is zero almost everywhere, the trajectory is extremal with respect to the
corresponding edge control problem: the edge state `(x, y, s)` of the trajectory on `[c, d]`
(`edgeState j X c`) with the edge control `u_e = edgeParam j u` lifts to an extremal of the edge
control problem (`IsEdgeProblemExtremal`, fixed endpoints those of the trajectory, (8.1.4)).

The edge state does not involve `g`, which on such an interval is determined by `(s, x)`
(equation (8.1.1), `eqn_g_edge`); the definition therefore takes `u` and `X` only. -/
def IsEdgeExtremalOn (a b : ℝ) (u : ℝ → Fin 3 → ℝ) (X : ℝ → Mat2) : Prop :=
  ∀ (j : Fin 3) (c d : ℝ), a ≤ c → c < d → d ≤ b → (∀ᵐ t, t ∈ Ioo c d → u t j = 0) →
    ∃ (ν : ℝ) (p : ℝ → StrongDual ℝ (Fin 3 → ℝ)),
      IsEdgeProblemExtremal (d - c) (fun t ↦ edgeParam j (u (c + t))) (edgeState j X c) ν p

/-! ### Faces of the control simplex and the maximizers of the Hamiltonian (§7.3) -/

/-- The set of controls in `U_T` maximizing the Hamiltonian `H(Λ₁, Λ_R, X; Z_u)`
(equation `eqn:max-ham`, §7.3): `(X, Λ_R) ∈ (T*O_J)_I` exactly when this set is the face
`(U_T)_I` spanned by the vertices `e_i`, `i ∈ I` (TeX 5813–5826). -/
def hamiltonianArgmax (lam : ℝ) (Λ₁ ΛR X : Mat2) : Set (Fin 3 → ℝ) :=
  {u ∈ controlSimplex | ∀ v ∈ controlSimplex,
    hamiltonian lam Λ₁ ΛR X v ≤ hamiltonian lam Λ₁ ΛR X u}

/-- The edge `{u ∈ U_T | u_k = 0}` of the control simplex, the face spanned by `vertex (k + 1)`
and `vertex (k + 2)`. -/
def controlEdge (k : Fin 3) : Set (Fin 3 → ℝ) := {u ∈ controlSimplex | u k = 0}

/-! ### The singular locus (Definition 8.2.4) -/

/-- **Definition 8.2.4** (singular locus).
`𝒮_sing = {(g, Λ₁, X, Λ_R) = (g₀, (3/2) λ_cost J, J, 0) | g₀ ∈ SL₂(ℝ), λ_cost ≠ 0}`, a subset of
the extended state space `T*(SL₂(ℝ) × 𝔰𝔩₂(ℝ))`, whose points are written `(g, Λ₁, X, Λ_R)`.
It lies over the point `z = i` of the star domain (`Φ(i) = J`).

The constant `λ_cost` is bound by the set-builder, as printed. Along an extremal with multiplier
`λ_cost`, the lift meets `𝒮_sing` at `t` exactly when `λ_cost ≠ 0`, `Λ₁(t) = (3/2) λ_cost J`,
`X(t) = J` and `Λ_R(t) = 0` with the extremal's own `λ_cost` (`l3st_mem_singularLocus_iff`, from
`H = 0`). -/
def singularLocus : Set (Mat2 × Mat2 × Mat2 × Mat2) :=
  {q | ∃ lam : ℝ, lam ≠ 0 ∧ q.1.det = 1 ∧ q.2.1 = (3 / 2 * lam) • J ∧ q.2.2.1 = J ∧
    q.2.2.2 = 0}

/-- The rotation `exp(Jt) = [[cos t, -sin t], [sin t, cos t]]`: the singular subarcs are
`g(t) = g₀ exp(Jt)` (Theorem 8.2.3). -/
noncomputable def expJ (t : ℝ) : Mat2 := !![Real.cos t, -Real.sin t; Real.sin t, Real.cos t]

/-- The centre `(⅓, ⅓, ⅓)` of the control simplex `U_T` (Theorem 8.2.3), with `Z_u = J/3`. -/
noncomputable def controlCentre : Fin 3 → ℝ := ![1 / 3, 1 / 3, 1 / 3]

/-! ### Bang-bang controls with finitely many switches -/

/-- The control `u` is **bang-bang with finitely many switches on `[a, b]`** (Definition 7.3.2;
Theorems 8.1.4, 8.3.2, 16.3.1: "equal a.e. to a piecewise constant function … with finitely many
switches"): off a finite set `S` of times, `u` is almost everywhere constant near each time of
`(a, b)`, equal to a vertex of `U_T`. (On each interval between consecutive points of `S ∪ {a, b}`
it is then almost everywhere equal to one vertex.) -/
def IsFiniteBangBang (a b : ℝ) (u : ℝ → Fin 3 → ℝ) : Prop :=
  ∃ S : Finset ℝ, ∀ t ∈ Ioo a b, t ∉ S → ∃ i : Fin 3, ∃ ε > 0,
    ∀ᵐ τ, τ ∈ Ioo (t - ε) (t + ε) → u τ = vertex i

/-! ### Basic facts about extremals on intervals -/

/-- A Pontryagin extremal on `[0, T]` is an extremal lifted trajectory on every subinterval
`[a, b]`. Proof: `isPontryaginExtremal_iff`, and the restriction of the integral equations and of
the almost-everywhere conditions to `[a, b]` after the time shift (as
`poly_integral_form_restrict`). Expected size: 60–120 lines. -/
theorem l3st_isExtremalOn_of_isPontryaginExtremal {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ} (h : IsPontryaginExtremal T u g X Λ₁ ΛR lam) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ T) : IsExtremalOn a b u g X Λ₁ ΛR lam := by
  sorry

/-- An extremal lifted trajectory on `[a, b]` is one on every subinterval `[c, d]`. Expected size:
40–80 lines (shared with `l3st_isExtremalOn_of_isPontryaginExtremal`). -/
theorem l3st_isExtremalOn_mono {a b c d : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    {lam : ℝ} (h : IsExtremalOn a b u g X Λ₁ ΛR lam) (hac : a ≤ c) (hcd : c < d) (hdb : d ≤ b) :
    IsExtremalOn c d u g X Λ₁ ΛR lam := by
  sorry

/-- Edge extremality on `[a, b]` passes to subintervals (immediate from Definition 8.1.2). -/
theorem l3st_isEdgeExtremalOn_mono {a b c d : ℝ} {u : ℝ → Fin 3 → ℝ} {X : ℝ → Mat2}
    (h : IsEdgeExtremalOn a b u X) (hac : a ≤ c) (hdb : d ≤ b) : IsEdgeExtremalOn c d u X :=
  fun j c' d' hc' hcd' hd' hu ↦ h j c' d' (hac.trans hc') hcd' (hd'.trans hdb) hu

/-- Along an extremal lifted trajectory on `[a, b]`, the lift `(g, Λ₁, X, Λ_R)` is continuous on
`[a, b]` (its entries are indefinite integrals of integrable functions). Expected size: 30–60
lines. -/
theorem l3st_continuousOn_lift {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (h : IsExtremalOn a b u g X Λ₁ ΛR lam) :
    ContinuousOn (fun t ↦ (g t, Λ₁ t, X t, ΛR t)) (Icc a b) := by
  sorry

/-- **Meeting the singular locus along an extremal.** Along an extremal lifted trajectory with
multiplier `λ_cost`, the lift is in `𝒮_sing` at `t ∈ [a, b]` if and only if `λ_cost ≠ 0`,
`Λ₁(t) = (3/2) λ_cost J`, `X(t) = J` and `Λ_R(t) = 0`; so the set of such times is closed.

Proof: at a time with `Λ_R(t) = 0` the Hamiltonian `H(Λ₁, Λ_R, X; Z_u) = ⟨Λ₁ - (3/2)λ_cost J, X⟩`
does not depend on the control, and `H = 0` almost everywhere extends to `t` by continuity (the
control-dependent term is a bounded multiple of `Λ_R`, as in the proof of Lemma 8.2.2); with
`Λ₁(t) = (3/2) μ J` and `X(t) = J` this gives `-3(μ - λ_cost) = 0`. Expected size: 60–120
lines. -/
theorem l3st_mem_singularLocus_iff {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    {lam : ℝ} (h : IsExtremalOn a b u g X Λ₁ ΛR lam) {t : ℝ} (ht : t ∈ Icc a b) :
    (g t, Λ₁ t, X t, ΛR t) ∈ singularLocus ↔
      lam ≠ 0 ∧ Λ₁ t = (3 / 2 * lam) • J ∧ X t = J ∧ ΛR t = 0 := by
  sorry

end SmoothedPolygons
