module

public import SmoothedPolygons.Ch8.Defs

/-!
# The edge control problem and the Reinhardt problem (§8.1, running text)

The running text of §8.1 (TeX 6678–6775) connects the edge control problem (Definition 8.1.1) to
a Reinhardt trajectory `(g, X)` whose control lies in an edge of `U_T` on a time interval
`[c, d]`, written `u = (0, ½ + u_e, ½ - u_e)` after the rotation `edgeFrame j`:

* `eqn_xy_edge`: the half-plane coordinates `z = x + iy` of `X` (`Φ(z) = X`, Lemma 4.2.1) and
  `s = ∫ dt/y` solve the state equations (8.1.3) `x' = y`, `y' = f₂(x, y, u_e)`, `s' = 1/y`
  (`eqn:xy-edge`): the specialization of Lemma 4.5.2 to the edge; `x' = y > 0`;
* `eqn_g_edge`: `g(t) = g₀ h(t₀)⁻¹ h(t)` with `h = [[1, -x], [s, 1 - sx]]` (8.1.1)–(8.1.2)
  (`eqn:g-edge`);
* `edgeCost_identity`: the cost of the Reinhardt trajectory on `[c, d]` is
  `(3/2)((s + x)|_c^d + ∫ x²/y)`, so that up to the positive factor `3/2` and a constant fixed by
  the boundary conditions it is the edge cost (8.1.5) (`eqn:edge:cost`), by (4.3.1);
* `eqn_edge_ham`: the Hamiltonian of the edge problem is (8.1.6) (`eqn:edge:ham`);
* `eqn_costate_edge`: the costate equations (8.1.7) (`eqn:costate-edge`), derived in the proof of
  Theorem 8.1.4 from (8.1.6) as `λ' = -∂H/∂(x, y, s)`; `λ₃` is constant.

Remark 8.1.6 is in `SmoothedPolygons/Ch8/EdgeAbnormal.lean`.
-/

@[expose] public section

namespace SmoothedPolygons

open Set MeasureTheory Filter Topology Matrix

/-- The matrix `h(t) = [[1, -x], [s, 1 - s x]]` of equation (8.1.1), as a function of the edge
state `q = (x, y, s)`. -/
noncomputable def edgeH (q : Fin 3 → ℝ) : Mat2 := !![1, -q 0; q 2, 1 - q 2 * q 0]

/-- **The edge state equations** (8.1.3) (`eqn:xy-edge`; running text TeX 6678–6730). Let
`(g, X)` be a state trajectory of the Reinhardt problem on `[0, T]` whose control has
`u_j = 0` almost everywhere on `[c, d] ⊆ [0, T]`. After the rotation `X̃ = Rʲ X R⁻ʲ` the control
is `(0, ½ + u_e, ½ - u_e)` with `u_e = edgeParam j u` (`Rʲ Z_u R⁻ʲ = Z_{edgeControl u_e}`), the
point `z = x + iy` with `Φ(z) = X̃` lies in the star domain, and `(x, y, s)` (`edgeState j X c`)
with `s = ∫ dt/y` is an admissible trajectory of the edge control system: `x' = y`,
`y' = f₂(x, y, u_e)`, `s' = 1/y`, in the state space `y > 0`, `|x| < 1/√3`, with controls in
`[-½, ½]`.

Proof (TeX 6690–6700): `X̃ = Rʲ X R⁻ʲ` solves `X̃' = [P̃, X̃]` with
`P̃ = Z_{u'}/⟨Z_{u'}, X̃⟩`, `u'_m = u_{m+j}` (`poly_Rinv_conj_vertex` and the conjugation
invariance of the trace form, as in `poly_conj_pow_rhs`), and `X̃` is a star state
(`poly_isStarState_conj_pow`), so `X̃ = Φ(x, y)` with `(x, y) ∈ 𝔥*` (`lemma4_1_1`,
`theorem4_4_1`). Lemma 4.5.2 (`lemma4_5_2`) gives `(x', y') = (f₁, f₂)(x, y; u')` at almost every
time, and for `u' = (0, ½ + u_e, ½ - u_e)` the entries `Z₁₀ = 0`, `Z₀₀ = 2u_e/√3`, `Z₀₁ = -2/3`
give `f₁ = y` and `f₂ = 2√3 y² u_e/(-1 + 2√3 x u_e)` (field_simp). The integral form follows from
the absolute continuity of `x = X̃₀₀/X̃₁₀`, `y = 1/X̃₁₀` (`X̃₁₀ > 0`, bounded below on `[c, d]`).
Expected size: 150–300 lines. -/
theorem eqn_xy_edge {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2} (h : IsStateTrajectory T u g X)
    {j : Fin 3} {c d : ℝ} (hc : 0 ≤ c) (hcd : c < d) (hd : d ≤ T)
    (hu : ∀ᵐ t, t ∈ Ioo c d → u t j = 0) :
    Pontryagin.IsAdmissibleIn edgeField edgeDomain edgeControlSet (edgeState j X c 0) (d - c)
        (fun t ↦ edgeParam j (u (c + t))) (edgeState j X c) ∧
      (∀ t ∈ Icc 0 (d - c),
        edgeFrame j (X (c + t)) = Φ (edgeState j X c t 0) (edgeState j X c t 1) ∧
          (edgeState j X c t 0, edgeState j X c t 1) ∈ starDomain) ∧
      ∀ᵐ t, t ∈ Ioo c d →
        edgeFrame j (controlMatrix (u t)) = controlMatrix (edgeControl (edgeParam j (u t))) := by
  sorry

/-- **Equation (8.1.1)** (`eqn:g-edge`, TeX 6704–6723). On an interval `[c, d]` on which the
control lies in the edge `{u_j = 0}`, the state `g` is determined by the edge state `(x, y, s)`:
in the rotated frame `g̃ = Rʲ g R⁻ʲ`, `g̃(t) = g̃(c) h(c)⁻¹ h(t)` with
`h = [[1, -x], [s, 1 - sx]]` and `s(t) = ∫_c^t dτ/y` ((8.1.2)); in particular `g` depends on the
path only through the endpoint values of `(s, x)` (adding a constant to `s` leaves `g`
unchanged).

Proof: `g̃' = g̃ X̃` (`X̃ = Rʲ X R⁻ʲ`), and `h' = h Φ(x, y)` when `x' = y`, `s' = 1/y`
(`h⁻¹h' = [[x/y, -(x² + y²)/y], [1/y, -x/y]] = Φ(z)`, `det h = 1`; matrix ext and field_simp),
with `X̃ = Φ(x, y)` (`eqn_xy_edge`); both sides solve `G' = G X̃` with the same value at `c`, so
they agree (uniqueness for the linear equation, as `IsStateTrajectory.eq_conj_of_isIntegralCurve`
or Gronwall). Expected size: 100–200 lines. -/
theorem eqn_g_edge {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2} (h : IsStateTrajectory T u g X)
    {j : Fin 3} {c d : ℝ} (hc : 0 ≤ c) (hcd : c < d) (hd : d ≤ T)
    (hu : ∀ᵐ t, t ∈ Ioo c d → u t j = 0) :
    ∀ t ∈ Icc c d, edgeFrame j (g t) =
      edgeFrame j (g c) * (edgeH (edgeState j X c 0))⁻¹ * edgeH (edgeState j X c (t - c)) := by
  sorry

/-- **The cost of an edge arc** (running text TeX 6739–6754, with (8.1.5), `eqn:edge:cost`).
On an interval `[c, d]` on which the control lies in the edge `{u_j = 0}`, the Reinhardt cost
`-(3/2) ∫_c^d ⟨J, X⟩` equals `(3/2) ((s + x)|_c^d + ∫_c^d x²/y)`: by (4.3.1),
`-(3/2)⟨J, Φ(z)⟩ = (3/2)(1 + x² + y²)/y`, and `(1 + x² + y²)/y = s' + x' + x²/y`. So, up to the
positive factor `3/2` and the constant `(s₁ + x₁) - (s₀ + x₀)` fixed by the boundary conditions,
the cost is the edge cost `∫ φ_edge`, `φ_edge = x²/y`.

Proof: `⟨J, Rʲ X R⁻ʲ⟩ = ⟨J, X⟩` (`J` commutes with `R`, `poly_conj_pow_J`), the explicit
`⟨J, Φ(x, y)⟩ = -(1 + x² + y²)/y`, and the fundamental theorem of calculus for the absolutely
continuous `x` and `s` (`eqn_xy_edge`). Expected size: 80–150 lines. -/
theorem edgeCost_identity {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsStateTrajectory T u g X) {j : Fin 3} {c d : ℝ} (hc : 0 ≤ c) (hcd : c < d) (hd : d ≤ T)
    (hu : ∀ᵐ t, t ∈ Ioo c d → u t j = 0) :
    -(3 / 2) * ∫ t in c..d, traceForm J (X t) =
      3 / 2 * ((edgeState j X c (d - c) 2 + edgeState j X c (d - c) 0) -
          (edgeState j X c 0 2 + edgeState j X c 0 0) +
        ∫ t in (0 : ℝ)..d - c, edgeCost (edgeState j X c t) (edgeParam j (u (c + t)))) := by
  sorry

/-- The Hamiltonian (8.1.6) of the edge control problem,
`H = λ₁ y + λ₂ f₂(x, y, u_e) + λ₃/y + λ_cost x²/y` (`eqn:edge:ham`). -/
noncomputable def edgeHamiltonian (lam l₁ l₂ l₃ x y ue : ℝ) : ℝ :=
  l₁ * y + l₂ * edgeF₂ x y ue + l₃ / y + lam * (x ^ 2 / y)

/-- **Equation (8.1.6)** (`eqn:edge:ham`): the Hamiltonian `⟨p, f(q, u_e)⟩ + λ_cost φ_edge(q)` of
the maximum principle for the edge control problem is
`λ₁ y + λ₂ f₂(x, y, u_e) + λ₃/y + λ_cost x²/y`, `λ_{i+1} = p(e_i)`. Proof: linearity of `p`
(`edgeField q u_e = y e₀ + f₂ e₁ + (1/y) e₂`). Expected size: 10–20 lines. -/
theorem eqn_edge_ham (ν : ℝ) (q : Fin 3 → ℝ) (p : StrongDual ℝ (Fin 3 → ℝ)) (ue : ℝ) :
    Pontryagin.controlHamiltonian edgeField edgeCost ν q p ue =
      edgeHamiltonian ν (edgeCostate p 0) (edgeCostate p 1) (edgeCostate p 2) (q 0) (q 1) ue := by
  sorry

/-- The right-hand side `λ₂ · 12 y² u_e² / (1 - 2√3 x u_e)² - 2 λ_cost x/y` of the costate
equation for `λ₁` in (8.1.7) (`eqn:costate-edge`), `= -∂H/∂x`. -/
noncomputable def edgeCostateRHS₁ (lam l₂ x y ue : ℝ) : ℝ :=
  l₂ * (12 * y ^ 2 * ue ^ 2 / (1 - 2 * √3 * x * ue) ^ 2) - 2 * lam * x / y

/-- The right-hand side
`λ₃/y² - λ₁ - λ₂ · 4√3 y u_e / (-1 + 2√3 x u_e) + λ_cost x²/y²` of the costate equation for `λ₂`
in (8.1.7) (`eqn:costate-edge`), `= -∂H/∂y`. -/
noncomputable def edgeCostateRHS₂ (lam l₁ l₂ l₃ x y ue : ℝ) : ℝ :=
  l₃ / y ^ 2 - l₁ - l₂ * (4 * √3 * y * ue / (-1 + 2 * √3 * x * ue)) + lam * x ^ 2 / y ^ 2

/-- **The costate equations (8.1.7)** (`eqn:costate-edge`, TeX 6822–6838, in the proof of
Theorem 8.1.4). Along an extremal of the edge control problem the costates `λ₁, λ₂, λ₃` (dual to
`x, y, s`) satisfy `λ₁' = -∂H/∂x = λ₂ 12 y² u_e²/(1 - 2√3 x u_e)² - 2 λ_cost x/y`,
`λ₂' = -∂H/∂y = λ₃/y² - λ₁ - λ₂ 4√3 y u_e/(-1 + 2√3 x u_e) + λ_cost x²/y²` and
`λ₃' = -∂H/∂s = 0`, in integral form ("We note that `λ₃` is constant").

Proof: the adjoint equation `p' = -p ∘ ∂ₓf - ν ∂ₓφ` (`Pontryagin.IsAdjoint`) evaluated on the
basis vectors `e₀, e₁, e₂`, with the partial derivatives of `edgeField` and `edgeCost`
(`∂f₂/∂x = -12 y² u_e²/(-1 + 2√3 x u_e)²`, `∂f₂/∂y = 4√3 y u_e/(-1 + 2√3 x u_e)`; nothing depends
on `s`), and the change from the backward form `p(t) = p(T) + ∫ₜᵀ` to the forward one.
Expected size: 80–150 lines. -/
theorem eqn_costate_edge {T : ℝ} {ue : ℝ → ℝ} {q : ℝ → Fin 3 → ℝ} {ν : ℝ}
    {p : ℝ → StrongDual ℝ (Fin 3 → ℝ)} (h : IsEdgeProblemExtremal T ue q ν p) :
    (∀ t ∈ Icc 0 T, edgeCostate (p t) 2 = edgeCostate (p 0) 2) ∧
      IntervalIntegrable
        (fun t ↦ edgeCostateRHS₁ ν (edgeCostate (p t) 1) (q t 0) (q t 1) (ue t)) volume 0 T ∧
      (∀ t ∈ Icc 0 T, edgeCostate (p t) 0 = edgeCostate (p 0) 0 +
        ∫ s in (0 : ℝ)..t, edgeCostateRHS₁ ν (edgeCostate (p s) 1) (q s 0) (q s 1) (ue s)) ∧
      IntervalIntegrable (fun t ↦ edgeCostateRHS₂ ν (edgeCostate (p t) 0) (edgeCostate (p t) 1)
        (edgeCostate (p t) 2) (q t 0) (q t 1) (ue t)) volume 0 T ∧
      ∀ t ∈ Icc 0 T, edgeCostate (p t) 1 = edgeCostate (p 0) 1 +
        ∫ s in (0 : ℝ)..t, edgeCostateRHS₂ ν (edgeCostate (p s) 0) (edgeCostate (p s) 1)
          (edgeCostate (p s) 2) (q s 0) (q s 1) (ue s) := by
  sorry

end SmoothedPolygons
