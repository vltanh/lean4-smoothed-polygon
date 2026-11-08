module

public import SmoothedPolygons.Ch8.Defs
public import SmoothedPolygons.Ch7.Faces

/-!
# Singular locus and singular subarcs (§8.2: Lemmas 8.2.1, 8.2.2, Theorems 8.2.3, 8.2.6)

* Lemma 8.2.1 (`lem:LambdaR`): if the control-dependent term `H₂ = -⟨Λ, Z_u⟩/⟨X, Z_u⟩` of the
  Hamiltonian does not depend on `u ∈ U_T` then `Λ = 0`; if `Λ ≠ 0` the maximizers form a vertex
  or an edge of `U_T`.
* Lemma 8.2.2 (`lem:Lambda1`): at a zero of `Λ_R` the costate equation for `Λ_R` has a continuous
  right-hand side, and if also `Λ_R' = 0` there, then `λ_cost ≠ 0` and `Λ₁ = (3/2) λ_cost J`.
* Theorem 8.2.3 (`thm:circle-singular`): if `Λ_R ≡ 0` on an interval, the trajectory is a circular
  arc with the centre control `(⅓, ⅓, ⅓)`: `X ≡ J`, `Λ₁ ≡ (3/2) λ_cost J`, `g = g₀ exp(Jt)`.
* Theorem 8.2.6 (`thm:circle-iff-singular`): a singular subarc on which the Hamiltonian does not
  depend on the control stays in the singular locus and is a circular arc, and conversely.

Notes on the statements:
* Lemma 8.2.1 is printed "for all `X ∈ 𝔰𝔩₂(ℝ)`", but `H₂` is defined only where
  `⟨X, Z_u⟩ ≠ 0` on `U_T` (gap G7); that is the hypothesis here (it holds on the state space by
  Lemma 3.3.4, and Lemma 7.3.1 has the same hypothesis). For `X = 0` the printed statement would
  be meaningless.
* The converse of Theorem 8.2.6 is argued in the book through necessary conditions only
  (gap G9); the formal statement exhibits the lift `λ_cost = -1`, `Λ₁ = -(3/2) J`, `Λ_R = 0`.
-/

@[expose] public section

namespace SmoothedPolygons

open Set MeasureTheory Filter Topology Matrix

/-- **Lemma 8.2.1** (`lem:LambdaR`). Let `X ∈ 𝔰𝔩₂(ℝ)` with `⟨X, Z_u⟩ ≠ 0` for every `u ∈ U_T`
(where the control-dependent term `H₂(Λ, X, Z_u) = -⟨Λ, Z_u⟩/⟨X, Z_u⟩` of the Hamiltonian is
defined; gap G7), and `Λ ∈ X^⊥` (traceless, `⟨Λ, X⟩ = 0`). If `H₂` does not depend on the control
`u ∈ U_T`, then `Λ = 0`. If `Λ ≠ 0`, the set of controls maximizing the Hamiltonian is a vertex or
an edge of `U_T`.

Proof (the book's, TeX 7107–7126): `H₂ = -⟨Λ, P_u⟩`, `P_u = Z_u/⟨X, Z_u⟩`. Reduce to `X` a star
state with `det X = 1` (`⟨X, Z_u⟩` has a constant sign on `U_T`, so `X` or `-X` satisfies the star
inequalities by Lemma 3.3.4 and `det X > 0`; scaling `X` scales `H₂`), so `X = Φ(z)`, `z ∈ 𝔥*`
(Lemma 4.1.1, Theorem 4.4.1). The vectors `[P_u, X]` are the velocities `f(x, y; u)` of
(4.5.1) through the tangent map of Lemma 4.2.4, whose affine hull is the whole tangent space
(Lemma 6.1.2, `lemma6_1_2`); a constant `⟨Λ, P_u⟩` makes `Λ` orthogonal to all differences
`P_u - P_v`, hence (with `Λ ⊥ X`) to all of `𝔰𝔩₂(ℝ)`, so `Λ = 0`. Contrapositive: if `Λ ≠ 0` the
Hamiltonian is not constant on `U_T`, and the set of maximizers is a face of `U_T`
(Lemma 7.3.1, `lemma7_3_1`) other than `U_T`, i.e. a vertex or an edge (the faces of the
triangle). A shorter argument (not the book's): `Z_{e₁}, Z_{e₂}, Z_{e₃}` span `𝔰𝔩₂(ℝ)`, so
constancy `c` of the ratio gives `Λ = cX`, and `⟨X, X⟩ = -2 det X ≠ 0` gives `c = 0`.
Expected size: 150–250 lines. -/
theorem lemma8_2_1 {X Λ : Mat2} (hX : X.trace = 0) (hden : ∀ u ∈ controlSimplex,
    traceForm X (controlMatrix u) ≠ 0) (hΛ : Λ.trace = 0) (hΛX : traceForm Λ X = 0) :
    ((∀ u ∈ controlSimplex, ∀ v ∈ controlSimplex,
        traceForm Λ (controlMatrix u) / traceForm X (controlMatrix u) =
          traceForm Λ (controlMatrix v) / traceForm X (controlMatrix v)) → Λ = 0) ∧
      (Λ ≠ 0 → ∀ (lam : ℝ) (Λ₁ : Mat2),
        (∃ i : Fin 3, hamiltonianArgmax lam Λ₁ Λ X = {vertex i}) ∨
          ∃ k : Fin 3, hamiltonianArgmax lam Λ₁ Λ X = controlEdge k) := by
  sorry

/-- **Lemma 8.2.2** (`lem:Lambda1`). Along an extremal lifted trajectory on `[a, b]`, at every
time `t₀` with `Λ_R(t₀) = 0` the right-hand side of the costate equation for `Λ_R`
(`costateRHS`, `eqn:lamR`) is continuous: it tends to `[-Λ₁(t₀) + (3/2) λ_cost J, X(t₀)]`, so
`Λ_R` is differentiable at `t₀` with that derivative. If moreover `Λ_R'(t₀) = 0`, then
`λ_cost ≠ 0` and `Λ₁(t₀) = (3/2) λ_cost J`.

Proof (the book's, TeX 7137–7167): the control-dependent terms `[P, Λ_R] - ⟨Λ_R, P⟩[P, X]` are
bounded multiples of `Λ_R` (`P = Z_u/⟨Z_u, X⟩` is bounded on the trajectory, Lemma 3.3.4), so they
tend to `0`; the rest is continuous. The Hamiltonian vanishes along the extremal (`H = 0`
almost everywhere, extended to `t₀` by the same continuity), which at `t₀` reads
`⟨Λ_{1,cost}, X⟩ = 0`, `Λ_{1,cost} = Λ₁ - (3/2) λ_cost J` (8.2.1); `0 = Λ_R'(t₀)
= -[Λ_{1,cost}, X(t₀)]` puts `Λ_{1,cost}(t₀)` in the centralizer `ℝX(t₀)`; `ℝX ∩ X^⊥ = 0`
(`⟨X, X⟩ = -2`) gives `Λ_{1,cost}(t₀) = 0`. If `λ_cost = 0` then `(λ_cost, Λ₁, Λ_R) = 0` at `t₀`,
against the nontriviality of the reduced costate (gap G1; part of `IsStateCostateSolution`).
Expected size: 150–250 lines. -/
theorem lemma8_2_2 {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (h : IsExtremalOn a b u g X Λ₁ ΛR lam) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b) (hΛ : ΛR t₀ = 0) :
    Tendsto (fun t ↦ costateRHS lam (Λ₁ t) (ΛR t) (X t) (u t)) (𝓝[Icc a b] t₀)
        (𝓝 ((-Λ₁ t₀ + (3 / 2 * lam) • J) * X t₀ - X t₀ * (-Λ₁ t₀ + (3 / 2 * lam) • J))) ∧
      HasDerivWithinAtEntrywise ΛR
        ((-Λ₁ t₀ + (3 / 2 * lam) • J) * X t₀ - X t₀ * (-Λ₁ t₀ + (3 / 2 * lam) • J))
        (Icc a b) t₀ ∧
      ((-Λ₁ t₀ + (3 / 2 * lam) • J) * X t₀ - X t₀ * (-Λ₁ t₀ + (3 / 2 * lam) • J) = 0 →
        lam ≠ 0 ∧ Λ₁ t₀ = (3 / 2 * lam) • J) := by
  sorry

/-- **Theorem 8.2.3** (`thm:circle-singular`). If an extremal lifted trajectory has `Λ_R ≡ 0` on
an interval `(t₁, t₂)`, then on that interval the control is the centre `(⅓, ⅓, ⅓)` of `U_T`
almost everywhere, with `Z_u = J/3`; the trajectory is normal and `X`, `Λ₁` are constant:
`λ_cost ≠ 0`, `X = J`, `Λ₁ = (3/2) λ_cost J`, and `g(t) = g₀ exp(Jt)`, an arc of a circle; and it
is a singular subarc (Definition 6.2.1(3): the Hamiltonian does not involve the control).

Proof (the book's, TeX 7188–7216): `Λ_R = Λ_R' = 0` on the interval, so Lemma 8.2.2
(`lemma8_2_2`) gives `λ_cost ≠ 0` and `Λ₁ ≡ (3/2) λ_cost J`; then
`0 = Λ₁' = [Λ₁, X] = (3/2) λ_cost [J, X]`, so `X ∈ ℝJ ∩ O_J = {J}` (`det X = 1` and the star
condition `X₁₀ > 0` exclude `-J`). `0 = X' = [P, J]` forces `Z_u ∈ ℝJ`, which on `U_T` holds only
at the centre (`Z_{centre} = J/3`). Finally `g' = gJ` gives `g(t) = g(t₁) exp(J(t - t₁))`
(uniqueness for the linear equation). Expected size: 150–250 lines. -/
theorem theorem8_2_3 {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (h : IsExtremalOn a b u g X Λ₁ ΛR lam) {t₁ t₂ : ℝ} (h₁ : a ≤ t₁) (h₁₂ : t₁ < t₂)
    (h₂ : t₂ ≤ b) (hΛ : ∀ t ∈ Ioo t₁ t₂, ΛR t = 0) :
    lam ≠ 0 ∧
      (∀ᵐ t, t ∈ Ioo t₁ t₂ → u t = controlCentre ∧ controlMatrix (u t) = (1 / 3 : ℝ) • J) ∧
      (∀ t ∈ Icc t₁ t₂, X t = J ∧ Λ₁ t = (3 / 2 * lam) • J) ∧
      (∀ t ∈ Icc t₁ t₂, g t = g t₁ * expJ (t - t₁)) ∧
      IsSingularSubarc lam Λ₁ ΛR X t₁ t₂ := by
  sorry

/-- **Theorem 8.2.6** (`thm:circle-iff-singular`). Consider a Pontryagin extremal of the
Reinhardt problem that contains a singular subarc `(t₁, t₂)` along which the Hamiltonian is
independent of the control. Then during that time interval the extremal remains in the singular
locus, and the unique solution of the state and costate equations there is a multi-curve of
circular arcs up to an affine transformation: the control is the centre `(⅓, ⅓, ⅓)` a.e. and
`g(t) = g(t₁) exp(J(t - t₁))`, so `σ_j(t) = g(t) s_j*` is the image under the linear map `g(t₁)`
of an arc of the unit circle. Conversely, the lifted trajectory attached to a multi-curve of
circular arcs (`g(t) = g₀ exp(J(t - t₁))`, `X ≡ J`, centre control) is an extremal singular
subarc lying in the singular locus.

The forward direction is stated for extremal lifted trajectories on an interval (every Pontryagin
extremal restricts to one, `l3st_isExtremalOn_of_isPontryaginExtremal`); the converse produces a
lift on the interval of the arc (an arc has no boundary conditions of Problem 3.6.2).

Proof (the book's, TeX 7271–7298, "a summary of results already obtained"): forward, the
Hamiltonian is independent of the control, so `Λ_R = 0` on the interval (Lemma 8.2.1,
`lemma8_2_1`, with `X(t)` a star state, Lemma 3.3.4), and Theorem 8.2.3 (`theorem8_2_3`) gives
the circle and the costates, which lie in `𝒮_sing`. Converse (gap G9: the book derives necessary
conditions; here the lift is exhibited): `λ_cost = -1`, `Λ₁ = -(3/2) J`, `Λ_R = 0` solve the costate
equations (`[J, J] = 0`), `H ≡ 0` is independent of the control, and `(λ_cost, Λ₁) ≠ 0`.
Expected size: 100–200 lines. -/
theorem theorem8_2_6 :
    (∀ {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ},
      IsExtremalOn a b u g X Λ₁ ΛR lam → ∀ {t₁ t₂ : ℝ}, a ≤ t₁ → t₂ ≤ b →
        IsSingularSubarc lam Λ₁ ΛR X t₁ t₂ →
        (∀ t ∈ Ioo t₁ t₂, ∀ v ∈ controlSimplex, ∀ w ∈ controlSimplex,
          hamiltonian lam (Λ₁ t) (ΛR t) (X t) v = hamiltonian lam (Λ₁ t) (ΛR t) (X t) w) →
        (∀ t ∈ Icc t₁ t₂, (g t, Λ₁ t, X t, ΛR t) ∈ singularLocus) ∧
          (∀ᵐ t, t ∈ Ioo t₁ t₂ → u t = controlCentre) ∧
          ∀ t ∈ Icc t₁ t₂, g t = g t₁ * expJ (t - t₁)) ∧
      ∀ (t₁ t₂ : ℝ) (g₀ : Mat2), t₁ < t₂ → g₀.det = 1 →
        ∃ (Λ₁ ΛR : ℝ → Mat2) (lam : ℝ),
          IsExtremalOn t₁ t₂ (fun _ ↦ controlCentre) (fun t ↦ g₀ * expJ (t - t₁)) (fun _ ↦ J)
            Λ₁ ΛR lam ∧
          IsSingularSubarc lam Λ₁ ΛR (fun _ ↦ J) t₁ t₂ ∧
          ∀ t ∈ Icc t₁ t₂, (g₀ * expJ (t - t₁), Λ₁ t, J, ΛR t) ∈ singularLocus := by
  sorry

end SmoothedPolygons
