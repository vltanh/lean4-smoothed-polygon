module

public import SmoothedPolygons.Ch4.StarDomain
public import SmoothedPolygons.AppA.FunctionalDerivative
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs

/-!
# The Hamiltonian and the costate equations (Chapter 6)

The convexity of the velocity sets (Lemma 6.1.2), normal, abnormal and singular extremals
(Definition 6.2.1), the Hamiltonian of the Reinhardt problem (`eqn:full-hamiltonian`), the costate
equations in the Lie algebra (Proposition 6.5.1), the general solution for `Λ₁`
(Corollary 6.5.3), and the control-dependent term of the costate equation (Corollary 6.5.4). The
state–costate equations of Problem 6.7.1 are part of `IsPontryaginExtremal` in
`SmoothedPolygons.Defs`.
-/

@[expose] public section

namespace SmoothedPolygons

open Matrix

/-- The velocity `f(x, y; u) = (f₁, f₂)` of the half-plane control problem (Problem 4.5.1). -/
noncomputable def halfPlaneField (x y : ℝ) (u : Fin 3 → ℝ) : Fin 2 → ℝ :=
  ![halfPlaneF₁ x y u, halfPlaneF₂ x y u]

/-- **Lemma 6.1.2** (`lem:control-convex`). For every `z = x + iy ∈ 𝔥*` the velocity set
`f(x, y; U_T)` is convex: it is the convex hull of the velocities at the three vertices of `U_T`.
Moreover its affine hull is all of `ℝ²`. -/
theorem lemma6_1_2 (x y : ℝ) (h : (x, y) ∈ starDomain) :
    halfPlaneField x y '' controlSimplex =
        convexHull ℝ {halfPlaneField x y (vertex 0), halfPlaneField x y (vertex 1),
          halfPlaneField x y (vertex 2)} ∧
      Convex ℝ (halfPlaneField x y '' controlSimplex) ∧
      affineSpan ℝ (halfPlaneField x y '' controlSimplex) = ⊤ := by
  sorry

/-- **Definition 6.2.1** (`def:normal-abonormal-singular-extremals`), (1): an abnormal extremal is
an extremal with `λ_cost = 0`. -/
def IsAbnormalExtremal (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X Λ₁ ΛR : ℝ → Mat2) (lam : ℝ) : Prop :=
  IsPontryaginExtremal T u g X Λ₁ ΛR lam ∧ lam = 0

/-- **Definition 6.2.1**, (2): a normal extremal is an extremal with `λ_cost ≠ 0`. -/
def IsNormalExtremal (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X Λ₁ ΛR : ℝ → Mat2) (lam : ℝ) : Prop :=
  IsPontryaginExtremal T u g X Λ₁ ΛR lam ∧ lam ≠ 0

/-- **Definition 6.2.1**, (3): the lifted trajectory is a singular subarc on the open interval
`(a, b)` if at every time of the interval the maximization of the Hamiltonian over `U_T` does not
determine the control uniquely. -/
def IsSingularSubarc (lam : ℝ) (Λ₁ ΛR X : ℝ → Mat2) (a b : ℝ) : Prop :=
  a < b ∧ ∀ t ∈ Set.Ioo a b, ∃ v ∈ controlSimplex, ∃ w ∈ controlSimplex, v ≠ w ∧
    (∀ v' ∈ controlSimplex, hamiltonian lam (Λ₁ t) (ΛR t) (X t) v' ≤
      hamiltonian lam (Λ₁ t) (ΛR t) (X t) v) ∧
    ∀ v' ∈ controlSimplex, hamiltonian lam (Λ₁ t) (ΛR t) (X t) v' ≤
      hamiltonian lam (Λ₁ t) (ΛR t) (X t) w

/-- The Hamiltonian before the reduction `Λ_R = [Λ₂, X]` (§6.4):
`H(Λ₁, Λ₂, X; Z_u) = ⟨Λ₁ - (3/2) λ_cost J, X⟩ + ⟨Λ₂, [Z_u, X]⟩ / ⟨X, Z_u⟩`. -/
noncomputable def fullHamiltonian (lam : ℝ) (Λ₁ Λ₂ X : Mat2) (u : Fin 3 → ℝ) : ℝ :=
  traceForm (Λ₁ - (3 / 2 * lam) • J) X +
    traceForm Λ₂ (controlMatrix u * X - X * controlMatrix u) / traceForm X (controlMatrix u)

/-- The right-hand side `[P, Λ_R] - ⟨Λ_R, P⟩[P, X] + [-Λ₁ + (3/2) λ_cost J, X]` of the costate
equation for `Λ_R` (`eqn:lamR`), with `P = Z_u/⟨Z_u, X⟩`. -/
noncomputable def costateRHS (lam : ℝ) (Λ₁ ΛR X : Mat2) (u : Fin 3 → ℝ) : Mat2 :=
  (controlP u X * ΛR - ΛR * controlP u X) -
      traceForm ΛR (controlP u X) • (controlP u X * X - X * controlP u X) +
    ((-Λ₁ + (3 / 2 * lam) • J) * X - X * (-Λ₁ + (3 / 2 * lam) • J))

/-- **Proposition 6.5.1** (`eqn:lamR`, Lie algebra costate variables). Along a lifted trajectory
satisfying Hamilton's equations for the Hamiltonian `H(Λ₁, Λ₂, X; Z_u)` in the trivialized
cotangent bundle, `X' = δH/δΛ₂` and `Λ₂' = -δH/δX` (canonical equations on `T*𝔰𝔩₂(ℝ)`), and the
Euler–Arnold equation `Λ₁' = -ad_{δH/δΛ₁} Λ₁` (cited from Cushman–Bates), the costate variables
evolve as `Λ₁' = [Λ₁, X]` and `Λ_R' = [P, Λ_R] - ⟨Λ_R, P⟩[P, X] + [-Λ₁ + (3/2) λ_cost J, X]`, where
`P = Z_u/⟨X, Z_u⟩` and `Λ_R = [Λ₂, X]`. The control `u` is the value of the control at time `t`. -/
theorem proposition6_5_1 (lam : ℝ) (u : Fin 3 → ℝ) (X Λ₁ Λ₂ : ℝ → Mat2) (t : ℝ)
    (X' Λ₁' Λ₂' D₁ : Mat2)
    (htr : (X t).trace = 0 ∧ (Λ₁ t).trace = 0 ∧ (Λ₂ t).trace = 0)
    (hden : traceForm (X t) (controlMatrix u) ≠ 0)
    (hX : HasDerivAtEntrywise X X' t) (hΛ₁ : HasDerivAtEntrywise Λ₁ Λ₁' t)
    (hΛ₂ : HasDerivAtEntrywise Λ₂ Λ₂' t)
    (hHΛ₂ : HasFunctionalDerivative (fun L ↦ fullHamiltonian lam (Λ₁ t) L (X t) u) (Λ₂ t) X')
    (hHX : HasFunctionalDerivative (fun Y ↦ fullHamiltonian lam (Λ₁ t) (Λ₂ t) Y u) (X t) (-Λ₂'))
    (hHΛ₁ : HasFunctionalDerivative (fun L ↦ fullHamiltonian lam L (Λ₂ t) (X t) u) (Λ₁ t) D₁)
    (hEA : Λ₁' = -(D₁ * Λ₁ t - Λ₁ t * D₁)) :
    Λ₁' = Λ₁ t * X t - X t * Λ₁ t ∧
      HasDerivAtEntrywise (fun s ↦ Λ₂ s * X s - X s * Λ₂ s)
        (costateRHS lam (Λ₁ t) (Λ₂ t * X t - X t * Λ₂ t) (X t) u) t := by
  sorry

/-- **Corollary 6.5.3** (`cor:lam1-gen-sol`, Jurdjevic). If `g' = gX` with `g(0) = I₂` and
`g(t) ∈ SL₂(ℝ)`, and `Λ₁' = [Λ₁, X]` (a Lax equation), then `Λ₁` evolves in an adjoint orbit:
`Λ₁(t) = Ad_{g(t)⁻¹} Λ₁(0) = g(t)⁻¹ Λ₁(0) g(t)`; in particular `det Λ₁(t)` is constant. -/
theorem corollary6_5_3 (T : ℝ) (g X Λ₁ : ℝ → Mat2)
    (hg : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAtEntrywise g (g t * X t) (Set.Icc 0 T) t)
    (hg0 : g 0 = 1) (hdet : ∀ t ∈ Set.Icc 0 T, (g t).det = 1)
    (hΛ : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAtEntrywise Λ₁ (Λ₁ t * X t - X t * Λ₁ t) (Set.Icc 0 T) t) :
    ∀ t ∈ Set.Icc 0 T, Λ₁ t = (g t)⁻¹ * Λ₁ 0 * g t ∧ (Λ₁ t).det = (Λ₁ 0).det := by
  sorry

/-- **Corollary 6.5.4** (`cor:control-dep-ad-alternate`). The control-dependent term of the
costate equation for `Λ_R` is
`[P, Λ_R] - (⟨Λ_R, Z_u⟩/⟨X, Z_u⟩)[P, X] = ad_{Z_u} δ/δZ_u (⟨Λ_R, Z_u⟩/⟨X, Z_u⟩)`; the functional
derivative is `(⟨X, Z_u⟩ Λ_R - ⟨Λ_R, Z_u⟩ X)/⟨X, Z_u⟩²`. -/
theorem corollary6_5_4 (ΛR X Z : Mat2) (hΛ : ΛR.trace = 0) (hX : X.trace = 0)
    (hZ : Z.trace = 0) (hXZ : traceForm X Z ≠ 0) :
    HasFunctionalDerivative (fun W ↦ traceForm ΛR W / traceForm X W) Z
        ((traceForm X Z ^ 2)⁻¹ • (traceForm X Z • ΛR - traceForm ΛR Z • X)) ∧
      Z * ((traceForm X Z ^ 2)⁻¹ • (traceForm X Z • ΛR - traceForm ΛR Z • X)) -
          ((traceForm X Z ^ 2)⁻¹ • (traceForm X Z • ΛR - traceForm ΛR Z • X)) * Z =
        ((traceForm X Z)⁻¹ • Z * ΛR - ΛR * (traceForm X Z)⁻¹ • Z) -
          (traceForm ΛR Z / traceForm X Z) •
            ((traceForm X Z)⁻¹ • Z * X - X * (traceForm X Z)⁻¹ • Z) := by
  sorry

end SmoothedPolygons
