module

public import SmoothedPolygons.Ch6.Hamiltonian
public import Mathlib.LinearAlgebra.Dual.Defs

/-!
# The Hamiltonian and costate equations in the upper half-plane (§6.8)

The cotangent space of the adjoint orbit (Lemma 6.8.1), the covector `ν = T*Φ(-Λ_R)`
(`eqn:nu`), the Hamiltonian in half-plane coordinates (Theorem 6.8.2), and the costate equation
`ν' = -dH` (Theorem 6.8.3).
-/

@[expose] public section

namespace SmoothedPolygons

open Matrix

/-- The orthogonal complement `X^⊥ = {Y ∈ 𝔰𝔩₂(ℝ) | ⟨Y, X⟩ = 0}` of `X` for the trace form. -/
def perpSl2 (X : Mat2) : Submodule ℝ Mat2 :=
  sl2 ⊓ LinearMap.ker ((Matrix.traceLinearMap (Fin 2) ℝ ℝ).comp (LinearMap.mulRight ℝ X))

/-- **Lemma 6.8.1** (`lem:cotangent-space-OX`). For `X ∈ 𝔰𝔩₂(ℝ)`, `X ≠ 0` (in the book,
`X ∈ O_J`): `X^⊥ = {[W, X] | W ∈ 𝔰𝔩₂(ℝ)}`, and `T*_X O_X ≅ (𝔰𝔩₂(ℝ)/ℝX)* ≅ X^⊥`, the second
isomorphism pairing `Y ∈ X^⊥` with `W + ℝX` by the trace form. -/
theorem lemma6_8_1 (X : Mat2) (hX : X.trace = 0) (hX0 : X ≠ 0) :
    (perpSl2 X : Set Mat2) = adImage X ∧
      ∃ e : perpSl2 X ≃ₗ[ℝ] Module.Dual ℝ (sl2 ⧸ (ℝ ∙ (⟨X, by simpa [sl2] using hX⟩ : sl2))),
        ∀ (Y : perpSl2 X) (W : sl2), e Y (Submodule.Quotient.mk W) = traceForm Y W := by
  sorry

/-- The covector `ν = T*Φ(-Λ_R) = ν₁ dx + ν₂ dy ∈ T*_z𝔥` (`eqn:nu`): `ν(r) = ⟨-Λ_R, Y_z(r)⟩`, where
`Y_z(r)` represents `T_zΦ(r)` in `𝔰𝔩₂(ℝ)/ℝX` (Lemma 4.2.4) and `Λ_R ∈ X^⊥ ≅ T*_X O_X`
(Lemma 6.8.1). -/
noncomputable def cotangentNu (x y : ℝ) (ΛR : Mat2) : ℝ × ℝ :=
  (traceForm (-ΛR) (tangentLift x y 1 0), traceForm (-ΛR) (tangentLift x y 0 1))

/-- The Hamiltonian in half-plane coordinates,
`H(Λ₁, x, y, ν₁, ν₂; u) = ⟨Λ₁ - (3/2) λ_cost J, X⟩ + ν₁ f₁ + ν₂ f₂` with `X = Φ(x + iy)`. -/
noncomputable def planeHamiltonian (lam : ℝ) (Λ₁ : Mat2) (x y ν₁ ν₂ : ℝ) (u : Fin 3 → ℝ) : ℝ :=
  traceForm (Λ₁ - (3 / 2 * lam) • J) (Φ x y) + ν₁ * halfPlaneF₁ x y u + ν₂ * halfPlaneF₂ x y u

/-- **Theorem 6.8.2** (`thm:plane-hamiltonian`, Hamiltonian in the upper half-plane). With
`ν = T*Φ(-Λ_R)`, the Hamiltonian `H(Λ₁, Λ_R, X; Z_u)` becomes
`⟨Λ₁ - (3/2) λ_cost J, X⟩ + ν₁ f₁ + ν₂ f₂` in half-plane coordinates. -/
theorem theorem6_8_2 (lam : ℝ) (Λ₁ ΛR : Mat2) (x y : ℝ) (u : Fin 3 → ℝ)
    (hxy : (x, y) ∈ starDomain) (hu : u ∈ controlSimplex) (hΛ : ΛR.trace = 0)
    (hperp : traceForm ΛR (Φ x y) = 0) :
    hamiltonian lam Λ₁ ΛR (Φ x y) u =
      planeHamiltonian lam Λ₁ x y (cotangentNu x y ΛR).1 (cotangentNu x y ΛR).2 u := by
  sorry

/-- **Theorem 6.8.3** (`thm:lamR-dynamics`). The costate equation for `Λ_R` becomes Hamilton's
equation `ν' = -dH = -(∂H/∂x) dx - (∂H/∂y) dy` for `ν = T*Φ(-Λ_R)`, the partial derivatives of
`H(Λ₁, x, y, ν₁, ν₂; u)` being taken with `Λ₁, ν₁, ν₂` fixed. (The book omits the proof.) -/
theorem theorem6_8_3 (lam : ℝ) (u : Fin 3 → ℝ) (x y : ℝ → ℝ) (Λ₁ ΛR : ℝ → Mat2) (t : ℝ)
    (hxy : (x t, y t) ∈ starDomain) (hu : u ∈ controlSimplex)
    (hx : HasDerivAt x (halfPlaneF₁ (x t) (y t) u) t)
    (hy : HasDerivAt y (halfPlaneF₂ (x t) (y t) u) t)
    (hΛ : (ΛR t).trace = 0) (hperp : traceForm (ΛR t) (Φ (x t) (y t)) = 0)
    (hΛR : HasDerivAtEntrywise ΛR (costateRHS lam (Λ₁ t) (ΛR t) (Φ (x t) (y t)) u) t) :
    HasDerivAt (fun s ↦ (cotangentNu (x s) (y s) (ΛR s)).1)
        (-deriv (fun ξ ↦ planeHamiltonian lam (Λ₁ t) ξ (y t)
          (cotangentNu (x t) (y t) (ΛR t)).1 (cotangentNu (x t) (y t) (ΛR t)).2 u) (x t)) t ∧
      HasDerivAt (fun s ↦ (cotangentNu (x s) (y s) (ΛR s)).2)
        (-deriv (fun η ↦ planeHamiltonian lam (Λ₁ t) (x t) η
          (cotangentNu (x t) (y t) (ΛR t)).1 (cotangentNu (x t) (y t) (ΛR t)).2 u) (y t)) t := by
  sorry

end SmoothedPolygons
