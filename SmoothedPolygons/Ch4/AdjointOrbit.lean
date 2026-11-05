module

public import SmoothedPolygons.Defs
public import Basic.Analysis.Calculus.MatrixEntrywise
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.Quotient.Defs

/-!
# The adjoint orbit of `J` and the upper half-plane (§4.1, §4.2)

The set of `X ∈ 𝔰𝔩₂(ℝ)` with `det X = 1` and `⟨J, X⟩ < 0` is the adjoint orbit `O_J`
(Lemma 4.1.1); the map `Φ` identifies the upper half-plane with `O_J` (Lemma 4.2.1), equivariantly
for the action of `SL₂(ℝ)` by linear fractional transformations (Remark 4.2.2). The tangent spaces
of adjoint orbits (Lemma 4.2.3) and the tangent map of `Φ` (Lemma 4.2.4).
-/

@[expose] public section

namespace SmoothedPolygons

open Matrix UpperHalfPlane

open scoped MatrixGroups

/-- The adjoint orbit `O_X = {Ad_g X | g ∈ SL₂(ℝ)} = {g X g⁻¹}` of `X`. -/
def adjointOrbit (X : Mat2) : Set Mat2 :=
  Set.range fun g : SL(2, ℝ) ↦ (g : Mat2) * X * ((g⁻¹ : SL(2, ℝ)) : Mat2)

/-- **Lemma 4.1.1** (`lem:X-hyperbolic`). The set of `X ∈ 𝔰𝔩₂(ℝ)` with `det X = 1` and
`⟨J, X⟩ < 0` is the adjoint orbit `O_J` of `J`. -/
theorem lemma4_1_1 :
    {X : Mat2 | X.trace = 0 ∧ X.det = 1 ∧ traceForm J X < 0} = adjointOrbit J := by
  sorry

/-- The map `Φ` on the upper half-plane `ℍ`: `Φ(x + iy) = [[x/y, -(x² + y²)/y], [1/y, -x/y]]`. -/
noncomputable def ΦH (z : ℍ) : Mat2 := Φ z.re z.im

/-- **Lemma 4.2.1** (`lem:def-phi`). The map `Φ : ℍ → O_J` is an isomorphism (a bijection of the
upper half-plane onto the adjoint orbit of `J`). -/
theorem lemma4_2_1 : Set.BijOn ΦH Set.univ (adjointOrbit J) := by
  sorry

/-- Remark 4.2.2: `Φ` is `SL₂(ℝ)`-equivariant, `g Φ(z) g⁻¹ = Φ(g · z)` for the action of `SL₂(ℝ)`
on `ℍ` by linear fractional transformations. -/
theorem ΦH_smul (g : SL(2, ℝ)) (z : ℍ) :
    ΦH (g • z) = (g : Mat2) * ΦH z * ((g⁻¹ : SL(2, ℝ)) : Mat2) := by
  sorry

/-- The Lie algebra `𝔰𝔩₂(ℝ)`, as the subspace of traceless matrices. -/
def sl2 : Submodule ℝ Mat2 := LinearMap.ker (Matrix.traceLinearMap (Fin 2) ℝ ℝ)

/-- The image `{[Y, X] | Y ∈ 𝔰𝔩₂(ℝ)}` of `ad_X` on `𝔰𝔩₂(ℝ)`. -/
def adImage (X : Mat2) : Submodule ℝ Mat2 :=
  sl2.map (LinearMap.mulRight ℝ X - LinearMap.mulLeft ℝ X)

/-- The tangent space at `X` of a set `S` of matrices: the velocities `γ'(0)` of the curves `γ` in
`S` with `γ(0) = X` that are differentiable at `0`. -/
def curveTangentSpace (S : Set Mat2) (X : Mat2) : Set Mat2 :=
  {V | ∃ γ : ℝ → Mat2, (∀ s, γ s ∈ S) ∧ γ 0 = X ∧ HasDerivAtEntrywise γ V 0}

/-- **Lemma 4.2.3** (`lem:half-plane-lie-algebra-iso`). For `X ∈ 𝔰𝔩₂(ℝ)`, `X ≠ 0`, the tangent space
of the adjoint orbit is `T_X O_X = {[Y, X] | Y ∈ 𝔰𝔩₂(ℝ)} ≅ 𝔰𝔩₂(ℝ)/ℝX`, the isomorphism sending
`[Y, X]` to `Y + ℝX`.

The book states the lemma for every `X ∈ 𝔰𝔩₂(ℝ)`; for `X = 0` the orbit is a point and
`𝔰𝔩₂(ℝ)/ℝX = 𝔰𝔩₂(ℝ)` is not isomorphic to `T_0 O_0 = 0`. The proof uses that `X` is regular,
which in `𝔰𝔩₂` means `X ≠ 0`, and the lemma is applied to `X ∈ O_J`; the hypothesis `X ≠ 0`
corrects this slip. -/
theorem lemma4_2_3 (X : Mat2) (hX : X.trace = 0) (hX0 : X ≠ 0) :
    curveTangentSpace (adjointOrbit X) X = adImage X ∧
      ∃ e : (sl2 ⧸ (ℝ ∙ (⟨X, by simpa [sl2] using hX⟩ : sl2))) ≃ₗ[ℝ] adImage X,
        ∀ Y : sl2, (e (Submodule.Quotient.mk Y) : Mat2) = (Y : Mat2) * X - X * (Y : Mat2) := by
  sorry

/-- The matrix `Y_z(r₁, r₂) = [[r₂/(2y), (y r₁ - r₂ x)/y], [0, -r₂/(2y)]]` that represents the
tangent vector `T_zΦ(r₁ ∂/∂x + r₂ ∂/∂y)` modulo `ℝX` (Lemma 4.2.4). -/
noncomputable def tangentLift (x y r₁ r₂ : ℝ) : Mat2 :=
  !![r₂ / (2 * y), (y * r₁ - r₂ * x) / y; 0, -r₂ / (2 * y)]

/-- **Lemma 4.2.4** (`lem:tangent-maps`). The tangent map of `Φ` at `z = x + iy` sends
`r₁ ∂/∂x + r₂ ∂/∂y` to `[Y_z(r₁, r₂), Φ(z)]`, that is, to the class of `Y_z(r₁, r₂)` in
`𝔰𝔩₂(ℝ)/ℝX ≅ T_X O_X`. -/
theorem lemma4_2_4 (x y r₁ r₂ : ℝ) (hy : 0 < y) :
    HasDerivAtEntrywise (fun s ↦ Φ (x + s * r₁) (y + s * r₂))
      (tangentLift x y r₁ r₂ * Φ x y - Φ x y * tangentLift x y r₁ r₂) 0 := by
  sorry

end SmoothedPolygons
