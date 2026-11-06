module

public import Mathlib.Geometry.Manifold.GroupLieAlgebra
public import Mathlib.Algebra.Lie.InvariantForm
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# Left-invariant control systems (Definition 6.3.1, Proposition 6.4.1; Jurdjevic)

A control system `dg/dt = f(g, u)` on a real Lie group `G`, with controls `u ∈ U ⊆ ℝᵐ`, is
left-invariant if `TL_h f(g, u) = f(hg, u)`; its cost `φ(g, u)` is left-invariant if
`φ(g, u) = φ(e, u)` (Definition 6.3.1). Through the left trivialization `T*G ≅ G × 𝔤*`
(`p̃ = T*L_{g⁻¹}(p)`, Proposition 3.6.1) and the identification `𝔤 ≅ 𝔤*` given by a nondegenerate
invariant symmetric bilinear form, the Hamiltonian `H(g, p̃) = ⟨p̃, f(g, u)⟩_*` of a left-invariant
system becomes `⟨p, f(e, u)⟩` (Proposition 6.4.1).

Setting. The book works on a general real Lie group with its cotangent bundle; Mathlib has real
Lie groups (`LieGroup I ∞ G`, a smooth manifold modelled on `E` by `I`), their tangent maps
(`mfderiv`) and their Lie algebras (`GroupLieAlgebra I G`, the tangent space at `1` with the bracket
of left-invariant vector fields), so the statements are made in that generality: `f(g, u)` is a
tangent vector at `g`, `TL_h = mfderiv I I (h * ·) g`, a cotangent vector at `g` is a linear form on
`T_g G`, and `p̃ = T*L_{g⁻¹}(p)` is `v ↦ p(TL_{g⁻¹} v)`. Mathlib's Lie algebra structure on
`GroupLieAlgebra I G` needs the group to be `C^{minSmoothness ℝ 3}`, which a smooth Lie group is
(the local instance `r3_lieGroup_minSmoothness`).

The rest of the formalized chapters does not use these results: the Reinhardt problem's
Hamiltonian is derived directly in `SmoothedPolygons.Ch6.Hamiltonian` (Proposition 6.5.1).
-/

@[expose] public section

namespace SmoothedPolygons

open scoped Manifold ContDiff

variable {E H G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [TopologicalSpace G] [ChartedSpace H G]
  [Group G] [LieGroup I ∞ G]

omit [FiniteDimensional ℝ E] in
/-- A smooth real Lie group is `C^{minSmoothness ℝ 3}` (`minSmoothness ℝ 3 = 3`), the smoothness
that Mathlib's Lie algebra of a Lie group (`GroupLieAlgebra`) requires. -/
@[local instance]
lemma r3_lieGroup_minSmoothness : LieGroup I (minSmoothness ℝ 3) G :=
  LieGroup.of_le (n := ∞) (by rw [minSmoothness_of_isRCLikeNormedField]; exact ENat.LEInfty.out)

/-- **Definition 6.3.1** (`def:left-invariant-control-system`; Jurdjevic), the control system. A
control system `dg/dt = f(g, u)` on a real Lie group `G`, with `f(g, u) ∈ T_g G` and controls
`u ∈ U ⊆ ℝᵐ`, is left-invariant if `TL_h f(g, u) = f(hg, u)` for all `g, h ∈ G` and `u ∈ U`, where
`L_h(g) = hg` and `TL_h : T_g G → T_{hg} G` is its tangent map. -/
def IsLeftInvariantControlSystem {m : ℕ} (U : Set (Fin m → ℝ))
    (f : (g : G) → (Fin m → ℝ) → TangentSpace I g) : Prop :=
  ∀ g h : G, ∀ u ∈ U, mfderiv I I (fun x ↦ h * x) g (f g u) = f (h * g) u

/-- **Definition 6.3.1** (`def:left-invariant-control-system`; Jurdjevic). An optimal control
problem with control system `dg/dt = f(g, u)` on a real Lie group `G`, controls `u ∈ U ⊆ ℝᵐ` and
cost function `φ(g, u)` is left-invariant if the control system is left-invariant,
`TL_h f(g, u) = f(hg, u)` for all `g, h ∈ G` (`IsLeftInvariantControlSystem`), and the cost function
is left-invariant: `φ(g, u) = φ(e, u)` for all `g` and `u`, where `e` is the neutral element. -/
def IsLeftInvariantProblem {m : ℕ} (U : Set (Fin m → ℝ))
    (f : (g : G) → (Fin m → ℝ) → TangentSpace I g) (φ : G → (Fin m → ℝ) → ℝ) : Prop :=
  IsLeftInvariantControlSystem I U f ∧ ∀ g : G, ∀ u ∈ U, φ g u = φ 1 u

/-- The Hamiltonian `H(g, p̃) = ⟨p̃, f(g, u)⟩_*` of the control system `dg/dt = f(g, u)` at a
cotangent vector `p̃ ∈ T*_g G` (the definition used in the proof of Proposition 6.4.1). -/
noncomputable def controlHamiltonian {m : ℕ} (f : (g : G) → (Fin m → ℝ) → TangentSpace I g)
    (g : G) (p : Module.Dual ℝ (TangentSpace I g)) (u : Fin m → ℝ) : ℝ :=
  p (f g u)

/-- The cotangent vector `p̃ = T*L_{g⁻¹}(p) ∈ T*_g G` of `p ∈ 𝔤*`, `v ↦ p(TL_{g⁻¹} v)`: the left
trivialization `T*G ≅ G × 𝔤*` (Proposition 3.6.1). -/
noncomputable def leftTrivCovector (g : G) (p : Module.Dual ℝ (GroupLieAlgebra I G)) :
    Module.Dual ℝ (TangentSpace I g) :=
  p ∘ₗ (mfderiv I I (fun x ↦ g⁻¹ * x) g : TangentSpace I g →L[ℝ] GroupLieAlgebra I G).toLinearMap

/-- **Proposition 6.4.1** (`prop:left-invariant-hams`; Jurdjevic). Consider a left-invariant
control system `dg/dt = f(g, u)` on a real Lie group `G`, with control `u ∈ U ⊆ ℝᵐ`, and assume
that the Lie algebra `𝔤` of `G` is equipped with a nondegenerate invariant symmetric bilinear form
`⟨·, ·⟩`. Then the Hamiltonian of this system is `H(g, p) = ⟨p, f(e, u)⟩`, `p ∈ 𝔤`, where `e` is
the identity.

Formally: for `p ∈ 𝔤`, identified with `⟨p, ·⟩ ∈ 𝔤*` by the form, the Hamiltonian
`H(g, p̃) = ⟨p̃, f(g, u)⟩_*` at the cotangent vector `p̃ = T*L_{g⁻¹}(⟨p, ·⟩) ∈ T*_g G` of the left
trivialization is `⟨p, f(e, u)⟩`, for every `g ∈ G` and `u ∈ U`. ("Invariant" is invariance under
the adjoint action, `⟨[x, y], z⟩ = -⟨y, [x, z]⟩`, Mathlib's `LinearMap.BilinForm.lieInvariant`.)
The nondegeneracy, symmetry and invariance of the form are the book's hypotheses; nondegeneracy is
what makes `p ↦ ⟨p, ·⟩` the identification `𝔤 ≅ 𝔤*`, and the identity itself holds for every
bilinear form. The proof is the book's: `TL_{g⁻¹} f(g, u) = f(g⁻¹g, u) = f(e, u)` by
left-invariance. -/
theorem proposition6_4_1 {m : ℕ} {U : Set (Fin m → ℝ)}
    {f : (g : G) → (Fin m → ℝ) → TangentSpace I g} (hf : IsLeftInvariantControlSystem I U f)
    (B : LinearMap.BilinForm ℝ (GroupLieAlgebra I G)) (_hB : B.Nondegenerate) (_hBs : B.IsSymm)
    (_hBi : B.lieInvariant (GroupLieAlgebra I G)) (g : G) (u : Fin m → ℝ) (hu : u ∈ U)
    (p : GroupLieAlgebra I G) :
    controlHamiltonian I f g (leftTrivCovector I g (B p)) u = B p (f 1 u) := by
  have h := hf g g⁻¹ u hu
  have h1 : f (g⁻¹ * g) u = f 1 u := by rw [inv_mul_cancel]
  change B p (mfderiv I I (fun x ↦ g⁻¹ * x) g (f g u)) = B p (f 1 u)
  rw [h, h1]

end SmoothedPolygons
