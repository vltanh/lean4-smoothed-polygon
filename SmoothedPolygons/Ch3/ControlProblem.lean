module

public import SmoothedPolygons.Defs
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.MFDeriv.Defs

/-!
# The Reinhardt optimal control problem (§3.6)

The trivialization of the tangent and cotangent bundles of a Lie group by left translation
(Proposition 3.6.1), and the Reinhardt control problem (Problem 3.6.2): admissible trajectories,
their cost, and global minimizers.
-/

@[expose] public section

namespace SmoothedPolygons

/-- **Proposition 3.6.1** (`prop:trivialization`). For a real Lie group `G` with Lie algebra
`𝔤 = T_eG`, left translation trivializes the tangent and the cotangent bundles:
`TG ≅ G × 𝔤` by `(g, v) ↦ (g, T_eL_g v)`, each `T_eL_g : 𝔤 → T_gG` being a linear isomorphism,
and `T*G ≅ G × 𝔤*` by `(g, p) ↦ (g, p ∘ T_gL_{g⁻¹})`. -/
theorem proposition3_6_1 {E H G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace G] [ChartedSpace H G]
    [Group G] {n : WithTop ℕ∞} [LieGroup I n G] (hn : 1 ≤ n) :
    (∀ g : G, Function.Bijective (mfderiv I I (fun h ↦ g * h) 1)) ∧
    Function.Bijective (fun p : G × TangentSpace I (1 : G) ↦
      (⟨p.1, mfderiv I I (fun h ↦ p.1 * h) 1 p.2⟩ : TangentBundle I G)) ∧
    Function.Bijective (fun p : G × (TangentSpace I (1 : G) →L[ℝ] ℝ) ↦
      (⟨p.1, p.2.comp (mfderiv I I (fun h ↦ p.1⁻¹ * h) p.1)⟩ :
        Σ g : G, TangentSpace I g →L[ℝ] ℝ)) := by
  sorry

/-- **Problem 3.6.2** (`pbm:reinhardt-optimal-control`). An admissible trajectory of the
Reinhardt control problem: a state trajectory on `[0, t_f]` (`g' = gX`, `X' = [Z_u, X]/⟨Z_u, X⟩`,
control in `U_T`, `X(t)` satisfying the star conditions with `det X = 1`) with the initial
condition `g(0) = I₂` and the terminal conditions `g(t_f) = R` and `X(t_f) = R⁻¹X(0)R`.

The problem prints the terminal condition as `X(t_f) = R X₀ R⁻¹`; the derivation that precedes it
(§3.5), the half-plane form (Problem 4.5.1) and the transversality conditions (§6.6) all give
`X(t_f) = R⁻¹ X₀ R`, which differs because `Ad_R` has order 3. This is a misprint, corrected
here. -/
def IsReinhardtAdmissible (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X : ℝ → Mat2) : Prop :=
  IsStateTrajectory T u g X ∧ g 0 = 1 ∧ g T = R ∧ X T = R⁻¹ * X 0 * R

/-- A global minimizer of the Reinhardt control problem (Problem 3.6.2): an admissible trajectory
whose cost `-(3/2) ∫ ⟨J, X⟩` is at most the cost of every admissible trajectory. -/
def IsReinhardtMinimizer (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X : ℝ → Mat2) : Prop :=
  IsReinhardtAdmissible T u g X ∧
    ∀ (T' : ℝ) (u' : ℝ → Fin 3 → ℝ) (g' X' : ℝ → Mat2), IsReinhardtAdmissible T' u' g' X' →
      reinhardtCost T X ≤ reinhardtCost T' X'

end SmoothedPolygons
