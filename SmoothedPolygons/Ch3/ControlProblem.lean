module

public import SmoothedPolygons.Defs
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.MFDeriv.Defs
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# The Reinhardt optimal control problem (§3.6)

The trivialization of the tangent and cotangent bundles of a Lie group by left translation
(Proposition 3.6.1), and `R⁻¹ J R = J`. The Reinhardt control problem (Problem 3.6.2), its
admissible trajectories (`IsReinhardtAdmissible`), their cost (`reinhardtCost`) and its global
minimizers (`IsReinhardtMinimizer`), is defined in `SmoothedPolygons/Defs.lean`, shared with the
Challenge's statement of Mahler's First conjecture.
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
  have hn0 : n ≠ 0 := (lt_of_lt_of_le zero_lt_one hn).ne'
  have hL : ∀ g h : G, MDifferentiableAt I I (fun x ↦ g * x) h := fun g h ↦
    (contMDiff_mul_left (I := I) (n := n) (a := g)).contMDiffAt.mdifferentiableAt hn0
  -- `T_eL_g` is an isomorphism with inverse `T_gL_{g⁻¹}`, by the chain rule applied to
  -- `L_{g⁻¹} ∘ L_g = id` and `L_g ∘ L_{g⁻¹} = id`: first `T_gL_{g⁻¹} ∘ T_eL_g = id`
  have hST : ∀ (g : G) (v : TangentSpace I (1 : G)),
      mfderiv I I (fun h ↦ g⁻¹ * h) g (mfderiv I I (fun h ↦ g * h) 1 v) = v := by
    intro g v
    have A : mfderiv I I ((fun x ↦ g⁻¹ * x) ∘ (fun x ↦ g * x)) (1 : G) =
        ContinuousLinearMap.id ℝ (TangentSpace I (1 : G)) := by
      have : (fun x ↦ g⁻¹ * x) ∘ (fun x ↦ g * x) = id := by ext x; simp
      rw [this, mfderiv_id]
    rw [mfderiv_comp (1 : G) (hL g⁻¹ _) (hL g 1)] at A
    have key : ∀ y : G, y = g → ∀ w : E,
        mfderiv I I (fun h ↦ g⁻¹ * h) y w = mfderiv I I (fun h ↦ g⁻¹ * h) g w := by
      rintro y rfl w; rfl
    exact (key _ (mul_one g) _).symm.trans (congrArg (fun L ↦ L v) A)
  -- and `T_eL_g ∘ T_gL_{g⁻¹} = id`
  have hTS : ∀ (g : G) (v : TangentSpace I g),
      mfderiv I I (fun h ↦ g * h) 1 (mfderiv I I (fun h ↦ g⁻¹ * h) g v) = v := by
    intro g v
    have A : mfderiv I I ((fun x ↦ g * x) ∘ (fun x ↦ g⁻¹ * x)) g =
        ContinuousLinearMap.id ℝ (TangentSpace I g) := by
      have : (fun x ↦ g * x) ∘ (fun x ↦ g⁻¹ * x) = id := by ext x; simp
      rw [this, mfderiv_id]
    rw [mfderiv_comp g (hL g _) (hL g⁻¹ g)] at A
    have key : ∀ y : G, y = 1 → ∀ w : E,
        mfderiv I I (fun h ↦ g * h) y w = mfderiv I I (fun h ↦ g * h) 1 w := by
      rintro y rfl w; rfl
    exact (key _ (inv_mul_cancel g) _).symm.trans (congrArg (fun L ↦ L v) A)
  refine ⟨fun g ↦ ⟨fun v w hvw ↦ ?_, fun v ↦ ⟨_, hTS g v⟩⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [← hST g v, ← hST g w, hvw]
  -- the trivialization of `TG` is bijective fiberwise
  · rintro ⟨g, v⟩ ⟨g', w⟩ h
    simp only at h
    obtain ⟨rfl, h⟩ := Bundle.TotalSpace.mk.inj h
    rw [← hST g v, ← hST g w, eq_of_heq h]
  · rintro ⟨g, v⟩
    exact ⟨(g, mfderiv I I (fun h ↦ g⁻¹ * h) g v), by simp only [hTS]⟩
  -- dually, `p ↦ p ∘ T_gL_{g⁻¹}` is a bijection `𝔤* → T*_gG`, with inverse `q ↦ q ∘ T_eL_g`
  · rintro ⟨g, φ⟩ ⟨g', ψ⟩ h
    simp only [Sigma.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
    rw [heq_iff_eq] at h
    simp only [Prod.mk.injEq, true_and]
    ext v
    rw [← hST g v]
    exact congrArg (fun L ↦ L (mfderiv I I (fun h ↦ g * h) 1 v)) h
  · rintro ⟨g, φ⟩
    refine ⟨(g, φ.comp (mfderiv I I (fun h ↦ g * h) 1)), ?_⟩
    simp only [Sigma.mk.injEq, heq_iff_eq, true_and]
    ext v
    exact congrArg φ (hTS g v)

/-- `R⁻¹ J R = J`: the rotation `R` by `π/3` commutes with the generator `J` of rotations. -/
theorem R_inv_mul_J_mul_R : R⁻¹ * J * R = J := by
  have hRJ : J * R = R * J := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [R, J, Matrix.mul_apply, Fin.sum_univ_two]
  have hdet : R.det = 1 := by
    rw [Matrix.det_fin_two]
    simp only [R, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    have := Real.mul_self_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    linear_combination (1 / 4 : ℝ) * this
  rw [Matrix.mul_assoc, hRJ, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul R (by rw [hdet]; exact isUnit_one), Matrix.one_mul]

end SmoothedPolygons
