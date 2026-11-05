module

public import SmoothedPolygons.Ch4.AdjointOrbit

/-!
# The Riemannian metric on the coadjoint orbit (Appendix A.11)
-/

@[expose] public section

namespace SmoothedPolygons

/-- **Lemma A.11.1** (`lem:riemannian`). The symmetric bilinear form on `T_z𝔥` determined by the
trace form on `𝔭_X = X^⊥ ≅ T_X O_J` (via `r ↦ [Y_z(r), X]`, Lemma 4.2.4) is twice the invariant
Riemannian metric of the upper half-plane: `⟨[Y_z(r), X], [Y_z(r'), X]⟩ = 2(r₁r₁' + r₂r₂')/y²`. -/
theorem lemmaA_11_1 (x y r₁ r₂ r₁' r₂' : ℝ) (hy : 0 < y) :
    traceForm (tangentLift x y r₁ r₂ * Φ x y - Φ x y * tangentLift x y r₁ r₂)
        (tangentLift x y r₁' r₂' * Φ x y - Φ x y * tangentLift x y r₁' r₂') =
      2 * (r₁ * r₁' + r₂ * r₂') / y ^ 2 := by
  have hy0 : y ≠ 0 := hy.ne'
  -- the images `ẽ₁, ẽ₂` of the basis `∂/∂x, ∂/∂y` under `r ↦ Y_z(r)`
  set e₁ : Mat2 := !![0, 1; 0, 0] with he₁
  set e₂ : Mat2 := !![1 / (2 * y), -x / y; 0, -1 / (2 * y)] with he₂
  set X := Φ x y with hX
  have hY : ∀ r₁ r₂, tangentLift x y r₁ r₂ * X - X * tangentLift x y r₁ r₂ =
      r₁ • (e₁ * X - X * e₁) + r₂ • (e₂ * X - X * e₂) := by
    intro r₁ r₂
    have : tangentLift x y r₁ r₂ = r₁ • e₁ + r₂ • e₂ := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [tangentLift, e₁, e₂] <;> field_simp; ring
    rw [this, add_mul, mul_add, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, mul_smul_comm,
      smul_sub, smul_sub]
    abel
  have h11 : traceForm (e₁ * X - X * e₁) (e₁ * X - X * e₁) = 2 / y ^ 2 := by
    simp [traceForm, X, Φ, e₁, Matrix.trace_fin_two]; field_simp; ring
  have h12 : traceForm (e₁ * X - X * e₁) (e₂ * X - X * e₂) = 0 := by
    simp [traceForm, X, Φ, e₁, e₂, Matrix.trace_fin_two]; field_simp; ring
  have h21 : traceForm (e₂ * X - X * e₂) (e₁ * X - X * e₁) = 0 := by
    simp [traceForm, X, Φ, e₁, e₂, Matrix.trace_fin_two]; field_simp; ring
  have h22 : traceForm (e₂ * X - X * e₂) (e₂ * X - X * e₂) = 2 / y ^ 2 := by
    simp [traceForm, X, Φ, e₂, Matrix.trace_fin_two]; field_simp; ring
  simp only [traceForm] at h11 h12 h21 h22 ⊢
  rw [hY, hY]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, Matrix.trace_add, Matrix.trace_smul,
    smul_eq_mul, h11, h12, h21, h22]
  ring

end SmoothedPolygons
