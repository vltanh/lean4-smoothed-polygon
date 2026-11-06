module

public import SmoothedPolygons.Ch7.Isolated.Poincare
public import SmoothedPolygons.Ch7.SmoothedPolygon
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Theorem 7.7.1, step 5: the direct calculation (hyperbolicity)

The derivative of the Poincaré map on the tangent space of the section at the octagon's point has
the explicit matrix `iso_sectionMatrix` in the basis `iso_sectionBasis` (`iso_fderiv_basis`, in
`SmoothedPolygons.Ch7.Isolated.Poincare`), with reciprocal
characteristic polynomial `z⁴ - e₁z³ + e₂z² - e₁z + 1`; the certified inequalities `-e₁ > 4` and
`2 + 2e₁ + e₂ > 0` show that it has no eigenvalue of modulus `1`.

## The proofs

* *The tangent space.* The constraint map `iso_sectionConstraints` is written out in coordinates
  (`ihy_sectionConstraints_eq`) and differentiated (`ihy_fderiv_sectionConstraints`); at
  `q_oct = q_fix(y₀)` (`ihy_phaseCoords_qFix`: `Λ₁(0) = λ₁Λ₁₀`, `Λ_R(0) = λ_R[[0, y₀²], [1, 0]]`)
  the basis vectors satisfy the five linearized constraints by direct substitution of `λ₁`, `λ_R`
  (`iso_sectionBasis_mem`). The constraints can be solved for `δX₁₀`, `δΛ₁₁₀`, `δΛ_R₀₀`, `δΛ_R₀₁`,
  `δΛ_R₁₀` (this uses `λ₁ ≠ 0` at the octagon), so a tangent vector is determined by its
  coordinates `δX₀₀, δX₀₁, δΛ₁₀₀, δΛ₁₀₁` (`ihy_tangentSection_eq_zero`): the tangent space is
  four-dimensional and spanned by `iso_sectionBasis` (`ihy_tangentSection_eq_sum`).
* *The characteristic polynomial.* For a `4 × 4` matrix, `χ = X⁴ - (tr)X³ + E₂X² - E₃X + det`
  with `E₂`, `E₃` the sums of the principal `2 × 2` and `3 × 3` minors (`ihy_charpoly_fin_four`).
  Clearing the common denominator `Q = 48u³(3u + 1)²(3Lu + L + 3u - 3)` of `iso_sectionMatrix`
  (`ihy_sectionMatrix_eq`), the four identities `tr = e₁`, `E₂ = e₂`, `E₃ = e₁`, `det = 1` become
  polynomial identities in `(u, L)`, checked by `ring` (`iso_sectionMatrix_charpoly`).
* *Hyperbolicity.* Writing `v = Σ cᵢbᵢ`, the derivative acts on `c` by `iso_sectionMatrix`
  (`iso_fderiv_basis`), so `A²v - 2cos θ Av + v = 0` gives `(M² - 2cos θ M + 1)c = 0` by linear
  independence, and `c = 0` by `iso_sectionMatrix_octagon_hyperbolic` (`iso_hyperbolic`).
-/

@[expose] public section

namespace SmoothedPolygons

open Matrix Set Filter Topology MeasureTheory

/-! ### The characteristic polynomial of a `4 × 4` matrix -/

/-- The sum of the principal `2 × 2` minors of a `4 × 4` matrix. -/
def ihy_minors2 (M : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  M 0 0 * M 1 1 - M 0 1 * M 1 0 + M 0 0 * M 2 2 - M 0 2 * M 2 0 + M 0 0 * M 3 3 - M 0 3 * M 3 0 +
    M 1 1 * M 2 2 - M 1 2 * M 2 1 + M 1 1 * M 3 3 - M 1 3 * M 3 1 + M 2 2 * M 3 3 - M 2 3 * M 3 2

/-- The sum of the principal `3 × 3` minors of a `4 × 4` matrix. -/
def ihy_minors3 (M : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  (M 0 0 * M 1 1 * M 2 2 - M 0 0 * M 1 2 * M 2 1 - M 0 1 * M 1 0 * M 2 2 + M 0 1 * M 1 2 * M 2 0 +
      M 0 2 * M 1 0 * M 2 1 - M 0 2 * M 1 1 * M 2 0) +
    (M 0 0 * M 1 1 * M 3 3 - M 0 0 * M 1 3 * M 3 1 - M 0 1 * M 1 0 * M 3 3 +
      M 0 1 * M 1 3 * M 3 0 + M 0 3 * M 1 0 * M 3 1 - M 0 3 * M 1 1 * M 3 0) +
    (M 0 0 * M 2 2 * M 3 3 - M 0 0 * M 2 3 * M 3 2 - M 0 2 * M 2 0 * M 3 3 +
      M 0 2 * M 2 3 * M 3 0 + M 0 3 * M 2 0 * M 3 2 - M 0 3 * M 2 2 * M 3 0) +
    (M 1 1 * M 2 2 * M 3 3 - M 1 1 * M 2 3 * M 3 2 - M 1 2 * M 2 1 * M 3 3 +
      M 1 2 * M 2 3 * M 3 1 + M 1 3 * M 2 1 * M 3 2 - M 1 3 * M 2 2 * M 3 1)

open Polynomial in
/-- The characteristic polynomial of a `4 × 4` matrix from its trace, the sums of its principal
`2 × 2` and `3 × 3` minors, and its determinant. -/
theorem ihy_charpoly_fin_four (M : Matrix (Fin 4) (Fin 4) ℝ) :
    M.charpoly = X ^ 4 - C (M 0 0 + M 1 1 + M 2 2 + M 3 3) * X ^ 3 + C (ihy_minors2 M) * X ^ 2 -
      C (ihy_minors3 M) * X + C M.det := by
  have h00 : Fin.succAbove (0 : Fin 4) (0 : Fin 3) = 1 := rfl
  have h01 : Fin.succAbove (0 : Fin 4) (1 : Fin 3) = 2 := rfl
  have h02 : Fin.succAbove (0 : Fin 4) (2 : Fin 3) = 3 := rfl
  have h10 : Fin.succAbove (1 : Fin 4) (0 : Fin 3) = 0 := rfl
  have h11 : Fin.succAbove (1 : Fin 4) (1 : Fin 3) = 2 := rfl
  have h12 : Fin.succAbove (1 : Fin 4) (2 : Fin 3) = 3 := rfl
  have h20 : Fin.succAbove (2 : Fin 4) (0 : Fin 3) = 0 := rfl
  have h21 : Fin.succAbove (2 : Fin 4) (1 : Fin 3) = 1 := rfl
  have h22 : Fin.succAbove (2 : Fin 4) (2 : Fin 3) = 3 := rfl
  have h30 : Fin.succAbove (3 : Fin 4) (0 : Fin 3) = 0 := rfl
  have h31 : Fin.succAbove (3 : Fin 4) (1 : Fin 3) = 1 := rfl
  have h32 : Fin.succAbove (3 : Fin 4) (2 : Fin 3) = 2 := rfl
  rw [Matrix.charpoly, Matrix.det_succ_row_zero, Matrix.det_succ_row_zero M, ihy_minors2,
    ihy_minors3]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.det_fin_three, Matrix.submatrix_apply,
    charmatrix_apply, Matrix.diagonal_apply]
  simp only [Fin.succAbove_zero, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.val_zero,
    Fin.val_succ, Fin.val_one, Fin.val_two]
  simp only [Fin.isValue, Fin.reduceSucc, h10, h11, h12, h20, h21, h22, h30, h31, h32]
  simp only [Fin.isValue, Fin.reduceEq, ite_true, ite_false]
  simp only [map_add, map_sub, map_mul, map_neg, map_one, map_zero, map_pow]
  ring

/-- The `4 × 4` determinant, expanded. -/
theorem ihy_det_fin_four (M : Matrix (Fin 4) (Fin 4) ℝ) :
    M.det = M 0 0 * M 1 1 * M 2 2 * M 3 3 - M 0 0 * M 1 1 * M 2 3 * M 3 2 -
      M 0 0 * M 1 2 * M 2 1 * M 3 3 + M 0 0 * M 1 2 * M 2 3 * M 3 1 +
      M 0 0 * M 1 3 * M 2 1 * M 3 2 - M 0 0 * M 1 3 * M 2 2 * M 3 1 -
      M 0 1 * M 1 0 * M 2 2 * M 3 3 + M 0 1 * M 1 0 * M 2 3 * M 3 2 +
      M 0 1 * M 1 2 * M 2 0 * M 3 3 - M 0 1 * M 1 2 * M 2 3 * M 3 0 -
      M 0 1 * M 1 3 * M 2 0 * M 3 2 + M 0 1 * M 1 3 * M 2 2 * M 3 0 +
      M 0 2 * M 1 0 * M 2 1 * M 3 3 - M 0 2 * M 1 0 * M 2 3 * M 3 1 -
      M 0 2 * M 1 1 * M 2 0 * M 3 3 + M 0 2 * M 1 1 * M 2 3 * M 3 0 +
      M 0 2 * M 1 3 * M 2 0 * M 3 1 - M 0 2 * M 1 3 * M 2 1 * M 3 0 -
      M 0 3 * M 1 0 * M 2 1 * M 3 2 + M 0 3 * M 1 0 * M 2 2 * M 3 1 +
      M 0 3 * M 1 1 * M 2 0 * M 3 2 - M 0 3 * M 1 1 * M 2 2 * M 3 0 -
      M 0 3 * M 1 2 * M 2 0 * M 3 1 + M 0 3 * M 1 2 * M 2 1 * M 3 0 := by
  have h10 : Fin.succAbove (1 : Fin 4) (0 : Fin 3) = 0 := rfl
  have h11 : Fin.succAbove (1 : Fin 4) (1 : Fin 3) = 2 := rfl
  have h12 : Fin.succAbove (1 : Fin 4) (2 : Fin 3) = 3 := rfl
  have h20 : Fin.succAbove (2 : Fin 4) (0 : Fin 3) = 0 := rfl
  have h21 : Fin.succAbove (2 : Fin 4) (1 : Fin 3) = 1 := rfl
  have h22 : Fin.succAbove (2 : Fin 4) (2 : Fin 3) = 3 := rfl
  have h30 : Fin.succAbove (3 : Fin 4) (0 : Fin 3) = 0 := rfl
  have h31 : Fin.succAbove (3 : Fin 4) (1 : Fin 3) = 1 := rfl
  have h32 : Fin.succAbove (3 : Fin 4) (2 : Fin 3) = 2 := rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.det_fin_three, Matrix.submatrix_apply]
  simp only [Fin.succAbove_zero, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.val_zero,
    Fin.val_succ, Fin.val_one, Fin.val_two]
  simp only [Fin.isValue, Fin.reduceSucc, h10, h11, h12, h20, h21, h22, h30, h31, h32]
  ring

open Polynomial in
/-- The characteristic polynomial of `c • K` from the four invariants of `K`. -/
theorem ihy_charpoly_smul (K : Matrix (Fin 4) (Fin 4) ℝ) (c e₁ e₂ : ℝ)
    (h1 : c * (K 0 0 + K 1 1 + K 2 2 + K 3 3) = e₁) (h2 : c ^ 2 * ihy_minors2 K = e₂)
    (h3 : c ^ 3 * ihy_minors3 K = e₁) (h4 : c ^ 4 * K.det = 1) :
    (c • K).charpoly = X ^ 4 - C e₁ * X ^ 3 + C e₂ * X ^ 2 - C e₁ * X + 1 := by
  have k1 : (c • K) 0 0 + (c • K) 1 1 + (c • K) 2 2 + (c • K) 3 3 = e₁ := by
    simp only [Matrix.smul_apply, smul_eq_mul]; rw [← h1]; ring
  have k2 : ihy_minors2 (c • K) = e₂ := by
    simp only [ihy_minors2, Matrix.smul_apply, smul_eq_mul]; rw [← h2, ihy_minors2]; ring
  have k3 : ihy_minors3 (c • K) = e₁ := by
    simp only [ihy_minors3, Matrix.smul_apply, smul_eq_mul]; rw [← h3, ihy_minors3]; ring
  have k4 : (c • K).det = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin, h4]
  rw [ihy_charpoly_fin_four, k1, k2, k3, k4, map_one]

/-- `iso_sectionMatrix` with its common denominator `48u³(3u + 1)²(3Lu + L + 3u - 3)` cleared. -/
noncomputable def ihy_sectionNum (u L : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![24*u^2*(81*L*u^4 + 162*L*u^3 - 12*L*u^2 - 10*L*u + 3*L + 216*u^4 - 243*u^3 - 3*u^2 + 39*u - 9),
    192*u^2*(6*L*u^2 - L*u - L + 9*u^3 - 12*u^2 + 3), -1728*u^4*(u - 1), -576*u^3*(u - 1);
    72*u^3*(135*L*u^4 + 216*L*u^3 + 6*L*u^2 - 8*L*u + 3*L + 270*u^4 - 261*u^3 - 33*u^2 + 33*u - 9),
    48*u^3*(27*L*u^3 + 99*L*u^2 - 3*L*u - 11*L + 135*u^3 - 153*u^2 - 15*u + 33),
    -5184*u^5*(u - 1), -1728*u^4*(u - 1);
    3*(u - 1)*(3*L*u + L - 6*u - 3)*(135*L*u^5 + 261*L*u^4 + 126*L*u^3 - 6*L*u^2 - 5*L*u + L +
      270*u^5 - 171*u^4 - 72*u^3 - 42*u^2 + 18*u - 3),
    8*(u - 1)*(3*L*u + L - 6*u - 3)*(18*L*u^3 + 15*L*u^2 - L + 27*u^4 - 27*u^3 - 3*u + 3),
    -24*u^2*(81*L*u^4 + 18*L*u^3 - 36*L*u^2 - 2*L*u + 3*L + 45*u^3 - 51*u^2 + 15*u - 9),
    -24*u*(45*L*u^4 + 24*L*u^3 - 6*L*u^2 + L + 18*u^4 + 9*u^3 - 27*u^2 + 3*u - 3);
    48*u^2*(u - 1)*(3*u - 1)*(3*L*u + L - 6*u - 3)*(3*L*u + L + 3*u - 3),
    96*u^2*(u - 1)*(3*L*u + L - 6*u - 3)*(3*L*u + L + 3*u - 3),
    1152*u^4*(3*L*u + L + 3*u - 3), -48*u^3*(9*u^2 + 6*u - 7)*(3*L*u + L + 3*u - 3)]

/-- `iso_sectionMatrix = Q⁻¹ • ihy_sectionNum`, `Q = 48u³(3u + 1)²(3Lu + L + 3u - 3)`. -/
theorem ihy_sectionMatrix_eq (u L : ℝ) (hu : 0 < u) (hL : 3 * L * u + L + 3 * u - 3 ≠ 0) :
    iso_sectionMatrix u L =
      (48 * u ^ 3 * (3 * u + 1) ^ 2 * (3 * L * u + L + 3 * u - 3))⁻¹ • ihy_sectionNum u L := by
  have h1 : 3 * u + 1 ≠ 0 := by positivity
  have hu0 : u ≠ 0 := hu.ne'
  have hQ : 48 * u ^ 3 * (3 * u + 1) ^ 2 * (3 * L * u + L + 3 * u - 3) ≠ 0 := by positivity
  have hL' : (u * 3 + 1) * L + u * 3 - 3 ≠ 0 := by convert hL using 1; ring
  rw [eq_inv_smul_iff₀ hQ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [iso_sectionMatrix, ihy_sectionNum] <;> field_simp <;> ring

/-! ### The tangent space of the section: the linearized constraints -/

/-- The constraint map in coordinates: `det X - 1`, `⟨X, Λ_R⟩`, `H(e₃)` (with
`⟨Λ_R, Z_{e₃}⟩/⟨X, Z_{e₃}⟩`, both written as linear forms), `χ₂₃` and `det Λ₁`. -/
theorem ihy_sectionConstraints_eq (v : Fin 9 → ℝ) :
    iso_sectionConstraints v =
      ![-(v 0 * v 0) - v 1 * v 2 - 1, 2 * (v 0 * v 6) + v 1 * v 8 + v 2 * v 7,
        2 * (v 0 * v 3) + (v 4 - 3 / 2) * v 2 + (v 5 + 3 / 2) * v 1 -
          (-(2 / √3) * v 6 - 2 / 3 * v 8) * (-(2 / √3) * v 0 - 2 / 3 * v 2)⁻¹,
        (-(2 / √3) * v 6 - 2 / 3 * v 8) * (-(2 / √3) * v 0 - 2 / 3 * v 2)⁻¹ -
          (2 / √3 * v 6 - 2 / 3 * v 8) * (2 / √3 * v 0 - 2 / 3 * v 2)⁻¹,
        -(v 3 * v 3) - v 4 * v 5] := by
  funext k
  fin_cases k <;>
    simp [iso_sectionConstraints, iso_phaseOfCoords, traceForm, hamiltonian, switchingFn,
      controlP, controlMatrix, vertex, Matrix.det_fin_two, Matrix.trace_fin_two, J] <;>
    ring

/-- The differential of the constraint map at a point where `⟨X, Z_{e₃}⟩ ≠ 0 ≠ ⟨X, Z_{e₂}⟩`. -/
theorem ihy_fderiv_sectionConstraints (p w : Fin 9 → ℝ) (hA : -(2 / √3) * p 0 - 2 / 3 * p 2 ≠ 0)
    (hB : 2 / √3 * p 0 - 2 / 3 * p 2 ≠ 0) :
    fderiv ℝ iso_sectionConstraints p w =
      ![-2 * p 0 * w 0 - p 1 * w 2 - p 2 * w 1,
        2 * p 0 * w 6 + 2 * p 6 * w 0 + p 1 * w 8 + p 8 * w 1 + p 2 * w 7 + p 7 * w 2,
        2 * p 0 * w 3 + 2 * p 3 * w 0 + (p 4 - 3 / 2) * w 2 + p 2 * w 4 + (p 5 + 3 / 2) * w 1 +
          p 1 * w 5 - ((-(2 / √3) * w 6 - 2 / 3 * w 8) * (-(2 / √3) * p 0 - 2 / 3 * p 2) -
            (-(2 / √3) * p 6 - 2 / 3 * p 8) * (-(2 / √3) * w 0 - 2 / 3 * w 2)) /
            (-(2 / √3) * p 0 - 2 / 3 * p 2) ^ 2,
        ((-(2 / √3) * w 6 - 2 / 3 * w 8) * (-(2 / √3) * p 0 - 2 / 3 * p 2) -
            (-(2 / √3) * p 6 - 2 / 3 * p 8) * (-(2 / √3) * w 0 - 2 / 3 * w 2)) /
            (-(2 / √3) * p 0 - 2 / 3 * p 2) ^ 2 -
          ((2 / √3 * w 6 - 2 / 3 * w 8) * (2 / √3 * p 0 - 2 / 3 * p 2) -
            (2 / √3 * p 6 - 2 / 3 * p 8) * (2 / √3 * w 0 - 2 / 3 * w 2)) /
            (2 / √3 * p 0 - 2 / 3 * p 2) ^ 2,
        -2 * p 3 * w 3 - p 4 * w 5 - p 5 * w 4] := by
  have hP : ∀ i, HasFDerivAt (fun v : Fin 9 → ℝ ↦ v i)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 9 ↦ ℝ) i) p :=
    fun i ↦ hasFDerivAt_apply i p
  have hlA : HasFDerivAt (fun v : Fin 9 → ℝ ↦ -(2 / √3) * v 0 - 2 / 3 * v 2) _ p :=
    ((hP 0).const_mul _).fun_sub ((hP 2).const_mul _)
  have hlB : HasFDerivAt (fun v : Fin 9 → ℝ ↦ 2 / √3 * v 0 - 2 / 3 * v 2) _ p :=
    ((hP 0).const_mul _).fun_sub ((hP 2).const_mul _)
  have hN3 : HasFDerivAt (fun v : Fin 9 → ℝ ↦ -(2 / √3) * v 6 - 2 / 3 * v 8) _ p :=
    ((hP 6).const_mul _).fun_sub ((hP 8).const_mul _)
  have hN2 : HasFDerivAt (fun v : Fin 9 → ℝ ↦ 2 / √3 * v 6 - 2 / 3 * v 8) _ p :=
    ((hP 6).const_mul _).fun_sub ((hP 8).const_mul _)
  have hiA : HasFDerivAt (fun v : Fin 9 → ℝ ↦ (-(2 / √3) * v 0 - 2 / 3 * v 2)⁻¹) _ p :=
    (hasDerivAt_inv hA).comp_hasFDerivAt p hlA
  have hiB : HasFDerivAt (fun v : Fin 9 → ℝ ↦ (2 / √3 * v 0 - 2 / 3 * v 2)⁻¹) _ p :=
    (hasDerivAt_inv hB).comp_hasFDerivAt p hlB
  have h0 : HasFDerivAt (fun v : Fin 9 → ℝ ↦ -(v 0 * v 0) - v 1 * v 2 - 1) _ p :=
    (((hP 0).fun_mul (hP 0)).fun_neg.fun_sub ((hP 1).fun_mul (hP 2))).sub_const 1
  have h1 : HasFDerivAt (fun v : Fin 9 → ℝ ↦ 2 * (v 0 * v 6) + v 1 * v 8 + v 2 * v 7) _ p :=
    ((((hP 0).fun_mul (hP 6)).const_mul 2).fun_add ((hP 1).fun_mul (hP 8))).fun_add
      ((hP 2).fun_mul (hP 7))
  have h2 : HasFDerivAt (fun v : Fin 9 → ℝ ↦ 2 * (v 0 * v 3) + (v 4 - 3 / 2) * v 2 +
      (v 5 + 3 / 2) * v 1 - (-(2 / √3) * v 6 - 2 / 3 * v 8) * (-(2 / √3) * v 0 - 2 / 3 * v 2)⁻¹)
      _ p :=
    (((((hP 0).fun_mul (hP 3)).const_mul 2).fun_add (((hP 4).sub_const _).fun_mul (hP 2))).fun_add
      (((hP 5).add_const _).fun_mul (hP 1))).fun_sub (hN3.fun_mul hiA)
  have h3 : HasFDerivAt (fun v : Fin 9 → ℝ ↦
      (-(2 / √3) * v 6 - 2 / 3 * v 8) * (-(2 / √3) * v 0 - 2 / 3 * v 2)⁻¹ -
        (2 / √3 * v 6 - 2 / 3 * v 8) * (2 / √3 * v 0 - 2 / 3 * v 2)⁻¹) _ p :=
    (hN3.fun_mul hiA).fun_sub (hN2.fun_mul hiB)
  have h4 : HasFDerivAt (fun v : Fin 9 → ℝ ↦ -(v 3 * v 3) - v 4 * v 5) _ p :=
    ((hP 3).fun_mul (hP 3)).fun_neg.fun_sub ((hP 4).fun_mul (hP 5))
  have hF : iso_sectionConstraints = fun v k ↦ ![-(v 0 * v 0) - v 1 * v 2 - 1,
      2 * (v 0 * v 6) + v 1 * v 8 + v 2 * v 7,
      2 * (v 0 * v 3) + (v 4 - 3 / 2) * v 2 + (v 5 + 3 / 2) * v 1 -
        (-(2 / √3) * v 6 - 2 / 3 * v 8) * (-(2 / √3) * v 0 - 2 / 3 * v 2)⁻¹,
      (-(2 / √3) * v 6 - 2 / 3 * v 8) * (-(2 / √3) * v 0 - 2 / 3 * v 2)⁻¹ -
        (2 / √3 * v 6 - 2 / 3 * v 8) * (2 / √3 * v 0 - 2 / 3 * v 2)⁻¹,
      -(v 3 * v 3) - v 4 * v 5] k := by
    funext v k; rw [ihy_sectionConstraints_eq]
  rw [hF, fderiv_pi]
  · funext k
    simp only [ContinuousLinearMap.pi_apply]
    fin_cases k
    · simp only [Fin.zero_eta, Matrix.cons_val_zero]
      rw [h0.fderiv]
      simp
      ring
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [h1.fderiv]
      simp
      ring
    · simp only [Fin.reduceFinMk, Matrix.cons_val]
      rw [h2.fderiv]
      simp
      field_simp
      ring
    · simp only [Fin.reduceFinMk, Matrix.cons_val]
      rw [h3.fderiv]
      simp
      field_simp
      ring
    · simp only [Fin.reduceFinMk, Matrix.cons_val]
      rw [h4.fderiv]
      simp
      ring
  · intro k
    fin_cases k
    exacts [h0.differentiableAt, h1.differentiableAt, h2.differentiableAt, h3.differentiableAt,
      h4.differentiableAt]

/-- `q_fix(y₀)` in coordinates. -/
theorem ihy_phaseCoords_qFix (y0 : ℝ) (hy0 : 0 < y0) :
    iso_phaseCoords (iso_qFix y0) =
      ![0, -y0, 1 / y0, 0, strongL₁ y0 * ((2 * y0 ^ 2 * (1 + 3 * y0 ^ 2))⁻¹ * (4 * √3 * y0 ^ 4)),
        strongL₁ y0 * ((2 * y0 ^ 2 * (1 + 3 * y0 ^ 2))⁻¹ * -(√3 * (1 + y0 ^ 2) * (3 * y0 ^ 2 - 1))),
        0, strongLR y0 * y0 ^ 2, strongLR y0] := by
  have hΛR0 : strongΛR y0 0 = strongLR y0 • !![0, y0 ^ 2; 1, 0] :=
    (costateΛR_solution y0 _ _ _ hy0 0).2
  have hΛ10 : strongΛ₁ y0 0 = strongL₁ y0 • Λ₁₀ y0 := by
    rw [strongΛ₁, str_segG_zero y0 hy0, inv_one, one_mul, mul_one]
  have hY : 0 < 1 + 3 * y0 ^ 2 := by positivity
  rw [iso_phaseCoords, iso_qFix, hΛR0, hΛ10]
  funext i
  fin_cases i <;> simp [Φ, Λ₁₀]
  field_simp

/-- The two denominators `⟨X, Z_{e₃}⟩`, `⟨X, Z_{e₂}⟩` of the constraints at `q_oct`. -/
lemma ihy_qFix_den :
    -(2 / √3) * iso_phaseCoords (iso_qFix (y₀ 1)) 0 - 2 / 3 * iso_phaseCoords (iso_qFix (y₀ 1)) 2 ≠
        0 ∧
      2 / √3 * iso_phaseCoords (iso_qFix (y₀ 1)) 0 - 2 / 3 * iso_phaseCoords (iso_qFix (y₀ 1)) 2 ≠
        0 := by
  have hy : 0 < y₀ 1 := poly_y0_pos (poly_y₀_mem le_rfl).1
  rw [ihy_phaseCoords_qFix _ hy]
  constructor <;>
    simp only [one_div, _root_.mul_inv_rev, mul_neg, Fin.isValue, cons_val_zero, mul_zero,
      cons_val, zero_sub, ne_eq, neg_eq_zero, mul_eq_zero, div_eq_zero_iff, OfNat.ofNat_ne_zero,
      or_self, inv_eq_zero, false_or] <;>
    positivity

/-! ### Step 5: the derivative of the Poincaré map in a basis of the section -/

/-- `iso_sectionBasis` is a basis of the tangent space of the section at `q_oct`. -/
theorem iso_sectionBasis_mem (j : Fin 4) :
    iso_sectionBasis (y₀ 1) (ellSw (y₀ 1)) j ∈ iso_tangentSection := by
  have hy : 0 < y₀ 1 := poly_y0_pos (poly_y₀_mem le_rfl).1
  obtain ⟨hA, hB⟩ := ihy_qFix_den
  rw [iso_tangentSection, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    ihy_fderiv_sectionConstraints _ _ hA hB, ihy_phaseCoords_qFix _ hy]
  generalize y₀ 1 = y at hy ⊢
  have hY : 0 < 1 + 3 * y ^ 2 := by positivity
  have hY' : 0 < 3 * y ^ 2 + 1 := by positivity
  funext k
  fin_cases j <;> fin_cases k <;>
    simp only [iso_sectionBasis, strongL₁, strongLR, Matrix.cons_val, Fin.reduceFinMk, Fin.zero_eta,
      Fin.mk_one, Pi.zero_apply, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    field_simp <;> ring_nf

/-- The basis vectors are linearly independent: their coordinates `δX₀₀, δX₀₁, δΛ₁₀₀, δΛ₁₀₁`
are `1, √3/3, 1/y₀, √3/(3y₀)` times the standard basis. -/
theorem iso_sectionBasis_linearIndependent :
    LinearIndependent ℝ (iso_sectionBasis (y₀ 1) (ellSw (y₀ 1))) := by
  have hy : 0 < y₀ 1 := poly_y0_pos (poly_y₀_mem le_rfl).1
  generalize y₀ 1 = y at hy ⊢
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have e0 := congrFun hg 0
  have e1 := congrFun hg 1
  have e3 := congrFun hg 3
  have e4 := congrFun hg 4
  simp only [iso_sectionBasis, neg_add_rev, neg_sub, neg_mul, one_div, Fin.isValue,
    Finset.sum_apply, Pi.smul_apply, cons_val', cons_val_zero, cons_val_fin_one, smul_eq_mul,
    Fin.sum_univ_four, mul_one, cons_val_one, mul_zero, add_zero, cons_val, Pi.zero_apply, zero_add,
    mul_eq_zero, div_eq_zero_iff, Nat.ofNat_nonneg, Real.sqrt_eq_zero, OfNat.ofNat_ne_zero, or_self,
    or_false, inv_eq_zero, false_or] at e0 e1 e3 e4
  intro i
  fin_cases i
  exacts [e0, e1, e3.resolve_right hy.ne', e4.resolve_right hy.ne']

open Polynomial in
/-- The characteristic polynomial of `iso_sectionMatrix` is reciprocal,
`z⁴ - e₁ z³ + e₂ z² - e₁ z + 1` (the Poincaré map is symplectic); an identity of rational
functions in `(u, L)` (checked exactly with sympy). -/
theorem iso_sectionMatrix_charpoly (u L : ℝ) (hu : 0 < u) (hL : 3 * L * u + L + 3 * u - 3 ≠ 0) :
    (iso_sectionMatrix u L).charpoly =
      X ^ 4 - C (iso_sectionE1 u L) * X ^ 3 + C (iso_sectionE2 u L) * X ^ 2 -
        C (iso_sectionE1 u L) * X + 1 := by
  have h1 : 3 * u + 1 ≠ 0 := by positivity
  have hu0 : u ≠ 0 := hu.ne'
  have hQ : 48 * u ^ 3 * (3 * u + 1) ^ 2 * (3 * L * u + L + 3 * u - 3) ≠ 0 := by positivity
  have hY : 1 + 3 * u ≠ 0 := by positivity
  have hD : L * (1 + 3 * u) + (1 + 3 * u) - 4 ≠ 0 := by convert hL using 1; ring
  rw [ihy_sectionMatrix_eq u L hu hL]
  apply ihy_charpoly_smul
  · rw [iso_sectionE1, inv_mul_eq_div, div_eq_div_iff hQ (by positivity)]
    simp only [ihy_sectionNum, Matrix.of_apply, Matrix.cons_val]
    ring
  · rw [iso_sectionE2, inv_pow, inv_mul_eq_div, div_eq_div_iff (by positivity) (by positivity)]
    simp only [ihy_minors2, ihy_sectionNum, Matrix.of_apply, Matrix.cons_val]
    ring
  · rw [iso_sectionE1, inv_pow, inv_mul_eq_div, div_eq_div_iff (by positivity) (by positivity)]
    simp only [ihy_minors3, ihy_sectionNum, Matrix.of_apply, Matrix.cons_val]
    ring
  · rw [ihy_det_fin_four, inv_pow, inv_mul_eq_div, div_eq_one_iff_eq (by positivity)]
    simp only [ihy_sectionNum, Matrix.of_apply, Matrix.cons_val]
    ring


open Polynomial in
/-- For a `4 × 4` matrix with reciprocal characteristic polynomial `z⁴ - e₁z³ + e₂z² - e₁z + 1`,
`det(M² - cM + 1) = p(c)²` with `p(w) = w² - e₁w + e₂ - 2` (the resultant of the characteristic
polynomial and `z² - cz + 1`: `χ(α) = α² p(α + 1/α)` at the roots `α, 1/α` of `z² - cz + 1`). -/
theorem iso_det_quadratic (M : Matrix (Fin 4) (Fin 4) ℝ) (e₁ e₂ : ℝ)
    (hM : M.charpoly = X ^ 4 - C e₁ * X ^ 3 + C e₂ * X ^ 2 - C e₁ * X + 1) (c : ℝ) :
    (M ^ 2 - c • M + 1).det = (c ^ 2 - e₁ * c + e₂ - 2) ^ 2 := by
  apply Complex.ofReal_injective
  set N : Matrix (Fin 4) (Fin 4) ℂ := Complex.ofRealHom.mapMatrix M with hN
  have hdet : ((M ^ 2 - c • M + 1).det : ℂ) = (N ^ 2 - (c : ℂ) • N + 1).det := by
    have := RingHom.map_det Complex.ofRealHom (M ^ 2 - c • M + 1)
    rw [Complex.ofRealHom_eq_coe] at this
    rw [this, map_add, map_sub, map_pow, map_one]
    congr 3
    ext i j
    simp [hN]
  have hcp : N.charpoly =
      X ^ 4 - C (e₁ : ℂ) * X ^ 3 + C (e₂ : ℂ) * X ^ 2 - C (e₁ : ℂ) * X + 1 := by
    rw [hN, RingHom.mapMatrix_apply, Matrix.charpoly_map, hM]
    simp
  -- `det(N - z) = χ(z)`
  have hev : ∀ z : ℂ, (N - z • 1).det = z ^ 4 - e₁ * z ^ 3 + e₂ * z ^ 2 - e₁ * z + 1 := by
    intro z
    have h1 := Matrix.eval_charpoly N z
    rw [hcp] at h1
    simp only [eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_C, eval_one,
      scalar_apply] at h1
    rw [show N - z • 1 = -(Matrix.scalar (Fin 4) z - N) by
      rw [Matrix.scalar_apply, neg_sub, Matrix.smul_one_eq_diagonal]]
    rw [Matrix.det_neg, Matrix.scalar_apply, ← h1]
    simp only [Fintype.card_fin]
    ring
  -- the roots `α, β = 1/α` of `z² - cz + 1`
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq ((c : ℂ) ^ 2 - 4) (by norm_num : 0 < 2)
  set α : ℂ := ((c : ℂ) + w) / 2 with hα
  set β : ℂ := (c : ℂ) - α with hβ
  have hαq : α ^ 2 - (c : ℂ) * α + 1 = 0 := by
    rw [hα]; linear_combination hw / 4
  have hfac : N ^ 2 - (c : ℂ) • N + 1 = (N - α • 1) * (N - β • 1) := by
    have hαβ : α * β = 1 := by rw [hβ]; linear_combination -hαq
    have hsum : α + β = c := by rw [hβ]; ring
    rw [sub_mul, mul_sub, mul_sub]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.one_mul, smul_smul,
      mul_comm β α, hαβ, one_smul]
    rw [← hsum, add_smul, sq]
    abel
  -- `χ(α) χ(β) = p(c)²`
  rw [hdet, hfac, Matrix.det_mul, hev, hev, hβ]
  push_cast
  linear_combination (α ^ 6 - 3*α^5*c + 3*α^4*c^2 + α^4*c*e₁ - α^4*e₁^2 + 2*α^4*e₂ - α^4 -
    α^3*c^3 - 2*α^3*c^2*e₁ + 2*α^3*c*e₁^2 - 4*α^3*c*e₂ + 2*α^3*c + α^2*c^3*e₁ - α^2*c^2*e₁^2 +
    3*α^2*c^2*e₂ - α^2*c^2 - α^2*c*e₁*e₂ + 2*α^2*c*e₁ - α^2*e₁^2 + α^2*e₂^2 - 2*α^2*e₂ +
    3*α^2 - α*c^3*e₂ + α*c^2*e₁*e₂ - 2*α*c^2*e₁ + α*c*e₁^2 - α*c*e₂^2 + 2*α*c*e₂ - 3*α*c +
    c^3*e₁ - c^2*e₁^2 - c^2*e₂ + 4*c^2 + 2*c*e₁*e₂ - 5*c*e₁ - e₂^2 + 4*e₂ - 3) * hαq

/-! ### Step 5: the certified inequalities and hyperbolicity -/

lemma iso_one_add_three_y₀_one_sq : 1 + 3 * y₀ 1 ^ 2 = 2 * √2 := by
  rw [poly_three_y₀_one_sq, poly_sqrt8]; ring

lemma iso_ellSw_octagon : ellSw (y₀ 1) = Real.log 2 / 2 := by
  rw [ellSw, poly_four_div_octagon, Real.log_sqrt (by norm_num)]

lemma iso_sqrt_two_bounds : (1.4142 : ℝ) < √2 ∧ √2 < 1.4143 :=
  ⟨by rw [Real.lt_sqrt (by norm_num)]; norm_num, by rw [Real.sqrt_lt' (by norm_num)]; norm_num⟩

/-- The common denominator `YL + Y - 4 = √2 (ln 2 + 2 - 2√2)` of `iso_sectionMatrix` is negative at
the octagon. -/
lemma iso_octagon_den :
    3 * ellSw (y₀ 1) * y₀ 1 ^ 2 + ellSw (y₀ 1) + 3 * y₀ 1 ^ 2 - 3 < 0 := by
  have hY := iso_one_add_three_y₀_one_sq
  have e : 3 * ellSw (y₀ 1) * y₀ 1 ^ 2 + ellSw (y₀ 1) + 3 * y₀ 1 ^ 2 - 3 =
      ellSw (y₀ 1) * (1 + 3 * y₀ 1 ^ 2) + (1 + 3 * y₀ 1 ^ 2) - 4 := by ring
  rw [e, hY, iso_ellSw_octagon]
  obtain ⟨hs1, hs2⟩ := iso_sqrt_two_bounds
  have hl := Real.log_two_lt_d9
  nlinarith

/-- `e₁` at the octagon: `((4√2 - 3) ln 2 + 42 - 30√2)/(ln 2 + 2 - 2√2) ≈ -10.4612`. -/
lemma iso_sectionE1_octagon :
    iso_sectionE1 (y₀ 1 ^ 2) (ellSw (y₀ 1)) =
      ((4 * √2 - 3) * Real.log 2 + 42 - 30 * √2) / (Real.log 2 + 2 - 2 * √2) := by
  have hY : 1 + 3 * y₀ 1 ^ 2 = 2 * √2 := iso_one_add_three_y₀_one_sq
  have hs2 : √2 ^ 2 = 2 := poly_sqrt_two_sq
  have hs3 : √2 ^ 3 = 2 * √2 := by rw [pow_succ, hs2]
  have hs0 : 0 < √2 := by positivity
  obtain ⟨hlo, hhi⟩ := iso_sqrt_two_bounds
  have hl := Real.log_two_lt_d9
  have hD : Real.log 2 + 2 - 2 * √2 ≠ 0 := by nlinarith
  have hden : Real.log 2 / 2 * (2 * √2) + 2 * √2 - 4 = √2 * (Real.log 2 + 2 - 2 * √2) := by
    linear_combination (2 : ℝ) * hs2
  rw [iso_sectionE1, hY, iso_ellSw_octagon, hden]
  field_simp
  ring_nf
  simp only [hs2, hs3, show √2 ^ 4 = 4 by rw [show 4 = 2 * 2 by rfl, pow_mul, hs2]; norm_num]
  ring

/-- `χ_A(-1) = 2 + 2e₁ + e₂` at the octagon: `(10 ln 2 + 52 - 42√2)/(ln 2 + 2 - 2√2) ≈ 3.4410`. -/
lemma iso_chiNegOne_octagon :
    2 + 2 * iso_sectionE1 (y₀ 1 ^ 2) (ellSw (y₀ 1)) + iso_sectionE2 (y₀ 1 ^ 2) (ellSw (y₀ 1)) =
      (10 * Real.log 2 + 52 - 42 * √2) / (Real.log 2 + 2 - 2 * √2) := by
  have hY : 1 + 3 * y₀ 1 ^ 2 = 2 * √2 := iso_one_add_three_y₀_one_sq
  have hs2 : √2 ^ 2 = 2 := poly_sqrt_two_sq
  have hs3 : √2 ^ 3 = 2 * √2 := by rw [pow_succ, hs2]
  have hs4 : √2 ^ 4 = 4 := by rw [show 4 = 2 * 2 by rfl, pow_mul, hs2]; norm_num
  have hs5 : √2 ^ 5 = 4 * √2 := by rw [pow_succ, hs4]
  have hs0 : 0 < √2 := by positivity
  obtain ⟨hlo, hhi⟩ := iso_sqrt_two_bounds
  have hl := Real.log_two_lt_d9
  have hD : Real.log 2 + 2 - 2 * √2 ≠ 0 := by nlinarith
  have hden : Real.log 2 / 2 * (2 * √2) + 2 * √2 - 4 = √2 * (Real.log 2 + 2 - 2 * √2) := by
    linear_combination (2 : ℝ) * hs2
  rw [iso_sectionE1, iso_sectionE2, hY, iso_ellSw_octagon, hden]
  field_simp
  ring_nf
  simp only [hs2, hs3, hs4, hs5]
  ring

/-- **The certified inequalities** of the direct calculation for the octagon: `-e₁ > 4` and
`p(-2) = χ_A(-1) = 2 + 2e₁ + e₂ > 0`, from `ln 2 ∈ (0.6931471803, 0.6931471808)` and
`√2 ∈ (1.4142, 1.4143)`. They reduce to `ln 2 + 2 - 2√2 < 0`,
`(4√2 + 1) ln 2 + 50 - 38√2 > 0` (`≈ 0.874`) and `10 ln 2 + 52 - 42√2 < 0` (`≈ -0.465`). -/
theorem iso_octagon_bounds :
    4 < -iso_sectionE1 (y₀ 1 ^ 2) (ellSw (y₀ 1)) ∧
      0 < 2 + 2 * iso_sectionE1 (y₀ 1 ^ 2) (ellSw (y₀ 1)) +
        iso_sectionE2 (y₀ 1 ^ 2) (ellSw (y₀ 1)) := by
  rw [iso_chiNegOne_octagon, iso_sectionE1_octagon]
  obtain ⟨hs1, hs2⟩ := iso_sqrt_two_bounds
  have hl1 := Real.log_two_gt_d9
  have hl2 := Real.log_two_lt_d9
  have hD : Real.log 2 + 2 - 2 * √2 < 0 := by nlinarith
  constructor
  · rw [← neg_div, lt_div_iff_of_neg hD]
    nlinarith [mul_pos (sub_pos.2 hs1) (sub_pos.2 hl1)]
  · exact div_pos_of_neg_of_neg (by nlinarith) hD

/-- The octagon's section matrix has no eigenvalue of modulus `1`: for every `θ`,
`det(A² - 2cos θ A + 1) = p(2cos θ)² > 0`, since `p(w) = (w + 2)² + (-e₁ - 4)(w + 2) + p(-2)` is
positive for `w ≥ -2`. (A complex eigenvalue `e^{iθ}` of the real matrix `A` would make
`A² - 2cos θ A + 1 = (A - e^{iθ})(A - e^{-iθ})` singular.) -/
theorem iso_sectionMatrix_octagon_hyperbolic (θ : ℝ) :
    ((iso_sectionMatrix (y₀ 1 ^ 2) (ellSw (y₀ 1))) ^ 2 -
        (2 * Real.cos θ) • iso_sectionMatrix (y₀ 1 ^ 2) (ellSw (y₀ 1)) + 1).det ≠ 0 := by
  have hu : 0 < y₀ 1 ^ 2 := by
    have := poly_y0_pos (poly_y₀_mem le_rfl).1
    positivity
  rw [iso_det_quadratic _ _ _ (iso_sectionMatrix_charpoly _ _ hu iso_octagon_den.ne)]
  obtain ⟨ha, hb⟩ := iso_octagon_bounds
  have hc := Real.neg_one_le_cos θ
  have hp : 0 < (2 * Real.cos θ) ^ 2 - iso_sectionE1 (y₀ 1 ^ 2) (ellSw (y₀ 1)) * (2 * Real.cos θ) +
      iso_sectionE2 (y₀ 1 ^ 2) (ellSw (y₀ 1)) - 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 ha.le) (show 0 ≤ 2 * Real.cos θ + 2 by linarith),
      sq_nonneg (2 * Real.cos θ + 2)]
  positivity

/-- `λ₁ ≠ 0` at the octagon: `-3 - 6y₀² + Yℓ = -1 - 2Y + Yℓ < 0` for `Y = 2√2`, `ℓ = ln 2/2`. -/
lemma ihy_strongL₁_octagon_ne_zero : strongL₁ (y₀ 1) ≠ 0 := by
  have hy : 0 < y₀ 1 := poly_y0_pos (poly_y₀_mem le_rfl).1
  have hY := iso_one_add_three_y₀_one_sq
  have hs : 0 < √2 := by positivity
  have hl := Real.log_two_lt_d9
  have hlt : (1 + 3 * y₀ 1 ^ 2) * ellSw (y₀ 1) < 3 + 6 * y₀ 1 ^ 2 := by
    rw [iso_ellSw_octagon, show 3 + 6 * y₀ 1 ^ 2 = 1 + 2 * (1 + 3 * y₀ 1 ^ 2) by ring, hY]
    nlinarith [mul_lt_mul_of_pos_left (show Real.log 2 < 1 by linarith) hs]
  rw [strongL₁]
  refine div_ne_zero (neg_ne_zero.2 (mul_ne_zero (by positivity) (by linarith))) (by positivity)

/-- The free coordinates of the tangent space of the section are `δX₀₀, δX₀₁, δΛ₁₀₀, δΛ₁₀₁`: a
tangent vector with these four coordinates zero vanishes (the linearized constraints are solved
for `δX₁₀`, `δΛ₁₁₀`, `δΛ_R₀₀`, `δΛ_R₀₁`, `δΛ_R₁₀`). -/
lemma ihy_tangentSection_eq_zero (w : Fin 9 → ℝ) (hw : w ∈ iso_tangentSection) (h0 : w 0 = 0)
    (h1 : w 1 = 0) (h3 : w 3 = 0) (h4 : w 4 = 0) : w = 0 := by
  have hy : 0 < y₀ 1 := poly_y0_pos (poly_y₀_mem le_rfl).1
  have hl := ihy_strongL₁_octagon_ne_zero
  obtain ⟨hA, hB⟩ := ihy_qFix_den
  rw [iso_tangentSection, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    ihy_fderiv_sectionConstraints _ _ hA hB, ihy_phaseCoords_qFix _ hy] at hw
  generalize y₀ 1 = y at hy hl hw
  have e0 := congrFun hw 0
  have e1 := congrFun hw 1
  have e2 := congrFun hw 2
  have e3 := congrFun hw 3
  have e4 := congrFun hw 4
  simp only [one_div, _root_.mul_inv_rev, mul_neg, Fin.isValue, cons_val_zero, mul_zero, h0,
    cons_val_one, neg_mul, sub_neg_eq_add, zero_add, cons_val, h1, sub_zero, zero_mul, add_zero, h3,
    h4, zero_sub, neg_neg, even_two, Even.neg_pow, Pi.zero_apply, mul_eq_zero, neg_eq_zero,
    inv_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, or_false,
    Nat.ofNat_nonneg, Real.sqrt_eq_zero, or_self, false_or, or_self_right] at e0 e1 e2 e3 e4
  have hY : 1 + 3 * y ^ 2 ≠ 0 := by positivity
  have hw2 : w 2 = 0 := e0.resolve_left hy.ne'
  have hw5 : w 5 = 0 := by simpa [hl, hY, hy.ne'] using e4
  have hs3 : 0 < √3 := by positivity
  simp only [hw2, hw5, mul_zero, sub_zero, neg_zero, add_zero] at e1 e2 e3
  field_simp at e3
  have hw6 : w 6 = 0 :=
    (mul_eq_zero.1 (show y * w 6 = 0 by linear_combination e3 / 6)).resolve_left hy.ne'
  rw [hw6] at e2
  field_simp at e2
  have hw8 : w 8 = 0 := by
    have h : √3 * y * w 8 = 0 := by linear_combination -e2
    simpa [hs3.ne', hy.ne'] using h
  have hw7 : w 7 = 0 := by
    rw [hw8, mul_zero, neg_zero, zero_add] at e1
    simpa [hy.ne'] using e1
  funext i
  fin_cases i <;> simp [h0, h1, hw2, h3, h4, hw5, hw6, hw7, hw8]

/-- Every tangent vector of the section is a combination of `iso_sectionBasis`, with the
coefficients read off from its free coordinates `δX₀₀, δX₀₁, δΛ₁₀₀, δΛ₁₀₁`. -/
lemma ihy_tangentSection_eq_sum (v : Fin 9 → ℝ) (hv : v ∈ iso_tangentSection) :
    v = ∑ i, ![v 0, √3 * v 1, y₀ 1 * v 3, √3 * y₀ 1 * v 4] i •
      iso_sectionBasis (y₀ 1) (ellSw (y₀ 1)) i := by
  have hy : 0 < y₀ 1 := poly_y0_pos (poly_y₀_mem le_rfl).1
  have hs3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  rw [← sub_eq_zero]
  apply ihy_tangentSection_eq_zero
  · exact iso_tangentSection.sub_mem hv (iso_tangentSection.sum_mem fun i _ ↦
      iso_tangentSection.smul_mem _ (iso_sectionBasis_mem i))
  · simp [Fin.sum_univ_four, iso_sectionBasis]
  · simp [Fin.sum_univ_four, iso_sectionBasis]
    linear_combination (-(v 1) / 3) * hs3
  · simp [Fin.sum_univ_four, iso_sectionBasis]
    field_simp
    ring
  · simp [Fin.sum_univ_four, iso_sectionBasis]
    field_simp
    rw [Real.sq_sqrt (by norm_num)]
    ring

/-- A continuous linear map acting on a family by a matrix acts on the coefficients of a
combination of the family by that matrix. -/
lemma ihy_map_sum_smul (f : (Fin 9 → ℝ) →L[ℝ] (Fin 9 → ℝ)) (b : Fin 4 → Fin 9 → ℝ)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hf : ∀ j, f (b j) = ∑ i, M i j • b i) (c : Fin 4 → ℝ) :
    f (∑ j, c j • b j) = ∑ i, (M *ᵥ c) i • b i := by
  simp only [map_sum, map_smul, hf, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct,
    Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [mul_comm]

/-- **"Direct calculation shows that the fixed point `q_oct` is hyperbolic"**: the derivative `A`
of the Poincaré map on the tangent space of the section has no eigenvalue of modulus `1`, in the
real form: `A²v - 2cos θ Av + v = 0` only for `v = 0`. (From `iso_sectionBasis_mem`,
`iso_sectionBasis_linearIndependent`, `iso_fderiv_basis` and
`iso_sectionMatrix_octagon_hyperbolic`, once the tangent space is known to be four-dimensional.) -/
theorem iso_hyperbolic (θ : ℝ) (v : Fin 9 → ℝ) (hv : v ∈ iso_tangentSection)
    (h : fderiv ℝ iso_poincareMapCoords (iso_phaseCoords (iso_qFix (y₀ 1)))
          (fderiv ℝ iso_poincareMapCoords (iso_phaseCoords (iso_qFix (y₀ 1))) v) -
        (2 * Real.cos θ) • fderiv ℝ iso_poincareMapCoords (iso_phaseCoords (iso_qFix (y₀ 1))) v +
          v = 0) :
    v = 0 := by
  set F := fderiv ℝ iso_poincareMapCoords (iso_phaseCoords (iso_qFix (y₀ 1)))
  set b := iso_sectionBasis (y₀ 1) (ellSw (y₀ 1))
  set M := iso_sectionMatrix (y₀ 1 ^ 2) (ellSw (y₀ 1))
  set c : Fin 4 → ℝ := ![v 0, √3 * v 1, y₀ 1 * v 3, √3 * y₀ 1 * v 4]
  have hv' : v = ∑ i, c i • b i := ihy_tangentSection_eq_sum v hv
  have hFb : ∀ j, F (b j) = ∑ i, M i j • b i := iso_fderiv_basis
  have h1 : F v = ∑ i, (M *ᵥ c) i • b i := by
    rw [hv']; exact ihy_map_sum_smul F b M hFb c
  have h2 : F (F v) = ∑ i, (M *ᵥ (M *ᵥ c)) i • b i := by
    rw [h1]; exact ihy_map_sum_smul F b M hFb _
  rw [h2, h1] at h
  have hcoef : (M ^ 2 - (2 * Real.cos θ) • M + 1) *ᵥ c = 0 := by
    have := Fintype.linearIndependent_iff.1 iso_sectionBasis_linearIndependent
      (fun i ↦ ((M ^ 2 - (2 * Real.cos θ) • M + 1) *ᵥ c) i) ?_
    · funext i; exact this i
    · change ∑ i, _ • b i = 0
      rw [← h]
      conv_rhs => rw [hv']
      simp only [sq, ← Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.sub_mulVec,
        Matrix.smul_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul, add_smul, sub_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.smul_sum, smul_smul]
  have hc0 : c = 0 :=
    Matrix.eq_zero_of_mulVec_eq_zero (iso_sectionMatrix_octagon_hyperbolic θ) hcoef
  rw [hv', hc0]
  simp

end SmoothedPolygons
