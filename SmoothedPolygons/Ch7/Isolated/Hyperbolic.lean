module

public import SmoothedPolygons.Ch7.Isolated.Defs
public import SmoothedPolygons.Ch7.SmoothedPolygon
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Theorem 7.7.1, step 5: the direct calculation (hyperbolicity)

The derivative of the Poincaré map on the tangent space of the section at the octagon's point has
the explicit matrix `iso_sectionMatrix` in the basis `iso_sectionBasis`, with reciprocal
characteristic polynomial `z⁴ - e₁z³ + e₂z² - e₁z + 1`; the certified inequalities `-e₁ > 4` and
`2 + 2e₁ + e₂ > 0` show that it has no eigenvalue of modulus `1`.
-/

@[expose] public section

namespace SmoothedPolygons

open Matrix Set Filter Topology MeasureTheory

/-! ### Step 5: the derivative of the Poincaré map in a basis of the section -/

/-- `iso_sectionBasis` is a basis of the tangent space of the section at `q_oct`. -/
theorem iso_sectionBasis_mem (j : Fin 4) :
    iso_sectionBasis (y₀ 1) (ellSw (y₀ 1)) j ∈ iso_tangentSection := by
  sorry

theorem iso_sectionBasis_linearIndependent :
    LinearIndependent ℝ (iso_sectionBasis (y₀ 1) (ellSw (y₀ 1))) := by
  sorry

/-- **The direct calculation.** The derivative of the Poincaré map at `q_oct` maps the basis
vectors by the matrix `iso_sectionMatrix`. -/
theorem iso_fderiv_basis (j : Fin 4) :
    fderiv ℝ iso_poincareMapCoords (iso_phaseCoords (iso_qFix (y₀ 1)))
        (iso_sectionBasis (y₀ 1) (ellSw (y₀ 1)) j) =
      ∑ i, iso_sectionMatrix (y₀ 1 ^ 2) (ellSw (y₀ 1)) i j •
        iso_sectionBasis (y₀ 1) (ellSw (y₀ 1)) i := by
  sorry

open Polynomial in
/-- The characteristic polynomial of `iso_sectionMatrix` is reciprocal,
`z⁴ - e₁ z³ + e₂ z² - e₁ z + 1` (the Poincaré map is symplectic); an identity of rational
functions in `(u, L)` (checked exactly with sympy). -/
theorem iso_sectionMatrix_charpoly (u L : ℝ) (hu : 0 < u) (hL : 3 * L * u + L + 3 * u - 3 ≠ 0) :
    (iso_sectionMatrix u L).charpoly =
      X ^ 4 - C (iso_sectionE1 u L) * X ^ 3 + C (iso_sectionE2 u L) * X ^ 2 -
        C (iso_sectionE1 u L) * X + 1 := by
  sorry

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
  sorry

end SmoothedPolygons
