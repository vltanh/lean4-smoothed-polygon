module

public import SmoothedPolygons.Ch3.ControlSets
public import SmoothedPolygons.Ch4.AdjointOrbit

/-!
# The star domain and the half-plane control problem (§4.4–§4.6)

The star inequalities on `X = Φ(x + iy)` cut out the ideal triangle `𝔥*` (Theorem 4.4.1); the
dynamics of `X` becomes an ODE for `(x, y)` (Problem 4.5.1, Lemma 4.5.2); and the dihedral group of
the hexagon acts compatibly on the controls, the star functions and the upper half-plane (§4.6).
-/

@[expose] public section

namespace SmoothedPolygons

open Matrix

/-- The star domain `𝔥* = {x + iy | y > 0, -1/√3 < x < 1/√3, x² + y² > 1/3}`, an ideal
triangle in the upper half-plane (`eqn:star`), as a subset of `ℝ × ℝ`. -/
def starDomain : Set (ℝ × ℝ) :=
  {p | 0 < p.2 ∧ -(1 / √3) < p.1 ∧ p.1 < 1 / √3 ∧ 1 / 3 < p.1 ^ 2 + p.2 ^ 2}

/-- **Theorem 4.4.1** (`prop:star-domain`). The star inequalities on `X = Φ(x + iy)` hold exactly
on the ideal triangle `𝔥*`; so the state space of the control problem is `SL₂(ℝ) × 𝔥*`.
(`Φ(z)` always has trace zero and determinant one.) -/
theorem theorem4_4_1 (x y : ℝ) (hy : 0 < y) : IsStarState (Φ x y) ↔ (x, y) ∈ starDomain := by
  have h3 : 0 < √3 := by positivity
  have h3sq : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hy0 : y ≠ 0 := hy.ne'
  -- `Φ(z)` is traceless with determinant one, and its star functions are explicit
  have htr : (Φ x y).trace = 0 := by simp [Φ, Matrix.trace_fin_two]; ring
  have hdet : (Φ x y).det = 1 := by
    simp [Φ, Matrix.det_fin_two]; field_simp; ring
  have hρ₀ : ρ₀ (Φ x y) = (1 + √3 * x) / (√3 * y) := by
    simp [ρ₀, Φ]; field_simp
  have hρ₁ : ρ₁ (Φ x y) = (1 - √3 * x) / (√3 * y) := by
    simp [ρ₁, Φ]; field_simp
  have hρ₂ : ρ₂ (Φ x y) = (3 * (x ^ 2 + y ^ 2) - 1) / (2 * √3 * y) := by
    simp [ρ₂, Φ]; field_simp; ring
  have hd₁ : 0 < √3 * y := by positivity
  have hd₂ : 0 < 2 * √3 * y := by positivity
  simp only [IsStarState, starDomain, Set.mem_ofPred_eq, htr, hdet, hρ₀, hρ₁, hρ₂,
    div_pos_iff_of_pos_right hd₁, div_pos_iff_of_pos_right hd₂, true_and, hy]
  have e1 : -(1 / √3) < x ↔ 0 < 1 + √3 * x := by
    rw [← neg_div, div_lt_iff₀ h3]; constructor <;> intro h <;> linarith
  have e2 : x < 1 / √3 ↔ 0 < 1 - √3 * x := by
    rw [lt_div_iff₀ h3]; constructor <;> intro h <;> linarith
  rw [e1, e2]
  constructor
  · rintro ⟨h1, h2, h3'⟩; exact ⟨h1, h2, by linarith⟩
  · rintro ⟨h1, h2, h3'⟩; exact ⟨h1, h2, by linarith⟩

/-- The right-hand side `f₁(x, y; u) = y(2ax + b - cx² + cy²)/(2ax + b - cx² - cy²)` of the
half-plane control problem (Problem 4.5.1), where `Z_u = [[a, b], [c, -a]]`.

Problem 4.5.1 prints `a = (u₂ - u₁)/√3`, the negative of the entry `(u₁ - u₂)/√3` of `Z_u` in
`eqn:trisystem-Z0` to which it refers; with the printed sign Lemma 4.5.2 fails. The entries of
`Z_u` are used here. -/
noncomputable def halfPlaneF₁ (x y : ℝ) (u : Fin 3 → ℝ) : ℝ :=
  y * (2 * controlMatrix u 0 0 * x + controlMatrix u 0 1 - controlMatrix u 1 0 * x ^ 2 +
      controlMatrix u 1 0 * y ^ 2) /
    (2 * controlMatrix u 0 0 * x + controlMatrix u 0 1 - controlMatrix u 1 0 * x ^ 2 -
      controlMatrix u 1 0 * y ^ 2)

/-- The right-hand side `f₂(x, y; u) = 2y²(a - cx)/(2ax + b - cx² - cy²)` of the half-plane control
problem (Problem 4.5.1), where `Z_u = [[a, b], [c, -a]]` (see `halfPlaneF₁` for the sign of `a`). -/
noncomputable def halfPlaneF₂ (x y : ℝ) (u : Fin 3 → ℝ) : ℝ :=
  2 * y ^ 2 * (controlMatrix u 0 0 - controlMatrix u 1 0 * x) /
    (2 * controlMatrix u 0 0 * x + controlMatrix u 0 1 - controlMatrix u 1 0 * x ^ 2 -
      controlMatrix u 1 0 * y ^ 2)

/-- The derivative of `s ↦ Φ(x(s), y(s))` when `x' = r₁`, `y' = r₂` (the chain rule, entry by
entry). -/
private noncomputable def algA_dΦ (x y r₁ r₂ : ℝ) : Mat2 :=
  !![(r₁ * y - x * r₂) / y ^ 2, (-(2 * x * r₁ + 2 * y * r₂) * y + (x ^ 2 + y ^ 2) * r₂) / y ^ 2;
    -r₂ / y ^ 2, -((r₁ * y - x * r₂) / y ^ 2)]

/-- The chain rule for `s ↦ Φ(x(s), y(s))`. -/
private lemma algA_hasDerivAt_Φ {x y : ℝ → ℝ} {t r₁ r₂ : ℝ} (hx : HasDerivAt x r₁ t)
    (hy : HasDerivAt y r₂ t) (hy0 : y t ≠ 0) :
    HasDerivAtEntrywise (fun s ↦ Φ (x s) (y s)) (algA_dΦ (x t) (y t) r₁ r₂) t := by
  rw [hasDerivAtEntrywise_fin_two_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [Φ, algA_dΦ] using hx.fun_div hy hy0
  · have h := (((hx.fun_pow 2).fun_add (hy.fun_pow 2)).fun_neg).fun_div hy hy0
    simp only [Φ, algA_dΦ, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    convert h using 1
    push_cast; ring
  · have h := (hasDerivAt_const t (1 : ℝ)).fun_div hy hy0
    simp only [Φ, algA_dΦ, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    convert h using 1
    ring
  · have h := hx.fun_neg.fun_div hy hy0
    simp only [Φ, algA_dΦ, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    convert h using 1
    ring

/-- **Lemma 4.5.2** (`lem:X-dynamics`). If `X = Φ(x + iy)` follows `X' = [Z_u, X]/⟨Z_u, X⟩`, then
`x' = f₁(x, y; u)` and `y' = f₂(x, y; u)`; moreover `T Φ(f₁, f₂)` is the class of
`Z_u/⟨Z_u, X⟩` (`eqn:tangent-map-f1f2`): `[Y_z(f₁, f₂), X] = [Z_u/⟨Z_u, X⟩, X]`. -/
theorem lemma4_5_2 (x y : ℝ → ℝ) (u : Fin 3 → ℝ) (t x' y' : ℝ)
    (hstar : (x t, y t) ∈ starDomain) (hu : u ∈ controlSimplex)
    (hx : HasDerivAt x x' t) (hy : HasDerivAt y y' t)
    (hX : HasDerivAtEntrywise (fun s ↦ Φ (x s) (y s))
      (controlP u (Φ (x t) (y t)) * Φ (x t) (y t) - Φ (x t) (y t) * controlP u (Φ (x t) (y t))) t) :
    x' = halfPlaneF₁ (x t) (y t) u ∧ y' = halfPlaneF₂ (x t) (y t) u ∧
      tangentLift (x t) (y t) x' y' * Φ (x t) (y t) -
          Φ (x t) (y t) * tangentLift (x t) (y t) x' y' =
        controlP u (Φ (x t) (y t)) * Φ (x t) (y t) -
          Φ (x t) (y t) * controlP u (Φ (x t) (y t)) := by
  have hy0 : 0 < y t := hstar.1
  -- `Φ(z(t))'` by the chain rule equals `[P, X]`
  have hD := algA_hasDerivAt_Φ hx hy hy0.ne'
  have hDP := hD.unique hX
  -- the denominator `y⟨Z_u, Φ(z)⟩ = 2ax + b - c(x² + y²)` is nonzero on the star domain
  -- (Theorem 4.4.1 and Lemma 3.3.4)
  have hXstar := (theorem4_4_1 (x t) (y t) hy0).2 hstar
  have hneg := (lemma3_3_4 (Φ (x t) (y t)) hXstar.1).1 hXstar.2.2 u hu
  have hZ11 : controlMatrix u 1 1 = -controlMatrix u 0 0 := by simp [controlMatrix]; ring
  have htf : traceForm (controlMatrix u) (Φ (x t) (y t)) =
      (2 * controlMatrix u 0 0 * x t + controlMatrix u 0 1 - controlMatrix u 1 0 * x t ^ 2 -
        controlMatrix u 1 0 * y t ^ 2) / y t := by
    rw [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Fin.sum_univ_two, hZ11]
    simp only [Φ, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    field_simp
    ring
  have hden : 2 * controlMatrix u 0 0 * x t + controlMatrix u 0 1 - controlMatrix u 1 0 * x t ^ 2 -
      controlMatrix u 1 0 * y t ^ 2 ≠ 0 := by
    intro h; rw [htf, h, zero_div] at hneg; exact lt_irrefl _ hneg
  -- compare the `(0, 0)` and `(1, 0)` entries
  have e00 := congrFun (congrFun hDP 0) 0
  have e10 := congrFun (congrFun hDP 1) 0
  simp only [controlP, htf, Matrix.sub_apply, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_apply,
    Matrix.mul_apply, Fin.sum_univ_two, hZ11, smul_eq_mul] at e00 e10
  simp only [algA_dΦ, Φ, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at e00 e10
  have hη : y t ≠ 0 := hy0.ne'
  set a := controlMatrix u 0 0 with ha
  set b := controlMatrix u 0 1 with hb
  set c := controlMatrix u 1 0 with hc
  set ξ := x t with hξ
  set η := y t with hη'
  set D := 2 * a * ξ + b - c * ξ ^ 2 - c * η ^ 2 with hD'
  field_simp at e00 e10
  -- solve for `x'` and `y'`
  have hy' : y' = halfPlaneF₂ ξ η u := by
    simp only [halfPlaneF₂, ← ha, ← hb, ← hc, ← hD']
    rw [eq_div_iff hden]
    linear_combination -e10
  have hx' : x' = halfPlaneF₁ ξ η u := by
    simp only [halfPlaneF₁, ← ha, ← hb, ← hc, ← hD']
    rw [eq_div_iff hden]
    have h : η * (x' * D - η * (2 * a * ξ + b - c * ξ ^ 2 + c * η ^ 2)) = 0 := by
      linear_combination e00 - ξ * e10
    linear_combination (mul_eq_zero.1 h).resolve_left hη
  refine ⟨hx', hy', ?_⟩
  -- `[Y_z(x', y'), X] = TΦ(x', y') = Φ(z(t))' = [P, X]` (Lemma 4.2.4)
  have hL := lemma4_2_4 ξ η x' y' hy0
  have hline := algA_hasDerivAt_Φ (x := fun s ↦ ξ + s * x') (y := fun s ↦ η + s * y') (t := 0)
    (by simpa using ((hasDerivAt_id (0 : ℝ)).mul_const x').const_add ξ)
    (by simpa using ((hasDerivAt_id (0 : ℝ)).mul_const y').const_add η) (by simpa using hη)
  simp only [zero_mul, add_zero] at hline
  rw [hL.unique hline, hDP]

/-! ### Dihedral symmetry (§4.6) -/

/-- The reflection `S = [[-1, 0], [0, 1]]` across the vertical axis (§4.6). -/
def reflS : Mat2 := !![-1, 0; 0, 1]

/-- `R⁻¹ = [[1/2, √3/2], [-√3/2, 1/2]]`. -/
private lemma algA_R_inv : R⁻¹ = !![1 / 2, √3 / 2; -(√3 / 2), 1 / 2] := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  refine Matrix.inv_eq_left_inv ?_
  ext i j; fin_cases i <;> fin_cases j <;> simp [R] <;> linarith [h3]

/-- `S⁻¹ = S`. -/
private lemma algA_reflS_inv : reflS⁻¹ = reflS := by
  refine Matrix.inv_eq_left_inv ?_
  ext i j; fin_cases i <;> fin_cases j <;> simp [reflS]

/-- §4.6: the rotation `R` permutes the control matrices of the vertices of `U_T`:
`R Z_{e₃} R⁻¹ = Z_{e₂}`, `R Z_{e₂} R⁻¹ = Z_{e₁}`, `R Z_{e₁} R⁻¹ = Z_{e₃}`. -/
theorem R_conj_controlMatrix_vertex :
    R * controlMatrix (vertex 2) * R⁻¹ = controlMatrix (vertex 1) ∧
      R * controlMatrix (vertex 1) * R⁻¹ = controlMatrix (vertex 0) ∧
      R * controlMatrix (vertex 0) * R⁻¹ = controlMatrix (vertex 2) := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3' : √3 ≠ 0 := by positivity
  rw [algA_R_inv]
  refine ⟨?_, ?_, ?_⟩ <;>
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [R, controlMatrix, vertex, Matrix.mul_apply, Fin.sum_univ_two] <;>
      field_simp <;> ring_nf <;> simp only [h3] <;> ring_nf

/-- §4.6: the rotation permutes the star functions, `ρ_j(R X R⁻¹) = ρ_{j-1}(X)` (indices mod 3),
for `X ∈ 𝔰𝔩₂(ℝ)`. -/
theorem ρ_R_conj (X : Mat2) (hX : X.trace = 0) :
    ρ₀ (R * X * R⁻¹) = ρ₂ X ∧ ρ₁ (R * X * R⁻¹) = ρ₀ X ∧ ρ₂ (R * X * R⁻¹) = ρ₁ X := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3' : √3 ≠ 0 := by positivity
  have h3c : √3 ^ 3 = 3 * √3 := by rw [pow_succ, h3]
  rw [algA_R_inv, algA_eta_of_trace_eq_zero X hX]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [R, ρ₀, ρ₁, ρ₂] <;>
    field_simp <;> ring_nf <;> simp only [h3, h3c] <;> ring_nf

/-- §4.6: the reflection acts on `Φ` by `z ↦ -z̄`: `ε_S S Φ(z) S⁻¹ = Φ(-z̄)`, where
`ε_S = det S = -1`. -/
theorem reflS_conj_Φ (x y : ℝ) (hy : 0 < y) : -(reflS * Φ x y * reflS⁻¹) = Φ (-x) y := by
  rw [algA_reflS_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [reflS, Φ] <;> ring

/-- §4.6: the reflection permutes the star functions, `ρ_j(ε_S S X S⁻¹) = ρ_{1-j}(X)`
(indices mod 3), for `X ∈ 𝔰𝔩₂(ℝ)`. -/
theorem ρ_reflS_conj (X : Mat2) (hX : X.trace = 0) :
    ρ₀ (-(reflS * X * reflS⁻¹)) = ρ₁ X ∧ ρ₁ (-(reflS * X * reflS⁻¹)) = ρ₀ X ∧
      ρ₂ (-(reflS * X * reflS⁻¹)) = ρ₂ X := by
  rw [algA_reflS_inv, algA_eta_of_trace_eq_zero X hX]
  refine ⟨?_, ?_, ?_⟩
  · simp [reflS, ρ₀, ρ₁, sub_eq_add_neg]
  · simp [reflS, ρ₀, ρ₁]
  · simp [reflS, ρ₂]

/-- §4.6: the reflection acts on the control matrices of the vertices by
`-S Z_{e₂} S⁻¹ = Z_{e₃}`, `-S Z_{e₃} S⁻¹ = Z_{e₂}`, `-S Z_{e₁} S⁻¹ = Z_{e₁}`. -/
theorem reflS_conj_controlMatrix_vertex :
    -(reflS * controlMatrix (vertex 1) * reflS⁻¹) = controlMatrix (vertex 2) ∧
      -(reflS * controlMatrix (vertex 2) * reflS⁻¹) = controlMatrix (vertex 1) ∧
      -(reflS * controlMatrix (vertex 0) * reflS⁻¹) = controlMatrix (vertex 0) := by
  rw [algA_reflS_inv]
  refine ⟨?_, ?_, ?_⟩ <;>
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [reflS, controlMatrix, vertex] <;> ring

end SmoothedPolygons
