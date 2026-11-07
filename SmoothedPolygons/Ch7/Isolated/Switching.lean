module

public import SmoothedPolygons.Ch7.Isolated.Defs
public import SmoothedPolygons.Ch7.HMax

/-!
# Theorem 7.7.1, step 2: transversality of the switching times

Step 2: the slopes of `χ₃₂` at `0` and of `χ₃₁` at `t_sw` along the strong lift (the remark after
Lemma 7.5.3), their sign, and the independence of the slope of `χ₃₂` on the switching surface from
the control on the edge `[e₂, e₃]`.

* `iso_chi32_hasDerivAt` follows the remark after Lemma 7.5.3. In the variables of the proof of
  Lemma 7.5.3, `χ₃₂(t) = 2 f(y, yW)/(3y²W y₀³(2 - W))`, `y = 1 + 3y₀²`, `W = exp(√3 y₀ t)`
  (`chi32_eq`); `f(y, y) = 0` (`hmaxF_diag`) and on the diagonal `∂f/∂r = -∂f/∂y = y((4 - y) -
  y ln(4/y))` (eqn:f', `hmax_deriv_diag`), so the quotient rule gives the slope. The book's identity
  `chi32_eq` is stated for `t ∈ [0, t_sw]`; a two-sided derivative at `0` needs it on a
  neighbourhood of `0`, and the same substitution proves it wherever `W ≠ 2` (`isw_chi32_eq`).
* `iso_chi31_hasDerivAt`: by the symmetry `χ₃₁(t_sw - t) = χ₃₂(t)` of the proof of Lemma 7.5.3,
  again extended from `[0, t_sw]` to `W ≠ 2` by the same substitution (`isw_chi31_eq_chi32`), and
  the chain rule.
* `iso_edge_slope`: write `A = P₂ = Z_{e₂}/⟨Z_{e₂}, X⟩`, `B = P₃`. Along a line the derivative of
  `χ₃₂ = ⟨Λ_R, A - B⟩` is `⟨δΛ_R, A - B⟩ - ⟨Λ_R, A⟩⟨A, δX⟩ + ⟨Λ_R, B⟩⟨B, δX⟩`
  (`isw_hasDerivAt_chi32_line`). For `u` on the edge `[e₂, e₃]`, `P_u = μA + (1 - μ)B`
  (`isw_controlP_edge`), and on the surface `χ₂₃ = 0` one has `⟨Λ_R, A⟩ = ⟨Λ_R, B⟩ = ⟨Λ_R, P_u⟩`,
  so the vector field of `H_u` is the convex combination `μV_{e₂} + (1 - μ)V_{e₃}` and the
  derivative of `χ₃₂` along `V_{e₂}` and along `V_{e₃}` is the same Poisson bracket; both facts
  together are one polynomial identity in the entries (`isw_core`). Only `⟨Z_{e₂}, X⟩ ≠ 0`,
  `⟨Z_{e₃}, X⟩ ≠ 0`, `⟨Z_u, X⟩ ≠ 0` (from `IsStarState X`) and `χ₂₃ = 0` are used; the hypotheses
  `tr X = 0`, `tr Λ_R = 0` of the statement are not needed.
-/

@[expose] public section

namespace SmoothedPolygons

open Matrix Set Filter Topology MeasureTheory

/-! ### The slopes of `χ₃₂` at `0` and of `χ₃₁` at `t_sw` -/

/-- The identity `chi32_eq` (proof of Lemma 7.5.3) wherever `W = exp(√3 y₀ t) ≠ 2`, not only on
`[0, t_sw]`; same proof. -/
lemma isw_chi32_eq (y0 : ℝ) (hy0 : 0 < y0) (t : ℝ) (hW : Real.exp (√3 * y0 * t) ≠ 2) :
    switchingFn 2 1 (strongΛR y0 t) (segX y0 t) =
      2 * hmaxF (1 + 3 * y0 ^ 2) ((1 + 3 * y0 ^ 2) * Real.exp (√3 * y0 * t)) /
        (3 * (1 + 3 * y0 ^ 2) ^ 2 * Real.exp (√3 * y0 * t) * y0 ^ 3 *
          (2 - Real.exp (√3 * y0 * t))) := by
  have h3 : (0 : ℝ) < √3 := by positivity
  have hW0 := Real.exp_pos (√3 * y0 * t)
  rw [strongΛR, str_switchingFn_eq, (str_traceForm_segX y0 t hy0).2.1,
    (str_traceForm_segX y0 t hy0).2.2, costateΛR, str_traceForm_Z1_fin_two,
    str_traceForm_Z2_fin_two]
  have hlog : Real.log ((1 + 3 * y0 ^ 2) * Real.exp (√3 * y0 * t)) =
      Real.log (1 + 3 * y0 ^ 2) + √3 * y0 * t := by
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
  have hell : Real.log (4 / (1 + 3 * y0 ^ 2)) = ellSw y0 := by rw [ellSw, add_comm]
  simp only [hmaxF, hlog, hell, costateΛR₀₀, costateΛR₁₀, strongL₁, strongLR]
  generalize ellSw y0 = ℓ
  generalize Real.log (1 + 3 * y0 ^ 2) = Ly
  generalize Real.exp (√3 * y0 * t) = W at hW0 hW ⊢
  have hW2' : W - 2 ≠ 0 := sub_ne_zero.2 hW
  have hW2'' : 2 - W ≠ 0 := sub_ne_zero.2 (Ne.symm hW)
  have hW0' : W ≠ 0 := hW0.ne'
  field_simp
  ring_nf
  simp only [str_sqrt3_sq, str_sqrt3_pow3]
  ring_nf

/-- On the diagonal, `∂f/∂r = -∂f/∂y` (`f(y, y) = 0`), which is `y((4 - y) - y ln(4/y))` by
eqn:f' (`hmax_deriv_diag`). -/
lemma isw_hmaxF_hasDerivAt_diag {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun r ↦ hmaxF y r) (-hmaxFDeriv y y) y := by
  have hid : HasDerivAt (fun r : ℝ => r) 1 y := hasDerivAt_id' y
  have hlog : HasDerivAt Real.log y⁻¹ y := Real.hasDerivAt_log hy.ne'
  have h := ((((hid.const_mul 2).mul_const (y - 1)).mul_const y).fun_mul hlog).fun_sub
      ((hid.sub_const y).fun_mul (((hid.mul_const (y - 1)).add_const (y * (-5 + 2 * y))).add_const
        (y ^ 2 * Real.log (4 / y)))) |>.fun_sub
      ((((hid.const_mul 2).mul_const (y - 1)).mul_const y).mul_const (Real.log y))
  unfold hmaxF
  convert h using 1
  rw [hmax_deriv_diag]
  field_simp
  ring

/-- `W = exp(√3 y₀ t) ≠ 2` near `t = 0`. -/
lemma isw_W_ne_two (y0 : ℝ) : ∀ᶠ t in 𝓝 (0 : ℝ), Real.exp (√3 * y0 * t) ≠ 2 := by
  have hc : ContinuousAt (fun t : ℝ ↦ Real.exp (√3 * y0 * t)) 0 := by fun_prop
  exact hc.eventually_ne (by norm_num)

/-- The remark after Lemma 7.5.3: `χ₃₂` vanishes at `t = 0` with slope `iso_chi32Slope y₀`
(`∂f/∂r = -∂f/∂y = y((4 - y) - y ln(4/y))` on the diagonal, eqn:f'). -/
theorem iso_chi32_hasDerivAt (y0 : ℝ) (hy0 : 1 / √3 < y0) :
    HasDerivAt (fun t ↦ switchingFn 2 1 (strongΛR y0 t) (segX y0 t)) (iso_chi32Slope y0) 0 := by
  have hy : 0 < y0 := poly_y0_pos hy0
  have h3 : (0 : ℝ) < √3 := by positivity
  set Y : ℝ := 1 + 3 * y0 ^ 2 with hYdef
  have hY : 0 < Y := by positivity
  have hE : HasDerivAt (fun t : ℝ ↦ Real.exp (√3 * y0 * t))
      (Real.exp (√3 * y0 * 0) * (√3 * y0 * 1)) 0 :=
    ((hasDerivAt_id' (0 : ℝ)).const_mul (√3 * y0)).exp
  -- the numerator `2 f(y, yW)`: chain rule with `∂f/∂r` on the diagonal
  have hF : HasDerivAt (fun t ↦ hmaxF Y (Y * Real.exp (√3 * y0 * t)))
      (-hmaxFDeriv Y Y * (Y * (Real.exp (√3 * y0 * 0) * (√3 * y0 * 1)))) 0 :=
    HasDerivAt.comp_of_eq 0 (isw_hmaxF_hasDerivAt_diag hY) (hE.const_mul Y) (by simp)
  -- the denominator `3y²W y₀³(2 - W)`
  have hD := ((hE.const_mul (3 * Y ^ 2)).mul_const (y0 ^ 3)).fun_mul (hE.const_sub 2)
  have hD0 : 3 * Y ^ 2 * Real.exp (√3 * y0 * 0) * y0 ^ 3 * (2 - Real.exp (√3 * y0 * 0)) ≠ 0 := by
    rw [mul_zero, Real.exp_zero, show (2 : ℝ) - 1 = 1 by norm_num]
    positivity
  have h := (hF.const_mul 2).fun_div hD hD0
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [isw_W_ne_two y0] with t ht
    exact isw_chi32_eq y0 hy t ht
  · -- `f(y, y) = 0`, so only `∂f/∂r` survives in the quotient rule
    have hdiag : hmaxF Y (Y * Real.exp (√3 * y0 * 0)) = 0 := by
      simp only [mul_zero, Real.exp_zero, mul_one]
      exact hmaxF_diag Y hY
    rw [hdiag, hmax_deriv_diag, iso_chi32Slope, ellSw,
      show 3 * y0 ^ 2 + 1 = Y by rw [hYdef]; ring]
    simp only [mul_zero, Real.exp_zero]
    field_simp
    ring

/-- The symmetry `χ₃₁(t_sw - t) = χ₃₂(t)` of the proof of Lemma 7.5.3 (`chi31_eq_chi32`) wherever
`W = exp(√3 y₀ t) ≠ 2`, not only on `[0, t_sw]`; same substitution. -/
lemma isw_chi31_eq_chi32 (y0 : ℝ) (hy0 : 0 < y0) (t : ℝ) (hW : Real.exp (√3 * y0 * t) ≠ 2) :
    switchingFn 2 0 (strongΛR y0 (switchTime y0 - t)) (segX y0 (switchTime y0 - t)) =
      switchingFn 2 1 (strongΛR y0 t) (segX y0 t) := by
  have h3 : (0 : ℝ) < √3 := by positivity
  have hW0 := Real.exp_pos (√3 * y0 * t)
  have hexp : Real.exp (√3 * y0 * (switchTime y0 - t)) =
      4 / (3 * y0 ^ 2 + 1) / Real.exp (√3 * y0 * t) := by
    rw [mul_sub, Real.exp_sub, str_exp_switchTime hy0]
  have hV : (3 * y0 ^ 2 + 1) * Real.exp (√3 * y0 * (switchTime y0 - t)) - 2 ≠ 0 := by
    rw [hexp, mul_div_assoc', mul_div_cancel₀ _ (by positivity : (3 * y0 ^ 2 + 1 : ℝ) ≠ 0),
      sub_ne_zero]
    intro h
    rw [div_eq_iff hW0.ne'] at h
    exact hW (by linarith)
  rw [str_chi31_closed y0 hy0 _ hV, str_chi32_closed y0 hy0 _ hW, hexp]
  rw [show switchTime y0 = ellSw y0 / (√3 * y0) from rfl]
  generalize ellSw y0 = ℓ
  generalize Real.exp (√3 * y0 * t) = W at hW0 hW ⊢
  have hW2' : W - 2 ≠ 0 := sub_ne_zero.2 hW
  have hW2'' : 4 - W * 2 ≠ 0 := fun h ↦ hW (by linarith)
  have hW0' : W ≠ 0 := hW0.ne'
  field_simp
  ring_nf

/-- By the symmetry `χ₃₁(t_sw - t) = χ₃₂(t)` (proof of Lemma 7.5.3), `χ₃₁` vanishes at `t_sw`
with slope `-iso_chi32Slope y₀`: the end of the first arc is a transversal switching time, the
hypothesis of the implicit function theorem for the Poincaré time. -/
theorem iso_chi31_hasDerivAt (y0 : ℝ) (hy0 : 1 / √3 < y0) :
    HasDerivAt (fun t ↦ switchingFn 2 0 (strongΛR y0 t) (segX y0 t)) (-iso_chi32Slope y0)
      (switchTime y0) := by
  have hy : 0 < y0 := poly_y0_pos hy0
  have hs : HasDerivAt (fun t : ℝ ↦ switchTime y0 - t) (-1) (switchTime y0) := by
    simpa using (hasDerivAt_id' (switchTime y0)).const_sub (switchTime y0)
  have h := HasDerivAt.comp_of_eq (switchTime y0) (iso_chi32_hasDerivAt y0 hy0) hs
    (sub_self _).symm
  rw [mul_neg_one] at h
  refine h.congr_of_eventuallyEq ?_
  have hev : ∀ᶠ t in 𝓝 (switchTime y0), Real.exp (√3 * y0 * (switchTime y0 - t)) ≠ 2 := by
    have hc : ContinuousAt (fun t : ℝ ↦ switchTime y0 - t) (switchTime y0) := by fun_prop
    have := hc.tendsto
    rw [sub_self] at this
    exact this.eventually (isw_W_ne_two y0)
  filter_upwards [hev] with t ht
  have e := isw_chi31_eq_chi32 y0 hy (switchTime y0 - t) ht
  rw [sub_sub_cancel] at e
  exact e

/-! ### The slope of `χ₃₂` on the switching surface -/

/-- The derivative of `χ₃₂ = ⟨Λ_R, P₂ - P₃⟩` at `(Λ_R, X)` in the direction `(δΛ_R, δX)`:
`⟨δΛ_R, P₂ - P₃⟩ - ⟨Λ_R, P₂⟩⟨P₂, δX⟩ + ⟨Λ_R, P₃⟩⟨P₃, δX⟩` (`dP = -P⟨P, dX⟩`). -/
noncomputable def isw_dchi32 (ΛR X δΛR δX : Mat2) : ℝ :=
  traceForm δΛR (controlP (vertex 1) X - controlP (vertex 2) X) -
    traceForm ΛR (controlP (vertex 1) X) * traceForm (controlP (vertex 1) X) δX +
    traceForm ΛR (controlP (vertex 2) X) * traceForm (controlP (vertex 2) X) δX

private lemma isw_traceForm_add_smul_left (A B C : Mat2) (s : ℝ) :
    traceForm (A + s • B) C = traceForm A C + s * traceForm B C := by
  simp only [traceForm, Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul,
    smul_eq_mul]

private lemma isw_traceForm_add_smul_right (A B C : Mat2) (s : ℝ) :
    traceForm A (B + s • C) = traceForm A B + s * traceForm A C := by
  simp only [traceForm, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
    smul_eq_mul]

/-- The derivative of `χ₃₂` along a line `s ↦ (Λ_R + s δΛ_R, X + s δX)` at `s = 0`, where
`⟨Z_{e₂}, X⟩ ≠ 0` and `⟨Z_{e₃}, X⟩ ≠ 0`. -/
lemma isw_hasDerivAt_chi32_line (ΛR X δΛR δX : Mat2)
    (h1 : traceForm (controlMatrix (vertex 1)) X ≠ 0)
    (h2 : traceForm (controlMatrix (vertex 2)) X ≠ 0) :
    HasDerivAt (fun s : ℝ ↦ switchingFn 2 1 (ΛR + s • δΛR) (X + s • δX))
      (isw_dchi32 ΛR X δΛR δX) 0 := by
  have key : (fun s : ℝ ↦ switchingFn 2 1 (ΛR + s • δΛR) (X + s • δX)) = fun s ↦
      (traceForm ΛR (controlMatrix (vertex 1)) + s * traceForm δΛR (controlMatrix (vertex 1))) /
          (traceForm (controlMatrix (vertex 1)) X +
            s * traceForm (controlMatrix (vertex 1)) δX) -
        (traceForm ΛR (controlMatrix (vertex 2)) + s * traceForm δΛR (controlMatrix (vertex 2))) /
          (traceForm (controlMatrix (vertex 2)) X +
            s * traceForm (controlMatrix (vertex 2)) δX) := by
    funext s
    rw [str_switchingFn_eq, isw_traceForm_add_smul_left, isw_traceForm_add_smul_left,
      isw_traceForm_add_smul_right, isw_traceForm_add_smul_right]
  have hl : ∀ p q : ℝ, HasDerivAt (fun s : ℝ ↦ p + s * q) q 0 := fun p q ↦ by
    simpa using ((hasDerivAt_id' (0 : ℝ)).mul_const q).const_add p
  have h := ((hl (traceForm ΛR (controlMatrix (vertex 1)))
      (traceForm δΛR (controlMatrix (vertex 1)))).fun_div
      (hl (traceForm (controlMatrix (vertex 1)) X) (traceForm (controlMatrix (vertex 1)) δX))
      (by simpa using h1)).fun_sub
    ((hl (traceForm ΛR (controlMatrix (vertex 2)))
      (traceForm δΛR (controlMatrix (vertex 2)))).fun_div
      (hl (traceForm (controlMatrix (vertex 2)) X) (traceForm (controlMatrix (vertex 2)) δX))
      (by simpa using h2))
  rw [key]
  convert h using 1
  simp only [isw_dchi32, controlP, traceForm, Matrix.mul_sub, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul, zero_mul, add_zero]
  simp only [traceForm] at h1 h2
  field_simp
  ring

/-- The Poisson-bracket identity behind `iso_edge_slope`, for arbitrary `2 × 2` matrices. Put
`P = μA + (1 - μ)B`, `K = -Λ₁ - (3/2)J` and freeze `⟨Λ_R, A⟩ = ⟨Λ_R, B⟩ = ⟨Λ_R, P⟩ = c`. The
vector field `V_P = ([P, X], [P, Λ_R] - c[P, X] + [K, X])` is then `μV_A + (1 - μ)V_B`, and the
derivative `⟨δΛ_R, A - B⟩ - c⟨A, δX⟩ + c⟨B, δX⟩` of `χ₃₂` takes the same value
`⟨Λ_R, [A, B]⟩ + 2c⟨X, [B, A]⟩ + ⟨[K, X], A - B⟩` along `V_A` and `V_B`. -/
private lemma isw_core (A B X ΛR K : Mat2) (μ c : ℝ) :
    traceForm (((μ • A + (1 - μ) • B) * ΛR - ΛR * (μ • A + (1 - μ) • B)) -
          c • ((μ • A + (1 - μ) • B) * X - X * (μ • A + (1 - μ) • B)) + (K * X - X * K))
        (A - B) -
      c * traceForm A ((μ • A + (1 - μ) • B) * X - X * (μ • A + (1 - μ) • B)) +
      c * traceForm B ((μ • A + (1 - μ) • B) * X - X * (μ • A + (1 - μ) • B)) =
    traceForm ((B * ΛR - ΛR * B) - c • (B * X - X * B) + (K * X - X * K)) (A - B) -
      c * traceForm A (B * X - X * B) + c * traceForm B (B * X - X * B) := by
  simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- `Z_u = u₂ Z_{e₂} + u₃ Z_{e₃}` for a control with `u₁ = 0`. -/
lemma isw_controlMatrix_edge (u : Fin 3 → ℝ) (hu0 : u 0 = 0) :
    controlMatrix u = u 1 • controlMatrix (vertex 1) + u 2 • controlMatrix (vertex 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [controlMatrix, vertex, hu0] <;> ring

/-- For a control `u` on the edge `[e₂, e₃]` and a star state `X`, `P_u` is the convex
combination `μP₂ + (1 - μ)P₃`, `μ = u₂⟨Z_{e₂}, X⟩/⟨Z_u, X⟩`. -/
lemma isw_controlP_edge {u : Fin 3 → ℝ} (hu : u ∈ controlSimplex) (hu0 : u 0 = 0) {X : Mat2}
    (hX : IsStarState X) :
    controlP u X =
      (u 1 * traceForm (controlMatrix (vertex 1)) X / traceForm (controlMatrix u) X) •
          controlP (vertex 1) X +
        (1 - u 1 * traceForm (controlMatrix (vertex 1)) X / traceForm (controlMatrix u) X) •
          controlP (vertex 2) X := by
  have ha := (poly_traceForm_neg (poly_vertex_mem 1) hX).ne
  have hb := (poly_traceForm_neg (poly_vertex_mem 2) hX).ne
  have hd := (poly_traceForm_neg hu hX).ne
  have hZ := isw_controlMatrix_edge u hu0
  have hdeq : traceForm (controlMatrix u) X = u 1 * traceForm (controlMatrix (vertex 1)) X +
      u 2 * traceForm (controlMatrix (vertex 2)) X := by
    rw [hZ]
    simp only [traceForm, Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul,
      smul_eq_mul]
  rw [controlP, controlP, controlP]
  generalize traceForm (controlMatrix u) X = d at hdeq hd ⊢
  rw [hZ, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
  congr 2
  · field_simp
  · field_simp
    linear_combination (-1 : ℝ) * hdeq

/-- On the switching surface `χ₂₃ = 0`, the derivative of `χ₃₂` along the state–costate vector
field is the same for every control `u` on the edge `[e₂, e₃]` of `U_T` (it is the Poisson
bracket `{H₃, H₂}`: the Hamiltonian vector field of `H_u` is a convex combination of those of
`H₂` and `H₃` where `H₂ = H₃`). With `iso_chi32_hasDerivAt` this excludes singular arcs and
chattering near the octagon's switching points. -/
theorem iso_edge_slope (q : iso_PhasePt) (hstar : IsStarState q.1)
    (hχ : switchingFn 1 2 q.2.2 q.1 = 0) (u : Fin 3 → ℝ) (hu : u ∈ controlSimplex) (hu0 : u 0 = 0) :
    HasDerivAt (fun s : ℝ ↦ switchingFn 2 1 (q.2.2 + s • (iso_extremalField u q).2.2)
        (q.1 + s • (iso_extremalField u q).1))
      (deriv (fun s : ℝ ↦ switchingFn 2 1 (q.2.2 + s • (iso_extremalField (vertex 2) q).2.2)
        (q.1 + s • (iso_extremalField (vertex 2) q).1)) 0) 0 := by
  have ha := (poly_traceForm_neg (poly_vertex_mem 1) hstar).ne
  have hb := (poly_traceForm_neg (poly_vertex_mem 2) hstar).ne
  rw [(isw_hasDerivAt_chi32_line _ _ _ _ ha hb).deriv]
  refine (isw_hasDerivAt_chi32_line _ _ _ _ ha hb).congr_deriv ?_
  -- on the surface `χ₂₃ = 0`: `⟨Λ_R, P₂⟩ = ⟨Λ_R, P₃⟩ = ⟨Λ_R, P_u⟩`
  have hc : traceForm q.2.2 (controlP (vertex 1) q.1) =
      traceForm q.2.2 (controlP (vertex 2) q.1) := by
    rw [switchingFn, traceForm, Matrix.mul_sub, Matrix.trace_sub, sub_eq_zero] at hχ
    exact hχ.symm
  have hPu := isw_controlP_edge hu hu0 hstar
  have hcu : traceForm q.2.2 (controlP u q.1) = traceForm q.2.2 (controlP (vertex 2) q.1) := by
    rw [hPu]
    simp only [traceForm, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
      smul_eq_mul] at hc ⊢
    rw [hc]
    ring
  simp only [isw_dchi32, iso_extremalField, costateRHS]
  rw [hcu, hc, hPu]
  exact isw_core _ _ _ _ _ _ _

/-- The slope of the remark after Lemma 7.5.3 is positive: `4 - Y - Y ln(4/Y) > 0` for
`Y = 1 + 3y₀² ∈ (2, 4)`, by `ln x < x - 1` (`x = 4/Y ≠ 1`). -/
theorem iso_chi32Slope_pos (y0 : ℝ) (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) : 0 < iso_chi32Slope y0 := by
  obtain ⟨hY2, hY4⟩ := hmax_y_mem hy0 hy1
  have hy : 0 < y0 := poly_y0_pos hy0
  have hYpos : 0 < 1 + 3 * y0 ^ 2 := by linarith
  have hlog : ellSw y0 < 4 / (1 + 3 * y0 ^ 2) - 1 := by
    rw [ellSw, show 3 * y0 ^ 2 + 1 = 1 + 3 * y0 ^ 2 by ring]
    refine Real.log_lt_sub_one_of_pos (by positivity) fun h ↦ ?_
    rw [div_eq_one_iff_eq hYpos.ne'] at h
    linarith
  have hkey : 0 < 4 - (1 + 3 * y0 ^ 2) - (1 + 3 * y0 ^ 2) * ellSw y0 := by
    have h' := mul_lt_mul_of_pos_left hlog hYpos
    rw [mul_sub, mul_div_cancel₀ _ hYpos.ne', mul_one] at h'
    linarith
  unfold iso_chi32Slope
  positivity

end SmoothedPolygons
