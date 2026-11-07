module

public import SmoothedPolygons.Ch7.Polygon

/-!
# One edge of the triangle: the strong transversality conditions (Theorem 7.5.1)

On the first switching interval `[0, t_sw]`, with constant control `e₃` from `z₀ = i y₀`, the state
trajectory lifts, uniquely up to a scalar, to a costate trajectory `(Λ₁, Λ_R, λ_cost)` with
`Λ_R(0) ⊥ X(0)`, `χ₂₃(0) = 0`, `H = 0`, `χ₃₁(t_sw) = 0` and the strong transversality conditions
`Λ_R(t_sw) = R⁻¹Λ_R(0)R`, `Λ₁(t_sw) = R⁻¹Λ₁(0)R`; the lift is normal.

The switching functions `χ_ij` of the book (`eqn:switch`) are indexed by the vertices `e₁, e₂, e₃`
of `U_T`; here they are indexed by `Fin 3`, with `e₁, e₂, e₃` as `0, 1, 2`.
-/

@[expose] public section

namespace SmoothedPolygons

open Matrix

/-- The switching function `χ_ij = ⟨Λ_R, P_j - P_i⟩` (`eqn:switch`), with
`P_k = Z_{e_k}/⟨Z_{e_k}, X⟩`; `χ_ij = H(e_i) - H(e_j)`. Indices: `0, 1, 2` stand for the book's
`1, 2, 3`. The book evaluates `P_{i,i}` at the initial `X₀`; along the constant control `e_i` it
is constant (Lemma 7.1.1), so both forms agree. -/
noncomputable def switchingFn (i j : Fin 3) (ΛR X : Mat2) : ℝ :=
  traceForm ΛR (controlP (vertex j) X - controlP (vertex i) X)

/-- The conditions of Theorem 7.5.1 on a costate lift `(Λ₁, Λ_R, λ_cost)` of the `e₃`-trajectory
`X(t) = X(z₀, t)` on `[0, t_sw]`, `z₀ = i y₀`: traceless costates solving the costate equations
with control `e₃`; `Λ_R(0) ∈ X(0)^⊥` and `χ₂₃(0) = 0` (`eqn:init-lambdaR`); `H_{u=e₃} = 0` and
`χ₃₁(t_sw) = 0` (`eqn:init-H-chi`); and the strong transversality conditions
`Λ_R(t_sw) = R⁻¹Λ_R(0)R`, `Λ₁(t_sw) = R⁻¹Λ₁(0)R`. -/
def IsStrongLift (y0 : ℝ) (Λ₁ ΛR : ℝ → Mat2) (lam : ℝ) : Prop :=
  (∀ t ∈ Set.Icc 0 (switchTime y0), (Λ₁ t).trace = 0 ∧ (ΛR t).trace = 0) ∧
    (∀ t ∈ Set.Icc 0 (switchTime y0), HasDerivWithinAtEntrywise Λ₁
      (Λ₁ t * segX y0 t - segX y0 t * Λ₁ t) (Set.Icc 0 (switchTime y0)) t) ∧
    (∀ t ∈ Set.Icc 0 (switchTime y0), HasDerivWithinAtEntrywise ΛR
      (costateRHS lam (Λ₁ t) (ΛR t) (segX y0 t) (vertex 2)) (Set.Icc 0 (switchTime y0)) t) ∧
    traceForm (ΛR 0) (segX y0 0) = 0 ∧ switchingFn 1 2 (ΛR 0) (segX y0 0) = 0 ∧
    hamiltonian lam (Λ₁ 0) (ΛR 0) (segX y0 0) (vertex 2) = 0 ∧
    switchingFn 2 0 (ΛR (switchTime y0)) (segX y0 (switchTime y0)) = 0 ∧
    ΛR (switchTime y0) = R⁻¹ * ΛR 0 * R ∧ Λ₁ (switchTime y0) = R⁻¹ * Λ₁ 0 * R

/-! ### The explicit costate lift

Closed forms of the costate trajectories with constant control `e₃` from `z₀ = i y₀`, computed
from the general solution of §7.1 (`Λ₁(t) = g(t)⁻¹Λ₁(0)g(t)` and the quadrature formula for `Λ_R`).
With `W = exp(√3 y₀ t)`, the solution of the costate equation for `Λ_R` with
`Λ₁(0) = l₁ Λ₁₀`, `Λ_R(0) = l_R [[0, y₀²], [1, 0]]` and multiplier `λ_cost = lam` is `costateΛR`.
-/

/-- `ℓ(y₀) = ln(4/(3y₀² + 1)) = √3 y₀ t_sw`. -/
noncomputable def ellSw (y0 : ℝ) : ℝ := Real.log (4 / (3 * y0 ^ 2 + 1))

/-- The generator `Λ₁₀ = h - (tr h/2) I₂` of the centralizer of `h = g(t_sw)R⁻¹` in `𝔰𝔩₂(ℝ)`
(proof of Theorem 7.5.1). -/
noncomputable def Λ₁₀ (y0 : ℝ) : Mat2 :=
  (2 * y0 ^ 2 * (1 + 3 * y0 ^ 2))⁻¹ •
    !![0, 4 * √3 * y0 ^ 4; -(√3 * (1 + y0 ^ 2) * (3 * y0 ^ 2 - 1)), 0]

/-- The value `λ₁` of the proof of Theorem 7.5.1 (for `λ_cost = -1`). -/
noncomputable def strongL₁ (y0 : ℝ) : ℝ :=
  -((1 + 3 * y0 ^ 2) * (-3 - 6 * y0 ^ 2 + (1 + 3 * y0 ^ 2) * ellSw y0)) / (12 * √3 * y0 ^ 4)

/-- The value `λ_R` of the proof of Theorem 7.5.1 (for `λ_cost = -1`). -/
noncomputable def strongLR (y0 : ℝ) : ℝ :=
  -(3 - 12 * y0 ^ 2 - 9 * y0 ^ 4 + 18 * y0 ^ 6 +
    (-1 + 3 * y0 ^ 2 + 21 * y0 ^ 4 + 9 * y0 ^ 6) * ellSw y0) / (24 * y0 ^ 6)

/-- The `(0, 0)` entry of `costateΛR`. -/
noncomputable def costateΛR₀₀ (y0 l1 lR lam t : ℝ) : ℝ :=
  let W : ℝ := Real.exp (√3 * y0 * t)
  (9*√3*t*W*l1*y0^5 + 18*√3*t*W*l1*y0^3 - 3*√3*t*W*l1*y0 - 18*t*W*lR*y0^5 - 6*t*W*lR*y0^3 +
    27*t*W*lam*y0^5 + 72*t*W*lam*y0^3 + 21*t*W*lam*y0 + 9*W^3*l1*y0^4 + 6*W^3*l1*y0^2 + W^3*l1 +
    9*√3*W^3*lam*y0^4 + 6*√3*W^3*lam*y0^2 + √3*W^3*lam - 18*W^2*l1*y0^4 - 24*W^2*l1*y0^2 -
    6*W^2*l1 + 6*√3*W^2*lR*y0^4 + 2*√3*W^2*lR*y0^2 - 18*√3*W^2*lam*y0^4 - 30*√3*W^2*lam*y0^2 -
    8*√3*W^2*lam + 9*W*l1*y0^4 + 6*W*l1*y0^2 + 9*W*l1 - 6*√3*W*lR*y0^4 - 2*√3*W*lR*y0^2 +
    9*√3*W*lam*y0^4 + 12*√3*W*lam*y0^2 + 3*√3*W*lam + 12*l1*y0^2 - 4*l1 + 12*√3*lam*y0^2 +
    4*√3*lam) / (18*W^2*y0^4 + 6*W^2*y0^2)

/-- The `(0, 1)` entry of `costateΛR`. -/
noncomputable def costateΛR₀₁ (y0 l1 lR lam t : ℝ) : ℝ :=
  let W : ℝ := Real.exp (√3 * y0 * t)
  (-81*t*W^3*l1*y0^7 - 189*t*W^3*l1*y0^5 - 27*t*W^3*l1*y0^3 + 9*t*W^3*l1*y0 + 54*√3*t*W^3*lR*y0^7
    + 36*√3*t*W^3*lR*y0^5 + 6*√3*t*W^3*lR*y0^3 - 81*√3*t*W^3*lam*y0^7 - 243*√3*t*W^3*lam*y0^5 -
    135*√3*t*W^3*lam*y0^3 - 21*√3*t*W^3*lam*y0 + 27*t*W*l1*y0^5 + 54*t*W*l1*y0^3 - 9*t*W*l1*y0 -
    18*√3*t*W*lR*y0^5 - 6*√3*t*W*lR*y0^3 + 27*√3*t*W*lam*y0^5 + 72*√3*t*W*lam*y0^3 +
    21*√3*t*W*lam*y0 + 27*√3*W^4*l1*y0^6 + 9*√3*W^4*l1*y0^4 - 3*√3*W^4*l1*y0^2 - √3*W^4*l1 +
    81*W^4*lam*y0^6 + 81*W^4*lam*y0^4 + 27*W^4*lam*y0^2 + 3*W^4*lam - 27*√3*W^3*l1*y0^6 +
    45*√3*W^3*l1*y0^4 + 39*√3*W^3*l1*y0^2 + 7*√3*W^3*l1 + 54*W^3*lR*y0^6 - 6*W^3*lR*y0^2 -
    81*W^3*lam*y0^6 + 81*W^3*lam*y0^4 + 153*W^3*lam*y0^2 + 39*W^3*lam - 63*√3*W^2*l1*y0^4 -
    66*√3*W^2*l1*y0^2 - 15*√3*W^2*l1 + 36*W^2*lR*y0^4 + 12*W^2*lR*y0^2 - 189*W^2*lam*y0^4 -
    288*W^2*lam*y0^2 - 75*W^2*lam + 9*√3*W*l1*y0^4 + 18*√3*W*l1*y0^2 + 13*√3*W*l1 - 18*W*lR*y0^4
    - 6*W*lR*y0^2 + 27*W*lam*y0^4 + 72*W*lam*y0^2 + 21*W*lam + 12*√3*l1*y0^2 - 4*√3*l1 +
    36*lam*y0^2 + 12*lam) / (54*W^2*y0^4 + 18*W^2*y0^2)

/-- The `(1, 0)` entry of `costateΛR`. -/
noncomputable def costateΛR₁₀ (y0 l1 lR lam t : ℝ) : ℝ :=
  let W : ℝ := Real.exp (√3 * y0 * t)
  (-27*t*W*l1*y0^5 - 54*t*W*l1*y0^3 + 9*t*W*l1*y0 + 18*√3*t*W*lR*y0^5 + 6*√3*t*W*lR*y0^3 -
    27*√3*t*W*lam*y0^5 - 72*√3*t*W*lam*y0^3 - 21*√3*t*W*lam*y0 + 9*√3*W^2*l1*y0^4 +
    6*√3*W^2*l1*y0^2 + √3*W^2*l1 + 27*W^2*lam*y0^4 + 36*W^2*lam*y0^2 + 9*W^2*lam - 9*√3*W*l1*y0^4
    + 6*√3*W*l1*y0^2 - 5*√3*W*l1 + 18*W*lR*y0^4 + 6*W*lR*y0^2 - 27*W*lam*y0^4 + 3*W*lam -
    12*√3*l1*y0^2 + 4*√3*l1 - 36*lam*y0^2 - 12*lam) / (18*W^2*y0^4 + 6*W^2*y0^2)

/-- The solution `Λ_R(t)` of the costate equation with control `e₃` along the `e₃`-trajectory from
`z₀ = i y₀`, with `Λ₁(0) = l1 Λ₁₀`, `Λ_R(0) = lR [[0, y₀²], [1, 0]]` and `λ_cost = lam`
(closed form, `W = exp(√3 y₀ t)`). -/
noncomputable def costateΛR (y0 l1 lR lam t : ℝ) : Mat2 :=
  !![costateΛR₀₀ y0 l1 lR lam t, costateΛR₀₁ y0 l1 lR lam t;
    costateΛR₁₀ y0 l1 lR lam t, -costateΛR₀₀ y0 l1 lR lam t]

/-- The costate `Λ₁(t) = g(t)⁻¹ (λ₁ Λ₁₀) g(t)` of the strong lift. -/
noncomputable def strongΛ₁ (y0 t : ℝ) : Mat2 :=
  (segG y0 t)⁻¹ * (strongL₁ y0 • Λ₁₀ y0) * segG y0 t

/-- The costate `Λ_R(t)` of the strong lift (`λ_cost = -1`). -/
noncomputable def strongΛR (y0 t : ℝ) : Mat2 := costateΛR y0 (strongL₁ y0) (strongLR y0) (-1) t

/-! ### Computations along the `e₃`-trajectory -/

/-- `⟨Z_{e₁}, Φ(x + iy)⟩ = (1 - 3(x² + y²))/(3y)`. -/
lemma str_traceForm_Z1_Φ (x y : ℝ) :
    traceForm (controlMatrix (vertex 0)) (Φ x y) = (1 - 3 * (x ^ 2 + y ^ 2)) / (3 * y) := by
  simp [traceForm, controlMatrix, vertex, Φ, Matrix.trace_fin_two]
  field_simp
  ring

/-- `⟨Z_{e₂}, Φ(x + iy)⟩ = 2(√3 x - 1)/(3y)`. -/
lemma str_traceForm_Z2_Φ (x y : ℝ) :
    traceForm (controlMatrix (vertex 1)) (Φ x y) = 2 * (√3 * x - 1) / (3 * y) := by
  have h3 : (0 : ℝ) < √3 := by positivity
  simp [traceForm, controlMatrix, vertex, Φ, Matrix.trace_fin_two]
  field_simp
  linear_combination (-(2 * x * y⁻¹)) * str_sqrt3_sq

/-- Along the `e₃`-trajectory `P = Z_{e₃}/⟨Z_{e₃}, X⟩` is the constant `P₀` (Lemma 7.1.1, here by
the closed form): `⟨Z_{e₃}, X(t)⟩ = -2/(3y₀)`. -/
lemma str_controlP_segX (y0 t : ℝ) (hy0 : 0 < y0) :
    controlP (vertex 2) (segX y0 t) = !![√3 * y0 / 2, y0; 0, -(√3 * y0 / 2)] := by
  have h3 : (0 : ℝ) < √3 := by positivity
  have hW := Real.exp_pos (√3 * y0 * t)
  have h : traceForm (controlMatrix (vertex 2)) (segX y0 t) =
      traceForm (controlMatrix (vertex 2)) (Φ 0 y0) := by
    rw [segX_eq y0 t hy0, str_traceForm_Z3_Φ, str_traceForm_Z3_Φ]
    field_simp
    ring
  rw [← str_segP_eq y0 hy0.ne', segP, controlP, controlP, h]

/-- The inverse of a `2 × 2` matrix of determinant one. -/
lemma str_inv_of_det_eq_one (M : Mat2) (h : M.det = 1) :
    M⁻¹ = !![M 1 1, -M 0 1; -M 1 0, M 0 0] := by
  refine Matrix.inv_eq_left_inv ?_
  rw [Matrix.det_fin_two] at h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linarith

/-- The closed form of `g(t)⁻¹ Λ₁₀ g(t)` in terms of `W = exp(√3 y₀ t)`. -/
noncomputable def str_Λ₁W (y0 l1 W : ℝ) : Mat2 :=
  !![l1 * (W - 1) * (-3 * W ^ 2 * (y0 ^ 2 + 1) * (3 * y0 ^ 2 - 1) + 12 * W * y0 ^ 2 -
        4 * W * (W - 2) - 4) / (6 * W ^ 2 * y0 ^ 2 * (3 * y0 ^ 2 + 1)),
    √3 * l1 * (3 * W ^ 2 * (W - 1) ^ 2 * (y0 ^ 2 + 1) * (3 * y0 ^ 2 - 1) +
        4 * (3 * W * y0 ^ 2 - W * (W - 2) - 1) ^ 2) / (18 * W ^ 2 * y0 ^ 2 * (3 * y0 ^ 2 + 1));
    √3 * l1 * (-3 * W ^ 2 * (y0 ^ 2 + 1) * (3 * y0 ^ 2 - 1) - 4 * (W - 1) ^ 2) /
      (6 * W ^ 2 * y0 ^ 2 * (3 * y0 ^ 2 + 1)),
    -(l1 * (W - 1) * (-3 * W ^ 2 * (y0 ^ 2 + 1) * (3 * y0 ^ 2 - 1) + 12 * W * y0 ^ 2 -
        4 * W * (W - 2) - 4) / (6 * W ^ 2 * y0 ^ 2 * (3 * y0 ^ 2 + 1)))]

/-- `Λ₁(t) = g(t)⁻¹ (l₁Λ₁₀) g(t)` in closed form. -/
lemma str_Λ₁_eq (y0 l1 t : ℝ) (hy0 : 0 < y0) :
    (segG y0 t)⁻¹ * (l1 • Λ₁₀ y0) * segG y0 t = str_Λ₁W y0 l1 (Real.exp (√3 * y0 * t)) := by
  have h3 : (0 : ℝ) < √3 := by positivity
  have hW := Real.exp_pos (√3 * y0 * t)
  rw [str_inv_of_det_eq_one _ ((seg_solution y0 t hy0).2.2.2.2 t), segG_eq y0 t hy0]
  simp only [Λ₁₀, str_Λ₁W]
  generalize Real.exp (√3 * y0 * t) = W at hW ⊢
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
    ring_nf <;> simp only [str_sqrt3_sq] <;> ring_nf

/-- A function `(A(W) + s B(W))/(D W²)` with `W = exp(κ s)`, `A` a polynomial of degree `4` and
`B = B₁W + B₃W³`: the shape of the entries of `costateΛR`. -/
noncomputable def str_gen (κ D A0 A1 A2 A3 A4 B1 B3 s : ℝ) : ℝ :=
  (A0 + A1 * Real.exp (κ * s) + A2 * Real.exp (κ * s) ^ 2 + A3 * Real.exp (κ * s) ^ 3 +
      A4 * Real.exp (κ * s) ^ 4 + s * (B1 * Real.exp (κ * s) + B3 * Real.exp (κ * s) ^ 3)) /
    (D * Real.exp (κ * s) ^ 2)

/-- The derivative of `str_gen`. -/
noncomputable def str_gen_deriv (κ D A0 A1 _A2 A3 A4 B1 B3 t : ℝ) : ℝ :=
  (-2 * κ * A0 + (B1 - κ * (A1 + t * B1)) * Real.exp (κ * t) +
      (B3 + κ * (A3 + t * B3)) * Real.exp (κ * t) ^ 3 + 2 * κ * A4 * Real.exp (κ * t) ^ 4) /
    (D * Real.exp (κ * t) ^ 2)

private lemma str_hasDerivAt_gen (κ D A0 A1 A2 A3 A4 B1 B3 t : ℝ) (hD : D ≠ 0) :
    HasDerivAt (str_gen κ D A0 A1 A2 A3 A4 B1 B3) (str_gen_deriv κ D A0 A1 A2 A3 A4 B1 B3 t) t := by
  have hW : HasDerivAt (fun s ↦ Real.exp (κ * s)) (Real.exp (κ * t) * κ) t := by
    simpa using ((hasDerivAt_id t).const_mul κ).exp
  have hs : HasDerivAt (fun s : ℝ ↦ s) 1 t := hasDerivAt_id t
  have hN := (((((hasDerivAt_const t A0).fun_add (hW.const_mul A1)).fun_add
    ((hW.fun_pow 2).const_mul A2)).fun_add ((hW.fun_pow 3).const_mul A3)).fun_add
    ((hW.fun_pow 4).const_mul A4)).fun_add
    (hs.fun_mul ((hW.const_mul B1).fun_add ((hW.fun_pow 3).const_mul B3)))
  have hDn := (hW.fun_pow 2).const_mul D
  have hE := Real.exp_pos (κ * t)
  have h := hN.fun_div hDn (by positivity)
  unfold str_gen str_gen_deriv
  convert h using 1
  field_simp
  ring

/-- The entry `00` of `costateΛR` as a Laurent polynomial in `W`, affine in `t`. -/
private lemma str_00_hasDerivAt (y0 l1 lR lam t : ℝ) (hy0 : 0 < y0) :
    HasDerivAt (fun s ↦ costateΛR₀₀ y0 l1 lR lam s)
      (str_gen_deriv (√3 * y0) (18 * y0 ^ 4 + 6 * y0 ^ 2)
        (12*l1*y0^2 - 4*l1 + 12*√3*lam*y0^2 + 4*√3*lam)
        (9*l1*y0^4 + 6*l1*y0^2 + 9*l1 - 6*√3*lR*y0^4 - 2*√3*lR*y0^2 + 9*√3*lam*y0^4 +
        12*√3*lam*y0^2 + 3*√3*lam)
        (-18*l1*y0^4 - 24*l1*y0^2 - 6*l1 + 6*√3*lR*y0^4 + 2*√3*lR*y0^2 - 18*√3*lam*y0^4 -
        30*√3*lam*y0^2 - 8*√3*lam)
        (9*l1*y0^4 + 6*l1*y0^2 + l1 + 9*√3*lam*y0^4 + 6*√3*lam*y0^2 + √3*lam)
        (0)
        (9*√3*l1*y0^5 + 18*√3*l1*y0^3 - 3*√3*l1*y0 - 18*lR*y0^5 - 6*lR*y0^3 + 27*lam*y0^5 +
        72*lam*y0^3 + 21*lam*y0)
        (0)
        t) t := by
  have hfun : (fun s ↦ costateΛR₀₀ y0 l1 lR lam s) =
      str_gen (√3 * y0) (18 * y0 ^ 4 + 6 * y0 ^ 2)
      (12*l1*y0^2 - 4*l1 + 12*√3*lam*y0^2 + 4*√3*lam)
      (9*l1*y0^4 + 6*l1*y0^2 + 9*l1 - 6*√3*lR*y0^4 - 2*√3*lR*y0^2 + 9*√3*lam*y0^4 + 12*√3*lam*y0^2
      + 3*√3*lam)
      (-18*l1*y0^4 - 24*l1*y0^2 - 6*l1 + 6*√3*lR*y0^4 + 2*√3*lR*y0^2 - 18*√3*lam*y0^4 -
      30*√3*lam*y0^2 - 8*√3*lam)
      (9*l1*y0^4 + 6*l1*y0^2 + l1 + 9*√3*lam*y0^4 + 6*√3*lam*y0^2 + √3*lam)
      (0)
      (9*√3*l1*y0^5 + 18*√3*l1*y0^3 - 3*√3*l1*y0 - 18*lR*y0^5 - 6*lR*y0^3 + 27*lam*y0^5 +
      72*lam*y0^3 + 21*lam*y0)
      (0)
      := by
    funext s
    simp only [costateΛR₀₀, str_gen]
    ring
  rw [hfun]
  exact str_hasDerivAt_gen _ _ _ _ _ _ _ _ _ t (by positivity)

/-- The entry `01` of `costateΛR` as a Laurent polynomial in `W`, affine in `t`. -/
private lemma str_01_hasDerivAt (y0 l1 lR lam t : ℝ) (hy0 : 0 < y0) :
    HasDerivAt (fun s ↦ costateΛR₀₁ y0 l1 lR lam s)
      (str_gen_deriv (√3 * y0) (54 * y0 ^ 4 + 18 * y0 ^ 2)
        (12*√3*l1*y0^2 - 4*√3*l1 + 36*lam*y0^2 + 12*lam)
        (9*√3*l1*y0^4 + 18*√3*l1*y0^2 + 13*√3*l1 - 18*lR*y0^4 - 6*lR*y0^2 + 27*lam*y0^4 +
        72*lam*y0^2 + 21*lam)
        (-63*√3*l1*y0^4 - 66*√3*l1*y0^2 - 15*√3*l1 + 36*lR*y0^4 + 12*lR*y0^2 - 189*lam*y0^4 -
        288*lam*y0^2 - 75*lam)
        (-27*√3*l1*y0^6 + 45*√3*l1*y0^4 + 39*√3*l1*y0^2 + 7*√3*l1 + 54*lR*y0^6 - 6*lR*y0^2 -
        81*lam*y0^6 + 81*lam*y0^4 + 153*lam*y0^2 + 39*lam)
        (27*√3*l1*y0^6 + 9*√3*l1*y0^4 - 3*√3*l1*y0^2 - √3*l1 + 81*lam*y0^6 + 81*lam*y0^4 +
        27*lam*y0^2 + 3*lam)
        (27*l1*y0^5 + 54*l1*y0^3 - 9*l1*y0 - 18*√3*lR*y0^5 - 6*√3*lR*y0^3 + 27*√3*lam*y0^5 +
        72*√3*lam*y0^3 + 21*√3*lam*y0)
        (-81*l1*y0^7 - 189*l1*y0^5 - 27*l1*y0^3 + 9*l1*y0 + 54*√3*lR*y0^7 + 36*√3*lR*y0^5 +
        6*√3*lR*y0^3 - 81*√3*lam*y0^7 - 243*√3*lam*y0^5 - 135*√3*lam*y0^3 - 21*√3*lam*y0)
        t) t := by
  have hfun : (fun s ↦ costateΛR₀₁ y0 l1 lR lam s) =
      str_gen (√3 * y0) (54 * y0 ^ 4 + 18 * y0 ^ 2)
      (12*√3*l1*y0^2 - 4*√3*l1 + 36*lam*y0^2 + 12*lam)
      (9*√3*l1*y0^4 + 18*√3*l1*y0^2 + 13*√3*l1 - 18*lR*y0^4 - 6*lR*y0^2 + 27*lam*y0^4 +
      72*lam*y0^2 + 21*lam)
      (-63*√3*l1*y0^4 - 66*√3*l1*y0^2 - 15*√3*l1 + 36*lR*y0^4 + 12*lR*y0^2 - 189*lam*y0^4 -
      288*lam*y0^2 - 75*lam)
      (-27*√3*l1*y0^6 + 45*√3*l1*y0^4 + 39*√3*l1*y0^2 + 7*√3*l1 + 54*lR*y0^6 - 6*lR*y0^2 -
      81*lam*y0^6 + 81*lam*y0^4 + 153*lam*y0^2 + 39*lam)
      (27*√3*l1*y0^6 + 9*√3*l1*y0^4 - 3*√3*l1*y0^2 - √3*l1 + 81*lam*y0^6 + 81*lam*y0^4 +
      27*lam*y0^2 + 3*lam)
      (27*l1*y0^5 + 54*l1*y0^3 - 9*l1*y0 - 18*√3*lR*y0^5 - 6*√3*lR*y0^3 + 27*√3*lam*y0^5 +
      72*√3*lam*y0^3 + 21*√3*lam*y0)
      (-81*l1*y0^7 - 189*l1*y0^5 - 27*l1*y0^3 + 9*l1*y0 + 54*√3*lR*y0^7 + 36*√3*lR*y0^5 +
      6*√3*lR*y0^3 - 81*√3*lam*y0^7 - 243*√3*lam*y0^5 - 135*√3*lam*y0^3 - 21*√3*lam*y0)
      := by
    funext s
    simp only [costateΛR₀₁, str_gen]
    ring
  rw [hfun]
  exact str_hasDerivAt_gen _ _ _ _ _ _ _ _ _ t (by positivity)

/-- The entry `10` of `costateΛR` as a Laurent polynomial in `W`, affine in `t`. -/
private lemma str_10_hasDerivAt (y0 l1 lR lam t : ℝ) (hy0 : 0 < y0) :
    HasDerivAt (fun s ↦ costateΛR₁₀ y0 l1 lR lam s)
      (str_gen_deriv (√3 * y0) (18 * y0 ^ 4 + 6 * y0 ^ 2)
        (-12*√3*l1*y0^2 + 4*√3*l1 - 36*lam*y0^2 - 12*lam)
        (-9*√3*l1*y0^4 + 6*√3*l1*y0^2 - 5*√3*l1 + 18*lR*y0^4 + 6*lR*y0^2 - 27*lam*y0^4 + 3*lam)
        (9*√3*l1*y0^4 + 6*√3*l1*y0^2 + √3*l1 + 27*lam*y0^4 + 36*lam*y0^2 + 9*lam)
        (0)
        (0)
        (-27*l1*y0^5 - 54*l1*y0^3 + 9*l1*y0 + 18*√3*lR*y0^5 + 6*√3*lR*y0^3 - 27*√3*lam*y0^5 -
        72*√3*lam*y0^3 - 21*√3*lam*y0)
        (0)
        t) t := by
  have hfun : (fun s ↦ costateΛR₁₀ y0 l1 lR lam s) =
      str_gen (√3 * y0) (18 * y0 ^ 4 + 6 * y0 ^ 2)
      (-12*√3*l1*y0^2 + 4*√3*l1 - 36*lam*y0^2 - 12*lam)
      (-9*√3*l1*y0^4 + 6*√3*l1*y0^2 - 5*√3*l1 + 18*lR*y0^4 + 6*lR*y0^2 - 27*lam*y0^4 + 3*lam)
      (9*√3*l1*y0^4 + 6*√3*l1*y0^2 + √3*l1 + 27*lam*y0^4 + 36*lam*y0^2 + 9*lam)
      (0)
      (0)
      (-27*l1*y0^5 - 54*l1*y0^3 + 9*l1*y0 + 18*√3*lR*y0^5 + 6*√3*lR*y0^3 - 27*√3*lam*y0^5 -
      72*√3*lam*y0^3 - 21*√3*lam*y0)
      (0)
      := by
    funext s
    simp only [costateΛR₁₀, str_gen]
    ring
  rw [hfun]
  exact str_hasDerivAt_gen _ _ _ _ _ _ _ _ _ t (by positivity)

/-- The right-hand side of the costate equation for `Λ_R` (`eqn:lamR`) with `P = [[p, q], [0, -p]]`,
`Λ₁ = [[m₀, m₁], [m₂, -m₀]]`, `Λ_R = [[a, b], [c, -a]]` and `X = Φ(x + iy)`. -/
private lemma str_costateRHS_eq (lam m0 m1 m2 a b c x y p q : ℝ)
    (hP : controlP (vertex 2) (Φ x y) = !![p, q; 0, -p]) :
    costateRHS lam !![m0, m1; m2, -m0] !![a, b; c, -a] (Φ x y) (vertex 2) =
      !![q * c - (2 * a * p + c * q) * (q / y) +
          ((-m1 - 3 / 2 * lam) / y + (x ^ 2 + y ^ 2) / y * (-m2 + 3 / 2 * lam)),
        2 * p * b - 2 * q * a -
          (2 * a * p + c * q) * (-2 * p * (x ^ 2 + y ^ 2) / y - 2 * q * x / y) +
          2 * (m0 * (x ^ 2 + y ^ 2) / y - (-m1 - 3 / 2 * lam) * x / y);
        -2 * p * c + (2 * a * p + c * q) * (2 * p / y) + 2 * ((-m2 + 3 / 2 * lam) * x / y + m0 / y),
        -(q * c - (2 * a * p + c * q) * (q / y) +
          ((-m1 - 3 / 2 * lam) / y + (x ^ 2 + y ^ 2) / y * (-m2 + 3 / 2 * lam)))] := by
  rw [costateRHS, hP]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [traceForm, J, Φ, Matrix.trace_fin_two] <;> ring

set_option maxRecDepth 2000 in
/-- `costateΛR` solves the costate equation for `Λ_R` with control `e₃` along the `e₃`-trajectory,
with `Λ₁(t) = g(t)⁻¹ (l1 Λ₁₀) g(t)`, and has the initial value `lR [[0, y₀²], [1, 0]]`. -/
theorem costateΛR_solution (y0 l1 lR lam : ℝ) (hy0 : 0 < y0) (t : ℝ) :
    HasDerivAtEntrywise (costateΛR y0 l1 lR lam)
        (costateRHS lam ((segG y0 t)⁻¹ * (l1 • Λ₁₀ y0) * segG y0 t) (costateΛR y0 l1 lR lam t)
          (segX y0 t) (vertex 2)) t ∧
      costateΛR y0 l1 lR lam 0 = lR • !![0, y0 ^ 2; 1, 0] := by
  have h3 : (0 : ℝ) < √3 := by positivity
  have hP := str_controlP_segX y0 t hy0
  rw [segX_eq y0 t hy0] at hP
  refine ⟨?_, ?_⟩
  · rw [str_Λ₁_eq y0 l1 t hy0, segX_eq y0 t hy0, costateΛR, str_Λ₁W,
      str_costateRHS_eq _ _ _ _ _ _ _ _ _ _ _ hP]
    have hW := Real.exp_pos (√3 * y0 * t)
    refine Matrix.hasDerivAtEntrywise_fin_two_iff.2 ⟨?_, ?_, ?_, ?_⟩
    · refine (str_00_hasDerivAt y0 l1 lR lam t hy0).congr_deriv ?_
      simp only [str_gen_deriv, costateΛR₀₀, costateΛR₀₁, costateΛR₁₀, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one]
      generalize Real.exp (√3 * y0 * t) = W at hW ⊢
      field_simp
      ring_nf
      simp only [str_sqrt3_sq, str_sqrt3_pow3, str_sqrt3_pow4]
      ring_nf
    · refine (str_01_hasDerivAt y0 l1 lR lam t hy0).congr_deriv ?_
      simp only [str_gen_deriv, costateΛR₀₀, costateΛR₀₁, costateΛR₁₀, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one]
      generalize Real.exp (√3 * y0 * t) = W at hW ⊢
      field_simp
      ring_nf
      simp only [str_sqrt3_sq, str_sqrt3_pow3, str_sqrt3_pow4, str_sqrt3_pow5]
      ring_nf
    · refine (str_10_hasDerivAt y0 l1 lR lam t hy0).congr_deriv ?_
      simp only [str_gen_deriv, costateΛR₀₀, costateΛR₀₁, costateΛR₁₀, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one]
      generalize Real.exp (√3 * y0 * t) = W at hW ⊢
      field_simp
      ring_nf
      simp only [str_sqrt3_sq, str_sqrt3_pow3, str_sqrt3_pow4]
      ring_nf
    · refine (str_00_hasDerivAt y0 l1 lR lam t hy0).neg.congr_deriv ?_
      simp only [str_gen_deriv, costateΛR₀₀, costateΛR₀₁, costateΛR₁₀, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
      generalize Real.exp (√3 * y0 * t) = W at hW ⊢
      field_simp
      ring_nf
      simp only [str_sqrt3_sq, str_sqrt3_pow3, str_sqrt3_pow4]
      ring_nf
  · have h0 : Real.exp (√3 * y0 * 0) = 1 := by simp
    simp only [costateΛR, costateΛR₀₀, costateΛR₀₁, costateΛR₁₀, h0]
    ext i j
    fin_cases i <;> fin_cases j <;> simp only [Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
      field_simp <;> ring

/-! ### Switching functions and the Hamiltonian in coordinates -/

lemma str_traceForm_controlP (Λ X : Mat2) (u : Fin 3 → ℝ) :
    traceForm Λ (controlP u X) =
      traceForm Λ (controlMatrix u) / traceForm (controlMatrix u) X := by
  simp only [controlP, traceForm, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  ring

lemma str_switchingFn_eq (i j : Fin 3) (Λ X : Mat2) :
    switchingFn i j Λ X =
      traceForm Λ (controlMatrix (vertex j)) / traceForm (controlMatrix (vertex j)) X -
        traceForm Λ (controlMatrix (vertex i)) / traceForm (controlMatrix (vertex i)) X := by
  rw [switchingFn, ← str_traceForm_controlP, ← str_traceForm_controlP, traceForm, traceForm,
    traceForm, Matrix.mul_sub, Matrix.trace_sub]

lemma str_traceForm_Z_fin_two (a b c : ℝ) :
    traceForm !![a, b; c, -a] (controlMatrix (vertex 0)) = b + c / 3 ∧
      traceForm !![a, b; c, -a] (controlMatrix (vertex 1)) = 2 * a / √3 - 2 * c / 3 ∧
      traceForm !![a, b; c, -a] (controlMatrix (vertex 2)) = -(2 * a / √3) - 2 * c / 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [traceForm, controlMatrix, vertex, Matrix.trace_fin_two] <;> ring

lemma str_traceForm_Z0_fin_two (a b c : ℝ) :
    traceForm !![a, b; c, -a] (controlMatrix (vertex 0)) = b + c / 3 :=
  (str_traceForm_Z_fin_two a b c).1

lemma str_traceForm_Z1_fin_two (a b c : ℝ) :
    traceForm !![a, b; c, -a] (controlMatrix (vertex 1)) = 2 * a / √3 - 2 * c / 3 :=
  (str_traceForm_Z_fin_two a b c).2.1

lemma str_traceForm_Z2_fin_two (a b c : ℝ) :
    traceForm !![a, b; c, -a] (controlMatrix (vertex 2)) = -(2 * a / √3) - 2 * c / 3 :=
  (str_traceForm_Z_fin_two a b c).2.2

/-- `⟨Z_{eᵢ}, X(t)⟩` along the `e₃`-trajectory, `W = exp(√3 y₀ t)`. -/
lemma str_traceForm_segX (y0 t : ℝ) (hy0 : 0 < y0) :
    traceForm (controlMatrix (vertex 0)) (segX y0 t) =
        (1 - (Real.exp (√3 * y0 * t) - 1) ^ 2 - 3 * y0 ^ 2 * Real.exp (√3 * y0 * t) ^ 2) /
          (3 * y0 * Real.exp (√3 * y0 * t)) ∧
      traceForm (controlMatrix (vertex 1)) (segX y0 t) =
        2 * (Real.exp (√3 * y0 * t) - 2) / (3 * y0 * Real.exp (√3 * y0 * t)) ∧
      traceForm (controlMatrix (vertex 2)) (segX y0 t) = -2 / (3 * y0) := by
  have h3 : (0 : ℝ) < √3 := by positivity
  have hW := Real.exp_pos (√3 * y0 * t)
  rw [segX_eq y0 t hy0, str_traceForm_Z1_Φ, str_traceForm_Z2_Φ, str_traceForm_Z3_Φ]
  generalize Real.exp (√3 * y0 * t) = W at hW ⊢
  refine ⟨?_, ?_, ?_⟩ <;> field_simp
  · ring_nf
    simp only [str_sqrt3_sq]
    ring
  · ring
  · ring

/-- `⟨X, Z_{e₃}⟩ ≠ 0` along the trajectory. -/
lemma str_traceForm_segX_Z3 (y0 t : ℝ) (hy0 : 0 < y0) :
    traceForm (segX y0 t) (controlMatrix (vertex 2)) = -2 / (3 * y0) := by
  rw [traceForm, Matrix.trace_mul_comm, ← traceForm, (str_traceForm_segX y0 t hy0).2.2]

/-! ### The conditions of Theorem 7.5.1 at `t = 0` and `t = t_sw` -/

lemma str_segX_zero (y0 : ℝ) (hy0 : 0 < y0) : segX y0 0 = Φ 0 y0 :=
  (seg_solution y0 0 hy0).2.2.2.1

lemma str_segG_zero (y0 : ℝ) (hy0 : 0 < y0) : segG y0 0 = 1 :=
  (seg_solution y0 0 hy0).2.2.1

/-- `Λ_R(0) ⊥ X(0)` for `Λ_R(0) = l_R [[0, y₀²], [1, 0]]`. -/
lemma str_perp_zero (y0 lR : ℝ) :
    traceForm (lR • !![0, y0 ^ 2; 1, 0]) (Φ 0 y0) = 0 := by
  simp [traceForm, Φ, Matrix.trace_fin_two]
  field_simp
  ring

/-- `χ₂₃(0) = 0` for `Λ_R(0) = l_R [[0, y₀²], [1, 0]]`. -/
lemma str_chi23_zero (y0 lR : ℝ) :
    switchingFn 1 2 (lR • !![0, y0 ^ 2; 1, 0]) (Φ 0 y0) = 0 := by
  rw [str_switchingFn_eq, str_traceForm_Z3_Φ, str_traceForm_Z2_Φ]
  simp [traceForm, controlMatrix, vertex, Matrix.trace_fin_two]

/-- `H(0)` for `Λ₁(0) = l₁Λ₁₀`, `Λ_R(0) = l_R [[0, y₀²], [1, 0]]` (proof of Theorem 7.5.1): a linear
form in `(λ₁, λ_R, λ_cost)`. -/
lemma str_hamiltonian_zero (y0 l1 lR lam : ℝ) (hy0 : 0 < y0) :
    hamiltonian lam (l1 • Λ₁₀ y0) (lR • !![0, y0 ^ 2; 1, 0]) (Φ 0 y0) (vertex 2) =
      ((3 * y0 ^ 4 + 6 * y0 ^ 2 - 1) * (√3 * l1) - (6 * y0 ^ 4 + 2 * y0 ^ 2) * lR +
        (9 * y0 ^ 4 + 12 * y0 ^ 2 + 3) * lam) / (2 * y0 * (3 * y0 ^ 2 + 1)) := by
  have h3 : (0 : ℝ) < √3 := by positivity
  simp [hamiltonian, traceForm, Λ₁₀, J, Φ, controlMatrix, vertex, Matrix.trace_fin_two]
  field_simp
  ring

/-- `⟨Z_{e₁}, X(t_sw)⟩ = -2/(3y₀)`. -/
lemma str_traceForm_Z1_switchTime (y0 : ℝ) (hy0 : 0 < y0) :
    traceForm (controlMatrix (vertex 0)) (segX y0 (switchTime y0)) = -2 / (3 * y0) := by
  rw [(str_traceForm_segX y0 _ hy0).1, str_exp_switchTime hy0]
  field_simp
  ring

/-- `χ₃₁(t_sw)` along `costateΛR` (proof of Theorem 7.5.1): a linear form in
`(λ₁, λ_R, λ_cost)`, `ℓ = ln(4/(3y₀² + 1))`. -/
lemma str_chi31_switchTime (y0 l1 lR lam : ℝ) (hy0 : 0 < y0) :
    switchingFn 2 0 (costateΛR y0 l1 lR lam (switchTime y0)) (segX y0 (switchTime y0)) =
      ((3 * ellSw y0 * y0 ^ 4 + 6 * ellSw y0 * y0 ^ 2 - ellSw y0 + 6 * y0 ^ 4 - 6 * y0 ^ 2) *
          (√3 * l1) - (6 * ellSw y0 * y0 ^ 4 + 2 * ellSw y0 * y0 ^ 2 + 12 * y0 ^ 4) * lR +
        (9 * ellSw y0 * y0 ^ 4 + 24 * ellSw y0 * y0 ^ 2 + 7 * ellSw y0 + 18 * y0 ^ 4 -
          6 * y0 ^ 2 - 12) * lam) / (y0 * (3 * y0 ^ 2 + 1)) := by
  have h3 : (0 : ℝ) < √3 := by positivity
  rw [str_switchingFn_eq, str_traceForm_Z1_switchTime y0 hy0, (str_traceForm_segX y0 _ hy0).2.2,
    costateΛR, (str_traceForm_Z_fin_two _ _ _).1, (str_traceForm_Z_fin_two _ _ _).2.2]
  simp only [costateΛR₀₀, costateΛR₀₁, costateΛR₁₀, str_exp_switchTime hy0]
  rw [show switchTime y0 = ellSw y0 / (√3 * y0) from rfl]
  generalize ellSw y0 = ℓ
  field_simp
  ring_nf
  simp only [str_sqrt3_sq, str_sqrt3_pow3]
  ring_nf

/-- The strong transversality condition for `Λ_R` holds for the values `λ₁`, `λ_R` (the
"remarkable" calculation of the proof of Theorem 7.5.1). -/
lemma str_costateΛR_switchTime (y0 : ℝ) (hy0 : 0 < y0) :
    costateΛR y0 (strongL₁ y0) (strongLR y0) (-1) (switchTime y0) =
      R⁻¹ * costateΛR y0 (strongL₁ y0) (strongLR y0) (-1) 0 * R := by
  have h3 : (0 : ℝ) < √3 := by positivity
  rw [(costateΛR_solution y0 _ _ _ hy0 0).2, str_R_inv]
  simp only [costateΛR, costateΛR₀₀, costateΛR₀₁, costateΛR₁₀, str_exp_switchTime hy0]
  rw [show switchTime y0 = ellSw y0 / (√3 * y0) from rfl]
  simp only [strongL₁, strongLR]
  generalize ellSw y0 = ℓ
  ext i j
  fin_cases i <;> fin_cases j <;> simp [R] <;> field_simp <;> ring_nf <;>
    simp only [str_sqrt3_sq, str_sqrt3_pow4] <;> ring_nf

/-- `Λ₁₀ = h - (tr h/2) I₂` with `h = g(t_sw)R⁻¹` (proof of Theorem 7.5.1). -/
lemma str_Λ₁₀_eq (y0 : ℝ) (hy0 : 1 / √3 < y0) :
    Λ₁₀ y0 = segG y0 (switchTime y0) * R⁻¹ -
      ((segG y0 (switchTime y0) * R⁻¹).trace / 2) • (1 : Mat2) := by
  have h3 : (0 : ℝ) < √3 := by positivity
  have hy0' : 0 < y0 := lt_trans (by positivity) hy0
  rw [trace_segG_switchTime y0 hy0, segG_eq _ _ hy0', str_exp_switchTime hy0', str_R_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Λ₁₀] <;> field_simp <;> ring_nf <;>
    simp only [str_sqrt3_sq] <;> ring_nf

lemma str_R_inv_mul_R : R⁻¹ * R = 1 :=
  Matrix.nonsing_inv_mul R (by rw [str_det_R]; exact isUnit_one)

/-- If `C` commutes with `h = gR⁻¹`, then `g⁻¹Cg = R⁻¹CR` (proof of Theorem 7.5.1). -/
lemma str_conj_eq_of_commute (g C : Mat2) (hg : IsUnit g.det) (hC : C * (g * R⁻¹) = g * R⁻¹ * C) :
    g⁻¹ * C * g = R⁻¹ * C * R := by
  calc g⁻¹ * C * g = g⁻¹ * C * (g * (R⁻¹ * R)) := by rw [str_R_inv_mul_R, mul_one]
    _ = g⁻¹ * (C * (g * R⁻¹)) * R := by simp only [mul_assoc]
    _ = g⁻¹ * (g * R⁻¹ * C) * R := by rw [hC]
    _ = (g⁻¹ * g) * R⁻¹ * C * R := by simp only [mul_assoc]
    _ = R⁻¹ * C * R := by rw [Matrix.nonsing_inv_mul g hg, one_mul]

/-- Conversely, `g⁻¹Ag = R⁻¹AR` means that `A` centralizes `h = gR⁻¹` (proof of Theorem 7.5.1). -/
lemma str_commute_of_conj_eq (g A : Mat2) (hg : IsUnit g.det) (h : g⁻¹ * A * g = R⁻¹ * A * R) :
    A * (g * R⁻¹) = g * R⁻¹ * A := by
  have hR : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R (by rw [str_det_R]; exact isUnit_one)
  calc A * (g * R⁻¹) = g * (g⁻¹ * A * g) * R⁻¹ := by
        simp only [← mul_assoc, Matrix.mul_nonsing_inv g hg, one_mul]
    _ = g * (R⁻¹ * A * R) * R⁻¹ := by rw [h]
    _ = g * R⁻¹ * A * (R * R⁻¹) := by simp only [mul_assoc]
    _ = g * R⁻¹ * A := by rw [hR, mul_one]

/-- `Λ₁(t) = g(t)⁻¹ C g(t)` solves the Lax equation `Λ₁' = [Λ₁, X]` (Corollary 6.5.3). -/
lemma str_conj_hasDerivAt (y0 : ℝ) (hy0 : 0 < y0) (C : Mat2) (t : ℝ) :
    HasDerivAtEntrywise (fun s ↦ (segG y0 s)⁻¹ * C * segG y0 s)
      ((segG y0 t)⁻¹ * C * segG y0 t * segX y0 t - segX y0 t * ((segG y0 t)⁻¹ * C * segG y0 t))
      t := by
  have hg := (seg_solution y0 t hy0).1
  have hdet : IsUnit (segG y0 t).det := by
    rw [(seg_solution y0 t hy0).2.2.2.2 t]; exact isUnit_one
  refine ((hg.inv hdet).mul_const C |>.mul hg).congr_deriv ?_
  have h1 : (segG y0 t)⁻¹ * (segG y0 t * segX y0 t) = segX y0 t := by
    rw [← mul_assoc, Matrix.nonsing_inv_mul _ hdet, one_mul]
  rw [h1]
  simp only [neg_mul, mul_assoc]
  abel

/-- `t_sw > 0`. -/
lemma str_switchTime_pos (y0 : ℝ) (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) : 0 < switchTime y0 := by
  have hy0' : 0 < y0 := lt_trans (by positivity) hy0
  rw [switchTime]
  refine div_pos (Real.log_pos ?_) (by positivity)
  rw [one_lt_div (by positivity)]
  nlinarith

/-- `Λ_R ⊥ X` along `costateΛR` (for all parameters). -/
lemma str_perp_costateΛR (y0 l1 lR lam t : ℝ) (hy0 : 0 < y0) :
    traceForm (costateΛR y0 l1 lR lam t) (segX y0 t) = 0 := by
  have h3 : (0 : ℝ) < √3 := by positivity
  have hW := Real.exp_pos (√3 * y0 * t)
  rw [segX_eq y0 t hy0, costateΛR]
  simp only [traceForm, Φ, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, costateΛR₀₀, costateΛR₀₁, costateΛR₁₀]
  generalize Real.exp (√3 * y0 * t) = W at hW ⊢
  field_simp
  ring_nf
  simp only [str_sqrt3_sq, str_sqrt3_pow3]
  ring_nf

/-- The Hamiltonian along `costateΛR` is constant, equal to its value `H(0)` at `t = 0`. -/
lemma str_hamiltonian_costateΛR (y0 l1 lR lam t : ℝ) (hy0 : 0 < y0) :
    hamiltonian lam ((segG y0 t)⁻¹ * (l1 • Λ₁₀ y0) * segG y0 t) (costateΛR y0 l1 lR lam t)
        (segX y0 t) (vertex 2) =
      ((3 * y0 ^ 4 + 6 * y0 ^ 2 - 1) * (√3 * l1) - (6 * y0 ^ 4 + 2 * y0 ^ 2) * lR +
        (9 * y0 ^ 4 + 12 * y0 ^ 2 + 3) * lam) / (2 * y0 * (3 * y0 ^ 2 + 1)) := by
  have h3 : (0 : ℝ) < √3 := by positivity
  have hW := Real.exp_pos (√3 * y0 * t)
  rw [str_Λ₁_eq y0 l1 t hy0, hamiltonian, str_traceForm_segX_Z3 y0 t hy0, costateΛR,
    str_traceForm_Z2_fin_two, segX_eq y0 t hy0]
  simp only [str_Λ₁W, traceForm, Φ, J, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    costateΛR₀₀, costateΛR₁₀]
  generalize Real.exp (√3 * y0 * t) = W at hW ⊢
  field_simp
  ring_nf
  simp only [str_sqrt3_sq, str_sqrt3_pow3]
  ring_nf

/-- The explicit lift satisfies the conditions of Theorem 7.5.1 with `λ_cost = -1`. -/
theorem strongLift_isStrongLift (y0 : ℝ) (hy0 : 1 / √3 < y0) :
    IsStrongLift y0 (strongΛ₁ y0) (strongΛR y0) (-1) := by
  have h3 : (0 : ℝ) < √3 := by positivity
  have hy0' : 0 < y0 := lt_trans (by positivity) hy0
  have hΛR0 : strongΛR y0 0 = strongLR y0 • !![0, y0 ^ 2; 1, 0] :=
    (costateΛR_solution y0 _ _ _ hy0' 0).2
  have hΛ10 : strongΛ₁ y0 0 = strongL₁ y0 • Λ₁₀ y0 := by
    rw [strongΛ₁, str_segG_zero y0 hy0', inv_one, one_mul, mul_one]
  refine ⟨fun t _ ↦ ⟨?_, ?_⟩, fun t _ ↦ ?_, fun t _ ↦ ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [strongΛ₁, str_Λ₁_eq y0 _ t hy0']
    simp [str_Λ₁W, Matrix.trace_fin_two]
  · simp [strongΛR, costateΛR, Matrix.trace_fin_two]
  · exact (str_conj_hasDerivAt y0 hy0' _ t).hasDerivWithinAtEntrywise
  · exact (costateΛR_solution y0 _ _ _ hy0' t).1.hasDerivWithinAtEntrywise
  · rw [hΛR0, str_segX_zero y0 hy0']
    exact str_perp_zero y0 _
  · rw [hΛR0, str_segX_zero y0 hy0']
    exact str_chi23_zero y0 _
  · rw [hΛR0, hΛ10, str_segX_zero y0 hy0', str_hamiltonian_zero y0 _ _ _ hy0', div_eq_zero_iff]
    left
    simp only [strongL₁, strongLR]
    field_simp
    ring_nf
  · rw [strongΛR, str_chi31_switchTime y0 _ _ _ hy0', div_eq_zero_iff]
    left
    simp only [strongL₁, strongLR]
    generalize ellSw y0 = ℓ
    field_simp
    ring_nf
  · exact str_costateΛR_switchTime y0 hy0'
  · rw [hΛ10, strongΛ₁]
    refine str_conj_eq_of_commute _ _ ?_ ?_
    · rw [(seg_solution y0 0 hy0').2.2.2.2 (switchTime y0)]; exact isUnit_one
    · rw [str_Λ₁₀_eq y0 hy0]
      simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, one_mul,
        mul_one]

/-! ### Uniqueness of the strong lift -/

/-- `costateΛR` is linear in `(λ₁, λ_R, λ_cost)`. -/
lemma str_costateΛR_smul (c y0 l1 lR lam t : ℝ) :
    costateΛR y0 (c * l1) (c * lR) (c * lam) t = c • costateΛR y0 l1 lR lam t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [costateΛR, costateΛR₀₀, costateΛR₀₁, costateΛR₁₀] <;> ring

/-- The centralizer in `𝔰𝔩₂(ℝ)` of `B = [[0, β], [γ, 0]]` with `β ≠ 0` is `ℝB`.

The proof of Theorem 7.5.1: `h = g(t_sw)R⁻¹` is regular (`tr h ∈ (1, 2)`), and its centralizer in
`𝔰𝔩₂(ℝ)` is `ℝΛ₁₀` with `Λ₁₀ = h - (tr h/2) I₂` (`str_Λ₁₀_eq`), since a matrix commutes with `h`
iff it commutes with `Λ₁₀ ≠ 0`, whose centralizer is `ℝΛ₁₀` (`orb_centralizer`). -/
lemma str_centralizer (A B : Mat2) (hA : A.trace = 0) (hB0 : B 0 0 = 0) (hB1 : B 1 1 = 0)
    (hB : B 0 1 ≠ 0) (hc : A * B = B * A) : A = (A 0 1 / B 0 1) • B := by
  have hBtr : B.trace = 0 := by rw [Matrix.trace_fin_two, hB0, hB1, add_zero]
  have hBne : B ≠ 0 := fun h ↦ hB (by rw [h]; rfl)
  obtain ⟨k, hk⟩ := orb_centralizer B A hBtr hBne hA (sub_eq_zero.2 hc)
  have hk' : k = A 0 1 / B 0 1 := by
    rw [hk, Matrix.smul_apply, smul_eq_mul, mul_div_assoc, div_self hB, mul_one]
  rw [← hk']
  exact hk

/-- The two initial conditions `Λ_R(0) ⊥ X(0)` and `χ₂₃(0) = 0` force
`Λ_R(0) = λ_R [[0, y₀²], [1, 0]]` (proof of Theorem 7.5.1). -/
lemma str_ΛR0_eq (y0 : ℝ) (hy0 : 0 < y0) (Λ : Mat2) (htr : Λ.trace = 0)
    (hperp : traceForm Λ (Φ 0 y0) = 0) (hchi : switchingFn 1 2 Λ (Φ 0 y0) = 0) :
    Λ = Λ 1 0 • !![0, y0 ^ 2; 1, 0] := by
  have h3 : (0 : ℝ) < √3 := by positivity
  rw [str_switchingFn_eq, str_traceForm_Z3_Φ, str_traceForm_Z2_Φ] at hchi
  simp [traceForm, controlMatrix, vertex, Φ, Matrix.trace_fin_two, Matrix.mul_apply,
    Fin.sum_univ_two] at hperp hchi
  rw [Matrix.trace_fin_two] at htr
  field_simp at hperp hchi
  have h11 : Λ 1 1 = -Λ 0 0 := by linarith
  rw [h11] at hchi
  have ha : Λ 0 0 = 0 := by nlinarith
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ha, h11]
  nlinarith

/-- `|D k l| ≤ ∑ |D i j|`. -/
private lemma str_abs_le_sum (D : Mat2) (k l : Fin 2) : |D k l| ≤ ∑ i, ∑ j, |D i j| := by
  have h1 : |D k l| ≤ ∑ j, |D k j| :=
    Finset.single_le_sum (f := fun j ↦ |D k j|) (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ l)
  have h2 : ∑ j, |D k j| ≤ ∑ i, ∑ j, |D i j| :=
    Finset.single_le_sum (f := fun i ↦ ∑ j, |D i j|)
      (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) (Finset.mem_univ k)
  linarith

/-- Entrywise bound for the linear part `D ↦ [M, D] - ⟨D, M⟩B` of the costate equation. -/
lemma str_lin_bound (M B D : Mat2) {m C : ℝ} (hm : ∀ k l, |M k l| ≤ m)
    (hC : ∀ k l, |B k l| ≤ C) (i j : Fin 2) :
    |((M * D - D * M) - traceForm D M • B) i j| ≤
      (4 * m + 4 * m * C) * ∑ k, ∑ l, |D k l| := by
  set S := ∑ k, ∑ l, |D k l|
  have hD := str_abs_le_sum D
  have hm0 : 0 ≤ m := le_trans (abs_nonneg _) (hm 0 0)
  have hS0 : 0 ≤ S := le_trans (abs_nonneg _) (hD 0 0)
  have hp : ∀ a b c d : Fin 2, |M a b * D c d| ≤ m * S := fun a b c d ↦ by
    rw [abs_mul]; exact mul_le_mul (hm _ _) (hD _ _) (abs_nonneg _) hm0
  have hq : ∀ a b c d : Fin 2, |D a b * M c d| ≤ m * S := fun a b c d ↦ by
    rw [abs_mul, mul_comm]; exact mul_le_mul (hm _ _) (hD _ _) (abs_nonneg _) hm0
  have htr : |traceForm D M| ≤ 4 * (m * S) := by
    simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    have := hq 0 0 0 0; have := hq 0 1 1 0; have := hq 1 0 0 1; have := hq 1 1 1 1
    rw [abs_le] at *
    constructor <;> linarith
  have hB : |traceForm D M * B i j| ≤ 4 * (m * S) * C := by
    rw [abs_mul]; exact mul_le_mul htr (hC i j) (abs_nonneg _) (by positivity)
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have := hp i 0 0 j; have := hp i 1 1 j; have := hq i 0 0 j; have := hq i 1 1 j
  rw [abs_le] at *
  constructor <;> nlinarith

/-- The difference of two values of the right-hand side of `eqn:lamR` is linear in `Λ_R`. -/
lemma str_costateRHS_sub (lam : ℝ) (Λ₁ P Q X : Mat2) (u : Fin 3 → ℝ) :
    costateRHS lam Λ₁ P X u - costateRHS lam Λ₁ Q X u =
      (controlP u X * (P - Q) - (P - Q) * controlP u X) -
        traceForm (P - Q) (controlP u X) • (controlP u X * X - X * controlP u X) := by
  simp only [costateRHS, traceForm, Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub, sub_smul]
  abel

/-- Uniqueness for the costate equation of `Λ_R` along the `e₃`-trajectory, with
`Λ₁(t) = g(t)⁻¹ (l₁Λ₁₀) g(t)` and `Λ_R(0) = l_R [[0, y₀²], [1, 0]]` (Gronwall). -/
lemma str_costateΛR_unique (y0 l1 lR lam : ℝ) (hy0 : 0 < y0) (T : ℝ) (ΛR : ℝ → Mat2)
    (hΛ : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAtEntrywise ΛR
      (costateRHS lam ((segG y0 t)⁻¹ * (l1 • Λ₁₀ y0) * segG y0 t) (ΛR t) (segX y0 t) (vertex 2))
      (Set.Icc 0 T) t)
    (h0 : ΛR 0 = lR • !![0, y0 ^ 2; 1, 0]) :
    ∀ t ∈ Set.Icc 0 T, ΛR t = costateΛR y0 l1 lR lam t := by
  set M : Mat2 := !![√3 * y0 / 2, y0; 0, -(√3 * y0 / 2)]
  have hM : ∀ t, controlP (vertex 2) (segX y0 t) = M := fun t ↦ str_controlP_segX y0 t hy0
  have hm : ∀ k l, |M k l| ≤ √3 * y0 + y0 := by
    have h3 : (0 : ℝ) < √3 := by positivity
    intro k l
    fin_cases k <;> fin_cases l <;>
      simp [M, abs_of_pos hy0, abs_of_pos (show (0 : ℝ) < √3 * y0 / 2 by positivity)] <;>
      nlinarith [mul_pos h3 hy0]
  have hXc : Continuous (segX y0) :=
    continuous_iff_continuousAt.2 fun t ↦ (seg_solution y0 t hy0).2.1.continuousAt
  have hBc : Continuous fun t ↦ M * segX y0 t - segX y0 t * M :=
    (continuous_const.matrix_mul hXc).sub (hXc.matrix_mul continuous_const)
  have hgc : Continuous fun t ↦ ∑ k, ∑ l, |(M * segX y0 t - segX y0 t * M) k l| :=
    continuous_finsetSum _ fun k _ ↦ continuous_finsetSum _ fun l _ ↦
      (hBc.matrix_elem k l).abs
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    hgc.continuousOn
  have hC' : ∀ t ∈ Set.Icc 0 T, ∀ k l, |(M * segX y0 t - segX y0 t * M) k l| ≤ max C 0 :=
    fun t ht k l ↦ (str_abs_le_sum _ k l).trans <| (le_abs_self _).trans <|
      (Real.norm_eq_abs _ ▸ hC t ht).trans (le_max_left _ _)
  intro t ht
  refine Matrix.ODE_solution_unique_of_bound_Icc
    (G := fun s P ↦ costateRHS lam ((segG y0 s)⁻¹ * (l1 • Λ₁₀ y0) * segG y0 s) P (segX y0 s)
      (vertex 2))
    (K := 4 * (√3 * y0 + y0) + 4 * (√3 * y0 + y0) * max C 0) ?_
    (fun s hs ↦ (hΛ s hs).continuousWithinAt) (fun s hs ↦ hΛ s (Set.Ico_subset_Icc_self hs))
    (fun s _ ↦ (costateΛR_solution y0 l1 lR lam hy0 s).1.continuousAt.continuousWithinAt)
    (fun s _ ↦ (costateΛR_solution y0 l1 lR lam hy0 s).1.hasDerivWithinAtEntrywise)
    (h0.trans (costateΛR_solution y0 l1 lR lam hy0 0).2.symm) ht
  intro s hs P Q i j
  rw [← Matrix.sub_apply, str_costateRHS_sub, hM]
  simpa only [Matrix.sub_apply] using
    str_lin_bound M _ (P - Q) hm (hC' s (Set.Ico_subset_Icc_self hs)) i j

/-- Every lift satisfying the conditions of Theorem 7.5.1 is `-λ_cost` times the explicit one. -/
theorem strongLift_unique (y0 : ℝ) (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) (Λ₁ ΛR : ℝ → Mat2)
    (lam : ℝ) (h : IsStrongLift y0 Λ₁ ΛR lam) :
    ∀ t ∈ Set.Icc 0 (switchTime y0),
      Λ₁ t = (-lam) • strongΛ₁ y0 t ∧ ΛR t = (-lam) • strongΛR y0 t := by
  have h3 : (0 : ℝ) < √3 := by positivity
  have hy0' : 0 < y0 := lt_trans (by positivity) hy0
  obtain ⟨htr, hΛ₁', hΛR', hperp, hchi23, hH, hchi31, -, htrans1⟩ := h
  have hT := str_switchTime_pos y0 hy0 hy1
  have h0 : (0 : ℝ) ∈ Set.Icc 0 (switchTime y0) := ⟨le_rfl, hT.le⟩
  have hTm : switchTime y0 ∈ Set.Icc 0 (switchTime y0) := ⟨hT.le, le_rfl⟩
  have hdet : ∀ s, IsUnit (segG y0 s).det := fun s ↦ by
    rw [(seg_solution y0 0 hy0').2.2.2.2 s]; exact isUnit_one
  -- `Λ₁(t) = g(t)⁻¹ Λ₁(0) g(t)` (Corollary 6.5.3)
  have hconj := corollary6_5_3 (switchTime y0) (segG y0) (segX y0) Λ₁
    (fun t _ ↦ (seg_solution y0 t hy0').1.hasDerivWithinAtEntrywise) (str_segG_zero y0 hy0')
    (fun t _ ↦ (seg_solution y0 0 hy0').2.2.2.2 t) hΛ₁'
  -- `Λ₁(0)` centralizes `h = g(t_sw)R⁻¹`, hence `Λ₁₀ = h - (tr h/2) I₂`
  have hcomm := str_commute_of_conj_eq (segG y0 (switchTime y0)) (Λ₁ 0) (hdet _)
    ((hconj _ hTm).1.symm.trans htrans1)
  have hcomm' : Λ₁ 0 * Λ₁₀ y0 = Λ₁₀ y0 * Λ₁ 0 := by
    rw [str_Λ₁₀_eq y0 hy0]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, mul_one, one_mul,
      hcomm]
  -- the centralizer of `h` in `𝔰𝔩₂(ℝ)` is `ℝΛ₁₀`
  obtain ⟨l1, hΛ10⟩ : ∃ l1, Λ₁ 0 = l1 • Λ₁₀ y0 :=
    ⟨_, str_centralizer (Λ₁ 0) (Λ₁₀ y0) (htr 0 h0).1 (by simp [Λ₁₀]) (by simp [Λ₁₀])
      (by
        rw [show Λ₁₀ y0 0 1 = (2 * y0 ^ 2 * (1 + 3 * y0 ^ 2))⁻¹ * (4 * √3 * y0 ^ 4) by
          simp [Λ₁₀]]
        positivity) hcomm'⟩
  -- `Λ_R(0) = λ_R [[0, y₀²], [1, 0]]`
  rw [str_segX_zero y0 hy0'] at hperp hchi23 hH
  obtain ⟨lR, hΛR0⟩ : ∃ lR, ΛR 0 = lR • !![0, y0 ^ 2; 1, 0] :=
    ⟨_, str_ΛR0_eq y0 hy0' (ΛR 0) (htr 0 h0).2 hperp hchi23⟩
  -- `Λ₁ = g⁻¹ (λ₁Λ₁₀) g` and `Λ_R = costateΛR y0 λ₁ λ_R λ_cost` on `[0, t_sw]`
  have hΛ₁t : ∀ t ∈ Set.Icc 0 (switchTime y0),
      Λ₁ t = (segG y0 t)⁻¹ * (l1 • Λ₁₀ y0) * segG y0 t := fun t ht ↦ by
    rw [(hconj t ht).1, hΛ10]
  have hΛRt := str_costateΛR_unique y0 l1 lR lam hy0' (switchTime y0) ΛR
    (fun t ht ↦ by rw [← hΛ₁t t ht]; exact hΛR' t ht) hΛR0
  -- the two homogeneous linear relations `H = 0`, `χ₃₁(t_sw) = 0`
  rw [hΛ10, hΛR0, str_hamiltonian_zero y0 _ _ _ hy0', div_eq_zero_iff] at hH
  rw [hΛRt _ hTm, str_chi31_switchTime y0 _ _ _ hy0', div_eq_zero_iff] at hchi31
  have eH := hH.resolve_right (by positivity)
  have eC := hchi31.resolve_right (by positivity)
  have e1 : 12 * y0 ^ 4 * (√3 * l1) =
      (3 * y0 ^ 2 + 1) * ((3 * y0 ^ 2 + 1) * ellSw y0 - 6 * y0 ^ 2 - 3) * lam := by
    have : -8 * y0 ^ 2 * (12 * y0 ^ 4 * (√3 * l1)) = -8 * y0 ^ 2 *
        ((3 * y0 ^ 2 + 1) * ((3 * y0 ^ 2 + 1) * ellSw y0 - 6 * y0 ^ 2 - 3) * lam) := by
      linear_combination (-(6 * ellSw y0 * y0 ^ 4 + 2 * ellSw y0 * y0 ^ 2 + 12 * y0 ^ 4)) * eH -
        (-(6 * y0 ^ 4 + 2 * y0 ^ 2)) * eC
    exact mul_left_cancel₀ (by positivity) this
  have e2 : 24 * y0 ^ 6 * lR = (9 * ellSw y0 * y0 ^ 6 + 21 * ellSw y0 * y0 ^ 4 +
      3 * ellSw y0 * y0 ^ 2 - ellSw y0 + 18 * y0 ^ 6 - 9 * y0 ^ 4 - 12 * y0 ^ 2 + 3) * lam := by
    have : -4 * (24 * y0 ^ 6 * lR) = -4 * ((9 * ellSw y0 * y0 ^ 6 + 21 * ellSw y0 * y0 ^ 4 +
        3 * ellSw y0 * y0 ^ 2 - ellSw y0 + 18 * y0 ^ 6 - 9 * y0 ^ 4 - 12 * y0 ^ 2 + 3) * lam) := by
      linear_combination (3 * y0 ^ 4 + 6 * y0 ^ 2 - 1) * eC -
        (3 * ellSw y0 * y0 ^ 4 + 6 * ellSw y0 * y0 ^ 2 - ellSw y0 + 6 * y0 ^ 4 - 6 * y0 ^ 2) * eH
    exact mul_left_cancel₀ (by norm_num) this
  -- hence `λ₁ = -λ_cost λ₁*`, `λ_R = -λ_cost λ_R*`
  have hl1 : l1 = -lam * strongL₁ y0 := by
    rw [strongL₁]
    field_simp
    linear_combination e1
  have hlR : lR = -lam * strongLR y0 := by
    rw [strongLR]
    field_simp
    linear_combination e2
  intro t ht
  constructor
  · rw [hΛ₁t t ht, hl1, strongΛ₁, mul_smul, Matrix.mul_smul, Matrix.smul_mul]
  · have := str_costateΛR_smul (-lam) y0 (strongL₁ y0) (strongLR y0) (-1) t
    rw [neg_mul_neg, mul_one] at this
    rw [hΛRt t ht, hl1, hlR, strongΛR, this]

/-- Along the explicit lift, `Λ_R ⊥ X` and the Hamiltonian with control `e₃` vanishes. -/
theorem strongLift_perp_hamiltonian (y0 : ℝ) (hy0 : 1 / √3 < y0) :
    ∀ t ∈ Set.Icc 0 (switchTime y0), traceForm (strongΛR y0 t) (segX y0 t) = 0 ∧
      hamiltonian (-1) (strongΛ₁ y0 t) (strongΛR y0 t) (segX y0 t) (vertex 2) = 0 := by
  intro t _
  have h3 : (0 : ℝ) < √3 := by positivity
  have hy0' : 0 < y0 := lt_trans (by positivity) hy0
  refine ⟨str_perp_costateΛR y0 _ _ _ t hy0', ?_⟩
  rw [strongΛ₁, strongΛR, str_hamiltonian_costateΛR y0 _ _ _ t hy0', div_eq_zero_iff]
  left
  simp only [strongL₁, strongLR]
  field_simp
  ring_nf

/-- `χ₃₂` along the explicit lift in closed form, `W = exp(√3 y₀ t)`. -/
lemma str_chi32_closed (y0 : ℝ) (hy0 : 0 < y0) (t : ℝ) (hW : Real.exp (√3 * y0 * t) ≠ 2) :
    switchingFn 2 1 (strongΛR y0 t) (segX y0 t) =
      -2 * (-3 * Real.exp (√3 * y0 * t) ^ 2 * y0 ^ 2 -
          3 * Real.exp (√3 * y0 * t) * ellSw y0 * y0 ^ 2 - Real.exp (√3 * y0 * t) * ellSw y0 +
          6 * √3 * Real.exp (√3 * y0 * t) * t * y0 ^ 3 - 3 * Real.exp (√3 * y0 * t) * y0 ^ 2 +
          3 * Real.exp (√3 * y0 * t) + 3 * ellSw y0 * y0 ^ 2 + ellSw y0 + 6 * y0 ^ 2 - 3) /
        (3 * Real.exp (√3 * y0 * t) * y0 ^ 3 * (Real.exp (√3 * y0 * t) - 2)) := by
  have h3 : (0 : ℝ) < √3 := by positivity
  have hW0 := Real.exp_pos (√3 * y0 * t)
  rw [strongΛR, str_switchingFn_eq, (str_traceForm_segX y0 t hy0).2.1,
    (str_traceForm_segX y0 t hy0).2.2, costateΛR, str_traceForm_Z1_fin_two,
    str_traceForm_Z2_fin_two]
  simp only [costateΛR₀₀, costateΛR₁₀, strongL₁, strongLR]
  generalize ellSw y0 = ℓ
  generalize Real.exp (√3 * y0 * t) = W at hW hW0 ⊢
  have hW2 : W - 2 ≠ 0 := sub_ne_zero.2 hW
  field_simp
  ring_nf
  simp only [str_sqrt3_sq, str_sqrt3_pow3]
  ring_nf

/-- `χ₃₁` along `costateΛR`: a linear form in `(λ₁, λ_R, λ_cost)`, `W = exp(√3 y₀ t)`. -/
lemma str_chi31_general (y0 l1 lR lam : ℝ) (hy0 : 0 < y0) (t : ℝ)
    (hW : (3 * y0 ^ 2 + 1) * Real.exp (√3 * y0 * t) - 2 ≠ 0) :
    switchingFn 2 0 (costateΛR y0 l1 lR lam t) (segX y0 t) =
      (Real.exp (√3 * y0 * t) * y0 * (-6 * Real.exp (√3 * y0 * t) * y0 ^ 3 -
          2 * Real.exp (√3 * y0 * t) * y0 + 3 * √3 * t * y0 ^ 4 + 6 * √3 * t * y0 ^ 2 - √3 * t +
          6 * y0 ^ 3 + 2 * y0) * (√3 * l1) -
        2 * Real.exp (√3 * y0 * t) * y0 ^ 3 * (3 * √3 * t * y0 ^ 2 + √3 * t + 6 * y0) * lR +
        (-18 * Real.exp (√3 * y0 * t) ^ 2 * y0 ^ 4 - 12 * Real.exp (√3 * y0 * t) ^ 2 * y0 ^ 2 -
          2 * Real.exp (√3 * y0 * t) ^ 2 + 9 * √3 * Real.exp (√3 * y0 * t) * t * y0 ^ 5 +
          24 * √3 * Real.exp (√3 * y0 * t) * t * y0 ^ 3 +
          7 * √3 * Real.exp (√3 * y0 * t) * t * y0 + 18 * Real.exp (√3 * y0 * t) * y0 ^ 4 +
          12 * Real.exp (√3 * y0 * t) * y0 ^ 2 - 6 * Real.exp (√3 * y0 * t) + 8) * lam) /
        (2 * y0 * ((3 * y0 ^ 2 + 1) * Real.exp (√3 * y0 * t) - 2)) := by
  have h3 : (0 : ℝ) < √3 := by positivity
  have hW0 := Real.exp_pos (√3 * y0 * t)
  have hZ1 : traceForm (controlMatrix (vertex 0)) (segX y0 t) =
      -((3 * y0 ^ 2 + 1) * Real.exp (√3 * y0 * t) - 2) / (3 * y0) := by
    rw [(str_traceForm_segX y0 t hy0).1]
    field_simp
    ring
  rw [str_switchingFn_eq, hZ1, (str_traceForm_segX y0 t hy0).2.2, costateΛR,
    str_traceForm_Z0_fin_two, str_traceForm_Z2_fin_two]
  generalize hQ : (3 * y0 ^ 2 + 1) * Real.exp (√3 * y0 * t) - 2 = Q at hW ⊢
  have hQ' : Real.exp (√3 * y0 * t) = (Q + 2) / (3 * y0 ^ 2 + 1) := by
    rw [← hQ]; field_simp; ring
  have key : ∀ x : ℝ, x / (-Q / (3 * y0)) = -(3 * y0 * x) / Q := fun x ↦ by
    field_simp
  rw [key, eq_div_iff (by positivity), sub_mul, div_mul_eq_mul_div, mul_div_assoc,
    show (2 * y0 * Q) / Q = 2 * y0 by field_simp]
  simp only [costateΛR₀₀, costateΛR₀₁, costateΛR₁₀]
  generalize Real.exp (√3 * y0 * t) = W at hQ hQ' hW0 ⊢
  subst hQ
  field_simp
  ring_nf
  simp only [str_sqrt3_sq, str_sqrt3_pow3]
  ring_nf

/-- `χ₃₁` along the explicit lift in closed form, `W = exp(√3 y₀ t)`. -/
lemma str_chi31_closed (y0 : ℝ) (hy0 : 0 < y0) (t : ℝ)
    (hW : (3 * y0 ^ 2 + 1) * Real.exp (√3 * y0 * t) - 2 ≠ 0) :
    switchingFn 2 0 (strongΛR y0 t) (segX y0 t) =
      (27 * Real.exp (√3 * y0 * t) ^ 2 * ellSw y0 * y0 ^ 6 +
          27 * Real.exp (√3 * y0 * t) ^ 2 * ellSw y0 * y0 ^ 4 +
          9 * Real.exp (√3 * y0 * t) ^ 2 * ellSw y0 * y0 ^ 2 +
          Real.exp (√3 * y0 * t) ^ 2 * ellSw y0 + 54 * Real.exp (√3 * y0 * t) ^ 2 * y0 ^ 6 +
          9 * Real.exp (√3 * y0 * t) ^ 2 * y0 ^ 4 - 12 * Real.exp (√3 * y0 * t) ^ 2 * y0 ^ 2 -
          3 * Real.exp (√3 * y0 * t) ^ 2 + 36 * Real.exp (√3 * y0 * t) * ellSw y0 * y0 ^ 4 -
          4 * Real.exp (√3 * y0 * t) * ellSw y0 - 72 * √3 * Real.exp (√3 * y0 * t) * t * y0 ^ 5 -
          24 * √3 * Real.exp (√3 * y0 * t) * t * y0 ^ 3 - 36 * Real.exp (√3 * y0 * t) * y0 ^ 4 +
          24 * Real.exp (√3 * y0 * t) * y0 ^ 2 + 12 * Real.exp (√3 * y0 * t) - 48 * y0 ^ 2) /
        (12 * y0 ^ 3 * ((3 * y0 ^ 2 + 1) * Real.exp (√3 * y0 * t) - 2)) := by
  have h3 : (0 : ℝ) < √3 := by positivity
  rw [strongΛR, str_chi31_general y0 _ _ _ hy0 t hW]
  simp only [strongL₁, strongLR]
  generalize ellSw y0 = ℓ
  generalize Real.exp (√3 * y0 * t) = W at hW ⊢
  field_simp
  ring_nf

/-! ### Scalar multiples of a strong lift -/

private lemma str_costateRHS_smul (c lam : ℝ) (Λ₁ ΛR X : Mat2) (u : Fin 3 → ℝ) :
    costateRHS (c * lam) (c • Λ₁) (c • ΛR) X u = c • costateRHS lam Λ₁ ΛR X u := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [costateRHS, traceForm, J, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two] <;>
    ring

private lemma str_traceForm_smul (c : ℝ) (A X : Mat2) :
    traceForm (c • A) X = c * traceForm A X := by
  simp [traceForm, Matrix.trace_smul]

private lemma str_switchingFn_smul (c : ℝ) (i j : Fin 3) (Λ X : Mat2) :
    switchingFn i j (c • Λ) X = c * switchingFn i j Λ X := by
  simp only [switchingFn, str_traceForm_smul]

private lemma str_hamiltonian_smul (c lam : ℝ) (Λ₁ ΛR X : Mat2) (u : Fin 3 → ℝ) :
    hamiltonian (c * lam) (c • Λ₁) (c • ΛR) X u = c * hamiltonian lam Λ₁ ΛR X u := by
  have h : c • Λ₁ - (3 / 2 * (c * lam)) • J = c • (Λ₁ - (3 / 2 * lam) • J) := by
    rw [smul_sub, smul_smul]; ring_nf
  simp only [hamiltonian, h, str_traceForm_smul]
  ring

/-- A scalar multiple `c • (Λ₁, Λ_R, -1)` of a strong lift is a strong lift (with
`λ_cost = -c`); the lift only matters on `[0, t_sw]`. -/
lemma str_isStrongLift_smul (y0 : ℝ) (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) (c : ℝ)
    (Λ₁ ΛR Λ₁' ΛR' : ℝ → Mat2) (h : IsStrongLift y0 Λ₁ ΛR (-1))
    (hc : ∀ t ∈ Set.Icc 0 (switchTime y0), Λ₁' t = c • Λ₁ t ∧ ΛR' t = c • ΛR t) :
    IsStrongLift y0 Λ₁' ΛR' (-c) := by
  obtain ⟨htr, hΛ₁, hΛR, hperp, hchi23, hH, hchi31, htransR, htrans1⟩ := h
  have hT := str_switchTime_pos y0 hy0 hy1
  have h0 : (0 : ℝ) ∈ Set.Icc 0 (switchTime y0) := ⟨le_rfl, hT.le⟩
  have hTm : switchTime y0 ∈ Set.Icc 0 (switchTime y0) := ⟨hT.le, le_rfl⟩
  have hlam : -c = c * -1 := by ring
  refine ⟨fun t ht ↦ ?_, fun t ht ↦ ?_, fun t ht ↦ ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(hc t ht).1, (hc t ht).2, Matrix.trace_smul, Matrix.trace_smul, (htr t ht).1,
      (htr t ht).2, smul_zero]
    exact ⟨rfl, rfl⟩
  · refine (((hΛ₁ t ht).const_smul c).congr_of_mem (fun x hx ↦ (hc x hx).1) ht).congr_deriv ?_
    rw [(hc t ht).1, smul_sub, Matrix.smul_mul, Matrix.mul_smul]
  · refine (((hΛR t ht).const_smul c).congr_of_mem (fun x hx ↦ (hc x hx).2) ht).congr_deriv ?_
    rw [(hc t ht).1, (hc t ht).2, hlam, str_costateRHS_smul]
  · rw [(hc 0 h0).2, str_traceForm_smul, hperp, mul_zero]
  · rw [(hc 0 h0).2, str_switchingFn_smul, hchi23, mul_zero]
  · rw [(hc 0 h0).1, (hc 0 h0).2, hlam, str_hamiltonian_smul, hH, mul_zero]
  · rw [(hc _ hTm).2, str_switchingFn_smul, hchi31, mul_zero]
  · rw [(hc _ hTm).2, (hc 0 h0).2, htransR, Matrix.mul_smul, Matrix.smul_mul]
  · rw [(hc _ hTm).1, (hc 0 h0).1, htrans1, Matrix.mul_smul, Matrix.smul_mul]

/-- The function `f(y, r)` of the proof of Lemma 7.5.3. -/
noncomputable def hmaxF (y r : ℝ) : ℝ :=
  2 * r * (y - 1) * y * Real.log r -
      (r - y) * (r * (y - 1) + y * (-5 + 2 * y) + y ^ 2 * Real.log (4 / y)) -
    2 * r * (y - 1) * y * Real.log y

/-- The switching function `χ₃₂` of the explicit lift in terms of `f`: with `y = 1 + 3y₀²` and
`W = exp(√3 y₀ t)`, `χ₃₂(t) = 2 f(y, yW) / (3 y² W y₀³ (2 - W))` (proof of Lemma 7.5.3). -/
theorem chi32_eq (y0 : ℝ) (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) (t : ℝ)
    (ht : t ∈ Set.Icc 0 (switchTime y0)) :
    switchingFn 2 1 (strongΛR y0 t) (segX y0 t) =
      2 * hmaxF (1 + 3 * y0 ^ 2) ((1 + 3 * y0 ^ 2) * Real.exp (√3 * y0 * t)) /
        (3 * (1 + 3 * y0 ^ 2) ^ 2 * Real.exp (√3 * y0 * t) * y0 ^ 3 *
          (2 - Real.exp (√3 * y0 * t))) := by
  have h3 : (0 : ℝ) < √3 := by positivity
  have hy0' : 0 < y0 := lt_trans (by positivity) hy0
  obtain ⟨hW1, hW2⟩ := str_W_mem hy0' ht
  have hWlt : Real.exp (√3 * y0 * t) < 2 := lt_of_le_of_lt hW2 (by
    rw [div_lt_iff₀ (by positivity)]; nlinarith [str_one_third_lt_sq hy0])
  rw [strongΛR, str_switchingFn_eq, (str_traceForm_segX y0 t hy0').2.1,
    (str_traceForm_segX y0 t hy0').2.2, costateΛR, str_traceForm_Z1_fin_two,
    str_traceForm_Z2_fin_two]
  have hlog : Real.log ((1 + 3 * y0 ^ 2) * Real.exp (√3 * y0 * t)) =
      Real.log (1 + 3 * y0 ^ 2) + √3 * y0 * t := by
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
  have hell : Real.log (4 / (1 + 3 * y0 ^ 2)) = ellSw y0 := by rw [ellSw, add_comm]
  simp only [hmaxF, hlog, hell, costateΛR₀₀, costateΛR₁₀, strongL₁, strongLR]
  generalize ellSw y0 = ℓ
  generalize Real.log (1 + 3 * y0 ^ 2) = Ly
  generalize Real.exp (√3 * y0 * t) = W at hW1 hWlt ⊢
  have hW2' : W - 2 ≠ 0 := by linarith
  have hW2'' : 2 - W ≠ 0 := by linarith
  have hW0 : W ≠ 0 := by linarith
  field_simp
  ring_nf
  simp only [str_sqrt3_sq, str_sqrt3_pow3]
  ring_nf

/-- The symmetry `χ₃₁(t_sw - t) = χ₃₂(t)` of the proof of Lemma 7.5.3. -/
theorem chi31_eq_chi32 (y0 : ℝ) (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) (t : ℝ)
    (ht : t ∈ Set.Icc 0 (switchTime y0)) :
    switchingFn 2 0 (strongΛR y0 (switchTime y0 - t)) (segX y0 (switchTime y0 - t)) =
      switchingFn 2 1 (strongΛR y0 t) (segX y0 t) := by
  have h3 : (0 : ℝ) < √3 := by positivity
  have hy0' : 0 < y0 := lt_trans (by positivity) hy0
  have hsq := str_one_third_lt_sq hy0
  obtain ⟨hW1, hW2⟩ := str_W_mem hy0' ht
  have hWlt : Real.exp (√3 * y0 * t) < 2 := lt_of_le_of_lt hW2 (by
    rw [div_lt_iff₀ (by positivity)]; nlinarith)
  have ht' : switchTime y0 - t ∈ Set.Icc 0 (switchTime y0) := ⟨by linarith [ht.2], by
    linarith [ht.1]⟩
  have hexp : Real.exp (√3 * y0 * (switchTime y0 - t)) =
      4 / (3 * y0 ^ 2 + 1) / Real.exp (√3 * y0 * t) := by
    rw [mul_sub, Real.exp_sub, str_exp_switchTime hy0']
  obtain ⟨hV1, -⟩ := str_W_mem hy0' ht'
  rw [str_chi31_closed y0 hy0' _ (by nlinarith), str_chi32_closed y0 hy0' _ hWlt.ne, hexp]
  rw [show switchTime y0 = ellSw y0 / (√3 * y0) from rfl]
  generalize ellSw y0 = ℓ
  generalize Real.exp (√3 * y0 * t) = W at hW1 hWlt ⊢
  have hW2' : W - 2 ≠ 0 := by linarith
  have hW2'' : 4 - W * 2 ≠ 0 := by linarith
  have hW0 : W ≠ 0 := by linarith
  field_simp
  ring_nf

/-- **Theorem 7.5.1** (`thm:strong-transversality`). Let `y₀ ∈ (1/√3, 1)`, `z₀ = i y₀`, `t_sw`
given by `eqn:t1`, and let `z(z₀, t)`, `g(t) = g₀(z₀, t)` be the solutions of the state equations
with constant control `e₃` on `[0, t_sw]`. These solutions lift uniquely, up to a scalar factor, to
a costate trajectory `(Λ₁, Λ_R, λ_cost)` with `Λ_R(0) ∈ X(0)^⊥`, `χ₂₃(0) = 0`, `H_{u=e₃} = 0`,
`χ₃₁(t_sw) = 0` and the strong transversality conditions; the trajectory is normal,
`λ_cost ≠ 0`. Here: there is such a lift with `λ_cost = -1`, and the lifts are exactly its scalar
multiples `c • (Λ₁, Λ_R, -1)`, so a nonzero lift has `λ_cost = -c ≠ 0`.

The proof follows the book's (`strongLift_isStrongLift`, `strongLift_unique`); the centralizer of
`h = g(t_sw)R⁻¹` in `𝔰𝔩₂` is `ℝΛ₁₀` (`str_centralizer`). -/
theorem theorem7_5_1 (y0 : ℝ) (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) :
    ∃ Λ₁ ΛR : ℝ → Mat2, IsStrongLift y0 Λ₁ ΛR (-1) ∧
      ∀ (Λ₁' ΛR' : ℝ → Mat2) (lam : ℝ), IsStrongLift y0 Λ₁' ΛR' lam ↔
        ∃ c : ℝ, lam = -c ∧
          ∀ t ∈ Set.Icc 0 (switchTime y0), Λ₁' t = c • Λ₁ t ∧ ΛR' t = c • ΛR t := by
  refine ⟨strongΛ₁ y0, strongΛR y0, strongLift_isStrongLift y0 hy0,
    fun Λ₁' ΛR' lam ↦ ⟨fun h ↦ ⟨-lam, by ring, strongLift_unique y0 hy0 hy1 Λ₁' ΛR' lam h⟩, ?_⟩⟩
  rintro ⟨c, rfl, hc⟩
  exact str_isStrongLift_smul y0 hy0 hy1 c _ _ _ _ (strongLift_isStrongLift y0 hy0) hc

/-- The values found in the proof of Theorem 7.5.1: a strong lift with `λ_cost = -1` has
`Λ₁(0) = λ₁ Λ₁₀` and `Λ_R(0) = λ_R [[0, y₀²], [1, 0]]`, where `ℓ = ln(4/(3y₀² + 1))`,
`Λ₁₀ = [[0, 4√3 y₀⁴], [-√3(1 + y₀²)(3y₀² - 1), 0]]/(2y₀²(1 + 3y₀²))`,
`λ₁ = -(1 + 3y₀²)(-3 - 6y₀² + (1 + 3y₀²)ℓ)/(12√3 y₀⁴)` and
`λ_R = -(3 - 12y₀² - 9y₀⁴ + 18y₀⁶ + (-1 + 3y₀² + 21y₀⁴ + 9y₀⁶)ℓ)/(24y₀⁶)`. -/
theorem strongLift_initial (y0 : ℝ) (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) (Λ₁ ΛR : ℝ → Mat2)
    (h : IsStrongLift y0 Λ₁ ΛR (-1)) :
    Λ₁ 0 = (-(1 + 3 * y0 ^ 2) * (-3 - 6 * y0 ^ 2 + (1 + 3 * y0 ^ 2) *
        Real.log (4 / (3 * y0 ^ 2 + 1))) / (12 * √3 * y0 ^ 4)) •
        ((2 * y0 ^ 2 * (1 + 3 * y0 ^ 2))⁻¹ •
          !![0, 4 * √3 * y0 ^ 4; -(√3 * (1 + y0 ^ 2) * (3 * y0 ^ 2 - 1)), 0]) ∧
      ΛR 0 = (-(3 - 12 * y0 ^ 2 - 9 * y0 ^ 4 + 18 * y0 ^ 6 +
        (-1 + 3 * y0 ^ 2 + 21 * y0 ^ 4 + 9 * y0 ^ 6) * Real.log (4 / (3 * y0 ^ 2 + 1))) /
          (24 * y0 ^ 6)) • !![0, y0 ^ 2; 1, 0] := by
  have hy0' : 0 < y0 := lt_trans (by positivity) hy0
  have hT := str_switchTime_pos y0 hy0 hy1
  obtain ⟨h1, h2⟩ := strongLift_unique y0 hy0 hy1 Λ₁ ΛR (-1) h 0 ⟨le_rfl, hT.le⟩
  rw [neg_neg, one_smul] at h1 h2
  constructor
  · rw [h1, strongΛ₁, str_segG_zero y0 hy0', inv_one, one_mul, mul_one, Λ₁₀]
    congr 1
    rw [strongL₁, ellSw]
    ring
  · rw [h2, strongΛR, (costateΛR_solution y0 _ _ _ hy0' 0).2, strongLR, ellSw]

end SmoothedPolygons
