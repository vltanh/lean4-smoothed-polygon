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

/-- `costateΛR` solves the costate equation for `Λ_R` with control `e₃` along the `e₃`-trajectory,
with `Λ₁(t) = g(t)⁻¹ (l1 Λ₁₀) g(t)`, and has the initial value `lR [[0, y₀²], [1, 0]]`. -/
theorem costateΛR_solution (y0 l1 lR lam : ℝ) (hy0 : 0 < y0) (t : ℝ) :
    HasDerivAtEntrywise (costateΛR y0 l1 lR lam)
        (costateRHS lam ((segG y0 t)⁻¹ * (l1 • Λ₁₀ y0) * segG y0 t) (costateΛR y0 l1 lR lam t)
          (segX y0 t) (vertex 2)) t ∧
      costateΛR y0 l1 lR lam 0 = lR • !![0, y0 ^ 2; 1, 0] := by
  sorry

/-- The explicit lift satisfies the conditions of Theorem 7.5.1 with `λ_cost = -1`. -/
theorem strongLift_isStrongLift (y0 : ℝ) (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) :
    IsStrongLift y0 (strongΛ₁ y0) (strongΛR y0) (-1) := by
  sorry

/-- Every lift satisfying the conditions of Theorem 7.5.1 is `-λ_cost` times the explicit one. -/
theorem strongLift_unique (y0 : ℝ) (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) (Λ₁ ΛR : ℝ → Mat2)
    (lam : ℝ) (h : IsStrongLift y0 Λ₁ ΛR lam) :
    ∀ t ∈ Set.Icc 0 (switchTime y0),
      Λ₁ t = (-lam) • strongΛ₁ y0 t ∧ ΛR t = (-lam) • strongΛR y0 t := by
  sorry

/-- Along the explicit lift, `Λ_R ⊥ X` and the Hamiltonian with control `e₃` vanishes. -/
theorem strongLift_perp_hamiltonian (y0 : ℝ) (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) :
    ∀ t ∈ Set.Icc 0 (switchTime y0), traceForm (strongΛR y0 t) (segX y0 t) = 0 ∧
      hamiltonian (-1) (strongΛ₁ y0 t) (strongΛR y0 t) (segX y0 t) (vertex 2) = 0 := by
  sorry

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
  sorry

/-- The symmetry `χ₃₁(t_sw - t) = χ₃₂(t)` of the proof of Lemma 7.5.3. -/
theorem chi31_eq_chi32 (y0 : ℝ) (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) (t : ℝ)
    (ht : t ∈ Set.Icc 0 (switchTime y0)) :
    switchingFn 2 0 (strongΛR y0 (switchTime y0 - t)) (segX y0 (switchTime y0 - t)) =
      switchingFn 2 1 (strongΛR y0 t) (segX y0 t) := by
  sorry

/-- **Theorem 7.5.1** (`thm:strong-transversality`). Let `y₀ ∈ (1/√3, 1)`, `z₀ = i y₀`, `t_sw`
given by `eqn:t1`, and let `z(z₀, t)`, `g(t) = g₀(z₀, t)` be the solutions of the state equations
with constant control `e₃` on `[0, t_sw]`. These solutions lift uniquely, up to a scalar factor, to
a costate trajectory `(Λ₁, Λ_R, λ_cost)` with `Λ_R(0) ∈ X(0)^⊥`, `χ₂₃(0) = 0`, `H_{u=e₃} = 0`,
`χ₃₁(t_sw) = 0` and the strong transversality conditions; the trajectory is normal,
`λ_cost ≠ 0`. Here: there is such a lift with `λ_cost = -1`, and the lifts are exactly its scalar
multiples `c • (Λ₁, Λ_R, -1)`, so a nonzero lift has `λ_cost = -c ≠ 0`. -/
theorem theorem7_5_1 (y0 : ℝ) (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) :
    ∃ Λ₁ ΛR : ℝ → Mat2, IsStrongLift y0 Λ₁ ΛR (-1) ∧
      ∀ (Λ₁' ΛR' : ℝ → Mat2) (lam : ℝ), IsStrongLift y0 Λ₁' ΛR' lam ↔
        ∃ c : ℝ, lam = -c ∧
          ∀ t ∈ Set.Icc 0 (switchTime y0), Λ₁' t = c • Λ₁ t ∧ ΛR' t = c • ΛR t := by
  sorry

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
  sorry

end SmoothedPolygons
