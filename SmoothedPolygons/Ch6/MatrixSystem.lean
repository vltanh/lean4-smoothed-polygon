module

public import SmoothedPolygons.Ch3.ControlProblem
public import SmoothedPolygons.Ch3.ControlSets
public import OptimalControl.Pontryagin.Defs

/-!
# The Reinhardt problem as a control system on `GL₂⁺(ℝ) × 𝔰𝔩₂(ℝ)` (§6.2)

The book applies the Pontryagin maximum principle (§6.2, TeX 4662–4830) to the Reinhardt control
problem (Problem 3.6.2, TeX 3203) on the manifold `SL₂(ℝ) × 𝔰𝔩₂(ℝ)`, with state `q = (g, X)` and
costate `p = (Λ₁, Λ₂)` (TeX 4806–4822). The maximum principle used here
(`External.pontryagin_maximum_principle`) is stated on an open subset of a finite-dimensional
space (its reading D1 of the book's "smooth manifold"). This file poses the problem on such a set,
in the book's variables:

* the state space `MatrixState = Mat₂(ℝ) × ℝ³`: the matrix `g` (`stateG`) and the coordinates
  `x = (a, b, c)` of `X = [[a, b], [c, -a]] ∈ 𝔰𝔩₂(ℝ)` (`slMatrix`, `stateX`);
* the open set `matrixDomain = GL₂⁺(ℝ) × C`, with `C` the open cone `ρ₀, ρ₁, ρ₂ > 0` of `𝔰𝔩₂(ℝ)`
  (the star conditions of Corollary 3.1.6 without `det X = 1`); on it `⟨Z_u, X⟩ < 0` for
  `u ∈ U_T` (Lemma 3.3.4, which needs only `tr X = 0`), so the dynamics are smooth there;
* the dynamics `matrixField`: `g' = gX` and `X' = [P, X]` with `P = Z_u/⟨Z_u, X⟩` (equations
  `eqn:trisystem-g`, `eqn:trisystem-X`), and the cost `matrixCost = -(3/2)⟨J, X⟩` (`eqn:cost`);
* the boundary condition `matrixEndpoints`, the zero set of the `C¹` submersion `matrixBoundary`
  (10 equations on `MatrixState × MatrixState`, of dimension 14): `g(0) = I₂` and `det X(0) = 1`
  (§3.5, TeX 3121–3160); of `g(t_f) = R` the entries `(0, 0)`, `(0, 1)`, `(1, 0)`; of
  `X(t_f) = R⁻¹X(0)R` (Problem 3.6.2) the entries `(0, 0)`, `(0, 1)`.

`det g` and `det X` are first integrals of the dynamics (`tr X = 0`, and `X' = [P, X]` is
isospectral). Hence `g(t) ∈ SL₂(ℝ)` and `det X(t) = 1` along every admissible pair satisfying the
boundary condition, and the two equations left out hold automatically: `det g(t_f) = 1` and
`R₀₀ = 1/2 ≠ 0` give `g(t_f)₁₁ = R₁₁`, and `det X(t_f) = 1` with `X(t_f)₀₁ < 0` on `C` gives
`X(t_f)₁₀ = -(1 + X(t_f)₀₀²)/X(t_f)₀₁ = (R⁻¹X(0)R)₁₀`. So these pairs are exactly the admissible
trajectories of Problem 3.6.2 (`SmoothedPolygons/Ch6/MatrixMinimizer.lean`).

Departure from the paper (E21, inventory §3.4): the boundary condition leaves out the two
equations `g(t_f)₁₁ = R₁₁` and `X(t_f)₁₀ = (R⁻¹X(0)R)₁₀`, which the first integrals `det g` and
`det X` make redundant. Were they kept, `ker G'` would lose the directions `(0, E₁₁)` of `g(t_f)`
and `(0, E₁₀)` of `X(t_f)`, and every admissible trajectory would satisfy the conclusions of the
maximum principle with `λ_cost = 0` and the covector `(p g, Λ₂) = (k I₂, 0)` (from `det g`) or
`(0, c X)` (from `det X`; this is E21), whose reduced costate `(Λ₁, Λ_R)` vanishes; the
nontriviality condition of `IsPontryaginExtremal` would not follow. Without them, the
transversality conditions in these two directions (`fderiv_matrixBoundary_g₁₁`,
`fderiv_matrixBoundary_X₁₀`) force `k = c = 0` (`SmoothedPolygons/Ch6/MatrixExtremal.lean`).
-/

@[expose] public section

namespace SmoothedPolygons

open Set Pontryagin ControlSystem

/-! ### Coordinates -/

/-- The state space `Mat₂(ℝ) × ℝ³` of the matrix system: the entries of the group variable `g`,
and the coordinates `x = (a, b, c)` of the Lie-algebra variable `X = [[a, b], [c, -a]]`. -/
abbrev MatrixState : Type := (Fin 2 → Fin 2 → ℝ) × (Fin 3 → ℝ)

/-- The traceless matrix `[[a, b], [c, -a]]` with coordinates `x = (a, b, c)`: the linear
isomorphism `ℝ³ ≅ 𝔰𝔩₂(ℝ)`. -/
def slMatrix (x : Fin 3 → ℝ) : Mat2 := !![x 0, x 1; x 2, -x 0]

/-- The coordinates `(M₀₀, M₀₁, M₁₀)` of a matrix; on `𝔰𝔩₂(ℝ)` the inverse of `slMatrix`. -/
def slCoords (M : Mat2) : Fin 3 → ℝ := ![M 0 0, M 0 1, M 1 0]

/-- The group variable `g` of a state. -/
def stateG (q : MatrixState) : Mat2 := Matrix.of q.1

/-- The Lie-algebra variable `X ∈ 𝔰𝔩₂(ℝ)` of a state. -/
def stateX (q : MatrixState) : Mat2 := slMatrix q.2

/-- The state with group variable `g` and Lie-algebra variable `X` (for traceless `X`). -/
def toMatrixState (g X : Mat2) : MatrixState := (fun i j ↦ g i j, slCoords X)

theorem trace_slMatrix (x : Fin 3 → ℝ) : (slMatrix x).trace = 0 := by
  simp [slMatrix, Matrix.trace_fin_two]

theorem slCoords_slMatrix (x : Fin 3 → ℝ) : slCoords (slMatrix x) = x := by
  ext i; fin_cases i <;> simp [slCoords, slMatrix]

theorem slMatrix_slCoords {M : Mat2} (hM : M.trace = 0) : slMatrix (slCoords M) = M := by
  have h11 : M 1 1 = -M 0 0 := by rw [Matrix.trace_fin_two] at hM; linarith
  ext i j; fin_cases i <;> fin_cases j <;> simp [slCoords, slMatrix, h11]

theorem stateG_toMatrixState (g X : Mat2) : stateG (toMatrixState g X) = g := rfl

theorem stateX_toMatrixState (g : Mat2) {X : Mat2} (hX : X.trace = 0) :
    stateX (toMatrixState g X) = X :=
  slMatrix_slCoords hX

/-- `R⁻¹ = [[1/2, √3/2], [-√3/2, 1/2]]`. -/
theorem mx_R_inv : R⁻¹ = !![1 / 2, √3 / 2; -(√3 / 2), 1 / 2] := by
  refine Matrix.inv_eq_right_inv ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [R] <;> ring_nf <;> norm_num

theorem mx_R_mul_R_inv : R * R⁻¹ = 1 := by
  rw [mx_R_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [R] <;> ring_nf <;> norm_num

theorem mx_R_inv_mul_R : R⁻¹ * R = 1 := by
  rw [mx_R_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [R] <;> ring_nf <;> norm_num

/-! ### The control system -/

/-- The open set `GL₂⁺(ℝ) × C` on which the matrix system is posed: `det g > 0`, and `X` in the
open cone `C` of `𝔰𝔩₂(ℝ)` cut out by the star inequalities `ρ₀(X), ρ₁(X), ρ₂(X) > 0`
(Corollary 3.1.6; the star states are the points of `C` with `det X = 1`). -/
def matrixDomain : Set MatrixState :=
  {q | 0 < (stateG q).det ∧ 0 < ρ₀ (stateX q) ∧ 0 < ρ₁ (stateX q) ∧ 0 < ρ₂ (stateX q)}

/-- The dynamics of the matrix system: `g' = gX` (`eqn:trisystem-g`) and `X' = [P, X]` with
`P = Z_u/⟨Z_u, X⟩` (`eqn:trisystem-X`), the latter in the coordinates `slCoords`. -/
noncomputable def matrixField (q : MatrixState) (u : Fin 3 → ℝ) : MatrixState :=
  (fun i j ↦ (stateG q * stateX q) i j,
    slCoords (controlP u (stateX q) * stateX q - stateX q * controlP u (stateX q)))

/-- The cost integrand `-(3/2)⟨J, X⟩` of the matrix system (equation `eqn:cost`). -/
noncomputable def matrixCost (q : MatrixState) (_u : Fin 3 → ℝ) : ℝ :=
  -(3 / 2) * traceForm J (stateX q)

/-- The boundary map of the matrix system, on `(q(0), q(t_f))`: `g(0) - I₂`; the entries
`(0, 0)`, `(0, 1)`, `(1, 0)` of `g(t_f) - R`; `det X(0) - 1`; the entries `(0, 0)`, `(0, 1)` of
`X(t_f) - R⁻¹X(0)R`. The entries `(1, 1)` of `g(t_f) - R` and `(1, 0)` of `X(t_f) - R⁻¹X(0)R` are
left out (see the module docstring: they are redundant, and keeping them lets the maximum
principle return the spurious multipliers of E21). -/
noncomputable def matrixBoundary (w : MatrixState × MatrixState) :
    (Fin 2 → Fin 2 → ℝ) × (Fin 3 → ℝ) × ℝ × (Fin 2 → ℝ) :=
  (fun i j ↦ (stateG w.1 - 1) i j,
    ![stateG w.2 0 0 - R 0 0, stateG w.2 0 1 - R 0 1, stateG w.2 1 0 - R 1 0],
    (stateX w.1).det - 1,
    ![stateX w.2 0 0 - (R⁻¹ * stateX w.1 * R) 0 0, stateX w.2 0 1 - (R⁻¹ * stateX w.1 * R) 0 1])

/-- The boundary condition of the matrix system: `g(0) = I₂`, `det X(0) = 1`, and `g(t_f) = R`,
`X(t_f) = R⁻¹X(0)R` up to the two redundant entries (`matrixBoundary`). -/
def matrixEndpoints : Set (MatrixState × MatrixState) := {w | matrixBoundary w = 0}

/-- On the cone `C`, `X₀₁ < 0`: `ρ₀ + ρ₁ > 0` gives `X₁₀ > 0`, and `ρ₂ > 0` gives
`3X₀₁ + X₁₀ < 0`. -/
theorem stateX_zero_one_neg {q : MatrixState} (hq : q ∈ matrixDomain) : stateX q 0 1 < 0 := by
  obtain ⟨-, h0, h1, h2⟩ := hq
  have h3 : (0 : ℝ) < √3 := by positivity
  simp only [ρ₀, ρ₁, ρ₂] at h0 h1 h2
  have a0 := (div_pos_iff_of_pos_right h3).1 h0
  have a1 := (div_pos_iff_of_pos_right h3).1 h1
  have a2 : 0 < -(3 * stateX q 0 1 + stateX q 1 0) :=
    (div_pos_iff_of_pos_right (by positivity)).1 h2
  linarith

/-! ### Regularity -/

/-- The control simplex `U_T` is compact. (The same statement as `isCompact_controlSimplex` of
`SmoothedPolygons/Ch6/LiftedSystem.lean`, to be merged with it when that file is removed.) -/
theorem mx_isCompact_controlSimplex : IsCompact controlSimplex := by
  have hsub : controlSimplex ⊆ Set.pi univ (fun _ : Fin 3 ↦ Icc (0 : ℝ) 1) :=
    fun u hu i _ ↦ hu.1 i
  refine (isCompact_univ_pi fun _ ↦ isCompact_Icc).of_isClosed_subset ?_ hsub
  have e : controlSimplex = (⋂ i, {u : Fin 3 → ℝ | 0 ≤ u i ∧ u i ≤ 1}) ∩
      {u | u 0 + u 1 + u 2 = 1} := by
    ext u; simp [controlSimplex]
  rw [e]
  refine IsClosed.inter (isClosed_iInter fun i ↦ ?_) (isClosed_eq (by fun_prop) continuous_const)
  exact (isClosed_le continuous_const (continuous_apply i)).inter
    (isClosed_le (continuous_apply i) continuous_const)

/-- `GL₂⁺(ℝ) × C` is open. -/
theorem isOpen_matrixDomain : IsOpen matrixDomain := by
  have hc : Continuous fun q : MatrixState ↦ (stateG q).det := by
    simp only [stateG, Matrix.det_fin_two, Matrix.of_apply]; fun_prop
  have h0 : Continuous fun q : MatrixState ↦ ρ₀ (stateX q) := by
    simp only [ρ₀, stateX, slMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]; fun_prop
  have h1 : Continuous fun q : MatrixState ↦ ρ₁ (stateX q) := by
    simp only [ρ₁, stateX, slMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]; fun_prop
  have h2 : Continuous fun q : MatrixState ↦ ρ₂ (stateX q) := by
    simp only [ρ₂, stateX, slMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]; fun_prop
  exact (isOpen_lt continuous_const hc).inter ((isOpen_lt continuous_const h0).inter
    ((isOpen_lt continuous_const h1).inter (isOpen_lt continuous_const h2)))

/-- The denominator `⟨Z_u, X⟩` of `P` is negative on `GL₂⁺(ℝ) × C` for `u ∈ U_T` (Lemma 3.3.4). -/
theorem traceForm_controlMatrix_stateX_neg {q : MatrixState} (hq : q ∈ matrixDomain)
    {u : Fin 3 → ℝ} (hu : u ∈ controlSimplex) : traceForm (controlMatrix u) (stateX q) < 0 :=
  (lemma3_3_4 (stateX q) (trace_slMatrix _)).1 hq.2 u hu

/-- The dynamics satisfies the regularity hypotheses of the maximum principle on `GL₂⁺(ℝ) × C`:
it is jointly smooth where `⟨Z_u, X⟩ ≠ 0`, an open set containing `GL₂⁺(ℝ) × C × U_T`
(`traceForm_controlMatrix_stateX_neg`). -/
theorem isC1On_matrixField : IsC1On matrixField matrixDomain controlSimplex := by
  sorry

/-- The cost integrand is smooth (linear in `X`). -/
theorem isC1On_matrixCost : IsC1On matrixCost matrixDomain controlSimplex := by
  sorry

/-- The boundary map is smooth (polynomial). -/
theorem contDiff_matrixBoundary : ContDiff ℝ 1 matrixBoundary := by
  sorry

/-- **The boundary map is a submersion** at every `(q(0), q(t_f))` with `q(0) ∈ GL₂⁺(ℝ) × C`:
its derivative is block triangular, the identity on `g(0)`, three entries of `g(t_f)`, two
entries of `X(t_f)`, and the derivative `W ↦ -⟨X(0), W⟩` of `det` at `X(0)`, which is onto since
`X(0) ≠ 0`. -/
theorem surjective_fderiv_matrixBoundary {w : MatrixState × MatrixState}
    (hw : w.1 ∈ matrixDomain) : Function.Surjective (fderiv ℝ matrixBoundary w) := by
  sorry

/-! ### Directions tangent to the boundary condition

The tangent space `ker G'` of the boundary condition at `(q(0), q(t_f))` (dimension 4) is
spanned by the following vectors, which the transversality conditions are applied to
(`SmoothedPolygons/Ch6/MatrixCostate.lean`). -/

/-- The direction `E₁₁` of `g(t_f)` is tangent to the boundary condition (the equation
`g(t_f)₁₁ = R₁₁` is left out). -/
theorem fderiv_matrixBoundary_g₁₁ (w : MatrixState × MatrixState) :
    fderiv ℝ matrixBoundary w
      ((0 : MatrixState), ((Pi.single 1 (Pi.single 1 (1 : ℝ)) : Fin 2 → Fin 2 → ℝ), 0)) = 0 := by
  sorry

/-- The direction `E₁₀` of `X(t_f)` (the coordinate `c`) is tangent to the boundary condition
(the equation `X(t_f)₁₀ = (R⁻¹X(0)R)₁₀` is left out). -/
theorem fderiv_matrixBoundary_X₁₀ (w : MatrixState × MatrixState) :
    fderiv ℝ matrixBoundary w ((0 : MatrixState), (0, (Pi.single 2 (1 : ℝ) : Fin 3 → ℝ))) =
      0 := by
  sorry

/-- The variations `δX(0) = Y` with `⟨X(0), Y⟩ = 0` (tangent to `det X = 1`) together with
`δX(t_f) = R⁻¹YR` are tangent to the boundary condition: "the initial and terminal submanifolds
coincide after rotation by `R`" (§6.6, TeX 5191–5197). -/
theorem fderiv_matrixBoundary_conj (w : MatrixState × MatrixState) {y : Fin 3 → ℝ}
    (hy : traceForm (stateX w.1) (slMatrix y) = 0) :
    fderiv ℝ matrixBoundary w (((0 : Fin 2 → Fin 2 → ℝ), y),
      ((0 : Fin 2 → Fin 2 → ℝ), slCoords (R⁻¹ * slMatrix y * R))) = 0 := by
  sorry

end SmoothedPolygons
