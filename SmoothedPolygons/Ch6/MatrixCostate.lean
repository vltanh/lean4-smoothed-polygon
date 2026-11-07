module

public import SmoothedPolygons.Ch6.MatrixSystem
public import SmoothedPolygons.Ch6.Hamiltonian

/-!
# The costates of the matrix system in Lie-algebra form (§§6.4–6.6)

A covector `π` on the state space `MatrixState = Mat₂(ℝ) × ℝ³` of the matrix system
(`SmoothedPolygons/Ch6/MatrixSystem.lean`) has a `g`-part and an `X`-part, identified with
matrices by the trace form (§6.2, TeX 4806–4822; Appendix A):

* `covectorG π`, the matrix `p` with `π(W, 0) = tr(p W)` for every `W ∈ Mat₂(ℝ)`; its left
  trivialization `p g` (Proposition 3.6.1) made traceless is the costate
  `Λ₁ = p g - (tr(p g)/2) I₂ ∈ 𝔰𝔩₂(ℝ)` (`covectorΛ₁`; on `𝔰𝔩₂(ℝ)` it pairs with `X` as `p g` does);
* `covectorΛ₂ π ∈ 𝔰𝔩₂(ℝ)`, with `π(0, x) = ⟨Λ₂, X(x)⟩` (`X(x) = slMatrix x`), and the reduced
  costate `Λ_R = [Λ₂, X]` (`covectorΛR`, TeX 4966–4967).

The results, following the book:

* **The Hamiltonian** (§6.4, Proposition 6.4.1 and `eqn:full-hamiltonian`, TeX 4884–4990): the
  control-dependent Hamiltonian `⟨π, f(q, u)⟩ + λ_cost φ(q, u)` of the maximum principle is
  `H(Λ₁, Λ₂, X; Z_u)` (`fullHamiltonian`) and `H(Λ₁, Λ_R, X; Z_u)` (`hamiltonian`)
  (`controlHamiltonian_matrix_eq_fullHamiltonian`, `controlHamiltonian_matrix_eq_hamiltonian`).
* **Hamilton's equations** (proof of Proposition 6.5.1, TeX 5017–5070): the adjoint equation
  `π' = -∂H/∂q` of the maximum principle is, on its `g`-part, `p' = -X p` (`∂H/∂g = X p` for the
  trace pairing, `covectorG_comp_fderiv_matrixField`), and on its `X`-part
  `Λ₂' = -δH/δX` (`hasFunctionalDerivative_fullHamiltonian`). With `p̃ = p - (tr(p g)/2) g⁻¹`
  (so that `p̃ g = Λ₁`; `tr(p g)` is constant since `(p g)' = [p g, X]`), these are the hypotheses
  of `proposition6_5_1`, whose conclusion is the pair of costate equations `Λ₁' = [Λ₁, X]` and
  `eqn:lamR` (`hasDerivAt_covectorΛ_of_adjoint`; the Euler–Arnold equation `External.euler_arnold`
  gives the first, the book's derivation of `Λ_R' = [Λ₂', X] + [Λ₂, X']`, TeX 5071–5085, the
  second).
* **Transversality** (§6.6, TeX 5157–5215): on the conjugate variations
  (`fderiv_matrixBoundary_conj`) the transversality condition gives
  `Λ₂(0) - RΛ₂(t_f)R⁻¹ ⊥ [W, X(0)]` for all `W`, hence `[Λ₂(0) - RΛ₂(t_f)R⁻¹, X(0)] = 0` and
  `Λ_R(t_f) = R⁻¹Λ_R(0)R` (`covectorΛR_transversality`); on the two directions of the boundary
  equations left out (the departure E21 of `SmoothedPolygons/Ch6/MatrixSystem.lean`) it gives
  `p(t_f)₁₁ = 0` and `Λ₂(t_f)₀₁ = 0` (`covector_transversality_dropped`), which exclude the
  spurious multipliers: a covector with `Λ₁ = Λ_R = 0` at `t_f` and these two entries zero is zero
  (`eq_zero_of_covectorΛ_eq_zero`).
-/

@[expose] public section

namespace SmoothedPolygons

open Set Matrix Pontryagin ControlSystem

/-! ### The costates of a covector -/

/-- The matrix `p` of the `g`-part of a covector `π` for the trace pairing:
`tr(p W) = π(W, 0)` (`trace_covectorG_mul`), i.e. `p i j = π(E_{ji}, 0)`. -/
noncomputable def covectorG (π : StrongDual ℝ MatrixState) : Mat2 :=
  Matrix.of fun i j ↦ π (Pi.single j (Pi.single i 1), 0)

/-- The costate `Λ₂ ∈ 𝔰𝔩₂(ℝ)` of the `X`-part of a covector `π`: `⟨Λ₂, slMatrix x⟩ = π(0, x)`
(`traceForm_covectorΛ₂`). -/
noncomputable def covectorΛ₂ (π : StrongDual ℝ MatrixState) : Mat2 :=
  !![π (0, Pi.single 0 1) / 2, π (0, Pi.single 2 1);
    π (0, Pi.single 1 1), -(π (0, Pi.single 0 1) / 2)]

/-- The costate `Λ₁ ∈ 𝔰𝔩₂(ℝ)` of a covector `π` at the state `q`: the left trivialization
`p g` of the `g`-part (Proposition 3.6.1), made traceless, `Λ₁ = p g - (tr(p g)/2) I₂`. -/
noncomputable def covectorΛ₁ (q : MatrixState) (π : StrongDual ℝ MatrixState) : Mat2 :=
  covectorG π * stateG q - ((covectorG π * stateG q).trace / 2) • (1 : Mat2)

/-- The reduced costate `Λ_R = [Λ₂, X]` of a covector `π` at the state `q` (TeX 4966–4967). -/
noncomputable def covectorΛR (q : MatrixState) (π : StrongDual ℝ MatrixState) : Mat2 :=
  covectorΛ₂ π * stateX q - stateX q * covectorΛ₂ π

theorem trace_covectorG_mul (π : StrongDual ℝ MatrixState) (W : Mat2) :
    (covectorG π * W).trace = π (fun i j ↦ W i j, 0) := by
  have e : ((fun i j ↦ W i j, 0) : MatrixState) =
      W 0 0 • ((Pi.single 0 (Pi.single 0 1), 0) : MatrixState) +
      W 0 1 • ((Pi.single 0 (Pi.single 1 1), 0) : MatrixState) +
      W 1 0 • ((Pi.single 1 (Pi.single 0 1), 0) : MatrixState) +
      W 1 1 • ((Pi.single 1 (Pi.single 1 1), 0) : MatrixState) := by
    refine Prod.ext ?_ (by simp)
    funext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [e]
  simp only [map_add, map_smul, smul_eq_mul]
  simp [covectorG, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem traceForm_covectorΛ₂ (π : StrongDual ℝ MatrixState) (x : Fin 3 → ℝ) :
    traceForm (covectorΛ₂ π) (slMatrix x) = π (0, x) := by
  have e : ((0, x) : MatrixState) =
      x 0 • ((0, Pi.single 0 1) : MatrixState) + x 1 • ((0, Pi.single 1 1) : MatrixState) +
      x 2 • ((0, Pi.single 2 1) : MatrixState) := by
    refine Prod.ext (by simp) ?_
    funext i
    fin_cases i <;> simp
  rw [e]
  simp only [map_add, map_smul, smul_eq_mul]
  simp [covectorΛ₂, slMatrix, traceForm, Matrix.trace_fin_two]
  ring

theorem trace_covectorΛ₁ (q : MatrixState) (π : StrongDual ℝ MatrixState) :
    (covectorΛ₁ q π).trace = 0 := by
  simp [covectorΛ₁, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]

theorem trace_covectorΛ₂ (π : StrongDual ℝ MatrixState) : (covectorΛ₂ π).trace = 0 := by
  simp [covectorΛ₂, Matrix.trace_fin_two]

theorem trace_covectorΛR (q : MatrixState) (π : StrongDual ℝ MatrixState) :
    (covectorΛR q π).trace = 0 := by
  rw [covectorΛR, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

/-- `Λ_R = [Λ₂, X] ⊥ X`. -/
theorem traceForm_covectorΛR_stateX (q : MatrixState) (π : StrongDual ℝ MatrixState) :
    traceForm (covectorΛR q π) (stateX q) = 0 := by
  rw [traceForm, covectorΛR, Matrix.sub_mul, Matrix.trace_sub,
    Matrix.trace_mul_cycle (covectorΛ₂ π), sub_self]

/-! ### The Hamiltonian (§6.4) -/

/-- **The Hamiltonian in the Lie algebra** (§6.4, TeX 4884–4990): the control-dependent
Hamiltonian `⟨π, f(q, u)⟩ + λ_cost φ(q, u)` of the matrix system is
`H(Λ₁, Λ₂, X; Z_u) = ⟨Λ₁ - (3/2)λ_cost J, X⟩ + ⟨Λ₂, [Z_u, X]⟩/⟨X, Z_u⟩`. The group term
`π(gX, 0) = tr(p g X) = ⟨Λ₁, X⟩` is the content of Proposition 6.4.1 (`Λ₁` the left-trivialized
costate, `f(e, X, u) = X`), checked here in matrix coordinates, where it is the associativity
`tr(p (g X)) = tr((p g) X)`.

`proposition6_4_1` (stated for Mathlib's Lie groups) is not applied literally with
`G = Mat₂(ℝ)ˣ`: Mathlib's Lie-group structure on the units of a complete normed algebra
(`Mathlib/Geometry/Manifold/Instances/UnitsOfNormedAlgebra.lean`) needs a normed algebra
structure on `Mat₂(ℝ)`, which Mathlib provides only as a local choice
(`Matrix.linftyOpNormedAlgebra`); the hypothesis that the trace form is invariant on
`GroupLieAlgebra 𝓘(ℝ, Mat₂(ℝ)) Mat₂(ℝ)ˣ` needs that algebra's bracket (the bracket `mlieBracket`
of left-invariant vector fields at `1`) to be the matrix commutator, which Mathlib does not prove;
and the covector `π` would have to be identified with `leftTrivCovector g ⟨p g, ·⟩` through the
tangent map of left translation on the units. All of this for a one-line identity. -/
theorem controlHamiltonian_matrix_eq_fullHamiltonian (ν : ℝ) (q : MatrixState)
    (π : StrongDual ℝ MatrixState) (u : Fin 3 → ℝ) :
    controlHamiltonian matrixField matrixCost ν q π u =
      fullHamiltonian ν (covectorΛ₁ q π) (covectorΛ₂ π) (stateX q) u := by
  have e : matrixField q u = ((fun i j ↦ (stateG q * stateX q) i j, 0) : MatrixState) +
      ((0, slCoords (controlP u (stateX q) * stateX q - stateX q * controlP u (stateX q))) :
        MatrixState) := by
    ext <;> simp [matrixField]
  have hX : (stateX q).trace = 0 := trace_slMatrix _
  have hc : (controlP u (stateX q) * stateX q - stateX q * controlP u (stateX q)).trace = 0 := by
    rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
  rw [controlHamiltonian, e, map_add, ← trace_covectorG_mul, ← traceForm_covectorΛ₂,
    slMatrix_slCoords hc]
  simp only [fullHamiltonian, covectorΛ₁, matrixCost, controlP, traceForm, Matrix.sub_mul,
    Matrix.trace_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.one_mul, hX,
    smul_eq_mul, Matrix.mul_assoc, Matrix.mul_sub]
  rw [Matrix.trace_mul_comm (controlMatrix u) (stateX q)]
  ring

/-- **The Hamiltonian in the reduced costate** (`eqn:full-hamiltonian`, TeX 4966–4980):
`⟨Λ₂, [Z_u, X]⟩/⟨X, Z_u⟩ = -⟨Λ_R, Z_u⟩/⟨X, Z_u⟩` with `Λ_R = [Λ₂, X]`, so the Hamiltonian of
the maximum principle is `hamiltonian λ_cost Λ₁ Λ_R X u`. -/
theorem controlHamiltonian_matrix_eq_hamiltonian (ν : ℝ) (q : MatrixState)
    (π : StrongDual ℝ MatrixState) (u : Fin 3 → ℝ) :
    controlHamiltonian matrixField matrixCost ν q π u =
      hamiltonian ν (covectorΛ₁ q π) (covectorΛR q π) (stateX q) u := by
  rw [controlHamiltonian_matrix_eq_fullHamiltonian]
  simp only [fullHamiltonian, hamiltonian, covectorΛR, traceForm, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.trace_sub, ← Matrix.mul_assoc]
  rw [Matrix.trace_mul_cycle (covectorΛ₂ π) (controlMatrix u) (stateX q)]
  ring

/-! ### Hamilton's equations and the costate equations (§6.5) -/

/-- `covectorG` is linear: it commutes with negation. -/
private theorem mxc_covectorG_neg (π : StrongDual ℝ MatrixState) :
    covectorG (-π) = -covectorG π := by
  ext i j; simp [covectorG]

/-- `covectorΛ₂` is linear: it commutes with negation. -/
private theorem mxc_covectorΛ₂_neg (π : StrongDual ℝ MatrixState) :
    covectorΛ₂ (-π) = -covectorΛ₂ π := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [covectorΛ₂] <;> ring

/-- `slMatrix` is linear. -/
private theorem mxc_slMatrix_add_smul (x y : Fin 3 → ℝ) (s : ℝ) :
    slMatrix (x + s • y) = slMatrix x + s • slMatrix y := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [slMatrix]; ring

/-- The covector `π ∘ ∂f/∂q + λ_cost ∂φ/∂q` of the adjoint equation is the derivative at `q` of
the Hamiltonian `q' ↦ ⟨π, f(q', u)⟩ + λ_cost φ(q', u)` of the maximum principle; along the line
`s ↦ q + s v`, its value at `v`. -/
private theorem mxc_hasDerivAt_controlHamiltonian_line {ν : ℝ} {q : MatrixState}
    (hq : q ∈ matrixDomain) {u : Fin 3 → ℝ} (hu : u ∈ controlSimplex)
    (π : StrongDual ℝ MatrixState) (v : MatrixState) :
    HasDerivAt (fun s : ℝ ↦ controlHamiltonian matrixField matrixCost ν (q + s • v) π u)
      ((π.comp (fderiv ℝ (matrixField · u) q) + ν • fderiv ℝ (matrixCost · u) q) v) 0 := by
  have hF : HasFDerivAt (fun q' ↦ π (matrixField q' u) + ν * matrixCost q' u)
      (π.comp (fderiv ℝ (matrixField · u) q) + ν • fderiv ℝ (matrixCost · u) q) q :=
    (π.hasFDerivAt.comp q (isC1On_matrixField.differentiableAt q hq u hu).hasFDerivAt).fun_add
      ((isC1On_matrixCost.differentiableAt q hq u hu).hasFDerivAt.const_mul ν)
  have hl : HasDerivAt (fun s : ℝ ↦ q + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add q
  exact hF.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)

/-- An affine function of `s` has derivative its slope. -/
private theorem mxc_hasDerivAt_affine (a b : ℝ) : HasDerivAt (fun s : ℝ ↦ a + s * b) b 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const b).const_add a

/-- The quotient rule for two affine functions of `s`, at `s = 0`. -/
private theorem mxc_hasDerivAt_affine_div (a b c d : ℝ) (hc : c ≠ 0) :
    HasDerivAt (fun s : ℝ ↦ (a + s * b) / (c + s * d)) ((b * c - a * d) / c ^ 2) 0 := by
  simpa using (mxc_hasDerivAt_affine a b).fun_div (mxc_hasDerivAt_affine c d) (by simpa using hc)

/-- In a direction `(W, 0)` of the group variable, `∂H/∂q (W, 0) = tr(p W X)`:
`f(g + sW, X) = f(g, X) + s(WX, 0)`, and the cost does not depend on `g`. -/
private theorem mxc_apply_g (ν : ℝ) {q : MatrixState} (hq : q ∈ matrixDomain)
    {u : Fin 3 → ℝ} (hu : u ∈ controlSimplex) (π : StrongDual ℝ MatrixState)
    (W : Fin 2 → Fin 2 → ℝ) :
    (π.comp (fderiv ℝ (matrixField · u) q) + ν • fderiv ℝ (matrixCost · u) q) (W, 0) =
      (covectorG π * (Matrix.of W * stateX q)).trace := by
  have hX : ∀ s : ℝ, stateX (q + s • ((W, 0) : MatrixState)) = stateX q := fun s ↦ by
    simp [stateX]
  have hf : ∀ s : ℝ, matrixField (q + s • ((W, 0) : MatrixState)) u =
      matrixField q u + s • ((fun i j ↦ (Matrix.of W * stateX q) i j, 0) : MatrixState) := by
    intro s
    refine Prod.ext ?_ ?_
    · funext i j
      simp only [matrixField, hX, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, stateG]
      simp [Matrix.mul_apply, Fin.sum_univ_two]
      ring
    · simp only [matrixField, hX, Prod.snd_add, Prod.smul_snd, smul_zero, add_zero]
  have e : (fun s : ℝ ↦ controlHamiltonian matrixField matrixCost ν
      (q + s • ((W, 0) : MatrixState)) π u) = fun s ↦
        controlHamiltonian matrixField matrixCost ν q π u +
          s * (covectorG π * (Matrix.of W * stateX q)).trace := by
    funext s
    simp only [controlHamiltonian, hf, map_add, map_smul, smul_eq_mul, matrixCost, hX,
      trace_covectorG_mul]
    ring
  have h := mxc_hasDerivAt_controlHamiltonian_line (ν := ν) hq hu π (W, 0)
  rw [e] at h
  exact h.unique (mxc_hasDerivAt_affine _ _)

/-- **Hamilton's equations, `g`-part** (proof of Proposition 6.5.1, TeX 5025–5058): the `g`-part
of `∂H/∂q = π ∘ ∂f/∂q + λ_cost ∂φ/∂q` is `X p` for the trace pairing (`∂H/∂g` of
`H = tr(p g X) + …`; the cost and the `X`-dynamics do not depend on `g`). -/
theorem covectorG_comp_fderiv_matrixField (ν : ℝ) {q : MatrixState} (hq : q ∈ matrixDomain)
    {u : Fin 3 → ℝ} (hu : u ∈ controlSimplex) (π : StrongDual ℝ MatrixState) :
    covectorG (π.comp (fderiv ℝ (matrixField · u) q) + ν • fderiv ℝ (matrixCost · u) q) =
      stateX q * covectorG π := by
  ext i j
  rw [covectorG, Matrix.of_apply, mxc_apply_g ν hq hu π]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- **Hamilton's equations, `X`-part** (proof of Proposition 6.5.1, TeX 5059–5070): the `X`-part
of `∂H/∂q` is the functional derivative `δH/δX` of `Y ↦ H(Λ₁, Λ₂, Y; Z_u)` at `X`
(Definition A.2.1), by `controlHamiltonian_matrix_eq_fullHamiltonian` and the chain rule along
`s ↦ (g, X + sW)`. -/
theorem hasFunctionalDerivative_fullHamiltonian (ν : ℝ) {q : MatrixState}
    (hq : q ∈ matrixDomain) {u : Fin 3 → ℝ} (hu : u ∈ controlSimplex)
    (π : StrongDual ℝ MatrixState) :
    HasFunctionalDerivative (fun Y ↦ fullHamiltonian ν (covectorΛ₁ q π) (covectorΛ₂ π) Y u)
      (stateX q)
      (covectorΛ₂ (π.comp (fderiv ℝ (matrixField · u) q) + ν • fderiv ℝ (matrixCost · u) q)) := by
  refine ⟨trace_covectorΛ₂ _, fun W hW ↦ ?_⟩
  -- along `s ↦ (g, X + sW)` the Hamiltonian of the maximum principle is `H(Λ₁, Λ₂, X + sW; Z_u)`
  have e : (fun s : ℝ ↦ controlHamiltonian matrixField matrixCost ν
      (q + s • ((0, slCoords W) : MatrixState)) π u) = fun s ↦
        fullHamiltonian ν (covectorΛ₁ q π) (covectorΛ₂ π) (stateX q + s • W) u := by
    funext s
    rw [controlHamiltonian_matrix_eq_fullHamiltonian]
    have hg : stateG (q + s • ((0, slCoords W) : MatrixState)) = stateG q := by simp [stateG]
    have hX : stateX (q + s • ((0, slCoords W) : MatrixState)) = stateX q + s • W := by
      simp only [stateX, Prod.snd_add, Prod.smul_snd, mxc_slMatrix_add_smul, slMatrix_slCoords hW]
    simp only [covectorΛ₁, hg, hX]
  have h := mxc_hasDerivAt_controlHamiltonian_line (ν := ν) hq hu π (0, slCoords W)
  rw [e] at h
  convert h using 1
  rw [traceForm, Matrix.trace_mul_comm, ← traceForm, ← traceForm_covectorΛ₂,
    slMatrix_slCoords hW]

/-- Along a differentiable covector curve, `π ↦ π v` is differentiable. -/
private theorem mxc_hasDerivAt_apply {p : ℝ → StrongDual ℝ MatrixState}
    {p' : StrongDual ℝ MatrixState} {t : ℝ} (hp : HasDerivAt p p' t) (v : MatrixState) :
    HasDerivAt (fun s ↦ p s v) (p' v) t := by
  simpa using hp.clm_apply (hasDerivAt_const t v)

/-- `p ↦ covectorG p` is linear, so it commutes with derivatives. -/
private theorem mxc_hasDerivAtEntrywise_covectorG {p : ℝ → StrongDual ℝ MatrixState}
    {p' : StrongDual ℝ MatrixState} {t : ℝ} (hp : HasDerivAt p p' t) :
    HasDerivAtEntrywise (fun s ↦ covectorG (p s)) (covectorG p') t :=
  fun _ _ ↦ mxc_hasDerivAt_apply hp _

/-- `p ↦ covectorΛ₂ p` is linear, so it commutes with derivatives. -/
private theorem mxc_hasDerivAtEntrywise_covectorΛ₂ {p : ℝ → StrongDual ℝ MatrixState}
    {p' : StrongDual ℝ MatrixState} {t : ℝ} (hp : HasDerivAt p p' t) :
    HasDerivAtEntrywise (fun s ↦ covectorΛ₂ (p s)) (covectorΛ₂ p') t := by
  have h := mxc_hasDerivAt_apply hp
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [covectorΛ₂] <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, of_apply, cons_val', cons_val_zero,
      cons_val_one, cons_val_fin_one]
  exacts [(h _).div_const 2, h _, h _, ((h _).div_const 2).neg]

/-- `slMatrix` is linear, so it commutes with derivatives. -/
private theorem mxc_hasDerivAtEntrywise_slMatrix {x : ℝ → Fin 3 → ℝ} {x' : Fin 3 → ℝ} {t : ℝ}
    (h : HasDerivAt x x' t) : HasDerivAtEntrywise (fun s ↦ slMatrix (x s)) (slMatrix x') t := by
  have hk := hasDerivAt_pi.1 h
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [slMatrix] <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, of_apply, cons_val', cons_val_zero,
      cons_val_one, cons_val_fin_one]
  exacts [hk 0, hk 1, hk 2, (hk 0).neg]

/-- **The costate equations** (Proposition 6.5.1, `eqn:lamR`). At a time `t` where the state `q`
and the covector `p` of the maximum principle are differentiable, with `q' = f(q, u)` and the
adjoint equation `p' = -(p ∘ ∂f/∂q + λ_cost ∂φ/∂q)` (`u` the value of the control at `t`), the
costates satisfy `Λ₁' = [Λ₁, X]` and
`Λ_R' = [P, Λ_R] - ⟨Λ_R, P⟩[P, X] + [-Λ₁ + (3/2)λ_cost J, X]`.

Proof: `proposition6_5_1` with `g = stateG ∘ q`, `X = stateX ∘ q`, `Λ₂ = covectorΛ₂ ∘ p` and the
momentum `p̃ = covectorG ∘ p - (tr(p g)/2) g⁻¹` (`p̃ g = Λ₁` near `t`, where `det g > 0`). Its
hypotheses are Hamilton's equations: `g' = gX = ∂H/∂p̃`; `p̃' = -X p̃ = -∂H/∂g`
(`covectorG_comp_fderiv_matrixField`, `(tr(p g))' = tr[p g, X] = 0`, `(g⁻¹)' = -X g⁻¹`);
`X' = [P, X] = δH/δΛ₂`; `Λ₂' = -δH/δX` (`hasFunctionalDerivative_fullHamiltonian`). -/
theorem hasDerivAt_covectorΛ_of_adjoint {ν : ℝ} {q : ℝ → MatrixState}
    {p : ℝ → StrongDual ℝ MatrixState} {u : Fin 3 → ℝ} {t : ℝ} (hq : q t ∈ matrixDomain)
    (hu : u ∈ controlSimplex) (hq' : HasDerivAt q (matrixField (q t) u) t)
    (hp' : HasDerivAt p (-((p t).comp (fderiv ℝ (matrixField · u) (q t)) +
      ν • fderiv ℝ (matrixCost · u) (q t))) t) :
    HasDerivAtEntrywise (fun s ↦ covectorΛ₁ (q s) (p s))
        (covectorΛ₁ (q t) (p t) * stateX (q t) - stateX (q t) * covectorΛ₁ (q t) (p t)) t ∧
      HasDerivAtEntrywise (fun s ↦ covectorΛR (q s) (p s))
        (costateRHS ν (covectorΛ₁ (q t) (p t)) (covectorΛR (q t) (p t)) (stateX (q t)) u) t := by
  -- the book's variables along the curve: `g`, `X`, `Λ₂` and the momentum `p̃` with `p̃ g = Λ₁`
  set G : ℝ → Mat2 := fun s ↦ stateG (q s) with hGdef
  set Xs : ℝ → Mat2 := fun s ↦ stateX (q s) with hXsdef
  set L₂ : ℝ → Mat2 := fun s ↦ covectorΛ₂ (p s) with hL₂def
  set Pm : ℝ → Mat2 := fun s ↦
    covectorG (p s) - ((covectorG (p s) * G s).trace / 2) • (G s)⁻¹ with hPmdef
  set dp := -((p t).comp (fderiv ℝ (matrixField · u) (q t)) +
    ν • fderiv ℝ (matrixCost · u) (q t)) with hdpdef
  have hkey : ∀ s, (G s).det ≠ 0 → Pm s * G s = covectorΛ₁ (q s) (p s) := by
    intro s hs
    rw [hPmdef]
    simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hs)]
    rfl
  have hΛ₁t : Pm t * G t = covectorΛ₁ (q t) (p t) := hkey t hq.1.ne'
  have hev : (fun s ↦ covectorΛ₁ (q s) (p s)) =ᶠ[nhds t] fun s ↦ Pm s * G s := by
    have hmem : ∀ᶠ s in nhds t, q s ∈ matrixDomain :=
      hq'.continuousAt.preimage_mem_nhds (isOpen_matrixDomain.mem_nhds hq)
    filter_upwards [hmem] with s hs
    exact (hkey s hs.1.ne').symm
  have hden : traceForm (Xs t) (controlMatrix u) ≠ 0 := by
    rw [traceForm, Matrix.trace_mul_comm]
    exact (traceForm_controlMatrix_stateX_neg hq hu).ne
  -- Hamilton's equations, in the form of the hypotheses of Proposition 6.5.1
  have hq₁ : HasDerivAt (fun s ↦ (q s).1) (matrixField (q t) u).1 t :=
    (hasFDerivAt_fst (𝕜 := ℝ) (E := Fin 2 → Fin 2 → ℝ) (F := Fin 3 → ℝ)
      (p := q t)).comp_hasDerivAt t hq'
  have hq₂ : HasDerivAt (fun s ↦ (q s).2) (matrixField (q t) u).2 t :=
    (hasFDerivAt_snd (𝕜 := ℝ) (E := Fin 2 → Fin 2 → ℝ) (F := Fin 3 → ℝ)
      (p := q t)).comp_hasDerivAt t hq'
  -- `X' = [P, X]` and `g' = gX`: the state equation
  have hX : HasDerivAtEntrywise Xs (controlP u (Xs t) * Xs t - Xs t * controlP u (Xs t)) t := by
    refine (mxc_hasDerivAtEntrywise_slMatrix hq₂).congr_deriv ?_
    exact slMatrix_slCoords (by rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self])
  have hG : HasDerivAtEntrywise G (G t * Xs t) t := fun i j ↦
    hasDerivAt_pi.1 (hasDerivAt_pi.1 hq₁ i) j
  -- `Λ₂' = Λ₂(p')`, `p'` given by the adjoint equation
  have hL₂ : HasDerivAtEntrywise L₂ (covectorΛ₂ dp) t := mxc_hasDerivAtEntrywise_covectorΛ₂ hp'
  -- `p̃' = -X p̃`: `p' = -X p` (`covectorG_comp_fderiv_matrixField`), `tr(p g)` is constant
  -- (`(p g)' = -X p g + p g X`), and `(g⁻¹)' = -g⁻¹ g' g⁻¹ = -X g⁻¹`
  have hPm : HasDerivAtEntrywise Pm (-(Xs t * Pm t)) t := by
    have hdetG : IsUnit (G t).det := isUnit_iff_ne_zero.2 hq.1.ne'
    have hP₀ := mxc_hasDerivAtEntrywise_covectorG hp'
    have hdP : covectorG dp = -(Xs t * covectorG (p t)) := by
      rw [hdpdef, mxc_covectorG_neg, covectorG_comp_fderiv_matrixField ν hq hu]
    have hc : HasDerivAt (fun s ↦ (covectorG (p s) * G s).trace / 2) 0 t := by
      convert ((hP₀.mul hG).trace).div_const 2 using 1
      rw [hdP, Matrix.trace_add, Matrix.neg_mul, Matrix.trace_neg, Matrix.mul_assoc,
        Matrix.trace_mul_comm (Xs t), ← Matrix.mul_assoc]
      ring
    have hGi := hG.inv hdetG
    refine (hP₀.sub (HasDerivAtEntrywise.smul hc hGi)).congr_deriv ?_
    have e : (G t)⁻¹ * (G t * Xs t) * (G t)⁻¹ = Xs t * (G t)⁻¹ := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdetG, Matrix.one_mul]
    rw [hdP, e, hPmdef]
    simp only [zero_smul, add_zero, smul_neg, Matrix.mul_sub, Matrix.mul_smul]
    abel
  -- `δH/δΛ₂ = [P, X]`
  have hHΛ₂ : HasFunctionalDerivative (fun L ↦ fullHamiltonian ν (Pm t * G t) L (Xs t) u) (L₂ t)
      (controlP u (Xs t) * Xs t - Xs t * controlP u (Xs t)) := by
    refine ⟨by rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self], fun W _ ↦ ?_⟩
    have e : (fun s : ℝ ↦ fullHamiltonian ν (Pm t * G t) (L₂ t + s • W) (Xs t) u) = fun s ↦
        traceForm (Pm t * G t - (3 / 2 * ν) • J) (Xs t) +
          (traceForm (L₂ t) (controlMatrix u * Xs t - Xs t * controlMatrix u) +
            s * traceForm W (controlMatrix u * Xs t - Xs t * controlMatrix u)) /
          (traceForm (Xs t) (controlMatrix u) + s * 0) := by
      funext s
      simp [fullHamiltonian, traceForm, Matrix.add_mul, Matrix.trace_add, Matrix.trace_smul]
    rw [e]
    convert (mxc_hasDerivAt_affine_div _ _ _ _ hden).const_add _ using 1
    simp only [controlP, traceForm, Matrix.smul_mul, Matrix.mul_smul, ← smul_sub,
      Matrix.trace_smul, smul_eq_mul, mul_zero, sub_zero]
    rw [Matrix.trace_mul_comm (controlMatrix u) (Xs t)]
    field_simp
  -- `δH/δX = -Λ₂'` (`hasFunctionalDerivative_fullHamiltonian`)
  have hHX : HasFunctionalDerivative (fun Y ↦ fullHamiltonian ν (Pm t * G t) (L₂ t) Y u) (Xs t)
      (-covectorΛ₂ dp) := by
    rw [hΛ₁t, hdpdef, mxc_covectorΛ₂_neg, neg_neg]
    exact hasFunctionalDerivative_fullHamiltonian ν hq hu (p t)
  -- `∂H/∂p̃ = g X` and `∂H/∂g = X p̃` for the trace pairing (`H` depends on `(g, p̃)` through
  -- `p̃ g`, by `⟨p̃ g, X⟩ = tr(p̃ g X)`)
  have hHp : External.HasTraceGradient (fun r ↦ fullHamiltonian ν (r * G t) (L₂ t) (Xs t) u)
      (Pm t) (G t * Xs t) := by
    intro W
    have e : (fun s : ℝ ↦ fullHamiltonian ν ((Pm t + s • W) * G t) (L₂ t) (Xs t) u) = fun s ↦
        fullHamiltonian ν (Pm t * G t) (L₂ t) (Xs t) u + s * (G t * Xs t * W).trace := by
      funext s
      simp only [fullHamiltonian, traceForm, Matrix.trace_fin_two, Matrix.mul_apply,
        Fin.sum_univ_two, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    rw [e]
    exact mxc_hasDerivAt_affine _ _
  have hHg : External.HasTraceGradient (fun k ↦ fullHamiltonian ν (Pm t * k) (L₂ t) (Xs t) u)
      (G t) (-(-(Xs t * Pm t))) := by
    intro W
    have e : (fun s : ℝ ↦ fullHamiltonian ν (Pm t * (G t + s • W)) (L₂ t) (Xs t) u) = fun s ↦
        fullHamiltonian ν (Pm t * G t) (L₂ t) (Xs t) u + s * (Xs t * Pm t * W).trace := by
      funext s
      simp only [fullHamiltonian, traceForm, Matrix.trace_fin_two, Matrix.mul_apply,
        Fin.sum_univ_two, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    rw [e, neg_neg]
    exact mxc_hasDerivAt_affine _ _
  obtain ⟨h1, h2⟩ := proposition6_5_1 ν u Xs (fun s ↦ Pm s * G s) L₂ G Pm t _ _ _ _ rfl
    ⟨trace_slMatrix _, by rw [hΛ₁t]; exact trace_covectorΛ₁ _ _, trace_covectorΛ₂ _⟩ hden hX hL₂
    hG hPm hHΛ₂ hHX hHp hHg
  rw [hΛ₁t] at h1 h2
  exact ⟨h1.congr_of_eventuallyEq hev, h2⟩

/-! ### Transversality (§6.6) -/

/-- **Transversality in the directions of the boundary equations left out** (the departure E21
of `SmoothedPolygons/Ch6/MatrixSystem.lean`): with `(-π₀, π₁) ⊥ ker G'`, the directions
`(0, E₁₁)` of `g(t_f)` and `(0, E₁₀)` of `X(t_f)` (`fderiv_matrixBoundary_g₁₁`,
`fderiv_matrixBoundary_X₁₀`) give `p(t_f)₁₁ = π₁(E₁₁, 0) = 0` and
`Λ₂(t_f)₀₁ = π₁(0, e₂) = 0`. -/
theorem covector_transversality_dropped {q₀ q₁ : MatrixState}
    {π₀ π₁ : StrongDual ℝ MatrixState}
    (hT : ∀ v w : MatrixState, fderiv ℝ matrixBoundary (q₀, q₁) (v, w) = 0 → -π₀ v + π₁ w = 0) :
    covectorG π₁ 1 1 = 0 ∧ covectorΛ₂ π₁ 0 1 = 0 := by
  have h1 := hT _ _ (fderiv_matrixBoundary_g₁₁ (q₀, q₁))
  have h2 := hT _ _ (fderiv_matrixBoundary_X₁₀ (q₀, q₁))
  simp only [map_zero, neg_zero, zero_add] at h1 h2
  exact ⟨by simpa [covectorG] using h1, by simpa [covectorΛ₂] using h2⟩

/-- The trace pairing is nondegenerate on all of `Mat₂(ℝ)`. -/
private theorem mxc_eq_zero_of_trace_mul {M : Mat2} (h : ∀ W : Mat2, (M * W).trace = 0) :
    M = 0 := by
  ext i j
  have := h (Matrix.single j i 1)
  rw [Matrix.trace_mul_single] at this
  simpa using this

/-- `⟨D, [W, X]⟩ = tr([X, D] W)`. -/
private theorem mxc_traceForm_bracket (D X W : Mat2) :
    traceForm D (W * X - X * W) = ((X * D - D * X) * W).trace := by
  simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.sub_apply]
  ring

/-- `⟨X, [W, X]⟩ = 0`. -/
private theorem mxc_traceForm_bracket_self (X W : Mat2) : traceForm X (W * X - X * W) = 0 := by
  simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.sub_apply]
  ring

/-- **Transversality for `Λ_R`** (§6.6, `eqn:transversality`, TeX 5191–5212): "the initial and
terminal submanifolds coincide after rotation by `R`". On the variations
`(δX(0), δX(t_f)) = (Y, R⁻¹YR)` with `⟨X(0), Y⟩ = 0` (`fderiv_matrixBoundary_conj`) the
transversality condition gives `⟨Λ₂(0) - RΛ₂(t_f)R⁻¹, Y⟩ = 0`; taking `Y = [W, X(0)]` for all
traceless `W`, `[Λ₂(0) - RΛ₂(t_f)R⁻¹, X(0)] = 0`, so with `X(t_f) = R⁻¹X(0)R`,
`Λ_R(0) = [Λ₂(0), X(0)] = R[Λ₂(t_f), X(t_f)]R⁻¹ = RΛ_R(t_f)R⁻¹`. -/
theorem covectorΛR_transversality {q₀ q₁ : MatrixState} {π₀ π₁ : StrongDual ℝ MatrixState}
    (hT : ∀ v w : MatrixState, fderiv ℝ matrixBoundary (q₀, q₁) (v, w) = 0 → -π₀ v + π₁ w = 0)
    (hX : stateX q₁ = R⁻¹ * stateX q₀ * R) :
    covectorΛR q₁ π₁ = R⁻¹ * covectorΛR q₀ π₀ * R := by
  have hRR : ∀ M : Mat2, R⁻¹ * (R * M) = M := fun M ↦ by
    rw [← Matrix.mul_assoc, mx_R_inv_mul_R, Matrix.one_mul]
  -- transversality on the conjugate variations: `⟨Λ₂(0) - RΛ₂(t_f)R⁻¹, Y⟩ = 0` for `Y ⊥ X(0)`
  have hY : ∀ Y : Mat2, Y.trace = 0 → traceForm (stateX q₀) Y = 0 →
      traceForm (covectorΛ₂ π₀ - R * covectorΛ₂ π₁ * R⁻¹) Y = 0 := by
    intro Y hYtr hYX
    have hc : (R⁻¹ * Y * R).trace = 0 := by
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, mx_R_mul_R_inv, Matrix.one_mul, hYtr]
    have h := hT _ _ (fderiv_matrixBoundary_conj (q₀, q₁) (y := slCoords Y)
      (by rw [slMatrix_slCoords hYtr]; exact hYX))
    rw [slMatrix_slCoords hYtr, ← traceForm_covectorΛ₂, ← traceForm_covectorΛ₂,
      slMatrix_slCoords hYtr, slMatrix_slCoords hc] at h
    have e : traceForm (covectorΛ₂ π₁) (R⁻¹ * Y * R) =
        traceForm (R * covectorΛ₂ π₁ * R⁻¹) Y := by
      simp only [traceForm]
      rw [show covectorΛ₂ π₁ * (R⁻¹ * Y * R) = covectorΛ₂ π₁ * R⁻¹ * Y * R by
        simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    rw [traceForm, Matrix.sub_mul, Matrix.trace_sub, ← traceForm, ← traceForm, ← e]
    linarith
  -- `Y = [W, X(0)]` for every `W`: `[X(0), Λ₂(0) - RΛ₂(t_f)R⁻¹] = 0`
  have hC : stateX q₀ * (covectorΛ₂ π₀ - R * covectorΛ₂ π₁ * R⁻¹) -
      (covectorΛ₂ π₀ - R * covectorΛ₂ π₁ * R⁻¹) * stateX q₀ = 0 := by
    refine mxc_eq_zero_of_trace_mul fun W ↦ ?_
    rw [← mxc_traceForm_bracket]
    exact hY _ (by rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self])
      (mxc_traceForm_bracket_self _ _)
  -- so `Λ_R(0) = [RΛ₂(t_f)R⁻¹, X(0)]`, and `Λ_R(t_f) = [Λ₂(t_f), R⁻¹X(0)R] = R⁻¹Λ_R(0)R`
  have hΛ₀ : covectorΛR q₀ π₀ = R * covectorΛ₂ π₁ * R⁻¹ * stateX q₀ -
      stateX q₀ * (R * covectorΛ₂ π₁ * R⁻¹) := by
    have e : covectorΛR q₀ π₀ = (R * covectorΛ₂ π₁ * R⁻¹ * stateX q₀ -
        stateX q₀ * (R * covectorΛ₂ π₁ * R⁻¹)) -
        (stateX q₀ * (covectorΛ₂ π₀ - R * covectorΛ₂ π₁ * R⁻¹) -
          (covectorΛ₂ π₀ - R * covectorΛ₂ π₁ * R⁻¹) * stateX q₀) := by
      simp only [covectorΛR, Matrix.mul_sub, Matrix.sub_mul]
      abel
    rw [e, hC, sub_zero]
  rw [hΛ₀, covectorΛR, hX]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hRR, mx_R_inv_mul_R,
    Matrix.mul_one]

/-- **The spurious multipliers are excluded at `t_f`**: at a state with `g = R` and `X₀₁ ≠ 0`, a
covector with `Λ₁ = 0` and `Λ_R = 0` is `(p, Λ₂) = (k R⁻¹, c X)` (`p R = (tr(p R)/2) I₂`, and
`[Λ₂, X] = 0`); `p₁₁ = k (R⁻¹)₁₁ = k/2` and `Λ₂₀₁ = c X₀₁`, so the transversality conditions of
`covector_transversality_dropped` give `k = c = 0`, and the covector vanishes. -/
theorem eq_zero_of_covectorΛ_eq_zero {q : MatrixState} {π : StrongDual ℝ MatrixState}
    (hg : stateG q = R) (hX : stateX q 0 1 ≠ 0) (h₁ : covectorΛ₁ q π = 0)
    (hR : covectorΛR q π = 0) (hG : covectorG π 1 1 = 0) (h₂ : covectorΛ₂ π 0 1 = 0) :
    π = 0 := by
  -- `p = κ R⁻¹` with `κ = tr(p R)/2`, and `p₁₁ = κ (R⁻¹)₁₁ = κ/2`
  set κ := (covectorG π * R).trace / 2 with hκ
  have hpR : covectorG π * R = κ • (1 : Mat2) := by
    rw [covectorΛ₁, hg, sub_eq_zero] at h₁; exact h₁
  have hp : covectorG π = κ • R⁻¹ := by
    calc covectorG π = covectorG π * R * R⁻¹ := by
          rw [Matrix.mul_assoc, mx_R_mul_R_inv, Matrix.mul_one]
      _ = κ • R⁻¹ := by rw [hpR, Matrix.smul_mul, Matrix.one_mul]
  have hκ0 : κ = 0 := by
    have := hG
    rw [hp, mx_R_inv] at this
    simp at this
    linarith
  have hp0 : covectorG π = 0 := by rw [hp, hκ0, zero_smul]
  -- `Λ₂ = 0`: `[Λ₂, X] = 0`, `Λ₂₀₁ = 0` and `X₀₁ ≠ 0`
  have hΛ : covectorΛ₂ π = 0 := by
    have e00 := congrFun (congrFun hR 0) 0
    have e01 := congrFun (congrFun hR 0) 1
    have htr := trace_covectorΛ₂ π
    have hXtr : stateX q 1 1 = -stateX q 0 0 := by simp [stateX, slMatrix]
    rw [Matrix.trace_fin_two] at htr
    simp only [covectorΛR, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.zero_apply] at e00 e01
    rw [h₂] at e00 e01
    have hc : covectorΛ₂ π 1 0 = 0 := by
      have : stateX q 0 1 * covectorΛ₂ π 1 0 = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hX
    have h11 : covectorΛ₂ π 1 1 = -covectorΛ₂ π 0 0 := by linarith
    have ha : covectorΛ₂ π 0 0 = 0 := by
      rw [h11] at e01
      have : 2 * covectorΛ₂ π 0 0 * stateX q 0 1 = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · exact absurd h hX
    have hd : covectorΛ₂ π 1 1 = 0 := by rw [h11, ha, neg_zero]
    ext i j; fin_cases i <;> fin_cases j <;> simp [ha, hc, h₂, hd]
  -- so `π(W, x) = tr(p W) + ⟨Λ₂, X(x)⟩ = 0`
  refine ContinuousLinearMap.ext fun ⟨W, x⟩ ↦ ?_
  have e : ((W, x) : MatrixState) =
      ((fun i j ↦ (Matrix.of W) i j, 0) : MatrixState) + (0, x) := by
    ext <;> simp
  rw [e, map_add, ← trace_covectorG_mul, ← traceForm_covectorΛ₂, hp0, hΛ]
  simp [traceForm]

end SmoothedPolygons
