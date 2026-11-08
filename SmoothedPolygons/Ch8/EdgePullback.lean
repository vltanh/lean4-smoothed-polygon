module

public import SmoothedPolygons.Ch8.EdgeProblem

/-!
# The Reinhardt costate pulled back to an edge arc

Let an extremal lifted trajectory of the Reinhardt problem have its control in the edge
`{u_j = 0}` of `U_T` on `[c, d]`. In the frame `edgeFrame j` (tildes) the trajectory lies on the
edge submanifold of (8.1.1) (`eqn_g_edge`): `g̃ = g̃(c) h(q(0))⁻¹ h(q)`, `X̃ = Φ(x, y)`, with
`h = edgeH q = [[1, -x], [s, 1 - s x]]` and `q = (x, y, s)` the edge state (`eqn_xy_edge`). The
Reinhardt costate `(Λ₁, Λ₂)` (`Λ₂` the costate of `X`, `Λ_R = [Λ₂, X]`, so `Λ̃₂ = ¼[X̃, Λ̃_R]`
since `X̃² = -I` and `Λ̃_R ⊥ X̃`) pulls back along `q ↦ (g̃, X̃)` to the covector
`⟨Λ̃₁, h⁻¹ dh⟩ + ⟨Λ̃₂, dΦ⟩` on the edge state space. Shifted by `(3/2) λ_cost d(s + x)` (the cost
identity `edgeCost_identity`: the Reinhardt running cost is `(3/2)(s' + x' + x²/y)`), it is the
covector `edgePullback`,

* `λ_x = ⟨Λ̃₁, h⁻¹ ∂ₓh⟩ + ⟨Λ̃₂, ∂ₓΦ⟩ + (3/2) λ_cost`,
* `λ_y = ⟨Λ̃₂, ∂_yΦ⟩`,
* `λ_s = ⟨Λ̃₁, h⁻¹ ∂ₛh⟩ + (3/2) λ_cost`,

and with `ν = (3/2) λ_cost` it is a costate of the edge control problem (Definition 8.1.1):

* `IsExtremalOn.controlHamiltonian_edgePullback`: the edge Hamiltonian (8.1.6) of the pulled-back
  covector equals the Reinhardt Hamiltonian at the corresponding control of the edge, at every time
  and for every edge control (`H_e = H_R`);
* `IsExtremalOn.isAdjoint_edgePullback`: it solves the adjoint equation of the edge problem;
* `IsExtremalOn.isMaximal_edgePullback`: it satisfies the maximum condition of the edge problem;
* `IsExtremalOn.isEdgeProblemExtremal_edgePullback`: for a normal extremal (`λ_cost ≠ 0`) it lifts
  the edge arc to an extremal of the edge control problem (`IsEdgeProblemExtremal`);
* `IsExtremalOn.isEdgeExtremalOn_of_ne_zero`, `IsNormalExtremal.isEdgeExtremalOn`: every normal
  extremal is edge extremal (Definition 8.1.2).

This is the repair, along the book's lines, of the edge case of Theorem 8.2.7 for normal lifts
(`SmoothedPolygons/Ch8/NoSingularArcs.lean`, E55): the book connects the two problems through
(8.1.1) and the cost identity (TeX 6704–6754) and says that edges are handled by the edge problem
(TeX 7253–7258, 806–821), without relating the costates. For abnormal lifts (`λ_cost = 0`) the
pulled-back covector can vanish identically: exactly when the Reinhardt costate is conormal to the
edge submanifold (the family that contains Remark 8.1.6's, `remark8_1_6`); then it gives no edge
costate. Before the proofs were written, the formulas were checked numerically: along a normal
extremal with control in an edge, integrated together with the edge state `(x, y, s)`, the
pulled-back covector satisfies `H_e = H_R`, the adjoint equation (8.1.7) and the maximum
condition of the edge problem.
-/

@[expose] public section

namespace SmoothedPolygons

open Set MeasureTheory Filter Topology Matrix

/-- The covector `l₁ dx + l₂ dy + l₃ ds` on the state space `(x, y, s)` of the edge control
problem: `edgeCostate (edgeCovector l₁ l₂ l₃) = ![l₁, l₂, l₃]`. -/
noncomputable def edgeCovector (l₁ l₂ l₃ : ℝ) : StrongDual ℝ (Fin 3 → ℝ) :=
  l₁ • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 ↦ ℝ) 0 +
    l₂ • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 ↦ ℝ) 1 +
    l₃ • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 ↦ ℝ) 2

/-- The control of the edge `{u_j = 0}` of `U_T` with edge parameter `v`: `u_j = 0`,
`u_{j+1} = ½ + v`, `u_{j+2} = ½ - v`. After the rotation `edgeFrame j` it is
`edgeControl v = (0, ½ + v, ½ - v)` (TeX 6684–6689), and `edgeParam j (edgeControlIn j v) = v`. -/
noncomputable def edgeControlIn (j : Fin 3) (v : ℝ) : Fin 3 → ℝ := fun m ↦ edgeControl v (m - j)

/-- An edge control `v ∈ [-½, ½]` gives a control `edgeControlIn j v` in `U_T`. -/
theorem edgeControlIn_mem_controlSimplex {j : Fin 3} {v : ℝ} (hv : v ∈ edgeControlSet) :
    edgeControlIn j v ∈ controlSimplex := by
  obtain ⟨h1, h2⟩ := hv
  refine ⟨fun m ↦ ?_, ?_⟩
  · fin_cases j <;> fin_cases m <;> simp [edgeControlIn, edgeControl] <;> constructor <;> linarith
  · fin_cases j <;> simp [edgeControlIn, edgeControl] <;> norm_num

/-- The edge parameter of `edgeControlIn j v` is `v`. -/
private theorem l3i_edgeParam_edgeControlIn (j : Fin 3) (v : ℝ) :
    edgeParam j (edgeControlIn j v) = v := by
  fin_cases j <;> simp [edgeParam, edgeControlIn, edgeControl]

/-- A control in the edge `{u_j = 0}` is `edgeControlIn j` of its edge parameter. -/
theorem edgeControlIn_edgeParam {j : Fin 3} {u : Fin 3 → ℝ} (hu : u ∈ controlEdge j) :
    edgeControlIn j (edgeParam j u) = u := by
  obtain ⟨⟨-, hs⟩, hj⟩ := hu
  funext m
  fin_cases j <;> fin_cases m <;> simp [edgeParam, edgeControlIn, edgeControl] at hj ⊢ <;>
    linarith

/-- The rotation `edgeFrame j` takes the control matrix of `edgeControlIn j v` to that of
`edgeControl v = (0, ½ + v, ½ - v)`. -/
private theorem l3i_edgeFrame_controlMatrix_edgeControlIn (j : Fin 3) (v : ℝ) :
    edgeFrame j (controlMatrix (edgeControlIn j v)) = controlMatrix (edgeControl v) := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3' : √3 ≠ 0 := by positivity
  have h4 : √3 ^ 4 = 9 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h3]; norm_num
  have hc : ∀ j : Fin 3, edgeControlIn j v = fun m ↦ edgeControl v (m - j) := fun _ ↦ rfl
  fin_cases j <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [hc, edgeFrame, edgeControl, controlMatrix, R, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.inv_def, Matrix.det_fin_two, pow_two] <;> field_simp <;> ring_nf <;>
    simp [h3, h4] <;> ring_nf

/-- The costate `Λ̃₂ = ¼ [X̃, Λ̃_R]` of the Lie-algebra variable in the frame `edgeFrame j`
(`X̃ = edgeFrame j X`, `Λ̃_R = edgeFrame j Λ_R`): for `X̃` with `det X̃ = 1`, `tr X̃ = 0` and
`Λ̃_R` traceless with `⟨Λ̃_R, X̃⟩ = 0`, it satisfies `[Λ̃₂, X̃] = Λ̃_R` (§6.4: `Λ_R = [Λ₂, X]`;
`Λ₂` is determined modulo `ℝX`, which the pairing with tangent vectors of the orbit does not
see). -/
noncomputable def edgeΛ₂ (j : Fin 3) (ΛR X : Mat2) : Mat2 :=
  (1 / 4 : ℝ) • (edgeFrame j X * edgeFrame j ΛR - edgeFrame j ΛR * edgeFrame j X)

/-- **The pulled-back costate** on the state space of the `j`-th edge control problem: the
covector `(λ_x, λ_y, λ_s)` with

* `λ_x = ⟨Λ̃₁, h⁻¹ ∂ₓh⟩ + ⟨Λ̃₂, ∂ₓΦ⟩ + (3/2) λ_cost`,
* `λ_y = ⟨Λ̃₂, ∂_yΦ⟩`,
* `λ_s = ⟨Λ̃₁, h⁻¹ ∂ₛh⟩ + (3/2) λ_cost`,

where the tildes are `edgeFrame j`, `h = edgeH q = [[1, -x], [s, 1 - s x]]` (8.1.1), so
`∂ₓh = [[0, -1], [0, -s]]` and `∂ₛh = [[0, 0], [1, -x]]`, `Λ̃₂ = edgeΛ₂ j Λ_R X`, and
`∂ₓΦ = [[1/y, -2x/y], [0, -1/y]]`, `∂_yΦ = [[-x/y², (x² - y²)/y²], [-1/y², x/y²]]` are the partial
derivatives of `Φ(x, y)` (Lemma 4.2.1), at `q = (x, y, s)`. It is the pullback of `(Λ₁, Λ₂)` along
the edge submanifold `q ↦ (g̃(c) h(q(0))⁻¹ h(q), Φ(x, y))` shifted by `(3/2) λ_cost d(x + s)`. -/
noncomputable def edgePullback (j : Fin 3) (lam : ℝ) (Λ₁ ΛR X : Mat2) (q : Fin 3 → ℝ) :
    StrongDual ℝ (Fin 3 → ℝ) :=
  edgeCovector
    (traceForm (edgeFrame j Λ₁) ((edgeH q)⁻¹ * !![0, -1; 0, -q 2]) +
      traceForm (edgeΛ₂ j ΛR X) !![1 / q 1, -(2 * q 0 / q 1); 0, -(1 / q 1)] + 3 / 2 * lam)
    (traceForm (edgeΛ₂ j ΛR X)
      !![-(q 0 / q 1 ^ 2), (q 0 ^ 2 - q 1 ^ 2) / q 1 ^ 2; -(1 / q 1 ^ 2), q 0 / q 1 ^ 2])
    (traceForm (edgeFrame j Λ₁) ((edgeH q)⁻¹ * !![0, 0; 1, -q 0]) + 3 / 2 * lam)

/-! ### Algebra of the pulled-back costate -/

/-- The components of `edgeCovector`. -/
private lemma l3i_edgeCostate_edgeCovector (l₁ l₂ l₃ : ℝ) :
    edgeCostate (edgeCovector l₁ l₂ l₃) 0 = l₁ ∧ edgeCostate (edgeCovector l₁ l₂ l₃) 1 = l₂ ∧
      edgeCostate (edgeCovector l₁ l₂ l₃) 2 = l₃ := by
  simp [edgeCovector, edgeCostate]

private lemma l3i_edgeCostate_edgeCovector_zero (l₁ l₂ l₃ : ℝ) :
    edgeCostate (edgeCovector l₁ l₂ l₃) 0 = l₁ := (l3i_edgeCostate_edgeCovector l₁ l₂ l₃).1

private lemma l3i_edgeCostate_edgeCovector_one (l₁ l₂ l₃ : ℝ) :
    edgeCostate (edgeCovector l₁ l₂ l₃) 1 = l₂ := (l3i_edgeCostate_edgeCovector l₁ l₂ l₃).2.1

private lemma l3i_edgeCostate_edgeCovector_two (l₁ l₂ l₃ : ℝ) :
    edgeCostate (edgeCovector l₁ l₂ l₃) 2 = l₃ := (l3i_edgeCostate_edgeCovector l₁ l₂ l₃).2.2

/-- Covectors on `ℝ³` with the same components are equal. -/
private lemma l3i_ext {p p' : StrongDual ℝ (Fin 3 → ℝ)}
    (h0 : edgeCostate p 0 = edgeCostate p' 0) (h1 : edgeCostate p 1 = edgeCostate p' 1)
    (h2 : edgeCostate p 2 = edgeCostate p' 2) : p = p' := by
  ext w
  rw [apply_eq_sum_edgeCostate p, apply_eq_sum_edgeCostate p', h0, h1, h2]

/-- `E = [[0, 1], [0, 0]]`, the generator of the translations of the half-plane:
`∂ₓΦ = [E, Φ]` and `∂_yΦ = ½ [[E, Φ], Φ]`. -/
private noncomputable def l3i_E : Mat2 := !![0, 1; 0, 0]

/-- The component `λ_x` of the pulled-back costate in terms of `Λ̃₁`, `Λ̃_R`, `X̃`. -/
private noncomputable def l3i_gx (lam : ℝ) (A B X : Mat2) : ℝ :=
  traceForm A !![0, -1; 0, 0] +
    traceForm ((1 / 4 : ℝ) • (X * B - B * X)) (l3i_E * X - X * l3i_E) + 3 / 2 * lam

/-- The component `λ_y` of the pulled-back costate in terms of `Λ̃_R`, `X̃`. -/
private noncomputable def l3i_gy (B X : Mat2) : ℝ :=
  traceForm ((1 / 4 : ℝ) • (X * B - B * X))
    ((1 / 2 : ℝ) • ((l3i_E * X - X * l3i_E) * X - X * (l3i_E * X - X * l3i_E)))

/-- The component `λ_s` of the pulled-back costate in terms of `Λ̃₁` and `x`. -/
private noncomputable def l3i_gs (lam : ℝ) (A : Mat2) (x : ℝ) : ℝ :=
  x * (A 0 0 - A 1 1) + A 0 1 - x ^ 2 * A 1 0 + 3 / 2 * lam

/-- `h⁻¹ = [[1 - s x, x], [-s, 1]]` (`det h = 1`). -/
private lemma l3i_edgeH_inv (q : Fin 3 → ℝ) : (edgeH q)⁻¹ = !![1 - q 2 * q 0, q 0; -q 2, 1] := by
  apply Matrix.inv_eq_left_inv
  ext i k
  fin_cases i <;> fin_cases k <;> simp [edgeH, Matrix.mul_apply] <;> ring

/-- The components of the pulled-back costate, where `X̃ = Φ(x, y)`. -/
private lemma l3i_edgePullback_apply {j : Fin 3} {lam : ℝ} {Λ₁ ΛR X : Mat2} {q : Fin 3 → ℝ}
    (hX : edgeFrame j X = Φ (q 0) (q 1)) (hy : q 1 ≠ 0) :
    edgeCostate (edgePullback j lam Λ₁ ΛR X q) 0 =
        l3i_gx lam (edgeFrame j Λ₁) (edgeFrame j ΛR) (edgeFrame j X) ∧
      edgeCostate (edgePullback j lam Λ₁ ΛR X q) 1 = l3i_gy (edgeFrame j ΛR) (edgeFrame j X) ∧
      edgeCostate (edgePullback j lam Λ₁ ΛR X q) 2 = l3i_gs lam (edgeFrame j Λ₁) (q 0) := by
  obtain ⟨h0, h1, h2⟩ := l3i_edgeCostate_edgeCovector
    (traceForm (edgeFrame j Λ₁) ((edgeH q)⁻¹ * !![0, -1; 0, -q 2]) +
      traceForm (edgeΛ₂ j ΛR X) !![1 / q 1, -(2 * q 0 / q 1); 0, -(1 / q 1)] + 3 / 2 * lam)
    (traceForm (edgeΛ₂ j ΛR X)
      !![-(q 0 / q 1 ^ 2), (q 0 ^ 2 - q 1 ^ 2) / q 1 ^ 2; -(1 / q 1 ^ 2), q 0 / q 1 ^ 2])
    (traceForm (edgeFrame j Λ₁) ((edgeH q)⁻¹ * !![0, 0; 1, -q 0]) + 3 / 2 * lam)
  have hM0 : (edgeH q)⁻¹ * !![0, -1; 0, -q 2] = !![0, -1; 0, 0] := by
    rw [l3i_edgeH_inv]; ext i k; fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply]
    ring
  have hMs : (edgeH q)⁻¹ * !![0, 0; 1, -q 0] = !![q 0, -q 0 ^ 2; 1, -q 0] := by
    rw [l3i_edgeH_inv]; ext i k; fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply]
    ring
  have hdx : !![1 / q 1, -(2 * q 0 / q 1); 0, -(1 / q 1)] =
      l3i_E * Φ (q 0) (q 1) - Φ (q 0) (q 1) * l3i_E := by
    ext i k; fin_cases i <;> fin_cases k <;> simp [l3i_E, Φ]
    ring
  have hdy : !![-(q 0 / q 1 ^ 2), (q 0 ^ 2 - q 1 ^ 2) / q 1 ^ 2; -(1 / q 1 ^ 2), q 0 / q 1 ^ 2] =
      (1 / 2 : ℝ) • ((l3i_E * Φ (q 0) (q 1) - Φ (q 0) (q 1) * l3i_E) * Φ (q 0) (q 1) -
        Φ (q 0) (q 1) * (l3i_E * Φ (q 0) (q 1) - Φ (q 0) (q 1) * l3i_E)) := by
    ext i k; fin_cases i <;> fin_cases k <;> simp [l3i_E, Φ] <;> field_simp <;> ring
  refine ⟨?_, ?_, ?_⟩
  · rw [edgePullback, h0, hM0, hdx, ← hX]; rfl
  · rw [edgePullback, h1, hdy, ← hX]; rfl
  · rw [edgePullback, h2, hMs, l3i_gs]
    simp [traceForm, Matrix.trace_fin_two, Matrix.mul_apply]
    ring

/-- A traceless matrix orthogonal to `Φ(x, y)` (`y ≠ 0`) is determined by two entries. -/
private lemma l3i_eq_of_perp {B : Mat2} {x y : ℝ} (hy : y ≠ 0) (hB : B.trace = 0)
    (hBX : traceForm B (Φ x y) = 0) :
    B = !![B 0 0, B 1 0 * (x ^ 2 + y ^ 2) - 2 * B 0 0 * x; B 1 0, -B 0 0] := by
  rw [Matrix.trace_fin_two] at hB
  have key : B 0 0 * x + B 0 1 - B 1 0 * (x ^ 2 + y ^ 2) - B 1 1 * x = 0 := by
    have : traceForm B (Φ x y) * y = 0 := by rw [hBX, zero_mul]
    simp only [traceForm, Φ, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one] at this
    field_simp at this
    linear_combination this
  ext i k
  fin_cases i <;> fin_cases k <;> simp
  · linear_combination key + x * hB
  · linear_combination hB

/-- The control matrix of `edgeControl v`, with `w = √3 v`. -/
private lemma l3i_controlMatrix_edgeControl (v : ℝ) :
    controlMatrix (edgeControl v) = !![2 * (√3 * v) / 3, -2 / 3; 0, -(2 * (√3 * v) / 3)] := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3' : √3 ≠ 0 := by positivity
  have key : ∀ a : ℝ, a / √3 = √3 * a / 3 := fun a ↦ by
    rw [div_eq_div_iff h3' (by norm_num)]; linear_combination (-a) * h3
  ext i k
  fin_cases i <;> fin_cases k <;> simp [controlMatrix, edgeControl, key] <;> ring

/-- **`H_e = H_R`, the core identity** (`w = √3 u_e`): with `X = Φ(x, y)` and `Λ̃_R` traceless and
orthogonal to `X`, the edge Hamiltonian of the pulled-back costate is the Reinhardt Hamiltonian at
the edge control. -/
private lemma l3i_core_H (lam x y w a1 b1 c1 d1 a2 c2 : ℝ) (hy : y ≠ 0)
    (hD : -1 + 2 * x * w ≠ 0) {A B : Mat2} (hA : A = !![a1, b1; c1, d1])
    (hB : B = !![a2, c2 * (x ^ 2 + y ^ 2) - 2 * a2 * x; c2, -a2]) :
    l3i_gx lam A B (Φ x y) * y + l3i_gy B (Φ x y) * (2 * y ^ 2 * w / (-1 + 2 * x * w)) +
        l3i_gs lam A x / y + 3 / 2 * lam * (x ^ 2 / y) =
      traceForm (A - (3 / 2 * lam) • J) (Φ x y) -
        traceForm B !![2 * w / 3, -2 / 3; 0, -(2 * w / 3)] /
          traceForm (Φ x y) !![2 * w / 3, -2 / 3; 0, -(2 * w / 3)] := by
  subst hA hB
  have hDa : -1 + x * 2 * w ≠ 0 := by rwa [mul_comm x 2]
  have hZX : traceForm (Φ x y) !![2 * w / 3, -2 / 3; 0, -(2 * w / 3)] =
      2 * (-1 + 2 * x * w) / (3 * y) := by
    simp [traceForm, Φ, Matrix.trace_fin_two]
    field_simp
    ring
  rw [hZX]
  simp [l3i_gx, l3i_gy, l3i_gs, l3i_E, traceForm, Φ, J, Matrix.trace_fin_two]
  field_simp
  ring

/-- The rotation `edgeFrame j` is a conjugation (`R⁻ʲ Rʲ = 1`). -/
private lemma l3i_conj (j : Fin 3) : R⁻¹ ^ (j : ℕ) * R ^ (j : ℕ) = 1 :=
  poly_Rinvpow_mul_Rpow (j : ℕ)

private lemma l3i_fr_add (j : Fin 3) (M N : Mat2) :
    edgeFrame j (M + N) = edgeFrame j M + edgeFrame j N := poly_conj_add M N

private lemma l3i_fr_sub (j : Fin 3) (M N : Mat2) :
    edgeFrame j (M - N) = edgeFrame j M - edgeFrame j N := poly_conj_sub M N

private lemma l3i_fr_neg (j : Fin 3) (M : Mat2) : edgeFrame j (-M) = -edgeFrame j M :=
  poly_conj_neg M

private lemma l3i_fr_smul (j : Fin 3) (r : ℝ) (M : Mat2) :
    edgeFrame j (r • M) = r • edgeFrame j M := poly_conj_smul r M

private lemma l3i_fr_bracket (j : Fin 3) (M N : Mat2) :
    edgeFrame j (M * N - N * M) = edgeFrame j M * edgeFrame j N - edgeFrame j N * edgeFrame j M :=
  poly_conj_bracket (l3i_conj j) M N

private lemma l3i_fr_traceForm (j : Fin 3) (M N : Mat2) :
    traceForm (edgeFrame j M) (edgeFrame j N) = traceForm M N :=
  poly_traceForm_conj (l3i_conj j) M N

private lemma l3i_fr_trace (j : Fin 3) (M : Mat2) : (edgeFrame j M).trace = M.trace :=
  poly_trace_conj (l3i_conj j) M

private lemma l3i_fr_J (j : Fin 3) : edgeFrame j J = J := by
  have hc : Commute J (R ^ (j : ℕ)) := Commute.pow_right poly_J_mul_R _
  rw [edgeFrame, ← hc.eq, Matrix.mul_assoc, poly_Rpow_mul_Rinvpow, Matrix.mul_one]

/-- The Reinhardt Hamiltonian is invariant under the rotation `edgeFrame j`, which takes
`edgeControlIn j v` to `edgeControl v`. -/
private lemma l3i_hamiltonian_edgeFrame (j : Fin 3) (lam : ℝ) (A B X : Mat2) (v : ℝ) :
    hamiltonian lam (edgeFrame j A) (edgeFrame j B) (edgeFrame j X) (edgeControl v) =
      hamiltonian lam A B X (edgeControlIn j v) := by
  have hAJ : edgeFrame j A - (3 / 2 * lam) • J = edgeFrame j (A - (3 / 2 * lam) • J) := by
    rw [l3i_fr_sub, l3i_fr_smul, l3i_fr_J]
  rw [hamiltonian, hamiltonian, ← l3i_edgeFrame_controlMatrix_edgeControlIn j v, hAJ,
    l3i_fr_traceForm, l3i_fr_traceForm, l3i_fr_traceForm]

/-- `H_e = H_R` at one time: the edge Hamiltonian of the pulled-back costate at an edge control is
the Reinhardt Hamiltonian at the corresponding control of `U_T`, where `X̃ = Φ(x, y)`, `y > 0`,
`|x| < 1/√3`, and `Λ_R` is traceless and orthogonal to `X`. -/
private lemma l3i_controlHamiltonian_edgePullback {j : Fin 3} {lam : ℝ} {Λ₁ ΛR X : Mat2}
    {q : Fin 3 → ℝ} (hX : edgeFrame j X = Φ (q 0) (q 1)) (hq : q ∈ edgeDomain)
    (hR : ΛR.trace = 0) (hRX : traceForm ΛR X = 0) {v : ℝ} (hv : v ∈ edgeControlSet) :
    Pontryagin.controlHamiltonian edgeField edgeCost (3 / 2 * lam) q
        (edgePullback j lam Λ₁ ΛR X q) v =
      hamiltonian lam Λ₁ ΛR X (edgeControlIn j v) := by
  obtain ⟨hy, hx1, hx2⟩ := hq
  have hD : -1 + 2 * q 0 * (√3 * v) ≠ 0 := by
    have := edgeF₂_denom_neg hx1 hx2 hv
    intro h; apply this.ne; linear_combination h
  obtain ⟨e0, e1, e2⟩ := l3i_edgePullback_apply (lam := lam) (Λ₁ := Λ₁) (ΛR := ΛR) hX hy.ne'
  have hBt : (edgeFrame j ΛR).trace = 0 := by rw [l3i_fr_trace, hR]
  have hBX : traceForm (edgeFrame j ΛR) (Φ (q 0) (q 1)) = 0 := by
    rw [← hX, l3i_fr_traceForm, hRX]
  have hcore := l3i_core_H lam (q 0) (q 1) (√3 * v) _ _ _ _ _ _ hy.ne' hD
    (Matrix.eta_fin_two (edgeFrame j Λ₁)) (l3i_eq_of_perp hy.ne' hBt hBX)
  have hf : edgeF₂ (q 0) (q 1) v = 2 * q 1 ^ 2 * (√3 * v) / (-1 + 2 * q 0 * (√3 * v)) := by
    unfold edgeF₂; ring
  rw [eqn_edge_ham, edgeHamiltonian, e0, e1, e2, ← l3i_hamiltonian_edgeFrame, hX, hamiltonian,
    l3i_controlMatrix_edgeControl, ← hcore, hf]

/-- The right-hand side of (8.1.7) for `λ₁`, with `w = √3 u_e`. -/
private lemma l3i_RHS₁_eq (ν l₂ x y v : ℝ) :
    edgeCostateRHS₁ ν l₂ x y v =
      l₂ * (4 * y ^ 2 * (√3 * v) ^ 2 / (-1 + 2 * x * (√3 * v)) ^ 2) - 2 * ν * x / y := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [edgeCostateRHS₁, mul_pow, h3]
  ring

/-- The right-hand side of (8.1.7) for `λ₂`, with `w = √3 u_e`. -/
private lemma l3i_RHS₂_eq (ν l₁ l₂ l₃ x y v : ℝ) :
    edgeCostateRHS₂ ν l₁ l₂ l₃ x y v =
      l₃ / y ^ 2 - l₁ - l₂ * (4 * y * (√3 * v) / (-1 + 2 * x * (√3 * v))) + ν * x ^ 2 / y ^ 2 := by
  rw [edgeCostateRHS₂]
  ring

/-- **The costate equation for `λ_x`, the core identity** (`w = √3 u_e`): the derivative of
`λ_x` along the Reinhardt state–costate equations is the right-hand side of (8.1.7). -/
private lemma l3i_core_D1 (lam x y w a1 b1 c1 d1 a2 c2 : ℝ) (hy : y ≠ 0)
    (hD : -1 + 2 * x * w ≠ 0) {X A B Z P X' A' B' : Mat2} (hX : X = Φ x y)
    (hA : A = !![a1, b1; c1, d1])
    (hB : B = !![a2, c2 * (x ^ 2 + y ^ 2) - 2 * a2 * x; c2, -a2])
    (hZ : Z = !![2 * w / 3, -2 / 3; 0, -(2 * w / 3)]) (hP : P = (traceForm Z X)⁻¹ • Z)
    (hX' : X' = P * X - X * P) (hA' : A' = A * X - X * A)
    (hB' : B' = (P * B - B * P) - traceForm B P • (P * X - X * P) +
      ((-A + (3 / 2 * lam) • J) * X - X * (-A + (3 / 2 * lam) • J))) :
    (A' * !![0, -1; 0, 0]).trace +
        ((1 / 4 : ℝ) • ((X' * B + X * B') - (B' * X + B * X')) * (l3i_E * X - X * l3i_E) +
          (1 / 4 : ℝ) • (X * B - B * X) * (l3i_E * X' - X' * l3i_E)).trace =
      l3i_gy B X * (4 * y ^ 2 * w ^ 2 / (-1 + 2 * x * w) ^ 2) - 2 * (3 / 2 * lam) * x / y := by
  subst hX hA hB hZ hP hX' hA' hB'
  have hDa : -1 + x * 2 * w ≠ 0 := by rwa [mul_comm x 2]
  have hZX : traceForm !![2 * w / 3, -2 / 3; 0, -(2 * w / 3)] (Φ x y) =
      2 * (-1 + 2 * x * w) / (3 * y) := by
    simp [traceForm, Φ, Matrix.trace_fin_two]
    field_simp
    ring
  rw [hZX]
  simp [l3i_gy, l3i_E, traceForm, Φ, J, Matrix.trace_fin_two]
  field_simp
  ring

/-- **The costate equation for `λ_y`, the core identity** (`w = √3 u_e`). -/
private lemma l3i_core_D2 (lam x y w a1 b1 c1 d1 a2 c2 : ℝ) (hy : y ≠ 0)
    (hD : -1 + 2 * x * w ≠ 0) {X A B Z P X' B' : Mat2} (hX : X = Φ x y)
    (hA : A = !![a1, b1; c1, d1])
    (hB : B = !![a2, c2 * (x ^ 2 + y ^ 2) - 2 * a2 * x; c2, -a2])
    (hZ : Z = !![2 * w / 3, -2 / 3; 0, -(2 * w / 3)]) (hP : P = (traceForm Z X)⁻¹ • Z)
    (hX' : X' = P * X - X * P)
    (hB' : B' = (P * B - B * P) - traceForm B P • (P * X - X * P) +
      ((-A + (3 / 2 * lam) • J) * X - X * (-A + (3 / 2 * lam) • J))) :
    ((1 / 4 : ℝ) • ((X' * B + X * B') - (B' * X + B * X')) *
          ((1 / 2 : ℝ) • ((l3i_E * X - X * l3i_E) * X - X * (l3i_E * X - X * l3i_E))) +
        (1 / 4 : ℝ) • (X * B - B * X) *
          ((1 / 2 : ℝ) • (((l3i_E * X' - X' * l3i_E) * X + (l3i_E * X - X * l3i_E) * X') -
            (X' * (l3i_E * X - X * l3i_E) + X * (l3i_E * X' - X' * l3i_E))))).trace =
      l3i_gs lam A x / y ^ 2 - l3i_gx lam A B X -
        l3i_gy B X * (4 * y * w / (-1 + 2 * x * w)) + 3 / 2 * lam * x ^ 2 / y ^ 2 := by
  subst hX hA hB hZ hP hX' hB'
  have hDa : -1 + x * 2 * w ≠ 0 := by rwa [mul_comm x 2]
  have hZX : traceForm !![2 * w / 3, -2 / 3; 0, -(2 * w / 3)] (Φ x y) =
      2 * (-1 + 2 * x * w) / (3 * y) := by
    simp [traceForm, Φ, Matrix.trace_fin_two]
    field_simp
    ring
  rw [hZX]
  simp [l3i_gx, l3i_gy, l3i_gs, l3i_E, traceForm, Φ, J, Matrix.trace_fin_two]
  field_simp
  ring

/-- **The costate equation for `λ_s`, the core identity**: `λ_s` is constant. -/
private lemma l3i_core_D3 (x y a1 b1 c1 d1 : ℝ) (hy : y ≠ 0) {X A A' : Mat2} (hX : X = Φ x y)
    (hA : A = !![a1, b1; c1, d1]) (hA' : A' = A * X - X * A) :
    y * (A 0 0 - A 1 1) + x * (A' 0 0 - A' 1 1) + A' 0 1 -
      (2 * x * y * A 1 0 + x ^ 2 * A' 1 0) = 0 := by
  subst hX hA hA'
  simp [Φ]
  field_simp
  ring

/-! ### Calculus along the trajectory -/

/-- Entrywise absolute continuity of a matrix curve on `[0, T]`. -/
private def l3i_AC (F : ℝ → Mat2) (T : ℝ) : Prop :=
  ∀ i k, AbsolutelyContinuousOnInterval (fun t ↦ F t i k) 0 T

private lemma l3i_AC_mul {F G : ℝ → Mat2} {T : ℝ} (hF : l3i_AC F T) (hG : l3i_AC G T) :
    l3i_AC (fun t ↦ F t * G t) T := by
  intro i k
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  exact ((hF i 0).fun_mul (hG 0 k)).fun_add ((hF i 1).fun_mul (hG 1 k))

private lemma l3i_AC_sub {F G : ℝ → Mat2} {T : ℝ} (hF : l3i_AC F T) (hG : l3i_AC G T) :
    l3i_AC (fun t ↦ F t - G t) T := fun i k ↦ by
  simpa only [Matrix.sub_apply] using (hF i k).fun_sub (hG i k)

private lemma l3i_AC_smul {F : ℝ → Mat2} {T : ℝ} (r : ℝ) (hF : l3i_AC F T) :
    l3i_AC (fun t ↦ r • F t) T := fun i k ↦ by
  simpa only [Matrix.smul_apply, smul_eq_mul] using (hF i k).const_mul r

private lemma l3i_ac_const (a T : ℝ) : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ a) 0 T :=
  (contDiffOn_const (c := a)).absolutelyContinuousOnInterval

private lemma l3i_AC_const (M : Mat2) (T : ℝ) : l3i_AC (fun _ ↦ M) T := fun i k ↦
  l3i_ac_const (M i k) T

private lemma l3i_AC_traceForm {F G : ℝ → Mat2} {T : ℝ} (hF : l3i_AC F T) (hG : l3i_AC G T) :
    AbsolutelyContinuousOnInterval (fun t ↦ traceForm (F t) (G t)) 0 T := by
  have h := l3i_AC_mul hF hG
  simp only [traceForm, Matrix.trace_fin_two]
  exact (h 0 0).fun_add (h 1 1)

private lemma l3i_AC_of_isIntegralCurve {F V : ℝ → Mat2} {T : ℝ} (hT : 0 ≤ T)
    (hI : IsIntegralCurve F V T) : l3i_AC F T := fun i k ↦
  hI.absolutelyContinuousOnInterval hT i k

private lemma l3i_AC_edgeFrame {F : ℝ → Mat2} {T : ℝ} (j : Fin 3) (hF : l3i_AC F T) :
    l3i_AC (fun t ↦ edgeFrame j (F t)) T :=
  l3i_AC_mul (l3i_AC_mul (l3i_AC_const _ T) hF) (l3i_AC_const _ T)

private lemma l3i_hasDerivAt_gx (lam : ℝ) {A B X : ℝ → Mat2} {A' B' X' : Mat2} {τ : ℝ}
    (hA : HasDerivAtEntrywise A A' τ) (hB : HasDerivAtEntrywise B B' τ)
    (hX : HasDerivAtEntrywise X X' τ) :
    HasDerivAt (fun t ↦ l3i_gx lam (A t) (B t) (X t))
      ((A' * !![0, -1; 0, 0]).trace +
        ((1 / 4 : ℝ) • ((X' * B τ + X τ * B') - (B' * X τ + B τ * X')) *
            (l3i_E * X τ - X τ * l3i_E) +
          (1 / 4 : ℝ) • (X τ * B τ - B τ * X τ) * (l3i_E * X' - X' * l3i_E)).trace) τ := by
  have h1 := (hA.mul_const !![0, -1; 0, 0]).trace
  have hL := ((hX.mul hB).sub (hB.mul hX)).const_smul (1 / 4 : ℝ)
  have hF := (hX.const_mul l3i_E).sub (hX.mul_const l3i_E)
  have h2 := (hL.mul hF).trace
  have h := (h1.fun_add h2).add_const (3 / 2 * lam)
  unfold l3i_gx traceForm
  convert h using 1

private lemma l3i_hasDerivAt_gy {B X : ℝ → Mat2} {B' X' : Mat2} {τ : ℝ}
    (hB : HasDerivAtEntrywise B B' τ) (hX : HasDerivAtEntrywise X X' τ) :
    HasDerivAt (fun t ↦ l3i_gy (B t) (X t))
      (((1 / 4 : ℝ) • ((X' * B τ + X τ * B') - (B' * X τ + B τ * X')) *
          ((1 / 2 : ℝ) • ((l3i_E * X τ - X τ * l3i_E) * X τ -
            X τ * (l3i_E * X τ - X τ * l3i_E))) +
        (1 / 4 : ℝ) • (X τ * B τ - B τ * X τ) *
          ((1 / 2 : ℝ) • (((l3i_E * X' - X' * l3i_E) * X τ + (l3i_E * X τ - X τ * l3i_E) * X') -
            (X' * (l3i_E * X τ - X τ * l3i_E) + X τ * (l3i_E * X' - X' * l3i_E))))).trace) τ := by
  have hL := ((hX.mul hB).sub (hB.mul hX)).const_smul (1 / 4 : ℝ)
  have hF := (hX.const_mul l3i_E).sub (hX.mul_const l3i_E)
  have hG := ((hF.mul hX).sub (hX.mul hF)).const_smul (1 / 2 : ℝ)
  simpa only [l3i_gy, traceForm] using (hL.mul hG).trace

private lemma l3i_hasDerivAt_gs (lam : ℝ) {A : ℝ → Mat2} {x : ℝ → ℝ} {A' : Mat2} {x' τ : ℝ}
    (hA : HasDerivAtEntrywise A A' τ) (hx : HasDerivAt x x' τ) :
    HasDerivAt (fun t ↦ l3i_gs lam (A t) (x t))
      (x' * (A τ 0 0 - A τ 1 1) + x τ * (A' 0 0 - A' 1 1) + A' 0 1 -
        (2 * x τ * x' * A τ 1 0 + x τ ^ 2 * A' 1 0)) τ := by
  have h := ((((hx.fun_mul ((hA 0 0).fun_sub (hA 1 1))).fun_add (hA 0 1)).fun_sub
    ((hx.fun_mul hx).fun_mul (hA 1 0))).add_const (3 / 2 * lam))
  simp only [l3i_gs, sq]
  convert h using 1
  ring

private lemma l3i_fr_controlP {j : Fin 3} {u w : Fin 3 → ℝ}
    (hZ : edgeFrame j (controlMatrix u) = controlMatrix w) (M : Mat2) :
    edgeFrame j (controlP u M) = controlP w (edgeFrame j M) :=
  poly_controlP_conj (l3i_conj j) hZ M

/-- The edge state of the shifted trajectory is the edge state from `c`. -/
private lemma l3i_edgeState_shift (j : Fin 3) (X : ℝ → Mat2) (c : ℝ) :
    edgeState j (fun t ↦ X (c + t)) 0 = edgeState j X c := by
  funext t
  ext i
  fin_cases i
  · simp [edgeState]
  · simp [edgeState]
  · simp [edgeState, intervalIntegral.integral_comp_add_left (fun τ ↦ edgeFrame j (X τ) 1 0) c]

/-- What the edge state equations (`eqn_xy_edge`) give on `[c, d]`, in the shifted time. -/
private lemma l3i_setup {c d : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (h : IsExtremalOn c d u g X Λ₁ ΛR lam) {j : Fin 3} (hu : ∀ᵐ t, t ∈ Ioo c d → u t j = 0) :
    Pontryagin.IsAdmissibleIn edgeField edgeDomain edgeControlSet (edgeState j X c 0) (d - c)
        (fun t ↦ edgeParam j (u (c + t))) (edgeState j X c) ∧
      (∀ t ∈ Icc 0 (d - c),
        edgeFrame j (X (c + t)) = Φ (edgeState j X c t 0) (edgeState j X c t 1)) ∧
      (∀ᵐ t, t ∈ Ioo 0 (d - c) → edgeFrame j (controlMatrix (u (c + t))) =
        controlMatrix (edgeControl (edgeParam j (u (c + t))))) ∧
      ∀ᵐ t, t ∈ Ioo 0 (d - c) → u (c + t) j = 0 := by
  have hst : IsStateTrajectory (d - c) (fun t ↦ u (c + t)) (fun t ↦ g (c + t))
      (fun t ↦ X (c + t)) := h.1
  have hu' : ∀ᵐ t, t ∈ Ioo 0 (d - c) → u (c + t) j = 0 := by
    filter_upwards [(measurePreserving_add_left volume c).quasiMeasurePreserving.ae hu]
      with t ht ht'
    exact ht ⟨by linarith [ht'.1], by linarith [ht'.2]⟩
  obtain ⟨h1, h2, h3⟩ := eqn_xy_edge hst le_rfl hst.1 le_rfl hu'
  rw [l3i_edgeState_shift] at h1 h2
  simp only [sub_zero, zero_add] at h1 h2 h3
  exact ⟨h1, fun t ht ↦ (h2 t ht).1, h3, hu'⟩

/-- The integrand of the adjoint equation of the edge problem, on the basis vectors: it is
`-(λ₁', λ₂', λ₃')` with the right-hand sides of (8.1.7). -/
private lemma l3i_adjoint_integrand {p : StrongDual ℝ (Fin 3 → ℝ)} {q : Fin 3 → ℝ} {ue ν : ℝ}
    (hy : q 1 ≠ 0) (hD : -1 + 2 * √3 * q 0 * ue ≠ 0) :
    p.comp (fderiv ℝ (fun x ↦ edgeField x ue) q) + ν • fderiv ℝ (fun x ↦ edgeCost x ue) q =
      edgeCovector (-edgeCostateRHS₁ ν (edgeCostate p 1) (q 0) (q 1) ue)
        (-edgeCostateRHS₂ ν (edgeCostate p 0) (edgeCostate p 1) (edgeCostate p 2) (q 0) (q 1) ue)
        0 := by
  have key : ∀ w, (p.comp (fderiv ℝ (fun x ↦ edgeField x ue) q) +
      ν • fderiv ℝ (fun x ↦ edgeCost x ue) q) w =
        fderiv ℝ (fun x ↦ edgeField x ue) q w 0 * edgeCostate p 0 +
          fderiv ℝ (fun x ↦ edgeField x ue) q w 1 * edgeCostate p 1 +
          fderiv ℝ (fun x ↦ edgeField x ue) q w 2 * edgeCostate p 2 +
          ν * fderiv ℝ (fun x ↦ edgeCost x ue) q w := by
    intro w
    simp only [add_apply, ContinuousLinearMap.comp_apply, smul_apply, smul_eq_mul]
    rw [apply_eq_sum_edgeCostate p]
  obtain ⟨e0, e1, e2⟩ := l3i_edgeCostate_edgeCovector
    (-edgeCostateRHS₁ ν (edgeCostate p 1) (q 0) (q 1) ue)
    (-edgeCostateRHS₂ ν (edgeCostate p 0) (edgeCostate p 1) (edgeCostate p 2) (q 0) (q 1) ue) 0
  apply l3i_ext
  · rw [e0]
    change (_ : StrongDual ℝ (Fin 3 → ℝ)) (Pi.single 0 1) = _
    rw [key, fderiv_edgeField_apply hy hD, fderiv_edgeCost_apply hy]
    simp only [edgeCostateRHS₁]
    simp
    ring
  · rw [e1]
    change (_ : StrongDual ℝ (Fin 3 → ℝ)) (Pi.single 1 1) = _
    rw [key, fderiv_edgeField_apply hy hD, fderiv_edgeCost_apply hy]
    simp only [edgeCostateRHS₂]
    simp
    ring
  · rw [e2]
    change (_ : StrongDual ℝ (Fin 3 → ℝ)) (Pi.single 2 1) = _
    rw [key, fderiv_edgeField_apply hy hD, fderiv_edgeCost_apply hy]
    simp

/-- **`H_e = H_R` for the pulled-back costate.** Along an extremal lifted trajectory on `[c, d]`
whose control lies in the edge `{u_j = 0}` almost everywhere, at every time `t ∈ [0, d - c]` and
for every edge control `v ∈ [-½, ½]`, the Hamiltonian of the edge problem (8.1.6) with
`ν = (3/2) λ_cost` and the pulled-back costate equals the Reinhardt Hamiltonian at the control
`edgeControlIn j v` of the edge.

Proof: `H_R` is invariant under the rotation `edgeFrame j` (`R` commutes with `J`, the trace form
is conjugation invariant, `edgeFrame j (Z_{edgeControlIn j v}) = Z_{edgeControl v}`). With
`X̃ = Φ(x, y)` (`eqn_xy_edge`), the edge velocity `(x', y', s') = (y, f₂, 1/y)` satisfies
`h⁻¹ (∂ₓh y + ∂ₛh / y) = Φ(x, y)` and `∂ₓΦ y + ∂_yΦ f₂ = [P̃, Φ]` with
`P̃ = Z_{edgeControl v}/⟨Z_{edgeControl v}, Φ⟩` (Lemma 4.5.2 on the edge); so
`⟨p, f_e⟩ = ⟨Λ̃₁, X̃⟩ + ⟨Λ̃₂, [P̃, X̃]⟩ + (3/2) λ_cost (y + 1/y)`, and
`⟨Λ̃₂, [P̃, X̃]⟩ = -⟨[Λ̃₂, X̃], P̃⟩ = -⟨Λ̃_R, P̃⟩` (`[Λ̃₂, X̃] = Λ̃_R` from `X̃² = -I` and
`⟨Λ̃_R, X̃⟩ = 0`), while `(3/2) λ_cost (y + 1/y + x²/y) = -(3/2) λ_cost ⟨J, Φ(x, y)⟩` (4.3.1).
Matrix algebra (`ext`, `field_simp`, `ring`). -/
theorem IsExtremalOn.controlHamiltonian_edgePullback {c d : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ} (h : IsExtremalOn c d u g X Λ₁ ΛR lam) {j : Fin 3}
    (hu : ∀ᵐ t, t ∈ Ioo c d → u t j = 0) :
    ∀ t ∈ Icc 0 (d - c), ∀ v ∈ edgeControlSet,
      Pontryagin.controlHamiltonian edgeField edgeCost (3 / 2 * lam) (edgeState j X c t)
          (edgePullback j lam (Λ₁ (c + t)) (ΛR (c + t)) (X (c + t)) (edgeState j X c t)) v =
        hamiltonian lam (Λ₁ (c + t)) (ΛR (c + t)) (X (c + t)) (edgeControlIn j v) := by
  intro t ht v hv
  obtain ⟨hadm, hΦ, -, -⟩ := l3i_setup h hu
  obtain ⟨-, hR, hRX, -⟩ := h.2.2.1 t ht
  exact l3i_controlHamiltonian_edgePullback (hΦ t ht) (hadm.2 t ht) hR hRX hv

/-- **The pulled-back costate solves the adjoint equation of the edge problem** (with
`ν = (3/2) λ_cost`, `Pontryagin.IsAdjoint`, the costate equations (8.1.7)), along an extremal
lifted trajectory on `[c, d]` whose control lies in the edge `{u_j = 0}` almost everywhere.

Proof: on `[0, d - c]`, with `X̃ = Φ(x, y)`, the components are `λ_x = ⟨Λ̃₁, [[0, -1], [0, 0]]⟩ +
⟨Λ̃₂, [E, X̃]⟩ + (3/2) λ_cost`, `λ_y = ⟨Λ̃₂, ½[[E, X̃], X̃]⟩` (`∂ₓΦ = [E, X̃]`,
`∂_yΦ = ½[[E, X̃], X̃]`, `E = [[0, 1], [0, 0]]`, `h⁻¹∂ₓh = [[0, -1], [0, 0]]`) and
`λ_s = x(Λ̃₁₀₀ - Λ̃₁₁₁) + Λ̃₁₀₁ - x²Λ̃₁₁₀ + (3/2) λ_cost` (`h⁻¹∂ₛh = [[x, -x²], [1, -x]]`),
polynomials in the entries of the rotated curves `Λ̃₁, Λ̃_R, X̃` and in `x`, which are absolutely
continuous (integral curves); so the components are absolutely continuous. At almost every time
the rotated curves have the derivatives given by the costate equations `Λ₁' = [Λ₁, X]`,
`Λ_R' = [P, Λ_R] - ⟨Λ_R, P⟩[P, X] + [-Λ₁ + (3/2) λ_cost J, X]` and the state equation `X' = [P, X]`
(rotated by `edgeFrame j`, with `P̃ = Z_{edgeControl u_e}/⟨Z, X̃⟩`, `eqn_xy_edge`), and `x' = y`;
the derivatives of `λ_x, λ_y, λ_s` are then the right-hand sides of (8.1.7) (identities of
rational functions in `x, y, √3 u_e` and the entries of `Λ̃₁, Λ̃_R`, with `Λ̃_R` traceless and
orthogonal to `Φ(x, y)`; `field_simp; ring`, checked first with sympy). The fundamental theorem of
calculus for absolutely continuous functions gives (8.1.7) in integral form, and the integrand of
`Pontryagin.IsAdjoint` is `-(λ₁', λ₂', λ₃')` on the basis vectors (the partial derivatives of
`edgeField` and `edgeCost`, as in the proof of `eqn_costate_edge`). -/
theorem IsExtremalOn.isAdjoint_edgePullback {c d : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ} (h : IsExtremalOn c d u g X Λ₁ ΛR lam) {j : Fin 3}
    (hu : ∀ᵐ t, t ∈ Ioo c d → u t j = 0) :
    Pontryagin.IsAdjoint edgeField edgeCost (3 / 2 * lam) (fun t ↦ edgeParam j (u (c + t)))
      (edgeState j X c) (d - c)
      (fun t ↦ edgePullback j lam (Λ₁ (c + t)) (ΛR (c + t)) (X (c + t)) (edgeState j X c t)) := by
  obtain ⟨hadm, hΦ, hZ, -⟩ := l3i_setup h hu
  have hst := h.1
  have hD : 0 < d - c := hst.1
  have hpt := h.2.2.1
  have hI1 := h.2.2.2.1
  have hIR := h.2.2.2.2.1
  have hXI := hst.2.2.2.2.2
  have hq := hadm.2
  have hy : ∀ t ∈ Icc 0 (d - c), edgeState j X c t 1 ≠ 0 := fun t ht ↦ (hq t ht).1.ne'
  -- the components of the pulled-back costate in terms of the rotated curves
  have hcomp := fun t (ht : t ∈ Icc 0 (d - c)) ↦
    l3i_edgePullback_apply (lam := lam) (Λ₁ := Λ₁ (c + t)) (ΛR := ΛR (c + t)) (hΦ t ht) (hy t ht)
  -- absolute continuity of the rotated curves and of `x`
  have hA : l3i_AC (fun t ↦ edgeFrame j (Λ₁ (c + t))) (d - c) :=
    l3i_AC_edgeFrame j (l3i_AC_of_isIntegralCurve hD.le hI1)
  have hB : l3i_AC (fun t ↦ edgeFrame j (ΛR (c + t))) (d - c) :=
    l3i_AC_edgeFrame j (l3i_AC_of_isIntegralCurve hD.le hIR)
  have hX : l3i_AC (fun t ↦ edgeFrame j (X (c + t))) (d - c) :=
    l3i_AC_edgeFrame j (l3i_AC_of_isIntegralCurve hD.le hXI)
  have hxeq : ∀ t ∈ Icc 0 (d - c),
      edgeState j X c t 0 = edgeState j X c 0 0 + ∫ s in (0 : ℝ)..t, edgeState j X c s 1 := by
    intro t ht
    have h1 := congrFun (hadm.1.2.2.2.2 t ht) 0
    have hsub : IntervalIntegrable
        (fun s ↦ edgeField (edgeState j X c s) (edgeParam j (u (c + s)))) volume 0 t :=
      hadm.1.2.2.2.1.mono_set
        (by rw [uIcc_of_le ht.1, uIcc_of_le hD.le]; exact Icc_subset_Icc le_rfl ht.2)
    rw [Pi.add_apply, intervalIntegral.eval_integral hsub] at h1
    simpa [edgeField] using h1
  have hyint : IntervalIntegrable (fun s ↦ edgeState j X c s 1) volume 0 (d - c) :=
    ((continuous_apply 1).comp_continuousOn hadm.1.2.2.1).intervalIntegrable_of_Icc hD.le
  have hx : AbsolutelyContinuousOnInterval (fun t ↦ edgeState j X c t 0) 0 (d - c) :=
    absolutelyContinuousOnInterval_of_eq_add_integral hD.le hyint hxeq
  have hEq : ∀ {f g : ℝ → ℝ}, (∀ t ∈ Icc 0 (d - c), f t = g t) →
      AbsolutelyContinuousOnInterval g 0 (d - c) → AbsolutelyContinuousOnInterval f 0 (d - c) :=
    fun hfg hg ↦ hg.congr fun t ht ↦ by rw [uIcc_of_le hD.le] at ht; exact (hfg t ht).symm
  have hac0 : AbsolutelyContinuousOnInterval (fun t ↦ edgeCostate
      (edgePullback j lam (Λ₁ (c + t)) (ΛR (c + t)) (X (c + t)) (edgeState j X c t)) 0)
      0 (d - c) := by
    refine hEq (fun t ht ↦ (hcomp t ht).1) ?_
    unfold l3i_gx
    exact ((l3i_AC_traceForm hA (l3i_AC_const _ _)).fun_add (l3i_AC_traceForm
      (l3i_AC_smul _ (l3i_AC_sub (l3i_AC_mul hX hB) (l3i_AC_mul hB hX)))
      (l3i_AC_sub (l3i_AC_mul (l3i_AC_const _ _) hX) (l3i_AC_mul hX (l3i_AC_const _ _))))).fun_add
      (l3i_ac_const _ _)
  have hac1 : AbsolutelyContinuousOnInterval (fun t ↦ edgeCostate
      (edgePullback j lam (Λ₁ (c + t)) (ΛR (c + t)) (X (c + t)) (edgeState j X c t)) 1)
      0 (d - c) := by
    refine hEq (fun t ht ↦ (hcomp t ht).2.1) ?_
    have hF := l3i_AC_sub (l3i_AC_mul (l3i_AC_const l3i_E _) hX)
      (l3i_AC_mul hX (l3i_AC_const l3i_E _))
    unfold l3i_gy
    exact l3i_AC_traceForm (l3i_AC_smul _ (l3i_AC_sub (l3i_AC_mul hX hB) (l3i_AC_mul hB hX)))
      (l3i_AC_smul _ (l3i_AC_sub (l3i_AC_mul hF hX) (l3i_AC_mul hX hF)))
  have hac2 : AbsolutelyContinuousOnInterval (fun t ↦ edgeCostate
      (edgePullback j lam (Λ₁ (c + t)) (ΛR (c + t)) (X (c + t)) (edgeState j X c t)) 2)
      0 (d - c) := by
    refine hEq (fun t ht ↦ (hcomp t ht).2.2) ?_
    simp only [l3i_gs, sq]
    exact (((hx.fun_mul ((hA 0 0).fun_sub (hA 1 1))).fun_add (hA 0 1)).fun_sub
      ((hx.fun_mul hx).fun_mul (hA 1 0))).fun_add (l3i_ac_const _ _)
  -- the derivatives of the rotated curves, almost everywhere
  have hdA : ∀ᵐ τ, τ ∈ Ioo 0 (d - c) → HasDerivAtEntrywise (fun t ↦ edgeFrame j (Λ₁ (c + t)))
      (edgeFrame j (Λ₁ (c + τ)) * edgeFrame j (X (c + τ)) -
        edgeFrame j (X (c + τ)) * edgeFrame j (Λ₁ (c + τ))) τ := by
    filter_upwards [hI1.ae_hasDerivAtEntrywise] with τ hτ hτI
    exact (((hτ hτI).const_mul (R ^ (j : ℕ))).mul_const (R⁻¹ ^ (j : ℕ))).congr_deriv
      (l3i_fr_bracket j _ _)
  have hdX : ∀ᵐ τ, τ ∈ Ioo 0 (d - c) → HasDerivAtEntrywise (fun t ↦ edgeFrame j (X (c + t)))
      (controlP (edgeControl (edgeParam j (u (c + τ)))) (edgeFrame j (X (c + τ))) *
          edgeFrame j (X (c + τ)) -
        edgeFrame j (X (c + τ)) *
          controlP (edgeControl (edgeParam j (u (c + τ)))) (edgeFrame j (X (c + τ)))) τ := by
    filter_upwards [hXI.ae_hasDerivAtEntrywise, hZ] with τ hτ hZτ hτI
    refine (((hτ hτI).const_mul (R ^ (j : ℕ))).mul_const (R⁻¹ ^ (j : ℕ))).congr_deriv ?_
    change edgeFrame j _ = _
    rw [l3i_fr_bracket, l3i_fr_controlP (hZτ hτI)]
  have hdB : ∀ᵐ τ, τ ∈ Ioo 0 (d - c) → HasDerivAtEntrywise (fun t ↦ edgeFrame j (ΛR (c + t)))
      ((controlP (edgeControl (edgeParam j (u (c + τ)))) (edgeFrame j (X (c + τ))) *
            edgeFrame j (ΛR (c + τ)) -
          edgeFrame j (ΛR (c + τ)) *
            controlP (edgeControl (edgeParam j (u (c + τ)))) (edgeFrame j (X (c + τ)))) -
        traceForm (edgeFrame j (ΛR (c + τ)))
            (controlP (edgeControl (edgeParam j (u (c + τ)))) (edgeFrame j (X (c + τ)))) •
          (controlP (edgeControl (edgeParam j (u (c + τ)))) (edgeFrame j (X (c + τ))) *
              edgeFrame j (X (c + τ)) -
            edgeFrame j (X (c + τ)) *
              controlP (edgeControl (edgeParam j (u (c + τ)))) (edgeFrame j (X (c + τ)))) +
        ((-edgeFrame j (Λ₁ (c + τ)) + (3 / 2 * lam) • J) * edgeFrame j (X (c + τ)) -
          edgeFrame j (X (c + τ)) * (-edgeFrame j (Λ₁ (c + τ)) + (3 / 2 * lam) • J))) τ := by
    filter_upwards [hIR.ae_hasDerivAtEntrywise, hZ] with τ hτ hZτ hτI
    refine (((hτ hτI).const_mul (R ^ (j : ℕ))).mul_const (R⁻¹ ^ (j : ℕ))).congr_deriv ?_
    change edgeFrame j _ = _
    rw [l3i_fr_add, l3i_fr_sub, l3i_fr_bracket, l3i_fr_smul, l3i_fr_bracket, l3i_fr_bracket,
      ← l3i_fr_traceForm j, l3i_fr_controlP (hZτ hτI), l3i_fr_add, l3i_fr_neg, l3i_fr_smul,
      l3i_fr_J]
  -- facts at one time
  have hfacts : ∀ τ ∈ Icc 0 (d - c),
      -1 + 2 * edgeState j X c τ 0 * (√3 * edgeParam j (u (c + τ))) ≠ 0 ∧
      (edgeFrame j (ΛR (c + τ)) = !![edgeFrame j (ΛR (c + τ)) 0 0,
        edgeFrame j (ΛR (c + τ)) 1 0 * (edgeState j X c τ 0 ^ 2 + edgeState j X c τ 1 ^ 2) -
          2 * edgeFrame j (ΛR (c + τ)) 0 0 * edgeState j X c τ 0;
        edgeFrame j (ΛR (c + τ)) 1 0, -edgeFrame j (ΛR (c + τ)) 0 0]) := by
    intro τ hτ
    obtain ⟨hyτ, hx1, hx2⟩ := hq τ hτ
    have hue : edgeParam j (u (c + τ)) ∈ edgeControlSet := hadm.1.2.1 τ hτ
    obtain ⟨-, hR, hRX, -⟩ := hpt τ hτ
    have hBt : (edgeFrame j (ΛR (c + τ))).trace = 0 := by rw [l3i_fr_trace, hR]
    have hBX : traceForm (edgeFrame j (ΛR (c + τ))) (Φ (edgeState j X c τ 0)
        (edgeState j X c τ 1)) = 0 := by rw [← hΦ τ hτ, l3i_fr_traceForm, hRX]
    refine ⟨fun h0 ↦ (edgeF₂_denom_neg hx1 hx2 hue).ne ?_, l3i_eq_of_perp hyτ.ne' hBt hBX⟩
    linear_combination h0
  -- the costate equations (8.1.7) almost everywhere
  have hd0 : ∀ᵐ τ, τ ∈ Ioo 0 (d - c) → HasDerivAt (fun t ↦ edgeCostate
      (edgePullback j lam (Λ₁ (c + t)) (ΛR (c + t)) (X (c + t)) (edgeState j X c t)) 0)
      (edgeCostateRHS₁ (3 / 2 * lam) (edgeCostate (edgePullback j lam (Λ₁ (c + τ)) (ΛR (c + τ))
        (X (c + τ)) (edgeState j X c τ)) 1) (edgeState j X c τ 0) (edgeState j X c τ 1)
        (edgeParam j (u (c + τ)))) τ := by
    filter_upwards [hdA, hdB, hdX] with τ hAτ hBτ hXτ hτI
    have hτ := Ioo_subset_Icc_self hτI
    have hg := l3i_hasDerivAt_gx lam (hAτ hτI) (hBτ hτI) (hXτ hτI)
    have hev : (fun t ↦ edgeCostate (edgePullback j lam (Λ₁ (c + t)) (ΛR (c + t)) (X (c + t))
        (edgeState j X c t)) 0) =ᶠ[𝓝 τ] fun t ↦ l3i_gx lam (edgeFrame j (Λ₁ (c + t)))
          (edgeFrame j (ΛR (c + t))) (edgeFrame j (X (c + t))) :=
      eventually_of_mem (Icc_mem_nhds hτI.1 hτI.2) fun t ht ↦ (hcomp t ht).1
    refine (hg.congr_of_eventuallyEq hev).congr_deriv ?_
    rw [l3i_RHS₁_eq, (hcomp τ hτ).2.1]
    obtain ⟨hDτ, hBτ'⟩ := hfacts τ hτ
    exact l3i_core_D1 lam _ _ _ _ _ _ _ _ _ (hy τ hτ) hDτ (hΦ τ hτ) (Matrix.eta_fin_two _) hBτ'
      (l3i_controlMatrix_edgeControl _) rfl rfl rfl rfl
  have hd1 : ∀ᵐ τ, τ ∈ Ioo 0 (d - c) → HasDerivAt (fun t ↦ edgeCostate
      (edgePullback j lam (Λ₁ (c + t)) (ΛR (c + t)) (X (c + t)) (edgeState j X c t)) 1)
      (edgeCostateRHS₂ (3 / 2 * lam)
        (edgeCostate (edgePullback j lam (Λ₁ (c + τ)) (ΛR (c + τ)) (X (c + τ))
          (edgeState j X c τ)) 0)
        (edgeCostate (edgePullback j lam (Λ₁ (c + τ)) (ΛR (c + τ)) (X (c + τ))
          (edgeState j X c τ)) 1)
        (edgeCostate (edgePullback j lam (Λ₁ (c + τ)) (ΛR (c + τ)) (X (c + τ))
          (edgeState j X c τ)) 2)
        (edgeState j X c τ 0) (edgeState j X c τ 1) (edgeParam j (u (c + τ)))) τ := by
    filter_upwards [hdA, hdB, hdX] with τ hAτ hBτ hXτ hτI
    have hτ := Ioo_subset_Icc_self hτI
    have hg := l3i_hasDerivAt_gy (hBτ hτI) (hXτ hτI)
    have hev : (fun t ↦ edgeCostate (edgePullback j lam (Λ₁ (c + t)) (ΛR (c + t)) (X (c + t))
        (edgeState j X c t)) 1) =ᶠ[𝓝 τ] fun t ↦ l3i_gy (edgeFrame j (ΛR (c + t)))
          (edgeFrame j (X (c + t))) :=
      eventually_of_mem (Icc_mem_nhds hτI.1 hτI.2) fun t ht ↦ (hcomp t ht).2.1
    refine (hg.congr_of_eventuallyEq hev).congr_deriv ?_
    rw [l3i_RHS₂_eq, (hcomp τ hτ).1, (hcomp τ hτ).2.1, (hcomp τ hτ).2.2]
    obtain ⟨hDτ, hBτ'⟩ := hfacts τ hτ
    exact l3i_core_D2 lam _ _ _ _ _ _ _ _ _ (hy τ hτ) hDτ (hΦ τ hτ) (Matrix.eta_fin_two _) hBτ'
      (l3i_controlMatrix_edgeControl _) rfl rfl rfl
  have hd2 : ∀ᵐ τ, τ ∈ Ioo 0 (d - c) → HasDerivAt (fun t ↦ edgeCostate
      (edgePullback j lam (Λ₁ (c + t)) (ΛR (c + t)) (X (c + t)) (edgeState j X c t)) 2) 0 τ := by
    filter_upwards [hdA, ae_hasDerivAt_of_eq_add_integral hyint ⟨le_rfl, hD.le⟩ hxeq]
      with τ hAτ hxτ hτI
    have hτ := Ioo_subset_Icc_self hτI
    have hg := l3i_hasDerivAt_gs lam (hAτ hτI) (hxτ hτI)
    have hev : (fun t ↦ edgeCostate (edgePullback j lam (Λ₁ (c + t)) (ΛR (c + t)) (X (c + t))
        (edgeState j X c t)) 2) =ᶠ[𝓝 τ] fun t ↦ l3i_gs lam (edgeFrame j (Λ₁ (c + t)))
          (edgeState j X c t 0) :=
      eventually_of_mem (Icc_mem_nhds hτI.1 hτI.2) fun t ht ↦ (hcomp t ht).2.2
    refine (hg.congr_of_eventuallyEq hev).congr_deriv ?_
    exact l3i_core_D3 _ _ _ _ _ _ (hy τ hτ) (hΦ τ hτ) (Matrix.eta_fin_two _) rfl
  -- the costate equations in integral form
  obtain ⟨hi0, hf0⟩ := hac0.eq_add_integral_of_ae_hasDerivAt hD.le hd0
  obtain ⟨hi1, hf1⟩ := hac1.eq_add_integral_of_ae_hasDerivAt hD.le hd1
  obtain ⟨-, hf2⟩ := hac2.eq_add_integral_of_ae_hasDerivAt hD.le hd2
  -- the integrand of the adjoint equation
  set G : ℝ → StrongDual ℝ (Fin 3 → ℝ) := fun r ↦ edgeCovector
    (-edgeCostateRHS₁ (3 / 2 * lam) (edgeCostate (edgePullback j lam (Λ₁ (c + r)) (ΛR (c + r))
      (X (c + r)) (edgeState j X c r)) 1) (edgeState j X c r 0) (edgeState j X c r 1)
      (edgeParam j (u (c + r))))
    (-edgeCostateRHS₂ (3 / 2 * lam)
        (edgeCostate (edgePullback j lam (Λ₁ (c + r)) (ΛR (c + r)) (X (c + r))
          (edgeState j X c r)) 0)
        (edgeCostate (edgePullback j lam (Λ₁ (c + r)) (ΛR (c + r)) (X (c + r))
          (edgeState j X c r)) 1)
        (edgeCostate (edgePullback j lam (Λ₁ (c + r)) (ΛR (c + r)) (X (c + r))
          (edgeState j X c r)) 2)
        (edgeState j X c r 0) (edgeState j X c r 1) (edgeParam j (u (c + r)))) 0 with hG
  have hFG : ∀ r ∈ Icc 0 (d - c),
      (edgePullback j lam (Λ₁ (c + r)) (ΛR (c + r)) (X (c + r)) (edgeState j X c r)).comp
          (Pontryagin.linearization edgeField (fun t ↦ edgeParam j (u (c + t)))
            (edgeState j X c) r) +
        (3 / 2 * lam) • fderiv ℝ (fun x ↦ edgeCost x (edgeParam j (u (c + r))))
          (edgeState j X c r) = G r := by
    intro r hr
    obtain ⟨hyr, hx1, hx2⟩ := hq r hr
    exact l3i_adjoint_integrand hyr.ne' (edgeF₂_denom_neg hx1 hx2 (hadm.1.2.1 r hr)).ne
  have hGi : IntervalIntegrable G volume 0 (d - c) := by
    simp only [hG, edgeCovector, zero_smul, add_zero]
    exact (IntervalIntegrable.smul_continuousOn hi0.neg continuousOn_const).add
      (IntervalIntegrable.smul_continuousOn hi1.neg continuousOn_const)
  have hsub : ∀ τ ∈ Icc 0 (d - c), uIcc τ (d - c) ⊆ Icc 0 (d - c) := fun τ hτ ↦ by
    rw [uIcc_of_le hτ.2]; exact Icc_subset_Icc hτ.1 le_rfl
  refine ⟨(intervalIntegrable_congr fun r hr ↦ (hFG r (Ioc_subset_Icc_self (by
    rwa [uIoc_of_le hD.le] at hr))).symm).1 hGi, fun τ hτ ↦ ?_⟩
  have hGτ : IntervalIntegrable G volume τ (d - c) :=
    hGi.mono_set (by rw [uIcc_of_le hτ.2, uIcc_of_le hD.le]; exact Icc_subset_Icc hτ.1 le_rfl)
  rw [intervalIntegral.integral_congr fun r hr ↦ hFG r (hsub τ hτ hr)]
  have hcomp' : ∀ i, edgeCostate (∫ r in τ..d - c, G r) i = ∫ r in τ..d - c, edgeCostate (G r) i :=
    fun i ↦ ContinuousLinearMap.intervalIntegral_apply hGτ _
  have hτD : ∀ (f : ℝ → ℝ), IntervalIntegrable f volume 0 (d - c) →
      ∫ r in τ..d - c, f r = (∫ r in (0 : ℝ)..d - c, f r) - ∫ r in (0 : ℝ)..τ, f r := fun f hf ↦
    (intervalIntegral.integral_interval_sub_left hf (hf.mono_set (by
      rw [uIcc_of_le hτ.1, uIcc_of_le hD.le]; exact Icc_subset_Icc le_rfl hτ.2))).symm
  have hDI : d - c ∈ Icc 0 (d - c) := ⟨hD.le, le_rfl⟩
  have hadd : ∀ (P Q : StrongDual ℝ (Fin 3 → ℝ)) (i : Fin 3),
      edgeCostate (P + Q) i = edgeCostate P i + edgeCostate Q i := fun _ _ _ ↦ rfl
  apply l3i_ext
  · rw [hadd, hcomp' 0]
    simp only [hG, l3i_edgeCostate_edgeCovector_zero, intervalIntegral.integral_neg]
    rw [hτD _ hi0]
    linarith [hf0 τ hτ, hf0 _ hDI]
  · rw [hadd, hcomp' 1]
    simp only [hG, l3i_edgeCostate_edgeCovector_one, intervalIntegral.integral_neg]
    rw [hτD _ hi1]
    linarith [hf1 τ hτ, hf1 _ hDI]
  · rw [hadd, hcomp' 2]
    simp only [hG, l3i_edgeCostate_edgeCovector_two, intervalIntegral.integral_zero]
    simp only [intervalIntegral.integral_zero] at hf2
    linarith [hf2 τ hτ, hf2 _ hDI]

/-- **The pulled-back costate satisfies the maximum condition of the edge problem**
(`Pontryagin.IsMaximal`, with `ν = (3/2) λ_cost` and controls in `[-½, ½]`), along an extremal
lifted trajectory on `[c, d]` whose control lies in the edge `{u_j = 0}` almost everywhere.

Proof: at almost every time the control is `edgeControlIn j u_e` (`u_j = 0`, `Σ u = 1`) and
maximizes the Reinhardt Hamiltonian over `U_T ⊇ controlEdge j`; by
`IsExtremalOn.controlHamiltonian_edgePullback` the edge Hamiltonian at `v ∈ [-½, ½]` is the
Reinhardt Hamiltonian at `edgeControlIn j v ∈ U_T`. -/
theorem IsExtremalOn.isMaximal_edgePullback {c d : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ} (h : IsExtremalOn c d u g X Λ₁ ΛR lam) {j : Fin 3}
    (hu : ∀ᵐ t, t ∈ Ioo c d → u t j = 0) :
    Pontryagin.IsMaximal edgeField edgeCost (3 / 2 * lam) edgeControlSet
      (fun t ↦ edgeParam j (u (c + t))) (edgeState j X c) (d - c)
      (fun t ↦ edgePullback j lam (Λ₁ (c + t)) (ΛR (c + t)) (X (c + t)) (edgeState j X c t)) := by
  obtain ⟨-, -, -, hu'⟩ := l3i_setup h hu
  have hH := h.controlHamiltonian_edgePullback hu
  have h0 : ∀ᵐ t : ℝ, t ≠ 0 := by simp [ae_iff, measure_singleton]
  have hD : ∀ᵐ t : ℝ, t ≠ d - c := by simp [ae_iff, measure_singleton]
  rw [Pontryagin.IsMaximal, ae_restrict_iff' measurableSet_Icc]
  filter_upwards [h.2.2.2.2.2, hu', h0, hD] with t hmax hj ht0 htD htI v hv
  have htI' : t ∈ Ioo 0 (d - c) := ⟨lt_of_le_of_ne htI.1 (Ne.symm ht0), lt_of_le_of_ne htI.2 htD⟩
  have hsim : u (c + t) ∈ controlSimplex := h.1.2.2.1 t htI
  have hue := edgeParam_mem_edgeControlSet (j := j) hsim
  rw [hH t htI v hv, hH t htI _ hue, edgeControlIn_edgeParam ⟨hsim, hj htI'⟩]
  exact (hmax htI').2 _ (edgeControlIn_mem_controlSimplex hv)

/-- **A normal extremal lifts its edge arcs to extremals of the edge problem.** Along an extremal
lifted trajectory on `[c, d]` with `λ_cost ≠ 0` whose control lies in the edge `{u_j = 0}` almost
everywhere, the pulled-back costate with `ν = (3/2) λ_cost` lifts the edge arc
`(edgeParam j u, edgeState j X c)` to an extremal of the `j`-th edge control problem.

Proof: `IsEdgeProblemExtremal` item by item: `0 < d - c`; admissibility (`eqn_xy_edge`, after the
time shift of `IsExtremalOn`); `ν = (3/2) λ_cost ≤ 0`; `(ν, p(t)) ≠ 0` because `ν ≠ 0`;
`IsExtremalOn.isAdjoint_edgePullback`; `IsExtremalOn.isMaximal_edgePullback`; and `H_e = 0`
almost everywhere from `H_R = 0` almost everywhere with
`IsExtremalOn.controlHamiltonian_edgePullback` at `v = u_e(t)`. -/
theorem IsExtremalOn.isEdgeProblemExtremal_edgePullback {c d : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ} (h : IsExtremalOn c d u g X Λ₁ ΛR lam) (hlam : lam ≠ 0)
    {j : Fin 3} (hu : ∀ᵐ t, t ∈ Ioo c d → u t j = 0) :
    IsEdgeProblemExtremal (d - c) (fun t ↦ edgeParam j (u (c + t))) (edgeState j X c)
      (3 / 2 * lam)
      (fun t ↦ edgePullback j lam (Λ₁ (c + t)) (ΛR (c + t)) (X (c + t)) (edgeState j X c t)) := by
  obtain ⟨hadm, -, -, hu'⟩ := l3i_setup h hu
  have hH := h.controlHamiltonian_edgePullback hu
  have h0 : ∀ᵐ t : ℝ, t ≠ 0 := by simp [ae_iff, measure_singleton]
  have hD : ∀ᵐ t : ℝ, t ≠ d - c := by simp [ae_iff, measure_singleton]
  refine ⟨h.1.1, hadm, by linarith [h.2.1], fun t _ h0' ↦ hlam ?_,
    h.isAdjoint_edgePullback hu, h.isMaximal_edgePullback hu, ?_⟩
  · have := congrArg Prod.fst h0'
    simp only [Prod.fst_zero] at this
    linarith
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [h.2.2.2.2.2, hu', h0, hD] with t hmax hj ht0 htD htI
  have htI' : t ∈ Ioo 0 (d - c) := ⟨lt_of_le_of_ne htI.1 (Ne.symm ht0), lt_of_le_of_ne htI.2 htD⟩
  have hsim : u (c + t) ∈ controlSimplex := h.1.2.2.1 t htI
  rw [hH t htI _ (edgeParam_mem_edgeControlSet hsim), edgeControlIn_edgeParam ⟨hsim, hj htI'⟩]
  exact (hmax htI').1

/-- **A normal extremal lifted trajectory is edge extremal** (Definition 8.1.2): on every
subinterval on which the control lies in an edge, the pulled-back costate is an edge costate
(`IsExtremalOn.isEdgeProblemExtremal_edgePullback` on the subinterval, `IsExtremalOn.mono`). -/
theorem IsExtremalOn.isEdgeExtremalOn_of_ne_zero {a b : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ} (h : IsExtremalOn a b u g X Λ₁ ΛR lam) (hlam : lam ≠ 0) :
    IsEdgeExtremalOn a b u X := fun _ _ _ hac hcd hdb hu ↦
  ⟨_, _, (IsExtremalOn.mono h hac hcd hdb).isEdgeProblemExtremal_edgePullback hlam hu⟩

/-- **Every normal Pontryagin extremal is edge extremal** on `[0, T]` (Definition 6.2.1(2),
Definition 8.1.2): `IsExtremalOn.isEdgeExtremalOn_of_ne_zero` on each subinterval
(`IsPontryaginExtremal.isExtremalOn`). -/
theorem IsNormalExtremal.isEdgeExtremalOn {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    {lam : ℝ} (h : IsNormalExtremal T u g X Λ₁ ΛR lam) : IsEdgeExtremalOn 0 T u X :=
  (IsPontryaginExtremal.isExtremalOn h.1 le_rfl h.1.1.1 le_rfl).isEdgeExtremalOn_of_ne_zero
    h.2

end SmoothedPolygons
