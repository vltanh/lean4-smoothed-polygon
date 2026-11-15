module

public import SmoothedPolygons.Defs

/-!
# Chapter 9, §9.0: the circular control sets and the rotation symmetry

The opening of Chapter 9 ("Circular Control Set", TeX 7676–7790) of Hales–Vajjha, *Packings of
Smoothed Polygons*. The chapter replaces the triangular control set `U_T` by a disk, a toy problem
whose Hamiltonian has a continuous rotation symmetry (§9.1 derives a conserved quantity from it,
`SmoothedPolygons/Ch9/AngularMomentum.lean`). The book says that this part "is logically
independent from the other parts, and it can be skipped" (TeX 7682–7684).

* **Definition 9.0.1** (`def:circ-control-set`, TeX 7691–7720): the disks `U_r` of the plane
  `u₀ + u₁ + u₂ = 1` centred at the centroid of `U_T` (`controlDisk`), their boundaries
  (`controlCircle`), the circumscribed disk `U_C` (`controlDiskC`, the reading below;
  `controlDiskCAsPrinted`, the printed formula) and the inscribed disk `U_I` (`controlDiskI`).
* **Theorem 9.0.3** (`thm:symmetries`, TeX 7751–7784): when the control set is closed under the
  rotations `Ad_A`, `A ∈ SO₂(ℝ)` (`IsRotationClosed`), the Hamiltonian is invariant under `SO₂(ℝ)`
  acting by `Ad_A` on `X`, `Λ₁`, `Λ_R` and the control matrix `Z_u` (`theorem9_0_3`, from the
  identity `hamiltonian_conj`). The disks `U_r` are closed under rotations
  (`isRotationClosed_controlDisk`).
* **Remark 9.0.4** (TeX 7786–7790): `U_T` is symmetric only under the rotations by multiples of
  `π/3`, which act on `U_T` as `ℤ/3ℤ` (`remark9_0_4`), and is not closed under rotations
  (`not_isRotationClosed_controlSimplex`).

Remark 9.0.2 (TeX 7721–7727: controls of `U_C ∖ U_T` give boundary curves that fail to be convex)
and the motivation (TeX 7729–7747) are not formalized.

## Readings

* **`U_C`** (TeX 7693–7699). The book defines `U_C = {0 ≤ uᵢ ≤ 1, Σuᵢ = 1, Σuᵢ² ≤ 1}`, "the
  circumscribing disk of the two-simplex". With the constraints `0 ≤ uᵢ ≤ 1` this set is `U_T`
  itself (`controlDiskCAsPrinted_eq_controlSimplex`: on `U_T`, `Σuᵢ² ≤ (Σuᵢ)² = 1`), which
  contradicts Remark 9.0.2 (`U_C ∖ U_T ≠ ∅`), Table 9.1 (`det Z_u = -⅓` on `∂U_C`) and the
  rotation symmetry the chapter is about. The circumscribed disk is `U_r` with `r² = 1`: its
  boundary circle passes through the vertices of `U_T` (`Σuᵢ² = 1` there). We read
  `U_C = U_1 = {Σuᵢ = 1, Σuᵢ² ≤ 1}` (`controlDiskC`).
* **`U_I`** (TeX 7700–7707) keeps the printed constraints `0 ≤ uᵢ ≤ 1`; they are implied by the
  others (the inscribed disk lies in `U_T`), so `U_I = U_r` with `r² = ½`
  (`controlDiskI_eq_controlDisk`).
* **`U_r`** (TeX 7708–7714) is printed for `⅓ ≤ r²`; `controlDisk r` is defined for every `r`
  (empty for `r² < ⅓`, the centroid for `r² = ⅓`).
* **Rotations** (Theorem 9.0.3: "if `A ∈ SO₂` is a rotation and `Z_u` is in the control set, then
  so is `Ad_A Z_u`"): the control set is read as the set `{Z_u | u ∈ U}` of control matrices, and
  `SO₂` as `Matrix.specialOrthogonalGroup (Fin 2) ℝ`, acting by `Ad_A M = A M A⁻¹`.
* **Theorem 9.0.3** is stated for the control-dependent Hamiltonian `H(Λ₁, Λ_R, X; Z_u)` of
  `eqn:full-hamiltonian` (`hamiltonian`), the function the proof computes with: the action
  `(Λ₁, Λ_R, X, Z_u) ↦ Ad_A(Λ₁, Λ_R, X, Z_u)` maps the controls of `U` to controls of `U` and leaves
  `H` unchanged. The proof's remarks that the transformed `Λ₁`, `Λ_R` satisfy the same equations
  are the equivariance of the dynamics, used in §9.1 (`matrixField_rotateState`,
  `SmoothedPolygons/Ch9/AngularMomentum.lean`).
-/

@[expose] public section

namespace SmoothedPolygons

open Set Matrix

/-! ### Definition 9.0.1: the circular control sets -/

/-- **The control set `U_r`** (Definition 9.0.1, third item, TeX 7708–7714):
`U_r = {(u₀, u₁, u₂) | u₀ + u₁ + u₂ = 1, u₀² + u₁² + u₂² ≤ r²}`, the disk of the plane of `U_T`
centred at the centroid `(⅓, ⅓, ⅓)` of radius `√(r² - ⅓)` (since `Σuᵢ² = ⅓ + |u - (⅓, ⅓, ⅓)|²`
on the plane). The book takes `⅓ ≤ r²`. -/
def controlDisk (r : ℝ) : Set (Fin 3 → ℝ) :=
  {u | u 0 + u 1 + u 2 = 1 ∧ u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 ≤ r ^ 2}

/-- **The boundary `∂U_r`** of `U_r` relative to its affine hull, the plane `u₀ + u₁ + u₂ = 1`
(Definition 9.0.1, TeX 7715–7717). -/
def controlCircle (r : ℝ) : Set (Fin 3 → ℝ) :=
  {u | u 0 + u 1 + u 2 = 1 ∧ u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = r ^ 2}

/-- **The circumscribed control set `U_C`** as printed (Definition 9.0.1, first item,
TeX 7693–7699): `{(u₀, u₁, u₂) | 0 ≤ uᵢ ≤ 1, Σuᵢ = 1, Σuᵢ² ≤ 1}`. This set is `U_T`
(`controlDiskCAsPrinted_eq_controlSimplex`); the formalization uses `controlDiskC`. -/
def controlDiskCAsPrinted : Set (Fin 3 → ℝ) :=
  {u | (∀ i, 0 ≤ u i ∧ u i ≤ 1) ∧ u 0 + u 1 + u 2 = 1 ∧ u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 ≤ 1}

/-- **The circumscribed (disk) control set `U_C`** (Definition 9.0.1, first item, read; see the
module docstring): the circumscribing disk of the simplex `U_T`, `U_C = U_1`, whose boundary
circle passes through the three vertices of `U_T`. -/
def controlDiskC : Set (Fin 3 → ℝ) := controlDisk 1

/-- **The inscribed control set `U_I`** (Definition 9.0.1, second item, TeX 7700–7707), as
printed: `{(u₀, u₁, u₂) | 0 ≤ uᵢ ≤ 1, Σuᵢ = 1, Σuᵢ² ≤ ½}`, the disk inscribed in `U_T`. -/
def controlDiskI : Set (Fin 3 → ℝ) :=
  {u | (∀ i, 0 ≤ u i ∧ u i ≤ 1) ∧ u 0 + u 1 + u 2 = 1 ∧ u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 ≤ 1 / 2}

/-- On the simplex, `Σuᵢ² = (Σuᵢ)² - 2(u₀u₁ + u₀u₂ + u₁u₂) = 1 - 2(u₀u₁ + u₀u₂ + u₁u₂)`. -/
private lemma sumSq_eq_of_mem_controlSimplex {u : Fin 3 → ℝ} (hu : u ∈ controlSimplex) :
    u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 1 - 2 * (u 0 * u 1 + u 0 * u 2 + u 1 * u 2) := by
  have hs : (u 0 + u 1 + u 2) ^ 2 = 1 := by rw [hu.2]; norm_num
  linear_combination hs

/-- On the simplex, `Σuᵢ² ≤ (Σuᵢ)² = 1`, since the cross terms `uᵢuⱼ` are `≥ 0`. -/
private lemma sumSq_le_one_of_mem_controlSimplex {u : Fin 3 → ℝ} (hu : u ∈ controlSimplex) :
    u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 ≤ 1 := by
  have h0 := (hu.1 0).1
  have h1 := (hu.1 1).1
  have h2 := (hu.1 2).1
  rw [sumSq_eq_of_mem_controlSimplex hu]
  nlinarith [mul_nonneg h0 h1, mul_nonneg h0 h2, mul_nonneg h1 h2]

/-- **The printed `U_C` is `U_T`**: on the simplex `Σuᵢ² ≤ (Σuᵢ)² = 1`, since `uᵢ ≥ 0`.

Proof: `⊆` forgets the last condition; `⊇` is `sumSq_le_one_of_mem_controlSimplex` (the cross
terms `uᵢuⱼ` are `≥ 0`). -/
theorem controlDiskCAsPrinted_eq_controlSimplex : controlDiskCAsPrinted = controlSimplex := by
  ext u
  exact ⟨fun h ↦ ⟨h.1, h.2.1⟩, fun h ↦ ⟨h.1, h.2, sumSq_le_one_of_mem_controlSimplex h⟩⟩

/-- The simplex lies in the circumscribed disk: `U_T ⊆ U_C`.

Proof: as in `controlDiskCAsPrinted_eq_controlSimplex`, `Σuᵢ² ≤ (Σuᵢ)² = 1` on `U_T`. -/
theorem controlSimplex_subset_controlDiskC : controlSimplex ⊆ controlDiskC := fun _ hu ↦
  ⟨hu.2, (sumSq_le_one_of_mem_controlSimplex hu).trans_eq (one_pow 2).symm⟩

/-- **`U_I = U_r` with `r² = ½`**: the printed constraints `0 ≤ uᵢ ≤ 1` of `U_I` follow from
`Σuᵢ = 1` and `Σuᵢ² ≤ ½` (the inscribed disk lies in `U_T`).

Proof: `(√2/2)² = ½`. For `⊇`, if `u₀ < 0` then `u₁ + u₂ = 1 - u₀ > 1` and
`u₀² + u₁² + u₂² ≥ u₀² + (1 - u₀)²/2 > ½` (`nlinarith` with `(u₁ - u₂)² ≥ 0`), a contradiction;
likewise for `u₁`, `u₂`; then `uᵢ ≤ 1` since the other two are `≥ 0`. -/
theorem controlDiskI_eq_controlDisk : controlDiskI = controlDisk (√2 / 2) := by
  have h2 : (√2 / 2) ^ 2 = 1 / 2 := by rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  ext u
  simp only [controlDiskI, controlDisk, Set.mem_ofPred_eq, h2]
  refine ⟨fun h ↦ h.2, fun ⟨hs, hq⟩ ↦ ⟨?_, hs, hq⟩⟩
  have h0 : 0 ≤ u 0 := by nlinarith [sq_nonneg (u 1 - u 2)]
  have h1 : 0 ≤ u 1 := by nlinarith [sq_nonneg (u 0 - u 2)]
  have h2 : 0 ≤ u 2 := by nlinarith [sq_nonneg (u 0 - u 1)]
  intro i
  fin_cases i <;> simp <;> constructor <;> linarith

/-- `U_r` is compact.

Proof: closed (the preimage of a closed set under continuous maps) and contained in the compact
box `[-|r|, |r|]³` (`uᵢ² ≤ Σuⱼ² ≤ r²`). -/
theorem isCompact_controlDisk (r : ℝ) : IsCompact (controlDisk r) := by
  have hc : IsClosed (controlDisk r) := by
    have h1 : Continuous fun u : Fin 3 → ℝ ↦ u 0 + u 1 + u 2 := by fun_prop
    have h2 : Continuous fun u : Fin 3 → ℝ ↦ u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 := by fun_prop
    exact (isClosed_eq h1 continuous_const).inter (isClosed_le h2 continuous_const)
  refine (isCompact_univ_pi fun _ ↦ isCompact_Icc (a := -|r|) (b := |r|)).of_isClosed_subset hc
    fun u hu i _ ↦ ?_
  have hsq : u i ^ 2 ≤ |r| ^ 2 := by
    rw [sq_abs]
    fin_cases i <;> simp <;> nlinarith [hu.2, sq_nonneg (u 0), sq_nonneg (u 1), sq_nonneg (u 2)]
  exact abs_le_of_sq_le_sq' hsq (abs_nonneg r)

/-! ### Rotations of the control set -/

/-- A control set `U` is **closed under rotations** (the hypothesis of Theorem 9.0.3, TeX 7753–7755:
"if `A ∈ SO₂` is a rotation and `Z_u` is in the control set, then so is `Ad_A Z_u`"): for every
`A ∈ SO₂(ℝ)` and `u ∈ U` there is `u' ∈ U` with `Z_{u'} = A Z_u A⁻¹`. -/
def IsRotationClosed (U : Set (Fin 3 → ℝ)) : Prop :=
  ∀ A ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ, ∀ u ∈ U, ∃ u' ∈ U,
    controlMatrix u' = A * controlMatrix u * A⁻¹

/-- The inverse of `[[a, -c], [c, a]]` with `a² + c² = 1` is `[[a, c], [-c, a]]`. -/
private lemma inv_rotationForm {a c : ℝ} (h : a ^ 2 + c ^ 2 = 1) :
    (!![a, -c; c, a] : Mat2)⁻¹ = !![a, c; -c, a] := by
  refine Matrix.inv_eq_right_inv ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linarith

/-- `[[a, -c], [c, a]]` with `a² + c² = 1` is in `SO₂(ℝ)`. -/
private lemma rotationForm_mem_specialOrthogonalGroup {a c : ℝ} (h : a ^ 2 + c ^ 2 = 1) :
    (!![a, -c; c, a] : Mat2) ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ :=
  Matrix.of_mem_specialOrthogonalGroup_fin_two_iff.2 ⟨rfl, rfl, by linear_combination h⟩

/-- Every `A ∈ SO₂(ℝ)` is `[[a, -c], [c, a]]` with `a² + c² = 1`. -/
private lemma exists_rotationForm_of_mem_specialOrthogonalGroup {A : Mat2}
    (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ) :
    ∃ a c : ℝ, a ^ 2 + c ^ 2 = 1 ∧ A = !![a, -c; c, a] := by
  rw [Matrix.eta_fin_two A] at hA
  obtain ⟨h1, h2, h3⟩ := Matrix.of_mem_specialOrthogonalGroup_fin_two_iff.1 hA
  refine ⟨A 0 0, A 1 0, by rw [h2] at h3; linear_combination h3, ?_⟩
  conv_lhs => rw [Matrix.eta_fin_two A]
  rw [← h1, h2]

/-- The squared Frobenius norm `Σᵢⱼ Mᵢⱼ² = tr(MᵀM)`. -/
private def frobeniusSq (M : Mat2) : ℝ := M 0 0 ^ 2 + M 0 1 ^ 2 + M 1 0 ^ 2 + M 1 1 ^ 2

/-- Conjugation by a rotation `A ∈ SO₂(ℝ)` preserves `⟨J, M⟩`, the Frobenius norm and the trace
(`A = [[a, -c], [c, a]]`, `A⁻¹ = Aᵀ`: `AᵀJA = J` and `M ↦ AMAᵀ` is orthogonal). -/
private lemma conj_invariants_of_mem_specialOrthogonalGroup {A : Mat2}
    (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ) (M : Mat2) :
    traceForm J (A * M * A⁻¹) = traceForm J M ∧ frobeniusSq (A * M * A⁻¹) = frobeniusSq M ∧
      (A * M * A⁻¹).trace = M.trace := by
  obtain ⟨a, c, h, rfl⟩ := exists_rotationForm_of_mem_specialOrthogonalGroup hA
  rw [inv_rotationForm h, Matrix.eta_fin_two M]
  refine ⟨?_, ?_, ?_⟩
  · simp [traceForm, J, Matrix.trace_fin_two]
    linear_combination (M 0 1 - M 1 0) * h
  · simp [frobeniusSq]
    linear_combination (a ^ 2 + c ^ 2 + 1) *
      (M 0 0 ^ 2 + M 0 1 ^ 2 + M 1 0 ^ 2 + M 1 1 ^ 2) * h
  · simp [Matrix.trace_fin_two]
    linear_combination (M 0 0 + M 1 1) * h

/-- `Σuᵢ = -(3/2) ⟨J, Z_u⟩`. -/
private lemma sum_eq_traceForm_J_controlMatrix (u : Fin 3 → ℝ) :
    u 0 + u 1 + u 2 = -(3 / 2) * traceForm J (controlMatrix u) := by
  simp [traceForm, J, controlMatrix, Matrix.trace_fin_two]
  ring

/-- `Σuᵢ² = (3/4) tr(Z_uᵀZ_u) + (3/8) ⟨J, Z_u⟩²`. -/
private lemma sumSq_eq_frobeniusSq_controlMatrix (u : Fin 3 → ℝ) :
    u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 =
      3 / 4 * frobeniusSq (controlMatrix u) + 3 / 8 * traceForm J (controlMatrix u) ^ 2 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp [frobeniusSq, traceForm, J, controlMatrix, Matrix.trace_fin_two, div_pow, h3]
  ring

/-- `u ↦ Z_u` maps onto `𝔰𝔩₂(ℝ)`: the traceless `M` is `Z_u` for
`u = (M₁₀, ((M₁₀ - 3M₀₁)/2 + √3 M₀₀)/2, ((M₁₀ - 3M₀₁)/2 - √3 M₀₀)/2)`. -/
private lemma exists_controlMatrix_eq_of_trace_eq_zero {M : Mat2} (hM : M.trace = 0) :
    ∃ u : Fin 3 → ℝ, controlMatrix u = M := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3' : √3 ≠ 0 := by positivity
  rw [Matrix.trace_fin_two] at hM
  refine ⟨![M 1 0, ((M 1 0 - 3 * M 0 1) / 2 + √3 * M 0 0) / 2,
    ((M 1 0 - 3 * M 0 1) / 2 - √3 * M 0 0) / 2], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [controlMatrix] <;> field_simp <;>
    first | linear_combination | linear_combination (-4 * √3) * hM

/-- If `Z_{u'} = A Z_u A⁻¹` with `A ∈ SO₂(ℝ)`, then `Σu'ᵢ = Σuᵢ` and `Σu'ᵢ² = Σuᵢ²`. -/
private lemma sum_eq_and_sumSq_eq_of_controlMatrix_eq_conj {A : Mat2}
    (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ) {u u' : Fin 3 → ℝ}
    (hu : controlMatrix u' = A * controlMatrix u * A⁻¹) :
    u' 0 + u' 1 + u' 2 = u 0 + u 1 + u 2 ∧
      u' 0 ^ 2 + u' 1 ^ 2 + u' 2 ^ 2 = u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 := by
  obtain ⟨hJ, hF, -⟩ := conj_invariants_of_mem_specialOrthogonalGroup hA (controlMatrix u)
  rw [sum_eq_traceForm_J_controlMatrix, sum_eq_traceForm_J_controlMatrix u,
    sumSq_eq_frobeniusSq_controlMatrix, sumSq_eq_frobeniusSq_controlMatrix u, hu, hJ, hF]
  exact ⟨rfl, rfl⟩

/-- **The disks `U_r` are closed under rotations** (TeX 7733–7734: "the disk control set is
invariant under rotations by the circle group `S¹`"; the proof of Theorem 9.1.6, TeX 7922–7925:
"`Z_u ↦ Ad_{exp(Jθ)} Z_u ∈ U_C`"; Remark 9.1.7 for `U_r`).

Proof:
1. `u ↦ Z_u` maps onto `𝔰𝔩₂(ℝ)`, with the explicit preimage
   `Z ↦ (Z₁₀, ((Z₁₀ - 3Z₀₁)/2 + √3 Z₀₀)/2, ((Z₁₀ - 3Z₀₁)/2 - √3 Z₀₀)/2)`; `u'` is the preimage of
   the traceless `A Z_u A⁻¹`.
2. `Σuᵢ = -(3/2)⟨J, Z_u⟩` and `Σuᵢ² = (3/4) tr(Z_uᵀZ_u) + (3/8)⟨J, Z_u⟩²`.
3. For `A = [[a, -c], [c, a]] ∈ SO₂(ℝ)` (`Matrix.of_mem_specialOrthogonalGroup_fin_two_iff`),
   `A⁻¹ = Aᵀ`, and `⟨J, AMA⁻¹⟩ = ⟨J, M⟩`, `tr((AMA⁻¹)ᵀ AMA⁻¹) = tr(MᵀM)`; so `Σu' = Σu = 1` and
   `Σu'ᵢ² = Σuᵢ² ≤ r²`. -/
theorem isRotationClosed_controlDisk (r : ℝ) : IsRotationClosed (controlDisk r) := by
  intro A hA u hu
  have htr : (A * controlMatrix u * A⁻¹).trace = 0 := by
    rw [(conj_invariants_of_mem_specialOrthogonalGroup hA _).2.2, Matrix.trace_fin_two]
    simp [controlMatrix]
    ring
  obtain ⟨u', hu'⟩ := exists_controlMatrix_eq_of_trace_eq_zero htr
  obtain ⟨h1, h2⟩ := sum_eq_and_sumSq_eq_of_controlMatrix_eq_conj hA hu'
  exact ⟨u', ⟨h1.trans hu.1, h2.trans_le hu.2⟩, hu'⟩

/-! ### Theorem 9.0.3: the rotation invariance of the Hamiltonian -/

/-- `A J A⁻¹ = J` for `A ∈ SO₂(ℝ)`. -/
private lemma conj_J_of_mem_specialOrthogonalGroup {A : Mat2}
    (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ) : A * J * A⁻¹ = J := by
  obtain ⟨a, c, h, rfl⟩ := exists_rotationForm_of_mem_specialOrthogonalGroup hA
  rw [inv_rotationForm h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J] <;> linarith

/-- The trace form is invariant under conjugation by `A ∈ SO₂(ℝ)`:
`⟨AMA⁻¹, ANA⁻¹⟩ = tr(A M N A⁻¹) = ⟨M, N⟩`. -/
private lemma traceForm_conj_of_mem_specialOrthogonalGroup {A : Mat2}
    (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ) (M N : Mat2) :
    traceForm (A * M * A⁻¹) (A * N * A⁻¹) = traceForm M N := by
  have hdet : IsUnit A.det := by
    rw [(Matrix.mem_specialOrthogonalGroup_iff.1 hA).2]
    exact isUnit_one
  unfold traceForm
  rw [show A * M * A⁻¹ * (A * N * A⁻¹) = A * (M * N) * A⁻¹ by
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hdet],
    Matrix.trace_mul_cycle, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]

/-- **The Hamiltonian is invariant under rotations** (the "simple computation" of the proof of
Theorem 9.0.3, TeX 7780–7784): for `A ∈ SO₂(ℝ)` and controls `u, u'` with `Z_{u'} = A Z_u A⁻¹`,
`H(AΛ₁A⁻¹, AΛ_RA⁻¹, AXA⁻¹; Z_{u'}) = H(Λ₁, Λ_R, X; Z_u)`, with `H` of `eqn:full-hamiltonian`.

Proof: the trace form is invariant under conjugation,
`⟨AMA⁻¹, ANA⁻¹⟩ = tr(A M N A⁻¹) = ⟨M, N⟩` (`Matrix.trace_mul_cycle`, `A` invertible since
`det A = 1`), and `A J A⁻¹ = J` for `A ∈ SO₂(ℝ)` (`A = [[a, -c], [c, a]]`); so each of
`⟨Λ₁ - (3/2) λ_cost J, X⟩`, `⟨Λ_R, Z_u⟩` and `⟨X, Z_u⟩` is unchanged (`A(Λ₁ - (3/2)λJ)A⁻¹ =
AΛ₁A⁻¹ - (3/2)λJ`). -/
theorem hamiltonian_conj {A : Mat2} (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ) (lam : ℝ)
    (Λ₁ ΛR X : Mat2) {u u' : Fin 3 → ℝ} (hu : controlMatrix u' = A * controlMatrix u * A⁻¹) :
    hamiltonian lam (A * Λ₁ * A⁻¹) (A * ΛR * A⁻¹) (A * X * A⁻¹) u' =
      hamiltonian lam Λ₁ ΛR X u := by
  have hsub : A * Λ₁ * A⁻¹ - (3 / 2 * lam) • J = A * (Λ₁ - (3 / 2 * lam) • J) * A⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      conj_J_of_mem_specialOrthogonalGroup hA]
  unfold hamiltonian
  simp only [hsub, hu, traceForm_conj_of_mem_specialOrthogonalGroup hA]


/-- **Theorem 9.0.3** (`thm:symmetries`, TeX 7751–7784). Let `H` be the Hamiltonian of the
Reinhardt optimal control problem (`eqn:full-hamiltonian`) and suppose that the control set `U` is
closed under rotations. Then `H` is invariant under the action of `SO₂(ℝ) ⊆ SL₂(ℝ)`: for
`A ∈ SO₂(ℝ)`, the action `X ↦ Ad_A X`, `Λ₁ ↦ Ad_A Λ₁`, `Λ_R ↦ Ad_A Λ_R`, `Z_u ↦ Ad_A Z_u` takes
each control `u ∈ U` to a control `u' ∈ U` and leaves `H` unchanged.

Proof (the book's): the hypothesis gives `u' ∈ U` with `Z_{u'} = Ad_A Z_u`, and the computation
`hamiltonian_conj` ("a simple computation now using the expression for the control-dependent
Hamiltonian"). -/
theorem theorem9_0_3 {U : Set (Fin 3 → ℝ)} (hU : IsRotationClosed U) {A : Mat2}
    (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ) (lam : ℝ) (Λ₁ ΛR X : Mat2)
    {u : Fin 3 → ℝ} (hu : u ∈ U) :
    ∃ u' ∈ U, controlMatrix u' = A * controlMatrix u * A⁻¹ ∧
      hamiltonian lam (A * Λ₁ * A⁻¹) (A * ΛR * A⁻¹) (A * X * A⁻¹) u' =
        hamiltonian lam Λ₁ ΛR X u := by
  obtain ⟨u', hu', hZ⟩ := hU A hA u hu
  exact ⟨u', hu', hZ, hamiltonian_conj hA lam Λ₁ ΛR X hZ⟩

/-! ### Remark 9.0.4: `U_T` has only a discrete symmetry -/

/-- `R = [[½, -√3/2], [√3/2, ½]]` has the form `[[a, -c], [c, a]]`. -/
private lemma R_eq_rotationForm : R = !![1 / 2, -(√3 / 2); √3 / 2, 1 / 2] := rfl

private lemma R_rotationForm_sq_add_sq : (1 / 2 : ℝ) ^ 2 + (√3 / 2) ^ 2 = 1 := by
  linear_combination (Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)) / 4

/-- `R² = [[-½, -√3/2], [√3/2, -½]]`, the rotation by `2π/3`. -/
private lemma R_sq_eq : R ^ 2 = !![-1 / 2, -(√3 / 2); √3 / 2, -1 / 2] := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [sq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [R] <;> linarith

/-- `R³ = -I`. -/
private lemma R_pow_three_eq : R ^ 3 = -1 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [pow_succ, R_sq_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [R] <;> linarith

/-- The property of Remark 9.0.4: `Ad_A` maps the control matrices of `U_T` to control matrices
of `U_T`. -/
private def ConjPreservesSimplex (A : Mat2) : Prop :=
  ∀ u ∈ controlSimplex, ∃ u' ∈ controlSimplex, controlMatrix u' = A * controlMatrix u * A⁻¹

private lemma conjPreservesSimplex_one : ConjPreservesSimplex 1 := fun u hu ↦ ⟨u, hu, by simp⟩

/-- The rotations preserving `U_T` are closed under products (`(AB)⁻¹ = B⁻¹A⁻¹`). -/
private lemma ConjPreservesSimplex.mul {A B : Mat2} (hA : ConjPreservesSimplex A)
    (hB : ConjPreservesSimplex B) : ConjPreservesSimplex (A * B) := by
  intro u hu
  obtain ⟨u₁, hu₁, h₁⟩ := hB u hu
  obtain ⟨u₂, hu₂, h₂⟩ := hA u₁ hu₁
  refine ⟨u₂, hu₂, ?_⟩
  rw [h₂, h₁, Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc]

/-- `Ad_R` permutes the coordinates of the controls cyclically: `R Z_u R⁻¹ = Z_{(u₁, u₂, u₀)}`
(on the vertices, `R Z_{e_m} R⁻¹ = Z_{e_{m-1}}`, indices mod 3). -/
private lemma conjPreservesSimplex_R : ConjPreservesSimplex R := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3' : √3 ≠ 0 := by positivity
  intro u ⟨hi, hs⟩
  refine ⟨![u 1, u 2, u 0], ⟨fun i ↦ ?_, ?_⟩, ?_⟩
  · fin_cases i
    exacts [hi 1, hi 2, hi 0]
  · simp only [Matrix.cons_val]
    linarith
  · rw [R_eq_rotationForm, inv_rotationForm R_rotationForm_sq_add_sq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [controlMatrix] <;> field_simp <;> ring_nf <;>
      simp only [h3] <;> ring_nf

private lemma conjPreservesSimplex_R_pow (k : ℕ) : ConjPreservesSimplex (R ^ k) := by
  induction k with
  | zero => simpa using conjPreservesSimplex_one
  | succ k ih => rw [pow_succ]; exact ih.mul conjPreservesSimplex_R

/-- The vertex step of Remark 9.0.4 (`⇒`): if the rotation `A = [[a, -c], [c, a]]` maps the
control matrices of `U_T` to control matrices of `U_T`, then `Ad_A Z_{e₀} = Z_{u'}` with
`u' ∈ U_T` and `Σu'ᵢ² = Σ(e₀)ᵢ² = 1` (`sum_eq_and_sumSq_eq_of_controlMatrix_eq_conj`), so `u'` is
a vertex `e_m` (on `U_T`, `Σuᵢ² = 1` forces the cross terms `uᵢuⱼ ≥ 0` to vanish); comparing the
entries `(0, 0)` and `(1, 0)` of `Ad_A Z_{e₀} = [[-4ac/3, ⋯], [a² - c²/3, ⋯]]` with those of
`Z_{e_m}` leaves the six rotations by multiples of `π/3`. -/
private lemma rotationForm_cases_of_conjPreservesSimplex {a c : ℝ} (h : a ^ 2 + c ^ 2 = 1)
    (hP : ConjPreservesSimplex !![a, -c; c, a]) :
    (a = 1 ∧ c = 0) ∨ (a = -1 ∧ c = 0) ∨ (a = 1 / 2 ∧ c = √3 / 2) ∨
      (a = -1 / 2 ∧ c = -(√3 / 2)) ∨ (a = -1 / 2 ∧ c = √3 / 2) ∨
        (a = 1 / 2 ∧ c = -(√3 / 2)) := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3' : √3 ≠ 0 := by positivity
  have hv : vertex 0 ∈ controlSimplex := by
    refine ⟨fun i ↦ ?_, ?_⟩ <;> (try fin_cases i) <;> simp [vertex]
  obtain ⟨u, hu, hZ⟩ := hP _ hv
  have hsq : u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 1 := by
    simpa [vertex] using
      (sum_eq_and_sumSq_eq_of_controlMatrix_eq_conj (rotationForm_mem_specialOrthogonalGroup h)
        hZ).2
  rw [inv_rotationForm h] at hZ
  -- the entries `(0, 0)` and `(1, 0)` of `Ad_A Z_{e₀}`
  have e00 : u 1 - u 2 = -(4 / 3) * (a * c) * √3 := by
    have e : (u 1 - u 2) / √3 = -(4 / 3) * (a * c) := by
      have e := congrFun (congrFun hZ 0) 0
      simp [controlMatrix, vertex] at e
      linarith
    rwa [div_eq_iff h3'] at e
  have e10 : u 0 = a ^ 2 - c ^ 2 / 3 := by
    have e := congrFun (congrFun hZ 1) 0
    simp [controlMatrix, vertex] at e
    linarith
  -- the image of `e₀` is a vertex: the cross terms vanish
  have hp := sumSq_eq_of_mem_controlSimplex hu
  obtain ⟨hi, hs⟩ := hu
  have h0 := (hi 0).1
  have h1 := (hi 1).1
  have h2 := (hi 2).1
  have h01 : u 0 * u 1 = 0 := by nlinarith [mul_nonneg h0 h1, mul_nonneg h0 h2, mul_nonneg h1 h2]
  have h02 : u 0 * u 2 = 0 := by nlinarith [mul_nonneg h0 h1, mul_nonneg h0 h2, mul_nonneg h1 h2]
  have h12 : u 1 * u 2 = 0 := by nlinarith [mul_nonneg h0 h1, mul_nonneg h0 h2, mul_nonneg h1 h2]
  -- `a² = ¼` and `ac = s√3/4` give `(a, c) = ±(½, s√3/2)`
  have hhalf : ∀ s : ℝ, a * c = s * (√3 / 4) → a ^ 2 = 1 / 4 →
      (a = 1 / 2 ∧ c = s * (√3 / 2)) ∨ (a = -1 / 2 ∧ c = -(s * (√3 / 2))) := by
    intro s hac ha
    have : (a - 1 / 2) * (a + 1 / 2) = 0 := by linear_combination ha
    rcases mul_eq_zero.1 this with ha | ha
    · refine Or.inl ⟨by linarith, ?_⟩
      rw [show a = 1 / 2 by linarith] at hac
      linear_combination 2 * hac
    · refine Or.inr ⟨by linarith, ?_⟩
      rw [show a = -1 / 2 by linarith] at hac
      linear_combination -2 * hac
  by_cases hu0 : u 0 = 0
  · by_cases hu1 : u 1 = 0
    · -- `Ad_A Z_{e₀} = Z_{e₂}`: `A = R` or `R⁴`
      have hu2 : u 2 = 1 := by linarith
      rw [hu1, hu2] at e00
      rw [hu0] at e10
      have hac : a * c = 1 * (√3 / 4) := by
        linear_combination (√3 / 4) * e00 - (a * c / 3) * h3
      rcases hhalf 1 hac (by linear_combination (1 / 4) * h - (3 / 4) * e10) with h' | h'
      · exact Or.inr (Or.inr (Or.inl (by simpa using h')))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa using h'))))
    · -- `Ad_A Z_{e₀} = Z_{e₁}`: `A = R²` or `R⁵`
      have hu2 : u 2 = 0 := (mul_eq_zero.1 h12).resolve_left hu1
      have hu1' : u 1 = 1 := by linarith
      rw [hu1', hu2] at e00
      rw [hu0] at e10
      have hac : a * c = -1 * (√3 / 4) := by
        linear_combination (√3 / 4) * e00 - (a * c / 3) * h3
      rcases hhalf (-1) hac (by linear_combination (1 / 4) * h - (3 / 4) * e10) with h' | h'
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by simpa using h')))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simpa using h')))))
  · -- `Ad_A Z_{e₀} = Z_{e₀}`: `A = ±I`
    have hu0' : u 0 = 1 := by
      have hu1 : u 1 = 0 := (mul_eq_zero.1 h01).resolve_left hu0
      have hu2 : u 2 = 0 := (mul_eq_zero.1 h02).resolve_left hu0
      linarith
    rw [hu0'] at e10
    have hc : c ^ 2 = 0 := by linear_combination (3 / 4) * h + (3 / 4) * e10
    obtain rfl : c = 0 := pow_eq_zero_iff two_ne_zero |>.1 hc
    have : (a - 1) * (a + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with ha | ha
    · exact Or.inl ⟨by linarith, rfl⟩
    · exact Or.inr (Or.inl ⟨by linarith, rfl⟩)

/-- **Remark 9.0.4** (TeX 7786–7790): "the control set `U_T` is only symmetric by discrete
`ℤ/3ℤ`-rotations and not under general `SO₂` rotations". A rotation `A ∈ SO₂(ℝ)` maps the control
matrices of `U_T` to control matrices of `U_T` exactly when `A` is a power of `R = exp(Jπ/3)`.
Since `R³ = -I`, `Ad_{Rᵏ}` depends on `k mod 3`: the symmetry group of `U_T` acting by `Ad` is
`ℤ/3ℤ`, and `Ad_R` permutes the vertices cyclically (`R⁻¹ Z_{e_m} R = Z_{e_{m+1}}`).

Proof (the book gives none):
1. (`⇐`) `R Z_u R⁻¹ = Z_{(u₁, u₂, u₀)}` (on the vertices `R Z_{e_m} R⁻¹ = Z_{e_{m-1}}`, as in
   `R_conj_controlMatrix_vertex`, `SmoothedPolygons/Ch4/StarDomain.lean`), and the rotations
   preserving `U_T` are closed under products; induction on `k`.
2. (`⇒`) `A = [[a, -c], [c, a]]` with `a² + c² = 1`
   (`Matrix.of_mem_specialOrthogonalGroup_fin_two_iff`). `Ad_A` preserves `Σuᵢ²` (as in
   `isRotationClosed_controlDisk`), and the vertices are the only points of `U_T` with
   `Σuᵢ² = 1`, so `Ad_A Z_{e₀} = Z_{e_m}` for some vertex `e_m`. Comparing two entries gives
   `(a, c) = ±(1, 0)` (`m = 0`), `±(½, √3/2)` (`m = 2`) or `±(-½, √3/2)` (`m = 1`), i.e.
   `A = Rᵏ` with `k = 0, 3`, `1, 4` or `2, 5` (`R³ = -I`). -/
theorem remark9_0_4 {A : Mat2} (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ) :
    (∀ u ∈ controlSimplex, ∃ u' ∈ controlSimplex, controlMatrix u' = A * controlMatrix u * A⁻¹) ↔
      ∃ k : ℕ, A = R ^ k := by
  refine ⟨fun hP ↦ ?_, ?_⟩
  · obtain ⟨a, c, h, rfl⟩ := exists_rotationForm_of_mem_specialOrthogonalGroup hA
    have hR4 : R ^ 4 = -R := by rw [pow_succ, R_pow_three_eq, neg_one_mul]
    have hR5 : R ^ 5 = -R ^ 2 := by
      rw [show 5 = 3 + 2 from rfl, pow_add, R_pow_three_eq, neg_one_mul]
    rcases rotationForm_cases_of_conjPreservesSimplex h hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨0, by ext i j; fin_cases i <;> fin_cases j <;> simp⟩
    · exact ⟨3, by rw [R_pow_three_eq]; ext i j; fin_cases i <;> fin_cases j <;> simp⟩
    · exact ⟨1, by rw [pow_one]; rfl⟩
    · exact ⟨4, by rw [hR4, R_eq_rotationForm]; ext i j; fin_cases i <;> fin_cases j <;> norm_num⟩
    · exact ⟨2, by rw [R_sq_eq]⟩
    · exact ⟨5, by rw [hR5, R_sq_eq]; ext i j; fin_cases i <;> fin_cases j <;> norm_num⟩
  · rintro ⟨k, rfl⟩
    exact conjPreservesSimplex_R_pow k

/-- The `(0, 0)` entry of `Rᵏ` is `1`, `½`, `-½` or `-1` (`Rᵏ = (-1)^⌊k/3⌋ R^(k mod 3)`). -/
private lemma R_pow_apply_zero_zero (k : ℕ) :
    (R ^ k) 0 0 = 1 ∨ (R ^ k) 0 0 = 1 / 2 ∨ (R ^ k) 0 0 = -1 / 2 ∨ (R ^ k) 0 0 = -1 := by
  rw [← Nat.div_add_mod k 3, pow_add, pow_mul, R_pow_three_eq]
  have hr : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases neg_one_pow_eq_or Mat2 (k / 3) with hs | hs <;> rw [hs] <;>
    rcases hr with hr | hr | hr <;> rw [hr] <;> simp only [pow_zero, pow_one, R_sq_eq] <;>
    norm_num [R]

/-- **`U_T` is not closed under rotations** (Remark 9.0.4, "not under general `SO₂` rotations").

Proof: the rotation `A = exp(Jπ/6) = [[√3/2, -½], [½, √3/2]] ∈ SO₂(ℝ)` is not a power of `R`
(the powers `Rᵏ` have `(0, 0)` entry in `{1, ½, -½, -1}`, since `R³ = -I`), so `remark9_0_4`
excludes it. -/
theorem not_isRotationClosed_controlSimplex : ¬ IsRotationClosed controlSimplex := by
  intro hU
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h : (√3 / 2) ^ 2 + (1 / 2 : ℝ) ^ 2 = 1 := by linear_combination h3 / 4
  obtain ⟨k, hk⟩ := (remark9_0_4 (rotationForm_mem_specialOrthogonalGroup h)).1
    (hU _ (rotationForm_mem_specialOrthogonalGroup h))
  have h00 := congrFun (congrFun hk 0) 0
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
    Matrix.cons_val_fin_one] at h00
  rcases R_pow_apply_zero_zero k with h' | h' | h' | h' <;> rw [h'] at h00 <;>
    nlinarith [Real.sqrt_nonneg 3]

end SmoothedPolygons
