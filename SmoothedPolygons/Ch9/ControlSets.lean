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

/-- **The printed `U_C` is `U_T`**: on the simplex `Σuᵢ² ≤ (Σuᵢ)² = 1`, since `uᵢ ≥ 0`.

Proof plan (10–15 lines): `ext u`; `⊆` forgets the last condition; `⊇`: `Σuᵢ² ≤ (Σuᵢ)² = 1`
by `nlinarith` from `0 ≤ uᵢ` (the cross terms `uᵢuⱼ ≥ 0`). -/
theorem controlDiskCAsPrinted_eq_controlSimplex : controlDiskCAsPrinted = controlSimplex := by
  sorry

/-- The simplex lies in the circumscribed disk: `U_T ⊆ U_C`.

Proof plan (5–10 lines): as in `controlDiskCAsPrinted_eq_controlSimplex`, `Σuᵢ² ≤ (Σuᵢ)² = 1` on
`U_T`. -/
theorem controlSimplex_subset_controlDiskC : controlSimplex ⊆ controlDiskC := by
  sorry

/-- **`U_I = U_r` with `r² = ½`**: the printed constraints `0 ≤ uᵢ ≤ 1` of `U_I` follow from
`Σuᵢ = 1` and `Σuᵢ² ≤ ½` (the inscribed disk lies in `U_T`).

Proof plan (15–25 lines): `ext u`; `(√2/2)² = ½`; for `⊇`, if `u₀ < 0` then `u₁ + u₂ > 1` and
`u₁² + u₂² ≥ (u₁ + u₂)²/2 > ½`, a contradiction (`nlinarith`), likewise for `u₁`, `u₂`; then
`uᵢ ≤ 1` since the other two are `≥ 0`. -/
theorem controlDiskI_eq_controlDisk : controlDiskI = controlDisk (√2 / 2) := by
  sorry

/-- `U_r` is compact.

Proof plan (15–25 lines): closed (preimage of a closed set under continuous maps) and bounded
(`|uᵢ| ≤ |r|` from `uᵢ² ≤ Σuⱼ² ≤ r²`), `Metric.isCompact_of_isClosed_isBounded`. -/
theorem isCompact_controlDisk (r : ℝ) : IsCompact (controlDisk r) := by
  sorry

/-! ### Rotations of the control set -/

/-- A control set `U` is **closed under rotations** (the hypothesis of Theorem 9.0.3, TeX 7753–7755:
"if `A ∈ SO₂` is a rotation and `Z_u` is in the control set, then so is `Ad_A Z_u`"): for every
`A ∈ SO₂(ℝ)` and `u ∈ U` there is `u' ∈ U` with `Z_{u'} = A Z_u A⁻¹`. -/
def IsRotationClosed (U : Set (Fin 3 → ℝ)) : Prop :=
  ∀ A ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ, ∀ u ∈ U, ∃ u' ∈ U,
    controlMatrix u' = A * controlMatrix u * A⁻¹

/-- **The disks `U_r` are closed under rotations** (TeX 7733–7734: "the disk control set is
invariant under rotations by the circle group `S¹`"; the proof of Theorem 9.1.6, TeX 7922–7925:
"`Z_u ↦ Ad_{exp(Jθ)} Z_u ∈ U_C`"; Remark 9.1.7 for `U_r`).

Proof plan (60–100 lines):
1. `u ↦ Z_u` is a linear isomorphism `ℝ³ ≅ 𝔰𝔩₂(ℝ)`, with inverse
   `Z ↦ (Z₁₀, ((Z₁₀ - 3Z₀₁)/2 + √3 Z₀₀)/2, ((Z₁₀ - 3Z₀₁)/2 - √3 Z₀₀)/2)` (check by `ext; ring`
   with `√3² = 3`); set `u' := ` this inverse applied to `A Z_u A⁻¹` (traceless).
2. `Σu = -(3/2)⟨J, Z_u⟩` and `Σuᵢ² = (Σuᵢ)²/3 - (3/2) det(Z_u - (Σu/3) J)` (the matrix
   `Z_u - (Σu/3) J` is symmetric and traceless; `ring` with `√3² = 3`).
3. For `A ∈ SO₂(ℝ)`: `A⁻¹ = Aᵀ`, `A J A⁻¹ = J` (`A = [[a, -c], [c, a]]` by
   `Matrix.of_mem_specialOrthogonalGroup_fin_two_iff`), `⟨J, A Z A⁻¹⟩ = ⟨J, Z⟩` and
   `det(A M A⁻¹) = det M`; so `Σu' = Σu = 1` and `Σu'ᵢ² = Σuᵢ² ≤ r²`. -/
theorem isRotationClosed_controlDisk (r : ℝ) : IsRotationClosed (controlDisk r) := by
  sorry

/-! ### Theorem 9.0.3: the rotation invariance of the Hamiltonian -/

/-- **The Hamiltonian is invariant under rotations** (the "simple computation" of the proof of
Theorem 9.0.3, TeX 7780–7784): for `A ∈ SO₂(ℝ)` and controls `u, u'` with `Z_{u'} = A Z_u A⁻¹`,
`H(AΛ₁A⁻¹, AΛ_RA⁻¹, AXA⁻¹; Z_{u'}) = H(Λ₁, Λ_R, X; Z_u)`, with `H` of `eqn:full-hamiltonian`.

Proof plan (25–40 lines): the trace form is invariant under conjugation,
`⟨AMA⁻¹, ANA⁻¹⟩ = tr(A M N A⁻¹) = ⟨M, N⟩` (`Matrix.trace_mul_cycle`, `A` invertible since
`det A = 1`), and `A J A⁻¹ = J` for `A ∈ SO₂(ℝ)` (`A = [[a, -c], [c, a]]`); so each of
`⟨Λ₁ - (3/2) λ_cost J, X⟩`, `⟨Λ_R, Z_u⟩` and `⟨X, Z_u⟩` is unchanged (`A(Λ₁ - (3/2)λJ)A⁻¹ =
AΛ₁A⁻¹ - (3/2)λJ`). -/
theorem hamiltonian_conj {A : Mat2} (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ) (lam : ℝ)
    (Λ₁ ΛR X : Mat2) {u u' : Fin 3 → ℝ} (hu : controlMatrix u' = A * controlMatrix u * A⁻¹) :
    hamiltonian lam (A * Λ₁ * A⁻¹) (A * ΛR * A⁻¹) (A * X * A⁻¹) u' =
      hamiltonian lam Λ₁ ΛR X u := by
  sorry

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

/-- **Remark 9.0.4** (TeX 7786–7790): "the control set `U_T` is only symmetric by discrete
`ℤ/3ℤ`-rotations and not under general `SO₂` rotations". A rotation `A ∈ SO₂(ℝ)` maps the control
matrices of `U_T` to control matrices of `U_T` exactly when `A` is a power of `R = exp(Jπ/3)`.
Since `R³ = -I`, `Ad_{Rᵏ}` depends on `k mod 3`: the symmetry group of `U_T` acting by `Ad` is
`ℤ/3ℤ`, and `Ad_R` permutes the vertices cyclically (`R⁻¹ Z_{e_m} R = Z_{e_{m+1}}`).

Proof plan (100–150 lines):
1. (`⇐`) `R Z_{e_m} R⁻¹ = Z_{e_{m-1}}` (inverse of `poly_Rinv_conj_vertex`,
   `SmoothedPolygons/Ch7/DiscreteK.lean`, conjugated), extended to `U_T` by linearity of `u ↦ Z_u`
   (the permuted control is in `U_T`); induction on `k`.
2. (`⇒`) `A = [[a, -c], [c, a]]` with `a² + c² = 1`
   (`Matrix.of_mem_specialOrthogonalGroup_fin_two_iff`). `Ad_A` is affine on the plane of the
   control matrices and maps the vertex set `{Z_{e_m}}` of `U_T` onto itself (the extreme points of
   the triangle; `Ad_A` is a bijection of the plane preserving the triangle). Writing
   `Z_{e_m} = J/3 + S_m` with `S_m` symmetric traceless, `Ad_A S` rotates `(S₀₀, S₀₁)` by `2θ`
   (`a = cos θ`, `c = sin θ`), so `Ad_A S₀ = S_m` forces `2θ ∈ 2πm/3 + 2πℤ`, hence
   `(a, c) = (cos(kπ/3), sin(kπ/3))` for some `k ∈ {0, …, 5}`, i.e. `A = Rᵏ` (`R = [[½, -√3/2],
   [√3/2, ½]]`; the six cases by `cos`/`sin` of multiples of `π/3`, or algebraically: `(a, c)` with
   `a² + c² = 1` solving the two linear equations of `Ad_A S₀ = S_m`). -/
theorem remark9_0_4 {A : Mat2} (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ) :
    (∀ u ∈ controlSimplex, ∃ u' ∈ controlSimplex, controlMatrix u' = A * controlMatrix u * A⁻¹) ↔
      ∃ k : ℕ, A = R ^ k := by
  sorry

/-- **`U_T` is not closed under rotations** (Remark 9.0.4, "not under general `SO₂` rotations").

Proof plan (20–30 lines): the rotation `A = exp(Jπ/6) = [[√3/2, -½], [½, √3/2]] ∈ SO₂(ℝ)` is not
a power of `R` (the powers `Rᵏ`, `k < 6`, have `(0, 0)` entry in `{1, ½, -½, -1}`, and `R⁶ = I`),
so `remark9_0_4` excludes it. Directly: `Ad_A` rotates the plane of control matrices by `π/3`
about `Z_{centroid} = J/3`, so `Ad_A Z_{e₀} = Z_{u'}` with `u' = (⅔, ⅔, ⅔) - e_m` for some `m` (the
reflection of a vertex through the centroid), which has the coordinate `-⅓ < 0`; `u ↦ Z_u` is
injective, so no `u' ∈ U_T` works. -/
theorem not_isRotationClosed_controlSimplex : ¬ IsRotationClosed controlSimplex := by
  sorry

end SmoothedPolygons
