module

public import SmoothedPolygons.Ch4.StarDomain
public import SmoothedPolygons.AppA.FunctionalDerivative
public import Basic.Analysis.Calculus.MatrixFTC
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs

/-!
# The Hamiltonian and the costate equations (Chapter 6)

The convexity of the velocity sets (Lemma 6.1.2), normal, abnormal and singular extremals
(Definition 6.2.1), the Hamiltonian of the Reinhardt problem (`eqn:full-hamiltonian`), the costate
equations in the Lie algebra (Proposition 6.5.1), the general solution for `Λ₁`
(Corollary 6.5.3), and the control-dependent term of the costate equation (Corollary 6.5.4). The
state–costate equations of Problem 6.7.1 are part of `IsPontryaginExtremal` in
`SmoothedPolygons.Defs`.
-/

@[expose] public section

namespace SmoothedPolygons

open Matrix

/-- The velocity `f(x, y; u) = (f₁, f₂)` of the half-plane control problem (Problem 4.5.1). -/
noncomputable def halfPlaneField (x y : ℝ) (u : Fin 3 → ℝ) : Fin 2 → ℝ :=
  ![halfPlaneF₁ x y u, halfPlaneF₂ x y u]

/-- A ratio `F(u) = N(u)/d(u)` of a linear map `N` and a linear function `d` is a combination of
its values at the vertices of `U_T` with the weights `u_j d(e_j)/d(u)` (when `d` is negative on
`U_T`, these are the nonnegative values `L(F(u))` of the affine functions `L` of the proof of
Lemma 6.1.2). -/
private theorem ratio_eq_sum (N : (Fin 3 → ℝ) → Fin 2 → ℝ) (d : (Fin 3 → ℝ) → ℝ)
    (hN : ∀ u, N u = ∑ j, u j • N (vertex j)) (hd0 : ∀ j, d (vertex j) ≠ 0) (u : Fin 3 → ℝ)
    (hu : d u ≠ 0) :
    (d u)⁻¹ • N u = ∑ j, (u j * d (vertex j) / d u) • ((d (vertex j))⁻¹ • N (vertex j)) := by
  rw [hN u, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [smul_smul, smul_smul]
  congr 1
  field_simp [hd0 j]

/-- **Lemma 6.1.2** (`lem:control-convex`). For every `z = x + iy ∈ 𝔥*` the velocity set
`f(x, y; U_T)` is convex: it is the convex hull of the velocities at the three vertices of `U_T`.
Moreover its affine hull is all of `ℝ²`. -/
theorem lemma6_1_2 (x y : ℝ) (h : (x, y) ∈ starDomain) :
    halfPlaneField x y '' controlSimplex =
        convexHull ℝ {halfPlaneField x y (vertex 0), halfPlaneField x y (vertex 1),
          halfPlaneField x y (vertex 2)} ∧
      Convex ℝ (halfPlaneField x y '' controlSimplex) ∧
      affineSpan ℝ (halfPlaneField x y '' controlSimplex) = ⊤ := by
  obtain ⟨hy, hx1, hx2, hr⟩ := h
  have h3 : (0 : ℝ) < √3 := by positivity
  have h33 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  -- `f(x, y; u) = N(u)/d(u)` with `N` and `d` linear in `u`
  set N : (Fin 3 → ℝ) → Fin 2 → ℝ := fun u ↦
    ![y * (2 * controlMatrix u 0 0 * x + controlMatrix u 0 1 - controlMatrix u 1 0 * x ^ 2 +
      controlMatrix u 1 0 * y ^ 2), 2 * y ^ 2 * (controlMatrix u 0 0 - controlMatrix u 1 0 * x)]
    with hNdef
  set d : (Fin 3 → ℝ) → ℝ := fun u ↦
    2 * controlMatrix u 0 0 * x + controlMatrix u 0 1 - controlMatrix u 1 0 * x ^ 2 -
      controlMatrix u 1 0 * y ^ 2 with hddef
  have hf : halfPlaneField x y = fun u ↦ (d u)⁻¹ • N u := by
    funext u i
    fin_cases i <;> simp [halfPlaneField, halfPlaneF₁, halfPlaneF₂, hNdef, hddef] <;> ring
  have hN : ∀ u, N u = ∑ j, u j • N (vertex j) := fun u ↦ by
    funext i
    fin_cases i <;> simp [hNdef, controlMatrix, vertex, Fin.sum_univ_three] <;> ring
  have hd : ∀ u, d u = ∑ j, u j * d (vertex j) := fun u ↦ by
    simp [hddef, controlMatrix, vertex, Fin.sum_univ_three]; ring
  -- the denominators at the vertices are negative: these are the star inequalities
  have hd0 : d (vertex 0) = 1 / 3 - x ^ 2 - y ^ 2 := by
    simp [hddef, controlMatrix, vertex]
  have hd1 : d (vertex 1) = 2 / √3 * x - 2 / 3 := by
    simp [hddef, controlMatrix, vertex]; ring
  have hd2 : d (vertex 2) = -(2 / √3) * x - 2 / 3 := by
    simp [hddef, controlMatrix, vertex]; ring
  have hneg : ∀ j, d (vertex j) < 0 := by
    intro j
    fin_cases j
    · simp only [Fin.zero_eta, hd0]; linarith
    · simp only [Fin.mk_one, hd1, sub_neg]
      calc 2 / √3 * x < 2 / √3 * (1 / √3) := mul_lt_mul_of_pos_left hx2 (by positivity)
        _ = 2 / 3 := by rw [div_mul_div_comm, h33]; norm_num
    · simp only [Fin.reduceFinMk, hd2, sub_neg]
      calc -(2 / √3) * x < -(2 / √3) * -(1 / √3) :=
            mul_lt_mul_of_neg_left hx1 (neg_neg_of_pos (by positivity))
        _ = 2 / 3 := by rw [neg_mul_neg, div_mul_div_comm, h33]; norm_num
  have hdne : ∀ j, d (vertex j) ≠ 0 := fun j ↦ (hneg j).ne
  set p : Fin 3 → Fin 2 → ℝ := fun j ↦ (d (vertex j))⁻¹ • N (vertex j) with hpdef
  have hpv : ∀ j, halfPlaneField x y (vertex j) = p j := fun j ↦ by rw [hf]
  simp only [hpv]
  -- the denominator `d(u)` is negative on `U_T`
  have hdu : ∀ u ∈ controlSimplex, d u < 0 := by
    intro u hu
    obtain ⟨hb, hs⟩ := hu
    set M := max (max (d (vertex 0)) (d (vertex 1))) (d (vertex 2))
    have hM : M < 0 := max_lt (max_lt (hneg 0) (hneg 1)) (hneg 2)
    have h0 : u 0 * d (vertex 0) ≤ u 0 * M :=
      mul_le_mul_of_nonneg_left (le_max_of_le_left (le_max_left _ _)) (hb 0).1
    have h1 : u 1 * d (vertex 1) ≤ u 1 * M :=
      mul_le_mul_of_nonneg_left (le_max_of_le_left (le_max_right _ _)) (hb 1).1
    have h2 : u 2 * d (vertex 2) ≤ u 2 * M := mul_le_mul_of_nonneg_left (le_max_right _ _) (hb 2).1
    have hsum : u 0 * M + u 1 * M + u 2 * M = M := by rw [← add_mul, ← add_mul, hs, one_mul]
    rw [hd u, Fin.sum_univ_three]
    linarith
  -- `f(U_T)` lies in the triangle: `f(u) = ∑ⱼ (uⱼ d(eⱼ)/d(u)) f(eⱼ)`, a convex combination
  have hsub1 : halfPlaneField x y '' controlSimplex ⊆ convexHull ℝ {p 0, p 1, p 2} := by
    rintro _ ⟨u, hu, rfl⟩
    have hdu' := hdu u hu
    rw [hf]
    dsimp only
    rw [ratio_eq_sum N d hN hdne u hdu'.ne]
    refine mem_convexHull_of_exists_fintype (fun j ↦ u j * d (vertex j) / d u) p (fun j ↦ ?_) ?_
      (fun j ↦ ?_) rfl
    · exact div_nonneg_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (hu.1 j).1 (hneg j).le) hdu'.le
    · rw [← Finset.sum_div, ← hd u, div_self hdu'.ne]
    · fin_cases j <;> simp
  -- conversely every convex combination `∑ⱼ lⱼ f(eⱼ)` is attained, at `uⱼ ∝ lⱼ/d(eⱼ)`
  set S : Set (Fin 2 → ℝ) :=
    {z | ∃ l : Fin 3 → ℝ, (∀ j, 0 ≤ l j) ∧ ∑ j, l j = 1 ∧ ∑ j, l j • p j = z} with hSdef
  have hS : convexHull ℝ {p 0, p 1, p 2} ⊆ S := by
    refine convexHull_min ?_ ?_
    · intro z hz
      have hv : ∀ k, p k ∈ S := fun k ↦ ⟨vertex k, fun j ↦ by
        fin_cases k <;> fin_cases j <;> simp [vertex], by simp [vertex], by simp [vertex]⟩
      rcases hz with rfl | rfl | rfl
      exacts [hv 0, hv 1, hv 2]
    · rintro _ ⟨l, hl0, hl1, rfl⟩ _ ⟨m, hm0, hm1, rfl⟩ a b ha hb hab
      refine ⟨a • l + b • m, fun j ↦ ?_, ?_, ?_⟩
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        exact add_nonneg (mul_nonneg ha (hl0 j)) (mul_nonneg hb (hm0 j))
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
          ← Finset.mul_sum, hl1, hm1, mul_one, hab]
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, mul_smul,
          Finset.sum_add_distrib, Finset.smul_sum]
  have hS' : S ⊆ halfPlaneField x y '' controlSimplex := by
    rintro _ ⟨l, hl0, hl1, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c : Fin 3 → ℝ, ∀ j, c j = l j / d (vertex j) := ⟨_, fun _ ↦ rfl⟩
    have hc0 : ∀ j, c j ≤ 0 := fun j ↦ by
      rw [hc]; exact div_nonpos_of_nonneg_of_nonpos (hl0 j) (hneg j).le
    obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = c 0 + c 1 + c 2 := ⟨_, rfl⟩
    have hcs : σ < 0 := by
      set M := max (max (d (vertex 0))⁻¹ (d (vertex 1))⁻¹) (d (vertex 2))⁻¹
      have hM : M < 0 :=
        max_lt (max_lt (inv_lt_zero.2 (hneg 0)) (inv_lt_zero.2 (hneg 1))) (inv_lt_zero.2 (hneg 2))
      have h0 : c 0 ≤ l 0 * M := by
        rw [hc, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (le_max_of_le_left (le_max_left _ _)) (hl0 0)
      have h1 : c 1 ≤ l 1 * M := by
        rw [hc, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (le_max_of_le_left (le_max_right _ _)) (hl0 1)
      have h2 : c 2 ≤ l 2 * M := by
        rw [hc, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (le_max_right _ _) (hl0 2)
      have hsum : l 0 * M + l 1 * M + l 2 * M = M := by
        rw [← add_mul, ← add_mul, ← Fin.sum_univ_three, hl1, one_mul]
      linarith
    obtain ⟨u, hu_def⟩ : ∃ u : Fin 3 → ℝ, ∀ j, u j = c j / σ := ⟨_, fun _ ↦ rfl⟩
    have hu0 : ∀ j, 0 ≤ u j := fun j ↦ by rw [hu_def]; exact div_nonneg_of_nonpos (hc0 j) hcs.le
    have hu1 : u 0 + u 1 + u 2 = 1 := by
      rw [hu_def, hu_def, hu_def, ← add_div, ← add_div, ← hσ, div_self hcs.ne]
    have hu : u ∈ controlSimplex := ⟨fun j ↦ ⟨hu0 j, by
      fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
        linarith [hu0 0, hu0 1, hu0 2]⟩, hu1⟩
    refine ⟨u, hu, ?_⟩
    have hdu' := hdu u hu
    have hud : ∀ j, u j * d (vertex j) = l j / σ := fun j ↦ by
      rw [hu_def, hc]; field_simp [hdne j]
    have hdu_eq : d u = σ⁻¹ := by
      rw [hd u, Fin.sum_univ_three, hud, hud, hud, ← add_div, ← add_div, ← Fin.sum_univ_three l,
        hl1, one_div]
    rw [hf]
    dsimp only
    rw [ratio_eq_sum N d hN hdne u hdu'.ne]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hud, hdu_eq]
    congr 1
    field_simp [hcs.ne]
  refine ⟨subset_antisymm hsub1 (hS.trans hS'), ?_, ?_⟩
  · rw [subset_antisymm hsub1 (hS.trans hS')]
    exact convex_convexHull ℝ _
  -- the image is a triangle: `f(e₁) - f(e₂)` and `f(e₃) - f(e₂)` are linearly independent, so its
  -- affine hull is the plane
  have hmem : ∀ j, p j ∈ halfPlaneField x y '' controlSimplex := fun j ↦
    ⟨vertex j, by
      fin_cases j <;> refine ⟨fun i ↦ ?_, ?_⟩ <;> (try fin_cases i) <;> simp [vertex], hpv j⟩
  have hpa : ∀ j i, p j i = (d (vertex j))⁻¹ * N (vertex j) i := fun _ _ ↦ rfl
  have hN00 : N (vertex 0) 0 = y * (d (vertex 0) + 2 * y ^ 2) := by
    simp [hNdef, hddef, controlMatrix, vertex, -mul_eq_mul_left_iff]; ring
  have hN10 : N (vertex 1) 0 = y * d (vertex 1) := by
    simp [hNdef, hddef, controlMatrix, vertex, -mul_eq_mul_left_iff]
  have hN20 : N (vertex 2) 0 = y * d (vertex 2) := by
    simp [hNdef, hddef, controlMatrix, vertex, -mul_eq_mul_left_iff]
  have hN11 : N (vertex 1) 1 = 2 * y ^ 2 / √3 := by
    simp [hNdef, controlMatrix, vertex, -mul_eq_mul_left_iff]; ring
  have hN21 : N (vertex 2) 1 = -(2 * y ^ 2 / √3) := by
    simp [hNdef, controlMatrix, vertex, -mul_eq_mul_left_iff]; ring
  have hsum12 : d (vertex 1) + d (vertex 2) = -4 / 3 := by rw [hd1, hd2]; ring
  set v₁ := p 0 - p 1 with hv₁
  set v₂ := p 2 - p 1 with hv₂
  have hv₁0 : v₁ 0 ≠ 0 := by
    have e : v₁ 0 = 2 * y ^ 3 / d (vertex 0) := by
      rw [hv₁, Pi.sub_apply, hpa, hpa, hN00, hN10]
      field_simp [hdne 0, hdne 1]
      ring
    rw [e]
    exact div_ne_zero (by positivity) (hdne 0)
  have hv₂0 : v₂ 0 = 0 := by
    rw [hv₂, Pi.sub_apply, hpa, hpa, hN20, hN10]
    field_simp [hdne 1, hdne 2]
    ring
  have hv₂1 : v₂ 1 ≠ 0 := by
    have e : v₂ 1 = -(2 * y ^ 2 / √3) * (d (vertex 1) + d (vertex 2)) /
        (d (vertex 1) * d (vertex 2)) := by
      rw [hv₂, Pi.sub_apply, hpa, hpa, hN21, hN11]
      field_simp [hdne 1, hdne 2]
      ring
    rw [e, hsum12]
    exact div_ne_zero (mul_ne_zero (neg_ne_zero.2 (by positivity)) (by norm_num))
      (mul_ne_zero (hdne 1) (hdne 2))
  rw [AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ (Fin 2 → ℝ)
    (Fin 2 → ℝ) ⟨_, hmem 0⟩,
    eq_top_iff]
  intro w _
  have h₁ : v₁ ∈ vectorSpan ℝ (halfPlaneField x y '' controlSimplex) :=
    vsub_mem_vectorSpan ℝ (hmem 0) (hmem 1)
  have h₂ : v₂ ∈ vectorSpan ℝ (halfPlaneField x y '' controlSimplex) :=
    vsub_mem_vectorSpan ℝ (hmem 2) (hmem 1)
  have hw : w = (w 0 / v₁ 0) • v₁ + ((w 1 - w 0 / v₁ 0 * v₁ 1) / v₂ 1) • v₂ := by
    funext i
    fin_cases i
    · simp [hv₂0, hv₁0]
    · simp only [Fin.mk_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring
  rw [hw]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ h₁) (Submodule.smul_mem _ _ h₂)

/-- **Definition 6.2.1** (`def:normal-abonormal-singular-extremals`), (1): an abnormal extremal is
an extremal with `λ_cost = 0`. -/
def IsAbnormalExtremal (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X Λ₁ ΛR : ℝ → Mat2) (lam : ℝ) : Prop :=
  IsPontryaginExtremal T u g X Λ₁ ΛR lam ∧ lam = 0

/-- **Definition 6.2.1**, (2): a normal extremal is an extremal with `λ_cost ≠ 0`. -/
def IsNormalExtremal (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X Λ₁ ΛR : ℝ → Mat2) (lam : ℝ) : Prop :=
  IsPontryaginExtremal T u g X Λ₁ ΛR lam ∧ lam ≠ 0

/-- **Definition 6.2.1**, (3): the lifted trajectory is a singular subarc on the open interval
`(a, b)` if at every time of the interval the maximization of the Hamiltonian over `U_T` does not
determine the control uniquely. -/
def IsSingularSubarc (lam : ℝ) (Λ₁ ΛR X : ℝ → Mat2) (a b : ℝ) : Prop :=
  a < b ∧ ∀ t ∈ Set.Ioo a b, ∃ v ∈ controlSimplex, ∃ w ∈ controlSimplex, v ≠ w ∧
    (∀ v' ∈ controlSimplex, hamiltonian lam (Λ₁ t) (ΛR t) (X t) v' ≤
      hamiltonian lam (Λ₁ t) (ΛR t) (X t) v) ∧
    ∀ v' ∈ controlSimplex, hamiltonian lam (Λ₁ t) (ΛR t) (X t) v' ≤
      hamiltonian lam (Λ₁ t) (ΛR t) (X t) w

/-- The Hamiltonian before the reduction `Λ_R = [Λ₂, X]` (§6.4):
`H(Λ₁, Λ₂, X; Z_u) = ⟨Λ₁ - (3/2) λ_cost J, X⟩ + ⟨Λ₂, [Z_u, X]⟩ / ⟨X, Z_u⟩`. -/
noncomputable def fullHamiltonian (lam : ℝ) (Λ₁ Λ₂ X : Mat2) (u : Fin 3 → ℝ) : ℝ :=
  traceForm (Λ₁ - (3 / 2 * lam) • J) X +
    traceForm Λ₂ (controlMatrix u * X - X * controlMatrix u) / traceForm X (controlMatrix u)

/-- The right-hand side `[P, Λ_R] - ⟨Λ_R, P⟩[P, X] + [-Λ₁ + (3/2) λ_cost J, X]` of the costate
equation for `Λ_R` (`eqn:lamR`), with `P = Z_u/⟨Z_u, X⟩`. -/
noncomputable def costateRHS (lam : ℝ) (Λ₁ ΛR X : Mat2) (u : Fin 3 → ℝ) : Mat2 :=
  (controlP u X * ΛR - ΛR * controlP u X) -
      traceForm ΛR (controlP u X) • (controlP u X * X - X * controlP u X) +
    ((-Λ₁ + (3 / 2 * lam) • J) * X - X * (-Λ₁ + (3 / 2 * lam) • J))

/-! ### Functional derivatives on `𝔰𝔩₂(ℝ)` -/

/-- The trace form is symmetric. -/
private theorem traceForm_comm (A B : Mat2) : traceForm A B = traceForm B A :=
  Matrix.trace_mul_comm A B

/-- The trace form is nondegenerate on `𝔰𝔩₂(ℝ)`: a traceless matrix is determined by its trace
form with the traceless matrices. Hence functional derivatives are unique. -/
private theorem eq_of_traceForm_eq {D D' : Mat2} (hD : D.trace = 0) (hD' : D'.trace = 0)
    (h : ∀ W : Mat2, W.trace = 0 → traceForm W D = traceForm W D') : D = D' := by
  have h1 := h !![0, 1; 0, 0] (by simp [Matrix.trace_fin_two])
  have h2 := h !![0, 0; 1, 0] (by simp [Matrix.trace_fin_two])
  have h3 := h !![1, 0; 0, -1] (by simp [Matrix.trace_fin_two])
  simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at h1 h2 h3
  rw [Matrix.trace_fin_two] at hD hD'
  ext i j
  fin_cases i <;> fin_cases j <;> simp at h1 h2 h3 ⊢ <;> linarith

/-- Two functional derivatives of the same function at the same point agree. -/
private theorem HasFunctionalDerivative.unique {F : Mat2 → ℝ} {X D D' : Mat2}
    (h : HasFunctionalDerivative F X D) (h' : HasFunctionalDerivative F X D') : D = D' :=
  eq_of_traceForm_eq h.1 h'.1 fun W hW ↦ (h.2 W hW).unique (h'.2 W hW)

/-- An affine function of `s` has derivative its slope. -/
private theorem hasDerivAt_affine (a b : ℝ) : HasDerivAt (fun s : ℝ ↦ a + s * b) b 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const b).const_add a

/-- The quotient rule for two affine functions of `s`, at `s = 0`. -/
private theorem hasDerivAt_affine_div (a b c d : ℝ) (hc : c ≠ 0) :
    HasDerivAt (fun s : ℝ ↦ (a + s * b) / (c + s * d)) ((b * c - a * d) / c ^ 2) 0 := by
  simpa using (hasDerivAt_affine a b).fun_div (hasDerivAt_affine c d) (by simpa using hc)

/-- **Proposition 6.5.1** (`eqn:lamR`, Lie algebra costate variables). Along a lifted trajectory
satisfying Hamilton's equations for the Hamiltonian `H(Λ₁, Λ₂, X; Z_u)` in the trivialized
cotangent bundle, `X' = δH/δΛ₂` and `Λ₂' = -δH/δX` (canonical equations on `T*𝔰𝔩₂(ℝ)`), and the
Euler–Arnold equation `Λ₁' = -ad_{δH/δΛ₁} Λ₁` (cited from Cushman–Bates), the costate variables
evolve as `Λ₁' = [Λ₁, X]` and `Λ_R' = [P, Λ_R] - ⟨Λ_R, P⟩[P, X] + [-Λ₁ + (3/2) λ_cost J, X]`, where
`P = Z_u/⟨X, Z_u⟩` and `Λ_R = [Λ₂, X]`. The control `u` is the value of the control at time `t`. -/
theorem proposition6_5_1 (lam : ℝ) (u : Fin 3 → ℝ) (X Λ₁ Λ₂ : ℝ → Mat2) (t : ℝ)
    (X' Λ₁' Λ₂' D₁ : Mat2)
    (htr : (X t).trace = 0 ∧ (Λ₁ t).trace = 0 ∧ (Λ₂ t).trace = 0)
    (hden : traceForm (X t) (controlMatrix u) ≠ 0)
    (hX : HasDerivAtEntrywise X X' t)
    (hΛ₂ : HasDerivAtEntrywise Λ₂ Λ₂' t)
    (hHΛ₂ : HasFunctionalDerivative (fun L ↦ fullHamiltonian lam (Λ₁ t) L (X t) u) (Λ₂ t) X')
    (hHX : HasFunctionalDerivative (fun Y ↦ fullHamiltonian lam (Λ₁ t) (Λ₂ t) Y u) (X t) (-Λ₂'))
    (hHΛ₁ : HasFunctionalDerivative (fun L ↦ fullHamiltonian lam L (Λ₂ t) (X t) u) (Λ₁ t) D₁)
    (hEA : Λ₁' = -(D₁ * Λ₁ t - Λ₁ t * D₁)) :
    Λ₁' = Λ₁ t * X t - X t * Λ₁ t ∧
      HasDerivAtEntrywise (fun s ↦ Λ₂ s * X s - X s * Λ₂ s)
        (costateRHS lam (Λ₁ t) (Λ₂ t * X t - X t * Λ₂ t) (X t) u) t := by
  obtain ⟨hXtr, hΛ₁tr, hΛ₂tr⟩ := htr
  set Z := controlMatrix u with hZdef
  set P := controlP u (X t) with hPdef
  set M := Λ₁ t - (3 / 2 * lam) • J with hMdef
  have hZtr : Z.trace = 0 := by
    simp [hZdef, controlMatrix, Matrix.trace_fin_two]; ring
  have hJtr : J.trace = 0 := by simp [J, Matrix.trace_fin_two]
  have hPZ : P = (traceForm Z (X t))⁻¹ • Z := rfl
  have hPtr : P.trace = 0 := by rw [hPZ, Matrix.trace_smul, hZtr, smul_zero]
  have hcomm_tr : ∀ A B : Mat2, (A * B - B * A).trace = 0 := fun A B ↦ by
    rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
  -- `δH/δΛ₂ = [P, X]`
  have hdΛ₂ : HasFunctionalDerivative (fun L ↦ fullHamiltonian lam (Λ₁ t) L (X t) u) (Λ₂ t)
      (P * X t - X t * P) := by
    refine ⟨hcomm_tr P (X t), fun W _ ↦ ?_⟩
    have e : (fun s : ℝ ↦ fullHamiltonian lam (Λ₁ t) (Λ₂ t + s • W) (X t) u) = fun s ↦
        traceForm M (X t) + (traceForm (Λ₂ t) (Z * X t - X t * Z) +
          s * traceForm W (Z * X t - X t * Z)) / (traceForm (X t) Z + s * 0) := by
      funext s
      simp [fullHamiltonian, traceForm, Matrix.add_mul, Matrix.trace_add, Matrix.trace_smul,
        hMdef, hZdef]
    rw [e]
    convert (hasDerivAt_affine_div _ _ _ _ hden).const_add (traceForm M (X t)) using 1
    rw [hPZ, traceForm_comm Z (X t)]
    simp only [traceForm, Matrix.smul_mul, Matrix.mul_smul, ← smul_sub, Matrix.trace_smul,
      smul_eq_mul, mul_zero, sub_zero]
    field_simp
  -- `δH/δΛ₁ = X`
  have hdΛ₁ : HasFunctionalDerivative (fun L ↦ fullHamiltonian lam L (Λ₂ t) (X t) u) (Λ₁ t)
      (X t) := by
    refine ⟨hXtr, fun W _ ↦ ?_⟩
    have e : (fun s : ℝ ↦ fullHamiltonian lam (Λ₁ t + s • W) (Λ₂ t) (X t) u) = fun s ↦
        (traceForm M (X t) + s * traceForm W (X t)) +
          traceForm (Λ₂ t) (Z * X t - X t * Z) / traceForm (X t) Z := by
      funext s
      simp only [fullHamiltonian, traceForm, hMdef, hZdef]
      rw [show Λ₁ t + s • W - (3 / 2 * lam) • J = (Λ₁ t - (3 / 2 * lam) • J) + s • W by abel,
        Matrix.add_mul, Matrix.trace_add, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    rw [e]
    exact (hasDerivAt_affine _ _).add_const _
  -- `δH/δX = Λ₁ - (3/2)λJ + [Λ₂, P] - ⟨[Λ₂, P], X⟩P`
  have hdX : HasFunctionalDerivative (fun Y ↦ fullHamiltonian lam (Λ₁ t) (Λ₂ t) Y u) (X t)
      (M + (Λ₂ t * P - P * Λ₂ t) - traceForm (Λ₂ t * P - P * Λ₂ t) (X t) • P) := by
    refine ⟨?_, fun W _ ↦ ?_⟩
    · rw [Matrix.trace_sub, Matrix.trace_add, hcomm_tr, Matrix.trace_smul, hPtr, hMdef,
        Matrix.trace_sub, Matrix.trace_smul, hJtr, hΛ₁tr]
      simp
    have e : (fun s : ℝ ↦ fullHamiltonian lam (Λ₁ t) (Λ₂ t) (X t + s • W) u) = fun s ↦
        (traceForm M (X t) + s * traceForm M W) +
          (traceForm (Λ₂ t) (Z * X t - X t * Z) + s * traceForm (Λ₂ t) (Z * W - W * Z)) /
            (traceForm (X t) Z + s * traceForm W Z) := by
      funext s
      simp [fullHamiltonian, traceForm, Matrix.add_mul, Matrix.mul_add, Matrix.trace_add,
        Matrix.trace_smul, Matrix.mul_sub, Matrix.trace_sub, hMdef, hZdef]
      ring
    rw [e]
    convert (hasDerivAt_affine _ _).add (hasDerivAt_affine_div _ _ _ _ hden) using 1
    rw [hPZ, traceForm_comm Z (X t)]
    have hden' := hden
    simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at hden' ⊢
    field_simp
    ring
  -- uniqueness of the functional derivatives
  have hX' : X' = P * X t - X t * P := hHΛ₂.unique hdΛ₂
  have hD₁ : D₁ = X t := hHΛ₁.unique hdΛ₁
  have hΛ₂' : -Λ₂' = M + (Λ₂ t * P - P * Λ₂ t) - traceForm (Λ₂ t * P - P * Λ₂ t) (X t) • P :=
    hHX.unique hdX
  refine ⟨by rw [hEA, hD₁]; noncomm_ring, ?_⟩
  -- `Λ_R' = [Λ₂', X] + [Λ₂, X']`
  refine (((hΛ₂.mul hX).sub (hX.mul hΛ₂))).congr_deriv ?_
  have hκ : traceForm (Λ₂ t * P - P * Λ₂ t) (X t) =
      -traceForm (Λ₂ t * X t - X t * Λ₂ t) P := by
    simp only [traceForm, Matrix.sub_mul, Matrix.trace_sub]
    rw [Matrix.trace_mul_cycle (Λ₂ t) (X t) P, Matrix.trace_mul_cycle (X t) (Λ₂ t) P,
      Matrix.trace_mul_cycle P (X t) (Λ₂ t)]
    ring
  have hΛ₂'' : Λ₂' = -M - (Λ₂ t * P - P * Λ₂ t) -
      traceForm (Λ₂ t * X t - X t * Λ₂ t) P • P := by
    rw [← neg_neg Λ₂', hΛ₂', hκ, neg_smul]; abel
  have hM : -Λ₁ t + (3 / 2 * lam) • J = -M := by rw [hMdef]; abel
  unfold costateRHS
  rw [← hPdef, hM, hX', hΛ₂'']
  generalize traceForm (Λ₂ t * X t - X t * Λ₂ t) P = κ
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_assoc, smul_sub]
  abel

/-- **Corollary 6.5.3** (`cor:lam1-gen-sol`, Jurdjevic). If `g' = gX` with `g(0) = I₂` and
`g(t) ∈ SL₂(ℝ)`, and `Λ₁' = [Λ₁, X]` (a Lax equation), then `Λ₁` evolves in an adjoint orbit:
`Λ₁(t) = Ad_{g(t)⁻¹} Λ₁(0) = g(t)⁻¹ Λ₁(0) g(t)`; in particular `det Λ₁(t)` is constant. -/
theorem corollary6_5_3 (T : ℝ) (g X Λ₁ : ℝ → Mat2)
    (hg : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAtEntrywise g (g t * X t) (Set.Icc 0 T) t)
    (hg0 : g 0 = 1) (hdet : ∀ t ∈ Set.Icc 0 T, (g t).det = 1)
    (hΛ : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAtEntrywise Λ₁ (Λ₁ t * X t - X t * Λ₁ t) (Set.Icc 0 T) t) :
    ∀ t ∈ Set.Icc 0 T, Λ₁ t = (g t)⁻¹ * Λ₁ 0 * g t ∧ (Λ₁ t).det = (Λ₁ 0).det := by
  have hunit : ∀ t ∈ Set.Icc 0 T, IsUnit (g t).det := fun t ht ↦ by
    rw [hdet t ht]; exact isUnit_one
  -- differentiating: `(g Λ₁ g⁻¹)' = gXΛ₁g⁻¹ + g[Λ₁, X]g⁻¹ - gΛ₁g⁻¹(gX)g⁻¹ = 0`
  have hM : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAtEntrywise (fun s ↦ g s * Λ₁ s * (g s)⁻¹) 0 (Set.Icc 0 T) t := by
    intro t ht
    refine (((hg t ht).mul (hΛ t ht)).mul ((hg t ht).inv (hunit t ht))).congr_deriv ?_
    have h1 : (g t)⁻¹ * (g t * X t) * (g t)⁻¹ = X t * (g t)⁻¹ := by
      rw [← Matrix.mul_assoc, nonsing_inv_mul _ (hunit t ht), Matrix.one_mul]
    rw [h1]
    noncomm_ring
  -- so `g Λ₁ g⁻¹` is constant, equal to its value `Λ₁(0)` at `0`
  have hconst := constant_of_hasDerivWithinAtEntrywise_Icc_zero
    (HasDerivWithinAtEntrywise.continuousOn hM) (fun t ht ↦ hM t (Set.Ico_subset_Icc_self ht))
  intro t ht
  have h0 : g 0 * Λ₁ 0 * (g 0)⁻¹ = Λ₁ 0 := by simp [hg0]
  have hM' : g t * Λ₁ t * (g t)⁻¹ = Λ₁ 0 := (hconst t ht).trans h0
  have hΛt : Λ₁ t = (g t)⁻¹ * Λ₁ 0 * g t := by
    rw [← hM']
    simp only [Matrix.mul_assoc, nonsing_inv_mul _ (hunit t ht), Matrix.mul_one]
    rw [← Matrix.mul_assoc, nonsing_inv_mul _ (hunit t ht), Matrix.one_mul]
  -- the determinant is invariant under conjugation
  refine ⟨hΛt, ?_⟩
  rw [hΛt, det_mul, det_mul, det_nonsing_inv, hdet t ht]
  simp

/-- The trace form is linear in its second argument along a line. -/
private theorem hasDerivAt_traceForm_line (A Z W : Mat2) :
    HasDerivAt (fun s : ℝ ↦ traceForm A (Z + s • W)) (traceForm A W) 0 := by
  have e : (fun s : ℝ ↦ traceForm A (Z + s • W)) =
      fun s ↦ traceForm A Z + s * traceForm A W := by
    funext s
    simp [traceForm, Matrix.mul_add, Matrix.trace_add, Matrix.trace_smul]
  rw [e]
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (traceForm A W)).const_add (traceForm A Z)

/-- **Corollary 6.5.4** (`cor:control-dep-ad-alternate`). The control-dependent term of the
costate equation for `Λ_R` is
`[P, Λ_R] - (⟨Λ_R, Z_u⟩/⟨X, Z_u⟩)[P, X] = ad_{Z_u} δ/δZ_u (⟨Λ_R, Z_u⟩/⟨X, Z_u⟩)`; the functional
derivative is `(⟨X, Z_u⟩ Λ_R - ⟨Λ_R, Z_u⟩ X)/⟨X, Z_u⟩²`. -/
theorem corollary6_5_4 (ΛR X Z : Mat2) (hΛ : ΛR.trace = 0) (hX : X.trace = 0)
    (hXZ : traceForm X Z ≠ 0) :
    HasFunctionalDerivative (fun W ↦ traceForm ΛR W / traceForm X W) Z
        ((traceForm X Z ^ 2)⁻¹ • (traceForm X Z • ΛR - traceForm ΛR Z • X)) ∧
      Z * ((traceForm X Z ^ 2)⁻¹ • (traceForm X Z • ΛR - traceForm ΛR Z • X)) -
          ((traceForm X Z ^ 2)⁻¹ • (traceForm X Z • ΛR - traceForm ΛR Z • X)) * Z =
        ((traceForm X Z)⁻¹ • Z * ΛR - ΛR * (traceForm X Z)⁻¹ • Z) -
          (traceForm ΛR Z / traceForm X Z) •
            ((traceForm X Z)⁻¹ • Z * X - X * (traceForm X Z)⁻¹ • Z) := by
  refine ⟨⟨?_, fun W _ ↦ ?_⟩, ?_⟩
  · -- the functional derivative is traceless
    simp [Matrix.trace_smul, Matrix.trace_sub, hΛ, hX]
  · -- quotient rule for the directional derivative
    have h := (hasDerivAt_traceForm_line ΛR Z W).fun_div (hasDerivAt_traceForm_line X Z W)
      (by simpa using hXZ)
    convert h using 1
    simp only [zero_smul, add_zero]
    rw [traceForm_comm ΛR W, traceForm_comm X W]
    simp only [traceForm, Matrix.mul_smul, Matrix.mul_sub, Matrix.trace_smul, Matrix.trace_sub,
      smul_eq_mul]
    field_simp
  · -- the bracket `[Z_u, δ/δZ_u (⟨Λ_R, Z_u⟩/⟨X, Z_u⟩)]`
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, smul_sub,
      smul_smul]
    have h1 : (traceForm X Z ^ 2)⁻¹ * traceForm X Z = (traceForm X Z)⁻¹ := by
      field_simp
    have h2 : (traceForm X Z ^ 2)⁻¹ * traceForm ΛR Z =
        traceForm ΛR Z / traceForm X Z * (traceForm X Z)⁻¹ := by
      field_simp
    rw [h1, h2]
    abel

end SmoothedPolygons
