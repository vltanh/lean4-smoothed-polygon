module

public import SmoothedPolygons.Ch6.Hamiltonian
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Algebra.Polynomial.Roots
public import Basic.Analysis.Calculus.MatrixEntrywiseExp
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import SmoothedPolygons.Ch3.LieAlgebraDynamics
public import SmoothedPolygons.AppA.Riemannian

/-!
# Solutions for constant control (§7.1, §7.2)

For a constant control `u`, `⟨X, Z_u⟩` is a constant of motion (Lemma 7.1.1), the speed of `X` is
constant (Lemma 7.1.2), the state equations are solved by matrix exponentials
(`eqn:const-control-g`, `eqn:const-control-z-X`), `P₀` and `X₀ + P₀` have the same characteristic
polynomial (Lemma 7.1.3), and for a vertex control the trajectories in the star domain are arcs of
generalized circles (Lemma 7.2.1).
-/

@[expose] public section

namespace SmoothedPolygons

open Matrix

/-- **Lemma 7.1.1** (`cor:X-det-const`). For a fixed control matrix `Z_u`, `⟨X, Z_u⟩` is a constant
of motion along `X' = [Z_u, X]/⟨Z_u, X⟩`. -/
theorem lemma7_1_1 (u : Fin 3 → ℝ) (X : ℝ → Mat2) (a b : ℝ)
    (hX : ∀ t ∈ Set.Icc a b, HasDerivWithinAtEntrywise X
      (controlP u (X t) * X t - X t * controlP u (X t)) (Set.Icc a b) t) :
    ∀ t ∈ Set.Icc a b, traceForm (X t) (controlMatrix u) = traceForm (X a) (controlMatrix u) := by
  -- `⟨X, Z⟩' = ⟨X', Z⟩ = ⟨[Z, X], Z⟩/⟨X, Z⟩ = 0`
  have hd : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt (fun s ↦ traceForm (X s) (controlMatrix u)) 0 (Set.Icc a b) t := by
    intro t ht
    have h := ((hX t ht).mul_const (controlMatrix u)).trace
    unfold traceForm
    convert h using 1
    unfold controlP
    simp only [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub, Matrix.trace_smul,
      Matrix.sub_mul, Matrix.trace_sub]
    rw [Matrix.trace_mul_cycle (X t) (controlMatrix u) (controlMatrix u), sub_self, smul_zero]
  intro t ht
  refine constant_of_has_deriv_right_zero (fun s hs ↦ (hd s hs).continuousWithinAt)
    (fun s hs ↦ (hd s (Set.Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin ?_) t ht
  exact Filter.mem_of_superset (Icc_mem_nhdsGE hs.2) (Set.Icc_subset_Icc_left hs.1)

/-- The chain rule for `t ↦ Φ(x(t), y(t))`: its derivative is the image `[Y_z(x', y'), Φ(z)]` of
the velocity `(x', y')` under the tangent map of `Φ` (Lemma 4.2.4). -/
private theorem hasDerivWithinAt_Φ_comp {x y : ℝ → ℝ} {x' y' : ℝ} {s : Set ℝ} {t : ℝ}
    (hy0 : 0 < y t) (hx : HasDerivWithinAt x x' s t) (hy : HasDerivWithinAt y y' s t) :
    HasDerivWithinAtEntrywise (fun τ ↦ Φ (x τ) (y τ))
      (tangentLift (x t) (y t) x' y' * Φ (x t) (y t) -
        Φ (x t) (y t) * tangentLift (x t) (y t) x' y') s t := by
  intro i j
  -- the entries of `Φ` are differentiable functions of `(x, y)` on the upper half-plane
  have hd : DifferentiableAt ℝ (fun p : ℝ × ℝ ↦ Φ p.1 p.2 i j) (x t, y t) := by
    have hy0' : y t ≠ 0 := hy0.ne'
    fin_cases i <;> fin_cases j <;>
      simp only [Φ, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] <;>
      fun_prop (disch := simpa using hy0')
  -- by Lemma 4.2.4, the derivative in the direction `(x', y')` is the entry of `[Y_z(x', y'), Φ]`
  have hline : HasDerivAt (fun σ : ℝ ↦ Φ (x t + σ * x') (y t + σ * y') i j)
      (fderiv ℝ (fun p : ℝ × ℝ ↦ Φ p.1 p.2 i j) (x t, y t) (x', y')) 0 := by
    have h1 : HasDerivAt (fun σ : ℝ ↦ x t + σ * x') x' 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const x').const_add (x t)
    have h2 : HasDerivAt (fun σ : ℝ ↦ y t + σ * y') y' 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const y').const_add (y t)
    exact hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 (h1.prodMk h2) (by simp)
  rw [← hline.unique (lemma4_2_4 (x t) (y t) x' y' hy0 i j)]
  exact hd.hasFDerivAt.comp_hasDerivWithinAt t (hx.prodMk hy)

/-- **Lemma 7.1.2** (`lem:Riemannian-speed`). For a constant control `u ∈ U_T`, the speed
`⟨X', X'⟩^{1/2}` of `X` is constant, and the trajectory `z = x + iy` with `X = Φ(z)` has constant
speed `(x'² + y'²)^{1/2}/y` for the invariant Riemannian metric of the upper half-plane. -/
theorem lemma7_1_2 (u : Fin 3 → ℝ) (hu : u ∈ controlSimplex) (X : ℝ → Mat2) (a b : ℝ)
    (hstar : ∀ t ∈ Set.Icc a b, IsStarState (X t))
    (hX : ∀ t ∈ Set.Icc a b, HasDerivWithinAtEntrywise X
      (controlP u (X t) * X t - X t * controlP u (X t)) (Set.Icc a b) t) :
    (∀ t ∈ Set.Icc a b,
      traceForm (controlP u (X t) * X t - X t * controlP u (X t))
          (controlP u (X t) * X t - X t * controlP u (X t)) =
        traceForm (controlP u (X a) * X a - X a * controlP u (X a))
          (controlP u (X a) * X a - X a * controlP u (X a))) ∧
      ∀ x y x' y' : ℝ → ℝ, (∀ t ∈ Set.Icc a b, X t = Φ (x t) (y t) ∧ 0 < y t ∧
          HasDerivWithinAt x (x' t) (Set.Icc a b) t ∧ HasDerivWithinAt y (y' t) (Set.Icc a b) t) →
        ∀ t ∈ Set.Icc a b, (x' t ^ 2 + y' t ^ 2) / y t ^ 2 = (x' a ^ 2 + y' a ^ 2) / y a ^ 2 := by
  -- `P = Z_u/⟨X, Z_u⟩` is constant (Lemma 7.1.1)
  have hP : ∀ t ∈ Set.Icc a b, controlP u (X t) = controlP u (X a) := fun t ht ↦ by
    unfold controlP
    rw [traceForm, Matrix.trace_mul_comm, ← traceForm, lemma7_1_1 u X a b hX t ht, traceForm,
      Matrix.trace_mul_comm, ← traceForm]
  -- the speed `⟨X', X'⟩` is constant: `⟨X', X'⟩' = 2⟨[P, X'], X'⟩ = 2⟨P, [X', X']⟩ = 0`
  have hspeed : ∀ t ∈ Set.Icc a b,
      traceForm (controlP u (X t) * X t - X t * controlP u (X t))
          (controlP u (X t) * X t - X t * controlP u (X t)) =
        traceForm (controlP u (X a) * X a - X a * controlP u (X a))
          (controlP u (X a) * X a - X a * controlP u (X a)) := by
    intro t ht
    set P := controlP u (X a)
    -- `X' = [P, X]`, so `X'' = [P, X']`
    have hX' : ∀ s ∈ Set.Icc a b, HasDerivWithinAtEntrywise (fun τ ↦ P * X τ - X τ * P)
        (P * (P * X s - X s * P) - (P * X s - X s * P) * P) (Set.Icc a b) s := fun s hs ↦ by
      have h := ((hX s hs).const_mul P).sub ((hX s hs).mul_const P)
      rwa [hP s hs] at h
    have hd : ∀ s ∈ Set.Icc a b, HasDerivWithinAt
        (fun τ ↦ ((P * X τ - X τ * P) * (P * X τ - X τ * P)).trace) 0 (Set.Icc a b) s := by
      intro s hs
      convert ((hX' s hs).mul (hX' s hs)).trace using 1
      generalize P * X s - X s * P = V
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_add]
      rw [← Matrix.mul_assoc V V P, Matrix.trace_mul_cycle V V P, ← Matrix.mul_assoc V P V]
      ring
    have hc := constant_of_has_deriv_right_zero (fun s hs ↦ (hd s hs).continuousWithinAt)
      (fun s hs ↦ (hd s (Set.Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
        (Filter.mem_of_superset (Icc_mem_nhdsGE hs.2) (Set.Icc_subset_Icc_left hs.1))) t ht
    rw [hP t ht]
    exact hc
  refine ⟨hspeed, fun x y x' y' hxy t ht ↦ ?_⟩
  -- the trajectory `z` has constant speed `(x'² + y'²)^{1/2}/y` (Lemma A.11.1)
  rcases eq_or_lt_of_le (ht.1.trans ht.2) with hab | hab
  · obtain rfl : t = a := le_antisymm (hab ▸ ht.2) ht.1
    rfl
  -- `X' = [Y_z(x', y'), X]` by the chain rule and Lemma 4.2.4
  have hlift : ∀ s ∈ Set.Icc a b,
      traceForm (controlP u (X s) * X s - X s * controlP u (X s))
          (controlP u (X s) * X s - X s * controlP u (X s)) =
        2 * (x' s * x' s + y' s * y' s) / y s ^ 2 := by
    intro s hs
    obtain ⟨hXs, hys, hxs, hys'⟩ := hxy s hs
    have h1 := hasDerivWithinAt_Φ_comp hys hxs hys'
    have h2 : HasDerivWithinAtEntrywise (fun τ ↦ Φ (x τ) (y τ))
        (controlP u (X s) * X s - X s * controlP u (X s)) (Set.Icc a b) s :=
      (hX s hs).congr (fun τ hτ ↦ ((hxy τ hτ).1).symm) hXs.symm
    rw [h2.unique (uniqueDiffOn_Icc hab s hs) h1, lemmaA_11_1 _ _ _ _ _ _ hys]
  have h := hspeed t ht
  rw [hlift t ht, hlift a (Set.left_mem_Icc.2 hab.le)] at h
  have hyt := (hxy t ht).2.1
  have hya := (hxy a (Set.left_mem_Icc.2 hab.le)).2.1
  field_simp at h ⊢
  linarith

/-- The general solution `g(t) = exp(t(X₀ + P₀)) exp(-tP₀)` of the state equation for `g` with
constant control (`eqn:const-control-g`), `P₀ = Z_u/⟨Z_u, X₀⟩`. -/
noncomputable def constControlG (X₀ P₀ : Mat2) (t : ℝ) : Mat2 :=
  NormedSpace.exp (t • (X₀ + P₀)) * NormedSpace.exp (-t • P₀)

/-- The general solution `X(t) = exp(tP₀) X₀ exp(-tP₀) = Ad_{exp(tP₀)} X₀` of the state equation
for `X` with constant control (`eqn:const-control-z-X`). -/
noncomputable def constControlX (X₀ P₀ : Mat2) (t : ℝ) : Mat2 :=
  NormedSpace.exp (t • P₀) * X₀ * NormedSpace.exp (-t • P₀)

/-- The general solutions for constant control (`eqn:const-control-g`, `eqn:const-control-z-X`):
with `P₀ = Z_u/⟨Z_u, X₀⟩`, `g(t) = exp(t(X₀ + P₀)) exp(-tP₀)` and `X(t) = exp(tP₀) X₀ exp(-tP₀)`
solve `g' = gX`, `X' = [Z_u, X]/⟨Z_u, X⟩` with `g(0) = I₂`, `X(0) = X₀`. -/
theorem constControl_solution (u : Fin 3 → ℝ) (X₀ : Mat2) (hX₀ : X₀.trace = 0)
    (hden : traceForm (controlMatrix u) X₀ ≠ 0) (t : ℝ) :
    HasDerivAtEntrywise (constControlG X₀ (controlP u X₀))
        (constControlG X₀ (controlP u X₀) t * constControlX X₀ (controlP u X₀) t) t ∧
      HasDerivAtEntrywise (constControlX X₀ (controlP u X₀))
        (controlP u (constControlX X₀ (controlP u X₀) t) * constControlX X₀ (controlP u X₀) t -
          constControlX X₀ (controlP u X₀) t * controlP u (constControlX X₀ (controlP u X₀) t)) t ∧
      constControlG X₀ (controlP u X₀) 0 = 1 ∧ constControlX X₀ (controlP u X₀) 0 = X₀ := by
  set Z := controlMatrix u
  set P := controlP u X₀ with hP
  have hPZ : P = (traceForm Z X₀)⁻¹ • Z := rfl
  -- `Z` commutes with `exp(sP₀)`, since `P₀` is a multiple of `Z`
  have hcomm : ∀ s : ℝ, Commute Z (NormedSpace.exp (s • P)) := fun s ↦ by
    rw [hPZ, smul_smul]
    exact commute_exp_smul Z _
  have hEF : ∀ s : ℝ, NormedSpace.exp (-s • P) * NormedSpace.exp (s • P) = 1 :=
    exp_neg_smul_mul_exp_smul P
  -- `⟨Z, X(t)⟩ = ⟨Z, X₀⟩`, so `P(t) = P₀`
  have hPt : controlP u (constControlX X₀ P t) = P := by
    have : traceForm Z (constControlX X₀ P t) = traceForm Z X₀ := by
      unfold traceForm constControlX
      have e : Z * (NormedSpace.exp (t • P) * X₀ * NormedSpace.exp (-t • P)) =
          Z * NormedSpace.exp (t • P) * X₀ * NormedSpace.exp (-t • P) := by
        simp only [Matrix.mul_assoc]
      rw [e, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← (hcomm (-t)).eq,
        Matrix.mul_assoc Z, hEF, Matrix.mul_one]
    unfold controlP
    rw [this]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `g' = exp(t(X₀+P₀))(X₀+P₀)exp(-tP₀) - g P₀ = g X`
    refine ((hasDerivAtEntrywise_exp_smul_const (X₀ + P) t).mul
      (hasDerivAtEntrywise_exp_neg_smul_const P t)).congr_deriv ?_
    unfold constControlG constControlX
    have h1 : NormedSpace.exp (-t • P) * P = P * NormedSpace.exp (-t • P) :=
      ((commute_exp_smul P (-t)).eq).symm
    have h2 : NormedSpace.exp (-t • P) * (NormedSpace.exp (t • P) * X₀ *
        NormedSpace.exp (-t • P)) = X₀ * NormedSpace.exp (-t • P) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hEF, Matrix.one_mul]
    have h3 : NormedSpace.exp (t • (X₀ + P)) * NormedSpace.exp (-t • P) *
        (NormedSpace.exp (t • P) * X₀ * NormedSpace.exp (-t • P)) =
        NormedSpace.exp (t • (X₀ + P)) * (X₀ * NormedSpace.exp (-t • P)) := by
      rw [Matrix.mul_assoc (NormedSpace.exp (t • (X₀ + P))), h2]
    rw [h3, h1]
    generalize NormedSpace.exp (t • (X₀ + P)) = A
    generalize NormedSpace.exp (-t • P) = B
    noncomm_ring
  · -- `X' = P₀ X - X P₀`
    rw [hPt]
    refine (((hasDerivAtEntrywise_exp_smul_const' P t).mul_const X₀).mul
      (hasDerivAtEntrywise_exp_neg_smul_const P t)).congr_deriv ?_
    unfold constControlX
    generalize NormedSpace.exp (t • P) = A
    generalize NormedSpace.exp (-t • P) = B
    noncomm_ring
  · simp [constControlG]
  · simp [constControlX]

/-- **Lemma 7.1.3** (unlabelled in the book; label `lem:P0-charpoly` here). With `det X₀ = 1` and
`P₀ = Z_u/⟨Z_u, X₀⟩`, the matrices `P₀` and `X₀ + P₀` have the same characteristic polynomial. If
`det Z_u < 0`, the eigenvalues are real: `±√(-det Z_u)/⟨X₀, Z_u⟩`. -/
theorem lemma7_1_3 (X₀ Z : Mat2) (hX : X₀.trace = 0) (hZ : Z.trace = 0) (hdet : X₀.det = 1)
    (hXZ : traceForm X₀ Z ≠ 0) :
    ((traceForm Z X₀)⁻¹ • Z).charpoly = (X₀ + (traceForm Z X₀)⁻¹ • Z).charpoly ∧
      (Z.det < 0 → ((traceForm Z X₀)⁻¹ • Z).charpoly.roots =
        {√(-Z.det) / traceForm X₀ Z, -(√(-Z.det) / traceForm X₀ Z)}) := by
  have hc : traceForm Z X₀ = traceForm X₀ Z := Matrix.trace_mul_comm Z X₀
  set P := (traceForm Z X₀)⁻¹ • Z with hP
  have hPtr : P.trace = 0 := by rw [hP, Matrix.trace_smul, hZ, smul_zero]
  have hXPtr : (X₀ + P).trace = 0 := by rw [Matrix.trace_add, hX, hPtr, add_zero]
  -- `⟨X₀, P₀⟩ = 1`
  have hXP : traceForm X₀ P = 1 := by
    rw [hP, traceForm, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, ← traceForm, hc,
      inv_mul_cancel₀ hXZ]
  -- `-2 det(X₀ + P₀) = ⟨X₀, X₀⟩ + 2⟨X₀, P₀⟩ + ⟨P₀, P₀⟩ = -2 det P₀`
  have hexp : traceForm (X₀ + P) (X₀ + P) =
      traceForm X₀ X₀ + 2 * traceForm X₀ P + traceForm P P := by
    simp only [traceForm, Matrix.add_mul, Matrix.mul_add, Matrix.trace_add]
    rw [Matrix.trace_mul_comm P X₀]
    ring
  have hdetXP : (X₀ + P).det = P.det := by
    have h := hexp
    rw [lemma3_4_1.1 _ hXPtr, lemma3_4_1.1 _ hX, lemma3_4_1.1 _ hPtr, hXP, hdet] at h
    linarith
  -- the characteristic polynomial of a traceless `2 × 2` matrix is `X² + det`
  refine ⟨by rw [charpoly_fin_two, charpoly_fin_two, hPtr, hXPtr, hdetXP], fun hZdet ↦ ?_⟩
  set r := √(-Z.det) / traceForm X₀ Z with hr
  have hPdet : P.det = -r ^ 2 := by
    rw [hP, Matrix.det_smul, hr, div_pow, Real.sq_sqrt (by linarith), hc]
    simp only [Fintype.card_fin, inv_pow]
    field_simp
  have hfac : P.charpoly =
      (Polynomial.X - Polynomial.C r) * (Polynomial.X - Polynomial.C (-r)) := by
    rw [charpoly_fin_two, hPtr, hPdet]
    simp only [map_neg, map_zero, zero_mul, sub_zero, map_pow]
    ring
  rw [hfac, Polynomial.roots_mul
    (mul_ne_zero (Polynomial.X_sub_C_ne_zero r) (Polynomial.X_sub_C_ne_zero (-r))),
    Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C, Multiset.singleton_add]
  rfl

/-- **Lemma 7.2.1** (`lem:const-control-trajectories`). If the control is constant at a vertex of
`U_T`, then the trajectories `z = x + iy` in the star domain are arcs of generalized circles
(`A(x² + y²) + Bx + Cy + D = 0` with `(A, B, C) ≠ 0`). If the control is `(0, 0, 1)` or
`(0, 1, 0)`, each trajectory moves along a Euclidean straight line (`A = 0`). -/
theorem lemma7_2_1 (i : Fin 3) (X : ℝ → Mat2) (x y : ℝ → ℝ) (a b : ℝ)
    (hX : ∀ t ∈ Set.Icc a b, HasDerivWithinAtEntrywise X
      (controlP (vertex i) (X t) * X t - X t * controlP (vertex i) (X t)) (Set.Icc a b) t)
    (hxy : ∀ t ∈ Set.Icc a b, X t = Φ (x t) (y t) ∧ (x t, y t) ∈ starDomain) :
    ∃ A B C D : ℝ, (A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0) ∧ (i ≠ 0 → A = 0) ∧
      ∀ t ∈ Set.Icc a b, A * (x t ^ 2 + y t ^ 2) + B * x t + C * y t + D = 0 := by
  sorry

end SmoothedPolygons
