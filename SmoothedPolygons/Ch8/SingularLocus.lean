module

public import SmoothedPolygons.Ch8.Defs
public import Basic.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import SmoothedPolygons.Ch7.Faces
public import SmoothedPolygons.Ch6.HalfPlane
public import SmoothedPolygons.Ch6.MatrixSystem

/-!
# Singular locus and singular subarcs (§8.2: Lemmas 8.2.1, 8.2.2, Theorems 8.2.3, 8.2.6)

* Lemma 8.2.1 (`lem:LambdaR`): if the control-dependent term `H₂ = -⟨Λ, Z_u⟩/⟨X, Z_u⟩` of the
  Hamiltonian does not depend on `u ∈ U_T` then `Λ = 0`; if `Λ ≠ 0` the maximizers form a vertex
  or an edge of `U_T`.
* Lemma 8.2.2 (`lem:Lambda1`): at a zero of `Λ_R` the costate equation for `Λ_R` has a continuous
  right-hand side, and if also `Λ_R' = 0` there, then `λ_cost ≠ 0` and `Λ₁ = (3/2) λ_cost J`.
* Theorem 8.2.3 (`thm:circle-singular`): if `Λ_R ≡ 0` on an interval, the trajectory is a circular
  arc with the centre control `(⅓, ⅓, ⅓)`: `X ≡ J`, `Λ₁ ≡ (3/2) λ_cost J`, `g = g₀ exp(Jt)`.
* Theorem 8.2.6 (`thm:circle-iff-singular`): a singular subarc on which the Hamiltonian does not
  depend on the control stays in the singular locus and is a circular arc, and conversely.

Notes on the statements:
* Lemma 8.2.1 is printed "for all `X ∈ 𝔰𝔩₂(ℝ)`", but `H₂` is defined only where
  `⟨X, Z_u⟩ ≠ 0` on `U_T` (E52); that is the hypothesis here (it holds on the state space by
  Lemma 3.3.4, and Lemma 7.3.1 has the same hypothesis). For `X = 0` the printed statement would
  be meaningless.
* The converse of Theorem 8.2.6 is argued in the book through necessary conditions only
  (E54); the formal statement exhibits the lift `λ_cost = -1`, `Λ₁ = -(3/2) J`, `Λ_R = 0`.
-/

@[expose] public section

namespace SmoothedPolygons

open Set MeasureTheory Filter Topology Matrix

/-! ### Extremal lifted trajectories on `[a, b]`, in the original time -/

/-- `f' = v` on `[a, b]` in integral form (Carathéodory's sense). -/
private abbrev l3f_IntForm (f v : ℝ → Mat2) (a b : ℝ) : Prop :=
  ∀ i j, IntervalIntegrable (fun s ↦ v s i j) volume a b ∧
    ∀ t ∈ Icc a b, f t i j = f a i j + ∫ s in a..t, v s i j

/-- An integral curve after the time shift `t ↦ a + t`, read in the original time. -/
private lemma l3f_unshift {f v : ℝ → Mat2} {a b : ℝ}
    (h : IsIntegralCurve (fun t ↦ f (a + t)) (fun t ↦ v (a + t)) (b - a)) :
    l3f_IntForm f v a b := by
  intro i j
  obtain ⟨hint, heq⟩ := h i j
  refine ⟨by simpa using hint.comp_sub_right a, fun t ht ↦ ?_⟩
  have h1 := heq (t - a) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h2 := intervalIntegral.integral_comp_add_left (fun s ↦ v s i j) a (a := 0) (b := t - a)
  simp only [add_zero, add_sub_cancel] at h1 h2
  rw [h1, h2]

/-- An almost-everywhere statement after the time shift `t ↦ a + t`, in the original time. -/
private lemma l3f_ae_unshift {p : ℝ → Prop} {a T : ℝ} (h : ∀ᵐ t, t ∈ Ioo 0 T → p (a + t)) :
    ∀ᵐ s, s ∈ Ioo a (a + T) → p s := by
  have hq := (measurePreserving_add_left volume (-a)).quasiMeasurePreserving.ae h
  filter_upwards [hq] with s hs hsI
  simpa using hs ⟨by linarith [hsI.1], by linarith [hsI.2]⟩

/-- The conditions of an extremal lifted trajectory on `[a, b]` (`IsExtremalOn`, which is written
after the time shift `t ↦ a + t`), in the original time. -/
private lemma l3f_data {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (h : IsExtremalOn a b u g X Λ₁ ΛR lam) :
    a < b ∧
      (∀ t ∈ Icc a b, u t ∈ controlSimplex ∧ (g t).det = 1 ∧ IsStarState (X t) ∧
        (Λ₁ t).trace = 0 ∧ (ΛR t).trace = 0 ∧ traceForm (ΛR t) (X t) = 0 ∧
        (lam ≠ 0 ∨ Λ₁ t ≠ 0 ∨ ΛR t ≠ 0)) ∧
      l3f_IntForm g (fun t ↦ g t * X t) a b ∧
      l3f_IntForm X (fun t ↦ controlP (u t) (X t) * X t - X t * controlP (u t) (X t)) a b ∧
      l3f_IntForm Λ₁ (fun t ↦ Λ₁ t * X t - X t * Λ₁ t) a b ∧
      l3f_IntForm ΛR (fun t ↦ costateRHS lam (Λ₁ t) (ΛR t) (X t) (u t)) a b ∧
      ∀ᵐ t, t ∈ Ioo a b → hamiltonian lam (Λ₁ t) (ΛR t) (X t) (u t) = 0 ∧
        ∀ v ∈ controlSimplex,
          hamiltonian lam (Λ₁ t) (ΛR t) (X t) v ≤ hamiltonian lam (Λ₁ t) (ΛR t) (X t) (u t) := by
  obtain ⟨⟨hT, -, hu, hst, hgI, hXI⟩, -, hco, hI1, hIR, hmax⟩ := h
  refine ⟨by linarith, fun t ht ↦ ?_, l3f_unshift hgI, l3f_unshift hXI, l3f_unshift hI1,
    l3f_unshift hIR, ?_⟩
  · have ht' : t - a ∈ Icc 0 (b - a) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have e : a + (t - a) = t := by ring
    have h1 := hu _ ht'
    have h2 := hst _ ht'
    have h3 := hco _ ht'
    simp only [e] at h1 h2 h3
    exact ⟨h1, h2.1, h2.2, h3⟩
  · have := l3f_ae_unshift (p := fun s ↦ hamiltonian lam (Λ₁ s) (ΛR s) (X s) (u s) = 0 ∧
      ∀ v ∈ controlSimplex,
        hamiltonian lam (Λ₁ s) (ΛR s) (X s) v ≤ hamiltonian lam (Λ₁ s) (ΛR s) (X s) (u s)) hmax
    rwa [add_sub_cancel] at this

/-- A real function tending to `L` at `t₀ ∈ [a, b]` within `[a, b]` and vanishing almost
everywhere on `(a, b)` has `L = 0`: a nonempty open subset of `(a, b)` has positive measure. -/
private lemma l3f_lim_eq_zero {F : ℝ → ℝ} {a b t₀ L : ℝ} (hab : a < b) (ht₀ : t₀ ∈ Icc a b)
    (hF : Tendsto F (𝓝[Icc a b] t₀) (𝓝 L)) (hae : ∀ᵐ t, t ∈ Ioo a b → F t = 0) : L = 0 := by
  by_contra hL
  obtain ⟨V, hVo, htV, hVsub⟩ := mem_nhdsWithin.1 (hF.eventually_ne hL)
  have hne : (V ∩ Ioo a b).Nonempty :=
    mem_closure_iff.1 (by rw [closure_Ioo hab.ne]; exact ht₀) V hVo htV
  refine ((hVo.inter isOpen_Ioo).measure_pos volume hne).ne'
    (measure_mono_null (fun τ hτ ↦ ?_) (ae_iff.1 hae))
  simp only [mem_ofPred_eq, not_imp]
  exact ⟨hτ.2, hVsub ⟨hτ.1, Ioo_subset_Icc_self hτ.2⟩⟩

/-- A continuous curve on `[t₁, t₂]` constant on `(t₁, t₂)` is constant on `[t₁, t₂]`. -/
private lemma l3f_eqOn_Icc {f : ℝ → Mat2} {c : Mat2} {t₁ t₂ : ℝ}
    (hf : ContinuousOn f (Icc t₁ t₂)) (h₁₂ : t₁ < t₂) (h : ∀ t ∈ Ioo t₁ t₂, f t = c) :
    ∀ t ∈ Icc t₁ t₂, f t = c := fun _ ht ↦
  Set.EqOn.of_subset_closure (g := fun _ ↦ c) h hf continuousOn_const Ioo_subset_Icc_self
    (by rw [closure_Ioo h₁₂.ne]) ht

/-! ### Matrices and controls -/

private lemma l3f_traceForm_comm (A B : Mat2) : traceForm A B = traceForm B A :=
  Matrix.trace_mul_comm A B

/-- `⟨c A, B⟩ = c ⟨A, B⟩`. -/
theorem traceForm_smul_left (c : ℝ) (A B : Mat2) :
    traceForm (c • A) B = c * traceForm A B := by
  simp [traceForm, Matrix.trace_smul]

private lemma l3f_traceForm_smul_right (c : ℝ) (A B : Mat2) :
    traceForm A (c • B) = c * traceForm A B := by
  simp [traceForm, Matrix.trace_smul]

/-- `U_T` is convex. -/
theorem convex_controlSimplex : Convex ℝ controlSimplex := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  refine ⟨fun i ↦ ⟨?_, ?_⟩, ?_⟩ <;> simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  · nlinarith [(hx1 i).1, (hy1 i).1]
  · nlinarith [mul_le_mul_of_nonneg_left (hx1 i).2 ha, mul_le_mul_of_nonneg_left (hy1 i).2 hb]
  · linear_combination a * hx2 + b * hy2 + hab

/-- A vertex of `U_T` lies in every edge `{u_k = 0}` with `k` different from its index. -/
theorem vertex_mem_controlEdge {i k : Fin 3} (h : i ≠ k) : vertex i ∈ controlEdge k :=
  ⟨poly_vertex_mem i, by simp [vertex, Ne.symm h]⟩

/-- The centre of `U_T` lies in `U_T`. -/
private lemma l3f_centre_mem : controlCentre ∈ controlSimplex := by
  refine ⟨fun i ↦ ?_, ?_⟩ <;> [fin_cases i <;> norm_num [controlCentre]; norm_num [controlCentre]]

/-- `Z_{(⅓, ⅓, ⅓)} = J/3`. -/
private lemma l3f_controlMatrix_centre : controlMatrix controlCentre = (1 / 3 : ℝ) • J := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [controlMatrix, controlCentre, J]

/-- The entries of `Z_u` have absolute value at most `1` on `U_T`. -/
private lemma l3f_abs_controlMatrix_le {u : Fin 3 → ℝ} (hu : u ∈ controlSimplex) (i j : Fin 2) :
    |controlMatrix u i j| ≤ 1 := by
  obtain ⟨hu01, hsum⟩ := hu
  obtain ⟨h00, h01⟩ := hu01 0
  obtain ⟨h10, h11⟩ := hu01 1
  obtain ⟨h20, h21⟩ := hu01 2
  have h3 : 1 ≤ √3 := by
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hs3 : 0 < √3 := by positivity
  fin_cases i <;> fin_cases j <;> simp only [controlMatrix, Fin.zero_eta, Fin.isValue,
    Fin.mk_one, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one] <;> rw [abs_le]
  · constructor
    · rw [le_div_iff₀ hs3]; nlinarith
    · rw [div_le_iff₀ hs3]; nlinarith
  · constructor <;> linarith
  · constructor <;> linarith
  · constructor
    · rw [le_div_iff₀ hs3]; nlinarith
    · rw [div_le_iff₀ hs3]; nlinarith

/-- `⟨Z_u, J⟩ = -2/3` on `U_T`. -/
private lemma l3f_traceForm_controlMatrix_J {u : Fin 3 → ℝ} (hu : u ∈ controlSimplex) :
    traceForm (controlMatrix u) J = -(2 / 3) := by
  have hsum := hu.2
  simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, J,
    controlMatrix, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one, Fin.isValue]
  linarith

/-- `u ↦ ⟨Z_u, M⟩` is linear: `⟨Z_u, M⟩ = Σ uᵢ ⟨Z_{eᵢ}, M⟩`. -/
private lemma l3f_traceForm_controlMatrix_eq (u : Fin 3 → ℝ) (M : Mat2) :
    traceForm (controlMatrix u) M = u 0 * traceForm (controlMatrix (vertex 0)) M +
      u 1 * traceForm (controlMatrix (vertex 1)) M +
        u 2 * traceForm (controlMatrix (vertex 2)) M := by
  simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  simp [controlMatrix, vertex]
  ring

/-- `X = J` is a star state. -/
private lemma l3f_isStarState_J : IsStarState J := by
  refine ⟨by simp [J, Matrix.trace_fin_two], by simp [J, Matrix.det_fin_two], ?_, ?_, ?_⟩ <;>
    simp [ρ₀, ρ₁, ρ₂, J]

/-- `⟨X, X⟩ = -2 det X = -2` for a star state. -/
private lemma l3f_traceForm_self {X : Mat2} (hX : IsStarState X) : traceForm X X = -2 := by
  obtain ⟨htr, hdet, -⟩ := hX
  rw [Matrix.trace_fin_two] at htr
  rw [Matrix.det_fin_two] at hdet
  have h11 : X 1 1 = -X 0 0 := by linarith
  simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  rw [h11] at hdet ⊢
  linear_combination (-2) * hdet

/-- A star state commuting with `J` is `J` (`ℝJ ∩ O_J = {J}`: `det X = 1` and `X₁₀ > 0`). -/
private lemma l3f_eq_J {X : Mat2} (hX : IsStarState X) (h : J * X - X * J = 0) : X = J := by
  obtain ⟨htr, hdet, h0, h1, -⟩ := hX
  rw [Matrix.trace_fin_two] at htr
  rw [Matrix.det_fin_two] at hdet
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.zero_apply] at e00 e01
  simp [J] at e00 e01
  have hc : 0 < X 1 0 := by
    simp only [ρ₀, ρ₁] at h0 h1
    have h3 : (0 : ℝ) < √3 := by positivity
    rw [div_pos_iff_of_pos_right h3] at h0 h1
    linarith
  have ha : X 0 0 = 0 := by linarith
  have hd : X 1 1 = 0 := by linarith
  have hb : X 0 1 = -X 1 0 := by linarith
  rw [ha, hd, hb] at hdet
  have hc1 : X 1 0 = 1 := by nlinarith
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J, ha, hd, hb, hc1]

/-- The control matrices commuting with `J` on `U_T`: only the centre, through
`[P, J] = [Z_u, J]/⟨Z_u, J⟩`. -/
private lemma l3f_eq_centre {u : Fin 3 → ℝ} (hu : u ∈ controlSimplex)
    (h : controlP u J * J - J * controlP u J = 0) : u = controlCentre := by
  have hc : traceForm (controlMatrix u) J ≠ 0 := by
    rw [l3f_traceForm_controlMatrix_J hu]; norm_num
  have h' : controlMatrix u * J - J * controlMatrix u = 0 := by
    have e : controlP u J * J - J * controlP u J =
        (traceForm (controlMatrix u) J)⁻¹ • (controlMatrix u * J - J * controlMatrix u) := by
      simp only [controlP, Matrix.smul_mul, Matrix.mul_smul, smul_sub]
    rw [e] at h
    exact (smul_eq_zero.1 h).resolve_left (inv_ne_zero hc)
  have e00 := congrFun (congrFun h' 0) 0
  have e01 := congrFun (congrFun h' 0) 1
  simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.zero_apply] at e00 e01
  simp only [controlMatrix, Fin.isValue, of_apply, cons_val', cons_val_zero, cons_val_fin_one, J,
    mul_zero, cons_val_one, mul_one, zero_add, zero_mul, neg_mul, one_mul, sub_neg_eq_add, mul_neg,
    add_zero] at e00 e01
  have hsum := hu.2
  have h3 : √3 ≠ 0 := by positivity
  have h12 : u 1 = u 2 := by
    field_simp at e01
    linarith
  funext i
  fin_cases i <;> simp [controlCentre] <;> linarith

/-- `exp(Jt)` at `t = 0`. -/
private lemma l3f_expJ_zero : expJ 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [expJ]

/-- `det exp(Jt) = 1`. -/
private lemma l3f_det_expJ (t : ℝ) : (expJ t).det = 1 := by
  rw [expJ, Matrix.det_fin_two_of]
  linear_combination Real.cos_sq_add_sin_sq t

/-- `t ↦ exp(Jt)` is continuous. -/
private lemma l3f_continuous_expJ : Continuous expJ :=
  continuous_matrix fun i j ↦ by
    fin_cases i <;> fin_cases j <;>
      simp only [expJ, Fin.zero_eta, Fin.isValue, Fin.mk_one, of_apply, cons_val', cons_val_zero,
        cons_val_one, cons_val_fin_one] <;> fun_prop

/-- `(exp(J(t - t₁)))' = exp(J(t - t₁)) J`. -/
private lemma l3f_hasDerivAt_expJ (t₁ t : ℝ) :
    HasDerivAtEntrywise (fun s ↦ expJ (s - t₁)) (expJ (t - t₁) * J) t := by
  have hs : HasDerivAt (fun s : ℝ ↦ s - t₁) 1 t := (hasDerivAt_id t).sub_const t₁
  rw [hasDerivAtEntrywise_fin_two_iff]
  simp only [expJ, J, Matrix.mul_apply, Fin.sum_univ_two, of_apply, cons_val', cons_val_zero,
    cons_val_one, empty_val', cons_val_fin_one, Fin.isValue]
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert hs.cos using 1; ring
  · convert hs.sin.neg using 1; ring
  · convert hs.sin using 1; ring
  · convert hs.cos using 1; ring

/-- Where `Λ_R = 0` the Hamiltonian does not involve the control, so every control maximizes it
and the arc is singular (Definition 6.2.1(3)). -/
private lemma l3f_isSingularSubarc_of_zero {lam : ℝ} {Λ₁ ΛR X : ℝ → Mat2} {t₁ t₂ : ℝ}
    (h₁₂ : t₁ < t₂) (h : ∀ t ∈ Ioo t₁ t₂, ΛR t = 0) : IsSingularSubarc lam Λ₁ ΛR X t₁ t₂ := by
  refine ⟨h₁₂, fun t ht ↦ ⟨vertex 0, poly_vertex_mem 0, vertex 1, poly_vertex_mem 1, ?_, ?_, ?_⟩⟩
  · intro hv
    have := congrFun hv 0
    simp [vertex] at this
  · intro v' _
    simp [hamiltonian, h t ht, traceForm]
  · intro v' _
    simp [hamiltonian, h t ht, traceForm]


/-! ### Lemma 8.2.1: rescaling to the star domain, and the faces of `U_T` -/

/-- The star inequalities give `det X > 0` (for traceless `X`): `X₁₀ > √3 |X₀₀|` and
`X₀₁ < -X₁₀/3`, so `3 det X = (X₁₀² - 3X₀₀²) + X₁₀(-(3X₀₁ + X₁₀)) > 0`. -/
private lemma l3f_det_pos {X : Mat2} (htr : X.trace = 0)
    (h : 0 < ρ₀ X ∧ 0 < ρ₁ X ∧ 0 < ρ₂ X) : 0 < X.det := by
  obtain ⟨h0, h1, h2⟩ := h
  have h3 : (0 : ℝ) < √3 := by positivity
  have h33 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [ρ₀, ρ₁, ρ₂] at h0 h1 h2
  rw [div_pos_iff_of_pos_right h3] at h0 h1
  rw [div_pos_iff_of_pos_right (by positivity)] at h2
  rw [Matrix.trace_fin_two] at htr
  rw [Matrix.det_fin_two]
  have h11 : X 1 1 = -X 0 0 := by linarith
  have hA : 0 < X 1 0 ^ 2 - 3 * X 0 0 ^ 2 := by
    have := mul_pos h0 h1
    have e : (X 1 0 + √3 * X 0 0) * (X 1 0 - √3 * X 0 0) = X 1 0 ^ 2 - 3 * X 0 0 ^ 2 := by
      linear_combination (-(X 0 0 ^ 2)) * h33
    linarith
  have hc : 0 < X 1 0 := by linarith
  have hB := mul_pos hc h2
  rw [h11]
  nlinarith

/-- `ρ_i(cX) = c ρ_i(X)`. -/
private lemma l3f_ρ_smul (c : ℝ) (M : Mat2) :
    ρ₀ (c • M) = c * ρ₀ M ∧ ρ₁ (c • M) = c * ρ₁ M ∧ ρ₂ (c • M) = c * ρ₂ M := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [ρ₀, ρ₁, ρ₂, Matrix.smul_apply, smul_eq_mul] <;> ring

/-- The reduction of Lemma 8.2.1 to a star state: if `⟨X, Z_u⟩ ≠ 0` on `U_T` (for traceless `X`),
then some nonzero multiple `κX` is a star state with `det(κX) = 1`. The denominator `⟨X, Z_u⟩` is
continuous on the connected set `U_T` and never zero, so it has a constant sign there; `X` or `-X`
then satisfies the star inequalities (Lemma 3.3.4), so `det X > 0`, and `X/√(det X)` or its
negative is a star state. -/
private lemma l3f_rescale {X : Mat2} (hX : X.trace = 0)
    (hden : ∀ u ∈ controlSimplex, traceForm X (controlMatrix u) ≠ 0) :
    ∃ κ : ℝ, κ ≠ 0 ∧ IsStarState (κ • X) := by
  have hcont : ContinuousOn (fun u ↦ traceForm X (controlMatrix u)) controlSimplex := by
    refine Continuous.continuousOn ?_
    simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      controlMatrix, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
      cons_val_fin_one]
    fun_prop
  have hpc : IsPreconnected controlSimplex := convex_controlSimplex.isPreconnected
  have hc := l3f_centre_mem
  -- the sign of the denominator
  obtain ⟨σ, hσ, hneg⟩ : ∃ σ : ℝ, σ ≠ 0 ∧
      ∀ u ∈ controlSimplex, traceForm (controlMatrix u) (σ • X) < 0 := by
    rcases lt_or_gt_of_ne (hden _ hc) with hlt | hgt
    · refine ⟨1, one_ne_zero, fun u hu ↦ ?_⟩
      rw [one_smul, l3f_traceForm_comm]
      by_contra hge
      push Not at hge
      obtain ⟨w, hw, hw0⟩ := hpc.intermediate_value hc hu hcont ⟨hlt.le, hge⟩
      exact hden w hw hw0
    · refine ⟨-1, by norm_num, fun u hu ↦ ?_⟩
      rw [l3f_traceForm_comm, traceForm_smul_left]
      by_contra hge
      push Not at hge
      obtain ⟨w, hw, hw0⟩ := hpc.intermediate_value hu hc hcont ⟨by linarith, hgt.le⟩
      exact hden w hw hw0
  -- `σX` satisfies the star inequalities, so `det(σX) > 0`; normalize the determinant
  have htr' : (σ • X).trace = 0 := by rw [Matrix.trace_smul, hX, smul_zero]
  have hρ := (lemma3_3_4 (σ • X) htr').2 hneg
  have hdet := l3f_det_pos htr' hρ
  set κ₀ := √((σ • X).det)
  have hκ₀ : 0 < κ₀ := Real.sqrt_pos.2 hdet
  refine ⟨κ₀⁻¹ * σ, mul_ne_zero (inv_ne_zero hκ₀.ne') hσ, ?_⟩
  rw [mul_smul]
  obtain ⟨e0, e1, e2⟩ := l3f_ρ_smul κ₀⁻¹ (σ • X)
  refine ⟨by rw [Matrix.trace_smul, htr', smul_zero], ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_smul, Fintype.card_fin, inv_pow, Real.sq_sqrt hdet.le,
      inv_mul_cancel₀ hdet.ne']
  · rw [e0]; exact mul_pos (inv_pos.2 hκ₀) hρ.1
  · rw [e1]; exact mul_pos (inv_pos.2 hκ₀) hρ.2.1
  · rw [e2]; exact mul_pos (inv_pos.2 hκ₀) hρ.2.2

/-- Every star state is `Φ(x + iy)` with `x + iy` in the star domain (Lemma 4.1.1 and
Theorem 4.4.1): `x = X₀₀/X₁₀`, `y = 1/X₁₀`. -/
private lemma l3f_exists_Φ {X : Mat2} (hX : IsStarState X) :
    ∃ x y, (x, y) ∈ starDomain ∧ X = Φ x y := by
  obtain ⟨htr, hdet, h0, h1, -⟩ := id hX
  have h3 : (0 : ℝ) < √3 := by positivity
  have hc : 0 < X 1 0 := by
    simp only [ρ₀, ρ₁] at h0 h1
    rw [div_pos_iff_of_pos_right h3] at h0 h1
    linarith
  rw [Matrix.trace_fin_two] at htr
  rw [Matrix.det_fin_two] at hdet
  have h11 : X 1 1 = -X 0 0 := by linarith
  have hc0 := hc.ne'
  have hXΦ : X = Φ (X 0 0 / X 1 0) (1 / X 1 0) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Φ] <;> field_simp
    · rw [h11] at hdet; linear_combination -hdet
    · exact h11
  refine ⟨_, _, (theorem4_4_1 _ _ (by positivity)).1 (hXΦ ▸ hX), hXΦ⟩

/-- Nondegeneracy: `Λ ∈ X^⊥` (`X = Φ(x + iy)`) pairing to zero with the tangent vectors
`Y_z(1, 0)` and `Y_z(0, 1)` (Lemma 4.2.4), i.e. with `ν = T*Φ(-Λ) = 0`, is zero: `Λ` lies in the
orthogonal complement of all of `𝔰𝔩₂(ℝ)`. -/
private lemma l3f_eq_zero_of_nu {Λ : Mat2} {x y : ℝ} (hy : 0 < y) (htr : Λ.trace = 0)
    (hΦ : traceForm Λ (Φ x y) = 0) (h1 : traceForm (-Λ) (tangentLift x y 1 0) = 0)
    (h2 : traceForm (-Λ) (tangentLift x y 0 1) = 0) : Λ = 0 := by
  have hy0 := hy.ne'
  rw [Matrix.trace_fin_two] at htr
  have h11 : Λ 1 1 = -Λ 0 0 := by linarith
  simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two] at hΦ h1 h2
  simp only [Fin.isValue, Φ, neg_add_rev, one_div, of_apply, cons_val', cons_val_zero,
    cons_val_fin_one, cons_val_one, h11, neg_mul, Matrix.neg_apply, tangentLift, zero_div, mul_one,
    zero_mul, sub_zero, neg_zero, mul_zero, add_zero, neg_neg, zero_add, neg_eq_zero, mul_eq_zero,
    div_eq_zero_iff, or_self, _root_.mul_inv_rev, one_mul, zero_sub] at hΦ h1 h2
  have hc : Λ 1 0 = 0 := h1.resolve_right hy0
  rw [hc] at h2 hΦ
  field_simp at h2 hΦ
  have ha : Λ 0 0 = 0 := by linarith
  rw [ha] at hΦ
  have hb : Λ 0 1 = 0 := by linarith
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, h11]

/-- An extreme subset `F` of `U_T` containing `q` contains every `p ∈ U_T` whose support is
contained in that of `q`: `q` lies in the open segment from `p` to `q + ε(q - p) ∈ U_T`. -/
private lemma l3f_absorb {F : Set (Fin 3 → ℝ)} (hext : IsExtreme ℝ controlSimplex F)
    {q p : Fin 3 → ℝ} (hq : q ∈ F) (hp : p ∈ controlSimplex) (hsupp : ∀ i, p i ≠ 0 → 0 < q i) :
    p ∈ F := by
  have hqU := hext.1 hq
  set m : Fin 3 → ℝ := fun i ↦ if 0 < q i then q i else 1
  have hm : ∀ i, 0 < m i := fun i ↦ by
    simp only [m]; split_ifs with h
    · exact h
    · exact one_pos
  have hmq : ∀ i, 0 < q i → m i ≤ q i := fun i hi ↦ by simp [m, hi]
  set ε := min (m 0) (min (m 1) (m 2))
  have hε : 0 < ε := lt_min (hm 0) (lt_min (hm 1) (hm 2))
  have hεm : ∀ i, ε ≤ m i := fun i ↦ by
    fin_cases i
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  set r : Fin 3 → ℝ := (1 + ε) • q - ε • p
  have hr0 : ∀ i, 0 ≤ r i := fun i ↦ by
    simp only [r, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have hq0 := (hqU.1 i).1
    have hp1 := (hp.1 i).2
    by_cases hpi : p i = 0
    · rw [hpi]; nlinarith
    · have := hεm i
      have := hmq i (hsupp i hpi)
      nlinarith
  have hrs : r 0 + r 1 + r 2 = 1 := by
    simp only [r, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (1 + ε) * hqU.2 - ε * hp.2
  have hrU : r ∈ controlSimplex := by
    refine ⟨fun i ↦ ⟨hr0 i, ?_⟩, hrs⟩
    have := hr0 0; have := hr0 1; have := hr0 2
    fin_cases i <;> simp <;> linarith
  have hseg : q ∈ openSegment ℝ p r := by
    refine ⟨ε / (1 + ε), 1 / (1 + ε), by positivity, by positivity,
      by rw [← add_div, div_eq_one_iff_eq (by positivity)]; ring, ?_⟩
    funext i
    simp only [r, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  exact hext.left_mem_of_mem_openSegment hp hrU hq hseg

/-- The faces of the triangle `U_T` other than `U_T`: a nonempty convex extreme subset `F ≠ U_T`
of `U_T` is a vertex or an edge. -/
private lemma l3f_face_classify {F : Set (Fin 3 → ℝ)} (hne : F.Nonempty) (hconv : Convex ℝ F)
    (hext : IsExtreme ℝ controlSimplex F) (hF : F ≠ controlSimplex) :
    (∃ i : Fin 3, F = {vertex i}) ∨ ∃ k : Fin 3, F = controlEdge k := by
  classical
  -- `A i`: some point of `F` has a positive `i`-th coordinate
  set A : Fin 3 → Prop := fun i ↦ ∃ p ∈ F, 0 < p i
  obtain ⟨q, hq⟩ := hne
  -- a point of `F` positive at every coordinate where some point of `F` is
  obtain ⟨m, hmF, hm⟩ : ∃ m ∈ F, ∀ i, A i → 0 < m i := by
    have hw : ∀ i, A i → ∃ p ∈ F, 0 < p i := fun i hi ↦ hi
    choose! w hwF hwpos using hw
    set w' : Fin 3 → Fin 3 → ℝ := fun i ↦ if A i then w i else q
    have hw'F : ∀ i, w' i ∈ F := fun i ↦ by
      simp only [w']; split_ifs with h
      · exact hwF i h
      · exact hq
    refine ⟨∑ i, (1 / 3 : ℝ) • w' i,
      hconv.sum_mem (fun _ _ ↦ by norm_num) (by simp) (fun i _ ↦ hw'F i), fun i hi ↦ ?_⟩
    have hnn : ∀ j, 0 ≤ (1 / 3 : ℝ) * w' j i := fun j ↦
      mul_nonneg (by norm_num) ((hext.1 (hw'F j)).1 i).1
    have hii : 0 < (1 / 3 : ℝ) * w' i i := by
      simp only [w', hi, ↓reduceIte]; exact mul_pos (by norm_num) (hwpos i hi)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact hii.trans_le (Finset.single_le_sum (fun j _ ↦ hnn j) (Finset.mem_univ i))
  -- `F = {p ∈ U_T | pᵢ = 0 whenever ¬A i}`
  have hFeq : ∀ p, p ∈ F ↔ p ∈ controlSimplex ∧ ∀ i, ¬A i → p i = 0 := by
    intro p
    constructor
    · intro hp
      refine ⟨hext.1 hp, fun i hi ↦ ?_⟩
      have := ((hext.1 hp).1 i).1
      by_contra hne'
      exact hi ⟨p, hp, lt_of_le_of_ne this (Ne.symm hne')⟩
    · rintro ⟨hp, hz⟩
      refine l3f_absorb hext hmF hp fun i hi ↦ hm i ?_
      by_contra hAi
      exact hi (hz i hAi)
  -- the edge `{u_k = 0}` when only `A k` fails, the vertex `e_i` when only `A i` holds
  have hedge : ∀ k : Fin 3, ¬A k → (∀ i, i ≠ k → A i) → F = controlEdge k := by
    intro k hk hA
    ext p
    rw [hFeq]
    simp only [controlEdge, mem_ofPred_eq]
    refine ⟨fun h ↦ ⟨h.1, h.2 k hk⟩, fun h ↦ ⟨h.1, fun i hi ↦ ?_⟩⟩
    by_cases hik : i = k
    · rw [hik]; exact h.2
    · exact absurd (hA i hik) hi
  have hvert : ∀ i : Fin 3, A i → (∀ j, j ≠ i → ¬A j) → F = {vertex i} := by
    intro i hi hA
    ext p
    rw [hFeq, mem_singleton_iff]
    constructor
    · rintro ⟨hp, hz⟩
      have hs := hp.2
      funext l
      by_cases hli : l = i
      · subst hli
        simp only [vertex, Pi.single_eq_same]
        have hsum : ∑ j, p j = 1 := by rw [Fin.sum_univ_three]; exact hs
        rw [← hsum, Finset.sum_eq_single l (fun j _ hj ↦ hz j (hA j hj))
          (fun h ↦ absurd (Finset.mem_univ l) h)]
      · simp only [vertex, Pi.single_apply, hli, ↓reduceIte]
        exact hz l (hA l hli)
    · rintro rfl
      refine ⟨poly_vertex_mem i, fun l hl ↦ ?_⟩
      have hli : l ≠ i := by
        rintro rfl
        exact hl hi
      simp [vertex, hli]
  by_cases h0 : A 0 <;> by_cases h1 : A 1 <;> by_cases h2 : A 2
  · -- every coordinate is positive somewhere on `F`: `F = U_T`
    refine absurd (Set.ext fun p ↦ ?_) hF
    rw [hFeq]
    refine ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun i hi ↦ ?_⟩⟩
    fin_cases i
    exacts [absurd h0 hi, absurd h1 hi, absurd h2 hi]
  · exact Or.inr ⟨2, hedge 2 h2 fun i hi ↦ by fin_cases i <;> first | exact h0 | exact h1 |
      exact absurd rfl hi⟩
  · exact Or.inr ⟨1, hedge 1 h1 fun i hi ↦ by fin_cases i <;> first | exact h0 | exact h2 |
      exact absurd rfl hi⟩
  · exact Or.inl ⟨0, hvert 0 h0 fun j hj ↦ by fin_cases j <;> first | exact h1 | exact h2 |
      exact absurd rfl hj⟩
  · exact Or.inr ⟨0, hedge 0 h0 fun i hi ↦ by fin_cases i <;> first | exact h1 | exact h2 |
      exact absurd rfl hi⟩
  · exact Or.inl ⟨1, hvert 1 h1 fun j hj ↦ by fin_cases j <;> first | exact h0 | exact h2 |
      exact absurd rfl hj⟩
  · exact Or.inl ⟨2, hvert 2 h2 fun j hj ↦ by fin_cases j <;> first | exact h0 | exact h1 |
      exact absurd rfl hj⟩
  · -- no coordinate is positive on `F`: impossible, the coordinates sum to `1`
    obtain ⟨hqU, hz⟩ := (hFeq q).1 hq
    have hs := hqU.2
    rw [hz 0 h0, hz 1 h1, hz 2 h2] at hs
    norm_num at hs

/-- **Lemma 8.2.1** (`lem:LambdaR`). Let `X ∈ 𝔰𝔩₂(ℝ)` with `⟨X, Z_u⟩ ≠ 0` for every `u ∈ U_T`
(where the control-dependent term `H₂(Λ, X, Z_u) = -⟨Λ, Z_u⟩/⟨X, Z_u⟩` of the Hamiltonian is
defined; E52), and `Λ ∈ X^⊥` (traceless, `⟨Λ, X⟩ = 0`). If `H₂` does not depend on the control
`u ∈ U_T`, then `Λ = 0`. If `Λ ≠ 0`, the set of controls maximizing the Hamiltonian is a vertex or
an edge of `U_T`.

Proof (the book's, TeX 7107–7126): `H₂ = -⟨Λ, P_u⟩`, `P_u = Z_u/⟨X, Z_u⟩`. Reduce to `X` a star
state with `det X = 1` (`⟨X, Z_u⟩` has a constant sign on `U_T`, so `X` or `-X` satisfies the star
inequalities by Lemma 3.3.4 and `det X > 0`; scaling `X` scales `H₂`), so `X = Φ(z)`, `z ∈ 𝔥*`
(Lemma 4.1.1, Theorem 4.4.1). The vectors `[P_u, X]` are the velocities `f(x, y; u)` of
(4.5.1) through the tangent map of Lemma 4.2.4, whose affine hull is the whole tangent space
(Lemma 6.1.2, `lemma6_1_2`); a constant `⟨Λ, P_u⟩` makes `Λ` orthogonal to all differences
`P_u - P_v`, hence (with `Λ ⊥ X`) to all of `𝔰𝔩₂(ℝ)`, so `Λ = 0`. Contrapositive: if `Λ ≠ 0` the
Hamiltonian is not constant on `U_T`, and the set of maximizers is a face of `U_T`
(Lemma 7.3.1, `lemma7_3_1`) other than `U_T`, i.e. a vertex or an edge (the faces of the
triangle). A shorter argument (not the book's): `Z_{e₁}, Z_{e₂}, Z_{e₃}` span `𝔰𝔩₂(ℝ)`, so
constancy `c` of the ratio gives `Λ = cX`, and `⟨X, X⟩ = -2 det X ≠ 0` gives `c = 0`.

Formal details. The constant sign of `⟨X, Z_u⟩` comes from the intermediate value theorem on the
connected set `U_T` (`l3f_rescale`). The identification of `H₂` with the velocities through the
tangent map is Theorem 6.8.2 (`theorem6_8_2`): `-H₂(u) = ν₁ f₁(u) + ν₂ f₂(u)` with
`ν = T*Φ(-Λ)`; the linear form `ν` is constant on `f(x, y; U_T)`, hence zero on its vector span,
which is all of `ℝ²` by Lemma 6.1.2 (the book's "the value of `H₂` must then be zero"); `ν = 0`
with `Λ ⊥ Φ(z)` gives `Λ = 0` (`l3f_eq_zero_of_nu`). The faces of the triangle other than `U_T`
are its vertices and edges (`l3f_face_classify`, a standard fact the book uses without proof). -/
theorem lemma8_2_1 {X Λ : Mat2} (hX : X.trace = 0) (hden : ∀ u ∈ controlSimplex,
    traceForm X (controlMatrix u) ≠ 0) (hΛ : Λ.trace = 0) (hΛX : traceForm Λ X = 0) :
    ((∀ u ∈ controlSimplex, ∀ v ∈ controlSimplex,
        traceForm Λ (controlMatrix u) / traceForm X (controlMatrix u) =
          traceForm Λ (controlMatrix v) / traceForm X (controlMatrix v)) → Λ = 0) ∧
      (Λ ≠ 0 → ∀ (lam : ℝ) (Λ₁ : Mat2),
        (∃ i : Fin 3, hamiltonianArgmax lam Λ₁ Λ X = {vertex i}) ∨
          ∃ k : Fin 3, hamiltonianArgmax lam Λ₁ Λ X = controlEdge k) := by
  have hpart1 : (∀ u ∈ controlSimplex, ∀ v ∈ controlSimplex,
      traceForm Λ (controlMatrix u) / traceForm X (controlMatrix u) =
        traceForm Λ (controlMatrix v) / traceForm X (controlMatrix v)) → Λ = 0 := by
    intro hconst
    -- reduce to a star state `κX = Φ(z)`, `z ∈ 𝔥*` (Lemma 3.3.4, Lemma 4.1.1, Theorem 4.4.1)
    obtain ⟨κ, hκ, hst⟩ := l3f_rescale hX hden
    obtain ⟨x, y, hxy, hΦ⟩ := l3f_exists_Φ hst
    have hΛΦ : traceForm Λ (Φ x y) = 0 := by
      rw [← hΦ, l3f_traceForm_smul_right, hΛX, mul_zero]
    -- the control-dependent term is `H₂ = ν₁ f₁ + ν₂ f₂` with `ν = T*Φ(-Λ)` (Theorem 6.8.2, through
    -- the tangent map of Lemma 4.2.4)
    set ν := cotangentNu x y Λ
    have hH₂ : ∀ u ∈ controlSimplex, ν.1 * halfPlaneF₁ x y u + ν.2 * halfPlaneF₂ x y u =
        -(κ⁻¹ * (traceForm Λ (controlMatrix u) / traceForm X (controlMatrix u))) := by
      intro u hu
      have h := theorem6_8_2 0 0 Λ x y u hxy hu hΛΦ
      simp only [hamiltonian, planeHamiltonian] at h
      rw [← hΦ, traceForm_smul_left] at h
      have e : traceForm Λ (controlMatrix u) / (κ * traceForm X (controlMatrix u)) =
          κ⁻¹ * (traceForm Λ (controlMatrix u) / traceForm X (controlMatrix u)) := by ring
      linarith
    -- `ℓ = ν₁ dx + ν₂ dy` is constant on the velocity set `f(x, y; U_T)`, whose affine hull is
    -- the whole tangent space (Lemma 6.1.2), so `ℓ = 0`
    obtain ⟨-, -, hspan⟩ := lemma6_1_2 x y hxy
    set S := halfPlaneField x y '' controlSimplex
    let ℓ : (Fin 2 → ℝ) →ₗ[ℝ] ℝ := ν.1 • LinearMap.proj 0 + ν.2 • LinearMap.proj 1
    have hℓ : ∀ w, ℓ w = ν.1 * w 0 + ν.2 * w 1 := fun w ↦ rfl
    have hℓS : ∀ w ∈ S, ℓ w = ℓ (halfPlaneField x y (vertex 0)) := by
      rintro _ ⟨u, hu, rfl⟩
      simp only [hℓ, halfPlaneField, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      rw [hH₂ u hu, hH₂ _ (poly_vertex_mem 0), hconst u hu (vertex 0) (poly_vertex_mem 0)]
    have hker : vectorSpan ℝ S ≤ LinearMap.ker ℓ := by
      rw [vectorSpan_def, Submodule.span_le]
      rintro _ ⟨w, hw, w', hw', rfl⟩
      simp [vsub_eq_sub, map_sub, hℓS w hw, hℓS w' hw']
    have htop : vectorSpan ℝ S = ⊤ := by
      rw [← direction_affineSpan, hspan, AffineSubspace.direction_top]
    have hν₁ : ν.1 = 0 := by
      have h := hker (htop ▸ Submodule.mem_top : (Pi.single 0 1 : Fin 2 → ℝ) ∈ vectorSpan ℝ S)
      simpa [hℓ] using h
    have hν₂ : ν.2 = 0 := by
      have h := hker (htop ▸ Submodule.mem_top : (Pi.single 1 1 : Fin 2 → ℝ) ∈ vectorSpan ℝ S)
      simpa [hℓ] using h
    -- `Λ ∈ X^⊥` is orthogonal to the whole tangent space: `Λ = 0`
    exact l3f_eq_zero_of_nu hxy.1 hΛ hΛΦ hν₁ hν₂
  refine ⟨hpart1, fun hΛ0 lam Λ₁ ↦ ?_⟩
  -- the maximizers form a face of `U_T` (Lemma 7.3.1), not all of `U_T` since `Λ ≠ 0`
  obtain ⟨hne, hconv, hext⟩ := lemma7_3_1 controlSimplex isCompact_controlSimplex
    convex_controlSimplex ⟨_, l3f_centre_mem⟩ lam Λ₁ Λ X hden
  refine l3f_face_classify hne hconv hext fun hF ↦ hΛ0 (hpart1 fun u hu v hv ↦ ?_)
  have hu' : u ∈ hamiltonianArgmax lam Λ₁ Λ X := hF ▸ hu
  have hv' : v ∈ hamiltonianArgmax lam Λ₁ Λ X := hF ▸ hv
  have h1 := hu'.2 v hv
  have h2 := hv'.2 u hu
  simp only [hamiltonian] at h1 h2
  linarith

/-! ### Lemma 8.2.2: the control-dependent terms are bounded multiples of `Λ_R` -/

private lemma l3f_abs_le_sum (M : Mat2) (i j : Fin 2) : |M i j| ≤ ∑ k, ∑ l, |M k l| :=
  (Finset.single_le_sum (f := fun l ↦ |M i l|) (fun _ _ ↦ abs_nonneg _)
    (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun k ↦ ∑ l, |M k l|)
      (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) (Finset.mem_univ i))

private lemma l3f_sum_nonneg (M : Mat2) : 0 ≤ ∑ k, ∑ l, |M k l| :=
  Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

private lemma l3f_abs_mul_le (A B : Mat2) (i j : Fin 2) :
    |(A * B) i j| ≤ (∑ k, ∑ l, |A k l|) * ∑ k, ∑ l, |B k l| := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  have hA0 := l3f_abs_le_sum A i 0
  have hA1 := l3f_abs_le_sum A i 1
  have hB : |B 0 j| + |B 1 j| ≤ ∑ k, ∑ l, |B k l| := by
    simp only [Fin.sum_univ_two]
    fin_cases j <;> simp <;>
      linarith [abs_nonneg (B 0 0), abs_nonneg (B 0 1), abs_nonneg (B 1 0), abs_nonneg (B 1 1)]
  have hsA := l3f_sum_nonneg A
  calc |A i 0 * B 0 j + A i 1 * B 1 j| ≤ |A i 0| * |B 0 j| + |A i 1| * |B 1 j| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ (∑ k, ∑ l, |A k l|) * |B 0 j| + (∑ k, ∑ l, |A k l|) * |B 1 j| :=
        add_le_add (mul_le_mul_of_nonneg_right hA0 (abs_nonneg _))
          (mul_le_mul_of_nonneg_right hA1 (abs_nonneg _))
    _ = (∑ k, ∑ l, |A k l|) * (|B 0 j| + |B 1 j|) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hB hsA

private lemma l3f_abs_traceForm_le (A B : Mat2) :
    |traceForm A B| ≤ 2 * ((∑ k, ∑ l, |A k l|) * ∑ k, ∑ l, |B k l|) := by
  rw [traceForm, Matrix.trace_fin_two]
  have := abs_add_le ((A * B) 0 0) ((A * B) 1 1)
  linarith [l3f_abs_mul_le A B 0 0, l3f_abs_mul_le A B 1 1]

/-- The control-dependent terms `[P, Λ] - ⟨Λ, P⟩[P, X]` of the costate equation for `Λ_R` are a
bounded multiple of `Λ`. -/
private lemma l3f_abs_ctrl_le (P Λ X : Mat2) (i j : Fin 2) :
    |((P * Λ - Λ * P) - traceForm Λ P • (P * X - X * P)) i j| ≤
      (∑ k, ∑ l, |Λ k l|) * (4 * (∑ k, ∑ l, |P k l|) +
        8 * (∑ k, ∑ l, |P k l|) ^ 2 * ∑ k, ∑ l, |X k l|) := by
  have h1 := poly_abs_bracket_le P Λ i j
  have h2 := poly_abs_bracket_le P X i j
  have h3 := l3f_abs_traceForm_le Λ P
  have hP := l3f_sum_nonneg P
  have hΛ := l3f_sum_nonneg Λ
  have hX := l3f_sum_nonneg X
  rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  calc _ ≤ |(P * Λ - Λ * P) i j| + |traceForm Λ P| * |(P * X - X * P) i j| := by
        rw [← abs_mul]; exact abs_sub _ _
    _ ≤ 4 * (∑ k, ∑ l, |P k l|) * (∑ k, ∑ l, |Λ k l|) +
          (2 * ((∑ k, ∑ l, |Λ k l|) * ∑ k, ∑ l, |P k l|)) *
            (4 * (∑ k, ∑ l, |P k l|) * ∑ k, ∑ l, |X k l|) :=
        add_le_add h1 (mul_le_mul h3 h2 (abs_nonneg _) (by positivity))
    _ = _ := by ring

/-- `Σ |Z_u|ᵢⱼ ≤ 4` on `U_T`. -/
private lemma l3f_sum_controlMatrix_le {u : Fin 3 → ℝ} (hu : u ∈ controlSimplex) :
    ∑ k, ∑ l, |controlMatrix u k l| ≤ 4 := by
  simp only [Fin.sum_univ_two]
  linarith [l3f_abs_controlMatrix_le hu 0 0, l3f_abs_controlMatrix_le hu 0 1,
    l3f_abs_controlMatrix_le hu 1 0, l3f_abs_controlMatrix_le hu 1 1]

/-- `P = Z_u/⟨Z_u, X⟩` is bounded where `⟨Z_u, X⟩ ≤ -δ`. -/
private lemma l3f_sum_controlP_le {u : Fin 3 → ℝ} (hu : u ∈ controlSimplex) {X : Mat2} {δ : ℝ}
    (hδ : 0 < δ) (h : traceForm (controlMatrix u) X ≤ -δ) :
    ∑ k, ∑ l, |controlP u X k l| ≤ 4 / δ := by
  have hc : δ ≤ |traceForm (controlMatrix u) X| := by
    rw [abs_of_neg (by linarith)]; linarith
  have e : ∑ k, ∑ l, |controlP u X k l| =
      |traceForm (controlMatrix u) X|⁻¹ * ∑ k, ∑ l, |controlMatrix u k l| := by
    simp only [controlP, Matrix.smul_apply, smul_eq_mul, abs_mul, abs_inv, Finset.mul_sum]
  rw [e, inv_mul_eq_div]
  exact div_le_div₀ (by norm_num) (l3f_sum_controlMatrix_le hu) hδ hc

/-- Near a time where `X` is a star state, `⟨Z_u, X⟩ ≤ -δ` uniformly in `u ∈ U_T` (Lemma 3.3.4 at
the vertices, continuity, and linearity in `u`). -/
private lemma l3f_eventually_denom {X : ℝ → Mat2} {s : Set ℝ} {t₀ : ℝ}
    (hX : ContinuousWithinAt X s t₀) (hst : IsStarState (X t₀)) :
    ∃ δ > 0, ∀ᶠ t in 𝓝[s] t₀, ∀ u ∈ controlSimplex, traceForm (controlMatrix u) (X t) ≤ -δ := by
  have hneg := (lemma3_3_4 (X t₀) hst.1).1 hst.2.2
  set d : Fin 3 → ℝ := fun i ↦ traceForm (controlMatrix (vertex i)) (X t₀)
  have hd : ∀ i, d i < 0 := fun i ↦ hneg _ (poly_vertex_mem i)
  set δ := min (-d 0) (min (-d 1) (-d 2)) / 2
  have hδ : 0 < δ := by
    have := hd 0; have := hd 1; have := hd 2
    exact div_pos (lt_min (by linarith) (lt_min (by linarith) (by linarith))) two_pos
  have hdδ : ∀ i, d i < -δ := by
    intro i
    have hle : min (-d 0) (min (-d 1) (-d 2)) ≤ -d i := by
      fin_cases i
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (min_le_left _ _)
      · exact (min_le_right _ _).trans (min_le_right _ _)
    have := hd i
    simp only [δ]
    linarith
  refine ⟨δ, hδ, ?_⟩
  have htr : Continuous fun M : Mat2 ↦ M.trace := continuous_id.matrix_trace
  have hev : ∀ i, ∀ᶠ t in 𝓝[s] t₀, traceForm (controlMatrix (vertex i)) (X t) < -δ := by
    intro i
    have hc : ContinuousWithinAt (fun t ↦ traceForm (controlMatrix (vertex i)) (X t)) s t₀ :=
      (htr.comp (continuous_const.mul continuous_id)).continuousAt.comp_continuousWithinAt hX
    exact hc.eventually (gt_mem_nhds (hdδ i))
  filter_upwards [hev 0, hev 1, hev 2] with t h0 h1 h2 u hu
  rw [l3f_traceForm_controlMatrix_eq]
  obtain ⟨hb, hsum⟩ := hu
  have e0 := mul_le_mul_of_nonneg_left h0.le (hb 0).1
  have e1 := mul_le_mul_of_nonneg_left h1.le (hb 1).1
  have e2 := mul_le_mul_of_nonneg_left h2.le (hb 2).1
  nlinarith

/-- **Lemma 8.2.2** (`lem:Lambda1`). Along an extremal lifted trajectory on `[a, b]`, at every
time `t₀` with `Λ_R(t₀) = 0` the right-hand side of the costate equation for `Λ_R`
(`costateRHS`, `eqn:lamR`) is continuous: it tends to `[-Λ₁(t₀) + (3/2) λ_cost J, X(t₀)]`, so
`Λ_R` is differentiable at `t₀` with that derivative. If moreover `Λ_R'(t₀) = 0`, then
`λ_cost ≠ 0` and `Λ₁(t₀) = (3/2) λ_cost J`.

Proof (the book's, TeX 7137–7167): the control-dependent terms `[P, Λ_R] - ⟨Λ_R, P⟩[P, X]` are
bounded multiples of `Λ_R` (`P = Z_u/⟨Z_u, X⟩` is bounded on the trajectory, Lemma 3.3.4), so they
tend to `0`; the rest is continuous. The Hamiltonian vanishes along the extremal (`H = 0`
almost everywhere, extended to `t₀` by the same continuity), which at `t₀` reads
`⟨Λ_{1,cost}, X⟩ = 0`, `Λ_{1,cost} = Λ₁ - (3/2) λ_cost J` (8.2.1); `0 = Λ_R'(t₀)
= -[Λ_{1,cost}, X(t₀)]` puts `Λ_{1,cost}(t₀)` in the centralizer `ℝX(t₀)`; `ℝX ∩ X^⊥ = 0`
(`⟨X, X⟩ = -2`) gives `Λ_{1,cost}(t₀) = 0`. If `λ_cost = 0` then `(λ_cost, Λ₁, Λ_R) = 0` at `t₀`,
against the nontriviality of the reduced costate (E21; part of `IsStateCostateSolution`).

Formal details. Near `t₀`, `⟨Z_u, X⟩ ≤ -δ` uniformly in `u ∈ U_T` (`l3f_eventually_denom`), so
`Σ|P_ij| ≤ 4/δ` and the control-dependent terms are at most `Σ|Λ_R|_ij` times a bound
(`l3f_abs_ctrl_le`). `H = 0` holds almost everywhere on `(a, b)`, and `H` tends to
`⟨Λ_{1,cost}(t₀), X(t₀)⟩` at `t₀` within `[a, b]`; a nonempty open subset of `(a, b)` has positive
measure, so the limit is `0` (`l3f_lim_eq_zero`). -/
theorem lemma8_2_2 {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (h : IsExtremalOn a b u g X Λ₁ ΛR lam) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b) (hΛ : ΛR t₀ = 0) :
    Tendsto (fun t ↦ costateRHS lam (Λ₁ t) (ΛR t) (X t) (u t)) (𝓝[Icc a b] t₀)
        (𝓝 ((-Λ₁ t₀ + (3 / 2 * lam) • J) * X t₀ - X t₀ * (-Λ₁ t₀ + (3 / 2 * lam) • J))) ∧
      HasDerivWithinAtEntrywise ΛR
        ((-Λ₁ t₀ + (3 / 2 * lam) • J) * X t₀ - X t₀ * (-Λ₁ t₀ + (3 / 2 * lam) • J))
        (Icc a b) t₀ ∧
      ((-Λ₁ t₀ + (3 / 2 * lam) • J) * X t₀ - X t₀ * (-Λ₁ t₀ + (3 / 2 * lam) • J) = 0 →
        lam ≠ 0 ∧ Λ₁ t₀ = (3 / 2 * lam) • J) := by
  obtain ⟨hab, hpt, -, hXI, hI1, hIR, hmax⟩ := l3f_data h
  have hXc : ContinuousOn X (Icc a b) := Matrix.continuousOn_of_eq_add_integral hXI
  have h1c : ContinuousOn Λ₁ (Icc a b) := Matrix.continuousOn_of_eq_add_integral hI1
  have hRc : ContinuousOn ΛR (Icc a b) := Matrix.continuousOn_of_eq_add_integral hIR
  have hst₀ := (hpt t₀ ht₀).2.2.1
  -- `|⟨Z_u, X⟩| ≥ δ` near `t₀`, so `P = Z_u/⟨Z_u, X⟩` stays bounded (Lemma 3.3.4)
  obtain ⟨δ, hδ, hev⟩ := l3f_eventually_denom (hXc t₀ ht₀) hst₀
  set B : ℝ → Mat2 := fun t ↦
    (-Λ₁ t + (3 / 2 * lam) • J) * X t - X t * (-Λ₁ t + (3 / 2 * lam) • J) with hBdef
  have hBc : ContinuousWithinAt B (Icc a b) t₀ :=
    (((h1c t₀ ht₀).neg.add continuousWithinAt_const).mul (hXc t₀ ht₀)).sub
      ((hXc t₀ ht₀).mul ((h1c t₀ ht₀).neg.add continuousWithinAt_const))
  -- the size of `Λ_R` tends to `0`
  have hσ : Continuous fun M : Mat2 ↦ ∑ k, ∑ l, |M k l| := by fun_prop
  have hsR : Tendsto (fun t ↦ ∑ k, ∑ l, |ΛR t k l|) (𝓝[Icc a b] t₀) (𝓝 0) := by
    have := (hσ.continuousAt.comp_continuousWithinAt (hRc t₀ ht₀)).tendsto
    simpa [Function.comp_def, hΛ] using this
  have hsX : Tendsto (fun t ↦ ∑ k, ∑ l, |X t k l|) (𝓝[Icc a b] t₀)
      (𝓝 (∑ k, ∑ l, |X t₀ k l|)) :=
    (hσ.continuousAt.comp_continuousWithinAt (hXc t₀ ht₀)).tendsto
  set K := 4 / δ
  have hbound : Tendsto (fun t ↦ (∑ k, ∑ l, |ΛR t k l|) *
      (4 * K + 8 * K ^ 2 * ∑ k, ∑ l, |X t k l|)) (𝓝[Icc a b] t₀) (𝓝 0) := by
    simpa using hsR.mul (tendsto_const_nhds.add (tendsto_const_nhds.mul hsX))
  -- the control-dependent terms `[P, Λ_R] - ⟨Λ_R, P⟩[P, X]` are bounded multiples of `Λ_R`
  have hctrl : ∀ i j, Tendsto (fun t ↦
      ((controlP (u t) (X t) * ΛR t - ΛR t * controlP (u t) (X t)) -
        traceForm (ΛR t) (controlP (u t) (X t)) •
        (controlP (u t) (X t) * X t - X t * controlP (u t) (X t))) i j) (𝓝[Icc a b] t₀)
      (𝓝 0) := by
    intro i j
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [hev, self_mem_nhdsWithin] with t ht htI
    rw [Real.norm_eq_abs]
    refine (l3f_abs_ctrl_le _ _ _ i j).trans ?_
    have hP := l3f_sum_controlP_le (hpt t htI).1 hδ (ht _ (hpt t htI).1)
    have hP0 := l3f_sum_nonneg (controlP (u t) (X t))
    have hR0 := l3f_sum_nonneg (ΛR t)
    have hX0 := l3f_sum_nonneg (X t)
    refine mul_le_mul_of_nonneg_left ?_ hR0
    have hP2 : (∑ k, ∑ l, |controlP (u t) (X t) k l|) ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ hP0 hP 2
    nlinarith [mul_le_mul_of_nonneg_right hP2 hX0]
  -- so the right-hand side of the costate equation for `Λ_R` is continuous at `t₀`
  have hV0 : costateRHS lam (Λ₁ t₀) (ΛR t₀) (X t₀) (u t₀) = B t₀ := by
    simp [costateRHS, hΛ, B, traceForm]
  have hVc : ContinuousWithinAt (fun t ↦ costateRHS lam (Λ₁ t) (ΛR t) (X t) (u t))
      (Icc a b) t₀ := by
    refine Matrix.continuousWithinAt_iff_entrywise.2 fun i j ↦ ?_
    have hB := Matrix.continuousWithinAt_iff_entrywise.1 hBc i j
    have := (hctrl i j).add hB
    rw [zero_add] at this
    rw [ContinuousWithinAt, hV0]
    exact this.congr fun t ↦ by simp only [costateRHS, Matrix.add_apply, B]
  have hV := hVc.tendsto
  have hD := Matrix.hasDerivWithinAtEntrywise_of_eq_add_integral hIR ht₀ hVc
  rw [hV0] at hV hD
  refine ⟨hV, hD, fun hB0 ↦ ?_⟩
  -- `H = 0` along the extremal extends to `t₀`, where it reads `⟨Λ_{1,cost}, X⟩ = 0`
  have htr : Continuous fun M : Mat2 ↦ M.trace := continuous_id.matrix_trace
  have hf : Tendsto (fun t ↦ traceForm (Λ₁ t - (3 / 2 * lam) • J) (X t)) (𝓝[Icc a b] t₀)
      (𝓝 (traceForm (Λ₁ t₀ - (3 / 2 * lam) • J) (X t₀))) :=
    (htr.continuousAt.comp_continuousWithinAt
      (((h1c t₀ ht₀).sub continuousWithinAt_const).mul (hXc t₀ ht₀))).tendsto
  have hq : Tendsto (fun t ↦ traceForm (ΛR t) (controlMatrix (u t)) /
      traceForm (X t) (controlMatrix (u t))) (𝓝[Icc a b] t₀) (𝓝 0) := by
    have hq0 : Tendsto (fun t ↦ 8 / δ * ∑ k, ∑ l, |ΛR t k l|) (𝓝[Icc a b] t₀) (𝓝 0) := by
      simpa using hsR.const_mul (8 / δ)
    refine squeeze_zero_norm' ?_ hq0
    filter_upwards [hev, self_mem_nhdsWithin] with t ht htI
    have hu := (hpt t htI).1
    have hd := ht _ hu
    have hc : δ ≤ |traceForm (X t) (controlMatrix (u t))| := by
      rw [l3f_traceForm_comm, abs_of_neg (by linarith)]; linarith
    have hn := (l3f_abs_traceForm_le (ΛR t) (controlMatrix (u t))).trans
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (l3f_sum_controlMatrix_le hu)
        (l3f_sum_nonneg _)) two_pos.le)
    rw [Real.norm_eq_abs, abs_div, div_le_iff₀ (hδ.trans_le hc)]
    have hR0 := l3f_sum_nonneg (ΛR t)
    calc |traceForm (ΛR t) (controlMatrix (u t))| ≤ 2 * ((∑ k, ∑ l, |ΛR t k l|) * 4) := hn
      _ = 8 / δ * (∑ k, ∑ l, |ΛR t k l|) * δ := by field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hc (by positivity)
  have hH : Tendsto (fun t ↦ hamiltonian lam (Λ₁ t) (ΛR t) (X t) (u t)) (𝓝[Icc a b] t₀)
      (𝓝 (traceForm (Λ₁ t₀ - (3 / 2 * lam) • J) (X t₀))) := by
    simpa [hamiltonian] using hf.sub hq
  have hW : traceForm (Λ₁ t₀ - (3 / 2 * lam) • J) (X t₀) = 0 :=
    l3f_lim_eq_zero hab ht₀ hH (hmax.mono fun t ht htI ↦ (ht htI).1)
  -- `0 = Λ_R'(t₀) = -[Λ_{1,cost}, X(t₀)]`: `Λ_{1,cost}(t₀) ∈ ℝX(t₀) ∩ X(t₀)^⊥ = 0`
  set W := Λ₁ t₀ - (3 / 2 * lam) • J with hWdef
  have hWtr : W.trace = 0 := by
    rw [hWdef, Matrix.trace_sub, Matrix.trace_smul, (hpt t₀ ht₀).2.2.2.1]
    simp [J, Matrix.trace_fin_two]
  have hWX : W * X t₀ - X t₀ * W = 0 := by
    have e : W * X t₀ - X t₀ * W = -((-Λ₁ t₀ + (3 / 2 * lam) • J) * X t₀ -
        X t₀ * (-Λ₁ t₀ + (3 / 2 * lam) • J)) := by
      simp only [hWdef, Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add,
        Matrix.neg_mul, Matrix.mul_neg]
      abel
    rw [e, hB0, neg_zero]
  have hX0 : X t₀ ≠ 0 := fun h0 ↦ by
    have := hst₀.2.1
    rw [h0, Matrix.det_zero] at this
    norm_num at this
  obtain ⟨k, hk⟩ := orb_centralizer (X t₀) W hst₀.1 hX0 hWtr hWX
  have hk0 : k = 0 := by
    rw [hk, traceForm_smul_left, l3f_traceForm_self hst₀] at hW
    linarith
  have hΛ₁ : Λ₁ t₀ = (3 / 2 * lam) • J := by
    rw [← sub_eq_zero, ← hWdef, hk, hk0, zero_smul]
  -- `λ_cost ≠ 0`, or the reduced costate would vanish at `t₀` (nontriviality, E21)
  refine ⟨fun hl ↦ ?_, hΛ₁⟩
  have hnt := (hpt t₀ ht₀).2.2.2.2.2.2
  rw [hΛ₁, hl, hΛ] at hnt
  simp at hnt

/-- **Theorem 8.2.3** (`thm:circle-singular`). If an extremal lifted trajectory has `Λ_R ≡ 0` on
an interval `(t₁, t₂)`, then on that interval the control is the centre `(⅓, ⅓, ⅓)` of `U_T`
almost everywhere, with `Z_u = J/3`; the trajectory is normal and `X`, `Λ₁` are constant:
`λ_cost ≠ 0`, `X = J`, `Λ₁ = (3/2) λ_cost J`, and `g(t) = g₀ exp(Jt)`, an arc of a circle; and it
is a singular subarc (Definition 6.2.1(3): the Hamiltonian does not involve the control).

Proof (the book's, TeX 7188–7216): `Λ_R = Λ_R' = 0` on the interval, so Lemma 8.2.2
(`lemma8_2_2`) gives `λ_cost ≠ 0` and `Λ₁ ≡ (3/2) λ_cost J`; then
`0 = Λ₁' = [Λ₁, X] = (3/2) λ_cost [J, X]`, so `X ∈ ℝJ ∩ O_J = {J}` (`det X = 1` and the star
condition `X₁₀ > 0` exclude `-J`). `0 = X' = [P, J]` forces `Z_u ∈ ℝJ`, which on `U_T` holds only
at the centre (`Z_{centre} = J/3`). Finally `g' = gJ` gives `g(t) = g(t₁) exp(J(t - t₁))`
(uniqueness for the linear equation).

Formal details. `Λ_R' = 0` at each `t ∈ (t₁, t₂)` because `Λ_R` vanishes near `t`, while
Lemma 8.2.2 gives `Λ_R'(t) = [-Λ_{1,cost}(t), X(t)]`. Since the control is only measurable,
`X' = [P, X]` holds at almost every time (Lebesgue's differentiation theorem for the Carathéodory
solution), which is why the control is the centre almost everywhere. The values at `t₁` and `t₂`
follow by continuity. -/
theorem theorem8_2_3 {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (h : IsExtremalOn a b u g X Λ₁ ΛR lam) {t₁ t₂ : ℝ} (h₁ : a ≤ t₁) (h₁₂ : t₁ < t₂)
    (h₂ : t₂ ≤ b) (hΛ : ∀ t ∈ Ioo t₁ t₂, ΛR t = 0) :
    lam ≠ 0 ∧
      (∀ᵐ t, t ∈ Ioo t₁ t₂ → u t = controlCentre ∧ controlMatrix (u t) = (1 / 3 : ℝ) • J) ∧
      (∀ t ∈ Icc t₁ t₂, X t = J ∧ Λ₁ t = (3 / 2 * lam) • J) ∧
      (∀ t ∈ Icc t₁ t₂, g t = g t₁ * expJ (t - t₁)) ∧
      IsSingularSubarc lam Λ₁ ΛR X t₁ t₂ := by
  obtain ⟨hab, hpt, hgI, hXI, hI1, -, -⟩ := l3f_data h
  have hXc : ContinuousOn X (Icc a b) := Matrix.continuousOn_of_eq_add_integral hXI
  have h1c : ContinuousOn Λ₁ (Icc a b) := Matrix.continuousOn_of_eq_add_integral hI1
  have hgc : ContinuousOn g (Icc a b) := Matrix.continuousOn_of_eq_add_integral hgI
  have hsub : Icc t₁ t₂ ⊆ Icc a b := Icc_subset_Icc h₁ h₂
  have hIoo : ∀ t ∈ Ioo t₁ t₂, t ∈ Ioo a b := fun t ht ↦ ⟨h₁.trans_lt ht.1, ht.2.trans_le h₂⟩
  -- `Λ_R = Λ_R' = 0` on the interval, so Lemma 8.2.2 applies at each of its times
  have hL : ∀ t ∈ Ioo t₁ t₂, lam ≠ 0 ∧ Λ₁ t = (3 / 2 * lam) • J := by
    intro t ht
    have htab := hIoo t ht
    obtain ⟨-, hd, h3⟩ := lemma8_2_2 h (Ioo_subset_Icc_self htab) (hΛ t ht)
    apply h3
    have h0 : HasDerivAtEntrywise ΛR 0 t :=
      (Matrix.hasDerivAtEntrywise_const 0 t).congr_of_eventuallyEq
        (eventually_of_mem (Ioo_mem_nhds ht.1 ht.2) fun s hs ↦ hΛ s hs)
    exact (hd.hasDerivAtEntrywise (Icc_mem_nhds htab.1 htab.2)).unique h0
  have hm : (t₁ + t₂) / 2 ∈ Ioo t₁ t₂ := ⟨by linarith, by linarith⟩
  have hlam : lam ≠ 0 := (hL _ hm).1
  have hΛ₁ : ∀ t ∈ Icc t₁ t₂, Λ₁ t = (3 / 2 * lam) • J :=
    l3f_eqOn_Icc (h1c.mono hsub) h₁₂ fun t ht ↦ (hL t ht).2
  -- `0 = Λ₁' = [Λ₁, X] = (3/2) λ_cost [J, X]`, so `X ∈ ℝJ ∩ O_J = {J}`
  have hXJ' : ∀ t ∈ Ioo t₁ t₂, X t = J := by
    intro t ht
    have htab := hIoo t ht
    have hcont : ContinuousAt (fun s ↦ Λ₁ s * X s - X s * Λ₁ s) t :=
      ((h1c.mul hXc).sub (hXc.mul h1c)).continuousAt (Icc_mem_nhds htab.1 htab.2)
    have hd := Matrix.hasDerivAtEntrywise_of_eq_add_integral hI1 htab hcont
    have h0 : HasDerivAtEntrywise Λ₁ 0 t :=
      (Matrix.hasDerivAtEntrywise_const ((3 / 2 * lam) • J) t).congr_of_eventuallyEq
        (eventually_of_mem (Ioo_mem_nhds ht.1 ht.2) fun s hs ↦ hΛ₁ s (Ioo_subset_Icc_self hs))
    have hbr := hd.unique h0
    rw [hΛ₁ t (Ioo_subset_Icc_self ht), Matrix.smul_mul, Matrix.mul_smul, ← smul_sub] at hbr
    exact l3f_eq_J (hpt t (Ioo_subset_Icc_self htab)).2.2.1
      ((smul_eq_zero.1 hbr).resolve_left (mul_ne_zero (by norm_num) hlam))
  have hXJ : ∀ t ∈ Icc t₁ t₂, X t = J := l3f_eqOn_Icc (hXc.mono hsub) h₁₂ hXJ'
  -- `0 = X' = [P, J]` almost everywhere, which forces the centre of `U_T`
  have hu : ∀ᵐ t, t ∈ Ioo t₁ t₂ → u t = controlCentre ∧
      controlMatrix (u t) = (1 / 3 : ℝ) • J := by
    have hall := Filter.eventually_all.2 fun i ↦ Filter.eventually_all.2 fun j ↦
      ae_hasDerivAt_of_eq_add_integral (hXI i j).1 ⟨le_rfl, hab.le⟩ (hXI i j).2
    filter_upwards [hall] with t ht htI
    have htab := hIoo t htI
    have hv0 : controlP (u t) (X t) * X t - X t * controlP (u t) (X t) = 0 := by
      ext i j
      have h0 : HasDerivAt (fun s ↦ X s i j) 0 t :=
        (hasDerivAt_const t (J i j)).congr_of_eventuallyEq
          (eventually_of_mem (Ioo_mem_nhds htI.1 htI.2) fun s hs ↦ by
            simp only [hXJ' s hs])
      exact (ht i j htab).unique h0
    rw [hXJ t (Ioo_subset_Icc_self htI)] at hv0
    have hc := l3f_eq_centre (hpt t (Ioo_subset_Icc_self htab)).1 hv0
    exact ⟨hc, by rw [hc]; exact l3f_controlMatrix_centre⟩
  -- `g' = gJ`, so `g(t) = g(t₁) exp(J(t - t₁))` (uniqueness for the linear equation)
  have hgJ : ∀ t ∈ Icc t₁ t₂, g t = g t₁ * expJ (t - t₁) := by
    have hgd : ∀ t ∈ Icc a b, HasDerivWithinAtEntrywise g (g t * X t) (Icc a b) t := fun t ht ↦
      Matrix.hasDerivWithinAtEntrywise_of_eq_add_integral hgI ht ((hgc.mul hXc) t ht)
    have hY : Continuous fun t ↦ g t₁ * expJ (t - t₁) :=
      continuous_const.mul (l3f_continuous_expJ.comp (continuous_id.sub continuous_const))
    have heq := Matrix.ODE_solution_unique_mul_right (a := t₁) (b := t₂) (A := X)
      (hXc.mono hsub) (hgc.mono hsub)
      (fun t ht ↦ (hgd t (hsub (Ico_subset_Icc_self ht))).mono hsub) hY.continuousOn
      (fun t ht ↦ ?_) (by rw [sub_self, l3f_expJ_zero, Matrix.mul_one])
    · exact fun t ht ↦ heq ht
    · have hd := ((l3f_hasDerivAt_expJ t₁ t).const_mul (g t₁)).hasDerivWithinAtEntrywise
        (s := Icc t₁ t₂)
      rwa [hXJ t (Ico_subset_Icc_self ht), Matrix.mul_assoc]
  exact ⟨hlam, hu, fun t ht ↦ ⟨hXJ t ht, hΛ₁ t ht⟩, hgJ, l3f_isSingularSubarc_of_zero h₁₂ hΛ⟩

/-- **Theorem 8.2.6** (`thm:circle-iff-singular`). Consider a Pontryagin extremal of the
Reinhardt problem that contains a singular subarc `(t₁, t₂)` along which the Hamiltonian is
independent of the control. Then during that time interval the extremal remains in the singular
locus, and the unique solution of the state and costate equations there is a multi-curve of
circular arcs up to an affine transformation: the control is the centre `(⅓, ⅓, ⅓)` a.e. and
`g(t) = g(t₁) exp(J(t - t₁))`, so `σ_j(t) = g(t) s_j*` is the image under the linear map `g(t₁)`
of an arc of the unit circle. Conversely, the lifted trajectory attached to a multi-curve of
circular arcs (`g(t) = g₀ exp(J(t - t₁))`, `X ≡ J`, centre control) is an extremal singular
subarc lying in the singular locus.

The forward direction is stated for extremal lifted trajectories on an interval (every Pontryagin
extremal restricts to one, `IsPontryaginExtremal.isExtremalOn`); the converse produces a
lift on the interval of the arc (an arc has no boundary conditions of Problem 3.6.2).

Proof (the book's, TeX 7271–7298, "a summary of results already obtained"): forward, the
Hamiltonian is independent of the control, so `Λ_R = 0` on the interval (Lemma 8.2.1,
`lemma8_2_1`, with `X(t)` a star state, Lemma 3.3.4), and Theorem 8.2.3 (`theorem8_2_3`) gives
the circle and the costates, which lie in `𝒮_sing`. Converse (E54: the book derives necessary
conditions; here the lift is exhibited): `λ_cost = -1`, `Λ₁ = -(3/2) J`, `Λ_R = 0` solve the costate
equations (`[J, J] = 0`), `H ≡ 0` is independent of the control, and `(λ_cost, Λ₁) ≠ 0`.
In the forward direction `Λ_R = 0` on `[t₁, t₂]` by continuity, so the lift is in `𝒮_sing` at the
endpoints too. -/
theorem theorem8_2_6 :
    (∀ {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ},
      IsExtremalOn a b u g X Λ₁ ΛR lam → ∀ {t₁ t₂ : ℝ}, a ≤ t₁ → t₂ ≤ b →
        IsSingularSubarc lam Λ₁ ΛR X t₁ t₂ →
        (∀ t ∈ Ioo t₁ t₂, ∀ v ∈ controlSimplex, ∀ w ∈ controlSimplex,
          hamiltonian lam (Λ₁ t) (ΛR t) (X t) v = hamiltonian lam (Λ₁ t) (ΛR t) (X t) w) →
        (∀ t ∈ Icc t₁ t₂, (g t, Λ₁ t, X t, ΛR t) ∈ singularLocus) ∧
          (∀ᵐ t, t ∈ Ioo t₁ t₂ → u t = controlCentre) ∧
          ∀ t ∈ Icc t₁ t₂, g t = g t₁ * expJ (t - t₁)) ∧
      ∀ (t₁ t₂ : ℝ) (g₀ : Mat2), t₁ < t₂ → g₀.det = 1 →
        ∃ (Λ₁ ΛR : ℝ → Mat2) (lam : ℝ),
          IsExtremalOn t₁ t₂ (fun _ ↦ controlCentre) (fun t ↦ g₀ * expJ (t - t₁)) (fun _ ↦ J)
            Λ₁ ΛR lam ∧
          IsSingularSubarc lam Λ₁ ΛR (fun _ ↦ J) t₁ t₂ ∧
          ∀ t ∈ Icc t₁ t₂, (g₀ * expJ (t - t₁), Λ₁ t, J, ΛR t) ∈ singularLocus := by
  refine ⟨fun {a b u g X Λ₁ ΛR lam} h {t₁ t₂} h₁ h₂ hsing hind ↦ ?_, fun t₁ t₂ g₀ h₁₂ hg₀ ↦ ?_⟩
  · -- the Hamiltonian is independent of the control, so `Λ_R = 0` (Lemma 8.2.1, `X(t)` being a
    -- star state, Lemma 3.3.4), and Theorem 8.2.3 gives the circle and the costates
    have h₁₂ := hsing.1
    obtain ⟨-, hpt, -, -, -, hIR, -⟩ := l3f_data h
    have hsub : Icc t₁ t₂ ⊆ Icc a b := Icc_subset_Icc h₁ h₂
    have hR : ∀ t ∈ Ioo t₁ t₂, ΛR t = 0 := by
      intro t ht
      obtain ⟨-, -, hX, -, hRtr, hRX, -⟩ := hpt t (hsub (Ioo_subset_Icc_self ht))
      have hden : ∀ v ∈ controlSimplex, traceForm (X t) (controlMatrix v) ≠ 0 := fun v hv ↦ by
        rw [l3f_traceForm_comm]; exact ((lemma3_3_4 _ hX.1).1 hX.2.2 v hv).ne
      refine (lemma8_2_1 hX.1 hden hRtr hRX).1 fun v hv w hw ↦ ?_
      have := hind t ht v hv w hw
      simp only [hamiltonian] at this
      linarith
    obtain ⟨hlam, hu, hXΛ, hg, -⟩ := theorem8_2_3 h h₁ h₁₂ h₂ hR
    have hR' := l3f_eqOn_Icc ((Matrix.continuousOn_of_eq_add_integral hIR).mono hsub) h₁₂ hR
    exact ⟨fun t ht ↦ ⟨lam, hlam, (hpt t (hsub ht)).2.1, (hXΛ t ht).2, (hXΛ t ht).1, hR' t ht⟩,
      hu.mono fun t ht hti ↦ (ht hti).1, hg⟩
  · -- converse (E54): the lift `λ_cost = -1`, `Λ₁ = -(3/2) J`, `Λ_R = 0` solves the costate
    -- equations (`[J, J] = 0`), and `H ≡ 0` does not depend on the control
    have hT : 0 < t₂ - t₁ := by linarith
    have hJJ : ∀ c : ℝ, (c • J) * J - J * (c • J) = 0 := fun c ↦ by
      rw [Matrix.smul_mul, Matrix.mul_smul, sub_self]
    have hcost : (-(3 / 2) : ℝ) • J - (3 / 2 * -1 : ℝ) • J = 0 := by
      rw [show (3 / 2 * -1 : ℝ) = -(3 / 2) by norm_num, sub_self]
    have hH : ∀ v, hamiltonian (-1) ((-(3 / 2) : ℝ) • J) 0 J v = 0 := fun v ↦ by
      simp only [hamiltonian, hcost, traceForm, Matrix.zero_mul, Matrix.trace_zero, zero_div,
        sub_zero]
    -- an integral curve with zero right-hand side is constant
    have hconst : ∀ (c : Mat2) (v : ℝ → Mat2), (∀ t, v t = 0) →
        IsIntegralCurve (fun _ ↦ c) v (t₂ - t₁) := fun c v hv i j ↦ by
      simp only [hv, Matrix.zero_apply, intervalIntegral.integral_zero, add_zero]
      exact ⟨intervalIntegrable_const, fun _ _ ↦ trivial⟩
    have hP : controlP controlCentre J = ((traceForm (controlMatrix controlCentre) J)⁻¹ *
        (1 / 3 : ℝ)) • J := by
      rw [controlP, l3f_controlMatrix_centre, smul_smul]
    refine ⟨fun _ ↦ (-(3 / 2) : ℝ) • J, fun _ ↦ 0, -1, ?_, l3f_isSingularSubarc_of_zero h₁₂
      fun _ _ ↦ rfl, fun t _ ↦ ⟨-1, by norm_num, by rw [Matrix.det_mul, hg₀, l3f_det_expJ,
        one_mul], by norm_num, rfl, rfl⟩⟩
    refine ⟨⟨hT, measurable_const, fun _ _ ↦ l3f_centre_mem,
      fun t _ ↦ ⟨by rw [Matrix.det_mul, hg₀, l3f_det_expJ, one_mul], l3f_isStarState_J⟩, ?_,
      hconst J _ fun _ ↦ by rw [hP, hJJ]⟩, by norm_num,
      fun _ _ ↦ ⟨by simp [J, Matrix.trace_fin_two], by simp, by simp [traceForm],
        Or.inl (by norm_num)⟩,
      hconst _ _ fun _ ↦ hJJ _, hconst _ _ fun _ ↦ ?_,
      Eventually.of_forall fun _ _ ↦ ⟨hH _, fun v _ ↦ by rw [hH, hH]⟩⟩
    · -- `g(t) = g₀ exp(J(t - t₁))` solves `g' = gJ` (FTC-2)
      have hd : ∀ t, HasDerivAtEntrywise (fun s ↦ g₀ * expJ (t₁ + s - t₁))
          (g₀ * expJ (t₁ + t - t₁) * J) t := fun t ↦ by
        have := (l3f_hasDerivAt_expJ 0 t).const_mul g₀
        simp only [sub_zero] at this
        simp only [add_sub_cancel_left]
        rwa [Matrix.mul_assoc]
      have hc : Continuous fun s ↦ g₀ * expJ (t₁ + s - t₁) * J :=
        (continuous_const.mul (l3f_continuous_expJ.comp ((continuous_const.add continuous_id).sub
          continuous_const))).mul continuous_const
      exact Matrix.eq_add_integral_of_hasDerivWithinAtEntrywise
        (fun t _ ↦ (hd t).hasDerivWithinAtEntrywise)
        (fun i j ↦ (hc.matrix_elem i j).intervalIntegrable _ _)
    · have e : -((-(3 / 2) : ℝ) • J) + (3 / 2 * -1 : ℝ) • J = 0 := by
        rw [show (3 / 2 * -1 : ℝ) = -(3 / 2) by norm_num, neg_add_cancel]
      simp only [e, traceForm, Matrix.mul_zero, Matrix.zero_mul, Matrix.trace_zero, zero_smul,
        sub_self, add_zero]

end SmoothedPolygons
