module

public import SmoothedPolygons.Ch14.LieChart
public import Basic.Analysis.Analytic.l6d_MatrixAnalytic
public import Basic.Analysis.Calculus.MatrixEntrywiseExp
import SmoothedPolygons.Ch7.Isolated.VertexFlow

/-!
# Chapter 14: the closed-form vertex flow is analytic in time and initial data

Step 2 of the proof of Lemma 14.3.1 of Hales–Vajjha, *Packings of Smoothed Polygons* (TeX
11792–11798): "The constant control `Z₀₁₀` solutions `(X(t), Λ₁(t), Λ_R(t))` to the Reinhardt
ODEs are given by matrix exponentials and are hence analytic in time `t` and initial conditions
`(X₀, Λ₁₀, Λ_R0)`." The closed form `iso_vertexFlow m q t` of Chapter 7 is
`X(t) = e^{tP} X₀ e^{-tP}`, `Λ₁(t) = g⁻¹ Λ₁₀ g` with `g = e^{t(X₀ + P)} e^{-tP}`
(`P = Z_{e_m}/⟨Z_{e_m}, X₀⟩`), and `Λ_R(t)` by quadratures. The first two are matrix exponentials;
for `Λ_R` the quadratures are replaced by a matrix exponential (Mathlib has no analytic parametric
integrals): in the frame rotating with `e^{tP}`, the triple
`(e^{-tP} Λ_R e^{tP}, e^{-tP} Λ₁ e^{tP}, e^{-tP} (3/2) J e^{tP})` solves a linear ODE with constant
coefficients (`l6d_rotLin`, depending polynomially on `(X₀, P)`), so it is
`exp (t • L(X₀, P))` applied to its initial value (`l6d_eq_exp_smul_apply_of_hasDerivAt`).

* `l6d_MatAn f x`: the entries of the matrix-valued `f` are analytic at `x`, with its algebra;
* `l6d_analyticAt_vertexFlow`: the entries of `iso_vertexFlow m (q y) (t y)` are analytic in `y`
  when those of `q y` and `t y` are and `⟨Z_{e_m}, X₀⟩ ≠ 0`.
-/

@[expose] public section

namespace SmoothedPolygons

open Matrix Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Entrywise analyticity of matrix-valued functions -/

/-- The entries of the matrix-valued function `f` are analytic at `x`. -/
def l6d_MatAn (f : E → Mat2) (x : E) : Prop := ∀ i j, AnalyticAt ℝ (fun y ↦ f y i j) x

namespace l6d_MatAn

variable {f g : E → Mat2} {x : E}

lemma const (c : Mat2) : l6d_MatAn (fun _ : E ↦ c) x := fun _ _ ↦ analyticAt_const

lemma add (hf : l6d_MatAn f x) (hg : l6d_MatAn g x) : l6d_MatAn (fun y ↦ f y + g y) x :=
  fun i j ↦ by simpa using (hf i j).fun_add (hg i j)

lemma sub (hf : l6d_MatAn f x) (hg : l6d_MatAn g x) : l6d_MatAn (fun y ↦ f y - g y) x :=
  fun i j ↦ by simpa using (hf i j).fun_sub (hg i j)

lemma neg (hf : l6d_MatAn f x) : l6d_MatAn (fun y ↦ -f y) x :=
  fun i j ↦ by simpa using (hf i j).fun_neg

lemma smul {c : E → ℝ} (hc : AnalyticAt ℝ c x) (hf : l6d_MatAn f x) :
    l6d_MatAn (fun y ↦ c y • f y) x :=
  fun i j ↦ by simpa using hc.fun_mul (hf i j)

lemma mul (hf : l6d_MatAn f x) (hg : l6d_MatAn g x) : l6d_MatAn (fun y ↦ f y * g y) x :=
  fun i j ↦ by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using
      ((hf i 0).fun_mul (hg 0 j)).fun_add ((hf i 1).fun_mul (hg 1 j))

lemma traceForm (hf : l6d_MatAn f x) (hg : l6d_MatAn g x) :
    AnalyticAt ℝ (fun y ↦ SmoothedPolygons.traceForm (f y) (g y)) x := by
  have h := hf.mul hg
  simpa [SmoothedPolygons.traceForm, Matrix.trace_fin_two] using (h 0 0).fun_add (h 1 1)

lemma exp_smul {c : E → ℝ} (hc : AnalyticAt ℝ c x) (hf : l6d_MatAn f x) :
    l6d_MatAn (fun y ↦ NormedSpace.exp (c y • f y)) x :=
  l6d_analyticAt_matrix_exp_apply (smul hc hf)

lemma of_entries {a b c d : E → ℝ} (ha : AnalyticAt ℝ a x) (hb : AnalyticAt ℝ b x)
    (hc : AnalyticAt ℝ c x) (hd : AnalyticAt ℝ d x) :
    l6d_MatAn (fun y ↦ !![a y, b y; c y, d y]) x := by
  intro i j
  fin_cases i <;> fin_cases j <;> simpa

end l6d_MatAn

/-! ### The rotating frame: a linear ODE with constant coefficients -/

/-- The phase space of the rotating frame, `𝔤𝔩₂(ℝ)³` written as a function space (so that it
carries Mathlib's product norm). -/
abbrev l6d_W : Type := Fin 3 → Fin 2 → Fin 2 → ℝ

/-- The vector field of the rotating frame: for `(Λ̃_R, N₁, N₂)`,
`(-⟨Λ̃_R, P⟩ [P, X₀] - [N₁ + N₂, X₀], [N₁, X₀ + P], [N₂, P])`. -/
noncomputable def l6d_rotMat (X₀ P A B C : Mat2) : Fin 3 → Mat2 :=
  ![-(SmoothedPolygons.traceForm A P) • (P * X₀ - X₀ * P) - ((B + C) * X₀ - X₀ * (B + C)),
    B * (X₀ + P) - (X₀ + P) * B, C * P - P * C]

/-- The vector field of the rotating frame on `l6d_W`. -/
noncomputable def l6d_rotField (X₀ P : Mat2) (w : l6d_W) : l6d_W :=
  fun a i j ↦ l6d_rotMat X₀ P (Matrix.of (w 0)) (Matrix.of (w 1)) (Matrix.of (w 2)) a i j

/-- The rotating-frame vector field as a linear map. -/
noncomputable def l6d_rotLin (X₀ P : Mat2) : l6d_W →ₗ[ℝ] l6d_W where
  toFun := l6d_rotField X₀ P
  map_add' w w' := by
    funext a i j
    fin_cases a <;>
      simp [l6d_rotField, l6d_rotMat, SmoothedPolygons.traceForm, Matrix.trace_fin_two,
        Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  map_smul' c w := by
    funext a i j
    fin_cases a <;>
      simp [l6d_rotField, l6d_rotMat, SmoothedPolygons.traceForm, Matrix.trace_fin_two,
        Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The rotating-frame vector field as a continuous linear map. -/
noncomputable def l6d_rotL (X₀ P : Mat2) : l6d_W →L[ℝ] l6d_W :=
  LinearMap.toContinuousLinearMap (l6d_rotLin X₀ P)

lemma l6d_rotL_apply (X₀ P : Mat2) (w : l6d_W) : l6d_rotL X₀ P w = l6d_rotField X₀ P w := rfl

/-- The vertex flow in the frame rotating with `e^{tP}`: the conjugates by `e^{-tP}` of `Λ_R(t)`,
`Λ₁(t)` and `(3/2) J`. -/
noncomputable def l6d_rotCurve (m : Fin 3) (q : iso_PhasePt) (t : ℝ) : l6d_W :=
  fun a i j ↦ (![NormedSpace.exp (-t • iso_vfP m q) * iso_vfΛR m q t *
      NormedSpace.exp (t • iso_vfP m q),
    NormedSpace.exp (-t • iso_vfP m q) * iso_vfΛ₁ m q t * NormedSpace.exp (t • iso_vfP m q),
    NormedSpace.exp (-t • iso_vfP m q) * ((3 / 2 : ℝ) • J) * NormedSpace.exp (t • iso_vfP m q)] :
      Fin 3 → Mat2) a i j

/-- The initial value `(Λ_R(0), Λ₁(0), (3/2) J)` in the rotating frame. -/
noncomputable def l6d_rotInit (q : iso_PhasePt) : l6d_W :=
  fun a i j ↦ (![q.2.2, q.2.1, (3 / 2 : ℝ) • J] : Fin 3 → Mat2) a i j

lemma l6d_rotCurve_zero (m : Fin 3) (q : iso_PhasePt) :
    l6d_rotCurve m q 0 = l6d_rotInit q := by
  have h := ivf_vertexFlow_zero m q
  simp only [iso_vertexFlow, Prod.ext_iff] at h
  funext a i j
  fin_cases a <;> simp [l6d_rotCurve, l6d_rotInit, h.2.1, h.2.2]

/-- The rotating-frame curve solves the linear ODE `w' = L(X₀, P) w`. -/
lemma l6d_rotCurve_hasDerivAt (m : Fin 3) (q : iso_PhasePt) (t : ℝ) :
    HasDerivAt (l6d_rotCurve m q) (l6d_rotL q.1 (iso_vfP m q) (l6d_rotCurve m q t)) t := by
  set P := iso_vfP m q with hPdef
  set Ef := NormedSpace.exp (t • P) with hE
  set Ff := NormedSpace.exp (-t • P) with hF
  have hFE : Ff * Ef = 1 := exp_neg_smul_mul_exp_smul P t
  have hEF : Ef * Ff = 1 := exp_smul_mul_exp_neg_smul P t
  have hPF : P * Ff = Ff * P := (commute_exp_smul P (-t)).eq
  have hdE := hasDerivAtEntrywise_exp_smul_const P t
  have hdF := hasDerivAtEntrywise_exp_neg_smul_const' P t
  -- the conjugation `M ↦ F M E`
  have hcX : Ff * iso_vfX m q t * Ef = q.1 := by
    rw [iso_vfX, constControlX, ← hPdef, ← hE, ← hF,
      show Ff * (Ef * q.1 * Ff) * Ef = (Ff * Ef) * q.1 * (Ff * Ef) by noncomm_ring, hFE,
      Matrix.one_mul, Matrix.mul_one]
  have hcP : Ff * P * Ef = P := by rw [← hPF, Matrix.mul_assoc, hFE, Matrix.mul_one]
  have hP : controlP (vertex m) (iso_vfX m q t) = P := ivf_controlP_vfX m q t
  have hconj : ∀ {Y Y' : Mat2} {f : ℝ → Mat2}, HasDerivAtEntrywise f Y' t → f t = Y →
      HasDerivAtEntrywise (fun s ↦ NormedSpace.exp (-s • P) * f s * NormedSpace.exp (s • P))
        (Ff * Y' * Ef - (P * (Ff * Y * Ef) - (Ff * Y * Ef) * P)) t := by
    intro Y Y' f hf hY
    refine ((hdF.mul hf).mul hdE).congr_deriv ?_
    rw [hY, ← hE, ← hF]
    noncomm_ring
  rw [hasDerivAt_pi]
  intro a
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  fin_cases a
  · have key : Ff * costateRHS (-1) (iso_vfΛ₁ m q t) (iso_vfΛR m q t) (iso_vfX m q t)
          (vertex m) * Ef - (P * (Ff * iso_vfΛR m q t * Ef) - (Ff * iso_vfΛR m q t * Ef) * P) =
        l6d_rotMat q.1 P (Ff * iso_vfΛR m q t * Ef) (Ff * iso_vfΛ₁ m q t * Ef)
          (Ff * ((3 / 2 : ℝ) • J) * Ef) 0 := by
      have hc : SmoothedPolygons.traceForm (iso_vfΛR m q t) P =
          SmoothedPolygons.traceForm (Ff * iso_vfΛR m q t * Ef) P := by
        conv_rhs => rw [← hcP]
        rw [poly_traceForm_conj hEF]
      rw [costateRHS, hP, hc]
      simp only [poly_conj_add, poly_conj_sub, poly_conj_smul, poly_conj_neg, poly_conj_mul hEF,
        hcP, hcX]
      simp only [l6d_rotMat, Fin.isValue, Matrix.cons_val_zero]
      ext k l
      simp [Matrix.mul_apply, Fin.sum_univ_two]
      ring
    have h := hconj (ivf_vfΛR_hasDerivAt m q t) rfl
    rw [key] at h
    exact h i j
  · have key : Ff * (iso_vfΛ₁ m q t * iso_vfX m q t - iso_vfX m q t * iso_vfΛ₁ m q t) * Ef -
          (P * (Ff * iso_vfΛ₁ m q t * Ef) - (Ff * iso_vfΛ₁ m q t * Ef) * P) =
        l6d_rotMat q.1 P (Ff * iso_vfΛR m q t * Ef) (Ff * iso_vfΛ₁ m q t * Ef)
          (Ff * ((3 / 2 : ℝ) • J) * Ef) 1 := by
      simp only [poly_conj_sub, poly_conj_mul hEF, hcX]
      simp only [l6d_rotMat, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      noncomm_ring
    have h := hconj (ivf_vfΛ₁_hasDerivAt m q t) rfl
    rw [key] at h
    exact h i j
  · have key : Ff * (0 : Mat2) * Ef -
          (P * (Ff * ((3 / 2 : ℝ) • J) * Ef) - (Ff * ((3 / 2 : ℝ) • J) * Ef) * P) =
        l6d_rotMat q.1 P (Ff * iso_vfΛR m q t * Ef) (Ff * iso_vfΛ₁ m q t * Ef)
          (Ff * ((3 / 2 : ℝ) • J) * Ef) 2 := by
      simp only [l6d_rotMat, Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons]
      noncomm_ring
    have h := hconj (hasDerivAtEntrywise_const ((3 / 2 : ℝ) • J) t) rfl
    rw [key] at h
    exact h i j

/-- `Λ_R(t) = e^{tP} Λ̃_R(t) e^{-tP}` with `Λ̃_R(t)` the first component of
`exp (t • L(X₀, P)) (Λ_R(0), Λ₁(0), (3/2) J)`. -/
lemma l6d_vfΛR_eq_exp (m : Fin 3) (q : iso_PhasePt) (t : ℝ) :
    iso_vfΛR m q t = NormedSpace.exp (t • iso_vfP m q) *
      Matrix.of (NormedSpace.exp (t • l6d_rotL q.1 (iso_vfP m q)) (l6d_rotInit q) 0) *
      NormedSpace.exp (-t • iso_vfP m q) := by
  have h := l6d_eq_exp_smul_apply_of_hasDerivAt (l6d_rotCurve_hasDerivAt m q) t
  rw [l6d_rotCurve_zero] at h
  rw [← h]
  set P := iso_vfP m q
  have hEF : NormedSpace.exp (t • P) * NormedSpace.exp (-t • P) = 1 :=
    exp_smul_mul_exp_neg_smul P t
  change _ = NormedSpace.exp (t • P) *
    (NormedSpace.exp (-t • P) * iso_vfΛR m q t * NormedSpace.exp (t • P)) *
      NormedSpace.exp (-t • P)
  simp only [← Matrix.mul_assoc, hEF, Matrix.one_mul]
  rw [Matrix.mul_assoc, hEF, Matrix.mul_one]

/-! ### Analyticity of the vertex flow -/

section Analytic

variable {q : E → iso_PhasePt} {t : E → ℝ} {x : E}

lemma l6d_MatAn.controlP (m : Fin 3) {X : E → Mat2} (hX : l6d_MatAn X x)
    (hZ : SmoothedPolygons.traceForm (controlMatrix (vertex m)) (X x) ≠ 0) :
    l6d_MatAn (fun y ↦ controlP (vertex m) (X y)) x := by
  have h : AnalyticAt ℝ (fun y ↦ SmoothedPolygons.traceForm (controlMatrix (vertex m)) (X y)) x :=
    (l6d_MatAn.const _).traceForm hX
  exact l6d_MatAn.smul (h.fun_inv hZ) (l6d_MatAn.const _)

lemma l6d_MatAn.vfP (m : Fin 3) (hq1 : l6d_MatAn (fun y ↦ (q y).1) x)
    (hZ : SmoothedPolygons.traceForm (controlMatrix (vertex m)) (q x).1 ≠ 0) :
    l6d_MatAn (fun y ↦ iso_vfP m (q y)) x :=
  l6d_MatAn.controlP m hq1 hZ

lemma l6d_MatAn.vfX (m : Fin 3) (hq1 : l6d_MatAn (fun y ↦ (q y).1) x) (ht : AnalyticAt ℝ t x)
    (hZ : SmoothedPolygons.traceForm (controlMatrix (vertex m)) (q x).1 ≠ 0) :
    l6d_MatAn (fun y ↦ iso_vfX m (q y) (t y)) x := by
  have hP := l6d_MatAn.vfP m hq1 hZ
  exact ((l6d_MatAn.exp_smul ht hP).mul hq1).mul (l6d_MatAn.exp_smul ht.fun_neg hP)

lemma l6d_vfG_inv (m : Fin 3) (q : iso_PhasePt) (t : ℝ) :
    (iso_vfG m q t)⁻¹ = NormedSpace.exp (t • iso_vfP m q) *
      NormedSpace.exp (-t • (q.1 + iso_vfP m q)) := by
  refine Matrix.inv_eq_left_inv ?_
  rw [iso_vfG, constControlG,
    show NormedSpace.exp (t • iso_vfP m q) * NormedSpace.exp (-t • (q.1 + iso_vfP m q)) *
      (NormedSpace.exp (t • (q.1 + iso_vfP m q)) * NormedSpace.exp (-t • iso_vfP m q)) =
      NormedSpace.exp (t • iso_vfP m q) * (NormedSpace.exp (-t • (q.1 + iso_vfP m q)) *
      NormedSpace.exp (t • (q.1 + iso_vfP m q))) * NormedSpace.exp (-t • iso_vfP m q) by
      noncomm_ring,
    exp_neg_smul_mul_exp_smul, Matrix.mul_one, exp_smul_mul_exp_neg_smul]

lemma l6d_MatAn.vfΛ₁ (m : Fin 3) (hq1 : l6d_MatAn (fun y ↦ (q y).1) x)
    (hq2 : l6d_MatAn (fun y ↦ (q y).2.1) x) (ht : AnalyticAt ℝ t x)
    (hZ : SmoothedPolygons.traceForm (controlMatrix (vertex m)) (q x).1 ≠ 0) :
    l6d_MatAn (fun y ↦ iso_vfΛ₁ m (q y) (t y)) x := by
  have hP := l6d_MatAn.vfP m hq1 hZ
  have hA := hq1.add hP
  have hG : l6d_MatAn (fun y ↦ iso_vfG m (q y) (t y)) x :=
    (l6d_MatAn.exp_smul ht hA).mul (l6d_MatAn.exp_smul ht.fun_neg hP)
  have hGi : l6d_MatAn (fun y ↦ (iso_vfG m (q y) (t y))⁻¹) x := by
    simp only [l6d_vfG_inv]
    exact (l6d_MatAn.exp_smul ht hP).mul (l6d_MatAn.exp_smul ht.fun_neg hA)
  exact (hGi.mul hq2).mul hG

/-- The initial value of the rotating frame is analytic. -/
lemma l6d_analyticAt_rotInit (hq2 : l6d_MatAn (fun y ↦ (q y).2.1) x)
    (hq3 : l6d_MatAn (fun y ↦ (q y).2.2) x) :
    AnalyticAt ℝ (fun y ↦ l6d_rotInit (q y)) x := by
  refine AnalyticAt.pi fun a ↦ AnalyticAt.pi fun i ↦ AnalyticAt.pi fun j ↦ ?_
  fin_cases a
  · exact hq3 i j
  · exact hq2 i j
  · exact analyticAt_const

/-- The rotating-frame vector field is analytic in `(X₀, P)`. -/
lemma l6d_analyticAt_rotL {X₀ P : E → Mat2} (hX : l6d_MatAn X₀ x) (hP : l6d_MatAn P x) :
    AnalyticAt ℝ (fun y ↦ l6d_rotL (X₀ y) (P y)) x := by
  refine l6d_analyticAt_clm_of_apply fun w ↦ ?_
  refine AnalyticAt.pi fun a ↦ AnalyticAt.pi fun i ↦ AnalyticAt.pi fun j ↦ ?_
  simp only [l6d_rotL_apply, l6d_rotField]
  have hA := l6d_MatAn.const (E := E) (x := x) (Matrix.of (w 0))
  have hB := l6d_MatAn.const (E := E) (x := x) (Matrix.of (w 1))
  have hC := l6d_MatAn.const (E := E) (x := x) (Matrix.of (w 2))
  fin_cases a
  · exact ((l6d_MatAn.smul (hA.traceForm hP).fun_neg ((hP.mul hX).sub (hX.mul hP))).sub
      (((hB.add hC).mul hX).sub (hX.mul (hB.add hC)))) i j
  · exact ((hB.mul (hX.add hP)).sub ((hX.add hP).mul hB)) i j
  · exact ((hC.mul hP).sub (hP.mul hC)) i j

lemma l6d_MatAn.vfΛR (m : Fin 3) (hq1 : l6d_MatAn (fun y ↦ (q y).1) x)
    (hq2 : l6d_MatAn (fun y ↦ (q y).2.1) x) (hq3 : l6d_MatAn (fun y ↦ (q y).2.2) x)
    (ht : AnalyticAt ℝ t x)
    (hZ : SmoothedPolygons.traceForm (controlMatrix (vertex m)) (q x).1 ≠ 0) :
    l6d_MatAn (fun y ↦ iso_vfΛR m (q y) (t y)) x := by
  have hP := l6d_MatAn.vfP m hq1 hZ
  simp only [l6d_vfΛR_eq_exp]
  refine ((l6d_MatAn.exp_smul ht hP).mul ?_).mul (l6d_MatAn.exp_smul ht.fun_neg hP)
  have hL := l6d_analyticAt_rotL hq1 hP
  have hexp : AnalyticAt ℝ (fun y ↦ NormedSpace.exp (t y • l6d_rotL (q y).1 (iso_vfP m (q y)))) x :=
    (NormedSpace.exp_analytic (𝕂 := ℝ) _).comp (ht.fun_smul hL)
  have happ : AnalyticAt ℝ (fun y ↦ NormedSpace.exp (t y • l6d_rotL (q y).1 (iso_vfP m (q y)))
      (l6d_rotInit (q y))) x :=
    ((ContinuousLinearMap.id ℝ (l6d_W →L[ℝ] l6d_W)).analyticAt_bilinear _).comp₂ hexp
      (l6d_analyticAt_rotInit hq2 hq3)
  intro i j
  exact analyticAt_pi_iff.1 (analyticAt_pi_iff.1 (analyticAt_pi_iff.1 happ 0) i) j

/-- **The vertex flow is analytic in time and initial data** (Step 2 of Lemma 14.3.1): the entries
of `iso_vertexFlow m (q y) (t y)` are analytic at `x` when those of `q y` and `t y` are and
`⟨Z_{e_m}, X₀⟩ ≠ 0` at `x`. -/
theorem l6d_analyticAt_vertexFlow (m : Fin 3) (hq1 : l6d_MatAn (fun y ↦ (q y).1) x)
    (hq2 : l6d_MatAn (fun y ↦ (q y).2.1) x) (hq3 : l6d_MatAn (fun y ↦ (q y).2.2) x)
    (ht : AnalyticAt ℝ t x)
    (hZ : SmoothedPolygons.traceForm (controlMatrix (vertex m)) (q x).1 ≠ 0) :
    l6d_MatAn (fun y ↦ (iso_vertexFlow m (q y) (t y)).1) x ∧
      l6d_MatAn (fun y ↦ (iso_vertexFlow m (q y) (t y)).2.1) x ∧
      l6d_MatAn (fun y ↦ (iso_vertexFlow m (q y) (t y)).2.2) x :=
  ⟨l6d_MatAn.vfX m hq1 ht hZ, l6d_MatAn.vfΛ₁ m hq1 hq2 ht hZ, l6d_MatAn.vfΛR m hq1 hq2 hq3 ht hZ⟩

end Analytic

/-! ### Conservation laws along the vertex flow -/

lemma l6d_traceForm_hasDerivAt {A B : ℝ → Mat2} {A' B' : Mat2} {t : ℝ}
    (hA : HasDerivAtEntrywise A A' t) (hB : HasDerivAtEntrywise B B' t) :
    HasDerivAt (fun s ↦ SmoothedPolygons.traceForm (A s) (B s))
      (SmoothedPolygons.traceForm A' (B t) + SmoothedPolygons.traceForm (A t) B') t := by
  have h := hA.mul hB
  have h2 := (h 0 0).add (h 1 1)
  simp only [Matrix.add_apply] at h2
  convert h2 using 1
  · funext s; simp [SmoothedPolygons.traceForm, Matrix.trace_fin_two]
  · simp [SmoothedPolygons.traceForm, Matrix.trace_fin_two]; ring

/-- The determinant of `X` is conserved along the vertex flow. -/
lemma l6d_vertexFlow_det_fst (m : Fin 3) (q : iso_PhasePt) (t : ℝ) :
    (iso_vertexFlow m q t).1.det = q.1.det := by
  have hEF := exp_smul_mul_exp_neg_smul (iso_vfP m q) t
  have hd := congrArg Matrix.det hEF
  rw [Matrix.det_mul, Matrix.det_one] at hd
  simp only [iso_vertexFlow, iso_vfX, constControlX, Matrix.det_mul]
  linear_combination q.1.det * hd

/-- The determinant of `Λ₁` is conserved along the vertex flow. -/
lemma l6d_vertexFlow_det_snd (m : Fin 3) (q : iso_PhasePt) (t : ℝ) :
    (iso_vertexFlow m q t).2.1.det = q.2.1.det := by
  have hu := ivf_vfG_isUnit m q t
  simp only [iso_vertexFlow, iso_vfΛ₁, Matrix.det_mul, Matrix.det_nonsing_inv]
  rw [mul_comm, ← mul_assoc, Ring.mul_inverse_cancel _ hu, one_mul]

/-- `⟨X, Λ_R⟩` is conserved along the vertex flow. -/
lemma l6d_vertexFlow_traceForm (m : Fin 3) (q : iso_PhasePt) (t : ℝ) :
    SmoothedPolygons.traceForm (iso_vertexFlow m q t).1 (iso_vertexFlow m q t).2.2 =
      SmoothedPolygons.traceForm q.1 q.2.2 := by
  have hd : ∀ s, HasDerivAt (fun u ↦ SmoothedPolygons.traceForm (iso_vertexFlow m q u).1
      (iso_vertexFlow m q u).2.2) 0 s := by
    intro s
    obtain ⟨h1, -, h3, -⟩ := iso_vertexFlow_solution m q s
    refine (l6d_traceForm_hasDerivAt h1 h3).congr_deriv ?_
    simp only [costateRHS, SmoothedPolygons.traceForm, Matrix.trace_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.neg_apply]
    ring
  have h := is_const_of_deriv_eq_zero (fun u ↦ (hd u).differentiableAt) (fun u ↦ (hd u).deriv)
    t 0
  simpa [ivf_vertexFlow_zero] using h

/-- `H(Z_u) = ⟨Λ₁ + (3/2) J, X⟩ - ⟨Λ_R, P_u⟩` (`λ_cost = -1`). -/
lemma l6d_hamiltonian_eq (Λ₁ ΛR X : Mat2) (u : Fin 3 → ℝ) :
    hamiltonian (-1) Λ₁ ΛR X u = SmoothedPolygons.traceForm (Λ₁ + (3 / 2 : ℝ) • J) X -
      SmoothedPolygons.traceForm ΛR (controlP u X) := by
  simp only [hamiltonian, controlP, SmoothedPolygons.traceForm, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul]
  rw [Matrix.trace_mul_comm X]
  norm_num
  ring

/-- `χ_ij = H(e_i) - H(e_j)`. -/
lemma l6d_hamiltonian_sub (Λ₁ ΛR X : Mat2) (i j : Fin 3) :
    hamiltonian (-1) Λ₁ ΛR X (vertex i) - hamiltonian (-1) Λ₁ ΛR X (vertex j) =
      switchingFn i j ΛR X := by
  simp only [l6d_hamiltonian_eq, switchingFn, SmoothedPolygons.traceForm, Matrix.mul_sub,
    Matrix.trace_sub]
  ring

/-- The Hamiltonian `H(e_m)` is conserved along the vertex flow with the control `e_m`. -/
lemma l6d_vertexFlow_hamiltonian (m : Fin 3) (q : iso_PhasePt) (t : ℝ) :
    hamiltonian (-1) (iso_vertexFlow m q t).2.1 (iso_vertexFlow m q t).2.2
      (iso_vertexFlow m q t).1 (vertex m) = hamiltonian (-1) q.2.1 q.2.2 q.1 (vertex m) := by
  have hP : ∀ s, controlP (vertex m) (iso_vertexFlow m q s).1 = iso_vfP m q :=
    fun s ↦ ivf_controlP_vfX m q s
  have hd : ∀ s, HasDerivAt (fun u ↦ hamiltonian (-1) (iso_vertexFlow m q u).2.1
      (iso_vertexFlow m q u).2.2 (iso_vertexFlow m q u).1 (vertex m)) 0 s := by
    intro s
    obtain ⟨h1, h2, h3, -⟩ := iso_vertexFlow_solution m q s
    simp only [l6d_hamiltonian_eq, hP]
    refine ((l6d_traceForm_hasDerivAt (h2.add_const _) h1).sub
      (l6d_traceForm_hasDerivAt h3 (hasDerivAtEntrywise_const _ s))).congr_deriv ?_
    rw [hP s]
    simp only [costateRHS, hP, SmoothedPolygons.traceForm, Matrix.trace_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.neg_apply, Matrix.zero_apply]
    ring
  have h := is_const_of_deriv_eq_zero (fun u ↦ (hd u).differentiableAt) (fun u ↦ (hd u).deriv)
    t 0
  simpa [ivf_vertexFlow_zero] using h

/-! ### The chart is analytic near the exceptional divisor -/

/-- Evaluation of a vector of `ℝ^ι` at a coordinate is analytic. -/
theorem l6d_analyticAt_pi_apply {ι : Type*} [Fintype ι] (i : ι) (x : ι → ℝ) :
    AnalyticAt ℝ (fun y : ι → ℝ ↦ y i) x :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).analyticAt x

attribute [local fun_prop] analyticAt_fst analyticAt_snd l6d_analyticAt_pi_apply

/-- `⟨Z_{e_k}, J⟩ = -2/3` for the three vertices. -/
lemma l6d_traceForm_controlMatrix_J (k : Fin 3) :
    SmoothedPolygons.traceForm (controlMatrix (vertex k)) J = -(2 / 3) := by
  fin_cases k <;>
    simp [SmoothedPolygons.traceForm, controlMatrix, vertex, J, Matrix.trace_fin_two] <;> norm_num

/-- The triple product `⟨X, [Z_{e₂}, Z_{e₃}]⟩` of the linear system (14.1.3) at `X = lieX r x₂₁`:
`-(8/(3√3)) (1 + r x₂₁)`. -/
lemma l6d_traceForm_lieX_bracket (r x21 : ℝ) :
    SmoothedPolygons.traceForm (lieX r x21)
        (controlMatrix (vertex 1) * controlMatrix (vertex 2) -
          controlMatrix (vertex 2) * controlMatrix (vertex 1)) =
      -(8 / (3 * √3)) * (1 + r * x21) := by
  have h3 : (√3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3' : √3 ≠ 0 := by positivity
  simp [SmoothedPolygons.traceForm, controlMatrix, vertex, lieX, Matrix.trace_fin_two]
  field_simp
  ring_nf

variable {g : E → ℝ × (Fin 3 → ℝ)} {x : E}

/-- **Step 1 of the proof of Lemma 14.3.1** (TeX 11788–11792): "Lie algebra coordinates
`(X₀, Λ₁₀, Λ_R0)` are rational functions with nonzero denominators (and hence analytic) in the
variables `(r₀, x̃₀)` and `(1 + r₀ x̃₂₁)⁻¹`." -/
lemma l6d_MatAn_lieChart (hg : AnalyticAt ℝ g x) (h1 : 1 + (g x).1 * (g x).2 0 ≠ 0)
    (h2 : 3 / 2 - (g x).1 ^ 2 * (g x).2 2 ≠ 0) :
    l6d_MatAn (fun y ↦ (lieChart (g y)).1) x ∧ l6d_MatAn (fun y ↦ (lieChart (g y)).2.1) x ∧
      l6d_MatAn (fun y ↦ (lieChart (g y)).2.2) x := by
  have hX : l6d_MatAn (fun y ↦ (lieChart (g y)).1) x := by
    simp only [lieChart, lieX]
    refine l6d_MatAn.of_entries ?_ ?_ ?_ ?_ <;> fun_prop (disch := assumption)
  have hΛ : l6d_MatAn (fun y ↦ (lieChart (g y)).2.1) x := by
    simp only [lieChart, lieΛ₁]
    refine l6d_MatAn.of_entries ?_ ?_ ?_ ?_ <;> fun_prop (disch := assumption)
  refine ⟨hX, hΛ, ?_⟩
  have hZ1 := l6d_MatAn.const (E := E) (x := x) (controlMatrix (vertex 1))
  have hZ2 := l6d_MatAn.const (E := E) (x := x) (controlMatrix (vertex 2))
  have hJ := l6d_MatAn.const (E := E) (x := x) J
  have hh : AnalyticAt ℝ (fun y ↦ reducedHam (lieChart (g y)).2.1 (lieChart (g y)).1) x :=
    (hΛ.add (l6d_MatAn.smul analyticAt_const hJ)).traceForm hX
  have hT : AnalyticAt ℝ (fun y ↦ SmoothedPolygons.traceForm (lieChart (g y)).1
      (controlMatrix (vertex 1) * controlMatrix (vertex 2) -
        controlMatrix (vertex 2) * controlMatrix (vertex 1))) x :=
    hX.traceForm ((hZ1.mul hZ2).sub (hZ2.mul hZ1))
  have hT0 : SmoothedPolygons.traceForm (lieChart (g x)).1
      (controlMatrix (vertex 1) * controlMatrix (vertex 2) -
        controlMatrix (vertex 2) * controlMatrix (vertex 1)) ≠ 0 := by
    rw [show (lieChart (g x)).1 = lieX (g x).1 ((g x).2 0) from rfl, l6d_traceForm_lieX_bracket]
    have h3 : (0 : ℝ) < √3 := by positivity
    exact mul_ne_zero (by rw [neg_ne_zero]; positivity) h1
  have hR : l6d_MatAn (fun y ↦ lieΛR (lieChart (g y)).1 (lieChart (g y)).2.1) x := by
    simp only [lieΛR, sl2Dual]
    refine l6d_MatAn.smul (hT.fun_inv hT0) (((l6d_MatAn.smul analyticAt_const
      ((hZ1.mul hZ2).sub (hZ2.mul hZ1))).add (l6d_MatAn.smul ((hX.traceForm hZ1).fun_mul hh)
      ((hZ2.mul hX).sub (hX.mul hZ2)))).add (l6d_MatAn.smul ((hX.traceForm hZ2).fun_mul hh)
      ((hX.mul hZ1).sub (hZ1.mul hX))))
  exact hR

end SmoothedPolygons
