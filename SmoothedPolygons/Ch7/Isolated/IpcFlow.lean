module

public import SmoothedPolygons.Ch7.Isolated.Defs
public import Basic.Analysis.Calculus.MatrixEntrywiseExp

/-!
# Theorem 7.7.1, step 4 (helper): the vertex flow without integrals

The closed form `iso_vertexFlow` of the extremal flow with the control `e₃` contains the integrals
of the quadrature formula of §7.1. Here they are evaluated: for traceless `A`, `B` with
`⟨A, A⟩ ≠ 0`, the integral of `Ad(e^{-sA}) B = e^{-sA} B e^{sA}` over `[0, t]` and its second
primitive are explicit (`ipc_I`, `ipc_II`), since `[A, [A, B]] = 2⟨A, A⟩B - 2⟨A, B⟩A`. With
`P = Z_{e₃}/⟨Z_{e₃}, X₀⟩` and `Y = X₀ + P`, the flow is then a rational expression in the
entries of `q`, `t` and of `e^{±tP}`, `e^{±tY}` (`ipc_vertexFlow_eq_cf`), valid where
`⟨Z_{e₃}, X₀⟩ ≠ 0` and `⟨Y, Y⟩ ≠ 0`; from this form the flow is `C¹` in `(q, t)` (`ipc_CD_cf`,
using the analyticity of the matrix exponential), and it is affine in `(Λ₁(0), Λ_R(0))`
(`ipc_cf_add_smul`). Both are used for the Poincaré map (`SmoothedPolygons.Ch7.Isolated.Poincare`).
-/

@[expose] public section

namespace SmoothedPolygons

open Matrix Set Filter Topology MeasureTheory

/-! ### Algebra of traceless `2 × 2` matrices -/

/-- A traceless `2 × 2` matrix in coordinates. -/
lemma ipc_eta {A : Mat2} (hA : A.trace = 0) : A = !![A 0 0, A 0 1; A 1 0, -A 0 0] := by
  have h : A 1 1 = -A 0 0 := by rw [Matrix.trace_fin_two] at hA; linarith
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h]

/-- `[A, [A, B]] = 2⟨A, A⟩B - 2⟨A, B⟩A` for traceless `A`, `B`. -/
lemma ipc_bracket_bracket {A B : Mat2} (hA : A.trace = 0) (hB : B.trace = 0) :
    A * (A * B - B * A) - (A * B - B * A) * A =
      (2 * traceForm A A) • B - (2 * traceForm A B) • A := by
  rw [ipc_eta hA, ipc_eta hB]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [traceForm, Matrix.trace_fin_two] <;> ring

/-! ### `Ad(e^{-tA})` and its primitives -/

/-- `Ad(e^{-tA}) B = e^{-tA} B e^{tA}`. -/
noncomputable def ipc_ad (A : Mat2) (t : ℝ) (B : Mat2) : Mat2 :=
  NormedSpace.exp (-t • A) * B * NormedSpace.exp (t • A)

lemma ipc_ad_zero (A B : Mat2) : ipc_ad A 0 B = B := by
  simp [ipc_ad]

lemma ipc_ad_self (A : Mat2) (t : ℝ) : ipc_ad A t A = A := by
  rw [ipc_ad, ← (Matrix.commute_exp_smul A (-t)).eq, Matrix.mul_assoc,
    Matrix.exp_neg_smul_mul_exp_smul, Matrix.mul_one]

lemma ipc_ad_add (A B C : Mat2) (t : ℝ) : ipc_ad A t (B + C) = ipc_ad A t B + ipc_ad A t C := by
  simp only [ipc_ad, Matrix.mul_add, Matrix.add_mul]

lemma ipc_ad_sub (A B C : Mat2) (t : ℝ) : ipc_ad A t (B - C) = ipc_ad A t B - ipc_ad A t C := by
  simp only [ipc_ad, Matrix.mul_sub, Matrix.sub_mul]

lemma ipc_ad_smul (A B : Mat2) (c t : ℝ) : ipc_ad A t (c • B) = c • ipc_ad A t B := by
  simp only [ipc_ad, Matrix.mul_smul, Matrix.smul_mul]

/-- `(Ad(e^{-tA}) B)' = -Ad(e^{-tA}) [A, B]`. -/
lemma ipc_hasDerivAt_ad (A B : Mat2) (t : ℝ) :
    HasDerivAtEntrywise (fun s ↦ ipc_ad A s B) (-ipc_ad A t (A * B - B * A)) t := by
  have h1 := Matrix.hasDerivAtEntrywise_exp_neg_smul_const' A t
  have h2 := Matrix.hasDerivAtEntrywise_exp_smul_const A t
  refine ((h1.mul_const B).mul h2).congr_deriv ?_
  have hc : A * NormedSpace.exp (-t • A) = NormedSpace.exp (-t • A) * A :=
    (Matrix.commute_exp_smul A (-t)).eq
  have hc' : NormedSpace.exp (t • A) * A = A * NormedSpace.exp (t • A) :=
    ((Matrix.commute_exp_smul A t).eq).symm
  simp only [ipc_ad, neg_mul, hc, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hc']
  abel

/-- `∫₀ᵗ Ad(e^{-sA}) B ds`, in closed form. -/
noncomputable def ipc_I (A B : Mat2) (t : ℝ) : Mat2 :=
  (t * (traceForm B A / traceForm A A)) • A +
    (2 * traceForm A A)⁻¹ • ((A * B - B * A) - ipc_ad A t (A * B - B * A))

/-- `∫₀ᵗ ∫₀^σ Ad(e^{-sA}) B ds dσ`, in closed form. -/
noncomputable def ipc_II (A B : Mat2) (t : ℝ) : Mat2 :=
  (t ^ 2 / 2 * (traceForm B A / traceForm A A)) • A +
    (2 * traceForm A A)⁻¹ • (t • (A * B - B * A) - B + ipc_ad A t B)

lemma ipc_I_zero (A B : Mat2) : ipc_I A B 0 = 0 := by
  simp [ipc_I, ipc_ad_zero]

lemma ipc_II_zero (A B : Mat2) : ipc_II A B 0 = 0 := by
  simp [ipc_II, ipc_ad_zero]

lemma ipc_hasDerivAt_I {A B : Mat2} (hA : A.trace = 0) (hB : B.trace = 0)
    (hAA : traceForm A A ≠ 0) (t : ℝ) :
    HasDerivAtEntrywise (fun s ↦ ipc_I A B s) (ipc_ad A t B) t := by
  have hs : HasDerivAt (fun s : ℝ ↦ s * (traceForm B A / traceForm A A))
      (1 * (traceForm B A / traceForm A A)) t := (hasDerivAt_id t).mul_const _
  refine ((hasDerivAtEntrywise_smul_const hs A).add
    (((hasDerivAtEntrywise_const (A * B - B * A) t).sub
      (ipc_hasDerivAt_ad A (A * B - B * A) t)).const_smul ((2 * traceForm A A)⁻¹))).congr_deriv ?_
  have hBA : traceForm B A = traceForm A B := Matrix.trace_mul_comm B A
  rw [ipc_bracket_bracket hA hB, ipc_ad_sub, ipc_ad_smul, ipc_ad_smul, ipc_ad_self, hBA]
  have h2 : (2 * traceForm A A) ≠ 0 := mul_ne_zero two_ne_zero hAA
  rw [zero_sub, neg_neg, smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ h2, one_smul, one_mul,
    ← sub_eq_zero]
  rw [show (2 * traceForm A A)⁻¹ * (2 * traceForm A B) = traceForm A B / traceForm A A by
    field_simp]
  abel

lemma ipc_hasDerivAt_II (A B : Mat2) (t : ℝ) :
    HasDerivAtEntrywise (fun s ↦ ipc_II A B s) (ipc_I A B t) t := by
  have hs : HasDerivAt (fun s : ℝ ↦ s ^ 2 / 2 * (traceForm B A / traceForm A A))
      (((2 : ℕ) * t ^ (2 - 1) * 1) / 2 * (traceForm B A / traceForm A A)) t :=
    (((hasDerivAt_id t).pow 2).div_const 2).mul_const _
  have ht : HasDerivAt (fun s : ℝ ↦ s) 1 t := hasDerivAt_id t
  refine ((hasDerivAtEntrywise_smul_const hs A).add
    ((((hasDerivAtEntrywise_smul_const ht (A * B - B * A)).sub_const B).add
      (ipc_hasDerivAt_ad A B t)).const_smul ((2 * traceForm A A)⁻¹))).congr_deriv ?_
  simp only [ipc_I]
  rw [show ((2 : ℕ) * t ^ (2 - 1) * 1) / 2 = t by push_cast; ring, one_smul]
  abel

/-! ### The vertex flow `e₃` in closed form -/

/-- `Y = X₀ + P`, `P = Z_{e₃}/⟨Z_{e₃}, X₀⟩`. -/
noncomputable def ipc_Y (q : iso_PhasePt) : Mat2 := q.1 + iso_vfP 2 q

/-- `K = [X₀, P]`. -/
noncomputable def ipc_K (q : iso_PhasePt) : Mat2 := q.1 * iso_vfP 2 q - iso_vfP 2 q * q.1

/-- `M(s) = Ad(e^{-sY}) Λ₁(0) + (3/2) Ad(e^{-sP}) J`. -/
noncomputable def ipc_M (q : iso_PhasePt) (s : ℝ) : Mat2 :=
  ipc_ad (ipc_Y q) s q.2.1 + (3 / 2 : ℝ) • ipc_ad (iso_vfP 2 q) s J

/-- `∫₀ᵗ M`. -/
noncomputable def ipc_IM (q : iso_PhasePt) (t : ℝ) : Mat2 :=
  ipc_I (ipc_Y q) q.2.1 t + (3 / 2 : ℝ) • ipc_I (iso_vfP 2 q) J t

/-- `∫₀ᵗ ∫₀^σ M`. -/
noncomputable def ipc_IIM (q : iso_PhasePt) (t : ℝ) : Mat2 :=
  ipc_II (ipc_Y q) q.2.1 t + (3 / 2 : ℝ) • ipc_II (iso_vfP 2 q) J t

/-- `Λ₁(t) = e^{tP} e^{-tY} Λ₁(0) e^{tY} e^{-tP}`. -/
noncomputable def ipc_cfΛ₁ (q : iso_PhasePt) (t : ℝ) : Mat2 :=
  NormedSpace.exp (t • iso_vfP 2 q) * NormedSpace.exp (-t • ipc_Y q) * q.2.1 *
    NormedSpace.exp (t • ipc_Y q) * NormedSpace.exp (-t • iso_vfP 2 q)

/-- `Λ_R(t)` without integrals. -/
noncomputable def ipc_cfΛR (q : iso_PhasePt) (t : ℝ) : Mat2 :=
  NormedSpace.exp (t • iso_vfP 2 q) *
    (q.2.2 - (t * traceForm q.2.2 (iso_vfP 2 q) - traceForm (ipc_IIM q t) (ipc_K q)) •
        (iso_vfP 2 q * q.1 - q.1 * iso_vfP 2 q) -
      (ipc_IM q t * q.1 - q.1 * ipc_IM q t)) *
    NormedSpace.exp (-t • iso_vfP 2 q)

/-- The vertex flow with control `e₃`, without integrals. -/
noncomputable def ipc_cf (q : iso_PhasePt) (t : ℝ) : iso_PhasePt :=
  (iso_vfX 2 q t, ipc_cfΛ₁ q t, ipc_cfΛR q t)

lemma ipc_trace_Z2 : (controlMatrix (vertex 2)).trace = 0 := by
  simp [controlMatrix, vertex, Matrix.trace_fin_two]
  ring

lemma ipc_trace_J : J.trace = 0 := by
  simp [J, Matrix.trace_fin_two]

lemma ipc_trace_vfP (q : iso_PhasePt) : (iso_vfP 2 q).trace = 0 := by
  rw [iso_vfP, controlP, Matrix.trace_smul, ipc_trace_Z2, smul_zero]

lemma ipc_traceForm_vfP (q : iso_PhasePt) (hc : traceForm (controlMatrix (vertex 2)) q.1 ≠ 0) :
    traceForm (iso_vfP 2 q) (iso_vfP 2 q) ≠ 0 := by
  have hZ : traceForm (controlMatrix (vertex 2)) (controlMatrix (vertex 2)) = 2 / 3 := by
    have h3 : (0 : ℝ) < √3 := by positivity
    have h := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    simp [traceForm, controlMatrix, vertex, Matrix.trace_fin_two]
    field_simp
    linarith
  have e : traceForm (iso_vfP 2 q) (iso_vfP 2 q) =
      (traceForm (controlMatrix (vertex 2)) q.1)⁻¹ ^ 2 *
        traceForm (controlMatrix (vertex 2)) (controlMatrix (vertex 2)) := by
    simp only [iso_vfP, controlP, traceForm, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
      smul_eq_mul]
    ring
  rw [e, hZ]
  exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hc)) (by norm_num)

lemma ipc_trace_Y (q : iso_PhasePt) (hX : q.1.trace = 0) : (ipc_Y q).trace = 0 := by
  rw [ipc_Y, Matrix.trace_add, hX, ipc_trace_vfP, add_zero]

/-- `M = (∫ M)'`. -/
lemma ipc_hasDerivAt_IM (q : iso_PhasePt) (hX : q.1.trace = 0) (hL : q.2.1.trace = 0)
    (hc : traceForm (controlMatrix (vertex 2)) q.1 ≠ 0) (hY : traceForm (ipc_Y q) (ipc_Y q) ≠ 0)
    (t : ℝ) : HasDerivAtEntrywise (fun s ↦ ipc_IM q s) (ipc_M q t) t :=
  (ipc_hasDerivAt_I (ipc_trace_Y q hX) hL hY t).add
    ((ipc_hasDerivAt_I (ipc_trace_vfP q) ipc_trace_J (ipc_traceForm_vfP q hc) t).const_smul _)

lemma ipc_hasDerivAt_IIM (q : iso_PhasePt) (t : ℝ) :
    HasDerivAtEntrywise (fun s ↦ ipc_IIM q s) (ipc_IM q t) t :=
  (ipc_hasDerivAt_II _ _ t).add ((ipc_hasDerivAt_II _ _ t).const_smul _)

lemma ipc_hasDerivAt_M (q : iso_PhasePt) (t : ℝ) :
    HasDerivAtEntrywise (fun s ↦ ipc_M q s)
      (-ipc_ad (ipc_Y q) t (ipc_Y q * q.2.1 - q.2.1 * ipc_Y q) +
        (3 / 2 : ℝ) • -ipc_ad (iso_vfP 2 q) t (iso_vfP 2 q * J - J * iso_vfP 2 q)) t :=
  (ipc_hasDerivAt_ad _ _ t).add ((ipc_hasDerivAt_ad _ _ t).const_smul _)

lemma ipc_IM_zero (q : iso_PhasePt) : ipc_IM q 0 = 0 := by
  simp [ipc_IM, ipc_I_zero]

lemma ipc_IIM_zero (q : iso_PhasePt) : ipc_IIM q 0 = 0 := by
  simp [ipc_IIM, ipc_II_zero]

lemma ipc_continuous_traceForm_M (q : iso_PhasePt) (K : Mat2) :
    Continuous fun s ↦ traceForm (ipc_M q s) K :=
  continuous_iff_continuousAt.2 fun s ↦ ((ipc_hasDerivAt_M q s).mul_const K).trace.continuousAt

lemma ipc_continuous_bracket_M (q : iso_PhasePt) (X : Mat2) (i j : Fin 2) :
    Continuous fun s ↦ (ipc_M q s * X - X * ipc_M q s) i j :=
  continuous_iff_continuousAt.2 fun s ↦
    ((((ipc_hasDerivAt_M q s).mul_const X).sub
      ((ipc_hasDerivAt_M q s).const_mul X)) i j).continuousAt

/-- `iso_vfM` is `M`: `e^{-sP} g(s)⁻¹ = e^{-sY}`. -/
lemma ipc_vfM_eq (q : iso_PhasePt) (s : ℝ) : iso_vfM 2 q s = ipc_M q s := by
  set P := iso_vfP 2 q
  set Y := ipc_Y q
  have hG : (iso_vfG 2 q s)⁻¹ = NormedSpace.exp (s • P) * NormedSpace.exp (-s • Y) := by
    refine Matrix.inv_eq_left_inv ?_
    simp only [iso_vfG, constControlG]
    change NormedSpace.exp (s • P) * NormedSpace.exp (-s • Y) *
      (NormedSpace.exp (s • Y) * NormedSpace.exp (-s • P)) = 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (NormedSpace.exp (-s • Y)),
      Matrix.exp_neg_smul_mul_exp_smul, Matrix.one_mul, Matrix.exp_smul_mul_exp_neg_smul]
  have h1 := Matrix.exp_neg_smul_mul_exp_smul P s
  simp only [iso_vfM, iso_vfΛ₁, hG, ipc_M, ipc_ad]
  change NormedSpace.exp (-s • P) *
      (NormedSpace.exp (s • P) * NormedSpace.exp (-s • Y) * q.2.1 *
        (NormedSpace.exp (s • Y) * NormedSpace.exp (-s • P)) + (3 / 2 : ℝ) • J) *
      NormedSpace.exp (s • P) = _
  rw [Matrix.mul_add, Matrix.add_mul]
  congr 1
  · simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
    simp only [Matrix.mul_assoc, h1, Matrix.mul_one]
    rfl
  · simp only [Matrix.mul_smul, Matrix.smul_mul]
    rfl

/-- `c(σ) = ⟨Λ_R(0), P⟩ - ⟨∫₀^σ M, K⟩`. -/
lemma ipc_vfC_eq (q : iso_PhasePt) (hX : q.1.trace = 0) (hL : q.2.1.trace = 0)
    (hc : traceForm (controlMatrix (vertex 2)) q.1 ≠ 0) (hY : traceForm (ipc_Y q) (ipc_Y q) ≠ 0)
    (σ : ℝ) :
    iso_vfC 2 q σ = traceForm q.2.2 (iso_vfP 2 q) - traceForm (ipc_IM q σ) (ipc_K q) := by
  have hd : ∀ s, HasDerivAt (fun s ↦ traceForm (ipc_IM q s) (ipc_K q))
      (traceForm (ipc_M q s) (ipc_K q)) s := fun s ↦
    ((ipc_hasDerivAt_IM q hX hL hc hY s).mul_const (ipc_K q)).trace
  have hcont := ipc_continuous_traceForm_M q (ipc_K q)
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := σ)
    (fun s _ ↦ hd s) (hcont.intervalIntegrable 0 σ)
  simp only [iso_vfC, ipc_vfM_eq, ipc_K] at hI ⊢
  rw [hI, ipc_IM_zero]
  simp [traceForm]

lemma ipc_continuous_vfC (q : iso_PhasePt) (hX : q.1.trace = 0) (hL : q.2.1.trace = 0)
    (hc : traceForm (controlMatrix (vertex 2)) q.1 ≠ 0) (hY : traceForm (ipc_Y q) (ipc_Y q) ≠ 0) :
    Continuous (iso_vfC 2 q) := by
  have hd : ∀ s, HasDerivAt (fun s ↦ traceForm (ipc_IM q s) (ipc_K q))
      (traceForm (ipc_M q s) (ipc_K q)) s := fun s ↦
    ((ipc_hasDerivAt_IM q hX hL hc hY s).mul_const (ipc_K q)).trace
  have : iso_vfC 2 q = fun σ ↦ traceForm q.2.2 (iso_vfP 2 q) - traceForm (ipc_IM q σ) (ipc_K q) :=
    funext (ipc_vfC_eq q hX hL hc hY)
  rw [this]
  exact continuous_const.sub (continuous_iff_continuousAt.2 fun s ↦ (hd s).continuousAt)

/-- `∫₀ᵗ c = t⟨Λ_R(0), P⟩ - ⟨∫₀ᵗ∫₀^σ M, K⟩`. -/
lemma ipc_integral_vfC (q : iso_PhasePt) (hX : q.1.trace = 0) (hL : q.2.1.trace = 0)
    (hc : traceForm (controlMatrix (vertex 2)) q.1 ≠ 0) (hY : traceForm (ipc_Y q) (ipc_Y q) ≠ 0)
    (t : ℝ) :
    ∫ σ in (0 : ℝ)..t, iso_vfC 2 q σ =
      t * traceForm q.2.2 (iso_vfP 2 q) - traceForm (ipc_IIM q t) (ipc_K q) := by
  have hd : ∀ s, HasDerivAt
      (fun s ↦ s * traceForm q.2.2 (iso_vfP 2 q) - traceForm (ipc_IIM q s) (ipc_K q))
      (iso_vfC 2 q s) s := fun s ↦ by
    rw [ipc_vfC_eq q hX hL hc hY]
    have h := ((hasDerivAt_id s).mul_const (traceForm q.2.2 (iso_vfP 2 q))).sub
      (((ipc_hasDerivAt_IIM q s).mul_const (ipc_K q)).trace)
    rw [one_mul] at h
    exact h
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t)
    (fun s _ ↦ hd s) ((ipc_continuous_vfC q hX hL hc hY).intervalIntegrable 0 t)
  rw [hI, ipc_IIM_zero]
  simp [traceForm]

/-- `∫₀ᵗ [M, X₀] = [∫₀ᵗ M, X₀]`. -/
lemma ipc_integral_bracket (q : iso_PhasePt) (hX : q.1.trace = 0) (hL : q.2.1.trace = 0)
    (hc : traceForm (controlMatrix (vertex 2)) q.1 ≠ 0) (hY : traceForm (ipc_Y q) (ipc_Y q) ≠ 0)
    (t : ℝ) :
    (Matrix.of fun i j ↦ ∫ s in (0 : ℝ)..t, (iso_vfM 2 q s * q.1 - q.1 * iso_vfM 2 q s) i j) =
      ipc_IM q t * q.1 - q.1 * ipc_IM q t := by
  ext i j
  have hd : ∀ s, HasDerivAt (fun s ↦ (ipc_IM q s * q.1 - q.1 * ipc_IM q s) i j)
      ((ipc_M q s * q.1 - q.1 * ipc_M q s) i j) s := fun s ↦
    (((ipc_hasDerivAt_IM q hX hL hc hY s).mul_const q.1).sub
      ((ipc_hasDerivAt_IM q hX hL hc hY s).const_mul q.1)) i j
  have hcont := ipc_continuous_bracket_M q q.1 i j
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t)
    (fun s _ ↦ hd s) (hcont.intervalIntegrable 0 t)
  simp only [Matrix.of_apply, ipc_vfM_eq]
  rw [hI, ipc_IM_zero]
  simp

/-- **The vertex flow without integrals.** -/
theorem ipc_vertexFlow_eq_cf (q : iso_PhasePt) (hX : q.1.trace = 0) (hL : q.2.1.trace = 0)
    (hc : traceForm (controlMatrix (vertex 2)) q.1 ≠ 0) (hY : traceForm (ipc_Y q) (ipc_Y q) ≠ 0)
    (t : ℝ) : iso_vertexFlow 2 q t = ipc_cf q t := by
  have hG : (iso_vfG 2 q t)⁻¹ =
      NormedSpace.exp (t • iso_vfP 2 q) * NormedSpace.exp (-t • ipc_Y q) := by
    refine Matrix.inv_eq_left_inv ?_
    simp only [iso_vfG, constControlG]
    change NormedSpace.exp (t • iso_vfP 2 q) * NormedSpace.exp (-t • ipc_Y q) *
      (NormedSpace.exp (t • ipc_Y q) * NormedSpace.exp (-t • iso_vfP 2 q)) = 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (NormedSpace.exp (-t • ipc_Y q)),
      Matrix.exp_neg_smul_mul_exp_smul, Matrix.one_mul, Matrix.exp_smul_mul_exp_neg_smul]
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · change (iso_vfG 2 q t)⁻¹ * q.2.1 * iso_vfG 2 q t = _
    rw [hG]
    simp only [ipc_cf, ipc_cfΛ₁, iso_vfG, constControlG, ipc_Y, Matrix.mul_assoc]
  · change NormedSpace.exp (t • iso_vfP 2 q) * _ * NormedSpace.exp (-t • iso_vfP 2 q) = _
    rw [ipc_integral_vfC q hX hL hc hY, ipc_integral_bracket q hX hL hc hY]
    rfl

/-! ### The flow is affine in the costate -/

/-- The linear part of `Λ_R(t)` in `(Λ₁(0), Λ_R(0))` (the closed form without the `J`-term). -/
noncomputable def ipc_linΛR (q : iso_PhasePt) (t : ℝ) : Mat2 :=
  NormedSpace.exp (t • iso_vfP 2 q) *
    (q.2.2 - (t * traceForm q.2.2 (iso_vfP 2 q) -
          traceForm (ipc_II (ipc_Y q) q.2.1 t) (ipc_K q)) •
        (iso_vfP 2 q * q.1 - q.1 * iso_vfP 2 q) -
      (ipc_I (ipc_Y q) q.2.1 t * q.1 - q.1 * ipc_I (ipc_Y q) q.2.1 t)) *
    NormedSpace.exp (-t • iso_vfP 2 q)

lemma ipc_I_add_smul (A B C : Mat2) (s t : ℝ) :
    ipc_I A (B + s • C) t = ipc_I A B t + s • ipc_I A C t := by
  simp only [ipc_I, ipc_ad_sub, ipc_ad_add, ipc_ad_smul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, traceForm, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
  match_scalars <;> ring

lemma ipc_II_add_smul (A B C : Mat2) (s t : ℝ) :
    ipc_II A (B + s • C) t = ipc_II A B t + s • ipc_II A C t := by
  simp only [ipc_II, ipc_ad_add, ipc_ad_smul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, traceForm, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
  match_scalars <;> ring

/-- The closed form is affine in `(Λ₁(0), Λ_R(0))`. -/
lemma ipc_cf_add_smul (X L Rr δL δR : Mat2) (s t : ℝ) :
    ipc_cf (X, L + s • δL, Rr + s • δR) t =
      ((ipc_cf (X, L, Rr) t).1, (ipc_cf (X, L, Rr) t).2.1 + s • ipc_cfΛ₁ (X, δL, δR) t,
        (ipc_cf (X, L, Rr) t).2.2 + s • ipc_linΛR (X, δL, δR) t) := by
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · simp only [ipc_cf, ipc_cfΛ₁, ipc_Y, iso_vfP, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul]
  · simp only [ipc_cf, ipc_cfΛR, ipc_linΛR, ipc_IM, ipc_IIM, ipc_Y, ipc_K, iso_vfP]
    rw [ipc_I_add_smul, ipc_II_add_smul]
    simp only [traceForm, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul, Matrix.mul_sub,
      Matrix.sub_mul]
    module

/-! ### Smoothness of the closed form -/

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- All entries of a matrix-valued function are `C¹` at `x`. -/
def ipc_CD (A : E → Mat2) (x : E) : Prop := ∀ i j, ContDiffAt ℝ 1 (fun y ↦ A y i j) x

lemma ipc_CD.const (M : Mat2) (x : E) : ipc_CD (fun _ ↦ M) x := fun _ _ ↦ contDiffAt_const

lemma ipc_CD.add {A B : E → Mat2} {x : E} (hA : ipc_CD A x) (hB : ipc_CD B x) :
    ipc_CD (fun y ↦ A y + B y) x := fun i j ↦ (hA i j).add (hB i j)

lemma ipc_CD.sub {A B : E → Mat2} {x : E} (hA : ipc_CD A x) (hB : ipc_CD B x) :
    ipc_CD (fun y ↦ A y - B y) x := fun i j ↦ (hA i j).sub (hB i j)

lemma ipc_CD.mul {A B : E → Mat2} {x : E} (hA : ipc_CD A x) (hB : ipc_CD B x) :
    ipc_CD (fun y ↦ A y * B y) x := fun i j ↦ by
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  exact ((hA i 0).mul (hB 0 j)).add ((hA i 1).mul (hB 1 j))

lemma ipc_CD.smul {c : E → ℝ} {A : E → Mat2} {x : E} (hc : ContDiffAt ℝ 1 c x)
    (hA : ipc_CD A x) : ipc_CD (fun y ↦ c y • A y) x := fun i j ↦ by
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact hc.mul (hA i j)

lemma ipc_CD.trace {A : E → Mat2} {x : E} (hA : ipc_CD A x) :
    ContDiffAt ℝ 1 (fun y ↦ (A y).trace) x := by
  simp only [Matrix.trace_fin_two]
  exact (hA 0 0).add (hA 1 1)

lemma ipc_CD.tf {A B : E → Mat2} {x : E} (hA : ipc_CD A x) (hB : ipc_CD B x) :
    ContDiffAt ℝ 1 (fun y ↦ traceForm (A y) (B y)) x :=
  (hA.mul hB).trace

lemma ipc_CD.of_entries {A : E → Mat2} {x : E} (hA : ipc_CD A x) :
    ∀ i j, ContDiffAt ℝ 1 (fun y ↦ A y i j) x := hA

open scoped Matrix.Norms.Operator in
/-- The matrix exponential is smooth, entry by entry. -/
lemma ipc_CD.exp {A : E → Mat2} {x : E} (hA : ipc_CD A x) :
    ipc_CD (fun y ↦ NormedSpace.exp (A y)) x := by
  have : @CompleteSpace (Matrix (Fin 2) (Fin 2) ℝ) PseudoMetricSpace.toUniformSpace := by
    exact inferInstanceAs (CompleteSpace (Matrix (Fin 2) (Fin 2) ℝ))
  have hA' : ContDiffAt ℝ 1 A x := by
    have e : A = fun y ↦ ∑ i : Fin 2, ∑ j : Fin 2, A y i j • Matrix.single i j (1 : ℝ) := by
      funext y
      conv_lhs => rw [Matrix.matrix_eq_sum_single (A y)]
      simp only [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [e]
    exact ContDiffAt.sum fun i _ ↦ ContDiffAt.sum fun j _ ↦ (hA i j).smul contDiffAt_const
  have hexp := (NormedSpace.analyticAt_exp_of_mem_ball (𝕂 := ℝ) (A x) (by
    rw [NormedSpace.expSeries_radius_eq_top]; simp)).contDiffAt (n := 1)
  intro i j
  have hl : ContDiff ℝ 1 (fun M : Mat2 ↦ M i j) :=
    (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℝ i j)).contDiff
  exact hl.contDiffAt.comp x (hexp.comp x hA')

lemma ipc_CD.ad {A B : E → Mat2} {c : E → ℝ} {x : E} (hA : ipc_CD A x) (hB : ipc_CD B x)
    (hc : ContDiffAt ℝ 1 c x) : ipc_CD (fun y ↦ ipc_ad (A y) (c y) (B y)) x :=
  (((ipc_CD.smul hc.neg hA).exp).mul hB).mul (ipc_CD.smul hc hA).exp

lemma ipc_CD.I {A B : E → Mat2} {c : E → ℝ} {x : E} (hA : ipc_CD A x) (hB : ipc_CD B x)
    (hc : ContDiffAt ℝ 1 c x) (hAA : traceForm (A x) (A x) ≠ 0) :
    ipc_CD (fun y ↦ ipc_I (A y) (B y) (c y)) x := by
  have hinv : ContDiffAt ℝ 1 (fun y ↦ (traceForm (A y) (A y))⁻¹) x := (hA.tf hA).inv hAA
  have hinv2 : ContDiffAt ℝ 1 (fun y ↦ (2 * traceForm (A y) (A y))⁻¹) x :=
    (contDiffAt_const.mul (hA.tf hA)).inv (mul_ne_zero two_ne_zero hAA)
  have hC : ipc_CD (fun y ↦ A y * B y - B y * A y) x := (hA.mul hB).sub (hB.mul hA)
  simp only [ipc_I, div_eq_mul_inv]
  exact (ipc_CD.smul (hc.mul ((hB.tf hA).mul hinv)) hA).add
    (ipc_CD.smul hinv2 (hC.sub (ipc_CD.ad hA hC hc)))

lemma ipc_CD.II {A B : E → Mat2} {c : E → ℝ} {x : E} (hA : ipc_CD A x) (hB : ipc_CD B x)
    (hc : ContDiffAt ℝ 1 c x) (hAA : traceForm (A x) (A x) ≠ 0) :
    ipc_CD (fun y ↦ ipc_II (A y) (B y) (c y)) x := by
  have hinv : ContDiffAt ℝ 1 (fun y ↦ (traceForm (A y) (A y))⁻¹) x := (hA.tf hA).inv hAA
  have hinv2 : ContDiffAt ℝ 1 (fun y ↦ (2 * traceForm (A y) (A y))⁻¹) x :=
    (contDiffAt_const.mul (hA.tf hA)).inv (mul_ne_zero two_ne_zero hAA)
  have hC : ipc_CD (fun y ↦ A y * B y - B y * A y) x := (hA.mul hB).sub (hB.mul hA)
  simp only [ipc_II, div_eq_mul_inv]
  exact (ipc_CD.smul (((hc.pow 2).mul contDiffAt_const).mul ((hB.tf hA).mul hinv)) hA).add
    (ipc_CD.smul hinv2 (((ipc_CD.smul hc hC).sub hB).add (ipc_CD.ad hA hB hc)))

/-- The parameters `(v, t) ↦ (q(v), t)` of the flow in coordinates. -/
abbrev ipc_E : Type := (Fin 9 → ℝ) × ℝ

lemma ipc_contDiffAt_coord (k : Fin 9) (p : ipc_E) :
    ContDiffAt ℝ 1 (fun p : ipc_E ↦ p.1 k) p :=
  (contDiffAt_apply ℝ (fun _ : Fin 9 ↦ ℝ) k p.1).comp p contDiffAt_fst

lemma ipc_CD_X (p : ipc_E) : ipc_CD (fun p : ipc_E ↦ (iso_phaseOfCoords p.1).1) p := by
  intro i j
  fin_cases i <;> fin_cases j
  exacts [ipc_contDiffAt_coord 0 p, ipc_contDiffAt_coord 1 p, ipc_contDiffAt_coord 2 p,
    (ipc_contDiffAt_coord 0 p).neg]

lemma ipc_CD_L (p : ipc_E) : ipc_CD (fun p : ipc_E ↦ (iso_phaseOfCoords p.1).2.1) p := by
  intro i j
  fin_cases i <;> fin_cases j
  exacts [ipc_contDiffAt_coord 3 p, ipc_contDiffAt_coord 4 p, ipc_contDiffAt_coord 5 p,
    (ipc_contDiffAt_coord 3 p).neg]

lemma ipc_CD_R (p : ipc_E) : ipc_CD (fun p : ipc_E ↦ (iso_phaseOfCoords p.1).2.2) p := by
  intro i j
  fin_cases i <;> fin_cases j
  exacts [ipc_contDiffAt_coord 6 p, ipc_contDiffAt_coord 7 p, ipc_contDiffAt_coord 8 p,
    (ipc_contDiffAt_coord 6 p).neg]

/-- The conditions under which the closed form is the flow, at the parameter `v`. -/
def ipc_Good (v : Fin 9 → ℝ) : Prop :=
  traceForm (controlMatrix (vertex 2)) (iso_phaseOfCoords v).1 ≠ 0 ∧
    traceForm (ipc_Y (iso_phaseOfCoords v)) (ipc_Y (iso_phaseOfCoords v)) ≠ 0

lemma ipc_CD_P (p : ipc_E)
    (hc : traceForm (controlMatrix (vertex 2)) (iso_phaseOfCoords p.1).1 ≠ 0) :
    ipc_CD (fun p : ipc_E ↦ iso_vfP 2 (iso_phaseOfCoords p.1)) p :=
  ipc_CD.smul (((ipc_CD.const _ p).tf (ipc_CD_X p)).inv hc) (ipc_CD.const _ p)

lemma ipc_CD_Y (p : ipc_E)
    (hc : traceForm (controlMatrix (vertex 2)) (iso_phaseOfCoords p.1).1 ≠ 0) :
    ipc_CD (fun p : ipc_E ↦ ipc_Y (iso_phaseOfCoords p.1)) p :=
  (ipc_CD_X p).add (ipc_CD_P p hc)

/-- The closed form of the flow is `C¹` in `(v, t)`. -/
theorem ipc_CD_cf (p : ipc_E) (hp : ipc_Good p.1) :
    ipc_CD (fun p : ipc_E ↦ (ipc_cf (iso_phaseOfCoords p.1) p.2).1) p ∧
      ipc_CD (fun p : ipc_E ↦ (ipc_cf (iso_phaseOfCoords p.1) p.2).2.1) p ∧
      ipc_CD (fun p : ipc_E ↦ (ipc_cf (iso_phaseOfCoords p.1) p.2).2.2) p := by
  obtain ⟨hc, hY⟩ := hp
  have ht : ContDiffAt ℝ 1 (fun p : ipc_E ↦ p.2) p := contDiffAt_snd
  have hX := ipc_CD_X p
  have hL := ipc_CD_L p
  have hR := ipc_CD_R p
  have hP := ipc_CD_P p hc
  have hYc := ipc_CD_Y p hc
  have hPP :
      traceForm (iso_vfP 2 (iso_phaseOfCoords p.1)) (iso_vfP 2 (iso_phaseOfCoords p.1)) ≠ 0 :=
    ipc_traceForm_vfP _ hc
  have eP : ipc_CD (fun p : ipc_E ↦ NormedSpace.exp (p.2 • iso_vfP 2 (iso_phaseOfCoords p.1))) p :=
    (ipc_CD.smul ht hP).exp
  have eP' :
      ipc_CD (fun p : ipc_E ↦ NormedSpace.exp (-p.2 • iso_vfP 2 (iso_phaseOfCoords p.1))) p :=
    (ipc_CD.smul ht.neg hP).exp
  have hIM : ipc_CD (fun p : ipc_E ↦ ipc_IM (iso_phaseOfCoords p.1) p.2) p :=
    (ipc_CD.I hYc hL ht hY).add (ipc_CD.smul contDiffAt_const
      (ipc_CD.I hP (ipc_CD.const J p) ht hPP))
  have hIIM : ipc_CD (fun p : ipc_E ↦ ipc_IIM (iso_phaseOfCoords p.1) p.2) p :=
    (ipc_CD.II hYc hL ht hY).add (ipc_CD.smul contDiffAt_const
      (ipc_CD.II hP (ipc_CD.const J p) ht hPP))
  have hK : ipc_CD (fun p : ipc_E ↦ ipc_K (iso_phaseOfCoords p.1)) p := (hX.mul hP).sub (hP.mul hX)
  refine ⟨(eP.mul hX).mul eP', ((((eP.mul (ipc_CD.smul ht.neg hYc).exp).mul hL).mul
    (ipc_CD.smul ht hYc).exp).mul eP'), ?_⟩
  exact (eP.mul ((hR.sub (ipc_CD.smul ((ht.mul (hR.tf hP)).sub (hIIM.tf hK))
    ((hP.mul hX).sub (hX.mul hP)))).sub ((hIM.mul hX).sub (hX.mul hIM)))).mul eP'

end Smooth

end SmoothedPolygons
