module

public import SmoothedPolygons.Defs
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Basic.Analysis.Calculus.MatrixEntrywiseExp
public import Basic.Analysis.Calculus.MatrixFTC
public import Mathlib.Analysis.Complex.Basic

/-!
# Matrix identities (Appendix A.6)

Identities for matrices in `𝔰𝔩₂(ℂ)` (Propositions A.6.1–A.6.3) and the matrix exponential of an
element of `𝔰𝔩₂(ℝ)` (Lemma A.6.4).
-/

@[expose] public section

namespace SmoothedPolygons

open Matrix

/-- A traceless `2 × 2` matrix is `[[a, b], [c, -a]]`. -/
private lemma algA_eta {R : Type*} [CommRing R] (X : Matrix (Fin 2) (Fin 2) R)
    (hX : X.trace = 0) : X = !![X 0 0, X 0 1; X 1 0, -X 0 0] := by
  rw [Matrix.trace_fin_two] at hX
  ext i j; fin_cases i <;> fin_cases j <;> simp; linear_combination hX

/-- **Proposition A.6.1** (`prop:brack-brack`). For `X, Y ∈ 𝔰𝔩₂(ℂ)`,
`ad_X² Y = [[Y, X], X] = -2 det(X) Y - 2XYX = 2⟨X, X⟩Y - 2⟨X, Y⟩X`. -/
theorem propositionA_6_1 (X Y : Matrix (Fin 2) (Fin 2) ℂ) (hX : X.trace = 0) (hY : Y.trace = 0) :
    X * (X * Y - Y * X) - (X * Y - Y * X) * X = (Y * X - X * Y) * X - X * (Y * X - X * Y) ∧
      (Y * X - X * Y) * X - X * (Y * X - X * Y) = (-2 * X.det) • Y - (2 : ℂ) • (X * Y * X) ∧
      (Y * X - X * Y) * X - X * (Y * X - X * Y) =
        (2 * (X * X).trace) • Y - (2 * (X * Y).trace) • X := by
  refine ⟨by noncomm_ring, ?_, ?_⟩ <;>
  · rw [algA_eta X hX, algA_eta Y hY]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.det_fin_two, Matrix.trace_fin_two] <;> ring

/-- **Proposition A.6.2** (`prop:trace-quotient-sub`). For `X, Y, Z, W ∈ 𝔰𝔩₂(ℂ)`,
`⟨X, Z⟩⟨Y, W⟩ - ⟨Y, Z⟩⟨X, W⟩ = -(1/2)⟨[X, Y], [Z, W]⟩`. -/
theorem propositionA_6_2 (X Y Z W : Matrix (Fin 2) (Fin 2) ℂ) (hX : X.trace = 0)
    (hY : Y.trace = 0) (hZ : Z.trace = 0) (hW : W.trace = 0) :
    (X * Z).trace * (Y * W).trace - (Y * Z).trace * (X * W).trace =
      -(1 / 2) * ((X * Y - Y * X) * (Z * W - W * Z)).trace := by
  rw [algA_eta X hX, algA_eta Y hY, algA_eta Z hZ, algA_eta W hW]
  simp [Matrix.trace_fin_two]
  ring

/-- **Proposition A.6.3** (`prop:brack-brack-inner-prod`). For `X, Y, Z, W ∈ 𝔰𝔩₂(ℂ)` with
`⟨Y, Z⟩ = 0`, `⟨[X, Y], [Z, W]⟩ = -2⟨X, Z⟩⟨Y, W⟩`. -/
theorem propositionA_6_3 (X Y Z W : Matrix (Fin 2) (Fin 2) ℂ) (hX : X.trace = 0)
    (hY : Y.trace = 0) (hZ : Z.trace = 0) (hW : W.trace = 0) (hYZ : (Y * Z).trace = 0) :
    ((X * Y - Y * X) * (Z * W - W * Z)).trace = -2 * (X * Z).trace * (Y * W).trace := by
  have h := propositionA_6_2 X Y Z W hX hY hZ hW
  rw [hYZ] at h
  linear_combination 2 * h

/-- Cayley–Hamilton for a traceless `2 × 2` matrix: `X² = -det(X) I`. -/
private lemma algA_sq_of_trace_zero (X : Matrix (Fin 2) (Fin 2) ℝ) (hX : X.trace = 0) :
    X * X = (-X.det) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [algA_eta X hX]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.det_fin_two] <;> ring

/-- `det (exp A) = exp (tr A)` for real `2 × 2` matrices, the formula cited in the proof of
Lemma A.6.4 (Mathlib does not have it): by the derivative of the determinant (Jacobi's formula),
`f(s) = det(exp(sA))` solves `f' = tr(A) f`, so `f(s) exp(-s tr A)` is constant. -/
private lemma algA_det_exp (A : Matrix (Fin 2) (Fin 2) ℝ) :
    (NormedSpace.exp A).det = Real.exp A.trace := by
  set f : ℝ → ℝ := fun s ↦ (NormedSpace.exp (s • A)).det with hfdef
  have hf : ∀ s, HasDerivAt f (A.trace * f s) s := by
    intro s
    have h := (Matrix.hasDerivAtEntrywise_exp_smul_const A s).det_fin_two
    convert h using 1
    simp only [f, Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  set h : ℝ → ℝ := fun s ↦ f s * Real.exp (-(s * A.trace)) with hhdef
  have hh : ∀ s, HasDerivAt h 0 s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ ↦ -(s * A.trace)) (-(1 * A.trace)) s :=
      ((hasDerivAt_id' s).mul_const _).fun_neg
    have := (hf s).fun_mul h1.exp
    convert this using 1
    ring
  have := is_const_of_deriv_eq_zero (fun s ↦ (hh s).differentiableAt) (fun s ↦ (hh s).deriv) 1 0
  simp only [h, f, one_smul, one_mul, zero_smul, NormedSpace.exp_zero, Matrix.det_one, zero_mul,
    neg_zero, Real.exp_zero, mul_one] at this
  rw [← mul_one (Real.exp A.trace), ← this, mul_comm, mul_assoc, ← Real.exp_add]
  simp

/-- A curve `G` with `G' = X G` and `G(0) = I` is `t ↦ exp(tX)`: both solve the initial value
problem `F' = XF`, `F(0) = I`, whose solution is unique. -/
private lemma algA_exp_smul_eq (X : Matrix (Fin 2) (Fin 2) ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ s, HasDerivAtEntrywise G (X * G s) s) (h0 : G 0 = 1) (t : ℝ) :
    NormedSpace.exp (t • X) = G t := by
  have key : ∀ (X : Matrix (Fin 2) (Fin 2) ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ),
      (∀ s, HasDerivAtEntrywise G (X * G s) s) → G 0 = 1 →
        ∀ t, 0 ≤ t → NormedSpace.exp (t • X) = G t := by
    intro X G hG h0 t ht
    refine Matrix.ODE_solution_unique_mul_left (A := fun _ ↦ X) (a := 0) (b := t)
      continuousOn_const
      (fun s _ ↦ (Matrix.hasDerivAtEntrywise_exp_smul_const' X s).continuousAt.continuousWithinAt)
      (fun s _ ↦ (Matrix.hasDerivAtEntrywise_exp_smul_const' X s).hasDerivWithinAtEntrywise)
      (fun s _ ↦ (hG s).continuousAt.continuousWithinAt)
      (fun s _ ↦ (hG s).hasDerivWithinAtEntrywise) ?_ ⟨ht, le_rfl⟩
    simp [h0]
  rcases le_or_gt 0 t with ht | ht
  · exact key X G hG h0 t ht
  · have hG' : ∀ s, HasDerivAtEntrywise (fun s ↦ G (-s)) (-X * G (-s)) s := fun s ↦
      ((hG (-s)).scomp (hasDerivAt_neg s)).congr_deriv (by simp)
    simpa using key (-X) (fun s ↦ G (-s)) hG' (by simp [h0]) (-t) (by linarith)

/-- **Lemma A.6.4** (`lem:exp-of-sl2`). If `X ∈ 𝔰𝔩₂(ℝ)` and `d = det X`, then `exp(X) ∈ SL₂(ℝ)`, and
`exp(tX) = cosh(t√(-d)) I₂ + sinh(t√(-d))/√(-d) X` if `d < 0`,
`exp(tX) = cos(t√d) I₂ + sin(t√d)/√d X` if `d > 0`, and `exp(tX) = I₂ + tX` if `d = 0`. -/
theorem lemmaA_6_4 (X : Matrix (Fin 2) (Fin 2) ℝ) (hX : X.trace = 0) :
    (NormedSpace.exp X).det = 1 ∧
      ∀ t : ℝ,
        (X.det < 0 → NormedSpace.exp (t • X) =
          Real.cosh (t * √(-X.det)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
            (Real.sinh (t * √(-X.det)) / √(-X.det)) • X) ∧
        (0 < X.det → NormedSpace.exp (t • X) =
          Real.cos (t * √X.det) • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
            (Real.sin (t * √X.det) / √X.det) • X) ∧
        (X.det = 0 → NormedSpace.exp (t • X) = 1 + t • X) := by
  have hXX := algA_sq_of_trace_zero X hX
  refine ⟨by rw [algA_det_exp, hX, Real.exp_zero], fun t ↦ ⟨fun hd ↦ ?_, fun hd ↦ ?_, fun hd ↦ ?_⟩⟩
  · set k := √(-X.det) with hk
    have hk0 : 0 < k := Real.sqrt_pos.2 (by linarith)
    have hkk : k * k = -X.det := Real.mul_self_sqrt (by linarith)
    refine algA_exp_smul_eq X
      (fun s ↦ Real.cosh (s * k) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + (Real.sinh (s * k) / k) • X)
      (fun s ↦ ?_) (by simp) t
    have h1 : HasDerivAt (fun s ↦ Real.cosh (s * k)) (Real.sinh (s * k) * (1 * k)) s :=
      ((hasDerivAt_id' s).mul_const k).cosh
    have h2 : HasDerivAt (fun s ↦ Real.sinh (s * k) / k) (Real.cosh (s * k) * (1 * k) / k) s :=
      ((hasDerivAt_id' s).mul_const k).sinh.div_const k
    refine ((Matrix.hasDerivAtEntrywise_smul_const h1 1).add
      (Matrix.hasDerivAtEntrywise_smul_const h2 X)).congr_deriv ?_
    have e1 : Real.sinh (s * k) / k * -X.det = Real.sinh (s * k) * (1 * k) := by
      rw [← hkk]; field_simp
    have e2 : Real.cosh (s * k) * (1 * k) / k = Real.cosh (s * k) := by field_simp
    rw [mul_add, Matrix.mul_smul, Matrix.mul_smul, hXX, smul_smul, Matrix.mul_one, e1, e2,
      add_comm]
  · set k := √X.det with hk
    have hk0 : 0 < k := Real.sqrt_pos.2 hd
    have hkk : k * k = X.det := Real.mul_self_sqrt hd.le
    refine algA_exp_smul_eq X
      (fun s ↦ Real.cos (s * k) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + (Real.sin (s * k) / k) • X)
      (fun s ↦ ?_) (by simp) t
    have h1 : HasDerivAt (fun s ↦ Real.cos (s * k)) (-Real.sin (s * k) * (1 * k)) s :=
      ((hasDerivAt_id' s).mul_const k).cos
    have h2 : HasDerivAt (fun s ↦ Real.sin (s * k) / k) (Real.cos (s * k) * (1 * k) / k) s :=
      ((hasDerivAt_id' s).mul_const k).sin.div_const k
    refine ((Matrix.hasDerivAtEntrywise_smul_const h1 1).add
      (Matrix.hasDerivAtEntrywise_smul_const h2 X)).congr_deriv ?_
    have e1 : Real.sin (s * k) / k * -X.det = -Real.sin (s * k) * (1 * k) := by
      rw [← hkk]; field_simp
    have e2 : Real.cos (s * k) * (1 * k) / k = Real.cos (s * k) := by field_simp
    rw [mul_add, Matrix.mul_smul, Matrix.mul_smul, hXX, smul_smul, Matrix.mul_one, e1, e2,
      add_comm]
  · refine algA_exp_smul_eq X (fun s ↦ 1 + s • X) (fun s ↦ ?_) (by simp) t
    refine ((Matrix.hasDerivAtEntrywise_smul_const (hasDerivAt_id' s) X).const_add 1).congr_deriv
      ?_
    rw [mul_add, Matrix.mul_smul, hXX, hd]
    simp

end SmoothedPolygons
