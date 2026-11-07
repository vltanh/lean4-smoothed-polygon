module

public import SmoothedPolygons.Ch7.Isolated.IpcFlow
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Theorem 7.7.1, step 4 (helper): the linearized flow at `q_fix(y₀)`

At `X₀ = Φ(i y₀)` the matrices `P = Z_{e₃}/⟨Z_{e₃}, X₀⟩` and `Y = X₀ + P` are triangular, and the
closed form of the vertex flow (`SmoothedPolygons.Ch7.Isolated.IpcFlow`) is explicit in
`W = exp(√3 y₀ t)`. Here: the part of the flow linear in `(Λ₁(0), Λ_R(0))` from `X₀`, at every
time (`ipc_linΛR_octagon`, `ipc_cfΛ₁_octagon`), and at `t_sw` in coordinates after `Ad(R)`
(`ipc_linVec_eq`, `ipc_Glin_eq`); the vector field at `q_fix(y₀)` (`ipc_Vq_eq`) and at the end of
the arc (`ipc_Ft_eq`); and the tangent of the curve `y₀ ↦ q_fix(y₀)` (`ipc_hasDerivAt_qFix`).
All are explicit in `(y₀, ℓ, √3)`, `ℓ = ln(4/(3y₀² + 1))`; the explicit vectors were obtained by a
symbolic computation and are checked here by `field_simp`/`ring`.
-/

@[expose] public section

namespace SmoothedPolygons

open Matrix Set Filter Topology MeasureTheory

/-- Normalize, and reduce the powers of `√3` (after `field_simp`). -/
macro "ipc_ring" : tactic =>
  `(tactic| (
    try ring_nf
    try simp only [str_sqrt3_sq, str_sqrt3_pow3, str_sqrt3_pow4, str_sqrt3_pow5, str_sqrt3_pow6,
      str_sqrt3_pow7, str_sqrt3_pow8]
    try ring_nf))

/-- `exp(tA) = cosh(ct) I + sinh(ct)/c A` for traceless `A` with `det A = -c²`. -/
lemma ipc_exp_smul_of_det_neg (A : Mat2) (hA : A.trace = 0) {c : ℝ} (hc : 0 < c)
    (hdet : A.det = -c ^ 2) (t : ℝ) :
    NormedSpace.exp (t • A) =
      ((Real.exp (c * t) + (Real.exp (c * t))⁻¹) / 2) • (1 : Mat2) +
        ((Real.exp (c * t) - (Real.exp (c * t))⁻¹) / (2 * c)) • A := by
  have hneg : A.det < 0 := by rw [hdet]; nlinarith [sq_pos_of_pos hc]
  have hs : √(-A.det) = c := by rw [hdet, neg_neg, Real.sqrt_sq hc.le]
  rw [((lemmaA_6_4 A hA).2 t).1 hneg, hs, Real.cosh_eq, Real.sinh_eq, mul_comm t c,
    Real.exp_neg, div_div]

/-- `P` at `X₀ = Φ(i y₀)`. -/
noncomputable def ipc_Pm (y : ℝ) : Mat2 := !![√3 * y / 2, y; 0, -(√3 * y / 2)]

/-- `Y = X₀ + P` at `X₀ = Φ(i y₀)`. -/
noncomputable def ipc_Ym (y : ℝ) : Mat2 := !![√3 * y / 2, 0; 1 / y, -(√3 * y / 2)]

lemma ipc_vfP_octagon (y : ℝ) (hy : 0 < y) (L R : Mat2) : iso_vfP 2 (Φ 0 y, L, R) = ipc_Pm y :=
  str_segP_eq y hy.ne'

lemma ipc_Y_octagon (y : ℝ) (hy : 0 < y) (L R : Mat2) : ipc_Y (Φ 0 y, L, R) = ipc_Ym y := by
  rw [ipc_Y, ipc_vfP_octagon y hy, ipc_Pm, ipc_Ym]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Φ]
  field_simp
  ring

lemma ipc_exp_Pm (y : ℝ) (hy : 0 < y) (t : ℝ) :
    NormedSpace.exp (t • ipc_Pm y) =
      !![Real.exp (√3 * y / 2 * t),
        (Real.exp (√3 * y / 2 * t) - (Real.exp (√3 * y / 2 * t))⁻¹) / √3;
        0, (Real.exp (√3 * y / 2 * t))⁻¹] := by
  have h3 : (0 : ℝ) < √3 := by positivity
  rw [ipc_exp_smul_of_det_neg (ipc_Pm y) ?_ (c := √3 * y / 2) (by positivity) ?_ t]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [ipc_Pm] <;> field_simp <;> ring
  · simp [ipc_Pm, Matrix.trace_fin_two]
  · simp [ipc_Pm, Matrix.det_fin_two]
    ring

lemma ipc_exp_Ym (y : ℝ) (hy : 0 < y) (t : ℝ) :
    NormedSpace.exp (t • ipc_Ym y) =
      !![Real.exp (√3 * y / 2 * t), 0;
        (Real.exp (√3 * y / 2 * t) - (Real.exp (√3 * y / 2 * t))⁻¹) / (√3 * y ^ 2),
        (Real.exp (√3 * y / 2 * t))⁻¹] := by
  have h3 : (0 : ℝ) < √3 := by positivity
  rw [ipc_exp_smul_of_det_neg (ipc_Ym y) ?_ (c := √3 * y / 2) (by positivity) ?_ t]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [ipc_Ym] <;> field_simp <;> ring
  · simp [ipc_Ym, Matrix.trace_fin_two]
  · simp [ipc_Ym, Matrix.det_fin_two]
    field_simp

/-- `Ad(e^{-tY}) B` at the octagon, `W = exp(√3 y₀ t)`. -/
noncomputable def ipc_S1 (y W b1 b2 b3 : ℝ) : Mat2 :=
  !![(3*W*b1*y^2 + √3*W*b2 - √3*b2)/(3*W*y^2),
    b2/W;
    (-2*√3*W^2*b1*y^2 - W^2*b2 + 3*W^2*b3*y^4 + 2*√3*W*b1*y^2 + 2*W*b2 - b2)/(3*W*y^4),
    -(3*W*b1*y^2 + √3*W*b2 - √3*b2)/(3*W*y^2)]

/-- `∫₀ᵗ Ad(e^{-sY}) Λ₁(0) ds` at the octagon. -/
noncomputable def ipc_IYm (y W t a1 a2 a3 : ℝ) : Mat2 :=
  !![(3*W*a1*t*y^3 + √3*W*a2*t*y - W*a2 + a2)/(3*W*y^3),
    √3*a2*(W - 1)/(3*W*y);
    (-6*W^2*a1*y^2 - √3*W^2*a2 + 3*√3*W^2*a3*y^4 + 6*√3*W*a1*t*y^3 + 6*W*a1*y^2 + 6*W*a2*t*y
      - 3*√3*W*a3*y^4 + √3*a2)/(9*W*y^5),
    -(3*W*a1*t*y^3 + √3*W*a2*t*y - W*a2 + a2)/(3*W*y^3)]

/-- `∫₀ᵗ ∫₀^σ Ad(e^{-sY}) Λ₁(0) ds dσ` at the octagon. -/
noncomputable def ipc_IIYm (y W t a1 a2 a3 : ℝ) : Mat2 :=
  !![(9*W*a1*t^2*y^4 + 3*√3*W*a2*t^2*y^2 - 6*W*a2*t*y + 2*√3*W*a2 - 2*√3*a2)/(18*W*y^4),
    a2*(√3*W*t*y - W + 1)/(3*W*y^2);
    -(2*√3*W^2*a1*y^2 + W^2*a2 - 3*W^2*a3*y^4 - 3*√3*W*a1*t^2*y^4 - 6*W*a1*t*y^3 - 2*√3*W*a1*y^2
      - 3*W*a2*t^2*y^2 - 2*W*a2 + 3*√3*W*a3*t*y^5 + 3*W*a3*y^4 + a2)/(9*W*y^6),
    -(9*W*a1*t^2*y^4 + 3*√3*W*a2*t^2*y^2 - 6*W*a2*t*y + 2*√3*W*a2 - 2*√3*a2)/(18*W*y^4)]

/-- The inner matrix of `ipc_linΛR` at the octagon. -/
noncomputable def ipc_Min (y W t a1 a2 a3 r1 r2 r3 : ℝ) : Mat2 :=
  !![-(-3*W*a2*t*y + 2*√3*W*a2 + 3*W*a3*t*y^3 + 3*√3*W*r1*t*y^3 - 3*W*r1*y^2 + 3*W*r3*t*y^3
      - 2*√3*a2)/(3*W*y^2),
    (2*√3*W^2*a1*y^2 + W^2*a2 - 3*W^2*a3*y^4 - 2*√3*W*a1*y^2 - 3*√3*W*a2*t*y^3 + 3*W*a2*y^2 - 2*W*a2
      + 3*√3*W*a3*t*y^5 + 3*W*a3*y^4 + 9*W*r1*t*y^5 + 3*W*r2*y^2 + 3*√3*W*r3*t*y^5 - 3*a2*y^2
      + a2)/(3*W*y^2);
    (2*√3*W^2*a1*y^2 + W^2*a2 - 3*W^2*a3*y^4 - 2*√3*W*a1*y^2 - 3*√3*W*a2*t*y^3 + 3*W*a2*y^2 - 2*W*a2
      + 3*√3*W*a3*t*y^5 + 3*W*a3*y^4 + 9*W*r1*t*y^5 + 3*√3*W*r3*t*y^5 + 3*W*r3*y^4 - 3*a2*y^2
      + a2)/(3*W*y^4),
    (-3*W*a2*t*y + 2*√3*W*a2 + 3*W*a3*t*y^3 + 3*√3*W*r1*t*y^3 - 3*W*r1*y^2 + 3*W*r3*t*y^3
      - 2*√3*a2)/(3*W*y^2)]

/-- The linear part of `Λ_R(t)` at the octagon. -/
noncomputable def ipc_LRW (y W t a1 a2 a3 r1 r2 r3 : ℝ) : Mat2 :=
  !![-(-6*W^3*a1*y^2 - √3*W^3*a2 + 3*√3*W^3*a3*y^4 + 12*W^2*a1*y^2 + 3*√3*W^2*a2*y^2 + 3*√3*W^2*a2
      - 6*√3*W^2*a3*y^4 - 9*W^2*r1*y^4 - 3*√3*W^2*r3*y^4 - 6*W*a1*y^2 - 9*W*a2*t*y^3 - 3*√3*W*a2
      + 9*W*a3*t*y^5 + 3*√3*W*a3*y^4 + 9*√3*W*r1*t*y^5 + 9*W*r3*t*y^5 + 3*√3*W*r3*y^4 - 3*√3*a2*y^2
      + √3*a2)/(9*W^2*y^4),
    (6*√3*W^4*a1*y^4 - 2*√3*W^4*a1*y^2 + 3*W^4*a2*y^2 - W^4*a2 - 9*W^4*a3*y^6 + 3*W^4*a3*y^4
      - 6*√3*W^3*a1*y^4 + 6*√3*W^3*a1*y^2 - 9*√3*W^3*a2*t*y^5 - 3*√3*W^3*a2*t*y^3 + 9*W^3*a2*y^4
      + 3*W^3*a2*y^2 + 4*W^3*a2 + 9*√3*W^3*a3*t*y^7 + 3*√3*W^3*a3*t*y^5 + 9*W^3*a3*y^6
      - 9*W^3*a3*y^4 + 27*W^3*r1*t*y^7 + 9*W^3*r1*t*y^5 - 6*√3*W^3*r1*y^4 + 9*W^3*r2*y^4
      + 9*√3*W^3*r3*t*y^7 + 3*√3*W^3*r3*t*y^5 - 3*W^3*r3*y^4 - 6*√3*W^2*a1*y^2 - 9*W^2*a2*y^4
      - 12*W^2*a2*y^2 - 6*W^2*a2 + 9*W^2*a3*y^4 + 6*√3*W^2*r1*y^4 + 6*W^2*r3*y^4 + 2*√3*W*a1*y^2
      + 3*√3*W*a2*t*y^3 + 3*W*a2*y^2 + 4*W*a2 - 3*√3*W*a3*t*y^5 - 3*W*a3*y^4 - 9*W*r1*t*y^5
      - 3*√3*W*r3*t*y^5 - 3*W*r3*y^4 + 3*a2*y^2 - a2)/(9*W^2*y^4);
    (2*√3*W^2*a1*y^2 + W^2*a2 - 3*W^2*a3*y^4 - 2*√3*W*a1*y^2 - 3*√3*W*a2*t*y^3 + 3*W*a2*y^2 - 2*W*a2
      + 3*√3*W*a3*t*y^5 + 3*W*a3*y^4 + 9*W*r1*t*y^5 + 3*√3*W*r3*t*y^5 + 3*W*r3*y^4 - 3*a2*y^2
      + a2)/(3*W^2*y^4),
    (-6*W^3*a1*y^2 - √3*W^3*a2 + 3*√3*W^3*a3*y^4 + 12*W^2*a1*y^2 + 3*√3*W^2*a2*y^2 + 3*√3*W^2*a2
      - 6*√3*W^2*a3*y^4 - 9*W^2*r1*y^4 - 3*√3*W^2*r3*y^4 - 6*W*a1*y^2 - 9*W*a2*t*y^3 - 3*√3*W*a2
      + 9*W*a3*t*y^5 + 3*√3*W*a3*y^4 + 9*√3*W*r1*t*y^5 + 9*W*r3*t*y^5 + 3*√3*W*r3*y^4 - 3*√3*a2*y^2
      + √3*a2)/(9*W^2*y^4)]

/-- The linear part of `Λ₁(t)` at the octagon. -/
noncomputable def ipc_L1W (y W a1 a2 a3 : ℝ) : Mat2 :=
  !![(-6*W^3*a1*y^2 - √3*W^3*a2 + 3*√3*W^3*a3*y^4 + 9*W^2*a1*y^4 + 12*W^2*a1*y^2 + 3*√3*W^2*a2*y^2
      + 3*√3*W^2*a2 - 3*√3*W^2*a3*y^4 - 6*W*a1*y^2 - 3*√3*W*a2*y^2 - 3*√3*W*a2 + √3*a2)/(9*W^2*y^4),
    -(-2*√3*W^4*a1*y^2 - W^4*a2 + 3*W^4*a3*y^4 + 6*√3*W^3*a1*y^4 + 6*√3*W^3*a1*y^2 + 6*W^3*a2*y^2
      + 4*W^3*a2 - 6*W^3*a3*y^4 - 6*√3*W^2*a1*y^4 - 6*√3*W^2*a1*y^2 - 9*W^2*a2*y^4 - 12*W^2*a2*y^2
      - 6*W^2*a2 + 3*W^2*a3*y^4 + 2*√3*W*a1*y^2 + 6*W*a2*y^2 + 4*W*a2 - a2)/(9*W^2*y^4);
    (-2*√3*W^2*a1*y^2 - W^2*a2 + 3*W^2*a3*y^4 + 2*√3*W*a1*y^2 + 2*W*a2 - a2)/(3*W^2*y^4),
    -(-6*W^3*a1*y^2 - √3*W^3*a2 + 3*√3*W^3*a3*y^4 + 9*W^2*a1*y^4 + 12*W^2*a1*y^2 + 3*√3*W^2*a2*y^2
      + 3*√3*W^2*a2 - 3*√3*W^2*a3*y^4 - 6*W*a1*y^2 - 3*√3*W*a2*y^2 - 3*√3*W*a2 + √3*a2)/(9*W^2*y^4)]

lemma ipc_traceForm_Ym (y : ℝ) : traceForm (ipc_Ym y) (ipc_Ym y) = 3 * y ^ 2 / 2 := by
  simp [ipc_Ym, traceForm, Matrix.trace_fin_two]
  ring_nf
  rw [str_sqrt3_sq]; ring

lemma ipc_traceForm_Pm (y : ℝ) : traceForm (ipc_Pm y) (ipc_Pm y) = 3 * y ^ 2 / 2 := by
  simp [ipc_Pm, traceForm, Matrix.trace_fin_two]
  ring_nf
  rw [str_sqrt3_sq]; ring

lemma ipc_ad_Ym (y : ℝ) (hy : 0 < y) (t b1 b2 b3 : ℝ) :
    ipc_ad (ipc_Ym y) t !![b1, b2; b3, -b1] = ipc_S1 y (Real.exp (√3 * y * t)) b1 b2 b3 := by
  have h3 : (0 : ℝ) < √3 := by positivity
  have hw := Real.exp_pos (√3 * y / 2 * t)
  have hW : Real.exp (√3 * y * t) = Real.exp (√3 * y / 2 * t) ^ 2 := by
    rw [sq, ← Real.exp_add]; ring_nf
  have hneg : Real.exp (√3 * y / 2 * -t) = (Real.exp (√3 * y / 2 * t))⁻¹ := by
    rw [mul_neg, Real.exp_neg]
  rw [ipc_ad, ipc_exp_Ym y hy, ipc_exp_Ym y hy, hneg, hW]
  generalize Real.exp (√3 * y / 2 * t) = w at hw ⊢
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ipc_S1, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ipc_ring

lemma ipc_I_Ym (y : ℝ) (hy : 0 < y) (t a1 a2 a3 : ℝ) :
    ipc_I (ipc_Ym y) !![a1, a2; a3, -a1] t = ipc_IYm y (Real.exp (√3 * y * t)) t a1 a2 a3 := by
  have h3 : (0 : ℝ) < √3 := by positivity
  have hC : ipc_Ym y * !![a1, a2; a3, -a1] - !![a1, a2; a3, -a1] * ipc_Ym y =
      !![-a2 / y, √3 * a2 * y; -(-2 * a1 + √3 * a3 * y ^ 2) / y, -(-a2 / y)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ipc_Ym] <;> field_simp <;> ring
  have hW := Real.exp_pos (√3 * y * t)
  rw [ipc_I, hC, ipc_ad_Ym y hy, ipc_traceForm_Ym y]
  generalize Real.exp (√3 * y * t) = W at hW ⊢
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ipc_S1, ipc_IYm, ipc_Ym, traceForm, Matrix.trace_fin_two] <;>
    field_simp <;> ipc_ring

lemma ipc_II_Ym (y : ℝ) (hy : 0 < y) (t a1 a2 a3 : ℝ) :
    ipc_II (ipc_Ym y) !![a1, a2; a3, -a1] t = ipc_IIYm y (Real.exp (√3 * y * t)) t a1 a2 a3 := by
  have h3 : (0 : ℝ) < √3 := by positivity
  have hW := Real.exp_pos (√3 * y * t)
  rw [ipc_II, ipc_ad_Ym y hy, ipc_traceForm_Ym y]
  generalize Real.exp (√3 * y * t) = W at hW ⊢
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ipc_S1, ipc_IIYm, ipc_Ym, traceForm, Matrix.trace_fin_two] <;>
    field_simp <;> ipc_ring

lemma ipc_Min_eq (y : ℝ) (hy : 0 < y) {W : ℝ} (hW : 0 < W) (t a1 a2 a3 r1 r2 r3 : ℝ) :
    !![r1, r2; r3, -r1] - (t * traceForm !![r1, r2; r3, -r1] (ipc_Pm y) -
        traceForm (ipc_IIYm y W t a1 a2 a3) (Φ 0 y * ipc_Pm y - ipc_Pm y * Φ 0 y)) •
        (ipc_Pm y * Φ 0 y - Φ 0 y * ipc_Pm y) -
      (ipc_IYm y W t a1 a2 a3 * Φ 0 y - Φ 0 y * ipc_IYm y W t a1 a2 a3) =
      ipc_Min y W t a1 a2 a3 r1 r2 r3 := by
  have h3 : (0 : ℝ) < √3 := by positivity
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ipc_Min, ipc_IIYm, ipc_IYm, ipc_Pm, Φ, traceForm, Matrix.trace_fin_two] <;>
    field_simp <;> ipc_ring

/-- The linear part of `Λ_R(t)` from `X₀ = Φ(i y₀)`, `W = exp(√3 y₀ t)`. -/
lemma ipc_linΛR_octagon (y : ℝ) (hy : 0 < y) (t a1 a2 a3 r1 r2 r3 : ℝ) :
    ipc_linΛR (Φ 0 y, !![a1, a2; a3, -a1], !![r1, r2; r3, -r1]) t =
      ipc_LRW y (Real.exp (√3 * y * t)) t a1 a2 a3 r1 r2 r3 := by
  have h3 : (0 : ℝ) < √3 := by positivity
  have hw := Real.exp_pos (√3 * y / 2 * t)
  have hW : Real.exp (√3 * y * t) = Real.exp (√3 * y / 2 * t) ^ 2 := by
    rw [sq, ← Real.exp_add]; ring_nf
  have hneg : Real.exp (√3 * y / 2 * -t) = (Real.exp (√3 * y / 2 * t))⁻¹ := by
    rw [mul_neg, Real.exp_neg]
  simp only [ipc_linΛR, ipc_K, ipc_Y_octagon y hy, ipc_vfP_octagon y hy]
  rw [ipc_I_Ym y hy, ipc_II_Ym y hy, ipc_Min_eq y hy (Real.exp_pos _), ipc_exp_Pm y hy,
    ipc_exp_Pm y hy, hneg, hW]
  generalize Real.exp (√3 * y / 2 * t) = w at hw ⊢
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ipc_Min, ipc_LRW, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ipc_ring

/-- The linear part of `Λ₁(t)` from `X₀ = Φ(i y₀)`, `W = exp(√3 y₀ t)`. -/
lemma ipc_cfΛ₁_octagon (y : ℝ) (hy : 0 < y) (t a1 a2 a3 : ℝ) (δR : Mat2) :
    ipc_cfΛ₁ (Φ 0 y, !![a1, a2; a3, -a1], δR) t = ipc_L1W y (Real.exp (√3 * y * t)) a1 a2 a3 := by
  have h3 : (0 : ℝ) < √3 := by positivity
  have hw := Real.exp_pos (√3 * y / 2 * t)
  have hW : Real.exp (√3 * y * t) = Real.exp (√3 * y / 2 * t) ^ 2 := by
    rw [sq, ← Real.exp_add]; ring_nf
  have hneg : Real.exp (√3 * y / 2 * -t) = (Real.exp (√3 * y / 2 * t))⁻¹ := by
    rw [mul_neg, Real.exp_neg]
  simp only [ipc_cfΛ₁, ipc_Y_octagon y hy, ipc_vfP_octagon y hy]
  rw [ipc_exp_Pm y hy, ipc_exp_Pm y hy, ipc_exp_Ym y hy, ipc_exp_Ym y hy, hneg, hW]
  generalize Real.exp (√3 * y / 2 * t) = w at hw ⊢
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ipc_L1W, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ipc_ring

/-! ### The vectors of the direct calculation -/

/-- The tangent `d/dy₀ q_fix(y₀)` of the family of fixed points, in coordinates. -/
noncomputable def ipc_Fam (y L : ℝ) : Fin 9 → ℝ :=
  ![0,
    -1,
    -1/y^2,
    0,
    (L + 3*y^2 - 3)/(3*y^3),
    -(9*L*y^4 - 2*L*y^2 - 3*L + 9*y^6 - 15*y^4 - 3*y^2 + 9)/(12*y^7),
    0,
    -(9*L*y^6 - 3*L*y^2 + 2*L + 9*y^6 - 18*y^4 + 15*y^2 - 6)/(12*y^5),
    (7*L*y^4 + 2*L*y^2 - L + 3*y^6 + 3*y^4 - 9*y^2 + 3)/(4*y^7)]

/-- The vector field at `q_fix(y₀)`, in coordinates. -/
noncomputable def ipc_Vq (y L : ℝ) : Fin 9 → ℝ :=
  ![1,
    -√3*y^2,
    -√3,
    (y - 1)*(y + 1)*(3*y^2 + 1)*(3*L*y^2 + L - 6*y^2 - 3)/(24*y^5),
    0,
    0,
    -(y - 1)*(y + 1)*(9*L*y^4 + 6*L*y^2 + L + 18*y^4 - 15*y^2 - 3)/(24*y^5),
    -√3*(9*L*y^6 + 21*L*y^4 + 3*L*y^2 - L + 18*y^6 - 9*y^4 - 12*y^2 + 3)/(12*y^3),
    0]

/-- `Ad(R)` of the vector field at the end `Ad(R⁻¹) q_fix(y₀)` of the arc, in coordinates. -/
noncomputable def ipc_Ft (y L : ℝ) : Fin 9 → ℝ :=
  ![1,
    √3*y^2,
    √3,
    (y - 1)*(y + 1)*(3*y^2 + 1)*(3*L*y^2 + L - 6*y^2 - 3)/(24*y^5),
    0,
    0,
    -(y - 1)*(y + 1)*(9*L*y^4 + 6*L*y^2 + L + 18*y^4 - 15*y^2 - 3)/(24*y^5),
    √3*(9*L*y^6 + 21*L*y^4 + 3*L*y^2 - L + 18*y^6 - 9*y^4 - 12*y^2 + 3)/(12*y^3),
    0]

/-- The derivative of `Ad(R) q(t_sw, q)` in the costate directions, in coordinates. -/
noncomputable def ipc_linVec (y L a1 a2 a3 r1 r2 r3 : ℝ) : Fin 9 → ℝ :=
  ![0,
    0,
    0,
    -(9*a1*y^6 + 6*a1*y^4 - 7*a1*y^2 + 3*√3*a2*y^4 + 2*√3*a2*y^2 - √3*a2 + 4*√3*a3*y^4)/(y^2*(3*y^2
      + 1)^2),
    -4*(-2*√3*a1*y^2 - a2 + 3*a3*y^4)/(3*y^2 + 1)^2,
    -(-24*√3*a1*y^6 - 16*√3*a1*y^4 + 8*√3*a1*y^2 + 27*a2*y^8 + 36*a2*y^6 - 6*a2*y^4 - 12*a2*y^2
      + 3*a2 - 16*a3*y^4)/(4*y^4*(3*y^2 + 1)^2),
    -(-9*√3*L*a2*y^4 - 6*√3*L*a2*y^2 - √3*L*a2 + 9*√3*L*a3*y^6 + 6*√3*L*a3*y^4 + √3*L*a3*y^2
      + 27*L*r1*y^6 + 18*L*r1*y^4 + 3*L*r1*y^2 + 9*√3*L*r3*y^6 + 6*√3*L*r3*y^4 + √3*L*r3*y^2
      - 36*a1*y^4 + 36*a1*y^2 - 6*√3*a2*y^2 + 6*√3*a2 + 18*√3*a3*y^6 - 18*√3*a3*y^4 + 27*r1*y^6
      - 3*r1*y^2 + 9*√3*r2*y^4 + 3*√3*r2*y^2 + 9*√3*r3*y^6 + 3*√3*r3*y^4)/(3*y^2*(3*y^2 + 1)^2),
    -(-36*L*a2*y^6 - 24*L*a2*y^4 - 4*L*a2*y^2 + 36*L*a3*y^8 + 24*L*a3*y^6 + 4*L*a3*y^4
      + 36*√3*L*r1*y^8 + 24*√3*L*r1*y^6 + 4*√3*L*r1*y^4 + 36*L*r3*y^8 + 24*L*r3*y^6 + 4*L*r3*y^4
      - 24*√3*a1*y^6 + 32*√3*a1*y^4 - 8*√3*a1*y^2 - 27*a2*y^8 + 6*a2*y^4 + 24*a2*y^2 - 3*a2
      + 36*a3*y^8 - 48*a3*y^6 + 12*a3*y^4 - 24*√3*r1*y^6 - 8*√3*r1*y^4 - 12*r2*y^4 - 4*r2*y^2
      + 36*r3*y^8 + 12*r3*y^6)/(4*y^2*(3*y^2 + 1)^2),
    -(-36*L*a2*y^6 - 24*L*a2*y^4 - 4*L*a2*y^2 + 36*L*a3*y^8 + 24*L*a3*y^6 + 4*L*a3*y^4
      + 36*√3*L*r1*y^8 + 24*√3*L*r1*y^6 + 4*√3*L*r1*y^4 + 36*L*r3*y^8 + 24*L*r3*y^6 + 4*L*r3*y^4
      - 24*√3*a1*y^6 + 32*√3*a1*y^4 - 8*√3*a1*y^2 - 27*a2*y^8 + 6*a2*y^4 + 24*a2*y^2 - 3*a2
      + 36*a3*y^8 - 48*a3*y^6 + 12*a3*y^4 - 24*√3*r1*y^6 - 8*√3*r1*y^4 + 36*r2*y^6 + 12*r2*y^4
      - 12*r3*y^6 - 4*r3*y^4)/(4*y^4*(3*y^2 + 1)^2)]

/-- The derivative of `χ₃₁(q(t_sw, q))` in the costate directions. -/
noncomputable def ipc_Glin (y L a1 a2 a3 r1 r2 r3 : ℝ) : ℝ :=
  -2*(-9*L*a2*y^4 - 6*L*a2*y^2 - L*a2 + 9*L*a3*y^6 + 6*L*a3*y^4 + L*a3*y^2 + 9*√3*L*r1*y^6
    + 6*√3*L*r1*y^4 + √3*L*r1*y^2 + 9*L*r3*y^6 + 6*L*r3*y^4 + L*r3*y^2 - 12*√3*a1*y^4 + 12*√3*a1*y^2
    - 6*a2*y^2 + 6*a2 + 18*a3*y^6 - 18*a3*y^4 + 9*√3*r1*y^6 - √3*r1*y^2 + 9*r2*y^4 + 3*r2*y^2
    + 9*r3*y^6 + 3*r3*y^4)/(y*(3*y^2 + 1)^2)

/-- The costate part of the basis vector `b_0`. -/
noncomputable def ipc_w0 (y L : ℝ) : Fin 9 → ℝ :=
  ![0,
    0,
    0,
    -(y - 1)*(y + 1)*(3*y^2 + 1)*(3*L*y^2 + L - 6*y^2 - 3)/(24*y^5),
    √3*(L + 3*y^2 - 3)/(3*y),
    -√3*(9*L*y^4 - 2*L*y^2 - 3*L + 9*y^6 - 15*y^4 - 3*y^2 + 9)/(12*y^5),
    -(3*L*y^2 + L + 3*y^2 - 3)/(3*y^3),
    √3*(7*L*y^4 + 2*L*y^2 - L + 3*y^6 + 3*y^4 - 9*y^2 + 3)/(4*y^3),
    √3*(7*L*y^4 + 2*L*y^2 - L + 3*y^6 + 3*y^4 - 9*y^2 + 3)/(4*y^5)]

/-- The costate part of the basis vector `b_1`. -/
noncomputable def ipc_w1 (y L : ℝ) : Fin 9 → ℝ :=
  ![0,
    0,
    0,
    0,
    √3*(L + 3*y^2 - 3)/(9*y^3),
    -√3*(9*L*y^4 - 2*L*y^2 - 3*L + 9*y^6 - 15*y^4 - 3*y^2 + 9)/(36*y^7),
    0,
    √3*(9*L*y^4 + 2*L*y^2 - 3*L + 9*y^6 - 3*y^4 - 15*y^2 + 9)/(36*y^5),
    √3*(9*L*y^4 + 2*L*y^2 - 3*L + 9*y^6 - 3*y^4 - 15*y^2 + 9)/(36*y^7)]

/-- The costate part of the basis vector `b_2`. -/
noncomputable def ipc_w2 (y _L : ℝ) : Fin 9 → ℝ :=
  ![0,
    0,
    0,
    1/y,
    0,
    0,
    0,
    0,
    0]

/-- The costate part of the basis vector `b_3`. -/
noncomputable def ipc_w3 (y _L : ℝ) : Fin 9 → ℝ :=
  ![0,
    0,
    0,
    0,
    √3/(3*y),
    √3*(y^2 + 1)*(3*y^2 - 1)/(12*y^5),
    0,
    -√3*(y - 1)*(y + 1)*(3*y^2 + 1)/(12*y^3),
    -√3*(y - 1)*(y + 1)*(3*y^2 + 1)/(12*y^5)]

/-! ### The ingredients of the direct calculation -/

lemma ipc_strongΛ₁_zero (y : ℝ) (hy : 0 < y) : strongΛ₁ y 0 = strongL₁ y • Λ₁₀ y := by
  rw [strongΛ₁, str_segG_zero y hy, inv_one, Matrix.one_mul, Matrix.mul_one]

lemma ipc_strongΛR_zero (y : ℝ) (hy : 0 < y) :
    strongΛR y 0 = strongLR y • !![0, y ^ 2; 1, 0] :=
  (costateΛR_solution y _ _ _ hy 0).2

/-- The point `q_fix(y₀)` in coordinates. -/
lemma ipc_phaseCoords_qFix (y : ℝ) (hy : 0 < y) :
    iso_phaseCoords (iso_qFix y) =
      ![0, -y, 1 / y, 0, strongL₁ y * ((2 * y ^ 2 * (1 + 3 * y ^ 2))⁻¹ * (4 * √3 * y ^ 4)),
        strongL₁ y * ((2 * y ^ 2 * (1 + 3 * y ^ 2))⁻¹ * -(√3 * (1 + y ^ 2) * (3 * y ^ 2 - 1))),
        0, strongLR y * y ^ 2, strongLR y] := by
  rw [iso_qFix, ipc_strongΛ₁_zero y hy, ipc_strongΛR_zero y hy]
  funext k
  fin_cases k <;> simp [iso_phaseCoords, Φ, Λ₁₀]
  field_simp

lemma ipc_hasDerivAt_of_eq {f g : ℝ → ℝ} {f' g' x : ℝ} (h : HasDerivAt f f' x)
    (hfg : ∀ z, g z = f z) (h' : f' = g') : HasDerivAt g g' x := by
  rw [show g = f from funext hfg, ← h']; exact h

lemma ipc_hasDerivAt_ellSw (y : ℝ) (hy : 0 < y) :
    HasDerivAt ellSw (-6 * y / (3 * y ^ 2 + 1)) y := by
  have h1 : 0 < 3 * y ^ 2 + 1 := by positivity
  have hq : HasDerivAt (fun x : ℝ ↦ 3 * x ^ 2 + 1) (6 * y) y :=
    ipc_hasDerivAt_of_eq (((hasDerivAt_pow 2 y).const_mul 3).add_const 1) (fun _ ↦ rfl)
      (by push_cast; ring)
  refine ipc_hasDerivAt_of_eq (((hasDerivAt_const y (4 : ℝ)).fun_div hq h1.ne').log
    (by positivity)) (fun _ ↦ rfl) ?_
  field_simp
  ring

/-- `(N(y)/D(y))'` with `N = -(1 + 3y²)(-3 - 6y² + (1 + 3y²)ℓ)`, `D = 12√3y⁴`. -/
lemma ipc_hasDerivAt_strongL₁ (y : ℝ) (hy : 0 < y) :
    HasDerivAt strongL₁
      (((-(6 * y * (-3 - 6 * y ^ 2 + (1 + 3 * y ^ 2) * ellSw y) +
          (1 + 3 * y ^ 2) * (-12 * y + 6 * y * ellSw y +
            (1 + 3 * y ^ 2) * (-6 * y / (3 * y ^ 2 + 1))))) * (12 * √3 * y ^ 4) -
        (-((1 + 3 * y ^ 2) * (-3 - 6 * y ^ 2 + (1 + 3 * y ^ 2) * ellSw y))) *
          (48 * √3 * y ^ 3)) / (12 * √3 * y ^ 4) ^ 2) y := by
  have hℓ := ipc_hasDerivAt_ellSw y hy
  have hA : HasDerivAt (fun x : ℝ ↦ 1 + 3 * x ^ 2) (6 * y) y :=
    ipc_hasDerivAt_of_eq (((hasDerivAt_pow 2 y).const_mul 3).const_add 1) (fun _ ↦ rfl)
      (by push_cast; ring)
  have hB : HasDerivAt (fun x : ℝ ↦ -3 - 6 * x ^ 2 + (1 + 3 * x ^ 2) * ellSw x)
      (-12 * y + 6 * y * ellSw y + (1 + 3 * y ^ 2) * (-6 * y / (3 * y ^ 2 + 1))) y :=
    ipc_hasDerivAt_of_eq ((((hasDerivAt_pow 2 y).const_mul 6).const_sub (-3)).add
      (hA.fun_mul hℓ)) (fun _ ↦ rfl) (by push_cast; ring)
  have hD : HasDerivAt (fun x : ℝ ↦ 12 * √3 * x ^ 4) (48 * √3 * y ^ 3) y :=
    ipc_hasDerivAt_of_eq ((hasDerivAt_pow 4 y).const_mul (12 * √3)) (fun _ ↦ rfl)
      (by push_cast; ring)
  refine ipc_hasDerivAt_of_eq (((hA.fun_mul hB).fun_neg).fun_div hD (by positivity))
    (fun z ↦ by unfold strongL₁; ring) ?_
  ring

/-- `(N(y)/D(y))'` with `N = -(3 - 12y² - 9y⁴ + 18y⁶ + (-1 + 3y² + 21y⁴ + 9y⁶)ℓ)`,
`D = 24y⁶`. -/
lemma ipc_hasDerivAt_strongLR (y : ℝ) (hy : 0 < y) :
    HasDerivAt strongLR
      (((-(-24 * y - 36 * y ^ 3 + 108 * y ^ 5 + ((6 * y + 84 * y ^ 3 + 54 * y ^ 5) * ellSw y +
          (-1 + 3 * y ^ 2 + 21 * y ^ 4 + 9 * y ^ 6) * (-6 * y / (3 * y ^ 2 + 1))))) *
          (24 * y ^ 6) -
        (-(3 - 12 * y ^ 2 - 9 * y ^ 4 + 18 * y ^ 6 +
          (-1 + 3 * y ^ 2 + 21 * y ^ 4 + 9 * y ^ 6) * ellSw y)) * (144 * y ^ 5)) /
        (24 * y ^ 6) ^ 2) y := by
  have hℓ := ipc_hasDerivAt_ellSw y hy
  have hp : HasDerivAt (fun x : ℝ ↦ 3 - 12 * x ^ 2 - 9 * x ^ 4 + 18 * x ^ 6)
      (-24 * y - 36 * y ^ 3 + 108 * y ^ 5) y :=
    ipc_hasDerivAt_of_eq ((((hasDerivAt_pow 2 y).const_mul 12).const_sub 3).sub
      ((hasDerivAt_pow 4 y).const_mul 9) |>.add ((hasDerivAt_pow 6 y).const_mul 18))
      (fun _ ↦ rfl) (by push_cast; ring)
  have hq : HasDerivAt (fun x : ℝ ↦ -1 + 3 * x ^ 2 + 21 * x ^ 4 + 9 * x ^ 6)
      (6 * y + 84 * y ^ 3 + 54 * y ^ 5) y :=
    ipc_hasDerivAt_of_eq (((((hasDerivAt_pow 2 y).const_mul 3).const_add (-1)).add
      ((hasDerivAt_pow 4 y).const_mul 21)).add ((hasDerivAt_pow 6 y).const_mul 9))
      (fun _ ↦ rfl) (by push_cast; ring)
  have hD : HasDerivAt (fun x : ℝ ↦ 24 * x ^ 6) (144 * y ^ 5) y :=
    ipc_hasDerivAt_of_eq ((hasDerivAt_pow 6 y).const_mul 24) (fun _ ↦ rfl) (by push_cast; ring)
  refine ipc_hasDerivAt_of_eq (((hp.fun_add (hq.fun_mul hℓ)).fun_neg).fun_div hD (by positivity))
    (fun z ↦ by unfold strongLR; ring) ?_
  ring

/-- `d/dy₀ q_fix(y₀)` in coordinates. -/
theorem ipc_hasDerivAt_qFix (y : ℝ) (hy : 0 < y) :
    HasDerivAt (fun x ↦ iso_phaseCoords (iso_qFix x)) (ipc_Fam y (ellSw y)) y := by
  have h3 : (0 : ℝ) < √3 := by positivity
  have h1 : 0 < 3 * y ^ 2 + 1 := by positivity
  have hev : (fun x ↦ iso_phaseCoords (iso_qFix x)) =ᶠ[𝓝 y] fun x ↦
      ![0, -x, 1 / x, 0, strongL₁ x * ((2 * x ^ 2 * (1 + 3 * x ^ 2))⁻¹ * (4 * √3 * x ^ 4)),
        strongL₁ x * ((2 * x ^ 2 * (1 + 3 * x ^ 2))⁻¹ * -(√3 * (1 + x ^ 2) * (3 * x ^ 2 - 1))),
        0, strongLR x * x ^ 2, strongLR x] := by
    filter_upwards [lt_mem_nhds hy] with x hx
    exact ipc_phaseCoords_qFix x hx
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  have hL := ipc_hasDerivAt_strongL₁ y hy
  have hR := ipc_hasDerivAt_strongLR y hy
  have hc4 : HasDerivAt (fun x : ℝ ↦ (2 * x ^ 2 * (1 + 3 * x ^ 2))⁻¹ * (4 * √3 * x ^ 4))
      (2 * √3 * (2 * y) / (1 + 3 * y ^ 2) ^ 2) y := by
    have e : (fun x : ℝ ↦ (2 * x ^ 2 * (1 + 3 * x ^ 2))⁻¹ * (4 * √3 * x ^ 4)) =ᶠ[𝓝 y]
        fun x ↦ 2 * √3 * x ^ 2 / (1 + 3 * x ^ 2) := by
      filter_upwards [lt_mem_nhds hy] with x hx
      field_simp
      ring
    refine HasDerivAt.congr_of_eventuallyEq ?_ e
    refine ipc_hasDerivAt_of_eq (((hasDerivAt_pow 2 y).const_mul (2 * √3)).fun_div
      (((hasDerivAt_pow 2 y).const_mul 3).const_add 1) (by positivity)) (fun _ ↦ rfl) ?_
    push_cast
    field_simp
    ring
  have hc5 : HasDerivAt
      (fun x : ℝ ↦ (2 * x ^ 2 * (1 + 3 * x ^ 2))⁻¹ * -(√3 * (1 + x ^ 2) * (3 * x ^ 2 - 1)))
      (-(√3 * ((2 * y * (3 * y ^ 2 - 1) + (1 + y ^ 2) * (6 * y)) * (2 * y ^ 2 + 6 * y ^ 4) -
        (1 + y ^ 2) * (3 * y ^ 2 - 1) * (4 * y + 24 * y ^ 3))) /
        (2 * y ^ 2 + 6 * y ^ 4) ^ 2) y := by
    have e : (fun x : ℝ ↦ (2 * x ^ 2 * (1 + 3 * x ^ 2))⁻¹ * -(√3 * (1 + x ^ 2) * (3 * x ^ 2 - 1)))
        = fun x ↦ -(√3 * ((1 + x ^ 2) * (3 * x ^ 2 - 1))) / (2 * x ^ 2 + 6 * x ^ 4) := by
      funext x; rw [div_eq_inv_mul]; congr 1 <;> ring
    rw [e]
    have hn : HasDerivAt (fun x : ℝ ↦ (1 + x ^ 2) * (3 * x ^ 2 - 1))
        (2 * y * (3 * y ^ 2 - 1) + (1 + y ^ 2) * (6 * y)) y :=
      ipc_hasDerivAt_of_eq (((hasDerivAt_pow 2 y).const_add 1).fun_mul
        (((hasDerivAt_pow 2 y).const_mul 3).sub_const 1)) (fun _ ↦ rfl) (by push_cast; ring)
    have hd : HasDerivAt (fun x : ℝ ↦ 2 * x ^ 2 + 6 * x ^ 4) (4 * y + 24 * y ^ 3) y :=
      ipc_hasDerivAt_of_eq (((hasDerivAt_pow 2 y).const_mul 2).add
        ((hasDerivAt_pow 4 y).const_mul 6)) (fun _ ↦ rfl) (by push_cast; ring)
    refine ipc_hasDerivAt_of_eq (((hn.const_mul √3).fun_neg).fun_div hd (by positivity))
      (fun _ ↦ rfl) ?_
    ring
  have hall : ∀ k : Fin 9, HasDerivAt (fun x : ℝ ↦
      ![0, -x, 1 / x, 0, strongL₁ x * ((2 * x ^ 2 * (1 + 3 * x ^ 2))⁻¹ * (4 * √3 * x ^ 4)),
        strongL₁ x * ((2 * x ^ 2 * (1 + 3 * x ^ 2))⁻¹ * -(√3 * (1 + x ^ 2) * (3 * x ^ 2 - 1))),
        0, strongLR x * x ^ 2, strongLR x] k) (ipc_Fam y (ellSw y) k) y := by
    intro k
    fin_cases k
    · simpa [ipc_Fam] using hasDerivAt_const y (0 : ℝ)
    · exact ipc_hasDerivAt_of_eq (hasDerivAt_neg y) (fun z ↦ by simp) (by simp [ipc_Fam])
    · refine ipc_hasDerivAt_of_eq ((hasDerivAt_id y).inv hy.ne') (fun z ↦ by simp) ?_
      simp [ipc_Fam]
    · simpa [ipc_Fam] using hasDerivAt_const y (0 : ℝ)
    · refine ipc_hasDerivAt_of_eq (hL.fun_mul hc4) (fun z ↦ by simp) ?_
      simp only [ipc_Fam, strongL₁]
      simp
      field_simp
      ipc_ring
    · refine ipc_hasDerivAt_of_eq (hL.fun_mul hc5) (fun z ↦ by simp) ?_
      simp only [ipc_Fam, strongL₁]
      simp
      field_simp
      ipc_ring
    · simpa [ipc_Fam] using hasDerivAt_const y (0 : ℝ)
    · refine ipc_hasDerivAt_of_eq (hR.fun_mul (hasDerivAt_pow 2 y)) (fun z ↦ by simp) ?_
      simp only [ipc_Fam, strongLR]
      simp
      field_simp
      ipc_ring
    · refine ipc_hasDerivAt_of_eq hR (fun z ↦ by simp) ?_
      simp only [ipc_Fam]
      simp
      field_simp
      ipc_ring
  exact hasDerivAt_pi.2 hall

lemma ipc_phaseCoords_eq (q : iso_PhasePt) (v : Fin 9 → ℝ)
    (h1 : q.1 = !![v 0, v 1; v 2, -v 0]) (h2 : q.2.1 = !![v 3, v 4; v 5, -v 3])
    (h3 : q.2.2 = !![v 6, v 7; v 8, -v 6]) : iso_phaseCoords q = v := by
  obtain ⟨X, L, R⟩ := q
  simp only at h1 h2 h3
  subst h1 h2 h3
  funext k
  fin_cases k <;> rfl

lemma ipc_Vq_X (y : ℝ) (hy : 0 < y) :
    ipc_Pm y * Φ 0 y - Φ 0 y * ipc_Pm y =
      !![ipc_Vq y (ellSw y) 0, ipc_Vq y (ellSw y) 1; ipc_Vq y (ellSw y) 2,
        -ipc_Vq y (ellSw y) 0] := by
  have h3 : (0 : ℝ) < √3 := by positivity
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ipc_Pm, Φ, ipc_Vq] <;> field_simp <;> ipc_ring

lemma ipc_Vq_L (y : ℝ) (hy : 0 < y) :
    strongL₁ y • Λ₁₀ y * Φ 0 y - Φ 0 y * (strongL₁ y • Λ₁₀ y) =
      !![ipc_Vq y (ellSw y) 3, ipc_Vq y (ellSw y) 4; ipc_Vq y (ellSw y) 5,
        -ipc_Vq y (ellSw y) 3] := by
  have h3 : (0 : ℝ) < √3 := by positivity
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Φ, Λ₁₀, strongL₁, ipc_Vq] <;>
    field_simp <;> ipc_ring

lemma ipc_Vq_R (y : ℝ) (hy : 0 < y) :
    costateRHS (-1) (strongL₁ y • Λ₁₀ y) (strongLR y • !![0, y ^ 2; 1, 0]) (Φ 0 y) (vertex 2) =
      !![ipc_Vq y (ellSw y) 6, ipc_Vq y (ellSw y) 7; ipc_Vq y (ellSw y) 8,
        -ipc_Vq y (ellSw y) 6] := by
  have h3 : (0 : ℝ) < √3 := by positivity
  have hP : controlP (vertex 2) (Φ 0 y) = ipc_Pm y := str_segP_eq y hy.ne'
  simp only [costateRHS, hP]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ipc_Pm, Φ, Λ₁₀, strongL₁, strongLR, J, traceForm, Matrix.trace_fin_two, ipc_Vq] <;>
    field_simp <;> ipc_ring

/-- The vector field at `q_fix(y₀)`, in coordinates. -/
theorem ipc_Vq_eq (y : ℝ) (hy : 0 < y) :
    iso_phaseCoords (controlP (vertex 2) (Φ 0 y) * Φ 0 y - Φ 0 y * controlP (vertex 2) (Φ 0 y),
      strongL₁ y • Λ₁₀ y * Φ 0 y - Φ 0 y * (strongL₁ y • Λ₁₀ y),
      costateRHS (-1) (strongL₁ y • Λ₁₀ y) (strongLR y • !![0, y ^ 2; 1, 0]) (Φ 0 y) (vertex 2)) =
      ipc_Vq y (ellSw y) := by
  have hP : controlP (vertex 2) (Φ 0 y) = ipc_Pm y := str_segP_eq y hy.ne'
  refine ipc_phaseCoords_eq _ _ ?_ (ipc_Vq_L y hy) (ipc_Vq_R y hy)
  rw [hP]
  exact ipc_Vq_X y hy

lemma ipc_Ft_X (y : ℝ) (hy : 0 < y) :
    R * (ipc_Pm y * (R⁻¹ * Φ 0 y * R) - R⁻¹ * Φ 0 y * R * ipc_Pm y) * R⁻¹ =
      !![ipc_Ft y (ellSw y) 0, ipc_Ft y (ellSw y) 1; ipc_Ft y (ellSw y) 2,
        -ipc_Ft y (ellSw y) 0] := by
  have h3 : (0 : ℝ) < √3 := by positivity
  rw [poly_R_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [R, ipc_Pm, Φ, ipc_Ft, Matrix.mul_apply] <;> field_simp <;> ipc_ring

lemma ipc_Ft_L (y : ℝ) (hy : 0 < y) :
    R * (R⁻¹ * (strongL₁ y • Λ₁₀ y) * R * (R⁻¹ * Φ 0 y * R) -
        R⁻¹ * Φ 0 y * R * (R⁻¹ * (strongL₁ y • Λ₁₀ y) * R)) * R⁻¹ =
      !![ipc_Ft y (ellSw y) 3, ipc_Ft y (ellSw y) 4; ipc_Ft y (ellSw y) 5,
        -ipc_Ft y (ellSw y) 3] := by
  have h3 : (0 : ℝ) < √3 := by positivity
  rw [poly_R_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [R, Φ, Λ₁₀, strongL₁, ipc_Ft, Matrix.mul_apply] <;>
    field_simp <;> ipc_ring

/-- `R P R⁻¹` at the octagon. -/
noncomputable def ipc_Pt (y : ℝ) : Mat2 := !![-(√3 * y / 2), y; 0, √3 * y / 2]

lemma ipc_conj_costateRHS (y : ℝ) (hy : 0 < y) (A B : Mat2) :
    R * costateRHS (-1) (R⁻¹ * A * R) (R⁻¹ * B * R) (R⁻¹ * Φ 0 y * R) (vertex 2) * R⁻¹ =
      (ipc_Pt y * B - B * ipc_Pt y) -
        traceForm B (ipc_Pt y) • (ipc_Pt y * Φ 0 y - Φ 0 y * ipc_Pt y) +
        ((-A + (3 / 2 * (-1 : ℝ)) • J) * Φ 0 y - Φ 0 y * (-A + (3 / 2 * (-1 : ℝ)) • J)) := by
  have h3 : (0 : ℝ) < √3 := by positivity
  have hRR : R * R⁻¹ = 1 := poly_R_mul_inv
  have hRR' : R⁻¹ * R = 1 := poly_inv_mul_R
  have hPt : R⁻¹ * ipc_Pt y * R = ipc_Pm y := by
    rw [poly_R_inv]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [R, ipc_Pt, ipc_Pm, Matrix.mul_apply] <;> field_simp <;> ipc_ring
  have hPc : controlP (vertex 2) (R⁻¹ * Φ 0 y * R) = ipc_Pm y := by
    have hc : traceForm (controlMatrix (vertex 2)) (R⁻¹ * Φ 0 y * R) = -2 / (3 * y) := by
      rw [poly_R_inv]
      simp [traceForm, controlMatrix, vertex, R, Φ, Matrix.trace_fin_two]
      field_simp
      ipc_ring
    rw [controlP, hc]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [controlMatrix, vertex, ipc_Pm] <;> field_simp <;> ipc_ring
  have hJ : R⁻¹ * J * R = J := by
    rw [Matrix.mul_assoc, poly_J_mul_R, ← Matrix.mul_assoc, hRR', Matrix.one_mul]
  have htf : traceForm (R⁻¹ * B * R) (ipc_Pm y) = traceForm B (ipc_Pt y) := by
    rw [← hPt, poly_traceForm_conj hRR]
  have hE : costateRHS (-1) (R⁻¹ * A * R) (R⁻¹ * B * R) (R⁻¹ * Φ 0 y * R) (vertex 2) =
      R⁻¹ * ((ipc_Pt y * B - B * ipc_Pt y) -
        traceForm B (ipc_Pt y) • (ipc_Pt y * Φ 0 y - Φ 0 y * ipc_Pt y) +
        ((-A + (3 / 2 * (-1 : ℝ)) • J) * Φ 0 y - Φ 0 y * (-A + (3 / 2 * (-1 : ℝ)) • J))) * R := by
    rw [costateRHS, hPc, htf]
    simp only [poly_conj_add, poly_conj_sub, poly_conj_smul, poly_conj_neg, poly_conj_mul hRR,
      hPt, hJ]
  rw [hE]
  simp only [← Matrix.mul_assoc, hRR, Matrix.one_mul]
  rw [Matrix.mul_assoc, hRR, Matrix.mul_one]

lemma ipc_Ft_R (y : ℝ) (hy : 0 < y) :
    R * costateRHS (-1) (R⁻¹ * (strongL₁ y • Λ₁₀ y) * R)
        (R⁻¹ * (strongLR y • !![0, y ^ 2; 1, 0]) * R) (R⁻¹ * Φ 0 y * R) (vertex 2) * R⁻¹ =
      !![ipc_Ft y (ellSw y) 6, ipc_Ft y (ellSw y) 7; ipc_Ft y (ellSw y) 8,
        -ipc_Ft y (ellSw y) 6] := by
  have h3 : (0 : ℝ) < √3 := by positivity
  rw [ipc_conj_costateRHS y hy]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ipc_Pt, Φ, Λ₁₀, strongL₁, strongLR, J, traceForm, Matrix.trace_fin_two, ipc_Ft] <;>
    field_simp <;> ipc_ring

/-- `Ad(R)` of the vector field at the end of the arc from `q_fix(y₀)`, in coordinates. -/
theorem ipc_Ft_eq (y : ℝ) (hy0 : 1 / √3 < y) :
    iso_phaseCoords (iso_adR
      (controlP (vertex 2) (segX y (switchTime y)) * segX y (switchTime y) -
          segX y (switchTime y) * controlP (vertex 2) (segX y (switchTime y)),
        strongΛ₁ y (switchTime y) * segX y (switchTime y) -
          segX y (switchTime y) * strongΛ₁ y (switchTime y),
        costateRHS (-1) (strongΛ₁ y (switchTime y)) (strongΛR y (switchTime y))
          (segX y (switchTime y)) (vertex 2))) = ipc_Ft y (ellSw y) := by
  have hy : 0 < y := poly_y0_pos hy0
  have hP : controlP (vertex 2) (segX y (switchTime y)) = ipc_Pm y := str_controlP_segX y _ hy
  obtain ⟨-, -, -, -, -, -, -, hR, h1⟩ := strongLift_isStrongLift y hy0
  rw [hP]
  rw [segX_switchTime y hy0, hR, h1, ipc_strongΛ₁_zero y hy, ipc_strongΛR_zero y hy]
  exact ipc_phaseCoords_eq _ _ (ipc_Ft_X y hy) (ipc_Ft_L y hy) (ipc_Ft_R y hy)

lemma ipc_linVec_L (y : ℝ) (hy0 : 1 / √3 < y) (a1 a2 a3 r1 r2 r3 : ℝ) :
    R * ipc_L1W y (4 / (3 * y ^ 2 + 1)) a1 a2 a3 * R⁻¹ =
      !![ipc_linVec y (ellSw y) a1 a2 a3 r1 r2 r3 3, ipc_linVec y (ellSw y) a1 a2 a3 r1 r2 r3 4;
        ipc_linVec y (ellSw y) a1 a2 a3 r1 r2 r3 5,
        -ipc_linVec y (ellSw y) a1 a2 a3 r1 r2 r3 3] := by
  have h3 : (0 : ℝ) < √3 := by positivity
  have hy : 0 < y := poly_y0_pos hy0
  rw [poly_R_inv]
  generalize ellSw y = L
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [R, ipc_L1W, Matrix.mul_apply, ipc_linVec] <;> field_simp <;> ipc_ring

lemma ipc_linVec_R (y : ℝ) (hy0 : 1 / √3 < y) (a1 a2 a3 r1 r2 r3 : ℝ) :
    R * ipc_LRW y (4 / (3 * y ^ 2 + 1)) (ellSw y / (√3 * y)) a1 a2 a3 r1 r2 r3 * R⁻¹ =
      !![ipc_linVec y (ellSw y) a1 a2 a3 r1 r2 r3 6, ipc_linVec y (ellSw y) a1 a2 a3 r1 r2 r3 7;
        ipc_linVec y (ellSw y) a1 a2 a3 r1 r2 r3 8,
        -ipc_linVec y (ellSw y) a1 a2 a3 r1 r2 r3 6] := by
  have h3 : (0 : ℝ) < √3 := by positivity
  have hy : 0 < y := poly_y0_pos hy0
  rw [poly_R_inv]
  generalize ellSw y = L
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [R, ipc_LRW, Matrix.mul_apply, ipc_linVec] <;> field_simp <;> ipc_ring

/-- The derivative of `Ad(R) q(t_sw, q)` in the costate directions, at `q_fix(y₀)`. -/
theorem ipc_linVec_eq (y : ℝ) (hy0 : 1 / √3 < y) (a1 a2 a3 r1 r2 r3 : ℝ) :
    iso_phaseCoords (iso_adR (0,
      ipc_cfΛ₁ (Φ 0 y, !![a1, a2; a3, -a1], !![r1, r2; r3, -r1]) (switchTime y),
      ipc_linΛR (Φ 0 y, !![a1, a2; a3, -a1], !![r1, r2; r3, -r1]) (switchTime y))) =
      ipc_linVec y (ellSw y) a1 a2 a3 r1 r2 r3 := by
  have hy : 0 < y := poly_y0_pos hy0
  rw [ipc_cfΛ₁_octagon y hy, ipc_linΛR_octagon y hy, str_exp_switchTime hy,
    show switchTime y = ellSw y / (√3 * y) from rfl]
  refine ipc_phaseCoords_eq _ _ ?_ (ipc_linVec_L y hy0 a1 a2 a3 r1 r2 r3)
    (ipc_linVec_R y hy0 a1 a2 a3 r1 r2 r3)
  simp only [iso_adR, Matrix.mul_zero, Matrix.zero_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ipc_linVec]

/-- The derivative of `χ₃₁(q(t_sw, q))` in the costate directions, at `q_fix(y₀)`. -/
theorem ipc_Glin_eq (y : ℝ) (hy0 : 1 / √3 < y) (a1 a2 a3 r1 r2 r3 : ℝ) :
    switchingFn 2 0 (ipc_linΛR (Φ 0 y, !![a1, a2; a3, -a1], !![r1, r2; r3, -r1]) (switchTime y))
      (segX y (switchTime y)) = ipc_Glin y (ellSw y) a1 a2 a3 r1 r2 r3 := by
  have h3 : (0 : ℝ) < √3 := by positivity
  have hy : 0 < y := poly_y0_pos hy0
  rw [str_switchingFn_eq, str_traceForm_Z1_switchTime y hy, (str_traceForm_segX y _ hy).2.2,
    ipc_linΛR_octagon y hy, str_exp_switchTime hy, show switchTime y = ellSw y / (√3 * y) from rfl]
  generalize ellSw y = L
  simp [traceForm, controlMatrix, vertex, ipc_LRW, ipc_Glin, Matrix.trace_fin_two]
  field_simp
  ipc_ring

end SmoothedPolygons
