module

public import SmoothedPolygons.Ch7.Polygon
public import Basic.Analysis.Calculus.MatrixFTC
public import Mathlib.MeasureTheory.Function.Floor

/-!
# The discreteness condition (Lemma 7.5.5)

Lemma 7.5.5 is about any state trajectory with the control of the spline, so we first show that
the spline of the smoothed polygon (for any `y₀ ∈ (1/√3, 1)` and `N` switching intervals of length
`τ = t_sw(y₀)`) is a state trajectory and the only one with its control and initial values.

* `poly_pw A B τ f₀` is the piecewise curve `Aⁿ f₀(t - nτ) Bⁿ` on `[nτ, (n+1)τ)`; `polygonX` and
  `polygonG` are of this form. If `f₀(τ) = A f₀(0) B`, it is continuous and equal to
  `Aⁱ f₀(t - iτ) Bⁱ` on the closed interval `[iτ, (i+1)τ]` (`poly_pw_of_mem_Icc`), and it is an
  integral curve of any right-hand side that agrees on `[iτ, (i+1)τ)` with the conjugates of the
  derivative of `f₀` (`poly_pw_isIntegralCurve`).
* On the `i`-th switching interval the control is `R⁻ⁱ · e₃` and the spline is the `R⁻ⁱ`-conjugate
  of the `e₃`-trajectory (`R⁻¹ Z_{e_m} R = Z_{e_{m+1}}`, `R_conj_controlMatrix_vertex`); the
  strong boundary condition `X(z₀, t_sw) = R⁻¹ X₀ R` (`segX_switchTime`) glues the pieces.
  Hence `poly_isStateTrajectory`.
* Uniqueness (`poly_trajectory_unique`): on each switching interval the control is constant, so
  `⟨X, Z_u⟩` is constant (Lemma 7.1.1), `X' = [P, X]` is linear with constant `P`, and `g' = gX`;
  both are solved uniquely, interval after interval.
* Lemma 7.5.5 compares eigenvalues of `R⁻¹ g_sw` (`poly_pow_eq_of_trace`).
-/

@[expose] public section

namespace SmoothedPolygons

open Matrix Set MeasureTheory
open scoped Topology

/-! ### The rotation `R` -/

lemma poly_sqrt3_sq : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

lemma poly_sqrt3_pow3 : √3 ^ 3 = 3 * √3 := by rw [pow_succ, poly_sqrt3_sq]

lemma poly_R_mul_Rinv' : R * !![1 / 2, √3 / 2; -(√3 / 2), 1 / 2] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [R] <;> ring_nf <;> norm_num

/-- `R⁻¹ = [[1/2, √3/2], [-√3/2, 1/2]]`. -/
lemma poly_R_inv : R⁻¹ = !![1 / 2, √3 / 2; -(√3 / 2), 1 / 2] :=
  Matrix.inv_eq_right_inv poly_R_mul_Rinv'

lemma poly_R_mul_inv : R * R⁻¹ = 1 := by rw [poly_R_inv, poly_R_mul_Rinv']

lemma poly_inv_mul_R : R⁻¹ * R = 1 := by
  rw [poly_R_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [R] <;> ring_nf <;> norm_num

lemma poly_det_R : R.det = 1 := by
  simp [R, Matrix.det_fin_two]
  ring_nf
  norm_num

lemma poly_det_Rinv : (R⁻¹).det = 1 := by
  rw [Matrix.det_nonsing_inv, poly_det_R, Ring.inverse_one]

/-- `R³ = -I₂` (`R` is the rotation by `π/3`). -/
lemma poly_R_pow_three : R ^ 3 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [R, pow_succ] <;> ring_nf <;>
    simp only [poly_sqrt3_sq, poly_sqrt3_pow3] <;> ring

lemma poly_Rinv_pow_three : R⁻¹ ^ 3 = -1 := by
  rw [poly_R_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_succ] <;> ring_nf <;>
    simp only [poly_sqrt3_sq, poly_sqrt3_pow3] <;> ring

lemma poly_J_mul_R : J * R = R * J := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [R, J]

lemma poly_Rpow_mul_Rinvpow (i : ℕ) : R ^ i * R⁻¹ ^ i = 1 := pow_mul_pow_eq_one i poly_R_mul_inv

lemma poly_Rinvpow_mul_Rpow (i : ℕ) : R⁻¹ ^ i * R ^ i = 1 := pow_mul_pow_eq_one i poly_inv_mul_R

/-! ### Conjugation -/

section Conj

variable {Ci C : Mat2}

lemma poly_conj_mul (h : C * Ci = 1) (M N : Mat2) :
    Ci * (M * N) * C = (Ci * M * C) * (Ci * N * C) := by
  have : C * (Ci * (N * C)) = N * C := by rw [← Matrix.mul_assoc, h, Matrix.one_mul]
  simp only [Matrix.mul_assoc, this]

lemma poly_conj_sub (M N : Mat2) : Ci * (M - N) * C = Ci * M * C - Ci * N * C := by
  rw [Matrix.mul_sub, Matrix.sub_mul]

lemma poly_conj_add (M N : Mat2) : Ci * (M + N) * C = Ci * M * C + Ci * N * C := by
  rw [Matrix.mul_add, Matrix.add_mul]

lemma poly_conj_neg (M : Mat2) : Ci * (-M) * C = -(Ci * M * C) := by
  rw [Matrix.mul_neg, Matrix.neg_mul]

lemma poly_conj_smul (c : ℝ) (M : Mat2) : Ci * (c • M) * C = c • (Ci * M * C) := by
  rw [Matrix.mul_smul, Matrix.smul_mul]

lemma poly_conj_bracket (h : C * Ci = 1) (P M : Mat2) :
    Ci * (P * M - M * P) * C = (Ci * P * C) * (Ci * M * C) - (Ci * M * C) * (Ci * P * C) := by
  rw [poly_conj_sub, poly_conj_mul h, poly_conj_mul h]

lemma poly_trace_conj (h : C * Ci = 1) (M : Mat2) : (Ci * M * C).trace = M.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, h, Matrix.one_mul]

lemma poly_traceForm_conj (h : C * Ci = 1) (M N : Mat2) :
    traceForm (Ci * M * C) (Ci * N * C) = traceForm M N := by
  unfold traceForm
  rw [← poly_conj_mul h, poly_trace_conj h]

lemma poly_det_conj (h : C * Ci = 1) (M : Mat2) : (Ci * M * C).det = M.det := by
  have hd := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_one] at hd
  rw [Matrix.det_mul, Matrix.det_mul]
  linear_combination M.det * hd

lemma poly_controlP_conj (h : C * Ci = 1) {u w : Fin 3 → ℝ}
    (hZ : Ci * controlMatrix u * C = controlMatrix w) (S : Mat2) :
    Ci * controlP u S * C = controlP w (Ci * S * C) := by
  unfold controlP
  rw [← hZ, poly_traceForm_conj h, poly_conj_smul]

end Conj

lemma poly_traceForm_comm (M N : Mat2) : traceForm M N = traceForm N M := Matrix.trace_mul_comm M N

/-! ### The vertices of `U_T` and the star states under the rotation -/

lemma poly_vertex_mem (j : Fin 3) : vertex j ∈ controlSimplex := by
  refine ⟨fun i ↦ ?_, ?_⟩ <;> fin_cases j <;> (try fin_cases i) <;> simp [vertex]

/-- `R⁻¹ Z_{e_m} R = Z_{e_{m+1}}` (indices mod 3), from `R_conj_controlMatrix_vertex`. -/
lemma poly_Rinv_conj_vertex (m : Fin 3) :
    R⁻¹ * controlMatrix (vertex m) * R = controlMatrix (vertex (m + 1)) := by
  obtain ⟨h2, h1, h0⟩ := R_conj_controlMatrix_vertex
  have key : ∀ Z Z' : Mat2, R * Z' * R⁻¹ = Z → R⁻¹ * Z * R = Z' := by
    intro Z Z' hZ
    rw [← hZ, show R⁻¹ * (R * Z' * R⁻¹) * R = (R⁻¹ * R) * Z' * (R⁻¹ * R) by
      simp only [Matrix.mul_assoc], poly_inv_mul_R, Matrix.one_mul, Matrix.mul_one]
  fin_cases m
  · exact key _ _ h1
  · exact key _ _ h2
  · exact key _ _ h0

lemma poly_conj_pow_vertex (i : ℕ) (m : Fin 3) :
    R⁻¹ ^ i * controlMatrix (vertex m) * R ^ i =
      controlMatrix (vertex ⟨(m.val + i) % 3, Nat.mod_lt _ (by norm_num)⟩) := by
  induction i with
  | zero => simp [Nat.mod_eq_of_lt m.isLt]
  | succ i ih =>
    rw [pow_succ', pow_succ, show R⁻¹ * R⁻¹ ^ i * controlMatrix (vertex m) * (R ^ i * R) =
      R⁻¹ * (R⁻¹ ^ i * controlMatrix (vertex m) * R ^ i) * R by simp only [Matrix.mul_assoc],
      ih, poly_Rinv_conj_vertex]
    congr 2
    ext
    simp only [Fin.val_add]
    simp
    omega

/-- The index `(2 + i) mod 3` of the control `R⁻ⁱ · e₃` on the `i`-th switching interval. -/
def poly_idx (i : ℕ) : Fin 3 := ⟨(2 + i) % 3, Nat.mod_lt _ (by norm_num)⟩

lemma poly_polygonControlAt_eq (τ t : ℝ) :
    polygonControlAt τ t = vertex (poly_idx ⌊t / τ⌋₊) := rfl

lemma poly_conj_pow_vertex_two (i : ℕ) :
    R⁻¹ ^ i * controlMatrix (vertex 2) * R ^ i = controlMatrix (vertex (poly_idx i)) :=
  poly_conj_pow_vertex i 2

lemma poly_conj_pow_J (i : ℕ) : R⁻¹ ^ i * J * R ^ i = J := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', pow_succ, show R⁻¹ * R⁻¹ ^ i * J * (R ^ i * R) =
      R⁻¹ * (R⁻¹ ^ i * J * R ^ i) * R by simp only [Matrix.mul_assoc], ih, Matrix.mul_assoc,
      poly_J_mul_R, ← Matrix.mul_assoc, poly_inv_mul_R, Matrix.one_mul]

lemma poly_traceForm_neg {u : Fin 3 → ℝ} (hu : u ∈ controlSimplex) {X : Mat2}
    (hX : IsStarState X) : traceForm (controlMatrix u) X < 0 :=
  (lemma3_3_4 X hX.1).1 ⟨hX.2.2.1, hX.2.2.2.1, hX.2.2.2.2⟩ u hu

lemma poly_isStarState_Rinv_conj {S : Mat2} (hS : IsStarState S) :
    IsStarState (R⁻¹ * S * R) := by
  obtain ⟨htr, hdet, h0, h1, h2⟩ := hS
  have htr' : (R⁻¹ * S * R).trace = 0 := by rw [poly_trace_conj poly_R_mul_inv, htr]
  have hρ := ρ_R_conj (R⁻¹ * S * R) htr'
  rw [show R * (R⁻¹ * S * R) * R⁻¹ = (R * R⁻¹) * S * (R * R⁻¹) by simp only [Matrix.mul_assoc],
    poly_R_mul_inv, Matrix.one_mul, Matrix.mul_one] at hρ
  exact ⟨htr', by rw [poly_det_conj poly_R_mul_inv, hdet], hρ.2.1 ▸ h1, hρ.2.2 ▸ h2, hρ.1 ▸ h0⟩

lemma poly_isStarState_conj_pow (i : ℕ) {S : Mat2} (hS : IsStarState S) :
    IsStarState (R⁻¹ ^ i * S * R ^ i) := by
  induction i with
  | zero => simpa using hS
  | succ i ih =>
    rw [pow_succ', pow_succ, show R⁻¹ * R⁻¹ ^ i * S * (R ^ i * R) =
      R⁻¹ * (R⁻¹ ^ i * S * R ^ i) * R by simp only [Matrix.mul_assoc]]
    exact poly_isStarState_Rinv_conj ih

/-- The bracket `[P, X]` of the state equation is equivariant under conjugation by `Rⁱ`. -/
lemma poly_conj_pow_rhs (i : ℕ) (S : Mat2) :
    R⁻¹ ^ i * (controlP (vertex 2) S * S - S * controlP (vertex 2) S) * R ^ i =
      controlP (vertex (poly_idx i)) (R⁻¹ ^ i * S * R ^ i) * (R⁻¹ ^ i * S * R ^ i) -
        (R⁻¹ ^ i * S * R ^ i) * controlP (vertex (poly_idx i)) (R⁻¹ ^ i * S * R ^ i) := by
  rw [poly_conj_bracket (poly_Rpow_mul_Rinvpow i),
    poly_controlP_conj (poly_Rpow_mul_Rinvpow i) (poly_conj_pow_vertex_two i)]

/-! ### Piecewise curves -/

/-- The piecewise curve `Aⁿ f₀(t - nτ) Bⁿ` on `[nτ, (n+1)τ)`, `n = ⌊t/τ⌋`. -/
noncomputable def poly_pw (A B : Mat2) (τ : ℝ) (f0 : ℝ → Mat2) (t : ℝ) : Mat2 :=
  A ^ ⌊t / τ⌋₊ * f0 (t - ⌊t / τ⌋₊ * τ) * B ^ ⌊t / τ⌋₊

lemma poly_polygonX_eq (y0 τ : ℝ) : polygonX y0 τ = poly_pw R⁻¹ R τ (segX y0) := rfl

lemma poly_polygonG_eq (y0 τ : ℝ) :
    polygonG y0 τ = poly_pw (segG y0 τ * R⁻¹) R τ (segG y0) := rfl

lemma poly_floor_eq {τ t : ℝ} (hτ : 0 < τ) {i : ℕ} (h1 : i * τ ≤ t) (h2 : t < (i + 1) * τ) :
    ⌊t / τ⌋₊ = i := by
  rw [Nat.floor_eq_iff (div_nonneg (le_trans (by positivity) h1) hτ.le)]
  exact ⟨(le_div_iff₀ hτ).2 h1, (div_lt_iff₀ hτ).2 h2⟩

lemma poly_floor_mem {τ t : ℝ} (hτ : 0 < τ) (ht : 0 ≤ t) :
    ⌊t / τ⌋₊ * τ ≤ t ∧ t < (⌊t / τ⌋₊ + 1) * τ :=
  ⟨(le_div_iff₀ hτ).1 (Nat.floor_le (div_nonneg ht hτ.le)),
    (div_lt_iff₀ hτ).1 (Nat.lt_floor_add_one _)⟩

section Piecewise

variable {A B : Mat2} {τ : ℝ} {f0 : ℝ → Mat2}

lemma poly_pw_of_mem_Ico (hτ : 0 < τ) {i : ℕ} {t : ℝ} (ht : t ∈ Ico (i * τ) ((i + 1) * τ)) :
    poly_pw A B τ f0 t = A ^ i * f0 (t - i * τ) * B ^ i := by
  rw [poly_pw, poly_floor_eq hτ ht.1 ht.2]

lemma poly_pw_of_mem_Icc (hτ : 0 < τ) (hglue : f0 τ = A * f0 0 * B) {i : ℕ} {t : ℝ}
    (ht : t ∈ Icc (i * τ) ((i + 1) * τ)) :
    poly_pw A B τ f0 t = A ^ i * f0 (t - i * τ) * B ^ i := by
  rcases ht.2.lt_or_eq with h | h
  · exact poly_pw_of_mem_Ico hτ ⟨ht.1, h⟩
  · rw [poly_pw_of_mem_Ico hτ (i := i + 1) ⟨by push_cast; exact h.ge, by push_cast; linarith⟩, h]
    push_cast
    rw [show ((i : ℝ) + 1) * τ - (i + 1) * τ = 0 by ring,
      show ((i : ℝ) + 1) * τ - i * τ = τ by ring, hglue, pow_succ, pow_succ']
    simp only [Matrix.mul_assoc]

lemma poly_pw_continuousOn (hτ : 0 < τ) (hglue : f0 τ = A * f0 0 * B)
    (hf0 : ContinuousOn f0 (Icc 0 τ)) (N : ℕ) :
    ContinuousOn (poly_pw A B τ f0) (Icc 0 (N * τ)) := by
  induction N with
  | zero => simp
  | succ n ih =>
    have hpiece : ContinuousOn (poly_pw A B τ f0) (Icc (n * τ) ((n + 1) * τ)) := by
      refine ContinuousOn.congr ?_ fun t ht ↦ poly_pw_of_mem_Icc hτ hglue ht
      refine (continuousOn_const.mul (hf0.comp (continuous_sub_right _).continuousOn
        fun t ht ↦ ?_)).mul continuousOn_const
      simp only [mem_Icc] at ht ⊢
      constructor <;> linarith
    push_cast
    rw [← Icc_union_Icc_eq_Icc (b := n * τ) (by positivity) (by nlinarith)]
    exact ih.union_of_isClosed hpiece isClosed_Icc isClosed_Icc

lemma poly_pw_hasDerivAt (hτ : 0 < τ) {i : ℕ} {t : ℝ} (ht : t ∈ Ioo (i * τ) ((i + 1) * τ))
    {f0' : Mat2} (hd : HasDerivAtEntrywise f0 f0' (t - i * τ)) :
    HasDerivAtEntrywise (poly_pw A B τ f0) (A ^ i * f0' * B ^ i) t := by
  have h1 : HasDerivAtEntrywise (fun s ↦ f0 (s - i * τ)) ((1 : ℝ) • f0') t :=
    HasDerivAtEntrywise.scomp (h := fun s ↦ s - i * τ) hd ((hasDerivAt_id' t).sub_const _)
  have h2 := (h1.const_mul (A ^ i)).mul_const (B ^ i)
  rw [one_smul] at h2
  refine h2.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact poly_pw_of_mem_Ico hτ ⟨hs.1.le, hs.2⟩

/-- A piecewise curve assembled from conjugates of a curve `f₀` with derivative `v₀` on
`(0, τ)` is an integral curve of a right-hand side `v` that agrees with the conjugates of `v₀`. -/
theorem poly_pw_isIntegralCurve (hτ : 0 < τ) {v0 : ℝ → Mat2} (hglue : f0 τ = A * f0 0 * B)
    (hf0 : ContinuousOn f0 (Icc 0 τ)) (hv0 : ContinuousOn v0 (Icc 0 τ))
    (hd : ∀ s ∈ Ioo 0 τ, HasDerivAtEntrywise f0 (v0 s) s) (N : ℕ) {v : ℝ → Mat2}
    (hv : ∀ i < N, ∀ t ∈ Ico (i * τ) ((i + 1) * τ), v t = A ^ i * v0 (t - i * τ) * B ^ i) :
    IsIntegralCurve (poly_pw A B τ f0) v (N * τ) := by
  have hint : ∀ i j, IntervalIntegrable (fun s ↦ v s i j) volume 0 (N * τ) := by
    intro i j
    have := IntervalIntegrable.trans_iterate (f := fun s ↦ v s i j) (μ := volume)
      (a := fun k : ℕ ↦ (k : ℝ) * τ) (n := N) ?_
    · simpa using this
    intro k hk
    have hle : (k : ℝ) * τ ≤ ((k + 1 : ℕ) : ℝ) * τ := by push_cast; nlinarith
    rw [intervalIntegrable_iff_integrableOn_Ico_of_le hle]
    have hc : ContinuousOn (fun s ↦ (A ^ k * v0 (s - k * τ) * B ^ k) i j)
        (Icc ((k : ℝ) * τ) (((k + 1 : ℕ) : ℝ) * τ)) := by
      have : ContinuousOn (fun s ↦ A ^ k * v0 (s - k * τ) * B ^ k)
          (Icc ((k : ℝ) * τ) (((k + 1 : ℕ) : ℝ) * τ)) := by
        refine (continuousOn_const.mul (hv0.comp (continuous_sub_right _).continuousOn
          fun t ht ↦ ?_)).mul continuousOn_const
        push_cast at ht
        simp only [mem_Icc] at ht ⊢
        constructor <;> linarith
      exact (continuousOn_iff_entrywise.1 this) i j
    refine ((hc.integrableOn_Icc).mono_set Ico_subset_Icc_self).congr_fun
      (fun s hs ↦ ?_) measurableSet_Ico
    push_cast at hs
    simp only [hv k hk s hs]
  refine Matrix.eq_add_integral_of_hasDerivAtEntrywise_off_countable
    (S := range fun n : ℕ ↦ (n : ℝ) * τ) (countable_range _) (poly_pw_continuousOn hτ hglue hf0 N)
    ?_ hint
  rintro t ⟨⟨ht0, htN⟩, htS⟩
  obtain ⟨h1, h2⟩ := poly_floor_mem hτ ht0.le
  have h1' : (⌊t / τ⌋₊ : ℝ) * τ < t := lt_of_le_of_ne h1 fun h ↦ htS ⟨_, h⟩
  have hiN : ⌊t / τ⌋₊ < N :=
    (Nat.floor_lt (div_nonneg ht0.le hτ.le)).2 ((div_lt_iff₀ hτ).2 htN)
  have := poly_pw_hasDerivAt (A := A) (B := B) hτ ⟨h1', h2⟩
    (hd (t - ⌊t / τ⌋₊ * τ) ⟨by linarith, by linarith⟩)
  rwa [← hv _ hiN t ⟨h1, h2⟩] at this

end Piecewise

/-! ### Auxiliary facts for integral curves -/

/-- An integral curve on `[0, T]` restricted to `[a, b] ⊆ [0, T]`, with the right-hand side
replaced by a continuous `w` agreeing with it on `[a, b)`. -/
lemma poly_integral_form_restrict {f v w : ℝ → Mat2} {T a b : ℝ} (hI : IsIntegralCurve f v T)
    (ha : 0 ≤ a) (hab : a ≤ b) (hbT : b ≤ T) (hw : ContinuousOn w (Icc a b))
    (hvw : ∀ t ∈ Ico a b, v t = w t) :
    ∀ i j, IntervalIntegrable (fun s ↦ w s i j) volume a b ∧
      ∀ t ∈ Icc a b, f t i j = f a i j + ∫ s in a..t, w s i j := by
  intro i j
  obtain ⟨hint, heq⟩ := hI i j
  have hwij : ContinuousOn (fun s ↦ w s i j) (Icc a b) := continuousOn_iff_entrywise.1 hw i j
  refine ⟨hwij.intervalIntegrable_of_Icc hab, fun t ht ↦ ?_⟩
  have hT : 0 ≤ T := ha.trans (hab.trans hbT)
  have h0a : IntervalIntegrable (fun s ↦ v s i j) volume 0 a := hint.mono_set (by
    rw [uIcc_of_le ha, uIcc_of_le hT]; exact Icc_subset_Icc_right (hab.trans hbT))
  have hat : IntervalIntegrable (fun s ↦ v s i j) volume a t := hint.mono_set (by
    rw [uIcc_of_le ht.1, uIcc_of_le hT]; exact Icc_subset_Icc ha (ht.2.trans hbT))
  have hadd := intervalIntegral.integral_add_adjacent_intervals h0a hat
  have hcongr : ∫ s in a..t, v s i j = ∫ s in a..t, w s i j := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [(countable_singleton b).ae_notMem volume] with s hs hsI
    rw [uIoc_of_le ht.1] at hsI
    have : s ∈ Ico a b := ⟨hsI.1.le, lt_of_le_of_ne (hsI.2.trans ht.2) hs⟩
    rw [hvw s this]
  rw [heq t ⟨ha.trans ht.1, ht.2.trans hbT⟩, heq a ⟨ha, hab.trans hbT⟩, ← hcongr, ← hadd]
  ring

/-- An integral curve stays an integral curve when the right-hand side is changed off
`[0, T]`. -/
lemma poly_isIntegralCurve_congr {f v v' : ℝ → Mat2} {T : ℝ} (hI : IsIntegralCurve f v T)
    (hT : 0 ≤ T) (h : ∀ t ∈ Icc 0 T, v t = v' t) : IsIntegralCurve f v' T := by
  intro i j
  obtain ⟨hint, heq⟩ := hI i j
  refine ⟨hint.congr fun s hs ↦ ?_, fun t ht ↦ ?_⟩
  · rw [uIoc_of_le hT] at hs
    simp only [h s ⟨hs.1.le, hs.2⟩]
  · rw [heq t ht]
    congr 1
    refine intervalIntegral.integral_congr fun s hs ↦ ?_
    rw [uIcc_of_le ht.1] at hs
    simp only [h s ⟨hs.1, hs.2.trans ht.2⟩]

lemma poly_abs_bracket_le (P D : Mat2) (i j : Fin 2) :
    |(P * D - D * P) i j| ≤ (4 * ∑ k, ∑ l, |P k l|) * ∑ k, ∑ l, |D k l| := by
  set SP := ∑ k, ∑ l, |P k l|
  set SD := ∑ k, ∑ l, |D k l|
  have hle : ∀ M : Mat2, ∀ k l, |M k l| ≤ ∑ k, ∑ l, |M k l| := fun M k l ↦
    (Finset.single_le_sum (f := fun l ↦ |M k l|) (fun _ _ ↦ abs_nonneg _)
      (Finset.mem_univ l)).trans (Finset.single_le_sum (f := fun k ↦ ∑ l, |M k l|)
        (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) (Finset.mem_univ k))
  have hm : ∀ a b c d, |P a b * D c d| ≤ SP * SD := fun a b c d ↦ by
    rw [abs_mul]
    exact mul_le_mul (hle P a b) (hle D c d) (abs_nonneg _) ((abs_nonneg _).trans (hle P a b))
  have hm' : ∀ a b c d, |D c d * P a b| ≤ SP * SD := fun a b c d ↦ by
    rw [mul_comm]; exact hm a b c d
  simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]
  calc |P i 0 * D 0 j + P i 1 * D 1 j - (D i 0 * P 0 j + D i 1 * P 1 j)|
      ≤ |P i 0 * D 0 j| + |P i 1 * D 1 j| + (|D i 0 * P 0 j| + |D i 1 * P 1 j|) :=
        (abs_sub _ _).trans (add_le_add (abs_add_le _ _) (abs_add_le _ _))
    _ ≤ SP * SD + SP * SD + (SP * SD + SP * SD) :=
        add_le_add (add_le_add (hm _ _ _ _) (hm _ _ _ _)) (add_le_add (hm' _ _ _ _) (hm' _ _ _ _))
    _ = 4 * SP * SD := by ring

/-- The control `P = Z_u/⟨Z_u, X⟩` depends continuously on a continuous curve of star states. -/
lemma poly_controlP_continuousOn {S : ℝ → Mat2} {s : Set ℝ} (hS : ContinuousOn S s)
    {u : Fin 3 → ℝ} (hu : u ∈ controlSimplex) (hst : ∀ t ∈ s, IsStarState (S t)) :
    ContinuousOn (fun t ↦ controlP u (S t)) s := by
  unfold controlP
  refine ContinuousOn.smul (f := fun t ↦ (traceForm (controlMatrix u) (S t))⁻¹) ?_
    continuousOn_const
  refine ContinuousOn.inv₀ ?_ fun t ht ↦ (poly_traceForm_neg hu (hst t ht)).ne
  have hc : Continuous fun X : Mat2 ↦ traceForm (controlMatrix u) X :=
    (continuous_const.matrix_mul continuous_id).matrix_trace
  exact hc.comp_continuousOn hS

/-! ### The spline is a state trajectory -/

lemma poly_y0_pos {y0 : ℝ} (hy0 : 1 / √3 < y0) : 0 < y0 := lt_trans (by positivity) hy0

lemma poly_switchTime_pos {y0 : ℝ} (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) : 0 < switchTime y0 := by
  have hy : 0 < y0 := poly_y0_pos hy0
  unfold switchTime
  refine div_pos (Real.log_pos ?_) (by positivity)
  rw [lt_div_iff₀ (by positivity)]
  nlinarith

lemma poly_segX_continuous {y0 : ℝ} (hy : 0 < y0) : Continuous (segX y0) :=
  continuous_iff_continuousAt.2 fun t ↦ (seg_solution y0 t hy).2.1.continuousAt

lemma poly_segG_continuous {y0 : ℝ} (hy : 0 < y0) : Continuous (segG y0) :=
  continuous_iff_continuousAt.2 fun t ↦ (seg_solution y0 t hy).1.continuousAt

lemma poly_segX_glue {y0 : ℝ} (hy0 : 1 / √3 < y0) :
    segX y0 (switchTime y0) = R⁻¹ * segX y0 0 * R := by
  rw [segX_switchTime y0 hy0, (seg_solution y0 0 (poly_y0_pos hy0)).2.2.2.1]

lemma poly_segG_glue {y0 : ℝ} (hy : 0 < y0) (τ : ℝ) :
    segG y0 τ = segG y0 τ * R⁻¹ * segG y0 0 * R := by
  rw [(seg_solution y0 0 hy).2.2.1, Matrix.mul_one, Matrix.mul_assoc, poly_inv_mul_R,
    Matrix.mul_one]

lemma poly_Rpow_cancel (i : ℕ) (Y : Mat2) : R ^ i * (R⁻¹ ^ i * Y) = Y := by
  rw [← Matrix.mul_assoc, poly_Rpow_mul_Rinvpow, Matrix.one_mul]

lemma poly_mul_conj (A G X : Mat2) (i : ℕ) :
    A * G * R ^ i * (R⁻¹ ^ i * X * R ^ i) = A * (G * X) * R ^ i := by
  simp only [Matrix.mul_assoc, poly_Rpow_cancel]

lemma poly_measurable_polygonControlAt (τ : ℝ) : Measurable (polygonControlAt τ) := by
  change Measurable ((fun n : ℕ ↦ vertex (poly_idx n)) ∘ fun t : ℝ ↦ ⌊t / τ⌋₊)
  exact measurable_from_nat.comp (Nat.measurable_floor.comp (measurable_id.div_const τ))

/-- The spline of the smoothed polygon (general `y₀`, switching time `t_sw(y₀)`, `N` switching
intervals) is a state trajectory, with `g(0) = I₂` and `X(0) = Φ(i y₀)`. -/
theorem poly_isStateTrajectory (y0 : ℝ) (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) (N : ℕ)
    (hN : 1 ≤ N) :
    IsStateTrajectory (N * switchTime y0) (polygonControlAt (switchTime y0))
        (polygonG y0 (switchTime y0)) (polygonX y0 (switchTime y0)) ∧
      polygonG y0 (switchTime y0) 0 = 1 ∧ polygonX y0 (switchTime y0) 0 = Φ 0 y0 := by
  set τ := switchTime y0 with hτdef
  have hτ : 0 < τ := poly_switchTime_pos hy0 hy1
  have hy : 0 < y0 := poly_y0_pos hy0
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsegstar : ∀ s ∈ Icc 0 τ, IsStarState (segX y0 s) := fun s hs ↦ segX_star y0 hy0 hy1 s hs
  have hXc := (poly_segX_continuous hy).continuousOn (s := Icc 0 τ)
  refine ⟨⟨by positivity, poly_measurable_polygonControlAt τ, fun t _ ↦ poly_vertex_mem _,
    fun t ht ↦ ?_, ?_, ?_⟩, ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := poly_floor_mem hτ ht.1
    have hs : t - ⌊t / τ⌋₊ * τ ∈ Icc 0 τ := ⟨by linarith, by linarith⟩
    constructor
    · simp only [poly_polygonG_eq, poly_pw, Matrix.det_mul, Matrix.det_pow,
        (seg_solution y0 0 hy).2.2.2.2, poly_det_Rinv, poly_det_R]
      simp
    · rw [poly_polygonX_eq, poly_pw]
      exact poly_isStarState_conj_pow _ (hsegstar _ hs)
  · rw [poly_polygonG_eq]
    refine poly_pw_isIntegralCurve hτ (v0 := fun s ↦ segG y0 s * segX y0 s) (poly_segG_glue hy τ)
      (poly_segG_continuous hy).continuousOn
      ((poly_segG_continuous hy).mul (poly_segX_continuous hy)).continuousOn
      (fun s _ ↦ (seg_solution y0 s hy).1) N fun i _ t ht ↦ ?_
    rw [poly_pw_of_mem_Ico hτ ht, poly_polygonX_eq, poly_pw_of_mem_Ico hτ ht, poly_mul_conj]
  · rw [poly_polygonX_eq]
    have hP := poly_controlP_continuousOn hXc (poly_vertex_mem 2) hsegstar
    refine poly_pw_isIntegralCurve hτ (poly_segX_glue hy0) hXc
      ((hP.mul hXc).sub (hXc.mul hP)) (fun s _ ↦ (seg_solution y0 s hy).2.1) N fun i _ t ht ↦ ?_
    simp only [poly_polygonControlAt_eq, poly_floor_eq hτ ht.1 ht.2]
    rw [poly_pw_of_mem_Ico hτ ht]
    exact (poly_conj_pow_rhs i _).symm
  · simp [polygonG, (seg_solution y0 0 hy).2.2.1]
  · simp [polygonX, (seg_solution y0 0 hy).2.2.2.1]

/-! ### Uniqueness of the state trajectory with the spline's control -/

/-- The piece `R⁻ⁱ X(z₀, t - iτ) Rⁱ` of the spline on the `i`-th switching interval. -/
noncomputable def poly_Xp (y0 τ : ℝ) (i : ℕ) (t : ℝ) : Mat2 :=
  R⁻¹ ^ i * segX y0 (t - i * τ) * R ^ i

/-- The piece `(g_sw R⁻¹)ⁱ g₀(z₀, t - iτ) Rⁱ` of the spline on the `i`-th switching interval. -/
noncomputable def poly_Gp (y0 τ : ℝ) (i : ℕ) (t : ℝ) : Mat2 :=
  (segG y0 τ * R⁻¹) ^ i * segG y0 (t - i * τ) * R ^ i

lemma poly_Xp_continuous {y0 : ℝ} (hy : 0 < y0) (τ : ℝ) (i : ℕ) : Continuous (poly_Xp y0 τ i) :=
  (continuous_const.mul ((poly_segX_continuous hy).comp (continuous_sub_right _))).mul
    continuous_const

lemma poly_Gp_continuous {y0 : ℝ} (hy : 0 < y0) (τ : ℝ) (i : ℕ) : Continuous (poly_Gp y0 τ i) :=
  (continuous_const.mul ((poly_segG_continuous hy).comp (continuous_sub_right _))).mul
    continuous_const

lemma poly_Xp_hasDerivAt {y0 : ℝ} (hy : 0 < y0) (τ : ℝ) (i : ℕ) (t : ℝ) :
    HasDerivAtEntrywise (poly_Xp y0 τ i)
      (controlP (vertex (poly_idx i)) (poly_Xp y0 τ i t) * poly_Xp y0 τ i t -
        poly_Xp y0 τ i t * controlP (vertex (poly_idx i)) (poly_Xp y0 τ i t)) t := by
  have h1 := HasDerivAtEntrywise.scomp (h := fun s ↦ s - i * τ) (seg_solution y0 (t - i * τ) hy).2.1
    ((hasDerivAt_id' t).sub_const _)
  have h2 := (h1.const_mul (R⁻¹ ^ i)).mul_const (R ^ i)
  rw [one_smul, poly_conj_pow_rhs] at h2
  exact h2

lemma poly_Gp_hasDerivAt {y0 : ℝ} (hy : 0 < y0) (τ : ℝ) (i : ℕ) (t : ℝ) :
    HasDerivAtEntrywise (poly_Gp y0 τ i) (poly_Gp y0 τ i t * poly_Xp y0 τ i t) t := by
  have h1 := HasDerivAtEntrywise.scomp (h := fun s ↦ s - i * τ) (seg_solution y0 (t - i * τ) hy).1
    ((hasDerivAt_id' t).sub_const _)
  have h2 := (h1.const_mul ((segG y0 τ * R⁻¹) ^ i)).mul_const (R ^ i)
  rw [one_smul] at h2
  rw [poly_Gp, poly_Xp, poly_mul_conj]
  exact h2

lemma poly_Xp_eq {y0 τ : ℝ} (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) (hτ : τ = switchTime y0)
    {i : ℕ} {t : ℝ} (ht : t ∈ Icc (i * τ) ((i + 1) * τ)) : polygonX y0 τ t = poly_Xp y0 τ i t := by
  subst hτ
  rw [poly_polygonX_eq,
    poly_pw_of_mem_Icc (poly_switchTime_pos hy0 hy1) (poly_segX_glue hy0) ht, poly_Xp]

lemma poly_Gp_eq {y0 τ : ℝ} (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) (hτ : τ = switchTime y0)
    {i : ℕ} {t : ℝ} (ht : t ∈ Icc (i * τ) ((i + 1) * τ)) : polygonG y0 τ t = poly_Gp y0 τ i t := by
  subst hτ
  rw [poly_polygonG_eq, poly_pw_of_mem_Icc (poly_switchTime_pos hy0 hy1)
    (poly_segG_glue (poly_y0_pos hy0) _) ht, poly_Gp]

/-- Every point of `[0, Nτ]` lies in one of the `N` switching intervals. -/
lemma poly_exists_piece {τ : ℝ} (hτ : 0 < τ) {N : ℕ} (hN : 1 ≤ N) {t : ℝ}
    (ht : t ∈ Icc 0 (N * τ)) : ∃ i < N, t ∈ Icc (i * τ) ((i + 1) * τ) := by
  rcases ht.2.lt_or_eq with h | h
  · obtain ⟨h1, h2⟩ := poly_floor_mem hτ ht.1
    exact ⟨_, (Nat.floor_lt (div_nonneg ht.1 hτ.le)).2 ((div_lt_iff₀ hτ).2 h), h1, h2.le⟩
  · refine ⟨N - 1, by omega, ?_⟩
    rw [Nat.cast_sub hN, h]
    push_cast
    constructor <;> nlinarith

/-- **Uniqueness of the spline.** A state trajectory with the control of the spline
(`e₃, e₁, e₂, …` on `N` switching intervals of length `t_sw(y₀)`) and the initial values
`g(0) = I₂`, `X(0) = Φ(i y₀)` is the spline. On each switching interval the control is constant,
so `⟨X, Z_u⟩` is constant there (Lemma 7.1.1), `X` solves the linear equation `X' = [P, X]` with
constant `P`, and then `g` solves `g' = gX`; both agree with the spline by uniqueness for linear
ODEs, interval by interval. -/
theorem poly_trajectory_unique (y0 : ℝ) (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) (N : ℕ)
    (g X : ℝ → Mat2)
    (h : IsStateTrajectory (N * switchTime y0) (polygonControlAt (switchTime y0)) g X)
    (hg0 : g 0 = 1) (hX0 : X 0 = Φ 0 y0) :
    ∀ t ∈ Icc 0 (N * switchTime y0),
      g t = polygonG y0 (switchTime y0) t ∧ X t = polygonX y0 (switchTime y0) t := by
  set τ := switchTime y0 with hτdef
  have hτ : 0 < τ := poly_switchTime_pos hy0 hy1
  have hy : 0 < y0 := poly_y0_pos hy0
  obtain ⟨hT, -, -, hst, hgI, hXI⟩ := h
  have hXc : ContinuousOn X (Icc 0 (N * τ)) := Matrix.continuousOn_of_eq_add_integral hXI
  have hgc : ContinuousOn g (Icc 0 (N * τ)) := Matrix.continuousOn_of_eq_add_integral hgI
  have hN : 1 ≤ N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · simp [h0] at hT
    · exact h0
  -- one switching interval
  have hseg : ∀ i < N, g (i * τ) = poly_Gp y0 τ i (i * τ) → X (i * τ) = poly_Xp y0 τ i (i * τ) →
      ∀ t ∈ Icc (i * τ) ((i + 1) * τ), g t = poly_Gp y0 τ i t ∧ X t = poly_Xp y0 τ i t := by
    intro i hi hgi hXi
    have hiN : (i : ℝ) + 1 ≤ N := by exact_mod_cast hi
    have hab : (i : ℝ) * τ ≤ (i + 1) * τ := by nlinarith
    have ha0 : 0 ≤ (i : ℝ) * τ := by positivity
    have hbT : ((i : ℝ) + 1) * τ ≤ N * τ := by nlinarith
    have hsub : Icc ((i : ℝ) * τ) ((i + 1) * τ) ⊆ Icc 0 (N * τ) := Icc_subset_Icc ha0 hbT
    have hu : vertex (poly_idx i) ∈ controlSimplex := poly_vertex_mem _
    have hPc : ContinuousOn (fun t ↦ controlP (vertex (poly_idx i)) (X t))
        (Icc ((i : ℝ) * τ) ((i + 1) * τ)) :=
      poly_controlP_continuousOn (hXc.mono hsub) hu fun t ht ↦ (hst t (hsub ht)).2
    have hwc : ContinuousOn (fun t ↦ controlP (vertex (poly_idx i)) (X t) * X t -
        X t * controlP (vertex (poly_idx i)) (X t)) (Icc ((i : ℝ) * τ) ((i + 1) * τ)) :=
      (hPc.mul (hXc.mono hsub)).sub ((hXc.mono hsub).mul hPc)
    have hform := poly_integral_form_restrict hXI ha0 hab hbT hwc fun t ht ↦ by
      simp only [poly_polygonControlAt_eq, poly_floor_eq hτ ht.1 ht.2]
    have hXd := fun t (ht : t ∈ Icc ((i : ℝ) * τ) ((i + 1) * τ)) ↦
      Matrix.hasDerivWithinAtEntrywise_of_eq_add_integral hform ht (hwc t ht)
    -- Lemma 7.1.1: `⟨X, Z_u⟩` is constant on the switching interval
    have hconst := lemma7_1_1 _ X _ _ hXd
    have hP : ∀ t ∈ Icc ((i : ℝ) * τ) ((i + 1) * τ),
        controlP (vertex (poly_idx i)) (X t) = controlP (vertex (poly_idx i)) (X (i * τ)) := by
      intro t ht
      unfold controlP
      rw [poly_traceForm_comm _ (X t), hconst t ht, poly_traceForm_comm (X _)]
    have hYd := fun t (_ : t ∈ Icc ((i : ℝ) * τ) ((i + 1) * τ)) ↦
      (poly_Xp_hasDerivAt hy τ i t).hasDerivWithinAtEntrywise (s := Icc ((i : ℝ) * τ) ((i + 1) * τ))
    have hconstY := lemma7_1_1 _ (poly_Xp y0 τ i) _ _ hYd
    have hPY : ∀ t ∈ Icc ((i : ℝ) * τ) ((i + 1) * τ),
        controlP (vertex (poly_idx i)) (poly_Xp y0 τ i t) =
          controlP (vertex (poly_idx i)) (X (i * τ)) := by
      intro t ht
      unfold controlP
      rw [poly_traceForm_comm _ (poly_Xp y0 τ i t), hconstY t ht, ← hXi,
        poly_traceForm_comm (X _)]
    -- uniqueness for the linear equation `X' = [P, X]`
    have hXY : EqOn X (poly_Xp y0 τ i) (Icc ((i : ℝ) * τ) ((i + 1) * τ)) := by
      refine Matrix.ODE_solution_unique_of_bound_Icc
        (G := fun _ M ↦ controlP (vertex (poly_idx i)) (X (i * τ)) * M -
          M * controlP (vertex (poly_idx i)) (X (i * τ)))
        (K := 4 * ∑ k, ∑ l, |controlP (vertex (poly_idx i)) (X (i * τ)) k l|)
        (fun _ _ P Q k l ↦ ?_) (hXc.mono hsub) (fun t ht ↦ ?_)
        (poly_Xp_continuous hy τ i).continuousOn (fun t ht ↦ ?_) hXi
      · rw [← Matrix.sub_apply, show ∀ P0 : Mat2, P0 * P - P * P0 - (P0 * Q - Q * P0) =
          P0 * (P - Q) - (P - Q) * P0 from fun P0 ↦ by noncomm_ring]
        simpa only [Matrix.sub_apply] using poly_abs_bracket_le _ (P - Q) k l
      · have := hXd t (Ico_subset_Icc_self ht)
        rwa [hP t (Ico_subset_Icc_self ht)] at this
      · have := hYd t (Ico_subset_Icc_self ht)
        rwa [hPY t (Ico_subset_Icc_self ht)] at this
    -- then `g' = gX`
    have hgd : ∀ t ∈ Ico ((i : ℝ) * τ) ((i + 1) * τ), HasDerivWithinAtEntrywise g
        (g t * poly_Xp y0 τ i t) (Icc ((i : ℝ) * τ) ((i + 1) * τ)) t := by
      intro t ht
      have ht' := Ico_subset_Icc_self ht
      rw [← hXY ht']
      exact (Matrix.hasDerivWithinAtEntrywise_of_eq_add_integral hgI (hsub ht')
        ((hgc.mul hXc) t (hsub ht'))).mono hsub
    have hgG : EqOn g (poly_Gp y0 τ i) (Icc ((i : ℝ) * τ) ((i + 1) * τ)) :=
      Matrix.ODE_solution_unique_mul_right (poly_Xp_continuous hy τ i).continuousOn
        (hgc.mono hsub) hgd (poly_Gp_continuous hy τ i).continuousOn
        (fun t _ ↦ (poly_Gp_hasDerivAt hy τ i t).hasDerivWithinAtEntrywise) hgi
    exact fun t ht ↦ ⟨hgG ht, hXY ht⟩
  -- induction over the switching intervals
  have hall : ∀ i < N, ∀ t ∈ Icc ((i : ℝ) * τ) ((i + 1) * τ),
      g t = poly_Gp y0 τ i t ∧ X t = poly_Xp y0 τ i t := by
    intro i
    induction i with
    | zero =>
      intro h0
      refine hseg 0 h0 ?_ ?_
      · simp [poly_Gp, hg0, (seg_solution y0 0 hy).2.2.1]
      · simp [poly_Xp, hX0, (seg_solution y0 0 hy).2.2.2.1]
    | succ i ih =>
      intro hi
      have hmem : ((i + 1 : ℕ) : ℝ) * τ ∈ Icc ((i : ℝ) * τ) ((i + 1) * τ) := by
        push_cast; constructor <;> nlinarith
      have hmem' : ((i + 1 : ℕ) : ℝ) * τ ∈
          Icc (((i + 1 : ℕ) : ℝ) * τ) ((((i + 1 : ℕ) : ℝ) + 1) * τ) := by
        constructor <;> nlinarith
      obtain ⟨hg', hX'⟩ := ih (by omega) _ hmem
      refine hseg (i + 1) hi ?_ ?_
      · rw [hg', ← poly_Gp_eq hy0 hy1 hτdef hmem, poly_Gp_eq hy0 hy1 hτdef hmem']
      · rw [hX', ← poly_Xp_eq hy0 hy1 hτdef hmem, poly_Xp_eq hy0 hy1 hτdef hmem']
  intro t ht
  obtain ⟨i, hi, hti⟩ := poly_exists_piece hτ hN ht
  rw [poly_Gp_eq hy0 hy1 hτdef hti, poly_Xp_eq hy0 hy1 hτdef hti]
  exact hall i hi t hti

/-! ### Lemma 7.5.5 -/

lemma poly_Rinv_cancel (Y : Mat2) : R⁻¹ * (R * Y) = Y := by
  rw [← Matrix.mul_assoc, poly_inv_mul_R, Matrix.one_mul]

/-- The product form of the spline at the end of `n` switching intervals:
`g_sw (R⁻¹ g_sw R) ⋯ (R^{-(n-1)} g_sw R^{n-1}) = (g_sw R⁻¹)ⁿ Rⁿ`. -/
lemma poly_prod_eq (g : Mat2) (n : ℕ) :
    ((List.range n).map fun m ↦ (R⁻¹) ^ m * g * R ^ m).prod = (g * R⁻¹) ^ n * R ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Matrix.mul_one]
    rw [pow_succ (g * R⁻¹), pow_succ' R]
    simp only [Matrix.mul_assoc, poly_Rpow_cancel, poly_Rinv_cancel]

/-- Comparison of eigenvalues: a matrix `A ∈ SL₂(ℝ)` with `tr A = 2 cos θ` and `sin θ ≠ 0` has the
distinct eigenvalues `λ^{±1} = e^{±iθ}`, so it is diagonalizable over `ℂ`; if `nθ = πk`, then
`λ^{±n} = (-1)^k` and hence `Aⁿ = (-1)^k I₂`. -/
lemma poly_pow_eq_of_trace (A : Mat2) (hdet : A.det = 1) (θ' : ℝ) (hsin : Real.sin θ' ≠ 0)
    (htr : A.trace = 2 * Real.cos θ') (n k : ℕ) (hn : n * θ' = Real.pi * k) :
    A ^ n = (-1) ^ k := by
  have htr' : A 0 0 + A 1 1 = 2 * Real.cos θ' := by rw [Matrix.trace_fin_two] at htr; exact htr
  have hdet' : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by rw [Matrix.det_fin_two] at hdet; exact hdet
  have hb : A 0 1 ≠ 0 := by
    intro hb0
    rw [hb0, zero_mul, sub_zero] at hdet'
    have h1 : (A 0 0 - A 1 1) ^ 2 = -4 * Real.sin θ' ^ 2 := by
      have := Real.sin_sq_add_cos_sq θ'
      have h2 : (A 0 0 + A 1 1) ^ 2 = 4 * Real.cos θ' ^ 2 := by rw [htr']; ring
      nlinarith
    have : 0 < Real.sin θ' ^ 2 := by positivity
    nlinarith [sq_nonneg (A 0 0 - A 1 1)]
  -- the eigenvalues `λ = e^{iθ}` and `λ⁻¹ = e^{-iθ}`
  set l : ℂ := Complex.exp (θ' * Complex.I) with hldef
  set m : ℂ := Complex.exp (-θ' * Complex.I) with hmdef
  have hl : l = Real.cos θ' + Real.sin θ' * Complex.I := by
    rw [hldef, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hm : m = Real.cos θ' - Real.sin θ' * Complex.I := by
    rw [hmdef, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin]
    ring
  have hpy : (Real.sin θ' : ℂ) ^ 2 + (Real.cos θ' : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq θ'
  have hql : l ^ 2 - 2 * Real.cos θ' * l + 1 = 0 := by
    rw [hl]; linear_combination (Real.sin θ' : ℂ) ^ 2 * Complex.I_sq - hpy
  have hqm : m ^ 2 - 2 * Real.cos θ' * m + 1 = 0 := by
    rw [hm]; linear_combination (Real.sin θ' : ℂ) ^ 2 * Complex.I_sq - hpy
  have hnc : (n : ℂ) * ((θ' : ℂ) * Complex.I) = (k : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
    have := congrArg (fun r : ℝ ↦ (r : ℂ)) hn
    push_cast at this
    linear_combination this * Complex.I
  have hln : l ^ n = (-1) ^ k := by
    rw [hldef, ← Complex.exp_nat_mul, hnc, Complex.exp_nat_mul, Complex.exp_pi_mul_I]
  have hmn : m ^ n = (-1) ^ k := by
    rw [hmdef, ← Complex.exp_nat_mul, show (n : ℂ) * (-(θ' : ℂ) * Complex.I) =
      -((n : ℂ) * ((θ' : ℂ) * Complex.I)) by ring, hnc, Complex.exp_neg, Complex.exp_nat_mul,
      Complex.exp_pi_mul_I, ← inv_pow, inv_neg, inv_one]
  -- diagonalization over `ℂ`: `A P = P D` with `P` the matrix of eigenvectors
  set φ : Mat2 →+* Matrix (Fin 2) (Fin 2) ℂ := Complex.ofRealHom.mapMatrix with hφ
  set P : Matrix (Fin 2) (Fin 2) ℂ := !![(A 0 1 : ℂ), A 0 1; l - A 0 0, m - A 0 0] with hP
  set D : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![l, m] with hD
  have htrC : (A 0 0 : ℂ) + A 1 1 = 2 * Real.cos θ' := by exact_mod_cast htr'
  have hdetC : (A 0 0 : ℂ) * A 1 1 - A 0 1 * A 1 0 = 1 := by exact_mod_cast hdet'
  have hAP : φ A * P = P * D := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hφ, hP, hD, Matrix.mul_apply, Fin.sum_univ_two]
    · ring
    · ring
    · linear_combination (-1 : ℂ) * hql + l * htrC - hdetC
    · linear_combination (-1 : ℂ) * hqm + m * htrC - hdetC
  have hdetP : IsUnit P.det := by
    refine isUnit_iff_ne_zero.2 ?_
    rw [hP, Matrix.det_fin_two_of, hl, hm]
    have hb' : (A 0 1 : ℂ) ≠ 0 := by exact_mod_cast hb
    have hs' : (Real.sin θ' : ℂ) ≠ 0 := by exact_mod_cast hsin
    have : (A 0 1 : ℂ) * (Real.cos θ' - Real.sin θ' * Complex.I - A 0 0) -
        A 0 1 * (Real.cos θ' + Real.sin θ' * Complex.I - A 0 0) =
          -2 * (A 0 1 : ℂ) * Real.sin θ' * Complex.I := by ring
    rw [this]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hb') hs') Complex.I_ne_zero
  have hDn : D ^ n = ((-1 : ℂ) ^ k) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [hD, Matrix.diagonal_pow, Matrix.smul_one_eq_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp [hln, hmn]
  have hpow : φ A ^ n * P = P * D ^ n := ((SemiconjBy.pow_right hAP.symm n).eq).symm
  have hC : φ A ^ n = ((-1 : ℂ) ^ k) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    calc φ A ^ n = φ A ^ n * P * P⁻¹ := (Matrix.mul_nonsing_inv_cancel_right P _ hdetP).symm
      _ = ((-1 : ℂ) ^ k) • (P * P⁻¹) := by
          rw [hpow, hDn, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
      _ = ((-1 : ℂ) ^ k) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
          rw [Matrix.mul_nonsing_inv _ hdetP]
  rw [← map_pow] at hC
  rw [show (-1 : Mat2) ^ k = ((-1 : ℝ) ^ k) • (1 : Mat2) by
    rw [← neg_one_smul ℝ (1 : Mat2), smul_pow, one_pow]]
  ext i j
  have h1 := congr_fun (congr_fun hC i) j
  simp only [hφ, RingHom.mapMatrix_apply, Matrix.map_apply, Complex.ofRealHom_eq_coe,
    Matrix.smul_apply, smul_eq_mul] at h1
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply] at h1 ⊢
  split_ifs at h1 ⊢ <;> exact_mod_cast h1

/-- **Lemma 7.5.5** (`lem:discrete-k`). Consider a trajectory `g : [0, t_f] → SL₂(ℝ)` with
`g(0) = I₂` following the spline with `3k+1` control mode parts of equal duration `t_sw`
(`eqn:3k+1`), from `z₀ = i y₀`. The trajectory reaches `g(t_f) = R` at `t_f = (3k+1) t_sw`,
provided `4/(3y₀² + 1) = 2 cos θ_k` with `θ_k = πk/(3k+1)` (`eqn:theta-k`).

Proof: the trajectory is the spline (`poly_trajectory_unique`), so by the spline
equations `g(t_f) = g_sw (R⁻¹ g_sw R) ⋯ (R^{-3k} g_sw R^{3k})` (`polygonG_eq_prod`), and
`g(t_f) = R` is equivalent to `(R⁻¹ g_sw)^{3k+1} = R^{-3k} = (-I₂)^k` (`eqn:eigen`). The trace of
`R⁻¹ g_sw` is `4/(1 + 3y₀²) = 2 cos θ_k` (`trace_segG_switchTime`), so its eigenvalues are
`e^{±iθ_k}`, whose `(3k+1)`-th powers are `(-1)^k`; comparing eigenvalues (`poly_pow_eq_of_trace`)
gives `(R⁻¹ g_sw)^{3k+1} = (-1)^k I₂`.

Departure from the paper: the book's proof argues the converse direction: from `g(t_f) = R` it
compares eigenvalues to get `λ^{3k+1} = (-1)^k`, chooses the branch `ℓ = 0, -k`, and deduces the
trace. That does not prove the statement, which is the sufficiency ("provided"). The formal proof
runs the eigenvalue comparison the other way: the trace `2 cos θ_k` with `sin θ_k ≠ 0` gives the
distinct eigenvalues `e^{±iθ_k}`, so `R⁻¹ g_sw` is diagonalizable over `ℂ` and its `(3k+1)`-th
power is `(-1)^k I₂`; the choice of branch plays no role in this direction. It also proves that
every trajectory with this control and these initial values is the spline, which the book takes
for granted. -/
theorem lemma7_5_5 (k : ℕ) (hk : 1 ≤ k) (y0 : ℝ) (hy0 : 1 / √3 < y0) (hy1 : y0 < 1)
    (hθ : 4 / (3 * y0 ^ 2 + 1) = 2 * Real.cos (θ k)) (g X : ℝ → Mat2)
    (h : IsStateTrajectory ((3 * k + 1) * switchTime y0) (polygonControlAt (switchTime y0)) g X)
    (hg0 : g 0 = 1) (hX0 : X 0 = Φ 0 y0) :
    g ((3 * k + 1) * switchTime y0) = R := by
  set τ := switchTime y0 with hτdef
  have hτ : 0 < τ := poly_switchTime_pos hy0 hy1
  have hy : 0 < y0 := poly_y0_pos hy0
  have hT : ((3 * k + 1 : ℝ)) * τ = ((3 * k + 1 : ℕ) : ℝ) * τ := by push_cast; ring
  rw [hT] at h ⊢
  -- the trajectory is the spline
  rw [(poly_trajectory_unique y0 hy0 hy1 _ g X h hg0 hX0 _ ⟨by positivity, le_rfl⟩).1,
    polygonG_eq_prod]
  have hfl : ⌊((3 * k + 1 : ℕ) : ℝ) * τ / τ⌋₊ = 3 * k + 1 := by
    rw [mul_div_cancel_right₀ _ hτ.ne', Nat.floor_natCast]
  rw [hfl, sub_self, (seg_solution y0 0 hy).2.2.1, Matrix.mul_one, poly_Rinvpow_mul_Rpow,
    Matrix.mul_one, poly_prod_eq]
  -- comparing eigenvalues: `(R⁻¹ g_sw)^{3k+1} = (-I₂)^k`
  have hθpos : 0 < θ k := by
    unfold θ
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have := Real.pi_pos
    positivity
  have hθlt : θ k < Real.pi := by
    unfold θ
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  have hA : (R⁻¹ * segG y0 τ) ^ (3 * k + 1) = (-1) ^ k := by
    refine poly_pow_eq_of_trace _ ?_ (θ k) (Real.sin_pos_of_pos_of_lt_pi hθpos hθlt).ne' ?_ _ _ ?_
    · rw [Matrix.det_mul, poly_det_Rinv, (seg_solution y0 0 hy).2.2.2.2, one_mul]
    · rw [Matrix.trace_mul_comm, trace_segG_switchTime y0 hy0, ← hθ, add_comm]
    · unfold θ; field_simp; push_cast; ring
  have hsemi : SemiconjBy R (R⁻¹ * segG y0 τ) (segG y0 τ * R⁻¹) := by
    unfold SemiconjBy
    rw [← Matrix.mul_assoc, poly_R_mul_inv, Matrix.one_mul, Matrix.mul_assoc, poly_inv_mul_R,
      Matrix.mul_one]
  have h1 := (hsemi.pow_right (3 * k + 1)).eq
  rw [hA] at h1
  calc (segG y0 τ * R⁻¹) ^ (3 * k + 1) * R ^ (3 * k + 1)
      = (segG y0 τ * R⁻¹) ^ (3 * k + 1) * R * R ^ (3 * k) := by
        rw [pow_succ' R, Matrix.mul_assoc]
    _ = R * (-1) ^ k * (-1) ^ k := by rw [← h1, pow_mul, poly_R_pow_three]
    _ = R := by rw [Matrix.mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow,
        Matrix.mul_one]

end SmoothedPolygons
