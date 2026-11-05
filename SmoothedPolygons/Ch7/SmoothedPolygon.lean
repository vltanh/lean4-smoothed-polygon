module

public import SmoothedPolygons.Ch7.HMax
public import SmoothedPolygons.Ch7.DiscreteK
public import SmoothedPolygons.Ch7.Faces
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The smoothed `(6k+2)`-gons are Pontryagin extremals (Theorem 7.5.6)

The trajectory of the smoothed `(6k+2)`-gon is the state trajectory with the control
`polygonControl k` (`e₃, e₁, e₂, …` on `3k+1` switching intervals of length `t_sw`), `g(0) = I₂`
and `X(0) = Φ(i y₀)`, where `4/(3y₀² + 1) = 2 cos θ_k`. It exists and is unique; it is a bang-bang
Pontryagin extremal (Theorem 7.5.6). For `k = 1` it is the smoothed octagon, whose cost (the area
of the disk in circle representation) gives Reinhardt's density `(8 - √32 - ln 2)/(√8 - 1)`
(the example before Theorem 7.5.6).
-/

@[expose] public section

namespace SmoothedPolygons

open Matrix Set MeasureTheory

/-! ### The height `y₀` of the smoothed `(6k+2)`-gon -/

lemma poly_θ_pos {k : ℕ} (hk : 1 ≤ k) : 0 < θ k := by
  unfold θ
  have : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have := Real.pi_pos
  positivity

lemma poly_θ_lt (k : ℕ) : θ k < Real.pi / 3 := by
  unfold θ
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [Real.pi_pos]

lemma poly_cos_θ {k : ℕ} (hk : 1 ≤ k) : 1 / 2 < Real.cos (θ k) ∧ Real.cos (θ k) < 1 := by
  have h0 := poly_θ_pos hk
  have h1 := poly_θ_lt k
  have hpi := Real.pi_pos
  constructor
  · rw [← Real.cos_pi_div_three]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi h0.le (by linarith) h1
  · rw [← Real.cos_zero]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith) h0

lemma poly_y₀_sq {k : ℕ} (hk : 1 ≤ k) : y₀ k ^ 2 = (2 / Real.cos (θ k) - 1) / 3 := by
  obtain ⟨h1, h2⟩ := poly_cos_θ hk
  rw [y₀, Real.sq_sqrt]
  have : 2 < 2 / Real.cos (θ k) := by rw [lt_div_iff₀ (by linarith)]; linarith
  linarith

/-- For `k ≥ 1`, `y₀ ∈ (1/√3, 1)`: `θ_k ∈ (0, π/3)`, so `cos θ_k ∈ (1/2, 1)`. -/
lemma poly_y₀_mem {k : ℕ} (hk : 1 ≤ k) : 1 / √3 < y₀ k ∧ y₀ k < 1 := by
  obtain ⟨h1, h2⟩ := poly_cos_θ hk
  have hc : 0 < Real.cos (θ k) := by linarith
  have hsq := poly_y₀_sq hk
  have hy : 0 ≤ y₀ k := Real.sqrt_nonneg _
  have hlo : 1 / 3 < y₀ k ^ 2 := by
    rw [hsq]
    have : 2 < 2 / Real.cos (θ k) := by rw [lt_div_iff₀ hc]; linarith
    linarith
  have hhi : y₀ k ^ 2 < 1 := by
    rw [hsq]
    have : 2 / Real.cos (θ k) < 4 := by rw [div_lt_iff₀ hc]; linarith
    linarith
  have h3 : (0 : ℝ) < √3 := by positivity
  constructor
  · have h13 : (1 / √3) ^ 2 = 1 / 3 := by rw [div_pow, poly_sqrt3_sq]; norm_num
    nlinarith [sq_nonneg (y₀ k - 1 / √3), sq_nonneg (y₀ k + 1 / √3),
      show 0 < 1 / √3 by positivity]
  · nlinarith

/-- `4/(3y₀² + 1) = 2 cos θ_k` (`eqn:theta-k`). -/
lemma poly_y₀_trace {k : ℕ} (hk : 1 ≤ k) : 4 / (3 * y₀ k ^ 2 + 1) = 2 * Real.cos (θ k) := by
  have hc : 0 < Real.cos (θ k) := by linarith [(poly_cos_θ hk).1]
  rw [poly_y₀_sq hk]
  field_simp
  ring

/-! ### Bang-bang controls -/

/-- The vertices `e_j` are extreme points of `U_T`. -/
lemma poly_vertex_extreme (j : Fin 3) : vertex j ∈ Set.extremePoints ℝ controlSimplex := by
  rw [mem_extremePoints]
  refine ⟨poly_vertex_mem j, fun x hx y hy ⟨a, b, ha, hb, hab, hxy⟩ ↦ ?_⟩
  have h : ∀ i, a * x i + b * y i = vertex j i := fun i ↦ by
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using congr_fun hxy i
  -- off `j`, both coordinates vanish
  have hoff : ∀ i, i ≠ j → x i = 0 ∧ y i = 0 := by
    intro i hij
    have hi := h i
    rw [vertex, Pi.single_eq_of_ne hij] at hi
    have hx0 := (hx.1 i).1
    have hy0 := (hy.1 i).1
    constructor <;> nlinarith [mul_nonneg ha.le hx0, mul_nonneg hb.le hy0]
  -- at `j`, both coordinates are `1`
  have hsum : ∀ z ∈ controlSimplex, (∀ i, i ≠ j → z i = 0) → z = vertex j := by
    intro z hz hzoff
    have hs : ∑ i, z i = 1 := by rw [Fin.sum_univ_three]; exact hz.2
    rw [Finset.sum_eq_single j (fun i _ hij ↦ hzoff i hij) (by simp)] at hs
    funext i
    by_cases hij : i = j
    · subst hij
      rw [hs, vertex, Pi.single_eq_same]
    · rw [hzoff i hij, vertex, Pi.single_eq_of_ne hij]
  exact ⟨hsum x hx fun i hij ↦ (hoff i hij).1, hsum y hy fun i hij ↦ (hoff i hij).2⟩

/-! ### The Hamiltonian and the costate equation under the rotation -/

section Conj

variable {Ci C : Mat2}

/-- The Hamiltonian is invariant under simultaneous conjugation of the state and costates when
the control is permuted accordingly and `J` is fixed. -/
lemma poly_hamiltonian_conj (h : C * Ci = 1) (hJ : Ci * J * C = J) {u w : Fin 3 → ℝ}
    (hZ : Ci * controlMatrix u * C = controlMatrix w) (lam : ℝ) (L1 L S : Mat2) :
    hamiltonian lam (Ci * L1 * C) (Ci * L * C) (Ci * S * C) w = hamiltonian lam L1 L S u := by
  have h1 : Ci * L1 * C - (3 / 2 * lam) • J = Ci * (L1 - (3 / 2 * lam) • J) * C := by
    rw [poly_conj_sub, poly_conj_smul, hJ]
  unfold hamiltonian
  rw [h1, ← hZ, poly_traceForm_conj h, poly_traceForm_conj h, poly_traceForm_conj h]

/-- The costate equation for `Λ_R` is equivariant under conjugation. -/
lemma poly_costateRHS_conj (h : C * Ci = 1) (hJ : Ci * J * C = J) {u w : Fin 3 → ℝ}
    (hZ : Ci * controlMatrix u * C = controlMatrix w) (lam : ℝ) (L1 L S : Mat2) :
    Ci * costateRHS lam L1 L S u * C =
      costateRHS lam (Ci * L1 * C) (Ci * L * C) (Ci * S * C) w := by
  unfold costateRHS
  rw [← poly_traceForm_conj h L (controlP u S)]
  simp only [poly_conj_add, poly_conj_sub, poly_conj_smul, poly_conj_neg, poly_conj_mul h, hJ,
    poly_controlP_conj h hZ]

end Conj

lemma poly_traceForm_sub_right (M A B : Mat2) :
    traceForm M (A - B) = traceForm M A - traceForm M B := by
  simp only [traceForm, Matrix.mul_sub, Matrix.trace_sub]

lemma poly_traceForm_smul_right (M A : Mat2) (c : ℝ) :
    traceForm M (c • A) = c * traceForm M A := by
  simp only [traceForm, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

lemma poly_traceForm_add_right (M A B : Mat2) :
    traceForm M (A + B) = traceForm M A + traceForm M B := by
  simp only [traceForm, Matrix.mul_add, Matrix.trace_add]

/-- `χ_ij = H(e_i) - H(e_j)`. -/
lemma poly_hamiltonian_sub (lam : ℝ) (Λ₁ ΛR X : Mat2) (i j : Fin 3) :
    hamiltonian lam Λ₁ ΛR X (vertex i) - hamiltonian lam Λ₁ ΛR X (vertex j) =
      switchingFn i j ΛR X := by
  simp only [hamiltonian, switchingFn, controlP, poly_traceForm_sub_right,
    poly_traceForm_smul_right, poly_traceForm_comm X]
  ring

lemma poly_controlMatrix_eq (v : Fin 3 → ℝ) :
    controlMatrix v = v 0 • controlMatrix (vertex 0) + v 1 • controlMatrix (vertex 1) +
      v 2 • controlMatrix (vertex 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [controlMatrix, vertex] <;> ring

/-- The control-dependent part of the Hamiltonian `-⟨Λ_R, Z_u⟩/⟨X, Z_u⟩` is, on `U_T`, a convex
combination of its values at the vertices (with weights `u_j ⟨X, Z_{e_j}⟩/⟨X, Z_u⟩ ≥ 0`); so a
bound of the Hamiltonian at the vertices bounds it on `U_T`. -/
lemma poly_hamiltonian_le_of_vertices (lam : ℝ) (Λ₁ ΛR X : Mat2) (hX : IsStarState X) (c : ℝ)
    (hv : ∀ m : Fin 3, hamiltonian lam Λ₁ ΛR X (vertex m) ≤ c) :
    ∀ v ∈ controlSimplex, hamiltonian lam Λ₁ ΛR X v ≤ c := by
  intro v hv'
  have hd : ∀ m : Fin 3, traceForm X (controlMatrix (vertex m)) < 0 := fun m ↦ by
    rw [poly_traceForm_comm]; exact poly_traceForm_neg (poly_vertex_mem m) hX
  have hD : traceForm X (controlMatrix v) < 0 := by
    rw [poly_traceForm_comm]; exact poly_traceForm_neg hv' hX
  set A0 := traceForm (Λ₁ - (3 / 2 * lam) • J) X
  have ha : ∀ m, traceForm ΛR (controlMatrix (vertex m)) ≤
      (A0 - c) * traceForm X (controlMatrix (vertex m)) := by
    intro m
    have := hv m
    unfold hamiltonian at this
    have h' : A0 - c ≤ traceForm ΛR (controlMatrix (vertex m)) /
        traceForm X (controlMatrix (vertex m)) := by linarith
    exact (le_div_iff_of_neg (hd m)).1 h'
  unfold hamiltonian
  have hle : A0 - c ≤ traceForm ΛR (controlMatrix v) / traceForm X (controlMatrix v) := by
    rw [le_div_iff_of_neg hD]
    rw [poly_controlMatrix_eq v]
    simp only [poly_traceForm_add_right, poly_traceForm_smul_right]
    have h0 := mul_le_mul_of_nonneg_left (ha 0) (hv'.1 0).1
    have h1 := mul_le_mul_of_nonneg_left (ha 1) (hv'.1 1).1
    have h2 := mul_le_mul_of_nonneg_left (ha 2) (hv'.1 2).1
    nlinarith
  linarith

/-- Continuity of the right-hand side of the costate equation along continuous curves. -/
lemma poly_costateRHS_continuousOn {L1 L S : ℝ → Mat2} {s : Set ℝ} (lam : ℝ) {u : Fin 3 → ℝ}
    (hu : u ∈ controlSimplex) (h1 : ContinuousOn L1 s) (h2 : ContinuousOn L s)
    (h3 : ContinuousOn S s) (hst : ∀ t ∈ s, IsStarState (S t)) :
    ContinuousOn (fun t ↦ costateRHS lam (L1 t) (L t) (S t) u) s := by
  have hP := poly_controlP_continuousOn h3 hu hst
  have htf : ContinuousOn (fun t ↦ traceForm (L t) (controlP u (S t))) s :=
    (continuous_id.matrix_trace).comp_continuousOn (h2.mul hP)
  have hK : ContinuousOn (fun t ↦ -L1 t + (3 / 2 * lam) • J) s := h1.neg.add continuousOn_const
  unfold costateRHS
  exact (((hP.mul h2).sub (h2.mul hP)).sub (htf.smul ((hP.mul h3).sub (h3.mul hP)))).add
    ((hK.mul h3).sub (h3.mul hK))

/-- `R^{-(3k+1)} M R^{3k+1} = R⁻¹ M R`, since `R³ = -I₂` is central. -/
lemma poly_conj_pow_three_mul_add_one (k : ℕ) (M : Mat2) :
    R⁻¹ ^ (3 * k + 1) * M * R ^ (3 * k + 1) = R⁻¹ * M * R := by
  rw [pow_succ, pow_succ', pow_mul, pow_mul, poly_Rinv_pow_three, poly_R_pow_three,
    show (-1 : Mat2) ^ k = ((-1 : ℝ) ^ k) • (1 : Mat2) by
      rw [← neg_one_smul ℝ (1 : Mat2), smul_pow, one_pow]]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
  rw [← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul, Matrix.mul_one]

/-! ### The trajectory of the smoothed `(6k+2)`-gon -/

lemma poly_tf_eq (k : ℕ) : tf k = ((3 * k + 1 : ℕ) : ℝ) * switchTime (y₀ k) := by
  rw [tf, tsw_eq_switchTime]; push_cast; ring

/-- The state trajectory of the smoothed `(6k+2)`-gon is unique: any two state trajectories with
the control `polygonControl k` and the initial values `g(0) = I₂`, `X(0) = Φ(i y₀)` agree on
`[0, t_f]` with the spline `(polygonG, polygonX)`. -/
theorem polygon_trajectory_unique (k : ℕ) (hk : 1 ≤ k) (g X : ℝ → Mat2)
    (h : IsStateTrajectory (tf k) (polygonControl k) g X) (hg0 : g 0 = 1) (hX0 : X 0 = Φ 0 (y₀ k)) :
    ∀ t ∈ Set.Icc 0 (tf k), g t = polygonG (y₀ k) (tsw k) t ∧ X t = polygonX (y₀ k) (tsw k) t := by
  rw [poly_tf_eq] at h ⊢
  exact poly_trajectory_unique (y₀ k) (poly_y₀_mem hk).1 (poly_y₀_mem hk).2 _ g X h hg0 hX0

/-- On the first switching interval the control `e₃` maximizes the Hamiltonian of the strong lift
among the vertices, with maximum `0`: `H(e₃) = 0` (`strongLift_perp_hamiltonian`) and
`H(e₃) - H(e_j) = χ_{3j} ≥ 0` (Lemma 7.5.3). -/
lemma poly_strong_hamiltonian_le {y0 : ℝ} (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) {s : ℝ}
    (hs : s ∈ Icc 0 (switchTime y0)) (m : Fin 3) :
    hamiltonian (-1) (strongΛ₁ y0 s) (strongΛR y0 s) (segX y0 s) (vertex m) ≤ 0 := by
  have hH := (strongLift_perp_hamiltonian y0 hy0 hy1 s hs).2
  have hχ := lemma7_5_3 y0 hy0 hy1 _ _ (strongLift_isStrongLift y0 hy0 hy1) s hs
  have h0 := poly_hamiltonian_sub (-1) (strongΛ₁ y0 s) (strongΛR y0 s) (segX y0 s) 2 0
  have h1 := poly_hamiltonian_sub (-1) (strongΛ₁ y0 s) (strongΛR y0 s) (segX y0 s) 2 1
  match m with
  | ⟨0, _⟩ => exact (by linarith [hχ.1] :
      hamiltonian (-1) (strongΛ₁ y0 s) (strongΛR y0 s) (segX y0 s) (vertex 0) ≤ 0)
  | ⟨1, _⟩ => exact (by linarith [hχ.2.1] :
      hamiltonian (-1) (strongΛ₁ y0 s) (strongΛR y0 s) (segX y0 s) (vertex 1) ≤ 0)
  | ⟨2, _⟩ => exact hH.le

/-- The spline of the smoothed `(6k+2)`-gon (any `y₀ ∈ (1/√3, 1)` with
`4/(3y₀² + 1) = 2 cos θ_k`) lifts to a Pontryagin extremal with `λ_cost = -1`: on the `i`-th
switching interval the costates are the conjugates `R⁻ⁱ Λ(t - iτ) Rⁱ` of the strong lift `Λ` of
Theorem 7.5.1. The strong transversality conditions make them continuous at the switching
times, and imply the transversality conditions at `t_f`; `g(t_f) = R` is Lemma 7.5.5; the
maximum principle on each switching interval is Lemma 7.5.3, conjugated. -/
theorem poly_isPontryaginExtremal (k : ℕ) (hk : 1 ≤ k) (y0 : ℝ) (hy0 : 1 / √3 < y0)
    (hy1 : y0 < 1) (hθ : 4 / (3 * y0 ^ 2 + 1) = 2 * Real.cos (θ k)) (g X : ℝ → Mat2)
    (h : IsStateTrajectory ((3 * k + 1) * switchTime y0) (polygonControlAt (switchTime y0)) g X)
    (hg0 : g 0 = 1) (hX0 : X 0 = Φ 0 y0) :
    IsPontryaginExtremal ((3 * k + 1) * switchTime y0) (polygonControlAt (switchTime y0)) g X
      (poly_pw R⁻¹ R (switchTime y0) (strongΛ₁ y0)) (poly_pw R⁻¹ R (switchTime y0) (strongΛR y0))
      (-1) := by
  set τ := switchTime y0 with hτdef
  have hτ : 0 < τ := poly_switchTime_pos hy0 hy1
  have hy : 0 < y0 := poly_y0_pos hy0
  -- `g(t_f) = R` (Lemma 7.5.5)
  have hgT := lemma7_5_5 k hk y0 hy0 hy1 hθ g X h hg0 hX0
  have hT : ((3 * k + 1 : ℝ)) * τ = ((3 * k + 1 : ℕ) : ℝ) * τ := by push_cast; ring
  rw [hT] at h hgT ⊢
  have hN : 1 ≤ 3 * k + 1 := by omega
  have huniq : ∀ t ∈ Icc 0 (((3 * k + 1 : ℕ) : ℝ) * τ),
      g t = polygonG y0 τ t ∧ X t = polygonX y0 τ t :=
    poly_trajectory_unique y0 hy0 hy1 _ g X h hg0 hX0
  have hTpos : 0 ≤ ((3 * k + 1 : ℕ) : ℝ) * τ := by positivity
  -- the strong lift of Theorem 7.5.1 on the first switching interval
  obtain ⟨htr, hd1, hdR, -, -, -, -, hgR, hg1⟩ := strongLift_isStrongLift y0 hy0 hy1
  have hc1 : ContinuousOn (strongΛ₁ y0) (Icc 0 τ) := HasDerivWithinAtEntrywise.continuousOn hd1
  have hcR : ContinuousOn (strongΛR y0) (Icc 0 τ) := HasDerivWithinAtEntrywise.continuousOn hdR
  have hcX : ContinuousOn (segX y0) (Icc 0 τ) := (poly_segX_continuous hy).continuousOn
  have hstar : ∀ s ∈ Icc 0 τ, IsStarState (segX y0 s) := fun s hs ↦ segX_star y0 hy0 hy1 s hs
  have hglX := poly_segX_glue hy0 hy1
  -- the values on the closed switching intervals
  have hpiece : ∀ i : ℕ, ∀ t ∈ Icc ((i : ℝ) * τ) ((i + 1) * τ),
      polygonX y0 τ t = R⁻¹ ^ i * segX y0 (t - i * τ) * R ^ i ∧
      poly_pw R⁻¹ R τ (strongΛ₁ y0) t = R⁻¹ ^ i * strongΛ₁ y0 (t - i * τ) * R ^ i ∧
      poly_pw R⁻¹ R τ (strongΛR y0) t = R⁻¹ ^ i * strongΛR y0 (t - i * τ) * R ^ i :=
    fun i t ht ↦ ⟨poly_pw_of_mem_Icc hτ hglX ht, poly_pw_of_mem_Icc hτ hg1 ht,
      poly_pw_of_mem_Icc hτ hgR ht⟩
  -- the values at `0` and `t_f`
  have hfl : ⌊((3 * k + 1 : ℕ) : ℝ) * τ / τ⌋₊ = 3 * k + 1 := by
    rw [mul_div_cancel_right₀ _ hτ.ne', Nat.floor_natCast]
  have hend : ∀ f0 : ℝ → Mat2,
      poly_pw R⁻¹ R τ f0 (((3 * k + 1 : ℕ) : ℝ) * τ) = R⁻¹ * f0 0 * R := by
    intro f0
    rw [poly_pw, hfl, sub_self, poly_conj_pow_three_mul_add_one]
  have hstart : ∀ f0 : ℝ → Mat2, poly_pw R⁻¹ R τ f0 0 = f0 0 := by
    intro f0
    simp [poly_pw]
  refine ⟨h, hg0, hgT, ?_, ?_, ?_, by norm_num, ?_, ?_, ?_, ?_⟩
  · -- `X(t_f) = R⁻¹ X(0) R`, from the strong boundary condition `eqn:poly-z`
    rw [(huniq _ ⟨hTpos, le_rfl⟩).2, poly_polygonX_eq, hend, hX0,
      (seg_solution y0 0 hy).2.2.2.1]
  · -- `Λ₁(t_f) = R⁻¹ Λ₁(0) R`
    rw [hend, hstart]
  · -- `Λ_R(t_f) = R⁻¹ Λ_R(0) R`
    rw [hend, hstart]
  · -- traceless costates, `Λ_R ⊥ X`, nontriviality
    intro t ht
    obtain ⟨i, -, hti⟩ := poly_exists_piece hτ hN ht
    have hs : t - i * τ ∈ Icc 0 τ := ⟨by linarith [hti.1], by linarith [hti.2]⟩
    obtain ⟨hX, h1, hR⟩ := hpiece i t hti
    rw [(huniq t ht).2, hX, h1, hR, poly_trace_conj (poly_Rpow_mul_Rinvpow i),
      poly_trace_conj (poly_Rpow_mul_Rinvpow i), poly_traceForm_conj (poly_Rpow_mul_Rinvpow i)]
    exact ⟨(htr _ hs).1, (htr _ hs).2, (strongLift_perp_hamiltonian y0 hy0 hy1 _ hs).1,
      Or.inl (by norm_num)⟩
  · -- the costate equation `Λ₁' = [Λ₁, X]`
    have hI := poly_pw_isIntegralCurve (A := R⁻¹) (B := R) hτ hg1 hc1
      (v0 := fun s ↦ strongΛ₁ y0 s * segX y0 s - segX y0 s * strongΛ₁ y0 s)
      ((hc1.mul hcX).sub (hcX.mul hc1))
      (fun s hs ↦ (hd1 s (Ioo_subset_Icc_self hs)).hasDerivAtEntrywise (Icc_mem_nhds hs.1 hs.2))
      (3 * k + 1) (v := fun t ↦ poly_pw R⁻¹ R τ (strongΛ₁ y0) t * polygonX y0 τ t -
        polygonX y0 τ t * poly_pw R⁻¹ R τ (strongΛ₁ y0) t) (fun i _ t ht ↦ ?_)
    · refine poly_isIntegralCurve_congr hI hTpos fun t ht ↦ ?_
      simp only [(huniq t ht).2]
    · obtain ⟨hX, h1, -⟩ := hpiece i t (Ico_subset_Icc_self ht)
      simp only [hX, h1]
      rw [poly_conj_bracket (poly_Rpow_mul_Rinvpow i)]
  · -- the costate equation for `Λ_R`
    have hI := poly_pw_isIntegralCurve (A := R⁻¹) (B := R) hτ hgR hcR
      (v0 := fun s ↦ costateRHS (-1) (strongΛ₁ y0 s) (strongΛR y0 s) (segX y0 s) (vertex 2))
      (poly_costateRHS_continuousOn (-1) (poly_vertex_mem 2) hc1 hcR hcX hstar)
      (fun s hs ↦ (hdR s (Ioo_subset_Icc_self hs)).hasDerivAtEntrywise (Icc_mem_nhds hs.1 hs.2))
      (3 * k + 1) (v := fun t ↦ costateRHS (-1) (poly_pw R⁻¹ R τ (strongΛ₁ y0) t)
        (poly_pw R⁻¹ R τ (strongΛR y0) t) (polygonX y0 τ t) (polygonControlAt τ t))
      (fun i _ t ht ↦ ?_)
    · refine poly_isIntegralCurve_congr hI hTpos fun t ht ↦ ?_
      simp only [costateRHS, (huniq t ht).2]
    · obtain ⟨hX, h1, hR⟩ := hpiece i t (Ico_subset_Icc_self ht)
      simp only [hX, h1, hR, poly_polygonControlAt_eq, poly_floor_eq hτ ht.1 ht.2]
      rw [poly_costateRHS_conj (poly_Rpow_mul_Rinvpow i) (poly_conj_pow_J i)
        (poly_conj_pow_vertex_two i)]
  · -- the maximum principle and `H = 0`, from Lemma 7.5.3 by conjugation
    refine Filter.Eventually.of_forall fun t ht ↦ ?_
    have htI : t ∈ Icc 0 (((3 * k + 1 : ℕ) : ℝ) * τ) := Ioo_subset_Icc_self ht
    obtain ⟨hf1, hf2⟩ := poly_floor_mem hτ ht.1.le
    set i := ⌊t / τ⌋₊ with hi
    have hs : t - i * τ ∈ Icc 0 τ := ⟨by linarith, by linarith⟩
    obtain ⟨hX, h1, hR⟩ := hpiece i t ⟨hf1, hf2.le⟩
    rw [(huniq t htI).2, hX, h1, hR, poly_polygonControlAt_eq, ← hi]
    have hH0 := poly_hamiltonian_conj (poly_Rpow_mul_Rinvpow i) (poly_conj_pow_J i)
      (poly_conj_pow_vertex_two i) (-1) (strongΛ₁ y0 (t - i * τ)) (strongΛR y0 (t - i * τ))
      (segX y0 (t - i * τ))
    rw [(strongLift_perp_hamiltonian y0 hy0 hy1 _ hs).2] at hH0
    refine ⟨hH0, fun v hv ↦ ?_⟩
    rw [hH0]
    refine poly_hamiltonian_le_of_vertices _ _ _ _ (poly_isStarState_conj_pow i (hstar _ hs)) 0
      (fun m ↦ ?_) v hv
    have hm : (⟨((⟨(m.val + 2 * i) % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3).val + i) % 3,
        Nat.mod_lt _ (by norm_num)⟩ : Fin 3) = m := by
      ext
      simp only
      omega
    rw [← hm, poly_hamiltonian_conj (poly_Rpow_mul_Rinvpow i) (poly_conj_pow_J i)
      (poly_conj_pow_vertex i _)]
    exact poly_strong_hamiltonian_le hy0 hy1 hs _

/-- **Theorem 7.5.6** (`thm:6k+2`). For each positive integer `k`, the smoothed `(6k+2)`-gon is a
Pontryagin extremal given by a bang-bang control: the state trajectory with the control
`polygonControl k` and `g(0) = I₂`, `X(0) = Φ(i y₀)` exists, its control is bang-bang, and it lifts
to a Pontryagin extremal.

The book's proof checks the transversality conditions at `t_f` from the strong transversality
conditions of Theorem 7.5.1 and `z(z₀, t_sw) = R⁻¹ · z₀`, relying on Theorem 7.5.1, Lemma 7.5.3 and
Lemma 7.5.5. The formal proof also fills in what the book leaves implicit: the lift on the `i`-th
switching interval is the `R⁻ⁱ`-conjugate of the explicit lift of Theorem 7.5.1
(`strongLift_isStrongLift`), continuous at the switching times by the strong transversality
conditions; `H = 0` and maximality are transported by conjugation from Lemma 7.5.3; and the
maximization over all of `U_T` reduces to the vertices because the Hamiltonian is a convex
combination of its vertex values with weights `u_j ⟨X, Z_{e_j}⟩/⟨X, Z_u⟩ ≥ 0`
(`poly_hamiltonian_le_of_vertices`), the argument of Lemma 7.3.1. -/
theorem theorem7_5_6 (k : ℕ) (hk : 1 ≤ k) :
    (∃ g X : ℝ → Mat2, IsStateTrajectory (tf k) (polygonControl k) g X ∧ g 0 = 1 ∧
      X 0 = Φ 0 (y₀ k)) ∧
    ∀ g X : ℝ → Mat2, IsStateTrajectory (tf k) (polygonControl k) g X → g 0 = 1 →
      X 0 = Φ 0 (y₀ k) →
      IsBangBang (tf k) (polygonControl k) ∧
        ∃ (Λ₁ ΛR : ℝ → Mat2) (lam : ℝ),
          IsPontryaginExtremal (tf k) (polygonControl k) g X Λ₁ ΛR lam := by
  obtain ⟨hy0, hy1⟩ := poly_y₀_mem hk
  refine ⟨?_, fun g X h hg0 hX0 ↦ ⟨fun t _ ↦ poly_vertex_extreme _, _, _, _,
    poly_isPontryaginExtremal k hk (y₀ k) hy0 hy1 (poly_y₀_trace hk) g X h hg0 hX0⟩⟩
  obtain ⟨hst, hg0, hX0⟩ := poly_isStateTrajectory (y₀ k) hy0 hy1 (3 * k + 1) (by omega)
  refine ⟨_, _, ?_, hg0, hX0⟩
  rw [poly_tf_eq]
  exact hst

/-! ### The smoothed octagon -/

/-- `⟨J, Φ(x + iy)⟩ = -(x² + y² + 1)/y`. -/
lemma poly_traceForm_J_Φ (x y : ℝ) (hy : 0 < y) :
    traceForm J (Φ x y) = -((x ^ 2 + y ^ 2 + 1) / y) := by
  simp [traceForm, J, Φ, Matrix.trace_fin_two]
  field_simp
  ring

/-- Along the `e₃`-trajectory from `z₀ = i y₀`, with `W = exp(√3 y₀ t)`,
`⟨J, X⟩ = -((1 + 3y₀²) W - 2 + 4/W)/(3y₀)`. -/
lemma poly_traceForm_J_segX {y0 : ℝ} (hy : 0 < y0) (t : ℝ) :
    traceForm J (segX y0 t) = -((1 + 3 * y0 ^ 2) * Real.exp (√3 * y0 * t) - 2 +
      4 * Real.exp (-(√3 * y0 * t))) / (3 * y0) := by
  have hW := Real.exp_pos (√3 * y0 * t)
  rw [segX_eq y0 t hy, poly_traceForm_J_Φ _ _ (by positivity), Real.exp_neg]
  generalize Real.exp (√3 * y0 * t) = W at hW ⊢
  have h3 : (0 : ℝ) < √3 := by positivity
  field_simp
  rw [poly_sqrt3_sq]
  ring

/-- An antiderivative of `t ↦ ⟨J, X(z₀, t)⟩`. -/
noncomputable def poly_costPrimitive (y0 t : ℝ) : ℝ :=
  -((1 + 3 * y0 ^ 2) * Real.exp (√3 * y0 * t) / (√3 * y0) - 2 * t -
    4 * Real.exp (-(√3 * y0 * t)) / (√3 * y0)) / (3 * y0)

lemma poly_costPrimitive_hasDerivAt {y0 : ℝ} (hy : 0 < y0) (t : ℝ) :
    HasDerivAt (poly_costPrimitive y0) (traceForm J (segX y0 t)) t := by
  rw [poly_traceForm_J_segX hy]
  have h1 : HasDerivAt (fun t ↦ Real.exp (√3 * y0 * t))
      (Real.exp (√3 * y0 * t) * (√3 * y0 * 1)) t :=
    ((hasDerivAt_id' t).const_mul (√3 * y0)).exp
  have h2 : HasDerivAt (fun t ↦ Real.exp (-(√3 * y0 * t)))
      (Real.exp (-(√3 * y0 * t)) * -(√3 * y0 * 1)) t :=
    ((hasDerivAt_id' t).const_mul (√3 * y0)).neg.exp
  have := ((((h1.const_mul (1 + 3 * y0 ^ 2)).div_const (√3 * y0)).sub
    ((hasDerivAt_id' t).const_mul 2)).sub ((h2.const_mul 4).div_const (√3 * y0))).neg.div_const
      (3 * y0)
  unfold poly_costPrimitive
  convert this using 1
  have h3 : (0 : ℝ) < √3 := by positivity
  field_simp
  ring

/-- `∫₀^b ⟨J, X(z₀, t)⟩ dt` by the fundamental theorem of calculus. -/
lemma poly_integral_J_segX {y0 : ℝ} (hy : 0 < y0) (b : ℝ) :
    ∫ t in (0 : ℝ)..b, traceForm J (segX y0 t) =
      poly_costPrimitive y0 b - poly_costPrimitive y0 0 :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ poly_costPrimitive_hasDerivAt hy t)
    ((continuous_const.matrix_mul (poly_segX_continuous hy)).matrix_trace.intervalIntegrable _ _)

/-- The cost is the same on every switching interval: if `X` is the spline on `[0, Nτ]`, then
`∫₀^{Nτ} ⟨J, X⟩ = N ∫₀^τ ⟨J, X(z₀, t)⟩`, because `⟨J, R⁻ⁱ Y Rⁱ⟩ = ⟨J, Y⟩` (`J` commutes with
`R`). -/
lemma poly_integral_J {y0 : ℝ} (hy0 : 1 / √3 < y0) (hy1 : y0 < 1) (N : ℕ) (X : ℝ → Mat2)
    (hXc : ContinuousOn X (Icc 0 (N * switchTime y0)))
    (hX : ∀ t ∈ Icc 0 (N * switchTime y0), X t = polygonX y0 (switchTime y0) t) :
    ∫ t in (0 : ℝ)..N * switchTime y0, traceForm J (X t) =
      N * ∫ t in (0 : ℝ)..switchTime y0, traceForm J (segX y0 t) := by
  set τ := switchTime y0 with hτdef
  have hτ : 0 < τ := poly_switchTime_pos hy0 hy1
  have hJc : ContinuousOn (fun t ↦ traceForm J (X t)) (Icc 0 (N * τ)) :=
    (continuous_const.matrix_mul continuous_id).matrix_trace.comp_continuousOn hXc
  have hsub : ∀ i < N, Icc ((i : ℝ) * τ) (((i + 1 : ℕ) : ℝ) * τ) ⊆ Icc 0 (N * τ) := by
    intro i hi
    have : ((i + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hi
    exact Icc_subset_Icc (by positivity) (by nlinarith)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (f := fun t ↦ traceForm J (X t)) (a := fun i : ℕ ↦ (i : ℝ) * τ) (n := N) fun i hi ↦
      (hJc.mono (hsub i hi)).intervalIntegrable_of_Icc (by push_cast; nlinarith)
  simp only [Nat.cast_zero, zero_mul] at hsum
  rw [← hsum, Finset.sum_congr rfl fun i hi ↦ ?_, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  have hi' := Finset.mem_range.1 hi
  rw [intervalIntegral.integral_congr (g := fun t ↦ traceForm J (segX y0 (t - i * τ))) ?_,
    intervalIntegral.integral_comp_sub_right (fun t ↦ traceForm J (segX y0 t)), sub_self]
  · congr 1
    push_cast
    ring
  · intro t ht
    have hle : (i : ℝ) * τ ≤ ((i + 1 : ℕ) : ℝ) * τ := by push_cast; nlinarith
    rw [uIcc_of_le hle] at ht
    have ht' : t ∈ Icc ((i : ℝ) * τ) ((i + 1) * τ) := by push_cast at ht; exact ht
    simp only
    rw [hX t (hsub i hi' ht), poly_Xp_eq hy0 hy1 hτdef ht', poly_Xp]
    conv_lhs => rw [← poly_conj_pow_J i]
    rw [poly_traceForm_conj (poly_Rpow_mul_Rinvpow i)]

lemma poly_sqrt_two_sq : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

lemma poly_sqrt8 : √8 = 2 * √2 := by
  rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]

lemma poly_sqrt32 : √32 = 4 * √2 := by
  rw [show (32 : ℝ) = 4 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num),
    Real.sqrt_sq (by norm_num)]

lemma poly_sqrt12 : √12 = 2 * √3 := by
  rw [show (12 : ℝ) = 2 ^ 2 * 3 by norm_num, Real.sqrt_mul (by norm_num),
    Real.sqrt_sq (by norm_num)]

lemma poly_θ_one : θ 1 = Real.pi / 4 := by
  unfold θ
  push_cast
  ring

lemma poly_two_div_cos_θ_one : 2 / Real.cos (θ 1) = √8 := by
  have h2 : (0 : ℝ) < √2 := by positivity
  rw [poly_θ_one, Real.cos_pi_div_four, poly_sqrt8]
  field_simp
  rw [poly_sqrt_two_sq]

lemma poly_y₀_one : y₀ 1 = √((√8 - 1) / 3) := by
  rw [y₀, poly_two_div_cos_θ_one]

lemma poly_three_y₀_one_sq : 3 * y₀ 1 ^ 2 = √8 - 1 := by
  rw [poly_y₀_sq le_rfl, poly_two_div_cos_θ_one]
  ring

/-- `W(t_sw) = exp(√3 y₀ t_sw) = 4/(3y₀² + 1)`. -/
lemma poly_exp_switchTime {y0 : ℝ} (hy : 0 < y0) :
    Real.exp (√3 * y0 * switchTime y0) = 4 / (3 * y0 ^ 2 + 1) := by
  have h3 : (0 : ℝ) < √3 := by positivity
  rw [show √3 * y0 * switchTime y0 = Real.log (4 / (3 * y0 ^ 2 + 1)) by
    rw [switchTime]; field_simp, Real.exp_log (by positivity)]

lemma poly_four_div_octagon : 4 / (3 * y₀ 1 ^ 2 + 1) = √2 := by
  have h2 : (0 : ℝ) < √2 := by positivity
  rw [poly_three_y₀_one_sq, sub_add_cancel, poly_sqrt8]
  field_simp
  rw [poly_sqrt_two_sq]
  norm_num

/-- **Example** (the smoothed octagon, before Theorem 7.5.6; label `ex:smoothed-octagon` here).
For `k = 1`: `θ₁ = π/4`, the trace of `R⁻¹ g_sw` is `√2`, `y₀ = √((√8 - 1)/3)`,
`t_sw = ln 2/(2√(√8 - 1))`, and for the trajectory of the smoothed octagon (`t_f = 4 t_sw`)
`area(K_oct) = -6 ∫₀^{t_sw} ⟨J, X⟩ dt = √12 (8 - √32 - ln 2)/(√8 - 1) ≈ 3.126 < π`, so the density
`δ = area(K_oct)/√12` is `(8 - √32 - ln 2)/(√8 - 1)` (`eqn:density-formula`). The area is the
cost `-(3/2) ∫₀^{t_f} ⟨J, X⟩ dt` (`eqn:cost`). -/
theorem example7_5_smoothedOctagon :
    θ 1 = Real.pi / 4 ∧ (R⁻¹ * segG (y₀ 1) (tsw 1)).trace = √2 ∧
      y₀ 1 = √((√8 - 1) / 3) ∧ tsw 1 = Real.log 2 / (2 * √(√8 - 1)) ∧
      ∀ g X : ℝ → Mat2, IsStateTrajectory (tf 1) (polygonControl 1) g X → g 0 = 1 →
        X 0 = Φ 0 (y₀ 1) →
        reinhardtCost (tf 1) X = -6 * ∫ t in (0 : ℝ)..tsw 1, traceForm J (X t) ∧
          reinhardtCost (tf 1) X = √12 * (8 - √32 - Real.log 2) / (√8 - 1) ∧
          reinhardtCost (tf 1) X < Real.pi ∧
          reinhardtCost (tf 1) X / √12 = (8 - √32 - Real.log 2) / (√8 - 1) := by
  obtain ⟨hy0, hy1⟩ := poly_y₀_mem (le_refl 1)
  have hy : 0 < y₀ 1 := poly_y0_pos hy0
  have h2 : (0 : ℝ) < √2 := by positivity
  have h3 : (0 : ℝ) < √3 := by positivity
  have hq := poly_three_y₀_one_sq
  have h8 : √8 - 1 = 2 * √2 - 1 := by rw [poly_sqrt8]
  have h2lo : (1.4142 : ℝ) < √2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2hi : √2 < (1.4143 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h3hi : √3 < (1.7321 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  -- the switching time
  have htsw : tsw 1 = Real.log 2 / (2 * √(√8 - 1)) := by
    rw [tsw, poly_four_div_octagon, Real.log_sqrt (by norm_num), poly_y₀_one, ← Real.sqrt_mul
      (by norm_num), show 3 * ((√8 - 1) / 3) = √8 - 1 by ring]
    ring
  refine ⟨poly_θ_one, ?_, poly_y₀_one, htsw, fun g X h hg0 hX0 ↦ ?_⟩
  · rw [Matrix.trace_mul_comm, tsw_eq_switchTime, trace_segG_switchTime _ hy0 hy1, add_comm,
      poly_four_div_octagon]
  -- the trajectory is the spline; the cost is four times the cost of one switching interval
  have huniq := polygon_trajectory_unique 1 le_rfl g X h hg0 hX0
  have htf : tf 1 = ((4 : ℕ) : ℝ) * switchTime (y₀ 1) := by
    rw [tf, tsw_eq_switchTime]; norm_num
  have hτ : 0 < switchTime (y₀ 1) := poly_switchTime_pos hy0 hy1
  have hXc : ContinuousOn X (Icc 0 (((4 : ℕ) : ℝ) * switchTime (y₀ 1))) := by
    rw [← htf]; exact Matrix.continuousOn_of_eq_add_integral h.2.2.2.2.2
  have hX4 : ∀ t ∈ Icc 0 (((4 : ℕ) : ℝ) * switchTime (y₀ 1)),
      X t = polygonX (y₀ 1) (switchTime (y₀ 1)) t := fun t ht ↦ (huniq t (htf ▸ ht)).2
  have hI4 := poly_integral_J hy0 hy1 4 X hXc hX4
  have hsub1 : Icc 0 (((1 : ℕ) : ℝ) * switchTime (y₀ 1)) ⊆
      Icc 0 (((4 : ℕ) : ℝ) * switchTime (y₀ 1)) :=
    Icc_subset_Icc le_rfl (by push_cast; nlinarith)
  have hI1 := poly_integral_J hy0 hy1 1 X (hXc.mono hsub1) fun t ht ↦ hX4 t (hsub1 ht)
  simp only [Nat.cast_one, one_mul] at hI1
  -- the integral over one switching interval, by the explicit primitive
  have hIseg : ∫ t in (0 : ℝ)..switchTime (y₀ 1), traceForm J (segX (y₀ 1) t) =
      -(8 - 4 * √2 - Real.log 2) / (√3 * (2 * √2 - 1)) := by
    have hc : √3 * y₀ 1 * switchTime (y₀ 1) = Real.log 2 / 2 := by
      rw [← Real.log_sqrt (by norm_num), ← poly_four_div_octagon, ← poly_exp_switchTime hy,
        Real.log_exp]
    have hq' : 3 * y₀ 1 ^ 2 = 2 * √2 - 1 := by rw [hq, h8]
    have hinv : (√2)⁻¹ = √2 / 2 := by
      have := poly_sqrt_two_sq
      field_simp
      linarith
    have e1 : poly_costPrimitive (y₀ 1) (switchTime (y₀ 1)) - poly_costPrimitive (y₀ 1) 0 =
        -((1 + 3 * y₀ 1 ^ 2) * (Real.exp (√3 * y₀ 1 * switchTime (y₀ 1)) - 1) -
          2 * (√3 * y₀ 1 * switchTime (y₀ 1)) -
          4 * (Real.exp (-(√3 * y₀ 1 * switchTime (y₀ 1))) - 1)) / (√3 * (3 * y₀ 1 ^ 2)) := by
      unfold poly_costPrimitive
      simp only [mul_zero, neg_zero, Real.exp_zero]
      field_simp
      ring
    rw [poly_integral_J_segX hy, e1, Real.exp_neg, poly_exp_switchTime hy, poly_four_div_octagon,
      hc, hq', show 1 + (2 * √2 - 1) = 2 * √2 by ring, hinv,
      show 2 * √2 * (√2 - 1) - 2 * (Real.log 2 / 2) - 4 * (√2 / 2 - 1) =
        8 - 4 * √2 - Real.log 2 by linear_combination 2 * poly_sqrt_two_sq]
  have hcost : reinhardtCost (tf 1) X = -6 * ∫ t in (0 : ℝ)..tsw 1, traceForm J (X t) := by
    rw [reinhardtCost, htf, hI4, tsw_eq_switchTime, hI1]
    push_cast
    ring
  have hval : reinhardtCost (tf 1) X = √12 * (8 - √32 - Real.log 2) / (√8 - 1) := by
    rw [hcost, tsw_eq_switchTime, hI1, hIseg, poly_sqrt12, poly_sqrt32, h8]
    field_simp
    rw [show √3 ^ 2 = 3 from poly_sqrt3_sq]
    ring
  refine ⟨hcost, hval, ?_, ?_⟩
  · -- `≈ 3.126 < π`
    rw [hval, poly_sqrt12, poly_sqrt32, h8, div_lt_iff₀ (by linarith)]
    have hl1 := Real.log_two_gt_d9
    have hl2 := Real.log_two_lt_d9
    have hpi := Real.pi_gt_d2
    have hX0' : 0 < 8 - 4 * √2 - Real.log 2 := by linarith
    have hX1 : 8 - 4 * √2 - Real.log 2 < 1.6501 := by linarith
    have e1 : 2 * √3 * (8 - 4 * √2 - Real.log 2) < 2 * 1.7321 * 1.6501 := by
      have := mul_lt_mul'' h3hi hX1 h3.le hX0'.le
      linarith
    have e2 : 3.14 * 1.8284 < Real.pi * (2 * √2 - 1) := by nlinarith
    norm_num at e1 e2
    linarith
  · rw [hval]
    field_simp

end SmoothedPolygons
