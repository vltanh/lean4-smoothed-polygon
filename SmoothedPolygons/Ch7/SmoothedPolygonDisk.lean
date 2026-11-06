module

public import SmoothedPolygons.Ch3.AreaFormula
public import SmoothedPolygons.Ch7.SmoothedPolygon
public import Basic.Analysis.Convex.StarCurveConvex
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The smoothed `(6k+2)`-gon as a balanced disk

The spline of §7.4–§7.5 (`polygonG`, `polygonX`, defined for `t ≥ 0`) gives the multi-curve
`σ_j(t) = g(t) s_j*` of the smoothed `(6k+2)`-gon. Its rotational symmetry
`g(t + t_sw) = (g_sw R⁻¹) g(t) R` and `g(t_f) = R` (Lemma 7.5.5) give `g(t + t_f) = g(t) R`, so
the spline extends to `ℝ` with period `6 t_f` (`smoothedPolygonG`, `smoothedPolygonX`). The region
swept from the origin by `σ₀` over one period is the smoothed `(6k+2)`-gon `K` in circle
representation (`smoothedPolygonDisk`); `(K, σ)` is a balanced pair
(`smoothedPolygonDisk_isBalancedPair`), and by the area formula `eqn:cost` its area is the cost of
the trajectory (`smoothedPolygonDisk_volume`). For `k = 1` this is the area
`√12 (8 - √32 - ln 2)/(√8 - 1)` of the smoothed octagon (`smoothedOctagon_volume`).

The book takes these facts for granted. The proof here:

* the multi-point, star and curvature conditions hold at each time: `det g = 1`, the star
  inequalities `ρᵢ(X) > 0` give the star condition (`oct_star_mulVec`, the converse of
  Corollary 3.1.6), and off the switching times the control is a vertex `u` of `U_T`, so that the
  curvatures `κ_j = det(s_{2j}*, (X + X⁻¹X') s_{2j}*)` are `-2u_j/⟨Z_u, X⟩ ≥ 0`
  (`oct_stateCurvature_eq`; Definition 3.3.2 read backwards);
* `σ₀` is simple on a period (`oct_curve0_injOn`): in the coordinates `oct_hat` in which
  `h = g_sw R⁻¹` (trace `2 cos θ_k`, `h₀₀ = h₁₁`) is the rotation by `-θ_k`, the symmetry
  `σ₀(t + 3t_sw) = -h³ σ₀(t)` is the rotation by `π - 3θ_k = π/(3k+1)`. On `[0, 3t_sw]` the curve
  stays in the half-plane `x > 0` (`oct_curve0_pos`, from the explicit `e₃`-trajectory), so its
  phase increases there by exactly `π/(3k+1)`, hence by `2π` over the period `2(3k+1) · 3t_sw`:
  the winding number is one (`oct_phase_period`), and a curve turning counterclockwise about the
  origin with winding number one is simple (`oct_injOn_of_phase`);
* convexity, compactness, the interior and the boundary of `K` come from
  `PlaneCurve.IsStarCurve` (`Basic.Analysis.Convex.StarCurve`, `StarCurveConvex`).
-/

@[expose] public section

namespace SmoothedPolygons

open MeasureTheory Matrix Set
open scoped Topology

/-! ### The rotational symmetry of the spline -/

section Spline

variable {y0 τ : ℝ}

/-- `g(s + τ) = (g_sw R⁻¹) g(s) R` for the spline (`eqn:gamma-bang-bang`). -/
lemma oct_polygonG_add (hτ : 0 < τ) {s : ℝ} (hs : 0 ≤ s) :
    polygonG y0 τ (s + τ) = segG y0 τ * R⁻¹ * polygonG y0 τ s * R := by
  have hfl : ⌊(s + τ) / τ⌋₊ = ⌊s / τ⌋₊ + 1 := by
    rw [add_div, div_self hτ.ne', Nat.floor_add_one (div_nonneg hs hτ.le)]
  simp only [polygonG, hfl]
  push_cast
  rw [show s + τ - ((⌊s / τ⌋₊ : ℝ) + 1) * τ = s - ⌊s / τ⌋₊ * τ by ring,
    pow_succ' (segG y0 τ * R⁻¹), pow_succ R]
  simp only [Matrix.mul_assoc]

/-- `X(s + τ) = R⁻¹ X(s) R` for the spline. -/
lemma oct_polygonX_add (hτ : 0 < τ) {s : ℝ} (hs : 0 ≤ s) :
    polygonX y0 τ (s + τ) = R⁻¹ * polygonX y0 τ s * R := by
  have hfl : ⌊(s + τ) / τ⌋₊ = ⌊s / τ⌋₊ + 1 := by
    rw [add_div, div_self hτ.ne', Nat.floor_add_one (div_nonneg hs hτ.le)]
  simp only [polygonX, hfl]
  push_cast
  rw [show s + τ - ((⌊s / τ⌋₊ : ℝ) + 1) * τ = s - ⌊s / τ⌋₊ * τ by ring,
    pow_succ' R⁻¹, pow_succ R]
  simp only [Matrix.mul_assoc]

lemma oct_polygonG_add_nat (hτ : 0 < τ) {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    polygonG y0 τ (s + n * τ) = (segG y0 τ * R⁻¹) ^ n * polygonG y0 τ s * R ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show s + ((n + 1 : ℕ) : ℝ) * τ = (s + n * τ) + τ by push_cast; ring,
      oct_polygonG_add hτ (add_nonneg hs (by positivity)), ih,
      pow_succ' (segG y0 τ * R⁻¹), pow_succ R]
    simp only [Matrix.mul_assoc]

lemma oct_polygonX_add_nat (hτ : 0 < τ) {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    polygonX y0 τ (s + n * τ) = R⁻¹ ^ n * polygonX y0 τ s * R ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show s + ((n + 1 : ℕ) : ℝ) * τ = (s + n * τ) + τ by push_cast; ring,
      oct_polygonX_add hτ (add_nonneg hs (by positivity)), ih, pow_succ' R⁻¹, pow_succ R]
    simp only [Matrix.mul_assoc]

end Spline

lemma oct_R_pow_six : R ^ 6 = 1 := by
  rw [show 6 = 3 * 2 by rfl, pow_mul, poly_R_pow_three]; norm_num

lemma oct_Rinv_pow_six : R⁻¹ ^ 6 = 1 := by
  rw [show 6 = 3 * 2 by rfl, pow_mul, poly_Rinv_pow_three]; norm_num

lemma oct_neg_one_pow_mul_self (k : ℕ) : ((-1 : Mat2) ^ k) * (-1) ^ k = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]; norm_num

/-! ### Periodic extension -/

/-- `t` reduced modulo `P` into `[0, P)` (for `P > 0`). -/
noncomputable def oct_red (P t : ℝ) : ℝ := t - ⌊t / P⌋ * P

lemma oct_red_mem {P : ℝ} (hP : 0 < P) (t : ℝ) : oct_red P t ∈ Ico 0 P := by
  have h1 := Int.floor_le (t / P)
  have h2 := Int.lt_floor_add_one (t / P)
  rw [le_div_iff₀ hP] at h1
  rw [div_lt_iff₀ hP] at h2
  simp only [oct_red]
  constructor <;> linarith

lemma oct_red_add {P : ℝ} (hP : 0 < P) (t : ℝ) : oct_red P (t + P) = oct_red P t := by
  simp only [oct_red]
  rw [add_div, div_self hP.ne', Int.floor_add_one]
  push_cast
  ring

/-- A function which is `P`-periodic on `[0, ∞)` agrees there with its periodic extension. -/
lemma oct_ext_eq {α : Type*} {f : ℝ → α} {P : ℝ} (hP : 0 < P)
    (hf : ∀ s, 0 ≤ s → f (s + P) = f s) {s : ℝ} (hs : 0 ≤ s) : f (oct_red P s) = f s := by
  have hn : 0 ≤ ⌊s / P⌋ := Int.floor_nonneg.2 (div_nonneg hs hP.le)
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hn
  have hiter : ∀ m : ℕ, ∀ x, 0 ≤ x → f (x + m * P) = f x := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      intro x hx
      rw [show x + ((m + 1 : ℕ) : ℝ) * P = (x + m * P) + P by push_cast; ring,
        hf _ (add_nonneg hx (by positivity)), ih x hx]
  have hr := oct_red_mem hP s
  simp only [oct_red, hm] at hr ⊢
  push_cast at hr ⊢
  rw [← hiter m (s - m * P) hr.1]
  congr 1
  ring

lemma oct_exists_int_add_pos {P : ℝ} (hP : 0 < P) (t : ℝ) : ∃ n : ℤ, 0 < t + n * P := by
  obtain ⟨n, hn⟩ := exists_int_gt (-t / P)
  refine ⟨n, ?_⟩
  rw [div_lt_iff₀ hP] at hn
  linarith

/-! ### General helpers -/

/-- A continuous curve whose derivative exists and is bounded by `C` off a countable set is
`C`-Lipschitz (fundamental theorem of calculus with countably many exceptional points). -/
lemma oct_lipschitzWith_of_hasDerivAt {f : ℝ → Fin 2 → ℝ} {S : Set ℝ} (hS : S.Countable)
    (hf : Continuous f) {C : NNReal} (hd : ∀ t ∉ S, ∃ v, HasDerivAt f v t ∧ ‖v‖ ≤ C) :
    LipschitzWith C f := by
  have hae : ∀ᵐ t ∂volume, t ∉ S := hS.ae_notMem volume
  have hderiv : ∀ t ∉ S, HasDerivAt f (deriv f t) t ∧ ‖deriv f t‖ ≤ C := by
    intro t ht
    obtain ⟨v, hv, hvC⟩ := hd t ht
    rw [hv.deriv]
    exact ⟨hv, hvC⟩
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  wlog hxy : x ≤ y generalizing x y
  · rw [dist_comm, dist_comm x]; exact this y x (le_of_not_ge hxy)
  have hint : IntervalIntegrable (deriv f) volume x y := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hxy]
    refine Integrable.of_bound (stronglyMeasurable_deriv f).aestronglyMeasurable C ?_
    filter_upwards [ae_restrict_of_ae hae] with t ht
    exact (hderiv t ht).2
  have hftc := integral_eq_of_hasDerivAt_off_countable_of_le f (deriv f) hxy hS hf.continuousOn
    (fun t ht ↦ (hderiv t ht.2).1) hint
  rw [dist_eq_norm, dist_eq_norm, norm_sub_rev, ← hftc, Real.norm_eq_abs, abs_sub_comm]
  refine intervalIntegral.norm_integral_le_of_norm_le_const_ae ?_
  filter_upwards [hae] with t ht _
  exact (hderiv t ht).2

/-- A continuous periodic function is bounded. -/
lemma oct_bound_of_periodic {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {P : ℝ} (hP : 0 < P)
    (hf : Continuous f) (hper : Function.Periodic f P) : ∃ C, ∀ t, ‖f t‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hf.continuousOn (s := Icc 0 P))
  refine ⟨C, fun t ↦ ?_⟩
  obtain ⟨y, hy, hty⟩ := hper.exists_mem_Ico₀ hP t
  rw [hty]
  exact hC y (Ico_subset_Icc_self hy)

lemma oct_sixthRoot_ne_zero (j : ZMod 6) : sixthRoot j ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [sixthRoot, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h0 h1
  have := Real.sin_sq_add_cos_sq (Real.pi * j.val / 3)
  rw [h0, h1] at this
  norm_num at this

/-- An `SL₂(ℝ)` matrix maps the sixth roots of unity to a multi-point. -/
lemma oct_isMultiPoint_mulVec {A : Mat2} (hA : A.det = 1) :
    IsMultiPoint fun j ↦ A *ᵥ sixthRoot j := by
  intro j
  obtain ⟨h1, h2, h3⟩ := algA_isMultiPoint_sixthRoot j
  refine ⟨?_, ?_, ?_⟩
  · simp only [← Matrix.mulVec_add, h1, Matrix.mulVec_zero]
  · simp only [h2, Matrix.mulVec_neg]
  · simp only
    rw [oct_det2_mulVec, hA, one_mul, h3]

/-- The star inequalities `ρᵢ(X) > 0` give the star condition at the sixth roots of unity:
`X s_j* = ρ_{j+1}(X) (s_{j+1}* - s_j*) + ρ_j(X) s_{j+1}*` (indices of `ρ` mod 3), the converse of
the computation in Corollary 3.1.6 (`eqn:rho-star-inequalities`, with
`s_{j+2}* = s_{j+1}* - s_j*`). -/
lemma oct_star_mulVec {X : Mat2} (hX : IsStarState X) (j : ZMod 6) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧
      X *ᵥ sixthRoot j = α • (sixthRoot (j + 1) - sixthRoot j) + β • sixthRoot (j + 1) := by
  obtain ⟨htr, -, h0, h1, h2⟩ := hX
  have hd : X 1 1 = -X 0 0 := by rw [Matrix.trace_fin_two] at htr; linarith
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3' : √3 ≠ 0 := by positivity
  fin_cases j
  · refine ⟨ρ₁ X, ρ₀ X, h1, h0, ?_⟩
    change X *ᵥ sixthRoot 0 = _ • (sixthRoot 1 - sixthRoot 0) + _ • sixthRoot 1
    rw [algA_sixthRoot_zero, algA_sixthRoot_one]
    ext i; fin_cases i
    all_goals simp [ρ₀, ρ₁, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hd]
    all_goals field_simp
    all_goals ring1
  · refine ⟨ρ₂ X, ρ₁ X, h2, h1, ?_⟩
    change X *ᵥ sixthRoot 1 = _ • (sixthRoot 2 - sixthRoot 1) + _ • sixthRoot 2
    rw [algA_sixthRoot_one, algA_sixthRoot_two]
    ext i; fin_cases i
    all_goals simp [ρ₁, ρ₂, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hd]
    all_goals field_simp
    all_goals first | ring1 | (ring_nf; simp only [h3]; ring1)
  · refine ⟨ρ₀ X, ρ₂ X, h0, h2, ?_⟩
    change X *ᵥ sixthRoot 2 = _ • (sixthRoot 3 - sixthRoot 2) + _ • sixthRoot 3
    rw [algA_sixthRoot_two, algA_sixthRoot_three]
    ext i; fin_cases i
    all_goals simp [ρ₀, ρ₂, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hd]
    all_goals field_simp
    all_goals first | ring1 | (ring_nf; simp only [h3]; ring1)
  · refine ⟨ρ₁ X, ρ₀ X, h1, h0, ?_⟩
    change X *ᵥ sixthRoot 3 = _ • (sixthRoot 4 - sixthRoot 3) + _ • sixthRoot 4
    rw [algA_sixthRoot_three, algA_sixthRoot_four]
    ext i; fin_cases i
    all_goals simp [ρ₀, ρ₁, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hd]
    all_goals field_simp
    all_goals ring1
  · refine ⟨ρ₂ X, ρ₁ X, h2, h1, ?_⟩
    change X *ᵥ sixthRoot 4 = _ • (sixthRoot 5 - sixthRoot 4) + _ • sixthRoot 5
    rw [algA_sixthRoot_four, algA_sixthRoot_five]
    ext i; fin_cases i
    all_goals simp [ρ₁, ρ₂, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hd]
    all_goals field_simp
    all_goals first | ring1 | (ring_nf; simp only [h3]; ring1)
  · refine ⟨ρ₀ X, ρ₂ X, h0, h2, ?_⟩
    change X *ᵥ sixthRoot 5 = _ • (sixthRoot 0 - sixthRoot 5) + _ • sixthRoot 0
    rw [algA_sixthRoot_five, algA_sixthRoot_zero]
    ext i; fin_cases i
    all_goals simp [ρ₀, ρ₂, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hd]
    all_goals field_simp
    all_goals (ring_nf; simp only [h3]; ring_nf)

/-- For `X ∈ 𝔰𝔩₂(ℝ)` with `det X = 1` and `P = Z/⟨Z, X⟩` (`Z ∈ 𝔰𝔩₂(ℝ)`), the solution of
`X' = [P, X]` has `X + X⁻¹X' = -2P`: the matrix `X + X⁻¹X'` whose entries give the curvatures
`κ_j` (`eqn:state-dep-curvature`) is a multiple of the control matrix. -/
lemma oct_add_inv_bracket {X Z : Mat2} (hX : X.trace = 0) (hdet : X.det = 1) (hZ : Z.trace = 0)
    (hc : traceForm Z X ≠ 0) :
    X + X⁻¹ * ((traceForm Z X)⁻¹ • Z * X - X * ((traceForm Z X)⁻¹ • Z)) =
      (-2 * (traceForm Z X)⁻¹) • Z := by
  have hd : X 1 1 = -X 0 0 := by rw [Matrix.trace_fin_two] at hX; linarith
  have hdZ : Z 1 1 = -Z 0 0 := by rw [Matrix.trace_fin_two] at hZ; linarith
  rw [Matrix.det_fin_two, hd] at hdet
  have hXX : X * X = -1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hd] <;> linarith
  have hinv : X⁻¹ = -X := Matrix.inv_eq_right_inv (by rw [Matrix.mul_neg, hXX, neg_neg])
  have hXZX : X * Z * X = traceForm Z X • X + Z := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [traceForm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, hd, hdZ]
    · linear_combination Z 0 0 * hdet
    · linear_combination Z 0 1 * hdet
    · linear_combination Z 1 0 * hdet
    · linear_combination (-Z 0 0) * hdet
  set c := traceForm Z X
  rw [hinv, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_sub, Matrix.neg_mul, Matrix.neg_mul,
    Matrix.mul_smul, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hXZX, hXX,
    Matrix.neg_mul, Matrix.one_mul, smul_add, smul_smul, inv_mul_cancel₀ hc, one_smul]
  module

/-- The state-dependent curvatures of a solution of `X' = [P, X]`, `P = Z_u/⟨Z_u, X⟩`, are
proportional to the control variables: `κ_j = -2 u_j/⟨Z_u, X⟩` (`eqn:state-dep-curvature`,
`eqn:def-Z0`, Definition 3.3.2). -/
lemma oct_stateCurvature_eq {X : Mat2} (hX : IsStarState X) (u : Fin 3 → ℝ)
    (hc : traceForm (controlMatrix u) X ≠ 0) (j : Fin 3) :
    stateCurvature X (controlP u X * X - X * controlP u X) j =
      -2 * (traceForm (controlMatrix u) X)⁻¹ * u j := by
  rw [stateCurvature, controlP, oct_add_inv_bracket hX.1 hX.2.1 (controlMatrix_spec u).1 hc,
    Matrix.smul_mulVec, (controlMatrix_spec u).2.1 j]
  simp only [det2, Pi.smul_apply, smul_eq_mul]
  ring

/-- The curvature condition along a solution of `X' = [P, X]` with a vertex control:
`det(Xs_j*, (X² + [P, X]) s_j*) = κ ≥ 0`. -/
lemma oct_det2_curv {X : Mat2} (hX : IsStarState X) (m : Fin 3) (j : ZMod 6) :
    0 ≤ det2 (X *ᵥ sixthRoot j)
      ((X * X + (controlP (vertex m) X * X - X * controlP (vertex m) X)) *ᵥ sixthRoot j) := by
  have hc := poly_traceForm_neg (poly_vertex_mem m) hX
  have hdetX : X.det ≠ 0 := by rw [hX.2.1]; norm_num
  have hmul : X * X + (controlP (vertex m) X * X - X * controlP (vertex m) X) =
      X * (X + X⁻¹ * (controlP (vertex m) X * X - X * controlP (vertex m) X)) := by
    rw [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdetX),
      Matrix.one_mul]
  rw [hmul, ← Matrix.mulVec_mulVec, oct_det2_mulVec, hX.2.1, one_mul]
  -- `s_j* = ±s_{2m'}*`, and `det(s_{2m'}*, (X + X⁻¹X') s_{2m'}*) = κ_{m'} ∝ u_{m'} ≥ 0`
  have hs : ∃ m' : Fin 3, sixthRoot j = sixthRoot (2 * (m'.val : ZMod 6)) ∨
      sixthRoot j = -sixthRoot (2 * (m'.val : ZMod 6)) := by
    have e : ∀ a b : ZMod 6, a + 3 = b → sixthRoot b = -sixthRoot a := fun a b h ↦ by
      rw [← h]; exact (algA_isMultiPoint_sixthRoot a).2.1
    fin_cases j
    · exact ⟨0, Or.inl rfl⟩
    · refine ⟨2, Or.inr ?_⟩
      change sixthRoot 1 = -sixthRoot 4
      rw [e 1 4 rfl, neg_neg]
    · exact ⟨1, Or.inl rfl⟩
    · exact ⟨0, Or.inr (e 0 3 rfl)⟩
    · exact ⟨2, Or.inl rfl⟩
    · exact ⟨1, Or.inr (e 2 5 rfl)⟩
  obtain ⟨m', hm'⟩ := hs
  have hκ := oct_stateCurvature_eq hX (vertex m) hc.ne m'
  rw [stateCurvature, controlP] at hκ
  rw [controlP] at *
  have hκ' : det2 (sixthRoot j) ((X + X⁻¹ * ((traceForm (controlMatrix (vertex m)) X)⁻¹ •
      controlMatrix (vertex m) * X - X * ((traceForm (controlMatrix (vertex m)) X)⁻¹ •
      controlMatrix (vertex m)))) *ᵥ sixthRoot j) =
      -2 * (traceForm (controlMatrix (vertex m)) X)⁻¹ * vertex m m' := by
    rcases hm' with h | h
    · rw [h, hκ]
    · rw [h, Matrix.mulVec_neg, oct_det2_neg, hκ]
  rw [hκ']
  have hv : 0 ≤ vertex m m' := by
    unfold vertex; by_cases h : m' = m
    · subst h; simp
    · simp [h]
  have : 0 < -2 * (traceForm (controlMatrix (vertex m)) X)⁻¹ := by
    have := inv_lt_zero.2 hc
    linarith
  positivity

/-! ### The winding of a plane curve -/

section Phase

variable {z z' : ℝ → ℂ}

/-- The phase `∫₀ᵗ Im(z'/z)` (the continuous determination of the argument) of a curve `z` in
`ℂ \ {0}` with derivative `z'`. -/
noncomputable def oct_phase (z z' : ℝ → ℂ) (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, (z' s / z s).im

/-- The logarithm `∫₀ᵗ Re(z'/z)` of the modulus of `z(t)/z(0)`. -/
noncomputable def oct_logmod (z z' : ℝ → ℂ) (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, (z' s / z s).re

lemma oct_ratio_continuous (hz : ∀ t, HasDerivAt z (z' t) t) (hz' : Continuous z')
    (hz0 : ∀ t, z t ≠ 0) : Continuous fun t ↦ z' t / z t :=
  hz'.div (continuous_iff_continuousAt.2 fun t ↦ (hz t).continuousAt) hz0

lemma oct_phase_hasDerivAt (hz : ∀ t, HasDerivAt z (z' t) t) (hz' : Continuous z')
    (hz0 : ∀ t, z t ≠ 0) (t : ℝ) : HasDerivAt (oct_phase z z') (z' t / z t).im t :=
  ((Complex.continuous_im.comp (oct_ratio_continuous hz hz' hz0)).integral_hasStrictDerivAt
    0 t).hasDerivAt

lemma oct_logmod_hasDerivAt (hz : ∀ t, HasDerivAt z (z' t) t) (hz' : Continuous z')
    (hz0 : ∀ t, z t ≠ 0) (t : ℝ) : HasDerivAt (oct_logmod z z') (z' t / z t).re t :=
  ((Complex.continuous_re.comp (oct_ratio_continuous hz hz' hz0)).integral_hasStrictDerivAt
    0 t).hasDerivAt

/-- `z(t) = z(0) exp(log|z(t)/z(0)| + i φ(t))` with the phase `φ`. -/
lemma oct_eq_exp (hz : ∀ t, HasDerivAt z (z' t) t) (hz' : Continuous z') (hz0 : ∀ t, z t ≠ 0)
    (t : ℝ) :
    z t = z 0 * Complex.exp (oct_logmod z z' t + oct_phase z z' t * Complex.I) := by
  set E : ℝ → ℂ := fun t ↦ (oct_logmod z z' t : ℂ) + (oct_phase z z' t : ℂ) * Complex.I
    with hEdef
  have hE : ∀ t, HasDerivAt E (z' t / z t) t := by
    intro t
    have := (oct_logmod_hasDerivAt hz hz' hz0 t).ofReal_comp.add
      ((oct_phase_hasDerivAt hz hz' hz0 t).ofReal_comp.mul_const Complex.I)
    convert this using 1
    exact (Complex.re_add_im _).symm
  have hw : ∀ t, HasDerivAt (fun t ↦ z t * Complex.exp (-E t)) 0 t := by
    intro t
    have := (hz t).mul (hE t).neg.cexp
    convert this using 1
    field_simp [hz0 t]
    ring
  have hconst := is_const_of_deriv_eq_zero (fun t ↦ (hw t).differentiableAt)
    (fun t ↦ (hw t).deriv) t 0
  have hE0 : E 0 = 0 := by simp [hEdef, oct_logmod, oct_phase]
  simp only [hE0, neg_zero, Complex.exp_zero, mul_one] at hconst
  calc z t = z t * Complex.exp (-E t) * Complex.exp (E t) := by
        rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    _ = z 0 * Complex.exp (E t) := by rw [hconst]

lemma oct_phase_zero : oct_phase z z' 0 = 0 := by simp [oct_phase]

lemma oct_phase_strictMono (hz : ∀ t, HasDerivAt z (z' t) t) (hz' : Continuous z')
    (hz0 : ∀ t, z t ≠ 0) (hpos : ∀ t, 0 < (z' t / z t).im) : StrictMono (oct_phase z z') :=
  strictMono_of_deriv_pos fun t ↦ by
    rw [(oct_phase_hasDerivAt hz hz' hz0 t).deriv]; exact hpos t

/-- Two times with the same point differ in phase by a multiple of `2π`. -/
lemma oct_phase_sub_of_eq (hz : ∀ t, HasDerivAt z (z' t) t) (hz' : Continuous z')
    (hz0 : ∀ t, z t ≠ 0) {a b : ℝ} {w : ℂ} (hab : z b = Complex.exp (w * Complex.I) * z a) :
    ∃ n : ℤ, oct_phase z z' b = oct_phase z z' a + w.re + n * (2 * Real.pi) := by
  rw [oct_eq_exp hz hz' hz0 a, oct_eq_exp hz hz' hz0 b, mul_left_comm, ← Complex.exp_add] at hab
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 (mul_left_cancel₀ (hz0 0) hab)
  refine ⟨n, ?_⟩
  have him := congrArg Complex.im hn
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
    Complex.I_im, Complex.mul_re, Complex.intCast_re, Complex.intCast_im] at him
  simp at him
  linarith

/-- **Injectivity from the winding.** A curve in `ℂ \ {0}` whose phase increases strictly and
by exactly `2π` over `[0, P]` is injective on `[0, P)`. -/
lemma oct_injOn_of_phase (hz : ∀ t, HasDerivAt z (z' t) t) (hz' : Continuous z')
    (hz0 : ∀ t, z t ≠ 0) (hpos : ∀ t, 0 < (z' t / z t).im) {P : ℝ}
    (hP : oct_phase z z' P = 2 * Real.pi) : InjOn z (Ico 0 P) := by
  have hmono := oct_phase_strictMono hz hz' hz0 hpos
  intro a ha b hb hab
  by_contra hne
  wlog hlt : a < b generalizing a b
  · exact this hb ha hab.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hne))
  obtain ⟨n, hn⟩ := oct_phase_sub_of_eq hz hz' hz0 (a := a) (b := b) (w := 0)
    (by rw [hab, zero_mul, Complex.exp_zero, one_mul])
  simp only [Complex.zero_re, add_zero] at hn
  have h1 := hmono hlt
  have h2 := hmono hb.2
  have h3 := hmono.monotone ha.1
  rw [oct_phase_zero] at h3
  have hpi := Real.pi_pos
  have hn1 : (1 : ℝ) ≤ n := by
    have : (0 : ℝ) < n := by nlinarith
    exact_mod_cast (show 1 ≤ n by exact_mod_cast this)
  nlinarith

end Phase

/-- On a period, the periodic reduction does not change the value. -/
lemma oct_periodic_red {α : Type*} {f : ℝ → α} {P : ℝ} (hper : Function.Periodic f P) (x : ℝ) :
    f (oct_red P x) = f x := by
  simp only [oct_red]
  exact hper.sub_int_mul_eq _

/-- A `P`-periodic function injective on `[0, P)` is injective on every window `[c, c + P)`. -/
lemma oct_injOn_shift {α : Type*} {f : ℝ → α} {P : ℝ} (hP : 0 < P)
    (hper : Function.Periodic f P) (hinj : InjOn f (Ico 0 P)) (c : ℝ) :
    InjOn (fun t ↦ f (t + c)) (Ico 0 P) := by
  intro a ha b hb hab
  have h := hinj (oct_red_mem hP (a + c)) (oct_red_mem hP (b + c))
    (by rw [oct_periodic_red hper, oct_periodic_red hper]; exact hab)
  simp only [oct_red] at h
  set m := ⌊(a + c) / P⌋ - ⌊(b + c) / P⌋ with hm
  have hab' : a - b = m * P := by rw [hm]; push_cast; linarith
  have h1 : (m : ℝ) < 1 := by
    by_contra h'
    have := mul_le_mul_of_nonneg_right (not_lt.1 h') hP.le
    linarith [ha.2, hb.1]
  have h2 : (-1 : ℝ) < m := by
    by_contra h'
    have := mul_le_mul_of_nonneg_right (not_lt.1 h') hP.le
    linarith [ha.1, hb.2]
  have hm0 : m = 0 := by
    have : m < 1 := by exact_mod_cast h1
    have : -1 < m := by exact_mod_cast h2
    omega
  rw [hm0, Int.cast_zero, zero_mul] at hab'
  linarith

/-- A `P`-periodic function takes all its values on `[0, P)`. -/
lemma oct_image_Ico {α : Type*} {f : ℝ → α} {P : ℝ} (hP : 0 < P)
    (hper : Function.Periodic f P) : f '' Ico 0 P = range f := by
  refine (image_subset_range _ _).antisymm ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨oct_red P x, oct_red_mem hP x, oct_periodic_red hper x⟩

/-- In a multi-point with the star condition, `det(σ_j, σ_j') = (α + β) √3/2 > 0`. -/
lemma oct_det2_pos_of_star {a b d : Fin 2 → ℝ} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hd : d = α • (b - a) + β • b) (hab : det2 a b = √3 / 2) : 0 < det2 a d := by
  have e : det2 a d = (α + β) * (√3 / 2) := by
    rw [hd, ← hab]
    simp only [det2, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  rw [e]
  positivity

/-- The trajectory `g` of the smoothed `(6k+2)`-gon, extended to `ℝ` with period `6 t_f`. -/
noncomputable def smoothedPolygonG (k : ℕ) (t : ℝ) : Mat2 :=
  polygonG (y₀ k) (tsw k) (oct_red (6 * tf k) t)

/-- The trajectory `X` of the smoothed `(6k+2)`-gon, extended to `ℝ` with period `6 t_f`. -/
noncomputable def smoothedPolygonX (k : ℕ) (t : ℝ) : Mat2 :=
  polygonX (y₀ k) (tsw k) (oct_red (6 * tf k) t)

/-- The multi-curve `σ_j(t) = g(t) s_j*` of the smoothed `(6k+2)`-gon. -/
noncomputable def smoothedPolygonCurve (k : ℕ) (j : ZMod 6) (t : ℝ) : Fin 2 → ℝ :=
  smoothedPolygonG k t *ᵥ sixthRoot j

/-- The smoothed `(6k+2)`-gon in circle representation: the region swept from the origin by the
curve `σ₀` over one period `[0, 6 t_f]`. -/
noncomputable def smoothedPolygonDisk (k : ℕ) : Set (Fin 2 → ℝ) :=
  PlaneCurve.radialHull (smoothedPolygonCurve k 0) 0 (6 * tf k)

section Disk

variable {k : ℕ}

lemma oct_tsw_pos (hk : 1 ≤ k) : 0 < tsw k :=
  poly_switchTime_pos (poly_y₀_mem hk).1 (poly_y₀_mem hk).2

lemma oct_tf_pos (hk : 1 ≤ k) : 0 < tf k := by
  have := oct_tsw_pos hk
  unfold tf
  positivity

lemma oct_P_pos (hk : 1 ≤ k) : 0 < 6 * tf k := by
  have := oct_tf_pos hk
  positivity

lemma oct_tf_eq (k : ℕ) : tf k = ((3 * k + 1 : ℕ) : ℝ) * tsw k := by
  rw [tf]; push_cast; ring

lemma oct_P_eq (k : ℕ) : 6 * tf k = ((6 * (3 * k + 1) : ℕ) : ℝ) * tsw k := by
  rw [tf]; push_cast; ring

/-- `(g_sw R⁻¹)^{3k+1} = (-1)^k`, from `g(t_f) = R` (Lemma 7.5.5). -/
lemma oct_h_pow (hk : 1 ≤ k) : (segG (y₀ k) (tsw k) * R⁻¹) ^ (3 * k + 1) = (-1) ^ k := by
  obtain ⟨hy0, hy1⟩ := poly_y₀_mem hk
  have hτ := oct_tsw_pos hk
  obtain ⟨hst, hg0, hX0⟩ := poly_isStateTrajectory (y₀ k) hy0 hy1 (3 * k + 1) (by omega)
  rw [← tsw_eq_switchTime] at hst hg0 hX0
  have hcast : ((3 * k + 1 : ℕ) : ℝ) = 3 * k + 1 := by push_cast; ring
  rw [hcast] at hst
  have h55 : polygonG (y₀ k) (tsw k) ((3 * k + 1) * tsw k) = R :=
    lemma7_5_5 k hk (y₀ k) hy0 hy1 (poly_y₀_trace hk) _ _ hst hg0 hX0
  have h2 := oct_polygonG_add_nat (y0 := y₀ k) hτ le_rfl (3 * k + 1)
  rw [zero_add, hcast, h55, hg0, Matrix.mul_one] at h2
  have hRN : R ^ (3 * k + 1) = (-1) ^ k * R := by rw [pow_succ, pow_mul, poly_R_pow_three]
  rw [hRN] at h2
  set A := (segG (y₀ k) (tsw k) * R⁻¹) ^ (3 * k + 1)
  have h3 : A * (-1) ^ k = 1 := by
    have := congrArg (· * R⁻¹) h2
    simp only [Matrix.mul_assoc, poly_R_mul_inv, Matrix.mul_one] at this
    exact this.symm
  calc A = A * ((-1) ^ k * (-1) ^ k) := by rw [oct_neg_one_pow_mul_self, Matrix.mul_one]
    _ = (A * (-1) ^ k) * (-1) ^ k := by rw [Matrix.mul_assoc]
    _ = (-1) ^ k := by rw [h3, Matrix.one_mul]

/-- `g(s + t_f) = g(s) R` for the spline, `s ≥ 0`. -/
lemma oct_polygonG_add_tf (hk : 1 ≤ k) {s : ℝ} (hs : 0 ≤ s) :
    polygonG (y₀ k) (tsw k) (s + tf k) = polygonG (y₀ k) (tsw k) s * R := by
  rw [oct_tf_eq, oct_polygonG_add_nat (oct_tsw_pos hk) hs, oct_h_pow hk,
    show R ^ (3 * k + 1) = (-1) ^ k * R by rw [pow_succ, pow_mul, poly_R_pow_three],
    ((Commute.neg_one_left _).pow_left k).eq, Matrix.mul_assoc, ← Matrix.mul_assoc ((-1) ^ k),
    oct_neg_one_pow_mul_self, Matrix.one_mul]

lemma oct_polygonG_add_P (hk : 1 ≤ k) {s : ℝ} (hs : 0 ≤ s) :
    polygonG (y₀ k) (tsw k) (s + 6 * tf k) = polygonG (y₀ k) (tsw k) s := by
  have htf := oct_tf_pos hk
  have key : ∀ n : ℕ, polygonG (y₀ k) (tsw k) (s + n * tf k) =
      polygonG (y₀ k) (tsw k) s * R ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show s + ((n + 1 : ℕ) : ℝ) * tf k = (s + n * tf k) + tf k by push_cast; ring,
        oct_polygonG_add_tf hk (add_nonneg hs (by positivity)), ih, pow_succ, Matrix.mul_assoc]
  have := key 6
  rw [oct_R_pow_six, Matrix.mul_one] at this
  rw [← this]
  norm_num

lemma oct_polygonX_add_P (hk : 1 ≤ k) {s : ℝ} (hs : 0 ≤ s) :
    polygonX (y₀ k) (tsw k) (s + 6 * tf k) = polygonX (y₀ k) (tsw k) s := by
  rw [oct_P_eq, oct_polygonX_add_nat (oct_tsw_pos hk) hs, pow_mul, pow_mul, oct_R_pow_six,
    oct_Rinv_pow_six, one_pow, Matrix.one_mul, Matrix.mul_one]

lemma oct_G_of_nonneg (hk : 1 ≤ k) {s : ℝ} (hs : 0 ≤ s) :
    smoothedPolygonG k s = polygonG (y₀ k) (tsw k) s :=
  oct_ext_eq (oct_P_pos hk) (fun _ hs ↦ oct_polygonG_add_P hk hs) hs

lemma oct_X_of_nonneg (hk : 1 ≤ k) {s : ℝ} (hs : 0 ≤ s) :
    smoothedPolygonX k s = polygonX (y₀ k) (tsw k) s :=
  oct_ext_eq (oct_P_pos hk) (fun _ hs ↦ oct_polygonX_add_P hk hs) hs

lemma oct_G_periodic (hk : 1 ≤ k) : Function.Periodic (smoothedPolygonG k) (6 * tf k) :=
  fun t ↦ by simp only [smoothedPolygonG, oct_red_add (oct_P_pos hk)]

lemma oct_X_periodic (hk : 1 ≤ k) : Function.Periodic (smoothedPolygonX k) (6 * tf k) :=
  fun t ↦ by simp only [smoothedPolygonX, oct_red_add (oct_P_pos hk)]

/-- `g(t + t_f) = g(t) R` for the extended trajectory. -/
lemma oct_G_add_tf (hk : 1 ≤ k) (t : ℝ) :
    smoothedPolygonG k (t + tf k) = smoothedPolygonG k t * R := by
  obtain ⟨n, hn⟩ := oct_exists_int_add_pos (oct_P_pos hk) t
  have hper := (oct_G_periodic hk).int_mul n
  rw [← hper t, ← hper (t + tf k), show t + tf k + n * (6 * tf k) = (t + n * (6 * tf k)) + tf k
    by ring, oct_G_of_nonneg hk (by linarith [oct_tf_pos hk]), oct_G_of_nonneg hk hn.le,
    oct_polygonG_add_tf hk hn.le]

/-- `g(t + t_sw) = (g_sw R⁻¹) g(t) R` for the extended trajectory. -/
lemma oct_G_add_tsw (hk : 1 ≤ k) (t : ℝ) :
    smoothedPolygonG k (t + tsw k) = segG (y₀ k) (tsw k) * R⁻¹ * smoothedPolygonG k t * R := by
  obtain ⟨n, hn⟩ := oct_exists_int_add_pos (oct_P_pos hk) t
  have hper := (oct_G_periodic hk).int_mul n
  rw [← hper t, ← hper (t + tsw k), show t + tsw k + n * (6 * tf k) =
    (t + n * (6 * tf k)) + tsw k by ring, oct_G_of_nonneg hk (by linarith [oct_tsw_pos hk]),
    oct_G_of_nonneg hk hn.le, oct_polygonG_add (oct_tsw_pos hk) hn.le]

/-! ### The extended trajectory: state, continuity, derivatives -/

/-- The spline is a state trajectory on `[0, Mτ]` for every `M ≥ 1`. -/
lemma oct_polygon_traj (hk : 1 ≤ k) (M : ℕ) (hM : 1 ≤ M) :
    IsStateTrajectory (M * tsw k) (polygonControlAt (tsw k)) (polygonG (y₀ k) (tsw k))
      (polygonX (y₀ k) (tsw k)) ∧
    polygonG (y₀ k) (tsw k) 0 = 1 ∧ polygonX (y₀ k) (tsw k) 0 = Φ 0 (y₀ k) :=
  poly_isStateTrajectory (y₀ k) (poly_y₀_mem hk).1 (poly_y₀_mem hk).2 M hM

lemma oct_exists_nat_gt (hk : 1 ≤ k) (s : ℝ) : ∃ M : ℕ, 1 ≤ M ∧ s < M * tsw k := by
  obtain ⟨M, hM⟩ := exists_nat_gt (s / tsw k)
  refine ⟨M + 1, by omega, ?_⟩
  rw [div_lt_iff₀ (oct_tsw_pos hk)] at hM
  push_cast
  nlinarith [oct_tsw_pos hk]

/-- At `s > 0` the spline is continuous and `g' = gX`. -/
lemma oct_polygon_at (hk : 1 ≤ k) {s : ℝ} (hs : 0 < s) :
    ContinuousAt (polygonG (y₀ k) (tsw k)) s ∧ ContinuousAt (polygonX (y₀ k) (tsw k)) s ∧
      HasDerivAtEntrywise (polygonG (y₀ k) (tsw k))
        (polygonG (y₀ k) (tsw k) s * polygonX (y₀ k) (tsw k) s) s := by
  obtain ⟨M, hM, hsM⟩ := oct_exists_nat_gt hk s
  obtain ⟨⟨-, -, -, -, hgI, hXI⟩, -, -⟩ := oct_polygon_traj hk M hM
  have hnhds : Icc 0 (M * tsw k) ∈ 𝓝 s := Icc_mem_nhds hs hsM
  have hgc := (Matrix.continuousOn_of_eq_add_integral hgI).continuousAt hnhds
  have hXc := (Matrix.continuousOn_of_eq_add_integral hXI).continuousAt hnhds
  exact ⟨hgc, hXc, Matrix.hasDerivAtEntrywise_of_eq_add_integral hgI ⟨hs, hsM⟩ (hgc.mul hXc)⟩

lemma oct_G_eventuallyEq (hk : 1 ≤ k) {s : ℝ} (hs : 0 < s) :
    smoothedPolygonG k =ᶠ[𝓝 s] polygonG (y₀ k) (tsw k) :=
  Filter.eventually_of_mem (Ioi_mem_nhds hs) fun _ hx ↦ oct_G_of_nonneg hk (le_of_lt hx)

lemma oct_X_eventuallyEq (hk : 1 ≤ k) {s : ℝ} (hs : 0 < s) :
    smoothedPolygonX k =ᶠ[𝓝 s] polygonX (y₀ k) (tsw k) :=
  Filter.eventually_of_mem (Ioi_mem_nhds hs) fun _ hx ↦ oct_X_of_nonneg hk (le_of_lt hx)

lemma oct_G_continuous (hk : 1 ≤ k) : Continuous (smoothedPolygonG k) := by
  refine continuous_iff_continuousAt.2 fun t ↦ ?_
  obtain ⟨n, hn⟩ := oct_exists_int_add_pos (oct_P_pos hk) t
  have hper := (oct_G_periodic hk).int_mul n
  have h1 : ContinuousAt (smoothedPolygonG k) (t + n * (6 * tf k)) :=
    (oct_polygon_at hk hn).1.congr (oct_G_eventuallyEq hk hn).symm
  have h2 : ContinuousAt (fun x ↦ smoothedPolygonG k (x + n * (6 * tf k))) t :=
    ContinuousAt.comp (g := smoothedPolygonG k) (f := fun x ↦ x + n * (6 * tf k)) h1
      (by fun_prop)
  rwa [show (fun x ↦ smoothedPolygonG k (x + n * (6 * tf k))) = smoothedPolygonG k from
    funext hper] at h2

lemma oct_X_continuous (hk : 1 ≤ k) : Continuous (smoothedPolygonX k) := by
  refine continuous_iff_continuousAt.2 fun t ↦ ?_
  obtain ⟨n, hn⟩ := oct_exists_int_add_pos (oct_P_pos hk) t
  have hper := (oct_X_periodic hk).int_mul n
  have h1 : ContinuousAt (smoothedPolygonX k) (t + n * (6 * tf k)) :=
    (oct_polygon_at hk hn).2.1.congr (oct_X_eventuallyEq hk hn).symm
  have h2 : ContinuousAt (fun x ↦ smoothedPolygonX k (x + n * (6 * tf k))) t :=
    ContinuousAt.comp (g := smoothedPolygonX k) (f := fun x ↦ x + n * (6 * tf k)) h1
      (by fun_prop)
  rwa [show (fun x ↦ smoothedPolygonX k (x + n * (6 * tf k))) = smoothedPolygonX k from
    funext hper] at h2

/-- `g' = gX` for the extended trajectory, at every time. -/
lemma oct_G_hasDerivAt (hk : 1 ≤ k) (t : ℝ) :
    HasDerivAtEntrywise (smoothedPolygonG k) (smoothedPolygonG k t * smoothedPolygonX k t) t := by
  obtain ⟨n, hn⟩ := oct_exists_int_add_pos (oct_P_pos hk) t
  have hperG := (oct_G_periodic hk).int_mul n
  have hperX := (oct_X_periodic hk).int_mul n
  have h1 : HasDerivAtEntrywise (smoothedPolygonG k)
      (smoothedPolygonG k (t + n * (6 * tf k)) * smoothedPolygonX k (t + n * (6 * tf k)))
      (t + n * (6 * tf k)) := by
    rw [oct_G_of_nonneg hk hn.le, oct_X_of_nonneg hk hn.le]
    exact (oct_polygon_at hk hn).2.2.congr_of_eventuallyEq (oct_G_eventuallyEq hk hn)
  have h2 := HasDerivAtEntrywise.scomp (h := fun x ↦ x + n * (6 * tf k)) h1
    ((hasDerivAt_id' t).add_const _)
  rw [one_smul, hperG, hperX, show (fun x ↦ smoothedPolygonG k (x + n * (6 * tf k))) =
    smoothedPolygonG k from funext hperG] at h2
  exact h2

/-- The extended trajectory stays in `SL₂(ℝ)` and in the star domain. -/
lemma oct_det_star (hk : 1 ≤ k) (t : ℝ) :
    (smoothedPolygonG k t).det = 1 ∧ IsStarState (smoothedPolygonX k t) := by
  obtain ⟨⟨-, -, -, hst, -⟩, -, -⟩ := oct_polygon_traj hk (6 * (3 * k + 1)) (by omega)
  have hr : oct_red (6 * tf k) t ∈ Icc 0 (((6 * (3 * k + 1) : ℕ) : ℝ) * tsw k) := by
    rw [← oct_P_eq]; exact Ico_subset_Icc_self (oct_red_mem (oct_P_pos hk) t)
  exact hst _ hr

lemma oct_G_zero (hk : 1 ≤ k) : smoothedPolygonG k 0 = 1 := by
  rw [oct_G_of_nonneg hk le_rfl]; exact (oct_polygon_traj hk 1 le_rfl).2.1

lemma oct_X_zero (hk : 1 ≤ k) : smoothedPolygonX k 0 = Φ 0 (y₀ k) := by
  rw [oct_X_of_nonneg hk le_rfl]; exact (oct_polygon_traj hk 1 le_rfl).2.2

/-- The switching times `mτ`, `m ∈ ℤ`, of the extended trajectory. -/
def oct_knots (τ : ℝ) : Set ℝ := range fun m : ℤ ↦ (m : ℝ) * τ

lemma oct_knots_countable (τ : ℝ) : (oct_knots τ).Countable := countable_range _

/-- Off the switching times, `X' = [P, X]` with `P = Z_u/⟨Z_u, X⟩` for a vertex `u` of `U_T`. -/
lemma oct_X_hasDerivAt (hk : 1 ≤ k) {t : ℝ} (ht : t ∉ oct_knots (tsw k)) :
    ∃ m : Fin 3, HasDerivAtEntrywise (smoothedPolygonX k)
      (controlP (vertex m) (smoothedPolygonX k t) * smoothedPolygonX k t -
        smoothedPolygonX k t * controlP (vertex m) (smoothedPolygonX k t)) t := by
  obtain ⟨hy0, hy1⟩ := poly_y₀_mem hk
  have hτ := oct_tsw_pos hk
  obtain ⟨n, hn⟩ := oct_exists_int_add_pos (oct_P_pos hk) t
  set s := t + n * (6 * tf k) with hsdef
  have hperX := (oct_X_periodic hk).int_mul n
  -- `s` is not a switching time either
  have hsS : s ∉ oct_knots (tsw k) := by
    rintro ⟨m, hm⟩
    refine ht ⟨m - n * (6 * (3 * k + 1) : ℕ), ?_⟩
    rw [oct_P_eq] at hsdef
    push_cast at hm hsdef ⊢
    linarith
  obtain ⟨h1, h2⟩ := poly_floor_mem hτ hn.le
  set i := ⌊s / tsw k⌋₊
  have h1' : (i : ℝ) * tsw k < s := lt_of_le_of_ne h1 fun h ↦ hsS ⟨i, by push_cast; exact h⟩
  have hloc : smoothedPolygonX k =ᶠ[𝓝 s] poly_Xp (y₀ k) (tsw k) i := by
    filter_upwards [Ioo_mem_nhds h1' h2] with x hx
    rw [oct_X_of_nonneg hk (by nlinarith [hx.1, hτ]),
      poly_Xp_eq (τ := tsw k) hy0 hy1 rfl ⟨hx.1.le, hx.2.le⟩]
  have hd := (poly_Xp_hasDerivAt (poly_y0_pos hy0) (tsw k) i s).congr_of_eventuallyEq hloc
  rw [← hloc.eq_of_nhds] at hd
  refine ⟨poly_idx i, ?_⟩
  have h3 := HasDerivAtEntrywise.scomp (h := fun x ↦ x + n * (6 * tf k)) hd
    ((hasDerivAt_id' t).add_const _)
  rw [one_smul, hperX, show (fun x ↦ smoothedPolygonX k (x + n * (6 * tf k))) =
    smoothedPolygonX k from funext hperX] at h3
  exact h3

/-! ### The multi-curve `σ_j(t) = g(t) s_j*` -/

lemma oct_curve_hasDerivAt (hk : 1 ≤ k) (j : ZMod 6) (t : ℝ) :
    HasDerivAt (smoothedPolygonCurve k j)
      ((smoothedPolygonG k t * smoothedPolygonX k t) *ᵥ sixthRoot j) t :=
  (oct_G_hasDerivAt hk t).mulVec_const _

lemma oct_curve_deriv (hk : 1 ≤ k) (j : ZMod 6) :
    deriv (smoothedPolygonCurve k j) =
      fun t ↦ (smoothedPolygonG k t * smoothedPolygonX k t) *ᵥ sixthRoot j :=
  funext fun t ↦ (oct_curve_hasDerivAt hk j t).deriv

lemma oct_GX_continuous (hk : 1 ≤ k) :
    Continuous fun t ↦ smoothedPolygonG k t * smoothedPolygonX k t :=
  (oct_G_continuous hk).matrix_mul (oct_X_continuous hk)

lemma oct_curve_contDiff (hk : 1 ≤ k) (j : ZMod 6) : ContDiff ℝ 1 (smoothedPolygonCurve k j) := by
  refine contDiff_one_iff_deriv.2 ⟨fun t ↦ (oct_curve_hasDerivAt hk j t).differentiableAt, ?_⟩
  rw [oct_curve_deriv hk j]
  exact (oct_GX_continuous hk).matrix_mulVec continuous_const

lemma oct_curve_deriv_ne_zero (hk : 1 ≤ k) (j : ZMod 6) (t : ℝ) :
    deriv (smoothedPolygonCurve k j) t ≠ 0 := by
  rw [oct_curve_deriv hk j]
  intro h
  have hdet : (smoothedPolygonG k t * smoothedPolygonX k t).det ≠ 0 := by
    rw [Matrix.det_mul, (oct_det_star hk t).1, (oct_det_star hk t).2.2.1]; norm_num
  exact oct_sixthRoot_ne_zero j (Matrix.eq_zero_of_mulVec_eq_zero hdet h)

lemma oct_curve_isMultiPoint (hk : 1 ≤ k) (t : ℝ) :
    IsMultiPoint fun j ↦ smoothedPolygonCurve k j t :=
  oct_isMultiPoint_mulVec (oct_det_star hk t).1

/-- The star condition: `σ_j' = α (σ_{j+1} - σ_j) + β σ_{j+1}` with `α, β > 0`, from the star
inequalities `ρᵢ(X) > 0` of the state. -/
lemma oct_curve_star (hk : 1 ≤ k) (j : ZMod 6) (t : ℝ) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ deriv (smoothedPolygonCurve k j) t =
      α • (smoothedPolygonCurve k (j + 1) t - smoothedPolygonCurve k j t) +
        β • smoothedPolygonCurve k (j + 1) t := by
  obtain ⟨α, β, hα, hβ, h⟩ := oct_star_mulVec (oct_det_star hk t).2 j
  refine ⟨α, β, hα, hβ, ?_⟩
  rw [oct_curve_deriv hk j]
  simp only [smoothedPolygonCurve]
  rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    Matrix.mulVec_sub]

lemma oct_curve_periodic (hk : 1 ≤ k) (j : ZMod 6) (t : ℝ) :
    smoothedPolygonCurve k j (t + 6 * tf k) = smoothedPolygonCurve k j t := by
  simp only [smoothedPolygonCurve, oct_G_periodic hk t]

/-- `σ_j(t + t_f) = σ_{j+1}(t)`: the arcs follow one another along the boundary. -/
lemma oct_curve_add_tf (hk : 1 ≤ k) (j : ZMod 6) (t : ℝ) :
    smoothedPolygonCurve k j (t + tf k) = smoothedPolygonCurve k (j + 1) t := by
  simp only [smoothedPolygonCurve]
  rw [oct_G_add_tf hk, ← Matrix.mulVec_mulVec, oct_R_mulVec_sixthRoot]

lemma oct_curve_add_nat_tf (hk : 1 ≤ k) (n : ℕ) (t : ℝ) :
    smoothedPolygonCurve k 0 (t + n * tf k) = smoothedPolygonCurve k (n : ZMod 6) t := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
    rw [show t + ((n + 1 : ℕ) : ℝ) * tf k = (t + tf k) + n * tf k by push_cast; ring, ih,
      oct_curve_add_tf hk]
    push_cast
    ring_nf

/-- The second derivative off the switching times. -/
lemma oct_curve_deriv2 (hk : 1 ≤ k) (j : ZMod 6) {t : ℝ} (ht : t ∉ oct_knots (tsw k)) :
    ∃ m : Fin 3, HasDerivAt (deriv (smoothedPolygonCurve k j))
      ((smoothedPolygonG k t * (smoothedPolygonX k t * smoothedPolygonX k t +
        (controlP (vertex m) (smoothedPolygonX k t) * smoothedPolygonX k t -
          smoothedPolygonX k t * controlP (vertex m) (smoothedPolygonX k t)))) *ᵥ
        sixthRoot j) t := by
  obtain ⟨m, hm⟩ := oct_X_hasDerivAt hk ht
  refine ⟨m, ?_⟩
  rw [oct_curve_deriv hk j]
  have := ((oct_G_hasDerivAt hk t).mul hm).mulVec_const (sixthRoot j)
  convert this using 2
  simp only [Matrix.mul_add, Matrix.mul_assoc]

/-- The curvature condition `det(σ_j', σ_j'') ≥ 0` almost everywhere: off the switching times the
control is a vertex `u` of `U_T`, and the curvatures are proportional to `u_j ≥ 0`. -/
lemma oct_curve_curvature (hk : 1 ≤ k) (j : ZMod 6) :
    ∀ᵐ t, 0 ≤ det2 (deriv (smoothedPolygonCurve k j) t)
      (deriv (deriv (smoothedPolygonCurve k j)) t) := by
  filter_upwards [(oct_knots_countable (tsw k)).ae_notMem volume] with t ht
  obtain ⟨m, hm⟩ := oct_curve_deriv2 hk j ht
  rw [hm.deriv, oct_curve_deriv hk j]
  simp only
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, oct_det2_mulVec, (oct_det_star hk t).1,
    one_mul]
  exact oct_det2_curv (oct_det_star hk t).2 m j

/-- `σ_j'` is Lipschitz: off the switching times its derivative is a continuous periodic
function of `t` (for each of the three vertex controls), hence bounded. -/
lemma oct_curve_lipschitz (hk : 1 ≤ k) (j : ZMod 6) :
    ∃ C, LipschitzWith C (deriv (smoothedPolygonCurve k j)) := by
  set G := smoothedPolygonG k
  set X := smoothedPolygonX k
  have hP := oct_P_pos hk
  have hbound : ∀ m : Fin 3, ∃ C, ∀ t, ‖(G t * (X t * X t + (controlP (vertex m) (X t) * X t -
      X t * controlP (vertex m) (X t)))) *ᵥ sixthRoot j‖ ≤ C := by
    intro m
    have hXc := oct_X_continuous hk
    have hPc : Continuous fun t ↦ controlP (vertex m) (X t) :=
      continuousOn_univ.1 (poly_controlP_continuousOn hXc.continuousOn (poly_vertex_mem m)
        fun t _ ↦ (oct_det_star hk t).2)
    refine oct_bound_of_periodic hP ?_ fun t ↦ ?_
    · exact ((oct_G_continuous hk).matrix_mul ((hXc.matrix_mul hXc).add
        ((hPc.matrix_mul hXc).sub (hXc.matrix_mul hPc)))).matrix_mulVec continuous_const
    · simp only [oct_G_periodic hk t, oct_X_periodic hk t, G, X]
  choose C hC using hbound
  refine ⟨Real.toNNReal (C 0 + C 1 + C 2), oct_lipschitzWith_of_hasDerivAt
    (oct_knots_countable (tsw k)) ?_ fun t ht ↦ ?_⟩
  · rw [oct_curve_deriv hk j]
    exact (oct_GX_continuous hk).matrix_mulVec continuous_const
  · obtain ⟨m, hm⟩ := oct_curve_deriv2 hk j ht
    refine ⟨_, hm, (hC m t).trans ?_⟩
    have h0 := (norm_nonneg _).trans (hC 0 t)
    have h1 := (norm_nonneg _).trans (hC 1 t)
    have h2 := (norm_nonneg _).trans (hC 2 t)
    refine le_trans ?_ (Real.le_coe_toNNReal _)
    fin_cases m <;> simp <;> linarith

/-! ### The symmetry `h = g_sw R⁻¹` -/

/-- `h = g_sw R⁻¹` has `h₀₀ = h₁₁ = cos θ_k`, `h₀₁ > 0` and `det h = 1`, so it is the rotation by
`-θ_k` in suitable coordinates. -/
lemma oct_h_entries (hk : 1 ≤ k) :
    (segG (y₀ k) (tsw k) * R⁻¹) 0 0 = Real.cos (θ k) ∧
      (segG (y₀ k) (tsw k) * R⁻¹) 1 1 = Real.cos (θ k) ∧
      0 < (segG (y₀ k) (tsw k) * R⁻¹) 0 1 ∧ (segG (y₀ k) (tsw k) * R⁻¹).det = 1 := by
  obtain ⟨hy0, hy1⟩ := poly_y₀_mem hk
  have hy := poly_y0_pos hy0
  have htr := poly_y₀_trace hk
  have hc1 := (poly_cos_θ hk).2
  have h3 : (0 : ℝ) < √3 := by positivity
  have hs3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hdet : (segG (y₀ k) (tsw k) * R⁻¹).det = 1 := by
    rw [Matrix.det_mul, (seg_solution (y₀ k) 0 hy).2.2.2.2, poly_det_Rinv, one_mul]
  rw [tsw_eq_switchTime, segG_eq _ _ hy, str_exp_switchTime hy, str_R_inv] at *
  have hcos : Real.cos (θ k) = 4 / (3 * y₀ k ^ 2 + 1) / 2 := by linarith
  have hW2 : 4 / (3 * y₀ k ^ 2 + 1) < 2 := by linarith
  have hY : 0 < y₀ k ^ 2 := by positivity
  refine ⟨?_, ?_, ?_, hdet⟩
  · rw [hcos]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
    ring
  · rw [hcos]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
    ring_nf
  · have hpos : 0 < (4 - 4 / (3 * y₀ k ^ 2 + 1)) / (2 * √3) :=
      div_pos (by linarith) (by positivity)
    refine lt_of_lt_of_eq hpos ?_
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
    ring_nf
    simp only [hs3]
    ring_nf

/-- The coordinates in which `h = g_sw R⁻¹` acts as the rotation by `-θ_k`:
`v ↦ v₀/h₀₁ + i v₁/sin θ_k`. -/
noncomputable def oct_hat (k : ℕ) (v : Fin 2 → ℝ) : ℂ :=
  ((v 0 / (segG (y₀ k) (tsw k) * R⁻¹) 0 1 : ℝ) : ℂ) + ((v 1 / Real.sin (θ k) : ℝ) : ℂ) * Complex.I

lemma oct_sin_θ_pos (hk : 1 ≤ k) : 0 < Real.sin (θ k) := by
  refine Real.sin_pos_of_pos_of_lt_pi (poly_θ_pos hk) ?_
  linarith [poly_θ_lt k, Real.pi_pos]

lemma oct_hat_neg (v : Fin 2 → ℝ) : oct_hat k (-v) = -oct_hat k v := by
  simp only [oct_hat, Pi.neg_apply, neg_div, Complex.ofReal_neg]
  ring

lemma oct_hat_re (v : Fin 2 → ℝ) :
    (oct_hat k v).re = v 0 / (segG (y₀ k) (tsw k) * R⁻¹) 0 1 := by
  simp only [oct_hat, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re,
    mul_zero, add_zero]

lemma oct_hat_im (v : Fin 2 → ℝ) : (oct_hat k v).im = v 1 / Real.sin (θ k) := by
  simp only [oct_hat, Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, Complex.I_im,
    mul_one, zero_add]

lemma oct_exp_neg_θ : Complex.exp (-(θ k : ℂ) * Complex.I) =
    (Real.cos (θ k) : ℂ) - (Real.sin (θ k) : ℂ) * Complex.I := by
  rw [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin]
  ring

lemma oct_hat_h (hk : 1 ≤ k) (v : Fin 2 → ℝ) :
    oct_hat k ((segG (y₀ k) (tsw k) * R⁻¹) *ᵥ v) =
      Complex.exp (-(θ k : ℂ) * Complex.I) * oct_hat k v := by
  obtain ⟨h00, h11, hb, hdet⟩ := oct_h_entries hk
  set h := segG (y₀ k) (tsw k) * R⁻¹ with hh
  have hs := oct_sin_θ_pos hk
  have hcs := Real.sin_sq_add_cos_sq (θ k)
  rw [Matrix.det_fin_two, h00, h11] at hdet
  have h10 : h 1 0 = -(Real.sin (θ k) ^ 2 / h 0 1) := by
    field_simp
    linarith
  rw [oct_exp_neg_θ]
  apply Complex.ext
  · rw [oct_hat_re, Complex.mul_re, oct_hat_re, oct_hat_im]
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, ← hh]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h00]
    field_simp
    ring
  · rw [oct_hat_im, Complex.mul_im, oct_hat_re, oct_hat_im]
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, ← hh]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h11, h10]
    field_simp
    ring

/-- `h³` acts as the rotation by `-3θ_k`. -/
lemma oct_hat_h_pow (hk : 1 ≤ k) (n : ℕ) (v : Fin 2 → ℝ) :
    oct_hat k ((segG (y₀ k) (tsw k) * R⁻¹) ^ n *ᵥ v) =
      Complex.exp (-(n * θ k : ℂ) * Complex.I) * oct_hat k v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, oct_hat_h hk, ih, ← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring

/-- `σ₀(t + 3t_sw) = -h³ σ₀(t)`, and `-h³` acts as the rotation by `π - 3θ_k = π/(3k+1)`. -/
lemma oct_hat_M (hk : 1 ≤ k) (v : Fin 2 → ℝ) :
    oct_hat k (-((segG (y₀ k) (tsw k) * R⁻¹) ^ 3) *ᵥ v) =
      Complex.exp ((Real.pi / (3 * k + 1) : ℝ) * Complex.I) * oct_hat k v := by
  rw [Matrix.neg_mulVec, oct_hat_neg, oct_hat_h_pow hk, ← neg_mul, ← neg_one_mul,
    ← Complex.exp_pi_mul_I, ← Complex.exp_add]
  congr 2
  have hθ : θ k = Real.pi * k / (3 * k + 1) := rfl
  have hkC : (3 * (k : ℂ) + 1) ≠ 0 := by norm_cast
  rw [hθ]
  push_cast
  field_simp
  ring

lemma oct_G_add_three_tsw (hk : 1 ≤ k) (t : ℝ) :
    smoothedPolygonG k (t + 3 * tsw k) =
      -((segG (y₀ k) (tsw k) * R⁻¹) ^ 3) * smoothedPolygonG k t := by
  rw [show t + 3 * tsw k = ((t + tsw k) + tsw k) + tsw k by ring, oct_G_add_tsw hk,
    oct_G_add_tsw hk, oct_G_add_tsw hk]
  have hR3 := poly_R_pow_three
  rw [pow_succ, pow_succ, pow_one] at hR3
  simp only [Matrix.mul_assoc] at hR3 ⊢
  rw [hR3, pow_succ, pow_succ, pow_one]
  simp only [Matrix.mul_assoc, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul]

/-! ### The curve `σ₀` is simple -/

/-- `g₀(z₀, u) s₁* = ((2 - w)/2, √3((w - 1)(2 - w) + 3y₀²w)/(6y₀²w))`, `w = exp(√3 y₀ u)`. -/
lemma oct_segG_s1 {y : ℝ} (hy : 0 < y) (u : ℝ) :
    segG y u *ᵥ sixthRoot 1 = ![(2 - Real.exp (√3 * y * u)) / 2,
      √3 * ((Real.exp (√3 * y * u) - 1) * (2 - Real.exp (√3 * y * u)) +
        3 * y ^ 2 * Real.exp (√3 * y * u)) / (6 * y ^ 2 * Real.exp (√3 * y * u))] := by
  have hw := Real.exp_pos (√3 * y * u)
  have h3 : (0 : ℝ) < √3 := by positivity
  have hs3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [segG_eq y u hy, algA_sixthRoot_one]
  generalize Real.exp (√3 * y * u) = w at hw ⊢
  ext i; fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    field_simp
    ring
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    field_simp
    ring_nf
    rw [hs3]
    ring

/-- `g₀(z₀, u) s₂* = (-w/2, √3(3y₀² + 1 - w)/(6y₀²))`, `w = exp(√3 y₀ u)`. -/
lemma oct_segG_s2 {y : ℝ} (hy : 0 < y) (u : ℝ) :
    segG y u *ᵥ sixthRoot 2 = ![-(Real.exp (√3 * y * u) / 2),
      √3 * (3 * y ^ 2 + 1 - Real.exp (√3 * y * u)) / (6 * y ^ 2)] := by
  have hw := Real.exp_pos (√3 * y * u)
  have h3 : (0 : ℝ) < √3 := by positivity
  have hs3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [segG_eq y u hy, algA_sixthRoot_two]
  generalize Real.exp (√3 * y * u) = w at hw ⊢
  ext i; fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    field_simp
    ring
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    field_simp
    ring_nf
    rw [hs3]
    ring

/-- `θ_k ≥ π/4`, so `2 cos² θ_k ≤ 1`. -/
lemma oct_two_cos_sq_le (hk : 1 ≤ k) : 2 * Real.cos (θ k) ^ 2 ≤ 1 := by
  have hθ4 : Real.pi / 4 ≤ θ k := by
    unfold θ
    rw [le_div_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith [Real.pi_pos]
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith [poly_θ_lt k,
    Real.pi_pos]) hθ4
  rw [Real.cos_pi_div_four] at hc
  have hc0 := (poly_cos_θ hk).1
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith

/-- **The half-plane condition.** On the first three switching intervals `[0, 3t_sw]` the curve
`σ₀` stays in the half-plane `x > 0`: there `σ₀ = hⁱ g₀(z₀, t - i t_sw) s_i*`, `i = 0, 1, 2`. -/
lemma oct_curve0_pos (hk : 1 ≤ k) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 3 * tsw k) :
    0 < smoothedPolygonCurve k 0 t 0 := by
  obtain ⟨hy0, hy1⟩ := poly_y₀_mem hk
  have hy := poly_y0_pos hy0
  have hτ := oct_tsw_pos hk
  obtain ⟨h00, h11, hb, hdet⟩ := oct_h_entries hk
  have hc0 := (poly_cos_θ hk).1
  have hcs := oct_two_cos_sq_le hk
  have hY := str_one_third_lt_sq hy0
  set h := segG (y₀ k) (tsw k) * R⁻¹ with hh
  have hpiece : ∀ i : ℕ, (i : ℝ) * tsw k ≤ t → t ≤ (i + 1) * tsw k →
      smoothedPolygonCurve k 0 t =
        h ^ i *ᵥ (segG (y₀ k) (t - i * tsw k) *ᵥ sixthRoot (i : ZMod 6)) := by
    intro i h1 h2
    simp only [smoothedPolygonCurve]
    rw [oct_G_of_nonneg hk ht0, poly_Gp_eq (τ := tsw k) hy0 hy1 rfl ⟨h1, h2⟩, poly_Gp,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, oct_R_pow_mulVec_sixthRoot, zero_add]
  -- `1 ≤ w < 2` on a switching interval
  have hW : ∀ u, 0 ≤ u → u ≤ tsw k →
      1 ≤ Real.exp (√3 * y₀ k * u) ∧ Real.exp (√3 * y₀ k * u) < 2 ∧
        Real.exp (√3 * y₀ k * u) < 3 * y₀ k ^ 2 + 1 := by
    intro u hu0 hu1
    obtain ⟨hw1, hw2⟩ := str_W_mem hy ⟨hu0, hu1⟩
    have : 4 / (3 * y₀ k ^ 2 + 1) < 2 := by rw [div_lt_iff₀ (by positivity)]; linarith
    exact ⟨hw1, by linarith, by linarith⟩
  rcases le_or_gt t (tsw k) with h1 | h1
  · rw [hpiece 0 (by simpa using ht0) (by simpa using h1)]
    simp [segG_eq _ _ hy, algA_sixthRoot_zero, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rcases le_or_gt t (2 * tsw k) with h2 | h2
  · rw [hpiece 1 (by simpa using h1.le) (by norm_num; linarith), pow_one]
    push_cast
    rw [oct_segG_s1 hy]
    obtain ⟨hw1, hw2, -⟩ := hW (t - 1 * tsw k) (by linarith) (by linarith)
    generalize Real.exp (√3 * y₀ k * (t - 1 * tsw k)) = w at hw1 hw2 ⊢
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    rw [h00]
    have : 0 < √3 * ((w - 1) * (2 - w) + 3 * y₀ k ^ 2 * w) / (6 * y₀ k ^ 2 * w) := by
      apply div_pos _ (by positivity)
      apply mul_pos (by positivity)
      nlinarith
    have : 0 < (2 - w) / 2 := by linarith
    positivity
  · rw [hpiece 2 (by norm_num; linarith) (by norm_num; linarith)]
    push_cast
    rw [oct_segG_s2 hy]
    obtain ⟨hw1, -, hw3⟩ := hW (t - 2 * tsw k) (by norm_num; linarith) (by norm_num; linarith)
    generalize Real.exp (√3 * y₀ k * (t - 2 * tsw k)) = w at hw1 hw3 ⊢
    rw [Matrix.det_fin_two, h00, h11] at hdet
    rw [pow_two h]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.mul_apply, h00, h11]
    have hv1 : 0 < √3 * (3 * y₀ k ^ 2 + 1 - w) / (6 * y₀ k ^ 2) :=
      div_pos (mul_pos (by positivity) (by linarith)) (by positivity)
    have hA : 0 ≤ (Real.cos (θ k) * Real.cos (θ k) + h 0 1 * h 1 0) * -(w / 2) := by
      have : Real.cos (θ k) * Real.cos (θ k) + h 0 1 * h 1 0 ≤ 0 := by nlinarith
      nlinarith
    have hB : 0 < (Real.cos (θ k) * h 0 1 + h 0 1 * Real.cos (θ k)) *
        (√3 * (3 * y₀ k ^ 2 + 1 - w) / (6 * y₀ k ^ 2)) := by positivity
    linarith

/-- The curve `σ₀` in the coordinates `oct_hat` in which `h` is a rotation. -/
noncomputable def oct_z (k : ℕ) (t : ℝ) : ℂ := oct_hat k (smoothedPolygonCurve k 0 t)

/-- The derivative of `oct_z`. -/
noncomputable def oct_z' (k : ℕ) (t : ℝ) : ℂ := oct_hat k (deriv (smoothedPolygonCurve k 0) t)

lemma oct_hat_hasDerivAt {γ : ℝ → Fin 2 → ℝ} {v : Fin 2 → ℝ} {t : ℝ} (h : HasDerivAt γ v t) :
    HasDerivAt (fun t ↦ oct_hat k (γ t)) (oct_hat k v) t := by
  have h0 := ((hasDerivAt_pi.1 h 0).div_const ((segG (y₀ k) (tsw k) * R⁻¹) 0 1)).ofReal_comp
  have h1 := ((hasDerivAt_pi.1 h 1).div_const (Real.sin (θ k))).ofReal_comp
  exact h0.add (h1.mul_const Complex.I)

lemma oct_hat_continuous {γ : ℝ → Fin 2 → ℝ} (h : Continuous γ) :
    Continuous fun t ↦ oct_hat k (γ t) :=
  (Complex.continuous_ofReal.comp (((continuous_apply 0).comp h).div_const _)).add
    ((Complex.continuous_ofReal.comp (((continuous_apply 1).comp h).div_const _)).mul
      continuous_const)

lemma oct_z_hasDerivAt (hk : 1 ≤ k) (t : ℝ) : HasDerivAt (oct_z k) (oct_z' k t) t :=
  oct_hat_hasDerivAt (((oct_curve_contDiff hk 0).differentiable one_ne_zero) t).hasDerivAt

lemma oct_z'_continuous (hk : 1 ≤ k) : Continuous (oct_z' k) :=
  oct_hat_continuous ((oct_curve_contDiff hk 0).continuous_deriv le_rfl)

lemma oct_z_ne_zero (hk : 1 ≤ k) (t : ℝ) : oct_z k t ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  rw [oct_z, oct_hat_re, Complex.zero_re, div_eq_zero_iff] at hre
  rw [oct_z, oct_hat_im, Complex.zero_im, div_eq_zero_iff] at him
  have hb := (oct_h_entries hk).2.2.1
  have hs := oct_sin_θ_pos hk
  have hσ : smoothedPolygonCurve k 0 t = 0 := by
    ext i; fin_cases i
    · exact hre.resolve_right hb.ne'
    · exact him.resolve_right hs.ne'
  have hdet : (smoothedPolygonG k t).det ≠ 0 := by rw [(oct_det_star hk t).1]; norm_num
  exact oct_sixthRoot_ne_zero 0 (Matrix.eq_zero_of_mulVec_eq_zero hdet hσ)

/-- The phase of `σ₀` increases: `Im(z'/z) = det(σ₀, σ₀')/(h₀₁ sin θ_k |z|²) > 0`. -/
lemma oct_z_im_pos (hk : 1 ≤ k) (t : ℝ) : 0 < (oct_z' k t / oct_z k t).im := by
  have hb := (oct_h_entries hk).2.2.1
  have hs := oct_sin_θ_pos hk
  obtain ⟨α, β, hα, hβ, hd⟩ := oct_curve_star hk 0 t
  have hmp := ((oct_curve_isMultiPoint hk t) 0).2.2
  simp only [zero_add] at hmp hd
  have hpos := oct_det2_pos_of_star hα hβ hd hmp
  have hn := Complex.normSq_pos.2 (oct_z_ne_zero hk t)
  rw [Complex.div_im, oct_z, oct_z', oct_hat_re, oct_hat_im, oct_hat_re, oct_hat_im]
  rw [oct_z] at hn
  rw [← sub_div]
  apply div_pos _ hn
  simp only [det2] at hpos
  have e : deriv (smoothedPolygonCurve k 0) t 1 / Real.sin (θ k) *
      (smoothedPolygonCurve k 0 t 0 / (segG (y₀ k) (tsw k) * R⁻¹) 0 1) -
      deriv (smoothedPolygonCurve k 0) t 0 / (segG (y₀ k) (tsw k) * R⁻¹) 0 1 *
      (smoothedPolygonCurve k 0 t 1 / Real.sin (θ k)) =
      (smoothedPolygonCurve k 0 t 0 * deriv (smoothedPolygonCurve k 0) t 1 -
        smoothedPolygonCurve k 0 t 1 * deriv (smoothedPolygonCurve k 0) t 0) /
        ((segG (y₀ k) (tsw k) * R⁻¹) 0 1 * Real.sin (θ k)) := by
    field_simp
  rw [e]
  positivity

lemma oct_curve0_add_three_tsw (hk : 1 ≤ k) (t : ℝ) :
    smoothedPolygonCurve k 0 (t + 3 * tsw k) =
      -((segG (y₀ k) (tsw k) * R⁻¹) ^ 3) *ᵥ smoothedPolygonCurve k 0 t := by
  simp only [smoothedPolygonCurve]
  rw [oct_G_add_three_tsw hk, Matrix.mulVec_mulVec]

/-- The rotational symmetry in the coordinates `oct_hat`: `z(t + 3t_sw) = e^{iπ/(3k+1)} z(t)`,
and likewise for `z'`. -/
lemma oct_z_add (hk : 1 ≤ k) (t : ℝ) :
    oct_z k (t + 3 * tsw k) =
      Complex.exp ((Real.pi / (3 * k + 1) : ℝ) * Complex.I) * oct_z k t := by
  rw [oct_z, oct_curve0_add_three_tsw hk, oct_hat_M hk, oct_z]

lemma oct_z'_add (hk : 1 ≤ k) (t : ℝ) :
    oct_z' k (t + 3 * tsw k) =
      Complex.exp ((Real.pi / (3 * k + 1) : ℝ) * Complex.I) * oct_z' k t := by
  set M := -((segG (y₀ k) (tsw k) * R⁻¹) ^ 3)
  have hd : ∀ x, HasDerivAt (smoothedPolygonCurve k 0) (deriv (smoothedPolygonCurve k 0) x) x :=
    fun x ↦ (((oct_curve_contDiff hk 0).differentiable one_ne_zero) x).hasDerivAt
  have h1 : HasDerivAt (fun x ↦ smoothedPolygonCurve k 0 (x + 3 * tsw k))
      (deriv (smoothedPolygonCurve k 0) (t + 3 * tsw k)) t := (hd _).comp_add_const _ _
  have h2 : HasDerivAt (fun x ↦ M *ᵥ smoothedPolygonCurve k 0 x)
      (M *ᵥ deriv (smoothedPolygonCurve k 0) t) t := by
    have := (hasDerivAtEntrywise_const M t).mulVec (hd t)
    simpa using this
  have hfun : (fun x ↦ smoothedPolygonCurve k 0 (x + 3 * tsw k)) =
      fun x ↦ M *ᵥ smoothedPolygonCurve k 0 x := funext fun x ↦ oct_curve0_add_three_tsw hk x
  rw [hfun] at h1
  rw [oct_z', h1.unique h2, oct_hat_M hk, oct_z']

lemma oct_ratio_periodic (hk : 1 ≤ k) :
    Function.Periodic (fun t ↦ (oct_z' k t / oct_z k t).im) (3 * tsw k) := by
  intro t
  simp only
  rw [oct_z_add hk, oct_z'_add hk, mul_div_mul_left _ _ (Complex.exp_ne_zero _)]

/-- Over three switching intervals the phase increases by exactly `π/(3k+1)`: the rotational
symmetry gives it up to a multiple of `2π`, and the half-plane condition bounds it by `π`. -/
lemma oct_phase_three_tsw (hk : 1 ≤ k) :
    oct_phase (oct_z k) (oct_z' k) (3 * tsw k) = Real.pi / (3 * k + 1) := by
  have hz := oct_z_hasDerivAt hk
  have hz' := oct_z'_continuous hk
  have hz0 := oct_z_ne_zero hk
  have hτ := oct_tsw_pos hk
  have hpi := Real.pi_pos
  have hmono := oct_phase_strictMono hz hz' hz0 (oct_z_im_pos hk)
  obtain ⟨n, hn⟩ := oct_phase_sub_of_eq hz hz' hz0 (a := 0) (b := 3 * tsw k)
    (w := ((Real.pi / (3 * k + 1) : ℝ) : ℂ)) (by rw [← oct_z_add hk, zero_add])
  rw [oct_phase_zero, zero_add, Complex.ofReal_re] at hn
  have hlo : 0 < oct_phase (oct_z k) (oct_z' k) (3 * tsw k) := by
    rw [← oct_phase_zero (z := oct_z k) (z' := oct_z' k)]; exact hmono (by positivity)
  -- the half-plane condition: the phase stays below `π`
  have hhi : oct_phase (oct_z k) (oct_z' k) (3 * tsw k) < Real.pi := by
    by_contra hcon
    replace hcon := not_lt.1 hcon
    have hcont : Continuous (oct_phase (oct_z k) (oct_z' k)) :=
      continuous_iff_continuousAt.2 fun t ↦ (oct_phase_hasDerivAt hz hz' hz0 t).continuousAt
    obtain ⟨t₁, ht₁, hπ⟩ := intermediate_value_Icc (by positivity : (0 : ℝ) ≤ 3 * tsw k)
      hcont.continuousOn ⟨by rw [oct_phase_zero]; exact hpi.le, hcon⟩
    have heq := oct_eq_exp hz hz' hz0 t₁
    rw [hπ, Complex.exp_add, Complex.exp_pi_mul_I, ← Complex.ofReal_exp] at heq
    have hre := congrArg Complex.re heq
    rw [oct_z, oct_hat_re] at hre
    simp only [mul_neg, mul_one, Complex.neg_re, Complex.re_mul_ofReal] at hre
    rw [oct_z, oct_hat_re] at hre
    have hb := (oct_h_entries hk).2.2.1
    have h1 := oct_curve0_pos hk ht₁.1 ht₁.2
    have h2 := oct_curve0_pos hk le_rfl (by positivity)
    have h3 := Real.exp_pos (oct_logmod (oct_z k) (oct_z' k) t₁)
    have : 0 < smoothedPolygonCurve k 0 t₁ 0 / (segG (y₀ k) (tsw k) * R⁻¹) 0 1 := by positivity
    have : 0 < smoothedPolygonCurve k 0 0 0 / (segG (y₀ k) (tsw k) * R⁻¹) 0 1 := by positivity
    nlinarith
  have hω0 : 0 < Real.pi / (3 * k + 1) := by positivity
  have hω1 : Real.pi / (3 * k + 1) ≤ Real.pi := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hn0 : n = 0 := by
    have : (n : ℝ) < 1 / 2 := by nlinarith
    have : (-1 / 2 : ℝ) < n := by nlinarith
    have : n < 1 := by exact_mod_cast (show (n : ℝ) < 1 by linarith)
    have : -1 < n := by exact_mod_cast (show (-1 : ℝ) < n by linarith)
    omega
  rw [hn, hn0]
  simp

/-- Over one period `6 t_f = 2(3k+1) · 3t_sw` the phase increases by `2π`: the winding number of
`σ₀` is one. -/
lemma oct_phase_period (hk : 1 ≤ k) :
    oct_phase (oct_z k) (oct_z' k) (6 * tf k) = 2 * Real.pi := by
  have hz := oct_z_hasDerivAt hk
  have hz' := oct_z'_continuous hk
  have hz0 := oct_z_ne_zero hk
  have hc := Complex.continuous_im.comp (oct_ratio_continuous hz hz' hz0)
  have h := (oct_ratio_periodic hk).intervalIntegral_add_zsmul_eq (2 * (3 * k + 1) : ℕ) 0
    fun a b ↦ hc.intervalIntegrable a b
  rw [zero_add, zero_add] at h
  have hP : (((2 * (3 * k + 1) : ℕ) : ℤ) • (3 * tsw k)) = 6 * tf k := by
    rw [zsmul_eq_mul, tf]; push_cast; ring
  rw [hP] at h
  unfold oct_phase
  rw [h]
  change (((2 * (3 * k + 1) : ℕ) : ℤ) • oct_phase (oct_z k) (oct_z' k) (3 * tsw k)) = _
  rw [oct_phase_three_tsw hk, zsmul_eq_mul]
  push_cast
  field_simp

/-- **`σ₀` is simple on a period.** -/
lemma oct_curve0_injOn (hk : 1 ≤ k) : InjOn (smoothedPolygonCurve k 0) (Ico 0 (6 * tf k)) := by
  have hinj := oct_injOn_of_phase (oct_z_hasDerivAt hk) (oct_z'_continuous hk)
    (oct_z_ne_zero hk) (oct_z_im_pos hk) (oct_phase_period hk)
  intro a ha b hb hab
  exact hinj ha hb (by simp only [oct_z, hab])

/-! ### The smoothed `(6k+2)`-gon is a balanced disk -/

lemma oct_curve_eq_shift (hk : 1 ≤ k) (j : ZMod 6) :
    smoothedPolygonCurve k j = fun t ↦ smoothedPolygonCurve k 0 (t + j.val * tf k) := by
  funext t
  rw [oct_curve_add_nat_tf hk, ZMod.natCast_zmod_val]

lemma oct_curve_injOn (hk : 1 ≤ k) (j : ZMod 6) :
    InjOn (smoothedPolygonCurve k j) (Ico 0 (6 * tf k)) := by
  rw [oct_curve_eq_shift hk j]
  exact oct_injOn_shift (oct_P_pos hk) (oct_curve_periodic hk 0) (oct_curve0_injOn hk) _

/-- `σ₀` is a star-shaped closed curve with period `6 t_f`. -/
lemma oct_polygon_isStarCurve (hk : 1 ≤ k) :
    PlaneCurve.IsStarCurve (smoothedPolygonCurve k 0) (6 * tf k) where
  pos := oct_P_pos hk
  contDiff := oct_curve_contDiff hk 0
  periodic := oct_curve_periodic hk 0
  injOn := oct_curve0_injOn hk
  cross_pos := fun t ↦ by
    obtain ⟨α, β, hα, hβ, hd⟩ := oct_curve_star hk 0 t
    have hmp := ((oct_curve_isMultiPoint hk t) 0).2.2
    simp only [zero_add] at hmp hd
    exact oct_det2_pos_of_star hα hβ hd hmp

lemma oct_curve_image (hk : 1 ≤ k) (j : ZMod 6) :
    smoothedPolygonCurve k j '' Ico 0 (6 * tf k) = frontier (smoothedPolygonDisk k) := by
  have hP := oct_P_pos hk
  rw [smoothedPolygonDisk, (oct_polygon_isStarCurve hk).frontier_radialHull,
    oct_image_Ico hP (oct_curve_periodic hk j), oct_image_Ico hP (oct_curve_periodic hk 0),
    oct_curve_eq_shift hk j]
  exact (Equiv.addRight ((ZMod.val j : ℝ) * tf k)).surjective.range_comp
    (smoothedPolygonCurve k 0)

lemma oct_disk_neg (hk : 1 ≤ k) : ∀ x ∈ smoothedPolygonDisk k, -x ∈ smoothedPolygonDisk k := by
  rintro x ⟨t, -, r, hr, rfl⟩
  refine ⟨oct_red (6 * tf k) (t + 3 * tf k), Ico_subset_Icc_self (oct_red_mem (oct_P_pos hk) _),
    r, hr, ?_⟩
  have h3 := oct_curve_add_nat_tf hk 3 t
  have hmp := ((oct_curve_isMultiPoint hk t) 0).2.1
  simp only [zero_add] at hmp
  push_cast at h3
  rw [oct_periodic_red (oct_curve_periodic hk 0), h3, hmp, smul_neg]

/-- **The smoothed `(6k+2)`-gon is a balanced disk in circle representation.** The curve `σ₀` is a
star-shaped closed curve (`oct_polygon_isStarCurve`: simple by the winding argument, turning
counterclockwise by the star condition); `K` is convex because the tangent of `σ₀` turns
counterclockwise (`det(σ₀', σ₀'') ≥ 0`), compact with `0` in its interior, centrally symmetric
(`σ₀(t + 3t_f) = -σ₀(t)`), and its boundary is the image of each `σ_j` over a period. -/
theorem smoothedPolygonDisk_isBalancedPair (k : ℕ) (hk : 1 ≤ k) :
    IsBalancedPair (smoothedPolygonDisk k) (smoothedPolygonCurve k) (tf k) ∧
      IsCircleRepresentation (smoothedPolygonCurve k) := by
  have hstar := oct_polygon_isStarCurve hk
  refine ⟨⟨⟨hstar.convex_radialHull (oct_curve_lipschitz hk 0) (oct_curve_curvature hk 0),
    hstar.isCompact_radialHull, ⟨0, hstar.zero_mem_interior_radialHull⟩, oct_disk_neg hk⟩,
    fun j ↦ ⟨oct_curve_contDiff hk j, oct_curve_deriv_ne_zero hk j⟩, oct_curve_lipschitz hk,
    oct_curve_isMultiPoint hk, oct_curve_curvature hk, oct_curve_star hk, oct_tf_pos hk,
    oct_curve_periodic hk, oct_curve_injOn hk, oct_curve_image hk⟩, fun j ↦ ?_⟩
  simp only [smoothedPolygonCurve, oct_G_zero hk, Matrix.one_mulVec]

/-- An integral curve is unchanged if the curve and the right-hand side are changed off
`[0, T]`. -/
lemma oct_isIntegralCurve_congr {f f' v v' : ℝ → Mat2} {T : ℝ} (hT : 0 ≤ T)
    (h : IsIntegralCurve f v T) (hf : ∀ t ∈ Icc 0 T, f' t = f t)
    (hv : ∀ t ∈ Icc 0 T, v' t = v t) : IsIntegralCurve f' v' T := by
  have h' := poly_isIntegralCurve_congr h hT fun t ht ↦ (hv t ht).symm
  intro i j
  refine ⟨(h' i j).1, fun t ht ↦ ?_⟩
  rw [hf t ht, hf 0 ⟨le_rfl, hT⟩]
  exact (h' i j).2 t ht

/-- The extended spline is the trajectory of the smoothed `(6k+2)`-gon of Theorem 7.5.6: the state
trajectory with the control `polygonControl k`, `g(0) = I₂` and `X(0) = Φ(i y₀)`. -/
theorem smoothedPolygon_isStateTrajectory (k : ℕ) (hk : 1 ≤ k) :
    IsStateTrajectory (tf k) (polygonControl k) (smoothedPolygonG k) (smoothedPolygonX k) ∧
      smoothedPolygonG k 0 = 1 ∧ smoothedPolygonX k 0 = Φ 0 (y₀ k) := by
  obtain ⟨⟨hT, hu, hus, hst, hgI, hXI⟩, -, -⟩ := oct_polygon_traj hk (3 * k + 1) (by omega)
  rw [← oct_tf_eq] at hT hus hst hgI hXI
  refine ⟨⟨hT, hu, hus, fun t ht ↦ ?_, ?_, ?_⟩, oct_G_zero hk, oct_X_zero hk⟩
  · rw [oct_G_of_nonneg hk ht.1, oct_X_of_nonneg hk ht.1]; exact hst t ht
  · refine oct_isIntegralCurve_congr hT.le hgI (fun t ht ↦ oct_G_of_nonneg hk ht.1)
      fun t ht ↦ ?_
    simp only [oct_G_of_nonneg hk ht.1, oct_X_of_nonneg hk ht.1]
  · refine oct_isIntegralCurve_congr hT.le hXI (fun t ht ↦ oct_X_of_nonneg hk ht.1)
      fun t ht ↦ ?_
    simp only [oct_X_of_nonneg hk ht.1, polygonControl_eq]

/-- **The area of the smoothed `(6k+2)`-gon is the cost of its trajectory** (`eqn:cost`). -/
theorem smoothedPolygonDisk_volume (k : ℕ) (hk : 1 ≤ k) :
    volume (smoothedPolygonDisk k) = ENNReal.ofReal (reinhardtCost (tf k) (smoothedPolygonX k)) :=
  eqn_cost (smoothedPolygonDisk_isBalancedPair k hk).1 (smoothedPolygonG k) (smoothedPolygonX k)
    (fun _ _ _ ↦ rfl) (fun t _ ↦ oct_G_hasDerivAt hk t) (oct_curve_add_tf hk)

/-- **The smoothed `(6k+2)`-gon as a balanced disk.** For every `k ≥ 1`, the trajectory
`(g, X)` of the smoothed `(6k+2)`-gon (Theorem 7.5.6), extended to `ℝ` with period `6 t_f`, gives
the multi-curve `σ_j(t) = g(t) s_j*`; the region `K` swept from the origin by `σ₀` is a balanced
disk, `(K, σ)` is a balanced pair in circle representation with `σ_j(t + t_f) = σ_{j+1}(t)`, and
the area of `K` is the cost `-(3/2) ∫₀^{t_f} ⟨J, X⟩ dt` (`eqn:cost`). -/
theorem smoothedPolygonDisk_spec (k : ℕ) (hk : 1 ≤ k) :
    IsStateTrajectory (tf k) (polygonControl k) (smoothedPolygonG k) (smoothedPolygonX k) ∧
      smoothedPolygonG k 0 = 1 ∧ smoothedPolygonX k 0 = Φ 0 (y₀ k) ∧
      (∀ j t, smoothedPolygonCurve k j t = smoothedPolygonG k t *ᵥ sixthRoot j) ∧
      (∀ j t, smoothedPolygonCurve k j (t + tf k) = smoothedPolygonCurve k (j + 1) t) ∧
      IsBalancedPair (smoothedPolygonDisk k) (smoothedPolygonCurve k) (tf k) ∧
      IsCircleRepresentation (smoothedPolygonCurve k) ∧
      volume (smoothedPolygonDisk k) =
        ENNReal.ofReal (reinhardtCost (tf k) (smoothedPolygonX k)) := by
  obtain ⟨h1, h2, h3⟩ := smoothedPolygon_isStateTrajectory k hk
  exact ⟨h1, h2, h3, fun _ _ ↦ rfl, oct_curve_add_tf hk,
    (smoothedPolygonDisk_isBalancedPair k hk).1, (smoothedPolygonDisk_isBalancedPair k hk).2,
    smoothedPolygonDisk_volume k hk⟩

/-- The area `√12 (8 - √32 - ln 2)/(√8 - 1)` of the smoothed octagon is nonnegative. -/
lemma oct_octagon_value_nonneg : 0 ≤ √12 * (8 - √32 - Real.log 2) / (√8 - 1) := by
  have h2lo : (1.4142 : ℝ) < √2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2hi : √2 < (1.4143 : ℝ) := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hl := Real.log_two_lt_d9
  rw [poly_sqrt32, poly_sqrt8, poly_sqrt12]
  exact div_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith)

/-- **The area of the smoothed octagon** (`k = 1`): `√12 (8 - √32 - ln 2)/(√8 - 1)`, so its
density is `(8 - √32 - ln 2)/(√8 - 1)` (`eqn:density-formula`), by `eqn:cost` and the example
before Theorem 7.5.6. -/
theorem smoothedOctagon_volume :
    volume (smoothedPolygonDisk 1) =
      ENNReal.ofReal (√12 * (8 - √32 - Real.log 2) / (√8 - 1)) ∧
      (volume (smoothedPolygonDisk 1)).toReal / √12 = (8 - √32 - Real.log 2) / (√8 - 1) := by
  obtain ⟨hst, hg0, hX0⟩ := smoothedPolygon_isStateTrajectory 1 le_rfl
  obtain ⟨-, -, -, -, h⟩ := example7_5_smoothedOctagon
  obtain ⟨-, hval, -, hdens⟩ := h _ _ hst hg0 hX0
  have hvol := smoothedPolygonDisk_volume 1 le_rfl
  refine ⟨by rw [hvol, hval], ?_⟩
  rw [hvol, ENNReal.toReal_ofReal, hdens]
  rw [hval]
  exact oct_octagon_value_nonneg

/-- **The smoothed octagon as a balanced disk** (the example before Theorem 7.5.6, with
`eqn:cost`). `y₀ = √((√8 - 1)/3)`, `t_sw = ln 2/(2√(√8 - 1))`, and the trajectory `(g, X)` of the
smoothed octagon (`k = 1`) defines a balanced pair `(K, σ)` in circle representation, with
`σ_j(t) = g(t) s_j*` and `σ_j(t + t_f) = σ_{j+1}(t)`; the area of `K` is
`√12 (8 - √32 - ln 2)/(√8 - 1) < π`, so its density `area/√12` is `(8 - √32 - ln 2)/(√8 - 1)`. -/
theorem smoothedOctagon_isBalancedPair_area :
    y₀ 1 = √((√8 - 1) / 3) ∧ tsw 1 = Real.log 2 / (2 * √(√8 - 1)) ∧
    ∃ (g X : ℝ → Mat2) (K : Set (Fin 2 → ℝ)) (σ : ZMod 6 → ℝ → Fin 2 → ℝ),
      IsStateTrajectory (tf 1) (polygonControl 1) g X ∧ g 0 = 1 ∧ X 0 = Φ 0 (y₀ 1) ∧
      (∀ j t, σ j t = g t *ᵥ sixthRoot j) ∧ (∀ j t, σ j (t + tf 1) = σ (j + 1) t) ∧
      IsBalancedPair K σ (tf 1) ∧ IsCircleRepresentation σ ∧
      volume K = ENNReal.ofReal (√12 * (8 - √32 - Real.log 2) / (√8 - 1)) ∧
      (volume K).toReal < Real.pi ∧
      (volume K).toReal / √12 = (8 - √32 - Real.log 2) / (√8 - 1) := by
  obtain ⟨-, -, hy, htsw, h⟩ := example7_5_smoothedOctagon
  obtain ⟨hst, hg0, hX0, hσ, hshift, hbal, hcirc, hvol⟩ := smoothedPolygonDisk_spec 1 le_rfl
  obtain ⟨-, hval, hlt, -⟩ := h _ _ hst hg0 hX0
  obtain ⟨hvol1, hdens⟩ := smoothedOctagon_volume
  have hpos : 0 ≤ reinhardtCost (tf 1) (smoothedPolygonX 1) := by
    rw [hval]; exact oct_octagon_value_nonneg
  refine ⟨hy, htsw, _, _, _, _, hst, hg0, hX0, hσ, hshift, hbal, hcirc, hvol1, ?_, hdens⟩
  rw [hvol, ENNReal.toReal_ofReal hpos]
  exact hlt

end Disk

end SmoothedPolygons
