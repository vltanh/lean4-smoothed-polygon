module

public import SmoothedPolygons.Ch2.MultiCurve
public import Mathlib.Algebra.Order.ToIntervalMod
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# The unit circle is a balanced disk (§3.2)

The unit disk `{x₀² + x₁² ≤ 1}` together with the rotating multi-curve
`σ_j(t) = Rot(t) s_j*` and `t_f = π/3` is a balanced pair in circle representation
(the example of §3.2, with `X = J` and area `π`). This shows that the hypothesis
`IsBalancedPair` of the theorems of Chapter 3 is satisfiable.
-/

@[expose] public section

namespace SmoothedPolygons

open Real

/-- The rotating multi-curve `σ_j(t) = Rot(t) s_j*`: the point of the unit circle at angle
`t + πj/3`. -/
noncomputable def circleMultiCurve (j : ZMod 6) (t : ℝ) : Fin 2 → ℝ :=
  ![Real.cos (t + Real.pi * j.val / 3), Real.sin (t + Real.pi * j.val / 3)]

/-- The closed unit disk (for the Euclidean norm) in `ℝ²`. -/
def unitDisk : Set (Fin 2 → ℝ) := {x | x 0 ^ 2 + x 1 ^ 2 ≤ 1}

private lemma zmod6_val_one : (1 : ZMod 6).val = 1 := rfl
private lemma zmod6_val_two : (2 : ZMod 6).val = 2 := rfl
private lemma zmod6_val_three : (3 : ZMod 6).val = 3 := rfl
private lemma zmod6_val_four : (4 : ZMod 6).val = 4 := rfl

/-- Rotating the index by `k` rotates the curve by the angle `πk/3`. -/
lemma circleMultiCurve_add (j k : ZMod 6) (t : ℝ) :
    circleMultiCurve (j + k) t =
      ![cos (t + π * j.val / 3 + π * k.val / 3),
        sin (t + π * j.val / 3 + π * k.val / 3)] := by
  have hdiv := Nat.mod_add_div (j.val + k.val) 6
  have h : ((j.val : ℝ) + k.val) =
      ((j + k).val : ℝ) + 6 * (((j.val + k.val) / 6 : ℕ) : ℝ) := by
    rw [ZMod.val_add]; exact_mod_cast hdiv.symm
  have harg : t + π * j.val / 3 + π * k.val / 3 =
      t + π * (j + k).val / 3 + (((j.val + k.val) / 6 : ℕ) : ℝ) * (2 * π) := by
    linear_combination (π / 3) * h
  rw [harg, cos_add_nat_mul_two_pi, sin_add_nat_mul_two_pi]
  rfl

private lemma cos_pi_mul_two_div_three : cos (π * 2 / 3) = -(1 / 2) := by
  rw [show π * 2 / 3 = π - π / 3 by ring, cos_pi_sub, cos_pi_div_three]

private lemma sin_pi_mul_two_div_three : sin (π * 2 / 3) = √3 / 2 := by
  rw [show π * 2 / 3 = π - π / 3 by ring, sin_pi_sub, sin_pi_div_three]

private lemma cos_pi_mul_four_div_three : cos (π * 4 / 3) = -(1 / 2) := by
  rw [show π * 4 / 3 = π / 3 + π by ring, cos_add_pi, cos_pi_div_three]

private lemma sin_pi_mul_four_div_three : sin (π * 4 / 3) = -(√3 / 2) := by
  rw [show π * 4 / 3 = π / 3 + π by ring, sin_add_pi, sin_pi_div_three]

private lemma sqrt_three_sq : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

/-- For every `t`, `j ↦ σ_j(t)` is a multi-point. -/
lemma circleMultiCurve_isMultiPoint (t : ℝ) : IsMultiPoint fun j ↦ circleMultiCurve j t := by
  intro j
  simp only [circleMultiCurve_add, zmod6_val_one, zmod6_val_two, zmod6_val_three,
    zmod6_val_four]
  unfold circleMultiCurve
  generalize t + π * j.val / 3 = y
  refine ⟨?_, ?_, ?_⟩
  · ext i
    fin_cases i <;>
      simp [cos_add, sin_add, cos_pi_mul_two_div_three, sin_pi_mul_two_div_three,
        cos_pi_mul_four_div_three, sin_pi_mul_four_div_three] <;> ring
  · ext i
    fin_cases i <;> simp [show π * 3 / 3 = π by ring, cos_add_pi, sin_add_pi]
  · simp [det2, cos_add, sin_add, cos_pi_div_three, sin_pi_div_three]
    linear_combination (√3 / 2) * sin_sq_add_cos_sq y

private lemma hasDerivAt_circ (c t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ ![cos (s + c), sin (s + c)]) ![-sin (t + c), cos (t + c)] t := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · simpa using ((hasDerivAt_id t).add_const c).cos
  · simpa using ((hasDerivAt_id t).add_const c).sin

private lemma hasDerivAt_circ_deriv (c t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ ![-sin (s + c), cos (s + c)]) ![-cos (t + c), -sin (t + c)] t := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · simpa using ((hasDerivAt_id t).add_const c).sin.fun_neg
  · simpa using ((hasDerivAt_id t).add_const c).cos

lemma deriv_circleMultiCurve (j : ZMod 6) :
    deriv (circleMultiCurve j) =
      fun t ↦ ![-sin (t + π * j.val / 3), cos (t + π * j.val / 3)] := by
  funext t
  exact (hasDerivAt_circ _ t).deriv

lemma deriv_deriv_circleMultiCurve (j : ZMod 6) :
    deriv (deriv (circleMultiCurve j)) =
      fun t ↦ ![-cos (t + π * j.val / 3), -sin (t + π * j.val / 3)] := by
  rw [deriv_circleMultiCurve]
  funext t
  exact (hasDerivAt_circ_deriv _ t).deriv

lemma contDiff_circleMultiCurve (j : ZMod 6) : ContDiff ℝ 1 (circleMultiCurve j) := by
  refine contDiff_pi.2 (Fin.forall_fin_two.2 ⟨?_, ?_⟩) <;>
    simp only [circleMultiCurve, Matrix.cons_val_zero, Matrix.cons_val_one] <;> fun_prop

private lemma lipschitzWith_circ_deriv (c : ℝ) :
    LipschitzWith 1 (fun t : ℝ ↦ ![-sin (t + c), cos (t + c)]) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  rw [NNReal.coe_one, one_mul]
  refine (dist_pi_le_iff dist_nonneg).2 fun i ↦ ?_
  fin_cases i
  · simpa [Real.dist_eq] using abs_sin_sub_sin_le (x + c) (y + c)
  · simpa [Real.dist_eq] using abs_cos_sub_cos_le (x + c) (y + c)

/-- The star condition: `σ_j' = (1/√3) (σ_{j+1} - σ_j) + (1/√3) σ_{j+1}`. -/
lemma circleMultiCurve_star (j : ZMod 6) (t : ℝ) :
    deriv (circleMultiCurve j) t =
      (√3 / 3) • (circleMultiCurve (j + 1) t - circleMultiCurve j t) +
        (√3 / 3) • circleMultiCurve (j + 1) t := by
  simp only [deriv_circleMultiCurve, circleMultiCurve_add, zmod6_val_one]
  unfold circleMultiCurve
  generalize t + π * j.val / 3 = y
  ext i
  fin_cases i
  · simp [cos_add, cos_pi_div_three, sin_pi_div_three]
    linear_combination (sin y / 3) * sqrt_three_sq
  · simp [sin_add, cos_pi_div_three, sin_pi_div_three]
    linear_combination (-cos y / 3) * sqrt_three_sq

lemma circleMultiCurve_curvature (j : ZMod 6) (t : ℝ) :
    0 ≤ det2 (deriv (circleMultiCurve j) t) (deriv (deriv (circleMultiCurve j)) t) := by
  rw [deriv_deriv_circleMultiCurve, deriv_circleMultiCurve]
  simp only [det2, Matrix.cons_val_zero, Matrix.cons_val_one]
  nlinarith [sin_sq_add_cos_sq (t + π * j.val / 3)]

lemma circleMultiCurve_periodic (j : ZMod 6) (t : ℝ) :
    circleMultiCurve j (t + 6 * (π / 3)) = circleMultiCurve j t := by
  unfold circleMultiCurve
  rw [show t + 6 * (π / 3) + π * j.val / 3 = t + π * j.val / 3 + 2 * π by ring,
    cos_add_two_pi, sin_add_two_pi]

lemma circleMultiCurve_injOn (j : ZMod 6) :
    Set.InjOn (circleMultiCurve j) (Set.Ico 0 (6 * (π / 3))) := by
  intro t₁ h₁ t₂ h₂ h
  have hc := congrFun h 0
  have hs := congrFun h 1
  simp only [circleMultiCurve, Matrix.cons_val_zero, Matrix.cons_val_one] at hc hs
  have hcos : cos (t₁ - t₂) = 1 := by
    rw [show t₁ - t₂ = (t₁ + π * j.val / 3) - (t₂ + π * j.val / 3) by ring, cos_sub, hc,
      hs]
    linear_combination cos_sq_add_sin_sq (t₂ + π * j.val / 3)
  have := (cos_eq_one_iff_of_lt_of_lt (by linarith [h₁.1, h₂.2])
    (by linarith [h₁.2, h₂.1])).1 hcos
  linarith

private lemma exists_cos_sin_eq (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    ∃ φ, cos φ = a ∧ sin φ = b := by
  have hab : |a| ≤ 1 := (sq_le_one_iff_abs_le_one a).1 (by nlinarith [sq_nonneg b])
  obtain ⟨ha1, ha2⟩ := abs_le.1 hab
  have hsin : sin (arccos a) = |b| := by
    rw [sin_arccos, show 1 - a ^ 2 = b ^ 2 by linarith, sqrt_sq_eq_abs]
  rcases le_or_gt 0 b with hb | hb
  · exact ⟨arccos a, cos_arccos ha1 ha2, by rw [hsin, abs_of_nonneg hb]⟩
  · exact ⟨-arccos a, by rw [cos_neg, cos_arccos ha1 ha2],
      by rw [sin_neg, hsin, abs_of_neg hb, neg_neg]⟩

/-- The boundary of the unit disk is the unit circle. -/
lemma frontier_unitDisk : frontier unitDisk = {x | x 0 ^ 2 + x 1 ^ 2 = 1} := by
  apply Set.Subset.antisymm
  · exact frontier_le_subset_eq (by fun_prop) continuous_const
  · intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    refine ⟨subset_closure (show x ∈ unitDisk from hx.le), fun hint ↦ ?_⟩
    have hcont : Continuous fun c : ℝ ↦ c • x := continuous_id.smul continuous_const
    have hmem : (fun c : ℝ ↦ c • x) ⁻¹' interior unitDisk ∈ nhds (1 : ℝ) :=
      hcont.continuousAt.preimage_mem_nhds (by simpa using isOpen_interior.mem_nhds hint)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hmem
    have h1 : (1 + ε / 2) • x ∈ unitDisk :=
      interior_subset (hball (by simp [abs_of_pos hε]; linarith))
    simp only [unitDisk, Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul] at h1
    have h2 : (1 + ε / 2) ^ 2 * (x 0 ^ 2 + x 1 ^ 2) ≤ 1 := by linarith
    rw [hx] at h2
    nlinarith

lemma unitDisk_isCCSDisk : IsCCSDisk unitDisk := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    obtain rfl : b = 1 - a := by linarith
    simp only [unitDisk, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hy ⊢
    nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x 0 - y 0)),
      mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x 1 - y 1)),
      mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy hb]
  · refine Metric.isCompact_of_isClosed_isBounded (isClosed_le (by fun_prop) continuous_const) ?_
    refine (Metric.isBounded_closedBall (x := (0 : Fin 2 → ℝ)) (r := 1)).subset fun x hx ↦ ?_
    simp only [unitDisk, Set.mem_ofPred_eq] at hx
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    fin_cases i
    · simpa using (sq_le_one_iff_abs_le_one (x 0)).1 (by nlinarith [sq_nonneg (x 1)])
    · simpa using (sq_le_one_iff_abs_le_one (x 1)).1 (by nlinarith [sq_nonneg (x 0)])
  · exact ⟨0, lt_subset_interior_le (f := fun x : Fin 2 → ℝ ↦ x 0 ^ 2 + x 1 ^ 2)
      (g := fun _ ↦ 1) (by fun_prop) continuous_const (by simp)⟩
  · intro x hx
    simpa [unitDisk] using hx

lemma image_circleMultiCurve (j : ZMod 6) :
    circleMultiCurve j '' Set.Ico 0 (6 * (π / 3)) = frontier unitDisk := by
  rw [frontier_unitDisk]
  apply Set.Subset.antisymm
  · rintro _ ⟨t, -, rfl⟩
    simp [circleMultiCurve, cos_sq_add_sin_sq]
  · intro x hx
    obtain ⟨φ, hc, hs⟩ := exists_cos_sin_eq (x 0) (x 1) hx
    refine ⟨toIcoMod two_pi_pos 0 (φ - π * j.val / 3), ?_, ?_⟩
    · rw [show 6 * (π / 3) = 0 + 2 * π by ring]
      exact toIcoMod_mem_Ico two_pi_pos 0 _
    · rw [← self_sub_toIcoDiv_zsmul, zsmul_eq_mul]
      set n := toIcoDiv two_pi_pos 0 (φ - π * j.val / 3)
      unfold circleMultiCurve
      rw [show φ - π * j.val / 3 - n * (2 * π) + π * j.val / 3 = φ - n * (2 * π) by ring,
        cos_sub_int_mul_two_pi, sin_sub_int_mul_two_pi, hc, hs]
      ext i
      fin_cases i <;> rfl

/-- The unit disk with `σ_j(t) = Rot(t) s_j*` and `t_f = π/3` is a balanced pair in circle
representation (the example of §3.2: `X = J`, area `π`). This shows `IsBalancedPair` is
satisfiable. -/
theorem circle_isBalancedPair :
    IsBalancedPair {x : Fin 2 → ℝ | x 0 ^ 2 + x 1 ^ 2 ≤ 1} circleMultiCurve (Real.pi / 3) ∧
      IsCircleRepresentation circleMultiCurve := by
  refine ⟨⟨unitDisk_isCCSDisk, fun j ↦ ⟨contDiff_circleMultiCurve j, fun t ↦ ?_⟩,
    fun j ↦ ⟨1, ?_⟩, circleMultiCurve_isMultiPoint,
    fun j ↦ Filter.Eventually.of_forall (circleMultiCurve_curvature j),
    fun j t ↦ ⟨√3 / 3, √3 / 3, by positivity, by positivity, circleMultiCurve_star j t⟩,
    by positivity, circleMultiCurve_periodic, circleMultiCurve_injOn,
    image_circleMultiCurve⟩, fun j ↦ ?_⟩
  · rw [deriv_circleMultiCurve]
    intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, neg_eq_zero] at h0 h1
    have := sin_sq_add_cos_sq (t + π * j.val / 3)
    rw [h0, h1] at this
    norm_num at this
  · rw [deriv_circleMultiCurve]
    exact lipschitzWith_circ_deriv _
  · simp [circleMultiCurve, sixthRoot]

end SmoothedPolygons
