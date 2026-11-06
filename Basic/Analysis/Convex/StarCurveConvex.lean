module

public import Basic.Analysis.Convex.StarCurve
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Convexity of regions bounded by locally convex star-shaped curves

If the tangent of a star-shaped closed curve (`PlaneCurve.IsStarCurve`) turns counterclockwise
(`γ'` Lipschitz and `det(γ', γ'') ≥ 0` almost everywhere), the region it bounds is convex.

## Proof

* The polar angle `φ = arg γ(0) + sc_angle γ` turns by `2π` over a period
  (`IsStarCurve.sc_angle_period`). Since `det(γ, γ') > 0`, the angle `α ∈ (0, π)` from `γ` to `γ'`
  is `arccos (⟨γ, γ'⟩ / (|γ| |γ'|))`, and `ψ = φ + α` is a continuous tangent angle, which also
  turns by `2π` over a period (`scc_tangent_angle`).
* `ψ` is nondecreasing (`scc_monotone_angle`): near `x`, with `w = γ'(x)`, the quotient
  `q = det(w, γ') / ⟨w, γ'⟩` is Lipschitz, hence absolutely continuous, with
  `q' = |w|² det(γ', γ'') / ⟨w, γ'⟩² ≥ 0` almost everywhere; by the fundamental theorem of calculus
  for absolutely continuous functions `q ≥ q(x) = 0` to the right of `x`, i.e.
  `sin (ψ - ψ(x)) ≥ 0` there.
* The tangent lines support the curve (`scc_support`): `f(t) = det(γ'(t₀), γ(t) - γ(t₀))` has
  `f' = |γ'(t₀)| |γ'(t)| sin (ψ(t) - ψ(t₀))`, which is `≥ 0` while `ψ(t) - ψ(t₀) ∈ [0, π]` and
  `≤ 0` on `[π, 2π]`; with `f(t₀) = f(t₀ + T) = 0` this gives `f ≥ 0`.
* Hence the region is the intersection of the half-planes `det(γ'(t), x - γ(t)) ≥ 0`: a point
  `r γ(s)` of the region is a convex combination of `γ(s)` and `0`, and `0` is in each half-plane
  since `det(γ'(t), -γ(t)) = det(γ(t), γ'(t)) > 0`; a point `x ∉` region is `c γ(t)` with `c > 1`
  (`IsStarCurve.sc_exists_smul_eq`), which the half-plane at `t` excludes.
-/

@[expose] public section

namespace PlaneCurve

open MeasureTheory Real

variable {γ : ℝ → Fin 2 → ℝ} {T : ℝ}

private lemma scc_sq_pos (h : IsStarCurve γ T) (t : ℝ) : 0 < γ t 0 ^ 2 + γ t 1 ^ 2 := by
  have hc := h.cross_pos t
  by_contra hle
  have h0 : γ t 0 = 0 := by nlinarith [sq_nonneg (γ t 0), sq_nonneg (γ t 1)]
  have h1 : γ t 1 = 0 := by nlinarith [sq_nonneg (γ t 0), sq_nonneg (γ t 1)]
  simp [cross, h0, h1] at hc

/-- The polar angle `φ = arg γ(0) + sc_angle γ` of a star curve, in polar form: it is continuous
and turns by `2π` over a period. -/
private lemma scc_polar_angle (h : IsStarCurve γ T) :
    ∃ φ : ℝ → ℝ, Continuous φ ∧ (∀ t, φ (t + T) = φ t + 2 * π) ∧
      ∀ t, γ t 0 = √(γ t 0 ^ 2 + γ t 1 ^ 2) * Real.cos (φ t) ∧
        γ t 1 = √(γ t 0 ^ 2 + γ t 1 ^ 2) * Real.sin (φ t) := by
  refine ⟨fun t => Complex.arg (sc_toC (γ 0)) + sc_angle γ t,
    continuous_const.add h.sc_continuous_angle, fun t => ?_, fun t => ?_⟩
  · simp only [h.sc_angle_add_period, h.sc_angle_period]
    ring
  · have hz := h.sc_toC_eq t
    have hnorm : √(γ t 0 ^ 2 + γ t 1 ^ 2) = ‖sc_toC (γ 0)‖ * Real.exp (sc_log γ t).re := by
      rw [← Complex.norm_exp, ← norm_mul, ← hz, Complex.norm_def, Complex.normSq_apply,
        sc_toC_re, sc_toC_im]
      ring_nf
    rw [hnorm]
    constructor
    · rw [← sc_toC_re (γ t), hz, Complex.mul_re, Complex.exp_re, Complex.exp_im,
        ← Complex.norm_mul_cos_arg (sc_toC (γ 0)), ← Complex.norm_mul_sin_arg (sc_toC (γ 0)),
        Real.cos_add]
      simp only [sc_angle]
      ring
    · rw [← sc_toC_im (γ t), hz, Complex.mul_im, Complex.exp_re, Complex.exp_im,
        ← Complex.norm_mul_cos_arg (sc_toC (γ 0)), ← Complex.norm_mul_sin_arg (sc_toC (γ 0)),
        Real.sin_add]
      simp only [sc_angle]
      ring

private lemma scc_deriv_sq_pos (h : IsStarCurve γ T) (t : ℝ) :
    0 < deriv γ t 0 ^ 2 + deriv γ t 1 ^ 2 := by
  have hc := h.cross_pos t
  by_contra hle
  have h0 : deriv γ t 0 = 0 := by nlinarith [sq_nonneg (deriv γ t 0), sq_nonneg (deriv γ t 1)]
  have h1 : deriv γ t 1 = 0 := by nlinarith [sq_nonneg (deriv γ t 0), sq_nonneg (deriv γ t 1)]
  simp [cross, h0, h1] at hc

/-- **Tangent angle of a star curve.** The direction of `γ'` has a continuous lift `ψ = φ + α`,
where `α ∈ (0, π)` is the angle from `γ` to `γ'`; it turns by `2π` over a period. -/
private lemma scc_tangent_angle (h : IsStarCurve γ T) {φ : ℝ → ℝ} (hcont : Continuous φ)
    (hφT : ∀ t, φ (t + T) = φ t + 2 * π)
    (hpolar : ∀ t, γ t 0 = √(γ t 0 ^ 2 + γ t 1 ^ 2) * Real.cos (φ t) ∧
        γ t 1 = √(γ t 0 ^ 2 + γ t 1 ^ 2) * Real.sin (φ t)) :
    ∃ ψ : ℝ → ℝ, Continuous ψ ∧ (∀ t, ψ (t + T) = ψ t + 2 * π) ∧
      ∀ t, deriv γ t 0 = √(deriv γ t 0 ^ 2 + deriv γ t 1 ^ 2) * Real.cos (ψ t) ∧
        deriv γ t 1 = √(deriv γ t 0 ^ 2 + deriv γ t 1 ^ 2) * Real.sin (ψ t) := by
  set v := deriv γ with hv
  have hvc : Continuous v := h.contDiff.continuous_deriv_one
  set σ : ℝ → ℝ := fun t => √(v t 0 ^ 2 + v t 1 ^ 2) with hσ
  have hσpos : ∀ t, 0 < σ t := fun t => Real.sqrt_pos.2 (scc_deriv_sq_pos h t)
  have hσsq : ∀ t, σ t ^ 2 = v t 0 ^ 2 + v t 1 ^ 2 := fun t =>
    Real.sq_sqrt (scc_deriv_sq_pos h t).le
  have hσc : Continuous σ := by
    have : Continuous fun t => v t 0 := (continuous_apply 0).comp hvc
    have : Continuous fun t => v t 1 := (continuous_apply 1).comp hvc
    fun_prop
  set c : ℝ → ℝ := fun t =>
    (Real.cos (φ t) * v t 0 + Real.sin (φ t) * v t 1) / σ t with hc
  set s : ℝ → ℝ := fun t =>
    (Real.cos (φ t) * v t 1 - Real.sin (φ t) * v t 0) / σ t with hs
  have hspos : ∀ t, 0 < s t := by
    intro t
    have hcr := h.cross_pos t
    have hr := Real.sqrt_pos.2 (scc_sq_pos h t)
    have e0 := (hpolar t).1
    have e1 := (hpolar t).2
    set r := √(γ t 0 ^ 2 + γ t 1 ^ 2)
    simp only [cross] at hcr
    refine div_pos ?_ (hσpos t)
    have : 0 < r * (Real.cos (φ t) * v t 1 - Real.sin (φ t) * v t 0) := by
      have : γ t 0 * deriv γ t 1 - γ t 1 * deriv γ t 0 =
          r * (Real.cos (φ t) * v t 1 - Real.sin (φ t) * v t 0) := by
        simp only [v]
        linear_combination (deriv γ t 1) * e0 - (deriv γ t 0) * e1
      linarith
    exact pos_of_mul_pos_right this hr.le
  have hcs : ∀ t, c t ^ 2 + s t ^ 2 = 1 := by
    intro t
    have hσ0 := (hσpos t).ne'
    simp only [c, s]
    field_simp
    rw [hσsq]
    nlinarith [Real.sin_sq_add_cos_sq (φ t)]
  have hcabs : ∀ t, -1 ≤ c t ∧ c t ≤ 1 := by
    intro t
    have := hcs t
    constructor <;> nlinarith [sq_nonneg (s t), sq_nonneg (c t + 1), sq_nonneg (c t - 1)]
  refine ⟨fun t => φ t + Real.arccos (c t), ?_, fun t => ?_, fun t => ?_⟩
  · have : Continuous c := by
      have : Continuous fun t => v t 0 := (continuous_apply 0).comp hvc
      have : Continuous fun t => v t 1 := (continuous_apply 1).comp hvc
      exact Continuous.div (by fun_prop) hσc (fun t => (hσpos t).ne')
    exact hcont.add (Real.continuous_arccos.comp this)
  · have : c (t + T) = c t := by
      simp only [c, σ, hφT, Real.cos_add_two_pi, Real.sin_add_two_pi, v,
        h.sc_deriv_periodic]
    simp only [this, hφT]
    ring
  · have hca := Real.cos_arccos (hcabs t).1 (hcabs t).2
    have hsa : Real.sin (Real.arccos (c t)) = s t := by
      rw [Real.sin_arccos, show 1 - c t ^ 2 = s t ^ 2 by linarith [hcs t]]
      exact Real.sqrt_sq (hspos t).le
    have hσ0 := (hσpos t).ne'
    change v t 0 = σ t * _ ∧ v t 1 = σ t * _
    rw [Real.cos_add, Real.sin_add, hca, hsa]
    simp only [c, s]
    constructor
    · have : σ t * (Real.cos (φ t) * c t - Real.sin (φ t) * s t) =
          Real.cos (φ t) * (Real.cos (φ t) * v t 0 + Real.sin (φ t) * v t 1) -
            Real.sin (φ t) * (Real.cos (φ t) * v t 1 - Real.sin (φ t) * v t 0) := by
        simp only [c, s]; field_simp
      rw [this]
      linear_combination (-(v t 0)) * Real.sin_sq_add_cos_sq (φ t)
    · have : σ t * (Real.sin (φ t) * c t + Real.cos (φ t) * s t) =
          Real.sin (φ t) * (Real.cos (φ t) * v t 0 + Real.sin (φ t) * v t 1) +
            Real.cos (φ t) * (Real.cos (φ t) * v t 1 - Real.sin (φ t) * v t 0) := by
        simp only [c, s]; field_simp
      rw [this]
      linear_combination (-(v t 1)) * Real.sin_sq_add_cos_sq (φ t)

/-- `cross` of two vectors in polar form. -/
private lemma scc_cross_polar {a b : Fin 2 → ℝ} {σa σb ψa ψb : ℝ}
    (ha : a 0 = σa * Real.cos ψa ∧ a 1 = σa * Real.sin ψa)
    (hb : b 0 = σb * Real.cos ψb ∧ b 1 = σb * Real.sin ψb) :
    cross a b = σa * σb * Real.sin (ψb - ψa) := by
  simp only [cross, ha.1, ha.2, hb.1, hb.2, Real.sin_sub]
  ring

/-- A continuous function that does not decrease just to the right of each point is
monotone. -/
private lemma scc_monotone_of_local {f : ℝ → ℝ} (hf : Continuous f)
    (hloc : ∀ x, ∃ δ > 0, ∀ y ∈ Set.Ioo x (x + δ), f x ≤ f y) : Monotone f := by
  intro a b hab
  have hsub : Set.Icc a b ⊆ {y | f a ≤ f y} := by
    apply IsClosed.Icc_subset_of_forall_mem_nhdsWithin
    · exact (isClosed_le continuous_const hf).inter isClosed_Icc
    · exact (le_rfl : f a ≤ f a)
    · intro x hx
      obtain ⟨δ, hδ, hδx⟩ := hloc x
      filter_upwards [Ioo_mem_nhdsGT (by linarith : x < x + δ)] with y hy
      exact le_trans hx.1 (hδx y hy)
  exact hsub ⟨hab, le_rfl⟩

/-- `x ↦ x⁻¹` is Lipschitz on `[m, ∞)` for `m > 0`. -/
private lemma scc_lipschitzOnWith_inv {m : ℝ} (hm : 0 < m) :
    LipschitzOnWith (Real.toNNReal (1 / m ^ 2)) (fun x : ℝ => x⁻¹) (Set.Ici m) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hx0 : 0 < x := lt_of_lt_of_le hm hx
  have hy0 : 0 < y := lt_of_lt_of_le hm hy
  rw [Real.coe_toNNReal _ (by positivity), Real.dist_eq, Real.dist_eq,
    inv_sub_inv hx0.ne' hy0.ne', abs_div, abs_of_pos (mul_pos hx0 hy0), abs_sub_comm]
  rw [div_le_iff₀ (mul_pos hx0 hy0)]
  have hxy : m ^ 2 ≤ x * y := by nlinarith [Set.mem_Ici.1 hx, Set.mem_Ici.1 hy]
  calc |x - y| = 1 / m ^ 2 * |x - y| * m ^ 2 := by field_simp
    _ ≤ 1 / m ^ 2 * |x - y| * (x * y) := by gcongr

/-- **The tangent angle does not decrease.** If `v` is Lipschitz, turns counterclockwise
(`cross(v, v') ≥ 0` a.e.) and `ψ` is a continuous lift of its direction, then `ψ` is monotone. -/
private lemma scc_monotone_angle {v : ℝ → Fin 2 → ℝ} {C : NNReal} (hv : LipschitzWith C v)
    (hcurv : ∀ᵐ t, 0 ≤ cross (v t) (deriv v t)) {ψ σ : ℝ → ℝ} (hψ : Continuous ψ)
    (hσ : ∀ t, 0 < σ t)
    (hrep : ∀ t, v t 0 = σ t * Real.cos (ψ t) ∧ v t 1 = σ t * Real.sin (ψ t)) :
    Monotone ψ := by
  apply scc_monotone_of_local hψ
  intro x
  set w := v x with hw
  set N : ℝ → ℝ := fun s => w 0 * v s 1 - w 1 * v s 0 with hN
  set D : ℝ → ℝ := fun s => w 0 * v s 0 + w 1 * v s 1 with hD
  have hv0 : LipschitzWith C fun s => v s 0 := by
    have := (LipschitzWith.eval (α := fun _ : Fin 2 => ℝ) 0).comp hv
    rwa [one_mul] at this
  have hv1 : LipschitzWith C fun s => v s 1 := by
    have := (LipschitzWith.eval (α := fun _ : Fin 2 => ℝ) 1).comp hv
    rwa [one_mul] at this
  have hDc : Continuous D := by
    have := hv0.continuous; have := hv1.continuous; fun_prop
  have hDx : 0 < D x := by
    have h1 : D x = σ x ^ 2 := by
      simp only [D, w, (hrep x).1, (hrep x).2]
      nlinarith [Real.sin_sq_add_cos_sq (ψ x)]
    rw [h1]; exact pow_pos (hσ x) 2
  -- a neighbourhood where `D > D x / 2` and `ψ` moves by less than `π`
  have hev : ∀ᶠ y in nhds x, D x / 2 < D y ∧ |ψ y - ψ x| < π := by
    refine (hDc.continuousAt.eventually (lt_mem_nhds (by linarith : D x / 2 < D x))).and ?_
    have : ContinuousAt (fun y => |ψ y - ψ x|) x := by fun_prop
    have h0 : (fun y => |ψ y - ψ x|) x < π := by simp [Real.pi_pos]
    exact this.eventually (gt_mem_nhds h0)
  obtain ⟨δ, hδ, hδx⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨δ, hδ, fun y hy => ?_⟩
  have hnear : ∀ s ∈ Set.Icc x y, D x / 2 < D s := by
    intro s hs
    refine (hδx ?_).1
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hs.1, hs.2, hy.1, hy.2]
  have hxy : x ≤ y := hy.1.le
  -- `q = N / D` is absolutely continuous on `[x, y]`
  have hvAC : ∀ i : Fin 2, AbsolutelyContinuousOnInterval (fun s => v s i) x y := by
    intro i
    have : LipschitzWith C fun s => v s i := by
      have := (LipschitzWith.eval (α := fun _ : Fin 2 => ℝ) i).comp hv
      rwa [one_mul] at this
    exact this.lipschitzOnWith.absolutelyContinuousOnInterval
  have hNAC : AbsolutelyContinuousOnInterval N x y :=
    ((hvAC 1).const_mul (w 0)).fun_sub ((hvAC 0).const_mul (w 1))
  have hDAC : AbsolutelyContinuousOnInterval D x y :=
    ((hvAC 0).const_mul (w 0)).fun_add ((hvAC 1).const_mul (w 1))
  have hDinvAC : AbsolutelyContinuousOnInterval (fun s => (D s)⁻¹) x y := by
    refine (scc_lipschitzOnWith_inv (by linarith : 0 < D x / 2)).comp_absolutelyContinuousOnInterval
      ?_ hDAC
    intro s hs
    rw [Set.uIcc_of_le hxy] at hs
    exact (hnear s hs).le
  have hqAC : AbsolutelyContinuousOnInterval (fun s => N s * (D s)⁻¹) x y :=
    hNAC.fun_mul hDinvAC
  have hFTC := hqAC.integral_deriv_eq_sub
  have hint : 0 ≤ ∫ s in x..y, deriv (fun s => N s * (D s)⁻¹) s := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict hxy
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hv.ae_differentiableAt_real, hcurv] with s hs1 hs2 hs3
    have hds := hs1.hasDerivAt
    have hd0 : HasDerivAt (fun s => v s 0) (deriv v s 0) s := hasDerivAt_pi.1 hds 0
    have hd1 : HasDerivAt (fun s => v s 1) (deriv v s 1) s := hasDerivAt_pi.1 hds 1
    have hDs := hnear s hs3
    have hDs0 : D s ≠ 0 := by linarith
    have hNd : HasDerivAt N (w 0 * deriv v s 1 - w 1 * deriv v s 0) s :=
      (hd1.const_mul _).sub (hd0.const_mul _)
    have hDd : HasDerivAt D (w 0 * deriv v s 0 + w 1 * deriv v s 1) s :=
      (hd0.const_mul _).add (hd1.const_mul _)
    have hq : HasDerivAt (fun s => N s * (D s)⁻¹) _ s := hNd.mul (hDd.inv hDs0)
    rw [Pi.zero_apply, hq.deriv]
    have key : (w 0 * deriv v s 1 - w 1 * deriv v s 0) * (D s)⁻¹ +
        N s * (-(w 0 * deriv v s 0 + w 1 * deriv v s 1) / D s ^ 2) =
        (w 0 ^ 2 + w 1 ^ 2) * cross (v s) (deriv v s) / D s ^ 2 := by
      simp only [N, D, cross]
      field_simp
      ring
    rw [key]
    positivity
  have hqx : N x * (D x)⁻¹ = 0 := by
    have : N x = 0 := by simp only [N, w]; ring
    rw [this, zero_mul]
  rw [hqx, sub_zero] at hFTC
  have hNy : 0 ≤ N y := by
    have hDy : 0 < D y := by linarith [hnear y ⟨hxy, le_rfl⟩]
    have := hFTC ▸ hint
    have h2 : 0 ≤ N y * (D y)⁻¹ := this
    exact (mul_nonneg_iff_of_pos_right (inv_pos.2 hDy)).1 h2
  have hcr : N y = σ x * σ y * Real.sin (ψ y - ψ x) := scc_cross_polar (hrep x) (hrep y)
  have habs := (hδx (y := y)
    (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hy.1, hy.2])).2
  by_contra hlt
  push Not at hlt
  have hneg : Real.sin (ψ y - ψ x) < 0 :=
    Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith [(abs_lt.1 habs).1])
  have : σ x * σ y * Real.sin (ψ y - ψ x) < 0 :=
    mul_neg_of_pos_of_neg (mul_pos (hσ x) (hσ y)) hneg
  linarith

/-- **The tangent lines support the curve.** If the tangent angle `ψ` does not decrease and turns
by `2π` over a period, the curve lies to the left of each of its tangent lines. -/
private lemma scc_support (h : IsStarCurve γ T) {ψ : ℝ → ℝ} (hψ : Monotone ψ)
    (hψT : ∀ t, ψ (t + T) = ψ t + 2 * π)
    (hrep : ∀ t, deriv γ t 0 = √(deriv γ t 0 ^ 2 + deriv γ t 1 ^ 2) * Real.cos (ψ t) ∧
        deriv γ t 1 = √(deriv γ t 0 ^ 2 + deriv γ t 1 ^ 2) * Real.sin (ψ t)) (t₀ t : ℝ) :
    0 ≤ cross (deriv γ t₀) (γ t - γ t₀) := by
  have hT := h.pos
  have hσ : ∀ t, 0 < √(deriv γ t 0 ^ 2 + deriv γ t 1 ^ 2) := fun t =>
    Real.sqrt_pos.2 (scc_deriv_sq_pos h t)
  set F : ℝ → ℝ := fun s => cross (deriv γ t₀) (γ s - γ t₀) with hFdef
  have hdγ : ∀ s, HasDerivAt γ (deriv γ s) s := fun s =>
    ((h.contDiff.differentiable one_ne_zero) s).hasDerivAt
  have hF : ∀ s, HasDerivAt F (cross (deriv γ t₀) (deriv γ s)) s := by
    intro s
    have hd0 := hasDerivAt_pi.1 (hdγ s) 0
    have hd1 := hasDerivAt_pi.1 (hdγ s) 1
    have := ((hd1.sub_const (γ t₀ 1)).const_mul (deriv γ t₀ 0)).sub
      ((hd0.sub_const (γ t₀ 0)).const_mul (deriv γ t₀ 1))
    convert this using 1
    · funext x; simp [F, cross]
    · simp [cross]
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun s => (hF s).continuousAt
  have hF' : ∀ s, cross (deriv γ t₀) (deriv γ s) =
      √(deriv γ t₀ 0 ^ 2 + deriv γ t₀ 1 ^ 2) * √(deriv γ s 0 ^ 2 + deriv γ s 1 ^ 2) *
        Real.sin (ψ s - ψ t₀) := fun s => scc_cross_polar (hrep t₀) (hrep s)
  have hmem := toIcoMod_mem_Ico hT t₀ t
  have hγt : γ (toIcoMod hT t₀ t) = γ t := by
    rw [← self_sub_toIcoDiv_zsmul]
    exact (show Function.Periodic γ T from h.periodic).sub_zsmul_eq _
  have hFt : F t = F (toIcoMod hT t₀ t) := by simp only [F, hγt]
  rw [show cross (deriv γ t₀) (γ t - γ t₀) = F t from rfl, hFt]
  set t' := toIcoMod hT t₀ t
  have hψ1 : ψ t₀ ≤ ψ t' := hψ hmem.1
  rcases le_total (ψ t' - ψ t₀) π with hle | hge
  · have hmono : MonotoneOn F (Set.Icc t₀ t') := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) hFc.continuousOn
        (fun s _ => (hF s).differentiableAt.differentiableWithinAt)
      intro s hs
      rw [interior_Icc] at hs
      rw [(hF s).deriv, hF']
      have h1 : ψ t₀ ≤ ψ s := hψ hs.1.le
      have h2 : ψ s ≤ ψ t' := hψ hs.2.le
      exact mul_nonneg (mul_pos (hσ _) (hσ _)).le
        (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))
    have := hmono ⟨le_rfl, hmem.1⟩ ⟨hmem.1, le_rfl⟩ hmem.1
    have hF0 : F t₀ = 0 := by simp [F, cross]
    linarith
  · have hanti : AntitoneOn F (Set.Icc t' (t₀ + T)) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hFc.continuousOn
        (fun s _ => (hF s).differentiableAt.differentiableWithinAt)
      intro s hs
      rw [interior_Icc] at hs
      rw [(hF s).deriv, hF']
      have h1 : ψ t' ≤ ψ s := hψ hs.1.le
      have h2 : ψ s ≤ ψ t₀ + 2 * π := by rw [← hψT]; exact hψ hs.2.le
      have hsin : Real.sin (ψ s - ψ t₀) ≤ 0 := by
        have := Real.sin_nonneg_of_nonneg_of_le_pi (x := ψ s - ψ t₀ - π) (by linarith)
          (by linarith)
        rw [Real.sin_sub_pi] at this
        linarith
      exact mul_nonpos_of_nonneg_of_nonpos (mul_pos (hσ _) (hσ _)).le hsin
    have := hanti ⟨le_rfl, hmem.2.le⟩ ⟨hmem.2.le, le_rfl⟩ hmem.2.le
    have hFT : F (t₀ + T) = 0 := by simp [F, h.periodic, cross]
    linarith

/-- **Local convexity implies convexity.** If the tangent of a star-shaped closed curve turns
counterclockwise (`γ'` Lipschitz, `det(γ', γ'') ≥ 0` almost everywhere), the region it bounds is
convex. -/
theorem IsStarCurve.convex_radialHull (h : IsStarCurve γ T) (hLip : ∃ C, LipschitzWith C (deriv γ))
    (hcurv : ∀ᵐ t, 0 ≤ cross (deriv γ t) (deriv (deriv γ) t)) : Convex ℝ (radialHull γ 0 T) := by
  obtain ⟨C, hC⟩ := hLip
  obtain ⟨φ, hφc, hφT, hpolar⟩ := scc_polar_angle h
  obtain ⟨ψ, hψc, hψT, hrep⟩ := scc_tangent_angle h hφc hφT hpolar
  have hψmono : Monotone ψ := scc_monotone_angle hC hcurv hψc
    (fun t => Real.sqrt_pos.2 (scc_deriv_sq_pos h t)) hrep
  have hsupp := scc_support h hψmono hψT hrep
  -- the region is the intersection of the half-planes bounded by the tangent lines
  have heq : radialHull γ 0 T = ⋂ t, {x | 0 ≤ cross (deriv γ t) (x - γ t)} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨s, -, r, hr, rfl⟩ t
      have h1 := hsupp t s
      have h2 := h.cross_pos t
      have : cross (deriv γ t) (r • γ s - γ t) =
          r * cross (deriv γ t) (γ s - γ t) + (1 - r) * cross (γ t) (deriv γ t) := by
        simp only [cross, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [this]
      exact add_nonneg (mul_nonneg hr.1 h1) (mul_nonneg (by linarith [hr.2]) h2.le)
    · intro hx
      by_cases hx0 : x = 0
      · exact ⟨0, ⟨le_rfl, h.pos.le⟩, 0, ⟨le_rfl, zero_le_one⟩, by simp [hx0]⟩
      obtain ⟨t, ht, c, hc, hγt⟩ := h.sc_exists_smul_eq hx0
      have hxc : x = c⁻¹ • γ t := by rw [hγt, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
      by_cases hc1 : c⁻¹ ≤ 1
      · exact ⟨t, ht, c⁻¹, ⟨inv_nonneg.2 hc.le, hc1⟩, hxc⟩
      · exfalso
        push Not at hc1
        have h1 := hx t
        have h2 := h.cross_pos t
        have : cross (deriv γ t) (x - γ t) = -((c⁻¹ - 1) * cross (γ t) (deriv γ t)) := by
          rw [hxc]
          simp only [cross, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          ring
        rw [this] at h1
        have : 0 < (c⁻¹ - 1) * cross (γ t) (deriv γ t) := mul_pos (by linarith) h2
        linarith
  rw [heq]
  refine convex_iInter fun t => ?_
  intro a ha b hb p q hp hq hpq
  simp only [Set.mem_ofPred_eq] at ha hb ⊢
  have : cross (deriv γ t) (p • a + q • b - γ t) =
      p * cross (deriv γ t) (a - γ t) + q * cross (deriv γ t) (b - γ t) := by
    simp only [cross, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (deriv γ t 0 * γ t 1 - deriv γ t 1 * γ t 0) * hpq
  rw [this]
  exact add_nonneg (mul_nonneg hp ha) (mul_nonneg hq hb)

end PlaneCurve
