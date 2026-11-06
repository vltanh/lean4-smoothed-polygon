module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Algebra.Order.ToIntervalMod
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Regions bounded by star-shaped closed curves in the plane

A closed `C¹` curve `γ` in `ℝ² = Fin 2 → ℝ` that turns counterclockwise about the origin
(`det(γ, γ') > 0`) and is simple over one period `T` bounds the region swept by the segments from
the origin to its points, `radialHull γ 0 T`. This file proves:

* `IsStarCurve.volume_radialHull`: the area of the region is `½ ∫₀ᵀ det(γ, γ') dt`; this is
  Green's formula `area = ½ ∮ x dy - y dx` for such regions, proved by the change of variables
  `(r, t) ↦ r γ(t)`, injective on `(0, 1] × [0, T)` with Jacobian `r det(γ, γ')`;
* `IsStarCurve.frontier_radialHull`: its boundary is the curve;
* `IsStarCurve.isCompact_radialHull`, `IsStarCurve.zero_mem_interior_radialHull`.

## Proof

Seen in `ℂ`, the curve is `z(t) = z(0) exp(L(t))` with `L(t) = ∫₀ᵗ z'/z`, so `φ = Im L` is a
continuous polar angle; it is strictly increasing because `Im (z'/z) = det(γ, γ')/|γ|² > 0`.
Periodicity gives `φ(T) = 2πn` with `n ≥ 1`. If `n ≥ 2`, the map `σ` sending `t` to the next time
the curve is back on the same ray (`φ(σ t) = φ t + 2π`) is continuous with `t < σ t < t + T`,
so by injectivity `|γ(σ t)| ≠ |γ(t)|` for all `t`; this contradicts the intermediate value theorem
at a minimum and a maximum of `|γ|`. Hence `φ(T) = 2π`: each ray from the origin meets the curve
exactly once per period (`IsStarCurve.sc_eq_of_smul_eq`, `IsStarCurve.sc_exists_smul_eq`).
Interior points `r γ(t)`, `0 < r < 1`, come from the inverse function theorem for
`(r, t) ↦ r γ(t)`.

Convexity is in `Basic.Analysis.Convex.StarCurveConvex`.
-/

@[expose] public section

namespace PlaneCurve

open MeasureTheory

/-- `cross v w = v₀ w₁ - v₁ w₀`, the determinant of the `2 × 2` matrix with columns `v, w`. -/
def cross (v w : Fin 2 → ℝ) : ℝ := v 0 * w 1 - v 1 * w 0

/-- The region swept by the segments from the origin to the points `γ(t)`, `t ∈ [a, b]`. -/
def radialHull (γ : ℝ → Fin 2 → ℝ) (a b : ℝ) : Set (Fin 2 → ℝ) :=
  {x | ∃ t ∈ Set.Icc a b, ∃ r ∈ Set.Icc (0 : ℝ) 1, x = r • γ t}

/-- A star-shaped closed curve with period `T`: `C¹`, `T`-periodic, injective on one period, and
turning counterclockwise about the origin. -/
structure IsStarCurve (γ : ℝ → Fin 2 → ℝ) (T : ℝ) : Prop where
  pos : 0 < T
  contDiff : ContDiff ℝ 1 γ
  periodic : ∀ t, γ (t + T) = γ t
  injOn : Set.InjOn γ (Set.Ico 0 T)
  cross_pos : ∀ t, 0 < cross (γ t) (deriv γ t)

variable {γ : ℝ → Fin 2 → ℝ} {T : ℝ}

open Set Filter Topology Real

/-! ### A continuous polar angle -/

/-- The point `v` of the plane as the complex number `v₀ + v₁ i`. -/
noncomputable def sc_toC (v : Fin 2 → ℝ) : ℂ := (v 0 : ℂ) + (v 1 : ℂ) * Complex.I

@[simp] lemma sc_toC_re (v : Fin 2 → ℝ) : (sc_toC v).re = v 0 := by simp [sc_toC]

@[simp] lemma sc_toC_im (v : Fin 2 → ℝ) : (sc_toC v).im = v 1 := by simp [sc_toC]

lemma sc_toC_smul (c : ℝ) (v : Fin 2 → ℝ) : sc_toC (c • v) = c * sc_toC v := by
  apply Complex.ext <;> simp

lemma sc_toC_injective : Function.Injective sc_toC := by
  intro v w hvw
  have h0 := congrArg Complex.re hvw
  have h1 := congrArg Complex.im hvw
  simp only [sc_toC_re, sc_toC_im] at h0 h1
  funext i
  fin_cases i
  · exact h0
  · exact h1

lemma sc_toC_eq_zero {v : Fin 2 → ℝ} : sc_toC v = 0 ↔ v = 0 := by
  constructor
  · intro hv
    apply sc_toC_injective
    rw [hv]
    apply Complex.ext <;> simp
  · rintro rfl
    apply Complex.ext <;> simp

lemma sc_continuous_toC : Continuous sc_toC := by
  unfold sc_toC
  fun_prop

lemma IsStarCurve.sc_ne_zero (h : IsStarCurve γ T) (t : ℝ) : γ t ≠ 0 := by
  intro h0
  have := h.cross_pos t
  rw [h0] at this
  simp [cross] at this

lemma IsStarCurve.sc_toC_ne_zero (h : IsStarCurve γ T) (t : ℝ) : sc_toC (γ t) ≠ 0 :=
  fun h0 => h.sc_ne_zero t (sc_toC_eq_zero.1 h0)

lemma IsStarCurve.sc_hasDerivAt (h : IsStarCurve γ T) (t : ℝ) : HasDerivAt γ (deriv γ t) t :=
  ((h.contDiff.differentiable one_ne_zero) t).hasDerivAt

lemma IsStarCurve.sc_continuous (h : IsStarCurve γ T) : Continuous γ := h.contDiff.continuous

lemma IsStarCurve.sc_continuous_deriv (h : IsStarCurve γ T) : Continuous (deriv γ) :=
  h.contDiff.continuous_deriv le_rfl

lemma IsStarCurve.sc_hasDerivAt_toC (h : IsStarCurve γ T) (t : ℝ) :
    HasDerivAt (fun s => sc_toC (γ s)) (sc_toC (deriv γ t)) t := by
  have h0 := (hasDerivAt_pi.1 (h.sc_hasDerivAt t) 0).ofReal_comp
  have h1 := (hasDerivAt_pi.1 (h.sc_hasDerivAt t) 1).ofReal_comp
  exact h0.add (h1.mul_const Complex.I)

lemma IsStarCurve.sc_deriv_periodic (h : IsStarCurve γ T) (t : ℝ) :
    deriv γ (t + T) = deriv γ t := by
  rw [← deriv_comp_add_const]
  congr 1
  funext s
  exact h.periodic s

/-- The logarithmic derivative `z'/z` of the curve seen in `ℂ`. -/
noncomputable def sc_logDeriv (γ : ℝ → Fin 2 → ℝ) (t : ℝ) : ℂ :=
  sc_toC (deriv γ t) / sc_toC (γ t)

/-- A continuous logarithm of the curve seen in `ℂ`, relative to its value at `0`. -/
noncomputable def sc_log (γ : ℝ → Fin 2 → ℝ) (t : ℝ) : ℂ := ∫ s in (0 : ℝ)..t, sc_logDeriv γ s

/-- A continuous polar angle of the curve, relative to its value at `0`. -/
noncomputable def sc_angle (γ : ℝ → Fin 2 → ℝ) (t : ℝ) : ℝ := (sc_log γ t).im

lemma IsStarCurve.sc_continuous_logDeriv (h : IsStarCurve γ T) : Continuous (sc_logDeriv γ) := by
  unfold sc_logDeriv
  exact (sc_continuous_toC.comp h.sc_continuous_deriv).div (sc_continuous_toC.comp h.sc_continuous)
    h.sc_toC_ne_zero

lemma IsStarCurve.sc_hasDerivAt_log (h : IsStarCurve γ T) (t : ℝ) :
    HasDerivAt (sc_log γ) (sc_logDeriv γ t) t :=
  (h.sc_continuous_logDeriv.integral_hasStrictDerivAt 0 t).hasDerivAt

lemma sc_log_zero : sc_log γ 0 = 0 := by simp [sc_log]

lemma sc_angle_zero : sc_angle γ 0 = 0 := by simp [sc_angle, sc_log_zero]

/-- The curve in `ℂ` is `z(0) exp(L(t))`. -/
lemma IsStarCurve.sc_toC_eq (h : IsStarCurve γ T) (t : ℝ) :
    sc_toC (γ t) = sc_toC (γ 0) * Complex.exp (sc_log γ t) := by
  have hd : ∀ s, HasDerivAt (fun s => sc_toC (γ s) * Complex.exp (-sc_log γ s)) 0 s := by
    intro s
    have := (h.sc_hasDerivAt_toC s).mul (h.sc_hasDerivAt_log s).neg.cexp
    convert this using 1
    have := h.sc_toC_ne_zero s
    simp only [sc_logDeriv]
    field_simp
    ring
  have hc := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv)
    t 0
  simp only [sc_log_zero, neg_zero, Complex.exp_zero, mul_one] at hc
  rw [← hc, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]

lemma sc_logDeriv_im (t : ℝ) :
    (sc_logDeriv γ t).im = cross (γ t) (deriv γ t) / Complex.normSq (sc_toC (γ t)) := by
  simp only [sc_logDeriv, Complex.div_im, sc_toC_re, sc_toC_im, cross]
  ring

lemma IsStarCurve.sc_logDeriv_im_pos (h : IsStarCurve γ T) (t : ℝ) :
    0 < (sc_logDeriv γ t).im := by
  rw [sc_logDeriv_im]
  exact div_pos (h.cross_pos t) (Complex.normSq_pos.2 (h.sc_toC_ne_zero t))

lemma IsStarCurve.sc_hasDerivAt_angle (h : IsStarCurve γ T) (t : ℝ) :
    HasDerivAt (sc_angle γ) (sc_logDeriv γ t).im t := by
  exact (Complex.imCLM.hasFDerivAt (x := sc_log γ t)).comp_hasDerivAt t (h.sc_hasDerivAt_log t)

lemma IsStarCurve.sc_continuous_angle (h : IsStarCurve γ T) : Continuous (sc_angle γ) :=
  continuous_iff_continuousAt.2 fun t => (h.sc_hasDerivAt_angle t).continuousAt

lemma IsStarCurve.sc_strictMono_angle (h : IsStarCurve γ T) : StrictMono (sc_angle γ) :=
  strictMono_of_deriv_pos fun t => by
    rw [(h.sc_hasDerivAt_angle t).deriv]
    exact h.sc_logDeriv_im_pos t

lemma IsStarCurve.sc_log_add_period (h : IsStarCurve γ T) (t : ℝ) :
    sc_log γ (t + T) = sc_log γ t + sc_log γ T := by
  have hd : ∀ s, HasDerivAt (fun s => sc_log γ (s + T) - sc_log γ s) 0 s := by
    intro s
    have := (HasDerivAt.comp_add_const s T (h.sc_hasDerivAt_log (s + T))).sub
      (h.sc_hasDerivAt_log s)
    convert this using 1
    simp [sc_logDeriv, h.periodic, h.sc_deriv_periodic]
  have hc := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv)
    t 0
  simp only [zero_add, sc_log_zero, sub_zero] at hc
  rw [← hc]
  ring

lemma IsStarCurve.sc_angle_add_period (h : IsStarCurve γ T) (t : ℝ) :
    sc_angle γ (t + T) = sc_angle γ t + sc_angle γ T := by
  simp [sc_angle, h.sc_log_add_period t]

/-- Two points of the curve on the same ray from the origin have angles differing by a multiple
of `2π`. -/
lemma IsStarCurve.sc_angle_of_sameDir (h : IsStarCurve γ T) {t u c : ℝ} (hc : 0 < c)
    (hz : sc_toC (γ u) = c * sc_toC (γ t)) :
    ∃ k : ℤ, sc_angle γ u = sc_angle γ t + k * (2 * π) := by
  rw [h.sc_toC_eq u, h.sc_toC_eq t, ← Real.exp_log hc, Complex.ofReal_exp, mul_left_comm,
    ← Complex.exp_add] at hz
  have hz := mul_left_cancel₀ (h.sc_toC_ne_zero 0) hz
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 hz
  refine ⟨n, ?_⟩
  have := congrArg Complex.im hn
  simp only [sc_angle]
  simp at this
  linarith

/-- Points of the curve whose angles differ by a multiple of `2π` are on the same ray. -/
lemma IsStarCurve.sc_sameDir_of_angle (h : IsStarCurve γ T) {t u : ℝ} {k : ℤ}
    (hk : sc_angle γ u = sc_angle γ t + k * (2 * π)) :
    ∃ c : ℝ, 0 < c ∧ sc_toC (γ u) = c * sc_toC (γ t) := by
  refine ⟨Real.exp ((sc_log γ u).re - (sc_log γ t).re), Real.exp_pos _, ?_⟩
  rw [h.sc_toC_eq u, h.sc_toC_eq t, Complex.ofReal_exp, mul_left_comm, ← Complex.exp_add]
  congr 1
  apply Complex.exp_eq_exp_iff_exists_int.2 ⟨k, ?_⟩
  apply Complex.ext
  · simp
  · simp only [sc_angle] at hk
    simp [hk]

/-- The angle grows by `2πn` over a period, for some integer `n ≥ 1`. -/
lemma IsStarCurve.sc_exists_angle_period (h : IsStarCurve γ T) :
    ∃ n : ℤ, 0 < n ∧ sc_angle γ T = n * (2 * π) := by
  have hz : Complex.exp (sc_log γ T) = 1 := by
    have h1 := h.sc_toC_eq T
    have hp : γ T = γ 0 := by simpa using h.periodic 0
    rw [hp] at h1
    exact mul_left_cancel₀ (h.sc_toC_ne_zero 0) (h1.symm.trans (mul_one _).symm)
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 hz
  have hT : sc_angle γ T = n * (2 * π) := by
    simp only [sc_angle, hn]
    simp
  refine ⟨n, ?_, hT⟩
  have hpos : 0 < sc_angle γ T := by
    rw [← sc_angle_zero (γ := γ)]
    exact h.sc_strictMono_angle h.pos
  by_contra hn0
  have : (n : ℝ) ≤ 0 := by exact_mod_cast not_lt.1 hn0
  nlinarith [pi_pos]

/-- **The curve turns exactly once.** The angle grows by `2π` over a period: a curve turning
`n ≥ 2` times about the origin meets itself. -/
lemma IsStarCurve.sc_angle_period (h : IsStarCurve γ T) : sc_angle γ T = 2 * π := by
  obtain ⟨n, hn, hT⟩ := h.sc_exists_angle_period
  suffices n = 1 by rw [hT, this]; simp
  by_contra hn1
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (show (2 : ℤ) ≤ n by omega)
  have hmono := h.sc_strictMono_angle
  have hcont := h.sc_continuous_angle
  have hadd := h.sc_angle_add_period
  have hk : ∀ (k : ℕ) (t : ℝ), sc_angle γ (t + k * T) = sc_angle γ t + k * sc_angle γ T := by
    intro k
    induction k with
    | zero => intro t; simp
    | succ k ih =>
      intro t
      push_cast
      rw [show t + (k + 1) * T = (t + k * T) + T by ring, hadd, ih]
      ring
  have hφT : 0 < sc_angle γ T := by rw [hT]; positivity
  have hsurj : Function.Surjective (sc_angle γ) := by
    refine hcont.surjective (tendsto_atTop_atTop_of_monotone hmono.monotone fun b => ?_)
      (tendsto_atBot_atBot_of_monotone hmono.monotone fun b => ?_)
    · obtain ⟨k, hk'⟩ := exists_nat_ge (b / sc_angle γ T)
      refine ⟨0 + k * T, ?_⟩
      rw [hk, sc_angle_zero]
      have := (div_le_iff₀ hφT).1 hk'
      linarith
    · obtain ⟨k, hk'⟩ := exists_nat_ge (-b / sc_angle γ T)
      refine ⟨-(k * T), ?_⟩
      have h1 := hk k (-(k * T))
      rw [neg_add_cancel, sc_angle_zero] at h1
      have := (div_le_iff₀ hφT).1 hk'
      linarith
  let e := StrictMono.orderIsoOfSurjective (sc_angle γ) hmono hsurj
  let σ : ℝ → ℝ := fun t => e.symm (sc_angle γ t + 2 * π)
  have hσ : ∀ t, sc_angle γ (σ t) = sc_angle γ t + 2 * π := fun t =>
    StrictMono.orderIsoOfSurjective_self_symm_apply (sc_angle γ) hmono hsurj _
  have hσc : Continuous σ := e.symm.continuous.comp (hcont.add continuous_const)
  have hσ1 : ∀ t, t < σ t := fun t => hmono.lt_iff_lt.1 (by rw [hσ]; linarith [pi_pos])
  have hσ2 : ∀ t, σ t < t + T := fun t =>
    hmono.lt_iff_lt.1 (by rw [hσ, hadd, hT]; nlinarith [pi_pos])
  have hdir : ∀ t, ∃ c : ℝ, 0 < c ∧ sc_toC (γ (σ t)) = c * sc_toC (γ t) := fun t =>
    h.sc_sameDir_of_angle (k := 1) (by rw [hσ]; simp)
  have hne : ∀ t, γ (σ t) ≠ γ t := by
    intro t heq
    have hp : Function.Periodic γ T := h.periodic
    have ha : ∀ s, γ (toIcoMod h.pos 0 s) = γ s := fun s => by
      rw [← self_sub_toIcoDiv_zsmul]
      exact hp.sub_zsmul_eq _
    have := h.injOn (toIcoMod_mem_Ico' h.pos (σ t)) (toIcoMod_mem_Ico' h.pos t)
      (by rw [ha, ha, heq])
    obtain ⟨m, hm⟩ := (toIcoMod_eq_toIcoMod h.pos).1 this
    have h1 := hσ1 t
    have h2 := hσ2 t
    have hT0 := h.pos
    rw [zsmul_eq_mul] at hm
    have a : (m : ℝ) < 0 := by nlinarith
    have b : (-1 : ℝ) < m := by nlinarith
    have a' : m < 0 := by exact_mod_cast a
    have b' : -1 < m := by exact_mod_cast b
    omega
  have hnorm : ∀ t, ‖sc_toC (γ (σ t))‖ ≠ ‖sc_toC (γ t)‖ := by
    intro t heq
    obtain ⟨c, hc, hz⟩ := hdir t
    rw [hz, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.le] at heq
    have hpos := norm_pos_iff.2 (h.sc_toC_ne_zero t)
    have hc1 : c = 1 := by
      have : (c - 1) * ‖sc_toC (γ t)‖ = 0 := by linarith
      rcases mul_eq_zero.1 this with h0 | h0
      · linarith
      · linarith
    apply hne t
    apply sc_toC_injective
    rw [hz, hc1]
    simp
  have hcz : Continuous fun t => ‖sc_toC (γ t)‖ := (sc_continuous_toC.comp h.sc_continuous).norm
  obtain ⟨t₁, -, ht₁⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 h.pos.le) hcz.continuousOn
  obtain ⟨t₂, -, ht₂⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 h.pos.le) hcz.continuousOn
  have hmin : ∀ s, ‖sc_toC (γ t₁)‖ ≤ ‖sc_toC (γ s)‖ := fun s => by
    obtain ⟨a, ha, hga⟩ := (show Function.Periodic γ T from h.periodic).exists_mem_Ico₀ h.pos s
    rw [hga]
    exact isMinOn_iff.1 ht₁ a (Ico_subset_Icc_self ha)
  have hmax : ∀ s, ‖sc_toC (γ s)‖ ≤ ‖sc_toC (γ t₂)‖ := fun s => by
    obtain ⟨a, ha, hga⟩ := (show Function.Periodic γ T from h.periodic).exists_mem_Ico₀ h.pos s
    rw [hga]
    exact isMaxOn_iff.1 ht₂ a (Ico_subset_Icc_self ha)
  have hD : Continuous fun t => ‖sc_toC (γ (σ t))‖ - ‖sc_toC (γ t)‖ := (hcz.comp hσc).sub hcz
  obtain ⟨t, ht⟩ := intermediate_value_univ t₂ t₁ hD
    (show (0 : ℝ) ∈ Icc _ _ from ⟨by linarith [hmax (σ t₂)], by linarith [hmin (σ t₁)]⟩)
  exact hnorm t (sub_eq_zero.1 ht)

lemma IsStarCurve.sc_angle_mem_Ico (h : IsStarCurve γ T) {t : ℝ} (ht : t ∈ Ico 0 T) :
    sc_angle γ t ∈ Ico 0 (2 * π) := by
  rw [← h.sc_angle_period, ← sc_angle_zero (γ := γ)]
  exact ⟨h.sc_strictMono_angle.monotone ht.1, h.sc_strictMono_angle ht.2⟩

/-- **Each ray from the origin meets the curve at most once per period.** -/
theorem IsStarCurve.sc_eq_of_smul_eq (h : IsStarCurve γ T) {t u c : ℝ} (ht : t ∈ Ico 0 T)
    (hu : u ∈ Ico 0 T) (hc : 0 < c) (hγ : γ u = c • γ t) : u = t := by
  obtain ⟨k, hk⟩ := h.sc_angle_of_sameDir (t := t) (u := u) hc (by rw [hγ, sc_toC_smul])
  have h1 := h.sc_angle_mem_Ico ht
  have h2 := h.sc_angle_mem_Ico hu
  have hk0 : k = 0 := by
    have a : (k : ℝ) < 1 := by nlinarith [pi_pos, h1.1, h1.2, h2.1, h2.2]
    have b : (-1 : ℝ) < k := by nlinarith [pi_pos, h1.1, h1.2, h2.1, h2.2]
    have a' : k < 1 := by exact_mod_cast a
    have b' : -1 < k := by exact_mod_cast b
    omega
  rw [hk0] at hk
  simp only [Int.cast_zero, zero_mul, add_zero] at hk
  exact h.sc_strictMono_angle.injective hk

/-- **Each ray from the origin meets the curve.** -/
theorem IsStarCurve.sc_exists_smul_eq (h : IsStarCurve γ T) {w : Fin 2 → ℝ} (hw : w ≠ 0) :
    ∃ t ∈ Icc 0 T, ∃ c : ℝ, 0 < c ∧ γ t = c • w := by
  set v : ℂ := sc_toC w / sc_toC (γ 0) with hv
  have hw0 : sc_toC w ≠ 0 := fun h0 => hw (sc_toC_eq_zero.1 h0)
  have hv0 : v ≠ 0 := div_ne_zero hw0 (h.sc_toC_ne_zero 0)
  have hsI : toIcoMod two_pi_pos 0 (Complex.arg v) ∈ Icc (sc_angle γ 0) (sc_angle γ T) := by
    rw [sc_angle_zero, h.sc_angle_period]
    have := toIcoMod_mem_Ico' two_pi_pos (Complex.arg v)
    exact ⟨this.1, this.2.le⟩
  obtain ⟨t, ht, hts⟩ := intermediate_value_Icc h.pos.le h.sc_continuous_angle.continuousOn hsI
  have hvn : (0 : ℝ) < ‖v‖ := norm_pos_iff.2 hv0
  refine ⟨t, ht, Real.exp (sc_log γ t).re / ‖v‖, div_pos (Real.exp_pos _) hvn, ?_⟩
  apply sc_toC_injective
  rw [sc_toC_smul, h.sc_toC_eq t]
  have hexp : Complex.exp (sc_log γ t) =
      Real.exp (sc_log γ t).re * Complex.exp (Complex.arg v * Complex.I) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    apply Complex.exp_eq_exp_iff_exists_int.2 ⟨-toIcoDiv two_pi_pos 0 (Complex.arg v), ?_⟩
    have h2 := self_sub_toIcoDiv_zsmul two_pi_pos 0 (Complex.arg v)
    rw [← hts, zsmul_eq_mul] at h2
    apply Complex.ext
    · simp
    · simp only [sc_angle] at h2
      simp
      linarith
  rw [hexp]
  have h3 := Complex.norm_mul_exp_arg_mul_I v
  have h4 : sc_toC w = v * sc_toC (γ 0) := by
    rw [hv, div_mul_cancel₀ _ (h.sc_toC_ne_zero 0)]
  have : (‖v‖ : ℂ) ≠ 0 := by exact_mod_cast hvn.ne'
  have h5 : Complex.exp (Complex.arg v * Complex.I) = v / ‖v‖ := by
    rw [eq_div_iff this, mul_comm]
    exact h3
  rw [h5, h4]
  push_cast
  field_simp

/-! ### The map `(r, t) ↦ r γ(t)` -/

/-- The map `(r, t) ↦ r γ(t)`, on `ℝ² = Fin 2 → ℝ`. -/
def sc_F (γ : ℝ → Fin 2 → ℝ) (p : Fin 2 → ℝ) : Fin 2 → ℝ := p 0 • γ (p 1)

/-- The derivative of `sc_F`. -/
noncomputable def sc_F' (γ : ℝ → Fin 2 → ℝ) (p : Fin 2 → ℝ) : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  p 0 • (ContinuousLinearMap.proj 1).smulRight (deriv γ (p 1)) +
    (ContinuousLinearMap.proj 0).smulRight (γ (p 1))

lemma IsStarCurve.sc_hasFDerivAt_F (h : IsStarCurve γ T) (p : Fin 2 → ℝ) :
    HasFDerivAt (sc_F γ) (sc_F' γ p) p := by
  have h0 : HasFDerivAt (fun q : Fin 2 → ℝ => q 0)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0) p :=
    hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) 0 p
  have h1 : HasFDerivAt (fun q : Fin 2 → ℝ => γ (q 1))
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).smulRight
        (deriv γ (p 1))) p := by
    have := (h.sc_hasDerivAt (p 1)).hasFDerivAt.comp p
      (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) 1 p)
    refine this.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
    funext i
    simp
  exact h0.smul h1

lemma sc_det_F' (p : Fin 2 → ℝ) :
    (sc_F' γ p).det = p 0 * cross (γ (p 1)) (deriv γ (p 1)) := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix', Matrix.det_fin_two]
  simp [LinearMap.toMatrix'_apply, sc_F', cross]
  ring

lemma IsStarCurve.sc_injOn_F (h : IsStarCurve γ T) :
    InjOn (sc_F γ) {p | p 0 ∈ Ioc 0 1 ∧ p 1 ∈ Ico 0 T} := by
  rintro p ⟨hp0, hp1⟩ q ⟨hq0, hq1⟩ hpq
  simp only [sc_F] at hpq
  have h1 : q 1 = p 1 := h.sc_eq_of_smul_eq hp1 hq1 (c := p 0 / q 0) (div_pos hp0.1 hq0.1) (by
    rw [div_eq_inv_mul, mul_smul, hpq, smul_smul, inv_mul_cancel₀ hq0.1.ne', one_smul])
  rw [h1] at hpq
  have h0 : p 0 = q 0 := smul_left_injective ℝ (h.sc_ne_zero (p 1)) hpq
  funext i
  fin_cases i
  · exact h0
  · exact h1.symm

lemma IsStarCurve.sc_continuous_cross (h : IsStarCurve γ T) :
    Continuous fun t => cross (γ t) (deriv γ t) := by
  have := h.sc_continuous
  have := h.sc_continuous_deriv
  unfold cross
  fun_prop

/-! ### The region -/

/-- **Green's formula for star-shaped regions.** The area of the region bounded by a star-shaped
closed curve is `½ ∫₀ᵀ det(γ, γ') dt`. -/
theorem IsStarCurve.volume_radialHull (h : IsStarCurve γ T) :
    volume (radialHull γ 0 T) =
      ENNReal.ofReal ((1 / 2) * ∫ t in (0 : ℝ)..T, cross (γ t) (deriv γ t)) := by
  set S : Set (Fin 2 → ℝ) := {p | p 0 ∈ Ioc 0 1 ∧ p 1 ∈ Ico 0 T} with hS
  have hSm : MeasurableSet S :=
    (measurableSet_Ioc.preimage (measurable_pi_apply 0)).inter
      (measurableSet_Ico.preimage (measurable_pi_apply 1))
  have hR : radialHull γ 0 T = insert 0 (sc_F γ '' S) := by
    ext x
    constructor
    · rintro ⟨t, ht, r, hr, rfl⟩
      rcases hr.1.eq_or_lt with hr0 | hr0
      · left
        simp [← hr0]
      right
      rcases ht.2.lt_or_eq with htT | htT
      · exact ⟨![r, t], ⟨by simpa using ⟨hr0, hr.2⟩, by simpa using ⟨ht.1, htT⟩⟩, by simp [sc_F]⟩
      · refine ⟨![r, 0], ⟨by simpa using ⟨hr0, hr.2⟩, by simpa using h.pos⟩, ?_⟩
        have : γ 0 = γ T := by simpa using (h.periodic 0).symm
        simp [sc_F, htT, this]
    · rintro (rfl | ⟨p, ⟨hp0, hp1⟩, rfl⟩)
      · exact ⟨0, ⟨le_rfl, h.pos.le⟩, 0, ⟨le_rfl, zero_le_one⟩, by simp⟩
      · exact ⟨p 1, Ico_subset_Icc_self hp1, p 0, Ioc_subset_Icc_self hp0, rfl⟩
  rw [hR, measure_congr (insert_ae_eq_self _ _), ← setLIntegral_one,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSm
      (fun p _ => (h.sc_hasFDerivAt_F p).hasFDerivWithinAt) h.sc_injOn_F]
  simp only [mul_one, sc_det_F']
  have hc : ∀ t, 0 ≤ cross (γ t) (deriv γ t) := fun t => (h.cross_pos t).le
  rw [setLIntegral_congr_fun hSm (g := fun p => ENNReal.ofReal (p 0) *
      ENNReal.ofReal (cross (γ (p 1)) (deriv γ (p 1)))) (fun p hp => by
      rw [abs_of_nonneg (mul_nonneg hp.1.1.le (hc _)), ENNReal.ofReal_mul hp.1.1.le])]
  have hS' : S = MeasurableEquiv.finTwoArrow ⁻¹' (Ioc (0 : ℝ) 1 ×ˢ Ico 0 T) := by
    ext p
    simp [S, MeasurableEquiv.finTwoArrow]
  have key : ∫⁻ p in S, ENNReal.ofReal (p 0) * ENNReal.ofReal (cross (γ (p 1)) (deriv γ (p 1))) =
      ∫⁻ q in Ioc (0 : ℝ) 1 ×ˢ Ico 0 T,
        ENNReal.ofReal q.1 * ENNReal.ofReal (cross (γ q.2) (deriv γ q.2)) := by
    rw [hS']
    exact (volume_preserving_finTwoArrow ℝ).setLIntegral_comp_preimage_emb
      MeasurableEquiv.finTwoArrow.measurableEmbedding
      (fun q : ℝ × ℝ => ENNReal.ofReal q.1 * ENNReal.ofReal (cross (γ q.2) (deriv γ q.2))) _
  rw [key, Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod_mul (f := fun r => ENNReal.ofReal r)
      (g := fun t => ENNReal.ofReal (cross (γ t) (deriv γ t)))
      ENNReal.measurable_ofReal.aemeasurable
      (ENNReal.measurable_ofReal.comp h.sc_continuous_cross.measurable).aemeasurable]
  have h1 : ∫⁻ r in Ioc (0 : ℝ) 1, ENNReal.ofReal r = ENNReal.ofReal (1 / 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal, ← intervalIntegral.integral_of_le zero_le_one,
      integral_id]
    · norm_num
    · exact (continuous_id.integrableOn_Icc).mono_set Ioc_subset_Icc_self
    · exact ae_restrict_of_forall_mem measurableSet_Ioc
        (fun r hr => (show (0 : ℝ) ≤ r from hr.1.le))
  have h2 : ∫⁻ t in Ico 0 T, ENNReal.ofReal (cross (γ t) (deriv γ t)) =
      ENNReal.ofReal (∫ t in (0 : ℝ)..T, cross (γ t) (deriv γ t)) := by
    rw [Measure.restrict_congr_set Ico_ae_eq_Ioc, ← ofReal_integral_eq_lintegral_ofReal,
      intervalIntegral.integral_of_le h.pos.le]
    · exact (h.sc_continuous_cross.integrableOn_Icc).mono_set Ioc_subset_Icc_self
    · exact Filter.Eventually.of_forall (fun t => hc t)
  rw [h1, h2, ← ENNReal.ofReal_mul (by norm_num)]

theorem IsStarCurve.isCompact_radialHull (h : IsStarCurve γ T) : IsCompact (radialHull γ 0 T) := by
  have : radialHull γ 0 T = (fun q : ℝ × ℝ => q.2 • γ q.1) '' (Icc 0 T ×ˢ Icc 0 1) := by
    ext x
    simp only [radialHull, mem_ofPred_eq, mem_image, mem_prod, Prod.exists]
    constructor
    · rintro ⟨t, ht, r, hr, rfl⟩
      exact ⟨t, r, ⟨ht, hr⟩, rfl⟩
    · rintro ⟨t, r, ⟨ht, hr⟩, rfl⟩
      exact ⟨t, ht, r, hr, rfl⟩
  rw [this]
  exact (isCompact_Icc.prod isCompact_Icc).image
    (continuous_snd.smul (h.sc_continuous.comp continuous_fst))

theorem IsStarCurve.zero_mem_interior_radialHull (h : IsStarCurve γ T) :
    (0 : Fin 2 → ℝ) ∈ interior (radialHull γ 0 T) := by
  have hcz : Continuous fun t => ‖sc_toC (γ t)‖ := (sc_continuous_toC.comp h.sc_continuous).norm
  obtain ⟨t₀, -, ht₀⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 h.pos.le) hcz.continuousOn
  set m := ‖sc_toC (γ t₀)‖
  have hm : 0 < m := norm_pos_iff.2 (h.sc_toC_ne_zero t₀)
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  refine ⟨m / 2, half_pos hm, fun x hx => ?_⟩
  rw [mem_ball_zero_iff] at hx
  by_cases hx0 : x = 0
  · exact ⟨0, ⟨le_rfl, h.pos.le⟩, 0, ⟨le_rfl, zero_le_one⟩, by simp [hx0]⟩
  obtain ⟨t, ht, c, hc, hγ⟩ := h.sc_exists_smul_eq hx0
  refine ⟨t, ht, c⁻¹, ⟨inv_nonneg.2 hc.le, ?_⟩, ?_⟩
  · have h1 : m ≤ ‖sc_toC (γ t)‖ := isMinOn_iff.1 ht₀ t ht
    rw [hγ, sc_toC_smul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.le] at h1
    have h2 : ‖sc_toC x‖ ≤ |x 0| + |x 1| := by
      simpa using Complex.norm_le_abs_re_add_abs_im (sc_toC x)
    have h3 : |x 0| < m / 2 := by
      rw [← Real.norm_eq_abs]
      exact (norm_le_pi_norm x 0).trans_lt hx
    have h4 : |x 1| < m / 2 := by
      rw [← Real.norm_eq_abs]
      exact (norm_le_pi_norm x 1).trans_lt hx
    have h5 := norm_nonneg (sc_toC x)
    rw [inv_le_one₀ hc]
    nlinarith
  · rw [hγ, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]

lemma IsStarCurve.sc_smul_mem_interior (h : IsStarCurve γ T) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (t : ℝ) : r • γ t ∈ interior (radialHull γ 0 T) := by
  rcases hr0.eq_or_lt with rfl | hr0
  · simpa using h.zero_mem_interior_radialHull
  rw [mem_interior_iff_mem_nhds]
  set p : Fin 2 → ℝ := ![r, t]
  have hFp : sc_F γ p = r • γ t := by simp [sc_F, p]
  have hstrict : HasStrictFDerivAt (sc_F γ) (sc_F' γ p) p := by
    have hC : ContDiff ℝ 1 (sc_F γ) := by
      unfold sc_F
      have := h.contDiff
      fun_prop
    have := (hC.contDiffAt (x := p)).hasStrictFDerivAt one_ne_zero
    rwa [(h.sc_hasFDerivAt_F p).fderiv] at this
  have hsurj : (sc_F' γ p).range = ⊤ := by
    have hdet : LinearMap.det ((sc_F' γ p) : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) ≠ 0 := by
      have := sc_det_F' (γ := γ) p
      rw [ContinuousLinearMap.det] at this
      rw [this]
      exact mul_ne_zero (by simp [p, hr0.ne']) (h.cross_pos _).ne'
    exact (LinearMap.isUnit_iff_range_eq_top _).1
      ((LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet))
  rw [← hFp, ← hstrict.map_nhds_eq_of_surj hsurj]
  apply Filter.mem_map.2
  have hopen : IsOpen {q : Fin 2 → ℝ | q 0 ∈ Ioo 0 1} := isOpen_Ioo.preimage (continuous_apply 0)
  refine Filter.mem_of_superset (hopen.mem_nhds ⟨by simpa [p] using hr0, by simpa [p] using hr1⟩)
    (fun q hq => ?_)
  obtain ⟨a, ha, hga⟩ := (show Function.Periodic γ T from h.periodic).exists_mem_Ico₀ h.pos (q 1)
  exact ⟨a, Ico_subset_Icc_self ha, q 0, ⟨hq.1.le, hq.2.le⟩, by simp [sc_F, hga]⟩

/-- The boundary of the region is the curve. -/
theorem IsStarCurve.frontier_radialHull (h : IsStarCurve γ T) :
    frontier (radialHull γ 0 T) = γ '' Set.Ico 0 T := by
  have hclosed := h.isCompact_radialHull.isClosed
  rw [frontier, hclosed.closure_eq]
  ext x
  constructor
  · rintro ⟨⟨t, ht, r, hr, rfl⟩, hint⟩
    rcases hr.2.lt_or_eq with hr1 | rfl
    · exact absurd (h.sc_smul_mem_interior hr.1 hr1 t) hint
    rw [one_smul]
    rcases ht.2.lt_or_eq with htT | rfl
    · exact ⟨t, ⟨ht.1, htT⟩, rfl⟩
    · exact ⟨0, ⟨le_rfl, h.pos⟩, by simpa using (h.periodic 0).symm⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨⟨t, Ico_subset_Icc_self ht, 1, ⟨zero_le_one, le_rfl⟩, (one_smul _ _).symm⟩,
      fun hint => ?_⟩
    rw [mem_interior_iff_mem_nhds] at hint
    have hlim : Tendsto (fun ε : ℝ => (1 + ε) • γ t) (𝓝[>] 0) (𝓝 (γ t)) := by
      have hc : Continuous (fun ε : ℝ => (1 + ε) • γ t) := by fun_prop
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    obtain ⟨ε, ⟨u, hu, r, hr, heq⟩, hε⟩ := ((hlim.eventually hint).and self_mem_nhdsWithin).exists
    have hε : 0 < ε := hε
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [zero_smul, smul_eq_zero] at heq
      rcases heq with h1 | h1
      · linarith
      · exact h.sc_ne_zero t h1
    obtain ⟨u', hu', hgu⟩ : ∃ u' ∈ Ico 0 T, γ u = γ u' := by
      rcases hu.2.lt_or_eq with huT | rfl
      · exact ⟨u, ⟨hu.1, huT⟩, rfl⟩
      · exact ⟨0, ⟨le_rfl, h.pos⟩, by simpa using h.periodic 0⟩
    rw [hgu] at heq
    have hrpos : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hr0)
    have hut := h.sc_eq_of_smul_eq ht hu' (c := (1 + ε) / r) (div_pos (by linarith) hrpos) (by
      rw [div_eq_inv_mul, mul_smul, heq, smul_smul, inv_mul_cancel₀ hr0, one_smul])
    rw [hut] at heq
    have := smul_left_injective ℝ (h.sc_ne_zero t) heq
    linarith [hr.2]

end PlaneCurve
