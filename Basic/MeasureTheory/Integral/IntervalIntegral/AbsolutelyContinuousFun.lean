module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Absolutely continuous functions in integral form

The fundamental theorem of calculus for absolutely continuous functions, in the integral form
`f t = f a + ∫ₐᵗ v` in which Carathéodory solutions of differential equations are written.

## Main statements

* `AbsolutelyContinuousOnInterval.eq_add_integral_of_ae_hasDerivAt`: a function absolutely
  continuous on `[a, b]` with derivative `v` almost everywhere on `(a, b)` is `f a + ∫ₐᵗ v`
  there, and `v` is interval integrable;
* `absolutelyContinuousOnInterval_of_eq_add_integral`: conversely, `f a + ∫ₐᵗ v` with `v`
  interval integrable is absolutely continuous on `[a, b]`;
* `ae_hasDerivAt_of_eq_add_integral`: a function `x₀ + ∫_cᵗ v` has derivative `v` at almost
  every point of `(a, b)` (Lebesgue's differentiation theorem), with values in a Banach space;
* `continuousOn_Icc_of_eq_add_integral`: and it is continuous on `[a, b]`;
* `AbsolutelyContinuousOnInterval.of_dist_le`: absolute continuity by comparison of increments;
* `absolutelyContinuousOnInterval_comp_of_eq_add_integral`: a function `C¹` near a curve
  `x(a) + ∫ₐᵗ v` in a normed space is absolutely continuous along it.
-/

@[expose] public section

open Set MeasureTheory Filter
open scoped Interval NNReal

variable {f v : ℝ → ℝ} {a b : ℝ}

/-- **Fundamental theorem of calculus for absolutely continuous functions**, in integral form: if
`f` is absolutely continuous on `[a, b]` and has derivative `v t` at almost every `t ∈ (a, b)`,
then `v` is interval integrable on `[a, b]` and `f t = f a + ∫ s in a..t, v s` for `t ∈ [a, b]`. -/
theorem AbsolutelyContinuousOnInterval.eq_add_integral_of_ae_hasDerivAt (hab : a ≤ b)
    (hf : AbsolutelyContinuousOnInterval f a b) (hd : ∀ᵐ t, t ∈ Ioo a b → HasDerivAt f (v t) t) :
    IntervalIntegrable v volume a b ∧ ∀ t ∈ Icc a b, f t = f a + ∫ s in a..t, v s := by
  have hae : ∀ᵐ t, t ∈ Ioc a b → deriv f t = v t := by
    have hb : ∀ᵐ t : ℝ, t ≠ b := by simp [ae_iff, measure_singleton]
    filter_upwards [hd, hb] with t ht htb htI
    exact (ht ⟨htI.1, lt_of_le_of_ne htI.2 htb⟩).deriv
  have hint : IntervalIntegrable v volume a b := by
    refine (hf.intervalIntegrable_deriv).congr_ae ?_
    rw [uIoc_of_le hab]
    exact (ae_restrict_iff' measurableSet_Ioc).2 hae
  refine ⟨hint, fun t ht ↦ ?_⟩
  have hsub : uIcc a t ⊆ uIcc a b := by
    rw [uIcc_of_le ht.1, uIcc_of_le hab]; exact Icc_subset_Icc_right ht.2
  have h := (hf.mono hsub).integral_deriv_eq_sub
  have h' : ∫ s in a..t, v s = ∫ s in a..t, deriv f s := by
    refine intervalIntegral.integral_congr_ae ?_
    rw [uIoc_of_le ht.1]
    filter_upwards [hae] with s hs hst
    exact (hs ⟨hst.1, hst.2.trans ht.2⟩).symm
  rw [h', h]
  ring

/-- A function of the form `f t = f a + ∫ s in a..t, v s` on `[a, b]`, with `v` interval
integrable, is absolutely continuous on `[a, b]`. -/
theorem absolutelyContinuousOnInterval_of_eq_add_integral (hab : a ≤ b)
    (hv : IntervalIntegrable v volume a b) (hf : ∀ t ∈ Icc a b, f t = f a + ∫ s in a..t, v s) :
    AbsolutelyContinuousOnInterval f a b := by
  have h1 := hv.absolutelyContinuousOnInterval_intervalIntegral (c := a) left_mem_uIcc
  refine ((LipschitzWith.const (f a)).lipschitzOnWith.absolutelyContinuousOnInterval.fun_add
    h1).congr fun t ht ↦ ?_
  rw [uIcc_of_le hab] at ht
  exact (hf t ht).symm

/-- A function of the form `x t = x₀ + ∫ s in c..t, v s` on `[a, b]`, with `v` interval integrable
and `c ∈ [a, b]`, has derivative `v t` at almost every `t ∈ (a, b)` (Lebesgue's differentiation
theorem). -/
theorem ae_hasDerivAt_of_eq_add_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {c : ℝ} {x w : ℝ → E} {x₀ : E} (hw : IntervalIntegrable w volume a b)
    (hc : c ∈ Icc a b) (hx : ∀ t ∈ Icc a b, x t = x₀ + ∫ s in c..t, w s) :
    ∀ᵐ t, t ∈ Ioo a b → HasDerivAt x (w t) t := by
  filter_upwards [IntervalIntegrable.ae_hasDerivAt_integral hw] with t ht htI
  have hIcc : Icc a b ⊆ uIcc a b := Icc_subset_uIcc
  have h := (ht (hIcc (Ioo_subset_Icc_self htI)) c (hIcc hc)).const_add x₀
  exact h.congr_of_eventuallyEq (eventually_of_mem (Icc_mem_nhds htI.1 htI.2)
    fun s hs ↦ hx s hs)

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A function of the form `x t = x a + ∫ s in a..t, w s` on `[a, b]`, with `w` interval
integrable, is continuous on `[a, b]`. -/
theorem continuousOn_Icc_of_eq_add_integral (hab : a ≤ b) {x w : ℝ → E}
    (hw : IntervalIntegrable w volume a b) (hx : ∀ t ∈ Icc a b, x t = x a + ∫ s in a..t, w s) :
    ContinuousOn x (Icc a b) := by
  have hc := intervalIntegral.continuousOn_primitive_interval' hw left_mem_uIcc
  rw [uIcc_of_le hab] at hc
  exact (continuousOn_const.add hc).congr hx

/-- **Absolute continuity by comparison of increments**: if
`dist (f s) (f t) ≤ dist (g s) (g t)` for `s, t ∈ [a, b]` and `g` is absolutely continuous on
`[a, b]`, so is `f`. -/
theorem AbsolutelyContinuousOnInterval.of_dist_le {X : Type*} [PseudoMetricSpace X]
    {f : ℝ → X} {g : ℝ → ℝ} (hg : AbsolutelyContinuousOnInterval g a b)
    (h : ∀ s ∈ uIcc a b, ∀ t ∈ uIcc a b, dist (f s) (f t) ≤ dist (g s) (g t)) :
    AbsolutelyContinuousOnInterval f a b := by
  apply squeeze_zero' ?_ ?_ hg
  · exact .of_forall fun _ ↦ Finset.sum_nonneg fun _ _ ↦ dist_nonneg
  rw [Filter.eventually_inf_principal]
  filter_upwards with E hE
  exact Finset.sum_le_sum fun i hi ↦ h _ (hE.left i hi).left _ (hE.left i hi).right

/-- If `F` is `C¹` near every point of a curve `x(t) = x(a) + ∫ₐᵗ w` on `[a, b]` (`w` interval
integrable), then `F ∘ x` is absolutely continuous on `[a, b]`: `F` is Lipschitz on the compact
set `x([a, b])`, and `‖x(t) - x(s)‖ ≤ |∫ₛᵗ ‖w‖|`. -/
theorem absolutelyContinuousOnInterval_comp_of_eq_add_integral {F : E → ℝ} (hab : a ≤ b)
    {x w : ℝ → E} (hw : IntervalIntegrable w volume a b)
    (hx : ∀ t ∈ Icc a b, x t = x a + ∫ s in a..t, w s)
    (hF : ∀ t ∈ Icc a b, ContDiffAt ℝ 1 F (x t)) :
    AbsolutelyContinuousOnInterval (fun t ↦ F (x t)) a b := by
  have hxc := continuousOn_Icc_of_eq_add_integral hab hw hx
  have hK : IsCompact (x '' Icc a b) := isCompact_Icc.image_of_continuousOn hxc
  have hloc : LocallyLipschitzOn (x '' Icc a b) F := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨K, U, hU, hKU⟩ := (hF t ht).exists_lipschitzOnWith
    exact ⟨K, U, nhdsWithin_le_nhds hU, hKU⟩
  obtain ⟨L, hL⟩ := hloc.exists_lipschitzOnWith_of_compact hK
  have hN := (hw.norm.absolutelyContinuousOnInterval_intervalIntegral
    (c := a) left_mem_uIcc).const_mul (L : ℝ)
  refine AbsolutelyContinuousOnInterval.of_dist_le hN fun s hs t ht ↦ ?_
  rw [uIcc_of_le hab] at hs ht
  have hws : IntervalIntegrable w volume a s := hw.mono_set (by
    rw [uIcc_of_le hab, uIcc_of_le hs.1]; exact Icc_subset_Icc_right hs.2)
  have hwt : IntervalIntegrable w volume a t := hw.mono_set (by
    rw [uIcc_of_le hab, uIcc_of_le ht.1]; exact Icc_subset_Icc_right ht.2)
  calc dist (F (x s)) (F (x t)) ≤ L * dist (x s) (x t) :=
        hL.dist_le_mul _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    _ = L * ‖∫ r in t..s, w r‖ := by
        rw [dist_eq_norm, hx s hs, hx t ht, add_sub_add_left_eq_sub,
          intervalIntegral.integral_interval_sub_left hws hwt]
    _ ≤ L * |∫ r in t..s, ‖w r‖| := by
        gcongr; exact intervalIntegral.norm_integral_le_abs_integral_norm
    _ = dist (L * ∫ r in a..s, ‖w r‖) (L * ∫ r in a..t, ‖w r‖) := by
        rw [Real.dist_eq, ← mul_sub, abs_mul, NNReal.abs_eq,
          intervalIntegral.integral_interval_sub_left hws.norm hwt.norm]

end Normed
