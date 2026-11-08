module

public import SmoothedPolygons.Ch8.EdgeProblem
public import SmoothedPolygons.Ch6.MatrixExtremal
import SmoothedPolygons.Ch7.SmoothedPolygon

/-!
# The global minimizer is extremal and edge extremal (Proposition 8.1.3)

Proposition 8.1.3 (`prop:edge-extremal`): the global minimizer of the Reinhardt problem is a
Pontryagin extremal of the Reinhardt control problem, and it is edge extremal (Definition 8.1.2).
The book's proof (TeX 6791–6798) has two sentences:

1. "We have seen that the global minimizer must be extremal": §6.1–§6.2, formalized in Layers 1–2
   as `exists_isPontryaginExtremal_of_isReinhardtMinimizer`.
2. The principle of optimality: on a subinterval where the control lies in an edge of `U_T`, the
   minimizer minimizes the cost among trajectories with the same endpoint conditions whose control
   lies in that edge; hence it is extremal for the edge control problem.

The second sentence needs (REPORT.md, E48): the maximum principle for the edge problem (an
open subset of `ℝ³`, fixed endpoints, free terminal time, integral cost), which is
`External.pontryagin_maximum_principle`; and the principle of optimality made precise. A
competitor of the edge problem with the same endpoints is spliced into the minimizer: its
Reinhardt trajectory is rebuilt from `(s, x, y)` by (8.1.1) (`eqn_g_edge`), so it ends at the
minimizer's `g(d)` and `X(d)`; the rest of the minimizer is shifted in time (free terminal time),
and the cost changes by `3/2` times the change of the edge cost (`edgeCost_identity`). The edge
problem's state space `y > 0`, `|x| < 1/√3` is larger than the star domain, so a competitor could
leave the Reinhardt state space: only competitors uniformly close to the minimizer's edge arc are
spliced (strong local minimality, which is all the maximum principle needs). This is
`l3st_isStrongLocalMinimizer_edgeState`.

## The formal proof

* Regularity (`l3st_isC1On_edgeField`, `l3st_isC1On_edgeCost`): `edgeField` and `edgeCost` are
  jointly `C¹` on the open set where `y ≠ 0` and `-1 + 2√3 x u_e ≠ 0`, which contains
  `edgeDomain × [-½, ½]` (`l3e_edge_denom_neg`).
* The middle arc of the splice. For an admissible pair `(u_e', q')` of the edge problem, the
  coordinates `x', y', s'` are absolutely continuous with derivatives `y'`, `f₂`, `1/y'` almost
  everywhere (Lebesgue's differentiation theorem, `ae_hasDerivAt_of_eq_add_integral`). Where they
  are differentiable, `Φ(x', y')` has derivative `[P, Φ]` with `P = Z_w/⟨Z_w, Φ⟩`,
  `w = (0, ½ + u_e', ½ - u_e')` (Lemma 4.5.2 read backwards, `l3e_hasDerivAt_Φ`), and
  `h(q') = [[1, -x'], [s', 1 - s'x']]` has derivative `h Φ` (`l3e_hasDerivAt_edgeH`): the identity
  `h⁻¹h' = Φ` behind (8.1.1). `C¹` functions of `q'` are absolutely continuous
  (`absolutelyContinuousOnInterval_comp_of_eq_add_integral`), so the fundamental theorem of
  calculus for absolutely continuous functions puts `Φ(x', y')` and `h(q')` in the integral form
  of the state equations (`l3e_IF_Φ`, `l3e_IF_edgeH`);
  conjugation by `Rʲ` (`R⁻ʲ Z_w Rʲ = Z_{rot_j w}`, `l3e_conj_controlMatrix`) and the shift
  `t ↦ t - c` give the arc of the splice (`l3e_IF_XM`, `l3e_IF_gM`).
* The splice (`l3e_splice_isReinhardtAdmissible`): the three pieces are glued in integral form
  (`l3e_IF_sp`); `g` stays in `SL₂(ℝ)` (`det h = 1`) and `X` is a star state (Theorem 4.4.1,
  `poly_isStarState_conj_pow`) because `(x', y')` stays in the star domain.
* The cost of the splice (`l3e_splice_cost`): `⟨J, Φ(x, y)⟩ = -(x² + y² + 1)/y` and the
  integral equations for `x'` and `s'`.
-/

@[expose] public section

namespace SmoothedPolygons

open Set MeasureTheory Filter Topology Matrix

/-! ### Regularity of the edge control system -/

/-- The state space of the edge problem is open. -/
private lemma l3e_isOpen_edgeDomain : IsOpen edgeDomain :=
  (isOpen_lt continuous_const (continuous_apply 1)).inter
    ((isOpen_lt continuous_const (continuous_apply 0)).inter
      (isOpen_lt (continuous_apply 0) continuous_const))

/-- On the state space of the edge problem, with `u_e ∈ [-½, ½]`, the denominator
`-1 + 2√3 x u_e` of `f₂` is negative: `|2√3 x u_e| ≤ √3 |x| < 1`. -/
private lemma l3e_edge_denom_neg {q : Fin 3 → ℝ} (hq : q ∈ edgeDomain) {ue : ℝ}
    (hue : ue ∈ edgeControlSet) : -1 + 2 * √3 * q 0 * ue < 0 :=
  edgeF₂_denom_neg hq.2.1 hq.2.2 hue

/-- The edge control system is `C¹` on its state space in the sense of the maximum principle
(`ControlSystem.IsC1On`, conditions (10.2)–(10.4) of Agrachev–Sachkov): on
`{y > 0, |x| < 1/√3} × [-½, ½]` we have `|2√3 x u_e| < 1`, so the denominator `-1 + 2√3 x u_e`
of `f₂` is negative and `edgeField` is a rational function with nonvanishing denominators there.
-/
private theorem l3st_isC1On_edgeField :
    ControlSystem.IsC1On edgeField edgeDomain edgeControlSet := by
  refine isC1On_of_contDiffOn
    (O := {p : (Fin 3 → ℝ) × ℝ | p.1 1 ≠ 0 ∧ -1 + 2 * √3 * p.1 0 * p.2 ≠ 0}) ?_ ?_ ?_
  · exact (isOpen_ne_fun (by fun_prop) continuous_const).inter
      (isOpen_ne_fun (by fun_prop) continuous_const)
  · rintro ⟨q, ue⟩ ⟨hq, hue⟩
    exact ⟨hq.1.ne', (l3e_edge_denom_neg hq hue).ne⟩
  · rintro ⟨q, ue⟩ ⟨h1, h2⟩
    refine ContDiffAt.contDiffWithinAt (contDiffAt_pi.2 fun k ↦ ?_)
    fin_cases k <;>
      simp only [edgeField, edgeF₂, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons] <;>
      fun_prop (disch := assumption)

/-- The edge cost `x²/y` is `C¹` on the state space of the edge problem. -/
private theorem l3st_isC1On_edgeCost : ControlSystem.IsC1On edgeCost edgeDomain edgeControlSet := by
  refine isC1On_of_contDiffOn (O := {p : (Fin 3 → ℝ) × ℝ | p.1 1 ≠ 0}) ?_ ?_ ?_
  · exact isOpen_ne_fun (by fun_prop) continuous_const
  · rintro ⟨q, ue⟩ ⟨hq, -⟩
    exact hq.1.ne'
  · rintro ⟨q, ue⟩ h1
    refine ContDiffAt.contDiffWithinAt ?_
    simp only [edgeCost]
    fun_prop (disch := assumption)

/-! ### Curves in integral form on an interval -/

/-- `f(t) = f(a) + ∫ₐᵗ v` on `[a, b]`, with `v` integrable on `[a, b]`. -/
private def l3e_IF (f v : ℝ → ℝ) (a b : ℝ) : Prop :=
  IntervalIntegrable v volume a b ∧ ∀ t ∈ Icc a b, f t = f a + ∫ s in a..t, v s

/-- An integral curve on `[0, T]` is in integral form on every `[a, b] ⊆ [0, T]`. -/
private lemma l3e_IF_of_isIntegralCurve {f v : ℝ → Mat2} {T a b : ℝ}
    (hI : IsIntegralCurve f v T) (ha : 0 ≤ a) (hab : a ≤ b) (hbT : b ≤ T) (i j : Fin 2) :
    l3e_IF (fun t ↦ f t i j) (fun t ↦ v t i j) a b := by
  obtain ⟨hint, heq⟩ := hI i j
  have hT : 0 ≤ T := ha.trans (hab.trans hbT)
  refine ⟨hint.mono_set (by rw [uIcc_of_le hab, uIcc_of_le hT]; exact Icc_subset_Icc ha hbT),
    fun t ht ↦ ?_⟩
  have h0a : IntervalIntegrable (fun s ↦ v s i j) volume 0 a := hint.mono_set (by
    rw [uIcc_of_le ha, uIcc_of_le hT]; exact Icc_subset_Icc_right (hab.trans hbT))
  have hat : IntervalIntegrable (fun s ↦ v s i j) volume a t := hint.mono_set (by
    rw [uIcc_of_le ht.1, uIcc_of_le hT]; exact Icc_subset_Icc ha (ht.2.trans hbT))
  beta_reduce
  rw [heq t ⟨ha.trans ht.1, ht.2.trans hbT⟩, heq a ⟨ha, hab.trans hbT⟩, add_assoc,
    intervalIntegral.integral_add_adjacent_intervals h0a hat]

/-- Integral form is kept when `f` is changed off `[a, b]` and `v` off `(a, b)`. -/
private lemma l3e_IF_congr {f v f' v' : ℝ → ℝ} {a b : ℝ} (h : l3e_IF f v a b) (hab : a ≤ b)
    (hf : ∀ t ∈ Icc a b, f t = f' t) (hv : ∀ t ∈ Ioo a b, v t = v' t) : l3e_IF f' v' a b := by
  have hv' : ∀ᵐ t, t ∈ Ioc a b → v t = v' t := by
    filter_upwards [(countable_singleton b).ae_notMem volume] with t htb htI
    exact hv t ⟨htI.1, lt_of_le_of_ne htI.2 htb⟩
  refine ⟨h.1.congr_ae ?_, fun t ht ↦ ?_⟩
  · rw [uIoc_of_le hab]
    exact (ae_restrict_iff' measurableSet_Ioc).2 hv'
  · rw [← hf t ht, ← hf a ⟨le_rfl, hab⟩, h.2 t ht]
    congr 1
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hv'] with s hs hsI
    rw [uIoc_of_le ht.1] at hsI
    exact hs ⟨hsI.1, hsI.2.trans ht.2⟩

/-- Integral form under a time shift. -/
private lemma l3e_IF_shift {f v : ℝ → ℝ} {a b : ℝ} (h : l3e_IF f v a b) (δ : ℝ) {a' b' : ℝ}
    (ha : a' = a + δ) (hb : b' = b + δ) :
    l3e_IF (fun t ↦ f (t - δ)) (fun t ↦ v (t - δ)) a' b' := by
  subst ha hb
  refine ⟨h.1.comp_sub_right δ, fun t ht ↦ ?_⟩
  have e := intervalIntegral.integral_comp_sub_right (f := v) (a := a + δ) (b := t) δ
  simp only [add_sub_cancel_right] at e ⊢
  rw [e, h.2 (t - δ) ⟨by linarith [ht.1], by linarith [ht.2]⟩]

/-- Integral forms on adjacent intervals glue. -/
private lemma l3e_IF_trans {f v : ℝ → ℝ} {a b c : ℝ} (h1 : l3e_IF f v a b)
    (h2 : l3e_IF f v b c) (hab : a ≤ b) (hbc : b ≤ c) : l3e_IF f v a c := by
  refine ⟨h1.1.trans h2.1, fun t ht ↦ ?_⟩
  rcases le_total t b with htb | htb
  · exact h1.2 t ⟨ht.1, htb⟩
  · have hi3 : IntervalIntegrable v volume b t := h2.1.mono_set (by
      rw [uIcc_of_le htb, uIcc_of_le hbc]; exact Icc_subset_Icc_right ht.2)
    rw [h2.2 t ⟨htb, ht.2⟩, h1.2 b ⟨hab, le_rfl⟩, add_assoc,
      intervalIntegral.integral_add_adjacent_intervals h1.1 hi3]

private lemma l3e_IF_add {f v g w : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : l3e_IF f v a b)
    (hg : l3e_IF g w a b) : l3e_IF (fun t ↦ f t + g t) (fun t ↦ v t + w t) a b := by
  refine ⟨hf.1.add hg.1, fun t ht ↦ ?_⟩
  have hsub : uIcc a t ⊆ uIcc a b := by
    rw [uIcc_of_le ht.1, uIcc_of_le hab]; exact Icc_subset_Icc_right ht.2
  beta_reduce
  rw [intervalIntegral.integral_add (hf.1.mono_set hsub) (hg.1.mono_set hsub), hf.2 t ht,
    hg.2 t ht]
  ring

private lemma l3e_IF_const_mul {f v : ℝ → ℝ} {a b : ℝ} (hf : l3e_IF f v a b) (k : ℝ) :
    l3e_IF (fun t ↦ k * f t) (fun t ↦ k * v t) a b := by
  refine ⟨hf.1.const_mul k, fun t ht ↦ ?_⟩
  beta_reduce
  rw [intervalIntegral.integral_const_mul, hf.2 t ht]
  ring

private lemma l3e_mul_apply (A M B : Mat2) (i j : Fin 2) :
    (A * M * B) i j = A i 0 * B 0 j * M 0 0 + A i 0 * B 1 j * M 0 1 + A i 1 * B 0 j * M 1 0 +
      A i 1 * B 1 j * M 1 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- Integral form of a matrix curve is kept under multiplication by constant matrices. -/
private lemma l3e_IF_conj {f v : ℝ → Mat2} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ i j, l3e_IF (fun t ↦ f t i j) (fun t ↦ v t i j) a b) (A B : Mat2) (i j : Fin 2) :
    l3e_IF (fun t ↦ (A * f t * B) i j) (fun t ↦ (A * v t * B) i j) a b := by
  simp only [l3e_mul_apply]
  exact l3e_IF_add hab (l3e_IF_add hab (l3e_IF_add hab (l3e_IF_const_mul (h 0 0) _)
    (l3e_IF_const_mul (h 0 1) _)) (l3e_IF_const_mul (h 1 0) _)) (l3e_IF_const_mul (h 1 1) _)

/-- An absolutely continuous function with derivative `v` almost everywhere is in integral form
(the fundamental theorem of calculus for absolutely continuous functions). -/
private lemma l3e_IF_of_ac {f v : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ᵐ t, t ∈ Ioo a b → HasDerivAt f (v t) t) : l3e_IF f v a b :=
  hf.eq_add_integral_of_ae_hasDerivAt hab hd

/-! ### Rotating a control of the edge `{u₀ = 0}` to the edge `{u_j = 0}` -/

/-- The control `w` rotated `j` times, `(rot_j w)_k = w_{k - j}`, so that
`R⁻ʲ Z_w Rʲ = Z_{rot_j w}`: a control in the edge `{u₀ = 0}` is taken to the edge `{u_j = 0}`. -/
private noncomputable def l3e_rot (j : Fin 3) (w : Fin 3 → ℝ) : Fin 3 → ℝ := fun k ↦ w (k - j)

private lemma l3e_controlMatrix_rot_one (w : Fin 3 → ℝ) :
    R⁻¹ * controlMatrix w * R = controlMatrix (l3e_rot 1 w) := by
  rw [poly_R_inv]
  have h3 : √3 ^ 2 = 3 := poly_sqrt3_sq
  have h3' : √3 ≠ 0 := by positivity
  have e0 : l3e_rot 1 w 0 = w 2 := rfl
  have e1 : l3e_rot 1 w 1 = w 0 := rfl
  have e2 : l3e_rot 1 w 2 = w 1 := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [controlMatrix, R, Matrix.mul_apply, Fin.sum_univ_two, e0, e1, e2] <;> field_simp <;>
    simp only [h3] <;> ring

/-- `R⁻ʲ Z_w Rʲ = Z_{rot_j w}`. -/
private lemma l3e_conj_controlMatrix (j : Fin 3) (w : Fin 3 → ℝ) :
    R⁻¹ ^ (j : ℕ) * controlMatrix w * R ^ (j : ℕ) = controlMatrix (l3e_rot j w) := by
  fin_cases j
  · have : l3e_rot 0 w = w := funext fun k ↦ by simp [l3e_rot]
    simp [this]
  · simpa using l3e_controlMatrix_rot_one w
  · have e : l3e_rot 2 w = l3e_rot 1 (l3e_rot 1 w) := funext fun k ↦ by
      fin_cases k <;> rfl
    simp only [Fin.reduceFinMk, Fin.isValue, e, ← l3e_controlMatrix_rot_one]
    rw [pow_two, pow_two]
    simp only [Matrix.mul_assoc]

private lemma l3e_rot_mem {j : Fin 3} {w : Fin 3 → ℝ} (hw : w ∈ controlSimplex) :
    l3e_rot j w ∈ controlSimplex := by
  obtain ⟨h01, hsum⟩ := hw
  refine ⟨fun i ↦ h01 _, ?_⟩
  fin_cases j
  · simpa [l3e_rot] using hsum
  · have e : l3e_rot 1 w 0 + l3e_rot 1 w 1 + l3e_rot 1 w 2 = w 2 + w 0 + w 1 := rfl
    simp only [Fin.mk_one] at e ⊢
    rw [e]; linarith
  · have e : l3e_rot 2 w 0 + l3e_rot 2 w 1 + l3e_rot 2 w 2 = w 1 + w 2 + w 0 := rfl
    simp only [Fin.reduceFinMk] at e ⊢
    rw [e]; linarith

private lemma l3e_continuous_rot (j : Fin 3) : Continuous (l3e_rot j) :=
  continuous_pi fun _ ↦ continuous_apply _

private lemma l3e_continuous_edgeControl : Continuous edgeControl := by
  refine continuous_pi fun m ↦ ?_
  fin_cases m <;>
    simp only [edgeControl, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] <;>
    fun_prop

/-! ### Derivatives along an edge trajectory -/

/-- The bracket `[P, Φ(x, y)]` for the edge control `w = (0, ½ + u_e, ½ - u_e)`, with
`k = -1 + 2√3 x u_e`. -/
private lemma l3e_bracket_Φ (x y ue : ℝ) (hy : y ≠ 0) (hk : -1 + 2 * √3 * x * ue ≠ 0) :
    controlP (edgeControl ue) (Φ x y) * Φ x y - Φ x y * controlP (edgeControl ue) (Φ x y) =
      !![-1 / (-1 + 2 * √3 * x * ue),
        (2 * x - 2 * √3 * ue * (x ^ 2 + y ^ 2)) / (-1 + 2 * √3 * x * ue);
        -(2 * √3 * ue) / (-1 + 2 * √3 * x * ue), 1 / (-1 + 2 * √3 * x * ue)] := by
  have h3 : √3 ^ 2 = 3 := poly_sqrt3_sq
  have h3' : √3 ≠ 0 := by positivity
  have hD : traceForm (controlMatrix (edgeControl ue)) (Φ x y) =
      2 * (-1 + 2 * √3 * x * ue) / (3 * y) := by
    simp [traceForm, controlMatrix, edgeControl, Φ, Matrix.trace_fin_two]
    field_simp
    linear_combination (-8 * ue * x) * h3
  simp only [controlP, hD]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [controlMatrix, edgeControl, Φ] <;>
    field_simp <;> ring_nf <;> (try simp only [h3]) <;> ring_nf

/-- Where `x' = y` and `y' = f₂(x, y, u_e)`, the matrix `Φ(x, y)` has derivative `[P, Φ(x, y)]`
with `P = Z_w/⟨Z_w, Φ(x, y)⟩`, `w = (0, ½ + u_e, ½ - u_e)` (Lemma 4.5.2 read backwards). -/
private lemma l3e_hasDerivAt_Φ {x y : ℝ → ℝ} {t ue : ℝ} (hy0 : y t ≠ 0)
    (hk : -1 + 2 * √3 * x t * ue ≠ 0)
    (hx : HasDerivAt x (y t) t) (hy : HasDerivAt y (edgeF₂ (x t) (y t) ue) t) (i j : Fin 2) :
    HasDerivAt (fun τ ↦ Φ (x τ) (y τ) i j)
      ((controlP (edgeControl ue) (Φ (x t) (y t)) * Φ (x t) (y t) -
        Φ (x t) (y t) * controlP (edgeControl ue) (Φ (x t) (y t))) i j) t := by
  rw [l3e_bracket_Φ _ _ _ hy0 hk]
  set K := -1 + 2 * √3 * x t * ue with hK
  have hf₂ : edgeF₂ (x t) (y t) ue = 2 * √3 * y t ^ 2 * ue / K := rfl
  fin_cases i <;> fin_cases j
  · refine ((hx.div hy hy0).congr_of_eventuallyEq (.of_forall fun τ ↦ by simp [Φ])).congr_deriv ?_
    simp only [hf₂, Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one]
    field_simp
    rw [hK]; ring
  · refine ((((hx.pow 2).add (hy.pow 2)).neg.div hy hy0).congr_of_eventuallyEq
      (.of_forall fun τ ↦ by simp [Φ])).congr_deriv ?_
    simp only [hf₂, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Pi.neg_apply, Pi.add_apply, Pi.pow_apply]
    field_simp
    rw [hK]; ring
  · refine (((hasDerivAt_const t (1 : ℝ)).div hy hy0).congr_of_eventuallyEq
      (.of_forall fun τ ↦ by simp [Φ])).congr_deriv ?_
    simp only [hf₂, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    field_simp
    ring
  · refine ((hx.neg.div hy hy0).congr_of_eventuallyEq
      (.of_forall fun τ ↦ by simp [Φ])).congr_deriv ?_
    simp only [hf₂, Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Pi.neg_apply]
    field_simp
    rw [hK]; ring

/-- Where `x' = y` and `s' = 1/y`, the matrix `h = [[1, -x], [s, 1 - sx]]` of (8.1.1) has
derivative `h Φ(x, y)` (TeX 6704–6723). -/
private lemma l3e_hasDerivAt_edgeH {Q : ℝ → Fin 3 → ℝ} {t : ℝ} (hy0 : Q t 1 ≠ 0)
    (hx : HasDerivAt (fun τ ↦ Q τ 0) (Q t 1) t) (hs : HasDerivAt (fun τ ↦ Q τ 2) (1 / Q t 1) t)
    (i j : Fin 2) :
    HasDerivAt (fun τ ↦ edgeH (Q τ) i j) ((edgeH (Q t) * Φ (Q t 0) (Q t 1)) i j) t := by
  fin_cases i <;> fin_cases j
  · refine ((hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq
      (.of_forall fun τ ↦ by simp [edgeH])).congr_deriv ?_
    simp [edgeH, Φ, Matrix.mul_apply]
    field_simp
    ring
  · refine (hx.neg.congr_of_eventuallyEq (.of_forall fun τ ↦ by simp [edgeH])).congr_deriv ?_
    simp [edgeH, Φ, Matrix.mul_apply]
    field_simp
    ring
  · refine (hs.congr_of_eventuallyEq (.of_forall fun τ ↦ by simp [edgeH])).congr_deriv ?_
    simp [edgeH, Φ, Matrix.mul_apply]
    field_simp
    ring
  · refine (((hasDerivAt_const t (1 : ℝ)).sub (hs.mul hx)).congr_of_eventuallyEq
      (.of_forall fun τ ↦ by simp [edgeH])).congr_deriv ?_
    simp [edgeH, Φ, Matrix.mul_apply]
    field_simp
    ring

/-! ### An admissible pair of the edge problem as a Reinhardt arc -/

section Competitor

variable {T' : ℝ} {u' : ℝ → ℝ} {Q : ℝ → Fin 3 → ℝ}

/-- The coordinates of an admissible pair of the edge problem are in integral form. -/
private lemma l3e_coord_IF (hT' : 0 ≤ T')
    (hadm : Pontryagin.IsAdmissibleIn edgeField edgeDomain edgeControlSet (Q 0) T' u' Q)
    (k : Fin 3) : l3e_IF (fun t ↦ Q t k) (fun t ↦ edgeField (Q t) (u' t) k) 0 T' := by
  obtain ⟨⟨-, -, -, hv, hx⟩, -⟩ := hadm
  let L : (Fin 3 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj k
  refine ⟨⟨L.integrable_comp hv.1, L.integrable_comp hv.2⟩, fun t ht ↦ ?_⟩
  have hvt : IntervalIntegrable (fun s ↦ edgeField (Q s) (u' s)) volume 0 t := hv.mono_set (by
    rw [uIcc_of_le hT', uIcc_of_le ht.1]; exact Icc_subset_Icc_right ht.2)
  have e := L.intervalIntegral_comp_comm hvt
  beta_reduce
  rw [hx t ht]
  exact congrArg (Q 0 k + ·) e.symm

/-- Along an admissible pair of the edge problem, `X = Φ(x, y)` solves `X' = [P, X]` with
`P = Z_w/⟨Z_w, X⟩`, `w = (0, ½ + u_e, ½ - u_e)`, in integral form. -/
private lemma l3e_IF_Φ (hT' : 0 ≤ T')
    (hadm : Pontryagin.IsAdmissibleIn edgeField edgeDomain edgeControlSet (Q 0) T' u' Q)
    (i j : Fin 2) :
    l3e_IF (fun τ ↦ Φ (Q τ 0) (Q τ 1) i j)
      (fun τ ↦ (controlP (edgeControl (u' τ)) (Φ (Q τ 0) (Q τ 1)) * Φ (Q τ 0) (Q τ 1) -
        Φ (Q τ 0) (Q τ 1) * controlP (edgeControl (u' τ)) (Φ (Q τ 0) (Q τ 1))) i j) 0 T' := by
  obtain ⟨⟨-, hU, -, hv, hx⟩, hΩ⟩ := hadm
  refine l3e_IF_of_ac hT' (absolutelyContinuousOnInterval_comp_of_eq_add_integral
    (F := fun q : Fin 3 → ℝ ↦ Φ (q 0) (q 1) i j) hT' hv hx fun t ht ↦ ?_) ?_
  · have h1 : Q t 1 ≠ 0 := (hΩ t ht).1.ne'
    fin_cases i <;> fin_cases j <;>
      simp only [Φ, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] <;>
      fun_prop (disch := assumption)
  · filter_upwards [ae_hasDerivAt_of_eq_add_integral hv ⟨le_rfl, hT'⟩ hx] with t ht htI
    have hd := ht htI
    have hΩt := hΩ t (Ioo_subset_Icc_self htI)
    exact l3e_hasDerivAt_Φ hΩt.1.ne'
      (l3e_edge_denom_neg hΩt (hU t (Ioo_subset_Icc_self htI))).ne
      (hasDerivAt_pi.1 hd 0) (hasDerivAt_pi.1 hd 1) i j

/-- Along an admissible pair of the edge problem, `h = [[1, -x], [s, 1 - sx]]` solves
`h' = h Φ(x, y)`, in integral form. -/
private lemma l3e_IF_edgeH (hT' : 0 ≤ T')
    (hadm : Pontryagin.IsAdmissibleIn edgeField edgeDomain edgeControlSet (Q 0) T' u' Q)
    (i j : Fin 2) :
    l3e_IF (fun τ ↦ edgeH (Q τ) i j) (fun τ ↦ (edgeH (Q τ) * Φ (Q τ 0) (Q τ 1)) i j) 0 T' := by
  obtain ⟨⟨-, -, -, hv, hx⟩, hΩ⟩ := hadm
  refine l3e_IF_of_ac hT' (absolutelyContinuousOnInterval_comp_of_eq_add_integral
    (F := fun q : Fin 3 → ℝ ↦ edgeH q i j) hT' hv hx fun t _ ↦ ?_) ?_
  · fin_cases i <;> fin_cases j <;>
      simp only [edgeH, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one] <;>
      fun_prop
  · filter_upwards [ae_hasDerivAt_of_eq_add_integral hv ⟨le_rfl, hT'⟩ hx] with t ht htI
    have hd := ht htI
    exact l3e_hasDerivAt_edgeH (hΩ t (Ioo_subset_Icc_self htI)).1.ne' (hasDerivAt_pi.1 hd 0)
      (hasDerivAt_pi.1 hd 2) i j

end Competitor

/-! ### Splicing a competitor into the minimizer -/

/-- The curve equal to `A` before `c`, to `B` on `[c, c')` and to `C` from `c'` on. -/
private noncomputable def l3e_sp {α : Type*} (c c' : ℝ) (A B C : ℝ → α) (t : ℝ) : α :=
  if t < c then A t else if t < c' then B t else C t

section Splice

variable {α : Type*} {c c' : ℝ} {A B C : ℝ → α} {t : ℝ}

private lemma l3e_sp_of_lt (ht : t < c) : l3e_sp c c' A B C t = A t := by
  simp only [l3e_sp, ht, ↓reduceIte]

private lemma l3e_sp_of_mem_Ico (ht : t ∈ Ico c c') : l3e_sp c c' A B C t = B t := by
  simp only [l3e_sp, not_lt.2 ht.1, ht.2, ↓reduceIte]

private lemma l3e_sp_right (hcc' : c ≤ c') (ht : c' ≤ t) : l3e_sp c c' A B C t = C t := by
  simp only [l3e_sp, not_lt.2 (hcc'.trans ht), not_lt.2 ht, ↓reduceIte]

private lemma l3e_sp_left (hcc' : c < c') (hAB : A c = B c) (ht : t ≤ c) :
    l3e_sp c c' A B C t = A t := by
  rcases ht.lt_or_eq with h | rfl
  · exact l3e_sp_of_lt h
  · rw [l3e_sp_of_mem_Ico ⟨le_rfl, hcc'⟩, hAB]

private lemma l3e_sp_mid (hBC : B c' = C c') (ht : t ∈ Icc c c') :
    l3e_sp c c' A B C t = B t := by
  rcases ht.2.lt_or_eq with h | rfl
  · exact l3e_sp_of_mem_Ico ⟨ht.1, h⟩
  · rw [l3e_sp_right ht.1 le_rfl, hBC]

end Splice

/-- Gluing integral forms on three adjacent intervals. -/
private lemma l3e_IF_sp {a b c e : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hce : c ≤ e)
    {f v f₁ v₁ f₂ v₂ f₃ v₃ : ℝ → ℝ} (h₁ : l3e_IF f₁ v₁ a b) (h₂ : l3e_IF f₂ v₂ b c)
    (h₃ : l3e_IF f₃ v₃ c e) (hf₁ : ∀ t ∈ Icc a b, f₁ t = f t)
    (hf₂ : ∀ t ∈ Icc b c, f₂ t = f t) (hf₃ : ∀ t ∈ Icc c e, f₃ t = f t)
    (hv₁ : ∀ t ∈ Ioo a b, v₁ t = v t) (hv₂ : ∀ t ∈ Ioo b c, v₂ t = v t)
    (hv₃ : ∀ t ∈ Ioo c e, v₃ t = v t) : l3e_IF f v a e :=
  l3e_IF_trans (l3e_IF_trans (l3e_IF_congr h₁ hab hf₁ hv₁) (l3e_IF_congr h₂ hbc hf₂ hv₂) hab hbc)
    (l3e_IF_congr h₃ hce hf₃ hv₃) (hab.trans hbc) hce

/-- `R⁻ʲ (Rʲ M R⁻ʲ) Rʲ = M`. -/
private lemma l3e_unframe (j : Fin 3) (M : Mat2) :
    R⁻¹ ^ (j : ℕ) * edgeFrame j M * R ^ (j : ℕ) = M := by
  unfold edgeFrame
  simp only [← Matrix.mul_assoc, poly_Rinvpow_mul_Rpow, Matrix.one_mul]
  rw [Matrix.mul_assoc, poly_Rinvpow_mul_Rpow, Matrix.mul_one]

private lemma l3e_det_edgeH (q : Fin 3 → ℝ) : (edgeH q).det = 1 := by
  rw [edgeH, Matrix.det_fin_two_of]
  ring

private lemma l3e_det_inv_edgeH (q : Fin 3 → ℝ) : ((edgeH q)⁻¹).det = 1 := by
  have h := Matrix.det_nonsing_inv_mul_det (A := edgeH q) (by rw [l3e_det_edgeH]; exact isUnit_one)
  rwa [l3e_det_edgeH, mul_one] at h

/-- The control of the spliced arc on `[c, c + T')`: the competitor's edge control, rotated to
the edge `{u_j = 0}`. -/
private noncomputable def l3e_uM (j : Fin 3) (c : ℝ) (u' : ℝ → ℝ) (t : ℝ) : Fin 3 → ℝ :=
  l3e_rot j (edgeControl (u' (t - c)))

/-- The state `X = R⁻ʲ Φ(x', y') Rʲ` of the spliced arc on `[c, c + T']`. -/
private noncomputable def l3e_XM (j : Fin 3) (c : ℝ) (Q : ℝ → Fin 3 → ℝ) (t : ℝ) : Mat2 :=
  R⁻¹ ^ (j : ℕ) * Φ (Q (t - c) 0) (Q (t - c) 1) * R ^ (j : ℕ)

/-- The state `g = R⁻ʲ (g̃(c) h(q'(0))⁻¹ h(q'(t - c))) Rʲ` of the spliced arc on `[c, c + T']`
(equation (8.1.1) read backwards). -/
private noncomputable def l3e_gM (j : Fin 3) (c : ℝ) (g₀ : Mat2) (Q : ℝ → Fin 3 → ℝ) (t : ℝ) :
    Mat2 :=
  R⁻¹ ^ (j : ℕ) * (edgeFrame j g₀ * (edgeH (Q 0))⁻¹ * edgeH (Q (t - c))) * R ^ (j : ℕ)

section Competitor

variable {T' : ℝ} {u' : ℝ → ℝ} {Q : ℝ → Fin 3 → ℝ}

private lemma l3e_IF_XM (hT' : 0 ≤ T')
    (hadm : Pontryagin.IsAdmissibleIn edgeField edgeDomain edgeControlSet (Q 0) T' u' Q)
    (j : Fin 3) (c : ℝ) (i k : Fin 2) :
    l3e_IF (fun t ↦ l3e_XM j c Q t i k)
      (fun t ↦ (controlP (l3e_uM j c u' t) (l3e_XM j c Q t) * l3e_XM j c Q t -
        l3e_XM j c Q t * controlP (l3e_uM j c u' t) (l3e_XM j c Q t)) i k) c (c + T') := by
  have h1 := l3e_IF_conj hT' (l3e_IF_Φ hT' hadm) (R⁻¹ ^ (j : ℕ)) (R ^ (j : ℕ)) i k
  have h2 := l3e_IF_shift h1 c (zero_add c).symm (add_comm c T')
  refine l3e_IF_congr h2 (by linarith) (fun t _ ↦ rfl) (fun t _ ↦ ?_)
  simp only [l3e_XM, l3e_uM]
  rw [poly_conj_bracket (poly_Rpow_mul_Rinvpow _),
    poly_controlP_conj (poly_Rpow_mul_Rinvpow _) (l3e_conj_controlMatrix j _)]

private lemma l3e_IF_gM (hT' : 0 ≤ T')
    (hadm : Pontryagin.IsAdmissibleIn edgeField edgeDomain edgeControlSet (Q 0) T' u' Q)
    (j : Fin 3) (c : ℝ) (g₀ : Mat2) (i k : Fin 2) :
    l3e_IF (fun t ↦ l3e_gM j c g₀ Q t i k)
      (fun t ↦ (l3e_gM j c g₀ Q t * l3e_XM j c Q t) i k) c (c + T') := by
  have h0 := l3e_IF_conj hT' (l3e_IF_edgeH hT' hadm) (edgeFrame j g₀ * (edgeH (Q 0))⁻¹) 1
  have h1 := l3e_IF_conj hT' h0 (R⁻¹ ^ (j : ℕ)) (R ^ (j : ℕ)) i k
  have h2 := l3e_IF_shift h1 c (zero_add c).symm (add_comm c T')
  refine l3e_IF_congr h2 (by linarith) (fun t _ ↦ ?_) (fun t _ ↦ ?_)
  · simp only [l3e_gM, Matrix.mul_one]
  · simp only [l3e_gM, l3e_XM, Matrix.mul_one]
    rw [← poly_conj_mul (poly_Rpow_mul_Rinvpow _)]
    simp only [Matrix.mul_assoc]

private lemma l3e_XM_left {j : Fin 3} {c : ℝ} {X₀ : Mat2}
    (hX0 : edgeFrame j X₀ = Φ (Q 0 0) (Q 0 1)) : l3e_XM j c Q c = X₀ := by
  simp only [l3e_XM, sub_self, ← hX0, l3e_unframe]

private lemma l3e_XM_right {j : Fin 3} {c : ℝ} {X₁ : Mat2}
    (hX1 : edgeFrame j X₁ = Φ (Q T' 0) (Q T' 1)) : l3e_XM j c Q (c + T') = X₁ := by
  simp only [l3e_XM, add_sub_cancel_left, ← hX1, l3e_unframe]

private lemma l3e_gM_left (j : Fin 3) (c : ℝ) (g₀ : Mat2) : l3e_gM j c g₀ Q c = g₀ := by
  simp only [l3e_gM, sub_self]
  rw [Matrix.mul_assoc (edgeFrame j g₀),
    Matrix.nonsing_inv_mul _ (by rw [l3e_det_edgeH]; exact isUnit_one), Matrix.mul_one,
    l3e_unframe]

private lemma l3e_gM_right {j : Fin 3} {c : ℝ} {g₀ g₁ : Mat2}
    (hg1 : edgeFrame j g₁ = edgeFrame j g₀ * (edgeH (Q 0))⁻¹ * edgeH (Q T')) :
    l3e_gM j c g₀ Q (c + T') = g₁ := by
  simp only [l3e_gM, add_sub_cancel_left, ← hg1, l3e_unframe]

private lemma l3e_det_gM (j : Fin 3) (c : ℝ) (g₀ : Mat2) (t : ℝ) :
    (l3e_gM j c g₀ Q t).det = g₀.det := by
  rw [l3e_gM, poly_det_conj (poly_Rpow_mul_Rinvpow _), Matrix.det_mul, Matrix.det_mul,
    l3e_det_edgeH, l3e_det_inv_edgeH, edgeFrame, poly_det_conj (poly_Rinvpow_mul_Rpow _)]
  ring

end Competitor

/-- **The splice.** Let `(T, u, g, X)` be admissible for Problem 3.6.2 and let `(u_e', q')` be an
admissible pair of the `j`-th edge problem on `[0, T']` whose `(x', y')` stays in the star domain
and whose endpoints match the trajectory at `c` and `d` in the sense of (8.1.1) and of
`Φ(x, y) = Rʲ X R⁻ʲ`. Then the trajectory equal to `(u, g, X)` on `[0, c]`, to the arc rebuilt
from `q'` on `[c, c + T']`, and to `(u, g, X)` shifted by `T' - (d - c)` afterwards, is admissible
for Problem 3.6.2 (with terminal time `T + T' - (d - c)`). -/
private lemma l3e_splice_isReinhardtAdmissible {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsReinhardtAdmissible T u g X) {j : Fin 3} {c d : ℝ} (hc : 0 ≤ c) (hcd : c < d)
    (hd : d ≤ T) {T' : ℝ} (hT' : 0 < T') {u' : ℝ → ℝ} {Q : ℝ → Fin 3 → ℝ}
    (hadm : Pontryagin.IsAdmissibleIn edgeField edgeDomain edgeControlSet (Q 0) T' u' Q)
    (hstar : ∀ τ ∈ Icc 0 T', (Q τ 0, Q τ 1) ∈ starDomain)
    (hX0 : edgeFrame j (X c) = Φ (Q 0 0) (Q 0 1)) (hX1 : edgeFrame j (X d) = Φ (Q T' 0) (Q T' 1))
    (hg1 : edgeFrame j (g d) = edgeFrame j (g c) * (edgeH (Q 0))⁻¹ * edgeH (Q T')) :
    IsReinhardtAdmissible (T + T' - (d - c))
      (l3e_sp c (c + T') u (l3e_uM j c u') (fun t ↦ u (t - (T' - (d - c)))))
      (l3e_sp c (c + T') g (l3e_gM j c (g c) Q) (fun t ↦ g (t - (T' - (d - c)))))
      (l3e_sp c (c + T') X (l3e_XM j c Q) (fun t ↦ X (t - (T' - (d - c))))) := by
  obtain ⟨⟨hT, humeas, hU, hgX, hgI, hXI⟩, hg0, hgT, hXT⟩ := h
  have hcc' : c < c + T' := by linarith
  have hc'T : c + T' ≤ T + T' - (d - c) := by linarith
  have hd' : c + T' - (T' - (d - c)) = d := by ring
  have hT'' : T + T' - (d - c) - (T' - (d - c)) = T := by ring
  have jX0 : X c = l3e_XM j c Q c := (l3e_XM_left hX0).symm
  have jX1 : l3e_XM j c Q (c + T') = X (c + T' - (T' - (d - c))) := by
    rw [hd']; exact l3e_XM_right hX1
  have jg0 : g c = l3e_gM j c (g c) Q c := (l3e_gM_left j c (g c)).symm
  have jg1 : l3e_gM j c (g c) Q (c + T') = g (c + T' - (T' - (d - c))) := by
    rw [hd']; exact l3e_gM_right hg1
  refine ⟨⟨by linarith, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · -- measurability
    refine Measurable.ite measurableSet_Iio humeas (Measurable.ite measurableSet_Iio ?_ ?_)
    · exact ((l3e_continuous_rot j).comp l3e_continuous_edgeControl).measurable.comp
        (hadm.1.1.comp (measurable_id.sub_const c))
    · exact humeas.comp (measurable_id.sub_const _)
  · -- the control lies in `U_T`
    intro t ht
    rcases lt_or_ge t c with h1 | h1
    · rw [l3e_sp_of_lt h1]; exact hU t ⟨ht.1, by linarith⟩
    rcases lt_or_ge t (c + T') with h2 | h2
    · rw [l3e_sp_of_mem_Ico ⟨h1, h2⟩]
      exact l3e_rot_mem
        (edgeControl_mem_controlSimplex (hadm.1.2.1 (t - c) ⟨by linarith, by linarith⟩))
    · rw [l3e_sp_right hcc'.le h2]; exact hU _ ⟨by linarith, by linarith [ht.2]⟩
  · -- `g ∈ SL₂(ℝ)` and `X` is a star state
    intro t ht
    rcases lt_or_ge t c with h1 | h1
    · rw [l3e_sp_of_lt h1, l3e_sp_of_lt h1]; exact hgX t ⟨ht.1, by linarith⟩
    rcases lt_or_ge t (c + T') with h2 | h2
    · rw [l3e_sp_of_mem_Ico ⟨h1, h2⟩, l3e_sp_of_mem_Ico ⟨h1, h2⟩, l3e_det_gM]
      have hτ : t - c ∈ Icc 0 T' := ⟨by linarith, by linarith⟩
      exact ⟨(hgX c ⟨hc, by linarith⟩).1, poly_isStarState_conj_pow _
        ((theorem4_4_1 _ _ (hstar _ hτ).1).2 (hstar _ hτ))⟩
    · rw [l3e_sp_right hcc'.le h2, l3e_sp_right hcc'.le h2]
      exact hgX _ ⟨by linarith, by linarith [ht.2]⟩
  · -- `g' = g X`
    intro i k
    exact l3e_IF_sp hc hcc'.le hc'T
      (l3e_IF_of_isIntegralCurve hgI le_rfl hc (hcd.le.trans hd) i k)
      (l3e_IF_gM hT'.le hadm j c (g c) i k)
      (l3e_IF_shift (l3e_IF_of_isIntegralCurve hgI (hc.trans hcd.le) hd le_rfl i k)
        (T' - (d - c)) (by ring) (by ring))
      (fun t ht ↦ by rw [l3e_sp_left hcc' jg0 ht.2])
      (fun t ht ↦ by rw [l3e_sp_mid jg1 ht])
      (fun t ht ↦ by rw [l3e_sp_right hcc'.le ht.1])
      (fun t ht ↦ by beta_reduce; rw [l3e_sp_of_lt ht.2, l3e_sp_of_lt ht.2])
      (fun t ht ↦ by
        beta_reduce; rw [l3e_sp_of_mem_Ico ⟨ht.1.le, ht.2⟩, l3e_sp_of_mem_Ico ⟨ht.1.le, ht.2⟩])
      (fun t ht ↦ by
        beta_reduce; rw [l3e_sp_right hcc'.le ht.1.le, l3e_sp_right hcc'.le ht.1.le])
  · -- `X' = [P, X]`
    intro i k
    exact l3e_IF_sp hc hcc'.le hc'T
      (l3e_IF_of_isIntegralCurve hXI le_rfl hc (hcd.le.trans hd) i k)
      (l3e_IF_XM hT'.le hadm j c i k)
      (l3e_IF_shift (l3e_IF_of_isIntegralCurve hXI (hc.trans hcd.le) hd le_rfl i k)
        (T' - (d - c)) (by ring) (by ring))
      (fun t ht ↦ by rw [l3e_sp_left hcc' jX0 ht.2])
      (fun t ht ↦ by rw [l3e_sp_mid jX1 ht])
      (fun t ht ↦ by rw [l3e_sp_right hcc'.le ht.1])
      (fun t ht ↦ by beta_reduce; rw [l3e_sp_of_lt ht.2, l3e_sp_of_lt ht.2])
      (fun t ht ↦ by
        beta_reduce; rw [l3e_sp_of_mem_Ico ⟨ht.1.le, ht.2⟩, l3e_sp_of_mem_Ico ⟨ht.1.le, ht.2⟩])
      (fun t ht ↦ by
        beta_reduce; rw [l3e_sp_right hcc'.le ht.1.le, l3e_sp_right hcc'.le ht.1.le])
  · rw [l3e_sp_left hcc' jg0 hc]; exact hg0
  · rw [l3e_sp_right hcc'.le hc'T, hT'']; exact hgT
  · rw [l3e_sp_right hcc'.le hc'T, l3e_sp_left hcc' jX0 hc, hT'']; exact hXT

/-- An integral curve on `[0, T]` is continuous there. -/
private lemma l3e_continuousOn_of_isIntegralCurve {f v : ℝ → Mat2} {T : ℝ}
    (h : IsIntegralCurve f v T) : ContinuousOn f (Icc 0 T) :=
  Matrix.continuousOn_of_eq_add_integral (f := f) (v := v) (a := 0) (b := T) h

/-- `⟨J, R⁻ʲ M Rʲ⟩ = ⟨J, M⟩`. -/
private lemma l3e_traceForm_J_conj (j : ℕ) (M : Mat2) :
    traceForm J (R⁻¹ ^ j * M * R ^ j) = traceForm J M := by
  conv_lhs => rw [← poly_conj_pow_J j]
  exact poly_traceForm_conj (poly_Rpow_mul_Rinvpow j) J M

/-- `⟨J, X⟩` along a curve continuous on `[a, b]` is integrable there. -/
private lemma l3e_intervalIntegrable_traceForm_J {X : ℝ → Mat2} {a b : ℝ} (hab : a ≤ b)
    (hX : ContinuousOn X (Icc a b)) :
    IntervalIntegrable (fun t ↦ traceForm J (X t)) volume a b := by
  have hc : Continuous fun M : Mat2 ↦ traceForm J M :=
    (continuous_const.matrix_mul continuous_id).matrix_trace
  exact (hc.comp_continuousOn hX).intervalIntegrable_of_Icc hab

/-- `∫ₐᵇ ⟨J, X⟩ = ∫ₐᶜ ⟨J, X⟩ + ∫ᶜᵇ ⟨J, X⟩` for `X` continuous on `[a, b]` and `c ∈ [a, b]`. -/
private lemma l3e_integral_traceForm_J_split {X : ℝ → Mat2} {a c b : ℝ} (hac : a ≤ c)
    (hcb : c ≤ b) (hX : ContinuousOn X (Icc a b)) :
    ∫ t in a..b, traceForm J (X t) =
      (∫ t in a..c, traceForm J (X t)) + ∫ t in c..b, traceForm J (X t) :=
  (intervalIntegral.integral_add_adjacent_intervals
    (l3e_intervalIntegrable_traceForm_J hac (hX.mono (Icc_subset_Icc_right hcb)))
    (l3e_intervalIntegrable_traceForm_J hcb (hX.mono (Icc_subset_Icc_left hac)))).symm

/-- **The cost of the splice.** The cost of the spliced trajectory is the cost of the
minimizer off `[c, d]` plus `(3/2)((x' + s')|₀^{T'} + ∫ x'²/y')`: on the middle arc
`-(3/2)⟨J, R⁻ʲ Φ(x', y') Rʲ⟩ = (3/2)(1 + x'² + y'²)/y' = (3/2)(x'' + s'' + x'²/y')` (the
computation behind `edgeCost_identity`, for the competitor). -/
private lemma l3e_splice_cost {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsReinhardtAdmissible T u g X) {j : Fin 3} {c d : ℝ} (hc : 0 ≤ c) (hcd : c < d)
    (hd : d ≤ T) {T' : ℝ} (hT' : 0 < T') {u' : ℝ → ℝ} {Q : ℝ → Fin 3 → ℝ}
    (hadm : Pontryagin.IsAdmissibleIn edgeField edgeDomain edgeControlSet (Q 0) T' u' Q)
    (hstar : ∀ τ ∈ Icc 0 T', (Q τ 0, Q τ 1) ∈ starDomain)
    (hX0 : edgeFrame j (X c) = Φ (Q 0 0) (Q 0 1)) (hX1 : edgeFrame j (X d) = Φ (Q T' 0) (Q T' 1))
    (hg1 : edgeFrame j (g d) = edgeFrame j (g c) * (edgeH (Q 0))⁻¹ * edgeH (Q T')) :
    reinhardtCost (T + T' - (d - c))
        (l3e_sp c (c + T') X (l3e_XM j c Q) (fun t ↦ X (t - (T' - (d - c))))) =
      -(3 / 2) * ((∫ t in (0 : ℝ)..c, traceForm J (X t)) + ∫ t in d..T, traceForm J (X t)) +
        3 / 2 * ((Q T' 0 - Q 0 0) + (Q T' 2 - Q 0 2) + Pontryagin.cost edgeCost T' u' Q) := by
  have hS := l3e_splice_isReinhardtAdmissible h hc hcd hd hT' hadm hstar hX0 hX1 hg1
  set XS := l3e_sp c (c + T') X (l3e_XM j c Q) (fun t ↦ X (t - (T' - (d - c)))) with hXS
  have hcc' : c < c + T' := by linarith
  have hc'T : c + T' ≤ T + T' - (d - c) := by linarith
  have hd' : c + T' - (T' - (d - c)) = d := by ring
  have hT'' : T + T' - (d - c) - (T' - (d - c)) = T := by ring
  have jX0 : X c = l3e_XM j c Q c := (l3e_XM_left hX0).symm
  have jX1 : l3e_XM j c Q (c + T') = X (c + T' - (T' - (d - c))) := by
    rw [hd']; exact l3e_XM_right hX1
  have hcont : ContinuousOn XS (Icc 0 (T + T' - (d - c))) :=
    l3e_continuousOn_of_isIntegralCurve hS.1.2.2.2.2.2
  rw [reinhardtCost, l3e_integral_traceForm_J_split hc (by linarith) hcont,
    l3e_integral_traceForm_J_split hcc'.le hc'T (hcont.mono (Icc_subset_Icc_left hc))]
  -- the first piece
  have e1 : ∫ t in (0 : ℝ)..c, traceForm J (XS t) = ∫ t in (0 : ℝ)..c, traceForm J (X t) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [uIcc_of_le hc] at ht
    simp only [hXS, l3e_sp_left hcc' jX0 ht.2]
  -- the last piece
  have e3 : ∫ t in c + T'..T + T' - (d - c), traceForm J (XS t) =
      ∫ t in d..T, traceForm J (X t) := by
    have e := intervalIntegral.integral_comp_sub_right (fun t ↦ traceForm J (X t))
      (a := c + T') (b := T + T' - (d - c)) (T' - (d - c))
    rw [hd', hT''] at e
    rw [← e]
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [uIcc_of_le hc'T] at ht
    simp only [hXS, l3e_sp_right hcc'.le ht.1]
  -- the middle piece
  have hQc : ContinuousOn Q (Icc 0 T') := hadm.1.2.2.1
  have hy : ∀ τ ∈ Icc 0 T', 0 < Q τ 1 := fun τ hτ ↦ (hadm.2 τ hτ).1
  have hI0 := l3e_coord_IF hT'.le hadm 0
  have hI2 := l3e_coord_IF hT'.le hadm 2
  have iy : IntervalIntegrable (fun τ ↦ Q τ 1) volume 0 T' := hI0.1
  have iy' : IntervalIntegrable (fun τ ↦ 1 / Q τ 1) volume 0 T' := hI2.1
  have ix : IntervalIntegrable (fun τ ↦ Q τ 0 ^ 2 / Q τ 1) volume 0 T' :=
    ContinuousOn.intervalIntegrable_of_Icc hT'.le
      ((((continuous_apply 0).comp_continuousOn hQc).pow 2).div
        ((continuous_apply 1).comp_continuousOn hQc) fun τ hτ ↦ (hy τ hτ).ne')
  have ey : ∫ τ in (0 : ℝ)..T', Q τ 1 = Q T' 0 - Q 0 0 := by
    have := hI0.2 T' ⟨hT'.le, le_rfl⟩
    change Q T' 0 = Q 0 0 + ∫ τ in (0 : ℝ)..T', Q τ 1 at this
    linarith
  have ey' : ∫ τ in (0 : ℝ)..T', 1 / Q τ 1 = Q T' 2 - Q 0 2 := by
    have := hI2.2 T' ⟨hT'.le, le_rfl⟩
    change Q T' 2 = Q 0 2 + ∫ τ in (0 : ℝ)..T', 1 / Q τ 1 at this
    linarith
  have e2 : ∫ t in c..c + T', traceForm J (XS t) =
      -((Q T' 0 - Q 0 0) + (Q T' 2 - Q 0 2) + Pontryagin.cost edgeCost T' u' Q) := by
    have step1 : ∫ t in c..c + T', traceForm J (XS t) =
        ∫ t in c..c + T', traceForm J (Φ (Q (t - c) 0) (Q (t - c) 1)) := by
      refine intervalIntegral.integral_congr fun t ht ↦ ?_
      rw [uIcc_of_le hcc'.le] at ht
      rw [hXS, l3e_sp_mid jX1 ht, l3e_XM, l3e_traceForm_J_conj]
    rw [step1, intervalIntegral.integral_comp_sub_right
      (fun τ ↦ traceForm J (Φ (Q τ 0) (Q τ 1))) c, sub_self, add_sub_cancel_left]
    have step2 : ∫ τ in (0 : ℝ)..T', traceForm J (Φ (Q τ 0) (Q τ 1)) =
        ∫ τ in (0 : ℝ)..T', -(Q τ 1 + 1 / Q τ 1 + Q τ 0 ^ 2 / Q τ 1) := by
      refine intervalIntegral.integral_congr fun τ hτ ↦ ?_
      rw [uIcc_of_le hT'.le] at hτ
      have hy0 := hy τ hτ
      rw [poly_traceForm_J_Φ _ _ hy0]
      field_simp
      ring
    rw [step2, intervalIntegral.integral_neg, intervalIntegral.integral_add (iy.add iy') ix,
      intervalIntegral.integral_add iy iy', ey, ey']
    rfl
  rw [e1, e2, e3]
  ring

/-- The star domain is open. -/
private lemma l3e_isOpen_starDomain : IsOpen starDomain := by
  have h : Continuous fun p : ℝ × ℝ ↦ p.1 ^ 2 + p.2 ^ 2 := by fun_prop
  simp only [starDomain, Set.ofPred_and]
  exact (isOpen_lt continuous_const continuous_snd).inter
    ((isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_fst continuous_const).inter (isOpen_lt continuous_const h)))

/-- **The principle of optimality for an edge arc** (proof of Proposition 8.1.3, TeX 6793–6797,
with E48's gap repaired). Let `(T, u, g, X)` be a global minimizer of the Reinhardt problem and let
`u_j = 0` almost everywhere on `[c, d] ⊆ [0, T]`. Then the edge arc `(u_e, (x, y, s))` of the
minimizer on `[c, d]` (`edgeParam j u`, `edgeState j X c`) is a strong local minimizer of the
`j`-th edge control problem with fixed endpoints (8.1.4) and free terminal time.

Proof: let `(u_e', q')` be an admissible pair of the edge problem on `[0, T']` with the same
endpoints, `|T' - (d - c)| < ε` and `‖q'(σT') - q(σ(d - c))‖ < ε`. For `ε` small, `(x', y')`
stays in a compact neighbourhood of the minimizer's arc inside the star domain (`eqn_xy_edge`:
the arc is in `𝔥*`, which is open). Splice: on `[0, c]` the minimizer; on `[c, c + T']` the
trajectory `X' = R⁻ʲ Φ(x', y') Rʲ`, `g' = R⁻ʲ (g̃(c) h(q'(0))⁻¹ h(q'(t - c))) Rʲ` (8.1.1), with
the control `R⁻ʲ`-rotated from `(0, ½ + u_e', ½ - u_e')`, which solves the Reinhardt state
equations (`eqn_xy_edge`, `eqn_g_edge` read backwards: `h⁻¹h' = Φ`); on
`[c + T', T + T' - (d - c)]` the minimizer shifted by `T' - (d - c)`. Equal endpoints of `(x, y, s)`
give `X'(c + T') = X(d)` and `g'(c + T') = g(d)` by (8.1.1), so the splice is admissible for
Problem 3.6.2 (the boundary conditions at `0` and at the terminal time are the minimizer's;
Carathéodory solutions glue, as `ct_pw_isIntegralCurve` in `Ch6/PeriodicExtension`). By
`edgeCost_identity` its cost minus the minimizer's is `(3/2)(cost_edge(u_e', q') -
cost_edge(u_e, q))`, the boundary terms `(s + x)|` being equal; minimality gives the inequality.

In the formal proof the splice is `l3e_splice_isReinhardtAdmissible` (the middle arc solves the
state equations because `x'`, `y'`, `s'` are absolutely continuous and `Φ`, `h` are `C¹` where
`y' > 0`: the chain rule almost everywhere, `l3e_hasDerivAt_Φ`, `l3e_hasDerivAt_edgeH`, and the
fundamental theorem of calculus for absolutely continuous functions) and its cost is
`l3e_splice_cost`. The neighbourhood is a thickening of the compact arc `(x, y)([0, d - c])`
inside the open star domain; `ε` is its radius (the condition on `T'` is not needed). -/
private theorem l3st_isStrongLocalMinimizer_edgeState {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (hmin : IsReinhardtMinimizer T u g X) {j : Fin 3} {c d : ℝ} (hc : 0 ≤ c) (hcd : c < d)
    (hd : d ≤ T) (hu : ∀ᵐ t, t ∈ Ioo c d → u t j = 0) :
    Pontryagin.IsStrongLocalMinimizer edgeField edgeCost edgeDomain edgeControlSet
      {w | w = (edgeState j X c 0, edgeState j X c (d - c))} (d - c)
      (fun t ↦ edgeParam j (u (c + t))) (edgeState j X c) := by
  have hst := hmin.1.1
  obtain ⟨hadm, hΦ, -⟩ := eqn_xy_edge hst hc hcd hd hu
  have hg := eqn_g_edge hst hc hcd hd hu
  have hcost := edgeCost_identity hst hc hcd hd hu
  have hL0 : 0 < d - c := sub_pos.2 hcd
  -- a thickening of the compact arc `(x, y)([0, d - c])` lies in the open star domain
  have hqc : ContinuousOn (edgeState j X c) (Icc 0 (d - c)) := hadm.1.2.2.1
  have hK : IsCompact ((fun t ↦ (edgeState j X c t 0, edgeState j X c t 1)) '' Icc 0 (d - c)) :=
    isCompact_Icc.image_of_continuousOn
      (((continuous_apply 0).comp_continuousOn hqc).prodMk
        ((continuous_apply 1).comp_continuousOn hqc))
  have hKsub : (fun t ↦ (edgeState j X c t 0, edgeState j X c t 1)) '' Icc 0 (d - c) ⊆
      starDomain := by
    rintro _ ⟨t, ht, rfl⟩
    exact (hΦ t ht).2
  obtain ⟨ε, hε, hεsub⟩ := hK.exists_thickening_subset_open l3e_isOpen_starDomain hKsub
  refine ⟨hL0, hadm, rfl, ε, hε, fun T' u' Q hT' hadm' hN _ hclose ↦ ?_⟩
  simp only [Set.mem_ofPred_eq, Prod.mk.injEq] at hN
  obtain ⟨hQ0, hQ1⟩ := hN
  -- the competitor stays in the star domain
  have hstar : ∀ τ ∈ Icc 0 T', (Q τ 0, Q τ 1) ∈ starDomain := by
    intro τ hτ
    have hσ : τ / T' ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg hτ.1 hT'.le, (div_le_one hT').2 hτ.2⟩
    have h1 := hclose _ hσ
    rw [div_mul_cancel₀ τ hT'.ne'] at h1
    refine hεsub (Metric.mem_thickening_iff.2 ⟨_, ⟨τ / T' * (d - c),
      ⟨mul_nonneg hσ.1 hL0.le, mul_le_of_le_one_left hL0.le hσ.2⟩, rfl⟩, ?_⟩)
    have h0 := norm_le_pi_norm (Q τ - edgeState j X c (τ / T' * (d - c))) 0
    have h1' := norm_le_pi_norm (Q τ - edgeState j X c (τ / T' * (d - c))) 1
    rw [Pi.sub_apply, Real.norm_eq_abs] at h0 h1'
    rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
    exact ⟨h0.trans_lt h1, h1'.trans_lt h1⟩
  -- the endpoint conditions of the splice
  have hX0 : edgeFrame j (X c) = Φ (Q 0 0) (Q 0 1) := by
    have := (hΦ 0 ⟨le_rfl, hL0.le⟩).1
    rw [add_zero] at this
    rw [hQ0]; exact this
  have hX1 : edgeFrame j (X d) = Φ (Q T' 0) (Q T' 1) := by
    have := (hΦ (d - c) ⟨hL0.le, le_rfl⟩).1
    rw [show c + (d - c) = d by ring] at this
    rw [hQ1]; exact this
  have hg1 : edgeFrame j (g d) = edgeFrame j (g c) * (edgeH (Q 0))⁻¹ * edgeH (Q T') := by
    rw [hQ0, hQ1]; exact hg d ⟨hcd.le, le_rfl⟩
  -- the splice is admissible, and the minimizer is no worse
  have hle := hmin.2 _ _ _ _
    (l3e_splice_isReinhardtAdmissible hmin.1 hc hcd hd hT' hadm' hstar hX0 hX1 hg1)
  rw [l3e_splice_cost hmin.1 hc hcd hd hT' hadm' hstar hX0 hX1 hg1, hQ0, hQ1] at hle
  have hXc : ContinuousOn X (Icc 0 T) := l3e_continuousOn_of_isIntegralCurve hst.2.2.2.2.2
  rw [reinhardtCost, l3e_integral_traceForm_J_split hc (hcd.le.trans hd) hXc,
    l3e_integral_traceForm_J_split hcd.le hd (hXc.mono (Icc_subset_Icc_left hc))] at hle
  simp only [Pontryagin.cost] at hle ⊢
  linarith

/-- **Proposition 8.1.3** (`prop:edge-extremal`). The global minimizer of the Reinhardt problem
is an extremal of the Reinhardt control problem, and it is also edge extremal (Definition 8.1.2)
on its whole domain `[0, T]`.

"The global solution" presupposes existence and uniqueness; the statement is for every global
minimizer (`IsReinhardtMinimizer`), and one exists (`exists_isReinhardtMinimizer`).

Proof (the book's, TeX 6791–6798, with E48's gap repaired):
1. Extremal: `exists_isPontryaginExtremal_of_isReinhardtMinimizer` ("We have seen that the global
   minimizer must be extremal", §6.1–§6.2).
2. Edge extremal: for `j`, `[c, d]` with `u_j = 0` a.e., the edge arc is a strong local minimizer
   of the edge problem (`l3st_isStrongLocalMinimizer_edgeState`, the principle of optimality);
   the maximum principle `External.pontryagin_maximum_principle` (with `l3st_isC1On_edgeField`,
   `l3st_isC1On_edgeCost`, the compact control set `[-½, ½]`, and the boundary map
   `G(q₀, q₁) = (q₀ - q(0), q₁ - q(d - c))`, a submersion whose zero set is the fixed endpoints)
   gives `ν ≤ 0` and `p` with the conclusions of `IsEdgeProblemExtremal`; admissibility is
   `eqn_xy_edge`. -/
theorem proposition8_1_3 {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (hmin : IsReinhardtMinimizer T u g X) :
    (∃ (Λ₁ ΛR : ℝ → Mat2) (lam : ℝ), IsPontryaginExtremal T u g X Λ₁ ΛR lam) ∧
      IsEdgeExtremalOn 0 T u X := by
  refine ⟨exists_isPontryaginExtremal_of_isReinhardtMinimizer hmin,
    fun j c d hc hcd hd hu ↦ ?_⟩
  have hsl := l3st_isStrongLocalMinimizer_edgeState hmin hc hcd hd hu
  -- the fixed endpoints as the zero set of the submersion `G(z) = z - (q(0), q(d - c))`
  let G : (Fin 3 → ℝ) × (Fin 3 → ℝ) → (Fin 3 → ℝ) × (Fin 3 → ℝ) :=
    fun z ↦ z - (edgeState j X c 0, edgeState j X c (d - c))
  have hGd : ∀ z, HasFDerivAt G (ContinuousLinearMap.id ℝ _) z :=
    fun z ↦ (hasFDerivAt_id z).sub_const _
  obtain ⟨ν, p, hν, -, hnt, hadj, hmax, hH, -⟩ :=
    External.pontryagin_maximum_principle l3e_isOpen_edgeDomain
      (by unfold edgeControlSet; exact isCompact_Icc) l3st_isC1On_edgeField
      l3st_isC1On_edgeCost hsl (G := G) (contDiff_id.sub contDiff_const).contDiffAt
      (by rw [(hGd _).fderiv]; exact fun w ↦ ⟨w, rfl⟩) (sub_self _)
      (.of_forall fun z hz ↦ sub_eq_zero.1 hz)
  exact ⟨ν, p, hsl.1, hsl.2.1, hν, hnt, hadj, hmax, hH⟩

end SmoothedPolygons
