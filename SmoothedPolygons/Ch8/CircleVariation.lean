module

public import SmoothedPolygons.Ch8.Defs
public import SmoothedPolygons.Ch3.LieAlgebraDynamics
public import SmoothedPolygons.Ch3.ControlProblem
public import SmoothedPolygons.AppA.MatrixIdentities
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# A circular arc is not a local minimizer (second variation, proof of Theorem 8.2.7)

The proof of Theorem 8.2.7 (`thm:no-singular-arcs`, TeX 7320–7391) shows by a second variation
that a trajectory of the Reinhardt problem containing a circular arc (`X ≡ J` on an interval) is
not a minimizer; the book cites Mahler's second-variation proof that the circle is not a local
minimizer (`mahler1947area`) as background and gives its own computation (MCA:1049350).

## The proof

`exists_lt_reinhardtCost_of_circleArc` follows the book's route (TeX 7327–7391).

1. On the arc, `g(t) = g(t₁) exp(J(t - t₁))` (`arc_eq`, uniqueness for `g' = gJ`). After the
   time shift `t ↦ t - t₁` and the left translation by `g(t₁)` (the book takes `g₀ = I`; both
   leave the cost invariant) the arc is `exp(Jt)`, `t ∈ [0, L]`, `L = t₂ - t₁`.
2. The deformation (TeX 7334–7342), in the book's own time `t`: `g_s(t) = Ψ_s(t) exp(Jt)` with
   `Ψ_s = exp(sS)`, `S = [[ψ₁, ψ₂], [ψ₂, -ψ₁]]`, for one fixed pair `ψ = (ψ₁, ψ₂)` of smooth
   functions with compact support in `(0, L)` (`psi1`, `psi2`, `fS`). They are written
   `ψ₁ + iψ₂ = ρ e^{iθ}` with `ρ` a smooth plateau bump (`amp`, `ρ = 1` on `[L/3, 2L/3]`) and
   `θ` (`ang`) decreasing from `π/2` to `0` on `[L/3, 2L/3]` and constant elsewhere, so that
   `S = ρ E(θ)`, `E(θ) = [[cos θ, sin θ], [sin θ, -cos θ]]`, and Lemma A.6.4 (`lemmaA_6_4`) gives
   `Ψ_s = cosh(sρ) I + sinh(sρ) E(θ)` (`fΨ`, `fΨ_eq_exp`) with no division by `|ψ| = ρ`.
3. The book's choice of `ψ` (TeX 7374–7378): `ψ₁, ψ₂ ≥ 0`, and `ψ₁' > 0`, `ψ₂' < 0` on the
   overlap of their supports, the open set where both are positive (`psi_spec`). As in
   Remark 8.2.8's piecewise linear example, which this choice smooths, `ψ₂` rises first, on the
   overlap `(L/3, 2L/3)` the pair turns clockwise from the `ψ₂`-axis to the `ψ₁`-axis, and `ψ₁`
   falls last.
4. The cost (TeX 7344–7362) is the parametrization-invariant `-(3/2) ∫ ⟨J, g⁻¹dg⟩` (Cartan–Maurer
   form of eqn `eqn:cost`, TeX 2814). The product rule gives
   `g_s⁻¹g_s' = exp(-Jt) (Ψ_s⁻¹Ψ_s' + J) exp(Jt)` (`hasDerivAt_fg`), so
   `⟨J, g_s⁻¹g_s'⟩ = ⟨J, J⟩ + ⟨J, Ψ_s⁻¹Ψ_s'⟩` (`traceForm_J_fX`).
5. The cost formula (TeX 7363–7373), exactly: with `r = |ψ| = ρ`,
   `⟨J, Ψ_s⁻¹Ψ_s'⟩ = 2 (sinh(sr)/r)² (ψ₁'ψ₂ - ψ₁ψ₂') = -2 sinh²(sρ) θ'` (`traceForm_J_fW_eq`,
   `traceForm_J_fW`, `psi_wronskian`: `ψ₁'ψ₂ - ψ₁ψ₂' = -ρ²θ'`), so
   `cost(g_s) = 3L - 3 ∫₀ᴸ (sinh(sr)/r)² (ψ₁'ψ₂ - ψ₁ψ₂') dt` (`costT_eq`). Since
   `(sinh(sr)/r)² = s² + s⁴r²/3 + ⋯`, the book's `cost(g₀) - 3s² ∫ (ψ₁'ψ₂ - ψ₁ψ₂') + O(s³)` is the
   second-order truncation of this formula (`costT_expansion` proves the limit of
   `(cost(g_s) - cost(g₀))/s²`; for this `ψ`, `cost(g_s) = 3L - (3π/2) sinh² s` exactly,
   `costT_eq'`).
6. By the book's condition the integrand is `≥ 0` (off the overlap one `ψᵢ` vanishes, and then
   so does `ψᵢ'`, at a minimum of `ψᵢ ≥ 0`) and `> 0` on the overlap, so `cost(g_s) < 3L =
   cost(g₀)` for every `s ≠ 0` (`costT_lt`).
7. For small `s > 0` (TeX 7384–7390): `X_s = g_s⁻¹g_s'` (`fX`) and its derivative `X_s'` (`fD`)
   are jointly continuous in `(s, t)` and equal `J` and `0` at `s = 0`, so by the tube lemma on
   the compact `[0, L]` (`eventually_pos`) the star inequalities `ρᵢ(X_s) > 0`, `det X_s > 0` and
   the curvature numerators `k_j = det(σ_j', σ_j'') > 0` of the curves `σ_j = g_s s_{2j}*` hold
   (`fk`, `fk_zero`, `det2_curve`); off `(L/6, 5L/6)`, `X_s = J`.
8. The reparametrization to `det X = 1` (the parametrization of Proposition 3.1.9):
   `τ(t) = ∫₀ᵗ √(det X_s)`, inverted with Mathlib's order isomorphism
   (`StrictMono.orderIsoOfSurjective`) and the derivative of the inverse function
   (`HasDerivAt.of_local_left_inverse`). `X̃ = X_s/√(det X_s)` has `det X̃ = 1`; the star
   inequalities, linear in `X`, are kept (`ρ_smul`); the state-dependent curvatures are
   `k_j (dt/dτ)³ > 0` (`det2_reparam`); and the cost is unchanged (change of variables,
   `intervalIntegral.integral_comp_mul_deriv`).
9. Theorem 3.4.2 (`theorem3_4_2`) with the control `u_j = κ_j / Σ κ` (Definition 3.3.2) gives
   `X̃' = [P_u, X̃]`: the deformed arc is a state trajectory (`exists_deformedArc`).
10. The competitor: the original trajectory on `[0, t₁]`, the deformed arc (left-multiplied by
    `g(t₁)`) on `[t₁, t₁ + ℓ]` (`ℓ = τ(L)`), and the original from `t₂` on, shifted by `ℓ - L`;
    its integral curves are glued from the three pieces (`IC.trans`, `IC.shift`, `IC.congr_ae`),
    and its boundary values are those of the original trajectory.

## Notes on the book's text

* The condition "`ψ₁' > 0` and `ψ₂' < 0` on their common support" (TeX 7376–7378) cannot hold
  literally for smooth nonnegative functions with compact support (where `ψᵢ = 0`, also
  `ψᵢ' = 0`); it is read on the interior of the overlap of the supports, the open set where
  both are positive (`psi_spec`). What it is for is the sign of `ψ₁'ψ₂ - ψ₁ψ₂'`: `> 0` on the
  overlap, `0` off it (`costT_lt`).
* The book's expansion is the second-order truncation of the exact formula of step 5 (its
  remainder is in fact `O(s⁴)`; the limit form is `costT_expansion`); the exact formula shows
  that the cost drops for every `s ≠ 0`, and smallness of `s` is needed only for admissibility
  (step 7).
* `cost(g₀) = π` (TeX 7382) holds only on an interval of length `π/3`; on `[t₁, t₂]` the cost of
  the arc is `3(t₂ - t₁)`.
* `σ_i = g_s e_i` (TeX 7385) should be `σ_i = g_s s_i*`, the multi-curve of the deformed disk
  (as in Remark 8.2.8, `σ_j = exp(Js₀) Ψ_s exp(Jt) s_j*`).
* The admissibility of the competitor is asserted in two sentences (TeX 7384–7390); steps 7–10
  carry it out along the book's lines: positive curvatures, the reparametrization to
  `det X = 1`, the control through Theorem 3.4.2, and the splice into the trajectory.
-/

@[expose] public section

namespace SmoothedPolygons

open Set MeasureTheory Filter Topology Matrix
open scoped ContDiff

/-! ### Integral curves on an interval -/

/-- `f` is the indefinite integral of `v` on `[a, b]`, entry by entry (for `a = 0`, `b = T` this
is `IsIntegralCurve f v T`). -/
private def IC (f v : ℝ → Mat2) (a b : ℝ) : Prop :=
  ∀ i j, IntervalIntegrable (fun s ↦ v s i j) volume a b ∧
    ∀ t ∈ Icc a b, f t i j = f a i j + ∫ s in a..t, v s i j

/-- Integral curves on adjacent intervals glue. -/
private lemma IC.trans {f v : ℝ → Mat2} {a b c : ℝ} (h₁ : IC f v a b) (h₂ : IC f v b c)
    (hab : a ≤ b) : IC f v a c := by
  intro i j
  refine ⟨(h₁ i j).1.trans (h₂ i j).1, fun t ht ↦ ?_⟩
  rcases le_total t b with htb | hbt
  · exact (h₁ i j).2 t ⟨ht.1, htb⟩
  · have hI : IntervalIntegrable (fun s ↦ v s i j) volume b t :=
      (h₂ i j).1.mono_set (uIcc_subset_uIcc left_mem_uIcc (Icc_subset_uIcc ⟨hbt, ht.2⟩))
    rw [(h₂ i j).2 t ⟨hbt, ht.2⟩, (h₁ i j).2 b ⟨hab, le_rfl⟩, add_assoc,
      intervalIntegral.integral_add_adjacent_intervals (h₁ i j).1 hI]

/-- An integral curve on `[a, b]` is one on every subinterval. -/
private lemma IC.mono {f v : ℝ → Mat2} {a b c d : ℝ} (h : IC f v a b) (hac : a ≤ c)
    (hcd : c ≤ d) (hdb : d ≤ b) : IC f v c d := by
  intro i j
  have hsub : ∀ x y, a ≤ x → x ≤ b → a ≤ y → y ≤ b →
      IntervalIntegrable (fun s ↦ v s i j) volume x y := fun x y hx hx' hy hy' ↦
    (h i j).1.mono_set (by
      rw [uIcc_of_le (hac.trans (hcd.trans hdb))]
      exact uIcc_subset_Icc ⟨hx, hx'⟩ ⟨hy, hy'⟩)
  refine ⟨hsub c d hac (hcd.trans hdb) (hac.trans hcd) hdb, fun t ht ↦ ?_⟩
  have h1 := (h i j).2 t ⟨hac.trans ht.1, ht.2.trans hdb⟩
  have h2 := (h i j).2 c ⟨hac, hcd.trans hdb⟩
  have h3 := intervalIntegral.integral_interval_sub_left
    (hsub a t le_rfl (hac.trans (hcd.trans hdb)) (hac.trans ht.1) (ht.2.trans hdb))
    (hsub a c le_rfl (hac.trans (hcd.trans hdb)) hac (hcd.trans hdb))
  linarith

/-- Change `f` on `[a, b]` and `v` on a null subset of `(a, b)`. -/
private lemma IC.congr_ae {f v f' v' : ℝ → Mat2} {a b : ℝ} (h : IC f v a b) (hab : a ≤ b)
    (hf : ∀ t ∈ Icc a b, f' t = f t) (hv : ∀ᵐ t, t ∈ Ioo a b → v' t = v t) : IC f' v' a b := by
  have hv' : ∀ᵐ t, t ∈ Ioc a b → v' t = v t := by
    filter_upwards [hv, (countable_singleton b).ae_notMem volume] with t h1 h2 ht
    exact h1 ⟨ht.1, lt_of_le_of_ne ht.2 h2⟩
  intro i j
  refine ⟨(h i j).1.congr_ae ?_, fun t ht ↦ ?_⟩
  · rw [uIoc_of_le hab, Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hv'] with x hx hx'
    rw [hx hx']
  · rw [hf t ht, hf a ⟨le_rfl, hab⟩, (h i j).2 t ht]
    congr 1
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hv'] with x hx hx'
    rw [uIoc_of_le ht.1] at hx'
    rw [hx ⟨hx'.1, hx'.2.trans ht.2⟩]

/-- Change `f` on `[a, b]` and `v` off `(a, b)`. -/
private lemma IC.congr {f v f' v' : ℝ → Mat2} {a b : ℝ} (h : IC f v a b) (hab : a ≤ b)
    (hf : ∀ t ∈ Icc a b, f' t = f t) (hv : ∀ t ∈ Ioo a b, v' t = v t) : IC f' v' a b :=
  h.congr_ae hab hf (Filter.Eventually.of_forall hv)

/-- Time shift by `d`. -/
private lemma IC.shift {f v : ℝ → Mat2} {a b : ℝ} (h : IC f v a b) (d : ℝ) :
    IC (fun t ↦ f (t - d)) (fun t ↦ v (t - d)) (a + d) (b + d) := by
  intro i j
  refine ⟨(h i j).1.comp_sub_right d, fun t ht ↦ ?_⟩
  have e := (h i j).2 (t - d) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  simp only [add_sub_cancel_right]
  rw [e, intervalIntegral.integral_comp_sub_right (fun s ↦ v s i j) d, add_sub_cancel_right]

/-- Left multiplication by a constant matrix. -/
private lemma IC.const_mul {f v : ℝ → Mat2} {a b : ℝ} (h : IC f v a b) (C : Mat2) :
    IC (fun t ↦ C * f t) (fun t ↦ C * v t) a b := by
  intro i j
  have hi : ∀ k, IntervalIntegrable (fun s ↦ C i k * v s k j) volume a b := fun k ↦
    (h k j).1.const_mul (C i k)
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨(hi 0).add (hi 1), fun t ht ↦ ?_⟩
  have hsub := uIcc_subset_uIcc left_mem_uIcc (Icc_subset_uIcc ht)
  rw [intervalIntegral.integral_add ((hi 0).mono_set hsub) ((hi 1).mono_set hsub),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, (h 0 j).2 t ht,
    (h 1 j).2 t ht]
  ring

/-- `IsIntegralCurve f v T` is `IC f v 0 T`. -/
private lemma IC.of_isIntegralCurve {f v : ℝ → Mat2} {T : ℝ} (h : IsIntegralCurve f v T) :
    IC f v 0 T := h

/-! ### The functions `ψ₁, ψ₂`

The fixed pair `ψ₁ + iψ₂ = ρ e^{iθ}` on `[0, L]`: `ρ` (`amp`) is a smooth plateau bump, positive
exactly on `(L/6, 5L/6)` and `1` on `[L/3, 2L/3]`; `θ` (`ang`) is `π/2` up to `L/3`, `0` from
`2L/3` on, and `θ' = -(π/2) φ / ∫ φ < 0` on `(L/3, 2L/3)` for a bump `φ` (`bump`). -/

/-- The bump `φ`, smooth and positive exactly on `(L/3, 2L/3)`. -/
private noncomputable def bump (L t : ℝ) : ℝ :=
  expNegInvGlue (t - L / 3) * expNegInvGlue (2 * L / 3 - t)

/-- `φ` is smooth. -/
private lemma bump_contDiff (L : ℝ) : ContDiff ℝ ∞ (bump L) :=
  (expNegInvGlue.contDiff.comp (contDiff_id.sub contDiff_const)).mul
    (expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id))

/-- `φ ≥ 0`. -/
private lemma bump_nonneg (L t : ℝ) : 0 ≤ bump L t :=
  mul_nonneg (expNegInvGlue.nonneg _) (expNegInvGlue.nonneg _)

/-- `φ` vanishes off `(L/3, 2L/3)`. -/
private lemma bump_eq_zero {L t : ℝ} (h : t ≤ L / 3 ∨ 2 * L / 3 ≤ t) : bump L t = 0 := by
  rcases h with h | h
  · simp [bump, expNegInvGlue.zero_of_nonpos (by linarith : t - L / 3 ≤ 0)]
  · simp [bump, expNegInvGlue.zero_of_nonpos (by linarith : 2 * L / 3 - t ≤ 0)]

/-- `φ` is positive on `(L/3, 2L/3)`. -/
private lemma bump_pos {L t : ℝ} (h₁ : L / 3 < t) (h₂ : t < 2 * L / 3) : 0 < bump L t :=
  mul_pos (expNegInvGlue.pos_of_pos (by linarith)) (expNegInvGlue.pos_of_pos (by linarith))

/-- `∫₀ᴸ φ > 0`. -/
private lemma integral_bump_pos {L : ℝ} (hL : 0 < L) : 0 < ∫ x in (0 : ℝ)..L, bump L x := by
  have hc : Continuous (bump L) := (bump_contDiff L).continuous
  refine lt_of_lt_of_le (intervalIntegral.intervalIntegral_pos_of_pos_on
    (hc.intervalIntegrable _ _) (fun x hx ↦ bump_pos hx.1 hx.2) (by linarith : L / 3 < 2 * L / 3))
    (intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith) ?_
      (hc.intervalIntegrable _ _))
  exact Filter.Eventually.of_forall fun x ↦ bump_nonneg L x

/-- The amplitude `ρ = |ψ|`: smooth, `ρ = 1` on `[L/3, 2L/3]`, `ρ > 0` exactly on `(L/6, 5L/6)`. -/
private noncomputable def amp (L t : ℝ) : ℝ :=
  Real.smoothTransition ((t - L / 6) / (L / 6)) *
    Real.smoothTransition ((5 * L / 6 - t) / (L / 6))

/-- `ρ` is smooth. -/
private lemma amp_contDiff (L : ℝ) : ContDiff ℝ ∞ (amp L) := by
  unfold amp; fun_prop

/-- `ρ ≥ 0`. -/
private lemma amp_nonneg (L t : ℝ) : 0 ≤ amp L t :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

/-- `ρ` vanishes off `(L/6, 5L/6)`. -/
private lemma amp_eq_zero {L t : ℝ} (hL : 0 < L) (h : t ≤ L / 6 ∨ 5 * L / 6 ≤ t) :
    amp L t = 0 := by
  rcases h with h | h
  · rw [amp, Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith)
      (by linarith)), zero_mul]
  · rw [amp, Real.smoothTransition.zero_of_nonpos (x := (5 * L / 6 - t) / (L / 6))
      (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)), mul_zero]

/-- `ρ = 1` on `[L/3, 2L/3]`. -/
private lemma amp_eq_one {L t : ℝ} (hL : 0 < L) (h₁ : L / 3 ≤ t) (h₂ : t ≤ 2 * L / 3) :
    amp L t = 1 := by
  rw [amp, Real.smoothTransition.one_of_one_le, Real.smoothTransition.one_of_one_le, mul_one]
  · rw [le_div_iff₀ (by linarith)]; linarith
  · rw [le_div_iff₀ (by linarith)]; linarith

/-- `ρ' = 0` off `[L/6, 5L/6]` and on `(L/3, 2L/3)`. -/
private lemma deriv_amp_eq_zero {L t : ℝ} (hL : 0 < L)
    (h : t < L / 6 ∨ 5 * L / 6 < t ∨ (L / 3 < t ∧ t < 2 * L / 3)) : deriv (amp L) t = 0 := by
  rcases h with h | h | h
  · have : amp L =ᶠ[𝓝 t] fun _ ↦ 0 := by
      filter_upwards [Iio_mem_nhds h] with x hx using amp_eq_zero hL (Or.inl hx.le)
    rw [this.deriv_eq, deriv_const]
  · have : amp L =ᶠ[𝓝 t] fun _ ↦ 0 := by
      filter_upwards [Ioi_mem_nhds h] with x hx using amp_eq_zero hL (Or.inr hx.le)
    rw [this.deriv_eq, deriv_const]
  · have : amp L =ᶠ[𝓝 t] fun _ ↦ 1 := by
      filter_upwards [Ioo_mem_nhds h.1 h.2] with x hx using amp_eq_one hL hx.1.le hx.2.le
    rw [this.deriv_eq, deriv_const]

/-- `θ' = -(π/2) φ / ∫₀ᴸ φ`, negative exactly on `(L/3, 2L/3)`. -/
private noncomputable def angD (L t : ℝ) : ℝ :=
  -(Real.pi / 2) / (∫ x in (0 : ℝ)..L, bump L x) * bump L t

/-- The angle `θ(t) = π/2 + ∫₀ᵗ θ'`, decreasing from `π/2` to `0` on `[L/3, 2L/3]`. -/
private noncomputable def ang (L t : ℝ) : ℝ := Real.pi / 2 + ∫ x in (0 : ℝ)..t, angD L x

/-- `θ'` is smooth. -/
private lemma angD_contDiff (L : ℝ) : ContDiff ℝ ∞ (angD L) :=
  contDiff_const.mul (bump_contDiff L)

/-- `θ` has derivative `θ'`. -/
private lemma hasDerivAt_ang (L t : ℝ) : HasDerivAt (ang L) (angD L t) t :=
  (((angD_contDiff L).continuous.integral_hasStrictDerivAt 0 t).hasDerivAt).const_add _

/-- `θ` is smooth. -/
private lemma ang_contDiff (L : ℝ) : ContDiff ℝ ∞ (ang L) := by
  refine contDiff_infty_iff_deriv.2 ⟨fun t ↦ (hasDerivAt_ang L t).differentiableAt, ?_⟩
  rw [show deriv (ang L) = angD L from funext fun t ↦ (hasDerivAt_ang L t).deriv]
  exact angD_contDiff L

/-- `θ' ≤ 0`. -/
private lemma angD_nonpos {L : ℝ} (hL : 0 < L) (t : ℝ) : angD L t ≤ 0 :=
  mul_nonpos_of_nonpos_of_nonneg (div_neg_of_neg_of_pos (by linarith [Real.pi_pos])
    (integral_bump_pos hL)).le (bump_nonneg L t)

/-- `θ' < 0` on `(L/3, 2L/3)`. -/
private lemma angD_neg {L t : ℝ} (hL : 0 < L) (h₁ : L / 3 < t) (h₂ : t < 2 * L / 3) :
    angD L t < 0 :=
  mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos (by linarith [Real.pi_pos])
    (integral_bump_pos hL)) (bump_pos h₁ h₂)

/-- `θ' = 0` off `(L/3, 2L/3)`. -/
private lemma angD_eq_zero {L t : ℝ} (h : t ≤ L / 3 ∨ 2 * L / 3 ≤ t) : angD L t = 0 := by
  rw [angD, bump_eq_zero h, mul_zero]

/-- `∫₀ᴸ θ' = -π/2`. -/
private lemma integral_angD {L : ℝ} (hL : 0 < L) :
    ∫ x in (0 : ℝ)..L, angD L x = -(Real.pi / 2) := by
  simp only [angD]
  rw [intervalIntegral.integral_const_mul, div_mul_cancel₀ _ (integral_bump_pos hL).ne']

/-- `θ = π/2` on `(-∞, L/3]`. -/
private lemma ang_of_le {L t : ℝ} (hL : 0 < L) (ht : t ≤ L / 3) : ang L t = Real.pi / 2 := by
  rw [ang, add_eq_left]
  rw [intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun x hx ↦ angD_eq_zero
    (Or.inl (hx.2.trans (sup_le (by linarith) ht)))]
  simp

/-- `θ = 0` on `[2L/3, ∞)`. -/
private lemma ang_of_ge {L t : ℝ} (hL : 0 < L) (ht : 2 * L / 3 ≤ t) : ang L t = 0 := by
  have hc : Continuous (angD L) := (angD_contDiff L).continuous
  rw [ang, ← intervalIntegral.integral_add_adjacent_intervals (b := L) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _), integral_angD hL]
  rw [intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun x hx ↦ angD_eq_zero
    (Or.inr ((le_inf (by linarith) ht).trans hx.1))]
  simp

/-- `0 ≤ θ ≤ π/2`. -/
private lemma ang_mem {L : ℝ} (hL : 0 < L) (t : ℝ) : 0 ≤ ang L t ∧ ang L t ≤ Real.pi / 2 := by
  have hanti : Antitone (ang L) :=
    antitone_of_hasDerivAt_nonpos (hasDerivAt_ang L) (angD_nonpos hL)
  constructor
  · rcases le_total t (2 * L / 3) with h | h
    · rw [← ang_of_ge hL (le_refl (2 * L / 3))]; exact hanti h
    · rw [ang_of_ge hL h]
  · rcases le_total t (L / 3) with h | h
    · rw [ang_of_le hL h]
    · rw [← ang_of_le hL (le_refl (L / 3))]; exact hanti h

/-- `ψ₁ = ρ cos θ`. -/
private noncomputable def psi1 (L t : ℝ) : ℝ := amp L t * Real.cos (ang L t)

/-- `ψ₂ = ρ sin θ`. -/
private noncomputable def psi2 (L t : ℝ) : ℝ := amp L t * Real.sin (ang L t)

/-- `ρ` has derivative `ρ'`. -/
private lemma hasDerivAt_amp (L t : ℝ) : HasDerivAt (amp L) (deriv (amp L) t) t :=
  ((amp_contDiff L).differentiable (by simp) t).hasDerivAt

/-- `ψ₁' = ρ' cos θ - ρ θ' sin θ`. -/
private lemma hasDerivAt_psi1 (L t : ℝ) : HasDerivAt (psi1 L)
    (deriv (amp L) t * Real.cos (ang L t) - amp L t * Real.sin (ang L t) * angD L t) t :=
  ((hasDerivAt_amp L t).mul (hasDerivAt_ang L t).cos).congr_deriv (by ring)

/-- `ψ₂' = ρ' sin θ + ρ θ' cos θ`. -/
private lemma hasDerivAt_psi2 (L t : ℝ) : HasDerivAt (psi2 L)
    (deriv (amp L) t * Real.sin (ang L t) + amp L t * Real.cos (ang L t) * angD L t) t :=
  ((hasDerivAt_amp L t).mul (hasDerivAt_ang L t).sin).congr_deriv (by ring)

/-- `ψ₁'ψ₂ - ψ₁ψ₂' = -ρ²θ'`. -/
private lemma psi_wronskian (L t : ℝ) :
    deriv (psi1 L) t * psi2 L t - psi1 L t * deriv (psi2 L) t = -(amp L t ^ 2 * angD L t) := by
  rw [(hasDerivAt_psi1 L t).deriv, (hasDerivAt_psi2 L t).deriv, psi1, psi2]
  linear_combination (-(amp L t ^ 2 * angD L t)) * Real.sin_sq_add_cos_sq (ang L t)

/-- **The book's choice of `ψ₁, ψ₂`** (TeX 7375–7378), read on the interior of the overlap of the
supports: `ψ₁, ψ₂` are smooth, nonnegative, supported in `[L/6, 5L/6] ⊂ (0, L)`, and where both are
positive, `ψ₁' > 0` and `ψ₂' < 0`. -/
private lemma psi_spec {L : ℝ} (hL : 0 < L) :
    ContDiff ℝ ∞ (psi1 L) ∧ ContDiff ℝ ∞ (psi2 L) ∧
      (∀ t, 0 ≤ psi1 L t ∧ 0 ≤ psi2 L t) ∧
      (∀ t, t ≤ L / 6 ∨ 5 * L / 6 ≤ t → psi1 L t = 0 ∧ psi2 L t = 0) ∧
      ∀ t, 0 < psi1 L t → 0 < psi2 L t → 0 < deriv (psi1 L) t ∧ deriv (psi2 L) t < 0 := by
  have ha := amp_contDiff L
  have hθ := ang_contDiff L
  refine ⟨by unfold psi1; fun_prop, by unfold psi2; fun_prop, fun t ↦ ?_, fun t ht ↦ ?_,
    fun t h1 h2 ↦ ?_⟩
  · obtain ⟨h0, hπ⟩ := ang_mem hL t
    refine ⟨mul_nonneg (amp_nonneg L t) (Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos],
      hπ⟩), mul_nonneg (amp_nonneg L t) (Real.sin_nonneg_of_nonneg_of_le_pi h0
        (by linarith [Real.pi_pos]))⟩
  · simp [psi1, psi2, amp_eq_zero hL ht]
  · -- on the overlap, `θ ∈ (0, π/2)`, so `t ∈ (L/3, 2L/3)`, where `ρ = 1` and `ρ' = 0`
    have ht₁ : L / 3 < t := by
      by_contra h
      have : Real.cos (ang L t) = 0 := by rw [ang_of_le hL (not_lt.1 h), Real.cos_pi_div_two]
      simp [psi1, this] at h1
    have ht₂ : t < 2 * L / 3 := by
      by_contra h
      have : Real.sin (ang L t) = 0 := by rw [ang_of_ge hL (not_lt.1 h), Real.sin_zero]
      simp [psi2, this] at h2
    have hρ : amp L t = 1 := amp_eq_one hL ht₁.le ht₂.le
    have hρ' : deriv (amp L) t = 0 := deriv_amp_eq_zero hL (Or.inr (Or.inr ⟨ht₁, ht₂⟩))
    have hc : 0 < Real.cos (ang L t) := by
      have := h1; rw [psi1, hρ, one_mul] at this; exact this
    have hs : 0 < Real.sin (ang L t) := by
      have := h2; rw [psi2, hρ, one_mul] at this; exact this
    have hd := angD_neg hL ht₁ ht₂
    rw [(hasDerivAt_psi1 L t).deriv, (hasDerivAt_psi2 L t).deriv, hρ, hρ']
    constructor <;> nlinarith [mul_pos hc (neg_pos.2 hd), mul_pos hs (neg_pos.2 hd)]


/-! ### Rotations -/

/-- The rotation `exp(Jθ)`. -/
private noncomputable def rot (θ : ℝ) : Mat2 :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

/-- `exp(J · 0) = I`. -/
private lemma rot_zero : rot 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rot]

/-- `det exp(Jθ) = 1`. -/
private lemma det_rot (θ : ℝ) : (rot θ).det = 1 := by
  rw [rot, Matrix.det_fin_two_of]; nlinarith [Real.cos_sq_add_sin_sq θ]

/-- `exp(Jθ) exp(-Jθ) = I`. -/
private lemma rot_mul_rot_neg (θ : ℝ) : rot θ * rot (-θ) = 1 := by
  have h := Real.cos_sq_add_sin_sq θ
  rw [rot, rot, Real.cos_neg, Real.sin_neg, Matrix.mul_fin_two, Matrix.one_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
    first | linear_combination h | ring

/-- `exp(-Jθ) exp(Jθ) = I`. -/
private lemma rot_neg_mul_rot (θ : ℝ) : rot (-θ) * rot θ = 1 := by
  simpa using rot_mul_rot_neg (-θ)

/-- `J` commutes with `exp(Jθ)`. -/
private lemma J_mul_rot (θ : ℝ) : J * rot θ = rot θ * J := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rot, J, Matrix.mul_apply, Fin.sum_univ_two]

/-- `exp(Jθ)` is the matrix exponential of `θJ` (Lemma A.6.4, `lemmaA_6_4`, with `det J = 1`). -/
private lemma rot_eq_exp (θ : ℝ) : rot θ = NormedSpace.exp (θ • J) := by
  have htr : J.trace = 0 := by simp [J, Matrix.trace_fin_two]
  have hdet : J.det = 1 := by simp [J, Matrix.det_fin_two]
  rw [((lemmaA_6_4 J htr).2 θ).2.1 (by rw [hdet]; exact one_pos), hdet, Real.sqrt_one, mul_one,
    div_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp [rot, J]

/-- `(exp(Jα))' = α' exp(Jα) J`. -/
private lemma hasDerivAt_rot {α : ℝ → ℝ} {A t : ℝ} (h : HasDerivAt α A t) :
    HasDerivAtEntrywise (fun τ ↦ rot (α τ)) (A • (rot (α t) * J)) t := by
  rw [hasDerivAtEntrywise_fin_two_iff]
  simp only [rot, J, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.smul_apply, Matrix.mul_apply,
    Fin.sum_univ_two, smul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (h.cos).congr_deriv (by simp; ring)
  · exact (h.sin.neg).congr_deriv (by simp; ring)
  · exact (h.sin).congr_deriv (by simp; ring)
  · exact (h.cos).congr_deriv (by simp; ring)

/-- On a circular arc (`X ≡ J` on `[t₁, t₂]`), `g(t) = g(t₁) exp(J(t - t₁))` (`g' = gJ`). -/
private lemma arc_eq {T t₁ t₂ : ℝ} {g X : ℝ → Mat2}
    (hgI : IsIntegralCurve g (fun t ↦ g t * X t) T) (h₁ : 0 ≤ t₁) (h₁₂ : t₁ ≤ t₂)
    (h₂ : t₂ ≤ T) (hX : ∀ t ∈ Icc t₁ t₂, X t = J) :
    ∀ t ∈ Icc t₁ t₂, g t = g t₁ * rot (t - t₁) := by
  have hIC : IC g (fun t ↦ g t * J) t₁ t₂ :=
    ((IC.of_isIntegralCurve hgI).mono h₁ h₁₂ h₂).congr h₁₂ (fun _ _ ↦ rfl)
      fun t ht ↦ by rw [hX t (Ioo_subset_Icc_self ht)]
  have hgc : ContinuousOn g (Icc t₁ t₂) := Matrix.continuousOn_of_eq_add_integral hIC
  have hd : ∀ t ∈ Icc t₁ t₂, HasDerivWithinAtEntrywise g (g t * J) (Icc t₁ t₂) t := fun t ht ↦
    Matrix.hasDerivWithinAtEntrywise_of_eq_add_integral hIC ht
      ((hgc.mul continuousOn_const) t ht)
  have hY : ∀ t, HasDerivAtEntrywise (fun τ ↦ g t₁ * rot (τ - t₁)) (g t₁ * rot (t - t₁) * J) t :=
    fun t ↦ by
      have := (hasDerivAt_rot ((hasDerivAt_id t).sub_const t₁)).const_mul (g t₁)
      simpa [Matrix.mul_assoc] using this
  have hYc : ContinuousOn (fun τ ↦ g t₁ * rot (τ - t₁)) (Icc t₁ t₂) := fun t _ ↦
    (HasDerivAtEntrywise.continuousAt (hY t)).continuousWithinAt
  intro t ht
  exact Matrix.ODE_solution_unique_mul_right (A := fun _ ↦ J) continuousOn_const hgc
    (fun t ht ↦ hd t (Ico_subset_Icc_self ht)) hYc
    (fun t _ ↦ (hY t).hasDerivWithinAtEntrywise) (by simp [rot_zero]) ht

/-- `⟨J, exp(-Jt) M exp(Jt)⟩ = ⟨J, M⟩`: the trace form is invariant under conjugation by the
rotations, which commute with `J`. -/
private lemma traceForm_J_conj (M : Mat2) (t : ℝ) :
    traceForm J (rot (-t) * M * rot t) = traceForm J M := by
  have h : rot t * (J * (rot (-t) * M)) = J * M := by
    rw [← Matrix.mul_assoc, ← J_mul_rot, Matrix.mul_assoc, ← Matrix.mul_assoc (rot t),
      rot_mul_rot_neg, Matrix.one_mul]
  simp only [traceForm]
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, h]

/-! ### The deformation `g_s = Ψ_s exp(Jt)`, as functions of `(s, t)` -/

/-- `sinh(s ρ(t))`. -/
private noncomputable def fσ (L : ℝ) (p : ℝ × ℝ) : ℝ := Real.sinh (p.1 * amp L p.2)

/-- `cosh(s ρ(t))`. -/
private noncomputable def fc (L : ℝ) (p : ℝ × ℝ) : ℝ := Real.cosh (p.1 * amp L p.2)

/-- `s ρ'(t)`. -/
private noncomputable def fR (L : ℝ) (p : ℝ × ℝ) : ℝ := p.1 * deriv (amp L) p.2

/-- The book's `S(t) = [[ψ₁, ψ₂], [ψ₂, -ψ₁]] = ρ(t) E(θ(t))`. -/
private noncomputable def fS (L t : ℝ) : Mat2 := !![psi1 L t, psi2 L t; psi2 L t, -psi1 L t]

/-- `Ψ_s(t) = cosh(sρ) I + sinh(sρ) E(θ)`, with `E(θ) = [[cos θ, sin θ], [sin θ, -cos θ]]`; it is
`exp(s S(t))` (`fΨ_eq_exp`). -/
private noncomputable def fΨ (L : ℝ) (p : ℝ × ℝ) : Mat2 :=
  !![fc L p + fσ L p * Real.cos (ang L p.2), fσ L p * Real.sin (ang L p.2);
    fσ L p * Real.sin (ang L p.2), fc L p - fσ L p * Real.cos (ang L p.2)]

/-- `Ψ_s⁻¹ Ψ_s' = sρ' E(θ) + sinh(sρ) cosh(sρ) θ' F(θ) + sinh²(sρ) θ' J`, with
`F(θ) = E'(θ) = [[-sin θ, cos θ], [cos θ, sin θ]]` (`hasDerivAt_fΨ`). -/
private noncomputable def fW (L : ℝ) (p : ℝ × ℝ) : Mat2 :=
  !![fR L p * Real.cos (ang L p.2) - fσ L p * fc L p * angD L p.2 * Real.sin (ang L p.2),
      fR L p * Real.sin (ang L p.2) + fσ L p * fc L p * angD L p.2 * Real.cos (ang L p.2) -
        fσ L p ^ 2 * angD L p.2;
    fR L p * Real.sin (ang L p.2) + fσ L p * fc L p * angD L p.2 * Real.cos (ang L p.2) +
        fσ L p ^ 2 * angD L p.2,
      -(fR L p * Real.cos (ang L p.2)) + fσ L p * fc L p * angD L p.2 * Real.sin (ang L p.2)]

/-- `X_s = g_s⁻¹ g_s' = exp(-Jt) (Ψ_s⁻¹Ψ_s' + J) exp(Jt)` (`hasDerivAt_fg`), in the book's time
`t`; `det X_s` need not be `1`. -/
private noncomputable def fX (L : ℝ) (p : ℝ × ℝ) : Mat2 := rot (-p.2) * (fW L p + J) * rot p.2

/-- `cosh² = sinh² + 1`. -/
private lemma fc_sq (L : ℝ) (p : ℝ × ℝ) : fc L p ^ 2 = fσ L p ^ 2 + 1 := Real.cosh_sq _

/-- `det Ψ_s = 1`. -/
private lemma det_fΨ (L : ℝ) (p : ℝ × ℝ) : (fΨ L p).det = 1 := by
  rw [fΨ, Matrix.det_fin_two_of]
  linear_combination fc_sq L p - fσ L p ^ 2 * Real.cos_sq_add_sin_sq (ang L p.2)

/-- `Ψ_s(t) = exp(s S(t))`, the book's definition of the deformation: `S ∈ 𝔰𝔩₂(ℝ)` with
`det S = -ρ²`, so Lemma A.6.4 (`lemmaA_6_4`) gives `exp(sS) = cosh(sρ) I + (sinh(sρ)/ρ) S`. -/
private lemma fΨ_eq_exp (L s t : ℝ) : fΨ L (s, t) = NormedSpace.exp (s • fS L t) := by
  have htr : (fS L t).trace = 0 := by simp [fS, Matrix.trace_fin_two]
  have hdet : (fS L t).det = -(amp L t ^ 2) := by
    rw [fS, Matrix.det_fin_two_of, psi1, psi2]
    linear_combination (-(amp L t) ^ 2) * Real.cos_sq_add_sin_sq (ang L t)
  rcases eq_or_lt_of_le (amp_nonneg L t) with h0 | hpos
  · have hS : fS L t = 0 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [fS, psi1, psi2, ← h0]
    rw [hS, smul_zero, NormedSpace.exp_zero]
    ext i j; fin_cases i <;> fin_cases j <;> simp [fΨ, fσ, fc, ← h0]
  · have hd : (fS L t).det < 0 := by rw [hdet]; nlinarith
    rw [((lemmaA_6_4 (fS L t) htr).2 s).1 hd, hdet, neg_neg, Real.sqrt_sq (amp_nonneg L t)]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [fΨ, fσ, fc, fS, psi1, psi2] <;> field_simp
    ring

/-- `Ψ_s' = Ψ_s W` with `W = Ψ_s⁻¹Ψ_s'` the matrix `fW`. -/
private lemma hasDerivAt_fΨ (L s t : ℝ) :
    HasDerivAtEntrywise (fun x ↦ fΨ L (s, x)) (fΨ L (s, t) * fW L (s, t)) t := by
  have hb : HasDerivAt (fun x ↦ s * amp L x) (s * deriv (amp L) t) t :=
    (hasDerivAt_amp L t).const_mul s
  have hc := hb.cosh
  have hσ := hb.sinh
  have hC := (hasDerivAt_ang L t).cos
  have hS := (hasDerivAt_ang L t).sin
  have h1 := Real.cosh_sq (s * amp L t)
  have h2 := Real.cos_sq_add_sin_sq (ang L t)
  rw [hasDerivAtEntrywise_fin_two_iff]
  simp only [fΨ, fW, fσ, fc, fR, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.mul_apply,
    Fin.sum_univ_two]
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (hc.add (hσ.mul hC)).congr_deriv ?_
    linear_combination (Real.sin (ang L t) * Real.sinh (s * amp L t) * angD L t) * h1 -
      (s * deriv (amp L) t * Real.sinh (s * amp L t)) * h2
  · refine (hσ.mul hS).congr_deriv ?_
    linear_combination (-(Real.cos (ang L t) * Real.sinh (s * amp L t) * angD L t)) * h1 -
      (Real.cosh (s * amp L t) * Real.sinh (s * amp L t) ^ 2 * angD L t) * h2
  · refine (hσ.mul hS).congr_deriv ?_
    linear_combination (-(Real.cos (ang L t) * Real.sinh (s * amp L t) * angD L t)) * h1 +
      (Real.cosh (s * amp L t) * Real.sinh (s * amp L t) ^ 2 * angD L t) * h2
  · refine (hc.sub (hσ.mul hC)).congr_deriv ?_
    linear_combination (-(Real.sin (ang L t) * Real.sinh (s * amp L t) * angD L t)) * h1 -
      (s * deriv (amp L) t * Real.sinh (s * amp L t)) * h2

/-- **The product rule** (TeX 7355–7362): `g_s = Ψ_s exp(Jt)` has `g_s' = g_s X_s` with
`X_s = exp(-Jt) (Ψ_s⁻¹Ψ_s' + J) exp(Jt)`. -/
private lemma hasDerivAt_fg (L s t : ℝ) :
    HasDerivAtEntrywise (fun x ↦ fΨ L (s, x) * rot x) (fΨ L (s, t) * rot t * fX L (s, t)) t := by
  have h := (hasDerivAt_fΨ L s t).mul (hasDerivAt_rot (hasDerivAt_id' t))
  refine h.congr_deriv ?_
  have e : rot t * (rot (-t) * (fW L (s, t) + J) * rot t) = (fW L (s, t) + J) * rot t := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, rot_mul_rot_neg, Matrix.one_mul]
  rw [one_smul, show fΨ L (s, t) * rot t * fX L (s, t) = fΨ L (s, t) * (rot t * fX L (s, t)) from
    Matrix.mul_assoc _ _ _, fX, e, Matrix.add_mul, Matrix.mul_add, J_mul_rot, Matrix.mul_assoc]

/-- `⟨J, Ψ_s⁻¹Ψ_s'⟩ = -2 sinh²(sρ) θ'`. -/
private lemma traceForm_J_fW (L : ℝ) (p : ℝ × ℝ) :
    traceForm J (fW L p) = -2 * fσ L p ^ 2 * angD L p.2 := by
  simp only [traceForm, J, fW, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

/-- **The product rule for the cost** (TeX 7355–7362):
`⟨J, g_s⁻¹g_s'⟩ = ⟨J, J⟩ + ⟨J, Ψ_s⁻¹Ψ_s'⟩`. -/
private lemma traceForm_J_fX (L : ℝ) (p : ℝ × ℝ) :
    traceForm J (fX L p) = traceForm J J + traceForm J (fW L p) := by
  rw [fX, traceForm_J_conj, traceForm, traceForm, traceForm, Matrix.mul_add, Matrix.trace_add,
    add_comm]

/-- **The exact cost density** (TeX 7363–7373): with `r = |ψ| = ρ`,
`⟨J, Ψ_s⁻¹Ψ_s'⟩ = 2 (sinh(sr)/r)² (ψ₁'ψ₂ - ψ₁ψ₂')`, whose `s²` term is the book's
`2 s² (ψ₁'ψ₂ - ψ₁ψ₂')`. -/
private lemma traceForm_J_fW_eq (L s t : ℝ) :
    traceForm J (fW L (s, t)) = 2 * (Real.sinh (s * amp L t) / amp L t) ^ 2 *
      (deriv (psi1 L) t * psi2 L t - psi1 L t * deriv (psi2 L) t) := by
  rw [traceForm_J_fW, psi_wronskian, fσ]
  rcases eq_or_ne (amp L t) 0 with h | h
  · simp [h]
  · field_simp

/-- `X_s ∈ 𝔰𝔩₂(ℝ)`. -/
private lemma trace_fX (L : ℝ) (p : ℝ × ℝ) : (fX L p).trace = 0 := by
  rw [fX, Matrix.trace_mul_comm, ← Matrix.mul_assoc, rot_mul_rot_neg, Matrix.one_mul,
    Matrix.trace_add]
  simp [fW, J, Matrix.trace_fin_two]

/-- `det g_s = 1`. -/
private lemma det_fg (L : ℝ) (p : ℝ × ℝ) : (fΨ L p * rot p.2).det = 1 := by
  rw [Matrix.det_mul, det_fΨ, det_rot, one_mul]

/-- Where `sρ = 0` and `sρ' = 0` (in particular for `s = 0`, and off the support of `ρ`), the
deformation is trivial: `Ψ_s⁻¹Ψ_s' = 0`, `X_s = J`, `Ψ_s = I`. -/
private lemma f_trivial {L : ℝ} {p : ℝ × ℝ} (h₁ : p.1 * amp L p.2 = 0)
    (h₂ : p.1 * deriv (amp L) p.2 = 0) : fW L p = 0 ∧ fX L p = J ∧ fΨ L p = 1 := by
  have hσ : fσ L p = 0 := by rw [fσ, h₁, Real.sinh_zero]
  have hc : fc L p = 1 := by rw [fc, h₁, Real.cosh_zero]
  have hR : fR L p = 0 := h₂
  have hW : fW L p = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [fW, hσ, hR]
  refine ⟨hW, ?_, ?_⟩
  · rw [fX, hW, zero_add, Matrix.mul_assoc, J_mul_rot, ← Matrix.mul_assoc, rot_neg_mul_rot,
      Matrix.one_mul]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [fΨ, hσ, hc]

/-- Off `(L/6, 5L/6)` the deformation is trivial. -/
private lemma f_trivial_of_not_mem {L t : ℝ} (hL : 0 < L) (s : ℝ) (h : t < L / 6 ∨ 5 * L / 6 < t) :
    fX L (s, t) = J ∧ fΨ L (s, t) = 1 := by
  have := f_trivial (L := L) (p := (s, t))
    (by rw [amp_eq_zero hL (h.imp le_of_lt le_of_lt), mul_zero])
    (by rw [deriv_amp_eq_zero hL (h.imp id Or.inl), mul_zero])
  exact this.2

/-- `σ_j = g s_{2j}*` has `det(σ_j', σ_j'') = det(s_{2j}*, (det X · X + adj X · X') s_{2j}*)` when
`g' = gX`, `σ_j'' = g(X² + X') s_{2j}*` and `det g = 1`: the curvature of `σ_j` is positive iff
this is. -/
private lemma det2_curve (g X D : Mat2) (hg : g.det = 1) (e : Fin 2 → ℝ) :
    det2 (g *ᵥ (X *ᵥ e)) (g *ᵥ ((X * X + D) *ᵥ e)) =
      det2 e ((X.det • X + X.adjugate * D) *ᵥ e) := by
  have hdet2 : ∀ u w : Fin 2 → ℝ, det2 (g *ᵥ u) (g *ᵥ w) = g.det * det2 u w := fun u w ↦ by
    simp only [det2, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two]; ring
  rw [hdet2, hg, one_mul]
  simp only [det2, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.mul_apply,
    Matrix.add_apply, Matrix.smul_apply, Matrix.adjugate_fin_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.det_fin_two, smul_eq_mul]
  ring

/-! ### Smoothness in `(s, t)` and the curvatures -/

/-- `sinh(sρ)` is smooth in `(s, t)`. -/
private lemma fσ_contDiff (L : ℝ) : ContDiff ℝ ∞ (fσ L) :=
  (contDiff_fst.mul ((amp_contDiff L).comp contDiff_snd)).sinh

/-- `cosh(sρ)` is smooth in `(s, t)`. -/
private lemma fc_contDiff (L : ℝ) : ContDiff ℝ ∞ (fc L) :=
  (contDiff_fst.mul ((amp_contDiff L).comp contDiff_snd)).cosh

/-- `sρ'` is smooth in `(s, t)`. -/
private lemma fR_contDiff (L : ℝ) : ContDiff ℝ ∞ (fR L) :=
  contDiff_fst.mul ((contDiff_infty_iff_deriv.1 (amp_contDiff L)).2.comp contDiff_snd)

/-- The entries of `X_s(t)` are smooth in `(s, t)`. -/
private lemma fX_contDiff (L : ℝ) (i j : Fin 2) : ContDiff ℝ ∞ fun p ↦ fX L p i j := by
  have hσ := fσ_contDiff L
  have hc := fc_contDiff L
  have hR := fR_contDiff L
  have hθ : ContDiff ℝ ∞ fun p : ℝ × ℝ ↦ ang L p.2 := (ang_contDiff L).comp contDiff_snd
  have hθ' : ContDiff ℝ ∞ fun p : ℝ × ℝ ↦ angD L p.2 := (angD_contDiff L).comp contDiff_snd
  fin_cases i <;> fin_cases j <;>
    simp only [fX, fW, rot, J, Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
    fun_prop

/-- `X_s(t)` is continuous in `(s, t)`. -/
private lemma fX_continuous (L : ℝ) : Continuous (fX L) :=
  continuous_iff_entrywise.2 fun i j ↦ (fX_contDiff L i j).continuous

/-- The derivative `X_s'` of `X_s` in `t`. -/
private noncomputable def fD (L : ℝ) (p : ℝ × ℝ) : Mat2 :=
  Matrix.of fun i j ↦ fderiv ℝ (fun q ↦ fX L q i j) p (0, 1)

/-- `X_s'(t)` is continuous in `(s, t)`. -/
private lemma fD_continuous (L : ℝ) : Continuous (fD L) :=
  continuous_iff_entrywise.2 fun i j ↦
    ((fX_contDiff L i j).continuous_fderiv (by simp)).clm_apply continuous_const

/-- The partial derivative in `t` of a `C¹` function of `(s, t)`. -/
private lemma hasDerivAt_partial {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (s t : ℝ) :
    HasDerivAt (fun x ↦ F (s, x)) (fderiv ℝ F (s, t) (0, 1)) t :=
  ((hF.differentiable (by simp)) (s, t)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t s).prodMk (hasDerivAt_id t))

/-- `fD` is the derivative of `X_s` in `t`. -/
private lemma hasDerivAt_fX (L s t : ℝ) :
    HasDerivAtEntrywise (fun x ↦ fX L (s, x)) (fD L (s, t)) t := fun i j ↦
  hasDerivAt_partial (fX_contDiff L i j) s t

/-- At `s = 0` (the circle), `X = J` and `X' = 0`. -/
private lemma fX_zero (L t : ℝ) : fX L (0, t) = J :=
  (f_trivial (p := (0, t)) (zero_mul _) (zero_mul _)).2.1

/-- At `s = 0`, `X' = 0`. -/
private lemma fD_zero (L t : ℝ) : fD L (0, t) = 0 := by
  have hJ : (fun x ↦ fX L (0, x)) = fun _ ↦ J := funext fun x ↦ fX_zero L x
  have h := hasDerivAt_fX L 0 t
  rw [hJ] at h
  exact h.unique (hasDerivAtEntrywise_const J t)

/-- The curvature numerator `k_j(s, t) = det(s_{2j}*, (det X · X + adj X · X') s_{2j}*)` of the
curve `σ_j = g_s s_{2j}*` in the book's time `t`: `k_j = det(σ_j', σ_j'')` (`det2_curve`), so the
curvature of `σ_j` has the sign of `k_j`. -/
private noncomputable def fk (L : ℝ) (j : Fin 3) (p : ℝ × ℝ) : ℝ :=
  det2 (sixthRoot (2 * (j.val : ZMod 6)))
    (((fX L p).det • fX L p + (fX L p).adjugate * fD L p) *ᵥ sixthRoot (2 * (j.val : ZMod 6)))

/-- The curvature numerators are continuous in `(s, t)` (the book's "`C^∞` functions of `s` and
`t`"). -/
private lemma fk_continuous (L : ℝ) (j : Fin 3) : Continuous (fk L j) := by
  have hX := fX_continuous L
  have hc : Continuous fun p ↦ ((fX L p).det • fX L p + (fX L p).adjugate * fD L p) *ᵥ
      sixthRoot (2 * (j.val : ZMod 6)) :=
    ((hX.matrix_det.smul hX).add (hX.matrix_adjugate.mul (fD_continuous L))).matrix_mulVec
      continuous_const
  unfold fk det2
  exact (continuous_const.mul ((continuous_apply 1).comp hc)).sub
    (continuous_const.mul ((continuous_apply 0).comp hc))

/-- At `s = 0` (the circle), `k_j = 1`. -/
private lemma fk_zero (L : ℝ) (j : Fin 3) (t : ℝ) : fk L j (0, t) = 1 := by
  have hJ : J.det = 1 := by simp [J, Matrix.det_fin_two]
  rw [fk, fD_zero, fX_zero, hJ, one_smul, Matrix.mul_zero, add_zero]
  simp only [det2, sixthRoot, J, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  nlinarith [Real.cos_sq_add_sin_sq (Real.pi * ((2 * (j.val : ZMod 6)).val : ℝ) / 3)]

/-- The tube lemma: a continuous function of `(s, t)`, positive at `s = 0` on a compact set of
`t`, stays positive there for `s` near `0`. -/
private lemma eventually_pos {F : ℝ × ℝ → ℝ} (hF : Continuous F) {K : Set ℝ} (hK : IsCompact K)
    (h0 : ∀ t ∈ K, 0 < F (0, t)) : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ t ∈ K, 0 < F (s, t) :=
  hK.eventually_forall_of_forall_eventually fun t ht ↦
    hF.continuousAt.eventually (lt_mem_nhds (h0 t ht))

/-! ### The cost of the deformation -/

/-- The cost `-(3/2) ∫₀ᴸ ⟨J, g_s⁻¹ g_s'⟩ dt` of the deformed arc `g_s`, `t ∈ [0, L]`, in the
book's time `t` (the Cartan–Maurer form of eqn `eqn:cost`; it does not depend on the
parametrization, step 7 of `exists_deformedArc`). -/
private noncomputable def costT (L s : ℝ) : ℝ :=
  -(3 / 2) * ∫ t in (0 : ℝ)..L, traceForm J (fX L (s, t))

/-- `∫₀ᴸ ⟨J, X_s⟩ = -2L + ∫₀ᴸ ⟨J, Ψ_s⁻¹Ψ_s'⟩` (the product rule, `traceForm_J_fX`). -/
private lemma integral_traceForm_J_fX (L s : ℝ) :
    ∫ t in (0 : ℝ)..L, traceForm J (fX L (s, t)) =
      -2 * L + ∫ t in (0 : ℝ)..L, traceForm J (fW L (s, t)) := by
  have hJ : traceForm J J = -2 := by
    simp [traceForm, J, Matrix.trace_fin_two]; norm_num
  have hWc : Continuous fun t ↦ traceForm J (fW L (s, t)) := by
    simp only [traceForm_J_fW]
    exact (continuous_const.mul (((fσ_contDiff L).continuous.comp
      (continuous_const.prodMk continuous_id)).pow 2)).mul (angD_contDiff L).continuous
  simp only [traceForm_J_fX, hJ]
  rw [intervalIntegral.integral_add intervalIntegrable_const (hWc.intervalIntegrable _ _),
    intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm]

/-- **The cost formula** (TeX 7363–7373), exact: with `r = |ψ| = ρ`,
`cost(g_s) = 3L - 3 ∫₀ᴸ (sinh(sr)/r)² (ψ₁'ψ₂ - ψ₁ψ₂') dt`. Its `s²` term is the book's
`-3 s² ∫ (ψ₁'ψ₂ - ψ₁ψ₂')`; the book's expansion is its second-order truncation. -/
private lemma costT_eq (L s : ℝ) :
    costT L s = 3 * L - 3 * ∫ t in (0 : ℝ)..L, (Real.sinh (s * amp L t) / amp L t) ^ 2 *
      (deriv (psi1 L) t * psi2 L t - psi1 L t * deriv (psi2 L) t) := by
  rw [costT, integral_traceForm_J_fX, intervalIntegral.integral_congr (g := fun t ↦ 2 *
    ((Real.sinh (s * amp L t) / amp L t) ^ 2 *
      (deriv (psi1 L) t * psi2 L t - psi1 L t * deriv (psi2 L) t))) fun t _ ↦ by
        simp only; rw [traceForm_J_fW_eq]; ring, intervalIntegral.integral_const_mul]
  ring

/-- **The cost drops** (TeX 7374–7383): with the book's choice of `ψ` (`psi_spec`), the integrand
`(sinh(sr)/r)² (ψ₁'ψ₂ - ψ₁ψ₂')` of `costT_eq` is `≥ 0` (on the overlap of the supports by the
book's condition; off it one `ψᵢ` vanishes, and then so does `ψᵢ'`, at a minimum of `ψᵢ ≥ 0`), and
`> 0` on the overlap `(L/3, 2L/3)`, so `cost(g_s) < 3L = cost(g₀)` for every `s ≠ 0`. -/
private lemma costT_lt {L : ℝ} (hL : 0 < L) {s : ℝ} (hs : s ≠ 0) : costT L s < 3 * L := by
  obtain ⟨-, -, hnn, -, hbook⟩ := psi_spec hL
  set w : ℝ → ℝ := fun t ↦ deriv (psi1 L) t * psi2 L t - psi1 L t * deriv (psi2 L) t with hw_def
  -- `ψ₁'ψ₂ - ψ₁ψ₂' ≥ 0`
  have hw : ∀ t, 0 ≤ w t := by
    intro t
    rcases (hnn t).1.eq_or_lt with h1 | h1
    · have hd : deriv (psi1 L) t = 0 := IsLocalMin.deriv_eq_zero
        (Filter.Eventually.of_forall fun x ↦ by rw [← h1]; exact (hnn x).1)
      simp [hw_def, hd, ← h1]
    rcases (hnn t).2.eq_or_lt with h2 | h2
    · have hd : deriv (psi2 L) t = 0 := IsLocalMin.deriv_eq_zero
        (Filter.Eventually.of_forall fun x ↦ by rw [← h2]; exact (hnn x).2)
      simp [hw_def, hd, ← h2]
    obtain ⟨d1, d2⟩ := hbook t h1 h2
    simp only [hw_def]
    nlinarith [mul_pos d1 h2, mul_pos h1 (neg_pos.2 d2)]
  set f : ℝ → ℝ := fun t ↦ (Real.sinh (s * amp L t) / amp L t) ^ 2 * w t with hf_def
  have hf : ∀ t, f t = -(Real.sinh (s * amp L t) ^ 2 * angD L t) := fun t ↦ by
    have := traceForm_J_fW_eq L s t
    rw [traceForm_J_fW, fσ] at this
    simp only [hf_def, hw_def]
    linarith
  have hfc : Continuous f := by
    rw [show f = fun t ↦ -(Real.sinh (s * amp L t) ^ 2 * angD L t) from funext hf]
    have := (amp_contDiff L).continuous
    have := (angD_contDiff L).continuous
    fun_prop
  have hsinh : Real.sinh s ≠ 0 := fun h ↦ hs (Real.sinh_injective (h.trans Real.sinh_zero.symm))
  have hpos : ∀ t ∈ Ioo (L / 3) (2 * L / 3), 0 < f t := by
    intro t ht
    have hw' : 0 < w t := by
      simp only [hw_def]
      rw [psi_wronskian, amp_eq_one hL ht.1.le ht.2.le]
      linarith [angD_neg hL ht.1 ht.2]
    simp only [hf_def, amp_eq_one hL ht.1.le ht.2.le, mul_one, div_one]
    exact mul_pos (by positivity) hw'
  have hint : 0 < ∫ t in (0 : ℝ)..L, f t :=
    lt_of_lt_of_le (intervalIntegral.intervalIntegral_pos_of_pos_on
      (hfc.intervalIntegrable _ _) hpos (by linarith))
      (intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
        (Filter.Eventually.of_forall fun t ↦ mul_nonneg (sq_nonneg _) (hw t))
        (hfc.intervalIntegrable _ _))
  rw [costT_eq]
  linarith

/-- `∫₀ᴸ (ψ₁'ψ₂ - ψ₁ψ₂') = π/2 > 0`: the book's `s²` coefficient is `-3π/2 < 0`. -/
private lemma integral_psi_wronskian {L : ℝ} (hL : 0 < L) :
    ∫ t in (0 : ℝ)..L, (deriv (psi1 L) t * psi2 L t - psi1 L t * deriv (psi2 L) t) =
      Real.pi / 2 := by
  have e : ∀ t, deriv (psi1 L) t * psi2 L t - psi1 L t * deriv (psi2 L) t = -angD L t := by
    intro t
    rw [psi_wronskian]
    rcases le_or_gt t (L / 3) with h | h
    · simp [angD_eq_zero (Or.inl h)]
    rcases le_or_gt (2 * L / 3) t with h' | h'
    · simp [angD_eq_zero (Or.inr h')]
    rw [amp_eq_one hL h.le h'.le]; ring
  simp only [e, intervalIntegral.integral_neg, integral_angD hL, neg_neg]

/-- With the chosen `ψ` (`ρ = 1` where `θ' ≠ 0`), `cost(g_s) = 3L - (3π/2) sinh² s` for every
`s`: the cost drops for every `s ≠ 0`. -/
private lemma costT_eq' {L : ℝ} (hL : 0 < L) (s : ℝ) :
    costT L s = 3 * L - 3 * Real.pi / 2 * Real.sinh s ^ 2 := by
  have e : ∀ t, traceForm J (fW L (s, t)) = -2 * Real.sinh s ^ 2 * angD L t := by
    intro t
    rw [traceForm_J_fW]
    rcases le_or_gt t (L / 3) with h | h
    · simp [angD_eq_zero (Or.inl h)]
    rcases le_or_gt (2 * L / 3) t with h' | h'
    · simp [angD_eq_zero (Or.inr h')]
    simp only [fσ, amp_eq_one hL h.le h'.le, mul_one]
  rw [costT, integral_traceForm_J_fX]
  simp only [e]
  rw [intervalIntegral.integral_const_mul, integral_angD hL]
  ring

/-- **The book's second-order expansion** (TeX 7363–7373):
`cost(g_s) = cost(g₀) - 3 s² ∫ (ψ₁'ψ₂ - ψ₁ψ₂') + o(s²)`, here as the limit of
`(cost(g_s) - cost(g₀)) / s²`. -/
private lemma costT_expansion {L : ℝ} (hL : 0 < L) :
    Tendsto (fun s ↦ (costT L s - costT L 0) / s ^ 2) (𝓝[≠] 0)
      (𝓝 (-3 * ∫ t in (0 : ℝ)..L,
        (deriv (psi1 L) t * psi2 L t - psi1 L t * deriv (psi2 L) t))) := by
  have h := (Real.hasDerivAt_sinh 0).tendsto_slope_zero
  simp only [zero_add, Real.sinh_zero, sub_zero, Real.cosh_zero] at h
  rw [integral_psi_wronskian hL]
  have h' := (h.pow 2).const_mul (-(3 * Real.pi / 2))
  rw [show -(3 * Real.pi / 2) * (1 : ℝ) ^ 2 = -3 * (Real.pi / 2) by ring] at h'
  refine h'.congr' ?_
  · filter_upwards [self_mem_nhdsWithin] with s hs
    rw [costT_eq' hL, costT_eq' hL, Real.sinh_zero, smul_eq_mul]
    field_simp
    ring

/-- `⟨J, M⟩ = M₀₁ - M₁₀`. -/
private lemma traceForm_J_eq (M : Mat2) : traceForm J M = M 0 1 - M 1 0 := by
  simp only [traceForm, J, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

/-- The cost integrand of a curve continuous on `[a, b]` is integrable on subintervals. -/
private lemma intervalIntegrable_traceForm_J {X : ℝ → Mat2} {a b c d : ℝ}
    (hX : ContinuousOn X (Icc a b)) (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
    IntervalIntegrable (fun t ↦ traceForm J (X t)) volume c d := by
  have he := continuousOn_iff_entrywise.1 hX
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hcd]
  simp only [traceForm_J_eq]
  exact ((he 0 1).sub (he 1 0)).mono (Icc_subset_Icc hac hdb)


/-! ### The reparametrization to `det X = 1`, Theorem 3.4.2, and the deformed arc -/

/-- A matrix curve with a continuous entrywise derivative is Lipschitz on every `[a, b]`. -/
private lemma lipschitzOnEntrywise_of_hasDerivAt {F F' : ℝ → Mat2}
    (hd : ∀ t, HasDerivAtEntrywise F (F' t) t) (hc : Continuous F') (a b : ℝ) :
    LipschitzOnEntrywise F (Icc a b) := by
  intro i j
  have hc' : Continuous fun t ↦ F' t i j := continuous_iff_entrywise.1 hc i j
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc'.continuousOn
  refine ⟨C.toNNReal, (convex_Icc a b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun x _ ↦ (hd x i j).hasDerivWithinAt) fun x hx ↦ ?_⟩
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
  exact (hC x hx).trans (le_max_left _ _)

/-- The star functions are linear: `ρᵢ(cX) = c ρᵢ(X)`. -/
private lemma ρ_smul (c : ℝ) (X : Mat2) :
    ρ₀ (c • X) = c * ρ₀ X ∧ ρ₁ (c • X) = c * ρ₁ X ∧ ρ₂ (c • X) = c * ρ₂ X := by
  simp only [ρ₀, ρ₁, ρ₂, Matrix.smul_apply, smul_eq_mul]
  refine ⟨?_, ?_, ?_⟩ <;> ring

/-- `⟨J, cX⟩ = c ⟨J, X⟩`. -/
private lemma traceForm_J_smul (c : ℝ) (X : Mat2) : traceForm J (c • X) = c * traceForm J X := by
  rw [traceForm, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, traceForm]

/-- **Curvatures under reparametrization**: if `X̃ = cX` with `c² det X = 1` (so `det X̃ = 1`) and
`X̃' = c (c X' + c' X)` (the chain rule for `X̃(τ) = c(t) X(t)`, `dt/dτ = c`), then
`det(e, (X̃ + X̃⁻¹X̃') e) = c³ det(e, (det X · X + adj X · X') e)`: the state-dependent
curvatures of the reparametrized curve are the curvature numerators `k_j` times `c³ > 0`. -/
private lemma det2_reparam (X D : Mat2) (c c' : ℝ) (hc : c ^ 2 * X.det = 1) (e : Fin 2 → ℝ) :
    det2 e ((c • X + (c • X)⁻¹ * (c • (c • D + c' • X))) *ᵥ e) =
      c ^ 3 * det2 e ((X.det • X + X.adjugate * D) *ᵥ e) := by
  have hinv : (c • X)⁻¹ = c • X.adjugate := by
    rw [Matrix.inv_def, Matrix.det_smul, Fintype.card_fin, hc, Ring.inverse_one, one_smul,
      Matrix.adjugate_smul, Fintype.card_fin, pow_one]
  rw [hinv]
  rw [Matrix.det_fin_two] at hc
  simp only [det2, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.mul_apply,
    Matrix.add_apply, Matrix.smul_apply, Matrix.adjugate_fin_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.det_fin_two, smul_eq_mul]
  linear_combination (-(c * (e 0 * (X 1 0 * e 0 + X 1 1 * e 1) -
    e 1 * (X 0 0 * e 0 + X 0 1 * e 1)))) * hc

/-- **The deformed arc** (the proof of Theorem 8.2.7, TeX 7327–7391). For every `L > 0` there is
a state trajectory `(G, X₀)` on some `[0, ℓ]` from `(I, J)` to `(exp(JL), J)` whose cost is less
than `3L`, the cost of the circular arc `exp(Jt)`, `t ∈ [0, L]`, which has the same endpoints.

The book's construction (steps 2–9 of the module docstring): the deformation
`g_s(t) = exp(sS(t)) exp(Jt)` in the book's time `t ∈ [0, L]`, with the fixed `ψ` of `psi_spec`,
costs `< 3L` for every `s ≠ 0` (`costT_lt`). For small `s > 0`, the star inequalities,
`det X_s > 0` and the curvature numerators `k_j > 0` hold uniformly on the compact `[0, L]` (the
tube lemma; `X_s = J` off `(L/6, 5L/6)`). The reparametrization `τ(t) = ∫₀ᵗ √(det X_s)`,
inverted by Mathlib's order isomorphism with the derivative of the inverse function, gives
`X̃ = X_s/√(det X_s)` with `det X̃ = 1`, the star inequalities (linear in `X`), positive
curvatures (`det2_reparam`), and the same cost (change of variables). Theorem 3.4.2 with the
control `u_j = κ_j / Σ κ` (Definition 3.3.2) makes it a state trajectory. -/
private lemma exists_deformedArc {L : ℝ} (hL : 0 < L) :
    ∃ (ℓ : ℝ) (u₀ : ℝ → Fin 3 → ℝ) (G X₀ : ℝ → Mat2), IsStateTrajectory ℓ u₀ G X₀ ∧
      G 0 = 1 ∧ X₀ 0 = J ∧ G ℓ = rot L ∧ X₀ ℓ = J ∧ reinhardtCost ℓ X₀ < 3 * L := by
  -- Step 1: for small `s > 0`, `X_s` is close to `J` on `[0, L]`
  have hK : IsCompact (Icc (0 : ℝ) L) := isCompact_Icc
  have hXc := fX_continuous L
  have hXe : ∀ i j, Continuous fun p ↦ fX L p i j := continuous_iff_entrywise.1 hXc
  have h3 : (0 : ℝ) < √3 := by positivity
  have hJdet : J.det = 1 := by simp [J, Matrix.det_fin_two]
  have e₀ := eventually_pos (F := fun p ↦ ρ₀ (fX L p))
    (((hXe 1 0).add (continuous_const.mul (hXe 0 0))).div_const _) hK
    fun t _ ↦ by rw [fX_zero]; simp [ρ₀, J, h3]
  have e₁ := eventually_pos (F := fun p ↦ ρ₁ (fX L p))
    (((hXe 1 0).sub (continuous_const.mul (hXe 0 0))).div_const _) hK
    fun t _ ↦ by rw [fX_zero]; simp [ρ₁, J, h3]
  have e₂ := eventually_pos (F := fun p ↦ ρ₂ (fX L p))
    (((continuous_const.mul (hXe 0 1)).add (hXe 1 0)).neg.div_const _) hK
    fun t _ ↦ by rw [fX_zero]; simp [ρ₂, J]
  have ed := eventually_pos (F := fun p ↦ (fX L p).det) hXc.matrix_det hK
    fun t _ ↦ by rw [fX_zero, hJdet]; exact one_pos
  have eκ : ∀ j, ∀ᶠ s in 𝓝 (0 : ℝ), ∀ t ∈ Icc 0 L, 0 < fk L j (s, t) := fun j ↦
    eventually_pos (fk_continuous L j) hK fun t _ ↦ by rw [fk_zero]; exact one_pos
  have hev := e₀.and (e₁.and (e₂.and (ed.and ((eκ 0).and ((eκ 1).and (eκ 2))))))
  obtain ⟨s, ⟨hρ₀, hρ₁, hρ₂, hd, hκ₀, hκ₁, hκ₂⟩, hs⟩ :=
    ((hev.filter_mono (nhdsWithin_le_nhds (s := Ioi 0))).and self_mem_nhdsWithin).exists
  have hs : 0 < s := hs
  have hκ : ∀ t ∈ Icc 0 L, ∀ j, 0 < fk L j (s, t) := fun t ht j ↦ by
    fin_cases j
    · exact hκ₀ t ht
    · exact hκ₁ t ht
    · exact hκ₂ t ht
  -- Step 2: the deformed curve in the book's time `t`
  have hpc : Continuous fun x : ℝ ↦ (s, x) := continuous_const.prodMk continuous_id
  set X : ℝ → Mat2 := fun t ↦ fX L (s, t) with hX_def
  set D : ℝ → Mat2 := fun t ↦ fD L (s, t) with hD_def
  -- the book's `g_s(t) = exp(s S(t)) exp(Jt)`
  set Gt : ℝ → Mat2 := fun t ↦ NormedSpace.exp (s • fS L t) * NormedSpace.exp (t • J)
    with hGt_def
  have hGt : Gt = fun t ↦ fΨ L (s, t) * rot t := funext fun t ↦ by
    simp only [hGt_def, fΨ_eq_exp, rot_eq_exp]
  have hXd : ∀ t, HasDerivAtEntrywise X (D t) t := hasDerivAt_fX L s
  have hGtd : ∀ t, HasDerivAtEntrywise Gt (Gt t * X t) t := fun t ↦ by
    rw [hGt]; exact hasDerivAt_fg L s t
  have hXcont : Continuous X := hXc.comp hpc
  have hDcont : Continuous D := (fD_continuous L).comp hpc
  have hout : ∀ t, t < L / 6 ∨ 5 * L / 6 < t → X t = J ∧ fΨ L (s, t) = 1 := fun t ht ↦
    f_trivial_of_not_mem hL s ht
  have hdpos : ∀ t, 0 < (X t).det := by
    intro t
    by_cases ht : t ∈ Icc 0 L
    · exact hd t ht
    · have : t < L / 6 ∨ 5 * L / 6 < t := by
        rw [mem_Icc, not_and_or, not_le, not_le] at ht
        rcases ht with h | h
        · left; linarith
        · right; linarith
      rw [(hout t this).1, hJdet]; exact one_pos
  -- Step 3: the speed `v = √(det X_s)` and the unit-speed time `τ = ∫ v`
  have hXt : ∀ i j, ContDiff ℝ ∞ fun t ↦ X t i j := fun i j ↦
    (fX_contDiff L i j).comp (contDiff_const.prodMk contDiff_id)
  have hδ : ContDiff ℝ ∞ fun t ↦ (X t).det := by
    simp only [Matrix.det_fin_two]
    exact ((hXt 0 0).mul (hXt 1 1)).sub ((hXt 0 1).mul (hXt 1 0))
  set v : ℝ → ℝ := fun t ↦ √((X t).det) with hv_def
  have hv : ContDiff ℝ ∞ v := hδ.sqrt fun t ↦ (hdpos t).ne'
  have hvpos : ∀ t, 0 < v t := fun t ↦ Real.sqrt_pos.2 (hdpos t)
  have hvsq : ∀ t, v t ^ 2 = (X t).det := fun t ↦ Real.sq_sqrt (hdpos t).le
  have hv1 : ∀ t, t < L / 6 ∨ 5 * L / 6 < t → v t = 1 := fun t ht ↦ by
    simp only [hv_def, (hout t ht).1, hJdet, Real.sqrt_one]
  set c : ℝ → ℝ := fun t ↦ (v t)⁻¹ with hc_def
  have hcd : ContDiff ℝ ∞ c := hv.inv fun t ↦ (hvpos t).ne'
  have hcd' : ∀ t, HasDerivAt c (deriv c t) t := fun t ↦
    (hcd.differentiable (by simp) t).hasDerivAt
  have hc'cont : Continuous (deriv c) := hcd.continuous_deriv (by simp)
  have hcpos : ∀ t, 0 < c t := fun t ↦ inv_pos.2 (hvpos t)
  have hcv : ∀ t, c t * v t = 1 := fun t ↦ inv_mul_cancel₀ (hvpos t).ne'
  have hc2 : ∀ t, c t ^ 2 * (X t).det = 1 := fun t ↦ by
    rw [← hvsq, ← mul_pow, hcv, one_pow]
  set τ : ℝ → ℝ := fun t ↦ ∫ x in (0 : ℝ)..t, v x with hτ_def
  have hτd : ∀ t, HasDerivAt τ (v t) t := fun t ↦
    (hv.continuous.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hτmono : StrictMono τ := strictMono_of_hasDerivAt_pos hτd hvpos
  have hτc : Continuous τ := continuous_iff_continuousAt.2 fun t ↦ (hτd t).continuousAt
  have hτ0 : τ 0 = 0 := intervalIntegral.integral_same
  have hτneg : ∀ t ≤ 0, τ t = t := by
    intro t ht
    simp only [hτ_def]
    rw [intervalIntegral.integral_congr (g := fun _ ↦ (1 : ℝ)) fun x hx ↦
      hv1 x (Or.inl (lt_of_le_of_lt (hx.2.trans (sup_le le_rfl ht)) (by linarith)))]
    simp
  have hτbig : ∀ t, L ≤ t → τ t = τ L + (t - L) := by
    intro t ht
    simp only [hτ_def]
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := L)
      (hv.continuous.intervalIntegrable _ _) (hv.continuous.intervalIntegrable _ _),
      intervalIntegral.integral_congr (a := L) (b := t) (g := fun _ ↦ (1 : ℝ)) fun x hx ↦
        hv1 x (Or.inr (lt_of_lt_of_le (by linarith) ((le_inf le_rfl ht).trans hx.1)))]
    simp
  have hsurj : Function.Surjective τ := by
    refine hτc.surjective ?_ ?_
    · refine (tendsto_atTop_add_const_right atTop (τ L - L) tendsto_id).congr' ?_
      filter_upwards [eventually_ge_atTop L] with t ht
      rw [hτbig t ht]; simp only [id]; ring
    · refine tendsto_id.congr' ?_
      filter_upwards [eventually_le_atBot 0] with t ht
      rw [hτneg t ht]; rfl
  -- Step 4: the inverse `t(τ)` of `τ(t)`
  set e := StrictMono.orderIsoOfSurjective τ hτmono hsurj with he_def
  set ti : ℝ → ℝ := fun σ ↦ e.symm σ with hti_def
  have hτti : ∀ σ, τ (ti σ) = σ := fun σ ↦ e.apply_symm_apply σ
  have htiτ : ∀ t, ti (τ t) = t := fun t ↦ e.symm_apply_apply t
  have htic : Continuous ti := e.symm.continuous
  have htid : ∀ σ, HasDerivAt ti (c (ti σ)) σ := fun σ ↦
    (hτd (ti σ)).of_local_left_inverse htic.continuousAt (hvpos _).ne'
      (Filter.Eventually.of_forall hτti)
  have hti0 : ti 0 = 0 := by have := htiτ 0; rwa [hτ0] at this
  set ℓ := τ L with hℓ_def
  have htiℓ : ti ℓ = L := htiτ L
  have hℓ : 0 < ℓ := by rw [hℓ_def, ← hτ0]; exact hτmono hL
  have htiI : ∀ σ ∈ Icc 0 ℓ, ti σ ∈ Icc 0 L := fun σ hσ ↦
    ⟨hti0 ▸ e.symm.monotone hσ.1, htiℓ ▸ e.symm.monotone hσ.2⟩
  -- Step 5: the reparametrized trajectory `G(σ) = g_s(t(σ))`, `X₀ = G⁻¹G' = X_s/√(det X_s)`
  set G : ℝ → Mat2 := fun σ ↦ Gt (ti σ) with hG_def
  set X₀ : ℝ → Mat2 := fun σ ↦ c (ti σ) • X (ti σ) with hX₀_def
  set X₀' : ℝ → Mat2 := fun σ ↦
    c (ti σ) • (c (ti σ) • D (ti σ) + deriv c (ti σ) • X (ti σ)) with hX₀'_def
  have hGd : ∀ σ, HasDerivAtEntrywise G (G σ * X₀ σ) σ := fun σ ↦
    ((hGtd (ti σ)).scomp (htid σ)).congr_deriv (by simp only [hG_def, hX₀_def, Matrix.mul_smul])
  have hX₀d : ∀ σ, HasDerivAtEntrywise X₀ (X₀' σ) σ := fun σ ↦
    (HasDerivAtEntrywise.smul (hcd' (ti σ)) (hXd (ti σ))).scomp (htid σ)
  have hccont : Continuous fun σ ↦ c (ti σ) := hcd.continuous.comp htic
  have hX₀c : Continuous X₀ := hccont.smul (hXcont.comp htic)
  have hX₀'c : Continuous X₀' :=
    hccont.smul ((hccont.smul (hDcont.comp htic)).add
      ((hc'cont.comp htic).smul (hXcont.comp htic)))
  have hGc : Continuous G := continuous_iff_continuousAt.2 fun σ ↦ (hGd σ).continuousAt
  have hdetG : ∀ σ, (G σ).det = 1 := fun σ ↦ by
    simp only [hG_def, hGt]; exact det_fg L (s, ti σ)
  have hunit : ∀ σ, IsUnit (G σ).det := fun σ ↦ by rw [hdetG]; exact isUnit_one
  have hdetX₀ : ∀ σ, (X₀ σ).det = 1 := fun σ ↦ by
    simp only [hX₀_def]
    rw [Matrix.det_smul, Fintype.card_fin, hc2]
  have htrX₀ : ∀ σ, (X₀ σ).trace = 0 := fun σ ↦ by
    simp only [hX₀_def]
    rw [Matrix.trace_smul, trace_fX, smul_zero]
  have hstar : ∀ σ ∈ Icc 0 ℓ, 0 < ρ₀ (X₀ σ) ∧ 0 < ρ₁ (X₀ σ) ∧ 0 < ρ₂ (X₀ σ) := by
    intro σ hσ
    have ht := htiI σ hσ
    obtain ⟨r₀, r₁, r₂⟩ := ρ_smul (c (ti σ)) (X (ti σ))
    simp only [hX₀_def, r₀, r₁, r₂]
    exact ⟨mul_pos (hcpos _) (hρ₀ _ ht), mul_pos (hcpos _) (hρ₁ _ ht),
      mul_pos (hcpos _) (hρ₂ _ ht)⟩
  -- the curvatures of the reparametrized curve are `c³ k_j > 0`
  have hκeq : ∀ σ j, stateCurvature (X₀ σ) (derivEntrywise X₀ σ) j =
      c (ti σ) ^ 3 * fk L j (s, ti σ) := by
    intro σ j
    rw [stateCurvature, (hX₀d σ).derivEntrywise]
    exact det2_reparam (X (ti σ)) (D (ti σ)) (c (ti σ)) (deriv c (ti σ)) (hc2 _) _
  set u₀ : ℝ → Fin 3 → ℝ := fun σ ↦
    controlVariables fun j ↦ c (ti σ) ^ 3 * fk L j (s, ti σ) with hu₀_def
  -- Step 6: Theorem 3.4.2 gives the dynamics
  have hLip : LipschitzOnEntrywise (fun σ ↦ G σ * X₀ σ) (Icc 0 ℓ) :=
    lipschitzOnEntrywise_of_hasDerivAt (fun σ ↦ (hGd σ).mul (hX₀d σ))
      (((hGc.mul hX₀c).mul hX₀c).add (hGc.mul hX₀'c)) 0 ℓ
  have hdyn := theorem3_4_2 ℓ G (fun σ ↦ G σ * X₀ σ)
    (fun σ _ ↦ (hGd σ).hasDerivWithinAtEntrywise) (fun σ _ ↦ hdetG σ) hLip X₀
    (fun σ ↦ by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hunit σ), Matrix.one_mul])
    (fun σ _ ↦ hdetX₀ σ) hstar
    (Filter.Eventually.of_forall fun σ hσ j ↦ by
      rw [hκeq]
      exact (mul_pos (pow_pos (hcpos _) 3) (hκ _ (htiI σ (Ioo_subset_Icc_self hσ)) j)).le)
    u₀ (fun σ ↦ by simp only [hu₀_def]; congr 1; funext j; exact (hκeq σ j).symm)
  have hum : Measurable u₀ := by
    have hκm : ∀ j, Measurable fun σ ↦ c (ti σ) ^ 3 * fk L j (s, ti σ) := fun j ↦
      ((hccont.pow 3).mul ((fk_continuous L j).comp (continuous_const.prodMk htic))).measurable
    exact Measurable.of_eval fun j ↦ (hκm j).div (((hκm 0).add (hκm 1)).add (hκm 2))
  have hus : ∀ σ ∈ Icc 0 ℓ, u₀ σ ∈ controlSimplex := by
    intro σ hσ
    have h1 : ∀ j, 0 < c (ti σ) ^ 3 * fk L j (s, ti σ) := fun j ↦
      mul_pos (pow_pos (hcpos _) 3) (hκ _ (htiI σ hσ) j)
    have h2 : 0 < c (ti σ) ^ 3 * fk L 0 (s, ti σ) + c (ti σ) ^ 3 * fk L 1 (s, ti σ) +
        c (ti σ) ^ 3 * fk L 2 (s, ti σ) := by
      linarith [h1 0, h1 1, h1 2]
    refine ⟨fun i ↦ ⟨div_nonneg (h1 i).le h2.le, (div_le_one h2).2 ?_⟩, ?_⟩
    · fin_cases i <;> simp <;> linarith [h1 0, h1 1, h1 2]
    · simp only [hu₀_def, controlVariables]
      rw [← add_div, ← add_div, div_self h2.ne']
  have hGI : IsIntegralCurve G (fun σ ↦ G σ * X₀ σ) ℓ :=
    Matrix.eq_add_integral_of_hasDerivAtEntrywise_off_countable countable_empty
      hGc.continuousOn (fun σ _ ↦ hGd σ) fun i j ↦
        ((continuous_iff_entrywise.1 (hGc.mul hX₀c)) i j).intervalIntegrable _ _
  have hXI : IsIntegralCurve X₀
      (fun σ ↦ controlP (u₀ σ) (X₀ σ) * X₀ σ - X₀ σ * controlP (u₀ σ) (X₀ σ)) ℓ := by
    have h1 : IC X₀ X₀' 0 ℓ :=
      Matrix.eq_add_integral_of_hasDerivAtEntrywise_off_countable countable_empty
        hX₀c.continuousOn (fun σ _ ↦ hX₀d σ) fun i j ↦
          ((continuous_iff_entrywise.1 hX₀'c) i j).intervalIntegrable _ _
    refine h1.congr_ae hℓ.le (fun _ _ ↦ rfl) ?_
    filter_upwards [hdyn] with σ hσ hσ'
    rw [(hX₀d σ).unique (hσ hσ')]
    simp only [controlP, Matrix.smul_mul, Matrix.mul_smul, smul_sub]
  -- Step 7: the cost does not depend on the parametrization (change of variables `σ = τ(t)`)
  have hcost : reinhardtCost ℓ X₀ = costT L s := by
    have hg : Continuous fun σ ↦ traceForm J (X₀ σ) := by
      simp only [traceForm_J_eq]
      exact ((continuous_iff_entrywise.1 hX₀c) 0 1).sub ((continuous_iff_entrywise.1 hX₀c) 1 0)
    have hcov := intervalIntegral.integral_comp_mul_deriv (a := 0) (b := L) (f := τ) (f' := v)
      (g := fun σ ↦ traceForm J (X₀ σ)) (fun t _ ↦ hτd t) hv.continuous.continuousOn hg
    rw [hτ0] at hcov
    rw [reinhardtCost, costT, ← hcov]
    congr 1
    refine intervalIntegral.integral_congr fun t _ ↦ ?_
    simp only [Function.comp, hX₀_def, htiτ, traceForm_J_smul]
    rw [mul_comm, ← mul_assoc, mul_comm (v t), hcv, one_mul]
  -- Step 8: the boundary values
  have hb0 := hout 0 (Or.inl (by linarith))
  have hbL := hout L (Or.inr (by linarith))
  refine ⟨ℓ, u₀, G, X₀, ⟨hℓ, hum, hus, fun σ hσ ↦ ⟨hdetG σ, htrX₀ σ, hdetX₀ σ, hstar σ hσ⟩,
    hGI, hXI⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hG_def, hGt, hti0, hb0.2, rot_zero, Matrix.one_mul]
  · simp only [hX₀_def, hti0, hc_def, hv1 0 (Or.inl (by linarith)), inv_one, one_smul, hb0.1]
  · simp only [hG_def, hGt, htiℓ, hbL.2, Matrix.one_mul]
  · simp only [hX₀_def, htiℓ, hc_def, hv1 L (Or.inr (by linarith)), inv_one, one_smul, hbL.1]
  · rw [hcost]; exact costT_lt hL hs.ne'

/-- **A circular arc is not a local minimizer** (the second-variation argument in the proof of
Theorem 8.2.7, TeX 7327–7391; Mahler 1947). If an admissible trajectory of Problem 3.6.2 has
`X ≡ J` on an interval `[t₁, t₂] ⊆ [0, T]` with `t₁ < t₂` (a circular arc: `g = g₀ exp(Jt)`
there), then some admissible trajectory has strictly smaller cost.

Proof (the book's; the steps and lemmas are in the module docstring):
1. On `[t₁, t₂]`, `g(t) = g(t₁) exp(J(t - t₁))` (`g' = gJ`).
2. The deformation `g_s = Ψ_s exp(Jt)`, `Ψ_s = exp(sS)`, `S = [[ψ₁, ψ₂], [ψ₂, -ψ₁]]`, of the arc
   (time-shifted to `[0, t₂ - t₁]` and left-translated by `g(t₁)`), for a fixed pair `ψ` of
   smooth nonnegative functions with compact support in the interval, `ψ₁' > 0` and `ψ₂' < 0`
   where both are positive (`psi_spec`); `g_s` agrees with the arc near the ends.
3. Its cost, the parametrization-invariant `-(3/2) ∫ ⟨J, g⁻¹dg⟩`, is exactly
   `3(t₂ - t₁) - 3 ∫ (sinh(sr)/r)² (ψ₁'ψ₂ - ψ₁ψ₂') dt`, `r = |ψ|` (`costT_eq`), whose
   second-order truncation is the book's `cost(g₀) - 3s² ∫ (ψ₁'ψ₂ - ψ₁ψ₂') + O(s³)`; by the
   choice of `ψ` it is `< 3(t₂ - t₁)`, the cost of the arc, for every `s ≠ 0` (`costT_lt`).
4. For small `s > 0` the curvatures of `σ_j = g_s s_{2j}*` are positive, uniformly on the
   interval; reparametrized to `det X = 1` (the cost is unchanged), the deformation is the
   trajectory of the control `u_j = κ_j / Σ κ` (Theorem 3.4.2) (`exists_deformedArc`).
5. The spliced trajectory (the original outside `[t₁, t₂]`, the reparametrized deformation
   inside, the rest shifted in time) satisfies the boundary conditions of Problem 3.6.2 and
   costs less.

Steps 4 and 5 carry out what the book asserts in two sentences (TeX 7384–7390). -/
theorem exists_lt_reinhardtCost_of_circleArc {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsReinhardtAdmissible T u g X) {t₁ t₂ : ℝ} (h₁ : 0 ≤ t₁) (h₁₂ : t₁ < t₂) (h₂ : t₂ ≤ T)
    (hX : ∀ t ∈ Icc t₁ t₂, X t = J) :
    ∃ (T' : ℝ) (u' : ℝ → Fin 3 → ℝ) (g' X' : ℝ → Mat2),
      IsReinhardtAdmissible T' u' g' X' ∧ reinhardtCost T' X' < reinhardtCost T X := by
  classical
  obtain ⟨⟨hT, hum, hus, hds, hgI, hXI⟩, hg0, hgT, hXT⟩ := h
  -- Step 1: the arc is `g(t) = g(t₁) exp(J(t - t₁))`
  have harc := arc_eq hgI h₁ h₁₂.le h₂ hX
  -- Steps 2–5: the deformed arc, replacing the arc on `[t₁, t₂]`, of duration `ℓ` in the
  -- unit-speed time
  set Λ := t₂ - t₁ with hΛ_def
  have hΛ : 0 < Λ := by rw [hΛ_def]; linarith
  obtain ⟨ℓ, u₀, G, X₀, ⟨hℓ, hum₀, hus₀, hds₀, hGI, hXI₀⟩, hG0, hX0, hGℓ, hXℓ, hc₀⟩ :=
    exists_deformedArc hΛ
  set a := t₁ with ha
  set d := ℓ - Λ with hd
  have haΛ : a + Λ ≤ t₂ := by rw [hΛ_def]; linarith
  have hT' : a + ℓ ≤ T + d := by rw [hd, hΛ_def]; linarith
  -- the spliced trajectory: the original on `[0, a]`, the deformed arc on `[a, a + ℓ]`, and the
  -- original from `a + Λ` on, shifted by `d = ℓ - Λ`
  set u' : ℝ → Fin 3 → ℝ := fun τ ↦
    if τ ≤ a then u τ else if τ ≤ a + ℓ then u₀ (τ - a) else u (τ - d) with hu'
  set g' : ℝ → Mat2 := fun τ ↦
    if τ ≤ a then g τ else if τ ≤ a + ℓ then g a * G (τ - a) else g (τ - d) with hg'
  set X' : ℝ → Mat2 := fun τ ↦
    if τ ≤ a then X τ else if τ ≤ a + ℓ then X₀ (τ - a) else X (τ - d) with hX'
  have v1 : ∀ τ, τ ≤ a → u' τ = u τ ∧ g' τ = g τ ∧ X' τ = X τ := fun τ hτ ↦ by
    simp only [hu', hg', hX', hτ, ite_true, and_self]
  have v2 : ∀ τ, a < τ → τ ≤ a + ℓ →
      u' τ = u₀ (τ - a) ∧ g' τ = g a * G (τ - a) ∧ X' τ = X₀ (τ - a) := fun τ hτ hτ' ↦ by
    simp only [hu', hg', hX', not_le.2 hτ, hτ', ite_true, ite_false, and_self]
  have v3 : ∀ τ, a + ℓ < τ → u' τ = u (τ - d) ∧ g' τ = g (τ - d) ∧ X' τ = X (τ - d) :=
    fun τ hτ ↦ by
      simp only [hu', hg', hX', not_le.2 (by linarith : a < τ), not_le.2 hτ, ite_false,
        and_self]
  have hXa : X a = J := hX a ⟨le_rfl, h₁₂.le⟩
  have hXaΛ : X (a + Λ) = J := hX (a + Λ) ⟨by linarith, haΛ⟩
  have hgaΛ : g (a + Λ) = g a * rot Λ := by
    rw [harc (a + Λ) ⟨by linarith, haΛ⟩, add_sub_cancel_left]
  have w2 : ∀ τ ∈ Icc a (a + ℓ), g' τ = g a * G (τ - a) ∧ X' τ = X₀ (τ - a) := by
    intro τ hτ
    rcases eq_or_lt_of_le hτ.1 with e | e
    · subst e
      rw [(v1 a le_rfl).2.1, (v1 a le_rfl).2.2, sub_self, hG0, hX0, hXa, Matrix.mul_one]
      exact ⟨rfl, rfl⟩
    · exact ⟨(v2 τ e hτ.2).2.1, (v2 τ e hτ.2).2.2⟩
  have w3 : ∀ τ ∈ Icc (a + ℓ) (T + d), g' τ = g (τ - d) ∧ X' τ = X (τ - d) := by
    intro τ hτ
    rcases eq_or_lt_of_le hτ.1 with e | e
    · subst e
      have e' : a + ℓ - d = a + Λ := by rw [hd]; ring
      rw [(v2 (a + ℓ) (by linarith) le_rfl).2.1, (v2 (a + ℓ) (by linarith) le_rfl).2.2,
        e', add_sub_cancel_left, hGℓ, hXℓ, hgaΛ, hXaΛ]
      exact ⟨rfl, rfl⟩
    · exact ⟨(v3 τ e).2.1, (v3 τ e).2.2⟩
  -- the integral curves, glued from the three pieces
  have hXI' : IsIntegralCurve X'
      (fun t ↦ controlP (u' t) (X' t) * X' t - X' t * controlP (u' t) (X' t)) (T + d) := by
    have p1 : IC X' (fun t ↦ controlP (u' t) (X' t) * X' t - X' t * controlP (u' t) (X' t))
        0 a :=
      ((IC.of_isIntegralCurve hXI).mono le_rfl h₁ (by linarith)).congr h₁
        (fun τ hτ ↦ (v1 τ hτ.2).2.2) fun τ hτ ↦ by
          rw [(v1 τ hτ.2.le).1, (v1 τ hτ.2.le).2.2]
    have p2 : IC X' (fun t ↦ controlP (u' t) (X' t) * X' t - X' t * controlP (u' t) (X' t))
        a (a + ℓ) := by
      have := (IC.of_isIntegralCurve hXI₀).shift a
      rw [zero_add, add_comm ℓ a] at this
      exact this.congr (by linarith) (fun τ hτ ↦ (w2 τ hτ).2) fun τ hτ ↦ by
        rw [(v2 τ hτ.1 hτ.2.le).1, (v2 τ hτ.1 hτ.2.le).2.2]
    have p3 : IC X' (fun t ↦ controlP (u' t) (X' t) * X' t - X' t * controlP (u' t) (X' t))
        (a + ℓ) (T + d) := by
      have := ((IC.of_isIntegralCurve hXI).mono (c := a + Λ) (d := T) (by linarith) (by linarith)
        le_rfl).shift d
      rw [show a + Λ + d = a + ℓ by rw [hd]; ring] at this
      exact this.congr hT' (fun τ hτ ↦ (w3 τ hτ).2) fun τ hτ ↦ by
        rw [(v3 τ hτ.1).1, (v3 τ hτ.1).2.2]
    exact (p1.trans p2 h₁).trans p3 (by linarith)
  have hgI' : IsIntegralCurve g' (fun t ↦ g' t * X' t) (T + d) := by
    have p1 : IC g' (fun t ↦ g' t * X' t) 0 a :=
      ((IC.of_isIntegralCurve hgI).mono le_rfl h₁ (by linarith)).congr h₁
        (fun τ hτ ↦ (v1 τ hτ.2).2.1) fun τ hτ ↦ by
          rw [(v1 τ hτ.2.le).2.1, (v1 τ hτ.2.le).2.2]
    have p2 : IC g' (fun t ↦ g' t * X' t) a (a + ℓ) := by
      have := ((IC.of_isIntegralCurve hGI).const_mul (g a)).shift a
      rw [zero_add, add_comm ℓ a] at this
      exact this.congr (by linarith) (fun τ hτ ↦ (w2 τ hτ).1) fun τ hτ ↦ by
        rw [(v2 τ hτ.1 hτ.2.le).2.1, (v2 τ hτ.1 hτ.2.le).2.2, Matrix.mul_assoc]
    have p3 : IC g' (fun t ↦ g' t * X' t) (a + ℓ) (T + d) := by
      have := ((IC.of_isIntegralCurve hgI).mono (c := a + Λ) (d := T) (by linarith) (by linarith)
        le_rfl).shift d
      rw [show a + Λ + d = a + ℓ by rw [hd]; ring] at this
      exact this.congr hT' (fun τ hτ ↦ (w3 τ hτ).1) fun τ hτ ↦ by
        rw [(v3 τ hτ.1).2.1, (v3 τ hτ.1).2.2]
    exact (p1.trans p2 h₁).trans p3 (by linarith)
  -- the pointwise conditions
  have hds' : ∀ τ ∈ Icc 0 (T + d), (g' τ).det = 1 ∧ IsStarState (X' τ) := by
    intro τ hτ
    rcases le_or_gt τ a with e | e
    · rw [(v1 τ e).2.1, (v1 τ e).2.2]; exact hds τ ⟨hτ.1, by linarith⟩
    rcases le_or_gt τ (a + ℓ) with e' | e'
    · rw [(v2 τ e e').2.1, (v2 τ e e').2.2, Matrix.det_mul, (hds a ⟨h₁, by linarith⟩).1,
        one_mul]
      exact hds₀ (τ - a) ⟨by linarith, by linarith⟩
    · rw [(v3 τ e').2.1, (v3 τ e').2.2]; exact hds (τ - d) ⟨by linarith, by linarith [hτ.2]⟩
  have hus' : ∀ τ ∈ Icc 0 (T + d), u' τ ∈ controlSimplex := by
    intro τ hτ
    rcases le_or_gt τ a with e | e
    · rw [(v1 τ e).1]; exact hus τ ⟨hτ.1, by linarith⟩
    rcases le_or_gt τ (a + ℓ) with e' | e'
    · rw [(v2 τ e e').1]; exact hus₀ (τ - a) ⟨by linarith, by linarith⟩
    · rw [(v3 τ e').1]; exact hus (τ - d) ⟨by linarith, by linarith [hτ.2]⟩
  have hum' : Measurable u' :=
    Measurable.ite measurableSet_Iic hum (Measurable.ite measurableSet_Iic
      (hum₀.comp (measurable_sub_const a)) (hum.comp (measurable_sub_const d)))
  refine ⟨T + d, u', g', X', ⟨⟨by linarith, hum', hus', hds', hgI', hXI'⟩, ?_, ?_, ?_⟩, ?_⟩
  · rw [(v1 0 h₁).2.1, hg0]
  · rw [(w3 (T + d) ⟨hT', le_rfl⟩).1, add_sub_cancel_right, hgT]
  · rw [(w3 (T + d) ⟨hT', le_rfl⟩).2, add_sub_cancel_right, (v1 0 h₁).2.2, hXT]
  -- the cost
  have hXc : ContinuousOn X (Icc 0 T) := Matrix.continuousOn_of_eq_add_integral hXI
  have hX'c : ContinuousOn X' (Icc 0 (T + d)) := Matrix.continuousOn_of_eq_add_integral hXI'
  have i1 := intervalIntegrable_traceForm_J hX'c (c := 0) (d := a) le_rfl h₁ (by linarith)
  have i2 := intervalIntegrable_traceForm_J hX'c (c := a) (d := a + ℓ) h₁ (by linarith)
    (by linarith)
  have i3 := intervalIntegrable_traceForm_J hX'c (c := a + ℓ) (d := T + d) (by linarith) hT'
    le_rfl
  have j1 := intervalIntegrable_traceForm_J hXc (c := 0) (d := a) le_rfl h₁ (by linarith)
  have j2 := intervalIntegrable_traceForm_J hXc (c := a) (d := a + Λ) h₁ (by linarith)
    (by linarith)
  have j3 := intervalIntegrable_traceForm_J hXc (c := a + Λ) (d := T) (by linarith) (by linarith)
    le_rfl
  have e1 : ∫ t in (0 : ℝ)..a, traceForm J (X' t) = ∫ t in (0 : ℝ)..a, traceForm J (X t) :=
    intervalIntegral.integral_congr fun τ hτ ↦ by
      rw [uIcc_of_le h₁] at hτ; rw [(v1 τ hτ.2).2.2]
  have e2 : ∫ t in a..a + ℓ, traceForm J (X' t) = ∫ t in (0 : ℝ)..ℓ, traceForm J (X₀ t) := by
    rw [intervalIntegral.integral_congr (g := fun t ↦ traceForm J (X₀ (t - a))) fun τ hτ ↦ by
      rw [uIcc_of_le (by linarith)] at hτ; rw [(w2 τ hτ).2],
      intervalIntegral.integral_comp_sub_right (fun t ↦ traceForm J (X₀ t)), sub_self,
      add_sub_cancel_left]
  have e3 : ∫ t in a + ℓ..T + d, traceForm J (X' t) = ∫ t in a + Λ..T, traceForm J (X t) := by
    rw [intervalIntegral.integral_congr (g := fun t ↦ traceForm J (X (t - d))) fun τ hτ ↦ by
      rw [uIcc_of_le hT'] at hτ; rw [(w3 τ hτ).2],
      intervalIntegral.integral_comp_sub_right (fun t ↦ traceForm J (X t)), add_sub_cancel_right,
      show a + ℓ - d = a + Λ by rw [hd]; ring]
  have e4 : ∫ t in a..a + Λ, traceForm J (X t) = -2 * Λ := by
    rw [intervalIntegral.integral_congr (g := fun _ ↦ traceForm J J) fun τ hτ ↦ by
      rw [uIcc_of_le (by linarith)] at hτ
      rw [hX τ ⟨hτ.1, by linarith [hτ.2]⟩]]
    rw [intervalIntegral.integral_const, add_sub_cancel_left, smul_eq_mul, traceForm_J_eq]
    simp only [J, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    ring
  have hsplit' := intervalIntegral.integral_add_adjacent_intervals i1
    (i2.trans i3)
  have hsplit'' := intervalIntegral.integral_add_adjacent_intervals i2 i3
  have hsplit := intervalIntegral.integral_add_adjacent_intervals j1 (j2.trans j3)
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals j2 j3
  have hc₀' : -(3 / 2) * ∫ t in (0 : ℝ)..ℓ, traceForm J (X₀ t) < 3 * Λ := hc₀
  simp only [reinhardtCost]
  linarith


end SmoothedPolygons
