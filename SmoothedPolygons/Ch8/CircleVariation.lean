module

public import SmoothedPolygons.Ch8.Defs
public import SmoothedPolygons.Ch3.LieAlgebraDynamics
public import SmoothedPolygons.Ch3.ControlProblem
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# A circular arc is not a local minimizer (second variation, proof of Theorem 8.2.7)

The proof of Theorem 8.2.7 (`thm:no-singular-arcs`, TeX 7320–7391) shows by a second variation
that a trajectory of the Reinhardt problem containing a circular arc (`X ≡ J` on an interval) is
not a minimizer; the book cites Mahler's second-variation proof that the circle is not a local
minimizer (`mahler1947area`) as background and gives its own computation (MCA:1049350).

The deformation (TeX 7334–7342): with compactly supported smooth `ψ₁, ψ₂` on `(t₁, t₂)` and
`S(t) = [[ψ₁, ψ₂], [ψ₂, -ψ₁]]`, `g_s(t) = g(t₁) exp(-J t₁) Ψ_s(t) exp(Jt)`, `Ψ_s = exp(s S)`
(the book takes `g₀ = I`; the cost is left invariant). The cost is the parametrization-invariant
`-(3/2) ∫ ⟨J, g⁻¹ dg⟩` (Cartan–Maurer form, eqn `eqn:cost` / (4.3.1)), and
`⟨J, g_s⁻¹ g_s'⟩ = ⟨J, J⟩ + ⟨J, Ψ_s⁻¹ Ψ_s'⟩`, whence (checked with sympy)
`cost(g_s) = cost(g₀) - 3 s² ∫ (ψ₁' ψ₂ - ψ₁ ψ₂') dt + O(s³)` (TeX 7363–7373; the book's
`cost(g₀) = π` holds only on `[0, π/3]`, on `(t₁, t₂)` the cost is `3(t₂ - t₁)`, gap G8).
Choosing `ψ₁, ψ₂` with `∫ (ψ₁'ψ₂ - ψ₁ψ₂') > 0` makes the `s²` term negative. (The book's choice
"`ψ₁' > 0` and `ψ₂' < 0` on their common support" is impossible at the ends of a support of a
compactly supported function and is read on the interior of the overlap; e.g. `ψ₂(t) = ψ₁(t + δ)`
(so `ψ₂` lies to the left of `ψ₁`, as in the book's choice and Remark 8.2.8) for a bump `ψ₁` and
small `δ > 0` gives `∫ (ψ₁'ψ₂ - ψ₁ψ₂') = 2 ∫ ψ₁'(τ) ψ₁(τ + δ) dτ ≈ 2δ ∫ ψ₁'² > 0`; the choice
`ψ₂(t) = ψ₁(t - δ)` gives the opposite sign and raises the cost.)
For small `s` the curvatures of `σ_i = g_s s_i*` stay positive, uniformly close to the circle's
(TeX 7384–7390); the deformed curve, reparametrized to `det X = 1`, is the trajectory of an
admissible control (§3.3–§3.4).

## The proof

`l3st_exists_lt_cost_of_circleArc` follows these steps.

1. On the arc, `g(t) = g(t₁) exp(J(t - t₁))` (`arc_eq`, uniqueness for `g' = gJ`).
2. The deformed arc (`exists_deformedArc`), written directly in the unit-speed time `τ`:
   `g(τ) = exp(Jα(τ)) Ψ(τ)`, `Ψ = exp(s ρ(τ) E(-3τ)) = cosh(sρ) I + sinh(sρ) E(-3τ)`, where
   `E(φ) = [[cos φ, sin φ], [sin φ, -cos φ]]` and `ρ` is a smooth bump, positive exactly on
   `(ℓ/3, 2ℓ/3)`. Then `X = g⁻¹g' = P J + Q E(π/2 - 3τ) + s ρ' E(-3τ)` with `P, Q` explicit in
   `α'` and `sρ`, and `det X = 1` is a quadratic equation for `α'` whose positive root is
   `α' = √(9 sinh²(sρ) cosh²(sρ) + 1 + s²ρ'²) - 3 sinh²(sρ)` (`fA`, `det_fX`).
   In the book's time `t = α(τ)` this is the book's `g_s = Ψ_s(t) exp(Jt)` with
   `ψ₁ + iψ₂ = ρ(τ(t)) e^{i(2t - 3τ(t))}`: the pair `(ψ₁, ψ₂)` turns clockwise
   (`d/dt (2t - 3τ(t)) = 2 - 3/α' < 0`), like the book's `ψ₁' > 0`, `ψ₂' < 0`, and
   `∫ (ψ₁'ψ₂ - ψ₁ψ₂') dt = ∫ ρ² (3 - 2α') dτ > 0`.
3. The cost of the deformed arc is `-(3/2) ∫ ⟨J, X⟩ = 3 ∫ P` (`traceForm_J_fX`), that of the
   circular arc with the same endpoints is `3 ∫ α'`, and `α' - P = sinh²(sρ) (3 - 2α')`
   (`fA_sub_fP`): the exact form of the book's `-3s² ∫ (ψ₁'ψ₂ - ψ₁ψ₂') + O(s³)`.
4. For small `s > 0`, uniformly on the compact `[0, ℓ]` (the tube lemma, `eventually_pos`):
   `α' < 3/2` (so the cost decreases), the star inequalities `ρᵢ(X) > 0`, and the curvatures
   `κ_j = det(s_{2j}*, (X + X⁻¹X') s_{2j}*) > 0`; at `s = 0` the curve is the circle, `X = J`,
   `X' = 0`, `κ_j = 1`. The joint smoothness in `(s, τ)` gives the continuity of `X'`.
5. Theorem 3.4.2 (`theorem3_4_2`) with the control `u_j = κ_j / Σ κ` (Definition 3.3.2) gives
   `X' = [P_u, X]`, so the deformed arc is a state trajectory (`IsStateTrajectory`).
6. The spliced trajectory: the original on `[0, t₁]`, the deformed arc on `[t₁, t₁ + ℓ]`, and the
   original from `t₁ + Λ` on, shifted by `ℓ - Λ` (`Λ = α(ℓ)`), with `ℓ = (t₂ - t₁)/2`; its
   integral curves are glued from the three pieces (`IC.trans`, `IC.shift`, `IC.congr_ae`).
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

private lemma IC.of_isIntegralCurve {f v : ℝ → Mat2} {T : ℝ} (h : IsIntegralCurve f v T) :
    IC f v 0 T := h

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

/-! ### The bump function -/

/-- The bump `ρ`, smooth and positive exactly on `(ℓ/3, 2ℓ/3)`. -/
private noncomputable def bump (ℓ τ : ℝ) : ℝ :=
  expNegInvGlue (τ - ℓ / 3) * expNegInvGlue (2 * ℓ / 3 - τ)

/-- `ρ` is smooth. -/
private lemma bump_contDiff (ℓ : ℝ) : ContDiff ℝ ∞ (bump ℓ) :=
  (expNegInvGlue.contDiff.comp (contDiff_id.sub contDiff_const)).mul
    (expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id))

/-- `ρ` vanishes off `(ℓ/3, 2ℓ/3)`. -/
private lemma bump_eq_zero {ℓ τ : ℝ} (h : τ ≤ ℓ / 3 ∨ 2 * ℓ / 3 ≤ τ) : bump ℓ τ = 0 := by
  rcases h with h | h
  · simp [bump, expNegInvGlue.zero_of_nonpos (by linarith : τ - ℓ / 3 ≤ 0)]
  · simp [bump, expNegInvGlue.zero_of_nonpos (by linarith : 2 * ℓ / 3 - τ ≤ 0)]

/-- `ρ` is positive on `(ℓ/3, 2ℓ/3)`. -/
private lemma bump_pos {ℓ τ : ℝ} (h₁ : ℓ / 3 < τ) (h₂ : τ < 2 * ℓ / 3) : 0 < bump ℓ τ :=
  mul_pos (expNegInvGlue.pos_of_pos (by linarith)) (expNegInvGlue.pos_of_pos (by linarith))

/-- `ρ'` vanishes off `[ℓ/3, 2ℓ/3]`. -/
private lemma deriv_bump_eq_zero {ℓ τ : ℝ} (h : τ < ℓ / 3 ∨ 2 * ℓ / 3 < τ) :
    deriv (bump ℓ) τ = 0 := by
  have : bump ℓ =ᶠ[𝓝 τ] fun _ ↦ 0 := by
    rcases h with h | h
    · filter_upwards [Iio_mem_nhds h] with x hx using bump_eq_zero (Or.inl hx.le)
    · filter_upwards [Ioi_mem_nhds h] with x hx using bump_eq_zero (Or.inr hx.le)
  rw [this.deriv_eq, deriv_const]

/-! ### The deformation, as functions of `(s, τ)` -/

/-- `sinh(s ρ(τ))`. -/
private noncomputable def fσ (ℓ : ℝ) (p : ℝ × ℝ) : ℝ := Real.sinh (p.1 * bump ℓ p.2)

/-- `cosh(s ρ(τ))`. -/
private noncomputable def fc (ℓ : ℝ) (p : ℝ × ℝ) : ℝ := Real.cosh (p.1 * bump ℓ p.2)

/-- `s ρ'(τ)`. -/
private noncomputable def fR (ℓ : ℝ) (p : ℝ × ℝ) : ℝ := p.1 * deriv (bump ℓ) p.2

/-- The speed `α'` of the rotation, the root of `α'² + 6σ²α' = 1 + 9σ² + R²` that makes
`det X = 1`. -/
private noncomputable def fA (ℓ : ℝ) (p : ℝ × ℝ) : ℝ :=
  √(9 * fσ ℓ p ^ 2 * fc ℓ p ^ 2 + 1 + fR ℓ p ^ 2) - 3 * fσ ℓ p ^ 2

/-- The `J`-coordinate of `X`. -/
private noncomputable def fP (ℓ : ℝ) (p : ℝ × ℝ) : ℝ :=
  fA ℓ p * (fc ℓ p ^ 2 + fσ ℓ p ^ 2) - 3 * fσ ℓ p ^ 2

/-- The `F`-coordinate of `X`. -/
private noncomputable def fQ (ℓ : ℝ) (p : ℝ × ℝ) : ℝ :=
  2 * fσ ℓ p * fc ℓ p * fA ℓ p - 3 * fσ ℓ p * fc ℓ p

/-- `X = P J + Q F(-3τ) + R E(-3τ)`. -/
private noncomputable def fX (ℓ : ℝ) (p : ℝ × ℝ) : Mat2 :=
  !![fQ ℓ p * Real.sin (3 * p.2) + fR ℓ p * Real.cos (3 * p.2),
      -fP ℓ p + fQ ℓ p * Real.cos (3 * p.2) - fR ℓ p * Real.sin (3 * p.2);
    fP ℓ p + fQ ℓ p * Real.cos (3 * p.2) - fR ℓ p * Real.sin (3 * p.2),
      -(fQ ℓ p * Real.sin (3 * p.2)) - fR ℓ p * Real.cos (3 * p.2)]

/-- `Ψ = exp(s ρ E(-3τ)) = cosh(sρ) I + sinh(sρ) E(-3τ)`. -/
private noncomputable def fΨ (ℓ : ℝ) (p : ℝ × ℝ) : Mat2 :=
  !![fc ℓ p + fσ ℓ p * Real.cos (3 * p.2), -(fσ ℓ p * Real.sin (3 * p.2));
    -(fσ ℓ p * Real.sin (3 * p.2)), fc ℓ p - fσ ℓ p * Real.cos (3 * p.2)]

/-- The derivative of `Ψ` in `τ`. -/
private noncomputable def fΨ' (ℓ : ℝ) (p : ℝ × ℝ) : Mat2 :=
  !![fσ ℓ p * fR ℓ p + fc ℓ p * fR ℓ p * Real.cos (3 * p.2) - 3 * fσ ℓ p * Real.sin (3 * p.2),
      -(fc ℓ p * fR ℓ p * Real.sin (3 * p.2) + 3 * fσ ℓ p * Real.cos (3 * p.2));
    -(fc ℓ p * fR ℓ p * Real.sin (3 * p.2) + 3 * fσ ℓ p * Real.cos (3 * p.2)),
      fσ ℓ p * fR ℓ p - fc ℓ p * fR ℓ p * Real.cos (3 * p.2) + 3 * fσ ℓ p * Real.sin (3 * p.2)]

/-- The derivative of `X` in `τ`. -/
private noncomputable def fD (ℓ : ℝ) (p : ℝ × ℝ) : Mat2 :=
  Matrix.of fun i j ↦ fderiv ℝ (fun q ↦ fX ℓ q i j) p (0, 1)

/-- The state-dependent curvature `κ_j = det(s_{2j}*, (X + X⁻¹X') s_{2j}*)`, with
`X⁻¹ = adj X`. -/
private noncomputable def fκ (ℓ : ℝ) (j : Fin 3) (p : ℝ × ℝ) : ℝ :=
  det2 (sixthRoot (2 * (j.val : ZMod 6)))
    ((fX ℓ p + (fX ℓ p).adjugate * fD ℓ p) *ᵥ sixthRoot (2 * (j.val : ZMod 6)))

/-- `cosh² = sinh² + 1`. -/
private lemma fc_sq (ℓ : ℝ) (p : ℝ × ℝ) : fc ℓ p ^ 2 = fσ ℓ p ^ 2 + 1 := Real.cosh_sq _

/-- The quadratic equation for `α'`: `(α' + 3σ²)² = 9σ²c² + 1 + R²`. -/
private lemma fA_sq (ℓ : ℝ) (p : ℝ × ℝ) :
    (fA ℓ p + 3 * fσ ℓ p ^ 2) ^ 2 = 9 * fσ ℓ p ^ 2 * fc ℓ p ^ 2 + 1 + fR ℓ p ^ 2 := by
  rw [fA, sub_add_cancel, Real.sq_sqrt (by positivity)]

/-- `α' > 0`. -/
private lemma fA_pos (ℓ : ℝ) (p : ℝ × ℝ) : 0 < fA ℓ p := by
  rw [fA, sub_pos, Real.lt_sqrt (by positivity), fc_sq]
  nlinarith [sq_nonneg (fσ ℓ p), sq_nonneg (fR ℓ p)]

/-- `α' - P = sinh²(sρ) (3 - 2α')`: the cost saving per unit time. -/
private lemma fA_sub_fP (ℓ : ℝ) (p : ℝ × ℝ) :
    fA ℓ p - fP ℓ p = fσ ℓ p ^ 2 * (3 - 2 * fA ℓ p) := by
  rw [fP, fc_sq]; ring

/-- `X ∈ 𝔰𝔩₂(ℝ)`. -/
private lemma trace_fX (ℓ : ℝ) (p : ℝ × ℝ) : (fX ℓ p).trace = 0 := by
  rw [fX, Matrix.trace_fin_two_of]; ring

/-- `det X = 1`, by the choice of `α'`. -/
private lemma det_fX (ℓ : ℝ) (p : ℝ × ℝ) : (fX ℓ p).det = 1 := by
  rw [fX, Matrix.det_fin_two_of]
  have h1 := fc_sq ℓ p
  have h2 := Real.cos_sq_add_sin_sq (3 * p.2)
  have h3 := fA_sq ℓ p
  simp only [fP, fQ]
  linear_combination (fA ℓ p ^ 2 * (fc ℓ p ^ 2 - fσ ℓ p ^ 2 + 1) + 6 * fA ℓ p * fσ ℓ p ^ 2) * h1 +
    h3 - ((2 * fσ ℓ p * fc ℓ p * fA ℓ p - 3 * fσ ℓ p * fc ℓ p) ^ 2 + fR ℓ p ^ 2) * h2

/-- `det Ψ = 1`. -/
private lemma det_fΨ (ℓ : ℝ) (p : ℝ × ℝ) : (fΨ ℓ p).det = 1 := by
  rw [fΨ, Matrix.det_fin_two_of]
  linear_combination fc_sq ℓ p - fσ ℓ p ^ 2 * Real.cos_sq_add_sin_sq (3 * p.2)

/-- `⟨J, X⟩ = -2P`. -/
private lemma traceForm_J_fX (ℓ : ℝ) (p : ℝ × ℝ) : traceForm J (fX ℓ p) = -2 * fP ℓ p := by
  simp only [traceForm, J, fX, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

/-- `α' J Ψ + Ψ' = Ψ X`: the curve `exp(Jα) Ψ` has `g⁻¹g' = X`. -/
private lemma fΨ_deriv_eq (ℓ : ℝ) (p : ℝ × ℝ) :
    fA ℓ p • (J * fΨ ℓ p) + fΨ' ℓ p = fΨ ℓ p * fX ℓ p := by
  have h1 := fc_sq ℓ p
  have h2 := Real.cos_sq_add_sin_sq (3 * p.2)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [J, fΨ, fΨ', fX, fP, fQ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.zero_eta,
      Fin.mk_one, Fin.isValue]
  · linear_combination (-Real.sin (3 * p.2) * fσ ℓ p * (fA ℓ p - 3)) * h1 +
      (-fR ℓ p * fσ ℓ p) * h2
  · linear_combination (-fA ℓ p * Real.cos (3 * p.2) * fσ ℓ p + fA ℓ p * fc ℓ p +
      3 * Real.cos (3 * p.2) * fσ ℓ p) * h1 + (-fc ℓ p * fσ ℓ p ^ 2 * (2 * fA ℓ p - 3)) * h2
  · linear_combination (-fA ℓ p * Real.cos (3 * p.2) * fσ ℓ p - fA ℓ p * fc ℓ p +
      3 * Real.cos (3 * p.2) * fσ ℓ p) * h1 + (fc ℓ p * fσ ℓ p ^ 2 * (2 * fA ℓ p - 3)) * h2
  · linear_combination (Real.sin (3 * p.2) * fσ ℓ p * (fA ℓ p - 3)) * h1 +
      (-fR ℓ p * fσ ℓ p) * h2

/-- Where `sρ = 0` and `sρ' = 0` (in particular for `s = 0`, and off the support of `ρ`), the
deformation is trivial: `X = J`, `Ψ = I`, `α' = 1`. -/
private lemma f_trivial {ℓ : ℝ} {p : ℝ × ℝ} (h₁ : p.1 * bump ℓ p.2 = 0)
    (h₂ : p.1 * deriv (bump ℓ) p.2 = 0) : fX ℓ p = J ∧ fΨ ℓ p = 1 ∧ fA ℓ p = 1 := by
  have hσ : fσ ℓ p = 0 := by rw [fσ, h₁, Real.sinh_zero]
  have hc : fc ℓ p = 1 := by rw [fc, h₁, Real.cosh_zero]
  have hR : fR ℓ p = 0 := h₂
  have hA : fA ℓ p = 1 := by rw [fA, hσ, hc, hR]; norm_num
  have hP : fP ℓ p = 1 := by rw [fP, hA, hσ, hc]; norm_num
  have hQ : fQ ℓ p = 0 := by rw [fQ, hσ]; ring
  refine ⟨?_, ?_, hA⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [fX, J, hP, hQ, hR]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [fΨ, hσ, hc]

/-! ### Smoothness in `(s, τ)` -/

/-- `sinh(sρ)` is smooth in `(s, τ)`. -/
private lemma fσ_contDiff (ℓ : ℝ) : ContDiff ℝ ∞ (fσ ℓ) :=
  (contDiff_fst.mul ((bump_contDiff ℓ).comp contDiff_snd)).sinh

/-- `cosh(sρ)` is smooth in `(s, τ)`. -/
private lemma fc_contDiff (ℓ : ℝ) : ContDiff ℝ ∞ (fc ℓ) :=
  (contDiff_fst.mul ((bump_contDiff ℓ).comp contDiff_snd)).cosh

/-- `sρ'` is smooth in `(s, τ)`. -/
private lemma fR_contDiff (ℓ : ℝ) : ContDiff ℝ ∞ (fR ℓ) :=
  contDiff_fst.mul ((contDiff_infty_iff_deriv.1 (bump_contDiff ℓ)).2.comp contDiff_snd)

/-- `α'` is smooth in `(s, τ)`. -/
private lemma fA_contDiff (ℓ : ℝ) : ContDiff ℝ ∞ (fA ℓ) := by
  have hσ := fσ_contDiff ℓ
  have hc := fc_contDiff ℓ
  have hR := fR_contDiff ℓ
  have : ContDiff ℝ ∞ fun p ↦ √(9 * fσ ℓ p ^ 2 * fc ℓ p ^ 2 + 1 + fR ℓ p ^ 2) :=
    ContDiff.sqrt (by fun_prop) fun p ↦ by positivity
  exact this.sub (by fun_prop)

/-- The entries of `X` are smooth in `(s, τ)`. -/
private lemma fX_contDiff (ℓ : ℝ) (i j : Fin 2) : ContDiff ℝ ∞ fun p ↦ fX ℓ p i j := by
  have hσ := fσ_contDiff ℓ
  have hc := fc_contDiff ℓ
  have hR := fR_contDiff ℓ
  have hA := fA_contDiff ℓ
  have hP : ContDiff ℝ ∞ (fP ℓ) := by unfold fP; fun_prop
  have hQ : ContDiff ℝ ∞ (fQ ℓ) := by unfold fQ; fun_prop
  fin_cases i <;> fin_cases j <;>
    simp only [fX, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
    fun_prop

/-- `X` is continuous in `(s, τ)`. -/
private lemma fX_continuous (ℓ : ℝ) : Continuous (fX ℓ) :=
  continuous_iff_entrywise.2 fun i j ↦ (fX_contDiff ℓ i j).continuous

/-- `X'` is continuous in `(s, τ)`. -/
private lemma fD_continuous (ℓ : ℝ) : Continuous (fD ℓ) :=
  continuous_iff_entrywise.2 fun i j ↦
    ((fX_contDiff ℓ i j).continuous_fderiv (by simp)).clm_apply continuous_const

/-- The partial derivative in `τ` of a `C¹` function of `(s, τ)`. -/
private lemma hasDerivAt_partial {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (s τ : ℝ) :
    HasDerivAt (fun x ↦ F (s, x)) (fderiv ℝ F (s, τ) (0, 1)) τ :=
  ((hF.differentiable (by simp)) (s, τ)).hasFDerivAt.comp_hasDerivAt τ
    ((hasDerivAt_const τ s).prodMk (hasDerivAt_id τ))

/-- `fD` is the derivative of `X` in `τ`. -/
private lemma hasDerivAt_fX (ℓ s τ : ℝ) :
    HasDerivAtEntrywise (fun x ↦ fX ℓ (s, x)) (fD ℓ (s, τ)) τ := fun i j ↦
  hasDerivAt_partial (fX_contDiff ℓ i j) s τ

/-- At `s = 0`, `X' = 0`. -/
private lemma fD_zero (ℓ τ : ℝ) : fD ℓ (0, τ) = 0 := by
  have hJ : (fun x ↦ fX ℓ (0, x)) = fun _ ↦ J := funext fun x ↦
    (f_trivial (p := (0, x)) (zero_mul _) (zero_mul _)).1
  have h := hasDerivAt_fX ℓ 0 τ
  rw [hJ] at h
  exact h.unique (hasDerivAtEntrywise_const J τ)

/-- `fΨ'` is the derivative of `Ψ` in `τ`. -/
private lemma hasDerivAt_fΨ (ℓ s τ : ℝ) :
    HasDerivAtEntrywise (fun x ↦ fΨ ℓ (s, x)) (fΨ' ℓ (s, τ)) τ := by
  have hb : HasDerivAt (fun x ↦ s * bump ℓ x) (s * deriv (bump ℓ) τ) τ :=
    (((bump_contDiff ℓ).differentiable (by simp)) τ).hasDerivAt.const_mul s
  have h3 : HasDerivAt (fun x : ℝ ↦ 3 * x) 3 τ := by
    simpa using (hasDerivAt_id τ).const_mul (3 : ℝ)
  have hc := hb.cosh
  have hσ := hb.sinh
  have hC := h3.cos
  have hS := h3.sin
  rw [hasDerivAtEntrywise_fin_two_iff]
  simp only [fΨ, fΨ', fσ, fc, fR, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (hc.add (hσ.mul hC)).congr_deriv (by ring)
  · exact ((hσ.mul hS).neg).congr_deriv (by ring)
  · exact ((hσ.mul hS).neg).congr_deriv (by ring)
  · exact (hc.sub (hσ.mul hC)).congr_deriv (by ring)

/-- The curvatures are continuous in `(s, τ)`. -/
private lemma fκ_continuous (ℓ : ℝ) (j : Fin 3) : Continuous (fκ ℓ j) := by
  have hc : Continuous fun p ↦
      (fX ℓ p + (fX ℓ p).adjugate * fD ℓ p) *ᵥ sixthRoot (2 * (j.val : ZMod 6)) :=
    ((fX_continuous ℓ).add ((fX_continuous ℓ).matrix_adjugate.mul (fD_continuous ℓ))).matrix_mulVec
      continuous_const
  unfold fκ det2
  exact (continuous_const.mul ((continuous_apply 1).comp hc)).sub
    (continuous_const.mul ((continuous_apply 0).comp hc))

/-- At `s = 0` (the circle), `κ_j = 1`. -/
private lemma fκ_zero (ℓ : ℝ) (j : Fin 3) (τ : ℝ) : fκ ℓ j (0, τ) = 1 := by
  rw [fκ, fD_zero, (f_trivial (p := (0, τ)) (zero_mul _) (zero_mul _)).1, Matrix.mul_zero,
    add_zero]
  simp only [det2, sixthRoot, J, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  nlinarith [Real.cos_sq_add_sin_sq (Real.pi * ((2 * (j.val : ZMod 6)).val : ℝ) / 3)]

/-- The tube lemma: a continuous function of `(s, τ)`, positive at `s = 0` on a compact set of
`τ`, stays positive there for `s` near `0`. -/
private lemma eventually_pos {F : ℝ × ℝ → ℝ} (hF : Continuous F) {K : Set ℝ} (hK : IsCompact K)
    (h0 : ∀ τ ∈ K, 0 < F (0, τ)) : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ τ ∈ K, 0 < F (s, τ) :=
  hK.eventually_forall_of_forall_eventually fun τ hτ ↦
    hF.continuousAt.eventually (lt_mem_nhds (h0 τ hτ))


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

/-- **The deformed arc** (steps 2–5 of the proof of Theorem 8.2.7). For every `ℓ > 0` there is a
state trajectory `(g, X)` on `[0, ℓ]` from `(I, J)` to `(exp(JΛ), J)`, `0 < Λ ≤ 3ℓ/2`, whose cost
is less than `3Λ`, the cost of the circular arc `exp(Jt)`, `t ∈ [0, Λ]`, which has the same
endpoints.

The trajectory is `g = exp(Jα) Ψ_s` with `Ψ_s = exp(s ρ E(-3τ))`, `E(φ)` the reflection
`[[cos φ, sin φ], [sin φ, -cos φ]]` and `ρ` a bump: the book's deformation `Ψ_s exp(Jt)` written
as `exp(Jt) (exp(-Jt) Ψ_s exp(Jt))`, with the reparametrization `τ` (`det X = 1`) built in, the
time change `t = α(τ)` solving `det(g⁻¹g') = 1` (a quadratic equation for `α'`). For small `s`,
`X = g⁻¹g'` is uniformly close to `J` and `X'` to `0` (the tube lemma for the compact `[0, ℓ]`),
so the star inequalities and the positivity of the curvatures hold, and Theorem 3.4.2 gives the
dynamics. The cost is `3 ∫ P` against `3Λ = 3 ∫ α'`, and `α' - P = sinh²(sρ)(3 - 2α') > 0` on the
support of `ρ`. -/
private lemma exists_deformedArc {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∃ (Λ : ℝ) (u₀ : ℝ → Fin 3 → ℝ) (G X₀ : ℝ → Mat2), IsStateTrajectory ℓ u₀ G X₀ ∧
      G 0 = 1 ∧ X₀ 0 = J ∧ G ℓ = rot Λ ∧ X₀ ℓ = J ∧ 0 < Λ ∧ Λ ≤ 3 / 2 * ℓ ∧
      reinhardtCost ℓ X₀ < 3 * Λ := by
  -- Step 1: for small `s`, the deformed curve is close to the circle on `[0, ℓ]`
  have hK : IsCompact (Icc (0 : ℝ) ℓ) := isCompact_Icc
  have hXc := fX_continuous ℓ
  have hXe : ∀ i j, Continuous fun p ↦ fX ℓ p i j := continuous_iff_entrywise.1 hXc
  have h0 : ∀ τ : ℝ, fX ℓ (0, τ) = J := fun τ ↦
    (f_trivial (p := (0, τ)) (zero_mul _) (zero_mul _)).1
  have h3 : (0 : ℝ) < √3 := by positivity
  have e₀ := eventually_pos (F := fun p ↦ ρ₀ (fX ℓ p))
    (((hXe 1 0).add (continuous_const.mul (hXe 0 0))).div_const _) hK
    fun τ _ ↦ by rw [h0]; simp [ρ₀, J, h3]
  have e₁ := eventually_pos (F := fun p ↦ ρ₁ (fX ℓ p))
    (((hXe 1 0).sub (continuous_const.mul (hXe 0 0))).div_const _) hK
    fun τ _ ↦ by rw [h0]; simp [ρ₁, J, h3]
  have e₂ := eventually_pos (F := fun p ↦ ρ₂ (fX ℓ p))
    (((continuous_const.mul (hXe 0 1)).add (hXe 1 0)).neg.div_const _) hK
    fun τ _ ↦ by rw [h0]; simp [ρ₂, J]
  have eκ : ∀ j, ∀ᶠ s in 𝓝 (0 : ℝ), ∀ τ ∈ Icc 0 ℓ, 0 < fκ ℓ j (s, τ) := fun j ↦
    eventually_pos (fκ_continuous ℓ j) hK fun τ _ ↦ by rw [fκ_zero]; exact one_pos
  have eA := eventually_pos (F := fun p ↦ 3 / 2 - fA ℓ p)
    (continuous_const.sub (fA_contDiff ℓ).continuous) hK
    fun τ _ ↦ by rw [(f_trivial (p := (0, τ)) (zero_mul _) (zero_mul _)).2.2]; norm_num
  have hev := e₀.and (e₁.and (e₂.and ((eκ 0).and ((eκ 1).and ((eκ 2).and eA)))))
  obtain ⟨s, ⟨hρ₀, hρ₁, hρ₂, hκ₀, hκ₁, hκ₂, hA'⟩, hs⟩ :=
    ((hev.filter_mono (nhdsWithin_le_nhds (s := Ioi 0))).and self_mem_nhdsWithin).exists
  have hA : ∀ τ ∈ Icc 0 ℓ, fA ℓ (s, τ) < 3 / 2 := fun τ hτ ↦ by linarith [hA' τ hτ]
  have hκ : ∀ τ ∈ Icc 0 ℓ, ∀ j, 0 < fκ ℓ j (s, τ) := fun τ hτ j ↦ by
    fin_cases j
    · exact hκ₀ τ hτ
    · exact hκ₁ τ hτ
    · exact hκ₂ τ hτ
  have hs : 0 < s := hs
  -- Step 2: the curve `g = exp(Jα) Ψ_s` and `X = g⁻¹g'`
  have hpc : Continuous fun x : ℝ ↦ (s, x) := continuous_const.prodMk continuous_id
  have hAc : Continuous fun x ↦ fA ℓ (s, x) := (fA_contDiff ℓ).continuous.comp hpc
  set α : ℝ → ℝ := fun τ ↦ ∫ x in (0 : ℝ)..τ, fA ℓ (s, x) with hα_def
  have hαd : ∀ τ, HasDerivAt α (fA ℓ (s, τ)) τ := fun τ ↦
    (hAc.integral_hasStrictDerivAt 0 τ).hasDerivAt
  set G : ℝ → Mat2 := fun τ ↦ rot (α τ) * fΨ ℓ (s, τ) with hG_def
  set X₀ : ℝ → Mat2 := fun τ ↦ fX ℓ (s, τ) with hX₀_def
  set u₀ : ℝ → Fin 3 → ℝ := fun τ ↦ controlVariables fun j ↦ fκ ℓ j (s, τ) with hu₀_def
  have hGd : ∀ τ, HasDerivAtEntrywise G (G τ * X₀ τ) τ := by
    intro τ
    have h := (hasDerivAt_rot (hαd τ)).mul (hasDerivAt_fΨ ℓ s τ)
    refine h.congr_deriv ?_
    simp only [hG_def, hX₀_def]
    rw [Matrix.mul_assoc, ← fΨ_deriv_eq, Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_assoc]
  have hdetG : ∀ τ, (G τ).det = 1 := fun τ ↦ by
    simp only [hG_def]; rw [Matrix.det_mul, det_rot, det_fΨ, one_mul]
  have hunit : ∀ τ, IsUnit (G τ).det := fun τ ↦ by rw [hdetG]; exact isUnit_one
  have hXd : ∀ τ, HasDerivAtEntrywise X₀ (fD ℓ (s, τ)) τ := hasDerivAt_fX ℓ s
  have hX₀c : Continuous X₀ := hXc.comp hpc
  have hDc : Continuous fun τ ↦ fD ℓ (s, τ) := (fD_continuous ℓ).comp hpc
  have hGc : Continuous G := continuous_iff_continuousAt.2 fun τ ↦ (hGd τ).continuousAt
  have hκeq : ∀ τ j, stateCurvature (X₀ τ) (derivEntrywise X₀ τ) j = fκ ℓ j (s, τ) := by
    intro τ j
    rw [stateCurvature, (hXd τ).derivEntrywise, Matrix.inv_def]
    simp only [hX₀_def, det_fX, Ring.inverse_one, one_smul, fκ]
  -- Step 3: the boundary values
  have hb0 := f_trivial (ℓ := ℓ) (p := (s, 0))
    (by rw [bump_eq_zero (Or.inl (by linarith)), mul_zero])
    (by rw [deriv_bump_eq_zero (Or.inl (by linarith)), mul_zero])
  have hbℓ := f_trivial (ℓ := ℓ) (p := (s, ℓ))
    (by rw [bump_eq_zero (Or.inr (by linarith)), mul_zero])
    (by rw [deriv_bump_eq_zero (Or.inr (by linarith)), mul_zero])
  have hG0 : G 0 = 1 := by
    simp only [hG_def, hα_def, intervalIntegral.integral_same, rot_zero, hb0.2.1, Matrix.one_mul]
  -- Step 4: the cost
  have hPc : Continuous fun x ↦ fP ℓ (s, x) := by
    have := (fA_contDiff ℓ).continuous
    have := (fσ_contDiff ℓ).continuous
    have := (fc_contDiff ℓ).continuous
    unfold fP
    fun_prop
  have hcost : reinhardtCost ℓ X₀ = 3 * ∫ x in (0 : ℝ)..ℓ, fP ℓ (s, x) := by
    simp only [reinhardtCost, hX₀_def, traceForm_J_fX]
    rw [intervalIntegral.integral_const_mul]
    ring
  have hlt : ∫ x in (0 : ℝ)..ℓ, fP ℓ (s, x) < α ℓ := by
    have hσc : Continuous fun x ↦ fσ ℓ (s, x) := (fσ_contDiff ℓ).continuous.comp hpc
    have hhc : Continuous fun x ↦ fσ ℓ (s, x) ^ 2 * (3 - 2 * fA ℓ (s, x)) :=
      (hσc.pow 2).mul (continuous_const.sub (continuous_const.mul hAc))
    have hpos : 0 < ∫ x in (0 : ℝ)..ℓ, fσ ℓ (s, x) ^ 2 * (3 - 2 * fA ℓ (s, x)) := by
      refine lt_of_lt_of_le (intervalIntegral.intervalIntegral_pos_of_pos_on
        (hhc.intervalIntegrable _ _) (fun x hx ↦ ?_) (by linarith : ℓ / 3 < 2 * ℓ / 3))
        (intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith) ?_
          (hhc.intervalIntegrable _ _))
      · have hx' : x ∈ Icc 0 ℓ := ⟨by linarith [hx.1], by linarith [hx.2]⟩
        have h1 : 0 < fσ ℓ (s, x) :=
          Real.sinh_pos_iff.2 (mul_pos hs (bump_pos hx.1 hx.2))
        have h2 := hA x hx'
        have : 0 < 3 - 2 * fA ℓ (s, x) := by linarith
        positivity
      · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
        refine Filter.Eventually.of_forall fun x hx ↦ ?_
        have h2 := hA x (Ioc_subset_Icc_self hx)
        have : 0 ≤ 3 - 2 * fA ℓ (s, x) := by linarith
        simp only [Pi.zero_apply]
        positivity
    have e : ∫ x in (0 : ℝ)..ℓ, fσ ℓ (s, x) ^ 2 * (3 - 2 * fA ℓ (s, x)) =
        α ℓ - ∫ x in (0 : ℝ)..ℓ, fP ℓ (s, x) := by
      rw [hα_def, ← intervalIntegral.integral_sub (hAc.intervalIntegrable _ _)
        (hPc.intervalIntegrable _ _)]
      exact intervalIntegral.integral_congr fun x _ ↦ (fA_sub_fP ℓ (s, x)).symm
    linarith
  -- Step 5: admissibility through Theorem 3.4.2
  have hLip : LipschitzOnEntrywise (fun t ↦ G t * X₀ t) (Icc 0 ℓ) :=
    lipschitzOnEntrywise_of_hasDerivAt (fun t ↦ (hGd t).mul (hXd t))
      (((hGc.mul hX₀c).mul hX₀c).add (hGc.mul hDc)) 0 ℓ
  have hstar : ∀ t ∈ Icc 0 ℓ, 0 < ρ₀ (X₀ t) ∧ 0 < ρ₁ (X₀ t) ∧ 0 < ρ₂ (X₀ t) := fun t ht ↦
    ⟨hρ₀ t ht, hρ₁ t ht, hρ₂ t ht⟩
  have hdyn := theorem3_4_2 ℓ G (fun t ↦ G t * X₀ t)
    (fun t _ ↦ (hGd t).hasDerivWithinAtEntrywise) (fun t _ ↦ hdetG t) hLip X₀
    (fun t ↦ by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hunit t), Matrix.one_mul])
    (fun t _ ↦ det_fX ℓ (s, t)) hstar
    (Filter.Eventually.of_forall fun t ht j ↦ by
      rw [hκeq]; exact (hκ t (Ioo_subset_Icc_self ht) j).le)
    u₀ (fun t ↦ by simp only [hu₀_def]; congr 1; funext j; exact (hκeq t j).symm)
  have hum : Measurable u₀ := by
    have hκm : ∀ j, Measurable fun t ↦ fκ ℓ j (s, t) := fun j ↦
      ((fκ_continuous ℓ j).comp hpc).measurable
    exact Measurable.of_eval fun j ↦ (hκm j).div (((hκm 0).add (hκm 1)).add (hκm 2))
  have hus : ∀ t ∈ Icc 0 ℓ, u₀ t ∈ controlSimplex := by
    intro t ht
    have h1 := hκ t ht
    have h2 : 0 < fκ ℓ 0 (s, t) + fκ ℓ 1 (s, t) + fκ ℓ 2 (s, t) := by
      linarith [h1 0, h1 1, h1 2]
    refine ⟨fun i ↦ ⟨div_nonneg (h1 i).le h2.le, (div_le_one h2).2 ?_⟩, ?_⟩
    · fin_cases i <;> simp <;> linarith [h1 0, h1 1, h1 2]
    · simp only [hu₀_def, controlVariables]; field_simp
  have hGI : IsIntegralCurve G (fun t ↦ G t * X₀ t) ℓ :=
    Matrix.eq_add_integral_of_hasDerivAtEntrywise_off_countable countable_empty
      hGc.continuousOn (fun t _ ↦ hGd t) fun i j ↦
        ((continuous_iff_entrywise.1 (hGc.mul hX₀c)) i j).intervalIntegrable _ _
  have hXI : IsIntegralCurve X₀
      (fun t ↦ controlP (u₀ t) (X₀ t) * X₀ t - X₀ t * controlP (u₀ t) (X₀ t)) ℓ := by
    have h1 : IC X₀ (fun t ↦ fD ℓ (s, t)) 0 ℓ :=
      Matrix.eq_add_integral_of_hasDerivAtEntrywise_off_countable countable_empty
        hX₀c.continuousOn (fun t _ ↦ hXd t) fun i j ↦
          ((continuous_iff_entrywise.1 hDc) i j).intervalIntegrable _ _
    refine h1.congr_ae hℓ.le (fun _ _ ↦ rfl) ?_
    filter_upwards [hdyn] with t ht ht'
    rw [(hXd t).unique (ht ht')]
    simp only [controlP, Matrix.smul_mul, Matrix.mul_smul, smul_sub]
  refine ⟨α ℓ, u₀, G, X₀, ⟨hℓ, hum, hus, fun t ht ↦ ⟨hdetG t, trace_fX ℓ (s, t),
    det_fX ℓ (s, t), hstar t ht⟩, hGI, hXI⟩, hG0, hb0.1, ?_, hbℓ.1, ?_, ?_, ?_⟩
  · simp only [hG_def, hbℓ.2.1, Matrix.mul_one]
  · exact intervalIntegral.intervalIntegral_pos_of_pos_on (hAc.intervalIntegrable _ _)
      (fun x _ ↦ fA_pos ℓ (s, x)) hℓ
  · have := intervalIntegral.integral_mono_on (μ := volume) hℓ.le
      (hAc.intervalIntegrable _ _) intervalIntegrable_const
      fun x hx ↦ (show fA ℓ (s, x) ≤ 3 / 2 by linarith [hA x hx])
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at this
    simp only [hα_def]
    linarith
  · rw [hcost]; linarith


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

/-- **A circular arc is not a local minimizer** (the second-variation argument in the proof of
Theorem 8.2.7, TeX 7327–7391; Mahler 1947). If an admissible trajectory of Problem 3.6.2 has
`X ≡ J` on an interval `[t₁, t₂] ⊆ [0, T]` with `t₁ < t₂` (a circular arc: `g = g₀ exp(Jt)`
there), then some admissible trajectory has strictly smaller cost.

Proof (the book's):
1. On `[t₁, t₂]`, `g(t) = g(t₁) exp(J(t - t₁))` (`g' = gJ`).
2. The deformation `g_s = g(t₁) exp(-Jt₁) Ψ_s exp(Jt)` on `[t₁, t₂]` with `Ψ_s = exp(sS)`,
   `S = [[ψ₁, ψ₂], [ψ₂, -ψ₁]]`, `ψᵢ` smooth with compact support in `(t₁, t₂)`; `g_s = g` near the
   ends, `det g_s = 1` (`tr S = 0`).
3. The cost `-(3/2) ∫ ⟨J, g⁻¹g'⟩` does not depend on the parametrization of `g`, and
   `cost(g_s) = cost(g) - 3s² ∫ (ψ₁'ψ₂ - ψ₁ψ₂') + O(s³)`.
4. Choose `ψ₁, ψ₂` with `∫ (ψ₁'ψ₂ - ψ₁ψ₂') > 0`; for small `s > 0`, `cost(g_s) < cost(g)`.
5. For small `s`, `X_s = g_s⁻¹ g_s'` is uniformly close to `J`, so it satisfies the star
   inequalities and has positive state-dependent curvatures `κ_j`; reparametrize so that
   `det X = 1` (the cost is unchanged), and take the control `u_j = κ_j / Σ κ`
   (Definition 3.3.2), which lies in `U_T` and drives `X` (Theorem 3.4.2, `theorem3_4_2`). The
   spliced trajectory (the original outside the deformed arc, the reparametrized deformation
   inside, the rest shifted in time) satisfies the boundary conditions of Problem 3.6.2.

Departure from the paper (in carrying out steps 2–5, see the module docstring): the deformation
is written directly in the time `τ` with `det X = 1`, as `exp(Jα(τ)) exp(s ρ(τ) E(-3τ))` with
`α'` the positive root of the quadratic equation `det(g⁻¹g') = 1`. In the book's time `t = α(τ)`
it is the book's `Ψ_s(t) exp(Jt)` with `ψ₁ + iψ₂ = ρ(τ(t)) e^{i(2t - 3τ(t))}` (turning clockwise,
as the book's choice `ψ₁' > 0`, `ψ₂' < 0`); since `τ(t)` depends on `s`, so do `ψ₁, ψ₂`. This
avoids inverting `τ(t) = ∫ √(det X_s)`. The cost is computed exactly,
`cost = 3Λ - 3 ∫ sinh²(sρ) (3 - 2α') dτ` against the cost `3Λ` of the circular arc with the same
endpoints, instead of up to `O(s³)`; its `s²` term is the book's. The deformed arc has length
`ℓ = (t₂ - t₁)/2` and replaces the arc `[t₁, t₁ + Λ]`, `Λ ≤ 3ℓ/2 < t₂ - t₁`. -/
theorem l3st_exists_lt_cost_of_circleArc {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsReinhardtAdmissible T u g X) {t₁ t₂ : ℝ} (h₁ : 0 ≤ t₁) (h₁₂ : t₁ < t₂) (h₂ : t₂ ≤ T)
    (hX : ∀ t ∈ Icc t₁ t₂, X t = J) :
    ∃ (T' : ℝ) (u' : ℝ → Fin 3 → ℝ) (g' X' : ℝ → Mat2),
      IsReinhardtAdmissible T' u' g' X' ∧ reinhardtCost T' X' < reinhardtCost T X := by
  classical
  obtain ⟨⟨hT, hum, hus, hds, hgI, hXI⟩, hg0, hgT, hXT⟩ := h
  -- Step 1: the arc is `g(t) = g(t₁) exp(J(t - t₁))`
  have harc := arc_eq hgI h₁ h₁₂.le h₂ hX
  -- Steps 2–5: the deformed arc on `[0, ℓ]`, `ℓ = (t₂ - t₁)/2`
  set ℓ := (t₂ - t₁) / 2 with hℓ_def
  have hℓ : 0 < ℓ := by rw [hℓ_def]; linarith
  obtain ⟨Λ, u₀, G, X₀, ⟨-, hum₀, hus₀, hds₀, hGI, hXI₀⟩, hG0, hX0, hGℓ, hXℓ, hΛ, hΛℓ, hc₀⟩ :=
    exists_deformedArc hℓ
  set a := t₁ with ha
  set d := ℓ - Λ with hd
  have haΛ : a + Λ < t₂ := by rw [hℓ_def] at hΛℓ; linarith
  have hT' : a + ℓ < T + d := by rw [hd]; linarith
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
  have hXaΛ : X (a + Λ) = J := hX (a + Λ) ⟨by linarith, haΛ.le⟩
  have hgaΛ : g (a + Λ) = g a * rot Λ := by
    rw [harc (a + Λ) ⟨by linarith, haΛ.le⟩, add_sub_cancel_left]
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
      exact this.congr hT'.le (fun τ hτ ↦ (w3 τ hτ).2) fun τ hτ ↦ by
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
      exact this.congr hT'.le (fun τ hτ ↦ (w3 τ hτ).1) fun τ hτ ↦ by
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
  · rw [(v3 (T + d) hT').2.1, add_sub_cancel_right, hgT]
  · rw [(v3 (T + d) hT').2.2, add_sub_cancel_right, (v1 0 h₁).2.2, hXT]
  -- the cost
  have hXc : ContinuousOn X (Icc 0 T) := Matrix.continuousOn_of_eq_add_integral hXI
  have hX'c : ContinuousOn X' (Icc 0 (T + d)) := Matrix.continuousOn_of_eq_add_integral hXI'
  have i1 := intervalIntegrable_traceForm_J hX'c (c := 0) (d := a) le_rfl h₁ (by linarith)
  have i2 := intervalIntegrable_traceForm_J hX'c (c := a) (d := a + ℓ) h₁ (by linarith)
    (by linarith)
  have i3 := intervalIntegrable_traceForm_J hX'c (c := a + ℓ) (d := T + d) (by linarith) hT'.le
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
      rw [uIcc_of_le hT'.le] at hτ; rw [(w3 τ hτ).2],
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
