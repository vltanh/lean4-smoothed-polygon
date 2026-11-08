module

public import SmoothedPolygons.Ch8.Defs
public import Basic.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Basic.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# The edge control problem and the Reinhardt problem (§8.1, running text)

The running text of §8.1 (TeX 6678–6775) connects the edge control problem (Definition 8.1.1) to
a Reinhardt trajectory `(g, X)` whose control lies in an edge of `U_T` on a time interval
`[c, d]`, written `u = (0, ½ + u_e, ½ - u_e)` after the rotation `edgeFrame j`:

* `eqn_xy_edge`: the half-plane coordinates `z = x + iy` of `X` (`Φ(z) = X`, Lemma 4.2.1) and
  `s = ∫ dt/y` solve the state equations (8.1.3) `x' = y`, `y' = f₂(x, y, u_e)`, `s' = 1/y`
  (`eqn:xy-edge`): the specialization of Lemma 4.5.2 to the edge; `x' = y > 0`;
* `eqn_g_edge`: `g(t) = g₀ h(t₀)⁻¹ h(t)` with `h = [[1, -x], [s, 1 - sx]]` (8.1.1)–(8.1.2)
  (`eqn:g-edge`);
* `edgeCost_identity`: the cost of the Reinhardt trajectory on `[c, d]` is
  `(3/2)((s + x)|_c^d + ∫ x²/y)`, so that up to the positive factor `3/2` and a constant fixed by
  the boundary conditions it is the edge cost (8.1.5) (`eqn:edge:cost`), by (4.3.1);
* `eqn_edge_ham`: the Hamiltonian of the edge problem is (8.1.6) (`eqn:edge:ham`);
* `eqn_costate_edge`: the costate equations (8.1.7) (`eqn:costate-edge`), derived in the proof of
  Theorem 8.1.4 from (8.1.6) as `λ' = -∂H/∂(x, y, s)`; `λ₃` is constant.

Remark 8.1.6 is in `SmoothedPolygons/Ch8/EdgeAbnormal.lean`. Facts used by the other files of
the chapter are public: the edge controls lie in `U_T` and the edge parameter in `[-½, ½]`
(`edgeControl_mem_controlSimplex`, `edgeParam_mem_edgeControlSet`), the denominator of `f₂` is
negative (`edgeF₂_denom_neg`), a covector on `ℝ³` is determined by its components
(`apply_eq_sum_edgeCostate`), the partial derivatives of the edge field and the edge cost
(`fderiv_edgeField_apply`, `fderiv_edgeCost_apply`), and the calculus of integral curves
(`IsIntegralCurve.ae_hasDerivAtEntrywise`, `IsIntegralCurve.absolutelyContinuousOnInterval`).
-/

@[expose] public section

namespace SmoothedPolygons

open Set MeasureTheory Filter Topology Matrix
open scoped Interval

/-- The matrix `h(t) = [[1, -x], [s, 1 - s x]]` of equation (8.1.1), as a function of the edge
state `q = (x, y, s)`. -/
noncomputable def edgeH (q : Fin 3 → ℝ) : Mat2 := !![1, -q 0; q 2, 1 - q 2 * q 0]

/-! ### The rotation to the edge `{u₀ = 0}` -/

/-- `R Z_u R⁻¹ = Z_{u'}` with `u'_m = u_{m+1}` (on the vertices this is
`R_conj_controlMatrix_vertex`; here by direct computation). -/
private lemma l3b_R_conj_controlMatrix (u : Fin 3 → ℝ) :
    R * controlMatrix u * R⁻¹ = controlMatrix (fun m ↦ u (m + 1)) := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3' : √3 ≠ 0 := by positivity
  rw [poly_R_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [R, controlMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring_nf <;> simp only [h3] <;> ring_nf

/-- `Rʲ Z_u R⁻ʲ = Z_{u'}` with `u'_m = u_{m+j}`: the rotation `edgeFrame j` takes the control
matrix of `u` to that of the cyclically permuted control. -/
private theorem l3b_edgeFrame_controlMatrix (j : Fin 3) (u : Fin 3 → ℝ) :
    edgeFrame j (controlMatrix u) = controlMatrix (fun m ↦ u (m + j)) := by
  fin_cases j
  · simp [edgeFrame]
  · simpa [edgeFrame] using l3b_R_conj_controlMatrix u
  · simp only [edgeFrame, Fin.reduceFinMk, Fin.isValue]
    rw [pow_two, pow_two, show R * R * controlMatrix u * (R⁻¹ * R⁻¹) =
      R * (R * controlMatrix u * R⁻¹) * R⁻¹ by simp only [Matrix.mul_assoc],
      l3b_R_conj_controlMatrix, l3b_R_conj_controlMatrix]
    congr 1
    funext m
    rw [add_assoc]
    rfl

/-- On the edge `{u_j = 0}` of `U_T`, the rotated control `u'_m = u_{m+j}` is
`(0, ½ + u_e, ½ - u_e)` with `u_e = edgeParam j u`. -/
private lemma l3b_rot_eq_edgeControl {u : Fin 3 → ℝ} (hu : u ∈ controlSimplex) {j : Fin 3}
    (hj : u j = 0) : (fun m ↦ u (m + j)) = edgeControl (edgeParam j u) := by
  have hs := hu.2
  funext m
  fin_cases j <;> fin_cases m <;>
    simp only [edgeControl, edgeParam, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Fin.reduceAdd, add_zero, zero_add, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hj ⊢ <;>
    linarith

/-- The edge control `(0, ½ + u_e, ½ - u_e)`, `u_e ∈ [-½, ½]`, lies in `U_T`. -/
theorem edgeControl_mem_controlSimplex {ue : ℝ} (hue : ue ∈ edgeControlSet) :
    edgeControl ue ∈ controlSimplex := by
  obtain ⟨h1, h2⟩ := hue
  refine ⟨fun i ↦ ?_, ?_⟩
  · fin_cases i <;> simp [edgeControl] <;> constructor <;> linarith
  · simp [edgeControl]; ring

/-- The edge parameter of a control in `U_T` lies in `[-½, ½]`. -/
theorem edgeParam_mem_edgeControlSet {j : Fin 3} {u : Fin 3 → ℝ} (hu : u ∈ controlSimplex) :
    edgeParam j u ∈ edgeControlSet := by
  have h1 := hu.1 (j + 1)
  have h2 := hu.1 (j + 2)
  simp only [edgeParam, edgeControlSet, mem_Icc]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- Conjugation `X ↦ R X R⁻¹` preserves the star states (`ρ_R_conj`). -/
private lemma l3b_isStarState_R_conj {S : Mat2} (hS : IsStarState S) :
    IsStarState (R * S * R⁻¹) := by
  obtain ⟨htr, hdet, h0, h1, h2⟩ := hS
  have hρ := ρ_R_conj S htr
  exact ⟨by rw [poly_trace_conj poly_inv_mul_R, htr], by rw [poly_det_conj poly_inv_mul_R, hdet],
    hρ.1 ▸ h2, hρ.2.1 ▸ h0, hρ.2.2 ▸ h1⟩

private lemma l3b_isStarState_Rpow_conj (i : ℕ) {S : Mat2} (hS : IsStarState S) :
    IsStarState (R ^ i * S * R⁻¹ ^ i) := by
  induction i with
  | zero => simpa using hS
  | succ i ih =>
    rw [pow_succ', pow_succ, show R * R ^ i * S * (R⁻¹ ^ i * R⁻¹) =
      R * (R ^ i * S * R⁻¹ ^ i) * R⁻¹ by simp only [Matrix.mul_assoc] ]
    exact l3b_isStarState_R_conj ih

/-- The rotation `X ↦ Rʲ X R⁻ʲ` (`edgeFrame j`) preserves the star states. -/
private theorem l3b_isStarState_edgeFrame (j : Fin 3) {S : Mat2} (hS : IsStarState S) :
    IsStarState (edgeFrame j S) :=
  l3b_isStarState_Rpow_conj j hS

/-- The rotation preserves `⟨J, X⟩` (`J` commutes with `R`). -/
private lemma l3b_traceForm_J_edgeFrame (j : Fin 3) (S : Mat2) :
    traceForm J (edgeFrame j S) = traceForm J S := by
  have hJ : R ^ (j : ℕ) * J * R⁻¹ ^ (j : ℕ) = J := by
    have hc : Commute J (R ^ (j : ℕ)) := (Commute.pow_right poly_J_mul_R _)
    rw [← hc.eq, Matrix.mul_assoc, poly_Rpow_mul_Rinvpow, Matrix.mul_one]
  rw [edgeFrame, ← hJ, poly_traceForm_conj (poly_Rinvpow_mul_Rpow _), hJ]

/-- A star state has `X₁₀ > 0` (`ρ₀ + ρ₁ = 2X₁₀/√3`). -/
private lemma l3b_pos_of_isStarState {S : Mat2} (hS : IsStarState S) : 0 < S 1 0 := by
  obtain ⟨-, -, h0, h1, -⟩ := hS
  simp only [ρ₀, ρ₁] at h0 h1
  have h3 : 0 < √3 := by positivity
  have := add_pos h0 h1
  rw [← add_div, div_pos_iff_of_pos_right h3] at this
  linarith

/-- A traceless matrix `S` of determinant one with `S₁₀ ≠ 0` is `Φ(x + iy)` with
`x = S₀₀/S₁₀`, `y = 1/S₁₀` (Lemma 4.2.1). -/
private lemma l3b_Φ_eq {S : Mat2} (htr : S.trace = 0) (hdet : S.det = 1) (h10 : S 1 0 ≠ 0) :
    Φ (S 0 0 / S 1 0) (1 / S 1 0) = S := by
  rw [Matrix.trace_fin_two] at htr
  rw [Matrix.det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Φ] <;> field_simp
  · linear_combination hdet - S 0 0 * htr
  · linarith

/-- On the edge, `f₁ = y` and `f₂ = 2√3 y² u_e/(-1 + 2√3 x u_e)` (the specialization of
Problem 4.5.1 to `u = (0, ½ + u_e, ½ - u_e)`, TeX 6697–6700). -/
private lemma l3b_halfPlaneF_edgeControl {x y ue : ℝ} (hD : -1 + 2 * √3 * x * ue ≠ 0) :
    halfPlaneF₁ x y (edgeControl ue) = y ∧ halfPlaneF₂ x y (edgeControl ue) = edgeF₂ x y ue := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3' : √3 ≠ 0 := by positivity
  have ha : controlMatrix (edgeControl ue) 0 0 = 2 * ue / √3 := by
    simp [controlMatrix, edgeControl]; ring
  have hb : controlMatrix (edgeControl ue) 0 1 = -2 / 3 := by
    simp [controlMatrix, edgeControl]; ring
  have hc : controlMatrix (edgeControl ue) 1 0 = 0 := by simp [controlMatrix, edgeControl]
  have hE : 2 * (2 * ue / √3) * x + -2 / 3 ≠ 0 := by
    intro h; apply hD
    field_simp at h
    linear_combination (√3 / 6) * h + (1 / 3) * h3
  simp only [halfPlaneF₁, halfPlaneF₂, ha, hb, hc, zero_mul, sub_zero, add_zero]
  refine ⟨by rw [mul_div_assoc, div_self hE, mul_one], ?_⟩
  rw [edgeF₂, div_eq_div_iff hE hD]
  field_simp
  ring_nf
  simp only [h3]

/-- On the state space and the control set of the edge problem, the denominator of `f₂` is negative:
`-1 + 2√3 x u_e < 0`. -/
theorem edgeF₂_denom_neg {x : ℝ} (hx1 : -(1 / √3) < x) (hx2 : x < 1 / √3) {ue : ℝ}
    (hue : ue ∈ edgeControlSet) : -1 + 2 * √3 * x * ue < 0 := by
  obtain ⟨hu1, hu2⟩ := hue
  have h3 : 0 < √3 := by positivity
  have h3' : √3 * (1 / √3) = 1 := by field_simp
  have hx1' : -1 < √3 * x := by nlinarith
  have hx2' : √3 * x < 1 := by nlinarith
  have ha : |√3 * x| < 1 := abs_lt.2 ⟨hx1', hx2'⟩
  have hue : |ue| ≤ 1 / 2 := abs_le.2 ⟨hu1, hu2⟩
  have : 2 * √3 * x * ue ≤ |√3 * x| := calc
    2 * √3 * x * ue ≤ |2 * (√3 * x) * ue| := by
      rw [show 2 * √3 * x * ue = 2 * (√3 * x) * ue by ring]; exact le_abs_self _
    _ = 2 * |√3 * x| * |ue| := by rw [abs_mul, abs_mul, abs_two]
    _ ≤ |√3 * x| := by nlinarith [abs_nonneg (√3 * x)]
  linarith

/-! ### Carathéodory calculus -/

/-- A curve in integral form has its entrywise derivative at almost every time (Lebesgue's
differentiation theorem). -/
theorem IsIntegralCurve.ae_hasDerivAtEntrywise {f v : ℝ → Mat2} {T : ℝ}
    (hI : IsIntegralCurve f v T) : ∀ᵐ τ, τ ∈ Ioo 0 T → HasDerivAtEntrywise f (v τ) τ := by
  rcases lt_or_ge T 0 with hT | hT
  · exact .of_forall fun τ hτ ↦ absurd (hτ.1.trans hτ.2) (not_lt.2 hT.le)
  have h : ∀ i k, ∀ᵐ τ, τ ∈ Ioo 0 T → HasDerivAt (fun s ↦ f s i k) (v τ i k) τ := fun i k ↦
    ae_hasDerivAt_of_eq_add_integral (hI i k).1 ⟨le_rfl, hT⟩ (hI i k).2
  have := ae_all_iff.2 fun i ↦ ae_all_iff.2 fun k ↦ h i k
  filter_upwards [this] with τ hτ hτI i k using hτ i k hτI

/-- The entries of a curve in integral form are absolutely continuous. -/
theorem IsIntegralCurve.absolutelyContinuousOnInterval {f v : ℝ → Mat2} {T : ℝ} (hT : 0 ≤ T)
    (hI : IsIntegralCurve f v T) (i k : Fin 2) :
    AbsolutelyContinuousOnInterval (fun t ↦ f t i k) 0 T :=
  absolutelyContinuousOnInterval_of_eq_add_integral hT (hI i k).1 (hI i k).2

/-- The entries of `A f(t) B` are absolutely continuous when those of `f` are. -/
private lemma l3b_ac_conj {f : ℝ → Mat2} {a b : ℝ} (A B : Mat2)
    (hf : ∀ i k, AbsolutelyContinuousOnInterval (fun t ↦ f t i k) a b) (i k : Fin 2) :
    AbsolutelyContinuousOnInterval (fun t ↦ (A * f t * B) i k) a b := by
  have e : (fun t ↦ (A * f t * B) i k) = fun t ↦ B 0 k * (A i 0 * f t 0 0 + A i 1 * f t 1 0) +
      B 1 k * (A i 0 * f t 0 1 + A i 1 * f t 1 1) := by
    funext t; simp only [Matrix.mul_apply, Fin.sum_univ_two]; ring
  rw [e]
  exact ((((hf 0 0).const_mul _).fun_add ((hf 1 0).const_mul _)).const_mul _).fun_add
    ((((hf 0 1).const_mul _).fun_add ((hf 1 1).const_mul _)).const_mul _)

/-- `r ↦ 1/r` is Lipschitz on `[m, ∞)`, `m > 0`. -/
private lemma l3b_lipschitzOnWith_one_div {m : ℝ} (hm : 0 < m) :
    LipschitzOnWith (Real.toNNReal (1 / m ^ 2)) (fun r : ℝ ↦ 1 / r) (Ici m) := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
  have hx0 : 0 < x := hm.trans_le hx
  have hy0 : 0 < y := hm.trans_le hy
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity),
    div_sub_div _ _ hx0.ne' hy0.ne', abs_div, abs_of_pos (mul_pos hx0 hy0),
    div_le_iff₀ (mul_pos hx0 hy0), show 1 * y - x * 1 = -(x - y) by ring, abs_neg]
  have hxy : m ^ 2 ≤ x * y := by rw [sq]; exact mul_le_mul hx hy hm.le hx0.le
  have h1 : 1 ≤ 1 / m ^ 2 * (x * y) := by
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ (by positivity), one_mul]; exact hxy
  nlinarith [abs_nonneg (x - y)]

/-- The derivative within `[a, b]` of a function in integral form with a continuous integrand. -/
private lemma l3b_hasDerivWithinAt_of_eq_add_integral {f w : ℝ → ℝ} {a b t : ℝ}
    (hw : ContinuousOn w (Icc a b)) (hf : ∀ s ∈ Icc a b, f s = f a + ∫ r in a..s, w r)
    (ht : t ∈ Icc a b) : HasDerivWithinAt f (w t) (Icc a b) t := by
  have : Fact (t ∈ Icc a b) := ⟨ht⟩
  have hab : a ≤ b := ht.1.trans ht.2
  have hint : IntervalIntegrable w volume a t :=
    (hw.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
  have hmeas : StronglyMeasurableAtFilter w (𝓝[Icc a b] t) :=
    ⟨Icc a b, self_mem_nhdsWithin, hw.aestronglyMeasurable measurableSet_Icc⟩
  have hd := intervalIntegral.integral_hasDerivWithinAt_right (s := Icc a b) (t := Icc a b)
    hint hmeas (hw t ht)
  exact (hd.const_add (f a)).congr (fun s hs ↦ hf s hs) (hf t ht)

/-! ### The edge coordinates of a Reinhardt trajectory -/

/-- The coordinate `x = X̃₀₀/X̃₁₀` of `X̃ = Rʲ X R⁻ʲ` at the time `τ`. -/
private noncomputable def l3b_x (j : Fin 3) (X : ℝ → Mat2) (τ : ℝ) : ℝ :=
  edgeFrame j (X τ) 0 0 / edgeFrame j (X τ) 1 0

/-- The coordinate `y = 1/X̃₁₀` of `X̃ = Rʲ X R⁻ʲ` at the time `τ`. -/
private noncomputable def l3b_y (j : Fin 3) (X : ℝ → Mat2) (τ : ℝ) : ℝ :=
  1 / edgeFrame j (X τ) 1 0

section Trajectory

variable {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}

/-- Along a Reinhardt trajectory, `X̃ = Rʲ X R⁻ʲ` is a star state, `X̃₁₀ > 0`, `X̃ = Φ(x, y)` and
`(x, y) ∈ 𝔥*` (`theorem4_4_1`). -/
private lemma l3b_star (h : IsStateTrajectory T u g X) (j : Fin 3) {τ : ℝ} (hτ : τ ∈ Icc 0 T) :
    IsStarState (edgeFrame j (X τ)) ∧ 0 < edgeFrame j (X τ) 1 0 ∧
      edgeFrame j (X τ) = Φ (l3b_x j X τ) (l3b_y j X τ) ∧
      (l3b_x j X τ, l3b_y j X τ) ∈ starDomain := by
  have hS := l3b_isStarState_edgeFrame j (h.2.2.2.1 τ hτ).2
  have hpos := l3b_pos_of_isStarState hS
  have hΦ : edgeFrame j (X τ) = Φ (l3b_x j X τ) (l3b_y j X τ) :=
    (l3b_Φ_eq hS.1 hS.2.1 hpos.ne').symm
  refine ⟨hS, hpos, hΦ, (theorem4_4_1 _ _ (by simp only [l3b_y]; positivity)).1 (hΦ ▸ hS)⟩

/-- `X̃ = Rʲ X R⁻ʲ` is continuous on `[0, T]`. -/
private lemma l3b_continuousOn (h : IsStateTrajectory T u g X) (j : Fin 3) :
    ContinuousOn (fun τ ↦ edgeFrame j (X τ)) (Icc 0 T) :=
  (continuousOn_const.mul (Matrix.continuousOn_of_eq_add_integral h.2.2.2.2.2)).mul
    continuousOn_const

/-- The coordinates `x`, `y` are continuous on `[0, T]`. -/
private lemma l3b_continuousOn_xy (h : IsStateTrajectory T u g X) (j : Fin 3) :
    ContinuousOn (l3b_x j X) (Icc 0 T) ∧ ContinuousOn (l3b_y j X) (Icc 0 T) := by
  have hc := continuousOn_iff_entrywise.1 (l3b_continuousOn h j)
  have hne : ∀ τ ∈ Icc 0 T, edgeFrame j (X τ) 1 0 ≠ 0 := fun τ hτ ↦ (l3b_star h j hτ).2.1.ne'
  exact ⟨(hc 0 0).div (hc 1 0) hne, continuousOn_const.div (hc 1 0) hne⟩

/-- **Lemma 4.5.2 on the edge** (TeX 6690–6700). At almost every time of `(c, d)`, where the
control lies in the edge `{u_j = 0}`, `x' = y` and `y' = f₂(x, y, u_e)`. -/
private lemma l3b_ae_hasDerivAt (h : IsStateTrajectory T u g X) (j : Fin 3) {c d : ℝ}
    (hc : 0 ≤ c) (hd : d ≤ T) (hu : ∀ᵐ t, t ∈ Ioo c d → u t j = 0) :
    ∀ᵐ τ, τ ∈ Ioo c d → HasDerivAt (l3b_x j X) (l3b_y j X τ) τ ∧
      HasDerivAt (l3b_y j X) (edgeF₂ (l3b_x j X τ) (l3b_y j X τ) (edgeParam j (u τ))) τ := by
  filter_upwards [h.2.2.2.2.2.ae_hasDerivAtEntrywise, hu] with τ hX hj hτ
  have hτ0 : τ ∈ Ioo 0 T := ⟨hc.trans_lt hτ.1, hτ.2.trans_le hd⟩
  have hτI : τ ∈ Icc 0 T := Ioo_subset_Icc_self hτ0
  obtain ⟨hS, hpos, hΦ, hstar⟩ := l3b_star h j hτI
  have huS := h.2.2.1 τ hτI
  have hue := edgeParam_mem_edgeControlSet (j := j) huS
  -- the rotated control is `(0, ½ + u_e, ½ - u_e)`
  have hZ : R ^ (j : ℕ) * controlMatrix (u τ) * R⁻¹ ^ (j : ℕ) =
      controlMatrix (edgeControl (edgeParam j (u τ))) := by
    rw [← edgeFrame, l3b_edgeFrame_controlMatrix, l3b_rot_eq_edgeControl huS (hj hτ)]
  -- `X̃' = [P̃, X̃]` with `P̃ = Z_{u'}/⟨Z_{u'}, X̃⟩`
  have hC := poly_Rinvpow_mul_Rpow (j : ℕ)
  have hXt : HasDerivAtEntrywise (fun s ↦ edgeFrame j (X s))
      (controlP (edgeControl (edgeParam j (u τ))) (edgeFrame j (X τ)) * edgeFrame j (X τ) -
        edgeFrame j (X τ) * controlP (edgeControl (edgeParam j (u τ))) (edgeFrame j (X τ))) τ := by
    have := ((hX hτ0).const_mul (R ^ (j : ℕ))).mul_const (R⁻¹ ^ (j : ℕ))
    refine this.congr_deriv ?_
    rw [poly_conj_bracket hC, poly_controlP_conj hC hZ]
    rfl
  -- `x = X̃₀₀/X̃₁₀` and `y = 1/X̃₁₀` are differentiable
  have hx := (hXt 0 0).div (hXt 1 0) hpos.ne'
  have hy := (hasDerivAt_const τ (1 : ℝ)).div (hXt 1 0) hpos.ne'
  -- near `τ`, `X̃ = Φ(x, y)`
  have hev : (fun s ↦ Φ (l3b_x j X s) (l3b_y j X s)) =ᶠ[𝓝 τ] fun s ↦ edgeFrame j (X s) :=
    eventually_of_mem (Ioo_mem_nhds hτ0.1 hτ0.2) fun s hs ↦
      (l3b_star h j (Ioo_subset_Icc_self hs)).2.2.1.symm
  have hΦd := hXt.congr_of_eventuallyEq hev
  rw [hΦ] at hΦd
  -- Lemma 4.5.2
  obtain ⟨hx', hy', -⟩ := lemma4_5_2 (l3b_x j X) (l3b_y j X) _ τ _ _ hstar
    (edgeControl_mem_controlSimplex hue) hx hy hΦd
  have hD := (edgeF₂_denom_neg hstar.2.1 hstar.2.2.1 hue).ne
  obtain ⟨hf₁, hf₂⟩ := l3b_halfPlaneF_edgeControl (y := l3b_y j X τ) hD
  exact ⟨hx.congr_deriv (hx'.trans hf₁), hy.congr_deriv (hy'.trans hf₂)⟩

/-- The coordinates `x`, `y` are absolutely continuous on `[c, d] ⊆ [0, T]`: the entries of `X̃`
are, and `X̃₁₀` is bounded below by a positive constant on `[c, d]`. -/
private lemma l3b_ac_xy (h : IsStateTrajectory T u g X) (j : Fin 3) {c d : ℝ} (hc : 0 ≤ c)
    (hcd : c ≤ d) (hd : d ≤ T) :
    AbsolutelyContinuousOnInterval (l3b_x j X) c d ∧
      AbsolutelyContinuousOnInterval (l3b_y j X) c d := by
  have hT : 0 ≤ T := hc.trans (hcd.trans hd)
  have hsub : uIcc c d ⊆ uIcc 0 T := by
    rw [uIcc_of_le hcd, uIcc_of_le hT]; exact Icc_subset_Icc hc hd
  have hXac : ∀ i k, AbsolutelyContinuousOnInterval (fun t ↦ X t i k) c d := fun i k ↦
    (h.2.2.2.2.2.absolutelyContinuousOnInterval hT i k).mono hsub
  have hXtac := l3b_ac_conj (R ^ (j : ℕ)) (R⁻¹ ^ (j : ℕ)) hXac
  -- a positive lower bound for `X̃₁₀` on `[c, d]`
  have hcont := (continuousOn_iff_entrywise.1 (l3b_continuousOn h j) 1 0).mono
    (Icc_subset_Icc hc hd)
  obtain ⟨τ₀, hτ₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hcd) hcont
  have hm : 0 < edgeFrame j (X τ₀) 1 0 :=
    (l3b_star h j ⟨hc.trans hτ₀.1, hτ₀.2.trans hd⟩).2.1
  have hmaps : MapsTo (fun t ↦ edgeFrame j (X t) 1 0) (uIcc c d) (Ici (edgeFrame j (X τ₀) 1 0)) :=
    fun t ht ↦ hmin (by rwa [uIcc_of_le hcd] at ht)
  have hyac : AbsolutelyContinuousOnInterval (l3b_y j X) c d :=
    (l3b_lipschitzOnWith_one_div hm).comp_absolutelyContinuousOnInterval hmaps (hXtac 1 0)
  refine ⟨((hXtac 0 0).fun_mul hyac).congr fun t _ ↦ ?_, hyac⟩
  simp only [l3b_x, l3b_y, mul_one_div]
  rfl

/-- **The edge state equations (8.1.3) in integral form**, in the original time: on `[c, d]`,
`x(τ) = x(c) + ∫_c^τ y` and `y(τ) = y(c) + ∫_c^τ f₂(x, y, u_e)`. -/
private lemma l3b_integral_xy (h : IsStateTrajectory T u g X) (j : Fin 3) {c d : ℝ}
    (hc : 0 ≤ c) (hcd : c ≤ d) (hd : d ≤ T) (hu : ∀ᵐ t, t ∈ Ioo c d → u t j = 0) :
    (IntervalIntegrable (l3b_y j X) volume c d ∧
      ∀ τ ∈ Icc c d, l3b_x j X τ = l3b_x j X c + ∫ σ in c..τ, l3b_y j X σ) ∧
    (IntervalIntegrable (fun τ ↦ edgeF₂ (l3b_x j X τ) (l3b_y j X τ) (edgeParam j (u τ)))
        volume c d ∧
      ∀ τ ∈ Icc c d, l3b_y j X τ = l3b_y j X c +
        ∫ σ in c..τ, edgeF₂ (l3b_x j X σ) (l3b_y j X σ) (edgeParam j (u σ))) := by
  obtain ⟨hxac, hyac⟩ := l3b_ac_xy h j hc hcd hd
  have hD := l3b_ae_hasDerivAt h j hc hd hu
  exact ⟨hxac.eq_add_integral_of_ae_hasDerivAt hcd (by
      filter_upwards [hD] with τ hτ hτI using (hτ hτI).1),
    hyac.eq_add_integral_of_ae_hasDerivAt hcd (by
      filter_upwards [hD] with τ hτ hτI using (hτ hτI).2)⟩

/-- The shift `t ↦ c + t` of an integrable function on `[c, d]` is integrable on `[0, d - c]`. -/
private lemma l3b_intervalIntegrable_shift {F : ℝ → ℝ} {c d : ℝ}
    (hF : IntervalIntegrable F volume c d) :
    IntervalIntegrable (fun s ↦ F (c + s)) volume 0 (d - c) := by
  simpa using hF.comp_add_left c

end Trajectory

/-- **The edge state equations** (8.1.3) (`eqn:xy-edge`; running text TeX 6678–6730). Let
`(g, X)` be a state trajectory of the Reinhardt problem on `[0, T]` whose control has
`u_j = 0` almost everywhere on `[c, d] ⊆ [0, T]`. After the rotation `X̃ = Rʲ X R⁻ʲ` the control
is `(0, ½ + u_e, ½ - u_e)` with `u_e = edgeParam j u` (`Rʲ Z_u R⁻ʲ = Z_{edgeControl u_e}`), the
point `z = x + iy` with `Φ(z) = X̃` lies in the star domain, and `(x, y, s)` (`edgeState j X c`)
with `s = ∫ dt/y` is an admissible trajectory of the edge control system: `x' = y`,
`y' = f₂(x, y, u_e)`, `s' = 1/y`, in the state space `y > 0`, `|x| < 1/√3`, with controls in
`[-½, ½]`.

Proof (TeX 6690–6700): `X̃ = Rʲ X R⁻ʲ` solves `X̃' = [P̃, X̃]` with
`P̃ = Z_{u'}/⟨Z_{u'}, X̃⟩`, `u'_m = u_{m+j}` (`poly_Rinv_conj_vertex` and the conjugation
invariance of the trace form, as in `poly_conj_pow_rhs`), and `X̃` is a star state
(`poly_isStarState_conj_pow`), so `X̃ = Φ(x, y)` with `(x, y) ∈ 𝔥*` (`lemma4_1_1`,
`theorem4_4_1`). Lemma 4.5.2 (`lemma4_5_2`) gives `(x', y') = (f₁, f₂)(x, y; u')` at almost every
time, and for `u' = (0, ½ + u_e, ½ - u_e)` the entries `Z₁₀ = 0`, `Z₀₀ = 2u_e/√3`, `Z₀₁ = -2/3`
give `f₁ = y` and `f₂ = 2√3 y² u_e/(-1 + 2√3 x u_e)` (field_simp). The integral form follows from
the absolute continuity of `x = X̃₀₀/X̃₁₀`, `y = 1/X̃₁₀` (`X̃₁₀ > 0`, bounded below on `[c, d]`).
Expected size: 150–300 lines. -/
theorem eqn_xy_edge {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2} (h : IsStateTrajectory T u g X)
    {j : Fin 3} {c d : ℝ} (hc : 0 ≤ c) (hcd : c < d) (hd : d ≤ T)
    (hu : ∀ᵐ t, t ∈ Ioo c d → u t j = 0) :
    Pontryagin.IsAdmissibleIn edgeField edgeDomain edgeControlSet (edgeState j X c 0) (d - c)
        (fun t ↦ edgeParam j (u (c + t))) (edgeState j X c) ∧
      (∀ t ∈ Icc 0 (d - c),
        edgeFrame j (X (c + t)) = Φ (edgeState j X c t 0) (edgeState j X c t 1) ∧
          (edgeState j X c t 0, edgeState j X c t 1) ∈ starDomain) ∧
      ∀ᵐ t, t ∈ Ioo c d →
        edgeFrame j (controlMatrix (u t)) = controlMatrix (edgeControl (edgeParam j (u t))) := by
  set q := edgeState j X c with hqdef
  have hq0 : ∀ t, q t 0 = l3b_x j X (c + t) := fun t ↦ rfl
  have hq1 : ∀ t, q t 1 = l3b_y j X (c + t) := fun t ↦ rfl
  have hq2 : ∀ t, q t 2 = ∫ τ in c..c + t, edgeFrame j (X τ) 1 0 := fun t ↦ rfl
  have hmem : ∀ t ∈ Icc 0 (d - c), c + t ∈ Icc c d := fun t ht ↦
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hmemT : ∀ τ ∈ Icc c d, τ ∈ Icc 0 T := fun τ hτ ↦ ⟨hc.trans hτ.1, hτ.2.trans hd⟩
  obtain ⟨⟨hyint, hxeq⟩, ⟨hfint, hyeq⟩⟩ := l3b_integral_xy h j hc hcd.le hd hu
  have hsint : IntervalIntegrable (fun τ ↦ edgeFrame j (X τ) 1 0) volume c d :=
    ((continuousOn_iff_entrywise.1 (l3b_continuousOn h j) 1 0).mono
      (Icc_subset_Icc hc hd)).intervalIntegrable_of_Icc hcd.le
  -- the components of the field along the edge state
  have hF : ∀ s, edgeField (q s) (edgeParam j (u (c + s))) =
      ![l3b_y j X (c + s), edgeF₂ (l3b_x j X (c + s)) (l3b_y j X (c + s)) (edgeParam j (u (c + s))),
        edgeFrame j (X (c + s)) 1 0] := by
    intro s
    simp only [edgeField, hq0, hq1, l3b_y, one_div_one_div]
  have hcomp : ∀ i, IntervalIntegrable (fun s ↦ edgeField (q s) (edgeParam j (u (c + s))) i)
      volume 0 (d - c) := by
    intro i
    simp only [hF]
    fin_cases i
    · exact l3b_intervalIntegrable_shift hyint
    · exact l3b_intervalIntegrable_shift hfint
    · exact l3b_intervalIntegrable_shift hsint
  have hint : IntervalIntegrable (fun s ↦ edgeField (q s) (edgeParam j (u (c + s)))) volume 0
      (d - c) :=
    ⟨Integrable.of_eval fun i ↦ (hcomp i).1, Integrable.of_eval fun i ↦ (hcomp i).2⟩
  have heq : ∀ t ∈ Icc 0 (d - c),
      q t = q 0 + ∫ s in (0 : ℝ)..t, edgeField (q s) (edgeParam j (u (c + s))) := by
    intro t ht
    have hsub : IntervalIntegrable (fun s ↦ edgeField (q s) (edgeParam j (u (c + s)))) volume 0
        t := hint.mono_set (by
      rw [uIcc_of_le ht.1, uIcc_of_le (by linarith : (0 : ℝ) ≤ d - c)]
      exact Icc_subset_Icc_right ht.2)
    funext i
    have e := ContinuousLinearMap.intervalIntegral_comp_comm
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 ↦ ℝ) i) hsub
    simp only [ContinuousLinearMap.proj_apply] at e
    rw [Pi.add_apply, ← e]
    simp only [hF]
    fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero, hq0, add_zero]
      rw [intervalIntegral.integral_comp_add_left (fun τ ↦ l3b_y j X τ), add_zero]
      exact hxeq (c + t) (hmem t ht)
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, hq1, add_zero]
      rw [intervalIntegral.integral_comp_add_left
        (fun τ ↦ edgeF₂ (l3b_x j X τ) (l3b_y j X τ) (edgeParam j (u τ))), add_zero]
      exact hyeq (c + t) (hmem t ht)
    · simp only [Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, hq2,
        add_zero, intervalIntegral.integral_same, zero_add]
      rw [intervalIntegral.integral_comp_add_left (fun τ ↦ edgeFrame j (X τ) 1 0), add_zero]
  have hdc : (0 : ℝ) ≤ d - c := by linarith
  refine ⟨⟨⟨?_, fun t ht ↦ edgeParam_mem_edgeControlSet (j := j) (h.2.2.1 _ (hmemT _ (hmem t ht))),
    ?_, hint, heq⟩, fun t ht ↦ ?_⟩, fun t ht ↦ ?_, ?_⟩
  · -- measurability of the edge control
    have hm : Measurable fun t ↦ u (c + t) := h.2.1.comp (measurable_const_add c)
    exact (((measurable_pi_apply _).comp hm).sub ((measurable_pi_apply _).comp hm)).div_const 2
  · -- continuity, from the integral form
    have hc' := intervalIntegral.continuousOn_primitive_interval' hint left_mem_uIcc
    rw [uIcc_of_le hdc] at hc'
    exact (continuousOn_const.add hc').congr heq
  · obtain ⟨-, -, -, hstar⟩ := l3b_star h j (hmemT _ (hmem t ht))
    exact ⟨hstar.1, hstar.2.1, hstar.2.2.1⟩
  · obtain ⟨-, -, hΦ, hstar⟩ := l3b_star h j (hmemT _ (hmem t ht))
    exact ⟨hΦ, hstar⟩
  · filter_upwards [hu] with t ht htI
    rw [l3b_edgeFrame_controlMatrix,
      l3b_rot_eq_edgeControl (h.2.2.1 t (hmemT t (Ioo_subset_Icc_self htI))) (ht htI)]

/-- **Equation (8.1.1)** (`eqn:g-edge`, TeX 6704–6723). On an interval `[c, d]` on which the
control lies in the edge `{u_j = 0}`, the state `g` is determined by the edge state `(x, y, s)`:
in the rotated frame `g̃ = Rʲ g R⁻ʲ`, `g̃(t) = g̃(c) h(c)⁻¹ h(t)` with
`h = [[1, -x], [s, 1 - sx]]` and `s(t) = ∫_c^t dτ/y` ((8.1.2)); in particular `g` depends on the
path only through the endpoint values of `(s, x)` (adding a constant to `s` leaves `g`
unchanged).

Proof: `g̃' = g̃ X̃` (`X̃ = Rʲ X R⁻ʲ`), and `h' = h Φ(x, y)` when `x' = y`, `s' = 1/y`
(`h⁻¹h' = [[x/y, -(x² + y²)/y], [1/y, -x/y]] = Φ(z)`, `det h = 1`; matrix ext and field_simp),
with `X̃ = Φ(x, y)` (`eqn_xy_edge`); both sides solve `G' = G X̃` with the same value at `c`, so
they agree (uniqueness for the linear equation, as `IsStateTrajectory.eq_conj_of_isIntegralCurve`
or Gronwall). Expected size: 100–200 lines. -/
theorem eqn_g_edge {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2} (h : IsStateTrajectory T u g X)
    {j : Fin 3} {c d : ℝ} (hc : 0 ≤ c) (hcd : c < d) (hd : d ≤ T)
    (hu : ∀ᵐ t, t ∈ Ioo c d → u t j = 0) :
    ∀ t ∈ Icc c d, edgeFrame j (g t) =
      edgeFrame j (g c) * (edgeH (edgeState j X c 0))⁻¹ * edgeH (edgeState j X c (t - c)) := by
  have hsub : Icc c d ⊆ Icc 0 T := Icc_subset_Icc hc hd
  obtain ⟨⟨-, hxeq⟩, -⟩ := l3b_integral_xy h j hc hcd.le hd hu
  obtain ⟨hxc, hyc⟩ := l3b_continuousOn_xy h j
  have hXtc := (l3b_continuousOn h j).mono hsub
  have hX10 := continuousOn_iff_entrywise.1 hXtc 1 0
  -- `s(τ) = ∫_c^τ X̃₁₀ = ∫_c^τ dσ/y`
  set s : ℝ → ℝ := fun τ ↦ ∫ σ in c..τ, edgeFrame j (X σ) 1 0 with hsdef
  have hseq : ∀ τ ∈ Icc c d, s τ = s c + ∫ σ in c..τ, edgeFrame j (X σ) 1 0 := fun τ _ ↦ by
    simp [hsdef]
  -- `h(τ) = [[1, -x], [s, 1 - s x]]`
  set H : ℝ → Mat2 := fun τ ↦ !![1, -l3b_x j X τ; s τ, 1 - s τ * l3b_x j X τ] with hHdef
  have hH : ∀ τ, edgeH (edgeState j X c (τ - c)) = H τ := fun τ ↦ by
    simp only [edgeH, edgeState, add_sub_cancel, hHdef, hsdef]
    rfl
  -- `h' = h X̃` on `[c, d]`
  have hx' : ∀ τ ∈ Icc c d, HasDerivWithinAt (l3b_x j X) (l3b_y j X τ) (Icc c d) τ :=
    fun τ hτ ↦ l3b_hasDerivWithinAt_of_eq_add_integral (hyc.mono hsub) hxeq hτ
  have hs' : ∀ τ ∈ Icc c d, HasDerivWithinAt s (edgeFrame j (X τ) 1 0) (Icc c d) τ :=
    fun τ hτ ↦ l3b_hasDerivWithinAt_of_eq_add_integral hX10 hseq hτ
  have hHd : ∀ τ ∈ Ico c d, HasDerivWithinAtEntrywise H (H τ * edgeFrame j (X τ)) (Icc c d) τ := by
    intro τ hτ
    have hτ' := Ico_subset_Icc_self hτ
    obtain ⟨hS, hpos, -, -⟩ := l3b_star h j (hsub hτ')
    have hd' : HasDerivWithinAtEntrywise H
        !![0, -l3b_y j X τ; edgeFrame j (X τ) 1 0,
          -(edgeFrame j (X τ) 1 0 * l3b_x j X τ + s τ * l3b_y j X τ)] (Icc c d) τ := by
      rw [hasDerivWithinAtEntrywise_fin_two_iff]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [hHdef] using hasDerivWithinAt_const τ (Icc c d) (1 : ℝ)
      · have := (hx' τ hτ').fun_neg
        simp only [hHdef, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
          Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one]
        exact this
      · simpa [hHdef] using hs' τ hτ'
      · have := ((hs' τ hτ').mul (hx' τ hτ')).const_sub 1
        simp only [hHdef, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one]
        convert this using 1
    refine hd'.congr_deriv ?_
    obtain ⟨htr, hdet, -⟩ := hS
    rw [Matrix.trace_fin_two] at htr
    rw [Matrix.det_fin_two] at hdet
    have h0 := hpos.ne'
    have hdd : edgeFrame j (X τ) 1 1 = -edgeFrame j (X τ) 0 0 := by linarith
    have hb : edgeFrame j (X τ) 0 1 = -(1 + edgeFrame j (X τ) 0 0 ^ 2) / edgeFrame j (X τ) 1 0 := by
      rw [eq_div_iff h0]; rw [hdd] at hdet; linarith
    ext i k
    fin_cases i <;> fin_cases k <;>
      simp only [hHdef, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Fin.zero_eta, Fin.mk_one, Fin.isValue, l3b_x, l3b_y, hb, hdd] <;>
      field_simp <;> ring
  -- `g̃' = g̃ X̃` on `[c, d]`
  have hgI := h.2.2.2.2.1
  have hgc : ContinuousOn g (Icc 0 T) := Matrix.continuousOn_of_eq_add_integral hgI
  have hXc : ContinuousOn X (Icc 0 T) := Matrix.continuousOn_of_eq_add_integral h.2.2.2.2.2
  set G : ℝ → Mat2 := fun τ ↦ edgeFrame j (g τ) with hGdef
  have hGc : ContinuousOn G (Icc c d) :=
    ((continuousOn_const.mul hgc).mul continuousOn_const).mono hsub
  have hGd : ∀ τ ∈ Ico c d, HasDerivWithinAtEntrywise G (G τ * edgeFrame j (X τ)) (Icc c d) τ := by
    intro τ hτ
    have hτT := hsub (Ico_subset_Icc_self hτ)
    have hg' := (Matrix.hasDerivWithinAtEntrywise_of_eq_add_integral hgI hτT
      ((hgc.mul hXc) τ hτT)).mono hsub
    refine ((hg'.const_mul (R ^ (j : ℕ))).mul_const (R⁻¹ ^ (j : ℕ))).congr_deriv ?_
    exact poly_conj_mul (poly_Rinvpow_mul_Rpow (j : ℕ)) _ _
  -- `det h = 1`, so `G(c) h(c)⁻¹ h` solves the same equation with the same initial value
  have hHc : ContinuousOn H (Icc c d) := by
    refine continuousOn_iff_entrywise.2 fun i k ↦ ?_
    have hs : ContinuousOn s (Icc c d) := fun τ hτ ↦ (hs' τ hτ).continuousWithinAt
    fin_cases i <;> fin_cases k <;> simp only [hHdef, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Fin.zero_eta, Fin.mk_one, Fin.isValue]
    · exact continuousOn_const
    · exact (hxc.mono hsub).neg
    · exact hs
    · exact continuousOn_const.sub (hs.mul (hxc.mono hsub))
  have hdetH : (H c).det = 1 := by
    simp only [hHdef, Matrix.det_fin_two_of]; ring
  have hHinv : (H c)⁻¹ * H c = 1 := Matrix.nonsing_inv_mul _ (by rw [hdetH]; exact isUnit_one)
  have hY : EqOn G (fun τ ↦ G c * (H c)⁻¹ * H τ) (Icc c d) := by
    refine Matrix.ODE_solution_unique_mul_right hXtc hGc hGd
      (continuousOn_const.mul hHc) (fun τ hτ ↦ ?_) ?_
    · exact ((hHd τ hτ).const_mul (G c * (H c)⁻¹)).congr_deriv (by simp only [Matrix.mul_assoc])
    · simp only [Matrix.mul_assoc, hHinv, Matrix.mul_one]
  intro t ht
  have hc0 := hH c
  rw [sub_self] at hc0
  rw [hH, hc0]
  exact hY ht

/-- **The cost of an edge arc** (running text TeX 6739–6754, with (8.1.5), `eqn:edge:cost`).
On an interval `[c, d]` on which the control lies in the edge `{u_j = 0}`, the Reinhardt cost
`-(3/2) ∫_c^d ⟨J, X⟩` equals `(3/2) ((s + x)|_c^d + ∫_c^d x²/y)`: by (4.3.1),
`-(3/2)⟨J, Φ(z)⟩ = (3/2)(1 + x² + y²)/y`, and `(1 + x² + y²)/y = s' + x' + x²/y`. So, up to the
positive factor `3/2` and the constant `(s₁ + x₁) - (s₀ + x₀)` fixed by the boundary conditions,
the cost is the edge cost `∫ φ_edge`, `φ_edge = x²/y`.

Proof: `⟨J, Rʲ X R⁻ʲ⟩ = ⟨J, X⟩` (`J` commutes with `R`, `poly_conj_pow_J`), the explicit
`⟨J, Φ(x, y)⟩ = -(1 + x² + y²)/y`, and the fundamental theorem of calculus for the absolutely
continuous `x` and `s` (`eqn_xy_edge`). Expected size: 80–150 lines. -/
theorem edgeCost_identity {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsStateTrajectory T u g X) {j : Fin 3} {c d : ℝ} (hc : 0 ≤ c) (hcd : c < d) (hd : d ≤ T)
    (hu : ∀ᵐ t, t ∈ Ioo c d → u t j = 0) :
    -(3 / 2) * ∫ t in c..d, traceForm J (X t) =
      3 / 2 * ((edgeState j X c (d - c) 2 + edgeState j X c (d - c) 0) -
          (edgeState j X c 0 2 + edgeState j X c 0 0) +
        ∫ t in (0 : ℝ)..d - c, edgeCost (edgeState j X c t) (edgeParam j (u (c + t)))) := by
  have hmemT : ∀ τ ∈ Icc c d, τ ∈ Icc 0 T := fun τ hτ ↦ ⟨hc.trans hτ.1, hτ.2.trans hd⟩
  obtain ⟨⟨hyint, hxeq⟩, -⟩ := l3b_integral_xy h j hc hcd.le hd hu
  have hXt := (continuousOn_iff_entrywise.1 (l3b_continuousOn h j) 1 0).mono
    (Icc_subset_Icc hc hd)
  have hsint : IntervalIntegrable (fun τ ↦ edgeFrame j (X τ) 1 0) volume c d :=
    hXt.intervalIntegrable_of_Icc hcd.le
  obtain ⟨hxc, hyc⟩ := l3b_continuousOn_xy h j
  have hφint : IntervalIntegrable (fun τ ↦ l3b_x j X τ ^ 2 / l3b_y j X τ) volume c d := by
    refine ContinuousOn.intervalIntegrable_of_Icc hcd.le ?_
    refine ((hxc.pow 2).div hyc fun τ hτ ↦ ?_).mono (Icc_subset_Icc hc hd)
    have := (l3b_star h j hτ).2.2.2.1
    exact this.ne'
  -- `⟨J, X⟩ = ⟨J, Φ(z)⟩ = -(1 + x² + y²)/y = -(s' + x' + x²/y)` on `[c, d]` (equation (4.3.1))
  have hJ : ∀ τ ∈ uIcc c d, traceForm J (X τ) =
      -(edgeFrame j (X τ) 1 0 + l3b_y j X τ + l3b_x j X τ ^ 2 / l3b_y j X τ) := by
    intro τ hτ
    rw [uIcc_of_le hcd.le] at hτ
    obtain ⟨-, -, hΦ, hstar⟩ := l3b_star h j (hmemT τ hτ)
    have hy := hstar.1.ne'
    rw [← l3b_traceForm_J_edgeFrame j, hΦ]
    simp only [traceForm, J, Φ, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    field_simp
    ring
  rw [intervalIntegral.integral_congr hJ, intervalIntegral.integral_neg,
    intervalIntegral.integral_add (hsint.add hyint) hφint,
    intervalIntegral.integral_add hsint hyint]
  -- `∫ s' = s(d)`, `∫ x' = x(d) - x(c)`, and the time shift in `∫ φ_edge`
  have hs : edgeState j X c (d - c) 2 = ∫ τ in c..d, edgeFrame j (X τ) 1 0 := by
    change ∫ τ in c..c + (d - c), edgeFrame j (X τ) 1 0 = _
    rw [add_sub_cancel]
  have hs0 : edgeState j X c 0 2 = 0 := by
    change ∫ τ in c..c + 0, edgeFrame j (X τ) 1 0 = 0
    rw [add_zero, intervalIntegral.integral_same]
  have hx1 : edgeState j X c (d - c) 0 = l3b_x j X d := by
    change l3b_x j X (c + (d - c)) = _
    rw [add_sub_cancel]
  have hx0 : edgeState j X c 0 0 = l3b_x j X c := by
    change l3b_x j X (c + 0) = _
    rw [add_zero]
  have hφ : ∫ t in (0 : ℝ)..d - c, edgeCost (edgeState j X c t) (edgeParam j (u (c + t))) =
      ∫ τ in c..d, l3b_x j X τ ^ 2 / l3b_y j X τ := by
    change ∫ t in (0 : ℝ)..d - c, l3b_x j X (c + t) ^ 2 / l3b_y j X (c + t) = _
    rw [intervalIntegral.integral_comp_add_left (fun τ ↦ l3b_x j X τ ^ 2 / l3b_y j X τ),
      add_zero, add_sub_cancel]
  have hxd := hxeq d ⟨hcd.le, le_rfl⟩
  rw [hs, hs0, hx1, hx0, hφ, hxd]
  ring

/-- A covector on `ℝ³` in terms of its values `λ₁, λ₂, λ₃` on the basis vectors. -/
theorem apply_eq_sum_edgeCostate (p : StrongDual ℝ (Fin 3 → ℝ)) (w : Fin 3 → ℝ) :
    p w = w 0 * edgeCostate p 0 + w 1 * edgeCostate p 1 + w 2 * edgeCostate p 2 := by
  have hw : w = w 0 • Pi.single 0 1 + w 1 • Pi.single 1 1 + w 2 • Pi.single 2 1 := by
    ext i; fin_cases i <;> simp
  conv_lhs => rw [hw]
  simp only [map_add, map_smul, smul_eq_mul, edgeCostate]

/-- The partial derivatives of the state equations (8.1.3) of the edge problem, at a point where
`y ≠ 0` and `-1 + 2√3 x u_e ≠ 0`. -/
theorem fderiv_edgeField_apply {q : Fin 3 → ℝ} {ue : ℝ} (hy : q 1 ≠ 0)
    (hD : -1 + 2 * √3 * q 0 * ue ≠ 0) (v : Fin 3 → ℝ) :
    fderiv ℝ (fun q ↦ edgeField q ue) q v =
      ![v 1, -(12 * q 1 ^ 2 * ue ^ 2 / (-1 + 2 * √3 * q 0 * ue) ^ 2) * v 0 +
        4 * √3 * q 1 * ue / (-1 + 2 * √3 * q 0 * ue) * v 1, -(v 1 / q 1 ^ 2)] := by
  have hdiff : DifferentiableAt ℝ (fun q ↦ edgeField q ue) q := by
    refine differentiableAt_pi.2 fun i ↦ ?_
    fin_cases i <;> simp only [edgeField, edgeF₂, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons, Fin.isValue] <;> fun_prop (disch := assumption)
  have hl : HasDerivAt (fun s : ℝ ↦ q + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add q
  have h1 : HasDerivAt (fun s : ℝ ↦ edgeField (q + s • v) ue)
      (fderiv ℝ (fun q ↦ edgeField q ue) q v) 0 := by
    have hf' : HasFDerivAt (fun q ↦ edgeField q ue) (fderiv ℝ (fun q ↦ edgeField q ue) q)
        (q + (0 : ℝ) • v) := by simpa using hdiff.hasFDerivAt
    exact hf'.comp_hasDerivAt (0 : ℝ) hl
  refine h1.unique (hasDerivAt_pi.2 fun i ↦ ?_)
  have hx : HasDerivAt (fun s : ℝ ↦ q 0 + s * v 0) (v 0) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v 0)).const_add (q 0)
  have hy' : HasDerivAt (fun s : ℝ ↦ q 1 + s * v 1) (v 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v 1)).const_add (q 1)
  fin_cases i
  · simpa [edgeField] using hy'
  · simp only [edgeField, edgeF₂, Fin.mk_one, Matrix.cons_val_one,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero]
    have hD0 : -1 + 2 * √3 * (q 0 + (0 : ℝ) * v 0) * ue ≠ 0 := by simpa using hD
    have h := (((hy'.fun_pow 2).const_mul (2 * √3)).mul_const ue).fun_div
      (((hx.const_mul (2 * √3)).mul_const ue).const_add (-1)) hD0
    convert h using 1
    have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    simp only [zero_mul, add_zero]
    field_simp
    ring_nf
    simp only [h3]
    ring
  · simp only [edgeField, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h := (hasDerivAt_const (0 : ℝ) (1 : ℝ)).fun_div hy' (by simpa using hy)
    convert h using 1
    simp only [zero_mul, add_zero]
    field_simp
    ring

/-- The partial derivatives of the edge cost `φ_edge = x²/y`, at a point where `y ≠ 0`. -/
theorem fderiv_edgeCost_apply {q : Fin 3 → ℝ} {ue : ℝ} (hy : q 1 ≠ 0) (v : Fin 3 → ℝ) :
    fderiv ℝ (fun q ↦ edgeCost q ue) q v = 2 * q 0 / q 1 * v 0 - q 0 ^ 2 / q 1 ^ 2 * v 1 := by
  have hdiff : DifferentiableAt ℝ (fun q ↦ edgeCost q ue) q := by
    simp only [edgeCost]; fun_prop (disch := assumption)
  have hl : HasDerivAt (fun s : ℝ ↦ q + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add q
  have h1 : HasDerivAt (fun s : ℝ ↦ edgeCost (q + s • v) ue)
      (fderiv ℝ (fun q ↦ edgeCost q ue) q v) 0 := by
    have hf' : HasFDerivAt (fun q ↦ edgeCost q ue) (fderiv ℝ (fun q ↦ edgeCost q ue) q)
        (q + (0 : ℝ) • v) := by simpa using hdiff.hasFDerivAt
    exact hf'.comp_hasDerivAt (0 : ℝ) hl
  have hx : HasDerivAt (fun s : ℝ ↦ q 0 + s * v 0) (v 0) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v 0)).const_add (q 0)
  have hy' : HasDerivAt (fun s : ℝ ↦ q 1 + s * v 1) (v 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v 1)).const_add (q 1)
  refine h1.unique ?_
  simp only [edgeCost, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h := (hx.fun_pow 2).fun_div hy' (by simpa using hy)
  convert h using 1
  simp only [zero_mul, add_zero]
  field_simp
  ring


/-- The Hamiltonian (8.1.6) of the edge control problem,
`H = λ₁ y + λ₂ f₂(x, y, u_e) + λ₃/y + λ_cost x²/y` (`eqn:edge:ham`). -/
noncomputable def edgeHamiltonian (lam l₁ l₂ l₃ x y ue : ℝ) : ℝ :=
  l₁ * y + l₂ * edgeF₂ x y ue + l₃ / y + lam * (x ^ 2 / y)

/-- **Equation (8.1.6)** (`eqn:edge:ham`): the Hamiltonian `⟨p, f(q, u_e)⟩ + λ_cost φ_edge(q)` of
the maximum principle for the edge control problem is
`λ₁ y + λ₂ f₂(x, y, u_e) + λ₃/y + λ_cost x²/y`, `λ_{i+1} = p(e_i)`. Proof: linearity of `p`
(`edgeField q u_e = y e₀ + f₂ e₁ + (1/y) e₂`). Expected size: 10–20 lines. -/
theorem eqn_edge_ham (ν : ℝ) (q : Fin 3 → ℝ) (p : StrongDual ℝ (Fin 3 → ℝ)) (ue : ℝ) :
    Pontryagin.controlHamiltonian edgeField edgeCost ν q p ue =
      edgeHamiltonian ν (edgeCostate p 0) (edgeCostate p 1) (edgeCostate p 2) (q 0) (q 1) ue := by
  rw [Pontryagin.controlHamiltonian, apply_eq_sum_edgeCostate, edgeHamiltonian, edgeCost]
  simp only [edgeField, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  ring

/-- The right-hand side `λ₂ · 12 y² u_e² / (1 - 2√3 x u_e)² - 2 λ_cost x/y` of the costate
equation for `λ₁` in (8.1.7) (`eqn:costate-edge`), `= -∂H/∂x`. -/
noncomputable def edgeCostateRHS₁ (lam l₂ x y ue : ℝ) : ℝ :=
  l₂ * (12 * y ^ 2 * ue ^ 2 / (1 - 2 * √3 * x * ue) ^ 2) - 2 * lam * x / y

/-- The right-hand side
`λ₃/y² - λ₁ - λ₂ · 4√3 y u_e / (-1 + 2√3 x u_e) + λ_cost x²/y²` of the costate equation for `λ₂`
in (8.1.7) (`eqn:costate-edge`), `= -∂H/∂y`. -/
noncomputable def edgeCostateRHS₂ (lam l₁ l₂ l₃ x y ue : ℝ) : ℝ :=
  l₃ / y ^ 2 - l₁ - l₂ * (4 * √3 * y * ue / (-1 + 2 * √3 * x * ue)) + lam * x ^ 2 / y ^ 2

/-- **The costate equations (8.1.7)** (`eqn:costate-edge`, TeX 6822–6838, in the proof of
Theorem 8.1.4). Along an extremal of the edge control problem the costates `λ₁, λ₂, λ₃` (dual to
`x, y, s`) satisfy `λ₁' = -∂H/∂x = λ₂ 12 y² u_e²/(1 - 2√3 x u_e)² - 2 λ_cost x/y`,
`λ₂' = -∂H/∂y = λ₃/y² - λ₁ - λ₂ 4√3 y u_e/(-1 + 2√3 x u_e) + λ_cost x²/y²` and
`λ₃' = -∂H/∂s = 0`, in integral form ("We note that `λ₃` is constant").

Proof: the adjoint equation `p' = -p ∘ ∂ₓf - ν ∂ₓφ` (`Pontryagin.IsAdjoint`) evaluated on the
basis vectors `e₀, e₁, e₂`, with the partial derivatives of `edgeField` and `edgeCost`
(`∂f₂/∂x = -12 y² u_e²/(-1 + 2√3 x u_e)²`, `∂f₂/∂y = 4√3 y u_e/(-1 + 2√3 x u_e)`; nothing depends
on `s`), and the change from the backward form `p(t) = p(T) + ∫ₜᵀ` to the forward one.
Expected size: 80–150 lines. -/
theorem eqn_costate_edge {T : ℝ} {ue : ℝ → ℝ} {q : ℝ → Fin 3 → ℝ} {ν : ℝ}
    {p : ℝ → StrongDual ℝ (Fin 3 → ℝ)} (h : IsEdgeProblemExtremal T ue q ν p) :
    (∀ t ∈ Icc 0 T, edgeCostate (p t) 2 = edgeCostate (p 0) 2) ∧
      IntervalIntegrable
        (fun t ↦ edgeCostateRHS₁ ν (edgeCostate (p t) 1) (q t 0) (q t 1) (ue t)) volume 0 T ∧
      (∀ t ∈ Icc 0 T, edgeCostate (p t) 0 = edgeCostate (p 0) 0 +
        ∫ s in (0 : ℝ)..t, edgeCostateRHS₁ ν (edgeCostate (p s) 1) (q s 0) (q s 1) (ue s)) ∧
      IntervalIntegrable (fun t ↦ edgeCostateRHS₂ ν (edgeCostate (p t) 0) (edgeCostate (p t) 1)
        (edgeCostate (p t) 2) (q t 0) (q t 1) (ue t)) volume 0 T ∧
      ∀ t ∈ Icc 0 T, edgeCostate (p t) 1 = edgeCostate (p 0) 1 +
        ∫ s in (0 : ℝ)..t, edgeCostateRHS₂ ν (edgeCostate (p s) 0) (edgeCostate (p s) 1)
          (edgeCostate (p s) 2) (q s 0) (q s 1) (ue s) := by
  obtain ⟨hT, ⟨⟨-, hU, -, -, -⟩, hΩ⟩, -, -, ⟨hint, hp⟩, -, -⟩ := h
  -- the integrand of the adjoint equation `p' = -p ∘ ∂f/∂q - ν ∂φ/∂q`
  set F : ℝ → StrongDual ℝ (Fin 3 → ℝ) := fun r ↦
    (p r).comp (Pontryagin.linearization edgeField ue q r) +
      ν • fderiv ℝ (edgeCost · (ue r)) (q r) with hFdef
  -- evaluated on the basis vectors: `-∂H/∂x`, `-∂H/∂y`, `-∂H/∂s` up to sign
  have hF : ∀ r ∈ Icc 0 T,
      F r (Pi.single 0 1) = -edgeCostateRHS₁ ν (edgeCostate (p r) 1) (q r 0) (q r 1) (ue r) ∧
      F r (Pi.single 1 1) = -edgeCostateRHS₂ ν (edgeCostate (p r) 0) (edgeCostate (p r) 1)
        (edgeCostate (p r) 2) (q r 0) (q r 1) (ue r) ∧ F r (Pi.single 2 1) = 0 := by
    intro r hr
    have hD := (edgeF₂_denom_neg (hΩ r hr).2.1 (hΩ r hr).2.2 (hU r hr)).ne
    have hy := (hΩ r hr).1.ne'
    simp only [hFdef, _root_.add_apply, ContinuousLinearMap.comp_apply,
      _root_.smul_apply, Pontryagin.linearization, fderiv_edgeField_apply hy hD,
      fderiv_edgeCost_apply hy, smul_eq_mul, apply_eq_sum_edgeCostate (p r), edgeCostateRHS₁,
      edgeCostateRHS₂]
    have hD2 : (1 - 2 * √3 * q r 0 * ue r) ^ 2 = (-1 + 2 * √3 * q r 0 * ue r) ^ 2 := by ring
    refine ⟨?_, ?_, ?_⟩ <;> simp [hD2] <;> ring
  -- evaluation at a vector is a continuous linear map on covectors
  have hev : ∀ w : Fin 3 → ℝ, IntervalIntegrable (fun r ↦ F r w) volume 0 T := fun w ↦
    ⟨(ContinuousLinearMap.apply ℝ ℝ w).integrable_comp hint.1,
      (ContinuousLinearMap.apply ℝ ℝ w).integrable_comp hint.2⟩
  -- the forward form `p(t) w = p(0) w - ∫₀ᵗ F w`
  have hfwd : ∀ w : Fin 3 → ℝ, ∀ t ∈ Icc 0 T,
      p t w = p 0 w + ∫ r in (0 : ℝ)..t, -F r w := by
    intro w t ht
    have hsub : ∀ a ∈ Icc 0 T, IntervalIntegrable F volume a T := fun a ha ↦
      hint.mono_set (by rw [uIcc_of_le ha.2, uIcc_of_le hT.le]; exact Icc_subset_Icc_left ha.1)
    have hval : ∀ a ∈ Icc 0 T, p a w = p T w + ∫ r in a..T, F r w := fun a ha ↦ by
      have e := (ContinuousLinearMap.apply ℝ ℝ w).intervalIntegral_comp_comm (hsub a ha)
      simp only [ContinuousLinearMap.apply_apply] at e
      rw [hp a ha, _root_.add_apply, e]
    have h0t : IntervalIntegrable (fun r ↦ F r w) volume 0 t := (hev w).mono_set (by
      rw [uIcc_of_le ht.1, uIcc_of_le hT.le]; exact Icc_subset_Icc_right ht.2)
    have htT : IntervalIntegrable (fun r ↦ F r w) volume t T := (hev w).mono_set (by
      rw [uIcc_of_le ht.2, uIcc_of_le hT.le]; exact Icc_subset_Icc_left ht.1)
    rw [hval t ht, hval 0 ⟨le_rfl, hT.le⟩, intervalIntegral.integral_neg,
      ← intervalIntegral.integral_add_adjacent_intervals h0t htT]
    ring
  have hIoc : ∀ r ∈ Ι (0 : ℝ) T, r ∈ Icc 0 T := fun r hr ↦ by
    rw [uIoc_of_le hT.le] at hr; exact ⟨hr.1.le, hr.2⟩
  have hcongr : ∀ t ∈ Icc 0 T, ∀ r ∈ uIcc 0 t, r ∈ Icc 0 T := fun t ht r hr ↦ by
    rw [uIcc_of_le ht.1] at hr; exact ⟨hr.1, hr.2.trans ht.2⟩
  refine ⟨fun t ht ↦ ?_, ?_, fun t ht ↦ ?_, ?_, fun t ht ↦ ?_⟩
  · rw [edgeCostate, edgeCostate, hfwd _ t ht]
    rw [intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun r hr ↦ by
      simp only [(hF r (hcongr t ht r hr)).2.2, neg_zero] ]
    simp
  · exact (hev (Pi.single 0 1)).neg.congr fun r hr ↦ by
      simp only [Pi.neg_apply, (hF r (hIoc r hr)).1, neg_neg]
  · rw [edgeCostate, edgeCostate, hfwd _ t ht]
    congr 1
    exact intervalIntegral.integral_congr fun r hr ↦ by
      simp only [(hF r (hcongr t ht r hr)).1, neg_neg]
  · exact (hev (Pi.single 1 1)).neg.congr fun r hr ↦ by
      simp only [Pi.neg_apply, (hF r (hIoc r hr)).2.1, neg_neg]
  · rw [edgeCostate, edgeCostate, hfwd _ t ht]
    congr 1
    exact intervalIntegral.integral_congr fun r hr ↦ by
      simp only [(hF r (hcongr t ht r hr)).2.1, neg_neg]

end SmoothedPolygons
