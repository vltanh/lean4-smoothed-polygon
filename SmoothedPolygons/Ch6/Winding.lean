module

public import SmoothedPolygons.Ch3.ControlProblem
public import Basic.Analysis.Calculus.MatrixFTC
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Order.IntermediateValue

/-!
# The winding number of an admissible trajectory

Problem 3.6.2 asks for `g(0) = I`, `g(t_f) = R` and `X(t_f) = R⁻¹X(0)R`. The book derives these
conditions so that "the curves `σ_j` close up seamlessly to form a simple closed curve" (§3.5,
TeX 3134–3139), but they do not force simplicity. Along an admissible trajectory the curve
`σ₀(t) = g(t) s₀*` turns counterclockwise about the origin (`det(s₀*, X s₀*) = X₁₀ > 0`), and
its continuous angle `θ` with `θ(0) = 0` ends at `θ(t_f) = π/3 + 2πm` for some `m ∈ ℕ`
(`g(t_f) s₀* = R s₀* = s₁*`); extended by `g(t + t_f) = g(t) R`, the closed curve `σ₀` on
`[0, 6t_f]` winds `1 + 6m` times around the origin. The book's construction (Chapters 2–3) only
produces `m = 0`; it notes in the proof of Lemma 7.5.5 (TeX 6322–6326) that other choices of
eigenvalues "will produce the right boundary conditions, but the corresponding multi-curves will
have the wrong winding number around the origin".

* `IsWindingOne T g`: the angle of `g(t) s₀*` increases by exactly `π/3` on `[0, T]` (`m = 0`).
* `exists_isReinhardtAdmissible_not_isWindingOne` (**the answer to the winding-number question**):
  admissible trajectories of higher winding exist. The unit circle traversed seven times
  (`X ≡ J`, `u ≡ (1/3, 1/3, 1/3)`, `g(t) = exp(tJ)`, `t_f = 7π/3`) is admissible, has winding
  number `7` and cost `7π`, and is not the boundary trajectory of a balanced pair with period
  parameter `t_f = 7π/3` and `σ_j = g s_j*` (`σ₀(0) = σ₀(2π)`, so `σ₀` is not injective on
  `[0, 6t_f)`); the unit disk is a balanced pair for `t_f = π/3`, but its area `π` is not the
  cost `7π`. Hence the converse of
  Problem 3.6.2 (E15) is false for all admissible trajectories, and holds only for those of
  winding number one (`exists_isBalancedPair_of_isReinhardtAdmissible`,
  `SmoothedPolygons/Ch6/AdmissibleDisk.lean`).
* `three_halves_mul_angle_le_reinhardtCost`: **higher winding costs more**: the cost is at least
  `(3/2)θ(t_f) = π/2 + 3πm`. Hence an admissible trajectory with cost `< 7π/2` (for instance one
  cheaper than the smoothed octagon, of cost `≈ 3.126`) has winding number one
  (`isWindingOne_of_reinhardtCost_lt`). So the existence of a global minimizer is not affected by
  the higher-winding trajectories, and Theorem 5.0.2 can be applied to every competitor that
  matters.

## Proof of the cost bound (not in the book)

Write `g = n(ν) a(ρ) k(ψ)` (Iwasawa decomposition `NAK`: `n(ν) = [[1, ν], [0, 1]]`,
`a(ρ) = diag(e^ρ, e^{-ρ})`, `k(ψ)` the rotation by `ψ`), so that the reversed bottom row of `g` is
`(g₁₁, g₁₀) = e^{-ρ}(cos ψ, sin ψ)`: the rotation angle `ψ` of the decomposition is the polar
angle of `(g₁₁, g₁₀)`, and it is all of the decomposition that the argument uses. Write
`X = [[a, b], [c, -a]]` (so `c > 0` from `ρ₀(X) + ρ₁(X) = 2c/√3 > 0`, and `-a² - bc = det X = 1`),
`κ = c - b = -tr(JX)` (so that the cost is `(3/2)∫κ`), and `(p, q) = (g₁₀, g₁₁)`.

1. The bottom row satisfies `(p, q)' = (p, q) X`, so (`wn_row_im_le`)
   `ψ' = (q p' - p q')/(p² + q²) = (2apq + cq² - bp²)/(p² + q²)`, and
   `κ - ψ' = (cp² - 2apq - bq²)/(p² + q²) ≥ 0`, because
   `c (cp² - 2apq - bq²) = (cp - aq)² + q² det X ≥ 0` and `c > 0`. (In the coordinates of the
   upper half-plane, `w = g · i = ν + i e^{2ρ} = X_h + iY_h`, this is the combination of the
   identity `κ = 2ψ' - X_h'/Y_h` and the bound `|X_h'|/Y_h ≤ √(κ² - 4) ≤ κ` on the hyperbolic speed
   of `g · i`: `κ - ψ' = (κ - X_h'/Y_h)/2`. The direct computation above needs neither.)
2. Integrating, `ψ(t_f) = ∫ψ' ≤ ∫κ = (2/3) cost`.
3. `ψ(t_f) = θ(t_f)`: the vectors `(g₀₀, g₁₀)` (angle `θ`) and `(g₁₁, g₁₀)` (angle `ψ`) are never
   opposite (they share the second coordinate, and if it vanishes `g₀₀g₁₁ = det g = 1 > 0`), so
   the continuous function `θ - ψ`, which vanishes at `0`, never reaches `±π` and stays in
   `(-π, π)` (intermediate value theorem, `wn_abs_lt_pi`); at `t_f` the two vectors coincide
   (`g(t_f) = R`, `R₀₀ = R₁₁`), so `θ(t_f) - ψ(t_f) ∈ 2πℤ ∩ (-π, π) = {0}`.

The angles are built as phases `∫ Im(z'/z)` of the complex curves `z = g₀₀ + i g₁₀` and
`z = g₁₁ + i g₁₀` (`wn_angle`, `wn_angle_polar`): `g` is `C¹` on `[0, t_f]`, because `g' = gX`
with `X` continuous (both are indefinite integrals). For `θ` this gives
`θ' = X₁₀ det g/|z|² > 0` (`wn_col_im`), whence `exists_angle_of_isReinhardtAdmissible`.
-/

@[expose] public section

namespace SmoothedPolygons

open MeasureTheory Set Matrix

/-- An admissible trajectory has **winding number one** on `[0, T]`: the continuous angle `θ` of
`σ₀(t) = g(t) s₀*` with `θ(0) = 0` ends at `θ(T) = π/3` (rather than `π/3 + 2πm`, `m ≥ 1`), so
that the closed curve `σ₀` on `[0, 6T]` (extended by `g(t + T) = g(t) R`) winds once around the
origin. -/
def IsWindingOne (T : ℝ) (g : ℝ → Mat2) : Prop :=
  ∃ θ : ℝ → ℝ, ContinuousOn θ (Icc 0 T) ∧ θ 0 = 0 ∧ θ T = Real.pi / 3 ∧
    ∀ t ∈ Icc 0 T, ∃ r : ℝ, 0 < r ∧
      g t *ᵥ sixthRoot 0 = r • ![Real.cos (θ t), Real.sin (θ t)]

/-! ### Phases of plane curves on `[0, T]` -/

section Phase

/-- The primitive `t ↦ ∫₀ᵗ f` of a function continuous on `[0, T]` is continuous on `[0, T]`. -/
private lemma wn_primitive_continuousOn {f : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hf : ContinuousOn f (Icc 0 T)) :
    ContinuousOn (fun t ↦ ∫ s in (0 : ℝ)..t, f s) (Icc 0 T) := by
  have h := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := T)
    (f := f) (by rw [uIcc_of_le hT]; exact hf.integrableOn_Icc)
  rwa [uIcc_of_le hT] at h

/-- The primitive `t ↦ ∫₀ᵗ f` of a function continuous on `[0, T]` has derivative `f t` at every
interior point. -/
private lemma wn_primitive_hasDerivAt {f : ℝ → ℝ} {T t : ℝ} (hf : ContinuousOn f (Icc 0 T))
    (ht : t ∈ Ioo 0 T) : HasDerivAt (fun t ↦ ∫ s in (0 : ℝ)..t, f s) (f t) t :=
  intervalIntegral.integral_hasDerivAt_right
    ((hf.mono (Icc_subset_Icc le_rfl ht.2.le)).intervalIntegrable_of_Icc ht.1.le)
    ((hf.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo t ht)
    (hf.continuousAt (Icc_mem_nhds ht.1 ht.2))

/-- **Polar form on `[0, T]`.** A curve `z` in `ℂ \ {0}`, continuous on `[0, T]` with continuous
derivative `z'` on `(0, T)` and `z(0) = 1`, is `z(t) = exp(∫₀ᵗ Re(z'/z) + i ∫₀ᵗ Im(z'/z))`. -/
private lemma wn_polar {T : ℝ} {z z' : ℝ → ℂ} (hzc : ContinuousOn z (Icc 0 T))
    (hz'c : ContinuousOn z' (Icc 0 T)) (hd : ∀ t ∈ Ioo 0 T, HasDerivAt z (z' t) t)
    (hz0 : ∀ t ∈ Icc 0 T, z t ≠ 0) (h1 : z 0 = 1) {t : ℝ} (ht : t ∈ Icc 0 T) :
    z t = Complex.exp ((∫ s in (0 : ℝ)..t, (z' s / z s).re : ℝ) +
      (∫ s in (0 : ℝ)..t, (z' s / z s).im : ℝ) * Complex.I) := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hq : ContinuousOn (fun s ↦ z' s / z s) (Icc 0 T) := hz'c.div hzc hz0
  have hre : ContinuousOn (fun s ↦ (z' s / z s).re) (Icc 0 T) :=
    Complex.continuous_re.comp_continuousOn hq
  have him : ContinuousOn (fun s ↦ (z' s / z s).im) (Icc 0 T) :=
    Complex.continuous_im.comp_continuousOn hq
  set E : ℝ → ℂ := fun t ↦ ((∫ s in (0 : ℝ)..t, (z' s / z s).re : ℝ) : ℂ) +
      ((∫ s in (0 : ℝ)..t, (z' s / z s).im : ℝ) : ℂ) * Complex.I with hEdef
  have hEc : ContinuousOn E (Icc 0 T) :=
    (Complex.continuous_ofReal.comp_continuousOn (wn_primitive_continuousOn hT hre)).add
      ((Complex.continuous_ofReal.comp_continuousOn (wn_primitive_continuousOn hT him)).mul
        continuousOn_const)
  have hEd : ∀ x ∈ Ioo 0 T, HasDerivAt E (z' x / z x) x := by
    intro x hx
    have := (wn_primitive_hasDerivAt hre hx).ofReal_comp.add
      ((wn_primitive_hasDerivAt him hx).ofReal_comp.mul_const Complex.I)
    convert this using 1
    exact (Complex.re_add_im _).symm
  have hwc : ContinuousOn (fun s ↦ z s * Complex.exp (-E s)) (Icc 0 T) :=
    hzc.mul (Complex.continuous_exp.comp_continuousOn hEc.neg)
  have hwd : ∀ x ∈ Ioo 0 T, HasDerivAt (fun s ↦ z s * Complex.exp (-E s)) 0 x := by
    intro x hx
    have := (hd x hx).mul (hEd x hx).neg.cexp
    convert this using 1
    have := hz0 x (Ioo_subset_Icc_self hx)
    field_simp
    ring
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (f' := fun _ ↦ (0 : ℂ))
    ht.1 (hwc.mono (Icc_subset_Icc le_rfl ht.2)) (fun x hx ↦ hwd x ⟨hx.1, hx.2.trans_le ht.2⟩)
    intervalIntegrable_const
  have hE0 : E 0 = 0 := by simp [hEdef]
  simp only [intervalIntegral.integral_zero, hE0, neg_zero, Complex.exp_zero, mul_one, h1] at hint
  have hzt : z t * Complex.exp (-E t) = 1 := by linear_combination -hint
  calc z t = z t * Complex.exp (-E t) * Complex.exp (E t) := by
        rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    _ = Complex.exp (E t) := by rw [hzt, one_mul]

end Phase

/-! ### Angles -/

section Angle

/-- Two polar representations of the same vector with positive radii have angles differing by a
multiple of `2π`. -/
private lemma wn_exists_int {r s a b : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hc : r * Real.cos a = s * Real.cos b) (hsn : r * Real.sin a = s * Real.sin b) :
    ∃ n : ℤ, a - b = n * (2 * Real.pi) := by
  have ha := Real.sin_sq_add_cos_sq a
  have hb := Real.sin_sq_add_cos_sq b
  have hrs : r = s := by
    have h2 : r ^ 2 = s ^ 2 := by
      have e1 : r ^ 2 = (r * Real.cos a) ^ 2 + (r * Real.sin a) ^ 2 := by
        linear_combination (-r ^ 2) * ha
      have e2 : s ^ 2 = (s * Real.cos b) ^ 2 + (s * Real.sin b) ^ 2 := by
        linear_combination (-s ^ 2) * hb
      rw [e1, e2, hc, hsn]
    nlinarith
  subst hrs
  have hc' : Real.cos a = Real.cos b := mul_left_cancel₀ hr.ne' hc
  have hs' : Real.sin a = Real.sin b := mul_left_cancel₀ hr.ne' hsn
  have h1 : Real.cos (a - b) = 1 := by
    rw [Real.cos_sub, hc', hs']; linear_combination hb
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).1 h1
  exact ⟨n, hn.symm⟩

/-- A continuous function on `[0, T]` that vanishes at `0` and never takes the values `±π` stays
in `(-π, π)` (intermediate value theorem). -/
private lemma wn_abs_lt_pi {T : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 T)) (h0 : f 0 = 0)
    (hne : ∀ t ∈ Icc 0 T, f t ≠ Real.pi ∧ f t ≠ -Real.pi) {t : ℝ} (ht : t ∈ Icc 0 T) :
    |f t| < Real.pi := by
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  have hft := hf.mono hsub
  have hpi := Real.pi_pos
  rw [abs_lt]
  constructor
  · by_contra hle
    obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc' ht.1 hft ⟨not_lt.1 hle, by rw [h0]; linarith⟩
    exact (hne s (hsub hs)).2 hfs
  · by_contra hle
    obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc ht.1 hft ⟨by rw [h0]; linarith, not_lt.1 hle⟩
    exact (hne s (hsub hs)).1 hfs

/-- An integer multiple of `2π` in `(-π, π)` is `0`. -/
private lemma wn_int_eq_zero {n : ℤ} (h : |(n : ℝ) * (2 * Real.pi)| < Real.pi) : n = 0 := by
  have hpi := Real.pi_pos
  rw [abs_lt] at h
  have h1 : n < 1 := by
    by_contra hc
    have : (1 : ℝ) ≤ n := by exact_mod_cast not_lt.1 hc
    nlinarith
  have h2 : -1 < n := by
    by_contra hc
    have : (n : ℝ) ≤ -1 := by exact_mod_cast not_lt.1 hc
    nlinarith
  omega

/-- `A s₀* = (A₀₀, A₁₀)`. -/
private lemma wn_mulVec_sixthRoot (A : Mat2) : A *ᵥ sixthRoot 0 = ![A 0 0, A 1 0] := by
  ext i
  fin_cases i <;> simp [sixthRoot, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The polar form of `A s₀*`, coordinatewise. -/
private lemma wn_mulVec_sixthRoot_eq_iff (A : Mat2) (r a : ℝ) :
    A *ᵥ sixthRoot 0 = r • ![Real.cos a, Real.sin a] ↔
      A 0 0 = r * Real.cos a ∧ A 1 0 = r * Real.sin a := by
  rw [wn_mulVec_sixthRoot]
  constructor
  · intro h
    exact ⟨by simpa using congrFun h 0, by simpa using congrFun h 1⟩
  · rintro ⟨h0, h1⟩
    ext i
    fin_cases i <;> simp [h0, h1]

/-- The vectors `(A₀₀, A₁₀)` and `(A₁₁, A₁₀)` of a matrix of determinant one are never opposite:
their angles do not differ by `±π`. -/
private lemma wn_ne_pi {A : Mat2} (hA : A.det = 1) {θ ψ r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (h1 : A 0 0 = r * Real.cos θ) (h2 : A 1 0 = r * Real.sin θ) (h3 : A 1 1 = s * Real.cos ψ)
    (h4 : A 1 0 = s * Real.sin ψ) : θ - ψ ≠ Real.pi ∧ θ - ψ ≠ -Real.pi := by
  rw [Matrix.det_fin_two] at hA
  have key : ¬ (Real.cos θ = -Real.cos ψ ∧ Real.sin θ = -Real.sin ψ) := by
    rintro ⟨hc, hsn⟩
    have hsin : Real.sin ψ = 0 := by
      have : (r + s) * Real.sin ψ = 0 := by linear_combination h2 - h4 + r * hsn
      exact (mul_eq_zero.1 this).resolve_left (by linarith)
    have h10 : A 1 0 = 0 := by rw [h4, hsin, mul_zero]
    have hcos : Real.cos ψ ^ 2 = 1 := by nlinarith [Real.sin_sq_add_cos_sq ψ]
    rw [h10, h1, h3, hc] at hA
    nlinarith [mul_pos hr hs]
  constructor
  · intro h
    apply key
    rw [show θ = ψ + Real.pi by linarith, Real.cos_add_pi, Real.sin_add_pi]
    exact ⟨rfl, rfl⟩
  · intro h
    apply key
    rw [show θ = ψ - Real.pi by linarith, Real.cos_sub_pi, Real.sin_sub_pi]
    exact ⟨rfl, rfl⟩

/-- The vector `(A_ii, A₁₀)` as a complex number: the column `(A₀₀, A₁₀) = A s₀*` for `i = 0`,
the reversed bottom row `(A₁₁, A₁₀)` for `i = 1`. -/
private noncomputable def wn_vec (i : Fin 2) (A : Mat2) : ℂ :=
  (A i i : ℂ) + (A 1 0 : ℂ) * Complex.I

private lemma wn_vec_re (i : Fin 2) (A : Mat2) : (wn_vec i A).re = A i i := by simp [wn_vec]

private lemma wn_vec_im (i : Fin 2) (A : Mat2) : (wn_vec i A).im = A 1 0 := by simp [wn_vec]

private lemma wn_vec_continuous (i : Fin 2) : Continuous (wn_vec i) := by
  unfold wn_vec
  fun_prop

private lemma wn_vec_ne_zero {A : Mat2} (hA : A.det = 1) (i : Fin 2) : wn_vec i A ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  rw [wn_vec_re, Complex.zero_re] at hre
  rw [wn_vec_im, Complex.zero_im] at him
  rw [Matrix.det_fin_two, him] at hA
  fin_cases i
  · simp only [Fin.zero_eta] at hre
    rw [hre] at hA; simp at hA
  · simp only [Fin.mk_one] at hre
    rw [hre] at hA; simp at hA

private lemma wn_vec_hasDerivAt {g : ℝ → Mat2} {A : Mat2} {t : ℝ} (i : Fin 2)
    (hd : HasDerivAtEntrywise g A t) : HasDerivAt (fun s ↦ wn_vec i (g s)) (wn_vec i A) t :=
  (hd i i).ofReal_comp.add ((hd 1 0).ofReal_comp.mul_const Complex.I)

/-- `Im(z'/z)` for the column `z = A₀₀ + i A₁₀` and `z' = (AY)₀₀ + i (AY)₁₀`:
`Y₁₀ det A / |z|²`. -/
private lemma wn_col_im (A Y : Mat2) :
    (wn_vec 0 (A * Y) / wn_vec 0 A).im = Y 1 0 * A.det / Complex.normSq (wn_vec 0 A) := by
  rw [Complex.div_im, Matrix.det_fin_two, ← sub_div]
  simp only [wn_vec_re, wn_vec_im, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- **The pointwise bound.** For the reversed bottom row `z = A₁₁ + i A₁₀` and
`z' = (AY)₁₁ + i (AY)₁₀`, `Im(z'/z) ≤ Y₁₀ - Y₀₁ = -tr(JY)` when `Y` is a star state. -/
private lemma wn_row_im_le {A Y : Mat2} (hY : IsStarState Y) (hA : wn_vec 1 A ≠ 0) :
    (wn_vec 1 (A * Y) / wn_vec 1 A).im ≤ Y 1 0 - Y 0 1 := by
  obtain ⟨htr, hdet, h0, h1, -⟩ := hY
  rw [Matrix.trace_fin_two] at htr
  rw [Matrix.det_fin_two] at hdet
  have hc : 0 < Y 1 0 := by
    have e : Y 1 0 = (ρ₀ Y + ρ₁ Y) * √3 / 2 := by
      unfold ρ₀ ρ₁
      field_simp
      ring
    rw [e]
    have := add_pos h0 h1
    positivity
  have hN : 0 < Complex.normSq (wn_vec 1 A) := Complex.normSq_pos.2 hA
  rw [Complex.div_im, ← sub_div, div_le_iff₀ hN]
  rw [Complex.normSq_apply] at hN ⊢
  simp only [wn_vec_re, wn_vec_im, Matrix.mul_apply, Fin.sum_univ_two]
  have hd : Y 1 1 = -Y 0 0 := by linarith
  rw [hd]
  set a := Y 0 0
  set b := Y 0 1
  set c := Y 1 0
  set p := A 1 0
  set q := A 1 1
  have key : c * (c * p ^ 2 - 2 * a * p * q - b * q ^ 2) = (c * p - a * q) ^ 2 + q ^ 2 := by
    rw [hd] at hdet
    linear_combination q ^ 2 * hdet
  have hE : 0 ≤ c * p ^ 2 - 2 * a * p * q - b * q ^ 2 :=
    nonneg_of_mul_nonneg_right (by rw [key]; positivity) hc
  nlinarith

/-- `-tr(JY) = Y₁₀ - Y₀₁`. -/
private lemma wn_traceForm_J (Y : Mat2) : traceForm J Y = Y 0 1 - Y 1 0 := by
  rw [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two]
  simp [J]
  ring

/-- The phase `∫₀ᵗ Im(z'/z)` of the curve `z = g_ii + i g₁₀` (`z' = (gX)_ii + i (gX)₁₀`): the
continuous angle of `g s₀*` for `i = 0`, of the reversed bottom row `(g₁₁, g₁₀)` (the rotation
angle `ψ` of the Iwasawa decomposition) for `i = 1`. -/
private noncomputable def wn_angle (i : Fin 2) (g X : ℝ → Mat2) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, (wn_vec i (g s * X s) / wn_vec i (g s)).im

/-- The regularity of a state trajectory: `g`, `X` are continuous on `[0, T]` and `g' = gX` on
`(0, T)`. -/
private lemma wn_regular {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsStateTrajectory T u g X) :
    ContinuousOn g (Icc 0 T) ∧ ContinuousOn (fun t ↦ g t * X t) (Icc 0 T) ∧
      ∀ t ∈ Ioo 0 T, HasDerivAtEntrywise g (g t * X t) t := by
  obtain ⟨-, -, -, -, hg, hX⟩ := h
  have hgc : ContinuousOn g (Icc 0 T) := Matrix.continuousOn_of_eq_add_integral hg
  have hXc : ContinuousOn X (Icc 0 T) := Matrix.continuousOn_of_eq_add_integral hX
  have hvc : ContinuousOn (fun t ↦ g t * X t) (Icc 0 T) := hgc.mul hXc
  exact ⟨hgc, hvc, fun t ht ↦ Matrix.hasDerivAtEntrywise_of_eq_add_integral hg ht
    (hvc.continuousAt (Icc_mem_nhds ht.1 ht.2))⟩

/-- The integrand of `wn_angle` is continuous on `[0, T]`. -/
private lemma wn_integrand_continuousOn {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsStateTrajectory T u g X) (i : Fin 2) :
    ContinuousOn (fun s ↦ (wn_vec i (g s * X s) / wn_vec i (g s)).im) (Icc 0 T) := by
  obtain ⟨hgc, hvc, -⟩ := wn_regular h
  exact Complex.continuous_im.comp_continuousOn
    (((wn_vec_continuous i).comp_continuousOn hvc).div
      ((wn_vec_continuous i).comp_continuousOn hgc)
      fun t ht ↦ wn_vec_ne_zero (h.2.2.2.1 t ht).1 i)

private lemma wn_angle_continuousOn {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsStateTrajectory T u g X) (i : Fin 2) : ContinuousOn (wn_angle i g X) (Icc 0 T) :=
  wn_primitive_continuousOn h.1.le (wn_integrand_continuousOn h i)

private lemma wn_angle_zero (i : Fin 2) (g X : ℝ → Mat2) : wn_angle i g X 0 = 0 := by
  simp [wn_angle]

/-- `(g_ii, g₁₀) = r (cos φ, sin φ)` with `r > 0` and the phase `φ = wn_angle i g X`. -/
private lemma wn_angle_polar {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsStateTrajectory T u g X) (hg0 : g 0 = 1) (i : Fin 2) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∃ r : ℝ, 0 < r ∧ g t i i = r * Real.cos (wn_angle i g X t) ∧
      g t 1 0 = r * Real.sin (wn_angle i g X t) := by
  obtain ⟨hgc, hvc, hd⟩ := wn_regular h
  have hz := wn_polar (z := fun s ↦ wn_vec i (g s)) (z' := fun s ↦ wn_vec i (g s * X s))
    ((wn_vec_continuous i).comp_continuousOn hgc) ((wn_vec_continuous i).comp_continuousOn hvc)
    (fun s hs ↦ wn_vec_hasDerivAt i (hd s hs)) (fun s hs ↦ wn_vec_ne_zero (h.2.2.2.1 s hs).1 i)
    (by simp [wn_vec, hg0]) ht
  refine ⟨Real.exp (∫ s in (0 : ℝ)..t, (wn_vec i (g s * X s) / wn_vec i (g s)).re),
    Real.exp_pos _, ?_, ?_⟩
  · have := congrArg Complex.re hz
    rw [wn_vec_re, Complex.exp_re] at this
    simpa [wn_angle] using this
  · have := congrArg Complex.im hz
    rw [wn_vec_im, Complex.exp_im] at this
    simpa [wn_angle] using this

end Angle

/-- Along an admissible trajectory, `σ₀ = g s₀*` turns counterclockwise about the origin, and its
continuous angle `θ` with `θ(0) = 0` ends at `θ(T) = π/3 + 2πm` for some `m ∈ ℕ`. -/
theorem exists_angle_of_isReinhardtAdmissible {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsReinhardtAdmissible T u g X) :
    ∃ θ : ℝ → ℝ, ContinuousOn θ (Icc 0 T) ∧ θ 0 = 0 ∧ StrictMonoOn θ (Icc 0 T) ∧
      (∃ m : ℕ, θ T = Real.pi / 3 + 2 * Real.pi * m) ∧
      ∀ t ∈ Icc 0 T, ∃ r : ℝ, 0 < r ∧
        g t *ᵥ sixthRoot 0 = r • ![Real.cos (θ t), Real.sin (θ t)] := by
  obtain ⟨hst, hg0, hgT, -⟩ := h
  have hT := hst.1
  have hTmem : T ∈ Icc 0 T := ⟨hT.le, le_rfl⟩
  have hdet := hst.2.2.2.1
  have hc := wn_integrand_continuousOn hst 0
  -- the angle is strictly increasing: `θ' = X₁₀ det g / |z|² > 0`
  have hmono : StrictMonoOn (wn_angle 0 g X) (Icc 0 T) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 T) (wn_angle_continuousOn hst 0) ?_
    intro x hx
    rw [interior_Icc] at hx
    have hD : HasDerivAt (wn_angle 0 g X) _ x := wn_primitive_hasDerivAt hc hx
    rw [hD.deriv]
    have hxI := Ioo_subset_Icc_self hx
    obtain ⟨hdx, hXx⟩ := hdet x hxI
    rw [wn_col_im, hdx, mul_one]
    have hc10 : 0 < X x 1 0 := by
      obtain ⟨-, -, h0, h1, -⟩ := hXx
      have e : X x 1 0 = (ρ₀ (X x) + ρ₁ (X x)) * √3 / 2 := by
        unfold ρ₀ ρ₁
        field_simp
        ring
      rw [e]
      have := add_pos h0 h1
      positivity
    exact div_pos hc10 (Complex.normSq_pos.2 (wn_vec_ne_zero hdx 0))
  refine ⟨wn_angle 0 g X, wn_angle_continuousOn hst 0, wn_angle_zero 0 g X, hmono, ?_, ?_⟩
  · obtain ⟨r, hr, h1, h2⟩ := wn_angle_polar hst hg0 0 hTmem
    rw [hgT] at h1 h2
    obtain ⟨n, hn⟩ := wn_exists_int (b := Real.pi / 3) hr one_pos
      (by rw [← h1, Real.cos_pi_div_three]; simp [R])
      (by rw [← h2, Real.sin_pi_div_three]; simp [R])
    have hpos : 0 < wn_angle 0 g X T := by
      have := hmono ⟨le_rfl, hT.le⟩ hTmem hT
      rwa [wn_angle_zero] at this
    have hn0 : 0 ≤ n := by
      by_contra hneg
      have : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt (not_le.1 hneg)
      have hpi := Real.pi_pos
      nlinarith
    lift n to ℕ using hn0
    refine ⟨n, ?_⟩
    push_cast at hn
    linarith
  · intro t ht
    obtain ⟨r, hr, h1, h2⟩ := wn_angle_polar hst hg0 0 ht
    exact ⟨r, hr, (wn_mulVec_sixthRoot_eq_iff _ _ _).2 ⟨h1, h2⟩⟩

/-- **Higher winding costs more.** For an admissible trajectory and the continuous angle `θ` of
`g(t) s₀*` with `θ(0) = 0`, the cost is at least `(3/2) θ(T)`; with `θ(T) = π/3 + 2πm`, at least
`π/2 + 3πm`. (Not in the book; see the module docstring for the proof.) -/
theorem three_halves_mul_angle_le_reinhardtCost {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsReinhardtAdmissible T u g X) {θ : ℝ → ℝ} (hθc : ContinuousOn θ (Icc 0 T))
    (hθ0 : θ 0 = 0)
    (hθ : ∀ t ∈ Icc 0 T, ∃ r : ℝ, 0 < r ∧
      g t *ᵥ sixthRoot 0 = r • ![Real.cos (θ t), Real.sin (θ t)]) :
    3 / 2 * θ T ≤ reinhardtCost T X := by
  obtain ⟨hst, hg0, hgT, -⟩ := h
  have hT := hst.1
  have hTmem : T ∈ Icc 0 T := ⟨hT.le, le_rfl⟩
  have hdet := hst.2.2.2.1
  set ψ := wn_angle 1 g X with hψ
  -- `θ - ψ` stays in `(-π, π)`
  have hlt : ∀ t ∈ Icc 0 T, |θ t - ψ t| < Real.pi := by
    refine fun t ht ↦ wn_abs_lt_pi (f := fun t ↦ θ t - ψ t)
      (hθc.sub (wn_angle_continuousOn hst 1))
      (by simp only [hθ0, hψ, wn_angle_zero, sub_zero]) (fun s hs ↦ ?_) ht
    obtain ⟨r, hr, hrθ⟩ := hθ s hs
    obtain ⟨h1, h2⟩ := (wn_mulVec_sixthRoot_eq_iff _ _ _).1 hrθ
    obtain ⟨r', hr', h3, h4⟩ := wn_angle_polar hst hg0 1 hs
    exact wn_ne_pi (hdet s hs).1 hr hr' h1 h2 h3 h4
  -- at `T` the two vectors coincide, so `θ(T) = ψ(T)`
  have hθψ : θ T = ψ T := by
    obtain ⟨r, hr, hrθ⟩ := hθ T hTmem
    obtain ⟨h1, h2⟩ := (wn_mulVec_sixthRoot_eq_iff _ _ _).1 hrθ
    obtain ⟨r', hr', h3, h4⟩ := wn_angle_polar hst hg0 1 hTmem
    rw [hgT] at h1 h2 h3 h4
    obtain ⟨n, hn⟩ := wn_exists_int hr hr'
      (by rw [← h1, ← h3]; simp [R]) (by rw [← h2, ← h4])
    have := hlt T hTmem
    rw [hn] at this
    rw [wn_int_eq_zero this, Int.cast_zero, zero_mul, sub_eq_zero] at hn
    exact hn
  -- `ψ' ≤ κ` integrated
  have hle : ψ T ≤ ∫ t in (0 : ℝ)..T, (X t 1 0 - X t 0 1) := by
    have hXc : ContinuousOn X (Icc 0 T) := Matrix.continuousOn_of_eq_add_integral hst.2.2.2.2.2
    have hκc : ContinuousOn (fun t ↦ X t 1 0 - X t 0 1) (Icc 0 T) :=
      ((continuousOn_iff_entrywise.1 hXc) 1 0).sub ((continuousOn_iff_entrywise.1 hXc) 0 1)
    refine intervalIntegral.integral_mono_on hT.le
      ((wn_integrand_continuousOn hst 1).intervalIntegrable_of_Icc hT.le)
      (hκc.intervalIntegrable_of_Icc hT.le) fun t ht ↦ ?_
    exact wn_row_im_le (hdet t ht).2 (wn_vec_ne_zero (hdet t ht).1 1)
  have hcost : reinhardtCost T X = 3 / 2 * ∫ t in (0 : ℝ)..T, (X t 1 0 - X t 0 1) := by
    rw [reinhardtCost, ← neg_neg (∫ t in (0 : ℝ)..T, (X t 1 0 - X t 0 1)),
      ← intervalIntegral.integral_neg]
    simp only [wn_traceForm_J, neg_sub]
    ring
  rw [hcost, hθψ]
  linarith

/-- An admissible trajectory of cost less than `7π/2` has winding number one. -/
theorem isWindingOne_of_reinhardtCost_lt {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsReinhardtAdmissible T u g X) (hc : reinhardtCost T X < 7 * Real.pi / 2) :
    IsWindingOne T g := by
  obtain ⟨θ, hθc, hθ0, -, ⟨m, hm⟩, hθ⟩ := exists_angle_of_isReinhardtAdmissible h
  have hb := three_halves_mul_angle_le_reinhardtCost h hθc hθ0 hθ
  have hm0 : m = 0 := by
    by_contra hne
    have h1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hne
    have hpi := Real.pi_pos
    rw [hm] at hb
    nlinarith
  subst hm0
  refine ⟨θ, hθc, hθ0, by simpa using hm, hθ⟩

/-! ### The seven-fold circle -/

section Circle

/-- The rotation `exp(tJ)` by the angle `t`. -/
private noncomputable def wn_rot (t : ℝ) : Mat2 :=
  !![Real.cos t, -Real.sin t; Real.sin t, Real.cos t]

private lemma wn_rot_mul_J (t : ℝ) : wn_rot t * J = !![-Real.sin t, -Real.cos t; Real.cos t,
    -Real.sin t] := by
  simp [wn_rot, J]

private lemma wn_rot_isIntegralCurve (T : ℝ) :
    IsIntegralCurve wn_rot (fun t ↦ wn_rot t * (fun _ ↦ J) t) T := by
  intro i j
  simp only [wn_rot_mul_J]
  fin_cases i <;> fin_cases j <;>
    refine ⟨Continuous.intervalIntegrable (by
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, of_apply, cons_val', cons_val_zero,
        cons_val_one, cons_val_fin_one]
      fun_prop) _ _, fun t _ ↦ ?_⟩ <;>
    simp [wn_rot, intervalIntegral.integral_neg, integral_sin, integral_cos]

private lemma wn_isStarState_J : IsStarState J := by
  refine ⟨by simp [J, Matrix.trace_fin_two], by simp [J, Matrix.det_fin_two], ?_, ?_, ?_⟩ <;>
    simp [ρ₀, ρ₁, ρ₂, J]

/-- The rotation by `2π` is the identity. -/
private lemma wn_rot_two_pi : wn_rot (2 * Real.pi) = wn_rot 0 := by
  simp [wn_rot]

end Circle

/-- **Admissible trajectories of higher winding exist** (REPORT.md,
E15). The unit circle traversed seven times, `X ≡ J`,
`u ≡ (1/3, 1/3, 1/3)`, `g(t) = exp(tJ)` on `[0, 7π/3]`, is admissible for Problem 3.6.2, does not
have winding number one, costs `7π`, and is not the boundary trajectory of any balanced pair with
period parameter `t_f = 7π/3` and `σ_j = g s_j*` on `[0, t_f]`: so the converse of Problem 3.6.2
(E15) fails for it. -/
theorem exists_isReinhardtAdmissible_not_isWindingOne :
    ∃ (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X : ℝ → Mat2), IsReinhardtAdmissible T u g X ∧
      ¬ IsWindingOne T g ∧ reinhardtCost T X = 7 * Real.pi ∧
      ¬ ∃ (K : Set (Fin 2 → ℝ)) (σ : ZMod 6 → ℝ → Fin 2 → ℝ), IsBalancedPair K σ T ∧
        ∀ j, ∀ t ∈ Icc 0 T, σ j t = g t *ᵥ sixthRoot j := by
  have hpi := Real.pi_pos
  have hZ : controlMatrix (fun _ ↦ 1 / 3) = (1 / 3 : ℝ) • J := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [controlMatrix, J]
  have hP : controlP (fun _ ↦ 1 / 3) J * J - J * controlP (fun _ ↦ 1 / 3) J = 0 := by
    simp only [controlP, hZ, smul_smul, smul_mul_assoc, mul_smul_comm, sub_self]
  refine ⟨7 * Real.pi / 3, fun _ _ ↦ 1 / 3, wn_rot, fun _ ↦ J, ⟨⟨by positivity,
    measurable_const, fun _ _ ↦ ⟨fun _ ↦ ⟨by norm_num, by norm_num⟩, by norm_num⟩,
    fun t _ ↦ ⟨?_, wn_isStarState_J⟩, wn_rot_isIntegralCurve _, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · -- `det g = 1`
    simp only [wn_rot, Matrix.det_fin_two_of]
    nlinarith [Real.sin_sq_add_cos_sq t]
  · -- `X ≡ J` is constant: `[P, J] = 0`
    intro i j
    simp only [hP, Matrix.zero_apply, intervalIntegral.integral_zero, add_zero]
    exact ⟨intervalIntegrable_const, fun _ _ ↦ by simp⟩
  · -- `g(0) = I`
    ext i j
    fin_cases i <;> fin_cases j <;> simp [wn_rot]
  · -- `g(7π/3) = R`
    have e : 7 * Real.pi / 3 = Real.pi / 3 + 2 * Real.pi := by ring
    simp only [wn_rot, e, Real.cos_add_two_pi, Real.sin_add_two_pi, Real.cos_pi_div_three,
      Real.sin_pi_div_three, R]
  · -- `X(t_f) = R⁻¹ X(0) R`
    exact R_inv_mul_J_mul_R.symm
  · -- not of winding number one
    rintro ⟨θ, hθc, hθ0, hθT, hθ⟩
    have hTmem : 7 * Real.pi / 3 ∈ Icc 0 (7 * Real.pi / 3) := ⟨by positivity, le_rfl⟩
    -- `θ(t) - t ∈ 2πℤ`, so it stays at `0`
    have hint : ∀ t ∈ Icc 0 (7 * Real.pi / 3), ∃ n : ℤ, θ t - t = n * (2 * Real.pi) := by
      intro t ht
      obtain ⟨r, hr, hrθ⟩ := hθ t ht
      obtain ⟨h1, h2⟩ := (wn_mulVec_sixthRoot_eq_iff _ _ _).1 hrθ
      exact wn_exists_int hr one_pos (by rw [← h1]; simp [wn_rot]) (by rw [← h2]; simp [wn_rot])
    have hlt := wn_abs_lt_pi (f := fun t ↦ θ t - t) (hθc.sub continuousOn_id)
      (by simp [hθ0]) (fun t ht ↦ ?_) hTmem
    · simp only [hθT] at hlt
      rw [show Real.pi / 3 - 7 * Real.pi / 3 = -(2 * Real.pi) by ring, abs_neg,
        abs_of_pos (by positivity)] at hlt
      linarith
    · obtain ⟨n, hn⟩ := hint t ht
      simp only [hn]
      constructor
      · intro h
        have : (n : ℝ) * 2 = 1 := by nlinarith
        have : n * 2 = 1 := by exact_mod_cast this
        omega
      · intro h
        have : (n : ℝ) * 2 = -1 := by nlinarith
        have : n * 2 = -1 := by exact_mod_cast this
        omega
  · -- the cost is `7π`
    have hJJ : traceForm J J = -2 := by rw [wn_traceForm_J]; simp [J]; norm_num
    simp only [reinhardtCost, hJJ, intervalIntegral.integral_const, smul_eq_mul]
    ring
  · -- `σ₀(0) = σ₀(2π)`, so `σ₀` is not injective on `[0, 6 t_f)`
    rintro ⟨K, σ, hK, hσ⟩
    obtain ⟨-, -, -, -, -, -, -, -, hinj, -⟩ := hK
    have h0 : (0 : ℝ) ∈ Icc 0 (7 * Real.pi / 3) := ⟨le_rfl, by positivity⟩
    have h2 : 2 * Real.pi ∈ Icc 0 (7 * Real.pi / 3) := ⟨by positivity, by linarith⟩
    have heq : σ 0 0 = σ 0 (2 * Real.pi) := by
      rw [hσ 0 0 h0, hσ 0 _ h2, wn_rot_two_pi]
    have := hinj 0 ⟨le_rfl, by positivity⟩ ⟨by positivity, by linarith⟩ heq
    linarith

end SmoothedPolygons
