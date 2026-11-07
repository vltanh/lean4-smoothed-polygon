module

public import SmoothedPolygons.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Topology.Covering.AddCircle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import Basic.Analysis.Calculus.MatrixFTC

/-!
# The Iwasawa chart: the universal cover of `SL₂(ℝ)` in coordinates

To apply the maximum principle (proved on open subsets of a vector space, `External.Pontryagin`)
to the Reinhardt problem, the state space `SL₂(ℝ) × 𝔥*` is covered by one chart: the Iwasawa
coordinates `π(s, r, θ) = n_s a_r k_θ`, with `n_s = [[1, s], [0, 1]]`,
`a_r = diag(e^r, e^{-r})` and `k_θ = exp(θJ)` the rotation by `θ` (`iwasawa`). The map
`π : ℝ³ → SL₂(ℝ)` is smooth, onto (the Iwasawa decomposition, proved in
`SmoothedPolygons/Ch4/AdjointOrbit.lean` as the private `orb_iwasawa`), and identifies points
exactly when `s, r` agree and the angles differ by a multiple of `2π`; it is the universal
covering. Continuous curves in `SL₂(ℝ)` lift through `π` (path lifting through `ℝ → S¹` in the
angle; `s, r` are explicit), uniquely given the initial point.

The left-invariant field `g ↦ gX` lifts to `iwasawaField p X`: with `W = k_θ X k_θ⁻¹`,
`s' = e^{2r}(W₀₁ + W₁₀)`, `r' = W₀₀`, `θ' = W₁₀` (from `g⁻¹g' = k⁻¹(s'e^{-2r}E + r'H)k + θ'J`).
So a curve `g` with `g' = gX` lifts to a solution of `p' = iwasawaField p X`, and conversely
(`isIntegralCurve_lift`, `isIntegralCurve_iwasawa`).

This chart is the formalization's device (reading of the book's "smooth manifold `M`", §6.2,
TeX 4670; departure D1 of the Layer 1 plan); the book applies the PMP on `SL₂(ℝ) × 𝔰𝔩₂(ℝ)`
directly. Inventory §3.4 (`notes/plan_ch5_8_16/inventory.md`) explains why neither
`SL₂(ℝ) × 𝔰𝔩₂(ℝ)` nor `Mat₂ × 𝔥*` can be used as the state space (spurious multipliers, E21).
-/

@[expose] public section

namespace SmoothedPolygons

open Set MeasureTheory
open scoped ContDiff Topology

/-- The rotation `k_θ = exp(θJ) = [[cos θ, -sin θ], [sin θ, cos θ]]`. -/
noncomputable def iwasawaK (θ : ℝ) : Mat2 :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

/-- The Iwasawa chart `π(s, r, θ) = n_s a_r k_θ` of `SL₂(ℝ)`, with `n_s = [[1, s], [0, 1]]`,
`a_r = diag(e^r, e^{-r})` and `k_θ` the rotation by `θ`; the point is `p = (s, r, θ)`. -/
noncomputable def iwasawa (p : ℝ × ℝ × ℝ) : Mat2 :=
  !![1, p.1; 0, 1] * !![Real.exp p.2.1, 0; 0, Real.exp (-p.2.1)] * iwasawaK p.2.2

/-- The lift of the left-invariant field `g ↦ gX` through the Iwasawa chart: with
`W = k_θ X k_θ⁻¹`, `(s', r', θ') = (e^{2r}(W₀₁ + W₁₀), W₀₀, W₁₀)`. -/
noncomputable def iwasawaField (p : ℝ × ℝ × ℝ) (X : Mat2) : ℝ × ℝ × ℝ :=
  (Real.exp (2 * p.2.1) * ((iwasawaK p.2.2 * X * iwasawaK (-p.2.2)) 0 1 +
      (iwasawaK p.2.2 * X * iwasawaK (-p.2.2)) 1 0),
    (iwasawaK p.2.2 * X * iwasawaK (-p.2.2)) 0 0, (iwasawaK p.2.2 * X * iwasawaK (-p.2.2)) 1 0)

/-- `π(0) = I`. -/
theorem iwasawa_zero : iwasawa 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [iwasawa, iwasawaK, Matrix.mul_apply, Fin.sum_univ_two]

/-- `π` takes its values in `SL₂(ℝ)`. -/
theorem det_iwasawa (p : ℝ × ℝ × ℝ) : (iwasawa p).det = 1 := by
  rw [iwasawa, Matrix.det_mul, Matrix.det_mul]
  simp [iwasawaK, Matrix.det_fin_two, ← Real.exp_add, ← sq, Real.cos_sq_add_sin_sq]

/-- The entries of `π(s, r, θ) = n_s a_r k_θ`:
`[[e^r cos θ + s e^{-r} sin θ, -e^r sin θ + s e^{-r} cos θ], [e^{-r} sin θ, e^{-r} cos θ]]`. -/
theorem iw_iwasawa_eq (p : ℝ × ℝ × ℝ) : iwasawa p =
    !![Real.exp p.2.1 * Real.cos p.2.2 + p.1 * Real.exp (-p.2.1) * Real.sin p.2.2,
      -(Real.exp p.2.1 * Real.sin p.2.2) + p.1 * Real.exp (-p.2.1) * Real.cos p.2.2;
      Real.exp (-p.2.1) * Real.sin p.2.2, Real.exp (-p.2.1) * Real.cos p.2.2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [iwasawa, iwasawaK, Matrix.mul_apply, Fin.sum_univ_two]

/-- The entries of `π` are smooth. -/
theorem contDiff_iwasawa (i j : Fin 2) : ContDiff ℝ ∞ (fun p ↦ iwasawa p i j) := by
  simp only [iw_iwasawa_eq]
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] <;> fun_prop

/-- The second row `(c, d)` of a matrix of determinant one is not zero. -/
private lemma iw_row_pos {g : Mat2} (hg : g.det = 1) : 0 < g 1 0 ^ 2 + g 1 1 ^ 2 := by
  rw [Matrix.det_fin_two] at hg
  by_contra h
  have hc : g 1 0 = 0 := by nlinarith
  have hd : g 1 1 = 0 := by nlinarith
  simp [hc, hd] at hg

/-- The Iwasawa coordinates of `g = [[a, b], [c, d]] ∈ SL₂(ℝ)`, given the angle `θ` of
`(d, c)`: `s = (ac + bd)/(c² + d²)`, `e^{-r} = √(c² + d²)` (the computation of `orb_iwasawa`,
`SmoothedPolygons/Ch4/AdjointOrbit.lean`, with `k_θ` for `[[p, -q], [q, p]]`). -/
private lemma iw_iwasawa_of_cos_sin {g : Mat2} (hg : g.det = 1) {θ : ℝ}
    (hc : Real.cos θ = g 1 1 / √(g 1 0 ^ 2 + g 1 1 ^ 2))
    (hs : Real.sin θ = g 1 0 / √(g 1 0 ^ 2 + g 1 1 ^ 2)) :
    iwasawa ((g 0 0 * g 1 0 + g 0 1 * g 1 1) / (g 1 0 ^ 2 + g 1 1 ^ 2),
      -Real.log √(g 1 0 ^ 2 + g 1 1 ^ 2), θ) = g := by
  have hn := iw_row_pos hg
  rw [Matrix.det_fin_two] at hg
  set a := g 0 0
  set b := g 0 1
  set c := g 1 0
  set d := g 1 1
  have hρ : 0 < √(c ^ 2 + d ^ 2) := Real.sqrt_pos.2 hn
  have hρ2 : √(c ^ 2 + d ^ 2) ^ 2 = c ^ 2 + d ^ 2 := Real.sq_sqrt hn.le
  have e1 : Real.exp (-(-Real.log √(c ^ 2 + d ^ 2))) = √(c ^ 2 + d ^ 2) := by
    rw [neg_neg, Real.exp_log hρ]
  have e2 : Real.exp (-Real.log √(c ^ 2 + d ^ 2)) = (√(c ^ 2 + d ^ 2))⁻¹ := by
    rw [Real.exp_neg, Real.exp_log hρ]
  rw [iw_iwasawa_eq]
  simp only [e1, e2, hc, hs]
  generalize √(c ^ 2 + d ^ 2) = ρ at hρ hρ2
  ext i j; fin_cases i <;> fin_cases j
  · simp; field_simp; rw [hρ2]; linear_combination (-d * (c ^ 2 + d ^ 2)) * hg
  · simp; field_simp; rw [hρ2]; linear_combination (c * (c ^ 2 + d ^ 2)) * hg
  · simp; field_simp; rfl
  · simp; field_simp; rfl

/-- The Iwasawa decomposition: `π` is onto `SL₂(ℝ)` (from `orb_iwasawa`,
`SmoothedPolygons/Ch4/AdjointOrbit.lean`).

That lemma is private to its file; its computation is repeated here (`iw_iwasawa_of_cos_sin`),
with the angle of `k_θ` the argument of `d + ic`. -/
theorem iwasawa_surjective (g : Mat2) (hg : g.det = 1) : ∃ p, iwasawa p = g := by
  have hn := iw_row_pos hg
  have hz : (⟨g 1 1, g 1 0⟩ : ℂ) ≠ 0 := by
    intro h
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp only [Complex.zero_re, Complex.zero_im] at h1 h2
    rw [h1, h2] at hn; simp at hn
  have hnorm : ‖(⟨g 1 1, g 1 0⟩ : ℂ)‖ = √(g 1 0 ^ 2 + g 1 1 ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_mk]; ring_nf
  refine ⟨_, iw_iwasawa_of_cos_sin hg (θ := Complex.arg ⟨g 1 1, g 1 0⟩) ?_ ?_⟩
  · rw [Complex.cos_arg hz, hnorm]
  · rw [Complex.sin_arg, hnorm]

/-- The fibres of `π`: `π(p) = π(p')` if and only if `s, r` agree and the angles differ by a
multiple of `2π` (so `π` is the universal covering of `SL₂(ℝ)`). -/
theorem iwasawa_eq_iwasawa_iff (p p' : ℝ × ℝ × ℝ) :
    iwasawa p = iwasawa p' ↔
      p.1 = p'.1 ∧ p.2.1 = p'.2.1 ∧ ∃ n : ℤ, p'.2.2 = p.2.2 + 2 * Real.pi * n := by
  obtain ⟨s, r, θ⟩ := p
  obtain ⟨s', r', θ'⟩ := p'
  simp only
  constructor
  · intro h
    rw [iw_iwasawa_eq, iw_iwasawa_eq] at h
    have h00 := congrFun (congrFun h 0) 0
    have h01 := congrFun (congrFun h 0) 1
    have h10 := congrFun (congrFun h 1) 0
    have h11 := congrFun (congrFun h 1) 1
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one] at h00 h01 h10 h11
    have hcs := Real.cos_sq_add_sin_sq θ
    have hcs' := Real.cos_sq_add_sin_sq θ'
    -- `e^{-2r} = c² + d² = e^{-2r'}`
    have hsq : Real.exp (-r) ^ 2 = Real.exp (-r') ^ 2 := by
      linear_combination (Real.exp (-r) * Real.cos θ + Real.exp (-r') * Real.cos θ') * h11 +
        (Real.exp (-r) * Real.sin θ + Real.exp (-r') * Real.sin θ') * h10 -
        Real.exp (-r) ^ 2 * hcs + Real.exp (-r') ^ 2 * hcs'
    have hE : Real.exp (-r) = Real.exp (-r') :=
      (pow_left_inj₀ (Real.exp_pos _).le (Real.exp_pos _).le two_ne_zero).1 hsq
    have hr : r = r' := by simpa using hE
    subst hr
    have hE0 := (Real.exp_pos (-r)).ne'
    have hc : Real.cos θ = Real.cos θ' := mul_left_cancel₀ hE0 h11
    have hs : Real.sin θ = Real.sin θ' := mul_left_cancel₀ hE0 h10
    rw [hc, hs] at h00 h01
    have hss : (s - s') * Real.exp (-r) = 0 := by
      linear_combination Real.sin θ' * h00 + Real.cos θ' * h01 -
        (s - s') * Real.exp (-r) * hcs'
    refine ⟨by linarith [(mul_eq_zero.1 hss).resolve_right hE0], rfl, ?_⟩
    obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 (Real.Angle.cos_sin_inj hc hs).symm
    exact ⟨k, by linarith⟩
  · rintro ⟨rfl, rfl, n, rfl⟩
    have hc : Real.cos (θ + 2 * Real.pi * n) = Real.cos θ := by
      rw [show θ + 2 * Real.pi * n = θ + n * (2 * Real.pi) by ring, Real.cos_add_int_mul_two_pi]
    have hs : Real.sin (θ + 2 * Real.pi * n) = Real.sin θ := by
      rw [show θ + 2 * Real.pi * n = θ + n * (2 * Real.pi) by ring, Real.sin_add_int_mul_two_pi]
    rw [iw_iwasawa_eq, iw_iwasawa_eq]
    simp only [hc, hs]

/-- The derivative of `π` at `p` in the direction `v = (v₁, v₂, v₃)`, entry by entry (the
derivative of the entries of `iw_iwasawa_eq`). -/
private noncomputable def iw_dπ (p v : ℝ × ℝ × ℝ) : Mat2 :=
  !![v.2.1 * Real.exp p.2.1 * Real.cos p.2.2 - v.2.2 * Real.exp p.2.1 * Real.sin p.2.2 +
      v.1 * Real.exp (-p.2.1) * Real.sin p.2.2 +
      p.1 * (-(v.2.1 * Real.exp (-p.2.1) * Real.sin p.2.2) +
        v.2.2 * Real.exp (-p.2.1) * Real.cos p.2.2),
    -(v.2.1 * Real.exp p.2.1 * Real.sin p.2.2 + v.2.2 * Real.exp p.2.1 * Real.cos p.2.2) +
      v.1 * Real.exp (-p.2.1) * Real.cos p.2.2 +
      p.1 * (-(v.2.1 * Real.exp (-p.2.1) * Real.cos p.2.2) -
        v.2.2 * Real.exp (-p.2.1) * Real.sin p.2.2);
    -(v.2.1 * Real.exp (-p.2.1) * Real.sin p.2.2) + v.2.2 * Real.exp (-p.2.1) * Real.cos p.2.2,
    -(v.2.1 * Real.exp (-p.2.1) * Real.cos p.2.2) - v.2.2 * Real.exp (-p.2.1) * Real.sin p.2.2]

/-- The derivative of `π` along the line `t ↦ p + t v` at `t = 0`. -/
private lemma iw_hasDerivAt_line (p v : ℝ × ℝ × ℝ) (i j : Fin 2) :
    HasDerivAt (fun t : ℝ ↦ iwasawa (p + t • v) i j) (iw_dπ p v i j) 0 := by
  obtain ⟨s, r, θ⟩ := p
  obtain ⟨v₁, v₂, v₃⟩ := v
  have hl : ∀ x w : ℝ, HasDerivAt (fun t : ℝ ↦ x + t * w) w 0 := fun x w ↦ by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const w).const_add x
  have hE := (hl r v₂).exp
  have hEi := (hl r v₂).neg.exp
  have hC := (hl θ v₃).cos
  have hS := (hl θ v₃).sin
  have hs := hl s v₁
  have e : ∀ t : ℝ, iwasawa ((s, r, θ) + t • (v₁, v₂, v₃)) =
      !![Real.exp (r + t * v₂) * Real.cos (θ + t * v₃) +
          (s + t * v₁) * Real.exp (-(r + t * v₂)) * Real.sin (θ + t * v₃),
        -(Real.exp (r + t * v₂) * Real.sin (θ + t * v₃)) +
          (s + t * v₁) * Real.exp (-(r + t * v₂)) * Real.cos (θ + t * v₃);
        Real.exp (-(r + t * v₂)) * Real.sin (θ + t * v₃),
        Real.exp (-(r + t * v₂)) * Real.cos (θ + t * v₃)] := fun t ↦ by
    rw [iw_iwasawa_eq]; simp
  simp only [e]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue]
  · refine ((hE.fun_mul hC).fun_add ((hs.fun_mul hEi).fun_mul hS)).congr_deriv ?_
    simp [iw_dπ]; ring
  · refine ((hE.fun_mul hS).fun_neg.fun_add ((hs.fun_mul hEi).fun_mul hC)).congr_deriv ?_
    simp [iw_dπ]; ring
  · refine (hEi.fun_mul hS).congr_deriv ?_
    simp [iw_dπ]; ring
  · refine (hEi.fun_mul hC).congr_deriv ?_
    simp [iw_dπ]; ring

/-- The derivative of the entries of `π` in a direction `v`. -/
private lemma iw_fderiv_iwasawa (p v : ℝ × ℝ × ℝ) (i j : Fin 2) :
    fderiv ℝ (fun p ↦ iwasawa p i j) p v = iw_dπ p v i j := by
  have hd : DifferentiableAt ℝ (fun p ↦ iwasawa p i j) p :=
    ((contDiff_iwasawa i j).differentiable (by simp)).differentiableAt
  have hline : HasDerivAt (fun t : ℝ ↦ p + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p
  have h := hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  exact h.unique (iw_hasDerivAt_line p v i j)

/-- The lifted field represents the left-invariant field: for traceless `X`,
`Dπ(p)(iwasawaField p X) = π(p) X`, entry by entry. -/
theorem fderiv_iwasawa_iwasawaField (p : ℝ × ℝ × ℝ) {X : Mat2} (hX : X.trace = 0) (i j : Fin 2) :
    fderiv ℝ (fun p ↦ iwasawa p i j) p (iwasawaField p X) = (iwasawa p * X) i j := by
  rw [iw_fderiv_iwasawa]
  obtain ⟨s, r, θ⟩ := p
  have hcs := Real.cos_sq_add_sin_sq θ
  have hEE : Real.exp r * Real.exp (-r) = 1 := by rw [← Real.exp_add]; simp
  have hE2 : Real.exp (2 * r) = Real.exp r ^ 2 := by rw [sq, ← Real.exp_add]; ring_nf
  have htr : X 0 0 + X 1 1 = 0 := by rwa [Matrix.trace_fin_two] at hX
  fin_cases i <;> fin_cases j <;>
  simp only [iw_dπ, iwasawaField, iwasawaK, iw_iwasawa_eq, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Real.cos_neg, Real.sin_neg, Fin.zero_eta,
    Fin.mk_one] <;>
  generalize Real.exp r = E at * <;>
  generalize Real.exp (-r) = Ei at * <;>
  generalize Real.exp (2 * r) = E2 at * <;>
  generalize Real.cos θ = C at * <;>
  generalize Real.sin θ = S at * <;>
  generalize X 0 0 = a at * <;>
  generalize X 0 1 = b at * <;>
  generalize X 1 0 = c at * <;>
  generalize X 1 1 = d at *
  · linear_combination (C*E*a + C*Ei*c*s - E*S*b - 2*E*S*c + E2*Ei*S*b + E2*Ei*S*c - Ei*S*d*s) *
      hcs + (4*C*E*S ^ 2*a - 2*E*S ^ 3*b - 2*E*S ^ 3*c + E*S*b + E*S*c) * hEE +
      (2*C*E*S ^ 2 - 2*C*E2*Ei*S ^ 2 - Ei*S*s) * htr +
      (4*C*Ei*S ^ 2*a - 2*Ei*S ^ 3*b - 2*Ei*S ^ 3*c + Ei*S*b + Ei*S*c) * hE2
  · linear_combination (-C*E*c + C*E2*Ei*b + C*E2*Ei*c - C*Ei*a*s - 2*E*S*a + E*S*d +
      2*E2*Ei*S*a - 2*E2*Ei*S*d + Ei*S*b*s) * hcs +
      (-2*C*E*S ^ 2*b - 2*C*E*S ^ 2*c + C*E*b + C*E*c - 4*E*S ^ 3*a + 4*E*S*a) * hEE +
      (-C*Ei*s - 2*E*S ^ 3 + 2*E*S + 2*E2*Ei*S ^ 3 - 2*E2*Ei*S) * htr +
      (-2*C*Ei*S ^ 2*b - 2*C*Ei*S ^ 2*c + C*Ei*b + C*Ei*c - 4*Ei*S ^ 3*a + 4*Ei*S*a) * hE2
  · linear_combination (C*Ei*c - Ei*S*d) * hcs + (-Ei*S) * htr
  · linear_combination (-C*Ei*a + Ei*S*b) * hcs + (-C*Ei) * htr

/-- `Dπ(p)` is injective: if `Dπ(p) v = 0` then `v = 0` (`π⁻¹ Dπ(p) v` is
`k⁻¹(v₁e^{-2r}E + v₂H + v₃J)k`). -/
private lemma iw_eq_zero_of_dπ {p v : ℝ × ℝ × ℝ} (h : ∀ i j, iw_dπ p v i j = 0) : v = 0 := by
  obtain ⟨s, r, θ⟩ := p
  obtain ⟨v₁, v₂, v₃⟩ := v
  have h00 := h 0 0
  have h01 := h 0 1
  have h10 := h 1 0
  have h11 := h 1 1
  simp only [iw_dπ, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at h00 h01 h10 h11
  have hcs := Real.cos_sq_add_sin_sq θ
  have hE0 := (Real.exp_pos (-r)).ne'
  have h2 : v₂ * Real.exp (-r) = 0 := by
    linear_combination (-Real.sin θ) * h10 + (-Real.cos θ) * h11 + (-(v₂ * Real.exp (-r))) * hcs
  have h3 : v₃ * Real.exp (-r) = 0 := by
    linear_combination Real.cos θ * h10 - Real.sin θ * h11 - v₃ * Real.exp (-r) * hcs
  have hv₂ := (mul_eq_zero.1 h2).resolve_right hE0
  have hv₃ := (mul_eq_zero.1 h3).resolve_right hE0
  subst hv₂ hv₃
  have h1 : v₁ * Real.exp (-r) = 0 := by
    linear_combination Real.sin θ * h00 + Real.cos θ * h01 - v₁ * Real.exp (-r) * hcs
  have hv₁ := (mul_eq_zero.1 h1).resolve_right hE0
  subst hv₁
  rfl

/-- **Path lifting** through the Iwasawa chart: a continuous curve in `SL₂(ℝ)` on `[0, T]` lifts
to a continuous curve in `ℝ³` from any point over its initial point.

Proof: `s = (ac + bd)/(c² + d²)` and `r = -log √(c² + d²)` are continuous functions of `g`; the
angle `θ` lifts the class of `arg(d + ic)` in `ℝ/2πℤ` through the covering `ℝ → ℝ/2πℤ`
(`IsCoveringMap.exists_path_lifts`, after reparametrizing `[0, T]` by `[0, 1]`). -/
theorem exists_continuousOn_lift {T : ℝ} (hT : 0 ≤ T) {g : ℝ → Mat2}
    (hg : ContinuousOn g (Icc 0 T)) (hdet : ∀ t ∈ Icc 0 T, (g t).det = 1) {p₀ : ℝ × ℝ × ℝ}
    (hp₀ : iwasawa p₀ = g 0) :
    ∃ p : ℝ → ℝ × ℝ × ℝ, ContinuousOn p (Icc 0 T) ∧ p 0 = p₀ ∧
      ∀ t ∈ Icc 0 T, iwasawa (p t) = g t := by
  rcases hT.eq_or_lt with rfl | hT
  · refine ⟨fun _ ↦ p₀, continuousOn_const, rfl, fun t ht ↦ ?_⟩
    rw [Icc_self, mem_singleton_iff] at ht
    rw [ht, hp₀]
  have hgij : ∀ i j, ContinuousOn (fun t ↦ g t i j) (Icc 0 T) :=
    Matrix.continuousOn_iff_entrywise.1 hg
  -- the point `d + ic` of `ℂ \ {0}`, whose argument is the angle `θ`
  set z : ℝ → ℂ := fun t ↦ (g t 1 1 : ℂ) + (g t 1 0 : ℂ) * Complex.I with hz_def
  have hz0 : ∀ t ∈ Icc 0 T, z t ≠ 0 := fun t ht h ↦ by
    have h1 : g t 1 1 = 0 := by simpa [hz_def] using congrArg Complex.re h
    have h2 : g t 1 0 = 0 := by simpa [hz_def] using congrArg Complex.im h
    have := iw_row_pos (hdet t ht)
    rw [h1, h2] at this
    simp at this
  have hzc : ContinuousOn z (Icc 0 T) :=
    (Complex.continuous_ofReal.comp_continuousOn (hgij 1 1)).add
      ((Complex.continuous_ofReal.comp_continuousOn (hgij 1 0)).mul continuousOn_const)
  have hnorm : ∀ t, ‖z t‖ = √(g t 1 0 ^ 2 + g t 1 1 ^ 2) := fun t ↦ by
    rw [Complex.norm_def, Complex.normSq_apply]
    simp [hz_def]
    ring_nf
  -- its argument in `ℝ/2πℤ` along `[0, T]`, reparametrized by `[0, 1]`
  have hσ : ∀ σ : unitInterval, (σ : ℝ) * T ∈ Icc 0 T := fun σ ↦
    ⟨mul_nonneg σ.2.1 hT.le, by nlinarith [σ.2.1, σ.2.2]⟩
  have hzσ : Continuous fun σ : unitInterval ↦ z (σ * T) :=
    hzc.comp_continuous (by fun_prop) hσ
  have hγc : Continuous fun σ : unitInterval ↦ ((Complex.arg (z (σ * T)) : ℝ) : Real.Angle) :=
    continuous_iff_continuousAt.2 fun σ ↦
      (Complex.continuousAt_arg_coe_angle (hz0 _ (hσ σ))).comp
        (f := fun σ : unitInterval ↦ z (σ * T)) hzσ.continuousAt
  let γ : C(unitInterval, AddCircle (2 * Real.pi)) := ⟨_, hγc⟩
  have hγ0 : γ 0 = ((p₀.2.2 : ℝ) : AddCircle (2 * Real.pi)) := by
    change ((Complex.arg (z ((0 : unitInterval) * T)) : ℝ) : Real.Angle) = (p₀.2.2 : Real.Angle)
    have hz00 : z ((0 : unitInterval) * T) = (Real.exp (-p₀.2.1) : ℂ) *
        (Real.Angle.cos (p₀.2.2 : Real.Angle) + Real.Angle.sin (p₀.2.2 : Real.Angle) *
          Complex.I) := by
      have h10 := congrFun (congrFun hp₀ 1) 0
      have h11 := congrFun (congrFun hp₀ 1) 1
      rw [iw_iwasawa_eq] at h10 h11
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one] at h10 h11
      simp only [hz_def, Set.Icc.coe_zero, zero_mul, ← h10, ← h11, Real.Angle.cos_coe,
        Real.Angle.sin_coe]
      push_cast
      ring
    rw [hz00, Complex.arg_mul_cos_add_sin_mul_I_coe_angle (Real.exp_pos _)]
  obtain ⟨Γ, hΓ, hΓ0⟩ :=
    (AddCircle.isCoveringMap_coe (2 * Real.pi)).exists_path_lifts γ p₀.2.2 hγ0
  set θ : ℝ → ℝ := fun t ↦ Γ (Set.projIcc 0 1 zero_le_one (t / T)) with hθ_def
  have hθc : Continuous θ := Γ.continuous.comp (continuous_projIcc.comp (by fun_prop))
  -- `θ(t)` is an angle of `d + ic`
  have hθarg : ∀ t ∈ Icc 0 T, (θ t : Real.Angle) = (Complex.arg (z t) : Real.Angle) := by
    intro t ht
    have hmem : t / T ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg ht.1 hT.le, (div_le_one hT).2 ht.2⟩
    have h := congrFun hΓ (Set.projIcc 0 1 zero_le_one (t / T))
    simp only [Function.comp_apply] at h
    change (θ t : Real.Angle) = _ at h
    rw [h]
    change ((Complex.arg (z ((Set.projIcc 0 1 zero_le_one (t / T) : ℝ) * T)) : ℝ) :
      Real.Angle) = _
    rw [Set.projIcc_of_mem _ hmem, Subtype.coe_mk, div_mul_cancel₀ t hT.ne']
  refine ⟨fun t ↦ ((g t 0 0 * g t 1 0 + g t 0 1 * g t 1 1) / (g t 1 0 ^ 2 + g t 1 1 ^ 2),
    -Real.log √(g t 1 0 ^ 2 + g t 1 1 ^ 2), θ t), ?_, ?_, ?_⟩
  · have hpos : ∀ t ∈ Icc 0 T, g t 1 0 ^ 2 + g t 1 1 ^ 2 ≠ 0 := fun t ht ↦
      (iw_row_pos (hdet t ht)).ne'
    have hn : ContinuousOn (fun t ↦ g t 1 0 ^ 2 + g t 1 1 ^ 2) (Icc 0 T) :=
      ((hgij 1 0).pow 2).add ((hgij 1 1).pow 2)
    refine ContinuousOn.prodMk ?_ (ContinuousOn.prodMk ?_ hθc.continuousOn)
    · exact (((hgij 0 0).mul (hgij 1 0)).add ((hgij 0 1).mul (hgij 1 1))).div hn hpos
    · refine (hn.sqrt.log fun t ht ↦ ?_).neg
      exact (Real.sqrt_pos.2 (iw_row_pos (hdet t ht))).ne'
  · have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
    have hq : iwasawa ((g 0 0 0 * g 0 1 0 + g 0 0 1 * g 0 1 1) / (g 0 1 0 ^ 2 + g 0 1 1 ^ 2),
        -Real.log √(g 0 1 0 ^ 2 + g 0 1 1 ^ 2), θ 0) = g 0 := by
      refine iw_iwasawa_of_cos_sin (hdet 0 h0) ?_ ?_
      · rw [← Real.Angle.cos_coe, hθarg 0 h0, Real.Angle.cos_coe, Complex.cos_arg (hz0 0 h0),
          hnorm]
        simp [hz_def]
      · rw [← Real.Angle.sin_coe, hθarg 0 h0, Real.Angle.sin_coe, Complex.sin_arg, hnorm]
        simp [hz_def]
    obtain ⟨h1, h2, -⟩ := (iwasawa_eq_iwasawa_iff _ _).1 (hq.trans hp₀.symm)
    have h3 : θ 0 = p₀.2.2 := by
      simp only [hθ_def, zero_div]
      rw [Set.projIcc_left]
      exact hΓ0
    exact Prod.ext h1 (Prod.ext h2 h3)
  · intro t ht
    refine iw_iwasawa_of_cos_sin (hdet t ht) ?_ ?_
    · rw [← Real.Angle.cos_coe, hθarg t ht, Real.Angle.cos_coe, Complex.cos_arg (hz0 t ht),
        hnorm]
      simp [hz_def]
    · rw [← Real.Angle.sin_coe, hθarg t ht, Real.Angle.sin_coe, Complex.sin_arg, hnorm]
      simp [hz_def]

/-- Uniqueness of lifts: two continuous curves on `[0, T]` with the same image under `π` and the
same initial point agree (`s, r` agree by `iwasawa_eq_iwasawa_iff`, and the difference of the
angles is continuous with values in the discrete set `2πℤ`, hence constant). -/
theorem eqOn_of_iwasawa_eq {T : ℝ} {p p' : ℝ → ℝ × ℝ × ℝ} (hp : ContinuousOn p (Icc 0 T))
    (hp' : ContinuousOn p' (Icc 0 T)) (h : ∀ t ∈ Icc 0 T, iwasawa (p t) = iwasawa (p' t))
    (h0 : p 0 = p' 0) : EqOn p p' (Icc 0 T) := by
  intro t ht
  have hfib := fun τ hτ ↦ (iwasawa_eq_iwasawa_iff (p τ) (p' τ)).1 (h τ hτ)
  -- the difference of the angles is continuous with values in `2πℤ`, hence constant
  have hc : ContinuousOn (fun τ ↦ (p' τ).2.2 - (p τ).2.2) (Icc 0 T) :=
    (continuous_snd.comp_continuousOn (continuous_snd.comp_continuousOn hp')).sub
      (continuous_snd.comp_continuousOn (continuous_snd.comp_continuousOn hp))
  have hmaps : MapsTo (fun τ ↦ (p' τ).2.2 - (p τ).2.2) (Icc 0 T)
      (AddSubgroup.zmultiples (2 * Real.pi) : Set ℝ) := by
    intro τ hτ
    obtain ⟨-, -, n, hn⟩ := hfib τ hτ
    refine ⟨n, ?_⟩
    simp only [hn, zsmul_eq_mul]
    ring
  have hd := isPreconnected_Icc.constant_of_mapsTo
    (isDiscrete_iff_discreteTopology.2
      (inferInstance : DiscreteTopology (AddSubgroup.zmultiples (2 * Real.pi)))) hc hmaps ht
    ⟨le_rfl, ht.1.trans ht.2⟩
  obtain ⟨h1, h2, -⟩ := hfib t ht
  simp only [h0, sub_self] at hd
  exact Prod.ext h1 (Prod.ext h2 (by linarith))

/-! ### Absolutely continuous curves

Carathéodory solutions are indefinite integrals of integrable functions, hence absolutely
continuous; a `C¹` function of one is again absolutely continuous, with the derivative given by
the chain rule almost everywhere, and is the indefinite integral of that derivative (the
fundamental theorem of calculus for absolutely continuous functions). -/

/-- Absolute continuity by comparison: if `dist (f s) (f t) ≤ dist (g s) (g t)` on `[a, b]` and
`g` is absolutely continuous, so is `f`. -/
theorem iw_absolutelyContinuousOnInterval_of_dist_le {X : Type*} [PseudoMetricSpace X]
    {f : ℝ → X} {g : ℝ → ℝ} {a b : ℝ} (hg : AbsolutelyContinuousOnInterval g a b)
    (h : ∀ s ∈ uIcc a b, ∀ t ∈ uIcc a b, dist (f s) (f t) ≤ dist (g s) (g t)) :
    AbsolutelyContinuousOnInterval f a b := by
  apply squeeze_zero' ?_ ?_ hg
  · exact .of_forall fun _ ↦ Finset.sum_nonneg fun _ _ ↦ dist_nonneg
  rw [Filter.eventually_inf_principal]
  filter_upwards with E hE
  exact Finset.sum_le_sum fun i hi ↦ h _ (hE.left i hi).left _ (hE.left i hi).right

section AbsolutelyContinuous

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- A curve in integral form `x(t) = x(0) + ∫₀ᵗ v` is continuous on `[0, T]`. -/
theorem iw_continuousOn_of_eq_add_integral {T : ℝ} (hT : 0 ≤ T) {x v : ℝ → E}
    (hv : IntervalIntegrable v volume 0 T)
    (hx : ∀ t ∈ Icc 0 T, x t = x 0 + ∫ s in (0 : ℝ)..t, v s) : ContinuousOn x (Icc 0 T) := by
  have hc := intervalIntegral.continuousOn_primitive_interval' hv left_mem_uIcc
  rw [uIcc_of_le hT] at hc
  exact (continuousOn_const.add hc).congr hx

/-- A curve in integral form `x(t) = x(0) + ∫₀ᵗ v` has derivative `v(t)` at almost every
`t ∈ (0, T)` (Lebesgue's differentiation theorem). -/
theorem iw_ae_hasDerivAt_of_eq_add_integral {T : ℝ} {x v : ℝ → E}
    (hv : IntervalIntegrable v volume 0 T)
    (hx : ∀ t ∈ Icc 0 T, x t = x 0 + ∫ s in (0 : ℝ)..t, v s) :
    ∀ᵐ t, t ∈ Ioo 0 T → HasDerivAt x (v t) t := by
  filter_upwards [hv.ae_hasDerivAt_integral] with t ht htT
  have hT : 0 ≤ T := (htT.1.trans htT.2).le
  have h0 : (0 : ℝ) ∈ uIcc 0 T := left_mem_uIcc
  have htm : t ∈ uIcc 0 T := by rw [uIcc_of_le hT]; exact Ioo_subset_Icc_self htT
  have hd := (ht htm 0 h0).const_add (x 0)
  exact hd.congr_of_eventuallyEq
    (Filter.eventually_of_mem (Icc_mem_nhds htT.1 htT.2) fun s hs ↦ hx s hs)

omit [FiniteDimensional ℝ E] in
/-- If `F` is `C¹` on an open set `O` containing `x([0, T])`, `x(t) = x(0) + ∫₀ᵗ v`, then
`F ∘ x` is absolutely continuous on `[0, T]`: `F` is Lipschitz on the compact set `x([0, T])`,
and `‖x(t) - x(s)‖ ≤ |∫ₛᵗ ‖v‖|`. -/
theorem iw_absolutelyContinuousOnInterval_comp {O : Set E} (hO : IsOpen O) {F : E → ℝ}
    (hF : ContDiffOn ℝ 1 F O) {T : ℝ} (hT : 0 ≤ T) {x v : ℝ → E}
    (hv : IntervalIntegrable v volume 0 T)
    (hx : ∀ t ∈ Icc 0 T, x t = x 0 + ∫ s in (0 : ℝ)..t, v s) (hxO : ∀ t ∈ Icc 0 T, x t ∈ O) :
    AbsolutelyContinuousOnInterval (fun t ↦ F (x t)) 0 T := by
  have hxc := iw_continuousOn_of_eq_add_integral hT hv hx
  have hK : IsCompact (x '' Icc 0 T) := isCompact_Icc.image_of_continuousOn hxc
  have hloc : LocallyLipschitzOn (x '' Icc 0 T) F := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨K, U, hU, hKU⟩ :=
      (hF.contDiffAt (hO.mem_nhds (hxO t ht))).exists_lipschitzOnWith
    exact ⟨K, U, nhdsWithin_le_nhds hU, hKU⟩
  obtain ⟨L, hL⟩ := hloc.exists_lipschitzOnWith_of_compact hK
  have hN := (hv.norm.absolutelyContinuousOnInterval_intervalIntegral
    (c := 0) left_mem_uIcc).const_mul (L : ℝ)
  refine iw_absolutelyContinuousOnInterval_of_dist_le hN fun s hs t ht ↦ ?_
  rw [uIcc_of_le hT] at hs ht
  have hvs : IntervalIntegrable v volume 0 s := hv.mono_set (by
    rw [uIcc_of_le hT, uIcc_of_le hs.1]; exact Icc_subset_Icc_right hs.2)
  have hvt : IntervalIntegrable v volume 0 t := hv.mono_set (by
    rw [uIcc_of_le hT, uIcc_of_le ht.1]; exact Icc_subset_Icc_right ht.2)
  calc dist (F (x s)) (F (x t)) ≤ L * dist (x s) (x t) :=
        hL.dist_le_mul _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    _ = L * ‖∫ r in t..s, v r‖ := by
        rw [dist_eq_norm, hx s hs, hx t ht, add_sub_add_left_eq_sub,
          intervalIntegral.integral_interval_sub_left hvs hvt]
    _ ≤ L * |∫ r in t..s, ‖v r‖| := by
        gcongr; exact intervalIntegral.norm_integral_le_abs_integral_norm
    _ = dist (L * ∫ r in (0 : ℝ)..s, ‖v r‖) (L * ∫ r in (0 : ℝ)..t, ‖v r‖) := by
        rw [Real.dist_eq, ← mul_sub, abs_mul, NNReal.abs_eq,
          intervalIntegral.integral_interval_sub_left hvs.norm hvt.norm]

/-- The fundamental theorem of calculus for an absolutely continuous `f` whose derivative is `φ`
almost everywhere: `φ` is integrable and `f(t) = f(0) + ∫₀ᵗ φ`. -/
theorem iw_eq_add_integral_of_ae_hasDerivAt {f φ : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hf : AbsolutelyContinuousOnInterval f 0 T)
    (hφ : ∀ᵐ t, t ∈ Ioo 0 T → HasDerivAt f (φ t) t) :
    IntervalIntegrable φ volume 0 T ∧ ∀ t ∈ Icc 0 T, f t = f 0 + ∫ s in (0 : ℝ)..t, φ s := by
  have hne : ∀ᵐ t : ℝ, t ≠ T := by simp [ae_iff, measure_singleton]
  have hae : ∀ᵐ t, t ∈ Ioc 0 T → deriv f t = φ t := by
    filter_upwards [hφ, hne] with t ht htT ht'
    exact (ht ⟨ht'.1, lt_of_le_of_ne ht'.2 htT⟩).deriv
  refine ⟨hf.intervalIntegrable_deriv.congr_ae ?_, fun t ht ↦ ?_⟩
  · rw [uIoc_of_le hT]
    exact (ae_restrict_iff' measurableSet_Ioc).2 hae
  · have hft : AbsolutelyContinuousOnInterval f 0 t := hf.mono (by
      rw [uIcc_of_le hT, uIcc_of_le ht.1]; exact Icc_subset_Icc_right ht.2)
    rw [← intervalIntegral.integral_congr_ae (f := deriv f), hft.integral_deriv_eq_sub]
    · ring
    · filter_upwards [hae] with s hs hs'
      rw [uIoc_of_le ht.1] at hs'
      exact hs ⟨hs'.1, hs'.2.trans ht.2⟩

/-- **Chain rule for Carathéodory curves.** If `x(t) = x(0) + ∫₀ᵗ v` on `[0, T]` and `F` is `C¹`
on an open set containing `x([0, T])`, then `F(x(t)) = F(x(0)) + ∫₀ᵗ DF(x) v`, the integrand
being integrable. -/
theorem iw_comp_eq_add_integral {O : Set E} (hO : IsOpen O) {F : E → ℝ}
    (hF : ContDiffOn ℝ 1 F O) {T : ℝ} (hT : 0 ≤ T) {x v : ℝ → E}
    (hv : IntervalIntegrable v volume 0 T)
    (hx : ∀ t ∈ Icc 0 T, x t = x 0 + ∫ s in (0 : ℝ)..t, v s) (hxO : ∀ t ∈ Icc 0 T, x t ∈ O) :
    IntervalIntegrable (fun s ↦ fderiv ℝ F (x s) (v s)) volume 0 T ∧
      ∀ t ∈ Icc 0 T, F (x t) = F (x 0) + ∫ s in (0 : ℝ)..t, fderiv ℝ F (x s) (v s) := by
  refine iw_eq_add_integral_of_ae_hasDerivAt hT
    (iw_absolutelyContinuousOnInterval_comp hO hF hT hv hx hxO) ?_
  filter_upwards [iw_ae_hasDerivAt_of_eq_add_integral hv hx] with t ht ht'
  have hd : DifferentiableAt ℝ F (x t) :=
    (hF.contDiffAt (hO.mem_nhds (hxO t (Ioo_subset_Icc_self ht')))).differentiableAt
      one_ne_zero
  exact hd.hasFDerivAt.comp_hasDerivAt t (ht ht')

end AbsolutelyContinuous

/-- The coordinate `s` of `π(s, r, θ) = [[a, b], [c, d]]`: `s = (ac + bd)/(c² + d²)`. -/
private lemma iw_fst_eq (p : ℝ × ℝ × ℝ) : p.1 =
    (iwasawa p 0 0 * iwasawa p 1 0 + iwasawa p 0 1 * iwasawa p 1 1) /
      (iwasawa p 1 0 ^ 2 + iwasawa p 1 1 ^ 2) := by
  have hn := iw_row_pos (det_iwasawa p)
  rw [eq_div_iff hn.ne', iw_iwasawa_eq]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

/-- The coordinate `r` of `π(s, r, θ) = [[a, b], [c, d]]`: `c² + d² = e^{-2r}`. -/
private lemma iw_snd_eq (p : ℝ × ℝ × ℝ) : p.2.1 =
    -(1 / 2) * Real.log (iwasawa p 1 0 ^ 2 + iwasawa p 1 1 ^ 2) := by
  have h : iwasawa p 1 0 ^ 2 + iwasawa p 1 1 ^ 2 = Real.exp (-2 * p.2.1) := by
    rw [iw_iwasawa_eq]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    have he : Real.exp (-2 * p.2.1) = Real.exp (-p.2.1) ^ 2 := by
      rw [sq, ← Real.exp_add]; ring_nf
    rw [he]
    linear_combination Real.exp (-p.2.1) ^ 2 * Real.sin_sq_add_cos_sq p.2.2
  rw [h, Real.log_exp]
  ring

/-- The angle of a continuous lift is differentiable wherever the curve below is: near `t`,
`θ(τ) = θ(t) + arctan(γ(τ)/δ(τ))` with `γ(τ) = c(τ)d(t) - d(τ)c(t)` and
`δ(τ) = d(τ)d(t) + c(τ)c(t)`, as `(c, d) = e^{-r}(sin θ, cos θ)` and `|θ(τ) - θ(t)| < π/2`. -/
private lemma iw_differentiableAt_angle {p : ℝ → ℝ × ℝ × ℝ} {g : ℝ → Mat2} {S : Set ℝ} {t : ℝ}
    (hS : S ∈ 𝓝 t) (hpg : ∀ τ ∈ S, iwasawa (p τ) = g τ)
    (hp : ContinuousAt (fun τ ↦ (p τ).2.2) t)
    (hc : DifferentiableAt ℝ (fun τ ↦ g τ 1 0) t) (hd : DifferentiableAt ℝ (fun τ ↦ g τ 1 1) t) :
    DifferentiableAt ℝ (fun τ ↦ (p τ).2.2) t := by
  have hentries : ∀ τ ∈ S, g τ 1 0 = Real.exp (-(p τ).2.1) * Real.sin (p τ).2.2 ∧
      g τ 1 1 = Real.exp (-(p τ).2.1) * Real.cos (p τ).2.2 := fun τ hτ ↦ by
    rw [← hpg τ hτ, iw_iwasawa_eq]; simp
  obtain ⟨hct, hdt⟩ := hentries t (mem_of_mem_nhds hS)
  have hδ : g t 1 1 * g t 1 1 + g t 1 0 * g t 1 0 ≠ 0 := by
    have h : g t 1 1 * g t 1 1 + g t 1 0 * g t 1 0 = Real.exp (-(p t).2.1) ^ 2 := by
      rw [hct, hdt]
      linear_combination Real.exp (-(p t).2.1) ^ 2 * Real.sin_sq_add_cos_sq (p t).2.2
    rw [h]
    positivity
  have hD : DifferentiableAt ℝ (fun τ ↦ (p t).2.2 + Real.arctan
      ((g τ 1 0 * g t 1 1 - g τ 1 1 * g t 1 0) / (g τ 1 1 * g t 1 1 + g τ 1 0 * g t 1 0))) t :=
    (((hc.mul_const _).sub (hd.mul_const _)).div ((hd.mul_const _).add (hc.mul_const _))
      hδ).arctan.const_add _
  refine hD.congr_of_eventuallyEq ?_
  have hnear : ∀ᶠ τ in 𝓝 t, (p τ).2.2 ∈ Ioo ((p t).2.2 - Real.pi / 2) ((p t).2.2 + Real.pi / 2) :=
    hp.eventually_mem (Ioo_mem_nhds (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]))
  filter_upwards [hS, hnear] with τ hτ hθ
  obtain ⟨hcτ, hdτ⟩ := hentries τ hτ
  have hpos : 0 < Real.exp (-(p τ).2.1) * Real.exp (-(p t).2.1) := by positivity
  have hcos : 0 < Real.cos ((p τ).2.2 - (p t).2.2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hq : (g τ 1 0 * g t 1 1 - g τ 1 1 * g t 1 0) / (g τ 1 1 * g t 1 1 + g τ 1 0 * g t 1 0) =
      Real.tan ((p τ).2.2 - (p t).2.2) := by
    have hc' : Real.cos (p τ).2.2 * Real.cos (p t).2.2 + Real.sin (p τ).2.2 * Real.sin (p t).2.2
        ≠ 0 := by rw [← Real.cos_sub]; exact hcos.ne'
    rw [Real.tan_eq_sin_div_cos, Real.sin_sub, Real.cos_sub, hcτ, hdτ, hct, hdt]
    rw [div_eq_div_iff ?_ hc']
    · ring
    · have e : Real.exp (-(p τ).2.1) * Real.cos (p τ).2.2 *
          (Real.exp (-(p t).2.1) * Real.cos (p t).2.2) + Real.exp (-(p τ).2.1) *
          Real.sin (p τ).2.2 * (Real.exp (-(p t).2.1) * Real.sin (p t).2.2) =
          Real.exp (-(p τ).2.1) * Real.exp (-(p t).2.1) * (Real.cos (p τ).2.2 *
            Real.cos (p t).2.2 + Real.sin (p τ).2.2 * Real.sin (p t).2.2) := by ring
      rw [e]
      exact mul_ne_zero hpos.ne' hc'
  rw [hq, Real.arctan_tan (by linarith [hθ.1]) (by linarith [hθ.2])]
  ring

/-- The lift of a solution of `g' = gX` (Carathéodory) is a solution of
`p' = iwasawaField p X`, for `X` continuous and traceless.

Proof: `g` is `C¹` (`gX` is continuous). At interior times `p` is differentiable (`s, r` are
smooth functions of `g`, and `θ = θ(t) + arctan(γ/δ)` near `t`, `iw_differentiableAt_angle`),
and `Dπ(p)p' = g' = gX = Dπ(p)(iwasawaField p X)` (`fderiv_iwasawa_iwasawaField`); `Dπ(p)` is
injective, so `p' = iwasawaField p X`, which is continuous; conclude by the fundamental theorem
of calculus. -/
theorem isIntegralCurve_lift {T : ℝ} (hT : 0 ≤ T) {g X : ℝ → Mat2}
    (hg : IsIntegralCurve g (fun t ↦ g t * X t) T) (hX : ContinuousOn X (Icc 0 T))
    (hXtr : ∀ t ∈ Icc 0 T, (X t).trace = 0) {p : ℝ → ℝ × ℝ × ℝ} (hp : ContinuousOn p (Icc 0 T))
    (hpg : ∀ t ∈ Icc 0 T, iwasawa (p t) = g t) :
    IntervalIntegrable (fun t ↦ iwasawaField (p t) (X t)) volume 0 T ∧
      ∀ t ∈ Icc 0 T, p t = p 0 + ∫ r in (0 : ℝ)..t, iwasawaField (p r) (X r) := by
  have hgc : ContinuousOn g (Icc 0 T) := Matrix.continuousOn_of_eq_add_integral hg
  have hXij := Matrix.continuousOn_iff_entrywise.1 hX
  have hgij := Matrix.continuousOn_iff_entrywise.1 hgc
  have hgX : ContinuousOn (fun t ↦ g t * X t) (Icc 0 T) := by
    refine Matrix.continuousOn_iff_entrywise.2 fun i j ↦ ?_
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    exact ((hgij i 0).mul (hXij 0 j)).add ((hgij i 1).mul (hXij 1 j))
  -- the lifted field along `p` is continuous on `[0, T]`
  have hr : ContinuousOn (fun t ↦ (p t).2.1) (Icc 0 T) :=
    continuous_fst.comp_continuousOn (continuous_snd.comp_continuousOn hp)
  have hθ : ContinuousOn (fun t ↦ (p t).2.2) (Icc 0 T) :=
    continuous_snd.comp_continuousOn (continuous_snd.comp_continuousOn hp)
  have hGc : ContinuousOn (fun t ↦ iwasawaField (p t) (X t)) (Icc 0 T) := by
    have h00 := hXij 0 0
    have h01 := hXij 0 1
    have h10 := hXij 1 0
    have h11 := hXij 1 1
    simp only [iwasawaField, iwasawaK, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    fun_prop
  have hGi : IntervalIntegrable (fun t ↦ iwasawaField (p t) (X t)) volume 0 T :=
    (hGc.mono (by rw [uIcc_of_le hT])).intervalIntegrable
  refine ⟨hGi, fun t ht ↦ ?_⟩
  -- at interior points, `p` is differentiable, and `Dπ(p)p' = g' = gX = Dπ(p)(iwasawaField p X)`
  have hderiv : ∀ τ ∈ Ioo 0 T, HasDerivAt p (iwasawaField (p τ) (X τ)) τ := by
    intro τ hτ
    have hτ' := Ioo_subset_Icc_self hτ
    have hS : Icc 0 T ∈ 𝓝 τ := Icc_mem_nhds hτ.1 hτ.2
    have hgd : Matrix.HasDerivAtEntrywise g (g τ * X τ) τ :=
      Matrix.hasDerivAtEntrywise_of_eq_add_integral hg hτ (hgX.continuousAt hS)
    have hpos : g τ 1 0 ^ 2 + g τ 1 1 ^ 2 ≠ 0 := by
      rw [← hpg τ hτ']; exact (iw_row_pos (det_iwasawa _)).ne'
    have hd1 : DifferentiableAt ℝ (fun σ ↦ (p σ).1) τ := by
      refine DifferentiableAt.congr_of_eventuallyEq (f := fun σ ↦
        (g σ 0 0 * g σ 1 0 + g σ 0 1 * g σ 1 1) / (g σ 1 0 ^ 2 + g σ 1 1 ^ 2)) ?_ ?_
      · exact ((((hgd 0 0).differentiableAt.mul (hgd 1 0).differentiableAt).add
          ((hgd 0 1).differentiableAt.mul (hgd 1 1).differentiableAt)).div
          (((hgd 1 0).differentiableAt.pow 2).add ((hgd 1 1).differentiableAt.pow 2)) hpos)
      · filter_upwards [hS] with σ hσ
        rw [iw_fst_eq (p σ), hpg σ hσ]
    have hd2 : DifferentiableAt ℝ (fun σ ↦ (p σ).2.1) τ := by
      refine DifferentiableAt.congr_of_eventuallyEq (f := fun σ ↦
        -(1 / 2) * Real.log (g σ 1 0 ^ 2 + g σ 1 1 ^ 2)) ?_ ?_
      · have hc := (hgd 1 0).differentiableAt
        have hd := (hgd 1 1).differentiableAt
        have hq : DifferentiableAt ℝ (fun σ ↦ g σ 1 0 ^ 2 + g σ 1 1 ^ 2) τ := by fun_prop
        exact (hq.log hpos).const_mul _
      · filter_upwards [hS] with σ hσ
        rw [iw_snd_eq (p σ), hpg σ hσ]
    have hd3 : DifferentiableAt ℝ (fun σ ↦ (p σ).2.2) τ :=
      iw_differentiableAt_angle hS hpg (hθ.continuousAt hS) (hgd 1 0).differentiableAt
        (hgd 1 1).differentiableAt
    have hpd : DifferentiableAt ℝ p τ := hd1.prodMk (hd2.prodMk hd3)
    have hkey : ∀ i j, iw_dπ (p τ) (deriv p τ - iwasawaField (p τ) (X τ)) i j = 0 := by
      intro i j
      rw [← iw_fderiv_iwasawa]
      have hπd : DifferentiableAt ℝ (fun q ↦ iwasawa q i j) (p τ) :=
        ((contDiff_iwasawa i j).differentiable (by simp)).differentiableAt
      have h1 := hπd.hasFDerivAt.comp_hasDerivAt τ hpd.hasDerivAt
      have h2 : HasDerivAt (fun σ ↦ iwasawa (p σ) i j) ((g τ * X τ) i j) τ :=
        (hgd i j).congr_of_eventuallyEq
          (Filter.eventually_of_mem hS fun σ hσ ↦ by simp only [hpg σ hσ])
      rw [map_sub, h1.unique h2, fderiv_iwasawa_iwasawaField _ (hXtr τ hτ'), hpg τ hτ',
        sub_self]
    have h0 := iw_eq_zero_of_dπ hkey
    rw [sub_eq_zero] at h0
    rw [← h0]
    exact hpd.hasDerivAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    (hp.mono (Icc_subset_Icc_right ht.2)) (fun τ hτ ↦ hderiv τ ⟨hτ.1, hτ.2.trans_le ht.2⟩)
    (hGi.mono_set (by rw [uIcc_of_le hT, uIcc_of_le ht.1]; exact Icc_subset_Icc_right ht.2))]
  abel

/-- Conversely, the image under `π` of a solution of `p' = iwasawaField p X` (Carathéodory), `X`
traceless, solves `g' = gX` (the chain rule for absolutely continuous curves,
`iw_comp_eq_add_integral`, and `fderiv_iwasawa_iwasawaField`). -/
theorem isIntegralCurve_iwasawa {T : ℝ} (hT : 0 ≤ T) {X : ℝ → Mat2}
    (hXtr : ∀ t ∈ Icc 0 T, (X t).trace = 0) {p : ℝ → ℝ × ℝ × ℝ} (hp : ContinuousOn p (Icc 0 T))
    (hint : IntervalIntegrable (fun t ↦ iwasawaField (p t) (X t)) volume 0 T)
    (hpeq : ∀ t ∈ Icc 0 T, p t = p 0 + ∫ r in (0 : ℝ)..t, iwasawaField (p r) (X r)) :
    IsIntegralCurve (fun t ↦ iwasawa (p t)) (fun t ↦ iwasawa (p t) * X t) T := by
  intro i j
  obtain ⟨hI, hE⟩ := iw_comp_eq_add_integral isOpen_univ
    ((contDiff_iwasawa i j).contDiffOn.of_le (by exact_mod_cast le_top)) hT hint hpeq
    (fun _ _ ↦ mem_univ _)
  have heq : ∀ s ∈ Icc 0 T, fderiv ℝ (fun q ↦ iwasawa q i j) (p s) (iwasawaField (p s) (X s)) =
      (iwasawa (p s) * X s) i j := fun s hs ↦ fderiv_iwasawa_iwasawaField _ (hXtr s hs) i j
  refine ⟨(intervalIntegrable_congr fun s hs ↦ ?_).1 hI, fun t ht ↦ ?_⟩
  · rw [uIoc_of_le hT] at hs
    exact heq s (Ioc_subset_Icc_self hs)
  · change iwasawa (p t) i j = iwasawa (p 0) i j + ∫ s in (0 : ℝ)..t, (iwasawa (p s) * X s) i j
    rw [hE t ht, intervalIntegral.integral_congr fun s hs ↦ heq s ?_]
    rw [uIcc_of_le ht.1] at hs
    exact ⟨hs.1, hs.2.trans ht.2⟩

end SmoothedPolygons
