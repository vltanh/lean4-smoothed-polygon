module

public import SmoothedPolygons.Ch15.CellCoordinates
public import Mathlib.Algebra.CubicDiscriminant
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Basic.Analysis.Polynomial.CubicRoots

/-!
# Chapter 15: switching polynomials, the smaller cells and Proposition 15.2.2 (§15.1–§15.2)

The switching functions of the cells of Hales–Vajjha, *Packings of Smoothed Polygons*, §15.1
(TeX 12086–12143) and the smaller cells of §15.2 ("Smaller cells", TeX 12209–12314):

* the switching functions `χ_A = χ^u_{u-1}` (switch from the first control `u` to `1`) and
  `χ_B = χ^u_{u-ū}` (switch from `u` to `ū`) as real cubics in `t` (`chiA`, `chiB`; explicit
  coefficients `chiA_chiB_eq`), the multiplicities `m_A`, `m_B` of the root `t = 0`, the reduced
  polynomials `χ_{A,m_A} = χ_A/t^{m_A}`, `χ_{B,m_B} = χ_B/t^{m_B}`, their discriminants
  `Δ_{A,m_A}`, `Δ_{B,m_B}` and the resultant `res_AB` (Mathlib's `Polynomial.discr`, normalized so
  that a real polynomial with only real roots has `Δ ≥ 0`, and `Polynomial.resultant`);
* on the big open cells `(m_A, m_B) = (0, 1)` (TeX 12137–12138);
* the 2-cells `𝒞₂(ζ, 0, 2)` (`topFaceOne`, `θ₂ = π`), `𝒞₂(ζ², 0, 2)` (`topFaceTwo`, `θ₂ = 0`) with
  its parts `𝒞₂^A = {Δ_{A,0} ≥ 0}` and `𝒞₂^B = {Δ_{A,0} < 0}` (TeX 12411–12422), the closed 2-cells
  `𝒞₂(ζ, 1, 1)` (`frontBackOne`, `z₃ = 0`, `θ₂ ∈ [π/3, π]`) and `𝒞₂(ζ², 1, 1)` (`frontBackTwo`,
  `θ₂ ∈ [-π, -π/3]`);
* the Descartes-rule facts on the 2-cells, the impossibility of `(m_A, m_B) = (0, 3)`;
* the **root-based cell maps** `F_A` and `F_B` of `𝒞₂(ζ², 0, 2)` (`cellMapA`, `cellMapB`) and where
  they agree with the Poincaré map `poincare`;
* Remark 15.2.1, Proposition 15.2.2 and the boundary maps on the red-shaded faces of Figure 15.1.

The continuity statements of §15.1–§15.2 (of the first switching time off the discriminant and
resultant loci, and of the dynamics up to the faces; of `F_A` and `F_B`) are in
`SmoothedPolygons/Ch15/Continuity.lean`.

## The semantic Poincaré map and the book's cell maps

`poincare` switches when the first control stops being optimal (`SmoothedPolygons/Ch13/Defs.lean`);
a tangency (a double root of a switching function at which the control stays optimal) is not a
switch. The book's maps on closed cells are continuous extensions from the interiors and may switch
at a tangency. On `𝒞₂(ζ², 0, 2)` the book's `F_A` uses the least positive root of `χ_{A,0}` on
all of `𝒞₂^A = {Δ_{A,0} ≥ 0}` (TeX 12413–12422), a double root on `{Δ_{A,0} = 0}`, where `poincare`
does not switch and agrees with `F_B` instead (`firstSwitchTime_topFaceTwo`; for example `r₂ = 1/2`,
`ψ = 1.0548151712321…`: double root `t = 1.30848`, switch at `6 r₁ sin ψ = 2.60943`; checklist,
line "L5 (Chapter 15)"). Both maps are stated here, with the agreement on `{Δ_{A,0} > 0}` and on
`{Δ_{A,0} ≤ 0}` respectively.

## Proofs

The switching functions are explicit cubics (`chiA_chiB_eq`, from (13.2.2)); on the cells their
coefficients have fixed signs, and Descartes's rule of signs (for a real cubic with all roots real,
the signs of the elementary symmetric functions) gives the root counts. On `𝒞₂(ζ², 0, 2)`, with
`z = (r₁ e^{-iψ}, r₂, -2 r₁ r₂ sin ψ)`, `χ_B = -t²(t/12 + y₁/2)` has the positive root
`t_B = -6 y₁ = 6 r₁ sin ψ`, and
`√3 χ_A = 3 r₁ r₂ S - (3/2) r₂ t - (r₁/4)(3C - √3 S) t² + (√3/12) t³` (`S = sin ψ`, `C = cos ψ`)
decreases on `(0, t_m)` and increases after its local minimum `t_m`. If `χ_{A,0}` has positive
roots, the least one is `≤ t_B` (the book asserts that "the first switching time is a root of
`χ_{A,0}`", TeX 12413–12415, and gives no argument for this estimate; the argument is this
formalization's): otherwise `χ_A(t_B) > 0` and `χ_A'(t_B) < 0`, that is
`r₁² S (√3 S - C) > (2/9) r₂` and `r₁² S (8√3 S - 6C) < r₂`, which together force
`3.5 √3 S < 1.5 C`, while the first forces `√3 S > C`: a contradiction. Continuity of the switching
times (`SmoothedPolygons/Ch15/Continuity.lean`) is continuity of simple roots. The limits at faces
where the cell's control is not the first control are a semicontinuity argument: the control is
beaten at times arbitrarily close to `0` at the face point, hence (strict inequalities are open) at
nearby points.

The maximum condition for `u ∈ {ζ, ζ²}` is `χ_A ≥ 0 ∧ χ_B ≥ 0` (`V_T = {1, u, ū}`), so the first
control and the first switching time are read off the signs of the two cubics. The root counts of
Descartes's rule are proved for the two sign patterns that occur: with `a < 0 < c, d`,
`t² P(s) - s² P(t) > 0` for `0 ≤ s < t`, so `P` has one positive root and changes sign there; with
`a, d > 0 > c`, a negative root `r₀` (intermediate value theorem) splits off, `P = (t - r₀) q`, and
`Δ(P) = Δ(q) q(r₀)²` with `q(r₀) > 0`, so `Δ(P)` decides whether `q` has two positive roots
(product `> 0`, sum `> 0`) or none (these general facts about real cubics are in
`Basic/Analysis/Polynomial/CubicRoots.lean`). The sign `χ_A'(t_B) < 0` in the estimate above is
obtained from this factorization (`1/(t - r₀) < 1/(r₁ - t) + 1/(r₂ - t)` on `[0, r₁)`); the estimate
is `leastPosRoot_chiA_le_of_mem_topFaceTwo`.
-/

@[expose] public section

namespace SmoothedPolygons

open Complex Set Filter Topology Polynomial
open scoped Real

namespace TriFuller

/-! ### Switching functions as cubic polynomials -/

/-- The value of a cubic: `P(t) = a t³ + b t² + c t + d`. -/
private lemma l5b_eval (P : Cubic ℝ) (t : ℝ) :
    P.toPoly.eval t = P.a * t ^ 3 + P.b * t ^ 2 + P.c * t + P.d := by
  simp [Cubic.toPoly]

private lemma l5b_sqrt3_pos : (0 : ℝ) < √3 := by positivity

private lemma l5b_sqrt3_mul : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)

/-- The switching function `χ^u_d(t, z⁰) = RR(d, z₃(t, z⁰, u))/√3` (`switchingFunction`) as a real
cubic polynomial in `t`, from (13.2.2): coefficients `RR(d, -iu)/(6√3)` of `t³`,
`RR(d, z₁⁰)/(2√3)` of `t²`, `RR(d, z₂⁰)/√3` of `t` and `RR(d, z₃⁰)/√3`. -/
noncomputable def switchingCubic (u d : ℂ) (z : Fin 3 → ℂ) : Cubic ℝ :=
  ⟨RR d (-I * u) / (6 * √3), RR d (z 0) / (2 * √3), RR d (z 1) / √3, RR d (z 2) / √3⟩

/-- The cubic `switchingCubic` evaluates to the switching function. -/
theorem eval_switchingCubic (u d : ℂ) (z : Fin 3 → ℂ) (t : ℝ) :
    (switchingCubic u d z).toPoly.eval t = switchingFunction u d t z := by
  have h3 := l5b_sqrt3_pos.ne'
  rw [l5b_eval]
  simp only [switchingCubic, switchingFunction, RR_eq_re_mul_add_im_mul]
  simp [flow, Complex.mul_re, Complex.mul_im, pow_succ]
  field_simp
  ring

/-- `H_F(z(t), u) - H_F(z(t), v) = √3 χ^u_{u-v}(t)` along the trajectory with control `u`. -/
private lemma l5b_ham_sub_eq (t : ℝ) (z : Fin 3 → ℂ) (u v : ℂ) :
    ham (flow t z u) u - ham (flow t z u) v =
      √3 * (switchingCubic u (u - v) z).toPoly.eval t := by
  have h3 := l5b_sqrt3_pos.ne'
  rw [ham_flow_sub_ham_flow, l5b_eval]
  simp only [switchingCubic]
  field_simp
  ring

/-- `χ_A = χ^u_{u-1}` (TeX 12088–12091): the switching function from the first control `u` to the
control `1`. -/
noncomputable def chiA (u : ℂ) (z : Fin 3 → ℂ) : Cubic ℝ := switchingCubic u (u - 1) z

/-- `χ_B = χ^u_{u-ū}` (TeX 12088–12091): the switching function from the first control `u` to the
control `ū` (`ζ ↔ ζ²`). -/
noncomputable def chiB (u : ℂ) (z : Fin 3 → ℂ) : Cubic ℝ :=
  switchingCubic u (u - starRingEnd ℂ u) z

/-- `m_A`: the multiplicity of `t = 0` as a root of `χ_A` (TeX 12088–12090). -/
noncomputable def multA (u : ℂ) (z : Fin 3 → ℂ) : ℕ := (chiA u z).toPoly.rootMultiplicity 0

/-- `m_B`: the multiplicity of `t = 0` as a root of `χ_B`. -/
noncomputable def multB (u : ℂ) (z : Fin 3 → ℂ) : ℕ := (chiB u z).toPoly.rootMultiplicity 0

/-- The reduced switching polynomial `χ_{A,m_A} = χ_A/t^{m_A}` (TeX 12091). -/
noncomputable def chiARed (u : ℂ) (z : Fin 3 → ℂ) : ℝ[X] := (chiA u z).toPoly /ₘ X ^ multA u z

/-- The reduced switching polynomial `χ_{B,m_B} = χ_B/t^{m_B}` (TeX 12091). -/
noncomputable def chiBRed (u : ℂ) (z : Fin 3 → ℂ) : ℝ[X] := (chiB u z).toPoly /ₘ X ^ multB u z

/-- The discriminant `Δ_{A,m_A}` of `χ_{A,m_A}` (TeX 12092). -/
noncomputable def discrA (u : ℂ) (z : Fin 3 → ℂ) : ℝ := (chiARed u z).discr

/-- The discriminant `Δ_{B,m_B}` of `χ_{B,m_B}` (TeX 12092). -/
noncomputable def discrB (u : ℂ) (z : Fin 3 → ℂ) : ℝ := (chiBRed u z).discr

/-- The resultant `res_AB` of `χ_{A,m_A}` and `χ_{B,m_B}` (TeX 12134–12135). -/
noncomputable def resAB (u : ℂ) (z : Fin 3 → ℂ) : ℝ := (chiARed u z).resultant (chiBRed u z)

/-- The switching cubics explicitly, with `z_j = x_j + i y_j` (from (13.2.2); `ζ = -1/2 + (√3/2)i`):
* `χ_A` for `u = ζ`: `-t³/12 + (y₁ - √3 x₁) t²/4 + (y₂ - √3 x₂) t/2 + (y₃ - √3 x₃)/2`;
* `χ_B` for `u = ζ`: `t³/12 + y₁ t²/2 + y₂ t + y₃`;
* `χ_A` for `u = ζ²`: `t³/12 - (y₁ + √3 x₁) t²/4 - (y₂ + √3 x₂) t/2 - (y₃ + √3 x₃)/2`;
* `χ_B` for `u = ζ²`: `-(t³/12 + y₁ t²/2 + y₂ t + y₃)`. -/
theorem chiA_chiB_eq (z : Fin 3 → ℂ) :
    chiA ζ z = ⟨-1 / 12, ((z 0).im - √3 * (z 0).re) / 4, ((z 1).im - √3 * (z 1).re) / 2,
      ((z 2).im - √3 * (z 2).re) / 2⟩ ∧
    chiB ζ z = ⟨1 / 12, (z 0).im / 2, (z 1).im, (z 2).im⟩ ∧
    chiA (ζ ^ 2) z = ⟨1 / 12, -((z 0).im + √3 * (z 0).re) / 4, -((z 1).im + √3 * (z 1).re) / 2,
      -((z 2).im + √3 * (z 2).re) / 2⟩ ∧
    chiB (ζ ^ 2) z = ⟨-1 / 12, -(z 0).im / 2, -(z 1).im, -(z 2).im⟩ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [chiA, chiB, switchingCubic, conj_ζ, conj_ζ_sq, RR_eq_re_mul_add_im_mul,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
      Complex.neg_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im, ζ_re, ζ_im,
      ζ_sq_re, ζ_sq_im] <;>
    refine Cubic.ext ?_ ?_ ?_ ?_
  all_goals
    dsimp only
    rw [div_eq_iff (by positivity)]
    ring_nf
    try norm_num [Real.sq_sqrt]
    try ring

/-! ### Helpers: the maximum condition through `χ_A` and `χ_B` -/

/-- The cell point in coordinates: `x₁ = r₁ cos(θ₂ - ψ)`, `y₁ = r₁ sin(θ₂ - ψ)`, `x₂ = r₂ cos θ₂`,
`y₂ = r₂ sin θ₂`, `x₃ = -2 r₁ r₂ sin ψ`, `y₃ = 0`. -/
private lemma l5b_cellPoint_apply (p : Fin 3 → ℝ) :
    (cellPoint p 0).re = (1 - p 0) * Real.cos (p 2 - p 1) ∧
    (cellPoint p 0).im = (1 - p 0) * Real.sin (p 2 - p 1) ∧
    (cellPoint p 1).re = p 0 * Real.cos (p 2) ∧
    (cellPoint p 1).im = p 0 * Real.sin (p 2) ∧
    (cellPoint p 2).re = -2 * (1 - p 0) * p 0 * Real.sin (p 1) ∧
    (cellPoint p 2).im = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [cellPoint, Matrix.cons_val_zero, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  · simp only [cellPoint, Matrix.cons_val_zero, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  · simp only [cellPoint, Matrix.cons_val_one, Matrix.cons_val_zero, Complex.re_ofReal_mul,
      Complex.exp_ofReal_mul_I_re]
  · simp only [cellPoint, Matrix.cons_val_one, Matrix.cons_val_zero, Complex.im_ofReal_mul,
      Complex.exp_ofReal_mul_I_im]
  · exact Complex.ofReal_re _
  · exact Complex.ofReal_im _

/-- `cellPoint p ≠ 0`: `‖z₁‖ + ‖z₂‖ = |1 - r₂| + |r₂| > 0`. -/
private lemma l5b_cellPoint_ne_zero (p : Fin 3 → ℝ) : cellPoint p ≠ 0 := by
  intro h
  have h0 := congrArg (fun z ↦ ‖z 0‖) h
  have h1 := congrArg (fun z ↦ ‖z 1‖) h
  simp only [cellPoint, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, norm_zero,
    norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at h0 h1
  rw [abs_eq_zero] at h0 h1
  linarith

private lemma l5b_continuous_cellPoint : Continuous cellPoint := by
  refine continuous_pi fun j ↦ ?_
  fin_cases j <;> simp only [cellPoint] <;> fun_prop

private lemma l5b_continuous_flow (u : ℂ) :
    Continuous fun x : ℝ × (Fin 3 → ℂ) ↦ flow x.1 x.2 u := by
  refine continuous_pi fun j ↦ ?_
  fin_cases j <;> simp only [flow] <;> fun_prop

private lemma l5b_continuous_ham (v : ℂ) : Continuous fun w : Fin 3 → ℂ ↦ ham w v := by
  simp only [ham, RR]
  fun_prop

private lemma l5b_ζ_ne_ζ_sq : ζ ≠ ζ ^ 2 := by
  intro h
  have := congrArg Complex.im h
  rw [ζ_im, ζ_sq_im] at this
  linarith [l5b_sqrt3_pos]

private lemma l5b_mem_VT_of {u : ℂ} (hu : u = ζ ∨ u = ζ ^ 2) : u ∈ VT := by
  rcases hu with rfl | rfl
  exacts [ζ_mem_VT, ζ_sq_mem_VT]

/-- The maximum condition for `u ∈ {ζ, ζ²}` along its trajectory at time `t` is
`χ_A(t) ≥ 0 ∧ χ_B(t) ≥ 0` (`V_T = {1, u, ū}`). -/
private lemma l5b_ham_le_iff {u : ℂ} (hu : u = ζ ∨ u = ζ ^ 2) (z : Fin 3 → ℂ) (t : ℝ) :
    (∀ v ∈ VT, ham (flow t z u) v ≤ ham (flow t z u) u) ↔
      0 ≤ (chiA u z).toPoly.eval t ∧ 0 ≤ (chiB u z).toPoly.eval t := by
  have hA : ham (flow t z u) u - ham (flow t z u) 1 = √3 * (chiA u z).toPoly.eval t :=
    l5b_ham_sub_eq t z u 1
  have hB : ham (flow t z u) u - ham (flow t z u) (starRingEnd ℂ u) =
      √3 * (chiB u z).toPoly.eval t := l5b_ham_sub_eq t z u _
  have h3 := l5b_sqrt3_pos
  constructor
  · intro h
    have h1 := h 1 one_mem_VT
    have h2 := h _ (conj_mem_VT (l5b_mem_VT_of hu))
    constructor
    · by_contra hc
      push Not at hc
      nlinarith [mul_neg_of_pos_of_neg h3 hc]
    · by_contra hc
      push Not at hc
      nlinarith [mul_neg_of_pos_of_neg h3 hc]
  · rintro ⟨hA', hB'⟩ v hv
    have e1 : ham (flow t z u) 1 ≤ ham (flow t z u) u := by nlinarith [mul_nonneg h3.le hA']
    have e2 : ham (flow t z u) (starRingEnd ℂ u) ≤ ham (flow t z u) u := by
      nlinarith [mul_nonneg h3.le hB']
    rcases mem_VT.1 hv with rfl | rfl | rfl
    · exact e1
    · rcases hu with rfl | rfl
      · exact le_rfl
      · rwa [conj_ζ_sq] at e2
    · rcases hu with rfl | rfl
      · rwa [conj_ζ] at e2
      · exact le_rfl

/-- `u ∈ {ζ, ζ²}` is beaten at time `t` exactly when `χ_A(t) < 0` or `χ_B(t) < 0`. -/
private lemma l5b_beaten_iff {u : ℂ} (hu : u = ζ ∨ u = ζ ^ 2) (z : Fin 3 → ℂ) (t : ℝ) :
    (∃ v ∈ VT, ham (flow t z u) u < ham (flow t z u) v) ↔
      (chiA u z).toPoly.eval t < 0 ∨ (chiB u z).toPoly.eval t < 0 := by
  rw [← not_iff_not]
  push Not
  exact l5b_ham_le_iff hu z t

private lemma l5b_isFirstControl_of {u : ℂ} (hu : u = ζ ∨ u = ζ ^ 2) {z : Fin 3 → ℂ} {ε : ℝ}
    (hε : 0 < ε)
    (h : ∀ t ∈ Icc 0 ε, 0 ≤ (chiA u z).toPoly.eval t ∧ 0 ≤ (chiB u z).toPoly.eval t) :
    IsFirstControl z u :=
  ⟨l5b_mem_VT_of hu, ε, hε, fun t ht ↦ (l5b_ham_le_iff hu z t).2 (h t ht)⟩

private lemma l5b_not_isFirstControl {u : ℂ} (hu : u = ζ ∨ u = ζ ^ 2) {z : Fin 3 → ℂ}
    (h : ∃ ε > 0, ∀ t ∈ Ioc 0 ε, (chiA u z).toPoly.eval t < 0) : ¬ IsFirstControl z u := by
  rintro ⟨-, ε, hε, hmax⟩
  obtain ⟨ε', hε', h⟩ := h
  have := ((l5b_ham_le_iff hu z (min ε ε')).1
    (hmax _ ⟨(lt_min hε hε').le, min_le_left _ _⟩)).1
  linarith [h (min ε ε') ⟨lt_min hε hε', min_le_right _ _⟩]

/-- The first switching time of a point with first control `u ∈ {ζ, ζ²}`: the infimum of the
positive times at which `χ_A` or `χ_B` is negative. -/
private lemma l5b_firstSwitchTime_eq {u : ℂ} (hu : u = ζ ∨ u = ζ ^ 2) {z : Fin 3 → ℂ}
    (hz : z ≠ 0) (hfc : IsFirstControl z u) :
    firstSwitchTime z = sInf {t | 0 < t ∧
      ((chiA u z).toPoly.eval t < 0 ∨ (chiB u z).toPoly.eval t < 0)} := by
  have hf : firstControl z = u := (firstControl_eq_iff hz).2 hfc
  unfold firstSwitchTime
  rw [hf]
  congr 1
  ext t
  simp only [Set.mem_ofPred_eq, l5b_beaten_iff hu]

/-- If the first nonzero coefficient of `P` (from the constant term up) is positive, `P ≥ 0` on
some `[0, ε]`. -/
private lemma l5b_nonneg_near_zero (P : Cubic ℝ)
    (h : 0 < P.d ∨ (P.d = 0 ∧ 0 < P.c) ∨ (P.d = 0 ∧ P.c = 0 ∧ 0 < P.b) ∨
      (P.d = 0 ∧ P.c = 0 ∧ P.b = 0 ∧ 0 < P.a)) :
    ∃ ε > 0, ∀ t ∈ Icc 0 ε, 0 ≤ P.toPoly.eval t := by
  obtain ⟨ε, hε, hpos⟩ := exists_forall_Ioc_cubic_pos h
  refine ⟨ε, hε, fun t ht ↦ ?_⟩
  rw [l5b_eval]
  rcases ht.1.eq_or_lt with rfl | ht0
  · have : 0 ≤ P.d := by rcases h with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> linarith
    simpa using this
  · linarith [hpos t ⟨ht0, ht.2⟩]

/-- If the first nonzero coefficient of `P` is negative, `P < 0` on some `(0, ε]`. -/
private lemma l5b_neg_near_zero (P : Cubic ℝ)
    (h : P.d < 0 ∨ (P.d = 0 ∧ P.c < 0) ∨ (P.d = 0 ∧ P.c = 0 ∧ P.b < 0) ∨
      (P.d = 0 ∧ P.c = 0 ∧ P.b = 0 ∧ P.a < 0)) :
    ∃ ε > 0, ∀ t ∈ Ioc 0 ε, P.toPoly.eval t < 0 := by
  obtain ⟨ε, hε, hpos⟩ := exists_forall_Ioc_cubic_pos (a := -P.d) (b := -P.c) (c := -P.b)
    (d := -P.a) (by
      rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩
      · exact Or.inl (by linarith)
      · exact Or.inr (Or.inl ⟨by rw [h1]; simp, by linarith⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨by rw [h1]; simp, by rw [h2]; simp, by linarith⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨by rw [h1]; simp, by rw [h2]; simp, by rw [h3]; simp,
          by linarith⟩)))
  exact ⟨ε, hε, fun t ht ↦ by rw [l5b_eval]; linarith [hpos t ht]⟩

private lemma l5b_rootMultiplicity_zero {P : ℝ[X]} (hP : P ≠ 0) {n : ℕ}
    (h0 : ∀ k < n, P.coeff k = 0) (hn : P.coeff n ≠ 0) : P.rootMultiplicity 0 = n := by
  apply le_antisymm
  · rw [rootMultiplicity_le_iff hP, map_zero, sub_zero, X_pow_dvd_iff]
    exact fun h ↦ hn (h n (Nat.lt_succ_self n))
  · rw [le_rootMultiplicity_iff hP, map_zero, sub_zero, X_pow_dvd_iff]
    exact h0

/-- The multiplicity of the root `t = 0` of a cubic is the number of its vanishing low-order
coefficients. -/
private lemma l5b_mult_cubic (P : Cubic ℝ) (ha : P.a ≠ 0) :
    (P.d ≠ 0 → P.toPoly.rootMultiplicity 0 = 0) ∧
    (P.d = 0 → P.c ≠ 0 → P.toPoly.rootMultiplicity 0 = 1) ∧
    (P.d = 0 → P.c = 0 → P.b ≠ 0 → P.toPoly.rootMultiplicity 0 = 2) ∧
    (P.d = 0 → P.c = 0 → P.b = 0 → P.toPoly.rootMultiplicity 0 = 3) := by
  have hP := Cubic.ne_zero_of_a_ne_zero ha
  refine ⟨fun hd ↦ ?_, fun hd hc ↦ ?_, fun hd hc hb ↦ ?_, fun hd hc hb ↦ ?_⟩
  · exact l5b_rootMultiplicity_zero hP (fun k hk ↦ absurd hk (Nat.not_lt_zero k))
      (by rwa [Cubic.coeff_eq_d])
  · refine l5b_rootMultiplicity_zero hP (fun k hk ↦ ?_) (by rwa [Cubic.coeff_eq_c])
    interval_cases k
    rwa [Cubic.coeff_eq_d]
  · refine l5b_rootMultiplicity_zero hP (fun k hk ↦ ?_) (by rwa [Cubic.coeff_eq_b])
    interval_cases k
    · rwa [Cubic.coeff_eq_d]
    · rwa [Cubic.coeff_eq_c]
  · refine l5b_rootMultiplicity_zero hP (fun k hk ↦ ?_) (by rwa [Cubic.coeff_eq_a])
    interval_cases k
    · rwa [Cubic.coeff_eq_d]
    · rwa [Cubic.coeff_eq_c]
    · rwa [Cubic.coeff_eq_b]

/-- The switching cubics at a cell point, with `r₂ = p 0`, `ψ = p 1`, `θ₂ = p 2`. -/
private lemma l5b_chi_cellPoint (p : Fin 3 → ℝ) :
    chiA ζ (cellPoint p) = ⟨-1 / 12,
      (1 - p 0) * (Real.sin (p 2 - p 1) - √3 * Real.cos (p 2 - p 1)) / 4,
      p 0 * (Real.sin (p 2) - √3 * Real.cos (p 2)) / 2, √3 * (1 - p 0) * p 0 * Real.sin (p 1)⟩ ∧
    chiB ζ (cellPoint p) =
      ⟨1 / 12, (1 - p 0) * Real.sin (p 2 - p 1) / 2, p 0 * Real.sin (p 2), 0⟩ ∧
    chiA (ζ ^ 2) (cellPoint p) = ⟨1 / 12,
      -((1 - p 0) * (Real.sin (p 2 - p 1) + √3 * Real.cos (p 2 - p 1))) / 4,
      -(p 0 * (Real.sin (p 2) + √3 * Real.cos (p 2))) / 2,
      √3 * (1 - p 0) * p 0 * Real.sin (p 1)⟩ ∧
    chiB (ζ ^ 2) (cellPoint p) =
      ⟨-1 / 12, -((1 - p 0) * Real.sin (p 2 - p 1)) / 2, -(p 0 * Real.sin (p 2)), 0⟩ := by
  obtain ⟨h1, h2, h3, h4⟩ := chiA_chiB_eq (cellPoint p)
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := l5b_cellPoint_apply p
  rw [h1, h2, h3, h4, e1, e2, e3, e4, e5, e6]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> refine Cubic.ext ?_ ?_ ?_ ?_ <;> dsimp only <;> ring

/-- The signs on the first big open cell: `-(√3/2) x₃ = √3 r₁ r₂ sin ψ > 0`, `0 < r₁` and
`y₂ = r₂ sin θ₂ > 0`. -/
private lemma l5b_openBoxOne_signs {p : Fin 3 → ℝ} (hp : p ∈ openBoxOne) :
    0 < √3 * (1 - p 0) * p 0 * Real.sin (p 1) ∧ 0 < 1 - p 0 ∧ 0 < p 0 * Real.sin (p 2) := by
  obtain ⟨⟨h0, h0'⟩, ⟨h1, h1'⟩, ⟨h2, h2'⟩⟩ := hp
  have hr : 0 < 1 - p 0 := by linarith
  exact ⟨mul_pos (mul_pos (mul_pos l5b_sqrt3_pos hr) h0) (Real.sin_pos_of_pos_of_lt_pi h1 h1'),
    hr, mul_pos h0 (Real.sin_pos_of_pos_of_lt_pi h2 h2')⟩

/-- The signs on the second big open cell: `√3 r₁ r₂ sin ψ > 0`, `0 < r₁` and `y₂ < 0`. -/
private lemma l5b_openBoxTwo_signs {p : Fin 3 → ℝ} (hp : p ∈ openBoxTwo) :
    0 < √3 * (1 - p 0) * p 0 * Real.sin (p 1) ∧ 0 < 1 - p 0 ∧ p 0 * Real.sin (p 2) < 0 := by
  obtain ⟨⟨h0, h0'⟩, ⟨h1, h1'⟩, ⟨h2, h2'⟩⟩ := hp
  have hr : 0 < 1 - p 0 := by linarith
  exact ⟨mul_pos (mul_pos (mul_pos l5b_sqrt3_pos hr) h0) (Real.sin_pos_of_pos_of_lt_pi h1 h1'),
    hr, mul_neg_of_pos_of_neg h0 (Real.sin_neg_of_neg_of_neg_pi_lt h2' h2)⟩

/-- On the big open cells `(m_A, m_B) = (0, 1)` (the notation `𝒞₃(u, 0, 1)⁰` of Definition 15.1.2;
"`χ_{A,0}(0) ≠ 0` and `χ_{B,1}(0) ≠ 0` on the big open cells", TeX 12137–12138): `χ_A(0) =
-(√3/2) x₃ ≠ 0` and `χ_B = t (±y₂ + …)` with `y₂ ≠ 0`. -/
theorem multA_multB_of_mem_openBox :
    (∀ p ∈ openBoxOne, multA ζ (cellPoint p) = 0 ∧ multB ζ (cellPoint p) = 1) ∧
      ∀ p ∈ openBoxTwo, multA (ζ ^ 2) (cellPoint p) = 0 ∧ multB (ζ ^ 2) (cellPoint p) = 1 := by
  refine ⟨fun p hp ↦ ?_, fun p hp ↦ ?_⟩
  · obtain ⟨hA, hB, -, -⟩ := l5b_chi_cellPoint p
    obtain ⟨hd, -, hy₂⟩ := l5b_openBoxOne_signs hp
    exact ⟨(l5b_mult_cubic _ (by rw [hA]; norm_num)).1 (by rw [hA]; exact hd.ne'),
      (l5b_mult_cubic _ (by rw [hB]; norm_num)).2.1 (by rw [hB]) (by rw [hB]; exact hy₂.ne')⟩
  · obtain ⟨-, -, hA, hB⟩ := l5b_chi_cellPoint p
    obtain ⟨hd, -, hy₂⟩ := l5b_openBoxTwo_signs hp
    exact ⟨(l5b_mult_cubic _ (by rw [hA]; norm_num)).1 (by rw [hA]; exact hd.ne'),
      (l5b_mult_cubic _ (by rw [hB]; norm_num)).2.1 (by rw [hB])
        (by rw [hB]; dsimp only; linarith)⟩

/-- The first control on the first big open cell is `ζ` (Definition 15.1.2, `definition15_1_2`). -/
private lemma l5b_isFirstControl_openBoxOne {p : Fin 3 → ℝ} (hp : p ∈ openBoxOne) :
    IsFirstControl (cellPoint p) ζ :=
  (firstControl_eq_iff (l5b_cellPoint_ne_zero p)).1 (definition15_1_2.2.2.2.2.2.1 p hp)

/-- The first control on the second big open cell is `ζ²` (Definition 15.1.2,
`definition15_1_2`). -/
private lemma l5b_isFirstControl_openBoxTwo {p : Fin 3 → ℝ} (hp : p ∈ openBoxTwo) :
    IsFirstControl (cellPoint p) (ζ ^ 2) :=
  (firstControl_eq_iff (l5b_cellPoint_ne_zero p)).1 (definition15_1_2.2.2.2.2.2.2.1 p hp)

/-! ### The smaller cells -/

/-- The 2-cell `𝒞₂(ζ, 0, 2)` (TeX 12223–12226): `x₃ ≠ 0` and `θ₂ = π`, with coordinates
`r₂ ∈ (0, 1)`, `ψ ∈ (0, π)`; the top face of the first big cell. -/
def topFaceOne : Set (Fin 3 → ℝ) := {p | p 0 ∈ Ioo 0 1 ∧ p 1 ∈ Ioo 0 π ∧ p 2 = π}

/-- The 2-cell `𝒞₂(ζ², 0, 2)` (TeX 12235–12238): `x₃ ≠ 0` and `θ₂ = 0`; the top face of the second
big cell. -/
def topFaceTwo : Set (Fin 3 → ℝ) := {p | p 0 ∈ Ioo 0 1 ∧ p 1 ∈ Ioo 0 π ∧ p 2 = 0}

/-- The closed 2-cell `𝒞₂(ζ) = 𝒞₂(ζ, 1, 1)` (TeX 12254–12276): `z₃ = 0`, in coordinates
`ψ ∈ {0, π}`, `r₂ ∈ [0, 1]`, `θ₂ ∈ [π/3, π]`. The book's coordinates are `r̃₁ = r₁ e^{iψ} = ±r₁`
(TeX 12265 writes "`r₁ = r̃₁ e^{iψ}`", reversed; gap G15.3) and `θ₂`; on `r̃₁ = 0` (`r₂ = 1`) the
two values of `ψ` give the same point. It is attached to the front and back faces `ψ ∈ {0, π}` of
the first big cell. -/
def frontBackOne : Set (Fin 3 → ℝ) :=
  {p | p 0 ∈ Icc 0 1 ∧ (p 1 = 0 ∨ p 1 = π) ∧ p 2 ∈ Icc (π / 3) π}

/-- The closed 2-cell `𝒞₂(ζ², 1, 1)` (TeX 12278–12285): `z₃ = 0`, `ψ ∈ {0, π}`, `r₂ ∈ [0, 1]`,
`θ₂ ∈ [-π, -π/3]` (the book: "brought into the interval `(-π, -π/3]`"), attached to the front and
back faces of the second big cell. Only the set is formalized: the book's claims about it (the
first control is `ζ²`, and the cell "can be attached in a similar way to the front and back faces
of the second 3-cell in a way that agrees with the dynamics", TeX 12278–12285) are not, since
`proposition15_2_2` covers `z₃ = 0` by `𝒞₂(ζ, 1, 1)` and no later proof uses `𝒞₂(ζ², 1, 1)`. -/
def frontBackTwo : Set (Fin 3 → ℝ) :=
  {p | p 0 ∈ Icc 0 1 ∧ (p 1 = 0 ∨ p 1 = π) ∧ p 2 ∈ Icc (-π) (-(π / 3))}

/-- The part `𝒞₂^A` of `𝒞₂(ζ², 0, 2)` on which `Δ_{A,0} ≥ 0` (TeX 12411–12415). -/
noncomputable def topFaceTwoA : Set (Fin 3 → ℝ) :=
  {p | p ∈ topFaceTwo ∧ 0 ≤ discrA (ζ ^ 2) (cellPoint p)}

/-- The part `𝒞₂^B` of `𝒞₂(ζ², 0, 2)` on which `Δ_{A,0} < 0` (TeX 12415–12418). -/
noncomputable def topFaceTwoB : Set (Fin 3 → ℝ) :=
  {p | p ∈ topFaceTwo ∧ discrA (ζ ^ 2) (cellPoint p) < 0}

/-- The least positive root of a real polynomial, of any multiplicity (`0` if there is none). -/
noncomputable def leastPosRoot (P : ℝ[X]) : ℝ := sInf {t | 0 < t ∧ P.eval t = 0}

/-- **The root-based cell map `F_A`** of `𝒞₂^A` (TeX 12413–12422): the trajectory with the first
control `ζ²` up to the least positive root of `χ_{A,0}`, double roots included. -/
noncomputable def cellMapA (z : Fin 3 → ℂ) : Fin 3 → ℂ :=
  flow (leastPosRoot (chiA (ζ ^ 2) z).toPoly) z (ζ ^ 2)

/-- **The root-based cell map `F_B`** of `𝒞₂^B` (TeX 12416–12422): the trajectory with the first
control `ζ²` up to the root `t_B = -6 y₁` of the linear polynomial `χ_{B,2} = -(t/12 + y₁/2)`. -/
noncomputable def cellMapB (z : Fin 3 → ℂ) : Fin 3 → ℂ := flow (-6 * (z 0).im) z (ζ ^ 2)

/-! ### The cell `𝒞₂(ζ, 0, 2)` -/

/-- **The cell `𝒞₂(ζ, 0, 2)`** (TeX 12223–12233): "The first control is `ζ`. The switching function
`χ_{B,2}` never has a positive root. Thus, the switching function is always `χ_{A,0}`. By
Descartes's rule of signs, `χ_{A,0}` always has a unique positive root."

Proof route: with `θ₂ = π`, `z = (r₁ e^{i(π - ψ)}, -r₂, -2 r₁ r₂ sin ψ)`, so `y₂ = 0` and
`y₁ = r₁ sin ψ > 0`: the tie between `ζ` and `ζ²` is broken by `y₁` (Lemma 13.2.6),
`χ_B = t²(y₁/2 + t/12)` has `m_B = 2` and `χ_{B,2} > 0` on `[0, ∞)`, and
`√3 χ_A = 3 r₁ r₂ sin ψ + (3/2) r₂ t + (r₁/4)(3 cos ψ + √3 sin ψ) t² - (√3/12) t³` has one sign
change of coefficients; the unique positive root is simple, so it is where `ζ` is first beaten (by
`1`). -/
theorem topFaceOne_switching {p : Fin 3 → ℝ} (hp : p ∈ topFaceOne) :
    firstControl (cellPoint p) = ζ ∧ multA ζ (cellPoint p) = 0 ∧ multB ζ (cellPoint p) = 2 ∧
      (∀ t : ℝ, 0 ≤ t → 0 < (chiBRed ζ (cellPoint p)).eval t) ∧
      ∃ T : ℝ, 0 < T ∧ {t : ℝ | 0 < t ∧ (chiA ζ (cellPoint p)).toPoly.eval t = 0} = {T} ∧
        firstSwitchTime (cellPoint p) = T := by
  obtain ⟨⟨h0, h0'⟩, ⟨h1, h1'⟩, h2⟩ := hp
  obtain ⟨hA, hB, -, -⟩ := l5b_chi_cellPoint p
  simp only [h2, Real.sin_pi_sub, Real.cos_pi_sub, Real.sin_pi, Real.cos_pi] at hA hB
  set z := cellPoint p
  set S := Real.sin (p 1)
  have hS : 0 < S := Real.sin_pos_of_pos_of_lt_pi h1 h1'
  have hr : 0 < 1 - p 0 := by linarith
  have h3 := l5b_sqrt3_pos
  have hd : 0 < √3 * (1 - p 0) * p 0 * S := mul_pos (mul_pos (mul_pos h3 hr) h0) hS
  have hc : 0 < p 0 * (0 - √3 * -1) / 2 := by
    have : 0 < p 0 * √3 := mul_pos h0 h3
    linarith
  obtain ⟨T, hT, hT0, hTpos, hTneg⟩ :=
    exists_pos_root_cubic_of_neg_of_pos_of_pos (a := -1 / 12)
      (b := (1 - p 0) * (S - √3 * -Real.cos (p 1)) / 4) (by norm_num) hc hd
  have hevalA : ∀ t, (chiA ζ z).toPoly.eval t = -1 / 12 * t ^ 3 +
      (1 - p 0) * (S - √3 * -Real.cos (p 1)) / 4 * t ^ 2 + p 0 * (0 - √3 * -1) / 2 * t +
        √3 * (1 - p 0) * p 0 * S := fun t ↦ by rw [l5b_eval, hA]
  have hevalB : ∀ t, (chiB ζ z).toPoly.eval t = t ^ 2 * (t / 12 + (1 - p 0) * S / 2) :=
    fun t ↦ by rw [l5b_eval, hB]; dsimp only; ring
  have hBnn : ∀ t, 0 ≤ t → 0 ≤ (chiB ζ z).toPoly.eval t := fun t ht ↦ by
    rw [hevalB]
    have : 0 < (1 - p 0) * S := mul_pos hr hS
    positivity
  have hfc : IsFirstControl z ζ := l5b_isFirstControl_of (Or.inl rfl) (half_pos hT)
    fun t ht ↦ ⟨by rw [hevalA]; exact (hTpos t ht.1 (by linarith [ht.2])).le, hBnn t ht.1⟩
  have hz := l5b_cellPoint_ne_zero p
  have hmB : multB ζ z = 2 := (l5b_mult_cubic _ (by rw [hB]; norm_num)).2.2.1 (by rw [hB])
    (by rw [hB]; simp) (by rw [hB]; dsimp only; have := mul_pos hr hS; linarith)
  refine ⟨(firstControl_eq_iff hz).2 hfc,
    (l5b_mult_cubic _ (by rw [hA]; norm_num)).1 (by rw [hA]; exact hd.ne'), hmB, ?_, T, hT, ?_,
    ?_⟩
  · intro t ht
    have hpoly : (chiB ζ z).toPoly =
        X ^ 2 * (C (1 / 12 : ℝ) * X + C ((1 - p 0) * S / 2)) := by
      rw [hB]
      simp only [Cubic.toPoly, mul_zero, map_zero, zero_mul, add_zero]
      ring
    rw [chiBRed, hmB, hpoly, mul_divByMonic_cancel_left _ (monic_X_pow 2)]
    simp only [eval_add, eval_mul, eval_C, eval_X]
    have := mul_pos hr hS
    positivity
  · ext t
    simp only [mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨ht, hft⟩
      rw [hevalA] at hft
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · linarith [hTpos t ht.le h]
      · linarith [hTneg t h]
    · rintro rfl
      exact ⟨hT, by rw [hevalA]; exact hT0⟩
  · rw [l5b_firstSwitchTime_eq (Or.inl rfl) hz hfc]
    have : {t | 0 < t ∧ ((chiA ζ z).toPoly.eval t < 0 ∨ (chiB ζ z).toPoly.eval t < 0)} =
        Ioi T := by
      ext t
      simp only [mem_ofPred_eq, mem_Ioi]
      constructor
      · rintro ⟨ht, h | h⟩
        · by_contra hle
          push Not at hle
          rw [hevalA] at h
          rcases hle.lt_or_eq with hlt | rfl
          · linarith [hTpos t ht.le hlt]
          · linarith
        · linarith [hBnn t ht.le]
      · intro ht
        exact ⟨hT.trans ht, Or.inl (by rw [hevalA]; exact hTneg t ht)⟩
    rw [this, csInf_Ioi]

set_option linter.unusedVariables false in
/-- **`(m_A, m_B) = (0, 3)` is impossible** (TeX 12249–12252): "if `m_B = 3`, then `y₁ = y₂ = 0`.
This implies that `r₁ = 0`, `r₂ = 0` or `θ₁, θ₂ ∈ πℤ`. Then `x₃ = -2 r₁ r₂ sin ψ = 0` by (15.1.1),
and `m_A > 0`." (From `chiA_chiB_eq`: `m_B = 3` means `y₃ = y₂ = y₁ = 0`.)

The hypothesis `p ∈ cellDomain` is the book's standing assumption of §15.2 (TeX 12214–12216: the
point is written in the cell coordinates, `r₂ ∈ [0, 1]`, `ψ ∈ [0, π]`); the argument does not use
it (the implications hold for every `p`), and the statement is kept as printed (REPORT.md,
Section 5). -/
theorem multB_eq_three {p : Fin 3 → ℝ} (hp : p ∈ cellDomain) {u : ℂ} (hu : u = ζ ∨ u = ζ ^ 2)
    (h : multB u (cellPoint p) = 3) : cellPoint p 2 = 0 ∧ 0 < multA u (cellPoint p) := by
  obtain ⟨hA1, hB1, hA2, hB2⟩ := l5b_chi_cellPoint p
  have hBa : (chiB u (cellPoint p)).a ≠ 0 := by
    rcases hu with rfl | rfl
    · rw [hB1]; norm_num
    · rw [hB2]; norm_num
  -- `m_B = 3`: the coefficients of `t` and `t²` in `χ_B` vanish, `y₂ = y₁ = 0`
  have hc : (chiB u (cellPoint p)).c = 0 ∧ (chiB u (cellPoint p)).b = 0 := by
    have := (le_rootMultiplicity_iff (Cubic.ne_zero_of_a_ne_zero hBa)).1 (le_of_eq h.symm)
    rw [map_zero, sub_zero, X_pow_dvd_iff] at this
    exact ⟨by rw [← Cubic.coeff_eq_c]; exact this 1 (by norm_num),
      by rw [← Cubic.coeff_eq_b]; exact this 2 (by norm_num)⟩
  have hy : (1 - p 0) * Real.sin (p 2 - p 1) = 0 ∧ p 0 * Real.sin (p 2) = 0 := by
    rcases hu with rfl | rfl
    · rw [hB1] at hc
      dsimp only at hc
      constructor <;> linarith [hc.1, hc.2]
    · rw [hB2] at hc
      dsimp only at hc
      constructor <;> linarith [hc.1, hc.2]
  -- hence `r₁ r₂ sin ψ = 0` (`sin ψ = sin θ₂ cos θ₁ - cos θ₂ sin θ₁`) and `x₃ = 0`
  have hx : (1 - p 0) * p 0 * Real.sin (p 1) = 0 := by
    have e : Real.sin (p 1) =
        Real.sin (p 2) * Real.cos (p 2 - p 1) - Real.cos (p 2) * Real.sin (p 2 - p 1) := by
      rw [← Real.sin_sub]; ring_nf
    rw [e]
    linear_combination (Real.cos (p 2 - p 1) * (1 - p 0)) * hy.2 - (p 0 * Real.cos (p 2)) * hy.1
  have h2 : cellPoint p 2 = 0 := by
    change (((-2 * (1 - p 0) * p 0 * Real.sin (p 1) : ℝ)) : ℂ) = 0
    rw [show -2 * (1 - p 0) * p 0 * Real.sin (p 1) = -2 * ((1 - p 0) * p 0 * Real.sin (p 1)) by
      ring, hx]
    simp
  refine ⟨h2, ?_⟩
  -- `χ_A(0) = 0`, so `m_A > 0`
  have hd : √3 * (1 - p 0) * p 0 * Real.sin (p 1) = 0 := by
    rw [mul_assoc, mul_assoc, ← mul_assoc (1 - p 0), hx, mul_zero]
  have hAa : (chiA u (cellPoint p)).a ≠ 0 := by
    rcases hu with rfl | rfl
    · rw [hA1]; norm_num
    · rw [hA2]; norm_num
  have hAd : (chiA u (cellPoint p)).d = 0 := by
    rcases hu with rfl | rfl
    · rw [hA1]; exact hd
    · rw [hA2]; exact hd
  unfold multA
  rw [rootMultiplicity_pos (Cubic.ne_zero_of_a_ne_zero hAa), IsRoot, l5b_eval, hAd]
  ring

/-! ### The region `z₃ = 0` and the closed 2-cells `𝒞₂(ζ^{±1}, 1, 1)` -/

private lemma l5b_ζ_pow_mem_VT (k : ℕ) : ζ ^ k ∈ VT := by
  induction k with
  | zero => rw [pow_zero]; exact one_mem_VT
  | succ k ih => rw [pow_succ]; exact mul_mem_VT ih ζ_mem_VT

/-- `exp(2πik/3) = ζ^k`. -/
private lemma l5b_exp_eq_ζ_pow (k : ℕ) :
    Complex.exp (((2 * π * k / 3 : ℝ) : ℂ) * I) = ζ ^ k := by
  rw [ζ, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Every angle is `V_T`-equivalent to a unique angle in `(π/3, π]` (TeX 12256–12257): there are
`k` and `θ' ∈ (π/3, π]` with `e^{iθ'} = ζ^k e^{iθ}`. -/
private lemma l5b_rot (θ : ℝ) : ∃ k : ℕ, ∃ θ' ∈ Ioc (π / 3) π,
    Complex.exp ((θ' : ℂ) * I) = ζ ^ k * Complex.exp ((θ : ℂ) * I) := by
  have hp : (0 : ℝ) < 2 * π / 3 := by positivity
  have hmem := toIocMod_mem_Ioc hp (π / 3) θ
  have hθ' := self_sub_toIocDiv_zsmul hp (π / 3) θ
  set m := toIocDiv hp (π / 3) θ
  set n := -m
  have hn : ((n % 3 : ℤ) : ℝ) + 3 * ((n / 3 : ℤ) : ℝ) = (n : ℝ) := by
    exact_mod_cast Int.emod_add_mul_ediv n 3
  have hk0 : 0 ≤ n % 3 := Int.emod_nonneg n (by norm_num)
  have hk : (((n % 3).toNat : ℕ) : ℝ) = ((n % 3 : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hk0]
  refine ⟨(n % 3).toNat, toIocMod hp (π / 3) θ, ⟨hmem.1, by linarith [hmem.2]⟩, ?_⟩
  rw [← l5b_exp_eq_ζ_pow, ← Complex.exp_add]
  apply Complex.exp_eq_exp_iff_exists_int.2
  refine ⟨n / 3, ?_⟩
  have hreal : toIocMod hp (π / 3) θ =
      2 * π * (((n % 3).toNat : ℕ) : ℝ) / 3 + θ + ((n / 3 : ℤ) : ℝ) * (2 * π) := by
    rw [← hθ', zsmul_eq_mul, hk]
    have : (m : ℝ) = -(n : ℝ) := by simp [n]
    rw [this]
    linear_combination (-(2 * π / 3)) * hn
  rw [hreal]
  push_cast
  ring

/-- `RR(z₁, i z₂) = -r₁ r₂ sin ψ` at a cell point. -/
private lemma l5b_RR_cellPoint (p : Fin 3 → ℝ) :
    RR (cellPoint p 0) (cellPoint p 1 * I) = -((1 - p 0) * p 0 * Real.sin (p 1)) := by
  obtain ⟨e1, e2, e3, e4, -, -⟩ := l5b_cellPoint_apply p
  have e : Real.sin (p 1) =
      Real.sin (p 2) * Real.cos (p 2 - p 1) - Real.cos (p 2) * Real.sin (p 2 - p 1) := by
    rw [← Real.sin_sub]; ring_nf
  rw [RR_eq_re_mul_add_im_mul, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, e1, e2,
    e3, e4, e]
  ring

/-- The representatives of the points with `z₃ = 0` (TeX 12254–12258): a point `w` with `w₃ = 0`,
`|w₁| + |w₂| = 1` and `RR(w₁, i w₂) = 0` (the vanishing Hamiltonian) is, after a rotation by
`ζ^k`, the cell point of coordinates `(r₂, ψ, θ₂)` with `ψ ∈ {0, π}` and `θ₂ ∈ (π/3, π]` (with
`ψ = 0` on `r₂ = 0`). -/
private lemma l5b_rep_z3_zero {w : Fin 3 → ℂ} (h2 : w 2 = 0) (hn : ‖w 0‖ + ‖w 1‖ = 1)
    (hRR : RR (w 0) (w 1 * I) = 0) :
    ∃ k : ℕ, ∃ q : Fin 3 → ℝ, (q 0 ∈ Icc 0 1 ∧ (q 1 = 0 ∨ q 1 = π) ∧ q 2 ∈ Ioc (π / 3) π ∧
      (q 0 = 0 → q 1 = 0)) ∧ cellPoint q = ζ ^ k • w := by
  have hw0' : w 0 = (‖w 0‖ : ℂ) * Complex.exp ((arg (w 0) : ℂ) * I) :=
    (Complex.norm_mul_exp_arg_mul_I _).symm
  have hw1' : w 1 = (‖w 1‖ : ℂ) * Complex.exp ((arg (w 1) : ℂ) * I) :=
    (Complex.norm_mul_exp_arg_mul_I _).symm
  by_cases hw1 : w 1 = 0
  · -- `r₂ = 0`: the point `(e^{iθ₁}, 0, 0)`
    have hn0 : ‖w 0‖ = 1 := by rw [hw1, norm_zero, add_zero] at hn; exact hn
    obtain ⟨k, θ', hθ', he⟩ := l5b_rot (arg (w 0))
    refine ⟨k, ![0, 0, θ'], ⟨by simp, by simp, by simpa using hθ', by simp⟩, ?_⟩
    funext j
    fin_cases j
    · simp only [cellPoint, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.cons_val_one,
        Matrix.tail_cons, Matrix.head_cons, Fin.zero_eta, Pi.smul_apply, smul_eq_mul]
      rw [hw0', hn0]
      simp [he]
    · simp [cellPoint, hw1]
    · simp [cellPoint, h2]
  · obtain ⟨k, θ', hθ', he⟩ := l5b_rot (arg (w 1))
    have hn1 : ‖w 1‖ ≤ 1 := by linarith [norm_nonneg (w 0)]
    have hr1 : (((1 - ‖w 1‖ : ℝ)) : ℂ) = (‖w 0‖ : ℂ) := by rw [← hn]; push_cast; ring
    -- the phase `ψ ∈ {0, π}` with `e^{iψ} = e^{i(θ₂ - θ₁)}`
    obtain ⟨ψ, hψ, hψe⟩ : ∃ ψ : ℝ, (ψ = 0 ∨ ψ = π) ∧ (w 0 ≠ 0 →
        Complex.exp (((arg (w 1) - arg (w 0) : ℝ) : ℂ) * I) = Complex.exp ((ψ : ℂ) * I)) := by
      by_cases hw0 : w 0 = 0
      · exact ⟨0, Or.inl rfl, fun h ↦ absurd hw0 h⟩
      have hsin : Real.sin (arg (w 1) - arg (w 0)) = 0 := by
        have e : RR (w 0) (w 1 * I) = -(‖w 0‖ * ‖w 1‖ * Real.sin (arg (w 1) - arg (w 0))) := by
          rw [RR_eq_re_mul_add_im_mul, Real.sin_sub, Complex.mul_re, Complex.mul_im, Complex.I_re,
            Complex.I_im, ← Complex.norm_mul_cos_arg (w 0), ← Complex.norm_mul_sin_arg (w 0),
            ← Complex.norm_mul_cos_arg (w 1), ← Complex.norm_mul_sin_arg (w 1)]
          ring
        have hpos : 0 < ‖w 0‖ * ‖w 1‖ := mul_pos (norm_pos_iff.2 hw0) (norm_pos_iff.2 hw1)
        rw [e, neg_eq_zero] at hRR
        exact (mul_eq_zero.1 hRR).resolve_left hpos.ne'
      set x := arg (w 1) - arg (w 0)
      have hcos : (Real.cos x - 1) * (Real.cos x + 1) = 0 := by
        have := Real.sin_sq_add_cos_sq x
        rw [hsin] at this
        linear_combination this
      rcases mul_eq_zero.1 hcos with h | h
      · refine ⟨0, Or.inl rfl, fun _ ↦ Complex.ext ?_ ?_⟩
        · rw [Complex.exp_ofReal_mul_I_re]; simp; linarith
        · rw [Complex.exp_ofReal_mul_I_im]; simp [hsin]
      · refine ⟨π, Or.inr rfl, fun _ ↦ Complex.ext ?_ ?_⟩
        · rw [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_re, Real.cos_pi]; linarith
        · rw [Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_im, Real.sin_pi, hsin]
    have hsψ : Real.sin ψ = 0 := by rcases hψ with rfl | rfl <;> simp
    refine ⟨k, ![‖w 1‖, ψ, θ'], ⟨by simp [hn1], by simpa using hψ, by simpa using hθ',
      fun h ↦ absurd (norm_eq_zero.1 (by simpa using h)) hw1⟩, ?_⟩
    funext j
    fin_cases j
    · simp only [cellPoint, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.cons_val_one,
        Matrix.tail_cons, Matrix.head_cons, Fin.zero_eta, Pi.smul_apply, smul_eq_mul]
      rw [hr1]
      by_cases hw0 : w 0 = 0
      · rw [hw0]; simp
      have e1 : Complex.exp (((θ' - ψ : ℝ) : ℂ) * I) =
          Complex.exp ((θ' : ℂ) * I) * Complex.exp (((-ψ : ℝ) : ℂ) * I) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      have e2 : Complex.exp ((arg (w 1) : ℂ) * I) = Complex.exp
          (((arg (w 1) - arg (w 0) : ℝ) : ℂ) * I) * Complex.exp ((arg (w 0) : ℂ) * I) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      have e3 : Complex.exp ((ψ : ℂ) * I) * Complex.exp (((-ψ : ℝ) : ℂ) * I) = 1 := by
        rw [← Complex.exp_add]; push_cast; simp
      rw [e1, he, e2, hψe hw0]
      conv_rhs => rw [hw0']
      linear_combination ((‖w 0‖ : ℂ) * ζ ^ k * Complex.exp ((arg (w 0) : ℂ) * I)) * e3
    · simp only [cellPoint, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.cons_val_one,
        Matrix.tail_cons, Matrix.head_cons, Fin.mk_one, Pi.smul_apply, smul_eq_mul]
      rw [he]
      conv_rhs => rw [hw1']
      ring
    · simp only [cellPoint, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.cons_val_one,
        Matrix.tail_cons, Matrix.head_cons, Pi.smul_apply, smul_eq_mul, hsψ]
      simp only [mul_zero, Complex.ofReal_zero]
      exact (mul_eq_zero_of_right _ h2).symm

/-- The first control on the closed 2-cell `𝒞₂(ζ, 1, 1)` with `θ₂ ∈ (π/3, π]` (and `ψ = 0` on
`r₂ = 0`) is `ζ`: `χ_A = t (r₂ K/2 + …)`, `K = sin θ₂ - √3 cos θ₂ = 2 sin(θ₂ - π/3) > 0`
(`χ_A = t² (K/4 - t/12)` on `r₂ = 0`), and `χ_B = t (r₂ sin θ₂ + …) ≥ 0` near `0`
(`χ_B = t³/12` at `θ₂ = π`). -/
private lemma l5b_isFirstControl_frontBack {q : Fin 3 → ℝ} (h0 : q 0 ∈ Icc 0 1)
    (h1 : q 1 = 0 ∨ q 1 = π) (h2 : q 2 ∈ Ioc (π / 3) π) (h01 : q 0 = 0 → q 1 = 0) :
    IsFirstControl (cellPoint q) ζ := by
  obtain ⟨hA, hB, -, -⟩ := l5b_chi_cellPoint q
  have hsψ : Real.sin (q 1) = 0 := by rcases h1 with h | h <;> rw [h] <;> simp
  have hs1 : Real.sin (q 2 - q 1) = Real.cos (q 1) * Real.sin (q 2) := by
    rw [Real.sin_sub, hsψ]; ring
  have hc1 : Real.cos (q 2 - q 1) = Real.cos (q 1) * Real.cos (q 2) := by
    rw [Real.cos_sub, hsψ]; ring
  have hK : 0 < Real.sin (q 2) - √3 * Real.cos (q 2) := by
    have e : Real.sin (q 2 - π / 3) = (Real.sin (q 2) - √3 * Real.cos (q 2)) / 2 := by
      rw [Real.sin_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]; ring
    have : 0 < Real.sin (q 2 - π / 3) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [h2.1]) (by linarith [h2.2, Real.pi_pos])
    linarith
  have hs2 : 0 ≤ Real.sin (q 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [h2.1, Real.pi_pos]) h2.2
  simp only [hs1, hc1, hsψ] at hA hB
  -- `χ_A ≥ 0` near `0`
  obtain ⟨ε₁, hε₁, hA'⟩ : ∃ ε > 0, ∀ t ∈ Icc 0 ε, 0 ≤ (chiA ζ (cellPoint q)).toPoly.eval t := by
    apply l5b_nonneg_near_zero
    rw [hA]
    dsimp only
    rcases h0.1.eq_or_lt with hq0 | hq0
    · have hψ := h01 hq0.symm
      rw [hψ, Real.cos_zero, ← hq0]
      refine Or.inr (Or.inr (Or.inl ⟨by ring, by ring, ?_⟩))
      nlinarith
    · exact Or.inr (Or.inl ⟨by ring, by have := mul_pos hq0 hK; linarith⟩)
  -- `χ_B ≥ 0` near `0`
  obtain ⟨ε₂, hε₂, hB'⟩ : ∃ ε > 0, ∀ t ∈ Icc 0 ε, 0 ≤ (chiB ζ (cellPoint q)).toPoly.eval t := by
    apply l5b_nonneg_near_zero
    rw [hB]
    dsimp only
    rcases hs2.lt_or_eq with hs | hs
    · rcases h0.1.eq_or_lt with hq0 | hq0
      · have hψ := h01 hq0.symm
        rw [hψ, Real.cos_zero, ← hq0]
        exact Or.inr (Or.inr (Or.inl ⟨rfl, by ring, by linarith⟩))
      · exact Or.inr (Or.inl ⟨rfl, mul_pos hq0 hs⟩)
    · rw [← hs]
      exact Or.inr (Or.inr (Or.inr ⟨rfl, by ring, by ring, by norm_num⟩))
  exact l5b_isFirstControl_of (Or.inl rfl) (lt_min hε₁ hε₂) fun t ht ↦
    ⟨hA' t ⟨ht.1, ht.2.trans (min_le_left _ _)⟩, hB' t ⟨ht.1, ht.2.trans (min_le_right _ _)⟩⟩

/-- On the front and back faces (`sin ψ = 0`, so `z₃ = 0`), changing `θ₂` by `α` is the rotation by
`e^{iα}`. -/
private lemma l5b_cellPoint_rotate {p : Fin 3 → ℝ} (hψ : Real.sin (p 1) = 0) (α θ : ℝ)
    (hθ : θ = p 2 + α) :
    cellPoint ![p 0, p 1, θ] = Complex.exp ((α : ℂ) * I) • cellPoint p := by
  subst hθ
  funext j
  fin_cases j
  · simp only [cellPoint, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.cons_val_one,
      Matrix.tail_cons, Matrix.head_cons, Fin.zero_eta, Pi.smul_apply, smul_eq_mul]
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  · simp only [cellPoint, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.cons_val_one,
      Matrix.tail_cons, Matrix.head_cons, Fin.mk_one, Pi.smul_apply, smul_eq_mul]
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  · simp only [cellPoint, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.cons_val_one,
      Matrix.tail_cons, Matrix.head_cons, Pi.smul_apply, smul_eq_mul, hψ]
    simp

/-- `e^{iα} = ζ^k` when `α ≡ 2πk/3 (mod 2π)`. -/
private lemma l5b_exp_eq_of {α : ℝ} {k : ℕ} {n : ℤ} (h : α = 2 * π * k / 3 + n * (2 * π)) :
    Complex.exp ((α : ℂ) * I) = ζ ^ k := by
  rw [← l5b_exp_eq_ζ_pow]
  apply Complex.exp_eq_exp_iff_exists_int.2
  exact ⟨n, by rw [h]; push_cast; ring⟩


/-- "In the remaining region, `z₃ = 0` (and `m_A > 0`). By (15.1.1), we have `r₂ ∈ {0, 1}`, or
`sin ψ = 0`. Each angle `θ₂` is `V_T`-equivalent to a unique angle `θ₂ ∈ (π/3, π]`" (TeX
12254–12258): every point of the closed cells with `z₃ = 0` is equivalent to a point of the closed
2-cell `𝒞₂(ζ, 1, 1)`. On its relative interior (`r₂ > 0`, `θ₂ ∈ (π/3, π)`) the first control is `ζ`
and `(m_A, m_B) = (1, 1)` (`χ_A = t (r₂ sin(θ₂ - π/3) + …)`, `χ_B = t (r₂ sin θ₂ + …)`).

Proof route: the rotation by `ζ` adds `2π/3` to `θ₁` and `θ₂` and fixes `ψ` and `z₃ = 0`; on
`r₂ = 0` the point `(e^{iθ₁}, 0, 0)` is represented with `ψ = 0`, `θ₂ = θ₁`; the first control
maximizes `RR(z₂, ·)` (the lexicographic rule of Lemma 13.2.6, `RR(z₃, ·) = 0`). -/
theorem frontBackOne_cover_and_switching :
    (∀ p ∈ cellDomain, cellPoint p 2 = 0 → ∃ q ∈ frontBackOne, cellClass q = cellClass p) ∧
      ∀ p ∈ frontBackOne, 0 < p 0 → p 2 ∈ Ioo (π / 3) π →
        firstControl (cellPoint p) = ζ ∧ multA ζ (cellPoint p) = 1 ∧
          multB ζ (cellPoint p) = 1 := by
  refine ⟨fun p hp h2 ↦ ?_, fun p hp hr hθ ↦ ?_⟩
  · -- `|z₁| + |z₂| = 1`, `z₃ = 0` and `RR(z₁, i z₂) = -r₁ r₂ sin ψ = x₃/2 = 0`
    have hn : ‖cellPoint p 0‖ + ‖cellPoint p 1‖ = 1 := by
      simp only [cellPoint, Matrix.cons_val_zero, Matrix.cons_val_one, norm_mul,
        Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (by linarith [hp.1.2]), abs_of_nonneg hp.1.1]
      ring
    have hRR : RR (cellPoint p 0) (cellPoint p 1 * I) = 0 := by
      rw [l5b_RR_cellPoint]
      have := congrArg Complex.re h2
      rw [(l5b_cellPoint_apply p).2.2.2.2.1, Complex.zero_re] at this
      linarith
    obtain ⟨k, q, ⟨hq0, hq1, hq2, -⟩, hq⟩ := l5b_rep_z3_zero h2 hn hRR
    refine ⟨q, ⟨hq0, hq1, Ioc_subset_Icc_self hq2⟩, ?_⟩
    have := classOf_smul_scale (l5b_ζ_pow_mem_VT k) one_pos (cellPoint_mem_sectionZero hp)
    rw [scale_one, ← hq] at this
    exact this
  · have hz := l5b_cellPoint_ne_zero p
    have hfc := l5b_isFirstControl_frontBack hp.1 hp.2.1 (Ioo_subset_Ioc_self hθ)
      (fun h ↦ absurd h hr.ne')
    obtain ⟨hA, hB, -, -⟩ := l5b_chi_cellPoint p
    have hsψ : Real.sin (p 1) = 0 := by rcases hp.2.1 with h | h <;> rw [h] <;> simp
    have hK : 0 < Real.sin (p 2) - √3 * Real.cos (p 2) := by
      have e : Real.sin (p 2 - π / 3) = (Real.sin (p 2) - √3 * Real.cos (p 2)) / 2 := by
        rw [Real.sin_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]; ring
      have : 0 < Real.sin (p 2 - π / 3) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
      linarith
    have hs2 : 0 < Real.sin (p 2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos]) hθ.2
    refine ⟨(firstControl_eq_iff hz).2 hfc, ?_, ?_⟩
    · exact (l5b_mult_cubic _ (by rw [hA]; norm_num)).2.1 (by rw [hA, hsψ]; dsimp only; ring)
        (by rw [hA]; dsimp only; have := mul_pos hr hK; positivity)
    · exact (l5b_mult_cubic _ (by rw [hB]; norm_num)).2.1 (by rw [hB])
        (by rw [hB]; dsimp only; exact (mul_pos hr hs2).ne')

/-! ### The cell `𝒞₂(ζ², 0, 2)` and the root-based maps `F_A`, `F_B` -/

/-- The data of the cell `𝒞₂(ζ², 0, 2)` (`θ₂ = 0`): `r₁, r₂, sin ψ > 0`, `y₁ = -r₁ sin ψ`,
`χ_A = t³/12 + r₁ (S - √3 C) t²/4 - (√3/2) r₂ t + √3 r₁ r₂ S`, `χ_B = -t³/12 + r₁ S t²/2`
(`S = sin ψ`, `C = cos ψ`), `(m_A, m_B) = (0, 2)` and the discriminant `Δ_{A,0}`. -/
private lemma l5b_topFaceTwo_data {p : Fin 3 → ℝ} (hp : p ∈ topFaceTwo) :
    0 < 1 - p 0 ∧ 0 < p 0 ∧ 0 < Real.sin (p 1) ∧
    (cellPoint p 0).im = -((1 - p 0) * Real.sin (p 1)) ∧
    chiA (ζ ^ 2) (cellPoint p) = ⟨1 / 12, (1 - p 0) * (Real.sin (p 1) - √3 * Real.cos (p 1)) / 4,
      -(√3 * p 0) / 2, √3 * (1 - p 0) * p 0 * Real.sin (p 1)⟩ ∧
    chiB (ζ ^ 2) (cellPoint p) = ⟨-1 / 12, (1 - p 0) * Real.sin (p 1) / 2, 0, 0⟩ ∧
    multA (ζ ^ 2) (cellPoint p) = 0 ∧ multB (ζ ^ 2) (cellPoint p) = 2 ∧
    discrA (ζ ^ 2) (cellPoint p) =
      ((1 - p 0) * (Real.sin (p 1) - √3 * Real.cos (p 1)) / 4) ^ 2 * (-(√3 * p 0) / 2) ^ 2 -
        4 * (1 / 12) * (-(√3 * p 0) / 2) ^ 3 -
        4 * ((1 - p 0) * (Real.sin (p 1) - √3 * Real.cos (p 1)) / 4) ^ 3 *
          (√3 * (1 - p 0) * p 0 * Real.sin (p 1)) -
        27 * (1 / 12) ^ 2 * (√3 * (1 - p 0) * p 0 * Real.sin (p 1)) ^ 2 +
        18 * (1 / 12) * ((1 - p 0) * (Real.sin (p 1) - √3 * Real.cos (p 1)) / 4) *
          (-(√3 * p 0) / 2) * (√3 * (1 - p 0) * p 0 * Real.sin (p 1)) := by
  obtain ⟨⟨h0, h0'⟩, ⟨h1, h1'⟩, h2⟩ := hp
  obtain ⟨-, -, hA, hB⟩ := l5b_chi_cellPoint p
  have him := (l5b_cellPoint_apply p).2.1
  simp only [h2, zero_sub, Real.sin_neg, Real.cos_neg, Real.sin_zero, Real.cos_zero] at hA hB him
  have hr : 0 < 1 - p 0 := by linarith
  have hS : 0 < Real.sin (p 1) := Real.sin_pos_of_pos_of_lt_pi h1 h1'
  have hA' : chiA (ζ ^ 2) (cellPoint p) = ⟨1 / 12,
      (1 - p 0) * (Real.sin (p 1) - √3 * Real.cos (p 1)) / 4, -(√3 * p 0) / 2,
      √3 * (1 - p 0) * p 0 * Real.sin (p 1)⟩ := by
    rw [hA]; exact Cubic.ext rfl (by ring) (by ring) rfl
  have hB' : chiB (ζ ^ 2) (cellPoint p) = ⟨-1 / 12, (1 - p 0) * Real.sin (p 1) / 2, 0, 0⟩ := by
    rw [hB]; exact Cubic.ext rfl (by ring) (by ring) rfl
  have hd : 0 < √3 * (1 - p 0) * p 0 * Real.sin (p 1) :=
    mul_pos (mul_pos (mul_pos l5b_sqrt3_pos hr) h0) hS
  have hmA : multA (ζ ^ 2) (cellPoint p) = 0 :=
    (l5b_mult_cubic _ (by rw [hA']; norm_num)).1 (by rw [hA']; exact hd.ne')
  have hmB : multB (ζ ^ 2) (cellPoint p) = 2 :=
    (l5b_mult_cubic _ (by rw [hB']; norm_num)).2.2.1 (by rw [hB']) (by rw [hB'])
      (by rw [hB']; dsimp only; exact (div_pos (mul_pos hr hS) two_pos).ne')
  refine ⟨hr, h0, hS, by rw [him]; ring, hA', hB', hmA, hmB, ?_⟩
  rw [discrA, chiARed, hmA, pow_zero, divByMonic_one,
    Cubic.discr_toPoly _ (by rw [hA']; norm_num), hA', Cubic.discr]

/-- The bracket of `P'(t) = a [(t - r₁)(t - r₂) + (t - r₀)(t - r₂) + (t - r₀)(t - r₁)]` is negative
on `[0, r₁)` when `r₀ < 0 < r₁ ≤ r₂` and `r₀ r₁ + r₀ r₂ + r₁ r₂ < 0` (that is, `P'(0) < 0`):
`1/(t - r₀) ≤ 1/(-r₀) < 1/r₁ + 1/r₂ ≤ 1/(r₁ - t) + 1/(r₂ - t)`. -/
private lemma l5b_deriv_neg {r₀ r₁ r₂ t : ℝ} (h₀ : r₀ < 0) (h₁ : 0 < r₁) (h₁₂ : r₁ ≤ r₂)
    (hσ : r₀ * r₁ + r₀ * r₂ + r₁ * r₂ < 0) (ht : 0 ≤ t) (ht₁ : t < r₁) :
    (t - r₁) * (t - r₂) + (t - r₀) * (t - r₂) + (t - r₀) * (t - r₁) < 0 := by
  set A := r₁ - t
  set B := r₂ - t
  set R := -r₀
  have hA : 0 < A := by simp only [A]; linarith
  have hB : 0 < B := by simp only [B]; linarith
  have hR : 0 < R := by simp only [R]; linarith
  have hr₂ : 0 < r₂ := h₁.trans_le h₁₂
  have key : r₁ * r₂ * (R * (A + B) - A * B) =
      A * B * (-(r₀ * r₁ + r₀ * r₂ + r₁ * r₂)) + R * t * (r₁ * A + r₂ * B) := by
    simp only [A, B, R]; ring
  have h1 : 0 < A * B * (-(r₀ * r₁ + r₀ * r₂ + r₁ * r₂)) := mul_pos (mul_pos hA hB) (by linarith)
  have h2 : 0 ≤ R * t * (r₁ * A + r₂ * B) := by positivity
  have h3 : 0 < R * (A + B) - A * B := by
    have : 0 < r₁ * r₂ * (R * (A + B) - A * B) := by rw [key]; linarith
    exact pos_of_mul_pos_right this (mul_pos h₁ hr₂).le
  have h4 : R * (A + B) ≤ (t - r₀) * (A + B) :=
    mul_le_mul_of_nonneg_right (by simp only [R]; linarith) (by linarith)
  have e : (t - r₁) * (t - r₂) + (t - r₀) * (t - r₂) + (t - r₀) * (t - r₁) =
      A * B - (t - r₀) * (A + B) := by simp only [A, B]; ring
  rw [e]
  linarith

/-- **The cell `𝒞₂(ζ², 0, 2)`** (TeX 12235–12238, 12411–12419): the first control is `ζ²`,
`(m_A, m_B) = (0, 2)`, `χ_{B,2} = -(t/12 + y₁/2)` has the unique root `t_B = -6 y₁ > 0`; "On one
part `𝒞₂^A`, we have `Δ_{A,0} ≥ 0`. By Descartes's rule of signs, `χ_{A,0}` has two positive roots
(counted with algebraic multiplicity). … On the interior of the part `𝒞₂^B`, we have `Δ_{A,0} < 0`.
In this case, `χ_{A,0}` has no positive root."

Proof route: `θ₂ = 0` gives `y₂ = 0`, `y₁ = -r₁ sin ψ < 0` (the tie is broken towards `ζ²`).
`χ_A` has coefficients `(1/12, ?, -(√3/2) r₂, -(√3/2) x₃)` (descending), so the product of the roots
is `< 0` and the sum of their pairwise products is `< 0`: with three real roots (`Δ ≥ 0`), exactly
one is negative and two are positive; with `Δ < 0`, the only real root is negative and
`χ_A > 0` on `[0, ∞)`. -/
theorem topFaceTwo_switching {p : Fin 3 → ℝ} (hp : p ∈ topFaceTwo) :
    firstControl (cellPoint p) = ζ ^ 2 ∧ multA (ζ ^ 2) (cellPoint p) = 0 ∧
      multB (ζ ^ 2) (cellPoint p) = 2 ∧ 0 < -6 * (cellPoint p 0).im ∧
      (chiBRed (ζ ^ 2) (cellPoint p)).roots = {-6 * (cellPoint p 0).im} ∧
      (0 ≤ discrA (ζ ^ 2) (cellPoint p) →
        ((chiA (ζ ^ 2) (cellPoint p)).toPoly.roots.filter (fun t ↦ 0 < t)).card = 2) ∧
      (discrA (ζ ^ 2) (cellPoint p) < 0 →
        ∀ t : ℝ, 0 ≤ t → 0 < (chiA (ζ ^ 2) (cellPoint p)).toPoly.eval t) := by
  obtain ⟨hr, h0, hS, him, hA, hB, hmA, hmB, hdisc⟩ := l5b_topFaceTwo_data hp
  have hd : 0 < √3 * (1 - p 0) * p 0 * Real.sin (p 1) :=
    mul_pos (mul_pos (mul_pos l5b_sqrt3_pos hr) h0) hS
  have hc : -(√3 * p 0) / 2 < 0 := by have := mul_pos l5b_sqrt3_pos h0; linarith
  have hBc : 0 < (1 - p 0) * Real.sin (p 1) / 2 := by positivity
  -- the first control: `χ_A(0) > 0` and `χ_B = t² (r₁ S/2 - t/12)`
  obtain ⟨ε₁, hε₁, hA'⟩ := l5b_nonneg_near_zero (chiA (ζ ^ 2) (cellPoint p))
    (Or.inl (by rw [hA]; exact hd))
  obtain ⟨ε₂, hε₂, hB'⟩ := l5b_nonneg_near_zero (chiB (ζ ^ 2) (cellPoint p))
    (Or.inr (Or.inr (Or.inl ⟨by rw [hB], by rw [hB], by rw [hB]; exact hBc⟩)))
  have hfc : IsFirstControl (cellPoint p) (ζ ^ 2) :=
    l5b_isFirstControl_of (Or.inr rfl) (lt_min hε₁ hε₂) fun t ht ↦
      ⟨hA' t ⟨ht.1, ht.2.trans (min_le_left _ _)⟩, hB' t ⟨ht.1, ht.2.trans (min_le_right _ _)⟩⟩
  refine ⟨(firstControl_eq_iff (l5b_cellPoint_ne_zero p)).2 hfc, hmA, hmB,
    by rw [him]; have := mul_pos hr hS; linarith, ?_, fun hD ↦ ?_, fun hD t ht ↦ ?_⟩
  · -- `χ_{B,2} = -(t/12 + y₁/2)` has the root `t_B = -6 y₁`
    have hpoly : (chiB (ζ ^ 2) (cellPoint p)).toPoly =
        X ^ 2 * (C (-1 / 12 : ℝ) * X + C ((1 - p 0) * Real.sin (p 1) / 2)) := by
      rw [hB]
      simp only [Cubic.toPoly, map_zero, zero_mul, add_zero]
      ring
    rw [chiBRed, hmB, hpoly, mul_divByMonic_cancel_left _ (monic_X_pow 2),
      roots_C_mul_X_add_C _ (by norm_num), him]
    congr 1
    ring
  · -- `Δ_{A,0} ≥ 0`: roots `r₀ < 0 < r₁ ≤ r₂`
    rw [hdisc] at hD
    obtain ⟨ρ₀, ρ₁, ρ₂, h₀, h₁, h₁₂, -, hb, hc', hd'⟩ :=
      exists_roots_cubic_of_discr_nonneg
        (b := (1 - p 0) * (Real.sin (p 1) - √3 * Real.cos (p 1)) / 4)
        (by norm_num) hc hd hD
    have hpoly : (chiA (ζ ^ 2) (cellPoint p)).toPoly =
        C (1 / 12 : ℝ) * (X - C ρ₀) * (X - C ρ₁) * (X - C ρ₂) := by
      rw [Cubic.C_mul_prod_X_sub_C_eq, hA, hb, hc', hd']
    rw [hpoly]
    exact Polynomial.card_roots_filter_pos_eq_two (by norm_num) h₀ h₁ h₁₂
  · -- `Δ_{A,0} < 0`: `χ_A > 0` on `[0, ∞)`
    rw [hdisc] at hD
    rw [l5b_eval, hA]
    exact (cubic_nonneg_of_discr_nonpos
      (b := (1 - p 0) * (Real.sin (p 1) - √3 * Real.cos (p 1)) / 4)
      (by norm_num) hc hd hD.le ht).2 hD

/-- The signs of `(1/12)(t - r₀)(t - r₁)(t - r₂)` for `r₀ < 0`, `r₁ ≤ r₂` and `t ≥ 0`: positive on
`[0, r₁)`, negative on `(r₁, r₂)`. -/
private lemma l5b_sign3 {r₀ r₁ r₂ t : ℝ} (h₀ : r₀ < 0) (h₁₂ : r₁ ≤ r₂) (ht : 0 ≤ t) :
    (t < r₁ → 0 < 1 / 12 * ((t - r₀) * ((t - r₁) * (t - r₂)))) ∧
      (r₁ < t → t < r₂ → 1 / 12 * ((t - r₀) * ((t - r₁) * (t - r₂))) < 0) := by
  have h' : 0 < t - r₀ := by linarith
  refine ⟨fun h ↦ ?_, fun h h₂ ↦ ?_⟩
  · exact mul_pos (by norm_num) (mul_pos h' (mul_pos_of_neg_of_neg (by linarith) (by linarith)))
  · exact mul_neg_of_pos_of_neg (by norm_num)
      (mul_neg_of_pos_of_neg h' (mul_neg_of_pos_of_neg (by linarith) (by linarith)))

/-- **The estimate `t₁ ≤ t_B` on `𝒞₂^A`** (module docstring; the book asserts that the first
switching time is a root of `χ_{A,0}`, TeX 12413–12415, without it): if
`χ_{A,0} = (1/12)(t - ρ₀)(t - ρ₁)(t - ρ₂)` with `ρ₀ < 0 < ρ₁ ≤ ρ₂`, then the least positive root
satisfies `ρ₁ ≤ t_B = 6 r₁ S` (`r₁ = 1 - r₂`, `S = sin ψ`, `C = cos ψ`). Otherwise
`χ_A(t_B) > 0` and `χ_A'(t_B) < 0` (`l5b_deriv_neg`); with `K = r₁² S` these read
`9√3 K S - 9 K C - 2 r₂ > 0` and `8√3 K S - 6 K C - r₂ < 0`, which force `7√3 S < 3 C` and
`C < √3 S`: a contradiction. -/
private lemma l5b_topFaceTwo_root_le {r₂ S Cψ ρ₀ ρ₁ ρ₂ : ℝ} (hr : 0 < 1 - r₂) (h0 : 0 < r₂)
    (hS : 0 < S) (h₀ : ρ₀ < 0) (h₁ : 0 < ρ₁) (h₁₂ : ρ₁ ≤ ρ₂)
    (hb : (1 - r₂) * (S - √3 * Cψ) / 4 = 1 / 12 * -(ρ₀ + ρ₁ + ρ₂))
    (hc : -(√3 * r₂) / 2 = 1 / 12 * (ρ₀ * ρ₁ + ρ₀ * ρ₂ + ρ₁ * ρ₂))
    (hd : √3 * (1 - r₂) * r₂ * S = 1 / 12 * -(ρ₀ * ρ₁ * ρ₂)) :
    ρ₁ ≤ 6 * ((1 - r₂) * S) := by
  set b := (1 - r₂) * (S - √3 * Cψ) / 4
  set tB := 6 * ((1 - r₂) * S) with htB
  have htB0 : 0 < tB := by positivity
  have h3 := l5b_sqrt3_pos
  by_contra hlt'
  push Not at hlt'
  have hfac : 1 / 12 * tB ^ 3 + b * tB ^ 2 + -(√3 * r₂) / 2 * tB + √3 * (1 - r₂) * r₂ * S =
      1 / 12 * ((tB - ρ₀) * ((tB - ρ₁) * (tB - ρ₂))) := by
    rw [hb, hc, hd]; ring
  -- `χ_A(t_B) > 0`
  have hf : 0 < 1 / 12 * tB ^ 3 + b * tB ^ 2 + -(√3 * r₂) / 2 * tB + √3 * (1 - r₂) * r₂ * S := by
    rw [hfac]; exact (l5b_sign3 h₀ h₁₂ htB0.le).1 hlt'
  -- `χ_A'(t_B) = (1/12)[(t - r₁)(t - r₂) + (t - r₀)(t - r₂) + (t - r₀)(t - r₁)] < 0`
  have hσ : ρ₀ * ρ₁ + ρ₀ * ρ₂ + ρ₁ * ρ₂ < 0 := by
    have : -(√3 * r₂) / 2 < 0 := by have := mul_pos h3 h0; linarith
    linarith
  have hf' := l5b_deriv_neg h₀ h₁ h₁₂ hσ htB0.le hlt'
  have e' : 3 * (1 / 12) * tB ^ 2 + 2 * b * tB + -(√3 * r₂) / 2 = 1 / 12 *
      ((tB - ρ₁) * (tB - ρ₂) + (tB - ρ₀) * (tB - ρ₂) + (tB - ρ₀) * (tB - ρ₁)) := by
    rw [hb, hc]; ring
  -- in coordinates, with `K = r₁² S`
  set K := (1 - r₂) ^ 2 * S with hK
  have e1 : 1 / 12 * tB ^ 3 + b * tB ^ 2 + -(√3 * r₂) / 2 * tB + √3 * (1 - r₂) * r₂ * S =
      √3 * (1 - r₂) * S * (9 * (√3 * K * S) - 9 * (K * Cψ) - 2 * r₂) := by
    simp only [tB, b, K]
    linear_combination (-9 * (1 - r₂) ^ 3 * S ^ 3) * l5b_sqrt3_mul
  have e2 : 3 * (1 / 12) * tB ^ 2 + 2 * b * tB + -(√3 * r₂) / 2 =
      √3 / 2 * (8 * (√3 * K * S) - 6 * (K * Cψ) - r₂) := by
    simp only [tB, b, K]
    linear_combination (-4 * (1 - r₂) ^ 2 * S ^ 2) * l5b_sqrt3_mul
  have P1 : 0 < 9 * (√3 * K * S) - 9 * (K * Cψ) - 2 * r₂ := by
    rw [e1] at hf
    exact pos_of_mul_pos_right hf (by positivity)
  have P2 : 8 * (√3 * K * S) - 6 * (K * Cψ) - r₂ < 0 := by
    have : √3 / 2 * (8 * (√3 * K * S) - 6 * (K * Cψ) - r₂) < 0 := by
      rw [← e2, e']; linarith
    exact neg_of_mul_neg_right this (by positivity)
  have hU : 0 < √3 * K * S := by positivity
  linarith

/-- **The first switching time on `𝒞₂(ζ², 0, 2)`** (TeX 12413–12418): on `{Δ_{A,0} > 0}` "the first
switching time is a root of `χ_{A,0}`", the least positive one, and `F = F_A`; on `𝒞₂^B` it "is the
unique root of the linear polynomial `χ_{B,2}`" and `F = F_B`. The second case includes the
discriminant locus `Δ_{A,0} = 0`: there the double positive root of `χ_{A,0}` is a tangency, not a
switch, so `poincare = F_B` while the book's extension `F_A` uses the double root (see the module
docstring).

Proof route: if `Δ_{A,0} ≤ 0`, `χ_A ≥ 0` on `[0, ∞)` (`topFaceTwo_switching`; a double root is a
local minimum), so `ζ²` is first beaten by `ζ`, at the sign change `t_B` of `χ_B = t² χ_{B,2}`. If
`Δ_{A,0} > 0`, the least positive root `t₁` of `χ_{A,0}` is simple and `t₁ ≤ t_B` (the computation
in the module docstring), so `ζ²` is first beaten by `1` at `t₁`. -/
theorem firstSwitchTime_topFaceTwo {p : Fin 3 → ℝ} (hp : p ∈ topFaceTwo) :
    (discrA (ζ ^ 2) (cellPoint p) ≤ 0 →
      firstSwitchTime (cellPoint p) = -6 * (cellPoint p 0).im ∧
        poincare (cellPoint p) = cellMapB (cellPoint p)) ∧
      (0 < discrA (ζ ^ 2) (cellPoint p) →
        firstSwitchTime (cellPoint p) = leastPosRoot (chiA (ζ ^ 2) (cellPoint p)).toPoly ∧
          poincare (cellPoint p) = cellMapA (cellPoint p)) := by
  obtain ⟨hr, h0, hS, him, hA, hB, -, -, hdisc⟩ := l5b_topFaceTwo_data hp
  set z := cellPoint p
  set S := Real.sin (p 1)
  set Cψ := Real.cos (p 1)
  set b := (1 - p 0) * (S - √3 * Cψ) / 4
  have h3 := l5b_sqrt3_pos
  have hz := l5b_cellPoint_ne_zero p
  have hd : 0 < √3 * (1 - p 0) * p 0 * S := mul_pos (mul_pos (mul_pos h3 hr) h0) hS
  have hc : -(√3 * p 0) / 2 < 0 := by have := mul_pos h3 h0; linarith
  have hfc0 := (topFaceTwo_switching hp).1
  have hfc : IsFirstControl z (ζ ^ 2) := (firstControl_eq_iff hz).1 hfc0
  have hsw := l5b_firstSwitchTime_eq (Or.inr rfl) hz hfc
  have hevalA : ∀ t, (chiA (ζ ^ 2) z).toPoly.eval t =
      1 / 12 * t ^ 3 + b * t ^ 2 + -(√3 * p 0) / 2 * t + √3 * (1 - p 0) * p 0 * S :=
    fun t ↦ by rw [l5b_eval, hA]
  have hevalB : ∀ t, (chiB (ζ ^ 2) z).toPoly.eval t =
      t ^ 2 * ((1 - p 0) * S / 2 - t / 12) := fun t ↦ by rw [l5b_eval, hB]; ring
  set tB := 6 * ((1 - p 0) * S) with htB
  have htB0 : 0 < tB := by positivity
  have htBim : -6 * (z 0).im = tB := by rw [him]; ring
  -- `χ_B(t) < 0` exactly for `t > t_B`, and `χ_B ≥ 0` on `[0, t_B]`
  have hBneg : ∀ t, 0 < t → ((chiB (ζ ^ 2) z).toPoly.eval t < 0 ↔ tB < t) := by
    intro t ht
    rw [hevalB]
    constructor
    · intro h
      by_contra hle
      push Not at hle
      have : 0 ≤ (1 - p 0) * S / 2 - t / 12 := by simp only [tB] at hle; linarith
      linarith [mul_nonneg (sq_nonneg t) this]
    · intro h
      have : (1 - p 0) * S / 2 - t / 12 < 0 := by simp only [tB] at h; linarith
      exact mul_neg_of_pos_of_neg (by positivity) this
  constructor
  · -- `Δ_{A,0} ≤ 0`: `χ_A ≥ 0` on `[0, ∞)`, the switch is at `t_B`
    intro hD
    rw [hdisc] at hD
    have hAnn : ∀ t, 0 ≤ t → 0 ≤ (chiA (ζ ^ 2) z).toPoly.eval t := fun t ht ↦ by
      rw [hevalA]; exact (cubic_nonneg_of_discr_nonpos (b := b) (by norm_num) hc hd hD ht).1
    have hset : {t | 0 < t ∧ ((chiA (ζ ^ 2) z).toPoly.eval t < 0 ∨
        (chiB (ζ ^ 2) z).toPoly.eval t < 0)} = Ioi tB := by
      ext t
      simp only [mem_ofPred_eq, mem_Ioi]
      constructor
      · rintro ⟨ht, h | h⟩
        · linarith [hAnn t ht.le]
        · exact (hBneg t ht).1 h
      · intro ht
        exact ⟨htB0.trans ht, Or.inr ((hBneg t (htB0.trans ht)).2 ht)⟩
    have h1 : firstSwitchTime z = -6 * (z 0).im := by rw [hsw, hset, csInf_Ioi, htBim]
    exact ⟨h1, by rw [poincare, h1, hfc0]; rfl⟩
  · -- `Δ_{A,0} > 0`: the least positive root `r₁` of `χ_{A,0}` is simple and `r₁ ≤ t_B`
    intro hD
    rw [hdisc] at hD
    obtain ⟨ρ₀, ρ₁, ρ₂, h₀, h₁, h₁₂, hlt, hb, hc', hd'⟩ :=
      exists_roots_cubic_of_discr_nonneg (b := b) (by norm_num) hc hd hD.le
    have hρ : ρ₁ < ρ₂ := hlt hD
    have hfac : ∀ t, (chiA (ζ ^ 2) z).toPoly.eval t =
        1 / 12 * ((t - ρ₀) * ((t - ρ₁) * (t - ρ₂))) := by
      intro t; rw [hevalA, hb, hc', hd']; ring
    have hle : ρ₁ ≤ tB := l5b_topFaceTwo_root_le hr h0 hS h₀ h₁ h₁₂ hb hc' hd'
    -- the least positive root
    have hroot : leastPosRoot (chiA (ζ ^ 2) z).toPoly = ρ₁ := by
      apply IsLeast.csInf_eq
      refine ⟨⟨h₁, by rw [hfac]; ring⟩, fun t ⟨ht, hft⟩ ↦ ?_⟩
      rw [hfac] at hft
      by_contra hlt'
      push Not at hlt'
      linarith [(l5b_sign3 h₀ h₁₂ ht.le).1 hlt']
    -- the first switching time
    have h1 : firstSwitchTime z = ρ₁ := by
      rw [hsw]
      apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
      · refine ⟨(ρ₁ + ρ₂) / 2, by linarith, Or.inl ?_⟩
        rw [hfac]
        exact (l5b_sign3 h₀ h₁₂ (by linarith)).2 (by linarith) (by linarith)
      · rintro t ⟨ht, h | h⟩
        · by_contra hlt'
          push Not at hlt'
          rw [hfac] at h
          linarith [(l5b_sign3 h₀ h₁₂ ht.le).1 hlt']
        · have := (hBneg t ht).1 h
          linarith
      · intro w hw
        have hm1 : ρ₁ < min w ρ₂ := lt_min hw hρ
        have hm2 := min_le_left w ρ₂
        have hm3 := min_le_right w ρ₂
        refine ⟨(ρ₁ + min w ρ₂) / 2, ⟨by linarith, Or.inl ?_⟩, by linarith⟩
        rw [hfac]
        exact (l5b_sign3 h₀ h₁₂ (by linarith)).2 (by linarith) (by linarith)
    refine ⟨h1.trans hroot.symm, ?_⟩
    rw [poincare, h1, hfc0, cellMapA, hroot]

/-- **The least positive root of `χ_{A,0}` on `𝒞₂(ζ², 0, 2)` is at most `t_B = -6 y₁`** (the
computation in the module docstring): if `χ_{A,0}` has a positive root, then `Δ_{A,0} ≥ 0`
(`topFaceTwo_switching`), so `χ_{A,0} = (1/12)(t - ρ₀)(t - ρ₁)(t - ρ₂)` with `ρ₀ < 0 < ρ₁ ≤ ρ₂`,
the least positive root is `ρ₁`, and `ρ₁ ≤ t_B` (`l5b_topFaceTwo_root_le`: otherwise
`χ_A(t_B) > 0` and `χ_A'(t_B) < 0`, which are incompatible). -/
theorem leastPosRoot_chiA_le_of_mem_topFaceTwo {p : Fin 3 → ℝ} (hp : p ∈ topFaceTwo)
    (hne : ∃ t, 0 < t ∧ (chiA (ζ ^ 2) (cellPoint p)).toPoly.eval t = 0) :
    leastPosRoot (chiA (ζ ^ 2) (cellPoint p)).toPoly ≤ -6 * (cellPoint p 0).im := by
  obtain ⟨hr, h0, hS, him, hA, -, -, -, hdisc⟩ := l5b_topFaceTwo_data hp
  set b := (1 - p 0) * (Real.sin (p 1) - √3 * Real.cos (p 1)) / 4
  have hd : 0 < √3 * (1 - p 0) * p 0 * Real.sin (p 1) :=
    mul_pos (mul_pos (mul_pos l5b_sqrt3_pos hr) h0) hS
  have hc : -(√3 * p 0) / 2 < 0 := by have := mul_pos l5b_sqrt3_pos h0; linarith
  -- a positive root forces `Δ_{A,0} ≥ 0`
  have hD : 0 ≤ discrA (ζ ^ 2) (cellPoint p) := by
    by_contra hD
    obtain ⟨t, ht, hroot⟩ := hne
    exact ((topFaceTwo_switching hp).2.2.2.2.2.2 (not_le.1 hD) t ht.le).ne' hroot
  rw [hdisc] at hD
  obtain ⟨ρ₀, ρ₁, ρ₂, h₀, h₁, h₁₂, -, hb, hc', hd'⟩ :=
    exists_roots_cubic_of_discr_nonneg (b := b) (by norm_num) hc hd hD
  have hevalA : ∀ t, (chiA (ζ ^ 2) (cellPoint p)).toPoly.eval t =
      1 / 12 * t ^ 3 + b * t ^ 2 + -(√3 * p 0) / 2 * t + √3 * (1 - p 0) * p 0 * Real.sin (p 1) :=
    fun t ↦ by rw [l5b_eval, hA]
  have hfac : ∀ t, (chiA (ζ ^ 2) (cellPoint p)).toPoly.eval t =
      1 / 12 * ((t - ρ₀) * ((t - ρ₁) * (t - ρ₂))) := by
    intro t; rw [hevalA, hb, hc', hd']; ring
  -- the least positive root is `ρ₁`
  have hroot : leastPosRoot (chiA (ζ ^ 2) (cellPoint p)).toPoly = ρ₁ := by
    apply IsLeast.csInf_eq
    refine ⟨⟨h₁, by rw [hfac]; ring⟩, fun t ⟨ht, hft⟩ ↦ ?_⟩
    rw [hfac] at hft
    by_contra hlt'
    push Not at hlt'
    linarith [(l5b_sign3 h₀ h₁₂ ht.le).1 hlt']
  have := l5b_topFaceTwo_root_le hr h0 hS h₀ h₁ h₁₂ hb hc' hd'
  rw [hroot, him]
  linarith

/-! ### Helpers for Proposition 15.2.2 and the boundary maps -/

/-- Changing `θ₂` by `2π` does not change the cell point. -/
private lemma l5b_cellPoint_add_two_pi (p : Fin 3 → ℝ) (θ : ℝ) (hθ : θ = p 2 + 2 * π) :
    cellPoint ![p 0, p 1, θ] = cellPoint p := by
  funext j
  fin_cases j
  · simp only [cellPoint, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.cons_val_one,
      Matrix.tail_cons, Matrix.head_cons, Fin.zero_eta]
    congr 1
    exact Complex.exp_eq_exp_iff_exists_int.2 ⟨1, by rw [hθ]; push_cast; ring⟩
  · simp only [cellPoint, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.cons_val_one,
      Matrix.tail_cons, Matrix.head_cons, Fin.mk_one]
    congr 1
    exact Complex.exp_eq_exp_iff_exists_int.2 ⟨1, by rw [hθ]; push_cast; ring⟩
  · simp only [cellPoint, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.cons_val_one,
      Matrix.tail_cons, Matrix.head_cons]
    rfl

/-- On `z₃ = 0` all controls give the same Hamiltonian: `H_F⁺(z) = RR(z₁, i z₂)`. -/
private lemma l5b_hamMax_of_z3_zero {w : Fin 3 → ℂ} (h2 : w 2 = 0) :
    hamMax w = RR (w 0) (w 1 * I) := by
  have : ∀ u, ham w u = RR (w 0) (w 1 * I) := fun u ↦ by
    rw [ham, h2, RR_eq_re_mul_add_im_mul u 0]; simp
  simp only [hamMax, this, max_self]

/-- **Semicontinuity at a face point where the cell's control is not the first control**
(the proof route of `proposition15_2_2`, part 3): the control `u` is beaten at times
arbitrarily close to `0` at `cellPoint p`; beating is a strict inequality between continuous
functions, so at nearby points of the open cell (first control `u`) `0 < t_sw ≤ ε`; then
`F(cellPoint q) = z(t_sw, cellPoint q, u) → cellPoint p`. -/
private lemma l5b_tendsto_of_not_isFirstControl {u : ℂ} (hu : u ∈ VT) {s : Set (Fin 3 → ℝ)}
    {p : Fin 3 → ℝ} (hs : ∀ q ∈ s, IsFirstControl (cellPoint q) u) (hsd : s ⊆ cellDomain)
    (hp : p ∈ cellDomain) (hnot : ¬ IsFirstControl (cellPoint p) u) :
    Tendsto (fun q ↦ firstSwitchTime (cellPoint q)) (𝓝[s] p) (𝓝 0) ∧
      Tendsto (fun q ↦ poincareAngZero (cellClass q)) (𝓝[s] p) (𝓝 (cellClass p)) := by
  have hfc : ∀ q ∈ s, firstControl (cellPoint q) = u :=
    fun q hq ↦ (firstControl_eq_iff (l5b_cellPoint_ne_zero q)).2 (hs q hq)
  have hbeat : ∀ ε > 0, ∃ t ∈ Icc 0 ε, ∃ v ∈ VT,
      ham (flow t (cellPoint p) u) u < ham (flow t (cellPoint p) u) v := by
    intro ε hε
    by_contra h
    push Not at h
    exact hnot ⟨hu, ε, hε, fun t ht v hv ↦ h t ht v hv⟩
  have h1 : Tendsto (fun q ↦ firstSwitchTime (cellPoint q)) (𝓝[s] p) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨t, ht, v, hv, hlt⟩ := hbeat (ε / 2) (half_pos hε)
    have hf : Continuous fun q : Fin 3 → ℝ ↦ flow t (cellPoint q) u :=
      (l5b_continuous_flow u).comp (continuous_const.prodMk l5b_continuous_cellPoint)
    have hcont : Continuous fun q : Fin 3 → ℝ ↦
        ham (flow t (cellPoint q) u) v - ham (flow t (cellPoint q) u) u :=
      ((l5b_continuous_ham v).comp hf).sub ((l5b_continuous_ham u).comp hf)
    have hev : ∀ᶠ q in 𝓝 p, 0 < ham (flow t (cellPoint q) u) v - ham (flow t (cellPoint q) u) u :=
      hcont.continuousAt.eventually (lt_mem_nhds (by linarith))
    filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with q hq hqs
    have hpos := firstSwitchTime_pos (l5b_cellPoint_ne_zero q)
    have hlt' : firstSwitchTime (cellPoint q) < t := by
      by_contra hle
      push Not at hle
      have := firstControl_maximizes (l5b_cellPoint_ne_zero q) t ⟨ht.1, hle⟩ v hv
      rw [hfc q hqs] at this
      linarith
    rw [Real.dist_eq, sub_zero, abs_of_pos hpos]
    linarith [ht.2]
  refine ⟨h1, ?_⟩
  have h2 : Tendsto (fun q ↦ poincare (cellPoint q)) (𝓝[s] p) (𝓝 (cellPoint p)) := by
    have hflow : Tendsto (fun q ↦ flow (firstSwitchTime (cellPoint q)) (cellPoint q) u) (𝓝[s] p)
        (𝓝 (flow 0 (cellPoint p) u)) :=
      ((l5b_continuous_flow u).tendsto _).comp (h1.prodMk_nhds
        (l5b_continuous_cellPoint.continuousAt.tendsto.mono_left nhdsWithin_le_nhds))
    rw [flow_zero] at hflow
    refine hflow.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with q hq
    rw [poincare, hfc q hq]
  have h3 : Tendsto (fun q ↦ poincare (cellPoint q)) (𝓝[s] p) (𝓝[sectionZero] (cellPoint p)) :=
    tendsto_nhdsWithin_iff.2 ⟨h2, eventually_nhdsWithin_of_forall fun q hq ↦
      poincare_mem_sectionZero (cellPoint_mem_sectionZero (hsd hq))⟩
  have h4 := (continuousOn_classOf _ (cellPoint_mem_sectionZero hp)).tendsto.comp h3
  refine h4.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with q hq
  simp only [Function.comp, cellClass]
  rw [poincareAngZero_classOf (cellPoint_mem_sectionZero (hsd hq))]

end TriFuller

open TriFuller

/-- **Remark 15.2.1** (`rem:two-cells`, label of this formalization; unlabelled, TeX 12287–12296):
"A symmetry of `V_T` carries the closed cell `𝒞₂(ζ, 1, 1)` to `𝒞₂(ζ², 1, 1)`, but we refrain from
identifying these two closed cells with each other." The
rotation by `ζ` maps `𝒞₂(ζ, 1, 1)` onto `𝒞₂(ζ², 1, 1)` (`θ₂ ↦ θ₂ + 2π/3 - 2π`, `ψ` and `z₃ = 0`
fixed), so corresponding points have the same class in `Ξ_{𝒲,0}/V_T`. (The rest of the remark,
"`F⁻¹(𝒞₂(ζ))` and `F⁻¹(𝒞₂(ζ²))` are the two sides of a hypersurface `∂_res` in the first big cell,
along which the Fuller–Poincaré map is discontinuous", is read off Figure 15.2 and is not
formalized: `Proposition15_3_2` does not contain it, and the proof of Theorem 16.1.1 does not use
it.) -/
theorem remark15_2_1 :
    ∀ p ∈ frontBackOne, ![p 0, p 1, p 2 - 4 * π / 3] ∈ frontBackTwo ∧
      ζ • cellPoint p = cellPoint ![p 0, p 1, p 2 - 4 * π / 3] ∧
      cellClass ![p 0, p 1, p 2 - 4 * π / 3] = cellClass p := by
  intro p hp
  have hsψ : Real.sin (p 1) = 0 := by rcases hp.2.1 with h | h <;> rw [h] <;> simp
  have hrot : cellPoint ![p 0, p 1, p 2 - 4 * π / 3] = ζ • cellPoint p := by
    rw [l5b_cellPoint_rotate hsψ (-(4 * π / 3)) _ (by ring), l5b_exp_eq_of (k := 1) (n := -1)
      (by push_cast; ring), pow_one]
  have hdom : p ∈ cellDomain :=
    ⟨hp.1, by rcases hp.2.1 with h | h <;> rw [h] <;> simp [Real.pi_pos.le],
      ⟨by linarith [hp.2.2.1, Real.pi_pos], hp.2.2.2⟩⟩
  refine ⟨⟨by simpa using hp.1, by simpa using hp.2.1,
    by simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
       constructor <;> linarith [hp.2.2.1, hp.2.2.2]⟩, hrot.symm, ?_⟩
  have := classOf_smul_scale ζ_mem_VT one_pos (cellPoint_mem_sectionZero hdom)
  rw [scale_one, ← hrot] at this
  exact this

/-- **Proposition 15.2.2** (`prop:closed-cells`, label of this formalization; unlabelled, TeX
12300–12314), in `Ξ_{𝒲,0}/V_T`. "Every point in the domain of `Ξ_{𝒲,0}/V_T` is equivalent to a
point in the union of the closures `𝒞₃(ζ^{±1})` of the first and second big cells (with
identifications on the boundaries of each cell as given above). The first control `u` is `ζ` on
the first big cell and `ζ²` on the second big cell. The dynamics on the faces of the cells is given
as the continuous extension from the dynamics on the interior of the cells. Every point on every
face of the cells that is not identified with a point in the domain `Ξ_{𝒲,0}/V_T` is a point with
vanishing (limiting) first switching time `t_sw = 0`."

Formalized (the book's proof: "See the discussion leading up to the statement"):
1. every point is in the second big cell with its top face (`cellTwoSet`), or has a representative
   in the closed first big cell at which the first control is `ζ` (from Lemma 15.1.1 and (15.1.1),
   through `cellClass_cellCoords` where `x₃ < 0` and `lemma15_1_1`, `eqn15_1_1` where `z₃ = 0`;
   Lemma 13.2.6 and `frontBackOne_cover_and_switching`);
2. the first control is `ζ` on the open first cell and `ζ²` on the second cell with its top face
   (the facts after Definition 15.1.2, `definition15_1_2`, and `topFaceTwo_switching`);
3. at a point `p` of the closed first (second) cell at which `ζ` (`ζ²`) is not the first control
   of `cellPoint p` — a face point whose cell dynamics does not represent the dynamics of its class
   ("not identified with a point in the domain") — the first switching time tends to `0` from the
   open cell, and the extended map is the identity of `Ξ_{𝒲,0}/V_T` there: `F(cellClass q) →
   cellClass p`. These are the red-shaded regions of Figure 15.1 and the boundary maps of
   TeX 12178–12195 (`θ₂ = 0⁺ ↦ 0⁻`, `θ₂ ↦ θ₂ ± 2π/3` on `ψ ∈ {0, π}`, `θ₂ ↦ 2π + θ₂`), each of which
   is a change of representative of the same class.

"The dynamics on the faces … is the continuous extension from the interior" holds where the
dynamics is continuous (`continuousWithinAt_topFaceOne`, `continuousWithinAt_frontBackOne`,
`continuousWithinAt_topFaceTwo`); the extensions on the closed parts of the cells are the subject of
Proposition 15.3.2 (`Proposition15_3_2`).

Proof route for 3: the first control at `cellPoint p` is not `ζ`, so `ζ` is beaten at some time
`t ∈ [0, ε]` for every `ε > 0`; beating is a strict inequality between continuous functions of
`(t, q)`, so for `q` near `p` in the open cell (first control `ζ`) `ζ` is beaten at a time `≤ ε`
along the trajectory of `cellPoint q`, so `0 < t_sw(cellPoint q) ≤ ε`; then
`F(cellPoint q) = z(t_sw, cellPoint q, ζ) → cellPoint p` and `classOf` is continuous. -/
theorem proposition15_2_2 :
    (∀ x : XiW0Quot, x ∈ cellTwoSet ∨
      ∃ p ∈ closedBoxOne, cellClass p = x ∧ IsFirstControl (cellPoint p) ζ) ∧
    (∀ p ∈ openBoxOne, IsFirstControl (cellPoint p) ζ) ∧
    (∀ p ∈ cellTwoDomain, IsFirstControl (cellPoint p) (ζ ^ 2)) ∧
    (∀ p ∈ closedBoxOne, ¬ IsFirstControl (cellPoint p) ζ →
      Tendsto (fun q ↦ firstSwitchTime (cellPoint q)) (𝓝[openBoxOne] p) (𝓝 0) ∧
        Tendsto (fun q ↦ poincareAngZero (cellClass q)) (𝓝[openBoxOne] p) (𝓝 (cellClass p))) ∧
    ∀ p ∈ closedBoxTwo, ¬ IsFirstControl (cellPoint p) (ζ ^ 2) →
      Tendsto (fun q ↦ firstSwitchTime (cellPoint q)) (𝓝[openBoxTwo] p) (𝓝 0) ∧
        Tendsto (fun q ↦ poincareAngZero (cellClass q)) (𝓝[openBoxTwo] p) (𝓝 (cellClass p)) := by
  have hdom1 : ∀ p ∈ closedBoxOne, p ∈ cellDomain := fun p hp ↦
    ⟨hp.1, hp.2.1, ⟨by linarith [hp.2.2.1, Real.pi_pos], hp.2.2.2⟩⟩
  have hdom2 : ∀ p ∈ closedBoxTwo, p ∈ cellDomain := fun p hp ↦
    ⟨hp.1, hp.2.1, ⟨hp.2.2.1, by linarith [hp.2.2.2, Real.pi_pos]⟩⟩
  have hsub1 : openBoxOne ⊆ cellDomain := fun p hp ↦ hdom1 p
    ⟨Ioo_subset_Icc_self hp.1, Ioo_subset_Icc_self hp.2.1, Ioo_subset_Icc_self hp.2.2⟩
  have hsub2 : openBoxTwo ⊆ cellDomain := fun p hp ↦ hdom2 p
    ⟨Ioo_subset_Icc_self hp.1, Ioo_subset_Icc_self hp.2.1, Ioo_subset_Icc_self hp.2.2⟩
  refine ⟨fun x ↦ ?_, fun p hp ↦ l5b_isFirstControl_openBoxOne hp, fun p hp ↦ ?_,
    fun p hp hnot ↦ l5b_tendsto_of_not_isFirstControl ζ_mem_VT
      (fun q hq ↦ l5b_isFirstControl_openBoxOne hq) hsub1 (hdom1 p hp) hnot,
    fun p hp hnot ↦ l5b_tendsto_of_not_isFirstControl ζ_sq_mem_VT
      (fun q hq ↦ l5b_isFirstControl_openBoxTwo hq) hsub2 (hdom2 p hp) hnot⟩
  · -- 1. a representative with `z₃ = x₃ ≤ 0` (a rotation by `V_T`)
    obtain ⟨z, hz, rfl⟩ := exists_classOf_eq x
    obtain ⟨hz0, hzw, hzH⟩ := hz
    obtain ⟨v, hv, σ, hσ, hvz⟩ : ∃ v ∈ VT, ∃ σ : ℝ, σ ≤ 0 ∧ v * z 2 = σ := by
      rcases hzw with (⟨σ, hσ, h⟩ | ⟨σ, hσ, h⟩) | ⟨σ, hσ, h⟩
      · exact ⟨1, one_mem_VT, σ, hσ, by rw [h, one_mul, pow_zero, mul_one]⟩
      · refine ⟨ζ ^ 2, ζ_sq_mem_VT, σ, hσ, ?_⟩
        rw [h, pow_one, mul_left_comm, ← pow_succ, ζ_pow_three, mul_one]
      · refine ⟨ζ, ζ_mem_VT, σ, hσ, ?_⟩
        rw [h, mul_left_comm, ← pow_succ', ζ_pow_three, mul_one]
    have hv0 : v ≠ 0 := by
      intro h; have := norm_eq_one_of_mem_VT hv; rw [h, norm_zero] at this; norm_num at this
    set w := v • z with hw
    have hw2 : w 2 = σ := hvz
    have hwz : classOf w = classOf z := by
      have := classOf_smul_scale hv one_pos ⟨hz0, hzw, hzH⟩
      rwa [scale_one] at this
    have hwH : hamMax w = 0 := by
      have := (hamMax_smul_scale_and_tau hv one_pos z).1
      rw [scale_one, hzH, mul_zero] at this
      exact this
    have hwS : w ∈ sectionZero :=
      ⟨smul_ne_zero hv0 hz0, by rw [hw2]; exact Or.inl (Or.inl ⟨σ, hσ, by simp⟩), hwH⟩
    rcases hσ.lt_or_eq with hσ | hσ
    · -- `x₃ < 0`: the cell coordinates (Lemma 15.1.1, (15.1.1)), `θ₂ ∈ (-π, π]`
      obtain ⟨⟨h0, h1, h2⟩, hcc⟩ := cellClass_cellCoords hwS (by rw [hw2]; simp)
        (by rw [hw2]; simpa using hσ)
      rcases le_or_gt (cellCoords w 2) 0 with hθ | hθ
      · exact Or.inl ⟨cellCoords w, ⟨h0, h1, ⟨h2.1, hθ⟩⟩, hcc.trans hwz⟩
      · refine Or.inr ⟨cellCoords w, ⟨Ioo_subset_Icc_self h0, Ioo_subset_Icc_self h1,
          ⟨hθ.le, h2.2⟩⟩, hcc.trans hwz, ?_⟩
        rcases h2.2.lt_or_eq with hπ | hπ
        · exact l5b_isFirstControl_openBoxOne ⟨h0, h1, ⟨hθ, hπ⟩⟩
        · exact (firstControl_eq_iff (l5b_cellPoint_ne_zero _)).1
            (topFaceOne_switching ⟨h0, h1, hπ⟩).1
    · -- `z₃ = 0`: rescale to `|z₁| + |z₂| = 1` and use the closed 2-cell `𝒞₂(ζ, 1, 1)`
      have hw2' : w 2 = 0 := by rw [hw2, hσ, Complex.ofReal_zero]
      -- (15.1.1) at `x₃ = 0` (`r₁ r₂ sin(θ₁ - θ₂) = 0`), and the rescaling of Lemma 15.1.1
      have h₃ : w 2 = ((2 * ‖w 0‖ * ‖w 1‖ * Real.sin (arg (w 0) - arg (w 1)) : ℝ) : ℂ) := by
        have hpolar : w = ![(‖w 0‖ : ℂ) * exp ((arg (w 0) : ℂ) * I),
            (‖w 1‖ : ℂ) * exp ((arg (w 1) : ℂ) * I), ((0 : ℝ) : ℂ)] := by
          funext j
          fin_cases j <;> simp [Complex.norm_mul_exp_arg_mul_I, hw2']
        have e := (eqn15_1_1 (r₁ := ‖w 0‖) (r₂ := ‖w 1‖) (θ₁ := arg (w 0)) (θ₂ := arg (w 1))
          (x₃ := 0) le_rfl).1.1 (by rw [← hpolar]; exact hwH)
        rw [hw2', ← e, Complex.ofReal_zero]
      obtain ⟨r, ⟨hr, hn'⟩, -⟩ := lemma15_1_1 hwS.1 h₃
      set w' := scale r w
      have hw'2 : w' 2 = 0 := by simp [w', scale, hw2']
      have hRR : RR (w' 0) (w' 1 * I) = 0 := by
        rw [← l5b_hamMax_of_z3_zero hw'2]
        have := (hamMax_smul_scale_and_tau one_mem_VT hr w).1
        rw [one_smul, hwH, mul_zero] at this
        exact this
      obtain ⟨k, q, ⟨hq0, hq1, hq2, hq01⟩, hq⟩ := l5b_rep_z3_zero hw'2 hn' hRR
      refine Or.inr ⟨q, ⟨hq0, by rcases hq1 with h | h <;> rw [h] <;> simp [Real.pi_pos.le],
        ⟨by linarith [hq2.1, Real.pi_pos], hq2.2⟩⟩, ?_,
        l5b_isFirstControl_frontBack hq0 hq1 hq2 hq01⟩
      rw [cellClass, hq, classOf_smul_scale (l5b_ζ_pow_mem_VT k) hr hwS, hwz]
  · -- 2. the second cell with its top face
    rcases hp.2.2.2.lt_or_eq with h | h
    · exact l5b_isFirstControl_openBoxTwo ⟨hp.1, hp.2.1, ⟨hp.2.2.1, h⟩⟩
    · exact (firstControl_eq_iff (l5b_cellPoint_ne_zero p)).1
        (topFaceTwo_switching ⟨hp.1, hp.2.1, h⟩).1

/-- **The boundary maps on the red-shaded faces** (TeX 12178–12195, Figure 15.1). "The bottom face
`θ₂ = 0⁺` of the first big cell maps to the top face `θ₂ = 0⁻` of the second big cell (by the
identity map `(r₂, ψ) ↦ (r₂, ψ)`). The bottom face `θ₂ = (-π)⁺` of the second big cell maps to the
top face `θ₂ = π⁻` of the first big cell by the map `(r₂, ψ, θ₂) ↦ (r₂, ψ, 2π + θ₂)`. The boundary
region `ψ ∈ {0, π}`, `θ₂ ∈ [0, π/3]` on the first big cell is shifted to `V_T`-equivalent points
`(ψ, θ₂) ↦ (ψ, θ₂ + 2π/3)` on the same faces. Also, the boundary region `ψ ∈ {0, π}`,
`θ₂ ∈ [-π/3, 0]` on the first [read: second] big cell is shifted to `V_T`-equivalent points
`(ψ, θ₂) ↦ (ψ, θ₂ - 2π/3)`."

On each of these faces the cell's control is not the first control (so, by `proposition15_2_2`,
`t_sw → 0` from the open cell and the extended map is the identity of `Ξ_{𝒲,0}/V_T`), and the face
point has the same class as the point it is said to map to. The bottom face of the first cell is in
the second cell (`cellTwoSet`). At `θ₂ = -π/3` (an endpoint of the book's closed interval) the tie
rule of Lemma 13.2.6 makes `ζ²` the first control, so that endpoint is excluded; at `θ₂ = π/3` the
same rule gives the control `1`, and the endpoint is included. The front and back clauses are stated
for `r₂ ∈ (0, 1]`: on the right face `r₂ = 0` (collapsed to edges, TeX 12192–12195) they can fail,
e.g. at `(r₂, ψ, θ₂) = (0, π, 0)` the point is `(-1, 0, 0)`, whose first control is `ζ`.

Proof route: the first controls from the lexicographic rule of Lemma 13.2.6 (`lemma13_2_6`): on
`θ₂ = 0` the tie between `ζ` and `ζ²` is broken by `y₁ = -r₁ sin ψ < 0`, on `θ₂ = -π` by
`y₁ = r₁ sin ψ > 0`; on `z₃ = 0` the first control maximizes `RR(z₂, ·)`, which is `1` when
`arg z₂ ∈ [0, π/3]` (`ζ` loses the tie at `π/3`) or `arg z₂ ∈ (-π/3, 0]`. The classes: the points
are equal (`e^{-iπ} = e^{iπ}`), or differ by the rotation by `ζ` (resp. `ζ²`), which fixes `ψ` and
`z₃ = 0`. -/
theorem boundary_maps_red_faces :
    (∀ p : Fin 3 → ℝ, p 0 ∈ Ioo 0 1 → p 1 ∈ Ioo 0 π → p 2 = 0 →
      ¬ IsFirstControl (cellPoint p) ζ ∧ cellClass p ∈ cellTwoSet) ∧
    (∀ p : Fin 3 → ℝ, p 0 ∈ Ioo 0 1 → p 1 ∈ Ioo 0 π → p 2 = -π →
      ¬ IsFirstControl (cellPoint p) (ζ ^ 2) ∧ cellClass p = cellClass ![p 0, p 1, π]) ∧
    (∀ p : Fin 3 → ℝ, p 0 ∈ Ioc 0 1 → (p 1 = 0 ∨ p 1 = π) → p 2 ∈ Icc 0 (π / 3) →
      ¬ IsFirstControl (cellPoint p) ζ ∧ cellClass p = cellClass ![p 0, p 1, p 2 + 2 * π / 3]) ∧
    ∀ p : Fin 3 → ℝ, p 0 ∈ Ioc 0 1 → (p 1 = 0 ∨ p 1 = π) → p 2 ∈ Ioc (-(π / 3)) 0 →
      ¬ IsFirstControl (cellPoint p) (ζ ^ 2) ∧
        cellClass p = cellClass ![p 0, p 1, p 2 - 2 * π / 3] := by
  have hne : ∀ {z : Fin 3 → ℂ}, IsFirstControl z ζ → ¬ IsFirstControl z (ζ ^ 2) :=
    fun h h' ↦ l5b_ζ_ne_ζ_sq (h.unique h')
  refine ⟨fun p h0 h1 h2 ↦ ⟨fun h ↦ hne h ?_, ⟨p, ⟨h0, h1, ⟨by rw [h2]; linarith [Real.pi_pos],
      h2.le⟩⟩, rfl⟩⟩, fun p h0 h1 h2 ↦ ?_, fun p h0 h1 h2 ↦ ?_, fun p h0 h1 h2 ↦ ?_⟩
  · -- the bottom face `θ₂ = 0` of the first cell is the top face of the second
    exact (firstControl_eq_iff (l5b_cellPoint_ne_zero p)).1 (topFaceTwo_switching ⟨h0, h1, h2⟩).1
  · -- the bottom face `θ₂ = -π` of the second cell is the top face `θ₂ = π` of the first
    have he : cellPoint ![p 0, p 1, π] = cellPoint p :=
      l5b_cellPoint_add_two_pi p π (by rw [h2]; ring)
    have hfc : IsFirstControl (cellPoint p) ζ := by
      rw [← he]
      exact (firstControl_eq_iff (l5b_cellPoint_ne_zero _)).1
        (topFaceOne_switching ⟨by simpa using h0, by simpa using h1, by simp⟩).1
    exact ⟨hne hfc, by rw [cellClass, cellClass, he]⟩
  · -- `ψ ∈ {0, π}`, `θ₂ ∈ [0, π/3]` on the first cell: `ζ` is beaten by `1` at once
    have hsψ : Real.sin (p 1) = 0 := by rcases h1 with h | h <;> rw [h] <;> simp
    have hdom : p ∈ cellDomain := ⟨Ioc_subset_Icc_self h0,
      by rcases h1 with h | h <;> rw [h] <;> simp [Real.pi_pos.le],
      ⟨by linarith [h2.1, Real.pi_pos], by linarith [h2.2, Real.pi_pos]⟩⟩
    have hrot : cellPoint ![p 0, p 1, p 2 + 2 * π / 3] = ζ • cellPoint p := by
      rw [l5b_cellPoint_rotate hsψ (2 * π / 3) _ rfl,
        l5b_exp_eq_of (k := 1) (n := 0) (by push_cast; ring), pow_one]
    refine ⟨l5b_not_isFirstControl (Or.inl rfl) (l5b_neg_near_zero _ ?_), ?_⟩
    · obtain ⟨hA, -, -, -⟩ := l5b_chi_cellPoint p
      have hK : Real.sin (p 2) - √3 * Real.cos (p 2) = 2 * Real.sin (p 2 - π / 3) := by
        rw [Real.sin_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]; ring
      have hs1 : Real.sin (p 2 - p 1) - √3 * Real.cos (p 2 - p 1) =
          Real.cos (p 1) * (Real.sin (p 2) - √3 * Real.cos (p 2)) := by
        rw [Real.sin_sub, Real.cos_sub, hsψ]; ring
      rw [hA, hs1, hK, hsψ]
      dsimp only
      rcases h2.2.lt_or_eq with hθ | hθ
      · have : Real.sin (p 2 - π / 3) < 0 :=
          Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith [h2.1, Real.pi_pos])
        exact Or.inr (Or.inl ⟨by ring, by nlinarith [h0.1]⟩)
      · rw [hθ, sub_self, Real.sin_zero]
        exact Or.inr (Or.inr (Or.inr ⟨by ring, by ring, by ring, by norm_num⟩))
    · have := classOf_smul_scale ζ_mem_VT one_pos (cellPoint_mem_sectionZero hdom)
      rw [scale_one, ← hrot] at this
      exact this.symm
  · -- `ψ ∈ {0, π}`, `θ₂ ∈ (-π/3, 0]` on the second cell: `ζ²` is beaten by `1` at once
    have hsψ : Real.sin (p 1) = 0 := by rcases h1 with h | h <;> rw [h] <;> simp
    have hdom : p ∈ cellDomain := ⟨Ioc_subset_Icc_self h0,
      by rcases h1 with h | h <;> rw [h] <;> simp [Real.pi_pos.le],
      ⟨by linarith [h2.1, Real.pi_pos], by linarith [h2.2, Real.pi_pos]⟩⟩
    have hrot : cellPoint ![p 0, p 1, p 2 - 2 * π / 3] = ζ ^ 2 • cellPoint p := by
      rw [l5b_cellPoint_rotate hsψ (-(2 * π / 3)) _ (by ring),
        l5b_exp_eq_of (k := 2) (n := -1) (by push_cast; ring)]
    refine ⟨l5b_not_isFirstControl (Or.inr rfl) (l5b_neg_near_zero _ ?_), ?_⟩
    · obtain ⟨-, -, hA, -⟩ := l5b_chi_cellPoint p
      have hK : Real.sin (p 2) + √3 * Real.cos (p 2) = 2 * Real.sin (p 2 + π / 3) := by
        rw [Real.sin_add, Real.cos_pi_div_three, Real.sin_pi_div_three]; ring
      have : 0 < Real.sin (p 2 + π / 3) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [h2.1]) (by linarith [h2.2, Real.pi_pos])
      rw [hA, hK, hsψ]
      dsimp only
      exact Or.inr (Or.inl ⟨by ring, by nlinarith [h0.1]⟩)
    · have := classOf_smul_scale ζ_sq_mem_VT one_pos (cellPoint_mem_sectionZero hdom)
      rw [scale_one, ← hrot] at this
      exact this.symm

end SmoothedPolygons
