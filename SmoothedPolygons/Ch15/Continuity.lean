module

public import SmoothedPolygons.Ch15.SmallerCells
public import Basic.Analysis.Polynomial.LeastPositiveRoot

/-!
# Chapter 15: continuity of the first switching time and of the cell maps (§15.1–§15.2)

The continuity claims of Hales–Vajjha, *Packings of Smoothed Polygons*, §15.1–§15.2:

* on a big open cell the first switching time, hence the Poincaré map, is continuous off the loci
  `Δ_{A,0} = 0`, `Δ_{B,1} = 0`, `res_AB = 0` (TeX 12139–12143; REPORT.md, E70);
* the dynamics extends continuously from the interior of the first big cell to its top face
  `𝒞₂(ζ, 0, 2)` (TeX 12233–12235) and to the closed 2-cell `𝒞₂(ζ, 1, 1)` on the front and back faces
  (TeX 12268–12276, at its nondegenerate points), and from the interior of the second big cell to
  its top face `𝒞₂(ζ², 0, 2)` "with exceptional discontinuities" (TeX 12239–12245);
* the root-based maps `F_A` on `𝒞₂^A` and `F_B` on the closure of `𝒞₂^B` are continuous
  (TeX 12419–12422).

## Proofs

All five rest on one fact, proved in `Basic/Analysis/Polynomial/LeastPositiveRoot.lean`: the least
positive sign change of a family of real functions depends continuously on the parameter
(`tendsto_sInf_pos_zeros_of_signChange`; the intermediate value theorem gives zeros just after it,
compactness of `[0, T - ε]` keeps the functions positive before it). Its polynomial form is
`Polynomial.tendsto_sInf_pos_roots_of_simple` (a simple least positive root depends continuously on
the coefficients). A double root forces the discriminant to vanish
(`Polynomial.discr_eq_zero_of_isRoot_of_isRoot_derivative`), which is how `Δ ≠ 0` enters.

The first switching time is the least time at which the first control `u` is beaten, that is, at
which `χ_A < 0` or `χ_B < 0` (`l5c_notBeaten_iff`). Its continuity at `p` (`l5c_scheme`) has two
halves:
* upper bound: `u` is beaten at times arbitrarily close to `t_sw(p)` on the right
  (`firstControl_beaten`), and a strict inequality persists at nearby points;
* lower bound: before `t_sw(p)` the reduced switching polynomials of `p` are positive, so they stay
  positive near `p` on each compact `[0, T']`, `T' < t_sw(p)` (`l5c_lower`). At `p` they are
  nonnegative on `[0, t_sw(p)]` (the first control is optimal there) and positive at `0`, and a
  zero inside `(0, t_sw(p))` would be a double root, which `Δ ≠ 0` excludes
  (`l5c_pos_of_discr_ne_zero`).

Near a face the multiplicities `m_A`, `m_B` jump, so the reduced polynomials of the face are not
those of the open cell. The switching polynomials of nearby points are written as
`α(q) + t (β(q) + t g(q, t))` with `α, β ≥ 0` on the closed cell and `g` positive at the face point.
This is the book's "no root can enter `(0, ∞)` through `0`".

For `F_A` on `𝒞₂^A` (`l5c_tendsto_leastPosRoot`), the least positive root `t₀` of `χ_{A,0}` is
either a sign change, where the general lemma applies, or a double root (`Δ_{A,0} = 0`). In the
second case `χ_A'(t₀) = 0` and `χ_A'(t₀ + ε/2) > 0`, also at nearby points. A nearby `χ_{A,0}` whose
positive roots all lay beyond `t₀ + ε` would be positive on `[0, t₀ + ε/2]` and nondecreasing after
it (`χ_A' ≥ 0` propagates to the right because `χ_A'(0) < 0`, `l5c_cubic_mono`), so it would have no
positive root, against `Δ_{A,0} ≥ 0`. `F_A` lands on a wall because `ζ²` and `1` tie at `t₀` and
`t₀ ≤ t_B` (`leastPosRoot_chiA_le_of_mem_topFaceTwo`, the computation in the module docstring of
`SmoothedPolygons/Ch15/SmallerCells.lean`).
-/

@[expose] public section

namespace SmoothedPolygons

open Complex Set Filter Topology Polynomial
open scoped Real

namespace TriFuller

/-! ### Helpers: controls, switching polynomials and cell points -/

private lemma l5c_sqrt3_pos : (0 : ℝ) < √3 := by positivity

/-- `H_F(w, a) - H_F(w, b) = RR(a - b, w₃)`. -/
private lemma l5c_ham_sub (w : Fin 3 → ℂ) (a b : ℂ) : ham w a - ham w b = RR (a - b) (w 2) := by
  simp only [ham, RR_eq_re_mul_add_im_mul, Complex.sub_re, Complex.sub_im]; ring

/-- Comparing two controls at `w` is comparing `RR(w₃, ·)`. -/
private lemma l5c_ham_le_iff (w : Fin 3 → ℂ) (a b : ℂ) :
    ham w a ≤ ham w b ↔ RR (w 2) a ≤ RR (w 2) b := by
  simp only [ham, RR_comm (w 2)]
  constructor <;> intro h <;> linarith

private lemma l5c_ζ_sq_ne_one : ζ ^ 2 ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  rw [ζ_sq_re, Complex.one_re] at this
  norm_num at this

private lemma l5c_chiA_eval (u : ℂ) (z : Fin 3 → ℂ) (t : ℝ) :
    (chiA u z).toPoly.eval t = (ham (flow t z u) u - ham (flow t z u) 1) / √3 := by
  rw [chiA, eval_switchingCubic, switchingFunction, l5c_ham_sub]

private lemma l5c_chiB_eval (u : ℂ) (z : Fin 3 → ℂ) (t : ℝ) :
    (chiB u z).toPoly.eval t =
      (ham (flow t z u) u - ham (flow t z u) (starRingEnd ℂ u)) / √3 := by
  rw [chiB, eval_switchingCubic, switchingFunction, l5c_ham_sub]

/-- The control `u ∈ {ζ, ζ²}` is not beaten at time `t` along its trajectory if and only if
`χ_A(t) ≥ 0` and `χ_B(t) ≥ 0`. -/
private lemma l5c_notBeaten_iff {u : ℂ} (hu : u = ζ ∨ u = ζ ^ 2) (z : Fin 3 → ℂ) (t : ℝ) :
    (∀ v ∈ VT, ham (flow t z u) v ≤ ham (flow t z u) u) ↔
      0 ≤ (chiA u z).toPoly.eval t ∧ 0 ≤ (chiB u z).toPoly.eval t := by
  rw [l5c_chiA_eval, l5c_chiB_eval, le_div_iff₀ l5c_sqrt3_pos, le_div_iff₀ l5c_sqrt3_pos,
    zero_mul, sub_nonneg, sub_nonneg]
  have huV : u ∈ VT := by rcases hu with rfl | rfl; exacts [ζ_mem_VT, ζ_sq_mem_VT]
  refine ⟨fun h ↦ ⟨h 1 one_mem_VT, h _ (conj_mem_VT huV)⟩, fun ⟨h1, h2⟩ v hv ↦ ?_⟩
  rcases hu with rfl | rfl <;> rcases mem_VT.1 hv with rfl | rfl | rfl
  · exact h1
  · exact le_rfl
  · rwa [conj_ζ] at h2
  · exact h1
  · rwa [conj_ζ_sq] at h2
  · exact le_rfl

/-- The switching cubics explicitly (`chiA_chiB_eq`). -/
private lemma l5c_eval_chi (z : Fin 3 → ℂ) (t : ℝ) :
    (chiA ζ z).toPoly.eval t = -1 / 12 * t ^ 3 + ((z 0).im - √3 * (z 0).re) / 4 * t ^ 2 +
      ((z 1).im - √3 * (z 1).re) / 2 * t + ((z 2).im - √3 * (z 2).re) / 2 ∧
    (chiB ζ z).toPoly.eval t = 1 / 12 * t ^ 3 + (z 0).im / 2 * t ^ 2 + (z 1).im * t + (z 2).im ∧
    (chiA (ζ ^ 2) z).toPoly.eval t = 1 / 12 * t ^ 3 + -((z 0).im + √3 * (z 0).re) / 4 * t ^ 2 +
      -((z 1).im + √3 * (z 1).re) / 2 * t + -((z 2).im + √3 * (z 2).re) / 2 ∧
    (chiB (ζ ^ 2) z).toPoly.eval t = -1 / 12 * t ^ 3 + -(z 0).im / 2 * t ^ 2 + -(z 1).im * t +
      -(z 2).im := by
  obtain ⟨h1, h2, h3, h4⟩ := chiA_chiB_eq z
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [h1, h2, h3, h4, Cubic.toPoly, eval_add, eval_mul, eval_C, eval_pow, eval_X]

/-- A cubic with no constant term, divided by `X`. -/
private lemma l5c_red {P : ℝ[X]} {a b c : ℝ} {m : ℕ} (hm : m = 1)
    (h : P = (⟨a, b, c, 0⟩ : Cubic ℝ).toPoly) : P /ₘ X ^ m = C a * X ^ 2 + C b * X + C c := by
  subst hm
  have e : (⟨a, b, c, 0⟩ : Cubic ℝ).toPoly = X * (C a * X ^ 2 + C b * X + C c) := by
    simp only [Cubic.toPoly, map_zero, add_zero]; ring
  rw [pow_one, h, e, mul_divByMonic_cancel_left _ monic_X]

private lemma l5c_eval_quad (a b c t : ℝ) :
    (C a * X ^ 2 + C b * X + C c : ℝ[X]).eval t = a * t ^ 2 + b * t + c := by
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]

/-- The coordinates of the cell point. -/
private lemma l5c_cellPoint_apply (p : Fin 3 → ℝ) :
    (cellPoint p 0).re = (1 - p 0) * Real.cos (p 2 - p 1) ∧
    (cellPoint p 0).im = (1 - p 0) * Real.sin (p 2 - p 1) ∧
    (cellPoint p 1).re = p 0 * Real.cos (p 2) ∧ (cellPoint p 1).im = p 0 * Real.sin (p 2) ∧
    (cellPoint p 2).re = -2 * (1 - p 0) * p 0 * Real.sin (p 1) ∧ (cellPoint p 2).im = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [cellPoint, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Complex.re_ofReal_mul, Complex.im_ofReal_mul,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.ofReal_re,
      Complex.ofReal_im]

private lemma l5c_im2 (p : Fin 3 → ℝ) : (cellPoint p 2).im = 0 := (l5c_cellPoint_apply p).2.2.2.2.2

private lemma l5c_continuous_cellPoint : Continuous cellPoint := by
  refine continuous_pi fun j ↦ ?_
  fin_cases j <;> simp only [cellPoint] <;> fun_prop

private lemma l5c_continuous_re (j : Fin 3) : Continuous fun q ↦ (cellPoint q j).re :=
  Complex.continuous_re.comp ((continuous_apply j).comp l5c_continuous_cellPoint)

private lemma l5c_continuous_im (j : Fin 3) : Continuous fun q ↦ (cellPoint q j).im :=
  Complex.continuous_im.comp ((continuous_apply j).comp l5c_continuous_cellPoint)

/-- `r₁ + r₂ = 1` forbids `cellPoint p = 0`. -/
private lemma l5c_cellPoint_ne_zero (p : Fin 3 → ℝ) : cellPoint p ≠ 0 := by
  intro h
  obtain ⟨h1, h2, h3, h4, -, -⟩ := l5c_cellPoint_apply p
  have e : ∀ j, (cellPoint p j).re = 0 ∧ (cellPoint p j).im = 0 := fun j ↦ by simp [h]
  rw [(e 0).1] at h1; rw [(e 0).2] at h2; rw [(e 1).1] at h3; rw [(e 1).2] at h4
  have a : (1 - p 0) ^ 2 = ((1 - p 0) * Real.sin (p 2 - p 1)) ^ 2 +
      ((1 - p 0) * Real.cos (p 2 - p 1)) ^ 2 := by
    rw [mul_pow, mul_pow, ← mul_add, Real.sin_sq_add_cos_sq, mul_one]
  have b : p 0 ^ 2 = (p 0 * Real.sin (p 2)) ^ 2 + (p 0 * Real.cos (p 2)) ^ 2 := by
    rw [mul_pow, mul_pow, ← mul_add, Real.sin_sq_add_cos_sq, mul_one]
  rw [← h1, ← h2] at a
  rw [← h3, ← h4] at b
  have a' : 1 - p 0 = 0 := pow_eq_zero_iff two_ne_zero |>.1 (by rw [a]; ring)
  have b' : p 0 = 0 := pow_eq_zero_iff two_ne_zero |>.1 (by rw [b]; ring)
  linarith

private lemma l5c_continuous_ham (v : ℂ) : Continuous fun w : Fin 3 → ℂ ↦ ham w v := by
  simp only [ham, RR_eq_re_mul_add_im_mul]; fun_prop

private lemma l5c_continuous_flow (u : ℂ) :
    Continuous fun x : ℝ × (Fin 3 → ℂ) ↦ flow x.1 x.2 u := by
  refine continuous_pi fun j ↦ ?_
  fin_cases j <;> simp only [flow] <;> fun_prop

private lemma l5c_continuous_flow_cellPoint (u : ℂ) :
    Continuous fun x : (Fin 3 → ℝ) × ℝ ↦ flow x.2 (cellPoint x.1) u :=
  (l5c_continuous_flow u).comp
    (continuous_snd.prodMk (l5c_continuous_cellPoint.comp continuous_fst))

/-- The evaluation `(q, t) ↦ χ_A(t)` at `cellPoint q` is jointly continuous. -/
private lemma l5c_continuous_chiA (u : ℂ) :
    Continuous fun x : (Fin 3 → ℝ) × ℝ ↦ (chiA u (cellPoint x.1)).toPoly.eval x.2 := by
  simp_rw [l5c_chiA_eval]
  exact (((l5c_continuous_ham u).comp (l5c_continuous_flow_cellPoint u)).sub
    ((l5c_continuous_ham 1).comp (l5c_continuous_flow_cellPoint u))).div_const _

/-- `x₃ ≤ 0` on the closed cells. -/
private lemma l5c_x3_nonpos {q : Fin 3 → ℝ} (hq : q ∈ cellDomain) : (cellPoint q 2).re ≤ 0 := by
  rw [(l5c_cellPoint_apply q).2.2.2.2.1]
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hq.2.1.1 hq.2.1.2
  have := mul_nonneg (mul_nonneg (sub_nonneg.2 hq.1.2) hq.1.1) hs
  nlinarith

/-- `x₃ < 0` when `r₂ ∈ (0, 1)` and `ψ ∈ (0, π)`. -/
private lemma l5c_x3_neg {q : Fin 3 → ℝ} (h0 : q 0 ∈ Ioo 0 1) (h1 : q 1 ∈ Ioo 0 π) :
    (cellPoint q 2).re < 0 := by
  rw [(l5c_cellPoint_apply q).2.2.2.2.1]
  have hs := Real.sin_pos_of_pos_of_lt_pi h1.1 h1.2
  have := mul_pos (mul_pos (sub_pos.2 h0.2) h0.1) hs
  nlinarith

private lemma l5c_openBoxOne_sub : openBoxOne ⊆ cellDomain := fun q hq ↦
  ⟨Ioo_subset_Icc_self hq.1, Ioo_subset_Icc_self hq.2.1,
    ⟨by linarith [hq.2.2.1, Real.pi_pos], hq.2.2.2.le⟩⟩

private lemma l5c_openBoxTwo_sub : openBoxTwo ⊆ cellDomain := fun q hq ↦
  ⟨Ioo_subset_Icc_self hq.1, Ioo_subset_Icc_self hq.2.1,
    ⟨hq.2.2.1.le, by linarith [hq.2.2.2, Real.pi_pos]⟩⟩

private lemma l5c_topFaceOne_sub : topFaceOne ⊆ cellDomain := fun q hq ↦
  ⟨Ioo_subset_Icc_self hq.1, Ioo_subset_Icc_self hq.2.1,
    ⟨by rw [hq.2.2]; linarith [Real.pi_pos], hq.2.2.le⟩⟩

private lemma l5c_topFaceTwo_sub : topFaceTwo ⊆ cellDomain := fun q hq ↦
  ⟨Ioo_subset_Icc_self hq.1, Ioo_subset_Icc_self hq.2.1,
    ⟨by rw [hq.2.2]; linarith [Real.pi_pos], by rw [hq.2.2]; exact Real.pi_pos.le⟩⟩

private lemma l5c_frontBackOne_sub : frontBackOne ⊆ cellDomain := fun q hq ↦
  ⟨hq.1, by rcases hq.2.1 with h | h <;> rw [h] <;> constructor <;> linarith [Real.pi_pos],
    ⟨by linarith [hq.2.2.1, Real.pi_pos], hq.2.2.2⟩⟩

private lemma l5c_sub_cellTwoDomain : openBoxTwo ∪ topFaceTwo ⊆ cellTwoDomain := by
  rintro q (hq | hq)
  · exact ⟨hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.le⟩
  · exact ⟨hq.1, hq.2.1, by rw [hq.2.2]; exact neg_lt_zero.2 Real.pi_pos, hq.2.2.le⟩

private lemma l5c_isOpen_openBoxOne : IsOpen openBoxOne :=
  (isOpen_Ioo.preimage (continuous_apply 0)).inter
    ((isOpen_Ioo.preimage (continuous_apply 1)).inter (isOpen_Ioo.preimage (continuous_apply 2)))

private lemma l5c_isOpen_openBoxTwo : IsOpen openBoxTwo :=
  (isOpen_Ioo.preimage (continuous_apply 0)).inter
    ((isOpen_Ioo.preimage (continuous_apply 1)).inter (isOpen_Ioo.preimage (continuous_apply 2)))

private lemma l5c_fc_one {q : Fin 3 → ℝ} (hq : q ∈ openBoxOne) : firstControl (cellPoint q) = ζ :=
  (firstControl_eq_iff (l5c_cellPoint_ne_zero q)).2 (proposition15_2_2.2.1 q hq)

private lemma l5c_fc_two {q : Fin 3 → ℝ} (hq : q ∈ cellTwoDomain) :
    firstControl (cellPoint q) = ζ ^ 2 :=
  (firstControl_eq_iff (l5c_cellPoint_ne_zero q)).2 (proposition15_2_2.2.2.1 q hq)

/-! ### The continuity scheme -/

/-- The first control is not beaten on `[0, t_sw]`: the switching polynomials are nonnegative
there (`firstControl_maximizes`). -/
private lemma l5c_nonneg_at {z : Fin 3 → ℂ} {u : ℂ} (hu : u = ζ ∨ u = ζ ^ 2) (hz : z ≠ 0)
    (hfc : firstControl z = u) {t : ℝ} (ht : t ∈ Icc 0 (firstSwitchTime z)) :
    0 ≤ (chiA u z).toPoly.eval t ∧ 0 ≤ (chiB u z).toPoly.eval t := by
  have := firstControl_maximizes hz t ht
  rw [hfc] at this
  exact (l5c_notBeaten_iff hu z t).1 this

/-- A polynomial, nonnegative on an open interval, that vanishes inside it has a double root there,
so its discriminant vanishes. -/
private lemma l5c_discr_eq_zero_of_nonneg {Q : ℝ[X]} (hQ : Q ≠ 0) {a b t₁ : ℝ} (ht : t₁ ∈ Ioo a b)
    (hnn : ∀ t ∈ Ioo a b, 0 ≤ Q.eval t) (h0 : Q.eval t₁ = 0) : Q.discr = 0 := by
  have hmin : IsLocalMin (fun t ↦ Q.eval t) t₁ := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with t ht'
    rw [h0]; exact hnn t ht'
  exact discr_eq_zero_of_isRoot_of_isRoot_derivative hQ h0
    (hmin.hasDerivAt_eq_zero (Q.hasDerivAt t₁))

/-- A polynomial with nonzero discriminant, positive at `0` and nonnegative on `(0, T)`, is
positive on `[0, T)`. -/
private lemma l5c_pos_of_discr_ne_zero {Q : ℝ[X]} (hd : Q.discr ≠ 0) {T : ℝ} (h0 : 0 < Q.eval 0)
    (hnn : ∀ t ∈ Ioo 0 T, 0 ≤ Q.eval t) : ∀ t ∈ Ico 0 T, 0 < Q.eval t := by
  intro t ht
  rcases ht.1.eq_or_lt with rfl | ht0
  · exact h0
  · refine lt_of_le_of_ne (hnn t ⟨ht0, ht.2⟩) fun he ↦ hd ?_
    have hQ : Q ≠ 0 := by rintro rfl; simp at h0
    exact l5c_discr_eq_zero_of_nonneg hQ ⟨ht0, ht.2⟩ hnn he.symm

/-- **The lower bound** for the switching time near `p`: if `gA`, `gB` are continuous and positive
at `p` on `[0, T)`, and near `p` (within `s`) the positivity of `gA` (`gB`) at a time `t > 0`
makes `χ_A(t)` (`χ_B(t)`) nonnegative, then for each `T' < T` the first control is not beaten on
`(0, T']` near `p`. -/
private lemma l5c_lower {s : Set (Fin 3 → ℝ)} {p : Fin 3 → ℝ} {u : ℂ} {T : ℝ}
    {gA gB : (Fin 3 → ℝ) × ℝ → ℝ} (hgA : Continuous gA) (hgB : Continuous gB)
    (hA : ∀ t ∈ Ico 0 T, 0 < gA (p, t)) (hB : ∀ t ∈ Ico 0 T, 0 < gB (p, t))
    (hfac : ∀ᶠ q in 𝓝[s] p, ∀ t > 0,
      (0 < gA (q, t) → 0 ≤ (chiA u (cellPoint q)).toPoly.eval t) ∧
        (0 < gB (q, t) → 0 ≤ (chiB u (cellPoint q)).toPoly.eval t)) :
    ∀ T' < T, ∀ᶠ q in 𝓝[s] p, ∀ t ∈ Ioc 0 T',
      0 ≤ (chiA u (cellPoint q)).toPoly.eval t ∧ 0 ≤ (chiB u (cellPoint q)).toPoly.eval t := by
  intro T' hT'
  have hK : IsCompact (Icc (0 : ℝ) T') := isCompact_Icc
  have eA := eventually_forall_pos_of_isCompact (f := fun q t ↦ gA (q, t)) hK
    (fun t _ ↦ hgA.continuousAt) (fun t ht ↦ hA t ⟨ht.1, ht.2.trans_lt hT'⟩)
  have eB := eventually_forall_pos_of_isCompact (f := fun q t ↦ gB (q, t)) hK
    (fun t _ ↦ hgB.continuousAt) (fun t ht ↦ hB t ⟨ht.1, ht.2.trans_lt hT'⟩)
  filter_upwards [hfac, nhdsWithin_le_nhds eA, nhdsWithin_le_nhds eB] with q hq hqA hqB t ht
  exact ⟨(hq t ht.1).1 (hqA t ⟨ht.1.le, ht.2⟩), (hq t ht.1).2 (hqB t ⟨ht.1.le, ht.2⟩)⟩

/-- **The continuity scheme**: if the first control is `u ∈ {ζ, ζ²}` at `p` and near `p` in `s`,
and near `p` it is not beaten on `(0, T']` for each `T' < t_sw(p)`, then the first switching time
and the Poincaré map on classes are continuous at `p` within `s`. -/
private lemma l5c_scheme {s : Set (Fin 3 → ℝ)} {p : Fin 3 → ℝ} {u : ℂ} (hu : u = ζ ∨ u = ζ ^ 2)
    (hs : s ⊆ cellDomain) (hp : p ∈ cellDomain)
    (hfc : ∀ᶠ q in 𝓝[s] p, firstControl (cellPoint q) = u) (hfcp : firstControl (cellPoint p) = u)
    (hlow : ∀ T' < firstSwitchTime (cellPoint p), ∀ᶠ q in 𝓝[s] p, ∀ t ∈ Ioc 0 T',
      0 ≤ (chiA u (cellPoint q)).toPoly.eval t ∧ 0 ≤ (chiB u (cellPoint q)).toPoly.eval t) :
    ContinuousWithinAt (fun q ↦ firstSwitchTime (cellPoint q)) s p ∧
      ContinuousWithinAt (fun q ↦ poincareAngZero (cellClass q)) s p := by
  have hz := l5c_cellPoint_ne_zero p
  have ht : ContinuousWithinAt (fun q ↦ firstSwitchTime (cellPoint q)) s p := by
    change Tendsto (fun q ↦ sInf {t : ℝ | 0 < t ∧ ∃ v ∈ VT,
      ham (flow t (cellPoint q) (firstControl (cellPoint q))) (firstControl (cellPoint q)) <
        ham (flow t (cellPoint q) (firstControl (cellPoint q))) v}) (𝓝[s] p)
      (𝓝 (firstSwitchTime (cellPoint p)))
    apply tendsto_csInf_of_eventually
    · -- upper: `u` is beaten right after `t_sw(p)`, and the strict inequality persists
      intro ε hε
      obtain ⟨t, ht, v, hv, hlt⟩ := firstControl_beaten hz hε
      rw [hfcp] at hlt
      have hc : Continuous fun q ↦
          ham (flow t (cellPoint q) u) v - ham (flow t (cellPoint q) u) u :=
        ((l5c_continuous_ham v).comp ((l5c_continuous_flow u).comp
          (continuous_const.prodMk l5c_continuous_cellPoint))).sub
        ((l5c_continuous_ham u).comp ((l5c_continuous_flow u).comp
          (continuous_const.prodMk l5c_continuous_cellPoint)))
      have hev := nhdsWithin_le_nhds (s := s) (hc.continuousAt.eventually
        (lt_mem_nhds (sub_pos.2 hlt)))
      filter_upwards [hfc, hev] with q hq hq'
      refine ⟨t, ⟨(firstSwitchTime_pos hz).trans ht.1, v, hv, ?_⟩, ht.2⟩
      rw [hq]
      exact sub_pos.1 hq'
    · -- lower: no beating on `(0, t_sw(p) - ε]` near `p`
      intro ε hε
      filter_upwards [hfc, hlow _ (sub_lt_self _ hε)] with q hq hq'
      rintro t ⟨ht, v, hv, hlt⟩
      by_contra hle
      rw [hq] at hlt
      have := (l5c_notBeaten_iff hu _ t).2 (hq' t ⟨ht, not_lt.1 hle⟩) v hv
      exact absurd this (not_le.2 hlt)
  refine ⟨ht, ?_⟩
  -- the Poincaré map is the flow at the switching time, and `classOf` is continuous
  have hG : ContinuousWithinAt (fun q ↦ flow (firstSwitchTime (cellPoint q)) (cellPoint q) u) s p :=
    (l5c_continuous_flow u).continuousAt.comp_continuousWithinAt
      (ht.prodMk l5c_continuous_cellPoint.continuousWithinAt)
  have hG' : ContinuousWithinAt (fun q ↦ poincare (cellPoint q)) s p := by
    refine hG.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [hfc] with q hq
      simp only [poincare, hq]
    · simp only [poincare, hfcp]
  have hmem : ∀ q ∈ cellDomain, poincare (cellPoint q) ∈ sectionZero := fun q hq ↦
    poincare_mem_sectionZero (cellPoint_mem_sectionZero hq)
  have hcl : ContinuousWithinAt (fun q ↦ classOf (poincare (cellPoint q))) s p :=
    ContinuousWithinAt.comp (f := fun q ↦ poincare (cellPoint q))
      (continuousOn_classOf _ (hmem p hp)) hG' fun q hq ↦ hmem q (hs hq)
  refine hcl.congr (fun q hq ↦ ?_) ?_
  · exact poincareAngZero_classOf (cellPoint_mem_sectionZero (hs hq))
  · exact poincareAngZero_classOf (cellPoint_mem_sectionZero hp)

/-! ### The big open cells -/

/-- The open-cell case of `continuousAt_firstSwitchTime_of_ne_zero`, for either cell: `χ_A` is
reduced (`m_A = 0`) and `χ_B = t g_B` (`m_B = 1`, `g_B` the reduced polynomial). -/
private lemma l5c_openBox {s : Set (Fin 3 → ℝ)} (hso : IsOpen s) (hs : s ⊆ cellDomain) {u : ℂ}
    (hu : u = ζ ∨ u = ζ ^ 2) (hfc : ∀ q ∈ s, firstControl (cellPoint q) = u)
    {gB : (Fin 3 → ℝ) × ℝ → ℝ} (hgB : Continuous gB)
    (hBfac : ∀ q t, (chiB u (cellPoint q)).toPoly.eval t = t * gB (q, t))
    {p : Fin 3 → ℝ} (hp : p ∈ s) (hmA : multA u (cellPoint p) = 0)
    (hA0 : 0 < (chiA u (cellPoint p)).toPoly.eval 0)
    (hBred : ∀ t, (chiBRed u (cellPoint p)).eval t = gB (p, t)) (hB0 : 0 < gB (p, 0))
    (hA : discrA u (cellPoint p) ≠ 0) (hB : discrB u (cellPoint p) ≠ 0) :
    ContinuousAt (fun q ↦ firstSwitchTime (cellPoint q)) p ∧
      ContinuousAt (fun q ↦ poincareAngZero (cellClass q)) p := by
  have hz := l5c_cellPoint_ne_zero p
  have hfcp := hfc p hp
  have hred : chiARed u (cellPoint p) = (chiA u (cellPoint p)).toPoly := by
    rw [chiARed, hmA, pow_zero, divByMonic_one]
  have hnn := fun t (ht : t ∈ Icc 0 (firstSwitchTime (cellPoint p))) ↦
    l5c_nonneg_at hu hz hfcp ht
  -- at `p`, the reduced polynomials are positive before the switch (`Δ ≠ 0`)
  have hposA : ∀ t ∈ Ico 0 (firstSwitchTime (cellPoint p)),
      0 < (chiA u (cellPoint p)).toPoly.eval t :=
    l5c_pos_of_discr_ne_zero (by rwa [discrA, hred] at hA) hA0 fun t ht ↦
      (hnn t ⟨ht.1.le, ht.2.le⟩).1
  have hposB : ∀ t ∈ Ico 0 (firstSwitchTime (cellPoint p)), 0 < gB (p, t) := by
    intro t ht
    rw [← hBred]
    refine l5c_pos_of_discr_ne_zero hB (by rwa [hBred]) (fun t ht ↦ ?_) t ht
    rw [hBred]
    have := (hnn t ⟨ht.1.le, ht.2.le⟩).2
    rw [hBfac] at this
    exact nonneg_of_mul_nonneg_right this ht.1
  have hlow := l5c_lower (s := s) (u := u) (l5c_continuous_chiA u) hgB hposA hposB
    (Eventually.of_forall fun q t ht ↦
      ⟨fun h ↦ h.le, fun h ↦ by rw [hBfac]; exact mul_nonneg ht.le h.le⟩)
  obtain ⟨h1, h2⟩ := l5c_scheme hu hs (hs hp) (eventually_mem_nhdsWithin.mono hfc) hfcp hlow
  exact ⟨h1.continuousAt (hso.mem_nhds hp), h2.continuousAt (hso.mem_nhds hp)⟩

/-- **Where the first switching time can be discontinuous** (TeX 12139–12143): "The first switching
time `t_sw` is a discontinuous function on the cell. The discontinuities can only appear along the
loci `Δ_{A,0} = 0`, `Δ_{B,1} = 0` and `res_AB = 0`." On a big open cell, off these loci, `t_sw` and
the Poincaré map are continuous.

Proof route: off the loci the positive roots of `χ_{A,0}` and `χ_{B,1}` are simple and distinct and
none is `0`, so each is a sign change and the least of them is `t_sw`; simple real roots depend
continuously on the coefficients, which are continuous in `p`, and no root can enter `(0, ∞)`
through `0` (`χ_{A,0}(0) ≠ 0 ≠ χ_{B,1}(0)`) or through a complex pair (`Δ ≠ 0`); finally
`F = z(t_sw)` and `classOf` is continuous (`continuousOn_classOf`). (On the faces of the cells,
which the book's claim leaves out, the switching time may tend to `0`; see Proposition 15.2.2 and
REPORT.md, E70.)

Proved along this route (`l5c_openBox`, `l5c_scheme`). The hypothesis `res_AB ≠ 0` is the book's
(the locus `res_AB = 0` of TeX 12141–12142) and is not used: `t_sw` is the least time at which
`χ_A < 0` or `χ_B < 0`, and a common simple root of `χ_{A,0}` and `χ_{B,1}` is still a sign change
of one of them. The statement is kept as printed (REPORT.md, Section 5). -/
theorem continuousAt_firstSwitchTime_of_ne_zero :
    (∀ p ∈ openBoxOne, discrA ζ (cellPoint p) ≠ 0 → discrB ζ (cellPoint p) ≠ 0 →
      resAB ζ (cellPoint p) ≠ 0 →
      ContinuousAt (fun q ↦ firstSwitchTime (cellPoint q)) p ∧
        ContinuousAt (fun q ↦ poincareAngZero (cellClass q)) p) ∧
    ∀ p ∈ openBoxTwo, discrA (ζ ^ 2) (cellPoint p) ≠ 0 → discrB (ζ ^ 2) (cellPoint p) ≠ 0 →
      resAB (ζ ^ 2) (cellPoint p) ≠ 0 →
      ContinuousAt (fun q ↦ firstSwitchTime (cellPoint q)) p ∧
        ContinuousAt (fun q ↦ poincareAngZero (cellClass q)) p := by
  have h0 := (l5c_continuous_im 0).comp (continuous_fst (X := Fin 3 → ℝ) (Y := ℝ))
  have h1 := (l5c_continuous_im 1).comp (continuous_fst (X := Fin 3 → ℝ) (Y := ℝ))
  constructor
  · intro p hp hA hB _
    have hm := multA_multB_of_mem_openBox.1 p hp
    have hBc : chiB ζ (cellPoint p) =
        ⟨1 / 12, (cellPoint p 0).im / 2, (cellPoint p 1).im, 0⟩ := by
      rw [(chiA_chiB_eq _).2.1, l5c_im2]
    refine l5c_openBox l5c_isOpen_openBoxOne l5c_openBoxOne_sub (Or.inl rfl)
      (fun q hq ↦ l5c_fc_one hq)
      (gB := fun x ↦ 1 / 12 * x.2 ^ 2 + (cellPoint x.1 0).im / 2 * x.2 + (cellPoint x.1 1).im)
      (((continuous_const.mul (continuous_snd.pow 2)).add
        ((h0.div_const 2).mul continuous_snd)).add h1) (fun q t ↦ ?_) hp hm.1 ?_ (fun t ↦ ?_) ?_
      hA hB
    · rw [(l5c_eval_chi _ t).2.1, l5c_im2]; ring
    · rw [(l5c_eval_chi _ 0).1, l5c_im2]
      have := l5c_x3_neg hp.1 hp.2.1
      nlinarith [l5c_sqrt3_pos]
    · rw [chiBRed, hBc, l5c_red hm.2 rfl, l5c_eval_quad]
    · have := mul_pos hp.1.1 (Real.sin_pos_of_pos_of_lt_pi hp.2.2.1 hp.2.2.2)
      simp only
      linarith [(l5c_cellPoint_apply p).2.2.2.1]
  · intro p hp hA hB _
    have hm := multA_multB_of_mem_openBox.2 p hp
    have hBc : chiB (ζ ^ 2) (cellPoint p) =
        ⟨-1 / 12, -(cellPoint p 0).im / 2, -(cellPoint p 1).im, 0⟩ := by
      rw [(chiA_chiB_eq _).2.2.2, l5c_im2, neg_zero]
    refine l5c_openBox l5c_isOpen_openBoxTwo l5c_openBoxTwo_sub (Or.inr rfl)
      (fun q hq ↦ l5c_fc_two (l5c_sub_cellTwoDomain (Or.inl hq)))
      (gB := fun x ↦ -1 / 12 * x.2 ^ 2 + -(cellPoint x.1 0).im / 2 * x.2 + -(cellPoint x.1 1).im)
      (((continuous_const.mul (continuous_snd.pow 2)).add
        ((h0.neg.div_const 2).mul continuous_snd)).add h1.neg) (fun q t ↦ ?_) hp hm.1 ?_
      (fun t ↦ ?_) ?_ hA hB
    · rw [(l5c_eval_chi _ t).2.2.2, l5c_im2]; ring
    · rw [(l5c_eval_chi _ 0).2.2.1, l5c_im2]
      have := l5c_x3_neg hp.1 hp.2.1
      nlinarith [l5c_sqrt3_pos]
    · rw [chiBRed, hBc, l5c_red hm.2 rfl, l5c_eval_quad]
    · have := mul_pos hp.1.1 (neg_pos.2 (Real.sin_neg_of_neg_of_neg_pi_lt hp.2.2.2 hp.2.2.1))
      simp only
      linarith [(l5c_cellPoint_apply p).2.2.2.1]

/-! ### The top face of the first big cell -/

/-- "The first switching time is then a continuous function on the cell. If we identify this cell
with the top face `θ₂ = π` of the first three-cell `𝒞₃(ζ)⁰`, then the dynamical system extends
continuously from the interior of the first big cell to its top face" (TeX 12233–12235).

Proof route: near the top face `χ_B = t (y₂ + y₁ t/2 + t²/12) > 0` for `t > 0` (`y₂ ≥ 0`, `y₁ > 0`),
and the unique positive root of `χ_{A,0}` is simple (`topFaceOne_switching`), so it varies
continuously and no other positive root appears nearby.

Proved along this route (`l5c_scheme`); the simplicity of the root is not needed: before the root
`χ_{A,0}` is positive at the face point, hence nearby, and right after it the control is beaten. -/
theorem continuousWithinAt_topFaceOne {p : Fin 3 → ℝ} (hp : p ∈ topFaceOne) :
    ContinuousWithinAt (fun q ↦ firstSwitchTime (cellPoint q)) (openBoxOne ∪ topFaceOne) p ∧
      ContinuousWithinAt (fun q ↦ poincareAngZero (cellClass q)) (openBoxOne ∪ topFaceOne) p := by
  obtain ⟨hfcp, -, -, -, T, -, hroots, hsw⟩ := topFaceOne_switching hp
  have hz := l5c_cellPoint_ne_zero p
  have hs : openBoxOne ∪ topFaceOne ⊆ cellDomain :=
    union_subset l5c_openBoxOne_sub l5c_topFaceOne_sub
  have hfc : ∀ q ∈ openBoxOne ∪ topFaceOne, firstControl (cellPoint q) = ζ := by
    rintro q (hq | hq)
    · exact l5c_fc_one hq
    · exact (topFaceOne_switching hq).1
  -- `χ_A > 0` on `[0, t_sw)` at `p`: its only positive root is `t_sw`
  have hposA : ∀ t ∈ Ico 0 (firstSwitchTime (cellPoint p)),
      0 < (chiA ζ (cellPoint p)).toPoly.eval t := by
    intro t ht
    rcases ht.1.eq_or_lt with rfl | ht0
    · rw [(l5c_eval_chi _ 0).1, l5c_im2]
      have := l5c_x3_neg hp.1 hp.2.1
      nlinarith [l5c_sqrt3_pos]
    · refine lt_of_le_of_ne (l5c_nonneg_at (Or.inl rfl) hz hfcp ⟨ht0.le, ht.2.le⟩).1 fun h ↦ ?_
      have hmem : t ∈ {t : ℝ | 0 < t ∧ (chiA ζ (cellPoint p)).toPoly.eval t = 0} := ⟨ht0, h.symm⟩
      rw [hroots, mem_singleton_iff] at hmem
      have := ht.2
      rw [hsw, hmem] at this
      exact lt_irrefl _ this
  -- `y₁ > 0` at `p`
  have hy1 : 0 < (cellPoint p 0).im := by
    rw [(l5c_cellPoint_apply p).2.1, hp.2.2, Real.sin_pi_sub]
    exact mul_pos (sub_pos.2 hp.1.2) (Real.sin_pos_of_pos_of_lt_pi hp.2.1.1 hp.2.1.2)
  have hlow := l5c_lower (s := openBoxOne ∪ topFaceOne) (u := ζ)
    (T := firstSwitchTime (cellPoint p))
    (gA := fun x ↦ (chiA ζ (cellPoint x.1)).toPoly.eval x.2)
    (gB := fun x ↦ x.2 / 12 + (cellPoint x.1 0).im / 2) (l5c_continuous_chiA ζ)
    ((continuous_snd.div_const 12).add
      (((l5c_continuous_im 0).comp continuous_fst).div_const 2)) hposA
    (fun t ht ↦ by simp only; linarith [ht.1]) ?_
  · exact l5c_scheme (Or.inl rfl) hs (hs (Or.inr hp)) (eventually_mem_nhdsWithin.mono hfc) hfcp
      hlow
  · -- near the face, `χ_B = t² (t/12 + y₁/2) + y₂ t` with `y₂ ≥ 0`
    filter_upwards [eventually_mem_nhdsWithin] with q hq t ht
    refine ⟨fun h ↦ h.le, fun h ↦ ?_⟩
    have hy2 : 0 ≤ (cellPoint q 1).im := by
      rw [(l5c_cellPoint_apply q).2.2.2.1]
      rcases hq with hq | hq
      · exact mul_nonneg hq.1.1.le (Real.sin_nonneg_of_nonneg_of_le_pi hq.2.2.1.le hq.2.2.2.le)
      · rw [hq.2.2, Real.sin_pi, mul_zero]
    rw [(l5c_eval_chi _ t).2.1, l5c_im2]
    nlinarith [mul_nonneg (sq_nonneg t) h.le, mul_nonneg hy2 ht.le]

/-! ### The front and back faces of the first big cell -/

/-- "If we attach each point `(r₂, ψ, θ₂)` of this cell to the point on the front and back boundary
faces `ψ ∈ {0, π}` of the first 3-cell with the same coordinates `(r₂, ψ, θ₂)`, then the dynamical
system on the interior of the 3-cell extends continuously to the front and back faces, in agreement
with the dynamics on the 2-cell `𝒞₂(ζ)`" (TeX 12268–12276), at the points of the relative interior
where the reduced polynomials `χ_{A,1}`, `χ_{B,1}` have simple roots (`Δ_{A,1}, Δ_{B,1} ≠ 0`). Some
restriction is forced: the book claims continuity on the whole 2-cell, which fails where the map of
the 2-cell itself is discontinuous. These hypotheses are sufficient, not minimal; the book's
"continuous extension" elsewhere on the 2-cell is the subject of Proposition 15.3.2.

Proof route: near such a face point, in the open cell, `χ_A` has a root near `0` that is negative
(`χ_A(0) = -(√3/2) x₃ > 0` and `χ_A'(0) > 0`) and two roots near those of `χ_{A,1}`; `χ_{B,1}` is
near the face's `χ_{B,1}`; the least positive sign change varies continuously.

Proved along this route (`l5c_scheme`): `χ_A = -(√3/2) x₃ + t g_A` with `x₃ ≤ 0` and `g_A` the
face's `χ_{A,1}` at the face point, `χ_B = t g_B` with `g_B` the face's `χ_{B,1}`. A common root of
`χ_{A,1}` and `χ_{B,1}` (`res_AB = 0`) does not matter: a common simple root is still a sign change
of one of them. -/
theorem continuousWithinAt_frontBackOne {p : Fin 3 → ℝ} (hp : p ∈ frontBackOne) (hr : 0 < p 0)
    (hθ : p 2 ∈ Ioo (π / 3) π) (hA : discrA ζ (cellPoint p) ≠ 0)
    (hB : discrB ζ (cellPoint p) ≠ 0) :
    ContinuousWithinAt (fun q ↦ poincareAngZero (cellClass q)) (openBoxOne ∪ frontBackOne) p := by
  obtain ⟨hfcp, hmA, hmB⟩ := frontBackOne_cover_and_switching.2 p hp hr hθ
  have hz := l5c_cellPoint_ne_zero p
  have hs : openBoxOne ∪ frontBackOne ⊆ cellDomain :=
    union_subset l5c_openBoxOne_sub l5c_frontBackOne_sub
  -- near `p` the first control is `ζ`
  have hU : {q : Fin 3 → ℝ | 0 < q 0 ∧ q 2 ∈ Ioo (π / 3) π} ∈ 𝓝 p :=
    ((isOpen_Ioi.preimage (continuous_apply 0)).inter
      (isOpen_Ioo.preimage (continuous_apply 2))).mem_nhds ⟨hr, hθ⟩
  have hfc : ∀ᶠ q in 𝓝[openBoxOne ∪ frontBackOne] p, firstControl (cellPoint q) = ζ := by
    filter_upwards [eventually_mem_nhdsWithin, nhdsWithin_le_nhds hU] with q hq hqU
    rcases hq with hq | hq
    · exact l5c_fc_one hq
    · exact (frontBackOne_cover_and_switching.2 q hq hqU.1 hqU.2).1
  -- at `p`, `x₃ = 0`
  have hx3 : (cellPoint p 2).re = 0 := by
    rw [(l5c_cellPoint_apply p).2.2.2.2.1]
    rcases hp.2.1 with h | h <;> rw [h] <;> simp [Real.sin_pi]
  have h00 := (l5c_continuous_im 0).comp (continuous_fst (X := Fin 3 → ℝ) (Y := ℝ))
  have h01 := (l5c_continuous_re 0).comp (continuous_fst (X := Fin 3 → ℝ) (Y := ℝ))
  have h10 := (l5c_continuous_im 1).comp (continuous_fst (X := Fin 3 → ℝ) (Y := ℝ))
  have h11 := (l5c_continuous_re 1).comp (continuous_fst (X := Fin 3 → ℝ) (Y := ℝ))
  -- `χ_A = -(√3/2) x₃ + t g_A`, `χ_B = t g_B`
  have hAfac : ∀ q t, (chiA ζ (cellPoint q)).toPoly.eval t = -(√3 * (cellPoint q 2).re) / 2 +
      t * (-1 / 12 * t ^ 2 + ((cellPoint q 0).im - √3 * (cellPoint q 0).re) / 4 * t +
        ((cellPoint q 1).im - √3 * (cellPoint q 1).re) / 2) := by
    intro q t; rw [(l5c_eval_chi _ t).1, l5c_im2]; ring
  have hBfac : ∀ q t, (chiB ζ (cellPoint q)).toPoly.eval t =
      t * (1 / 12 * t ^ 2 + (cellPoint q 0).im / 2 * t + (cellPoint q 1).im) := by
    intro q t; rw [(l5c_eval_chi _ t).2.1, l5c_im2]; ring
  -- the reduced polynomials at `p`
  have hAred : ∀ t, (chiARed ζ (cellPoint p)).eval t = -1 / 12 * t ^ 2 +
      ((cellPoint p 0).im - √3 * (cellPoint p 0).re) / 4 * t +
        ((cellPoint p 1).im - √3 * (cellPoint p 1).re) / 2 := by
    intro t
    have hAc : chiA ζ (cellPoint p) = ⟨-1 / 12, ((cellPoint p 0).im - √3 * (cellPoint p 0).re) / 4,
        ((cellPoint p 1).im - √3 * (cellPoint p 1).re) / 2, 0⟩ := by
      rw [(chiA_chiB_eq _).1, l5c_im2, hx3]; norm_num
    rw [chiARed, hAc, l5c_red hmA rfl, l5c_eval_quad]
  have hBred : ∀ t, (chiBRed ζ (cellPoint p)).eval t =
      1 / 12 * t ^ 2 + (cellPoint p 0).im / 2 * t + (cellPoint p 1).im := by
    intro t
    have hBc : chiB ζ (cellPoint p) =
        ⟨1 / 12, (cellPoint p 0).im / 2, (cellPoint p 1).im, 0⟩ := by
      rw [(chiA_chiB_eq _).2.1, l5c_im2]
    rw [chiBRed, hBc, l5c_red hmB rfl, l5c_eval_quad]
  have hnn := fun t (ht : t ∈ Icc 0 (firstSwitchTime (cellPoint p))) ↦
    l5c_nonneg_at (Or.inl rfl) hz hfcp ht
  obtain ⟨-, -, h1re, h1im, -, -⟩ := l5c_cellPoint_apply p
  have hposA : ∀ t ∈ Ico 0 (firstSwitchTime (cellPoint p)), 0 < -1 / 12 * t ^ 2 +
      ((cellPoint p 0).im - √3 * (cellPoint p 0).re) / 4 * t +
        ((cellPoint p 1).im - √3 * (cellPoint p 1).re) / 2 := by
    intro t ht
    rw [← hAred]
    refine l5c_pos_of_discr_ne_zero hA ?_ (fun t ht ↦ ?_) t ht
    · -- `χ_{A,1}(0) = r₂ sin(θ₂ - π/3) > 0`
      have hs3 : 0 < Real.sin (p 2 - π / 3) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
      rw [Real.sin_sub, Real.sin_pi_div_three, Real.cos_pi_div_three] at hs3
      rw [hAred, h1re, h1im]
      nlinarith [mul_pos hr hs3]
    · rw [hAred]
      have := (hnn t ⟨ht.1.le, ht.2.le⟩).1
      rw [hAfac, hx3, mul_zero, neg_zero, zero_div, zero_add] at this
      exact nonneg_of_mul_nonneg_right this ht.1
  have hposB : ∀ t ∈ Ico 0 (firstSwitchTime (cellPoint p)),
      0 < 1 / 12 * t ^ 2 + (cellPoint p 0).im / 2 * t + (cellPoint p 1).im := by
    intro t ht
    rw [← hBred]
    refine l5c_pos_of_discr_ne_zero hB ?_ (fun t ht ↦ ?_) t ht
    · -- `χ_{B,1}(0) = y₂ = r₂ sin θ₂ > 0`
      rw [hBred, h1im]
      have := mul_pos hr (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos]) hθ.2)
      linarith
    · rw [hBred]
      have := (hnn t ⟨ht.1.le, ht.2.le⟩).2
      rw [hBfac] at this
      exact nonneg_of_mul_nonneg_right this ht.1
  have hlow := l5c_lower (s := openBoxOne ∪ frontBackOne) (u := ζ)
    (T := firstSwitchTime (cellPoint p))
    (gA := fun x ↦ -1 / 12 * x.2 ^ 2 +
      ((cellPoint x.1 0).im - √3 * (cellPoint x.1 0).re) / 4 * x.2 +
        ((cellPoint x.1 1).im - √3 * (cellPoint x.1 1).re) / 2)
    (gB := fun x ↦ 1 / 12 * x.2 ^ 2 + (cellPoint x.1 0).im / 2 * x.2 + (cellPoint x.1 1).im)
    (by fun_prop) (by fun_prop) hposA hposB ?_
  · exact (l5c_scheme (Or.inl rfl) hs (hs (Or.inr hp)) hfc hfcp hlow).2
  · filter_upwards [eventually_mem_nhdsWithin] with q hq t ht
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · rw [hAfac]
      have := l5c_x3_nonpos (hs hq)
      nlinarith [l5c_sqrt3_pos, mul_pos ht h]
    · rw [hBfac]
      exact mul_nonneg ht.le h.le

/-! ### The root-based maps `F_A`, `F_B` of the top face of the second big cell -/

/-- The coefficients of `χ_A` for the control `ζ²` at `cellPoint q`:
`χ_A = t³/12 + b t² + c t + d`. -/
private noncomputable def l5c_b (q : Fin 3 → ℝ) : ℝ :=
  -((cellPoint q 0).im + √3 * (cellPoint q 0).re) / 4

private noncomputable def l5c_c (q : Fin 3 → ℝ) : ℝ :=
  -((cellPoint q 1).im + √3 * (cellPoint q 1).re) / 2

private noncomputable def l5c_d (q : Fin 3 → ℝ) : ℝ :=
  -((cellPoint q 2).im + √3 * (cellPoint q 2).re) / 2

private lemma l5c_evalA2 (q : Fin 3 → ℝ) (t : ℝ) :
    (chiA (ζ ^ 2) (cellPoint q)).toPoly.eval t =
      t ^ 3 / 12 + l5c_b q * t ^ 2 + l5c_c q * t + l5c_d q := by
  rw [(l5c_eval_chi _ t).2.2.1, l5c_b, l5c_c, l5c_d]; ring

private lemma l5c_continuous_b : Continuous l5c_b :=
  ((l5c_continuous_im 0).add (continuous_const.mul (l5c_continuous_re 0))).neg.div_const 4

private lemma l5c_continuous_c : Continuous l5c_c :=
  ((l5c_continuous_im 1).add (continuous_const.mul (l5c_continuous_re 1))).neg.div_const 2

private lemma l5c_hasDerivAt_cubic (b c d t : ℝ) :
    HasDerivAt (fun t ↦ t ^ 3 / 12 + b * t ^ 2 + c * t + d) (t ^ 2 / 4 + 2 * b * t + c) t := by
  have h := ((((hasDerivAt_pow 3 t).div_const 12).add ((hasDerivAt_pow 2 t).const_mul b)).add
    ((hasDerivAt_id t).const_mul c)).add_const d
  exact h.congr_deriv (by norm_num; ring)

/-- On `𝒞₂(ζ², 0, 2)`: `c = -(√3/2) r₂ < 0` and `d = √3 r₁ r₂ sin ψ > 0`. -/
private lemma l5c_face_cd {q : Fin 3 → ℝ} (hq : q ∈ topFaceTwo) : l5c_c q < 0 ∧ 0 < l5c_d q := by
  obtain ⟨-, -, h1re, h1im, h2re, h2im⟩ := l5c_cellPoint_apply q
  rw [l5c_c, l5c_d, h1re, h1im, h2re, h2im, hq.2.2, Real.cos_zero, Real.sin_zero]
  have hS := Real.sin_pos_of_pos_of_lt_pi hq.2.1.1 hq.2.1.2
  have := mul_pos (mul_pos (sub_pos.2 hq.1.2) hq.1.1) hS
  constructor <;> nlinarith [l5c_sqrt3_pos, hq.1.1]

private lemma l5c_face_eval0 {q : Fin 3 → ℝ} (hq : q ∈ topFaceTwo) :
    0 < (chiA (ζ ^ 2) (cellPoint q)).toPoly.eval 0 := by
  rw [l5c_evalA2]
  simpa using (l5c_face_cd hq).2

/-- A real polynomial positive at `0` is positive before its least positive root. -/
private lemma l5c_pos_below (P : ℝ[X]) (h0 : 0 < P.eval 0) :
    ∀ t ∈ Ico 0 (leastPosRoot P), 0 < P.eval t := by
  intro t ht
  rcases ht.1.eq_or_lt with rfl | ht0
  · exact h0
  by_contra hle
  obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc' ht.1 P.continuousOn ⟨not_lt.1 hle, h0.le⟩
  have hc0 : 0 < c := lt_of_le_of_ne hc.1 (by rintro rfl; exact h0.ne' hfc)
  have hbdd : BddBelow {t | 0 < t ∧ P.eval t = 0} := ⟨0, fun s hs ↦ hs.1.le⟩
  have := csInf_le hbdd (⟨hc0, hfc⟩ : c ∈ {t | 0 < t ∧ P.eval t = 0})
  exact absurd (this.trans hc.2) (not_le.2 ht.2)

/-- The least positive root is a positive root when there is one. -/
private lemma l5c_leastPosRoot_mem (P : ℝ[X]) (hP : P ≠ 0) (hne : ∃ t, 0 < t ∧ P.eval t = 0) :
    0 < leastPosRoot P ∧ P.eval (leastPosRoot P) = 0 := by
  have hfin : {t | 0 < t ∧ P.eval t = 0}.Finite :=
    (finite_setOfPred_isRoot hP).subset fun t ht ↦ ht.2
  exact hfin.isClosed.csInf_mem hne ⟨0, fun s hs ↦ hs.1.le⟩

/-- On `𝒞₂^A` (`Δ_{A,0} ≥ 0`) the polynomial `χ_{A,0}` has a positive root
(`topFaceTwo_switching`). -/
private lemma l5c_exists_posRoot {q : Fin 3 → ℝ} (hq : q ∈ topFaceTwoA) :
    ∃ t, 0 < t ∧ (chiA (ζ ^ 2) (cellPoint q)).toPoly.eval t = 0 := by
  have h := (topFaceTwo_switching hq.1).2.2.2.2.2.1 hq.2
  obtain ⟨t, ht⟩ := Multiset.card_pos_iff_exists_mem.1 (by rw [h]; norm_num)
  rw [Multiset.mem_filter] at ht
  exact ⟨t, ht.2, (mem_roots'.1 ht.1).2⟩

/-- `χ_A' ≥ 0` propagates to the right when `χ_A'(0) = c < 0`: if the derivative of
`t³/12 + b t² + c t + d` is nonnegative at `s > 0`, the cubic is nondecreasing on `[s, ∞)`. -/
private lemma l5c_cubic_mono {b c d s t : ℝ} (hc : c < 0) (hs : 0 < s)
    (hd : 0 ≤ s ^ 2 / 4 + 2 * b * s + c) (hst : s ≤ t) :
    s ^ 3 / 12 + b * s ^ 2 + c * s + d ≤ t ^ 3 / 12 + b * t ^ 2 + c * t + d := by
  have hb : 0 < s / 4 + 2 * b := by
    by_contra h
    rw [not_lt] at h
    nlinarith
  have h1 : 0 ≤ (t + 2 * s) / 12 + b := by linarith
  have e : t ^ 3 / 12 + b * t ^ 2 + c * t + d - (s ^ 3 / 12 + b * s ^ 2 + c * s + d) =
      (t - s) * ((s ^ 2 / 4 + 2 * b * s + c) + (t - s) * ((t + 2 * s) / 12 + b)) := by ring
  have := mul_nonneg (sub_nonneg.2 hst) (add_nonneg hd (mul_nonneg (sub_nonneg.2 hst) h1))
  linarith

/-- **`F_A` lands on a wall** (TeX 12413–12422): at the least positive root `t₀ ≤ t_B` of `χ_{A,0}`
the controls `ζ²` and `1` tie and maximize (`ζ` does not beat `ζ²` before `t_B`), so `z₃(t₀) ∈ 𝒲`;
`H_F⁺` is conserved along the first control, and `t₀ ≤ t_sw`, so `z(t₀) ≠ 0`. -/
private lemma l5c_cellMapA_mem {p : Fin 3 → ℝ} (hp : p ∈ topFaceTwoA) :
    cellMapA (cellPoint p) ∈ sectionZero := by
  have hz := l5c_cellPoint_ne_zero p
  have hfc : firstControl (cellPoint p) = ζ ^ 2 := (topFaceTwo_switching hp.1).1
  have h0 := l5c_face_eval0 hp.1
  have hP : (chiA (ζ ^ 2) (cellPoint p)).toPoly ≠ 0 := by
    intro h; rw [h, eval_zero] at h0; exact lt_irrefl 0 h0
  have hne := l5c_exists_posRoot hp
  obtain ⟨ht₀, hroot⟩ := l5c_leastPosRoot_mem _ hP hne
  have htB := leastPosRoot_chiA_le_of_mem_topFaceTwo hp.1 hne
  have hy2 : (cellPoint p 1).im = 0 := by
    rw [(l5c_cellPoint_apply p).2.2.2.1, hp.1.2.2, Real.sin_zero, mul_zero]
  -- the control `ζ²` is not beaten on `[0, t₀]`
  have hnb : ∀ t ∈ Icc 0 (leastPosRoot (chiA (ζ ^ 2) (cellPoint p)).toPoly), ∀ v ∈ VT,
      ham (flow t (cellPoint p) (ζ ^ 2)) v ≤ ham (flow t (cellPoint p) (ζ ^ 2)) (ζ ^ 2) := by
    intro t ht
    refine (l5c_notBeaten_iff (Or.inr rfl) _ t).2 ⟨?_, ?_⟩
    · rcases ht.2.lt_or_eq with h | h
      · exact (l5c_pos_below _ h0 t ⟨ht.1, h⟩).le
      · rw [h, hroot]
    · rw [(l5c_eval_chi _ t).2.2.2, hy2, l5c_im2]
      nlinarith [mul_nonneg (sq_nonneg t) (by linarith [ht.2] :
        0 ≤ -(cellPoint p 0).im / 2 - t / 12)]
  -- `t₀ ≤ t_sw`
  have hsw : leastPosRoot (chiA (ζ ^ 2) (cellPoint p)).toPoly ≤ firstSwitchTime (cellPoint p) := by
    obtain ⟨t, ht, v, hv, hlt⟩ := firstControl_beaten hz one_pos
    rw [firstSwitchTime]
    refine le_csInf ⟨t, (firstSwitchTime_pos hz).trans ht.1, v, hv, hlt⟩ ?_
    rintro s ⟨hs, v, hv, hlt⟩
    by_contra hlt'
    rw [not_le] at hlt'
    rw [hfc] at hlt
    exact absurd (hnb s ⟨hs.le, hlt'.le⟩ v hv) (not_le.2 hlt)
  have hmax := hnb _ ⟨ht₀.le, le_rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · have := flow_firstControl_ne_zero hz ⟨ht₀.le, hsw⟩
    rwa [hfc] at this
  · -- the tie between `ζ²` and `1`
    have htie : ham (flow (leastPosRoot (chiA (ζ ^ 2) (cellPoint p)).toPoly) (cellPoint p) (ζ ^ 2))
        1 = ham (flow (leastPosRoot (chiA (ζ ^ 2) (cellPoint p)).toPoly) (cellPoint p) (ζ ^ 2))
          (ζ ^ 2) := by
      have := l5c_chiA_eval (ζ ^ 2) (cellPoint p) (leastPosRoot (chiA (ζ ^ 2) (cellPoint p)).toPoly)
      rw [hroot, eq_comm, div_eq_zero_iff, sub_eq_zero] at this
      exact (this.resolve_right l5c_sqrt3_pos.ne').symm
    exact mem_walls_of_maximizers ζ_sq_mem_VT one_mem_VT l5c_ζ_sq_ne_one
      (fun x hx ↦ (l5c_ham_le_iff _ _ _).1 (hmax x hx))
      (fun x hx ↦ (l5c_ham_le_iff _ _ _).1 ((hmax x hx).trans_eq htie.symm))
  · have h0' := hnb 0 ⟨le_rfl, ht₀.le⟩
    rw [flow_zero] at h0'
    change hamMax (flow (leastPosRoot (chiA (ζ ^ 2) (cellPoint p)).toPoly) (cellPoint p) (ζ ^ 2))
      = 0
    rw [hamMax_eq_of_forall_le ζ_sq_mem_VT hmax, ham_flow, ← hamMax_eq_of_forall_le ζ_sq_mem_VT h0']
    exact (cellPoint_mem_sectionZero (l5c_topFaceTwo_sub hp.1)).2.2

/-- **Continuity of the least positive root of `χ_{A,0}` on `𝒞₂^A`.** At a sign change this is
`tendsto_sInf_pos_zeros_of_signChange`. At a double root `t₀` (`Δ_{A,0} = 0`), `χ_A'(t₀) = 0`, so
`χ_A'(t₀ + ε/2) > 0`, also at nearby points; a nearby `χ_{A,0}` with `Δ_{A,0} ≥ 0` has a positive
root, and if all its positive roots exceeded `t₀ + ε` it would be positive on `[0, t₀ + ε/2]` and
nondecreasing after (`l5c_cubic_mono`), with no positive root at all. -/
private lemma l5c_tendsto_leastPosRoot {p₀ : Fin 3 → ℝ} (hp₀ : p₀ ∈ topFaceTwoA) :
    Tendsto (fun q ↦ leastPosRoot (chiA (ζ ^ 2) (cellPoint q)).toPoly) (𝓝[topFaceTwoA] p₀)
      (𝓝 (leastPosRoot (chiA (ζ ^ 2) (cellPoint p₀)).toPoly)) := by
  have hcont := l5c_continuous_chiA (ζ ^ 2)
  obtain ⟨hc₀, -⟩ := l5c_face_cd hp₀.1
  have h0 := l5c_face_eval0 hp₀.1
  have hP : (chiA (ζ ^ 2) (cellPoint p₀)).toPoly ≠ 0 := by
    intro h; rw [h, eval_zero] at h0; exact lt_irrefl 0 h0
  obtain ⟨ht₀, hroot⟩ := l5c_leastPosRoot_mem _ hP (l5c_exists_posRoot hp₀)
  have hpos := l5c_pos_below _ h0
  by_cases hsc : ∀ ε > 0, ∃ t ∈ Ioo (leastPosRoot (chiA (ζ ^ 2) (cellPoint p₀)).toPoly)
      (leastPosRoot (chiA (ζ ^ 2) (cellPoint p₀)).toPoly + ε),
      (chiA (ζ ^ 2) (cellPoint p₀)).toPoly.eval t < 0
  · -- a sign change: the general lemma
    exact (tendsto_sInf_pos_zeros_of_signChange
      (f := fun q t ↦ (chiA (ζ ^ 2) (cellPoint q)).toPoly.eval t) hcont ht₀ hpos hsc).mono_left
      nhdsWithin_le_nhds
  -- a double root: `χ_A'(t₀) = 0`
  push Not at hsc
  obtain ⟨ε₀, hε₀, hge⟩ := hsc
  set t₀ := leastPosRoot (chiA (ζ ^ 2) (cellPoint p₀)).toPoly with ht₀_def
  have hmin : IsLocalMin (fun t ↦ t ^ 3 / 12 + l5c_b p₀ * t ^ 2 + l5c_c p₀ * t + l5c_d p₀) t₀ := by
    filter_upwards [Ioo_mem_nhds ht₀ (lt_add_of_pos_right t₀ hε₀)] with t ht
    rw [← l5c_evalA2, ← l5c_evalA2, hroot]
    rcases lt_trichotomy t t₀ with h | h | h
    · exact (hpos t ⟨ht.1.le, h⟩).le
    · rw [h, hroot]
    · exact hge t ⟨h, ht.2⟩
  have hd' : t₀ ^ 2 / 4 + 2 * l5c_b p₀ * t₀ + l5c_c p₀ = 0 :=
    hmin.hasDerivAt_eq_zero (l5c_hasDerivAt_cubic _ _ _ _)
  have hb : 0 < t₀ / 4 + 2 * l5c_b p₀ := by
    by_contra h
    rw [not_lt] at h
    nlinarith
  change Tendsto (fun q ↦ sInf {t : ℝ | 0 < t ∧ (chiA (ζ ^ 2) (cellPoint q)).toPoly.eval t = 0})
    _ _
  apply tendsto_csInf_of_eventually
  · intro ε hε
    have hs0 : 0 < t₀ + ε / 2 := by linarith
    have hds : 0 < (t₀ + ε / 2) ^ 2 / 4 + 2 * l5c_b p₀ * (t₀ + ε / 2) + l5c_c p₀ := by
      have e : (t₀ + ε / 2) ^ 2 / 4 + 2 * l5c_b p₀ * (t₀ + ε / 2) + l5c_c p₀ =
          (t₀ ^ 2 / 4 + 2 * l5c_b p₀ * t₀ + l5c_c p₀) +
            ε / 2 * (t₀ / 2 + ε / 8 + 2 * l5c_b p₀) := by
        ring
      rw [e, hd', zero_add]
      exact mul_pos (half_pos hε) (by linarith)
    have hev : ∀ᶠ q in 𝓝 p₀, 0 < (t₀ + ε / 2) ^ 2 / 4 + 2 * l5c_b q * (t₀ + ε / 2) + l5c_c q :=
      ((continuous_const.add ((continuous_const.mul l5c_continuous_b).mul continuous_const)).add
        l5c_continuous_c).continuousAt.eventually (lt_mem_nhds hds)
    filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with q hq hqA
    by_contra hno
    push Not at hno
    obtain ⟨hcq, -⟩ := l5c_face_cd hqA.1
    obtain ⟨r, hr0, hr⟩ := l5c_exists_posRoot hqA
    have hq0 := l5c_face_eval0 hqA.1
    -- `χ_A > 0` on `[0, t₀ + ε/2]`, then nondecreasing
    have hPs : 0 < (chiA (ζ ^ 2) (cellPoint q)).toPoly.eval (t₀ + ε / 2) := by
      by_contra hle
      obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc' hs0.le
        (chiA (ζ ^ 2) (cellPoint q)).toPoly.continuousOn ⟨not_lt.1 hle, hq0.le⟩
      have hc0 : 0 < c := lt_of_le_of_ne hc.1 (by rintro rfl; exact hq0.ne' hfc)
      have := hno c ⟨hc0, hfc⟩
      linarith [hc.2]
    have hrs : t₀ + ε / 2 ≤ r := by linarith [hno r ⟨hr0, hr⟩]
    have := l5c_cubic_mono (d := l5c_d q) hcq hs0 hq.le hrs
    rw [← l5c_evalA2, ← l5c_evalA2, hr] at this
    linarith
  · intro ε hε
    have := eventually_forall_pos_of_isCompact
      (f := fun q t ↦ (chiA (ζ ^ 2) (cellPoint q)).toPoly.eval t)
      (isCompact_Icc (a := 0) (b := t₀ - ε)) (fun t _ ↦ hcont.continuousAt)
      (fun t ht ↦ hpos t ⟨ht.1, by linarith [ht.2]⟩)
    filter_upwards [nhdsWithin_le_nhds this] with q hq t ⟨ht, hft⟩
    by_contra hle
    exact (hq t ⟨ht.le, not_lt.1 hle⟩).ne' hft

/-- **`F_A` and `F_B` are continuous** (TeX 12419–12422): "The map `F` is discontinuous along the
discriminant locus `Δ_{A,0} = 0`. However, the first switching time and the Fuller–Poincaré map `F`
extend continuously to give `F_A` with domain `𝒞₂^A` and `F_B` with domain `𝒞₂^B`": `F_A` is
continuous on the closed part `𝒞₂^A = {Δ_{A,0} ≥ 0}` (the least positive root tends to the double
root at `Δ_{A,0} = 0`) and `F_B` on the closure `{Δ_{A,0} ≤ 0}` of `𝒞₂^B` in the face, both with
values in the section.

The book asserts this without argument. Proof: `t_B = -6 y₁` is continuous; on `{Δ_{A,0} > 0}` the
least positive root of `χ_{A,0}` is a sign change, which depends continuously on the coefficients
(`tendsto_sInf_pos_zeros_of_signChange`); at a double root (`Δ_{A,0} = 0`) the proof uses the
shape of `χ_{A,0}` on the face: `χ_A'(0) < 0`, so `χ_A` decreases and then increases, and a nearby
`χ_{A,0}` with `Δ_{A,0} ≥ 0` has a root near the double root (`l5c_tendsto_leastPosRoot`). (A
standard alternative is the continuity of the roots of a polynomial, in Mathlib's one-sided form
`Polynomial.exists_roots_norm_sub_lt_of_norm_coeff_sub_lt`, since a nearby `χ_{A,0}` with
`Δ_{A,0} ≥ 0` splits over `ℝ`.) At the least positive root `t₀ ≤ t_B`
(`leastPosRoot_chiA_le_of_mem_topFaceTwo`) the controls `ζ²` and `1` tie and maximize, so `F_A`
lands on a wall (`l5c_cellMapA_mem`); `F_B` lands in the section because it is the Poincaré map on
`{Δ_{A,0} ≤ 0}` (`firstSwitchTime_topFaceTwo`). -/
theorem continuousOn_cellMapA_cellMapB :
    (∀ p ∈ topFaceTwoA, cellMapA (cellPoint p) ∈ sectionZero) ∧
      ContinuousOn (fun p ↦ classOf (cellMapA (cellPoint p))) topFaceTwoA ∧
      (∀ p ∈ topFaceTwo, discrA (ζ ^ 2) (cellPoint p) ≤ 0 →
        cellMapB (cellPoint p) ∈ sectionZero) ∧
      ContinuousOn (fun p ↦ classOf (cellMapB (cellPoint p)))
        {p | p ∈ topFaceTwo ∧ discrA (ζ ^ 2) (cellPoint p) ≤ 0} := by
  have hB : ∀ p ∈ topFaceTwo, discrA (ζ ^ 2) (cellPoint p) ≤ 0 →
      cellMapB (cellPoint p) ∈ sectionZero := fun p hp hd ↦ by
    rw [← ((firstSwitchTime_topFaceTwo hp).1 hd).2]
    exact poincare_mem_sectionZero (cellPoint_mem_sectionZero (l5c_topFaceTwo_sub hp))
  refine ⟨fun p hp ↦ l5c_cellMapA_mem hp, fun p hp ↦ ?_, hB, ?_⟩
  · have hG : ContinuousWithinAt (fun q ↦ cellMapA (cellPoint q)) topFaceTwoA p :=
      (l5c_continuous_flow (ζ ^ 2)).continuousAt.comp_continuousWithinAt
        ((l5c_tendsto_leastPosRoot hp).prodMk_nhds l5c_continuous_cellPoint.continuousWithinAt)
    exact ContinuousWithinAt.comp (f := fun q ↦ cellMapA (cellPoint q))
      (continuousOn_classOf _ (l5c_cellMapA_mem hp)) hG fun q hq ↦ l5c_cellMapA_mem hq
  · have hG : Continuous fun p ↦ cellMapB (cellPoint p) :=
      (l5c_continuous_flow (ζ ^ 2)).comp
        ((continuous_const.mul (l5c_continuous_im 0)).prodMk l5c_continuous_cellPoint)
    exact continuousOn_classOf.comp hG.continuousOn fun q hq ↦ hB q hq.1 hq.2

/-! ### The top face of the second big cell -/

/-- "If we identify this `2`-cell with the top face `θ₂ = 0` of the second three-cell `𝒞₃(ζ²)⁰`,
then the dynamical system extends continuously from the interior of the second big cell to its top
face (with exceptional discontinuities, where the dynamical system is already discontinuous on
`𝒞₂(ζ², 0, 2)`)" (TeX 12239–12245): at the points of the face where `Δ_{A,0} ≠ 0`, since the map
of the face (`F_A` where `Δ_{A,0} > 0`, `F_B` where `Δ_{A,0} ≤ 0`) is discontinuous only on
`{Δ_{A,0} = 0}`. Where `Δ_{A,0} > 0` the least positive root of `χ_{A,0}` lies below `t_B`
(`firstSwitchTime_topFaceTwo`), so a root of `χ_{A,0}` at `t_B` is a larger root and does not
change the switch.

Proof route: in the open cell near the face, `χ_{B,1} = -(y₂ + y₁ t/2 + t²/12)` (`y₂ < 0` small) has
a positive root near `t_B` and a negative one near `0`; the roots of `χ_{A,0}` are near those of the
face.

Proved along this route (`l5c_scheme`): `χ_B = t² (-y₁/2 - t/12) - y₂ t` with `-y₂ ≥ 0`, and
`t_sw ≤ t_B` at the face point since `χ_B < 0` after `t_B`; `χ_{A,0} > 0` on `[0, t_sw)` at the
face point because a zero there would be a double root (`Δ_{A,0} ≠ 0`). -/
theorem continuousWithinAt_topFaceTwo {p : Fin 3 → ℝ} (hp : p ∈ topFaceTwo)
    (hA : discrA (ζ ^ 2) (cellPoint p) ≠ 0) :
    ContinuousWithinAt (fun q ↦ poincareAngZero (cellClass q)) (openBoxTwo ∪ topFaceTwo) p := by
  have hz := l5c_cellPoint_ne_zero p
  have hs : openBoxTwo ∪ topFaceTwo ⊆ cellDomain :=
    union_subset l5c_openBoxTwo_sub l5c_topFaceTwo_sub
  have hfc : ∀ q ∈ openBoxTwo ∪ topFaceTwo, firstControl (cellPoint q) = ζ ^ 2 := fun q hq ↦
    l5c_fc_two (l5c_sub_cellTwoDomain hq)
  have hfcp := hfc p (Or.inr hp)
  have hmA := (topFaceTwo_switching hp).2.1
  have hT₀ := firstSwitchTime_pos hz
  have hnn := fun t (ht : t ∈ Icc 0 (firstSwitchTime (cellPoint p))) ↦
    l5c_nonneg_at (Or.inr rfl) hz hfcp ht
  have hy2 : (cellPoint p 1).im = 0 := by
    rw [(l5c_cellPoint_apply p).2.2.2.1, hp.2.2, Real.sin_zero, mul_zero]
  -- `t_sw ≤ t_B`: after `t_B` the control `ζ` beats `ζ²`
  have hTB : firstSwitchTime (cellPoint p) ≤ -6 * (cellPoint p 0).im := by
    have := (hnn _ ⟨hT₀.le, le_rfl⟩).2
    rw [(l5c_eval_chi _ _).2.2.2, hy2, l5c_im2] at this
    by_contra h
    rw [not_le] at h
    nlinarith [mul_pos (pow_pos hT₀ 2) (by linarith : 0 < firstSwitchTime (cellPoint p) / 12 +
      (cellPoint p 0).im / 2)]
  have hred : chiARed (ζ ^ 2) (cellPoint p) = (chiA (ζ ^ 2) (cellPoint p)).toPoly := by
    rw [chiARed, hmA, pow_zero, divByMonic_one]
  have hposA : ∀ t ∈ Ico 0 (firstSwitchTime (cellPoint p)),
      0 < (chiA (ζ ^ 2) (cellPoint p)).toPoly.eval t := by
    refine l5c_pos_of_discr_ne_zero (by rwa [discrA, hred] at hA) ?_ fun t ht ↦
      (hnn t ⟨ht.1.le, ht.2.le⟩).1
    rw [(l5c_eval_chi _ 0).2.2.1, l5c_im2]
    have := l5c_x3_neg hp.1 hp.2.1
    nlinarith [l5c_sqrt3_pos]
  have hlow := l5c_lower (s := openBoxTwo ∪ topFaceTwo) (u := ζ ^ 2)
    (T := firstSwitchTime (cellPoint p))
    (gA := fun x ↦ (chiA (ζ ^ 2) (cellPoint x.1)).toPoly.eval x.2)
    (gB := fun x ↦ -(cellPoint x.1 0).im / 2 - x.2 / 12) (l5c_continuous_chiA _)
    ((((l5c_continuous_im 0).comp continuous_fst).neg.div_const 2).sub
      (continuous_snd.div_const 12)) hposA
    (fun t ht ↦ by simp only; linarith [ht.2, hTB]) ?_
  · exact (l5c_scheme (Or.inr rfl) hs (hs (Or.inr hp)) (eventually_mem_nhdsWithin.mono hfc) hfcp
      hlow).2
  · -- near the face, `χ_B = t² (-y₁/2 - t/12) - y₂ t` with `y₂ ≤ 0`
    filter_upwards [eventually_mem_nhdsWithin] with q hq t ht
    refine ⟨fun h ↦ h.le, fun h ↦ ?_⟩
    have hy2 : (cellPoint q 1).im ≤ 0 := by
      rw [(l5c_cellPoint_apply q).2.2.2.1]
      rcases hq with hq | hq
      · exact mul_nonpos_of_nonneg_of_nonpos hq.1.1.le
          (Real.sin_nonpos_of_nonpos_of_neg_pi_le hq.2.2.2.le hq.2.2.1.le)
      · rw [hq.2.2, Real.sin_zero, mul_zero]
    rw [(l5c_eval_chi _ t).2.2.2, l5c_im2]
    nlinarith [mul_nonneg (sq_nonneg t) h.le, mul_nonneg (neg_nonneg.2 hy2) ht.le]

end TriFuller

end SmoothedPolygons
