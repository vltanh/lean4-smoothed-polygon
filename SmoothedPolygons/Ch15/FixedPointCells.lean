module

public import SmoothedPolygons.Ch15.Involution
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan

/-!
# Chapter 15: Remark 15.3.1, the fixed points in cell coordinates

Remark 15.3.1 of Hales–Vajjha, *Packings of Smoothed Polygons* (TeX 12445–12461), with `q_in` and
`q_out` corrected (gap G15.1): the cell coordinates of the fixed points of Lemma 13.5.2,
`pOut ≈ (0.267949, 0.1705935, 2.91574)` with `r₂ = 2 - √3` exactly, and `pIn = τ(pOut) ≈ (0.267949,
2.9709992, 0.2258527)` (`remark15_3_1`), and the closeness of `q_in` to the triple juncture of
`𝒟₀, 𝒟₁, 𝒟₄` along the segment `r₂ ↦ (r₂, ψ_in, θ_{2in})` (`remark15_3_1_segment`).

All the numbers are certified by exact rational arithmetic, with no floating point: `r_scale` from
`rScale_fine_bounds`, `√3` by squaring, `π` from `Real.pi_gt_d20`, `arctan` by partial sums of its
alternating series (`Real.hasSum_arctan`), and the coordinates along the segment, which are
algebraic (no trigonometric function is evaluated: `e^{iθ}` at the angles of `q_in` is
`±z̄_j/|z_j|` for the coordinates `z_j` of (13.5.1)).
-/

@[expose] public section

namespace SmoothedPolygons

open Complex Set Filter Topology
open scoped Real

open TriFuller

/-! ### Elementary bounds (private helpers)

The arguments of the coordinates of `qOutCart` are `π - arctan t` for explicit algebraic numbers
`t ∈ ℚ(√3, r_scale)`; `arctan t` is bracketed by partial sums of its alternating Taylor series, at
decimal bounds of `t` obtained from `rScale_fine_bounds` and `√3 ∈ (1.7320508075688772,
1.7320508075688773)` by sign conditions of polynomials in `r` (each monomial `r^k` bounded by
`r_lo^k`, `r_hi^k`). -/

/-- Partial sums of the arctangent series bracket `arctan x` on `[0, 1)` (alternating series with
decreasing terms, `Real.hasSum_arctan`). -/
private lemma l5e_arctan_bounds {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) (k : ℕ) :
    ∑ i ∈ Finset.range (2 * k), (-1) ^ i * (x ^ (2 * i + 1) / (2 * i + 1)) ≤ Real.arctan x ∧
      Real.arctan x ≤
        ∑ i ∈ Finset.range (2 * k + 1), (-1) ^ i * (x ^ (2 * i + 1) / (2 * i + 1)) := by
  have hs := Real.hasSum_arctan (x := x) (by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1)
  have ht : Tendsto (fun n ↦ ∑ i ∈ Finset.range n, (-1) ^ i * (x ^ (2 * i + 1) / (2 * i + 1)))
      atTop (𝓝 (Real.arctan x)) := by
    convert hs.tendsto_sum_nat using 3 with n i
    push_cast
    ring
  have hanti : Antitone fun i : ℕ ↦ x ^ (2 * i + 1) / (2 * i + 1) := by
    intro i j hij
    have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
    exact div_le_div₀ (pow_nonneg h0 _) (pow_le_pow_of_le_one h0 h1.le (by omega))
      (by positivity) (by linarith)
  exact ⟨hanti.alternating_series_le_tendsto ht k, hanti.tendsto_le_alternating_series ht k⟩

/-- The argument of a point of the open second quadrant. -/
private lemma l5e_arg_eq {z : ℂ} (hre : z.re < 0) (him : 0 < z.im) :
    arg z = π - Real.arctan (z.im / -z.re) := by
  have h2 : arg z < π := arg_lt_pi_iff.2 (Or.inr him.ne')
  have h3 : π / 2 < arg z := by
    have h0 : 0 ≤ arg z := arg_nonneg_iff.2 him.le
    have h := mt (abs_arg_le_pi_div_two_iff (z := z)).1 (not_le.2 hre)
    rw [not_le, abs_of_nonneg h0] at h
    exact h
  have htan : Real.tan (arg z - π) = z.im / z.re := by
    rw [Real.tan_periodic.sub_eq, tan_arg]
  have := Real.arctan_tan (x := arg z - π) (by linarith) (by linarith)
  rw [htan] at this
  rw [div_neg, Real.arctan_neg, this]
  ring

private lemma l5e_sq_norm (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

private lemma l5e_sqrt3_bounds : (1.7320508075688772 : ℝ) < √3 ∧ √3 < 1.7320508075688773 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]
    norm_num
  · rw [Real.sqrt_lt' (by norm_num)]
    norm_num

/-- The real and imaginary parts of the first two coordinates of `qOutCart` (13.5.1). -/
private lemma l5e_qOutCart_parts :
    (qOutCart 0).re = -1 ∧ (qOutCart 0).im = (-1 + rScale) / (√3 * (1 + rScale)) ∧
      (qOutCart 1).re = -((-1 + rScale ^ 3) / (√3 * (1 + rScale ^ 3))) ∧
      (qOutCart 1).im = (1 - 3 * rScale - 2 * rScale ^ 2 - 3 * rScale ^ 3 + rScale ^ 4) /
        (3 * (1 + rScale + rScale ^ 3 + rScale ^ 4)) := by
  simp only [qOutCart, equilExact, Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im, Complex.one_re,
    Complex.one_im]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- Powers of `r_scale` between powers of its decimal bounds. -/
private lemma l5e_rScale_pow_bounds (k : ℕ) (hk : k ≠ 0) :
    (6.2741673995248239329 : ℝ) ^ k < rScale ^ k ∧ rScale ^ k < 6.2741673995248239330 ^ k :=
  ⟨pow_lt_pow_left₀ rScale_fine_bounds.1 (by norm_num) hk,
    pow_lt_pow_left₀ rScale_fine_bounds.2 (by linarith [rScale_fine_bounds.1]) hk⟩

/-- `Im z₁ = (r - 1)/(√3(1 + r)) ≈ 0.41861037843` at `qOutCart`. -/
private lemma l5e_im0_bounds :
    (0.4186103784 : ℝ) < (-1 + rScale) / (√3 * (1 + rScale)) ∧
      (-1 + rScale) / (√3 * (1 + rScale)) < 0.4186103785 := by
  obtain ⟨hr1, hr2⟩ := rScale_fine_bounds
  obtain ⟨hs1, hs2⟩ := l5e_sqrt3_bounds
  have hr0 : 0 < 1 + rScale := by linarith
  constructor
  · rw [lt_div_iff₀ (by positivity)]
    nlinarith [mul_lt_mul_of_pos_left hs2 hr0]
  · rw [div_lt_iff₀ (by positivity)]
    nlinarith [mul_lt_mul_of_pos_left hs1 hr0]

/-- `Im z₂ / (-Re z₂) = √3 g(r)`, `g(r) = (r⁴ - 3r³ - 2r² - 3r + 1)/(3(1 + r)(r³ - 1)) ≈
0.13265942650`, at `qOutCart`: `≈ 0.22977286680`. -/
private lemma l5e_t2_bounds :
    (0.2297728667 : ℝ) <
        (1 - 3 * rScale - 2 * rScale ^ 2 - 3 * rScale ^ 3 + rScale ^ 4) /
          (3 * (1 + rScale + rScale ^ 3 + rScale ^ 4)) /
        ((-1 + rScale ^ 3) / (√3 * (1 + rScale ^ 3))) ∧
      (1 - 3 * rScale - 2 * rScale ^ 2 - 3 * rScale ^ 3 + rScale ^ 4) /
          (3 * (1 + rScale + rScale ^ 3 + rScale ^ 4)) /
        ((-1 + rScale ^ 3) / (√3 * (1 + rScale ^ 3))) < 0.2297728669 := by
  obtain ⟨hr1, hr2⟩ := rScale_fine_bounds
  obtain ⟨hs1, hs2⟩ := l5e_sqrt3_bounds
  obtain ⟨h21, h22⟩ := l5e_rScale_pow_bounds 2 (by norm_num)
  obtain ⟨h31, h32⟩ := l5e_rScale_pow_bounds 3 (by norm_num)
  obtain ⟨h41, h42⟩ := l5e_rScale_pow_bounds 4 (by norm_num)
  set r := rScale
  have hD : 0 < 3 * (1 + r) * (r ^ 3 - 1) := by
    have : 0 < r ^ 3 - 1 := by norm_num at h31; linarith
    positivity
  have heq : (1 - 3 * r - 2 * r ^ 2 - 3 * r ^ 3 + r ^ 4) / (3 * (1 + r + r ^ 3 + r ^ 4)) /
      ((-1 + r ^ 3) / (√3 * (1 + r ^ 3))) =
      √3 * ((1 - 3 * r - 2 * r ^ 2 - 3 * r ^ 3 + r ^ 4) / (3 * (1 + r) * (r ^ 3 - 1))) := by
    have h1 : 0 < 1 + r := by linarith
    have h3 : 0 < 1 + r ^ 3 := by positivity
    have h4 : (1 + r + r ^ 3 + r ^ 4) = (1 + r) * (1 + r ^ 3) := by ring
    have h5 : (-1 + r ^ 3) ≠ 0 := by norm_num at h31; linarith
    have h6 : r ^ 3 - 1 ≠ 0 := by norm_num at h31; linarith
    rw [h4]
    field_simp
    ring
  have hg1 : (0.132659426501 : ℝ) <
      (1 - 3 * r - 2 * r ^ 2 - 3 * r ^ 3 + r ^ 4) / (3 * (1 + r) * (r ^ 3 - 1)) := by
    rw [lt_div_iff₀ hD]
    norm_num at h21 h22 h31 h32 h41 h42 ⊢
    nlinarith
  have hg2 : (1 - 3 * r - 2 * r ^ 2 - 3 * r ^ 3 + r ^ 4) / (3 * (1 + r) * (r ^ 3 - 1)) <
      0.132659426502 := by
    rw [div_lt_iff₀ hD]
    norm_num at h21 h22 h31 h32 h41 h42 ⊢
    nlinarith
  rw [heq]
  constructor
  · calc (0.2297728667 : ℝ) < 1.7320508075688772 * 0.132659426501 := by norm_num
      _ < _ := mul_lt_mul hs1 hg1.le (by norm_num) (Real.sqrt_nonneg _)
  · calc _ < (1.7320508075688773 : ℝ) * 0.132659426502 :=
          mul_lt_mul hs2 hg2.le (by linarith) (by norm_num)
      _ < 0.2297728669 := by norm_num

/-- `arctan(Im z₁) ≈ 0.396446156524` at `qOutCart`. -/
private lemma l5e_arctan_im0_bounds :
    (0.39644615 : ℝ) < Real.arctan ((-1 + rScale) / (√3 * (1 + rScale))) ∧
      Real.arctan ((-1 + rScale) / (√3 * (1 + rScale))) < 0.39644616 := by
  obtain ⟨h1, h2⟩ := l5e_im0_bounds
  have hl := (l5e_arctan_bounds (x := 0.4186103784) (by norm_num) (by norm_num) 5).1
  have hu := (l5e_arctan_bounds (x := 0.4186103785) (by norm_num) (by norm_num) 5).2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hl hu
  norm_num at hl hu
  constructor
  · calc (0.39644615 : ℝ) < Real.arctan 0.4186103784 := by linarith
      _ < _ := Real.arctan_strictMono h1
  · calc _ < Real.arctan 0.4186103785 := Real.arctan_strictMono h2
      _ < 0.39644616 := by linarith

/-- `arctan(Im z₂/(-Re z₂)) ≈ 0.225852655766` at `qOutCart`. -/
private lemma l5e_arctan_t2_bounds :
    (0.22585265 : ℝ) < Real.arctan
        ((1 - 3 * rScale - 2 * rScale ^ 2 - 3 * rScale ^ 3 + rScale ^ 4) /
          (3 * (1 + rScale + rScale ^ 3 + rScale ^ 4)) /
        ((-1 + rScale ^ 3) / (√3 * (1 + rScale ^ 3)))) ∧
      Real.arctan
        ((1 - 3 * rScale - 2 * rScale ^ 2 - 3 * rScale ^ 3 + rScale ^ 4) /
          (3 * (1 + rScale + rScale ^ 3 + rScale ^ 4)) /
        ((-1 + rScale ^ 3) / (√3 * (1 + rScale ^ 3)))) < 0.22585266 := by
  obtain ⟨h1, h2⟩ := l5e_t2_bounds
  have hl := (l5e_arctan_bounds (x := 0.2297728667) (by norm_num) (by norm_num) 3).1
  have hu := (l5e_arctan_bounds (x := 0.2297728669) (by norm_num) (by norm_num) 3).2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hl hu
  norm_num at hl hu
  constructor
  · calc (0.22585265 : ℝ) < Real.arctan 0.2297728667 := by linarith
      _ < _ := Real.arctan_strictMono h1
  · calc _ < Real.arctan 0.2297728669 := Real.arctan_strictMono h2
      _ < 0.22585266 := by linarith

/-- `|z₁|⁴ = 4|z₂|²` at (13.5.1), identically in `r` (with `(√3)² = 3`): `|z₁|² = 2|z₂|`, which
makes the rescaling of Lemma 15.1.1 explicit and gives `r₂ = 2 - √3`. -/
private lemma l5e_norm_sq_qOutCart : ‖qOutCart 0‖ ^ 2 = 2 * ‖qOutCart 1‖ := by
  obtain ⟨a0, a1, a2, a3⟩ := l5e_qOutCart_parts
  have hr := rScale_fine_bounds.1
  set r := rScale
  have hs : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < √3 := by positivity
  have hr0 : 0 < r := by linarith
  have key : (‖qOutCart 0‖ ^ 2) ^ 2 = 4 * ‖qOutCart 1‖ ^ 2 := by
    rw [l5e_sq_norm, l5e_sq_norm, a0, a1, a2, a3]
    simp only [div_pow, neg_sq, mul_pow, hs]
    have h1 : (1 + r) ≠ 0 := by positivity
    have h3 : (1 + r ^ 3) ≠ 0 := by positivity
    have h4 : (1 + r + r ^ 3 + r ^ 4) ≠ 0 := by positivity
    field_simp
    ring
  have hpos : 0 < ‖qOutCart 0‖ ^ 2 + 2 * ‖qOutCart 1‖ := by
    rw [l5e_sq_norm, a0]
    positivity
  have h := congrArg (· - 4 * ‖qOutCart 1‖ ^ 2) key
  simp only [sub_self] at h
  have h' : (‖qOutCart 0‖ ^ 2 - 2 * ‖qOutCart 1‖) * (‖qOutCart 0‖ ^ 2 + 2 * ‖qOutCart 1‖) = 0 := by
    rw [← h]
    ring
  rcases mul_eq_zero.1 h' with h'' | h''
  · linarith
  · linarith

/-- `-Re z₂ = (r³ - 1)/(√3(1 + r³)) > 0` at `qOutCart`. -/
private lemma l5e_X_pos : 0 < (-1 + rScale ^ 3) / (√3 * (1 + rScale ^ 3)) := by
  have hr := rScale_fine_bounds.1
  have : 1 < rScale ^ 3 := one_lt_pow₀ (by linarith) (by norm_num)
  exact div_pos (by linarith) (by positivity)

/-- The arguments of `z₁ = -1 + i b` and `z₂ = -X + i Y` at `qOutCart`. -/
private lemma l5e_args :
    arg (qOutCart 0) = π - Real.arctan ((-1 + rScale) / (√3 * (1 + rScale))) ∧
      arg (qOutCart 1) = π - Real.arctan
        ((1 - 3 * rScale - 2 * rScale ^ 2 - 3 * rScale ^ 3 + rScale ^ 4) /
          (3 * (1 + rScale + rScale ^ 3 + rScale ^ 4)) /
        ((-1 + rScale ^ 3) / (√3 * (1 + rScale ^ 3)))) := by
  obtain ⟨a0, a1, a2, a3⟩ := l5e_qOutCart_parts
  refine ⟨?_, ?_⟩
  · rw [l5e_arg_eq (by rw [a0]; norm_num) (by rw [a1]; linarith [l5e_im0_bounds.1]), a0, a1,
      neg_neg, div_one]
  · rw [l5e_arg_eq (by rw [a2]; linarith [l5e_X_pos]) qOutCart_signs.2.2, a2, a3, neg_neg]

/-- The angles of `pOut`: `ψ = arg z₂ - arg z₁` (already in `[0, 2π)`) and `θ₂ = arg z₂`. -/
private lemma l5e_pOut_args :
    pOut 1 = arg (qOutCart 1) - arg (qOutCart 0) ∧ pOut 2 = arg (qOutCart 1) := by
  obtain ⟨harg0, harg1⟩ := l5e_args
  obtain ⟨hA1, hA2⟩ := l5e_arctan_im0_bounds
  obtain ⟨hC1, hC2⟩ := l5e_arctan_t2_bounds
  have hpi1 := Real.pi_gt_d20
  refine ⟨?_, by simp [pOut, cellCoords]⟩
  simp only [pOut, cellCoords, Matrix.cons_val_one, Matrix.cons_val_zero]
  rw [toIcoMod_eq_self, harg0, harg1, zero_add]
  constructor <;> linarith

/-- **Remark 15.3.1** (`rem:qin-juncture`, label of this formalization; unlabelled, TeX
12445–12461), **with `q_in` and `q_out` corrected** (gap G15.1). The book prints "The fixed point
`q_in ∈ 𝒟₁` is given by coordinates `(r_{2in}, ψ_in, θ_{2in}) ≈ (0.267949, 0.1705935, 2.91574)`"
and "The fixed point `q_out ∈ 𝒟₁` with coordinates
`(r₂, π - ψ_in, π - θ_{2in})`". The labels are swapped: the printed point is `q_out`, the cell
coordinates of (13.5.1) (Lemma 13.5.2, labelled `q_out` there; Chapter 16 places `q_out` in
`𝒟_out = 𝒟₀₀`, which contains the printed point, and `q_in` in `𝒟_in = 𝒟_{1,22}`, which contains
its image `(r₂, π - ψ, π - θ₂)`; the Jacobian at the printed point has eigenvalues of modulus
`< 0.1`, so it is the attracting fixed point, Lemma 13.5.5). This is a slip with one reading: the
corrected remark reads "`q_out` has coordinates `≈ (0.267949, 0.1705935, 2.91574)` and `q_in`
has coordinates `(r₂, π - ψ_out, π - θ_{2out}) ≈ (0.267949, 2.9709992, 0.2258527)`".

Formalized: the coordinates `pOut` of `q_out`, with `r₂ = 2 - √3` exactly (the book's `0.267949`;
equivalently `|z₁|² = 2|z₂|` at (13.5.1)) and the printed angles to `10⁻⁷`; `pIn = τ(pOut)` are the
coordinates of `q_in`, and `𝔦(q_out) = q_in`. The closeness of `q_in` to the triple juncture of
`𝒟₀, 𝒟₁, 𝒟₄` is `remark15_3_1_segment`; "`q_out` is far from the other parts `𝒟₀, 𝒟₄`" and
"`q_in ∈ 𝒟₁`" are read off Figure 15.2 and are not formalized.

Proof route: `pOut = cellCoords qOutCart` (`cellClass_cellCoords`, `classOf_qOutCart`);
`r₂ = 2 - √3` is the identity `(1 + b²)² = 4(x² + y²)` for `qOutCart = (-1 + ib, x + iy, ·)`, an
identity in `ℚ(√3)(r)` that holds for every `r` (`P(r_scale) = 0` is not used): `|z₁|² = 2|z₂|`, so
the rescaling of Lemma 15.1.1 has `s|z₁| = √3 - 1` and `r₂ = (√3 - 1)²/2`. The angles are
`ψ = arctan b - arctan(y/(-x))` and `θ₂ = π - arctan(y/(-x))`, with `b`, `y/(-x)` enclosed to
`10⁻¹⁰` from `rScale_fine_bounds` and `arctan` bracketed by partial sums of its alternating series;
`pIn = τ(pOut)` and `cellClass pIn = q_in` by `cellClass_cellTau` and `τ(q_out) = q_in`
(`tauQuot_qOut`); `𝔦(q_out) = q_in` is `inInvolution_qOut0_qIn0`. -/
theorem remark15_3_1 :
    pOut ∈ openBoxOne ∧ cellClass pOut = qOut0 ∧ pOut 0 = 2 - √3 ∧
      |pOut 1 - 0.1705935| < 1e-7 ∧ |pOut 2 - 2.91574| < 1e-7 ∧
      pIn = ![pOut 0, π - pOut 1, π - pOut 2] ∧ pIn ∈ openBoxOne ∧ cellClass pIn = qIn0 ∧
      involution qOut0 = qIn0 := by
  obtain ⟨a0, a1, a2, a3⟩ := l5e_qOutCart_parts
  obtain ⟨hB1, hB2⟩ := l5e_im0_bounds
  obtain ⟨ht1, ht2⟩ := l5e_t2_bounds
  obtain ⟨hA1, hA2⟩ := l5e_arctan_im0_bounds
  obtain ⟨hC1, hC2⟩ := l5e_arctan_t2_bounds
  obtain ⟨hs1, hs2⟩ := l5e_sqrt3_bounds
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  have hr := rScale_fine_bounds.1
  obtain ⟨harg0, harg1⟩ := l5e_args
  have hY := qOutCart_signs.2.2
  -- the three coordinates of `pOut`
  have hb0 : ‖qOutCart 1‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    intro h
    rw [h] at hY
    simp at hY
  have hp0 : pOut 0 = 2 - √3 := by
    have hn := l5e_norm_sq_qOutCart
    have ha : 0 < ‖qOutCart 0‖ := by
      rw [norm_pos_iff]
      intro h
      rw [h] at a0
      simp at a0
    simp only [pOut, cellCoords, Matrix.cons_val_zero, ite_eq_right hb0]
    set a := ‖qOutCart 0‖
    set b := ‖qOutCart 1‖
    have hsq : √(a ^ 2 + 4 * b) = √3 * a := by
      rw [show a ^ 2 + 4 * b = 3 * a ^ 2 by linarith, Real.sqrt_mul (by norm_num),
        Real.sqrt_sq ha.le]
    have hs : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    rw [hsq, show b = a ^ 2 / 2 by linarith]
    field_simp
    linear_combination hs
  obtain ⟨hp1, hp2⟩ := l5e_pOut_args
  have hmem : pOut ∈ openBoxOne := by
    refine ⟨⟨by rw [hp0]; linarith, by rw [hp0]; linarith⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [hp1, harg0, harg1]; linarith
    · rw [hp1, harg0, harg1]; linarith
    · rw [hp2, harg1]; linarith
    · rw [hp2, harg1]; linarith
  have hclass : cellClass pOut = qOut0 :=
    (cellClass_cellCoords classOf_qOutCart.1 qOutCart_normalization.2.1
      qOutCart_normalization.2.2).2.trans classOf_qOutCart.2.1
  have hpIn : pIn = ![pOut 0, π - pOut 1, π - pOut 2] := by
    simp only [pIn, cellTau, ite_eq_left hmem.2.2.1.le]
  have htau : tauZero qOut0 = qIn0 := Subtype.ext tauQuot_qOut
  refine ⟨hmem, hclass, hp0, ?_, ?_, hpIn, ?_, ?_, ?_⟩
  · rw [abs_lt, hp1, harg0, harg1]
    constructor <;> linarith
  · rw [abs_lt, hp2, harg1]
    constructor <;> linarith
  · obtain ⟨⟨h01, h02⟩, ⟨h11, h12⟩, ⟨h21, h22⟩⟩ := hmem
    rw [hpIn]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp <;> linarith
  · rw [pIn, (cellClass_cellTau ⟨⟨hmem.1.1.le, hmem.1.2.le⟩,
      ⟨hmem.2.1.1.le, hmem.2.1.2.le⟩, ⟨by linarith [hmem.2.2.1], hmem.2.2.2.le⟩⟩).2, hclass, htau]
  · have h := inInvolution_qOut0_qIn0.1
    rwa [image_singleton, singleton_eq_singleton_iff] at h

/-! ### The segment through `q_in` (private helpers)

Along `r ↦ (r, ψ_in, θ_{2in})` the point is explicit in the coordinates of `qOutCart =
(-1 + i b, -X + i Y, ·)`: with `ρ = |z₁|` (and `|z₂| = ρ²/2`),
`z = (-(1 - r)(1 + i b)/ρ, 2r(X + iY)/ρ², -4(1 - r) r (X b - Y)/ρ³)`. The switching cubics from
the first control `ζ` are `χ_A = -t³/12 + (1 - r) β t² - r γ t + (1 - r) r δ` and
`χ_B = t (t²/12 - (1 - r) η₁ t/2 + r η₂)` for five constants `β, γ, δ, η₁, η₂` of `qOutCart`,
enclosed to `10⁻¹⁴` from `rScale_fine_bounds` and `√3`. The signs needed are then rational
inequalities (with margins `≥ 2·10⁻⁶` for the switching cubics and `≥ 2·10⁻¹¹` for `Δ_{A,0}`,
whose enclosures have width `≤ 10⁻¹⁵`). -/

/-- The cell coordinates of `q_in`: `pIn = (r₂, π - ψ_out, π - θ_{2out})`. -/
private lemma l5e_pIn_args :
    pIn 1 = π - (arg (qOutCart 1) - arg (qOutCart 0)) ∧ pIn 2 = π - arg (qOutCart 1) := by
  have h := remark15_3_1.2.2.2.2.2.1
  obtain ⟨h1, h2⟩ := l5e_pOut_args
  refine ⟨?_, ?_⟩
  · rw [h, ← h1]
    simp
  · rw [h, ← h2]
    simp

private lemma l5e_qOutCart_ne_zero : qOutCart 0 ≠ 0 ∧ qOutCart 1 ≠ 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := l5e_qOutCart_parts.1
    rw [h] at this
    norm_num at this
  · have := qOutCart_signs.2.2
    rw [h] at this
    simp at this

/-- The coordinates of the point `(r, ψ_in, θ_{2in})` of the segment. -/
private lemma l5e_seg_coords (r : ℝ) :
    (cellPoint ![r, pIn 1, pIn 2] 0).re = (1 - r) * ((qOutCart 0).re / ‖qOutCart 0‖) ∧
      (cellPoint ![r, pIn 1, pIn 2] 0).im = (1 - r) * -((qOutCart 0).im / ‖qOutCart 0‖) ∧
      (cellPoint ![r, pIn 1, pIn 2] 1).re = r * -((qOutCart 1).re / ‖qOutCart 1‖) ∧
      (cellPoint ![r, pIn 1, pIn 2] 1).im = r * ((qOutCart 1).im / ‖qOutCart 1‖) ∧
      (cellPoint ![r, pIn 1, pIn 2] 2).re = -2 * (1 - r) * r *
        ((qOutCart 1).im / ‖qOutCart 1‖ * ((qOutCart 0).re / ‖qOutCart 0‖) -
          (qOutCart 1).re / ‖qOutCart 1‖ * ((qOutCart 0).im / ‖qOutCart 0‖)) ∧
      (cellPoint ![r, pIn 1, pIn 2] 2).im = 0 := by
  obtain ⟨h1, h2⟩ := l5e_pIn_args
  obtain ⟨hq0, hq1⟩ := l5e_qOutCart_ne_zero
  have e : pIn 2 - pIn 1 = -arg (qOutCart 0) := by
    rw [h1, h2]
    ring
  simp only [cellPoint, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, e, Real.cos_neg, Complex.cos_arg hq0]
  · rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im, e, Real.sin_neg, Complex.sin_arg]
  · rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, h2, Real.cos_pi_sub,
      Complex.cos_arg hq1]
  · rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im, h2, Real.sin_pi_sub, Complex.sin_arg]
  · rw [Complex.ofReal_re, h1, Real.sin_pi_sub, Real.sin_sub, Complex.sin_arg, Complex.sin_arg,
      Complex.cos_arg hq0, Complex.cos_arg hq1]
  · rw [Complex.ofReal_im]

/-- `β = (√3 - b)/(4ρ)`. -/
private noncomputable def l5eβ : ℝ := (√3 - (qOutCart 0).im) / (4 * ‖qOutCart 0‖)

/-- `γ = (√3 X - Y)/ρ²`. -/
private noncomputable def l5eγ : ℝ :=
  (√3 * -(qOutCart 1).re - (qOutCart 1).im) / ‖qOutCart 0‖ ^ 2

/-- `δ = 2√3 (X b - Y)/ρ³`. -/
private noncomputable def l5eδ : ℝ :=
  2 * √3 * (-(qOutCart 1).re * (qOutCart 0).im - (qOutCart 1).im) / ‖qOutCart 0‖ ^ 3

/-- `η₁ = b/ρ`. -/
private noncomputable def l5eη₁ : ℝ := (qOutCart 0).im / ‖qOutCart 0‖

/-- `η₂ = 2Y/ρ²`. -/
private noncomputable def l5eη₂ : ℝ := 2 * (qOutCart 1).im / ‖qOutCart 0‖ ^ 2

/-- The coefficients of the switching cubics along the segment. -/
private lemma l5e_seg_coeffs (r : ℝ) :
    ((cellPoint ![r, pIn 1, pIn 2] 0).im - √3 * (cellPoint ![r, pIn 1, pIn 2] 0).re) / 4 =
        (1 - r) * l5eβ ∧
      ((cellPoint ![r, pIn 1, pIn 2] 1).im - √3 * (cellPoint ![r, pIn 1, pIn 2] 1).re) / 2 =
        -(r * l5eγ) ∧
      ((cellPoint ![r, pIn 1, pIn 2] 2).im - √3 * (cellPoint ![r, pIn 1, pIn 2] 2).re) / 2 =
        (1 - r) * r * l5eδ ∧
      (cellPoint ![r, pIn 1, pIn 2] 0).im = -((1 - r) * l5eη₁) ∧
      (cellPoint ![r, pIn 1, pIn 2] 1).im = r * l5eη₂ ∧
      (cellPoint ![r, pIn 1, pIn 2] 2).im = 0 := by
  obtain ⟨c0, c1, c2, c3, c4, c5⟩ := l5e_seg_coords r
  have a0 := l5e_qOutCart_parts.1
  have hn := l5e_norm_sq_qOutCart
  have hρ : 0 < ‖qOutCart 0‖ := norm_pos_iff.2 l5e_qOutCart_ne_zero.1
  have hn1 : ‖qOutCart 1‖ = ‖qOutCart 0‖ ^ 2 / 2 := by linarith
  rw [c0, c1, c2, c3, c4, c5, hn1, a0]
  unfold l5eβ l5eγ l5eδ l5eη₁ l5eη₂
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl⟩ <;> field_simp <;> ring

/-- `H_F(z(t), 1) - H_F(z(t), ζ) = -√3 χ_A(t)` along the trajectory with the control `ζ`. -/
private lemma l5e_ham_one_sub (t : ℝ) (z : Fin 3 → ℂ) :
    ham (flow t z ζ) 1 - ham (flow t z ζ) ζ = -√3 * (-t ^ 3 / 12 +
      ((z 0).im - √3 * (z 0).re) / 4 * t ^ 2 + ((z 1).im - √3 * (z 1).re) / 2 * t +
      ((z 2).im - √3 * (z 2).re) / 2) := by
  have hs : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  rw [ham_flow_sub_ham_flow, ζ_eq_mk]
  simp only [RR_eq_re_mul_add_im_mul, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.I_re, Complex.I_im]
  linear_combination (-((z 0).re * t ^ 2 / 4 + (z 1).re * t / 2 + (z 2).re / 2)) * hs

/-- `H_F(z(t), ζ²) - H_F(z(t), ζ) = -√3 χ_B(t)` along the trajectory with the control `ζ`. -/
private lemma l5e_ham_sq_sub (t : ℝ) (z : Fin 3 → ℂ) :
    ham (flow t z ζ) (ζ ^ 2) - ham (flow t z ζ) ζ =
      -√3 * (t ^ 3 / 12 + (z 0).im / 2 * t ^ 2 + (z 1).im * t + (z 2).im) := by
  rw [ham_flow_sub_ham_flow, ζ_sq_eq_mk, ζ_eq_mk]
  simp only [RR_eq_re_mul_add_im_mul, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
  ring

open Polynomial in
/-- The discriminants along the segment, on the open first box, where `(m_A, m_B) = (0, 1)`:
`Δ_{A,0}` of `χ_A = a t³ + b t² + c t + d` (`a = -1/12`, `b = (1 - r)β`, `c = -rγ`,
`d = (1 - r) r δ`) and `Δ_{B,1}` of `χ_B/t = t²/12 - (1 - r)η₁ t/2 + r η₂`. -/
private lemma l5e_seg_discr {r : ℝ} (hp : ![r, pIn 1, pIn 2] ∈ openBoxOne) :
    discrA ζ (cellPoint ![r, pIn 1, pIn 2]) =
        ((1 - r) * l5eβ) ^ 2 * (r * l5eγ) ^ 2 - (r * l5eγ) ^ 3 / 3 -
          4 * ((1 - r) * l5eβ) ^ 3 * ((1 - r) * r * l5eδ) - 3 / 16 * ((1 - r) * r * l5eδ) ^ 2 +
          3 / 2 * ((1 - r) * l5eβ) * (r * l5eγ) * ((1 - r) * r * l5eδ) ∧
      discrB ζ (cellPoint ![r, pIn 1, pIn 2]) = ((1 - r) * l5eη₁) ^ 2 / 4 - r * l5eη₂ / 3 := by
  obtain ⟨hA, hB⟩ := multA_multB_of_mem_openBox.1 _ hp
  obtain ⟨k0, k1, k2, k3, k4, k5⟩ := l5e_seg_coeffs r
  obtain ⟨eA, eB, -, -⟩ := chiA_chiB_eq (cellPoint ![r, pIn 1, pIn 2])
  constructor
  · unfold discrA chiARed
    rw [hA, pow_zero, divByMonic_one, eA, k0, k1, k2,
      Polynomial.discr_of_degree_eq_three (Cubic.degree_of_a_ne_zero' (by norm_num))]
    simp only [Cubic.coeff_eq_a, Cubic.coeff_eq_b, Cubic.coeff_eq_c, Cubic.coeff_eq_d]
    ring
  · unfold discrB chiBRed
    rw [hB, pow_one, eB, k3, k4, k5]
    have e : (⟨1 / 12, -((1 - r) * l5eη₁) / 2, r * l5eη₂, 0⟩ : Cubic ℝ).toPoly =
        X * (C (1 / 12) * X ^ 2 + C (-((1 - r) * l5eη₁) / 2) * X + C (r * l5eη₂)) := by
      simp only [Cubic.toPoly, map_zero, add_zero]
      ring
    rw [e, mul_divByMonic_cancel_left _ monic_X,
      Polynomial.discr_of_degree_eq_two (Polynomial.degree_quadratic (by norm_num))]
    simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
    norm_num
    ring

/-- An upper bound for the first switching time: a time `t > 0` at which a control beats the first
control `ζ`. -/
private lemma l5e_firstSwitchTime_le {z : Fin 3 → ℂ} (hz : firstControl z = ζ) {t : ℝ}
    (ht : 0 < t) {v : ℂ} (hv : v ∈ VT) (h : ham (flow t z ζ) ζ < ham (flow t z ζ) v) :
    firstSwitchTime z ≤ t := by
  refine csInf_le ⟨0, fun s hs ↦ hs.1.le⟩ ⟨ht, v, hv, ?_⟩
  rw [hz]
  exact h

/-- A lower bound for the first switching time: the first control `ζ` is not beaten on
`(0, T₀)`. -/
private lemma l5e_le_firstSwitchTime {z : Fin 3 → ℂ} (hz0 : z ≠ 0) (hz : firstControl z = ζ)
    {T₀ : ℝ} (h : ∀ t, 0 < t → t < T₀ →
      ham (flow t z ζ) 1 ≤ ham (flow t z ζ) ζ ∧ ham (flow t z ζ) (ζ ^ 2) ≤ ham (flow t z ζ) ζ) :
    T₀ ≤ firstSwitchTime z := by
  obtain ⟨s, hs, v, hv, hlt⟩ := firstControl_beaten hz0 one_pos
  refine le_csInf ⟨s, (firstSwitchTime_pos hz0).trans hs.1, v, hv, hlt⟩ ?_
  rintro t ⟨ht, v, hv, hlt⟩
  rw [hz] at hlt
  by_contra hT
  obtain ⟨h1, h2⟩ := h t ht (not_le.1 hT)
  rcases mem_VT.1 hv with rfl | rfl | rfl
  · linarith
  · exact lt_irrefl _ hlt
  · linarith

/-- The first control after the switch: the control that is not beaten by the other one at `F(z)`
(the first control of `F(z)` maximizes `H_F` there and differs from `ζ`). -/
private lemma l5e_firstControl_poincare {z : Fin 3 → ℂ} (hz0 : z ≠ 0) (hz : firstControl z = ζ) :
    (ham (poincare z) 1 < ham (poincare z) ζ → firstControl (poincare z) = ζ ^ 2) ∧
      (ham (poincare z) (ζ ^ 2) < ham (poincare z) ζ → firstControl (poincare z) = 1) := by
  have hne := firstControl_poincare_ne hz0
  rw [hz] at hne
  obtain ⟨hu, ε, hε, hmax⟩ := isFirstControl_firstControl (poincare_ne_zero hz0)
  have hζ : ham (poincare z) ζ ≤ ham (poincare z) (firstControl (poincare z)) := by
    have := hmax 0 ⟨le_rfl, hε.le⟩ ζ ζ_mem_VT
    rwa [flow_zero] at this
  constructor
  · intro h
    rcases mem_VT.1 hu with h1 | h1 | h1
    · rw [h1] at hζ
      linarith
    · exact absurd h1 hne
    · exact h1
  · intro h
    rcases mem_VT.1 hu with h1 | h1 | h1
    · exact h1
    · exact absurd h1 hne
    · rw [h1] at hζ
      linarith

/-! #### Enclosures of the five constants -/

private lemma l5e_iv_mul {a b a1 a2 b1 b2 : ℝ} (ha : a1 < a ∧ a < a2) (hb : b1 < b ∧ b < b2)
    (h1 : 0 ≤ a1) (h2 : 0 ≤ b1) : a1 * b1 < a * b ∧ a * b < a2 * b2 :=
  ⟨mul_lt_mul'' ha.1 hb.1 h1 h2, mul_lt_mul'' ha.2 hb.2 (h1.trans ha.1.le) (h2.trans hb.1.le)⟩

private lemma l5e_iv_div {a b a1 a2 b1 b2 : ℝ} (ha : a1 < a ∧ a < a2) (hb : b1 < b ∧ b < b2)
    (h1 : 0 ≤ a1) (h2 : 0 < b1) : a1 / b2 < a / b ∧ a / b < a2 / b1 := by
  have hb0 : 0 < b := h2.trans hb.1
  have ha0 : 0 < a := h1.trans_lt ha.1
  constructor
  · calc a1 / b2 ≤ a1 / b := div_le_div_of_nonneg_left h1 hb0 hb.2.le
      _ < a / b := div_lt_div_of_pos_right ha.1 hb0
  · calc a / b < a2 / b := div_lt_div_of_pos_right ha.2 hb0
      _ < a2 / b1 := div_lt_div_of_pos_left (ha0.trans ha.2) h2 hb.1

private lemma l5e_iv_sub {a b a1 a2 b1 b2 : ℝ} (ha : a1 < a ∧ a < a2) (hb : b1 < b ∧ b < b2) :
    a1 - b2 < a - b ∧ a - b < a2 - b1 :=
  ⟨by linarith [ha.1, hb.2], by linarith [ha.2, hb.1]⟩

private lemma l5e_iv_pow {a a1 a2 : ℝ} (ha : a1 < a ∧ a < a2) (h1 : 0 ≤ a1) (n : ℕ) (hn : n ≠ 0) :
    a1 ^ n < a ^ n ∧ a ^ n < a2 ^ n :=
  ⟨pow_lt_pow_left₀ ha.1 h1 hn, pow_lt_pow_left₀ ha.2 (h1.trans ha.1.le) hn⟩

private lemma l5e_iv_weaken {a x1 x2 y1 y2 : ℝ} (h : x1 < a ∧ a < x2) (h1 : y1 ≤ x1)
    (h2 : x2 ≤ y2) : y1 < a ∧ a < y2 :=
  ⟨h1.trans_lt h.1, h.2.trans_le h2⟩

private lemma l5e_sqrt3_fine :
    (1.73205080756887729352 : ℝ) < √3 ∧ √3 < 1.73205080756887729353 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]
    norm_num
  · rw [Real.sqrt_lt' (by norm_num)]
    norm_num

/-- `b = Im z₁ ≈ 0.4186103784284259` at `qOutCart`. -/
private lemma l5e_B_fine :
    (0.418610378428425 : ℝ) < (qOutCart 0).im ∧ (qOutCart 0).im < 0.418610378428426 := by
  obtain ⟨hr1, hr2⟩ := rScale_fine_bounds
  obtain ⟨hs1, hs2⟩ := l5e_sqrt3_fine
  have hr0 : 0 < 1 + rScale := by linarith
  rw [l5e_qOutCart_parts.2.1]
  constructor
  · rw [lt_div_iff₀ (by positivity)]
    nlinarith [mul_lt_mul_of_pos_left hs2 hr0]
  · rw [div_lt_iff₀ (by positivity)]
    nlinarith [mul_lt_mul_of_pos_left hs1 hr0]

/-- `X = -Re z₂ ≈ 0.5726939127284037` at `qOutCart`. -/
private lemma l5e_X_fine :
    (0.572693912728403 : ℝ) < -(qOutCart 1).re ∧ -(qOutCart 1).re < 0.572693912728404 := by
  obtain ⟨h31, h32⟩ := l5e_rScale_pow_bounds 3 (by norm_num)
  obtain ⟨hs1, hs2⟩ := l5e_sqrt3_fine
  have hr0 : 0 < 1 + rScale ^ 3 := by norm_num at h31; linarith
  rw [l5e_qOutCart_parts.2.2.1, neg_neg]
  norm_num at h31 h32
  constructor
  · rw [lt_div_iff₀ (by positivity)]
    nlinarith [mul_lt_mul_of_pos_left hs2 hr0]
  · rw [div_lt_iff₀ (by positivity)]
    nlinarith [mul_lt_mul_of_pos_left hs1 hr0]

/-- `Y = Im z₂ ≈ 0.1315895221286841` at `qOutCart`. -/
private lemma l5e_Y_fine :
    (0.131589522128683 : ℝ) < (qOutCart 1).im ∧ (qOutCart 1).im < 0.131589522128686 := by
  obtain ⟨hr1, hr2⟩ := rScale_fine_bounds
  obtain ⟨h21, h22⟩ := l5e_rScale_pow_bounds 2 (by norm_num)
  obtain ⟨h31, h32⟩ := l5e_rScale_pow_bounds 3 (by norm_num)
  obtain ⟨h41, h42⟩ := l5e_rScale_pow_bounds 4 (by norm_num)
  have hD : 0 < 3 * (1 + rScale + rScale ^ 3 + rScale ^ 4) := by
    have : 0 < rScale := by linarith
    positivity
  rw [l5e_qOutCart_parts.2.2.2]
  norm_num at h21 h22 h31 h32 h41 h42
  constructor
  · rw [lt_div_iff₀ hD]
    nlinarith
  · rw [div_lt_iff₀ hD]
    nlinarith

/-- `ρ = |z₁| = √(1 + b²) ≈ 1.0840823995102908` at `qOutCart`. -/
private lemma l5e_ρ_fine :
    (1.08408239951029 : ℝ) < ‖qOutCart 0‖ ∧ ‖qOutCart 0‖ < 1.084082399510291 := by
  obtain ⟨hB1, hB2⟩ := l5e_B_fine
  have e : ‖qOutCart 0‖ ^ 2 = 1 + (qOutCart 0).im ^ 2 := by
    rw [l5e_sq_norm, l5e_qOutCart_parts.1]
    norm_num
  have hB1' : (0.418610378428425 : ℝ) ^ 2 < (qOutCart 0).im ^ 2 :=
    pow_lt_pow_left₀ hB1 (by norm_num) (by norm_num)
  have hB2' : (qOutCart 0).im ^ 2 < (0.418610378428426 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hB2 (by linarith) (by norm_num)
  constructor
  · refine lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) ?_
    rw [e]
    norm_num at hB1' ⊢
    linarith
  · refine lt_of_pow_lt_pow_left₀ 2 (by norm_num) ?_
    rw [e]
    norm_num at hB2' ⊢
    linarith

private lemma l5e_consts_fine :
    ((0.302892203981396 : ℝ) < l5eβ ∧ l5eβ < 0.302892203981397) ∧
      ((0.732062684406984 : ℝ) < l5eγ ∧ l5eγ < 0.73206268440699) ∧
      ((0.294045527648685 : ℝ) < l5eδ ∧ l5eδ < 0.294045527648698) ∧
      ((0.38614258345816 : ℝ) < l5eη₁ ∧ l5eη₁ < 0.386142583458162) ∧
      ((0.223937444745548 : ℝ) < l5eη₂ ∧ l5eη₂ < 0.223937444745555) := by
  have hs := l5e_sqrt3_fine
  have hB := l5e_B_fine
  have hX := l5e_X_fine
  have hY := l5e_Y_fine
  have hρ := l5e_ρ_fine
  have hρ2 := l5e_iv_pow hρ (by norm_num) 2 (by norm_num)
  have hρ3 := l5e_iv_pow hρ (by norm_num) 3 (by norm_num)
  unfold l5eβ l5eγ l5eδ l5eη₁ l5eη₂
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h4ρ : 4 * (1.08408239951029 : ℝ) < 4 * ‖qOutCart 0‖ ∧
        4 * ‖qOutCart 0‖ < 4 * 1.084082399510291 := ⟨by linarith [hρ.1], by linarith [hρ.2]⟩
    exact l5e_iv_weaken (l5e_iv_div (l5e_iv_sub hs hB) h4ρ (by norm_num) (by norm_num))
      (by norm_num) (by norm_num)
  · exact l5e_iv_weaken (l5e_iv_div (l5e_iv_sub (l5e_iv_mul hs hX (by norm_num) (by norm_num)) hY)
      hρ2 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  · have h2s : 2 * (1.73205080756887729352 : ℝ) < 2 * √3 ∧ 2 * √3 < 2 * 1.73205080756887729353 :=
      ⟨by linarith [hs.1], by linarith [hs.2]⟩
    exact l5e_iv_weaken (l5e_iv_div (l5e_iv_mul h2s (l5e_iv_sub (l5e_iv_mul hX hB (by norm_num)
      (by norm_num)) hY) (by norm_num) (by norm_num)) hρ3 (by norm_num) (by norm_num))
      (by norm_num) (by norm_num)
  · exact l5e_iv_weaken (l5e_iv_div hB hρ (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  · have h2Y : 2 * (0.131589522128683 : ℝ) < 2 * (qOutCart 1).im ∧
        2 * (qOutCart 1).im < 2 * 0.131589522128686 := ⟨by linarith [hY.1], by linarith [hY.2]⟩
    exact l5e_iv_weaken (l5e_iv_div h2Y hρ2 (by norm_num) (by norm_num)) (by norm_num)
      (by norm_num)

/-! #### Sign certificates -/

/-- The switching functions along the segment: `H_F(z(t), 1) - H_F(z(t), ζ) = -√3 χ_A(t)` and
`H_F(z(t), ζ²) - H_F(z(t), ζ) = -√3 χ_B(t)`. -/
private lemma l5e_seg_ham (r t : ℝ) :
    ham (flow t (cellPoint ![r, pIn 1, pIn 2]) ζ) 1 -
        ham (flow t (cellPoint ![r, pIn 1, pIn 2]) ζ) ζ =
      -√3 * (-t ^ 3 / 12 + (1 - r) * l5eβ * t ^ 2 - r * l5eγ * t + (1 - r) * r * l5eδ) ∧
    ham (flow t (cellPoint ![r, pIn 1, pIn 2]) ζ) (ζ ^ 2) -
        ham (flow t (cellPoint ![r, pIn 1, pIn 2]) ζ) ζ =
      -√3 * (t ^ 3 / 12 - (1 - r) * l5eη₁ / 2 * t ^ 2 + r * l5eη₂ * t) := by
  obtain ⟨k0, k1, k2, k3, k4, k5⟩ := l5e_seg_coeffs r
  rw [l5e_ham_one_sub, l5e_ham_sq_sub, k0, k1, k2, k3, k4, k5]
  constructor <;> ring

/-- A cubic `p₀ + p₁ s + (p₂ - s/12) s²` is positive for `s ≤ h` when `p₂ - h/12 ≥ κ > 0` and
`p₁² < 4 κ p₀`. -/
private lemma l5e_cubic_pos {p0 p1 p2 κ h s : ℝ} (hs : s ≤ h) (hκ : 0 < κ)
    (h2 : κ ≤ p2 - h / 12) (hd : p1 ^ 2 < 4 * κ * p0) :
    0 < p0 + p1 * s + (p2 - s / 12) * s ^ 2 := by
  have h1 : κ * s ^ 2 ≤ (p2 - s / 12) * s ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg s)
  nlinarith [sq_nonneg (2 * κ * s + p1)]

/-- `χ_A(t) = -t³/12 + b t² - c t + d > 0` on `(0, T]`, from bounds `b > b₁`, `c < c₂`, `d > d₁` and
the expansion of `-t³/12 + b₁ t² - c₂ t + d₁` at a point `m` near its local minimum. -/
private lemma l5e_chiA_pos {b c d b1 c2 d1 m κ T t : ℝ} (hb : b1 < b) (hc : c < c2) (hd : d1 < d)
    (ht0 : 0 < t) (htT : t ≤ T) (hκ : 0 < κ) (h2 : κ ≤ b1 - m / 4 - (T - m) / 12)
    (hdisc : (-m ^ 2 / 4 + 2 * b1 * m - c2) ^ 2 <
      4 * κ * (-m ^ 3 / 12 + b1 * m ^ 2 - c2 * m + d1)) :
    0 < -t ^ 3 / 12 + b * t ^ 2 - c * t + d := by
  have key : -t ^ 3 / 12 + b1 * t ^ 2 - c2 * t + d1 = (-m ^ 3 / 12 + b1 * m ^ 2 - c2 * m + d1) +
      (-m ^ 2 / 4 + 2 * b1 * m - c2) * (t - m) + (b1 - m / 4 - (t - m) / 12) * (t - m) ^ 2 := by
    ring
  have hpos := l5e_cubic_pos (s := t - m) (h := T - m) (by linarith) hκ h2 hdisc
  nlinarith [mul_nonneg (sub_nonneg.2 hb.le) (sq_nonneg t), mul_nonneg (sub_nonneg.2 hc.le) ht0.le]

/-- `χ_B(t) = t³/12 - e₁ t²/2 + e₂ t > 0` for `t > 0` when `Δ_{B,1} = e₁²/4 - e₂/3 < 0`. -/
private lemma l5e_chiB_pos {e1 e2 t : ℝ} (hΔ : e1 ^ 2 / 4 - e2 / 3 < 0) (ht : 0 < t) :
    0 < t ^ 3 / 12 - e1 / 2 * t ^ 2 + e2 * t := by
  have : 0 < t ^ 2 / 12 - e1 / 2 * t + e2 := by nlinarith [sq_nonneg (t - 3 * e1)]
  nlinarith

/-- Monotone bounds for `Δ_{A,0} = b²c² - c³/3 - 4b³d - 3d²/16 + 3bcd/2` (in terms of
`c = -χ_A'(0)`) with `b, c, d ≥ 0`. -/
private lemma l5e_discrA_bounds {b c d b1 b2 c1 c2 d1 d2 : ℝ} (hb : b1 < b ∧ b < b2)
    (hc : c1 < c ∧ c < c2) (hd : d1 < d ∧ d < d2) (hb1 : 0 ≤ b1) (hc1 : 0 ≤ c1) (hd1 : 0 ≤ d1) :
    b1 ^ 2 * c1 ^ 2 - c2 ^ 3 / 3 - 4 * b2 ^ 3 * d2 - 3 / 16 * d2 ^ 2 + 3 / 2 * b1 * c1 * d1 ≤
        b ^ 2 * c ^ 2 - c ^ 3 / 3 - 4 * b ^ 3 * d - 3 / 16 * d ^ 2 + 3 / 2 * b * c * d ∧
      b ^ 2 * c ^ 2 - c ^ 3 / 3 - 4 * b ^ 3 * d - 3 / 16 * d ^ 2 + 3 / 2 * b * c * d ≤
        b2 ^ 2 * c2 ^ 2 - c1 ^ 3 / 3 - 4 * b1 ^ 3 * d1 - 3 / 16 * d1 ^ 2 +
          3 / 2 * b2 * c2 * d2 := by
  obtain ⟨hb', hb''⟩ := hb
  obtain ⟨hc', hc''⟩ := hc
  obtain ⟨hd', hd''⟩ := hd
  have hb0 : 0 ≤ b := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hd0 : 0 ≤ d := by linarith
  have hb2 : 0 ≤ b2 := by linarith
  have hc2 : 0 ≤ c2 := by linarith
  have e1 : b1 ^ 2 * c1 ^ 2 ≤ b ^ 2 * c ^ 2 := by gcongr
  have e1' : b ^ 2 * c ^ 2 ≤ b2 ^ 2 * c2 ^ 2 := by gcongr
  have e2 : c1 ^ 3 ≤ c ^ 3 := by gcongr
  have e2' : c ^ 3 ≤ c2 ^ 3 := by gcongr
  have e3 : b1 ^ 3 * d1 ≤ b ^ 3 * d := by gcongr
  have e3' : b ^ 3 * d ≤ b2 ^ 3 * d2 := mul_le_mul (by gcongr) hd''.le hd0 (by positivity)
  have e4 : d1 ^ 2 ≤ d ^ 2 := by gcongr
  have e4' : d ^ 2 ≤ d2 ^ 2 := by gcongr
  have e5 : b1 * c1 * d1 ≤ b * c * d := by gcongr
  have e5' : b * c * d ≤ b2 * c2 * d2 :=
    mul_le_mul (mul_le_mul hb''.le hc''.le hc0 hb2) hd''.le hd0 (by positivity)
  constructor <;> linarith

private lemma l5e_scale_iv {a a1 a2 k : ℝ} (h : a1 < a ∧ a < a2) (hk : 0 < k) :
    k * a1 < k * a ∧ k * a < k * a2 :=
  ⟨mul_lt_mul_of_pos_left h.1 hk, mul_lt_mul_of_pos_left h.2 hk⟩

/-- **Remark 15.3.1, the segment through `q_in`** (`rem:qin-juncture`, TeX 12452–12458), corrected
(gap G15.1): "The fixed point is remarkably close to the triple juncture of `𝒟₀, 𝒟₁`, and `𝒟₄`.
In fact, the line segment `r₂ ↦ (r₂, ψ_in, θ_{2in})`, `r₂ ∈ [0, 1]` meets the boundary `∂_B`
(separating `𝒟₄` from `𝒟₀`) at `r₂ ≈ 0.2677`, then meets the boundary `∂_A` (separating `𝒟₀` from
`𝒟₁`) at `r₂ ≈ 0.267905`, then reaches the fixed point at `r₂ ≈ 0.267949`." With the true angles
of `q_in` (`pIn`), the crossings are checked through what characterizes them:
* `∂_B` between `r₂ = 0.26775` and `0.26777`: `Δ_{B,1}` changes sign from `+` to `-` and the switch
  changes from `ζ²` (`χ_B` active, `𝒟₄`) to `1` (`χ_A` active, `𝒟₀`);
* `∂_A` between `r₂ = 0.26790` and `0.26791`: `Δ_{A,0}` changes sign from `-` to `+` and the first
  switching time jumps from `≈ 0.984` to `≈ 0.824` (the discontinuity of `F` along `∂_A`);
* the fixed point at `r₂ = 2 - √3 ≈ 0.2679492` (`remark15_3_1`).
(Along the segment through the printed point, the book's "`q_in`", neither discriminant vanishes
near `r₂ = 0.2679`.)

Proof (certified, exact rational arithmetic): along the segment the point is algebraic,
`z = (-(1 - r)(1 + ib)/ρ, 2r(X + iY)/ρ², -4(1 - r) r (Xb - Y)/ρ³)` for `qOutCart = (-1 + ib,
-X + iY, ·)` and `ρ = |z₁|` (`|z₂| = ρ²/2`), and the switching cubics from the first control `ζ`
are `χ_A = -t³/12 + (1 - r)β t² - rγ t + (1 - r) r δ` and `χ_B = t(t²/12 - (1 - r)η₁ t/2 + rη₂)`
for five constants enclosed to `10⁻¹⁴` (`l5e_consts_fine`). Then:
* `Δ_{B,1} = (1 - r)²η₁²/4 - rη₂/3` (`8.8·10⁻⁷` at `0.26775`, `-1.7·10⁻⁶` at `0.26777`);
* at `r = 0.26775`, `χ_B(0.85) < 0`, so `t_sw ≤ 0.85`, and `χ_A > 0` on `(0, 0.85]` (a Taylor
  certificate at the local minimum `t ≈ 0.832`, value `1.1·10⁻⁴`), so at `F(z)` the control `1`
  is beaten by `ζ` and the new first control is `ζ²`; at `r = 0.26777`, `Δ_{B,1} < 0` gives
  `χ_B > 0` for `t > 0`, so the new first control is `1`;
* `Δ_{A,0}` (`-2.6·10⁻¹¹` at `0.26790`, `+2.0·10⁻¹¹` at `0.26791`) is enclosed to `10⁻¹⁵` by
  monotonicity in `b, -c, d > 0`;
* at `r = 0.26790`, `χ_A > 0` on `(0, 0.96]` (local minimum `3.5·10⁻⁶` at `t ≈ 0.8393`) and
  `χ_B > 0`, so `t_sw ≥ 0.96`; at `r = 0.26791`, `χ_A(0.84) ≈ -3.4·10⁻⁶ < 0`, so `t_sw ≤ 0.84`.
The small size of `Δ_{A,0}` is the normalization `a = -1/12` (`a⁴ ≈ 5·10⁻⁵`), not a near-double
root: at `r = 0.26791` the roots `0.8238, 0.8580, 0.9791` are well separated. -/
theorem remark15_3_1_segment :
    let seg : ℝ → Fin 3 → ℝ := fun r ↦ ![r, pIn 1, pIn 2]
    (0 < discrB ζ (cellPoint (seg 0.26775)) ∧ discrB ζ (cellPoint (seg 0.26777)) < 0 ∧
      firstControl (poincare (cellPoint (seg 0.26775))) = ζ ^ 2 ∧
      firstControl (poincare (cellPoint (seg 0.26777))) = 1) ∧
    (discrA ζ (cellPoint (seg 0.26790)) < 0 ∧ 0 < discrA ζ (cellPoint (seg 0.26791)) ∧
      0.95 < firstSwitchTime (cellPoint (seg 0.26790)) ∧
      firstSwitchTime (cellPoint (seg 0.26791)) < 0.86) ∧
    0.26791 < 2 - √3 := by
  intro seg
  have hIn := remark15_3_1.2.2.2.2.2.2.1
  obtain ⟨hβ, hγ, hδ, hη₁, hη₂⟩ := l5e_consts_fine
  have hs3 : 0 < √3 := by positivity
  have hmem : ∀ r : ℝ, 0 < r → r < 1 → ![r, pIn 1, pIn 2] ∈ openBoxOne := fun r h0 h1 ↦
    ⟨⟨by simpa using h0, by simpa using h1⟩, by simpa using hIn.2.1, by simpa using hIn.2.2⟩
  have hne : ∀ r : ℝ, r < 1 → cellPoint ![r, pIn 1, pIn 2] ≠ 0 := by
    intro r hr h
    have hρ := l5e_ρ_fine.1
    have h1 : (1 - r) * (-1 / ‖qOutCart 0‖) ≠ 0 :=
      mul_ne_zero (by linarith) (div_ne_zero (by norm_num) (by linarith))
    have := (l5e_seg_coords r).1
    rw [h, l5e_qOutCart_parts.1] at this
    simp only [Pi.zero_apply, Complex.zero_re] at this
    exact h1 this.symm
  have hfc : ∀ r : ℝ, 0 < r → r < 1 → firstControl (cellPoint ![r, pIn 1, pIn 2]) = ζ :=
    fun r h0 h1 ↦ definition15_1_2.2.2.2.2.2.1 _ (hmem r h0 h1)
  -- `Δ_{B,1} < 0` at `r = 0.26777, 0.26790`
  have hΔB : ∀ r : ℝ, r ∈ Icc (0.26777 : ℝ) 0.26791 →
      ((1 - r) * l5eη₁) ^ 2 / 4 - r * l5eη₂ / 3 < 0 := by
    intro r ⟨h1, h2⟩
    have e1 : ((1 - r) * l5eη₁) ^ 2 < ((1 - 0.26777) * 0.386142583458162) ^ 2 := by
      apply pow_lt_pow_left₀ _ (by nlinarith [hη₁.1]) (by norm_num)
      nlinarith [hη₁.2, hη₁.1]
    have e2 : 0.26777 * 0.223937444745548 < r * l5eη₂ := by nlinarith [hη₂.1, hη₂.2]
    norm_num at e1 e2 ⊢
    linarith
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  -- `∂_B`: the sign of `Δ_{B,1}` and the switch
  · rw [(l5e_seg_discr (hmem _ (by norm_num) (by norm_num))).2]
    have e1 : ((1 - 0.26775) * 0.38614258345816) ^ 2 < ((1 - (0.26775 : ℝ)) * l5eη₁) ^ 2 :=
      pow_lt_pow_left₀ (by nlinarith [hη₁.1]) (by norm_num) (by norm_num)
    norm_num at e1 ⊢
    linarith [hη₂.2]
  · rw [(l5e_seg_discr (hmem 0.26777 (by norm_num) (by norm_num))).2]
    exact hΔB 0.26777 ⟨by norm_num, by norm_num⟩
  · have hz := hne 0.26775 (by norm_num)
    have hc := hfc 0.26775 (by norm_num) (by norm_num)
    have hT0 := firstSwitchTime_pos hz
    -- `ζ²` beats `ζ` at `t = 0.85` (`χ_B(0.85) < 0`)
    have hT : firstSwitchTime (cellPoint ![0.26775, pIn 1, pIn 2]) ≤ 0.85 := by
      refine l5e_firstSwitchTime_le hc (by norm_num) ζ_sq_mem_VT ?_
      have h := (l5e_seg_ham 0.26775 0.85).2
      have hχ : (0.85 : ℝ) ^ 3 / 12 - (1 - 0.26775) * l5eη₁ / 2 * 0.85 ^ 2 +
          0.26775 * l5eη₂ * 0.85 < 0 := by
        linarith [hη₁.1, hη₂.2]
      nlinarith [mul_pos hs3 (neg_pos.2 hχ)]
    -- `χ_A > 0` on `(0, 0.85]`
    have hχA := l5e_chiA_pos (l5e_scale_iv hβ (by norm_num : (0 : ℝ) < 1 - 0.26775)).1
      (l5e_scale_iv hγ (by norm_num : (0 : ℝ) < 0.26775)).2
      (l5e_scale_iv hδ (by norm_num : (0 : ℝ) < (1 - 0.26775) * 0.26775)).1 hT0 hT
      (m := 0.832092) (κ := 0.01) (by norm_num) (by norm_num) (by norm_num)
    refine (l5e_firstControl_poincare hz hc).1 ?_
    have h := (l5e_seg_ham 0.26775 (firstSwitchTime (cellPoint ![0.26775, pIn 1, pIn 2]))).1
    rw [poincare, hc]
    nlinarith [mul_pos hs3 hχA]
  · have hz := hne 0.26777 (by norm_num)
    have hc := hfc 0.26777 (by norm_num) (by norm_num)
    have hT0 := firstSwitchTime_pos hz
    have hχB := l5e_chiB_pos (hΔB 0.26777 ⟨by norm_num, by norm_num⟩) hT0
    refine (l5e_firstControl_poincare hz hc).2 ?_
    have h := (l5e_seg_ham 0.26777 (firstSwitchTime (cellPoint ![0.26777, pIn 1, pIn 2]))).2
    rw [poincare, hc]
    nlinarith [mul_pos hs3 hχB]
  -- `∂_A`: the sign of `Δ_{A,0}` and the jump of the switching time
  · rw [(l5e_seg_discr (hmem _ (by norm_num) (by norm_num))).1]
    refine lt_of_le_of_lt (l5e_discrA_bounds
      (l5e_scale_iv hβ (by norm_num : (0 : ℝ) < 1 - 0.26790))
      (l5e_scale_iv hγ (by norm_num : (0 : ℝ) < 0.26790))
      (l5e_scale_iv hδ (by norm_num : (0 : ℝ) < (1 - 0.26790) * 0.26790))
      (by norm_num) (by norm_num) (by norm_num)).2 ?_
    norm_num
  · rw [(l5e_seg_discr (hmem _ (by norm_num) (by norm_num))).1]
    refine lt_of_lt_of_le ?_ (l5e_discrA_bounds
      (l5e_scale_iv hβ (by norm_num : (0 : ℝ) < 1 - 0.26791))
      (l5e_scale_iv hγ (by norm_num : (0 : ℝ) < 0.26791))
      (l5e_scale_iv hδ (by norm_num : (0 : ℝ) < (1 - 0.26791) * 0.26791))
      (by norm_num) (by norm_num) (by norm_num)).1
    norm_num
  · have hz := hne 0.26790 (by norm_num)
    have hc := hfc 0.26790 (by norm_num) (by norm_num)
    refine lt_of_lt_of_le (by norm_num : (0.95 : ℝ) < 0.96)
      (l5e_le_firstSwitchTime hz hc fun t ht htT ↦ ⟨?_, ?_⟩)
    · have hχA := l5e_chiA_pos (l5e_scale_iv hβ (by norm_num : (0 : ℝ) < 1 - 0.26790)).1
        (l5e_scale_iv hγ (by norm_num : (0 : ℝ) < 0.26790)).2
        (l5e_scale_iv hδ (by norm_num : (0 : ℝ) < (1 - 0.26790) * 0.26790)).1 ht htT.le
        (m := 0.839323) (κ := 0.0018) (by norm_num) (by norm_num) (by norm_num)
      have h := (l5e_seg_ham 0.26790 t).1
      nlinarith [mul_pos hs3 hχA]
    · have hχB := l5e_chiB_pos (hΔB 0.26790 ⟨by norm_num, by norm_num⟩) ht
      have h := (l5e_seg_ham 0.26790 t).2
      nlinarith [mul_pos hs3 hχB]
  · have hc := hfc 0.26791 (by norm_num) (by norm_num)
    -- `1` beats `ζ` at `t = 0.84` (`χ_A(0.84) < 0`)
    refine lt_of_le_of_lt (l5e_firstSwitchTime_le hc (t := 0.84) (by norm_num) one_mem_VT ?_)
      (by norm_num)
    have h := (l5e_seg_ham 0.26791 0.84).1
    have hχ : -(0.84 : ℝ) ^ 3 / 12 + (1 - 0.26791) * l5eβ * 0.84 ^ 2 -
        0.26791 * l5eγ * 0.84 + (1 - 0.26791) * 0.26791 * l5eδ < 0 := by
      linarith [hβ.2, hγ.1, hδ.2]
    nlinarith [mul_pos hs3 (neg_pos.2 hχ)]
  · linarith [l5e_sqrt3_bounds.2]

end SmoothedPolygons
