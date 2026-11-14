module

public import SmoothedPolygons.Ch16.BasinHypotheses
public import SmoothedPolygons.Ch15.FixedPointCells
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# Chapter 16: Theorem 16.1.1, the global basin of attraction of `q_out`

Theorem 16.1.1 (`thm:basin`) of Hales–Vajjha, *Packings of Smoothed Polygons* (TeX 12505–12744):
every orbit of the Fuller–Poincaré map `F_ang` on `Ξ_{𝒲,0}/V_T` other than the fixed point `q_in`
tends to the fixed point `q_out`. It is proved here from the three named numerical facts of
`SmoothedPolygons/Ch16/BasinHypotheses.lean` (Table 16.1 and the contraction on `𝒟_out`), which are
explicit hypotheses of `theorem16_1_1`.

## The book's proof, and this proof

The book (TeX 12511–12744): partition the two closed big cells into `𝒟₀, …, 𝒟₄` with continuous
branches `F_i`, and `𝒟₁` further into the boxes `𝒟_{1,ij}`; Table 16.1 lists the containments
`F_i(𝒟) ⊆ ⋃ 𝒟*` ("upper triangular", with diagonal entries only for `𝒟_in`, `𝒟_out` and
`𝒟₁ ∖ 𝒟_in`); then (a) a point `q ≠ q_in` of `𝒟_in` eventually leaves `𝒟_in`, "because the
iterates `F^{-k}(τ q)` exit `𝒟_out`", (b) by the triangular structure the orbit eventually stays in
`𝒟₁ ∖ 𝒟_in`, (c) the subclaims make the boxes `𝒟_{1,ij}` strictly decrease in the lexicographic
order until `𝒟_{1,00} = 𝒟_out`, and (d) "once in the small rectangle `𝒟_out` containing `q_out`,
the iterates rapidly converge to the fixed point `q_out`".

This proof follows the same steps with the box regions of `BasinHypotheses.lean`:
1. **Convergence in `𝒟_out`** (step (d); gap G16.3): from `DOutContracts`, `F^N(𝒟₀₀) ⊆ B` and `F`
   is a contraction `g` of the box `B` in coordinates; the contraction mapping theorem gives
   `F^k(x) → q_out` for `x ∈ 𝒟₀₀` (`l5st_tendsto_qOut0_of_mem_boxSet`), and a backward orbit inside
   `𝒟₀₀` is constant at `q_out` (`l5st_eq_qOut0_of_backward_orbit`).
2. **`𝒟₂₂` is never re-entered** (replacing (b) and the last row's exclusion argument, gap G16.5):
   for a switching point `x` (every `F(y)` is one), `F(x) ∈ 𝒟₂₂` implies `x ∈ 𝒟₂₂`, because
   `τ(𝒟₂₂) = 𝒟₀₀`, `F(τ F(x)) = τ(x)` (`F⁻¹ = τ F τ` at switching points) and `F(𝒟₀₀) ⊆ 𝒟₀₀`
   (`l5st_mem_boxSet_22_of_poincareAngZero_mem`).
3. **Leaving `𝒟₂₂`** (step (a)): if `F^n(q) ∈ 𝒟₂₂` for all `n ≥ 1`, then `w_j := τ F^{j+1}(q)` is a
   backward orbit in `𝒟₀₀` (`F(w_{j+1}) = w_j` by `F⁻¹ = τ F τ`), so `w₀ = q_out` by step 1 and
   `F(q) = q_in`; and `F⁻¹(q_in) = {q_in}` (`poincareAngZero_eq_qIn0_iff`), so `q = q_in`.
4. **Descent** (step (c), with the rows `𝒟₄`, `𝒟₂`, `𝒟₃`): outside `𝒟₂₂`, a point of the second
   cell reaches `𝒟₀₀` within three steps (`CellTwoEntersDOut`), and a point of a box `𝒟_{ij}` of the
   first cell goes to the second cell or to a smaller box (`BoxSubclaims`); by induction on the
   lexicographic order the orbit reaches `𝒟₀₀` (`l5st_exists_iterate_mem_boxSet_00`).

Departures from the paper (all forced by gaps of the book's argument, and recorded in
`BasinHypotheses.lean`): the boundary method (gap G16.2) is replaced by containments to be
certified by direct enclosure; the convergence in `𝒟_out` uses a contraction hypothesis
(gap G16.3); `𝒟_in` is the whole box `𝒟₂₂` and the exclusion argument for the last row
(`𝒟₀ ⊂ 𝒟_in`, `𝒟₄ ⊂ F(𝒟₂₂)` and the injectivity of the multi-valued `F`, gap G16.5) is replaced by
step 2, which uses the time reversal as the book's step (a) does; the map is the Poincaré map of
`Ξ_{𝒲,0}/V_T`, at whose non-switching points `F⁻¹ = τ F τ` fails (gap G15.6), which steps 2–3
handle (every image is a switching point; `F⁻¹(q_in) = {q_in}`).
-/

@[expose] public section

namespace SmoothedPolygons

open Set Filter Topology
open scoped Real

namespace TriFuller

/-- `q_out` and `q_in` are fixed points of `F` on `Ξ_{𝒲,0}/V_T` (Lemma 13.5.2, `lemma13_5_2`), and
`τ` exchanges them (`tauQuot_qOut`). -/
theorem poincareAngZero_qOut0_qIn0 :
    poincareAngZero qOut0 = qOut0 ∧ poincareAngZero qIn0 = qIn0 ∧ tauZero qOut0 = qIn0 ∧
      tauZero qIn0 = qOut0 := by
  have hfix := lemma13_5_2.1
  have hO := (Set.ext_iff.1 hfix qOut).2 (Or.inl rfl)
  have hI := (Set.ext_iff.1 hfix qIn).2 (Or.inr rfl)
  have hτ : tauZero qOut0 = qIn0 := Subtype.ext tauQuot_qOut
  refine ⟨Subtype.ext hO.1, Subtype.ext hI.1, hτ, ?_⟩
  rw [← hτ]
  exact continuous_involutive_tauZero.2 qOut0

/-- The breakpoints of the boxes. -/
private lemma l5f_basin_vals :
    basinA 0 = 0 ∧ basinA 1 = π / 3 ∧ basinA 2 = 2 * π / 3 ∧ basinA 3 = π ∧
      basinB 0 = π ∧ basinB 1 = π - 1.1 ∧ basinB 2 = 1.1 ∧ basinB 3 = 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- "We have `q_in ∈ 𝒟_in := 𝒟_{1,22}` and `q_out ∈ 𝒟_out := 𝒟_{1,00} = 𝒟₀₀`" (TeX 12536–12537),
for the boxes: `pOut ≈ (0.2679, 0.1706, 2.9157) ∈ 𝒟₀₀` and `pIn ≈ (0.2679, 2.9710, 0.2259) ∈ 𝒟₂₂`
(Remark 15.3.1 corrected; from the enclosures of `remark15_3_1`). -/
theorem pOut_mem_cellBox_pIn_mem_cellBox : pOut ∈ cellBox 0 0 ∧ pIn ∈ cellBox 2 2 := by
  obtain ⟨⟨⟨h0, h0'⟩, -, ⟨-, h2'⟩⟩, -, -, h1b, h2b, hIn, -⟩ := remark15_3_1
  obtain ⟨a0, a1, a2, a3, b0, b1, b2, b3⟩ := l5f_basin_vals
  have hpi := Real.two_le_pi
  have hpi' := Real.pi_le_four
  rw [abs_lt] at h1b h2b
  norm_num at h1b h2b
  obtain ⟨h1b, h1b'⟩ := h1b
  obtain ⟨h2b, h2b'⟩ := h2b
  refine ⟨?_, ?_⟩
  · change pOut 0 ∈ Icc 0 1 ∧ pOut 1 ∈ Icc (basinA 0) (basinA 1) ∧
      pOut 2 ∈ Icc (basinB 1) (basinB 0)
    rw [a0, a1, b0, b1]
    exact ⟨⟨h0.le, h0'.le⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · change pIn 0 ∈ Icc 0 1 ∧ pIn 1 ∈ Icc (basinA 2) (basinA 3) ∧
      pIn 2 ∈ Icc (basinB 3) (basinB 2)
    rw [a2, a3, b2, b3, hIn]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    exact ⟨⟨h0.le, h0'.le⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-! ### The arc of the inward spiral (private helpers) -/

/-- The third coordinate of the flow (13.2.2), with real coefficients of the powers of `t`. -/
private lemma l5f_flow_two (t : ℝ) (z : Fin 3 → ℂ) (u : ℂ) :
    flow t z u 2 = z 2 + z 1 * (t : ℂ) + z 0 * ((t ^ 2 / 2 : ℝ) : ℂ) -
      Complex.I * u * ((t ^ 3 / 6 : ℝ) : ℂ) := by
  simp only [flow, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  push_cast
  ring

/-- The third coordinate of the flow with the control `ζ`, in real coordinates. -/
private lemma l5f_flow_two_ζ (t : ℝ) (z : Fin 3 → ℂ) :
    (flow t z ζ 2).re = (z 2).re + (z 1).re * t + (z 0).re * t ^ 2 / 2 + √3 * t ^ 3 / 12 ∧
      (flow t z ζ 2).im = (z 2).im + (z 1).im * t + (z 0).im * t ^ 2 / 2 + t ^ 3 / 12 := by
  rw [l5f_flow_two]
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.add_im, Complex.sub_im,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, ζ_re, ζ_im]
  constructor <;> ring

/-- The signs of the coordinates of (13.5.1): `qOutCart = (-1 + ib, x + iy, z₃)` with `b > 0` and
`x < 0 < y` (`r_scale > 6.27`). -/
private lemma l5f_qOutCart_signs :
    0 < (qOutCart 0).im ∧ (qOutCart 1).re < 0 ∧ 0 < (qOutCart 1).im := by
  have hr : 6.27 < rScale := rScale_bounds.1
  have hs : 0 < √3 := by positivity
  have e0 : (qOutCart 0).im = (-1 + rScale) / (√3 * (1 + rScale)) := by
    simp only [qOutCart, equilExact, Matrix.cons_val_zero, Complex.add_im, Complex.neg_im,
      Complex.one_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  have e1 : (qOutCart 1).re = -((-1 + rScale ^ 3) / (√3 * (1 + rScale ^ 3))) := by
    simp only [qOutCart, equilExact, Matrix.cons_val_one, Matrix.cons_val_zero, Complex.add_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have e2 : (qOutCart 1).im = (1 - 3 * rScale - 2 * rScale ^ 2 - 3 * rScale ^ 3 + rScale ^ 4) /
      (3 * (1 + rScale + rScale ^ 3 + rScale ^ 4)) := by
    simp only [qOutCart, equilExact, Matrix.cons_val_one, Matrix.cons_val_zero, Complex.add_im,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hr0 : 0 < rScale := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [e0]
    exact div_pos (by linarith) (by positivity)
  · rw [e1, neg_lt_zero]
    have : 1 < rScale ^ 3 := one_lt_pow₀ (by linarith) (by norm_num)
    exact div_pos (by linarith) (by positivity)
  · rw [e2]
    refine div_pos ?_ (by positivity)
    have h3 : 0 < rScale ^ 3 := by positivity
    nlinarith [mul_pos h3 (by linarith : (0 : ℝ) < rScale - 6), mul_pos hr0 hr0]

/-- The first control at a point with `z₃ ∈ ℝ_{<0}` and `y₂ > 0` is `ζ` (the lexicographic rule of
Lemma 13.2.6: `RR(z₃, ζ) = RR(z₃, ζ²) > RR(z₃, 1)`, and the tie is broken by
`RR(z₂, ζ) - RR(z₂, ζ²) = √3 y₂ > 0`). -/
private lemma l5f_firstControl_eq_ζ {z : Fin 3 → ℂ} (hz : z ≠ 0) (h2 : (z 2).im = 0)
    (h2' : (z 2).re < 0) (h1 : 0 < (z 1).im) : firstControl z = ζ := by
  have hs : 0 < √3 := by positivity
  obtain ⟨hV, hmax⟩ := firstControl_mem_lexMaxControls hz
  rcases mem_VT.1 hV with h | h | h
  · exfalso
    rw [h] at hmax
    refine hmax ζ ζ_mem_VT ⟨0, fun j hj ↦ absurd hj (Fin.not_lt_zero j), ?_⟩
    simp only [controlVector, Pi.sub_apply, Matrix.cons_val_zero, RR_eq_re_mul_add_im_mul, ζ_re,
      ζ_im, Complex.one_re, Complex.one_im, h2]
    linarith
  · exact h
  · exfalso
    rw [h] at hmax
    refine hmax ζ ζ_mem_VT ⟨1, fun j hj ↦ ?_, ?_⟩
    · obtain rfl : j = 0 := (Fin.lt_one_iff j).1 hj
      simp only [controlVector, Pi.sub_apply, Matrix.cons_val_zero, RR_eq_re_mul_add_im_mul,
        ζ_re, ζ_im, ζ_sq_re, ζ_sq_im, h2]
      ring
    · simp only [controlVector, Pi.sub_apply, Matrix.cons_val_one, Matrix.cons_val_zero,
        RR_eq_re_mul_add_im_mul, ζ_re, ζ_im, ζ_sq_re, ζ_sq_im]
      nlinarith

/-- The flow under the virial group: `z(t, v (ρ z₁, ρ² z₂, ρ³ z₃), v u) = v (ρ-scaling)z(t/ρ, z, u)`
(Lemmas 13.2.1 and 13.2.2 for constant controls). -/
private lemma l5f_flow_smul_scale {ρ : ℝ} (hρ : ρ ≠ 0) (t : ℝ) (v u : ℂ) (z : Fin 3 → ℂ) :
    flow t (v • scale ρ z) (v * u) = v • scale ρ (flow (t / ρ) z u) := by
  have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ
  funext j
  fin_cases j <;> simp [flow, scale] <;> field_simp

/-- `τ(v · (c z₁, c² z₂, c³ z₃)) = v̄ · (c-scaling)(τ z)` for real `c`. -/
private lemma l5f_tau_smul_scale (v : ℂ) (c : ℝ) (z : Fin 3 → ℂ) :
    tau (v • scale c z) = starRingEnd ℂ v • scale c (tau z) := by
  funext j
  fin_cases j <;> simp [tau, scale]

/-- Composition of virial actions. -/
private lemma l5f_smul_scale_smul_scale (v w : ℂ) (c d : ℝ) (z : Fin 3 → ℂ) :
    v • scale c (w • scale d z) = (v * w) • scale (c * d) z := by
  funext j
  fin_cases j <;> simp [scale] <;> ring

/-- A constant-control trajectory passes through each point at most once (`z₁(t) = z₁ - itu`). -/
private lemma l5f_eq_of_flow_eq {t t' : ℝ} {z : Fin 3 → ℂ} {u : ℂ} (hu : u ≠ 0)
    (h : flow t z u = flow t' z u) : t = t' := by
  have h0 := congrFun h 0
  simp only [flow, Matrix.cons_val_zero] at h0
  have : ((t : ℂ) - t') * (Complex.I * u) = 0 := by linear_combination -h0
  rcases mul_eq_zero.1 this with h1 | h1
  · exact_mod_cast sub_eq_zero.1 h1
  · exact absurd h1 (mul_ne_zero Complex.I_ne_zero hu)

/-- A point of the open sector where `ζ` is the only maximizer of `RR(·, w)` over `V_T`
(`Im w > 0` beats `ζ²`, `RR(ζ - 1, w) > 0` beats `1`) is not on a wall: on `𝒲₀` the imaginary part
vanishes, on `𝒲₁ = ℝ_{≤0} ζ` it is `≤ 0`, and on `𝒲₂ = ℝ_{≤0} ζ²` the controls `1` and `ζ` tie. -/
private lemma l5f_not_mem_walls {w : ℂ} (him : 0 < w.im) (hRR : 0 < RR (ζ - 1) w) :
    w ∉ walls := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hs : 0 < √3 := by positivity
  rw [RR_eq_re_mul_add_im_mul, Complex.sub_re, Complex.sub_im, ζ_re, ζ_im, Complex.one_re,
    Complex.one_im] at hRR
  rintro ((⟨s, hs0, rfl⟩ | ⟨s, hs0, rfl⟩) | ⟨s, hs0, rfl⟩)
  · simp at him
  · rw [pow_one, Complex.im_ofReal_mul, ζ_im] at him
    nlinarith
  · rw [Complex.re_ofReal_mul, Complex.im_ofReal_mul, ζ_sq_re, ζ_sq_im] at hRR
    have : (-1 / 2 - 1) * (s * (-1 / 2)) + (√3 / 2 - 0) * (s * -(√3 / 2)) = 0 := by
      linear_combination (-s / 4) * h3
    linarith

/-- A cubic `c₀ + c₁t + c₂t² + c₃t³` with `c₀ > 0`, `c₁, c₂ ≥ 0` and a root `T` is positive on
`[0, T)`: `T³ f(t) = c₀(T³ - t³) + c₁tT(T² - t²) + c₂t²T²(T - t)` there (the argument of
`firstSwitchTime_qOutCart`). -/
private lemma l5f_cubic_pos {c₀ c₁ c₂ c₃ T t : ℝ} (h₀ : 0 < c₀) (h₁ : 0 ≤ c₁) (h₂ : 0 ≤ c₂)
    (hT : c₀ + c₁ * T + c₂ * T ^ 2 + c₃ * T ^ 3 = 0) (ht : 0 ≤ t) (htT : t < T) :
    0 < c₀ + c₁ * t + c₂ * t ^ 2 + c₃ * t ^ 3 := by
  have hT0 : 0 < T := ht.trans_lt htT
  have key : T ^ 3 * (c₀ + c₁ * t + c₂ * t ^ 2 + c₃ * t ^ 3) =
      c₀ * (T ^ 3 - t ^ 3) + c₁ * t * T * (T ^ 2 - t ^ 2) + c₂ * t ^ 2 * T ^ 2 * (T - t) := by
    linear_combination t ^ 3 * hT
  have e1 : 0 < T ^ 3 - t ^ 3 := by
    have := pow_lt_pow_left₀ htT ht (by norm_num : (3 : ℕ) ≠ 0)
    linarith
  have e2 : 0 ≤ T ^ 2 - t ^ 2 := by
    have := pow_le_pow_left₀ ht htT.le 2
    linarith
  have e3 : 0 < c₀ * (T ^ 3 - t ^ 3) := mul_pos h₀ e1
  have e4 : 0 ≤ c₁ * t * T * (T ^ 2 - t ^ 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg h₁ ht) hT0.le) e2
  have e5 : 0 ≤ c₂ * t ^ 2 * T ^ 2 * (T - t) :=
    mul_nonneg (mul_nonneg (mul_nonneg h₂ (sq_nonneg t)) (sq_nonneg T)) (by linarith)
  have hpos : 0 < T ^ 3 * (c₀ + c₁ * t + c₂ * t ^ 2 + c₃ * t ^ 3) := by
    rw [key]
    linarith
  exact pos_of_mul_pos_right hpos (by positivity)

/-- **The arc of the inward spiral does not meet the walls in its interior**: along
`t ↦ z(t, τ(qOutCart), u)` with `u` the first control of `τ(qOutCart)`, `z₃(t) ∉ 𝒲` for
`0 < t < t_sw`. By Lemma 13.2.4 the switching functions along this arc are those along the arc of
`qOutCart` reversed in time, and along that arc `χ_{ζ→ζ²}(t) = √3 t (y + bt/2 + t²/12) > 0` and
`χ_{ζ→1} > 0` on `(0, t_sw)` (the computation of `firstSwitchTime_qOutCart`, TeX 11340–11344;
`SmoothedPolygons/Ch13/FixedPoints.lean`), so `z₃(t)` stays in the open sector where `ζ` is the
only maximizer, which contains no point of `𝒲`. The reduction is to `τ` of the rotated and
rescaled copy `ζ · scale(1/r_scale)` of the arc of `qOutCart`. Prove it by this symmetry, not by a
direct numerical bound: along the arc of `τ(qOutCart)` the polynomial `χ_{ζ→ζ²}/t` has
discriminant about `-5.45·10⁻⁵` and minimum about `2.8·10⁻⁴` at `t ≈ 1.256`, just after the
switch at `t_sw ≈ 1.180`. -/
theorem flow_tau_qOutCart_not_mem_walls :
    ∀ t ∈ Ioo 0 (firstSwitchTime (tau qOutCart)),
      flow t (tau qOutCart) (firstControl (tau qOutCart)) 2 ∉ walls := by
  obtain ⟨hb, hx, hy⟩ := l5f_qOutCart_signs
  obtain ⟨h0re, h2im, h2re⟩ := qOutCart_normalization
  have hr0 : 0 < rScale := by linarith [rScale_spec.1]
  have hq0 := qOutCart_ne_zero
  have hτ0 := tau_qOutCart_ne_zero
  have hs3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hs : 0 < √3 := by positivity
  have hζ0 : ζ ≠ 0 := fun h ↦ by simpa [h] using norm_ζ
  have hζ3 : ζ * ζ * ζ = 1 := by rw [← ζ_pow_three]; ring
  -- the first controls of `qOutCart` and `τ(qOutCart)` are `ζ` (Lemma 13.2.6)
  have hfc : firstControl qOutCart = ζ := l5f_firstControl_eq_ζ hq0 h2im h2re hy
  have hfcτ : firstControl (tau qOutCart) = ζ := by
    refine l5f_firstControl_eq_ζ hτ0 ?_ ?_ ?_ <;> simp [tau, h2im, h2re, hy]
  -- the arc of `qOutCart` ends at `F(qOutCart) = ζ² (r_scale-scaling)(qOutCart)` (Lemma 13.5.2)
  have hF := poincare_qOutCart
  rw [poincare, hfc] at hF
  -- Lemma 13.2.4/13.2.5: the arc of `τ(qOutCart)` with control `ζ` is the arc of `qOutCart`
  -- reversed in time about `t_sw`, conjugated by `τ`, rotated by `ζ²` and rescaled by `1/r_scale`
  have harc : ∀ s : ℝ, flow s (tau qOutCart) ζ = ζ ^ 2 • scale rScale⁻¹
      (tau (flow (firstSwitchTime qOutCart - rScale * s) qOutCart ζ)) := by
    intro s
    have e1 : flow (firstSwitchTime qOutCart - rScale * s) qOutCart ζ =
        flow (-(rScale * s)) (ζ ^ 2 • scale rScale qOutCart) ζ := by
      rw [← hF, ← flow_add, sub_eq_add_neg]
    have e2 : flow (rScale * s) (ζ • scale rScale (tau qOutCart)) (ζ * ζ) =
        ζ • scale rScale (flow s (tau qOutCart) ζ) := by
      rw [l5f_flow_smul_scale hr0.ne', mul_div_cancel_left₀ s hr0.ne']
    rw [e1, tau_flow_neg, conj_ζ, l5f_tau_smul_scale, conj_ζ_sq, pow_two ζ, e2,
      l5f_smul_scale_smul_scale, hζ3, inv_mul_cancel₀ hr0.ne', one_smul, scale_one]
  -- hence `t_sw(τ qOutCart) = t_sw(qOutCart)/r_scale` (`F(τ qOutCart)`, Lemma 13.5.2)
  have hT' : firstSwitchTime (tau qOutCart) = firstSwitchTime qOutCart / rScale := by
    have h1 := poincare_tau_qOutCart
    rw [poincare, hfcτ] at h1
    refine l5f_eq_of_flow_eq hζ0 (h1.trans ?_)
    rw [harc, show firstSwitchTime qOutCart - rScale * (firstSwitchTime qOutCart / rScale) = 0 by
      field_simp; ring, flow_zero]
  -- along the outward arc, `χ_{ζ→1}` is a cubic with coefficients `+ + + -` vanishing at `t_sw`
  have hRR : ∀ τ' : ℝ, RR (ζ - 1) (flow τ' qOutCart ζ 2) =
      -3 / 2 * (qOutCart 2).re + (-3 / 2 * (qOutCart 1).re + √3 / 2 * (qOutCart 1).im) * τ' +
        (3 / 4 + √3 / 4 * (qOutCart 0).im) * τ' ^ 2 + -(√3 / 12) * τ' ^ 3 := by
    intro τ'
    obtain ⟨e1, e2⟩ := l5f_flow_two_ζ τ' qOutCart
    rw [RR_eq_re_mul_add_im_mul, e1, e2, Complex.sub_re, Complex.sub_im, ζ_re, ζ_im,
      Complex.one_re, Complex.one_im, h0re, h2im]
    ring
  have hfT : RR (ζ - 1) (flow (firstSwitchTime qOutCart) qOutCart ζ 2) = 0 := by
    rw [hF]
    have e : (ζ ^ 2 • scale rScale qOutCart) 2 =
        ζ ^ 2 * (((rScale ^ 3 : ℝ) : ℂ) * qOutCart 2) := by
      simp only [Pi.smul_apply, smul_eq_mul, scale, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons]
      push_cast
      ring
    rw [e, RR_eq_re_mul_add_im_mul]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, h2im,
      Complex.sub_re, Complex.sub_im, ζ_re, ζ_im, ζ_sq_re, ζ_sq_im, Complex.one_re,
      Complex.one_im]
    linear_combination (-(rScale ^ 3 * (qOutCart 2).re) / 4) * hs3
  rw [hRR] at hfT
  have hc0 : 0 < -3 / 2 * (qOutCart 2).re := by linarith
  have hc1 : 0 ≤ -3 / 2 * (qOutCart 1).re + √3 / 2 * (qOutCart 1).im := by nlinarith
  have hc2 : 0 ≤ 3 / 4 + √3 / 4 * (qOutCart 0).im := by positivity
  -- the point `t` of the inward arc is the point `s = t_sw - r_scale t` of the outward arc
  intro t ht
  rw [hT'] at ht
  obtain ⟨ht0, ht1⟩ := ht
  rw [lt_div_iff₀ hr0] at ht1
  rw [hfcτ, harc]
  have hs0 : 0 < firstSwitchTime qOutCart - rScale * t := by linarith
  have hs1 : firstSwitchTime qOutCart - rScale * t < firstSwitchTime qOutCart := by
    nlinarith [mul_pos hr0 ht0]
  -- there both switching functions from `ζ` are positive
  have hWim : 0 < (flow (firstSwitchTime qOutCart - rScale * t) qOutCart ζ 2).im := by
    rw [(l5f_flow_two_ζ _ qOutCart).2, h2im]
    positivity
  have hWRR : 0 < RR (ζ - 1) (flow (firstSwitchTime qOutCart - rScale * t) qOutCart ζ 2) := by
    rw [hRR]
    exact l5f_cubic_pos hc0 hc1 hc2 hfT hs0.le hs1
  -- and the reversal exchanges them: `Im` of the image is `RR(ζ - 1, w)/√3`, up to `r_scale⁻³`,
  -- and `RR(ζ - 1, ·)` of the image is `√3 Im w`
  generalize flow (firstSwitchTime qOutCart - rScale * t) qOutCart ζ = Z at hWim hWRR ⊢
  have e : (ζ ^ 2 • scale rScale⁻¹ (tau Z)) 2 =
      ((rScale⁻¹ ^ 3 : ℝ) : ℂ) * (ζ ^ 2 * starRingEnd ℂ (Z 2)) := by
    simp only [Pi.smul_apply, smul_eq_mul, scale, tau, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    push_cast
    ring
  rw [e]
  have hc : 0 < rScale⁻¹ ^ 3 := by positivity
  rw [RR_eq_re_mul_add_im_mul, Complex.sub_re, Complex.sub_im, ζ_re, ζ_im, Complex.one_re,
    Complex.one_im] at hWRR
  apply l5f_not_mem_walls
  · rw [Complex.im_ofReal_mul]
    refine mul_pos hc ?_
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im, ζ_sq_re, ζ_sq_im]
    nlinarith [mul_pos hs hWRR]
  · rw [RR_ofReal_mul_right]
    refine mul_pos hc ?_
    simp only [RR_eq_re_mul_add_im_mul, Complex.mul_re, Complex.mul_im, Complex.conj_re,
      Complex.conj_im, ζ_sq_re, ζ_sq_im, Complex.sub_re, Complex.sub_im, ζ_re, ζ_im,
      Complex.one_re, Complex.one_im]
    nlinarith [mul_pos hs hWim]

/-- The rescaling of a nonzero point is nonzero. -/
private lemma l5f_scale_ne_zero {ρ : ℝ} (hρ : 0 < ρ) {z : Fin 3 → ℂ} (hz : z ≠ 0) :
    scale ρ z ≠ 0 := by
  intro h
  apply hz
  have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  funext j
  have := congrFun h j
  fin_cases j <;> simpa [scale, hρ'] using this

/-- `s ζⁿ ∈ 𝒲` for `s ≤ 0` (`ζ³ = 1`). -/
private lemma l5f_ofReal_mul_ζ_pow_mem_walls {s : ℝ} (hs : s ≤ 0) (n : ℕ) :
    (s : ℂ) * ζ ^ n ∈ walls := by
  have e : ζ ^ n = ζ ^ (n % 3) := by
    conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, ζ_pow_three, one_pow, one_mul]
  rw [e]
  rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h | h | h <;> rw [h]
  · exact Or.inl (Or.inl ⟨s, hs, rfl⟩)
  · exact Or.inl (Or.inr ⟨s, hs, rfl⟩)
  · exact Or.inr ⟨s, hs, rfl⟩

/-- The walls are invariant under `V_T` and positive real scalings. -/
private lemma l5f_mul_mem_walls {v : ℂ} (hv : v ∈ VT) {c : ℝ} (hc : 0 ≤ c) {w : ℂ}
    (hw : w ∈ walls) : v * ((c : ℂ) * w) ∈ walls := by
  obtain ⟨j, hj⟩ : ∃ j : ℕ, v = ζ ^ j := by
    rcases mem_VT.1 hv with rfl | rfl | rfl
    exacts [⟨0, by simp⟩, ⟨1, by simp⟩, ⟨2, rfl⟩]
  have key : ∀ k : ℕ, w ∈ wall k → v * ((c : ℂ) * w) ∈ walls := by
    rintro k ⟨s, hs, rfl⟩
    have := l5f_ofReal_mul_ζ_pow_mem_walls (by nlinarith : c * s ≤ 0) (j + k)
    convert this using 1
    rw [hj, pow_add]
    push_cast
    ring
  rcases hw with (hw | hw) | hw
  exacts [key 0 hw, key 1 hw, key 2 hw]

/-- The converse: `v (c w) ∈ 𝒲` with `v ∈ V_T`, `c > 0` implies `w ∈ 𝒲`. -/
private lemma l5f_mem_walls_of_mul {v : ℂ} (hv : v ∈ VT) {c : ℝ} (hc : 0 < c) {w : ℂ}
    (hw : v * ((c : ℂ) * w) ∈ walls) : w ∈ walls := by
  have h := l5f_mul_mem_walls (conj_mem_VT hv) (inv_nonneg.2 hc.le) hw
  have hv1 : starRingEnd ℂ v * v = 1 := by
    rw [Complex.conj_mul', norm_eq_one_of_mem_VT hv]
    simp
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  convert h using 1
  rw [show starRingEnd ℂ v * (((c⁻¹ : ℝ) : ℂ) * (v * ((c : ℂ) * w))) =
      (starRingEnd ℂ v * v) * (((c : ℂ))⁻¹ * c) * w by push_cast; ring, hv1,
    inv_mul_cancel₀ hc0]
  ring

/-- **`F⁻¹(q_in) = {q_in}`** on `Ξ_{𝒲,0}/V_T` (implicit in the book's statement of Theorem 16.1.1:
an orbit that reached `q_in` would stay there). If `x` is a switching point,
`τ(x) = F(τ F(x)) = F(τ q_in) = F(q_out) = q_out`; otherwise `x` lies in the interior of the arc
that ends at `F(x) = q_in` and starts at a switching point `w` with `F(w) = q_in`
(`exists_isSwitchingPoint_of_not`), so `w = q_in` and `x` is an interior point of the arc of `q_in`,
which does not meet the walls (`flow_tau_qOutCart_not_mem_walls`), against `x ∈ Ξ_𝒲`. -/
theorem poincareAngZero_eq_qIn0_iff (x : XiW0Quot) : poincareAngZero x = qIn0 ↔ x = qIn0 := by
  obtain ⟨hFO, hFI, hτO, hτI⟩ := poincareAngZero_qOut0_qIn0
  have hinv := continuous_involutive_tauZero.2
  refine ⟨fun hx ↦ ?_, fun hx ↦ hx ▸ hFI⟩
  -- a switching point `y` with `F(y) = q_in`: `τ(y) = F(τ F(y)) = F(τ q_in) = F(q_out) = q_out`
  have hsw : ∀ y : XiW0Quot, IsSwitchingPointQ y → poincareAngZero y = qIn0 → y = qIn0 := by
    intro y hy hFy
    have e := poincareAngZero_tauZero_poincareAngZero hy
    rw [hFy, hτI, hFO] at e
    rw [← hinv y, ← e, hτO]
  by_cases hx' : IsSwitchingPointQ x
  · exact hsw x hx' hx
  -- otherwise a representative `z` of `x` lies inside the arc from a switching point `w`
  exfalso
  obtain ⟨z, hz, rfl⟩ := exists_classOf_eq x
  have hz0 : z ≠ 0 := hz.1
  obtain ⟨w, hw0, hw2, hwsw, s, hs, hzw, hFw⟩ :=
    exists_isSwitchingPoint_of_not hz0 fun h ↦ hx' ⟨z, hz, rfl, h⟩
  have hwsec : w ∈ sectionZero := by
    refine ⟨hw0, hw2, ?_⟩
    rw [← hamMax_poincare hw0, hFw, hamMax_poincare hz0]
    exact hz.2.2
  -- `F(w) = F(z)`, so the class of `w` is a switching point mapped to `q_in`: it is `q_in`
  have hcw : classOf w = qIn0 := by
    refine hsw _ ⟨w, hwsec, rfl, hwsw⟩ ?_
    rw [poincareAngZero_classOf hwsec, hFw, ← poincareAngZero_classOf hz, hx]
  obtain ⟨-, -, hτsec, hτcl⟩ := classOf_qOutCart
  obtain ⟨v, hv, ρ, hρ, rfl⟩ := (classOf_eq_classOf_iff hτsec hwsec).1 (hτcl.trans hcw.symm)
  -- so `z` is an interior point of the arc of `τ(qOutCart)`, up to the virial group
  have hτ0 := tau_qOutCart_ne_zero
  have hsc0 : scale ρ (tau qOutCart) ≠ 0 := l5f_scale_ne_zero hρ hτ0
  rw [(poincare_smul hv hsc0).2.1, (poincare_scale hρ hτ0).2.1] at hs
  rw [(poincare_smul hv hsc0).1, (poincare_scale hρ hτ0).1, l5f_flow_smul_scale hρ.ne'] at hzw
  have hmem : s / ρ ∈ Ioo 0 (firstSwitchTime (tau qOutCart)) :=
    ⟨div_pos hs.1 hρ, (div_lt_iff₀' hρ).2 hs.2⟩
  -- which does not meet the walls, against `z₃ ∈ 𝒲`
  apply flow_tau_qOutCart_not_mem_walls _ hmem
  apply l5f_mem_walls_of_mul hv (pow_pos hρ 3)
  have h2 := hz.2.1
  rw [hzw] at h2
  convert h2 using 1
  simp [scale]

/-- Every point of `Ξ_{𝒲,0}/V_T` lies in the second big cell or in one of the nine boxes of the
first (Proposition 15.2.2 and `closedBoxOne_eq_iUnion_cellBox`). -/
theorem mem_cellTwoSet_or_exists_mem_boxSet (x : XiW0Quot) :
    x ∈ cellTwoSet ∨ ∃ i j : Fin 3, x ∈ boxSet i j := by
  rcases proposition15_2_2.1 x with h | ⟨p, hp, rfl, -⟩
  · exact Or.inl h
  · rw [closedBoxOne_eq_iUnion_cellBox] at hp
    obtain ⟨i, j, hij⟩ : ∃ i j, p ∈ cellBox i j := by simpa only [mem_iUnion] using hp
    exact Or.inr ⟨i, j, p, hij, rfl⟩

/-! ### The contraction on `𝒟_out` (private helpers) -/

private lemma l5f_openBoxOne_subset_cellDomain : openBoxOne ⊆ cellDomain := by
  rintro p ⟨⟨h0, h0'⟩, ⟨h1, h1'⟩, ⟨h2, h2'⟩⟩
  exact ⟨⟨h0.le, h0'.le⟩, ⟨h1.le, h1'.le⟩, ⟨by linarith [Real.pi_pos], h2'.le⟩⟩

/-- On a box `B` where `F` is `g` in coordinates and `g(B) ⊆ B`, `F^k(cellClass p) =
cellClass (g^k p)`. -/
private lemma l5f_iterate_cellClass {B : Set (Fin 3 → ℝ)} {g : (Fin 3 → ℝ) → (Fin 3 → ℝ)}
    (hg : MapsTo g B B) (hF : ∀ p ∈ B, poincareAngZero (cellClass p) = cellClass (g p))
    {p : Fin 3 → ℝ} (hp : p ∈ B) (k : ℕ) :
    poincareAngZero^[k] (cellClass p) = cellClass (g^[k] p) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, hF _ (hg.iterate k hp), ← Function.iterate_succ_apply' g]

/-- The data of `DOutContracts`, with the fixed point `p₀ ∈ B` of `g` representing `q_out`:
`q_out ∈ 𝒟₀₀` is fixed by `F`, so `q_out = F^N(q_out) = cellClass p₀` with `p₀ ∈ B`, and
`cellClass (g p₀) = F(q_out) = cellClass p₀` gives `g p₀ = p₀` by the injectivity of `cellClass`
on the open first box (`definition15_1_2`). -/
private lemma l5f_contraction_data (h : DOutContracts) :
    ∃ (B : Set (Fin 3 → ℝ)) (N : ℕ) (κ : NNReal) (g : (Fin 3 → ℝ) → (Fin 3 → ℝ))
      (p₀ : Fin 3 → ℝ), κ < 1 ∧ IsClosed B ∧ Bornology.IsBounded B ∧ B ⊆ openBoxOne ∧
      (∀ x ∈ boxSet 0 0, poincareAngZero^[N] x ∈ cellClass '' B) ∧
      MapsTo g B B ∧ LipschitzOnWith κ g B ∧
      (∀ p ∈ B, poincareAngZero (cellClass p) = cellClass (g p)) ∧
      p₀ ∈ B ∧ g p₀ = p₀ ∧ cellClass p₀ = qOut0 := by
  obtain ⟨-, lo, hi, N, κ, hκ, hB, hN, g, hg, hL, hF⟩ := h
  have hq : qOut0 ∈ boxSet 0 0 :=
    ⟨pOut, pOut_mem_cellBox_pIn_mem_cellBox.1, remark15_3_1.2.1⟩
  have hfix := poincareAngZero_qOut0_qIn0.1
  obtain ⟨p₀, hp₀, hcl⟩ : qOut0 ∈ cellClass '' Icc lo hi := by
    have := hN _ hq
    rwa [Function.iterate_fixed hfix] at this
  refine ⟨Icc lo hi, N, κ, g, p₀, hκ, isClosed_Icc, isCompact_Icc.isBounded, hB, hN, hg, hL,
    hF, hp₀, ?_, hcl⟩
  refine definition15_1_2.2.2.2.1 (hB (hg hp₀)) (hB hp₀) ?_
  rw [← hF p₀ hp₀, hcl, hfix]

/-- **Convergence in `𝒟_out`** (TeX 12594–12598, 12742–12743; gap G16.3): under `DOutContracts`,
every orbit starting in `𝒟₀₀` tends to `q_out`. Proof route: `F^N(x) = cellClass p` with `p ∈ B`,
`F^{N+k}(x) = cellClass (g^k p)`; `g` is a contraction of the complete box `B`, so `g^k p → p*`
(`ContractingWith`, Banach's fixed point theorem); `cellClass` is continuous
(`continuousOn_cellClass`); and `cellClass p* = q_out`: `q_out ∈ 𝒟₀₀`
(`pOut_mem_cellBox_pIn_mem_cellBox`) is fixed, so `q_out = cellClass p₀` with `p₀ ∈ B`, `g p₀ = p₀`
by the injectivity of `cellClass` on the open first box (`definition15_1_2`). -/
theorem l5st_tendsto_qOut0_of_mem_boxSet (h : DOutContracts) {x : XiW0Quot}
    (hx : x ∈ boxSet 0 0) : Tendsto (fun k : ℕ ↦ poincareAngZero^[k] x) atTop (𝓝 qOut0) := by
  obtain ⟨B, N, κ, g, p₀, hκ, hBc, -, hB, hN, hg, hL, hFg, hp₀, hgp₀, hcl⟩ :=
    l5f_contraction_data h
  obtain ⟨p, hp, hpx⟩ := hN x hx
  -- the contraction mapping theorem on the complete box `B`: `g^k(p) → p₀`
  have hc : ContractingWith κ (hg.restrict g B B) := ⟨hκ, hL.mapsToRestrict hg⟩
  have : CompleteSpace B := hBc.completeSpace_coe
  have : Nonempty B := ⟨⟨p₀, hp₀⟩⟩
  have hfp : (⟨p₀, hp₀⟩ : B) = ContractingWith.fixedPoint _ hc :=
    hc.fixedPoint_unique (Subtype.ext hgp₀)
  have hlim := hc.tendsto_iterate_fixedPoint ⟨p, hp⟩
  rw [← hfp] at hlim
  -- `cellClass` is continuous on `B`, and `F^{k+N}(x) = cellClass (g^k p)`
  have hcont : Continuous fun y : B ↦ cellClass (y : Fin 3 → ℝ) :=
    (continuousOn_cellClass.mono (hB.trans l5f_openBoxOne_subset_cellDomain)).domRestrict
  have hlim' := (hcont.tendsto _).comp hlim
  rw [← tendsto_add_atTop_iff_nat N]
  have e : ∀ k, poincareAngZero^[k + N] x =
      cellClass (((hg.restrict g B B)^[k] ⟨p, hp⟩ : B) : Fin 3 → ℝ) := by
    intro k
    rw [MapsTo.coe_iterate_restrict, Function.iterate_add_apply, ← hpx,
      l5f_iterate_cellClass hg hFg hp]
  rw [tendsto_congr e, ← hcl]
  exact hlim'

/-- **A backward orbit inside `𝒟_out` is `q_out`** (the book's "the iterates `F^{-k}(τ q)` exit
`𝒟_out`", TeX 12729–12732; gap G16.3): if `w_j ∈ 𝒟₀₀` and `F(w_{j+1}) = w_j` for all `j`, then
`w₀ = q_out`. Proof route: `w_j = F^N(w_{j+N}) ∈ cellClass '' B`, say `w_j = cellClass p_j`; by the
injectivity of `cellClass` on `B`, `g(p_{j+1}) = p_j`; so `p₀ = g^k(p_k)` and
`dist(p₀, p*) ≤ κ^k diam B → 0`. -/
theorem l5st_eq_qOut0_of_backward_orbit (h : DOutContracts) (w : ℕ → XiW0Quot)
    (hw : ∀ j, w j ∈ boxSet 0 0) (hF : ∀ j, poincareAngZero (w (j + 1)) = w j) : w 0 = qOut0 := by
  obtain ⟨B, N, κ, g, p₀, hκ, -, hBb, hB, hN, hg, hL, hFg, hp₀, hgp₀, hcl⟩ :=
    l5f_contraction_data h
  have hinj : InjOn cellClass B := definition15_1_2.2.2.2.1.mono hB
  -- `w j = F^N(w (j + N)) ∈ cellClass '' B`, say `w j = cellClass (p j)`
  have hback : ∀ n j, poincareAngZero^[n] (w (j + n)) = w j := by
    intro n
    induction n with
    | zero => intro j; rfl
    | succ n ih =>
      intro j
      rw [Function.iterate_succ_apply, ← add_assoc, hF, ih]
  have hmem : ∀ j, ∃ q, q ∈ B ∧ cellClass q = w j := by
    intro j
    have := hN _ (hw (j + N))
    rwa [hback N j] at this
  choose p hp hpw using hmem
  -- `g (p (j + 1)) = p j` by the injectivity of `cellClass` on `B`, so `p 0 = g^k (p k)`
  have hgp : ∀ j, g (p (j + 1)) = p j := fun j ↦
    hinj (hg (hp (j + 1))) (hp j) (by rw [← hFg _ (hp (j + 1)), hpw (j + 1), hpw j, hF])
  have hiter : ∀ k, g^[k] (p k) = p 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply, hgp, ih]
  -- the contraction: `dist (p 0) p₀ = dist (g^k (p k)) (g^k p₀) ≤ κ^k diam B → 0`
  have hc : ContractingWith κ (hg.restrict g B B) := ⟨hκ, hL.mapsToRestrict hg⟩
  have hfix : Function.IsFixedPt (hg.restrict g B B) ⟨p₀, hp₀⟩ := Subtype.ext hgp₀
  have hle : ∀ k : ℕ, dist (p 0) p₀ ≤ (κ : ℝ) ^ k * Metric.diam B := by
    intro k
    have e := (hc.toLipschitzWith.iterate k).dist_le_mul ⟨p k, hp k⟩ ⟨p₀, hp₀⟩
    rw [(hfix.iterate k).eq, Subtype.dist_eq, Subtype.dist_eq, MapsTo.coe_iterate_restrict,
      hiter] at e
    calc dist (p 0) p₀ ≤ (κ : ℝ) ^ k * dist (p k) p₀ := by simpa using e
      _ ≤ (κ : ℝ) ^ k * Metric.diam B := by
        gcongr
        exact Metric.dist_le_diam_of_mem hBb (hp k) hp₀
  have hlim : Tendsto (fun k : ℕ ↦ (κ : ℝ) ^ k * Metric.diam B) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one κ.coe_nonneg
      (by exact_mod_cast hκ)).mul_const (Metric.diam B)
  have h0 : dist (p 0) p₀ = 0 := le_antisymm (ge_of_tendsto' hlim hle) dist_nonneg
  rw [← hpw 0, dist_eq_zero.1 h0, hcl]

/-- **`𝒟₂₂` is backward invariant for switching points**: if `x` is a switching point and
`F(x) ∈ 𝒟₂₂`, then `x ∈ 𝒟₂₂`. Proof route: `τ F(x) ∈ τ(𝒟₂₂) = 𝒟₀₀` (`tauZero_image_boxSet`),
`F(τ F(x)) = τ(x)` (`poincareAngZero_tauZero_poincareAngZero`), so `τ(x) ∈ F(𝒟₀₀) ⊆ 𝒟₀₀`
(`DOutContracts`) and `x = τ τ x ∈ 𝒟₂₂`. -/
theorem l5st_mem_boxSet_22_of_poincareAngZero_mem (h : DOutContracts) {x : XiW0Quot}
    (hx : IsSwitchingPointQ x) (hFx : poincareAngZero x ∈ boxSet 2 2) : x ∈ boxSet 2 2 := by
  have hinv := continuous_involutive_tauZero.2
  -- `τ F(x) ∈ τ(𝒟₂₂) = 𝒟₀₀`, so `τ(x) = F(τ F(x)) ∈ F(𝒟₀₀) ⊆ 𝒟₀₀`
  have h1 : tauZero (poincareAngZero x) ∈ boxSet 0 0 := by
    rw [← tauZero_image_boxSet.2]
    exact mem_image_of_mem _ hFx
  have h2 : tauZero x ∈ boxSet 0 0 := by
    rw [← poincareAngZero_tauZero_poincareAngZero hx]
    exact h.1 h1
  rw [← tauZero_image_boxSet.1]
  exact ⟨tauZero x, h2, hinv x⟩

/-- **An orbit staying in `𝒟₂₂` is `q_in`** (the book's step for `𝒟_in`, TeX 12728–12733): if `x`
is a switching point and `F^n(x) ∈ 𝒟₂₂` for every `n`, then `x = q_in`. Proof route:
`w_j := τ F^j(x) ∈ 𝒟₀₀` and `F(w_{j+1}) = F(τ F(F^j x)) = τ F^j(x) = w_j` (`F^j(x)` is a switching
point), so `τ(x) = w₀ = q_out` (`l5st_eq_qOut0_of_backward_orbit`). -/
theorem l5st_eq_qIn0_of_forall_iterate_mem_boxSet_22 (h : DOutContracts) {x : XiW0Quot}
    (hx : IsSwitchingPointQ x) (hin : ∀ n, poincareAngZero^[n] x ∈ boxSet 2 2) : x = qIn0 := by
  have hinv := continuous_involutive_tauZero.2
  -- every `F^j(x)` is a switching point
  have hsw : ∀ n, IsSwitchingPointQ (poincareAngZero^[n] x) := by
    intro n
    cases n with
    | zero => exact hx
    | succ n =>
      rw [Function.iterate_succ_apply']
      exact isSwitchingPointQ_poincareAngZero _
  -- `w_j = τ F^j(x)` is a backward orbit in `𝒟₀₀`
  have h0 := l5st_eq_qOut0_of_backward_orbit h (fun j ↦ tauZero (poincareAngZero^[j] x))
    (fun j ↦ by
      rw [← tauZero_image_boxSet.2]
      exact mem_image_of_mem _ (hin j))
    (fun j ↦ by
      rw [Function.iterate_succ_apply']
      exact poincareAngZero_tauZero_poincareAngZero (hsw j))
  simp only [Function.iterate_zero, id] at h0
  rw [← hinv x, h0, poincareAngZero_qOut0_qIn0.2.2.1]

/-- **Descent to `𝒟_out`** (TeX 12734–12743, with the rows `𝒟₄`, `𝒟₂`, `𝒟₃` of Table 16.1): an orbit
that never meets `𝒟₂₂` reaches `𝒟₀₀`. Proof route: by well-founded induction on the least box (in
the lexicographic order) containing the current point when it is not in the second cell: a point
of the second cell reaches `𝒟₀₀` within three steps (`CellTwoEntersDOut`); a point of a box
`(i, j) ≠ (0, 0)` (and `≠ (2, 2)`, the orbit avoiding `𝒟₂₂`) goes to the second cell or to a
smaller box (`BoxSubclaims`); every point is in one of these regions
(`mem_cellTwoSet_or_exists_mem_boxSet`). -/
theorem l5st_exists_iterate_mem_boxSet_00 (h₂ : CellTwoEntersDOut) (h₃ : BoxSubclaims)
    {x : XiW0Quot} (hin : ∀ n, poincareAngZero^[n] x ∉ boxSet 2 2) :
    ∃ n, poincareAngZero^[n] x ∈ boxSet 0 0 := by
  -- from the second cell, `𝒟₀₀` within three steps
  have hcell : ∀ y ∈ cellTwoSet, ∃ n, poincareAngZero^[n] y ∈ boxSet 0 0 := fun y hy ↦
    let ⟨n, _, hn⟩ := h₂ y hy
    ⟨n, hn⟩
  -- induction on the rank `3i + j` of the box (the lexicographic order)
  suffices H : ∀ m : ℕ, ∀ y : XiW0Quot, (∀ n, poincareAngZero^[n] y ∉ boxSet 2 2) →
      ∀ i j : Fin 3, 3 * (i : ℕ) + j = m → y ∈ boxSet i j →
        ∃ n, poincareAngZero^[n] y ∈ boxSet 0 0 by
    rcases mem_cellTwoSet_or_exists_mem_boxSet x with hx | ⟨i, j, hx⟩
    · exact hcell x hx
    · exact H _ x hin i j rfl hx
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro y hy i j hm hyij
    by_cases hc : y ∈ cellTwoSet
    · exact hcell y hc
    by_cases h00 : (i, j) = (0, 0)
    · rw [Prod.mk.injEq] at h00
      obtain ⟨rfl, rfl⟩ := h00
      exact ⟨0, hyij⟩
    by_cases h22 : (i, j) = (2, 2)
    · rw [Prod.mk.injEq] at h22
      obtain ⟨rfl, rfl⟩ := h22
      exact absurd hyij (hy 0)
    have hy1 : ∀ n, poincareAngZero^[n] (poincareAngZero y) ∉ boxSet 2 2 := fun n ↦ by
      rw [← Function.iterate_succ_apply]
      exact hy (n + 1)
    -- one step goes to the second cell or to a smaller box (`BoxSubclaims`)
    rcases h₃ i j h00 h22 y hyij hc with hF | ⟨k, l, hlt, hF⟩
    · obtain ⟨n, hn⟩ := hcell _ hF
      exact ⟨n + 1, by rw [Function.iterate_succ_apply]; exact hn⟩
    · have hlt' : 3 * (k : ℕ) + l < m := by
        rw [← hm]
        have hl := l.isLt
        have hj := j.isLt
        rcases hlt with hlt | ⟨rfl, hlt⟩
        · have := Fin.lt_def.1 hlt
          omega
        · have := Fin.lt_def.1 hlt
          omega
      obtain ⟨n, hn⟩ := ih _ hlt' _ hy1 k l rfl hF
      exact ⟨n + 1, by rw [Function.iterate_succ_apply]; exact hn⟩

end TriFuller

open TriFuller

/-- **Theorem 16.1.1 (Global Basin)** (`thm:basin`, TeX 12505–12509). "Let `q ≠ q_in` be a point in
`Ξ_{𝒲,0}/V_T`. Then the iterates `F^k q` under the Fuller–Poincaré map tend to the fixed point
`q_out`."

Here `F` is the Poincaré map `poincareAngZero` of `Ξ_{𝒲,0}/V_T` (Lemma 13.5.5), and the numerical
facts the book takes from Mathematica (Table 16.1, Figures 16.1–16.4) and the contraction on
`𝒟_out` that it does not prove (gap G16.3) are the explicit hypotheses `DOutContracts`,
`CellTwoEntersDOut`, `BoxSubclaims` (`SmoothedPolygons/Ch16/BasinHypotheses.lean`, each with its
TeX source and a certification plan).

Proof (the book's steps, module docstring): if some `F^n(q)`, `n ≥ 1`, is outside `𝒟₂₂`, then every
later iterate is (`l5st_mem_boxSet_22_of_poincareAngZero_mem`, the iterates being switching points,
`isSwitchingPointQ_poincareAngZero`), the orbit reaches `𝒟₀₀` (`l5st_exists_iterate_mem_boxSet_00`)
and converges to `q_out` (`l5st_tendsto_qOut0_of_mem_boxSet`); otherwise `F(q) = q_in`
(`l5st_eq_qIn0_of_forall_iterate_mem_boxSet_22`), so `q = q_in` (`poincareAngZero_eq_qIn0_iff`),
excluded.

Departures from the paper: see the module docstring (gaps G16.2, G16.3, G16.5, G15.6). -/
theorem theorem16_1_1 (h₁ : DOutContracts) (h₂ : CellTwoEntersDOut) (h₃ : BoxSubclaims)
    (q : XiW0Quot) (hq : q ≠ qIn0) :
    Tendsto (fun k : ℕ ↦ poincareAngZero^[k] q) atTop (𝓝 qOut0) := by
  by_cases hall : ∀ n, poincareAngZero^[n + 1] q ∈ boxSet 2 2
  · -- the orbit stays in `𝒟₂₂`: `F(q) = q_in`, so `q = q_in`
    exfalso
    apply hq
    refine (poincareAngZero_eq_qIn0_iff q).1 ?_
    refine l5st_eq_qIn0_of_forall_iterate_mem_boxSet_22 h₁ (isSwitchingPointQ_poincareAngZero q)
      fun n ↦ ?_
    rw [← Function.iterate_succ_apply]
    exact hall n
  push Not at hall
  obtain ⟨m, hm⟩ := hall
  -- once outside `𝒟₂₂` (after one step), the orbit never returns
  have hout : ∀ n, poincareAngZero^[n] (poincareAngZero^[m + 1] q) ∉ boxSet 2 2 := by
    intro n
    induction n with
    | zero => exact hm
    | succ n ih =>
      intro hmem
      apply ih
      rw [Function.iterate_succ_apply'] at hmem
      have hsw : IsSwitchingPointQ (poincareAngZero^[n] (poincareAngZero^[m + 1] q)) := by
        rw [← Function.iterate_add_apply, show n + (m + 1) = (n + m) + 1 by ring,
          Function.iterate_succ_apply']
        exact isSwitchingPointQ_poincareAngZero _
      exact l5st_mem_boxSet_22_of_poincareAngZero_mem h₁ hsw hmem
  -- it reaches `𝒟₀₀` and converges to `q_out` there
  obtain ⟨n, hn⟩ := l5st_exists_iterate_mem_boxSet_00 h₂ h₃ hout
  have ht := l5st_tendsto_qOut0_of_mem_boxSet h₁ hn
  rw [← tendsto_add_atTop_iff_nat (n + (m + 1))]
  refine ht.congr fun k ↦ ?_
  rw [Function.iterate_add_apply poincareAngZero k (n + (m + 1)),
    Function.iterate_add_apply poincareAngZero n (m + 1)]

end SmoothedPolygons
