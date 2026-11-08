module

public import SmoothedPolygons.Ch13.PoincareMap
public import SmoothedPolygons.Ch13.RScale

/-!
# Chapter 13: the fixed points `q_out` and `q_in` (verification)

The objects of Lemma 13.5.2 of Hales–Vajjha, *Packings of Smoothed Polygons* (`lem:qout`,
TeX 11298–11387), and the verification that they are what the lemma says; the classification
("exactly two fixed points") and the lemma itself are in
`SmoothedPolygons/Ch13/FixedPointsClassification.lean`.

* `equilExact r`: the right-hand side of equation `eqn:equil-exact` (13.5.1), as a function of `r`;
  `qOutCart = equilExact r_scale`, the representative of `q_out` normalized by `Re z₁ = -1` and
  `z₃ ∈ ℝ_{<0}`;
* `qOut`, `qIn`: the classes in `Ξ_𝒲/V_T` of the angular parts of `qOutCart` and `τ(qOutCart)`;
* the facts that the proof of Lemma 13.5.2 leaves out (inventory, gap 10): the first control of
  `qOutCart` is `ζ` (TeX 11384–11386), its first switching time is
  `t_sw = 2(1 + r + r²)/(√3(r + 1))` (TeX 11340–11344) — in particular `t_sw` is the *first*
  switching time, the control `ζ` staying optimal on `(0, t_sw)` (gap (b)) — the fixed-point
  equation (13.5.2) holds with `(r, ζ₁) = (r_scale, ζ²)`, and `H_F⁺ = 0` there (gap (c));
* the inward spiral: `F(τ qOutCart) = ζ² · (r_scale⁻¹ scaling)(τ qOutCart)` and `τ(q_out) = q_in`;
* Remark 13.5.4 (the fixed point `q_fix` for `(r, ζ₁) = (1, ζ)`).

All the numbers are certified, with no floating point: `r_scale` by sign changes of `P`
(`SmoothedPolygons/Ch13/RScale.lean`); the fixed-point equation (13.5.2) at (13.5.1) as six real
identities in `ℚ(√3)(r)` modulo `s² - 3` (`s = √3`) and `P(r)`, verified through the linear
system (13.5.2) coordinate by coordinate (the first two coordinates hold for every `r`, only the
third uses `P(r) = 0`), each with explicit cofactors (computed by reduction modulo the Gröbner basis
`{s² - 3, P(r)}`) checked by `field_simp; ring`; the signs of the switching functions on
`[0, t_sw]` from the signs of their coefficients and the root `t_sw`, which the fixed-point equation
supplies (no root isolation is needed); and `7.4 < t_sw < 7.41` from the fine enclosure of
`r_scale` and `1.732 < √3 < 1.7321`.

Along the outward spiral the two switching functions from the first control `ζ` are
`χ_{ζ→ζ²}(t) = t (0.22792… + 0.36253… t + 0.14434… t²)` (exactly `√3 t (y + bt/2 + t²/12)` with
`y = Im z₂⁰ > 0`, `b = Im z₁⁰ > 0`), positive on `(0, ∞)`, and
`χ_{ζ→1}(t) = 0.32444… + 0.97300… t + 0.93126… t² - 0.14434… t³` (up to the factor `√3`), with
one sign change of coefficients, hence (Descartes) one positive root, which is `t_sw` because
`z₃(t_sw) = ζ² r³ z₃⁰` lies on the wall `ℝ_{≤0}ζ²` between `1` and `ζ`. Explicitly, for a cubic
`f = a₀ + a₁t + a₂t² + a₃t³` with `a₀, a₁, a₂ ≥ 0` and `f(T) = 0`,
`T³ f(t) = a₀(T³ - t³) + a₁ t T (T² - t²) + a₂ t² T² (T - t)`, which is `≥ 0` on `[0, T]` and
`< 0` after `T` when `a₀ > 0`.
-/

@[expose] public section

namespace SmoothedPolygons

open Complex Set

namespace TriFuller

/-- The right-hand side of equation `eqn:equil-exact` (13.5.1) (TeX 11307–11328), as a function of
`r`:
`(-1 + i(-1 + r)/(√3(1 + r)), -(-1 + r³)/(√3(1 + r³)) + i(1 - 3r - 2r² - 3r³ + r⁴)/(3(1 + r + r³ +
r⁴)), -2(1 + r - 4r³ - 7r⁴ - 9r⁵ - 7r⁶ - 4r⁷ + r⁹ + r¹⁰)/(9(1 + r)²(1 - r + r²)(1 + r³ + r⁶)))`. -/
noncomputable def equilExact (r : ℝ) : Fin 3 → ℂ :=
  ![-1 + I * (((-1 + r) / (√3 * (1 + r)) : ℝ) : ℂ),
    ((-((-1 + r ^ 3) / (√3 * (1 + r ^ 3))) : ℝ) : ℂ) +
      I * (((1 - 3 * r - 2 * r ^ 2 - 3 * r ^ 3 + r ^ 4) / (3 * (1 + r + r ^ 3 + r ^ 4)) : ℝ) : ℂ),
    (((-2 * (1 + r - 4 * r ^ 3 - 7 * r ^ 4 - 9 * r ^ 5 - 7 * r ^ 6 - 4 * r ^ 7 + r ^ 9 + r ^ 10)) /
      (9 * (1 + r) ^ 2 * (1 - r + r ^ 2) * (1 + r ^ 3 + r ^ 6)) : ℝ) : ℂ)]

/-- The representative of `q_out` in Cartesian coordinates given by (13.5.1) with `r = r_scale`
(TeX 11303–11335): "after virial rescaling to make the real part of the first coordinate equal to
`-1`", and rotated by `V_T` to make the third coordinate real and negative. -/
noncomputable def qOutCart : Fin 3 → ℂ := equilExact rScale


/-! ### Explicit coordinates (private helpers)

The proofs below compute in real coordinates. With `s = √3`, `ζ = (-1 + s i)/2`,
`ζ² = (-1 - s i)/2`, and `qOutCart = (-1 + i b, x + i y, z)` with `b, x, y, z` the real
functions `l4g_qb`, `l4g_qx`, `l4g_qy`, `l4g_qz` of `r = r_scale` and `s`. The fixed-point
equation (13.5.2) at `t_sw = l4g_T r s` is the six real identities of `l4g_fixed_eqs`, which hold
in `ℚ(s)(r)` modulo `s² - 3` and `P(r)`: the first four are identities in `r` (modulo `s² = 3`),
and only the third coordinate uses `P(r) = 0`. Their cofactors were computed by reduction modulo
the Gröbner basis `{s² - 3, P(r)}`; Lean checks each identity with `field_simp; ring`. -/

/-- The flow (13.2.2) in real coordinates. -/
private lemma l4g_flow_mk (t a0 b0 a1 b1 a2 b2 ur ui : ℝ) :
    flow t ![⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩] ⟨ur, ui⟩ =
      ![⟨a0 + t * ui, b0 - t * ur⟩,
        ⟨a1 + a0 * t + t ^ 2 * ui / 2, b1 + b0 * t - t ^ 2 * ur / 2⟩,
        ⟨a2 + a1 * t + a0 * t ^ 2 / 2 + t ^ 3 * ui / 6,
          b2 + b1 * t + b0 * t ^ 2 / 2 - t ^ 3 * ur / 6⟩] := by
  ext j
  fin_cases j <;> apply Complex.ext <;>
    simp [flow, pow_succ, Complex.div_ofNat_re, Complex.div_ofNat_im] <;> ring

/-- The virial action in real coordinates. -/
private lemma l4g_smul_scale_mk (cr ci c a0 b0 a1 b1 a2 b2 : ℝ) :
    (⟨cr, ci⟩ : ℂ) • scale c ![⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩] =
      ![⟨c * (cr * a0 - ci * b0), c * (cr * b0 + ci * a0)⟩,
        ⟨c ^ 2 * (cr * a1 - ci * b1), c ^ 2 * (cr * b1 + ci * a1)⟩,
        ⟨c ^ 3 * (cr * a2 - ci * b2), c ^ 3 * (cr * b2 + ci * a2)⟩] := by
  ext j
  fin_cases j <;> apply Complex.ext <;> simp [scale, pow_succ] <;> ring

/-- The rotation by `V_T` in real coordinates. -/
private lemma l4g_smul_mk (cr ci a0 b0 a1 b1 a2 b2 : ℝ) :
    (⟨cr, ci⟩ : ℂ) • ![(⟨a0, b0⟩ : ℂ), ⟨a1, b1⟩, ⟨a2, b2⟩] =
      ![⟨cr * a0 - ci * b0, cr * b0 + ci * a0⟩, ⟨cr * a1 - ci * b1, cr * b1 + ci * a1⟩,
        ⟨cr * a2 - ci * b2, cr * b2 + ci * a2⟩] := by
  ext j
  fin_cases j <;> apply Complex.ext <;> simp

private lemma l4g_one_mk : (1 : ℂ) = ⟨1, 0⟩ := rfl

private lemma l4g_RR_mk (a b c d : ℝ) : RR ⟨a, b⟩ ⟨c, d⟩ = a * c + b * d := by
  simp [RR]

/-- Comparing two controls: only the term `RR(v, z₃)` of `H_F` depends on the control. -/
private lemma l4g_ham_le_iff (w : Fin 3 → ℂ) (u v : ℂ) :
    ham w v ≤ ham w u ↔ RR v (w 2) ≤ RR u (w 2) := by
  simp [ham]

private lemma l4g_ham_lt_iff (w : Fin 3 → ℂ) (u v : ℂ) :
    ham w u < ham w v ↔ RR u (w 2) < RR v (w 2) := by
  simp [ham]

/-- `τ(v · (c z₁, c² z₂, c³ z₃)) = v̄ · (c τ(z)₁, c² τ(z)₂, c³ τ(z)₃)` for real `c`. -/
private lemma l4g_tau_smul_scale (v : ℂ) (c : ℝ) (z : Fin 3 → ℂ) :
    tau (v • scale c z) = starRingEnd ℂ v • scale c (tau z) := by
  ext j
  fin_cases j <;> simp [tau, scale]

/-- Composition of virial actions. -/
private lemma l4g_smul_scale_smul_scale (v w : ℂ) (c d : ℝ) (z : Fin 3 → ℂ) :
    v • scale c (w • scale d z) = (v * w) • scale (c * d) z := by
  ext j
  fin_cases j <;> simp [scale] <;> ring

/-- A point whose first coordinate has nonzero real part is not `0`. -/
private lemma l4g_ne_zero_of_re {z : Fin 3 → ℂ} (h : (z 0).re ≠ 0) : z ≠ 0 :=
  fun hz ↦ h (by simp [hz])

/-- **The sign of a cubic below and above a positive root.** If
`f(t) = a₀ + a₁t + a₂t² + a₃t³` with `a₀, a₁, a₂ ≥ 0` vanishes at `T > 0`, then
`T³ f(t) = a₀(T³ - t³) + a₁ t T (T² - t²) + a₂ t² T² (T - t)`, so `f ≥ 0` on `[0, T]`. (This is
Descartes' rule of signs for the sign pattern `+ + + -`.) -/
private lemma l4g_cubic_nonneg {a0 a1 a2 a3 T t : ℝ} (h0 : 0 ≤ a0) (h1 : 0 ≤ a1) (h2 : 0 ≤ a2)
    (hT : 0 < T) (hroot : a0 + a1 * T + a2 * T ^ 2 + a3 * T ^ 3 = 0) (ht0 : 0 ≤ t)
    (htT : t ≤ T) : 0 ≤ a0 + a1 * t + a2 * t ^ 2 + a3 * t ^ 3 := by
  have key : T ^ 3 * (a0 + a1 * t + a2 * t ^ 2 + a3 * t ^ 3) =
      a0 * (T ^ 3 - t ^ 3) + a1 * t * T * (T ^ 2 - t ^ 2) + a2 * t ^ 2 * T ^ 2 * (T - t) := by
    linear_combination t ^ 3 * hroot
  have h3 : 0 ≤ T ^ 3 - t ^ 3 := sub_nonneg.2 (pow_le_pow_left₀ ht0 htT 3)
  have h2' : 0 ≤ T ^ 2 - t ^ 2 := sub_nonneg.2 (pow_le_pow_left₀ ht0 htT 2)
  have hrhs : 0 ≤ a0 * (T ^ 3 - t ^ 3) + a1 * t * T * (T ^ 2 - t ^ 2) +
      a2 * t ^ 2 * T ^ 2 * (T - t) :=
    add_nonneg (add_nonneg (mul_nonneg h0 h3) (mul_nonneg (mul_nonneg (mul_nonneg h1 ht0) hT.le)
      h2')) (mul_nonneg (by positivity) (sub_nonneg.2 htT))
  by_contra hneg
  have := mul_neg_of_pos_of_neg (pow_pos hT 3) (not_le.1 hneg)
  linarith

/-- The same cubic is negative after its root `T` (with `a₀ > 0`). -/
private lemma l4g_cubic_neg {a0 a1 a2 a3 T t : ℝ} (h0 : 0 < a0) (h1 : 0 ≤ a1) (h2 : 0 ≤ a2)
    (hT : 0 < T) (hroot : a0 + a1 * T + a2 * T ^ 2 + a3 * T ^ 3 = 0) (hTt : T < t) :
    a0 + a1 * t + a2 * t ^ 2 + a3 * t ^ 3 < 0 := by
  have ht0 : 0 < t := hT.trans hTt
  have key : T ^ 3 * (a0 + a1 * t + a2 * t ^ 2 + a3 * t ^ 3) =
      a0 * (T ^ 3 - t ^ 3) + a1 * t * T * (T ^ 2 - t ^ 2) + a2 * t ^ 2 * T ^ 2 * (T - t) := by
    linear_combination t ^ 3 * hroot
  have h3 : T ^ 3 - t ^ 3 < 0 := sub_neg.2 (pow_lt_pow_left₀ hTt hT.le (by norm_num))
  have h2' : T ^ 2 - t ^ 2 < 0 := sub_neg.2 (pow_lt_pow_left₀ hTt hT.le (by norm_num))
  have hrhs : a0 * (T ^ 3 - t ^ 3) + a1 * t * T * (T ^ 2 - t ^ 2) +
      a2 * t ^ 2 * T ^ 2 * (T - t) < 0 := by
    have e1 := mul_neg_of_pos_of_neg h0 h3
    have e2 : a1 * t * T * (T ^ 2 - t ^ 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) h2'.le
    have e3 : a2 * t ^ 2 * T ^ 2 * (T - t) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    linarith
  by_contra hnn
  have := mul_nonneg (pow_pos hT 3).le (not_lt.1 hnn)
  linarith

/-- The imaginary part of the first coordinate of (13.5.1). -/
private noncomputable def l4g_qb (r s : ℝ) : ℝ := (-1 + r) / (s * (1 + r))

/-- The real part of the second coordinate of (13.5.1). -/
private noncomputable def l4g_qx (r s : ℝ) : ℝ := -((-1 + r ^ 3) / (s * (1 + r ^ 3)))

/-- The imaginary part of the second coordinate of (13.5.1). -/
private noncomputable def l4g_qy (r : ℝ) : ℝ :=
  (1 - 3 * r - 2 * r ^ 2 - 3 * r ^ 3 + r ^ 4) / (3 * (1 + r + r ^ 3 + r ^ 4))

/-- The third coordinate of (13.5.1) (real). -/
private noncomputable def l4g_qz (r : ℝ) : ℝ :=
  -2 * (1 + r - 4 * r ^ 3 - 7 * r ^ 4 - 9 * r ^ 5 - 7 * r ^ 6 - 4 * r ^ 7 + r ^ 9 + r ^ 10) /
    (9 * (1 + r) ^ 2 * (1 - r + r ^ 2) * (1 + r ^ 3 + r ^ 6))

/-- The switching time `t_sw = 2(1 + r + r²)/(s(r + 1))` of Lemma 13.5.2. -/
private noncomputable def l4g_T (r s : ℝ) : ℝ := 2 * (1 + r + r ^ 2) / (s * (r + 1))

private lemma l4g_qb_pos {r s : ℝ} (hr : 1 < r) (hs : 0 < s) : 0 < l4g_qb r s :=
  div_pos (by linarith) (mul_pos hs (by linarith))

private lemma l4g_qx_neg {r s : ℝ} (hr : 1 < r) (hs : 0 < s) : l4g_qx r s < 0 := by
  have h3 : 1 < r ^ 3 := one_lt_pow₀ hr (by norm_num)
  exact neg_neg_of_pos (div_pos (by linarith) (mul_pos hs (by linarith)))

private lemma l4g_qy_pos {r : ℝ} (hr : 6 ≤ r) : 0 < l4g_qy r := by
  obtain ⟨e, he, rfl⟩ : ∃ e : ℝ, 0 ≤ e ∧ r = 6 + e := ⟨r - 6, by linarith, by ring⟩
  have hnum : 1 - 3 * (6 + e) - 2 * (6 + e) ^ 2 - 3 * (6 + e) ^ 3 + (6 + e) ^ 4 =
      e ^ 4 + 21 * e ^ 3 + 160 * e ^ 2 + 513 * e + 559 := by ring
  unfold l4g_qy
  rw [hnum]
  positivity

private lemma l4g_qz_neg {r : ℝ} (hr : 6 ≤ r) : l4g_qz r < 0 := by
  obtain ⟨e, he, rfl⟩ : ∃ e : ℝ, 0 ≤ e ∧ r = 6 + e := ⟨r - 6, by linarith, by ring⟩
  have hnum : 1 + (6 + e) - 4 * (6 + e) ^ 3 - 7 * (6 + e) ^ 4 - 9 * (6 + e) ^ 5 -
      7 * (6 + e) ^ 6 - 4 * (6 + e) ^ 7 + (6 + e) ^ 9 + (6 + e) ^ 10 =
      e ^ 10 + 61 * e ^ 9 + 1674 * e ^ 8 + 27212 * e ^ 7 + 290129 * e ^ 6 + 2119563 * e ^ 5 +
        10743239 * e ^ 4 + 37296332 * e ^ 3 + 84850128 * e ^ 2 + 114195745 * e + 69017623 := by
    ring
  unfold l4g_qz
  rw [hnum]
  apply div_neg_of_neg_of_pos
  · have : 0 < e ^ 10 + 61 * e ^ 9 + 1674 * e ^ 8 + 27212 * e ^ 7 + 290129 * e ^ 6 +
        2119563 * e ^ 5 + 10743239 * e ^ 4 + 37296332 * e ^ 3 + 84850128 * e ^ 2 +
        114195745 * e + 69017623 := by positivity
    linarith
  · have : 0 < 1 - (6 + e) + (6 + e) ^ 2 := by nlinarith
    positivity

private lemma l4g_T_pos {r s : ℝ} (hr : 1 < r) (hs : 0 < s) : 0 < l4g_T r s :=
  div_pos (by nlinarith) (mul_pos hs (by linarith))

/-- **The fixed-point equation (13.5.2) at (13.5.1), in real coordinates**: the real and
imaginary parts of `z_j(t_sw, q, ζ) = ζ² r^j q_j` (`j = 1, 2, 3`), as identities in
`ℚ(s)(r)` modulo `s² = 3` and `P(r) = 0`. -/
private lemma l4g_fixed_eqs {r s : ℝ} (hr : 1 < r) (hs0 : 0 < s) (hs : s ^ 2 = 3)
    (hP : 1 - 5 * r - 7 * r ^ 2 - 5 * r ^ 3 - 7 * r ^ 4 - 5 * r ^ 5 + r ^ 6 = 0) :
    -1 + l4g_T r s * (s / 2) = r * (-1 / 2 * -1 - -(s / 2) * l4g_qb r s) ∧
    l4g_qb r s - l4g_T r s * (-1 / 2) = r * (-1 / 2 * l4g_qb r s + -(s / 2) * -1) ∧
    l4g_qx r s + -1 * l4g_T r s + l4g_T r s ^ 2 * (s / 2) / 2 =
      r ^ 2 * (-1 / 2 * l4g_qx r s - -(s / 2) * l4g_qy r) ∧
    l4g_qy r + l4g_qb r s * l4g_T r s - l4g_T r s ^ 2 * (-1 / 2) / 2 =
      r ^ 2 * (-1 / 2 * l4g_qy r + -(s / 2) * l4g_qx r s) ∧
    l4g_qz r + l4g_qx r s * l4g_T r s + -1 * l4g_T r s ^ 2 / 2 + l4g_T r s ^ 3 * (s / 2) / 6 =
      r ^ 3 * (-1 / 2 * l4g_qz r - -(s / 2) * 0) ∧
    0 + l4g_qy r * l4g_T r s + l4g_qb r s * l4g_T r s ^ 2 / 2 - l4g_T r s ^ 3 * (-1 / 2) / 6 =
      r ^ 3 * (-1 / 2 * 0 + -(s / 2) * l4g_qz r) := by
  have hr0 : 0 < r := by linarith
  have hs' : s ≠ 0 := hs0.ne'
  have h1 : 1 + r ≠ 0 := by positivity
  have h1' : r + 1 ≠ 0 := by positivity
  have h3 : 1 + r ^ 3 ≠ 0 := by positivity
  have h4 : 1 + r + r ^ 3 + r ^ 4 ≠ 0 := by positivity
  have h5 : 1 - r + r ^ 2 ≠ 0 := by nlinarith
  have h5' : r ^ 2 - r + 1 ≠ 0 := by nlinarith
  have h6 : 1 + r ^ 3 + r ^ 6 ≠ 0 := by positivity
  have h6' : r ^ 6 + r ^ 3 + 1 ≠ 0 := by positivity
  unfold l4g_qb l4g_qx l4g_qy l4g_qz l4g_T
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [← sub_eq_zero]
  · field_simp
    ring
  · calc _ = (-r) * (s ^ 2 - 3) / (2 * s) := by field_simp; ring
      _ = 0 := by rw [hs]; ring
  · calc _ = (-r ^ 2 * (r ^ 2 - 4 * r + 1) * (r ^ 2 + r + 1)) * (s ^ 2 - 3) /
          (6 * s * (r + 1) ^ 2 * (r ^ 2 - r + 1)) := by field_simp; ring
      _ = 0 := by rw [hs]; ring
  · calc _ = (-(r ^ 2 + r + 1) * (r ^ 2 + 3 * r - 1)) * (s ^ 2 - 3) /
          (3 * s ^ 2 * (r + 1) ^ 2) := by field_simp; ring
      _ = 0 := by rw [hs]; ring
  · calc _ = ((-(r + 1) * (r ^ 3 + 2) * (r ^ 2 + r + 1) ^ 2 *
          (r ^ 6 - r ^ 5 - r ^ 4 - r ^ 3 - r ^ 2 - r + 1)) * (s ^ 2 - 3) +
          (3 * r ^ 3 * (r - 1) * (r ^ 2 + r + 1) ^ 2) *
            (1 - 5 * r - 7 * r ^ 2 - 5 * r ^ 3 - 7 * r ^ 4 - 5 * r ^ 5 + r ^ 6)) /
          (9 * s ^ 2 * (r + 1) ^ 3 * (r ^ 2 - r + 1) * (r ^ 6 + r ^ 3 + 1)) := by
          field_simp; ring
      _ = 0 := by rw [hP, hs]; ring
  · calc _ = ((-(r ^ 2 + r + 1) ^ 2 * (r ^ 10 * s ^ 2 + 3 * r ^ 10 - 2 * r ^ 8 * s ^ 2 -
          12 * r ^ 8 - 2 * r ^ 7 * s ^ 2 + 18 * r ^ 7 - 2 * r ^ 6 * s ^ 2 - 12 * r ^ 6 -
          2 * r ^ 5 * s ^ 2 - 12 * r ^ 5 + 24 * r ^ 4 + r ^ 3 * s ^ 2 - 3 * r ^ 3 - 6 * r ^ 2 +
          24 * r - 6)) * (s ^ 2 - 3) +
          (-3 * (r - 1) * (r ^ 3 + 2) * (r ^ 2 + r + 1) ^ 2) *
            (1 - 5 * r - 7 * r ^ 2 - 5 * r ^ 3 - 7 * r ^ 4 - 5 * r ^ 5 + r ^ 6)) /
          (9 * s ^ 3 * (r + 1) ^ 3 * (r ^ 2 - r + 1) * (r ^ 6 + r ^ 3 + 1)) := by
          field_simp; ring
      _ = 0 := by rw [hP, hs]; ring

/-- **`H_F = 0` along (13.5.1) at the roots of `P`**: `H_F(q, ζ) = y + b x - z/2` vanishes in
`ℚ(s)(r)` modulo `s² = 3` and `P(r) = 0`. -/
private lemma l4g_ham_eq {r s : ℝ} (hr : 1 < r) (hs0 : 0 < s) (hs : s ^ 2 = 3)
    (hP : 1 - 5 * r - 7 * r ^ 2 - 5 * r ^ 3 - 7 * r ^ 4 - 5 * r ^ 5 + r ^ 6 = 0) :
    l4g_qy r + l4g_qb r s * l4g_qx r s - l4g_qz r / 2 = 0 := by
  have hr0 : 0 < r := by linarith
  have hs' : s ≠ 0 := hs0.ne'
  have h1 : 1 + r ≠ 0 := by positivity
  have h3 : 1 + r ^ 3 ≠ 0 := by positivity
  have h4 : 1 + r + r ^ 3 + r ^ 4 ≠ 0 := by positivity
  have h5 : 1 - r + r ^ 2 ≠ 0 := by nlinarith
  have h5' : r ^ 2 - r + 1 ≠ 0 := by nlinarith
  have h6 : 1 + r ^ 3 + r ^ 6 ≠ 0 := by positivity
  have h6' : r ^ 6 + r ^ 3 + 1 ≠ 0 := by positivity
  unfold l4g_qb l4g_qx l4g_qy l4g_qz
  calc _ = (((r ^ 2 + r + 1) * (4 * r ^ 8 - 12 * r ^ 7 + 2 * r ^ 6 - 15 * r ^ 4 + 2 * r ^ 2 -
        12 * r + 4)) * (s ^ 2 - 3) + (3 * (r ^ 2 - r + 1) * (r ^ 2 + r + 1)) *
          (1 - 5 * r - 7 * r ^ 2 - 5 * r ^ 3 - 7 * r ^ 4 - 5 * r ^ 5 + r ^ 6)) /
        (9 * s ^ 2 * (r + 1) ^ 2 * (r ^ 2 - r + 1) * (r ^ 6 + r ^ 3 + 1)) := by
        field_simp; ring
    _ = 0 := by rw [hP, hs]; ring

/-- `r_scale > 6` and the facts `s = √3 > 0`, `s² = 3`, `P(r_scale) = 0` in the form used here. -/
private lemma l4g_rs_facts :
    6 < rScale ∧ 0 < √3 ∧ √3 ^ 2 = 3 ∧
      1 - 5 * rScale - 7 * rScale ^ 2 - 5 * rScale ^ 3 - 7 * rScale ^ 4 - 5 * rScale ^ 5 +
        rScale ^ 6 = 0 :=
  ⟨by linarith [rScale_bounds.1], by positivity, Real.sq_sqrt (by norm_num),
    rScale_spec.2⟩

/-- `qOutCart` in real coordinates. -/
private lemma l4g_qOutCart_mk :
    qOutCart =
      ![⟨-1, l4g_qb rScale √3⟩, ⟨l4g_qx rScale √3, l4g_qy rScale⟩, ⟨l4g_qz rScale, 0⟩] := by
  refine congrArg₂ Matrix.vecCons ?_ (congrArg₂ Matrix.vecCons ?_
    (congrArg₂ Matrix.vecCons ?_ rfl)) <;> apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im,
      Complex.one_re, Complex.one_im, l4g_qb, l4g_qx, l4g_qy, l4g_qz] <;> ring

/-- `q_out ≠ 0`. -/
theorem qOutCart_ne_zero : qOutCart ≠ 0 :=
  l4g_ne_zero_of_re (by rw [l4g_qOutCart_mk]; norm_num)

/-- `τ(q_out) ≠ 0`. -/
theorem tau_qOutCart_ne_zero : tau qOutCart ≠ 0 :=
  l4g_ne_zero_of_re (by rw [l4g_qOutCart_mk]; simp [tau])

/-- **The fixed-point equation (13.5.2) at `q_out`** along the constant control `ζ`. -/
private lemma l4g_flow_T :
    flow (l4g_T rScale √3) qOutCart ζ = ζ ^ 2 • scale rScale qOutCart := by
  obtain ⟨hr6, hs0, hs, hP⟩ := l4g_rs_facts
  obtain ⟨E0, E1, E2, E3, E4, E5⟩ := l4g_fixed_eqs (by linarith) hs0 hs hP
  rw [ζ_sq_eq_mk, l4g_qOutCart_mk, ζ_eq_mk, l4g_flow_mk, l4g_smul_scale_mk]
  refine congrArg₂ Matrix.vecCons (congrArg₂ Complex.mk ?_ ?_)
    (congrArg₂ Matrix.vecCons (congrArg₂ Complex.mk ?_ ?_)
      (congrArg₂ Matrix.vecCons (congrArg₂ Complex.mk ?_ ?_) rfl))
  · linear_combination E0
  · linear_combination E1
  · linear_combination E2
  · linear_combination E3
  · linear_combination E4
  · linear_combination E5

/-- The third coordinate along the control `ζ` from `qOutCart`, in real coordinates. -/
private lemma l4g_flow_two (t : ℝ) :
    flow t qOutCart ζ 2 =
      ⟨l4g_qz rScale + l4g_qx rScale √3 * t + -1 * t ^ 2 / 2 + t ^ 3 * (√3 / 2) / 6,
        0 + l4g_qy rScale * t + l4g_qb rScale √3 * t ^ 2 / 2 - t ^ 3 * (-1 / 2) / 6⟩ := by
  rw [l4g_qOutCart_mk, ζ_eq_mk, l4g_flow_mk]
  rfl

/-- The two switching functions from `ζ` along `t ↦ z(t, qOutCart, ζ)`: to `1`, a cubic
`a₀ + a₁t + a₂t² + a₃t³` with `a₀, a₁, a₂ > 0` (signs `+ + + -`), and to `ζ²`,
`√3 t (y + bt/2 + t²/12)` (TeX's `t(0.22792 + 0.36253t + 0.14434t²)` up to the factor `√3`). -/
private lemma l4g_switching (t : ℝ) :
    RR ζ (flow t qOutCart ζ 2) - RR 1 (flow t qOutCart ζ 2) =
      -3 / 2 * l4g_qz rScale + (-3 / 2 * l4g_qx rScale √3 + √3 / 2 * l4g_qy rScale) * t +
        (3 / 4 + √3 / 4 * l4g_qb rScale √3) * t ^ 2 + -(√3 / 12) * t ^ 3 ∧
    RR ζ (flow t qOutCart ζ 2) - RR (ζ ^ 2) (flow t qOutCart ζ 2) =
      √3 * t * (l4g_qy rScale + l4g_qb rScale √3 * t / 2 + t ^ 2 / 12) := by
  rw [l4g_flow_two, ζ_sq_eq_mk, ζ_eq_mk, l4g_one_mk, l4g_RR_mk, l4g_RR_mk, l4g_RR_mk]
  constructor <;> ring

/-- The coefficients of the switching function from `ζ` to `1` are positive, and it vanishes
at `t_sw` (from the fixed-point equation: `z₃(t_sw) = ζ² r³ z₃⁰` lies on the wall `ℝ_{≤0}ζ²`
between `1` and `ζ`). -/
private lemma l4g_switching_coeffs :
    0 < -3 / 2 * l4g_qz rScale ∧ 0 < -3 / 2 * l4g_qx rScale √3 + √3 / 2 * l4g_qy rScale ∧
      0 < 3 / 4 + √3 / 4 * l4g_qb rScale √3 ∧
      -3 / 2 * l4g_qz rScale + (-3 / 2 * l4g_qx rScale √3 + √3 / 2 * l4g_qy rScale) *
        l4g_T rScale √3 + (3 / 4 + √3 / 4 * l4g_qb rScale √3) * l4g_T rScale √3 ^ 2 +
        -(√3 / 12) * l4g_T rScale √3 ^ 3 = 0 := by
  obtain ⟨hr6, hs0, hs, hP⟩ := l4g_rs_facts
  obtain ⟨-, -, -, -, E4, E5⟩ := l4g_fixed_eqs (by linarith) hs0 hs hP
  have hz := l4g_qz_neg hr6.le
  have hx := l4g_qx_neg (r := rScale) (by linarith) hs0
  have hy := l4g_qy_pos hr6.le
  have hb := l4g_qb_pos (r := rScale) (by linarith) hs0
  refine ⟨by linarith, by nlinarith, by nlinarith, ?_⟩
  linear_combination (-3 / 2) * E4 + (√3 / 2) * E5 - (rScale ^ 3 * l4g_qz rScale / 4) * hs

/-- **`ζ` is optimal on `[0, t_sw]`** along its own trajectory from `qOutCart`. -/
private lemma l4g_max {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ l4g_T rScale √3) :
    ∀ v ∈ VT, ham (flow t qOutCart ζ) v ≤ ham (flow t qOutCart ζ) ζ := by
  obtain ⟨hr6, hs0, -, -⟩ := l4g_rs_facts
  obtain ⟨c0, c1, c2, hroot⟩ := l4g_switching_coeffs
  obtain ⟨h1, h2⟩ := l4g_switching t
  intro v hv
  rw [l4g_ham_le_iff]
  rcases mem_VT.1 hv with rfl | rfl | rfl
  · have := l4g_cubic_nonneg c0.le c1.le c2.le (l4g_T_pos (by linarith) hs0) hroot ht0 htT
    linarith
  · exact le_rfl
  · have : 0 ≤ √3 * t * (l4g_qy rScale + l4g_qb rScale √3 * t / 2 + t ^ 2 / 12) := by
      have := l4g_qy_pos hr6.le
      have := l4g_qb_pos (by linarith : 1 < rScale) hs0
      positivity
    linarith

/-- **`ζ` is beaten by `1` after `t_sw`**. -/
private lemma l4g_beaten {t : ℝ} (ht : l4g_T rScale √3 < t) :
    ham (flow t qOutCart ζ) ζ < ham (flow t qOutCart ζ) 1 := by
  obtain ⟨hr6, hs0, -, -⟩ := l4g_rs_facts
  obtain ⟨c0, c1, c2, hroot⟩ := l4g_switching_coeffs
  have := l4g_cubic_neg c0 c1.le c2.le (l4g_T_pos (by linarith) hs0) hroot ht
  rw [l4g_ham_lt_iff]
  linarith [(l4g_switching t).1]

/-- `ζ²` beats `ζ` at small negative times along `t ↦ z(t, qOutCart, ζ)`: `ζ` is not the most
recent control of `qOutCart` (which is a genuine switching point; its most recent control is
`ζ²`). -/
private lemma l4g_not_mostRecent : ¬ IsMostRecentControl qOutCart ζ := by
  obtain ⟨hr6, hs0, -, -⟩ := l4g_rs_facts
  have hy := l4g_qy_pos hr6.le
  have hb := l4g_qb_pos (by linarith : 1 < rScale) hs0
  rintro ⟨-, ε, hε, h⟩
  set m := min ε (l4g_qy rScale / l4g_qb rScale √3) with hm_def
  have hm : 0 < m := lt_min hε (div_pos hy hb)
  have hm1 : m ≤ ε := min_le_left _ _
  have hbm : l4g_qb rScale √3 * m ≤ l4g_qy rScale := by
    have := min_le_right ε (l4g_qy rScale / l4g_qb rScale √3)
    rw [← hm_def, le_div_iff₀ hb] at this
    linarith
  have hle := h (-m) ⟨by linarith, by linarith⟩ (ζ ^ 2) ζ_sq_mem_VT
  rw [l4g_ham_le_iff] at hle
  have hg := (l4g_switching (-m)).2
  have hin : 0 < l4g_qy rScale + l4g_qb rScale √3 * -m / 2 + (-m) ^ 2 / 12 := by nlinarith
  have : √3 * -m * (l4g_qy rScale + l4g_qb rScale √3 * -m / 2 + (-m) ^ 2 / 12) < 0 :=
    mul_neg_of_neg_of_pos (by nlinarith) hin
  linarith

/-- The angular parts of `qOutCart` and `τ(qOutCart)` lie in `Ξ_𝒲` (their third coordinates are
real and negative). -/
theorem ang_qOutCart_mem_XiW : ang qOutCart ∈ XiW ∧ ang (tau qOutCart) ∈ XiW := by
  have hz := l4g_qz_neg (by linarith [rScale_bounds.1] : (6 : ℝ) ≤ rScale)
  have key : ∀ z : Fin 3 → ℂ, z ≠ 0 → z 2 = (l4g_qz rScale : ℂ) → ang z ∈ XiW := by
    intro z hz0 h2
    change ang z ∈ Xi ∧ ang z 2 ∈ walls
    refine ⟨ang_mem_Xi hz0, Set.mem_union_left _ (Set.mem_union_left _ ?_)⟩
    refine ⟨(weightedNorm z)⁻¹ ^ 3 * l4g_qz rScale,
      mul_nonpos_of_nonneg_of_nonpos
        (pow_nonneg (inv_nonneg.2 (weightedNorm_pos hz0).le) 3) hz.le, ?_⟩
    simp [ang, scale, h2]
  refine ⟨key _ qOutCart_ne_zero ?_, key _ tau_qOutCart_ne_zero ?_⟩
  · rw [l4g_qOutCart_mk]
    rfl
  · rw [l4g_qOutCart_mk]
    apply Complex.ext <;> simp [tau]

/-- The fixed point `q_out ∈ Ξ_𝒲/V_T` (Lemma 13.5.2): the switching point of the outward
triangular spiral. -/
noncomputable def qOut : XiWQuot := Quotient.mk'' ⟨ang qOutCart, ang_qOutCart_mem_XiW.1⟩

/-- The fixed point `q_in ∈ Ξ_𝒲/V_T` (Lemma 13.5.2): the switching point of the inward triangular
spiral, represented by `τ(qOutCart)`. -/
noncomputable def qIn : XiWQuot := Quotient.mk'' ⟨ang (tau qOutCart), ang_qOutCart_mem_XiW.2⟩

/-- The normalization of (13.5.1): `Re z₁ = -1`, and `z₃` is real and negative. -/
theorem qOutCart_normalization :
    (qOutCart 0).re = -1 ∧ (qOutCart 2).im = 0 ∧ (qOutCart 2).re < 0 := by
  rw [l4g_qOutCart_mk]
  exact ⟨rfl, rfl, l4g_qz_neg (by linarith [rScale_bounds.1])⟩

/-- The first control of `qOutCart` is `ζ = ζ₁²` (TeX 11384–11386; the tie between `ζ` and `ζ²` on
the wall `𝒲₀` is broken by `Im z₂ > 0`). Proof: the constant control `ζ` is optimal along its own
trajectory on `[0, t_sw]` (the switching functions of `firstSwitchTime_qOutCart`; the one to
`ζ²` is `√3 t (Im z₂⁰ + Im z₁⁰ t/2 + t²/12) ≥ 0`, which is where `Im z₂⁰ > 0` enters), and the
first control is unique (`firstControl_eq_iff`). -/
private theorem l4st_firstControl_qOutCart : firstControl qOutCart = ζ := by
  obtain ⟨hr6, hs0, -, -⟩ := l4g_rs_facts
  exact (firstControl_eq_iff qOutCart_ne_zero).2
    ⟨ζ_mem_VT, l4g_T rScale √3, l4g_T_pos (by linarith) hs0,
      fun t ht v hv ↦ l4g_max ht.1 ht.2 v hv⟩

/-- **The first switching time of (13.5.1)** (TeX 11340–11344, and inventory gap 10(b)):
`t_sw = 2(1 + r + r²)/(√3(r + 1))` with `r = r_scale`, and it is the *first* switching time: along
`t ↦ z(t, qOutCart, ζ)` the switching function from `ζ` to `ζ²` is nonnegative on `[0, t_sw]`
(it vanishes at `0` because `z₃` is real), the switching function from `ζ` to `1` is positive on
`[0, t_sw)` and changes sign at its simple root `t_sw`.

Proof: both switching functions are cubics in `t` with coefficients in `ℚ(√3, r_scale)`. The one
to `ζ²` is `√3 t (Im z₂⁰ + Im z₁⁰ t/2 + t²/12)`, with positive coefficients. The one to `1` has the
sign pattern `+ + + -` (`Re z₂⁰ < 0 < Im z₂⁰`, `z₃⁰ < 0`, `Im z₁⁰ > 0`) and vanishes at
`t_sw` by the fixed-point equation (`z₃(t_sw) = ζ² r³ z₃⁰`, and `RR(ζ - 1, ζ²) = 0`); so it is
`≥ 0` on `[0, t_sw]` and `< 0` after `t_sw` (see the module docstring). Hence `ζ` is optimal
exactly up to `t_sw`, and the set of times at which `ζ` is beaten is `(t_sw, ∞)`. -/
theorem firstSwitchTime_qOutCart :
    firstSwitchTime qOutCart = 2 * (1 + rScale + rScale ^ 2) / (√3 * (rScale + 1)) := by
  obtain ⟨hr6, hs0, -, -⟩ := l4g_rs_facts
  rw [firstSwitchTime, l4st_firstControl_qOutCart]
  have hset : {t : ℝ | 0 < t ∧ ∃ v ∈ VT,
      ham (flow t qOutCart ζ) ζ < ham (flow t qOutCart ζ) v} = Ioi (l4g_T rScale √3) := by
    ext t
    constructor
    · rintro ⟨ht0, v, hv, hlt⟩
      by_contra hle
      exact absurd (l4g_max ht0.le (not_lt.1 hle) v hv) (not_le.2 hlt)
    · intro ht
      exact ⟨(l4g_T_pos (by linarith) hs0).trans ht, 1, one_mem_VT, l4g_beaten ht⟩
  rw [hset, csInf_Ioi]
  rfl

/-- **The fixed-point equation (13.5.2) at `q_out`** (TeX 11348–11358): `F(qOutCart) =
ζ² · (r z₁, r² z₂, r³ z₃)` with `r = r_scale`, the outward triangular spiral (`r_scale > 1`).
Proof: with `t_sw` from `firstSwitchTime_qOutCart`, both sides are explicit elements
of `ℚ(√3)(r)`; the six real coordinates of the linear system (13.5.2) agree modulo `s² - 3` and
`P(r)` (`l4g_fixed_eqs`). -/
theorem poincare_qOutCart : poincare qOutCart = ζ ^ 2 • scale rScale qOutCart := by
  rw [poincare, firstSwitchTime_qOutCart, l4st_firstControl_qOutCart]
  exact l4g_flow_T

/-- **The Hamiltonian vanishes at `q_out`** (inventory, gap 10(c): the statement of Lemma 13.5.2
asserts it, the proof does not show it). Along (13.5.1) as a function of `r`, `z₃` is real, so
the controls `ζ` and `ζ²` tie and `H_F(z, ζ) = H_F(z, ζ²) = (r² + r + 1) P(r) /
(9 (r + 1)² (1 + r³ + r⁶))`, which vanishes exactly at the roots of `P`; and
`H_F(z, 1) = H_F(z, ζ) + (3/2) z₃ < 0`. -/
theorem hamMax_qOutCart : hamMax qOutCart = 0 := by
  obtain ⟨hr6, hs0, hs, hP⟩ := l4g_rs_facts
  have hH := l4g_ham_eq (by linarith) hs0 hs hP
  have hz := l4g_qz_neg hr6.le
  have hv : ∀ v : ℂ, ham qOutCart v =
      l4g_qy rScale + l4g_qb rScale √3 * l4g_qx rScale √3 + RR v ⟨l4g_qz rScale, 0⟩ := by
    intro v
    have hI : (⟨l4g_qx rScale √3, l4g_qy rScale⟩ : ℂ) * I =
        ⟨-l4g_qy rScale, l4g_qx rScale √3⟩ := by
      apply Complex.ext <;> simp
    rw [ham, l4g_qOutCart_mk]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rw [hI, l4g_RR_mk]
    ring
  rw [hamMax, hv, hv, hv, ζ_sq_eq_mk, ζ_eq_mk, l4g_one_mk, l4g_RR_mk, l4g_RR_mk, l4g_RR_mk]
  have e2 : l4g_qy rScale + l4g_qb rScale √3 * l4g_qx rScale √3 +
      (-1 / 2 * l4g_qz rScale + √3 / 2 * 0) = 0 := by linear_combination hH
  have e3 : l4g_qy rScale + l4g_qb rScale √3 * l4g_qx rScale √3 +
      (-1 / 2 * l4g_qz rScale + -(√3 / 2) * 0) = 0 := by linear_combination hH
  rw [e2, e3, max_self]
  exact max_eq_right (by linarith)

/-- **The inward spiral** (TeX 11381–11383): `F(τ qOutCart) = ζ² · (r⁻¹ z₁, r⁻² z₂, r⁻³ z₃)` with
`r = r_scale`. Proof route: `qOutCart` is a genuine switching point (its most recent control is
`ζ²`, the conjugate of the first control `ζ` of `τ(qOutCart)`, Lemma 13.2.5), so
`F(τ F(qOutCart)) = τ(qOutCart)` (`poincare_tau_poincare`); with
`τ F(qOutCart) = ζ · (r_s-scaling)(τ qOutCart)` and the equivariance of `F`
(`poincare_smul`, `poincare_scale`). -/
theorem poincare_tau_qOutCart :
    poincare (tau qOutCart) = ζ ^ 2 • scale rScale⁻¹ (tau qOutCart) := by
  have hr : 0 < rScale := by linarith [rScale_spec.1]
  have hτ := tau_qOutCart_ne_zero
  have hsτ : scale rScale (tau qOutCart) ≠ 0 :=
    l4g_ne_zero_of_re (by
      rw [l4g_qOutCart_mk]
      simpa [scale, tau] using hr.ne')
  have h1 := poincare_tau_poincare qOutCart_ne_zero
    (by rw [l4st_firstControl_qOutCart]; exact l4g_not_mostRecent)
  rw [poincare_qOutCart, l4g_tau_smul_scale, conj_ζ_sq,
    (poincare_smul ζ_mem_VT hsτ).2.2, (poincare_scale hr hτ).2.2] at h1
  calc poincare (tau qOutCart)
      = ζ ^ 2 • scale rScale⁻¹ (ζ • scale rScale (poincare (tau qOutCart))) := by
        rw [l4g_smul_scale_smul_scale, ← pow_succ, ζ_pow_three, inv_mul_cancel₀ hr.ne',
          one_smul, scale_one]
    _ = ζ ^ 2 • scale rScale⁻¹ (tau qOutCart) := by rw [h1]

/-- `τ(q_out) = q_in` in `Ξ_𝒲/V_T` (TeX 11302–11303). -/
theorem tauQuot_qOut : tauQuot qOut = qIn := by
  unfold tauQuot qOut qIn
  rw [Quotient.map'_mk'']
  congr 1
  exact Subtype.ext (tau_ang qOutCart)

/-- `q_out` and `q_in` lie in `Ξ_{𝒲,0}/V_T`: the Hamiltonian vanishes there
(`hamMax_qOutCart`, scaling and `H_F⁺(τ z) = H_F⁺(z)`). -/
theorem hamMaxQuot_qOut_qIn : hamMaxQuot qOut = 0 ∧ hamMaxQuot qIn = 0 := by
  have hang : ∀ z : Fin 3 → ℂ, z ≠ 0 → hamMax (ang z) = (weightedNorm z)⁻¹ ^ 3 * hamMax z := by
    intro z hz
    have := (hamMax_smul_scale_and_tau one_mem_VT (inv_pos.2 (weightedNorm_pos hz)) z).1
    rwa [one_smul] at this
  constructor
  · change hamMax (ang qOutCart) = 0
    rw [hang _ qOutCart_ne_zero, hamMax_qOutCart, mul_zero]
  · change hamMax (ang (tau qOutCart)) = 0
    rw [hang _ tau_qOutCart_ne_zero, (hamMax_smul_scale_and_tau one_mem_VT one_pos qOutCart).2,
      hamMax_qOutCart, mul_zero]

/-- `q_out` as a point of `Ξ_{𝒲,0}/V_T`. -/
noncomputable def qOut0 : XiW0Quot := ⟨qOut, hamMaxQuot_qOut_qIn.1⟩

/-- `q_in` as a point of `Ξ_{𝒲,0}/V_T`. -/
noncomputable def qIn0 : XiW0Quot := ⟨qIn, hamMaxQuot_qOut_qIn.2⟩

/-- `7.4 < t_sw < 7.41` for (13.5.1) (the book's `t_sw ≈ 7.4`, TeX 11344). The coarse enclosure
`6.27 < r_scale < 6.28` does not suffice (`t_sw(6.27) ≈ 7.3988`, `t_sw(6.28) ≈ 7.4101`); the proof
uses `rScale_fine_bounds` and `1.732 < √3 < 1.7321`. -/
theorem firstSwitchTime_qOutCart_bounds :
    7.4 < firstSwitchTime qOutCart ∧ firstSwitchTime qOutCart < 7.41 := by
  obtain ⟨hlo, hhi⟩ := rScale_fine_bounds
  have hs1 : √3 < 1.7321 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hs2 : 1.732 < √3 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hden : 0 < √3 * (rScale + 1) := by positivity
  rw [firstSwitchTime_qOutCart, lt_div_iff₀ hden, div_lt_iff₀ hden]
  constructor
  · have : √3 * (rScale + 1) < 1.7321 * (rScale + 1) :=
      mul_lt_mul_of_pos_right hs1 (by linarith)
    nlinarith
  · have : 1.732 * (rScale + 1) < √3 * (rScale + 1) :=
      mul_lt_mul_of_pos_right hs2 (by linarith)
    nlinarith

/-- The fixed point `q_fix = (1, -i/2, -1/2)` of Remark 13.5.4 (TeX 11402–11406). -/
noncomputable def qFix : Fin 3 → ℂ := ![1, -I / 2, -1 / 2]

/-- `q_fix` in real coordinates. -/
private lemma l4g_qFix_mk : qFix = ![⟨1, 0⟩, ⟨0, -1 / 2⟩, ⟨-1 / 2, 0⟩] := by
  ext j
  fin_cases j <;> apply Complex.ext <;> simp [qFix]

/-- The switching functions from `ζ²` along `t ↦ z(t, q_fix, ζ²)`: to `1`,
`(√3/12)(t - √3)(t² - 2√3 t - 3)`, and to `ζ`, `√3 t (6 - t²)/12`. -/
private lemma l4g_qFix_switching (t : ℝ) :
    RR (ζ ^ 2) (flow t qFix (ζ ^ 2) 2) - RR 1 (flow t qFix (ζ ^ 2) 2) =
      √3 / 12 * (t - √3) * (t ^ 2 - 2 * √3 * t - 3) ∧
    RR (ζ ^ 2) (flow t qFix (ζ ^ 2) 2) - RR ζ (flow t qFix (ζ ^ 2) 2) =
      √3 * t * (6 - t ^ 2) / 12 := by
  have hs : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [l4g_qFix_mk, ζ_sq_eq_mk, l4g_flow_mk, ζ_eq_mk, l4g_one_mk]
  simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  rw [l4g_RR_mk, l4g_RR_mk, l4g_RR_mk]
  constructor
  · linear_combination (-1 / 4 - √3 * t / 6 + t ^ 2 / 4) * hs
  · ring

/-- `ζ²` is optimal on `[0, √3]` along its own trajectory from `q_fix`. -/
private lemma l4g_qFix_max {t : ℝ} (ht0 : 0 ≤ t) (hts : t ≤ √3) :
    ∀ v ∈ VT, ham (flow t qFix (ζ ^ 2)) v ≤ ham (flow t qFix (ζ ^ 2)) (ζ ^ 2) := by
  have hs : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < √3 := by positivity
  obtain ⟨h1, h2⟩ := l4g_qFix_switching t
  intro v hv
  rw [l4g_ham_le_iff]
  rcases mem_VT.1 hv with rfl | rfl | rfl
  · have hq : t ^ 2 - 2 * √3 * t - 3 < 0 := by nlinarith
    have : 0 ≤ √3 / 12 * (t - √3) * (t ^ 2 - 2 * √3 * t - 3) :=
      mul_nonneg_of_nonpos_of_nonpos
        (mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)) hq.le
    linarith
  · have : 0 ≤ √3 * t * (6 - t ^ 2) / 12 := by
      have : t ^ 2 ≤ 3 := by nlinarith
      have : 0 ≤ 6 - t ^ 2 := by linarith
      positivity
    linarith
  · exact le_rfl

/-- `ζ²` is beaten by `1` on `(√3, √3 + 1)` along its trajectory from `q_fix`. -/
private lemma l4g_qFix_beaten {t : ℝ} (ht1 : √3 < t) (ht2 : t < √3 + 1) :
    ham (flow t qFix (ζ ^ 2)) (ζ ^ 2) < ham (flow t qFix (ζ ^ 2)) 1 := by
  have hs : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs1 : 1 < √3 := by nlinarith [Real.sqrt_nonneg 3]
  rw [l4g_ham_lt_iff]
  have h1 := (l4g_qFix_switching t).1
  have hq : t ^ 2 - 2 * √3 * t - 3 < 0 := by nlinarith
  have : √3 / 12 * (t - √3) * (t ^ 2 - 2 * √3 * t - 3) < 0 :=
    mul_neg_of_pos_of_neg (mul_pos (by positivity) (by linarith)) hq
  linarith

private lemma l4g_firstControl_qFix : TriFuller.firstControl TriFuller.qFix = TriFuller.ζ ^ 2 :=
  (firstControl_eq_iff (l4g_ne_zero_of_re (by rw [l4g_qFix_mk]; norm_num))).2
    ⟨ζ_sq_mem_VT, √3, by positivity, fun _ ht v hv ↦ l4g_qFix_max ht.1 ht.2 v hv⟩

private lemma l4g_firstSwitchTime_qFix : TriFuller.firstSwitchTime TriFuller.qFix = √3 := by
  have hs0 : 0 < √3 := by positivity
  rw [firstSwitchTime, l4g_firstControl_qFix]
  apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
  · exact ⟨√3 + 1 / 2, by positivity, 1, one_mem_VT, l4g_qFix_beaten (by linarith) (by linarith)⟩
  · rintro a ⟨ha0, v, hv, hlt⟩
    by_contra has
    exact absurd (l4g_qFix_max ha0.le (not_le.1 has).le v hv) (not_le.2 hlt)
  · intro w hw
    have hm : 0 < min (w - √3) 1 := lt_min (by linarith) one_pos
    have hm1 : min (w - √3) 1 ≤ w - √3 := min_le_left _ _
    have hm2 : min (w - √3) 1 ≤ 1 := min_le_right _ _
    exact ⟨√3 + min (w - √3) 1 / 2, ⟨by positivity, 1, one_mem_VT,
      l4g_qFix_beaten (by linarith) (by linarith)⟩, by linarith⟩

private lemma l4g_poincare_qFix :
    TriFuller.poincare TriFuller.qFix = TriFuller.ζ • TriFuller.qFix := by
  have hs : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [poincare, l4g_firstSwitchTime_qFix, l4g_firstControl_qFix, ζ_sq_eq_mk, ζ_eq_mk,
    l4g_qFix_mk, l4g_flow_mk, l4g_smul_mk]
  refine congrArg₂ Matrix.vecCons (congrArg₂ Complex.mk ?_ ?_)
    (congrArg₂ Matrix.vecCons (congrArg₂ Complex.mk ?_ ?_)
      (congrArg₂ Matrix.vecCons (congrArg₂ Complex.mk ?_ ?_) rfl))
  · linear_combination (-1 / 2) * hs
  · ring
  · linear_combination (-(√3 / 4)) * hs
  · linear_combination (1 / 4) * hs
  · linear_combination (-(√3 ^ 2 - 3) / 12) * hs
  · linear_combination (√3 / 12) * hs

private lemma l4g_hamMax_qFix : TriFuller.hamMax TriFuller.qFix = 3 / 4 := by
  have hv : ∀ v : ℂ, ham qFix v = 1 / 2 + RR v ⟨-1 / 2, 0⟩ := by
    intro v
    have hI : (⟨0, -1 / 2⟩ : ℂ) * I = ⟨1 / 2, 0⟩ := by
      apply Complex.ext <;> norm_num
    rw [ham, l4g_qFix_mk]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rw [hI, l4g_RR_mk]
    ring
  rw [hamMax, hv, hv, hv, ζ_sq_eq_mk, ζ_eq_mk, l4g_one_mk, l4g_RR_mk, l4g_RR_mk, l4g_RR_mk]
  norm_num

end TriFuller

/-- **Remark 13.5.4** (`rem:qfix`, label of this formalization; unlabelled, TeX 11402–11427), its
verifiable part. The fixed point `q_fix` corresponding to `(r, ζ₁) = (1, ζ)` in the proof of Lemma
13.5.2 has the form `q_fix = (1, -i/2, -1/2) mod 𝒢`: from `q_fix` the first control is `ζ²`, the
first switching time is `√3`, and `F(q_fix) = ζ · q_fix`; and "the Fuller-system Hamiltonian is
not zero at `q_fix`": `H_F⁺(q_fix) = 3/4`.

Not formalized: the remark's interpretation of `q_fix` as the limit, after the procedure of §14.2,
of the one-parameter family of Pontryagin extremals of §7.5 (the smoothed `6k+2`-gons) as
`y₀ = 1 - r → 1` (Mathematica `MCA:zfix1`; it needs Chapter 14 and is not used later). -/
theorem remark13_5_4 :
    TriFuller.firstControl TriFuller.qFix = TriFuller.ζ ^ 2 ∧
      TriFuller.firstSwitchTime TriFuller.qFix = √3 ∧
      TriFuller.poincare TriFuller.qFix = TriFuller.ζ • TriFuller.qFix ∧
      TriFuller.hamMax TriFuller.qFix = 3 / 4 :=
  ⟨TriFuller.l4g_firstControl_qFix, TriFuller.l4g_firstSwitchTime_qFix,
    TriFuller.l4g_poincare_qFix, TriFuller.l4g_hamMax_qFix⟩

end SmoothedPolygons
