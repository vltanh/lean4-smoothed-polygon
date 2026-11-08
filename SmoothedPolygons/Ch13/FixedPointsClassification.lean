module

public import SmoothedPolygons.Ch13.FixedPoints

/-!
# Chapter 13: Lemma 13.5.2 (the two fixed points) and Remark 13.5.3

Lemma 13.5.2 of Hales–Vajjha, *Packings of Smoothed Polygons* (`lem:qout`, TeX 11298–11387):
`F_ang` has exactly two fixed points in `Ξ_𝒲/V_T` at which the Hamiltonian vanishes, `q_out` and
`q_in = τ(q_out)`, the switching points of the outward and inward triangular spirals, with the
scaling factor `r_scale`, the unique real root greater than `1` of the palindromic polynomial
`P`. And Remark 13.5.3 (TeX 11389–11400): the iterates of `F` along the spirals.

The book's proof, step by step, with the helper statements of this file:
1. A fixed point of `F_ang` in `Ξ_𝒲/V_T` lifts to `z⁰` with `F(z⁰) = ζ₁ (r z₁⁰, r² z₂⁰, r³ z₃⁰)`
   for some `r > 0`, `ζ₁ ∈ V_T` (the fixed-point condition `eqn:fixed-point` (13.5.2)).
2. Solving the linear equations (13.2.2) gives `z⁰` in terms of `(t_sw, u, r, ζ₁)`
   (`fixedPointCandidate`, `l4st_eq_fixedPointCandidate`; TeX 11353–11358), and `z₃⁰ ≠ 0`.
3. The maximum principle at `t = 0` and `t = t_sw` (the first control `u` and the next one `ζ₁ u`
   both maximize at `t_sw`) gives `z₃⁰ ū ζ₁² ∈ ℝ_{≤0}` (TeX 11359–11372; the book's displayed
   inequalities are garbled, inventory gap 10(a), the final condition is right), whence
   `(r, ζ₁) ∈ {(1, ζ), (r_scale, ζ²), (1/r_scale, ζ²)}` (`l4st_fixedPoint_cases`): the imaginary
   part is proportional to `(r - 1) P(r)` for `ζ₁ ∈ {ζ, ζ²}`, the sign of the real part selects
   the roots, and `ζ₁ = 1` is impossible (the control must switch).
4. `r = 1` is rejected because `H_F ≠ 0` there (`l4st_hamMax_ne_zero_of_r_eq_one`; the book's
   `1/(4√3)` in the normalization `t_sw = 1`).
5. The two remaining solutions are, up to the virial group, `qOutCart` and `τ(qOutCart)`
   (`l4st_fixedPointCandidate_virialEquiv`), which are fixed points with `H_F⁺ = 0`
   (`SmoothedPolygons/Ch13/FixedPoints.lean`: the verification the book leaves out, gap 10(b),(c))
   and are distinct (`l4st_qOut_ne_qIn`).
-/

@[expose] public section

namespace SmoothedPolygons

open Complex Set

namespace TriFuller

/-- The solution `z⁰` of the fixed-point equations `z_j(t, z⁰, u) = r^j w z_j⁰` (`j = 1, 2, 3`) of
(13.5.2), from the linear equations (13.2.2) (TeX 11353–11358):
`z₁⁰ = -itu/(rw - 1)`, `z₂⁰ = -it²u(rw + 1)/(2(rw - 1)(r²w - 1))`,
`z₃⁰ = -it³u(1 + 2rw + 2r²w + r³w²)/(6(rw - 1)(r²w - 1)(r³w - 1))`. -/
noncomputable def fixedPointCandidate (r : ℝ) (w u : ℂ) (t : ℝ) : Fin 3 → ℂ :=
  ![-I * t * u / (r * w - 1),
    -I * t ^ 2 * u * (r * w + 1) / (2 * (r * w - 1) * (r ^ 2 * w - 1)),
    -I * t ^ 3 * u * (1 + 2 * r * w + 2 * r ^ 2 * w + r ^ 3 * w ^ 2) /
      (6 * (r * w - 1) * (r ^ 2 * w - 1) * (r ^ 3 * w - 1))]

/-- Step 2 of the proof of Lemma 13.5.2: for `r > 0` and `w ∈ V_T` with `(r, w) ≠ (1, 1)`, the
linear system `z(t, z⁰, u) = w (r z₁⁰, r² z₂⁰, r³ z₃⁰)` has the unique solution
`fixedPointCandidate r w u t` (the determinant `(rw - 1)(r²w - 1)(r³w - 1)` vanishes only for
`r = 1`, `w = 1`). -/
theorem l4st_eq_fixedPointCandidate {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : w ∈ VT)
    (hrw : ¬ (r = 1 ∧ w = 1)) {u : ℂ} {t : ℝ} {z : Fin 3 → ℂ}
    (h : flow t z u = w • scale r z) : z = fixedPointCandidate r w u t := by
  sorry

/-- Step 3 of the proof of Lemma 13.5.2 (TeX 11359–11380): if `z⁰ ≠ 0` lies on a wall and
`F(z⁰) = w (r z₁⁰, r² z₂⁰, r³ z₃⁰)` with `r > 0`, `w ∈ V_T`, then
`(r, w) ∈ {(1, ζ), (r_scale, ζ²), (1/r_scale, ζ²)}`. -/
theorem l4st_fixedPoint_cases {z : Fin 3 → ℂ} (hz : z ≠ 0) (h₃ : z 2 ∈ walls) {r : ℝ}
    (hr : 0 < r) {w : ℂ} (hw : w ∈ VT) (h : poincare z = w • scale r z) :
    (r = 1 ∧ w = ζ) ∨ (r = rScale ∧ w = ζ ^ 2) ∨ (r = rScale⁻¹ ∧ w = ζ ^ 2) := by
  sorry

/-- Step 4 of the proof of Lemma 13.5.2 (TeX 11380–11381): the fixed points with `(r, ζ₁) = (1, ζ)`
have `H_F ≠ 0` (`H_F = t_sw³/(4√3)`; the book's `1/(4√3)` for `t_sw = 1`). -/
theorem l4st_hamMax_ne_zero_of_r_eq_one {z : Fin 3 → ℂ} (hz : z ≠ 0) (h₃ : z 2 ∈ walls)
    (h : poincare z = ζ • scale 1 z) : hamMax z ≠ 0 := by
  sorry

/-- Step 5 of the proof of Lemma 13.5.2: the fixed points with `(r, ζ₁) = (r_scale, ζ²)` are
virial-equivalent to `qOutCart`, those with `(1/r_scale, ζ²)` to `τ(qOutCart)`. -/
theorem l4st_fixedPointCandidate_virialEquiv {u : ℂ} (hu : u ∈ VT) {t : ℝ} (ht : 0 < t) :
    VirialEquiv qOutCart (fixedPointCandidate rScale (ζ ^ 2) u t) ∧
      VirialEquiv (tau qOutCart) (fixedPointCandidate rScale⁻¹ (ζ ^ 2) u t) := by
  sorry

/-- `q_out ≠ q_in` (their spirals have the scaling factors `r_scale ≠ 1/r_scale`). -/
theorem l4st_qOut_ne_qIn : qOut ≠ qIn := by
  sorry

end TriFuller

open TriFuller

/-- **Lemma 13.5.2** (`lem:qout`, TeX 11298–11387). The dynamical system `F_ang` has exactly two
fixed points in `Ξ_𝒲/V_T` at which the Hamiltonian vanishes. They are the switching points
`q_out`, `q_in` of outward and inward triangular spirals: `F(qOutCart) = ζ² · (r_scale-scaling)
(qOutCart)` and `F(τ qOutCart) = ζ² · (r_scale⁻¹-scaling)(τ qOutCart)`. They are related by the
time-reversing symmetry, `τ(q_out) = q_in`. After virial rescaling to make the real part of the
first coordinate equal to `-1` (and the third coordinate real and negative), `q_out` takes the
form (13.5.1) (`qOutCart = equilExact r_scale`), where `r = r_scale ≈ 6.27` is the unique real root
greater than `1` of the palindromic polynomial `1 - 5r - 7r² - 5r³ - 7r⁴ - 5r⁵ + r⁶`. The first
switching time of the initial condition (13.5.1) is `t_sw = 2(1 + r + r²)/(√3(r + 1)) ≈ 7.4`.

Proof: the book's, step by step, in the module docstring (`l4st_fixedPoint_cases`,
`l4st_hamMax_ne_zero_of_r_eq_one`, `l4st_fixedPointCandidate_virialEquiv`), with the verification
of the two spirals that the book omits (`l4st_firstSwitchTime_qOutCart`,
`l4st_poincare_qOutCart`, `l4st_hamMax_qOutCart`, `l4st_poincare_tau_qOutCart`) and the facts on
`r_scale` (`l4st_rScale_spec`, `l4st_rScale_unique`, `l4st_rScale_bounds`). -/
theorem lemma13_5_2 :
    {x : XiWQuot | poincareAngQuot x = x ∧ hamMaxQuot x = 0} = {qOut, qIn} ∧ qOut ≠ qIn ∧
      poincare qOutCart = ζ ^ 2 • scale rScale qOutCart ∧
      poincare (tau qOutCart) = ζ ^ 2 • scale rScale⁻¹ (tau qOutCart) ∧
      tauQuot qOut = qIn ∧
      qOutCart = equilExact rScale ∧
      ((qOutCart 0).re = -1 ∧ (qOutCart 2).im = 0 ∧ (qOutCart 2).re < 0) ∧
      (1 < rScale ∧ rScalePoly rScale = 0 ∧ ∀ r : ℝ, 1 < r → rScalePoly r = 0 → r = rScale) ∧
      (6.27 < rScale ∧ rScale < 6.28) ∧
      firstSwitchTime qOutCart = 2 * (1 + rScale + rScale ^ 2) / (√3 * (rScale + 1)) ∧
      (7.4 < firstSwitchTime qOutCart ∧ firstSwitchTime qOutCart < 7.41) := by
  sorry

/-- **Remark 13.5.3** (unlabelled, TeX 11389–11400). By the fixed-point equation (13.5.2), the
iterates of `F` satisfy `F^k(q_out) = (r_scale, ζ²)^k · q_out` (the virial action): discrete
points on a logarithmic spiral, moving outward because `r_scale > 1`. Similarly, `F^k(q_in)` are
points on an inward moving logarithmic spiral, `F^k(q_in) = (1/r_scale, ζ²)^k · q_in`.

Proof: induction on `k`, from `F(qOutCart) = ζ² · (r_scale-scaling)(qOutCart)` (Lemma 13.5.2)
and the equivariance of `F` under `V_T` and rescaling (`l4st_poincare_smul`,
`l4st_poincare_scale`). -/
theorem remark13_5_3 (k : ℕ) :
    poincare^[k] qOutCart = (ζ ^ 2) ^ k • scale (rScale ^ k) qOutCart ∧
      poincare^[k] (tau qOutCart) = (ζ ^ 2) ^ k • scale (rScale⁻¹ ^ k) (tau qOutCart) := by
  sorry

end SmoothedPolygons
