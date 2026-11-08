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

All the numbers are certified: `r_scale` by sign changes of `P`
(`SmoothedPolygons/Ch13/RScale.lean`), the identities in `ℚ(√3)[r]/(P)`, and the sign conditions
on `(0, t_sw)` by exact algebra or interval bounds on `r_scale`.
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

/-- The angular parts of `qOutCart` and `τ(qOutCart)` lie in `Ξ_𝒲` (their third coordinates are
real and negative). -/
theorem l4st_ang_qOutCart_mem : ang qOutCart ∈ XiW ∧ ang (tau qOutCart) ∈ XiW := by
  sorry

/-- The fixed point `q_out ∈ Ξ_𝒲/V_T` (Lemma 13.5.2): the switching point of the outward
triangular spiral. -/
noncomputable def qOut : XiWQuot := Quotient.mk'' ⟨ang qOutCart, l4st_ang_qOutCart_mem.1⟩

/-- The fixed point `q_in ∈ Ξ_𝒲/V_T` (Lemma 13.5.2): the switching point of the inward triangular
spiral, represented by `τ(qOutCart)`. -/
noncomputable def qIn : XiWQuot := Quotient.mk'' ⟨ang (tau qOutCart), l4st_ang_qOutCart_mem.2⟩

/-- The normalization of (13.5.1): `Re z₁ = -1`, and `z₃` is real and negative. -/
theorem l4st_qOutCart_normalization :
    (qOutCart 0).re = -1 ∧ (qOutCart 2).im = 0 ∧ (qOutCart 2).re < 0 := by
  sorry

/-- The first control of `qOutCart` is `ζ = ζ₁²` (TeX 11384–11386; the tie between `ζ` and `ζ²` on
the wall `𝒲₀` is broken by `Im z₂ > 0`). -/
theorem l4st_firstControl_qOutCart : firstControl qOutCart = ζ := by
  sorry

/-- **The first switching time of (13.5.1)** (TeX 11340–11344, and inventory gap 10(b)):
`t_sw = 2(1 + r + r²)/(√3(r + 1))` with `r = r_scale`, and it is the *first* switching time: along
`t ↦ z(t, qOutCart, ζ)` the switching function from `ζ` to `ζ²` is nonnegative on `[0, t_sw]`
(it vanishes at `0` because `z₃` is real), the switching function from `ζ` to `1` is positive on
`[0, t_sw)` and changes sign at its simple root `t_sw`.

Proof route: both switching functions are cubics in `t` with coefficients in `ℚ(√3, r_scale)`;
their signs on `[0, t_sw]` follow from exact factorizations modulo `P` or from interval bounds on
`r_scale` (`l4st_rScale_fine_bounds`) and Sturm sequences. -/
theorem l4st_firstSwitchTime_qOutCart :
    firstSwitchTime qOutCart = 2 * (1 + rScale + rScale ^ 2) / (√3 * (rScale + 1)) := by
  sorry

/-- **The fixed-point equation (13.5.2) at `q_out`** (TeX 11348–11358): `F(qOutCart) =
ζ² · (r z₁, r² z₂, r³ z₃)` with `r = r_scale`, the outward triangular spiral (`r_scale > 1`).
Proof route: with `t_sw` from `l4st_firstSwitchTime_qOutCart`, both sides are explicit elements
of `ℚ(√3)(r)`, equal modulo `P(r)`. -/
theorem l4st_poincare_qOutCart : poincare qOutCart = ζ ^ 2 • scale rScale qOutCart := by
  sorry

/-- **The Hamiltonian vanishes at `q_out`** (inventory, gap 10(c): the statement of Lemma 13.5.2
asserts it, the proof does not show it). `H_F(z⁰, u)` along the family `(r, ζ²)` has numerator
`√3 r³ P(r)`, so it vanishes exactly at the roots of `P`. -/
theorem l4st_hamMax_qOutCart : hamMax qOutCart = 0 := by
  sorry

/-- **The inward spiral** (TeX 11381–11383): `F(τ qOutCart) = ζ² · (r⁻¹ z₁, r⁻² z₂, r⁻³ z₃)` with
`r = r_scale`. Proof route: `qOutCart` is a genuine switching point (its most recent control is
`ζ²`, the conjugate of the first control `ζ` of `τ(qOutCart)`, Lemma 13.2.5), so
`F(τ F(qOutCart)) = τ(qOutCart)` (`l4st_poincare_tau_poincare`); with
`τ F(qOutCart) = ζ · (r_s-scaling)(τ qOutCart)` and the equivariance of `F`
(`l4st_poincare_smul`, `l4st_poincare_scale`). -/
theorem l4st_poincare_tau_qOutCart :
    poincare (tau qOutCart) = ζ ^ 2 • scale rScale⁻¹ (tau qOutCart) := by
  sorry

/-- `τ(q_out) = q_in` in `Ξ_𝒲/V_T` (TeX 11302–11303). -/
theorem l4st_tauQuot_qOut : tauQuot qOut = qIn := by
  sorry

/-- `q_out` and `q_in` lie in `Ξ_{𝒲,0}/V_T`: the Hamiltonian vanishes there
(`l4st_hamMax_qOutCart`, scaling and `H_F⁺(τ z) = H_F⁺(z)`). -/
theorem l4st_hamMaxQuot_qOut_qIn : hamMaxQuot qOut = 0 ∧ hamMaxQuot qIn = 0 := by
  sorry

/-- `q_out` as a point of `Ξ_{𝒲,0}/V_T`. -/
noncomputable def qOut0 : XiW0Quot := ⟨qOut, l4st_hamMaxQuot_qOut_qIn.1⟩

/-- `q_in` as a point of `Ξ_{𝒲,0}/V_T`. -/
noncomputable def qIn0 : XiW0Quot := ⟨qIn, l4st_hamMaxQuot_qOut_qIn.2⟩

/-- `7.4 < t_sw < 7.41` for (13.5.1) (the book's `t_sw ≈ 7.4`, TeX 11344). -/
theorem l4st_firstSwitchTime_qOutCart_bounds :
    7.4 < firstSwitchTime qOutCart ∧ firstSwitchTime qOutCart < 7.41 := by
  sorry

/-- The fixed point `q_fix = (1, -i/2, -1/2)` of Remark 13.5.4 (TeX 11402–11406). -/
noncomputable def qFix : Fin 3 → ℂ := ![1, -I / 2, -1 / 2]

end TriFuller

/-- **Remark 13.5.4** (unlabelled, TeX 11402–11427), its verifiable part. The fixed point `q_fix`
corresponding to `(r, ζ₁) = (1, ζ)` in the proof of Lemma 13.5.2 has the form
`q_fix = (1, -i/2, -1/2) mod 𝒢`: from `q_fix` the first control is `ζ²`, the first switching time
is `√3`, and `F(q_fix) = ζ · q_fix`; and "the Fuller-system Hamiltonian is not zero at `q_fix`":
`H_F⁺(q_fix) = 3/4`.

Not formalized: the remark's interpretation of `q_fix` as the limit, after the procedure of §14.2,
of the one-parameter family of Pontryagin extremals of §7.5 (the smoothed `6k+2`-gons) as
`y₀ = 1 - r → 1` (Mathematica `MCA:zfix1`; it needs Chapter 14 and is not used later). -/
theorem remark13_5_4 :
    TriFuller.firstControl TriFuller.qFix = TriFuller.ζ ^ 2 ∧
      TriFuller.firstSwitchTime TriFuller.qFix = √3 ∧
      TriFuller.poincare TriFuller.qFix = TriFuller.ζ • TriFuller.qFix ∧
      TriFuller.hamMax TriFuller.qFix = 3 / 4 := by
  sorry

end SmoothedPolygons
