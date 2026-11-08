module

public import SmoothedPolygons.Ch13.FixedPointsClassification
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Topology.OpenPartialHomeomorph.Defs

/-!
# Chapter 13: the Jacobian of the Fuller–Poincaré map at `q_out` (certified)

The computation behind Lemma 13.5.5 of Hales–Vajjha, *Packings of Smoothed Polygons*
(`lem:eigenvalues`, TeX 11443–11453): "An open neighborhood of `q_out` in `Ξ_{𝒲,0}/V_T` is
diffeomorphic to an open subset of `ℝ³`. An explicit calculation of the eigenvalues of the Jacobian
matrix in terms of local coordinates centered at `q_out` gives the result. Numerically, the three
eigenvalues have absolute value less than `0.1`. The calculations were made in Mathematica." The
book gives no chart, matrix or values (inventory, gap 12); this file fixes them and states them
exactly.

**The chart.** Near `q_out`, every point of `Ξ_{𝒲,0}/V_T` has a unique representative `z ∈ ℂ³` with
`z₃ ∈ ℝ_{<0}` (rotation by `V_T`) and `Re z₁ = -1` (virial rescaling; `Re z₁ < 0` near `q_out`),
the normalization of (13.5.1). Writing `z₁ = -1 + ip`, `z₂ = c + id`, the condition `H_F⁺ = 0`
reads `pc + d - z₃/2 = 0` (the first control is `ζ` or `ζ²`, and `RR(ζ, z₃) = -z₃/2`), so
`z₃ = 2(pc + d)` and `x = (p, c, d) ∈ ℝ³` are coordinates (`chartCart`; the chart is
`l4st_exists_chart`). At `q_out`, `x_out = (Im z₁, Re z₂, Im z₂)` of (13.5.1) (`xOut`).

**The map in the chart** (`chartMap`). Near `x_out` the first control is `ζ` (`Im z₂ > 0`), and the
first switching time is the simple root, near `t_sw(q_out)`, of the switching function
`RR(ζ - 1, z₃(t))` from `ζ` to `1 = ζ/ζ` (a cubic in `t` with coefficients affine in `x`), a `C^∞`
function of `x` by the implicit function theorem. With `w = F(z) = z(t_sw, z, ζ)` on the wall
`𝒲₂`, the rotated point `ζ w` has `(ζ w)₃ ∈ ℝ_{<0}`, and the rescaling by
`s = -1/Re (ζ w)₁` gives the chart coordinates `(s Im(ζw)₁, s² Re(ζw)₂, s² Im(ζw)₂)`.

**The exact Jacobian** (`jacobianOut`, computed by implicit differentiation in
`ℚ(√3)[r]/(P(r))`, `r = r_scale`): its entries are the polynomials of degree `≤ 5` in `r_scale`
(some times `√3`) written in `jacobianOut`; numerically
`[[-0.0753149, -0.0301873, 0.0083316], [-0.0084243, -0.0109306, -0.0224886],
[-0.0441430, -0.0198735, -0.0011447]]`. Its characteristic polynomial is
`λ³ - T λ² + M λ - D` with `T, M, D ∈ ℚ(r_scale)` (the `√3` cancel) given by `jacTrace`,
`jacMinorSum`, `jacDet`; numerically `T = -0.0873902`, `M = 0.000588510`, `D = 4.16439 × 10⁻⁷`,
and the eigenvalues are `-0.0799655`, `-0.0080700`, `0.00064532` (the coordinator's independent
finite-difference computation in another chart agrees; inventory §13.5).

**The certificate** (`l4st_charpoly_jacobianOut_roots`). With `χ(λ) = λ³ - Tλ² + Mλ - D`:
`χ(-1/10) < 0 < χ(-1/20)`, `χ(-1/1000) < 0 < χ(1/10)`, so `χ` has three real roots in
`(-1/10, 1/10)`, which are all its complex roots (degree 3). Each `χ(λ₀)` is a polynomial of degree
`≤ 5` in `r_scale` with rational coefficients (reduce modulo `P`); its sign follows from
`l4st_rScale_fine_bounds` (the values are `≈ -1.85 × 10⁻⁴`, `6.4 × 10⁻⁵`, `-9.2 × 10⁻⁷`,
`1.9 × 10⁻³`, with derivative `≈ 6 × 10⁸` in `r`, so an enclosure of `r_scale` of width
`10⁻¹⁹` is ample).
-/

@[expose] public section

namespace SmoothedPolygons

open Complex Set Filter Topology Polynomial

namespace TriFuller

/-- The chart's Cartesian point `(-1 + ip, c + id, 2(pc + d))` of `x = (p, c, d) ∈ ℝ³`: the
normalized representative (`Re z₁ = -1`, `z₃` real) with `H_F⁺ = 0` (when `pc + d < 0`). -/
noncomputable def chartCart (x : Fin 3 → ℝ) : Fin 3 → ℂ :=
  ![-1 + (x 0 : ℂ) * I, (x 1 : ℂ) + (x 2 : ℂ) * I, ((2 * (x 0 * x 1 + x 2) : ℝ) : ℂ)]

/-- The chart coordinates `x_out = (Im z₁, Re z₂, Im z₂)` of `q_out`, from (13.5.1). -/
noncomputable def xOut : Fin 3 → ℝ := ![(qOutCart 0).im, (qOutCart 1).re, (qOutCart 1).im]

/-- The Fuller–Poincaré map in the chart near `x_out`: `w = ζ F(chartCart x)` (rotated back to the
wall `𝒲₀`), rescaled by `s = -1/Re w₁` to `Re z₁ = -1`, in the coordinates `(Im, Re, Im)`. -/
noncomputable def chartMap (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  let w := ζ • poincare (chartCart x)
  let s := -((w 0).re)⁻¹
  ![s * (w 0).im, s ^ 2 * (w 1).re, s ^ 2 * (w 1).im]

/-- The exact Jacobian matrix of `chartMap` at `x_out`, as a function of `r = r_scale`
(entries in `ℚ(√3)[r]`, reduced modulo `P`). -/
noncomputable def jacobianOut (r : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![6890 * r ^ 5 / 51 - 11126 * r ^ 4 / 17 - 53387 * r ^ 3 / 51 - 42974 * r ^ 2 / 51 -
        18318 * r / 17 - 43114 / 51,
      3155 * r ^ 5 / 51 - 15254 * r ^ 4 / 51 - 24622 * r ^ 3 / 51 - 19739 * r ^ 2 / 51 -
        25291 * r / 51 - 19868 / 51,
      √3 * (7025 * r ^ 5 / 51 - 2000 * r ^ 4 / 3 - 54622 * r ^ 3 / 51 - 43861 * r ^ 2 / 51 -
        3305 * r / 3 - 44128 / 51);
    -140075 * r ^ 5 / 459 + 226025 * r ^ 4 / 153 + 1088534 * r ^ 3 / 459 + 51379 * r ^ 2 / 27 +
        372902 * r / 153 + 878221 / 459,
      -14381 * r ^ 5 / 102 + 34804 * r ^ 4 / 51 + 55910 * r ^ 3 / 51 + 44788 * r ^ 2 / 51 +
        57404 * r / 51 + 45064 / 51,
      √3 * (-32221 * r ^ 5 / 102 + 77980 * r ^ 4 / 51 + 41742 * r ^ 3 / 17 + 33516 * r ^ 2 / 17 +
        42936 * r / 17 + 101080 / 51);
    √3 * (-26311 * r ^ 5 / 459 + 127673 * r ^ 4 / 459 + 11926 * r ^ 3 / 27 +
        162895 * r ^ 2 / 459 + 209998 * r / 459 + 162001 / 459),
      √3 * (-2963 * r ^ 5 / 102 + 2382 * r ^ 4 / 17 + 3882 * r ^ 3 / 17 + 9404 * r ^ 2 / 51 +
        11860 * r / 51 + 9430 / 51),
      -18005 * r ^ 5 / 102 + 43598 * r ^ 4 / 51 + 23274 * r ^ 3 / 17 + 56248 * r ^ 2 / 51 +
        71968 * r / 51 + 18822 / 17]

/-- The trace `T` of `jacobianOut r_scale`, reduced modulo `P` (`√3` cancels). -/
noncomputable def jacTrace (r : ℝ) : ℝ :=
  (-3101 * r ^ 5 + 15008 * r ^ 4 + 24115 * r ^ 3 + 19354 * r ^ 2 + 24806 * r + 19472) / 17

/-- The sum `M` of the principal `2 × 2` minors of `jacobianOut r_scale`, reduced modulo `P`. -/
noncomputable def jacMinorSum (r : ℝ) : ℝ :=
  (460838 * r ^ 5 - 2230742 * r ^ 4 - 3581397 * r ^ 3 - 2875008 * r ^ 2 - 3684085 * r) / 17 -
    170080

/-- The determinant `D` of `jacobianOut r_scale`, reduced modulo `P`. -/
noncomputable def jacDet (r : ℝ) : ℝ :=
  -310195 * r ^ 5 + 1501535 * r ^ 4 + 2410685 * r ^ 3 + 1935199 * r ^ 2 + 2479805 * r + 1946215

/-- **The chart** (TeX 11446–11447: "An open neighborhood of `q_out` in `Ξ_{𝒲,0}/V_T` is
diffeomorphic to an open subset of `ℝ³`"): an open partial homeomorphism `e` of `Ξ_{𝒲,0}/V_T`
into `ℝ³`, defined near `q_out`, with `e(q_out) = x_out`, whose inverse is
`x ↦ [ang (chartCart x)]`, and which conjugates `F_ang` to `chartMap` near `q_out`.

Proof route: near `x_out`, `chartCart x` has `z₃ < 0` and `H_F⁺ = 0`, so `x ↦ [ang (chartCart x)]`
maps a small ball into `Ξ_{𝒲,0}/V_T`; the inverse takes the representative with `ξ₃ ∈ ℝ_{<0}`
(unique, since the three rotations of `ξ₃ ≠ 0` lie on different walls) and rescales it to
`Re z₁ = -1`; both are continuous. The conjugacy is `l4st_ang_poincare_ang` with the
equivariance of `F` (`l4st_poincare_smul`, `l4st_poincare_scale`). -/
theorem l4st_exists_chart :
    ∃ e : OpenPartialHomeomorph XiW0Quot (Fin 3 → ℝ), qOut0 ∈ e.source ∧ e qOut0 = xOut ∧
      ∀ᶠ x in 𝓝 qOut0, poincareAngZero x ∈ e.source ∧ e (poincareAngZero x) = chartMap (e x) := by
  sorry

/-- `x_out` is a fixed point of the map in the chart (Lemma 13.5.2: `F(qOutCart) =
ζ² (r_scale-scaling)(qOutCart)`, and `ζ · ζ² = 1`). -/
theorem l4st_chartMap_xOut : chartMap xOut = xOut := by
  sorry

/-- The map in the chart is `C¹` (indeed `C^∞`) near `x_out`: near `x_out` the first control is `ζ`
(an open lexicographic condition, `Im z₂ > 0` on the wall `𝒲₀`), the first switching time is the
simple root of `RR(ζ - 1, z₃(t))` near `t_sw(q_out)`, smooth in `x` by the implicit function
theorem (Mathlib's `ImplicitFunction` or `HasStrictDerivAt` for a scalar equation), and the other
switching functions stay positive on `[0, t_sw]` by continuity and compactness. -/
theorem l4st_contDiffAt_chartMap : ContDiffAt ℝ 1 chartMap xOut := by
  sorry

/-- **The exact Jacobian at `q_out`**: the derivative of `chartMap` at `x_out` is the matrix
`jacobianOut r_scale` (implicit differentiation: `dt_sw = -(∂χ/∂x)/(∂χ/∂t)` at the simple root,
then the chain rule through the flow (13.2.2), the rotation and the rescaling; exact arithmetic in
`ℚ(√3)[r]` modulo `P(r)`). -/
theorem l4st_hasFDerivAt_chartMap :
    HasFDerivAt chartMap (Matrix.toLin' (jacobianOut rScale)).toContinuousLinearMap xOut := by
  sorry

/-- The characteristic polynomial of the Jacobian: `λ³ - T λ² + M λ - D` with
`T = jacTrace r_scale`, `M = jacMinorSum r_scale`, `D = jacDet r_scale` (polynomial identities in
`ℚ(√3)[r]` modulo `P(r)`, using `l4st_rScale_spec`). -/
theorem l4st_charpoly_jacobianOut :
    (jacobianOut rScale).charpoly =
      X ^ 3 - C (jacTrace rScale) * X ^ 2 + C (jacMinorSum rScale) * X - C (jacDet rScale) := by
  sorry

/-- **The certified eigenvalue bound** ("Numerically, the three eigenvalues have absolute value
less than `0.1`", TeX 11450–11452): every complex root of the characteristic polynomial of the
Jacobian has modulus `< 1/10`. Certificate: `χ(-1/10) < 0 < χ(-1/20)` and
`χ(-1/1000) < 0 < χ(1/10)` (the signs of degree-5 polynomials in `r_scale`, from
`l4st_rScale_fine_bounds`), so the three roots are real and lie in `(-1/10, 1/10)`. -/
theorem l4st_charpoly_jacobianOut_roots :
    ∀ μ : ℂ, aeval μ (jacobianOut rScale).charpoly = 0 → ‖μ‖ < 1 / 10 := by
  sorry

end TriFuller

end SmoothedPolygons
