module

public import SmoothedPolygons.Ch13.FixedPointsClassification
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Topology.OpenPartialHomeomorph.Defs
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Chapter 13: the Jacobian of the Fuller–Poincaré map at `q_out` (certified)

The computation behind Lemma 13.5.5 of Hales–Vajjha, *Packings of Smoothed Polygons*
(`lem:eigenvalues`, TeX 11443–11453): "An open neighborhood of `q_out` in `Ξ_{𝒲,0}/V_T` is
diffeomorphic to an open subset of `ℝ³`. An explicit calculation of the eigenvalues of the Jacobian
matrix in terms of local coordinates centered at `q_out` gives the result. Numerically, the three
eigenvalues have absolute value less than `0.1`. The calculations were made in Mathematica." The
book gives no chart, matrix or values (REPORT.md, E68); this file fixes them and states them
exactly.

**The chart.** Near `q_out`, every point of `Ξ_{𝒲,0}/V_T` has a unique representative `z ∈ ℂ³` with
`z₃ ∈ ℝ_{<0}` (rotation by `V_T`) and `Re z₁ = -1` (virial rescaling; `Re z₁ < 0` near `q_out`),
the normalization of (13.5.1). Writing `z₁ = -1 + ip`, `z₂ = c + id`, the condition `H_F⁺ = 0`
reads `pc + d - z₃/2 = 0` (the first control is `ζ` or `ζ²`, and `RR(ζ, z₃) = -z₃/2`), so
`z₃ = 2(pc + d)` and `x = (p, c, d) ∈ ℝ³` are coordinates (`chartCart`; the chart is
`exists_chart`). At `q_out`, `x_out = (Im z₁, Re z₂, Im z₂)` of (13.5.1) (`xOut`).

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
and the eigenvalues are `-0.0799655`, `-0.0080700`, `0.00064532` (an independent
finite-difference computation in another chart agrees).

**The certificate** (`norm_lt_of_aeval_charpoly_jacobianOut_eq_zero`). With
`χ(λ) = λ³ - Tλ² + Mλ - D`: `χ(-1/10) < 0 < χ(-1/20)`, `χ(-1/1000) < 0 < χ(1/10)`, so `χ`
has three real roots in
`(-1/10, 1/10)`, which are all its complex roots (degree 3). Each `χ(λ₀)` is a polynomial of degree
`≤ 5` in `r_scale` with rational coefficients (reduce modulo `P`); its sign follows from
`rScale_fine_bounds` (the values are `≈ -1.85 × 10⁻⁴`, `6.4 × 10⁻⁵`, `-9.2 × 10⁻⁷`,
`1.9 × 10⁻³`, with derivative `≈ 6 × 10⁸` in `r`, so an enclosure of `r_scale` of width
`10⁻¹⁹` is ample).

**For Chapter 14: the normalization map** (`chartOf`). Theorem 14.3.3 (TeX 11911–11917) needs the
linearization of `F` at `q_out` on the exceptional divisor (three eigenvalues of modulus `< 1`),
not only the asymptotic stability of Lemma 13.5.5, and it must transfer it to its own
coordinates `x̃` on the divisor. The map `chartOf : ℂ³ → ℝ³` (rotate so that `z₃ ∈ ℝ_{<0}`, rescale
so that `Re z₁ = -1`, read off `(Im z₁, Re z₂, Im z₂)`) does this: `chartOf (chartCart x) = x` on
the chart's domain (`chartOf_chartCart`), `chartMap = chartOf ∘ F ∘ chartCart` near `x_out`
(`chartMap_eventuallyEq_chartOf`), and `chartOf` is smooth near `qOutCart`
(`eventually_contDiffAt_chartOf`). With `hasFDerivAt_chartMap` and
`norm_lt_of_aeval_charpoly_jacobianOut_eq_zero`, the chain rule then gives the linearization in
any smooth coordinates on the divisor near `q_out`.

**The proofs.**
* The local structure (`l4j_local`, `l4j_eventually_local`): with `x = (p, c, d)`, the switching
  function from `ζ` to `1` along the chart is the cubic
  `g(x, t) = -3(pc + d) + t(√3 d - 3c)/2 + t²(3 + √3 p)/4 - √3 t³/12`; at a root `T`,
  `g(x, t) = (t - T)(-(√3/12) t² + B t + C)`, and at `(x_out, t₀)`, with `r = r_scale`,
  `B = -(r² - 5r - 2)/(6(r + 1)) < 0` and
  `√3 C = -(r² + r + 1)(r⁴ - 6r³ - 2r² + 3r + 1)/(3(r + 1)²(r² - r + 1)) < 0`. The root
  `ψ(x)` near `t₀` comes from the implicit function theorem (`g(x_out, t₀) = 0` and
  `∂g/∂t (x_out, t₀) = -√3 r² d ≠ 0` modulo `P`). This also reproves near `x_out` that `t₀` is the
  first switching time of `q_out`; `firstSwitchTime_qOutCart` is not used.
* The exact Jacobian: `chartMap = N(x, ψ(x))` near `x_out` with `N` explicit, and the chain rule;
  each of the nine entries is an identity in `ℚ(√3)[r]/(P)`, proved by `linear_combination` with
  `P(r_scale) = 0` and `√3² = 3` after reducing the coordinates of `x_out`, `t₀`,
  `(Re (ζ w)₁)⁻¹ = -1/r` and `(∂g/∂t)⁻¹` to representatives of degree `≤ 5` in `r` (certificates by
  exact polynomial division).
* The eigenvalue certificate: `χ(λ₀)` is expanded at the convergent `3961388236/631380705` of
  `r_scale` (within `10⁻¹⁸`, from `rScale_fine_bounds`); its Taylor coefficients of order
  `≥ 1` are positive, which bounds the error. The intermediate value theorem gives the three real
  roots, and a monic cubic with three distinct real roots has no other complex roots.

**The normal direction (block-triangular structure; not formalized).** On the 4-dimensional chart
`Re z₁ = -1`, `z₃ ∈ ℝ_{<0}` free, with coordinates `(p, c, d, z₃)`, let `G` be the normalized
Poincaré map and `s(x)` its rescaling factor. With `h = H_F⁺`, `h(G(x)) = s(x)³ h(x)`
(`hamMax_smul_scale_and_tau`, `hamMax_poincare`), so the hypersurface `{h = 0}` (the chart
`chartCart`) is invariant under `G`, and at the fixed point, where `h = 0` and `s = 1/r_s`,
`dh ∘ DG = r_s⁻³ dh`. The derivative of `G` at the fixed point is therefore block triangular: its
eigenvalues are the three eigenvalues above, tangent to `{h = 0}`, and the normal eigenvalue
`r_s⁻³ ≈ 0.0040489`.
-/

@[expose] public section

namespace SmoothedPolygons

open Complex Set Filter Topology Polynomial

open scoped ContDiff

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

/-- **The normalization map** `ℂ³ → ℝ³` of the chart, defined on all of `ℂ³` (for Chapter 14,
which works in its own coordinates): rotate `z` by the unit complex number
`ω = -z̄₃/|z₃|`, so that `(ω z)₃ = -|z₃| ∈ ℝ_{<0}` (when `z₃ ≠ 0`), rescale the result by
`s = -1/Re (ω z)₁ > 0` so that `Re z₁ = -1` (when `Re (ω z)₁ < 0`), and read off
`(Im z₁, Re z₂, Im z₂)`. On the walls the rotation is by an element of `V_T` (for `z₃ ∈ ℝ_{<0} ζ²`
it is `ζ`, as in `chartMap`); off them it is not, which makes `chartOf` smooth near `qOutCart`.
It is invariant under the virial rescalings `(r z₁, r² z₂, r³ z₃)`, `r > 0`, and under
multiplication by unit complex numbers. -/
noncomputable def chartOf (z : Fin 3 → ℂ) : Fin 3 → ℝ :=
  let w := (-starRingEnd ℂ (z 2) / (‖z 2‖ : ℂ)) • z
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

/-! ### Helpers: the explicit map in the chart -/

private lemma l4j_sqrt3_sq : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

/-- The real part of the rotated first coordinate `(ζ z(t))₁` along the chart. -/
private noncomputable def l4j_R0 (x : Fin 3 → ℝ) (t : ℝ) : ℝ := 1 / 2 - √3 * (x 0 + t) / 2

/-- The imaginary part of `(ζ z(t))₁` along the chart. -/
private noncomputable def l4j_I0 (x : Fin 3 → ℝ) (t : ℝ) : ℝ := (t - x 0 - √3) / 2

/-- The real part of `(ζ z(t))₂` along the chart. -/
private noncomputable def l4j_R1 (x : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  -x 1 / 2 - √3 * x 2 / 2 + t / 2 - √3 * x 0 * t / 2 - √3 * t ^ 2 / 4

/-- The imaginary part of `(ζ z(t))₂` along the chart. -/
private noncomputable def l4j_I1 (x : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  √3 * x 1 / 2 - x 2 / 2 - x 0 * t / 2 - √3 * t / 2 + t ^ 2 / 4

/-- The switching function `RR(ζ - 1, z₃(t))` from `ζ` to `1` along the chart (`√3` times the
book's `χ`), a cubic in `t`. -/
private noncomputable def l4j_g (x : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  -3 * (x 0 * x 1 + x 2) + t * (√3 * x 2 - 3 * x 1) / 2 + t ^ 2 * (3 + √3 * x 0) / 4 -
    √3 * t ^ 3 / 12

/-- The normalized point `(s Im w₁, s² Re w₂, s² Im w₂)`, `s = -1/Re w₁`, of `w = ζ z(t)`. -/
private noncomputable def l4j_N (x : Fin 3 → ℝ) (t : ℝ) : Fin 3 → ℝ :=
  ![-(l4j_R0 x t)⁻¹ * l4j_I0 x t, (-(l4j_R0 x t)⁻¹) ^ 2 * l4j_R1 x t,
    (-(l4j_R0 x t)⁻¹) ^ 2 * l4j_I1 x t]

private lemma l4j_flow_chartCart (x : Fin 3 → ℝ) (t : ℝ) :
    (ζ * flow t (chartCart x) ζ 0).re = l4j_R0 x t ∧
      (ζ * flow t (chartCart x) ζ 0).im = l4j_I0 x t ∧
      (ζ * flow t (chartCart x) ζ 1).re = l4j_R1 x t ∧
      (ζ * flow t (chartCart x) ζ 1).im = l4j_I1 x t ∧
      RR (ζ - 1) (flow t (chartCart x) ζ 2) = l4j_g x t ∧
      RR (ζ - ζ ^ 2) (flow t (chartCart x) ζ 2) = √3 * t * (x 2 + x 0 * t / 2 + t ^ 2 / 12) := by
  have h3 := l4j_sqrt3_sq
  simp only [flow, chartCart, RR_eq_re_mul_add_im_mul, Matrix.cons_val, Complex.mul_re,
    Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.div_re,
    Complex.div_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_re, Complex.one_im, ζ_re, ζ_im, ζ_sq_re, ζ_sq_im, l4j_R0, l4j_I0,
    l4j_R1, l4j_I1, l4j_g, ← Complex.ofReal_pow]
  norm_num
  refine ⟨by ring, by linear_combination (t / 4) * h3, by ring,
    by linear_combination (t ^ 2 / 8) * h3, by ring, by ring⟩

/-- The chart's Cartesian points are nonzero (`Re z₁ = -1`). -/
private lemma l4j_chartCart_ne_zero (x : Fin 3 → ℝ) : chartCart x ≠ 0 := by
  intro h
  have := congrArg (fun z ↦ (z 0).re) h
  simp [chartCart] at this

/-- In the chart, `chartMap` is the normalized point of `ζ z(t_sw)` as soon as the first control
is `ζ`. -/
private lemma l4j_chartMap_eq {x : Fin 3 → ℝ} (h : firstControl (chartCart x) = ζ) :
    chartMap x = l4j_N x (firstSwitchTime (chartCart x)) := by
  obtain ⟨h0, h1, h2, h3, -⟩ := l4j_flow_chartCart x (firstSwitchTime (chartCart x))
  simp only [chartMap, poincare, h, Pi.smul_apply, smul_eq_mul, l4j_N, h0, h1, h2, h3]

/-- `H_F(w, v) ≤ H_F(w, u)` if and only if `RR(u - v, w₃) ≥ 0`. -/
private lemma l4j_ham_le_iff (w : Fin 3 → ℂ) (u v : ℂ) :
    ham w v ≤ ham w u ↔ 0 ≤ RR (u - v) (w 2) := by
  simp only [ham, RR_eq_re_mul_add_im_mul, Complex.sub_re, Complex.sub_im]
  constructor <;> intro h <;> linarith

/-- **The first control and the first switching time in the chart.** If `p > 0`, `d > 0`, and
`T > 0` is a root of the switching function `l4j_g x` from `ζ` to `1` whose quotient
`l4j_g x t / (t - T) = -(√3/12) t² + B t + C` has `B, C < 0`, then the first control of
`chartCart x` is `ζ` and its first switching time is `T`: along `t ↦ z(t, chartCart x, ζ)` the
switching function from `ζ` to `ζ²` is `√3 t (d + pt/2 + t²/12) ≥ 0`, and the one from `ζ` to `1`
is `(t - T) k(t)` with `k < 0` on `t ≥ 0`, positive on `[0, T)` and negative after `T`. -/
private lemma l4j_local {x : Fin 3 → ℝ} {T : ℝ} (hp : 0 < x 0) (hd : 0 < x 2) (hT : 0 < T)
    (hg : l4j_g x T = 0) (hB : -√3 * T / 12 + (3 + √3 * x 0) / 4 < 0)
    (hC : -√3 * T ^ 2 / 12 + (3 + √3 * x 0) * T / 4 + (√3 * x 2 - 3 * x 1) / 2 < 0) :
    firstControl (chartCart x) = ζ ∧ firstSwitchTime (chartCart x) = T := by
  have h3 : 0 < √3 := by positivity
  set B := -√3 * T / 12 + (3 + √3 * x 0) / 4 with hBdef
  set C := -√3 * T ^ 2 / 12 + (3 + √3 * x 0) * T / 4 + (√3 * x 2 - 3 * x 1) / 2 with hCdef
  have hfac : ∀ t, l4j_g x t = (t - T) * (-√3 / 12 * t ^ 2 + B * t + C) := by
    intro t
    have := hg
    simp only [l4j_g, hBdef, hCdef] at this ⊢
    linear_combination this
  have hk : ∀ t, 0 ≤ t → -√3 / 12 * t ^ 2 + B * t + C < 0 := by
    intro t ht
    nlinarith [mul_nonneg h3.le (sq_nonneg t), mul_nonneg ht (neg_nonneg.mpr hB.le)]
  have hg_le : ∀ t, 0 ≤ t → t ≤ T → 0 ≤ l4j_g x t := fun t ht₀ htT ↦ by
    rw [hfac]; exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (hk t ht₀).le
  have hg_lt : ∀ t, T < t → l4j_g x t < 0 := fun t ht ↦ by
    rw [hfac]; exact mul_neg_of_pos_of_neg (by linarith) (hk t (by linarith))
  -- `ζ` is optimal on `[0, T]`
  have hopt : ∀ t, 0 ≤ t → t ≤ T → ∀ v ∈ VT,
      ham (flow t (chartCart x) ζ) v ≤ ham (flow t (chartCart x) ζ) ζ := by
    intro t ht₀ htT v hv
    obtain ⟨-, -, -, -, h1, h2⟩ := l4j_flow_chartCart x t
    rw [l4j_ham_le_iff]
    rcases mem_VT.mp hv with rfl | rfl | rfl
    · rw [h1]; exact hg_le t ht₀ htT
    · simp [RR]
    · rw [h2]; positivity
  have hfc : IsFirstControl (chartCart x) ζ :=
    ⟨mem_VT.mpr (Or.inr (Or.inl rfl)), T, hT, fun t ht v hv ↦ hopt t ht.1 ht.2 v hv⟩
  have hζ : firstControl (chartCart x) = ζ :=
    (firstControl_eq_iff (l4j_chartCart_ne_zero x)).mpr hfc
  refine ⟨hζ, ?_⟩
  have hS : {t : ℝ | 0 < t ∧ ∃ v ∈ VT,
      ham (flow t (chartCart x) (firstControl (chartCart x))) (firstControl (chartCart x)) <
        ham (flow t (chartCart x) (firstControl (chartCart x))) v} = Ioi T := by
    ext t
    rw [hζ]
    simp only [Set.mem_ofPred_eq, mem_Ioi]
    constructor
    · rintro ⟨ht, v, hv, hlt⟩
      by_contra hle
      exact (hopt t ht.le (not_lt.mp hle) v hv).not_gt hlt
    · intro ht
      refine ⟨hT.trans ht, 1, mem_VT.mpr (Or.inl rfl), ?_⟩
      obtain ⟨-, -, -, -, h1, -⟩ := l4j_flow_chartCart x t
      have := hg_lt t ht
      rw [← h1, ← not_le, l4j_ham_le_iff] at *
      exact this
  rw [firstSwitchTime, hS, csInf_Ioi]

/-! ### The point `x_out` -/

/-- The maximized Hamiltonian of a normalized point (`Re z₁ = -1`, `z₃ ∈ ℝ_{<0}`):
`H_F⁺(z) = H_F(z, ζ) = H_F(z, ζ²) = p c + d - z₃/2`. -/
private lemma l4j_hamMax_normalized {z : Fin 3 → ℂ} (h0 : (z 0).re = -1) (h2 : (z 2).im = 0)
    (h2' : (z 2).re < 0) : hamMax z = (z 0).im * (z 1).re + (z 1).im - (z 2).re / 2 := by
  simp only [hamMax, ham, RR_eq_re_mul_add_im_mul, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.one_re, Complex.one_im, ζ_re, ζ_im, ζ_sq_re, ζ_sq_im, h0, h2,
    mul_zero, mul_one, add_zero, zero_sub]
  rw [max_self, max_eq_right (by linarith)]
  ring

/-- `chartCart x_out = qOutCart`: the third coordinate of `qOutCart` is `2(pc + d)` because
`H_F⁺(qOutCart) = 0` (`hamMax_qOutCart`). -/
private lemma l4j_chartCart_xOut : chartCart xOut = qOutCart := by
  obtain ⟨h0, h2, h2'⟩ := qOutCart_normalization
  have hH := hamMax_qOutCart
  rw [l4j_hamMax_normalized h0 h2 h2'] at hH
  funext i
  fin_cases i
  · apply Complex.ext <;> simp [chartCart, xOut, h0]
  · apply Complex.ext <;> simp [chartCart, xOut]
  · apply Complex.ext <;> simp [chartCart, xOut, h2]
    linarith

/-- The coordinates of `x_out` as rational functions of `r_scale` (from (13.5.1)). -/
private lemma l4j_xOut_rat :
    xOut 0 = (-1 + rScale) / (√3 * (1 + rScale)) ∧
      xOut 1 = -((-1 + rScale ^ 3) / (√3 * (1 + rScale ^ 3))) ∧
      xOut 2 = (1 - 3 * rScale - 2 * rScale ^ 2 - 3 * rScale ^ 3 + rScale ^ 4) /
        (3 * (1 + rScale + rScale ^ 3 + rScale ^ 4)) := by
  simp only [xOut, qOutCart, equilExact, Matrix.cons_val, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im]
  norm_num

/-- The first switching time of (13.5.1), `t₀ = 2(1 + r + r²)/(√3(r + 1))` (TeX 11340–11344). -/
private noncomputable def l4j_t0 : ℝ := 2 * (1 + rScale + rScale ^ 2) / (√3 * (rScale + 1))

/-- Representatives in `ℚ[r]/(P)`: `x_out = (√3 Pp(r), √3 Pc(r), Pd(r))`, `t₀ = √3 Pt(r)`. -/
private noncomputable def l4j_Pp (r : ℝ) : ℝ :=
  2 * r ^ 5 / 9 - 4 * r ^ 4 / 3 - 2 * r ^ 3 / 9 - 8 * r ^ 2 / 9 - 2 * r / 3 - 1 / 9

private noncomputable def l4j_Pc (r : ℝ) : ℝ :=
  -4 * r ^ 5 / 81 + 8 * r ^ 4 / 27 - 2 * r ^ 3 / 81 + 46 * r ^ 2 / 81 + 2 * r / 3 + 17 / 81

private noncomputable def l4j_Pd (r : ℝ) : ℝ :=
  -10 * r ^ 5 / 27 + 58 * r ^ 4 / 27 + 10 * r ^ 3 / 9 - 14 * r ^ 2 / 27 + 80 * r / 27 - 1 / 3

private noncomputable def l4j_Pt (r : ℝ) : ℝ :=
  -2 * r ^ 5 / 9 + 4 * r ^ 4 / 3 + 2 * r ^ 3 / 9 + 8 * r ^ 2 / 9 + 4 * r / 3 + 4 / 9

private lemma l4j_rScale_pos : 0 < rScale := one_pos.trans rScale_spec.1

private lemma l4j_hP :
    1 - 5 * rScale - 7 * rScale ^ 2 - 5 * rScale ^ 3 - 7 * rScale ^ 4 - 5 * rScale ^ 5 +
      rScale ^ 6 = 0 := rScale_spec.2

private lemma l4j_xOut_rep :
    xOut 0 = √3 * l4j_Pp rScale ∧ xOut 1 = √3 * l4j_Pc rScale ∧ xOut 2 = l4j_Pd rScale := by
  obtain ⟨h0, h1, h2⟩ := l4j_xOut_rat
  have hr := l4j_rScale_pos
  have hP := l4j_hP
  have hs := l4j_sqrt3_sq
  set r := rScale
  refine ⟨?_, ?_, ?_⟩
  · rw [h0, div_eq_iff (by positivity), l4j_Pp]
    linear_combination (-2 * r ^ 6 / 9 + 10 * r ^ 5 / 9 + 14 * r ^ 4 / 9 + 10 * r ^ 3 / 9
      + 14 * r ^ 2 / 9 + 7 * r / 9 + 1 / 9) * hs + (-2 / 3) * hP
  · rw [h1, ← neg_div, div_eq_iff (by positivity), l4j_Pc]
    linear_combination (4 * r ^ 8 / 81 - 8 * r ^ 7 / 27 + 2 * r ^ 6 / 81 - 14 * r ^ 5 / 27
      - 26 * r ^ 4 / 27 - 5 * r ^ 3 / 27 - 46 * r ^ 2 / 81 - 2 * r / 3 - 17 / 81) * hs
      + (4 * r ^ 2 / 27 - 4 * r / 27 + 10 / 27) * hP
  · rw [h2, div_eq_iff (by positivity), l4j_Pd]
    linear_combination (10 * r ^ 3 / 9 + 2 * r ^ 2 / 9 - 8 * r / 9 + 2) * hP

private lemma l4j_t0_rep : l4j_t0 = √3 * l4j_Pt rScale := by
  have hr := l4j_rScale_pos
  have hP := l4j_hP
  have hs := l4j_sqrt3_sq
  rw [l4j_t0, div_eq_iff (by positivity), l4j_Pt]
  set r := rScale
  linear_combination (2 * r ^ 6 / 9 - 10 * r ^ 5 / 9 - 14 * r ^ 4 / 9 - 10 * r ^ 3 / 9
    - 20 * r ^ 2 / 9 - 16 * r / 9 - 4 / 9) * hs + (2 / 3) * hP

private lemma l4j_t0_pos : 0 < l4j_t0 := by
  have hr := l4j_rScale_pos
  unfold l4j_t0; positivity

/-- `x_out` is a fixed point of the map in the chart (Lemma 13.5.2: `F(qOutCart) =
ζ² (r_scale-scaling)(qOutCart)`, and `ζ · ζ² = 1`). -/
theorem chartMap_xOut : chartMap xOut = xOut := by
  have hr := l4j_rScale_pos
  have hζ : ζ • ζ ^ 2 • scale rScale qOutCart = scale rScale qOutCart := by
    rw [smul_smul, ← pow_succ', ζ_pow_three, one_smul]
  have h0 := qOutCart_normalization.1
  simp only [chartMap, l4j_chartCart_xOut, poincare_qOutCart, hζ]
  funext i
  fin_cases i <;> simp [scale, xOut, h0, ← Complex.ofReal_pow] <;> field_simp

/-- The sign conditions at `(x_out, t₀)`: `p > 0`, `d > 0`, and the two coefficients `B, C` of the
quotient of the switching function by `t - t₀` are negative (exact rational functions of
`r_scale`, signs from `6.27 < r_scale < 6.28`). -/
private lemma l4j_signs :
    0 < xOut 0 ∧ 0 < xOut 2 ∧ -√3 * l4j_t0 / 12 + (3 + √3 * xOut 0) / 4 < 0 ∧
      -√3 * l4j_t0 ^ 2 / 12 + (3 + √3 * xOut 0) * l4j_t0 / 4 + (√3 * xOut 2 - 3 * xOut 1) / 2 <
        0 := by
  obtain ⟨h0, h1, h2⟩ := l4j_xOut_rat
  obtain ⟨hr1, hr2⟩ := rScale_bounds
  have hr : 0 < rScale := l4j_rScale_pos
  have h3 : 0 < √3 := by positivity
  have hs := l4j_sqrt3_sq
  have ha : √3 * l4j_t0 = 2 * (1 + rScale + rScale ^ 2) / (rScale + 1) := by
    unfold l4j_t0; field_simp
  set r := rScale with hrdef
  have hr1' : 0 < 1 + r := by positivity
  have hr3' : 0 < 1 + r ^ 3 := by positivity
  have hr4' : 0 < 1 + r + r ^ 3 + r ^ 4 := by positivity
  have hrr : 0 < r ^ 2 - r + 1 := by nlinarith
  have hrr' : r ^ 2 - r + 1 ≠ 0 := hrr.ne'
  have hb : √3 * xOut 0 = (-1 + r) / (1 + r) := by rw [h0]; field_simp
  have hc : √3 * xOut 1 = -((-1 + r ^ 3) / (1 + r ^ 3)) := by rw [h1]; field_simp
  have hd : 0 < 1 - 3 * r - 2 * r ^ 2 - 3 * r ^ 3 + r ^ 4 := by
    nlinarith [mul_pos (pow_pos hr 3) (by linarith : (0 : ℝ) < r - 4)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h0]; exact div_pos (by linarith) (by positivity)
  · rw [h2]; exact div_pos hd (by positivity)
  · have e : -√3 * l4j_t0 / 12 + (3 + √3 * xOut 0) / 4 = -(r ^ 2 - 5 * r - 2) / (6 * (r + 1)) := by
      rw [show -√3 * l4j_t0 / 12 = -(√3 * l4j_t0) / 12 by ring, ha, hb]
      field_simp
      ring
    rw [e]
    exact div_neg_of_neg_of_pos (by nlinarith) (by positivity)
  · set C := -√3 * l4j_t0 ^ 2 / 12 + (3 + √3 * xOut 0) * l4j_t0 / 4 +
      (√3 * xOut 2 - 3 * xOut 1) / 2 with hC
    have e : √3 * C = -(√3 * l4j_t0) ^ 2 / 12 + (3 + √3 * xOut 0) * (√3 * l4j_t0) / 4 +
        (3 * xOut 2 - 3 * (√3 * xOut 1)) / 2 := by
      rw [hC]; linear_combination (xOut 2 / 2) * hs
    have key : √3 * C = -((r ^ 2 + r + 1) * (r ^ 4 - 6 * r ^ 3 - 2 * r ^ 2 + 3 * r + 1)) /
        (3 * (r + 1) ^ 2 * (r ^ 2 - r + 1)) := by
      rw [e, ha, hb, hc, h2]
      obtain ⟨q, hqdef, hq⟩ : ∃ q, r ^ 2 - r + 1 = q ∧ q ≠ 0 := ⟨_, rfl, hrr'⟩
      have e1 : 1 + r + r ^ 3 + r ^ 4 = (r + 1) ^ 2 * q := by rw [← hqdef]; ring
      have e2 : 1 + r ^ 3 = (r + 1) * q := by rw [← hqdef]; ring
      have e3 : 1 + r = r + 1 := by ring
      rw [e1, e2, e3, hqdef]
      have : r + 1 ≠ 0 := by positivity
      field_simp
      rw [← hqdef]
      ring
    have hq : 0 < r ^ 4 - 6 * r ^ 3 - 2 * r ^ 2 + 3 * r + 1 := by
      nlinarith [mul_pos (sub_pos.2 hr1) (sub_pos.2 hr2), mul_pos hr (sub_pos.2 hr1),
        mul_pos (mul_pos hr hr) (sub_pos.2 hr1)]
    have hneg : √3 * C < 0 := by
      rw [key]
      exact div_neg_of_neg_of_pos
        (by nlinarith [mul_pos (by positivity : (0 : ℝ) < r ^ 2 + r + 1) hq]) (by positivity)
    by_contra hcon
    exact (mul_nonneg h3.le (not_lt.mp hcon)).not_gt hneg

/-! ### The first switching time near `x_out`: the implicit function theorem -/

open ContinuousLinearMap in
/-- The linear form `(v, τ) ↦ a₀ v₀ + a₁ v₁ + a₂ v₂ + b τ` on `ℝ³ × ℝ`. -/
private noncomputable def l4j_lf (a₀ a₁ a₂ b : ℝ) : (Fin 3 → ℝ) × ℝ →L[ℝ] ℝ :=
  a₀ • (proj 0).comp (fst ℝ _ ℝ) + a₁ • (proj 1).comp (fst ℝ _ ℝ) +
    a₂ • (proj 2).comp (fst ℝ _ ℝ) + b • snd ℝ _ ℝ

private lemma l4j_lf_apply (a₀ a₁ a₂ b : ℝ) (w : (Fin 3 → ℝ) × ℝ) :
    l4j_lf a₀ a₁ a₂ b w = a₀ * w.1 0 + a₁ * w.1 1 + a₂ * w.1 2 + b * w.2 := by
  simp [l4j_lf]

private lemma l4j_hasFDerivAt_coord (i : Fin 3) (u : (Fin 3 → ℝ) × ℝ) :
    HasFDerivAt (fun u : (Fin 3 → ℝ) × ℝ ↦ u.1 i)
      ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ (Fin 3 → ℝ) ℝ)) u := by
  have := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 ↦ ℝ) i).comp
    (ContinuousLinearMap.fst ℝ (Fin 3 → ℝ) ℝ)).hasFDerivAt (x := u)
  exact this

private lemma l4j_hasFDerivAt_time (u : (Fin 3 → ℝ) × ℝ) :
    HasFDerivAt (fun u : (Fin 3 → ℝ) × ℝ ↦ u.2) (ContinuousLinearMap.snd ℝ (Fin 3 → ℝ) ℝ) u :=
  hasFDerivAt_snd

/-- `∂g/∂t`. -/
private noncomputable def l4j_gt (x : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  (√3 * x 2 - 3 * x 1) / 2 + t * (3 + √3 * x 0) / 2 - √3 * t ^ 2 / 4

/-- The derivative of the switching function `g(x, t)` on `ℝ³ × ℝ`. -/
private lemma l4j_hasFDerivAt_g (u : (Fin 3 → ℝ) × ℝ) :
    HasFDerivAt (fun u : (Fin 3 → ℝ) × ℝ ↦ l4j_g u.1 u.2)
      (l4j_lf (-3 * u.1 1 + √3 * u.2 ^ 2 / 4) (-3 * u.1 0 - 3 * u.2 / 2) (-3 + √3 * u.2 / 2)
        (l4j_gt u.1 u.2)) u := by
  have hX := fun i ↦ l4j_hasFDerivAt_coord i u
  have hT := l4j_hasFDerivAt_time u
  have h1 := (((hX 0).mul (hX 1)).add (hX 2)).const_mul (-3)
  have h2 := (hT.mul (((hX 2).const_mul √3).sub ((hX 1).const_mul 3))).mul_const (1 / 2)
  have h3 := ((hT.pow 2).mul (((hX 0).const_mul √3).const_add 3)).mul_const (1 / 4)
  have h4 := ((hT.pow 3).const_mul √3).mul_const (1 / 12)
  refine (((h1.add h2).add h3).sub h4).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun u ↦ by simp [l4j_g]; ring) |>.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun w ↦ ?_
  simp [l4j_lf_apply, l4j_gt]
  ring

private lemma l4j_contDiff_g : ContDiff ℝ 1 (fun u : (Fin 3 → ℝ) × ℝ ↦ l4j_g u.1 u.2) := by
  unfold l4j_g; fun_prop

/-- The base point `(x_out, t₀)` of the implicit function theorem. -/
private noncomputable def l4j_u0 : (Fin 3 → ℝ) × ℝ := (xOut, l4j_t0)

/-- The representative `∂g/∂t (x_out, t₀) = √3 Pg(r)` (`= -√3 r² d`). -/
private noncomputable def l4j_Pg (r : ℝ) : ℝ :=
  8 * r ^ 4 / 27 - 50 * r ^ 3 / 27 + r ^ 2 / 9 - 50 * r / 27 + 8 / 27

/-- The representative of `(∂g/∂t)⁻¹ = √3 Pκ(r)`. -/
private noncomputable def l4j_Pk (r : ℝ) : ℝ :=
  1975 * r ^ 5 / 153 - 9560 * r ^ 4 / 153 - 15350 * r ^ 3 / 153 - 12326 * r ^ 2 / 153 -
    15770 * r / 153 - 12362 / 153

private lemma l4j_gt0 : l4j_gt xOut l4j_t0 = √3 * l4j_Pg rScale := by
  obtain ⟨h0, h1, h2⟩ := l4j_xOut_rep
  have hP := l4j_hP
  have hs := l4j_sqrt3_sq
  rw [l4j_gt, h0, h1, h2, l4j_t0_rep, l4j_Pp, l4j_Pc, l4j_Pd, l4j_Pt, l4j_Pg]
  set r := rScale
  linear_combination (-r ^ 10 * √3 / 27 + 4 * r ^ 9 * √3 / 9 - 34 * r ^ 8 * √3 / 27
    - 4 * r ^ 7 * √3 / 27 - 13 * r ^ 6 * √3 / 9 - 65 * r ^ 5 * √3 / 27 - 44 * r ^ 4 * √3 / 27
    - 43 * r ^ 3 * √3 / 27 - 4 * r ^ 2 * √3 / 3 - 14 * r * √3 / 27 - 2 * √3 / 27) * hs
    + (-r ^ 4 * √3 / 9 + 7 * r ^ 3 * √3 / 9 - 2 * r ^ 2 * √3 / 3 + 10 * r * √3 / 9 - √3 / 3) * hP

private lemma l4j_gt0_inv : (l4j_gt xOut l4j_t0)⁻¹ = √3 * l4j_Pk rScale := by
  have hP := l4j_hP
  have hs := l4j_sqrt3_sq
  rw [l4j_gt0]
  apply inv_eq_of_mul_eq_one_right
  rw [l4j_Pg, l4j_Pk]
  set r := rScale
  linear_combination (15800 * r ^ 9 / 4131 - 6490 * r ^ 8 / 153 + 13375 * r ^ 7 / 153
    + 541462 * r ^ 6 / 4131 + 6130 * r ^ 5 / 27 + 8782 * r ^ 4 / 27 + 1064290 * r ^ 3 / 4131
    + 24178 * r ^ 2 / 153 + 18220 * r / 153 - 98896 / 4131) * hs + (15800 * r ^ 3 / 1377
    - 96230 * r ^ 2 / 1377 - 9425 * r / 1377 - 100273 / 1377) * hP

private lemma l4j_gt0_ne : l4j_gt xOut l4j_t0 ≠ 0 := by
  intro h
  have := l4j_gt0_inv
  rw [h, inv_zero] at this
  have h1 := congrArg (· * (√3 * l4j_Pg rScale)) this
  simp only [zero_mul] at h1
  rw [← l4j_gt0, h, mul_zero] at h1
  -- `0 = 0`: use the product identity instead
  have hP := l4j_hP
  have hs := l4j_sqrt3_sq
  have e : √3 * l4j_Pg rScale * (√3 * l4j_Pk rScale) = 1 := by
    rw [l4j_Pg, l4j_Pk]
    set r := rScale
    linear_combination (15800 * r ^ 9 / 4131 - 6490 * r ^ 8 / 153 + 13375 * r ^ 7 / 153
      + 541462 * r ^ 6 / 4131 + 6130 * r ^ 5 / 27 + 8782 * r ^ 4 / 27 + 1064290 * r ^ 3 / 4131
      + 24178 * r ^ 2 / 153 + 18220 * r / 153 - 98896 / 4131) * hs + (15800 * r ^ 3 / 1377
      - 96230 * r ^ 2 / 1377 - 9425 * r / 1377 - 100273 / 1377) * hP
  rw [← l4j_gt0, h, zero_mul] at e
  exact zero_ne_one e

private lemma l4j_g0 : l4j_g xOut l4j_t0 = 0 := by
  obtain ⟨h0, h1, h2⟩ := l4j_xOut_rep
  have hP := l4j_hP
  have hs := l4j_sqrt3_sq
  rw [l4j_g, h0, h1, h2, l4j_t0_rep, l4j_Pp, l4j_Pc, l4j_Pd, l4j_Pt]
  set r := rScale
  linear_combination (8 * r ^ 15 * √3 ^ 2 / 2187 + 8 * r ^ 15 / 729 - 16 * r ^ 14 * √3 ^ 2 / 243
    - 16 * r ^ 14 / 81 + 280 * r ^ 13 * √3 ^ 2 / 729 + 280 * r ^ 13 / 243
    - 512 * r ^ 12 * √3 ^ 2 / 729 - 512 * r ^ 12 / 243 + 62 * r ^ 11 * √3 ^ 2 / 729
    + 62 * r ^ 11 / 243 - 215 * r ^ 10 * √3 ^ 2 / 243 - 622 * r ^ 10 / 243
    - 4592 * r ^ 9 * √3 ^ 2 / 2187 - 5414 * r ^ 9 / 729 - 470 * r ^ 8 * √3 ^ 2 / 243
    - 218 * r ^ 8 / 81 - 674 * r ^ 7 * √3 ^ 2 / 243 - 608 * r ^ 7 / 81
    - 6923 * r ^ 6 * √3 ^ 2 / 2187 - 4862 * r ^ 6 / 729 - 196 * r ^ 5 * √3 ^ 2 / 81
    + 64 * r ^ 5 / 81 - 1324 * r ^ 4 * √3 ^ 2 / 729 - 274 * r ^ 4 / 243 - 908 * r ^ 3 * √3 ^ 2 / 729
    + 82 * r ^ 3 / 243 - 404 * r ^ 2 * √3 ^ 2 / 729 + 502 * r ^ 2 / 243 - 32 * r * √3 ^ 2 / 243
    + 172 * r / 243 - 28 * √3 ^ 2 / 2187 - 25 / 729) * hs + (8 * r ^ 9 / 243 - 104 * r ^ 8 / 243
    + 376 * r ^ 7 / 243 - 344 * r ^ 6 / 243 + 634 * r ^ 5 / 243 + 88 * r ^ 4 / 243
    - 152 * r ^ 3 / 243 + 640 * r ^ 2 / 243 - 554 * r / 243 + 218 / 243) * hP

private lemma l4j_R0_u0 : l4j_R0 xOut l4j_t0 = -rScale := by
  obtain ⟨h0, -, -⟩ := l4j_xOut_rep
  have hs := l4j_sqrt3_sq
  rw [l4j_R0, h0, l4j_t0_rep, l4j_Pp, l4j_Pt]
  set r := rScale
  linear_combination (-r / 3 - 1 / 6) * hs

private lemma l4j_fderiv_g : fderiv ℝ (fun u : (Fin 3 → ℝ) × ℝ ↦ l4j_g u.1 u.2) l4j_u0 =
    l4j_lf (-3 * xOut 1 + √3 * l4j_t0 ^ 2 / 4) (-3 * xOut 0 - 3 * l4j_t0 / 2)
      (-3 + √3 * l4j_t0 / 2) (l4j_gt xOut l4j_t0) :=
  (l4j_hasFDerivAt_g l4j_u0).fderiv

/-- The partial derivative in `t` and its inverse, as continuous linear maps `ℝ → ℝ`. -/
private lemma l4j_comp_inr_inverse :
    (fderiv ℝ (fun u : (Fin 3 → ℝ) × ℝ ↦ l4j_g u.1 u.2) l4j_u0 ∘L
        ContinuousLinearMap.inr ℝ (Fin 3 → ℝ) ℝ) ∘L
        ((l4j_gt xOut l4j_t0)⁻¹ • ContinuousLinearMap.id ℝ ℝ) = ContinuousLinearMap.id ℝ ℝ ∧
      ((l4j_gt xOut l4j_t0)⁻¹ • ContinuousLinearMap.id ℝ ℝ) ∘L
        (fderiv ℝ (fun u : (Fin 3 → ℝ) × ℝ ↦ l4j_g u.1 u.2) l4j_u0 ∘L
          ContinuousLinearMap.inr ℝ (Fin 3 → ℝ) ℝ) = ContinuousLinearMap.id ℝ ℝ := by
  have hne := l4j_gt0_ne
  rw [l4j_fderiv_g]
  constructor <;> refine ContinuousLinearMap.ext fun τ ↦ ?_ <;>
    simp [l4j_lf_apply] <;> field_simp

private lemma l4j_cdf :
    ContDiffAt ℝ 1 (fun u : (Fin 3 → ℝ) × ℝ ↦ l4j_g u.1 u.2) l4j_u0 :=
  l4j_contDiff_g.contDiffAt

private lemma l4j_isInvertible :
    (fderiv ℝ (fun u : (Fin 3 → ℝ) × ℝ ↦ l4j_g u.1 u.2) l4j_u0 ∘L
      ContinuousLinearMap.inr ℝ (Fin 3 → ℝ) ℝ).IsInvertible :=
  ContinuousLinearMap.IsInvertible.of_inverse l4j_comp_inr_inverse.1 l4j_comp_inr_inverse.2

/-- **The first switching time near `x_out`** (implicit function theorem): the root `ψ(x)` of
the switching function `g(x, ·)` near `t₀`, a `C¹` function of `x` with `ψ(x_out) = t₀`. -/
private noncomputable def l4j_ψ : (Fin 3 → ℝ) → ℝ :=
  ContDiffAt.implicitFunction l4j_cdf one_ne_zero l4j_isInvertible

private lemma l4j_ψ_xOut : l4j_ψ xOut = l4j_t0 :=
  ContDiffAt.implicitFunction_apply_self l4j_cdf one_ne_zero
    l4j_isInvertible

private lemma l4j_ψ_root : ∀ᶠ x in 𝓝 xOut, l4j_g x (l4j_ψ x) = 0 := by
  have := ContDiffAt.eventually_apply_implicitFunction l4j_cdf one_ne_zero l4j_isInvertible
  unfold l4j_ψ
  simpa [l4j_u0, l4j_g0] using this

private lemma l4j_ψ_contDiffAt : ContDiffAt ℝ 1 l4j_ψ xOut :=
  ContDiffAt.contDiffAt_implicitFunction l4j_cdf one_ne_zero
    l4j_isInvertible

/-- The derivative of `ψ` at `x_out`: `dψ = -(∂g/∂t)⁻¹ ∂g/∂x`. -/
private lemma l4j_ψ_hasFDerivAt :
    HasFDerivAt l4j_ψ (-(l4j_gt xOut l4j_t0)⁻¹ •
      (l4j_lf (-3 * xOut 1 + √3 * l4j_t0 ^ 2 / 4) (-3 * xOut 0 - 3 * l4j_t0 / 2)
        (-3 + √3 * l4j_t0 / 2) 0 ∘L ContinuousLinearMap.inl ℝ (Fin 3 → ℝ) ℝ)) xOut := by
  have h := (ContDiffAt.hasStrictFDerivAt_implicitFunction l4j_cdf one_ne_zero
    l4j_isInvertible).hasFDerivAt
  rw [ContinuousLinearMap.inverse_eq l4j_comp_inr_inverse.1 l4j_comp_inr_inverse.2,
    l4j_fderiv_g] at h
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v ↦ ?_)
  simp [l4j_lf_apply]

/-- **The local structure near `x_out`**: for `x` near `x_out`, the first control of
`chartCart x` is `ζ` and its first switching time is `ψ(x)`. -/
private lemma l4j_eventually_local : ∀ᶠ x in 𝓝 xOut,
    firstControl (chartCart x) = ζ ∧ firstSwitchTime (chartCart x) = l4j_ψ x := by
  obtain ⟨hp, hd, hB, hC⟩ := l4j_signs
  have hψc : ContinuousAt l4j_ψ xOut := l4j_ψ_contDiffAt.continuousAt
  have hc0 : ContinuousAt (fun x : Fin 3 → ℝ ↦ x 0) xOut := (continuous_apply 0).continuousAt
  have hc1 : ContinuousAt (fun x : Fin 3 → ℝ ↦ x 1) xOut := (continuous_apply 1).continuousAt
  have hc2 : ContinuousAt (fun x : Fin 3 → ℝ ↦ x 2) xOut := (continuous_apply 2).continuousAt
  have e1 : ∀ᶠ x in 𝓝 xOut, 0 < x 0 := hc0.eventually (lt_mem_nhds hp)
  have e2 : ∀ᶠ x in 𝓝 xOut, 0 < x 2 := hc2.eventually (lt_mem_nhds hd)
  have e3 : ∀ᶠ x in 𝓝 xOut, 0 < l4j_ψ x := hψc.eventually (lt_mem_nhds (l4j_ψ_xOut ▸ l4j_t0_pos))
  have e4 : ∀ᶠ x in 𝓝 xOut, -√3 * l4j_ψ x / 12 + (3 + √3 * x 0) / 4 < 0 := by
    have hcont : ContinuousAt (fun x : Fin 3 → ℝ ↦ -√3 * l4j_ψ x / 12 + (3 + √3 * x 0) / 4)
        xOut :=
      ((continuousAt_const.mul hψc).div_const 12).add
        ((continuousAt_const.add (continuousAt_const.mul hc0)).div_const 4)
    exact hcont.eventually (gt_mem_nhds (by beta_reduce; rw [l4j_ψ_xOut]; exact hB))
  have e5 : ∀ᶠ x in 𝓝 xOut, -√3 * l4j_ψ x ^ 2 / 12 + (3 + √3 * x 0) * l4j_ψ x / 4 +
      (√3 * x 2 - 3 * x 1) / 2 < 0 := by
    have hcont : ContinuousAt (fun x : Fin 3 → ℝ ↦ -√3 * l4j_ψ x ^ 2 / 12 +
        (3 + √3 * x 0) * l4j_ψ x / 4 + (√3 * x 2 - 3 * x 1) / 2) xOut :=
      (((continuousAt_const.mul (hψc.pow 2)).div_const 12).add
        (((continuousAt_const.add (continuousAt_const.mul hc0)).mul hψc).div_const 4)).add
        (((continuousAt_const.mul hc2).sub (continuousAt_const.mul hc1)).div_const 2)
    exact hcont.eventually (gt_mem_nhds (by beta_reduce; rw [l4j_ψ_xOut]; exact hC))
  filter_upwards [e1, e2, e3, e4, e5, l4j_ψ_root] with x h1 h2 h3 h4 h5 h6
  exact l4j_local h1 h2 h3 h6 h4 h5

private lemma l4j_chartMap_eventuallyEq : chartMap =ᶠ[𝓝 xOut] fun x ↦ l4j_N x (l4j_ψ x) := by
  filter_upwards [l4j_eventually_local] with x hx
  rw [l4j_chartMap_eq hx.1, hx.2]

/-! ### The map in the chart near `x_out`: smoothness and the derivative -/

private lemma l4j_R0_ne : l4j_R0 xOut (l4j_ψ xOut) ≠ 0 := by
  rw [l4j_ψ_xOut, l4j_R0_u0]; exact neg_ne_zero.mpr l4j_rScale_pos.ne'

private lemma l4j_contDiffAt_N : ContDiffAt ℝ 1 (fun x ↦ l4j_N x (l4j_ψ x)) xOut := by
  have hψ := l4j_ψ_contDiffAt
  have hR : 1 / 2 - √3 * (xOut 0 + l4j_ψ xOut) / 2 ≠ 0 := l4j_R0_ne
  rw [contDiffAt_pi]
  intro i
  fin_cases i <;>
    simp only [l4j_N, l4j_R0, l4j_I0, l4j_R1, l4j_I1, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val] <;>
    fun_prop (disch := assumption)

private lemma l4j_hasFDerivAt_R0 (u : (Fin 3 → ℝ) × ℝ) :
    HasFDerivAt (fun u : (Fin 3 → ℝ) × ℝ ↦ l4j_R0 u.1 u.2)
      (l4j_lf (-(√3 / 2)) 0 0 (-(√3 / 2))) u := by
  have hX := fun i ↦ l4j_hasFDerivAt_coord i u
  have hT := l4j_hasFDerivAt_time u
  refine ((hasFDerivAt_const (1 / 2 : ℝ) u).sub ((((hX 0).add hT).const_mul √3).mul_const
    (1 / 2))).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun u ↦ by simp [l4j_R0]; ring) |>.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun w ↦ ?_
  simp [l4j_lf_apply]
  ring

private lemma l4j_hasFDerivAt_I0 (u : (Fin 3 → ℝ) × ℝ) :
    HasFDerivAt (fun u : (Fin 3 → ℝ) × ℝ ↦ l4j_I0 u.1 u.2) (l4j_lf (-(1 / 2)) 0 0 (1 / 2)) u := by
  have hX := fun i ↦ l4j_hasFDerivAt_coord i u
  have hT := l4j_hasFDerivAt_time u
  refine (((hT.sub (hX 0)).sub_const √3).mul_const (1 / 2)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun u ↦ by simp [l4j_I0]; ring) |>.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun w ↦ ?_
  simp [l4j_lf_apply]
  ring

private lemma l4j_hasFDerivAt_R1 (u : (Fin 3 → ℝ) × ℝ) :
    HasFDerivAt (fun u : (Fin 3 → ℝ) × ℝ ↦ l4j_R1 u.1 u.2)
      (l4j_lf (-(√3 * u.2 / 2)) (-(1 / 2)) (-(√3 / 2))
        (1 / 2 - √3 * u.1 0 / 2 - √3 * u.2 / 2)) u := by
  have hX := fun i ↦ l4j_hasFDerivAt_coord i u
  have hT := l4j_hasFDerivAt_time u
  have a1 := ((hX 1).mul_const (-(1 / 2))).sub (((hX 2).const_mul √3).mul_const (1 / 2))
  have a2 := (a1.add (hT.mul_const (1 / 2))).sub
    ((((hX 0).const_mul √3).mul hT).mul_const (1 / 2))
  have a3 := a2.sub (((hT.pow 2).const_mul √3).mul_const (1 / 4))
  refine (a3.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun u ↦ by simp [l4j_R1]; ring)).congr_fderiv ?_
  refine ContinuousLinearMap.ext fun w ↦ ?_
  simp [l4j_lf_apply]
  ring

private lemma l4j_hasFDerivAt_I1 (u : (Fin 3 → ℝ) × ℝ) :
    HasFDerivAt (fun u : (Fin 3 → ℝ) × ℝ ↦ l4j_I1 u.1 u.2)
      (l4j_lf (-(u.2 / 2)) (√3 / 2) (-(1 / 2)) (-(u.1 0 / 2) - √3 / 2 + u.2 / 2)) u := by
  have hX := fun i ↦ l4j_hasFDerivAt_coord i u
  have hT := l4j_hasFDerivAt_time u
  have a1 := (((hX 1).const_mul √3).mul_const (1 / 2)).sub ((hX 2).mul_const (1 / 2))
  have a2 := (a1.sub (((hX 0).mul hT).mul_const (1 / 2))).sub
    ((hT.const_mul √3).mul_const (1 / 2))
  have a3 := a2.add ((hT.pow 2).mul_const (1 / 4))
  refine (a3.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun u ↦ by simp [l4j_I1]; ring)).congr_fderiv ?_
  refine ContinuousLinearMap.ext fun w ↦ ?_
  simp [l4j_lf_apply]
  ring

/-- The derivative of `x ↦ (x, ψ(x))` at `x_out`. -/
private lemma l4j_hasFDerivAt_pair :
    HasFDerivAt (fun x ↦ (x, l4j_ψ x)) ((ContinuousLinearMap.id ℝ (Fin 3 → ℝ)).prod
      (-(l4j_gt xOut l4j_t0)⁻¹ •
        (l4j_lf (-3 * xOut 1 + √3 * l4j_t0 ^ 2 / 4) (-3 * xOut 0 - 3 * l4j_t0 / 2)
          (-3 + √3 * l4j_t0 / 2) 0 ∘L ContinuousLinearMap.inl ℝ (Fin 3 → ℝ) ℝ))) xOut :=
  (hasFDerivAt_id xOut).prodMk l4j_ψ_hasFDerivAt

/-! #### The nine entries of the Jacobian (exact, in `ℚ(√3)[r]/(P)`) -/

private lemma l4j_Ri1 :
    (l4j_R0 xOut l4j_t0)⁻¹ =
      rScale ^ 5 - 5 * rScale ^ 4 - 7 * rScale ^ 3 - 5 * rScale ^ 2 - 7 * rScale - 5 := by
  have hP := l4j_hP
  have hs := l4j_sqrt3_sq
  rw [l4j_R0_u0]
  apply inv_eq_of_mul_eq_one_right
  set r := rScale
  linear_combination (-1) * hP

private lemma l4j_Ri2 :
    (l4j_R0 xOut l4j_t0)⁻¹ ^ 2 =
      -5 * rScale ^ 5 + 24 * rScale ^ 4 + 40 * rScale ^ 3 + 32 * rScale ^ 2 + 40 * rScale
      + 32 := by
  have hP := l4j_hP
  have hs := l4j_sqrt3_sq
  rw [l4j_Ri1]
  set r := rScale
  linear_combination (r ^ 4 - 5 * r ^ 3 - 7 * r ^ 2 - 5 * r - 7) * hP

private lemma l4j_Ri3 :
    (l4j_R0 xOut l4j_t0)⁻¹ ^ 3 =
      32 * rScale ^ 5 - 155 * rScale ^ 4 - 248 * rScale ^ 3 - 200 * rScale ^ 2 - 256 * rScale
      - 200 := by
  have hP := l4j_hP
  have hs := l4j_sqrt3_sq
  rw [l4j_Ri1]
  set r := rScale
  linear_combination (r ^ 9 - 10 * r ^ 8 + 11 * r ^ 7 + 60 * r ^ 6 + 85 * r ^ 5 + 130 * r ^ 4
    + 172 * r ^ 3 + 145 * r ^ 2 + 106 * r + 75) * hP

private lemma l4j_I0v :
    l4j_I0 xOut l4j_t0 =
      -2 * rScale ^ 5 * √3 / 9 + 4 * rScale ^ 4 * √3 / 3 + 2 * rScale ^ 3 * √3 / 9 + 8 *
      rScale ^ 2 * √3 / 9 + rScale * √3 - 2 * √3 / 9 := by
  have hP := l4j_hP
  have hs := l4j_sqrt3_sq
  obtain ⟨h0, h1, h2⟩ := l4j_xOut_rep
  rw [l4j_I0, h0, l4j_t0_rep, l4j_Pp, l4j_Pt]
  set r := rScale
  ring

private lemma l4j_R1v :
    l4j_R1 xOut l4j_t0 =
      -10 * rScale ^ 5 * √3 / 81 + 2 * rScale ^ 4 * √3 / 3 + 46 * rScale ^ 3 * √3 / 81 + 25 *
      rScale ^ 2 * √3 / 81 + 8 * rScale * √3 / 27 - 4 * √3 / 81 := by
  have hP := l4j_hP
  have hs := l4j_sqrt3_sq
  obtain ⟨h0, h1, h2⟩ := l4j_xOut_rep
  rw [l4j_R1, h0, h1, h2, l4j_t0_rep, l4j_Pp, l4j_Pc, l4j_Pd, l4j_Pt]
  set r := rScale
  linear_combination (r ^ 10 * √3 / 81 - 4 * r ^ 9 * √3 / 27 + 34 * r ^ 8 * √3 / 81 + 4 * r ^ 7 *
    √3 / 81 + 43 * r ^ 6 * √3 / 81 + 43 * r ^ 5 * √3 / 81 + 28 * r ^ 4 * √3 / 81 + 25 * r ^ 3 *
    √3 / 81 + 4 * r ^ 2 * √3 / 81 - 2 * r * √3 / 27 - 2 * √3 / 81) * hs + (r ^ 4 * √3 / 27 - 7 *
    r ^ 3 * √3 / 27 + 2 * r ^ 2 * √3 / 9 - 10 * r * √3 / 27 + 7 * √3 / 27) * hP

private lemma l4j_I1v :
    l4j_I1 xOut l4j_t0 =
      -8 * rScale ^ 4 / 27 + 50 * rScale ^ 3 / 27 - rScale ^ 2 / 9 + 50 * rScale / 27
      - 8 / 27 := by
  have hP := l4j_hP
  have hs := l4j_sqrt3_sq
  obtain ⟨h0, h1, h2⟩ := l4j_xOut_rep
  rw [l4j_I1, h0, h1, h2, l4j_t0_rep, l4j_Pp, l4j_Pc, l4j_Pd, l4j_Pt]
  set r := rScale
  linear_combination (r ^ 10 / 27 - 4 * r ^ 9 / 9 + 34 * r ^ 8 / 27 + 4 * r ^ 7 / 27 + 13 *
    r ^ 6 / 9 + 202 * r ^ 5 / 81 + 10 * r ^ 4 / 9 + 119 * r ^ 3 / 81 + 95 * r ^ 2 / 81 + 5 * r / 27
    - 7 / 162) * hs + (r ^ 4 / 9 - 7 * r ^ 3 / 9 + 2 * r ^ 2 / 3 - 10 * r / 9 + 1 / 3) * hP

private lemma l4j_tau0 :
    -((l4j_gt xOut l4j_t0)⁻¹ * (-(3 * xOut 1) + √3 * l4j_t0 ^ 2 / 4)) =
      25 * rScale ^ 5 - 2059 * rScale ^ 4 / 17 - 3296 * rScale ^ 3 / 17 - 2628 * rScale ^ 2 / 17
      - 3381 * rScale / 17 - 2654 / 17 := by
  have hP := l4j_hP
  have hs := l4j_sqrt3_sq
  obtain ⟨h0, h1, h2⟩ := l4j_xOut_rep
  rw [l4j_gt0_inv, h1, l4j_t0_rep, l4j_Pc, l4j_Pt, l4j_Pk]
  set r := rScale
  linear_combination (-1975 * r ^ 15 * √3 ^ 2 / 12393 - 1975 * r ^ 15 / 4131 + 33260 * r ^ 14 *
    √3 ^ 2 / 12393 + 33260 * r ^ 14 / 4131 - 166520 * r ^ 13 * √3 ^ 2 / 12393 - 166520 *
    r ^ 13 / 4131 + 48422 * r ^ 12 * √3 ^ 2 / 4131 + 48422 * r ^ 12 / 1377 + 354923 * r ^ 11 *
    √3 ^ 2 / 12393 + 354923 * r ^ 11 / 4131 + 507226 * r ^ 10 * √3 ^ 2 / 12393 + 166442 *
    r ^ 10 / 1377 + 1628950 * r ^ 9 * √3 ^ 2 / 12393 + 190510 * r ^ 9 / 459 + 3430 * r ^ 8 *
    √3 ^ 2 / 17 + 86240 * r ^ 8 / 153 + 306926 * r ^ 7 * √3 ^ 2 / 1377 + 2553208 * r ^ 7 / 4131
    + 3544786 * r ^ 6 * √3 ^ 2 / 12393 + 3009632 * r ^ 6 / 4131 + 3420244 * r ^ 5 * √3 ^ 2 / 12393
    + 1927099 * r ^ 5 / 4131 + 2510456 * r ^ 4 * √3 ^ 2 / 12393 + 228964 * r ^ 4 / 1377 + 11896 *
    r ^ 3 * √3 ^ 2 / 81 + 192838 * r ^ 3 / 4131 + 1070608 * r ^ 2 * √3 ^ 2 / 12393 - 559166 *
    r ^ 2 / 4131 + 359768 * r * √3 ^ 2 / 12393 - 575870 * r / 4131 + 49448 * √3 ^ 2 / 12393
    - 160706 / 4131) * hs + (-1975 * r ^ 9 / 1377 + 7795 * r ^ 8 / 459 - 21140 * r ^ 7 / 459
    - 18014 * r ^ 6 / 1377 - 8443 * r ^ 5 / 153 - 169987 * r ^ 4 / 1377 - 82364 * r ^ 3 / 1377
    - 119767 * r ^ 2 / 1377 - 10223 * r / 459 + 54268 / 1377) * hP

private lemma l4j_tau1 :
    -((l4j_gt xOut l4j_t0)⁻¹ * (-(3 * xOut 0) - 3 * l4j_t0 / 2)) =
      589 * rScale ^ 5 / 51 - 2854 * rScale ^ 4 / 51 - 4565 * rScale ^ 3 / 51 - 3652 *
      rScale ^ 2 / 51 - 4643 * rScale / 51 - 3676 / 51 := by
  have hP := l4j_hP
  have hs := l4j_sqrt3_sq
  obtain ⟨h0, h1, h2⟩ := l4j_xOut_rep
  rw [l4j_gt0_inv, h0, l4j_t0_rep, l4j_Pp, l4j_Pt, l4j_Pk]
  set r := rScale
  linear_combination (1975 * r ^ 10 / 459 - 21410 * r ^ 9 / 459 + 785 * r ^ 8 / 9 + 81434 *
    r ^ 7 / 459 + 111776 * r ^ 6 / 459 + 17551 * r ^ 5 / 51 + 129686 * r ^ 4 / 459 + 60092 *
    r ^ 3 / 459 + 12374 * r ^ 2 / 153 - 15770 * r / 459 - 12362 / 459) * hs + (1975 * r ^ 4 / 153
    - 3845 * r ^ 3 / 51 - 3815 * r ^ 2 / 153 - 2837 * r / 51 - 1334 / 153) * hP

private lemma l4j_tau2 :
    -((l4j_gt xOut l4j_t0)⁻¹ * (-3 + √3 * l4j_t0 / 2)) =
      1303 * rScale ^ 5 * √3 / 51 - 6308 * rScale ^ 4 * √3 / 51 - 10121 * rScale ^ 3 * √3 / 51
      - 8138 * rScale ^ 2 * √3 / 51 - 10403 * rScale * √3 / 51 - 8150 * √3 / 51 := by
  have hP := l4j_hP
  have hs := l4j_sqrt3_sq
  obtain ⟨h0, h1, h2⟩ := l4j_xOut_rep
  rw [l4j_gt0_inv, l4j_t0_rep, l4j_Pt, l4j_Pk]
  set r := rScale
  linear_combination (1975 * r ^ 10 * √3 / 1377 - 21410 * r ^ 9 * √3 / 1377 + 785 * r ^ 8 * √3 / 27
    + 81434 * r ^ 7 * √3 / 1377 + 5878 * r ^ 6 * √3 / 81 + 23266 * r ^ 5 * √3 / 153 + 250466 *
    r ^ 4 * √3 / 1377 + 10594 * r ^ 3 * √3 / 81 + 56240 * r ^ 2 * √3 / 459 + 105712 * r * √3 / 1377
    + 24724 * √3 / 1377) * hs + (1975 * r ^ 4 * √3 / 459 - 3845 * r ^ 3 * √3 / 153 - 3815 * r ^ 2 *
    √3 / 459 - 2837 * r * √3 / 153 - 13184 * √3 / 459) * hP

private lemma l4j_E00 :
    (l4j_R0 xOut l4j_t0)⁻¹ ^ 2 * l4j_I0 xOut l4j_t0 * (-(√3 / 2) + -(√3 / 2) *
      -((l4j_gt xOut l4j_t0)⁻¹ * (-(3 * xOut 1) + √3 * l4j_t0 ^ 2 / 4))) - (l4j_R0 xOut l4j_t0)⁻¹ *
      (-(1 / 2) + 1 / 2 * -((l4j_gt xOut l4j_t0)⁻¹ * (-(3 * xOut 1) + √3 *
      l4j_t0 ^ 2 / 4))) = jacobianOut rScale 0 0 := by
  have hP := l4j_hP
  have hs := l4j_sqrt3_sq
  rw [l4j_Ri2, l4j_Ri1, l4j_I0v, l4j_tau0]
  simp only [jacobianOut, Matrix.of_apply, Matrix.cons_val]
  set r := rScale
  linear_combination (-125 * r ^ 15 / 9 + 33245 * r ^ 14 / 153 - 136781 * r ^ 13 / 153 - 51103 *
    r ^ 12 / 153 + 1049935 * r ^ 11 / 306 + 2236349 * r ^ 10 / 306 + 820504 * r ^ 9 / 51
    + 4303061 * r ^ 8 / 153 + 9995527 * r ^ 7 / 306 + 3526883 * r ^ 6 / 102 + 1670899 * r ^ 5 / 51
    + 3363692 * r ^ 4 / 153 + 1881548 * r ^ 3 / 153 + 331780 * r ^ 2 / 51 + 3256 * r / 3
    - 9376 / 17) * hs + (-125 * r ^ 9 / 3 + 7540 * r ^ 8 / 17 - 756 * r ^ 7 - 32056 * r ^ 6 / 17
    - 255079 * r ^ 5 / 102 - 476803 * r ^ 4 / 102 - 252503 * r ^ 3 / 51 - 160574 * r ^ 2 / 51
    - 277811 * r / 102 - 122605 / 102) * hP

private lemma l4j_E10 :
    -2 * (l4j_R0 xOut l4j_t0)⁻¹ ^ 3 * l4j_R1 xOut l4j_t0 * (-(√3 / 2) + -(√3 / 2) *
      -((l4j_gt xOut l4j_t0)⁻¹ * (-(3 * xOut 1) + √3 * l4j_t0 ^ 2 / 4)))
      + (l4j_R0 xOut l4j_t0)⁻¹ ^ 2 * (-(√3 * l4j_t0 / 2) + (1 / 2 - √3 * xOut 0 / 2 - √3 *
      l4j_t0 / 2) * -((l4j_gt xOut l4j_t0)⁻¹ * (-(3 * xOut 1) + √3 *
      l4j_t0 ^ 2 / 4))) = jacobianOut rScale 1 0 := by
  have hP := l4j_hP
  have hs := l4j_sqrt3_sq
  obtain ⟨h0, -, -⟩ := l4j_xOut_rep
  rw [l4j_Ri3, l4j_Ri2, l4j_R1v, l4j_tau0, h0, l4j_t0_rep]
  simp only [jacobianOut, Matrix.of_apply, Matrix.cons_val, l4j_Pp, l4j_Pt]
  set r := rScale
  linear_combination (-8000 * r ^ 15 / 81 + 684010 * r ^ 14 / 459 - 7572332 * r ^ 13 / 1377
    - 8398516 * r ^ 12 / 1377 + 33905162 * r ^ 11 / 1377 + 61936427 * r ^ 10 / 918 + 356040535 *
    r ^ 9 / 2754 + 297128509 * r ^ 8 / 1377 + 119088976 * r ^ 7 / 459 + 695205131 * r ^ 6 / 2754
    + 33777557 * r ^ 5 / 153 + 208243976 * r ^ 4 / 1377 + 6312904 * r ^ 3 / 81 + 15923452 *
    r ^ 2 / 459 + 4132568 * r / 459 - 36032 / 51) * hs + (-8000 * r ^ 9 / 27 + 1372030 * r ^ 8 / 459
    - 1664182 * r ^ 7 / 459 - 7795216 * r ^ 6 / 459 - 400446 * r ^ 5 / 17 - 15147469 * r ^ 4 / 459
    - 5584631 * r ^ 3 / 153 - 11208037 * r ^ 2 / 459 - 6602819 * r / 459 - 2997613 / 459) * hP

private lemma l4j_E20 :
    -2 * (l4j_R0 xOut l4j_t0)⁻¹ ^ 3 * l4j_I1 xOut l4j_t0 * (-(√3 / 2) + -(√3 / 2) *
      -((l4j_gt xOut l4j_t0)⁻¹ * (-(3 * xOut 1) + √3 * l4j_t0 ^ 2 / 4)))
      + (l4j_R0 xOut l4j_t0)⁻¹ ^ 2 * (-(l4j_t0 / 2) + (-(xOut 0 / 2) - √3 / 2 + l4j_t0 / 2) *
      -((l4j_gt xOut l4j_t0)⁻¹ * (-(3 * xOut 1) + √3 *
      l4j_t0 ^ 2 / 4))) = jacobianOut rScale 2 0 := by
  have hP := l4j_hP
  have hs := l4j_sqrt3_sq
  obtain ⟨h0, -, -⟩ := l4j_xOut_rep
  rw [l4j_Ri3, l4j_Ri2, l4j_I1v, l4j_tau0, h0, l4j_t0_rep]
  simp only [jacobianOut, Matrix.of_apply, Matrix.cons_val, l4j_Pp, l4j_Pt]
  set r := rScale
  linear_combination (250 * r ^ 9 * √3 / 9 - 244520 * r ^ 8 * √3 / 459 + 1421440 * r ^ 7 * √3 / 459
    - 11302 * r ^ 6 * √3 / 3 - 3309494 * r ^ 5 * √3 / 459 - 5659831 * r ^ 4 * √3 / 459 - 8811169 *
    r ^ 3 * √3 / 459 - 7903661 * r ^ 2 * √3 / 459 - 1681825 * r * √3 / 153 - 3874897 * √3 / 459) *
    hP

private lemma l4j_E01 :
    (l4j_R0 xOut l4j_t0)⁻¹ ^ 2 * l4j_I0 xOut l4j_t0 * (0 + -(√3 / 2) * -((l4j_gt xOut l4j_t0)⁻¹ *
      (-(3 * xOut 0) - 3 * l4j_t0 / 2))) - (l4j_R0 xOut l4j_t0)⁻¹ * (0 + 1 / 2 *
      -((l4j_gt xOut l4j_t0)⁻¹ * (-(3 * xOut 0) - 3 * l4j_t0 / 2))) = jacobianOut rScale 0 1 := by
  have hP := l4j_hP
  have hs := l4j_sqrt3_sq
  rw [l4j_Ri2, l4j_Ri1, l4j_I0v, l4j_tau1]
  simp only [jacobianOut, Matrix.of_apply, Matrix.cons_val]
  set r := rScale
  linear_combination (-2945 * r ^ 15 / 459 + 46076 * r ^ 14 / 459 - 189602 * r ^ 13 / 459 - 23524 *
    r ^ 12 / 153 + 53823 * r ^ 11 / 34 + 517522 * r ^ 10 / 153 + 6815125 * r ^ 9 / 918 + 5958011 *
    r ^ 8 / 459 + 13846529 * r ^ 7 / 918 + 7319957 * r ^ 6 / 459 + 770908 * r ^ 5 / 51 + 1554176 *
    r ^ 4 / 153 + 867764 * r ^ 3 / 153 + 1380584 * r ^ 2 / 459 + 233728 * r / 459 - 117632 / 459) *
    hs + (-2945 * r ^ 9 / 153 + 31351 * r ^ 8 / 153 - 53462 * r ^ 7 / 153 - 133150 * r ^ 6 / 153
    - 20851 * r ^ 5 / 18 - 329113 * r ^ 4 / 153 - 700445 * r ^ 3 / 306 - 74048 * r ^ 2 / 51
    - 127873 * r / 102 - 85598 / 153) * hP

private lemma l4j_E11 :
    -2 * (l4j_R0 xOut l4j_t0)⁻¹ ^ 3 * l4j_R1 xOut l4j_t0 * (0 + -(√3 / 2) *
      -((l4j_gt xOut l4j_t0)⁻¹ * (-(3 * xOut 0) - 3 * l4j_t0 / 2))) + (l4j_R0 xOut l4j_t0)⁻¹ ^ 2 *
      (-(1 / 2) + (1 / 2 - √3 * xOut 0 / 2 - √3 * l4j_t0 / 2) * -((l4j_gt xOut l4j_t0)⁻¹ * (-(3 *
      xOut 0) - 3 * l4j_t0 / 2))) = jacobianOut rScale 1 1 := by
  have hP := l4j_hP
  have hs := l4j_sqrt3_sq
  obtain ⟨h0, -, -⟩ := l4j_xOut_rep
  rw [l4j_Ri3, l4j_Ri2, l4j_R1v, l4j_tau1, h0, l4j_t0_rep]
  simp only [jacobianOut, Matrix.of_apply, Matrix.cons_val, l4j_Pp, l4j_Pt]
  set r := rScale
  linear_combination (-188480 * r ^ 15 / 4131 + 2844022 * r ^ 14 / 4131 - 3498938 * r ^ 13 / 1377
    - 11624716 * r ^ 12 / 4131 + 46938082 * r ^ 11 / 4131 + 257812379 * r ^ 10 / 8262 + 82190119 *
    r ^ 9 / 1377 + 274195931 * r ^ 8 / 2754 + 29106718 * r ^ 7 / 243 + 35645473 * r ^ 6 / 306
    + 420793742 * r ^ 5 / 4131 + 288655568 * r ^ 4 / 4131 + 148789760 * r ^ 3 / 4131 + 3899380 *
    r ^ 2 / 243 + 17333056 * r / 4131 - 1352768 / 4131) * hs + (-188480 * r ^ 9 / 1377 + 633874 *
    r ^ 8 / 459 - 2308064 * r ^ 7 / 1377 - 3598694 * r ^ 6 / 459 - 5003342 * r ^ 5 / 459
    - 20927638 * r ^ 4 / 1377 - 23194802 * r ^ 3 / 1377 - 5178908 * r ^ 2 / 459 - 3044336 * r / 459
    - 4179560 / 1377) * hP

private lemma l4j_E21 :
    -2 * (l4j_R0 xOut l4j_t0)⁻¹ ^ 3 * l4j_I1 xOut l4j_t0 * (0 + -(√3 / 2) *
      -((l4j_gt xOut l4j_t0)⁻¹ * (-(3 * xOut 0) - 3 * l4j_t0 / 2))) + (l4j_R0 xOut l4j_t0)⁻¹ ^ 2 *
      (√3 / 2 + (-(xOut 0 / 2) - √3 / 2 + l4j_t0 / 2) * -((l4j_gt xOut l4j_t0)⁻¹ * (-(3 * xOut 0)
      - 3 * l4j_t0 / 2))) = jacobianOut rScale 2 1 := by
  have hP := l4j_hP
  have hs := l4j_sqrt3_sq
  obtain ⟨h0, -, -⟩ := l4j_xOut_rep
  rw [l4j_Ri3, l4j_Ri2, l4j_I1v, l4j_tau1, h0, l4j_t0_rep]
  simp only [jacobianOut, Matrix.of_apply, Matrix.cons_val, l4j_Pp, l4j_Pt]
  set r := rScale
  linear_combination (5890 * r ^ 9 * √3 / 459 - 338890 * r ^ 8 * √3 / 1377 + 1970236 * r ^ 7 *
    √3 / 1377 - 2398706 * r ^ 6 * √3 / 1377 - 4576756 * r ^ 5 * √3 / 1377 - 7877216 * r ^ 4 *
    √3 / 1377 - 4046798 * r ^ 3 * √3 / 459 - 11001676 * r ^ 2 * √3 / 1377 - 6934226 * r * √3 / 1377
    - 5408386 * √3 / 1377) * hP

private lemma l4j_E02 :
    (l4j_R0 xOut l4j_t0)⁻¹ ^ 2 * l4j_I0 xOut l4j_t0 * (0 + -(√3 / 2) * -((l4j_gt xOut l4j_t0)⁻¹ *
      (-3 + √3 * l4j_t0 / 2))) - (l4j_R0 xOut l4j_t0)⁻¹ * (0 + 1 / 2 * -((l4j_gt xOut l4j_t0)⁻¹ *
      (-3 + √3 * l4j_t0 / 2))) = jacobianOut rScale 0 2 := by
  have hP := l4j_hP
  have hs := l4j_sqrt3_sq
  rw [l4j_Ri2, l4j_Ri1, l4j_I0v, l4j_tau2]
  simp only [jacobianOut, Matrix.of_apply, Matrix.cons_val]
  set r := rScale
  linear_combination (-6515 * r ^ 15 * √3 / 459 + 101902 * r ^ 14 * √3 / 459 - 419024 * r ^ 13 *
    √3 / 459 - 157588 * r ^ 12 * √3 / 459 + 3211783 * r ^ 11 * √3 / 918 + 3436637 * r ^ 10 *
    √3 / 459 + 15131669 * r ^ 9 * √3 / 918 + 13234238 * r ^ 8 * √3 / 459 + 30789133 * r ^ 7 *
    √3 / 918 + 16301084 * r ^ 6 * √3 / 459 + 15448870 * r ^ 5 * √3 / 459 + 10381504 * r ^ 4 *
    √3 / 459 + 5806108 * r ^ 3 * √3 / 459 + 1023632 * r ^ 2 * √3 / 153 + 171568 * r * √3 / 153
    - 260800 * √3 / 459) * hs + (-6515 * r ^ 9 * √3 / 153 + 7703 * r ^ 8 * √3 / 17 - 117994 *
    r ^ 7 * √3 / 153 - 294844 * r ^ 6 * √3 / 153 - 262171 * r ^ 5 * √3 / 102 - 732764 * r ^ 4 *
    √3 / 153 - 91597 * r ^ 3 * √3 / 18 - 495917 * r ^ 2 * √3 / 153 - 856087 * r * √3 / 306
    - 189541 * √3 / 153) * hP

private lemma l4j_E12 :
    -2 * (l4j_R0 xOut l4j_t0)⁻¹ ^ 3 * l4j_R1 xOut l4j_t0 * (0 + -(√3 / 2) *
      -((l4j_gt xOut l4j_t0)⁻¹ * (-3 + √3 * l4j_t0 / 2))) + (l4j_R0 xOut l4j_t0)⁻¹ ^ 2 * (-(√3 / 2)
      + (1 / 2 - √3 * xOut 0 / 2 - √3 * l4j_t0 / 2) * -((l4j_gt xOut l4j_t0)⁻¹ * (-3 + √3 *
      l4j_t0 / 2))) = jacobianOut rScale 1 2 := by
  have hP := l4j_hP
  have hs := l4j_sqrt3_sq
  obtain ⟨h0, -, -⟩ := l4j_xOut_rep
  rw [l4j_Ri3, l4j_Ri2, l4j_R1v, l4j_tau2, h0, l4j_t0_rep]
  simp only [jacobianOut, Matrix.of_apply, Matrix.cons_val, l4j_Pp, l4j_Pt]
  set r := rScale
  linear_combination (-416960 * r ^ 15 * √3 / 4131 + 698866 * r ^ 14 * √3 / 459 - 23195558 *
    r ^ 13 * √3 / 4131 - 8598500 * r ^ 12 * √3 / 1377 + 11520410 * r ^ 11 * √3 / 459 + 570537529 *
    r ^ 10 * √3 / 8262 + 182452948 * r ^ 9 * √3 / 1377 + 35848127 * r ^ 8 * √3 / 162 + 1100443685 *
    r ^ 7 * √3 / 4131 + 126063691 * r ^ 6 * √3 / 486 + 104159243 * r ^ 5 * √3 / 459 + 642739600 *
    r ^ 4 * √3 / 4131 + 331386080 * r ^ 3 * √3 / 4131 + 49173052 * r ^ 2 * √3 / 1377 + 12796232 *
    r * √3 / 1377 - 2999200 * √3 / 4131) * hs + (-416960 * r ^ 9 * √3 / 1377 + 4204994 * r ^ 8 *
    √3 / 1377 - 1696436 * r ^ 7 * √3 / 459 - 23891882 * r ^ 6 * √3 / 1377 - 33294626 * r ^ 5 *
    √3 / 1377 - 15543958 * r ^ 4 * √3 / 459 - 17219194 * r ^ 3 * √3 / 459 - 34608632 * r ^ 2 *
    √3 / 1377 - 20367716 * r * √3 / 1377 - 9271192 * √3 / 1377) * hP

private lemma l4j_E22 :
    -2 * (l4j_R0 xOut l4j_t0)⁻¹ ^ 3 * l4j_I1 xOut l4j_t0 * (0 + -(√3 / 2) *
      -((l4j_gt xOut l4j_t0)⁻¹ * (-3 + √3 * l4j_t0 / 2))) + (l4j_R0 xOut l4j_t0)⁻¹ ^ 2 * (-(1 / 2)
      + (-(xOut 0 / 2) - √3 / 2 + l4j_t0 / 2) * -((l4j_gt xOut l4j_t0)⁻¹ * (-3 + √3 *
      l4j_t0 / 2))) = jacobianOut rScale 2 2 := by
  have hP := l4j_hP
  have hs := l4j_sqrt3_sq
  obtain ⟨h0, -, -⟩ := l4j_xOut_rep
  rw [l4j_Ri3, l4j_Ri2, l4j_I1v, l4j_tau2, h0, l4j_t0_rep]
  simp only [jacobianOut, Matrix.of_apply, Matrix.cons_val, l4j_Pp, l4j_Pt]
  set r := rScale
  linear_combination (13030 * r ^ 15 / 459 - 944980 * r ^ 14 / 1377 + 7829512 * r ^ 13 / 1377
    - 22016402 * r ^ 12 / 1377 - 10699870 * r ^ 11 / 1377 + 53537266 * r ^ 10 / 1377 + 43625132 *
    r ^ 9 / 459 + 33142802 * r ^ 8 / 153 + 161770394 * r ^ 7 / 459 + 539808220 * r ^ 6 / 1377
    + 557563000 * r ^ 5 / 1377 + 26537536 * r ^ 4 / 81 + 9797264 * r ^ 3 / 51 + 137668480 *
    r ^ 2 / 1377 + 45075776 * r / 1377 - 11475200 / 1377) * hs + (13030 * r ^ 9 / 153 - 44090 *
    r ^ 8 / 27 + 4355492 * r ^ 7 / 459 - 5290202 * r ^ 6 / 459 - 10136456 * r ^ 5 / 459 - 1026484 *
    r ^ 4 / 27 - 27080242 * r ^ 3 / 459 - 24454292 * r ^ 2 / 459 - 15534806 * r / 459
    - 11990738 / 459) * hP

/-- The derivative of the first coordinate `-(Re w₁)⁻¹ Im w₁` of the map in the chart. -/
private lemma l4j_hasFDerivAt_N0 :
    HasFDerivAt (fun x ↦ l4j_N x (l4j_ψ x) 0)
      ((ContinuousLinearMap.proj 0).comp
        (Matrix.toLin' (jacobianOut rScale)).toContinuousLinearMap) xOut := by
  have hR := (l4j_hasFDerivAt_R0 (xOut, l4j_ψ xOut)).comp xOut l4j_hasFDerivAt_pair
  have hRi := (hasFDerivAt_inv l4j_R0_ne).comp xOut hR
  have hI := (l4j_hasFDerivAt_I0 (xOut, l4j_ψ xOut)).comp xOut l4j_hasFDerivAt_pair
  refine ((hRi.neg.mul hI).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun x ↦ ?_)).congr_fderiv ?_
  · simp [l4j_N]
  refine ContinuousLinearMap.ext fun v ↦ ?_
  simp [l4j_lf_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    l4j_ψ_xOut]
  linear_combination v 0 * l4j_E00 + v 1 * l4j_E01 + v 2 * l4j_E02

/-- The derivative of the second coordinate `(Re w₁)⁻² Re w₂` of the map in the chart. -/
private lemma l4j_hasFDerivAt_N1 :
    HasFDerivAt (fun x ↦ l4j_N x (l4j_ψ x) 1)
      ((ContinuousLinearMap.proj 1).comp
        (Matrix.toLin' (jacobianOut rScale)).toContinuousLinearMap) xOut := by
  have hR := (l4j_hasFDerivAt_R0 (xOut, l4j_ψ xOut)).comp xOut l4j_hasFDerivAt_pair
  have hRi := (hasFDerivAt_inv l4j_R0_ne).comp xOut hR
  have hR1 := (l4j_hasFDerivAt_R1 (xOut, l4j_ψ xOut)).comp xOut l4j_hasFDerivAt_pair
  refine (((hRi.neg.pow 2).mul hR1).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun x ↦ ?_)).congr_fderiv ?_
  · simp [l4j_N]
  refine ContinuousLinearMap.ext fun v ↦ ?_
  simp [l4j_lf_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    l4j_ψ_xOut]
  linear_combination v 0 * l4j_E10 + v 1 * l4j_E11 + v 2 * l4j_E12

/-- The derivative of the third coordinate `(Re w₁)⁻² Im w₂` of the map in the chart. -/
private lemma l4j_hasFDerivAt_N2 :
    HasFDerivAt (fun x ↦ l4j_N x (l4j_ψ x) 2)
      ((ContinuousLinearMap.proj 2).comp
        (Matrix.toLin' (jacobianOut rScale)).toContinuousLinearMap) xOut := by
  have hR := (l4j_hasFDerivAt_R0 (xOut, l4j_ψ xOut)).comp xOut l4j_hasFDerivAt_pair
  have hRi := (hasFDerivAt_inv l4j_R0_ne).comp xOut hR
  have hI1 := (l4j_hasFDerivAt_I1 (xOut, l4j_ψ xOut)).comp xOut l4j_hasFDerivAt_pair
  refine (((hRi.neg.pow 2).mul hI1).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun x ↦ ?_)).congr_fderiv ?_
  · simp [l4j_N]
  refine ContinuousLinearMap.ext fun v ↦ ?_
  simp [l4j_lf_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    l4j_ψ_xOut]
  linear_combination v 0 * l4j_E20 + v 1 * l4j_E21 + v 2 * l4j_E22

/-- **The exact derivative of the map in the chart at `x_out`.** -/
private lemma l4j_hasFDerivAt_N :
    HasFDerivAt (fun x ↦ l4j_N x (l4j_ψ x))
      (Matrix.toLin' (jacobianOut rScale)).toContinuousLinearMap xOut := by
  rw [hasFDerivAt_pi']
  intro i
  fin_cases i
  exacts [l4j_hasFDerivAt_N0, l4j_hasFDerivAt_N1, l4j_hasFDerivAt_N2]

/-! ### The image of `F` near `x_out` lies on the wall `𝒲₂ = ℝ_{≤0} ζ²` -/

/-- The real part of the rotated third coordinate `(ζ z(t))₃` along the chart. -/
private noncomputable def l4j_R2 (x : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  -(2 * (x 0 * x 1 + x 2) + x 1 * t - t ^ 2 / 2 + √3 * t ^ 3 / 12) / 2 -
    √3 * (x 2 * t + x 0 * t ^ 2 / 2 + t ^ 3 / 12) / 2

/-- `(ζ z(t))₃ = R₂ - i g/√3`: on the zero set of the switching function from `ζ` to `1`, the
point `ζ z(t)₃` is real. -/
private lemma l4j_flow_chartCart_two (x : Fin 3 → ℝ) (t : ℝ) :
    (ζ * flow t (chartCart x) ζ 2).re = l4j_R2 x t ∧
      √3 * (ζ * flow t (chartCart x) ζ 2).im = -l4j_g x t := by
  have h3 := l4j_sqrt3_sq
  simp only [flow, chartCart, Matrix.cons_val, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.div_re,
    Complex.div_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    ζ_re, ζ_im, l4j_R2, l4j_g, ← Complex.ofReal_pow]
  norm_num
  constructor
  · ring
  · linear_combination (x 1 * x 0 + x 1 * t / 2 + x 2 + √3 * t ^ 3 / 24 - t ^ 2 / 4) * h3

/-- At `x_out`, the first control is `ζ`, the first switching time is `t₀`, and
`F(qOutCart) = z(t₀, qOutCart, ζ)`. -/
private lemma l4j_poincare_chartCart_eventually : ∀ᶠ x in 𝓝 xOut,
    poincare (chartCart x) = flow (l4j_ψ x) (chartCart x) ζ := by
  filter_upwards [l4j_eventually_local] with x hx
  rw [poincare, hx.1, hx.2]

private lemma l4j_R2_u0 : l4j_R2 xOut (l4j_ψ xOut) < 0 := by
  have hP : poincare (chartCart xOut) = flow (l4j_ψ xOut) (chartCart xOut) ζ :=
    l4j_poincare_chartCart_eventually.self_of_nhds
  rw [← (l4j_flow_chartCart_two xOut (l4j_ψ xOut)).1, ← hP, l4j_chartCart_xOut,
    poincare_qOutCart]
  have h3 : ζ * (ζ ^ 2 * ((rScale : ℂ) ^ 3 * qOutCart 2)) = (rScale : ℂ) ^ 3 * qOutCart 2 := by
    rw [← mul_assoc, ← pow_succ', ζ_pow_three, one_mul]
  simp only [scale, Pi.smul_apply, smul_eq_mul, Matrix.cons_val, h3]
  rw [← Complex.ofReal_pow, Complex.re_ofReal_mul]
  exact mul_neg_of_pos_of_neg (pow_pos l4j_rScale_pos 3) qOutCart_normalization.2.2

private lemma l4j_eventually_wall : ∀ᶠ x in 𝓝 xOut,
    poincare (chartCart x) = flow (l4j_ψ x) (chartCart x) ζ ∧ l4j_g x (l4j_ψ x) = 0 ∧
      l4j_R2 x (l4j_ψ x) < 0 := by
  have hψ := l4j_ψ_contDiffAt
  have hc : ContDiffAt ℝ 1 (fun x ↦ l4j_R2 x (l4j_ψ x)) xOut := by
    unfold l4j_R2; fun_prop
  filter_upwards [l4j_poincare_chartCart_eventually, l4j_ψ_root,
    hc.continuousAt.eventually (gt_mem_nhds l4j_R2_u0)] with x h1 h2 h3
  exact ⟨h1, h2, h3⟩

/-- If `ζ w₃ = a` is real and negative, the rotation factor `-w̄₃/|w₃|` of `chartOf` is `ζ`. -/
private lemma l4j_rotation_eq {w : ℂ} {a : ℝ} (hw : ζ * w = a) (ha : a < 0) :
    -starRingEnd ℂ w / (‖w‖ : ℂ) = ζ := by
  have hw2 : w = ζ ^ 2 * a := by
    rw [← hw, ← mul_assoc, ← pow_succ, ζ_pow_three, one_mul]
  have hn : ‖w‖ = -a := by
    rw [hw2, norm_mul, norm_pow, norm_ζ, one_pow, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_neg ha]
  have hne : ((-a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (neg_pos.mpr ha).ne'
  rw [hn, div_eq_iff hne, hw2, map_mul, conj_ζ_sq, Complex.conj_ofReal]
  push_cast
  ring

/-! ### Smoothness of the normalization map `chartOf` -/

section ChartOfSmooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : WithTop ℕ∞}

private lemma l4j_cd_re {f : E → ℂ} {x : E} (hf : ContDiffAt ℝ n f x) :
    ContDiffAt ℝ n (fun x ↦ (f x).re) x :=
  Complex.reCLM.contDiff.contDiffAt.comp x hf

private lemma l4j_cd_im {f : E → ℂ} {x : E} (hf : ContDiffAt ℝ n f x) :
    ContDiffAt ℝ n (fun x ↦ (f x).im) x :=
  Complex.imCLM.contDiff.contDiffAt.comp x hf

private lemma l4j_cd_conj {f : E → ℂ} {x : E} (hf : ContDiffAt ℝ n f x) :
    ContDiffAt ℝ n (fun x ↦ starRingEnd ℂ (f x)) x :=
  Complex.conjCLE.contDiff.contDiffAt.comp x hf

private lemma l4j_cd_norm {f : E → ℂ} {x : E} (hf : ContDiffAt ℝ n f x) (h : f x ≠ 0) :
    ContDiffAt ℝ n (fun x ↦ ‖f x‖) x :=
  (contDiffAt_norm ℝ h).comp x hf

end ChartOfSmooth

attribute [local fun_prop] l4j_cd_re l4j_cd_im l4j_cd_conj l4j_cd_norm

/-- The rotation factor `ω = -z̄₃/|z₃|` of `chartOf`, written with a real scalar. -/
private noncomputable def l4j_ω (z : Fin 3 → ℂ) : ℂ := (‖z 2‖⁻¹ : ℝ) • -starRingEnd ℂ (z 2)

private lemma l4j_chartOf_eq (z : Fin 3 → ℂ) :
    chartOf z = ![-((l4j_ω z * z 0).re)⁻¹ * (l4j_ω z * z 0).im,
      (-((l4j_ω z * z 0).re)⁻¹) ^ 2 * (l4j_ω z * z 1).re,
      (-((l4j_ω z * z 0).re)⁻¹) ^ 2 * (l4j_ω z * z 1).im] := by
  have h : -starRingEnd ℂ (z 2) / (‖z 2‖ : ℂ) = l4j_ω z := by
    rw [l4j_ω, Complex.real_smul, Complex.ofReal_inv, div_eq_inv_mul]
  simp only [chartOf, h, Pi.smul_apply, smul_eq_mul]

private lemma l4j_contDiffAt_chartOf_of {z : Fin 3 → ℂ} (h2 : z 2 ≠ 0)
    (h0 : (l4j_ω z * z 0).re ≠ 0) : ContDiffAt ℝ ∞ chartOf z := by
  have hn : ‖z 2‖ ≠ 0 := norm_ne_zero_iff.mpr h2
  simp only [l4j_ω] at h0
  have hc : ContDiffAt ℝ ∞ (fun z : Fin 3 → ℂ ↦ ![-((l4j_ω z * z 0).re)⁻¹ * (l4j_ω z * z 0).im,
      (-((l4j_ω z * z 0).re)⁻¹) ^ 2 * (l4j_ω z * z 1).re,
      (-((l4j_ω z * z 0).re)⁻¹) ^ 2 * (l4j_ω z * z 1).im]) z := by
    rw [contDiffAt_pi]
    intro i
    fin_cases i <;>
      simp only [l4j_ω, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val] <;>
      fun_prop (disch := assumption)
  exact hc.congr_of_eventuallyEq (Filter.Eventually.of_forall l4j_chartOf_eq)

/-! ### The chart of `Ξ_{𝒲,0}/V_T` near `q_out` -/

/-- `chartOf` is invariant under multiplication by a unit complex number. -/
private lemma l4j_chartOf_smul {v : ℂ} (hv : ‖v‖ = 1) (z : Fin 3 → ℂ) :
    chartOf (v • z) = chartOf z := by
  have hvv : starRingEnd ℂ v * v = 1 := by
    rw [Complex.conj_mul', hv]; simp
  have key : ∀ i, l4j_ω (v • z) * (v • z) i = l4j_ω z * z i := by
    intro i
    simp only [l4j_ω, Pi.smul_apply, smul_eq_mul, map_mul, norm_mul, hv, one_mul,
      Complex.real_smul]
    linear_combination (((‖z 2‖⁻¹ : ℝ) : ℂ) * -(starRingEnd ℂ (z 2)) * z i) * hvv
  rw [l4j_chartOf_eq, l4j_chartOf_eq, key 0, key 1]

/-- The rotation factor is invariant under the virial rescalings. -/
private lemma l4j_ω_scale {s : ℝ} (hs : 0 < s) (z : Fin 3 → ℂ) :
    l4j_ω (scale s z) = l4j_ω z := by
  have h2 : scale s z 2 = (s : ℂ) ^ 3 * z 2 := rfl
  simp only [l4j_ω, h2, Complex.real_smul, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hs, map_mul, map_pow, Complex.conj_ofReal]
  by_cases h : z 2 = 0
  · simp [h]
  · have : (‖z 2‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h
    have : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    push_cast
    field_simp

/-- `chartOf` is invariant under the virial rescalings. -/
private lemma l4j_chartOf_scale {s : ℝ} (hs : 0 < s) (z : Fin 3 → ℂ) :
    chartOf (scale s z) = chartOf z := by
  rw [l4j_chartOf_eq, l4j_chartOf_eq, l4j_ω_scale hs]
  have h0 : l4j_ω z * scale s z 0 = ((s : ℝ) : ℂ) * (l4j_ω z * z 0) := by
    simp only [scale, Matrix.cons_val]; ring
  have h1 : l4j_ω z * scale s z 1 = ((s ^ 2 : ℝ) : ℂ) * (l4j_ω z * z 1) := by
    simp only [scale, Matrix.cons_val]; push_cast; ring
  rw [h0, h1]
  simp only [Complex.re_ofReal_mul, Complex.im_ofReal_mul]
  by_cases h : (l4j_ω z * z 0).re = 0
  · simp [h]
  · have : s ≠ 0 := hs.ne'
    funext i
    fin_cases i <;> simp <;> field_simp

private lemma l4j_chartOf_ang {z : Fin 3 → ℂ} (hz : z ≠ 0) : chartOf (ang z) = chartOf z :=
  l4j_chartOf_scale (inv_pos.mpr (weightedNorm_pos hz)) z

/-- The rotation factor of a point with `z₃ ∈ ℝ_{<0}` is `1`. -/
private lemma l4j_ω_eq_one {z : Fin 3 → ℂ} (h2 : (z 2).im = 0) (h2' : (z 2).re < 0) :
    l4j_ω z = 1 := by
  have hq : z 2 = ((z 2).re : ℂ) := Complex.ext (by simp) (by simp [h2])
  have hnorm : ‖z 2‖ = -(z 2).re := by
    rw [hq, Complex.norm_real, Real.norm_eq_abs, abs_of_neg h2', Complex.ofReal_re]
  rw [l4j_ω, hnorm, hq, Complex.conj_ofReal, Complex.ofReal_re, Complex.real_smul]
  have : ((z 2).re : ℂ) ≠ 0 := by exact_mod_cast h2'.ne
  push_cast
  field_simp

/-- A normalized point (`Re z₁ = -1`, `z₃ ∈ ℝ_{<0}`) with `H_F⁺ = 0` is a chart point. -/
private lemma l4j_eq_chartCart {z : Fin 3 → ℂ} (h0 : (z 0).re = -1) (h2 : (z 2).im = 0)
    (h2' : (z 2).re < 0) (hH : hamMax z = 0) :
    z = chartCart ![(z 0).im, (z 1).re, (z 1).im] ∧ (z 0).im * (z 1).re + (z 1).im < 0 := by
  rw [l4j_hamMax_normalized h0 h2 h2'] at hH
  refine ⟨?_, by linarith⟩
  funext i
  fin_cases i
  · apply Complex.ext <;> simp [chartCart, h0]
  · apply Complex.ext <;> simp [chartCart]
  · apply Complex.ext <;> simp [chartCart, h2]
    linarith

/-- The angular part of a chart point lies in `Ξ_𝒲`, has `H_F⁺ = 0`, and has
`Re ξ₃ < 0`, `Re ξ₁ < 0`. -/
private lemma l4j_ang_chartCart {x : Fin 3 → ℝ} (hx : x 0 * x 1 + x 2 < 0) :
    ang (chartCart x) ∈ XiW ∧ hamMax (ang (chartCart x)) = 0 ∧
      (ang (chartCart x) 2).re < 0 ∧ (ang (chartCart x) 0).re < 0 := by
  have hz := l4j_chartCart_ne_zero x
  have hφ := weightedNorm_pos hz
  set φ := weightedNorm (chartCart x)
  have hang : ang (chartCart x) = scale φ⁻¹ (chartCart x) := rfl
  have hc0 : chartCart x 0 = -1 + (x 0 : ℂ) * I := rfl
  have hc2 : chartCart x 2 = ((2 * (x 0 * x 1 + x 2) : ℝ) : ℂ) := rfl
  have h2 : ang (chartCart x) 2 = ((φ⁻¹ ^ 3 * (2 * (x 0 * x 1 + x 2)) : ℝ) : ℂ) := by
    rw [hang]; simp only [scale, Matrix.cons_val]; rw [hc2]; push_cast; ring
  have h0 : (ang (chartCart x) 0).re = -φ⁻¹ := by
    rw [hang]; simp only [scale, Matrix.cons_val]; rw [hc0]; simp
  have hneg : φ⁻¹ ^ 3 * (2 * (x 0 * x 1 + x 2)) < 0 :=
    mul_neg_of_pos_of_neg (by positivity) (by linarith)
  have hH : hamMax (chartCart x) = 0 := by
    rw [l4j_hamMax_normalized (by simp [chartCart]) (by simp [chartCart])
      (by simp [chartCart]; linarith)]
    simp [chartCart]
  refine ⟨⟨ang_mem_Xi hz, Or.inl (Or.inl ⟨_, hneg.le, by rw [h2, pow_zero, mul_one]⟩)⟩,
    ?_, ?_, ?_⟩
  · have hv : (1 : ℂ) ∈ VT := mem_VT.mpr (Or.inl rfl)
    have := (hamMax_smul_scale_and_tau hv (inv_pos.mpr hφ) (chartCart x)).1
    rw [one_smul, hH, mul_zero] at this
    exact this
  · rw [h2, Complex.ofReal_re]; exact hneg
  · rw [h0]; exact neg_neg_of_pos (inv_pos.mpr hφ)

/-- The domain of the chart in `Ξ_𝒲`: `Re ξ₃ < 0` and `Re ξ₁ < 0` (then `ξ₃ ∈ ℝ_{<0}`). -/
private noncomputable def l4j_A : Set XiW :=
  {ξ | ((ξ : Fin 3 → ℂ) 2).re < 0 ∧ ((ξ : Fin 3 → ℂ) 0).re < 0}

private lemma l4j_isOpen_A : IsOpen l4j_A := by
  have h : IsOpen {z : Fin 3 → ℂ | (z 2).re < 0 ∧ (z 0).re < 0} :=
    (isOpen_lt (Complex.continuous_re.comp (continuous_apply 2)) continuous_const).inter
      (isOpen_lt (Complex.continuous_re.comp (continuous_apply 0)) continuous_const)
  exact h.preimage continuous_subtype_val

private lemma l4j_norm_root (g : rootsOfUnity 3 ℂ) : ‖((g : ℂˣ) : ℂ)‖ = 1 := by
  have h : ((g : ℂˣ) : ℂ) ∈ VT := (mem_VT_iff_exists_rootsOfUnity _).mpr ⟨g, rfl⟩
  exact norm_eq_one_of_mem_VT h

/-- The image in `Ξ_𝒲/V_T` of an open set of `Ξ_𝒲` is open (the quotient map by a group of
homeomorphisms is open). -/
private lemma l4j_isOpen_image_mk {A : Set XiW} (hA : IsOpen A) :
    IsOpen ((Quotient.mk'' : XiW → XiWQuot) '' A) := by
  have : ContinuousConstSMul (rootsOfUnity 3 ℂ) XiW :=
    ⟨fun g ↦ continuous_induced_rng.2 (by
      have e : (Subtype.val ∘ fun x : XiW ↦ g • x) =
          fun x : XiW ↦ ((g : ℂˣ) : ℂ) • (x : Fin 3 → ℂ) := rfl
      rw [e]
      exact (continuous_const_smul ((g : ℂˣ) : ℂ)).comp continuous_subtype_val)⟩
  exact isOpenMap_quotient_mk'_mul A hA

/-- The map in the chart is `C¹` (indeed `C^∞`) near `x_out`: near `x_out` the first control is `ζ`
and the first switching time is the simple root `ψ(x)` of `RR(ζ - 1, z₃(t))` near `t_sw(q_out)`,
`C¹` in `x` by the implicit function theorem (Mathlib's `ContDiffAt.implicitFunction`).

Proof: along `t ↦ z(t, chartCart x, ζ)` the switching function from `ζ` to `ζ²` is
`√3 t (d + pt/2 + t²/12) ≥ 0` (`p, d > 0` near `x_out`), and the one from `ζ` to `1` factors as
`(t - ψ(x)) k(t)` with `k` a quadratic whose coefficients are negative at `(x_out, t₀)`, hence near
it (`l4j_local`): `ζ` is optimal exactly on `[0, ψ(x)]` and `1` beats it right after. The explicit
factorization replaces the compactness argument; then `chartMap x = N(x, ψ(x))` with `N` an
explicit rational map whose denominator `Re (ζ z(t))₁ = -r_scale ≠ 0` at `(x_out, t₀)`. -/
theorem contDiffAt_chartMap : ContDiffAt ℝ 1 chartMap xOut :=
  l4j_contDiffAt_N.congr_of_eventuallyEq l4j_chartMap_eventuallyEq

/-- **The exact Jacobian at `q_out`**: the derivative of `chartMap` at `x_out` is the matrix
`jacobianOut r_scale` (implicit differentiation: `dt_sw = -(∂χ/∂x)/(∂χ/∂t)` at the simple root,
then the chain rule through the flow (13.2.2), the rotation and the rescaling; exact arithmetic in
`ℚ(√3)[r]` modulo `P(r)`). -/
theorem hasFDerivAt_chartMap :
    HasFDerivAt chartMap (Matrix.toLin' (jacobianOut rScale)).toContinuousLinearMap xOut :=
  l4j_hasFDerivAt_N.congr_of_eventuallyEq l4j_chartMap_eventuallyEq

/-! ### The normalization map, for Chapter 14 -/

/-- `chartOf` inverts `chartCart` on the chart's domain `{pc + d < 0}` (where the third coordinate
`2(pc + d)` of `chartCart x` is negative): `chartOf (chartCart x) = x`.

Proof route: `chartCart x` has `z₃ = 2(pc + d) ∈ ℝ_{<0}`, so the rotation factor is
`ω = -z₃/|z₃| = 1`; `Re z₁ = -1`, so the rescaling factor is `s = 1`; and
`(Im z₁, Re z₂, Im z₂) = (p, c, d)`. -/
theorem chartOf_chartCart {x : Fin 3 → ℝ} (hx : x 0 * x 1 + x 2 < 0) :
    chartOf (chartCart x) = x := by
  have hneg : 2 * (x 0 * x 1 + x 2) < 0 := by linarith
  have hn : ‖chartCart x 2‖ = -(2 * (x 0 * x 1 + x 2)) := by
    simp only [chartCart, Matrix.cons_val]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg hneg]
  have hω : -starRingEnd ℂ (chartCart x 2) / (‖chartCart x 2‖ : ℂ) = 1 := by
    rw [hn]
    have hne : ((-(2 * (x 0 * x 1 + x 2)) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (neg_pos.mpr hneg).ne'
    rw [div_eq_one_iff_eq hne]
    simp only [chartCart, Matrix.cons_val, Complex.conj_ofReal, Complex.ofReal_neg]
  simp only [chartOf, hω, one_smul]
  funext i
  fin_cases i <;> simp [chartCart]

/-- **The map in the chart is the normalized Poincaré map**: `chartMap = chartOf ∘ F ∘ chartCart`
near `x_out`.

Proof: `chartCart x_out = qOutCart` (`z₃ = 2(pc + d)` there because `H_F⁺(qOutCart) = 0`,
`hamMax_qOutCart`). Near `x_out` the first control of `chartCart x` is `ζ` and the trajectory
switches from `ζ` to `1` at the root `ψ(x)` of the switching function `RR(ζ - 1, z₃(t))` (the
argument of `contDiffAt_chartMap`), so `w = F(chartCart x)` has `Im (ζ w₃) = 0`
(`√3 Im (ζ z₃(t)) = -RR(ζ - 1, z₃(t))`): `w₃` lies on the line `ℝ ζ²`; and `Re (ζ w₃) < 0` by
continuity, since `ζ F(qOutCart)₃ = r_s³ (qOutCart)₃ < 0` (`poincare_qOutCart`,
`qOutCart_normalization`). For `w₃ = -aζ²` with `a > 0` the rotation factor of `chartOf` is
`-w̄₃/|w₃| = ζ`, the rotation of `chartMap`, and the rescalings and read-offs are the same
expressions. -/
theorem chartMap_eventuallyEq_chartOf :
    chartMap =ᶠ[𝓝 xOut] chartOf ∘ poincare ∘ chartCart := by
  filter_upwards [l4j_eventually_wall] with x ⟨hP, hg, hR⟩
  have hw : ζ * poincare (chartCart x) 2 = ((l4j_R2 x (l4j_ψ x) : ℝ) : ℂ) := by
    obtain ⟨h1, h2⟩ := l4j_flow_chartCart_two x (l4j_ψ x)
    rw [hg, neg_zero] at h2
    apply Complex.ext
    · rw [hP, h1, Complex.ofReal_re]
    · rw [hP, Complex.ofReal_im]
      exact (mul_eq_zero.mp h2).resolve_left (by positivity)
  have hω := l4j_rotation_eq hw hR
  simp only [Function.comp, chartOf, chartMap, hω]

/-- **`chartOf` is smooth near `qOutCart`**: it is `C^∞` at every point of a neighborhood of
`qOutCart` in `ℂ³` (as a real manifold `ℝ⁶`).

Proof route: `(qOutCart)₃ ∈ ℝ_{<0}` (`qOutCart_normalization`), so `z ↦ |z₃|` is smooth near
`qOutCart` (`z₃ ≠ 0`; `contDiffAt_norm` for the inner product space `ℂ`), hence so are
`ω = -z̄₃/|z₃|` and `w = ω z` (complex conjugation is `ℝ`-linear); at `qOutCart`, `ω = 1` and
`Re w₁ = -1 ≠ 0`, so `s = -1/Re w₁` and the three read-off coordinates are smooth near
`qOutCart`. -/
theorem eventually_contDiffAt_chartOf : ∀ᶠ z in 𝓝 qOutCart, ContDiffAt ℝ ∞ chartOf z := by
  obtain ⟨h0, h2, h2'⟩ := qOutCart_normalization
  have hq2 : qOutCart 2 ≠ 0 := fun h ↦ by rw [h] at h2'; simp at h2'
  have hn : ‖qOutCart 2‖ ≠ 0 := norm_ne_zero_iff.mpr hq2
  have hω : l4j_ω qOutCart = 1 := by
    have hq : qOutCart 2 = ((qOutCart 2).re : ℂ) := Complex.ext (by simp) (by simp [h2])
    have hnorm : ‖qOutCart 2‖ = -(qOutCart 2).re := by
      rw [hq, Complex.norm_real, Real.norm_eq_abs, abs_of_neg h2', Complex.ofReal_re]
    rw [l4j_ω, hnorm, hq, Complex.conj_ofReal, Complex.ofReal_re, Complex.real_smul]
    have : ((qOutCart 2).re : ℂ) ≠ 0 := by exact_mod_cast h2'.ne
    push_cast
    field_simp
  have hc : ContinuousAt (fun z : Fin 3 → ℂ ↦ (l4j_ω z * z 0).re) qOutCart := by
    have : ContDiffAt ℝ 1 (fun z : Fin 3 → ℂ ↦ (l4j_ω z * z 0).re) qOutCart := by
      simp only [l4j_ω]; fun_prop (disch := assumption)
    exact this.continuousAt
  filter_upwards [(continuous_apply 2).continuousAt.eventually_ne hq2,
    hc.eventually_ne (y := 0) (by rw [hω, one_mul, h0]; norm_num)] with z hz2 hz0
  exact l4j_contDiffAt_chartOf_of hz2 hz0

/-! ### The chart: construction -/

private lemma l4j_chartOf_orbitRel (ξ η : XiW)
    (h : MulAction.orbitRel (rootsOfUnity 3 ℂ) XiW ξ η) : chartOf ξ = chartOf η := by
  obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 h)
  change chartOf (((g : ℂˣ) : ℂ) • (η : Fin 3 → ℂ)) = chartOf η
  exact l4j_chartOf_smul (l4j_norm_root g) _

/-- `chartOf` on `Ξ_𝒲/V_T` (it is invariant under `V_T`). -/
private noncomputable def l4j_chartQuot : XiWQuot → (Fin 3 → ℝ) :=
  Quotient.lift (fun ξ : XiW ↦ chartOf ξ) l4j_chartOf_orbitRel

/-- The inverse of the chart, `x ↦ [ang (chartCart x)]` on `{pc + d < 0}` (junk value `q_out`
elsewhere). -/
private noncomputable def l4j_chartInv (x : Fin 3 → ℝ) : XiW0Quot :=
  open Classical in
  if hx : x 0 * x 1 + x 2 < 0 then
    ⟨Quotient.mk'' ⟨ang (chartCart x), (l4j_ang_chartCart hx).1⟩, (l4j_ang_chartCart hx).2.1⟩
  else qOut0

private lemma l4j_chartInv_val {x : Fin 3 → ℝ} (hx : x 0 * x 1 + x 2 < 0) :
    (l4j_chartInv x).1 = Quotient.mk'' ⟨ang (chartCart x), (l4j_ang_chartCart hx).1⟩ := by
  rw [l4j_chartInv, dite_eq_left hx]

/-- **The inverse on the domain**: a point `ξ` of `Ξ_𝒲` with `H_F⁺ = 0`, `Re ξ₃ < 0` and
`Re ξ₁ < 0` has `ξ₃ ∈ ℝ_{<0}`; its rescaling with `Re z₁ = -1` is the chart point
`chartCart (chartOf ξ)`, so `chartOf ξ` lies in `{pc + d < 0}` and `[ang (chartCart (chartOf ξ))]`
is the class of `ξ`. -/
private lemma l4j_chartInv_chartOf {ξ : XiW} (hξ : ξ ∈ l4j_A) (hH : hamMax (ξ : Fin 3 → ℂ) = 0) :
    chartOf ξ 0 * chartOf ξ 1 + chartOf ξ 2 < 0 ∧
      (l4j_chartInv (chartOf ξ)).1 = Quotient.mk'' ξ := by
  obtain ⟨h2', h0'⟩ := hξ
  have hmem : (ξ : Fin 3 → ℂ) ∈ Xi ∧ (ξ : Fin 3 → ℂ) 2 ∈ walls := ξ.2
  have h2 : ((ξ : Fin 3 → ℂ) 2).im = 0 := im_eq_zero_of_mem_walls hmem.2 h2'
  set s := -(((ξ : Fin 3 → ℂ) 0).re)⁻¹ with hs_def
  have hs : 0 < s := neg_pos.mpr (inv_lt_zero.mpr h0')
  have hz0 : (scale s (ξ : Fin 3 → ℂ) 0).re = -1 := by
    simp only [scale, Matrix.cons_val, Complex.re_ofReal_mul, hs_def]
    field_simp
    rw [div_self h0'.ne]
  have hz2 : (scale s (ξ : Fin 3 → ℂ) 2).im = 0 := by
    simp only [scale, Matrix.cons_val, ← Complex.ofReal_pow, Complex.im_ofReal_mul, h2, mul_zero]
  have hz2' : (scale s (ξ : Fin 3 → ℂ) 2).re < 0 := by
    simp only [scale, Matrix.cons_val, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
    exact mul_neg_of_pos_of_neg (pow_pos hs 3) h2'
  have hzH : hamMax (scale s (ξ : Fin 3 → ℂ)) = 0 := by
    have hv : (1 : ℂ) ∈ VT := mem_VT.mpr (Or.inl rfl)
    have := (hamMax_smul_scale_and_tau hv hs (ξ : Fin 3 → ℂ)).1
    rw [one_smul, hH, mul_zero] at this
    exact this
  obtain ⟨hzc, hneg⟩ := l4j_eq_chartCart hz0 hz2 hz2' hzH
  set x : Fin 3 → ℝ := ![(scale s (ξ : Fin 3 → ℂ) 0).im, (scale s (ξ : Fin 3 → ℂ) 1).re,
    (scale s (ξ : Fin 3 → ℂ) 1).im] with hx_def
  have hx : x 0 * x 1 + x 2 < 0 := hneg
  have hcx : chartOf ξ = x := by
    rw [← l4j_chartOf_scale hs, hzc, chartOf_chartCart hx]
  rw [hcx]
  refine ⟨hx, ?_⟩
  rw [l4j_chartInv_val hx]
  congr 1
  apply Subtype.ext
  change ang (chartCart x) = (ξ : Fin 3 → ℂ)
  rw [← hzc]
  exact (weightedNorm_ang_scale hs hmem.1).2

/-- The domain of the chart in `Ξ_{𝒲,0}/V_T`: the classes with a representative in `l4j_A`. -/
private noncomputable def l4j_source : Set XiW0Quot :=
  Subtype.val ⁻¹' ((Quotient.mk'' : XiW → XiWQuot) '' l4j_A)

private lemma l4j_hamMax_of_mk {ξ : XiW} {q : XiW0Quot} (h : Quotient.mk'' ξ = q.1) :
    hamMax (ξ : Fin 3 → ℂ) = 0 := by
  have := q.2
  rw [← h] at this
  exact this

private lemma l4j_continuousOn_chartOf_A : ContinuousOn (fun ξ : XiW ↦ chartOf ξ) l4j_A := by
  intro ξ hξ
  obtain ⟨h2', h0'⟩ := hξ
  have hmem : (ξ : Fin 3 → ℂ) ∈ Xi ∧ (ξ : Fin 3 → ℂ) 2 ∈ walls := ξ.2
  have h2 : ((ξ : Fin 3 → ℂ) 2).im = 0 := im_eq_zero_of_mem_walls hmem.2 h2'
  have hne : (ξ : Fin 3 → ℂ) 2 ≠ 0 := fun h ↦ by rw [h] at h2'; simp at h2'
  have h0 : (l4j_ω ξ * (ξ : Fin 3 → ℂ) 0).re ≠ 0 := by
    rw [l4j_ω_eq_one h2 h2', one_mul]; exact h0'.ne
  exact ((l4j_contDiffAt_chartOf_of hne h0).continuousAt.comp
    continuous_subtype_val.continuousAt).continuousWithinAt

private lemma l4j_continuousOn_chart :
    ContinuousOn (fun q : XiW0Quot ↦ l4j_chartQuot q.1) l4j_source := by
  rw [continuousOn_iff']
  intro t ht
  refine ⟨Subtype.val ⁻¹' ((Quotient.mk'' : XiW → XiWQuot) ''
    (l4j_A ∩ (fun ξ : XiW ↦ chartOf ξ) ⁻¹' t)), ?_, ?_⟩
  · exact (l4j_isOpen_image_mk (l4j_continuousOn_chartOf_A.isOpen_inter_preimage l4j_isOpen_A
      ht)).preimage continuous_subtype_val
  · ext q
    simp only [Set.mem_inter_iff, Set.mem_preimage, l4j_source, Set.mem_image]
    constructor
    · rintro ⟨hq, ξ, hξ, he⟩
      refine ⟨⟨ξ, ⟨hξ, ?_⟩, he⟩, ξ, hξ, he⟩
      rw [← he] at hq
      exact hq
    · rintro ⟨⟨ξ, ⟨hξ, hξt⟩, he⟩, hsrc⟩
      refine ⟨?_, hsrc⟩
      rw [← he]
      exact hξt

private lemma l4j_continuous_chartCart : Continuous chartCart := by
  refine continuous_pi fun i ↦ ?_
  fin_cases i <;> simp only [chartCart, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> fun_prop

private lemma l4j_continuousOn_chartInv :
    ContinuousOn l4j_chartInv {x : Fin 3 → ℝ | x 0 * x 1 + x 2 < 0} := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hf : ({x : Fin 3 → ℝ | x 0 * x 1 + x 2 < 0}.domRestrict l4j_chartInv) =
      fun x : {x : Fin 3 → ℝ | x 0 * x 1 + x 2 < 0} ↦ (⟨Quotient.mk''
        ⟨ang (chartCart x), (l4j_ang_chartCart x.2).1⟩, (l4j_ang_chartCart x.2).2.1⟩ :
          XiW0Quot) := by
    funext x
    exact Subtype.ext (l4j_chartInv_val x.2)
  rw [hf]
  refine Continuous.subtype_mk (continuous_quotient_mk'.comp (Continuous.subtype_mk ?_ _)) _
  exact continuousOn_ang.comp_continuous (l4j_continuous_chartCart.comp continuous_subtype_val)
    fun x ↦ l4j_chartCart_ne_zero x

/-- **The chart** of `Ξ_{𝒲,0}/V_T` near `q_out`. -/
private noncomputable def l4j_chart : OpenPartialHomeomorph XiW0Quot (Fin 3 → ℝ) where
  toFun q := l4j_chartQuot q.1
  invFun := l4j_chartInv
  source := l4j_source
  target := {x | x 0 * x 1 + x 2 < 0}
  map_source' := by
    rintro q ⟨ξ, hξ, he⟩
    rw [← he]
    exact (l4j_chartInv_chartOf hξ (l4j_hamMax_of_mk he)).1
  map_target' := by
    intro x hx
    exact ⟨⟨ang (chartCart x), (l4j_ang_chartCart hx).1⟩,
      ⟨(l4j_ang_chartCart hx).2.2.1, (l4j_ang_chartCart hx).2.2.2⟩, (l4j_chartInv_val hx).symm⟩
  left_inv' := by
    rintro q ⟨ξ, hξ, he⟩
    apply Subtype.ext
    rw [← he]
    exact (l4j_chartInv_chartOf hξ (l4j_hamMax_of_mk he)).2
  right_inv' := by
    intro x hx
    rw [l4j_chartInv_val hx]
    change chartOf (ang (chartCart x)) = x
    rw [l4j_chartOf_ang (l4j_chartCart_ne_zero x)]
    exact chartOf_chartCart hx
  open_source := (l4j_isOpen_image_mk l4j_isOpen_A).preimage continuous_subtype_val
  open_target := isOpen_lt (by fun_prop) continuous_const
  continuousOn_toFun := l4j_continuousOn_chart
  continuousOn_invFun := l4j_continuousOn_chartInv

private lemma l4j_chart_apply (q : XiW0Quot) : l4j_chart q = l4j_chartQuot q.1 := rfl

private lemma l4j_xOut_mem : xOut 0 * xOut 1 + xOut 2 < 0 := by
  have h := qOutCart_normalization.2.2
  rw [← l4j_chartCart_xOut] at h
  simp only [chartCart, Matrix.cons_val, Complex.ofReal_re] at h
  linarith

private lemma l4j_qOut0_mem : qOut0 ∈ l4j_chart.source := by
  have h := l4j_ang_chartCart l4j_xOut_mem
  rw [l4j_chartCart_xOut] at h
  exact ⟨⟨ang qOutCart, ang_qOutCart_mem_XiW.1⟩, ⟨h.2.2.1, h.2.2.2⟩, rfl⟩

private lemma l4j_chart_qOut0 : l4j_chart qOut0 = xOut := by
  rw [l4j_chart_apply]
  change chartOf (ang qOutCart) = xOut
  rw [← l4j_chartCart_xOut, l4j_chartOf_ang (l4j_chartCart_ne_zero xOut),
    chartOf_chartCart l4j_xOut_mem]

/-- The facts at `x = e(q)` used for the conjugacy, valid near `x_out`. -/
private lemma l4j_eventually_conj : ∀ᶠ x in 𝓝 xOut,
    x 0 * x 1 + x 2 < 0 ∧ chartMap x = chartOf (poincare (chartCart x)) ∧
      poincare (chartCart x) = flow (l4j_ψ x) (chartCart x) ζ ∧ l4j_R2 x (l4j_ψ x) < 0 ∧
      l4j_R0 x (l4j_ψ x) < 0 := by
  have ht : ∀ᶠ x in 𝓝 xOut, x 0 * x 1 + x 2 < 0 :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds l4j_xOut_mem
  have hψ := l4j_ψ_contDiffAt
  have hc : ContDiffAt ℝ 1 (fun x ↦ l4j_R0 x (l4j_ψ x)) xOut := by
    unfold l4j_R0; fun_prop
  have hR0 : l4j_R0 xOut (l4j_ψ xOut) < 0 := by
    rw [l4j_ψ_xOut, l4j_R0_u0]; exact neg_neg_of_pos l4j_rScale_pos
  filter_upwards [ht, chartMap_eventuallyEq_chartOf, l4j_eventually_wall,
    hc.continuousAt.eventually (gt_mem_nhds hR0)] with x h1 h2 h3 h4
  exact ⟨h1, h2, h3.1, h3.2.2, h4⟩


/-- **The chart** (TeX 11446–11447: "An open neighborhood of `q_out` in `Ξ_{𝒲,0}/V_T` is
diffeomorphic to an open subset of `ℝ³`"): an open partial homeomorphism `e` of `Ξ_{𝒲,0}/V_T`
into `ℝ³`, defined near `q_out`, with `e(q_out) = x_out`, whose inverse is
`x ↦ [ang (chartCart x)]`, and which conjugates `F_ang` to `chartMap` near `q_out`.

Proof: on `{pc + d < 0}`, `chartCart x` has `z₃ ∈ ℝ_{<0}` and `H_F⁺ = 0`, so
`x ↦ [ang (chartCart x)]` maps it into `Ξ_{𝒲,0}/V_T`. The chart is `chartOf` on the quotient (it is
invariant under `V_T` and the rescalings), with source the classes having a representative with
`Re ξ₃ < 0` and `Re ξ₁ < 0` (on the walls, `Re ξ₃ < 0` forces `ξ₃ ∈ ℝ_{<0}`), an open set since
the quotient map by `V_T` is open; there `chartOf` is continuous, and it rescales the representative
to `Re z₁ = -1`, which is `chartCart` of its image (`H_F⁺ = 0` gives `z₃ = 2(pc + d)`). For the
conjugacy, with `x = e(q)` near `x_out`, `[ang F(ang (chartCart x))] = [ang F(chartCart x)]`
(`ang_poincare_ang`); its rotation by `ζ` has `Re ξ₃ < 0` and `Re ξ₁ < 0` (by continuity from
`x_out`), and its image is `chartOf (F (chartCart x)) = chartMap x`
(`chartMap_eventuallyEq_chartOf`). -/
theorem exists_chart :
    ∃ e : OpenPartialHomeomorph XiW0Quot (Fin 3 → ℝ), qOut0 ∈ e.source ∧ e qOut0 = xOut ∧
      ∀ᶠ x in 𝓝 qOut0, poincareAngZero x ∈ e.source ∧ e (poincareAngZero x) = chartMap (e x) := by
  refine ⟨l4j_chart, l4j_qOut0_mem, l4j_chart_qOut0, ?_⟩
  have hcont : ContinuousAt l4j_chart qOut0 := l4j_chart.continuousAt l4j_qOut0_mem
  have hV : ∀ᶠ x in 𝓝 (l4j_chart qOut0), x 0 * x 1 + x 2 < 0 ∧
      chartMap x = chartOf (poincare (chartCart x)) ∧
      poincare (chartCart x) = flow (l4j_ψ x) (chartCart x) ζ ∧ l4j_R2 x (l4j_ψ x) < 0 ∧
      l4j_R0 x (l4j_ψ x) < 0 := by
    rw [l4j_chart_qOut0]; exact l4j_eventually_conj
  filter_upwards [hcont.tendsto.eventually hV, l4j_chart.open_source.mem_nhds l4j_qOut0_mem]
    with q ⟨hx, hcm, hP, hR2, hR0⟩ hsrc
  set x := l4j_chart q with hxdef
  have hz := l4j_chartCart_ne_zero x
  have hq1 : q.1 = Quotient.mk'' ⟨ang (chartCart x), (l4j_ang_chartCart hx).1⟩ := by
    have h := congrArg Subtype.val (l4j_chart.left_inv hsrc)
    rw [← h]
    exact l4j_chartInv_val hx
  set w := poincare (chartCart x) with hwdef
  have hw0 : w ≠ 0 := poincare_ne_zero hz
  have hmemW : ang w ∈ XiW := by
    have h := ang_poincare_mem_XiW (l4j_ang_chartCart hx).1
    rwa [ang_poincare_ang hz] at h
  have hP1 : (poincareAngZero q).1 = Quotient.mk'' (⟨ang w, hmemW⟩ : XiW) := by
    change poincareAngQuot q.1 = _
    rw [hq1]
    change Quotient.mk'' (poincareAng ⟨ang (chartCart x), _⟩) = _
    congr 1
    exact Subtype.ext (ang_poincare_ang hz)
  refine ⟨?_, ?_⟩
  · obtain ⟨g, hg⟩ := (mem_VT_iff_exists_rootsOfUnity ζ).mp (mem_VT.mpr (Or.inr (Or.inl rfl)))
    refine ⟨g • ⟨ang w, hmemW⟩, ?_, ?_⟩
    · have hval : ((g • (⟨ang w, hmemW⟩ : XiW) : XiW) : Fin 3 → ℂ) = ζ • ang w := by
        rw [← hg]; rfl
      have hφ := weightedNorm_pos hw0
      have h0' := (l4j_flow_chartCart x (l4j_ψ x)).1
      have h2' := (l4j_flow_chartCart_two x (l4j_ψ x)).1
      rw [← hP] at h0' h2'
      have e2 : (ζ • ang w) 2 = (((weightedNorm w)⁻¹ ^ 3 : ℝ) : ℂ) * (ζ * w 2) := by
        simp only [Pi.smul_apply, smul_eq_mul, ang, scale, Matrix.cons_val]; push_cast; ring
      have e0 : (ζ • ang w) 0 = (((weightedNorm w)⁻¹ : ℝ) : ℂ) * (ζ * w 0) := by
        simp only [Pi.smul_apply, smul_eq_mul, ang, scale, Matrix.cons_val]; ring
      change (((g • (⟨ang w, hmemW⟩ : XiW) : XiW) : Fin 3 → ℂ) 2).re < 0 ∧
        (((g • (⟨ang w, hmemW⟩ : XiW) : XiW) : Fin 3 → ℂ) 0).re < 0
      rw [hval, e2, e0, Complex.re_ofReal_mul, Complex.re_ofReal_mul, h2', h0']
      exact ⟨mul_neg_of_pos_of_neg (by positivity) hR2,
        mul_neg_of_pos_of_neg (by positivity) hR0⟩
    · rw [hP1]
      exact Quotient.sound' (MulAction.orbitRel_apply.2 (MulAction.mem_orbit _ _))
  · rw [l4j_chart_apply, hP1]
    change chartOf (ang w) = chartMap x
    rw [l4j_chartOf_ang hw0, hcm]


/-! ### The characteristic polynomial and the certified eigenvalue bound -/

/-- The characteristic polynomial of a `3 × 3` matrix: `λ³ - (tr A) λ² + M λ - det A`, with `M` the
sum of the principal `2 × 2` minors. -/
private lemma l4j_charpoly_fin_three {R : Type*} [CommRing R] (A : Matrix (Fin 3) (Fin 3) R) :
    A.charpoly = X ^ 3 - C (A 0 0 + A 1 1 + A 2 2) * X ^ 2 +
      C (A 0 0 * A 1 1 - A 0 1 * A 1 0 + (A 0 0 * A 2 2 - A 0 2 * A 2 0) +
        (A 1 1 * A 2 2 - A 1 2 * A 2 1)) * X -
      C (A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1 - A 0 1 * A 1 0 * A 2 2 +
        A 0 1 * A 1 2 * A 2 0 + A 0 2 * A 1 0 * A 2 1 - A 0 2 * A 1 1 * A 2 0) := by
  rw [Matrix.charpoly, Matrix.det_fin_three]
  simp only [Matrix.charmatrix_apply_eq, ne_eq, Fin.reduceEq, not_false_eq_true,
    Matrix.charmatrix_apply_ne, map_add, map_sub, map_mul]
  ring

/-- The trace of `jacobianOut r` is `jacTrace r` (an identity in `ℚ[r]`). -/
private lemma l4j_trace (r : ℝ) :
    jacobianOut r 0 0 + jacobianOut r 1 1 + jacobianOut r 2 2 = jacTrace r := by
  simp only [jacobianOut, jacTrace, Matrix.of_apply, Matrix.cons_val]
  ring

/-- The sum of the principal minors of `jacobianOut r` is `jacMinorSum r` modulo `P(r)`. -/
private lemma l4j_minorSum {r : ℝ} (hr : rScalePoly r = 0) :
    jacobianOut r 0 0 * jacobianOut r 1 1 - jacobianOut r 0 1 * jacobianOut r 1 0 +
        (jacobianOut r 0 0 * jacobianOut r 2 2 - jacobianOut r 0 2 * jacobianOut r 2 0) +
        (jacobianOut r 1 1 * jacobianOut r 2 2 - jacobianOut r 1 2 * jacobianOut r 2 1) =
      jacMinorSum r := by
  have hP : 1 - 5 * r - 7 * r ^ 2 - 5 * r ^ 3 - 7 * r ^ 4 - 5 * r ^ 5 + r ^ 6 = 0 := hr
  have hs : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [jacobianOut, jacMinorSum, Matrix.of_apply, Matrix.cons_val]
  linear_combination (-119898307 * r ^ 10 / 93636 + 284400202 * r ^ 9 / 23409
    - 3479194 * r ^ 8 / 459 - 114963364 * r ^ 7 / 1377 - 3495951586 * r ^ 6 / 23409
    - 193552303 * r ^ 5 / 867 - 7348211435 * r ^ 4 / 23409 - 6698421697 * r ^ 3 / 23409
    - 1581662503 * r ^ 2 / 7803 - 3352396231 * r / 23409 - 1429879472/23409) * hs
    + (-69522749 * r ^ 4 / 23409 + 314343931 * r ^ 3 / 23409 + 23919727 * r ^ 2 / 867
    + 625349003 * r / 23409 + 645233768/23409) * hP

/-- The determinant of `jacobianOut r` is `jacDet r` modulo `P(r)`. -/
private lemma l4j_det {r : ℝ} (hr : rScalePoly r = 0) :
    jacobianOut r 0 0 * jacobianOut r 1 1 * jacobianOut r 2 2 -
        jacobianOut r 0 0 * jacobianOut r 1 2 * jacobianOut r 2 1 -
        jacobianOut r 0 1 * jacobianOut r 1 0 * jacobianOut r 2 2 +
        jacobianOut r 0 1 * jacobianOut r 1 2 * jacobianOut r 2 0 +
        jacobianOut r 0 2 * jacobianOut r 1 0 * jacobianOut r 2 1 -
        jacobianOut r 0 2 * jacobianOut r 1 1 * jacobianOut r 2 0 =
      jacDet r := by
  have hP : 1 - 5 * r - 7 * r ^ 2 - 5 * r ^ 3 - 7 * r ^ 4 - 5 * r ^ 5 + r ^ 6 = 0 := hr
  have hs : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [jacobianOut, jacDet, Matrix.of_apply, Matrix.cons_val]
  linear_combination (-4634349910 * r ^ 15 / 397953 + 23784892433 * r ^ 14 / 132651
    - 373513597799 * r ^ 13 / 530604 - 1129646777705 * r ^ 12 / 2387718
    + 6717632574115 * r ^ 11 / 2387718 + 626720046871 * r ^ 10 / 88434
    + 34633288442267 * r ^ 9 / 2387718 + 61006384650805 * r ^ 8 / 2387718
    + 77058299858203 * r ^ 7 / 2387718 + 82691615160901 * r ^ 6 / 2387718
    + 40277597890676 * r ^ 5 / 1193859 + 31909984343864 * r ^ 4 / 1193859
    + 2274269691722 * r ^ 3 / 132651 + 1306281175342 * r ^ 2 / 132651 + 5152389116594 * r / 1193859
    + 1221738949312/1193859) * hs
    + (-363691970 * r ^ 9 / 70227 + 3486431408 * r ^ 8 / 70227 - 2626976687 * r ^ 7 / 70227
    - 22085429339 * r ^ 6 / 70227 - 42244344376 * r ^ 5 / 70227 - 66320420516 * r ^ 4 / 70227
    - 91183976852 * r ^ 3 / 70227 - 86547962752 * r ^ 2 / 70227 - 66301228580 * r / 70227
    - 15220850575/23409) * hP

/-- The characteristic polynomial of the Jacobian: `λ³ - T λ² + M λ - D` with
`T = jacTrace r_scale`, `M = jacMinorSum r_scale`, `D = jacDet r_scale` (polynomial identities in
`ℚ(√3)[r]` modulo `P(r)`, using `rScale_spec`). -/
theorem charpoly_jacobianOut :
    (jacobianOut rScale).charpoly =
      X ^ 3 - C (jacTrace rScale) * X ^ 2 + C (jacMinorSum rScale) * X - C (jacDet rScale) := by
  rw [l4j_charpoly_fin_three, l4j_trace, l4j_minorSum rScale_spec.2,
    l4j_det rScale_spec.2]

/-- The characteristic polynomial `χ(λ) = λ³ - T λ² + M λ - D` of the Jacobian, as a real
function. -/
private noncomputable def l4j_chi (l : ℝ) : ℝ :=
  l ^ 3 - jacTrace rScale * l ^ 2 + jacMinorSum rScale * l - jacDet rScale

/-- `r_scale` is within `10⁻¹⁸` of the continued-fraction convergent `3961388236/631380705`
(`rScale_fine_bounds`). -/
private lemma l4j_rScale_near : |rScale - 3961388236 / 631380705| ≤ 1 / 10 ^ 18 := by
  obtain ⟨h₁, h₂⟩ := rScale_fine_bounds
  rw [abs_le]
  constructor <;> norm_num at h₁ h₂ ⊢ <;> linarith

/-- A Taylor polynomial `d₀ + d₁ s + ⋯ + d₅ s⁵` with `d₁, …, d₅ ≥ 0` and `|s| ≤ ε ≤ 1` is within
`(d₁ + ⋯ + d₅) ε` of `d₀`. -/
private lemma l4j_taylor5 {s ε d₀ d₁ d₂ d₃ d₄ d₅ : ℝ} (hs : |s| ≤ ε) (hε : ε ≤ 1)
    (h₁ : 0 ≤ d₁) (h₂ : 0 ≤ d₂) (h₃ : 0 ≤ d₃) (h₄ : 0 ≤ d₄) (h₅ : 0 ≤ d₅) :
    d₀ - (d₁ + d₂ + d₃ + d₄ + d₅) * ε ≤
        d₀ + d₁ * s + d₂ * s ^ 2 + d₃ * s ^ 3 + d₄ * s ^ 4 + d₅ * s ^ 5 ∧
      d₀ + d₁ * s + d₂ * s ^ 2 + d₃ * s ^ 3 + d₄ * s ^ 4 + d₅ * s ^ 5 ≤
        d₀ + (d₁ + d₂ + d₃ + d₄ + d₅) * ε := by
  have hs1 : |s| ≤ 1 := hs.trans hε
  have hk : ∀ k : ℕ, k ≠ 0 → -ε ≤ s ^ k ∧ s ^ k ≤ ε := fun k hk ↦ abs_le.mp (by
    rw [abs_pow]; exact (pow_le_of_le_one (abs_nonneg s) hs1 hk).trans hs)
  obtain ⟨a₁, b₁⟩ := hk 1 one_ne_zero
  obtain ⟨a₂, b₂⟩ := hk 2 two_ne_zero
  obtain ⟨a₃, b₃⟩ := hk 3 three_ne_zero
  obtain ⟨a₄, b₄⟩ := hk 4 four_ne_zero
  obtain ⟨a₅, b₅⟩ := hk 5 (by norm_num)
  rw [pow_one] at a₁ b₁
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left a₁ h₁, mul_le_mul_of_nonneg_left a₂ h₂,
      mul_le_mul_of_nonneg_left a₃ h₃, mul_le_mul_of_nonneg_left a₄ h₄,
      mul_le_mul_of_nonneg_left a₅ h₅]
  · nlinarith [mul_le_mul_of_nonneg_left b₁ h₁, mul_le_mul_of_nonneg_left b₂ h₂,
      mul_le_mul_of_nonneg_left b₃ h₃, mul_le_mul_of_nonneg_left b₄ h₄,
      mul_le_mul_of_nonneg_left b₅ h₅]

private lemma l4j_taylor5_neg {s ε d₀ d₁ d₂ d₃ d₄ d₅ : ℝ} (hs : |s| ≤ ε) (hε : ε ≤ 1)
    (h₁ : 0 ≤ d₁) (h₂ : 0 ≤ d₂) (h₃ : 0 ≤ d₃) (h₄ : 0 ≤ d₄) (h₅ : 0 ≤ d₅)
    (h : d₀ + (d₁ + d₂ + d₃ + d₄ + d₅) * ε < 0) :
    d₀ + d₁ * s + d₂ * s ^ 2 + d₃ * s ^ 3 + d₄ * s ^ 4 + d₅ * s ^ 5 < 0 :=
  (l4j_taylor5 hs hε h₁ h₂ h₃ h₄ h₅).2.trans_lt h

private lemma l4j_taylor5_pos {s ε d₀ d₁ d₂ d₃ d₄ d₅ : ℝ} (hs : |s| ≤ ε) (hε : ε ≤ 1)
    (h₁ : 0 ≤ d₁) (h₂ : 0 ≤ d₂) (h₃ : 0 ≤ d₃) (h₄ : 0 ≤ d₄) (h₅ : 0 ≤ d₅)
    (h : 0 < d₀ - (d₁ + d₂ + d₃ + d₄ + d₅) * ε) :
    0 < d₀ + d₁ * s + d₂ * s ^ 2 + d₃ * s ^ 3 + d₄ * s ^ 4 + d₅ * s ^ 5 :=
  h.trans_le (l4j_taylor5 hs hε h₁ h₂ h₃ h₄ h₅).1

private lemma l4j_chi_neg_tenth : l4j_chi (-1 / 10) < 0 := by
  have key : l4j_chi (-1 / 10) = (-2749390791680471124295285874289667126257331 /
      14832269556997505767678806820367572589236875000 : ℝ)
      + (354273808162584787938080636139500228009422882 /
      587295012325309567690970490631621875 : ℝ) * (rScale - 3961388236 / 631380705)
      + (671570645958562018251469055576687689 /
      1860351473126850044272323750 : ℝ) * (rScale - 3961388236 / 631380705) ^ 2
      + (5636331038313412968003461 /
      69328972981964700 : ℝ) * (rScale - 3961388236 / 631380705) ^ 3
      + (19034813316729769 /
      2333363475 : ℝ) * (rScale - 3961388236 / 631380705) ^ 4
      + (522726221 /
      1700 : ℝ) * (rScale - 3961388236 / 631380705) ^ 5 := by
    unfold l4j_chi jacTrace jacMinorSum jacDet; ring
  rw [key]
  exact l4j_taylor5_neg l4j_rScale_near (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

private lemma l4j_chi_neg_twentieth : 0 < l4j_chi (-1 / 20) := by
  have key : l4j_chi (-1 / 20) = (57888369757532268147216225307581887667770593 /
      909712532829180353750966818315877785473195000000 : ℝ)
      + (7274825958543315902774060010107318285223028883 /
      12006920251984106717237618919579825000 : ℝ) * (rScale - 3961388236 / 631380705)
      + (20685523989644065188837027509138653859 /
      57050778509223401357684595000 : ℝ) * (rScale - 3961388236 / 631380705) ^ 2
      + (590269348083381756699315911 /
      7228700916252852720 : ℝ) * (rScale - 3961388236 / 631380705) ^ 3
      + (586304792335855899 /
      71556479900 : ℝ) * (rScale - 3961388236 / 631380705) ^ 4
      + (2100112341 /
      6800 : ℝ) * (rScale - 3961388236 / 631380705) ^ 5 := by
    unfold l4j_chi jacTrace jacMinorSum jacDet; ring
  rw [key]
  exact l4j_taylor5_pos l4j_rScale_near (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

private lemma l4j_chi_neg_thousandth : l4j_chi (-1 / 1000) < 0 := by
  have key : l4j_chi (-1 / 1000) = (-12531920151191488585642142869584937799179261637 /
      13645687992437705306264502274738166782097925000000000 : ℝ)
      + (164387332774083199486190868271638902021070612131197 /
      270155705669642401137846425690546062500000 : ℝ) * (rScale - 3961388236 / 631380705)
      + (155808452196516397878177828474311859408617 /
      427880838819175510182634462500000 : ℝ) * (rScale - 3961388236 / 631380705) ^ 2
      + (22230269247563556974421880034237 /
      271076284359481977000000 : ℝ) * (rScale - 3961388236 / 631380705) ^ 3
      + (4416191843992870612427 /
      536673599250000 : ℝ) * (rScale - 3961388236 / 631380705) ^ 4
      + (5272854165101 /
      17000000 : ℝ) * (rScale - 3961388236 / 631380705) ^ 5 := by
    unfold l4j_chi jacTrace jacMinorSum jacDet; ring
  rw [key]
  exact l4j_taylor5_neg l4j_rScale_near (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

private lemma l4j_chi_tenth : 0 < l4j_chi (1 / 10) := by
  have key : l4j_chi (1 / 10) = (219733834077616595488316270696173586155144919 /
      113714066603647544218870852289484723184149375000 : ℝ)
      + (921329898271986176868453215424704883065092129 /
      1500865031498013339654702364947478125 : ℝ) * (rScale - 3961388236 / 631380705)
      + (5239490773364384437539962605558047629 /
      14262694627305850339421148750 : ℝ) * (rScale - 3961388236 / 631380705) ^ 2
      + (747554379056400872539969141 /
      9035876145316065900 : ℝ) * (rScale - 3961388236 / 631380705) ^ 3
      + (148506683329220139 /
      17889119975 : ℝ) * (rScale - 3961388236 / 631380705) ^ 4
      + (531942981 /
      1700 : ℝ) * (rScale - 3961388236 / 631380705) ^ 5 := by
    unfold l4j_chi jacTrace jacMinorSum jacDet; ring
  rw [key]
  exact l4j_taylor5_pos l4j_rScale_near (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)


/-- A monic real cubic with three distinct real roots `a, b, c` has no other complex roots. -/
private lemma l4j_cubic_roots {T M D a b c : ℝ}
    (ha : a ^ 3 - T * a ^ 2 + M * a - D = 0) (hb : b ^ 3 - T * b ^ 2 + M * b - D = 0)
    (hc : c ^ 3 - T * c ^ 2 + M * c - D = 0) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {μ : ℂ}
    (hμ : μ ^ 3 - T * μ ^ 2 + M * μ - D = 0) : μ = a ∨ μ = b ∨ μ = c := by
  have hab' : a ^ 2 + a * b + b ^ 2 - T * (a + b) + M = 0 := by
    have h : (a - b) * (a ^ 2 + a * b + b ^ 2 - T * (a + b) + M) = 0 := by
      linear_combination ha - hb
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hab)
  have hac' : a ^ 2 + a * c + c ^ 2 - T * (a + c) + M = 0 := by
    have h : (a - c) * (a ^ 2 + a * c + c ^ 2 - T * (a + c) + M) = 0 := by
      linear_combination ha - hc
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hac)
  have hT : T = a + b + c := by
    have h : (b - c) * (a + b + c - T) = 0 := by linear_combination hab' - hac'
    linear_combination -((mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hbc))
  have hM : M = a * b + a * c + b * c := by linear_combination hab' + (a + b) * hT
  have hD : D = a * b * c := by linear_combination -ha + (-a ^ 2) * hT + a * hM
  have hT' : (T : ℂ) = a + b + c := by exact_mod_cast hT
  have hM' : (M : ℂ) = a * b + a * c + b * c := by exact_mod_cast hM
  have hD' : (D : ℂ) = a * b * c := by exact_mod_cast hD
  have h : (μ - a) * (μ - b) * (μ - c) = 0 := by
    linear_combination hμ + μ ^ 2 * hT' - μ * hM' + hD'
  rcases mul_eq_zero.mp h with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
  · exact Or.inr (Or.inr (sub_eq_zero.mp h))

/-- **The certified eigenvalue bound** ("Numerically, the three eigenvalues have absolute value
less than `0.1`", TeX 11450–11452): every complex root of the characteristic polynomial of the
Jacobian has modulus `< 1/10`. Certificate: `χ(-1/10) < 0 < χ(-1/20)` and
`χ(-1/1000) < 0 < χ(1/10)` (the signs of degree-5 polynomials in `r_scale`, from
`rScale_fine_bounds`), so the three roots are real and lie in `(-1/10, 1/10)`. -/
theorem norm_lt_of_aeval_charpoly_jacobianOut_eq_zero :
    ∀ μ : ℂ, aeval μ (jacobianOut rScale).charpoly = 0 → ‖μ‖ < 1 / 10 := by
  intro μ hμ
  rw [charpoly_jacobianOut] at hμ
  simp only [map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C, Complex.coe_algebraMap] at hμ
  have hcont : ContinuousOn l4j_chi univ := by
    unfold l4j_chi; fun_prop
  obtain ⟨x₁, ⟨h₁l, h₁r⟩, h₁⟩ : ∃ x ∈ Ioo (-1 / 10 : ℝ) (-1 / 20), l4j_chi x = 0 :=
    intermediate_value_Ioo (by norm_num) (hcont.mono (subset_univ _))
      ⟨l4j_chi_neg_tenth, l4j_chi_neg_twentieth⟩
  obtain ⟨x₂, ⟨h₂l, h₂r⟩, h₂⟩ : ∃ x ∈ Ioo (-1 / 20 : ℝ) (-1 / 1000), l4j_chi x = 0 :=
    intermediate_value_Ioo' (by norm_num) (hcont.mono (subset_univ _))
      ⟨l4j_chi_neg_thousandth, l4j_chi_neg_twentieth⟩
  obtain ⟨x₃, ⟨h₃l, h₃r⟩, h₃⟩ : ∃ x ∈ Ioo (-1 / 1000 : ℝ) (1 / 10), l4j_chi x = 0 :=
    intermediate_value_Ioo (by norm_num) (hcont.mono (subset_univ _))
      ⟨l4j_chi_neg_thousandth, l4j_chi_tenth⟩
  unfold l4j_chi at h₁ h₂ h₃
  rcases l4j_cubic_roots h₁ h₂ h₃ (by linarith) (by linarith) (by linarith) hμ with h | h | h <;>
    rw [h, Complex.norm_real, Real.norm_eq_abs, abs_lt] <;> constructor <;> linarith

end TriFuller

end SmoothedPolygons
