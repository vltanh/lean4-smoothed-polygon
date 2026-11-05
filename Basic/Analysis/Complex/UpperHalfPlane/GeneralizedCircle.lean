module

public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction

/-!
# Möbius transformations map generalized circles to generalized circles

A *generalized circle* (a Euclidean circle or a Euclidean line) in the plane `ℂ ≅ ℝ²` is the zero
set of `A (x² + y²) + B x + C y + D` with real coefficients such that `B² + C² - 4AD > 0`; it is a
line exactly when `A = 0`. The linear fractional transformation `z ↦ (pz + q)/(rz + s)` of
`g = [[p, q], [r, s]] ∈ SL₂(ℝ)` maps the points of the upper half-plane `ℍ` on the generalized
circle with coefficients `(A, B, C, D)` to points on the generalized circle with coefficients
`(As² - Brs + Dr², B(ps + qr) - 2Aqs - 2Dpr, C, Aq² - Bpq + Dp²)`, and the discriminant
`B² + C² - 4AD` is unchanged.

## Main results

* `UpperHalfPlane.genCircle_smul`: the image of a point of a generalized circle under `g ∈ SL₂(ℝ)`
  lies on the transformed generalized circle;
* `UpperHalfPlane.genCircle_discr_smul`: the discriminant of the transformed coefficients;
* `UpperHalfPlane.genCircle_smul_coeff_ne_zero`: a nondegenerate generalized circle
  (`B² + C² - 4AD > 0`) is mapped to a nondegenerate one, in particular `(A', B', C') ≠ 0`;
* `UpperHalfPlane.smul_ray_genCircle`: the image under `g` of the ray from `0` through `w₀ ∈ ℍ` lies
  on a generalized circle, which is a line when `g` fixes `∞` or sends `0` to `∞`
  (`g₁₀ g₁₁ = 0`).
-/

@[expose] public section

namespace UpperHalfPlane

open scoped MatrixGroups

/-- The real and imaginary parts and the squared modulus of `w = g • z` for
`g = [[p, q], [r, s]] ∈ SL₂(ℝ)` and `z = x + iy`, multiplied by `|rz + s|²`:
`Re w · |rz + s|² = pr(x² + y²) + (ps + qr)x + qs`, `Im w · |rz + s|² = y` and
`|w|² · |rz + s|² = (px + q)² + (py)²`. -/
theorem smul_re_im_mul_normSq_denom (g : SL(2, ℝ)) (z : ℍ) :
    (g • z).re * ((g 1 0 * z.re + g 1 1) ^ 2 + (g 1 0 * z.im) ^ 2) =
        g 0 0 * g 1 0 * (z.re ^ 2 + z.im ^ 2) + (g 0 0 * g 1 1 + g 0 1 * g 1 0) * z.re +
          g 0 1 * g 1 1 ∧
      (g • z).im * ((g 1 0 * z.re + g 1 1) ^ 2 + (g 1 0 * z.im) ^ 2) = z.im ∧
      ((g • z).re ^ 2 + (g • z).im ^ 2) * ((g 1 0 * z.re + g 1 1) ^ 2 + (g 1 0 * z.im) ^ 2) =
        (g 0 0 * z.re + g 0 1) ^ 2 + (g 0 0 * z.im) ^ 2 := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := g.det_coe; rwa [Matrix.det_fin_two] at this
  have hcoe := coe_specialLinearGroup_apply g z
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at hcoe
  have hD : ((g 1 0 : ℂ) * z + g 1 1) ≠ 0 := by
    have := denom_ne_zero (g : GL (Fin 2) ℝ) z
    simpa [denom] using this
  -- `w (rz + s) = pz + q`, in real and imaginary parts
  have hmul : ((g • z : ℍ) : ℂ) * ((g 1 0 : ℂ) * z + g 1 1) = (g 0 0 : ℂ) * z + g 0 1 := by
    rw [hcoe, div_mul_cancel₀ _ hD]
  have h1 := congrArg Complex.re hmul
  have h2 := congrArg Complex.im hmul
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, zero_mul, sub_zero,
    add_zero] at h1 h2
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (g 1 0 * z.re + g 1 1) * h1 + g 1 0 * z.im * h2
  · linear_combination (g 1 0 * z.re + g 1 1) * h2 - g 1 0 * z.im * h1 + z.im * hdet
  · linear_combination
      ((g • z).re * (g 1 0 * z.re + g 1 1) - (g • z).im * (g 1 0 * z.im) +
          (g 0 0 * z.re + g 0 1)) * h1 +
        ((g • z).re * (g 1 0 * z.im) + (g • z).im * (g 1 0 * z.re + g 1 1) + g 0 0 * z.im) * h2

/-- **Möbius transformations map generalized circles to generalized circles.** If `z ∈ ℍ` lies on
the generalized circle `A (x² + y²) + B x + C y + D = 0`, then `g • z` lies on the generalized
circle with coefficients `(As² - Brs + Dr², B(ps + qr) - 2Aqs - 2Dpr, C, Aq² - Bpq + Dp²)`, where
`g = [[p, q], [r, s]] ∈ SL₂(ℝ)`. -/
theorem genCircle_smul (g : SL(2, ℝ)) (z : ℍ) {A B C D : ℝ}
    (h : A * (z.re ^ 2 + z.im ^ 2) + B * z.re + C * z.im + D = 0) :
    (A * g 1 1 ^ 2 - B * g 1 0 * g 1 1 + D * g 1 0 ^ 2) * ((g • z).re ^ 2 + (g • z).im ^ 2) +
        (B * (g 0 0 * g 1 1 + g 0 1 * g 1 0) - 2 * A * g 0 1 * g 1 1 - 2 * D * g 0 0 * g 1 0) *
          (g • z).re +
        C * (g • z).im + (A * g 0 1 ^ 2 - B * g 0 0 * g 0 1 + D * g 0 0 ^ 2) = 0 := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := g.det_coe; rwa [Matrix.det_fin_two] at this
  obtain ⟨R1, R2, R3⟩ := smul_re_im_mul_normSq_denom g z
  set N := (g 1 0 * z.re + g 1 1) ^ 2 + (g 1 0 * z.im) ^ 2 with hN
  have hNpos : 0 < N := by
    rcases eq_or_ne (g 1 0) 0 with hr | hr
    · have hs : g 1 1 ≠ 0 := by intro hs; rw [hr, hs] at hdet; simp at hdet
      rw [hN, hr]; simp only [zero_mul, zero_add]; positivity
    · have := z.im_pos
      rw [hN]; positivity
  refine (mul_eq_zero.1 ?_).resolve_right hNpos.ne'
  linear_combination
    (A * g 1 1 ^ 2 - B * g 1 0 * g 1 1 + D * g 1 0 ^ 2) * R3 +
      (B * (g 0 0 * g 1 1 + g 0 1 * g 1 0) - 2 * A * g 0 1 * g 1 1 - 2 * D * g 0 0 * g 1 0) * R1 +
      C * R2 + h +
      (g 0 0 * g 1 1 - g 0 1 * g 1 0 + 1) * (A * (z.re ^ 2 + z.im ^ 2) + B * z.re + D) * hdet

/-- The discriminant `B² + C² - 4AD` of a generalized circle is invariant under `SL₂(ℝ)`. -/
theorem genCircle_discr_smul (g : SL(2, ℝ)) (A B C D : ℝ) :
    (B * (g 0 0 * g 1 1 + g 0 1 * g 1 0) - 2 * A * g 0 1 * g 1 1 - 2 * D * g 0 0 * g 1 0) ^ 2 +
        C ^ 2 - 4 * (A * g 1 1 ^ 2 - B * g 1 0 * g 1 1 + D * g 1 0 ^ 2) *
          (A * g 0 1 ^ 2 - B * g 0 0 * g 0 1 + D * g 0 0 ^ 2) =
      B ^ 2 + C ^ 2 - 4 * A * D := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := g.det_coe; rwa [Matrix.det_fin_two] at this
  linear_combination (g 0 0 * g 1 1 - g 0 1 * g 1 0 + 1) * (B ^ 2 - 4 * A * D) * hdet

/-- A nondegenerate generalized circle (`B² + C² - 4AD > 0`) is mapped by `g ∈ SL₂(ℝ)` to a
nondegenerate one; in particular its first three coefficients do not all vanish. -/
theorem genCircle_smul_coeff_ne_zero (g : SL(2, ℝ)) {A B C D : ℝ}
    (hdisc : 0 < B ^ 2 + C ^ 2 - 4 * A * D) :
    A * g 1 1 ^ 2 - B * g 1 0 * g 1 1 + D * g 1 0 ^ 2 ≠ 0 ∨
      B * (g 0 0 * g 1 1 + g 0 1 * g 1 0) - 2 * A * g 0 1 * g 1 1 - 2 * D * g 0 0 * g 1 0 ≠ 0 ∨
      C ≠ 0 := by
  by_contra hcon
  simp only [not_or, not_not] at hcon
  obtain ⟨hA, hB, hC⟩ := hcon
  have h := genCircle_discr_smul g A B C D
  rw [hA, hB] at h
  subst hC
  nlinarith

/-- **The image of a ray from `0` under a Möbius transformation is (an arc of) a generalized
circle.** The points `z = t w₀` of the ray from `0` through `w₀ ∈ ℍ` lie on the line
`-Im(w₀) x + Re(w₀) y = 0`; their images under `g = [[p, q], [r, s]] ∈ SL₂(ℝ)` lie on the
generalized circle `Im(w₀) rs (x² + y²) - Im(w₀)(ps + qr) x + Re(w₀) y + Im(w₀) pq = 0`. It is a
line when `rs = 0`, that is, when `g · ∞ = p/r` or `g · 0 = q/s` is `∞`. -/
theorem smul_ray_genCircle (g : SL(2, ℝ)) (w₀ z : ℍ) {t : ℝ} (hz : (z : ℂ) = t * w₀) :
    w₀.im * (g 1 0 * g 1 1) * ((g • z).re ^ 2 + (g • z).im ^ 2) -
        w₀.im * (g 0 0 * g 1 1 + g 0 1 * g 1 0) * (g • z).re + w₀.re * (g • z).im +
        w₀.im * (g 0 0 * g 0 1) = 0 := by
  have hre : z.re = t * w₀.re := by
    rw [← UpperHalfPlane.coe_re, hz]; simp
  have him : z.im = t * w₀.im := by
    rw [← UpperHalfPlane.coe_im, hz]; simp
  have hline : 0 * (z.re ^ 2 + z.im ^ 2) + -w₀.im * z.re + w₀.re * z.im + 0 = 0 := by
    rw [hre, him]; ring
  linear_combination genCircle_smul g z hline

/-- The generalized circle of `smul_ray_genCircle` is nondegenerate: its first three coefficients
do not all vanish. -/
theorem smul_ray_genCircle_coeff_ne_zero (g : SL(2, ℝ)) (w₀ : ℍ) :
    w₀.im * (g 1 0 * g 1 1) ≠ 0 ∨ -(w₀.im * (g 0 0 * g 1 1 + g 0 1 * g 1 0)) ≠ 0 ∨
      w₀.re ≠ 0 := by
  have hdisc : 0 < (-w₀.im) ^ 2 + w₀.re ^ 2 - 4 * 0 * 0 := by
    have := w₀.im_pos; nlinarith [sq_nonneg w₀.re]
  have h := genCircle_smul_coeff_ne_zero g hdisc
  convert h using 2 <;> ring_nf

end UpperHalfPlane
