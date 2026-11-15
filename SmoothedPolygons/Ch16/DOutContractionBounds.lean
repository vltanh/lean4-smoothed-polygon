module

public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The derivative bounds of the contraction, an interval chain written out step by step

Bounds on the partial derivatives of the Fuller–Poincaré map near `q_out`, used by
`SmoothedPolygons/Ch16/DOutContraction.lean` for the Lipschitz bound of `DOutContracts` on the box
`B` of `SmoothedPolygons/Ch16/DOutImages.lean`. With `σ = 1/τ` and the coefficients
`x₁, y₁, x₂, y₂, κ` of the cell point, the image of `p ∈ B` is the class of the point whose
normalized coordinates are `w₁/τ = u₀ + i v₀`, `w₂/τ² = u₁ + i v₁` with
`u₀ = x₁ σ - √3/2`, `v₀ = 1/3 - 2 y₂ σ² + 2√3 κ σ³`, `u₁ = x₁ σ + x₂ σ² - √3/4`,
`v₁ = 1/12 - y₂ σ² + 2√3 κ σ³` (`nu0`, `nv0`, `nu1`, `nv1`; the coefficient `y₁` is eliminated
with the root equation), and `σ` is the root of `nF = √3 κ σ³ - y₁ σ/2 - y₂ σ² - 1/12`. The
angles of the image are `arctan (v₁/u₁)` and `arctan (v₁/u₁) - arctan (v₀/u₀)`, whose derivatives
are `angD` (`(u v' - v u')/(u² + v²)`); the radius enters through `(u₁² + v₁²)/(u₀² + v₀²)²`,
whose derivative is `radD`.

The lemmas `lip_*` are an interval evaluation written out step by step (about 330 steps, generated
by a script), each step checked by `norm_num`: each step is one of the elementary interval lemmas
`iadd`, `isub`, `ineg`, `imul`, `idiv`, `ipow`, `isq_nonpos`, with rational endpoints (denominator
`10⁶`, rounded outward) and side conditions closed by `norm_num`; no kernel computation (no
`decide`) and no enumeration of boxes is involved. The script that wrote them is
`numerics/generators/dout_contraction_bounds.py`, on the single box `B × [σlo, σhi]`:

* `lip_coef`: the coefficients from the intervals of `r₂` and of `sin`, `cos` of the angles;
* `lip_uv`: `u₀, v₀, u₁, v₁`;
* `lip_dir0`, `lip_dir1`, `lip_dir2`, `lip_dirσ`: the partial derivatives of the two angles, of the
  radius function and of `nF` in the directions `r₂, ψ, θ₂` and `σ`;
* `lip_bracket`: `nF < 0` at `σlo = 371/2000` and `nF > 0` at `σhi = 441/2000`;
* `lip_combo*`: the combinations `|q - e α/β|` of the implicit mean value theorem
  (`abs_sub_le_sum_of_implicit`), whose row sums are `≤ 0.652` (`θ₂`), `≤ 0.514`
  (`ψ`) and `≤ 0.910` (the radius function; `≤ 0.52` for `r₂` after dividing by `7/4`).
-/

@[expose] public section

namespace SmoothedPolygons.TriFuller.DOutAnalytic

open Set

/-! ### Interval arithmetic -/

theorem iconst (a : ℝ) : a ∈ Icc a a := ⟨le_rfl, le_rfl⟩

theorem iadd {x y a b c d lo hi : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d) (h1 : lo ≤ a + c)
    (h2 : b + d ≤ hi) : x + y ∈ Icc lo hi :=
  ⟨by linarith [hx.1, hy.1], by linarith [hx.2, hy.2]⟩

theorem isub {x y a b c d lo hi : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d) (h1 : lo ≤ a - d)
    (h2 : b - c ≤ hi) : x - y ∈ Icc lo hi :=
  ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩

theorem ineg {x a b lo hi : ℝ} (hx : x ∈ Icc a b) (h1 : lo ≤ -b) (h2 : -a ≤ hi) :
    -x ∈ Icc lo hi :=
  ⟨by linarith [hx.2], by linarith [hx.1]⟩

/-- The product of two intervals: `x y` lies between the products of the endpoints. -/
theorem imul {x y a b c d lo hi : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d)
    (h1 : lo ≤ a * c) (h2 : lo ≤ a * d) (h3 : lo ≤ b * c) (h4 : lo ≤ b * d)
    (h5 : a * c ≤ hi) (h6 : a * d ≤ hi) (h7 : b * c ≤ hi) (h8 : b * d ≤ hi) :
    x * y ∈ Icc lo hi := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  constructor
  · rcases le_total 0 y with hy0 | hy0
    · have : a * y ≤ x * y := mul_le_mul_of_nonneg_right hx1 hy0
      rcases le_total 0 a with ha | ha
      · nlinarith [mul_le_mul_of_nonneg_left hy1 ha]
      · nlinarith [mul_le_mul_of_nonpos_left hy2 ha]
    · have : b * y ≤ x * y := mul_le_mul_of_nonpos_right hx2 hy0
      rcases le_total 0 b with hb | hb
      · nlinarith [mul_le_mul_of_nonneg_left hy1 hb]
      · nlinarith [mul_le_mul_of_nonpos_left hy2 hb]
  · rcases le_total 0 y with hy0 | hy0
    · have : x * y ≤ b * y := mul_le_mul_of_nonneg_right hx2 hy0
      rcases le_total 0 b with hb | hb
      · nlinarith [mul_le_mul_of_nonneg_left hy2 hb]
      · nlinarith [mul_le_mul_of_nonpos_left hy1 hb]
    · have : x * y ≤ a * y := mul_le_mul_of_nonpos_right hx1 hy0
      rcases le_total 0 a with ha | ha
      · nlinarith [mul_le_mul_of_nonneg_left hy2 ha]
      · nlinarith [mul_le_mul_of_nonpos_left hy1 ha]

/-- The quotient by a positive interval. -/
theorem idiv {x y a b c d lo hi : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d) (hc : 0 < c)
    (h1 : lo ≤ a / c) (h2 : lo ≤ a / d) (h3 : lo ≤ b / c) (h4 : lo ≤ b / d)
    (h5 : a / c ≤ hi) (h6 : a / d ≤ hi) (h7 : b / c ≤ hi) (h8 : b / d ≤ hi) :
    x / y ∈ Icc lo hi := by
  have hy0 : 0 < y := lt_of_lt_of_le hc hy.1
  have hinv : y⁻¹ ∈ Icc d⁻¹ c⁻¹ := ⟨inv_anti₀ hy0 hy.2, inv_anti₀ hc hy.1⟩
  rw [div_eq_mul_inv]
  refine imul hx hinv ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simpa only [div_eq_mul_inv] using ‹_›

theorem ipow {x a b lo hi : ℝ} {n : ℕ} (hx : x ∈ Icc a b) (ha : 0 ≤ a) (h1 : lo ≤ a ^ n)
    (h2 : b ^ n ≤ hi) : x ^ n ∈ Icc lo hi :=
  ⟨h1.trans (pow_le_pow_left₀ ha hx.1 n), (pow_le_pow_left₀ (ha.trans hx.1) hx.2 n).trans h2⟩

theorem isq_nonpos {x a b lo hi : ℝ} (hx : x ∈ Icc a b) (hb : b ≤ 0) (h1 : lo ≤ b ^ 2)
    (h2 : a ^ 2 ≤ hi) : x ^ 2 ∈ Icc lo hi := by
  obtain ⟨hx1, hx2⟩ := hx
  constructor <;> nlinarith

theorem iabs {x a b L : ℝ} (hx : x ∈ Icc a b) (h1 : -L ≤ a) (h2 : b ≤ L) : |x| ≤ L :=
  abs_le.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-! ### The normalized image and its derivatives -/

/-- `u₀ = x₁ σ - √3/2` (`Re (ζ z₁(τ))/τ`). -/
noncomputable def nu0 (x1 t : ℝ) : ℝ := x1 * t - √3 / 2

/-- `v₀ = 1/3 - 2 y₂ σ² + 2√3 κ σ³` (`Im (ζ z₁(τ))/τ` at the root). -/
noncomputable def nv0 (y2 k t : ℝ) : ℝ := 1 / 3 - 2 * y2 * t ^ 2 + 2 * √3 * k * t ^ 3

/-- `u₁ = x₁ σ + x₂ σ² - √3/4` (`Re (ζ z₂(τ))/τ²`). -/
noncomputable def nu1 (x1 x2 t : ℝ) : ℝ := x1 * t + x2 * t ^ 2 - √3 / 4

/-- `v₁ = 1/12 - y₂ σ² + 2√3 κ σ³` (`Im (ζ z₂(τ))/τ²` at the root). -/
noncomputable def nv1 (y2 k t : ℝ) : ℝ := 1 / 12 - y2 * t ^ 2 + 2 * √3 * k * t ^ 3

/-- The root equation `D(τ)/τ³ = √3 κ σ³ - y₁ σ/2 - y₂ σ² - 1/12`, up to sign. -/
noncomputable def nF (y1 y2 k t : ℝ) : ℝ := √3 * k * t ^ 3 - y1 * t / 2 - y2 * t ^ 2 - 1 / 12

/-- The derivative `(u v' - v u')/(u² + v²)` of `arctan (v/u)`. -/
noncomputable def angD (u v du dv : ℝ) : ℝ := (u * dv - v * du) / (u ^ 2 + v ^ 2)

/-- The derivative of `(u₁² + v₁²)/(u₀² + v₀²)²`. -/
noncomputable def radD (u0 v0 u1 v1 du0 dv0 du1 dv1 : ℝ) : ℝ :=
  (2 * (u1 * du1 + v1 * dv1) * (u0 ^ 2 + v0 ^ 2) -
    2 * (u1 ^ 2 + v1 ^ 2) * (2 * (u0 * du0 + v0 * dv0))) / (u0 ^ 2 + v0 ^ 2) ^ 3

/-! ### The interval chains -/

/-- The coefficients on `B` (generated interval chain). -/
theorem lip_coef {r cφ1 sφ1 cφ2 sφ2 sψ cψ : ℝ}
    (hr : r ∈ Icc (11 / 50 : ℝ) (3 / 10 : ℝ))
    (hc1 : cφ1 ∈ Icc (-128991 / 1000000 : ℝ) (61109 / 200000 : ℝ))
    (hs1 : sφ1 ∈ Icc (-1 : ℝ) (-476077 / 500000 : ℝ))
    (hc2 : cφ2 ∈ Icc (69933 / 1000000 : ℝ) (19031 / 50000 : ℝ))
    (hs2 : sφ2 ∈ Icc (-498787 / 500000 : ℝ) (-924707 / 1000000 : ℝ))
    (hsψ : sψ ∈ Icc (25 / 313 : ℝ) (20 / 101 : ℝ))
    (hcψ : cψ ∈ Icc (99 / 101 : ℝ) (312 / 313 : ℝ))
    :
    (1 - r) * cφ1 ∈ Icc (-100613 / 1000000 : ℝ) (119163 / 500000 : ℝ) ∧
    (1 - r) * sφ1 ∈ Icc (-39 / 50 : ℝ) (-666507 / 1000000 : ℝ) ∧
    r * cφ2 ∈ Icc (3077 / 200000 : ℝ) (57093 / 500000 : ℝ) ∧
    r * sφ2 ∈ Icc (-299273 / 1000000 : ℝ) (-40687 / 200000 : ℝ) ∧
    (1 - r) * r * sψ ∈ Icc (123 / 10000 : ℝ) (46337 / 1000000 : ℝ) ∧
    (1 - 2 * r) * sψ ∈ Icc (7987 / 250000 : ℝ) (27723 / 250000 : ℝ) ∧
    (1 - r) * r * cψ ∈ Icc (3019 / 20000 : ℝ) (233253 / 1000000 : ℝ) := by
  have h1 := iconst (1 : ℝ)
  have h2 := iconst (2 : ℝ)
  have h3 := isub (lo := 7 / 10) (hi := 39 / 50) h1 hr
    (by norm_num) (by norm_num)
  have h4 := imul (lo := -100613 / 1000000) (hi := 119163 / 500000) h3 hc1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h5 := imul (lo := -39 / 50) (hi := -666507 / 1000000) h3 hs1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h6 := imul (lo := 3077 / 200000) (hi := 57093 / 500000) hr hc2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h7 := imul (lo := -299273 / 1000000) (hi := -40687 / 200000) hr hs2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h8 := imul (lo := 77 / 500) (hi := 117 / 500) h3 hr
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h9 := imul (lo := 123 / 10000) (hi := 46337 / 1000000) h8 hsψ
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h10 := imul (lo := 11 / 25) (hi := 3 / 5) h2 hr
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h11 := isub (lo := 2 / 5) (hi := 14 / 25) h1 h10
    (by norm_num) (by norm_num)
  have h12 := imul (lo := 7987 / 250000) (hi := 27723 / 250000) h11 hsψ
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h13 := imul (lo := 3019 / 20000) (hi := 233253 / 1000000) h8 hcψ
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h4, h5, h6, h7, h9, h12, h13⟩

/-- The normalized image on `B × [σlo, σhi]` (generated interval chain). -/
theorem lip_uv {x1 x2 y2 k t : ℝ}
    (hx1 : x1 ∈ Icc (-100613 / 1000000 : ℝ) (119163 / 500000 : ℝ))
    (hx2 : x2 ∈ Icc (3077 / 200000 : ℝ) (57093 / 500000 : ℝ))
    (hy2 : y2 ∈ Icc (-299273 / 1000000 : ℝ) (-40687 / 200000 : ℝ))
    (hk : k ∈ Icc (123 / 10000 : ℝ) (46337 / 1000000 : ℝ))
    (ht : t ∈ Icc (371 / 2000 : ℝ) (441 / 2000 : ℝ))
    (hq : √3 ∈ Icc (433 / 250 : ℝ) (17321 / 10000 : ℝ))
    :
    nu0 x1 t ∈ Icc (-222059 / 250000 : ℝ) (-813449 / 1000000 : ℝ) ∧
    nv0 y2 k t ∈ Icc (86901 / 250000 : ℝ) (364157 / 1000000 : ℝ) ∧
    nu1 x1 x2 t ∈ Icc (-227341 / 500000 : ℝ) (-374897 / 1000000 : ℝ) ∧
    nv1 y2 k t ∈ Icc (22651 / 250000 : ℝ) (49803 / 500000 : ℝ) := by
  have h1 := iconst (1 / 3 : ℝ)
  have h2 := iconst (1 / 12 : ℝ)
  have h3 := iconst (2 : ℝ)
  have h4 := ipow (lo := 3441 / 100000) (hi := 48621 / 1000000) (n := 2) ht
    (by norm_num) (by norm_num) (by norm_num)
  have h5 := ipow (lo := 6383 / 1000000) (hi := 10721 / 1000000) (n := 3) ht
    (by norm_num) (by norm_num) (by norm_num)
  have h6 := imul (lo := -11093 / 500000) (hi := 52551 / 1000000) hx1 ht
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h7 := iconst (2 : ℝ)
  have h8 := idiv (lo := 433 / 500) (hi := 17321 / 20000) hq h7
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have h9 := isub (lo := -222059 / 250000) (hi := -813449 / 1000000) h6 h8
    (by norm_num) (by norm_num)
  have h10 := imul (lo := -299273 / 500000) (hi := -40687 / 100000) h3 hy2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h11 := imul (lo := -14551 / 500000) (hi := -7 / 500) h10 h4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h12 := isub (lo := 347333 / 1000000) (hi := 90609 / 250000) h1 h11
    (by norm_num) (by norm_num)
  have h13 := imul (lo := 433 / 125) (hi := 17321 / 5000) h3 hq
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h14 := imul (lo := 42607 / 1000000) (hi := 160521 / 1000000) h13 hk
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h15 := imul (lo := 271 / 1000000) (hi := 1721 / 1000000) h14 h5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h16 := iadd (lo := 86901 / 250000) (hi := 364157 / 1000000) h12 h15
    (by norm_num) (by norm_num)
  have h17 := imul (lo := -11093 / 500000) (hi := 52551 / 1000000) hx1 ht
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h18 := imul (lo := 529 / 1000000) (hi := 347 / 62500) hx2 h4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h19 := iadd (lo := -21657 / 1000000) (hi := 58103 / 1000000) h17 h18
    (by norm_num) (by norm_num)
  have h20 := iconst (4 : ℝ)
  have h21 := idiv (lo := 433 / 1000) (hi := 17321 / 40000) hq h20
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have h22 := isub (lo := -227341 / 500000) (hi := -374897 / 1000000) h19 h21
    (by norm_num) (by norm_num)
  have h23 := imul (lo := -14551 / 1000000) (hi := -7 / 1000) hy2 h4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h24 := isub (lo := 90333 / 1000000) (hi := 19577 / 200000) h2 h23
    (by norm_num) (by norm_num)
  have h25 := imul (lo := 433 / 125) (hi := 17321 / 5000) h3 hq
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h26 := imul (lo := 42607 / 1000000) (hi := 160521 / 1000000) h25 hk
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h27 := imul (lo := 271 / 1000000) (hi := 1721 / 1000000) h26 h5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h28 := iadd (lo := 22651 / 250000) (hi := 49803 / 500000) h24 h27
    (by norm_num) (by norm_num)
  exact ⟨h9, h16, h22, h28⟩

/-- The derivatives in the direction `0` (generated interval chain). -/
theorem lip_dir0 {u0 v0 u1 v1 t dx1 dy1 dx2 dy2 dk : ℝ}
    (hu0 : u0 ∈ Icc (-222059 / 250000 : ℝ) (-813449 / 1000000 : ℝ))
    (hv0 : v0 ∈ Icc (86901 / 250000 : ℝ) (364157 / 1000000 : ℝ))
    (hu1 : u1 ∈ Icc (-227341 / 500000 : ℝ) (-374897 / 1000000 : ℝ))
    (hv1 : v1 ∈ Icc (22651 / 250000 : ℝ) (49803 / 500000 : ℝ))
    (ht : t ∈ Icc (371 / 2000 : ℝ) (441 / 2000 : ℝ))
    (hq : √3 ∈ Icc (433 / 250 : ℝ) (17321 / 10000 : ℝ))
    (hdx1 : dx1 ∈ Icc (-61109 / 200000 : ℝ) (128991 / 1000000 : ℝ))
    (hdy1 : dy1 ∈ Icc (476077 / 500000 : ℝ) (1 : ℝ))
    (hdx2 : dx2 ∈ Icc (69933 / 1000000 : ℝ) (19031 / 50000 : ℝ))
    (hdy2 : dy2 ∈ Icc (-498787 / 500000 : ℝ) (-924707 / 1000000 : ℝ))
    (hdk : dk ∈ Icc (7987 / 250000 : ℝ) (27723 / 250000 : ℝ))
    :
    angD u1 v1 (dx1 * t + dx2 * t ^ 2) (2 * √3 * dk * t ^ 3 - dy2 * t ^ 2) ∈ Icc (-192289 /
      1000000 : ℝ) (-5281 / 200000 : ℝ) ∧
    angD u0 v0 (dx1 * t) (2 * √3 * dk * t ^ 3 - 2 * dy2 * t ^ 2) ∈ Icc (-16003 / 125000 : ℝ)
      (-30171 / 1000000 : ℝ) ∧
    radD u0 v0 u1 v1 (dx1 * t) (2 * √3 * dk * t ^ 3 - 2 * dy2 * t ^ 2) (dx1 * t + dx2 * t ^ 2) (2
      * √3 * dk * t ^ 3 - dy2 * t ^ 2) ∈ Icc (-245621 / 1000000 : ℝ) (69517 / 500000 : ℝ) ∧
    √3 * dk * t ^ 3 - dy1 * t / 2 - dy2 * t ^ 2 ∈ Icc (-39039 / 500000 : ℝ) (-9437 / 250000 :
      ℝ) := by
  unfold angD radD
  have h1 := iconst (2 : ℝ)
  have h2 := ipow (lo := 3441 / 100000) (hi := 48621 / 1000000) (n := 2) ht
    (by norm_num) (by norm_num) (by norm_num)
  have h3 := ipow (lo := 6383 / 1000000) (hi := 10721 / 1000000) (n := 3) ht
    (by norm_num) (by norm_num) (by norm_num)
  have h4 := imul (lo := -67373 / 1000000) (hi := 28443 / 1000000) hdx1 ht
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h5 := imul (lo := 433 / 125) (hi := 17321 / 5000) h1 hq
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h6 := imul (lo := 110667 / 1000000) (hi := 384153 / 1000000) h5 hdk
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h7 := imul (lo := 353 / 500000) (hi := 4119 / 1000000) h6 h3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h8 := imul (lo := -498787 / 250000) (hi := -924707 / 500000) h1 hdy2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h9 := imul (lo := -97007 / 1000000) (hi := -31819 / 500000) h8 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h10 := isub (lo := 8043 / 125000) (hi := 50563 / 500000) h7 h9
    (by norm_num) (by norm_num)
  have h11 := imul (lo := -67373 / 1000000) (hi := 28443 / 1000000) hdx1 ht
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h12 := imul (lo := 1203 / 500000) (hi := 18507 / 1000000) hdx2 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h13 := iadd (lo := -64967 / 1000000) (hi := 939 / 20000) h11 h12
    (by norm_num) (by norm_num)
  have h14 := imul (lo := -6063 / 125000) (hi := -31819 / 1000000) hdy2 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h15 := isub (lo := 1301 / 40000) (hi := 52623 / 1000000) h7 h14
    (by norm_num) (by norm_num)
  have h16 := imul (lo := 55333 / 1000000) (hi := 192077 / 1000000) hq hdk
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h17 := imul (lo := 353 / 1000000) (hi := 103 / 50000) h16 h3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h18 := imul (lo := 11039 / 62500) (hi := 441 / 2000) hdy1 ht
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h19 := idiv (lo := 11039 / 125000) (hi := 441 / 4000) h18 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have h20 := isub (lo := -109897 / 1000000) (hi := -21563 / 250000) h17 h19
    (by norm_num) (by norm_num)
  have h21 := imul (lo := -6063 / 125000) (hi := -31819 / 1000000) hdy2 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h22 := isub (lo := -39039 / 500000) (hi := -9437 / 250000) h20 h21
    (by norm_num) (by norm_num)
  have h23 := iconst (2 : ℝ)
  have h24 := isq_nonpos (lo := 661699 / 1000000) (hi := 197241 / 250000) hu0
    (by norm_num) (by norm_num) (by norm_num)
  have h25 := ipow (lo := 30207 / 250000) (hi := 132611 / 1000000) (n := 2) hv0
    (by norm_num) (by norm_num) (by norm_num)
  have h26 := isq_nonpos (lo := 140547 / 1000000) (hi := 12921 / 62500) hu1
    (by norm_num) (by norm_num) (by norm_num)
  have h27 := ipow (lo := 8209 / 1000000) (hi := 4961 / 500000) (n := 2) hv1
    (by norm_num) (by norm_num) (by norm_num)
  have h28 := iadd (lo := 782527 / 1000000) (hi := 36863 / 40000) h24 h25
    (by norm_num) (by norm_num)
  have h29 := iadd (lo := 37189 / 250000) (hi := 108329 / 500000) h26 h27
    (by norm_num) (by norm_num)
  have h30 := imul (lo := -23927 / 1000000) (hi := -12193 / 1000000) hu1 h15
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h31 := imul (lo := -809 / 125000) (hi := 4677 / 1000000) hv1 h13
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h32 := isub (lo := -7151 / 250000) (hi := -5721 / 1000000) h30 h31
    (by norm_num) (by norm_num)
  have h33 := idiv (lo := -192289 / 1000000) (hi := -5281 / 200000) h32 h29
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have h34 := imul (lo := -2807 / 31250) (hi := -2617 / 50000) hu0 h10
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h35 := imul (lo := -4907 / 200000) (hi := 5179 / 500000) hv0 h4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h36 := isub (lo := -50091 / 500000) (hi := -5561 / 200000) h34 h35
    (by norm_num) (by norm_num)
  have h37 := idiv (lo := -16003 / 125000) (hi := -30171 / 1000000) h36 h28
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have h38 := imul (lo := -5337 / 250000) (hi := 1477 / 50000) hu1 h13
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h39 := imul (lo := 1473 / 500000) (hi := 2621 / 500000) hv1 h15
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h40 := iadd (lo := -9201 / 500000) (hi := 17391 / 500000) h38 h39
    (by norm_num) (by norm_num)
  have h41 := imul (lo := -9201 / 250000) (hi := 17391 / 250000) h23 h40
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h42 := imul (lo := -5053 / 200000) (hi := 14961 / 250000) hu0 h4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h43 := imul (lo := 11183 / 500000) (hi := 18413 / 500000) hv0 h10
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h44 := iadd (lo := -2899 / 1000000) (hi := 9667 / 100000) h42 h43
    (by norm_num) (by norm_num)
  have h45 := imul (lo := -2899 / 500000) (hi := 9667 / 50000) h23 h44
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h46 := imul (lo := -16959 / 500000) (hi := 64109 / 1000000) h41 h28
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h47 := imul (lo := 37189 / 125000) (hi := 108329 / 250000) h23 h29
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h48 := imul (lo := -2513 / 1000000) (hi := 41889 / 500000) h47 h45
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h49 := isub (lo := -1839 / 15625) (hi := 33311 / 500000) h46 h48
    (by norm_num) (by norm_num)
  have h50 := ipow (lo := 479179 / 1000000) (hi := 156539 / 200000) (n := 3) h28
    (by norm_num) (by norm_num) (by norm_num)
  have h51 := idiv (lo := -245621 / 1000000) (hi := 69517 / 500000) h49 h50
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  exact ⟨h33, h37, h51, h22⟩

/-- The derivatives in the direction `1` (generated interval chain). -/
theorem lip_dir1 {u0 v0 u1 v1 t dx1 dy1 dx2 dy2 dk : ℝ}
    (hu0 : u0 ∈ Icc (-222059 / 250000 : ℝ) (-813449 / 1000000 : ℝ))
    (hv0 : v0 ∈ Icc (86901 / 250000 : ℝ) (364157 / 1000000 : ℝ))
    (hu1 : u1 ∈ Icc (-227341 / 500000 : ℝ) (-374897 / 1000000 : ℝ))
    (hv1 : v1 ∈ Icc (22651 / 250000 : ℝ) (49803 / 500000 : ℝ))
    (ht : t ∈ Icc (371 / 2000 : ℝ) (441 / 2000 : ℝ))
    (hq : √3 ∈ Icc (433 / 250 : ℝ) (17321 / 10000 : ℝ))
    (hdx1 : dx1 ∈ Icc (-39 / 50 : ℝ) (-666507 / 1000000 : ℝ))
    (hdy1 : dy1 ∈ Icc (-119163 / 500000 : ℝ) (100613 / 1000000 : ℝ))
    (hdx2 : dx2 ∈ Icc (0 : ℝ) (0 : ℝ))
    (hdy2 : dy2 ∈ Icc (0 : ℝ) (0 : ℝ))
    (hdk : dk ∈ Icc (3019 / 20000 : ℝ) (233253 / 1000000 : ℝ))
    :
    angD u1 v1 (dx1 * t + dx2 * t ^ 2) (2 * √3 * dk * t ^ 3 - dy2 * t ^ 2) ∈ Icc (16761 / 500000 :
      ℝ) (106759 / 1000000 : ℝ) ∧
    angD u0 v0 (dx1 * t) (2 * √3 * dk * t ^ 3 - 2 * dy2 * t ^ 2) ∈ Icc (38283 / 1000000 : ℝ) (7657
      / 100000 : ℝ) ∧
    radD u0 v0 u1 v1 (dx1 * t) (2 * √3 * dk * t ^ 3 - 2 * dy2 * t ^ 2) (dx1 * t + dx2 * t ^ 2) (2
      * √3 * dk * t ^ 3 - dy2 * t ^ 2) ∈ Icc (-64813 / 500000 : ℝ) (88897 / 500000 : ℝ) ∧
    √3 * dk * t ^ 3 - dy1 * t / 2 - dy2 * t ^ 2 ∈ Icc (-377 / 40000 : ℝ) (1913 / 62500 : ℝ) := by
  unfold angD radD
  have h1 := iconst (2 : ℝ)
  have h2 := ipow (lo := 3441 / 100000) (hi := 48621 / 1000000) (n := 2) ht
    (by norm_num) (by norm_num) (by norm_num)
  have h3 := ipow (lo := 6383 / 1000000) (hi := 10721 / 1000000) (n := 3) ht
    (by norm_num) (by norm_num) (by norm_num)
  have h4 := imul (lo := -17199 / 100000) (hi := -123637 / 1000000) hdx1 ht
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h5 := imul (lo := 433 / 125) (hi := 17321 / 5000) h1 hq
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h6 := imul (lo := 52289 / 100000) (hi := 202009 / 250000) h5 hdk
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h7 := imul (lo := 3337 / 1000000) (hi := 8663 / 1000000) h6 h3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h8 := imul (lo := 0) (hi := 0) h1 hdy2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h9 := imul (lo := 0) (hi := 0) h8 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h10 := isub (lo := 3337 / 1000000) (hi := 8663 / 1000000) h7 h9
    (by norm_num) (by norm_num)
  have h11 := imul (lo := -17199 / 100000) (hi := -123637 / 1000000) hdx1 ht
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h12 := imul (lo := 0) (hi := 0) hdx2 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h13 := iadd (lo := -17199 / 100000) (hi := -123637 / 1000000) h11 h12
    (by norm_num) (by norm_num)
  have h14 := imul (lo := 0) (hi := 0) hdy2 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h15 := isub (lo := 3337 / 1000000) (hi := 8663 / 1000000) h7 h14
    (by norm_num) (by norm_num)
  have h16 := imul (lo := 52289 / 200000) (hi := 202009 / 500000) hq hdk
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h17 := imul (lo := 417 / 250000) (hi := 1083 / 250000) h16 h3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h18 := imul (lo := -52551 / 1000000) (hi := 11093 / 500000) hdy1 ht
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h19 := idiv (lo := -6569 / 250000) (hi := 11093 / 1000000) h18 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have h20 := isub (lo := -377 / 40000) (hi := 1913 / 62500) h17 h19
    (by norm_num) (by norm_num)
  have h21 := imul (lo := 0) (hi := 0) hdy2 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h22 := isub (lo := -377 / 40000) (hi := 1913 / 62500) h20 h21
    (by norm_num) (by norm_num)
  have h23 := iconst (2 : ℝ)
  have h24 := isq_nonpos (lo := 661699 / 1000000) (hi := 197241 / 250000) hu0
    (by norm_num) (by norm_num) (by norm_num)
  have h25 := ipow (lo := 30207 / 250000) (hi := 132611 / 1000000) (n := 2) hv0
    (by norm_num) (by norm_num) (by norm_num)
  have h26 := isq_nonpos (lo := 140547 / 1000000) (hi := 12921 / 62500) hu1
    (by norm_num) (by norm_num) (by norm_num)
  have h27 := ipow (lo := 8209 / 1000000) (hi := 4961 / 500000) (n := 2) hv1
    (by norm_num) (by norm_num) (by norm_num)
  have h28 := iadd (lo := 782527 / 1000000) (hi := 36863 / 40000) h24 h25
    (by norm_num) (by norm_num)
  have h29 := iadd (lo := 37189 / 250000) (hi := 108329 / 500000) h26 h27
    (by norm_num) (by norm_num)
  have h30 := imul (lo := -3939 / 1000000) (hi := -1251 / 1000000) hu1 h15
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h31 := imul (lo := -4283 / 250000) (hi := -5601 / 500000) hv1 h13
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h32 := isub (lo := 7263 / 1000000) (hi := 15881 / 1000000) h30 h31
    (by norm_num) (by norm_num)
  have h33 := idiv (lo := 16761 / 500000) (hi := 106759 / 1000000) h32 h29
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have h34 := imul (lo := -1539 / 200000) (hi := -1357 / 500000) hu0 h10
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h35 := imul (lo := -7829 / 125000) (hi := -1343 / 31250) hv0 h4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h36 := isub (lo := 35281 / 1000000) (hi := 29959 / 500000) h34 h35
    (by norm_num) (by norm_num)
  have h37 := idiv (lo := 38283 / 1000000) (hi := 7657 / 100000) h36 h28
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have h38 := imul (lo := 46351 / 1000000) (hi := 78201 / 1000000) hu1 h13
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h39 := imul (lo := 151 / 500000) (hi := 863 / 1000000) hv1 h15
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h40 := iadd (lo := 46653 / 1000000) (hi := 9883 / 125000) h38 h39
    (by norm_num) (by norm_num)
  have h41 := imul (lo := 46653 / 500000) (hi := 9883 / 62500) h23 h40
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h42 := imul (lo := 25143 / 250000) (hi := 2387 / 15625) hu0 h4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h43 := imul (lo := 1159 / 1000000) (hi := 631 / 200000) hv0 h10
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h44 := iadd (lo := 101731 / 1000000) (hi := 155923 / 1000000) h42 h43
    (by norm_num) (by norm_num)
  have h45 := imul (lo := 101731 / 500000) (hi := 155923 / 500000) h23 h44
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h46 := imul (lo := 36507 / 500000) (hi := 145727 / 1000000) h41 h28
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h47 := imul (lo := 37189 / 125000) (hi := 108329 / 250000) h23 h29
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h48 := imul (lo := 15133 / 250000) (hi := 16891 / 125000) h47 h45
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h49 := isub (lo := -31057 / 500000) (hi := 17039 / 200000) h46 h48
    (by norm_num) (by norm_num)
  have h50 := ipow (lo := 479179 / 1000000) (hi := 156539 / 200000) (n := 3) h28
    (by norm_num) (by norm_num) (by norm_num)
  have h51 := idiv (lo := -64813 / 500000) (hi := 88897 / 500000) h49 h50
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  exact ⟨h33, h37, h51, h22⟩

/-- The derivatives in the direction `2` (generated interval chain). -/
theorem lip_dir2 {u0 v0 u1 v1 t dx1 dy1 dx2 dy2 dk : ℝ}
    (hu0 : u0 ∈ Icc (-222059 / 250000 : ℝ) (-813449 / 1000000 : ℝ))
    (hv0 : v0 ∈ Icc (86901 / 250000 : ℝ) (364157 / 1000000 : ℝ))
    (hu1 : u1 ∈ Icc (-227341 / 500000 : ℝ) (-374897 / 1000000 : ℝ))
    (hv1 : v1 ∈ Icc (22651 / 250000 : ℝ) (49803 / 500000 : ℝ))
    (ht : t ∈ Icc (371 / 2000 : ℝ) (441 / 2000 : ℝ))
    (hq : √3 ∈ Icc (433 / 250 : ℝ) (17321 / 10000 : ℝ))
    (hdx1 : dx1 ∈ Icc (666507 / 1000000 : ℝ) (39 / 50 : ℝ))
    (hdy1 : dy1 ∈ Icc (-100613 / 1000000 : ℝ) (119163 / 500000 : ℝ))
    (hdx2 : dx2 ∈ Icc (40687 / 200000 : ℝ) (299273 / 1000000 : ℝ))
    (hdy2 : dy2 ∈ Icc (3077 / 200000 : ℝ) (57093 / 500000 : ℝ))
    (hdk : dk ∈ Icc (0 : ℝ) (0 : ℝ))
    :
    angD u1 v1 (dx1 * t + dx2 * t ^ 2) (2 * √3 * dk * t ^ 3 - dy2 * t ^ 2) ∈ Icc (-123579 /
      1000000 : ℝ) (-1719 / 40000 : ℝ) ∧
    angD u0 v0 (dx1 * t) (2 * √3 * dk * t ^ 3 - 2 * dy2 * t ^ 2) ∈ Icc (-3947 / 50000 : ℝ) (-3593
      / 100000 : ℝ) ∧
    radD u0 v0 u1 v1 (dx1 * t) (2 * √3 * dk * t ^ 3 - 2 * dy2 * t ^ 2) (dx1 * t + dx2 * t ^ 2) (2
      * √3 * dk * t ^ 3 - dy2 * t ^ 2) ∈ Icc (-203037 / 1000000 : ℝ) (123497 / 1000000 : ℝ) ∧
    √3 * dk * t ^ 3 - dy1 * t / 2 - dy2 * t ^ 2 ∈ Icc (-7957 / 250000 : ℝ) (2641 / 250000 :
      ℝ) := by
  unfold angD radD
  have h1 := iconst (2 : ℝ)
  have h2 := ipow (lo := 3441 / 100000) (hi := 48621 / 1000000) (n := 2) ht
    (by norm_num) (by norm_num) (by norm_num)
  have h3 := ipow (lo := 6383 / 1000000) (hi := 10721 / 1000000) (n := 3) ht
    (by norm_num) (by norm_num) (by norm_num)
  have h4 := imul (lo := 123637 / 1000000) (hi := 17199 / 100000) hdx1 ht
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h5 := imul (lo := 433 / 125) (hi := 17321 / 5000) h1 hq
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h6 := imul (lo := 0) (hi := 0) h5 hdk
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h7 := imul (lo := 0) (hi := 0) h6 h3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h8 := imul (lo := 3077 / 100000) (hi := 57093 / 250000) h1 hdy2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h9 := imul (lo := 529 / 500000) (hi := 347 / 31250) h8 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h10 := isub (lo := -347 / 31250) (hi := -529 / 500000) h7 h9
    (by norm_num) (by norm_num)
  have h11 := imul (lo := 123637 / 1000000) (hi := 17199 / 100000) hdx1 ht
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h12 := imul (lo := 7 / 1000) (hi := 14551 / 1000000) hdx2 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h13 := iadd (lo := 130637 / 1000000) (hi := 186541 / 1000000) h11 h12
    (by norm_num) (by norm_num)
  have h14 := imul (lo := 529 / 1000000) (hi := 347 / 62500) hdy2 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h15 := isub (lo := -347 / 62500) (hi := -529 / 1000000) h7 h14
    (by norm_num) (by norm_num)
  have h16 := imul (lo := 0) (hi := 0) hq hdk
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h17 := imul (lo := 0) (hi := 0) h16 h3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h18 := imul (lo := -11093 / 500000) (hi := 52551 / 1000000) hdy1 ht
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h19 := idiv (lo := -11093 / 1000000) (hi := 6569 / 250000) h18 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have h20 := isub (lo := -6569 / 250000) (hi := 11093 / 1000000) h17 h19
    (by norm_num) (by norm_num)
  have h21 := imul (lo := 529 / 1000000) (hi := 347 / 62500) hdy2 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h22 := isub (lo := -7957 / 250000) (hi := 2641 / 250000) h20 h21
    (by norm_num) (by norm_num)
  have h23 := iconst (2 : ℝ)
  have h24 := isq_nonpos (lo := 661699 / 1000000) (hi := 197241 / 250000) hu0
    (by norm_num) (by norm_num) (by norm_num)
  have h25 := ipow (lo := 30207 / 250000) (hi := 132611 / 1000000) (n := 2) hv0
    (by norm_num) (by norm_num) (by norm_num)
  have h26 := isq_nonpos (lo := 140547 / 1000000) (hi := 12921 / 62500) hu1
    (by norm_num) (by norm_num) (by norm_num)
  have h27 := ipow (lo := 8209 / 1000000) (hi := 4961 / 500000) (n := 2) hv1
    (by norm_num) (by norm_num) (by norm_num)
  have h28 := iadd (lo := 782527 / 1000000) (hi := 36863 / 40000) h24 h25
    (by norm_num) (by norm_num)
  have h29 := iadd (lo := 37189 / 250000) (hi := 108329 / 500000) h26 h27
    (by norm_num) (by norm_num)
  have h30 := imul (lo := 99 / 500000) (hi := 101 / 40000) hu1 h15
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h31 := imul (lo := 2959 / 250000) (hi := 18581 / 1000000) hv1 h13
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h32 := isub (lo := -18383 / 1000000) (hi := -9311 / 1000000) h30 h31
    (by norm_num) (by norm_num)
  have h33 := idiv (lo := -123579 / 1000000) (hi := -1719 / 40000) h32 h29
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have h34 := imul (lo := 43 / 50000) (hi := 9863 / 1000000) hu0 h10
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h35 := imul (lo := 1343 / 31250) (hi := 7829 / 125000) hv0 h4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h36 := isub (lo := -15443 / 250000) (hi := -33113 / 1000000) h34 h35
    (by norm_num) (by norm_num)
  have h37 := idiv (lo := -3947 / 50000) (hi := -3593 / 100000) h36 h28
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have h38 := imul (lo := -84817 / 1000000) (hi := -1959 / 40000) hu1 h13
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h39 := imul (lo := -277 / 500000) (hi := -47 / 1000000) hv1 h15
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h40 := iadd (lo := -85371 / 1000000) (hi := -24511 / 500000) h38 h39
    (by norm_num) (by norm_num)
  have h41 := imul (lo := -85371 / 500000) (hi := -24511 / 250000) h23 h40
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h42 := imul (lo := -2387 / 15625) (hi := -25143 / 250000) hu0 h4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h43 := imul (lo := -1011 / 250000) (hi := -367 / 1000000) hv0 h10
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h44 := iadd (lo := -39203 / 250000) (hi := -100939 / 1000000) h42 h43
    (by norm_num) (by norm_num)
  have h45 := imul (lo := -39203 / 125000) (hi := -100939 / 500000) h23 h44
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h46 := imul (lo := -19669 / 125000) (hi := -38361 / 500000) h41 h28
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h47 := imul (lo := 37189 / 125000) (hi := 108329 / 250000) h23 h29
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h48 := imul (lo := -135899 / 1000000) (hi := -60061 / 1000000) h47 h45
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h49 := isub (lo := -97291 / 1000000) (hi := 59177 / 1000000) h46 h48
    (by norm_num) (by norm_num)
  have h50 := ipow (lo := 479179 / 1000000) (hi := 156539 / 200000) (n := 3) h28
    (by norm_num) (by norm_num) (by norm_num)
  have h51 := idiv (lo := -203037 / 1000000) (hi := 123497 / 1000000) h49 h50
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  exact ⟨h33, h37, h51, h22⟩

/-- The derivatives in the time variable `σ` (generated interval chain). -/
theorem lip_dirσ {u0 v0 u1 v1 t x1 y1 x2 y2 k : ℝ}
    (hu0 : u0 ∈ Icc (-222059 / 250000 : ℝ) (-813449 / 1000000 : ℝ))
    (hv0 : v0 ∈ Icc (86901 / 250000 : ℝ) (364157 / 1000000 : ℝ))
    (hu1 : u1 ∈ Icc (-227341 / 500000 : ℝ) (-374897 / 1000000 : ℝ))
    (hv1 : v1 ∈ Icc (22651 / 250000 : ℝ) (49803 / 500000 : ℝ))
    (ht : t ∈ Icc (371 / 2000 : ℝ) (441 / 2000 : ℝ))
    (hq : √3 ∈ Icc (433 / 250 : ℝ) (17321 / 10000 : ℝ))
    (hx1 : x1 ∈ Icc (-100613 / 1000000 : ℝ) (119163 / 500000 : ℝ))
    (hy1 : y1 ∈ Icc (-39 / 50 : ℝ) (-666507 / 1000000 : ℝ))
    (hx2 : x2 ∈ Icc (3077 / 200000 : ℝ) (57093 / 500000 : ℝ))
    (hy2 : y2 ∈ Icc (-299273 / 1000000 : ℝ) (-40687 / 200000 : ℝ))
    (hk : k ∈ Icc (123 / 10000 : ℝ) (46337 / 1000000 : ℝ))
    :
    angD u1 v1 (x1 + 2 * x2 * t) (6 * √3 * k * t ^ 2 - 2 * y2 * t) ∈ Icc (-668283 / 1000000 : ℝ)
      (-11821 / 125000 : ℝ) ∧
    angD u0 v0 x1 (6 * √3 * k * t ^ 2 - 4 * y2 * t) ∈ Icc (-27319 / 62500 : ℝ) (-48681 / 500000 :
      ℝ) ∧
    radD u0 v0 u1 v1 x1 (6 * √3 * k * t ^ 2 - 4 * y2 * t) (x1 + 2 * x2 * t) (6 * √3 * k * t ^ 2 -
      2 * y2 * t) ∈ Icc (-51747 / 62500 : ℝ) (255363 / 500000 : ℝ) ∧
    3 * √3 * k * t ^ 2 - y1 / 2 - 2 * y2 * t ∈ Icc (205463 / 500000 : ℝ) (66711 / 125000 :
      ℝ) := by
  unfold angD radD
  have h1 := iconst (2 : ℝ)
  have h2 := ipow (lo := 3441 / 100000) (hi := 48621 / 1000000) (n := 2) ht
    (by norm_num) (by norm_num) (by norm_num)
  have h3 := iconst (6 : ℝ)
  have h4 := imul (lo := 1299 / 125) (hi := 51963 / 5000) h3 hq
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h5 := imul (lo := 127821 / 1000000) (hi := 240781 / 500000) h4 hk
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h6 := imul (lo := 2199 / 500000) (hi := 4683 / 200000) h5 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h7 := iconst (4 : ℝ)
  have h8 := imul (lo := -299273 / 250000) (hi := -40687 / 50000) h7 hy2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h9 := imul (lo := -263959 / 1000000) (hi := -37737 / 250000) h8 ht
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h10 := isub (lo := 77673 / 500000) (hi := 143687 / 500000) h6 h9
    (by norm_num) (by norm_num)
  have h11 := imul (lo := 3077 / 100000) (hi := 57093 / 250000) h1 hx2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h12 := imul (lo := 5707 / 1000000) (hi := 50357 / 1000000) h11 ht
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h13 := iadd (lo := -47453 / 500000) (hi := 288683 / 1000000) hx1 h12
    (by norm_num) (by norm_num)
  have h14 := imul (lo := -299273 / 500000) (hi := -40687 / 100000) h1 hy2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h15 := imul (lo := -6599 / 50000) (hi := -37737 / 500000) h14 ht
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h16 := isub (lo := 1248 / 15625) (hi := 31079 / 200000) h6 h15
    (by norm_num) (by norm_num)
  have h17 := iconst (3 : ℝ)
  have h18 := imul (lo := 1299 / 250) (hi := 51963 / 10000) h17 hq
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h19 := imul (lo := 6391 / 100000) (hi := 240781 / 1000000) h18 hk
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h20 := imul (lo := 2199 / 1000000) (hi := 2927 / 250000) h19 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h21 := idiv (lo := -39 / 100) (hi := -333253 / 1000000) hy1 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have h22 := isub (lo := 83863 / 250000) (hi := 100427 / 250000) h20 h21
    (by norm_num) (by norm_num)
  have h23 := imul (lo := -299273 / 500000) (hi := -40687 / 100000) h1 hy2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h24 := imul (lo := -6599 / 50000) (hi := -37737 / 500000) h23 ht
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h25 := isub (lo := 205463 / 500000) (hi := 66711 / 125000) h22 h24
    (by norm_num) (by norm_num)
  have h26 := iconst (2 : ℝ)
  have h27 := isq_nonpos (lo := 661699 / 1000000) (hi := 197241 / 250000) hu0
    (by norm_num) (by norm_num) (by norm_num)
  have h28 := ipow (lo := 30207 / 250000) (hi := 132611 / 1000000) (n := 2) hv0
    (by norm_num) (by norm_num) (by norm_num)
  have h29 := isq_nonpos (lo := 140547 / 1000000) (hi := 12921 / 62500) hu1
    (by norm_num) (by norm_num) (by norm_num)
  have h30 := ipow (lo := 8209 / 1000000) (hi := 4961 / 500000) (n := 2) hv1
    (by norm_num) (by norm_num) (by norm_num)
  have h31 := iadd (lo := 782527 / 1000000) (hi := 36863 / 40000) h27 h28
    (by norm_num) (by norm_num)
  have h32 := iadd (lo := 37189 / 250000) (hi := 108329 / 500000) h29 h30
    (by norm_num) (by norm_num)
  have h33 := imul (lo := -1104 / 15625) (hi := -29943 / 1000000) hu1 h16
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h34 := imul (lo := -4727 / 500000) (hi := 5751 / 200000) hv1 h13
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h35 := isub (lo := -99411 / 1000000) (hi := -20489 / 1000000) h33 h34
    (by norm_num) (by norm_num)
  have h36 := idiv (lo := -668283 / 1000000) (hi := -11821 / 125000) h35 h32
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have h37 := imul (lo := -31907 / 125000) (hi := -63183 / 500000) hu0 h10
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h38 := imul (lo := -36639 / 1000000) (hi := 86789 / 1000000) hv0 hx1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h39 := isub (lo := -68409 / 200000) (hi := -89727 / 1000000) h37 h38
    (by norm_num) (by norm_num)
  have h40 := idiv (lo := -27319 / 62500) (hi := -48681 / 500000) h39 h31
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have h41 := imul (lo := -131259 / 1000000) (hi := 43153 / 1000000) hu1 h13
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h42 := imul (lo := 1809 / 250000) (hi := 15479 / 1000000) hv1 h16
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h43 := iadd (lo := -124023 / 1000000) (hi := 7329 / 125000) h41 h42
    (by norm_num) (by norm_num)
  have h44 := imul (lo := -124023 / 500000) (hi := 7329 / 62500) h26 h43
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h45 := imul (lo := -21169 / 100000) (hi := 89369 / 1000000) hu0 hx1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h46 := imul (lo := 26999 / 500000) (hi := 2093 / 20000) hv0 h10
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h47 := iadd (lo := -39423 / 250000) (hi := 194019 / 1000000) h45 h46
    (by norm_num) (by norm_num)
  have h48 := imul (lo := -39423 / 125000) (hi := 194019 / 500000) h26 h47
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h49 := imul (lo := -228593 / 1000000) (hi := 27017 / 250000) h44 h31
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h50 := imul (lo := 37189 / 125000) (hi := 108329 / 250000) h26 h32
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h51 := imul (lo := -136661 / 1000000) (hi := 10509 / 62500) h50 h48
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h52 := isub (lo := -396737 / 1000000) (hi := 244729 / 1000000) h49 h51
    (by norm_num) (by norm_num)
  have h53 := ipow (lo := 479179 / 1000000) (hi := 156539 / 200000) (n := 3) h31
    (by norm_num) (by norm_num) (by norm_num)
  have h54 := idiv (lo := -51747 / 62500) (hi := 255363 / 500000) h52 h53
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  exact ⟨h36, h40, h54, h25⟩

/-- The bracket `[σlo, σhi]` of the root `σ = 1/τ` (generated interval chain). -/
theorem lip_bracket {y1 y2 k : ℝ}
    (hy1 : y1 ∈ Icc (-39 / 50 : ℝ) (-666507 / 1000000 : ℝ))
    (hy2 : y2 ∈ Icc (-299273 / 1000000 : ℝ) (-40687 / 200000 : ℝ))
    (hk : k ∈ Icc (123 / 10000 : ℝ) (46337 / 1000000 : ℝ))
    (hq : √3 ∈ Icc (433 / 250 : ℝ) (17321 / 10000 : ℝ))
    :
    nF y1 y2 k (371 / 2000) < 0 ∧
    0 < nF y1 y2 k (441 / 2000) := by
  unfold nF
  have h1 := iconst (371 / 2000 : ℝ)
  have h2 := iconst (2 : ℝ)
  have h3 := imul (lo := 21303 / 1000000) (hi := 80261 / 1000000) hq hk
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h4 := ipow (lo := 6383 / 1000000) (hi := 399 / 62500) (n := 3) h1
    (by norm_num) (by norm_num) (by norm_num)
  have h5 := imul (lo := 27 / 200000) (hi := 513 / 1000000) h3 h4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h6 := imul (lo := -14469 / 100000) (hi := -123637 / 1000000) hy1 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h7 := idiv (lo := -14469 / 200000) (hi := -30909 / 500000) h6 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have h8 := isub (lo := 61953 / 1000000) (hi := 36429 / 500000) h5 h7
    (by norm_num) (by norm_num)
  have h9 := ipow (lo := 3441 / 100000) (hi := 34411 / 1000000) (n := 2) h1
    (by norm_num) (by norm_num) (by norm_num)
  have h10 := imul (lo := -10299 / 1000000) (hi := -7 / 1000) hy2 h9
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h11 := isub (lo := 68953 / 1000000) (hi := 83157 / 1000000) h8 h10
    (by norm_num) (by norm_num)
  have h12 := iconst (1 / 12 : ℝ)
  have h13 := isub (lo := -14381 / 1000000) (hi := -11 / 62500) h11 h12
    (by norm_num) (by norm_num)
  have h14 := iconst (441 / 2000 : ℝ)
  have h15 := iconst (2 : ℝ)
  have h16 := imul (lo := 21303 / 1000000) (hi := 80261 / 1000000) hq hk
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h17 := ipow (lo := 67 / 6250) (hi := 10721 / 1000000) (n := 3) h14
    (by norm_num) (by norm_num) (by norm_num)
  have h18 := imul (lo := 57 / 250000) (hi := 861 / 1000000) h16 h17
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h19 := imul (lo := -17199 / 100000) (hi := -36741 / 250000) hy1 h14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h20 := idiv (lo := -17199 / 200000) (hi := -36741 / 500000) h19 h15
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have h21 := isub (lo := 7371 / 100000) (hi := 10857 / 125000) h18 h20
    (by norm_num) (by norm_num)
  have h22 := ipow (lo := 2431 / 50000) (hi := 48621 / 1000000) (n := 2) h14
    (by norm_num) (by norm_num) (by norm_num)
  have h23 := imul (lo := -14551 / 1000000) (hi := -9891 / 1000000) hy2 h22
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h24 := isub (lo := 83601 / 1000000) (hi := 101407 / 1000000) h21 h23
    (by norm_num) (by norm_num)
  have h25 := iconst (1 / 12 : ℝ)
  have h26 := isub (lo := 267 / 1000000) (hi := 9037 / 500000) h24 h25
    (by norm_num) (by norm_num)
  exact ⟨h13.2.trans_lt (by norm_num), lt_of_lt_of_le (by norm_num) h26.1⟩

/-- A difference of intervals. -/
theorem lip_sub0 {a b : ℝ}
    (ha : a ∈ Icc (-192289 / 1000000 : ℝ) (-5281 / 200000 : ℝ))
    (hb : b ∈ Icc (-16003 / 125000 : ℝ) (-30171 / 1000000 : ℝ))
    :
    a - b ∈ Icc (-81059 / 500000 : ℝ) (101619 / 1000000 : ℝ) := by
  have h1 := isub (lo := -81059 / 500000) (hi := 101619 / 1000000) ha hb
    (by norm_num) (by norm_num)
  exact h1

/-- A difference of intervals. -/
theorem lip_sub1 {a b : ℝ}
    (ha : a ∈ Icc (16761 / 500000 : ℝ) (106759 / 1000000 : ℝ))
    (hb : b ∈ Icc (38283 / 1000000 : ℝ) (7657 / 100000 : ℝ))
    :
    a - b ∈ Icc (-5381 / 125000 : ℝ) (17119 / 250000 : ℝ) := by
  have h1 := isub (lo := -5381 / 125000) (hi := 17119 / 250000) ha hb
    (by norm_num) (by norm_num)
  exact h1

/-- A difference of intervals. -/
theorem lip_sub2 {a b : ℝ}
    (ha : a ∈ Icc (-123579 / 1000000 : ℝ) (-1719 / 40000 : ℝ))
    (hb : b ∈ Icc (-3947 / 50000 : ℝ) (-3593 / 100000 : ℝ))
    :
    a - b ∈ Icc (-87649 / 1000000 : ℝ) (7193 / 200000 : ℝ) := by
  have h1 := isub (lo := -87649 / 1000000) (hi := 7193 / 200000) ha hb
    (by norm_num) (by norm_num)
  exact h1

/-- A difference of intervals. -/
theorem lip_subs {a b : ℝ}
    (ha : a ∈ Icc (-668283 / 1000000 : ℝ) (-11821 / 125000 : ℝ))
    (hb : b ∈ Icc (-27319 / 62500 : ℝ) (-48681 / 500000 : ℝ))
    :
    a - b ∈ Icc (-570921 / 1000000 : ℝ) (42817 / 125000 : ℝ) := by
  have h1 := isub (lo := -570921 / 1000000) (hi := 42817 / 125000) ha hb
    (by norm_num) (by norm_num)
  exact h1

/-- A combination `|q - e α/β|`. -/
theorem lip_comboθ0 {q e α β : ℝ}
    (hq : q ∈ Icc (-192289 / 1000000 : ℝ) (-5281 / 200000 : ℝ))
    (he : e ∈ Icc (-668283 / 1000000 : ℝ) (-11821 / 125000 : ℝ))
    (hα : α ∈ Icc (-39039 / 500000 : ℝ) (-9437 / 250000 : ℝ))
    (hβ : β ∈ Icc (205463 / 500000 : ℝ) (66711 / 125000 : ℝ))
    :
    |q - e * α / β| ≤ 319269 / 1000000 := by
  have h1 := imul (lo := 3569 / 1000000) (hi := 52179 / 1000000) he hα
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := idiv (lo := 6687 / 1000000) (hi := 6349 / 50000) h1 hβ
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have h3 := isub (lo := -319269 / 1000000) (hi := -8273 / 250000) hq h2
    (by norm_num) (by norm_num)
  exact iabs h3 (by norm_num) (by norm_num)

/-- A combination `|q - e α/β|`. -/
theorem lip_comboψ0 {q e α β : ℝ}
    (hq : q ∈ Icc (-81059 / 500000 : ℝ) (101619 / 1000000 : ℝ))
    (he : e ∈ Icc (-570921 / 1000000 : ℝ) (42817 / 125000 : ℝ))
    (hα : α ∈ Icc (-39039 / 500000 : ℝ) (-9437 / 250000 : ℝ))
    (hβ : β ∈ Icc (205463 / 500000 : ℝ) (66711 / 125000 : ℝ))
    :
    |q - e * α / β| ≤ 135299 / 500000 := by
  have h1 := imul (lo := -5349 / 200000) (hi := 44577 / 1000000) he hα
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := idiv (lo := -13017 / 200000) (hi := 339 / 3125) h1 hβ
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have h3 := isub (lo := -135299 / 500000) (hi := 10419 / 62500) hq h2
    (by norm_num) (by norm_num)
  exact iabs h3 (by norm_num) (by norm_num)

/-- A combination `|q - e α/β|`. -/
theorem lip_combor0 {q e α β : ℝ}
    (hq : q ∈ Icc (-245621 / 1000000 : ℝ) (69517 / 500000 : ℝ))
    (he : e ∈ Icc (-51747 / 62500 : ℝ) (255363 / 500000 : ℝ))
    (hα : α ∈ Icc (-39039 / 500000 : ℝ) (-9437 / 250000 : ℝ))
    (hβ : β ∈ Icc (205463 / 500000 : ℝ) (66711 / 125000 : ℝ))
    :
    |q - e * α / β| ≤ 402937 / 1000000 := by
  have h1 := imul (lo := -39877 / 1000000) (hi := 12929 / 200000) he hα
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := idiv (lo := -48521 / 500000) (hi := 39329 / 250000) h1 hβ
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have h3 := isub (lo := -402937 / 1000000) (hi := 59019 / 250000) hq h2
    (by norm_num) (by norm_num)
  exact iabs h3 (by norm_num) (by norm_num)

/-- A combination `|q - e α/β|`. -/
theorem lip_comboθ1 {q e α β : ℝ}
    (hq : q ∈ Icc (16761 / 500000 : ℝ) (106759 / 1000000 : ℝ))
    (he : e ∈ Icc (-668283 / 1000000 : ℝ) (-11821 / 125000 : ℝ))
    (hα : α ∈ Icc (-377 / 40000 : ℝ) (1913 / 62500 : ℝ))
    (hβ : β ∈ Icc (205463 / 500000 : ℝ) (66711 / 125000 : ℝ))
    :
    |q - e * α / β| ≤ 156537 / 1000000 := by
  have h1 := imul (lo := -4091 / 200000) (hi := 6299 / 1000000) he hα
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := idiv (lo := -24889 / 500000) (hi := 15329 / 1000000) h1 hβ
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have h3 := isub (lo := 18193 / 1000000) (hi := 156537 / 1000000) hq h2
    (by norm_num) (by norm_num)
  exact iabs h3 (by norm_num) (by norm_num)

/-- A combination `|q - e α/β|`. -/
theorem lip_comboψ1 {q e α β : ℝ}
    (hq : q ∈ Icc (-5381 / 125000 : ℝ) (17119 / 250000 : ℝ))
    (he : e ∈ Icc (-570921 / 1000000 : ℝ) (42817 / 125000 : ℝ))
    (hα : α ∈ Icc (-377 / 40000 : ℝ) (1913 / 62500 : ℝ))
    (hβ : β ∈ Icc (205463 / 500000 : ℝ) (66711 / 125000 : ℝ))
    :
    |q - e * α / β| ≤ 55501 / 500000 := by
  have h1 := imul (lo := -699 / 40000) (hi := 2097 / 200000) he hα
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := idiv (lo := -21263 / 500000) (hi := 6379 / 250000) h1 hβ
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have h3 := isub (lo := -17141 / 250000) (hi := 55501 / 500000) hq h2
    (by norm_num) (by norm_num)
  exact iabs h3 (by norm_num) (by norm_num)

/-- A combination `|q - e α/β|`. -/
theorem lip_combor1 {q e α β : ℝ}
    (hq : q ∈ Icc (-64813 / 500000 : ℝ) (88897 / 500000 : ℝ))
    (he : e ∈ Icc (-51747 / 62500 : ℝ) (255363 / 500000 : ℝ))
    (hα : α ∈ Icc (-377 / 40000 : ℝ) (1913 / 62500 : ℝ))
    (hβ : β ∈ Icc (205463 / 500000 : ℝ) (66711 / 125000 : ℝ))
    :
    |q - e * α / β| ≤ 47893 / 200000 := by
  have h1 := imul (lo := -12671 / 500000) (hi := 15633 / 1000000) he hα
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := idiv (lo := -61671 / 1000000) (hi := 9511 / 250000) h1 hβ
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have h3 := isub (lo := -16767 / 100000) (hi := 47893 / 200000) hq h2
    (by norm_num) (by norm_num)
  exact iabs h3 (by norm_num) (by norm_num)

/-- A combination `|q - e α/β|`. -/
theorem lip_comboθ2 {q e α β : ℝ}
    (hq : q ∈ Icc (-123579 / 1000000 : ℝ) (-1719 / 40000 : ℝ))
    (he : e ∈ Icc (-668283 / 1000000 : ℝ) (-11821 / 125000 : ℝ))
    (hα : α ∈ Icc (-7957 / 250000 : ℝ) (2641 / 250000 : ℝ))
    (hβ : β ∈ Icc (205463 / 500000 : ℝ) (66711 / 125000 : ℝ))
    :
    |q - e * α / β| ≤ 175343 / 1000000 := by
  have h1 := imul (lo := -353 / 50000) (hi := 21271 / 1000000) he hα
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := idiv (lo := -17181 / 1000000) (hi := 12941 / 250000) h1 hβ
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have h3 := isub (lo := -175343 / 1000000) (hi := -12897 / 500000) hq h2
    (by norm_num) (by norm_num)
  exact iabs h3 (by norm_num) (by norm_num)

/-- A combination `|q - e α/β|`. -/
theorem lip_comboψ2 {q e α β : ℝ}
    (hq : q ∈ Icc (-87649 / 1000000 : ℝ) (7193 / 200000 : ℝ))
    (he : e ∈ Icc (-570921 / 1000000 : ℝ) (42817 / 125000 : ℝ))
    (hα : α ∈ Icc (-7957 / 250000 : ℝ) (2641 / 250000 : ℝ))
    (hβ : β ∈ Icc (205463 / 500000 : ℝ) (66711 / 125000 : ℝ))
    :
    |q - e * α / β| ≤ 4121 / 31250 := by
  have h1 := imul (lo := -10903 / 1000000) (hi := 4543 / 250000) he hα
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := idiv (lo := -26533 / 1000000) (hi := 44223 / 1000000) h1 hβ
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have h3 := isub (lo := -4121 / 31250) (hi := 31249 / 500000) hq h2
    (by norm_num) (by norm_num)
  exact iabs h3 (by norm_num) (by norm_num)

/-- A combination `|q - e α/β|`. -/
theorem lip_combor2 {q e α β : ℝ}
    (hq : q ∈ Icc (-203037 / 1000000 : ℝ) (123497 / 1000000 : ℝ))
    (he : e ∈ Icc (-51747 / 62500 : ℝ) (255363 / 500000 : ℝ))
    (hα : α ∈ Icc (-7957 / 250000 : ℝ) (2641 / 250000 : ℝ))
    (hβ : β ∈ Icc (205463 / 500000 : ℝ) (66711 / 125000 : ℝ))
    :
    |q - e * α / β| ≤ 8349 / 31250 := by
  have h1 := imul (lo := -254 / 15625) (hi := 26353 / 1000000) he hα
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := idiv (lo := -989 / 25000) (hi := 64131 / 1000000) h1 hβ
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have h3 := isub (lo := -8349 / 31250) (hi := 163057 / 1000000) hq h2
    (by norm_num) (by norm_num)
  exact iabs h3 (by norm_num) (by norm_num)

end SmoothedPolygons.TriFuller.DOutAnalytic
