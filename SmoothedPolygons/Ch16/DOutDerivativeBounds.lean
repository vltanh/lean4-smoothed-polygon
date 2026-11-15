module

public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The derivative bounds of the contraction, by hand

Bounds on the partial derivatives of the Fuller–Poincaré map near `q_out`, for the Lipschitz bound
of `DOutContracts` (`lipschitzOnWith_gmap`, `SmoothedPolygons/Ch16/DOutContraction.lean`) on the
box `B` of `SmoothedPolygons/Ch16/DOutImages.lean`. The argument fits on a page: every number below
is obtained from numbers above it by a product of two intervals or a sum, and can be checked by
hand.

**Setting.** For `p = (r, ψ, θ) ∈ B` (`r = r₂`, `θ = θ₂`) let `x₁ + i y₁ = (1 - r) e^{iφ₁}`,
`x₂ + i y₂ = r e^{iφ₂}` (`φ₁ = θ - ψ + 2π/3`, `φ₂ = θ + 2π/3`) and `κ = r (1 - r) sin ψ`. For
`σ > 0` let `X₁ = x₁ σ`, `X₂ = x₂ σ²`, `W₂ = -y₂ σ²`, `W₃ = √3 κ σ³` and
* `a = u₀ + i v₀ = (X₁ - √3/2) + i (1/3 + 2 W₂ + 2 W₃)` (`nu0`, `nv0`),
* `b = u₁ + i v₁ = (X₁ + X₂ - √3/4) + i (1/12 + W₂ + 2 W₃)` (`nu1`, `nv1`),
* `F = √3 κ σ³ - y₁ σ/2 - y₂ σ² - 1/12` (`nF`).

At the root `σ(p)` of `F` (`σ = 1/τ`, `τ` the switching time), `a = w₁/τ` and `b = w₂/τ²` for the
image `w = ζ F(z)`, and the coordinates of `g(p)` are, up to constants, `θ₂' = arg b`,
`ψ' = arg b - arg a` and `log H(r₂') = log |b|² - 2 log |a|²`, `H(r) = (r/(1 - r)²)²`
(`gmap_spec`, `log_MM`). So a partial derivative `∂` of a coordinate of `g` is a combination of
the logarithmic derivatives `∂b/b` and `∂a/a`:
`∂θ₂' = Im (∂b/b)`, `∂ψ' = Im (∂b/b) - Im (∂a/a)`, `∂ log H(r₂') = 2 Re (∂b/b) - 4 Re (∂a/a)`,
where for `z = u + i v`, `δ = du + i dv`: `Im (δ/z) = angD u v du dv = (u dv - v du)/(u² + v²)`
and `Re (δ/z) = radD u v du dv = (u du + v dv)/(u² + v²)`.

**Step 1: ranges on `B × [0.185, 0.221]`.** By monotonicity of `sin` and `cos` (`box_trig`):
`cos φ₁ ∈ [-0.129, 0.3056]`, `sin φ₁ ∈ [-1, -0.952]`, `cos φ₂ ∈ [0.0699, 0.3807]`,
`sin φ₂ ∈ [-0.9976, -0.9247]`, `sin ψ ∈ [25/313, 20/101]`, `cos ψ ∈ [99/101, 312/313]`; and
`r (1 - r) ∈ [0.1716, 0.21]` (`r (1 - r) - 0.1716 = (r - 0.22) (0.78 - r)`,
`0.21 - r (1 - r) = (0.3 - r) (0.7 - r)`). A product `x y` of two intervals lies between the
products of the endpoints (`mul_mem_Icc`); this gives (`coef_ranges`) `x₁ ∈ [-0.101, 0.239]`,
`y₁ ∈ [-0.78, -0.666]`, `x₂ ∈ [0.0153, 0.115]`, `y₂ ∈ [-0.3, -0.203]`, `κ ∈ [0.0137, 0.0416]`,
`(1 - 2r) sin ψ ∈ [0.0319, 0.111]`, `r (1 - r) cos ψ ∈ [0, 0.21]`. With `σ² ∈ [0.0342, 0.0489]`,
`σ³ ∈ [0.00633, 0.0108]` (`pow_ranges`) and `√3 ∈ [1.732, 1.7321]`: `X₁ ∈ [-0.0224, 0.0529]`,
`X₂ ∈ [0.0005, 0.0057]`, `W₂ ∈ [0.0069, 0.0147]`, `W₃ ∈ [0.00015, 0.00078]`, hence
(`uv_ranges`, `UVBox`) `u₀ ∈ [-0.889, -0.813]`, `v₀ ∈ [0.347, 0.365]`, `u₁ ∈ [-0.455, -0.374]`,
`v₁ ∈ [0.09, 0.1]`.

**Step 2: the root.** `F` is increasing in `σ ≥ 0` (`nF_mono`), and (`sigma_bracket`)
`F(0.185) ≤ 1.7321·0.0416·0.185³ + 0.78·0.185/2 + 0.3·0.185² - 1/12 < -0.0004`,
`F(0.221) ≥ 1.732·0.0137·0.221³ + 0.666·0.221/2 + 0.203·0.221² - 1/12 > 0.0004`;
so `σ(p) ∈ [0.185, 0.221]` (`sig_spec`).

**Step 3: the partial derivatives** of `u₀, v₀, u₁, v₁, F` on `B × [0.185, 0.221]`. In a direction
`∂ = ∂_r, ∂_ψ, ∂_θ` at fixed `σ`: `∂u₀ = σ ∂x₁`, `∂v₀ = 2√3 σ³ ∂κ - 2 σ² ∂y₂`,
`∂u₁ = σ ∂x₁ + σ² ∂x₂`, `∂v₁ = 2√3 σ³ ∂κ - σ² ∂y₂`, `∂F = √3 σ³ ∂κ - σ ∂y₁/2 - σ² ∂y₂`, where
`(∂x₁, ∂y₁, ∂x₂, ∂y₂, ∂κ)` is `(-cos φ₁, -sin φ₁, cos φ₂, sin φ₂, (1 - 2r) sin ψ)` for `r`,
`(y₁, -x₁, 0, 0, r (1 - r) cos ψ)` for `ψ` and `(-y₁, x₁, -y₂, x₂, 0)` for `θ`. In `σ` at fixed
`p`: `∂u₀ = x₁`, `∂v₀ = 6√3 κ σ² - 4 y₂ σ`, `∂u₁ = x₁ + 2 x₂ σ`, `∂v₁ = 6√3 κ σ² - 2 y₂ σ`,
`∂F = 3√3 κ σ² - y₁/2 - 2 y₂ σ`. By Step 1 (`dir_r`, `dir_psi`, `dir_theta`, `dir_sigma`):

| | `∂u₀` | `∂v₀` | `∂u₁` | `∂v₁` |
|---|---|---|---|---|
| `r` | [-0.0676, 0.0286] | [0.0638, 0.1018] | [-0.0653, 0.0473] | [0.0322, 0.053] |
| `ψ` | [-0.1724, -0.1232] | [0, 0.00786] | [-0.1724, -0.1232] | [0, 0.00786] |
| `θ` | [0.1232, 0.1724] | [-0.0114, -0.001] | [0.1301, 0.1871] | [-0.0057, -0.0005] |
| `σ` | [-0.101, 0.239] | [0.154, 0.2864] | [-0.0954, 0.29] | [0.0798, 0.1538] |

and `∂_r F ∈ [-0.0786, -0.0371]`, `∂_ψ F ∈ [-0.0112, 0.0304]`, `∂_θ F ∈ [-0.0322, 0.0107]`,
`∂_σ F ≥ 0.41`.

**Step 4: the logarithmic derivatives.** If `u ≤ -m < 0 ≤ v ≤ M`, `|du| ≤ A`, `|dv| ≤ B`, then
`|Im (δ/z)| ≤ (B + (M/m) A)/m` and `|Re (δ/z)| ≤ (A + (M/m) B)/m` (`abs_angD_le`,
`abs_radD_le`: `|u dv - v du| ≤ |u| B + M A`, and `u² + v² ≥ u² ≥ m |u|`, `≥ m²`). With
`(m, M) = (0.374, 0.1)` for `b` and `(0.813, 0.365)` for `a`, the table of Step 3 gives
`|Im (∂b/b)|, |Im (∂a/a)| ≤ A` and `|2 Re (∂b/b) - 4 Re (∂a/a)| ≤ R` (`entry`) with

| | `r` | `ψ` | `θ` | `σ` |
|---|---|---|---|---|
| `A` | 0.19 | 0.145 | 0.15 | 0.62 |
| `R` | 1 | 1.8 | 1.9 | 3.6 |
| sign of `Im (∂b/b)` and `Im (∂a/a)` | `≤ 0` | `≥ 0` | `≤ 0` | `≤ 0` |

(for instance `(0.1538 + (0.1/0.374)·0.29)/0.374 < 0.619` for `Im (∂_σ b/b)`). The sign of
`Im (δ/z)` is that of `u dv - v du`, in which one product dominates: `u dv` for `r` and `σ`
(`u₁ ∂_r v₁ ≤ -0.374·0.0322 < -0.012 < -0.1·0.0653 ≤ v₁ ∂_r u₁`, and so on), `v du` for `ψ` and
`θ` (`v₁ ∂_θ u₁ ≥ 0.09·0.1301 > 0.0117 > 0.455·0.0057 ≥ u₁ ∂_θ v₁`, and so on). As the two angles
move the same way, `|Im (∂b/b) - Im (∂a/a)| ≤ A` too (`abs_sub_le_of_same_sign`).

**Step 5: the rows.** By the implicit mean value theorem (`abs_sub_le_sum_of_implicit`) with
`|q - e α/β| ≤ |q| + |e| |α|/β` (`abs_sub_mul_div_le`), `θ₂'` and `ψ'` satisfy
`|Δ| ≤ Σ_j L_j |Δp_j|` with `L_j = A_j + 0.62 |∂_j F|/0.41` (`j = r, ψ, θ`; about
`0.309, 0.191, 0.199`, sum `< 0.699`), and `log H(r₂')` with `R_j + 3.6 |∂_j F|/0.41` (about
`1.69, 2.07, 2.18`, sum `< 5.94`). Since `(log H)'(r) = 2/r + 4/(1 - r) ≥ 6 + 4` on
`[0.22, 0.3]`, `r₂'` has `1/10` of these (sum `< 0.594`). All three row sums are `< 3/4`.

The interval chain of about 330 steps that this file replaces is kept, as a reference no longer used
by the Lean proof, in `numerics/generators/dout_contraction_bounds.py`.
-/

@[expose] public section

namespace SmoothedPolygons.TriFuller.DOutAnalytic

open Set

/-! ### The normalized image and its logarithmic derivatives -/

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

/-- `Im (δ/z) = (u dv - v du)/(u² + v²)` for `z = u + i v`, `δ = du + i dv`: the derivative of
`arctan (v/u)`. -/
noncomputable def angD (u v du dv : ℝ) : ℝ := (u * dv - v * du) / (u ^ 2 + v ^ 2)

/-- `Re (δ/z) = (u du + v dv)/(u² + v²)`: the derivative of `log √(u² + v²)`. -/
noncomputable def radD (u v du dv : ℝ) : ℝ := (u * du + v * dv) / (u ^ 2 + v ^ 2)

/-! ### Elementary estimates -/

/-- **The product of two intervals**: `x y` lies between the products of the endpoints. -/
theorem mul_mem_Icc {x y a b c d lo hi : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d)
    (h : (lo ≤ a * c ∧ lo ≤ a * d ∧ lo ≤ b * c ∧ lo ≤ b * d) ∧
      (a * c ≤ hi ∧ a * d ≤ hi ∧ b * c ≤ hi ∧ b * d ≤ hi)) : x * y ∈ Icc lo hi := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  obtain ⟨⟨h1, h2, h3, h4⟩, h5, h6, h7, h8⟩ := h
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

theorem abs_le_of_mem_Icc {x a b c : ℝ} (hx : x ∈ Icc a b) (ha : -c ≤ a) (hb : b ≤ c) :
    |x| ≤ c :=
  abs_le.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- The quotient of `N` with `|N| ≤ |u| X + M Y` by `u² + v²`, for `u ≤ -m < 0 ≤ v ≤ M`:
`u² + v² ≥ u² ≥ m |u|` and `≥ m²`. -/
theorem abs_div_normSq_le {u v N X Y m M : ℝ} (hm : 0 < m) (hu : u ≤ -m) (hv : 0 ≤ v)
    (hvM : v ≤ M) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hN : |N| ≤ -u * X + M * Y) :
    |N / (u ^ 2 + v ^ 2)| ≤ (X + M / m * Y) / m := by
  have hM : 0 ≤ M := hv.trans hvM
  have hmu : m ≤ -u := by linarith
  have hu' : 0 < -u := hm.trans_le hmu
  have hD : 0 < u ^ 2 + v ^ 2 := by nlinarith [mul_pos hu' hu', sq_nonneg v]
  rw [abs_div, abs_of_pos hD, div_le_iff₀ hD]
  have hc : 0 ≤ (X + M / m * Y) / m := by positivity
  have h1 : -u ≤ u ^ 2 / m := by
    rw [le_div_iff₀ hm]; nlinarith [mul_le_mul_of_nonneg_left hmu hu'.le]
  have h2 : 1 ≤ u ^ 2 / m ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; nlinarith [mul_le_mul hmu hmu hm.le hu'.le]
  have e : (X + M / m * Y) / m * u ^ 2 = X * (u ^ 2 / m) + M * Y * (u ^ 2 / m ^ 2) := by
    field_simp
  have key : -u * X + M * Y ≤ (X + M / m * Y) / m * u ^ 2 := by
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left h1 hX, mul_le_mul_of_nonneg_left h2 (mul_nonneg hM hY)]
  nlinarith [mul_nonneg hc (sq_nonneg v)]

/-- **The angular part of `δ/z`**: `|Im (δ/z)| ≤ (B + (M/m) A)/m` for `u ≤ -m < 0 ≤ v ≤ M`,
`|du| ≤ A`, `|dv| ≤ B`. -/
theorem abs_angD_le {u v du dv m M A B : ℝ} (hm : 0 < m) (hu : u ≤ -m) (hv : 0 ≤ v)
    (hvM : v ≤ M) (hA : |du| ≤ A) (hB : |dv| ≤ B) : |angD u v du dv| ≤ (B + M / m * A) / m := by
  unfold angD
  refine abs_div_normSq_le hm hu hv hvM ((abs_nonneg _).trans hB) ((abs_nonneg _).trans hA) ?_
  have hu0 : 0 ≤ -u := by linarith
  calc |u * dv - v * du| ≤ |u * dv| + |v * du| := abs_sub _ _
    _ = -u * |dv| + v * |du| := by
        rw [abs_mul, abs_mul, abs_of_neg (show u < 0 by linarith), abs_of_nonneg hv]
    _ ≤ -u * B + M * A := by
        nlinarith [mul_le_mul_of_nonneg_left hB hu0,
          mul_le_mul hvM hA (abs_nonneg du) (hv.trans hvM)]

/-- **The radial part of `δ/z`**: `|Re (δ/z)| ≤ (A + (M/m) B)/m`. -/
theorem abs_radD_le {u v du dv m M A B : ℝ} (hm : 0 < m) (hu : u ≤ -m) (hv : 0 ≤ v)
    (hvM : v ≤ M) (hA : |du| ≤ A) (hB : |dv| ≤ B) : |radD u v du dv| ≤ (A + M / m * B) / m := by
  unfold radD
  refine abs_div_normSq_le hm hu hv hvM ((abs_nonneg _).trans hA) ((abs_nonneg _).trans hB) ?_
  have hu0 : 0 ≤ -u := by linarith
  calc |u * du + v * dv| ≤ |u * du| + |v * dv| := abs_add_le _ _
    _ = -u * |du| + v * |dv| := by
        rw [abs_mul, abs_mul, abs_of_neg (show u < 0 by linarith), abs_of_nonneg hv]
    _ ≤ -u * A + M * B := by
        nlinarith [mul_le_mul_of_nonneg_left hA hu0,
          mul_le_mul hvM hB (abs_nonneg dv) (hv.trans hvM)]

/-- Two numbers of the same sign: `|x - y| ≤ max |x| |y|`. -/
theorem abs_sub_le_of_same_sign {x y A : ℝ} (h : (x ≤ 0 ∧ y ≤ 0) ∨ (0 ≤ x ∧ 0 ≤ y))
    (hx : |x| ≤ A) (hy : |y| ≤ A) : |x - y| ≤ A := by
  rw [abs_le] at *
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- **The combination of the implicit mean value theorem**: `|q - e α/β| ≤ A + E P/β₀` for
`|q| ≤ A`, `|e| ≤ E`, `|α| ≤ P`, `β ≥ β₀ > 0`. -/
theorem abs_sub_mul_div_le {q e α β A E P β₀ : ℝ} (hq : |q| ≤ A) (he : |e| ≤ E) (hα : |α| ≤ P)
    (hβ₀ : 0 < β₀) (hβ : β₀ ≤ β) : |q - e * α / β| ≤ A + E * P / β₀ := by
  have hβ0 : 0 < β := hβ₀.trans_le hβ
  have hE : 0 ≤ E := (abs_nonneg e).trans he
  have h1 : |e * α / β| ≤ E * P / β₀ := by
    rw [abs_div, abs_mul, abs_of_pos hβ0]
    calc |e| * |α| / β ≤ E * P / β := by gcongr
      _ ≤ E * P / β₀ := by
          have : 0 ≤ E * P := mul_nonneg hE ((abs_nonneg α).trans hα)
          gcongr
  calc |q - e * α / β| ≤ |q| + |e * α / β| := abs_sub _ _
    _ ≤ A + E * P / β₀ := add_le_add hq h1

/-! ### Step 1: ranges on `B × [0.185, 0.221]` -/

/-- **The coefficients on `B`** (`x₁`, `y₁`, `x₂`, `y₂`, `κ` and the derivatives of `κ`). -/
theorem coef_ranges {r c1 s1 c2 s2 sψ cψ : ℝ} (hr : r ∈ Icc (11 / 50) (3 / 10))
    (hc1 : c1 ∈ Icc (-0.129) 0.3056) (hs1 : s1 ∈ Icc (-1) (-0.952))
    (hc2 : c2 ∈ Icc 0.0699 0.3807) (hs2 : s2 ∈ Icc (-0.9976) (-0.9247))
    (hsψ : sψ ∈ Icc (25 / 313) (20 / 101)) (hcψ : cψ ∈ Icc (99 / 101) (312 / 313)) :
    (1 - r) * c1 ∈ Icc (-0.101) 0.239 ∧ (1 - r) * s1 ∈ Icc (-0.78) (-0.666) ∧
      r * c2 ∈ Icc 0.0153 0.115 ∧ r * s2 ∈ Icc (-0.3) (-0.203) ∧
      (1 - r) * r * sψ ∈ Icc 0.0137 0.0416 ∧ (1 - 2 * r) * sψ ∈ Icc 0.0319 0.111 ∧
      (1 - r) * r * cψ ∈ Icc 0 0.21 := by
  have hr1 : 1 - r ∈ Icc (0.7 : ℝ) 0.78 := ⟨by linarith [hr.2], by linarith [hr.1]⟩
  have hr2 : 1 - 2 * r ∈ Icc (0.4 : ℝ) 0.56 := ⟨by linarith [hr.2], by linarith [hr.1]⟩
  have hrr : (1 - r) * r ∈ Icc (0.1716 : ℝ) 0.21 := by
    obtain ⟨a, b⟩ := hr
    constructor <;> nlinarith
  exact ⟨mul_mem_Icc hr1 hc1 (by norm_num), mul_mem_Icc hr1 hs1 (by norm_num),
    mul_mem_Icc hr hc2 (by norm_num), mul_mem_Icc hr hs2 (by norm_num),
    mul_mem_Icc hrr hsψ (by norm_num), mul_mem_Icc hr2 hsψ (by norm_num),
    mul_mem_Icc hrr hcψ (by norm_num)⟩

theorem pow_ranges {t : ℝ} (ht : t ∈ Icc 0.185 0.221) :
    t ^ 2 ∈ Icc 0.0342 0.0489 ∧ t ^ 3 ∈ Icc 0.00633 0.0108 := by
  obtain ⟨a, b⟩ := ht
  have h0 : (0 : ℝ) ≤ 0.185 := by norm_num
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · nlinarith [pow_le_pow_left₀ h0 a 2]
  · nlinarith [pow_le_pow_left₀ (h0.trans a) b 2]
  · nlinarith [pow_le_pow_left₀ h0 a 3]
  · nlinarith [pow_le_pow_left₀ (h0.trans a) b 3]

theorem sqrt_three_mem : √3 ∈ Icc (1.732 : ℝ) 1.7321 := by
  constructor
  · rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  · exact (Real.sqrt_lt' (by norm_num)).2 (by norm_num) |>.le

/-- The ranges of `u₀, v₀, u₁, v₁` on `B × [0.185, 0.221]`. -/
def UVBox (u0 v0 u1 v1 : ℝ) : Prop :=
  u0 ∈ Icc (-0.889) (-0.813) ∧ v0 ∈ Icc 0.347 0.365 ∧ u1 ∈ Icc (-0.455) (-0.374) ∧
    v1 ∈ Icc 0.09 0.1

/-- **The normalized image on `B × [0.185, 0.221]`**, through `X₁ = x₁ σ ∈ [-0.0224, 0.0529]`,
`X₂ = x₂ σ² ∈ [0.0005, 0.0057]`, `W₂ = -y₂ σ² ∈ [0.0069, 0.0147]`,
`W₃ = √3 κ σ³ ∈ [0.00015, 0.00078]`. -/
theorem uv_ranges {x1 x2 y2 k t : ℝ} (hx1 : x1 ∈ Icc (-0.101) 0.239)
    (hx2 : x2 ∈ Icc 0.0153 0.115) (hy2 : y2 ∈ Icc (-0.3) (-0.203)) (hk : k ∈ Icc 0.0137 0.0416)
    (ht : t ∈ Icc 0.185 0.221) :
    UVBox (nu0 x1 t) (nv0 y2 k t) (nu1 x1 x2 t) (nv1 y2 k t) := by
  obtain ⟨t2, t3⟩ := pow_ranges ht
  have hq := sqrt_three_mem
  have X1 := mul_mem_Icc (lo := -0.0224) (hi := 0.0529) hx1 ht (by norm_num)
  have X2 := mul_mem_Icc (lo := 0.0005) (hi := 0.0057) hx2 t2 (by norm_num)
  have W2 := mul_mem_Icc (lo := -0.0147) (hi := -0.0069) hy2 t2 (by norm_num)
  have qk := mul_mem_Icc (lo := 0.0237) (hi := 0.07206) hq hk (by norm_num)
  have W3 := mul_mem_Icc (lo := 0.00015) (hi := 0.00078) qk t3 (by norm_num)
  obtain ⟨q1, q2⟩ := hq
  unfold UVBox nu0 nv0 nu1 nv1
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    linarith [X1.1, X1.2, X2.1, X2.2, W2.1, W2.2, W3.1, W3.2]

/-! ### Step 2: the root -/

/-- **The bracket of the root `σ = 1/τ`**: `F(0.185) < 0 < F(0.221)`. -/
theorem sigma_bracket {y1 y2 k : ℝ} (hy1 : y1 ∈ Icc (-0.78) (-0.666))
    (hy2 : y2 ∈ Icc (-0.3) (-0.203)) (hk : k ∈ Icc 0.0137 0.0416) :
    nF y1 y2 k 0.185 < 0 ∧ 0 < nF y1 y2 k 0.221 := by
  have qk := mul_mem_Icc (lo := 0.0237) (hi := 0.07206) sqrt_three_mem hk (by norm_num)
  unfold nF
  obtain ⟨a1, b1⟩ := hy1
  obtain ⟨a2, b2⟩ := hy2
  obtain ⟨a3, b3⟩ := qk
  constructor <;> norm_num <;> nlinarith

/-! ### Steps 3 and 4: the partial derivatives and the logarithmic derivatives -/

/-- **One column of the derivative bounds**: from the ranges of `u₀, v₀, u₁, v₁` and bounds
`|du₀| ≤ a₀`, `|dv₀| ≤ b₀`, `|du₁| ≤ a₁`, `|dv₁| ≤ b₁` of a direction in which the two angles
move the same way: `|Im (δb/b)|`, `|Im (δb/b) - Im (δa/a)| ≤ A` and
`|2 Re (δb/b) - 4 Re (δa/a)| ≤ R`. -/
theorem entry {u0 v0 u1 v1 du0 dv0 du1 dv1 a0 b0 a1 b1 A R : ℝ} (huv : UVBox u0 v0 u1 v1)
    (ha0 : |du0| ≤ a0) (hb0 : |dv0| ≤ b0) (ha1 : |du1| ≤ a1) (hb1 : |dv1| ≤ b1)
    (hs : (u1 * dv1 - v1 * du1 ≤ 0 ∧ u0 * dv0 - v0 * du0 ≤ 0) ∨
      (0 ≤ u1 * dv1 - v1 * du1 ∧ 0 ≤ u0 * dv0 - v0 * du0))
    (hA : (b1 + 0.1 / 0.374 * a1) / 0.374 ≤ A ∧ (b0 + 0.365 / 0.813 * a0) / 0.813 ≤ A)
    (hR : 2 * ((a1 + 0.1 / 0.374 * b1) / 0.374) + 4 * ((a0 + 0.365 / 0.813 * b0) / 0.813) ≤ R) :
    |angD u1 v1 du1 dv1| ≤ A ∧ |angD u1 v1 du1 dv1 - angD u0 v0 du0 dv0| ≤ A ∧
      |2 * radD u1 v1 du1 dv1 - 4 * radD u0 v0 du0 dv0| ≤ R := by
  obtain ⟨⟨-, hu0⟩, ⟨hv0, hv0'⟩, ⟨-, hu1⟩, ⟨hv1, hv1'⟩⟩ := huv
  have i1 := (abs_angD_le (by norm_num) hu1 (by linarith) hv1' ha1 hb1).trans hA.1
  have i0 := (abs_angD_le (by norm_num) hu0 (by linarith) hv0' ha0 hb0).trans hA.2
  have r1 := abs_radD_le (by norm_num) hu1 (by linarith) hv1' ha1 hb1
  have r0 := abs_radD_le (by norm_num) hu0 (by linarith) hv0' ha0 hb0
  have hD1 : 0 ≤ u1 ^ 2 + v1 ^ 2 := by positivity
  have hD0 : 0 ≤ u0 ^ 2 + v0 ^ 2 := by positivity
  refine ⟨i1, abs_sub_le_of_same_sign ?_ i1 i0, ?_⟩
  · unfold angD
    rcases hs with ⟨h1, h0⟩ | ⟨h1, h0⟩
    · exact Or.inl ⟨div_nonpos_of_nonpos_of_nonneg h1 hD1, div_nonpos_of_nonpos_of_nonneg h0 hD0⟩
    · exact Or.inr ⟨div_nonneg h1 hD1, div_nonneg h0 hD0⟩
  · calc |2 * radD u1 v1 du1 dv1 - 4 * radD u0 v0 du0 dv0|
        ≤ |2 * radD u1 v1 du1 dv1| + |4 * radD u0 v0 du0 dv0| := abs_sub _ _
      _ = 2 * |radD u1 v1 du1 dv1| + 4 * |radD u0 v0 du0 dv0| := by
          rw [abs_mul, abs_mul, abs_two, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      _ ≤ R := by linarith

/-- **The direction `r`**: `(∂x₁, ∂y₁, ∂x₂, ∂y₂, ∂κ) = (-cos φ₁, -sin φ₁, cos φ₂, sin φ₂,
(1 - 2r) sin ψ)`; both angles decrease (`u ∂v` dominates). -/
theorem dir_r {u0 v0 u1 v1 t dx1 dy1 dx2 dy2 dk : ℝ} (huv : UVBox u0 v0 u1 v1)
    (ht : t ∈ Icc 0.185 0.221) (hdx1 : dx1 ∈ Icc (-0.3056) 0.129) (hdy1 : dy1 ∈ Icc 0.952 1)
    (hdx2 : dx2 ∈ Icc 0.0699 0.3807) (hdy2 : dy2 ∈ Icc (-0.9976) (-0.9247))
    (hdk : dk ∈ Icc 0.0319 0.111) :
    |angD u1 v1 (dx1 * t + dx2 * t ^ 2) (2 * √3 * dk * t ^ 3 - dy2 * t ^ 2)| ≤ 0.19 ∧
    |angD u1 v1 (dx1 * t + dx2 * t ^ 2) (2 * √3 * dk * t ^ 3 - dy2 * t ^ 2) -
      angD u0 v0 (dx1 * t) (2 * √3 * dk * t ^ 3 - 2 * dy2 * t ^ 2)| ≤ 0.19 ∧
    |2 * radD u1 v1 (dx1 * t + dx2 * t ^ 2) (2 * √3 * dk * t ^ 3 - dy2 * t ^ 2) -
      4 * radD u0 v0 (dx1 * t) (2 * √3 * dk * t ^ 3 - 2 * dy2 * t ^ 2)| ≤ 1 ∧
    |√3 * dk * t ^ 3 - dy1 * t / 2 - dy2 * t ^ 2| ≤ 0.0786 := by
  obtain ⟨t2, t3⟩ := pow_ranges ht
  have P1 := mul_mem_Icc (lo := -0.0676) (hi := 0.0286) hdx1 ht (by norm_num)
  have P2 := mul_mem_Icc (lo := 0.0023) (hi := 0.0187) hdx2 t2 (by norm_num)
  have P3 := mul_mem_Icc (lo := 0.176) (hi := 0.221) hdy1 ht (by norm_num)
  have P4 := mul_mem_Icc (lo := -0.0488) (hi := -0.0316) hdy2 t2 (by norm_num)
  have qk := mul_mem_Icc (lo := 0.0552) (hi := 0.19227) sqrt_three_mem hdk (by norm_num)
  have P5 := mul_mem_Icc (lo := 0.00034) (hi := 0.00208) qk t3 (by norm_num)
  have du0 : dx1 * t ∈ Icc (-0.0676) 0.0286 := P1
  have dv0 : 2 * √3 * dk * t ^ 3 - 2 * dy2 * t ^ 2 ∈ Icc 0.0638 0.1018 :=
    ⟨by linarith [P4.2, P5.1], by linarith [P4.1, P5.2]⟩
  have du1 : dx1 * t + dx2 * t ^ 2 ∈ Icc (-0.0653) 0.0473 :=
    ⟨by linarith [P1.1, P2.1], by linarith [P1.2, P2.2]⟩
  have dv1 : 2 * √3 * dk * t ^ 3 - dy2 * t ^ 2 ∈ Icc 0.0322 0.053 :=
    ⟨by linarith [P4.2, P5.1], by linarith [P4.1, P5.2]⟩
  have dF : √3 * dk * t ^ 3 - dy1 * t / 2 - dy2 * t ^ 2 ∈ Icc (-0.0786) (-0.0371) :=
    ⟨by linarith [P3.2, P4.2, P5.1], by linarith [P3.1, P4.1, P5.2]⟩
  have n1 := mul_mem_Icc (lo := -0.0242) (hi := -0.012) huv.2.2.1 dv1 (by norm_num)
  have n2 := mul_mem_Icc (lo := -0.0066) (hi := 0.0048) huv.2.2.2 du1 (by norm_num)
  have n3 := mul_mem_Icc (lo := -0.0906) (hi := -0.0518) huv.1 dv0 (by norm_num)
  have n4 := mul_mem_Icc (lo := -0.0247) (hi := 0.0105) huv.2.1 du0 (by norm_num)
  obtain ⟨h1, h2, h3⟩ := entry huv (abs_le_of_mem_Icc (c := 0.0676) du0 (by norm_num) (by norm_num))
    (abs_le_of_mem_Icc (c := 0.1018) dv0 (by norm_num) (by norm_num))
    (abs_le_of_mem_Icc (c := 0.0653) du1 (by norm_num) (by norm_num))
    (abs_le_of_mem_Icc (c := 0.053) dv1 (by norm_num) (by norm_num))
    (Or.inl ⟨by linarith [n1.2, n2.1], by linarith [n3.2, n4.1]⟩) (A := 0.19) (R := 1)
    (by norm_num) (by norm_num)
  exact ⟨h1, h2, h3, abs_le_of_mem_Icc (c := 0.0786) dF (by norm_num) (by norm_num)⟩

/-- **The direction `ψ`**: `(∂x₁, ∂y₁, ∂x₂, ∂y₂, ∂κ) = (y₁, -x₁, 0, 0, r (1 - r) cos ψ)`; both
angles increase (`-v ∂u` dominates). -/
theorem dir_psi {u0 v0 u1 v1 t dx1 dy1 dx2 dy2 dk : ℝ} (huv : UVBox u0 v0 u1 v1)
    (ht : t ∈ Icc 0.185 0.221) (hdx1 : dx1 ∈ Icc (-0.78) (-0.666))
    (hdy1 : dy1 ∈ Icc (-0.239) 0.101) (hdx2 : dx2 = 0) (hdy2 : dy2 = 0)
    (hdk : dk ∈ Icc 0 0.21) :
    |angD u1 v1 (dx1 * t + dx2 * t ^ 2) (2 * √3 * dk * t ^ 3 - dy2 * t ^ 2)| ≤ 0.145 ∧
    |angD u1 v1 (dx1 * t + dx2 * t ^ 2) (2 * √3 * dk * t ^ 3 - dy2 * t ^ 2) -
      angD u0 v0 (dx1 * t) (2 * √3 * dk * t ^ 3 - 2 * dy2 * t ^ 2)| ≤ 0.145 ∧
    |2 * radD u1 v1 (dx1 * t + dx2 * t ^ 2) (2 * √3 * dk * t ^ 3 - dy2 * t ^ 2) -
      4 * radD u0 v0 (dx1 * t) (2 * √3 * dk * t ^ 3 - 2 * dy2 * t ^ 2)| ≤ 1.8 ∧
    |√3 * dk * t ^ 3 - dy1 * t / 2 - dy2 * t ^ 2| ≤ 0.0304 := by
  subst hdx2 hdy2
  obtain ⟨t2, t3⟩ := pow_ranges ht
  have P1 := mul_mem_Icc (lo := -0.1724) (hi := -0.1232) hdx1 ht (by norm_num)
  have P3 := mul_mem_Icc (lo := -0.0529) (hi := 0.0224) hdy1 ht (by norm_num)
  have qk := mul_mem_Icc (lo := 0) (hi := 0.36375) sqrt_three_mem hdk (by norm_num)
  have P5 := mul_mem_Icc (lo := 0) (hi := 0.00393) qk t3 (by norm_num)
  have du0 : dx1 * t ∈ Icc (-0.1724) (-0.1232) := P1
  have dv0 : 2 * √3 * dk * t ^ 3 - 2 * 0 * t ^ 2 ∈ Icc 0 0.00786 :=
    ⟨by linarith [P5.1], by linarith [P5.2]⟩
  have du1 : dx1 * t + 0 * t ^ 2 ∈ Icc (-0.1724) (-0.1232) :=
    ⟨by linarith [P1.1], by linarith [P1.2]⟩
  have dv1 : 2 * √3 * dk * t ^ 3 - 0 * t ^ 2 ∈ Icc 0 0.00786 :=
    ⟨by linarith [P5.1], by linarith [P5.2]⟩
  have dF : √3 * dk * t ^ 3 - dy1 * t / 2 - 0 * t ^ 2 ∈ Icc (-0.0112) 0.0304 :=
    ⟨by linarith [P3.2, P5.1], by linarith [P3.1, P5.2]⟩
  have n1 := mul_mem_Icc (lo := -0.0036) (hi := 0) huv.2.2.1 dv1 (by norm_num)
  have n2 := mul_mem_Icc (lo := -0.0173) (hi := -0.011) huv.2.2.2 du1 (by norm_num)
  have n3 := mul_mem_Icc (lo := -0.007) (hi := 0) huv.1 dv0 (by norm_num)
  have n4 := mul_mem_Icc (lo := -0.063) (hi := -0.0427) huv.2.1 du0 (by norm_num)
  obtain ⟨h1, h2, h3⟩ := entry huv (abs_le_of_mem_Icc (c := 0.1724) du0 (by norm_num) (by norm_num))
    (abs_le_of_mem_Icc (c := 0.00786) dv0 (by norm_num) (by norm_num))
    (abs_le_of_mem_Icc (c := 0.1724) du1 (by norm_num) (by norm_num))
    (abs_le_of_mem_Icc (c := 0.00786) dv1 (by norm_num) (by norm_num))
    (Or.inr ⟨by linarith [n1.1, n2.2], by linarith [n3.1, n4.2]⟩) (A := 0.145) (R := 1.8)
    (by norm_num) (by norm_num)
  exact ⟨h1, h2, h3, abs_le_of_mem_Icc (c := 0.0304) dF (by norm_num) (by norm_num)⟩

/-- **The direction `θ`**: `(∂x₁, ∂y₁, ∂x₂, ∂y₂, ∂κ) = (-y₁, x₁, -y₂, x₂, 0)`; both angles
decrease (`-v ∂u` dominates). -/
theorem dir_theta {u0 v0 u1 v1 t dx1 dy1 dx2 dy2 dk : ℝ} (huv : UVBox u0 v0 u1 v1)
    (ht : t ∈ Icc 0.185 0.221) (hdx1 : dx1 ∈ Icc 0.666 0.78) (hdy1 : dy1 ∈ Icc (-0.101) 0.239)
    (hdx2 : dx2 ∈ Icc 0.203 0.3) (hdy2 : dy2 ∈ Icc 0.0153 0.115) (hdk : dk = 0) :
    |angD u1 v1 (dx1 * t + dx2 * t ^ 2) (2 * √3 * dk * t ^ 3 - dy2 * t ^ 2)| ≤ 0.15 ∧
    |angD u1 v1 (dx1 * t + dx2 * t ^ 2) (2 * √3 * dk * t ^ 3 - dy2 * t ^ 2) -
      angD u0 v0 (dx1 * t) (2 * √3 * dk * t ^ 3 - 2 * dy2 * t ^ 2)| ≤ 0.15 ∧
    |2 * radD u1 v1 (dx1 * t + dx2 * t ^ 2) (2 * √3 * dk * t ^ 3 - dy2 * t ^ 2) -
      4 * radD u0 v0 (dx1 * t) (2 * √3 * dk * t ^ 3 - 2 * dy2 * t ^ 2)| ≤ 1.9 ∧
    |√3 * dk * t ^ 3 - dy1 * t / 2 - dy2 * t ^ 2| ≤ 0.0322 := by
  subst hdk
  obtain ⟨t2, t3⟩ := pow_ranges ht
  have P1 := mul_mem_Icc (lo := 0.1232) (hi := 0.1724) hdx1 ht (by norm_num)
  have P2 := mul_mem_Icc (lo := 0.0069) (hi := 0.0147) hdx2 t2 (by norm_num)
  have P3 := mul_mem_Icc (lo := -0.0224) (hi := 0.0529) hdy1 ht (by norm_num)
  have P4 := mul_mem_Icc (lo := 0.0005) (hi := 0.0057) hdy2 t2 (by norm_num)
  have du0 : dx1 * t ∈ Icc 0.1232 0.1724 := P1
  have dv0 : 2 * √3 * 0 * t ^ 3 - 2 * dy2 * t ^ 2 ∈ Icc (-0.0114) (-0.001) :=
    ⟨by linarith [P4.2], by linarith [P4.1]⟩
  have du1 : dx1 * t + dx2 * t ^ 2 ∈ Icc 0.1301 0.1871 :=
    ⟨by linarith [P1.1, P2.1], by linarith [P1.2, P2.2]⟩
  have dv1 : 2 * √3 * 0 * t ^ 3 - dy2 * t ^ 2 ∈ Icc (-0.0057) (-0.0005) :=
    ⟨by linarith [P4.2], by linarith [P4.1]⟩
  have dF : √3 * 0 * t ^ 3 - dy1 * t / 2 - dy2 * t ^ 2 ∈ Icc (-0.0322) 0.0107 :=
    ⟨by linarith [P3.2, P4.2], by linarith [P3.1, P4.1]⟩
  have n1 := mul_mem_Icc (lo := 0) (hi := 0.0026) huv.2.2.1 dv1 (by norm_num)
  have n2 := mul_mem_Icc (lo := 0.0117) (hi := 0.0188) huv.2.2.2 du1 (by norm_num)
  have n3 := mul_mem_Icc (lo := 0) (hi := 0.0102) huv.1 dv0 (by norm_num)
  have n4 := mul_mem_Icc (lo := 0.0427) (hi := 0.063) huv.2.1 du0 (by norm_num)
  obtain ⟨h1, h2, h3⟩ := entry huv (abs_le_of_mem_Icc (c := 0.1724) du0 (by norm_num) (by norm_num))
    (abs_le_of_mem_Icc (c := 0.0114) dv0 (by norm_num) (by norm_num))
    (abs_le_of_mem_Icc (c := 0.1871) du1 (by norm_num) (by norm_num))
    (abs_le_of_mem_Icc (c := 0.0057) dv1 (by norm_num) (by norm_num))
    (Or.inl ⟨by linarith [n1.2, n2.1], by linarith [n3.2, n4.1]⟩) (A := 0.15) (R := 1.9)
    (by norm_num) (by norm_num)
  exact ⟨h1, h2, h3, abs_le_of_mem_Icc (c := 0.0322) dF (by norm_num) (by norm_num)⟩

/-- **The direction `σ`** (at fixed `p`): both angles decrease (`u ∂v` dominates), and
`∂_σ F ≥ 0.41`. -/
theorem dir_sigma {u0 v0 u1 v1 t x1 y1 x2 y2 k : ℝ} (huv : UVBox u0 v0 u1 v1)
    (ht : t ∈ Icc 0.185 0.221) (hx1 : x1 ∈ Icc (-0.101) 0.239) (hy1 : y1 ∈ Icc (-0.78) (-0.666))
    (hx2 : x2 ∈ Icc 0.0153 0.115) (hy2 : y2 ∈ Icc (-0.3) (-0.203)) (hk : k ∈ Icc 0.0137 0.0416) :
    |angD u1 v1 (x1 + 2 * x2 * t) (6 * √3 * k * t ^ 2 - 2 * y2 * t)| ≤ 0.62 ∧
    |angD u1 v1 (x1 + 2 * x2 * t) (6 * √3 * k * t ^ 2 - 2 * y2 * t) -
      angD u0 v0 x1 (6 * √3 * k * t ^ 2 - 4 * y2 * t)| ≤ 0.62 ∧
    |2 * radD u1 v1 (x1 + 2 * x2 * t) (6 * √3 * k * t ^ 2 - 2 * y2 * t) -
      4 * radD u0 v0 x1 (6 * √3 * k * t ^ 2 - 4 * y2 * t)| ≤ 3.6 ∧
    0.41 ≤ 3 * √3 * k * t ^ 2 - y1 / 2 - 2 * y2 * t := by
  obtain ⟨t2, -⟩ := pow_ranges ht
  have Q1 := mul_mem_Icc (lo := 0.0028) (hi := 0.0255) hx2 ht (by norm_num)
  have Q2 := mul_mem_Icc (lo := -0.0663) (hi := -0.0375) hy2 ht (by norm_num)
  have qk := mul_mem_Icc (lo := 0.0237) (hi := 0.07206) sqrt_three_mem hk (by norm_num)
  have Q3 := mul_mem_Icc (lo := 0.0008) (hi := 0.00353) qk t2 (by norm_num)
  have dv0 : 6 * √3 * k * t ^ 2 - 4 * y2 * t ∈ Icc 0.154 0.2864 :=
    ⟨by linarith [Q2.2, Q3.1], by linarith [Q2.1, Q3.2]⟩
  have du1 : x1 + 2 * x2 * t ∈ Icc (-0.0954) 0.29 :=
    ⟨by linarith [hx1.1, Q1.1], by linarith [hx1.2, Q1.2]⟩
  have dv1 : 6 * √3 * k * t ^ 2 - 2 * y2 * t ∈ Icc 0.0798 0.1538 :=
    ⟨by linarith [Q2.2, Q3.1], by linarith [Q2.1, Q3.2]⟩
  have n1 := mul_mem_Icc (lo := -0.07) (hi := -0.0298) huv.2.2.1 dv1 (by norm_num)
  have n2 := mul_mem_Icc (lo := -0.0096) (hi := 0.029) huv.2.2.2 du1 (by norm_num)
  have n3 := mul_mem_Icc (lo := -0.2547) (hi := -0.1252) huv.1 dv0 (by norm_num)
  have n4 := mul_mem_Icc (lo := -0.0369) (hi := 0.0873) huv.2.1 hx1 (by norm_num)
  obtain ⟨h1, h2, h3⟩ := entry huv (abs_le_of_mem_Icc (c := 0.239) hx1 (by norm_num) (by norm_num))
    (abs_le_of_mem_Icc (c := 0.2864) dv0 (by norm_num) (by norm_num))
    (abs_le_of_mem_Icc (c := 0.29) du1 (by norm_num) (by norm_num))
    (abs_le_of_mem_Icc (c := 0.1538) dv1 (by norm_num) (by norm_num))
    (Or.inl ⟨by linarith [n1.2, n2.1], by linarith [n3.2, n4.1]⟩) (A := 0.62) (R := 3.6)
    (by norm_num) (by norm_num)
  exact ⟨h1, h2, h3, by linarith [hy1.2, Q2.2, Q3.1]⟩

end SmoothedPolygons.TriFuller.DOutAnalytic
