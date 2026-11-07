module

public import SmoothedPolygons.Ch2.Mahler
public import SmoothedPolygons.Ch2.BalancedDensity
public import SmoothedPolygons.Ch4.StarDomain
public import Basic.Analysis.Calculus.MatrixEntrywise

/-!
# The hexagon of a point of the star domain (Lemmas 5.0.3–5.0.5)

A point `z = x + iy ∈ 𝔥*` determines the matrix `X = Φ(z)` (`det X = 1`, star inequalities
`ρⱼ(X) > 0`), and Remark 3.1.7 (`rem:hexagon`, equation `eqn:hex-vertex`, TeX 2525–2545) builds
from it a centrally symmetric hexagon `H_K(z)` whose edges have midpoints `s_j*` and directions
`X s_j*`: its vertex between `s_j*` and `s_{j+1}*` is

  `p_j = s_j* + ρ_{j+2}(X) X s_j* = s_{j+1}* - ρ_j(X) X s_{j+1}*`      (`hexVertex`),

indices of `ρ` modulo 3 (`starFn`). Chapter 5 (TeX 4029–4083) names the triangles

* `T_i = △ s_i p_i s_{i+1}` (`innerTriangle`, `triArea`), `i = 0, 1, 2`;
* `T_i^ext = △ p_{i+1} q_{i+1} p_{i+2}` (`outerTriangle`, `extTriArea`), where
  `q_j = p_j + 2ρ_j(X) X s_j*` is the intersection of the lines of the two edges adjacent to the
  edge `p_j p_{j+1}` (`hexExtVertex`; TeX 4128: `q₁ = p₁ + 2ρ₁Xs₁ = p₂ - 2ρ₁Xs₃`), so that
  `T₀^ext = △p₁q₁p₂`, `T₁^ext = △p₂q₂p₃`, `T₂^ext = △p₃q₃p₄ = -△p₀q₀p₁`;

areas are Lebesgue measure (`volume.real`). Then (TeX 4185–4199, 4332–4348)

* `h_i = {z ∈ 𝔥* | T_i(z) ≥ T_i^ext(z)}` (`hRegion`), `area_i = T_i - √(T_i^ext T_i)` (`areaFn`),
  and `I_i` the indicator of `h_i` (`Set.indicator (hRegion i) (areaFn i)` is `I_i area_i`);
* `δ(z) = (3√3/2 + 2 Σ_{i=0}^{2} I_i(z) area_i(z))/√12` (`densityBound`), the lower bound of the
  packing density of the balanced disks with critical hexagon `H_K(z)` (Theorem 5.0.6);
* `δ_oct = (8 - √32 - ln 2)/(√8 - 1)` (`octagonDensity`), the packing density of the smoothed
  octagon (the example before Theorem 7.5.6; `smoothedOctagon_volume`,
  `greatestPackingDensity_of_isBalancedPair`).

## Statements and the book's proofs

* **Lemma 5.0.3** (`lemma5_0_3`, `lem:pt-to-hexagon`, TeX 4000–4015). The book's proof: the
  hexagon is reconstructed from `Φ(z)` by Remark 3.1.7. Its second claim, that `H_K(z)` is the
  critical hexagon of `K` at the multi-point `s_j*`, is not argued; it is proved here along the
  lines of Remark 3.1.7 and §2.2. The proof: the identity `X s_j = ρ_j s_{j+1} + ρ_{j+1} s_{j+2}`
  of `eqn:rho-star-inequalities` (`hx_mulVec_sixthRoot`, for every traceless `X`) and
  `ρ_jρ_{j+1} + ρ_{j+1}ρ_{j+2} + ρ_{j+2}ρ_j = det X = 1` (`eqn:det-rho`, `hx_sigma`, with
  `theorem4_4_1` for `det Φ(z) = 1` and the star inequalities `ρ_j > 0`) express every point of the
  construction in the frame `(s_j*, s_{j+1}*)`, where `det(α s_j* + β s_{j+1}*, γ s_j* + δ s_{j+1}*)
  = (αδ - βγ)√3/2`. In that frame the two forms of `eqn:hex-vertex` agree (`hx_edge`:
  `p_j = s_{j+1}* - ρ_j X s_{j+1}*`, `p_{j+1} - p_j = 2ρ_j X s_{j+1}*`), so `s_{j+1}*` is the
  midpoint of `p_j p_{j+1}`; central symmetry and convexity (`IsCSHexagon`) are
  `det(p_j, p_{j+1}) > 0` and `det(p_{j+1} - p_j, p_{j+2} - p_{j+1}) = 4ρ_jρ_{j+1} · √3/2 > 0`; the
  star condition holds with `α = ρ_{j+1}ρ_{j+2}`, `β = ρ_jρ_{j+2}`. For the critical hexagon:
  `g(0) = I` (the `s_j*` span the plane), `g` is differentiable (its columns are combinations of
  `σ₀`, `σ₁`), so `σ_j'(0) = g'(0) s_j* = Φ(z) s_j*` (`hx_deriv_eq`); the line of the edge through
  `s_j*` is the tangent of the boundary curve `σ_j` at `s_j*`, hence a support line of `K`
  (`bdy_det2_deriv_sub_nonneg`, `hx_support`), and `K ⊆ H_K(z)`, the intersection of the six
  half-planes (`rein_mem_hexagonOf_hex3`). The area of `H_K(z)` is
  `4 det(s₁*, s₂*) = 2√3 = √12` (`rein_volume_hexagonOf`; equivalently
  `3√3/2 + 2(T₀ + T₁ + T₂)` by Lemma 5.0.4); and every centrally symmetric hexagon containing `K`
  has area at least `√12`: by Theorem 2.2.2 (`theorem2_2_2`, with
  `ch2_not_isParallelogram_of_isBalancedPair`) a least-area hexagon `H` exists and
  `δ(K) = area(K)/area(H)`, while `δ(K) = area(K)/√12` by E12
  (`greatestPackingDensity_of_isBalancedPair`), so `area(H) = √12`. The critical hexagon of
  Definition 2.3.8 is then Theorem 2.3.9 (`theorem2_3_9`).
* **Lemma 5.0.4** (`lemma5_0_4`, `lem:triangle-areas`, TeX 4087–4151). The book's proof: the
  coordinates of `p_i`, `q_i` from Lemma 5.0.3 and equations (3.1.3), (3.1.6), (3.1.8), (3.1.7)
  with `det X = 1`; e.g. `area(T₀) = ½ det(p₀ - s₀, s₂) = ½ ρ₂ det(Xs₀, s₂) = (√3/4)ρ₀ρ₂` and
  `area(T₀^ext) = -2ρ₁² det(Xs₃, Xs₁) = √3ρ₁²`; the sum is `(√3/4)(ρ₀ρ₂ + ρ₁ρ₂ + ρ₀ρ₁) =
  (√3/4)det X` by (3.1.7). The proof is the book's: the area of a triangle is `|det|/2`
  (`hx_volume_real_triangle`: the triangle is the image of the standard triangle under an affine
  map), and the determinants are computed in the frame of Lemma 5.0.3 (`hx_triArea`:
  `△ s_j* p_j s_{j+1}* = (√3/4) ρ_jρ_{j+2}`; `hx_extTriArea`: `q_j - p_j = 2ρ_j X s_j*`,
  `p_{j+1} - p_j = 2ρ_j X s_{j+1}*` and `det(X s_j*, X s_{j+1}*) = det X · √3/2`, so
  `△ p_j q_j p_{j+1} = √3 ρ_j²`).
* **Lemma 5.0.5** (`lemma5_0_5`, `lem:geom-thales`, TeX 4153–4180). The book's proof: an affine
  map (preserving ratios of areas) reduces to a right angle at `s₁` with `s₀s₁ = s₁p₀ = 1`,
  `s₁r̃₀ = r`, where the identity reads `r/2 = (1 - √((1 - r)²))/2`. The proof carries out this
  reduction with the determinant: every area is `|det|/2` (`hx_volume_real_triangle`); with
  `D = det(s₁ - s₀, p₀ - s₀)`, `r₀ = s₀ + t₁(p₀ - s₀)` and `r̃₀ = s₁ + t₂(p₀ - s₁)`, the parallel
  condition reads `(t₁ - t₂) D = 0`. If `D ≠ 0` then `t₁ = t₂ = t` (the book's `r`), and the areas
  are `△s₀s₁r = t|D|/2`, `△s₀p₀s₁ = |D|/2`, `△r₀p₀r̃₀ = (1 - t)²|D|/2`: the book's identity times
  `|D|`. If `D = 0` the three areas vanish.

Besides the numbered results: `areaFn_nonneg_of_mem_hRegion` (`√(T^ext T) ≤ √(T T) = T` on `h_i`)
and `densityBound_eq` (`√12 = 2√3`).
-/

@[expose] public section

namespace SmoothedPolygons

open MeasureTheory Set Matrix

/-- The star function `ρ_{j mod 3}(X)` (Corollary 3.1.6, `eqn:rho`), indices modulo 3:
`ρ_{j+3} = ρ_j`. -/
noncomputable def starFn (X : Mat2) (j : ZMod 6) : ℝ :=
  match j.val % 3 with
  | 0 => ρ₀ X
  | 1 => ρ₁ X
  | _ => ρ₂ X

/-- The vertex `p_j = s_j* + ρ_{j+2}(X) X s_j*` of the hexagon `H_K(z)` of `z = x + iy`, with
`X = Φ(z)` (`eqn:hex-vertex`, with `det X = 1`): the intersection of the edge lines through
`s_j*` and `s_{j+1}*` with directions `X s_j*` and `X s_{j+1}*`. -/
noncomputable def hexVertex (x y : ℝ) (j : ZMod 6) : Fin 2 → ℝ :=
  sixthRoot j + starFn (Φ x y) (j + 2) • (Φ x y *ᵥ sixthRoot j)

/-- The point `q_j = p_j + 2ρ_j(X) X s_j*` (TeX 4128), the intersection of the lines of the edges
`p_{j-1}p_j` (through `s_j*`) and `p_{j+1}p_{j+2}` (through `s_{j+2}*`), the apex of the exterior
triangle over the edge `p_j p_{j+1}`. -/
noncomputable def hexExtVertex (x y : ℝ) (j : ZMod 6) : Fin 2 → ℝ :=
  hexVertex x y j + (2 * starFn (Φ x y) j) • (Φ x y *ᵥ sixthRoot j)

/-- The interior triangle `T_i = △ s_i* p_i s_{i+1}*` of `H_K(z)` (TeX 4060–4063). -/
noncomputable def innerTriangle (x y : ℝ) (i : Fin 3) : Set (Fin 2 → ℝ) :=
  convexHull ℝ {sixthRoot (i.val : ZMod 6), hexVertex x y (i.val : ZMod 6),
    sixthRoot ((i.val : ZMod 6) + 1)}

/-- The exterior triangle `T_i^ext = △ p_{i+1} q_{i+1} p_{i+2}` of `H_K(z)` (TeX 4063–4070):
`T₀^ext = △p₁q₁p₂`, `T₁^ext = △p₂q₂p₃`, and `T₂^ext = △p₃q₃p₄`, the reflection of the book's
`△p₀q₀p₁`. -/
noncomputable def outerTriangle (x y : ℝ) (i : Fin 3) : Set (Fin 2 → ℝ) :=
  convexHull ℝ {hexVertex x y ((i.val : ZMod 6) + 1), hexExtVertex x y ((i.val : ZMod 6) + 1),
    hexVertex x y ((i.val : ZMod 6) + 2)}

/-- The area `T_i(z)` of the interior triangle `T_i` (Lebesgue measure). -/
noncomputable def triArea (x y : ℝ) (i : Fin 3) : ℝ := volume.real (innerTriangle x y i)

/-- The area `T_i^ext(z)` of the exterior triangle `T_i^ext` (Lebesgue measure). -/
noncomputable def extTriArea (x y : ℝ) (i : Fin 3) : ℝ := volume.real (outerTriangle x y i)

/-- The region `h_i = {z ∈ 𝔥* | T_i(z) ≥ T_i^ext(z)}` (TeX 4187–4191). -/
noncomputable def hRegion (i : Fin 3) : Set (ℝ × ℝ) :=
  {z | z ∈ starDomain ∧ extTriArea z.1 z.2 i ≤ triArea z.1 z.2 i}

/-- The function `area_i(z) = T_i(z) - √(T_i^ext(z) T_i(z))` (TeX 4196–4198). Its product with the
indicator `I_i` of `h_i` is `(hRegion i).indicator (areaFn i)`. -/
noncomputable def areaFn (i : Fin 3) (z : ℝ × ℝ) : ℝ :=
  triArea z.1 z.2 i - √(extTriArea z.1 z.2 i * triArea z.1 z.2 i)

/-- The density bound `δ(z) = (3√3/2 + 2 Σ_{i=0}^{2} I_i(z) area_i(z))/√12` (TeX 4337–4342), a
lower bound for the packing density of every balanced disk with critical hexagon `H_K(z)`
(Theorem 5.0.6). -/
noncomputable def densityBound (z : ℝ × ℝ) : ℝ :=
  (3 * √3 / 2 + 2 * ∑ i : Fin 3, (hRegion i).indicator (areaFn i) z) / √12

/-- `δ_oct = (8 - √32 - ln 2)/(√8 - 1) ≈ 0.902414`, the packing density of the smoothed octagon
(TeX 4344–4346; the example before Theorem 7.5.6, `eqn:density-formula`). -/
noncomputable def octagonDensity : ℝ := (8 - √32 - Real.log 2) / (√8 - 1)

/-! ## Helper lemmas

### Star functions and the identity `X s_j* = ρ_j s_{j+1}* + ρ_{j+1} s_{j+2}*` -/

/-- `ρ_{j+3} = ρ_j`. -/
lemma hx_starFn_add_three (X : Mat2) (j : ZMod 6) : starFn X (j + 3) = starFn X j := by
  rcases rein_zmod6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private lemma hx_sqrt3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

/-- `X s_j* = ρ_j s_{j+1}* + ρ_{j+1} s_{j+2}*` for traceless `X` (`eqn:rho-star-inequalities`; the
book's `ρ̃_j` equals `ρ_j`). -/
lemma hx_mulVec_sixthRoot {X : Mat2} (hX : X 1 1 = -X 0 0) (j : ZMod 6) :
    X *ᵥ sixthRoot j = starFn X j • sixthRoot (j + 1) + starFn X (j + 1) • sixthRoot (j + 2) := by
  have h3 := hx_sqrt3
  have h3' : (0 : ℝ) < √3 := by positivity
  rcases rein_zmod6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rein_z6
    simp only [show starFn X 0 = ρ₀ X from rfl, show starFn X 1 = ρ₁ X from rfl,
      show starFn X 2 = ρ₂ X from rfl, show starFn X 3 = ρ₀ X from rfl,
      show starFn X 4 = ρ₁ X from rfl, show starFn X 5 = ρ₂ X from rfl,
      algA_sixthRoot_zero, algA_sixthRoot_one, algA_sixthRoot_two, algA_sixthRoot_three,
      algA_sixthRoot_four, algA_sixthRoot_five, ρ₀, ρ₁, ρ₂]
    ext i
    fin_cases i <;>
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hX]
      try field_simp
      try first | ring1 | linear_combination (X 0 1) * h3 | linear_combination (-X 0 1) * h3

/-- `det X = ρ_jρ_{j+1} + ρ_{j+1}ρ_{j+2} + ρ_{j+2}ρ_j` for traceless `X` (`eqn:det-rho`). -/
lemma hx_det_eq {X : Mat2} (hX : X 1 1 = -X 0 0) (j : ZMod 6) :
    X.det = starFn X j * starFn X (j + 1) + starFn X (j + 1) * starFn X (j + 2) +
      starFn X (j + 2) * starFn X j := by
  have h3 := hx_sqrt3
  have h3' : (0 : ℝ) < √3 := by positivity
  have key : X.det = ρ₀ X * ρ₁ X + ρ₁ X * ρ₂ X + ρ₂ X * ρ₀ X := by
    simp only [Matrix.det_fin_two, hX, ρ₀, ρ₁, ρ₂]
    field_simp
    linear_combination (-(2 * X 0 1 * X 1 0)) * h3
  rcases rein_zmod6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rein_z6
    simp only [show starFn X 0 = ρ₀ X from rfl, show starFn X 1 = ρ₁ X from rfl,
      show starFn X 2 = ρ₂ X from rfl, show starFn X 3 = ρ₀ X from rfl,
      show starFn X 4 = ρ₁ X from rfl, show starFn X 5 = ρ₂ X from rfl, key]
    try ring1

/-- On the star domain, `ρ_j(Φ(z)) > 0` (Theorem 4.4.1). -/
lemma hx_starFn_pos {x y : ℝ} (hz : (x, y) ∈ starDomain) (j : ZMod 6) :
    0 < starFn (Φ x y) j := by
  obtain ⟨-, -, h0, h1, h2⟩ := (theorem4_4_1 x y hz.1).2 hz
  rcases rein_zmod6_cases j with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h0, h1, h2]

/-- On the star domain, `ρ_jρ_{j+1} + ρ_{j+1}ρ_{j+2} + ρ_{j+2}ρ_j = det Φ(z) = 1`
(`eqn:det-rho`, Lemma 4.2.1). -/
lemma hx_sigma {x y : ℝ} (hz : (x, y) ∈ starDomain) (j : ZMod 6) :
    starFn (Φ x y) j * starFn (Φ x y) (j + 1) + starFn (Φ x y) (j + 1) * starFn (Φ x y) (j + 2) +
      starFn (Φ x y) (j + 2) * starFn (Φ x y) j = 1 := by
  rw [← hx_det_eq (by simp [Φ]; ring) j]
  exact ((theorem4_4_1 x y hz.1).2 hz).2.1

/-! ### The frame `(s_j*, s_{j+1}*)`

All the points of the construction are combinations `α s_j* + β s_{j+1}*` (`hx_F j α β`), and
`det(α s_j* + β s_{j+1}*, γ s_j* + δ s_{j+1}*) = (αδ - βγ) √3/2`. -/

/-- The point `α s_j* + β s_{j+1}*`. -/
private noncomputable def hx_F (j : ZMod 6) (α β : ℝ) : Fin 2 → ℝ :=
  α • sixthRoot j + β • sixthRoot (j + 1)

private lemma hx_F_add (j : ZMod 6) (α β γ δ : ℝ) :
    hx_F j α β + hx_F j γ δ = hx_F j (α + γ) (β + δ) := by
  simp only [hx_F]; module

private lemma hx_F_sub (j : ZMod 6) (α β γ δ : ℝ) :
    hx_F j α β - hx_F j γ δ = hx_F j (α - γ) (β - δ) := by
  simp only [hx_F]; module

private lemma hx_F_neg (j : ZMod 6) (α β : ℝ) : -hx_F j α β = hx_F j (-α) (-β) := by
  simp only [hx_F]; module

private lemma hx_F_smul (j : ZMod 6) (c α β : ℝ) : c • hx_F j α β = hx_F j (c * α) (c * β) := by
  simp only [hx_F]; module

private lemma hx_midpoint_F (j : ZMod 6) (α β γ δ : ℝ) :
    midpoint ℝ (hx_F j α β) (hx_F j γ δ) = hx_F j ((α + γ) / 2) ((β + δ) / 2) := by
  rw [midpoint_eq_smul_add, hx_F_add, invOf_eq_inv, hx_F_smul]
  congr 1 <;> ring

private lemma hx_det2_F (j : ZMod 6) (α β γ δ : ℝ) :
    det2 (hx_F j α β) (hx_F j γ δ) = (α * δ - β * γ) * (√3 / 2) := by
  have h := (algA_isMultiPoint_sixthRoot j).2.2
  simp only [hx_F, det2, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h ⊢
  linear_combination (α * δ - β * γ) * h

private lemma hx_sixthRoot_F (j : ZMod 6) :
    sixthRoot j = hx_F j 1 0 ∧ sixthRoot (j + 1) = hx_F j 0 1 ∧
      sixthRoot (j + 2) = hx_F j (-1) 1 ∧ sixthRoot (j + 3) = hx_F j (-1) 0 := by
  have h0 := algA_isMultiPoint_sixthRoot j
  have h1 := algA_isMultiPoint_sixthRoot (j + 1)
  rw [show j + 1 + 3 = j + 4 by ring] at h1
  have h2 : sixthRoot (j + 2) = sixthRoot (j + 1) - sixthRoot j := by
    rw [h1.2.1] at h0
    linear_combination (norm := module) h0.1
  refine ⟨by simp [hx_F], by simp [hx_F], by rw [h2, hx_F]; module, by rw [h0.2.1, hx_F]; module⟩

/-- `X s_j*`, `X s_{j+1}*` and the vertices `p_j, p_{j+1}, p_{j+2}` in the frame at `j`, with
`A = ρ_j`, `B = ρ_{j+1}`, `C = ρ_{j+2}` (the definition `eqn:hex-vertex` and
`hx_mulVec_sixthRoot`); `p_{j+3} = -p_j`; and the definition of `q_j`. -/
private lemma hx_frame (x y : ℝ) (j : ZMod 6) :
    Φ x y *ᵥ sixthRoot j = hx_F j (-starFn (Φ x y) (j + 1))
        (starFn (Φ x y) j + starFn (Φ x y) (j + 1)) ∧
      Φ x y *ᵥ sixthRoot (j + 1) = hx_F j (-(starFn (Φ x y) (j + 1) + starFn (Φ x y) (j + 2)))
        (starFn (Φ x y) (j + 1)) ∧
      hexVertex x y j = hx_F j (1 - starFn (Φ x y) (j + 1) * starFn (Φ x y) (j + 2))
        (starFn (Φ x y) (j + 2) * (starFn (Φ x y) j + starFn (Φ x y) (j + 1))) ∧
      hexVertex x y (j + 1) =
        hx_F j (-(starFn (Φ x y) j * (starFn (Φ x y) (j + 1) + starFn (Φ x y) (j + 2))))
        (1 + starFn (Φ x y) j * starFn (Φ x y) (j + 1)) ∧
      hexVertex x y (j + 2) =
        hx_F j (-(1 + starFn (Φ x y) (j + 1) * starFn (Φ x y) (j + 2)))
        (1 - starFn (Φ x y) j * starFn (Φ x y) (j + 1)) ∧
      hexVertex x y (j + 3) = -hexVertex x y j ∧
      hexExtVertex x y j = hexVertex x y j + (2 * starFn (Φ x y) j) • (Φ x y *ᵥ sixthRoot j) := by
  set X := Φ x y with hXdef
  have hX : X 1 1 = -X 0 0 := by simp [X, Φ]; ring
  obtain ⟨s0, s1, s2, s3⟩ := hx_sixthRoot_F j
  have e1 : j + 1 + 1 = j + 2 := by ring
  have e2 : j + 1 + 2 = j + 3 := by ring
  have e3 : j + 2 + 1 = j + 3 := by ring
  have e4 : j + 2 + 2 = j + 1 + 3 := by ring
  have e5 : j + 3 + 2 = j + 2 + 3 := by ring
  have hXj := hx_mulVec_sixthRoot hX j
  have hXj1 := hx_mulVec_sixthRoot hX (j + 1)
  have hXj2 := hx_mulVec_sixthRoot hX (j + 2)
  rw [e1, e2] at hXj1
  rw [e3, e4] at hXj2
  have t3 := hx_starFn_add_three X j
  have t13 := hx_starFn_add_three X (j + 1)
  have t23 := hx_starFn_add_three X (j + 2)
  have m3 := (algA_isMultiPoint_sixthRoot (j + 1)).2.1
  have f0 : X *ᵥ sixthRoot j = hx_F j (-starFn X (j + 1)) (starFn X j + starFn X (j + 1)) := by
    rw [hXj, s1, s2]; simp only [hx_F_add, hx_F_smul]; congr 1 <;> ring
  have f1 : X *ᵥ sixthRoot (j + 1) =
      hx_F j (-(starFn X (j + 1) + starFn X (j + 2))) (starFn X (j + 1)) := by
    rw [hXj1, s2, s3]; simp only [hx_F_add, hx_F_smul]; congr 1 <;> ring
  have f2 : X *ᵥ sixthRoot (j + 2) = hx_F j (-starFn X (j + 2)) (-starFn X j) := by
    rw [hXj2, t3, m3, s3, s1]; simp only [hx_F_add, hx_F_smul, hx_F_neg]; congr 1 <;> ring
  refine ⟨f0, f1, ?_, ?_, ?_, ?_, rfl⟩
  · rw [hexVertex, ← hXdef, f0, s0, hx_F_smul, hx_F_add]; congr 1 <;> ring
  · rw [hexVertex, ← hXdef, e2, t3, f1, s1, hx_F_smul, hx_F_add]; congr 1; ring
  · rw [hexVertex, ← hXdef, e4, t13, f2, s2, hx_F_smul, hx_F_add]; congr 1 <;> ring
  · simp only [hexVertex, ← hXdef, e5, t23, (algA_isMultiPoint_sixthRoot j).2.1, Matrix.mulVec_neg,
      smul_neg]
    abel

/-- On the star domain (`det X = 1`), the two forms of the vertex in `eqn:hex-vertex`:
`p_j = s_{j+1}* - ρ_j X s_{j+1}*`, so the edge `p_j p_{j+1}` lies on the line through `s_{j+1}*`
in direction `X s_{j+1}*`, with `p_{j+1} - p_j = 2ρ_j X s_{j+1}*`. -/
lemma hx_edge {x y : ℝ} (hz : (x, y) ∈ starDomain) (j : ZMod 6) :
    hexVertex x y j = sixthRoot (j + 1) - starFn (Φ x y) j • (Φ x y *ᵥ sixthRoot (j + 1)) ∧
      hexVertex x y (j + 1) - hexVertex x y j =
        (2 * starFn (Φ x y) j) • (Φ x y *ᵥ sixthRoot (j + 1)) := by
  obtain ⟨-, f1, p0, p1, -⟩ := hx_frame x y j
  obtain ⟨-, s1, -⟩ := hx_sixthRoot_F j
  have hσ := hx_sigma hz j
  rw [p0, p1, f1, s1, hx_F_smul, hx_F_sub, hx_F_sub, hx_F_smul]
  constructor
  · congr 1
    · linear_combination -hσ
    · linear_combination hσ
  · congr 1
    · linear_combination hσ
    · linear_combination -hσ

/-! ### Areas of triangles -/

/-- The standard triangle `{y | y₀ ≥ 0, y₁ ≥ 0, y₀ + y₁ ≤ 1}`. -/
private def hx_stdTri : Set (Fin 2 → ℝ) := {y | 0 ≤ y 0 ∧ 0 ≤ y 1 ∧ y 0 + y 1 ≤ 1}

private lemma hx_convex_stdTri : Convex ℝ hx_stdTri := by
  intro y hy z hz s t hs ht hst
  obtain ⟨h1, h2, h3⟩ := hy
  obtain ⟨k1, k2, k3⟩ := hz
  simp only [hx_stdTri, mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine ⟨by positivity, by positivity, ?_⟩
  nlinarith

/-- The triangle `△abc` is the image of the standard triangle under the affine map
`y ↦ a + y₀ (b - a) + y₁ (c - a)`. -/
private lemma hx_convexHull_triple (a b c : Fin 2 → ℝ) :
    convexHull ℝ {a, b, c} = (fun x ↦ a + x) '' (hex_lin (b - a) (c - a) '' hx_stdTri) := by
  apply Subset.antisymm
  · refine convexHull_min ?_ ((hx_convex_stdTri.linear_image _).translate a)
    have hmem : ∀ y ∈ hx_stdTri, a + (y 0 • (b - a) + y 1 • (c - a)) ∈
        (fun x ↦ a + x) '' (hex_lin (b - a) (c - a) '' hx_stdTri) :=
      fun y hy ↦ ⟨_, ⟨y, hy, hex_lin_apply _ _ _⟩, rfl⟩
    rintro p (rfl | rfl | rfl)
    · simpa using hmem ![0, 0] (by simp [hx_stdTri])
    · simpa using hmem ![1, 0] (by simp [hx_stdTri])
    · simpa using hmem ![0, 1] (by simp [hx_stdTri])
  · rintro _ ⟨_, ⟨y, ⟨h1, h2, h3⟩, rfl⟩, rfl⟩
    rw [hex_lin_apply]
    have := (convex_convexHull ℝ ({a, b, c} : Set (Fin 2 → ℝ))).sum_mem (t := Finset.univ)
      (w := ![1 - y 0 - y 1, y 0, y 1]) (z := ![a, b, c])
      (by intro i _; fin_cases i <;> simp <;> linarith)
      (by simp [Fin.sum_univ_three]; ring)
      (by intro i _; fin_cases i <;> exact subset_convexHull ℝ _ (by simp))
    convert this using 1
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    module

/-- The area of the triangle `△abc` is `|det(b - a, c - a)|/2` (the image of the standard
triangle, of area `1/2`, under an affine map of determinant `det(b - a, c - a)`). -/
lemma hx_volume_real_triangle (a b c : Fin 2 → ℝ) :
    volume.real (convexHull ℝ {a, b, c}) = |det2 (b - a) (c - a)| / 2 := by
  have hstd : volume hx_stdTri = ENNReal.ofReal (1 / 2) := rein_volume_stdTri
  rw [measureReal_def, hx_convexHull_triple, image_add_left, measure_preimage_add,
    Measure.addHaar_image_linearMap, hex_det_lin, hstd, ← ENNReal.ofReal_mul (abs_nonneg _),
    ENNReal.toReal_ofReal (by positivity)]
  ring

/-- The interior triangle `△ s_j* p_j s_{j+1}*` has area `(√3/4) ρ_j ρ_{j+2}`
(proof of Lemma 5.0.4: `T₀ = ½ det(p₀ - s₀, s₂) = ½ ρ₂ det(X s₀, s₂) = (√3/4) ρ₀ρ₂`). -/
lemma hx_triArea {x y : ℝ} (hz : (x, y) ∈ starDomain) (j : ZMod 6) :
    volume.real (convexHull ℝ {sixthRoot j, hexVertex x y j, sixthRoot (j + 1)}) =
      √3 / 4 * starFn (Φ x y) j * starFn (Φ x y) (j + 2) := by
  obtain ⟨-, -, p0, -⟩ := hx_frame x y j
  obtain ⟨s0, s1, -⟩ := hx_sixthRoot_F j
  have hA := hx_starFn_pos hz j
  have hC := hx_starFn_pos hz (j + 2)
  rw [hx_volume_real_triangle, p0, s0, s1, hx_F_sub, hx_F_sub, hx_det2_F]
  rw [show ((1 - starFn (Φ x y) (j + 1) * starFn (Φ x y) (j + 2) - 1) * (1 - 0) -
      (starFn (Φ x y) (j + 2) * (starFn (Φ x y) j + starFn (Φ x y) (j + 1)) - 0) * (0 - 1)) *
      (√3 / 2) = starFn (Φ x y) j * starFn (Φ x y) (j + 2) * (√3 / 2) by ring]
  rw [abs_of_pos (by positivity)]
  ring

/-- The exterior triangle `△ p_j q_j p_{j+1}` has area `√3 ρ_j²` (proof of Lemma 5.0.4:
`q_j - p_j = 2ρ_j X s_j*`, `p_{j+1} - p_j = 2ρ_j X s_{j+1}*`, and
`det(X s_j*, X s_{j+1}*) = det X · det(s_j*, s_{j+1}*) = √3/2`). -/
lemma hx_extTriArea {x y : ℝ} (hz : (x, y) ∈ starDomain) (j : ZMod 6) :
    volume.real (convexHull ℝ {hexVertex x y j, hexExtVertex x y j, hexVertex x y (j + 1)}) =
      √3 * starFn (Φ x y) j ^ 2 := by
  obtain ⟨f0, f1, -, -, -, -, hq⟩ := hx_frame x y j
  obtain ⟨-, hedge⟩ := hx_edge hz j
  have hσ := hx_sigma hz j
  have hA := hx_starFn_pos hz j
  rw [hx_volume_real_triangle, hedge, hq, add_sub_cancel_left, f0, f1, hx_F_smul, hx_F_smul,
    hx_det2_F]
  set A := starFn (Φ x y) j
  set B := starFn (Φ x y) (j + 1)
  set C := starFn (Φ x y) (j + 2)
  rw [show (2 * A * -B * (2 * A * B) - 2 * A * (A + B) * (2 * A * -(B + C))) * (√3 / 2) =
      2 * A ^ 2 * √3 * (A * B + B * C + C * A) by ring, hσ, mul_one,
    abs_of_pos (by positivity)]
  ring


/-! ### Support lines of a balanced disk at the multi-point -/

/-- Each curve `σ_j` of a balanced pair is a positively oriented regular `C¹` parameterization of
`∂K`: its range is `∂K` by periodicity, and `det(σ_j, σ_j') = (α + β) √3/2 > 0` by the star
condition. -/
lemma hx_isPositiveBoundaryParam {K : Set (Fin 2 → ℝ)} {σ : ZMod 6 → ℝ → Fin 2 → ℝ}
    {tf : ℝ} (h : IsBalancedPair K σ tf) (j : ZMod 6) : IsPositiveBoundaryParam K (σ j) := by
  obtain ⟨-, hσ, -, hmulti, -, hstar, htf, hper, -, himage⟩ := h
  refine ⟨(hσ j).1, (hσ j).2, ?_, fun t ↦ ?_⟩
  · apply Subset.antisymm
    · rintro _ ⟨t, rfl⟩
      obtain ⟨u, hu, hut⟩ := Function.Periodic.exists_mem_Ico₀ (hper j) (by positivity) t
      rw [hut, ← himage j]
      exact mem_image_of_mem _ hu
    · rw [← himage j]
      exact image_subset_range _ _
  · obtain ⟨α, β, hα, hβ, hd⟩ := hstar j t
    have hdet := ((hmulti t) j).2.2
    simp only at hdet
    have : det2 (σ j t) (deriv (σ j) t) = (α + β) * det2 (σ j t) (σ (j + 1) t) := by
      rw [hd]; simp only [det2, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [this, hdet]
    positivity

/-- If `σ_j(t) = g(t) s_j*` with `σ_j(0) = s_j*` (circle representation) and
`g(0)⁻¹ g'(0) = Φ(z)`, then `σ_j'(0) = Φ(z) s_j*`: `g(0) = I` because `s₀*, s₁*` are a basis, and
`g` is differentiable because its columns are combinations of `σ₀`, `σ₁`. -/
lemma hx_deriv_eq {K : Set (Fin 2 → ℝ)} {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {tf : ℝ}
    {g : ℝ → Mat2} {X : Mat2} (hbal : IsBalancedPair K σ tf) (hcirc : IsCircleRepresentation σ)
    (hσg : ∀ j t, σ j t = g t *ᵥ sixthRoot j) (hX : (g 0)⁻¹ * derivEntrywise g 0 = X)
    (j : ZMod 6) : deriv (σ j) 0 = X *ᵥ sixthRoot j := by
  have h3 : (0 : ℝ) < √3 := by positivity
  have hcol0 : ∀ t i, g t i 0 = σ 0 t i := by
    intro t i
    rw [hσg, algA_sixthRoot_zero]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hcol1 : ∀ t i, g t i 1 = (2 * σ 1 t i - σ 0 t i) / √3 := by
    intro t i
    rw [hσg 1, hσg 0, algA_sixthRoot_zero, algA_sixthRoot_one]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    field_simp
    ring
  -- `g(0) = I`
  have hg0 : g 0 = 1 := by
    have hσ0 : ∀ j, g 0 *ᵥ sixthRoot j = sixthRoot j := fun j ↦ by rw [← hσg, hcirc]
    have e0 := hσ0 0
    have e1 := hσ0 1
    rw [algA_sixthRoot_zero] at e0
    rw [algA_sixthRoot_one] at e1
    have a00 : g 0 0 0 = 1 := by
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun e0 0
    have a10 : g 0 1 0 = 0 := by
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun e0 1
    have a01 : g 0 0 0 * (1 / 2) + g 0 0 1 * (√3 / 2) = 1 / 2 := by
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun e1 0
    have a11 : g 0 1 0 * (1 / 2) + g 0 1 1 * (√3 / 2) = √3 / 2 := by
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun e1 1
    rw [a00] at a01
    rw [a10] at a11
    have h3' : √3 / 2 ≠ 0 := by positivity
    have b01 : g 0 0 1 = 0 := by
      have : g 0 0 1 * (√3 / 2) = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_right h3'
    have b11 : g 0 1 1 = 1 := by
      have : (g 0 1 1 - 1) * (√3 / 2) = 0 := by linarith
      linarith [(mul_eq_zero.1 this).resolve_right h3']
    ext i k
    fin_cases i <;> fin_cases k <;> simp [a00, a10, b01, b11]
  rw [hg0, inv_one, one_mul] at hX
  -- `g` is differentiable at `0`, entry by entry
  have hd : ∀ j, DifferentiableAt ℝ (σ j) 0 :=
    fun j ↦ ((hbal.2.1 j).1.differentiable one_ne_zero) 0
  have hdiff : ∀ i k, DifferentiableAt ℝ (fun t ↦ g t i k) 0 := by
    intro i k
    fin_cases k
    · simp only [Fin.zero_eta, Fin.isValue, hcol0]
      exact differentiableAt_pi.1 (hd 0) i
    · simp only [Fin.mk_one, Fin.isValue, hcol1]
      exact (((differentiableAt_pi.1 (hd 1) i).const_mul 2).sub
        (differentiableAt_pi.1 (hd 0) i)).div_const _
  have hg : HasDerivAtEntrywise g (derivEntrywise g 0) 0 := fun i k ↦ by
    simpa [derivEntrywise] using (hdiff i k).hasDerivAt
  have hσj : σ j = fun t ↦ g t *ᵥ sixthRoot j := funext fun t ↦ hσg j t
  rw [hσj, (hg.mulVec_const (sixthRoot j)).deriv, hX]

/-- The support lines of `K` at the multi-point: `K` lies to the left of the line through `s_j*` in
direction `Φ(z) s_j* = σ_j'(0)`, the tangent of the boundary curve `σ_j` at `s_j*`
(`bdy_det2_deriv_sub_nonneg`). -/
lemma hx_support {K : Set (Fin 2 → ℝ)} {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {tf : ℝ}
    {g : ℝ → Mat2} {X : Mat2} (hbal : IsBalancedPair K σ tf) (hcirc : IsCircleRepresentation σ)
    (hσg : ∀ j t, σ j t = g t *ᵥ sixthRoot j) (hX : (g 0)⁻¹ * derivEntrywise g 0 = X)
    (j : ZMod 6) {q : Fin 2 → ℝ} (hq : q ∈ K) : 0 ≤ det2 (X *ᵥ sixthRoot j) (q - sixthRoot j) := by
  have h := bdy_det2_deriv_sub_nonneg hbal.1 (hx_isPositiveBoundaryParam hbal j) 0 hq
  rwa [hx_deriv_eq hbal hcirc hσg hX j, hcirc j] at h

/-- `√12 = 2√3`. -/
private lemma hx_sqrt12 : √12 = 2 * √3 := by
  rw [show (12 : ℝ) = 2 ^ 2 * 3 by norm_num, Real.sqrt_mul (by norm_num),
    Real.sqrt_sq (by norm_num)]


/-- **Lemma 5.0.3** (`lem:pt-to-hexagon`). Every `z = x + iy ∈ 𝔥*` gives a centrally symmetric
hexagon `H_K(z)` with vertices `p_j` (`hexVertex`), whose edge midpoints are the sixth roots of
unity (the edge `p_j p_{j+1}` has midpoint `s_{j+1}*`) and whose oriented edge directions satisfy
the star condition: `p_j - s_j*` lies in the open cone spanned by `s_{j+1}* - s_j*` and `s_{j+1}*`.
If `z` comes from a balanced disk `K` in circle representation at the multi-point `s_j*`, that is,
`σ_j(t) = g(t) s_j*` and `X(0) = g(0)⁻¹g'(0) = Φ(z)`, then `H_K(z)` is a centrally symmetric hexagon
of least area containing `K`, the critical hexagon of `K` (Definition 2.3.8) at the `s_j*`. -/
theorem lemma5_0_3 {x y : ℝ} (hz : (x, y) ∈ starDomain) :
    IsCSHexagon (hexVertex x y) ∧
      (∀ j, hexMidpoint (hexVertex x y) j = sixthRoot (j + 1)) ∧
      (∀ j, ∃ α β : ℝ, 0 < α ∧ 0 < β ∧
        hexVertex x y j - sixthRoot j = α • (sixthRoot (j + 1) - sixthRoot j) +
          β • sixthRoot (j + 1)) ∧
      ∀ (K : Set (Fin 2 → ℝ)) (σ : ZMod 6 → ℝ → Fin 2 → ℝ) (tf : ℝ) (g : ℝ → Mat2),
        IsBalancedPair K σ tf → IsCircleRepresentation σ → (∀ j t, σ j t = g t *ᵥ sixthRoot j) →
        (g 0)⁻¹ * derivEntrywise g 0 = Φ x y →
        IsLeastAreaHexagon K (hexVertex x y) ∧ IsCriticalHexagon K (hexagonOf (hexVertex x y)) := by
  -- Remark 3.1.7: the vertices `p_j = s_j* + ρ_{j+2} X s_j*` form a centrally symmetric hexagon
  have hcs : IsCSHexagon (hexVertex x y) := by
    intro j
    obtain ⟨-, -, p0, p1, p2, p3, -⟩ := hx_frame x y j
    have hA := hx_starFn_pos hz j
    have hB := hx_starFn_pos hz (j + 1)
    have hC := hx_starFn_pos hz (j + 2)
    have hσ := hx_sigma hz j
    set A := starFn (Φ x y) j
    set B := starFn (Φ x y) (j + 1)
    set C := starFn (Φ x y) (j + 2)
    refine ⟨p3, ?_, ?_⟩
    · rw [p0, p1, hx_det2_F]
      have : (1 - B * C) * (1 + A * B) - C * (A + B) * -(A * (B + C)) =
          (A * B + C * A) * (1 + A * B) + A * C * (A + B) * (B + C) := by
        linear_combination (-(1 + A * B)) * hσ
      rw [this]
      positivity
    · rw [p0, p1, p2, hx_F_sub, hx_F_sub, hx_det2_F]
      have : (-(A * (B + C)) - (1 - B * C)) * (1 - A * B - (1 + A * B)) -
          (1 + A * B - C * (A + B)) * (-(1 + B * C) - -(A * (B + C))) = 4 * A * B := by
        linear_combination (A * B + B * C + C * A - 1 - 2 * B * C) * hσ
      rw [this]
      positivity
  -- the edge midpoints are the sixth roots of unity (`eqn:hex-vertex`)
  have hmid : ∀ j, hexMidpoint (hexVertex x y) j = sixthRoot (j + 1) := by
    intro j
    obtain ⟨-, -, p0, p1, -⟩ := hx_frame x y j
    obtain ⟨-, s1, -⟩ := hx_sixthRoot_F j
    have hσ := hx_sigma hz j
    rw [hexMidpoint, p0, p1, hx_midpoint_F, s1]
    congr 1
    · linear_combination (-1 / 2 : ℝ) * hσ
    · linear_combination (1 / 2 : ℝ) * hσ
  refine ⟨hcs, hmid, ?_, ?_⟩
  · -- the star condition: `p_j - s_j* = ρ_{j+1}ρ_{j+2} (s_{j+1}* - s_j*) + ρ_jρ_{j+2} s_{j+1}*`
    intro j
    obtain ⟨-, -, p0, -⟩ := hx_frame x y j
    obtain ⟨s0, s1, -⟩ := hx_sixthRoot_F j
    refine ⟨starFn (Φ x y) (j + 1) * starFn (Φ x y) (j + 2),
      starFn (Φ x y) j * starFn (Φ x y) (j + 2),
      mul_pos (hx_starFn_pos hz _) (hx_starFn_pos hz _),
      mul_pos (hx_starFn_pos hz _) (hx_starFn_pos hz _), ?_⟩
    rw [p0, s0, s1, hx_F_sub, hx_F_sub, hx_F_smul, hx_F_smul, hx_F_add]
    congr 1 <;> ring
  intro K σ tf g hbal hcirc hσg hX
  have hK : IsCCSDisk K := hbal.1
  -- `K` lies in the half-plane of each edge: the edge `p_j p_{j+1}` lies on the tangent line of
  -- `∂K` at `s_{j+1}*`, a support line of `K`
  have hhalf : ∀ j, ∀ q ∈ K,
      0 ≤ det2 (hexVertex x y (j + 1) - hexVertex x y j) (q - hexVertex x y j) := by
    intro j q hq
    obtain ⟨e1, e2⟩ := hx_edge hz j
    have hs := hx_support hbal hcirc hσg hX (j + 1) hq
    have hA := hx_starFn_pos hz j
    rw [e2, e1]
    have : det2 ((2 * starFn (Φ x y) j) • (Φ x y *ᵥ sixthRoot (j + 1)))
        (q - (sixthRoot (j + 1) - starFn (Φ x y) j • (Φ x y *ᵥ sixthRoot (j + 1)))) =
        2 * starFn (Φ x y) j * det2 (Φ x y *ᵥ sixthRoot (j + 1)) (q - sixthRoot (j + 1)) := by
      simp only [det2, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [this]
    positivity
  -- hence `K ⊆ H_K(z)`, the intersection of these six half-planes
  have hsub : K ⊆ hexagonOf (hexVertex x y) := by
    intro q hq
    have hq' : -q ∈ K := hK.2.2.2 q hq
    have heq := rein_eq_hex3 hcs
    have hcs' : IsCSHexagon (rein_hex3 (hexVertex x y 0) (hexVertex x y 1) (hexVertex x y 2)) :=
      heq ▸ hcs
    have h3 : -hexVertex x y 0 = hexVertex x y (2 + 1) := by
      rw [show (2 : ZMod 6) + 1 = 0 + 3 from rfl, (hcs 0).1]
    have e01 : hexVertex x y (0 + 1) = hexVertex x y 1 := by rw [zero_add]
    have e12 : hexVertex x y (1 + 1) = hexVertex x y 2 := rfl
    rw [heq, rein_mem_hexagonOf_hex3 hcs', rein_InHex, h3]
    have a := hhalf 0 q hq
    have b := hhalf 1 q hq
    have c := hhalf 2 q hq
    have a' := hhalf 0 (-q) hq'
    have b' := hhalf 1 (-q) hq'
    have c' := hhalf 2 (-q) hq'
    rw [e01] at a a'
    rw [e12] at b b'
    exact ⟨a, b, c, a', b', c'⟩
  -- `area(H_K(z)) = 4 det(s₁*, s₂*) = 2√3 = √12`
  have hvolp : volume (hexagonOf (hexVertex x y)) = ENNReal.ofReal √12 := by
    have h12 : det2 (sixthRoot 1) (sixthRoot 2) = √3 / 2 := (algA_isMultiPoint_sixthRoot 1).2.2
    rw [rein_volume_hexagonOf hcs, hmid, hmid, zero_add, show (1 : ZMod 6) + 1 = 2 from rfl, h12,
      hx_sqrt12]
    ring_nf
  -- every centrally symmetric hexagon around `K` has area at least `√12`: by Theorem 2.2.2 a
  -- least-area hexagon `H` exists and `δ(K) = area(K)/area(H)`, while `δ(K) = area(K)/√12` (E12)
  obtain ⟨⟨v, hv⟩, hδ⟩ := theorem2_2_2 hK (ch2_not_isParallelogram_of_isBalancedPair hbal)
  have hvolv : volume.real (hexagonOf v) = √12 := by
    have h := (hδ v hv).symm.trans (greatestPackingDensity_of_isBalancedPair hbal)
    have hHpos : 0 < volume.real (hexagonOf v) := by
      rw [hex_volume_hexagonOf hv.1]; linarith [rein_det2_hexMidpoint_pos hv.1]
    have h12 : (0 : ℝ) < √12 := by positivity
    rw [div_eq_div_iff hHpos.ne' h12.ne'] at h
    exact (mul_left_cancel₀ (rein_volume_real_pos hK).ne' h).symm
  have hvolv' : volume (hexagonOf v) = ENNReal.ofReal √12 := by
    rw [rein_volume_hexagonOf hv.1, ← hvolv, hex_volume_hexagonOf hv.1]
  have hleast : IsLeastAreaHexagon K (hexVertex x y) := by
    refine ⟨hcs, hsub, fun w hw hKw ↦ ?_⟩
    rw [hvolp, ← hvolv']
    exact hv.2.2 w hw hKw
  -- the critical hexagon of Definition 2.3.8: Theorem 2.3.9
  exact ⟨hleast, theorem2_3_9 hK hleast⟩

/-- **Lemma 5.0.4** (`lem:triangle-areas`). For `z = x + iy ∈ 𝔥*` and `ρ_j = ρ_j(Φ(z))`:
`area(T₀) = (√3/4)ρ₀ρ₂`, `area(T₁) = (√3/4)ρ₀ρ₁`, `area(T₂) = (√3/4)ρ₁ρ₂`,
`area(T₀^ext) = √3ρ₁²`, `area(T₁^ext) = √3ρ₂²`, `area(T₂^ext) = √3ρ₀²`, and
`area(T₀) + area(T₁) + area(T₂) = √3/4`. -/
theorem lemma5_0_4 {x y : ℝ} (hz : (x, y) ∈ starDomain) :
    triArea x y 0 = √3 / 4 * ρ₀ (Φ x y) * ρ₂ (Φ x y) ∧
      triArea x y 1 = √3 / 4 * ρ₀ (Φ x y) * ρ₁ (Φ x y) ∧
      triArea x y 2 = √3 / 4 * ρ₁ (Φ x y) * ρ₂ (Φ x y) ∧
      extTriArea x y 0 = √3 * ρ₁ (Φ x y) ^ 2 ∧
      extTriArea x y 1 = √3 * ρ₂ (Φ x y) ^ 2 ∧
      extTriArea x y 2 = √3 * ρ₀ (Φ x y) ^ 2 ∧
      triArea x y 0 + triArea x y 1 + triArea x y 2 = √3 / 4 := by
  set X := Φ x y
  -- the interior triangles (`T_i = △ s_i p_i s_{i+1}`) and the exterior triangles
  -- (`T_i^ext = △ p_{i+1} q_{i+1} p_{i+2}`) at `j = i`, resp. `j = i + 1`
  have hT : ∀ i : Fin 3, triArea x y i =
      √3 / 4 * starFn X (i.val : ZMod 6) * starFn X ((i.val : ZMod 6) + 2) :=
    fun i ↦ hx_triArea hz _
  have hE : ∀ i : Fin 3, extTriArea x y i = √3 * starFn X ((i.val : ZMod 6) + 1) ^ 2 := by
    intro i
    have h := hx_extTriArea hz ((i.val : ZMod 6) + 1)
    rwa [show (i.val : ZMod 6) + 1 + 1 = (i.val : ZMod 6) + 2 by ring] at h
  have r0 : starFn X ((0 : Fin 3).val : ZMod 6) = ρ₀ X := rfl
  have r02 : starFn X (((0 : Fin 3).val : ZMod 6) + 2) = ρ₂ X := rfl
  have r01 : starFn X (((0 : Fin 3).val : ZMod 6) + 1) = ρ₁ X := rfl
  have r1 : starFn X ((1 : Fin 3).val : ZMod 6) = ρ₁ X := rfl
  have r12 : starFn X (((1 : Fin 3).val : ZMod 6) + 2) = ρ₀ X := rfl
  have r11 : starFn X (((1 : Fin 3).val : ZMod 6) + 1) = ρ₂ X := rfl
  have r2 : starFn X ((2 : Fin 3).val : ZMod 6) = ρ₂ X := rfl
  have r22 : starFn X (((2 : Fin 3).val : ZMod 6) + 2) = ρ₁ X := rfl
  have r21 : starFn X (((2 : Fin 3).val : ZMod 6) + 1) = ρ₀ X := rfl
  -- `ρ₀ρ₁ + ρ₁ρ₂ + ρ₂ρ₀ = det X = 1` (`eqn:det-rho`)
  have hσ : ρ₀ X * ρ₁ X + ρ₁ X * ρ₂ X + ρ₂ X * ρ₀ X = 1 := hx_sigma hz 0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hT, r0, r02]
  · rw [hT, r1, r12]; ring
  · rw [hT, r2, r22]; ring
  · rw [hE, r01]
  · rw [hE, r11]
  · rw [hE, r21]
  · rw [hT, hT, hT, r0, r02, r1, r12, r2, r22]
    linear_combination √3 / 4 * hσ

/-- **Lemma 5.0.5** (`lem:geom-thales`). In a triangle `△ s₀ s₁ p₀` (here `a`, `b`, `p`), let
`r₀ ∈ [s₀, p₀]` and `r̃₀ ∈ [s₁, p₀]` with `r₀r̃₀ ∥ s₀s₁`. Then for every `r` on the segment
`[r̃₀, r₀]`, `△s₀s₁r = △s₀p₀s₁ - √(△r₀p₀r̃₀ · △s₀p₀s₁)` (areas). -/
theorem lemma5_0_5 {a b p r₀ r₀' r : Fin 2 → ℝ} (hr₀ : r₀ ∈ segment ℝ a p)
    (hr₀' : r₀' ∈ segment ℝ b p) (hpar : det2 (r₀' - r₀) (b - a) = 0)
    (hr : r ∈ segment ℝ r₀' r₀) :
    volume.real (convexHull ℝ {a, b, r}) =
      volume.real (convexHull ℝ {a, p, b}) -
        √(volume.real (convexHull ℝ {r₀, p, r₀'}) * volume.real (convexHull ℝ {a, p, b})) := by
  -- the book's affine reduction: in the frame at `s₀ = a` with axes `u = s₁ - s₀`,
  -- `w = p₀ - s₀`, `r₀ = s₀ + t₁ w`, `r̃₀ = s₀ + (1 - t₂) u + t₂ w`, and every area is
  -- `|det(u, w)|` times the area in the normalized triangle
  obtain ⟨s₁, t₁, hs₁, ht₁, hst₁, rfl⟩ := hr₀
  obtain ⟨s₂, t₂, hs₂, ht₂, hst₂, rfl⟩ := hr₀'
  obtain ⟨σ, τ, hσ, hτ, hστ, rfl⟩ := hr
  obtain rfl : s₁ = 1 - t₁ := by linarith
  obtain rfl : s₂ = 1 - t₂ := by linarith
  obtain rfl : σ = 1 - τ := by linarith
  rw [hx_volume_real_triangle, hx_volume_real_triangle, hx_volume_real_triangle]
  set D := det2 (b - a) (p - a) with hD
  have e1 : det2 (b - a) ((1 - τ) • ((1 - t₂) • b + t₂ • p) + τ • ((1 - t₁) • a + t₁ • p) - a) =
      ((1 - τ) * t₂ + τ * t₁) * D := by
    simp only [hD, det2, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have e2 : det2 (p - a) (b - a) = -D := by simp only [hD, det2, Pi.sub_apply]; ring
  have e3 : det2 (p - ((1 - t₁) • a + t₁ • p)) ((1 - t₂) • b + t₂ • p - ((1 - t₁) • a + t₁ • p)) =
      -((1 - t₁) * (1 - t₂) * D) := by
    simp only [hD, det2, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have e4 : det2 ((1 - t₂) • b + t₂ • p - ((1 - t₁) • a + t₁ • p)) (b - a) = (t₁ - t₂) * D := by
    simp only [hD, det2, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [e1, e2, e3, abs_neg, abs_neg]
  rw [e4] at hpar
  rcases mul_eq_zero.1 hpar with h | h
  · -- `r₀ r̃₀ ∥ s₀ s₁` in a nondegenerate triangle: `r₀`, `r̃₀` divide the sides in the same ratio
    obtain rfl : t₁ = t₂ := by linarith
    have h1 : 0 ≤ 1 - t₁ := by linarith
    rw [show (1 - τ) * t₁ + τ * t₁ = t₁ by ring, abs_mul, abs_mul, abs_of_nonneg ht₁,
      abs_of_nonneg (mul_nonneg h1 h1),
      show (1 - t₁) * (1 - t₁) * |D| / 2 * (|D| / 2) = ((1 - t₁) * |D| / 2) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
    ring
  · -- a degenerate triangle: all three areas vanish
    simp [h]

/-- `area_i ≥ 0` on `h_i` (TeX 4198: `area_i = 0` where `I_i` jumps). -/
theorem areaFn_nonneg_of_mem_hRegion {i : Fin 3} {z : ℝ × ℝ} (hz : z ∈ hRegion i) :
    0 ≤ areaFn i z := by
  obtain ⟨-, hle⟩ := hz
  have hT : 0 ≤ triArea z.1 z.2 i := measureReal_nonneg
  have hE : 0 ≤ extTriArea z.1 z.2 i := measureReal_nonneg
  -- `√(T^ext T) ≤ √(T T) = T`
  have : √(extTriArea z.1 z.2 i * triArea z.1 z.2 i) ≤ triArea z.1 z.2 i := by
    calc √(extTriArea z.1 z.2 i * triArea z.1 z.2 i)
        ≤ √(triArea z.1 z.2 i * triArea z.1 z.2 i) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hle hT)
      _ = triArea z.1 z.2 i := Real.sqrt_mul_self hT
  simp only [areaFn]
  linarith

/-- The second form of the density bound (TeX 4342):
`δ(z) = 3/4 + Σ_{i=0}^{2} I_i(z) area_i(z)/√3`. -/
theorem densityBound_eq (z : ℝ × ℝ) :
    densityBound z = 3 / 4 + (∑ i : Fin 3, (hRegion i).indicator (areaFn i) z) / √3 := by
  have h3 : 0 < √3 := by positivity
  have h12 : √12 = 2 * √3 := by
    rw [show (12 : ℝ) = 2 ^ 2 * 3 by norm_num, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  rw [densityBound, h12]
  field_simp
  ring

end SmoothedPolygons
