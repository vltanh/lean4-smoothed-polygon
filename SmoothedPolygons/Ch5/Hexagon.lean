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
  critical hexagon of `K` at the multi-point `s_j*`, is not argued. Proof to write: the vertex
  formula is `eqn:hex-vertex` with `det X = 1` (`lemma4_2_1`, `theorem4_4_1` for the star
  inequalities; the identity `X s_j = ρ_j s_{j+1} + ρ_{j+1} s_{j+2}` of
  `eqn:rho-star-inequalities`); convexity and central symmetry (`IsCSHexagon`) are polynomial
  identities and inequalities in the `ρⱼ > 0` with `ρ₀ρ₁ + ρ₁ρ₂ + ρ₂ρ₀ = 1` (`eqn:det-rho`); the
  edge directions satisfy the star condition with `α = ρ_{j+1}ρ_{j+2}`, `β = ρ_jρ_{j+2}`. For the
  critical hexagon: the edge through `s_j*` has direction `σ_j'(0) = g'(0) s_j* = X(0) s_j*`
  (`g(0) = I`), so its line is the tangent, hence a support line, of the convex disk `K` at
  `s_j* ∈ ∂K`, and `K ⊆ H_K(z)`; its area is `3√3/2 + 2(T₀ + T₁ + T₂) = √12` (Lemma 5.0.4); and
  every centrally symmetric hexagon containing `K` has area at least `√12`: by Theorem 2.2.2
  (`theorem2_2_2`, with `ch2_not_isParallelogram_of_isBalancedPair`) and E12
  (`greatestPackingDensity_of_isBalancedPair`), `area(K)/√12 = δ(K) = area(K)/area(H)` for a
  least-area hexagon `H`. The critical hexagon of Definition 2.3.8 is then Theorem 2.3.9
  (`theorem2_3_9`). Size: 300–500 lines.
* **Lemma 5.0.4** (`lemma5_0_4`, `lem:triangle-areas`, TeX 4087–4151). The book's proof: the
  coordinates of `p_i`, `q_i` from Lemma 5.0.3 and equations (3.1.3), (3.1.6), (3.1.8), (3.1.7)
  with `det X = 1`; e.g. `area(T₀) = ½ det(p₀ - s₀, s₂) = ½ ρ₂ det(Xs₀, s₂) = (√3/4)ρ₀ρ₂` and
  `area(T₀^ext) = -2ρ₁² det(Xs₃, Xs₁) = √3ρ₁²`; the sum is `(√3/4)(ρ₀ρ₂ + ρ₁ρ₂ + ρ₀ρ₁) =
  (√3/4)det X` by (3.1.7). Proof to write: the area of a triangle as `|det|/2` (translate, then
  `rein_volume_tri` of `Ch2/Reinhardt.lean`), and the explicit determinants. Size: 150–250 lines.
* **Lemma 5.0.5** (`lemma5_0_5`, `lem:geom-thales`, TeX 4153–4180). The book's proof: an affine
  map (preserving ratios of areas) reduces to a right angle at `s₁` with `s₀s₁ = s₁p₀ = 1`,
  `s₁r̃₀ = r`, where the identity reads `r/2 = (1 - √((1 - r)²))/2`. Proof to write: write
  `r₀ = p + λ(a - p)`, `r̃₀ = p + λ(b - p)` (the parallel condition forces the same `λ` when the
  triangle is nondegenerate), so `△r₀pr̃₀ = λ² △apb` and `△abr = (1 - λ) △apb` for `r` on
  `[r̃₀, r₀]`; degenerate triangles have all areas zero. Size: 100–200 lines.
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
  sorry

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
  sorry

/-- **Lemma 5.0.5** (`lem:geom-thales`). In a triangle `△ s₀ s₁ p₀` (here `a`, `b`, `p`), let
`r₀ ∈ [s₀, p₀]` and `r̃₀ ∈ [s₁, p₀]` with `r₀r̃₀ ∥ s₀s₁`. Then for every `r` on the segment
`[r̃₀, r₀]`, `△s₀s₁r = △s₀p₀s₁ - √(△r₀p₀r̃₀ · △s₀p₀s₁)` (areas). -/
theorem lemma5_0_5 {a b p r₀ r₀' r : Fin 2 → ℝ} (hr₀ : r₀ ∈ segment ℝ a p)
    (hr₀' : r₀' ∈ segment ℝ b p) (hpar : det2 (r₀' - r₀) (b - a) = 0)
    (hr : r ∈ segment ℝ r₀' r₀) :
    volume.real (convexHull ℝ {a, b, r}) =
      volume.real (convexHull ℝ {a, p, b}) -
        √(volume.real (convexHull ℝ {r₀, p, r₀'}) * volume.real (convexHull ℝ {a, p, b})) := by
  sorry

/-- `area_i ≥ 0` on `h_i` (TeX 4198: `area_i = 0` where `I_i` jumps). -/
theorem areaFn_nonneg_of_mem_hRegion {i : Fin 3} {z : ℝ × ℝ} (hz : z ∈ hRegion i) :
    0 ≤ areaFn i z := by
  sorry

/-- The second form of the density bound (TeX 4342):
`δ(z) = 3/4 + Σ_{i=0}^{2} I_i(z) area_i(z)/√3`. -/
theorem densityBound_eq (z : ℝ × ℝ) :
    densityBound z = 3 / 4 + (∑ i : Fin 3, (hRegion i).indicator (areaFn i) z) / √3 := by
  sorry

end SmoothedPolygons
