module

public import SmoothedPolygons.Ch5.Hexagon

/-!
# A lower bound for the area of a balanced disk (Theorem 5.0.6)

For a balanced disk `K` in circle representation whose critical hexagon is `H_K(z)`,
`z = x + iy ∈ 𝔥*` (Lemma 5.0.3), Theorem 5.0.6 (TeX 4203–4317) bounds the area from below:

  `area(K) ≥ 3√3/2 + 2 Σ_{i=0}^{2} I_i(z) area_i(z)`        (`theorem5_0_6`).

## The book's proof

1. If `z ∉ h₀ ∪ h₁ ∪ h₂`, the bound is `area(K) ≥ area(conv{s_j*}) = 3√3/2`, because `K` is
   convex and contains the sixth roots of unity (`IsCircleRepresentation`, `σ_j(0) ∈ ∂K`).
   (The book recalls that Reinhardt 1934 has this inequality.)
2. `h₀ ∩ h₁ ∩ h₂ = ∅` (`inter_hRegion_eq_empty`, TeX 4229–4241): by Lemma 5.0.4 and
   Cauchy–Schwarz, `Σ T_i = (√3/4)(ρ₀ρ₂ + ρ₀ρ₁ + ρ₁ρ₂) ≤ (√3/4)(ρ₀² + ρ₁² + ρ₂²) =
   (1/4) Σ T_i^ext < Σ T_i^ext`. By the threefold symmetry (shifting indices) two cases remain.
3. **Case 1**, `z ∈ h₀ \ (h₁ ∪ h₂)` (TeX 4248–4300): cut the corner `p₀` of `H_K(z)` by the segment
   `[r₀, r̃₀] ∥ s₀s₁` with `△r₀p₀r̃₀ = T₀^ext` (`cutPoint`, `cutPoint'`: `r₀ = p₀ + λ(s₀ - p₀)`,
   `r̃₀ = p₀ + λ(s₁ - p₀)`, `λ = √(T₀^ext/T₀) ≤ 1`). *Claim* (`exists_mem_frontier_segment_cut`):
   some `r ∈ [r₀, r̃₀]` lies on `∂K`. Otherwise `K` lies in the centrally symmetric hexagon with
   vertices `r₀, r̃₀, q₁` and their reflections, which has the area of `H_K(z)` (the corners `p₀`,
   `p₃` of area `T₀^ext` are cut off, the exterior triangles `△p₁q₁p₂`, `△p₄q₄p₅` of area `T₀^ext`
   are added); pushing the cut edges inward until they meet `K` gives a centrally symmetric hexagon
   containing `K` of smaller area, contradicting the minimality of `H_K(z)`
   (`IsLeastAreaHexagon`). Then `K ⊇ conv{s_j*, ±r}`, of area `3√3/2 + 2 △s₀rs₁`, and
   `△s₀rs₁ = T₀ - √(T₀^ext T₀)` by Lemma 5.0.5 (`lemma5_0_5`).
4. **Case 2**, `z ∈ h₀ ∩ h₁` (TeX 4302–4312): "the above argument can also be adapted", giving two
   points `r`, `r'` on `∂K` in `T₀` and `T₁`, and the bound with `area₀ + area₁`. Only sketched.

## Proof to write, and the gap of Case 2

The claim of Case 1 holds for each `i` with `z ∈ h_i` separately: its argument modifies `H_K(z)`
only near the corners `p_i`, `p_{i+3}` and over the edges `p_{i+1}p_{i+2}`, `p_{i+4}p_{i+5}`; the
modified hexagon is the intersection of the strips of the lines through `s_i*`, `s_{i+1}*` and of
the cut lines, so it is a centrally symmetric hexagon containing `K` whenever `K` misses the cut,
whatever happens at the other corners. So the claim is stated for every `i` with `z ∈ h_i`
(`exists_mem_frontier_segment_cut`). Then, for `I = {i | z ∈ h_i}`, the points `±r_i`, `i ∈ I`,
with `r_i ∈ T_i`, give `K ⊇ conv{s_j*} ∪ ⋃_{i ∈ I} (△s_i r_i s_{i+1} ∪ -△s_i r_i s_{i+1})`, a union
of a hexagon and triangles with disjoint interiors (each triangle lies beyond its own edge
`s_i s_{i+1}`), so `area(K) ≥ 3√3/2 + 2 Σ_{i ∈ I} area_i` by Lemma 5.0.5. This repairs Case 2
along the book's lines and makes step 2 unnecessary (it is stated as in the book).

Facts used: `K` convex and compact (`IsCCSDisk`), `s_j* ∈ ∂K`; `K ⊆ hexagonOf (hexVertex x y)` and
minimality (`IsLeastAreaHexagon`); areas of triangles and hexagons (`rein_volume_tri`,
`rein_volume_hexagonOf` in `SmoothedPolygons/Ch2/Reinhardt.lean`); Lemmas 5.0.4 and 5.0.5.
Size: 600–1,200 lines (the convex geometry of the claim is the bulk).
-/

@[expose] public section

namespace SmoothedPolygons

open MeasureTheory Set

/-- The ratio `λ_i = √(T_i^ext/T_i)` of the cut of the corner `p_i` (proof of Theorem 5.0.6): the
triangle `△ r p_i r̃` with `r - p_i = λ_i (s_i* - p_i)`, `r̃ - p_i = λ_i (s_{i+1}* - p_i)` has area
`λ_i² T_i = T_i^ext`. -/
noncomputable def cutRatio (x y : ℝ) (i : Fin 3) : ℝ := √(extTriArea x y i / triArea x y i)

/-- The point `r₀ = p_i + λ_i (s_i* - p_i)` on the edge `[s_i*, p_i]` (proof of Theorem 5.0.6,
TeX 4256–4260). -/
noncomputable def cutPoint (x y : ℝ) (i : Fin 3) : Fin 2 → ℝ :=
  hexVertex x y (i.val : ZMod 6) +
    cutRatio x y i • (sixthRoot (i.val : ZMod 6) - hexVertex x y (i.val : ZMod 6))

/-- The point `r̃₀ = p_i + λ_i (s_{i+1}* - p_i)` on the edge `[s_{i+1}*, p_i]` (proof of
Theorem 5.0.6, TeX 4256–4260). -/
noncomputable def cutPoint' (x y : ℝ) (i : Fin 3) : Fin 2 → ℝ :=
  hexVertex x y (i.val : ZMod 6) +
    cutRatio x y i • (sixthRoot ((i.val : ZMod 6) + 1) - hexVertex x y (i.val : ZMod 6))

/-- `h₀ ∩ h₁ ∩ h₂ = ∅` (proof of Theorem 5.0.6, TeX 4229–4241): by Lemma 5.0.4 and Cauchy–Schwarz,
`Σ T_i ≤ (1/4) Σ T_i^ext < Σ T_i^ext`. -/
theorem inter_hRegion_eq_empty : hRegion 0 ∩ hRegion 1 ∩ hRegion 2 = ∅ := by
  sorry

/-- **The claim in the proof of Theorem 5.0.6** (Case 1, TeX 4262–4276). Let `K` be a balanced
disk in circle representation with critical hexagon `H_K(z)`, `z ∈ 𝔥*`. If `z ∈ h_i`, the boundary
of `K` meets the cut segment `[r̃₀, r₀]` of the corner `p_i`. -/
theorem exists_mem_frontier_segment_cut {K : Set (Fin 2 → ℝ)} {σ : ZMod 6 → ℝ → Fin 2 → ℝ}
    {tf : ℝ} (hKσ : IsBalancedPair K σ tf) (hcirc : IsCircleRepresentation σ) {x y : ℝ}
    (hz : (x, y) ∈ starDomain) (hH : IsLeastAreaHexagon K (hexVertex x y)) {i : Fin 3}
    (hi : (x, y) ∈ hRegion i) :
    ∃ r ∈ frontier K, r ∈ segment ℝ (cutPoint' x y i) (cutPoint x y i) := by
  sorry

/-- **Theorem 5.0.6** (`thm:compactification-area-bound`, label of this formalization: the theorem
is unlabelled in the TeX, line 4203). If `K` is a balanced disk in circle representation with
critical hexagon `H_K(z)`, `z = x + iy ∈ 𝔥*` (a centrally symmetric hexagon of least area containing
`K`, Lemma 5.0.3), then `area(K) ≥ 3√3/2 + 2 Σ_{i=0}^{2} I_i(z) area_i(z)`.

The book proves Case 2 (`z ∈ h_i ∩ h_{i+1}`) only by "the above argument can also be adapted";
see the module docstring for the repair along its lines. -/
theorem theorem5_0_6 {K : Set (Fin 2 → ℝ)} {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {tf : ℝ}
    (hKσ : IsBalancedPair K σ tf) (hcirc : IsCircleRepresentation σ) {x y : ℝ}
    (hz : (x, y) ∈ starDomain) (hH : IsLeastAreaHexagon K (hexVertex x y)) :
    3 * √3 / 2 + 2 * ∑ i : Fin 3, (hRegion i).indicator (areaFn i) (x, y) ≤ volume.real K := by
  sorry

end SmoothedPolygons
