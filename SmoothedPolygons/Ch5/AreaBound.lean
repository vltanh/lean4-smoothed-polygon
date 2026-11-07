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

## The proof: Case 2 repaired, Case 1 restructured

Departure from the paper, in both cases. Case 2, which the book only sketches, is repaired, and
Case 1 is restructured with it: the case `z ∉ h₀ ∪ h₁ ∪ h₂` (step 1) and the two cases are one
argument, and the area is bounded by the measure of a union of almost disjoint pieces instead of
`area(conv{s_j*, ±r})` (the same quantity). The claim of Case 1 holds for each `i` with `z ∈ h_i`
separately: its argument modifies `H_K(z)` only near the corners `p_i`, `p_{i+3}`
and over the edges `p_{i+1}p_{i+2}`, `p_{i+4}p_{i+5}`; the modified hexagon is the intersection of
the strips of the lines through `s_i*`, `s_{i+1}*` and of the cut lines, so it is a centrally
symmetric hexagon containing `K` whenever `K` misses the cut, whatever happens at the other corners.
So the claim is stated for every `i` with `z ∈ h_i` (`exists_mem_frontier_segment_cut`). Then, for
`I = {i | z ∈ h_i}`, the points `±r_i`, `i ∈ I`, with `r_i ∈ T_i`, give `K ⊇ conv{s_j*} ∪ ⋃_{i ∈ I}
(△s_i r_i s_{i+1} ∪ -△s_i r_i s_{i+1})`, a union of a hexagon and triangles with disjoint interiors
(each triangle lies beyond its own edge `s_i s_{i+1}`), so `area(K) ≥ 3√3/2 + 2 Σ_{i ∈ I} area_i` by
Lemma 5.0.5. For `I = ∅` this is step 1, and for `I = {0}` it is Case 1 with the area of
`conv{s_j*, ±r}` written as that of the union. This repairs Case 2 along the book's lines and makes
step 2 unnecessary (it is proved as in the book).

**The claim** (`ab_corner`, in the frame `(e, f) = (s_i*, s_{i+1}*)`, where
`p_i = A(B + C) e + C(A + B) f`, `p_{i+1} = -A(B + C) e + (1 + AB) f`,
`p_{i+2} = -(1 + BC) e + C(A + B) f`, `q_{i+1} = -(A + 2B)(B + C) e + (1 + AB + 2B²) f` with
`A, B, C = ρ_i, ρ_{i+1}, ρ_{i+2}` and `AB + BC + CA = 1`; `ab_hexVertex_frame`). The book's
construction is made in one step: the line parallel to the cut is pushed to the supporting line of
`K` (the maximum of `x ↦ det(x, s_{i+1}* - s_i*)` on the compact `K`). If that line lies strictly
inside the cut (`K` misses the closed corner beyond the cut), the centrally symmetric hexagon with
vertices `r_μ, r̃_μ, q_{i+1}` and their reflections, cut at the ratio `μ > λ` of that line, contains
`K` (strip conditions, `ab_mem_cut`; it is a hexagon for `0 < μ ≤ 1`, `ab_hexCond_cut`) and has area
`area(H_K(z)) + 2T_i^ext - 2μ²T_i < area(H_K(z))`, contradicting minimality (`IsLeastAreaHexagon`).
Otherwise the cut line meets `K` (on the segment from `s_i*` to the maximizer), and the extreme
point of `K` on the cut line in the direction `s_i* - s_{i+1}*` is a boundary point of `K`; it lies
on `[r̃, r]` because `H_K(z)` meets the cut line exactly in `[r̃, r]`. This fills in the book's step
"if no point of the segment is on `∂K`, then `K` lies in the hexagon `r₀, r̃₀, q₁, …`".

**The area** (`theorem5_0_6`). The triangles `△s_i r_i s_{i+1}` lie in `K` and in the triangles
`s_i* s_{i+1}* (s_i* + s_{i+1}*)` (since `p_i` does, `ab_hexVertex_mem_sixthTriangle`); these six
triangles and `conv{s_j*}` have pairwise disjoint interiors, and frontiers of convex sets are null,
so the pieces are almost disjoint and `Σ area ≤ area(K)` (`tsum_meas_le_meas_iUnion_of_disjoint₀`).
The area of `△r₀p₀r̃₀` is `λ²T_i = T_i^ext` (a homothety of `T_i`, `ab_volume_cut`), so Lemma 5.0.5
gives `area(△s_i r_i s_{i+1}) = area_i(z)`; and `area(conv{s_j*}) = 3√3/2`
(`rein_volume_hexagonOf_hex3`).

Facts used: `K` convex and compact (`IsCCSDisk`), `s_j* ∈ ∂K`; `K ⊆ hexagonOf (hexVertex x y)` and
minimality (`IsLeastAreaHexagon`); the strip description and the area of a centrally symmetric
hexagon (`rein_mem_hexagonOf_iff_strips`, `rein_volume_hexagonOf_hex3`); Lemmas 5.0.4 and 5.0.5;
`mulVec_sixthRoot_eq_starFn`, `starFn_Φ_mul_add_eq_one`, `starFn_Φ_pos` of
`SmoothedPolygons/Ch5/Hexagon.lean`.
-/

@[expose] public section

namespace SmoothedPolygons

open MeasureTheory Set Matrix

/-- The ratio `λ_i = √(T_i^ext/T_i)` of the cut of the corner `p_i` (proof of Theorem 5.0.6): the
triangle `△ r p_i r̃` with `r - p_i = λ_i (s_i* - p_i)`, `r̃ - p_i = λ_i (s_{i+1}* - p_i)` has area
`λ_i² T_i = T_i^ext`. -/
noncomputable def cutRatio (x y : ℝ) (i : Fin 3) : ℝ := √(extTriArea x y i / triArea x y i)

/-- The point `r₀ = p_i + λ_i (s_i* - p_i)` on the edge `[s_i*, p_i]` (proof of Theorem 5.0.6,
TeX 4258–4267). -/
noncomputable def cutPoint (x y : ℝ) (i : Fin 3) : Fin 2 → ℝ :=
  hexVertex x y (i.val : ZMod 6) +
    cutRatio x y i • (sixthRoot (i.val : ZMod 6) - hexVertex x y (i.val : ZMod 6))

/-- The point `r̃₀ = p_i + λ_i (s_{i+1}* - p_i)` on the edge `[s_{i+1}*, p_i]` (proof of
Theorem 5.0.6, TeX 4258–4267). -/
noncomputable def cutPoint' (x y : ℝ) (i : Fin 3) : Fin 2 → ℝ :=
  hexVertex x y (i.val : ZMod 6) +
    cutRatio x y i • (sixthRoot ((i.val : ZMod 6) + 1) - hexVertex x y (i.val : ZMod 6))

/-! ### Coordinates in a frame -/

/-- The point `p e + q f` of the frame `(e, f)`. -/
private noncomputable def ab_F (e f : Fin 2 → ℝ) (p q : ℝ) : Fin 2 → ℝ := p • e + q • f

private lemma ab_det2_F (e f : Fin 2 → ℝ) (p q p' q' : ℝ) :
    det2 (ab_F e f p q) (ab_F e f p' q') = (p * q' - q * p') * det2 e f := by
  simp only [ab_F, det2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

private lemma ab_F_sub (e f : Fin 2 → ℝ) (p q p' q' : ℝ) :
    ab_F e f p q - ab_F e f p' q' = ab_F e f (p - p') (q - q') := by
  simp only [ab_F]; module

private lemma ab_F_add (e f : Fin 2 → ℝ) (p q p' q' : ℝ) :
    ab_F e f p q + ab_F e f p' q' = ab_F e f (p + p') (q + q') := by
  simp only [ab_F]; module

private lemma ab_F_neg (e f : Fin 2 → ℝ) (p q : ℝ) : -ab_F e f p q = ab_F e f (-p) (-q) := by
  simp only [ab_F]; module

private lemma ab_F_smul (e f : Fin 2 → ℝ) (t p q : ℝ) :
    t • ab_F e f p q = ab_F e f (t * p) (t * q) := by
  simp only [ab_F]; module

/-- Every point has coordinates in a frame `(e, f)` with `det(e, f) ≠ 0` (Cramer's rule). -/
private lemma ab_exists_F {e f : Fin 2 → ℝ} (hD : det2 e f ≠ 0) (x : Fin 2 → ℝ) :
    ∃ X1 X2 : ℝ, x = ab_F e f X1 X2 := by
  refine ⟨det2 x f / det2 e f, det2 e x / det2 e f, ?_⟩
  have hcr := rein_cramer e f x
  simp only [ab_F]
  rw [div_eq_inv_mul, div_eq_inv_mul, mul_smul, mul_smul, ← smul_add, ← hcr, smul_smul,
    inv_mul_cancel₀ hD, one_smul]

/-- `|k u D| ≤ k v D` with `k, D > 0` gives `|u| ≤ v`. -/
private lemma ab_abs_le_of_mul {u v k D : ℝ} (hk : 0 < k) (hD : 0 < D)
    (h : |k * u * D| ≤ k * v * D) : |u| ≤ v := by
  rw [abs_mul, abs_mul, abs_of_pos hk, abs_of_pos hD] at h
  exact le_of_mul_le_mul_left (le_of_mul_le_mul_right h hD) hk

/-- `|u| ≤ v` gives `|k u D| ≤ k v D` for `k, D > 0`. -/
private lemma ab_mul_abs_le {u v k D : ℝ} (hk : 0 < k) (hD : 0 < D) (h : |u| ≤ v) :
    |k * u * D| ≤ k * v * D := by
  rw [abs_mul, abs_mul, abs_of_pos hk, abs_of_pos hD]
  gcongr

section corner

variable {e f : Fin 2 → ℝ} {A B C : ℝ}

/-- The two strip conditions of the hexagon `H_K(z)` through the edges at the corner `p₀`
(through `e = s₀*` and `f = s₁*`), in the frame `(e, f)`. -/
private lemma ab_strips_coord (hD : 0 < det2 e f) (hA : 0 < A) (hC : 0 < C)
    (hABC : A * B + B * C + C * A = 1) {X1 X2 : ℝ}
    (h : rein_strips (ab_F e f (A * (B + C)) (C * (A + B)))
      (ab_F e f (-(A * (B + C))) (1 + A * B)) (ab_F e f (-(1 + B * C)) (C * (A + B)))
      (ab_F e f X1 X2)) :
    |B * X1 + (B + C) * X2| ≤ B + C ∧ |(A + B) * X1 + B * X2| ≤ A + B := by
  obtain ⟨h1, -, h3⟩ := h
  rw [ab_F_sub, ab_det2_F, ab_det2_F] at h1
  rw [ab_F_add, ab_det2_F, ab_det2_F] at h3
  have e1 : (A * (B + C) - -(A * (B + C))) * X2 - (C * (A + B) - (1 + A * B)) * X1 =
      2 * A * (B * X1 + (B + C) * X2) := by linear_combination (-X1) * hABC
  have e2 : A * (B + C) * (1 + A * B) - C * (A + B) * -(A * (B + C)) = 2 * A * (B + C) := by
    linear_combination (A * (B + C)) * hABC
  have e3 : (-(1 + B * C) + A * (B + C)) * X2 - (C * (A + B) + C * (A + B)) * X1 =
      -(2 * C * ((A + B) * X1 + B * X2)) := by linear_combination X2 * hABC
  have e4 : A * (B + C) * (C * (A + B)) - C * (A + B) * -(1 + B * C) = 2 * C * (A + B) := by
    linear_combination (C * (A + B)) * hABC
  rw [e1, e2] at h1
  rw [e3, e4, neg_mul, abs_neg] at h3
  exact ⟨ab_abs_le_of_mul (by positivity) hD h1, ab_abs_le_of_mul (by positivity) hD h3⟩

/-- The determinants of the vertices `r, r̃, q` of the hexagon obtained by cutting the corner `p₀`
at the ratio `μ` (`r = p₀ + μ(e - p₀)`, `r̃ = p₀ + μ(f - p₀)`, `q = q₁`), in the frame `(e, f)`. -/
private lemma ab_det2_cut (hABC : A * B + B * C + C * A = 1) (μ : ℝ) :
    det2 (ab_F e f ((1 - μ) * (A * (B + C)) + μ) ((1 - μ) * (C * (A + B))))
        (ab_F e f ((1 - μ) * (A * (B + C))) ((1 - μ) * (C * (A + B)) + μ)) =
      μ * (1 + (1 - μ) * (A * C)) * det2 e f ∧
    det2 (ab_F e f ((1 - μ) * (A * (B + C))) ((1 - μ) * (C * (A + B)) + μ))
        (ab_F e f (-((A + 2 * B) * (B + C))) (1 + A * B + 2 * B ^ 2)) =
      (2 * A + 2 * B - μ * A) * (B + C) * det2 e f ∧
    det2 (ab_F e f ((1 - μ) * (A * (B + C)) + μ) ((1 - μ) * (C * (A + B))))
        (ab_F e f (-((A + 2 * B) * (B + C))) (1 + A * B + 2 * B ^ 2)) =
      (2 * B + 2 * C - μ * C) * (A + B) * det2 e f := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [ab_det2_F]
  · linear_combination (-μ * (μ - 1) * det2 e f) * hABC
  · linear_combination (-(A + 2 * B) * (B + C) * (μ - 1) * det2 e f) * hABC
  · linear_combination ((-A * B * μ + A * B - A * C * μ + A * C - 2 * B ^ 2 * μ + 2 * B ^ 2 -
      2 * B * C * μ + 2 * B * C - μ) * det2 e f) * hABC

/-- The determinants of the vertices `p₀, p₁, p₂` of `H_K(z)` in the frame `(e, f)`. -/
private lemma ab_det2_hex (hABC : A * B + B * C + C * A = 1) :
    det2 (ab_F e f (A * (B + C)) (C * (A + B))) (ab_F e f (-(A * (B + C))) (1 + A * B)) =
      2 * A * (B + C) * det2 e f ∧
    det2 (ab_F e f (-(A * (B + C))) (1 + A * B)) (ab_F e f (-(1 + B * C)) (C * (A + B))) =
      2 * B * (C + A) * det2 e f ∧
    det2 (ab_F e f (A * (B + C)) (C * (A + B))) (ab_F e f (-(1 + B * C)) (C * (A + B))) =
      2 * C * (A + B) * det2 e f := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [ab_det2_F]
  · linear_combination (A * (B + C) * det2 e f) * hABC
  · linear_combination ((-A * C - 1) * det2 e f) * hABC
  · linear_combination (C * (A + B) * det2 e f) * hABC

/-- The cut hexagon is a centrally symmetric hexagon for `0 < μ ≤ 1`. -/
private lemma ab_hexCond_cut (hD : 0 < det2 e f) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hABC : A * B + B * C + C * A = 1) {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) :
    rein_HexCond (ab_F e f ((1 - μ) * (A * (B + C)) + μ) ((1 - μ) * (C * (A + B))))
      (ab_F e f ((1 - μ) * (A * (B + C))) ((1 - μ) * (C * (A + B)) + μ))
      (ab_F e f (-((A + 2 * B) * (B + C))) (1 + A * B + 2 * B ^ 2)) := by
  obtain ⟨h1, h2, h3⟩ := ab_det2_cut (e := e) (f := f) hABC μ
  have hk : 0 < 2 * A + 2 * B - μ * A := by nlinarith
  have hn : 0 < 2 * B + 2 * C - μ * C := by nlinarith
  have hm : 0 < 1 + (1 - μ) * (A * C) := by
    have : 0 ≤ (1 - μ) * (A * C) := mul_nonneg (by linarith) (by positivity)
    linarith
  have i0 : μ * (1 + (1 - μ) * (A * C)) + (2 * A + 2 * B - μ * A) * (B + C) -
      (2 * B + 2 * C - μ * C) * (A + B) = μ * C * (2 * A + 2 * B - μ * A) := by
    linear_combination (-μ) * hABC
  have i1 : (2 * A + 2 * B - μ * A) * (B + C) + (2 * B + 2 * C - μ * C) * (A + B) -
      μ * (1 + (1 - μ) * (A * C)) = (2 * A + 2 * B - μ * A) * (2 * B + 2 * C - μ * C) := by
    linear_combination μ * hABC
  have i2 : μ * (1 + (1 - μ) * (A * C)) + (2 * B + 2 * C - μ * C) * (A + B) -
      (2 * A + 2 * B - μ * A) * (B + C) = A * μ * (2 * B + 2 * C - μ * C) := by
    linear_combination (-μ) * hABC
  have p0 : 0 < μ * C * (2 * A + 2 * B - μ * A) := by positivity
  have p1 : 0 < (2 * A + 2 * B - μ * A) * (2 * B + 2 * C - μ * C) := by positivity
  have p2 : 0 < A * μ * (2 * B + 2 * C - μ * C) := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [h1, h2, h3]
  · positivity
  · positivity
  · positivity
  · nlinarith [mul_pos p0 hD]
  · nlinarith [mul_pos p1 hD]
  · nlinarith [mul_pos p2 hD]

/-- A point of `H_K(z)` on the inner side of the cut lines lies in the cut hexagon. -/
private lemma ab_mem_cut (hD : 0 < det2 e f) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hABC : A * B + B * C + C * A = 1) {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) {X1 X2 : ℝ}
    (h1 : |B * X1 + (B + C) * X2| ≤ B + C) (h2 : |(A + B) * X1 + B * X2| ≤ A + B)
    (h3 : |X1 + X2| ≤ 1 + (1 - μ) * (A * C)) :
    ab_F e f X1 X2 ∈ hexagonOf (rein_hex3
      (ab_F e f ((1 - μ) * (A * (B + C)) + μ) ((1 - μ) * (C * (A + B))))
      (ab_F e f ((1 - μ) * (A * (B + C))) ((1 - μ) * (C * (A + B)) + μ))
      (ab_F e f (-((A + 2 * B) * (B + C))) (1 + A * B + 2 * B ^ 2))) := by
  rw [rein_mem_hexagonOf_iff_strips (ab_hexCond_cut hD hA hB hC hABC hμ0 hμ1)]
  obtain ⟨d1, d2, d3⟩ := ab_det2_cut (e := e) (f := f) hABC μ
  have hk : 0 < 2 * A + 2 * B - μ * A := by nlinarith
  have hn : 0 < 2 * B + 2 * C - μ * C := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · rw [d1, ab_F_sub, ab_det2_F]
    have : ((1 - μ) * (A * (B + C)) + μ - (1 - μ) * (A * (B + C))) * X2 -
        ((1 - μ) * (C * (A + B)) - ((1 - μ) * (C * (A + B)) + μ)) * X1 = μ * (X1 + X2) := by ring
    rw [this]
    exact ab_mul_abs_le hμ0 hD h3
  · rw [d2, ab_F_sub, ab_det2_F]
    have : ((1 - μ) * (A * (B + C)) - -((A + 2 * B) * (B + C))) * X2 -
        ((1 - μ) * (C * (A + B)) + μ - (1 + A * B + 2 * B ^ 2)) * X1 =
        (2 * A + 2 * B - μ * A) * (B * X1 + (B + C) * X2) := by
      linear_combination (X1 * (μ - 1)) * hABC
    rw [this]
    exact ab_mul_abs_le hk hD h1
  · rw [d3, ab_F_add, ab_det2_F]
    have : (-((A + 2 * B) * (B + C)) + ((1 - μ) * (A * (B + C)) + μ)) * X2 -
        (1 + A * B + 2 * B ^ 2 + (1 - μ) * (C * (A + B))) * X1 =
        -((2 * B + 2 * C - μ * C) * ((A + B) * X1 + B * X2)) := by
      linear_combination (X1 - X2 * μ) * hABC
    rw [this, neg_mul, abs_neg]
    exact ab_mul_abs_le hn hD h2

/-- **The claim in the proof of Theorem 5.0.6, in a frame.** Let `H = H_K(z)` be a least-area
hexagon of `K` with vertices `p₀, p₁, p₂` written in the frame `(e, f) = (s₀*, s₁*)` through the
star functions `A = ρ₀`, `B = ρ₁`, `C = ρ₂`, and cut the corner `p₀` by the segment `[r̃, r]`,
`r = p₀ + λ(e - p₀)`, `r̃ = p₀ + λ(f - p₀)`, with `λ²T₀ ≥ T₀^ext` (here `T₀ = (√3/4)AC` and
`T₀^ext = √3B²`). Then `∂K` meets `[r̃, r]`.

The book's argument: otherwise `K` misses the segment and so lies on the inner side of the cut line
(and of its reflection), so pushing the cut line inward until it meets `K` gives a centrally
symmetric hexagon (the vertices `r_μ, r̃_μ, q₁` and their reflections, `μ > λ`) containing `K` of
area `area(H) - 2μ²T₀ + 2T₀^ext < area(H)`, contradicting the minimality of `H`. Here the push is
made directly to the supporting line of `K` parallel to the cut (the maximum of `x ↦ det(x, f - e)`
on `K`); if that line is not inside the corner, the cut line meets `K`, and the extreme point of
`K` on the cut line is a boundary point of `K` in `[r̃, r]`. -/
private lemma ab_corner {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) (hD : 0 < det2 e f)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hABC : A * B + B * C + C * A = 1)
    (hH : IsLeastAreaHexagon K (rein_hex3 (ab_F e f (A * (B + C)) (C * (A + B)))
      (ab_F e f (-(A * (B + C))) (1 + A * B)) (ab_F e f (-(1 + B * C)) (C * (A + B)))))
    (he : e ∈ K) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hl : 4 * B ^ 2 ≤ l ^ 2 * (A * C)) :
    ∃ r ∈ frontier K, r ∈ segment ℝ
      (ab_F e f ((1 - l) * (A * (B + C))) ((1 - l) * (C * (A + B)) + l))
      (ab_F e f ((1 - l) * (A * (B + C)) + l) ((1 - l) * (C * (A + B)))) := by
  have hD' : det2 e f ≠ 0 := hD.ne'
  have hAC : 0 < A * C := mul_pos hA hC
  have hcond := rein_isCSHexagon_iff_hexCond.1 hH.1
  -- the coordinates of the points of `K` satisfy the strip conditions at the corner
  have hKc : ∀ X1 X2, ab_F e f X1 X2 ∈ K →
      |B * X1 + (B + C) * X2| ≤ B + C ∧ |(A + B) * X1 + B * X2| ≤ A + B := fun X1 X2 hx ↦
    ab_strips_coord hD hA hC hABC ((rein_mem_hexagonOf_iff_strips hcond).1 (hH.2.1 hx))
  -- the functional `ψ(x) = det(x, f - e)`, constant on the lines parallel to the cut
  have hfe : f - e = ab_F e f (-1) 1 := by simp only [ab_F]; module
  have hψF : ∀ X1 X2, det2 (ab_F e f X1 X2) (f - e) = (X1 + X2) * det2 e f := by
    intro X1 X2; rw [hfe, ab_det2_F]; ring
  have hψe : det2 e (f - e) = det2 e f := by
    rw [rein_det2_sub_right, rein_det2_self, sub_zero]
  have hψc : Continuous fun x ↦ det2 x (f - e) := rein_continuous_det2_right _
  obtain ⟨k₀, hk₀K, hk₀⟩ := hK.2.1.exists_isMaxOn ⟨e, he⟩ hψc.continuousOn
  have hk₀' : ∀ x ∈ K, det2 x (f - e) ≤ det2 k₀ (f - e) := isMaxOn_iff.1 hk₀
  have hmD : det2 e f ≤ det2 k₀ (f - e) := hψe ▸ hk₀' e he
  by_cases hm : (1 + (1 - l) * (A * C)) * det2 e f ≤ det2 k₀ (f - e)
  · -- the cut line meets `K`
    obtain ⟨z, hzK, hzψ⟩ : ∃ z ∈ K, det2 z (f - e) = (1 + (1 - l) * (A * C)) * det2 e f := by
      have hc0 : 0 ≤ (1 - l) * (A * C) * det2 e f :=
        mul_nonneg (mul_nonneg (by linarith) hAC.le) hD.le
      rcases eq_or_lt_of_le hmD with hmD' | hmD'
      · refine ⟨e, he, ?_⟩
        rw [hψe]
        linarith
      · set t := ((1 + (1 - l) * (A * C)) * det2 e f - det2 e f) / (det2 k₀ (f - e) - det2 e f)
          with ht
        have hpos : 0 < det2 k₀ (f - e) - det2 e f := by linarith
        have ht0 : 0 ≤ t := div_nonneg (by linarith) hpos.le
        have ht1 : t ≤ 1 := by rw [ht, div_le_one hpos]; linarith
        refine ⟨e + t • (k₀ - e), hK.1.add_smul_sub_mem he hk₀K ⟨ht0, ht1⟩, ?_⟩
        rw [rein_det2_add_left, rein_det2_smul_left, rein_det2_sub_left, hψe, ht]
        field_simp
        ring
    -- the extreme point of `K` on the cut line, in the direction `e - f`
    have hS : IsCompact (K ∩ {x | det2 x (f - e) = (1 + (1 - l) * (A * C)) * det2 e f}) :=
      hK.2.1.inter_right (isClosed_eq hψc continuous_const)
    obtain ⟨w, ⟨hwK, hwψ⟩, hwmax⟩ :=
      hS.exists_isMaxOn ⟨z, hzK, hzψ⟩ (rein_continuous_det2_right f).continuousOn
    have hwmax' := isMaxOn_iff.1 hwmax
    simp only [mem_ofPred_eq] at hwψ
    refine ⟨w, ?_, ?_⟩
    · rw [hK.2.1.isClosed.frontier_eq]
      refine ⟨hwK, fun hwi ↦ ?_⟩
      obtain ⟨t, ht, htK⟩ := rein_exists_add_smul_mem hwi (e - f)
      have h1 : det2 (w + t • (e - f)) (f - e) = (1 + (1 - l) * (A * C)) * det2 e f := by
        rw [rein_det2_add_left, rein_det2_smul_left, show e - f = -(f - e) by abel,
          rein_det2_neg_left, rein_det2_self, hwψ]
        ring
      have h2 := hwmax' _ ⟨htK, h1⟩
      rw [rein_det2_add_left, rein_det2_smul_left, rein_det2_sub_left, rein_det2_self] at h2
      nlinarith [mul_pos ht hD]
    · obtain ⟨X1, X2, rfl⟩ := ab_exists_F hD' w
      obtain ⟨h1, h2⟩ := hKc X1 X2 hwK
      rw [hψF] at hwψ
      have hsum : X1 + X2 = 1 + (1 - l) * (A * C) := mul_right_cancel₀ hD' hwψ
      have hl0' : 0 < l := by
        rcases eq_or_lt_of_le hl0 with h | h
        · subst h; nlinarith
        · exact h
      have hBC : A * (B + C) = 1 - B * C := by linear_combination hABC
      have hAB : C * (A + B) = 1 - A * B := by linear_combination hABC
      set t := (X1 - (1 - l) * (A * (B + C))) / l with ht
      have hX1lo : (1 - l) * (A * (B + C)) ≤ X1 := by
        have := (abs_le.1 h1).2
        have hX2 : X2 = 1 + (1 - l) * (A * C) - X1 := by linarith
        rw [hX2] at this
        have : (1 - l) * (A * (B + C)) * C ≤ X1 * C := by nlinarith
        exact le_of_mul_le_mul_right this hC
      have hX1hi : X1 ≤ (1 - l) * (A * (B + C)) + l := by
        have := (abs_le.1 h2).2
        have hX2 : X2 = 1 + (1 - l) * (A * C) - X1 := by linarith
        rw [hX2] at this
        have e1 : ((1 - l) * (A * (B + C)) + l) * A = A - (1 - l) * (A * C) * B := by
          linear_combination ((1 - l) * A) * hABC
        have : X1 * A ≤ ((1 - l) * (A * (B + C)) + l) * A := by rw [e1]; linarith
        exact le_of_mul_le_mul_right this hA
      have ht0 : 0 ≤ t := div_nonneg (by linarith) hl0'.le
      have ht1 : t ≤ 1 := by rw [ht, div_le_one hl0']; linarith
      refine ⟨1 - t, t, by linarith, ht0, by ring, ?_⟩
      rw [ab_F_smul, ab_F_smul, ab_F_add]
      congr 1
      · rw [ht]; field_simp; ring
      · rw [ht]; field_simp; linear_combination (-l) * hsum + l * (1 - l) * hABC
  · -- otherwise the hexagon cut at the supporting line of `K` is smaller than `H`
    replace hm := not_le.1 hm
    exfalso
    set m := det2 k₀ (f - e) with hm_def
    set μ := 1 - (m / det2 e f - 1) / (A * C) with hμ
    have hμm : (1 + (1 - μ) * (A * C)) * det2 e f = m := by
      rw [hμ]; field_simp; ring
    have hlμ : l < μ := by
      rw [hμ, lt_sub_iff_add_lt, ← lt_sub_iff_add_lt', div_lt_iff₀ hAC, sub_lt_iff_lt_add,
        div_lt_iff₀ hD]
      linarith
    have hμ1 : μ ≤ 1 := by
      rw [hμ, sub_le_self_iff]
      exact div_nonneg (by rw [sub_nonneg, le_div_iff₀ hD]; linarith) hAC.le
    have hμ0 : 0 < μ := by linarith
    have hc' := ab_hexCond_cut (e := e) (f := f) hD hA hB hC hABC hμ0 hμ1
    have hsub : K ⊆ hexagonOf (rein_hex3
        (ab_F e f ((1 - μ) * (A * (B + C)) + μ) ((1 - μ) * (C * (A + B))))
        (ab_F e f ((1 - μ) * (A * (B + C))) ((1 - μ) * (C * (A + B)) + μ))
        (ab_F e f (-((A + 2 * B) * (B + C))) (1 + A * B + 2 * B ^ 2))) := by
      intro x hx
      obtain ⟨X1, X2, rfl⟩ := ab_exists_F hD' x
      obtain ⟨h1, h2⟩ := hKc X1 X2 hx
      have hup := hk₀' _ hx
      have hdn := hk₀' _ (hK.2.2.2 _ hx)
      rw [hψF] at hup
      rw [ab_F_neg, hψF] at hdn
      refine ab_mem_cut hD hA hB hC hABC hμ0 hμ1 h1 h2 ?_
      rw [← hμm] at hup hdn
      rw [abs_le]
      constructor
      · nlinarith
      · nlinarith
    have hvol := hH.2.2 _ (rein_isCSHexagon_iff_hexCond.2 hc') hsub
    obtain ⟨d1, d2, d3⟩ := ab_det2_cut (e := e) (f := f) hABC μ
    obtain ⟨e1, e2, e3⟩ := ab_det2_hex (e := e) (f := f) hABC
    rw [rein_volume_hexagonOf_hex3' hcond, rein_volume_hexagonOf_hex3' hc', d1, d2, d3, e1, e2,
      e3, ENNReal.ofReal_le_ofReal_iff (by rw [← d1, ← d2, ← d3]; linarith [hc'.hA, hc'.hB,
        hc'.hC])] at hvol
    have key : μ * (1 + (1 - μ) * (A * C)) * det2 e f +
        (2 * A + 2 * B - μ * A) * (B + C) * det2 e f +
        (2 * B + 2 * C - μ * C) * (A + B) * det2 e f -
        (2 * A * (B + C) * det2 e f + 2 * B * (C + A) * det2 e f + 2 * C * (A + B) * det2 e f) =
        (4 * B ^ 2 - μ ^ 2 * (A * C)) * det2 e f := by
      linear_combination (-μ * det2 e f) * hABC
    have hμl : l ^ 2 < μ ^ 2 := by nlinarith
    nlinarith [mul_lt_mul_of_pos_right hμl hAC]

end corner


/-! ### The hexagon `H_K(z)` in the frame `(s_j*, s_{j+1}*)` -/

/-- `ρ_{j+3} = ρ_j`. -/
private lemma ab_starFn_add_three (X : Mat2) (j : ZMod 6) : starFn X (j + 3) = starFn X j := by
  rcases rein_zmod6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The vertices `p_j, p_{j+1}, p_{j+2}` of `H_K(z)` in the frame `(s_j*, s_{j+1}*)`, with
`A = ρ_j`, `B = ρ_{j+1}`, `C = ρ_{j+2}` (`eqn:hex-vertex` and `eqn:rho-star-inequalities`). -/
private lemma ab_hexVertex_frame {x y : ℝ} (hz : (x, y) ∈ starDomain) (j : ZMod 6) {A B C : ℝ}
    (hA : starFn (Φ x y) j = A) (hB : starFn (Φ x y) (j + 1) = B)
    (hC : starFn (Φ x y) (j + 2) = C) :
    hexVertex x y j = ab_F (sixthRoot j) (sixthRoot (j + 1)) (A * (B + C)) (C * (A + B)) ∧
    hexVertex x y (j + 1) = ab_F (sixthRoot j) (sixthRoot (j + 1)) (-(A * (B + C))) (1 + A * B) ∧
    hexVertex x y (j + 2) =
      ab_F (sixthRoot j) (sixthRoot (j + 1)) (-(1 + B * C)) (C * (A + B)) := by
  have htr : (Φ x y) 1 1 = -(Φ x y) 0 0 := by simp [Φ]; ring
  have hABC : A * B + B * C + C * A = 1 := by
    rw [← hA, ← hB, ← hC]; exact starFn_Φ_mul_add_eq_one hz j
  have hs2 : sixthRoot (j + 2) = sixthRoot (j + 1) - sixthRoot j := by
    rw [(rein_sixthRoot_rel j).2.1]; abel
  have hs3 : sixthRoot (j + 3) = -sixthRoot j := (rein_sixthRoot_rel j).1
  have hs4 : sixthRoot (j + 4) = -sixthRoot (j + 1) := by
    rw [← (rein_sixthRoot_rel (j + 1)).1]; ring_nf
  have hA3 : starFn (Φ x y) (j + 3) = A := by rw [ab_starFn_add_three, hA]
  have hB3 : starFn (Φ x y) (j + 4) = B := by
    rw [show j + 4 = j + 1 + 3 by ring, ab_starFn_add_three, hB]
  refine ⟨?_, ?_, ?_⟩
  · rw [hexVertex, mulVec_sixthRoot_eq_starFn htr, hA, hB, hC, hs2,
      show A * (B + C) = 1 - B * C by linear_combination hABC]
    simp only [ab_F]; module
  · rw [hexVertex, mulVec_sixthRoot_eq_starFn htr, show j + 1 + 2 = j + 3 by ring,
      show j + 1 + 1 = j + 2 by ring, hA3, hB, hC, hs2, hs3]
    simp only [ab_F]; module
  · rw [hexVertex, mulVec_sixthRoot_eq_starFn htr, show j + 2 + 2 = j + 4 by ring,
      show j + 2 + 1 = j + 3 by ring, hB3, hA3, hC, hs2, hs3, hs4,
      show C * (A + B) = 1 - A * B by linear_combination hABC]
    simp only [ab_F]; module

/-- The areas of Lemma 5.0.4 in terms of `ρ_i`, `ρ_{i+1}`, `ρ_{i+2}`. -/
private lemma ab_areas {x y : ℝ} (hz : (x, y) ∈ starDomain) (i : Fin 3) :
    triArea x y i = √3 / 4 * (starFn (Φ x y) (i.val : ZMod 6) *
      starFn (Φ x y) ((i.val : ZMod 6) + 2)) ∧
    extTriArea x y i = √3 * starFn (Φ x y) ((i.val : ZMod 6) + 1) ^ 2 := by
  obtain ⟨t0, t1, t2, e0, e1, e2, -⟩ := lemma5_0_4 hz
  fin_cases i
  · exact ⟨t0.trans (by rw [mul_assoc]; rfl), e0.trans rfl⟩
  · exact ⟨t1.trans (by rw [mul_assoc, mul_comm (ρ₀ _)]; rfl), e1.trans rfl⟩
  · exact ⟨t2.trans (by rw [mul_assoc, mul_comm (ρ₁ _)]; rfl), e2.trans rfl⟩

/-- The sixth roots of unity lie on the boundary of a balanced disk in circle representation. -/
private lemma ab_sixthRoot_mem_frontier {K : Set (Fin 2 → ℝ)} {σ : ZMod 6 → ℝ → Fin 2 → ℝ}
    {tf : ℝ} (hKσ : IsBalancedPair K σ tf) (hcirc : IsCircleRepresentation σ) (j : ZMod 6) :
    sixthRoot j ∈ frontier K := by
  have htf : 0 < tf := hKσ.2.2.2.2.2.2.1
  rw [← hKσ.2.2.2.2.2.2.2.2.2 j, ← hcirc j]
  exact mem_image_of_mem _ ⟨le_rfl, by linarith⟩

/-! ### The two claims of the proof -/

/-- `h₀ ∩ h₁ ∩ h₂ = ∅` (proof of Theorem 5.0.6, TeX 4229–4241): by Lemma 5.0.4 and Cauchy–Schwarz,
`Σ T_i ≤ (1/4) Σ T_i^ext < Σ T_i^ext`. -/
theorem inter_hRegion_eq_empty : hRegion 0 ∩ hRegion 1 ∩ hRegion 2 = ∅ := by
  refine eq_empty_of_forall_notMem ?_
  rintro ⟨x, y⟩ ⟨⟨h0, h1⟩, h2⟩
  have hz : (x, y) ∈ starDomain := h0.1
  obtain ⟨-, -, p0, p1, p2⟩ := (theorem4_4_1 x y hz.1).2 hz
  obtain ⟨t0, t1, t2, e0, e1, e2, -⟩ := lemma5_0_4 hz
  have c0 : extTriArea x y 0 ≤ triArea x y 0 := h0.2
  have c1 : extTriArea x y 1 ≤ triArea x y 1 := h1.2
  have c2 : extTriArea x y 2 ≤ triArea x y 2 := h2.2
  rw [t0, e0] at c0
  rw [t1, e1] at c1
  rw [t2, e2] at c2
  have h3 : 0 < √3 := by positivity
  -- `Σ T_i^ext ≤ Σ T_i = (√3/4)(ρ₀ρ₂ + ρ₀ρ₁ + ρ₁ρ₂) ≤ (√3/4)(ρ₀² + ρ₁² + ρ₂²) = (1/4) Σ T_i^ext`
  -- (Cauchy–Schwarz), impossible as `Σ T_i^ext > 0`
  have hcs : ρ₀ (Φ x y) * ρ₂ (Φ x y) + ρ₀ (Φ x y) * ρ₁ (Φ x y) + ρ₁ (Φ x y) * ρ₂ (Φ x y) ≤
      ρ₀ (Φ x y) ^ 2 + ρ₁ (Φ x y) ^ 2 + ρ₂ (Φ x y) ^ 2 := by
    nlinarith [sq_nonneg (ρ₀ (Φ x y) - ρ₁ (Φ x y)), sq_nonneg (ρ₁ (Φ x y) - ρ₂ (Φ x y)),
      sq_nonneg (ρ₀ (Φ x y) - ρ₂ (Φ x y))]
  have hsum : √3 * (ρ₀ (Φ x y) ^ 2 + ρ₁ (Φ x y) ^ 2 + ρ₂ (Φ x y) ^ 2) ≤
      √3 / 4 * (ρ₀ (Φ x y) ^ 2 + ρ₁ (Φ x y) ^ 2 + ρ₂ (Φ x y) ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hcs (by positivity : (0 : ℝ) ≤ √3 / 4)]
  nlinarith [mul_pos h3 (mul_pos p0 p0)]

/-- **The claim in the proof of Theorem 5.0.6** (Case 1, TeX 4271–4281). Let `K` be a balanced
disk in circle representation with critical hexagon `H_K(z)`, `z ∈ 𝔥*`. If `z ∈ h_i`, the boundary
of `K` meets the cut segment `[r̃₀, r₀]` of the corner `p_i`. -/
theorem exists_mem_frontier_segment_cut {K : Set (Fin 2 → ℝ)} {σ : ZMod 6 → ℝ → Fin 2 → ℝ}
    {tf : ℝ} (hKσ : IsBalancedPair K σ tf) (hcirc : IsCircleRepresentation σ) {x y : ℝ}
    (hz : (x, y) ∈ starDomain) (hH : IsLeastAreaHexagon K (hexVertex x y)) {i : Fin 3}
    (hi : (x, y) ∈ hRegion i) :
    ∃ r ∈ frontier K, r ∈ segment ℝ (cutPoint' x y i) (cutPoint x y i) := by
  have hK : IsCCSDisk K := hKσ.1
  obtain ⟨hT, hTe⟩ := ab_areas hz i
  set j : ZMod 6 := (i.val : ZMod 6) with hj
  set A := starFn (Φ x y) j with hA
  set B := starFn (Φ x y) (j + 1) with hB
  set C := starFn (Φ x y) (j + 2) with hC
  have hA0 : 0 < A := starFn_Φ_pos hz _
  have hB0 : 0 < B := starFn_Φ_pos hz _
  have hC0 : 0 < C := starFn_Φ_pos hz _
  have hABC : A * B + B * C + C * A = 1 := starFn_Φ_mul_add_eq_one hz j
  obtain ⟨hv0, hv1, hv2⟩ := ab_hexVertex_frame hz j hA.symm hB.symm hC.symm
  have hw : IsLeastAreaHexagon K
      (rein_hex3 (hexVertex x y j) (hexVertex x y (j + 1)) (hexVertex x y (j + 2))) := by
    have h := rein_isLeastAreaHexagon_shift hH j
    rw [rein_eq_hex3 h.1] at h
    simpa only [zero_add, add_comm _ j, add_zero] using h
  rw [hv0, hv1, hv2] at hw
  have he : sixthRoot j ∈ K :=
    rein_frontier_subset hK (ab_sixthRoot_mem_frontier hKσ hcirc j)
  -- the cut ratio `λ = √(T^ext/T)`
  have hAC : 0 < A * C := mul_pos hA0 hC0
  have hTpos : 0 < triArea x y i := by rw [hT]; positivity
  set l := cutRatio x y i with hl
  have hl0 : 0 ≤ l := Real.sqrt_nonneg _
  have hl1 : l ≤ 1 := Real.sqrt_le_one.2 ((div_le_one hTpos).2 hi.2)
  have hl2 : l ^ 2 * (A * C) = 4 * B ^ 2 := by
    rw [hl, cutRatio, Real.sq_sqrt (div_nonneg (by rw [hTe]; positivity) hTpos.le), hT, hTe]
    have h3 : (0 : ℝ) < √3 := by positivity
    field_simp
  obtain ⟨r, hr, hseg⟩ := ab_corner hK (rein_det2_sixthRoot_pos j) hA0 hB0 hC0 hABC hw he hl0
    hl1 hl2.ge
  refine ⟨r, hr, ?_⟩
  convert hseg using 2
  · rw [cutPoint', hv0]; simp only [ab_F]; module
  · rw [cutPoint, hv0]; simp only [ab_F]; module


/-! ### The area bound -/

private lemma ab_det2_F_right (e f : Fin 2 → ℝ) (p q : ℝ) :
    det2 (ab_F e f p q) f = p * det2 e f := by
  simp only [ab_F, det2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

private lemma ab_det2_left_F (e f : Fin 2 → ℝ) (p q : ℝ) :
    det2 e (ab_F e f p q) = q * det2 e f := by
  simp only [ab_F, det2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

/-- The vertex `p_j` of `H_K(z)` lies in the triangle `s_j* s_{j+1}* (s_j* + s_{j+1}*)`. -/
private lemma ab_hexVertex_mem_sixthTriangle {x y : ℝ} (hz : (x, y) ∈ starDomain) (j : ZMod 6) :
    hexVertex x y j ∈ sixthTriangle j := by
  have hA := starFn_Φ_pos hz j
  have hB := starFn_Φ_pos hz (j + 1)
  have hC := starFn_Φ_pos hz (j + 2)
  have hABC := starFn_Φ_mul_add_eq_one hz j
  have hD := rein_det2_sixthRoot_pos j
  rw [(ab_hexVertex_frame hz j rfl rfl rfl).1, sixthTriangle, rein_mem_convexHull_triple hD,
    ab_det2_F_right, ab_det2_left_F]
  set A := starFn (Φ x y) j
  set B := starFn (Φ x y) (j + 1)
  set C := starFn (Φ x y) (j + 2)
  have e1 : A * (B + C) = 1 - B * C := by linear_combination hABC
  have e2 : C * (A + B) = 1 - A * B := by linear_combination hABC
  rw [e1, e2]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith [mul_pos (mul_pos hB hC) hD, mul_pos (mul_pos hA hB) hD,
    mul_pos (mul_pos hA hC) hD]

/-- `0 ≤ λ_i ≤ 1` on `h_i`, and `λ_i² T_i = T_i^ext`. -/
private lemma ab_cutRatio {x y : ℝ} (hz : (x, y) ∈ starDomain) {i : Fin 3}
    (hi : (x, y) ∈ hRegion i) :
    0 ≤ cutRatio x y i ∧ cutRatio x y i ≤ 1 ∧ 0 < triArea x y i ∧
      cutRatio x y i ^ 2 * triArea x y i = extTriArea x y i := by
  obtain ⟨hT, -⟩ := ab_areas hz i
  have hTpos : 0 < triArea x y i := by
    rw [hT]; have := starFn_Φ_pos hz (i.val : ZMod 6)
    have := starFn_Φ_pos hz ((i.val : ZMod 6) + 2); positivity
  refine ⟨Real.sqrt_nonneg _, Real.sqrt_le_one.2 ((div_le_one hTpos).2 hi.2), hTpos, ?_⟩
  have hTe0 : 0 ≤ extTriArea x y i := measureReal_nonneg
  rw [cutRatio, Real.sq_sqrt (div_nonneg hTe0 hTpos.le)]
  field_simp

/-- The cut points lie in the triangle `s_i* s_{i+1}* (s_i* + s_{i+1}*)`, which contains `T_i`. -/
private lemma ab_cutPoint_mem {x y : ℝ} (hz : (x, y) ∈ starDomain) {i : Fin 3}
    (hi : (x, y) ∈ hRegion i) :
    cutPoint x y i ∈ sixthTriangle (i.val : ZMod 6) ∧
      cutPoint' x y i ∈ sixthTriangle (i.val : ZMod 6) := by
  obtain ⟨hl0, hl1, -⟩ := ab_cutRatio hz hi
  have hp := ab_hexVertex_mem_sixthTriangle hz (i.val : ZMod 6)
  have hconv : Convex ℝ (sixthTriangle (i.val : ZMod 6)) := convex_convexHull ℝ _
  have hs : sixthRoot (i.val : ZMod 6) ∈ sixthTriangle (i.val : ZMod 6) :=
    subset_convexHull ℝ _ (by simp)
  have hs' : sixthRoot ((i.val : ZMod 6) + 1) ∈ sixthTriangle (i.val : ZMod 6) :=
    subset_convexHull ℝ _ (by simp)
  exact ⟨hconv.add_smul_sub_mem hp hs ⟨hl0, hl1⟩, hconv.add_smul_sub_mem hp hs' ⟨hl0, hl1⟩⟩

/-- The triangle `r₀ p₀ r̃₀` is the image of `T_i` under the homothety of center `p_i` and
ratio `λ_i`, so its area is `λ_i² T_i`. -/
private lemma ab_volume_cut (x y : ℝ) (i : Fin 3) :
    volume.real (convexHull ℝ {cutPoint x y i, hexVertex x y (i.val : ZMod 6), cutPoint' x y i}) =
      cutRatio x y i ^ 2 * triArea x y i := by
  have himg : convexHull ℝ {cutPoint x y i, hexVertex x y (i.val : ZMod 6), cutPoint' x y i} =
      AffineMap.homothety (hexVertex x y (i.val : ZMod 6)) (cutRatio x y i) ''
        innerTriangle x y i := by
    rw [innerTriangle, AffineMap.image_convexHull]
    congr 1
    simp only [image_insert_eq, image_singleton, AffineMap.homothety_apply_same,
      AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, cutPoint, cutPoint', add_comm]
  rw [himg, triArea, measureReal_def, measureReal_def, Measure.addHaar_image_homothety,
    Module.finrank_fin_fun, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _),
    abs_of_nonneg (sq_nonneg _)]

/-- **The pieces of the proof of Theorem 5.0.6.** For `z ∈ h_i` and a boundary point `r` of `K` on
the cut segment, the triangle `△ s_i* r s_{i+1}*` lies in `K` and beyond the edge `s_i* s_{i+1}*`
(in `s_i* s_{i+1}* (s_i* + s_{i+1}*)`), and its area is `area_i(z)` (Lemma 5.0.5). -/
private lemma ab_piece {K : Set (Fin 2 → ℝ)} {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {tf : ℝ}
    (hKσ : IsBalancedPair K σ tf) (hcirc : IsCircleRepresentation σ) {x y : ℝ}
    (hz : (x, y) ∈ starDomain) {i : Fin 3} (hi : (x, y) ∈ hRegion i) {r : Fin 2 → ℝ}
    (hrK : r ∈ frontier K) (hr : r ∈ segment ℝ (cutPoint' x y i) (cutPoint x y i)) :
    convexHull ℝ {sixthRoot (i.val : ZMod 6), sixthRoot ((i.val : ZMod 6) + 1), r} ⊆ K ∧
      convexHull ℝ {sixthRoot (i.val : ZMod 6), sixthRoot ((i.val : ZMod 6) + 1), r} ⊆
        sixthTriangle (i.val : ZMod 6) ∧
      volume.real (convexHull ℝ {sixthRoot (i.val : ZMod 6), sixthRoot ((i.val : ZMod 6) + 1), r}) =
        areaFn i (x, y) := by
  have hK : IsCCSDisk K := hKσ.1
  set j : ZMod 6 := (i.val : ZMod 6)
  obtain ⟨hl0, hl1, hTpos, hl2⟩ := ab_cutRatio hz hi
  obtain ⟨hc, hc'⟩ := ab_cutPoint_mem hz hi
  refine ⟨?_, ?_, ?_⟩
  · refine convexHull_min ?_ hK.1
    simp only [insert_subset_iff, singleton_subset_iff]
    exact ⟨rein_frontier_subset hK (ab_sixthRoot_mem_frontier hKσ hcirc j),
      rein_frontier_subset hK (ab_sixthRoot_mem_frontier hKσ hcirc (j + 1)),
      rein_frontier_subset hK hrK⟩
  · refine convexHull_min ?_ (convex_convexHull ℝ _)
    simp only [insert_subset_iff, singleton_subset_iff]
    exact ⟨subset_convexHull ℝ _ (by simp), subset_convexHull ℝ _ (by simp),
      (convex_convexHull ℝ _).segment_subset hc' hc hr⟩
  · have hr₀ : cutPoint x y i ∈ segment ℝ (sixthRoot j) (hexVertex x y j) := by
      refine ⟨cutRatio x y i, 1 - cutRatio x y i, hl0, by linarith, by ring, ?_⟩
      rw [cutPoint]; module
    have hr₀' : cutPoint' x y i ∈ segment ℝ (sixthRoot (j + 1)) (hexVertex x y j) := by
      refine ⟨cutRatio x y i, 1 - cutRatio x y i, hl0, by linarith, by ring, ?_⟩
      rw [cutPoint']; module
    have hpar : det2 (cutPoint' x y i - cutPoint x y i) (sixthRoot (j + 1) - sixthRoot j) = 0 := by
      have : cutPoint' x y i - cutPoint x y i =
          cutRatio x y i • (sixthRoot (j + 1) - sixthRoot j) := by
        rw [cutPoint, cutPoint']; module
      rw [this, rein_det2_smul_left, rein_det2_self, mul_zero]
    rw [lemma5_0_5 hr₀ hr₀' hpar hr, ab_volume_cut, ← innerTriangle, ← triArea, hl2, areaFn]


/-- The sixth roots of unity are the vertices of a centrally symmetric hexagon. -/
private lemma ab_isCSHexagon_sixthRoot : IsCSHexagon sixthRoot := by
  intro j
  obtain ⟨h3, h1, hd⟩ := rein_sixthRoot_rel j
  refine ⟨h3, by rw [hd]; positivity, ?_⟩
  have e1 : sixthRoot (j + 1) - sixthRoot j = sixthRoot (j + 2) := by rw [h1]; abel
  have e2 : sixthRoot (j + 2) - sixthRoot (j + 1) = sixthRoot (j + 3) := by rw [h3, h1]; abel
  have e3 := (rein_sixthRoot_rel (j + 2)).2.2
  rw [show j + 2 + 1 = j + 3 by ring] at e3
  rw [e1, e2, e3]
  positivity

/-- The hexagon `h_K = conv{s_j*}` has area `3√3/2`. -/
private lemma ab_volume_hexS : volume (hexagonOf sixthRoot) = ENNReal.ofReal (3 * √3 / 2) := by
  have h := ab_isCSHexagon_sixthRoot
  have h' := h
  rw [rein_eq_hex3 h'] at h ⊢
  have d01 : det2 (sixthRoot 0) (sixthRoot 1) = √3 / 2 := (rein_sixthRoot_rel 0).2.2
  have d12 : det2 (sixthRoot 1) (sixthRoot 2) = √3 / 2 := (rein_sixthRoot_rel 1).2.2
  have d02 : det2 (sixthRoot 0) (sixthRoot 2) = √3 / 2 := by
    simp [rein_sixthRoot_zero, rein_sixthRoot_two, det2]
  rw [rein_volume_hexagonOf_hex3 h, d01, d12, d02]
  congr 1
  ring

/-- `{x | |f x| ≤ 1}` is convex for a linear `f`. -/
private lemma ab_convex_abs_le {f : (Fin 2 → ℝ) → ℝ} (hf : IsLinearMap ℝ f) :
    Convex ℝ {x | |f x| ≤ 1} := by
  have : {x | |f x| ≤ 1} = {x | f x ≤ 1} ∩ {x | -1 ≤ f x} := by
    ext x; simp only [mem_ofPred_eq, mem_inter_iff, abs_le]; tauto
  rw [this]
  exact (convex_halfSpace_le hf 1).inter (convex_halfSpace_ge hf (-1))

/-- The hexagon `conv{s_j*}` in the coordinates `x = A s₀* + B s₁*`: `|A + B|, |A|, |B| ≤ 1`. -/
private lemma ab_hexS_coord {x : Fin 2 → ℝ} (hx : x ∈ hexagonOf sixthRoot) :
    |rein_cA x + rein_cB x| ≤ 1 ∧ |rein_cA x| ≤ 1 ∧ |rein_cB x| ≤ 1 := by
  have hA : IsLinearMap ℝ rein_cA :=
    ⟨rein_cA_add, fun c x ↦ by rw [rein_cA_smul, smul_eq_mul]⟩
  have hB : IsLinearMap ℝ rein_cB :=
    ⟨rein_cB_add, fun c x ↦ by rw [rein_cB_smul, smul_eq_mul]⟩
  have hAB : IsLinearMap ℝ fun x ↦ rein_cA x + rein_cB x :=
    ⟨fun x y ↦ by rw [rein_cA_add, rein_cB_add]; ring,
      fun c x ↦ by rw [rein_cA_smul, rein_cB_smul, smul_eq_mul]; ring⟩
  have hconv := (ab_convex_abs_le hAB).inter ((ab_convex_abs_le hA).inter (ab_convex_abs_le hB))
  refine convexHull_min ?_ hconv hx
  rintro _ ⟨k, rfl⟩
  obtain ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩, ⟨a4, b4⟩, ⟨a5, b5⟩⟩ := rein_coord_sixthRoot
  rcases rein_zmod6_cases k with rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [mem_inter_iff, mem_ofPred_eq, a0, b0, a1, b1, a2, b2, a3, b3, a4, b4, a5, b5] <;>
  norm_num

/-- `conv{s_j*}` does not meet the interior of `s_k* s_{k+1}* (s_k* + s_{k+1}*)`. -/
private lemma ab_hexS_disj {k : ZMod 6} {x : Fin 2 → ℝ} (hx : x ∈ hexagonOf sixthRoot)
    (hx' : x ∈ interior (sixthTriangle k)) : False := by
  obtain ⟨h1, h2, h3⟩ := ab_hexS_coord hx
  rw [rein_mem_interior_sixthTriangle] at hx'
  rw [abs_le] at h1 h2 h3
  rcases rein_zmod6_cases k with rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [rein_InTo_zero, rein_InTo_one, rein_InTo_two, rein_InTo_three, rein_InTo_four,
    rein_InTo_five] at hx' <;>
  linarith [hx'.1, hx'.2.1, hx'.2.2]

/-- Two different triangles `s_k* s_{k+1}* (s_k* + s_{k+1}*)` have disjoint interiors: the interior
of one does not meet the other. -/
private lemma ab_sixthTriangle_disj {k k' : ZMod 6} (hkk : k ≠ k') {x : Fin 2 → ℝ}
    (h : x ∈ interior (sixthTriangle k)) (h' : x ∈ sixthTriangle k') : False := by
  rw [rein_mem_interior_sixthTriangle] at h
  rw [rein_mem_sixthTriangle] at h'
  generalize rein_cA x = a at h h'
  generalize rein_cB x = b at h h'
  rcases rein_zmod6_cases k with rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases rein_zmod6_cases k' with rfl | rfl | rfl | rfl | rfl | rfl <;>
  first
    | exact hkk rfl
    | (simp only [rein_InTo_zero, rein_InTo_one, rein_InTo_two, rein_InTo_three, rein_InTo_four,
        rein_InTo_five, rein_InT_zero, rein_InT_one, rein_InT_two, rein_InT_three, rein_InT_four,
        rein_InT_five] at h h'
       linarith [h.1, h.2.1, h.2.2, h'.1, h'.2.1, h'.2.2])

/-- A set inside `s_k* s_{k+1}* (s_k* + s_{k+1}*)` meets its complement in a null set. -/
private lemma ab_inter_sixthTriangle_null {k : ZMod 6} {S T : Set (Fin 2 → ℝ)}
    (hS : S ⊆ sixthTriangle k) (hT : ∀ x ∈ T, x ∉ interior (sixthTriangle k)) :
    volume (S ∩ T) = 0 := by
  refine measure_mono_null ?_ (Convex.addHaar_frontier volume (s := sixthTriangle k)
    (convex_convexHull ℝ _))
  rintro x ⟨hxS, hxT⟩
  exact ⟨subset_closure (hS hxS), hT x hxT⟩

/-- `-(s_k* s_{k+1}* (s_k* + s_{k+1}*)) = s_{k+3}* s_{k+4}* (s_{k+3}* + s_{k+4}*)`. -/
private lemma ab_neg_mem_sixthTriangle {k : ZMod 6} {x : Fin 2 → ℝ}
    (hx : -x ∈ sixthTriangle k) : x ∈ sixthTriangle (k + 3) := by
  rw [rein_mem_sixthTriangle, rein_cA_neg, rein_cB_neg] at hx
  have := (rein_InT_add_three k (-rein_cA x) (-rein_cB x)).2 hx
  rwa [neg_neg, neg_neg, ← rein_mem_sixthTriangle] at this


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
  classical
  have hK : IsCCSDisk K := hKσ.1
  -- the claim of Case 1, at every corner `p_i` with `z ∈ h_i`
  have hclaim : ∀ i : Fin 3, (x, y) ∈ hRegion i →
      ∃ r ∈ frontier K, r ∈ segment ℝ (cutPoint' x y i) (cutPoint x y i) :=
    fun i hi ↦ exists_mem_frontier_segment_cut hKσ hcirc hz hH hi
  choose! r hrK hrseg using hclaim
  -- the triangles `△ s_i* r_i s_{i+1}*` for `z ∈ h_i` (empty otherwise)
  set T : Fin 3 → Set (Fin 2 → ℝ) := fun i ↦ if (x, y) ∈ hRegion i then
    convexHull ℝ {sixthRoot (i.val : ZMod 6), sixthRoot ((i.val : ZMod 6) + 1), r i} else ∅
    with hT
  have hTK : ∀ i, T i ⊆ K ∧ T i ⊆ sixthTriangle (i.val : ZMod 6) ∧
      volume (T i) = ENNReal.ofReal ((hRegion i).indicator (areaFn i) (x, y)) ∧
      0 ≤ (hRegion i).indicator (areaFn i) (x, y) ∧ MeasurableSet (T i) := by
    intro i
    by_cases hi : (x, y) ∈ hRegion i
    · obtain ⟨h1, h2, h3⟩ := ab_piece hKσ hcirc hz hi (hrK i hi) (hrseg i hi)
      have hc : IsCompact (convexHull ℝ
          {sixthRoot (i.val : ZMod 6), sixthRoot ((i.val : ZMod 6) + 1), r i}) :=
        (toFinite _).isCompact_convexHull ℝ
      simp only [hT, hi, ↓reduceIte, indicator_of_mem hi]
      refine ⟨h1, h2, ?_, ?_, hc.isClosed.measurableSet⟩
      · rw [← h3, measureReal_def, ENNReal.ofReal_toReal hc.measure_lt_top.ne]
      · rw [← h3]; exact measureReal_nonneg
    · simp only [hT, hi, ↓reduceIte, indicator_of_notMem hi]
      exact ⟨empty_subset _, empty_subset _, by simp, le_rfl, MeasurableSet.empty⟩
  -- the pieces: the hexagon `conv{s_j*}`, the triangles and their reflections
  set S : Option (Fin 3 × Bool) → Set (Fin 2 → ℝ) :=
    fun o ↦ o.elim (hexagonOf sixthRoot) fun p ↦ cond p.2 (-T p.1) (T p.1) with hS
  set idx : Fin 3 × Bool → ZMod 6 := fun p ↦ (p.1.val : ZMod 6) + cond p.2 3 0 with hidx_def
  have hidx : Function.Injective idx := by decide
  have hSs : ∀ p, S (some p) ⊆ sixthTriangle (idx p) := by
    rintro ⟨i, b⟩ v hv
    cases b
    · simpa [hS, hidx_def] using (hTK i).2.1 hv
    · exact ab_neg_mem_sixthTriangle ((hTK i).2.1 hv)
  have hSK : ∀ o, S o ⊆ K := by
    rintro (_ | ⟨i, _ | _⟩) v hv
    · refine convexHull_min ?_ hK.1 hv
      rintro _ ⟨k, rfl⟩
      exact rein_frontier_subset hK (ab_sixthRoot_mem_frontier hKσ hcirc k)
    · exact (hTK i).1 hv
    · simpa using hK.2.2.2 _ ((hTK i).1 hv)
  have hSm : ∀ o, NullMeasurableSet (S o) volume := by
    rintro (_ | ⟨i, _ | _⟩)
    · exact ((finite_range sixthRoot).isCompact_convexHull ℝ).isClosed.measurableSet
        |>.nullMeasurableSet
    · exact (hTK i).2.2.2.2.nullMeasurableSet
    · exact (hTK i).2.2.2.2.neg.nullMeasurableSet
  have hdisj : Pairwise (Function.onFun (AEDisjoint volume) S) := by
    intro o o' hne
    change volume (S o ∩ S o') = 0
    rcases o with _ | p <;> rcases o' with _ | p'
    · exact absurd rfl hne
    · rw [inter_comm]
      exact ab_inter_sixthTriangle_null (hSs p') fun v hv hvi ↦ ab_hexS_disj hv hvi
    · exact ab_inter_sixthTriangle_null (hSs p) fun v hv hvi ↦ ab_hexS_disj hv hvi
    · have hpp : idx p ≠ idx p' := hidx.ne fun h ↦ hne (by rw [h])
      exact ab_inter_sixthTriangle_null (hSs p) fun v hv hvi ↦
        ab_sixthTriangle_disj hpp hvi (hSs p' hv)
  have hsum := (tsum_meas_le_meas_iUnion_of_disjoint₀ volume hSm hdisj).trans
    (measure_mono (iUnion_subset hSK))
  rw [tsum_fintype, Fintype.sum_option, Fintype.sum_prod_type] at hsum
  simp only [Fintype.sum_bool, hS, Option.elim, cond, Measure.measure_neg, ab_volume_hexS] at hsum
  simp only [(hTK _).2.2.1] at hsum
  -- `area(K) ≥ 3√3/2 + 2 Σ_i I_i area_i`
  rw [measureReal_def, ← ENNReal.ofReal_le_iff_le_toReal hK.2.1.measure_lt_top.ne]
  refine le_trans (le_of_eq ?_) hsum
  have hI : ∀ i, 0 ≤ (hRegion i).indicator (areaFn i) (x, y) := fun i ↦ (hTK i).2.2.2.1
  rw [ENNReal.ofReal_add (by positivity)
      (mul_nonneg zero_le_two (Finset.sum_nonneg fun i _ ↦ hI i)),
    Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun i _ ↦ mul_nonneg zero_le_two (hI i)]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [two_mul, ENNReal.ofReal_add (hI i) (hI i)]

end SmoothedPolygons
