module

public import SmoothedPolygons.Ch2.Density
public import SmoothedPolygons.Ch2.Irreducible
public import Basic.Analysis.Convex.LatticePacking
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.LinearAlgebra.AffineSpace.Midpoint
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Topology.MetricSpace.Closeds

/-!
# Reinhardt's approach (§2.2)

Lattice packings of a centrally symmetric convex disk inside hexagons (Lemma 2.2.1), the formula
`δ(K) = area(K)/area(H_K)` with `H_K` a least-area centrally symmetric circumscribed hexagon
(Theorem 2.2.2), support lines (Definition 2.2.3), the hyperbolic arcs at the edge midpoints of
`H_K` (Remark 2.2.4), and Reinhardt's properties of a worst disk `K_min` (Lemmas 2.2.5–2.2.7).

Conventions. As in the book, centrally symmetric means symmetric about the origin. A centrally
symmetric hexagon is given by its vertices `v₀, …, v₅` in counterclockwise order
(`IsCSHexagon`), and is the convex hull `hexagonOf v` of its vertices; its edge `j` joins `v_j` to
`v_{j+1}` and has midpoint `hexMidpoint v j`. In §2.2 a *critical hexagon* of `K` is a centrally
symmetric hexagon of least area circumscribing `K` (`IsLeastAreaHexagon`); Definition 2.3.8 gives
Mahler's definition, and Theorem 2.3.9 shows that the first kind is of the second kind.
-/

@[expose] public section

namespace SmoothedPolygons

open MeasureTheory Set Matrix Real

/-! ### Polygons -/

/-- `P` is a parallelogram: `P = {c + s u + t v | |s| ≤ 1, |t| ≤ 1}` for linearly independent
`u, v`. -/
def IsParallelogram (P : Set (Fin 2 → ℝ)) : Prop :=
  ∃ c u v : Fin 2 → ℝ, det2 u v ≠ 0 ∧
    P = {x | ∃ s t : ℝ, |s| ≤ 1 ∧ |t| ≤ 1 ∧ x = c + s • u + t • v}

/-- `P` is a parallelogram centered at the origin. -/
def IsCSParallelogram (P : Set (Fin 2 → ℝ)) : Prop :=
  ∃ u v : Fin 2 → ℝ, det2 u v ≠ 0 ∧ P = {x | ∃ s t : ℝ, |s| ≤ 1 ∧ |t| ≤ 1 ∧ x = s • u + t • v}

/-- `v₀, …, v₅` are the vertices, in counterclockwise order, of a convex hexagon centered at the
origin: `v_{j+3} = -v_j`, consecutive vertices turn counterclockwise about the origin
(`det(v_j, v_{j+1}) > 0`), and the boundary turns left at every vertex
(`det(v_{j+1} - v_j, v_{j+2} - v_{j+1}) > 0`). -/
def IsCSHexagon (v : ZMod 6 → Fin 2 → ℝ) : Prop :=
  ∀ j, v (j + 3) = -v j ∧ 0 < det2 (v j) (v (j + 1)) ∧
    0 < det2 (v (j + 1) - v j) (v (j + 2) - v (j + 1))

/-- The hexagon with vertices `v₀, …, v₅`: their convex hull. -/
def hexagonOf (v : ZMod 6 → Fin 2 → ℝ) : Set (Fin 2 → ℝ) := convexHull ℝ (range v)

/-- The midpoint of the edge `[v_j, v_{j+1}]` of the hexagon with vertices `v`. -/
noncomputable def hexMidpoint (v : ZMod 6 → Fin 2 → ℝ) (j : ZMod 6) : Fin 2 → ℝ :=
  midpoint ℝ (v j) (v (j + 1))

/-- A critical hexagon of `K` in the sense of §2.2: a centrally symmetric hexagon of least area
circumscribing `K` (Theorem 2.2.2). -/
def IsLeastAreaHexagon (K : Set (Fin 2 → ℝ)) (v : ZMod 6 → Fin 2 → ℝ) : Prop :=
  IsCSHexagon v ∧ K ⊆ hexagonOf v ∧
    ∀ w, IsCSHexagon w → K ⊆ hexagonOf w → volume (hexagonOf v) ≤ volume (hexagonOf w)

/-- The translates `H + l`, `l ∈ L`, tile the plane: they cover it and have pairwise disjoint
interiors. -/
def IsLatticeTiling (H : Set (Fin 2 → ℝ)) (L : Submodule ℤ (Fin 2 → ℝ)) : Prop :=
  (⋃ l ∈ L, (fun x ↦ x + l) '' H) = univ ∧
    ∀ l ∈ L, ∀ l' ∈ L, l ≠ l' →
      Disjoint (interior ((fun x ↦ x + l) '' H)) (interior ((fun x ↦ x + l') '' H))

/-! ## Helper lemmas on centrally symmetric hexagons -/

/-! ### Determinants -/

lemma rein_det2_add_left (a b c : Fin 2 → ℝ) : det2 (a + b) c = det2 a c + det2 b c := by
  simp only [det2, Pi.add_apply]; ring

lemma rein_det2_add_right (a b c : Fin 2 → ℝ) : det2 a (b + c) = det2 a b + det2 a c := by
  simp only [det2, Pi.add_apply]; ring

lemma rein_det2_sub_left (a b c : Fin 2 → ℝ) : det2 (a - b) c = det2 a c - det2 b c := by
  simp only [det2, Pi.sub_apply]; ring

lemma rein_det2_sub_right (a b c : Fin 2 → ℝ) : det2 a (b - c) = det2 a b - det2 a c := by
  simp only [det2, Pi.sub_apply]; ring

lemma rein_det2_neg_left (a b : Fin 2 → ℝ) : det2 (-a) b = -det2 a b := by
  simp only [det2, Pi.neg_apply]; ring

lemma rein_det2_neg_right (a b : Fin 2 → ℝ) : det2 a (-b) = -det2 a b := by
  simp only [det2, Pi.neg_apply]; ring

lemma rein_det2_smul_left (r : ℝ) (a b : Fin 2 → ℝ) : det2 (r • a) b = r * det2 a b := by
  simp only [det2, Pi.smul_apply, smul_eq_mul]; ring

lemma rein_det2_smul_right (r : ℝ) (a b : Fin 2 → ℝ) : det2 a (r • b) = r * det2 a b := by
  simp only [det2, Pi.smul_apply, smul_eq_mul]; ring

lemma rein_det2_self (a : Fin 2 → ℝ) : det2 a a = 0 := by
  simp only [det2]; ring

lemma rein_det2_swap (a b : Fin 2 → ℝ) : det2 b a = -det2 a b := by
  simp only [det2]; ring

lemma rein_isLinearMap_det2 (p : Fin 2 → ℝ) : IsLinearMap ℝ (det2 p) :=
  ⟨rein_det2_add_right p, fun r x ↦ by rw [rein_det2_smul_right, smul_eq_mul]⟩

lemma rein_continuous_det2 : Continuous fun q : (Fin 2 → ℝ) × (Fin 2 → ℝ) ↦ det2 q.1 q.2 := by
  simp only [det2]; fun_prop

/-- Cramer's rule in the plane: `det(p, q) x = det(x, q) p + det(p, x) q`. -/
lemma rein_cramer (p q x : Fin 2 → ℝ) : det2 p q • x = det2 x q • p + det2 p x • q := by
  ext i; fin_cases i <;> simp [det2] <;> ring

/-- Evaluates sums and differences of numerals in `ZMod 6`. -/
macro "rein_z6" : tactic => `(tactic| simp only [
    show (0 : ZMod 6) + 1 = 1 from rfl,
    show (0 : ZMod 6) + 2 = 2 from rfl,
    show (0 : ZMod 6) + 3 = 3 from rfl,
    show (0 : ZMod 6) + 4 = 4 from rfl,
    show (0 : ZMod 6) + 5 = 5 from rfl,
    show (1 : ZMod 6) + 1 = 2 from rfl,
    show (1 : ZMod 6) + 2 = 3 from rfl,
    show (1 : ZMod 6) + 3 = 4 from rfl,
    show (1 : ZMod 6) + 4 = 5 from rfl,
    show (1 : ZMod 6) + 5 = 0 from rfl,
    show (2 : ZMod 6) + 1 = 3 from rfl,
    show (2 : ZMod 6) + 2 = 4 from rfl,
    show (2 : ZMod 6) + 3 = 5 from rfl,
    show (2 : ZMod 6) + 4 = 0 from rfl,
    show (2 : ZMod 6) + 5 = 1 from rfl,
    show (3 : ZMod 6) + 1 = 4 from rfl,
    show (3 : ZMod 6) + 2 = 5 from rfl,
    show (3 : ZMod 6) + 3 = 0 from rfl,
    show (3 : ZMod 6) + 4 = 1 from rfl,
    show (3 : ZMod 6) + 5 = 2 from rfl,
    show (4 : ZMod 6) + 1 = 5 from rfl,
    show (4 : ZMod 6) + 2 = 0 from rfl,
    show (4 : ZMod 6) + 3 = 1 from rfl,
    show (4 : ZMod 6) + 4 = 2 from rfl,
    show (4 : ZMod 6) + 5 = 3 from rfl,
    show (5 : ZMod 6) + 1 = 0 from rfl,
    show (5 : ZMod 6) + 2 = 1 from rfl,
    show (5 : ZMod 6) + 3 = 2 from rfl,
    show (5 : ZMod 6) + 4 = 3 from rfl,
    show (5 : ZMod 6) + 5 = 4 from rfl,
    show (0 : ZMod 6) - 1 = 5 from rfl,
    show (0 : ZMod 6) - 2 = 4 from rfl,
    show (1 : ZMod 6) - 1 = 0 from rfl,
    show (1 : ZMod 6) - 2 = 5 from rfl,
    show (2 : ZMod 6) - 1 = 1 from rfl,
    show (2 : ZMod 6) - 2 = 0 from rfl,
    show (3 : ZMod 6) - 1 = 2 from rfl,
    show (3 : ZMod 6) - 2 = 1 from rfl,
    show (4 : ZMod 6) - 1 = 3 from rfl,
    show (4 : ZMod 6) - 2 = 2 from rfl,
    show (5 : ZMod 6) - 1 = 4 from rfl,
    show (5 : ZMod 6) - 2 = 3 from rfl] at *)

/-! ### Centrally symmetric hexagons given by three vertices -/

lemma rein_zmod6_cases (k : ZMod 6) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by
  revert k; decide

/-- The centrally symmetric hexagon with vertices `a, b, c, -a, -b, -c`. -/
def rein_hex3 (a b c : Fin 2 → ℝ) : ZMod 6 → Fin 2 → ℝ :=
  fun k ↦ (![a, b, c, -a, -b, -c] : Fin 6 → Fin 2 → ℝ) k

section hex3
variable (a b c : Fin 2 → ℝ)
@[simp] lemma rein_hex3_zero : rein_hex3 a b c 0 = a := rfl
@[simp] lemma rein_hex3_one : rein_hex3 a b c 1 = b := rfl
@[simp] lemma rein_hex3_two : rein_hex3 a b c 2 = c := rfl
@[simp] lemma rein_hex3_three : rein_hex3 a b c 3 = -a := rfl
@[simp] lemma rein_hex3_four : rein_hex3 a b c 4 = -b := rfl
@[simp] lemma rein_hex3_five : rein_hex3 a b c 5 = -c := rfl
end hex3

lemma rein_eq_hex3 {v : ZMod 6 → Fin 2 → ℝ} (hv : IsCSHexagon v) :
    v = rein_hex3 (v 0) (v 1) (v 2) := by
  funext k
  fin_cases k
  · rfl
  · rfl
  · rfl
  · exact (hv 0).1
  · exact (hv 1).1
  · exact (hv 2).1

/-- The conditions for `a, b, c, -a, -b, -c` to be a centrally symmetric hexagon: with
`D₁ = det(a, b)`, `D₂ = det(b, c)`, `D₃ = det(a, c)`, these are `Dᵢ > 0` and the triangle
inequalities. -/
lemma rein_isCSHexagon_hex3_iff (a b c : Fin 2 → ℝ) :
    IsCSHexagon (rein_hex3 a b c) ↔
      0 < det2 a b ∧ 0 < det2 b c ∧ 0 < det2 a c ∧ det2 a c < det2 a b + det2 b c ∧
        det2 a b < det2 b c + det2 a c ∧ det2 b c < det2 a b + det2 a c := by
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    rein_z6
    simp only [rein_hex3_zero, rein_hex3_one, rein_hex3_two, rein_hex3_three,
      rein_hex3_four] at h0 h1 h2
    simp only [det2, Pi.sub_apply, Pi.neg_apply] at h0 h1 h2 ⊢
    refine ⟨h0.2.1, h1.2.1, ?_, ?_, ?_, ?_⟩ <;> nlinarith [h0.2.2, h1.2.2, h2.2.2, h2.2.1]
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    intro k
    simp only [det2] at *
    rcases rein_zmod6_cases k with rfl | rfl | rfl | rfl | rfl | rfl <;> rein_z6 <;>
    simp only [rein_hex3_zero, rein_hex3_one, rein_hex3_two, rein_hex3_three,
      rein_hex3_four, rein_hex3_five, neg_neg, Pi.sub_apply, Pi.neg_apply, true_and] <;>
    refine ⟨?_, ?_⟩ <;> nlinarith


/-! ### Half-planes, triangles and the area of a centrally symmetric hexagon -/

/-- The triangle with vertices `0, p, q` (for `det(p, q) > 0`): the points `α p + β q` with
`α, β ≥ 0` and `α + β ≤ 1`, the coefficients being given by Cramer's rule. -/
def rein_tri (p q : Fin 2 → ℝ) : Set (Fin 2 → ℝ) :=
  {x | 0 ≤ det2 x q ∧ 0 ≤ det2 p x ∧ det2 x q + det2 p x ≤ det2 p q}

/-- A convex set containing `p`, `q` and `-p` contains the triangle `0 p q`. -/
lemma rein_mem_of_mem_tri {s : Set (Fin 2 → ℝ)} (hs : Convex ℝ s) {p q x : Fin 2 → ℝ}
    (hp : p ∈ s) (hq : q ∈ s) (hnp : -p ∈ s) (hpq : 0 < det2 p q) (hx : x ∈ rein_tri p q) :
    x ∈ s := by
  obtain ⟨h1, h2, h3⟩ := hx
  have hcr := rein_cramer p q x
  set D := det2 p q with hD
  set α := det2 x q / D with hα_def
  set β := det2 p x / D with hβ_def
  set γ := (1 - α - β) / 2 with hγ_def
  have hα : 0 ≤ α := div_nonneg h1 hpq.le
  have hβ : 0 ≤ β := div_nonneg h2 hpq.le
  have hγ : 0 ≤ γ := by
    have : α + β ≤ 1 := by rw [← add_div, div_le_one hpq]; exact h3
    linarith
  have key : x = (α + γ) • p + β • q + γ • (-p) := by
    have hx : x = D⁻¹ • (det2 x q • p + det2 p x • q) := by
      rw [← hcr, smul_smul, inv_mul_cancel₀ hpq.ne', one_smul]
    conv_lhs => rw [hx]
    ext i
    simp only [Pi.smul_apply, Pi.add_apply, Pi.neg_apply, smul_eq_mul, hα_def, hβ_def, hγ_def]
    field_simp
    ring
  rw [key]
  have := hs.sum_mem (t := Finset.univ) (w := ![α + γ, β, γ]) (z := ![p, q, -p])
    (by intro i _; fin_cases i <;> simp <;> linarith)
    (by simp only [Fin.sum_univ_three, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]; ring)
    (by intro i _; fin_cases i <;> simp [hp, hq, hnp])
  simpa [Fin.sum_univ_three, add_assoc] using this

/-- The six half-plane conditions of the hexagon `a, b, c, -a, -b, -c`: `x` lies to the left of
each directed edge. -/
def rein_InHex (a b c x : Fin 2 → ℝ) : Prop :=
  0 ≤ det2 (b - a) (x - a) ∧ 0 ≤ det2 (c - b) (x - b) ∧ 0 ≤ det2 (-a - c) (x - c) ∧
    0 ≤ det2 (b - a) (-x - a) ∧ 0 ≤ det2 (c - b) (-x - b) ∧ 0 ≤ det2 (-a - c) (-x - c)

lemma rein_convex_inHex (a b c : Fin 2 → ℝ) : Convex ℝ {x | rein_InHex a b c x} := by
  have h1 : ∀ d p : Fin 2 → ℝ, Convex ℝ {x | 0 ≤ det2 d (x - p)} := by
    intro d p
    have := convex_halfSpace_ge (rein_isLinearMap_det2 d) (det2 d p)
    convert this using 1
    ext x
    simp only [mem_ofPred_eq]
    rw [rein_det2_sub_right, sub_nonneg]
  have h2 : ∀ d p : Fin 2 → ℝ, Convex ℝ {x | 0 ≤ det2 d (-x - p)} := by
    intro d p
    have := convex_halfSpace_le (rein_isLinearMap_det2 d) (-det2 d p)
    convert this using 1
    ext x
    simp only [mem_ofPred_eq]
    rw [rein_det2_sub_right, rein_det2_neg_right]
    constructor <;> intro h <;> linarith
  simp only [rein_InHex, ofPred_and]
  exact (h1 _ _).inter ((h1 _ _).inter ((h1 _ _).inter ((h2 _ _).inter ((h2 _ _).inter
    (h2 _ _)))))

/-- The hexagon with vertices `a, b, c, -a, -b, -c` is the intersection of the six half-planes
bounded by the lines of its edges. -/
lemma rein_mem_hexagonOf_hex3 {a b c : Fin 2 → ℝ} (h : IsCSHexagon (rein_hex3 a b c))
    (x : Fin 2 → ℝ) : x ∈ hexagonOf (rein_hex3 a b c) ↔ rein_InHex a b c x := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := (rein_isCSHexagon_hex3_iff a b c).1 h
  constructor
  · intro hx
    refine (convexHull_min ?_ (rein_convex_inHex a b c)) hx
    rintro _ ⟨k, rfl⟩
    simp only [rein_InHex, det2, mem_ofPred_eq] at h1 h2 h3 h4 h5 h6 ⊢
    rcases rein_zmod6_cases k with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [rein_hex3_zero, rein_hex3_one, rein_hex3_two, rein_hex3_three,
      rein_hex3_four, rein_hex3_five, neg_neg, Pi.sub_apply, Pi.neg_apply] <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith
  · intro hx
    have hconv : Convex ℝ (hexagonOf (rein_hex3 a b c)) := convex_convexHull ℝ _
    have hv : ∀ k, rein_hex3 a b c k ∈ hexagonOf (rein_hex3 a b c) :=
      fun k ↦ subset_convexHull ℝ _ ⟨k, rfl⟩
    have ha := hv 0
    have hb := hv 1
    have hc := hv 2
    have hna := hv 3
    have hnb := hv 4
    have hnc := hv 5
    simp only [rein_hex3_zero, rein_hex3_one, rein_hex3_two, rein_hex3_three,
      rein_hex3_four, rein_hex3_five] at ha hb hc hna hnb hnc
    obtain ⟨e0, e1, e2, e3, e4, e5⟩ := hx
    simp only [det2, Pi.sub_apply, Pi.neg_apply] at e0 e1 e2 e3 e4 e5 h1 h2 h3 h4 h5 h6
    rcases le_or_gt 0 (det2 a x) with hax | hax
    · rcases le_or_gt (det2 b x) 0 with hbx | hbx
      · refine rein_mem_of_mem_tri hconv ha hb hna (by simpa [det2] using h1) ?_
        simp only [rein_tri, det2, mem_ofPred_eq] at hax hbx ⊢
        refine ⟨?_, ?_, ?_⟩ <;> nlinarith
      rcases le_or_gt (det2 c x) 0 with hcx | hcx
      · refine rein_mem_of_mem_tri hconv hb hc hnb (by simpa [det2] using h2) ?_
        simp only [rein_tri, det2, mem_ofPred_eq] at hax hbx hcx ⊢
        refine ⟨?_, ?_, ?_⟩ <;> nlinarith
      · refine rein_mem_of_mem_tri hconv hc hna hnc (by simp [det2]; nlinarith) ?_
        simp only [rein_tri, det2, mem_ofPred_eq, Pi.neg_apply] at hax hbx hcx ⊢
        refine ⟨?_, ?_, ?_⟩ <;> nlinarith
    · rcases le_or_gt 0 (det2 b x) with hbx | hbx
      · refine rein_mem_of_mem_tri hconv hna hnb (by simpa using ha) (by simp [det2]; nlinarith) ?_
        simp only [rein_tri, det2, mem_ofPred_eq, Pi.neg_apply] at hax hbx ⊢
        refine ⟨?_, ?_, ?_⟩ <;> nlinarith
      rcases le_or_gt 0 (det2 c x) with hcx | hcx
      · refine rein_mem_of_mem_tri hconv hnb hnc (by simpa using hb) (by simp [det2]; nlinarith) ?_
        simp only [rein_tri, det2, mem_ofPred_eq, Pi.neg_apply] at hax hbx hcx ⊢
        refine ⟨?_, ?_, ?_⟩ <;> nlinarith
      · refine rein_mem_of_mem_tri hconv hnc ha (by simpa using hc) (by simp [det2]; nlinarith) ?_
        simp only [rein_tri, det2, mem_ofPred_eq, Pi.neg_apply] at hax hbx hcx ⊢
        refine ⟨?_, ?_, ?_⟩ <;> nlinarith

/-! ### Areas -/

/-- The linear functional `x ↦ det(p, x)`. -/
noncomputable def rein_det2L (p : Fin 2 → ℝ) : (Fin 2 → ℝ) →ₗ[ℝ] ℝ :=
  IsLinearMap.mk' (det2 p) (rein_isLinearMap_det2 p)

/-- A line `{x | det(p, x) = c}`, `p ≠ 0`, has area zero. -/
lemma rein_volume_line {p : Fin 2 → ℝ} (hp : p ≠ 0) (c : ℝ) :
    volume {x : Fin 2 → ℝ | det2 p x = c} = 0 := by
  have hn : 0 < p 0 ^ 2 + p 1 ^ 2 := by
    by_contra h
    apply hp
    ext i
    fin_cases i <;> simp <;> nlinarith [sq_nonneg (p 0), sq_nonneg (p 1)]
  set w : Fin 2 → ℝ := ![-p 1, p 0]
  have hw : det2 p w = p 0 ^ 2 + p 1 ^ 2 := by simp [det2, w]; ring
  set x0 : Fin 2 → ℝ := (c / (p 0 ^ 2 + p 1 ^ 2)) • w
  have hx0 : det2 p x0 = c := by
    simp only [x0, rein_det2_smul_right, hw]; field_simp
  have hker : (LinearMap.ker (rein_det2L p)) ≠ ⊤ := by
    intro h
    have : w ∈ LinearMap.ker (rein_det2L p) := h ▸ Submodule.mem_top
    rw [LinearMap.mem_ker] at this
    change det2 p w = 0 at this
    rw [hw] at this
    exact hn.ne' this
  have h0 := Measure.addHaar_submodule volume _ hker
  have heq : {x : Fin 2 → ℝ | det2 p x = c} =
      (fun h ↦ -x0 + h) ⁻¹' (LinearMap.ker (rein_det2L p) : Set (Fin 2 → ℝ)) := by
    ext x
    simp only [mem_ofPred_eq, mem_preimage, SetLike.mem_coe, LinearMap.mem_ker]
    change _ ↔ det2 p (-x0 + x) = 0
    rw [neg_add_eq_sub]
    simp only [det2, Pi.sub_apply] at hx0 ⊢
    constructor <;> intro h <;> linarith
  rw [heq, measure_preimage_add]
  exact h0

/-- The standard triangle `{y | y₀ ≥ 0, y₁ ≥ 0, y₀ + y₁ ≤ 1}` has area `1/2`. -/
lemma rein_volume_stdTri :
    volume {y : Fin 2 → ℝ | 0 ≤ y 0 ∧ 0 ≤ y 1 ∧ y 0 + y 1 ≤ 1} = ENNReal.ofReal (1 / 2) := by
  set Δ := {y : Fin 2 → ℝ | 0 ≤ y 0 ∧ 0 ≤ y 1 ∧ y 0 + y 1 ≤ 1}
  set Δ' := {y : Fin 2 → ℝ | y 0 ≤ 1 ∧ y 1 ≤ 1 ∧ 1 ≤ y 0 + y 1}
  have hΔ' : Δ' = -((fun h ↦ (1 : Fin 2 → ℝ) + h) ⁻¹' Δ) := by
    ext y
    simp only [Δ, Δ', mem_ofPred_eq, mem_neg, mem_preimage, Pi.add_apply, Pi.neg_apply,
      Pi.one_apply]
    constructor
    · rintro ⟨h1, h2, h3⟩; refine ⟨?_, ?_, ?_⟩ <;> linarith
    · rintro ⟨h1, h2, h3⟩; refine ⟨?_, ?_, ?_⟩ <;> linarith
  have hvol' : volume Δ' = volume Δ := by
    rw [hΔ', Measure.measure_neg, measure_preimage_add]
  have hunion : Δ ∪ Δ' = Icc 0 1 := by
    ext y
    simp only [Δ, Δ', mem_union, mem_ofPred_eq, mem_Icc, Pi.le_def, Fin.forall_fin_two,
      Pi.zero_apply, Pi.one_apply]
    constructor
    · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩) <;> refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      rcases le_total (y 0 + y 1) 1 with h | h
      · exact Or.inl ⟨h1, h2, h⟩
      · exact Or.inr ⟨h3, h4, h⟩
  have hinter : volume (Δ ∩ Δ') = 0 := by
    refine measure_mono_null ?_ (rein_volume_line (p := ![1, -1]) (by
      intro h; have := congrFun h 0; simp at this) 1)
    rintro y ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩
    simp only [mem_ofPred_eq, det2]
    simp
    linarith
  have hmeas : NullMeasurableSet Δ' volume := by
    refine (IsClosed.measurableSet ?_).nullMeasurableSet
    simp only [Δ', ofPred_and]
    refine (isClosed_le (continuous_apply 0) continuous_const).inter
      ((isClosed_le (continuous_apply 1) continuous_const).inter
      (isClosed_le continuous_const ((continuous_apply 0).add (continuous_apply 1))))
  have key := measure_union_add_inter₀ (μ := volume) Δ hmeas
  rw [hunion, hinter, hvol', add_zero, Real.volume_Icc_pi] at key
  simp only [Pi.one_apply, Pi.zero_apply, sub_zero, ENNReal.ofReal_one,
    Finset.prod_const_one] at key
  have hne : volume Δ ≠ ⊤ := by
    intro h; rw [h] at key; simp at key
  rw [← ENNReal.ofReal_toReal hne]
  congr 1
  have := congrArg ENNReal.toReal key
  rw [ENNReal.toReal_add hne hne] at this
  simp at this
  linarith

/-- The triangle `0 p q` has area `det(p, q)/2`. -/
lemma rein_volume_tri {p q : Fin 2 → ℝ} (hpq : 0 < det2 p q) :
    volume (rein_tri p q) = ENNReal.ofReal (det2 p q / 2) := by
  set M : Matrix (Fin 2) (Fin 2) ℝ := !![p 0, q 0; p 1, q 1]
  have hM : ∀ y : Fin 2 → ℝ, Matrix.toLin' M y = y 0 • p + y 1 • q := by
    intro y
    ext i
    fin_cases i <;> simp [M, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring
  have himage : rein_tri p q =
      Matrix.toLin' M '' {y : Fin 2 → ℝ | 0 ≤ y 0 ∧ 0 ≤ y 1 ∧ y 0 + y 1 ≤ 1} := by
    ext x
    simp only [rein_tri, mem_ofPred_eq, mem_image, hM]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨![det2 x q / det2 p q, det2 p x / det2 p q], ?_, ?_⟩
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        refine ⟨div_nonneg h1 hpq.le, div_nonneg h2 hpq.le, ?_⟩
        rw [← add_div, div_le_one hpq]; exact h3
      · have hcr := rein_cramer p q x
        ext i
        have hi := congrFun hcr i
        simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Matrix.cons_val_zero,
          Matrix.cons_val_one] at hi ⊢
        field_simp
        linarith
    · rintro ⟨y, ⟨h1, h2, h3⟩, rfl⟩
      have e1 : det2 (y 0 • p + y 1 • q) q = y 0 * det2 p q := by simp [det2]; ring
      have e2 : det2 p (y 0 • p + y 1 • q) = y 1 * det2 p q := by simp [det2]; ring
      rw [e1, e2]
      refine ⟨mul_nonneg h1 hpq.le, mul_nonneg h2 hpq.le, ?_⟩
      nlinarith
  rw [himage, Measure.addHaar_image_linearMap, LinearMap.det_toLin', rein_volume_stdTri]
  simp only [M, Matrix.det_fin_two_of]
  rw [← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  have : p 0 * q 1 - q 0 * p 1 = det2 p q := by simp [det2]; ring
  rw [this, abs_of_pos hpq]
  ring



/-- The Plücker relation `det(a, b) det(c, x) = det(c, b) det(a, x) + det(a, c) det(b, x)`. -/
lemma rein_plucker (a b c x : Fin 2 → ℝ) :
    det2 a b * det2 c x = det2 c b * det2 a x + det2 a c * det2 b x := by
  simp only [det2]; ring

/-- If `det(p, q), det(q, r), det(p, r) > 0`, no `x` has `det(p, x) > 0`, `det(q, x) < 0` and
`det(r, x) > 0`. -/
lemma rein_plucker_contra {p q r x : Fin 2 → ℝ} (hpq : 0 < det2 p q) (hqr : 0 < det2 q r)
    (hpr : 0 < det2 p r) (h1 : 0 < det2 p x) (h2 : det2 q x < 0) (h3 : 0 < det2 r x) : False := by
  have e := rein_plucker p q r x
  rw [rein_det2_swap q r] at e
  nlinarith [mul_pos hpq h3, mul_pos hqr h1, mul_pos hpr (neg_pos.2 h2)]


lemma rein_continuous_det2_left (p : Fin 2 → ℝ) : Continuous (det2 p) := by
  unfold det2; fun_prop

lemma rein_continuous_det2_right (p : Fin 2 → ℝ) : Continuous fun x ↦ det2 x p := by
  unfold det2; fun_prop

lemma rein_isClosed_tri (p q : Fin 2 → ℝ) : IsClosed (rein_tri p q) := by
  have : rein_tri p q = {x | 0 ≤ det2 x q} ∩ ({x | 0 ≤ det2 p x} ∩
      {x | det2 x q + det2 p x ≤ det2 p q}) := by
    ext x; simp [rein_tri]
  rw [this]
  exact (isClosed_le continuous_const (rein_continuous_det2_right q)).inter
    ((isClosed_le continuous_const (rein_continuous_det2_left p)).inter
    (isClosed_le ((rein_continuous_det2_right q).add (rein_continuous_det2_left p))
      continuous_const))

/-- The hexagon `a, b, c, -a, -b, -c` is the union of the six triangles `0 v_j v_{j+1}`. -/
lemma rein_hexagonOf_hex3_eq_iUnion {a b c : Fin 2 → ℝ} (h : IsCSHexagon (rein_hex3 a b c)) :
    hexagonOf (rein_hex3 a b c) =
      ⋃ i : ZMod 6, rein_tri (rein_hex3 a b c i) (rein_hex3 a b c (i + 1)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := (rein_isCSHexagon_hex3_iff a b c).1 h
  apply Subset.antisymm
  · intro x hx
    rw [rein_mem_hexagonOf_hex3 h] at hx
    obtain ⟨e0, e1, e2, e3, e4, e5⟩ := hx
    simp only [mem_iUnion]
    simp only [det2, Pi.sub_apply, Pi.neg_apply] at e0 e1 e2 e3 e4 e5 h1 h2 h3 h4 h5 h6
    rcases le_or_gt 0 (det2 a x) with hax | hax
    · rcases le_or_gt (det2 b x) 0 with hbx | hbx
      · refine ⟨0, ?_⟩
        rein_z6
        simp only [rein_tri, det2, mem_ofPred_eq, rein_hex3_zero, rein_hex3_one] at hax hbx ⊢
        refine ⟨?_, ?_, ?_⟩ <;> nlinarith
      rcases le_or_gt (det2 c x) 0 with hcx | hcx
      · refine ⟨1, ?_⟩
        rein_z6
        simp only [rein_tri, det2, mem_ofPred_eq, rein_hex3_one, rein_hex3_two] at hax hbx hcx ⊢
        refine ⟨?_, ?_, ?_⟩ <;> nlinarith
      · refine ⟨2, ?_⟩
        rein_z6
        simp only [rein_tri, det2, mem_ofPred_eq, rein_hex3_two, rein_hex3_three,
          Pi.neg_apply] at hax hbx hcx ⊢
        refine ⟨?_, ?_, ?_⟩ <;> nlinarith
    · rcases le_or_gt 0 (det2 b x) with hbx | hbx
      · refine ⟨3, ?_⟩
        rein_z6
        simp only [rein_tri, det2, mem_ofPred_eq, rein_hex3_three, rein_hex3_four,
          Pi.neg_apply] at hax hbx ⊢
        refine ⟨?_, ?_, ?_⟩ <;> nlinarith
      rcases le_or_gt 0 (det2 c x) with hcx | hcx
      · refine ⟨4, ?_⟩
        rein_z6
        simp only [rein_tri, det2, mem_ofPred_eq, rein_hex3_four, rein_hex3_five,
          Pi.neg_apply] at hax hbx hcx ⊢
        refine ⟨?_, ?_, ?_⟩ <;> nlinarith
      · refine ⟨5, ?_⟩
        rein_z6
        simp only [rein_tri, det2, mem_ofPred_eq, rein_hex3_five, rein_hex3_zero,
          Pi.neg_apply] at hax hbx hcx ⊢
        refine ⟨?_, ?_, ?_⟩ <;> nlinarith
  · refine iUnion_subset fun i ↦ ?_
    intro x hx
    have hv : ∀ k, rein_hex3 a b c k ∈ hexagonOf (rein_hex3 a b c) :=
      fun k ↦ subset_convexHull ℝ _ ⟨k, rfl⟩
    refine rein_mem_of_mem_tri (convex_convexHull ℝ _) (hv i) (hv (i + 1)) ?_ ((h i).2.1) hx
    rw [← (h i).1]
    exact hv _

/-- Facts on consecutive vertices of the hexagon `a, b, c, -a, -b, -c`. -/
lemma rein_hex3_facts {a b c : Fin 2 → ℝ} (h : IsCSHexagon (rein_hex3 a b c)) (i : ZMod 6) :
    0 < det2 (rein_hex3 a b c i) (rein_hex3 a b c (i + 2)) := by
  obtain ⟨h1, h2, h3, -, -, -⟩ := (rein_isCSHexagon_hex3_iff a b c).1 h
  rcases rein_zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;> rein_z6 <;>
  simp only [rein_hex3_zero, rein_hex3_one, rein_hex3_two, rein_hex3_three, rein_hex3_four,
    rein_hex3_five, rein_det2_neg_left, rein_det2_neg_right, neg_neg] <;>
  first
    | assumption
    | (rw [rein_det2_swap]; linarith)

/-- Facts on consecutive vertices of a centrally symmetric hexagon. -/
lemma rein_hex_facts {v : ZMod 6 → Fin 2 → ℝ} (hv : IsCSHexagon v) (i : ZMod 6) :
    0 < det2 (v i) (v (i + 1)) ∧ 0 < det2 (v i) (v (i + 2)) ∧ v (i + 3) = -v i := by
  refine ⟨(hv i).2.1, ?_, (hv i).1⟩
  have h := hv
  rw [rein_eq_hex3 hv] at h ⊢
  exact rein_hex3_facts h i

/-- The area of the hexagon `a, b, c, -a, -b, -c` is `det(a, b) + det(b, c) + det(a, c)`. -/
lemma rein_volume_hexagonOf_hex3 {a b c : Fin 2 → ℝ} (h : IsCSHexagon (rein_hex3 a b c)) :
    volume (hexagonOf (rein_hex3 a b c)) = ENNReal.ofReal (det2 a b + det2 b c + det2 a c) := by
  obtain ⟨h1, h2, h3, -, -, -⟩ := (rein_isCSHexagon_hex3_iff a b c).1 h
  set w := rein_hex3 a b c with hw
  have hw0 : ∀ i, w i ≠ 0 := by
    intro i hi
    have : 0 < det2 (w i) (w (i + 1)) := (rein_hex_facts h i).1
    rw [hi] at this
    simp [det2] at this
  -- the null set of the three lines through the vertices
  set N := ⋃ i : ZMod 6, {x : Fin 2 → ℝ | det2 (w i) x = 0}
  have hN : volume N = 0 := measure_iUnion_null fun i ↦ rein_volume_line (hw0 i) 0
  have hsign : ∀ i x, x ∈ rein_tri (w i) (w (i + 1)) → x ∉ N →
      0 < det2 (w i) x ∧ det2 (w (i + 1)) x < 0 := by
    intro i x hx hxN
    simp only [N, mem_iUnion, mem_ofPred_eq, not_exists] at hxN
    obtain ⟨hx1, hx2, -⟩ := hx
    rw [rein_det2_swap] at hx1
    exact ⟨lt_of_le_of_ne hx2 (Ne.symm (hxN i)), lt_of_le_of_ne (by linarith) (hxN (i + 1))⟩
  have hdisj : Pairwise (Function.onFun (AEDisjoint volume)
      fun i : ZMod 6 ↦ rein_tri (w i) (w (i + 1))) := by
    -- two triangles `i` and `i + d`, `d = 1, 2, 3`, meet in `N`
    have key : ∀ i x, x ∈ rein_tri (w i) (w (i + 1)) → x ∉ N → ∀ d : ZMod 6,
        d = 1 ∨ d = 2 ∨ d = 3 → x ∉ rein_tri (w (i + d)) (w (i + d + 1)) := by
      intro i x hi hxN d hd hj
      obtain ⟨hi1, hi2⟩ := hsign i x hi hxN
      obtain ⟨hj1, hj2⟩ := hsign (i + d) x hj hxN
      rcases hd with rfl | rfl | rfl
      · linarith
      · obtain ⟨f1, f2, -⟩ := rein_hex_facts h i
        obtain ⟨f3, -, -⟩ := rein_hex_facts h (i + 1)
        rw [show i + 1 + 1 = i + 2 by ring] at f3
        exact rein_plucker_contra f1 f3 f2 hi1 hi2 hj1
      · rw [(rein_hex_facts h i).2.2, rein_det2_neg_left] at hj1
        linarith
    intro i j hij
    change volume (rein_tri (w i) (w (i + 1)) ∩ rein_tri (w j) (w (j + 1))) = 0
    refine measure_mono_null ?_ hN
    rintro x ⟨hi, hj⟩
    by_contra hxN
    obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by ring⟩
    have hd : d ≠ 0 := by rintro rfl; exact hij (by ring)
    rcases rein_zmod6_cases d with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hd rfl
    · exact key i x hi hxN 1 (Or.inl rfl) hj
    · exact key i x hi hxN 2 (Or.inr (Or.inl rfl)) hj
    · exact key i x hi hxN 3 (Or.inr (Or.inr rfl)) hj
    · refine key (i + 4) x hj hxN 2 (Or.inr (Or.inl rfl)) ?_
      rw [add_assoc i 4 2, show (4 : ZMod 6) + 2 = 0 from rfl, add_zero]; exact hi
    · refine key (i + 5) x hj hxN 1 (Or.inl rfl) ?_
      rw [add_assoc i 5 1, show (5 : ZMod 6) + 1 = 0 from rfl, add_zero]; exact hi
  have hmeas : ∀ i : ZMod 6, NullMeasurableSet (rein_tri (w i) (w (i + 1))) volume :=
    fun i ↦ (rein_isClosed_tri _ _).measurableSet.nullMeasurableSet
  rw [rein_hexagonOf_hex3_eq_iUnion h, measure_iUnion₀ hdisj hmeas, tsum_fintype]
  have hsum : ∑ i : ZMod 6, volume (rein_tri (w i) (w (i + 1))) =
      volume (rein_tri (w 0) (w (0 + 1))) + volume (rein_tri (w 1) (w (1 + 1))) +
      volume (rein_tri (w 2) (w (2 + 1))) + volume (rein_tri (w 3) (w (3 + 1))) +
      volume (rein_tri (w 4) (w (4 + 1))) + volume (rein_tri (w 5) (w (5 + 1))) :=
    Fin.sum_univ_six _
  rw [hsum]
  have hv : ∀ i, volume (rein_tri (w i) (w (i + 1))) =
      ENNReal.ofReal (det2 (w i) (w (i + 1)) / 2) := fun i ↦
    rein_volume_tri (rein_hex_facts h i).1
  simp only [hv]
  rein_z6
  simp only [hw, rein_hex3_zero, rein_hex3_one, rein_hex3_two, rein_hex3_three, rein_hex3_four,
    rein_hex3_five, rein_det2_neg_left, rein_det2_neg_right, neg_neg]
  rw [← rein_det2_swap c a]
  have q1 : 0 ≤ det2 a b / 2 := by linarith
  have q2 : 0 ≤ det2 b c / 2 := by linarith
  have q3 : 0 ≤ det2 a c / 2 := by linarith
  rw [← ENNReal.ofReal_add q1 q2, ← ENNReal.ofReal_add (by linarith) q3,
    ← ENNReal.ofReal_add (by linarith) q1, ← ENNReal.ofReal_add (by linarith) q2,
    ← ENNReal.ofReal_add (by linarith) q3]
  congr 1
  ring


/-! ### Edge midpoints of a least-area hexagon

The rotation argument below uses the strip description of the hexagon. It is the only copy:
`SmoothedPolygons.Ch2.Hexagon`, `SmoothedPolygons.Ch2.Mahler` and
`SmoothedPolygons.Ch2.BalancedDensity` (downstream of this file) use these lemmas. -/

/-- The conditions on `a, b, c` that make `rein_hex3 a b c` a convex hexagon. -/
structure rein_HexCond (a b c : Fin 2 → ℝ) : Prop where
  hA : 0 < det2 a b
  hB : 0 < det2 b c
  hC : 0 < det2 a c
  h0 : det2 a c < det2 a b + det2 b c
  h1 : det2 a b < det2 b c + det2 a c
  h2 : det2 b c < det2 a b + det2 a c

lemma rein_isCSHexagon_iff_hexCond {a b c : Fin 2 → ℝ} :
    IsCSHexagon (rein_hex3 a b c) ↔ rein_HexCond a b c := by
  rw [rein_isCSHexagon_hex3_iff]
  exact ⟨fun ⟨h1, h2, h3, h4, h5, h6⟩ ↦ ⟨h1, h2, h3, h4, h5, h6⟩,
    fun ⟨h1, h2, h3, h4, h5, h6⟩ ↦ ⟨h1, h2, h3, h4, h5, h6⟩⟩

/-- The hexagon `rein_hex3 a b c` is the intersection of three strips. -/
def rein_strips (a b c x : Fin 2 → ℝ) : Prop :=
  |det2 (a - b) x| ≤ det2 a b ∧ |det2 (b - c) x| ≤ det2 b c ∧ |det2 (c + a) x| ≤ det2 a c

lemma rein_mem_hexagonOf_iff_strips {a b c x : Fin 2 → ℝ} (h : rein_HexCond a b c) :
    x ∈ hexagonOf (rein_hex3 a b c) ↔ rein_strips a b c x := by
  rw [rein_mem_hexagonOf_hex3 (rein_isCSHexagon_iff_hexCond.2 h)]
  simp only [rein_InHex, rein_strips, abs_le, det2, Pi.sub_apply, Pi.neg_apply, Pi.add_apply]
  constructor
  · rintro ⟨e0, e1, e2, e3, e4, e5⟩
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> nlinarith
  · rintro ⟨⟨e0, e1⟩, ⟨e2, e3⟩, ⟨e4, e5⟩⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith

lemma rein_volume_hexagonOf_hex3' {a b c : Fin 2 → ℝ} (h : rein_HexCond a b c) :
    volume (hexagonOf (rein_hex3 a b c)) = ENNReal.ofReal (det2 a b + det2 b c + det2 a c) :=
  rein_volume_hexagonOf_hex3 (rein_isCSHexagon_iff_hexCond.2 h)

/-- `det(f(τ), g(τ))` is continuous in `τ`. -/
lemma rein_continuous_det2_comp {f g : ℝ → Fin 2 → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun τ ↦ det2 (f τ) (g τ) := by
  unfold det2
  fun_prop

open Filter Topology in
/-- The conditions `rein_HexCond` persist under small perturbations of `a` and `b`. -/
lemma rein_eventually_hexCond {a b c : Fin 2 → ℝ} (h : rein_HexCond a b c)
    {a' b' : ℝ → Fin 2 → ℝ} (ha : Continuous a') (hb : Continuous b') (ha0 : a' 0 = a)
    (hb0 : b' 0 = b) : ∀ᶠ τ in 𝓝 0, rein_HexCond (a' τ) (b' τ) c := by
  have dab := rein_continuous_det2_comp ha hb
  have dbc := rein_continuous_det2_comp hb (continuous_const (y := c))
  have dac := rein_continuous_det2_comp ha (continuous_const (y := c))
  have e1 : ∀ᶠ τ in 𝓝 (0 : ℝ), 0 < det2 (a' τ) (b' τ) :=
    continuousAt_const.eventually_lt dab.continuousAt (by simpa [ha0, hb0] using h.hA)
  have e2 : ∀ᶠ τ in 𝓝 (0 : ℝ), 0 < det2 (b' τ) c :=
    continuousAt_const.eventually_lt dbc.continuousAt (by simpa [hb0] using h.hB)
  have e3 : ∀ᶠ τ in 𝓝 (0 : ℝ), 0 < det2 (a' τ) c :=
    continuousAt_const.eventually_lt dac.continuousAt (by simpa [ha0] using h.hC)
  have e4 : ∀ᶠ τ in 𝓝 (0 : ℝ), det2 (a' τ) c < det2 (a' τ) (b' τ) + det2 (b' τ) c :=
    dac.continuousAt.eventually_lt (dab.add dbc).continuousAt (by simpa [ha0, hb0] using h.h0)
  have e5 : ∀ᶠ τ in 𝓝 (0 : ℝ), det2 (a' τ) (b' τ) < det2 (b' τ) c + det2 (a' τ) c :=
    dab.continuousAt.eventually_lt (dbc.add dac).continuousAt (by simpa [ha0, hb0] using h.h1)
  have e6 : ∀ᶠ τ in 𝓝 (0 : ℝ), det2 (b' τ) c < det2 (a' τ) (b' τ) + det2 (a' τ) c :=
    dbc.continuousAt.eventually_lt (dab.add dac).continuousAt (by simpa [ha0, hb0] using h.h2)
  filter_upwards [e1, e2, e3, e4, e5, e6] with τ h1 h2 h3 h4 h5 h6 using ⟨h1, h2, h3, h4, h5, h6⟩


open Filter Topology in
/-- **The rotation argument** (§2.2, TeX ~1395–1400). If the midpoint of the edge `[a, b]` of a
circumscribed hexagon `rein_hex3 a b c` is not in `K`, then the line of that edge can be turned
about a point of the edge (moving the vertices `a` and `b` along the adjacent edge lines) so
that the hexagon still contains `K` and has smaller area. -/
lemma rein_midpoint_mem_of_least {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {a b c : Fin 2 → ℝ}
    (h : rein_HexCond a b c) (hKH : K ⊆ hexagonOf (rein_hex3 a b c))
    (hmin : ∀ a' b' : Fin 2 → ℝ, rein_HexCond a' b' c → K ⊆ hexagonOf (rein_hex3 a' b' c) →
      det2 a b + det2 b c + det2 a c ≤ det2 a' b' + det2 b' c + det2 a' c) :
    midpoint ℝ a b ∈ K := by
  obtain ⟨hconv, hcomp, -, hsymm⟩ := hK
  have hstrip : ∀ x ∈ K, rein_strips a b c x :=
    fun x hx ↦ (rein_mem_hexagonOf_iff_strips h).1 (hKH hx)
  have hA0 : det2 a b ≠ 0 := h.hA.ne'
  by_contra hm
  -- the support functional `f ≥ 0` of the edge `[a, b]`, vanishing on its line
  let f : (Fin 2 → ℝ) → ℝ := fun x ↦ det2 a b - det2 (a - b) x
  have hf_cont : Continuous f := by simp only [f, det2]; fun_prop
  have hf_nonneg : ∀ x ∈ K, 0 ≤ f x := fun x hx ↦ by
    have := (hstrip x hx).1
    simp only [f]
    linarith [le_abs_self (det2 (a - b) x)]
  -- the position `λ` along the edge: `x = (1 - λ) a + λ b` on its line
  let lam : (Fin 2 → ℝ) → ℝ := fun x ↦ det2 a x / det2 a b
  have hlam_cont : Continuous lam := by simp only [lam, det2]; fun_prop
  have hline : ∀ x, f x = 0 → x = (1 - lam x) • a + lam x • b := by
    intro x hx
    simp only [f, lam] at hx ⊢
    ext i
    fin_cases i <;> simp <;> field_simp <;> simp only [det2, Pi.sub_apply] at hx ⊢
    · linear_combination (-a 0) * hx
    · linear_combination (-a 1) * hx
  -- the contact set `Z = K ∩ {f = 0}` lies on one side of the midpoint
  let Z := K ∩ f ⁻¹' {0}
  have hZc : IsCompact Z := hcomp.inter_right (isClosed_singleton.preimage hf_cont)
  have hZconv : Convex ℝ Z := by
    refine hconv.inter fun x hx y hy s t hs ht hst ↦ ?_
    simp only [mem_preimage, mem_singleton_iff, f] at hx hy ⊢
    simp only [det2, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hx hy ⊢
    linear_combination s * hx + t * hy - (a 0 * b 1 - a 1 * b 0) * hst
  have hdich : (∀ x ∈ Z, lam x < 1 / 2) ∨ (∀ x ∈ Z, 1 / 2 < lam x) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨x₁, hx₁, h₁⟩, ⟨x₂, hx₂, h₂⟩⟩ := hcon
    obtain ⟨x, hxZ, hx⟩ := hZconv.isPreconnected.intermediate_value hx₂ hx₁
      hlam_cont.continuousOn ⟨h₂, h₁⟩
    apply hm
    have hx' := hline x hxZ.2
    rw [hx] at hx'
    have : midpoint ℝ a b = x := by
      rw [midpoint_eq_smul_add, hx']
      ext i
      simp
      ring
    rw [this]
    exact hxZ.1
  -- a point `λ₀` of the edge between the contact set and the midpoint, `c₀ = 1 - 2 λ₀`
  obtain ⟨l₀, c₀, hc₀, hc₀def, hpos⟩ : ∃ l₀ c₀ : ℝ, c₀ ≠ 0 ∧ c₀ = 1 - 2 * l₀ ∧
      ∀ x ∈ Z, 0 < c₀ * (l₀ - lam x) := by
    rcases hdich with hL | hR
    · obtain ⟨e, he, hle⟩ := hZc.exists_forall_le' (f := fun x ↦ 1 / 2 - lam x)
        (continuous_const.sub hlam_cont).continuousOn (a := 0)
        (fun x hx ↦ by have := hL x hx; linarith)
      refine ⟨1 / 2 - e / 2, e, he.ne', by ring, fun x hx ↦ mul_pos he ?_⟩
      have := hle x hx
      linarith
    · obtain ⟨e, he, hle⟩ := hZc.exists_forall_le' (f := fun x ↦ lam x - 1 / 2)
        (hlam_cont.sub continuous_const).continuousOn (a := 0)
        (fun x hx ↦ by have := hR x hx; linarith)
      refine ⟨1 / 2 + e / 2, -e, neg_ne_zero.2 he.ne', by ring,
        fun x hx ↦ mul_pos_of_neg_of_neg (by linarith) ?_⟩
      have := hle x hx
      linarith
  -- the turning angles: `a` moves along the line of the edge `[-c, a]`, `b` along `[b, c]`
  obtain ⟨α, hα⟩ : ∃ α, α = det2 a b + det2 a c - det2 b c := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, β = det2 a b + det2 b c - det2 a c := ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ, γ = det2 b c + det2 a c - det2 a b := ⟨_, rfl⟩
  have hαpos : 0 < α := by rw [hα]; linarith [h.h2]
  have hβpos : 0 < β := by rw [hβ]; linarith [h.h0]
  obtain ⟨p, hp⟩ : ∃ p, p = l₀ * c₀ / α := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = (1 - l₀) * c₀ / β := ⟨_, rfl⟩
  have hpα : p * α = l₀ * c₀ := by rw [hp, div_mul_cancel₀ _ hαpos.ne']
  have hqβ : q * β = (1 - l₀) * c₀ := by rw [hq, div_mul_cancel₀ _ hβpos.ne']
  -- the first-order change `G` of the support functional; it is positive on the contact set
  let G : (Fin 2 → ℝ) → ℝ := fun x ↦
    q * det2 (c - b) (x - a) - p * det2 (a + c) (x - a) + p * α
  have hG_cont : Continuous G := by simp only [G, det2]; fun_prop
  have hGZ : ∀ x ∈ Z, 0 < G x := by
    intro x hx
    have hx' := hline x hx.2
    have key : G x = c₀ * (l₀ - lam x) := by
      generalize lam x = l at hx' ⊢
      subst hx'
      have e1 : det2 (c - b) ((1 - l) • a + l • b - a) = -l * β := by
        rw [hβ]
        simp only [det2, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      have e2 : det2 (a + c) ((1 - l) • a + l • b - a) = l * α := by
        rw [hα]
        simp only [det2, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      simp only [G]
      rw [e1, e2]
      linear_combination (1 - l) * hpα - l * hqβ
    rw [key]
    exact hpos x hx
  have hE : ∀ τ x, det2 (a + (τ * p) • (a + c)) (b + (τ * q) • (c - b)) -
      det2 (a + (τ * p) • (a + c) - (b + (τ * q) • (c - b))) x =
      f x + τ * G x + τ ^ 2 * (p * q * γ) := by
    intro τ x
    simp only [f, G, hα, hγ, det2, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have harea : ∀ τ, det2 (a + (τ * p) • (a + c)) (b + (τ * q) • (c - b)) +
      det2 (b + (τ * q) • (c - b)) c + det2 (a + (τ * p) • (a + c)) c -
      (det2 a b + det2 b c + det2 a c) = τ * (p * α - q * β) + τ ^ 2 * (p * q * γ) := by
    intro τ
    simp only [hα, hβ, hγ, det2, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  -- uniform bounds from compactness
  obtain ⟨η, hη, hηZ⟩ := hZc.exists_forall_le' hG_cont.continuousOn (a := 0) hGZ
  let K₁ := K ∩ {x | G x ≤ η / 2}
  have hK₁c : IsCompact K₁ := hcomp.inter_right (isClosed_le hG_cont continuous_const)
  have hfK₁ : ∀ x ∈ K₁, 0 < f x := by
    intro x hx
    rcases (hf_nonneg x hx.1).lt_or_eq with h' | h'
    · exact h'
    · have h1 := hηZ x ⟨hx.1, h'.symm⟩
      have h2 : G x ≤ η / 2 := hx.2
      linarith
  obtain ⟨δ, hδ, hδK₁⟩ := hK₁c.exists_forall_le' hf_cont.continuousOn (a := 0) hfK₁
  obtain ⟨M, hM⟩ := hcomp.exists_bound_of_continuousOn hG_cont.continuousOn
  obtain ⟨R, hR⟩ : ∃ R, R = |p * q * γ| := ⟨_, rfl⟩
  -- a small turning angle `τ > 0`
  have ev1 : ∀ᶠ τ in 𝓝 (0 : ℝ), τ * M + τ ^ 2 * R < δ := by
    have : Continuous fun τ : ℝ ↦ τ * M + τ ^ 2 * R := by fun_prop
    exact this.continuousAt.eventually_lt continuousAt_const (by simpa using hδ)
  have ev2 : ∀ᶠ τ in 𝓝 (0 : ℝ), τ * R < η / 2 := by
    have : Continuous fun τ : ℝ ↦ τ * R := by fun_prop
    exact this.continuousAt.eventually_lt continuousAt_const (by simpa using half_pos hη)
  have ev3 : ∀ᶠ τ in 𝓝 (0 : ℝ), τ * (p * q * γ) < c₀ ^ 2 := by
    have : Continuous fun τ : ℝ ↦ τ * (p * q * γ) := by fun_prop
    exact this.continuousAt.eventually_lt continuousAt_const (by simp only [zero_mul]; positivity)
  have ev4 := rein_eventually_hexCond h (a' := fun τ ↦ a + (τ * p) • (a + c))
    (b' := fun τ ↦ b + (τ * q) • (c - b)) (by fun_prop) (by fun_prop) (by simp) (by simp)
  obtain ⟨τ, ⟨⟨⟨h1, h2⟩, h3⟩, hhex⟩, hτ⟩ := ((((ev1.and ev2).and ev3).and ev4).filter_mono
    nhdsWithin_le_nhds |>.and (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
  have hτ0 : 0 < τ := hτ
  -- the turned support line still supports `K`
  have hE_nonneg : ∀ x ∈ K, 0 ≤ f x + τ * G x + τ ^ 2 * (p * q * γ) := by
    intro x hx
    have hRb : -(τ ^ 2 * R) ≤ τ ^ 2 * (p * q * γ) := by
      have := mul_nonneg (sq_nonneg τ)
        (show 0 ≤ p * q * γ + R by rw [hR]; linarith [neg_abs_le (p * q * γ)])
      nlinarith
    rcases le_or_gt (G x) (η / 2) with hGx | hGx
    · have hfx := hδK₁ x ⟨hx, hGx⟩
      have hGM : |G x| ≤ M := by simpa [Real.norm_eq_abs] using hM x hx
      have : -(τ * M) ≤ τ * G x := by
        have := neg_abs_le (G x)
        nlinarith
      linarith
    · have hfx := hf_nonneg x hx
      have e1 : τ * (η / 2) ≤ τ * G x := mul_le_mul_of_nonneg_left hGx.le hτ0.le
      have e2 : τ ^ 2 * R ≤ τ * (η / 2) := by nlinarith
      linarith
  have hKsub : K ⊆ hexagonOf (rein_hex3 (a + (τ * p) • (a + c)) (b + (τ * q) • (c - b)) c) := by
    intro x hx
    rw [rein_mem_hexagonOf_iff_strips hhex]
    have hE1 := hE_nonneg x hx
    have hE2 := hE_nonneg (-x) (hsymm x hx)
    rw [← hE] at hE1 hE2
    rw [rein_det2_neg_right] at hE2
    obtain ⟨-, s1, s2⟩ := hstrip x hx
    have hb' : b + (τ * q) • (c - b) - c = (1 - τ * q) • (b - c) := by module
    have hca' : c + (a + (τ * p) • (a + c)) = (1 + τ * p) • (c + a) := by module
    have hdb : det2 (b + (τ * q) • (c - b)) c = (1 - τ * q) * det2 b c := by
      simp only [det2, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    have hda : det2 (a + (τ * p) • (a + c)) c = (1 + τ * p) * det2 a c := by
      simp only [det2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    have hq1 : 0 < 1 - τ * q := by
      have := hhex.hB
      rw [hdb] at this
      by_contra hh
      push Not at hh
      nlinarith [h.hB]
    have hp1 : 0 < 1 + τ * p := by
      have := hhex.hC
      rw [hda] at this
      by_contra hh
      push Not at hh
      nlinarith [h.hC]
    refine ⟨abs_le.2 ⟨by linarith, by linarith⟩, ?_, ?_⟩
    · rw [hb', rein_det2_smul_left, abs_mul, abs_of_pos hq1, hdb]
      exact mul_le_mul_of_nonneg_left s1 hq1.le
    · rw [hca', rein_det2_smul_left, abs_mul, abs_of_pos hp1, hda]
      exact mul_le_mul_of_nonneg_left s2 hp1.le
  -- and the turned hexagon has smaller area
  have hle := hmin _ _ hhex hKsub
  have ha := harea τ
  have key : τ * (p * α - q * β) + τ ^ 2 * (p * q * γ) =
      -(τ * (c₀ ^ 2 - τ * (p * q * γ))) := by
    rw [hpα, hqβ, hc₀def]
    ring
  linarith [mul_pos hτ0 (sub_pos.2 h3)]

open Filter Topology in
/-- The midpoint of the edge `[a, b]` of a least-area hexagon `rein_hex3 a b c` circumscribing `K`
is a boundary point of `K`: it is in `K` (`rein_midpoint_mem_of_least`) and on a support line. -/
lemma rein_midpoint_mem_frontier_of_least {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K)
    {a b c : Fin 2 → ℝ} (h : rein_HexCond a b c) (hKH : K ⊆ hexagonOf (rein_hex3 a b c))
    (hmin : ∀ a' b' : Fin 2 → ℝ, rein_HexCond a' b' c → K ⊆ hexagonOf (rein_hex3 a' b' c) →
      det2 a b + det2 b c + det2 a c ≤ det2 a' b' + det2 b' c + det2 a' c) :
    midpoint ℝ a b ∈ frontier K := by
  have hmK := rein_midpoint_mem_of_least hK h hKH hmin
  refine ⟨subset_closure hmK, fun hmi ↦ ?_⟩
  have hc : Continuous fun ε : ℝ ↦ midpoint ℝ a b + ε • a := by fun_prop
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), midpoint ℝ a b + ε • a ∈ K :=
    hc.continuousAt.preimage_mem_nhds (by simpa using mem_interior_iff_mem_nhds.1 hmi)
  obtain ⟨ε, hεK, hε⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
  have hε0 : (0 : ℝ) < ε := hε
  have := ((rein_mem_hexagonOf_iff_strips h).1 (hKH hεK)).1
  have e : det2 (a - b) (midpoint ℝ a b + ε • a) = (1 + ε) * det2 a b := by
    rw [midpoint_eq_smul_add]
    simp only [det2, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, invOf_eq_inv]
    ring
  rw [e, abs_le] at this
  nlinarith [h.hA]

/-- `rein_hexMidpoint_mem_frontier` for the edge `j = 0`. -/
lemma rein_hexMidpoint_zero_mem_frontier {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K)
    {v : ZMod 6 → Fin 2 → ℝ} (hv : IsLeastAreaHexagon K v) : hexMidpoint v 0 ∈ frontier K := by
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c, v = rein_hex3 a b c := ⟨_, _, _, rein_eq_hex3 hv.1⟩
  have h := rein_isCSHexagon_iff_hexCond.1 hv.1
  have hm : hexMidpoint (rein_hex3 a b c) 0 = midpoint ℝ a b := rfl
  rw [hm]
  refine rein_midpoint_mem_frontier_of_least hK h hv.2.1 fun a' b' h' hK' ↦ ?_
  have := hv.2.2 _ (rein_isCSHexagon_iff_hexCond.2 h') hK'
  rw [rein_volume_hexagonOf_hex3' h, rein_volume_hexagonOf_hex3' h'] at this
  exact (ENNReal.ofReal_le_ofReal_iff (by linarith [h'.hA, h'.hB, h'.hC])).1 this

/-- The midpoints of the edges of a least-area centrally symmetric hexagon circumscribing `K` lie
on the boundary of `K` (§2.2, before Definition 2.2.3). -/
lemma rein_hexMidpoint_mem_frontier {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K)
    {v : ZMod 6 → Fin 2 → ℝ} (hv : IsLeastAreaHexagon K v) (j : ZMod 6) :
    hexMidpoint v j ∈ frontier K := by
  let v' : ZMod 6 → Fin 2 → ℝ := fun k ↦ v (k + j)
  have hrange : range v' = range v := (Equiv.addRight j).surjective.range_comp v
  have hhex : hexagonOf v' = hexagonOf v := by simp only [hexagonOf, hrange]
  have hcs : IsCSHexagon v' := by
    intro k
    obtain ⟨h1, h2, h3⟩ := hv.1 (k + j)
    refine ⟨?_, ?_, ?_⟩
    · simp only [v']; rw [show k + 3 + j = k + j + 3 by ring]; exact h1
    · simp only [v']; rw [show k + 1 + j = k + j + 1 by ring]; exact h2
    · simp only [v']
      rw [show k + 1 + j = k + j + 1 by ring, show k + 2 + j = k + j + 2 by ring]
      exact h3
  have hv' : IsLeastAreaHexagon K v' :=
    ⟨hcs, hhex ▸ hv.2.1, fun w hw hKw ↦ hhex ▸ hv.2.2 w hw hKw⟩
  have hm : hexMidpoint v' 0 = hexMidpoint v j := by
    simp only [hexMidpoint, v', zero_add]
    rw [add_comm 1 j]
  rw [← hm]
  exact rein_hexMidpoint_zero_mem_frontier hK hv'



/-- A centrally symmetric convex disk contains the origin in its interior. -/
lemma rein_zero_mem_interior {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) :
    (0 : Fin 2 → ℝ) ∈ interior K := by
  obtain ⟨hconv, -, ⟨x, hx⟩, hsymm⟩ := hK
  have hneg : -interior K ⊆ interior K := by
    refine interior_maximal (fun y hy ↦ ?_) (isOpen_interior.neg)
    simpa using hsymm _ (interior_subset (Set.mem_neg.1 hy))
  have hx' : -x ∈ interior K := hneg (by simpa using hx)
  have := hconv.interior hx hx' (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  simpa [smul_neg] using this


open Filter Topology

/-! ### Clipping the corners of a parallelogram -/

lemma rein_volume_real_hexagonOf_hex3 {a b c : Fin 2 → ℝ} (h : IsCSHexagon (rein_hex3 a b c)) :
    volume.real (hexagonOf (rein_hex3 a b c)) = det2 a b + det2 b c + det2 a c := by
  obtain ⟨h1, h2, h3, -⟩ := (rein_isCSHexagon_hex3_iff a b c).1 h
  rw [measureReal_def, rein_volume_hexagonOf_hex3 h, ENNReal.toReal_ofReal (by linarith)]

/-- **Clipping** (§2.2, before Theorem 2.2.2): if `K` lies in the parallelogram with vertices
`p, q, -p, -q` (`det(p, q) > 0`) and `q ∉ K`, then clipping the corners `±q` gives a centrally
symmetric hexagon containing `K` of smaller area than the parallelogram, `2 det(p, q)`. -/
lemma rein_clip {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {p q : Fin 2 → ℝ}
    (hpq : 0 < det2 p q)
    (hP : ∀ x ∈ K, 0 ≤ det2 (q - p) (x - p) ∧ 0 ≤ det2 (-p - q) (x - q)) (hq : q ∉ K) :
    ∃ w, IsCSHexagon w ∧ K ⊆ hexagonOf w ∧ volume.real (hexagonOf w) < 2 * det2 p q := by
  set D := det2 p q with hD
  -- the bound `det(p, x) ≤ D` on the parallelogram, with equality only at `q`
  have hbound : ∀ x ∈ K, det2 p x ≤ D ∧ (det2 p x = D → x = q) := by
    intro x hx
    obtain ⟨h1, h2⟩ := hP x hx
    have e1 : det2 (q - p) (x - p) = D - det2 x q - det2 p x := by
      simp only [hD, det2, Pi.sub_apply]; ring
    have e2 : det2 (-p - q) (x - q) = D + det2 x q - det2 p x := by
      simp only [hD, det2, Pi.sub_apply, Pi.neg_apply]; ring
    rw [e1] at h1
    rw [e2] at h2
    refine ⟨by linarith, fun h ↦ ?_⟩
    have hs : det2 x q = 0 := by linarith
    have hcr := rein_cramer p q x
    rw [hs, h, zero_smul, zero_add] at hcr
    exact smul_right_injective _ hpq.ne' hcr
  obtain ⟨xs, hxsK, hxs⟩ := hK.2.1.exists_isMaxOn
    ⟨0, interior_subset (rein_zero_mem_interior hK)⟩ (rein_continuous_det2_left p).continuousOn
  set M := det2 p xs
  have hMD : M < D := by
    rcases (hbound xs hxsK).1.lt_or_eq with h | h
    · exact h
    · exact absurd ((hbound xs hxsK).2 h ▸ hxsK) hq
  have hM0 : 0 ≤ M := by
    have : det2 p 0 ≤ det2 p xs := hxs (interior_subset (rein_zero_mem_interior hK))
    rw [show det2 p 0 = 0 by simp [det2]] at this
    exact this
  have hKM : ∀ x ∈ K, det2 p x ≤ M := fun x hx ↦ hxs hx
  set ε := (D - M) / (2 * D) with hε
  have hε0 : 0 < ε := div_pos (by linarith) (by linarith)
  have hε1 : ε ≤ 1 / 2 := by
    rw [hε, div_le_iff₀ (by linarith)]; linarith
  have hεD : (1 - ε) * D = (D + M) / 2 := by rw [hε]; field_simp; ring
  set q1 := q + ε • (p - q) with hq1
  set q2 := q - ε • (p + q) with hq2
  have d1 : det2 p q1 = (1 - ε) * D := by
    simp only [hq1, hD, det2, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  have d2 : det2 q1 q2 = 2 * ε * (1 - ε) * D := by
    simp only [hq1, hq2, hD, det2, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  have d3 : det2 p q2 = (1 - ε) * D := by
    simp only [hq2, hD, det2, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  have hpos1 : 0 < (1 - ε) * D := mul_pos (by linarith) hpq
  have hpos2 : 0 < 2 * ε * (1 - ε) * D := by
    have := mul_pos (mul_pos (mul_pos two_pos hε0) (show 0 < 1 - ε by linarith)) hpq
    linarith
  have hhex : IsCSHexagon (rein_hex3 p q1 q2) := by
    rw [rein_isCSHexagon_hex3_iff, d1, d2, d3]
    refine ⟨hpos1, hpos2, hpos1, by linarith, by linarith, ?_⟩
    nlinarith
  refine ⟨_, hhex, fun x hx ↦ ?_, ?_⟩
  · rw [rein_mem_hexagonOf_hex3 hhex]
    have hx' := hK.2.2.2 x hx
    obtain ⟨a1, a2⟩ := hP x hx
    obtain ⟨b1, b2⟩ := hP (-x) hx'
    have m1 := hKM x hx
    have m2 := hKM (-x) hx'
    have f0 : ∀ y, det2 (q1 - p) (y - p) = (1 - ε) * det2 (q - p) (y - p) := by
      intro y; simp only [hq1, det2, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
    have f1 : ∀ y, det2 (q2 - q1) (y - q1) = 2 * ε * ((1 - ε) * D - det2 p y) := by
      intro y; simp only [hq1, hq2, hD, det2, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
        smul_eq_mul]; ring
    have f2 : ∀ y, det2 (-p - q2) (y - q2) = (1 - ε) * det2 (-p - q) (y - q) := by
      intro y; simp only [hq2, det2, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply,
        smul_eq_mul]; ring
    have hε' : 0 ≤ 1 - ε := by linarith
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [f0]; exact mul_nonneg hε' a1
    · rw [f1]; exact mul_nonneg (by linarith) (by linarith)
    · rw [f2]; exact mul_nonneg hε' a2
    · rw [f0]; exact mul_nonneg hε' b1
    · rw [f1]; exact mul_nonneg (by linarith) (by linarith)
    · rw [f2]; exact mul_nonneg hε' b2
  · rw [rein_volume_real_hexagonOf_hex3 hhex, d1, d2, d3]
    nlinarith


/-- Clipping, for a parallelogram one of whose vertices `p, q` is not in `K`. -/
lemma rein_clip' {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {p q : Fin 2 → ℝ}
    (hpq : 0 < det2 p q)
    (hP : ∀ x ∈ K, 0 ≤ det2 (q - p) (x - p) ∧ 0 ≤ det2 (-p - q) (x - q))
    (hpqK : ¬(p ∈ K ∧ q ∈ K)) :
    ∃ w, IsCSHexagon w ∧ K ⊆ hexagonOf w ∧ volume.real (hexagonOf w) < 2 * det2 p q := by
  by_cases hq : q ∈ K
  · have hp : p ∉ K := fun hp ↦ hpqK ⟨hp, hq⟩
    -- relabel the parallelogram as `q, -p, -q, p`
    have hpq' : 0 < det2 q (-p) := by rw [rein_det2_neg_right, rein_det2_swap, neg_neg]; exact hpq
    have hP' : ∀ x ∈ K, 0 ≤ det2 (-p - q) (x - q) ∧ 0 ≤ det2 (-q - -p) (x - -p) := by
      intro x hx
      refine ⟨(hP x hx).2, ?_⟩
      have := (hP (-x) (hK.2.2.2 x hx)).1
      have e : det2 (-q - -p) (x - -p) = det2 (q - p) (-x - p) := by
        simp only [det2, Pi.sub_apply, Pi.neg_apply]; ring
      rw [e]; exact this
    have hnp : -p ∉ K := fun h ↦ hp (by simpa using hK.2.2.2 _ h)
    obtain ⟨w, hw, hKw, harea⟩ := rein_clip hK hpq' hP' hnp
    refine ⟨w, hw, hKw, ?_⟩
    rwa [rein_det2_neg_right, rein_det2_swap, neg_neg] at harea
  · exact rein_clip hK hpq hP hq

/-- A bound on the vertices of a centrally symmetric hexagon containing the ball of radius `r`
about the origin, in terms of its area. -/
lemma rein_hex_bound {K : Set (Fin 2 → ℝ)} {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball (0 : Fin 2 → ℝ) r ⊆ K) {a b c : Fin 2 → ℝ}
    (h : IsCSHexagon (rein_hex3 a b c)) (hKH : K ⊆ hexagonOf (rein_hex3 a b c)) (i : Fin 2) :
    r * |a i| ≤ 3 * (det2 a b + det2 b c + det2 a c) ∧
      r * |b i| ≤ 3 * (det2 a b + det2 b c + det2 a c) ∧
      r * |c i| ≤ 3 * (det2 a b + det2 b c + det2 a c) := by
  obtain ⟨h1, h2, h3, -⟩ := (rein_isCSHexagon_hex3_iff a b c).1 h
  have hin : ∀ x : Fin 2 → ℝ, (∀ j, |x j| < r) → rein_InHex a b c x := by
    intro x hx
    refine (rein_mem_hexagonOf_hex3 h x).1 (hKH (hball ?_))
    rw [mem_ball_zero_iff, pi_norm_lt_iff hr]
    intro j; rw [Real.norm_eq_abs]; exact hx j
  have hr2 : |r / 2| < r := by rw [abs_of_pos (by linarith)]; linarith
  have hr2' : |-(r / 2)| < r := by rw [abs_neg]; exact hr2
  have h0 : |(0 : ℝ)| < r := by simpa using hr
  have q1 := hin ![r / 2, 0] (by intro j; fin_cases j <;> simpa)
  have q2 := hin ![-(r / 2), 0] (by intro j; fin_cases j <;> simpa)
  have q3 := hin ![0, r / 2] (by intro j; fin_cases j <;> simpa)
  have q4 := hin ![0, -(r / 2)] (by intro j; fin_cases j <;> simpa)
  simp only [rein_InHex, det2, Pi.sub_apply, Pi.neg_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one] at q1 q2 q3 q4 h1 h2 h3
  obtain ⟨a1, a2, a3, -, -, -⟩ := q1
  obtain ⟨b1, b2, b3, -, -, -⟩ := q2
  obtain ⟨c1, c2, c3, -, -, -⟩ := q3
  obtain ⟨d1, d2, d3, -, -, -⟩ := q4
  simp only [det2]
  rw [← abs_of_pos hr, ← abs_mul, ← abs_mul, ← abs_mul, abs_le, abs_le, abs_le]
  fin_cases i <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one] <;>
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> nlinarith


lemma rein_volume_real_pos {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) : 0 < volume.real K := by
  have h1 : 0 < volume (interior K) := isOpen_interior.measure_pos volume hK.2.2.1
  have h2 : volume K < ⊤ := hK.2.1.measure_lt_top
  rw [measureReal_def]
  exact ENNReal.toReal_pos (lt_of_lt_of_le h1 (measure_mono interior_subset)).ne' h2.ne

lemma rein_isCompact_hexagonOf (v : ZMod 6 → Fin 2 → ℝ) : IsCompact (hexagonOf v) := by
  unfold hexagonOf; exact (Set.finite_range v).isCompact_convexHull ℝ

lemma rein_continuous_hex3_apply (k : ZMod 6) :
    Continuous fun s : (Fin 2 → ℝ) × (Fin 2 → ℝ) × (Fin 2 → ℝ) ↦ rein_hex3 s.1 s.2.1 s.2.2 k := by
  rcases rein_zmod6_cases k with rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [rein_hex3_zero, rein_hex3_one, rein_hex3_two, rein_hex3_three, rein_hex3_four,
    rein_hex3_five] <;> fun_prop

/-- **Limits of circumscribed hexagons.** A sequence of centrally symmetric hexagons containing
`K` whose areas tend to a lower bound `A` of the areas of all such hexagons has a subsequence
converging to a least-area hexagon of `K`, of area `A`. A degenerate limit would be a
parallelogram of area `A` containing `K`, whose corners could be clipped (`rein_clip'`), unless
`K` is that parallelogram (excluded by `hnp`). -/
lemma rein_limit_hex {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K)
    (hnp : ∀ p q, 0 < det2 p q →
      (∀ x ∈ K, 0 ≤ det2 (q - p) (x - p) ∧ 0 ≤ det2 (-p - q) (x - q)) → ¬(p ∈ K ∧ q ∈ K))
    {A : ℝ} (hA : ∀ w, IsCSHexagon w → K ⊆ hexagonOf w → A ≤ volume.real (hexagonOf w))
    (u : ℕ → ZMod 6 → Fin 2 → ℝ) (hu : ∀ n, IsCSHexagon (u n)) (hKu : ∀ n, K ⊆ hexagonOf (u n))
    (harea : Tendsto (fun n ↦ volume.real (hexagonOf (u n))) atTop (𝓝 A)) :
    ∃ w, IsLeastAreaHexagon K w ∧ volume.real (hexagonOf w) = A ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun n ↦ u (φ n)) atTop (𝓝 w) := by
  obtain ⟨r, hr, hball⟩ :=
    Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 (rein_zero_mem_interior hK))
  obtain ⟨B, hB⟩ := harea.bddAbove_range
  set t : ℕ → (Fin 2 → ℝ) × (Fin 2 → ℝ) × (Fin 2 → ℝ) := fun n ↦ (u n 0, u n 1, u n 2) with ht
  have hu3 : ∀ n, u n = rein_hex3 (t n).1 (t n).2.1 (t n).2.2 := fun n ↦ rein_eq_hex3 (hu n)
  have hu3' : ∀ n, IsCSHexagon (rein_hex3 (t n).1 (t n).2.1 (t n).2.2) := fun n ↦ hu3 n ▸ hu n
  set S : (Fin 2 → ℝ) × (Fin 2 → ℝ) × (Fin 2 → ℝ) → ℝ :=
    fun s ↦ det2 s.1 s.2.1 + det2 s.2.1 s.2.2 + det2 s.1 s.2.2 with hS
  have hSc : Continuous S := by simp only [hS, det2]; fun_prop
  have harea3 : ∀ n, volume.real (hexagonOf (u n)) = S (t n) := by
    intro n; rw [hu3 n]; exact rein_volume_real_hexagonOf_hex3 (hu3' n)
  have hSB : ∀ n, S (t n) ≤ B := fun n ↦ harea3 n ▸ hB ⟨n, rfl⟩
  have hSpos : ∀ n, 0 < S (t n) := by
    intro n
    obtain ⟨h1, h2, h3, -⟩ := (rein_isCSHexagon_hex3_iff _ _ _).1 (hu3' n)
    simp only [hS]; linarith
  have hB0 : 0 ≤ 3 * B / r := div_nonneg (by linarith [hSpos 0, hSB 0]) hr.le
  have hmem : ∀ n, t n ∈ Metric.closedBall (0 : Fin 2 → ℝ) (3 * B / r) ×ˢ
      (Metric.closedBall (0 : Fin 2 → ℝ) (3 * B / r) ×ˢ Metric.closedBall 0 (3 * B / r)) := by
    intro n
    have hb := rein_hex_bound hr hball (hu3' n) (hu3 n ▸ hKu n)
    simp only [mem_prod, mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hB0, Real.norm_eq_abs]
    have hS' := hSB n
    simp only [hS] at hS'
    refine ⟨fun i ↦ ?_, fun i ↦ ?_, fun i ↦ ?_⟩ <;> rw [le_div_iff₀ hr] <;>
      nlinarith [(hb i).1, (hb i).2.1, (hb i).2.2]
  obtain ⟨⟨a, b, c⟩, -, φ, hφ, hlim⟩ := (isCompact_closedBall _ _ |>.prod
    (isCompact_closedBall _ _ |>.prod (isCompact_closedBall _ _))).tendsto_subseq hmem
  have lim_ge : ∀ f : (Fin 2 → ℝ) × (Fin 2 → ℝ) × (Fin 2 → ℝ) → ℝ, Continuous f →
      (∀ n, 0 ≤ f (t n)) → 0 ≤ f (a, b, c) :=
    fun f hf h ↦ ge_of_tendsto' ((hf.tendsto _).comp hlim) (fun n ↦ h (φ n))
  -- the area of the limit
  have hSA : S (a, b, c) = A := by
    refine tendsto_nhds_unique ((hSc.tendsto _).comp hlim) ?_
    have := harea.comp hφ.tendsto_atTop
    refine this.congr fun n ↦ ?_
    simp only [Function.comp_apply, harea3]
  have hApos : 0 < A := by
    have h : ∀ n, volume.real K ≤ volume.real (hexagonOf (u n)) := fun n ↦
      measureReal_mono (hKu n) ((rein_isCompact_hexagonOf (u n)).measure_lt_top (μ := volume)).ne
    exact lt_of_lt_of_le (rein_volume_real_pos hK) (ge_of_tendsto' harea h)
  -- non-strict limits of the hexagon conditions and of the half-plane conditions
  have hD : ∀ (f : (Fin 2 → ℝ) × (Fin 2 → ℝ) × (Fin 2 → ℝ) → ℝ), Continuous f →
      (∀ a b c, IsCSHexagon (rein_hex3 a b c) → 0 ≤ f (a, b, c)) → 0 ≤ f (a, b, c) :=
    fun f hf h ↦ lim_ge f hf fun n ↦ h _ _ _ (hu3' n)
  have hT1 : 0 ≤ det2 a b + det2 b c - det2 a c := hD (fun s ↦ det2 s.1 s.2.1 + det2 s.2.1 s.2.2 -
      det2 s.1 s.2.2) (by simp only [det2]; fun_prop) fun a b c h ↦ by
    obtain ⟨-, -, -, h4, -⟩ := (rein_isCSHexagon_hex3_iff a b c).1 h; simp only; linarith
  have hT2 : 0 ≤ det2 b c + det2 a c - det2 a b := hD (fun s ↦ det2 s.2.1 s.2.2 + det2 s.1 s.2.2 -
      det2 s.1 s.2.1) (by simp only [det2]; fun_prop) fun a b c h ↦ by
    obtain ⟨-, -, -, -, h5, -⟩ := (rein_isCSHexagon_hex3_iff a b c).1 h; simp only; linarith
  have hT0 : 0 ≤ det2 a b + det2 a c - det2 b c := hD (fun s ↦ det2 s.1 s.2.1 + det2 s.1 s.2.2 -
      det2 s.2.1 s.2.2) (by simp only [det2]; fun_prop) fun a b c h ↦ by
    obtain ⟨-, -, -, -, -, h6⟩ := (rein_isCSHexagon_hex3_iff a b c).1 h; simp only; linarith
  have hin : ∀ x ∈ K, rein_InHex a b c x := by
    intro x hx
    have hx' : ∀ n, rein_InHex (t n).1 (t n).2.1 (t n).2.2 x := fun n ↦
      (rein_mem_hexagonOf_hex3 (hu3' n) x).1 (hu3 n ▸ hKu n hx)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact lim_ge (fun s ↦ det2 (s.2.1 - s.1) (x - s.1)) (by simp only [det2]; fun_prop)
        fun n ↦ (hx' n).1
    · exact lim_ge (fun s ↦ det2 (s.2.2 - s.2.1) (x - s.2.1)) (by simp only [det2]; fun_prop)
        fun n ↦ (hx' n).2.1
    · exact lim_ge (fun s ↦ det2 (-s.1 - s.2.2) (x - s.2.2)) (by simp only [det2]; fun_prop)
        fun n ↦ (hx' n).2.2.1
    · exact lim_ge (fun s ↦ det2 (s.2.1 - s.1) (-x - s.1)) (by simp only [det2]; fun_prop)
        fun n ↦ (hx' n).2.2.2.1
    · exact lim_ge (fun s ↦ det2 (s.2.2 - s.2.1) (-x - s.2.1)) (by simp only [det2]; fun_prop)
        fun n ↦ (hx' n).2.2.2.2.1
    · exact lim_ge (fun s ↦ det2 (-s.1 - s.2.2) (-x - s.2.2)) (by simp only [det2]; fun_prop)
        fun n ↦ (hx' n).2.2.2.2.2
  simp only [hS] at hSA
  -- a degenerate limit is a parallelogram of area `A`, which can be clipped
  have hclip : ∀ p q, 0 < det2 p q → 2 * det2 p q = A →
      (∀ x ∈ K, 0 ≤ det2 (q - p) (x - p) ∧ 0 ≤ det2 (-p - q) (x - q)) → False := by
    intro p q hpq hA' hP
    obtain ⟨w, hw, hKw, hlt⟩ := rein_clip' hK hpq hP (hnp p q hpq hP)
    linarith [hA w hw hKw]
  by_cases hstrict : 0 < det2 a b + det2 b c - det2 a c ∧ 0 < det2 b c + det2 a c - det2 a b ∧
      0 < det2 a b + det2 a c - det2 b c
  · obtain ⟨s1, s2, s3⟩ := hstrict
    have hw : IsCSHexagon (rein_hex3 a b c) := by
      rw [rein_isCSHexagon_hex3_iff]
      refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
    have hKw : K ⊆ hexagonOf (rein_hex3 a b c) := fun x hx ↦
      (rein_mem_hexagonOf_hex3 hw x).2 (hin x hx)
    have hvol : volume.real (hexagonOf (rein_hex3 a b c)) = A := by
      rw [rein_volume_real_hexagonOf_hex3 hw]; exact hSA
    refine ⟨rein_hex3 a b c, ⟨hw, hKw, fun w' hw' hKw' ↦ ?_⟩, hvol, φ, hφ, ?_⟩
    · have h1 := hA w' hw' hKw'
      have hf1 : volume (hexagonOf (rein_hex3 a b c)) ≠ ⊤ :=
        (rein_isCompact_hexagonOf (rein_hex3 a b c)).measure_lt_top.ne
      have hf2 : volume (hexagonOf w') ≠ ⊤ := (rein_isCompact_hexagonOf w').measure_lt_top.ne
      rw [← ENNReal.ofReal_toReal hf1, ← ENNReal.ofReal_toReal hf2]
      apply ENNReal.ofReal_le_ofReal
      rw [← measureReal_def, ← measureReal_def, hvol]; exact h1
    · refine tendsto_pi_nhds.2 fun k ↦ ?_
      have : (fun n ↦ u (φ n) k) = fun n ↦ rein_hex3 (t (φ n)).1 (t (φ n)).2.1 (t (φ n)).2.2 k :=
        funext fun n ↦ by rw [← hu3]
      rw [this]
      exact ((rein_continuous_hex3_apply k).tendsto _).comp hlim
  · exfalso
    simp only [not_and_or, not_lt] at hstrict
    rcases hstrict with h | h | h
    · -- the turn at `b` vanishes: the parallelogram `a, c, -a, -c`
      have h' : det2 a c = det2 a b + det2 b c := by linarith
      refine hclip a c (by linarith) (by linarith) fun x hx ↦ ⟨?_, (hin x hx).2.2.1⟩
      have e : det2 (c - a) (x - a) = det2 (b - a) (x - a) + det2 (c - b) (x - b) := by
        have : det2 (c - a) (x - a) - (det2 (b - a) (x - a) + det2 (c - b) (x - b)) =
            det2 a c - (det2 a b + det2 b c) := by simp only [det2, Pi.sub_apply]; ring
        linarith
      rw [e]; exact add_nonneg (hin x hx).1 (hin x hx).2.1
    · -- the turn at `c` vanishes: the parallelogram `a, b, -a, -b`
      have h' : det2 a b = det2 b c + det2 a c := by linarith
      refine hclip a b (by linarith) (by linarith) fun x hx ↦ ⟨(hin x hx).1, ?_⟩
      have e : det2 (-a - b) (x - b) = det2 (c - b) (x - b) + det2 (-a - c) (x - c) := by
        have : det2 (-a - b) (x - b) - (det2 (c - b) (x - b) + det2 (-a - c) (x - c)) =
            det2 a b - (det2 b c + det2 a c) := by
          simp only [det2, Pi.sub_apply, Pi.neg_apply]; ring
        linarith
      rw [e]; exact add_nonneg (hin x hx).2.1 (hin x hx).2.2.1
    · -- the turn at `a` vanishes: the parallelogram `b, c, -b, -c`
      have h' : det2 b c = det2 a b + det2 a c := by linarith
      refine hclip b c (by linarith) (by linarith) fun x hx ↦ ⟨(hin x hx).2.1, ?_⟩
      have e : det2 (-b - c) (x - c) = det2 (-a - c) (x - c) + det2 (b - a) (-x - a) := by
        have : det2 (-b - c) (x - c) - (det2 (-a - c) (x - c) + det2 (b - a) (-x - a)) =
            det2 b c - (det2 a b + det2 a c) := by
          simp only [det2, Pi.sub_apply, Pi.neg_apply]; ring
        linarith
      rw [e]; exact add_nonneg (hin x hx).2.2.1 (hin x hx).2.2.2.1


/-- A disk that is not a parallelogram is not the parallelogram `p, q, -p, -q` containing it. -/
lemma rein_hnp_of_not_isParallelogram {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K)
    (hnp : ¬IsParallelogram K) :
    ∀ p q, 0 < det2 p q →
      (∀ x ∈ K, 0 ≤ det2 (q - p) (x - p) ∧ 0 ≤ det2 (-p - q) (x - q)) → ¬(p ∈ K ∧ q ∈ K) := by
  rintro p q hpq hP ⟨hp, hq⟩
  apply hnp
  set D := det2 p q
  have hD := hpq.ne'
  refine ⟨0, (1 / 2 : ℝ) • (p - q), (1 / 2 : ℝ) • (p + q), ?_, ?_⟩
  · have : det2 ((1 / 2 : ℝ) • (p - q)) ((1 / 2 : ℝ) • (p + q)) = D / 2 := by
      simp only [D, det2, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]; ring
    rw [this]; positivity
  ext x
  simp only [mem_ofPred_eq, zero_add]
  constructor
  · intro hx
    obtain ⟨a1, a2⟩ := hP x hx
    obtain ⟨b1, b2⟩ := hP (-x) (hK.2.2.2 x hx)
    set α := det2 x q / D
    set β := det2 p x / D
    have e1 : det2 (q - p) (x - p) = D * (1 - α - β) := by
      simp only [α, β]; field_simp; simp only [D, det2, Pi.sub_apply]; ring
    have e2 : det2 (-p - q) (x - q) = D * (1 + α - β) := by
      simp only [α, β]; field_simp; simp only [D, det2, Pi.sub_apply, Pi.neg_apply]; ring
    have e3 : det2 (q - p) (-x - p) = D * (1 + α + β) := by
      simp only [α, β]; field_simp; simp only [D, det2, Pi.sub_apply, Pi.neg_apply]; ring
    have e4 : det2 (-p - q) (-x - q) = D * (1 - α + β) := by
      simp only [α, β]; field_simp; simp only [D, det2, Pi.sub_apply, Pi.neg_apply]; ring
    rw [e1] at a1; rw [e2] at a2; rw [e3] at b1; rw [e4] at b2
    have f1 := (mul_nonneg_iff_of_pos_left hpq).1 a1
    have f2 := (mul_nonneg_iff_of_pos_left hpq).1 a2
    have f3 := (mul_nonneg_iff_of_pos_left hpq).1 b1
    have f4 := (mul_nonneg_iff_of_pos_left hpq).1 b2
    refine ⟨α - β, α + β, abs_le.2 ⟨by linarith, by linarith⟩,
      abs_le.2 ⟨by linarith, by linarith⟩, ?_⟩
    have hcr := rein_cramer p q x
    ext i
    have hi := congrFun hcr i
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul, α, β] at hi ⊢
    field_simp
    linarith
  · rintro ⟨s, t, hs, ht, rfl⟩
    have hx : s • ((1 / 2 : ℝ) • (p - q)) + t • ((1 / 2 : ℝ) • (p + q)) =
        ((s + t) / 2) • p + ((t - s) / 2) • q := by
      ext i; simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]; ring
    rw [hx]
    have h0 : (0 : Fin 2 → ℝ) ∈ K := interior_subset (rein_zero_mem_interior hK)
    have hsym := hK.2.2.2
    -- a combination `α p + β q` with `|α| + |β| ≤ 1`
    have key : ∀ α β : ℝ, |α| + |β| ≤ 1 → α • p + β • q ∈ K := by
      intro α β hαβ
      have hp' : ∀ α : ℝ, α • p = |α| • (if 0 ≤ α then p else -p) := by
        intro α; split_ifs with h
        · rw [abs_of_nonneg h]
        · rw [abs_of_neg (not_le.1 h), neg_smul, smul_neg, neg_neg]
      have hq' : ∀ β : ℝ, β • q = |β| • (if 0 ≤ β then q else -q) := by
        intro β; split_ifs with h
        · rw [abs_of_nonneg h]
        · rw [abs_of_neg (not_le.1 h), neg_smul, smul_neg, neg_neg]
      have hpK : (if 0 ≤ α then p else -p) ∈ K := by split_ifs; exacts [hp, hsym p hp]
      have hqK : (if 0 ≤ β then q else -q) ∈ K := by split_ifs; exacts [hq, hsym q hq]
      rw [hp', hq']
      rcases (add_nonneg (abs_nonneg α) (abs_nonneg β)).eq_or_lt with h | h
      · rw [abs_eq_zero.1 (by linarith [abs_nonneg α, abs_nonneg β] : |α| = 0),
          abs_eq_zero.1 (by linarith [abs_nonneg α, abs_nonneg β] : |β| = 0)]
        simp [h0]
      · have hz := hK.1 hpK hqK (div_nonneg (abs_nonneg α) h.le) (div_nonneg (abs_nonneg β) h.le)
          (by field_simp)
        have := hK.1.smul_mem_of_zero_mem h0 hz ⟨h.le, hαβ⟩
        convert this using 1
        rw [smul_add, smul_smul, smul_smul]
        congr 2 <;> field_simp
    apply key
    have hs' := abs_le.1 hs
    have ht' := abs_le.1 ht
    rcases abs_cases ((s + t) / 2) with ⟨h1, -⟩ | ⟨h1, -⟩ <;>
    rcases abs_cases ((t - s) / 2) with ⟨h2, -⟩ | ⟨h2, -⟩ <;> rw [h1, h2] <;>
    linarith [hs'.1, hs'.2, ht'.1, ht'.2]

/-- A centrally symmetric hexagon containing a given compact set. -/
lemma rein_exists_hex_superset {K : Set (Fin 2 → ℝ)} (hK : IsCompact K) :
    ∃ w, IsCSHexagon w ∧ K ⊆ hexagonOf w := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  set R' := max R 1
  have hR' : 0 < R' := lt_max_of_lt_right one_pos
  set a : Fin 2 → ℝ := ![2 * R', 0]
  set b : Fin 2 → ℝ := ![0, 2 * R']
  set c : Fin 2 → ℝ := ![-(2 * R'), 2 * R']
  have hw : IsCSHexagon (rein_hex3 a b c) := by
    rw [rein_isCSHexagon_hex3_iff]
    simp only [a, b, c, det2, Matrix.cons_val_zero, Matrix.cons_val_one]
    refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  refine ⟨_, hw, fun x hx ↦ ?_⟩
  have hx' := hR hx
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (le_trans (norm_nonneg _) hx')] at hx'
  have h0 : |x 0| ≤ R' := le_trans (hx' 0) (le_max_left _ _)
  have h1 : |x 1| ≤ R' := le_trans (hx' 1) (le_max_left _ _)
  rw [abs_le] at h0 h1
  rw [rein_mem_hexagonOf_hex3 hw]
  simp only [rein_InHex, a, b, c, det2, Pi.sub_apply, Pi.neg_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- **Existence of a least-area circumscribed hexagon**, for a centrally symmetric convex disk that
is not a parallelogram (by compactness, `rein_limit_hex`). -/
lemma rein_exists_least {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K)
    (hnp : ∀ p q, 0 < det2 p q →
      (∀ x ∈ K, 0 ≤ det2 (q - p) (x - p) ∧ 0 ≤ det2 (-p - q) (x - q)) → ¬(p ∈ K ∧ q ∈ K)) :
    ∃ v, IsLeastAreaHexagon K v := by
  set As := {A | ∃ w, IsCSHexagon w ∧ K ⊆ hexagonOf w ∧ volume.real (hexagonOf w) = A}
  have hne : As.Nonempty := by
    obtain ⟨w, hw, hKw⟩ := rein_exists_hex_superset hK.2.1
    exact ⟨_, w, hw, hKw, rfl⟩
  have hbdd : BddBelow As := ⟨0, by rintro _ ⟨w, -, -, rfl⟩; exact measureReal_nonneg⟩
  set A := sInf As
  have hA : ∀ w, IsCSHexagon w → K ⊆ hexagonOf w → A ≤ volume.real (hexagonOf w) :=
    fun w hw hKw ↦ csInf_le hbdd ⟨w, hw, hKw, rfl⟩
  have hseq : ∀ n : ℕ, ∃ w, IsCSHexagon w ∧ K ⊆ hexagonOf w ∧
      volume.real (hexagonOf w) < A + 1 / (n + 1) := by
    intro n
    have hlt' : A < A + 1 / ((n : ℝ) + 1) := by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    obtain ⟨_, ⟨w, hw, hKw, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hne hlt'
    exact ⟨w, hw, hKw, hlt⟩
  choose u hu hKu hlt using hseq
  have harea : Tendsto (fun n ↦ volume.real (hexagonOf (u n))) atTop (𝓝 A) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun n ↦ hA _ (hu n) (hKu n)) (fun n ↦ (hlt n).le)
    have h1 : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have := (tendsto_const_nhds (x := A)).add h1
    simpa using this
  obtain ⟨w, hw, -⟩ := rein_limit_hex hK hnp hA u hu hKu harea
  exact ⟨w, hw⟩

/-- From an interior point one can move a little in any direction. -/
lemma rein_exists_add_smul_mem {S : Set (Fin 2 → ℝ)} {x : Fin 2 → ℝ} (hx : x ∈ interior S)
    (v : Fin 2 → ℝ) : ∃ t : ℝ, 0 < t ∧ x + t • v ∈ S := by
  have hc : Continuous fun t : ℝ ↦ x + t • v := by fun_prop
  have hev : ∀ᶠ t in nhds (0 : ℝ), x + t • v ∈ S :=
    hc.continuousAt.preimage_mem_nhds (by simpa using mem_interior_iff_mem_nhds.1 hx)
  obtain ⟨t, htS, ht⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ nhdsWithin 0 (Ioi 0))).exists
  exact ⟨t, ht, htS⟩

open scoped Pointwise

/-! ### Lattice tilings and the hexagonal lattice packing -/

/-- A convex compact tile of a lattice tiling is a fundamental domain, so its area is the
determinant of the lattice. -/
lemma rein_latticeDet_eq_of_tiling {H : Set (Fin 2 → ℝ)} (hHc : Convex ℝ H) (hHk : IsCompact H)
    {L : Submodule ℤ (Fin 2 → ℝ)} (hL : IsPlaneLattice L) (hT : IsLatticeTiling H L) :
    latticeDet L = volume.real H := by
  obtain ⟨hd, hs⟩ := hL
  have : IsZLattice ℝ L := ⟨hs⟩
  rw [latticeDet]
  apply ZLattice.covolume_eq_measure_fundamentalDomain
  have himg : ∀ g : L, g +ᵥ H = (fun x ↦ x + (g : Fin 2 → ℝ)) '' H := by
    intro g
    rw [← Set.image_vadd]
    congr 1
    funext x
    rw [Submodule.vadd_def, vadd_eq_add, add_comm]
  refine ⟨hHk.isClosed.measurableSet.nullMeasurableSet, ?_, ?_⟩
  · refine Filter.Eventually.of_forall fun x ↦ ?_
    have : x ∈ ⋃ l ∈ L, (fun y ↦ y + l) '' H := hT.1 ▸ mem_univ x
    simp only [mem_iUnion, mem_image] at this
    obtain ⟨l, hl, h, hH, rfl⟩ := this
    refine ⟨⟨-l, neg_mem hl⟩, ?_⟩
    rw [Submodule.vadd_def, vadd_eq_add]
    simpa using hH
  · intro g g' hgg'
    change volume ((g +ᵥ H) ∩ (g' +ᵥ H)) = 0
    rw [himg, himg]
    have hdisj := hT.2 g g.2 g' g'.2 (fun h ↦ hgg' (Subtype.ext h))
    have hconv : ∀ l : Fin 2 → ℝ, Convex ℝ ((fun x ↦ x + l) '' H) := fun l ↦ by
      have := hHc.translate l
      convert this using 1
      ext x; simp [add_comm]
    have hcl : ∀ l : Fin 2 → ℝ, IsClosed ((fun x ↦ x + l) '' H) := fun l ↦
      (hHk.image (continuous_id.add continuous_const)).isClosed
    refine measure_mono_null (t := frontier ((fun x ↦ x + (g : Fin 2 → ℝ)) '' H) ∪
      frontier ((fun x ↦ x + (g' : Fin 2 → ℝ)) '' H)) ?_ (measure_union_null
        ((hconv _).addHaar_frontier volume) ((hconv _).addHaar_frontier volume))
    rintro x ⟨hx1, hx2⟩
    by_cases h1 : x ∈ interior ((fun x ↦ x + (g : Fin 2 → ℝ)) '' H)
    · by_cases h2 : x ∈ interior ((fun x ↦ x + (g' : Fin 2 → ℝ)) '' H)
      · exact absurd (Set.disjoint_left.1 hdisj h1 h2) (fun h ↦ h)
      · right; rw [(hcl _).frontier_eq]; exact ⟨hx2, h2⟩
    · left; rw [(hcl _).frontier_eq]; exact ⟨hx1, h1⟩


/-- The arithmetic of the hexagonal lattice packing: a nonzero lattice vector `p (2 m₀) + q (2 m₁)`
leaves one of the three strips of the hexagon of twice the width. -/
lemma rein_lattice_arith {D1 D2 D3 : ℝ} (h1 : 0 < D1) (h2 : 0 < D2) (h3 : 0 < D3)
    (h5 : D1 < D2 + D3) (h6 : D2 < D1 + D3) {p q : ℤ}
    (hpq : ¬(p = 0 ∧ q = 0))
    (g0 : |2 * p * D1 + q * (D1 + D3 - D2)| < 2 * D1)
    (g1 : |p * (D2 + D3 - D1) + 2 * q * D2| < 2 * D2)
    (g2 : |p * (D1 - D2 - D3) + q * (D1 + D3 - D2)| < 2 * D3) : False := by
  rw [abs_lt] at g0 g1 g2
  have hp : p ≤ -1 ∨ p = 0 ∨ 1 ≤ p := by omega
  have hq : q ≤ -1 ∨ q = 0 ∨ 1 ≤ q := by omega
  rcases hp with hp | hp | hp <;> rcases hq with hq | hq | hq
  · have hp' : (p : ℝ) ≤ -1 := by exact_mod_cast hp
    have hq' : (q : ℝ) ≤ -1 := by exact_mod_cast hq
    nlinarith
  · have hp' : (p : ℝ) ≤ -1 := by exact_mod_cast hp
    rw [hq] at g0 g1 g2; push_cast at g0 g1 g2
    nlinarith
  · have hp' : (p : ℝ) ≤ -1 := by exact_mod_cast hp
    have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
    nlinarith
  · rw [hp] at g0 g1 g2; push_cast at g0 g1 g2
    have hq' : (q : ℝ) ≤ -1 := by exact_mod_cast hq
    nlinarith
  · exact hpq ⟨hp, hq⟩
  · rw [hp] at g0 g1 g2; push_cast at g0 g1 g2
    have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
    nlinarith
  · have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
    have hq' : (q : ℝ) ≤ -1 := by exact_mod_cast hq
    nlinarith
  · have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
    rw [hq] at g0 g1 g2; push_cast at g0 g1 g2
    nlinarith
  · have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
    have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
    nlinarith

/-- Interior points of a centrally symmetric hexagon lie strictly inside its three strips. -/
lemma rein_interior_strips {a b c x : Fin 2 → ℝ} (h : IsCSHexagon (rein_hex3 a b c))
    (hx : x ∈ interior (hexagonOf (rein_hex3 a b c))) :
    |det2 (a - b) x| < det2 a b ∧ |det2 (b - c) x| < det2 b c ∧ |det2 (c + a) x| < det2 a c := by
  have hc := rein_isCSHexagon_iff_hexCond.1 h
  have hs : ∀ y ∈ hexagonOf (rein_hex3 a b c), rein_strips a b c y :=
    fun y hy ↦ (rein_mem_hexagonOf_iff_strips hc).1 hy
  have key : ∀ (d w : Fin 2 → ℝ) (B : ℝ), 0 < det2 d w →
      (∀ y ∈ hexagonOf (rein_hex3 a b c), |det2 d y| ≤ B) → |det2 d x| < B := by
    intro d w B hdw hB
    obtain ⟨t1, ht1, h1⟩ := rein_exists_add_smul_mem hx w
    obtain ⟨t2, ht2, h2⟩ := rein_exists_add_smul_mem hx (-w)
    have e1 := (abs_le.1 (hB _ h1)).2
    have e2 := (abs_le.1 (hB _ h2)).1
    rw [rein_det2_add_right, rein_det2_smul_right] at e1 e2
    rw [rein_det2_neg_right] at e2
    rw [abs_lt]
    constructor <;> nlinarith [mul_pos ht1 hdw, mul_pos ht2 hdw]
  refine ⟨key (a - b) a _ ?_ fun y hy ↦ (hs y hy).1, key (b - c) b _ ?_ fun y hy ↦ (hs y hy).2.1,
    key (c + a) c _ ?_ fun y hy ↦ (hs y hy).2.2⟩
  · rw [rein_det2_sub_left, rein_det2_self, zero_sub, rein_det2_swap, neg_neg]; exact hc.hA
  · rw [rein_det2_sub_left, rein_det2_self, zero_sub, rein_det2_swap, neg_neg]; exact hc.hB
  · rw [rein_det2_add_left, rein_det2_self, zero_add]; exact hc.hC

/-- **Every centrally symmetric hexagon packs** (§2.2: "every centrally symmetric hexagon tiles"):
the translates of the hexagon by the lattice generated by twice two consecutive edge midpoints
have disjoint interiors, and the determinant of this lattice is the area of the hexagon. -/
lemma rein_hex_lattice {v : ZMod 6 → Fin 2 → ℝ} (hv : IsCSHexagon v) :
    ∃ L : Submodule ℤ (Fin 2 → ℝ), IsPlaneLattice L ∧ latticeDet L = volume.real (hexagonOf v) ∧
      IsLatticePacking (hexagonOf v) L := by
  have h := hv
  rw [rein_eq_hex3 hv] at h ⊢
  set a := v 0
  set b := v 1
  set c := v 2
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := (rein_isCSHexagon_hex3_iff a b c).1 h
  set u1 := a + b with hu1
  set u2 := b + c with hu2
  have hdet : det2 u1 u2 = det2 a b + det2 b c + det2 a c := by
    simp only [hu1, hu2, det2, Pi.add_apply]; ring
  have hD : det2 u1 u2 ≠ 0 := by rw [hdet]; linarith
  have hli : LinearIndependent ℝ ![u1, u2] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have e1 : s * det2 u1 u2 = 0 := by
      have := congrArg (fun x ↦ det2 x u2) hst
      simp only [rein_det2_add_left, rein_det2_smul_left, rein_det2_self, mul_zero,
        add_zero] at this
      rw [this]; simp [det2]
    have e2 : t * det2 u1 u2 = 0 := by
      have := congrArg (det2 u1) hst
      simp only [rein_det2_add_right, rein_det2_smul_right, rein_det2_self, mul_zero,
        zero_add] at this
      rw [this]; simp [det2]
    exact ⟨(mul_eq_zero.1 e1).resolve_right hD, (mul_eq_zero.1 e2).resolve_right hD⟩
  set B := basisOfLinearIndependentOfCardEqFinrank hli (by simp) with hB
  have hBapp : ∀ i, B i = ![u1, u2] i := fun i ↦ by
    rw [hB, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hrange : Set.range B = {u1, u2} := by
    rw [show (B : Fin 2 → Fin 2 → ℝ) = ![u1, u2] from funext hBapp, Matrix.range_cons,
      Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  set L := Submodule.span ℤ (Set.range B) with hL
  refine ⟨L, ⟨inferInstance, IsZLattice.span_top⟩, ?_, ?_⟩
  · rw [latticeDet, ZLattice.covolume_eq_det L (B.restrictScalars ℤ),
      rein_volume_real_hexagonOf_hex3 h, Matrix.det_fin_two]
    have e : ∀ i, ((B.restrictScalars ℤ i : L) : Fin 2 → ℝ) = ![u1, u2] i := fun i ↦ by
      rw [Module.Basis.restrictScalars_apply, hBapp]
    simp only [Matrix.of_apply, Function.comp_apply, e, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    have : u1 0 * u2 1 - u1 1 * u2 0 = det2 u1 u2 := rfl
    rw [this, hdet, abs_of_pos (by linarith)]
  · intro l hl l' hl' hne
    rw [Set.disjoint_left]
    intro y hy1 hy2
    rw [show (fun x : Fin 2 → ℝ ↦ x + l) = ⇑(Homeomorph.addRight l) from rfl,
      ← Homeomorph.image_interior] at hy1
    rw [show (fun x : Fin 2 → ℝ ↦ x + l') = ⇑(Homeomorph.addRight l') from rfl,
      ← Homeomorph.image_interior] at hy2
    obtain ⟨x, hx, rfl⟩ := hy1
    obtain ⟨x', hx', hxx⟩ := hy2
    simp only [Homeomorph.coe_addRight] at hxx
    have hd : l' - l ∈ L := sub_mem hl' hl
    rw [hL, hrange] at hd
    obtain ⟨p, q, hpq⟩ := Submodule.mem_span_pair.1 hd
    rw [← Int.cast_smul_eq_zsmul ℝ p, ← Int.cast_smul_eq_zsmul ℝ q] at hpq
    have hs1 := rein_interior_strips h hx
    have hs2 := rein_interior_strips h hx'
    have hx'eq : x' = x - (l' - l) := by
      rw [eq_sub_iff_add_eq, ← add_sub_assoc, hxx, add_sub_cancel_right]
    rw [hx'eq, ← hpq] at hs2
    have G : ∀ w : Fin 2 → ℝ, det2 w (x - ((p : ℝ) • u1 + (q : ℝ) • u2)) =
        det2 w x - (p * det2 w u1 + q * det2 w u2) := by
      intro w; simp only [det2, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [G, G, G] at hs2
    have v0a : det2 (a - b) u1 = 2 * det2 a b := by
      simp only [hu1, det2, Pi.sub_apply, Pi.add_apply]; ring
    have v0b : det2 (a - b) u2 = det2 a b + det2 a c - det2 b c := by
      simp only [hu2, det2, Pi.sub_apply, Pi.add_apply]; ring
    have v1a : det2 (b - c) u1 = det2 b c + det2 a c - det2 a b := by
      simp only [hu1, det2, Pi.sub_apply, Pi.add_apply]; ring
    have v1b : det2 (b - c) u2 = 2 * det2 b c := by
      simp only [hu2, det2, Pi.sub_apply, Pi.add_apply]; ring
    have v2a : det2 (c + a) u1 = det2 a b - det2 b c - det2 a c := by
      simp only [hu1, det2, Pi.add_apply]; ring
    have v2b : det2 (c + a) u2 = det2 a b + det2 a c - det2 b c := by
      simp only [hu2, det2, Pi.add_apply]; ring
    rw [v0a, v0b, v1a, v1b, v2a, v2b] at hs2
    obtain ⟨s1, s2, s3⟩ := hs1
    obtain ⟨t1, t2, t3⟩ := hs2
    rw [abs_lt] at s1 s2 s3 t1 t2 t3
    refine rein_lattice_arith h1 h2 h3 h5 h6 (p := p) (q := q) ?_ ?_ ?_ ?_
    · rintro ⟨rfl, rfl⟩
      simp only [Int.cast_zero, zero_smul, add_zero] at hpq
      exact hne (sub_eq_zero.1 hpq.symm).symm
    all_goals rw [abs_lt]; constructor <;> nlinarith


/-- A parallelogram with center `0` and half-sides `u, v` (`det(u, v) > 0`) is the image of the
square `[-1, 1]²`; its area is `4 det(u, v)`. -/
lemma rein_parallelogram_eq_image {u v : Fin 2 → ℝ} :
    {x : Fin 2 → ℝ | ∃ s t : ℝ, |s| ≤ 1 ∧ |t| ≤ 1 ∧ x = s • u + t • v} =
      Matrix.toLin' !![u 0, v 0; u 1, v 1] '' Icc (-1) 1 := by
  have hM : ∀ y : Fin 2 → ℝ, Matrix.toLin' !![u 0, v 0; u 1, v 1] y = y 0 • u + y 1 • v := by
    intro y; ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring
  ext x
  simp only [mem_ofPred_eq, mem_image, hM, mem_Icc, Pi.le_def, Fin.forall_fin_two,
    Pi.neg_apply, Pi.one_apply]
  constructor
  · rintro ⟨s, t, hs, ht, rfl⟩
    rw [abs_le] at hs ht
    exact ⟨![s, t], ⟨⟨hs.1, ht.1⟩, hs.2, ht.2⟩, by simp⟩
  · rintro ⟨y, ⟨⟨h0, h1⟩, h2, h3⟩, rfl⟩
    exact ⟨y 0, y 1, abs_le.2 ⟨h0, h2⟩, abs_le.2 ⟨h1, h3⟩, rfl⟩

lemma rein_volume_parallelogram {u v : Fin 2 → ℝ} (huv : 0 < det2 u v) :
    volume.real {x : Fin 2 → ℝ | ∃ s t : ℝ, |s| ≤ 1 ∧ |t| ≤ 1 ∧ x = s • u + t • v} =
      4 * det2 u v := by
  rw [rein_parallelogram_eq_image, measureReal_def, Measure.addHaar_image_linearMap,
    LinearMap.det_toLin', Real.volume_Icc_pi, Matrix.det_fin_two_of]
  have : u 0 * v 1 - v 0 * u 1 = det2 u v := by simp only [det2]; ring
  rw [this, abs_of_pos huv]
  simp only [Pi.one_apply, Pi.neg_apply, sub_neg_eq_add, Fin.prod_univ_two]
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul]
  simp only [nonneg_add_self_iff, zero_le_one, ENNReal.toReal_ofReal]; norm_num
  rw [ENNReal.toReal_ofReal huv.le]; ring

lemma rein_parallelogram_convex_compact (u v : Fin 2 → ℝ) :
    Convex ℝ {x : Fin 2 → ℝ | ∃ s t : ℝ, |s| ≤ 1 ∧ |t| ≤ 1 ∧ x = s • u + t • v} ∧
      IsCompact {x : Fin 2 → ℝ | ∃ s t : ℝ, |s| ≤ 1 ∧ |t| ≤ 1 ∧ x = s • u + t • v} := by
  rw [rein_parallelogram_eq_image]
  exact ⟨(convex_Icc _ _).linear_image _,
    isCompact_Icc.image (LinearMap.continuous_of_finiteDimensional _)⟩

/-- **Clipping a parallelogram** (§2.2): a centrally symmetric parallelogram containing `K` (which
is not a parallelogram) has larger area than some centrally symmetric hexagon containing `K`. -/
lemma rein_parallelogram_clip {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K)
    (hnp : ∀ p q, 0 < det2 p q →
      (∀ x ∈ K, 0 ≤ det2 (q - p) (x - p) ∧ 0 ≤ det2 (-p - q) (x - q)) → ¬(p ∈ K ∧ q ∈ K))
    {H : Set (Fin 2 → ℝ)} (hH : IsCSParallelogram H) (hKH : K ⊆ H) :
    ∃ w, IsCSHexagon w ∧ K ⊆ hexagonOf w ∧ volume.real (hexagonOf w) < volume.real H := by
  obtain ⟨u, v, huv, rfl⟩ := hH
  -- reduce to `det(u, v) > 0`
  wlog hpos : 0 < det2 u v generalizing u v
  · have hneg : 0 < det2 v u := by
      rw [rein_det2_swap]; rcases lt_or_gt_of_ne huv with h | h
      · linarith
      · exact absurd h hpos
    have heq : {x : Fin 2 → ℝ | ∃ s t : ℝ, |s| ≤ 1 ∧ |t| ≤ 1 ∧ x = s • u + t • v} =
        {x : Fin 2 → ℝ | ∃ s t : ℝ, |s| ≤ 1 ∧ |t| ≤ 1 ∧ x = s • v + t • u} := by
      ext x; simp only [mem_ofPred_eq]
      constructor <;> rintro ⟨s, t, hs, ht, rfl⟩ <;> exact ⟨t, s, ht, hs, add_comm _ _⟩
    rw [heq] at hKH ⊢
    exact this v u hneg.ne' hKH hneg
  set p := u + v
  set q := v - u
  have hpq : 0 < det2 p q := by
    have : det2 p q = 2 * det2 u v := by simp only [p, q, det2, Pi.add_apply, Pi.sub_apply]; ring
    rw [this]; linarith
  have hP : ∀ x ∈ K, 0 ≤ det2 (q - p) (x - p) ∧ 0 ≤ det2 (-p - q) (x - q) := by
    intro x hx
    obtain ⟨s, t, hs, ht, rfl⟩ := hKH hx
    rw [abs_le] at hs ht
    have e1 : det2 (q - p) (s • u + t • v - p) = 2 * (1 - t) * det2 u v := by
      simp only [p, q, det2, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    have e2 : det2 (-p - q) (s • u + t • v - q) = 2 * (s + 1) * det2 u v := by
      simp only [p, q, det2, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply,
        smul_eq_mul]; ring
    rw [e1, e2]
    exact ⟨by nlinarith, by nlinarith⟩
  obtain ⟨w, hw, hKw, hlt⟩ := rein_clip' hK hpq hP (hnp p q hpq hP)
  refine ⟨w, hw, hKw, ?_⟩
  rw [rein_volume_parallelogram hpos]
  have : det2 p q = 2 * det2 u v := by simp only [p, q, det2, Pi.add_apply, Pi.sub_apply]; ring
  linarith

lemma rein_isLatticePacking_mono {K H : Set (Fin 2 → ℝ)} (hKH : K ⊆ H)
    {L : Submodule ℤ (Fin 2 → ℝ)} (h : IsLatticePacking H L) : IsLatticePacking K L :=
  fun l hl l' hl' hne ↦ (h l hl l' hl' hne).mono (interior_mono (image_mono hKH))
    (interior_mono (image_mono hKH))

lemma rein_least_le {K : Set (Fin 2 → ℝ)} {v w : ZMod 6 → Fin 2 → ℝ}
    (hv : IsLeastAreaHexagon K v) (hw : IsCSHexagon w) (hKw : K ⊆ hexagonOf w) :
    volume.real (hexagonOf v) ≤ volume.real (hexagonOf w) :=
  ENNReal.toReal_mono (rein_isCompact_hexagonOf w).measure_lt_top.ne (hv.2.2 w hw hKw)

/-! ### Strips, parallelograms and hexagons (for Lemma 2.2.1) -/

/-- The dual basis `u, v` of two independent functionals `a, b`: `x = ⟨a, x⟩ u + ⟨b, x⟩ v`. -/
lemma tile_dual {a b : Fin 2 → ℝ} (hab : a 0 * b 1 - a 1 * b 0 ≠ 0) :
    ∃ u v : Fin 2 → ℝ, det2 u v = (a 0 * b 1 - a 1 * b 0)⁻¹ ∧
      (∀ x, det2 x v = (a 0 * b 1 - a 1 * b 0)⁻¹ * (a ⬝ᵥ x)) ∧
      (∀ x, det2 u x = (a 0 * b 1 - a 1 * b 0)⁻¹ * (b ⬝ᵥ x)) ∧
      (∀ x, x = (a ⬝ᵥ x) • u + (b ⬝ᵥ x) • v) ∧
      a ⬝ᵥ u = 1 ∧ b ⬝ᵥ u = 0 ∧ a ⬝ᵥ v = 0 ∧ b ⬝ᵥ v = 1 := by
  have hk : (a 0 * b 1 - a 1 * b 0) * (a 0 * b 1 - a 1 * b 0)⁻¹ = 1 := mul_inv_cancel₀ hab
  refine ⟨(a 0 * b 1 - a 1 * b 0)⁻¹ • ![b 1, -b 0], (a 0 * b 1 - a 1 * b 0)⁻¹ • ![-a 1, a 0],
    ?_, fun x ↦ ?_, fun x ↦ ?_, fun x ↦ ?_, ?_, ?_, ?_, ?_⟩
  · simp only [det2, Pi.smul_apply, smul_eq_mul, cons_val_zero, cons_val_one]
    linear_combination (a 0 * b 1 - a 1 * b 0)⁻¹ * hk
  · simp only [det2, Pi.smul_apply, smul_eq_mul, cons_val_zero, cons_val_one,
      PlaneLattice.dotProduct_two]
    ring
  · simp only [det2, Pi.smul_apply, smul_eq_mul, cons_val_zero, cons_val_one,
      PlaneLattice.dotProduct_two]
    ring
  · ext i
    fin_cases i <;>
      simp only [PlaneLattice.dotProduct_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        cons_val_zero, cons_val_one, Fin.zero_eta, Fin.mk_one]
    · linear_combination (-x 0) * hk
    · linear_combination (-x 1) * hk
  all_goals
    simp only [PlaneLattice.dotProduct_two, Pi.smul_apply, smul_eq_mul, cons_val_zero,
      cons_val_one]
  · linear_combination hk
  · ring
  · ring
  · linear_combination hk

/-- Two independent strips cut out a centrally symmetric parallelogram. -/
lemma tile_isCSParallelogram {a b : Fin 2 → ℝ} (hab : a 0 * b 1 - a 1 * b 0 ≠ 0) :
    IsCSParallelogram {x | |a ⬝ᵥ x| ≤ 1 ∧ |b ⬝ᵥ x| ≤ 1} := by
  obtain ⟨u, v, huv, -, -, hx, hau, hbu, hav, hbv⟩ := tile_dual hab
  refine ⟨u, v, by rw [huv]; exact inv_ne_zero hab, ?_⟩
  ext x
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨_, _, h1, h2, hx x⟩
  · rintro ⟨s, t, hs, ht, rfl⟩
    simp only [mem_ofPred_eq, dotProduct_add, dotProduct_smul, hau, hbu, hav, hbv,
      smul_eq_mul, mul_one, mul_zero, add_zero, zero_add]
    exact ⟨hs, ht⟩

/-- The centrally symmetric hexagon with vertices `u - v`, `u + k v`, `k' u + v` and their
negatives (`det(u, v) > 0`), as an intersection of three strips. -/
lemma tile_hex_core {u v : Fin 2 → ℝ} {k k' : ℝ} (hD : 0 < det2 u v) (h1 : 0 < 1 + k)
    (h2 : 0 < 1 + k') (h3 : k * k' < 1) (h4 : k' - k + k * k' < 1)
    (h5 : k - k' + k * k' < 1) :
    IsCSHexagon (rein_hex3 (u - v) (u + k • v) (k' • u + v)) ∧
      ∀ x, x ∈ hexagonOf (rein_hex3 (u - v) (u + k • v) (k' • u + v)) ↔
        (|det2 x v| ≤ det2 u v ∧ |(1 - k) * det2 x v + (1 - k') * det2 u x| ≤
          (1 - k * k') * det2 u v ∧ |det2 u x| ≤ det2 u v) := by
  set D := det2 u v
  have eAB : det2 (u - v) (u + k • v) = (1 + k) * D := by
    simp only [D, det2, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have eBC : det2 (u + k • v) (k' • u + v) = (1 - k * k') * D := by
    simp only [D, det2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have eAC : det2 (u - v) (k' • u + v) = (1 + k') * D := by
    simp only [D, det2, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hc : rein_HexCond (u - v) (u + k • v) (k' • u + v) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [eAB]; exact mul_pos h1 hD
    · rw [eBC]; exact mul_pos (sub_pos.2 h3) hD
    · rw [eAC]; exact mul_pos h2 hD
    · rw [eAC, eAB, eBC]
      nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 - (k' - k + k * k')) hD]
    · rw [eAB, eBC, eAC]
      nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 - (k - k' + k * k')) hD]
    · rw [eBC, eAB, eAC]
      nlinarith [mul_pos (mul_pos h1 h2) hD]
  refine ⟨rein_isCSHexagon_iff_hexCond.2 hc, fun x ↦ ?_⟩
  rw [rein_mem_hexagonOf_iff_strips hc, rein_strips, eAB, eBC, eAC]
  have e1 : det2 (u - v - (u + k • v)) x = (1 + k) * det2 x v := by
    simp only [det2, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have e2 : det2 (u + k • v - (k' • u + v)) x = (1 - k) * det2 x v + (1 - k') * det2 u x := by
    simp only [det2, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have e3 : det2 (k' • u + v + (u - v)) x = (1 + k') * det2 u x := by
    simp only [det2, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [e1, e2, e3, abs_mul, abs_of_pos h1, abs_mul, abs_of_pos h2,
    mul_le_mul_iff_of_pos_left h1, mul_le_mul_iff_of_pos_left h2]

/-- Three strips `|⟨a, x⟩|, |⟨b, x⟩|, |⟨α a + β b, x⟩| ≤ 1` with `det(a, b) > 0`, `α, β > 0`,
`|α - β| < 1 < α + β` cut out a centrally symmetric hexagon. -/
lemma tile_hex_of_pos {a b : Fin 2 → ℝ} (hD : 0 < a 0 * b 1 - a 1 * b 0) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (h1 : α + β > 1) (h2 : α < 1 + β) (h3 : β < 1 + α) :
    ∃ v, IsCSHexagon v ∧
      {x | |a ⬝ᵥ x| ≤ 1 ∧ |b ⬝ᵥ x| ≤ 1 ∧ |(α • a + β • b) ⬝ᵥ x| ≤ 1} = hexagonOf v := by
  obtain ⟨u, v, huv, hxv, hux, -, -, -, -, -⟩ := tile_dual hD.ne'
  set D := a 0 * b 1 - a 1 * b 0
  set k := (1 - α) / β
  set k' := (1 - β) / α
  have hk : k * β = 1 - α := div_mul_cancel₀ _ hβ.ne'
  have hk' : k' * α = 1 - β := div_mul_cancel₀ _ hα.ne'
  have g1 : 0 < 1 + k := by
    have : (1 + k) * β = β + 1 - α := by rw [add_mul, hk]; ring
    nlinarith
  have g2 : 0 < 1 + k' := by
    have : (1 + k') * α = α + 1 - β := by rw [add_mul, hk']; ring
    nlinarith
  have hkk : (k * k') * (α * β) = (1 - α) * (1 - β) := by
    rw [show k * k' * (α * β) = (k * β) * (k' * α) by ring, hk, hk']
  have hab : 0 < α * β := mul_pos hα hβ
  have g3 : k * k' < 1 := by nlinarith
  have g4 : k' - k + k * k' < 1 := by
    have : (k' - k + k * k') * (α * β) = β * (1 - β) - α * (1 - α) + (1 - α) * (1 - β) := by
      rw [show (k' - k + k * k') * (α * β) = (k' * α) * β - (k * β) * α + k * k' * (α * β) by
        ring, hk, hk', hkk]
      ring
    nlinarith
  have g5 : k - k' + k * k' < 1 := by
    have : (k - k' + k * k') * (α * β) = α * (1 - α) - β * (1 - β) + (1 - α) * (1 - β) := by
      rw [show (k - k' + k * k') * (α * β) = (k * β) * α - (k' * α) * β + k * k' * (α * β) by
        ring, hk, hk', hkk]
      ring
    nlinarith
  have hDuv : 0 < det2 u v := by rw [huv]; exact inv_pos.2 hD
  obtain ⟨hhex, hmem⟩ := tile_hex_core hDuv g1 g2 g3 g4 g5
  refine ⟨_, hhex, ?_⟩
  ext x
  rw [hmem x, huv, hxv x, hux x]
  simp only [mem_ofPred_eq, add_dotProduct, smul_dotProduct, smul_eq_mul]
  have hDi : 0 < D⁻¹ := inv_pos.2 hD
  have e : (1 - k) * (D⁻¹ * (a ⬝ᵥ x)) + (1 - k') * (D⁻¹ * (b ⬝ᵥ x)) =
      ((1 - k * k') * D⁻¹) * (α * (a ⬝ᵥ x) + β * (b ⬝ᵥ x)) := by
    have e1 : 1 - k = (1 - k * k') * α := by
      have : (1 - k) * β = (1 - k * k') * α * β := by linear_combination (-1 : ℝ) * hk + hkk
      exact mul_right_cancel₀ hβ.ne' this
    have e2 : 1 - k' = (1 - k * k') * β := by
      have : (1 - k') * α = (1 - k * k') * β * α := by
        linear_combination (-1 : ℝ) * hk' + hkk
      exact mul_right_cancel₀ hα.ne' this
    rw [e1, e2]; ring
  rw [e, abs_mul (D⁻¹), abs_mul (D⁻¹), abs_of_pos hDi, mul_le_iff_le_one_right hDi,
    mul_le_iff_le_one_right hDi, abs_mul, abs_of_pos (mul_pos (sub_pos.2 g3) hDi),
    mul_le_iff_le_one_right (mul_pos (sub_pos.2 g3) hDi)]
  tauto

/-- Three strips `|⟨a, x⟩|, |⟨b, x⟩|, |⟨α a + β b, x⟩| ≤ 1` (`a, b` independent, `α, β ≥ 0`) cut
out a centrally symmetric parallelogram or hexagon. -/
lemma tile_shape_nonneg {a b : Fin 2 → ℝ} (hD : a 0 * b 1 - a 1 * b 0 ≠ 0) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    IsCSParallelogram {x | |a ⬝ᵥ x| ≤ 1 ∧ |b ⬝ᵥ x| ≤ 1 ∧ |(α • a + β • b) ⬝ᵥ x| ≤ 1} ∨
      ∃ v, IsCSHexagon v ∧
        {x | |a ⬝ᵥ x| ≤ 1 ∧ |b ⬝ᵥ x| ≤ 1 ∧ |(α • a + β • b) ⬝ᵥ x| ≤ 1} = hexagonOf v := by
  have hc : ∀ x, (α • a + β • b) ⬝ᵥ x = α * (a ⬝ᵥ x) + β * (b ⬝ᵥ x) := fun x ↦ by
    simp only [add_dotProduct, smul_dotProduct, smul_eq_mul]
  by_cases hA : α + β ≤ 1
  · -- the third strip is implied
    left
    convert tile_isCSParallelogram hD using 1
    ext x
    simp only [mem_ofPred_eq, hc]
    constructor
    · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, h2, (abs_add_le _ _).trans ?_⟩
      rw [abs_mul, abs_mul, abs_of_nonneg hα, abs_of_nonneg hβ]
      nlinarith [abs_nonneg (a ⬝ᵥ x), abs_nonneg (b ⬝ᵥ x)]
  by_cases hB : 1 + β ≤ α
  · -- the first strip is implied
    left
    have hD' : b 0 * (α • a + β • b) 1 - b 1 * (α • a + β • b) 0 ≠ 0 := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have : b 0 * (α * a 1 + β * b 1) - b 1 * (α * a 0 + β * b 0) =
          -α * (a 0 * b 1 - a 1 * b 0) := by ring
      rw [this]; exact mul_ne_zero (by linarith) hD
    convert tile_isCSParallelogram hD' using 1
    ext x
    simp only [mem_ofPred_eq, hc]
    constructor
    · rintro ⟨-, h2, h3⟩; exact ⟨h2, h3⟩
    · rintro ⟨h2, h3⟩
      refine ⟨?_, h2, h3⟩
      have h4 : α * |a ⬝ᵥ x| ≤ 1 + β := by
        calc α * |a ⬝ᵥ x| = |α * (a ⬝ᵥ x) + β * (b ⬝ᵥ x) - β * (b ⬝ᵥ x)| := by
              rw [add_sub_cancel_right, abs_mul, abs_of_nonneg hα]
          _ ≤ |α * (a ⬝ᵥ x) + β * (b ⬝ᵥ x)| + |β * (b ⬝ᵥ x)| := abs_sub _ _
          _ ≤ 1 + β := by rw [abs_mul, abs_of_nonneg hβ]; nlinarith
      by_contra hcon
      push Not at hcon
      nlinarith
  by_cases hC : 1 + α ≤ β
  · -- the second strip is implied
    left
    have hD' : a 0 * (α • a + β • b) 1 - a 1 * (α • a + β • b) 0 ≠ 0 := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have : a 0 * (α * a 1 + β * b 1) - a 1 * (α * a 0 + β * b 0) =
          β * (a 0 * b 1 - a 1 * b 0) := by ring
      rw [this]; exact mul_ne_zero (by linarith) hD
    convert tile_isCSParallelogram hD' using 1
    ext x
    simp only [mem_ofPred_eq, hc]
    constructor
    · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      refine ⟨h1, ?_, h3⟩
      have h4 : β * |b ⬝ᵥ x| ≤ 1 + α := by
        calc β * |b ⬝ᵥ x| = |α * (a ⬝ᵥ x) + β * (b ⬝ᵥ x) - α * (a ⬝ᵥ x)| := by
              rw [add_sub_cancel_left, abs_mul, abs_of_nonneg hβ]
          _ ≤ |α * (a ⬝ᵥ x) + β * (b ⬝ᵥ x)| + |α * (a ⬝ᵥ x)| := abs_sub _ _
          _ ≤ 1 + α := by rw [abs_mul, abs_of_nonneg hα]; nlinarith
      by_contra hcon
      push Not at hcon
      nlinarith
  push Not at hA hB hC
  right
  have hα' : 0 < α := by
    rcases eq_or_lt_of_le hα with h | h
    · rw [← h] at hA hC; linarith
    · exact h
  have hβ' : 0 < β := by
    rcases eq_or_lt_of_le hβ with h | h
    · rw [← h] at hA hB; linarith
    · exact h
  rcases lt_or_gt_of_ne hD with hneg | hpos
  · have hpos' : 0 < b 0 * a 1 - b 1 * a 0 := by linarith
    obtain ⟨v, hv, he⟩ := tile_hex_of_pos hpos' hβ' hα' (by linarith) hC hB
    refine ⟨v, hv, ?_⟩
    rw [← he]
    ext x
    simp only [mem_ofPred_eq, add_comm (α • a)]
    tauto
  · exact tile_hex_of_pos hpos hα' hβ' hA hB hC

/-- Three strips `|⟨a, x⟩|, |⟨b, x⟩|, |⟨c, x⟩| ≤ 1` with `a, b` independent cut out a centrally
symmetric parallelogram or hexagon. -/
lemma tile_shape {a b : Fin 2 → ℝ} (hD : a 0 * b 1 - a 1 * b 0 ≠ 0) (c : Fin 2 → ℝ) :
    IsCSParallelogram {x | |a ⬝ᵥ x| ≤ 1 ∧ |b ⬝ᵥ x| ≤ 1 ∧ |c ⬝ᵥ x| ≤ 1} ∨
      ∃ v, IsCSHexagon v ∧ {x | |a ⬝ᵥ x| ≤ 1 ∧ |b ⬝ᵥ x| ≤ 1 ∧ |c ⬝ᵥ x| ≤ 1} = hexagonOf v := by
  have hk : (a 0 * b 1 - a 1 * b 0) * (a 0 * b 1 - a 1 * b 0)⁻¹ = 1 := mul_inv_cancel₀ hD
  set α₀ := (c 0 * b 1 - c 1 * b 0) / (a 0 * b 1 - a 1 * b 0)
  set β₀ := (a 0 * c 1 - a 1 * c 0) / (a 0 * b 1 - a 1 * b 0)
  have hc : c = α₀ • a + β₀ • b := by
    ext i
    fin_cases i <;>
      simp only [α₀, β₀, Pi.add_apply, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv,
        Fin.zero_eta, Fin.mk_one]
    · linear_combination (-c 0) * hk
    · linear_combination (-c 1) * hk
  -- normalize the signs of the coefficients
  set σ : ℝ := if 0 ≤ α₀ then 1 else -1
  set τ : ℝ := if 0 ≤ β₀ then 1 else -1
  have hσ : σ * σ = 1 := by simp only [σ]; split_ifs <;> norm_num
  have hτ : τ * τ = 1 := by simp only [τ]; split_ifs <;> norm_num
  have hσα : 0 ≤ σ * α₀ := by simp only [σ]; split_ifs with h <;> linarith
  have hτβ : 0 ≤ τ * β₀ := by simp only [τ]; split_ifs with h <;> linarith
  have hD' : (σ • a) 0 * (τ • b) 1 - (σ • a) 1 * (τ • b) 0 ≠ 0 := by
    simp only [Pi.smul_apply, smul_eq_mul]
    have : σ * a 0 * (τ * b 1) - σ * a 1 * (τ * b 0) = (σ * τ) * (a 0 * b 1 - a 1 * b 0) := by
      ring
    rw [this]
    refine mul_ne_zero ?_ hD
    intro h0; have : σ * τ * (σ * τ) = 1 := by rw [show σ * τ * (σ * τ) = (σ * σ) * (τ * τ)
      by ring, hσ, hτ, one_mul]
    rw [h0, zero_mul] at this; norm_num at this
  have hc' : c = (σ * α₀) • (σ • a) + (τ * β₀) • (τ • b) := by
    rw [hc, smul_smul, smul_smul, show σ * α₀ * σ = (σ * σ) * α₀ by ring,
      show τ * β₀ * τ = (τ * τ) * β₀ by ring, hσ, hτ, one_mul, one_mul]
  have hσa : ∀ x, |(σ • a) ⬝ᵥ x| = |a ⬝ᵥ x| := fun x ↦ by
    rw [smul_dotProduct, smul_eq_mul, abs_mul]
    simp only [σ]; split_ifs <;> simp
  have hτb : ∀ x, |(τ • b) ⬝ᵥ x| = |b ⬝ᵥ x| := fun x ↦ by
    rw [smul_dotProduct, smul_eq_mul, abs_mul]
    simp only [τ]; split_ifs <;> simp
  have hset : {x | |a ⬝ᵥ x| ≤ 1 ∧ |b ⬝ᵥ x| ≤ 1 ∧ |c ⬝ᵥ x| ≤ 1} =
      {x | |(σ • a) ⬝ᵥ x| ≤ 1 ∧ |(τ • b) ⬝ᵥ x| ≤ 1 ∧
        |((σ * α₀) • (σ • a) + (τ * β₀) • (τ • b)) ⬝ᵥ x| ≤ 1} := by
    ext x; simp only [mem_ofPred_eq, hσa, hτb, ← hc']
  rw [hset]
  exact tile_shape_nonneg hD' hσα hτβ

/-- **Blichfeldt**: a convex set whose translates by a lattice `L` pack has area at most
`det(L)`. -/
lemma rein_volume_le_latticeDet {H : Set (Fin 2 → ℝ)} (hHc : Convex ℝ H)
    {L : Submodule ℤ (Fin 2 → ℝ)} (hL : IsPlaneLattice L) (hP : IsLatticePacking H L) :
    volume.real H ≤ latticeDet L := by
  have := hL.1
  have : IsZLattice ℝ L := ⟨hL.2⟩
  exact PlaneLattice.volume_real_le_covolume L hHc hP

/-! ### Lemma 2.2.1 and Theorem 2.2.2 -/

/-- **Lemma 2.2.1** (`lem:reinhardt-tiling`), corrected. Let `K` be a centrally symmetric convex
disk and `K + L` a lattice packing of `K`. Then `K` lies in a parallelogram or a centrally
symmetric convex hexagon `H_K` (centered at the origin) whose translates `H_K + L` form a packing;
in particular `area(H_K) ≤ det(L)` (`rein_volume_le_latticeDet`).

Statement correction: the book states that the packing `K + L` "is realized by placing `K` inside
an appropriate parallelogram or centrally symmetric convex hexagon `H_K`, tiling the plane with
translates of `H_K`, then placing a copy of `K` inside each translate of `H_K`" (conclusion
`IsLatticeTiling H L` in place of `IsLatticePacking H L`). That statement is false: for `L = ℤ²`
and the parallelogram `K = {y | |2y₀ + y₁| ≤ 1, |2y₁ - y₀| ≤ 1}` (area `4/5`), the translates
`K + L` pack, and the half-lattice points `(±1/2, 0)`, `(0, ±1/2)` lie in the relative interiors
of the four edges of `K`; so every convex `H ⊇ K` whose `L`-translates pack keeps them on its
boundary with the same support lines, hence `H ⊆ K`, while `(1/2, 1/2)` is not covered by
`K + L`: no convex `H ⊇ K`, centred at the origin or not, tiles with `L`
(`lemma2_2_1_false_as_printed` in `SmoothedPolygons.Ch2.TilingCounterexample`). The corrected
statement is the classical form of Reinhardt's lemma, and it is all that Theorem 2.2.2 uses
(`area(H) ≤ det(L)` for the lattice `L` that realizes `δ_L(K)`).

Departure from the paper: the book's argument (expand `K`, separate touching translates by lines,
crop, repeat until the plane is tiled; at most six edges by an Euler characteristic count) is an
argument for the false tiling statement (in the example it is stuck at `K` from the start), so
the corrected statement is proved differently (`PlaneLattice.exists_halfLatticeFree_eq_strips`):
a maximal (Zorn's lemma) centrally symmetric convex set `C ⊇ K` with no point of `½L \ {0}` in
its interior is cut out by the strips of the support lines that are the only support line at some
point of `½L`; two such points with different lines span a lattice triangle with no other point of
`½L`, so they form a basis of `½L`, and four vectors cannot pairwise form bases. Hence `C` is
cut out by two or three strips: a parallelogram or a centrally symmetric hexagon
(`tile_isCSParallelogram`, `tile_shape`). -/
theorem lemma2_2_1 {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {L : Submodule ℤ (Fin 2 → ℝ)}
    (hL : IsPlaneLattice L) (hKL : IsLatticePacking K L) :
    ∃ H, (IsCSParallelogram H ∨ ∃ v, IsCSHexagon v ∧ H = hexagonOf v) ∧ K ⊆ H ∧
      IsLatticePacking H L := by
  have := hL.1
  have : IsZLattice ℝ L := ⟨hL.2⟩
  obtain ⟨C, hCc, -, hKC, hCs, hCL, a, b, hab, hC⟩ :=
    PlaneLattice.exists_halfLatticeFree_eq_strips L hK.1 hK.2.1 (rein_zero_mem_interior hK)
      hK.2.2.2 (PlaneLattice.halfLatticeFree_of_isPacking hK.2.2.2 hKL)
  refine ⟨C, ?_, hKC, PlaneLattice.isPacking_of_halfLatticeFree hCc hCs hCL⟩
  rcases hC with rfl | ⟨c, rfl⟩
  · exact Or.inl (tile_isCSParallelogram hab)
  · rcases tile_shape hab c with h | ⟨v, hv, he⟩
    · exact Or.inl h
    · exact Or.inr ⟨v, hv, he⟩

/-- **Theorem 2.2.2** (Reinhardt–Fejes Tóth; `thm:frac-hexagon`, equation
`eqn:reinhardt-fejes-toth`). If `K ⊂ ℝ²` is a centrally symmetric convex disk that is not a
parallelogram, then its packing density is `δ(K) = area(K)/area(H_K)`, where `H_K` is a centrally
symmetric hexagon of least area circumscribing `K`. The statement includes that such a hexagon
exists.

The proof is the book's. By Fejes Tóth (Theorem 2.1.3), `δ(K) = δ_L(K)`. Let `L` be a lattice
that realizes `δ_L(K)`. By Lemma 2.2.1 the packing `K + L` comes from a parallelogram or a
centrally symmetric hexagon `H ⊇ K` whose translates `H + L` pack, so `area(H) ≤ det(L)`
(`rein_volume_le_latticeDet`). Every centrally symmetric hexagon `H' ⊇ K` tiles
(`rein_hex_lattice`); the lattice packing of `K` that it gives has density
`area(K)/area(H') ≤ δ_L(K) = area(K)/det(L)`, so `det(L) ≤ area(H')`. Hence `H` is not a
parallelogram (its corners could be clipped to a smaller hexagon containing `K`, as the book
remarks before the theorem: `rein_parallelogram_clip`), `H` is a hexagon `H_K` of least area (so
one exists), and every least-area `H_K` has `det(L) ≤ area(H_K) ≤ area(H) ≤ det(L)`, so the
density of `K + L` is `δ(K) = area(K)/area(H_K)`.

Gap filled: the book does not justify that some lattice `L` realizes `δ_L(K)`. Twice a critical
lattice `Λ` of `K` (Mahler's compactness theorem gives one, `irr_exists_packing`) does: `K + 2Λ` is
a packing of determinant `4Δ(K)`, and `δ_L(K) = area(K)/(4Δ(K))` (`irr_glpd_eq`). -/
theorem theorem2_2_2 {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) (hpar : ¬ IsParallelogram K) :
    (∃ v, IsLeastAreaHexagon K v) ∧
      ∀ v, IsLeastAreaHexagon K v →
        greatestPackingDensity K = volume.real K / volume.real (hexagonOf v) := by
  have hnp := rein_hnp_of_not_isParallelogram hK hpar
  have hKc : IsConvexDisk K := ⟨hK.1, hK.2.1, hK.2.2.1⟩
  have hKpos := rein_volume_real_pos hK
  -- by Fejes Tóth (Theorem 2.1.3), `δ(K) = δ_L(K)`
  rw [theorem2_1_3 hK]
  -- a lattice `L` that realizes `δ_L(K)`: twice a critical lattice of `K`, of determinant
  -- `4Δ(K)`, while `δ_L(K) = area(K)/(4Δ(K))`
  obtain ⟨L, hL, hKL, hdetL⟩ := irr_exists_packing hK
  have hLpos : 0 < latticeDet L := hKpos.trans_le (rein_volume_le_latticeDet hK.1 hL hKL)
  have hδ : greatestLatticePackingDensity K = volume.real K / latticeDet L := by
    rw [irr_glpd_eq hK, hdetL]
  -- by Lemma 2.2.1, `K` lies in a parallelogram or a centrally symmetric hexagon `H` whose
  -- translates `H + L` pack (so `area(H) ≤ det(L)`)
  obtain ⟨H, hHt, hKH, hHL⟩ := lemma2_2_1 hK hL hKL
  -- every centrally symmetric hexagon `H' ⊇ K` tiles, and the lattice packing of `K` it gives
  -- has density `area(K)/area(H') ≤ δ_L(K) = area(K)/det(L)`: so `det(L) ≤ area(H')`
  have hbdd : BddAbove
      {d | ∃ L, IsPlaneLattice L ∧ IsLatticePacking K L ∧ latticePackingDensity K L = d} := by
    refine ⟨1, ?_⟩
    rintro _ ⟨L', hL', hKL', rfl⟩
    have h := rein_volume_le_latticeDet hK.1 hL' hKL'
    rw [ch2_latticePackingDensity_eq hKc hL' hKL']
    exact div_le_one_of_le₀ h (measureReal_nonneg.trans h)
  have hmin : ∀ w, IsCSHexagon w → K ⊆ hexagonOf w →
      latticeDet L ≤ volume.real (hexagonOf w) := by
    intro w hw hKw
    obtain ⟨L', hL', hdet', hpack'⟩ := rein_hex_lattice hw
    have hKL' := rein_isLatticePacking_mono hKw hpack'
    have h1 : latticePackingDensity K L' ≤ greatestLatticePackingDensity K :=
      le_csSup hbdd ⟨L', hL', hKL', rfl⟩
    rw [ch2_latticePackingDensity_eq hKc hL' hKL', hdet', hδ] at h1
    have hwpos : 0 < volume.real (hexagonOf w) := hKpos.trans_le
      (measureReal_mono hKw (rein_isCompact_hexagonOf w).measure_lt_top.ne)
    exact (div_le_div_iff_of_pos_left hKpos hwpos hLpos).1 h1
  rcases hHt with hHpar | ⟨v, hv, rfl⟩
  · -- `H` is not a parallelogram: clipping its corners gives a hexagon `H' ⊇ K` with
    -- `area(H') < area(H) ≤ det(L) ≤ area(H')`
    exfalso
    obtain ⟨w, hw, hKw, hlt⟩ := rein_parallelogram_clip hK hnp hHpar hKH
    obtain ⟨u, u', -, rfl⟩ := hHpar
    linarith [hmin w hw hKw,
      rein_volume_le_latticeDet (rein_parallelogram_convex_compact u u').1 hL hHL]
  -- the hexagon `H` has least area: `area(H) ≤ det(L) ≤ area(H')`
  have hHdet := rein_volume_le_latticeDet (convex_convexHull ℝ (range v)) hL hHL
  have hleast : IsLeastAreaHexagon K v := by
    refine ⟨hv, hKH, fun w hw hKw ↦ ?_⟩
    exact (ENNReal.toReal_le_toReal (rein_isCompact_hexagonOf v).measure_lt_top.ne
      (rein_isCompact_hexagonOf w).measure_lt_top.ne).1 (hHdet.trans (hmin w hw hKw))
  -- for every least-area `H_K`, `det(L) ≤ area(H_K) ≤ area(H) ≤ det(L)`, so the density of
  -- `K + L` is `area(K)/area(H_K)`
  refine ⟨⟨v, hleast⟩, fun v' hv' ↦ ?_⟩
  rw [hδ, le_antisymm (hmin v' hv'.1 hv'.2.1) ((rein_least_le hv' hv hKH).trans hHdet)]

/-! ### Support lines and hyperbolic arcs -/

/-- **Definition 2.2.3** (support line; `def:support`). For a convex disk `K`, a support line is a
line containing at least one point of `K` that does not separate any two points of `K`. The line
is `{x | a · x = c}` with `a ≠ 0`; it separates `x` and `y` when they lie strictly on opposite
sides, `(a · x - c)(a · y - c) < 0`. -/
def IsSupportLine (K ℓ : Set (Fin 2 → ℝ)) : Prop :=
  (∃ a : Fin 2 → ℝ, a ≠ 0 ∧ ∃ c : ℝ, ℓ = {x | a ⬝ᵥ x = c} ∧
    ∀ x ∈ K, ∀ y ∈ K, 0 ≤ (a ⬝ᵥ x - c) * (a ⬝ᵥ y - c)) ∧ (ℓ ∩ K).Nonempty

/-- The function `p ↦ det(e₁, p - v_j) · det(e₂, p - v_{j+1})`, with `e₁ = v_j - v_{j-1}` and
`e₂ = v_{j+2} - v_{j+1}`: the product of the (scaled) signed distances from `p` to the lines of
the edges `j - 1` and `j + 1` of the hexagon `v`. Its level set through the midpoint of edge `j`
is the hyperbola with these two lines as asymptotes that is tangent to edge `j` at its midpoint
(Remark 2.2.4). -/
def hexHyperbolaFun (v : ZMod 6 → Fin 2 → ℝ) (j : ZMod 6) (p : Fin 2 → ℝ) : ℝ :=
  det2 (v j - v (j - 1)) (p - v j) * det2 (v (j + 2) - v (j + 1)) (p - v (j + 1))

/-! ## Helper lemmas: changes of coordinates and support lines -/

/-! ### Linear changes of coordinates -/

/-- The linear map with `p ↦ p'`, `q ↦ q'` (when `det(p, q) ≠ 0`), by Cramer's rule. -/
noncomputable def rein_frameLin (p q p' q' : Fin 2 → ℝ) : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun x := (det2 x q / det2 p q) • p' + (det2 p x / det2 p q) • q'
  map_add' x y := by ext i; simp only [det2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  map_smul' r x := by
    ext i; simp only [det2, Pi.add_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

lemma rein_frameLin_apply (p q p' q' x : Fin 2 → ℝ) :
    rein_frameLin p q p' q' x = (det2 x q / det2 p q) • p' + (det2 p x / det2 p q) • q' := rfl

lemma rein_frameLin_left {p q : Fin 2 → ℝ} (h : det2 p q ≠ 0) (p' q' : Fin 2 → ℝ) :
    rein_frameLin p q p' q' p = p' := by
  rw [rein_frameLin_apply, div_self h, rein_det2_self, zero_div, one_smul, zero_smul, add_zero]

lemma rein_frameLin_right {p q : Fin 2 → ℝ} (h : det2 p q ≠ 0) (p' q' : Fin 2 → ℝ) :
    rein_frameLin p q p' q' q = q' := by
  rw [rein_frameLin_apply, div_self h, rein_det2_self, zero_div, one_smul, zero_smul, zero_add]

lemma rein_det2_frameLin {p q : Fin 2 → ℝ} (h : det2 p q ≠ 0) (p' q' x y : Fin 2 → ℝ) :
    det2 (rein_frameLin p q p' q' x) (rein_frameLin p q p' q' y) =
      det2 p' q' / det2 p q * det2 x y := by
  simp only [rein_frameLin_apply]
  have e1 : ∀ α β γ δ : ℝ, det2 (α • p' + β • q') (γ • p' + δ • q') =
      (α * δ - β * γ) * det2 p' q' := by
    intro α β γ δ; simp only [det2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have e2 : det2 x q * det2 p y - det2 p x * det2 y q = det2 p q * det2 x y := by
    simp only [det2]; ring
  rw [e1]
  have e3 : det2 x q / det2 p q * (det2 p y / det2 p q) -
      det2 p x / det2 p q * (det2 y q / det2 p q) = det2 x y / det2 p q := by
    rw [div_mul_div_comm, div_mul_div_comm, ← sub_div, e2]
    field_simp
  rw [e3]
  ring

lemma rein_frameLin_comp {p q p' q' : Fin 2 → ℝ} (h : det2 p q ≠ 0) (h' : det2 p' q' ≠ 0) :
    (rein_frameLin p' q' p q).comp (rein_frameLin p q p' q') = LinearMap.id := by
  apply LinearMap.ext
  intro x
  ext i
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  rw [rein_frameLin_apply (p := p'), rein_frameLin_apply]
  have e1 : det2 ((det2 x q / det2 p q) • p' + (det2 p x / det2 p q) • q') q' =
      det2 x q / det2 p q * det2 p' q' := by
    simp only [det2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have e2 : det2 p' ((det2 x q / det2 p q) • p' + (det2 p x / det2 p q) • q') =
      det2 p x / det2 p q * det2 p' q' := by
    simp only [det2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [e1, e2]
  have hcr := congrFun (rein_cramer p q x) i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hcr ⊢
  field_simp
  linear_combination (-1 : ℝ) * hcr

/-- The linear automorphism of the plane with `p ↦ p'` and `q ↦ q'`. -/
noncomputable def rein_frame (p q p' q' : Fin 2 → ℝ) (h : det2 p q ≠ 0) (h' : det2 p' q' ≠ 0) :
    (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
    (LinearEquiv.ofLinearMap (rein_frameLin p q p' q') (rein_frameLin p' q' p q)
      (rein_frameLin_comp h' h) (rein_frameLin_comp h h'))

lemma rein_frame_apply {p q p' q' : Fin 2 → ℝ} (h : det2 p q ≠ 0) (h' : det2 p' q' ≠ 0)
    (x : Fin 2 → ℝ) : rein_frame p q p' q' h h' x = rein_frameLin p q p' q' x := rfl

/-- `e` is an orientation-preserving linear automorphism multiplying areas by `d`. -/
structure rein_PosLin (e : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ)) (d : ℝ) : Prop where
  pos : 0 < d
  det : ∀ x y, det2 (e x) (e y) = d * det2 x y

lemma rein_posLin_frame {p q p' q' : Fin 2 → ℝ} (h : 0 < det2 p q) (h' : 0 < det2 p' q') :
    rein_PosLin (rein_frame p q p' q' h.ne' h'.ne') (det2 p' q' / det2 p q) :=
  ⟨div_pos h' h, fun x y ↦ rein_det2_frameLin h.ne' p' q' x y⟩

lemma rein_PosLin.symm {e : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ)} {d : ℝ} (he : rein_PosLin e d) :
    rein_PosLin e.symm d⁻¹ := by
  refine ⟨inv_pos.2 he.pos, fun x y ↦ ?_⟩
  have := he.det (e.symm x) (e.symm y)
  simp only [ContinuousLinearEquiv.apply_symm_apply] at this
  rw [this, ← mul_assoc, inv_mul_cancel₀ he.pos.ne', one_mul]

section transport

variable {e : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ)} {d : ℝ}

lemma rein_PosLin.linearMap_det (he : rein_PosLin e d) :
    LinearMap.det (e : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) = d := by
  rw [← LinearMap.det_toMatrix', Matrix.det_fin_two]
  have := he.det (Pi.single 0 1) (Pi.single 1 1)
  simp only [det2, Pi.single_apply] at this
  simp only [LinearMap.toMatrix'_apply]
  simp only [Fin.isValue, ↓reduceIte, mul_one, one_ne_zero, zero_ne_one, mul_zero,
    sub_zero] at this
  change e (Pi.single 0 1) 0 * e (Pi.single 1 1) 1 - e (Pi.single 1 1) 0 * e (Pi.single 0 1) 1 = d
  linarith

lemma rein_PosLin.volume_image (he : rein_PosLin e d) (S : Set (Fin 2 → ℝ)) :
    volume (e '' S) = ENNReal.ofReal d * volume S := by
  have := Measure.addHaar_image_linearMap volume (e : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) S
  rw [he.linearMap_det, abs_of_pos he.pos] at this
  simpa using this

lemma rein_isCSHexagon_comp (he : rein_PosLin e d) {v : ZMod 6 → Fin 2 → ℝ}
    (hv : IsCSHexagon v) : IsCSHexagon (fun k ↦ e (v k)) := by
  intro j
  obtain ⟨h1, h2, h3⟩ := hv j
  refine ⟨by simp [h1], ?_, ?_⟩
  · rw [he.det]; exact mul_pos he.pos h2
  · rw [← map_sub, ← map_sub, he.det]; exact mul_pos he.pos h3

lemma rein_hexagonOf_comp (v : ZMod 6 → Fin 2 → ℝ) :
    hexagonOf (fun k ↦ e (v k)) = e '' hexagonOf v := by
  have h := LinearMap.image_convexHull (e : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) (range v)
  have h2 : (e : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) '' range v = range fun k ↦ e (v k) := by
    rw [← range_comp]; rfl
  rw [h2] at h
  exact h.symm

lemma rein_hexMidpoint_comp (v : ZMod 6 → Fin 2 → ℝ) (j : ZMod 6) :
    hexMidpoint (fun k ↦ e (v k)) j = e (hexMidpoint v j) := by
  simp only [hexMidpoint, midpoint_eq_smul_add, map_smul, map_add]

lemma rein_image_symm_image (S : Set (Fin 2 → ℝ)) : e.symm '' (e '' S) = S := by
  rw [image_image]; simp

lemma rein_isLeastAreaHexagon_comp (he : rein_PosLin e d) {K : Set (Fin 2 → ℝ)}
    {v : ZMod 6 → Fin 2 → ℝ} (hv : IsLeastAreaHexagon K v) :
    IsLeastAreaHexagon (e '' K) (fun k ↦ e (v k)) := by
  refine ⟨rein_isCSHexagon_comp he hv.1, ?_, fun w hw hKw ↦ ?_⟩
  · rw [rein_hexagonOf_comp]; exact image_mono hv.2.1
  · have hw' := rein_isCSHexagon_comp he.symm hw
    have hKw' : K ⊆ hexagonOf (fun k ↦ e.symm (w k)) := by
      rw [rein_hexagonOf_comp]
      intro x hx
      exact ⟨e x, hKw (mem_image_of_mem e hx), by simp⟩
    have := hv.2.2 _ hw' hKw'
    rw [rein_hexagonOf_comp, he.volume_image]
    rw [rein_hexagonOf_comp, he.symm.volume_image] at this
    calc ENNReal.ofReal d * volume (hexagonOf v)
        ≤ ENNReal.ofReal d * (ENNReal.ofReal d⁻¹ * volume (hexagonOf w)) := by gcongr
      _ = volume (hexagonOf w) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul he.pos.le, mul_inv_cancel₀ he.pos.ne',
          ENNReal.ofReal_one, one_mul]

lemma rein_isCCSDisk_image {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) : IsCCSDisk (e '' K) := by
  obtain ⟨h1, h2, h3, h4⟩ := hK
  refine ⟨h1.linear_image (e : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)), h2.image e.continuous, ?_, ?_⟩
  · rw [show interior (e '' K) = e '' interior K from (e.toHomeomorph.image_interior K).symm]
    exact h3.image _
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨-x, h4 x hx, by simp⟩

lemma rein_frontier_image (K : Set (Fin 2 → ℝ)) : frontier (e '' K) = e '' frontier K :=
  (e.toHomeomorph.image_frontier K).symm

lemma rein_interior_image (K : Set (Fin 2 → ℝ)) : interior (e '' K) = e '' interior K :=
  (e.toHomeomorph.image_interior K).symm

/-- The image of a support line under a linear automorphism is a support line of the image. -/
lemma rein_isSupportLine_image {K ℓ : Set (Fin 2 → ℝ)} (h : IsSupportLine K ℓ) :
    IsSupportLine (e '' K) (e '' ℓ) := by
  obtain ⟨⟨a, ha, c, rfl, hsep⟩, ⟨x, hxℓ, hxK⟩⟩ := h
  set a' : Fin 2 → ℝ := fun i ↦ a ⬝ᵥ e.symm (Pi.single i 1) with ha'
  have key : ∀ y, a ⬝ᵥ e.symm y = a' ⬝ᵥ y := by
    intro y
    have hy : y = y 0 • Pi.single 0 1 + y 1 • Pi.single 1 1 := by
      ext i; fin_cases i <;> simp
    conv_lhs => rw [hy]
    simp only [map_add, map_smul, ha', dotProduct, Fin.sum_univ_two, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  refine ⟨⟨a', ?_, c, ?_, ?_⟩, ⟨e x, mem_image_of_mem e hxℓ, mem_image_of_mem e hxK⟩⟩
  · intro h0
    apply ha
    have : ∀ y, a ⬝ᵥ e.symm y = 0 := fun y ↦ by rw [key, h0, zero_dotProduct]
    ext i
    have := this (e (Pi.single i 1))
    simp only [ContinuousLinearEquiv.symm_apply_apply] at this
    simpa [dotProduct, Pi.single_apply] using this
  · ext y
    simp only [mem_image, mem_ofPred_eq]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [← key]; simpa using hz
    · intro hy
      exact ⟨e.symm y, by rw [key]; exact hy, by simp⟩
  · rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    rw [← key, ← key]
    simpa using hsep y hy z hz

end transport


/-! ### Support lines -/

/-- A support line in normal form: `ℓ = {a · x = c}`, `a ≠ 0`, with `K` on the side `a · x ≤ c`. -/
lemma rein_supportLine_normal {K ℓ : Set (Fin 2 → ℝ)} (h : IsSupportLine K ℓ) :
    ∃ a : Fin 2 → ℝ, a ≠ 0 ∧ ∃ c, ℓ = {x | a ⬝ᵥ x = c} ∧ ∀ x ∈ K, a ⬝ᵥ x ≤ c := by
  obtain ⟨⟨a, ha, c, rfl, hsep⟩, -⟩ := h
  by_cases hpos : ∃ x ∈ K, c < a ⬝ᵥ x
  · obtain ⟨x, hx, hxc⟩ := hpos
    refine ⟨-a, neg_ne_zero.2 ha, -c, ?_, fun y hy ↦ ?_⟩
    · ext z
      simp only [vec2_dotProduct, Fin.isValue, mem_ofPred_eq, neg_dotProduct, neg_add_rev]
      constructor <;> intro h <;> linarith
    · have := hsep x hx y hy
      rw [neg_dotProduct]
      nlinarith
  · push Not at hpos
    exact ⟨a, ha, c, rfl, hpos⟩

lemma rein_isSupportLine_of {K : Set (Fin 2 → ℝ)} {a : Fin 2 → ℝ} (ha : a ≠ 0) {c : ℝ}
    (hK : ∀ x ∈ K, a ⬝ᵥ x ≤ c) {u : Fin 2 → ℝ} (hu : u ∈ K) (huc : a ⬝ᵥ u = c) :
    IsSupportLine K {x | a ⬝ᵥ x = c} := by
  refine ⟨⟨a, ha, c, rfl, fun x hx y hy ↦ ?_⟩, ⟨u, huc, hu⟩⟩
  have := hK x hx
  have := hK y hy
  nlinarith

/-- If a support line contains a point of the open segment between two points of `K`, it contains
these two points. -/
lemma rein_supportLine_openSegment {K ℓ : Set (Fin 2 → ℝ)} (h : IsSupportLine K ℓ)
    {x y z : Fin 2 → ℝ} (hx : x ∈ K) (hy : y ∈ K) (hz : z ∈ ℓ) (hzs : z ∈ openSegment ℝ x y) :
    x ∈ ℓ ∧ y ∈ ℓ := by
  obtain ⟨a, -, c, rfl, hK⟩ := rein_supportLine_normal h
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hzs
  have h1 := hK x hx
  have h2 := hK y hy
  simp only [mem_ofPred_eq, dotProduct_add, dotProduct_smul, smul_eq_mul] at hz ⊢
  have e1 : s * (c - a ⬝ᵥ x) + t * (c - a ⬝ᵥ y) = 0 := by linear_combination c * hst - hz
  have p1 := mul_nonneg hs.le (sub_nonneg.2 h1)
  have p2 := mul_nonneg ht.le (sub_nonneg.2 h2)
  have q1 : s * (c - a ⬝ᵥ x) = 0 := by linarith
  have q2 : t * (c - a ⬝ᵥ y) = 0 := by linarith
  rcases mul_eq_zero.1 q1 with h | h
  · exact absurd h hs.ne'
  rcases mul_eq_zero.1 q2 with h' | h'
  · exact absurd h' ht.ne'
  constructor <;> linarith

/-- A support line contains the line through any two of its points. -/
lemma rein_supportLine_lineMap {K ℓ : Set (Fin 2 → ℝ)} (h : IsSupportLine K ℓ)
    {p q : Fin 2 → ℝ} (hp : p ∈ ℓ) (hq : q ∈ ℓ) (t : ℝ) : p + t • (q - p) ∈ ℓ := by
  obtain ⟨⟨a, -, c, rfl, -⟩, -⟩ := h
  simp only [mem_ofPred_eq, dotProduct_add, dotProduct_smul, dotProduct_sub, smul_eq_mul] at hp hq ⊢
  rw [hp, hq]; ring

/-- A point of `K` on a support line is a boundary point. -/
lemma rein_mem_frontier_of_supportLine {K ℓ : Set (Fin 2 → ℝ)} (hK : IsClosed K)
    (h : IsSupportLine K ℓ) {x : Fin 2 → ℝ} (hx : x ∈ K) (hxℓ : x ∈ ℓ) : x ∈ frontier K := by
  obtain ⟨a, ha, c, rfl, hKa⟩ := rein_supportLine_normal h
  rw [hK.frontier_eq]
  refine ⟨hx, fun hi ↦ ?_⟩
  have hc : Continuous fun t : ℝ ↦ x + t • a := by fun_prop
  have hev : ∀ᶠ t in nhds (0 : ℝ), x + t • a ∈ K :=
    hc.continuousAt.preimage_mem_nhds (by simpa using mem_interior_iff_mem_nhds.1 hi)
  obtain ⟨t, htK, ht⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ nhdsWithin 0 (Ioi 0))).exists
  have h1 := hKa _ htK
  simp only [mem_ofPred_eq] at hxℓ
  rw [dotProduct_add, dotProduct_smul, hxℓ, smul_eq_mul] at h1
  have h2 : 0 < a ⬝ᵥ a := by
    simp only [dotProduct, Fin.sum_univ_two]
    by_contra hneg
    apply ha
    ext i; fin_cases i <;> simp <;> nlinarith [sq_nonneg (a 0), sq_nonneg (a 1)]
  have : (0 : ℝ) < t := ht
  nlinarith

/-- `det(p, x)` as a dot product. -/
lemma rein_det2_eq_dotProduct (p x : Fin 2 → ℝ) : det2 p x = ![-p 1, p 0] ⬝ᵥ x := by
  simp [det2, dotProduct, Fin.sum_univ_two]; ring

/-- A line `{x | det(p, x) = c}`. -/
lemma rein_det2_line_eq (p : Fin 2 → ℝ) (c : ℝ) :
    {x : Fin 2 → ℝ | det2 p x = c} = {x | ![-p 1, p 0] ⬝ᵥ x = c} := by
  ext x; simp [rein_det2_eq_dotProduct]

lemma rein_ne_zero_of_det2 {p : Fin 2 → ℝ} (hp : p ≠ 0) : (![-p 1, p 0] : Fin 2 → ℝ) ≠ 0 := by
  intro h
  apply hp
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp at h0 h1
  ext i; fin_cases i <;> simp [h0, h1]

/-! ### The consequences of Lemma 2.2.5 -/

/-- The properties of a worst disk given by Lemma 2.2.5: `K` is a centrally symmetric convex disk
with a unique support line at each boundary point, and each such support line contains an edge of
a critical hexagon. -/
def rein_Good (K : Set (Fin 2 → ℝ)) : Prop :=
  IsCCSDisk K ∧ (∀ u ∈ frontier K, ∃! ℓ, IsSupportLine K ℓ ∧ u ∈ ℓ) ∧
    ∀ u ∈ frontier K, ∀ ℓ, IsSupportLine K ℓ → u ∈ ℓ →
      ∃ v, IsLeastAreaHexagon K v ∧ ∃ j, segment ℝ (v j) (v (j + 1)) ⊆ ℓ

lemma rein_good_image {e : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ)} {d : ℝ} (he : rein_PosLin e d)
    {K : Set (Fin 2 → ℝ)} (hK : rein_Good K) : rein_Good (e '' K) := by
  obtain ⟨hK, hU, hE⟩ := hK
  have hsl : ∀ ℓ, IsSupportLine (e '' K) ℓ → IsSupportLine K (e.symm '' ℓ) := by
    intro ℓ hℓ
    have := rein_isSupportLine_image (e := e.symm) hℓ
    rwa [rein_image_symm_image] at this
  have himg : ∀ ℓ : Set (Fin 2 → ℝ), e '' (e.symm '' ℓ) = ℓ := by
    intro ℓ; rw [image_image]; simp
  refine ⟨rein_isCCSDisk_image hK, ?_, ?_⟩
  · intro u hu
    rw [rein_frontier_image] at hu
    obtain ⟨u₀, hu₀, rfl⟩ := hu
    obtain ⟨ℓ₀, ⟨hℓ₀, huℓ₀⟩, huniq⟩ := hU u₀ hu₀
    refine ⟨e '' ℓ₀, ⟨rein_isSupportLine_image hℓ₀, mem_image_of_mem e huℓ₀⟩, ?_⟩
    rintro ℓ ⟨hℓ, huℓ⟩
    have := huniq (e.symm '' ℓ) ⟨hsl ℓ hℓ, ⟨e u₀, huℓ, by simp⟩⟩
    rw [← this, himg]
  · intro u hu ℓ hℓ huℓ
    rw [rein_frontier_image] at hu
    obtain ⟨u₀, hu₀, rfl⟩ := hu
    obtain ⟨v, hv, j, hj⟩ := hE u₀ hu₀ _ (hsl ℓ hℓ) ⟨e u₀, huℓ, by simp⟩
    refine ⟨fun k ↦ e (v k), rein_isLeastAreaHexagon_comp he hv, j, ?_⟩
    have := image_segment ℝ (e : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)).toAffineMap (v j) (v (j + 1))
    have hseg : segment ℝ (e (v j)) (e (v (j + 1))) = e '' segment ℝ (v j) (v (j + 1)) :=
      this.symm
    change segment ℝ (e (v j)) (e (v (j + 1))) ⊆ ℓ
    rw [hseg, ← himg ℓ]
    exact image_mono hj

/-! ### Reindexing a hexagon -/

lemma rein_isCSHexagon_shift {v : ZMod 6 → Fin 2 → ℝ} (hv : IsCSHexagon v) (j : ZMod 6) :
    IsCSHexagon fun k ↦ v (k + j) := by
  intro k
  obtain ⟨h1, h2, h3⟩ := hv (k + j)
  refine ⟨?_, ?_, ?_⟩
  · simp only; rw [show k + 3 + j = k + j + 3 by ring]; exact h1
  · simp only; rw [show k + 1 + j = k + j + 1 by ring]; exact h2
  · simp only
    rw [show k + 1 + j = k + j + 1 by ring, show k + 2 + j = k + j + 2 by ring]
    exact h3

lemma rein_hexagonOf_shift (v : ZMod 6 → Fin 2 → ℝ) (j : ZMod 6) :
    hexagonOf (fun k ↦ v (k + j)) = hexagonOf v := by
  have hrange : range (fun k ↦ v (k + j)) = range v := (Equiv.addRight j).surjective.range_comp v
  simp only [hexagonOf, hrange]

lemma rein_isLeastAreaHexagon_shift {K : Set (Fin 2 → ℝ)} {v : ZMod 6 → Fin 2 → ℝ}
    (hv : IsLeastAreaHexagon K v) (j : ZMod 6) : IsLeastAreaHexagon K fun k ↦ v (k + j) := by
  refine ⟨rein_isCSHexagon_shift hv.1 j, ?_, fun w hw hKw ↦ ?_⟩
  · rw [rein_hexagonOf_shift]; exact hv.2.1
  · rw [rein_hexagonOf_shift]; exact hv.2.2 w hw hKw

lemma rein_hexMidpoint_shift (v : ZMod 6 → Fin 2 → ℝ) (j k : ZMod 6) :
    hexMidpoint (fun i ↦ v (i + j)) k = hexMidpoint v (k + j) := by
  simp only [hexMidpoint]
  rw [show k + 1 + j = k + j + 1 by ring]

/-! ### Edge midpoints -/

lemma rein_hexMidpoint_add_three {v : ZMod 6 → Fin 2 → ℝ} (hv : IsCSHexagon v) (j : ZMod 6) :
    hexMidpoint v (j + 3) = -hexMidpoint v j := by
  have h1 := (hv j).1
  have h2 := (hv (j + 1)).1
  simp only [hexMidpoint]
  rw [show j + 3 + 1 = j + 1 + 3 by ring, h1, h2, midpoint_eq_smul_add, midpoint_eq_smul_add,
    ← neg_add, smul_neg]

lemma rein_hexMidpoint_succ {v : ZMod 6 → Fin 2 → ℝ} (hv : IsCSHexagon v) (j : ZMod 6) :
    hexMidpoint v (j + 1) = hexMidpoint v j + hexMidpoint v (j + 2) := by
  have h1 := (hv j).1
  simp only [hexMidpoint]
  rw [show j + 2 + 1 = j + 3 by ring, show j + 1 + 1 = j + 2 by ring, h1, midpoint_eq_smul_add,
    midpoint_eq_smul_add, midpoint_eq_smul_add, ← smul_add]
  congr 1
  abel

lemma rein_det2_hexMidpoint {v : ZMod 6 → Fin 2 → ℝ} (hv : IsCSHexagon v) (j : ZMod 6) :
    det2 (hexMidpoint v j) (hexMidpoint v (j + 1)) = det2 (hexMidpoint v 0) (hexMidpoint v 1) := by
  have step : ∀ i, det2 (hexMidpoint v (i + 1)) (hexMidpoint v (i + 1 + 1)) =
      det2 (hexMidpoint v i) (hexMidpoint v (i + 1)) := by
    intro i
    have e1 := rein_hexMidpoint_succ hv i
    have e2 : hexMidpoint v (i + 1 + 1) = hexMidpoint v (i + 1) - hexMidpoint v i := by
      rw [show i + 1 + 1 = i + 2 by ring, e1]; abel
    rw [e2, rein_det2_sub_right, rein_det2_self, zero_sub, rein_det2_swap, neg_neg]
  have s1 := step 0
  have s2 := step 1
  have s3 := step 2
  have s4 := step 3
  have s5 := step 4
  rein_z6
  rcases rein_zmod6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;> rein_z6 <;>
    simp only [s1, s2, s3, s4, s5]

lemma rein_volume_hexagonOf {v : ZMod 6 → Fin 2 → ℝ} (hv : IsCSHexagon v) :
    volume (hexagonOf v) = ENNReal.ofReal (4 * det2 (hexMidpoint v 0) (hexMidpoint v 1)) := by
  have h := hv
  rw [rein_eq_hex3 hv] at h ⊢
  rw [rein_volume_hexagonOf_hex3 h]
  congr 1
  simp only [hexMidpoint, midpoint_eq_smul_add, rein_hex3_zero, rein_hex3_one,
    show (0 : ZMod 6) + 1 = 1 from rfl, show (1 : ZMod 6) + 1 = 2 from rfl, rein_hex3_two]
  simp only [det2, Pi.smul_apply, Pi.add_apply, smul_eq_mul, invOf_eq_inv]
  ring

lemma rein_det2_hexMidpoint_pos {v : ZMod 6 → Fin 2 → ℝ} (hv : IsCSHexagon v) :
    0 < det2 (hexMidpoint v 0) (hexMidpoint v 1) := by
  have h := hv
  rw [rein_eq_hex3 hv] at h ⊢
  obtain ⟨h1, h2, h3, -⟩ := (rein_isCSHexagon_hex3_iff _ _ _).1 h
  simp only [hexMidpoint, midpoint_eq_smul_add, rein_hex3_zero, rein_hex3_one,
    show (0 : ZMod 6) + 1 = 1 from rfl, show (1 : ZMod 6) + 1 = 2 from rfl, rein_hex3_two]
  simp only [det2, Pi.smul_apply, Pi.add_apply, smul_eq_mul, invOf_eq_inv] at h1 h2 h3 ⊢
  nlinarith

/-- Two least-area hexagons of `K` have the same value of `det(m₀, m₁)`. -/
lemma rein_det2_hexMidpoint_eq {K : Set (Fin 2 → ℝ)} {v w : ZMod 6 → Fin 2 → ℝ}
    (hv : IsLeastAreaHexagon K v) (hw : IsLeastAreaHexagon K w) :
    det2 (hexMidpoint v 0) (hexMidpoint v 1) = det2 (hexMidpoint w 0) (hexMidpoint w 1) := by
  have h1 := hv.2.2 w hw.1 hw.2.1
  have h2 := hw.2.2 v hv.1 hv.2.1
  rw [rein_volume_hexagonOf hv.1, rein_volume_hexagonOf hw.1] at h1 h2
  have p1 := rein_det2_hexMidpoint_pos hv.1
  have p2 := rein_det2_hexMidpoint_pos hw.1
  rw [ENNReal.ofReal_le_ofReal_iff (by linarith)] at h1 h2
  linarith

lemma rein_frontier_subset {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) : frontier K ⊆ K :=
  hK.2.1.isClosed.frontier_subset

/-! ### Remark 2.2.4 -/

section remark

variable {a b c : Fin 2 → ℝ} {D A1 A2 : ℝ}

/-- The affine coordinates `ξ, η` with respect to the apex `O` of the triangle cut off by the edge
`[a, b]` (the intersection of the lines of the edges `[-c, a]` and `[b, c]`) and the vertices
`a, b`: `z = O + ξ(z) (a - O) + η(z) (b - O)`. -/
lemma rein_rmk_rep (z : Fin 2 → ℝ) (hD : D ≠ 0) (hA1 : A1 ≠ 0) (hA2 : A2 ≠ 0)
    (eD : D = det2 b c + det2 a c - det2 a b) (eA1 : A1 = det2 a b - det2 b c + det2 a c)
    (eA2 : A2 = det2 a b + det2 b c - det2 a c) :
    z = (a + (A2 / D) • (a + c)) + (det2 (c - b) (z - b) / A2) • (a - (a + (A2 / D) • (a + c))) +
      (det2 (a + c) (z - a) / A1) • (b - (a + (A2 / D) • (a + c))) := by
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  simp only [det2, Pi.add_apply, Pi.sub_apply] at eD eA1 eA2 ⊢
  subst eD eA1 eA2
  fin_cases i <;> simp <;> ring

variable (x y : ℝ)

lemma rein_rmk_e1 (hD : D ≠ 0) (eD : D = det2 b c + det2 a c - det2 a b)
    (eA1 : A1 = det2 a b - det2 b c + det2 a c) (eA2 : A2 = det2 a b + det2 b c - det2 a c) :
    det2 (a + ((1 - x) * A2 / D) • (a + c)) (b + ((1 - y) * A1 / D) • (b - c)) * D =
      x * det2 a c * A2 + y * det2 b c * A1 - x * y * A1 * A2 := by
  simp only [det2, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at eD eA1 eA2 ⊢
  field_simp
  subst eD eA1 eA2
  ring

lemma rein_rmk_e2 (hD : D ≠ 0) (eD : D = det2 b c + det2 a c - det2 a b)
    (eA1 : A1 = det2 a b - det2 b c + det2 a c) :
    det2 (b + ((1 - y) * A1 / D) • (b - c)) c * D = det2 b c * (2 * det2 a c - y * A1) := by
  rw [rein_det2_add_left, rein_det2_smul_left, rein_det2_sub_left, rein_det2_self, sub_zero]
  field_simp
  subst eD eA1
  ring

lemma rein_rmk_e3 (hD : D ≠ 0) (eD : D = det2 b c + det2 a c - det2 a b)
    (eA2 : A2 = det2 a b + det2 b c - det2 a c) :
    det2 (a + ((1 - x) * A2 / D) • (a + c)) c * D = det2 a c * (2 * det2 b c - x * A2) := by
  rw [rein_det2_add_left, rein_det2_smul_left, rein_det2_add_left, rein_det2_self, add_zero]
  field_simp
  subst eD eA2
  ring

lemma rein_rmk_eE0 (z : Fin 2 → ℝ) (hD : D ≠ 0) (hA1 : A1 ≠ 0) (hA2 : A2 ≠ 0)
    (eD : D = det2 b c + det2 a c - det2 a b)
    (eA1 : A1 = det2 a b - det2 b c + det2 a c) (eA2 : A2 = det2 a b + det2 b c - det2 a c) :
    det2 ((b + ((1 - y) * A1 / D) • (b - c)) - (a + ((1 - x) * A2 / D) • (a + c)))
      (z - (a + ((1 - x) * A2 / D) • (a + c))) * D =
      A1 * A2 * (y * (det2 (c - b) (z - b) / A2) + x * (det2 (a + c) (z - a) / A1) - x * y) := by
  simp only [det2, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at eD eA1 eA2 ⊢
  field_simp
  subst eD eA1 eA2
  ring

lemma rein_rmk_eE1 (z : Fin 2 → ℝ) (hD : D ≠ 0) (eD : D = det2 b c + det2 a c - det2 a b)
    (eA1 : A1 = det2 a b - det2 b c + det2 a c) :
    det2 (c - (b + ((1 - y) * A1 / D) • (b - c))) (z - (b + ((1 - y) * A1 / D) • (b - c))) * D =
      (2 * det2 a c - y * A1) * det2 (c - b) (z - b) := by
  simp only [det2, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at eD eA1 ⊢
  field_simp
  subst eD eA1
  ring

lemma rein_rmk_eE2 (z : Fin 2 → ℝ) (hD : D ≠ 0) (eD : D = det2 b c + det2 a c - det2 a b)
    (eA2 : A2 = det2 a b + det2 b c - det2 a c) :
    det2 (-(a + ((1 - x) * A2 / D) • (a + c)) - c) (z - c) * D =
      (2 * det2 b c - x * A2) * det2 (-a - c) (z - c) := by
  simp only [det2, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at eD eA2 ⊢
  field_simp
  subst eD eA2
  ring

omit x y in
/-- The moving-edge step of Remark 2.2.4: if a line meets the lines of the edges `[-c, a]` and
`[b, c]` at `O + x (a - O)` and `O + y (b - O)`, leaves `K` and the origin on the same side, and
meets the edge lines inside the adjacent edge-halves, then replacing the edge `[a, b]` (and
`[-a, -b]`) by this line gives a circumscribed centrally symmetric hexagon of area
`area(H) - (x y - 1) A₁ A₂ / D`; by minimality `x y ≤ 1`. -/
lemma rein_rmk_newHex {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K)
    (hv : IsLeastAreaHexagon K (rein_hex3 a b c)) (eD : D = det2 b c + det2 a c - det2 a b)
    (eA1 : A1 = det2 a b - det2 b c + det2 a c) (eA2 : A2 = det2 a b + det2 b c - det2 a c)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxδ : x * A2 ≤ A2 / 2 + det2 b c) (hyγ : y * A1 ≤ A1 / 2 + det2 a c)
    (hKside : ∀ z ∈ K,
      x * y ≤ y * (det2 (c - b) (z - b) / A2) + x * (det2 (a + c) (z - a) / A1))
    (h0side : x * y < y * (det2 b c / A2) + x * (det2 a c / A1)) : x * y ≤ 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := (rein_isCSHexagon_hex3_iff a b c).1 hv.1
  have hD : 0 < D := by rw [eD]; linarith
  have hA1 : 0 < A1 := by rw [eA1]; linarith
  have hA2 : 0 < A2 := by rw [eA2]; linarith
  have hA12 := mul_pos hA1 hA2
  have posD : ∀ t, 0 < t * D → 0 < t := fun t ht ↦ by
    by_contra h; push Not at h; nlinarith
  have nnD : ∀ t, 0 ≤ t * D → 0 ≤ t := fun t ht ↦ by
    by_contra h; push Not at h; nlinarith
  set a' : Fin 2 → ℝ := a + ((1 - x) * A2 / D) • (a + c) with ha'
  set b' : Fin 2 → ℝ := b + ((1 - y) * A1 / D) • (b - c) with hb'
  have e1 := rein_rmk_e1 x y hD.ne' eD eA1 eA2
  have e2 := rein_rmk_e2 (a := a) (b := b) (c := c) y hD.ne' eD eA1
  have e3 := rein_rmk_e3 (a := a) (b := b) (c := c) x hD.ne' eD eA2
  have earea : D * (det2 a b + det2 b c + det2 a c) = 4 * det2 b c * det2 a c - A1 * A2 := by
    rw [eD, eA1, eA2]; ring
  have hq1 : 0 < 2 * det2 a c - y * A1 := by rw [eA1] at hyγ ⊢; linarith
  have hq2 : 0 < 2 * det2 b c - x * A2 := by rw [eA2] at hxδ ⊢; linarith
  have hd1 : 0 < det2 a' b' := by
    refine posD _ ?_
    rw [e1]
    have h := mul_lt_mul_of_pos_left h0side hA12
    have e' : A1 * A2 * (y * (det2 b c / A2) + x * (det2 a c / A1)) =
        x * det2 a c * A2 + y * det2 b c * A1 := by field_simp; ring
    linarith
  have hd2 : 0 < det2 b' c := posD _ (by rw [e2]; exact mul_pos h2 hq1)
  have hd3 : 0 < det2 a' c := posD _ (by rw [e3]; exact mul_pos h3 hq2)
  have hhex : IsCSHexagon (rein_hex3 a' b' c) := by
    rw [rein_isCSHexagon_hex3_iff]
    refine ⟨hd1, hd2, hd3, ?_, ?_, ?_⟩
    · have := posD (det2 a' b' + det2 b' c - det2 a' c) (by
        rw [show (det2 a' b' + det2 b' c - det2 a' c) * D = x * A2 * (2 * det2 a c - y * A1) by
          linear_combination e1 + e2 - e3]
        exact mul_pos (mul_pos hx hA2) hq1)
      linarith
    · have := posD (det2 b' c + det2 a' c - det2 a' b') (by
        rw [show (det2 b' c + det2 a' c - det2 a' b') * D =
            (2 * det2 b c - x * A2) * (2 * det2 a c - y * A1) by
          linear_combination e2 + e3 - e1]
        exact mul_pos hq2 hq1)
      linarith
    · have := posD (det2 a' b' + det2 a' c - det2 b' c) (by
        rw [show (det2 a' b' + det2 a' c - det2 b' c) * D = y * A1 * (2 * det2 b c - x * A2) by
          linear_combination e1 + e3 - e2]
        exact mul_pos (mul_pos hy hA1) hq2)
      linarith
  -- the new hexagon contains `K`
  have hKsub : K ⊆ hexagonOf (rein_hex3 a' b' c) := by
    intro z hz
    rw [rein_mem_hexagonOf_hex3 hhex]
    obtain ⟨o0, o1, o2, o3, o4, o5⟩ := (rein_mem_hexagonOf_hex3 hv.1 z).1 (hv.2.1 hz)
    obtain ⟨p0, p1, p2, p3, p4, p5⟩ :=
      (rein_mem_hexagonOf_hex3 hv.1 (-z)).1 (hv.2.1 (hK.2.2.2 z hz))
    have k1 := hKside z hz
    have k2 := hKside (-z) (hK.2.2.2 z hz)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact nnD _ (by
        rw [rein_rmk_eE0 x y z hD.ne' hA1.ne' hA2.ne' eD eA1 eA2]
        exact mul_nonneg hA12.le (by linarith))
    · exact nnD _ (by rw [rein_rmk_eE1 y z hD.ne' eD eA1]; exact mul_nonneg hq1.le o1)
    · exact nnD _ (by rw [rein_rmk_eE2 x z hD.ne' eD eA2]; exact mul_nonneg hq2.le o2)
    · exact nnD _ (by
        rw [rein_rmk_eE0 x y (-z) hD.ne' hA1.ne' hA2.ne' eD eA1 eA2]
        exact mul_nonneg hA12.le (by linarith))
    · exact nnD _ (by rw [rein_rmk_eE1 y (-z) hD.ne' eD eA1]; exact mul_nonneg hq1.le p1)
    · exact nnD _ (by rw [rein_rmk_eE2 x (-z) hD.ne' eD eA2]; exact mul_nonneg hq2.le p2)
  -- and has area `area(H) - (x y - 1) A₁ A₂ / D`
  have hle := hv.2.2 _ hhex hKsub
  rw [rein_volume_hexagonOf_hex3 hv.1, rein_volume_hexagonOf_hex3 hhex,
    ENNReal.ofReal_le_ofReal_iff (by linarith)] at hle
  have key : (det2 a' b' + det2 b' c + det2 a' c) * D =
      4 * det2 b c * det2 a c - x * y * A1 * A2 := by
    linear_combination e1 + e2 + e3
  by_contra hxy
  push Not at hxy
  have : (det2 a' b' + det2 b' c + det2 a' c) * D < (det2 a b + det2 b c + det2 a c) * D := by
    rw [key, mul_comm _ D, earea]
    nlinarith
  have := lt_of_mul_lt_mul_right this hD.le
  linarith

lemma rein_rmk_amgm {ξ η x y : ℝ} (hξη : ξ * η = 1 / 4) (hξ : 0 < ξ) (hη : 0 < η) (hx : 0 < x)
    (hy : 0 < y) (h : y * ξ + x * η < x * y) : 1 < x * y := by
  have h4 : 4 * (ξ * η) * (x * y) ≤ (y * ξ + x * η) ^ 2 := by
    nlinarith [sq_nonneg (y * ξ - x * η)]
  rw [hξη] at h4
  have hS : 0 < y * ξ + x * η := by positivity
  have hxy0 := mul_pos hx hy
  nlinarith [mul_lt_mul_of_pos_right h hS, mul_lt_mul_of_pos_left h hxy0]

/-- The apex lies on the side of `p`: the triangle `O m₅ m₁` contains `p`, and `g ≥ c₀` at its
vertices `m₅, m₁`. -/
lemma rein_rmk_apex {gO c0 α β ξ η δ γ : ℝ} (hδ : 1 < δ) (hγ : 1 < γ) (hξ : 0 < ξ) (hη : 0 < η)
    (hw : ξ / δ + η / γ < 1) (h5 : c0 ≤ gO + δ * α) (h1 : c0 ≤ gO + γ * β)
    (hp : gO + ξ * α + η * β < c0) : gO < c0 := by
  by_contra hO
  push Not at hO
  have w1 : 0 ≤ ξ / δ := div_nonneg hξ.le (by linarith)
  have w2 : 0 ≤ η / γ := div_nonneg hη.le (by linarith)
  have q1 := mul_nonneg w1 (show 0 ≤ gO + δ * α - c0 by linarith)
  have q2 := mul_nonneg w2 (show 0 ≤ gO + γ * β - c0 by linarith)
  have q3 := mul_nonneg (show 0 ≤ 1 - ξ / δ - η / γ by linarith) (show 0 ≤ gO - c0 by linarith)
  have hδ0 : δ ≠ 0 := by linarith
  have hγ0 : γ ≠ 0 := by linarith
  have : ξ / δ * (gO + δ * α - c0) + η / γ * (gO + γ * β - c0) +
      (1 - ξ / δ - η / γ) * (gO - c0) = gO + ξ * α + η * β - c0 := by
    field_simp; ring
  linarith

/-- The values of the coordinates `ξ, η` at the points `m`, `m₅`, `m₁`, `0`. -/
lemma rein_rmk_values (hA1 : A1 ≠ 0) (hA2 : A2 ≠ 0) (eA1 : A1 = det2 a b - det2 b c + det2 a c)
    (eA2 : A2 = det2 a b + det2 b c - det2 a c) :
    det2 (c - b) (midpoint ℝ a b - b) / A2 = 1 / 2 ∧
    det2 (a + c) (midpoint ℝ a b - a) / A1 = 1 / 2 ∧
    det2 (c - b) (midpoint ℝ (-c) a - b) / A2 = 1 / 2 + det2 b c / A2 ∧
    det2 (a + c) (midpoint ℝ (-c) a - a) / A1 = 0 ∧
    det2 (c - b) (midpoint ℝ b c - b) / A2 = 0 ∧
    det2 (a + c) (midpoint ℝ b c - a) / A1 = 1 / 2 + det2 a c / A1 ∧
    det2 (c - b) (0 - b) / A2 = det2 b c / A2 ∧ det2 (a + c) (0 - a) / A1 = det2 a c / A1 := by
  simp only [midpoint_eq_smul_add, det2, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply,
    Pi.zero_apply, smul_eq_mul, invOf_eq_inv] at eA1 eA2 ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> field_simp
  · subst eA2; ring
  · subst eA1; ring
  · subst eA2; ring
  · ring
  · ring
  · subst eA1; ring
  · ring
  · ring

lemma rein_rmk_δ (hv : IsCSHexagon (rein_hex3 a b c)) (hA2 : 0 < A2)
    (eA2 : A2 = det2 a b + det2 b c - det2 a c) : 1 < 1 / 2 + det2 b c / A2 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := (rein_isCSHexagon_hex3_iff a b c).1 hv
  rw [← sub_pos]
  have : 1 / 2 + det2 b c / A2 - 1 = (det2 b c + det2 a c - det2 a b) / (2 * A2) := by
    field_simp; rw [eA2]; ring
  rw [this]; apply div_pos (by linarith) (by linarith)

lemma rein_rmk_γ (hv : IsCSHexagon (rein_hex3 a b c)) (hA1 : 0 < A1)
    (eA1 : A1 = det2 a b - det2 b c + det2 a c) : 1 < 1 / 2 + det2 a c / A1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := (rein_isCSHexagon_hex3_iff a b c).1 hv
  rw [← sub_pos]
  have : 1 / 2 + det2 a c / A1 - 1 = (det2 b c + det2 a c - det2 a b) / (2 * A1) := by
    field_simp; rw [eA1]; ring
  rw [this]; apply div_pos (by linarith) (by linarith)

/-- The contradiction in Remark 2.2.4, in the coordinates `ξ, η`: an affine function
`g = g(O) + ξ α + η β` with `g ≥ c₀` on `K`, `g(p) < c₀` and `g(0) > c₀`, for a point `p` of the
hyperbola `ξ η = 1/4` near the midpoint. -/
lemma rein_rmk_final {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K)
    (hv : IsLeastAreaHexagon K (rein_hex3 a b c)) (hD : 0 < D) (hA1 : 0 < A1) (hA2 : 0 < A2)
    (eD : D = det2 b c + det2 a c - det2 a b)
    (eA1 : A1 = det2 a b - det2 b c + det2 a c) (eA2 : A2 = det2 a b + det2 b c - det2 a c)
    {p : Fin 2 → ℝ} (hξp : 0 < det2 (c - b) (p - b) / A2) (hηp : 0 < det2 (a + c) (p - a) / A1)
    (hw : det2 (c - b) (p - b) / A2 / (1 / 2 + det2 b c / A2) +
      det2 (a + c) (p - a) / A1 / (1 / 2 + det2 a c / A1) < 1)
    (hξη : det2 (c - b) (p - b) / A2 * (det2 (a + c) (p - a) / A1) = 1 / 4)
    {gO c0 α β : ℝ}
    (hc0 : ∀ z ∈ K, c0 ≤ gO + det2 (c - b) (z - b) / A2 * α + det2 (a + c) (z - a) / A1 * β)
    (hpg : gO + det2 (c - b) (p - b) / A2 * α + det2 (a + c) (p - a) / A1 * β < c0)
    (h0 : c0 < gO + det2 b c / A2 * α + det2 a c / A1 * β) : False := by
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8⟩ := rein_rmk_values hA1.ne' hA2.ne' eA1 eA2
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := (rein_isCSHexagon_hex3_iff a b c).1 hv.1
  set ξp := det2 (c - b) (p - b) / A2
  set ηp := det2 (a + c) (p - a) / A1
  obtain ⟨δ5, hδ5⟩ : ∃ δ5 : ℝ, δ5 = 1 / 2 + det2 b c / A2 := ⟨_, rfl⟩
  obtain ⟨γ1, hγ1⟩ : ∃ γ1 : ℝ, γ1 = 1 / 2 + det2 a c / A1 := ⟨_, rfl⟩
  rw [← hδ5, ← hγ1] at hw
  have hδ5' : 1 < δ5 := by
    rw [hδ5, ← sub_pos]
    have : 1 / 2 + det2 b c / A2 - 1 = (det2 b c + det2 a c - det2 a b) / (2 * A2) := by
      field_simp; rw [eA2]; ring
    rw [this]; apply div_pos (by linarith) (by linarith)
  have hγ1' : 1 < γ1 := by
    rw [hγ1, ← sub_pos]
    have : 1 / 2 + det2 a c / A1 - 1 = (det2 b c + det2 a c - det2 a b) / (2 * A1) := by
      field_simp; rw [eA1]; ring
    rw [this]; apply div_pos (by linarith) (by linarith)
  -- the midpoints `m₅, m₁` of the adjacent edges are in `K`
  have hm5K : midpoint ℝ (-c) a ∈ K := by
    have := rein_frontier_subset hK (rein_hexMidpoint_mem_frontier hK hv 5)
    simpa [hexMidpoint, show (5 : ZMod 6) + 1 = 0 from rfl] using this
  have hm1K : midpoint ℝ b c ∈ K := by
    have := rein_frontier_subset hK (rein_hexMidpoint_mem_frontier hK hv 1)
    simpa [hexMidpoint, show (1 : ZMod 6) + 1 = 2 from rfl] using this
  have hm5g := hc0 _ hm5K
  rw [v3, v4, ← hδ5, zero_mul, add_zero] at hm5g
  have hm1g := hc0 _ hm1K
  rw [v5, v6, ← hγ1, zero_mul, add_zero] at hm1g
  -- the apex `O` lies on the side of `p`
  have hOc : gO < c0 := rein_rmk_apex hδ5' hγ1' hξp hηp hw hm5g hm1g hpg
  have hαpos : 0 < α := by
    by_contra h; push Not at h
    have : δ5 * α ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) h
    linarith
  have hβpos : 0 < β := by
    by_contra h; push Not at h
    have : γ1 * β ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) h
    linarith
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = c0 - gO := ⟨_, rfl⟩
  have hκpos : 0 < κ := by linarith
  obtain ⟨x, hx⟩ : ∃ x, x = κ / α := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = κ / β := ⟨_, rfl⟩
  have hxpos : 0 < x := by rw [hx]; exact div_pos hκpos hαpos
  have hypos : 0 < y := by rw [hy]; exact div_pos hκpos hβpos
  have hαx : α * x = κ := by rw [hx]; field_simp
  have hβy : β * y = κ := by rw [hy]; field_simp
  have hxδ : x ≤ δ5 := by rw [hx, div_le_iff₀ hαpos]; linarith
  have hyγ : y ≤ γ1 := by rw [hy, div_le_iff₀ hβpos]; linarith
  -- the side of the new support line `{g = c₀}` in the coordinates `ξ, η`
  have hgz : ∀ s t : ℝ, (gO + s * α + t * β - c0) * (x * y) = κ * (y * s + x * t - x * y) := by
    intro s t
    linear_combination y * s * hαx + x * t * hβy + x * y * hκ
  have hxy0 := mul_pos hxpos hypos
  have hside : ∀ s t : ℝ, c0 ≤ gO + s * α + t * β → x * y ≤ y * s + x * t := by
    intro s t h
    have h' := mul_nonneg (sub_nonneg.2 h) hxy0.le
    rw [hgz] at h'
    have := (mul_nonneg_iff_of_pos_left hκpos).1 h'
    linarith
  have hKside : ∀ z ∈ K,
      x * y ≤ y * (det2 (c - b) (z - b) / A2) + x * (det2 (a + c) (z - a) / A1) :=
    fun z hz ↦ hside _ _ (hc0 z hz)
  have hpside : y * ξp + x * ηp < x * y := by
    have h := mul_neg_of_neg_of_pos (sub_neg.2 hpg) hxy0
    rw [hgz] at h
    by_contra hc
    push Not at hc
    have := mul_nonneg hκpos.le (by linarith : 0 ≤ y * ξp + x * ηp - x * y)
    linarith
  -- the new support line cuts off a larger triangle: `x y > 1` (AM-GM)
  have hxy : 1 < x * y := rein_rmk_amgm hξη hξp hηp hxpos hypos hpside
  -- the origin is on the far side of the new support line
  have h0side : x * y < y * (det2 b c / A2) + x * (det2 a c / A1) := by
    have h := mul_pos (sub_pos.2 h0) hxy0
    rw [hgz] at h
    by_contra hc
    push Not at hc
    have := mul_nonpos_of_nonneg_of_nonpos hκpos.le (by linarith :
      y * (det2 b c / A2) + x * (det2 a c / A1) - x * y ≤ 0)
    linarith
  -- the moving-edge step gives `x y ≤ 1`
  have hxA : x * A2 ≤ A2 / 2 + det2 b c := by
    calc x * A2 ≤ δ5 * A2 := mul_le_mul_of_nonneg_right hxδ hA2.le
      _ = A2 / 2 + det2 b c := by rw [hδ5]; field_simp
  have hyA : y * A1 ≤ A1 / 2 + det2 a c := by
    calc y * A1 ≤ γ1 * A1 := mul_le_mul_of_nonneg_right hyγ hA1.le
      _ = A1 / 2 + det2 a c := by rw [hγ1]; field_simp
  have := rein_rmk_newHex hK hv eD eA1 eA2 hxpos hypos hxA hyA hKside h0side
  linarith

/-- The contradiction in Remark 2.2.4: a point `p` of the hyperbola near `m` outside `K` is
separated from `K` by a support line (the reviewer's argument). -/
lemma rein_rmk_contra {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K)
    (hv : IsLeastAreaHexagon K (rein_hex3 a b c)) (hD : 0 < D) (hA1 : 0 < A1) (hA2 : 0 < A2)
    (eD : D = det2 b c + det2 a c - det2 a b)
    (eA1 : A1 = det2 a b - det2 b c + det2 a c) (eA2 : A2 = det2 a b + det2 b c - det2 a c)
    {p : Fin 2 → ℝ} (hξp : 0 < det2 (c - b) (p - b) / A2) (hηp : 0 < det2 (a + c) (p - a) / A1)
    (hw : det2 (c - b) (p - b) / A2 / (1 / 2 + det2 b c / A2) +
      det2 (a + c) (p - a) / A1 / (1 / 2 + det2 a c / A1) < 1)
    (hξη : det2 (c - b) (p - b) / A2 * (det2 (a + c) (p - a) / A1) = 1 / 4) (hpK : p ∉ K) :
    False := by
  obtain ⟨-, -, -, -, -, -, v7, v8⟩ := rein_rmk_values hA1.ne' hA2.ne' eA1 eA2
  set O : Fin 2 → ℝ := a + (A2 / D) • (a + c)
  have hrep := fun z ↦ rein_rmk_rep z hD.ne' hA1.ne' hA2.ne' eD eA1 eA2
  obtain ⟨g, u, hgp, hgK⟩ := geometric_hahn_banach_point_closed hK.1 hK.2.1.isClosed hpK
  obtain ⟨x0, hx0K, hx0⟩ := hK.2.1.exists_isMinOn ⟨_, hK.2.2.2 _ (hK.2.2.2 _
    (interior_subset (rein_zero_mem_interior hK)))⟩ g.continuous.continuousOn
  have hc0 : ∀ z ∈ K, g x0 ≤ g z := fun z hz ↦ hx0 hz
  have hpc : g p < g x0 := hgp.trans (hgK _ hx0K)
  have hg : ∀ z, g z = g O + det2 (c - b) (z - b) / A2 * (g a - g O) +
      det2 (a + c) (z - a) / A1 * (g b - g O) := by
    intro z
    conv_lhs => rw [hrep z]
    simp only [O, map_add, map_smul, map_sub, smul_eq_mul]
  -- `g(0) = 0 > c₀`: the origin is an interior point
  have hc0neg : g x0 < 0 := by
    have hgne : ∃ w, 0 < g w := by
      by_contra hcon
      push Not at hcon
      have e1 : g p = 0 :=
        le_antisymm (hcon p) (by have := hcon (-p); rw [map_neg] at this; linarith)
      have e2 : g x0 = 0 :=
        le_antisymm (hcon x0) (by have := hcon (-x0); rw [map_neg] at this; linarith)
      linarith
    obtain ⟨w, hw⟩ := hgne
    obtain ⟨t, ht, htK⟩ := rein_exists_add_smul_mem (rein_zero_mem_interior hK) (-w)
    have h := hc0 _ htK
    rw [zero_add, map_smul, map_neg, smul_eq_mul] at h
    have := mul_pos ht hw
    linarith
  refine rein_rmk_final hK hv hD hA1 hA2 eD eA1 eA2 hξp hηp hw hξη (gO := g O) (c0 := g x0)
    (fun z hz ↦ (hg z) ▸ hc0 z hz) ((hg p) ▸ hpc) ?_
  have h := hg 0
  rw [map_zero, v7, v8] at h
  linarith

/-- Remark 2.2.4 for the edge `[a, b]` of a least-area hexagon `a, b, c, -a, -b, -c`. -/
lemma rein_remark_hex3 {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K)
    (hv : IsLeastAreaHexagon K (rein_hex3 a b c)) :
    ∃ ε > 0, ∀ p, dist p (midpoint ℝ a b) < ε →
      det2 (a + c) (p - a) * det2 (c - b) (p - b) =
        det2 (a + c) (midpoint ℝ a b - a) * det2 (c - b) (midpoint ℝ a b - b) → p ∈ K := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := (rein_isCSHexagon_hex3_iff a b c).1 hv.1
  obtain ⟨D, eD⟩ : ∃ D, D = det2 b c + det2 a c - det2 a b := ⟨_, rfl⟩
  obtain ⟨A1, eA1⟩ : ∃ A1, A1 = det2 a b - det2 b c + det2 a c := ⟨_, rfl⟩
  obtain ⟨A2, eA2⟩ : ∃ A2, A2 = det2 a b + det2 b c - det2 a c := ⟨_, rfl⟩
  have hD : 0 < D := by rw [eD]; linarith
  have hA1 : 0 < A1 := by rw [eA1]; linarith
  have hA2 : 0 < A2 := by rw [eA2]; linarith
  obtain ⟨v1, v2, -⟩ := rein_rmk_values hA1.ne' hA2.ne' eA1 eA2
  have hδ5'' := rein_rmk_δ hv.1 hA2 eA2
  have hγ1'' := rein_rmk_γ hv.1 hA1 eA1
  have hδ5' : 0 < 1 / 2 + det2 b c / A2 := by linarith
  have hγ1' : 0 < 1 / 2 + det2 a c / A1 := by linarith
  have hcξ : Continuous fun z : Fin 2 → ℝ ↦ det2 (c - b) (z - b) / A2 :=
    ((rein_continuous_det2_left _).comp (continuous_id.sub continuous_const)).div_const _
  have hcη : Continuous fun z : Fin 2 → ℝ ↦ det2 (a + c) (z - a) / A1 :=
    ((rein_continuous_det2_left _).comp (continuous_id.sub continuous_const)).div_const _
  -- a neighbourhood of `m` in which the hyperbola lies inside the triangle `O m₅ m₁`
  have hev : ∀ᶠ p in nhds (midpoint ℝ a b), 0 < det2 (c - b) (p - b) / A2 ∧
      0 < det2 (a + c) (p - a) / A1 ∧
      det2 (c - b) (p - b) / A2 / (1 / 2 + det2 b c / A2) +
        det2 (a + c) (p - a) / A1 / (1 / 2 + det2 a c / A1) < 1 := by
    have e1 := (continuousAt_const (y := (0 : ℝ))).eventually_lt hcξ.continuousAt
      (show (0 : ℝ) < det2 (c - b) (midpoint ℝ a b - b) / A2 by rw [v1]; norm_num)
    have e2 := (continuousAt_const (y := (0 : ℝ))).eventually_lt hcη.continuousAt
      (show (0 : ℝ) < det2 (a + c) (midpoint ℝ a b - a) / A1 by rw [v2]; norm_num)
    have hc3 : Continuous fun p : Fin 2 → ℝ ↦ det2 (c - b) (p - b) / A2 / (1 / 2 + det2 b c / A2) +
        det2 (a + c) (p - a) / A1 / (1 / 2 + det2 a c / A1) :=
      (hcξ.div_const _).add (hcη.div_const _)
    have e3 := hc3.continuousAt.eventually_lt (continuousAt_const (y := (1 : ℝ))) (by
      rw [v1, v2]
      have q1 : 1 / 2 / (1 / 2 + det2 b c / A2) < 1 / 2 := by
        rw [div_lt_iff₀ hδ5']; nlinarith
      have q2 : 1 / 2 / (1 / 2 + det2 a c / A1) < 1 / 2 := by
        rw [div_lt_iff₀ hγ1']; nlinarith
      linarith)
    filter_upwards [e1, e2, e3] with p h1 h2 h3 using ⟨h1, h2, h3⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨ε, hε, fun p hp hFp ↦ ?_⟩
  obtain ⟨hξp, hηp, hw⟩ := hball hp
  have hξη : det2 (c - b) (p - b) / A2 * (det2 (a + c) (p - a) / A1) = 1 / 4 := by
    have hF : ∀ z, det2 (a + c) (z - a) * det2 (c - b) (z - b) =
        A1 * A2 * (det2 (c - b) (z - b) / A2 * (det2 (a + c) (z - a) / A1)) := by
      intro z; field_simp
    rw [hF, hF, v1, v2] at hFp
    have := mul_pos hA1 hA2
    have h' : A1 * A2 * (det2 (c - b) (p - b) / A2 * (det2 (a + c) (p - a) / A1) - 1 / 4) = 0 := by
      linarith
    rcases mul_eq_zero.1 h' with h | h
    · exact absurd h this.ne'
    · linarith
  by_contra hpK
  exact rein_rmk_contra hK hv hD hA1 hA2 eD eA1 eA2 hξp hηp hw hξη hpK

end remark

/-- **Remark 2.2.4** (`rem:arc-hyperbola`). Let `K` be a centrally symmetric convex disk and `H_K`
a centrally symmetric hexagon of least area circumscribing it (there is none when `K` is a
parallelogram). Locally around each edge midpoint of `H_K`, `K` contains an arc of the hyperbola
through that midpoint whose asymptotes are the lines through the two adjacent edges (the envelope
of the edges obtained by sliding the edge with the area fixed).

Departure from the paper: the book gives no proof. The proof follows the suggested argument with
a separating line (Hahn–Banach) in place of the support line at the nearest point: if a point of
the hyperbola near the midpoint were outside `K`, a line separating it from `K` would cut off from
the angle between the adjacent edge lines a larger triangle than the edge does (AM–GM), giving a
circumscribed centrally symmetric hexagon of smaller area. -/
theorem remark2_2_4 {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {v : ZMod 6 → Fin 2 → ℝ}
    (hv : IsLeastAreaHexagon K v) (j : ZMod 6) :
    ∃ ε > 0, ∀ p, dist p (hexMidpoint v j) < ε →
      hexHyperbolaFun v j p = hexHyperbolaFun v j (hexMidpoint v j) → p ∈ K := by
  set v' : ZMod 6 → Fin 2 → ℝ := fun k ↦ v (k + j) with hv'def
  have hv' : IsLeastAreaHexagon K v' := rein_isLeastAreaHexagon_shift hv j
  have hF : ∀ p, hexHyperbolaFun v j p = hexHyperbolaFun v' 0 p := by
    intro p
    simp only [hexHyperbolaFun, hv'def]
    rw [show (0 : ZMod 6) - 1 + j = j - 1 by ring, show (0 : ZMod 6) + j = j by ring,
      show (0 : ZMod 6) + 2 + j = j + 2 by ring, show (0 : ZMod 6) + 1 + j = j + 1 by ring]
  have hm : hexMidpoint v j = hexMidpoint v' 0 := by
    rw [hv'def, rein_hexMidpoint_shift, zero_add]
  have h3 := rein_eq_hex3 hv'.1
  have hv3 : IsLeastAreaHexagon K (rein_hex3 (v' 0) (v' 1) (v' 2)) := h3 ▸ hv'
  obtain ⟨ε, hε, H⟩ := rein_remark_hex3 hK hv3
  have hF3 : ∀ p, hexHyperbolaFun v' 0 p =
      det2 (v' 0 + v' 2) (p - v' 0) * det2 (v' 2 - v' 1) (p - v' 1) := by
    intro p
    rw [h3]
    simp only [hexHyperbolaFun, show (0 : ZMod 6) - 1 = 5 from rfl, zero_add,
      show (0 : ZMod 6) + 2 = 2 from rfl, rein_hex3_zero, rein_hex3_one, rein_hex3_two,
      rein_hex3_five, sub_neg_eq_add]
  have hm3 : hexMidpoint v' 0 = midpoint ℝ (v' 0) (v' 1) := by
    simp only [hexMidpoint, zero_add]
  refine ⟨ε, hε, fun p hp hpF ↦ H p (by rw [← hm3, ← hm]; exact hp) ?_⟩
  rw [hF, hF, hF3, hF3, hm, hm3] at hpF
  exact hpF


/-! ## Helper lemmas for Lemma 2.2.5 -/

/-! ### The sixth roots of unity -/

private lemma rein_sixthRoot_eq (k : ZMod 6) (n : ℕ) (hn : k.val = n) :
    sixthRoot k = ![Real.cos (Real.pi * n / 3), Real.sin (Real.pi * n / 3)] := by
  rw [sixthRoot, hn]

lemma rein_sixthRoot_zero : sixthRoot 0 = ![1, 0] := by
  rw [rein_sixthRoot_eq 0 0 rfl]; simp

lemma rein_sixthRoot_one : sixthRoot 1 = ![1 / 2, √3 / 2] := by
  rw [rein_sixthRoot_eq 1 1 rfl]; simp

lemma rein_sixthRoot_two : sixthRoot 2 = ![-(1 / 2), √3 / 2] := by
  rw [rein_sixthRoot_eq 2 2 rfl]
  have : Real.pi * (2 : ℕ) / 3 = Real.pi - Real.pi / 3 := by push_cast; ring
  rw [this, Real.cos_pi_sub, Real.sin_pi_sub]; simp

lemma rein_sixthRoot_three : sixthRoot 3 = ![-1, 0] := by
  rw [rein_sixthRoot_eq 3 3 rfl]
  have : Real.pi * (3 : ℕ) / 3 = Real.pi := by push_cast; ring
  rw [this]; simp

lemma rein_sixthRoot_four : sixthRoot 4 = ![-(1 / 2), -(√3 / 2)] := by
  rw [rein_sixthRoot_eq 4 4 rfl]
  have : Real.pi * (4 : ℕ) / 3 = Real.pi / 3 + Real.pi := by push_cast; ring
  rw [this, Real.cos_add_pi, Real.sin_add_pi]; simp

lemma rein_sixthRoot_five : sixthRoot 5 = ![1 / 2, -(√3 / 2)] := by
  rw [rein_sixthRoot_eq 5 5 rfl]
  have : Real.pi * (5 : ℕ) / 3 = -(Real.pi / 3) + 2 * Real.pi := by push_cast; ring
  rw [this, Real.cos_add_two_pi, Real.sin_add_two_pi, Real.cos_neg, Real.sin_neg]; simp

lemma rein_sqrt3_sq : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)

lemma rein_sqrt3_pos : 0 < √3 := by positivity

/-- The relations of the sixth roots of unity: `s_{j+3}* = -s_j*`, `s_{j+1}* = s_j* + s_{j+2}*`,
`det(s_j*, s_{j+1}*) = √3/2`. -/
lemma rein_sixthRoot_rel (j : ZMod 6) :
    sixthRoot (j + 3) = -sixthRoot j ∧ sixthRoot (j + 1) = sixthRoot j + sixthRoot (j + 2) ∧
      det2 (sixthRoot j) (sixthRoot (j + 1)) = √3 / 2 := by
  rcases rein_zmod6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;> rein_z6 <;>
  simp only [rein_sixthRoot_zero, rein_sixthRoot_one, rein_sixthRoot_two, rein_sixthRoot_three,
    rein_sixthRoot_four, rein_sixthRoot_five, det2] <;>
  refine ⟨?_, ?_, ?_⟩ <;>
  first
    | (ext i; fin_cases i <;> norm_num)
    | (simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; ring)

lemma rein_det2_sixthRoot_pos (j : ZMod 6) : 0 < det2 (sixthRoot j) (sixthRoot (j + 1)) := by
  rw [(rein_sixthRoot_rel j).2.2]; positivity

lemma rein_det2_sixthRoot_ne (j : ZMod 6) : det2 (sixthRoot j) (sixthRoot (j + 1)) ≠ 0 :=
  (rein_det2_sixthRoot_pos j).ne'

/-- The linear change of coordinates taking the edge midpoints of a least-area hexagon to the sixth
roots of unity (§2.2: "replacing `K` by its image under an affine transformation, we may assume
that `s₀, …, s₅` are the sixth roots of unity"). -/
lemma rein_normalize {K : Set (Fin 2 → ℝ)} {v : ZMod 6 → Fin 2 → ℝ}
    (hv : IsLeastAreaHexagon K v) :
    ∃ (e : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ)) (d : ℝ), rein_PosLin e d ∧
      ∀ k, e (hexMidpoint v k) = sixthRoot k := by
  have hD := rein_det2_hexMidpoint_pos hv.1
  refine ⟨rein_frame _ _ (sixthRoot 0) (sixthRoot 1) hD.ne' (rein_det2_sixthRoot_ne 0), _,
    rein_posLin_frame hD (rein_det2_sixthRoot_pos 0), ?_⟩
  set e := rein_frame _ _ (sixthRoot 0) (sixthRoot 1) hD.ne' (rein_det2_sixthRoot_ne 0)
  have e0 : e (hexMidpoint v 0) = sixthRoot 0 := by
    rw [rein_frame_apply, rein_frameLin_left hD.ne']
  have e1 : e (hexMidpoint v 1) = sixthRoot 1 := by
    rw [rein_frame_apply, rein_frameLin_right hD.ne']
  have e2 : e (hexMidpoint v 2) = sixthRoot 2 := by
    have h := rein_hexMidpoint_succ hv.1 0
    have h' := (rein_sixthRoot_rel 0).2.1
    simp only [zero_add] at h h'
    rw [show hexMidpoint v 2 = hexMidpoint v 1 - hexMidpoint v 0 by rw [h]; abel, map_sub, e0,
      e1, h']
    abel
  have neg : ∀ i, e (hexMidpoint v (i + 3)) = -e (hexMidpoint v i) := by
    intro i; rw [rein_hexMidpoint_add_three hv.1, map_neg]
  intro k
  rcases rein_zmod6_cases k with rfl | rfl | rfl | rfl | rfl | rfl
  · exact e0
  · exact e1
  · exact e2
  · rw [show (3 : ZMod 6) = 0 + 3 from rfl, neg, e0, (rein_sixthRoot_rel 0).1]
  · rw [show (4 : ZMod 6) = 1 + 3 from rfl, neg, e1, (rein_sixthRoot_rel 1).1]
  · rw [show (5 : ZMod 6) = 2 + 3 from rfl, neg, e2, (rein_sixthRoot_rel 2).1]

/-! ### Existence of a worst disk -/

/-- `K` is not the parallelogram with vertices `p, q, -p, -q` for any `p, q` (the hypothesis of
`rein_exists_least`). -/
def rein_NP (K : Set (Fin 2 → ℝ)) : Prop :=
  ∀ p q, 0 < det2 p q →
    (∀ x ∈ K, 0 ≤ det2 (q - p) (x - p) ∧ 0 ≤ det2 (-p - q) (x - q)) → ¬(p ∈ K ∧ q ∈ K)

lemma rein_mem_of_abs_add {K : Set (Fin 2 → ℝ)} (hc : Convex ℝ K) (h0 : (0 : Fin 2 → ℝ) ∈ K)
    {p q : Fin 2 → ℝ} (hp : p ∈ K) (hp' : -p ∈ K) (hq : q ∈ K) (hq' : -q ∈ K) {α β : ℝ}
    (h : |α| + |β| ≤ 1) : α • p + β • q ∈ K := by
  obtain ⟨p₁, hp₁, e1⟩ : ∃ p₁ ∈ K, α • p = |α| • p₁ := by
    rcases le_or_gt 0 α with ha | ha
    · exact ⟨p, hp, by rw [abs_of_nonneg ha]⟩
    · exact ⟨-p, hp', by rw [abs_of_neg ha, smul_neg, neg_smul, neg_neg]⟩
  obtain ⟨q₁, hq₁, e2⟩ : ∃ q₁ ∈ K, β • q = |β| • q₁ := by
    rcases le_or_gt 0 β with hb | hb
    · exact ⟨q, hq, by rw [abs_of_nonneg hb]⟩
    · exact ⟨-q, hq', by rw [abs_of_neg hb, smul_neg, neg_smul, neg_neg]⟩
  rw [e1, e2]
  rcases (add_nonneg (abs_nonneg α) (abs_nonneg β)).eq_or_lt with hs0 | hs0
  · have ha : |α| = 0 := by linarith [abs_nonneg α, abs_nonneg β]
    have hb : |β| = 0 := by linarith [abs_nonneg α, abs_nonneg β]
    rw [ha, hb, zero_smul, zero_smul, add_zero]; exact h0
  · have hz : (|α| / (|α| + |β|)) • p₁ + (|β| / (|α| + |β|)) • q₁ ∈ K :=
      hc hp₁ hq₁ (div_nonneg (abs_nonneg _) hs0.le) (div_nonneg (abs_nonneg _) hs0.le)
        (by rw [← add_div]; exact div_self hs0.ne')
    have := hc.smul_mem_of_zero_mem h0 hz ⟨hs0.le, h⟩
    convert this using 1
    rw [smul_add, smul_smul, smul_smul]
    congr 2 <;> field_simp

/-- **Padding a parallelogram.** The centrally symmetric hexagon `p, ((1+ε)/2)(p+q), q, …`
contains the parallelogram with vertices `±p, ±q` and has area `(2 + ε) det(p, q)`. -/
lemma rein_pad {p q : Fin 2 → ℝ} (hpq : 0 < det2 p q) {ε : ℝ} (hε : 0 < ε) :
    IsCSHexagon (rein_hex3 p (((1 + ε) / 2) • (p + q)) q) ∧
      (∀ α β : ℝ, |α| + |β| ≤ 1 →
        α • p + β • q ∈ hexagonOf (rein_hex3 p (((1 + ε) / 2) • (p + q)) q)) ∧
      volume.real (hexagonOf (rein_hex3 p (((1 + ε) / 2) • (p + q)) q)) =
        (2 + ε) * det2 p q := by
  set b := ((1 + ε) / 2) • (p + q) with hb
  have d1 : det2 p b = (1 + ε) / 2 * det2 p q := by
    rw [hb, rein_det2_smul_right, rein_det2_add_right, rein_det2_self, zero_add]
  have d2 : det2 b q = (1 + ε) / 2 * det2 p q := by
    rw [hb, rein_det2_smul_left, rein_det2_add_left, rein_det2_self, add_zero]
  have hH : IsCSHexagon (rein_hex3 p b q) := by
    rw [rein_isCSHexagon_hex3_iff, d1, d2]
    refine ⟨by positivity, by positivity, hpq, by nlinarith, by nlinarith, by nlinarith⟩
  refine ⟨hH, fun α β h ↦ ?_, ?_⟩
  · have hv : ∀ k, rein_hex3 p b q k ∈ hexagonOf (rein_hex3 p b q) :=
      fun k ↦ subset_convexHull ℝ _ ⟨k, rfl⟩
    have h0 : (0 : Fin 2 → ℝ) ∈ hexagonOf (rein_hex3 p b q) := by
      have := (convex_convexHull ℝ (range (rein_hex3 p b q))) (hv 0) (hv 3)
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      rwa [rein_hex3_zero, rein_hex3_three, smul_neg, add_neg_cancel] at this
    have h0' := hv 0
    have h3' := hv 3
    have h2' := hv 2
    have h5' := hv 5
    rw [rein_hex3_zero] at h0'
    rw [rein_hex3_three] at h3'
    rw [rein_hex3_two] at h2'
    rw [rein_hex3_five] at h5'
    exact rein_mem_of_abs_add (convex_convexHull ℝ _) h0 h0' h3' h2' h5' h
  · rw [rein_volume_real_hexagonOf_hex3 hH, d1, d2]; ring

/-- A centrally symmetric parallelogram can be written with a positively oriented frame. -/
lemma rein_csPar_pos {P : Set (Fin 2 → ℝ)} (hP : IsCSParallelogram P) :
    ∃ u v : Fin 2 → ℝ, 0 < det2 u v ∧
      P = {x | ∃ s t : ℝ, |s| ≤ 1 ∧ |t| ≤ 1 ∧ x = s • u + t • v} := by
  obtain ⟨u, v, huv, rfl⟩ := hP
  rcases huv.lt_or_gt with h | h
  · refine ⟨v, u, by rw [rein_det2_swap]; linarith, ?_⟩
    ext x
    constructor
    · rintro ⟨s, t, hs, ht, rfl⟩; exact ⟨t, s, ht, hs, add_comm _ _⟩
    · rintro ⟨s, t, hs, ht, rfl⟩; exact ⟨t, s, ht, hs, add_comm _ _⟩
  · exact ⟨u, v, h, rfl⟩

/-- A centrally symmetric parallelogram lies in centrally symmetric hexagons of area arbitrarily
close to its own. -/
lemma rein_par_pad {P : Set (Fin 2 → ℝ)} (hP : IsCSParallelogram P) {ε : ℝ} (hε : 0 < ε) :
    ∃ w, IsCSHexagon w ∧ P ⊆ hexagonOf w ∧
      volume.real (hexagonOf w) ≤ (1 + ε) * volume.real P := by
  obtain ⟨u, v, huv, rfl⟩ := rein_csPar_pos hP
  have e : det2 (u + v) (v - u) = 2 * det2 u v := by
    simp only [det2, Pi.add_apply, Pi.sub_apply]; ring
  have hpq : 0 < det2 (u + v) (v - u) := by rw [e]; linarith
  obtain ⟨hH, hmem, hvol⟩ := rein_pad hpq (ε := 2 * ε) (by linarith)
  refine ⟨_, hH, ?_, ?_⟩
  · intro x hx
    obtain ⟨s, t, hs, ht, rfl⟩ := hx
    have key := hmem ((s + t) / 2) ((t - s) / 2) (by
      rw [abs_le] at hs ht
      rcases abs_cases ((s + t) / 2) with ⟨h1, -⟩ | ⟨h1, -⟩ <;>
      rcases abs_cases ((t - s) / 2) with ⟨h2, -⟩ | ⟨h2, -⟩ <;> rw [h1, h2] <;>
      linarith [hs.1, hs.2, ht.1, ht.2])
    convert key using 1
    ext i; simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  · rw [hvol, rein_volume_parallelogram huv, e]
    exact le_of_eq (by ring)

lemma rein_le_of_forall_sq {A V : ℝ} (h : ∀ ε > 0, A ≤ (1 + ε) ^ 2 * V) : A ≤ V := by
  have ht : Tendsto (fun ε : ℝ ↦ (1 + ε) ^ 2 * V) (𝓝[>] 0) (𝓝 V) := by
    have hc : Continuous (fun ε : ℝ ↦ (1 + ε) ^ 2 * V) := by fun_prop
    have h2 := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using h2
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε ↦ h ε hε)

lemma rein_glpd_nonneg (K : Set (Fin 2 → ℝ)) : 0 ≤ greatestLatticePackingDensity K :=
  Real.sSup_nonneg fun _ ⟨_, _, _, hd⟩ ↦ hd ▸ ENNReal.toReal_nonneg

/-- The density of a lattice packing of `K` is at most `area(K)/A` when every centrally symmetric
hexagon containing `K` has area at least `A` (Lemma 2.2.1: `K` lies in a parallelogram or hexagon
whose `L`-translates pack, so of area at most `det(L)`, `rein_volume_le_latticeDet`; a
parallelogram is padded to a hexagon). -/
lemma rein_density_le {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {A : ℝ} (hA : 0 < A)
    (hhex : ∀ w, IsCSHexagon w → K ⊆ hexagonOf w → A ≤ volume.real (hexagonOf w))
    {L : Submodule ℤ (Fin 2 → ℝ)} (hL : IsPlaneLattice L) (hKL : IsLatticePacking K L) :
    latticePackingDensity K L ≤ volume.real K / A := by
  have hKc : IsConvexDisk K := ⟨hK.1, hK.2.1, hK.2.2.1⟩
  rw [ch2_latticePackingDensity_eq hKc hL hKL]
  obtain ⟨H, hHt, hKH, hT⟩ := lemma2_2_1 hK hL hKL
  have hdet : A ≤ latticeDet L := by
    rcases hHt with hP | ⟨w, hw, rfl⟩
    · have hP' := hP
      obtain ⟨u, u', -, rfl⟩ := hP'
      have hcc := rein_parallelogram_convex_compact u u'
      refine le_trans ?_ (rein_volume_le_latticeDet hcc.1 hL hT)
      apply rein_le_of_forall_sq
      intro ε hε
      obtain ⟨w, hw, hPw, hvol⟩ := rein_par_pad hP hε
      have h1 := hhex w hw (hKH.trans hPw)
      have hV : 0 ≤ volume.real
          {x : Fin 2 → ℝ | ∃ s t : ℝ, |s| ≤ 1 ∧ |t| ≤ 1 ∧ x = s • u + t • u'} :=
        measureReal_nonneg
      nlinarith [mul_nonneg hε.le hV]
    · exact (hhex w hw hKH).trans (rein_volume_le_latticeDet (convex_convexHull ℝ _) hL hT)
  exact div_le_div_of_nonneg_left measureReal_nonneg hA hdet

lemma rein_glpd_le {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {A : ℝ} (hA : 0 < A)
    (hhex : ∀ w, IsCSHexagon w → K ⊆ hexagonOf w → A ≤ volume.real (hexagonOf w)) :
    greatestLatticePackingDensity K ≤ volume.real K / A :=
  Real.sSup_le (fun _ ⟨_, hL, hKL, hd⟩ ↦ hd ▸ rein_density_le hK hA hhex hL hKL)
    (div_nonneg measureReal_nonneg hA.le)

lemma rein_glpd_le_one {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) :
    greatestLatticePackingDensity K ≤ 1 := by
  have hpos := rein_volume_real_pos hK
  have := rein_glpd_le hK hpos (fun w _ hKw ↦
    measureReal_mono hKw (rein_isCompact_hexagonOf w).measure_lt_top.ne)
  rwa [div_self hpos.ne'] at this

/-- `δ_L(K) = area(K)/area(H_K)` for a least-area hexagon `H_K` (the proof of Theorem 2.2.2). -/
lemma rein_glpd_eq {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {v : ZMod 6 → Fin 2 → ℝ}
    (hv : IsLeastAreaHexagon K v) :
    greatestLatticePackingDensity K = volume.real K / volume.real (hexagonOf v) := by
  have hKc : IsConvexDisk K := ⟨hK.1, hK.2.1, hK.2.2.1⟩
  have hvpos : 0 < volume.real (hexagonOf v) := lt_of_lt_of_le (rein_volume_real_pos hK)
    (measureReal_mono hv.2.1 (rein_isCompact_hexagonOf v).measure_lt_top.ne)
  obtain ⟨L0, hL0, hdet0, hpack0⟩ := rein_hex_lattice hv.1
  have hpackK : IsLatticePacking K L0 := rein_isLatticePacking_mono hv.2.1 hpack0
  refine IsGreatest.csSup_eq ⟨⟨L0, hL0, hpackK, ?_⟩, ?_⟩
  · rw [ch2_latticePackingDensity_eq hKc hL0 hpackK, hdet0]
  · rintro _ ⟨L, hL, hKL, rfl⟩
    exact rein_density_le hK hvpos (fun w hw hKw ↦ rein_least_le hv hw hKw) hL hKL

/-- A disk that is a parallelogram `±p, ±q` has `δ_L = 1` (it lies in hexagons of area
arbitrarily close to its own, whose lattice tilings pack it). -/
lemma rein_one_le_glpd {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) (hnp : ¬rein_NP K) :
    1 ≤ greatestLatticePackingDensity K := by
  simp only [rein_NP, not_forall, not_not, exists_prop] at hnp
  obtain ⟨p, q, hpq, hP, hp, hq⟩ := hnp
  have hKc : IsConvexDisk K := ⟨hK.1, hK.2.1, hK.2.2.1⟩
  have hpos := rein_volume_real_pos hK
  have h0 : (0 : Fin 2 → ℝ) ∈ K := interior_subset (rein_zero_mem_interior hK)
  have hp' := hK.2.2.2 p hp
  have hq' := hK.2.2.2 q hq
  have hco : ∀ x ∈ K, |det2 x q / det2 p q| + |det2 p x / det2 p q| ≤ 1 := by
    intro x hx
    obtain ⟨h1, h2⟩ := hP x hx
    obtain ⟨h3, h4⟩ := hP (-x) (hK.2.2.2 x hx)
    have e1 : det2 (q - p) (x - p) = det2 p q - det2 x q - det2 p x := by
      simp only [det2, Pi.sub_apply]; ring
    have e2 : det2 (-p - q) (x - q) = det2 p q + det2 x q - det2 p x := by
      simp only [det2, Pi.sub_apply, Pi.neg_apply]; ring
    have e3 : det2 (q - p) (-x - p) = det2 p q + det2 x q + det2 p x := by
      simp only [det2, Pi.sub_apply, Pi.neg_apply]; ring
    have e4 : det2 (-p - q) (-x - q) = det2 p q - det2 x q + det2 p x := by
      simp only [det2, Pi.sub_apply, Pi.neg_apply]; ring
    rw [e1] at h1; rw [e2] at h2; rw [e3] at h3; rw [e4] at h4
    rw [abs_div, abs_div, abs_of_pos hpq, ← add_div, div_le_one hpq]
    rcases abs_cases (det2 x q) with ⟨ha, -⟩ | ⟨ha, -⟩ <;>
    rcases abs_cases (det2 p x) with ⟨hb, -⟩ | ⟨hb, -⟩ <;> rw [ha, hb] <;> linarith
  have hxeq : ∀ x : Fin 2 → ℝ, (det2 x q / det2 p q) • p + (det2 p x / det2 p q) • q = x := by
    intro x
    have h := rein_cramer p q x
    rw [div_eq_inv_mul, div_eq_inv_mul, mul_smul, mul_smul, ← smul_add, ← h, smul_smul,
      inv_mul_cancel₀ hpq.ne', one_smul]
  -- the inscribed parallelogram `±p, ±q` has area `2 det(p, q)`
  have hvolK : 2 * det2 p q ≤ volume.real K := by
    set u : Fin 2 → ℝ := (1 / 2 : ℝ) • (p - q)
    set v : Fin 2 → ℝ := (1 / 2 : ℝ) • (p + q)
    have huv : det2 u v = det2 p q / 2 := by
      simp only [u, v, det2, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]; ring
    have hsub : {x : Fin 2 → ℝ | ∃ s t : ℝ, |s| ≤ 1 ∧ |t| ≤ 1 ∧ x = s • u + t • v} ⊆ K := by
      intro x hx
      obtain ⟨s, t, hs, ht, rfl⟩ := hx
      have key := rein_mem_of_abs_add hK.1 h0 hp hp' hq hq' (α := (s + t) / 2)
        (β := (t - s) / 2) (by
          rw [abs_le] at hs ht
          rcases abs_cases ((s + t) / 2) with ⟨h1, -⟩ | ⟨h1, -⟩ <;>
          rcases abs_cases ((t - s) / 2) with ⟨h2, -⟩ | ⟨h2, -⟩ <;> rw [h1, h2] <;>
          linarith [hs.1, hs.2, ht.1, ht.2])
      convert key using 1
      ext i; simp only [u, v, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
    have := measureReal_mono hsub (hK.2.1.measure_lt_top (μ := volume)).ne
    rw [rein_volume_parallelogram (by rw [huv]; positivity), huv] at this
    linarith
  have hbdd : BddAbove {d | ∃ L, IsPlaneLattice L ∧ IsLatticePacking K L ∧
      latticePackingDensity K L = d} := by
    refine ⟨1, fun _ ⟨L, hL, hKL, hd⟩ ↦ hd ▸ ?_⟩
    have := rein_density_le hK hpos (fun w _ hKw ↦
      measureReal_mono hKw (rein_isCompact_hexagonOf w).measure_lt_top.ne) hL hKL
    rwa [div_self hpos.ne'] at this
  have hge : ∀ ε > 0, 2 / (2 + ε) ≤ greatestLatticePackingDensity K := by
    intro ε hε
    obtain ⟨hH, hmem, hvol⟩ := rein_pad hpq hε
    have hKH : K ⊆ hexagonOf (rein_hex3 p (((1 + ε) / 2) • (p + q)) q) := by
      intro x hx
      rw [← hxeq x]
      exact hmem _ _ (hco x hx)
    obtain ⟨L0, hL0, hdet0, hpack0⟩ := rein_hex_lattice hH
    have hpackK : IsLatticePacking K L0 := rein_isLatticePacking_mono hKH hpack0
    have h1 := le_csSup hbdd ⟨L0, hL0, hpackK, rfl⟩
    rw [ch2_latticePackingDensity_eq hKc hL0 hpackK, hdet0, hvol] at h1
    refine le_trans ?_ h1
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have ht : Tendsto (fun ε : ℝ ↦ 2 / (2 + ε)) (𝓝[>] 0) (𝓝 1) := by
    have hc : ContinuousAt (fun ε : ℝ ↦ 2 / (2 + ε)) 0 := by
      apply ContinuousAt.div continuousAt_const (by fun_prop) (by norm_num)
    have h2 := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using h2
  exact le_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε ↦ hge ε hε)

/-! ### Scaling -/

/-- The homothety `x ↦ c x`. -/
noncomputable def rein_sc (c : ℝ) (hc : c ≠ 0) : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ) :=
  (LinearEquiv.smulOfNeZero ℝ (Fin 2 → ℝ) c hc).toContinuousLinearEquiv

lemma rein_sc_apply (c : ℝ) (hc : c ≠ 0) (x : Fin 2 → ℝ) : rein_sc c hc x = c • x := rfl

lemma rein_posLin_sc {c : ℝ} (hc : 0 < c) : rein_PosLin (rein_sc c hc.ne') (c ^ 2) :=
  ⟨by positivity, fun x y ↦ by
    simp only [rein_sc_apply, det2, Pi.smul_apply, smul_eq_mul]; ring⟩

lemma rein_mem_sc_image {c : ℝ} (hc : c ≠ 0) {S : Set (Fin 2 → ℝ)} {z : Fin 2 → ℝ}
    (h : c⁻¹ • z ∈ S) : z ∈ rein_sc c hc '' S :=
  ⟨c⁻¹ • z, h, by rw [rein_sc_apply, smul_smul, mul_inv_cancel₀ hc, one_smul]⟩

lemma rein_real_image {e : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ)} {d : ℝ} (he : rein_PosLin e d)
    (S : Set (Fin 2 → ℝ)) : volume.real (e '' S) = d * volume.real S := by
  rw [measureReal_def, he.volume_image, ENNReal.toReal_mul, ENNReal.toReal_ofReal he.pos.le]
  rfl

/-- A convex set containing the ball of radius `r` about the origin contains `(r/(r + ρ)) z` for
every `z` within `ρ` of it. -/
lemma rein_mem_scale {K : Set (Fin 2 → ℝ)} (hc : Convex ℝ K) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball (0 : Fin 2 → ℝ) r ⊆ K) {y z : Fin 2 → ℝ} (hy : y ∈ K) {ρ : ℝ}
    (hρ : 0 < ρ) (hyz : dist z y < ρ) : (r / (r + ρ)) • z ∈ K := by
  have hw : (r / ρ) • (z - y) ∈ K := by
    apply hball
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (div_pos hr hρ).le, ← dist_eq_norm]
    calc r / ρ * dist z y < r / ρ * ρ := by gcongr
      _ = r := by field_simp
  have := hc hy hw (div_pos hr (add_pos hr hρ)).le (div_pos hρ (add_pos hr hρ)).le
    (by field_simp)
  convert this using 1
  ext i; simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; field_simp; ring

/-- The area of a hexagon whose edge midpoints are the sixth roots of unity is `2√3`. -/
lemma rein_volume_std {w : ZMod 6 → Fin 2 → ℝ} (hw : IsCSHexagon w)
    (hm : ∀ j, hexMidpoint w j = sixthRoot j) : volume.real (hexagonOf w) = 2 * √3 := by
  have h := (rein_sixthRoot_rel 0).2.2
  rw [zero_add] at h
  rw [measureReal_def, rein_volume_hexagonOf hw, hm, hm, h, ENNReal.toReal_ofReal (by positivity)]
  ring

/-! ### The Blaschke selection theorem -/

/-- **Blaschke selection** (via the compactness of the space of nonempty compact subsets of a
compact set, `TopologicalSpace.NonemptyCompacts.isCompact_subsets_of_isCompact`). A sequence of
centrally symmetric convex disks between two fixed balls has a subsequence converging to a
centrally symmetric convex disk `Ks`, in the sense that eventually `K_n ⊆ (1 + ε) Ks` and
`Ks ⊆ (1 + ε) K_n`. -/
lemma rein_blaschke {K : ℕ → Set (Fin 2 → ℝ)} (hK : ∀ n, IsCCSDisk (K n)) {r R : ℝ}
    (hr : 0 < r) (hball : ∀ n, Metric.ball (0 : Fin 2 → ℝ) r ⊆ K n)
    (hR : ∀ n, K n ⊆ Metric.closedBall 0 R) :
    ∃ Ks : Set (Fin 2 → ℝ), IsCCSDisk Ks ∧ Metric.ball 0 r ⊆ Ks ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, (∀ z ∈ K (φ n), (1 + ε)⁻¹ • z ∈ Ks) ∧
        ∀ z ∈ Ks, (1 + ε)⁻¹ • z ∈ K (φ n) := by
  let N : ℕ → TopologicalSpace.NonemptyCompacts (Fin 2 → ℝ) := fun n ↦
    ⟨⟨K n, (hK n).2.1⟩, ⟨0, hball n (Metric.mem_ball_self hr)⟩⟩
  obtain ⟨Ls, -, φ, hφ, hT⟩ := (TopologicalSpace.NonemptyCompacts.isCompact_subsets_of_isCompact
    (isCompact_closedBall (0 : Fin 2 → ℝ) R)).tendsto_subseq (x := N) (fun n ↦ hR n)
  set Ks : Set (Fin 2 → ℝ) := (Ls : Set (Fin 2 → ℝ)) with hKsdef
  have F1 : ∀ U, IsOpen U → Ks ⊆ U → ∀ᶠ n in atTop, K (φ n) ⊆ U := fun U hU hsub ↦
    hT.eventually ((TopologicalSpace.NonemptyCompacts.isOpen_subsets_of_isOpen hU).mem_nhds hsub)
  have F2 : ∀ U, IsOpen U → (Ks ∩ U).Nonempty → ∀ᶠ n in atTop, (K (φ n) ∩ U).Nonempty :=
    fun U hU hne ↦ hT.eventually
      ((TopologicalSpace.NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hU).mem_nhds hne)
  have hKsc : IsClosed Ks := Ls.isCompact.isClosed
  have F3 : ∀ z, (∀ δ > 0, ∀ᶠ n in atTop, ∃ z' ∈ K (φ n), dist z' z < δ) → z ∈ Ks := by
    intro z hz
    by_contra hzK
    obtain ⟨δ, hδ, hδK⟩ := Metric.isOpen_iff.1 hKsc.isOpen_compl z hzK
    obtain ⟨n, hn1, hn2⟩ := ((F1 _ Metric.isOpen_thickening
      (Metric.self_subset_thickening (half_pos hδ) Ks)).and (hz (δ / 2) (half_pos hδ))).exists
    obtain ⟨z', hz'K, hz'z⟩ := hn2
    obtain ⟨k, hk, hdk⟩ := Metric.mem_thickening_iff.1 (hn1 hz'K)
    exact hδK (Metric.mem_ball.2 (by linarith [dist_triangle k z' z, dist_comm k z'])) hk
  have F4 : ∀ x ∈ Ks, ∀ δ > 0, ∀ᶠ n in atTop, ∃ x' ∈ K (φ n), dist x' x < δ := by
    intro x hx δ hδ
    exact (F2 _ Metric.isOpen_ball ⟨x, hx, Metric.mem_ball_self hδ⟩).mono
      fun n ⟨x', hx', hd⟩ ↦ ⟨x', hx', hd⟩
  have hballKs : Metric.ball (0 : Fin 2 → ℝ) r ⊆ Ks := fun x hx ↦
    F3 x fun δ hδ ↦ Eventually.of_forall fun n ↦ ⟨x, hball _ hx, by simpa using hδ⟩
  have hconvKs : Convex ℝ Ks := by
    intro x hx y hy a b ha hb hab
    apply F3
    intro δ hδ
    filter_upwards [F4 x hx (δ / 2) (half_pos hδ), F4 y hy (δ / 2) (half_pos hδ)] with n hxn hyn
    obtain ⟨x', hx', hdx⟩ := hxn
    obtain ⟨y', hy', hdy⟩ := hyn
    refine ⟨a • x' + b • y', (hK (φ n)).1 hx' hy' ha hb hab, ?_⟩
    have h1 := dist_add_add_le (a • x') (b • y') (a • x) (b • y)
    rw [dist_smul₀, dist_smul₀, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb] at h1
    nlinarith [mul_le_mul_of_nonneg_left hdx.le ha, mul_le_mul_of_nonneg_left hdy.le hb]
  have hsymm : ∀ x ∈ Ks, -x ∈ Ks := by
    intro x hx
    apply F3
    intro δ hδ
    filter_upwards [F4 x hx δ hδ] with n hxn
    obtain ⟨x', hx', hd⟩ := hxn
    exact ⟨-x', (hK (φ n)).2.2.2 x' hx', by rwa [dist_neg_neg]⟩
  have hKs : IsCCSDisk Ks := ⟨hconvKs, Ls.isCompact, ⟨0, mem_interior_iff_mem_nhds.2
    (Filter.mem_of_superset (Metric.ball_mem_nhds 0 hr) hballKs)⟩, hsymm⟩
  refine ⟨Ks, hKs, hballKs, φ, hφ, fun ε hε ↦ ?_⟩
  have hρ : 0 < r * ε := mul_pos hr hε
  have hscale : r / (r + r * ε) = (1 + ε)⁻¹ := by field_simp
  have E1 := F1 _ Metric.isOpen_thickening (Metric.self_subset_thickening hρ Ks)
  obtain ⟨t, htK, htfin, hcov⟩ := finite_cover_balls_of_compact Ls.isCompact (half_pos hρ)
  have E2 : ∀ᶠ n in atTop, ∀ x ∈ t, ∃ x' ∈ K (φ n), dist x' x < r * ε / 2 :=
    (eventually_all_finite htfin).2 fun x hx ↦ F4 x (htK hx) _ (half_pos hρ)
  filter_upwards [E1, E2] with n h1 h2
  constructor
  · intro z hz
    obtain ⟨y, hy, hd⟩ := Metric.mem_thickening_iff.1 (h1 hz)
    rw [← hscale]
    exact rein_mem_scale hconvKs hr hballKs hy hρ hd
  · intro z hz
    obtain ⟨x, hxt, hzx⟩ := mem_iUnion₂.1 (hcov hz)
    obtain ⟨x', hx', hd⟩ := h2 x hxt
    rw [← hscale]
    refine rein_mem_scale (hK (φ n)).1 hr (hball _) hx' hρ ?_
    rw [Metric.mem_ball] at hzx
    linarith [dist_triangle z x x', dist_comm x' x]


/-- In normal position the disk contains the ball of radius `1/3` about the origin. -/
lemma rein_ball_std {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K)
    (hm : ∀ j, sixthRoot j ∈ K) : Metric.ball (0 : Fin 2 → ℝ) (1 / 3) ⊆ K := by
  intro x hx
  have hc := hK.1
  have h0 : (0 : Fin 2 → ℝ) ∈ K := interior_subset (rein_zero_mem_interior hK)
  have hq : (1 / 2 : ℝ) • sixthRoot 1 + (1 / 2 : ℝ) • sixthRoot 2 ∈ K :=
    hc (hm 1) (hm 2) (by norm_num) (by norm_num) (by norm_num)
  have hqv : (1 / 2 : ℝ) • sixthRoot 1 + (1 / 2 : ℝ) • sixthRoot 2 = ![0, √3 / 2] := by
    rw [rein_sixthRoot_one, rein_sixthRoot_two]
    ext i; fin_cases i
    · simp
    · simp; ring
  rw [hqv] at hq
  have hq' := hK.2.2.2 _ hq
  have hp := hm 0
  have hp' := hK.2.2.2 _ hp
  rw [rein_sixthRoot_zero] at hp hp'
  have hs3 : 1 < √3 := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hx0 : |x 0| < 1 / 3 := by
    rw [mem_ball_zero_iff] at hx
    exact lt_of_le_of_lt (norm_le_pi_norm x 0) hx
  have hx1 : |x 1| < 1 / 3 := by
    rw [mem_ball_zero_iff] at hx
    exact lt_of_le_of_lt (norm_le_pi_norm x 1) hx
  have key := rein_mem_of_abs_add hc h0 hp hp' hq hq' (α := x 0) (β := x 1 * (2 / √3)) (by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / √3)]
    have : 2 / √3 ≤ 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    nlinarith [abs_nonneg (x 1)])
  convert key using 1
  have hs : √3 ≠ 0 := by positivity
  ext i; fin_cases i
  · simp
  · simp; field_simp

/-- In normal position the disk lies in the ball of radius `36`. -/
lemma rein_bound_std {K : Set (Fin 2 → ℝ)} {w : ZMod 6 → Fin 2 → ℝ} (hw : IsLeastAreaHexagon K w)
    (hm : ∀ j, hexMidpoint w j = sixthRoot j) (hball : Metric.ball (0 : Fin 2 → ℝ) (1 / 3) ⊆ K) :
    K ⊆ Metric.closedBall 0 36 := by
  have h3 := rein_eq_hex3 hw.1
  have hw3 : IsCSHexagon (rein_hex3 (w 0) (w 1) (w 2)) := h3 ▸ hw.1
  have hKw : K ⊆ hexagonOf (rein_hex3 (w 0) (w 1) (w 2)) := h3 ▸ hw.2.1
  have hA : det2 (w 0) (w 1) + det2 (w 1) (w 2) + det2 (w 0) (w 2) = 2 * √3 := by
    rw [← rein_volume_real_hexagonOf_hex3 hw3, ← h3]; exact rein_volume_std hw.1 hm
  have hb := rein_hex_bound (by norm_num : (0 : ℝ) < 1 / 3) hball hw3 hKw
  have hs3 : √3 < 2 := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hbd : ∀ y : Fin 2 → ℝ, (∀ i, 1 / 3 * |y i| ≤ 3 * (2 * √3)) →
      y ∈ Metric.closedBall (0 : Fin 2 → ℝ) 36 ∧ -y ∈ Metric.closedBall (0 : Fin 2 → ℝ) 36 := by
    intro y hy
    have : y ∈ Metric.closedBall (0 : Fin 2 → ℝ) 36 := by
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by norm_num)]
      intro i; rw [Real.norm_eq_abs]; have := hy i; nlinarith
    exact ⟨this, by simpa using this⟩
  have ha := hbd (w 0) fun i ↦ by have := (hb i).1; rwa [hA] at this
  have hb' := hbd (w 1) fun i ↦ by have := (hb i).2.1; rwa [hA] at this
  have hc := hbd (w 2) fun i ↦ by have := (hb i).2.2; rwa [hA] at this
  refine hKw.trans (convexHull_min ?_ (convex_closedBall 0 36))
  rintro _ ⟨k, rfl⟩
  rcases rein_zmod6_cases k with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ha.1
  · exact hb'.1
  · exact hc.1
  · exact ha.2
  · exact hb'.2
  · exact hc.2

/-- **Existence of a worst disk** (Lemma 2.2.5, first part; Reinhardt's argument by the Blaschke
selection theorem). A minimizing sequence of non-parallelograms is normalized by linear maps so
that a critical hexagon has the sixth roots of unity as edge midpoints; the normalized disks lie
between two fixed balls, so a subsequence converges (`rein_blaschke`). The limit has every
circumscribed hexagon of area at least `2√3` and area at most the limit of the areas, so its
greatest lattice packing density is at most the infimum. -/
lemma rein_exists_worst : ∃ K, IsWorstLatticeDisk K := by
  have hsq : IsCCSDisk (Metric.closedBall (0 : Fin 2 → ℝ) 1) := by
    refine ⟨convex_closedBall 0 1, isCompact_closedBall 0 1, ?_, fun x hx ↦ by simpa using hx⟩
    rw [interior_closedBall 0 one_ne_zero]; exact ⟨0, Metric.mem_ball_self one_pos⟩
  by_cases hS : ∃ K, IsCCSDisk K ∧ rein_NP K
  swap
  · simp only [not_exists, not_and] at hS
    exact ⟨_, hsq, fun K' hK' ↦ (rein_glpd_le_one hsq).trans (rein_one_le_glpd hK' (hS K' hK'))⟩
  obtain ⟨K₁, hK₁, hnp₁⟩ := hS
  set V := {d | ∃ K, IsCCSDisk K ∧ rein_NP K ∧ greatestLatticePackingDensity K = d} with hV
  have hVne : V.Nonempty := ⟨_, K₁, hK₁, hnp₁, rfl⟩
  have hVbdd : BddBelow V := ⟨0, fun _ ⟨K, _, _, hd⟩ ↦ hd ▸ rein_glpd_nonneg K⟩
  set m := sInf V with hm
  have hm0 : 0 ≤ m := le_csInf hVne (fun _ ⟨K, _, _, hd⟩ ↦ hd ▸ rein_glpd_nonneg K)
  have hseq : ∀ n : ℕ, ∃ K, IsCCSDisk K ∧ rein_NP K ∧
      greatestLatticePackingDensity K < m + 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨_, ⟨K, hK, hnp, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hVne
      (lt_add_of_pos_right m (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)))
    exact ⟨K, hK, hnp, hlt⟩
  choose K₀ hK₀ hnp₀ hlt₀ using hseq
  -- the affine normalization
  have hnorm : ∀ n, ∃ K, IsCCSDisk K ∧
      (∃ w, IsLeastAreaHexagon K w ∧ ∀ j, hexMidpoint w j = sixthRoot j) ∧
      volume.real K / (2 * √3) = greatestLatticePackingDensity (K₀ n) := by
    intro n
    obtain ⟨v, hv⟩ := rein_exists_least (hK₀ n) (hnp₀ n)
    obtain ⟨e, d, he, hme⟩ := rein_normalize hv
    have hw := rein_isLeastAreaHexagon_comp he hv
    have hwm : ∀ j, hexMidpoint (fun k ↦ e (v k)) j = sixthRoot j := fun j ↦ by
      rw [rein_hexMidpoint_comp, hme]
    refine ⟨e '' K₀ n, rein_isCCSDisk_image (hK₀ n), ⟨_, hw, hwm⟩, ?_⟩
    rw [rein_glpd_eq (hK₀ n) hv, ← rein_volume_std hw.1 hwm, rein_hexagonOf_comp,
      rein_real_image he, rein_real_image he, mul_div_mul_left _ _ he.pos.ne']
  choose K hK hstd hdens using hnorm
  have hmem6 : ∀ n j, sixthRoot j ∈ K n := fun n j ↦ by
    obtain ⟨w, hw, hmw⟩ := hstd n
    rw [← hmw j]; exact rein_frontier_subset (hK n) (rein_hexMidpoint_mem_frontier (hK n) hw j)
  have hball : ∀ n, Metric.ball (0 : Fin 2 → ℝ) (1 / 3) ⊆ K n := fun n ↦
    rein_ball_std (hK n) (hmem6 n)
  have hR : ∀ n, K n ⊆ Metric.closedBall 0 36 := fun n ↦ by
    obtain ⟨w, hw, hmw⟩ := hstd n
    exact rein_bound_std hw hmw (hball n)
  -- Blaschke selection
  obtain ⟨Ks, hKs, -, φ, hφ, hconv⟩ := rein_blaschke hK (by norm_num) hball hR
  -- every hexagon circumscribing the limit has area at least `2√3`
  have hhex : ∀ w, IsCSHexagon w → Ks ⊆ hexagonOf w → 2 * √3 ≤ volume.real (hexagonOf w) := by
    intro w hw hKsw
    apply rein_le_of_forall_sq
    intro ε hε
    have hε1 : (0 : ℝ) < 1 + ε := by linarith
    obtain ⟨n, hn⟩ := (hconv ε hε).exists
    obtain ⟨wn, hwn, hmn⟩ := hstd (φ n)
    have he := rein_posLin_sc hε1
    have hw' := rein_isCSHexagon_comp he hw
    have hsub : K (φ n) ⊆ hexagonOf (fun k ↦ rein_sc (1 + ε) hε1.ne' (w k)) := by
      rw [rein_hexagonOf_comp]
      exact fun z hz ↦ rein_mem_sc_image hε1.ne' (hKsw (hn.1 z hz))
    have := rein_least_le hwn hw' hsub
    rwa [rein_volume_std hwn.1 hmn, rein_hexagonOf_comp, rein_real_image he] at this
  -- the area of the limit is at most `2√3 m`
  have hvol : volume.real Ks / (2 * √3) ≤ m := by
    apply rein_le_of_forall_sq
    intro ε hε
    have hε1 : (0 : ℝ) < 1 + ε := by linarith
    have he := rein_posLin_sc hε1
    have hlim : Tendsto (fun n ↦ (1 + ε) ^ 2 * (m + 1 / ((φ n : ℝ) + 1))) atTop
        (𝓝 ((1 + ε) ^ 2 * m)) := by
      have h1 : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h3 := ((h1.comp hφ.tendsto_atTop).const_add m).const_mul ((1 + ε) ^ 2)
      simpa using h3
    refine ge_of_tendsto hlim ((hconv ε hε).mono fun n hn ↦ ?_)
    have hsub : Ks ⊆ rein_sc (1 + ε) hε1.ne' '' K (φ n) := fun z hz ↦
      rein_mem_sc_image hε1.ne' (hn.2 z hz)
    have h1 : volume.real Ks ≤ (1 + ε) ^ 2 * volume.real (K (φ n)) := by
      rw [← rein_real_image he]
      exact measureReal_mono hsub
        (((hK (φ n)).2.1.image (rein_sc (1 + ε) hε1.ne').continuous).measure_lt_top).ne
    have h2 := hlt₀ (φ n)
    rw [← hdens (φ n)] at h2
    have hpos : (0 : ℝ) < 2 * √3 := by positivity
    rw [div_lt_iff₀ hpos] at h2
    rw [div_le_iff₀ hpos]
    nlinarith [mul_le_mul_of_nonneg_left h2.le (sq_nonneg (1 + ε))]
  refine ⟨Ks, hKs, fun K' hK' ↦ ?_⟩
  have hglpd : greatestLatticePackingDensity Ks ≤ volume.real Ks / (2 * √3) :=
    rein_glpd_le hKs (by positivity) hhex
  by_cases hK'np : rein_NP K'
  · exact hglpd.trans (hvol.trans (csInf_le hVbdd ⟨K', hK', hK'np, rfl⟩))
  · have hm1 : m ≤ 1 := (csInf_le hVbdd ⟨K₁, hK₁, hnp₁, rfl⟩).trans (rein_glpd_le_one hK₁)
    exact hglpd.trans (hvol.trans (hm1.trans (rein_one_le_glpd hK' hK'np)))


/-! ### Reinhardt's lemmas on the worst disk -/

/-- **Lemma 2.2.5** (`lem:no-corner`). A disk `K_min` with the worst greatest density lattice
packing exists. `K_min` has no corners, that is, there is a unique support line to `K_min` at each
boundary point. Moreover, the support line of each boundary point of `K_min` contains an edge of
some critical hexagon.

Existence is the book's argument: Reinhardt's use of the Blaschke selection theorem
(`rein_exists_worst`).

Departure from the paper: the book proves the other two claims by shaving, which has a gap.
Shaving `K` near a boundary point only shows that the part `ℓ ∩ K` of `K` on a support line `ℓ`
meets the boundary of some critical hexagon. This gives nothing at an endpoint of a segment of the
boundary lying on an edge of a critical hexagon away from the edge's midpoint, and the book's step
"each endpoint of the segment is the midpoint of an edge of a critical hexagon, for otherwise it
can be shaved" cannot be repaired along its lines without a quantitative expansion that the book
does not have. We follow Mahler's lattice route instead:
1. `K_min` is irreducible in Mahler's sense (`irr_isIrreducible_of_worst`): since
   `δ_L(K) = area(K)/(4Δ(K))` (`irr_glpd_eq`; `K + L` is a packing iff `½L` is `K`-admissible), a
   proper symmetric convex subdomain with the same `Δ` would have a smaller density. `K_min` is
   not a parallelogram (`irr_not_isParallelogram_of_worst`: the Euclidean disk has `δ_L < 1`).
2. Mahler's Lemma 3 (`External.mahler_irreducible`, by shaving along `±ℓ`): every support line `ℓ`
   passes through a point `x` of a critical lattice, one of the six points `s_j` of Mahler's
   Lemma 2.
3. Mahler's Theorem 2 (`External.mahler_1947`): `ℓ` is the only support line at `x`, and it is the
   line of an edge of the hexagon bounded by the support lines at the `s_j`, which contains `K`
   and has area at most `4Δ(K)` (`irr_main`). Every centrally symmetric hexagon around `K` has
   area at least `4Δ(K)` (its lattice tiling, `rein_hex_lattice`, packs `K`), so this hexagon is
   critical.

No corners: if `{b · x = 1}` and `{c · x = 1}` are support lines at `u`, the support line
`{(b + c)/2 · x = 1}` at `u` passes through a point `x` of a critical lattice, `x` lies on both
lines, and there is only one support line at `x`. -/
theorem lemma2_2_5 :
    (∃ K, IsWorstLatticeDisk K) ∧
      ∀ K, IsWorstLatticeDisk K →
        (∀ u ∈ frontier K, ∃! ℓ, IsSupportLine K ℓ ∧ u ∈ ℓ) ∧
        ∀ u ∈ frontier K, ∀ ℓ, IsSupportLine K ℓ → u ∈ ℓ →
          ∃ v, IsLeastAreaHexagon K v ∧ ∃ j, segment ℝ (v j) (v (j + 1)) ⊆ ℓ := by
  -- existence, by the Blaschke selection theorem
  refine ⟨rein_exists_worst, fun K hK ↦ ?_⟩
  have hK1 : IsCCSDisk K := hK.1
  -- every centrally symmetric hexagon around `K` has area at least `4Δ(K)`: its lattice tiling
  -- packs `K`, and `K + L` is a packing only if `½L` is `K`-admissible
  have hlow : ∀ w, IsCSHexagon w → K ⊆ hexagonOf w →
      4 * External.MinkowskiMahler.minimalDeterminant K ≤ volume.real (hexagonOf w) := by
    intro w hw hKw
    obtain ⟨L0, hL0, hdet0, hpack0⟩ := rein_hex_lattice hw
    rw [← hdet0]
    exact irr_four_mul_le_latticeDet hK1 hL0 (rein_isLatticePacking_mono hKw hpack0)
  -- a support line `{b · x = 1}` passes through a point `x` of `K` at which it is the only
  -- support line, and it contains an edge of a critical hexagon (Mahler's Lemma 3 and Theorem 2)
  have key : ∀ b : Fin 2 → ℝ, (∀ x ∈ K, b ⬝ᵥ x ≤ 1) → (∃ u ∈ K, b ⬝ᵥ u = 1) →
      ∃ x ∈ K, b ⬝ᵥ x = 1 ∧ (∀ c : Fin 2 → ℝ, (∀ y ∈ K, c ⬝ᵥ y ≤ 1) → c ⬝ᵥ x = 1 → c = b) ∧
        ∃ v, IsLeastAreaHexagon K v ∧ ∃ j, segment ℝ (v j) (v (j + 1)) ⊆ {y | b ⬝ᵥ y = 1} := by
    intro b hb hbu
    obtain ⟨x, hxK, hbx, huniq, w₀, w₁, w₂, j, hc, hstrip, hsum, hj0, hj1⟩ :=
      irr_main hK hb hbu
    have hC : rein_HexCond w₀ w₁ w₂ :=
      ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2⟩
    refine ⟨x, hxK, hbx, huniq, rein_hex3 w₀ w₁ w₂, ⟨rein_isCSHexagon_iff_hexCond.2 hC,
      fun y hy ↦ (rein_mem_hexagonOf_iff_strips hC).2 (hstrip y hy), fun w hw hKw ↦ ?_⟩, j, ?_⟩
    · rw [rein_volume_hexagonOf_hex3' hC,
        ← ENNReal.ofReal_toReal (rein_isCompact_hexagonOf w).measure_lt_top.ne]
      exact ENNReal.ofReal_le_ofReal (hsum.trans (hlow w hw hKw))
    · rintro y ⟨s, t, hs, ht, hst, rfl⟩
      change b ⬝ᵥ (s • irr_hex3 w₀ w₁ w₂ j + t • irr_hex3 w₀ w₁ w₂ (j + 1)) = 1
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul, hj0, hj1, smul_eq_mul, smul_eq_mul,
        mul_one, mul_one, hst]
  refine ⟨fun u hu ↦ ?_, fun u hu ℓ hℓ huℓ ↦ ?_⟩
  · -- a support line at `u`
    obtain ⟨b, hb, hbu⟩ := irr_exists_normal hK1 hu
    have huK := rein_frontier_subset hK1 hu
    have hb0 : b ≠ 0 := by rintro rfl; simp at hbu
    refine ⟨{y | b ⬝ᵥ y = 1}, ⟨rein_isSupportLine_of hb0 hb huK hbu, hbu⟩, ?_⟩
    -- uniqueness: for two support lines `{b · x = 1}`, `{c · x = 1}` at `u`, the support line
    -- `{(b + c)/2 · x = 1}` at `u` passes through a point of a critical lattice which lies on
    -- both lines, and at which there is only one support line
    rintro ℓ ⟨hℓ, huℓ⟩
    obtain ⟨c, rfl, hc⟩ := irr_normal hK1 (rein_supportLine_normal hℓ)
    have hcu : c ⬝ᵥ u = 1 := huℓ
    set d : Fin 2 → ℝ := (1 / 2 : ℝ) • (b + c) with hd
    have hdK : ∀ y ∈ K, d ⬝ᵥ y ≤ 1 := by
      intro y hy
      rw [hd, smul_dotProduct, add_dotProduct, smul_eq_mul]
      linarith [hb y hy, hc y hy]
    have hdu : d ⬝ᵥ u = 1 := by
      rw [hd, smul_dotProduct, add_dotProduct, smul_eq_mul, hbu, hcu]; norm_num
    obtain ⟨x, hxK, hdx, huniq, -⟩ := key d hdK ⟨u, huK, hdu⟩
    rw [hd, smul_dotProduct, add_dotProduct, smul_eq_mul] at hdx
    have hbx : b ⬝ᵥ x = 1 := by linarith [hb x hxK, hc x hxK]
    have hcx : c ⬝ᵥ x = 1 := by linarith [hb x hxK, hc x hxK]
    have e1 := huniq c hc hcx
    have e2 := huniq b hb hbx
    rw [e1, e2]
  · -- every support line contains an edge of a critical hexagon
    obtain ⟨b, rfl, hb⟩ := irr_normal hK1 (rein_supportLine_normal hℓ)
    obtain ⟨-, -, -, -, v, hv, j, hj⟩ := key b hb ⟨u, rein_frontier_subset hK1 hu, huℓ⟩
    exact ⟨v, hv, j, hj⟩

/-- The triangle `T_j` with vertices `s_j*`, `s_{j+1}*` and `s_j* + s_{j+1}*` (§2.2). -/
noncomputable def sixthTriangle (j : ZMod 6) : Set (Fin 2 → ℝ) :=
  convexHull ℝ {sixthRoot j, sixthRoot (j + 1), sixthRoot j + sixthRoot (j + 1)}

/-! ## Helper lemmas: the triangles `T_j` -/

/-! ### The sixth roots of unity and the triangles `T_j` -/

/-- The triangle with vertices `p, q, p + q` in the coordinates `α = det(x, q)/det(p, q)`,
`β = det(p, x)/det(p, q)` (`x = α p + β q`): `α ≤ 1`, `β ≤ 1`, `α + β ≥ 1`. -/
lemma rein_mem_convexHull_triple {p q x : Fin 2 → ℝ} (hpq : 0 < det2 p q) :
    x ∈ convexHull ℝ {p, q, p + q} ↔
      det2 x q ≤ det2 p q ∧ det2 p x ≤ det2 p q ∧ det2 p q ≤ det2 x q + det2 p x := by
  constructor
  · intro hx
    refine (convexHull_min (t := {y : Fin 2 → ℝ | det2 y q ≤ det2 p q ∧ det2 p y ≤ det2 p q ∧
      det2 p q ≤ det2 y q + det2 p y}) ?_ ?_) hx
    · intro y hy
      simp only [mem_insert_iff, mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl <;> simp only [mem_ofPred_eq] <;>
        simp only [det2, Pi.add_apply] at hpq ⊢ <;> refine ⟨?_, ?_, ?_⟩ <;> nlinarith
    · have : {y : Fin 2 → ℝ | det2 y q ≤ det2 p q ∧ det2 p y ≤ det2 p q ∧
          det2 p q ≤ det2 y q + det2 p y} =
          {w | det2 (-q) w ≤ det2 p q} ∩ ({w | det2 p w ≤ det2 p q} ∩
            {w | det2 (q - p) w ≤ -det2 p q}) := by
        ext y
        simp only [mem_ofPred_eq, mem_inter_iff, det2, Pi.sub_apply, Pi.neg_apply]
        constructor <;> rintro ⟨h1, h2, h3⟩ <;> refine ⟨?_, ?_, ?_⟩ <;> linarith
      rw [this]
      exact (convex_halfSpace_le (rein_isLinearMap_det2 _) _).inter
        ((convex_halfSpace_le (rein_isLinearMap_det2 _) _).inter
          (convex_halfSpace_le (rein_isLinearMap_det2 _) _))
  · rintro ⟨h1, h2, h3⟩
    set D := det2 p q
    have hcr := rein_cramer p q x
    set α := det2 x q / D with hα
    set β := det2 p x / D with hβ
    have hα1 : α ≤ 1 := by rw [hα, div_le_one hpq]; exact h1
    have hβ1 : β ≤ 1 := by rw [hβ, div_le_one hpq]; exact h2
    have hαβ : 1 ≤ α + β := by rw [hα, hβ, ← add_div, le_div_iff₀ hpq]; linarith
    have key : x = (1 - β) • p + (1 - α) • q + (α + β - 1) • (p + q) := by
      have hx : x = D⁻¹ • (det2 x q • p + det2 p x • q) := by
        rw [← hcr, smul_smul, inv_mul_cancel₀ hpq.ne', one_smul]
      conv_lhs => rw [hx]
      ext i
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, hα, hβ]
      field_simp
      ring
    rw [key]
    have := (convex_convexHull ℝ ({p, q, p + q} : Set (Fin 2 → ℝ))).sum_mem
      (t := Finset.univ) (w := ![1 - β, 1 - α, α + β - 1]) (z := ![p, q, p + q])
      (by intro i _; fin_cases i <;> simp <;> linarith)
      (by simp only [Fin.sum_univ_three, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]; ring)
      (by intro i _; apply subset_convexHull; fin_cases i <;> simp)
    simpa [Fin.sum_univ_three, add_assoc] using this


/-- The triangle with vertices `p, q, p + q` in the coordinates `x = α p + β q`. -/
lemma rein_mem_convexHull_triple' {p q x : Fin 2 → ℝ} (hpq : 0 < det2 p q) :
    x ∈ convexHull ℝ {p, q, p + q} ↔
      det2 x q / det2 p q ≤ 1 ∧ det2 p x / det2 p q ≤ 1 ∧
        1 ≤ det2 x q / det2 p q + det2 p x / det2 p q := by
  rw [rein_mem_convexHull_triple hpq, div_le_one hpq, div_le_one hpq, ← add_div,
    le_div_iff₀ hpq, one_mul]

/-- The interior of the triangle with vertices `p, q, p + q`. -/
lemma rein_mem_interior_convexHull_triple {p q x : Fin 2 → ℝ} (hpq : 0 < det2 p q) :
    x ∈ interior (convexHull ℝ {p, q, p + q}) ↔
      det2 x q / det2 p q < 1 ∧ det2 p x / det2 p q < 1 ∧
        1 < det2 x q / det2 p q + det2 p x / det2 p q := by
  rw [div_lt_one hpq, div_lt_one hpq, ← add_div, lt_div_iff₀ hpq, one_mul]
  constructor
  · intro hx
    obtain ⟨t1, ht1, h1⟩ := rein_exists_add_smul_mem hx p
    obtain ⟨t2, ht2, h2⟩ := rein_exists_add_smul_mem hx q
    obtain ⟨t3, ht3, h3⟩ := rein_exists_add_smul_mem hx (-(p + q))
    rw [rein_mem_convexHull_triple hpq] at h1 h2 h3
    have e1 : det2 (x + t1 • p) q = det2 x q + t1 * det2 p q := by
      simp only [det2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    have e2 : det2 p (x + t2 • q) = det2 p x + t2 * det2 p q := by
      simp only [det2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    have e3 : det2 (x + t3 • -(p + q)) q + det2 p (x + t3 • -(p + q)) =
        det2 x q + det2 p x - 2 * t3 * det2 p q := by
      simp only [det2, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]; ring
    have := mul_pos ht1 hpq
    have := mul_pos ht2 hpq
    have := mul_pos ht3 hpq
    refine ⟨by linarith [h1.1], by linarith [h2.2.1], by linarith [h3.2.2]⟩
  · intro hx
    have hsub : {y : Fin 2 → ℝ | det2 y q < det2 p q ∧ det2 p y < det2 p q ∧
        det2 p q < det2 y q + det2 p y} ⊆ interior (convexHull ℝ {p, q, p + q}) := by
      refine interior_maximal (fun y hy ↦ ?_) ?_
      · rw [rein_mem_convexHull_triple hpq]
        obtain ⟨h1, h2, h3⟩ := hy
        exact ⟨h1.le, h2.le, h3.le⟩
      · have c1 := rein_continuous_det2_right q
        have c2 := rein_continuous_det2_left p
        exact (isOpen_lt c1 continuous_const).inter ((isOpen_lt c2 continuous_const).inter
          (isOpen_lt continuous_const (c1.add c2)))
    exact hsub hx

/-! ### Coordinates with respect to `s₀*, s₁*` -/

/-- The first coordinate of `x = A s₀* + B s₁*`. -/
noncomputable def rein_cA (x : Fin 2 → ℝ) : ℝ := det2 x (sixthRoot 1) / (√3 / 2)

/-- The second coordinate of `x = A s₀* + B s₁*`. -/
noncomputable def rein_cB (x : Fin 2 → ℝ) : ℝ := det2 (sixthRoot 0) x / (√3 / 2)

lemma rein_cA_eq (x : Fin 2 → ℝ) : rein_cA x = x 0 - x 1 / √3 := by
  have h3 := rein_sqrt3_sq
  have h3' := rein_sqrt3_pos
  simp only [rein_cA, det2, rein_sixthRoot_one]
  simp
  field_simp

lemma rein_cB_eq (x : Fin 2 → ℝ) : rein_cB x = 2 * x 1 / √3 := by
  have h3' := rein_sqrt3_pos
  simp only [rein_cB, det2, rein_sixthRoot_zero]
  simp
  field_simp

lemma rein_eq_coord (x : Fin 2 → ℝ) :
    x = ![rein_cA x + rein_cB x / 2, rein_cB x * (√3 / 2)] := by
  have h3' := rein_sqrt3_pos
  have h3 := rein_sqrt3_sq
  rw [rein_cA_eq, rein_cB_eq]
  ext i; fin_cases i
  · simp; field_simp; ring
  · simp; field_simp

lemma rein_det2_coord (x y : Fin 2 → ℝ) :
    det2 x y = √3 / 2 * (rein_cA x * rein_cB y - rein_cB x * rein_cA y) := by
  have h3' := rein_sqrt3_pos
  have h3 := rein_sqrt3_sq
  rw [rein_cA_eq, rein_cB_eq, rein_cA_eq, rein_cB_eq]
  simp only [det2]
  field_simp
  ring_nf

lemma rein_coord_ext {x y : Fin 2 → ℝ} (hA : rein_cA x = rein_cA y) (hB : rein_cB x = rein_cB y) :
    x = y := by
  rw [rein_eq_coord x, rein_eq_coord y, hA, hB]

lemma rein_cA_add (x y : Fin 2 → ℝ) : rein_cA (x + y) = rein_cA x + rein_cA y := by
  simp only [rein_cA_eq, Pi.add_apply]; ring
lemma rein_cB_add (x y : Fin 2 → ℝ) : rein_cB (x + y) = rein_cB x + rein_cB y := by
  simp only [rein_cB_eq, Pi.add_apply]; ring
lemma rein_cA_sub (x y : Fin 2 → ℝ) : rein_cA (x - y) = rein_cA x - rein_cA y := by
  simp only [rein_cA_eq, Pi.sub_apply]; ring
lemma rein_cB_sub (x y : Fin 2 → ℝ) : rein_cB (x - y) = rein_cB x - rein_cB y := by
  simp only [rein_cB_eq, Pi.sub_apply]; ring
lemma rein_cA_neg (x : Fin 2 → ℝ) : rein_cA (-x) = -rein_cA x := by
  simp only [rein_cA_eq, Pi.neg_apply]; ring
lemma rein_cB_neg (x : Fin 2 → ℝ) : rein_cB (-x) = -rein_cB x := by
  simp only [rein_cB_eq, Pi.neg_apply]; ring
lemma rein_cA_smul (r : ℝ) (x : Fin 2 → ℝ) : rein_cA (r • x) = r * rein_cA x := by
  simp only [rein_cA_eq, Pi.smul_apply, smul_eq_mul]; ring
lemma rein_cB_smul (r : ℝ) (x : Fin 2 → ℝ) : rein_cB (r • x) = r * rein_cB x := by
  simp only [rein_cB_eq, Pi.smul_apply, smul_eq_mul]; ring

lemma rein_continuous_cA : Continuous rein_cA := by
  unfold rein_cA; exact (rein_continuous_det2_right _).div_const _
lemma rein_continuous_cB : Continuous rein_cB := by
  unfold rein_cB; exact (rein_continuous_det2_left _).div_const _

/-- The coordinates of the sixth roots of unity: `(1, 0), (0, 1), (-1, 1), (-1, 0), (0, -1),
(1, -1)`. -/
lemma rein_coord_sixthRoot :
    (rein_cA (sixthRoot 0) = 1 ∧ rein_cB (sixthRoot 0) = 0) ∧
    (rein_cA (sixthRoot 1) = 0 ∧ rein_cB (sixthRoot 1) = 1) ∧
    (rein_cA (sixthRoot 2) = -1 ∧ rein_cB (sixthRoot 2) = 1) ∧
    (rein_cA (sixthRoot 3) = -1 ∧ rein_cB (sixthRoot 3) = 0) ∧
    (rein_cA (sixthRoot 4) = 0 ∧ rein_cB (sixthRoot 4) = -1) ∧
    (rein_cA (sixthRoot 5) = 1 ∧ rein_cB (sixthRoot 5) = -1) := by
  have h3' := rein_sqrt3_pos
  simp only [rein_cA_eq, rein_cB_eq, rein_sixthRoot_zero, rein_sixthRoot_one, rein_sixthRoot_two,
    rein_sixthRoot_three, rein_sixthRoot_four, rein_sixthRoot_five]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, cons_val_zero, cons_val_one,
    cons_val_fin_one, zero_div, sub_zero, mul_zero, and_self, one_div, mul_neg, true_and]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (try constructor) <;> field_simp <;> ring

/-- The triangles `T_k` in coordinates. -/
def rein_InT (k : ZMod 6) (A B : ℝ) : Prop :=
  (![A ≤ 1 ∧ B ≤ 1 ∧ 1 ≤ A + B,
    A + B ≤ 1 ∧ -1 ≤ A ∧ 1 ≤ B,
    B ≤ 1 ∧ -1 ≤ A + B ∧ A ≤ -1,
    -1 ≤ A ∧ -1 ≤ B ∧ A + B ≤ -1,
    -1 ≤ A + B ∧ A ≤ 1 ∧ B ≤ -1,
    -1 ≤ B ∧ A + B ≤ 1 ∧ 1 ≤ A] : Fin 6 → Prop) k

/-- The interiors of the triangles `T_k` in coordinates. -/
def rein_InTo (k : ZMod 6) (A B : ℝ) : Prop :=
  (![A < 1 ∧ B < 1 ∧ 1 < A + B,
    A + B < 1 ∧ -1 < A ∧ 1 < B,
    B < 1 ∧ -1 < A + B ∧ A < -1,
    -1 < A ∧ -1 < B ∧ A + B < -1,
    -1 < A + B ∧ A < 1 ∧ B < -1,
    -1 < B ∧ A + B < 1 ∧ 1 < A] : Fin 6 → Prop) k

section InT
variable (A B : ℝ)
lemma rein_InT_zero : rein_InT 0 A B ↔ A ≤ 1 ∧ B ≤ 1 ∧ 1 ≤ A + B := Iff.rfl
lemma rein_InT_one : rein_InT 1 A B ↔ A + B ≤ 1 ∧ -1 ≤ A ∧ 1 ≤ B := Iff.rfl
lemma rein_InT_two : rein_InT 2 A B ↔ B ≤ 1 ∧ -1 ≤ A + B ∧ A ≤ -1 := Iff.rfl
lemma rein_InT_three : rein_InT 3 A B ↔ -1 ≤ A ∧ -1 ≤ B ∧ A + B ≤ -1 := Iff.rfl
lemma rein_InT_four : rein_InT 4 A B ↔ -1 ≤ A + B ∧ A ≤ 1 ∧ B ≤ -1 := Iff.rfl
lemma rein_InT_five : rein_InT 5 A B ↔ -1 ≤ B ∧ A + B ≤ 1 ∧ 1 ≤ A := Iff.rfl
lemma rein_InTo_zero : rein_InTo 0 A B ↔ A < 1 ∧ B < 1 ∧ 1 < A + B := Iff.rfl
lemma rein_InTo_one : rein_InTo 1 A B ↔ A + B < 1 ∧ -1 < A ∧ 1 < B := Iff.rfl
lemma rein_InTo_two : rein_InTo 2 A B ↔ B < 1 ∧ -1 < A + B ∧ A < -1 := Iff.rfl
lemma rein_InTo_three : rein_InTo 3 A B ↔ -1 < A ∧ -1 < B ∧ A + B < -1 := Iff.rfl
lemma rein_InTo_four : rein_InTo 4 A B ↔ -1 < A + B ∧ A < 1 ∧ B < -1 := Iff.rfl
lemma rein_InTo_five : rein_InTo 5 A B ↔ -1 < B ∧ A + B < 1 ∧ 1 < A := Iff.rfl
end InT

lemma rein_sixthTriangle_frame (k : ZMod 6) (x : Fin 2 → ℝ) :
    det2 x (sixthRoot (k + 1)) / det2 (sixthRoot k) (sixthRoot (k + 1)) =
      rein_cA x * rein_cB (sixthRoot (k + 1)) - rein_cB x * rein_cA (sixthRoot (k + 1)) ∧
    det2 (sixthRoot k) x / det2 (sixthRoot k) (sixthRoot (k + 1)) =
      rein_cA (sixthRoot k) * rein_cB x - rein_cB (sixthRoot k) * rein_cA x := by
  have h3' := rein_sqrt3_pos
  rw [(rein_sixthRoot_rel k).2.2, rein_det2_coord, rein_det2_coord]
  constructor <;> field_simp

lemma rein_mem_sixthTriangle (k : ZMod 6) (x : Fin 2 → ℝ) :
    x ∈ sixthTriangle k ↔ rein_InT k (rein_cA x) (rein_cB x) := by
  rw [sixthTriangle, rein_mem_convexHull_triple' (rein_det2_sixthRoot_pos k),
    (rein_sixthTriangle_frame k x).1, (rein_sixthTriangle_frame k x).2]
  obtain ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩, ⟨a4, b4⟩, ⟨a5, b5⟩⟩ := rein_coord_sixthRoot
  rcases rein_zmod6_cases k with rfl | rfl | rfl | rfl | rfl | rfl <;> rein_z6 <;>
  simp only [rein_InT_zero, rein_InT_one, rein_InT_two, rein_InT_three, rein_InT_four,
    rein_InT_five, a0, b0, a1, b1, a2, b2, a3, b3, a4, b4, a5, b5] <;>
  constructor <;> rintro ⟨h1, h2, h3⟩ <;> refine ⟨?_, ?_, ?_⟩ <;> linarith

lemma rein_mem_interior_sixthTriangle (k : ZMod 6) (x : Fin 2 → ℝ) :
    x ∈ interior (sixthTriangle k) ↔ rein_InTo k (rein_cA x) (rein_cB x) := by
  rw [sixthTriangle, rein_mem_interior_convexHull_triple (rein_det2_sixthRoot_pos k),
    (rein_sixthTriangle_frame k x).1, (rein_sixthTriangle_frame k x).2]
  obtain ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩, ⟨a4, b4⟩, ⟨a5, b5⟩⟩ := rein_coord_sixthRoot
  rcases rein_zmod6_cases k with rfl | rfl | rfl | rfl | rfl | rfl <;> rein_z6 <;>
  simp only [rein_InTo_zero, rein_InTo_one, rein_InTo_two, rein_InTo_three, rein_InTo_four,
    rein_InTo_five, a0, b0, a1, b1, a2, b2, a3, b3, a4, b4, a5, b5] <;>
  constructor <;> rintro ⟨h1, h2, h3⟩ <;> refine ⟨?_, ?_, ?_⟩ <;> linarith

/-! ### Weak monotonicity in coordinates -/

/-- The points `z` of the triangles `T_k` with `det(s₀, z) = det(s₀*, s₁*)`, for `s₀ = (p, q)`
in `T₀`, other than `s₀*` and `s₁*` (in coordinates). -/
lemma rein_wm_class (p q a b : ℝ) (h0 : p ≤ 1 ∧ q ≤ 1 ∧ 1 ≤ p + q) (hn1 : p < 1 ∨ 0 < q)
    (hn2 : 0 < p ∨ q < 1) (hL : p * b - q * a = 1) (h : ∃ k, rein_InT k a b) :
    rein_InT 1 a b ∨ rein_InT 2 a b ∨ (p = 1 ∧ a = 0 ∧ b = 1) ∨ (q = 1 ∧ a = -1 ∧ b = 0) := by
  obtain ⟨h1, h2, h3⟩ := h0
  have hp : 0 ≤ p := by linarith
  have hq : 0 ≤ q := by linarith
  obtain ⟨k, hk⟩ := h
  rcases rein_zmod6_cases k with rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [rein_InT_zero, rein_InT_one, rein_InT_two, rein_InT_three, rein_InT_four,
    rein_InT_five] at hk ⊢
  · obtain ⟨b1, b2, b3⟩ := hk
    right; right; left
    have e1 : p * (1 - b) ≥ 0 := mul_nonneg hp (by linarith)
    have e2 : q * a ≥ 0 := mul_nonneg hq (by linarith)
    have hp1 : p = 1 := by nlinarith
    subst hp1
    have hb : b = 1 := by nlinarith
    subst hb
    have hqa : q * a = 0 := by linarith
    rcases hn1 with hn1 | hn1
    · linarith
    · exact ⟨rfl, by rcases mul_eq_zero.1 hqa with h | h <;> [linarith; exact h], rfl⟩
  · exact Or.inl hk
  · exact Or.inr (Or.inl hk)
  · obtain ⟨b1, b2, b3⟩ := hk
    right; right; right
    have e1 : q * (1 + a) ≥ 0 := mul_nonneg hq (by linarith)
    have e2 : p * b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp (by linarith)
    have hq1 : q = 1 := by nlinarith
    subst hq1
    have ha : a = -1 := by nlinarith
    subst ha
    have hpb : p * b = 0 := by linarith
    rcases hn2 with hn2 | hn2
    · exact ⟨rfl, rfl, by rcases mul_eq_zero.1 hpb with h | h <;> [linarith; exact h]⟩
    · linarith
  · obtain ⟨b1, b2, b3⟩ := hk
    have e1 : p * b ≤ -p := by nlinarith
    have e2 : q * a ≥ 0 := mul_nonneg hq (by linarith)
    exfalso; nlinarith
  · obtain ⟨b1, b2, b3⟩ := hk
    have e1 : p * b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp (by linarith)
    have e2 : q * a ≥ q := by nlinarith
    exfalso; nlinarith

/-- Weak monotonicity in coordinates: if `s₀ = (p, q) ∈ T₀ \ {s₀*, s₁*}`, `s₂ = (x, y)` and
`s₁ = s₀ + s₂` lie in `⋃ T_k`, and `det(s₀, s₂) = det(s₀*, s₁*)`, then `s₁ ∈ T₁` and `s₂ ∈ T₂`. -/
lemma rein_wm_real (p q x y : ℝ) (h0 : p ≤ 1 ∧ q ≤ 1 ∧ 1 ≤ p + q) (hn1 : p < 1 ∨ 0 < q)
    (hn2 : 0 < p ∨ q < 1)
    (hdet : p * y - q * x = 1) (h2 : ∃ k, rein_InT k x y)
    (h1 : ∃ k, rein_InT k (p + x) (q + y)) :
    rein_InT 1 (p + x) (q + y) ∧ rein_InT 2 x y := by
  have c2 := rein_wm_class p q x y h0 hn1 hn2 hdet h2
  have c1 := rein_wm_class p q (p + x) (q + y) h0 hn1 hn2 (by linarith) h1
  obtain ⟨a1, a2, a3⟩ := h0
  simp only [rein_InT_one, rein_InT_two] at c1 c2 ⊢
  rcases c2 with ⟨b1, b2, b3⟩ | ⟨b1, b2, b3⟩ | ⟨b1, b2, b3⟩ | ⟨b1, b2, b3⟩ <;>
  rcases c1 with ⟨d1, d2, d3⟩ | ⟨d1, d2, d3⟩ | ⟨d1, d2, d3⟩ | ⟨d1, d2, d3⟩
  -- s₂ ∈ T₁
  · refine ⟨⟨d1, d2, d3⟩, ?_, ?_, ?_⟩ <;> linarith
  · rcases hn2 with hn2 | hn2 <;> exfalso <;> linarith
  · rcases hn1 with hn1 | hn1 <;> exfalso <;> linarith
  · exfalso; linarith
  -- s₂ ∈ T₂
  · exact ⟨⟨d1, d2, d3⟩, b1, b2, b3⟩
  · -- the determinant condition in the frame `s₂*, s₃*`
    have hpq : p + q = 1 := by linarith
    have hα : q + y = 1 := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 - (q + y) by linarith)
        (show (0 : ℝ) ≤ -x - y by linarith),
        mul_nonneg (show (0 : ℝ) ≤ q + y by linarith) (show (0 : ℝ) ≤ 1 - (-x - y) by linarith),
        mul_nonneg (show (0 : ℝ) ≤ -(p + x) - (q + y) by linarith) (show (0 : ℝ) ≤ y by linarith)]
    have hβ : -(p + x) - (q + y) = 0 ∨ y = 0 := by
      have : (-(p + x) - (q + y)) * y = 0 := by nlinarith
      exact mul_eq_zero.1 this
    rcases hβ with hβ | hβ
    · refine ⟨⟨?_, ?_, ?_⟩, b1, b2, b3⟩ <;> linarith
    · rcases hn2 with hn2 | hn2 <;> exfalso <;> linarith
  · refine ⟨⟨?_, ?_, ?_⟩, b1, b2, b3⟩ <;> linarith
  · exfalso; linarith
  -- s₂ = s₁*
  all_goals first
    | (exfalso; linarith)
    | (refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;> linarith)

/-! ## Helper lemmas: Reinhardt's normal position and the proof of Lemma 2.2.6 -/

/-! ### General facts -/

lemma rein_not_mem_frontier_of_mem_interior {K : Set (Fin 2 → ℝ)} {x : Fin 2 → ℝ}
    (hx : x ∈ interior K) : x ∉ frontier K := fun h ↦ h.2 hx

/-- `α y₁ + β y₂ ∈ interior K` for `y₁, y₂ ∈ K`, `α, β ≥ 0`, `α + β < 1`, when `0` is an interior
point of the convex set `K`. -/
lemma rein_mem_interior_of_combo {K : Set (Fin 2 → ℝ)} (hK : Convex ℝ K)
    (h0 : (0 : Fin 2 → ℝ) ∈ interior K) {y₁ y₂ : Fin 2 → ℝ} (h1 : y₁ ∈ K) (h2 : y₂ ∈ K)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β < 1) : α • y₁ + β • y₂ ∈ interior K := by
  rcases (add_nonneg hα hβ).eq_or_lt with h | h
  · have hα0 : α = 0 := by linarith
    have hβ0 : β = 0 := by linarith
    simp [hα0, hβ0, h0]
  · have hw : (α / (α + β)) • y₁ + (β / (α + β)) • y₂ ∈ K :=
      hK h1 h2 (div_nonneg hα h.le) (div_nonneg hβ h.le) (by field_simp)
    have := hK.combo_interior_self_mem_interior h0 hw (a := 1 - (α + β)) (b := α + β)
      (by linarith) h.le (by ring)
    convert this using 1
    rw [smul_zero, zero_add, smul_add, smul_smul, smul_smul]
    congr 2 <;> field_simp

/-- The open segment `(p, q)` in the coordinates `x = α p + β q`. -/
lemma rein_mem_openSegment_iff {p q x : Fin 2 → ℝ} (hpq : 0 < det2 p q) :
    x ∈ openSegment ℝ p q ↔
      det2 x q + det2 p x = det2 p q ∧ 0 < det2 x q ∧ 0 < det2 p x := by
  constructor
  · rintro ⟨s, t, hs, ht, hst, rfl⟩
    have e1 : det2 (s • p + t • q) q = s * det2 p q := by
      simp only [det2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    have e2 : det2 p (s • p + t • q) = t * det2 p q := by
      simp only [det2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [e1, e2]
    refine ⟨by rw [← add_mul, hst, one_mul], mul_pos hs hpq, mul_pos ht hpq⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨det2 x q / det2 p q, det2 p x / det2 p q, div_pos h2 hpq, div_pos h3 hpq,
      by rw [← add_div, h1, div_self hpq.ne'], ?_⟩
    have hcr := rein_cramer p q x
    ext i
    have hi := congrFun hcr i
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at hi ⊢
    field_simp
    linarith

/-- If a support line of a centrally symmetric convex disk passes through `p` and `q`, with
`det(p, q) > 0`, then `K` lies in the half-plane `{α + β ≤ 1}` of the coordinates
`x = α p + β q`. -/
lemma rein_supportLine_side {K ℓ : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) (hℓ : IsSupportLine K ℓ)
    {p q : Fin 2 → ℝ} (hp : p ∈ ℓ) (hq : q ∈ ℓ) (hpq : 0 < det2 p q) :
    ∀ x ∈ K, det2 x q + det2 p x ≤ det2 p q := by
  obtain ⟨a, ha, c, rfl, hKa⟩ := rein_supportLine_normal hℓ
  simp only [mem_ofPred_eq] at hp hq
  have hc : 0 < c := by
    have h0 := rein_zero_mem_interior hK
    have := hKa 0 (interior_subset h0)
    rcases this.lt_or_eq with h | h
    · simpa using h
    · exfalso
      have hsl : IsSupportLine K {x | a ⬝ᵥ x = c} := hℓ
      exact (rein_mem_frontier_of_supportLine hK.2.1.isClosed hsl (interior_subset h0)
        (by simpa using h)).2 h0
  intro x hx
  have hcr := rein_cramer p q x
  have key : det2 p q * (a ⬝ᵥ x) = (det2 x q + det2 p x) * c := by
    have := congrArg (fun y ↦ a ⬝ᵥ y) hcr
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, hp, hq] at this
    linarith
  have := hKa x hx
  nlinarith

/-- The edge half-plane of a hexagon `v` at the edge `j`, in terms of its midpoint. -/
lemma rein_edge_halfPlane {v : ZMod 6 → Fin 2 → ℝ} (hv : IsCSHexagon v) (j : ZMod 6)
    {x : Fin 2 → ℝ} (hx : x ∈ hexagonOf v) :
    0 ≤ det2 (v (j + 1) - v j) (x - hexMidpoint v j) := by
  have hv' := rein_isCSHexagon_shift hv j
  rw [← rein_hexagonOf_shift v j] at hx
  have h := hv'
  rw [rein_eq_hex3 hv'] at h hx
  have := ((rein_mem_hexagonOf_hex3 h x).1 hx).1
  simp only [zero_add, show (1 : ZMod 6) + j = j + 1 by ring] at this
  have e : det2 (v (j + 1) - v j) (x - hexMidpoint v j) =
      det2 (v (j + 1) - v j) (x - v j) := by
    simp only [hexMidpoint, midpoint_eq_smul_add, det2, Pi.sub_apply, Pi.smul_apply,
      Pi.add_apply, smul_eq_mul, invOf_eq_inv]
    ring
  rw [e]; exact this

/-- The bound `α ≤ 1` from the edge of a circumscribed hexagon through `m`. -/
lemma rein_edge_bound {K : Set (Fin 2 → ℝ)} {v : ZMod 6 → Fin 2 → ℝ} (hv : IsCSHexagon v)
    (hKv : K ⊆ hexagonOf v) (j : ZMod 6) {e x : Fin 2 → ℝ} (he : e ∈ K)
    (hme : hexMidpoint v j - e ∈ K) (hx : x ∈ K) (hmx : 0 ≤ det2 (hexMidpoint v j) x)
    (hD : 0 < det2 (hexMidpoint v j) e) :
    det2 x e ≤ det2 (hexMidpoint v j) e := by
  set m := hexMidpoint v j with hm
  set d := v (j + 1) - v j
  have hP : det2 d m < 0 := by
    have h1 := (hv j).2.1
    simp only [d, hm, hexMidpoint, midpoint_eq_smul_add, det2, Pi.sub_apply, Pi.smul_apply,
      Pi.add_apply, smul_eq_mul, invOf_eq_inv] at h1 ⊢
    nlinarith
  have h1 := rein_edge_halfPlane hv j (hKv he)
  have h2 := rein_edge_halfPlane hv j (hKv hme)
  have h3 := rein_edge_halfPlane hv j (hKv hx)
  rw [rein_det2_sub_right] at h1 h2 h3
  rw [rein_det2_sub_right] at h2
  have hcr := rein_cramer m e x
  have key : det2 m e * det2 d x = det2 x e * det2 d m + det2 m x * det2 d e := by
    have := congrArg (det2 d) hcr
    simp only [rein_det2_add_right, rein_det2_smul_right] at this
    linarith
  nlinarith [mul_nonneg hmx (show 0 ≤ -det2 d e by linarith)]

/-- The bound `β ≤ 1` from the edge of a circumscribed hexagon through `m`. -/
lemma rein_edge_bound' {K : Set (Fin 2 → ℝ)} {v : ZMod 6 → Fin 2 → ℝ} (hv : IsCSHexagon v)
    (hKv : K ⊆ hexagonOf v) (j : ZMod 6) {e x : Fin 2 → ℝ} (he : e ∈ K)
    (hme : hexMidpoint v j - e ∈ K) (hx : x ∈ K) (hmx : 0 ≤ det2 x (hexMidpoint v j))
    (hD : 0 < det2 e (hexMidpoint v j)) :
    det2 e x ≤ det2 e (hexMidpoint v j) := by
  set m := hexMidpoint v j with hm
  set d := v (j + 1) - v j
  have hP : det2 d m < 0 := by
    have h1 := (hv j).2.1
    simp only [d, hm, hexMidpoint, midpoint_eq_smul_add, det2, Pi.sub_apply, Pi.smul_apply,
      Pi.add_apply, smul_eq_mul, invOf_eq_inv] at h1 ⊢
    nlinarith
  have h1 := rein_edge_halfPlane hv j (hKv he)
  have h2 := rein_edge_halfPlane hv j (hKv hme)
  have h3 := rein_edge_halfPlane hv j (hKv hx)
  rw [rein_det2_sub_right] at h1 h2 h3
  rw [rein_det2_sub_right] at h2
  have hcr := rein_cramer e m x
  have key : det2 e m * det2 d x = det2 x m * det2 d e + det2 e x * det2 d m := by
    have := congrArg (det2 d) hcr
    simp only [rein_det2_add_right, rein_det2_smul_right] at this
    linarith
  nlinarith [mul_nonneg hmx (show 0 ≤ -det2 d e by linarith)]

/-- The six cones spanned by consecutive sixth roots of unity cover the plane. -/
lemma rein_cone_sixthRoot (x : Fin 2 → ℝ) :
    ∃ j, 0 ≤ det2 (sixthRoot j) x ∧ 0 ≤ det2 x (sixthRoot (j + 1)) := by
  obtain ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩, ⟨a4, b4⟩, ⟨a5, b5⟩⟩ := rein_coord_sixthRoot
  have h3 : 0 < √3 / 2 := by positivity
  simp only [rein_det2_coord]
  set A := rein_cA x
  set B := rein_cB x
  rcases le_or_gt 0 B with hB | hB
  · rcases le_or_gt 0 A with hA | hA
    · exact ⟨0, by rw [a0, b0]; nlinarith, by rein_z6; rw [a1, b1]; nlinarith⟩
    rcases le_or_gt 0 (A + B) with hAB | hAB
    · exact ⟨1, by rw [a1, b1]; nlinarith, by rein_z6; rw [a2, b2]; nlinarith⟩
    · exact ⟨2, by rw [a2, b2]; nlinarith, by rein_z6; rw [a3, b3]; nlinarith⟩
  · rcases le_or_gt A 0 with hA | hA
    · exact ⟨3, by rw [a3, b3]; nlinarith, by rein_z6; rw [a4, b4]; nlinarith⟩
    rcases le_or_gt (A + B) 0 with hAB | hAB
    · exact ⟨4, by rw [a4, b4]; nlinarith, by rein_z6; rw [a5, b5]; nlinarith⟩
    · exact ⟨5, by rw [a5, b5]; nlinarith, by rein_z6; rw [a0, b0]; nlinarith⟩

/-! ### Reinhardt's normal position -/

/-- `K` is in Reinhardt's normal position: it has a critical hexagon whose edge midpoints are the
sixth roots of unity `s_j*`. -/
def rein_Std (K : Set (Fin 2 → ℝ)) : Prop :=
  ∃ w, IsLeastAreaHexagon K w ∧ ∀ j, hexMidpoint w j = sixthRoot j

lemma rein_sixthRoot_mem_frontier {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) (hS : rein_Std K)
    (j : ZMod 6) : sixthRoot j ∈ frontier K := by
  obtain ⟨w, hw, hm⟩ := hS
  rw [← hm j]
  exact rein_hexMidpoint_mem_frontier hK hw j

/-- In normal position, `det(s_j, s_{j+1}) = √3/2` for the edge midpoints of every critical
hexagon. -/
lemma rein_det2_hexMidpoint_std {K : Set (Fin 2 → ℝ)} (hS : rein_Std K)
    {v : ZMod 6 → Fin 2 → ℝ} (hv : IsLeastAreaHexagon K v) (j : ZMod 6) :
    det2 (hexMidpoint v j) (hexMidpoint v (j + 1)) = √3 / 2 := by
  obtain ⟨w, hw, hm⟩ := hS
  rw [rein_det2_hexMidpoint hv.1, rein_det2_hexMidpoint_eq hv hw, hm, hm]
  exact (rein_sixthRoot_rel 0).2.2

/-- In normal position, a boundary point in the cone spanned by `s_j*, s_{j+1}*` lies in
`T_j`. -/
lemma rein_mem_T_of_cone {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) (hS : rein_Std K)
    {x : Fin 2 → ℝ} (hx : x ∈ frontier K) (j : ZMod 6) (h1 : 0 ≤ det2 (sixthRoot j) x)
    (h2 : 0 ≤ det2 x (sixthRoot (j + 1))) : x ∈ sixthTriangle j := by
  have hs := rein_sixthRoot_mem_frontier hK hS
  have hsK : ∀ j, sixthRoot j ∈ K := fun j ↦ rein_frontier_subset hK (hs j)
  obtain ⟨w, hw, hm⟩ := hS
  have hD := rein_det2_sixthRoot_pos j
  have hxK := rein_frontier_subset hK hx
  obtain ⟨r3, r1, -⟩ := rein_sixthRoot_rel j
  -- `s_{j-1}* = s_j* - s_{j+1}*` and `s_{j+2}* = s_{j+1}* - s_j*`
  have hm1 : sixthRoot j - sixthRoot (j + 1) ∈ K := by
    have : sixthRoot j - sixthRoot (j + 1) = sixthRoot (j + 2 + 3) := by
      rw [(rein_sixthRoot_rel (j + 2)).1, r1]; abel
    rw [this]; exact hsK _
  have hm2 : sixthRoot (j + 1) - sixthRoot j ∈ K := by
    have : sixthRoot (j + 1) - sixthRoot j = sixthRoot (j + 2) := by rw [r1]; abel
    rw [this]; exact hsK _
  have b1 : det2 x (sixthRoot (j + 1)) ≤ det2 (sixthRoot j) (sixthRoot (j + 1)) := by
    have := rein_edge_bound hw.1 hw.2.1 j (e := sixthRoot (j + 1)) (hsK _) (by rw [hm]; exact hm1)
      hxK (by rw [hm]; exact h1) (by rw [hm]; exact hD)
    rwa [hm] at this
  have b2 : det2 (sixthRoot j) x ≤ det2 (sixthRoot j) (sixthRoot (j + 1)) := by
    have := rein_edge_bound' hw.1 hw.2.1 (j + 1) (e := sixthRoot j) (hsK _) (by rw [hm]; exact hm2)
      hxK (by rw [hm]; exact h2) (by rw [hm]; exact hD)
    rwa [hm] at this
  rw [sixthTriangle, rein_mem_convexHull_triple hD]
  refine ⟨b1, b2, ?_⟩
  by_contra hlt
  push Not at hlt
  set D := det2 (sixthRoot j) (sixthRoot (j + 1))
  have hint := rein_mem_interior_of_combo hK.1 (rein_zero_mem_interior hK) (hsK j) (hsK (j + 1))
    (div_nonneg h2 hD.le) (div_nonneg h1 hD.le)
    (by rw [← add_div, div_lt_one hD]; linarith)
  have hx' : x = (det2 x (sixthRoot (j + 1)) / D) • sixthRoot j +
      (det2 (sixthRoot j) x / D) • sixthRoot (j + 1) := by
    have hcr := rein_cramer (sixthRoot j) (sixthRoot (j + 1)) x
    ext i
    have hi := congrFun hcr i
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at hi ⊢
    field_simp
    linarith
  rw [← hx'] at hint
  exact rein_not_mem_frontier_of_mem_interior hint hx

/-- In normal position, the boundary of `K` is contained in the union of the triangles `T_j`
(§2.2). -/
lemma rein_frontier_subset_T {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) (hS : rein_Std K)
    {x : Fin 2 → ℝ} (hx : x ∈ frontier K) : ∃ j, x ∈ sixthTriangle j := by
  obtain ⟨j, h1, h2⟩ := rein_cone_sixthRoot x
  exact ⟨j, rein_mem_T_of_cone hK hS hx j h1 h2⟩

lemma rein_frontier_InT {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) (hS : rein_Std K)
    {x : Fin 2 → ℝ} (hx : x ∈ frontier K) : ∃ j, rein_InT j (rein_cA x) (rein_cB x) := by
  obtain ⟨j, hj⟩ := rein_frontier_subset_T hK hS hx
  exact ⟨j, (rein_mem_sixthTriangle j x).1 hj⟩


lemma rein_coord_hexMidpoint_succ {v : ZMod 6 → Fin 2 → ℝ} (hv : IsCSHexagon v) (j : ZMod 6) :
    rein_cA (hexMidpoint v (j + 1)) =
        rein_cA (hexMidpoint v j) + rein_cA (hexMidpoint v (j + 2)) ∧
      rein_cB (hexMidpoint v (j + 1)) =
        rein_cB (hexMidpoint v j) + rein_cB (hexMidpoint v (j + 2)) := by
  rw [rein_hexMidpoint_succ hv j, rein_cA_add, rein_cB_add]; exact ⟨rfl, rfl⟩

/-- The determinant of two points in coordinates, for normal position. -/
lemma rein_det2_coord_eq {x y : Fin 2 → ℝ} (h : det2 x y = √3 / 2) :
    rein_cA x * rein_cB y - rein_cB x * rein_cA y = 1 := by
  rw [rein_det2_coord] at h
  have h3 : 0 < √3 / 2 := by positivity
  nlinarith

/-- `T_{k+3} = -T_k`. -/
lemma rein_InT_add_three (k : ZMod 6) (A B : ℝ) :
    rein_InT (k + 3) (-A) (-B) ↔ rein_InT k A B := by
  rcases rein_zmod6_cases k with rfl | rfl | rfl | rfl | rfl | rfl <;> rein_z6 <;>
  simp only [rein_InT_zero, rein_InT_one, rein_InT_two, rein_InT_three, rein_InT_four,
    rein_InT_five] <;>
  constructor <;> rintro ⟨h1, h2, h3⟩ <;> refine ⟨?_, ?_, ?_⟩ <;> linarith

lemma rein_InTo_add_three (k : ZMod 6) (A B : ℝ) :
    rein_InTo (k + 3) (-A) (-B) ↔ rein_InTo k A B := by
  rcases rein_zmod6_cases k with rfl | rfl | rfl | rfl | rfl | rfl <;> rein_z6 <;>
  simp only [rein_InTo_zero, rein_InTo_one, rein_InTo_two, rein_InTo_three, rein_InTo_four,
    rein_InTo_five] <;>
  constructor <;> rintro ⟨h1, h2, h3⟩ <;> refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- **Weak monotonicity** (proof of Lemma 2.2.6, first paragraph), at the index `0`: if the edge
midpoint `s₀` of a critical hexagon lies in `T₀ \ {s₀*, s₁*}`, then `s_k ∈ T_k` for all `k`. -/
lemma rein_weak_mono {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) (hS : rein_Std K)
    {v : ZMod 6 → Fin 2 → ℝ} (hv : IsLeastAreaHexagon K v)
    (h0 : hexMidpoint v 0 ∈ sixthTriangle 0) (hne0 : hexMidpoint v 0 ≠ sixthRoot 0)
    (hne1 : hexMidpoint v 0 ≠ sixthRoot 1) : ∀ k, hexMidpoint v k ∈ sixthTriangle k := by
  obtain ⟨⟨a0, b0⟩, ⟨a1, b1⟩, -⟩ := rein_coord_sixthRoot
  have hF : ∀ k, hexMidpoint v k ∈ frontier K := rein_hexMidpoint_mem_frontier hK hv
  rw [rein_mem_sixthTriangle, rein_InT_zero] at h0
  set p := rein_cA (hexMidpoint v 0)
  set q := rein_cB (hexMidpoint v 0)
  set x := rein_cA (hexMidpoint v 2)
  set y := rein_cB (hexMidpoint v 2)
  obtain ⟨e1, e2⟩ := rein_coord_hexMidpoint_succ hv.1 0
  rw [zero_add, show (0 : ZMod 6) + 2 = 2 from rfl] at e1 e2
  have hdet := rein_det2_coord_eq (rein_det2_hexMidpoint_std hS hv 0)
  rw [zero_add, e1, e2] at hdet
  have hn1 : p < 1 ∨ 0 < q := by
    by_contra h
    push Not at h
    apply hne0
    apply rein_coord_ext
    · rw [a0]; linarith [h.1]
    · rw [b0]; linarith [h.2]
  have hn2 : 0 < p ∨ q < 1 := by
    by_contra h
    push Not at h
    apply hne1
    apply rein_coord_ext
    · rw [a1]; linarith [h.1]
    · rw [b1]; linarith [h.2]
  have h2 := rein_frontier_InT hK hS (hF 2)
  have h1 := rein_frontier_InT hK hS (hF 1)
  rw [e1, e2] at h1
  obtain ⟨r1, r2⟩ := rein_wm_real p q x y h0 hn1 hn2 (by linarith) h2 h1
  rw [← e1, ← e2, ← rein_mem_sixthTriangle] at r1
  rw [← rein_mem_sixthTriangle] at r2
  have r0 : hexMidpoint v 0 ∈ sixthTriangle 0 := by
    rw [rein_mem_sixthTriangle, rein_InT_zero]; exact h0
  have hneg : ∀ k, hexMidpoint v k ∈ sixthTriangle k →
      hexMidpoint v (k + 3) ∈ sixthTriangle (k + 3) := by
    intro k hk
    rw [rein_mem_sixthTriangle] at hk ⊢
    rw [rein_hexMidpoint_add_three hv.1, rein_cA_neg, rein_cB_neg, rein_InT_add_three]
    exact hk
  intro k
  rcases rein_zmod6_cases k with rfl | rfl | rfl | rfl | rfl | rfl
  · exact r0
  · exact r1
  · exact r2
  · exact hneg 0 r0
  · exact hneg 1 r1
  · exact hneg 2 r2

/-! ### Rotating the normal position -/

/-- The rotation taking `s_j*, s_{j+1}*` to `s₀*, s₁*`. -/
noncomputable def rein_rot (j : ZMod 6) : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ) :=
  rein_frame (sixthRoot j) (sixthRoot (j + 1)) (sixthRoot 0) (sixthRoot 1)
    (rein_det2_sixthRoot_ne j) (rein_det2_sixthRoot_ne 0)

lemma rein_posLin_rot (j : ZMod 6) : rein_PosLin (rein_rot j) 1 := by
  refine ⟨one_pos, fun x y ↦ ?_⟩
  have := rein_det2_frameLin (rein_det2_sixthRoot_ne j) (sixthRoot 0) (sixthRoot 1) x y
  have e1 := (rein_sixthRoot_rel j).2.2
  have e2 := (rein_sixthRoot_rel 0).2.2
  rw [zero_add] at e2
  rw [e1, e2, div_self (by positivity)] at this
  exact this

lemma rein_rot_sixthRoot (j k : ZMod 6) : rein_rot j (sixthRoot (k + j)) = sixthRoot k := by
  have e0 : rein_rot j (sixthRoot j) = sixthRoot 0 := by
    rw [rein_rot, rein_frame_apply, rein_frameLin_left (rein_det2_sixthRoot_ne j)]
  have e1 : rein_rot j (sixthRoot (j + 1)) = sixthRoot 1 := by
    rw [rein_rot, rein_frame_apply, rein_frameLin_right (rein_det2_sixthRoot_ne j)]
  have e2 : rein_rot j (sixthRoot (j + 2)) = sixthRoot 2 := by
    have h := (rein_sixthRoot_rel j).2.1
    have h' := (rein_sixthRoot_rel 0).2.1
    rw [zero_add, show (0 : ZMod 6) + 2 = 2 from rfl] at h'
    rw [show sixthRoot (j + 2) = sixthRoot (j + 1) - sixthRoot j by rw [h]; abel, map_sub, e0,
      e1, h']
    abel
  have neg : ∀ i, rein_rot j (sixthRoot (j + i + 3)) = -rein_rot j (sixthRoot (j + i)) := by
    intro i; rw [(rein_sixthRoot_rel (j + i)).1, map_neg]
  rcases rein_zmod6_cases k with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [zero_add, e0]
  · rw [add_comm, e1]
  · rw [add_comm, e2]
  · rw [show (3 : ZMod 6) + j = j + 0 + 3 by ring, neg, add_zero, e0,
      ← (rein_sixthRoot_rel 0).1]; rfl
  · rw [show (4 : ZMod 6) + j = j + 1 + 3 by ring, neg, e1, ← (rein_sixthRoot_rel 1).1]; rfl
  · rw [show (5 : ZMod 6) + j = j + 2 + 3 by ring, neg, e2, ← (rein_sixthRoot_rel 2).1]; rfl

lemma rein_rot_image_sixthTriangle (j k : ZMod 6) :
    rein_rot j '' sixthTriangle (k + j) = sixthTriangle k := by
  rw [sixthTriangle, sixthTriangle]
  set f : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) := (rein_rot j : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))
  have h := LinearMap.image_convexHull f
    {sixthRoot (k + j), sixthRoot (k + j + 1), sixthRoot (k + j) + sixthRoot (k + j + 1)}
  have h0 : f (sixthRoot (k + j)) = sixthRoot k := rein_rot_sixthRoot j k
  have h1 : f (sixthRoot (k + j + 1)) = sixthRoot (k + 1) := by
    rw [show k + j + 1 = k + 1 + j by ring]; exact rein_rot_sixthRoot j (k + 1)
  simp only [image_insert_eq, image_singleton, map_add, h0, h1] at h
  exact h

lemma rein_rot_mem_sixthTriangle (j k : ZMod 6) (x : Fin 2 → ℝ) :
    rein_rot j x ∈ sixthTriangle k ↔ x ∈ sixthTriangle (k + j) := by
  rw [← rein_rot_image_sixthTriangle j k]
  exact (rein_rot j).injective.mem_set_image

lemma rein_rot_mem_interior_sixthTriangle (j k : ZMod 6) (x : Fin 2 → ℝ) :
    rein_rot j x ∈ interior (sixthTriangle k) ↔ x ∈ interior (sixthTriangle (k + j)) := by
  rw [← rein_rot_image_sixthTriangle j k, rein_interior_image]
  exact (rein_rot j).injective.mem_set_image

lemma rein_rot_mem_openSegment (j k : ZMod 6) (x : Fin 2 → ℝ) :
    rein_rot j x ∈ openSegment ℝ (sixthRoot k) (sixthRoot (k + 1)) ↔
      x ∈ openSegment ℝ (sixthRoot (k + j)) (sixthRoot (k + j + 1)) := by
  set f : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) := (rein_rot j : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))
  have h := image_openSegment ℝ f.toAffineMap (sixthRoot (k + j)) (sixthRoot (k + j + 1))
  have h0 : f (sixthRoot (k + j)) = sixthRoot k := rein_rot_sixthRoot j k
  have h1 : f (sixthRoot (k + j + 1)) = sixthRoot (k + 1) := by
    rw [show k + j + 1 = k + 1 + j by ring]; exact rein_rot_sixthRoot j (k + 1)
  simp only [LinearMap.coe_toAffineMap, h0, h1] at h
  rw [← h]
  exact (rein_rot j).injective.mem_set_image

lemma rein_std_rot {K : Set (Fin 2 → ℝ)} (hS : rein_Std K) (j : ZMod 6) :
    rein_Std (rein_rot j '' K) := by
  obtain ⟨w, hw, hm⟩ := hS
  refine ⟨fun k ↦ rein_rot j (w (k + j)),
    rein_isLeastAreaHexagon_comp (rein_posLin_rot j) (rein_isLeastAreaHexagon_shift hw j),
    fun k ↦ ?_⟩
  rw [rein_hexMidpoint_comp (e := rein_rot j) (fun i ↦ w (i + j)), rein_hexMidpoint_shift, hm,
    rein_rot_sixthRoot]

lemma rein_least_rot {K : Set (Fin 2 → ℝ)} {v : ZMod 6 → Fin 2 → ℝ} (hv : IsLeastAreaHexagon K v)
    (j : ZMod 6) :
    IsLeastAreaHexagon (rein_rot j '' K) (fun k ↦ rein_rot j (v (k + j))) :=
  rein_isLeastAreaHexagon_comp (rein_posLin_rot j) (rein_isLeastAreaHexagon_shift hv j)

lemma rein_hexMidpoint_rot (v : ZMod 6 → Fin 2 → ℝ) (j k : ZMod 6) :
    hexMidpoint (fun i ↦ rein_rot j (v (i + j))) k = rein_rot j (hexMidpoint v (k + j)) := by
  rw [rein_hexMidpoint_comp (e := rein_rot j) (fun i ↦ v (i + j)), rein_hexMidpoint_shift]

/-- Weak monotonicity at the index `j`. -/
lemma rein_weak_mono_at {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) (hS : rein_Std K)
    {v : ZMod 6 → Fin 2 → ℝ} (hv : IsLeastAreaHexagon K v) (j : ZMod 6)
    (h0 : hexMidpoint v j ∈ sixthTriangle j) (hne0 : hexMidpoint v j ≠ sixthRoot j)
    (hne1 : hexMidpoint v j ≠ sixthRoot (j + 1)) : ∀ k, hexMidpoint v k ∈ sixthTriangle k := by
  have := rein_weak_mono (rein_isCCSDisk_image hK) (rein_std_rot hS j) (rein_least_rot hv j)
  simp only [rein_hexMidpoint_rot, zero_add, rein_rot_mem_sixthTriangle] at this
  intro k
  have hk := this h0 ?_ ?_ (k - j)
  · rwa [sub_add_cancel] at hk
  · intro h
    apply hne0
    have := rein_rot_sixthRoot j 0
    rw [zero_add] at this
    exact (rein_rot j).injective (h.trans this.symm)
  · intro h
    apply hne1
    have := rein_rot_sixthRoot j 1
    rw [add_comm] at this
    exact (rein_rot j).injective (h.trans this.symm)


/-! ### Lines in coordinates -/

lemma rein_cB_line (h : ℝ) :
    {x : Fin 2 → ℝ | rein_cB x = h} = {x | (![0, 1] : Fin 2 → ℝ) ⬝ᵥ x = h * (√3 / 2)} := by
  have h3 := rein_sqrt3_pos
  ext x
  simp only [mem_ofPred_eq, rein_cB_eq, dotProduct, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zero_mul, one_mul, zero_add]
  rw [div_eq_iff h3.ne']
  constructor <;> intro hx <;> linarith

lemma rein_isSupportLine_cB {K : Set (Fin 2 → ℝ)} {h : ℝ} (hK : ∀ x ∈ K, rein_cB x ≤ h)
    {u : Fin 2 → ℝ} (hu : u ∈ K) (huh : rein_cB u = h) :
    IsSupportLine K {x | rein_cB x = h} := by
  have h3 := rein_sqrt3_pos
  have key : ∀ x, (![0, 1] : Fin 2 → ℝ) ⬝ᵥ x = rein_cB x * (√3 / 2) := by
    intro x
    simp only [rein_cB_eq, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, zero_mul, one_mul, zero_add]
    field_simp
  rw [rein_cB_line]
  refine rein_isSupportLine_of (by intro h0; have := congrFun h0 1; simp at this)
    (fun x hx ↦ ?_) hu (by rw [key, huh])
  rw [key]
  have := hK x hx
  nlinarith

/-- The open segment `(s_k*, s_{k+1}*)` in the frame coordinates. -/
lemma rein_mem_openSegment_sixthRoot (k : ZMod 6) (x : Fin 2 → ℝ) :
    x ∈ openSegment ℝ (sixthRoot k) (sixthRoot (k + 1)) ↔
      (rein_cA x * rein_cB (sixthRoot (k + 1)) - rein_cB x * rein_cA (sixthRoot (k + 1))) +
        (rein_cA (sixthRoot k) * rein_cB x - rein_cB (sixthRoot k) * rein_cA x) = 1 ∧
      0 < rein_cA x * rein_cB (sixthRoot (k + 1)) - rein_cB x * rein_cA (sixthRoot (k + 1)) ∧
      0 < rein_cA (sixthRoot k) * rein_cB x - rein_cB (sixthRoot k) * rein_cA x := by
  have hD := rein_det2_sixthRoot_pos k
  rw [rein_mem_openSegment_iff hD, ← (rein_sixthTriangle_frame k x).1,
    ← (rein_sixthTriangle_frame k x).2, ← add_div, div_eq_one_iff_eq hD.ne',
    div_pos_iff_of_pos_right hD, div_pos_iff_of_pos_right hD]

/-- **Claim** (proof of Lemma 2.2.6, second paragraph), at the index `0`: in normal position, no
edge midpoint `s₀` of a critical hexagon lies in the relative interior of the edge `(s₀*, s₁*)`
of `T₀`.

The book takes "any midpoint `u₁` of a critical hexagon in the interior of `T₁` whose support line
is different from the support lines at `s₁*` and `s₂*`", which exists "because there are no
corners". We construct it: the support line of `K` normal to the edge `[s₁*, s₂*]` (at the
highest point of `K` in that direction) contains an edge of a critical hexagon (Lemma 2.2.5), and
the midpoint `u₁` of that edge has the required properties, again by the uniqueness of support
lines. -/
lemma rein_claimE {K : Set (Fin 2 → ℝ)} (hG : rein_Good K) (hS : rein_Std K)
    {v : ZMod 6 → Fin 2 → ℝ} (hv : IsLeastAreaHexagon K v) :
    hexMidpoint v 0 ∉ openSegment ℝ (sixthRoot 0) (sixthRoot 1) := by
  intro hseg
  obtain ⟨hK, hU, hE⟩ := hG
  obtain ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩, -, -⟩ := rein_coord_sixthRoot
  have h3 := rein_sqrt3_pos
  have hs := rein_sixthRoot_mem_frontier hK hS
  have hsK : ∀ j, sixthRoot j ∈ K := fun j ↦ rein_frontier_subset hK (hs j)
  have hKc : IsClosed K := hK.2.1.isClosed
  have huniq : ∀ z ∈ frontier K, ∀ ℓ₁ ℓ₂, IsSupportLine K ℓ₁ → z ∈ ℓ₁ → IsSupportLine K ℓ₂ →
      z ∈ ℓ₂ → ℓ₁ = ℓ₂ := by
    intro z hz ℓ₁ ℓ₂ h1 hz1 h2 hz2
    obtain ⟨ℓ, -, hu⟩ := hU z hz
    rw [hu ℓ₁ ⟨h1, hz1⟩, hu ℓ₂ ⟨h2, hz2⟩]
  have hmF : hexMidpoint v 0 ∈ frontier K := rein_hexMidpoint_mem_frontier hK hv 0
  obtain ⟨ℓm, ⟨hℓm, hmℓ⟩, -⟩ := hU _ hmF
  obtain ⟨h0ℓ, h1ℓ⟩ := rein_supportLine_openSegment hℓm (hsK 0) (hsK 1) hmℓ hseg
  -- the highest point `u` of `K` in the direction normal to `[s₁*, s₂*]`
  obtain ⟨u, huK, hmax⟩ := hK.2.1.exists_isMaxOn ⟨_, hsK 0⟩ rein_continuous_cB.continuousOn
  set h := rein_cB u with hh
  have hmax' : ∀ x ∈ K, rein_cB x ≤ h := fun x hx ↦ hmax hx
  have hL : IsSupportLine K {x | rein_cB x = h} := rein_isSupportLine_cB hmax' huK rfl
  have h1 : 1 < h := by
    by_contra hle
    push Not at hle
    have hh1 : h = 1 := le_antisymm hle (by have := hmax' _ (hsK 1); rwa [b1] at this)
    have hL1 : sixthRoot 1 ∈ {x | rein_cB x = h} := by
      simp only [mem_ofPred_eq, b1, hh1]
    have := huniq _ (hs 1) _ _ hL hL1 hℓm h1ℓ
    have h0L : sixthRoot 0 ∈ {x | rein_cB x = h} := this ▸ h0ℓ
    simp only [mem_ofPred_eq, b0] at h0L
    linarith
  have huF : u ∈ frontier K := rein_mem_frontier_of_supportLine hKc hL huK rfl
  -- the midpoint `u₁` of an edge of a critical hexagon on this support line (Lemma 2.2.5)
  obtain ⟨v', hv', k, hk⟩ := hE u huF _ hL rfl
  set u1 := hexMidpoint v' k with hu1def
  have hu1L : u1 ∈ {x | rein_cB x = h} := hk (midpoint_mem_segment _ _)
  have hu1L' : rein_cB u1 = h := hu1L
  have hu1F : u1 ∈ frontier K := rein_hexMidpoint_mem_frontier hK hv' k
  have hu1K : u1 ∈ K := rein_frontier_subset hK hu1F
  -- `u₁ ∈ T₁`
  obtain ⟨j, hj⟩ := rein_frontier_InT hK hS hu1F
  have hT1 : rein_InT 1 (rein_cA u1) (rein_cB u1) := by
    rcases rein_zmod6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [rein_InT_zero, rein_InT_one, rein_InT_two, rein_InT_three, rein_InT_four,
      rein_InT_five] at hj ⊢ <;>
    first
      | exact hj
      | (exfalso; obtain ⟨c1, c2, c3⟩ := hj; linarith)
  rw [rein_InT_one] at hT1
  obtain ⟨t1, t2, t3⟩ := hT1
  -- `u₁` is not on the line through `s₀*, s₁*`
  have hA1 : rein_cA u1 + rein_cB u1 < 1 := by
    by_contra hc
    have hline : u1 = sixthRoot 0 + rein_cB u1 • (sixthRoot 1 - sixthRoot 0) := by
      apply rein_coord_ext
      · simp only [rein_cA_add, rein_cA_smul, rein_cA_sub, a0, a1]; linarith
      · simp only [rein_cB_add, rein_cB_smul, rein_cB_sub, b0, b1]; ring
    have hu1m : u1 ∈ ℓm := hline ▸ rein_supportLine_lineMap hℓm h0ℓ h1ℓ _
    have := huniq _ hu1F _ _ hℓm hu1m hL hu1L
    have h0L : sixthRoot 0 ∈ {x | rein_cB x = h} := this ▸ h0ℓ
    simp only [mem_ofPred_eq, b0] at h0L
    linarith
  -- `u₁` is not on the line through `s₃*, s₂*`
  have hA2 : -1 < rein_cA u1 := by
    by_contra hc
    have he : rein_cA u1 = -1 := by linarith
    obtain ⟨ℓ2, ⟨hℓ2, h2ℓ⟩, -⟩ := hU _ (hs 2)
    have hpos : 0 < h := by linarith
    have hseg2 : sixthRoot 2 ∈ openSegment ℝ (sixthRoot 3) u1 := by
      refine ⟨1 - 1 / h, 1 / h, by rw [sub_pos, div_lt_one hpos]; exact h1,
        by positivity, by ring, ?_⟩
      apply rein_coord_ext
      · simp only [rein_cA_add, rein_cA_smul, a2, a3, he]; ring
      · simp only [rein_cB_add, rein_cB_smul, b2, b3, hu1L']; field_simp; ring
    obtain ⟨-, hu1ℓ2⟩ := rein_supportLine_openSegment hℓ2 (hsK 3) hu1K h2ℓ hseg2
    have := huniq _ hu1F _ _ hℓ2 hu1ℓ2 hL hu1L
    have h2L : sixthRoot 2 ∈ {x | rein_cB x = h} := this ▸ h2ℓ
    simp only [mem_ofPred_eq, b2] at h2L
    linarith
  -- reindex the critical hexagon so that `u₁` is its first edge midpoint
  set v'' : ZMod 6 → Fin 2 → ℝ := fun i ↦ v' (i + (k - 1)) with hv''def
  have hv'' : IsLeastAreaHexagon K v'' := rein_isLeastAreaHexagon_shift hv' _
  have hm1 : hexMidpoint v'' 1 = u1 := by
    rw [hv''def, rein_hexMidpoint_shift, show (1 : ZMod 6) + (k - 1) = k by ring]
  -- weak monotonicity at the index `1`: `u₀ ∈ T₀`
  have hT := rein_weak_mono_at hK hS hv'' 1 (by
      rw [hm1, rein_mem_sixthTriangle, rein_InT_one]; exact ⟨t1, t2, t3⟩)
    (by rw [hm1]; intro he; have := congrArg rein_cB he; rw [b1] at this; linarith)
    (by
      rw [hm1, show (1 : ZMod 6) + 1 = 2 from rfl]
      intro he; have := congrArg rein_cB he; rw [b2] at this; linarith)
  have hu0T := hT 0
  rw [rein_mem_sixthTriangle, rein_InT_zero] at hu0T
  have hu0K : hexMidpoint v'' 0 ∈ K :=
    rein_frontier_subset hK (rein_hexMidpoint_mem_frontier hK hv'' 0)
  -- `K` lies below the line through `s₀*, s₁*`, so `u₀` lies on the edge `[s₀*, s₁*]`
  have hside := rein_supportLine_side hK hℓm h0ℓ h1ℓ (rein_det2_sixthRoot_pos 0)
  have hside' : ∀ x ∈ K, rein_cA x + rein_cB x ≤ 1 := by
    intro x hx
    have := hside x hx
    rw [rein_det2_coord, rein_det2_coord, rein_det2_coord, a0, b0, a1, b1] at this
    nlinarith
  have hu0c : rein_cA (hexMidpoint v'' 0) + rein_cB (hexMidpoint v'' 0) = 1 :=
    le_antisymm (hside' _ hu0K) hu0T.2.2
  -- the multi-point conditions
  have hdet := rein_det2_coord_eq (rein_det2_hexMidpoint_std hS hv'' 0)
  rw [zero_add, hm1] at hdet
  have hu2 : hexMidpoint v'' 2 = u1 - hexMidpoint v'' 0 := by
    have := rein_hexMidpoint_succ hv''.1 0
    rw [zero_add, hm1, show (0 : ZMod 6) + 2 = 2 from rfl] at this
    rw [this]; abel
  have hu2K : u1 - hexMidpoint v'' 0 ∈ K :=
    hu2 ▸ rein_frontier_subset hK (rein_hexMidpoint_mem_frontier hK hv'' 2)
  -- `u₁ = s₂* + t u₀` and `u₂ = s₂* + (t - 1) u₀` with `0 < t < 1`
  set t := rein_cA u1 + rein_cB u1 with ht
  have ht0 : 0 < t := by linarith
  have hseg3 : sixthRoot 2 ∈ openSegment ℝ u1 (u1 - hexMidpoint v'' 0) := by
    refine ⟨1 - t, t, by linarith, ht0, by ring, ?_⟩
    apply rein_coord_ext
    · simp only [rein_cA_add, rein_cA_smul, rein_cA_sub, a2]
      linear_combination -hdet - rein_cA u1 * hu0c
    · simp only [rein_cB_add, rein_cB_smul, rein_cB_sub, b2]
      linear_combination hdet - rein_cB u1 * hu0c
  obtain ⟨ℓ2, ⟨hℓ2, h2ℓ⟩, -⟩ := hU _ (hs 2)
  obtain ⟨hu1ℓ2, -⟩ := rein_supportLine_openSegment hℓ2 hu1K hu2K h2ℓ hseg3
  have := huniq _ hu1F _ _ hℓ2 hu1ℓ2 hL hu1L
  have h2L : sixthRoot 2 ∈ {x | rein_cB x = h} := this ▸ h2ℓ
  simp only [mem_ofPred_eq, b2] at h2L
  linarith

/-- The claim at the index `j`. -/
lemma rein_claimE_at {K : Set (Fin 2 → ℝ)} (hG : rein_Good K) (hS : rein_Std K)
    {v : ZMod 6 → Fin 2 → ℝ} (hv : IsLeastAreaHexagon K v) (j : ZMod 6) :
    hexMidpoint v j ∉ openSegment ℝ (sixthRoot j) (sixthRoot (j + 1)) := by
  intro h
  apply rein_claimE (rein_good_image (rein_posLin_rot j) hG) (rein_std_rot hS j)
    (rein_least_rot hv j)
  rw [rein_hexMidpoint_rot, zero_add, show (1 : ZMod 6) = 0 + 1 from rfl,
    rein_rot_mem_openSegment, zero_add]
  exact h


/-! ### Points of `T_k` off the edge `[s_k*, s_{k+1}*]` -/

/-- `x` lies in `T_k` but not on its edge `[s_k*, s_{k+1}*]`. -/
def rein_OffChord (k : ZMod 6) (x : Fin 2 → ℝ) : Prop :=
  x ∈ sixthTriangle k ∧
    det2 (sixthRoot k) (sixthRoot (k + 1)) < det2 x (sixthRoot (k + 1)) + det2 (sixthRoot k) x

lemma rein_offChord_iff (k : ZMod 6) (x : Fin 2 → ℝ) :
    rein_OffChord k x ↔ x ∈ sixthTriangle k ∧
      1 < (rein_cA x * rein_cB (sixthRoot (k + 1)) - rein_cB x * rein_cA (sixthRoot (k + 1))) +
        (rein_cA (sixthRoot k) * rein_cB x - rein_cB (sixthRoot k) * rein_cA x) := by
  have hD := rein_det2_sixthRoot_pos k
  rw [rein_OffChord, ← (rein_sixthTriangle_frame k x).1, ← (rein_sixthTriangle_frame k x).2,
    ← add_div, one_lt_div hD]

lemma rein_rot_offChord (j k : ZMod 6) (x : Fin 2 → ℝ) :
    rein_OffChord k (rein_rot j x) ↔ rein_OffChord (k + j) x := by
  have hR := (rein_posLin_rot j).det
  have e1 : sixthRoot (k + 1) = rein_rot j (sixthRoot (k + j + 1)) := by
    rw [show k + j + 1 = k + 1 + j by ring, rein_rot_sixthRoot]
  have e0 : sixthRoot k = rein_rot j (sixthRoot (k + j)) := (rein_rot_sixthRoot j k).symm
  rw [rein_OffChord, rein_OffChord, rein_rot_mem_sixthTriangle, e1, e0, hR, hR, hR, one_mul,
    one_mul, one_mul]

/-- In normal position the tip `s₀* + s₁*` of `T₀` is not a boundary point (it would be a
corner). -/
lemma rein_tip_not_mem_frontier {K : Set (Fin 2 → ℝ)} (hG : rein_Good K) (hS : rein_Std K) :
    sixthRoot 0 + sixthRoot 1 ∉ frontier K := by
  intro ht
  obtain ⟨hK, hU, -⟩ := hG
  obtain ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, -, -, ⟨a5, b5⟩⟩ := rein_coord_sixthRoot
  have h3 := rein_sqrt3_pos
  have hs := rein_sixthRoot_mem_frontier hK hS
  have hsK : ∀ j, sixthRoot j ∈ K := fun j ↦ rein_frontier_subset hK (hs j)
  have htK := rein_frontier_subset hK ht
  obtain ⟨ℓ0, ⟨hℓ0, h0ℓ⟩, -⟩ := hU _ (hs 0)
  obtain ⟨ℓ1, ⟨hℓ1, h1ℓ⟩, -⟩ := hU _ (hs 1)
  have hseg0 : sixthRoot 0 ∈ openSegment ℝ (sixthRoot 5) (sixthRoot 0 + sixthRoot 1) := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    apply rein_coord_ext
    · simp only [rein_cA_add, rein_cA_smul, a0, a1, a5]; norm_num
    · simp only [rein_cB_add, rein_cB_smul, b0, b1, b5]; norm_num
  have hseg1 : sixthRoot 1 ∈ openSegment ℝ (sixthRoot 2) (sixthRoot 0 + sixthRoot 1) := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    apply rein_coord_ext
    · simp only [rein_cA_add, rein_cA_smul, a0, a1, a2]; norm_num
    · simp only [rein_cB_add, rein_cB_smul, b0, b1, b2]; norm_num
  obtain ⟨-, ht0⟩ := rein_supportLine_openSegment hℓ0 (hsK 5) htK h0ℓ hseg0
  obtain ⟨-, ht1⟩ := rein_supportLine_openSegment hℓ1 (hsK 2) htK h1ℓ hseg1
  obtain ⟨ℓ, -, hu⟩ := hU _ ht
  have heq : ℓ0 = ℓ1 := by rw [hu ℓ0 ⟨hℓ0, ht0⟩, hu ℓ1 ⟨hℓ1, ht1⟩]
  have h1ℓ0 : sixthRoot 1 ∈ ℓ0 := heq ▸ h1ℓ
  have := rein_supportLine_side hK hℓ0 h0ℓ h1ℓ0 (rein_det2_sixthRoot_pos 0) _ htK
  rw [rein_det2_coord, rein_det2_coord, rein_det2_coord] at this
  simp only [rein_cA_add, rein_cB_add, a0, b0, a1, b1] at this
  nlinarith

/-- **Step** (proof of Lemma 2.2.6, third paragraph), at the index `0`: if `s₀ ∈ T₀ \ [s₀*, s₁*]`
and `s₁ ∈ T₁`, then `s₁ ∈ T₁ \ [s₁*, s₂*]`. The book excludes `s₁ = s₁*` by the claim applied to
`s₅ = s₀ - s₁*`; this needs `s₅` to be in the relative interior of `(s₅*, s₀*)`, which fails when
`s₀` is the tip `s₀* + s₁*` of `T₀`; that case is excluded by `rein_tip_not_mem_frontier`. -/
lemma rein_step {K : Set (Fin 2 → ℝ)} (hG : rein_Good K) (hS : rein_Std K)
    {v : ZMod 6 → Fin 2 → ℝ} (hv : IsLeastAreaHexagon K v)
    (h0 : rein_OffChord 0 (hexMidpoint v 0)) (h1 : hexMidpoint v 1 ∈ sixthTriangle 1) :
    rein_OffChord 1 (hexMidpoint v 1) := by
  obtain ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, -, -, ⟨a5, b5⟩⟩ := rein_coord_sixthRoot
  have hK := hG.1
  rw [rein_offChord_iff] at h0 ⊢
  refine ⟨h1, ?_⟩
  obtain ⟨h0T, h0c⟩ := h0
  rw [rein_mem_sixthTriangle, rein_InT_zero] at h0T
  have h1T := h1
  rw [rein_mem_sixthTriangle, rein_InT_one] at h1T
  rw [show (0 : ZMod 6) + 1 = 1 from rfl, a0, b0, a1, b1] at h0c
  rw [show (1 : ZMod 6) + 1 = 2 from rfl, a1, b1, a2, b2]
  set A0 := rein_cA (hexMidpoint v 0)
  set B0 := rein_cB (hexMidpoint v 0)
  set A1 := rein_cA (hexMidpoint v 1)
  set B1 := rein_cB (hexMidpoint v 1)
  obtain ⟨n1, n2, n3⟩ := h1T
  by_contra hB
  have hB1 : B1 = 1 := by nlinarith
  have hdet := rein_det2_coord_eq (rein_det2_hexMidpoint_std hS hv 0)
  rw [zero_add] at hdet
  change A0 * B1 - B0 * A1 = 1 at hdet
  rw [hB1] at hdet
  rcases lt_or_eq_of_le n2 with hA | hA
  · rcases lt_or_eq_of_le (show A1 ≤ 0 by linarith) with hA' | hA'
    · -- `s₁` in the relative interior of `(s₁*, s₂*)`
      apply rein_claimE_at hG hS hv 1
      rw [rein_mem_openSegment_sixthRoot, show (1 : ZMod 6) + 1 = 2 from rfl, a1, b1, a2, b2]
      refine ⟨?_, ?_, ?_⟩ <;> simp only [A1, B1] at * <;> nlinarith
    · -- `s₁ = s₁*`: then `s₀ = s₀* + B₀ s₁*` and `s₅ = s₀ - s₁*`
      have hA0 : A0 = 1 := by rw [hA'] at hdet; linarith
      have hm5 : hexMidpoint v 5 = hexMidpoint v 0 - hexMidpoint v 1 := by
        have e1 := rein_hexMidpoint_succ hv.1 0
        have e2 := rein_hexMidpoint_add_three hv.1 2
        rw [zero_add, show (0 : ZMod 6) + 2 = 2 from rfl] at e1
        rw [show (2 : ZMod 6) + 3 = 5 from rfl] at e2
        rw [e2, e1]; abel
      rcases lt_or_eq_of_le h0T.2.1 with hB0 | hB0
      · apply rein_claimE_at hG hS hv 5
        rw [rein_mem_openSegment_sixthRoot, show (5 : ZMod 6) + 1 = 0 from rfl, a5, b5, a0, b0,
          hm5, rein_cA_sub, rein_cB_sub]
        refine ⟨?_, ?_, ?_⟩ <;> simp only [A0, B0, A1, B1] at * <;> nlinarith
      · apply rein_tip_not_mem_frontier hG hS
        have : hexMidpoint v 0 = sixthRoot 0 + sixthRoot 1 := by
          apply rein_coord_ext
          · rw [rein_cA_add, a0, a1]; simp only [A0] at hA0; linarith
          · rw [rein_cB_add, b0, b1]; simp only [B0] at hB0; linarith
        rw [← this]
        exact rein_hexMidpoint_mem_frontier hK hv 0
  · -- `s₁ = s₂*`: then `det(s₀, s₂*) = det(s₀*, s₁*)` puts `s₀` on the edge `[s₀*, s₁*]`
    rw [← hA] at hdet
    linarith

/-- The step at the index `j`. -/
lemma rein_step_at {K : Set (Fin 2 → ℝ)} (hG : rein_Good K) (hS : rein_Std K)
    {v : ZMod 6 → Fin 2 → ℝ} (hv : IsLeastAreaHexagon K v) (j : ZMod 6)
    (h0 : rein_OffChord j (hexMidpoint v j)) (h1 : hexMidpoint v (j + 1) ∈ sixthTriangle (j + 1)) :
    rein_OffChord (j + 1) (hexMidpoint v (j + 1)) := by
  have := rein_step (rein_good_image (rein_posLin_rot j) hG) (rein_std_rot hS j)
    (rein_least_rot hv j)
  simp only [rein_hexMidpoint_rot, rein_rot_offChord, rein_rot_mem_sixthTriangle, zero_add] at this
  rw [add_comm 1 j] at this
  exact this h0 h1

/-- **Interior** (proof of Lemma 2.2.6, last sentence), at the index `0`: if `s₅, s₀, s₁` are off
the edges `[s_k*, s_{k+1}*]` of their triangles, then `s₀` is in the interior of `T₀`. -/
lemma rein_interior_step {K : Set (Fin 2 → ℝ)} (hG : rein_Good K) (hS : rein_Std K)
    {v : ZMod 6 → Fin 2 → ℝ} (hv : IsLeastAreaHexagon K v)
    (h0 : rein_OffChord 0 (hexMidpoint v 0)) (h1 : rein_OffChord 1 (hexMidpoint v 1))
    (h5 : rein_OffChord 5 (hexMidpoint v 5)) : hexMidpoint v 0 ∈ interior (sixthTriangle 0) := by
  obtain ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, -, -, ⟨a5, b5⟩⟩ := rein_coord_sixthRoot
  obtain ⟨hK, hU, -⟩ := hG
  have h3 := rein_sqrt3_pos
  have hs := rein_sixthRoot_mem_frontier hK hS
  have hsK : ∀ j, sixthRoot j ∈ K := fun j ↦ rein_frontier_subset hK (hs j)
  have hmK : ∀ k, hexMidpoint v k ∈ K :=
    fun k ↦ rein_frontier_subset hK (rein_hexMidpoint_mem_frontier hK hv k)
  rw [rein_offChord_iff] at h0 h1 h5
  obtain ⟨h0T, h0c⟩ := h0
  rw [rein_mem_sixthTriangle, rein_InT_zero] at h0T
  rw [show (0 : ZMod 6) + 1 = 1 from rfl, a0, b0, a1, b1] at h0c
  rw [show (1 : ZMod 6) + 1 = 2 from rfl, a1, b1, a2, b2] at h1
  rw [show (5 : ZMod 6) + 1 = 0 from rfl, a5, b5, a0, b0] at h5
  rw [rein_mem_interior_sixthTriangle, rein_InTo_zero]
  refine ⟨?_, ?_, by linarith⟩
  · -- if `s₀` is on the edge `[s₀*, s₀* + s₁*]`, the support line at `s₀*` is the line of
    -- `[s₅*, s₀*]`, and `s₅ ∈ T₅` is on the edge `[s₅*, s₀*]`
    by_contra hA
    have hA0 : rein_cA (hexMidpoint v 0) = 1 := by linarith [h0T.1]
    have hBpos : 0 < rein_cB (hexMidpoint v 0) := by linarith
    have hne : 1 + rein_cB (hexMidpoint v 0) ≠ 0 := by linarith
    obtain ⟨ℓ0, ⟨hℓ0, h0ℓ⟩, -⟩ := hU _ (hs 0)
    have hseg : sixthRoot 0 ∈ openSegment ℝ (sixthRoot 5) (hexMidpoint v 0) := by
      refine ⟨rein_cB (hexMidpoint v 0) / (1 + rein_cB (hexMidpoint v 0)),
        1 / (1 + rein_cB (hexMidpoint v 0)), by positivity, by positivity,
        by field_simp; ring, ?_⟩
      apply rein_coord_ext
      · simp only [rein_cA_add, rein_cA_smul, a0, a5, hA0]; field_simp; ring
      · simp only [rein_cB_add, rein_cB_smul, b0, b5]; field_simp; ring
    obtain ⟨h5ℓ, -⟩ := rein_supportLine_openSegment hℓ0 (hsK 5) (hmK 0) h0ℓ hseg
    have hside := rein_supportLine_side hK hℓ0 h5ℓ (show sixthRoot (5 + 1) ∈ ℓ0 from h0ℓ)
      (rein_det2_sixthRoot_pos 5) _ (hmK 5)
    rw [show (5 : ZMod 6) + 1 = 0 from rfl, rein_det2_coord, rein_det2_coord, rein_det2_coord,
      a5, b5, a0, b0] at hside
    nlinarith [h5.2]
  · by_contra hB
    have hB0 : rein_cB (hexMidpoint v 0) = 1 := by linarith [h0T.2.1]
    have hApos : 0 < rein_cA (hexMidpoint v 0) := by linarith
    have hne : 1 + rein_cA (hexMidpoint v 0) ≠ 0 := by linarith
    obtain ⟨ℓ1, ⟨hℓ1, h1ℓ⟩, -⟩ := hU _ (hs 1)
    have hseg : sixthRoot 1 ∈ openSegment ℝ (sixthRoot 2) (hexMidpoint v 0) := by
      refine ⟨rein_cA (hexMidpoint v 0) / (1 + rein_cA (hexMidpoint v 0)),
        1 / (1 + rein_cA (hexMidpoint v 0)), by positivity, by positivity,
        by field_simp; ring, ?_⟩
      apply rein_coord_ext
      · simp only [rein_cA_add, rein_cA_smul, a1, a2]; field_simp; ring
      · simp only [rein_cB_add, rein_cB_smul, b1, b2, hB0]; field_simp; ring
    obtain ⟨h2ℓ, -⟩ := rein_supportLine_openSegment hℓ1 (hsK 2) (hmK 0) h1ℓ hseg
    have hside := rein_supportLine_side hK hℓ1 h1ℓ (show sixthRoot (1 + 1) ∈ ℓ1 from h2ℓ)
      (rein_det2_sixthRoot_pos 1) _ (hmK 1)
    rw [show (1 : ZMod 6) + 1 = 2 from rfl, rein_det2_coord, rein_det2_coord, rein_det2_coord,
      a1, b1, a2, b2] at hside
    nlinarith [h1.2]

/-- The interior step at the index `j`. -/
lemma rein_interior_step_at {K : Set (Fin 2 → ℝ)} (hG : rein_Good K) (hS : rein_Std K)
    {v : ZMod 6 → Fin 2 → ℝ} (hv : IsLeastAreaHexagon K v) (j : ZMod 6)
    (h0 : rein_OffChord j (hexMidpoint v j)) (h1 : rein_OffChord (j + 1) (hexMidpoint v (j + 1)))
    (h5 : rein_OffChord (j + 5) (hexMidpoint v (j + 5))) :
    hexMidpoint v j ∈ interior (sixthTriangle j) := by
  have := rein_interior_step (rein_good_image (rein_posLin_rot j) hG) (rein_std_rot hS j)
    (rein_least_rot hv j)
  simp only [rein_hexMidpoint_rot, rein_rot_offChord, rein_rot_mem_interior_sixthTriangle,
    zero_add] at this
  rw [add_comm 1 j, add_comm 5 j] at this
  exact this h0 h1 h5


/-- The consequences of Lemma 2.2.5 for a disk with the worst greatest lattice packing density. -/
lemma rein_good_of_worst {K : Set (Fin 2 → ℝ)} (hK : IsWorstLatticeDisk K) : rein_Good K :=
  ⟨hK.1, (lemma2_2_5.2 K hK).1, (lemma2_2_5.2 K hK).2⟩

/-- Lemma 2.2.6 for a disk with the properties of Lemma 2.2.5 (`rein_Good`). -/
lemma rein_lemma2_2_6 {K : Set (Fin 2 → ℝ)} (hG : rein_Good K) (hS : rein_Std K)
    {v : ZMod 6 → Fin 2 → ℝ} (hv : IsLeastAreaHexagon K v)
    (h0 : hexMidpoint v 0 ∈ sixthTriangle 0 \ {sixthRoot 0, sixthRoot 1}) :
    ∀ j, hexMidpoint v j ∈ interior (sixthTriangle j) := by
  obtain ⟨⟨a0, b0⟩, ⟨a1, b1⟩, -⟩ := rein_coord_sixthRoot
  have hK := hG.1
  obtain ⟨h0T, h0ne⟩ := h0
  have hne0 : hexMidpoint v 0 ≠ sixthRoot 0 := fun h ↦ h0ne (Or.inl h)
  have hne1 : hexMidpoint v 0 ≠ sixthRoot 1 := fun h ↦ h0ne (Or.inr h)
  -- weak monotonicity
  have hT := rein_weak_mono hK hS hv h0T hne0 hne1
  -- `s₀` is not on the edge `[s₀*, s₁*]`
  have hoff0 : rein_OffChord 0 (hexMidpoint v 0) := by
    rw [rein_offChord_iff]
    refine ⟨h0T, ?_⟩
    have h0T' := h0T
    rw [rein_mem_sixthTriangle, rein_InT_zero] at h0T'
    rw [show (0 : ZMod 6) + 1 = 1 from rfl, a0, b0, a1, b1]
    by_contra hc
    push Not at hc
    have hsum : rein_cA (hexMidpoint v 0) + rein_cB (hexMidpoint v 0) = 1 := by linarith
    rcases (show 0 ≤ rein_cA (hexMidpoint v 0) by linarith).eq_or_lt with hA | hA
    · exact hne1 (rein_coord_ext (by rw [a1]; linarith) (by rw [b1]; linarith))
    rcases (show 0 ≤ rein_cB (hexMidpoint v 0) by linarith).eq_or_lt with hB | hB
    · exact hne0 (rein_coord_ext (by rw [a0]; linarith) (by rw [b0]; linarith))
    apply rein_claimE hG hS hv
    rw [show (1 : ZMod 6) = 0 + 1 from rfl, rein_mem_openSegment_sixthRoot,
      show (0 : ZMod 6) + 1 = 1 from rfl, a0, b0, a1, b1]
    refine ⟨by linarith, by linarith, by linarith⟩
  -- the step, repeated
  have o1 := rein_step_at hG hS hv 0 hoff0 (hT _)
  have o2 := rein_step_at hG hS hv _ o1 (hT _)
  have o3 := rein_step_at hG hS hv _ o2 (hT _)
  have o4 := rein_step_at hG hS hv _ o3 (hT _)
  have o5 := rein_step_at hG hS hv _ o4 (hT _)
  rein_z6
  have hoff : ∀ k, rein_OffChord k (hexMidpoint v k) := by
    intro k
    rcases rein_zmod6_cases k with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hoff0
    · exact o1
    · exact o2
    · exact o3
    · exact o4
    · exact o5
  intro j
  exact rein_interior_step_at hG hS hv j (hoff j) (hoff (j + 1)) (hoff (j + 5))

/-- **Lemma 2.2.6** (`lem:tri-interior`; Reinhardt's *monotonicity*). Assume that `K_min` has a
critical hexagon with edge midpoints `s_j*`. Consider a second critical hexagon of `K_min` with
edge midpoints `s₀, …, s₅`, indexed so that `s₀ ∈ T₀ \ {s₀*, s₁*}`. Then for all `j`, `s_j` lies
in the interior of `T_j`.

Gaps in the paper's proof, filled along its lines: the point `u₁` of Claim E is constructed from
the support line of `K` parallel to `[s₁*, s₂*]` and Lemma 2.2.5; the case where a midpoint is
the tip `s_j* + s_{j+1}*` of `T_j`, which the book's step does not treat, is excluded because the
tip would be a corner of `K` (Lemma 2.2.5). -/
theorem lemma2_2_6 {K : Set (Fin 2 → ℝ)} (hK : IsWorstLatticeDisk K)
    (hstar : ∃ w, IsLeastAreaHexagon K w ∧ ∀ j, hexMidpoint w j = sixthRoot j)
    {v : ZMod 6 → Fin 2 → ℝ} (hv : IsLeastAreaHexagon K v)
    (h0 : hexMidpoint v 0 ∈ sixthTriangle 0 \ {sixthRoot 0, sixthRoot 1}) :
    ∀ j, hexMidpoint v j ∈ interior (sixthTriangle j) :=
  rein_lemma2_2_6 (rein_good_of_worst hK) hstar hv h0

/-! ## Helper lemmas for Lemma 2.2.7 -/

/-! ### Uniqueness of the critical hexagon with a given edge midpoint -/

/-- A line `{x | det(p, x - q) = 0}` with `K` on the side `det(p, x - q) ≥ 0` and `q ∈ K` is a
support line. -/
lemma rein_isSupportLine_det2 {K : Set (Fin 2 → ℝ)} {p q : Fin 2 → ℝ} (hp : p ≠ 0)
    (hK : ∀ x ∈ K, 0 ≤ det2 p (x - q)) (hq : q ∈ K) :
    IsSupportLine K {x | det2 p (x - q) = 0} := by
  refine ⟨⟨![-p 1, p 0], rein_ne_zero_of_det2 hp, det2 p q, ?_, fun x hx y hy ↦ ?_⟩,
    ⟨q, by simp [det2], hq⟩⟩
  · ext x
    simp only [mem_ofPred_eq, rein_det2_sub_right, ← rein_det2_eq_dotProduct, sub_eq_zero]
  · rw [← rein_det2_eq_dotProduct, ← rein_det2_eq_dotProduct, ← rein_det2_sub_right,
      ← rein_det2_sub_right]
    exact mul_nonneg (hK x hx) (hK y hy)

/-- The line of the edge `k` of a least-area hexagon is a support line of `K`. -/
lemma rein_isSupportLine_edge {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K)
    {v : ZMod 6 → Fin 2 → ℝ} (hv : IsLeastAreaHexagon K v) (k : ZMod 6) :
    IsSupportLine K {x | det2 (v (k + 1) - v k) (x - hexMidpoint v k) = 0} := by
  refine rein_isSupportLine_det2 ?_ (fun x hx ↦ rein_edge_halfPlane hv.1 k (hv.2.1 hx))
    (rein_frontier_subset hK (rein_hexMidpoint_mem_frontier hK hv k))
  intro h
  have := (hv.1 k).2.1
  rw [sub_eq_zero] at h
  rw [h, rein_det2_self] at this
  exact lt_irrefl _ this

/-- Two least-area hexagons of `K` with the same edge midpoints are equal, when `K` has a unique
support line at each boundary point. -/
lemma rein_eq_of_hexMidpoint_eq {K : Set (Fin 2 → ℝ)} (hG : rein_Good K)
    {v w : ZMod 6 → Fin 2 → ℝ} (hv : IsLeastAreaHexagon K v) (hw : IsLeastAreaHexagon K w)
    (h : ∀ k, hexMidpoint v k = hexMidpoint w k) : v = w := by
  obtain ⟨hK, hU, -⟩ := hG
  have hline : ∀ k, {x | det2 (v (k + 1) - v k) (x - hexMidpoint v k) = 0} =
      {x | det2 (w (k + 1) - w k) (x - hexMidpoint w k) = 0} := by
    intro k
    obtain ⟨ℓ, -, hu⟩ := hU _ (rein_hexMidpoint_mem_frontier hK hv k)
    rw [hu _ ⟨rein_isSupportLine_edge hK hv k, by simp [det2]⟩,
      hu _ ⟨rein_isSupportLine_edge hK hw k, by simp [h k, det2]⟩]
  have hon1 : ∀ (u : ZMod 6 → Fin 2 → ℝ) k,
      det2 (u (k + 1) - u k) (u (k + 1) - hexMidpoint u k) = 0 := by
    intro u k
    simp only [hexMidpoint, midpoint_eq_smul_add, det2, Pi.sub_apply, Pi.smul_apply, Pi.add_apply,
      smul_eq_mul, invOf_eq_inv]
    ring
  have hon2 : ∀ (u : ZMod 6 → Fin 2 → ℝ) k,
      det2 (u (k + 1 + 1) - u (k + 1)) (u (k + 1) - hexMidpoint u (k + 1)) = 0 := by
    intro u k
    simp only [hexMidpoint, midpoint_eq_smul_add, det2, Pi.sub_apply, Pi.smul_apply, Pi.add_apply,
      smul_eq_mul, invOf_eq_inv]
    ring
  funext i
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by ring⟩
  have e1 : v (k + 1) ∈ {x | det2 (w (k + 1) - w k) (x - hexMidpoint w k) = 0} := by
    rw [← hline k]; exact hon1 v k
  have e2 : v (k + 1) ∈ {x | det2 (w (k + 1 + 1) - w (k + 1)) (x - hexMidpoint w (k + 1)) = 0} := by
    rw [← hline (k + 1)]; exact hon2 v k
  have f1 := hon1 w k
  have f2 := hon2 w k
  simp only [mem_ofPred_eq] at e1 e2
  have hturn := (hw.1 k).2.2
  rw [show k + 2 = k + 1 + 1 by ring] at hturn
  -- two non-parallel lines meet in at most one point
  set d := w (k + 1) - w k
  set d' := w (k + 1 + 1) - w (k + 1)
  have g1 : det2 d (v (k + 1) - w (k + 1)) = 0 := by
    have : v (k + 1) - w (k + 1) =
        (v (k + 1) - hexMidpoint w k) - (w (k + 1) - hexMidpoint w k) := by
      abel
    rw [this, rein_det2_sub_right, e1, f1, sub_zero]
  have g2 : det2 d' (v (k + 1) - w (k + 1)) = 0 := by
    have : v (k + 1) - w (k + 1) =
        (v (k + 1) - hexMidpoint w (k + 1)) - (w (k + 1) - hexMidpoint w (k + 1)) := by abel
    rw [this, rein_det2_sub_right, e2, f2, sub_zero]
  have hcr := rein_cramer d d' (v (k + 1) - w (k + 1))
  rw [rein_det2_swap d' (v (k + 1) - w (k + 1)), g2, g1, neg_zero, zero_smul, zero_smul,
    add_zero] at hcr
  have := smul_eq_zero.1 hcr
  rcases this with h0 | h0
  · exact absurd h0 hturn.ne'
  · exact sub_eq_zero.1 h0

/-- The tips `s_j* + s_{j+1}*` of the triangles `T_j` are not boundary points (corners). -/
lemma rein_tip_not_mem_frontier_at {K : Set (Fin 2 → ℝ)} (hG : rein_Good K) (hS : rein_Std K)
    (j : ZMod 6) : sixthRoot j + sixthRoot (j + 1) ∉ frontier K := by
  intro h
  apply rein_tip_not_mem_frontier (rein_good_image (rein_posLin_rot j) hG) (rein_std_rot hS j)
  rw [rein_frontier_image]
  refine ⟨_, h, ?_⟩
  have e0 := rein_rot_sixthRoot j 0
  have e1 := rein_rot_sixthRoot j 1
  rw [zero_add] at e0
  rw [add_comm 1 j] at e1
  rw [map_add, e0, e1]

/-- In normal position, the critical hexagon with first edge midpoint `s₀*` is the reference
hexagon (proof of Lemma 2.2.7: "each point on the boundary is the edge midpoint of at most one
critical hexagon"). -/
lemma rein_unique_std {K : Set (Fin 2 → ℝ)} (hG : rein_Good K) {w : ZMod 6 → Fin 2 → ℝ}
    (hw : IsLeastAreaHexagon K w) (hwm : ∀ j, hexMidpoint w j = sixthRoot j)
    {v : ZMod 6 → Fin 2 → ℝ} (hv : IsLeastAreaHexagon K v) (hv0 : hexMidpoint v 0 = sixthRoot 0) :
    v = w := by
  have hS : rein_Std K := ⟨w, hw, hwm⟩
  have hK := hG.1
  obtain ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩, ⟨a4, b4⟩, ⟨a5, b5⟩⟩ := rein_coord_sixthRoot
  have hF : ∀ k, hexMidpoint v k ∈ frontier K := rein_hexMidpoint_mem_frontier hK hv
  have hdet := rein_det2_coord_eq (rein_det2_hexMidpoint_std hS hv 0)
  rw [zero_add, hv0, a0, b0] at hdet
  have hB : rein_cB (hexMidpoint v 1) = 1 := by linarith
  have hm2 : hexMidpoint v 2 = hexMidpoint v 1 - sixthRoot 0 := by
    have h := rein_hexMidpoint_succ hv.1 0
    rw [zero_add, show (0 : ZMod 6) + 2 = 2 from rfl, hv0] at h
    rw [h]; abel
  obtain ⟨k, hk⟩ := rein_frontier_InT hK hS (hF 1)
  rw [hB] at hk
  set A := rein_cA (hexMidpoint v 1) with hA
  rcases lt_trichotomy A 0 with hneg | hzero | hpos
  · rcases lt_trichotomy A (-1) with hlt | heq | hgt
    · -- `s₂ = s₁ - s₀*` is outside the triangles
      exfalso
      obtain ⟨k', hk'⟩ := rein_frontier_InT hK hS (hF 2)
      rw [hm2, rein_cA_sub, rein_cB_sub, a0, b0, hB] at hk'
      rcases rein_zmod6_cases k' with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [rein_InT_zero, rein_InT_one, rein_InT_two, rein_InT_three, rein_InT_four,
        rein_InT_five] at hk' <;> obtain ⟨c1, c2, c3⟩ := hk' <;> linarith
    · -- `s₁ = s₂*` and `s₂ = s₂* + s₃*` is a corner
      exfalso
      apply rein_tip_not_mem_frontier_at hG hS 2
      have : hexMidpoint v 2 = sixthRoot 2 + sixthRoot (2 + 1) := by
        rw [hm2]
        apply rein_coord_ext
        · rw [rein_cA_sub, rein_cA_add, a0, show (2 : ZMod 6) + 1 = 3 from rfl, a2, a3, ← hA, heq]
          norm_num
        · rw [rein_cB_sub, rein_cB_add, b0, show (2 : ZMod 6) + 1 = 3 from rfl, b2, b3, hB]
          norm_num
      rw [← this]; exact hF 2
    · -- `s₁` in the relative interior of `(s₁*, s₂*)`
      exfalso
      apply rein_claimE_at hG hS hv 1
      rw [rein_mem_openSegment_sixthRoot, show (1 : ZMod 6) + 1 = 2 from rfl, a1, b1, a2, b2, hB]
      refine ⟨by ring, by linarith, by linarith⟩
  · -- `s₁ = s₁*`: all the edge midpoints agree
    have hm1 : hexMidpoint v 1 = sixthRoot 1 :=
      rein_coord_ext (by rw [a1, ← hA, hzero]) (by rw [b1, hB])
    apply rein_eq_of_hexMidpoint_eq hG hv hw
    have hm2' : hexMidpoint v 2 = sixthRoot 2 := by
      have r := (rein_sixthRoot_rel 0).2.1
      simp only [zero_add] at r
      rw [hm2, hm1, r]; abel
    intro k
    rw [hwm]
    rcases rein_zmod6_cases k with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hv0
    · exact hm1
    · exact hm2'
    · rw [show (3 : ZMod 6) = 0 + 3 from rfl, rein_hexMidpoint_add_three hv.1, hv0,
        (rein_sixthRoot_rel 0).1]
    · rw [show (4 : ZMod 6) = 1 + 3 from rfl, rein_hexMidpoint_add_three hv.1, hm1,
        (rein_sixthRoot_rel 1).1]
    · rw [show (5 : ZMod 6) = 2 + 3 from rfl, rein_hexMidpoint_add_three hv.1, hm2',
        (rein_sixthRoot_rel 2).1]
  · -- `s₁ ∈ T₀ \ {s₀*, s₁*}`: by Lemma 2.2.6, `s₀ = s₀*` would be in the interior of `T₅`
    exfalso
    have hT0 : rein_InT 0 A 1 := by
      rcases rein_zmod6_cases k with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [rein_InT_zero, rein_InT_one, rein_InT_two, rein_InT_three, rein_InT_four,
        rein_InT_five] at hk ⊢ <;> obtain ⟨c1, c2, c3⟩ := hk <;>
      first | exact ⟨c1, c2, c3⟩ | (exfalso; linarith)
    set v' : ZMod 6 → Fin 2 → ℝ := fun i ↦ v (i + 1) with hv'def
    have hv' : IsLeastAreaHexagon K v' := rein_isLeastAreaHexagon_shift hv 1
    have hm : ∀ i, hexMidpoint v' i = hexMidpoint v (i + 1) := fun i ↦ rein_hexMidpoint_shift v 1 i
    have h0 : hexMidpoint v' 0 ∈ sixthTriangle 0 \ {sixthRoot 0, sixthRoot 1} := by
      rw [hm, zero_add]
      refine ⟨by rw [rein_mem_sixthTriangle, hB]; exact hT0, ?_⟩
      rintro (h | h) <;> have := congrArg rein_cA h <;> simp only [a0, a1] at this <;>
        [ (have := congrArg rein_cB h; rw [b0, hB] at this; norm_num at this); linarith ]
    have := rein_lemma2_2_6 hG hS hv' h0 5
    rw [hm, show (5 : ZMod 6) + 1 = 0 from rfl, hv0, rein_mem_interior_sixthTriangle,
      rein_InTo_five, a0, b0] at this
    linarith [this.2.1]

/-- Each boundary point is the edge midpoint of at most one critical hexagon (proof of
Lemma 2.2.7): two least-area hexagons with a common edge midpoint differ by a reindexing. -/
lemma rein_unique {K : Set (Fin 2 → ℝ)} (hG : rein_Good K) {v v' : ZMod 6 → Fin 2 → ℝ}
    (hv : IsLeastAreaHexagon K v) (hv' : IsLeastAreaHexagon K v') {j j' : ZMod 6}
    (h : hexMidpoint v j = hexMidpoint v' j') : ∀ k, v' (k + j') = v (k + j) := by
  set a : ZMod 6 → Fin 2 → ℝ := fun k ↦ v (k + j)
  set b : ZMod 6 → Fin 2 → ℝ := fun k ↦ v' (k + j')
  have ha : IsLeastAreaHexagon K a := rein_isLeastAreaHexagon_shift hv j
  have hb : IsLeastAreaHexagon K b := rein_isLeastAreaHexagon_shift hv' j'
  obtain ⟨e, d, he, hem⟩ := rein_normalize ha
  have hG' := rein_good_image he hG
  have hwa := rein_isLeastAreaHexagon_comp he ha
  have hwb := rein_isLeastAreaHexagon_comp he hb
  have key := rein_unique_std hG' hwa (fun k ↦ by rw [rein_hexMidpoint_comp, hem]) hwb (by
    rw [rein_hexMidpoint_comp, ← hem 0]
    congr 1
    simp only [a, b, rein_hexMidpoint_shift, zero_add]
    exact h.symm)
  intro k
  exact e.injective (congrFun key k)

lemma rein_hexagonOf_eq_of_unique {K : Set (Fin 2 → ℝ)} (hG : rein_Good K)
    {v v' : ZMod 6 → Fin 2 → ℝ} (hv : IsLeastAreaHexagon K v) (hv' : IsLeastAreaHexagon K v')
    {j j' : ZMod 6} (h : hexMidpoint v j = hexMidpoint v' j') : hexagonOf v' = hexagonOf v := by
  have key := rein_unique hG hv hv' h
  rw [← rein_hexagonOf_shift v' j', ← rein_hexagonOf_shift v j]
  congr 1
  funext k
  exact key k

/-- A disk with a unique support line at each boundary point is not a parallelogram: the vertex
`q` of a parallelogram `p, q, -p, -q` containing `K` with `p, q ∈ K` would be a corner. -/
lemma rein_hnp_of_good {K : Set (Fin 2 → ℝ)} (hG : rein_Good K) :
    ∀ p q, 0 < det2 p q →
      (∀ x ∈ K, 0 ≤ det2 (q - p) (x - p) ∧ 0 ≤ det2 (-p - q) (x - q)) → ¬(p ∈ K ∧ q ∈ K) := by
  rintro p q hpq hP ⟨hp, hq⟩
  obtain ⟨hK, hU, -⟩ := hG
  have hne1 : q - p ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [h, rein_det2_self] at hpq; exact lt_irrefl _ hpq
  have hne2 : -p - q ≠ 0 := by
    intro h
    have : q = -p := by rw [← sub_eq_zero, show q - -p = -(-p - q) by abel, h, neg_zero]
    rw [this, rein_det2_neg_right, rein_det2_self, neg_zero] at hpq; exact lt_irrefl _ hpq
  have hL1 := rein_isSupportLine_det2 hne1 (fun x hx ↦ (hP x hx).1) hp
  have hL2 := rein_isSupportLine_det2 hne2 (fun x hx ↦ (hP x hx).2) hq
  have hq1 : q ∈ {x | det2 (q - p) (x - p) = 0} := by simp [rein_det2_self]
  have hq2 : q ∈ {x | det2 (-p - q) (x - q) = 0} := by simp [det2]
  have hqF := rein_mem_frontier_of_supportLine hK.2.1.isClosed hL2 hq hq2
  obtain ⟨ℓ, -, hu⟩ := hU q hqF
  have heq := (hu _ ⟨hL1, hq1⟩).trans (hu _ ⟨hL2, hq2⟩).symm
  have hp1 : p ∈ {x | det2 (q - p) (x - p) = 0} := by simp [det2]
  rw [heq] at hp1
  simp only [mem_ofPred_eq] at hp1
  have : det2 (-p - q) (p - q) = 2 * det2 p q := by
    simp only [det2, Pi.sub_apply, Pi.neg_apply]; ring
  rw [this] at hp1
  linarith

/-! ### The boundary in polar coordinates -/

/-- The direction `e(θ) = (cos θ, sin θ)`. -/
noncomputable def rein_dir (θ : ℝ) : Fin 2 → ℝ := ![Real.cos θ, Real.sin θ]

/-- The boundary point of `K` in the direction `θ`, `e(θ)/g_K(e(θ))` (`g_K` the gauge). -/
noncomputable def rein_bd (K : Set (Fin 2 → ℝ)) (θ : ℝ) : Fin 2 → ℝ :=
  (gauge K (rein_dir θ))⁻¹ • rein_dir θ

lemma rein_det2_dir (α β : ℝ) : det2 (rein_dir α) (rein_dir β) = Real.sin (β - α) := by
  simp only [rein_dir, det2, Matrix.cons_val_zero, Matrix.cons_val_one, Real.sin_sub]
  ring

lemma rein_dir_ne_zero (θ : ℝ) : rein_dir θ ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [rein_dir, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Pi.zero_apply] at h0 h1
  have := Real.sin_sq_add_cos_sq θ
  rw [h0, h1] at this; norm_num at this

lemma rein_nhds_zero {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) : K ∈ 𝓝 (0 : Fin 2 → ℝ) :=
  mem_interior_iff_mem_nhds.1 (rein_zero_mem_interior hK)

lemma rein_gauge_pos {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {x : Fin 2 → ℝ} (hx : x ≠ 0) :
    0 < gauge K x :=
  (gauge_pos (absorbent_nhds_zero (rein_nhds_zero hK))
    (NormedSpace.isVonNBounded_iff ℝ |>.2 hK.2.1.isBounded)).2 hx

lemma rein_gauge_smul {K : Set (Fin 2 → ℝ)} {r : ℝ} (hr : 0 ≤ r) (x : Fin 2 → ℝ) :
    gauge K (r • x) = r * gauge K x := by
  rw [gauge_smul_of_nonneg hr, smul_eq_mul]

lemma rein_bd_mem_frontier {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) (θ : ℝ) :
    rein_bd K θ ∈ frontier K := by
  rw [← gauge_eq_one_iff_mem_frontier hK.1 (rein_nhds_zero hK), rein_bd,
    rein_gauge_smul (inv_nonneg.2 (gauge_nonneg _))]
  exact inv_mul_cancel₀ (rein_gauge_pos hK (rein_dir_ne_zero θ)).ne'

lemma rein_continuous_dir : Continuous rein_dir := by
  unfold rein_dir; fun_prop

lemma rein_continuous_bd {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) : Continuous (rein_bd K) := by
  have hg := (continuous_gauge hK.1 (rein_nhds_zero hK)).comp rein_continuous_dir
  refine (hg.inv₀ fun θ ↦ (rein_gauge_pos hK (rein_dir_ne_zero θ)).ne').smul rein_continuous_dir

lemma rein_bd_add_two_pi (K : Set (Fin 2 → ℝ)) (θ : ℝ) :
    rein_bd K (θ + 2 * π) = rein_bd K θ := by
  simp only [rein_bd, rein_dir, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- A boundary point on the ray in the direction `θ` is the point `rein_bd K θ`. -/
lemma rein_eq_bd {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {u : Fin 2 → ℝ} (hu : u ∈ frontier K)
    {r θ : ℝ} (hr : 0 < r) (h : u = r • rein_dir θ) : u = rein_bd K θ := by
  rw [← gauge_eq_one_iff_mem_frontier hK.1 (rein_nhds_zero hK), h, rein_gauge_smul hr.le] at hu
  have hg := rein_gauge_pos hK (rein_dir_ne_zero θ)
  rw [h, rein_bd]
  congr 1
  field_simp
  linarith

/-- Polar coordinates of a nonzero point. -/
lemma rein_exists_polar {u : Fin 2 → ℝ} (hu : u ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∃ θ, u = r • rein_dir θ := by
  set z : ℂ := ⟨u 0, u 1⟩
  have hz : z ≠ 0 := by
    intro h
    apply hu
    ext i; fin_cases i
    · simpa [z] using congrArg Complex.re h
    · simpa [z] using congrArg Complex.im h
  refine ⟨‖z‖, norm_pos_iff.2 hz, Complex.arg z, ?_⟩
  ext i; fin_cases i
  · simp only [rein_dir, Pi.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.isValue,
      Matrix.cons_val_zero]
    rw [Complex.norm_mul_cos_arg]
  · simp only [rein_dir, Pi.smul_apply, smul_eq_mul, Fin.mk_one, Fin.isValue,
      Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [Complex.norm_mul_sin_arg]

lemma rein_frontier_eq_bd {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {u : Fin 2 → ℝ}
    (hu : u ∈ frontier K) : ∃ θ, u = rein_bd K θ := by
  have hu0 : u ≠ 0 := by
    rintro rfl; exact hu.2 (rein_zero_mem_interior hK)
  obtain ⟨r, hr, θ, h⟩ := rein_exists_polar hu0
  exact ⟨θ, rein_eq_bd hK hu hr h⟩

lemma rein_det2_bd {K : Set (Fin 2 → ℝ)} (α β : ℝ) :
    det2 (rein_bd K α) (rein_bd K β) =
      (gauge K (rein_dir α))⁻¹ * (gauge K (rein_dir β))⁻¹ * Real.sin (β - α) := by
  rw [rein_bd, rein_bd, rein_det2_smul_left, rein_det2_smul_right, rein_det2_dir]; ring

lemma rein_det2_bd_pos_iff {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) (α β : ℝ) :
    0 < det2 (rein_bd K α) (rein_bd K β) ↔ 0 < Real.sin (β - α) := by
  rw [rein_det2_bd]
  have h1 := inv_pos.2 (rein_gauge_pos hK (rein_dir_ne_zero α))
  have h2 := inv_pos.2 (rein_gauge_pos hK (rein_dir_ne_zero β))
  constructor
  · intro h; exact pos_of_mul_pos_right h (mul_pos h1 h2).le
  · intro h; positivity

lemma rein_bd_inj {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {α β : ℝ}
    (h : rein_bd K α = rein_bd K β) : ∃ k : ℤ, β = α + k * (2 * π) := by
  have h1 := inv_pos.2 (rein_gauge_pos hK (rein_dir_ne_zero α))
  have h2 := inv_pos.2 (rein_gauge_pos hK (rein_dir_ne_zero β))
  set gα := (gauge K (rein_dir α))⁻¹
  set gβ := (gauge K (rein_dir β))⁻¹
  have e0 : gα * Real.cos α = gβ * Real.cos β := by
    have := congrFun h 0; simp only [rein_bd, Pi.smul_apply, smul_eq_mul] at this; exact this
  have e1 : gα * Real.sin α = gβ * Real.sin β := by
    have := congrFun h 1; simp only [rein_bd, Pi.smul_apply, smul_eq_mul] at this; exact this
  have hs : gα * Real.sin (β - α) = 0 := by
    rw [Real.sin_sub]
    linear_combination Real.sin β * e0 - Real.cos β * e1
  have hc : gα * Real.cos (β - α) = gβ := by
    rw [Real.cos_sub]
    linear_combination Real.cos β * e0 + Real.sin β * e1 + gβ * Real.sin_sq_add_cos_sq β
  have hs' : Real.sin (β - α) = 0 := (mul_eq_zero.1 hs).resolve_left h1.ne'
  have hc' : 0 < Real.cos (β - α) := by
    have : 0 < gα * Real.cos (β - α) := hc ▸ h2
    exact pos_of_mul_pos_right this h1.le
  have hcos : Real.cos (β - α) = 1 := by
    have := Real.sin_sq_add_cos_sq (β - α)
    rw [hs'] at this
    nlinarith
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).1 hcos
  exact ⟨n, by linarith⟩

/-- Two boundary points on the same ray coincide. -/
lemma rein_frontier_ray {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {u : Fin 2 → ℝ}
    (hu : u ∈ frontier K) {c : ℝ} (hc : 0 < c) (h : c • u ∈ frontier K) : c = 1 := by
  rw [← gauge_eq_one_iff_mem_frontier hK.1 (rein_nhds_zero hK)] at hu h
  rw [rein_gauge_smul hc.le, hu, mul_one] at h
  exact h

/-- Two boundary points `u, x` with `det(u, x) = 0` and `x` not opposite to `u` coincide. -/
lemma rein_frontier_eq_of_det2 {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {u x w : Fin 2 → ℝ}
    (hu : u ∈ frontier K) (hx : x ∈ frontier K) (hw : 0 < det2 u w) (hux : det2 u x = 0)
    (hxw : 0 ≤ det2 x w) : x = u := by
  have hcr := rein_cramer u w x
  rw [hux, zero_smul, add_zero] at hcr
  obtain ⟨c, hcdef⟩ : ∃ c, c = det2 x w / det2 u w := ⟨_, rfl⟩
  have hxc : x = c • u := by
    rw [show c • u = (det2 u w)⁻¹ • (det2 x w • u) by rw [hcdef, smul_smul, div_eq_inv_mul],
      ← hcr, smul_smul, inv_mul_cancel₀ hw.ne', one_smul]
  have hc0 : 0 ≤ c := hcdef ▸ div_nonneg hxw hw.le
  rcases hc0.eq_or_lt with h | h
  · rw [hxc, ← h, zero_smul] at hx
    exact absurd hx (fun h' ↦ h'.2 (rein_zero_mem_interior hK))
  · have := rein_frontier_ray hK hu h (hxc ▸ hx)
    rw [hxc, this, one_smul]

/-! ### Monotonicity in a general position -/

/-- Transitivity of the counterclockwise order of points in the half-plane to the left of `a`. -/
lemma rein_det2_trans {a x y w : Fin 2 → ℝ} (hax : 0 < det2 a x) (hay : 0 < det2 a y)
    (haw : 0 < det2 a w) (hxy : 0 < det2 x y) (hyw : 0 < det2 y w) : 0 < det2 x w := by
  have e : det2 a y * det2 x w = det2 a x * det2 y w + det2 a w * det2 x y := by
    simp only [det2]; ring
  have : 0 < det2 a y * det2 x w := by rw [e]; positivity
  exact pos_of_mul_pos_right this hay.le

/-- Interior points of `T_j` lie strictly inside the cone spanned by `s_j*, s_{j+1}*`. -/
lemma rein_cone_of_mem_interior {j : ZMod 6} {x : Fin 2 → ℝ}
    (h : x ∈ interior (sixthTriangle j)) :
    0 < det2 (sixthRoot j) x ∧ 0 < det2 x (sixthRoot (j + 1)) := by
  have hD := rein_det2_sixthRoot_pos j
  rw [sixthTriangle, rein_mem_interior_convexHull_triple hD] at h
  obtain ⟨h1, h2, h3⟩ := h
  have a1 : det2 x (sixthRoot (j + 1)) / det2 (sixthRoot j) (sixthRoot (j + 1)) > 0 := by
    linarith
  have a2 : det2 (sixthRoot j) x / det2 (sixthRoot j) (sixthRoot (j + 1)) > 0 := by linarith
  exact ⟨(div_pos_iff_of_pos_right hD).1 a2, (div_pos_iff_of_pos_right hD).1 a1⟩

/-- **Comparison principle** (Lemma 2.2.6 in a general position): if the `i`-th edge midpoint of a
critical hexagon `v'` lies strictly between the `i`-th and `(i+1)`-th edge midpoints of a critical
hexagon `v`, then so does the `k`-th one, for every `k`. -/
lemma rein_CP {K : Set (Fin 2 → ℝ)} (hG : rein_Good K) {v v' : ZMod 6 → Fin 2 → ℝ}
    (hv : IsLeastAreaHexagon K v) (hv' : IsLeastAreaHexagon K v') (i : ZMod 6)
    (h1 : 0 < det2 (hexMidpoint v i) (hexMidpoint v' i))
    (h2 : 0 < det2 (hexMidpoint v' i) (hexMidpoint v (i + 1))) :
    ∀ k, 0 < det2 (hexMidpoint v k) (hexMidpoint v' k) ∧
      0 < det2 (hexMidpoint v' k) (hexMidpoint v (k + 1)) := by
  set a : ZMod 6 → Fin 2 → ℝ := fun k ↦ v (k + i)
  set a' : ZMod 6 → Fin 2 → ℝ := fun k ↦ v' (k + i)
  have ha : IsLeastAreaHexagon K a := rein_isLeastAreaHexagon_shift hv i
  have ha' : IsLeastAreaHexagon K a' := rein_isLeastAreaHexagon_shift hv' i
  obtain ⟨e, d, he, hem⟩ := rein_normalize ha
  have hG' := rein_good_image he hG
  have hw := rein_isLeastAreaHexagon_comp he ha
  have hS' : rein_Std (e '' K) := ⟨_, hw, fun k ↦ by rw [rein_hexMidpoint_comp, hem]⟩
  have hb := rein_isLeastAreaHexagon_comp he ha'
  have hmb : ∀ k, hexMidpoint (fun k ↦ e (a' k)) k = e (hexMidpoint v' (k + i)) := by
    intro k; rw [rein_hexMidpoint_comp, rein_hexMidpoint_shift]
  have hsa : ∀ k, sixthRoot k = e (hexMidpoint v (k + i)) := by
    intro k; rw [← hem k, rein_hexMidpoint_shift]
  have hF := rein_hexMidpoint_mem_frontier hG'.1 hb 0
  have c1 : 0 < det2 (sixthRoot 0) (hexMidpoint (fun k ↦ e (a' k)) 0) := by
    rw [hsa, hmb, he.det, zero_add]; exact mul_pos he.pos h1
  have c2 : 0 < det2 (hexMidpoint (fun k ↦ e (a' k)) 0) (sixthRoot (0 + 1)) := by
    rw [hsa, hmb, he.det, zero_add, show (0 : ZMod 6) + 1 + i = i + 1 by ring]
    exact mul_pos he.pos h2
  have hT := rein_mem_T_of_cone hG'.1 hS' hF 0 c1.le c2.le
  have hne0 : hexMidpoint (fun k ↦ e (a' k)) 0 ≠ sixthRoot 0 := by
    intro h; rw [h, rein_det2_self] at c1; exact lt_irrefl _ c1
  have hne1 : hexMidpoint (fun k ↦ e (a' k)) 0 ≠ sixthRoot 1 := by
    intro h; rw [h, zero_add, rein_det2_self] at c2; exact lt_irrefl _ c2
  have key := rein_lemma2_2_6 hG' hS' hb ⟨hT, by rintro (h | h) <;> [exact hne0 h; exact hne1 h]⟩
  intro k
  obtain ⟨k1, k2⟩ := rein_cone_of_mem_interior (key (k - i))
  rw [hsa, hmb, he.det, sub_add_cancel] at k1
  rw [hsa, hmb, he.det, sub_add_cancel, show k - i + 1 + i = k + 1 by ring] at k2
  exact ⟨pos_of_mul_pos_right k1 he.pos.le, pos_of_mul_pos_right k2 he.pos.le⟩

/-- A centrally symmetric hexagon is determined by the lines of its edges. -/
lemma rein_eq_of_edgeLines {v w : ZMod 6 → Fin 2 → ℝ} (hw : IsCSHexagon w)
    (hline : ∀ k, {x | det2 (v (k + 1) - v k) (x - hexMidpoint v k) = 0} =
      {x | det2 (w (k + 1) - w k) (x - hexMidpoint w k) = 0}) : v = w := by
  have hon1 : ∀ (u : ZMod 6 → Fin 2 → ℝ) k,
      det2 (u (k + 1) - u k) (u (k + 1) - hexMidpoint u k) = 0 := by
    intro u k
    simp only [hexMidpoint, midpoint_eq_smul_add, det2, Pi.sub_apply, Pi.smul_apply, Pi.add_apply,
      smul_eq_mul, invOf_eq_inv]
    ring
  have hon2 : ∀ (u : ZMod 6 → Fin 2 → ℝ) k,
      det2 (u (k + 1 + 1) - u (k + 1)) (u (k + 1) - hexMidpoint u (k + 1)) = 0 := by
    intro u k
    simp only [hexMidpoint, midpoint_eq_smul_add, det2, Pi.sub_apply, Pi.smul_apply, Pi.add_apply,
      smul_eq_mul, invOf_eq_inv]
    ring
  funext i
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by ring⟩
  have e1 : v (k + 1) ∈ {x | det2 (w (k + 1) - w k) (x - hexMidpoint w k) = 0} := by
    rw [← hline k]; exact hon1 v k
  have e2 : v (k + 1) ∈
      {x | det2 (w (k + 1 + 1) - w (k + 1)) (x - hexMidpoint w (k + 1)) = 0} := by
    rw [← hline (k + 1)]; exact hon2 v k
  have f1 := hon1 w k
  have f2 := hon2 w k
  simp only [mem_ofPred_eq] at e1 e2
  have hturn := (hw k).2.2
  rw [show k + 2 = k + 1 + 1 by ring] at hturn
  set d := w (k + 1) - w k
  set d' := w (k + 1 + 1) - w (k + 1)
  have g1 : det2 d (v (k + 1) - w (k + 1)) = 0 := by
    have : v (k + 1) - w (k + 1) =
        (v (k + 1) - hexMidpoint w k) - (w (k + 1) - hexMidpoint w k) := by abel
    rw [this, rein_det2_sub_right, e1, f1, sub_zero]
  have g2 : det2 d' (v (k + 1) - w (k + 1)) = 0 := by
    have : v (k + 1) - w (k + 1) =
        (v (k + 1) - hexMidpoint w (k + 1)) - (w (k + 1) - hexMidpoint w (k + 1)) := by abel
    rw [this, rein_det2_sub_right, e2, f2, sub_zero]
  have hcr := rein_cramer d d' (v (k + 1) - w (k + 1))
  rw [rein_det2_swap d' (v (k + 1) - w (k + 1)), g2, g1, neg_zero, zero_smul, zero_smul,
    add_zero] at hcr
  rcases smul_eq_zero.1 hcr with h0 | h0
  · exact absurd h0 hturn.ne'
  · exact sub_eq_zero.1 h0

/-- The line of the edge `k` of a least-area hexagon is the unique support line at its midpoint. -/
lemma rein_edgeLine_eq {K : Set (Fin 2 → ℝ)} (hG : rein_Good K) {v : ZMod 6 → Fin 2 → ℝ}
    (hv : IsLeastAreaHexagon K v) (k : ZMod 6) {ℓ : Set (Fin 2 → ℝ)} (hℓ : IsSupportLine K ℓ)
    (hm : hexMidpoint v k ∈ ℓ) :
    {x | det2 (v (k + 1) - v k) (x - hexMidpoint v k) = 0} = ℓ := by
  obtain ⟨ℓ0, -, hu⟩ := hG.2.1 _ (rein_hexMidpoint_mem_frontier hG.1 hv k)
  rw [hu _ ⟨rein_isSupportLine_edge hG.1 hv k, by simp [det2]⟩, hu _ ⟨hℓ, hm⟩]


/-! ### Angles -/

lemma rein_bd_sub_int (K : Set (Fin 2 → ℝ)) (θ : ℝ) (n : ℤ) :
    rein_bd K (θ - n * (2 * π)) = rein_bd K θ := by
  simp only [rein_bd, rein_dir, Real.cos_sub_int_mul_two_pi, Real.sin_sub_int_mul_two_pi]

lemma rein_exists_bd_Ico {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {u : Fin 2 → ℝ}
    (hu : u ∈ frontier K) (a : ℝ) : ∃ ψ, a ≤ ψ ∧ ψ < a + 2 * π ∧ u = rein_bd K ψ := by
  obtain ⟨θ, rfl⟩ := rein_frontier_eq_bd hK hu
  have hm := toIcoMod_mem_Ico two_pi_pos a θ
  refine ⟨toIcoMod two_pi_pos a θ, hm.1, hm.2, ?_⟩
  rw [← self_sub_toIcoDiv_zsmul, zsmul_eq_mul, rein_bd_sub_int]

lemma rein_sin_pos_iff {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 2 * π) :
    0 < Real.sin x ↔ 0 < x ∧ x < π := by
  constructor
  · intro h
    refine ⟨lt_of_le_of_ne h0 (fun h' ↦ by rw [← h', Real.sin_zero] at h; exact lt_irrefl _ h), ?_⟩
    by_contra hx
    push Not at hx
    have : 0 ≤ Real.sin (x - π) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    rw [Real.sin_sub_pi] at this
    linarith
  · rintro ⟨h0, h1⟩; exact Real.sin_pos_of_pos_of_lt_pi h0 h1

lemma rein_sin_pos_iff' {x : ℝ} (h0 : -π < x) (h1 : x < π) : 0 < Real.sin x ↔ 0 < x := by
  constructor
  · intro h
    by_contra hx
    push Not at hx
    have : 0 ≤ Real.sin (-x) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    rw [Real.sin_neg] at this
    linarith
  · intro h; exact Real.sin_pos_of_pos_of_lt_pi h h1

lemma rein_isClosed_supportLine {K ℓ : Set (Fin 2 → ℝ)} (h : IsSupportLine K ℓ) : IsClosed ℓ := by
  obtain ⟨⟨a, -, c, rfl, -⟩, -⟩ := h
  exact isClosed_eq (continuous_const.dotProduct continuous_id) continuous_const

/-! ### The proof of Lemma 2.2.7: no jumps -/

/-- The boundary between two boundary points `p, q` (`det(p, q) > 0`) is a straight segment if the
support line at each boundary point strictly between them passes through `p` or `q` (connectedness
of the arc, and uniqueness of the support lines). -/
lemma rein_arc_straight {K : Set (Fin 2 → ℝ)} (hG : rein_Good K) {p q : Fin 2 → ℝ}
    (hp : p ∈ frontier K) (hq : q ∈ frontier K) (hpq : 0 < det2 p q)
    (H : ∀ z ∈ frontier K, 0 < det2 p z → 0 < det2 z q →
      ∀ ℓ, IsSupportLine K ℓ → z ∈ ℓ → p ∈ ℓ ∨ q ∈ ℓ)
    {ℓp ℓq : Set (Fin 2 → ℝ)} (hℓp : IsSupportLine K ℓp) (hpℓ : p ∈ ℓp)
    (hℓq : IsSupportLine K ℓq) (hqℓ : q ∈ ℓq) : ℓp = ℓq := by
  obtain ⟨hK, hU, -⟩ := hG
  have huniq : ∀ z ∈ frontier K, ∀ ℓ₁ ℓ₂, IsSupportLine K ℓ₁ → z ∈ ℓ₁ → IsSupportLine K ℓ₂ →
      z ∈ ℓ₂ → ℓ₁ = ℓ₂ := by
    intro z hz ℓ₁ ℓ₂ h1 hz1 h2 hz2
    obtain ⟨ℓ, -, hu⟩ := hU z hz
    rw [hu ℓ₁ ⟨h1, hz1⟩, hu ℓ₂ ⟨h2, hz2⟩]
  obtain ⟨α, -, -, rfl⟩ := rein_exists_bd_Ico hK hp 0
  obtain ⟨β, hβ1, hβ2, rfl⟩ := rein_exists_bd_Ico hK hq α
  have hsin := (rein_det2_bd_pos_iff hK α β).1 hpq
  obtain ⟨hβα, hβπ⟩ := (rein_sin_pos_iff (by linarith) (by linarith)).1 hsin
  have hcov : Icc α β ⊆ rein_bd K ⁻¹' ℓp ∪ rein_bd K ⁻¹' ℓq := by
    intro ψ hψ
    rcases hψ.1.eq_or_lt with h | h
    · left; rw [← h]; exact hpℓ
    rcases hψ.2.eq_or_lt with h' | h'
    · right; rw [h']; exact hqℓ
    have hz := rein_bd_mem_frontier hK ψ
    have h1 : 0 < det2 (rein_bd K α) (rein_bd K ψ) := by
      rw [rein_det2_bd_pos_iff hK]; exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have h2 : 0 < det2 (rein_bd K ψ) (rein_bd K β) := by
      rw [rein_det2_bd_pos_iff hK]; exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    obtain ⟨ℓz, ⟨hℓz, hzℓ⟩, -⟩ := hU _ hz
    rcases H _ hz h1 h2 ℓz hℓz hzℓ with hpz | hqz
    · left; change rein_bd K ψ ∈ ℓp
      rw [← huniq _ hp _ _ hℓz hpz hℓp hpℓ]; exact hzℓ
    · right; change rein_bd K ψ ∈ ℓq
      rw [← huniq _ hq _ _ hℓz hqz hℓq hqℓ]; exact hzℓ
  obtain ⟨ψ, -, hψp, hψq⟩ := isPreconnected_closed_iff.1 isPreconnected_Icc _ _
    ((rein_isClosed_supportLine hℓp).preimage (rein_continuous_bd hK))
    ((rein_isClosed_supportLine hℓq).preimage (rein_continuous_bd hK)) hcov
    ⟨α, left_mem_Icc.2 (by linarith), hpℓ⟩ ⟨β, right_mem_Icc.2 (by linarith), hqℓ⟩
  exact huniq _ (rein_bd_mem_frontier hK ψ) _ _ hℓp hψp hℓq hψq

/-- If the support line at a boundary point `z` strictly between `p` and `q` contains a point
`y ∈ K` not strictly between them, it contains `p` or `q`. -/
lemma rein_supportLine_through_end {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {p q z y : Fin 2 → ℝ}
    (hp : p ∈ frontier K) (hq : q ∈ frontier K) (hpq : 0 < det2 p q) (hpz : 0 < det2 p z)
    (hzq : 0 < det2 z q) {ℓ : Set (Fin 2 → ℝ)} (hℓ : IsSupportLine K ℓ) (hzK : z ∈ K)
    (hzℓ : z ∈ ℓ) (hyK : y ∈ K) (hyℓ : y ∈ ℓ) (hyout : ¬(0 < det2 p y ∧ 0 < det2 y q)) :
    p ∈ ℓ ∨ q ∈ ℓ := by
  obtain ⟨zt, hzt⟩ : ∃ zt : ℝ → Fin 2 → ℝ, zt = fun t ↦ z + t • (y - z) := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : ℝ → ℝ, h = fun t ↦ min (det2 p (zt t)) (det2 (zt t) q) := ⟨_, rfl⟩
  have hzc : Continuous zt := by rw [hzt]; fun_prop
  have hc : Continuous h := by
    rw [hh]
    exact ((rein_continuous_det2_left p).comp hzc).min ((rein_continuous_det2_right q).comp hzc)
  have hz0 : zt 0 = z := by rw [hzt]; simp
  have hz1 : zt 1 = y := by rw [hzt]; simp
  have h0 : 0 ≤ h 0 := by rw [hh]; simp only; rw [hz0]; exact le_min hpz.le hzq.le
  have h1 : h 1 ≤ 0 := by
    rw [hh]; simp only; rw [hz1]
    by_contra hc'
    push Not at hc'
    exact hyout ⟨(lt_min_iff.1 hc').1, (lt_min_iff.1 hc').2⟩
  obtain ⟨t, ht, hht⟩ := intermediate_value_Icc' zero_le_one hc.continuousOn ⟨h1, h0⟩
  have htK : zt t ∈ K := by
    have := hK.1 hzK hyK (sub_nonneg.2 ht.2) ht.1 (sub_add_cancel 1 t)
    convert this using 1
    rw [hzt]; simp only [smul_sub, sub_smul, one_smul]; abel
  have htℓ : zt t ∈ ℓ := by rw [hzt]; exact rein_supportLine_lineMap hℓ hzℓ hyℓ t
  rw [hh] at hht
  simp only at hht
  have htF := rein_mem_frontier_of_supportLine hK.2.1.isClosed hℓ htK htℓ
  rcases min_eq_iff.1 hht with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · left
    have := rein_frontier_eq_of_det2 hK hp htF hpq e1 (by linarith)
    rw [← this]; exact htℓ
  · right
    have hq' : 0 < det2 q (-p) := by rw [rein_det2_neg_right, rein_det2_swap, neg_neg]; exact hpq
    have e3 : det2 q (zt t) = 0 := by rw [rein_det2_swap]; linarith
    have := rein_frontier_eq_of_det2 hK hq htF hq' e3 (by
      rw [rein_det2_neg_right, rein_det2_swap, neg_neg]; linarith)
    rw [← this]; exact htℓ

/-- **No jumps** (proof of Lemma 2.2.7). Let `v₁, v₂` be critical hexagons whose first edge
midpoints `p₀, q₀` (`det(p₀, q₀) > 0`, `q₀` not beyond the second midpoint `p₁` of `v₁`) bound
an arc of the boundary without edge midpoints of critical hexagons. Then `v₁ = v₂`: by
monotonicity, the arcs between `p_j` and `q_j` contain no edge midpoints either; by Lemma 2.2.5
they are straight; so `v₁` and `v₂` have the same edge lines. -/
lemma rein_gap_eq {K : Set (Fin 2 → ℝ)} (hG : rein_Good K) {v1 v2 : ZMod 6 → Fin 2 → ℝ}
    (hv1 : IsLeastAreaHexagon K v1) (hv2 : IsLeastAreaHexagon K v2)
    (h01 : 0 < det2 (hexMidpoint v1 0) (hexMidpoint v2 0))
    (h0p1 : 0 ≤ det2 (hexMidpoint v2 0) (hexMidpoint v1 1))
    (hgap : ∀ v3, IsLeastAreaHexagon K v3 → ∀ k,
      ¬(0 < det2 (hexMidpoint v1 0) (hexMidpoint v3 k) ∧
        0 < det2 (hexMidpoint v3 k) (hexMidpoint v2 0))) : v1 = v2 := by
  have hK := hG.1
  set p := hexMidpoint v1 with hp
  set q := hexMidpoint v2 with hq
  have hpF : ∀ k, p k ∈ frontier K := rein_hexMidpoint_mem_frontier hK hv1
  have hqF : ∀ k, q k ∈ frontier K := rein_hexMidpoint_mem_frontier hK hv2
  have hpp : ∀ k, 0 < det2 (p k) (p (k + 1)) := fun k ↦ by
    rw [rein_det2_hexMidpoint hv1.1]; exact rein_det2_hexMidpoint_pos hv1.1
  have hqq : ∀ k, 0 < det2 (q k) (q (k + 1)) := fun k ↦ by
    rw [rein_det2_hexMidpoint hv2.1]; exact rein_det2_hexMidpoint_pos hv2.1
  -- the two cases: `q₀` strictly before `p₁`, or `q₀ = p₁`
  have hp01 : 0 < det2 (p 0) (p 1) := by have := hpp 0; rwa [zero_add] at this
  have hcase : (∀ k, 0 < det2 (p k) (q k) ∧ 0 < det2 (q k) (p (k + 1))) ∨
      (∀ k, q k = p (k + 1)) := by
    rcases h0p1.lt_or_eq with h | h
    · exact Or.inl (rein_CP hG hv1 hv2 0 h01 (by rw [zero_add]; exact h))
    · right
      have hq' : 0 < det2 (q 0) (-p 0) := by
        rw [rein_det2_neg_right, rein_det2_swap, neg_neg]; exact h01
      have hp1 : 0 ≤ det2 (p 1) (-p 0) := by
        rw [rein_det2_neg_right, rein_det2_swap, neg_neg]; exact hp01.le
      have e := rein_frontier_eq_of_det2 hK (hqF 0) (hpF 1) hq' h.symm hp1
      have key := rein_unique hG hv1 hv2 (j := 1) (j' := 0) e
      intro k
      have hv2k : v2 = fun i ↦ v1 (i + 1) := funext fun i ↦ by simpa using key i
      rw [hq, hp, hv2k, rein_hexMidpoint_shift]
  have hpq : ∀ k, 0 < det2 (p k) (q k) := by
    rcases hcase with h | h
    · exact fun k ↦ (h k).1
    · intro k; rw [h k]; exact hpp k
  -- monotonicity: no edge midpoint strictly between `p_j` and `q_j`
  have hA : ∀ j v3, IsLeastAreaHexagon K v3 → ∀ i,
      ¬(0 < det2 (p j) (hexMidpoint v3 i) ∧ 0 < det2 (hexMidpoint v3 i) (q j)) := by
    rintro j v3 hv3 i ⟨hz1, hz2⟩
    set v3' : ZMod 6 → Fin 2 → ℝ := fun k ↦ v3 (k + (i - j))
    have hv3' : IsLeastAreaHexagon K v3' := rein_isLeastAreaHexagon_shift hv3 _
    have hz : hexMidpoint v3' j = hexMidpoint v3 i := by
      simp only [v3', rein_hexMidpoint_shift]; congr 1; ring
    rw [← hz] at hz1 hz2
    have hz3 : 0 < det2 (hexMidpoint v3' j) (p (j + 1)) := by
      rcases hcase with h | h
      · exact rein_det2_trans hz1 (hpq j) (hpp j) hz2 (h j).2
      · rw [← h j]; exact hz2
    have hCP := rein_CP hG hv1 hv3' j hz1 hz3
    obtain ⟨c1, c2⟩ := hCP 0
    rw [zero_add] at c2
    have hng := hgap v3' hv3' 0
    rcases (not_lt.1 fun h ↦ hng ⟨c1, h⟩).lt_or_eq with h | h
    · -- `z₀` strictly beyond `q₀`
      have h' : 0 < det2 (q 0) (hexMidpoint v3' 0) := by rw [rein_det2_swap]; linarith
      have c3 : 0 < det2 (hexMidpoint v3' 0) (q (0 + 1)) := by
        rcases hcase with hc | hc
        · have hq01 : 0 < det2 (q 0) (q (0 + 1)) := hqq 0
          rw [zero_add] at hq01 ⊢
          have a1 := (hc 0).2
          rw [zero_add] at a1
          exact rein_det2_trans h' a1 hq01 c2 (hc 1).1
        · exfalso
          rw [hc 0, zero_add] at h
          linarith
      have := (rein_CP hG hv2 hv3' 0 h' c3 j).1
      rw [rein_det2_swap] at this
      linarith
    · -- `z₀ = q₀`: then `v₃' = v₂`
      have hq' : 0 < det2 (q 0) (-p 0) := by
        rw [rein_det2_neg_right, rein_det2_swap, neg_neg]; exact hpq 0
      have e := rein_frontier_eq_of_det2 hK (hqF 0) (rein_hexMidpoint_mem_frontier hK hv3' 0) hq'
        (by rw [rein_det2_swap, h, neg_zero]) (by
          rw [rein_det2_neg_right, rein_det2_swap, neg_neg]; exact c1.le)
      have key := rein_unique hG hv2 hv3' (j := 0) (j' := 0) e.symm
      have : v3' = v2 := funext fun k ↦ by simpa using key k
      rw [this] at hz2
      rw [rein_det2_self] at hz2
      exact lt_irrefl _ hz2
  -- the boundary arcs between `p_j` and `q_j` are straight, so the edge lines agree
  apply rein_eq_of_edgeLines hv2.1
  intro j
  obtain ⟨ℓp, ⟨hℓp, hpℓ⟩, -⟩ := hG.2.1 _ (hpF j)
  obtain ⟨ℓq, ⟨hℓq, hqℓ⟩, -⟩ := hG.2.1 _ (hqF j)
  rw [rein_edgeLine_eq hG hv1 j hℓp hpℓ, rein_edgeLine_eq hG hv2 j hℓq hqℓ]
  refine rein_arc_straight hG (hpF j) (hqF j) (hpq j) (fun z hz hz1 hz2 ℓ hℓ hzℓ ↦ ?_)
    hℓp hpℓ hℓq hqℓ
  obtain ⟨v4, hv4, k, hk⟩ := hG.2.2 z hz ℓ hℓ hzℓ
  exact rein_supportLine_through_end hK (hpF j) (hqF j) (hpq j) hz1 hz2 hℓ
    (rein_frontier_subset hK hz) hzℓ
    (rein_frontier_subset hK (rein_hexMidpoint_mem_frontier hK hv4 k))
    (hk (midpoint_mem_segment _ _)) (hA j v4 hv4 k)


/-! ### Every boundary point is an edge midpoint -/

/-- The angles of the boundary points that are first edge midpoints of critical hexagons. -/
def rein_Θ (K : Set (Fin 2 → ℝ)) : Set ℝ :=
  {θ | ∃ v, IsLeastAreaHexagon K v ∧ hexMidpoint v 0 = rein_bd K θ}

lemma rein_least_volume_eq {K : Set (Fin 2 → ℝ)} {v w : ZMod 6 → Fin 2 → ℝ}
    (hv : IsLeastAreaHexagon K v) (hw : IsLeastAreaHexagon K w) :
    volume.real (hexagonOf v) = volume.real (hexagonOf w) :=
  le_antisymm (rein_least_le hv hw.1 hw.2.1) (rein_least_le hw hv.1 hv.2.1)

lemma rein_continuous_hexMidpoint (j : ZMod 6) :
    Continuous fun u : ZMod 6 → Fin 2 → ℝ ↦ hexMidpoint u j := by
  unfold hexMidpoint; simp only [midpoint_eq_smul_add]; fun_prop

/-- **The set of critical hexagons is closed** (proof of Lemma 2.2.5): a sequence of critical
hexagons whose first edge midpoints converge to `u` has a subsequence converging to a critical
hexagon with first edge midpoint `u`. -/
lemma rein_limit_critical {K : Set (Fin 2 → ℝ)} (hG : rein_Good K)
    (v : ℕ → ZMod 6 → Fin 2 → ℝ) (hv : ∀ n, IsLeastAreaHexagon K (v n)) :
    ∃ w, IsLeastAreaHexagon K w ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n ↦ v (φ n)) atTop (𝓝 w) := by
  have hA : ∀ w, IsCSHexagon w → K ⊆ hexagonOf w →
      volume.real (hexagonOf (v 0)) ≤ volume.real (hexagonOf w) :=
    fun w hw hKw ↦ rein_least_le (hv 0) hw hKw
  have harea : Tendsto (fun n ↦ volume.real (hexagonOf (v n))) atTop
      (𝓝 (volume.real (hexagonOf (v 0)))) := by
    simp only [rein_least_volume_eq (hv _) (hv 0)]; exact tendsto_const_nhds
  obtain ⟨w, hw, -, φ, hφ, hconv⟩ := rein_limit_hex hG.1 (rein_hnp_of_good hG) hA v
    (fun n ↦ (hv n).1) (fun n ↦ (hv n).2.1) harea
  exact ⟨w, hw, φ, hφ, hconv⟩

lemma rein_isClosed_Θ {K : Set (Fin 2 → ℝ)} (hG : rein_Good K) : IsClosed (rein_Θ K) := by
  refine IsSeqClosed.isClosed fun θs θ hθs hlim ↦ ?_
  choose v hv hvm using hθs
  obtain ⟨w, hw, φ, hφ, hconv⟩ := rein_limit_critical hG v hv
  refine ⟨w, hw, tendsto_nhds_unique (((rein_continuous_hexMidpoint 0).tendsto w).comp hconv) ?_⟩
  have := ((rein_continuous_bd hG.1).tendsto θ).comp (hlim.comp hφ.tendsto_atTop)
  refine this.congr fun n ↦ ?_
  simp only [Function.comp_apply, hvm]

lemma rein_mem_Θ_sub_int {K : Set (Fin 2 → ℝ)} {θ : ℝ} (h : θ ∈ rein_Θ K) (n : ℤ) :
    θ - n * (2 * π) ∈ rein_Θ K := by
  obtain ⟨v, hv, hvm⟩ := h
  exact ⟨v, hv, by rw [rein_bd_sub_int, hvm]⟩

/-- Every edge midpoint of a critical hexagon is the boundary point at an angle in `rein_Θ`, which
can be taken in any interval `[a, a + 2π)`. -/
lemma rein_midpoint_mem_Θ {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {v : ZMod 6 → Fin 2 → ℝ}
    (hv : IsLeastAreaHexagon K v) (k : ZMod 6) (a : ℝ) :
    ∃ ψ, a ≤ ψ ∧ ψ < a + 2 * π ∧ ψ ∈ rein_Θ K ∧ hexMidpoint v k = rein_bd K ψ := by
  obtain ⟨ψ, h1, h2, h3⟩ := rein_exists_bd_Ico hK (rein_hexMidpoint_mem_frontier hK hv k) a
  refine ⟨ψ, h1, h2, ⟨fun i ↦ v (i + k), rein_isLeastAreaHexagon_shift hv k, ?_⟩, h3⟩
  rw [rein_hexMidpoint_shift, zero_add, h3]

/-- **Every boundary point is an edge midpoint of a critical hexagon** (Lemma 2.2.7): the angles
of the edge midpoints form a closed set without gaps. -/
lemma rein_mem_Θ {K : Set (Fin 2 → ℝ)} (hG : rein_Good K) (θ : ℝ) : θ ∈ rein_Θ K := by
  have hK := hG.1
  by_contra hθ
  have hC := rein_isClosed_Θ hG
  obtain ⟨v0, hv0⟩ := rein_exists_least hK (rein_hnp_of_good hG)
  obtain ⟨θ0, -, -, hθ0, -⟩ := rein_midpoint_mem_Θ hK hv0 0 0
  have h2π := Real.two_pi_pos
  -- the largest angle `θ₁ ≤ θ` and the smallest angle `θ₂ ≥ θ` in `rein_Θ`
  have hne1 : (rein_Θ K ∩ Iic θ).Nonempty := by
    refine ⟨θ0 - ⌈(θ0 - θ) / (2 * π)⌉ * (2 * π), rein_mem_Θ_sub_int hθ0 _, ?_⟩
    have := Int.le_ceil ((θ0 - θ) / (2 * π))
    rw [div_le_iff₀ h2π] at this
    simp only [mem_Iic]; linarith
  have hne2 : (rein_Θ K ∩ Ici θ).Nonempty := by
    refine ⟨θ0 - ⌊(θ0 - θ) / (2 * π)⌋ * (2 * π), rein_mem_Θ_sub_int hθ0 _, ?_⟩
    have := Int.floor_le ((θ0 - θ) / (2 * π))
    rw [le_div_iff₀ h2π] at this
    simp only [mem_Ici]; linarith
  set θ1 := sSup (rein_Θ K ∩ Iic θ)
  set θ2 := sInf (rein_Θ K ∩ Ici θ)
  have hb1 : BddAbove (rein_Θ K ∩ Iic θ) := ⟨θ, fun x hx ↦ hx.2⟩
  have hb2 : BddBelow (rein_Θ K ∩ Ici θ) := ⟨θ, fun x hx ↦ hx.2⟩
  have hθ1 := (hC.inter isClosed_Iic).csSup_mem hne1 hb1
  have hθ2 := (hC.inter isClosed_Ici).csInf_mem hne2 hb2
  have hθ1θ : θ1 < θ := lt_of_le_of_ne hθ1.2 (fun h ↦ hθ (h ▸ hθ1.1))
  have hθθ2 : θ < θ2 := lt_of_le_of_ne hθ2.2 (fun h ↦ hθ (h ▸ hθ2.1))
  have hgapΘ : ∀ ψ ∈ rein_Θ K, ¬(θ1 < ψ ∧ ψ < θ2) := by
    rintro ψ hψ ⟨h1, h2⟩
    rcases le_total ψ θ with h | h
    · exact absurd (le_csSup hb1 ⟨hψ, h⟩) (not_le.2 h1)
    · exact absurd (csInf_le hb2 ⟨hψ, h⟩) (not_le.2 h2)
  obtain ⟨v1, hv1, hm1⟩ := hθ1.1
  obtain ⟨v2, hv2, hm2⟩ := hθ2.1
  -- the second edge midpoint of `v₁` is at an angle `ψ ∈ (θ₁, θ₁ + π)`, not in the gap
  obtain ⟨ψ, hψ1, hψ2, hψΘ, hψm⟩ := rein_midpoint_mem_Θ hK hv1 1 θ1
  have hdet01 := rein_det2_hexMidpoint_pos hv1.1
  rw [hm1, hψm, rein_det2_bd_pos_iff hK] at hdet01
  obtain ⟨hψa, hψb⟩ := (rein_sin_pos_iff (by linarith) (by linarith)).1 hdet01
  have hθ2ψ : θ2 ≤ ψ := by
    by_contra h; push Not at h; exact hgapΘ ψ hψΘ ⟨by linarith, h⟩
  have h01 : 0 < det2 (hexMidpoint v1 0) (hexMidpoint v2 0) := by
    rw [hm1, hm2, rein_det2_bd_pos_iff hK]
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have h0p1 : 0 ≤ det2 (hexMidpoint v2 0) (hexMidpoint v1 1) := by
    rw [hm2, hψm, rein_det2_bd]
    have := Real.sin_nonneg_of_nonneg_of_le_pi (show 0 ≤ ψ - θ2 by linarith)
      (show ψ - θ2 ≤ π by linarith)
    have g1 := inv_pos.2 (rein_gauge_pos hK (rein_dir_ne_zero θ2))
    have g2 := inv_pos.2 (rein_gauge_pos hK (rein_dir_ne_zero ψ))
    positivity
  have hgap : ∀ v3, IsLeastAreaHexagon K v3 → ∀ k,
      ¬(0 < det2 (hexMidpoint v1 0) (hexMidpoint v3 k) ∧
        0 < det2 (hexMidpoint v3 k) (hexMidpoint v2 0)) := by
    rintro v3 hv3 k ⟨h1, h2⟩
    obtain ⟨ψ', h1', h2', hψ'Θ, hψ'm⟩ := rein_midpoint_mem_Θ hK hv3 k θ1
    rw [hm1, hψ'm, rein_det2_bd_pos_iff hK] at h1
    rw [hm2, hψ'm, rein_det2_bd_pos_iff hK] at h2
    obtain ⟨a1, a2⟩ := (rein_sin_pos_iff (by linarith) (by linarith)).1 h1
    have a3 := (rein_sin_pos_iff' (by linarith) (by linarith)).1 h2
    exact hgapΘ ψ' hψ'Θ ⟨by linarith, by linarith⟩
  have heq := rein_gap_eq hG hv1 hv2 h01 h0p1 hgap
  rw [heq, hm2] at hm1
  obtain ⟨k, hk⟩ := rein_bd_inj hK hm1
  have hk' : θ1 = θ2 + k * (2 * π) := hk
  rcases le_or_gt 0 k with hk0 | hk0
  · have : (0 : ℝ) ≤ k := by exact_mod_cast hk0
    have := mul_nonneg this h2π.le
    linarith
  · have : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
    have := mul_le_mul_of_nonneg_right this h2π.le
    linarith [Real.pi_pos]


/-! ### Angles between points -/

/-- A point of the plane as a complex number. -/
noncomputable def rein_toC (v : Fin 2 → ℝ) : ℂ := (v 0 : ℂ) + (v 1 : ℂ) * Complex.I

lemma rein_toC_re (v : Fin 2 → ℝ) : (rein_toC v).re = v 0 := by simp [rein_toC]
lemma rein_toC_im (v : Fin 2 → ℝ) : (rein_toC v).im = v 1 := by simp [rein_toC]

lemma rein_toC_ne_zero {x : Fin 2 → ℝ} (hx : x ≠ 0) : rein_toC x ≠ 0 := by
  intro h
  apply hx
  ext i; fin_cases i
  · simpa [rein_toC_re] using congrArg Complex.re h
  · simpa [rein_toC_im] using congrArg Complex.im h

lemma rein_continuous_toC : Continuous rein_toC := by
  unfold rein_toC; fun_prop

/-- The angle from `x` to `y`, in `(-π, π]`. -/
noncomputable def rein_ang (x y : Fin 2 → ℝ) : ℝ := Complex.arg (rein_toC y / rein_toC x)

lemma rein_im_div_pos {x y : Fin 2 → ℝ} (hx : x ≠ 0) (h : 0 < det2 x y) :
    0 < (rein_toC y / rein_toC x).im := by
  rw [Complex.div_im, rein_toC_re, rein_toC_re, rein_toC_im, rein_toC_im, ← sub_div]
  apply div_pos _ (Complex.normSq_pos.2 (rein_toC_ne_zero hx))
  simp only [det2] at h; linarith

/-- If `x` is on the ray of angle `θ`, then `y` is on the ray of angle `θ + rein_ang x y`. -/
lemma rein_ang_spec {x y : Fin 2 → ℝ} {c θ : ℝ} (hc : 0 < c) (hx : x = c • rein_dir θ)
    (hy : y ≠ 0) : ∃ r : ℝ, 0 < r ∧ y = r • rein_dir (θ + rein_ang x y) := by
  have hx0 : x ≠ 0 := by rw [hx]; exact smul_ne_zero hc.ne' (rein_dir_ne_zero θ)
  set w := rein_toC y / rein_toC x with hw
  have hw0 : w ≠ 0 := div_ne_zero (rein_toC_ne_zero hy) (rein_toC_ne_zero hx0)
  have hxc : rein_toC x = (c : ℂ) * Complex.exp (θ * Complex.I) := by
    apply Complex.ext
    · rw [rein_toC_re, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, hx]; rfl
    · rw [rein_toC_im, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im, hx]; rfl
  have hyc :
      rein_toC y = ((c * ‖w‖ : ℝ) : ℂ) * Complex.exp ((θ + Complex.arg w : ℝ) * Complex.I) := by
    have h1 : rein_toC y = rein_toC x * w := by
      rw [hw, mul_div_cancel₀ _ (rein_toC_ne_zero hx0)]
    have hwexp := Complex.norm_mul_exp_arg_mul_I w
    rw [h1, hxc]
    nth_rewrite 1 [← hwexp]
    push_cast
    rw [add_mul, Complex.exp_add]
    ring
  refine ⟨c * ‖w‖, mul_pos hc (norm_pos_iff.2 hw0), ?_⟩
  ext i; fin_cases i
  · have := congrArg Complex.re hyc
    rw [rein_toC_re, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re] at this
    simpa [rein_dir, rein_ang, hw] using this
  · have := congrArg Complex.im hyc
    rw [rein_toC_im, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im] at this
    simpa [rein_dir, rein_ang, hw] using this

lemma rein_continuous_ang {f g : ℝ → Fin 2 → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ t, f t ≠ 0 ∧ 0 < det2 (f t) (g t)) : Continuous fun t ↦ rein_ang (f t) (g t) := by
  have hq : Continuous fun t ↦ rein_toC (g t) / rein_toC (f t) :=
    (rein_continuous_toC.comp hg).div (rein_continuous_toC.comp hf)
      fun t ↦ rein_toC_ne_zero (h t).1
  refine continuous_iff_continuousAt.2 fun t ↦ ?_
  refine (Complex.continuousAt_arg ?_).comp hq.continuousAt
  rw [Complex.mem_slitPlane_iff]
  exact Or.inr (rein_im_div_pos (h t).1 (h t).2).ne'

/-! ### The edge midpoints as functions of the angle -/

section midpointFunctions

variable {K : Set (Fin 2 → ℝ)} (hG : rein_Good K) {V : ℝ → ZMod 6 → Fin 2 → ℝ}
  (hV : ∀ θ, IsLeastAreaHexagon K (V θ)) (hVm : ∀ θ, hexMidpoint (V θ) 0 = rein_bd K θ)
include hG hV hVm

lemma rein_V_unique {θ : ℝ} {v : ZMod 6 → Fin 2 → ℝ} (hv : IsLeastAreaHexagon K v)
    (hvm : hexMidpoint v 0 = rein_bd K θ) : v = V θ :=
  funext fun k ↦ by
    have := rein_unique hG hv (hV θ) (j := 0) (j' := 0) (hvm.trans (hVm θ).symm) k
    simpa using this.symm

lemma rein_V_sub_int (θ : ℝ) (n : ℤ) : V (θ - n * (2 * π)) = V θ :=
  (rein_V_unique hG hV hVm (hV _) (by rw [hVm, rein_bd_sub_int])).symm

lemma rein_continuous_V : Continuous V := by
  refine continuous_iff_seqContinuous.2 fun θs θ hlim ↦ ?_
  refine tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  obtain ⟨w, hw, φ, hφ, hconv⟩ := rein_limit_critical hG (fun n ↦ V (θs (ns n))) (fun n ↦ hV _)
  have hwm : hexMidpoint w 0 = rein_bd K θ := by
    refine tendsto_nhds_unique (((rein_continuous_hexMidpoint 0).tendsto w).comp hconv) ?_
    have := ((rein_continuous_bd hG.1).tendsto θ).comp
      ((hlim.comp hns).comp hφ.tendsto_atTop)
    refine this.congr fun n ↦ ?_
    simp only [Function.comp_apply, hVm]
  rw [rein_V_unique hG hV hVm hw hwm] at hconv
  exact ⟨φ, hconv⟩

/-- The angle of the `j`-th edge midpoint, for `j = 1, 2`. -/
noncomputable def rein_φ (V : ℝ → ZMod 6 → Fin 2 → ℝ) (K : Set (Fin 2 → ℝ)) (j : ZMod 6)
    (θ : ℝ) : ℝ :=
  θ + rein_ang (rein_bd K θ) (hexMidpoint (V θ) j)

omit hG hV hVm in
lemma rein_det2_hexMidpoint_two {v : ZMod 6 → Fin 2 → ℝ} (hv : IsCSHexagon v) :
    0 < det2 (hexMidpoint v 0) (hexMidpoint v 2) := by
  have h := rein_hexMidpoint_succ hv 0
  rw [zero_add, show (0 : ZMod 6) + 2 = 2 from rfl] at h
  have : hexMidpoint v 2 = hexMidpoint v 1 - hexMidpoint v 0 := by rw [h]; abel
  rw [this, rein_det2_sub_right, rein_det2_self, sub_zero]
  exact rein_det2_hexMidpoint_pos hv

omit hVm in
lemma rein_φ_spec {j : ZMod 6} (θ : ℝ) :
    ∃ r : ℝ, 0 < r ∧ hexMidpoint (V θ) j = r • rein_dir (rein_φ V K j θ) := by
  have hg := rein_gauge_pos hG.1 (rein_dir_ne_zero θ)
  have hy : hexMidpoint (V θ) j ≠ 0 := by
    intro h
    have hF := rein_hexMidpoint_mem_frontier hG.1 (hV θ) j
    rw [h] at hF
    exact hF.2 (rein_zero_mem_interior hG.1)
  exact rein_ang_spec (inv_pos.2 hg) rfl hy

lemma rein_continuous_φ {j : ZMod 6} (hj : j = 1 ∨ j = 2) : Continuous (rein_φ V K j) := by
  refine continuous_id.add (rein_continuous_ang (rein_continuous_bd hG.1)
    ((rein_continuous_hexMidpoint j).comp (rein_continuous_V hG hV hVm)) fun θ ↦ ⟨?_, ?_⟩)
  · exact fun h ↦ (rein_bd_mem_frontier hG.1 θ).2 (h ▸ rein_zero_mem_interior hG.1)
  · rw [← hVm θ]
    rcases hj with rfl | rfl
    · exact rein_det2_hexMidpoint_pos (hV θ).1
    · exact rein_det2_hexMidpoint_two (hV θ).1

lemma rein_φ_add_int {j : ZMod 6} (θ : ℝ) (n : ℤ) :
    rein_φ V K j (θ + n * (2 * π)) = rein_φ V K j θ + n * (2 * π) := by
  have h1 : V (θ + n * (2 * π)) = V θ := by
    have := rein_V_sub_int hG hV hVm (θ + n * (2 * π)) n
    rw [add_sub_cancel_right] at this; exact this.symm
  have h2 : rein_bd K (θ + n * (2 * π)) = rein_bd K θ := by
    have := rein_bd_sub_int K (θ + n * (2 * π)) n
    rw [add_sub_cancel_right] at this; exact this.symm
  simp only [rein_φ, h1, h2]; ring

lemma rein_strictMono_φ {j : ZMod 6} (hj : j = 1 ∨ j = 2) : StrictMono (rein_φ V K j) := by
  have hinj : Function.Injective (rein_φ V K j) := by
    intro θ θ' h
    obtain ⟨r, hr, hm⟩ := rein_φ_spec hG hV θ
    obtain ⟨r', hr', hm'⟩ := rein_φ_spec hG hV θ'
    rw [← h] at hm'
    have e1 := rein_eq_bd hG.1 (rein_hexMidpoint_mem_frontier hG.1 (hV θ) j) hr hm
    have e2 := rein_eq_bd hG.1 (rein_hexMidpoint_mem_frontier hG.1 (hV θ') j) hr' hm'
    have key := rein_unique hG (hV θ) (hV θ') (e1.trans e2.symm)
    have hVV : V θ' = V θ := funext fun k ↦ by simpa using key (k - j)
    have hb : rein_bd K θ = rein_bd K θ' := by rw [← hVm, ← hVm, hVV]
    obtain ⟨k, hk⟩ := rein_bd_inj hG.1 hb
    rw [hk, rein_φ_add_int hG hV hVm] at h
    have : (k : ℝ) * (2 * π) = 0 := by linarith
    rcases mul_eq_zero.1 this with h0 | h0
    · rw [hk, h0, zero_mul, add_zero]
    · exact absurd h0 Real.two_pi_pos.ne'
  rcases (rein_continuous_φ hG hV hVm hj).strictMono_of_inj hinj with h | h
  · exact h
  · exfalso
    have := h (show 0 < 0 + 1 * (2 * π) by linarith [Real.two_pi_pos])
    have e := rein_φ_add_int hG hV hVm (j := j) 0 1
    push_cast at e
    linarith [Real.two_pi_pos]

end midpointFunctions

lemma rein_dir_add_pi (θ : ℝ) : rein_dir (θ + π) = -rein_dir θ := by
  ext i; fin_cases i <;> simp [rein_dir, Real.cos_add_pi, Real.sin_add_pi]

/-- **Lemma 2.2.7** (`lem:multi-cont`). Let `K = K_min` have worst greatest packing density.
Then every point of the boundary of `K` is the midpoint of an edge of a unique critical hexagon.
As `s₀` advances around the boundary of `K` in a counterclockwise direction, the five other
midpoints `s₁, …, s₅` advance strictly monotonically and continuously in a counterclockwise
direction.

The second part is stated with polar angles: when `s₀` is the boundary point at angle `θ`, the
midpoint `s_j` of the critical hexagon is the boundary point at angle `φ_j(θ)`, where `φ₀ = id`
and each `φ_j` is a continuous strictly increasing lift of a circle map
(`φ_j(θ + 2π) = φ_j(θ) + 2π`).

Gaps in the paper's proof, filled along its lines: the set of angles of edge midpoints of critical
hexagons is closed (a limit of critical hexagons is critical, by compactness), which gives the
"largest interval" of the book; the boundary is parametrized by polar angle through the gauge of
`K`; two critical hexagons with the same edge lines coincide; continuity of the `φ_j` is proved
by subsequences and their strict monotonicity from injectivity and continuity. -/
theorem lemma2_2_7 {K : Set (Fin 2 → ℝ)} (hK : IsWorstDisk K) :
    (∀ u ∈ frontier K, ∃! H, ∃ v, IsLeastAreaHexagon K v ∧ hexagonOf v = H ∧
      ∃ j, hexMidpoint v j = u) ∧
    ∃ φ : ZMod 6 → ℝ → ℝ, φ 0 = id ∧
      (∀ j, Continuous (φ j) ∧ StrictMono (φ j) ∧ ∀ θ, φ j (θ + 2 * π) = φ j θ + 2 * π) ∧
      ∀ θ, ∃ v, IsLeastAreaHexagon K v ∧ ∀ j, hexMidpoint v j ∈ frontier K ∧
        ∃ r : ℝ, 0 < r ∧ hexMidpoint v j = r • ![cos (φ j θ), sin (φ j θ)] := by
  have hG : rein_Good K := rein_good_of_worst (ch2_isWorstLatticeDisk_iff_isWorstDisk.2 hK)
  have hK' := hG.1
  refine ⟨fun u hu ↦ ?_, ?_⟩
  · -- every boundary point is an edge midpoint (no jumps), of a unique critical hexagon
    -- (monotonicity)
    obtain ⟨θ, rfl⟩ := rein_frontier_eq_bd hK' hu
    obtain ⟨v, hv, hvm⟩ := rein_mem_Θ hG θ
    refine ⟨hexagonOf v, ⟨v, hv, rfl, 0, hvm⟩, ?_⟩
    rintro H ⟨v', hv', rfl, j, hj⟩
    exact rein_hexagonOf_eq_of_unique hG hv hv' (hvm.trans hj.symm)
  · -- the edge midpoints move continuously and strictly monotonically
    choose V hV hVm using rein_mem_Θ hG
    have hp1 := rein_φ_add_int hG hV hVm (j := 1)
    have hp2 := rein_φ_add_int hG hV hVm (j := 2)
    have h2π : ∀ θ : ℝ, θ + 2 * π = θ + ((1 : ℤ) : ℝ) * (2 * π) := fun θ ↦ by push_cast; ring
    refine ⟨fun k ↦ (![id, rein_φ V K 1, rein_φ V K 2, fun θ ↦ θ + π,
      fun θ ↦ rein_φ V K 1 θ + π, fun θ ↦ rein_φ V K 2 θ + π] : Fin 6 → ℝ → ℝ) k, rfl,
      fun j ↦ ?_, fun θ ↦ ⟨V θ, hV θ, fun j ↦ ⟨rein_hexMidpoint_mem_frontier hK' (hV θ) j, ?_⟩⟩⟩
    · have c1 := rein_continuous_φ hG hV hVm (j := 1) (Or.inl rfl)
      have c2 := rein_continuous_φ hG hV hVm (j := 2) (Or.inr rfl)
      have m1 := rein_strictMono_φ hG hV hVm (j := 1) (Or.inl rfl)
      have m2 := rein_strictMono_φ hG hV hVm (j := 2) (Or.inr rfl)
      rcases rein_zmod6_cases j with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨continuous_id, strictMono_id, fun θ ↦ rfl⟩
      · exact ⟨c1, m1, fun θ ↦ by
          change rein_φ V K 1 (θ + 2 * π) = rein_φ V K 1 θ + 2 * π
          rw [h2π θ, hp1 θ 1]; push_cast; ring⟩
      · exact ⟨c2, m2, fun θ ↦ by
          change rein_φ V K 2 (θ + 2 * π) = rein_φ V K 2 θ + 2 * π
          rw [h2π θ, hp2 θ 1]; push_cast; ring⟩
      · exact ⟨continuous_id.add continuous_const, strictMono_id.add_const π,
          fun θ ↦ by change θ + 2 * π + π = θ + π + 2 * π; ring⟩
      · exact ⟨c1.add continuous_const, m1.add_const π,
          fun θ ↦ by change rein_φ V K 1 (θ + 2 * π) + π = rein_φ V K 1 θ + π + 2 * π
                     rw [h2π θ, hp1 θ 1]; push_cast; ring⟩
      · exact ⟨c2.add continuous_const, m2.add_const π,
          fun θ ↦ by change rein_φ V K 2 (θ + 2 * π) + π = rein_φ V K 2 θ + π + 2 * π
                     rw [h2π θ, hp2 θ 1]; push_cast; ring⟩
    · have hg := inv_pos.2 (rein_gauge_pos hK' (rein_dir_ne_zero θ))
      obtain ⟨r1, hr1, e1⟩ := rein_φ_spec hG hV (j := 1) θ
      obtain ⟨r2, hr2, e2⟩ := rein_φ_spec hG hV (j := 2) θ
      have n3 := rein_hexMidpoint_add_three (hV θ).1 0
      have n4 := rein_hexMidpoint_add_three (hV θ).1 1
      have n5 := rein_hexMidpoint_add_three (hV θ).1 2
      rw [zero_add] at n3
      rcases rein_zmod6_cases j with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, hg, hVm θ⟩
      · exact ⟨r1, hr1, e1⟩
      · exact ⟨r2, hr2, e2⟩
      · refine ⟨_, hg, ?_⟩
        change hexMidpoint (V θ) 3 = _ • rein_dir (θ + π)
        rw [n3, hVm θ, rein_dir_add_pi, smul_neg]; rfl
      · refine ⟨r1, hr1, ?_⟩
        change hexMidpoint (V θ) (1 + 3) = r1 • rein_dir (rein_φ V K 1 θ + π)
        rw [n4, e1, rein_dir_add_pi, smul_neg]
      · refine ⟨r2, hr2, ?_⟩
        change hexMidpoint (V θ) (2 + 3) = r2 • rein_dir (rein_φ V K 2 θ + π)
        rw [n5, e2, rein_dir_add_pi, smul_neg]

end SmoothedPolygons
