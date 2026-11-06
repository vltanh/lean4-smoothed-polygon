module

public import SmoothedPolygons.Ch2.Density
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.LinearAlgebra.AffineSpace.Midpoint

/-!
# Reinhardt's approach (§2.2)

Lattice packings of a centrally symmetric convex disk by tiles (Lemma 2.2.1), the formula
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

/-! ### Lemma 2.2.1 and Theorem 2.2.2 -/

/-- **Lemma 2.2.1** (`lem:reinhardt-tiling`). Let `K` be a centrally symmetric convex disk and
`K + L` a lattice packing of `K`. The packing `K + L` is realized by placing `K` inside an
appropriate parallelogram or centrally symmetric convex hexagon `H_K`, tiling the plane with
translates of `H_K` by `L`, then placing a copy of `K` inside each translate of `H_K`. -/
theorem lemma2_2_1 {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {L : Submodule ℤ (Fin 2 → ℝ)}
    (hL : IsPlaneLattice L) (hKL : IsLatticePacking K L) :
    ∃ H, (IsCSParallelogram H ∨ ∃ v, IsCSHexagon v ∧ H = hexagonOf v) ∧ K ⊆ H ∧
      IsLatticeTiling H L := by
  sorry

/-- **Theorem 2.2.2** (Reinhardt–Fejes Tóth; `thm:frac-hexagon`, equation
`eqn:reinhardt-fejes-toth`). If `K ⊂ ℝ²` is a centrally symmetric convex disk that is not a
parallelogram, then its packing density is `δ(K) = area(K)/area(H_K)`, where `H_K` is a centrally
symmetric hexagon of least area circumscribing `K`. The statement includes that such a hexagon
exists. -/
theorem theorem2_2_2 {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) (hpar : ¬ IsParallelogram K) :
    (∃ v, IsLeastAreaHexagon K v) ∧
      ∀ v, IsLeastAreaHexagon K v →
        greatestPackingDensity K = volume.real K / volume.real (hexagonOf v) := by
  sorry

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

/-- **Remark 2.2.4** (`rem:arc-hyperbola`). Let `K` be a centrally symmetric convex disk and `H_K`
a centrally symmetric hexagon of least area circumscribing it (there is none when `K` is a
parallelogram). Locally around each edge midpoint of `H_K`, `K` contains an arc of the hyperbola
through that midpoint whose asymptotes are the lines through the two adjacent edges (the envelope
of the edges obtained by sliding the edge with the area fixed). -/
theorem remark2_2_4 {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {v : ZMod 6 → Fin 2 → ℝ}
    (hv : IsLeastAreaHexagon K v) (j : ZMod 6) :
    ∃ ε > 0, ∀ p, dist p (hexMidpoint v j) < ε →
      hexHyperbolaFun v j p = hexHyperbolaFun v j (hexMidpoint v j) → p ∈ K := by
  sorry

/-! ### Reinhardt's lemmas on the worst disk -/

/-- **Lemma 2.2.5** (`lem:no-corner`). A disk `K_min` with the worst greatest density lattice
packing exists. `K_min` has no corners, that is, there is a unique support line to `K_min` at each
boundary point. Moreover, the support line of each boundary point of `K_min` contains an edge of
some critical hexagon. -/
theorem lemma2_2_5 :
    (∃ K, IsWorstLatticeDisk K) ∧
      ∀ K, IsWorstLatticeDisk K →
        (∀ u ∈ frontier K, ∃! ℓ, IsSupportLine K ℓ ∧ u ∈ ℓ) ∧
        ∀ u ∈ frontier K, ∀ ℓ, IsSupportLine K ℓ → u ∈ ℓ →
          ∃ v, IsLeastAreaHexagon K v ∧ ∃ j, segment ℝ (v j) (v (j + 1)) ⊆ ℓ := by
  sorry

/-- The triangle `T_j` with vertices `s_j*`, `s_{j+1}*` and `s_j* + s_{j+1}*` (§2.2). -/
noncomputable def sixthTriangle (j : ZMod 6) : Set (Fin 2 → ℝ) :=
  convexHull ℝ {sixthRoot j, sixthRoot (j + 1), sixthRoot j + sixthRoot (j + 1)}

/-- **Lemma 2.2.6** (`lem:tri-interior`; Reinhardt's *monotonicity*). Assume that `K_min` has a
critical hexagon with edge midpoints `s_j*`. Consider a second critical hexagon of `K_min` with
edge midpoints `s₀, …, s₅`, indexed so that `s₀ ∈ T₀ \ {s₀*, s₁*}`. Then for all `j`, `s_j` lies
in the interior of `T_j`. -/
theorem lemma2_2_6 {K : Set (Fin 2 → ℝ)} (hK : IsWorstLatticeDisk K)
    (hstar : ∃ w, IsLeastAreaHexagon K w ∧ ∀ j, hexMidpoint w j = sixthRoot j)
    {v : ZMod 6 → Fin 2 → ℝ} (hv : IsLeastAreaHexagon K v)
    (h0 : hexMidpoint v 0 ∈ sixthTriangle 0 \ {sixthRoot 0, sixthRoot 1}) :
    ∀ j, hexMidpoint v j ∈ interior (sixthTriangle j) := by
  sorry

/-- **Lemma 2.2.7** (`lem:multi-cont`). Let `K = K_min` have worst greatest packing density.
Then every point of the boundary of `K` is the midpoint of an edge of a unique critical hexagon.
As `s₀` advances around the boundary of `K` in a counterclockwise direction, the five other
midpoints `s₁, …, s₅` advance strictly monotonically and continuously in a counterclockwise
direction.

The second part is stated with polar angles: when `s₀` is the boundary point at angle `θ`, the
midpoint `s_j` of the critical hexagon is the boundary point at angle `φ_j(θ)`, where `φ₀ = id`
and each `φ_j` is a continuous strictly increasing lift of a circle map
(`φ_j(θ + 2π) = φ_j(θ) + 2π`). -/
theorem lemma2_2_7 {K : Set (Fin 2 → ℝ)} (hK : IsWorstDisk K) :
    (∀ u ∈ frontier K, ∃! H, ∃ v, IsLeastAreaHexagon K v ∧ hexagonOf v = H ∧
      ∃ j, hexMidpoint v j = u) ∧
    ∃ φ : ZMod 6 → ℝ → ℝ, φ 0 = id ∧
      (∀ j, Continuous (φ j) ∧ StrictMono (φ j) ∧ ∀ θ, φ j (θ + 2 * π) = φ j θ + 2 * π) ∧
      ∀ θ, ∃ v, IsLeastAreaHexagon K v ∧ ∀ j, hexMidpoint v j ∈ frontier K ∧
        ∃ r > 0, hexMidpoint v j = r • ![cos (φ j θ), sin (φ j θ)] := by
  sorry

end SmoothedPolygons
