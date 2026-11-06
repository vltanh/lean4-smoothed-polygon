module

public import Basic.Analysis.Convex.CellDecomposition.Defs

/-!
# (B) The holes of a maximal family are pinwheels

Part of the proof of the cell lemma (`Basic.Analysis.Convex.CellDecomposition`).
-/

@[expose] public section

open MeasureTheory Set

namespace PlaneConvex

/-! ### (B) The holes of a maximal family are pinwheels -/

/-- **(B) Holes of a maximal family are pinwheels** (Böröczky 2003, proof of Lemma 5). Let
`Q = halfPlanesInter b d` be bounded, `K i` compact convex with nonempty interiors, and `C i`
convex polygons with `K i ⊆ C i ⊆ Q`, non-overlapping, of maximal total area
(`IsMaximalCells`). Then the family has pinwheel holes (`HasPinwheelHoles`): every hole `H`
(closure of a connected component of `Q \ ⋃ C i`) is a convex polygon in `interior Q`, each
corner of which is a side point of some cell.

Argument. A hole `H` has nonempty interior (`Q \ ⋃ C i` is relatively open in `Q`, and `Q` is
convex with nonempty interior). Its boundary consists of finitely many segments, each contained
in a side of a cell or in `∂Q`, since the `C i` are polygons. Maximality is used through local
enlargements: if the line `ℓ` carrying a side `e` of a cell `C i` can be rotated about a point
or translated slightly so that the new half-plane, intersected with the other half-planes of
`C i`, gives a convex set `C' i ⊋ C i` whose added part lies in `H` (so it meets no other cell's
interior and stays in `Q`), then replacing `C i` by `C' i` contradicts `IsMaximalCells`
(the added part has nonempty interior, hence positive area). Following Böröczky: call
`s₁, …, s_k` the maximal boundary segments of `H` in cyclic order and `v_j = s_{j-1} ∩ s_j`.
Let `s₁ ⊆ e₁ ⊆ ∂C_{i₁}` meet `interior Q`. If neither endpoint of `s₁` were in the relative
interior of `e₁`, rotating `ℓ(e₁)` slightly about an endpoint of `s₁` would enlarge `C_{i₁}`
into `H`; so one endpoint `v₂` of `s₁` is in the relative interior of `e₁`. Then the next segment
`s₂` lies on a side `e₂` of a cell `C_{i₂}` having `v₂` as an endpoint, and by the same argument
its other endpoint `v₃` is in the relative interior of `e₂`; and so on around `H`. Hence every
`s_j` meets `interior Q` (no `s_j` lies in `∂Q`, so `H ⊆ interior Q`), the turn at each `v_j` is
convex (at a reflex vertex the cell whose side ends there could be enlarged), so `H` is a convex
polygon (`IsConvexPolygon`: the intersection of the half-planes of its sides), and each corner
`v_j` lies in the relative interior of the side `e_{j-1}` of `C_{i_{j-1}}`, i.e. is a side point
of that cell (`IsSidePoint`, with `w` the outer normal of `e_{j-1}` and `ε` less than the
distances from `v_j` to the endpoints of `e_{j-1}` and to the lines of the other sides).

Estimated size: 1500–2000 lines (the boundary structure of the components of the complement of
finitely many polygons, and the perturbation arguments). -/
theorem hasPinwheelHoles_of_isMaximalCells {m n : ℕ} (b : Fin m → Fin 2 → ℝ) (d : Fin m → ℝ)
    (hQ : Bornology.IsBounded (halfPlanesInter b d)) (K : Fin n → Set (Fin 2 → ℝ))
    (hK : ∀ i, Convex ℝ (K i) ∧ IsCompact (K i) ∧ (interior (K i)).Nonempty)
    (C : Fin n → Set (Fin 2 → ℝ)) (hC : ∀ i, IsConvexPolygon (C i)) (hKC : ∀ i, K i ⊆ C i)
    (hCQ : ∀ i, C i ⊆ halfPlanesInter b d) (hdisj : NonOverlapping C)
    (hmax : IsMaximalCells (halfPlanesInter b d) K C) :
    HasPinwheelHoles (halfPlanesInter b d) C := by
  sorry

end PlaneConvex
