module

public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Topology.Connected.Basic
public import Basic.Analysis.Convex.CircumscribedPolygon

/-!
# Cell decompositions of finite packings: shared definitions

Convex polygons, non-overlapping families, maximal families of cells, side points, holes and
pinwheel holes, used by the cell lemma (`Basic.Analysis.Convex.CellDecomposition`).
-/

@[expose] public section

open MeasureTheory Set

namespace PlaneConvex

/-! ### Shared definitions -/

/-- A convex polygon: a bounded intersection of finitely many closed half-planes, with nonempty
interior. -/
def IsConvexPolygon (P : Set (Fin 2 → ℝ)) : Prop :=
  (∃ (k : ℕ) (a : Fin k → Fin 2 → ℝ) (c : Fin k → ℝ), P = halfPlanesInter a c) ∧
    Bornology.IsBounded P ∧ (interior P).Nonempty

/-- A family of sets is non-overlapping: the interiors are pairwise disjoint. -/
def NonOverlapping {ι : Type*} (C : ι → Set (Fin 2 → ℝ)) : Prop :=
  Pairwise fun i j ↦ Disjoint (interior (C i)) (interior (C j))

/-- The cells `C i` (with `K i ⊆ C i ⊆ Q`) have maximal total area among all non-overlapping
families of convex sets `C' i` with `K i ⊆ C' i ⊆ Q`. -/
def IsMaximalCells {n : ℕ} (Q : Set (Fin 2 → ℝ)) (K C : Fin n → Set (Fin 2 → ℝ)) : Prop :=
  ∀ C' : Fin n → Set (Fin 2 → ℝ), (∀ i, Convex ℝ (C' i)) → (∀ i, K i ⊆ C' i) →
    (∀ i, C' i ⊆ Q) → NonOverlapping C' → ∑ i, volume (C' i) ≤ ∑ i, volume (C i)

/-- `v` is a *side point* of `C`: near `v`, `C` coincides with a closed half-plane whose boundary
line passes through `v` (so `v` lies in the relative interior of a side of the polygon `C`). -/
def IsSidePoint (C : Set (Fin 2 → ℝ)) (v : Fin 2 → ℝ) : Prop :=
  ∃ w : Fin 2 → ℝ, w ≠ 0 ∧ ∃ ε > 0, ∀ x, dist x v < ε → (x ∈ C ↔ w ⬝ᵥ (x - v) ≤ 0)

/-- The holes of a family of cells in `Q`: the closures of the connected components of
`Q \ ⋃ i, C i`. -/
def holes {n : ℕ} (Q : Set (Fin 2 → ℝ)) (C : Fin n → Set (Fin 2 → ℝ)) :
    Set (Set (Fin 2 → ℝ)) :=
  {H | ∃ x ∈ Q \ ⋃ i, C i, H = closure (connectedComponentIn (Q \ ⋃ i, C i) x)}

/-- The cells have *pinwheel holes* (Böröczky): every hole is a convex polygon contained in the
interior of `Q` (so the cells cover the boundary of `Q`), and every corner (extreme point) of a
hole is a side point of some cell. -/
def HasPinwheelHoles {n : ℕ} (Q : Set (Fin 2 → ℝ)) (C : Fin n → Set (Fin 2 → ℝ)) : Prop :=
  ∀ H ∈ holes Q C, IsConvexPolygon H ∧ H ⊆ interior Q ∧
    ∀ v ∈ extremePoints ℝ H, ∃ i, IsSidePoint (C i) v

end PlaneConvex
