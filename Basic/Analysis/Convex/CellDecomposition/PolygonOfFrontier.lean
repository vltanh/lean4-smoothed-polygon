module

public import Basic.Analysis.Convex.CellDecomposition.Defs

/-!
# Recognizing a convex polygon

A compact convex set with nonempty interior whose frontier lies on finitely many lines is a convex
polygon. Used by part (B) of the cell lemma
(`Basic.Analysis.Convex.CellDecomposition.PinwheelHoles`).
-/

@[expose] public section

open MeasureTheory Set

namespace PlaneConvex

/-- **Recognizing a convex polygon.** A compact convex set with nonempty interior whose frontier
lies in finitely many lines `⟨a l, x⟩ = c l` (`a l ≠ 0`) is a convex polygon.

Argument. For each `l` such that `L_l = {⟨a l, x⟩ = c l}` meets `frontier S` in a segment of
positive length, `L_l` is a supporting line of `S` (a line containing a nondegenerate piece of the
boundary of a convex body with nonempty interior supports it); let `P_l ⊇ S` be the corresponding
closed half-plane. Then `S = ⋂ P_l`: if `x ∈ ⋂ P_l \ S`, take `y ∈ interior S`; the segment
`[y, x]` leaves `S` at a frontier point `z`; near `z` the frontier is a finite union of pieces of
the `L_l` through `z`, at least one of which has positive length on each side of `z` (the
frontier of a planar convex body is a closed curve without isolated pieces), and the half-planes
`P_l` of the lines carrying them cut off `x`, a contradiction. Boundedness and nonempty interior
are inherited from `S`.

Estimated size: 200–400 lines. -/
theorem pin_isConvexPolygon_of_frontier_subset {S : Set (Fin 2 → ℝ)} (hconv : Convex ℝ S)
    (hcpt : IsCompact S) (hint : (interior S).Nonempty) {ι : Type*} [Finite ι]
    (a : ι → Fin 2 → ℝ) (c : ι → ℝ) (ha : ∀ l, a l ≠ 0)
    (hfr : frontier S ⊆ ⋃ l, {x | a l ⬝ᵥ x = c l}) :
    IsConvexPolygon S := by
  sorry

end PlaneConvex
