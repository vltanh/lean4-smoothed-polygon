module

public import Basic.Analysis.Convex.CellDecomposition.Defs

/-!
# (C1) Sides of a convex polygon

Part of the proof of the cell lemma (`Basic.Analysis.Convex.CellDecomposition`).
-/

@[expose] public section

open MeasureTheory Set

namespace PlaneConvex

/-! ### (C1) Sides of a convex polygon -/

/-- **(C1) A convex polygon with `N` corners is cut out by `N ≥ 3` half-planes.** If `P` is a
convex polygon (`IsConvexPolygon`), its set of extreme points is finite with `N ≥ 3` elements,
and `P = halfPlanesInter a c` for some `a : Fin N → Fin 2 → ℝ`, `c : Fin N → ℝ`.

Argument. Write `P = halfPlanesInter a₀ c₀` with `k` half-planes. Discard the redundant ones and
merge parallel ones with the same normal direction (keep the smaller offset); call the remaining
normals, sorted by angle, `u₁, …, u_N'`. Each remaining half-plane meets `P` in a side (a segment
of positive length, else it would be redundant), consecutive sides meet in a corner, and the
corners are exactly the extreme points of `P` (`Set.extremePoints`): a point of `P` on a single
side, or in the interior, is the midpoint of two other points of `P`; the common endpoint of two
consecutive sides with non-parallel normals is not. So `N = N'`; `N ≥ 3` because `P` is bounded
with nonempty interior (two half-planes cut out an unbounded set or one with empty interior).
Alternatively: `P` is compact, so it is the convex hull of its extreme points (Krein–Milman);
these are finitely many (each is the intersection point of two of the `k` lines), and the `N`
edges of `conv{p₁, …, p_N}`, with the points in angular order about an interior point, give the
`N` half-planes.

Estimated size: 300–500 lines. -/
theorem IsConvexPolygon.exists_halfPlanesInter_ncard {P : Set (Fin 2 → ℝ)}
    (hP : IsConvexPolygon P) :
    ∃ (a : Fin (extremePoints ℝ P).ncard → Fin 2 → ℝ) (c : Fin (extremePoints ℝ P).ncard → ℝ),
      P = halfPlanesInter a c ∧ 3 ≤ (extremePoints ℝ P).ncard := by
  sorry

end PlaneConvex
