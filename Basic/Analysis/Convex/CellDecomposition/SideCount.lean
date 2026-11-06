module

public import Basic.Analysis.Convex.CellDecomposition.Defs

/-!
# (C2) The side count

Part of the proof of the cell lemma (`Basic.Analysis.Convex.CellDecomposition`).
-/

@[expose] public section

open MeasureTheory Set

namespace PlaneConvex

/-! ### (C2) The side count -/

/-- **(C2) The side count.** Let `Q = halfPlanesInter b d` (`m` half-planes) be bounded and
`C 0, …, C (n-1)`, `n ≥ 1`, non-overlapping convex polygons in `Q` with pinwheel holes
(`HasPinwheelHoles`). Then the numbers `N i` of corners (extreme points) of the cells satisfy
`∑ N i ≤ 6n + m - 6`, i.e. `∑ N i + 6 ≤ 6n + m`.

Argument (an angle count; no Euler formula or Jordan curve theorem). For a closed convex set `S`
and a point `p` let `θ_p(S) ∈ [0, 2π]` be the angle of `S` at `p`:
`|S ∩ B(p, ε)| = θ_p(S) ε²/2` for all small `ε` (`B` the Euclidean disk), so `θ_p = 0` off `S`,
`π` at a side point, `2π` at an interior point, and `θ_p(P) = π - (gap between the outer normals
of the two sides at p) ∈ (0, π)` at a corner of a polygon `P`.
(1) *Angle sum.* For a convex polygon `P` with `N` corners, `∑_{corners} θ_v(P) = (N - 2)π`: the
exterior angles `π - θ_v` are the gaps between consecutive outer normals in angular order, which
sum to `2π`.
(2) *Local count.* Write `A_p = ∑ θ_p(C i)` over the cells having a corner at `p`, and `c_p` for
their number. The cells and the holes cover `Q` and do not overlap, so at every point `p`,
`∑_i θ_p(C i) + ∑_H θ_p(H) = θ_p(Q)` (compare areas in `B(p, ε)`; boundaries are null sets).
Each corner angle is `< π`; side points contribute `π`. Two distinct holes cannot share a
boundary segment (they would be one connected component), and the boundary of a hole is covered
by cell sides. Hence:
* at `p ∈ interior Q` not a corner of a hole: if `p` is in the interior of a cell or hole,
  `A_p = 0`; if `p` is a side point of a hole, the other half-disk is a cell side (`A_p = 0`) or
  is filled by `c_p ≥ 2` corners (`A_p = π`); otherwise cells fill `2π` with `t ≤ 2` side points
  and corners, giving `A_p = 0`, or `A_p = π` with `c_p ≥ 2`, or `A_p = 2π` with `c_p ≥ 3`.
  In all cases `A_p ≤ (2/3)π c_p`;
* on a side of `Q` (the cells cover `∂Q` since the holes lie in `interior Q`):
  `A_p ∈ {0, π}`, with `c_p ≥ 2` if `A_p = π`; so again `A_p ≤ (2/3)π c_p`;
* at a corner of `Q` with angle `γ_p`: `A_p = γ_p` and `c_p ≥ 1`;
* at a point `v` which is a corner of `r_v ≥ 1` holes: by `HasPinwheelHoles` exactly one cell
  has `v` as a side point (two would leave no room), so
  `A_v = π - ∑_{H ∋ v} θ_v(H) > 0`, `c_v ≥ 1`, and `c_v ≥ r_v - 1` (consecutive holes around `v`
  are separated by cell corners). Summing over all hole corners, with `∑_{v ∈ H} θ_v(H) =
  (k_H - 2)π` for a hole with `k_H ≥ 3` corners and `h ≤ (∑_v r_v)/3` holes:
  `∑_v A_v = ∑_v π - ∑_H (k_H - 2)π ≤ π ∑_v (1 - r_v/3) ≤ (2/3)π ∑_v max(1, r_v - 1)
  ≤ (2/3)π ∑_v c_v` (pointwise `1 - r/3 ≤ (2/3) max(1, r - 1)`).
(3) *Summation.* With (1), `∑_i (N i - 2)π = ∑_p A_p`; by (2), splitting off the `m' ≤ m`
corners of `Q` (where `∑ γ_p = (m' - 2)π` and `c_p ≥ 1`),
`∑_p A_p ≤ (2/3)π (∑_i N i - m') + (m' - 2)π`, i.e. `∑ N i ≤ 6n + m' - 6 ≤ 6n + m - 6`.

A further split for parallel work: (1) as a lemma on convex polygons; the local identity in (2)
as a lemma on finite non-overlapping families of convex polygons covering a neighbourhood; and
the bookkeeping (2)–(3).

Estimated size: 1500–2000 lines. -/
theorem sum_ncard_extremePoints_add_six_le {m n : ℕ} (hn : 1 ≤ n) (b : Fin m → Fin 2 → ℝ)
    (d : Fin m → ℝ) (hQ : Bornology.IsBounded (halfPlanesInter b d))
    (C : Fin n → Set (Fin 2 → ℝ)) (hC : ∀ i, IsConvexPolygon (C i))
    (hCQ : ∀ i, C i ⊆ halfPlanesInter b d) (hdisj : NonOverlapping C)
    (hpin : HasPinwheelHoles (halfPlanesInter b d) C) :
    ∑ i, (extremePoints ℝ (C i)).ncard + 6 ≤ 6 * n + m := by
  sorry

end PlaneConvex
