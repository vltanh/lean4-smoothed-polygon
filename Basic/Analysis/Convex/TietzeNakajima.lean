module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Analysis.Normed.Group.Basic

/-!
# The Tietze–Nakajima theorem in the plane

A closed connected subset of the plane which is locally convex is convex. Used by the cell lemma
of Fejes Tóth's packing theorem (`Basic.Analysis.Convex.CellDecomposition.PinwheelHoles`).
-/

@[expose] public section

open Set

namespace PlaneConvex

/-- **The Tietze–Nakajima theorem in the plane.** A closed connected set which is locally convex
(every point `p` of `S` has a ball `B(p, r)` with `S ∩ B(p, r)` convex) is convex.

Argument (Tietze 1928, Nakajima 1928; see F. A. Valentine, *Convex Sets*, Thm 4.4). (1) `S` is
polygonally connected: the set of points of `S` joined to a given point by a polygonal path in
`S` is open and closed in `S` (local convexity), hence all of `S`. (2) *Triangle lemma:* if
`[p₀, p₁] ∪ [p₁, p₂] ⊆ S` then `conv {p₀, p₁, p₂} ⊆ S`. Let `t*` be the supremum of the `t ∈ [0, 1]`
with `conv {p₀, p₁, p₁ + t (p₂ - p₁)} ⊆ S`; the set of such `t` is closed. If `t* < 1`, local
convexity at the point `q* = p₁ + t* (p₂ - p₁)` gives a small triangle beyond `[p₀, q*]` near
`q*`, and local convexity along the compact segment `[p₀, q*]` (a uniform radius by compactness)
propagates it from `q*` to `p₀`, giving `conv {p₀, p₁, p₁ + t (p₂ - p₁)} ⊆ S` for some `t > t*`.
(3) By (2), a polygonal path in `S` from `x` to `y` can be replaced by one with fewer vertices
(drop `p₁` using `[p₀, p₂] ⊆ conv {p₀, p₁, p₂}`), so `[x, y] ⊆ S`.

Estimated size: 300–500 lines. -/
theorem pin_convex_of_isClosed_of_isConnected {S : Set (Fin 2 → ℝ)} (hS : IsClosed S)
    (hconn : IsConnected S) (hloc : ∀ p ∈ S, ∃ r > 0, Convex ℝ (S ∩ Metric.ball p r)) :
    Convex ℝ S := by
  sorry

end PlaneConvex
