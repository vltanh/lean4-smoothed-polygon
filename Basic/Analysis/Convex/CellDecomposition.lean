module

public import Basic.Analysis.Convex.CellDecomposition.Defs
public import Basic.Analysis.Convex.CellDecomposition.MaximalCells
public import Basic.Analysis.Convex.CellDecomposition.PinwheelHoles
public import Basic.Analysis.Convex.CellDecomposition.PolygonSides
public import Basic.Analysis.Convex.CellDecomposition.SideCount

/-!
# Fejes Tóth's cell lemma

Let `Q` be a bounded convex polygon cut out by `m` closed half-planes and `K₀, …, K_{n-1}`,
`n ≥ 1`, pairwise non-overlapping convex disks in `Q`. Then the `K i` lie in pairwise
non-overlapping convex polygons `C i ⊆ Q` with `s i` sides such that `∑ s i ≤ 6n + m - 6`
(`PlaneConvex.exists_cell_decomposition`). This is the planar-topology core of L. Fejes Tóth's
packing inequality (*Some packing and covering theorems*, Acta Sci. Math. Szeged 12A (1950));
we follow K. Böröczky Jr., *Finite packing and covering by congruent convex domains*, Discrete
Comput. Geom. 30 (2003), 185–193, Lemma 5, with an angle count in place of Euler's formula.

The proof is assembled here from four independent lemmas, each left as `sorry` with its argument
in its docstring:

* (A) `PlaneConvex.exists_isMaximalCells`: there are cells `K i ⊆ C i ⊆ Q`, convex polygons,
  non-overlapping, of maximal total area among all non-overlapping families of convex sets
  `K i ⊆ C' i ⊆ Q` (compactness).
* (B) `PlaneConvex.hasPinwheelHoles_of_isMaximalCells`: for such a maximal family, every hole
  (closure of a connected component of `Q \ ⋃ C i`) is a convex polygon in the interior of `Q`
  each of whose corners is a *side point* of some cell (Böröczky's "pinwheel" holes).
* (C1) `PlaneConvex.IsConvexPolygon.exists_halfPlanesInter_ncard`: a convex polygon with `N`
  corners (extreme points) is the intersection of `N ≥ 3` closed half-planes.
* (C2) `PlaneConvex.sum_ncard_extremePoints_add_six_le`: the side count
  `∑ #corners (C i) + 6 ≤ 6n + m` for non-overlapping convex polygons in `Q` with pinwheel holes
  (the angle-sum argument).

Shared vocabulary: `PlaneConvex.IsConvexPolygon`, `PlaneConvex.NonOverlapping`,
`PlaneConvex.IsMaximalCells`, `PlaneConvex.IsSidePoint`, `PlaneConvex.holes`,
`PlaneConvex.HasPinwheelHoles`; `PlaneConvex.halfPlanesInter a c = {x | ∀ i, ⟨a i, x⟩ ≤ c i}` is
from `Basic/Analysis/Convex/CircumscribedPolygon.lean`. Points of the plane are `Fin 2 → ℝ` with
the sup metric (`dist`), `⟨u, x⟩ = u ⬝ᵥ x`, and `volume` is Lebesgue measure.
-/

@[expose] public section

open MeasureTheory Set

namespace PlaneConvex
/-! ### The cell lemma -/

/-- **Fejes Tóth's cell lemma** (L. Fejes Tóth 1950; Böröczky 2003, Lemma 5). Let
`Q = halfPlanesInter b d` (`m` half-planes) be bounded and `K 0, …, K (n-1)`, `n ≥ 1`, pairwise
non-overlapping compact convex sets with nonempty interiors in `Q`. Then there are convex
polygons `C i = halfPlanesInter (a i) (c i)` cut out by `s i ≥ 3` half-planes, with
`K i ⊆ C i ⊆ Q`, pairwise non-overlapping, such that `∑ s i ≤ 6n + m - 6`.

Proof: a maximal family of cells (A) has pinwheel holes (B); write each cell with as many
half-planes as it has corners (C1) and count the corners (C2). -/
theorem exists_cell_decomposition {m n : ℕ} (hn : 1 ≤ n) (b : Fin m → Fin 2 → ℝ)
    (d : Fin m → ℝ) (hQ : Bornology.IsBounded (halfPlanesInter b d))
    (K : Fin n → Set (Fin 2 → ℝ))
    (hK : ∀ i, Convex ℝ (K i) ∧ IsCompact (K i) ∧ (interior (K i)).Nonempty)
    (hKQ : ∀ i, K i ⊆ halfPlanesInter b d) (hdisj : NonOverlapping K) :
    ∃ (s : Fin n → ℕ) (a : ∀ i, Fin (s i) → Fin 2 → ℝ) (c : ∀ i, Fin (s i) → ℝ),
      (∀ i, 3 ≤ s i) ∧ (∀ i, K i ⊆ halfPlanesInter (a i) (c i)) ∧
      (∀ i, halfPlanesInter (a i) (c i) ⊆ halfPlanesInter b d) ∧
      NonOverlapping (fun i ↦ halfPlanesInter (a i) (c i)) ∧ ∑ i, s i + 6 ≤ 6 * n + m := by
  obtain ⟨C, hCpoly, hKC, hCQ, hCdisj, hmax⟩ := exists_isMaximalCells b d hQ K hK hKQ hdisj
  have hpin := hasPinwheelHoles_of_isMaximalCells b d hQ K hK C hCpoly hKC hCQ hCdisj hmax
  choose a c hac using fun i ↦ (hCpoly i).exists_halfPlanesInter_ncard
  have hC : (fun i ↦ halfPlanesInter (a i) (c i)) = C := funext fun i ↦ (hac i).1.symm
  refine ⟨fun i ↦ (extremePoints ℝ (C i)).ncard, a, c, fun i ↦ (hac i).2, fun i ↦ ?_,
    fun i ↦ ?_, ?_, sum_ncard_extremePoints_add_six_le hn b d hQ C hCpoly hCQ hCdisj hpin⟩
  · rw [← (hac i).1]
    exact hKC i
  · rw [← (hac i).1]
    exact hCQ i
  · rw [hC]
    exact hCdisj

end PlaneConvex
