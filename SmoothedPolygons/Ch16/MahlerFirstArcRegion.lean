module

public import SmoothedPolygons.Ch16.BasinFacts
public import SmoothedPolygons.Ch14.ArcRegionInvariant

/-!
# Chapter 16: Mahler's First conjecture from the single-step statement (INV)

Theorem 16.3.1 (`thm:mahler`, Mahler's First conjecture) of Hales–Vajjha, *Packings of Smoothed
Polygons* (TeX 12789–12833), conditional on the named statement (INV) (`ArcRegionInvariant`,
`SmoothedPolygons/Ch14/ArcRegionInvariant.lean`): one step of the Reinhardt–Poincaré map sends the
explicit region `𝒢*` of section points into itself or onto a point whose `e₂`-arc leaves the star
domain. The three facts of Table 16.1 are proved (`SmoothedPolygons/Ch16/BasinFacts.lean`), and
N4 (`UnstableCurveLeavesStarDomain`, Figure 14.2) follows from (INV) by Theorem 5.2 of the
research notes (`unstableCurveLeavesStarDomain_of_arcRegionInvariant`).

**Departure from the paper.** The book computes the unstable curve numerically (Figure 14.2,
TeX 11951–11991); the formalization proves N4 from (INV) by the exact structure of the arcs.

Proof (one line): `theorem16_3_1_of_unstableCurveLeavesStarDomain` applied to
`unstableCurveLeavesStarDomain_of_arcRegionInvariant h`.
-/

@[expose] public section

namespace SmoothedPolygons

/-- **Theorem 16.3.1** (`thm:mahler`, Mahler's First conjecture), **conditional on (INV)**
(`ArcRegionInvariant`): the global minimizer of the Reinhardt optimal control problem is a
bang-bang solution with finitely many switches, and the minimizer `K_min` is a finite-sided
smoothed polygon with rounded hyperbolic arcs at each corner of the sort described by Reinhardt and
Mahler. -/
theorem theorem16_3_1_of_arcRegionInvariant (h : ArcRegionInvariant) :
    (∀ (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X : ℝ → Mat2), IsReinhardtMinimizer T u g X →
      IsFiniteBangBang 0 T u) ∧
    ∀ K : Set (Fin 2 → ℝ), IsWorstDisk K → IsSmoothedPolygon K :=
  theorem16_3_1_of_unstableCurveLeavesStarDomain
    (unstableCurveLeavesStarDomain_of_arcRegionInvariant h)

end SmoothedPolygons
