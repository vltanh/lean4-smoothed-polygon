module

public import SmoothedPolygons.Ch16.BasinFacts
public import SmoothedPolygons.Ch14.ArcRegionInvariant

/-!
# Chapter 16: Theorem 14.4.1 and Mahler's First conjecture, unconditionally

Theorem 16.3.1 (`thm:mahler`, Mahler's First conjecture) of Hales–Vajjha, *Packings of Smoothed
Polygons* (TeX 12789–12833), and Theorem 14.4.1 (`thm:no-return`, TeX 11995–12013), with no
hypothesis. The book's proof of Theorem 16.3.1 rests on four facts it reads off computations that
it did not certify: the three facts of Table 16.1 behind Theorems 16.1.1 and 16.4.1, and N4, that
the unstable curve over `q_out` reaches the boundary of the star domain (Figure 14.2), behind
Theorem 14.4.1. All four are proved, without computer assistance (departures from the paper, by
the user's decision):

* the three facts of Table 16.1 analytically (`dOutContracts`, `cellTwoEntersDOut`,
  `boxSubclaims`; `SmoothedPolygons/Ch16/BasinFacts.lean`);
* N4 (`unstableCurveLeavesStarDomain`, `SmoothedPolygons/Ch14/ArcRegionInvariant.lean`) by the
  exact structure of the Reinhardt flow along an `e₂`-arc and the invariance of an explicit region
  of section points, the single-step statement (INV) (`arcRegionInvariant`).

**Departure from the paper** (the user's decision; REPORT.md E88): the book computes the unstable
curve numerically (Figure 14.2, TeX 11951–11991); the formalization proves N4 instead (see
`SmoothedPolygons/Ch14/ArcRegionInvariant.lean`).

* `theorem14_4_1_unconditional`: Theorem 14.4.1, `theorem14_4_1` applied to N4.
* `noChatteringIntoSingularLocus`: the named hypothesis of `theorem16_3_1`
  (`SmoothedPolygons/Ch16/MahlerFirst.lean`), from Theorem 14.4.1 and Table 16.1.
* `theorem16_3_1_unconditional`: Mahler's First conjecture,
  `theorem16_3_1_of_unstableCurveLeavesStarDomain` applied to N4.
* `theorem16_3_1_of_arcRegionInvariant`: the form conditional on (INV) alone (Theorem A of the
  N4 proof, `unstableCurveLeavesStarDomain_of_arcRegionInvariant`); (INV) is now proved, so it is
  a corollary.
-/

@[expose] public section

namespace SmoothedPolygons

open TriFuller

/-- **Theorem 14.4.1** (`thm:no-return`, TeX 11995–12013), unconditionally, for locally finitely
bang-bang extremals (the reading of `Theorem14_4_1`, equivalent to the unrestricted statement,
`theorem14_4_1_iff_unrestricted`): a trajectory of the Reinhardt system that emanates from the
fixed point `(0, x_out)` on the exceptional divisor does not return to the exceptional divisor, and
a trajectory that tends to `(0, x_in)` did not emanate at an earlier time from the divisor. The
book's proof (`theorem14_4_1`) with N4 (`unstableCurveLeavesStarDomain`, Figure 14.2), which the
book reads off a computation and the formalization proves (departure from the paper, the user's
decision; REPORT.md E88). -/
theorem theorem14_4_1_unconditional : Theorem14_4_1 :=
  theorem14_4_1 unstableCurveLeavesStarDomain

/-- **No chattering into the singular locus** (`NoChatteringIntoSingularLocus`, the named
hypothesis of `theorem16_3_1`), unconditionally: from Theorem 14.4.1
(`theorem14_4_1_unconditional`) and the three facts of Table 16.1 (`dOutContracts`,
`cellTwoEntersDOut`, `boxSubclaims`), by `noChatteringIntoSingularLocus_of_theorem14_4_1`
(Theorem 16.4.1 and the periodicity argument of the book's proof of Theorem 16.3.1). -/
theorem noChatteringIntoSingularLocus : NoChatteringIntoSingularLocus :=
  noChatteringIntoSingularLocus_of_theorem14_4_1 dOutContracts cellTwoEntersDOut boxSubclaims
    theorem14_4_1_unconditional

/-- **Theorem 16.3.1** (`thm:mahler`, Mahler's First conjecture), **conditional on (INV)**
(`ArcRegionInvariant`): the global minimizer of the Reinhardt optimal control problem is a
bang-bang solution with finitely many switches, and the minimizer `K_min` is a finite-sided
smoothed polygon with rounded hyperbolic arcs at each corner of the sort described by Reinhardt and
Mahler. (INV) is proved (`arcRegionInvariant`), so this is a corollary of
`theorem16_3_1_unconditional`; it records the reduction of N4 to (INV) (Theorem A,
`unstableCurveLeavesStarDomain_of_arcRegionInvariant`). -/
theorem theorem16_3_1_of_arcRegionInvariant (h : ArcRegionInvariant) :
    (∀ (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X : ℝ → Mat2), IsReinhardtMinimizer T u g X →
      IsFiniteBangBang 0 T u) ∧
    ∀ K : Set (Fin 2 → ℝ), IsWorstDisk K → IsSmoothedPolygon K :=
  theorem16_3_1_of_unstableCurveLeavesStarDomain
    (unstableCurveLeavesStarDomain_of_arcRegionInvariant h)

/-- **Theorem 16.3.1** (`thm:mahler`, Mahler's First conjecture), **unconditionally**: the global
minimizer of the Reinhardt optimal control problem is a bang-bang solution with finitely many
switches, and the minimizer `K_min` is a finite-sided smoothed polygon with rounded hyperbolic arcs
at each corner of the sort described by Reinhardt and Mahler (`IsSmoothedPolygon`: no corners, and
the boundary alternates between straight edges and hyperbolic arcs whose asymptotes extend straight
edges).

"The global minimizer" and "the minimizer `K_min`" presuppose uniqueness, which the book does not
prove; the statement is for every global minimizer of Problem 3.6.2 (`IsReinhardtMinimizer`; one
exists, `exists_isReinhardtMinimizer`) and every `K_min` (`IsWorstDisk`; one exists), as in
`theorem16_3_1` (`SmoothedPolygons/Ch16/MahlerFirst.lean`).

The book's proof rests on the uncertified computations of Table 16.1 and of Figure 14.2 (N4); here
the three facts of Table 16.1 are proved analytically (`SmoothedPolygons/Ch16/BasinFacts.lean`) and
N4 is `unstableCurveLeavesStarDomain` (from (INV), `arcRegionInvariant`), both without computer
assistance (departures from the paper, the user's decision; REPORT.md E88). Proof:
`theorem16_3_1_of_unstableCurveLeavesStarDomain` applied to `unstableCurveLeavesStarDomain`. -/
theorem theorem16_3_1_unconditional :
    (∀ (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X : ℝ → Mat2), IsReinhardtMinimizer T u g X →
      IsFiniteBangBang 0 T u) ∧
    ∀ K : Set (Fin 2 → ℝ), IsWorstDisk K → IsSmoothedPolygon K :=
  theorem16_3_1_of_unstableCurveLeavesStarDomain unstableCurveLeavesStarDomain

end SmoothedPolygons
