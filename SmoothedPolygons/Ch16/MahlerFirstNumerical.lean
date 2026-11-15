module

public import SmoothedPolygons.Ch16.NoChattering
public import SmoothedPolygons.Ch14.NoReturnProof

/-!
# Chapter 16: Mahler's First conjecture from the four named numerical facts

Theorem 16.3.1 (`thm:mahler`, Mahler's First conjecture) of Hales–Vajjha, *Packings of Smoothed
Polygons* (TeX 12789–12833), in its final form in this formalization: conditional only on the four
named numerical facts that the book takes from computations it did not certify:

* the three facts of Table 16.1 behind the global basin theorem (Theorem 16.1.1, Layer 5,
  `SmoothedPolygons/Ch16/BasinHypotheses.lean`): `DOutContracts`, `CellTwoEntersDOut`,
  `BoxSubclaims`;
* N4, the unstable curve `W^u(q_out)` reaches the boundary of the star domain (Figure 14.2, Layer 7,
  `SmoothedPolygons/Ch14/UnstableCurve.lean`): `UnstableCurveLeavesStarDomain`.

Proof (planned, one line): `theorem16_3_1_of_theorem14_4_1 h₁ h₂ h₃ (theorem14_4_1 h₄)`
(`SmoothedPolygons/Ch16/NoChattering.lean`, `SmoothedPolygons/Ch14/NoReturnProof.lean`).
-/

@[expose] public section

namespace SmoothedPolygons

open TriFuller

/-- **Theorem 16.3.1** (`thm:mahler`, Mahler's First conjecture), **conditional on the four named
numerical facts**: the three of Theorem 16.1.1 (`DOutContracts`, `CellTwoEntersDOut`,
`BoxSubclaims`, Table 16.1) and N4 (`UnstableCurveLeavesStarDomain`, Figure 14.2). The global
minimizer of the Reinhardt optimal control problem is a bang-bang solution with finitely many
switches, and the minimizer `K_min` is a finite-sided smoothed polygon with rounded hyperbolic arcs
at each corner of the sort described by Reinhardt and Mahler. -/
theorem theorem16_3_1_of_numerical_facts (h₁ : DOutContracts) (h₂ : CellTwoEntersDOut)
    (h₃ : BoxSubclaims) (h₄ : UnstableCurveLeavesStarDomain) :
    (∀ (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X : ℝ → Mat2), IsReinhardtMinimizer T u g X →
      IsFiniteBangBang 0 T u) ∧
    ∀ K : Set (Fin 2 → ℝ), IsWorstDisk K → IsSmoothedPolygon K := by
  sorry

end SmoothedPolygons
