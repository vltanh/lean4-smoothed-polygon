module

public import Basic.Analysis.Calculus.MatrixEntrywise
public import SmoothedPolygons.AppA.FunctionalDerivative
public import SmoothedPolygons.AppA.MatrixIdentities
public import SmoothedPolygons.AppA.Riemannian
public import SmoothedPolygons.Ch2.BalancedCircle
public import SmoothedPolygons.Ch2.MultiCurve
public import SmoothedPolygons.Ch3.AreaFormula
public import SmoothedPolygons.Ch3.ControlProblem
public import SmoothedPolygons.Ch3.ControlSets
public import SmoothedPolygons.Ch3.CostFunctional
public import SmoothedPolygons.Ch3.Jacobi
public import SmoothedPolygons.Ch3.LieAlgebraDynamics
public import SmoothedPolygons.Ch3.StateDynamics
public import SmoothedPolygons.Ch4.AdjointOrbit
public import SmoothedPolygons.Ch4.StarDomain
public import SmoothedPolygons.Ch4.TerminalTime
public import SmoothedPolygons.Ch6.HalfPlane
public import SmoothedPolygons.Ch6.Hamiltonian
public import SmoothedPolygons.Ch7.ConstantControl
public import SmoothedPolygons.Ch7.DiscreteK
public import SmoothedPolygons.Ch7.Faces
public import SmoothedPolygons.Ch7.HMax
public import SmoothedPolygons.Ch7.HMaxInequality
public import SmoothedPolygons.Ch7.Polygon
public import SmoothedPolygons.Ch7.SmoothedPolygon
public import SmoothedPolygons.Ch7.SmoothedPolygonDisk
public import SmoothedPolygons.Ch7.StrongTransversality
public import SmoothedPolygons.Defs

/-!
# Solution

Entry point of the library: it imports every module, and restates the two theorems of
`Challenge.lean` word for word, with their proofs from the library (`theorem7_5_6`,
`example7_5_smoothedOctagon`). Palomar's Comparator checks that these are the Challenge's
statements and that their proofs use only the standard axioms (`comparator.json`).
-/

@[expose] public section

namespace SmoothedPolygonsChallenge

open SmoothedPolygons

/-- **Theorem 7.5.6** (Hales–Vajjha). For each positive integer `k`, the smoothed `(6k+2)`-gon is a
Pontryagin extremal of the Reinhardt control problem given by a bang-bang control. -/
theorem smoothed_polygon_extremal (k : ℕ) (hk : 1 ≤ k) :
    (∃ g X : ℝ → Mat2, IsStateTrajectory (tf k) (polygonControl k) g X ∧ g 0 = 1 ∧
      X 0 = Φ 0 (y₀ k)) ∧
    ∀ g X : ℝ → Mat2, IsStateTrajectory (tf k) (polygonControl k) g X → g 0 = 1 →
      X 0 = Φ 0 (y₀ k) →
      IsBangBang (tf k) (polygonControl k) ∧
        ∃ (Λ₁ ΛR : ℝ → Mat2) (lam : ℝ),
          IsPontryaginExtremal (tf k) (polygonControl k) g X Λ₁ ΛR lam := by
  exact theorem7_5_6 k hk

/-- **The smoothed octagon** (the example before Theorem 7.5.6). For `k = 1`,
`y₀ = √((√8 - 1)/3)` and `t_sw = ln 2/(2√(√8 - 1))`, and the trajectory of the smoothed octagon has
cost (area) `√12 (8 - √32 - ln 2)/(√8 - 1) < π`, hence density
`(8 - √32 - ln 2)/(√8 - 1)`. -/
theorem smoothed_octagon_density :
    y₀ 1 = √((√8 - 1) / 3) ∧ tsw 1 = Real.log 2 / (2 * √(√8 - 1)) ∧
      ∀ g X : ℝ → Mat2, IsStateTrajectory (tf 1) (polygonControl 1) g X → g 0 = 1 →
        X 0 = Φ 0 (y₀ 1) →
        reinhardtCost (tf 1) X = √12 * (8 - √32 - Real.log 2) / (√8 - 1) ∧
          reinhardtCost (tf 1) X < Real.pi ∧
          reinhardtCost (tf 1) X / √12 = (8 - √32 - Real.log 2) / (√8 - 1) := by
  obtain ⟨-, -, h1, h2, h3⟩ := example7_5_smoothedOctagon
  exact ⟨h1, h2, fun g X h hg0 hX0 ↦ (h3 g X h hg0 hX0).2⟩

end SmoothedPolygonsChallenge

end
