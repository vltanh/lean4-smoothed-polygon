module

public import Basic.Analysis.Calculus.MatrixEntrywise
public import Basic.Analysis.Convex.LatticePacking
public import External.MahlerIrreducible
public import External.MahlerIrreducible.Lemma3
public import External.Filippov
public import External.Pontryagin
public import SmoothedPolygons.AppA.FunctionalDerivative
public import SmoothedPolygons.AppA.MatrixIdentities
public import SmoothedPolygons.AppA.Riemannian
public import SmoothedPolygons.Ch2.BalancedCircle
public import SmoothedPolygons.Ch2.BalancedDensity
public import SmoothedPolygons.Ch2.Boundary
public import SmoothedPolygons.Ch2.Density
public import SmoothedPolygons.Ch2.Hexagon
public import SmoothedPolygons.Ch2.Irreducible
public import SmoothedPolygons.Ch2.Mahler
public import SmoothedPolygons.Ch2.MultiCurve
public import SmoothedPolygons.Ch2.Reinhardt
public import SmoothedPolygons.Ch2.TilingCounterexample
public import SmoothedPolygons.Ch3.AreaFormula
public import SmoothedPolygons.Ch3.ControlProblem
public import SmoothedPolygons.Ch3.ControlSets
public import SmoothedPolygons.Ch3.CostFunctional
public import SmoothedPolygons.Ch3.HyperbolicArc
public import SmoothedPolygons.Ch3.Jacobi
public import SmoothedPolygons.Ch3.LieAlgebraDynamics
public import SmoothedPolygons.Ch3.StateDynamics
public import SmoothedPolygons.Ch4.AdjointOrbit
public import SmoothedPolygons.Ch4.IdealVertices
public import SmoothedPolygons.Ch4.StarDomain
public import SmoothedPolygons.Ch4.TerminalTime
public import SmoothedPolygons.Ch5.AreaBound
public import SmoothedPolygons.Ch5.Compactification
public import SmoothedPolygons.Ch5.EdgeBound
public import SmoothedPolygons.Ch5.Hexagon
public import SmoothedPolygons.Ch5.Monotonicity
public import SmoothedPolygons.Ch5.Recenter
public import SmoothedPolygons.Ch5.Theorem502
public import SmoothedPolygons.Ch6.AdmissibleDisk
public import SmoothedPolygons.Ch6.Existence
public import SmoothedPolygons.Ch6.HalfPlane
public import SmoothedPolygons.Ch6.Hamiltonian
public import SmoothedPolygons.Ch6.LeftInvariant
public import SmoothedPolygons.Ch6.MatrixCostate
public import SmoothedPolygons.Ch6.MatrixExtremal
public import SmoothedPolygons.Ch6.MatrixMinimizer
public import SmoothedPolygons.Ch6.MatrixSystem
public import SmoothedPolygons.Ch6.PeriodicExtension
public import SmoothedPolygons.Ch6.Winding
public import SmoothedPolygons.Ch6.WorstDisk
public import SmoothedPolygons.Ch7.ConstantControl
public import SmoothedPolygons.Ch7.DiscreteK
public import SmoothedPolygons.Ch7.Faces
public import SmoothedPolygons.Ch7.HMax
public import SmoothedPolygons.Ch7.HMaxInequality
public import SmoothedPolygons.Ch7.Isolated
public import SmoothedPolygons.Ch7.Isolated.Defs
public import SmoothedPolygons.Ch7.Isolated.FixedPoints
public import SmoothedPolygons.Ch7.Isolated.Hyperbolic
public import SmoothedPolygons.Ch7.Isolated.IpcAlgebra
public import SmoothedPolygons.Ch7.Isolated.IpcFlow
public import SmoothedPolygons.Ch7.Isolated.IpcOctagon
public import SmoothedPolygons.Ch7.Isolated.Poincare
public import SmoothedPolygons.Ch7.Isolated.Return
public import SmoothedPolygons.Ch7.Isolated.Switching
public import SmoothedPolygons.Ch7.Isolated.VertexFlow
public import SmoothedPolygons.Ch7.Polygon
public import SmoothedPolygons.Ch7.Remarks
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

/-- **The smoothed octagon** (the example before Theorem 7.5.6, with the area formula `eqn:cost`
of §3.2). For `k = 1`, `y₀ = √((√8 - 1)/3)` and `t_sw = ln 2/(2√(√8 - 1))`; every trajectory of
the smoothed octagon has cost `√12 (8 - √32 - ln 2)/(√8 - 1) < π`, so cost/√12 is
`(8 - √32 - ln 2)/(√8 - 1)`; and the trajectory defines a balanced disk `K` in circle
representation (`σ_j(t) = g(t) s_j*`, `σ_j(t + t_f) = σ_{j+1}(t)`) whose area is that cost and whose
greatest packing density (Definition 2.1.1) is `(8 - √32 - ln 2)/(√8 - 1)`. -/
theorem smoothed_octagon_density :
    y₀ 1 = √((√8 - 1) / 3) ∧ tsw 1 = Real.log 2 / (2 * √(√8 - 1)) ∧
      (∀ g X : ℝ → Mat2, IsStateTrajectory (tf 1) (polygonControl 1) g X → g 0 = 1 →
        X 0 = Φ 0 (y₀ 1) →
        reinhardtCost (tf 1) X = √12 * (8 - √32 - Real.log 2) / (√8 - 1) ∧
          reinhardtCost (tf 1) X < Real.pi ∧
          reinhardtCost (tf 1) X / √12 = (8 - √32 - Real.log 2) / (√8 - 1)) ∧
    ∃ (g X : ℝ → Mat2) (K : Set (Fin 2 → ℝ)) (σ : ZMod 6 → ℝ → Fin 2 → ℝ),
      IsStateTrajectory (tf 1) (polygonControl 1) g X ∧ g 0 = 1 ∧ X 0 = Φ 0 (y₀ 1) ∧
      (∀ j t, σ j t = Matrix.mulVec (g t) (sixthRoot j)) ∧ (∀ j t, σ j (t + tf 1) = σ (j + 1) t) ∧
      IsBalancedPair K σ (tf 1) ∧ IsCircleRepresentation σ ∧
      MeasureTheory.volume K = ENNReal.ofReal (√12 * (8 - √32 - Real.log 2) / (√8 - 1)) ∧
      greatestPackingDensity K = (8 - √32 - Real.log 2) / (√8 - 1) := by
  obtain ⟨-, -, h1, h2, h3⟩ := example7_5_smoothedOctagon
  obtain ⟨-, -, g, X, K, σ, hst, hg0, hX0, hσ, hshift, hbal, hcirc, hvol, -, hdens⟩ :=
    smoothedOctagon_isBalancedPair_area
  refine ⟨h1, h2, fun g X h hg0 hX0 ↦ (h3 g X h hg0 hX0).2,
    g, X, K, σ, hst, hg0, hX0, hσ, hshift, hbal, hcirc, hvol, ?_⟩
  rw [greatestPackingDensity_of_isBalancedPair hbal, MeasureTheory.measureReal_def, hdens]

end SmoothedPolygonsChallenge

end
