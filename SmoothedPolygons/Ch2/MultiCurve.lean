module

public import SmoothedPolygons.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Data.ZMod.Defs
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Data.Matrix.Mul

/-!
# Multi-points, multi-curves and balanced disks (§2.3, §2.4)

The definitions of Chapter 2 that Chapter 3 builds on: multi-points and multi-curves
(Definition 2.4.1), the sixth roots of unity `s_j*`, centrally symmetric convex disks, and balanced
disks (Definition 2.4.7). Points of the plane are `Fin 2 → ℝ`; the indices `j ∈ ℤ/6ℤ` are
`ZMod 6`.
-/

@[expose] public section

namespace SmoothedPolygons

open MeasureTheory

/-- A `C^k` multi-curve on `[0, t_f]` (Definition 2.4.1): six `C^k` curves `σ_j` such that
`j ↦ σ_j(t)` is a multi-point for every `t ∈ [0, t_f]`. -/
def IsMultiCurve (k : ℕ) (σ : ZMod 6 → ℝ → Fin 2 → ℝ) (tf : ℝ) : Prop :=
  (∀ j, ContDiffOn ℝ k (σ j) (Set.Icc 0 tf)) ∧ ∀ t ∈ Set.Icc 0 tf, IsMultiPoint fun j ↦ σ j t

/-- A convex disk (§1.1, §2.1): a compact convex set with nonempty interior. -/
def IsConvexDisk (K : Set (Fin 2 → ℝ)) : Prop :=
  Convex ℝ K ∧ IsCompact K ∧ (interior K).Nonempty

end SmoothedPolygons
