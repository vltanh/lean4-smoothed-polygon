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

/-- The determinant `det(v, w) = v₁w₂ - v₂w₁` of the `2 × 2` matrix with columns `v, w`. -/
def det2 (v w : Fin 2 → ℝ) : ℝ := v 0 * w 1 - v 1 * w 0

/-- A multi-point (Definition 2.4.1): `s : ℤ/6ℤ → ℝ²` with `s₀ + s₂ + s₄ = 0`,
`s_{j+3} = -s_j` and `det(s_j, s_{j+1}) = √3/2` for all `j` (equations `eqn:multi`,
`eqn:sqrt12`); the first condition is imposed for every shift `j`, as in equation
`eqn:multi-point-properties`. -/
def IsMultiPoint (s : ZMod 6 → Fin 2 → ℝ) : Prop :=
  ∀ j : ZMod 6, s j + s (j + 2) + s (j + 4) = 0 ∧ s (j + 3) = -s j ∧
    det2 (s j) (s (j + 1)) = √3 / 2

/-- The sixth roots of unity `s_j* = exp(2πij/6)`, as points of `ℝ²`. -/
noncomputable def sixthRoot (j : ZMod 6) : Fin 2 → ℝ :=
  ![Real.cos (Real.pi * j.val / 3), Real.sin (Real.pi * j.val / 3)]

/-- A `C^k` multi-curve on `[0, t_f]` (Definition 2.4.1): six `C^k` curves `σ_j` such that
`j ↦ σ_j(t)` is a multi-point for every `t ∈ [0, t_f]`. -/
def IsMultiCurve (k : ℕ) (σ : ZMod 6 → ℝ → Fin 2 → ℝ) (tf : ℝ) : Prop :=
  (∀ j, ContDiffOn ℝ k (σ j) (Set.Icc 0 tf)) ∧ ∀ t ∈ Set.Icc 0 tf, IsMultiPoint fun j ↦ σ j t

/-- A convex disk (§1.1, §2.1): a compact convex set with nonempty interior. -/
def IsConvexDisk (K : Set (Fin 2 → ℝ)) : Prop :=
  Convex ℝ K ∧ IsCompact K ∧ (interior K).Nonempty

/-- A centrally symmetric convex disk centered at the origin (§1.1, §2.1): a compact convex set
with nonempty interior, invariant under `x ↦ -x`. -/
def IsCCSDisk (K : Set (Fin 2 → ℝ)) : Prop :=
  Convex ℝ K ∧ IsCompact K ∧ (interior K).Nonempty ∧ ∀ x ∈ K, -x ∈ K

/-- A balanced pair `(K, σ)` (Definition 2.4.7): `K` is a centrally symmetric convex disk and
`σ` is a multi-curve of six regular `C¹` curves `σ_j : ℝ → ℝ²` such that

1. each `σ_j` is `C¹` and regular;
2. each derivative `σ_j'` is Lipschitz;
3. `j ↦ σ_j(t)` is a multi-point for every `t`;
4. the curvature constraint `det(σ_j'(t), σ_j''(t)) ≥ 0` holds for almost every `t`;
5. (star condition) `σ_j'(t)` points into the open cone with apex `σ_j(t)` and rays through
   `σ_{j+1}(t)` and `σ_j(t) + σ_{j+1}(t)`, that is, `σ_j' = α (σ_{j+1} - σ_j) + β σ_{j+1}` with
   `α, β > 0`;
6. the curves are periodic with the common period `6 t_f`, and each `σ_j` restricted to one
   period is a simple closed curve whose image is the boundary of `K`.

The counterclockwise orientation required by item 1 of the definition follows from items 3 and 5
(`det(σ_j, σ_j') > 0`). -/
def IsBalancedPair (K : Set (Fin 2 → ℝ)) (σ : ZMod 6 → ℝ → Fin 2 → ℝ) (tf : ℝ) : Prop :=
  IsCCSDisk K ∧
    (∀ j, ContDiff ℝ 1 (σ j) ∧ ∀ t, deriv (σ j) t ≠ 0) ∧
    (∀ j, ∃ C, LipschitzWith C (deriv (σ j))) ∧
    (∀ t, IsMultiPoint fun j ↦ σ j t) ∧
    (∀ j, ∀ᵐ t, 0 ≤ det2 (deriv (σ j) t) (deriv (deriv (σ j)) t)) ∧
    (∀ j t, ∃ α β : ℝ, 0 < α ∧ 0 < β ∧
      deriv (σ j) t = α • (σ (j + 1) t - σ j t) + β • σ (j + 1) t) ∧
    0 < tf ∧ (∀ j t, σ j (t + 6 * tf) = σ j t) ∧
    (∀ j, Set.InjOn (σ j) (Set.Ico 0 (6 * tf))) ∧
    (∀ j, σ j '' Set.Ico 0 (6 * tf) = frontier K)

/-- A balanced pair is in circle representation (§2.4) if `σ_j(0) = s_j*` for all `j`. -/
def IsCircleRepresentation (σ : ZMod 6 → ℝ → Fin 2 → ℝ) : Prop :=
  ∀ j, σ j 0 = sixthRoot j

end SmoothedPolygons
