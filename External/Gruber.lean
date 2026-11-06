module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# The density of a lattice packing

Cited in Definition 2.1.2 of Hales–Vajjha, *Packings of Smoothed Polygons*, from P. M. Gruber,
*Convex and Discrete Geometry*, Grundlehren 336, Springer, 2007, Corollary 30.1: if `C` is a convex
body and `L` a lattice such that the translates `C + l`, `l ∈ L`, have pairwise disjoint
interiors, then the upper and lower densities of the lattice packing `{C + l | l ∈ L}` coincide
and are equal to `V(C)/d(L)`.

Definitions, in the terms of the source. Space is `E^d = ι → ℝ` with Lebesgue measure `V`. A
convex body is a compact convex set, here with nonempty interior. A lattice is
`L = {z₁ b₁ + ⋯ + z_d b_d | zᵢ ∈ ℤ}` for a basis `b₁, …, b_d` of `E^d`, and `d(L) = |det(b₁, …,
b_d)|`. The upper and lower densities of the lattice packing are
`limsup` and `liminf`, as `λ → ∞`, of `Σ_{l ∈ L} V((C + l) ∩ λB^d) / V(λB^d)`, where
`λB^d = {x | Σ xᵢ² ≤ λ²}` is the solid Euclidean ball of radius `λ` about the origin. Densities
take values in `[0, ∞]`.
-/

@[expose] public section

namespace External

open MeasureTheory Filter Set
open scoped ENNReal

namespace Gruber

variable {ι : Type*} [Fintype ι]

/-- The solid Euclidean ball `λB^d = {x | Σ xᵢ² ≤ λ²}` of radius `λ` about the origin. -/
def ball (r : ℝ) : Set (ι → ℝ) := {x | ∑ i, x i ^ 2 ≤ r ^ 2}

/-- A (proper) convex body: a compact convex set with nonempty interior. -/
def IsConvexBody (C : Set (ι → ℝ)) : Prop :=
  Convex ℝ C ∧ IsCompact C ∧ (interior C).Nonempty

/-- The lattice `L = ℤ b₁ + ⋯ + ℤ b_d` with basis `b`. -/
noncomputable def lattice (b : Module.Basis ι ℝ (ι → ℝ)) : Submodule ℤ (ι → ℝ) :=
  Submodule.span ℤ (range b)

/-- The determinant `d(L) = |det(b₁, …, b_d)|` of the lattice with basis `b`. -/
noncomputable def latticeDet [DecidableEq ι] (b : Module.Basis ι ℝ (ι → ℝ)) : ℝ :=
  |(Matrix.of fun i j ↦ b i j).det|

/-- `{C + l | l ∈ L}` is a packing: the translates have pairwise disjoint interiors. -/
def IsLatticePacking (C : Set (ι → ℝ)) (b : Module.Basis ι ℝ (ι → ℝ)) : Prop :=
  ∀ l ∈ lattice b, ∀ l' ∈ lattice b, l ≠ l' →
    Disjoint (interior ((fun x ↦ x + l) '' C)) (interior ((fun x ↦ x + l') '' C))

/-- The ratio `Σ_{l ∈ L} V((C + l) ∩ λB^d) / V(λB^d)`. -/
noncomputable def densityRatio (C : Set (ι → ℝ)) (b : Module.Basis ι ℝ (ι → ℝ)) (r : ℝ) :
    ℝ≥0∞ :=
  (∑' l : lattice b, volume ((fun x ↦ x + (l : ι → ℝ)) '' C ∩ ball r)) / volume (ball (ι := ι) r)

/-- The upper density of the lattice packing `{C + l | l ∈ L}`. -/
noncomputable def upperDensity (C : Set (ι → ℝ)) (b : Module.Basis ι ℝ (ι → ℝ)) : ℝ≥0∞ :=
  limsup (densityRatio C b) atTop

/-- The lower density of the lattice packing `{C + l | l ∈ L}`. -/
noncomputable def lowerDensity (C : Set (ι → ℝ)) (b : Module.Basis ι ℝ (ι → ℝ)) : ℝ≥0∞ :=
  liminf (densityRatio C b) atTop

end Gruber

open Gruber in
/-- **Gruber, *Convex and Discrete Geometry*, Corollary 30.1.** If `C` is a convex body and `L` a
lattice such that `{C + l | l ∈ L}` is a packing, then its upper and lower densities are both
equal to `V(C)/d(L)`. -/
theorem gruber_corollary_30_1 {ι : Type*} [Fintype ι] [DecidableEq ι] {C : Set (ι → ℝ)}
    (hC : IsConvexBody C) {b : Module.Basis ι ℝ (ι → ℝ)} (hCb : IsLatticePacking C b) :
    upperDensity C b = ENNReal.ofReal (volume.real C / latticeDet b) ∧
      lowerDensity C b = ENNReal.ofReal (volume.real C / latticeDet b) := by
  sorry

end External
