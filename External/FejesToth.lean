module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Fejes Tóth's theorem: lattice packings are densest for centrally symmetric disks

Cited as Theorem 2.1.3 of Hales–Vajjha, *Packings of Smoothed Polygons*, from L. Fejes Tóth,
*Some packing and covering theorems*, Acta Sci. Math. Szeged 12(A) (1950), 62–67, and
*Lagerungen in der Ebene auf der Kugel und im Raum*, Springer, 1953 (3rd edition with G. Fejes
Tóth and W. Kuperberg, 2023): if `K` is a centrally symmetric convex disk, then the greatest
density of a packing of congruent copies of `K` equals the greatest density of a lattice packing
of translates of `K`, `δ(K) = δ_L(K)`.

Definitions, in the terms of the source. The plane is `Fin 2 → ℝ` with Lebesgue measure. A
*packing* is a family of sets with pairwise disjoint interiors. The *upper density* of a family
`𝒜` is `limsup_{r → ∞} Σ_{A ∈ 𝒜} area(A ∩ D_r) / area(D_r)`, where `D_r` is the circular disk of
radius `r` about the origin. `δ(K)` is the supremum of the upper densities of the packings of
congruent copies of `K` (images under Euclidean motions `x ↦ A x + b`, `A` orthogonal), and
`δ_L(K)` the supremum of the upper densities of the lattice packings `{K + l | l ∈ L}`, `L` a
lattice (a discrete subgroup of `ℝ²` spanning `ℝ²`). Taking suprema of upper densities gives the
strongest form of the statement (no packing of congruent copies is denser, even in the sense of
upper density, than the best lattice packing). Densities take values in `[0, ∞]`.
-/

@[expose] public section

namespace External

open MeasureTheory Filter Set Matrix
open scoped ENNReal

namespace FejesToth

/-- The circular disk `D_r = {x | x₀² + x₁² ≤ r²}`. -/
def disk (r : ℝ) : Set (Fin 2 → ℝ) := {x | x 0 ^ 2 + x 1 ^ 2 ≤ r ^ 2}

/-- A convex disk (convex domain): a compact convex set with nonempty interior. -/
def IsConvexDisk (K : Set (Fin 2 → ℝ)) : Prop :=
  Convex ℝ K ∧ IsCompact K ∧ (interior K).Nonempty

/-- `K` is centrally symmetric (about the origin). -/
def IsCentrallySymmetric (K : Set (Fin 2 → ℝ)) : Prop := ∀ x ∈ K, -x ∈ K

/-- `K'` is congruent to `K`: `K' = {A x + b | x ∈ K}` with `A` orthogonal. -/
def IsCongruent (K K' : Set (Fin 2 → ℝ)) : Prop :=
  ∃ A ∈ Matrix.orthogonalGroup (Fin 2) ℝ, ∃ b : Fin 2 → ℝ, K' = (fun x ↦ A *ᵥ x + b) '' K

/-- A packing: a family of sets with pairwise disjoint interiors. -/
def IsPacking (𝒜 : Set (Set (Fin 2 → ℝ))) : Prop :=
  𝒜.Pairwise fun A B ↦ Disjoint (interior A) (interior B)

/-- The upper density `limsup_{r → ∞} Σ_{A ∈ 𝒜} area(A ∩ D_r) / area(D_r)` of a family. -/
noncomputable def upperDensity (𝒜 : Set (Set (Fin 2 → ℝ))) : ℝ≥0∞ :=
  limsup (fun r ↦ (∑' A : 𝒜, volume ((A : Set (Fin 2 → ℝ)) ∩ disk r)) / volume (disk r)) atTop

/-- The greatest packing density `δ(K)`: the supremum of the upper densities of the packings of
congruent copies of `K`. -/
noncomputable def packingDensity (K : Set (Fin 2 → ℝ)) : ℝ≥0∞ :=
  ⨆ (𝒜 : Set (Set (Fin 2 → ℝ))) (_ : IsPacking 𝒜) (_ : ∀ A ∈ 𝒜, IsCongruent K A),
    upperDensity 𝒜

/-- A lattice: a discrete subgroup of `ℝ²` that spans `ℝ²`. -/
def IsLattice (L : Submodule ℤ (Fin 2 → ℝ)) : Prop :=
  DiscreteTopology L ∧ Submodule.span ℝ (L : Set (Fin 2 → ℝ)) = ⊤

/-- The family of translates `{K + l | l ∈ L}`. -/
def translates (K : Set (Fin 2 → ℝ)) (L : Submodule ℤ (Fin 2 → ℝ)) : Set (Set (Fin 2 → ℝ)) :=
  range fun l : L ↦ (fun x ↦ x + (l : Fin 2 → ℝ)) '' K

/-- The greatest lattice packing density `δ_L(K)`: the supremum of the upper densities of the
lattice packings of `K`. -/
noncomputable def latticePackingDensity (K : Set (Fin 2 → ℝ)) : ℝ≥0∞ :=
  ⨆ (L : Submodule ℤ (Fin 2 → ℝ)) (_ : IsLattice L) (_ : IsPacking (translates K L)),
    upperDensity (translates K L)

end FejesToth

open FejesToth in
/-- **Fejes Tóth (1950).** For a centrally symmetric convex disk `K`, the greatest packing density
of `K` equals its greatest lattice packing density: `δ(K) = δ_L(K)`. -/
theorem fejes_toth {K : Set (Fin 2 → ℝ)} (hK : IsConvexDisk K) (hsymm : IsCentrallySymmetric K) :
    packingDensity K = latticePackingDensity K := by
  sorry

end External
