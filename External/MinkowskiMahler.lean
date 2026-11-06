module

public import Mathlib.Algebra.Module.ZLattice.Covolume

/-!
# Critical lattices of a symmetric convex domain (Minkowski, Mahler)

Cited as Theorem 2.3.6 of Hales–Vajjha, *Packings of Smoothed Polygons*, from H. Minkowski,
*Diophantische Approximationen*, Teubner, 1907, and K. Mahler, *Lattice points in n-dimensional
star bodies II*, Proc. Kon. Ned. Akad. Wet. 49 (1946), 331–343: a critical lattice `Λ` of a
symmetric convex domain `K` has three points `P₀, P₁, P₂` on the boundary of `K` with
`P₁ = P₀ + P₂` such that `P₀, P₁` is a basis of `Λ`, so that `d(Λ) = |det(P₀, P₁)| = Δ(K)`;
conversely, for any three boundary points with `P₁ = P₀ + P₂`, `|det(P₀, P₁)| ≥ Δ(K)`, with
equality exactly when the lattice with basis `P₀, P₁` is critical.

Definitions, in the terms of the sources. The plane is `Fin 2 → ℝ`. A symmetric convex domain is a
compact convex set with nonempty interior, symmetric about the origin `O`. A lattice `Λ` is a
discrete subgroup of `ℝ²` spanning `ℝ²`; its determinant `d(Λ)` is the area of a fundamental
parallelogram (Mathlib's covolume, equal to `|det(a, b)|` for every basis `a, b`). `Λ` is
`K`-admissible if `O` is its only point in the interior of `K`; `Δ(K)` is the infimum of `d(Λ)`
over the `K`-admissible lattices, and a critical lattice is a `K`-admissible lattice with
`d(Λ) = Δ(K)`. These definitions are shared with `External.Mahler1947`.
-/

@[expose] public section

namespace External

namespace MinkowskiMahler

open Set

/-- The determinant `det(u, v) = u₀v₁ - u₁v₀` of two vectors of the plane. -/
def cross (u v : Fin 2 → ℝ) : ℝ := u 0 * v 1 - u 1 * v 0

/-- A symmetric convex domain: a compact convex set with nonempty interior, symmetric about the
origin. -/
def IsSymmetricConvexDomain (K : Set (Fin 2 → ℝ)) : Prop :=
  Convex ℝ K ∧ IsCompact K ∧ (interior K).Nonempty ∧ ∀ x ∈ K, -x ∈ K

/-- A lattice: a discrete subgroup of `ℝ²` that spans `ℝ²`. -/
def IsLattice (Λ : Submodule ℤ (Fin 2 → ℝ)) : Prop :=
  DiscreteTopology Λ ∧ Submodule.span ℝ (Λ : Set (Fin 2 → ℝ)) = ⊤

/-- The determinant `d(Λ)` of a lattice: the area of a fundamental parallelogram. -/
noncomputable def det (Λ : Submodule ℤ (Fin 2 → ℝ)) : ℝ := ZLattice.covolume Λ

/-- `a, b` is a basis of the lattice `Λ`. -/
def IsBasis (Λ : Submodule ℤ (Fin 2 → ℝ)) (a b : Fin 2 → ℝ) : Prop :=
  LinearIndependent ℤ ![a, b] ∧ Submodule.span ℤ {a, b} = Λ

/-- `Λ` is `K`-admissible: the origin is the only point of `Λ` in the interior of `K`. -/
def IsAdmissible (K : Set (Fin 2 → ℝ)) (Λ : Submodule ℤ (Fin 2 → ℝ)) : Prop :=
  ∀ x ∈ Λ, x ∈ interior K → x = 0

/-- The minimal determinant `Δ(K)`: the infimum of `d(Λ)` over the `K`-admissible lattices. -/
noncomputable def minimalDeterminant (K : Set (Fin 2 → ℝ)) : ℝ :=
  sInf {d | ∃ Λ, IsLattice Λ ∧ IsAdmissible K Λ ∧ det Λ = d}

/-- A critical lattice of `K`: a `K`-admissible lattice with `d(Λ) = Δ(K)`. -/
def IsCritical (K : Set (Fin 2 → ℝ)) (Λ : Submodule ℤ (Fin 2 → ℝ)) : Prop :=
  IsLattice Λ ∧ IsAdmissible K Λ ∧ det Λ = minimalDeterminant K

end MinkowskiMahler

open MinkowskiMahler in
/-- **Minkowski (1907), Mahler (1946).** Let `Λ` be a critical lattice of a symmetric convex domain
`K`. Then `Λ` has three points `P₀, P₁, P₂` on the boundary of `K` with `P₁ = P₀ + P₂` (the
parallelogram `O P₀ P₁ P₂`) such that `P₀, P₁` is a basis of `Λ` and
`d(Λ) = |det(P₀, P₁)| = Δ(K)`. Conversely, if `P₀, P₁, P₂` are points on the boundary of `K` with
`P₁ = P₀ + P₂`, then `|det(P₀, P₁)| ≥ Δ(K)`, with equality if and only if the lattice with basis
`P₀, P₁` is critical. -/
theorem minkowski_mahler {K : Set (Fin 2 → ℝ)} (hK : IsSymmetricConvexDomain K) :
    (∀ Λ, IsCritical K Λ →
      ∃ P₀ P₁ P₂ : Fin 2 → ℝ, P₀ ∈ Λ ∧ P₁ ∈ Λ ∧ P₂ ∈ Λ ∧
        P₀ ∈ frontier K ∧ P₁ ∈ frontier K ∧ P₂ ∈ frontier K ∧
        IsBasis Λ P₀ P₁ ∧ P₁ = P₀ + P₂ ∧
        det Λ = |cross P₀ P₁| ∧ |cross P₀ P₁| = minimalDeterminant K) ∧
    ∀ P₀ P₁ P₂ : Fin 2 → ℝ, P₀ ∈ frontier K → P₁ ∈ frontier K → P₂ ∈ frontier K →
      P₁ = P₀ + P₂ →
        minimalDeterminant K ≤ |cross P₀ P₁| ∧
          (|cross P₀ P₁| = minimalDeterminant K ↔
            IsCritical K (Submodule.span ℤ {P₀, P₁})) := by
  sorry

end External
