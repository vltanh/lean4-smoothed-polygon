module

public import External.MinkowskiMahler
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.LinearAlgebra.AffineSpace.Midpoint
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Mahler's theorem on the circumscribed hexagons of a convex domain

Cited as Theorem 2.3.7 of Hales–Vajjha, *Packings of Smoothed Polygons*, from K. Mahler, *On the
minimum determinant and the circumscribed hexagons of a convex domain*, Proc. Kon. Ned. Akad.
Wet. 50 (1947), 692–703: let `K` be a symmetric convex domain that is not a parallelogram, `Λ` a
critical lattice of `K`, and `P₀, …, P₅` points of `Λ` on the boundary of `K` with
`P₀ - P₁ + P₂ = 0` and `P_{j+3} = -P_j`. There are unique symmetric tac-lines (support lines)
`ℓ_j` of `K` at the points `P_j` such that no two of them coincide, the hexagon `H` bounded by them
has area `4Δ(K)`, each side of `H` is bisected at the point `P_j` where it touches `K`, and `H` has
the least area among the hexagons bounded by symmetric tac-lines of `K`.

Definitions, in the terms of the source; lattices, `Δ(K)` and critical lattices are those of
`External.MinkowskiMahler`. A tac-line of `K` is a line that meets `K` and has `K` on one side. A
tac-line of a symmetric convex domain does not pass through the origin, an interior point, so it
is `ℓ = {x | a · x = 1}` for a unique vector `a`, with `K ⊆ {x | a · x ≤ 1}`; the symmetric
tac-line is `-ℓ = {x | -a · x = 1}`. Six tac-lines `ℓ_j = {x | a_j · x = 1}` bound the hexagon
`{x | a_j · x ≤ 1 for all j}`.
-/

@[expose] public section

namespace External

open MeasureTheory Set Matrix MinkowskiMahler

namespace Mahler1947

/-- `P` is a parallelogram: `P = {c + s u + t v | |s| ≤ 1, |t| ≤ 1}` with `u, v` linearly
independent. -/
def IsParallelogram (P : Set (Fin 2 → ℝ)) : Prop :=
  ∃ c u v : Fin 2 → ℝ, cross u v ≠ 0 ∧
    P = {x | ∃ s t : ℝ, |s| ≤ 1 ∧ |t| ≤ 1 ∧ x = c + s • u + t • v}

/-- A tac-line (support line) of `K`: a line `{x | a · x = c}`, `a ≠ 0`, that meets `K` and has
`K` on one side. -/
def IsTacLine (K ℓ : Set (Fin 2 → ℝ)) : Prop :=
  (∃ a : Fin 2 → ℝ, a ≠ 0 ∧ ∃ c : ℝ, ℓ = {x | a ⬝ᵥ x = c} ∧ ∀ x ∈ K, a ⬝ᵥ x ≤ c) ∧
    (ℓ ∩ K).Nonempty

/-- The hexagon `{x | a_j · x ≤ 1 for all j}` bounded by the lines `{x | a_j · x = 1}`. -/
def hexagon (a : ZMod 6 → Fin 2 → ℝ) : Set (Fin 2 → ℝ) := {x | ∀ j, a j ⬝ᵥ x ≤ 1}

/-- The conclusion of Mahler's theorem for the tac-lines `ℓ_j = {x | a_j · x = 1}` at the points
`P_j`: the lines are symmetric (`a_{j+3} = -a_j`) tac-lines of `K` through `P_j`, and the only
tac-lines of `K` at `P_j` (Mahler's (i): "there are unique tac-lines … at these points"; his
footnote 7: they are tangents of the boundary), no two coincide,
the hexagon `H` they bound has area `4Δ(K)`, each side of `H` is bisected at `P_j`, and `H` has
the least area among the hexagons bounded by six distinct symmetric tac-lines of `K`. -/
def IsMahlerHexagon (K : Set (Fin 2 → ℝ)) (P a : ZMod 6 → Fin 2 → ℝ) : Prop :=
  (∀ j, a (j + 3) = -a j) ∧
  (∀ j, IsTacLine K {x | a j ⬝ᵥ x = 1} ∧ a j ⬝ᵥ P j = 1) ∧
  (∀ j ℓ, IsTacLine K ℓ → P j ∈ ℓ → ℓ = {x | a j ⬝ᵥ x = 1}) ∧
  (∀ i j, i ≠ j → a i ≠ a j) ∧
  volume.real (hexagon a) = 4 * minimalDeterminant K ∧
  (∀ j, ∃ p q, hexagon a ∩ {x | a j ⬝ᵥ x = 1} = segment ℝ p q ∧ P j = midpoint ℝ p q) ∧
  ∀ b : ZMod 6 → Fin 2 → ℝ, (∀ j, b (j + 3) = -b j) → (∀ i j, i ≠ j → b i ≠ b j) →
    (∀ j, IsTacLine K {x | b j ⬝ᵥ x = 1}) → volume (hexagon a) ≤ volume (hexagon b)

end Mahler1947

open Mahler1947 in
/-- **Mahler (1947).** Let `K` be a symmetric convex domain which is not a parallelogram, `Λ` a
critical lattice of `K`, and `P₀, …, P₅` points of `Λ` on the boundary of `K` with
`P₀ - P₁ + P₂ = 0` and `P_{j+3} = -P_j`. Then there are unique symmetric tac-lines of `K` at these
points such that no two of them coincide, the hexagon `H` bounded by them has area
`area(H) = 4Δ(K)`, each side of `H` is bisected at the point `P_j` where it touches the boundary of
`K`, and `area(H)` is the least area of a hexagon bounded by symmetric tac-lines of `K`.

The minimality is Mahler's Theorem 1 (`Δ(K) = ¼ inf_H V(H)` over the hexagons and parallelograms
bounded by symmetric tac-lines, the bound being attained); here it is compared only with hexagons
bounded by six distinct symmetric tac-lines, which is no stronger. Mahler takes all the points of
`Λ` on the boundary; for a domain that is not a parallelogram these are six points as above. -/
theorem mahler_1947 {K : Set (Fin 2 → ℝ)} (hK : IsSymmetricConvexDomain K)
    (hpar : ¬ IsParallelogram K) {Λ : Submodule ℤ (Fin 2 → ℝ)} (hΛ : IsCritical K Λ)
    {P : ZMod 6 → Fin 2 → ℝ} (hPΛ : ∀ j, P j ∈ Λ) (hPK : ∀ j, P j ∈ frontier K)
    (h012 : P 0 - P 1 + P 2 = 0) (hsymm : ∀ j, P (j + 3) = -P j) :
    ∃! a, IsMahlerHexagon K P a := by
  sorry

end External
