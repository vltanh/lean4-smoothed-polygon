module

public import SmoothedPolygons.Ch14.NoReturn
public import SmoothedPolygons.Ch14.NoReturnTools
public import SmoothedPolygons.Ch8.EdgePullback
public import SmoothedPolygons.Ch8.FiniteBangBang

/-!
# Chapter 14: the reading of "trajectory" in Theorem 14.4.1 is no restriction

`Theorem14_4_1` (`SmoothedPolygons/Ch14/NoReturn.lean`) reads "a trajectory of the Reinhardt
system" (Theorem 14.4.1, Hales–Vajjha, *Packings of Smoothed Polygons*, TeX 11995–12002) as an
extremal on `[a, c]` (`λ_cost = -1`) that is bang-bang with finitely many switches on every compact
subinterval of `(a, c)`. The module docstring there leaves open whether the statement without that
hypothesis has a counterexample. It has none: **the two statements are equivalent**
(`theorem14_4_1_iff_unrestricted`).

## Why

The finite bang-bang hypothesis is used only before the first return to the singular locus, where
it holds anyway. A normal extremal (`λ_cost = -1 ≠ 0`) is edge extremal on every subinterval
(`IsExtremalOn.isEdgeExtremalOn_of_ne_zero`: the pulled-back costate is an edge costate, E55, E57),
so by Theorem 8.3.2 (`theorem8_3_2`) it is finitely bang-bang on every compact interval on which its
lift avoids the singular locus. In the first statement, if the lift met the singular locus at some
`t ∈ (a, c]`, then `t > b` (the chattering arc out of `a` avoids it on `(a, b]`), and the first
meeting time `s ∈ (b, t]` (`IsExtremalOn.exists_first_mem_singularLocus`) has the lift off the
singular locus on `(a, s)`; so the extremal on `[a, s]` is finitely bang-bang on compact
subintervals of `(a, s)`, and `Theorem14_4_1` on `[a, s]` (with the same `b`) says that the lift
avoids the singular locus at `s`: a contradiction. The second statement is the first for the
reflected extremal (`IsExtremalOn.reverse`, `IsChatteringArcInto.reverse`, as in
`theorem14_4_1_in`, `SmoothedPolygons/Ch14/NoReturnProof.lean`). The converse implication drops a
hypothesis.

Possible counterexamples to the unrestricted statement would have to be non-bang-bang extremals
that return to the singular locus: singular arcs (Theorem 8.2.3) lie in the singular locus, and
edge-singular arcs are excluded for normal extremals by edge extremality (Theorems 8.1.4, 8.3.2);
abnormal extremals (`λ_cost = 0`, Remark 8.1.6, E57), which can use any control in an edge, never
meet the singular locus (`IsExtremalOn.mem_singularLocus_iff` needs `λ_cost ≠ 0`), and every
extremal that meets it can be normalized to `λ_cost = -1` (`IsExtremalOn.normalize`). The bang-bang
clause inside `IsChatteringArcOutOf` / `IsChatteringArcInto` is likewise a consequence of
Theorem 8.3.2 (the lift avoids the singular locus on the open arc); it is kept there because the
switching sequence `τ` is part of the statement.

## Proof (planned)

`→`: the argument above (first statement: `exists_first_mem_singularLocus`, `IsExtremalOn.mono`,
`theorem8_3_2` with `isEdgeExtremalOn_of_ne_zero` for `α < β`, the empty case `β ≤ α` directly;
second statement: the reflection, as in `theorem14_4_1_in`). `←`: drop the hypothesis.
Size: 100–150 lines.
-/

@[expose] public section

namespace SmoothedPolygons

open Set Filter Topology
open TriFuller

/-- **The reading of Theorem 14.4.1 is no restriction**: `Theorem14_4_1` (for extremals that are
finitely bang-bang on compact subintervals of `(a, c)`) is equivalent to the same statement for all
extremals on `[a, c]` with `λ_cost = -1` (Theorem 8.3.2 supplies the finite bang-bang control up to
the first return to the singular locus, which is all the statement needs). -/
theorem theorem14_4_1_iff_unrestricted : Theorem14_4_1 ↔
    (∀ (a b c : ℝ) (u : ℝ → Fin 3 → ℝ) (g X Λ₁ ΛR : ℝ → Mat2) (τ : ℕ → ℝ),
      IsExtremalOn a c u g X Λ₁ ΛR (-1) → b ∈ Ioc a c →
      IsChatteringArcOutOf a b u g X Λ₁ ΛR τ →
      TendstoModVT (switchAng X Λ₁ ΛR τ) (ang qOutCart) →
      ∀ t ∈ Ioc a c, (g t, Λ₁ t, X t, ΛR t) ∉ singularLocus) ∧
    ∀ (a b c : ℝ) (u : ℝ → Fin 3 → ℝ) (g X Λ₁ ΛR : ℝ → Mat2) (τ : ℕ → ℝ),
      IsExtremalOn a c u g X Λ₁ ΛR (-1) → b ∈ Ico a c →
      IsChatteringArcInto b c u g X Λ₁ ΛR τ →
      TendstoModVT (switchAng X Λ₁ ΛR τ) (ang (tau qOutCart)) →
      ∀ t ∈ Ico a c, (g t, Λ₁ t, X t, ΛR t) ∉ singularLocus := by
  sorry

end SmoothedPolygons
