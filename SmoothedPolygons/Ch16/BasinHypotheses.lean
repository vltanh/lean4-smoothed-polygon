module

public import SmoothedPolygons.Ch15.CellCoordinates
public import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Chapter 16: the numerical facts behind the global basin theorem (Table 16.1)

The proof of Theorem 16.1.1 (`thm:basin`) of Hales–Vajjha, *Packings of Smoothed Polygons*
(TeX 12511–12744) rests on containments of the Fuller–Poincaré map that the book computes
numerically in Mathematica and shows in Figures 16.1–16.4 (Table 16.1, "Upper triangular structure
of the Fuller–Poincaré map on the two big cells"). This file states them as three named
propositions, the explicit hypotheses of `theorem16_1_1` (`SmoothedPolygons/Ch16/GlobalBasin.lean`),
to be certified later (layer 5b):

* `DOutContracts`: `F(𝒟_out) ⊆ 𝒟_out` (the row `𝒟_out` of Table 16.1, Figure 16.1, TeX 12592–12607)
  and a contraction to `q_out` inside `𝒟_out` (the book: "The forward iterates `F₁^k(𝒟_out)` quickly
  shrink toward `q_out`", unproved; gap G16.3);
* `CellTwoEntersDOut`: every point of the second big cell enters `𝒟_out` within three steps (the
  rows `𝒟₂` and `𝒟₃`, TeX 12616–12620, 12629–12638, and `F²𝒟₃ ⊂ 𝒟₀₀`, Figure 16.2, TeX
  12640–12665);
* `BoxSubclaims`: the subclaims `subclaim_{ij}` (TeX 12677–12726, Figures 16.3–16.4), with the row
  `𝒟₄` (TeX 12612–12615) merged in: from a box `𝒟_{ij}`, `(i, j) ∉ {(0,0), (2,2)}`, the map goes to
  the second big cell or to a lexicographically smaller box.

## The regions

The boxes `𝒟_{ij} = {r₂ ∈ [0, 1], ψ ∈ [a_i, a_{i+1}], θ₂ ∈ [b_{j+1}, b_j]}` of the first big cell
(TeX 12526–12534), with `(a₀, …, a₃) = (0, π/3, 2π/3, π)` and `(b₀, …, b₃) = (π, π - 1.1, 1.1, 0)`
(`cellBox`; the book prints `θ₂ ∈ [b_{i+1}, b_i]`, an index slip with one reading, gap G16.1), as
sets of `Ξ_{𝒲,0}/V_T` (`boxSet i j`); `𝒟_out = 𝒟₀₀` and `𝒟_in ⊆ 𝒟₂₂` (gap G16.13: TeX 12680 swaps
the two). The second big cell is `cellTwoSet` (first control `ζ²`, `x₃ < 0`, including its top
face `θ₂ = 0`). These are the regions of Table 16.1 that are boxes; the curved parts `𝒟₀, 𝒟₁, 𝒟₄`
and the split `𝒟₂ | 𝒟₃` (`SmoothedPolygons/Ch15/Involution.lean`) are not needed:
* the book's `𝒟_in = 𝒟₁ ∩ 𝒟₂₂` is replaced by the whole box `𝒟₂₂`; its row ("can be anything") is
  unchanged, and `𝒟₀ ⊂ 𝒟₂₂` (the book's "`𝒟₀ ⊂ 𝒟_in`") is no longer used;
* the rows `𝒟₄` and `𝒟₁ ∖ 𝒟_in`: a point of a box `𝒟_{ij}` of the first cell goes either to the
  second cell (it lies in `𝒟₄`) or to a smaller box (the book's `subclaim_{ij}` on `𝒟_{1,ij}`), and
  no orbit re-enters `𝒟₂₂` (proved from `DOutContracts` by time reversal, `theorem16_1_1`), which
  replaces the book's argument by exclusion (`𝒟₀ ⊂ 𝒟_in`, `𝒟₄ ⊂ F(𝒟₂₂)` and the injectivity of `F`,
  gap G16.5);
* the rows `𝒟₂ → 𝒟₃ → 𝒟₁ ∖ 𝒟_in` and `F²𝒟₃ ⊂ 𝒟₀₀` give: from the second cell, `𝒟₀₀` within three
  steps.

## The map and the faces

The facts are about the Poincaré map `poincareAngZero` of `Ξ_{𝒲,0}/V_T` (the switch happens when
the first control stops being optimal), at every point of the closed boxes, faces included. At a
face point where the cell's control is not the first control (the red regions of Figure 15.1,
`proposition15_2_2`), the book's extended map is the identity of `Ξ_{𝒲,0}/V_T` (a change of
representative), and the fact is about the point's actual first switch. All three were checked by
sampling, with the first control chosen by the lexicographic rule of Lemma 13.2.6 and the first
switching time as the least positive sign change of the switching cubics, including points on and
within `10⁻⁹` of every face (the coordinator's earlier sampling, inventory C16.1–C16.3, and new
runs for this formulation; no violation).

## Certification (layer 5b): direct enclosure instead of the boundary method

The book's "boundary method" (TeX 12577–12587: `F_i(∂𝒟) ⊂ 𝒟̃` convex suffices when `𝒟` is a closed
ball) needs `F_i` injective on `𝒟` and invariance of domain (gap G16.2), and the images of the
curved faces. The facts here are stated so that they can be certified by **direct enclosure**:
subdivide the domain box into small boxes; on each, decide the first control by the signs of `y₂`,
`y₁`; enclose the switching time as a root of the explicit switching cubics (`chiA_chiB_eq`;
coefficients affine in `x_j, y_j`, which are `r_j cos θ_j`, `r_j sin θ_j`) by sign changes at the
ends of an interval and a sign of the derivative (interval Newton), and the positivity of the other
switching cubic up to it; enclose `z(t)` (polynomial in `t`), the rotation onto `𝒲₀` (a fixed power
of `ζ` for each switch), the rescaling to `r₁ + r₂ = 1` (a quadratic root) and the arguments; check
the inclusion in the target boxes. No ODE is solved. Near the faces where the switching time tends
to `0`, a local expansion replaces the root enclosure. The transcendental functions need verified
bounds (Taylor models for `sin`, `cos`, `arctan`, `√`; Mathlib has no interval arithmetic).
-/

@[expose] public section

namespace SmoothedPolygons

open Set Filter Topology
open scoped Real NNReal

namespace TriFuller

/-- The `ψ`-breakpoints `(a₀, a₁, a₂, a₃) = (0, π/3, 2π/3, π)` of the boxes (TeX 12533–12534). -/
noncomputable def basinA : Fin 4 → ℝ := ![0, π / 3, 2 * π / 3, π]

/-- The `θ₂`-breakpoints `(b₀, b₁, b₂, b₃) = (π, π - 1.1, 1.1, 0)` of the boxes (TeX 12534). -/
noncomputable def basinB : Fin 4 → ℝ := ![π, π - 1.1, 1.1, 0]

/-- The box `𝒟_{ij}` of the first big cell (TeX 12526–12531): `r₂ ∈ [0, 1]`, `ψ ∈ [a_i, a_{i+1}]`,
`θ₂ ∈ [b_{j+1}, b_j]` (corrected index; the book prints `θ₂ ∈ [b_{i+1}, b_i]`, gap G16.1). -/
def cellBox (i j : Fin 3) : Set (Fin 3 → ℝ) :=
  {p | p 0 ∈ Icc 0 1 ∧ p 1 ∈ Icc (basinA i.castSucc) (basinA i.succ) ∧
    p 2 ∈ Icc (basinB j.succ) (basinB j.castSucc)}

/-- The box `𝒟_{ij}` as a set of `Ξ_{𝒲,0}/V_T`. `boxSet 0 0` is `𝒟_out = 𝒟₀₀` and `boxSet 2 2` is
the box `𝒟₂₂ ⊇ 𝒟_in` (TeX 12535–12537). -/
noncomputable def boxSet (i j : Fin 3) : Set XiW0Quot := cellClass '' cellBox i j

/-- The lexicographic order on box indices: `(k, ℓ) ≺ (i, j)` iff `k < i`, or `k = i` and `ℓ < j`
(TeX 12686–12691). -/
def BoxLexLt (k l i j : Fin 3) : Prop := k < i ∨ (k = i ∧ l < j)

/-- The nine boxes cover the closed first big cell. -/
theorem closedBoxOne_eq_iUnion_cellBox : closedBoxOne = ⋃ i, ⋃ j, cellBox i j := by
  sorry

/-- The time reversal exchanges `𝒟₀₀ = 𝒟_out` and `𝒟₂₂` (TeX 12729–12732: `τ(𝒟_in) ⊆ 𝒟_out`):
`τ(r₂, ψ, θ₂) = (r₂, π - ψ, π - θ₂)` maps `ψ ∈ [0, π/3]`, `θ₂ ∈ [π - 1.1, π]` onto `ψ ∈ [2π/3, π]`,
`θ₂ ∈ [0, 1.1]` (`cellClass_cellTau`). -/
theorem tauZero_image_boxSet :
    tauZero '' boxSet 0 0 = boxSet 2 2 ∧ tauZero '' boxSet 2 2 = boxSet 0 0 := by
  sorry

/-! ### The named numerical facts -/

/-- **`F` maps `𝒟_out` into itself and contracts it to `q_out`** (Table 16.1, row `𝒟_out`; Figure
16.1, TeX 12592–12607: "We compute the interval containment `F₁(𝒟_out) ⊂ 𝒟_out` by the boundary
method. … The forward iterates `F₁^k(𝒟_out)` quickly shrink toward `q_out`"). The book proves only
the containment and the local stability of `q_out` (Lemma 13.5.5), which do not give convergence of
every point of `𝒟_out` (gap G16.3); the contraction is the repair proposed in the inventory (C16.1):
* `F(𝒟₀₀) ⊆ 𝒟₀₀`;
* there are a box `B = [lo, hi]` in the open first cell, `N` and `κ < 1` with `F^N(𝒟₀₀) ⊆ B`, and a
  map `g` of `B` into itself, `κ`-Lipschitz (sup norm of the coordinates `(r₂, ψ, θ₂)`), which is
  `F` in coordinates on `B`.

Recommended witnesses: `lo = (0.25, 0.15, 2.85)`, `hi = (0.29, 0.19, 2.98)`, `N = 2`, `κ = 1/2`.
Sampling (20,000 points of `𝒟₀₀`, a fifth of them within `10⁻⁸` of the faces, and the exact faces):
the sampled hull of `F(𝒟₀₀)` is `[0.0245, 0.2737] × [0.0064, 0.1939] × [2.7329, 3.1389]`, but the
true image comes arbitrarily close to `r₂ = 0`, `ψ = 0`, `θ₂ = π`: `𝒟₀₀` contains the edge
`r₂ = 0`, `θ₂ ∈ [0.9944, π/3)`, where the first control is `1`, and at interior points near it the
switching time tends to `0` and the image has `r₂` near `0`. So `F(𝒟₀₀)` lies in no compact box of
the open cell, and `N ≥ 2` is forced. The second step is the delicate one near the corner
`r₂ = 0`, `θ₂ = π/3`: there `F(q)` tends to the class of `(-1, 0, 0)`, where `F_ang` is
discontinuous (from the second cell's side the switching time tends to `0`), and `F²(q) ∈ B`
holds because `F(q)` approaches from `θ₂ < π` (to first order `θ₂ ≈ π - 2δ`); a certificate must
treat this corner separately. Then
`F²(𝒟₀₀) ⊆ [0.2654, 0.2697] × [0.1652, 0.1742] × [2.8964, 2.9296]` (margin `0.0152` in `B`),
`F(B) ⊆ [0.26668, 0.26897] × [0.16801, 0.17253] × [2.90549, 2.92458]` (margin `0.0167`), and the
Jacobian of `g` on `B` has sup-operator norm `≤ 0.32` (eigenvalues at `q_out`: `-0.0800, -0.0081,
0.00065`, as in Lemma 13.5.5). One step fails broadly, not only near `r₂ = 0`: about half of `𝒟₀₀`
maps outside `B` (for instance `F(1, 1/2, 5/2)` has `θ₂ ≈ 2.7817 < 2.85`). An independent
mpmath check (about 1.1 million evaluations) confirmed these figures. In it, the cell of an image
with `z₃ ≠ 0` was always decided by the control that beats the first control, so the walls between
the cells need no metric margin; the margin of `F(𝒟₀₀) ⊆ 𝒟₀₀` to the inner edges of the box is
`0.69`.

Certification: direct enclosure of `F` and `F²` on a subdivision of `𝒟₀₀` (module docstring);
for `g`: on `B` the first control is `ζ`, the switch is the simple root of `χ_A` near `t ≈ 5.0`
(`χ_B > 0` before it), and `g` is explicit; bound the row sums of `Dg` (implicit differentiation of
the root) by interval evaluation, then the mean value inequality on the convex box. -/
def DOutContracts : Prop :=
  MapsTo poincareAngZero (boxSet 0 0) (boxSet 0 0) ∧
    ∃ (lo hi : Fin 3 → ℝ) (N : ℕ) (κ : ℝ≥0), κ < 1 ∧ Icc lo hi ⊆ openBoxOne ∧
      (∀ x ∈ boxSet 0 0, poincareAngZero^[N] x ∈ cellClass '' Icc lo hi) ∧
      ∃ g : (Fin 3 → ℝ) → (Fin 3 → ℝ), MapsTo g (Icc lo hi) (Icc lo hi) ∧
        LipschitzOnWith κ g (Icc lo hi) ∧
        ∀ p ∈ Icc lo hi, poincareAngZero (cellClass p) = cellClass (g p)

/-- **Every point of the second big cell enters `𝒟_out` within three steps** (Table 16.1, rows `𝒟₂`
and `𝒟₃`, and Figure 16.2). The book: "`F₂(𝒟₂) = τ(𝔦(𝒟₂)) = τ(𝒟₂) ⊂ 𝒟₃`" (TeX 12616–12620; "`θ₂ ∈
[-π/3, 0]` holds on `𝒟₂`"), "`F₃(𝒟₃) = τ(𝔦(𝒟₃)) = τ(𝒟₄)`, which is a subset of the first cell"
(TeX 12629–12638), and "We have that `F²𝒟₃ ⊂ 𝒟₀₀`, as shown by the calculation in Figure 16.2"
(TeX 12640–12665). Hence a point of `𝒟₂` reaches `𝒟₀₀` after three steps and a point of `𝒟₃` after
two; this is the form used here, for every point of the second big cell (open cell and top face
`𝒞₂(ζ², 0, 2)`), without the split `𝒟₂ | 𝒟₃` along `∂_{A,ζ²}`.

Sampling (30,000 points of the second cell, including its top face and points within `10⁻⁹` of
every face): no point needs more than three steps; the shares of `n = 1, 2, 3` depend on the
sampling weights (64/34/2% here, 70/28/1.6% in an independent check of about 150,000 points).
The smallest margin, `1.1 - π/3 ≈ 0.053` to the inner edge `θ₂ = 1.1` of `𝒟₀₀`, is approached as
`r₂ → 0`, `ψ → π`, `θ₂ ↓ -π/3`, where all three steps are changes of representative
(`t_sw → 0`) near the class of `(1, 0, 0)`; a certificate needs an asymptotic expansion there.

Certification: direct enclosure of `F`, `F²`, `F³` on a subdivision of the cell; the switch of each
piece (to `1`, staying in the second cell, or to `ζ`, entering the first) from the signs of the
switching cubics; near `θ₂ = -π` the first step is a change of representative (`t_sw → 0`). -/
def CellTwoEntersDOut : Prop :=
  ∀ x ∈ cellTwoSet, ∃ n ≤ 3, poincareAngZero^[n] x ∈ boxSet 0 0

/-- **The subclaims** `subclaim_{ij}` (TeX 12677–12726, Figures 16.3–16.4: "`F₁(𝒟_{1,ij}) ⊂
∪_{k,ℓ} 𝒟_{kℓ}`, where the union runs over `(k, ℓ) ≺ (i, j)`"), merged with the row `𝒟₄` of Table
16.1 (TeX 12612–12615: "`F₄(𝒟₄) = τ(𝔦(𝒟₄)) = τ(𝒟₃)`, which is contained in the second big cell"):
for `(i, j) ∉ {(0, 0), (2, 2)}`, every point of the box `𝒟_{ij}` that is not in the second big cell
is mapped into the second big cell (it lies in `𝒟₄`) or into a box `𝒟_{kℓ}` with `(k, ℓ) ≺ (i, j)`
(it lies in `𝒟_{1,ij}` or on a face). The book's subclaims are about `𝒟_{1,ij} = 𝒟₁ ∩ 𝒟_{ij}`;
here the box is the whole `𝒟_{ij}`, so that the curved part `𝒟₁` is not needed.

Sampling (8,000 points per box, a third of them on or within `10⁻⁹` of a face): no violation
(inventory C16.3: 4,000 points per box of `𝒟_{1,ij}`).

Certification: direct enclosure of `F` on a subdivision of each box. Near the surfaces where the
switch changes (`∂_res`, `∂_B`, where the target changes from a smaller box to the second cell) both
candidate switches are enclosed and both images checked. An independent check found that `∂_A`
(three positive roots of `χ_{A,0}`) meets only the excluded box `𝒟₂₂`, so no other box needs it,
and that the smallest margin is `2.2 - 2π/3 ≈ 0.106`, in the box `𝒟₀₁` near the corner
`r₂ → 0`, `ψ → π/3`, `θ₂ → 1.1` (where `t_sw → 0`; a local expansion is needed there). The target
"second cell or a smaller box" is not a closed set, so near `∂_res` an enclosure must switch
between the charts of the two targets. (Theorem 16.4.1, in a later layer, needs the table for the
branch maps and cluster points; this pointwise statement about the honest map may then need a
version with closed targets or branch maps.) -/
def BoxSubclaims : Prop :=
  ∀ i j : Fin 3, (i, j) ≠ (0, 0) → (i, j) ≠ (2, 2) → ∀ x ∈ boxSet i j, x ∉ cellTwoSet →
    poincareAngZero x ∈ cellTwoSet ∨
      ∃ k l : Fin 3, BoxLexLt k l i j ∧ poincareAngZero x ∈ boxSet k l

end TriFuller

end SmoothedPolygons
