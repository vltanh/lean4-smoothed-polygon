module

public import SmoothedPolygons.Ch15.CellCoordinates
public import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Chapter 16: the numerical facts behind the global basin theorem (Table 16.1)

The proof of Theorem 16.1.1 (`thm:basin`) of Hales–Vajjha, *Packings of Smoothed Polygons*
(TeX 12511–12744) rests on containments of the Fuller–Poincaré map that the book computes
numerically in Mathematica and shows in Figures 16.1–16.4 (Table 16.1, "Upper triangular structure
of the Fuller–Poincaré map on the two big cells"). This file states them as three named
propositions, the explicit hypotheses of `theorem16_1_1` (`SmoothedPolygons/Ch16/GlobalBasin.lean`).
All three are proved, without computer assistance (`dOutContracts`, `cellTwoEntersDOut`,
`boxSubclaims`; the unconditional theorems are in `SmoothedPolygons/Ch16/BasinFacts.lean`):

* `DOutContracts`: `F(𝒟_out) ⊆ 𝒟_out` (the row `𝒟_out` of Table 16.1, Figure 16.1, TeX 12592–12607)
  and a contraction to `q_out` inside `𝒟_out` (the book: "The forward iterates `F₁^k(𝒟_out)` quickly
  shrink toward `q_out`", unproved; REPORT.md, E78);
* `CellTwoEntersDOut`: every point of the second big cell enters `𝒟_out` within three steps (the
  rows `𝒟₂` and `𝒟₃`, TeX 12614–12620, 12629–12638, and `F²𝒟₃ ⊂ 𝒟₀₀`, Figure 16.2, TeX
  12640–12665);
* `BoxSubclaims`: the subclaims `subclaim_{ij}` (TeX 12680–12726, Figures 16.3–16.4), with the row
  `𝒟₄` (TeX 12612–12615) merged in: from a box `𝒟_{ij}`, `(i, j) ∉ {(0,0), (2,2)}`, the map goes to
  the second big cell or to a lexicographically smaller box.

## The regions

The boxes `𝒟_{ij} = {r₂ ∈ [0, 1], ψ ∈ [a_i, a_{i+1}], θ₂ ∈ [b_{j+1}, b_j]}` of the first big cell
(TeX 12526–12534), with `(a₀, …, a₃) = (0, π/3, 2π/3, π)` and `(b₀, …, b₃) = (π, π - 1.1, 1.1, 0)`
(`cellBox`; the book prints `θ₂ ∈ [b_{i+1}, b_i]`, an index slip with one reading), as sets of
`Ξ_{𝒲,0}/V_T` (`boxSet i j`); `𝒟_out = 𝒟₀₀` and `𝒟_in ⊆ 𝒟₂₂` (TeX 12680 swaps the two; REPORT.md,
E76). The second big cell is `cellTwoSet` (first control `ζ²`, `x₃ < 0`, including its top face
`θ₂ = 0`). These are the regions of Table 16.1 that are boxes; the curved parts `𝒟₀, 𝒟₁, 𝒟₄`
and the split `𝒟₂ | 𝒟₃` (`SmoothedPolygons/Ch15/Involution.lean`) are not needed:
* the book's `𝒟_in = 𝒟₁ ∩ 𝒟₂₂` is replaced by the whole box `𝒟₂₂`; its row ("can be anything") is
  unchanged, and `𝒟₀ ⊂ 𝒟₂₂` (the book's "`𝒟₀ ⊂ 𝒟_in`") is no longer used;
* the rows `𝒟₄` and `𝒟₁ ∖ 𝒟_in`: a point of a box `𝒟_{ij}` of the first cell goes either to the
  second cell (it lies in `𝒟₄`) or to a smaller box (the book's `subclaim_{ij}` on `𝒟_{1,ij}`). This
  form of `BoxSubclaims` (whole boxes, with target "the second cell or a smaller box") replaces the
  book's argument by exclusion for the last row (`𝒟₀ ⊂ 𝒟_in`, `𝒟₄ ⊂ F(𝒟₂₂)` and the injectivity of
  `F`, REPORT.md, E79). That no orbit re-enters `𝒟₂₂` (the column `𝒟_in` of Table 16.1, the
  book's step (b)) is proved from `DOutContracts` by the time reversal of the book's step (a)
  (`theorem16_1_1`);
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
within `10⁻⁹` of every face (an earlier sampling of the book's regions and new runs for this
formulation; no violation).

## The proofs

The book's "boundary method" (TeX 12577–12587: `F_i(∂𝒟) ⊂ 𝒟̃` convex suffices when `𝒟` is a closed
ball) needs `F_i` injective on `𝒟` and invariance of domain (REPORT.md, E77), and the images of the
curved faces. The facts here are stated pointwise, at every point of the closed boxes, and are
proved without it. **Departure from the paper** (the user's decision: proofs without computer
assistance, the computation kept as a Python reference in `numerics/`): the book reads the facts
off computer plots; the formalization proves them analytically, from the root structure of the
explicit switching cubics, exact identities with sign-definite terms and explicit
inequalities, with no local or asymptotic expansion at the faces where the switching time tends
to `0`:
* `dOutContracts` (`SmoothedPolygons/Ch16/DOutContraction.lean`), with the witnesses
  `B = Icc boxLo boxHi ≈ [0.22, 0.30] × [0.080, 0.199] × [2.688, 3.009]`, `N = 2`, `κ = 3/4`
  and `g = gmap`; its Lipschitz bound rests on bounds of the derivatives on the single box `B`,
  by a short argument written out by hand (`SmoothedPolygons/Ch16/DOutDerivativeBounds.lean`);
* `cellTwoEntersDOut` (`SmoothedPolygons/Ch16/CellTwoEntersDOut.lean`);
* `boxSubclaims` (`SmoothedPolygons/Ch16/BoxSubclaims.lean`).
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
`θ₂ ∈ [b_{j+1}, b_j]` (corrected index; the book prints `θ₂ ∈ [b_{i+1}, b_i]`, REPORT.md, E76). -/
def cellBox (i j : Fin 3) : Set (Fin 3 → ℝ) :=
  {p | p 0 ∈ Icc 0 1 ∧ p 1 ∈ Icc (basinA i.castSucc) (basinA i.succ) ∧
    p 2 ∈ Icc (basinB j.succ) (basinB j.castSucc)}

/-- The box `𝒟_{ij}` as a set of `Ξ_{𝒲,0}/V_T`. `boxSet 0 0` is `𝒟_out = 𝒟₀₀` and `boxSet 2 2` is
the box `𝒟₂₂ ⊇ 𝒟_in` (TeX 12535–12537). -/
noncomputable def boxSet (i j : Fin 3) : Set XiW0Quot := cellClass '' cellBox i j

/-- The lexicographic order on box indices: `(k, ℓ) ≺ (i, j)` iff `k < i`, or `k = i` and `ℓ < j`
(TeX 12686–12691). -/
def BoxLexLt (k l i j : Fin 3) : Prop := k < i ∨ (k = i ∧ l < j)

private lemma l5e_basinA_vals :
    basinA 0 = 0 ∧ basinA 1 = π / 3 ∧ basinA 2 = 2 * π / 3 ∧ basinA 3 = π := by
  simp [basinA]

private lemma l5e_basinB_vals :
    basinB 0 = π ∧ basinB 1 = π - 1.1 ∧ basinB 2 = 1.1 ∧ basinB 3 = 0 := by
  simp [basinB]

/-- Membership in a box, with the breakpoints evaluated. -/
private lemma l5e_mem_cellBox_iff (i j : Fin 3) (p : Fin 3 → ℝ) :
    p ∈ cellBox i j ↔ p 0 ∈ Icc 0 1 ∧ p 1 ∈ Icc (basinA i.castSucc) (basinA i.succ) ∧
      p 2 ∈ Icc (basinB j.succ) (basinB j.castSucc) := Iff.rfl

/-- Every box lies in the closed first big cell (the breakpoints lie in `[0, π]`). -/
private lemma l5e_cellBox_subset (i j : Fin 3) : cellBox i j ⊆ closedBoxOne := by
  obtain ⟨a0, a1, a2, a3⟩ := l5e_basinA_vals
  obtain ⟨b0, b1, b2, b3⟩ := l5e_basinB_vals
  have hpi := Real.pi_gt_three
  intro p hp
  rw [l5e_mem_cellBox_iff] at hp
  obtain ⟨h0, ⟨h1, h1'⟩, ⟨h2, h2'⟩⟩ := hp
  refine ⟨h0, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · fin_cases i <;> simp_all <;> linarith
  · fin_cases i <;> simp_all <;> linarith
  · fin_cases j <;> simp_all <;> linarith
  · fin_cases j <;> simp_all <;> linarith

/-- The nine boxes cover the closed first big cell. -/
theorem closedBoxOne_eq_iUnion_cellBox : closedBoxOne = ⋃ i, ⋃ j, cellBox i j := by
  obtain ⟨a0, a1, a2, a3⟩ := l5e_basinA_vals
  obtain ⟨b0, b1, b2, b3⟩ := l5e_basinB_vals
  have hpi := Real.pi_gt_three
  refine Subset.antisymm (fun p hp ↦ ?_) (iUnion_subset fun i ↦ iUnion_subset fun j ↦
    l5e_cellBox_subset i j)
  obtain ⟨h0, ⟨h1, h1'⟩, ⟨h2, h2'⟩⟩ := hp
  simp only [mem_iUnion]
  -- the `ψ`-index
  obtain ⟨i, hi⟩ : ∃ i : Fin 3, p 1 ∈ Icc (basinA i.castSucc) (basinA i.succ) := by
    rcases le_total (p 1) (π / 3) with h | h
    · exact ⟨0, by simp [a0, a1, h1, h]⟩
    rcases le_total (p 1) (2 * π / 3) with h' | h'
    · exact ⟨1, by simp [a1, a2, h, h']⟩
    · exact ⟨2, by simp [a2, a3, h', h1']⟩
  -- the `θ₂`-index
  obtain ⟨j, hj⟩ : ∃ j : Fin 3, p 2 ∈ Icc (basinB j.succ) (basinB j.castSucc) := by
    rcases le_total (π - 1.1) (p 2) with h | h
    · exact ⟨0, by simp [b0, b1, h2', h]⟩
    rcases le_total 1.1 (p 2) with h' | h'
    · exact ⟨1, by simp [b1, b2, h, h']⟩
    · exact ⟨2, by simp [b2, b3, h2, h']⟩
  exact ⟨i, j, h0, hi, hj⟩

/-- The time reversal exchanges `𝒟₀₀ = 𝒟_out` and `𝒟₂₂` (TeX 12729–12732: `τ(𝒟_in) ⊆ 𝒟_out`):
`τ(r₂, ψ, θ₂) = (r₂, π - ψ, π - θ₂)` maps `ψ ∈ [0, π/3]`, `θ₂ ∈ [π - 1.1, π]` onto `ψ ∈ [2π/3, π]`,
`θ₂ ∈ [0, 1.1]` (`cellClass_cellTau`). -/
theorem tauZero_image_boxSet :
    tauZero '' boxSet 0 0 = boxSet 2 2 ∧ tauZero '' boxSet 2 2 = boxSet 0 0 := by
  obtain ⟨a0, a1, a2, a3⟩ := l5e_basinA_vals
  obtain ⟨b0, b1, b2, b3⟩ := l5e_basinB_vals
  have hpi := Real.pi_gt_three
  -- `τ` on classes is `cellTau` on coordinates, on the closed first cell
  have himage : ∀ i j : Fin 3,
      tauZero '' boxSet i j = cellClass '' (cellTau '' cellBox i j) := by
    intro i j
    rw [boxSet, image_image, image_image]
    refine image_congr fun p hp ↦ ?_
    have hp' := l5e_cellBox_subset i j hp
    exact (cellClass_cellTau ⟨hp'.1, hp'.2.1, ⟨by linarith [hp'.2.2.1], hp'.2.2.2⟩⟩).2.symm
  -- `cellTau` is `(r₂, ψ, θ₂) ↦ (r₂, π - ψ, π - θ₂)` there, and exchanges the two boxes
  have hform : ∀ p : Fin 3 → ℝ, 0 ≤ p 2 → cellTau p = ![p 0, π - p 1, π - p 2] := by
    intro p hp
    simp [cellTau, hp]
  have hmaps : ∀ p ∈ cellBox 0 0, cellTau p ∈ cellBox 2 2 := by
    intro p hp
    obtain ⟨h0, ⟨h1, h1'⟩, ⟨h2, h2'⟩⟩ := hp
    simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one, a0, a1, b0, b1] at h1 h1' h2 h2'
    rw [hform p (by linarith)]
    refine ⟨by simpa using h0, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
      simp [a2, a3, b2, b3] <;> linarith
  have hmaps' : ∀ p ∈ cellBox 2 2, cellTau p ∈ cellBox 0 0 := by
    intro p hp
    obtain ⟨h0, ⟨h1, h1'⟩, ⟨h2, h2'⟩⟩ := hp
    simp only [show (2 : Fin 3).castSucc = 2 from rfl, show (2 : Fin 3).succ = 3 from rfl, a2, a3,
      b2, b3] at h1 h1' h2 h2'
    rw [hform p h2]
    refine ⟨by simpa using h0, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
      simp [a0, a1, b0, b1] <;> linarith
  have hinv : ∀ p : Fin 3 → ℝ, 0 ≤ p 2 → p 2 ≤ π → cellTau (cellTau p) = p := by
    intro p h h'
    rw [hform p h, hform _ (by simp; linarith)]
    ext k
    fin_cases k <;> simp
  have hsurj : ∀ {S T : Set (Fin 3 → ℝ)}, (∀ p ∈ S, cellTau p ∈ T) →
      (∀ p ∈ T, cellTau p ∈ S) → (∀ p ∈ T, cellTau (cellTau p) = p) →
      cellTau '' S = T := by
    intro S T hST hTS hTT
    refine Subset.antisymm (image_subset_iff.2 hST) fun p hp ↦ ⟨cellTau p, hTS p hp, hTT p hp⟩
  have h00 : ∀ p ∈ cellBox 0 0, cellTau (cellTau p) = p := fun p hp ↦
    hinv p ((l5e_cellBox_subset 0 0 hp).2.2.1) ((l5e_cellBox_subset 0 0 hp).2.2.2)
  have h22 : ∀ p ∈ cellBox 2 2, cellTau (cellTau p) = p := fun p hp ↦
    hinv p ((l5e_cellBox_subset 2 2 hp).2.2.1) ((l5e_cellBox_subset 2 2 hp).2.2.2)
  refine ⟨?_, ?_⟩
  · rw [himage, hsurj hmaps hmaps' h22, boxSet]
  · rw [himage, hsurj hmaps' hmaps h00, boxSet]

/-! ### The named numerical facts -/

/-- **`F` maps `𝒟_out` into itself and contracts it to `q_out`** (Table 16.1, row `𝒟_out`; Figure
16.1, TeX 12592–12607: "We compute the interval containment `F₁(𝒟_out) ⊂ 𝒟_out` by the boundary
method. … The forward iterates `F₁^k(𝒟_out)` quickly shrink toward `q_out`"). The book proves only
the containment and the local stability of `q_out` (Lemma 13.5.5), which do not give convergence of
every point of `𝒟_out` (REPORT.md, E78); the contraction repairs this:
* `F(𝒟₀₀) ⊆ 𝒟₀₀`;
* there are a box `B = [lo, hi]` in the open first cell, `N` and `κ < 1` with `F^N(𝒟₀₀) ⊆ B`, and a
  map `g` of `B` into itself, `κ`-Lipschitz (sup norm of the coordinates `(r₂, ψ, θ₂)`), which is
  `F` in coordinates on `B`.

Proved: `dOutContracts` (`SmoothedPolygons/Ch16/DOutContraction.lean`), with
`B = Icc boxLo boxHi ≈ [0.22, 0.30] × [0.080, 0.199] × [2.688, 3.009]`, `N = 2`, `κ = 3/4` and
`g = gmap` (the cell coordinates of `ζ F(z)`). `N ≥ 2` is forced: `F(𝒟₀₀)` lies in no compact box
of the open cell, because `𝒟₀₀` contains the edge `r₂ = 0`, `θ₁ = θ₂ - ψ ∈ [0.9944, π/3)`, where
the first control is `1`, and at interior points near it the switching time tends to `0` and the
image has `r₂` near `0`; one step fails broadly (for instance `F(1, 1/2, 5/2)` has `θ₂ ≈ 2.7817`).

Departure from the paper: the book reads the containment off a computer calculation by the boundary
method and the shrinking of the iterates off Figure 16.1; the formalization proves both
analytically (`mapsTo_boxSet_zero_zero`, `iterate_two_mem`, `lipschitzOnWith_gmap`). -/
def DOutContracts : Prop :=
  MapsTo poincareAngZero (boxSet 0 0) (boxSet 0 0) ∧
    ∃ (lo hi : Fin 3 → ℝ) (N : ℕ) (κ : ℝ≥0), κ < 1 ∧ Icc lo hi ⊆ openBoxOne ∧
      (∀ x ∈ boxSet 0 0, poincareAngZero^[N] x ∈ cellClass '' Icc lo hi) ∧
      ∃ g : (Fin 3 → ℝ) → (Fin 3 → ℝ), MapsTo g (Icc lo hi) (Icc lo hi) ∧
        LipschitzOnWith κ g (Icc lo hi) ∧
        ∀ p ∈ Icc lo hi, poincareAngZero (cellClass p) = cellClass (g p)

/-- **Every point of the second big cell enters `𝒟_out` within three steps** (Table 16.1, rows `𝒟₂`
and `𝒟₃`, and Figure 16.2). The book: "`F₂(𝒟₂) = τ(𝔦(𝒟₂)) = τ(𝒟₂) ⊂ 𝒟₃`" (TeX 12614–12620; "`θ₂ ∈
[-π/3, 0]` holds on `𝒟₂`"), "`F₃(𝒟₃) = τ(𝔦(𝒟₃)) = τ(𝒟₄)`, which is a subset of the first cell"
(TeX 12629–12638), and "We have that `F²𝒟₃ ⊂ 𝒟₀₀`, as shown by the calculation in Figure 16.2"
(TeX 12640–12665). Hence a point of `𝒟₂` reaches `𝒟₀₀` after three steps and a point of `𝒟₃` after
two; this is the form used here, for every point of the second big cell (open cell and top face
`𝒞₂(ζ², 0, 2)`), without the split `𝒟₂ | 𝒟₃` along `∂_{A,ζ²}`.

Proved: `cellTwoEntersDOut` (`SmoothedPolygons/Ch16/CellTwoEntersDOut.lean`). The smallest
margin, `1.1 - π/3 ≈ 0.053` to the inner edge `θ₂ = 1.1` of `𝒟₀₀`, is approached as `r₂ → 0`,
`ψ → π`, `θ₂ ↓ -π/3`, where all three steps are changes of representative (`t_sw → 0`); the proof
decides every case by the signs of the switching functions, not by margins.

Departure from the paper: the book reads `F²𝒟₃ ⊂ 𝒟₀₀` off a Mathematica plot and the rows `𝒟₂`,
`𝒟₃` from the involution; the formalization proves the statement analytically, without the split
`𝒟₂ | 𝒟₃` and without the involution. -/
def CellTwoEntersDOut : Prop :=
  ∀ x ∈ cellTwoSet, ∃ n ≤ 3, poincareAngZero^[n] x ∈ boxSet 0 0

/-- **The subclaims** `subclaim_{ij}` (TeX 12680–12726, Figures 16.3–16.4: "`F₁(𝒟_{1,ij}) ⊂
∪_{k,ℓ} 𝒟_{kℓ}`, where the union runs over `(k, ℓ) ≺ (i, j)`"), merged with the row `𝒟₄` of Table
16.1 (TeX 12612–12615: "`F₄(𝒟₄) = τ(𝔦(𝒟₄)) = τ(𝒟₃)`, which is contained in the second big cell"):
for `(i, j) ∉ {(0, 0), (2, 2)}`, every point of the box `𝒟_{ij}` that is not in the second big cell
is mapped into the second big cell (it lies in `𝒟₄`) or into a box `𝒟_{kℓ}` with `(k, ℓ) ≺ (i, j)`
(it lies in `𝒟_{1,ij}` or on a face). The book's subclaims are about `𝒟_{1,ij} = 𝒟₁ ∩ 𝒟_{ij}`;
here the box is the whole `𝒟_{ij}`, so that the curved part `𝒟₁` is not needed.

Proved: `boxSubclaims` (`SmoothedPolygons/Ch16/BoxSubclaims.lean`). The target "second cell or a
smaller box" is not a closed set; the proof decides it pointwise, by the sign of `Im z₃` before the
switch to `1`.

Departure from the paper: the book reads the subclaims off computer plots by the boundary method
(Figures 16.3–16.4); the formalization proves them analytically, by the root structure of the
switching cubics and exact identities with sign-definite terms. -/
def BoxSubclaims : Prop :=
  ∀ i j : Fin 3, (i, j) ≠ (0, 0) → (i, j) ≠ (2, 2) → ∀ x ∈ boxSet i j, x ∉ cellTwoSet →
    poincareAngZero x ∈ cellTwoSet ∨
      ∃ k l : Fin 3, BoxLexLt k l i j ∧ poincareAngZero x ∈ boxSet k l

end TriFuller

end SmoothedPolygons
