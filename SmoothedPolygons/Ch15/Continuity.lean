module

public import SmoothedPolygons.Ch15.SmallerCells

/-!
# Chapter 15: continuity of the first switching time and of the cell maps (§15.1–§15.2)

The continuity claims of Hales–Vajjha, *Packings of Smoothed Polygons*, §15.1–§15.2:

* on a big open cell the first switching time, hence the Poincaré map, is continuous off the loci
  `Δ_{A,0} = 0`, `Δ_{B,1} = 0`, `res_AB = 0` (TeX 12139–12143; gap G15.8);
* the dynamics extends continuously from the interior of the first big cell to its top face
  `𝒞₂(ζ, 0, 2)` (TeX 12233–12235) and to the closed 2-cell `𝒞₂(ζ, 1, 1)` on the front and back faces
  (TeX 12268–12276, at its nondegenerate points), and from the interior of the second big cell to
  its top face `𝒞₂(ζ², 0, 2)` "with exceptional discontinuities" (TeX 12239–12245);
* the root-based maps `F_A` on `𝒞₂^A` and `F_B` on the closure of `𝒞₂^B` are continuous
  (TeX 12419–12422).

## Proofs

One tool serves all of them: a simple real root of a real polynomial depends continuously on the
coefficients (intermediate value theorem on a small interval around the root, where the derivative
has a fixed sign), and a real root cannot appear in a compact interval away from the roots of the
limit polynomial (uniform convergence of the polynomials on compacts). This general lemma belongs in
`Basic/` (it is not in Mathlib in this form). With it, the least positive sign change of the
switching cubics (the first switching time, `firstSwitchTime_topFaceTwo`, `topFaceOne_switching`)
varies continuously wherever the relevant roots are simple, distinct and nonzero, and `classOf` is
continuous on the section (`continuousOn_classOf`).
-/

@[expose] public section

namespace SmoothedPolygons

open Complex Set Filter Topology Polynomial
open scoped Real

namespace TriFuller

/-- **Where the first switching time can be discontinuous** (TeX 12139–12143): "The first switching
time `t_sw` is a discontinuous function on the cell. The discontinuities can only appear along the
loci `Δ_{A,0} = 0`, `Δ_{B,1} = 0` and `res_AB = 0`." On a big open cell, off these loci, `t_sw` and
the Poincaré map are continuous.

Proof route: off the loci the positive roots of `χ_{A,0}` and `χ_{B,1}` are simple and distinct and
none is `0`, so each is a sign change and the least of them is `t_sw`; simple real roots depend
continuously on the coefficients, which are continuous in `p`, and no root can enter `(0, ∞)`
through `0` (`χ_{A,0}(0) ≠ 0 ≠ χ_{B,1}(0)`) or through a complex pair (`Δ ≠ 0`); finally
`F = z(t_sw)` and `classOf` is continuous (`continuousOn_classOf`). (Gap G15.8: on the faces of
the cells the switching time may tend to `0`; see Proposition 15.2.2.) -/
theorem continuousAt_firstSwitchTime_of_ne_zero :
    (∀ p ∈ openBoxOne, discrA ζ (cellPoint p) ≠ 0 → discrB ζ (cellPoint p) ≠ 0 →
      resAB ζ (cellPoint p) ≠ 0 →
      ContinuousAt (fun q ↦ firstSwitchTime (cellPoint q)) p ∧
        ContinuousAt (fun q ↦ poincareAngZero (cellClass q)) p) ∧
    ∀ p ∈ openBoxTwo, discrA (ζ ^ 2) (cellPoint p) ≠ 0 → discrB (ζ ^ 2) (cellPoint p) ≠ 0 →
      resAB (ζ ^ 2) (cellPoint p) ≠ 0 →
      ContinuousAt (fun q ↦ firstSwitchTime (cellPoint q)) p ∧
        ContinuousAt (fun q ↦ poincareAngZero (cellClass q)) p := by
  sorry

/-- "The first switching time is then a continuous function on the cell. If we identify this cell
with the top face `θ₂ = π` of the first three-cell `𝒞₃(ζ)⁰`, then the dynamical system extends
continuously from the interior of the first big cell to its top face" (TeX 12233–12235).

Proof route: near the top face `χ_B = t (y₂ + y₁ t/2 + t²/12) > 0` for `t > 0` (`y₂ ≥ 0`, `y₁ > 0`),
and the unique positive root of `χ_{A,0}` is simple (`topFaceOne_switching`), so it varies
continuously and no other positive root appears nearby. -/
theorem continuousWithinAt_topFaceOne {p : Fin 3 → ℝ} (hp : p ∈ topFaceOne) :
    ContinuousWithinAt (fun q ↦ firstSwitchTime (cellPoint q)) (openBoxOne ∪ topFaceOne) p ∧
      ContinuousWithinAt (fun q ↦ poincareAngZero (cellClass q)) (openBoxOne ∪ topFaceOne) p := by
  sorry

/-- "If we attach each point `(r₂, ψ, θ₂)` of this cell to the point on the front and back boundary
faces `ψ ∈ {0, π}` of the first 3-cell with the same coordinates `(r₂, ψ, θ₂)`, then the dynamical
system on the interior of the 3-cell extends continuously to the front and back faces, in agreement
with the dynamics on the 2-cell `𝒞₂(ζ)`" (TeX 12268–12276), at the points of the relative interior
where the reduced polynomials `χ_{A,1}`, `χ_{B,1}` have simple roots and no common root. Some
restriction is forced: the book claims continuity on the whole 2-cell, which fails where the map of
the 2-cell itself is discontinuous. These hypotheses are sufficient, not minimal; the book's
"continuous extension" elsewhere on the 2-cell is the subject of Proposition 15.3.2.

Proof route: near such a face point, in the open cell, `χ_A` has a root near `0` that is negative
(`χ_A(0) = -(√3/2) x₃ > 0` and `χ_A'(0) > 0`) and two roots near those of `χ_{A,1}`; `χ_{B,1}` is
near the face's `χ_{B,1}`; the least positive sign change varies continuously. -/
theorem continuousWithinAt_frontBackOne {p : Fin 3 → ℝ} (hp : p ∈ frontBackOne) (hr : 0 < p 0)
    (hθ : p 2 ∈ Ioo (π / 3) π) (hA : discrA ζ (cellPoint p) ≠ 0)
    (hB : discrB ζ (cellPoint p) ≠ 0) (hres : resAB ζ (cellPoint p) ≠ 0) :
    ContinuousWithinAt (fun q ↦ poincareAngZero (cellClass q)) (openBoxOne ∪ frontBackOne) p := by
  sorry

/-- **`F_A` and `F_B` are continuous** (TeX 12419–12422): "The map `F` is discontinuous along the
discriminant locus `Δ_{A,0} = 0`. However, the first switching time and the Fuller–Poincaré map `F`
extend continuously to give `F_A` with domain `𝒞₂^A` and `F_B` with domain `𝒞₂^B`": `F_A` is
continuous on the closed part `𝒞₂^A = {Δ_{A,0} ≥ 0}` (the least positive root tends to the double
root at `Δ_{A,0} = 0`) and `F_B` on the closure `{Δ_{A,0} ≤ 0}` of `𝒞₂^B` in the face, both with
values in the section.

Proof route: `t_B = -6 y₁` is continuous; on `{Δ_{A,0} > 0}` the least positive root is simple, and
at `Δ_{A,0} = 0` both positive roots tend to the double root (continuity of the roots of a cubic as
a multiset); at the double root `t₀ ≤ t_B` the controls `ζ²` and `1` tie and maximize, so `F_A`
lands on a wall. -/
theorem continuousOn_cellMapA_cellMapB :
    (∀ p ∈ topFaceTwoA, cellMapA (cellPoint p) ∈ sectionZero) ∧
      ContinuousOn (fun p ↦ classOf (cellMapA (cellPoint p))) topFaceTwoA ∧
      (∀ p ∈ topFaceTwo, discrA (ζ ^ 2) (cellPoint p) ≤ 0 →
        cellMapB (cellPoint p) ∈ sectionZero) ∧
      ContinuousOn (fun p ↦ classOf (cellMapB (cellPoint p)))
        {p | p ∈ topFaceTwo ∧ discrA (ζ ^ 2) (cellPoint p) ≤ 0} := by
  sorry

/-- "If we identify this `2`-cell with the top face `θ₂ = 0` of the second three-cell `𝒞₃(ζ²)⁰`,
then the dynamical system extends continuously from the interior of the second big cell to its top
face (with exceptional discontinuities, where the dynamical system is already discontinuous on
`𝒞₂(ζ², 0, 2)`)" (TeX 12239–12245): at the points of the face where `Δ_{A,0} ≠ 0`, since the map
of the face (`F_A` where `Δ_{A,0} > 0`, `F_B` where `Δ_{A,0} ≤ 0`) is discontinuous only on
`{Δ_{A,0} = 0}`. Where `Δ_{A,0} > 0` the least positive root of `χ_{A,0}` lies below `t_B`
(`firstSwitchTime_topFaceTwo`), so a root of `χ_{A,0}` at `t_B` is a larger root and does not
change the switch.

Proof route: in the open cell near the face, `χ_{B,1} = -(y₂ + y₁ t/2 + t²/12)` (`y₂ < 0` small) has
a positive root near `t_B` and a negative one near `0`; the roots of `χ_{A,0}` are near those of the
face. -/
theorem continuousWithinAt_topFaceTwo {p : Fin 3 → ℝ} (hp : p ∈ topFaceTwo)
    (hA : discrA (ζ ^ 2) (cellPoint p) ≠ 0) :
    ContinuousWithinAt (fun q ↦ poincareAngZero (cellClass q)) (openBoxTwo ∪ topFaceTwo) p := by
  sorry

end TriFuller

end SmoothedPolygons
