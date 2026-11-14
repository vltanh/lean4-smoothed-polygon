module

public import SmoothedPolygons.Ch15.CellCoordinates
public import Mathlib.Algebra.CubicDiscriminant
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Chapter 15: switching polynomials, the smaller cells and Proposition 15.2.2 (§15.1–§15.2)

The switching functions of the cells of Hales–Vajjha, *Packings of Smoothed Polygons*, §15.1
(TeX 12086–12143) and the smaller cells of §15.2 ("Smaller cells", TeX 12209–12314):

* the switching functions `χ_A = χ^u_{u-1}` (switch from the first control `u` to `1`) and
  `χ_B = χ^u_{u-ū}` (switch from `u` to `ū`) as real cubics in `t` (`chiA`, `chiB`; explicit
  coefficients `chiA_chiB_eq`), the multiplicities `m_A`, `m_B` of the root `t = 0`, the reduced
  polynomials `χ_{A,m_A} = χ_A/t^{m_A}`, `χ_{B,m_B} = χ_B/t^{m_B}`, their discriminants
  `Δ_{A,m_A}`, `Δ_{B,m_B}` and the resultant `res_AB` (Mathlib's `Polynomial.discr`, normalized so
  that a real polynomial with only real roots has `Δ ≥ 0`, and `Polynomial.resultant`);
* on the big open cells `(m_A, m_B) = (0, 1)` (TeX 12137–12138);
* the 2-cells `𝒞₂(ζ, 0, 2)` (`topFaceOne`, `θ₂ = π`), `𝒞₂(ζ², 0, 2)` (`topFaceTwo`, `θ₂ = 0`) with
  its parts `𝒞₂^A = {Δ_{A,0} ≥ 0}` and `𝒞₂^B = {Δ_{A,0} < 0}` (TeX 12411–12422), the closed 2-cells
  `𝒞₂(ζ, 1, 1)` (`frontBackOne`, `z₃ = 0`, `θ₂ ∈ [π/3, π]`) and `𝒞₂(ζ², 1, 1)` (`frontBackTwo`,
  `θ₂ ∈ [-π, -π/3]`);
* the Descartes-rule facts on the 2-cells, the impossibility of `(m_A, m_B) = (0, 3)`;
* the **root-based cell maps** `F_A` and `F_B` of `𝒞₂(ζ², 0, 2)` (`cellMapA`, `cellMapB`) and where
  they agree with the Poincaré map `poincare`;
* Remark 15.2.1, Proposition 15.2.2 and the boundary maps on the red-shaded faces of Figure 15.1.

The continuity statements of §15.1–§15.2 (of the first switching time off the discriminant and
resultant loci, and of the dynamics up to the faces; of `F_A` and `F_B`) are in
`SmoothedPolygons/Ch15/Continuity.lean`.

## The semantic Poincaré map and the book's cell maps

`poincare` switches when the first control stops being optimal (`SmoothedPolygons/Ch13/Defs.lean`);
a tangency (a double root of a switching function at which the control stays optimal) is not a
switch. The book's maps on closed cells are continuous extensions from the interiors and may switch
at a tangency. On `𝒞₂(ζ², 0, 2)` the book's `F_A` uses the least positive root of `χ_{A,0}` on
all of `𝒞₂^A = {Δ_{A,0} ≥ 0}` (TeX 12413–12422), a double root on `{Δ_{A,0} = 0}`, where `poincare`
does not switch and agrees with `F_B` instead (`firstSwitchTime_topFaceTwo`; for example `r₂ = 1/2`,
`ψ = 1.0548151712321…`: double root `t = 1.30848`, switch at `6 r₁ sin ψ = 2.60943`; checklist,
line "L5 (Chapter 15)"). Both maps are stated here, with the agreement on `{Δ_{A,0} > 0}` and on
`{Δ_{A,0} ≤ 0}` respectively.

## Proofs

The switching functions are explicit cubics (`chiA_chiB_eq`, from (13.2.2)); on the cells their
coefficients have fixed signs, and Descartes's rule of signs (for a real cubic with all roots real,
the signs of the elementary symmetric functions) gives the root counts. On `𝒞₂(ζ², 0, 2)`, with
`z = (r₁ e^{-iψ}, r₂, -2 r₁ r₂ sin ψ)`, `χ_B = -t²(t/12 + y₁/2)` has the positive root
`t_B = -6 y₁ = 6 r₁ sin ψ`, and
`√3 χ_A = 3 r₁ r₂ S - (3/2) r₂ t - (r₁/4)(3C - √3 S) t² + (√3/12) t³` (`S = sin ψ`, `C = cos ψ`)
decreases on `(0, t_m)` and increases after its local minimum `t_m`. If `χ_{A,0}` has positive
roots, the least one is `≤ t_B`: otherwise `χ_A(t_B) > 0` and `χ_A'(t_B) < 0`, that is
`r₁² S (√3 S - C) > (2/9) r₂` and `r₁² S (8√3 S - 6C) < r₂`, which together force
`3.5 √3 S < 1.5 C`, while the first forces `√3 S > C`: a contradiction. Continuity of the switching
times (`SmoothedPolygons/Ch15/Continuity.lean`) is continuity of simple roots. The limits at faces
where the cell's control is not the first control are a semicontinuity argument: the control is
beaten at times arbitrarily close to `0` at the face point, hence (strict inequalities are open) at
nearby points.
-/

@[expose] public section

namespace SmoothedPolygons

open Complex Set Filter Topology Polynomial
open scoped Real

namespace TriFuller

/-! ### Switching functions as cubic polynomials -/

/-- The switching function `χ^u_d(t, z⁰) = RR(d, z₃(t, z⁰, u))/√3` (`switchingFunction`) as a real
cubic polynomial in `t`, from (13.2.2): coefficients `RR(d, -iu)/(6√3)` of `t³`,
`RR(d, z₁⁰)/(2√3)` of `t²`, `RR(d, z₂⁰)/√3` of `t` and `RR(d, z₃⁰)/√3`. -/
noncomputable def switchingCubic (u d : ℂ) (z : Fin 3 → ℂ) : Cubic ℝ :=
  ⟨RR d (-I * u) / (6 * √3), RR d (z 0) / (2 * √3), RR d (z 1) / √3, RR d (z 2) / √3⟩

/-- The cubic `switchingCubic` evaluates to the switching function. -/
theorem eval_switchingCubic (u d : ℂ) (z : Fin 3 → ℂ) (t : ℝ) :
    (switchingCubic u d z).toPoly.eval t = switchingFunction u d t z := by
  sorry

/-- `χ_A = χ^u_{u-1}` (TeX 12088–12091): the switching function from the first control `u` to the
control `1`. -/
noncomputable def chiA (u : ℂ) (z : Fin 3 → ℂ) : Cubic ℝ := switchingCubic u (u - 1) z

/-- `χ_B = χ^u_{u-ū}` (TeX 12088–12091): the switching function from the first control `u` to the
control `ū` (`ζ ↔ ζ²`). -/
noncomputable def chiB (u : ℂ) (z : Fin 3 → ℂ) : Cubic ℝ :=
  switchingCubic u (u - starRingEnd ℂ u) z

/-- `m_A`: the multiplicity of `t = 0` as a root of `χ_A` (TeX 12088–12090). -/
noncomputable def multA (u : ℂ) (z : Fin 3 → ℂ) : ℕ := (chiA u z).toPoly.rootMultiplicity 0

/-- `m_B`: the multiplicity of `t = 0` as a root of `χ_B`. -/
noncomputable def multB (u : ℂ) (z : Fin 3 → ℂ) : ℕ := (chiB u z).toPoly.rootMultiplicity 0

/-- The reduced switching polynomial `χ_{A,m_A} = χ_A/t^{m_A}` (TeX 12091). -/
noncomputable def chiARed (u : ℂ) (z : Fin 3 → ℂ) : ℝ[X] := (chiA u z).toPoly /ₘ X ^ multA u z

/-- The reduced switching polynomial `χ_{B,m_B} = χ_B/t^{m_B}` (TeX 12091). -/
noncomputable def chiBRed (u : ℂ) (z : Fin 3 → ℂ) : ℝ[X] := (chiB u z).toPoly /ₘ X ^ multB u z

/-- The discriminant `Δ_{A,m_A}` of `χ_{A,m_A}` (TeX 12092). -/
noncomputable def discrA (u : ℂ) (z : Fin 3 → ℂ) : ℝ := (chiARed u z).discr

/-- The discriminant `Δ_{B,m_B}` of `χ_{B,m_B}` (TeX 12092). -/
noncomputable def discrB (u : ℂ) (z : Fin 3 → ℂ) : ℝ := (chiBRed u z).discr

/-- The resultant `res_AB` of `χ_{A,m_A}` and `χ_{B,m_B}` (TeX 12134–12135). -/
noncomputable def resAB (u : ℂ) (z : Fin 3 → ℂ) : ℝ := (chiARed u z).resultant (chiBRed u z)

/-- The switching cubics explicitly, with `z_j = x_j + i y_j` (from (13.2.2); `ζ = -1/2 + (√3/2)i`):
* `χ_A` for `u = ζ`: `-t³/12 + (y₁ - √3 x₁) t²/4 + (y₂ - √3 x₂) t/2 + (y₃ - √3 x₃)/2`;
* `χ_B` for `u = ζ`: `t³/12 + y₁ t²/2 + y₂ t + y₃`;
* `χ_A` for `u = ζ²`: `t³/12 - (y₁ + √3 x₁) t²/4 - (y₂ + √3 x₂) t/2 - (y₃ + √3 x₃)/2`;
* `χ_B` for `u = ζ²`: `-(t³/12 + y₁ t²/2 + y₂ t + y₃)`. -/
theorem chiA_chiB_eq (z : Fin 3 → ℂ) :
    chiA ζ z = ⟨-1 / 12, ((z 0).im - √3 * (z 0).re) / 4, ((z 1).im - √3 * (z 1).re) / 2,
      ((z 2).im - √3 * (z 2).re) / 2⟩ ∧
    chiB ζ z = ⟨1 / 12, (z 0).im / 2, (z 1).im, (z 2).im⟩ ∧
    chiA (ζ ^ 2) z = ⟨1 / 12, -((z 0).im + √3 * (z 0).re) / 4, -((z 1).im + √3 * (z 1).re) / 2,
      -((z 2).im + √3 * (z 2).re) / 2⟩ ∧
    chiB (ζ ^ 2) z = ⟨-1 / 12, -(z 0).im / 2, -(z 1).im, -(z 2).im⟩ := by
  sorry

/-- On the big open cells `(m_A, m_B) = (0, 1)` (the notation `𝒞₃(u, 0, 1)⁰` of Definition 15.1.2;
"`χ_{A,0}(0) ≠ 0` and `χ_{B,1}(0) ≠ 0` on the big open cells", TeX 12137–12138): `χ_A(0) =
-(√3/2) x₃ ≠ 0` and `χ_B = t (±y₂ + …)` with `y₂ ≠ 0`. -/
theorem multA_multB_of_mem_openBox :
    (∀ p ∈ openBoxOne, multA ζ (cellPoint p) = 0 ∧ multB ζ (cellPoint p) = 1) ∧
      ∀ p ∈ openBoxTwo, multA (ζ ^ 2) (cellPoint p) = 0 ∧ multB (ζ ^ 2) (cellPoint p) = 1 := by
  sorry

/-! ### The smaller cells -/

/-- The 2-cell `𝒞₂(ζ, 0, 2)` (TeX 12223–12226): `x₃ ≠ 0` and `θ₂ = π`, with coordinates
`r₂ ∈ (0, 1)`, `ψ ∈ (0, π)`; the top face of the first big cell. -/
def topFaceOne : Set (Fin 3 → ℝ) := {p | p 0 ∈ Ioo 0 1 ∧ p 1 ∈ Ioo 0 π ∧ p 2 = π}

/-- The 2-cell `𝒞₂(ζ², 0, 2)` (TeX 12235–12238): `x₃ ≠ 0` and `θ₂ = 0`; the top face of the second
big cell. -/
def topFaceTwo : Set (Fin 3 → ℝ) := {p | p 0 ∈ Ioo 0 1 ∧ p 1 ∈ Ioo 0 π ∧ p 2 = 0}

/-- The closed 2-cell `𝒞₂(ζ) = 𝒞₂(ζ, 1, 1)` (TeX 12254–12276): `z₃ = 0`, in coordinates
`ψ ∈ {0, π}`, `r₂ ∈ [0, 1]`, `θ₂ ∈ [π/3, π]`. The book's coordinates are `r̃₁ = r₁ e^{iψ} = ±r₁`
(TeX 12265 writes "`r₁ = r̃₁ e^{iψ}`", reversed; gap G15.3) and `θ₂`; on `r̃₁ = 0` (`r₂ = 1`) the
two values of `ψ` give the same point. It is attached to the front and back faces `ψ ∈ {0, π}` of
the first big cell. -/
def frontBackOne : Set (Fin 3 → ℝ) :=
  {p | p 0 ∈ Icc 0 1 ∧ (p 1 = 0 ∨ p 1 = π) ∧ p 2 ∈ Icc (π / 3) π}

/-- The closed 2-cell `𝒞₂(ζ², 1, 1)` (TeX 12278–12285): `z₃ = 0`, `ψ ∈ {0, π}`, `r₂ ∈ [0, 1]`,
`θ₂ ∈ [-π, -π/3]` (the book: "brought into the interval `(-π, -π/3]`"), attached to the front and
back faces of the second big cell. -/
def frontBackTwo : Set (Fin 3 → ℝ) :=
  {p | p 0 ∈ Icc 0 1 ∧ (p 1 = 0 ∨ p 1 = π) ∧ p 2 ∈ Icc (-π) (-(π / 3))}

/-- The part `𝒞₂^A` of `𝒞₂(ζ², 0, 2)` on which `Δ_{A,0} ≥ 0` (TeX 12411–12415). -/
noncomputable def topFaceTwoA : Set (Fin 3 → ℝ) :=
  {p | p ∈ topFaceTwo ∧ 0 ≤ discrA (ζ ^ 2) (cellPoint p)}

/-- The part `𝒞₂^B` of `𝒞₂(ζ², 0, 2)` on which `Δ_{A,0} < 0` (TeX 12415–12418). -/
noncomputable def topFaceTwoB : Set (Fin 3 → ℝ) :=
  {p | p ∈ topFaceTwo ∧ discrA (ζ ^ 2) (cellPoint p) < 0}

/-- The least positive root of a real polynomial, of any multiplicity (`0` if there is none). -/
noncomputable def leastPosRoot (P : ℝ[X]) : ℝ := sInf {t | 0 < t ∧ P.eval t = 0}

/-- **The root-based cell map `F_A`** of `𝒞₂^A` (TeX 12413–12422): the trajectory with the first
control `ζ²` up to the least positive root of `χ_{A,0}`, double roots included. -/
noncomputable def cellMapA (z : Fin 3 → ℂ) : Fin 3 → ℂ :=
  flow (leastPosRoot (chiA (ζ ^ 2) z).toPoly) z (ζ ^ 2)

/-- **The root-based cell map `F_B`** of `𝒞₂^B` (TeX 12416–12422): the trajectory with the first
control `ζ²` up to the root `t_B = -6 y₁` of the linear polynomial `χ_{B,2} = -(t/12 + y₁/2)`. -/
noncomputable def cellMapB (z : Fin 3 → ℂ) : Fin 3 → ℂ := flow (-6 * (z 0).im) z (ζ ^ 2)

/-! ### The cell `𝒞₂(ζ, 0, 2)` -/

/-- **The cell `𝒞₂(ζ, 0, 2)`** (TeX 12223–12233): "The first control is `ζ`. The switching function
`χ_{B,2}` never has a positive root. Thus, the switching function is always `χ_{A,0}`. By
Descartes's rule of signs, `χ_{A,0}` always has a unique positive root."

Proof route: with `θ₂ = π`, `z = (r₁ e^{i(π - ψ)}, -r₂, -2 r₁ r₂ sin ψ)`, so `y₂ = 0` and
`y₁ = r₁ sin ψ > 0`: the tie between `ζ` and `ζ²` is broken by `y₁` (Lemma 13.2.6),
`χ_B = t²(y₁/2 + t/12)` has `m_B = 2` and `χ_{B,2} > 0` on `[0, ∞)`, and
`√3 χ_A = 3 r₁ r₂ sin ψ + (3/2) r₂ t + (r₁/4)(3 cos ψ + √3 sin ψ) t² - (√3/12) t³` has one sign
change of coefficients; the unique positive root is simple, so it is where `ζ` is first beaten (by
`1`). -/
theorem topFaceOne_switching {p : Fin 3 → ℝ} (hp : p ∈ topFaceOne) :
    firstControl (cellPoint p) = ζ ∧ multA ζ (cellPoint p) = 0 ∧ multB ζ (cellPoint p) = 2 ∧
      (∀ t : ℝ, 0 ≤ t → 0 < (chiBRed ζ (cellPoint p)).eval t) ∧
      ∃ T : ℝ, 0 < T ∧ {t : ℝ | 0 < t ∧ (chiA ζ (cellPoint p)).toPoly.eval t = 0} = {T} ∧
        firstSwitchTime (cellPoint p) = T := by
  sorry

/-- **`(m_A, m_B) = (0, 3)` is impossible** (TeX 12249–12252): "if `m_B = 3`, then `y₁ = y₂ = 0`.
This implies that `r₁ = 0`, `r₂ = 0` or `θ₁, θ₂ ∈ πℤ`. Then `x₃ = -2 r₁ r₂ sin ψ = 0` by (15.1.1),
and `m_A > 0`." (From `chiA_chiB_eq`: `m_B = 3` means `y₃ = y₂ = y₁ = 0`.) -/
theorem multB_eq_three {p : Fin 3 → ℝ} (hp : p ∈ cellDomain) {u : ℂ} (hu : u = ζ ∨ u = ζ ^ 2)
    (h : multB u (cellPoint p) = 3) : cellPoint p 2 = 0 ∧ 0 < multA u (cellPoint p) := by
  sorry

/-! ### The region `z₃ = 0` and the closed 2-cells `𝒞₂(ζ^{±1}, 1, 1)` -/

/-- "In the remaining region, `z₃ = 0` (and `m_A > 0`). By (15.1.1), we have `r₂ ∈ {0, 1}`, or
`sin ψ = 0`. Each angle `θ₂` is `V_T`-equivalent to a unique angle `θ₂ ∈ (π/3, π]`" (TeX
12254–12258): every point of the closed cells with `z₃ = 0` is equivalent to a point of the closed
2-cell `𝒞₂(ζ, 1, 1)`. On its relative interior (`r₂ > 0`, `θ₂ ∈ (π/3, π)`) the first control is `ζ`
and `(m_A, m_B) = (1, 1)` (`χ_A = t (r₂ sin(θ₂ - π/3) + …)`, `χ_B = t (r₂ sin θ₂ + …)`).

Proof route: the rotation by `ζ` adds `2π/3` to `θ₁` and `θ₂` and fixes `ψ` and `z₃ = 0`; on
`r₂ = 0` the point `(e^{iθ₁}, 0, 0)` is represented with `ψ = 0`, `θ₂ = θ₁`; the first control
maximizes `RR(z₂, ·)` (the lexicographic rule of Lemma 13.2.6, `RR(z₃, ·) = 0`). -/
theorem frontBackOne_cover_and_switching :
    (∀ p ∈ cellDomain, cellPoint p 2 = 0 → ∃ q ∈ frontBackOne, cellClass q = cellClass p) ∧
      ∀ p ∈ frontBackOne, 0 < p 0 → p 2 ∈ Ioo (π / 3) π →
        firstControl (cellPoint p) = ζ ∧ multA ζ (cellPoint p) = 1 ∧
          multB ζ (cellPoint p) = 1 := by
  sorry

/-! ### The cell `𝒞₂(ζ², 0, 2)` and the root-based maps `F_A`, `F_B` -/

/-- **The cell `𝒞₂(ζ², 0, 2)`** (TeX 12235–12238, 12411–12419): the first control is `ζ²`,
`(m_A, m_B) = (0, 2)`, `χ_{B,2} = -(t/12 + y₁/2)` has the unique root `t_B = -6 y₁ > 0`; "On one
part `𝒞₂^A`, we have `Δ_{A,0} ≥ 0`. By Descartes's rule of signs, `χ_{A,0}` has two positive roots
(counted with algebraic multiplicity). … On the interior of the part `𝒞₂^B`, we have `Δ_{A,0} < 0`.
In this case, `χ_{A,0}` has no positive root."

Proof route: `θ₂ = 0` gives `y₂ = 0`, `y₁ = -r₁ sin ψ < 0` (the tie is broken towards `ζ²`).
`χ_A` has coefficients `(1/12, ?, -(√3/2) r₂, -(√3/2) x₃)` (descending), so the product of the roots
is `< 0` and the sum of their pairwise products is `< 0`: with three real roots (`Δ ≥ 0`), exactly
one is negative and two are positive; with `Δ < 0`, the only real root is negative and
`χ_A > 0` on `[0, ∞)`. -/
theorem topFaceTwo_switching {p : Fin 3 → ℝ} (hp : p ∈ topFaceTwo) :
    firstControl (cellPoint p) = ζ ^ 2 ∧ multA (ζ ^ 2) (cellPoint p) = 0 ∧
      multB (ζ ^ 2) (cellPoint p) = 2 ∧ 0 < -6 * (cellPoint p 0).im ∧
      (chiBRed (ζ ^ 2) (cellPoint p)).roots = {-6 * (cellPoint p 0).im} ∧
      (0 ≤ discrA (ζ ^ 2) (cellPoint p) →
        ((chiA (ζ ^ 2) (cellPoint p)).toPoly.roots.filter (fun t ↦ 0 < t)).card = 2) ∧
      (discrA (ζ ^ 2) (cellPoint p) < 0 →
        ∀ t : ℝ, 0 ≤ t → 0 < (chiA (ζ ^ 2) (cellPoint p)).toPoly.eval t) := by
  sorry

/-- **The first switching time on `𝒞₂(ζ², 0, 2)`** (TeX 12413–12418): on `{Δ_{A,0} > 0}` "the first
switching time is a root of `χ_{A,0}`", the least positive one, and `F = F_A`; on `𝒞₂^B` it "is the
unique root of the linear polynomial `χ_{B,2}`" and `F = F_B`. The second case includes the
discriminant locus `Δ_{A,0} = 0`: there the double positive root of `χ_{A,0}` is a tangency, not a
switch, so `poincare = F_B` while the book's extension `F_A` uses the double root (see the module
docstring).

Proof route: if `Δ_{A,0} ≤ 0`, `χ_A ≥ 0` on `[0, ∞)` (`topFaceTwo_switching`; a double root is a
local minimum), so `ζ²` is first beaten by `ζ`, at the sign change `t_B` of `χ_B = t² χ_{B,2}`. If
`Δ_{A,0} > 0`, the least positive root `t₁` of `χ_{A,0}` is simple and `t₁ ≤ t_B` (the computation
in the module docstring), so `ζ²` is first beaten by `1` at `t₁`. -/
theorem firstSwitchTime_topFaceTwo {p : Fin 3 → ℝ} (hp : p ∈ topFaceTwo) :
    (discrA (ζ ^ 2) (cellPoint p) ≤ 0 →
      firstSwitchTime (cellPoint p) = -6 * (cellPoint p 0).im ∧
        poincare (cellPoint p) = cellMapB (cellPoint p)) ∧
      (0 < discrA (ζ ^ 2) (cellPoint p) →
        firstSwitchTime (cellPoint p) = leastPosRoot (chiA (ζ ^ 2) (cellPoint p)).toPoly ∧
          poincare (cellPoint p) = cellMapA (cellPoint p)) := by
  sorry

end TriFuller

open TriFuller

/-- **Remark 15.2.1** (TeX 12287–12296): "A symmetry of `V_T` carries the closed cell `𝒞₂(ζ, 1, 1)`
to `𝒞₂(ζ², 1, 1)`, but we refrain from identifying these two closed cells with each other." The
rotation by `ζ` maps `𝒞₂(ζ, 1, 1)` onto `𝒞₂(ζ², 1, 1)` (`θ₂ ↦ θ₂ + 2π/3 - 2π`, `ψ` and `z₃ = 0`
fixed), so corresponding points have the same class in `Ξ_{𝒲,0}/V_T`. (The rest of the remark,
"`F⁻¹(𝒞₂(ζ))` and `F⁻¹(𝒞₂(ζ²))` are the two sides of a hypersurface `∂_res` in the first big cell,
along which the Fuller–Poincaré map is discontinuous", is read off Figure 15.2 and is not
formalized: `Proposition15_3_2` does not contain it, and the proof of Theorem 16.1.1 does not use
it.) -/
theorem remark15_2_1 :
    ∀ p ∈ frontBackOne, ![p 0, p 1, p 2 - 4 * π / 3] ∈ frontBackTwo ∧
      ζ • cellPoint p = cellPoint ![p 0, p 1, p 2 - 4 * π / 3] ∧
      cellClass ![p 0, p 1, p 2 - 4 * π / 3] = cellClass p := by
  sorry

/-- **Proposition 15.2.2** (TeX 12300–12314), in `Ξ_{𝒲,0}/V_T`. "Every point in the domain of
`Ξ_{𝒲,0}/V_T` is equivalent to a point in the union of the closures `𝒞₃(ζ^{±1})` of the first and
second big cells (with identifications on the boundaries of each cell as given above). The first
control `u` is `ζ` on the first big cell and `ζ²` on the second big cell. The dynamics on the faces
of the cells is given as the continuous extension from the dynamics on the interior of the cells.
Every point on every face of the cells that is not identified with a point in the domain
`Ξ_{𝒲,0}/V_T` is a point with vanishing (limiting) first switching time `t_sw = 0`."

Formalized (the book's proof: "See the discussion leading up to the statement"):
1. every point is in the second big cell with its top face (`cellTwoSet`), or has a representative
   in the closed first big cell at which the first control is `ζ` (from Lemma 15.1.1, (15.1.1),
   Lemma 13.2.6 and `frontBackOne_cover_and_switching`);
2. the first control is `ζ` on the open first cell and `ζ²` on the second cell with its top face;
3. at a point `p` of the closed first (second) cell at which `ζ` (`ζ²`) is not the first control
   of `cellPoint p` — a face point whose cell dynamics does not represent the dynamics of its class
   ("not identified with a point in the domain") — the first switching time tends to `0` from the
   open cell, and the extended map is the identity of `Ξ_{𝒲,0}/V_T` there: `F(cellClass q) →
   cellClass p`. These are the red-shaded regions of Figure 15.1 and the boundary maps of
   TeX 12178–12195 (`θ₂ = 0⁺ ↦ 0⁻`, `θ₂ ↦ θ₂ ± 2π/3` on `ψ ∈ {0, π}`, `θ₂ ↦ 2π + θ₂`), each of which
   is a change of representative of the same class.

"The dynamics on the faces … is the continuous extension from the interior" holds where the
dynamics is continuous (`continuousWithinAt_topFaceOne`, `continuousWithinAt_frontBackOne`,
`continuousWithinAt_topFaceTwo`); the extensions on the closed parts of the cells are the subject of
Proposition 15.3.2 (`Proposition15_3_2`).

Proof route for 3: the first control at `cellPoint p` is not `ζ`, so `ζ` is beaten at some time
`t ∈ [0, ε]` for every `ε > 0`; beating is a strict inequality between continuous functions of
`(t, q)`, so for `q` near `p` in the open cell (first control `ζ`) `ζ` is beaten at a time `≤ ε`
along the trajectory of `cellPoint q`, so `0 < t_sw(cellPoint q) ≤ ε`; then
`F(cellPoint q) = z(t_sw, cellPoint q, ζ) → cellPoint p` and `classOf` is continuous. -/
theorem proposition15_2_2 :
    (∀ x : XiW0Quot, x ∈ cellTwoSet ∨
      ∃ p ∈ closedBoxOne, cellClass p = x ∧ IsFirstControl (cellPoint p) ζ) ∧
    (∀ p ∈ openBoxOne, IsFirstControl (cellPoint p) ζ) ∧
    (∀ p ∈ cellTwoDomain, IsFirstControl (cellPoint p) (ζ ^ 2)) ∧
    (∀ p ∈ closedBoxOne, ¬ IsFirstControl (cellPoint p) ζ →
      Tendsto (fun q ↦ firstSwitchTime (cellPoint q)) (𝓝[openBoxOne] p) (𝓝 0) ∧
        Tendsto (fun q ↦ poincareAngZero (cellClass q)) (𝓝[openBoxOne] p) (𝓝 (cellClass p))) ∧
    ∀ p ∈ closedBoxTwo, ¬ IsFirstControl (cellPoint p) (ζ ^ 2) →
      Tendsto (fun q ↦ firstSwitchTime (cellPoint q)) (𝓝[openBoxTwo] p) (𝓝 0) ∧
        Tendsto (fun q ↦ poincareAngZero (cellClass q)) (𝓝[openBoxTwo] p) (𝓝 (cellClass p)) := by
  sorry

/-- **The boundary maps on the red-shaded faces** (TeX 12178–12195, Figure 15.1). "The bottom face
`θ₂ = 0⁺` of the first big cell maps to the top face `θ₂ = 0⁻` of the second big cell (by the
identity map `(r₂, ψ) ↦ (r₂, ψ)`). The bottom face `θ₂ = (-π)⁺` of the second big cell maps to the
top face `θ₂ = π⁻` of the first big cell by the map `(r₂, ψ, θ₂) ↦ (r₂, ψ, 2π + θ₂)`. The boundary
region `ψ ∈ {0, π}`, `θ₂ ∈ [0, π/3]` on the first big cell is shifted to `V_T`-equivalent points
`(ψ, θ₂) ↦ (ψ, θ₂ + 2π/3)` on the same faces. Also, the boundary region `ψ ∈ {0, π}`,
`θ₂ ∈ [-π/3, 0]` on the first [read: second] big cell is shifted to `V_T`-equivalent points
`(ψ, θ₂) ↦ (ψ, θ₂ - 2π/3)`."

On each of these faces the cell's control is not the first control (so, by `proposition15_2_2`,
`t_sw → 0` from the open cell and the extended map is the identity of `Ξ_{𝒲,0}/V_T`), and the face
point has the same class as the point it is said to map to. The bottom face of the first cell is in
the second cell (`cellTwoSet`). At `θ₂ = -π/3` (an endpoint of the book's closed interval) the tie
rule of Lemma 13.2.6 makes `ζ²` the first control, so that endpoint is excluded; at `θ₂ = π/3` the
same rule gives the control `1`, and the endpoint is included.

Proof route: the first controls from the lexicographic rule of Lemma 13.2.6 (`lemma13_2_6`): on
`θ₂ = 0` the tie between `ζ` and `ζ²` is broken by `y₁ = -r₁ sin ψ < 0`, on `θ₂ = -π` by
`y₁ = r₁ sin ψ > 0`; on `z₃ = 0` the first control maximizes `RR(z₂, ·)`, which is `1` when
`arg z₂ ∈ [0, π/3]` (`ζ` loses the tie at `π/3`) or `arg z₂ ∈ (-π/3, 0]`. The classes: the points
are equal (`e^{-iπ} = e^{iπ}`), or differ by the rotation by `ζ` (resp. `ζ²`), which fixes `ψ` and
`z₃ = 0`. -/
theorem boundary_maps_red_faces :
    (∀ p : Fin 3 → ℝ, p 0 ∈ Ioo 0 1 → p 1 ∈ Ioo 0 π → p 2 = 0 →
      ¬ IsFirstControl (cellPoint p) ζ ∧ cellClass p ∈ cellTwoSet) ∧
    (∀ p : Fin 3 → ℝ, p 0 ∈ Ioo 0 1 → p 1 ∈ Ioo 0 π → p 2 = -π →
      ¬ IsFirstControl (cellPoint p) (ζ ^ 2) ∧ cellClass p = cellClass ![p 0, p 1, π]) ∧
    (∀ p : Fin 3 → ℝ, p 0 ∈ Ioc 0 1 → (p 1 = 0 ∨ p 1 = π) → p 2 ∈ Icc 0 (π / 3) →
      ¬ IsFirstControl (cellPoint p) ζ ∧ cellClass p = cellClass ![p 0, p 1, p 2 + 2 * π / 3]) ∧
    ∀ p : Fin 3 → ℝ, p 0 ∈ Ioc 0 1 → (p 1 = 0 ∨ p 1 = π) → p 2 ∈ Ioc (-(π / 3)) 0 →
      ¬ IsFirstControl (cellPoint p) (ζ ^ 2) ∧
        cellClass p = cellClass ![p 0, p 1, p 2 - 2 * π / 3] := by
  sorry

end SmoothedPolygons
