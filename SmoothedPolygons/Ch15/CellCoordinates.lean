module

public import SmoothedPolygons.Ch13.FixedPointsClassification
public import Mathlib.Algebra.Order.ToIntervalMod

/-!
# Chapter 15: the cell coordinates `(r₂, ψ, θ₂)` on `Ξ_{𝒲,0}/V_T` (§15.1)

§15.1 of Hales–Vajjha, *Packings of Smoothed Polygons* ("Three-Cells", TeX 12043–12207), the
coordinates in which Chapters 15 and 16 describe the Fuller–Poincaré map `F = F_ang` on
`Ξ_{𝒲,0}/V_T` (`poincareAngZero`, `SmoothedPolygons/Ch13/PoincareMap.lean`):

* the class `classOf z ∈ Ξ_{𝒲,0}/V_T` of a point `z ≠ 0` of `ℂ³` with `z₃ ∈ 𝒲` and `H_F⁺(z) = 0`
  (`sectionZero`), and its compatibility with the virial group, with `F` and with `τ`;
* equation (15.1.1) `eqn:x3`: with `z_j = r_j e^{iθ_j}` and `z₃ = x₃ ≤ 0`, the vanishing of the
  Hamiltonian reads `x₃ = 2 r₁ r₂ sin(θ₁ - θ₂) = -2 r₁ r₂ sin ψ`, `ψ = θ₂ - θ₁` (`eqn15_1_1`);
* Lemma 15.1.1: the unique virial rescaling with `r₁ + r₂ = 1` (`lemma15_1_1`);
* the cell coordinates `p = (r₂, ψ, θ₂)` (`p 0 = r₂`, `p 1 = ψ`, `p 2 = θ₂`) and the point
  `cellPoint p = ((1 - r₂) e^{i(θ₂ - ψ)}, r₂ e^{iθ₂}, -2 (1 - r₂) r₂ sin ψ)`, whose class is
  `cellClass p`; the closed big cells `closedBoxOne` (`θ₂ ∈ [0, π]`) and `closedBoxTwo`
  (`θ₂ ∈ [-π, 0]`), the open boxes, and the second open cell with its top face `cellTwoDomain`;
* the face identifications (TeX 12149–12160): on `r₂ = 0` the point depends only on
  `θ₁ = θ₂ - ψ`, on `r₂ = 1` only on `θ₂`;
* the time reversal in coordinates, `τ(r₂, ψ, θ₂) = (r₂, π - ψ, ±π - θ₂)` (TeX 12077–12084,
  12132–12136) (`cellTau`, `tau_cellPoint`, `cellClass_cellTau`);
* Definition 15.1.2 `def:big:open` (the big open cells) with the facts stated after it
  (TeX 12104–12136) (`openCellOne`, `openCellTwo`, `definition15_1_2`);
* the inverse coordinates `cellCoords` and the coordinates `pOut`, `pIn = τ(pOut)` of the fixed
  points `q_out`, `q_in` of Lemma 13.5.2 (used by Remark 15.3.1 and Chapter 16).

## Points of `Ξ_{𝒲,0}/V_T` versus points of the book's cell complex

The book works with "the domain given by the cells covering `Ξ_{𝒲,0}/V_T`" (TeX 12038–12041): two
closed boxes whose faces are identified only partly (TeX 12149–12165: the bottom face `θ₂ = 0` of
the first big cell is *not* identified with the top face `θ₂ = 0` of the second, nor `θ₂ = π`
with `θ₂ = -π`), so that the cell complex has points that are the same point of `Ξ_{𝒲,0}/V_T`.
This formalization keeps the book's theorem in `Ξ_{𝒲,0}/V_T` (`XiW0Quot`) with the honest
Pontryagin map `poincareAngZero` (see `SmoothedPolygons/Ch13/Defs.lean` on robustness), and
uses the cells as *charts*: `cellClass : ℝ³ → Ξ_{𝒲,0}/V_T` is continuous on the closed cells,
surjective from their union (Proposition 15.2.2), and injective on each open box. Regions of
`Ξ_{𝒲,0}/V_T` are images `cellClass '' S` of sets `S` of coordinates.

## Proofs

All the statements here are elementary: (15.1.1) is `H_F(z, ζ) = RR(z₁, i z₂) + RR(ζ, x₃) =
-r₁ r₂ sin ψ - x₃/2` and `H_F(z, 1) ≤ H_F(z, ζ) = H_F(z, ζ²)` when `x₃ ≤ 0`; Lemma 15.1.1 is the
quadratic `r₁ s + r₂ s² = 1`; the τ-formula is `conj(e^{iθ}) = e^{-iθ}`,
`-e^{-iθ₂} = e^{i(±π - θ₂)}` and `sin(π - ψ) = sin ψ`; the class map is the quotient map composed
with `ang`, so it is continuous where `ang` is (`continuousOn_ang`) and compatible with `F` and
`τ` by `ang_poincare_ang`, `poincare_smul`, `poincare_scale`, `tau_ang`.
-/

@[expose] public section

namespace SmoothedPolygons

open Complex Set Filter Topology
open scoped Real

namespace TriFuller

/-! ### The class of a point of the section -/

/-- The zero-Hamiltonian Poincaré section in Cartesian coordinates: `z ≠ 0`, `z₃ ∈ 𝒲` and
`H_F⁺(z) = 0` (the points whose angular part lies in `Ξ_{𝒲,0}`, TeX 11429–11436). -/
def sectionZero : Set (Fin 3 → ℂ) := {z | z ≠ 0 ∧ z 2 ∈ walls ∧ hamMax z = 0}

/-- The angular part of a point `z ≠ 0` with `z₃ ∈ 𝒲` lies in `Ξ_𝒲` (`ang` rescales `z₃` by a
positive real, and `𝒲` is a union of rays). -/
theorem ang_mem_XiW {z : Fin 3 → ℂ} (hz : z ≠ 0) (h : z 2 ∈ walls) : ang z ∈ XiW := by
  sorry

/-- `H_F⁺(ang z) = φ(z)⁻³ H_F⁺(z)` vanishes when `H_F⁺(z)` does (`hamMax_smul_scale_and_tau`). -/
theorem hamMax_ang_eq_zero {z : Fin 3 → ℂ} (hz : z ≠ 0) (h : hamMax z = 0) :
    hamMax (ang z) = 0 := by
  sorry

/-- The class in `Ξ_{𝒲,0}/V_T` of a point of the section `sectionZero` (the class of its angular
part `ang z`); the junk value `q_out` off the section. -/
noncomputable def classOf (z : Fin 3 → ℂ) : XiW0Quot :=
  open Classical in
  if h : z ∈ sectionZero then
    ⟨Quotient.mk'' ⟨ang z, ang_mem_XiW h.1 h.2.1⟩, hamMax_ang_eq_zero h.1 h.2.2⟩
  else qOut0

/-- Every point of `Ξ_{𝒲,0}/V_T` is the class of a point of the section (of any representative
`ξ ∈ Ξ_{𝒲,0}`, for which `ang ξ = ξ`). -/
theorem exists_classOf_eq (x : XiW0Quot) : ∃ z ∈ sectionZero, classOf z = x := by
  sorry

/-- The class is invariant under the virial group: `classOf (v · (r z₁, r² z₂, r³ z₃)) =
classOf z` for `v ∈ V_T`, `r > 0` (`weightedNorm_ang_smul_scale`). -/
theorem classOf_smul_scale {v : ℂ} (hv : v ∈ VT) {r : ℝ} (hr : 0 < r) {z : Fin 3 → ℂ}
    (hz : z ∈ sectionZero) : classOf (v • scale r z) = classOf z := by
  sorry

/-- Two points of the section have the same class exactly when they differ by the virial group
(`𝒢 ≅ ℝ_{>0} × ℤ/3`, TeX 10820–10827). -/
theorem classOf_eq_classOf_iff {z w : Fin 3 → ℂ} (hz : z ∈ sectionZero)
    (hw : w ∈ sectionZero) :
    classOf z = classOf w ↔ ∃ v ∈ VT, ∃ r : ℝ, 0 < r ∧ w = v • scale r z := by
  sorry

/-- `F` maps the section to itself: `F(z) ≠ 0` (`poincare_ne_zero`), `F(z)₃ ∈ 𝒲` (the trajectory
switches on a wall) and `H_F⁺(F z) = H_F⁺(z)` (`hamMax_poincare`). -/
theorem poincare_mem_sectionZero {z : Fin 3 → ℂ} (hz : z ∈ sectionZero) :
    poincare z ∈ sectionZero := by
  sorry

/-- `F_ang` on classes is `F` on representatives: `F(classOf z) = classOf (F z)`
(`ang_poincare_ang`, TeX 11256–11265). -/
theorem poincareAngZero_classOf {z : Fin 3 → ℂ} (hz : z ∈ sectionZero) :
    poincareAngZero (classOf z) = classOf (poincare z) := by
  sorry

/-- `τ` maps the section to itself (`tau_ne_zero`, `conj 𝒲 = 𝒲`, `H_F⁺(τ z) = H_F⁺(z)`). -/
theorem tau_mem_sectionZero {z : Fin 3 → ℂ} (hz : z ∈ sectionZero) : tau z ∈ sectionZero := by
  sorry

/-- `τ` on classes is `τ` on representatives (`tau_ang`). -/
theorem tauZero_classOf {z : Fin 3 → ℂ} (hz : z ∈ sectionZero) :
    tauZero (classOf z) = classOf (tau z) := by
  sorry

/-- The class map is continuous on the section (`continuousOn_ang`, the quotient map). -/
theorem continuousOn_classOf : ContinuousOn classOf sectionZero := by
  sorry

/-- `qOutCart` and `τ(qOutCart)` represent `q_out` and `q_in` (Lemma 13.5.2). -/
theorem classOf_qOutCart :
    qOutCart ∈ sectionZero ∧ classOf qOutCart = qOut0 ∧ tau qOutCart ∈ sectionZero ∧
      classOf (tau qOutCart) = qIn0 := by
  sorry

/-! ### Cell coordinates -/

/-- The point of `ℂ³` with cell coordinates `p = (r₂, ψ, θ₂)` (`p 0 = r₂`, `p 1 = ψ`,
`p 2 = θ₂`; TeX 12045–12067): `r₁ = 1 - r₂`, `θ₁ = θ₂ - ψ` and, by (15.1.1),
`z₃ = x₃ = -2 r₁ r₂ sin ψ`:
`(z₁, z₂, z₃) = ((1 - r₂) e^{i(θ₂ - ψ)}, r₂ e^{iθ₂}, -2 (1 - r₂) r₂ sin ψ)`. -/
noncomputable def cellPoint (p : Fin 3 → ℝ) : Fin 3 → ℂ :=
  ![((1 - p 0 : ℝ) : ℂ) * exp (((p 2 - p 1 : ℝ) : ℂ) * I), (p 0 : ℂ) * exp ((p 2 : ℂ) * I),
    ((-2 * (1 - p 0) * p 0 * Real.sin (p 1) : ℝ) : ℂ)]

/-- The coordinate domain `r₂ ∈ [0, 1]`, `ψ ∈ [0, π]`, `θ₂ ∈ [-π, π]` of the two closed big cells
(TeX 12073–12080). -/
def cellDomain : Set (Fin 3 → ℝ) := {p | p 0 ∈ Icc 0 1 ∧ p 1 ∈ Icc 0 π ∧ p 2 ∈ Icc (-π) π}

/-- The closed first big cell `𝒞₃(ζ)` in coordinates: `r₂ ∈ [0, 1]`, `ψ ∈ [0, π]`, `θ₂ ∈ [0, π]`
(TeX 12115–12118; the closure of the open box, with the book's face identifications made in
`Ξ_{𝒲,0}/V_T` by `cellClass`). -/
def closedBoxOne : Set (Fin 3 → ℝ) := {p | p 0 ∈ Icc 0 1 ∧ p 1 ∈ Icc 0 π ∧ p 2 ∈ Icc 0 π}

/-- The closed second big cell `𝒞₃(ζ²)` in coordinates: `θ₂ ∈ [-π, 0]` (TeX 12118–12121). -/
def closedBoxTwo : Set (Fin 3 → ℝ) := {p | p 0 ∈ Icc 0 1 ∧ p 1 ∈ Icc 0 π ∧ p 2 ∈ Icc (-π) 0}

/-- The open box `r₂ ∈ (0, 1)`, `ψ ∈ (0, π)`, `θ₂ ∈ (0, π)` of the first big open cell
`𝒞₃(ζ)⁰` (TeX 12115–12118). -/
def openBoxOne : Set (Fin 3 → ℝ) := {p | p 0 ∈ Ioo 0 1 ∧ p 1 ∈ Ioo 0 π ∧ p 2 ∈ Ioo 0 π}

/-- The open box `θ₂ ∈ (-π, 0)` of the second big open cell `𝒞₃(ζ²)⁰` (TeX 12118–12121). -/
def openBoxTwo : Set (Fin 3 → ℝ) := {p | p 0 ∈ Ioo 0 1 ∧ p 1 ∈ Ioo 0 π ∧ p 2 ∈ Ioo (-π) 0}

/-- The second big open cell together with its top face `θ₂ = 0` (the 2-cell `𝒞₂(ζ², 0, 2)`,
TeX 12235–12245): `r₂ ∈ (0, 1)`, `ψ ∈ (0, π)`, `θ₂ ∈ (-π, 0]`. These are exactly the points of
`Ξ_{𝒲,0}/V_T` with `x₃ < 0` whose first control is `ζ²` (`mem_cellTwoSet_iff`). -/
def cellTwoDomain : Set (Fin 3 → ℝ) :=
  {p | p 0 ∈ Ioo 0 1 ∧ p 1 ∈ Ioo 0 π ∧ p 2 ∈ Ioc (-π) 0}

/-- The class in `Ξ_{𝒲,0}/V_T` of the point with cell coordinates `p`. -/
noncomputable def cellClass (p : Fin 3 → ℝ) : XiW0Quot := classOf (cellPoint p)

/-- The points of `Ξ_{𝒲,0}/V_T` of the second big cell (first control `ζ²`, `x₃ < 0`): the
image of `cellTwoDomain`. Its complement is the set of points with a representative in the
closed first big cell at which the first control is `ζ` (`proposition15_2_2`). -/
noncomputable def cellTwoSet : Set XiW0Quot := cellClass '' cellTwoDomain

/-- Points with cell coordinates in the closed cells lie on the section: `cellPoint p ≠ 0`
(`r₁ + r₂ = 1`), `z₃ = -2 r₁ r₂ sin ψ ≤ 0` lies on the wall `𝒲₀`, and `H_F⁺ = 0` by (15.1.1). -/
theorem cellPoint_mem_sectionZero {p : Fin 3 → ℝ} (hp : p ∈ cellDomain) :
    cellPoint p ∈ sectionZero := by
  sorry

/-- The class map is continuous on the closed cells. -/
theorem continuousOn_cellClass : ContinuousOn cellClass cellDomain := by
  sorry

/-- **The face identifications** (TeX 12149–12160): "We identify points along the face `r₂ = 0`,
if they have the same image under … `f(ψ, θ₂) = θ₂ - ψ = θ₁`" (on `r₂ = 0` the point is
`(e^{iθ₁}, 0, 0)`), and "along the face `r₂ = 1`, if they have the same image under the projection
`f(ψ, θ₂) = θ₂`" (the point is `(0, e^{iθ₂}, 0)`). -/
theorem cellPoint_face_identifications :
    (∀ p q : Fin 3 → ℝ, p 0 = 0 → q 0 = 0 → p 2 - p 1 = q 2 - q 1 → cellPoint p = cellPoint q) ∧
      ∀ p q : Fin 3 → ℝ, p 0 = 1 → q 0 = 1 → p 2 = q 2 → cellPoint p = cellPoint q := by
  sorry

/-! ### The time reversal in cell coordinates -/

/-- The time reversal in cell coordinates, `τ(r₂, ψ, θ₂) = (r₂, π - ψ, ±π - θ₂)`, "the sign `±π`
… chosen to give a value again in `[-π, π]`" (TeX 12077–12084): `+π` for `θ₂ ≥ 0`, `-π` for
`θ₂ < 0`. At `θ₂ = 0` the TeX allows either sign and its formula for the second cell (TeX
12129–12130) gives `-π`; both give the same class (`cellClass_cellTau`), but with `+π` the map
`cellTau` does not send `closedBoxTwo` into itself. -/
noncomputable def cellTau (p : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![p 0, π - p 1, (if 0 ≤ p 2 then π else -π) - p 2]

/-- `τ(cellPoint p) = cellPoint (τ p)` for every `p`: `conj((1 - r₂)e^{iθ₁}) = (1 - r₂)e^{-iθ₁}`,
`-conj(r₂ e^{iθ₂}) = r₂ e^{i(±π - θ₂)}` and `sin(π - ψ) = sin ψ`. -/
theorem tau_cellPoint (p : Fin 3 → ℝ) : tau (cellPoint p) = cellPoint (cellTau p) := by
  sorry

/-- `τ` maps the coordinate domain to itself and is `τ` on classes. -/
theorem cellClass_cellTau {p : Fin 3 → ℝ} (hp : p ∈ cellDomain) :
    cellTau p ∈ cellDomain ∧ cellClass (cellTau p) = tauZero (cellClass p) := by
  sorry

/-! ### Inverse coordinates -/

/-- The cell coordinates of a point `z` of the section with `z₃ ∈ ℝ_{<0}`: with `a = |z₁|`,
`b = |z₂|` and `s > 0` the root of `a s + b s² = 1` (Lemma 15.1.1), `r₂ = s² b`, `θ₂ = arg z₂`
and `ψ = arg z₂ - arg z₁` reduced to `[0, 2π)`. -/
noncomputable def cellCoords (z : Fin 3 → ℂ) : Fin 3 → ℝ :=
  let a := ‖z 0‖
  let b := ‖z 1‖
  let s := if b = 0 then a⁻¹ else (-a + √(a ^ 2 + 4 * b)) / (2 * b)
  ![s ^ 2 * b, toIcoMod Real.two_pi_pos 0 (arg (z 1) - arg (z 0)), arg (z 1)]

/-- `cellCoords` inverts `cellPoint` on the open cells and their top faces (`r₂ ∈ (0, 1)`,
`ψ ∈ (0, π)`, `θ₂ ∈ (-π, π]`). -/
theorem cellCoords_cellPoint {p : Fin 3 → ℝ} (hp : p 0 ∈ Ioo 0 1 ∧ p 1 ∈ Ioo 0 π ∧
    p 2 ∈ Ioc (-π) π) : cellCoords (cellPoint p) = p := by
  sorry

/-- A point `z` of the section with `z₃ ∈ ℝ_{<0}` has cell coordinates: `r₂ ∈ (0, 1)`,
`ψ ∈ (0, π)` (by (15.1.1), `x₃ < 0` forces `r₁ r₂ ≠ 0` and `sin ψ > 0`), `θ₂ ∈ (-π, π]`, and
`cellPoint (cellCoords z)` is the rescaling of `z` with `r₁ + r₂ = 1`, so it has the same
class. -/
theorem cellClass_cellCoords {z : Fin 3 → ℂ} (hz : z ∈ sectionZero) (h₃ : (z 2).im = 0)
    (h₃' : (z 2).re < 0) :
    (cellCoords z 0 ∈ Ioo 0 1 ∧ cellCoords z 1 ∈ Ioo 0 π ∧ cellCoords z 2 ∈ Ioc (-π) π) ∧
      cellClass (cellCoords z) = classOf z := by
  sorry

/-- The cell coordinates `(r₂, ψ, θ₂)` of the fixed point `q_out` (13.5.1): numerically
`(0.267949…, 0.1705935…, 2.91574…)`, which Remark 15.3.1 prints as the coordinates of `q_in`
(gap G15.1; `remark15_3_1`). -/
noncomputable def pOut : Fin 3 → ℝ := cellCoords qOutCart

/-- The cell coordinates of the fixed point `q_in = τ(q_out)`:
`τ(pOut) = (0.267949…, 2.9709991…, 0.2258526…)`. -/
noncomputable def pIn : Fin 3 → ℝ := cellTau pOut

/-! ### The big open cells (Definition 15.1.2) -/

/-- The first big open cell `𝒞₃(ζ)⁰ = 𝒞₃(ζ, 0, 1)⁰` (Definition 15.1.2, TeX 12104–12108): the
points of `Ξ_{𝒲,0}/V_T` with a representative such that `z₃ = x₃ < 0` ("`x₃ ≠ 0`" after the
rotation making `z₃ = x₃ ≤ 0`, TeX 12047–12048) and `y₂ = Im z₂ > 0`. -/
def openCellOne : Set XiW0Quot :=
  {x | ∃ z ∈ sectionZero, classOf z = x ∧ (z 2).im = 0 ∧ (z 2).re < 0 ∧ 0 < (z 1).im}

/-- The second big open cell `𝒞₃(ζ²)⁰ = 𝒞₃(ζ², 0, 1)⁰` (Definition 15.1.2): `x₃ < 0` and
`y₂ < 0`. -/
def openCellTwo : Set XiW0Quot :=
  {x | ∃ z ∈ sectionZero, classOf z = x ∧ (z 2).im = 0 ∧ (z 2).re < 0 ∧ (z 1).im < 0}

/-- The points of the second big cell (`cellTwoSet`) are those with a representative with
`z₃ ∈ ℝ_{<0}` and first control `ζ²`; the first control of such a representative is `ζ` or `ζ²`
(the controls `ζ`, `ζ²` tie at `z₃`, `RR(z₃, 1) = x₃ < -x₃/2`), and the tie is broken by `y₂`, then
by `y₁` (Lemma 13.2.6). -/
theorem mem_cellTwoSet_iff (x : XiW0Quot) :
    x ∈ cellTwoSet ↔ ∃ z ∈ sectionZero, classOf z = x ∧ (z 2).im = 0 ∧ (z 2).re < 0 ∧
      firstControl z = ζ ^ 2 := by
  sorry

end TriFuller

open TriFuller

/-- **Equation (15.1.1)** (`eqn:x3`, TeX 12049–12058). Write `z_j = r_j e^{iθ_j}` and assume
`z₃ = x₃ ≤ 0` (on the wall `𝒲₀`, after a rotation by `V_T`). "The vanishing Hamiltonian
condition implies `x₃ = 2 r₁ r₂ sin(θ₁ - θ₂) = -2 r₁ r₂ sin ψ`, where `ψ := θ₂ - θ₁`. If `x₃ < 0`,
this implies `r₁ r₂ ≠ 0` and `ψ ∈ (0, π)` (modulo integer multiples of `2π`)."

The Hamiltonian is the maximized one, `H_F⁺` (the Hamiltonian of the first control, which is `ζ`
or `ζ²` when `x₃ ≤ 0`): for a real `x₃ ≤ 0`, `H_F(z, ζ) = H_F(z, ζ²) = RR(z₁, i z₂) - x₃/2 =
-r₁ r₂ sin(θ₂ - θ₁) - x₃/2 ≥ H_F(z, 1) = -r₁ r₂ sin(θ₂ - θ₁) + x₃`. The second assertion uses
`r₁, r₂ ≥ 0` ("`ψ ∈ (0, π)` modulo `2π`" is `sin ψ > 0`). -/
theorem eqn15_1_1 {r₁ r₂ θ₁ θ₂ x₃ : ℝ} (hx₃ : x₃ ≤ 0) :
    (hamMax ![(r₁ : ℂ) * exp ((θ₁ : ℂ) * I), (r₂ : ℂ) * exp ((θ₂ : ℂ) * I), (x₃ : ℂ)] = 0 ↔
      x₃ = 2 * r₁ * r₂ * Real.sin (θ₁ - θ₂)) ∧
      (0 ≤ r₁ → 0 ≤ r₂ → x₃ < 0 →
        hamMax ![(r₁ : ℂ) * exp ((θ₁ : ℂ) * I), (r₂ : ℂ) * exp ((θ₂ : ℂ) * I), (x₃ : ℂ)] = 0 →
        r₁ * r₂ ≠ 0 ∧ 0 < Real.sin (θ₂ - θ₁)) := by
  sorry

/-- **Lemma 15.1.1** (TeX 12060–12071). "For each `z = (z₁, z₂, z₃) ≠ 0` satisfying (15.1.1),
there is a unique rescaling by a positive scalar in the virial group so that `r₁ + r₂ = 1` (and
`r₁, r₂ ≥ 0`)."

The book's proof: if `r₁ = r₂ = 0`, then `z = 0` by (15.1.1), contrary to assumption; hence
`r₁ + r₂ > 0`, and the quadratic equation `r₁/s + r₂/s² = 1` has a unique positive root `s`; scale
`r_i ↦ r_i/s^i` (the rescaling `scale (1/s)`; uniqueness because `s ↦ r₁ s + r₂ s²` is strictly
increasing on `(0, ∞)`). -/
theorem lemma15_1_1 {z : Fin 3 → ℂ} (hz : z ≠ 0)
    (h₃ : z 2 = ((2 * ‖z 0‖ * ‖z 1‖ * Real.sin (arg (z 0) - arg (z 1)) : ℝ) : ℂ)) :
    ∃! s : ℝ, 0 < s ∧ ‖scale s z 0‖ + ‖scale s z 1‖ = 1 := by
  sorry

/-- **Definition 15.1.2** (`def:big:open`, TeX 12104–12136) and the facts stated after it. The
big open cells `𝒞₃(ζ)⁰ = {x₃ ≠ 0, y₂ > 0}` and `𝒞₃(ζ²)⁰ = {x₃ ≠ 0, y₂ < 0}`:
* "`𝒞₃(ζ)⁰` is a three-dimensional open rectangle in `ℝ³` with coordinates `r₂ ∈ (0, 1)`,
  `ψ ∈ (0, π)`, and `θ₂ ∈ (0, π)`" and `𝒞₃(ζ²)⁰` has `θ₂ ∈ (-π, 0)`: the cell coordinates map
  the open boxes bijectively onto the open cells (Lemma 15.1.1 and (15.1.1));
* "The first control is `ζ`" on the first cell and `ζ²` on the second (Lemma 13.2.6: the tie
  between `ζ` and `ζ²` in `RR(z₃, ·)` is broken by `RR(z₂, ζ) - RR(z₂, ζ²) = √3 y₂`);
* "The involution `τ` is given by `τ(r₂, ψ, θ₂) = (r₂, π - ψ, π - θ₂)` on the first big cell and
  by `τ(r₂, ψ, θ₂) = (r₂, π - ψ, -π - θ₂)` on the second big cell" (`tau_cellPoint`).

The multiplicities `(m_A, m_B) = (0, 1)` of the notation `𝒞₃(u, m_A, m_B)` are
`multA_multB_of_mem_openBox` (`SmoothedPolygons/Ch15/SmallerCells.lean`). -/
theorem definition15_1_2 :
    cellClass '' openBoxOne = openCellOne ∧ cellClass '' openBoxTwo = openCellTwo ∧
      Disjoint openCellOne openCellTwo ∧ InjOn cellClass openBoxOne ∧
      InjOn cellClass openBoxTwo ∧
      (∀ p ∈ openBoxOne, firstControl (cellPoint p) = ζ) ∧
      (∀ p ∈ openBoxTwo, firstControl (cellPoint p) = ζ ^ 2) ∧
      (∀ p ∈ openBoxOne, ![p 0, π - p 1, π - p 2] ∈ openBoxOne ∧
        tauZero (cellClass p) = cellClass ![p 0, π - p 1, π - p 2]) ∧
      ∀ p ∈ openBoxTwo, ![p 0, π - p 1, -π - p 2] ∈ openBoxTwo ∧
        tauZero (cellClass p) = cellClass ![p 0, π - p 1, -π - p 2] := by
  sorry

end SmoothedPolygons
