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

The first controls on the big cells come from Lemma 13.2.6 (`lemma13_2_6`): on `𝒲₀` the control
vectors of `ζ` and `ζ²` beat that of `1` in their first entry and differ by `√3 (0, y₂, y₁)`, so
`V_{T,max}` is a singleton. The injectivity of `cellClass` on the open boxes: two points of the
section with `z₃ ∈ ℝ_{<0}` and the same class differ by a rescaling alone (a rotation by `ζ^{±1}`
would make `z₃` non-real), and the rescaling is the identity by the uniqueness in Lemma 15.1.1.
-/

@[expose] public section

namespace SmoothedPolygons

open Complex Set Filter Topology
open scoped Real

namespace TriFuller

/-! ### The class of a point of the section -/

/-- A real number `x ≤ 0` lies on the wall `𝒲₀`. -/
private lemma l5a_mem_walls_of_real {w : ℂ} (him : w.im = 0) (hre : w.re ≤ 0) : w ∈ walls :=
  Or.inl (Or.inl ⟨w.re, hre, by apply Complex.ext <;> simp [him]⟩)

/-- The zero-Hamiltonian Poincaré section in Cartesian coordinates: `z ≠ 0`, `z₃ ∈ 𝒲` and
`H_F⁺(z) = 0` (the points whose angular part lies in `Ξ_{𝒲,0}`, TeX 11429–11436). -/
def sectionZero : Set (Fin 3 → ℂ) := {z | z ≠ 0 ∧ z 2 ∈ walls ∧ hamMax z = 0}

/-- The angular part of a point `z ≠ 0` with `z₃ ∈ 𝒲` lies in `Ξ_𝒲` (`ang` rescales `z₃` by a
positive real, and `𝒲` is a union of rays). -/
theorem ang_mem_XiW {z : Fin 3 → ℂ} (hz : z ≠ 0) (h : z 2 ∈ walls) : ang z ∈ XiW := by
  change ang z ∈ Xi ∧ ang z 2 ∈ walls
  refine ⟨ang_mem_Xi hz, ?_⟩
  have e : ang z 2 = (((weightedNorm z)⁻¹ ^ 3 : ℝ) : ℂ) * z 2 := by simp [ang, scale]
  rw [e]
  exact ofReal_mul_mem_walls (pow_nonneg (inv_nonneg.2 (weightedNorm_pos hz).le) 3) h

/-- `H_F⁺(ang z) = φ(z)⁻³ H_F⁺(z)` vanishes when `H_F⁺(z)` does (`hamMax_smul_scale_and_tau`). -/
theorem hamMax_ang_eq_zero {z : Fin 3 → ℂ} (hz : z ≠ 0) (h : hamMax z = 0) :
    hamMax (ang z) = 0 := by
  have e := (hamMax_smul_scale_and_tau one_mem_VT (inv_pos.2 (weightedNorm_pos hz)) z).1
  rw [one_smul] at e
  rw [show ang z = scale (weightedNorm z)⁻¹ z from rfl, e, h, mul_zero]

/-- The class in `Ξ_{𝒲,0}/V_T` of a point of the section `sectionZero` (the class of its angular
part `ang z`); the junk value `q_out` off the section. -/
noncomputable def classOf (z : Fin 3 → ℂ) : XiW0Quot :=
  open Classical in
  if h : z ∈ sectionZero then
    ⟨Quotient.mk'' ⟨ang z, ang_mem_XiW h.1 h.2.1⟩, hamMax_ang_eq_zero h.1 h.2.2⟩
  else qOut0

/-- The class of a point of the section, unfolded. -/
private lemma l5a_classOf_eq {z : Fin 3 → ℂ} (hz : z ∈ sectionZero) :
    classOf z = ⟨Quotient.mk'' ⟨ang z, ang_mem_XiW hz.1 hz.2.1⟩,
      hamMax_ang_eq_zero hz.1 hz.2.2⟩ := by
  unfold classOf
  rw [dite_eq_left hz]

/-- Two points of the section with angular parts differing by a rotation have the same class. -/
private lemma l5a_classOf_eq_of_ang {z w : Fin 3 → ℂ} (hz : z ∈ sectionZero)
    (hw : w ∈ sectionZero) {v : ℂ} (hv : v ∈ VT) (h : ang z = v • ang w) :
    classOf z = classOf w := by
  rw [l5a_classOf_eq hz, l5a_classOf_eq hw]
  exact Subtype.ext (mk_eq_mk_iff_exists_mem_VT.2 ⟨v, hv, h⟩)

/-- The virial group maps the section to itself. -/
private lemma l5a_smul_scale_mem {v : ℂ} (hv : v ∈ VT) {r : ℝ} (hr : 0 < r) {z : Fin 3 → ℂ}
    (hz : z ∈ sectionZero) : v • scale r z ∈ sectionZero := by
  refine ⟨fun h ↦ ?_, ?_, ?_⟩
  · have e := (weightedNorm_ang_smul_scale hz.1 hr hv).1
    rw [h, weightedNorm_zero] at e
    exact (mul_pos hr (weightedNorm_pos hz.1)).ne' e.symm
  · have e : (v • scale r z) 2 = v * (((r ^ 3 : ℝ) : ℂ) * z 2) := by simp [scale]
    rw [e]
    exact mul_mem_walls hv (ofReal_mul_mem_walls (by positivity) hz.2.1)
  · rw [(hamMax_smul_scale_and_tau hv hr z).1, hz.2.2, mul_zero]

/-- Every point of `Ξ_{𝒲,0}/V_T` is the class of a point of the section (of any representative
`ξ ∈ Ξ_{𝒲,0}`, for which `ang ξ = ξ`). -/
theorem exists_classOf_eq (x : XiW0Quot) : ∃ z ∈ sectionZero, classOf z = x := by
  obtain ⟨x, hx⟩ := x
  revert hx
  refine Quotient.inductionOn' x fun ξ hx ↦ ?_
  have hξ : (ξ : Fin 3 → ℂ) ∈ Xi ∧ (ξ : Fin 3 → ℂ) 2 ∈ walls := ξ.2
  have hs : (ξ : Fin 3 → ℂ) ∈ sectionZero := ⟨ne_zero_of_mem_Xi hξ.1, hξ.2, hx⟩
  refine ⟨ξ, hs, ?_⟩
  rw [l5a_classOf_eq hs]
  exact Subtype.ext (congrArg Quotient.mk'' (Subtype.ext (ang_of_mem_Xi hξ.1)))

/-- The class is invariant under the virial group: `classOf (v · (r z₁, r² z₂, r³ z₃)) =
classOf z` for `v ∈ V_T`, `r > 0` (`weightedNorm_ang_smul_scale`). -/
theorem classOf_smul_scale {v : ℂ} (hv : v ∈ VT) {r : ℝ} (hr : 0 < r) {z : Fin 3 → ℂ}
    (hz : z ∈ sectionZero) : classOf (v • scale r z) = classOf z :=
  l5a_classOf_eq_of_ang (l5a_smul_scale_mem hv hr hz) hz hv
    (weightedNorm_ang_smul_scale hz.1 hr hv).2

/-- Two points of the section have the same class exactly when they differ by the virial group
(`𝒢 ≅ ℝ_{>0} × ℤ/3`, TeX 10820–10827). -/
theorem classOf_eq_classOf_iff {z w : Fin 3 → ℂ} (hz : z ∈ sectionZero)
    (hw : w ∈ sectionZero) :
    classOf z = classOf w ↔ ∃ v ∈ VT, ∃ r : ℝ, 0 < r ∧ w = v • scale r z := by
  constructor
  · intro h
    rw [l5a_classOf_eq hz, l5a_classOf_eq hw] at h
    obtain ⟨v, hv, e⟩ := mk_eq_mk_iff_exists_mem_VT.1 (congrArg Subtype.val h.symm)
    change ang w = v • ang z at e
    refine ⟨v, hv, weightedNorm w / weightedNorm z,
      div_pos (weightedNorm_pos hw.1) (weightedNorm_pos hz.1), ?_⟩
    conv_lhs => rw [← scale_weightedNorm_ang hw.1]
    rw [e, ang, scale_smul, scale_scale, div_eq_mul_inv]
  · rintro ⟨v, hv, r, hr, rfl⟩
    exact (classOf_smul_scale hv hr hz).symm

/-- `F` maps the section to itself: `F(z) ≠ 0` (`poincare_ne_zero`), `F(z)₃ ∈ 𝒲` (the trajectory
switches on a wall) and `H_F⁺(F z) = H_F⁺(z)` (`hamMax_poincare`). -/
theorem poincare_mem_sectionZero {z : Fin 3 → ℂ} (hz : z ∈ sectionZero) :
    poincare z ∈ sectionZero := by
  have hF := poincare_ne_zero hz.1
  refine ⟨hF, ?_, by rw [hamMax_poincare hz.1]; exact hz.2.2⟩
  have h1 := ang_poincare_mem_XiW (ang_mem_XiW hz.1 hz.2.1)
  rw [ang_poincare_ang hz.1] at h1
  have h2 : ang (poincare z) 2 ∈ walls := h1.2
  have e := congrFun (scale_weightedNorm_ang hF) 2
  have e' : poincare z 2 = ((weightedNorm (poincare z) ^ 3 : ℝ) : ℂ) * ang (poincare z) 2 := by
    rw [← e]; simp [scale]
  rw [e']
  exact ofReal_mul_mem_walls (pow_nonneg (weightedNorm_pos hF).le 3) h2

/-- `F_ang` on classes is `F` on representatives: `F(classOf z) = classOf (F z)`
(`ang_poincare_ang`, TeX 11256–11265). -/
theorem poincareAngZero_classOf {z : Fin 3 → ℂ} (hz : z ∈ sectionZero) :
    poincareAngZero (classOf z) = classOf (poincare z) := by
  rw [l5a_classOf_eq hz, l5a_classOf_eq (poincare_mem_sectionZero hz)]
  exact Subtype.ext (congrArg Quotient.mk'' (Subtype.ext (ang_poincare_ang hz.1)))

/-- `τ` maps the section to itself (`tau_ne_zero`, `conj 𝒲 = 𝒲`, `H_F⁺(τ z) = H_F⁺(z)`). -/
theorem tau_mem_sectionZero {z : Fin 3 → ℂ} (hz : z ∈ sectionZero) : tau z ∈ sectionZero :=
  ⟨tau_ne_zero hz.1, conj_mem_walls hz.2.1,
    (hamMax_smul_scale_and_tau one_mem_VT one_pos z).2.trans hz.2.2⟩

/-- `τ` on classes is `τ` on representatives (`tau_ang`). -/
theorem tauZero_classOf {z : Fin 3 → ℂ} (hz : z ∈ sectionZero) :
    tauZero (classOf z) = classOf (tau z) := by
  rw [l5a_classOf_eq hz, l5a_classOf_eq (tau_mem_sectionZero hz)]
  exact Subtype.ext (congrArg Quotient.mk'' (Subtype.ext (tau_ang z)))

/-- The class map is continuous on the section (`continuousOn_ang`, the quotient map). -/
theorem continuousOn_classOf : ContinuousOn classOf sectionZero := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hc : Continuous fun z : sectionZero ↦
      (⟨Quotient.mk'' ⟨ang z, ang_mem_XiW z.2.1 z.2.2.1⟩, hamMax_ang_eq_zero z.2.1 z.2.2.2⟩ :
        XiW0Quot) :=
    Continuous.subtype_mk (continuous_quot_mk.comp (Continuous.subtype_mk
      (continuousOn_ang.comp_continuous continuous_subtype_val fun z ↦ z.2.1) _)) _
  exact hc.congr fun z ↦ (l5a_classOf_eq z.2).symm

/-- `qOutCart` and `τ(qOutCart)` represent `q_out` and `q_in` (Lemma 13.5.2). -/
theorem classOf_qOutCart :
    qOutCart ∈ sectionZero ∧ classOf qOutCart = qOut0 ∧ tau qOutCart ∈ sectionZero ∧
      classOf (tau qOutCart) = qIn0 := by
  obtain ⟨-, him, hre⟩ := qOutCart_normalization
  have h : qOutCart ∈ sectionZero :=
    ⟨qOutCart_ne_zero, l5a_mem_walls_of_real him hre.le, hamMax_qOutCart⟩
  have h' := tau_mem_sectionZero h
  refine ⟨h, ?_, h', ?_⟩
  · rw [l5a_classOf_eq h]; rfl
  · rw [l5a_classOf_eq h']; rfl

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

/-! #### Helpers: the Hamiltonian on `𝒲₀` and the coordinates of `cellPoint` -/

/-- On the wall `𝒲₀` (`z₃ = x₃ ≤ 0`) the controls `ζ`, `ζ²` tie and beat `1`:
`H_F⁺(z) = RR(z₁, i z₂) - x₃/2`. -/
private lemma l5a_hamMax_wall {z : Fin 3 → ℂ} {x₃ : ℝ} (h2 : z 2 = x₃) (hx : x₃ ≤ 0) :
    hamMax z = RR (z 0) (z 1 * I) - x₃ / 2 := by
  have hR : ∀ u : ℂ, ham z u = RR (z 0) (z 1 * I) + u.re * x₃ := by
    intro u
    rw [ham, h2, RR_eq_re_mul_add_im_mul u]
    simp
  rw [hamMax, hR, hR, hR, Complex.one_re, ζ_re, ζ_sq_re, max_self, max_eq_right (by linarith)]
  ring

/-- `RR(r₁ e^{iθ₁}, i r₂ e^{iθ₂}) = r₁ r₂ sin(θ₁ - θ₂)`. -/
private lemma l5a_RR_polar (r₁ r₂ θ₁ θ₂ : ℝ) :
    RR ((r₁ : ℂ) * exp ((θ₁ : ℂ) * I)) ((r₂ : ℂ) * exp ((θ₂ : ℂ) * I) * I) =
      r₁ * r₂ * Real.sin (θ₁ - θ₂) := by
  rw [RR_eq_re_mul_add_im_mul, Real.sin_sub]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.I_re, Complex.I_im]
  ring

/-- `RR(a, i b) = Im a Re b - Re a Im b`. -/
private lemma l5a_RR_mul_I (a b : ℂ) : RR a (b * I) = a.im * b.re - a.re * b.im := by
  simp [RR_eq_re_mul_add_im_mul]
  ring

private lemma l5a_cellPoint_zero (p : Fin 3 → ℝ) :
    cellPoint p 0 = ((1 - p 0 : ℝ) : ℂ) * exp (((p 2 - p 1 : ℝ) : ℂ) * I) := rfl

private lemma l5a_cellPoint_one (p : Fin 3 → ℝ) :
    cellPoint p 1 = (p 0 : ℂ) * exp ((p 2 : ℂ) * I) := rfl

private lemma l5a_cellPoint_two (p : Fin 3 → ℝ) :
    cellPoint p 2 = ((-2 * (1 - p 0) * p 0 * Real.sin (p 1) : ℝ) : ℂ) := rfl

/-- The imaginary parts of the coordinates of `cellPoint p`, and `x₃`. -/
private lemma l5a_cellPoint_im (p : Fin 3 → ℝ) :
    (cellPoint p 0).im = (1 - p 0) * Real.sin (p 2 - p 1) ∧
      (cellPoint p 1).im = p 0 * Real.sin (p 2) ∧ (cellPoint p 2).im = 0 ∧
      (cellPoint p 2).re = -2 * (1 - p 0) * p 0 * Real.sin (p 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [l5a_cellPoint_zero, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  · rw [l5a_cellPoint_one, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  · rw [l5a_cellPoint_two, Complex.ofReal_im]
  · rw [l5a_cellPoint_two, Complex.ofReal_re]

/-- `|z₁| = r₁ = 1 - r₂` and `|z₂| = r₂` for `r₂ ∈ [0, 1]`. -/
private lemma l5a_norm_cellPoint {p : Fin 3 → ℝ} (h0 : 0 ≤ p 0) (h1 : p 0 ≤ 1) :
    ‖cellPoint p 0‖ = 1 - p 0 ∧ ‖cellPoint p 1‖ = p 0 := by
  constructor
  · rw [l5a_cellPoint_zero, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  · rw [l5a_cellPoint_one, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg h0]

/-- `x₃ = -2 r₁ r₂ sin ψ < 0` on the open cells. -/
private lemma l5a_cellPoint_two_neg {p : Fin 3 → ℝ} (h0 : p 0 ∈ Ioo 0 1) (h1 : p 1 ∈ Ioo 0 π) :
    -2 * (1 - p 0) * p 0 * Real.sin (p 1) < 0 := by
  have hs := Real.sin_pos_of_pos_of_lt_pi h1.1 h1.2
  have : 0 < (1 - p 0) * p 0 * Real.sin (p 1) :=
    mul_pos (mul_pos (by linarith [h0.2]) h0.1) hs
  linarith

private lemma l5a_continuous_cellPoint : Continuous cellPoint := by
  refine continuous_pi fun j ↦ ?_
  fin_cases j
  · change Continuous fun p : Fin 3 → ℝ ↦ ((1 - p 0 : ℝ) : ℂ) * exp (((p 2 - p 1 : ℝ) : ℂ) * I)
    fun_prop
  · change Continuous fun p : Fin 3 → ℝ ↦ (p 0 : ℂ) * exp ((p 2 : ℂ) * I)
    fun_prop
  · change Continuous fun p : Fin 3 → ℝ ↦ ((-2 * (1 - p 0) * p 0 * Real.sin (p 1) : ℝ) : ℂ)
    fun_prop

/-- Points with cell coordinates in the closed cells lie on the section: `cellPoint p ≠ 0`
(`r₁ + r₂ = 1`), `z₃ = -2 r₁ r₂ sin ψ ≤ 0` lies on the wall `𝒲₀`, and `H_F⁺ = 0` by (15.1.1). -/
theorem cellPoint_mem_sectionZero {p : Fin 3 → ℝ} (hp : p ∈ cellDomain) :
    cellPoint p ∈ sectionZero := by
  obtain ⟨⟨h0, h1⟩, ⟨hψ0, hψ1⟩, -⟩ := hp
  have hs : 0 ≤ Real.sin (p 1) := Real.sin_nonneg_of_nonneg_of_le_pi hψ0 hψ1
  have hx : -2 * (1 - p 0) * p 0 * Real.sin (p 1) ≤ 0 := by
    have : 0 ≤ (1 - p 0) * p 0 * Real.sin (p 1) := mul_nonneg (mul_nonneg (by linarith) h0) hs
    linarith
  refine ⟨fun h ↦ ?_, ?_, ?_⟩
  · have e0 := congrFun h 0
    have e1 := congrFun h 1
    rw [l5a_cellPoint_zero, Pi.zero_apply] at e0
    rw [l5a_cellPoint_one, Pi.zero_apply] at e1
    rcases mul_eq_zero.1 e0 with e0 | e0
    · rcases mul_eq_zero.1 e1 with e1 | e1
      · have := Complex.ofReal_eq_zero.1 e0
        have := Complex.ofReal_eq_zero.1 e1
        linarith
      · exact Complex.exp_ne_zero _ e1
    · exact Complex.exp_ne_zero _ e0
  · obtain ⟨-, -, him, hre⟩ := l5a_cellPoint_im p
    exact l5a_mem_walls_of_real him (hre ▸ hx)
  · rw [l5a_hamMax_wall (l5a_cellPoint_two p) hx, l5a_cellPoint_zero, l5a_cellPoint_one,
      l5a_RR_polar, show p 2 - p 1 - p 2 = -p 1 by ring, Real.sin_neg]
    ring

/-- The class map is continuous on the closed cells. -/
theorem continuousOn_cellClass : ContinuousOn cellClass cellDomain :=
  continuousOn_classOf.comp l5a_continuous_cellPoint.continuousOn
    fun _ hp ↦ cellPoint_mem_sectionZero hp

/-- **The face identifications** (TeX 12149–12160): "We identify points along the face `r₂ = 0`,
if they have the same image under … `f(ψ, θ₂) = θ₂ - ψ = θ₁`" (on `r₂ = 0` the point is
`(e^{iθ₁}, 0, 0)`), and "along the face `r₂ = 1`, if they have the same image under the projection
`f(ψ, θ₂) = θ₂`" (the point is `(0, e^{iθ₂}, 0)`). -/
theorem cellPoint_face_identifications :
    (∀ p q : Fin 3 → ℝ, p 0 = 0 → q 0 = 0 → p 2 - p 1 = q 2 - q 1 → cellPoint p = cellPoint q) ∧
      ∀ p q : Fin 3 → ℝ, p 0 = 1 → q 0 = 1 → p 2 = q 2 → cellPoint p = cellPoint q := by
  constructor
  · intro p q hp hq h
    funext j
    fin_cases j
    · change cellPoint p 0 = cellPoint q 0
      rw [l5a_cellPoint_zero, l5a_cellPoint_zero, hp, hq, h]
    · change cellPoint p 1 = cellPoint q 1
      rw [l5a_cellPoint_one, l5a_cellPoint_one, hp, hq]
      simp
    · change cellPoint p 2 = cellPoint q 2
      rw [l5a_cellPoint_two, l5a_cellPoint_two, hp, hq]
      simp
  · intro p q hp hq h
    funext j
    fin_cases j
    · change cellPoint p 0 = cellPoint q 0
      rw [l5a_cellPoint_zero, l5a_cellPoint_zero, hp, hq]
      simp
    · change cellPoint p 1 = cellPoint q 1
      rw [l5a_cellPoint_one, l5a_cellPoint_one, hp, hq, h]
    · change cellPoint p 2 = cellPoint q 2
      rw [l5a_cellPoint_two, l5a_cellPoint_two, hp, hq]
      simp

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
private lemma l5a_conj_polar (a θ : ℝ) :
    starRingEnd ℂ ((a : ℂ) * exp ((θ : ℂ) * I)) = (a : ℂ) * exp (((-θ : ℝ) : ℂ) * I) := by
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I]
  push_cast
  ring_nf

private lemma l5a_exp_add (x y : ℝ) :
    exp (((x + y : ℝ) : ℂ) * I) = exp ((x : ℂ) * I) * exp ((y : ℂ) * I) := by
  rw [← Complex.exp_add]
  push_cast
  ring_nf

/-- `τ(cellPoint p) = cellPoint (r₂, π - ψ, c - θ₂)` whenever `e^{ic} = -1`. -/
private lemma l5a_tau_cellPoint_aux (p : Fin 3 → ℝ) {c : ℝ} (hc : exp ((c : ℂ) * I) = -1) :
    tau (cellPoint p) = cellPoint ![p 0, π - p 1, c - p 2] := by
  have hπ : exp (((-π : ℝ) : ℂ) * I) = -1 := by
    push_cast
    rw [neg_mul]
    exact Complex.exp_neg_pi_mul_I
  funext j
  fin_cases j
  · change starRingEnd ℂ (cellPoint p 0) =
      ((1 - p 0 : ℝ) : ℂ) * exp (((c - p 2 - (π - p 1) : ℝ) : ℂ) * I)
    rw [l5a_cellPoint_zero, l5a_conj_polar,
      show c - p 2 - (π - p 1) = c + (-π + -(p 2 - p 1)) by ring, l5a_exp_add, l5a_exp_add, hc,
      hπ]
    ring
  · change -starRingEnd ℂ (cellPoint p 1) = (p 0 : ℂ) * exp (((c - p 2 : ℝ) : ℂ) * I)
    rw [l5a_cellPoint_one, l5a_conj_polar, show c - p 2 = c + -p 2 by ring, l5a_exp_add, hc]
    ring
  · change starRingEnd ℂ (cellPoint p 2) =
      ((-2 * (1 - p 0) * p 0 * Real.sin (π - p 1) : ℝ) : ℂ)
    rw [l5a_cellPoint_two, Complex.conj_ofReal, Real.sin_pi_sub]

theorem tau_cellPoint (p : Fin 3 → ℝ) : tau (cellPoint p) = cellPoint (cellTau p) := by
  change tau (cellPoint p) = cellPoint ![p 0, π - p 1, (if 0 ≤ p 2 then π else -π) - p 2]
  split_ifs
  · exact l5a_tau_cellPoint_aux p Complex.exp_pi_mul_I
  · refine l5a_tau_cellPoint_aux p ?_
    push_cast
    rw [neg_mul]
    exact Complex.exp_neg_pi_mul_I

/-- `τ` maps the coordinate domain to itself and is `τ` on classes. -/
theorem cellClass_cellTau {p : Fin 3 → ℝ} (hp : p ∈ cellDomain) :
    cellTau p ∈ cellDomain ∧ cellClass (cellTau p) = tauZero (cellClass p) := by
  obtain ⟨h0, ⟨h1, h1'⟩, ⟨h2, h2'⟩⟩ := hp
  refine ⟨⟨h0, ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · change 0 ≤ π - p 1
    linarith
  · change π - p 1 ≤ π
    linarith
  · change (if 0 ≤ p 2 then π else -π) - p 2 ∈ Icc (-π) π
    split_ifs with h
    · constructor <;> linarith
    · constructor <;> linarith
  · unfold cellClass
    rw [← tau_cellPoint, tauZero_classOf (cellPoint_mem_sectionZero ⟨h0, ⟨h1, h1'⟩, ⟨h2, h2'⟩⟩)]

/-! ### Inverse coordinates -/

/-- The positive root of `a s + b s² = 1` (`a, b ≥ 0`, `a + b > 0`; Lemma 15.1.1): `s = 1/a` if
`b = 0`, else `s = (-a + √(a² + 4b))/(2b)`. -/
private lemma l5a_root_spec {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) :
    0 < (if b = 0 then a⁻¹ else (-a + √(a ^ 2 + 4 * b)) / (2 * b)) ∧
      a * (if b = 0 then a⁻¹ else (-a + √(a ^ 2 + 4 * b)) / (2 * b)) +
        b * (if b = 0 then a⁻¹ else (-a + √(a ^ 2 + 4 * b)) / (2 * b)) ^ 2 = 1 := by
  split_ifs with hb0
  · have ha0 : 0 < a := by linarith
    refine ⟨inv_pos.2 ha0, ?_⟩
    rw [hb0, zero_mul, add_zero, mul_inv_cancel₀ ha0.ne']
  · have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    have hsq := Real.sq_sqrt (by positivity : 0 ≤ a ^ 2 + 4 * b)
    have hgt : a < √(a ^ 2 + 4 * b) := (Real.lt_sqrt ha).2 (by linarith)
    refine ⟨div_pos (by linarith) (by linarith), ?_⟩
    set d := √(a ^ 2 + 4 * b)
    have hs : 2 * b * ((-a + d) / (2 * b)) = -a + d := by field_simp
    have key : 4 * b * (a * ((-a + d) / (2 * b)) + b * ((-a + d) / (2 * b)) ^ 2 - 1) = 0 := by
      have e : 4 * b * (a * ((-a + d) / (2 * b)) + b * ((-a + d) / (2 * b)) ^ 2 - 1) =
          2 * a * (2 * b * ((-a + d) / (2 * b))) + (2 * b * ((-a + d) / (2 * b))) ^ 2 - 4 * b := by
        ring
      rw [e, hs]
      linear_combination hsq
    have := (mul_eq_zero.1 key).resolve_left (by positivity)
    linarith

/-- Uniqueness of the positive root of `a s + b s² = 1`: `s ↦ a s + b s²` is strictly increasing
on `(0, ∞)`. -/
private lemma l5a_root_unique {a b s t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b)
    (hs : 0 < s) (ht : 0 < t) (h : a * s + b * s ^ 2 = a * t + b * t ^ 2) : s = t := by
  have hpos : 0 < a + b * (s + t) := by
    rcases ha.lt_or_eq with ha' | ha'
    · nlinarith [mul_nonneg hb (add_pos hs ht).le]
    · rw [← ha', zero_add]
      exact mul_pos (by linarith) (add_pos hs ht)
  have e : (s - t) * (a + b * (s + t)) = 0 := by linear_combination h
  have := (mul_eq_zero.1 e).resolve_right hpos.ne'
  linarith

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
  obtain ⟨⟨h0, h0'⟩, ⟨h1, h1'⟩, ⟨h2, h2'⟩⟩ := hp
  obtain ⟨na, nb⟩ := l5a_norm_cellPoint h0.le h0'.le
  have hsq : √((1 - p 0) ^ 2 + 4 * p 0) = 1 + p 0 := by
    rw [show (1 - p 0) ^ 2 + 4 * p 0 = (1 + p 0) ^ 2 by ring]
    exact Real.sqrt_sq (by linarith)
  have hs : (-(1 - p 0) + √((1 - p 0) ^ 2 + 4 * p 0)) / (2 * p 0) = 1 := by
    rw [hsq, div_eq_one_iff_eq (by positivity)]
    ring
  have harg1 : arg (cellPoint p 1) = p 2 := by
    rw [l5a_cellPoint_one, Complex.arg_real_mul _ h0, Complex.arg_exp_mul_I, toIocMod_eq_self]
    constructor <;> linarith
  have harg0 : arg (cellPoint p 0) = p 2 - p 1 -
      toIocDiv Real.two_pi_pos (-π) (p 2 - p 1) • (2 * π) := by
    rw [l5a_cellPoint_zero, Complex.arg_real_mul _ (by linarith), Complex.arg_exp_mul_I]
    exact eq_sub_of_add_eq (toIocMod_add_toIocDiv_zsmul _ _ _)
  funext j
  fin_cases j
  · change (if ‖cellPoint p 1‖ = 0 then ‖cellPoint p 0‖⁻¹ else
      (-‖cellPoint p 0‖ + √(‖cellPoint p 0‖ ^ 2 + 4 * ‖cellPoint p 1‖)) /
        (2 * ‖cellPoint p 1‖)) ^ 2 * ‖cellPoint p 1‖ = p 0
    rw [na, nb, ite_eq_right h0.ne', hs]
    ring
  · change toIcoMod Real.two_pi_pos 0 (arg (cellPoint p 1) - arg (cellPoint p 0)) = p 1
    rw [harg1, harg0, show ∀ x : ℝ, p 2 - (p 2 - p 1 - x) = p 1 + x by intro x; ring,
      toIcoMod_add_zsmul, toIcoMod_eq_self]
    constructor <;> linarith
  · exact harg1

/-- A point `z` of the section with `z₃ ∈ ℝ_{<0}` has cell coordinates: `r₂ ∈ (0, 1)`,
`ψ ∈ (0, π)` (by (15.1.1), `x₃ < 0` forces `r₁ r₂ ≠ 0` and `sin ψ > 0`), `θ₂ ∈ (-π, π]`, and
`cellPoint (cellCoords z)` is the rescaling of `z` with `r₁ + r₂ = 1`, so it has the same
class. -/
theorem cellClass_cellCoords {z : Fin 3 → ℂ} (hz : z ∈ sectionZero) (h₃ : (z 2).im = 0)
    (h₃' : (z 2).re < 0) :
    (cellCoords z 0 ∈ Ioo 0 1 ∧ cellCoords z 1 ∈ Ioo 0 π ∧ cellCoords z 2 ∈ Ioc (-π) π) ∧
      cellClass (cellCoords z) = classOf z := by
  set a := ‖z 0‖ with ha_def
  set b := ‖z 1‖ with hb_def
  set θ₁ := arg (z 0) with hθ₁
  set θ₂ := arg (z 1) with hθ₂
  set x₃ := (z 2).re with hx₃
  have hz2 : z 2 = (x₃ : ℂ) := Complex.ext (by simp [x₃]) (by simp [h₃])
  have hz0 : z 0 = (a : ℂ) * exp ((θ₁ : ℂ) * I) := (Complex.norm_mul_exp_arg_mul_I _).symm
  have hz1 : z 1 = (b : ℂ) * exp ((θ₂ : ℂ) * I) := (Complex.norm_mul_exp_arg_mul_I _).symm
  -- (15.1.1): `x₃ = 2 r₁ r₂ sin(θ₁ - θ₂)`, so `r₁ r₂ ≠ 0` and `sin ψ > 0`
  have hH : a * b * Real.sin (θ₁ - θ₂) - x₃ / 2 = 0 := by
    have h := hz.2.2
    rwa [l5a_hamMax_wall hz2 h₃'.le, hz0, hz1, l5a_RR_polar] at h
  have hprod : a * b * Real.sin (θ₁ - θ₂) < 0 := by linarith
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have ha : 0 < a := by
    rcases ha0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hprod
      simp at hprod
  have hb : 0 < b := by
    rcases hb0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hprod
      simp at hprod
  have hsin : 0 < Real.sin (θ₂ - θ₁) := by
    have : Real.sin (θ₁ - θ₂) < 0 := by
      by_contra hc
      push Not at hc
      have := mul_nonneg (mul_nonneg ha0 hb0) hc
      linarith
    rw [show θ₂ - θ₁ = -(θ₁ - θ₂) by ring, Real.sin_neg]
    linarith
  -- Lemma 15.1.1: the rescaling `s` with `r₁ + r₂ = 1`
  obtain ⟨hs, hs1⟩ := l5a_root_spec ha0 hb0 (by linarith)
  rw [ite_eq_right hb.ne'] at hs hs1
  set s := (-a + √(a ^ 2 + 4 * b)) / (2 * b) with hs_def
  -- `ψ = θ₂ - θ₁` reduced to `[0, 2π)` lies in `(0, π)`
  set ψ := toIcoMod Real.two_pi_pos 0 (θ₂ - θ₁) with hψ_def
  have hψ : ψ = θ₂ - θ₁ - toIcoDiv Real.two_pi_pos 0 (θ₂ - θ₁) • (2 * π) :=
    eq_sub_of_add_eq (toIcoMod_add_toIcoDiv_zsmul _ _ _)
  set n := toIcoDiv Real.two_pi_pos 0 (θ₂ - θ₁)
  have hψmem : ψ ∈ Ico 0 (0 + 2 * π) := toIcoMod_mem_Ico _ _ _
  have hsinψ : Real.sin ψ = Real.sin (θ₂ - θ₁) := by
    rw [hψ, zsmul_eq_mul, Real.sin_sub_int_mul_two_pi]
  have hψpos : 0 < ψ := by
    rcases hψmem.1.lt_or_eq with h | h
    · exact h
    · rw [← h, Real.sin_zero] at hsinψ
      linarith
  have hψlt : ψ < π := by
    by_contra hc
    push Not at hc
    have h1 : 0 ≤ Real.sin (ψ - π) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hψmem.2])
    rw [Real.sin_sub_pi] at h1
    linarith
  have hc : cellCoords z = ![s ^ 2 * b, ψ, θ₂] := by
    have e : (if b = 0 then a⁻¹ else (-a + √(a ^ 2 + 4 * b)) / (2 * b)) = s :=
      ite_eq_right hb.ne'
    exact congrArg (fun t ↦ ![t ^ 2 * b, ψ, θ₂]) e
  have has : 1 - s ^ 2 * b = a * s := by linarith
  rw [hc]
  refine ⟨⟨?_, ⟨hψpos, hψlt⟩, ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩⟩, ?_⟩
  · change s ^ 2 * b ∈ Ioo 0 1
    have : 0 < a * s := mul_pos ha hs
    constructor
    · positivity
    · linarith
  -- `cellPoint (cellCoords z)` is the rescaling `(s z₁, s² z₂, s³ z₃)` of `z`
  change classOf (cellPoint ![s ^ 2 * b, ψ, θ₂]) = classOf z
  have e : cellPoint ![s ^ 2 * b, ψ, θ₂] = (1 : ℂ) • scale s z := by
    funext j
    fin_cases j
    · change ((1 - s ^ 2 * b : ℝ) : ℂ) * exp (((θ₂ - ψ : ℝ) : ℂ) * I) = 1 * ((s : ℂ) * z 0)
      have h2π : exp ((((n : ℝ) * (2 * π) : ℝ) : ℂ) * I) = 1 := by
        rw [← Complex.exp_int_mul_two_pi_mul_I n]
        push_cast
        ring_nf
      rw [show θ₂ - ψ = θ₁ + (n : ℝ) * (2 * π) by rw [hψ, zsmul_eq_mul]; ring, l5a_exp_add,
        h2π, hz0, has]
      push_cast
      ring
    · change ((s ^ 2 * b : ℝ) : ℂ) * exp ((θ₂ : ℂ) * I) = 1 * ((s : ℂ) ^ 2 * z 1)
      rw [hz1]
      push_cast
      ring
    · change ((-2 * (1 - s ^ 2 * b) * (s ^ 2 * b) * Real.sin ψ : ℝ) : ℂ) =
        1 * ((s : ℂ) ^ 3 * z 2)
      have h : -2 * (1 - s ^ 2 * b) * (s ^ 2 * b) * Real.sin ψ = s ^ 3 * x₃ := by
        rw [hsinψ, has, show θ₂ - θ₁ = -(θ₁ - θ₂) by ring, Real.sin_neg]
        linear_combination (2 * s ^ 3) * hH
      rw [h, hz2]
      push_cast
      ring
  rw [e, classOf_smul_scale one_mem_VT hs hz]

/-- The cell coordinates `(r₂, ψ, θ₂)` of the fixed point `q_out` (13.5.1): numerically
`(0.267949…, 0.1705935…, 2.91574…)`, which Remark 15.3.1 prints as the coordinates of `q_in`
(REPORT.md, E75; `remark15_3_1`). -/
noncomputable def pOut : Fin 3 → ℝ := cellCoords qOutCart

/-- The cell coordinates of the fixed point `q_in = τ(q_out)`:
`τ(pOut) = (0.267949…, 2.9709991…, 0.2258526…)`. -/
noncomputable def pIn : Fin 3 → ℝ := cellTau pOut

/-! ### The big open cells (Definition 15.1.2) -/

/-! #### Helpers: the first control on the wall `𝒲₀` (Lemma 13.2.6) -/

/-- A vector with a positive first nonzero entry. -/
private lemma l5a_lexPos_of {x : Fin 3 → ℝ}
    (h : 0 < x 0 ∨ (x 0 = 0 ∧ 0 < x 1) ∨ (x 0 = 0 ∧ x 1 = 0 ∧ 0 < x 2)) : LexPos x := by
  rcases h with h | ⟨h0, h1⟩ | ⟨h0, h1, h2⟩
  · exact ⟨0, fun j hj ↦ absurd hj (Fin.not_lt_zero j), h⟩
  · refine ⟨1, fun j hj ↦ ?_, h1⟩
    fin_cases j
    · exact h0
    · exact absurd hj (by decide)
    · exact absurd hj (by decide)
  · refine ⟨2, fun j hj ↦ ?_, h2⟩
    fin_cases j
    · exact h0
    · exact h1
    · exact absurd hj (by decide)

/-- The lexicographic order is asymmetric. -/
private lemma l5a_lexLt_asymm {v w : Fin 3 → ℝ} (h : LexLt v w) : ¬ LexLt w v := by
  rintro ⟨j, hj, hpj⟩
  obtain ⟨k, hk, hpk⟩ := h
  simp only [Pi.sub_apply] at hj hpj hk hpk
  rcases lt_trichotomy j k with hjk | rfl | hkj
  · have := hk j hjk
    linarith
  · linarith
  · have := hj k hkj
    linarith

/-- A control whose control vector beats the other two is the first control (Lemma 13.2.6, the
case `V_{T,max} = {u}`). -/
private lemma l5a_firstControl_of_lexLt {z : Fin 3 → ℂ} (hz : z ≠ 0) {u : ℂ} (hu : u ∈ VT)
    (h : ∀ v ∈ VT, v ≠ u → LexLt (controlVector z v) (controlVector z u)) :
    firstControl z = u := by
  have hmax : lexMaxControls z = {u} := by
    ext w
    simp only [lexMaxControls, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hw, hmax⟩
      by_contra hne
      exact hmax u hu (h w hw hne)
    · rintro rfl
      refine ⟨hu, fun v hv hlt ↦ ?_⟩
      by_cases hvw : v = w
      · subst hvw
        obtain ⟨k, -, hk⟩ := hlt
        simp at hk
      · exact l5a_lexLt_asymm (h v hv hvw) hlt
  exact (firstControl_eq_iff hz).2 ((lemma13_2_6 hz).1 u hmax)

/-- **The first control on `𝒲₀`** (TeX 12111–12121, Lemma 13.2.6): if `z₃ = x₃ < 0`, the controls
`ζ`, `ζ²` tie at `z₃` and beat `1` (`RR(z₃, ζ) - RR(z₃, 1) = -3x₃/2 > 0`); the tie is broken by
`RR(z₂, ζ) - RR(z₂, ζ²) = √3 y₂`, then by `RR(z₁, ζ) - RR(z₁, ζ²) = √3 y₁`. -/
theorem firstControl_eq_of_ofReal_neg {z : Fin 3 → ℂ} {x₃ : ℝ} (h2 : z 2 = x₃) (hx : x₃ < 0) :
    ((0 < (z 1).im ∨ ((z 1).im = 0 ∧ 0 < (z 0).im)) → firstControl z = ζ) ∧
      (((z 1).im < 0 ∨ ((z 1).im = 0 ∧ (z 0).im < 0)) → firstControl z = ζ ^ 2) := by
  have hz : z ≠ 0 := by
    intro h
    have e := congrFun h 2
    rw [h2, Pi.zero_apply, Complex.ofReal_eq_zero] at e
    linarith
  have h3 : 0 < √3 := by positivity
  have key : ∀ v w : ℂ, (controlVector z v - controlVector z w) 0 = (v - w).re * x₃ ∧
      (controlVector z v - controlVector z w) 1 = (v - w).re * (z 1).re + (v - w).im * (z 1).im ∧
      (controlVector z v - controlVector z w) 2 =
        (v - w).re * (z 0).re + (v - w).im * (z 0).im := by
    intro v w
    obtain ⟨e0, e1, e2⟩ := controlVector_sub_apply z v w
    rw [e0, e1, e2, h2, RR_eq_re_mul_add_im_mul, RR_eq_re_mul_add_im_mul,
      RR_eq_re_mul_add_im_mul]
    simp
  have hζ1 : LexLt (controlVector z 1) (controlVector z ζ) := by
    apply l5a_lexPos_of
    left
    rw [(key ζ 1).1, Complex.sub_re, ζ_re, Complex.one_re]
    linarith
  have hζ21 : LexLt (controlVector z 1) (controlVector z (ζ ^ 2)) := by
    apply l5a_lexPos_of
    left
    rw [(key (ζ ^ 2) 1).1, Complex.sub_re, ζ_sq_re, Complex.one_re]
    linarith
  constructor
  · intro hy
    refine l5a_firstControl_of_lexLt hz ζ_mem_VT fun v hv hne ↦ ?_
    rcases mem_VT.1 hv with rfl | rfl | rfl
    · exact hζ1
    · exact absurd rfl hne
    · apply l5a_lexPos_of
      obtain ⟨k0, k1, k2⟩ := key ζ (ζ ^ 2)
      rw [k0, k1, k2]
      simp only [Complex.sub_re, Complex.sub_im, ζ_re, ζ_im, ζ_sq_re, ζ_sq_im]
      rcases hy with hy | ⟨hy0, hy1⟩
      · right; left
        constructor
        · ring
        · nlinarith
      · right; right
        refine ⟨by ring, by rw [hy0]; ring, by nlinarith⟩
  · intro hy
    refine l5a_firstControl_of_lexLt hz ζ_sq_mem_VT fun v hv hne ↦ ?_
    rcases mem_VT.1 hv with rfl | rfl | rfl
    · exact hζ21
    · apply l5a_lexPos_of
      obtain ⟨k0, k1, k2⟩ := key (ζ ^ 2) ζ
      rw [k0, k1, k2]
      simp only [Complex.sub_re, Complex.sub_im, ζ_re, ζ_im, ζ_sq_re, ζ_sq_im]
      rcases hy with hy | ⟨hy0, hy1⟩
      · right; left
        constructor
        · ring
        · nlinarith
      · right; right
        refine ⟨by ring, by rw [hy0]; ring, by nlinarith⟩
    · exact absurd rfl hne

private lemma l5a_ζ_ne_ζ_sq : ζ ≠ ζ ^ 2 := by
  intro h
  have := congrArg Complex.im h
  rw [ζ_im, ζ_sq_im] at this
  have h3 : 0 < √3 := by positivity
  linarith

/-- If `z` and `w` lie on the section with `z₃, w₃ ∈ ℝ`, `z₃ < 0`, and have the same class, then
`w = (r z₁, r² z₂, r³ z₃)` for some `r > 0` (a rotation by `ζ` or `ζ²` would make `w₃`
non-real). -/
private lemma l5a_eq_scale_of_classOf_eq {z w : Fin 3 → ℂ} (hz : z ∈ sectionZero)
    (hw : w ∈ sectionZero) (hz3 : (z 2).im = 0) (hz3' : (z 2).re < 0) (hw3 : (w 2).im = 0)
    (h : classOf z = classOf w) : ∃ r : ℝ, 0 < r ∧ w = scale r z := by
  obtain ⟨v, hv, r, hr, rfl⟩ := (classOf_eq_classOf_iff hz hw).1 h
  refine ⟨r, hr, ?_⟩
  have e : (v • scale r z) 2 = v * (((r ^ 3 : ℝ) : ℂ) * z 2) := by simp [scale]
  rw [e, Complex.mul_im, Complex.re_ofReal_mul, Complex.im_ofReal_mul, hz3, mul_zero, mul_zero,
    zero_add] at hw3
  have hvim : v.im = 0 := by
    rcases mul_eq_zero.1 hw3 with h | h
    · exact h
    · exfalso
      have : 0 < r ^ 3 := pow_pos hr 3
      nlinarith
  have h3 : 0 < √3 := by positivity
  rcases mem_VT.1 hv with rfl | rfl | rfl
  · rw [one_smul]
  · rw [ζ_im] at hvim
    linarith
  · rw [ζ_sq_im] at hvim
    linarith

/-- On the open cells, the class determines the cell coordinates: if `cellClass p = cellClass q`,
then `cellPoint q = (r z₁, r² z₂, r³ z₃)` with `z = cellPoint p` and `r > 0`, and `r = 1` by
`r₁ + r₂ = 1` (the uniqueness in Lemma 15.1.1); `cellCoords` inverts `cellPoint`. -/
private lemma l5a_eq_of_cellClass_eq {p q : Fin 3 → ℝ}
    (hp : p 0 ∈ Ioo 0 1 ∧ p 1 ∈ Ioo 0 π ∧ p 2 ∈ Ioc (-π) π)
    (hq : q 0 ∈ Ioo 0 1 ∧ q 1 ∈ Ioo 0 π ∧ q 2 ∈ Ioc (-π) π) (h : cellClass p = cellClass q) :
    p = q := by
  have hdom : ∀ p : Fin 3 → ℝ, (p 0 ∈ Ioo 0 1 ∧ p 1 ∈ Ioo 0 π ∧ p 2 ∈ Ioc (-π) π) →
      p ∈ cellDomain := fun p hp ↦
    ⟨⟨hp.1.1.le, hp.1.2.le⟩, ⟨hp.2.1.1.le, hp.2.1.2.le⟩, ⟨hp.2.2.1.le, hp.2.2.2⟩⟩
  obtain ⟨-, -, hp3, hp3'⟩ := l5a_cellPoint_im p
  obtain ⟨-, -, hq3, -⟩ := l5a_cellPoint_im q
  obtain ⟨r, hr, e⟩ := l5a_eq_scale_of_classOf_eq (cellPoint_mem_sectionZero (hdom p hp))
    (cellPoint_mem_sectionZero (hdom q hq)) hp3 (hp3' ▸ l5a_cellPoint_two_neg hp.1 hp.2.1) hq3 h
  obtain ⟨np0, np1⟩ := l5a_norm_cellPoint hp.1.1.le hp.1.2.le
  obtain ⟨nq0, nq1⟩ := l5a_norm_cellPoint hq.1.1.le hq.1.2.le
  have e0 : 1 - q 0 = r * (1 - p 0) := by
    rw [← nq0, ← np0, e]
    simp [scale, abs_of_pos hr]
  have e1 : q 0 = r ^ 2 * p 0 := by
    rw [← nq1, ← np1, e]
    simp [scale, abs_of_pos hr]
  have hr1 : r = 1 := l5a_root_unique (a := 1 - p 0) (b := p 0) (by linarith [hp.1.2])
    hp.1.1.le (by linarith) hr one_pos (by linear_combination -e0 - e1)
  rw [hr1, scale_one] at e
  rw [← cellCoords_cellPoint hp, ← cellCoords_cellPoint hq, e]

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
  constructor
  · rintro ⟨p, ⟨h0, h1, h2⟩, rfl⟩
    obtain ⟨hy1, hy2, h3, h3'⟩ := l5a_cellPoint_im p
    have hx := l5a_cellPoint_two_neg h0 h1
    refine ⟨cellPoint p,
      cellPoint_mem_sectionZero ⟨⟨h0.1.le, h0.2.le⟩, ⟨h1.1.le, h1.2.le⟩, ⟨h2.1.le, by
        linarith [h2.2, Real.pi_pos]⟩⟩, rfl, h3, h3' ▸ hx, ?_⟩
    refine (firstControl_eq_of_ofReal_neg (l5a_cellPoint_two p) hx).2 ?_
    rw [hy1, hy2]
    rcases h2.2.lt_or_eq with h | h
    · left
      exact mul_neg_of_pos_of_neg h0.1 (Real.sin_neg_of_neg_of_neg_pi_lt h h2.1)
    · right
      rw [h, Real.sin_zero, mul_zero, zero_sub, Real.sin_neg]
      refine ⟨rfl, ?_⟩
      have := Real.sin_pos_of_pos_of_lt_pi h1.1 h1.2
      nlinarith [h0.2]
  · rintro ⟨z, hz, rfl, h3, h3', hfc⟩
    obtain ⟨⟨c0, c1, c2⟩, hc⟩ := cellClass_cellCoords hz h3 h3'
    refine ⟨cellCoords z, ⟨c0, c1, c2.1, ?_⟩, hc⟩
    change arg (z 1) ≤ 0
    by_contra hpos
    push Not at hpos
    have hz2 : z 2 = ((z 2).re : ℂ) := Complex.ext (by simp) (by simp [h3])
    have hy : 0 < (z 1).im ∨ ((z 1).im = 0 ∧ 0 < (z 0).im) := by
      rcases (Complex.arg_nonneg_iff.1 hpos.le).lt_or_eq with h | h
      · exact Or.inl h
      · right
        refine ⟨h.symm, ?_⟩
        have hre : (z 1).re < 0 := by
          by_contra hre
          push Not at hre
          exact hpos.ne' (Complex.arg_eq_zero_iff.2 ⟨hre, h.symm⟩)
        have hH := hz.2.2
        rw [l5a_hamMax_wall hz2 h3'.le, l5a_RR_mul_I, ← h, mul_zero, sub_zero] at hH
        nlinarith
    exact l5a_ζ_ne_ζ_sq (((firstControl_eq_of_ofReal_neg hz2 h3').1 hy).symm.trans hfc)

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
  set z : Fin 3 → ℂ := ![(r₁ : ℂ) * exp ((θ₁ : ℂ) * I), (r₂ : ℂ) * exp ((θ₂ : ℂ) * I), (x₃ : ℂ)]
  -- `H_F⁺(z) = H_F(z, ζ) = RR(z₁, i z₂) - x₃/2 = r₁ r₂ sin(θ₁ - θ₂) - x₃/2`
  have hH : hamMax z = r₁ * r₂ * Real.sin (θ₁ - θ₂) - x₃ / 2 := by
    rw [l5a_hamMax_wall (z := z) rfl hx₃]
    exact congrArg (· - x₃ / 2) (l5a_RR_polar r₁ r₂ θ₁ θ₂)
  rw [hH]
  refine ⟨⟨fun h ↦ by linarith, fun h ↦ by linarith⟩, fun h1 h2 hx h ↦ ?_⟩
  have hs : r₁ * r₂ * Real.sin (θ₁ - θ₂) < 0 := by linarith
  have hrr : r₁ * r₂ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hs
    exact lt_irrefl _ hs
  refine ⟨hrr, ?_⟩
  have hpos : 0 < r₁ * r₂ := lt_of_le_of_ne (mul_nonneg h1 h2) (Ne.symm hrr)
  have hneg : Real.sin (θ₁ - θ₂) < 0 := by
    by_contra hc
    push Not at hc
    nlinarith
  rw [show θ₂ - θ₁ = -(θ₁ - θ₂) by ring, Real.sin_neg]
  linarith

/-- **Lemma 15.1.1** (`lem:cell-rescale`, label of this formalization; unlabelled, TeX
12060–12071). "For each `z = (z₁, z₂, z₃) ≠ 0` satisfying (15.1.1), there is a unique rescaling by a
positive scalar in the virial group so that `r₁ + r₂ = 1` (and `r₁, r₂ ≥ 0`)."

The book's proof: if `r₁ = r₂ = 0`, then `z = 0` by (15.1.1), contrary to assumption; hence
`r₁ + r₂ > 0`, and the quadratic equation `r₁/s + r₂/s² = 1` has a unique positive root `s`; scale
`r_i ↦ r_i/s^i` (the rescaling `scale (1/s)`; uniqueness because `s ↦ r₁ s + r₂ s²` is strictly
increasing on `(0, ∞)`). -/
theorem lemma15_1_1 {z : Fin 3 → ℂ} (hz : z ≠ 0)
    (h₃ : z 2 = ((2 * ‖z 0‖ * ‖z 1‖ * Real.sin (arg (z 0) - arg (z 1)) : ℝ) : ℂ)) :
    ∃! s : ℝ, 0 < s ∧ ‖scale s z 0‖ + ‖scale s z 1‖ = 1 := by
  have ha : 0 ≤ ‖z 0‖ := norm_nonneg _
  have hb : 0 ≤ ‖z 1‖ := norm_nonneg _
  -- `r₁ = r₂ = 0` would force `z = 0` by (15.1.1)
  have hab : 0 < ‖z 0‖ + ‖z 1‖ := by
    by_contra hc
    have ha0 : ‖z 0‖ = 0 := by linarith
    have hb0 : ‖z 1‖ = 0 := by linarith
    apply hz
    funext j
    fin_cases j
    · exact norm_eq_zero.1 ha0
    · exact norm_eq_zero.1 hb0
    · change z 2 = 0
      rw [h₃, ha0]
      simp
  have hnorm : ∀ s : ℝ, 0 < s →
      ‖scale s z 0‖ + ‖scale s z 1‖ = ‖z 0‖ * s + ‖z 1‖ * s ^ 2 := by
    intro s hs
    simp [scale, abs_of_pos hs]
    ring
  -- the unique positive root of `r₁ s + r₂ s² = 1`
  obtain ⟨hs, hs1⟩ := l5a_root_spec ha hb hab
  refine ⟨_, ⟨hs, by rw [hnorm _ hs]; exact hs1⟩, fun t ⟨ht, ht1⟩ ↦ ?_⟩
  rw [hnorm t ht] at ht1
  exact l5a_root_unique ha hb hab ht hs (ht1.trans hs1.symm)

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
  have hdom : ∀ p : Fin 3 → ℝ, (p 0 ∈ Ioo 0 1 ∧ p 1 ∈ Ioo 0 π ∧ p 2 ∈ Ioc (-π) π) →
      p ∈ cellDomain := fun p hp ↦
    ⟨⟨hp.1.1.le, hp.1.2.le⟩, ⟨hp.2.1.1.le, hp.2.1.2.le⟩, ⟨hp.2.2.1.le, hp.2.2.2⟩⟩
  have hone : ∀ p ∈ openBoxOne, p 0 ∈ Ioo 0 1 ∧ p 1 ∈ Ioo 0 π ∧ p 2 ∈ Ioc (-π) π :=
    fun p ⟨h0, h1, h2⟩ ↦ ⟨h0, h1, ⟨by linarith [h2.1, Real.pi_pos], h2.2.le⟩⟩
  have htwo : ∀ p ∈ openBoxTwo, p 0 ∈ Ioo 0 1 ∧ p 1 ∈ Ioo 0 π ∧ p 2 ∈ Ioc (-π) π :=
    fun p ⟨h0, h1, h2⟩ ↦ ⟨h0, h1, ⟨h2.1, by linarith [h2.2, Real.pi_pos]⟩⟩
  -- the first control is `ζ` on the first box, `ζ²` on the second (`y₂ ≷ 0`)
  have hfc1 : ∀ p ∈ openBoxOne, firstControl (cellPoint p) = ζ := by
    rintro p ⟨h0, h1, h2⟩
    obtain ⟨-, hy2, -, -⟩ := l5a_cellPoint_im p
    refine (firstControl_eq_of_ofReal_neg (l5a_cellPoint_two p) (l5a_cellPoint_two_neg h0 h1)).1
      (Or.inl ?_)
    rw [hy2]
    exact mul_pos h0.1 (Real.sin_pos_of_pos_of_lt_pi h2.1 h2.2)
  have hfc2 : ∀ p ∈ openBoxTwo, firstControl (cellPoint p) = ζ ^ 2 := by
    rintro p ⟨h0, h1, h2⟩
    obtain ⟨-, hy2, -, -⟩ := l5a_cellPoint_im p
    refine (firstControl_eq_of_ofReal_neg (l5a_cellPoint_two p) (l5a_cellPoint_two_neg h0 h1)).2
      (Or.inl ?_)
    rw [hy2]
    exact mul_neg_of_pos_of_neg h0.1 (Real.sin_neg_of_neg_of_neg_pi_lt h2.2 h2.1)
  -- the points of the open boxes give points of the open cells
  have hmem : ∀ p : Fin 3 → ℝ, (p 0 ∈ Ioo 0 1 ∧ p 1 ∈ Ioo 0 π ∧ p 2 ∈ Ioc (-π) π) →
      cellPoint p ∈ sectionZero ∧ (cellPoint p 2).im = 0 ∧ (cellPoint p 2).re < 0 ∧
        (cellPoint p 1).im = p 0 * Real.sin (p 2) := by
    intro p hp
    obtain ⟨-, hy2, h3, h3'⟩ := l5a_cellPoint_im p
    exact ⟨cellPoint_mem_sectionZero (hdom p hp), h3, h3' ▸ l5a_cellPoint_two_neg hp.1 hp.2.1,
      hy2⟩
  refine ⟨?_, ?_, ?_, fun p hp q hq h ↦ l5a_eq_of_cellClass_eq (hone p hp) (hone q hq) h,
    fun p hp q hq h ↦ l5a_eq_of_cellClass_eq (htwo p hp) (htwo q hq) h, hfc1, hfc2, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨hs, h3, h3', hy⟩ := hmem p (hone p hp)
      exact ⟨cellPoint p, hs, rfl, h3, h3', hy ▸ mul_pos hp.1.1
        (Real.sin_pos_of_pos_of_lt_pi hp.2.2.1 hp.2.2.2)⟩
    · rintro ⟨z, hz, rfl, h3, h3', hy⟩
      obtain ⟨⟨c0, c1, -⟩, hc⟩ := cellClass_cellCoords hz h3 h3'
      refine ⟨cellCoords z, ⟨c0, c1, ?_⟩, hc⟩
      change arg (z 1) ∈ Ioo 0 π
      refine ⟨lt_of_le_of_ne (Complex.arg_nonneg_iff.2 hy.le) fun h ↦ ?_,
        Complex.arg_lt_pi_iff.2 (Or.inr hy.ne')⟩
      exact hy.ne' (Complex.arg_eq_zero_iff.1 h.symm).2
  · ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨hs, h3, h3', hy⟩ := hmem p (htwo p hp)
      exact ⟨cellPoint p, hs, rfl, h3, h3', hy ▸ mul_neg_of_pos_of_neg hp.1.1
        (Real.sin_neg_of_neg_of_neg_pi_lt hp.2.2.2 hp.2.2.1)⟩
    · rintro ⟨z, hz, rfl, h3, h3', hy⟩
      obtain ⟨⟨c0, c1, -⟩, hc⟩ := cellClass_cellCoords hz h3 h3'
      exact ⟨cellCoords z, ⟨c0, c1, Complex.neg_pi_lt_arg _, Complex.arg_neg_iff.2 hy⟩, hc⟩
  · -- the two cells are disjoint: `y₂ > 0` and `y₂ < 0` cannot hold for one class
    rw [Set.disjoint_left]
    rintro x ⟨z, hz, rfl, h3, h3', hy⟩ ⟨w, hw, hzw, hw3, -, hy'⟩
    obtain ⟨r, hr, rfl⟩ := l5a_eq_scale_of_classOf_eq hz hw h3 h3' hw3 hzw.symm
    have e : (scale r z 1).im = r ^ 2 * (z 1).im := by
      rw [show scale r z 1 = ((r ^ 2 : ℝ) : ℂ) * z 1 by simp [scale], Complex.im_ofReal_mul]
    rw [e] at hy'
    have := mul_pos (pow_pos hr 2) hy
    linarith
  · rintro p hp
    have hp2 := hp.2.2
    refine ⟨⟨hp.1, show π - p 1 ∈ Ioo 0 π from ⟨by linarith [hp.2.1.2], by linarith [hp.2.1.1]⟩,
      show π - p 2 ∈ Ioo 0 π from ⟨by linarith [hp2.2], by linarith [hp2.1]⟩⟩, ?_⟩
    have e : cellTau p = ![p 0, π - p 1, π - p 2] := by
      change ![p 0, π - p 1, (if 0 ≤ p 2 then π else -π) - p 2] = _
      rw [ite_eq_left hp2.1.le]
    rw [← e, (cellClass_cellTau (hdom p (hone p hp))).2]
  · rintro p hp
    have hp2 := hp.2.2
    refine ⟨⟨hp.1, show π - p 1 ∈ Ioo 0 π from ⟨by linarith [hp.2.1.2], by linarith [hp.2.1.1]⟩,
      show -π - p 2 ∈ Ioo (-π) 0 from ⟨by linarith [hp2.2], by linarith [hp2.1]⟩⟩, ?_⟩
    have e : cellTau p = ![p 0, π - p 1, -π - p 2] := by
      change ![p 0, π - p 1, (if 0 ≤ p 2 then π else -π) - p 2] = _
      rw [ite_eq_right (not_le.2 hp2.2)]
    rw [← e, (cellClass_cellTau (hdom p (htwo p hp))).2]

end SmoothedPolygons
