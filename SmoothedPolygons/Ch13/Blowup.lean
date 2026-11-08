module

public import SmoothedPolygons.Ch13.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Topology.Algebra.Group.Basic

/-!
# Chapter 13: blowing up the Fuller system at the singular locus

§13.4 of Hales–Vajjha, *Packings of Smoothed Polygons* ("Blowing up Fuller", TeX 11159–11229):

* the weighted norm `φ(z) = (Σ_{j=1}^{3} |z_j|^{6/j})^{1/6}` (`weightedNorm`) with
  `φ(r z₁, r² z₂, r³ z₃) = r φ(z)` for `r > 0` (`l4st_weightedNorm_scale`), the weighted sphere
  `Ξ = {φ = 1}` (`Xi`) and the angular projection `z ↦ (z₁/φ, z₂/φ², z₃/φ³)` (`ang`);
* the identification `ℂ³ ∖ 0 ≅ ℝ_{>0} × Ξ`, `z ↦ (φ(z), ang z)`, with inverse
  `(r, ξ) ↦ (r ξ₁, r² ξ₂, r³ ξ₃)` (`blowup`; "weighted spherical coordinates"), equivariant for the
  virial group (`l4st_virial_equivariant`);
* the Poincaré section `Ξ_𝒲 = {ξ ∈ Ξ | ξ₃ ∈ 𝒲}` with the diagonal action of `V_T` (`XiW`, a
  `SubMulAction` of the group `rootsOfUnity 3 ℂ`, whose elements are the points of `V_T`,
  `l4st_mem_VT_iff`), and the quotient `Ξ_𝒲/V_T` (`XiWQuot`) with its quotient topology. Under
  the action the three walls are identified (`l4st_exists_smul_mem_wall_zero`).

**Regularity of the identification (a correction).** The book calls the identification a
diffeomorphism (TeX 11169–11177). The function `φ⁶ = |z₁|⁶ + |z₂|³ + |z₃|²` is `C²` but not `C³`
at points with `z₂ = 0` (the term `|z₂|³`), so `Ξ` is a `C²` hypersurface of `ℂ³` and the
identification is a `C²` diffeomorphism, smooth away from `{z₂ = 0}` (inventory, gap 8). Only the
one reading is possible, and it is recorded here: the identification is stated as a homeomorphism
together with the regularity of `φ` (`l4st_contDiffOn_weightedNorm`,
`l4st_contDiffOn_weightedNorm_of_ne`); the inverse map is polynomial. The book uses the
identification as coordinates, and smoothness only near the fixed point `q_out` (Lemma 13.5.5),
where `z₂ ≠ 0`.

The "oriented weighted real blowup" `ℝ_{≥0} × Ξ → ℂ³` with exceptional divisor `{0} × Ξ`
(TeX 11198–11206) is descriptive and has no statement of its own.
-/

@[expose] public section

namespace SmoothedPolygons

open Complex Set

open scoped ContDiff

namespace TriFuller

/-- The weighted norm `φ(z) = (Σ_{j=1}^{3} |z_j|^{6/j})^{1/6} = (|z₁|⁶ + |z₂|³ + |z₃|²)^{1/6}`
(TeX 11161–11165). -/
noncomputable def weightedNorm (z : Fin 3 → ℂ) : ℝ :=
  (‖z 0‖ ^ 6 + ‖z 1‖ ^ 3 + ‖z 2‖ ^ 2) ^ (1 / 6 : ℝ)

/-- The weighted sphere `Ξ = {ξ ∈ ℂ³ | φ(ξ) = 1}` (TeX 11170). -/
def Xi : Set (Fin 3 → ℂ) := {ξ | weightedNorm ξ = 1}

/-- The angular projection `z ↦ (z₁/r, z₂/r², z₃/r³)`, `r = φ(z)` (TeX 11169–11177; the book's
`π_ang` composed with the identification). -/
noncomputable def ang (z : Fin 3 → ℂ) : Fin 3 → ℂ := scale (weightedNorm z)⁻¹ z

/-- `φ(r z₁, r² z₂, r³ z₃) = r φ(z)` for `r > 0` (TeX 11165). -/
theorem l4st_weightedNorm_scale {r : ℝ} (hr : 0 < r) (z : Fin 3 → ℂ) :
    weightedNorm (scale r z) = r * weightedNorm z := by
  sorry

/-- `φ` is positive off the singular locus. -/
theorem l4st_weightedNorm_pos {z : Fin 3 → ℂ} (hz : z ≠ 0) : 0 < weightedNorm z := by
  sorry

/-- `φ` is continuous. -/
theorem l4st_continuous_weightedNorm : Continuous weightedNorm := by
  sorry

/-- The angular projection is continuous off the singular locus. -/
theorem l4st_continuousOn_ang : ContinuousOn ang {z | z ≠ 0} := by
  sorry

/-- The virial rescaling is jointly continuous. -/
theorem l4st_continuous_scale : Continuous fun p : ℝ × (Fin 3 → ℂ) ↦ scale p.1 p.2 := by
  sorry

/-- The angular projection lands in `Ξ`. -/
theorem l4st_ang_mem_Xi {z : Fin 3 → ℂ} (hz : z ≠ 0) : ang z ∈ Xi := by
  sorry

/-- `(r ξ₁, r² ξ₂, r³ ξ₃) ≠ 0` for `r > 0` and `ξ ∈ Ξ`. -/
theorem l4st_scale_ne_zero {r : ℝ} (hr : 0 < r) {ξ : Fin 3 → ℂ} (hξ : ξ ∈ Xi) :
    scale r ξ ≠ 0 := by
  sorry

/-- `z = (r ξ₁, r² ξ₂, r³ ξ₃)` with `r = φ(z)` and `ξ = ang z`. -/
theorem l4st_scale_weightedNorm_ang {z : Fin 3 → ℂ} (hz : z ≠ 0) :
    scale (weightedNorm z) (ang z) = z := by
  sorry

/-- `φ(r ξ₁, r² ξ₂, r³ ξ₃) = r` and `ang (r ξ₁, r² ξ₂, r³ ξ₃) = ξ` for `r > 0` and `ξ ∈ Ξ`. -/
theorem l4st_weightedNorm_ang_scale {r : ℝ} (hr : 0 < r) {ξ : Fin 3 → ℂ} (hξ : ξ ∈ Xi) :
    weightedNorm (scale r ξ) = r ∧ ang (scale r ξ) = ξ := by
  sorry

/-- **The weighted spherical coordinates** (TeX 11169–11180): the homeomorphism
`ℂ³ ∖ 0 ≅ ℝ_{>0} × Ξ`, `z ↦ (φ(z), (z₁/r, z₂/r², z₃/r³))` with `r = φ(z)`, whose inverse is
`(r, ξ) ↦ (r ξ₁, r² ξ₂, r³ ξ₃)`. (The book's "diffeomorphism": see the module docstring; the
regularity is `l4st_contDiffOn_weightedNorm`.) -/
noncomputable def blowup : {z : Fin 3 → ℂ // z ≠ 0} ≃ₜ Ioi (0 : ℝ) × Xi where
  toFun z := (⟨weightedNorm z, l4st_weightedNorm_pos z.2⟩, ⟨ang z, l4st_ang_mem_Xi z.2⟩)
  invFun p := ⟨scale p.1 p.2, l4st_scale_ne_zero p.1.2 p.2.2⟩
  left_inv z := Subtype.ext (l4st_scale_weightedNorm_ang z.2)
  right_inv p := Prod.ext (Subtype.ext (l4st_weightedNorm_ang_scale p.1.2 p.2.2).1)
    (Subtype.ext (l4st_weightedNorm_ang_scale p.1.2 p.2.2).2)
  continuous_toFun :=
    (l4st_continuous_weightedNorm.comp continuous_subtype_val).subtype_mk _ |>.prodMk
      ((l4st_continuousOn_ang.comp_continuous continuous_subtype_val fun z ↦ z.2).subtype_mk _)
  continuous_invFun :=
    (l4st_continuous_scale.comp ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))).subtype_mk _

/-- **Regularity of the weighted norm** (the book's "diffeomorphism", TeX 11169, corrected): `φ`
is `C²` on `ℂ³ ∖ 0` (`φ⁶ = |z₁|⁶ + |z₂|³ + |z₃|²` is `C²`, and `t ↦ t^{1/6}` is smooth on
`t > 0`). It is not `C³` at the points with `z₂ = 0` (see the module docstring). -/
theorem l4st_contDiffOn_weightedNorm : ContDiffOn ℝ 2 weightedNorm {z | z ≠ 0} := by
  sorry

/-- `φ` is smooth on `ℂ³ ∖ {z₂ = 0}` (in particular near `q_out`). -/
theorem l4st_contDiffOn_weightedNorm_of_ne :
    ContDiffOn ℝ ∞ weightedNorm {z | z ≠ 0 ∧ z 1 ≠ 0} := by
  sorry

/-- `φ` is invariant under the rotations by `V_T`. -/
theorem l4st_weightedNorm_smul {v : ℂ} (hv : v ∈ VT) (z : Fin 3 → ℂ) :
    weightedNorm (v • z) = weightedNorm z := by
  sorry

/-- **The identification is equivariant for the virial group** (TeX 11216–11219): rescalings act
by multiplication on the radial component and `V_T` acts by scalar multiplication on the angular
component, `φ(v·(r z₁, r² z₂, r³ z₃)) = r φ(z)` and `ang (v·(r z₁, r² z₂, r³ z₃)) = v · ang z`. -/
theorem l4st_virial_equivariant {z : Fin 3 → ℂ} (hz : z ≠ 0) {r : ℝ} (hr : 0 < r) {v : ℂ}
    (hv : v ∈ VT) :
    weightedNorm (v • scale r z) = r * weightedNorm z ∧ ang (v • scale r z) = v • ang z := by
  sorry

/-- The elements of the group `rootsOfUnity 3 ℂ` are the points of `V_T`. -/
theorem l4st_mem_VT_iff (v : ℂ) : v ∈ VT ↔ ∃ g : rootsOfUnity 3 ℂ, ((g : ℂˣ) : ℂ) = v := by
  sorry

/-- `Ξ_𝒲` is invariant under the diagonal action of `V_T` (`|v| = 1`, `v𝒲 = 𝒲`). -/
theorem l4st_smul_mem_XiW (g : rootsOfUnity 3 ℂ) {ξ : Fin 3 → ℂ}
    (h : ξ ∈ {ξ : Fin 3 → ℂ | ξ ∈ Xi ∧ ξ 2 ∈ walls}) :
    g • ξ ∈ {ξ : Fin 3 → ℂ | ξ ∈ Xi ∧ ξ 2 ∈ walls} := by
  sorry

/-- The Poincaré section `Ξ_𝒲 = {ξ ∈ Ξ | ξ₃ ∈ 𝒲}` (TeX 11221–11225), with the diagonal action of
`V_T = rootsOfUnity 3 ℂ` by scalar multiplication (TeX 11225–11229). -/
noncomputable def XiW : SubMulAction (rootsOfUnity 3 ℂ) (Fin 3 → ℂ) where
  carrier := {ξ | ξ ∈ Xi ∧ ξ 2 ∈ walls}
  smul_mem' := l4st_smul_mem_XiW

/-- The quotient `Ξ_𝒲/V_T` of the Poincaré section by the cyclic group `V_T` acting diagonally
(TeX 11225–11229), with the quotient topology. -/
abbrev XiWQuot : Type := MulAction.orbitRel.Quotient (rootsOfUnity 3 ℂ) XiW

/-- "Under the group action, the three walls of `𝒲` are identified with one another"
(TeX 11228–11229): every point with `ξ₃ ∈ 𝒲` has a rotation `v ξ`, `v ∈ V_T`, with
`(v ξ)₃ ∈ 𝒲₀ = ℝ_{≤0}`. -/
theorem l4st_exists_smul_mem_wall_zero {ξ : Fin 3 → ℂ} (h : ξ 2 ∈ walls) :
    ∃ v ∈ VT, (v • ξ) 2 ∈ wall 0 := by
  sorry

end TriFuller

end SmoothedPolygons
