module

public import SmoothedPolygons.Ch13.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Chapter 13: blowing up the Fuller system at the singular locus

§13.4 of Hales–Vajjha, *Packings of Smoothed Polygons* ("Blowing up Fuller", TeX 11159–11229):

* the weighted norm `φ(z) = (Σ_{j=1}^{3} |z_j|^{6/j})^{1/6}` (`weightedNorm`) with
  `φ(r z₁, r² z₂, r³ z₃) = r φ(z)` for `r > 0` (`weightedNorm_scale`), the weighted sphere
  `Ξ = {φ = 1}` (`Xi`) and the angular projection `z ↦ (z₁/φ, z₂/φ², z₃/φ³)` (`ang`);
* the identification `ℂ³ ∖ 0 ≅ ℝ_{>0} × Ξ`, `z ↦ (φ(z), ang z)`, with inverse
  `(r, ξ) ↦ (r ξ₁, r² ξ₂, r³ ξ₃)` (`blowup`; "weighted spherical coordinates"), equivariant for the
  virial group (`weightedNorm_ang_smul_scale`);
* the Poincaré section `Ξ_𝒲 = {ξ ∈ Ξ | ξ₃ ∈ 𝒲}` with the diagonal action of `V_T` (`XiW`, a
  `SubMulAction` of the group `rootsOfUnity 3 ℂ`, whose elements are the points of `V_T`,
  `mem_VT_iff_exists_rootsOfUnity`), and the quotient `Ξ_𝒲/V_T` (`XiWQuot`) with its quotient
  topology. Under the action the three walls are identified (`exists_smul_mem_wall_zero`).

**Regularity of the identification (a correction).** The book calls the identification a
diffeomorphism (TeX 11169–11177). The function `φ⁶ = |z₁|⁶ + |z₂|³ + |z₃|²` is `C²` but not `C³`
at points with `z₂ = 0` (the term `|z₂|³`), so `Ξ` is a `C²` hypersurface of `ℂ³` and the
identification is a `C²` diffeomorphism, smooth away from `{z₂ = 0}` (inventory, gap 8). Only the
one reading is possible, and it is recorded here: the identification is stated as a homeomorphism
together with the regularity of `φ` (`contDiffOn_weightedNorm`,
`contDiffOn_weightedNorm_infty`); the inverse map is polynomial. The book uses the
identification as coordinates, and smoothness only near the fixed point `q_out` (Lemma 13.5.5),
where `z₂ ≠ 0`.

The "oriented weighted real blowup" `ℝ_{≥0} × Ξ → ℂ³` with exceptional divisor `{0} × Ξ`
(TeX 11198–11206) is descriptive and has no statement of its own.

## Proofs

The book states the facts of §13.4 without proof. The homogeneity of `φ` is the computation
`|r z₁|⁶ + |r² z₂|³ + |r³ z₃|² = r⁶ φ(z)⁶`; the homeomorphism and the equivariance follow from it
and from the rescalings composing as the multiplicative group `ℝ_{>0}` (rescaling by `r`, then by
`s`, is rescaling by `r s`). The `C²` regularity of `φ` comes from
that of `w ↦ |w|³` on a real inner product space, whose derivative `3 ⟪|w| w, ·⟫` is `C¹` because
`w ↦ |w| w` is (with derivative `|w| id + |w|⁻¹ ⟪w, ·⟫ w`, of norm `≤ 2|w|`, at `w ≠ 0`, and `0`
at `w = 0`); Mathlib proves only that `w ↦ |w|^p` is `C¹` for `p > 1`. The group `rootsOfUnity 3 ℂ`
is identified with `V_T` through `ζ = exp(2πi/3)` being a primitive cube root of unity.
-/

@[expose] public section

namespace SmoothedPolygons

open Complex Set

open scoped ContDiff

namespace TriFuller

/-! ### Calculus of `w ↦ |w|³` on a real inner product space -/

section NormCube

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The derivative of the norm off the origin: `D|·|(x) = |x|⁻¹ ⟪x, ·⟫`. -/
private theorem l4e_hasFDerivAt_norm {x : E} (hx : x ≠ 0) :
    HasFDerivAt (fun y : E ↦ ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt (by simpa using hx)
  simp only [Real.sqrt_sq (norm_nonneg _)] at h
  convert h using 1
  ext v
  simp [innerSL_apply_apply]
  field_simp

/-- `x ↦ |x| x` is `C¹`, with derivative `|x| id + |x|⁻¹ ⟪x, ·⟫ x` (which is `0` at `x = 0`, and
of norm at most `2 |x|`). -/
private theorem l4e_contDiff_norm_smul : ContDiff ℝ 1 (fun x : E ↦ ‖x‖ • x) := by
  rw [contDiff_one_iff_hasFDerivAt]
  refine ⟨fun x ↦ ‖x‖ • ContinuousLinearMap.id ℝ E + (‖x‖⁻¹ • innerSL ℝ x).smulRight x, ?_, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x = 0
    · subst hx
      simp only [ContinuousAt, norm_zero, zero_smul, inv_zero,
        ContinuousLinearMap.smulRight_zero, add_zero]
      refine squeeze_zero_norm (a := fun x : E ↦ 2 * ‖x‖) (fun y ↦ ?_) ?_
      · refine (norm_add_le _ _).trans ?_
        rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply, norm_smul, norm_inv, norm_norm,
          innerSL_apply_norm]
        have h1 : ‖ContinuousLinearMap.id ℝ E‖ ≤ 1 := ContinuousLinearMap.norm_id_le
        have h2 : ‖y‖⁻¹ * ‖y‖ * ‖y‖ ≤ ‖y‖ := by
          rcases eq_or_ne ‖y‖ 0 with h | h
          · simp [h]
          · rw [inv_mul_cancel₀ h, one_mul]
        nlinarith [norm_nonneg y]
      · simpa using (continuous_norm.tendsto (0 : E)).const_mul 2
    · have : ContinuousAt (fun x : E ↦ ‖x‖⁻¹) x :=
        continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hx)
      have hc : ContinuousAt (fun y : E ↦ ‖y‖⁻¹ • innerSL ℝ y) x := by fun_prop
      have hs : ContinuousAt (fun y : E ↦ (‖y‖⁻¹ • innerSL ℝ y).smulRight y) x :=
        (isBoundedBilinearMap_smulRight (𝕜 := ℝ) (E := E) (F := E)).continuous.continuousAt.comp
          (hc.prodMk continuousAt_id)
      exact (continuous_norm.continuousAt.smul continuousAt_const).add hs
  · intro x
    by_cases hx : x = 0
    · subst hx
      simp only [norm_zero, zero_smul, inv_zero, ContinuousLinearMap.smulRight_zero, add_zero]
      refine .of_isLittleO ?_
      simp only [norm_zero, zero_smul, sub_zero, zero_apply]
      rw [← Asymptotics.isLittleO_norm_left]
      simp_rw [norm_smul, norm_norm, ← sq]
      exact Asymptotics.isLittleO_norm_pow_id one_lt_two
    · exact (l4e_hasFDerivAt_norm hx).smul (hasFDerivAt_id x)

/-- `x ↦ |x|³` is `C²`: its derivative `3 ⟪|x| x, ·⟫` is `C¹` (`l4e_contDiff_norm_smul`). -/
private theorem l4e_contDiff_norm_pow_three : ContDiff ℝ 2 (fun x : E ↦ ‖x‖ ^ 3) := by
  have h2 : (2 : WithTop ℕ∞) = ((1 : ℕ) : WithTop ℕ∞) + 1 := by norm_num
  rw [h2, contDiff_succ_iff_hasFDerivAt]
  refine ⟨fun x ↦ (3 : ℝ) • innerSL ℝ (‖x‖ • x), ?_, fun x ↦ ?_⟩
  · exact (((innerSL ℝ (E := E)).contDiff).comp l4e_contDiff_norm_smul).const_smul _
  · have h := hasFDerivAt_norm_rpow x (p := 3) (by norm_num)
    convert h using 1
    · ext y
      rw [← Real.rpow_natCast]
      norm_num
    · ext y
      simp [innerSL_apply_apply]
      norm_num
      ring

end NormCube

/-! ### The cube roots of unity -/

/-- `ζ = exp(2πi/3)` is a primitive cube root of unity. -/
private theorem l4e_isPrimitiveRoot_ζ : IsPrimitiveRoot ζ 3 := by
  have h := Complex.isPrimitiveRoot_exp 3 (by norm_num)
  rwa [Nat.cast_ofNat] at h

private theorem l4e_ζ_pow_mod (n : ℕ) : ζ ^ n = ζ ^ (n % 3) := by
  conv_lhs => rw [← Nat.mod_add_div n 3, pow_add, pow_mul, ζ_pow_three, one_pow, mul_one]

/-- `V_T = {ζⁿ | n ∈ ℕ}`. -/
private theorem l4e_mem_VT_iff_pow {v : ℂ} : v ∈ VT ↔ ∃ n : ℕ, v = ζ ^ n := by
  constructor
  · intro hv
    simp only [VT, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl
    exacts [⟨0, (pow_zero ζ).symm⟩, ⟨1, (pow_one ζ).symm⟩, ⟨2, rfl⟩]
  · rintro ⟨n, rfl⟩
    rw [l4e_ζ_pow_mod]
    simp only [VT, Set.mem_insert_iff, Set.mem_singleton_iff]
    obtain h | h | h : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    · simp [h]
    · simp [h]
    · simp [h]

private theorem l4e_pow_three_of_mem_VT {v : ℂ} (hv : v ∈ VT) : v ^ 3 = 1 := by
  obtain ⟨n, rfl⟩ := l4e_mem_VT_iff_pow.mp hv
  rw [← pow_mul, mul_comm, pow_mul, ζ_pow_three, one_pow]

/-- `𝒲 = {s ζⁿ | s ≤ 0, n ∈ ℕ}`. -/
private theorem l4e_mem_walls_iff {w : ℂ} :
    w ∈ walls ↔ ∃ s : ℝ, s ≤ 0 ∧ ∃ n : ℕ, w = s * ζ ^ n := by
  constructor
  · rintro ((⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩) | ⟨s, hs, rfl⟩)
    exacts [⟨s, hs, 0, rfl⟩, ⟨s, hs, 1, rfl⟩, ⟨s, hs, 2, rfl⟩]
  · rintro ⟨s, hs, n, rfl⟩
    rw [l4e_ζ_pow_mod]
    obtain h | h | h : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    · rw [h]; exact Or.inl (Or.inl ⟨s, hs, rfl⟩)
    · rw [h]; exact Or.inl (Or.inr ⟨s, hs, rfl⟩)
    · rw [h]; exact Or.inr ⟨s, hs, rfl⟩

/-- `V_T 𝒲 = 𝒲`. -/
private theorem l4e_mul_mem_walls {v w : ℂ} (hv : v ∈ VT) (hw : w ∈ walls) : v * w ∈ walls := by
  obtain ⟨m, rfl⟩ := l4e_mem_VT_iff_pow.mp hv
  obtain ⟨s, hs, n, rfl⟩ := l4e_mem_walls_iff.mp hw
  exact l4e_mem_walls_iff.mpr ⟨s, hs, m + n, by ring⟩

/-! ### The virial rescaling -/

/-! ### The weighted norm -/

/-- The weighted norm `φ(z) = (Σ_{j=1}^{3} |z_j|^{6/j})^{1/6} = (|z₁|⁶ + |z₂|³ + |z₃|²)^{1/6}`
(TeX 11161–11165). -/
noncomputable def weightedNorm (z : Fin 3 → ℂ) : ℝ :=
  (‖z 0‖ ^ 6 + ‖z 1‖ ^ 3 + ‖z 2‖ ^ 2) ^ (1 / 6 : ℝ)

/-- The weighted sphere `Ξ = {ξ ∈ ℂ³ | φ(ξ) = 1}` (TeX 11170). -/
def Xi : Set (Fin 3 → ℂ) := {ξ | weightedNorm ξ = 1}

/-- The angular projection `z ↦ (z₁/r, z₂/r², z₃/r³)`, `r = φ(z)` (TeX 11169–11177; the book's
`π_ang` composed with the identification). -/
noncomputable def ang (z : Fin 3 → ℂ) : Fin 3 → ℂ := scale (weightedNorm z)⁻¹ z

/-- `φ⁶ = |z₁|⁶ + |z₂|³ + |z₃|²` vanishes only at `0`. -/
private theorem l4e_sum_pos {z : Fin 3 → ℂ} (hz : z ≠ 0) :
    0 < ‖z 0‖ ^ 6 + ‖z 1‖ ^ 3 + ‖z 2‖ ^ 2 := by
  refine lt_of_le_of_ne (by positivity) fun h ↦ hz ?_
  have a0 := pow_nonneg (norm_nonneg (z 0)) 6
  have a1 := pow_nonneg (norm_nonneg (z 1)) 3
  have a2 := pow_nonneg (norm_nonneg (z 2)) 2
  have h0 : z 0 = 0 := by
    have : ‖z 0‖ ^ 6 = 0 := by linarith
    simpa using this
  have h1 : z 1 = 0 := by
    have : ‖z 1‖ ^ 3 = 0 := by linarith
    simpa using this
  have h2 : z 2 = 0 := by
    have : ‖z 2‖ ^ 2 = 0 := by linarith
    simpa using this
  funext i; fin_cases i
  exacts [h0, h1, h2]

/-- `φ(0) = 0`. -/
theorem weightedNorm_zero : weightedNorm 0 = 0 := by
  simp [weightedNorm]

/-- `φ(r z₁, r² z₂, r³ z₃) = r φ(z)` for `r > 0` (TeX 11165). -/
theorem weightedNorm_scale {r : ℝ} (hr : 0 < r) (z : Fin 3 → ℂ) :
    weightedNorm (scale r z) = r * weightedNorm z := by
  have h : ‖scale r z 0‖ ^ 6 + ‖scale r z 1‖ ^ 3 + ‖scale r z 2‖ ^ 2 =
      r ^ 6 * (‖z 0‖ ^ 6 + ‖z 1‖ ^ 3 + ‖z 2‖ ^ 2) := by
    simp [scale, abs_of_pos hr]
    ring
  unfold weightedNorm
  rw [h, Real.mul_rpow (by positivity) (by positivity)]
  congr 1
  rw [show (1 / 6 : ℝ) = ((6 : ℕ) : ℝ)⁻¹ by norm_num, Real.pow_rpow_inv_natCast hr.le (by norm_num)]

/-- `φ` is positive off the singular locus. -/
theorem weightedNorm_pos {z : Fin 3 → ℂ} (hz : z ≠ 0) : 0 < weightedNorm z :=
  Real.rpow_pos_of_pos (l4e_sum_pos hz) _

/-- `φ` is continuous. -/
theorem continuous_weightedNorm : Continuous weightedNorm := by
  have h : Continuous fun z : Fin 3 → ℂ ↦ ‖z 0‖ ^ 6 + ‖z 1‖ ^ 3 + ‖z 2‖ ^ 2 := by fun_prop
  exact h.rpow_const fun _ ↦ Or.inr (by norm_num)

/-- The virial rescaling is jointly continuous. -/
theorem continuous_scale : Continuous fun p : ℝ × (Fin 3 → ℂ) ↦ scale p.1 p.2 := by
  unfold scale
  fun_prop

/-- The angular projection is continuous off the singular locus. -/
theorem continuousOn_ang : ContinuousOn ang {z | z ≠ 0} :=
  continuous_scale.comp_continuousOn
    ((continuous_weightedNorm.continuousOn.inv₀ fun _ hz ↦
      (weightedNorm_pos hz).ne').prodMk continuousOn_id)

/-- The angular projection lands in `Ξ`. -/
theorem ang_mem_Xi {z : Fin 3 → ℂ} (hz : z ≠ 0) : ang z ∈ Xi := by
  have h := weightedNorm_pos hz
  change weightedNorm (scale (weightedNorm z)⁻¹ z) = 1
  rw [weightedNorm_scale (inv_pos.mpr h), inv_mul_cancel₀ h.ne']

/-- `(r ξ₁, r² ξ₂, r³ ξ₃) ≠ 0` for `r > 0` and `ξ ∈ Ξ`. -/
theorem scale_ne_zero_of_mem_Xi {r : ℝ} (hr : 0 < r) {ξ : Fin 3 → ℂ} (hξ : ξ ∈ Xi) :
    scale r ξ ≠ 0 := by
  intro h
  have hξ' : weightedNorm ξ = 1 := hξ
  have := weightedNorm_scale hr ξ
  rw [h, hξ', mul_one, weightedNorm_zero] at this
  exact hr.ne this

/-- `z = (r ξ₁, r² ξ₂, r³ ξ₃)` with `r = φ(z)` and `ξ = ang z`. -/
theorem scale_weightedNorm_ang {z : Fin 3 → ℂ} (hz : z ≠ 0) :
    scale (weightedNorm z) (ang z) = z := by
  rw [ang, scale_scale, mul_inv_cancel₀ (weightedNorm_pos hz).ne', scale_one]

/-- `φ(r ξ₁, r² ξ₂, r³ ξ₃) = r` and `ang (r ξ₁, r² ξ₂, r³ ξ₃) = ξ` for `r > 0` and `ξ ∈ Ξ`. -/
theorem weightedNorm_ang_scale {r : ℝ} (hr : 0 < r) {ξ : Fin 3 → ℂ} (hξ : ξ ∈ Xi) :
    weightedNorm (scale r ξ) = r ∧ ang (scale r ξ) = ξ := by
  have hξ' : weightedNorm ξ = 1 := hξ
  have h1 : weightedNorm (scale r ξ) = r := by rw [weightedNorm_scale hr, hξ', mul_one]
  refine ⟨h1, ?_⟩
  rw [ang, h1, scale_scale, inv_mul_cancel₀ hr.ne', scale_one]

/-- The points of `Ξ` are not `0`. -/
theorem ne_zero_of_mem_Xi {ξ : Fin 3 → ℂ} (hξ : ξ ∈ Xi) : ξ ≠ 0 := by
  rintro rfl
  have h : weightedNorm 0 = 1 := hξ
  rw [weightedNorm_zero] at h
  exact zero_ne_one h

/-- `ang ξ = ξ` on the weighted sphere. -/
theorem ang_of_mem_Xi {ξ : Fin 3 → ℂ} (hξ : ξ ∈ Xi) : ang ξ = ξ := by
  have h1 : weightedNorm ξ = 1 := hξ
  rw [ang, h1, inv_one, scale_one]

/-- `φ(τ z) = φ(z)`. -/
theorem weightedNorm_tau (z : Fin 3 → ℂ) : weightedNorm (tau z) = weightedNorm z := by
  simp [weightedNorm, tau]

/-- `τ` commutes with the virial rescalings. -/
theorem tau_scale (r : ℝ) (z : Fin 3 → ℂ) : tau (scale r z) = scale r (tau z) := by
  funext i; fin_cases i <;> simp [tau, scale]

/-- `τ` commutes with the angular projection. -/
theorem tau_ang (z : Fin 3 → ℂ) : tau (ang z) = ang (tau z) := by
  rw [ang, ang, weightedNorm_tau, tau_scale]

/-- **The weighted spherical coordinates** (TeX 11169–11180): the homeomorphism
`ℂ³ ∖ 0 ≅ ℝ_{>0} × Ξ`, `z ↦ (φ(z), (z₁/r, z₂/r², z₃/r³))` with `r = φ(z)`, whose inverse is
`(r, ξ) ↦ (r ξ₁, r² ξ₂, r³ ξ₃)`. (The book's "diffeomorphism": see the module docstring; the
regularity is `contDiffOn_weightedNorm`.) -/
noncomputable def blowup : {z : Fin 3 → ℂ // z ≠ 0} ≃ₜ Ioi (0 : ℝ) × Xi where
  toFun z := (⟨weightedNorm z, weightedNorm_pos z.2⟩, ⟨ang z, ang_mem_Xi z.2⟩)
  invFun p := ⟨scale p.1 p.2, scale_ne_zero_of_mem_Xi p.1.2 p.2.2⟩
  left_inv z := Subtype.ext (scale_weightedNorm_ang z.2)
  right_inv p := Prod.ext (Subtype.ext (weightedNorm_ang_scale p.1.2 p.2.2).1)
    (Subtype.ext (weightedNorm_ang_scale p.1.2 p.2.2).2)
  continuous_toFun :=
    (continuous_weightedNorm.comp continuous_subtype_val).subtype_mk _ |>.prodMk
      ((continuousOn_ang.comp_continuous continuous_subtype_val fun z ↦ z.2).subtype_mk _)
  continuous_invFun :=
    (continuous_scale.comp ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))).subtype_mk _

private theorem l4e_contDiff_norm_pow_six {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun z : Fin 3 → ℂ ↦ ‖z 0‖ ^ 6) := by
  have e : (fun z : Fin 3 → ℂ ↦ ‖z 0‖ ^ 6) = fun z ↦ (‖z 0‖ ^ 2) ^ 3 := by
    funext z; ring
  rw [e]
  exact ((contDiff_apply ℝ (fun _ : Fin 3 ↦ ℂ) 0).norm_sq ℝ).pow 3

private theorem l4e_contDiff_norm_sq_two {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun z : Fin 3 → ℂ ↦ ‖z 2‖ ^ 2) :=
  (contDiff_apply ℝ (fun _ : Fin 3 ↦ ℂ) 2).norm_sq ℝ

/-- **Regularity of the weighted norm** (the book's "diffeomorphism", TeX 11169, corrected): `φ`
is `C²` on `ℂ³ ∖ 0` (`φ⁶ = |z₁|⁶ + |z₂|³ + |z₃|²` is `C²`, and `t ↦ t^{1/6}` is smooth on
`t > 0`). It is not `C³` at the points with `z₂ = 0` (see the module docstring). -/
theorem contDiffOn_weightedNorm : ContDiffOn ℝ 2 weightedNorm {z | z ≠ 0} := by
  intro z hz
  have h0 : ContDiff ℝ 2 (fun z : Fin 3 → ℂ ↦ ‖z 0‖ ^ 6) := l4e_contDiff_norm_pow_six
  have h1 : ContDiff ℝ 2 (fun z : Fin 3 → ℂ ↦ ‖z 1‖ ^ 3) :=
    l4e_contDiff_norm_pow_three.comp (contDiff_apply ℝ (fun _ : Fin 3 ↦ ℂ) 1)
  have h2 : ContDiff ℝ 2 (fun z : Fin 3 → ℂ ↦ ‖z 2‖ ^ 2) := l4e_contDiff_norm_sq_two
  exact (((h0.add h1).add h2).contDiffAt.rpow_const_of_ne (l4e_sum_pos hz).ne').contDiffWithinAt

/-- `φ` is smooth on `ℂ³ ∖ {z₂ = 0}` (in particular near `q_out`). -/
theorem contDiffOn_weightedNorm_infty :
    ContDiffOn ℝ ∞ weightedNorm {z | z ≠ 0 ∧ z 1 ≠ 0} := by
  intro z hz
  have h0 : ContDiff ℝ ∞ (fun z : Fin 3 → ℂ ↦ ‖z 0‖ ^ 6) := l4e_contDiff_norm_pow_six
  have h1 : ContDiffAt ℝ ∞ (fun z : Fin 3 → ℂ ↦ ‖z 1‖ ^ 3) z :=
    ((contDiffAt_norm ℝ hz.2).comp z
      (contDiff_apply ℝ (fun _ : Fin 3 ↦ ℂ) 1).contDiffAt).pow 3
  have h2 : ContDiff ℝ ∞ (fun z : Fin 3 → ℂ ↦ ‖z 2‖ ^ 2) := l4e_contDiff_norm_sq_two
  exact (((h0.contDiffAt.add h1).add h2.contDiffAt).rpow_const_of_ne
    (l4e_sum_pos hz.1).ne').contDiffWithinAt

/-- `φ` is invariant under the rotations by `V_T`. -/
theorem weightedNorm_smul {v : ℂ} (hv : v ∈ VT) (z : Fin 3 → ℂ) :
    weightedNorm (v • z) = weightedNorm z := by
  simp only [weightedNorm, Pi.smul_apply, smul_eq_mul, norm_mul, norm_eq_one_of_mem_VT hv,
    one_mul]

/-- `ang (v w) = v ang w` for `v ∈ V_T`. -/
theorem ang_smul {v : ℂ} (hv : v ∈ VT) (w : Fin 3 → ℂ) : ang (v • w) = v • ang w := by
  rw [ang, ang, weightedNorm_smul hv]
  funext i
  fin_cases i <;> simp [scale] <;> ring

/-- **The identification is equivariant for the virial group** (TeX 11216–11219): rescalings act
by multiplication on the radial component and `V_T` acts by scalar multiplication on the angular
component, `φ(v·(r z₁, r² z₂, r³ z₃)) = r φ(z)` and `ang (v·(r z₁, r² z₂, r³ z₃)) = v · ang z`. -/
theorem weightedNorm_ang_smul_scale {z : Fin 3 → ℂ} (hz : z ≠ 0) {r : ℝ} (hr : 0 < r) {v : ℂ}
    (hv : v ∈ VT) :
    weightedNorm (v • scale r z) = r * weightedNorm z ∧ ang (v • scale r z) = v • ang z := by
  have hφ : weightedNorm (v • scale r z) = r * weightedNorm z := by
    rw [weightedNorm_smul hv, weightedNorm_scale hr]
  refine ⟨hφ, ?_⟩
  have hr0 : r ≠ 0 := hr.ne'
  have hφ0 : weightedNorm z ≠ 0 := (weightedNorm_pos hz).ne'
  simp only [ang, hφ, scale_smul, scale_scale]
  congr 2
  field_simp

/-- The elements of the group `rootsOfUnity 3 ℂ` are the points of `V_T`. -/
theorem mem_VT_iff_exists_rootsOfUnity (v : ℂ) :
    v ∈ VT ↔ ∃ g : rootsOfUnity 3 ℂ, ((g : ℂˣ) : ℂ) = v := by
  constructor
  · intro hv
    exact ⟨rootsOfUnity.mkOfPowEq v (l4e_pow_three_of_mem_VT hv), rootsOfUnity.coe_mkOfPowEq _⟩
  · rintro ⟨g, rfl⟩
    have h : ((g : ℂˣ) : ℂ) ^ 3 = 1 := by
      have hg : (g : ℂˣ) ^ 3 = 1 := (_root_.mem_rootsOfUnity 3 (g : ℂˣ)).mp g.2
      rw [← Units.val_pow_eq_pow_val, hg, Units.val_one]
    obtain ⟨i, -, hi⟩ := l4e_isPrimitiveRoot_ζ.eq_pow_of_pow_eq_one h
    exact l4e_mem_VT_iff_pow.mpr ⟨i, hi.symm⟩

/-- `Ξ_𝒲` is invariant under the diagonal action of `V_T` (`|v| = 1`, `v𝒲 = 𝒲`). -/
theorem smul_mem_XiW (g : rootsOfUnity 3 ℂ) {ξ : Fin 3 → ℂ}
    (h : ξ ∈ {ξ : Fin 3 → ℂ | ξ ∈ Xi ∧ ξ 2 ∈ walls}) :
    g • ξ ∈ {ξ : Fin 3 → ℂ | ξ ∈ Xi ∧ ξ 2 ∈ walls} := by
  have hv : ((g : ℂˣ) : ℂ) ∈ VT := (mem_VT_iff_exists_rootsOfUnity _).mpr ⟨g, rfl⟩
  have hg : g • ξ = ((g : ℂˣ) : ℂ) • ξ := rfl
  rw [hg]
  refine ⟨?_, ?_⟩
  · change weightedNorm _ = 1
    rw [weightedNorm_smul hv]
    exact h.1
  · exact l4e_mul_mem_walls hv h.2

/-- The Poincaré section `Ξ_𝒲 = {ξ ∈ Ξ | ξ₃ ∈ 𝒲}` (TeX 11221–11225), with the diagonal action of
`V_T = rootsOfUnity 3 ℂ` by scalar multiplication (TeX 11225–11229). -/
noncomputable def XiW : SubMulAction (rootsOfUnity 3 ℂ) (Fin 3 → ℂ) where
  carrier := {ξ | ξ ∈ Xi ∧ ξ 2 ∈ walls}
  smul_mem' := smul_mem_XiW

/-- The quotient `Ξ_𝒲/V_T` of the Poincaré section by the cyclic group `V_T` acting diagonally
(TeX 11225–11229), with the quotient topology. -/
abbrev XiWQuot : Type := MulAction.orbitRel.Quotient (rootsOfUnity 3 ℂ) XiW

/-- "Under the group action, the three walls of `𝒲` are identified with one another"
(TeX 11228–11229): every point with `ξ₃ ∈ 𝒲` has a rotation `v ξ`, `v ∈ V_T`, with
`(v ξ)₃ ∈ 𝒲₀ = ℝ_{≤0}`. -/
theorem exists_smul_mem_wall_zero {ξ : Fin 3 → ℂ} (h : ξ 2 ∈ walls) :
    ∃ v ∈ VT, (v • ξ) 2 ∈ wall 0 := by
  obtain ⟨s, hs, n, hn⟩ := l4e_mem_walls_iff.mp h
  refine ⟨ζ ^ (2 * n), l4e_mem_VT_iff_pow.mpr ⟨2 * n, rfl⟩, s, hs, ?_⟩
  have h3 : ζ ^ (2 * n) * ζ ^ n = 1 := by
    rw [← pow_add, show 2 * n + n = 3 * n by ring, pow_mul, ζ_pow_three, one_pow]
  simp only [Pi.smul_apply, smul_eq_mul, hn, pow_zero, mul_one]
  linear_combination (s : ℂ) * h3

end TriFuller

end SmoothedPolygons
