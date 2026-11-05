module

public import SmoothedPolygons.Defs
public import Basic.Analysis.Calculus.MatrixEntrywise
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Basic.Analysis.Calculus.MatrixEntrywiseExp
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The adjoint orbit of `J` and the upper half-plane (§4.1, §4.2)

The set of `X ∈ 𝔰𝔩₂(ℝ)` with `det X = 1` and `⟨J, X⟩ < 0` is the adjoint orbit `O_J`
(Lemma 4.1.1); the map `Φ` identifies the upper half-plane with `O_J` (Lemma 4.2.1), equivariantly
for the action of `SL₂(ℝ)` by linear fractional transformations (Remark 4.2.2). The tangent spaces
of adjoint orbits (Lemma 4.2.3) and the tangent map of `Φ` (Lemma 4.2.4).
-/

@[expose] public section

namespace SmoothedPolygons

open Matrix UpperHalfPlane

open scoped MatrixGroups

/-- The adjoint orbit `O_X = {Ad_g X | g ∈ SL₂(ℝ)} = {g X g⁻¹}` of `X`. -/
def adjointOrbit (X : Mat2) : Set Mat2 :=
  Set.range fun g : SL(2, ℝ) ↦ (g : Mat2) * X * ((g⁻¹ : SL(2, ℝ)) : Mat2)

/-- The rotations `[[p, -q], [q, p]]` (in particular `SO₂`) centralize `J`. -/
private lemma orb_rot_mul_J (p q : ℝ) : !![p, -q; q, p] * J = J * !![p, -q; q, p] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J]

/-- The Iwasawa decomposition of `SL₂(ℝ)`: `g = h k` with
`h = [[1, x], [0, 1]] diag(√y, 1/√y) = [[√y, x/√y], [0, 1/√y]]` (Mathlib's `toSL2R (x + iy)`)
and `k ∈ SO₂`. -/
private lemma orb_iwasawa (g : SL(2, ℝ)) : ∃ (z : ℍ) (p q : ℝ), p ^ 2 + q ^ 2 = 1 ∧
    (g : Mat2) = (z.toSL2R : Mat2) * !![p, -q; q, p] := by
  have hdet : (g : Mat2) 0 0 * (g : Mat2) 1 1 - (g : Mat2) 0 1 * (g : Mat2) 1 0 = 1 := by
    have := g.det_coe; rwa [det_fin_two] at this
  set a := (g : Mat2) 0 0
  set b := (g : Mat2) 0 1
  set c := (g : Mat2) 1 0
  set d := (g : Mat2) 1 1
  have hn : 0 < c ^ 2 + d ^ 2 := by
    by_contra h
    have hc : c = 0 := by nlinarith
    have hd : d = 0 := by nlinarith
    simp [hc, hd] at hdet
  set y := 1 / (c ^ 2 + d ^ 2) with hy_def
  have hy : 0 < y := by positivity
  set x := (a * c + b * d) / (c ^ 2 + d ^ 2) with hx_def
  have hs : √y * √y = y := Real.mul_self_sqrt hy.le
  have hs0 : √y ≠ 0 := (Real.sqrt_pos.mpr hy).ne'
  refine ⟨⟨x + y * Complex.I, by simpa using hy⟩, √y * d, √y * c, ?_, ?_⟩
  · rw [mul_pow, mul_pow, Real.sq_sqrt hy.le, hy_def]; field_simp; ring
  · have hre : (⟨x + y * Complex.I, by simpa using hy⟩ : ℍ).re = x := by
      simp [UpperHalfPlane.re]
    have him : (⟨x + y * Complex.I, by simpa using hy⟩ : ℍ).im = y := by
      simp [UpperHalfPlane.im]
    rw [coe_toSL2R, hre, him]
    have ha : a = y * d + x * c := by
      rw [hy_def, hx_def]; field_simp; linear_combination d * hdet
    have hb : b = x * d - y * c := by
      rw [hy_def, hx_def]; field_simp; linear_combination -c * hdet
    have hs2 : √y ^ 2 = y := Real.sq_sqrt hy.le
    ext i j; fin_cases i <;> fin_cases j
    · change a = _
      simp
      field_simp
      rw [hs2, ha]
    · change b = _
      simp
      field_simp
      rw [hs2, hb]; ring
    · change c = _
      simp
      field_simp
    · change d = _
      simp
      field_simp

/-- `h J h⁻¹ = Φ(x + iy)` for `h = [[1, x], [0, 1]] diag(√y, 1/√y)` (Mathlib's `toSL2R`). -/
private lemma orb_toSL2R_conj (z : ℍ) :
    (z.toSL2R : Mat2) * J * ((z.toSL2R⁻¹ : SL(2, ℝ)) : Mat2) = Φ z.re z.im := by
  have hy := z.im_pos
  have hs2 : √z.im ^ 2 = z.im := Real.sq_sqrt hy.le
  have hs0 : √z.im ≠ 0 := (Real.sqrt_pos.mpr hy).ne'
  rw [SpecialLinearGroup.coe_inv, coe_toSL2R, adjugate_fin_two]
  generalize √z.im = s at hs2 hs0 ⊢
  ext i j; fin_cases i <;> fin_cases j <;> simp [J, Φ] <;> field_simp <;> rw [← hs2] <;> ring

/-- `Φ(x + iy)` is traceless, has determinant one, and `⟨J, Φ(x + iy)⟩ = -(1 + x² + y²)/y < 0`. -/
private lemma orb_Φ_mem (x y : ℝ) (hy : 0 < y) :
    (Φ x y).trace = 0 ∧ (Φ x y).det = 1 ∧ traceForm J (Φ x y) < 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Φ, trace_fin_two]; ring
  · rw [Φ, det_fin_two_of]; field_simp; ring
  · have : traceForm J (Φ x y) = -(1 + x ^ 2 + y ^ 2) / y := by
      simp [traceForm, J, Φ, trace_fin_two]; field_simp; ring
    rw [this]
    exact div_neg_of_neg_of_pos (by nlinarith) hy

/-- A traceless `X = [[a, b], [c, -a]]` with `det X = 1` and `⟨J, X⟩ = b - c < 0` has `c > 0` and
is `Φ(a/c + i/c)`: "precisely the form of a general element `X` satisfying the conditions". -/
private lemma orb_eq_Φ (X : Mat2) (htr : X.trace = 0) (hdet : X.det = 1)
    (hJ : traceForm J X < 0) : 0 < X 1 0 ∧ X = Φ (X 0 0 / X 1 0) (1 / X 1 0) := by
  rw [trace_fin_two] at htr
  rw [det_fin_two] at hdet
  have hJ' : X 0 1 - X 1 0 < 0 := by
    simp only [traceForm, trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two] at hJ
    simp [J] at hJ
    linarith
  have h11 : X 1 1 = -X 0 0 := by linarith
  have hc : 0 < X 1 0 := by
    rw [h11] at hdet
    by_contra h
    push Not at h
    nlinarith [sq_nonneg (X 0 0), mul_nonneg (neg_nonneg.mpr h) (neg_nonneg.mpr h)]
  refine ⟨hc, ?_⟩
  have hc0 := hc.ne'
  ext i j; fin_cases i <;> fin_cases j <;> simp [Φ] <;> field_simp
  · rw [h11] at hdet; linear_combination -hdet
  · exact h11

/-- **Lemma 4.1.1** (`lem:X-hyperbolic`). The set of `X ∈ 𝔰𝔩₂(ℝ)` with `det X = 1` and
`⟨J, X⟩ < 0` is the adjoint orbit `O_J` of `J`. -/
theorem lemma4_1_1 :
    {X : Mat2 | X.trace = 0 ∧ X.det = 1 ∧ traceForm J X < 0} = adjointOrbit J := by
  ext X
  constructor
  · rintro ⟨htr, hdet, hJ⟩
    obtain ⟨hc, hX⟩ := orb_eq_Φ X htr hdet hJ
    refine ⟨(⟨X 0 0 / X 1 0 + (1 / X 1 0 : ℝ) * Complex.I, by simpa using hc⟩ : ℍ).toSL2R,
      (orb_toSL2R_conj _).trans ((?_ : _ = Φ _ _).trans hX.symm)⟩
    simp [UpperHalfPlane.re, UpperHalfPlane.im]
  · rintro ⟨g, rfl⟩
    obtain ⟨z, p, q, -, hg⟩ := orb_iwasawa g
    have hinv : ((z.toSL2R⁻¹ : SL(2, ℝ)) : Mat2) * (z.toSL2R : Mat2) = 1 := by
      rw [← SpecialLinearGroup.coe_mul, inv_mul_cancel, SpecialLinearGroup.coe_one]
    have hgg : (g : Mat2) * ((g⁻¹ : SL(2, ℝ)) : Mat2) = 1 := by
      rw [← SpecialLinearGroup.coe_mul, mul_inv_cancel, SpecialLinearGroup.coe_one]
    have hk : !![p, -q; q, p] = ((z.toSL2R⁻¹ : SL(2, ℝ)) : Mat2) * (g : Mat2) := by
      rw [hg, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
    have : (g : Mat2) * J * ((g⁻¹ : SL(2, ℝ)) : Mat2) = Φ z.re z.im := calc
      (g : Mat2) * J * ((g⁻¹ : SL(2, ℝ)) : Mat2)
          = (z.toSL2R : Mat2) * (!![p, -q; q, p] * J) * ((g⁻¹ : SL(2, ℝ)) : Mat2) := by
        rw [hg, Matrix.mul_assoc (z.toSL2R : Mat2)]
      _ = (z.toSL2R : Mat2) * J * (!![p, -q; q, p] * ((g⁻¹ : SL(2, ℝ)) : Mat2)) := by
        rw [orb_rot_mul_J]; simp only [Matrix.mul_assoc]
      _ = (z.toSL2R : Mat2) * J * ((z.toSL2R⁻¹ : SL(2, ℝ)) : Mat2) := by
        rw [hk, Matrix.mul_assoc _ (g : Mat2), hgg, Matrix.mul_one]
      _ = Φ z.re z.im := orb_toSL2R_conj z
    change (g : Mat2) * J * ((g⁻¹ : SL(2, ℝ)) : Mat2) ∈ _
    rw [this]
    exact orb_Φ_mem _ _ z.im_pos

/-- The map `Φ` on the upper half-plane `ℍ`: `Φ(x + iy) = [[x/y, -(x² + y²)/y], [1/y, -x/y]]`. -/
noncomputable def ΦH (z : ℍ) : Mat2 := Φ z.re z.im

/-- The equivariance `Φ(g · z) = g Φ(z) g⁻¹` (Remark 4.2.2), proved before Lemma 4.2.1 since the
orbit–stabilizer argument for Lemma 4.2.1 uses it. The book checks it by computer algebra; here it
is the direct computation with `g · z = (az + b)/(cz + d)`, `Im(g · z) = y/|cz + d|²` and
`|g · z|² = |az + b|²/|cz + d|²`. -/
private lemma orb_ΦH_smul (g : SL(2, ℝ)) (z : ℍ) :
    ΦH (g • z) = (g : Mat2) * ΦH z * ((g⁻¹ : SL(2, ℝ)) : Mat2) := by
  have hdet : (g : Mat2) 0 0 * (g : Mat2) 1 1 - (g : Mat2) 0 1 * (g : Mat2) 1 0 = 1 := by
    have := g.det_coe; rwa [det_fin_two] at this
  have hcoe := coe_specialLinearGroup_apply g z
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at hcoe
  set a := (g : Mat2) 0 0
  set b := (g : Mat2) 0 1
  set c := (g : Mat2) 1 0
  set d := (g : Mat2) 1 1
  set x := z.re
  set y := z.im
  have hy : 0 < y := z.im_pos
  have hN : 0 < (c * x + d) ^ 2 + (c * y) ^ 2 := by
    rcases eq_or_ne c 0 with hc | hc
    · have hd : d ≠ 0 := by rintro hd; rw [hc, hd] at hdet; simp at hdet
      simp only [hc, zero_mul, zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, add_zero]
      positivity
    · have : 0 < (c * y) ^ 2 := by positivity
      positivity
  have hnsq : Complex.normSq ((c : ℂ) * z + d) = (c * x + d) ^ 2 + (c * y) ^ 2 := by
    rw [Complex.normSq_apply]; simp [x, y]; ring
  have hnum_re : ((a : ℂ) * z + b).re = a * x + b := by simp [x]
  have hnum_im : ((a : ℂ) * z + b).im = a * y := by simp [y]
  have hden_re : ((c : ℂ) * z + d).re = c * x + d := by simp [x]
  have hden_im : ((c : ℂ) * z + d).im = c * y := by simp [y]
  obtain ⟨N, hN_def⟩ : ∃ N, N = (c * x + d) ^ 2 + (c * y) ^ 2 := ⟨_, rfl⟩
  rw [← hN_def] at hnsq hN
  have hN0 := hN.ne'
  have hy0 := hy.ne'
  have hre : (g • z).re = ((a * x + b) * (c * x + d) + a * c * y ^ 2) / N := by
    rw [← coe_re, hcoe, Complex.div_re, hnsq, hnum_re, hnum_im, hden_re, hden_im]
    field_simp
  have him : (g • z).im = y / N := by
    rw [← coe_im, hcoe, Complex.div_im, hnsq, hnum_re, hnum_im, hden_re, hden_im]
    field_simp
    linear_combination hdet
  have hnorm : (g • z).re ^ 2 + (g • z).im ^ 2 = ((a * x + b) ^ 2 + (a * y) ^ 2) / N := by
    have : (g • z).re ^ 2 + (g • z).im ^ 2 = Complex.normSq ((g • z : ℍ) : ℂ) := by
      rw [Complex.normSq_apply, coe_re, coe_im]; ring
    rw [this, hcoe, Complex.normSq_div, hnsq, Complex.normSq_apply, hnum_re, hnum_im]
    ring
  have hg : (g : Mat2) = !![a, b; c, d] := Matrix.eta_fin_two _
  rw [ΦH, Φ, hnorm, hre, him, SpecialLinearGroup.coe_inv, hg, adjugate_fin_two_of,
    show ΦH z = Φ x y from rfl]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Φ] <;> field_simp <;>
    subst hN_def <;> ring

/-- `Φ(i) = J`. -/
private lemma orb_ΦH_I : ΦH UpperHalfPlane.I = J := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [ΦH, Φ, J, UpperHalfPlane.I_re, UpperHalfPlane.I_im]

/-- The centralizer of `J` in `SL₂(ℝ)` is `SO₂`, which is the stabilizer of `i`: if `k J = J k`,
then `k = [[p, -q], [q, p]]` and `k · i = (pi - q)/(qi + p) = i`. -/
private lemma orb_smul_I_of_comm_J (k : SL(2, ℝ)) (hk : (k : Mat2) * J = J * (k : Mat2)) :
    k • UpperHalfPlane.I = UpperHalfPlane.I := by
  have h01 : (k : Mat2) 0 1 = -(k : Mat2) 1 0 := by
    simpa [J, Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hk 0) 0
  have h11 : (k : Mat2) 1 1 = (k : Mat2) 0 0 := by
    simpa [J, Matrix.mul_apply, Fin.sum_univ_two] using (congrFun (congrFun hk 0) 1).symm
  have hdet : (k : Mat2) 0 0 ^ 2 + (k : Mat2) 1 0 ^ 2 = 1 := by
    have := k.det_coe; rw [det_fin_two, h11, h01] at this; linarith
  have hden : ((k 1 0 : ℝ) : ℂ) * Complex.I + ((k 1 1 : ℝ) : ℂ) ≠ 0 := by
    intro h0
    have hre := congrArg Complex.re h0
    have him := congrArg Complex.im h0
    simp [h11] at hre him
    nlinarith
  apply UpperHalfPlane.ext
  rw [coe_specialLinearGroup_apply]
  simp only [Algebra.algebraMap_self, RingHom.id_apply, coe_I]
  rw [div_eq_iff hden, h01, h11]
  push_cast
  linear_combination (-((k : Mat2) 1 0 : ℂ)) * Complex.I_sq

/-- **Lemma 4.2.1** (`lem:def-phi`). The map `Φ : ℍ → O_J` is an isomorphism (a bijection of the
upper half-plane onto the adjoint orbit of `J`).

Proof as in the book (orbit–stabilizer): every `z ∈ ℍ` is `g · i`, and
`Φ(g · i) = g Φ(i) g⁻¹ = g J g⁻¹` (Remark 4.2.2, `Φ(i) = J`); so `Φ` maps `ℍ` onto `O_J`. If
`g J g⁻¹ = g' J g'⁻¹`, then `g'⁻¹ g` centralizes `J`, hence lies in `SO₂`, the stabilizer of `i`,
and `g · i = g' · i`. -/
theorem lemma4_2_1 : Set.BijOn ΦH Set.univ (adjointOrbit J) := by
  have key : ∀ g : SL(2, ℝ),
      ΦH (g • UpperHalfPlane.I) = (g : Mat2) * J * ((g⁻¹ : SL(2, ℝ)) : Mat2) := fun g ↦ by
    rw [orb_ΦH_smul, orb_ΦH_I]
  refine ⟨fun z _ ↦ ⟨z.toSL2R, (key _).symm.trans (congrArg ΦH (toSL2R_smul_I z))⟩,
    fun z _ w _ h ↦ ?_, fun X ⟨g, hg⟩ ↦ ⟨g • UpperHalfPlane.I, trivial, (key g).trans hg⟩⟩
  rw [← toSL2R_smul_I z, ← toSL2R_smul_I w, key, key] at h
  rw [← toSL2R_smul_I z, ← toSL2R_smul_I w]
  set g := z.toSL2R
  set g' := w.toSL2R
  -- `J` as an element of `SL₂(ℝ)`
  set Jg : SL(2, ℝ) := ⟨J, by simp [J, det_fin_two]⟩
  have h' : g * Jg * g⁻¹ = g' * Jg * g'⁻¹ := by
    apply Subtype.ext
    simpa only [SpecialLinearGroup.coe_mul] using h
  have hk : g'⁻¹ * g * Jg = Jg * (g'⁻¹ * g) := calc
    g'⁻¹ * g * Jg = g'⁻¹ * (g * Jg * g⁻¹) * g := by group
    _ = g'⁻¹ * (g' * Jg * g'⁻¹) * g := by rw [h']
    _ = Jg * (g'⁻¹ * g) := by group
  have hk' := congrArg (fun k : SL(2, ℝ) ↦ (k : Mat2)) hk
  simp only [SpecialLinearGroup.coe_mul] at hk'
  calc g • UpperHalfPlane.I = g' • ((g'⁻¹ * g) • UpperHalfPlane.I) := by
        rw [smul_smul, mul_inv_cancel_left]
    _ = g' • UpperHalfPlane.I := by
        rw [orb_smul_I_of_comm_J _ (by simpa only [SpecialLinearGroup.coe_mul] using hk')]

/-- Remark 4.2.2: `Φ` is `SL₂(ℝ)`-equivariant, `g Φ(z) g⁻¹ = Φ(g · z)` for the action of `SL₂(ℝ)`
on `ℍ` by linear fractional transformations (`orb_ΦH_smul`: the direct computation). -/
theorem ΦH_smul (g : SL(2, ℝ)) (z : ℍ) :
    ΦH (g • z) = (g : Mat2) * ΦH z * ((g⁻¹ : SL(2, ℝ)) : Mat2) :=
  orb_ΦH_smul g z

/-- The Lie algebra `𝔰𝔩₂(ℝ)`, as the subspace of traceless matrices. -/
def sl2 : Submodule ℝ Mat2 := LinearMap.ker (Matrix.traceLinearMap (Fin 2) ℝ ℝ)

/-- The image `{[Y, X] | Y ∈ 𝔰𝔩₂(ℝ)}` of `ad_X` on `𝔰𝔩₂(ℝ)`. -/
def adImage (X : Mat2) : Submodule ℝ Mat2 :=
  sl2.map (LinearMap.mulRight ℝ X - LinearMap.mulLeft ℝ X)

/-- The tangent space at `X` of a set `S` of matrices: the velocities `γ'(0)` of the curves `γ` in
`S` with `γ(0) = X` that are differentiable at `0`. -/
def curveTangentSpace (S : Set Mat2) (X : Mat2) : Set Mat2 :=
  {V | ∃ γ : ℝ → Mat2, (∀ s, γ s ∈ S) ∧ γ 0 = X ∧ HasDerivAtEntrywise γ V 0}

/-- For traceless `Y`, `det (exp (s • Y)) = 1`: the derivative of `s ↦ det (exp (s • Y))` is
`det (exp (s • Y)) · tr Y = 0`. -/
private lemma orb_det_exp_smul (Y : Mat2) (hY : Y.trace = 0) (s : ℝ) :
    (NormedSpace.exp (s • Y)).det = 1 := by
  have hd : ∀ t, HasDerivAt (fun s : ℝ ↦ (NormedSpace.exp (s • Y)).det) 0 t := by
    intro t
    convert (Matrix.hasDerivAtEntrywise_exp_smul_const Y t).det_fin_two using 1
    rw [trace_fin_two] at hY
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (-((NormedSpace.exp (t • Y)) 0 0 * (NormedSpace.exp (t • Y)) 1 1 -
      (NormedSpace.exp (t • Y)) 0 1 * (NormedSpace.exp (t • Y)) 1 0)) * hY
  have := is_const_of_deriv_eq_zero (fun t ↦ (hd t).differentiableAt) (fun t ↦ (hd t).deriv) s 0
  rw [this, zero_smul, NormedSpace.exp_zero, det_one]

/-- The centralizer of a nonzero `X ∈ 𝔰𝔩₂(ℝ)` in `𝔰𝔩₂(ℝ)` is `ℝX`: "the element `X` is regular in
the rank one algebra `𝔰𝔩₂(ℝ)`, so that its centralizer is the span `ℝX`". For
`X = [[a, b], [c, -a]]` and `Y = [[α, β], [γ, -α]]`, `[Y, X] = 0` says `βc = bγ`, `αb = aβ`,
`aγ = αc`, so `Y` is proportional to `X`. -/
theorem orb_centralizer (X Y : Mat2) (hX : X.trace = 0) (hX0 : X ≠ 0) (hY : Y.trace = 0)
    (hXY : Y * X - X * Y = 0) : ∃ k : ℝ, Y = k • X := by
  rw [trace_fin_two] at hX hY
  have e00 : (Y * X - X * Y) 0 0 = 0 := by rw [hXY]; rfl
  have e01 : (Y * X - X * Y) 0 1 = 0 := by rw [hXY]; rfl
  have e10 : (Y * X - X * Y) 1 0 = 0 := by rw [hXY]; rfl
  simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10
  have hX11 : X 1 1 = -X 0 0 := by linarith
  have hY11 : Y 1 1 = -Y 0 0 := by linarith
  rw [hX11, hY11] at e01 e10
  have hX' : X 0 0 ≠ 0 ∨ X 0 1 ≠ 0 ∨ X 1 0 ≠ 0 := by
    by_contra h
    push Not at h
    exact hX0 (by ext i j; fin_cases i <;> fin_cases j <;> simp [h.1, h.2.1, h.2.2, hX11])
  rcases hX' with ha | hb | hc
  · refine ⟨Y 0 0 / X 0 0, ?_⟩
    ext i j; fin_cases i <;> fin_cases j <;> simp [hX11, hY11] <;> field_simp
    · linear_combination (-1 / 2 : ℝ) * e01
    · linear_combination (1 / 2 : ℝ) * e10
  · refine ⟨Y 0 1 / X 0 1, ?_⟩
    ext i j; fin_cases i <;> fin_cases j <;> simp [hX11, hY11] <;> field_simp
    · linear_combination (1 / 2 : ℝ) * e01
    · linear_combination -e00
    · linear_combination (1 / 2 : ℝ) * e01
  · refine ⟨Y 1 0 / X 1 0, ?_⟩
    ext i j; fin_cases i <;> fin_cases j <;> simp [hX11, hY11] <;> field_simp
    · linear_combination (-1 / 2 : ℝ) * e10
    · linear_combination e00
    · linear_combination (-1 / 2 : ℝ) * e10

/-- `ad_X` on `𝔰𝔩₂(ℝ)`: `Y ↦ [Y, X]`, whose range is `adImage X`. -/
noncomputable def orb_adSl2 (X : Mat2) : sl2 →ₗ[ℝ] Mat2 :=
  (LinearMap.mulRight ℝ X - LinearMap.mulLeft ℝ X).domRestrict sl2

theorem orb_adSl2_apply (X : Mat2) (Y : sl2) : orb_adSl2 X Y = (Y : Mat2) * X - X * Y := rfl

theorem orb_range_adSl2 (X : Mat2) : LinearMap.range (orb_adSl2 X) = adImage X :=
  LinearMap.range_domRestrict _ _

/-- The kernel of `ad_X` on `𝔰𝔩₂(ℝ)` (the centralizer `𝔰𝔩₂(ℝ)_X`) is `ℝX` for `X ≠ 0`. -/
theorem orb_ker_adSl2 (X : Mat2) (hX : X.trace = 0) (hX0 : X ≠ 0) :
    LinearMap.ker (orb_adSl2 X) = ℝ ∙ (⟨X, by simpa [sl2] using hX⟩ : sl2) := by
  ext Y
  rw [LinearMap.mem_ker, Submodule.mem_span_singleton, orb_adSl2_apply]
  constructor
  · intro h
    obtain ⟨k, hk⟩ := orb_centralizer X Y hX hX0 (by simpa [sl2] using Y.2) h
    exact ⟨k, Subtype.ext hk.symm⟩
  · rintro ⟨k, rfl⟩
    change (k • X) * X - X * (k • X) = 0
    rw [Matrix.smul_mul, Matrix.mul_smul, sub_self]

/-- `dim 𝔰𝔩₂(ℝ) = 3`. -/
theorem orb_finrank_sl2 : Module.finrank ℝ sl2 = 3 := by
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.traceLinearMap (Fin 2) ℝ ℝ)
  have hr : LinearMap.range (Matrix.traceLinearMap (Fin 2) ℝ ℝ) = ⊤ :=
    LinearMap.range_eq_top.mpr fun r ↦ ⟨Matrix.diagonal ![r, 0], by simp⟩
  rw [hr, finrank_top, Module.finrank_matrix] at h
  simp only [Module.finrank_self, Fintype.card_fin] at h
  change Module.finrank ℝ (LinearMap.ker (Matrix.traceLinearMap (Fin 2) ℝ ℝ)) = 3
  omega

/-- `dim {[Y, X] | Y ∈ 𝔰𝔩₂(ℝ)} = dim 𝔰𝔩₂(ℝ) - dim ℝX = 2` for `X ≠ 0`. -/
theorem orb_finrank_adImage (X : Mat2) (hX : X.trace = 0) (hX0 : X ≠ 0) :
    Module.finrank ℝ (adImage X) = 2 := by
  have h := LinearMap.finrank_range_add_finrank_ker (orb_adSl2 X)
  rw [orb_range_adSl2, orb_ker_adSl2 X hX hX0, finrank_span_singleton, orb_finrank_sl2] at h
  · omega
  · exact fun h ↦ hX0 (congrArg Subtype.val h)

/-- `X^⊥ = {[W, X] | W ∈ 𝔰𝔩₂(ℝ)}` for `X ∈ 𝔰𝔩₂(ℝ)`, `X ≠ 0` (Lemma 6.8.1, the argument of the
book): `⟨[W, X], X⟩ = ⟨W, [X, X]⟩ = 0`, and both spaces have dimension two. -/
theorem orb_adImage_eq_perp (X : Mat2) (hX : X.trace = 0) (hX0 : X ≠ 0) :
    adImage X =
      sl2 ⊓ LinearMap.ker ((Matrix.traceLinearMap (Fin 2) ℝ ℝ).comp (LinearMap.mulRight ℝ X)) := by
  set P := sl2 ⊓ LinearMap.ker ((Matrix.traceLinearMap (Fin 2) ℝ ℝ).comp (LinearMap.mulRight ℝ X))
  have hle : adImage X ≤ P := by
    rintro _ ⟨W, hW, rfl⟩
    refine ⟨?_, ?_⟩
    · change Matrix.trace (W * X - X * W) = 0
      rw [trace_sub, trace_mul_comm W X, sub_self]
    · simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.mulRight_apply, LinearMap.sub_apply, LinearMap.mulLeft_apply,
        traceLinearMap_apply, Matrix.sub_mul, trace_sub]
      rw [Matrix.mul_assoc X W X, trace_mul_comm X (W * X), Matrix.mul_assoc, sub_self]
  -- `P` is a proper subspace of `𝔰𝔩₂(ℝ)`: some traceless `V` has `⟨V, X⟩ ≠ 0`
  have hlt : P < sl2 := by
    refine lt_of_le_of_ne inf_le_left fun hP ↦ ?_
    have hmem : ∀ V : Mat2, V.trace = 0 → (V * X).trace = 0 := fun V hV ↦ by
      have : V ∈ P := hP ▸ (show V ∈ sl2 by simpa [sl2] using hV)
      simpa using this.2
    rw [trace_fin_two] at hX
    have h1 := hmem !![1, 0; 0, -1] (by simp [trace_fin_two])
    have h2 := hmem !![0, 1; 0, 0] (by simp [trace_fin_two])
    have h3 := hmem !![0, 0; 1, 0] (by simp [trace_fin_two])
    rw [Matrix.eta_fin_two X] at h1 h2 h3
    simp [trace_fin_two] at h1 h2 h3
    exact hX0 (by ext i j; fin_cases i <;> fin_cases j <;> simp <;> linarith)
  have h3 : Module.finrank ℝ P < 3 := orb_finrank_sl2 ▸ Submodule.finrank_lt_finrank_of_lt hlt
  exact Submodule.eq_of_le_of_finrank_le hle (by rw [orb_finrank_adImage X hX hX0]; omega)

/-- **Lemma 4.2.3** (`lem:half-plane-lie-algebra-iso`). For `X ∈ 𝔰𝔩₂(ℝ)`, `X ≠ 0`, the tangent space
of the adjoint orbit is `T_X O_X = {[Y, X] | Y ∈ 𝔰𝔩₂(ℝ)} ≅ 𝔰𝔩₂(ℝ)/ℝX`, the isomorphism sending
`[Y, X]` to `Y + ℝX`.

The book states the lemma for every `X ∈ 𝔰𝔩₂(ℝ)`; for `X = 0` the orbit is a point and
`𝔰𝔩₂(ℝ)/ℝX = 𝔰𝔩₂(ℝ)` is not isomorphic to `T_0 O_0 = 0`. The proof uses that `X` is regular,
which in `𝔰𝔩₂` means `X ≠ 0`, and the lemma is applied to `X ∈ O_J`; the hypothesis `X ≠ 0`
corrects this slip.

Proof as in the book: the curves `Ad_{exp(sY)} X` give `[Y, X] ∈ T_X O_X`, and
`𝔰𝔩₂(ℝ)/𝔰𝔩₂(ℝ)_X ≅ {[Y, X]}` with centralizer `𝔰𝔩₂(ℝ)_X = ℝX` (`orb_ker_adSl2`). Gap filled: the
book does not argue the inclusion `T_X O_X ⊆ {[Y, X]}`. Here: along a curve in `O_X` the trace and
the determinant are constant, so its velocity `V` is traceless with `⟨V, X⟩ = 0` (the derivative
of `det` is `-⟨V, X⟩`), and `X^⊥ = {[Y, X]}` by the dimension count of Lemma 6.8.1
(`orb_adImage_eq_perp`). -/
theorem lemma4_2_3 (X : Mat2) (hX : X.trace = 0) (hX0 : X ≠ 0) :
    curveTangentSpace (adjointOrbit X) X = adImage X ∧
      ∃ e : (sl2 ⧸ (ℝ ∙ (⟨X, by simpa [sl2] using hX⟩ : sl2))) ≃ₗ[ℝ] adImage X,
        ∀ Y : sl2, (e (Submodule.Quotient.mk Y) : Mat2) = (Y : Mat2) * X - X * (Y : Mat2) := by
  refine ⟨?_, ?_⟩
  · ext V
    constructor
    · rintro ⟨γ, hγ, hγ0, hV⟩
      -- along a curve in the orbit, the trace and the determinant are constant
      have htr : ∀ s, (γ s).trace = 0 := fun s ↦ by
        obtain ⟨g, hg⟩ := hγ s
        simp only at hg
        rw [← hg, trace_mul_comm, ← Matrix.mul_assoc, ← SpecialLinearGroup.coe_mul, inv_mul_cancel,
          SpecialLinearGroup.coe_one, Matrix.one_mul, hX]
      have hdet : ∀ s, (γ s).det = X.det := fun s ↦ by
        obtain ⟨g, hg⟩ := hγ s
        simp only at hg
        rw [← hg, det_mul, det_mul, SpecialLinearGroup.det_coe, SpecialLinearGroup.det_coe,
          one_mul, mul_one]
      have hVtr : V.trace = 0 := by
        have h2 : HasDerivAt (fun s ↦ (γ s).trace) 0 0 := by
          simp only [htr]; exact hasDerivAt_const _ _
        exact hV.trace.unique h2
      have hVX : traceForm V X = 0 := by
        have h2 : HasDerivAt (fun s ↦ (γ s).det) 0 0 := by
          simp only [hdet]; exact hasDerivAt_const _ _
        have h := hV.det_fin_two.unique h2
        rw [hγ0] at h
        rw [trace_fin_two] at hVtr hX
        simp only [traceForm, trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
        linear_combination -h + (V 0 0 + V 1 1) * hX
      have hmem : V ∈ sl2 ⊓
          LinearMap.ker ((Matrix.traceLinearMap (Fin 2) ℝ ℝ).comp (LinearMap.mulRight ℝ X)) :=
        ⟨hVtr, hVX⟩
      rw [← orb_adImage_eq_perp X hX hX0] at hmem
      exact hmem
    · rintro ⟨Y, hY, rfl⟩
      have hYtr : Y.trace = 0 := hY
      -- the curve `s ↦ Ad_{exp(sY)} X` in the orbit
      let g : ℝ → SL(2, ℝ) := fun s ↦ ⟨NormedSpace.exp (s • Y), orb_det_exp_smul Y hYtr s⟩
      have hginv : ∀ s, (((g s)⁻¹ : SL(2, ℝ)) : Mat2) = NormedSpace.exp (-s • Y) := by
        intro s
        have : (g s)⁻¹ = ⟨NormedSpace.exp (-s • Y), orb_det_exp_smul Y hYtr (-s)⟩ :=
          inv_eq_of_mul_eq_one_right (Subtype.ext (exp_smul_mul_exp_neg_smul Y s))
        rw [this]
      refine ⟨fun s ↦ (g s : Mat2) * X * (((g s)⁻¹ : SL(2, ℝ)) : Mat2), fun s ↦ ⟨g s, rfl⟩, ?_, ?_⟩
      · simp only [hginv, neg_zero]
        simp [g]
      · simp only [hginv]
        convert ((hasDerivAtEntrywise_exp_smul_const' Y 0).mul_const X).mul
          (hasDerivAtEntrywise_exp_neg_smul_const' Y 0) using 1
        simp [sub_eq_add_neg]
  · exact ⟨(Submodule.quotEquivOfEq _ _ (orb_ker_adSl2 X hX hX0)).symm.trans
      ((orb_adSl2 X).quotKerEquivRange.trans (LinearEquiv.ofEq _ _ (orb_range_adSl2 X))),
      fun Y ↦ rfl⟩

/-- The matrix `Y_z(r₁, r₂) = [[r₂/(2y), (y r₁ - r₂ x)/y], [0, -r₂/(2y)]]` that represents the
tangent vector `T_zΦ(r₁ ∂/∂x + r₂ ∂/∂y)` modulo `ℝX` (Lemma 4.2.4). -/
noncomputable def tangentLift (x y r₁ r₂ : ℝ) : Mat2 :=
  !![r₂ / (2 * y), (y * r₁ - r₂ * x) / y; 0, -r₂ / (2 * y)]

/-- **Lemma 4.2.4** (`lem:tangent-maps`). The tangent map of `Φ` at `z = x + iy` sends
`r₁ ∂/∂x + r₂ ∂/∂y` to `[Y_z(r₁, r₂), Φ(z)]`, that is, to the class of `Y_z(r₁, r₂)` in
`𝔰𝔩₂(ℝ)/ℝX ≅ T_X O_X`. -/
theorem lemma4_2_4 (x y r₁ r₂ : ℝ) (hy : 0 < y) :
    HasDerivAtEntrywise (fun s ↦ Φ (x + s * r₁) (y + s * r₂))
      (tangentLift x y r₁ r₂ * Φ x y - Φ x y * tangentLift x y r₁ r₂) 0 := by
  have hX : HasDerivAt (fun s : ℝ ↦ x + s * r₁) r₁ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const r₁).const_add x
  have hY : HasDerivAt (fun s : ℝ ↦ y + s * r₂) r₂ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const r₂).const_add y
  have hy0 : y + 0 * r₂ ≠ 0 := by simpa using hy.ne'
  have hy0' := hy.ne'
  rw [hasDerivAtEntrywise_fin_two_iff]
  simp only [Φ, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert hX.div hY hy0 using 1
    simp [tangentLift]; field_simp; ring
  · convert ((hX.pow 2).add (hY.pow 2)).neg.div hY hy0 using 1
    simp [tangentLift]; field_simp; ring
  · convert (hasDerivAt_const (0 : ℝ) (1 : ℝ)).div hY hy0 using 1
    simp [tangentLift]; field_simp; ring
  · convert hX.neg.div hY hy0 using 1
    simp [tangentLift]; field_simp; ring

end SmoothedPolygons
