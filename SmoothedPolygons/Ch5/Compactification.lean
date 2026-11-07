module

public import SmoothedPolygons.Ch4.AdjointOrbit
public import SmoothedPolygons.Ch4.StarDomain
public import Mathlib.Topology.MetricSpace.ProperSpace.Real

/-!
# The compactification `𝔥**` of the star domain (Definition 5.0.1)

Chapter 5 (TeX 3856–4516) cuts the open, unbounded star domain
`𝔥* = {x + iy | |x| < 1/√3, x² + y² > 1/3}` (`starDomain`, a subset of `ℝ × ℝ`) down to an
explicit compact set `𝔥**` (Definition 5.0.1, TeX 3918–3946) by removing three open horoballs at
the cusps and three open half-planes (in the sense of the book: regions bounded by a line or a
circle) along the edges:

* `B(i∞) = {y > 4.5}` (`horoballAtInfty`), and `B(±1/√3) = R^{±1} B(i∞)`, the images under the
  linear fractional transformations `R` and `R²` (`R² = -R⁻¹` acts on `ℍ` as `R⁻¹`);
* `Π₀⁺ = {y > 15(1/√3 - x)}` (`edgeHalfPlane`), a neighbourhood of the edge `x = 1/√3`, and
  `Π₁⁺ = R Π₀⁺`, `Π₂⁺ = R² Π₀⁺`;
* `𝔥** = 𝔥* \ (B(i∞) ∪ B(1/√3) ∪ B(-1/√3) ∪ Π₀⁺ ∪ Π₁⁺ ∪ Π₂⁺)` (`truncatedStarDomain`).

Points of the upper half-plane are pairs `(x, y)` with `y > 0`, as in `starDomain`; a real
`2 × 2` matrix `A = [[a, b], [c, d]]` acts by `z ↦ (az + b)/(cz + d)` (`lftAct`, in coordinates),
the reflection `S` of §4.6 by `z ↦ -z̄` (`reflAct`). The dihedral group of §4.6 acts on `𝔥*`
through these maps (`Φ_lftAct`, Remark 4.2.2; `reflS_conj_Φ`).

## Statements

* `lftAct_image_horoball` (TeX 3904–3915): for `A` with `det A > 0` and `c ≠ 0`, the image of the
  horoball `{y > y₀}` is the open disk tangent to the real axis at `A · ∞ = a/c`, of radius
  `r = det A/(2y₀c²)`; with `A = R^{±1}`, `y₀ = 4.5`, the radius is `4/27`
  (`lftAct_R_horoballAtInfty`, `lftAct_R_sq_horoballAtInfty`, TeX 3922–3925);
* the images of `Π₀⁺` (`lftAct_R_edgeHalfPlane`, `lftAct_R_sq_edgeHalfPlane`): `Π₁⁺` is the inside
  of the circle `x² + (y - 1/(15√3))² = 1/3 + 1/675` through `±1/√3`, and `Π₂⁺` is the mirror image
  `{y > 15(x + 1/√3)}` of `Π₀⁺`;
* `truncatedStarDomain_eq`: `𝔥**` by explicit inequalities;
* `isCompact_truncatedStarDomain`: `𝔥**` is compact (asserted at TeX 3975, not proved there);
* `image_lftAct_R_starDomain`, `image_reflAct_starDomain` (§4.6, TeX 3779) and
  `image_lftAct_R_truncatedStarDomain`, `image_reflAct_truncatedStarDomain` (TeX 3976–3977): the
  dihedral group preserves `𝔥*` and `𝔥**`;
* the fundamental domain `{x ≥ 0, (x - 1/√3)² + y² ≥ 4/3}` of the dihedral action on `𝔥*`
  (`fundamentalDomain`, `exists_dihedralAct_mem_fundamentalDomain`) and the sets of
  Definition 5.0.1 that meet it (`mem_horoball_or_edgeHalfPlane_of_mem_fundamentalDomain`), used
  in the proof of Theorem 5.0.2 (TeX 4470–4484).

## Readings and corrections

* **The fundamental domain (TeX 4479).** The proof of Theorem 5.0.2 writes
  `{x ≥ 0, (x - 1/√3)² + y² = 4/3}`, a curve; §4.6 (TeX 3807) gives the sector with `≤ 4/3`. The
  proof needs the sector with `≥ 4/3`, which lies in `{x ≥ 0, y ≥ 1}` (TeX 4480); both sectors are
  fundamental domains (the six sectors cut out by the three medians through `i` are permuted
  simply transitively). We use `≥ 4/3`.
* **`Π₂⁺` (TeX 4500–4501).** "The regions `Π₁⁺` and `Π₂⁺` do not meet the fundamental domain" is
  false for `Π₂⁺ = {y > 15(x + 1/√3)}`, which meets `{x ≥ 0, y ≥ 1}` where `y > 15/√3 ≈ 8.66`.
  Those points lie in `B(i∞)`, so the proof is unaffected;
  `mem_horoball_or_edgeHalfPlane_of_mem_fundamentalDomain` states what the proof uses.

## Proofs

* `Φ_lftAct`: `ΦH_smul` (Remark 4.2.2) for `A ∈ SL₂(ℝ)`; `lftAct A z` is the pair of real and
  imaginary parts of `(az + b)/(cz + d)` (`(az + b)\overline{(cz + d)} = P + i det(A) y`), which
  is `UpperHalfPlane.coe_specialLinearGroup_apply`.
* `lftAct_image_horoball`: `|A · z - a/c|² = det(A)²/(c²|cz + d|²)` and
  `Im(A · z) = det(A) y/|cz + d|²`, so
  `|A · z - (a/c + ir)|² - r² = det(A)²(y₀ - y)/(c²y₀|cz + d|²)`;
  `lftAct A` is a bijection of the upper half-plane with inverse `lftAct (adjugate A)` (the
  composition rule `A · (B · z) = (AB) · z` is checked in `ℂ`, and scalar matrices act
  trivially). The book gives the formula without proof. `lftAct_R_horoballAtInfty` and
  `lftAct_R_sq_horoballAtInfty` follow with `R = [[1/2, -√3/2], [√3/2, 1/2]]`,
  `R² = [[-1/2, -√3/2], [√3/2, -1/2]]`, `c² = 3/4`.
* `lftAct_R_edgeHalfPlane`, `lftAct_R_sq_edgeHalfPlane`: by the explicit identities
  `|Rz|² - 2 Im(Rz)/(15√3) - 1/3 = 2(15(1/√3 - x) - y)/(15√3 |cz + d|²)` and
  `Im(R²z) - 15(Re(R²z) + 1/√3) = (y - 15(1/√3 - x))/|cz + d|²` (exact computations with
  `√3² = 3`), and the bijectivity of `lftAct A` on the upper half-plane.
* `truncatedStarDomain_eq`: from the four image lemmas.
* `isCompact_truncatedStarDomain`: closed and bounded. Bounded: `y ≤ 4.5`, `|x| < 1/√3`. A lower
  bound on `y`: the conditions of `Π₁⁺` give `x² + y² ≥ 1/3 + 2y/(15√3)`, and those of `Π₀⁺`,
  `Π₂⁺` give `|x| ≤ 1/√3 - y/15`; together they give
  `y ≥ (4/(15√3))·(225/226) > 0.15` on `𝔥**`. So `𝔥**` is the set of the closed versions of the
  explicit inequalities intersected with `{y ≥ 0.15}`, which is closed. (The closed inequalities
  alone do not suffice: the cusps `(±1/√3, 0)` satisfy all of them, as isolated points.)
* Dihedral invariance: the invariance of `𝔥*` is §4.6: `R` and `X ↦ -S X S⁻¹` permute the star
  functions (`ρ_R_conj`, `ρ_reflS_conj`) and preserve trace zero and determinant one, so they
  preserve the star states; by `theorem4_4_1`, `Φ_lftAct` and `reflS_conj_Φ` they preserve `𝔥*`.
  For `𝔥**`: `R` permutes `S, RS, R²S` for `S = B(i∞)` and `S = Π₀⁺` (`R³ = -I` acts
  trivially); `S` fixes `B(i∞)` and `Π₁⁺` and exchanges `B(1/√3) ↔ B(-1/√3)`, `Π₀⁺ ↔ Π₂⁺`
  (explicit forms). `dihedralAct_mem_iff` by induction on `n`.
* Fundamental domain: with `f_±(z) = (x ± 1/√3)² + y² - 4/3` (the medians `x = 0` and
  `f_∓ = 0` through `i`), the explicit identities `Re(Rz) = √3 f₋(z)/(4N)`,
  `f₊(Rz) = -4x/(√3 N)`, `f₋(Rz) = -f₊(z)/N` (`N = |cz + d|² > 0`) show that one of `z`, `Rz`,
  `R²z` has `f₊ ≥ 0` and `f₋ ≥ 0` (`z` if both hold; `Rz` if `x < 0`, since then `f₊(z) < 0`;
  `R²z` if `x ≥ 0`, since then `f₋(z) < 0`), and then that point or its mirror image `-z̄` lies
  in the sector `{x ≥ 0, f₋ ≥ 0}`. The intersections: `B(±1/√3)` lies in `y < 8/27` and `Π₁⁺`
  in `y < 0.62`, below `y = 1`; `Π₂⁺ ∩ {x ≥ 0}` lies in `y > 15/√3 > 4.5`.
-/

@[expose] public section

namespace SmoothedPolygons

open Set

/-- The linear fractional transformation `z ↦ (az + b)/(cz + d)` of a real matrix
`A = [[a, b], [c, d]]`, in the coordinates `z = (x, y)` of the upper half-plane:
`Re(A · z) = ((ax + b)(cx + d) + acy²)/|cz + d|²` and `Im(A · z) = det(A) y/|cz + d|²`, with
`|cz + d|² = (cx + d)² + (cy)²`. -/
noncomputable def lftAct (A : Mat2) (z : ℝ × ℝ) : ℝ × ℝ :=
  (((A 0 0 * z.1 + A 0 1) * (A 1 0 * z.1 + A 1 1) + A 0 0 * A 1 0 * z.2 ^ 2) /
      ((A 1 0 * z.1 + A 1 1) ^ 2 + (A 1 0 * z.2) ^ 2),
    A.det * z.2 / ((A 1 0 * z.1 + A 1 1) ^ 2 + (A 1 0 * z.2) ^ 2))

/-- The action `z ↦ -z̄` of the reflection `S` of §4.6 on the upper half-plane
(`-S Φ(z) S⁻¹ = Φ(-z̄)`, `reflS_conj_Φ`). -/
def reflAct (z : ℝ × ℝ) : ℝ × ℝ := (-z.1, z.2)

/-- The element `S^b R^n` of the dihedral group of §4.6 acting on the upper half-plane:
`z ↦ R^n · z`, followed by `z ↦ -z̄` if `b`. -/
noncomputable def dihedralAct (n : ℕ) (b : Bool) (z : ℝ × ℝ) : ℝ × ℝ :=
  if b then reflAct (lftAct (R ^ n) z) else lftAct (R ^ n) z

/-- The open horoball `B(i∞) = {y > 4.5}` at the cusp `i∞` of `𝔥*` (Definition 5.0.1). -/
def horoballAtInfty : Set (ℝ × ℝ) := {z | 9 / 2 < z.2}

/-- The open half-plane `Π₀⁺ = {y > 15(1/√3 - x)}` of the upper half-plane, a neighbourhood of
the edge `x = 1/√3`, `y > 0`, of `𝔥*` (Definition 5.0.1). -/
noncomputable def edgeHalfPlane : Set (ℝ × ℝ) := {z | 0 < z.2 ∧ 15 * (1 / √3 - z.1) < z.2}

/-- **Definition 5.0.1** (compactification). The truncated star domain
`𝔥** = 𝔥* \ (B(i∞) ∪ B(1/√3) ∪ B(-1/√3) ∪ Π₀⁺ ∪ Π₁⁺ ∪ Π₂⁺)`, where `B(1/√3) = R B(i∞)`,
`B(-1/√3) = R² B(i∞)`, `Π₁⁺ = R Π₀⁺` and `Π₂⁺ = R² Π₀⁺`, the images under the linear fractional
transformations `R`, `R²` (TeX 3918–3946). -/
noncomputable def truncatedStarDomain : Set (ℝ × ℝ) :=
  starDomain \ (horoballAtInfty ∪ lftAct R '' horoballAtInfty ∪ lftAct (R ^ 2) '' horoballAtInfty ∪
    edgeHalfPlane ∪ lftAct R '' edgeHalfPlane ∪ lftAct (R ^ 2) '' edgeHalfPlane)

/-- The fundamental domain `{z ∈ 𝔥* | x ≥ 0, (x - 1/√3)² + y² ≥ 4/3}` of the action of the
dihedral group on `𝔥*` used in the proof of Theorem 5.0.2 (TeX 4477–4479, where `= 4/3` is printed
for `≥ 4/3`; see the module docstring). -/
noncomputable def fundamentalDomain : Set (ℝ × ℝ) :=
  {z | z ∈ starDomain ∧ 0 ≤ z.1 ∧ 4 / 3 ≤ (z.1 - 1 / √3) ^ 2 + z.2 ^ 2}

/-! ### Linear fractional transformations in complex form -/

/-- The point `x + iy` of `ℂ`. -/
private def cp_toC (z : ℝ × ℝ) : ℂ := ⟨z.1, z.2⟩

/-- The map `w ↦ (aw + b)/(cw + d)` on `ℂ` (with `w/0 = 0`). -/
private noncomputable def cp_mob (A : Mat2) (w : ℂ) : ℂ :=
  ((A 0 0 : ℂ) * w + (A 0 1 : ℂ)) / ((A 1 0 : ℂ) * w + (A 1 1 : ℂ))

/-- `lftAct` is the real and imaginary parts of `(az + b)/(cz + d)`:
`(az + b) \overline{(cz + d)} = P + i det(A) y`. -/
private lemma cp_lftAct_eq (A : Mat2) (z : ℝ × ℝ) :
    lftAct A z = ((cp_mob A (cp_toC z)).re, (cp_mob A (cp_toC z)).im) := by
  have hN : Complex.normSq ((A 1 0 : ℂ) * cp_toC z + (A 1 1 : ℂ)) =
      (A 1 0 * z.1 + A 1 1) ^ 2 + (A 1 0 * z.2) ^ 2 := by
    simp [Complex.normSq_apply, cp_toC]; ring
  ext
  · simp only [lftAct, cp_mob, Complex.div_re, hN]
    simp [cp_toC]
    ring
  · simp only [lftAct, cp_mob, Complex.div_im, hN, Matrix.det_fin_two]
    simp [cp_toC]
    ring

private lemma cp_toC_lftAct (A : Mat2) (z : ℝ × ℝ) : cp_toC (lftAct A z) = cp_mob A (cp_toC z) := by
  rw [cp_lftAct_eq]; rfl

/-- `cw + d ≠ 0` on the upper half-plane when `det A ≠ 0`. -/
private lemma cp_den_ne {A : Mat2} (hA : A.det ≠ 0) {w : ℂ} (hw : 0 < w.im) :
    (A 1 0 : ℂ) * w + (A 1 1 : ℂ) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    add_zero, Complex.zero_im, Complex.add_re, Complex.mul_re, sub_zero,
    Complex.zero_re] at him hre
  rcases mul_eq_zero.1 him with hc | hw0
  · rw [hc, zero_mul, zero_add] at hre
    apply hA
    rw [Matrix.det_fin_two, hc, hre]; ring
  · linarith

/-- `A · (B · w) = (AB) · w`. -/
private lemma cp_mob_mul (A B : Mat2) {w : ℂ} (hw : (B 1 0 : ℂ) * w + (B 1 1 : ℂ) ≠ 0) :
    cp_mob A (cp_mob B w) = cp_mob (A * B) w := by
  simp only [cp_mob, Matrix.mul_apply, Fin.sum_univ_two]
  rw [mul_div_assoc', mul_div_assoc', div_add' _ _ _ hw, div_add' _ _ _ hw,
    div_div_div_cancel_right₀ hw]
  push_cast
  congr 1 <;> ring

/-- `|cz + d|² > 0` on the upper half-plane when `det A ≠ 0`. -/
private lemma cp_N_pos {A : Mat2} (hA : A.det ≠ 0) {z : ℝ × ℝ} (hz : 0 < z.2) :
    0 < (A 1 0 * z.1 + A 1 1) ^ 2 + (A 1 0 * z.2) ^ 2 := by
  rcases eq_or_ne (A 1 0) 0 with hc | hc
  · have hd : A 1 1 ≠ 0 := by
      intro hd; apply hA; rw [Matrix.det_fin_two, hc, hd]; ring
    simp only [hc, zero_mul, zero_add]
    positivity
  · have : 0 < (A 1 0 * z.2) ^ 2 := by positivity
    positivity

/-- `Im(A · z) = det(A) y/|cz + d|² > 0` for `det A > 0`. -/
private lemma cp_lftAct_snd_pos {A : Mat2} (hA : 0 < A.det) {z : ℝ × ℝ} (hz : 0 < z.2) :
    0 < (lftAct A z).2 :=
  div_pos (mul_pos hA hz) (cp_N_pos hA.ne' hz)

/-- `A · (B · z) = (AB) · z` on the upper half-plane. -/
private lemma cp_lftAct_mul (A : Mat2) {B : Mat2} (hB : B.det ≠ 0) {z : ℝ × ℝ} (hz : 0 < z.2) :
    lftAct A (lftAct B z) = lftAct (A * B) z := by
  rw [cp_lftAct_eq A, cp_toC_lftAct, cp_mob_mul A B (cp_den_ne hB hz), ← cp_lftAct_eq]

/-- Scalar matrices act trivially. -/
private lemma cp_lftAct_smul_one {c : ℝ} (hc : c ≠ 0) (z : ℝ × ℝ) : lftAct (c • 1) z = z := by
  ext
  · simp [lftAct]; field_simp
  · simp [lftAct]; field_simp

private lemma cp_lftAct_neg (A : Mat2) (z : ℝ × ℝ) : lftAct (-A) z = lftAct A z := by
  ext
  · simp only [lftAct, Matrix.neg_apply]; ring_nf
  · simp only [lftAct, Matrix.neg_apply, Matrix.det_neg, Fintype.card_fin]; ring_nf

private lemma cp_lftAct_negOne (z : ℝ × ℝ) : lftAct (-1) z = z := by
  rw [cp_lftAct_neg, ← one_smul ℝ (1 : Mat2), cp_lftAct_smul_one one_ne_zero]

/-- `adj(A) · (A · z) = z`. -/
private lemma cp_adj_lftAct {A : Mat2} (hA : 0 < A.det) {z : ℝ × ℝ} (hz : 0 < z.2) :
    lftAct (Matrix.adjugate A) (lftAct A z) = z := by
  rw [cp_lftAct_mul _ hA.ne' hz, Matrix.adjugate_mul, cp_lftAct_smul_one hA.ne']

/-- To compute the image of `S` under `A` (with `det A > 0`), it suffices to know which points
of the upper half-plane are mapped into `T`: the map is a bijection of the upper half-plane, with
inverse `adj(A)`. -/
private lemma cp_image_eq {A : Mat2} (hA : 0 < A.det) {S T : Set (ℝ × ℝ)}
    (hT : ∀ w ∈ T, 0 < w.2) (h : ∀ z : ℝ × ℝ, 0 < z.2 → (z ∈ S ↔ lftAct A z ∈ T))
    (hS : ∀ z ∈ S, 0 < z.2) : lftAct A '' S = T := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (h z (hS z hz)).1 hz
  · intro hw
    have hw2 := hT w hw
    have hadj : 0 < (Matrix.adjugate A).det := by
      rw [Matrix.det_adjugate, Fintype.card_fin]; simpa using hA
    have hz2 := cp_lftAct_snd_pos hadj hw2
    have hAz : lftAct A (lftAct (Matrix.adjugate A) w) = w := by
      rw [cp_lftAct_mul A hadj.ne' hw2, Matrix.mul_adjugate, cp_lftAct_smul_one hA.ne']
    exact ⟨_, (h _ hz2).2 (by rw [hAz]; exact hw), hAz⟩

/-- `A · z ∈ A S ↔ z ∈ S` on the upper half-plane. -/
private lemma cp_mem_image_iff {A : Mat2} (hA : 0 < A.det) {S : Set (ℝ × ℝ)}
    (hS : ∀ z ∈ S, 0 < z.2) {z : ℝ × ℝ} (hz : 0 < z.2) :
    lftAct A z ∈ lftAct A '' S ↔ z ∈ S := by
  refine ⟨fun ⟨w, hw, hwz⟩ ↦ ?_, fun h ↦ ⟨z, h, rfl⟩⟩
  have := congrArg (lftAct (Matrix.adjugate A)) hwz
  rw [cp_adj_lftAct hA (hS w hw), cp_adj_lftAct hA hz] at this
  exact this ▸ hw

private lemma cp_image_image (A : Mat2) {B : Mat2} (hB : 0 < B.det) {S : Set (ℝ × ℝ)}
    (hS : ∀ z ∈ S, 0 < z.2) : lftAct A '' (lftAct B '' S) = lftAct (A * B) '' S := by
  rw [image_image]
  exact image_congr fun z hz ↦ cp_lftAct_mul A hB.ne' (hS z hz)

private lemma cp_image_snd_pos {A : Mat2} (hA : 0 < A.det) {S : Set (ℝ × ℝ)}
    (hS : ∀ z ∈ S, 0 < z.2) : ∀ w ∈ lftAct A '' S, 0 < w.2 := by
  rintro _ ⟨z, hz, rfl⟩
  exact cp_lftAct_snd_pos hA (hS z hz)

/-! ### The rotation `R` -/

private lemma cp_sqrt3_sq : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

private lemma cp_sqrt3_pos : 0 < √3 := by positivity

private lemma cp_R_eq : R = !![1 / 2, -(√3 / 2); √3 / 2, 1 / 2] := rfl

private lemma cp_R_det : R.det = 1 := by
  rw [cp_R_eq, Matrix.det_fin_two_of]
  linear_combination cp_sqrt3_sq / 4

private lemma cp_R_sq : R ^ 2 = !![-(1 / 2), -(√3 / 2); √3 / 2, -(1 / 2)] := by
  rw [pow_two, cp_R_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linarith [cp_sqrt3_sq]

private lemma cp_R_cube : R * R ^ 2 = -1 := by
  rw [cp_R_sq, cp_R_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linarith [cp_sqrt3_sq]

private lemma cp_R_pos : 0 < R.det := by rw [cp_R_det]; norm_num

private lemma cp_R_sq_pos : 0 < (R ^ 2).det := by rw [Matrix.det_pow, cp_R_det]; norm_num

/-- The explicit form of `lftAct` for `A = [[a, b], [c, d]]`. -/
private lemma cp_lftAct_of (a b c d : ℝ) (z : ℝ × ℝ) :
    lftAct !![a, b; c, d] z =
      (((a * z.1 + b) * (c * z.1 + d) + a * c * z.2 ^ 2) / ((c * z.1 + d) ^ 2 + (c * z.2) ^ 2),
        (a * d - b * c) * z.2 / ((c * z.1 + d) ^ 2 + (c * z.2) ^ 2)) := by
  simp [lftAct, Matrix.det_fin_two]

/-- Reduction of the powers of `s = √3`. -/
private lemma cp_s_pows {s : ℝ} (hs : s ^ 2 = 3) :
    s ^ 3 = 3 * s ∧ s ^ 4 = 9 ∧ s ^ 5 = 9 * s ∧ s ^ 6 = 27 :=
  ⟨by linear_combination s * hs, by linear_combination (s ^ 2 + 3) * hs,
    by linear_combination s * (s ^ 2 + 3) * hs, by linear_combination (s ^ 4 + 3 * s ^ 2 + 9) * hs⟩

/-- `|R z|² - 2 Im(Rz)/(15√3) - 1/3 = 2(15(1/√3 - x) - y)/(15√3 |cz + d|²)`: the image of the
line `y = 15(1/√3 - x)` under `R` is the circle `x² + y² - 2y/(15√3) = 1/3`. -/
private lemma cp_R_edge_key {z : ℝ × ℝ} (hz : 0 < z.2) :
    (lftAct R z).1 ^ 2 + (lftAct R z).2 ^ 2 - 2 * (lftAct R z).2 / (15 * √3) - 1 / 3 =
      2 * (15 * (1 / √3 - z.1) - z.2) /
        (15 * √3 * ((√3 / 2 * z.1 + 1 / 2) ^ 2 + (√3 / 2 * z.2) ^ 2)) := by
  have hN := cp_N_pos cp_R_pos.ne' hz
  rw [cp_R_eq] at hN ⊢
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at hN
  rw [cp_lftAct_of]
  have hs := cp_sqrt3_sq
  have hs0 := cp_sqrt3_pos
  generalize √3 = s at *
  obtain ⟨h3, h4, h5, h6⟩ := cp_s_pows hs
  obtain ⟨x, y⟩ := z
  simp only at *
  have hN' := hN.ne'
  field_simp
  ring_nf
  simp only [hs, h3, h4, h5, h6]
  ring_nf

/-- `R² z = (w₁, w₂)` with `w₂ - 15(w₁ + 1/√3) = (y - 15(1/√3 - x))/|cz + d|²`: the image of the
line `y = 15(1/√3 - x)` under `R²` is the line `y = 15(x + 1/√3)`. -/
private lemma cp_R_sq_edge_key {z : ℝ × ℝ} (hz : 0 < z.2) :
    (lftAct (R ^ 2) z).2 - 15 * ((lftAct (R ^ 2) z).1 + 1 / √3) =
      (z.2 - 15 * (1 / √3 - z.1)) / ((√3 / 2 * z.1 + -(1 / 2)) ^ 2 + (√3 / 2 * z.2) ^ 2) := by
  have hN : 0 < (√3 / 2 * z.1 + -(1 / 2)) ^ 2 + (√3 / 2 * z.2) ^ 2 := by
    have : 0 < (√3 / 2 * z.2) ^ 2 := by have := cp_sqrt3_pos; positivity
    positivity
  rw [cp_R_sq, cp_lftAct_of]
  have hs := cp_sqrt3_sq
  have hs0 := cp_sqrt3_pos
  generalize √3 = s at *
  obtain ⟨h3, -, -, -⟩ := cp_s_pows hs
  obtain ⟨x, y⟩ := z
  simp only at *
  have hN' := hN.ne'
  field_simp
  ring_nf
  simp only [hs, h3]
  ring_nf

/-- The rotation `R` and the medians `x = 0`, `(x ∓ 1/√3)² + y² = 4/3` of `𝔥*`: with
`f_±(z) = (x ± 1/√3)² + y² - 4/3` and `N = |cz + d|²`, `Re(Rz) = √3 f₋(z)/(4N)`,
`f₊(Rz) = -4x/(√3 N)` and `f₋(Rz) = -f₊(z)/N`. -/
private lemma cp_R_median_key {z : ℝ × ℝ} (hz : 0 < z.2) :
    (lftAct R z).1 = √3 * ((z.1 - 1 / √3) ^ 2 + z.2 ^ 2 - 4 / 3) /
        (4 * ((√3 / 2 * z.1 + 1 / 2) ^ 2 + (√3 / 2 * z.2) ^ 2)) ∧
      ((lftAct R z).1 + 1 / √3) ^ 2 + (lftAct R z).2 ^ 2 - 4 / 3 =
        -4 * z.1 / (√3 * ((√3 / 2 * z.1 + 1 / 2) ^ 2 + (√3 / 2 * z.2) ^ 2)) ∧
      ((lftAct R z).1 - 1 / √3) ^ 2 + (lftAct R z).2 ^ 2 - 4 / 3 =
        -((z.1 + 1 / √3) ^ 2 + z.2 ^ 2 - 4 / 3) /
          ((√3 / 2 * z.1 + 1 / 2) ^ 2 + (√3 / 2 * z.2) ^ 2) := by
  have hN : 0 < (√3 / 2 * z.1 + 1 / 2) ^ 2 + (√3 / 2 * z.2) ^ 2 := by
    have : 0 < (√3 / 2 * z.2) ^ 2 := by have := cp_sqrt3_pos; positivity
    positivity
  rw [cp_R_eq, cp_lftAct_of]
  have hs := cp_sqrt3_sq
  have hs0 := cp_sqrt3_pos
  generalize √3 = s at *
  obtain ⟨h3, h4, h5, h6⟩ := cp_s_pows hs
  obtain ⟨x, y⟩ := z
  simp only at *
  have hN' := hN.ne'
  refine ⟨?_, ?_, ?_⟩ <;>
  · field_simp
    ring_nf
    simp only [hs, h3, h4, h5, h6]
    ring_nf

/-- `1/√3 ∈ (0.57, 0.58)` and `(1/√3)² = 1/3`. -/
private lemma cp_u_facts : (1 / √3) ^ 2 = 1 / 3 ∧ 57 / 100 < 1 / √3 ∧ 1 / √3 < 58 / 100 := by
  have hs := cp_sqrt3_sq
  have hs0 := cp_sqrt3_pos
  refine ⟨by rw [div_pow, hs]; norm_num, ?_, ?_⟩
  · rw [lt_div_iff₀ hs0]; nlinarith
  · rw [div_lt_iff₀ hs0]; nlinarith

private lemma cp_lftAct_one (z : ℝ × ℝ) : lftAct 1 z = z := by
  simpa using cp_lftAct_smul_one (one_ne_zero (α := ℝ)) z

/-- Remark 4.2.2 in coordinates: for `det A = 1` and `y > 0`, `Φ(A · z) = A Φ(z) A⁻¹`. -/
theorem Φ_lftAct (A : Mat2) (hA : A.det = 1) {z : ℝ × ℝ} (hz : 0 < z.2) :
    Φ (lftAct A z).1 (lftAct A z).2 = A * Φ z.1 z.2 * A⁻¹ := by
  let g : Matrix.SpecialLinearGroup (Fin 2) ℝ := ⟨A, hA⟩
  let w : UpperHalfPlane := ⟨cp_toC z, hz⟩
  have h := ΦH_smul g w
  have hgw : ((g • w : UpperHalfPlane) : ℂ) = cp_mob A (cp_toC z) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    rfl
  have hre : (g • w).re = (lftAct A z).1 := by
    rw [cp_lftAct_eq, ← UpperHalfPlane.coe_re, hgw]
  have him : (g • w).im = (lftAct A z).2 := by
    rw [cp_lftAct_eq, ← UpperHalfPlane.coe_im, hgw]
  have hinv : ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Mat2) = A⁻¹ := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.inv_def, hA, Ring.inverse_one, one_smul]
  simp only [ΦH, hre, him, hinv] at h
  exact h

/-- **Images of horoballs** (TeX 3904–3915). For `A = [[a, b], [c, d]]` with `det A > 0` and
`c ≠ 0`, the linear fractional transformation `A` maps the open horoball `{y > y₀}`, `y₀ > 0`, onto
the open disk tangent to the real axis at `A · ∞ = a/c`, with center `a/c + ir` and radius
`r = det A/(2y₀c²)`. (The book states it for the horocycle `y = y₀` and its image circle.) -/
theorem lftAct_image_horoball (A : Mat2) (hA : 0 < A.det) (hc : A 1 0 ≠ 0) {y₀ : ℝ}
    (hy₀ : 0 < y₀) :
    lftAct A '' {z | y₀ < z.2} =
      {w | (w.1 - A 0 0 / A 1 0) ^ 2 + (w.2 - A.det / (2 * y₀ * A 1 0 ^ 2)) ^ 2 <
        (A.det / (2 * y₀ * A 1 0 ^ 2)) ^ 2} := by
  have hr : 0 < A.det / (2 * y₀ * A 1 0 ^ 2) := by positivity
  refine cp_image_eq hA (fun w hw ↦ ?_) (fun z hz ↦ ?_) (fun z hz ↦ hy₀.trans hz)
  · simp only [mem_ofPred_eq] at hw
    by_contra hw2
    push Not at hw2
    nlinarith [sq_nonneg (w.1 - A 0 0 / A 1 0)]
  · simp only [mem_ofPred_eq]
    have hN := cp_N_pos hA.ne' hz
    have hf : 0 < A.det ^ 2 /
        (A 1 0 ^ 2 * ((A 1 0 * z.1 + A 1 1) ^ 2 + (A 1 0 * z.2) ^ 2) * y₀) := by
      have : A.det ^ 2 > 0 := by positivity
      positivity
    have key : ((lftAct A z).1 - A 0 0 / A 1 0) ^ 2 +
          ((lftAct A z).2 - A.det / (2 * y₀ * A 1 0 ^ 2)) ^ 2 -
          (A.det / (2 * y₀ * A 1 0 ^ 2)) ^ 2 =
        A.det ^ 2 / (A 1 0 ^ 2 * ((A 1 0 * z.1 + A 1 1) ^ 2 + (A 1 0 * z.2) ^ 2) * y₀) *
          (y₀ - z.2) := by
      have hN' := hN.ne'
      have hy₀' := hy₀.ne'
      simp only [lftAct, Matrix.det_fin_two]
      field_simp
      ring
    have hiff : ((lftAct A z).1 - A 0 0 / A 1 0) ^ 2 +
          ((lftAct A z).2 - A.det / (2 * y₀ * A 1 0 ^ 2)) ^ 2 <
          (A.det / (2 * y₀ * A 1 0 ^ 2)) ^ 2 ↔ y₀ < z.2 := by
      rw [← sub_neg, key]
      constructor
      · intro h; by_contra h'; push Not at h'; nlinarith
      · intro h; exact mul_neg_of_pos_of_neg hf (by linarith)
    exact hiff.symm

/-- `B(1/√3) = R B(i∞)` is the open disk of radius `4/27` tangent to the real axis at `1/√3`
(Definition 5.0.1, TeX 3922–3925). -/
theorem lftAct_R_horoballAtInfty :
    lftAct R '' horoballAtInfty =
      {w | (w.1 - 1 / √3) ^ 2 + (w.2 - 4 / 27) ^ 2 < (4 / 27) ^ 2} := by
  have h := lftAct_image_horoball R cp_R_pos (by rw [cp_R_eq]; simp) (y₀ := 9 / 2) (by norm_num)
  have e1 : R 0 0 / R 1 0 = 1 / √3 := by
    rw [cp_R_eq]; simp; field_simp
  have e2 : R.det / (2 * (9 / 2) * R 1 0 ^ 2) = 4 / 27 := by
    rw [cp_R_det, cp_R_eq]
    simp only [one_div, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_fin_one, Matrix.cons_val_one, mul_inv_rev, inv_div]
    rw [div_pow, cp_sqrt3_sq]; norm_num
  rw [e1, e2] at h
  exact h

/-- `B(-1/√3) = R² B(i∞)` is the open disk of radius `4/27` tangent to the real axis at `-1/√3`
(Definition 5.0.1, TeX 3922–3925). -/
theorem lftAct_R_sq_horoballAtInfty :
    lftAct (R ^ 2) '' horoballAtInfty =
      {w | (w.1 + 1 / √3) ^ 2 + (w.2 - 4 / 27) ^ 2 < (4 / 27) ^ 2} := by
  have h := lftAct_image_horoball (R ^ 2) cp_R_sq_pos (by rw [cp_R_sq]; simp) (y₀ := 9 / 2)
    (by norm_num)
  have e1 : (R ^ 2) 0 0 / (R ^ 2) 1 0 = -(1 / √3) := by
    rw [cp_R_sq]; simp; field_simp
  have e2 : (R ^ 2).det / (2 * (9 / 2) * (R ^ 2) 1 0 ^ 2) = 4 / 27 := by
    rw [Matrix.det_pow, cp_R_det, cp_R_sq]
    simp only [one_pow, one_div, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, mul_inv_rev, inv_div]
    rw [div_pow, cp_sqrt3_sq]; norm_num
  rw [e1, e2] at h
  simp only [sub_neg_eq_add] at h
  exact h

/-- `Π₁⁺ = R Π₀⁺` is the part of the upper half-plane inside the circle
`x² + y² - 2y/(15√3) = 1/3` through `±1/√3`, a neighbourhood of the lower edge
`x² + y² = 1/3` of `𝔥*` (Definition 5.0.1). -/
theorem lftAct_R_edgeHalfPlane :
    lftAct R '' edgeHalfPlane =
      {w | 0 < w.2 ∧ w.1 ^ 2 + w.2 ^ 2 - 2 * w.2 / (15 * √3) < 1 / 3} := by
  refine cp_image_eq cp_R_pos (fun w hw ↦ hw.1) (fun z hz ↦ ?_) (fun z hz ↦ hz.1)
  have key := cp_R_edge_key hz
  have hpos : 0 < 15 * √3 * ((√3 / 2 * z.1 + 1 / 2) ^ 2 + (√3 / 2 * z.2) ^ 2) := by
    have := cp_sqrt3_pos
    have : 0 < (√3 / 2 * z.2) ^ 2 := by positivity
    positivity
  simp only [edgeHalfPlane, mem_ofPred_eq]
  have hiff : (lftAct R z).1 ^ 2 + (lftAct R z).2 ^ 2 - 2 * (lftAct R z).2 / (15 * √3) < 1 / 3 ↔
      15 * (1 / √3 - z.1) < z.2 := by
    rw [← sub_neg, key, div_lt_iff₀ hpos, zero_mul]
    constructor <;> intro h <;> linarith
  rw [hiff]
  constructor
  · rintro ⟨-, h⟩; exact ⟨cp_lftAct_snd_pos cp_R_pos hz, by linarith⟩
  · rintro ⟨-, h⟩; exact ⟨hz, by linarith⟩

/-- `Π₂⁺ = R² Π₀⁺` is the half-plane `{y > 15(x + 1/√3)}`, the mirror image of `Π₀⁺`
(Definition 5.0.1). -/
theorem lftAct_R_sq_edgeHalfPlane :
    lftAct (R ^ 2) '' edgeHalfPlane = {w | 0 < w.2 ∧ 15 * (w.1 + 1 / √3) < w.2} := by
  refine cp_image_eq cp_R_sq_pos (fun w hw ↦ hw.1) (fun z hz ↦ ?_) (fun z hz ↦ hz.1)
  have key := cp_R_sq_edge_key hz
  have hpos : 0 < (√3 / 2 * z.1 + -(1 / 2)) ^ 2 + (√3 / 2 * z.2) ^ 2 := by
    have := cp_sqrt3_pos
    have : 0 < (√3 / 2 * z.2) ^ 2 := by positivity
    positivity
  simp only [edgeHalfPlane, mem_ofPred_eq]
  have hiff : 15 * ((lftAct (R ^ 2) z).1 + 1 / √3) < (lftAct (R ^ 2) z).2 ↔
      15 * (1 / √3 - z.1) < z.2 := by
    rw [← sub_pos, key, lt_div_iff₀ hpos, zero_mul, sub_pos]
  rw [hiff]
  constructor
  · rintro ⟨-, h⟩; exact ⟨cp_lftAct_snd_pos cp_R_sq_pos hz, by linarith⟩
  · rintro ⟨-, h⟩; exact ⟨hz, by linarith⟩

/-- `𝔥**` by explicit inequalities: the points of `𝔥*` with `y ≤ 4.5`, outside the two disks of
radius `4/27` tangent to the real axis at `±1/√3`, with `y ≤ 15(1/√3 - |x|)`, and outside the
circle `x² + y² - 2y/(15√3) = 1/3`. -/
theorem truncatedStarDomain_eq :
    truncatedStarDomain =
      {z | z ∈ starDomain ∧ z.2 ≤ 9 / 2 ∧
        (4 / 27) ^ 2 ≤ (z.1 - 1 / √3) ^ 2 + (z.2 - 4 / 27) ^ 2 ∧
        (4 / 27) ^ 2 ≤ (z.1 + 1 / √3) ^ 2 + (z.2 - 4 / 27) ^ 2 ∧
        z.2 ≤ 15 * (1 / √3 - z.1) ∧ 1 / 3 ≤ z.1 ^ 2 + z.2 ^ 2 - 2 * z.2 / (15 * √3) ∧
        z.2 ≤ 15 * (z.1 + 1 / √3)} := by
  ext z
  rw [truncatedStarDomain, lftAct_R_horoballAtInfty, lftAct_R_sq_horoballAtInfty,
    lftAct_R_edgeHalfPlane, lftAct_R_sq_edgeHalfPlane]
  simp only [horoballAtInfty, edgeHalfPlane, mem_sdiff, mem_union, mem_ofPred_eq, not_or, not_lt,
    not_and]
  constructor
  · rintro ⟨hz, ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
    exact ⟨hz, h1, h2, h3, h4 hz.1, h5 hz.1, h6 hz.1⟩
  · rintro ⟨hz, h1, h2, h3, h4, h5, h6⟩
    exact ⟨hz, ⟨⟨⟨⟨h1, h2⟩, h3⟩, fun _ ↦ h4⟩, fun _ ↦ h5⟩, fun _ ↦ h6⟩

/-- **`𝔥**` is compact** (`def:compactification:compact`, label of this formalization;
Definition 5.0.1, asserted without proof at TeX 3975). -/
theorem isCompact_truncatedStarDomain : IsCompact truncatedStarDomain := by
  obtain ⟨hu2, hu1, hu3⟩ := cp_u_facts
  set C : Set (ℝ × ℝ) := {z | 3 / 20 ≤ z.2 ∧ z.2 ≤ 9 / 2 ∧
    (4 / 27) ^ 2 ≤ (z.1 - 1 / √3) ^ 2 + (z.2 - 4 / 27) ^ 2 ∧
    (4 / 27) ^ 2 ≤ (z.1 + 1 / √3) ^ 2 + (z.2 - 4 / 27) ^ 2 ∧
    z.2 ≤ 15 * (1 / √3 - z.1) ∧ 1 / 3 ≤ z.1 ^ 2 + z.2 ^ 2 - 2 * z.2 / (15 * √3) ∧
    z.2 ≤ 15 * (z.1 + 1 / √3)} with hCdef
  have hC : truncatedStarDomain = C := by
    rw [truncatedStarDomain_eq]
    ext z
    simp only [hCdef, mem_ofPred_eq, starDomain]
    have e : 2 * z.2 / (15 * √3) = 2 * z.2 * (1 / √3) / 15 := by ring
    rw [e]
    constructor
    · rintro ⟨⟨hy, -, -, -⟩, h1, h2, h3, h4, h5, h6⟩
      refine ⟨?_, h1, h2, h3, h4, h5, h6⟩
      -- the lower bound `y ≥ (4/(15√3))(225/226) > 0.15`: `|x| ≤ 1/√3 - y/15` and the circle
      -- `x² + y² - 2y/(15√3) ≥ 1/3` give `4y/(15√3) ≤ (226/225) y²`
      have hx : z.1 ^ 2 ≤ (1 / √3 - z.2 / 15) ^ 2 := by
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / √3 - z.2 / 15 - z.1)
          (by linarith : (0 : ℝ) ≤ 1 / √3 - z.2 / 15 + z.1)]
      have h7 : z.2 * (4 * (1 / √3) / 15) ≤ z.2 * (226 * z.2 / 225) := by
        nlinarith
      have h8 := le_of_mul_le_mul_left h7 hy
      linarith
    · rintro ⟨hy, h1, h2, h3, h4, h5, h6⟩
      have hy0 : 0 < z.2 := by linarith
      have : 0 < 2 * z.2 * (1 / √3) / 15 := by positivity
      exact ⟨⟨hy0, by linarith, by linarith, by linarith⟩, h1, h2, h3, h4, h5, h6⟩
  rw [hC]
  refine IsCompact.of_isClosed_subset
    ((isCompact_Icc (a := (-1 : ℝ)) (b := 1)).prod (isCompact_Icc (a := (0 : ℝ)) (b := 5)))
    ?_ ?_
  · simp only [hCdef, ofPred_and]
    refine (isClosed_le ?_ ?_).inter ((isClosed_le ?_ ?_).inter ((isClosed_le ?_ ?_).inter
      ((isClosed_le ?_ ?_).inter ((isClosed_le ?_ ?_).inter ((isClosed_le ?_ ?_).inter
      (isClosed_le ?_ ?_)))))) <;> fun_prop
  · rintro z ⟨hy, h1, -, -, h4, -, h6⟩
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- Conjugation by `R` preserves the star states: it preserves the trace and the determinant and
permutes the star functions (`ρ_R_conj`, §4.6). -/
private lemma cp_isStarState_R_conj (X : Mat2) : IsStarState (R * X * R⁻¹) ↔ IsStarState X := by
  have hRu : IsUnit R.det := by rw [cp_R_det]; exact isUnit_one
  have htr : (R * X * R⁻¹).trace = X.trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hRu, Matrix.one_mul]
  have hdet : (R * X * R⁻¹).det = X.det := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, cp_R_det, Ring.inverse_one]
    ring
  unfold IsStarState
  rw [htr, hdet]
  constructor
  · rintro ⟨h0, h1, h2, h3, h4⟩
    obtain ⟨e0, e1, e2⟩ := ρ_R_conj X h0
    rw [e0] at h2; rw [e1] at h3; rw [e2] at h4
    exact ⟨h0, h1, h3, h4, h2⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩
    obtain ⟨e0, e1, e2⟩ := ρ_R_conj X h0
    rw [e0, e1, e2]
    exact ⟨h0, h1, h4, h2, h3⟩

/-- §4.6 pointwise: `Rz ∈ 𝔥* ↔ z ∈ 𝔥*`, by Theorem 4.4.1, Remark 4.2.2 and `ρ_R_conj`. -/
private lemma cp_R_mem_starDomain_iff {z : ℝ × ℝ} (hz : 0 < z.2) :
    lftAct R z ∈ starDomain ↔ z ∈ starDomain := by
  have h1 := cp_lftAct_snd_pos cp_R_pos hz
  have e1 := theorem4_4_1 (lftAct R z).1 (lftAct R z).2 h1
  have e2 := theorem4_4_1 z.1 z.2 hz
  rw [Prod.mk.eta] at e1 e2
  rw [← e1, ← e2, Φ_lftAct R cp_R_det hz, cp_isStarState_R_conj]

private lemma cp_reflAct_reflAct (z : ℝ × ℝ) : reflAct (reflAct z) = z := by
  simp [reflAct]

/-- `X ↦ -S X S⁻¹` preserves the star states: it preserves the determinant, negates the trace
and permutes the star functions (`ρ_reflS_conj`, §4.6). -/
private lemma cp_isStarState_reflS_conj (X : Mat2) :
    IsStarState (-(reflS * X * reflS⁻¹)) ↔ IsStarState X := by
  have hSdet : reflS.det = -1 := by simp [reflS, Matrix.det_fin_two]
  have hSu : IsUnit reflS.det := by rw [hSdet]; exact isUnit_one.neg
  have htr : (-(reflS * X * reflS⁻¹)).trace = -X.trace := by
    rw [Matrix.trace_neg, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hSu,
      Matrix.one_mul]
  have hdet : (-(reflS * X * reflS⁻¹)).det = X.det := by
    rw [Matrix.det_neg, Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, hSdet,
      Fintype.card_fin, Ring.inverse_eq_inv]
    ring
  unfold IsStarState
  rw [htr, hdet, neg_eq_zero]
  constructor
  · rintro ⟨h0, h1, h2, h3, h4⟩
    obtain ⟨e0, e1, e2⟩ := ρ_reflS_conj X h0
    rw [e0] at h2; rw [e1] at h3; rw [e2] at h4
    exact ⟨h0, h1, h3, h2, h4⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩
    obtain ⟨e0, e1, e2⟩ := ρ_reflS_conj X h0
    rw [e0, e1, e2]
    exact ⟨h0, h1, h3, h2, h4⟩

/-- §4.6 pointwise: `-z̄ ∈ 𝔥* ↔ z ∈ 𝔥*`, by Theorem 4.4.1, `reflS_conj_Φ` and `ρ_reflS_conj`. -/
private lemma cp_refl_mem_starDomain_iff (z : ℝ × ℝ) :
    reflAct z ∈ starDomain ↔ z ∈ starDomain := by
  by_cases hz : 0 < z.2
  · have e1 := theorem4_4_1 (-z.1) z.2 hz
    have e2 := theorem4_4_1 z.1 z.2 hz
    rw [Prod.mk.eta] at e2
    rw [show reflAct z = (-z.1, z.2) from rfl, ← e1, ← e2, ← reflS_conj_Φ,
      cp_isStarState_reflS_conj]
  · exact iff_of_false (fun h ↦ hz h.1) (fun h ↦ hz h.1)

private lemma cp_image_reflAct {S : Set (ℝ × ℝ)} (h : ∀ z, reflAct z ∈ S ↔ z ∈ S) :
    reflAct '' S = S := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (h w).2 hw
  · intro hz
    refine ⟨reflAct z, (h (reflAct z)).1 ?_, cp_reflAct_reflAct z⟩
    rwa [cp_reflAct_reflAct]

/-- `R` permutes `S, R S, R² S` (for `S` in the upper half-plane), since `R³ = -I` acts
trivially. -/
private lemma cp_R_mem_orbit {S : Set (ℝ × ℝ)} (hS : ∀ z ∈ S, 0 < z.2) {z : ℝ × ℝ}
    (hz : 0 < z.2) :
    (lftAct R z ∈ S ↔ z ∈ lftAct (R ^ 2) '' S) ∧
      (lftAct R z ∈ lftAct R '' S ↔ z ∈ S) ∧
      (lftAct R z ∈ lftAct (R ^ 2) '' S ↔ z ∈ lftAct R '' S) := by
  have hRS := cp_image_snd_pos cp_R_pos hS
  have hR2S := cp_image_snd_pos cp_R_sq_pos hS
  refine ⟨?_, cp_mem_image_iff cp_R_pos hS hz, ?_⟩
  · have h3 : lftAct R '' (lftAct (R ^ 2) '' S) = S := by
      rw [cp_image_image R cp_R_sq_pos hS, cp_R_cube,
        show lftAct (-1) = id from funext cp_lftAct_negOne, image_id]
    have := cp_mem_image_iff cp_R_pos hR2S hz
    rwa [h3] at this
  · rw [show lftAct (R ^ 2) '' S = lftAct R '' (lftAct R '' S) by
      rw [cp_image_image R cp_R_pos hS, pow_two]]
    exact cp_mem_image_iff cp_R_pos hRS hz

/-- The permutation of the six removed sets by `R`, as a propositional identity. -/
private lemma cp_perm_iff {a b c d e f g : Prop} :
    (g ∧ ¬(((((c ∨ a) ∨ b) ∨ f) ∨ d) ∨ e)) ↔ (g ∧ ¬(((((a ∨ b) ∨ c) ∨ d) ∨ e) ∨ f)) := by
  tauto

/-- `Rz ∈ 𝔥** ↔ z ∈ 𝔥**` on the upper half-plane: `R` preserves `𝔥*` and permutes the three
horoballs and the three half-planes. -/
private lemma cp_R_mem_truncated_iff {z : ℝ × ℝ} (hz : 0 < z.2) :
    lftAct R z ∈ truncatedStarDomain ↔ z ∈ truncatedStarDomain := by
  have hH : ∀ z ∈ horoballAtInfty, 0 < z.2 := fun z hz ↦ by
    have : 9 / 2 < z.2 := hz
    linarith
  have hE : ∀ z ∈ edgeHalfPlane, 0 < z.2 := fun z hz ↦ hz.1
  obtain ⟨a1, a2, a3⟩ := cp_R_mem_orbit hH hz
  obtain ⟨b1, b2, b3⟩ := cp_R_mem_orbit hE hz
  unfold truncatedStarDomain
  rw [mem_sdiff, mem_sdiff, cp_R_mem_starDomain_iff hz]
  simp only [mem_union, a1, a2, a3, b1, b2, b3]
  exact cp_perm_iff

/-- `z ↦ -z̄` preserves `𝔥**`: it fixes `B(i∞)` and `Π₁⁺` and exchanges `B(1/√3) ↔ B(-1/√3)`,
`Π₀⁺ ↔ Π₂⁺` (explicit forms). -/
private lemma cp_refl_mem_truncated_iff (z : ℝ × ℝ) :
    reflAct z ∈ truncatedStarDomain ↔ z ∈ truncatedStarDomain := by
  rw [truncatedStarDomain_eq]
  simp only [mem_ofPred_eq, cp_refl_mem_starDomain_iff]
  simp only [reflAct, neg_sq]
  have e1 : (-z.1 - 1 / √3) ^ 2 = (z.1 + 1 / √3) ^ 2 := by ring
  have e2 : (-z.1 + 1 / √3) ^ 2 = (z.1 - 1 / √3) ^ 2 := by ring
  have e3 : 15 * (1 / √3 - -z.1) = 15 * (z.1 + 1 / √3) := by ring
  have e4 : 15 * (-z.1 + 1 / √3) = 15 * (1 / √3 - z.1) := by ring
  rw [e1, e2, e3, e4]
  tauto

/-- §4.6: the rotation `R` maps the star domain onto itself (TeX 3779, "the dihedral group acts
on the star domain"). -/
theorem image_lftAct_R_starDomain : lftAct R '' starDomain = starDomain := by
  exact cp_image_eq cp_R_pos (fun w hw ↦ hw.1) (fun z hz ↦ (cp_R_mem_starDomain_iff hz).symm)
    (fun z hz ↦ hz.1)

/-- §4.6: the reflection `z ↦ -z̄` maps the star domain onto itself. -/
theorem image_reflAct_starDomain : reflAct '' starDomain = starDomain := by
  exact cp_image_reflAct cp_refl_mem_starDomain_iff

/-- **`𝔥**` is invariant under the rotation `R`** (TeX 3976–3977: "the shape of the
compactification has been chosen to be invariant under the action of the dihedral group"). -/
theorem image_lftAct_R_truncatedStarDomain :
    lftAct R '' truncatedStarDomain = truncatedStarDomain := by
  exact cp_image_eq cp_R_pos (fun w hw ↦ hw.1.1)
    (fun z hz ↦ (cp_R_mem_truncated_iff hz).symm) (fun z hz ↦ hz.1.1)

/-- **`𝔥**` is invariant under the reflection `z ↦ -z̄`** (TeX 3976–3977). -/
theorem image_reflAct_truncatedStarDomain :
    reflAct '' truncatedStarDomain = truncatedStarDomain := by
  exact cp_image_reflAct cp_refl_mem_truncated_iff

/-- The dihedral group preserves `𝔥*` and `𝔥**`: for every element `S^b R^n`, `z ∈ 𝔥*` iff its
image is, and `z ∈ 𝔥**` iff its image is. -/
theorem dihedralAct_mem_iff (n : ℕ) (b : Bool) {z : ℝ × ℝ} (hz : 0 < z.2) :
    (dihedralAct n b z ∈ starDomain ↔ z ∈ starDomain) ∧
      (dihedralAct n b z ∈ truncatedStarDomain ↔ z ∈ truncatedStarDomain) := by
  have hn : ∀ n : ℕ, 0 < (lftAct (R ^ n) z).2 ∧
      (lftAct (R ^ n) z ∈ starDomain ↔ z ∈ starDomain) ∧
      (lftAct (R ^ n) z ∈ truncatedStarDomain ↔ z ∈ truncatedStarDomain) := by
    intro n
    induction n with
    | zero => rw [pow_zero, cp_lftAct_one]; exact ⟨hz, Iff.rfl, Iff.rfl⟩
    | succ n ih =>
      have hdet : (R ^ n).det ≠ 0 := by rw [Matrix.det_pow, cp_R_det, one_pow]; exact one_ne_zero
      rw [pow_succ', ← cp_lftAct_mul R hdet hz]
      exact ⟨cp_lftAct_snd_pos cp_R_pos ih.1, (cp_R_mem_starDomain_iff ih.1).trans ih.2.1,
        (cp_R_mem_truncated_iff ih.1).trans ih.2.2⟩
  cases b
  · simpa [dihedralAct] using (hn n).2
  · simpa [dihedralAct, cp_refl_mem_starDomain_iff, cp_refl_mem_truncated_iff] using (hn n).2

/-- **A fundamental domain of the dihedral action on `𝔥*`** (§4.6, TeX 3794–3809; proof of
Theorem 5.0.2, TeX 4475–4479): every point of `𝔥*` is mapped into `fundamentalDomain` by an element
`S^b R^n` of the dihedral group. -/
theorem exists_dihedralAct_mem_fundamentalDomain {z : ℝ × ℝ} (hz : z ∈ starDomain) :
    ∃ n : Fin 3, ∃ b : Bool, dihedralAct n b z ∈ fundamentalDomain := by
  obtain ⟨hu2, hu1, hu3⟩ := cp_u_facts
  have hs0 := cp_sqrt3_pos
  have hy := hz.1
  -- some `Rⁿ z` lies outside both medians `(x ∓ 1/√3)² + y² = 4/3`
  obtain ⟨n, hw⟩ : ∃ n : Fin 3,
      0 ≤ ((lftAct (R ^ (n : ℕ)) z).1 + 1 / √3) ^ 2 + (lftAct (R ^ (n : ℕ)) z).2 ^ 2 - 4 / 3 ∧
      0 ≤ ((lftAct (R ^ (n : ℕ)) z).1 - 1 / √3) ^ 2 + (lftAct (R ^ (n : ℕ)) z).2 ^ 2 - 4 / 3 := by
    by_cases h0 : 0 ≤ (z.1 + 1 / √3) ^ 2 + z.2 ^ 2 - 4 / 3 ∧
        0 ≤ (z.1 - 1 / √3) ^ 2 + z.2 ^ 2 - 4 / 3
    · exact ⟨⟨0, by norm_num⟩, by simpa [cp_lftAct_one] using h0⟩
    obtain ⟨k1, k2, k3⟩ := cp_R_median_key hy
    have hN : 0 < (√3 / 2 * z.1 + 1 / 2) ^ 2 + (√3 / 2 * z.2) ^ 2 := by
      have : 0 < (√3 / 2 * z.2) ^ 2 := by positivity
      positivity
    by_cases hx : z.1 < 0
    · -- `f₊(z) < 0`: then `R z` works
      have hp : (z.1 + 1 / √3) ^ 2 + z.2 ^ 2 - 4 / 3 < 0 := by
        by_contra hp
        push Not at hp
        refine h0 ⟨hp, ?_⟩
        nlinarith
      refine ⟨⟨1, by norm_num⟩, ?_⟩
      change 0 ≤ ((lftAct (R ^ 1) z).1 + 1 / √3) ^ 2 + (lftAct (R ^ 1) z).2 ^ 2 - 4 / 3 ∧
        0 ≤ ((lftAct (R ^ 1) z).1 - 1 / √3) ^ 2 + (lftAct (R ^ 1) z).2 ^ 2 - 4 / 3
      rw [pow_one, k2, k3]
      constructor
      · apply div_nonneg <;> nlinarith
      · apply div_nonneg <;> linarith
    · -- `f₋(z) < 0`: then `R² z` works
      push Not at hx
      have hm : (z.1 - 1 / √3) ^ 2 + z.2 ^ 2 - 4 / 3 < 0 := by
        by_contra hm
        push Not at hm
        refine h0 ⟨?_, hm⟩
        nlinarith
      have hRz := cp_lftAct_snd_pos cp_R_pos hy
      obtain ⟨-, l2, l3⟩ := cp_R_median_key hRz
      have hN' : 0 < (√3 / 2 * (lftAct R z).1 + 1 / 2) ^ 2 + (√3 / 2 * (lftAct R z).2) ^ 2 := by
        have : 0 < (√3 / 2 * (lftAct R z).2) ^ 2 := by positivity
        positivity
      have hRz1 : (lftAct R z).1 < 0 := by
        rw [k1]
        apply div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hs0 hm)
        positivity
      refine ⟨⟨2, by norm_num⟩, ?_⟩
      change 0 ≤ ((lftAct (R ^ 2) z).1 + 1 / √3) ^ 2 + (lftAct (R ^ 2) z).2 ^ 2 - 4 / 3 ∧
        0 ≤ ((lftAct (R ^ 2) z).1 - 1 / √3) ^ 2 + (lftAct (R ^ 2) z).2 ^ 2 - 4 / 3
      rw [pow_two R, ← cp_lftAct_mul R cp_R_pos.ne' hy, l2, l3, k2]
      constructor
      · apply div_nonneg <;> nlinarith
      · apply div_nonneg _ hN'.le
        rw [neg_nonneg]
        exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  -- then `w` or its mirror image lies in the fundamental domain
  have hwS : lftAct (R ^ (n : ℕ)) z ∈ starDomain :=
    (dihedralAct_mem_iff n false hy).1.2 hz
  by_cases hx : 0 ≤ (lftAct (R ^ (n : ℕ)) z).1
  · refine ⟨n, false, ?_⟩
    simp only [dihedralAct, Bool.false_eq_true, ite_false]
    exact ⟨hwS, hx, by linarith [hw.2]⟩
  · refine ⟨n, true, ?_⟩
    simp only [dihedralAct, ite_true]
    refine ⟨(cp_refl_mem_starDomain_iff _).2 hwS, ?_, ?_⟩
    · simp only [reflAct]; linarith
    · simp only [reflAct]
      have : (-(lftAct (R ^ (n : ℕ)) z).1 - 1 / √3) ^ 2 =
          ((lftAct (R ^ (n : ℕ)) z).1 + 1 / √3) ^ 2 := by ring
      rw [this]; linarith [hw.1]

/-- The sets of Definition 5.0.1 that meet the fundamental domain (proof of Theorem 5.0.2,
TeX 4480–4484 and 4500–4501): the fundamental domain lies in `{x ≥ 0, y ≥ 1}`, and a point of it
outside `𝔥**` lies in `B(i∞)` or in `Π₀⁺ ∩ {y ≤ 4.5}`. (The book says that only `B(i∞)` and `Π₀⁺`
meet `{x ≥ 0, y ≥ 1}`; `Π₂⁺` meets it too, but only inside `B(i∞)`.) -/
theorem mem_horoball_or_edgeHalfPlane_of_mem_fundamentalDomain {z : ℝ × ℝ}
    (hz : z ∈ fundamentalDomain) :
    0 ≤ z.1 ∧ 1 ≤ z.2 ∧
      (z ∉ truncatedStarDomain → z ∈ horoballAtInfty ∨ (z ∈ edgeHalfPlane ∧ z.2 ≤ 9 / 2)) := by
  obtain ⟨hu2, hu1, hu3⟩ := cp_u_facts
  obtain ⟨⟨hy, hx1, hx2, hr⟩, hx, hfd⟩ := hz
  have hy1 : 1 ≤ z.2 := by nlinarith
  refine ⟨hx, hy1, fun hn ↦ ?_⟩
  by_cases h45 : 9 / 2 < z.2
  · exact Or.inl h45
  · right
    push Not at h45
    refine ⟨⟨hy, ?_⟩, h45⟩
    by_contra hE
    push Not at hE
    apply hn
    rw [truncatedStarDomain_eq]
    have e : 2 * z.2 / (15 * √3) = 2 * z.2 * (1 / √3) / 15 := by ring
    refine ⟨⟨hy, hx1, hx2, hr⟩, h45, ?_, ?_, hE, ?_, ?_⟩
    · nlinarith
    · nlinarith
    · rw [e]; nlinarith
    · nlinarith

end SmoothedPolygons
