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

## Proofs (to be written)

* `Φ_lftAct`: `ΦH_smul` (Remark 4.2.2) for `A ∈ SL₂(ℝ)`, with the coordinates of `g • z` from
  `UpperHalfPlane.smul_re_im_mul_normSq_denom`; or a direct `field_simp` computation.
* `lftAct_image_horoball`: `Im(A · z) = det A · y/|cz + d|²` and
  `|A · z - (a/c + ir)|² - r² = ...`; the inverse map is `lftAct (adjugate A)`. The book gives the
  formula without proof. `lftAct_R_horoballAtInfty` and `lftAct_R_sq_horoballAtInfty` follow with
  `R = [[1/2, -√3/2], [√3/2, 1/2]]`, `c² = 3/4`.
* `lftAct_R_edgeHalfPlane`, `lftAct_R_sq_edgeHalfPlane`: the images of the generalized circle
  `15x + y - 15/√3 = 0` (`UpperHalfPlane.genCircle_smul` in
  `Basic/Analysis/Complex/UpperHalfPlane/GeneralizedCircle.lean`, with the sign of the left-hand
  side preserved since it is multiplied by `|cz + d|² > 0`), and the bijectivity of `lftAct A` on
  the upper half-plane for `det A = 1`.
* `truncatedStarDomain_eq`: from the four image lemmas.
* `isCompact_truncatedStarDomain`: closed and bounded. Bounded: `y ≤ 4.5`, `|x| < 1/√3`. Closed:
  the explicit inequalities are closed, and they force the strict inequalities of `𝔥*`: the
  conditions of `Π₁⁺` give `x² + y² ≥ 1/3 + 2y/(15√3)`, and those of `Π₀⁺`, `Π₂⁺` give
  `|x| ≤ 1/√3 - y/15`; near the cusps `(±1/√3, 0)` these two are incompatible with `y > 0`
  small (expand `x = 1/√3 - δ`, `δ ≥ y/15`: `-2δ/√3 + δ² + y² ≥ 2y/(15√3)` fails for small
  `δ, y > 0`), and `y = 0` is excluded since then `|x| < 1/√3` contradicts `x² ≥ 1/3`. So the
  explicit set equals the closed set obtained by replacing `𝔥*` by its closure.
* Dihedral invariance: `R` permutes the three horoballs (`R³ = -I` acts trivially) and the three
  half-planes; `S` fixes `B(i∞)` and `Π₁⁺` and exchanges `B(1/√3) ↔ B(-1/√3)`, `Π₀⁺ ↔ Π₂⁺`
  (explicit forms). The invariance of `𝔥*` is §4.6 (`ρ_R_conj`, `ρ_reflS_conj` with
  `theorem4_4_1` and `Φ_lftAct`, `reflS_conj_Φ`).
* Fundamental domain: the three medians `x = 0`, `(x ∓ 1/√3)² + y² = 4/3` through `i` cut `𝔥*`
  into six sectors permuted by `R` and `S`; an explicit case analysis on the signs of `x` and of
  `(x ∓ 1/√3)² + y² - 4/3` gives the element of the group. The intersections: `B(±1/√3)` lies in
  `y < 8/27` and `Π₁⁺` in `y < 0.62`, below `y = 1`; `Π₂⁺ ∩ {x ≥ 0}` lies in `y > 15/√3 > 4.5`.

Size: 300–500 lines.
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

/-- Remark 4.2.2 in coordinates: for `det A = 1` and `y > 0`, `Φ(A · z) = A Φ(z) A⁻¹`. -/
theorem Φ_lftAct (A : Mat2) (hA : A.det = 1) {z : ℝ × ℝ} (hz : 0 < z.2) :
    Φ (lftAct A z).1 (lftAct A z).2 = A * Φ z.1 z.2 * A⁻¹ := by
  sorry

/-- **Images of horoballs** (TeX 3904–3915). For `A = [[a, b], [c, d]]` with `det A > 0` and
`c ≠ 0`, the linear fractional transformation `A` maps the open horoball `{y > y₀}`, `y₀ > 0`, onto
the open disk tangent to the real axis at `A · ∞ = a/c`, with center `a/c + ir` and radius
`r = det A/(2y₀c²)`. (The book states it for the horocycle `y = y₀` and its image circle.) -/
theorem lftAct_image_horoball (A : Mat2) (hA : 0 < A.det) (hc : A 1 0 ≠ 0) {y₀ : ℝ}
    (hy₀ : 0 < y₀) :
    lftAct A '' {z | y₀ < z.2} =
      {w | (w.1 - A 0 0 / A 1 0) ^ 2 + (w.2 - A.det / (2 * y₀ * A 1 0 ^ 2)) ^ 2 <
        (A.det / (2 * y₀ * A 1 0 ^ 2)) ^ 2} := by
  sorry

/-- `B(1/√3) = R B(i∞)` is the open disk of radius `4/27` tangent to the real axis at `1/√3`
(Definition 5.0.1, TeX 3922–3925). -/
theorem lftAct_R_horoballAtInfty :
    lftAct R '' horoballAtInfty =
      {w | (w.1 - 1 / √3) ^ 2 + (w.2 - 4 / 27) ^ 2 < (4 / 27) ^ 2} := by
  sorry

/-- `B(-1/√3) = R² B(i∞)` is the open disk of radius `4/27` tangent to the real axis at `-1/√3`
(Definition 5.0.1, TeX 3922–3925). -/
theorem lftAct_R_sq_horoballAtInfty :
    lftAct (R ^ 2) '' horoballAtInfty =
      {w | (w.1 + 1 / √3) ^ 2 + (w.2 - 4 / 27) ^ 2 < (4 / 27) ^ 2} := by
  sorry

/-- `Π₁⁺ = R Π₀⁺` is the part of the upper half-plane inside the circle
`x² + y² - 2y/(15√3) = 1/3` through `±1/√3`, a neighbourhood of the lower edge
`x² + y² = 1/3` of `𝔥*` (Definition 5.0.1). -/
theorem lftAct_R_edgeHalfPlane :
    lftAct R '' edgeHalfPlane =
      {w | 0 < w.2 ∧ w.1 ^ 2 + w.2 ^ 2 - 2 * w.2 / (15 * √3) < 1 / 3} := by
  sorry

/-- `Π₂⁺ = R² Π₀⁺` is the half-plane `{y > 15(x + 1/√3)}`, the mirror image of `Π₀⁺`
(Definition 5.0.1). -/
theorem lftAct_R_sq_edgeHalfPlane :
    lftAct (R ^ 2) '' edgeHalfPlane = {w | 0 < w.2 ∧ 15 * (w.1 + 1 / √3) < w.2} := by
  sorry

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
  sorry

/-- **`𝔥**` is compact** (`def:compactification:compact`, label of this formalization;
Definition 5.0.1, asserted without proof at TeX 3975). -/
theorem isCompact_truncatedStarDomain : IsCompact truncatedStarDomain := by
  sorry

/-- §4.6: the rotation `R` maps the star domain onto itself (TeX 3779, "the dihedral group acts
on the star domain"). -/
theorem image_lftAct_R_starDomain : lftAct R '' starDomain = starDomain := by
  sorry

/-- §4.6: the reflection `z ↦ -z̄` maps the star domain onto itself. -/
theorem image_reflAct_starDomain : reflAct '' starDomain = starDomain := by
  sorry

/-- **`𝔥**` is invariant under the rotation `R`** (TeX 3976–3977: "the shape of the
compactification has been chosen to be invariant under the action of the dihedral group"). -/
theorem image_lftAct_R_truncatedStarDomain :
    lftAct R '' truncatedStarDomain = truncatedStarDomain := by
  sorry

/-- **`𝔥**` is invariant under the reflection `z ↦ -z̄`** (TeX 3976–3977). -/
theorem image_reflAct_truncatedStarDomain :
    reflAct '' truncatedStarDomain = truncatedStarDomain := by
  sorry

/-- The dihedral group preserves `𝔥*` and `𝔥**`: for every element `S^b R^n`, `z ∈ 𝔥*` iff its
image is, and `z ∈ 𝔥**` iff its image is. -/
theorem dihedralAct_mem_iff (n : ℕ) (b : Bool) {z : ℝ × ℝ} (hz : 0 < z.2) :
    (dihedralAct n b z ∈ starDomain ↔ z ∈ starDomain) ∧
      (dihedralAct n b z ∈ truncatedStarDomain ↔ z ∈ truncatedStarDomain) := by
  sorry

/-- **A fundamental domain of the dihedral action on `𝔥*`** (§4.6, TeX 3794–3809; proof of
Theorem 5.0.2, TeX 4475–4479): every point of `𝔥*` is mapped into `fundamentalDomain` by an element
`S^b R^n` of the dihedral group. -/
theorem exists_dihedralAct_mem_fundamentalDomain {z : ℝ × ℝ} (hz : z ∈ starDomain) :
    ∃ n : Fin 3, ∃ b : Bool, dihedralAct n b z ∈ fundamentalDomain := by
  sorry

/-- The sets of Definition 5.0.1 that meet the fundamental domain (proof of Theorem 5.0.2,
TeX 4480–4484 and 4500–4501): the fundamental domain lies in `{x ≥ 0, y ≥ 1}`, and a point of it
outside `𝔥**` lies in `B(i∞)` or in `Π₀⁺ ∩ {y ≤ 4.5}`. (The book says that only `B(i∞)` and `Π₀⁺`
meet `{x ≥ 0, y ≥ 1}`; `Π₂⁺` meets it too, but only inside `B(i∞)`.) -/
theorem mem_horoball_or_edgeHalfPlane_of_mem_fundamentalDomain {z : ℝ × ℝ}
    (hz : z ∈ fundamentalDomain) :
    0 ≤ z.1 ∧ 1 ≤ z.2 ∧
      (z ∉ truncatedStarDomain → z ∈ horoballAtInfty ∨ (z ∈ edgeHalfPlane ∧ z.2 ≤ 9 / 2)) := by
  sorry

end SmoothedPolygons
