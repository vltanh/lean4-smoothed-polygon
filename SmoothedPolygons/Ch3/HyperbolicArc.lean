module

public import SmoothedPolygons.Ch2.MultiCurve
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.LinearAlgebra.AffineSpace.Midpoint

/-!
# Hyperbolic arcs (Lemma 3.1.8)

If two curves `σ_{i-1}` and `σ_{i+1}` of a multi-curve parametrizing the boundary of a centrally
symmetric convex disk move along straight lines during a time interval, then the third curve `σ_i`
moves along a hyperbolic arc whose asymptotes are these two lines (Reinhardt's observation that
the pencil of lines cutting a constant area from a parallelogram envelopes a hyperbola).

The lemma belongs to §3.1 (`SmoothedPolygons.Ch3.StateDynamics`); it is kept in its own module
because it uses only the vocabulary of Chapter 2 (`IsCCSDisk`, `IsMultiCurve`, `det2`) and adding
it to `StateDynamics` would rebuild the modules of Chapters 3–7 that import it.

The book's proof uses three pieces of plane geometry, proved here:

* lines and their intersection points (`hyp_line`, `hyp_lineInter`) and the signed area of a
  polygon by the shoelace formula (`hyp_area`), with the area of a centrally symmetric hexagon in
  terms of two consecutive edge midpoints (`hyp_area_hex3`) and the additivity of the area when
  two opposite corners of a parallelogram are cut off (`hyp_area_cut`);
* **Reinhardt's observation** (§2.2, TeX 1404–1418) in the form the proof uses: the midpoint of
  the segment that a line cuts out of the two sides of an angle lies on the hyperbola with the
  sides as asymptotes determined by the area of the triangle cut off (`hyp_reinhardt_midpoint`);
* **the hexagon `H_K(t)` of a multi-curve at the multi-point `σ(t)`** (`hyp_hexagon`), cut out by
  the six tangent lines at the `σ_j(t)`: its edges lie on the tangent lines
  (`hyp_hexagon_mem_tangent`), it is centrally symmetric (`hyp_hexagon_add_three`), its edge
  midpoints are the `σ_j(t)` (`hyp_midpoint_hexagon`) and its area is `√12`
  (`hyp_area_hexagon`), whenever the tangent lines at `σ_j(t)` and `σ_{j+2}(t)` are not parallel
  (for one `j`, equivalently for all: `hyp_det2_vel_eq`).

Chapter 2's centrally symmetric hexagons (`IsCSHexagon`, `hexagonOf`, `hexMidpoint`, with the
areas `rein_volume_hexagonOf_hex3` and `hex_volume_hexagonOf`) are convex hexagons measured by
Lebesgue measure. The proof below does not need `H_K(t)` to be convex, so it measures areas by
the signed area `hyp_area`, and this module does not import those files.

Conventions. The line through `p` with direction `d ≠ 0` is `{x | det(d, x - p) = 0}`. For two
lines `L₁ = {det(d₁, x - p₁) = 0}` and `L₂ = {det(d₂, x - p₂) = 0}` that are not parallel
(`det(d₁, d₂) ≠ 0`), the level sets `{x | det(d₁, x - p₁) · det(d₂, x - p₂) = c}` with `c ≠ 0` are
exactly the hyperbolas with asymptotes `L₁` and `L₂`, as in Remark 2.2.4 (`hexHyperbolaFun`).
The velocity `σ_j'(t)` of a multi-curve on `[0, t_f]` is the derivative within `[0, t_f]`
(`hyp_vel`), one-sided at the ends of the interval.
-/

@[expose] public section

namespace SmoothedPolygons

open Set Filter Topology

/-! ### Determinants -/

/-- `det(d, x - p) = det(d, x) - det(d, p)`. -/
private lemma sm_det2_sub (d x p : Fin 2 → ℝ) : det2 d (x - p) = det2 d x - det2 d p := by
  simp only [det2, Pi.sub_apply]; ring

private lemma sm_det2_add (d x y : Fin 2 → ℝ) : det2 d (x + y) = det2 d x + det2 d y := by
  simp only [det2, Pi.add_apply]; ring

private lemma sm_det2_neg (d x : Fin 2 → ℝ) : det2 d (-x) = -det2 d x := by
  simp only [det2, Pi.neg_apply]; ring

private lemma sm_det2_comm (x y : Fin 2 → ℝ) : det2 x y = -det2 y x := by
  simp only [det2]; ring

private lemma sm_det2_self (x : Fin 2 → ℝ) : det2 x x = 0 := by
  simp only [det2]; ring

/-- Cramer's rule in the plane: `det(a, b) c = det(c, b) a + det(a, c) b`. -/
private lemma sm_cramer (a b c : Fin 2 → ℝ) :
    det2 a b • c = det2 c b • a + det2 a c • b := by
  ext k
  fin_cases k <;> simp [det2] <;> ring

private lemma sm_ne_zero_of_det2 {d : Fin 2 → ℝ} (hd : d ≠ 0) : 0 < d 0 ^ 2 + d 1 ^ 2 := by
  by_contra h
  apply hd
  ext k
  fin_cases k <;> simp <;> nlinarith [sq_nonneg (d 0), sq_nonneg (d 1)]

/-- Two vectors parallel to a nonzero vector `u` are parallel (as `bdy_det2_eq_zero_of_parallel`
in `SmoothedPolygons.Ch2.Boundary`, which this module does not import). -/
private lemma hyp_det2_eq_zero_of_parallel {u a w : Fin 2 → ℝ} (hu : u ≠ 0) (ha : det2 u a = 0)
    (hw : det2 u w = 0) : det2 a w = 0 := by
  have h0 : det2 a w * u 0 = 0 := by
    unfold det2 at *; linear_combination (a 0) * hw - (w 0) * ha
  have h1 : det2 a w * u 1 = 0 := by
    unfold det2 at *; linear_combination (a 1) * hw - (w 1) * ha
  have h : det2 a w * (u 0 ^ 2 + u 1 ^ 2) = 0 := by
    linear_combination (u 0) * h0 + (u 1) * h1
  exact (mul_eq_zero.1 h).resolve_right (sm_ne_zero_of_det2 hu).ne'

/-- Nonzero vectors parallel to two nonparallel vectors `d₁`, `d₂` are not parallel. -/
private lemma hyp_det2_ne_zero_of_parallel {d₁ d₂ u w : Fin 2 → ℝ} (hD : det2 d₁ d₂ ≠ 0)
    (hu : u ≠ 0) (hw : w ≠ 0) (h₁ : det2 d₁ u = 0) (h₂ : det2 d₂ w = 0) : det2 u w ≠ 0 := by
  intro huw
  have hu₁ : det2 u d₁ = 0 := by rw [sm_det2_comm, h₁, neg_zero]
  have hw₁ : det2 w d₁ = 0 := by
    rw [sm_det2_comm]; exact neg_eq_zero.2 (hyp_det2_eq_zero_of_parallel hu hu₁ huw)
  have hw₂ : det2 w d₂ = 0 := by rw [sm_det2_comm, h₂, neg_zero]
  exact hD (hyp_det2_eq_zero_of_parallel hw hw₁ hw₂)

/-! ### Lines and their intersections -/

/-- The line through `p` with direction `d`: `{x | det(d, x - p) = 0}` (a line when `d ≠ 0`). -/
def hyp_line (d p : Fin 2 → ℝ) : Set (Fin 2 → ℝ) := {x | det2 d (x - p) = 0}

lemma hyp_mem_line {d p x : Fin 2 → ℝ} : x ∈ hyp_line d p ↔ det2 d (x - p) = 0 := Iff.rfl

/-- A point of a line can serve as its base point. -/
lemma hyp_mem_line_of_mem {d p q x : Fin 2 → ℝ} (hq : q ∈ hyp_line d p)
    (hx : x ∈ hyp_line d p) : x ∈ hyp_line d q := by
  rw [hyp_mem_line, sm_det2_sub] at *
  linarith

/-- The line through a point `x` of `hyp_line d p` with a direction `v ≠ 0` parallel to `d` is
`hyp_line d p`. -/
lemma hyp_line_eq {d p v x : Fin 2 → ℝ} (hd : d ≠ 0) (hv : v ≠ 0) (hdv : det2 d v = 0)
    (hx : x ∈ hyp_line d p) : hyp_line v x = hyp_line d p := by
  ext y
  have e : det2 d (y - p) = det2 d (y - x) := by
    rw [hyp_mem_line, sm_det2_sub] at hx
    rw [sm_det2_sub, sm_det2_sub]; linarith
  rw [hyp_mem_line, hyp_mem_line, e]
  have hvd : det2 v d = 0 := by rw [sm_det2_comm, hdv, neg_zero]
  exact ⟨fun h ↦ hyp_det2_eq_zero_of_parallel hv hvd h,
    fun h ↦ hyp_det2_eq_zero_of_parallel hd hdv h⟩

/-- The intersection point `(det(d, p) e - det(e, q) d) / det(d, e)` of the lines `hyp_line d p`
and `hyp_line e q` when they are not parallel (`det(d, e) ≠ 0`; `hyp_lineInter_mem_left`,
`hyp_lineInter_mem_right`, `hyp_eq_lineInter`). -/
noncomputable def hyp_lineInter (d p e q : Fin 2 → ℝ) : Fin 2 → ℝ :=
  (det2 d e)⁻¹ • (det2 d p • e - det2 e q • d)

lemma hyp_lineInter_mem_left {d p e q : Fin 2 → ℝ} (h : det2 d e ≠ 0) :
    hyp_lineInter d p e q ∈ hyp_line d p := by
  have e : det2 d (hyp_lineInter d p e q) = (det2 d e)⁻¹ * (det2 d e * det2 d p) := by
    simp only [hyp_lineInter, det2, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  rw [hyp_mem_line, sm_det2_sub, e, inv_mul_cancel_left₀ h, sub_self]

lemma hyp_lineInter_mem_right {d p e q : Fin 2 → ℝ} (h : det2 d e ≠ 0) :
    hyp_lineInter d p e q ∈ hyp_line e q := by
  have e : det2 e (hyp_lineInter d p e q) = (det2 d e)⁻¹ * (det2 d e * det2 e q) := by
    simp only [hyp_lineInter, det2, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  rw [hyp_mem_line, sm_det2_sub, e, inv_mul_cancel_left₀ h, sub_self]

/-- Two nonparallel lines meet in exactly one point. -/
lemma hyp_eq_lineInter {d p e q x : Fin 2 → ℝ} (h : det2 d e ≠ 0) (h₁ : x ∈ hyp_line d p)
    (h₂ : x ∈ hyp_line e q) : x = hyp_lineInter d p e q := by
  rw [hyp_mem_line] at h₁ h₂
  have key : det2 d e • x = det2 d p • e - det2 e q • d := by
    simp only [det2, Pi.sub_apply] at h₁ h₂
    ext k
    fin_cases k <;> simp [det2]
    · linear_combination e 0 * h₁ - d 0 * h₂
    · linear_combination e 1 * h₁ - d 1 * h₂
  rw [hyp_lineInter, ← key, smul_smul, inv_mul_cancel₀ h, one_smul]

/-- The intersection of the reflected lines is the reflected intersection point. -/
lemma hyp_lineInter_neg (d p e q : Fin 2 → ℝ) :
    hyp_lineInter (-d) (-p) (-e) (-q) = -hyp_lineInter d p e q := by
  ext k
  simp only [hyp_lineInter, det2, Pi.neg_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-! ### Signed areas of polygons -/

/-- The signed area of the polygon with vertices `x₀, …, x_{n-1}`, by the shoelace formula
`½ (det(x₀, x₁) + det(x₁, x₂) + ⋯ + det(x_{n-1}, x₀))`. For a convex polygon whose vertices are
listed counterclockwise, it is the area of the polygon. -/
noncomputable def hyp_area (l : List (Fin 2 → ℝ)) : ℝ :=
  (List.zipWith det2 l (l.rotate 1)).sum / 2

/-- The signed area of the triangle `O, P, Q` is `det(P - O, Q - O)/2`. -/
lemma hyp_area_triangle (O P Q : Fin 2 → ℝ) : hyp_area [O, P, Q] = det2 (P - O) (Q - O) / 2 := by
  simp [hyp_area, det2]
  ring

/-- Three points on a line span a triangle of area zero. -/
lemma hyp_area_eq_zero_of_mem_line {d p x y z : Fin 2 → ℝ} (hd : d ≠ 0) (hx : x ∈ hyp_line d p)
    (hy : y ∈ hyp_line d p) (hz : z ∈ hyp_line d p) : hyp_area [x, y, z] = 0 := by
  rw [hyp_area_triangle, hyp_det2_eq_zero_of_parallel hd (hyp_mem_line_of_mem hx hy)
    (hyp_mem_line_of_mem hx hz), zero_div]

/-- The area of the centrally symmetric hexagon `a, b, c, -a, -b, -c` is `4 det(m₀, m₁)`, where
`m₀, m₁` are the midpoints of the edges `ab` and `bc` (the signed form of
`rein_volume_hexagonOf_hex3` and `hex_volume_hexagonOf` in Chapter 2). -/
lemma hyp_area_hex3 (a b c : Fin 2 → ℝ) :
    hyp_area [a, b, c, -a, -b, -c] = 4 * det2 (midpoint ℝ a b) (midpoint ℝ b c) := by
  simp [hyp_area, midpoint_eq_smul_add, det2]
  ring

/-- **Cutting two corners off a parallelogram.** Let `-R, O, R, -O` be a parallelogram, and let
`P` lie on the line `-R O` and `Q` on the line `O R`. Cutting off the triangles `O Q P` and
`-O -Q -P` leaves the hexagon `P, Q, R, -P, -Q, -R`, and the areas add up:
`area(-R, O, R, -O) = area(P, Q, R, -P, -Q, -R) + 2 area(O, Q, P)`. -/
lemma hyp_area_cut {O R P Q : Fin 2 → ℝ} (hP : hyp_area [-R, P, O] = 0)
    (hQ : hyp_area [O, Q, R] = 0) :
    hyp_area [-R, O, R, -O] = hyp_area [P, Q, R, -P, -Q, -R] + 2 * hyp_area [O, Q, P] := by
  simp [hyp_area, det2] at hP hQ ⊢
  linear_combination -hP - hQ

/-! ### Reinhardt's observation -/

/-- **Reinhardt's observation** (§2.2, TeX 1404–1418: the hyperbola is the envelope of a pencil
of lines cutting a constant area from an angle, and "every point on the hyperbolic envelope is the
midpoint of a unique line segment formed by a line in the pencil and the `x` and `y` axes"), in
the form the proof of Lemma 3.1.8 uses: the midpoints of these segments lie on the hyperbola.

Let `ℓ₁ = hyp_line d₁ O` and `ℓ₂ = hyp_line d₂ O` be two lines through `O`. A line meeting `ℓ₁`
at `P` and `ℓ₂` at `Q` cuts from the angle the triangle `O, P, Q`, of signed area `A`; the
midpoint `M` of the segment `PQ` lies on the hyperbola
`det(d₁, x - O) det(d₂, x - O) = -det(d₁, d₂) A / 2`, whose asymptotes are `ℓ₁` and `ℓ₂`.
So the lines cutting a constant area `A` from the angle have the midpoints of their segments on
one hyperbola, which is nondegenerate when `A ≠ 0` and the lines are not parallel. The envelope
statement itself is not needed: the proof of Lemma 3.1.8 uses only the midpoints ("the midpoints
`σ₀(t)` must lie on that envelope"). -/
theorem hyp_reinhardt_midpoint {O d₁ d₂ P Q : Fin 2 → ℝ} (hP : P ∈ hyp_line d₁ O)
    (hQ : Q ∈ hyp_line d₂ O) :
    det2 d₁ (midpoint ℝ P Q - O) * det2 d₂ (midpoint ℝ P Q - O) =
      -(det2 d₁ d₂ * hyp_area [O, P, Q]) / 2 := by
  rw [hyp_area_triangle]
  rw [hyp_mem_line] at hP hQ
  simp only [midpoint_eq_smul_add, invOf_eq_inv, det2, Pi.sub_apply, Pi.smul_apply,
    Pi.add_apply, smul_eq_mul] at hP hQ ⊢
  linear_combination
    ((d₂ 0 * (P 1 - O 1) - d₂ 1 * (P 0 - O 0)) +
      2 * (d₂ 0 * (Q 1 - O 1) - d₂ 1 * (Q 0 - O 0))) / 4 * hP +
    (d₁ 0 * (Q 1 - O 1) - d₁ 1 * (Q 0 - O 0)) / 4 * hQ

/-! ### The hexagon of a multi-curve at a multi-point -/

/-- The multi-point relations `s_{j+1} = s_j + s_{j+2}`, `s_{j+3} = -s_j` and
`det(s_j, s_{j+2}) = √3/2`. -/
private lemma hyp_mp {s : ZMod 6 → Fin 2 → ℝ} (hs : IsMultiPoint s) (j : ZMod 6) :
    s (j + 1) = s j + s (j + 2) ∧ s (j + 3) = -s j ∧ det2 (s j) (s (j + 2)) = √3 / 2 := by
  have h1 := (hs j).1
  have h2 := (hs (j + 1)).2.1
  rw [show j + 1 + 3 = j + 4 by ring] at h2
  rw [h2] at h1
  have e : s (j + 1) = s j + s (j + 2) := by linear_combination -h1
  refine ⟨e, (hs j).2.1, ?_⟩
  have h3 := (hs j).2.2
  rwa [e, sm_det2_add, sm_det2_self, zero_add] at h3

/-- The multi-point relations around `s_i`: `s_i = s_{i-1} + s_{i+1}`,
`det(s_{i-1}, s_i) = det(s_{i-1}, s_{i+1}) = √3/2`. -/
private lemma hyp_mp_at {s : ZMod 6 → Fin 2 → ℝ} (hs : IsMultiPoint s) (i : ZMod 6) :
    s i = s (i - 1) + s (i + 1) ∧ det2 (s (i - 1)) (s i) = √3 / 2 ∧
      det2 (s (i - 1)) (s (i + 1)) = √3 / 2 := by
  obtain ⟨h1, -, h3⟩ := hyp_mp hs (i - 1)
  have h2 := (hs (i - 1)).2.2
  rw [show i - 1 + 1 = i by ring] at h1 h2
  rw [show i - 1 + 2 = i + 1 by ring] at h1 h3
  exact ⟨h1, h2, h3⟩

/-- The velocity `σ_j'(t)` of a multi-curve on `[0, t_f]`: the derivative of `σ_j` within
`[0, t_f]` (one-sided at the ends of the interval). -/
noncomputable def hyp_vel (σ : ZMod 6 → ℝ → Fin 2 → ℝ) (tf : ℝ) (j : ZMod 6) (t : ℝ) :
    Fin 2 → ℝ :=
  derivWithin (σ j) (Icc 0 tf) t

/-- The derivative of `x ↦ det(f(x), g(x))`. -/
private lemma hyp_hasDerivWithinAt_det2 {f g : ℝ → Fin 2 → ℝ} {f' g' : Fin 2 → ℝ} {s : Set ℝ}
    {t : ℝ} (hf : HasDerivWithinAt f f' s t) (hg : HasDerivWithinAt g g' s t) :
    HasDerivWithinAt (fun x ↦ det2 (f x) (g x)) (det2 f' (g t) + det2 (f t) g') s t := by
  have h := HasDerivWithinAt.sub (HasDerivWithinAt.mul (hasDerivWithinAt_pi.1 hf 0)
    (hasDerivWithinAt_pi.1 hg 1)) (HasDerivWithinAt.mul (hasDerivWithinAt_pi.1 hf 1)
    (hasDerivWithinAt_pi.1 hg 0))
  have e : det2 f' (g t) + det2 (f t) g' =
      f' 0 * g t 1 + f t 0 * g' 1 - (f' 1 * g t 0 + f t 1 * g' 0) := by
    simp only [det2]; ring
  rw [e]
  exact h

section MultiCurve

variable {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {tf t : ℝ}

private lemma hyp_hasDerivWithinAt_vel (hσ : IsMultiCurve 1 σ tf) (ht : t ∈ Icc 0 tf)
    (j : ZMod 6) : HasDerivWithinAt (σ j) (hyp_vel σ tf j t) (Icc 0 tf) t :=
  (((hσ.1 j).differentiableOn (by norm_num)) t ht).hasDerivWithinAt

/-- The differentiated multi-point relations: `σ_{j+1}' = σ_j' + σ_{j+2}'`, `σ_{j+3}' = -σ_j'`, and
`det(σ_j', σ_{j+2}) + det(σ_j, σ_{j+2}') = 0` (the derivative of `det(σ_j, σ_{j+2}) = √3/2`). -/
lemma hyp_vel_rel (hσ : IsMultiCurve 1 σ tf) (htf : 0 < tf) (ht : t ∈ Icc 0 tf) (j : ZMod 6) :
    hyp_vel σ tf (j + 1) t = hyp_vel σ tf j t + hyp_vel σ tf (j + 2) t ∧
      hyp_vel σ tf (j + 3) t = -hyp_vel σ tf j t ∧
      det2 (hyp_vel σ tf j t) (σ (j + 2) t) + det2 (σ j t) (hyp_vel σ tf (j + 2) t) = 0 := by
  have hu : UniqueDiffWithinAt ℝ (Icc 0 tf) t := uniqueDiffOn_Icc htf t ht
  have hd := hyp_hasDerivWithinAt_vel hσ ht
  have hm : ∀ s ∈ Icc 0 tf, _ := fun s hs ↦ hyp_mp (hσ.2 s hs) j
  refine ⟨?_, ?_, ?_⟩
  · exact hu.eq_deriv _ (hd (j + 1))
      (((hd j).add (hd (j + 2))).congr_of_mem (fun s hs ↦ (hm s hs).1) ht)
  · exact hu.eq_deriv _ (hd (j + 3)) ((hd j).neg.congr_of_mem (fun s hs ↦ (hm s hs).2.1) ht)
  · exact hu.eq_deriv _ (hyp_hasDerivWithinAt_det2 (hd j) (hd (j + 2)))
      ((hasDerivWithinAt_const t _ (√3 / 2)).congr_of_mem (fun s hs ↦ (hm s hs).2.2) ht)

private lemma hyp_det2_vel_succ (hσ : IsMultiCurve 1 σ tf) (htf : 0 < tf) (ht : t ∈ Icc 0 tf)
    (j : ZMod 6) :
    det2 (hyp_vel σ tf (j + 1) t) (hyp_vel σ tf (j + 1 + 2) t) =
      det2 (hyp_vel σ tf j t) (hyp_vel σ tf (j + 2) t) := by
  obtain ⟨e1, e3, -⟩ := hyp_vel_rel hσ htf ht j
  rw [show j + 1 + 2 = j + 3 by ring, e1, e3]
  simp only [det2, Pi.add_apply, Pi.neg_apply]; ring

/-- `det(σ_j'(t), σ_{j+2}'(t))` does not depend on `j` (writing `σ_j(t) = g s_j*`, it is
`det(g X s_j*, g X s_{j+2}*) = (√3/2) det X`, the determinant that Remark 3.1.7 (`rem:hexagon`)
divides by). -/
lemma hyp_det2_vel_eq (hσ : IsMultiCurve 1 σ tf) (htf : 0 < tf) (ht : t ∈ Icc 0 tf)
    (j k : ZMod 6) :
    det2 (hyp_vel σ tf k t) (hyp_vel σ tf (k + 2) t) =
      det2 (hyp_vel σ tf j t) (hyp_vel σ tf (j + 2) t) := by
  have step : ∀ n : ℕ, det2 (hyp_vel σ tf (j + n) t) (hyp_vel σ tf (j + n + 2) t) =
      det2 (hyp_vel σ tf j t) (hyp_vel σ tf (j + 2) t) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.cast_succ, ← add_assoc, hyp_det2_vel_succ hσ htf ht, ih]
  have hk : k = j + ((k - j).val : ℕ) := by rw [ZMod.natCast_zmod_val]; ring
  rw [hk]
  exact step _

/-- Consecutive tangent lines are not parallel when `σ_j'(t)`, `σ_{j+2}'(t)` are not. -/
private lemma hyp_det2_vel_add_one_ne (hσ : IsMultiCurve 1 σ tf) (htf : 0 < tf)
    (ht : t ∈ Icc 0 tf) (hX : ∀ j, det2 (hyp_vel σ tf j t) (hyp_vel σ tf (j + 2) t) ≠ 0)
    (k : ZMod 6) : det2 (hyp_vel σ tf k t) (hyp_vel σ tf (k + 1) t) ≠ 0 := by
  rw [(hyp_vel_rel hσ htf ht k).1, sm_det2_add, sm_det2_self, zero_add]
  exact hX k

/-- **The hexagon `H_K(t)`** of a multi-curve at the multi-point `σ(t)` (the book's "time
dependent critical hexagon" in the proof of Lemma 3.1.8; Remark 3.1.7 (`rem:hexagon`)): its vertex
`k` is the intersection of the tangent lines at `σ_{k-1}(t)` and `σ_k(t)`, so that its edge from
the vertex `k` to the vertex `k + 1` lies on the tangent line at `σ_k(t)`. -/
noncomputable def hyp_hexagon (σ : ZMod 6 → ℝ → Fin 2 → ℝ) (tf t : ℝ) (k : ZMod 6) :
    Fin 2 → ℝ :=
  hyp_lineInter (hyp_vel σ tf (k - 1) t) (σ (k - 1) t) (hyp_vel σ tf k t) (σ k t)

/-- **The edges of `H_K(t)` lie on the tangent lines**: the vertices `k` and `k + 1` of `H_K(t)`
lie on the tangent line at `σ_k(t)`; the vertex `k` also lies on the tangent line at
`σ_{k-1}(t)`. -/
theorem hyp_hexagon_mem_tangent (hσ : IsMultiCurve 1 σ tf) (htf : 0 < tf) (ht : t ∈ Icc 0 tf)
    (hX : ∀ j, det2 (hyp_vel σ tf j t) (hyp_vel σ tf (j + 2) t) ≠ 0) (k : ZMod 6) :
    hyp_hexagon σ tf t k ∈ hyp_line (hyp_vel σ tf (k - 1) t) (σ (k - 1) t) ∧
      hyp_hexagon σ tf t k ∈ hyp_line (hyp_vel σ tf k t) (σ k t) ∧
      hyp_hexagon σ tf t (k + 1) ∈ hyp_line (hyp_vel σ tf k t) (σ k t) := by
  have hne := hyp_det2_vel_add_one_ne hσ htf ht hX (k - 1)
  rw [sub_add_cancel] at hne
  refine ⟨hyp_lineInter_mem_left hne, hyp_lineInter_mem_right hne, ?_⟩
  have h := hyp_lineInter_mem_left (p := σ k t) (q := σ (k + 1) t)
    (hyp_det2_vel_add_one_ne hσ htf ht hX k)
  rwa [hyp_hexagon, add_sub_cancel_right]

/-- The core of the midpoint property: let `u, w` and `s = u + w` be points with velocities
`u', w'` and `s' = u' + w'`, such that `det(u, w)` is stationary
(`det(u', w) + det(u, w') = 0`) and the lines through `u`, `w` with directions `u'`, `w'` are not
parallel. If the line through `s` with direction `s'` meets them at `P` and `Q`, then `s` is the
midpoint of `PQ`. -/
private lemma hyp_midpoint_of_tangent {u w u' w' P Q : Fin 2 → ℝ}
    (hc : det2 u' w + det2 u w' = 0) (hne : det2 u' w' ≠ 0)
    (hPs : P ∈ hyp_line (u' + w') (u + w)) (hPu : P ∈ hyp_line u' u)
    (hQs : Q ∈ hyp_line (u' + w') (u + w)) (hQw : Q ∈ hyp_line w' w) :
    midpoint ℝ P Q = u + w := by
  rw [hyp_mem_line] at hPs hPu hQs hQw
  have key : ∀ k, det2 u' w' * (P k + Q k - 2 * (u k + w k)) = 0 := by
    intro k
    unfold det2 at hc hPs hPu hQs hQw ⊢
    simp only [Pi.add_apply, Pi.sub_apply] at hPs hPu hQs hQw
    fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue]
    · linear_combination
        -(u' 0) * hPs + (u' 0 + w' 0) * hPu + (w' 0) * hQs - (u' 0 + w' 0) * hQw -
          (u' 0 + w' 0) * hc
    · linear_combination
        -(u' 1) * hPs + (u' 1 + w' 1) * hPu + (w' 1) * hQs - (u' 1 + w' 1) * hQw -
          (u' 1 + w' 1) * hc
  ext k
  have h := (mul_eq_zero.1 (key k)).resolve_left hne
  simp only [midpoint_eq_smul_add, invOf_eq_inv, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  linarith

/-- **The edge midpoints of `H_K(t)` are the points `σ_k(t)`** of the multi-point (the book:
"`±σ₀(t)` are the midpoints of those edges"; Remark 3.1.7 (`rem:hexagon`): "Each `s_j*` is
manifestly an edge midpoint"). The edge `k` lies on the tangent line at `σ_k(t)` between the
tangent lines at `σ_{k-1}(t)` and `σ_{k+1}(t)`; the midpoint property follows from
`σ_k = σ_{k-1} + σ_{k+1}` and the stationarity of `det(σ_{k-1}, σ_{k+1}) = √3/2`. -/
theorem hyp_midpoint_hexagon (hσ : IsMultiCurve 1 σ tf) (htf : 0 < tf) (ht : t ∈ Icc 0 tf)
    (hX : ∀ j, det2 (hyp_vel σ tf j t) (hyp_vel σ tf (j + 2) t) ≠ 0) (k : ZMod 6) :
    midpoint ℝ (hyp_hexagon σ tf t k) (hyp_hexagon σ tf t (k + 1)) = σ k t := by
  obtain ⟨hs, -, -⟩ := hyp_mp (hσ.2 t ht) (k - 1)
  obtain ⟨hv, -, hc⟩ := hyp_vel_rel hσ htf ht (k - 1)
  have hne := hX (k - 1)
  have e2 : k - 1 + 2 = k + 1 := by ring
  rw [sub_add_cancel, e2] at hs hv
  rw [e2] at hc hne
  obtain ⟨hP₁, hP₂, hQ₂⟩ := hyp_hexagon_mem_tangent hσ htf ht hX k
  have hQ₃ := (hyp_hexagon_mem_tangent hσ htf ht hX (k + 1)).2.1
  rw [hs, hv] at hP₂ hQ₂
  rw [hs]
  exact hyp_midpoint_of_tangent hc hne hP₂ hP₁ hQ₂ hQ₃

/-- `H_K(t)` is centrally symmetric: its vertex `k + 3` is minus its vertex `k`. -/
theorem hyp_hexagon_add_three (hσ : IsMultiCurve 1 σ tf) (htf : 0 < tf) (ht : t ∈ Icc 0 tf)
    (k : ZMod 6) : hyp_hexagon σ tf t (k + 3) = -hyp_hexagon σ tf t k := by
  have e : k + 3 - 1 = k - 1 + 3 := by ring
  rw [hyp_hexagon, hyp_hexagon, e, (hyp_vel_rel hσ htf ht (k - 1)).2.1,
    (hyp_vel_rel hσ htf ht k).2.1, (hyp_mp (hσ.2 t ht) (k - 1)).2.1,
    (hyp_mp (hσ.2 t ht) k).2.1, hyp_lineInter_neg]

/-- **The area of `H_K(t)` is `√12`** (§2.2: a centrally symmetric hexagon has area
`4 det(m₀, m₁)` in terms of two consecutive edge midpoints, and here `det(σ_k, σ_{k+1}) = √3/2`;
this is the normalization `area(H_K) = √12` of §2.2, `eqn:sqrt12`). The vertices are listed from
the vertex `k`, counterclockwise when `H_K(t)` is a convex hexagon around the origin. -/
theorem hyp_area_hexagon (hσ : IsMultiCurve 1 σ tf) (htf : 0 < tf) (ht : t ∈ Icc 0 tf)
    (hX : ∀ j, det2 (hyp_vel σ tf j t) (hyp_vel σ tf (j + 2) t) ≠ 0) (k : ZMod 6) :
    hyp_area [hyp_hexagon σ tf t k, hyp_hexagon σ tf t (k + 1), hyp_hexagon σ tf t (k + 2),
      hyp_hexagon σ tf t (k + 3), hyp_hexagon σ tf t (k + 4), hyp_hexagon σ tf t (k + 5)] =
      √12 := by
  have h1 := hyp_midpoint_hexagon hσ htf ht hX (k + 1)
  rw [show k + 1 + 1 = k + 2 by ring] at h1
  rw [show k + 4 = k + 1 + 3 by ring, show k + 5 = k + 2 + 3 by ring,
    hyp_hexagon_add_three hσ htf ht, hyp_hexagon_add_three hσ htf ht,
    hyp_hexagon_add_three hσ htf ht]
  rw [hyp_area_hex3, hyp_midpoint_hexagon hσ htf ht hX k, h1, (hσ.2 t ht k).2.2,
    show (12 : ℝ) = 2 ^ 2 * 3 by norm_num, Real.sqrt_mul (by norm_num),
    Real.sqrt_sq (by norm_num)]
  ring

end MultiCurve

/-! ### Lemma 3.1.8 -/

/-- A curve that is constant on a neighbourhood of `t₀` has derivative zero at `t₀`. -/
private lemma sm_derivWithin_eq_zero {f : ℝ → Fin 2 → ℝ} {s U : Set ℝ} {t₀ : ℝ}
    {C : Fin 2 → ℝ} (hU : U ∈ 𝓝 t₀) (hf : ∀ t ∈ U, f t = C) : derivWithin f s t₀ = 0 := by
  have h : f =ᶠ[𝓝 t₀] fun _ ↦ C := Filter.mem_of_superset hU fun t ht ↦ hf t ht
  rw [h.derivWithin_eq_of_nhds]
  simp

/-- **Supporting line.** If a curve `γ` in a convex set `K` with nonempty interior moves along the
line `{det(d, x - p) = 0}` near `t₀`, with nonzero velocity at `t₀`, and `γ(t₀)` is a boundary point
of `K`, then the line supports `K`: `K` lies on one side of it. -/
private lemma sm_support {K : Set (Fin 2 → ℝ)} (hKc : Convex ℝ K) (hKi : (interior K).Nonempty)
    {γ : ℝ → Fin 2 → ℝ} {t₀ : ℝ} {v : Fin 2 → ℝ} (hγ : HasDerivAt γ v t₀) (hv : v ≠ 0)
    (hK : ∀ᶠ t in 𝓝 t₀, γ t ∈ K) (hfr : γ t₀ ∉ interior K) {d p : Fin 2 → ℝ} (hd : d ≠ 0)
    (hline : ∀ᶠ t in 𝓝 t₀, det2 d (γ t - p) = 0) :
    ∃ μ : ℝ, μ ≠ 0 ∧ ∀ x ∈ K, μ * det2 d (x - p) ≤ 0 := by
  obtain ⟨φ, hφ⟩ := geometric_hahn_banach_open_point hKc.interior isOpen_interior hfr
  -- `φ ≤ φ(γ t₀)` on `K = closure (interior K)`
  have hle : ∀ x ∈ K, φ x ≤ φ (γ t₀) := by
    intro x hx
    have hcl : K ⊆ closure (interior K) := by
      rw [hKc.closure_interior_eq_closure_of_nonempty_interior hKi]; exact subset_closure
    have : closure (interior K) ⊆ {x | φ x ≤ φ (γ t₀)} :=
      closure_minimal (fun y hy ↦ (hφ y hy).le) (isClosed_le φ.continuous continuous_const)
    exact this (hcl hx)
  -- Fermat: `φ(v) = 0`
  have hmax : IsLocalMax (fun t ↦ φ (γ t)) t₀ := hK.mono fun t ht ↦ hle _ ht
  have hφv : φ v = 0 := IsLocalMax.hasDerivAt_eq_zero hmax (φ.hasFDerivAt.comp_hasDerivAt t₀ hγ)
  -- the velocity is parallel to the line: `det(d, v) = 0`
  have hdv : det2 d v = 0 := by
    have h0 := hasDerivAt_pi.1 hγ 0
    have h1 := hasDerivAt_pi.1 hγ 1
    have hD : HasDerivAt (fun t ↦ det2 d (γ t - p)) (det2 d v) t₀ := by
      simp only [det2, Pi.sub_apply]
      exact ((h1.sub_const (p 1)).const_mul (d 0)).sub ((h0.sub_const (p 0)).const_mul (d 1))
    have hD0 : HasDerivAt (fun t ↦ det2 d (γ t - p)) 0 t₀ :=
      (hasDerivAt_const t₀ (0 : ℝ)).congr_of_eventuallyEq hline
    exact hD.unique hD0
  -- `φ = μ det(d, ·)`
  set a₀ := φ (Pi.single 0 1)
  set a₁ := φ (Pi.single 1 1)
  have hφx : ∀ x : Fin 2 → ℝ, φ x = a₀ * x 0 + a₁ * x 1 := by
    intro x
    have hx : x = x 0 • (Pi.single 0 1 : Fin 2 → ℝ) + x 1 • Pi.single 1 1 := by
      ext k; fin_cases k <;> simp
    conv_lhs => rw [hx]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_comm (x 0), mul_comm (x 1)]
  have hφd : a₀ * d 0 + a₁ * d 1 = 0 := by
    rw [hφx] at hφv
    simp only [det2] at hdv
    by_cases hv0 : v 0 = 0
    · have hv1 : v 1 ≠ 0 := fun h ↦ hv (by ext k; fin_cases k <;> simp [hv0, h])
      refine (mul_left_inj' hv1).1 ?_
      linear_combination d 1 * hφv + a₀ * hdv
    · refine (mul_left_inj' hv0).1 ?_
      linear_combination d 0 * hφv - a₁ * hdv
  have hd2 := sm_ne_zero_of_det2 hd
  set μ := (a₁ * d 0 - a₀ * d 1) / (d 0 ^ 2 + d 1 ^ 2) with hμ
  have hφμ : ∀ x, φ x = μ * det2 d x := by
    intro x
    have e : φ x * (d 0 ^ 2 + d 1 ^ 2) = (a₁ * d 0 - a₀ * d 1) * det2 d x := by
      rw [hφx, det2]
      linear_combination (d 0 * x 0 + d 1 * x 1) * hφd
    rw [hμ, div_mul_eq_mul_div, eq_div_iff hd2.ne', e]
  refine ⟨μ, fun h0 ↦ ?_, fun x hx ↦ ?_⟩
  · obtain ⟨y, hy⟩ := hKi
    have := hφ y hy
    rw [hφμ, hφμ, h0, zero_mul, zero_mul] at this
    exact lt_irrefl _ this
  · have hγp : det2 d (γ t₀ - p) = 0 := hline.self_of_nhds
    have h1 := hle x hx
    rw [hφμ, hφμ] at h1
    rw [sm_det2_sub] at hγp ⊢
    linear_combination h1 + μ * hγp

/-- From `P x = r d` with `r ≠ 0`, `d ≠ 0`: `x = (r/P) d`. -/
private lemma sm_eq_smul_of_smul {P r : ℝ} {x d : Fin 2 → ℝ} (hd : d ≠ 0) (hr : r ≠ 0)
    (h : P • x = r • d) : x = (r / P) • d := by
  have hP : P ≠ 0 := by
    rintro rfl
    rw [zero_smul] at h
    exact (smul_ne_zero hr hd) h.symm
  rw [div_eq_inv_mul, mul_smul, ← h, smul_smul, inv_mul_cancel₀ hP, one_smul]

private lemma sm_le_of_mul {μ X : ℝ} (h : μ * X ≤ 0) : (0 < μ → X ≤ 0) ∧ (μ < 0 → 0 ≤ X) :=
  ⟨fun hμ ↦ by nlinarith, fun hμ ↦ by nlinarith⟩

/-- The sign bookkeeping of the parallel case: two parallel supporting lines at levels `A`, `B`
of `det(d₁, ·)` with `σ_i = σ_{i-1} + σ_{i+1}` force `A + B = 0`. -/
private lemma sm_sign_cases {μ₁ μ₂ A B : ℝ} (h1 : μ₁ ≠ 0) (h2 : μ₂ ≠ 0)
    (i1 : μ₁ * (-A - A) ≤ 0) (i2 : μ₁ * B ≤ 0) (i3 : μ₁ * (-B - A) ≤ 0)
    (j1 : μ₂ * (-B - B) ≤ 0) (j2 : μ₂ * A ≤ 0) (j3 : μ₂ * (-A - B) ≤ 0) : A + B = 0 := by
  have f1 := sm_le_of_mul i1
  have f2 := sm_le_of_mul i2
  have f3 := sm_le_of_mul i3
  have f4 := sm_le_of_mul j1
  have f5 := sm_le_of_mul j2
  have f6 := sm_le_of_mul j3
  rcases h1.lt_or_gt with h1 | h1 <;> rcases h2.lt_or_gt with h2 | h2
  · linarith [f1.2 h1, f2.2 h1, f3.2 h1, f4.2 h2, f5.2 h2, f6.2 h2]
  · linarith [f1.2 h1, f2.2 h1, f3.2 h1, f4.1 h2, f5.1 h2, f6.1 h2]
  · linarith [f1.1 h1, f2.1 h1, f3.1 h1, f4.2 h2, f5.2 h2, f6.2 h2]
  · linarith [f1.1 h1, f2.1 h1, f3.1 h1, f4.1 h2, f5.1 h2, f6.1 h2]

/-- **`P_K` is a parallelogram** (step 1 of the proof of Lemma 3.1.8; this fills a gap of the
book, which takes `P_K` to be a parallelogram): the lines `L₁`, `L₂` along which `σ_{i-1}` and
`σ_{i+1}` move are not parallel. Each line contains an arc of `∂K`, so it supports `K`
(Hahn–Banach at the boundary point and Fermat at an interior time, `sm_support`). If the lines
were parallel, the support inequalities at `±σ_{i-1}, ±σ_{i+1}, σ_i ∈ K` would force `σ_i` onto
the line through `0` parallel to `L₁`, where `det(σ_{i-1}, σ_i) = √3/2` pins it to one point:
`σ_i` would be constant, contradicting regularity. -/
private lemma hyp_lines_not_parallel {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K)
    {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {tf : ℝ} (hσ : IsMultiCurve 1 σ tf)
    (hbd : ∀ j, ∀ t ∈ Set.Icc 0 tf, σ j t ∈ frontier K)
    (hreg : ∀ j, ∀ t ∈ Set.Icc 0 tf, derivWithin (σ j) (Set.Icc 0 tf) t ≠ 0)
    (i : ZMod 6) {a b : ℝ} (hab : a < b) (ha : 0 ≤ a) (hb : b ≤ tf)
    {p₁ d₁ p₂ d₂ : Fin 2 → ℝ} (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0)
    (h₁ : ∀ t ∈ Set.Icc a b, det2 d₁ (σ (i - 1) t - p₁) = 0)
    (h₂ : ∀ t ∈ Set.Icc a b, det2 d₂ (σ (i + 1) t - p₂) = 0) : det2 d₁ d₂ ≠ 0 := by
  obtain ⟨hKc, hKcpt, hKi, hKs⟩ := hK
  have hsub : Icc a b ⊆ Icc 0 tf := Icc_subset_Icc ha hb
  have hmp : ∀ t ∈ Icc a b, _ := fun t ht ↦ hyp_mp_at (hσ.2 t (hsub ht)) i
  have hK_of : ∀ j, ∀ t ∈ Icc 0 tf, σ j t ∈ K := fun j t ht ↦
    hKcpt.isClosed.frontier_subset (hbd j t ht)
  set t₀ := (a + b) / 2 with ht₀def
  have ht₀ : t₀ ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have ht₀' : t₀ ∈ Icc 0 tf := hsub (Ioo_subset_Icc_self ht₀)
  have hab0 : t₀ ∈ Icc a b := Ioo_subset_Icc_self ht₀
  have hIab : Icc a b ∈ 𝓝 t₀ := Icc_mem_nhds ht₀.1 ht₀.2
  have hI0 : Icc 0 tf ∈ 𝓝 t₀ := Filter.mem_of_superset hIab hsub
  have hder : ∀ j, HasDerivAt (σ j) (derivWithin (σ j) (Icc 0 tf) t₀) t₀ := by
    intro j
    have hd : DifferentiableAt ℝ (σ j) t₀ :=
      (((hσ.1 j).differentiableOn (by norm_num)) t₀ ht₀').differentiableAt hI0
    rw [derivWithin_of_mem_nhds hI0]
    exact hd.hasDerivAt
  have hP₁ : ∀ t ∈ Icc a b, det2 d₁ (σ (i - 1) t) = det2 d₁ p₁ := fun t ht ↦ by
    have := h₁ t ht; rw [sm_det2_sub] at this; linarith
  have hP₂ : ∀ t ∈ Icc a b, det2 d₂ (σ (i + 1) t) = det2 d₂ p₂ := fun t ht ↦ by
    have := h₂ t ht; rw [sm_det2_sub] at this; linarith
  intro hD
  have hfr : ∀ j, σ j t₀ ∉ interior K := fun j h ↦ (hbd j t₀ ht₀').2 h
  have hevK : ∀ j, ∀ᶠ t in 𝓝 t₀, σ j t ∈ K := fun j ↦
    Filter.mem_of_superset hI0 fun t ht ↦ hK_of j t ht
  -- both lines support `K` (they contain arcs of the boundary)
  obtain ⟨μ₁, hμ₁, hs₁⟩ := sm_support hKc hKi (hder (i - 1)) (hreg _ _ ht₀') (hevK _)
    (hfr _) hd₁ (Filter.mem_of_superset hIab fun t ht ↦ h₁ t ht)
  obtain ⟨μ₂, hμ₂, hs₂⟩ := sm_support hKc hKi (hder (i + 1)) (hreg _ _ ht₀') (hevK _)
    (hfr _) hd₂ (Filter.mem_of_superset hIab fun t ht ↦ h₂ t ht)
  -- `det(d₂, ·) = κ det(d₁, ·)`
  have hd₁2 := sm_ne_zero_of_det2 hd₁
  set κ := (d₁ 0 * d₂ 0 + d₁ 1 * d₂ 1) / (d₁ 0 ^ 2 + d₁ 1 ^ 2) with hκ
  have hκx : ∀ x, det2 d₂ x = κ * det2 d₁ x := by
    intro x
    have e : det2 d₂ x * (d₁ 0 ^ 2 + d₁ 1 ^ 2) = (d₁ 0 * d₂ 0 + d₁ 1 * d₂ 1) * det2 d₁ x := by
      simp only [det2] at hD ⊢
      linear_combination (-(d₁ 0 * x 0) - d₁ 1 * x 1) * hD
    rw [hκ, div_mul_eq_mul_div, eq_div_iff hd₁2.ne', e]
  have hκ0 : κ ≠ 0 := by
    intro h0
    apply hd₂
    have e0 := hκx (Pi.single 0 1)
    have e1 := hκx (Pi.single 1 1)
    simp [det2, h0] at e0 e1
    ext k; fin_cases k <;> simp [e0, e1]
  -- the values of `det(d₁, ·)` at the multi-point
  obtain ⟨hs, -, -⟩ := hmp t₀ hab0
  have hu := hP₁ t₀ hab0
  have hw : det2 d₂ p₂ = κ * det2 d₁ (σ (i + 1) t₀) := by rw [← hP₂ t₀ hab0, hκx]
  have hmemK : ∀ j, σ j t₀ ∈ K := fun j ↦ hK_of j t₀ ht₀'
  have i1 := hs₁ _ (hKs _ (hmemK (i - 1)))
  have i2 := hs₁ _ (hmemK i)
  have i3 := hs₁ _ (hKs _ (hmemK (i + 1)))
  have j1 := hs₂ _ (hKs _ (hmemK (i + 1)))
  have j2 := hs₂ _ (hmemK i)
  have j3 := hs₂ _ (hKs _ (hmemK (i - 1)))
  rw [sm_det2_sub, sm_det2_neg, hu] at i1
  rw [sm_det2_sub, hs, sm_det2_add, hu] at i2
  rw [sm_det2_sub, sm_det2_neg] at i3
  rw [sm_det2_sub, sm_det2_neg, hw, hκx] at j1
  rw [sm_det2_sub, hw, hs, hκx, sm_det2_add, hu] at j2
  rw [sm_det2_sub, sm_det2_neg, hw, hκx, hu] at j3
  have hAB : det2 d₁ p₁ + det2 d₁ (σ (i + 1) t₀) = 0 :=
    sm_sign_cases hμ₁ (mul_ne_zero hμ₂ hκ0) i1 (by convert i2 using 1; ring) i3
      (by convert j1 using 1; ring) (by convert j2 using 1; ring) (by convert j3 using 1; ring)
  -- so `σ_i` lies on the line through `0` parallel to `L₁`, and is constant
  have hconst : ∀ t ∈ Icc a b, σ i t = (-(√3 / 2) / det2 d₁ p₁) • d₁ := by
    intro t ht
    obtain ⟨hs', hdet, -⟩ := hmp t ht
    have hwt : det2 d₁ (σ (i + 1) t) = det2 d₁ (σ (i + 1) t₀) := by
      have := hP₂ t ht
      rw [hκx, ← hP₂ t₀ hab0, hκx] at this
      exact mul_left_cancel₀ hκ0 this
    have hv0 : det2 d₁ (σ i t) = 0 := by rw [hs', sm_det2_add, hP₁ t ht, hwt, hAB]
    have hcr := sm_cramer d₁ (σ (i - 1) t) (σ i t)
    rw [hP₁ t ht, sm_det2_comm (σ i t), hdet, hv0, zero_smul, add_zero] at hcr
    exact sm_eq_smul_of_smul hd₁ (neg_ne_zero.2 (by positivity)) hcr
  exact hreg i t₀ ht₀' (sm_derivWithin_eq_zero hIab hconst)

/-- **The hyperbola is nondegenerate** (step 5 of the proof of Lemma 3.1.8; this fills a gap of
the book, which does not show `c ≠ 0`): if `det(d₁, σ_i - p₁) det(d₂, σ_i - p₂) = c` on `[a, b]`,
then `c ≠ 0`. Otherwise, for each `t` one factor vanishes; the two zero sets are closed and cover
`[a, b]`, so one has interior points, and there `σ_{i+1}` (resp. `σ_{i-1}`) lies on the line
through `0` parallel to `L₁` (resp. `L₂`), hence is constant, contradicting regularity. -/
private lemma hyp_const_ne_zero {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {tf : ℝ}
    (hσ : IsMultiCurve 1 σ tf)
    (hreg : ∀ j, ∀ t ∈ Set.Icc 0 tf, derivWithin (σ j) (Set.Icc 0 tf) t ≠ 0)
    (i : ZMod 6) {a b : ℝ} (hab : a < b) (ha : 0 ≤ a) (hb : b ≤ tf)
    {p₁ d₁ p₂ d₂ : Fin 2 → ℝ} (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0)
    (h₁ : ∀ t ∈ Set.Icc a b, det2 d₁ (σ (i - 1) t - p₁) = 0)
    (h₂ : ∀ t ∈ Set.Icc a b, det2 d₂ (σ (i + 1) t - p₂) = 0) {c : ℝ}
    (hid : ∀ t ∈ Set.Icc a b, det2 d₁ (σ i t - p₁) * det2 d₂ (σ i t - p₂) = c) : c ≠ 0 := by
  intro hc0
  have hsub : Icc a b ⊆ Icc 0 tf := Icc_subset_Icc ha hb
  have hmp : ∀ t ∈ Icc a b, _ := fun t ht ↦ hyp_mp_at (hσ.2 t (hsub ht)) i
  have hP₁ : ∀ t ∈ Icc a b, det2 d₁ (σ (i - 1) t) = det2 d₁ p₁ := fun t ht ↦ by
    have := h₁ t ht; rw [sm_det2_sub] at this; linarith
  have hP₂ : ∀ t ∈ Icc a b, det2 d₂ (σ (i + 1) t) = det2 d₂ p₂ := fun t ht ↦ by
    have := h₂ t ht; rw [sm_det2_sub] at this; linarith
  -- a regular curve is not constant near a time of `[0, t_f]`
  have hnc : ∀ j (U : Set ℝ) (t₁ : ℝ), U ∈ 𝓝 t₁ → t₁ ∈ Icc 0 tf → ∀ C : Fin 2 → ℝ,
      (∀ t ∈ U, σ j t = C) → False := fun j U t₁ hU ht₁ C hC ↦
    hreg j t₁ ht₁ (sm_derivWithin_eq_zero hU hC)
  have hσc : ∀ j, ContinuousOn (σ j) (Icc a b) := fun j ↦ (hσ.1 j).continuousOn.mono hsub
  have hcont : ∀ (d p : Fin 2 → ℝ), ContinuousOn (fun t ↦ det2 d (σ i t - p)) (Icc a b) := by
    intro d p
    have h0 : ContinuousOn (fun t ↦ σ i t 0) (Icc a b) :=
      (continuous_apply 0).comp_continuousOn (hσc i)
    have h1 : ContinuousOn (fun t ↦ σ i t 1) (Icc a b) :=
      (continuous_apply 1).comp_continuousOn (hσc i)
    simp only [det2, Pi.sub_apply]
    exact ((h1.sub continuousOn_const).const_smul (d 0)).sub
      ((h0.sub continuousOn_const).const_smul (d 1))
  set Z₁ := Icc a b ∩ (fun t ↦ det2 d₁ (σ i t - p₁)) ⁻¹' {0} with hZ₁
  set Z₂ := Icc a b ∩ (fun t ↦ det2 d₂ (σ i t - p₂)) ⁻¹' {0} with hZ₂
  have hZ₁c : IsClosed Z₁ :=
    (hcont d₁ p₁).preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hunion : Z₁ ∪ Z₂ = Icc a b := by
    ext t
    refine ⟨fun h ↦ h.elim (fun h ↦ h.1) (fun h ↦ h.1), fun ht ↦ ?_⟩
    rcases mul_eq_zero.1 ((hid t ht).trans hc0) with h | h
    exacts [Or.inl ⟨ht, h⟩, Or.inr ⟨ht, h⟩]
  have hZ₁i : interior Z₁ = ∅ := by
    by_contra hne
    obtain ⟨t₁, ht₁⟩ := Set.nonempty_iff_ne_empty.2 hne
    refine hnc (i + 1) (interior Z₁) t₁ (isOpen_interior.mem_nhds ht₁)
      (hsub (interior_subset ht₁).1) ((-(√3 / 2) / det2 d₁ p₁) • d₁) fun t ht ↦ ?_
    obtain ⟨htab, hG⟩ := interior_subset ht
    simp only [mem_preimage, mem_singleton_iff] at hG
    obtain ⟨hs', -, hdet⟩ := hmp t htab
    have hw0 : det2 d₁ (σ (i + 1) t) = 0 := by
      rw [sm_det2_sub, hs', sm_det2_add, hP₁ t htab] at hG; linarith
    have hcr := sm_cramer d₁ (σ (i - 1) t) (σ (i + 1) t)
    rw [hP₁ t htab, sm_det2_comm (σ (i + 1) t), hdet, hw0, zero_smul, add_zero] at hcr
    exact sm_eq_smul_of_smul hd₁ (neg_ne_zero.2 (by positivity)) hcr
  have hZ₂i : interior Z₂ = ∅ := by
    by_contra hne
    obtain ⟨t₁, ht₁⟩ := Set.nonempty_iff_ne_empty.2 hne
    refine hnc (i - 1) (interior Z₂) t₁ (isOpen_interior.mem_nhds ht₁)
      (hsub (interior_subset ht₁).1) ((√3 / 2 / det2 d₂ p₂) • d₂) fun t ht ↦ ?_
    obtain ⟨htab, hG⟩ := interior_subset ht
    simp only [mem_preimage, mem_singleton_iff] at hG
    obtain ⟨hs', -, hdet⟩ := hmp t htab
    have hu0 : det2 d₂ (σ (i - 1) t) = 0 := by
      rw [sm_det2_sub, hs', sm_det2_add, hP₂ t htab] at hG; linarith
    have hcr := sm_cramer d₂ (σ (i + 1) t) (σ (i - 1) t)
    rw [hP₂ t htab, hdet, hu0, zero_smul, add_zero] at hcr
    exact sm_eq_smul_of_smul hd₂ (by positivity) hcr
  have ht₀ : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have h := interior_union_isClosed_of_interior_empty hZ₁c hZ₂i
  rw [hunion, interior_Icc, hZ₁i] at h
  exact (h ▸ ht₀ : (a + b) / 2 ∈ (∅ : Set ℝ))

/-- A curve moving along the line `hyp_line d p` during `[a, b]` has velocity parallel to `d`
there (one-sided at the ends of `[a, b]`). -/
private lemma hyp_det2_vel_eq_zero {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {tf : ℝ}
    (hσ : IsMultiCurve 1 σ tf) {a b : ℝ} (hab : a < b) (ha : 0 ≤ a) (hb : b ≤ tf) {j : ZMod 6}
    {d p : Fin 2 → ℝ} (h : ∀ t ∈ Set.Icc a b, det2 d (σ j t - p) = 0) {t : ℝ}
    (ht : t ∈ Icc a b) : det2 d (hyp_vel σ tf j t) = 0 := by
  have hsub : Icc a b ⊆ Icc 0 tf := Icc_subset_Icc ha hb
  have hd := (hyp_hasDerivWithinAt_vel hσ (hsub ht) j).mono hsub
  have h1 := hyp_hasDerivWithinAt_det2 (hasDerivWithinAt_const t (Icc a b) d) (hd.sub_const p)
  have h2 : HasDerivWithinAt (fun x ↦ det2 d (σ j x - p)) 0 (Icc a b) t :=
    (hasDerivWithinAt_const t _ 0).congr_of_mem h ht
  have := (uniqueDiffOn_Icc hab t ht).eq_deriv _ h1 h2
  simpa [det2] using this

set_option linter.unusedVariables false in
/-- **Lemma 3.1.8** (`lem:hyp-arc`). Suppose that `K ∈ 𝔎_ccs` and that the boundary of `K` is
parametrized by a `C¹` multi-curve `σ`. If two curves `σ_{i-1}` and `σ_{i+1}` move along straight
lines during some time interval, then the third curve `σ_i` moves along a hyperbolic arc, whose
asymptotes are the lines determined by `σ_{i-1}` and `σ_{i+1}`.

Reading. "The boundary is parametrized by a `C¹` multi-curve" is read, as in §2.4 (TeX 1944–1947:
"we can parameterize the boundary by a regular `C¹` curve"), as: `σ` is a `C¹` multi-curve on
`[0, t_f]` (Definition 2.4.1), every `σ_j(t)` lies on the boundary of `K`, the arcs
`σ_j([0, t_f])` cover the boundary, and the curves are regular (`σ_j' ≠ 0`). The time interval is
`[a, b] ⊆ [0, t_f]` with `a < b`; `σ_{i-1}` moves along the line `L₁` through `p₁` with direction
`d₁ ≠ 0`, and `σ_{i+1}` along the line `L₂` through `p₂` with direction `d₂ ≠ 0` (regular curves
are not constant, so these are the lines determined by `σ_{i-1}` and `σ_{i+1}`).
The conclusion: the lines are not parallel, and `σ_i([a, b])` lies on one hyperbola
`det(d₁, x - p₁) · det(d₂, x - p₂) = c`, `c ≠ 0`, with asymptotes `L₁` and `L₂`.

Without regularity the statement is false: for the square `[-λ, λ]²`, `λ² = √3/2`, the boundary
has a `C¹` multi-curve in which `σ₂ = (-λ, 0)` is constant while `σ₁` and `σ₃ = -σ₀` slide along
the parallel edge lines `y = λ` and `y = -λ`; no hyperbola has parallel asymptotes.

Proof: the book's argument. Areas are the signed areas `hyp_area` of the polygons with the listed
vertices (shoelace formula); for a convex polygon listed counterclockwise, which the book takes
`P_K` and `H_K(t)` to be, this is the area, and the book's area bookkeeping holds verbatim for
signed areas, with no convexity needed.
1. The lines `±L₁`, `±L₂` traced by `±σ_{i-1}`, `±σ_{i+1}` bound a parallelogram `P_K` with
   vertices `-R, O, R, -O`, where `O = L₁ ∩ L₂` and `R = L₂ ∩ (-L₁)`. That `L₁` and `L₂` are not
   parallel is not shown in the book, which takes `P_K` to be a parallelogram; the gap is filled
   by `hyp_lines_not_parallel`.
2. At each time `t ∈ [a, b]`, the tangent lines at `σ_{i-1}(t)`, `σ_{i+1}(t)`, `σ_{i+2}(t)` are
   `L₁`, `L₂`, `-L₁` (`hyp_line_eq`, as `σ_{i-1}`, `σ_{i+1}` move along these lines), so the
   hexagon `H_K(t)` cut out by the six tangent lines (`hyp_hexagon`) has the vertices
   `P(t) ∈ L₁ ∩ T(t)`, `Q(t) ∈ T(t) ∩ L₂`, `R`, `-P(t)`, `-Q(t)`, `-R`, where `T(t)` is the tangent
   line at `σ_i(t)`; four of its edges lie on the edge lines of `P_K`, the other two on `±T(t)`,
   and `±σ_i(t)` are the midpoints of these two (`hyp_midpoint_hexagon`).
3. The area of `P_K` does not depend on `t`, and the area of `H_K(t)` is `√12`
   (`hyp_area_hexagon`), so the area `A` of the triangle `O, Q(t), P(t)` cut off from `P_K` by
   `T(t)` is constant: `area(P_K) = √12 + 2A` (`hyp_area_cut`).
4. By Reinhardt's observation (`hyp_reinhardt_midpoint`), the midpoint `σ_i(t)` of `P(t)Q(t)`
   lies on the hyperbola `det(d₁, x - O) det(d₂, x - O) = c = det(d₁, d₂) A / 2` with asymptotes
   `L₁`, `L₂`.
5. `c ≠ 0`, i.e. the hyperbola is nondegenerate: not shown in the book; the gap is filled by
   `hyp_const_ne_zero`.

The hypothesis `hcover` (the arcs cover `∂K`, part of "the boundary is parametrized by `σ`") is
not used by the proof; it is kept because it is part of the book's hypothesis. -/
theorem lemma3_1_8 {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {σ : ZMod 6 → ℝ → Fin 2 → ℝ}
    {tf : ℝ} (hσ : IsMultiCurve 1 σ tf) (hbd : ∀ j, ∀ t ∈ Set.Icc 0 tf, σ j t ∈ frontier K)
    (hcover : (⋃ j, σ j '' Set.Icc 0 tf) = frontier K)
    (hreg : ∀ j, ∀ t ∈ Set.Icc 0 tf, derivWithin (σ j) (Set.Icc 0 tf) t ≠ 0)
    (i : ZMod 6) {a b : ℝ} (hab : a < b) (ha : 0 ≤ a) (hb : b ≤ tf)
    {p₁ d₁ p₂ d₂ : Fin 2 → ℝ} (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0)
    (h₁ : ∀ t ∈ Set.Icc a b, det2 d₁ (σ (i - 1) t - p₁) = 0)
    (h₂ : ∀ t ∈ Set.Icc a b, det2 d₂ (σ (i + 1) t - p₂) = 0) :
    det2 d₁ d₂ ≠ 0 ∧ ∃ c : ℝ, c ≠ 0 ∧ ∀ t ∈ Set.Icc a b,
      det2 d₁ (σ i t - p₁) * det2 d₂ (σ i t - p₂) = c := by
  have hsub : Icc a b ⊆ Icc 0 tf := Icc_subset_Icc ha hb
  have htf : 0 < tf := by linarith
  -- 1. `P_K` is a parallelogram, with vertices `-R, O, R, -O`
  have hD : det2 d₁ d₂ ≠ 0 := hyp_lines_not_parallel hK hσ hbd hreg i hab ha hb hd₁ hd₂ h₁ h₂
  have hD' : det2 d₂ d₁ ≠ 0 := by rw [sm_det2_comm]; exact neg_ne_zero.2 hD
  set O := hyp_lineInter d₁ p₁ d₂ p₂
  set R := hyp_lineInter d₂ p₂ d₁ (-p₁)
  have hO₁ : O ∈ hyp_line d₁ p₁ := hyp_lineInter_mem_left hD
  have hO₂ : O ∈ hyp_line d₂ p₂ := hyp_lineInter_mem_right hD
  have hR₂ : R ∈ hyp_line d₂ p₂ := hyp_lineInter_mem_left hD'
  have hR₁ : -R ∈ hyp_line d₁ p₁ := by
    have h := hyp_lineInter_mem_right (p := p₂) (q := -p₁) hD'
    rw [hyp_mem_line, sub_neg_eq_add] at h
    rw [hyp_mem_line, show -R - p₁ = -(R + p₁) by abel, sm_det2_neg, h, neg_zero]
  -- 2.–3. at each time `t`, the hexagon `H_K(t)` and the area cut off from `P_K`
  have hstep : ∀ t ∈ Icc a b, σ i t = midpoint ℝ (hyp_hexagon σ tf t (i + 1))
      (hyp_hexagon σ tf t i) ∧ hyp_hexagon σ tf t i ∈ hyp_line d₁ O ∧
      hyp_hexagon σ tf t (i + 1) ∈ hyp_line d₂ O ∧
      hyp_area [O, hyp_hexagon σ tf t (i + 1), hyp_hexagon σ tf t i] =
        (hyp_area [-R, O, R, -O] - √12) / 2 := by
    intro t ht
    have ht' := hsub ht
    -- `σ_{i+2} = -σ_{i-1}` and `σ_{i+2}' = -σ_{i-1}'`
    obtain ⟨-, hs3, -⟩ := hyp_mp (hσ.2 t ht') (i - 1)
    obtain ⟨-, hv3, -⟩ := hyp_vel_rel hσ htf ht' (i - 1)
    have e2 : i - 1 + 2 = i + 1 := by ring
    rw [show i - 1 + 3 = i + 2 by ring] at hs3 hv3
    -- the velocities of `σ_{i-1}`, `σ_{i+1}` are parallel to `d₁`, `d₂` and not parallel
    have hu₁ := hyp_det2_vel_eq_zero hσ hab ha hb h₁ ht
    have hw₂ := hyp_det2_vel_eq_zero hσ hab ha hb h₂ ht
    have hu0 : hyp_vel σ tf (i - 1) t ≠ 0 := hreg _ _ ht'
    have hw0 : hyp_vel σ tf (i + 1) t ≠ 0 := hreg _ _ ht'
    have hX : ∀ j, det2 (hyp_vel σ tf j t) (hyp_vel σ tf (j + 2) t) ≠ 0 := by
      intro j
      rw [hyp_det2_vel_eq hσ htf ht' (i - 1) j, e2]
      exact hyp_det2_ne_zero_of_parallel hD hu0 hw0 hu₁ hw₂
    -- the tangent lines at `σ_{i-1}(t)`, `σ_{i+1}(t)`, `σ_{i+2}(t)` are `L₁`, `L₂`, `-L₁`
    have hT₁ : hyp_line (hyp_vel σ tf (i - 1) t) (σ (i - 1) t) = hyp_line d₁ p₁ :=
      hyp_line_eq hd₁ hu0 hu₁ (h₁ t ht)
    have hT₂ : hyp_line (hyp_vel σ tf (i + 1) t) (σ (i + 1) t) = hyp_line d₂ p₂ :=
      hyp_line_eq hd₂ hw0 hw₂ (h₂ t ht)
    have hT₃ : hyp_line (hyp_vel σ tf (i + 2) t) (σ (i + 2) t) = hyp_line d₁ (-p₁) := by
      rw [hv3, hs3]
      refine hyp_line_eq hd₁ (neg_ne_zero.2 hu0) (by rw [sm_det2_neg, hu₁, neg_zero]) ?_
      rw [hyp_mem_line, show -σ (i - 1) t - -p₁ = -(σ (i - 1) t - p₁) by abel, sm_det2_neg,
        h₁ t ht, neg_zero]
    -- the vertices `P(t) = H_K(t)_i ∈ L₁`, `Q(t) = H_K(t)_{i+1} ∈ L₂` and `H_K(t)_{i+2} = R`
    have hP := (hyp_hexagon_mem_tangent hσ htf ht' hX i).1
    have hQ := (hyp_hexagon_mem_tangent hσ htf ht' hX (i + 1)).1
    have hR' := hyp_hexagon_mem_tangent hσ htf ht' hX (i + 2)
    rw [show i + 1 - 1 = i by ring] at hQ
    rw [hT₁] at hP
    rw [show i + 2 - 1 = i + 1 by ring, hT₂] at hR'
    rw [hT₃] at hR'
    have hRt : hyp_hexagon σ tf t (i + 2) = R := by
      have h := hR'.2.1
      rw [hyp_mem_line, sub_neg_eq_add] at h
      exact hyp_eq_lineInter hD' hR'.1 (by rw [hyp_mem_line, sub_neg_eq_add]; exact h)
    have hQ₂ : hyp_hexagon σ tf t (i + 1) ∈ hyp_line d₂ p₂ := by
      rw [← hT₂]; exact (hyp_hexagon_mem_tangent hσ htf ht' hX (i + 1)).2.1
    -- `σ_i(t)` is the midpoint of the edge `P(t)Q(t)` on the tangent line at `σ_i(t)`, and
    -- `area(H_K(t)) = area(P(t), Q(t), R, -P(t), -Q(t), -R) = √12`
    have hmid := hyp_midpoint_hexagon hσ htf ht' hX i
    have harea := hyp_area_hexagon hσ htf ht' hX i
    rw [show i + 4 = i + 1 + 3 by ring, show i + 5 = i + 2 + 3 by ring,
      hyp_hexagon_add_three hσ htf ht', hyp_hexagon_add_three hσ htf ht',
      hyp_hexagon_add_three hσ htf ht', hRt] at harea
    have hcut := hyp_area_cut (O := O) (R := R) (P := hyp_hexagon σ tf t i)
      (Q := hyp_hexagon σ tf t (i + 1)) (hyp_area_eq_zero_of_mem_line hd₁ hR₁ hP hO₁)
      (hyp_area_eq_zero_of_mem_line hd₂ hO₂ hQ₂ hR₂)
    refine ⟨by rw [midpoint_comm, hmid], hyp_mem_line_of_mem hO₁ hP,
      hyp_mem_line_of_mem hO₂ hQ₂, ?_⟩
    -- the area cut off from `P_K` is `A = (area(P_K) - area(H_K(t)))/2`
    rw [hcut, harea]
    ring
  -- 4. Reinhardt: the midpoints `σ_i(t)` lie on one hyperbola with asymptotes `L₁`, `L₂`
  set c := det2 d₁ d₂ * ((hyp_area [-R, O, R, -O] - √12) / 2) / 2 with hc
  have hid : ∀ t ∈ Icc a b, det2 d₁ (σ i t - p₁) * det2 d₂ (σ i t - p₂) = c := by
    intro t ht
    obtain ⟨hmid, hP, hQ, hA⟩ := hstep t ht
    have h := hyp_reinhardt_midpoint hQ hP
    rw [← hmid, hA] at h
    have e₁ : det2 d₁ (σ i t - p₁) = det2 d₁ (σ i t - O) := by
      have h' := hO₁
      rw [hyp_mem_line, sm_det2_sub] at h'
      rw [sm_det2_sub, sm_det2_sub]; linarith
    have e₂ : det2 d₂ (σ i t - p₂) = det2 d₂ (σ i t - O) := by
      have h' := hO₂
      rw [hyp_mem_line, sm_det2_sub] at h'
      rw [sm_det2_sub, sm_det2_sub]; linarith
    rw [e₁, e₂, mul_comm (det2 d₁ _), h, hc, sm_det2_comm d₂ d₁]
    ring
  -- 5. the hyperbola is nondegenerate
  exact ⟨hD, c, hyp_const_ne_zero hσ hreg i hab ha hb hd₁ hd₂ h₁ h₂ hid, hid⟩

end SmoothedPolygons
