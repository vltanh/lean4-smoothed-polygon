module

public import SmoothedPolygons.Ch2.Reinhardt
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Centrally symmetric hexagons

Helper lemmas on the centrally symmetric hexagons of §2.2 (`IsCSHexagon`, `hexagonOf`,
`hexMidpoint`, defined in `SmoothedPolygons.Ch2.Reinhardt`), shared by §2.3 (Theorem 2.3.9,
`SmoothedPolygons.Ch2.Mahler`) and by the density of balanced disks
(`SmoothedPolygons.Ch2.BalancedDensity`).

The hexagon toolkit itself is in `SmoothedPolygons.Ch2.Reinhardt`. A centrally symmetric hexagon
is `rein_hex3 a b c`, with vertices `a, b, c, -a, -b, -c` (`rein_eq_hex3`); it is a convex
hexagon iff `rein_HexCond a b c` (`rein_isCSHexagon_iff_hexCond`); it is the intersection of three
strips (`rein_mem_hexagonOf_iff_strips`) and the union of the six triangles `[0, v_j, v_{j+1}]`,
so its area is `det(a, b) + det(b, c) + det(a, c)` (`rein_volume_hexagonOf_hex3`), which is
`4 det(m₀, m₁)` (`rein_volume_hexagonOf`). The edge midpoints of a least-area centrally symmetric
hexagon circumscribing `K` lie on the boundary of `K` (§2.2, stated in the book;
`rein_hexMidpoint_mem_frontier`), by the book's rotation argument (`rein_midpoint_mem_of_least`,
TeX ~1395–1400).

This file adds:

* `hex_volume_hexagonOf`: the area `4 det(m₀, m₁)` as a real number;
* `hex_hexMidpoint_sub`: `m₁ - m₀ = m₂`;
* `hex_volume_real_mk`: the area `det(a, b) + det(b, c) + det(a, c)` of `rein_hex3 a b c` as a
  real number, under `rein_HexCond a b c`;
* the linear map `hex_lin u w` with columns `u, w` (`hex_lin_apply`, `hex_det_lin`), and the
  additions of numerals in `ℤ/6ℤ` (`hex_zmod_facts`).
-/

@[expose] public section

namespace SmoothedPolygons

open MeasureTheory Set

/-- The edge midpoints of a centrally symmetric hexagon satisfy `m₁ - m₀ = m₂`. -/
lemma hex_hexMidpoint_sub {v : ZMod 6 → Fin 2 → ℝ} (hv : IsCSHexagon v) :
    hexMidpoint v 1 - hexMidpoint v 0 = hexMidpoint v 2 := by
  have h3 : v 3 = -v 0 := by simpa using (hv 0).1
  have h21 : (2 : ZMod 6) + 1 = 3 := by decide
  have h11 : (1 : ZMod 6) + 1 = 2 := by decide
  simp only [hexMidpoint, midpoint_eq_smul_add, h21, h11, zero_add, h3]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, smul_eq_mul]
  ring

/-- The linear map `p ↦ p₀ u + p₁ w`. -/
noncomputable def hex_lin (u w : Fin 2 → ℝ) : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
  Matrix.toLin' !![u 0, w 0; u 1, w 1]

lemma hex_lin_apply (u w p : Fin 2 → ℝ) : hex_lin u w p = p 0 • u + p 1 • w := by
  ext i
  fin_cases i <;> simp [hex_lin, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

lemma hex_det_lin (u w : Fin 2 → ℝ) : LinearMap.det (hex_lin u w) = det2 u w := by
  rw [hex_lin, LinearMap.det_toLin', Matrix.det_fin_two_of, det2]
  ring

/-- Additions of numerals in `ℤ/6ℤ`. -/
lemma hex_zmod_facts :
    (0 : ZMod 6) + 1 = 1 ∧ (1 : ZMod 6) + 1 = 2 ∧ (2 : ZMod 6) + 1 = 3 ∧ (3 : ZMod 6) + 1 = 4 ∧
    (4 : ZMod 6) + 1 = 5 ∧ (5 : ZMod 6) + 1 = 0 ∧ (0 : ZMod 6) + 2 = 2 ∧ (1 : ZMod 6) + 2 = 3 ∧
    (2 : ZMod 6) + 2 = 4 ∧ (3 : ZMod 6) + 2 = 5 ∧ (4 : ZMod 6) + 2 = 0 ∧ (5 : ZMod 6) + 2 = 1 ∧
    (0 : ZMod 6) + 3 = 3 ∧ (1 : ZMod 6) + 3 = 4 ∧ (2 : ZMod 6) + 3 = 5 ∧ (3 : ZMod 6) + 3 = 0 ∧
    (4 : ZMod 6) + 3 = 1 ∧ (5 : ZMod 6) + 3 = 2 := by decide

/-- The area of the hexagon `rein_hex3 a b c`, as a real number. -/
lemma hex_volume_real_mk {a b c : Fin 2 → ℝ} (h : rein_HexCond a b c) :
    volume.real (hexagonOf (rein_hex3 a b c)) = det2 a b + det2 b c + det2 a c :=
  rein_volume_real_hexagonOf_hex3 (rein_isCSHexagon_iff_hexCond.2 h)

/-- The area of a centrally symmetric hexagon is `4 det(m₀, m₁)`, where `m₀, m₁` are the midpoints
of two consecutive edges (§2.2: `det(s_j, s_{j+1})` is a fixed fraction of `area(H_K)`). -/
lemma hex_volume_hexagonOf {v : ZMod 6 → Fin 2 → ℝ} (hv : IsCSHexagon v) :
    volume.real (hexagonOf v) = 4 * det2 (hexMidpoint v 0) (hexMidpoint v 1) := by
  rw [measureReal_def, rein_volume_hexagonOf hv,
    ENNReal.toReal_ofReal (by linarith [rein_det2_hexMidpoint_pos hv])]

end SmoothedPolygons
