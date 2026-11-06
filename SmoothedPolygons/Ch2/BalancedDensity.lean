module

public import SmoothedPolygons.Ch2.Boundary

/-!
# The packing density of a balanced disk

The book computes the density of the smoothed octagon as `δ = area(K_oct)/√12` (the example before
Theorem 7.5.6), from Theorem 2.2.2 and the normalization `area(H_K) = √12` of §2.2. This file
states the general fact behind that computation: for every balanced pair `(K, σ)`,
`δ(K) = area(K)/√12` (`greatestPackingDensity_of_isBalancedPair`).

What the book claims. Theorem 2.2.2 gives `δ(K) = area(K)/area(H_K)` for a least-area centrally
symmetric circumscribed hexagon `H_K`. The book then *chooses* the scale `area(H_K) = √12` (§2.2)
and states that every minimizer `K_min` with this normalization is balanced (after
Definition 2.4.7); the normalization is how the factor `√3/2` enters the multi-point conditions
(`eqn:sqrt12`). It does not show the converse direction that the example uses: that a balanced
disk, such as the smoothed octagon, has `area(H_K) = √12`. The gap is filled by the argument
recorded in the helper lemmas below:

* the edge midpoints `m_j` of a least-area hexagon lie on the boundary of `K` (§2.2, stated in the
  book), and `area(H_K) = 4 det(m₀, m₁)` (`ch2_volume_hexagonOf`);
* the multi-point `σ(t)` with `σ₀(t) = m₀` gives a second inscribed configuration with the same
  first point; for a centrally symmetric convex disk, the value `det(u, p)` with `u, p, p - u` on
  the boundary and `det(u, p) > 0` depends only on `u` (`ch2_det2_eq_of_inscribed`: the chords
  parallel to `u` have concave, even length, which equals `|u|` at one height only), so
  `det(m₀, m₁) = det(σ₀(t), σ₁(t)) = √3/2` and `area(H_K) = 2√3 = √12`.
-/

@[expose] public section

namespace SmoothedPolygons

open MeasureTheory Set

/-- The edge midpoints of a centrally symmetric hexagon satisfy `m₁ - m₀ = m₂`. -/
lemma ch2_hexMidpoint_sub {v : ZMod 6 → Fin 2 → ℝ} (hv : IsCSHexagon v) :
    hexMidpoint v 1 - hexMidpoint v 0 = hexMidpoint v 2 := by
  have h3 : v 3 = -v 0 := by simpa using (hv 0).1
  have h21 : (2 : ZMod 6) + 1 = 3 := by decide
  have h11 : (1 : ZMod 6) + 1 = 2 := by decide
  simp only [hexMidpoint, midpoint_eq_smul_add, h21, h11, zero_add, h3]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, smul_eq_mul]
  ring

/-- The edge midpoints of a centrally symmetric hexagon turn counterclockwise:
`det(m₀, m₁) > 0`. -/
lemma ch2_det2_hexMidpoint_pos {v : ZMod 6 → Fin 2 → ℝ} (hv : IsCSHexagon v) :
    0 < det2 (hexMidpoint v 0) (hexMidpoint v 1) := by
  have h3 : v 3 = -v 0 := by simpa using (hv 0).1
  have h01 := (hv 0).2.1
  have h12 := (hv 1).2.1
  have h23 := (hv 2).2.1
  have h21 : (2 : ZMod 6) + 1 = 3 := by decide
  have h11 : (1 : ZMod 6) + 1 = 2 := by decide
  simp only [zero_add, h11, h21, h3] at h01 h12 h23
  simp only [hexMidpoint, midpoint_eq_smul_add, zero_add, h11]
  simp only [det2, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, smul_eq_mul, invOf_eq_inv] at *
  nlinarith [h01, h12, h23]

/-- The area of a centrally symmetric hexagon is `4 det(m₀, m₁)`, where `m₀, m₁` are the midpoints
of two consecutive edges (§2.2: `det(s_j, s_{j+1})` is a fixed fraction of `area(H_K)`). -/
lemma ch2_volume_hexagonOf {v : ZMod 6 → Fin 2 → ℝ} (hv : IsCSHexagon v) :
    volume.real (hexagonOf v) = 4 * det2 (hexMidpoint v 0) (hexMidpoint v 1) := by
  sorry

/-- The midpoints of the edges of a least-area centrally symmetric hexagon circumscribing `K` lie
on the boundary of `K` (§2.2, before Definition 2.2.3). -/
lemma ch2_hexMidpoint_mem_frontier {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K)
    {v : ZMod 6 → Fin 2 → ℝ} (hv : IsLeastAreaHexagon K v) (j : ZMod 6) :
    hexMidpoint v j ∈ frontier K := by
  sorry

/-- For a centrally symmetric convex disk `K` and a boundary point `u`, the value `det(u, p)`, for
`p` with `p` and `p - u` on the boundary and `det(u, p) > 0`, does not depend on `p`. -/
lemma ch2_det2_eq_of_inscribed {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {u p q : Fin 2 → ℝ}
    (hu : u ∈ frontier K) (hp : p ∈ frontier K) (hpu : p - u ∈ frontier K)
    (hq : q ∈ frontier K) (hqu : q - u ∈ frontier K) (hup : 0 < det2 u p) (huq : 0 < det2 u q) :
    det2 u p = det2 u q := by
  sorry

/-- The boundary of a balanced disk is a regular `C¹` closed curve, so a balanced disk is not a
parallelogram. -/
lemma ch2_not_isParallelogram_of_isBalancedPair {K : Set (Fin 2 → ℝ)}
    {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {tf : ℝ} (h : IsBalancedPair K σ tf) : ¬ IsParallelogram K := by
  sorry

/-- **The density of a balanced disk.** For every balanced pair `(K, σ)` (Definition 2.4.7), the
greatest packing density of `K` is `δ(K) = area(K)/√12`. This is the formula
`δ = area(K_oct)/√12` that the book applies to the smoothed octagon (the example before
Theorem 7.5.6). The book obtains it from Theorem 2.2.2 and the normalization `area(H_K) = √12`
(§2.2), which it imposes on `K_min`; for a general balanced disk the normalization is a
consequence, proved here by the argument of the module docstring. -/
theorem greatestPackingDensity_of_isBalancedPair {K : Set (Fin 2 → ℝ)}
    {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {tf : ℝ} (h : IsBalancedPair K σ tf) :
    greatestPackingDensity K = volume.real K / √12 := by
  have hK : IsCCSDisk K := h.1
  have hmulti : ∀ t, IsMultiPoint fun j ↦ σ j t := h.2.2.2.1
  have himage : ∀ j, σ j '' Ico 0 (6 * tf) = frontier K := h.2.2.2.2.2.2.2.2.2
  obtain ⟨⟨v, hv⟩, hδ⟩ := theorem2_2_2 hK (ch2_not_isParallelogram_of_isBalancedPair h)
  rw [hδ v hv, ch2_volume_hexagonOf hv.1]
  have hm : ∀ j, hexMidpoint v j ∈ frontier K := ch2_hexMidpoint_mem_frontier hK hv
  obtain ⟨t, ht, ht0⟩ : hexMidpoint v 0 ∈ σ 0 '' Ico 0 (6 * tf) := (himage 0).symm ▸ hm 0
  have hσ1 : σ 1 t ∈ frontier K := himage 1 ▸ mem_image_of_mem _ ht
  have hσ2 : σ 2 t ∈ frontier K := himage 2 ▸ mem_image_of_mem _ ht
  obtain ⟨h024, -, hdet⟩ := hmulti t 0
  have h41 : σ 4 t = -σ 1 t := (hmulti t 1).2.1
  simp only [zero_add] at h024 hdet
  have h21 : σ 1 t - σ 0 t = σ 2 t := by
    rw [h41] at h024
    rw [eq_comm, ← sub_eq_zero, ← h024]
    abel
  have heq := ch2_det2_eq_of_inscribed hK (hm 0) (hm 1) (ch2_hexMidpoint_sub hv.1 ▸ hm 2)
    (q := σ 1 t) hσ1 (ht0 ▸ h21 ▸ hσ2) (ch2_det2_hexMidpoint_pos hv.1)
    (ht0 ▸ hdet ▸ by positivity)
  rw [heq, ← ht0, hdet]
  congr 1
  rw [show (12 : ℝ) = 2 ^ 2 * 3 by norm_num, Real.sqrt_mul (by norm_num),
    Real.sqrt_sq (by norm_num)]
  ring

end SmoothedPolygons
