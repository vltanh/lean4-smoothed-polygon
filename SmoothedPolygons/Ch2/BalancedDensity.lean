module

public import SmoothedPolygons.Ch2.Boundary
public import SmoothedPolygons.Ch2.Hexagon
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

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
  book; `hex_hexMidpoint_mem_frontier`), and `area(H_K) = 4 det(m₀, m₁)` (`hex_volume_hexagonOf`);
* the multi-point `σ(t)` with `σ₀(t) = m₀` gives a second inscribed configuration with the same
  first point; for a centrally symmetric convex disk, the value `det(u, p)` with `u, p, p - u` on
  the boundary and `det(u, p) > 0` depends only on `u` (`ch2_det2_eq_of_inscribed`: the chords
  parallel to `u` have concave, even length, which equals `|u|` at one height only), so
  `det(m₀, m₁) = det(σ₀(t), σ₁(t)) = √3/2` and `area(H_K) = 2√3 = √12`.

How the helper lemmas are proved. The first two, on centrally symmetric hexagons, are in
`SmoothedPolygons.Ch2.Hexagon` (`hex_volume_hexagonOf`: the hexagon is cut into six triangles;
`hex_hexMidpoint_mem_frontier`: the book's rotation argument).

* `ch2_det2_eq_of_inscribed`. Suppose `0 < det(u, p) < det(u, q)` and put
  `θ = det(u, p)/det(u, q) ∈ (0, 1)`. The point `θ q` is interior (it is between `0` and `q`), and
  `θ q - u = (1 - θ)(-u) + θ (q - u)` is in `K`; both are at the height `det(u, p)` of `p` and
  `p - u` (this is the concavity of the chord length at the heights `0 < det(u, p) < det(u, q)`).
  Writing `p = θ q + μ u`, in each of the cases `μ ≤ 0`, `0 < μ ≤ 1`, `μ > 1` one of `p`, `p - u`
  lies between an interior point and a point of `K`, so in the interior
  (`bal_not_lt_of_inscribed`). By symmetry `det(u, p) = det(u, q)`.
* `ch2_not_isParallelogram_of_isBalancedPair`. The curve `σ₀` passes through a vertex `w` of the
  parallelogram; both coordinates of `σ₀(t)` in its edge basis are maximal at `w`, so both
  derivatives vanish there and `σ₀' = 0`, contradicting regularity.
-/

@[expose] public section

namespace SmoothedPolygons

open MeasureTheory Set

/-! ### Chords parallel to a vector -/

/-- A centrally symmetric convex disk contains the origin in its interior. -/
lemma bal_zero_mem_interior {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) :
    (0 : Fin 2 → ℝ) ∈ interior K := by
  obtain ⟨hconv, -, ⟨x, hx⟩, hsymm⟩ := hK
  have hneg : -interior K ⊆ interior K := by
    refine interior_maximal (fun y hy ↦ ?_) (isOpen_interior.neg)
    simpa using hsymm _ (interior_subset (Set.mem_neg.1 hy))
  have hx' : -x ∈ interior K := hneg (by simpa using hx)
  have := hconv.interior hx hx' (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  simpa [smul_neg] using this

/-- If `det(u, y) = 0` and `det(u, w) ≠ 0`, then `y` is a multiple of `u`. -/
lemma bal_eq_smul_of_det2_eq_zero {u y w : Fin 2 → ℝ} (hw : det2 u w ≠ 0) (hy : det2 u y = 0) :
    y = (det2 y w / det2 u w) • u := by
  ext i
  fin_cases i <;> simp <;> field_simp <;> simp only [det2] at hy ⊢
  · linear_combination (w 0) * hy
  · linear_combination (w 1) * hy

/-- If `0 < det(u, p) < det(u, q)` with `q, q - u, u` in `K`, then `p` or `p - u` lies in the
interior of `K`: the chord of `K` through `p` parallel to `u` is longer than `|u|`. -/
lemma bal_not_lt_of_inscribed {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {u p q : Fin 2 → ℝ}
    (hu : u ∈ K) (hp : p ∈ frontier K) (hpu : p - u ∈ frontier K) (hq : q ∈ K) (hqu : q - u ∈ K)
    (hup : 0 < det2 u p) (hlt : det2 u p < det2 u q) : False := by
  have h0 := bal_zero_mem_interior hK
  obtain ⟨hconv, hcomp, -, hsymm⟩ := hK
  have hpK : p ∈ K := hcomp.isClosed.frontier_subset hp
  have hpuK : p - u ∈ K := hcomp.isClosed.frontier_subset hpu
  have hpi : p ∉ interior K := hp.2
  have hpui : p - u ∉ interior K := hpu.2
  have huq : 0 < det2 u q := hup.trans hlt
  set θ := det2 u p / det2 u q with hθ
  have hθ0 : 0 < θ := div_pos hup huq
  have hθ1 : θ < 1 := (div_lt_one huq).2 hlt
  have hz : θ • q ∈ interior K := by
    have := hconv.combo_interior_self_mem_interior h0 hq (a := 1 - θ) (b := θ) (by linarith)
      hθ0.le (by ring)
    simpa using this
  have hr : θ • q - u ∈ K := by
    have := hconv (hsymm u hu) hqu (a := 1 - θ) (b := θ) (by linarith) hθ0.le (by ring)
    convert this using 1
    module
  have hdet : det2 u (p - θ • q) = 0 := by
    have : det2 u (p - θ • q) = det2 u p - θ * det2 u q := by simp [det2]; ring
    rw [this, hθ, div_mul_cancel₀ _ huq.ne']
    ring
  set μ := det2 (p - θ • q) p / det2 u p
  have hpz : p = θ • q + μ • u := by
    rw [← bal_eq_smul_of_det2_eq_zero hup.ne' hdet]
    abel
  rcases le_or_gt μ 0 with hμ | hμ
  · apply hpi
    have hμ' : 0 < 1 - μ := by linarith
    have := hconv.combo_interior_self_mem_interior hz hpuK (a := 1 / (1 - μ)) (b := -μ / (1 - μ))
      (by positivity) (div_nonneg (by linarith) hμ'.le) (by field_simp; ring)
    convert this using 1
    conv_lhs => rw [hpz]
    conv_rhs => rw [hpz]
    ext i
    simp
    field_simp
    ring
  rcases le_or_gt μ 1 with hμ1 | hμ1
  · apply hpui
    have := hconv.combo_interior_self_mem_interior hz hr (a := μ) (b := 1 - μ) hμ (by linarith)
      (by ring)
    convert this using 1
    rw [hpz]
    module
  · apply hpui
    have := hconv.combo_interior_self_mem_interior hz hpK (a := 1 / μ) (b := (μ - 1) / μ)
      (by positivity) (div_nonneg (by linarith) (by linarith)) (by field_simp; ring)
    convert this using 1
    conv_lhs => rw [hpz]
    conv_rhs => rw [hpz]
    ext i
    simp
    field_simp
    ring

/-- For a centrally symmetric convex disk `K` and a boundary point `u`, the value `det(u, p)`, for
`p` with `p` and `p - u` on the boundary and `det(u, p) > 0`, does not depend on `p`. -/
lemma ch2_det2_eq_of_inscribed {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {u p q : Fin 2 → ℝ}
    (hu : u ∈ frontier K) (hp : p ∈ frontier K) (hpu : p - u ∈ frontier K)
    (hq : q ∈ frontier K) (hqu : q - u ∈ frontier K) (hup : 0 < det2 u p) (huq : 0 < det2 u q) :
    det2 u p = det2 u q := by
  have hcl := hK.2.1.isClosed
  rcases lt_trichotomy (det2 u p) (det2 u q) with h | h | h
  · exact (bal_not_lt_of_inscribed hK (hcl.frontier_subset hu) hp hpu (hcl.frontier_subset hq)
      (hcl.frontier_subset hqu) hup h).elim
  · exact h
  · exact (bal_not_lt_of_inscribed hK (hcl.frontier_subset hu) hq hqu (hcl.frontier_subset hp)
      (hcl.frontier_subset hpu) huq h).elim

/-! ### Balanced disks are not parallelograms -/

open Filter Topology in
/-- The boundary of a balanced disk is a regular `C¹` closed curve, so a balanced disk is not a
parallelogram. -/
lemma ch2_not_isParallelogram_of_isBalancedPair {K : Set (Fin 2 → ℝ)}
    {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {tf : ℝ} (h : IsBalancedPair K σ tf) : ¬ IsParallelogram K := by
  rintro ⟨c, u, v, huv, hKeq⟩
  obtain ⟨⟨-, hcomp, -, -⟩, hσ, -, -, -, -, htf, hper, -, himage⟩ := h
  have hcoord : ∀ x ∈ K, det2 (x - c) v / det2 u v ≤ 1 ∧ det2 u (x - c) / det2 u v ≤ 1 := by
    intro x hx
    rw [hKeq] at hx
    obtain ⟨s, t, hs, ht, rfl⟩ := hx
    have e1 : det2 (c + s • u + t • v - c) v / det2 u v = s := by
      field_simp; simp only [det2, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    have e2 : det2 u (c + s • u + t • v - c) / det2 u v = t := by
      field_simp; simp only [det2, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [e1, e2]
    exact ⟨(le_abs_self s).trans hs, (le_abs_self t).trans ht⟩
  set w := c + u + v with hw
  have hwK : w ∈ K := hKeq ▸ ⟨1, 1, by simp, by simp, by rw [hw]; simp⟩
  have hfw : det2 (w - c) v / det2 u v = 1 := by
    rw [div_eq_one_iff_eq huv]; simp only [hw, det2, Pi.add_apply, Pi.sub_apply]; ring
  have hgw : det2 u (w - c) / det2 u v = 1 := by
    rw [div_eq_one_iff_eq huv]; simp only [hw, det2, Pi.add_apply, Pi.sub_apply]; ring
  have hw_int : w ∉ interior K := by
    intro hwi
    have hc : Continuous fun ε : ℝ ↦ w + ε • u := by fun_prop
    have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), w + ε • u ∈ K :=
      hc.continuousAt.preimage_mem_nhds (by simpa using mem_interior_iff_mem_nhds.1 hwi)
    obtain ⟨ε, hεK, hε⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
    have h1 := (hcoord _ hεK).1
    have : det2 (w + ε • u - c) v / det2 u v = 1 + ε := by
      rw [← hfw]
      field_simp
      simp only [det2, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [this] at h1
    exact absurd hε (by simp; linarith)
  have hw_fr : w ∈ frontier K := ⟨subset_closure hwK, hw_int⟩
  rw [← himage 0] at hw_fr
  obtain ⟨t0, -, ht0⟩ := hw_fr
  have hall : ∀ t, σ 0 t ∈ K := by
    intro t
    obtain ⟨y, hy, hyt⟩ := Function.Periodic.exists_mem_Ico₀ (hper 0) (by positivity) t
    rw [hyt]
    exact hcomp.isClosed.frontier_subset (himage 0 ▸ mem_image_of_mem _ hy)
  have hd : HasDerivAt (σ 0) (deriv (σ 0) t0) t0 :=
    (((hσ 0).1.differentiable one_ne_zero) t0).hasDerivAt
  have hd0 := hasDerivAt_pi.1 hd 0
  have hd1 := hasDerivAt_pi.1 hd 1
  have hF : HasDerivAt (fun t ↦ det2 (σ 0 t - c) v / det2 u v)
      ((deriv (σ 0) t0 0 * v 1 - deriv (σ 0) t0 1 * v 0) / det2 u v) t0 := by
    simp only [det2, Pi.sub_apply]
    exact (((hd0.sub_const (c 0)).mul_const (v 1)).sub
      ((hd1.sub_const (c 1)).mul_const (v 0))).div_const _
  have hG : HasDerivAt (fun t ↦ det2 u (σ 0 t - c) / det2 u v)
      ((u 0 * deriv (σ 0) t0 1 - u 1 * deriv (σ 0) t0 0) / det2 u v) t0 := by
    simp only [det2, Pi.sub_apply]
    exact (((hd1.sub_const (c 1)).const_mul (u 0)).sub
      ((hd0.sub_const (c 0)).const_mul (u 1))).div_const _
  have hmaxF : IsLocalMax (fun t ↦ det2 (σ 0 t - c) v / det2 u v) t0 :=
    Eventually.of_forall fun t ↦ by
      simp only
      rw [ht0, hfw]
      exact (hcoord _ (hall t)).1
  have hmaxG : IsLocalMax (fun t ↦ det2 u (σ 0 t - c) / det2 u v) t0 :=
    Eventually.of_forall fun t ↦ by
      simp only
      rw [ht0, hgw]
      exact (hcoord _ (hall t)).2
  have h1 := hmaxF.hasDerivAt_eq_zero hF
  have h2 := hmaxG.hasDerivAt_eq_zero hG
  rw [div_eq_zero_iff, or_iff_left huv] at h1 h2
  apply (hσ 0).2 t0
  have huv' := huv
  simp only [det2] at huv'
  ext i
  fin_cases i
  · have : deriv (σ 0) t0 0 * det2 u v = 0 := by
      simp only [det2]; linear_combination (u 0) * h1 + (v 0) * h2
    simpa [huv] using this
  · have : deriv (σ 0) t0 1 * det2 u v = 0 := by
      simp only [det2]; linear_combination (u 1) * h1 + (v 1) * h2
    simpa [huv] using this

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
  rw [hδ v hv, hex_volume_hexagonOf hv.1]
  have hm : ∀ j, hexMidpoint v j ∈ frontier K := hex_hexMidpoint_mem_frontier hK hv
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
  have heq := ch2_det2_eq_of_inscribed hK (hm 0) (hm 1) (hex_hexMidpoint_sub hv.1 ▸ hm 2)
    (q := σ 1 t) hσ1 (ht0 ▸ h21 ▸ hσ2) (hex_det2_hexMidpoint_pos hv.1)
    (ht0 ▸ hdet ▸ by positivity)
  rw [heq, ← ht0, hdet]
  congr 1
  rw [show (12 : ℝ) = 2 ^ 2 * 3 by norm_num, Real.sqrt_mul (by norm_num),
    Real.sqrt_sq (by norm_num)]
  ring

end SmoothedPolygons
