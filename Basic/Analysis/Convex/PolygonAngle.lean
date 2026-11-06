module

public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.Analysis.Normed.Group.Pointwise
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Basic.Analysis.Convex.CircumscribedPolygon

/-!
# Angles of convex polygons, measured by area

For a set `K` of the plane `Fin 2 → ℝ`, `cnt_ang K` is half the area of `K ∩ B`, `B` the unit ball
of the sup norm (the open square `(-1, 1)²`). For a cone `K` this is the *angle* of `K` in units of
`π` (a half-plane has angle `1`, the plane `2`): it is additive on cones with disjoint interiors,
invariant under the quarter turn and under `x ↦ -x`, and for a convex polygon `S` the area of
`S ∩ ball p ε` is `2 ε² · cnt_angle S p` for all small `ε`, where `cnt_angle S p` is the angle of
the tangent cone of `S` at `p`.

Main results:
* `PlaneConvex.cnt_ang_add_ang_polar`: a pointed convex cone with nonempty interior and its polar
  cone have angles adding up to `1` (that is, `π`).
* `PlaneConvex.cnt_sum_angle_extremePoints`: the angles of a compact convex set with nonempty
  interior and `N` corners (finitely many) sum to `N - 2` (that is, `(N - 2)π`). The exterior
  angles are the angles of the normal cones, which tile the plane (the *normal fan*,
  `PlaneConvex.cnt_sum_ang_ncone`).
* `PlaneConvex.cnt_angle_pos`, `PlaneConvex.cnt_angle_lt_one`,
  `PlaneConvex.cnt_angle_eq_of_not_mem_extremePoints`: the angle of a convex polygon is in `(0, 1)`
  at a corner, and `0`, `1` or `2` elsewhere; `PlaneConvex.cnt_angle_eq_one_of_halfPlane`: it is
  `1` where the set is locally a half-plane.
* `PlaneConvex.cnt_volume_inter_ball`: the area of a convex polygon near a point.
* `PlaneConvex.cnt_extremePoints_finite`: a polygon `halfPlanesInter a c` has finitely many
  corners.

The sup norm is used instead of the Euclidean one since the only properties of the unit ball that
matter are its invariance under the quarter turn and under `x ↦ -x`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped Pointwise

namespace PlaneConvex

/-! ### Planar linear algebra -/

/-- The quarter turn `(x₀, x₁) ↦ (-x₁, x₀)`, as a linear map. -/
noncomputable def cnt_perp : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) := Matrix.toLin' !![0, -1; 1, 0]

lemma cnt_perp_apply_zero (x : Fin 2 → ℝ) : cnt_perp x 0 = -x 1 := by
  simp [cnt_perp, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma cnt_perp_apply_one (x : Fin 2 → ℝ) : cnt_perp x 1 = x 0 := by
  simp [cnt_perp, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma cnt_dot_two (x y : Fin 2 → ℝ) : x ⬝ᵥ y = x 0 * y 0 + x 1 * y 1 := by
  simp [dotProduct, Fin.sum_univ_two]

lemma cnt_perp_dot (x y : Fin 2 → ℝ) : cnt_perp x ⬝ᵥ y = -x 1 * y 0 + x 0 * y 1 := by
  rw [cnt_dot_two, cnt_perp_apply_zero, cnt_perp_apply_one]

lemma cnt_normSq_pos {x : Fin 2 → ℝ} (hx : x ≠ 0) : 0 < x 0 * x 0 + x 1 * x 1 := by
  by_contra h
  apply hx
  have h0 : x 0 = 0 := by nlinarith [mul_self_nonneg (x 0), mul_self_nonneg (x 1)]
  have h1 : x 1 = 0 := by nlinarith [mul_self_nonneg (x 0), mul_self_nonneg (x 1)]
  ext i; fin_cases i <;> simp [h0, h1]

lemma cnt_dot_self_pos {x : Fin 2 → ℝ} (hx : x ≠ 0) : 0 < x ⬝ᵥ x := by
  rw [cnt_dot_two]; exact cnt_normSq_pos hx

lemma cnt_dot_perp_self (x : Fin 2 → ℝ) : x ⬝ᵥ cnt_perp x = 0 := by
  rw [dotProduct_comm, cnt_perp_dot]; ring

lemma cnt_perp_dot_self (x : Fin 2 → ℝ) : cnt_perp x ⬝ᵥ x = 0 := by
  rw [cnt_perp_dot]; ring

lemma cnt_perp_dot_perp (x : Fin 2 → ℝ) : cnt_perp x ⬝ᵥ cnt_perp x = x ⬝ᵥ x := by
  rw [cnt_perp_dot, cnt_perp_apply_zero, cnt_perp_apply_one, cnt_dot_two]; ring

lemma cnt_perp_ne_zero {x : Fin 2 → ℝ} (hx : x ≠ 0) : cnt_perp x ≠ 0 := by
  intro h
  have := cnt_perp_dot_perp x
  rw [h, zero_dotProduct] at this
  exact (cnt_dot_self_pos hx).ne this

/-- A vector `u` with `⟨perp m, u⟩ = 0`, `m ≠ 0`, is a multiple of `m`. -/
lemma cnt_eq_smul_of_perp_dot_eq_zero {m u : Fin 2 → ℝ} (hm : m ≠ 0)
    (h : cnt_perp m ⬝ᵥ u = 0) : u = ((m ⬝ᵥ u) / (m ⬝ᵥ m)) • m := by
  have hN := cnt_normSq_pos hm
  rw [cnt_perp_dot] at h
  rw [cnt_dot_two, cnt_dot_two]
  ext i; fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div, eq_div_iff hN.ne']
    linear_combination (-(m 1)) * h
  · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div, eq_div_iff hN.ne']
    linear_combination (m 0) * h

/-- Cramer's rule: if `⟨perp a, b⟩ ≠ 0`, every `x` is `α a + β b` with the explicit coefficients
`α = ⟨perp x, b⟩ / ⟨perp a, b⟩`, `β = ⟨perp a, x⟩ / ⟨perp a, b⟩`. -/
lemma cnt_cramer {a b : Fin 2 → ℝ} (hab : cnt_perp a ⬝ᵥ b ≠ 0) (x : Fin 2 → ℝ) :
    x = (cnt_perp x ⬝ᵥ b / cnt_perp a ⬝ᵥ b) • a + (cnt_perp a ⬝ᵥ x / cnt_perp a ⬝ᵥ b) • b := by
  rw [cnt_perp_dot] at hab
  rw [cnt_perp_dot, cnt_perp_dot, cnt_perp_dot]
  ext i; fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hab]
    ring
  · simp only [Fin.mk_one, Fin.isValue, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hab]
    ring

lemma cnt_norm_perp (x : Fin 2 → ℝ) : ‖cnt_perp x‖ = ‖x‖ := by
  have key : ∀ y : Fin 2 → ℝ, ‖cnt_perp y‖ ≤ ‖y‖ := by
    intro y
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg y)).2 fun i ↦ ?_
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, cnt_perp_apply_zero, norm_neg]
      exact norm_le_pi_norm y 1
    · simp only [Fin.mk_one, Fin.isValue, cnt_perp_apply_one]
      exact norm_le_pi_norm y 0
  refine le_antisymm (key x) ?_
  have h2 : cnt_perp (cnt_perp x) = -x := by
    ext i; fin_cases i <;> simp [cnt_perp_apply_zero, cnt_perp_apply_one]
  calc ‖x‖ = ‖cnt_perp (cnt_perp x)‖ := by rw [h2, norm_neg]
    _ ≤ ‖cnt_perp x‖ := key _

/-! ### Points near an interior point -/

lemma cnt_exists_add_sub_smul_mem {K : Set (Fin 2 → ℝ)} {x : Fin 2 → ℝ} (hx : x ∈ interior K)
    (v : Fin 2 → ℝ) : ∃ δ : ℝ, 0 < δ ∧ x + δ • v ∈ K ∧ x - δ • v ∈ K := by
  have h1 : Tendsto (fun t : ℝ ↦ x + t • v) (𝓝[>] 0) (𝓝 x) := by
    have hc : Continuous fun t : ℝ ↦ x + t • v := by fun_prop
    have := hc.tendsto 0
    simp only [zero_smul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun t : ℝ ↦ x - t • v) (𝓝[>] 0) (𝓝 x) := by
    have hc : Continuous fun t : ℝ ↦ x - t • v := by fun_prop
    have := hc.tendsto 0
    simp only [zero_smul, sub_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hK := mem_interior_iff_mem_nhds.mp hx
  obtain ⟨t, ⟨ht1, ht2⟩, ht0⟩ :=
    (((h1.eventually_mem hK).and (h2.eventually_mem hK)).and eventually_mem_nhdsWithin).exists
  exact ⟨t, ht0, ht1, ht2⟩

lemma cnt_exists_ne_zero_mem {K : Set (Fin 2 → ℝ)} {x : Fin 2 → ℝ} (hx : x ∈ interior K) :
    ∃ m ∈ K, m ≠ 0 := by
  obtain ⟨δ, hδ, h1, h2⟩ := cnt_exists_add_sub_smul_mem hx ![1, 0]
  by_cases h : x + δ • ![1, 0] = 0
  · refine ⟨_, h2, fun h' ↦ ?_⟩
    have := congrFun (h.trans h'.symm) 0
    simp at this
    linarith
  · exact ⟨_, h1, h⟩

/-- A set contained in a line has empty interior. -/
lemma cnt_interior_eq_empty_of_dot_eq_zero {K : Set (Fin 2 → ℝ)} {w : Fin 2 → ℝ} (hw : w ≠ 0)
    (h : ∀ u ∈ K, w ⬝ᵥ u = 0) : interior K = ∅ := by
  by_contra hne
  obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.2 hne
  obtain ⟨δ, hδ, h1, -⟩ := cnt_exists_add_sub_smul_mem hx w
  have e1 := h _ h1
  rw [dotProduct_add, h x (interior_subset hx), dotProduct_smul, smul_eq_mul, zero_add] at e1
  have := cnt_dot_self_pos hw
  rcases mul_eq_zero.1 e1 with h' | h' <;> linarith

/-! ### Angles of cones, measured by area -/

/-- Half the area of `K ∩ (-1, 1)²`; for a cone `K`, its angle in units of `π`. -/
noncomputable def cnt_ang (K : Set (Fin 2 → ℝ)) : ℝ :=
  (volume (K ∩ ball (0 : Fin 2 → ℝ) 1)).toReal / 2

lemma cnt_volume_ball (x : Fin 2 → ℝ) {r : ℝ} (hr : 0 < r) :
    volume (ball x r) = ENNReal.ofReal (4 * r ^ 2) := by
  rw [Real.volume_pi_ball x hr, Fintype.card_fin]
  ring_nf

lemma cnt_volume_inter_ball_lt_top (K : Set (Fin 2 → ℝ)) (x : Fin 2 → ℝ) (r : ℝ) :
    volume (K ∩ ball x r) < ⊤ :=
  (measure_mono inter_subset_right).trans_lt measure_ball_lt_top

lemma cnt_ang_nonneg (K : Set (Fin 2 → ℝ)) : 0 ≤ cnt_ang K :=
  div_nonneg ENNReal.toReal_nonneg zero_le_two

lemma cnt_ang_univ : cnt_ang univ = 2 := by
  rw [cnt_ang, univ_inter, cnt_volume_ball 0 one_pos, ENNReal.toReal_ofReal (by norm_num)]
  norm_num

lemma cnt_inter_subset_frontier {X Y : Set (Fin 2 → ℝ)}
    (h : Disjoint (interior X) (interior Y)) : X ∩ Y ⊆ frontier X ∪ frontier Y := by
  rintro z ⟨hzX, hzY⟩
  by_contra hz
  simp only [mem_union, not_or] at hz
  have h1 : z ∈ interior X := by
    by_contra h'
    exact hz.1 (by rw [frontier]; exact ⟨subset_closure hzX, h'⟩)
  have h2 : z ∈ interior Y := by
    by_contra h'
    exact hz.2 (by rw [frontier]; exact ⟨subset_closure hzY, h'⟩)
  exact h.ne_of_mem h1 h2 rfl

/-- Finitely many convex sets with pairwise disjoint interiors: the area of their union inside a
measurable set `B` is the sum of the areas. -/
lemma cnt_volume_biUnion_inter {ι : Type*} (s : Finset ι) (X : ι → Set (Fin 2 → ℝ))
    (hX : ∀ i ∈ s, Convex ℝ (X i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (interior (X i)) (interior (X j)))
    {B : Set (Fin 2 → ℝ)} (hB : MeasurableSet B) :
    volume ((⋃ i ∈ s, X i) ∩ B) = ∑ i ∈ s, volume (X i ∩ B) := by
  rw [iUnion₂_inter]
  refine measure_biUnion_finset₀ (fun i hi j hj hij ↦ ?_) (fun i hi ↦ ?_)
  · change volume ((X i ∩ B) ∩ (X j ∩ B)) = 0
    refine measure_mono_null (fun z hz ↦
      cnt_inter_subset_frontier (hd i hi j hj hij) ⟨hz.1.1, hz.2.1⟩) ?_
    exact measure_union_null (Convex.addHaar_frontier volume (hX i hi))
      (Convex.addHaar_frontier volume (hX j hj))
  · exact (Convex.nullMeasurableSet volume (hX i hi)).inter hB.nullMeasurableSet

/-- Angles of convex cones with disjoint interiors add up. -/
lemma cnt_ang_biUnion {ι : Type*} (s : Finset ι) (K : ι → Set (Fin 2 → ℝ))
    (hK : ∀ i ∈ s, Convex ℝ (K i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (interior (K i)) (interior (K j))) :
    cnt_ang (⋃ i ∈ s, K i) = ∑ i ∈ s, cnt_ang (K i) := by
  unfold cnt_ang
  rw [cnt_volume_biUnion_inter s K hK hd measurableSet_ball,
    ENNReal.toReal_sum (fun i _ ↦ (cnt_volume_inter_ball_lt_top _ _ _).ne), Finset.sum_div]

lemma cnt_ang_neg (K : Set (Fin 2 → ℝ)) : cnt_ang (-K) = cnt_ang K := by
  unfold cnt_ang
  have : -K ∩ ball (0 : Fin 2 → ℝ) 1 = -(K ∩ ball 0 1) := by
    rw [Set.inter_neg, neg_ball, neg_zero]
  rw [this, Measure.measure_neg]

lemma cnt_ang_perp_preimage (K : Set (Fin 2 → ℝ)) : cnt_ang (cnt_perp ⁻¹' K) = cnt_ang K := by
  unfold cnt_ang
  have hb : cnt_perp ⁻¹' ball (0 : Fin 2 → ℝ) 1 = ball 0 1 := by
    ext x
    simp [cnt_norm_perp]
  have hdet : LinearMap.det cnt_perp = 1 := by
    rw [cnt_perp, LinearMap.det_toLin', Matrix.det_fin_two_of]
    norm_num
  rw [show cnt_perp ⁻¹' K ∩ ball 0 1 = cnt_perp ⁻¹' (K ∩ ball 0 1) by rw [preimage_inter, hb],
    Measure.addHaar_preimage_linearMap volume (by rw [hdet]; norm_num), hdet]
  simp

/-- A cone with nonempty interior has positive angle. -/
lemma cnt_ang_pos {K : Set (Fin 2 → ℝ)} (hcone : ∀ u ∈ K, ∀ r : ℝ, 0 < r → r • u ∈ K)
    (hint : (interior K).Nonempty) : 0 < cnt_ang K := by
  obtain ⟨z, hz⟩ := hint
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hz)
  set s : ℝ := 1 / (2 * (‖z‖ + r)) with hsdef
  have hzr : 0 < ‖z‖ + r := by positivity
  have hs : 0 < s := by positivity
  have hsub : ball (s • z) (s * r) ⊆ K ∩ ball 0 1 := by
    intro y hy
    rw [mem_ball, dist_eq_norm] at hy
    constructor
    · have hy' : s⁻¹ • y ∈ ball z r := by
        rw [mem_ball, dist_eq_norm]
        have e : s⁻¹ • y - z = s⁻¹ • (y - s • z) := by rw [smul_sub, inv_smul_smul₀ hs.ne']
        rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs)]
        calc s⁻¹ * ‖y - s • z‖ < s⁻¹ * (s * r) := by gcongr
          _ = r := by field_simp
      have := hcone _ (hball hy') s hs
      rwa [smul_inv_smul₀ hs.ne'] at this
    · rw [mem_ball_zero_iff]
      have e : s * r + s * ‖z‖ = 1 / 2 := by
        rw [hsdef]
        field_simp
        ring
      calc ‖y‖ = ‖(y - s • z) + s • z‖ := by rw [sub_add_cancel]
        _ ≤ ‖y - s • z‖ + ‖s • z‖ := norm_add_le _ _
        _ < s * r + s * ‖z‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs]
          linarith
        _ < 1 := by rw [e]; norm_num
  have hpos : 0 < volume (K ∩ ball (0 : Fin 2 → ℝ) 1) :=
    (measure_ball_pos volume _ (mul_pos hs hr)).trans_le (measure_mono hsub)
  unfold cnt_ang
  exact div_pos (ENNReal.toReal_pos hpos.ne' (cnt_volume_inter_ball_lt_top _ _ _).ne) two_pos

/-! ### Polar cones and the duality `ang K + ang K° = 1` -/

/-- The polar cone `K° = {n | ∀ u ∈ K, ⟨n, u⟩ ≤ 0}`. -/
def cnt_polar (K : Set (Fin 2 → ℝ)) : Set (Fin 2 → ℝ) := {n | ∀ u ∈ K, n ⬝ᵥ u ≤ 0}

lemma cnt_convex_polar (K : Set (Fin 2 → ℝ)) : Convex ℝ (cnt_polar K) := by
  intro x hx y hy a b ha hb _ u hu
  rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  nlinarith [mul_nonneg ha (neg_nonneg.2 (hx u hu)), mul_nonneg hb (neg_nonneg.2 (hy u hu))]

/-- Positive combinations stay in a convex cone. -/
lemma cnt_smul_add_smul_mem {K : Set (Fin 2 → ℝ)} (hconv : Convex ℝ K)
    (hcone : ∀ u ∈ K, ∀ r : ℝ, 0 < r → r • u ∈ K) {u w : Fin 2 → ℝ} (hu : u ∈ K) (hw : w ∈ K)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : a • u + b • w ∈ K := by
  have hab : 0 < a + b := by linarith
  have h := hconv hu hw (div_pos ha hab).le (div_pos hb hab).le
    (by rw [← add_div, div_self hab.ne'])
  have := hcone _ h (a + b) hab
  convert this using 1
  rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ hab.ne', mul_div_cancel₀ _ hab.ne']

lemma cnt_zero_not_mem_interior {K : Set (Fin 2 → ℝ)} (hptd : ∀ u ∈ K, -u ∈ K → u = 0) :
    (0 : Fin 2 → ℝ) ∉ interior K := by
  intro h0
  obtain ⟨δ, hδ, h1, h2⟩ := cnt_exists_add_sub_smul_mem h0 ![1, 0]
  rw [zero_add] at h1
  rw [zero_sub] at h2
  have := congrFun (hptd _ h1 h2) 0
  simp at this
  linarith

lemma cnt_mem_interior_neg_iff {K : Set (Fin 2 → ℝ)} {x : Fin 2 → ℝ} :
    x ∈ interior (-K) ↔ -x ∈ interior K := by
  have := (Homeomorph.neg (Fin 2 → ℝ)).preimage_interior K
  change x ∈ interior ((Homeomorph.neg (Fin 2 → ℝ)) ⁻¹' K) ↔ _
  rw [← this]
  rfl

/-- **Duality.** A pointed convex cone `K` with nonempty interior and its polar cone have angles
adding up to `1` (that is, `π`). The cones `K`, `-K`, `perp⁻¹ K°` and `-perp⁻¹ K°` tile the plane;
the area of each of the last two is that of `K°`. -/
theorem cnt_ang_add_ang_polar {K : Set (Fin 2 → ℝ)} (hconv : Convex ℝ K)
    (hcone : ∀ u ∈ K, ∀ r : ℝ, 0 < r → r • u ∈ K) (hptd : ∀ u ∈ K, -u ∈ K → u = 0)
    (hint : (interior K).Nonempty) : cnt_ang K + cnt_ang (cnt_polar K) = 1 := by
  set A := cnt_perp ⁻¹' cnt_polar K with hAdef
  have hmemA : ∀ m, m ∈ A ↔ ∀ u ∈ K, cnt_perp m ⬝ᵥ u ≤ 0 := fun m ↦ Iff.rfl
  have hmemnA : ∀ m, m ∈ -A ↔ ∀ u ∈ K, 0 ≤ cnt_perp m ⬝ᵥ u := by
    intro m
    rw [Set.mem_neg, hmemA]
    simp only [map_neg, neg_dotProduct, neg_nonpos]
  have h0 : (0 : Fin 2 → ℝ) ∉ interior K := cnt_zero_not_mem_interior hptd
  -- interior points of `K` are in neither `A` nor `-A`
  have hKA : ∀ x ∈ interior K, x ∉ A := by
    intro x hx hxA
    have hx0 : x ≠ 0 := fun h ↦ h0 (h ▸ hx)
    obtain ⟨δ, hδ, h1, -⟩ := cnt_exists_add_sub_smul_mem hx (cnt_perp x)
    have e := (hmemA x).1 hxA _ h1
    rw [dotProduct_add, cnt_perp_dot_self, dotProduct_smul, smul_eq_mul, zero_add] at e
    have := cnt_dot_self_pos (cnt_perp_ne_zero hx0)
    nlinarith
  have hKnA : ∀ x ∈ interior K, x ∉ -A := by
    intro x hx hxA
    have hx0 : x ≠ 0 := fun h ↦ h0 (h ▸ hx)
    obtain ⟨δ, hδ, -, h2⟩ := cnt_exists_add_sub_smul_mem hx (cnt_perp x)
    have e := (hmemnA x).1 hxA _ h2
    rw [dotProduct_sub, cnt_perp_dot_self, dotProduct_smul, smul_eq_mul, zero_sub] at e
    have := cnt_dot_self_pos (cnt_perp_ne_zero hx0)
    nlinarith
  -- the four cones cover the plane
  have hcover : ∀ m, m ∈ K ∨ m ∈ -K ∨ m ∈ A ∨ m ∈ -A := by
    intro m
    by_contra hcon
    have hmA : ¬ ∀ u ∈ K, cnt_perp m ⬝ᵥ u ≤ 0 := fun h ↦ hcon (Or.inr (Or.inr (Or.inl h)))
    have hmnA : ¬ ∀ u ∈ K, 0 ≤ cnt_perp m ⬝ᵥ u :=
      fun h ↦ hcon (Or.inr (Or.inr (Or.inr ((hmemnA m).2 h))))
    have hmK : m ∉ K := fun h ↦ hcon (Or.inl h)
    have hnmK : -m ∉ K := fun h ↦ hcon (Or.inr (Or.inl (Set.mem_neg.2 h)))
    push Not at hmA hmnA
    obtain ⟨u1, hu1, h1⟩ := hmA
    obtain ⟨u2, hu2, h2⟩ := hmnA
    have hm0 : m ≠ 0 := by
      rintro rfl
      simp at h1
    have hβ : 0 < -(cnt_perp m ⬝ᵥ u2) := by linarith
    have hu := cnt_smul_add_smul_mem hconv hcone hu1 hu2 hβ h1
    have hperp : cnt_perp m ⬝ᵥ ((-(cnt_perp m ⬝ᵥ u2)) • u1 + (cnt_perp m ⬝ᵥ u1) • u2) = 0 := by
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      ring
    have heq := cnt_eq_smul_of_perp_dot_eq_zero hm0 hperp
    set s := m ⬝ᵥ ((-(cnt_perp m ⬝ᵥ u2)) • u1 + (cnt_perp m ⬝ᵥ u1) • u2) / (m ⬝ᵥ m)
    rcases lt_trichotomy s 0 with hs | hs | hs
    · apply hnmK
      have := hcone _ hu (-s)⁻¹ (inv_pos.2 (neg_pos.2 hs))
      rw [heq, smul_smul, inv_neg, neg_mul, inv_mul_cancel₀ hs.ne, neg_smul, one_smul] at this
      exact this
    · have hz : (-(cnt_perp m ⬝ᵥ u2)) • u1 + (cnt_perp m ⬝ᵥ u1) • u2 = 0 := by
        rw [heq, hs, zero_smul]
      have h3 : (-(cnt_perp m ⬝ᵥ u2)) • (-u1) =
          (-(cnt_perp m ⬝ᵥ u2)) • ((cnt_perp m ⬝ᵥ u1 / -(cnt_perp m ⬝ᵥ u2)) • u2) := by
        rw [smul_neg, eq_neg_of_add_eq_zero_left hz, neg_neg, smul_smul,
          mul_div_cancel₀ _ hβ.ne']
      have h4 := smul_right_injective _ hβ.ne' h3
      have hu10 : u1 = 0 := hptd u1 hu1 (h4 ▸ hcone _ hu2 _ (div_pos h1 hβ))
      rw [hu10, dotProduct_zero] at h1
      exact lt_irrefl _ h1
    · apply hmK
      have := hcone _ hu s⁻¹ (inv_pos.2 hs)
      rwa [heq, smul_smul, inv_mul_cancel₀ hs.ne', one_smul] at this
  -- pairwise disjoint interiors
  have d01 : Disjoint (interior K) (interior (-K)) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    rw [cnt_mem_interior_neg_iff] at hx'
    have hx0 := hptd x (interior_subset hx) (interior_subset hx')
    exact h0 (hx0 ▸ hx)
  have d02 : Disjoint (interior K) (interior A) :=
    Set.disjoint_left.2 fun x hx hx' ↦ hKA x hx (interior_subset hx')
  have d03 : Disjoint (interior K) (interior (-A)) :=
    Set.disjoint_left.2 fun x hx hx' ↦ hKnA x hx (interior_subset hx')
  have d12 : Disjoint (interior (-K)) (interior A) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    rw [cnt_mem_interior_neg_iff] at hx
    exact hKnA _ hx (by rw [Set.mem_neg, neg_neg]; exact interior_subset hx')
  have d13 : Disjoint (interior (-K)) (interior (-A)) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    rw [cnt_mem_interior_neg_iff] at hx
    exact hKA _ hx (Set.mem_neg.1 (interior_subset hx'))
  have d23 : Disjoint (interior A) (interior (-A)) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    have hx2 : x ∈ interior (A ∩ -A) := by rw [interior_inter]; exact ⟨hx, hx'⟩
    obtain ⟨m, ⟨hmA, hmnA⟩, hm0⟩ := cnt_exists_ne_zero_mem hx2
    have hK0 : interior K = ∅ := cnt_interior_eq_empty_of_dot_eq_zero (cnt_perp_ne_zero hm0)
      fun u hu ↦ le_antisymm ((hmemA m).1 hmA u hu) ((hmemnA m).1 hmnA u hu)
    rw [hK0] at hint
    exact not_nonempty_empty hint
  have hAconv : Convex ℝ A := (cnt_convex_polar K).linear_preimage cnt_perp
  let X : Fin 4 → Set (Fin 2 → ℝ) := ![K, -K, A, -A]
  have hXc : ∀ i ∈ (Finset.univ : Finset (Fin 4)), Convex ℝ (X i) := by
    intro i _
    fin_cases i
    exacts [hconv, hconv.neg, hAconv, hAconv.neg]
  have hXd : ∀ i ∈ (Finset.univ : Finset (Fin 4)), ∀ j ∈ (Finset.univ : Finset (Fin 4)),
      i ≠ j → Disjoint (interior (X i)) (interior (X j)) := by
    intro i _ j _ hij
    fin_cases i <;> fin_cases j <;> simp only [X] at hij ⊢
    all_goals first
      | exact absurd rfl hij
      | exact d01 | exact d01.symm | exact d02 | exact d02.symm | exact d03 | exact d03.symm
      | exact d12 | exact d12.symm | exact d13 | exact d13.symm | exact d23 | exact d23.symm
  have hU : (⋃ i ∈ (Finset.univ : Finset (Fin 4)), X i) = univ := by
    refine eq_univ_of_forall fun m ↦ ?_
    simp only [Finset.mem_univ, iUnion_true, mem_iUnion]
    rcases hcover m with h | h | h | h
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩, ⟨3, h⟩]
  have hsum := cnt_ang_biUnion Finset.univ X hXc hXd
  rw [hU, cnt_ang_univ, Fin.sum_univ_four] at hsum
  change 2 = cnt_ang K + cnt_ang (-K) + cnt_ang A + cnt_ang (-A) at hsum
  have hA : cnt_ang A = cnt_ang (cnt_polar K) := cnt_ang_perp_preimage _
  rw [cnt_ang_neg, cnt_ang_neg, hA] at hsum
  linarith

/-! ### Tangent cones, normal cones and angles of sets -/

/-- The tangent cone of `S` at `p`: the directions `u` with `p + t u ∈ S` for some `t > 0`. -/
def cnt_tcone (S : Set (Fin 2 → ℝ)) (p : Fin 2 → ℝ) : Set (Fin 2 → ℝ) :=
  {u | ∃ t : ℝ, 0 < t ∧ p + t • u ∈ S}

/-- The normal cone of `S` at `p`: the `n` with `⟨n, x - p⟩ ≤ 0` for all `x ∈ S`. -/
def cnt_ncone (S : Set (Fin 2 → ℝ)) (p : Fin 2 → ℝ) : Set (Fin 2 → ℝ) :=
  {n | ∀ x ∈ S, n ⬝ᵥ (x - p) ≤ 0}

/-- The angle of `S` at `p`, in units of `π`: the angle of the tangent cone if `p ∈ S`, else `0`.
For a convex polygon `S`, the area of `S ∩ ball p ε` is `2 ε² · cnt_angle S p` for small `ε`
(`cnt_volume_inter_ball`). -/
noncomputable def cnt_angle (S : Set (Fin 2 → ℝ)) (p : Fin 2 → ℝ) : ℝ := by
  classical exact if p ∈ S then cnt_ang (cnt_tcone S p) else 0

variable {S : Set (Fin 2 → ℝ)} {p : Fin 2 → ℝ}

lemma cnt_angle_of_mem (hp : p ∈ S) : cnt_angle S p = cnt_ang (cnt_tcone S p) := by
  simp [cnt_angle, hp]

lemma cnt_angle_of_not_mem (hp : p ∉ S) : cnt_angle S p = 0 := by
  simp [cnt_angle, hp]

lemma cnt_angle_nonneg (S : Set (Fin 2 → ℝ)) (p : Fin 2 → ℝ) : 0 ≤ cnt_angle S p := by
  by_cases hp : p ∈ S
  · rw [cnt_angle_of_mem hp]; exact cnt_ang_nonneg _
  · rw [cnt_angle_of_not_mem hp]

lemma cnt_add_smul_mem_of_le (hS : Convex ℝ S) (hp : p ∈ S) {u : Fin 2 → ℝ} {t s : ℝ}
    (ht : p + t • u ∈ S) (hs0 : 0 ≤ s) (hst : s ≤ t) : p + s • u ∈ S := by
  rcases hs0.eq_or_lt with rfl | hs
  · simpa using hp
  have ht0 : 0 < t := hs.trans_le hst
  have := hS.add_smul_mem hp ht (t := s / t) ⟨div_nonneg hs0 ht0.le, (div_le_one ht0).2 hst⟩
  rwa [smul_smul, div_mul_cancel₀ _ ht0.ne'] at this

lemma cnt_tcone_cone : ∀ u ∈ cnt_tcone S p, ∀ r : ℝ, 0 < r → r • u ∈ cnt_tcone S p := by
  rintro u ⟨t, ht, hu⟩ r hr
  refine ⟨t / r, div_pos ht hr, ?_⟩
  rwa [smul_smul, div_mul_cancel₀ _ hr.ne']

lemma cnt_convex_tcone (hS : Convex ℝ S) (hp : p ∈ S) : Convex ℝ (cnt_tcone S p) := by
  rintro u ⟨t, ht, hu⟩ w ⟨t', ht', hw⟩ a b ha hb hab
  refine ⟨min t t', lt_min ht ht', ?_⟩
  have h1 := cnt_add_smul_mem_of_le hS hp hu (le_min ht.le ht'.le) (min_le_left _ _)
  have h2 := cnt_add_smul_mem_of_le hS hp hw (le_min ht.le ht'.le) (min_le_right _ _)
  have := hS h1 h2 ha hb hab
  convert this using 1
  rw [smul_add, smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul, mul_comm a,
    mul_comm b, ← add_assoc, add_add_add_comm, ← add_smul, hab, one_smul]
  abel

lemma cnt_sub_mem_tcone {x : Fin 2 → ℝ} (hx : x ∈ S) : x - p ∈ cnt_tcone S p :=
  ⟨1, one_pos, by rwa [one_smul, add_sub_cancel]⟩

lemma cnt_interior_tcone_nonempty (hint : (interior S).Nonempty) :
    (interior (cnt_tcone S p)).Nonempty := by
  obtain ⟨z, hz⟩ := hint
  refine ⟨z - p, ?_⟩
  have hsub : (Homeomorph.addLeft p) ⁻¹' S ⊆ cnt_tcone S p := fun u hu ↦
    ⟨1, one_pos, by rw [one_smul]; exact hu⟩
  apply interior_mono hsub
  rw [← (Homeomorph.addLeft p).preimage_interior]
  change p + (z - p) ∈ interior S
  rwa [add_sub_cancel]

lemma cnt_tcone_eq_univ (hp : p ∈ interior S) : cnt_tcone S p = univ := by
  refine eq_univ_of_forall fun u ↦ ?_
  obtain ⟨δ, hδ, h1, -⟩ := cnt_exists_add_sub_smul_mem hp u
  exact ⟨δ, hδ, h1⟩

lemma cnt_eq_zero_of_mem_extremePoints {A : Set (Fin 2 → ℝ)} {x e : Fin 2 → ℝ}
    (hx : x ∈ extremePoints ℝ A) (h1 : x + e ∈ A) (h2 : x - e ∈ A) : e = 0 := by
  have hseg : x ∈ openSegment ℝ (x + e) (x - e) :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by ext i; simp; ring⟩
  have := ((mem_extremePoints.1 hx).2 _ h1 _ h2 hseg).1
  simpa using this

/-- At a corner the tangent cone is pointed. -/
lemma cnt_tcone_pointed (hS : Convex ℝ S) (hv : p ∈ extremePoints ℝ S) :
    ∀ u ∈ cnt_tcone S p, -u ∈ cnt_tcone S p → u = 0 := by
  rintro u ⟨t, ht, hu⟩ ⟨t', ht', hu'⟩
  have hp := extremePoints_subset hv
  have h1 := cnt_add_smul_mem_of_le hS hp hu (le_min ht.le ht'.le) (min_le_left _ _)
  have h2 := cnt_add_smul_mem_of_le hS hp hu' (le_min ht.le ht'.le) (min_le_right _ _)
  rw [smul_neg, ← sub_eq_add_neg] at h2
  have := cnt_eq_zero_of_mem_extremePoints hv h1 h2
  exact (smul_eq_zero.1 this).resolve_left (lt_min ht ht').ne'

/-- At a point of `S` which is not a corner the tangent cone contains a line. -/
lemma cnt_tcone_not_pointed (hp : p ∈ S) (hne : p ∉ extremePoints ℝ S) :
    ∃ u : Fin 2 → ℝ, u ≠ 0 ∧ u ∈ cnt_tcone S p ∧ -u ∈ cnt_tcone S p := by
  rw [mem_extremePoints] at hne
  push Not at hne
  obtain ⟨x1, hx1, x2, hx2, ⟨a, b, ha, hb, hab, h⟩, hne⟩ := hne hp
  have hsum : a • (x1 - p) + b • (x2 - p) = 0 := by
    ext i
    have := congrFun h i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.zero_apply] at this ⊢
    linear_combination this - p i * hab
  have hneg : -(x1 - p) = (b / a) • (x2 - p) := by
    apply smul_right_injective _ ha.ne'
    simp only
    rw [smul_neg, eq_neg_of_add_eq_zero_left hsum, neg_neg, smul_smul, mul_div_cancel₀ _ ha.ne']
  refine ⟨x1 - p, fun h0 ↦ ?_, cnt_sub_mem_tcone hx1, ?_⟩
  · have hx1p : x1 = p := sub_eq_zero.1 h0
    rw [h0, smul_zero, zero_add] at hsum
    have hx2p : x2 = p := sub_eq_zero.1 ((smul_eq_zero.1 hsum).resolve_left hb.ne')
    exact hne hx1p hx2p
  · rw [hneg]
    exact cnt_tcone_cone _ (cnt_sub_mem_tcone hx2) _ (div_pos hb ha)

lemma cnt_polar_tcone : cnt_polar (cnt_tcone S p) = cnt_ncone S p := by
  ext n
  constructor
  · intro hn x hx
    exact hn _ (cnt_sub_mem_tcone hx)
  · rintro hn u ⟨t, ht, hu⟩
    have := hn _ hu
    rw [add_sub_cancel_left, dotProduct_smul, smul_eq_mul] at this
    nlinarith

lemma cnt_convex_ncone (S : Set (Fin 2 → ℝ)) (p : Fin 2 → ℝ) : Convex ℝ (cnt_ncone S p) := by
  intro x hx y hy a b ha hb _ z hz
  rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  nlinarith [mul_nonneg ha (neg_nonneg.2 (hx z hz)), mul_nonneg hb (neg_nonneg.2 (hy z hz))]

lemma cnt_ncone_cone : ∀ n ∈ cnt_ncone S p, ∀ r : ℝ, 0 < r → r • n ∈ cnt_ncone S p := by
  intro n hn r hr x hx
  rw [smul_dotProduct, smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos hr.le (hn x hx)

/-- The normal cones at two distinct points of `S` have disjoint interiors. -/
lemma cnt_disjoint_interior_ncone {v w : Fin 2 → ℝ} (hv : v ∈ S) (hw : w ∈ S) (hvw : v ≠ w) :
    Disjoint (interior (cnt_ncone S v)) (cnt_ncone S w) := by
  rw [Set.disjoint_left]
  intro n hn hn'
  obtain ⟨δ, hδ, h1, -⟩ := cnt_exists_add_sub_smul_mem hn (w - v)
  have e1 := h1 w hw
  have e2 := hn' v hv
  have e3 := interior_subset hn w hw
  rw [add_dotProduct, smul_dotProduct, smul_eq_mul] at e1
  have hpos := cnt_dot_self_pos (sub_ne_zero.2 hvw.symm)
  have e4 : n ⬝ᵥ (v - w) = -(n ⬝ᵥ (w - v)) := by
    rw [← dotProduct_neg, neg_sub]
  nlinarith

/-- Every `n` is an outer normal at some corner of a compact convex set (Krein–Milman). -/
lemma cnt_exists_extremePoint_mem_ncone (hc : IsCompact S) (hne : S.Nonempty)
    (n : Fin 2 → ℝ) : ∃ v ∈ extremePoints ℝ S, n ∈ cnt_ncone S v := by
  set M := {y ∈ S | ∀ z ∈ S, n ⬝ᵥ z ≤ n ⬝ᵥ y} with hM
  obtain ⟨y0, hy0, hmax⟩ := hc.exists_isMaxOn hne
    (by fun_prop : Continuous fun x : Fin 2 → ℝ ↦ n ⬝ᵥ x).continuousOn
  have hMne : M.Nonempty := ⟨y0, hy0, fun z hz ↦ hmax hz⟩
  have hMc : IsCompact M := by
    have : M = S ∩ ⋂ z ∈ S, {y | n ⬝ᵥ z ≤ n ⬝ᵥ y} := by
      ext y; simp [hM]
    rw [this]
    exact hc.inter_right (isClosed_biInter fun z _ ↦ isClosed_le continuous_const
      (by fun_prop))
  have hMext : IsExtreme ℝ S M := by
    refine ⟨fun y hy ↦ hy.1, fun x1 hx1 x2 hx2 x hx hseg ↦ ?_⟩
    obtain ⟨a, b, ha, hb, hab, hxy⟩ := hseg
    have e : a * (n ⬝ᵥ x1) + b * (n ⬝ᵥ x2) = n ⬝ᵥ x := by
      rw [← hxy, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    have h1 := hx.2 x1 hx1
    have h2 := hx.2 x2 hx2
    have e1 : n ⬝ᵥ x1 = n ⬝ᵥ x := by
      have hb' : b = 1 - a := by linarith
      subst hb'
      nlinarith
    exact ⟨hx1, fun z hz ↦ e1 ▸ hx.2 z hz⟩
  obtain ⟨v, hv⟩ := hMc.extremePoints_nonempty hMne
  refine ⟨v, hMext.extremePoints_subset_extremePoints hv, fun x hx ↦ ?_⟩
  have := (extremePoints_subset hv).2 x hx
  rw [dotProduct_sub]
  linarith

/-- **The normal fan.** The angles of the normal cones at the corners of a compact convex set with
finitely many corners add up to `2` (that is, `2π`). -/
theorem cnt_sum_ang_ncone (hc : IsCompact S) (hne : S.Nonempty)
    (hfin : (extremePoints ℝ S).Finite) :
    ∑ v ∈ hfin.toFinset, cnt_ang (cnt_ncone S v) = 2 := by
  have hU : (⋃ v ∈ hfin.toFinset, cnt_ncone S v) = univ := by
    refine eq_univ_of_forall fun n ↦ ?_
    obtain ⟨v, hv, hn⟩ := cnt_exists_extremePoint_mem_ncone hc hne n
    exact mem_biUnion (hfin.mem_toFinset.2 hv) hn
  rw [← cnt_ang_univ, ← hU]
  refine (cnt_ang_biUnion _ _ (fun v _ ↦ cnt_convex_ncone S v) fun v hv w hw hvw ↦ ?_).symm
  rw [Set.Finite.mem_toFinset] at hv hw
  exact (cnt_disjoint_interior_ncone (extremePoints_subset hv) (extremePoints_subset hw)
    hvw).mono_right interior_subset

/-- At a corner of a convex set with nonempty interior, the angle and the angle of the normal
cone add up to `1`. -/
lemma cnt_angle_add_ang_ncone (hS : Convex ℝ S) (hint : (interior S).Nonempty)
    (hv : p ∈ extremePoints ℝ S) : cnt_angle S p + cnt_ang (cnt_ncone S p) = 1 := by
  have hp := extremePoints_subset hv
  rw [cnt_angle_of_mem hp, ← cnt_polar_tcone]
  exact cnt_ang_add_ang_polar (cnt_convex_tcone hS hp) cnt_tcone_cone (cnt_tcone_pointed hS hv)
    (cnt_interior_tcone_nonempty hint)

/-- **Angle sum.** The angles of a compact convex set with nonempty interior and `N` corners
(finitely many) add up to `N - 2` (that is, `(N - 2)π`). -/
theorem cnt_sum_angle_extremePoints (hc : IsCompact S) (hS : Convex ℝ S)
    (hint : (interior S).Nonempty) (hfin : (extremePoints ℝ S).Finite) :
    ∑ v ∈ hfin.toFinset, cnt_angle S v = (hfin.toFinset.card : ℝ) - 2 := by
  have h := cnt_sum_ang_ncone hc (hint.mono interior_subset) hfin
  have : ∀ v ∈ hfin.toFinset, cnt_angle S v = 1 - cnt_ang (cnt_ncone S v) := by
    intro v hv
    rw [Set.Finite.mem_toFinset] at hv
    linarith [cnt_angle_add_ang_ncone hS hint hv]
  rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, h, Finset.sum_const, nsmul_eq_mul,
    mul_one]

/-! ### Angles at points which are not corners -/

lemma cnt_add_mem {K : Set (Fin 2 → ℝ)} (hconv : Convex ℝ K)
    (hcone : ∀ u ∈ K, ∀ r : ℝ, 0 < r → r • u ∈ K) {u w : Fin 2 → ℝ} (hu : u ∈ K) (hw : w ∈ K) :
    u + w ∈ K := by
  simpa using cnt_smul_add_smul_mem hconv hcone hu hw one_pos one_pos

lemma cnt_ang_union {X Y : Set (Fin 2 → ℝ)} (hX : Convex ℝ X) (hY : Convex ℝ Y)
    (hd : Disjoint (interior X) (interior Y)) : cnt_ang (X ∪ Y) = cnt_ang X + cnt_ang Y := by
  have h := cnt_ang_biUnion (Finset.univ : Finset Bool) (fun b ↦ cond b X Y)
    (fun b _ ↦ by cases b <;> assumption) (fun i _ j _ hij ↦ by
      cases i <;> cases j
      · exact absurd rfl hij
      · exact hd.symm
      · exact hd
      · exact absurd rfl hij)
  have hU : (⋃ b ∈ (Finset.univ : Finset Bool), cond b X Y) = X ∪ Y := by
    ext x; simp [or_comm]
  rw [hU] at h
  rw [h]
  simp

/-- A convex cone with nonempty interior containing a line is the plane or has angle `1`. -/
lemma cnt_ang_of_not_pointed {K : Set (Fin 2 → ℝ)} (hconv : Convex ℝ K)
    (hcone : ∀ u ∈ K, ∀ r : ℝ, 0 < r → r • u ∈ K) (hint : (interior K).Nonempty)
    {u0 : Fin 2 → ℝ} (hu0 : u0 ≠ 0) (h1 : u0 ∈ K) (h2 : -u0 ∈ K) :
    K = univ ∨ cnt_ang K = 1 := by
  by_cases hU : K = univ
  · exact Or.inl hU
  right
  have h0 : (0 : Fin 2 → ℝ) ∈ K := by
    have := hconv h1 h2 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    rwa [smul_neg, add_neg_cancel] at this
  have hline : ∀ s : ℝ, s • u0 ∈ K := by
    intro s
    rcases lt_trichotomy s 0 with hs | rfl | hs
    · have := hcone _ h2 (-s) (neg_pos.2 hs)
      rwa [smul_neg, neg_smul, neg_neg] at this
    · rwa [zero_smul]
    · exact hcone _ h1 s hs
  -- a point of `K` off the line `ℝ u0`
  obtain ⟨z, hz, hfz⟩ : ∃ z ∈ K, cnt_perp u0 ⬝ᵥ z ≠ 0 := by
    by_contra hcon
    push Not at hcon
    rw [cnt_interior_eq_empty_of_dot_eq_zero (cnt_perp_ne_zero hu0) hcon] at hint
    exact not_nonempty_empty hint
  -- `K ∪ -K` is the plane
  have hcover : ∀ u, u ∈ K ∨ -u ∈ K := by
    intro u
    set q := cnt_perp u0 ⬝ᵥ u / cnt_perp u0 ⬝ᵥ z with hq
    have hker : cnt_perp u0 ⬝ᵥ (u - q • z) = 0 := by
      rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, hq, div_mul_cancel₀ _ hfz, sub_self]
    have hrep := cnt_eq_smul_of_perp_dot_eq_zero hu0 hker
    set t := u0 ⬝ᵥ (u - q • z) / (u0 ⬝ᵥ u0)
    have hu : u = q • z + t • u0 := by rw [← hrep]; abel
    rcases lt_trichotomy q 0 with hq0 | hq0 | hq0
    · right
      have : -u = (-q) • z + (-t) • u0 := by rw [hu, neg_add, neg_smul, neg_smul]
      rw [this]
      exact cnt_add_mem hconv hcone (hcone _ hz _ (neg_pos.2 hq0)) (hline _)
    · left
      rw [hu, hq0, zero_smul, zero_add]
      exact hline _
    · left
      rw [hu]
      exact cnt_add_mem hconv hcone (hcone _ hz _ hq0) (hline _)
  have hd : Disjoint (interior K) (interior (-K)) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    rw [cnt_mem_interior_neg_iff] at hx'
    have hmid := hconv.interior hx hx' (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    rw [smul_neg, add_neg_cancel] at hmid
    apply hU
    refine eq_univ_of_forall fun u ↦ ?_
    obtain ⟨δ, hδ, hu, -⟩ := cnt_exists_add_sub_smul_mem hmid u
    rw [zero_add] at hu
    have := hcone _ hu δ⁻¹ (inv_pos.2 hδ)
    rwa [smul_smul, inv_mul_cancel₀ hδ.ne', one_smul] at this
  have hKK : K ∪ -K = univ := eq_univ_of_forall fun u ↦ (hcover u).elim Or.inl
    (fun h ↦ Or.inr (Set.mem_neg.2 h))
  have := cnt_ang_union hconv hconv.neg hd
  rw [hKK, cnt_ang_univ, cnt_ang_neg] at this
  linarith

lemma cnt_angle_of_mem_interior (hp : p ∈ interior S) : cnt_angle S p = 2 := by
  rw [cnt_angle_of_mem (interior_subset hp), cnt_tcone_eq_univ hp, cnt_ang_univ]

/-- At a point which is not a corner, the angle of a convex set with nonempty interior is `0`,
`1` or `2`. -/
theorem cnt_angle_eq_of_not_mem_extremePoints (hS : Convex ℝ S) (hint : (interior S).Nonempty)
    (hp : p ∉ extremePoints ℝ S) :
    cnt_angle S p = 0 ∨ cnt_angle S p = 1 ∨ cnt_angle S p = 2 := by
  by_cases hpS : p ∈ S
  · obtain ⟨u0, hu0, h1, h2⟩ := cnt_tcone_not_pointed hpS hp
    rw [cnt_angle_of_mem hpS]
    rcases cnt_ang_of_not_pointed (cnt_convex_tcone hS hpS) cnt_tcone_cone
      (cnt_interior_tcone_nonempty hint) hu0 h1 h2 with h | h
    · rw [h, cnt_ang_univ]
      exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl h)
  · exact Or.inl (cnt_angle_of_not_mem hpS)

/-- At a point of a set with nonempty interior the angle is positive. -/
theorem cnt_angle_pos (hint : (interior S).Nonempty) (hp : p ∈ S) :
    0 < cnt_angle S p := by
  rw [cnt_angle_of_mem hp]
  exact cnt_ang_pos cnt_tcone_cone (cnt_interior_tcone_nonempty hint)

/-- At a point where `S` coincides locally with the half-plane `⟨w, x - v⟩ ≤ 0` (a side point),
the angle of a convex set is `1`. -/
theorem cnt_angle_eq_one_of_halfPlane (hS : Convex ℝ S) {w : Fin 2 → ℝ} (hw : w ≠ 0) {ε : ℝ}
    (hε : 0 < ε) (h : ∀ x, dist x p < ε → (x ∈ S ↔ w ⬝ᵥ (x - p) ≤ 0)) : cnt_angle S p = 1 := by
  have hp : p ∈ S := (h p (by rw [dist_self]; exact hε)).2 (by rw [sub_self, dotProduct_zero])
  have hsmall : ∀ u : Fin 2 → ℝ, ∃ s : ℝ, 0 < s ∧ dist (p + s • u) p < ε := by
    intro u
    refine ⟨ε / (2 * (‖u‖ + 1)), by positivity, ?_⟩
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg u]
  have hT : cnt_tcone S p = {u | w ⬝ᵥ u ≤ 0} := by
    ext u
    constructor
    · rintro ⟨t, ht, hu⟩
      obtain ⟨s, hs, hsd⟩ := hsmall u
      have hmem := cnt_add_smul_mem_of_le hS hp hu (le_min hs.le ht.le) (min_le_right _ _)
      have hd : dist (p + min s t • u) p < ε := by
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_pos (lt_min hs ht)]
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hs] at hsd
        calc min s t * ‖u‖ ≤ s * ‖u‖ := by gcongr; exact min_le_left _ _
          _ < ε := hsd
      have := (h _ hd).1 hmem
      rw [add_sub_cancel_left, dotProduct_smul, smul_eq_mul] at this
      exact nonpos_of_mul_nonpos_right this (lt_min hs ht)
    · intro hu
      obtain ⟨s, hs, hsd⟩ := hsmall u
      refine ⟨s, hs, (h _ hsd).2 ?_⟩
      rw [add_sub_cancel_left, dotProduct_smul, smul_eq_mul]
      exact mul_nonpos_of_nonneg_of_nonpos hs.le hu
  rw [cnt_angle_of_mem hp, hT]
  have hconv : Convex ℝ {u : Fin 2 → ℝ | w ⬝ᵥ u ≤ 0} :=
    convex_halfSpace_le ⟨fun x y ↦ dotProduct_add _ _ _, fun r x ↦ dotProduct_smul r _ _⟩ 0
  have hcone : ∀ u ∈ {u : Fin 2 → ℝ | w ⬝ᵥ u ≤ 0}, ∀ r : ℝ, 0 < r →
      r • u ∈ {u : Fin 2 → ℝ | w ⬝ᵥ u ≤ 0} := by
    intro u hu r hr
    simp only [mem_ofPred_eq, dotProduct_smul, smul_eq_mul] at hu ⊢
    exact mul_nonpos_of_nonneg_of_nonpos hr.le hu
  have hint : (interior {u : Fin 2 → ℝ | w ⬝ᵥ u ≤ 0}).Nonempty := by
    refine ⟨-w, interior_maximal (t := {u | w ⬝ᵥ u < 0}) (fun u (hu : w ⬝ᵥ u < 0) ↦ le_of_lt hu)
      (isOpen_lt (f := fun u : Fin 2 → ℝ ↦ w ⬝ᵥ u) (by fun_prop) continuous_const) ?_⟩
    change w ⬝ᵥ -w < 0
    rw [dotProduct_neg, neg_neg_iff_pos]
    exact cnt_dot_self_pos hw
  rcases cnt_ang_of_not_pointed hconv hcone hint (cnt_perp_ne_zero hw)
    (show w ⬝ᵥ cnt_perp w ≤ 0 from (cnt_dot_perp_self w).le)
    (show w ⬝ᵥ -cnt_perp w ≤ 0 by rw [dotProduct_neg, cnt_dot_perp_self, neg_zero]) with h' | h'
  · have h1 : w ∈ {u : Fin 2 → ℝ | w ⬝ᵥ u ≤ 0} := h' ▸ mem_univ w
    have h2 := cnt_dot_self_pos hw
    exact absurd h1 (not_le.2 h2)
  · exact h'

/-! ### Polygons -/

section Polygon

variable {ι : Type*} [Finite ι] {a : ι → Fin 2 → ℝ} {c : ι → ℝ}

/-- Moving from `x ∈ halfPlanesInter a c` in a direction keeping the active constraints active
stays in the polygon for small times of either sign. -/
lemma cnt_eventually_add_smul_mem {x d : Fin 2 → ℝ} (hx : x ∈ halfPlanesInter a c)
    (hd : ∀ j, a j ⬝ᵥ x = c j → a j ⬝ᵥ d = 0) :
    ∀ᶠ t in 𝓝 (0 : ℝ), x + t • d ∈ halfPlanesInter a c := by
  have : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ j, a j ⬝ᵥ (x + t • d) ≤ c j := by
    rw [eventually_all]
    intro j
    rcases (hx j).eq_or_lt with h | h
    · exact Eventually.of_forall fun t ↦ by
        rw [dotProduct_add, dotProduct_smul, h, hd j h, smul_zero, add_zero]
    · have hc : Continuous fun t : ℝ ↦ a j ⬝ᵥ (x + t • d) := by fun_prop
      have := hc.tendsto 0
      simp only [zero_smul, add_zero] at this
      exact (this.eventually (gt_mem_nhds h)).mono fun t ht ↦ ht.le
  exact this.mono fun t ht ↦ ht

/-- At a corner, no nonzero direction keeps all the active constraints active. -/
lemma cnt_eq_zero_of_active {x d : Fin 2 → ℝ} (hx : x ∈ extremePoints ℝ (halfPlanesInter a c))
    (hd : ∀ j, a j ⬝ᵥ x = c j → a j ⬝ᵥ d = 0) : d = 0 := by
  have hev := cnt_eventually_add_smul_mem (extremePoints_subset hx) hd
  have hev' : ∀ᶠ t in 𝓝 (0 : ℝ), x + (-t) • d ∈ halfPlanesInter a c :=
    (continuous_neg.tendsto' (0 : ℝ) 0 neg_zero).eventually hev
  obtain ⟨t, ⟨h1, h2⟩, ht⟩ := (((hev.and hev').filter_mono nhdsWithin_le_nhds).and
    (eventually_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0))).exists
  have := cnt_eq_zero_of_mem_extremePoints hx h1
    (by simpa [neg_smul, ← sub_eq_add_neg] using h2)
  exact (smul_eq_zero.1 this).resolve_left (ne_of_gt ht)

/-- A polygon has finitely many corners: a corner is determined by its active constraints. -/
theorem cnt_extremePoints_finite : (extremePoints ℝ (halfPlanesInter a c)).Finite := by
  refine Finite.of_finite_image (f := fun x ↦ {j | a j ⬝ᵥ x = c j}) (Set.toFinite _) ?_
  intro x hx y hy hxy
  have hd : ∀ j, a j ⬝ᵥ x = c j → a j ⬝ᵥ (y - x) = 0 := by
    intro j hjx
    have : j ∈ {j | a j ⬝ᵥ y = c j} := by
      have h' : j ∈ {j | a j ⬝ᵥ x = c j} := hjx
      simp only at hxy
      rwa [hxy] at h'
    rw [dotProduct_sub, this, hjx, sub_self]
  exact (sub_eq_zero.1 (cnt_eq_zero_of_active hx hd)).symm

lemma cnt_tcone_halfPlanesInter {p : Fin 2 → ℝ} (hp : p ∈ halfPlanesInter a c) :
    cnt_tcone (halfPlanesInter a c) p = {u | ∀ j, a j ⬝ᵥ p = c j → a j ⬝ᵥ u ≤ 0} := by
  ext u
  constructor
  · rintro ⟨t, ht, hu⟩ j hj
    have := hu j
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul, hj] at this
    nlinarith
  · intro hu
    have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ j, a j ⬝ᵥ p < c j → a j ⬝ᵥ (p + t • u) < c j := by
      rw [eventually_all]
      intro j
      by_cases hj : a j ⬝ᵥ p < c j
      · have hc : Continuous fun t : ℝ ↦ a j ⬝ᵥ (p + t • u) := by fun_prop
        have := hc.tendsto 0
        simp only [zero_smul, add_zero] at this
        exact (this.eventually (gt_mem_nhds hj)).mono fun t ht _ ↦ ht
      · exact Eventually.of_forall fun t h ↦ absurd h hj
    obtain ⟨t, ht, ht0⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
      (eventually_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0))).exists
    have ht0' : (0 : ℝ) < t := ht0
    refine ⟨t, ht0', fun j ↦ ?_⟩
    rcases (hp j).eq_or_lt with h | h
    · rw [dotProduct_add, dotProduct_smul, smul_eq_mul, h]
      have := hu j h
      nlinarith
    · exact (ht j h).le

/-- Near a point `p`, the polygon coincides with `p` plus its tangent cone. -/
lemma cnt_eventually_mem_iff {p : Fin 2 → ℝ} (hp : p ∈ halfPlanesInter a c) :
    ∀ᶠ x in 𝓝 p, (x ∈ halfPlanesInter a c ↔ x - p ∈ cnt_tcone (halfPlanesInter a c) p) := by
  have hev : ∀ᶠ x in 𝓝 p, ∀ j, a j ⬝ᵥ p < c j → a j ⬝ᵥ x < c j := by
    rw [eventually_all]
    intro j
    by_cases hj : a j ⬝ᵥ p < c j
    · have hc : Continuous fun x : Fin 2 → ℝ ↦ a j ⬝ᵥ x := by fun_prop
      exact ((hc.tendsto p).eventually (gt_mem_nhds hj)).mono fun x hx _ ↦ hx
    · exact Eventually.of_forall fun x h ↦ absurd h hj
  refine hev.mono fun x hx ↦ ⟨cnt_sub_mem_tcone, fun hxT j ↦ ?_⟩
  rw [cnt_tcone_halfPlanesInter hp] at hxT
  rcases (hp j).eq_or_lt with h | h
  · have := hxT j h
    rw [dotProduct_sub, h] at this
    linarith
  · exact (hx j h).le

end Polygon

lemma cnt_volume_cone_inter_ball {K : Set (Fin 2 → ℝ)}
    (hcone : ∀ u ∈ K, ∀ r : ℝ, 0 < r → r • u ∈ K) {ε : ℝ} (hε : 0 < ε) :
    volume (K ∩ ball 0 ε) = ENNReal.ofReal (ε ^ 2) * volume (K ∩ ball 0 1) := by
  have h : K ∩ ball (0 : Fin 2 → ℝ) ε = ε • (K ∩ ball 0 1) := by
    ext u
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hε.ne']
    constructor
    · rintro ⟨hu, hb⟩
      refine ⟨hcone _ hu _ (inv_pos.2 hε), ?_⟩
      rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hε),
        inv_mul_lt_iff₀ hε, mul_one]
      rwa [mem_ball_zero_iff] at hb
    · rintro ⟨hu, hb⟩
      refine ⟨?_, ?_⟩
      · have := hcone _ hu ε hε
        rwa [smul_inv_smul₀ hε.ne'] at this
      · rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hε),
          inv_mul_lt_iff₀ hε, mul_one] at hb
        rwa [mem_ball_zero_iff]
  rw [h, Measure.addHaar_smul, Module.finrank_fin_fun, abs_of_pos (by positivity)]

/-- **Area near a point.** For a polygon `S`, the area of `S ∩ ball p ε` is `2 ε² · angle` for all
small `ε > 0`. -/
theorem cnt_volume_inter_ball {ι : Type*} [Finite ι] {a : ι → Fin 2 → ℝ} {c : ι → ℝ}
    (hS : S = halfPlanesInter a c) (p : Fin 2 → ℝ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), (volume (S ∩ ball p ε)).toReal = 2 * ε ^ 2 * cnt_angle S p := by
  subst hS
  by_cases hp : p ∈ halfPlanesInter a c
  · obtain ⟨δ, hδ, hloc⟩ := Metric.eventually_nhds_iff.1 (cnt_eventually_mem_iff hp)
    filter_upwards [Ioo_mem_nhdsGT hδ] with ε ⟨hε0, hεδ⟩
    set T := cnt_tcone (halfPlanesInter a c) p
    have hset : halfPlanesInter a c ∩ ball p ε = (fun x ↦ -p + x) ⁻¹' (T ∩ ball 0 ε) := by
      ext x
      simp only [mem_inter_iff, mem_preimage, mem_ball, dist_zero_right, neg_add_eq_sub]
      rw [← dist_eq_norm]
      constructor
      · rintro ⟨hx, hd⟩
        exact ⟨(hloc (hd.trans hεδ)).1 hx, hd⟩
      · rintro ⟨hx, hd⟩
        exact ⟨(hloc (hd.trans hεδ)).2 hx, hd⟩
    rw [hset, measure_preimage_add, cnt_volume_cone_inter_ball cnt_tcone_cone hε0,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), cnt_angle_of_mem hp, cnt_ang]
    ring
  · obtain ⟨δ, hδ, hball⟩ :=
      Metric.isOpen_iff.1 (isClosed_halfPlanesInter a c).isOpen_compl p hp
    filter_upwards [Ioo_mem_nhdsGT hδ] with ε ⟨hε0, hεδ⟩
    have : halfPlanesInter a c ∩ ball p ε = ∅ := by
      ext x
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
      intro hx hd
      exact hball (ball_subset_ball hεδ.le hd) hx
    rw [this, measure_empty, ENNReal.toReal_zero, cnt_angle_of_not_mem hp, mul_zero]

section Polygon

variable {ι : Type*} [Finite ι] {a : ι → Fin 2 → ℝ} {c : ι → ℝ}

/-- At a corner of a polygon, two active constraints have independent normals. -/
lemma cnt_exists_active_indep {v : Fin 2 → ℝ} (hv : v ∈ extremePoints ℝ (halfPlanesInter a c)) :
    ∃ i j, a i ⬝ᵥ v = c i ∧ a j ⬝ᵥ v = c j ∧ cnt_perp (a i) ⬝ᵥ a j ≠ 0 := by
  by_contra hcon
  have hcon' : ∀ i j, a i ⬝ᵥ v = c i → a j ⬝ᵥ v = c j → cnt_perp (a i) ⬝ᵥ a j = 0 := by
    intro i j hi hj
    by_contra h
    exact hcon ⟨i, j, hi, hj, h⟩
  by_cases h : ∃ i, a i ⬝ᵥ v = c i ∧ a i ≠ 0
  · obtain ⟨i, hi, hi0⟩ := h
    have := cnt_eq_zero_of_active hv (d := cnt_perp (a i)) fun j hj ↦ by
      rw [dotProduct_comm]; exact hcon' i j hi hj
    exact cnt_perp_ne_zero hi0 this
  · have h' : ∀ i, a i ⬝ᵥ v = c i → a i = 0 := by
      intro i hi
      by_contra h0
      exact h ⟨i, hi, h0⟩
    have := cnt_eq_zero_of_active hv (d := ![1, 0]) fun j hj ↦ by
      rw [h' j hj, zero_dotProduct]
    have := congrFun this 0
    simp at this

/-- At a corner of a polygon, the normal cone has nonempty interior. -/
lemma cnt_interior_ncone_nonempty {v : Fin 2 → ℝ}
    (hv : v ∈ extremePoints ℝ (halfPlanesInter a c)) :
    (interior (cnt_ncone (halfPlanesInter a c) v)).Nonempty := by
  obtain ⟨i, j, hi, hj, hD⟩ := cnt_exists_active_indep hv
  set D := cnt_perp (a i) ⬝ᵥ a j with hDdef
  set U := {x : Fin 2 → ℝ | 0 < cnt_perp x ⬝ᵥ a j / D ∧ 0 < cnt_perp (a i) ⬝ᵥ x / D}
  have hUo : IsOpen U := by
    have hp : Continuous fun x : Fin 2 → ℝ ↦ cnt_perp x :=
      cnt_perp.continuous_of_finiteDimensional
    have h1 : Continuous fun x : Fin 2 → ℝ ↦ cnt_perp x ⬝ᵥ a j / D := by fun_prop
    have h2 : Continuous fun x : Fin 2 → ℝ ↦ cnt_perp (a i) ⬝ᵥ x / D := by fun_prop
    exact (isOpen_lt continuous_const h1).inter (isOpen_lt continuous_const h2)
  have hUsub : U ⊆ cnt_ncone (halfPlanesInter a c) v := by
    rintro x ⟨hα, hβ⟩ y hy
    rw [cnt_cramer hD x, add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul,
      smul_eq_mul, dotProduct_sub, dotProduct_sub, hi, hj]
    have h1 := hy i
    have h2 := hy j
    nlinarith [mul_nonneg hα.le (sub_nonneg.2 h1), mul_nonneg hβ.le (sub_nonneg.2 h2)]
  refine ⟨a i + a j, interior_maximal hUsub hUo ⟨?_, ?_⟩⟩
  · rw [map_add, add_dotProduct, cnt_perp_dot_self, add_zero, div_self hD]
    exact one_pos
  · rw [dotProduct_add, cnt_perp_dot_self, zero_add, div_self hD]
    exact one_pos

/-- At a corner of a polygon with nonempty interior, the angle is less than `1` (that is, `π`). -/
theorem cnt_angle_lt_one (hint : (interior (halfPlanesInter a c)).Nonempty) {v : Fin 2 → ℝ}
    (hv : v ∈ extremePoints ℝ (halfPlanesInter a c)) : cnt_angle (halfPlanesInter a c) v < 1 := by
  have h := cnt_angle_add_ang_ncone (convex_halfPlanesInter a c) hint hv
  have := cnt_ang_pos cnt_ncone_cone (cnt_interior_ncone_nonempty hv)
  linarith

end Polygon

end PlaneConvex
