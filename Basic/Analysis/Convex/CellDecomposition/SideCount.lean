module

public import Basic.Analysis.Convex.CellDecomposition.Defs
public import Basic.Analysis.Convex.PolygonAngle

/-!
# (C2) The side count

Part of the proof of the cell lemma (`Basic.Analysis.Convex.CellDecomposition`).

The angles are those of `Basic.Analysis.Convex.PolygonAngle` (`PlaneConvex.cnt_angle`, measured by
area, in units of `π`), with the angle sum `PlaneConvex.cnt_sum_angle_extremePoints`. Here:
* the holes: distinct holes do not overlap, cells and holes cover `Q`, every corner of a hole is a
  corner of a cell, and there are finitely many holes;
* a polygon cut out by `m` half-planes has at most `m` corners;
* the local identity: at every point the angles of the cells and holes add up to that of `Q`;
* the count (C2).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric

namespace PlaneConvex

/-! ### Convex polygons -/

section PolygonFacts

variable {S : Set (Fin 2 → ℝ)}

private lemma poly_convex (hS : IsConvexPolygon S) : Convex ℝ S := by
  obtain ⟨⟨k, a, c, rfl⟩, -, -⟩ := hS
  exact convex_halfPlanesInter a c

private lemma poly_closed (hS : IsConvexPolygon S) : IsClosed S := by
  obtain ⟨⟨k, a, c, rfl⟩, -, -⟩ := hS
  exact isClosed_halfPlanesInter a c

private lemma poly_compact (hS : IsConvexPolygon S) : IsCompact S :=
  Metric.isCompact_of_isClosed_isBounded (poly_closed hS) hS.2.1

private lemma poly_int (hS : IsConvexPolygon S) : (interior S).Nonempty := hS.2.2

private lemma poly_finite (hS : IsConvexPolygon S) : (extremePoints ℝ S).Finite := by
  obtain ⟨⟨k, a, c, rfl⟩, -, -⟩ := hS
  exact cnt_extremePoints_finite

private lemma poly_angle_lt_one (hS : IsConvexPolygon S) {v : Fin 2 → ℝ}
    (hv : v ∈ extremePoints ℝ S) : cnt_angle S v < 1 := by
  obtain ⟨⟨k, a, c, rfl⟩, -, hint⟩ := hS
  exact cnt_angle_lt_one hint hv

private lemma poly_angle_pos (hS : IsConvexPolygon S) {v : Fin 2 → ℝ} (hv : v ∈ S) :
    0 < cnt_angle S v :=
  cnt_angle_pos hS.2.2 hv

private lemma poly_angle_nat (hS : IsConvexPolygon S) {v : Fin 2 → ℝ}
    (hv : v ∉ extremePoints ℝ S) :
    cnt_angle S v = 0 ∨ cnt_angle S v = 1 ∨ cnt_angle S v = 2 :=
  cnt_angle_eq_of_not_mem_extremePoints (poly_convex hS) hS.2.2 hv

private lemma poly_angle_sum (hS : IsConvexPolygon S) (T : Finset (Fin 2 → ℝ))
    (hT : (T : Set (Fin 2 → ℝ)) = extremePoints ℝ S) :
    ∑ v ∈ T, cnt_angle S v = (T.card : ℝ) - 2 := by
  have hfin := poly_finite hS
  have : hfin.toFinset = T := by
    ext x
    simp [← hT]
  rw [← this]
  exact cnt_sum_angle_extremePoints (poly_compact hS) (poly_convex hS) hS.2.2 hfin

private lemma poly_volume (hS : IsConvexPolygon S) (p : Fin 2 → ℝ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), (volume (S ∩ ball p ε)).toReal = 2 * ε ^ 2 * cnt_angle S p := by
  obtain ⟨⟨k, a, c, rfl⟩, -, -⟩ := hS
  exact cnt_volume_inter_ball rfl p

/-- A convex polygon has at least three corners (by the angle sum). -/
private lemma poly_three_le (hS : IsConvexPolygon S) (T : Finset (Fin 2 → ℝ))
    (hT : (T : Set (Fin 2 → ℝ)) = extremePoints ℝ S) : 3 ≤ T.card := by
  have hsum := poly_angle_sum hS T hT
  obtain ⟨v, hv⟩ := (poly_compact hS).extremePoints_nonempty (hS.2.2.mono interior_subset)
  have hvT : v ∈ T := by rw [← Finset.mem_coe, hT]; exact hv
  have hpos : 0 < ∑ v ∈ T, cnt_angle S v :=
    Finset.sum_pos' (fun w _ ↦ cnt_angle_nonneg S w)
      ⟨v, hvT, poly_angle_pos hS (extremePoints_subset hv)⟩
  have : (2 : ℝ) < T.card := by linarith
  exact_mod_cast this

private lemma not_mem_interior_of_mem_extremePoints (hS : Convex ℝ S) {v : Fin 2 → ℝ}
    (hv : v ∈ extremePoints ℝ S) : v ∉ interior S := by
  intro hvi
  have h := cnt_tcone_pointed hS hv ![1, 0] (by rw [cnt_tcone_eq_univ hvi]; exact mem_univ _)
    (by rw [cnt_tcone_eq_univ hvi]; exact mem_univ _)
  have := congrFun h 0
  simp at this

private lemma side_angle (hS : Convex ℝ S) {v : Fin 2 → ℝ} (h : IsSidePoint S v) :
    cnt_angle S v = 1 := by
  obtain ⟨w, hw, ε, hε, h⟩ := h
  exact cnt_angle_eq_one_of_halfPlane hS hw hε h

/-- If finitely many non-overlapping convex polygons have angles at `v` adding up to at least `2`,
they cover a neighbourhood of `v`. -/
private lemma ball_subset_of_two_le {ι : Type*} (s : Finset ι) (X : ι → Set (Fin 2 → ℝ))
    (hX : ∀ k ∈ s, IsConvexPolygon (X k))
    (hd : ∀ k ∈ s, ∀ l ∈ s, k ≠ l → Disjoint (interior (X k)) (interior (X l)))
    (v : Fin 2 → ℝ) (h2 : 2 ≤ ∑ k ∈ s, cnt_angle (X k) v) :
    ∃ ε > 0, ball v ε ⊆ ⋃ k ∈ s, X k := by
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ k ∈ s,
      (volume (X k ∩ ball v ε)).toReal = 2 * ε ^ 2 * cnt_angle (X k) v :=
    (eventually_all_finset s).2 fun k hk ↦ poly_volume (hX k hk) v
  obtain ⟨ε, hε, hε0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hε0' : (0 : ℝ) < ε := hε0
  refine ⟨ε, hε0', ?_⟩
  set U := ⋃ k ∈ s, X k with hUdef
  have hUc : IsClosed U := isClosed_biUnion_finset fun k hk ↦ poly_closed (hX k hk)
  have hvol : volume (U ∩ ball v ε) = ∑ k ∈ s, volume (X k ∩ ball v ε) :=
    cnt_volume_biUnion_inter s X (fun k hk ↦ poly_convex (hX k hk)) hd measurableSet_ball
  have hreal : (volume (ball v ε)).toReal ≤ (volume (U ∩ ball v ε)).toReal := by
    rw [hvol, ENNReal.toReal_sum (fun k _ ↦ (cnt_volume_inter_ball_lt_top _ _ _).ne),
      Finset.sum_congr rfl hε, ← Finset.mul_sum, cnt_volume_ball v hε0',
      ENNReal.toReal_ofReal (by positivity)]
    nlinarith [sq_nonneg ε]
  have heq : volume (U ∩ ball v ε) = volume (ball v ε) := by
    refine le_antisymm (measure_mono inter_subset_right) ?_
    exact (ENNReal.toReal_le_toReal measure_ball_lt_top.ne
      (cnt_volume_inter_ball_lt_top _ _ _).ne).1 hreal
  have hnull : volume (ball v ε \ U) = 0 := by
    rw [← sdiff_inter_self_eq_sdiff, measure_sdiff inter_subset_right
      (hUc.measurableSet.inter measurableSet_ball).nullMeasurableSet
      (cnt_volume_inter_ball_lt_top _ _ _).ne, heq, tsub_self]
  have hempty := (((isOpen_ball.sdiff hUc).measure_eq_zero_iff volume).1 hnull)
  exact sdiff_eq_empty.1 hempty

end PolygonFacts

/-! ### Holes -/

section Holes

variable {n : ℕ} {Q : Set (Fin 2 → ℝ)} {C : Fin n → Set (Fin 2 → ℝ)}

private lemma hole_disjoint_cell {H : Set (Fin 2 → ℝ)} (hH : H ∈ holes Q C) (i : Fin n) :
    Disjoint (interior H) (interior (C i)) := by
  obtain ⟨x, -, rfl⟩ := hH
  have h1 : Disjoint (connectedComponentIn (Q \ ⋃ i, C i) x) (interior (C i)) := by
    rw [Set.disjoint_left]
    intro y hy hy'
    exact (connectedComponentIn_subset _ _ hy).2 (mem_iUnion.2 ⟨i, interior_subset hy'⟩)
  exact (h1.closure_left isOpen_interior).mono_left interior_subset

/-- The interior of a hole lies in its component. -/
private lemma interior_hole_subset (hC : ∀ i, IsConvexPolygon (C i)) (hpin : HasPinwheelHoles Q C)
    {H : Set (Fin 2 → ℝ)} (hH : H ∈ holes Q C) {x : Fin 2 → ℝ}
    (hx : H = closure (connectedComponentIn (Q \ ⋃ i, C i) x)) :
    interior H ⊆ connectedComponentIn (Q \ ⋃ i, C i) x := by
  obtain ⟨hHp, hHQ, -⟩ := hpin H hH
  have hF : interior H ⊆ Q \ ⋃ i, C i := by
    intro y hy
    refine ⟨interior_subset (hHQ (interior_subset hy)), fun hyC ↦ ?_⟩
    obtain ⟨i, hyi⟩ := mem_iUnion.1 hyC
    have hcl : C i ⊆ closure (interior (C i)) := by
      rw [(poly_convex (hC i)).closure_interior_eq_closure_of_nonempty_interior (poly_int (hC i))]
      exact subset_closure
    obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.1 (hcl hyi) _ isOpen_interior hy
    exact (hole_disjoint_cell hH i).ne_of_mem hz1 hz2 rfl
  obtain ⟨y, hy⟩ := poly_int hHp
  have hy' : y ∈ closure (connectedComponentIn (Q \ ⋃ i, C i) x) := hx ▸ interior_subset hy
  obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.1 hy' _ isOpen_interior hy
  have := (poly_convex hHp).interior.isPreconnected.subset_connectedComponentIn hz1 hF
  rwa [← connectedComponentIn_eq hz2] at this

/-- Distinct holes do not overlap. -/
private lemma holes_disjoint (hC : ∀ i, IsConvexPolygon (C i)) (hpin : HasPinwheelHoles Q C)
    {H₁ H₂ : Set (Fin 2 → ℝ)} (h₁ : H₁ ∈ holes Q C) (h₂ : H₂ ∈ holes Q C) (hne : H₁ ≠ H₂) :
    Disjoint (interior H₁) (interior H₂) := by
  obtain ⟨x₁, -, hx₁⟩ := id h₁
  obtain ⟨x₂, -, hx₂⟩ := id h₂
  rw [Set.disjoint_left]
  intro y hy₁ hy₂
  have e₁ := interior_hole_subset hC hpin h₁ hx₁ hy₁
  have e₂ := interior_hole_subset hC hpin h₂ hx₂ hy₂
  apply hne
  rw [hx₁, hx₂, connectedComponentIn_eq e₁, connectedComponentIn_eq e₂]

/-- The cells and the holes cover `Q`. -/
private lemma mem_cell_or_hole {y : Fin 2 → ℝ} (hy : y ∈ Q) :
    (∃ i, y ∈ C i) ∨ ∃ H ∈ holes Q C, y ∈ H := by
  by_cases h : ∃ i, y ∈ C i
  · exact Or.inl h
  · right
    have hyF : y ∈ Q \ ⋃ i, C i := ⟨hy, by simpa using h⟩
    exact ⟨_, ⟨y, hyF, rfl⟩, subset_closure (mem_connectedComponentIn hyF)⟩

/-- A point `v + σ perp w` with `|σ| ‖w‖ < δ / 2` is in the closure of the open half-ball
`{y ∈ ball v δ | ⟨w, v⟩ < ⟨w, y⟩}`. -/
private lemma mem_closure_halfBall {v w : Fin 2 → ℝ} {δ σ : ℝ} (hδ : 0 < δ)
    (hσ : |σ| * ‖w‖ < δ / 2) (hw : w ≠ 0) :
    v + σ • cnt_perp w ∈ closure (ball v δ ∩ {y | w ⬝ᵥ v < w ⬝ᵥ y}) := by
  have hc : Continuous fun s : ℝ ↦ v + σ • cnt_perp w + s • w := by fun_prop
  have ht : Tendsto (fun s : ℝ ↦ v + σ • cnt_perp w + s • w) (𝓝[>] 0)
      (𝓝 (v + σ • cnt_perp w)) := by
    have := hc.tendsto 0
    simp only [zero_smul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht ?_
  have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw
  filter_upwards [Ioo_mem_nhdsGT (by positivity : (0 : ℝ) < δ / (2 * ‖w‖))] with s ⟨hs0, hs⟩
  refine ⟨?_, ?_⟩
  · rw [mem_ball, dist_eq_norm, add_assoc, add_sub_cancel_left]
    calc ‖σ • cnt_perp w + s • w‖ ≤ ‖σ • cnt_perp w‖ + ‖s • w‖ := norm_add_le _ _
      _ = |σ| * ‖w‖ + s * ‖w‖ := by
        rw [norm_smul, norm_smul, cnt_norm_perp, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_pos hs0]
      _ < δ / 2 + δ / 2 := by
        have : s * ‖w‖ < δ / 2 := by
          rw [lt_div_iff₀ (by positivity)] at hs
          linarith
        linarith
      _ = δ := by ring
  · change w ⬝ᵥ v < w ⬝ᵥ (v + σ • cnt_perp w + s • w)
    rw [dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul, cnt_dot_perp_self,
      smul_eq_mul, smul_eq_mul, mul_zero, add_zero]
    have := cnt_dot_self_pos hw
    nlinarith

/-- **Every corner of a hole is a corner of a cell.** By `HasPinwheelHoles` the corner `v` is a
side point of a cell `C j`. If `v` were a corner of no cell, then no other cell would contain `v`
(two cells with angles `≥ 1` at `v` would cover a neighbourhood of `v`, but `v` is in the closure of
`Q \ ⋃ C i`), so near `v` the complement of `C j` is an open half-ball avoiding all cells; it is
connected and meets the component of the hole, so it lies in the hole, and then `v` is the
midpoint of a segment in the hole. -/
private lemma hole_corner_mem (hC : ∀ i, IsConvexPolygon (C i)) (hdisj : NonOverlapping C)
    (hpin : HasPinwheelHoles Q C) {H : Set (Fin 2 → ℝ)} (hH : H ∈ holes Q C) {v : Fin 2 → ℝ}
    (hv : v ∈ extremePoints ℝ H) : ∃ i, v ∈ extremePoints ℝ (C i) := by
  classical
  obtain ⟨hHp, hHQ, hside⟩ := hpin H hH
  obtain ⟨j, hj⟩ := hside v hv
  by_contra hno
  push Not at hno
  have hθj : cnt_angle (C j) v = 1 := side_angle (poly_convex (hC j)) hj
  obtain ⟨w, hw, ε, hε, hjloc⟩ := hj
  obtain ⟨x, hxF, hxH⟩ := hH
  set F := Q \ ⋃ i, C i with hFdef
  have hvH : v ∈ closure (connectedComponentIn F x) := hxH ▸ extremePoints_subset hv
  -- the other cells avoid `v`
  have hother : ∀ i, i ≠ j → v ∉ C i := by
    intro i hij hvi
    have hθi : 1 ≤ cnt_angle (C i) v := by
      rcases poly_angle_nat (hC i) (hno i) with h | h | h
      · exact absurd h (poly_angle_pos (hC i) hvi).ne'
      · exact h.ge
      · rw [h]; norm_num
    obtain ⟨δ, hδ, hball⟩ := ball_subset_of_two_le {i, j} C (fun k _ ↦ hC k)
      (fun k _ l _ hkl ↦ hdisj hkl) v (by
        rw [Finset.sum_pair hij]
        linarith)
    obtain ⟨y, hy, hyd⟩ := Metric.mem_closure_iff.1 hvH δ hδ
    have hyB : y ∈ ball v δ := by rw [mem_ball, dist_comm]; exact hyd
    obtain ⟨k, -, hk⟩ := mem_iUnion₂.1 (hball hyB)
    exact (connectedComponentIn_subset _ _ hy).2 (mem_iUnion.2 ⟨k, hk⟩)
  -- a ball around `v` inside `interior Q` meeting no other cell
  have hev : ∀ᶠ y in 𝓝 v, y ∈ interior Q ∧ ∀ i, i ≠ j → y ∉ C i := by
    refine (show ∀ᶠ y in 𝓝 v, y ∈ interior Q from
      isOpen_interior.mem_nhds (hHQ (extremePoints_subset hv))).and ?_
    rw [eventually_all]
    intro i
    by_cases hij : i = j
    · exact Eventually.of_forall fun y h ↦ absurd hij h
    · exact (show ∀ᶠ y in 𝓝 v, y ∈ (C i)ᶜ from
        (poly_closed (hC i)).isOpen_compl.mem_nhds (hother i hij)).mono fun y hy _ ↦ hy
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.eventually_nhds_iff.1 hev
  set δ := min δ₀ ε with hδdef
  have hδ : 0 < δ := lt_min hδ₀ hε
  set D := ball v δ ∩ {y | w ⬝ᵥ v < w ⬝ᵥ y} with hDdef
  have hDF : D ⊆ F := by
    rintro y ⟨hyb, hyw⟩
    rw [mem_ball] at hyb
    have hy := hball (hyb.trans_le (min_le_left _ _))
    refine ⟨interior_subset hy.1, fun hyC ↦ ?_⟩
    obtain ⟨i, hyi⟩ := mem_iUnion.1 hyC
    by_cases hij : i = j
    · subst hij
      have := (hjloc y (hyb.trans_le (min_le_right _ _))).1 hyi
      rw [dotProduct_sub] at this
      change w ⬝ᵥ v < w ⬝ᵥ y at hyw
      linarith
    · exact hy.2 i hij hyi
  have hDconv : Convex ℝ D := (convex_ball v δ).inter
    (convex_halfSpace_gt ⟨fun x y ↦ dotProduct_add _ _ _, fun r x ↦ dotProduct_smul r _ _⟩ _)
  -- the component of the hole meets `D`
  obtain ⟨y₀, hy₀, hy₀d⟩ := Metric.mem_closure_iff.1 hvH δ hδ
  have hy₀D : y₀ ∈ D := by
    have hy₀b : dist y₀ v < δ := by rw [dist_comm]; exact hy₀d
    refine ⟨hy₀b, ?_⟩
    have hnot : y₀ ∉ C j := fun h ↦
      (connectedComponentIn_subset _ _ hy₀).2 (mem_iUnion.2 ⟨j, h⟩)
    have := mt (hjloc y₀ (hy₀b.trans_le (min_le_right _ _))).2 hnot
    rw [dotProduct_sub, not_le] at this
    change w ⬝ᵥ v < w ⬝ᵥ y₀
    linarith
  have hDH : D ⊆ H := by
    have := hDconv.isPreconnected.subset_connectedComponentIn hy₀D hDF
    rw [← connectedComponentIn_eq hy₀] at this
    rw [hxH]
    exact this.trans subset_closure
  have hclH : closure D ⊆ H := (poly_closed hHp).closure_subset_iff.2 hDH
  -- `v ± t perp w ∈ H`, so `v` is not a corner of `H`
  set t := δ / (4 * ‖w‖) with htdef
  have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw
  have ht : 0 < t := by positivity
  have htw : |t| * ‖w‖ < δ / 2 := by
    rw [abs_of_pos ht, htdef, div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) two_pos]
    nlinarith
  have htw' : |-t| * ‖w‖ < δ / 2 := by rwa [abs_neg]
  have h1 := hclH (mem_closure_halfBall hδ htw hw)
  have h2 := hclH (mem_closure_halfBall hδ htw' hw)
  rw [neg_smul, ← sub_eq_add_neg] at h2
  have := cnt_eq_zero_of_mem_extremePoints hv h1 h2
  exact cnt_perp_ne_zero hw ((smul_eq_zero.1 this).resolve_left ht.ne')

/-- There are finitely many holes: a hole is the closed convex hull of its corners, which are
corners of cells. -/
private lemma holes_finite (hC : ∀ i, IsConvexPolygon (C i)) (hdisj : NonOverlapping C)
    (hpin : HasPinwheelHoles Q C) : (holes Q C).Finite := by
  have hV : (⋃ i, extremePoints ℝ (C i)).Finite := finite_iUnion fun i ↦ poly_finite (hC i)
  refine (hV.finite_subsets.image fun E ↦ closure (convexHull ℝ E)).subset ?_
  intro H hH
  obtain ⟨hHp, -, -⟩ := hpin H hH
  refine ⟨extremePoints ℝ H, fun v hv ↦ ?_,
    closure_convexHull_extremePoints (poly_compact hHp) (poly_convex hHp)⟩
  obtain ⟨i, hi⟩ := hole_corner_mem hC hdisj hpin hH hv
  exact mem_iUnion.2 ⟨i, hi⟩

end Holes

/-! ### The corners of `Q` -/

/-- Of three points on a line, the middle one (in the order along the line) is in the open
segment of the other two. -/
private lemma mem_openSegment_of_line {b : Fin 2 → ℝ} {d : ℝ} (hb : b ≠ 0) {x y z : Fin 2 → ℝ}
    (hx : b ⬝ᵥ x = d) (hy : b ⬝ᵥ y = d) (hz : b ⬝ᵥ z = d)
    (hxy : cnt_perp b ⬝ᵥ x < cnt_perp b ⬝ᵥ y) (hyz : cnt_perp b ⬝ᵥ y < cnt_perp b ⬝ᵥ z) :
    y ∈ openSegment ℝ x z := by
  have hD : 0 < cnt_perp b ⬝ᵥ z - cnt_perp b ⬝ᵥ x := by linarith
  have key : ∀ u, b ⬝ᵥ u = 0 → cnt_perp b ⬝ᵥ u = 0 → u = 0 := by
    intro u h1 h2
    rw [cnt_eq_smul_of_perp_dot_eq_zero hb h2, h1, zero_div, zero_smul]
  refine ⟨(cnt_perp b ⬝ᵥ z - cnt_perp b ⬝ᵥ y) / (cnt_perp b ⬝ᵥ z - cnt_perp b ⬝ᵥ x),
    (cnt_perp b ⬝ᵥ y - cnt_perp b ⬝ᵥ x) / (cnt_perp b ⬝ᵥ z - cnt_perp b ⬝ᵥ x),
    div_pos (by linarith) hD, div_pos (by linarith) hD, ?_, ?_⟩
  · rw [← add_div, div_eq_one_iff_eq hD.ne']
    ring
  · apply sub_eq_zero.1
    apply key
    · rw [dotProduct_sub, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul,
        smul_eq_mul, hx, hz, hy]
      field_simp
      ring
    · rw [dotProduct_sub, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul,
        smul_eq_mul]
      field_simp
      ring

/-- A line contains at most two corners of a set. -/
private lemma card_le_two_of_line {S : Set (Fin 2 → ℝ)} {b : Fin 2 → ℝ} {d : ℝ} (hb : b ≠ 0)
    (F : Finset (Fin 2 → ℝ)) (hF : ∀ v ∈ F, v ∈ extremePoints ℝ S ∧ b ⬝ᵥ v = d) :
    F.card ≤ 2 := by
  classical
  by_contra hlt
  push Not at hlt
  have hne : F.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨v₁, hv₁, hmin⟩ := F.exists_min_image (fun v ↦ cnt_perp b ⬝ᵥ v) hne
  obtain ⟨v₃, hv₃, hmax⟩ := F.exists_max_image (fun v ↦ cnt_perp b ⬝ᵥ v) hne
  obtain ⟨v₂, hv₂, h21, h23⟩ : ∃ v₂ ∈ F, v₂ ≠ v₁ ∧ v₂ ≠ v₃ := by
    by_contra hcon
    push Not at hcon
    have hsub : F ⊆ {v₁, v₃} := fun v hv ↦ by
      rcases eq_or_ne v v₁ with h | h
      · simp [h]
      · simp [hcon v hv h]
    have := (Finset.card_le_card hsub).trans Finset.card_le_two
    omega
  have key : ∀ u w, b ⬝ᵥ u = d → b ⬝ᵥ w = d → cnt_perp b ⬝ᵥ u = cnt_perp b ⬝ᵥ w → u = w := by
    intro u w hu hw h
    have h1 : b ⬝ᵥ (u - w) = 0 := by rw [dotProduct_sub, hu, hw, sub_self]
    have h2 : cnt_perp b ⬝ᵥ (u - w) = 0 := by rw [dotProduct_sub, h, sub_self]
    have := cnt_eq_smul_of_perp_dot_eq_zero hb h2
    rw [h1, zero_div, zero_smul] at this
    exact sub_eq_zero.1 this
  have hlt1 : cnt_perp b ⬝ᵥ v₁ < cnt_perp b ⬝ᵥ v₂ := lt_of_le_of_ne (hmin v₂ hv₂)
    fun h ↦ h21 (key _ _ (hF _ hv₂).2 (hF _ hv₁).2 h.symm)
  have hlt2 : cnt_perp b ⬝ᵥ v₂ < cnt_perp b ⬝ᵥ v₃ := lt_of_le_of_ne (hmax v₂ hv₂)
    fun h ↦ h23 (key _ _ (hF _ hv₂).2 (hF _ hv₃).2 h)
  have hseg := mem_openSegment_of_line hb (hF _ hv₁).2 (hF _ hv₂).2 (hF _ hv₃).2 hlt1 hlt2
  have := ((mem_extremePoints.1 (hF _ hv₂).1).2 _ (extremePoints_subset (hF _ hv₁).1) _
    (extremePoints_subset (hF _ hv₃).1) hseg).1
  exact h21 this.symm

/-- A polygon cut out by `m` half-planes has at most `m` corners: each corner lies on two lines
with independent normals, and each line carries at most two corners. -/
private lemma ncard_extremePoints_le {m : ℕ} (b : Fin m → Fin 2 → ℝ) (d : Fin m → ℝ) :
    (extremePoints ℝ (halfPlanesInter b d)).ncard ≤ m := by
  classical
  have hfin : (extremePoints ℝ (halfPlanesInter b d)).Finite := cnt_extremePoints_finite
  rw [Set.ncard_eq_toFinset_card _ hfin]
  set E := hfin.toFinset with hEdef
  set P : (Fin 2 → ℝ) → Fin m → Prop := fun v j ↦ b j ⬝ᵥ v = d j ∧ b j ≠ 0 with hPdef
  have h2 : ∀ v ∈ E, 2 ≤ (Finset.univ.filter (P v)).card := by
    intro v hv
    rw [Set.Finite.mem_toFinset] at hv
    obtain ⟨i, j, hi, hj, hij⟩ := cnt_exists_active_indep hv
    have hi0 : b i ≠ 0 := by
      rintro h
      rw [h, map_zero, zero_dotProduct] at hij
      exact hij rfl
    have hj0 : b j ≠ 0 := by
      rintro h
      rw [h, dotProduct_zero] at hij
      exact hij rfl
    have hne : i ≠ j := by
      rintro rfl
      exact hij (cnt_perp_dot_self _)
    have hsub : ({i, j} : Finset (Fin m)) ⊆ Finset.univ.filter (P v) := by
      intro k hk
      rw [Finset.mem_insert, Finset.mem_singleton] at hk
      rw [Finset.mem_filter]
      rcases hk with rfl | rfl
      exacts [⟨Finset.mem_univ _, hi, hi0⟩, ⟨Finset.mem_univ _, hj, hj0⟩]
    have := Finset.card_le_card hsub
    rwa [Finset.card_pair hne] at this
  have hline : ∀ j, (E.filter fun v ↦ P v j).card ≤ 2 := by
    intro j
    by_cases hb : b j = 0
    · have : (E.filter fun v ↦ P v j) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro v _ hv
        exact hv.2 hb
      rw [this, Finset.card_empty]
      norm_num
    · refine card_le_two_of_line (S := halfPlanesInter b d) (d := d j) hb _ fun v hv ↦ ?_
      rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hv
      exact ⟨hv.1, hv.2.1⟩
  have hcount : ∑ v ∈ E, (Finset.univ.filter (P v)).card =
      ∑ j, (E.filter fun v ↦ P v j).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hle1 : 2 * E.card ≤ ∑ v ∈ E, (Finset.univ.filter (P v)).card := by
    rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum h2
  have hle2 : ∑ j, (E.filter fun v ↦ P v j).card ≤ 2 * m := by
    calc ∑ j, (E.filter fun v ↦ P v j).card ≤ ∑ _j : Fin m, 2 := Finset.sum_le_sum fun j _ ↦ hline j
      _ = 2 * m := by simp [mul_comm]
  omega

/-! ### The local identity -/

/-- **Angles add up.** At every point `p`, the angles at `p` of the cells and of the holes add up
to the angle of `Q` at `p`: the cells and holes are non-overlapping convex polygons covering `Q`,
so the areas of their intersections with a small ball around `p` add up. -/
private lemma local_identity {n : ℕ} {Q : Set (Fin 2 → ℝ)} (hQp : IsConvexPolygon Q)
    {C : Fin n → Set (Fin 2 → ℝ)} (hC : ∀ i, IsConvexPolygon (C i)) (hCQ : ∀ i, C i ⊆ Q)
    (hdisj : NonOverlapping C) (hpin : HasPinwheelHoles Q C) (hHfin : (holes Q C).Finite)
    (p : Fin 2 → ℝ) :
    ∑ i, cnt_angle (C i) p + ∑ H ∈ hHfin.toFinset, cnt_angle H p = cnt_angle Q p := by
  classical
  set s : Finset (Fin n ⊕ Set (Fin 2 → ℝ)) := Finset.univ.disjSum hHfin.toFinset with hsdef
  set X : Fin n ⊕ Set (Fin 2 → ℝ) → Set (Fin 2 → ℝ) := Sum.elim C id with hXdef
  have hmem : ∀ {H}, Sum.inr H ∈ s → H ∈ holes Q C := fun hk ↦
    hHfin.mem_toFinset.1 (Finset.inr_mem_disjSum.1 hk)
  have hXp : ∀ k ∈ s, IsConvexPolygon (X k) := by
    rintro (i | H) hk
    · exact hC i
    · exact (hpin H (hmem hk)).1
  have hXd : ∀ k ∈ s, ∀ l ∈ s, k ≠ l → Disjoint (interior (X k)) (interior (X l)) := by
    rintro (i | H) hk (j | H') hl hkl
    · exact hdisj fun h ↦ hkl (congrArg Sum.inl h)
    · exact (hole_disjoint_cell (hmem hl) i).symm
    · exact hole_disjoint_cell (hmem hk) j
    · exact holes_disjoint hC hpin (hmem hk) (hmem hl) fun h ↦ hkl (congrArg Sum.inr h)
  have hU : (⋃ k ∈ s, X k) = Q := by
    apply Subset.antisymm
    · refine iUnion₂_subset ?_
      rintro (i | H) hk
      · exact hCQ i
      · exact ((hpin H (hmem hk)).2.1).trans interior_subset
    · intro y hy
      rcases mem_cell_or_hole hy with ⟨i, hi⟩ | ⟨H, hH, hyH⟩
      · exact mem_biUnion (x := Sum.inl i) (Finset.inl_mem_disjSum.2 (Finset.mem_univ i)) hi
      · exact mem_biUnion (x := Sum.inr H) (Finset.inr_mem_disjSum.2 (hHfin.mem_toFinset.2 hH))
          hyH
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (volume (Q ∩ ball p ε)).toReal = 2 * ε ^ 2 * cnt_angle Q p ∧
      ∀ k ∈ s, (volume (X k ∩ ball p ε)).toReal = 2 * ε ^ 2 * cnt_angle (X k) p :=
    (poly_volume hQp p).and ((eventually_all_finset s).2 fun k hk ↦ poly_volume (hXp k hk) p)
  obtain ⟨ε, ⟨hεQ, hεX⟩, hε0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hε0' : (0 : ℝ) < ε := hε0
  have hvol := cnt_volume_biUnion_inter s X (fun k hk ↦ poly_convex (hXp k hk)) hXd
    (measurableSet_ball (x := p) (ε := ε))
  rw [hU] at hvol
  have h := congrArg ENNReal.toReal hvol
  rw [ENNReal.toReal_sum (fun k _ ↦ (cnt_volume_inter_ball_lt_top _ _ _).ne), hεQ,
    Finset.sum_congr rfl hεX, ← Finset.mul_sum, Finset.sum_disjSum] at h
  have hε2 : (0 : ℝ) < 2 * ε ^ 2 := by positivity
  exact (mul_left_cancel₀ hε2.ne' h).symm

/-! ### (C2) The side count -/

/-- **(C2) The side count.** Let `Q = halfPlanesInter b d` (`m` half-planes) be bounded and
`C 0, …, C (n-1)`, `n ≥ 1`, non-overlapping convex polygons in `Q` with pinwheel holes
(`HasPinwheelHoles`). Then the numbers `N i` of corners (extreme points) of the cells satisfy
`∑ N i ≤ 6n + m - 6`, i.e. `∑ N i + 6 ≤ 6n + m`.

Argument (an angle count; no Euler formula or Jordan curve theorem). For a closed convex set `S`
and a point `p` let `θ_p(S) ∈ [0, 2π]` be the angle of `S` at `p`:
`|S ∩ B(p, ε)| = θ_p(S) ε²/2` for all small `ε` (`B` the Euclidean disk), so `θ_p = 0` off `S`,
`π` at a side point, `2π` at an interior point, and `θ_p(P) = π - (gap between the outer normals
of the two sides at p) ∈ (0, π)` at a corner of a polygon `P`.
(1) *Angle sum.* For a convex polygon `P` with `N` corners, `∑_{corners} θ_v(P) = (N - 2)π`: the
exterior angles `π - θ_v` are the gaps between consecutive outer normals in angular order, which
sum to `2π`.
(2) *Local count.* Write `A_p = ∑ θ_p(C i)` over the cells having a corner at `p`, and `c_p` for
their number. The cells and the holes cover `Q` and do not overlap, so at every point `p`,
`∑_i θ_p(C i) + ∑_H θ_p(H) = θ_p(Q)` (compare areas in `B(p, ε)`; boundaries are null sets).
Each corner angle is `< π`; side points contribute `π`. Two distinct holes cannot share a
boundary segment (they would be one connected component), and the boundary of a hole is covered
by cell sides. Hence:
* at `p ∈ interior Q` not a corner of a hole: if `p` is in the interior of a cell or hole,
  `A_p = 0`; if `p` is a side point of a hole, the other half-disk is a cell side (`A_p = 0`) or
  is filled by `c_p ≥ 2` corners (`A_p = π`); otherwise cells fill `2π` with `t ≤ 2` side points
  and corners, giving `A_p = 0`, or `A_p = π` with `c_p ≥ 2`, or `A_p = 2π` with `c_p ≥ 3`.
  In all cases `A_p ≤ (2/3)π c_p`;
* on a side of `Q` (the cells cover `∂Q` since the holes lie in `interior Q`):
  `A_p ∈ {0, π}`, with `c_p ≥ 2` if `A_p = π`; so again `A_p ≤ (2/3)π c_p`;
* at a corner of `Q` with angle `γ_p`: `A_p = γ_p` and `c_p ≥ 1`;
* at a point `v` which is a corner of `r_v ≥ 1` holes: by `HasPinwheelHoles` exactly one cell
  has `v` as a side point (two would leave no room), so
  `A_v = π - ∑_{H ∋ v} θ_v(H) > 0`, `c_v ≥ 1`, and `c_v ≥ r_v - 1` (consecutive holes around `v`
  are separated by cell corners). Summing over all hole corners, with `∑_{v ∈ H} θ_v(H) =
  (k_H - 2)π` for a hole with `k_H ≥ 3` corners and `h ≤ (∑_v r_v)/3` holes:
  `∑_v A_v = ∑_v π - ∑_H (k_H - 2)π ≤ π ∑_v (1 - r_v/3) ≤ (2/3)π ∑_v max(1, r_v - 1)
  ≤ (2/3)π ∑_v c_v` (pointwise `1 - r/3 ≤ (2/3) max(1, r - 1)`).
(3) *Summation.* With (1), `∑_i (N i - 2)π = ∑_p A_p`; by (2), splitting off the `m' ≤ m`
corners of `Q` (where `∑ γ_p = (m' - 2)π` and `c_p ≥ 1`),
`∑_p A_p ≤ (2/3)π (∑_i N i - m') + (m' - 2)π`, i.e. `∑ N i ≤ 6n + m' - 6 ≤ 6n + m - 6`.

Formalized argument. Angles are measured by area (`cnt_angle`, in units of `π`, with the sup-norm
unit ball in place of the Euclidean disk: only its invariance under the quarter turn and under
`x ↦ -x` matters), see `Basic.Analysis.Convex.PolygonAngle`; the angle sum (1) is proved there
with the normal fan (the normal cones at the corners tile the plane, and the angle of the normal
cone at a corner is `π` minus the angle there), without sorting the normals by angle. The count
(2)–(3) is organized as follows, with `A_p`, `c_p` as above, `I_p`, `J_p` the sums of the angles
of the cells and of the holes not having a corner at `p` (integers `0, 1, 2` each), and `B_p` the
sum of the corner angles of the holes at `p`; the local identity reads `A_p + I_p + B_p + J_p =
θ_p(Q)`. Only cell corners `p` matter (`A_p = 0` elsewhere), and `A_p < c_p` there.
* corners of `Q`: `A_p ≤ γ_p`; every corner of `Q` is a cell corner (else `I_p = γ_p ∈ (0, 1)`
  would be an integer);
* hole corners `p`: `θ_p(Q) = 2` and the side-point cell gives `I_p ≥ 1`, so `A_p ≤ 1 - B_p`;
  every hole corner is a cell corner (if not, the cell `C j` with side point `p` would be the
  only cell near `p`, and the open half-ball outside `C j` would lie in the hole, making `p` the
  midpoint of a segment of the hole); so `c_p ≥ 1`, and the hole corners contribute
  `∑ (1 - B_p) = #HC - ∑_H (k_H - 2) ≤ #HC - #HC/3 ≤ (2/3) ∑ c_p` (`#HC ≤ ∑_H k_H` and
  `k_H ≥ 3`); the bound `c_p ≥ r_p - 1` is not needed;
* other cell corners: `A_p = θ_p(Q) - I_p - J_p` is an integer in `[0, 2]` with `A_p < c_p`,
  so `3 A_p ≤ 2 c_p` (this replaces the case analysis above; sides of `Q` are included).
The holes are finitely many (each is the closed convex hull of its corners, which are cell
corners), distinct holes do not overlap, and `Q` has `m' ≤ m` corners (each corner lies on two
of the lines with independent normals, each line carries at most two corners). -/
theorem sum_ncard_extremePoints_add_six_le {m n : ℕ} (hn : 1 ≤ n) (b : Fin m → Fin 2 → ℝ)
    (d : Fin m → ℝ) (hQ : Bornology.IsBounded (halfPlanesInter b d))
    (C : Fin n → Set (Fin 2 → ℝ)) (hC : ∀ i, IsConvexPolygon (C i))
    (hCQ : ∀ i, C i ⊆ halfPlanesInter b d) (hdisj : NonOverlapping C)
    (hpin : HasPinwheelHoles (halfPlanesInter b d) C) :
    ∑ i, (extremePoints ℝ (C i)).ncard + 6 ≤ 6 * n + m := by
  classical
  set Q := halfPlanesInter b d with hQdef
  have hQint : (interior Q).Nonempty :=
    (poly_int (hC ⟨0, hn⟩)).mono (interior_mono (hCQ _))
  have hQp : IsConvexPolygon Q := ⟨⟨m, b, d, rfl⟩, hQ, hQint⟩
  -- the holes
  have hHfin : (holes Q C).Finite := holes_finite hC hdisj hpin
  set 𝓗 := hHfin.toFinset with h𝓗
  have hmem𝓗 : ∀ H, H ∈ 𝓗 ↔ H ∈ holes Q C := fun H ↦ hHfin.mem_toFinset
  have hHp : ∀ H ∈ 𝓗, IsConvexPolygon H := fun H hH ↦ (hpin H ((hmem𝓗 H).1 hH)).1
  have hHQ : ∀ H ∈ 𝓗, H ⊆ interior Q := fun H hH ↦ (hpin H ((hmem𝓗 H).1 hH)).2.1
  have hloc := local_identity hQp hC hCQ hdisj hpin hHfin
  -- the corners of the cells
  have hfinC : ∀ i, (extremePoints ℝ (C i)).Finite := fun i ↦ poly_finite (hC i)
  set V : Finset (Fin 2 → ℝ) := Finset.univ.biUnion fun i ↦ (hfinC i).toFinset with hVdef
  have hmemV : ∀ p, p ∈ V ↔ ∃ i, p ∈ extremePoints ℝ (C i) := by
    intro p
    simp [hVdef]
  -- the quantities at a point `p`: `A p` (corner angles of cells), `I p` (other angles of cells),
  -- `B p`, `J p` (the same for holes), `c p` (the number of cells with a corner at `p`)
  obtain ⟨A, hA⟩ : ∃ A : (Fin 2 → ℝ) → ℝ, ∀ p, A p =
      ∑ i, if p ∈ extremePoints ℝ (C i) then cnt_angle (C i) p else 0 := ⟨_, fun _ ↦ rfl⟩
  obtain ⟨I, hI⟩ : ∃ I : (Fin 2 → ℝ) → ℝ, ∀ p, I p =
      ∑ i, if p ∈ extremePoints ℝ (C i) then 0 else cnt_angle (C i) p := ⟨_, fun _ ↦ rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : (Fin 2 → ℝ) → ℝ, ∀ p, B p =
      ∑ H ∈ 𝓗, if p ∈ extremePoints ℝ H then cnt_angle H p else 0 := ⟨_, fun _ ↦ rfl⟩
  obtain ⟨J, hJ⟩ : ∃ J : (Fin 2 → ℝ) → ℝ, ∀ p, J p =
      ∑ H ∈ 𝓗, if p ∈ extremePoints ℝ H then 0 else cnt_angle H p := ⟨_, fun _ ↦ rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : (Fin 2 → ℝ) → ℕ, ∀ p, c p =
      (Finset.univ.filter fun i ↦ p ∈ extremePoints ℝ (C i)).card := ⟨_, fun _ ↦ rfl⟩
  have hsum4 : ∀ p, A p + I p + B p + J p = cnt_angle Q p := by
    intro p
    rw [← hloc p, hA, hI, hB, hJ, add_assoc (∑ i, _ + _), ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    congr 1
    · exact Finset.sum_congr rfl fun i _ ↦ by split_ifs <;> simp
    · exact Finset.sum_congr rfl fun H _ ↦ by split_ifs <;> simp
  have hA0 : ∀ p, 0 ≤ A p := fun p ↦ by
    rw [hA]; exact Finset.sum_nonneg fun i _ ↦ by split_ifs; exacts [cnt_angle_nonneg _ _, le_rfl]
  have hI0 : ∀ p, 0 ≤ I p := fun p ↦ by
    rw [hI]; exact Finset.sum_nonneg fun i _ ↦ by split_ifs; exacts [le_rfl, cnt_angle_nonneg _ _]
  have hB0 : ∀ p, 0 ≤ B p := fun p ↦ by
    rw [hB]; exact Finset.sum_nonneg fun H _ ↦ by split_ifs; exacts [cnt_angle_nonneg _ _, le_rfl]
  have hJ0 : ∀ p, 0 ≤ J p := fun p ↦ by
    rw [hJ]; exact Finset.sum_nonneg fun H _ ↦ by split_ifs; exacts [le_rfl, cnt_angle_nonneg _ _]
  -- angles away from corners are integers
  have hint : ∀ {S : Set (Fin 2 → ℝ)} {p : Fin 2 → ℝ}, IsConvexPolygon S →
      ∃ z : ℤ, (if p ∈ extremePoints ℝ S then 0 else cnt_angle S p) = z := by
    intro S p hS
    split_ifs with h
    · exact ⟨0, by simp⟩
    · rcases poly_angle_nat hS h with h' | h' | h'
      · exact ⟨0, by simp [h']⟩
      · exact ⟨1, by simp [h']⟩
      · exact ⟨2, by simp [h']⟩
  have hIint : ∀ p, ∃ z : ℤ, I p = z := by
    intro p
    choose! g hg using fun i (_ : i ∈ Finset.univ) ↦ hint (p := p) (hC i)
    exact ⟨∑ i, g i, by rw [hI, Int.cast_sum]; exact Finset.sum_congr rfl hg⟩
  have hJint : ∀ p, ∃ z : ℤ, J p = z := by
    intro p
    choose! g hg using fun H (hH : H ∈ 𝓗) ↦ hint (p := p) (hHp H hH)
    exact ⟨∑ H ∈ 𝓗, g H, by rw [hJ, Int.cast_sum]; exact Finset.sum_congr rfl hg⟩
  -- at a corner of a cell, `A p < c p`
  have hc1 : ∀ p ∈ V, 1 ≤ c p := by
    intro p hp
    obtain ⟨i, hi⟩ := (hmemV p).1 hp
    rw [hc]
    exact Finset.card_pos.2 ⟨i, by simp [hi]⟩
  have hAc : ∀ p ∈ V, A p < c p := by
    intro p hp
    obtain ⟨i, hi⟩ := (hmemV p).1 hp
    rw [hA, hc, Finset.natCast_card_filter]
    refine Finset.sum_lt_sum (fun j _ ↦ ?_) ⟨i, Finset.mem_univ _, ?_⟩
    · split_ifs with h
      exacts [(poly_angle_lt_one (hC j) h).le, le_rfl]
    · simp only [ite_eq_left hi]
      exact poly_angle_lt_one (hC i) hi
  -- corners of `Q` are not in the holes
  have hQext : ∀ p ∈ extremePoints ℝ Q, ∀ H ∈ 𝓗, p ∉ H := fun p hp H hH hpH ↦
    not_mem_interior_of_mem_extremePoints (poly_convex hQp) hp (hHQ H hH hpH)
  -- every corner of `Q` is a corner of a cell
  have hQV : ∀ p ∈ extremePoints ℝ Q, p ∈ V := by
    intro p hp
    by_contra hpV
    have hA' : A p = 0 := by
      rw [hA]
      exact Finset.sum_eq_zero fun i _ ↦ ite_eq_right fun h ↦ hpV ((hmemV p).2 ⟨i, h⟩)
    have hB' : B p = 0 := by
      rw [hB]
      exact Finset.sum_eq_zero fun H hH ↦
        ite_eq_right fun h ↦ hQext p hp H hH (extremePoints_subset h)
    have hJ' : J p = 0 := by
      rw [hJ]
      refine Finset.sum_eq_zero fun H hH ↦ ?_
      split_ifs
      · rfl
      · exact cnt_angle_of_not_mem (hQext p hp H hH)
    have h := hsum4 p
    obtain ⟨z, hz⟩ := hIint p
    have h1 := poly_angle_pos hQp (extremePoints_subset hp)
    have h2 := poly_angle_lt_one hQp hp
    rw [hA', hB', hJ', hz] at h
    have hz0 : (0 : ℝ) < z := by linarith
    have hz1 : (z : ℝ) < 1 := by linarith
    have hz0' : 0 < z := by exact_mod_cast hz0
    have hz1' : z < 1 := by exact_mod_cast hz1
    omega
  -- the corners of holes
  set HC := V.filter fun p ↦ ∃ H ∈ 𝓗, p ∈ extremePoints ℝ H with hHCdef
  have hHC : ∀ H ∈ 𝓗, ∀ p ∈ extremePoints ℝ H, p ∈ HC := by
    intro H hH p hp
    obtain ⟨i, hi⟩ := hole_corner_mem hC hdisj hpin ((hmem𝓗 H).1 hH) hp
    exact Finset.mem_filter.2 ⟨(hmemV p).2 ⟨i, hi⟩, H, hH, hp⟩
  -- the pointwise inequality
  obtain ⟨g, hg⟩ : ∃ g : (Fin 2 → ℝ) → ℝ, ∀ p, g p =
      (if p ∈ extremePoints ℝ Q then 3 * cnt_angle Q p - 2 else 0) +
        (if p ∈ HC then 1 - 3 * B p else 0) := ⟨_, fun _ ↦ rfl⟩
  have hpt : ∀ p ∈ V, 3 * A p ≤ 2 * (c p : ℝ) + g p := by
    intro p hp
    have hcp : (1 : ℝ) ≤ c p := by exact_mod_cast hc1 p hp
    have h := hsum4 p
    by_cases hpQ : p ∈ extremePoints ℝ Q
    · -- a corner of `Q`
      have hnHC : p ∉ HC := fun h' ↦ by
        obtain ⟨-, H, hH, hpH⟩ := Finset.mem_filter.1 h'
        exact hQext p hpQ H hH (extremePoints_subset hpH)
      rw [hg, ite_eq_left hpQ, ite_eq_right hnHC, add_zero]
      linarith [hI0 p, hB0 p, hJ0 p]
    · by_cases hpH : p ∈ HC
      · -- a corner of a hole: a cell has `p` as a side point
        obtain ⟨-, H₀, hH₀, hpH₀⟩ := Finset.mem_filter.1 hpH
        have hθQ : cnt_angle Q p = 2 :=
          cnt_angle_of_mem_interior (hHQ H₀ hH₀ (extremePoints_subset hpH₀))
        obtain ⟨j, hj⟩ := (hpin H₀ ((hmem𝓗 H₀).1 hH₀)).2.2 p hpH₀
        have hθj : cnt_angle (C j) p = 1 := side_angle (poly_convex (hC j)) hj
        have hjext : p ∉ extremePoints ℝ (C j) := fun h' ↦ by
          have := poly_angle_lt_one (hC j) h'
          linarith
        have hI1 : 1 ≤ I p := by
          have := Finset.single_le_sum (f := fun i ↦
            if p ∈ extremePoints ℝ (C i) then 0 else cnt_angle (C i) p)
            (fun i _ ↦ by split_ifs; exacts [le_rfl, cnt_angle_nonneg _ _]) (Finset.mem_univ j)
          simp only [ite_eq_right hjext, hθj] at this
          rw [hI]
          exact this
        rw [hg, ite_eq_right hpQ, ite_eq_left hpH, zero_add]
        rw [hθQ] at h
        linarith [hJ0 p]
      · -- any other corner of a cell: `A p` is an integer `≤ 2`
        have hB' : B p = 0 := by
          rw [hB]
          exact Finset.sum_eq_zero fun H hH ↦
            ite_eq_right fun h' ↦ hpH (Finset.mem_filter.2 ⟨hp, H, hH, h'⟩)
        rw [hg, ite_eq_right hpQ, ite_eq_right hpH, add_zero]
        obtain ⟨zI, hzI⟩ := hIint p
        obtain ⟨zJ, hzJ⟩ := hJint p
        obtain ⟨zQ, hzQ, hzQ2⟩ : ∃ z : ℤ, cnt_angle Q p = z ∧ z ≤ 2 := by
          rcases poly_angle_nat hQp hpQ with h' | h' | h'
          · exact ⟨0, by simp [h'], by norm_num⟩
          · exact ⟨1, by simp [h'], by norm_num⟩
          · exact ⟨2, by simp [h'], le_rfl⟩
        have hAk : A p = ((zQ - zI - zJ : ℤ) : ℝ) := by
          push_cast
          rw [hB', hzI, hzJ, hzQ] at h
          linarith
        have hk0 : (0 : ℝ) ≤ ((zQ - zI - zJ : ℤ) : ℝ) := hAk ▸ hA0 p
        have hzI0 : (0 : ℝ) ≤ zI := hzI ▸ hI0 p
        have hzJ0 : (0 : ℝ) ≤ zJ := hzJ ▸ hJ0 p
        have hkc : ((zQ - zI - zJ : ℤ) : ℝ) < ((c p : ℕ) : ℝ) := hAk ▸ hAc p hp
        have hk0' : 0 ≤ zQ - zI - zJ := by exact_mod_cast hk0
        have hzI0' : 0 ≤ zI := by exact_mod_cast hzI0
        have hzJ0' : 0 ≤ zJ := by exact_mod_cast hzJ0
        have hkc' : zQ - zI - zJ < ((c p : ℕ) : ℤ) := by exact_mod_cast hkc
        have : 3 * (zQ - zI - zJ) ≤ 2 * ((c p : ℕ) : ℤ) := by omega
        rw [hAk]
        exact_mod_cast this
  -- summing over the corners of the cells
  have hfilterC : ∀ i, ((V.filter fun p ↦ p ∈ extremePoints ℝ (C i) : Finset (Fin 2 → ℝ)) :
      Set (Fin 2 → ℝ)) = extremePoints ℝ (C i) := by
    intro i
    ext p
    constructor
    · intro h
      exact (Finset.mem_filter.1 (Finset.mem_coe.1 h)).2
    · intro h
      exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨(hmemV p).2 ⟨i, h⟩, h⟩)
  have hN : ∀ i, (extremePoints ℝ (C i)).ncard =
      (V.filter fun p ↦ p ∈ extremePoints ℝ (C i)).card := by
    intro i
    conv_rhs => rw [← Set.ncard_coe_finset, hfilterC i]
  have hSA : ∑ p ∈ V, A p = ∑ i, (((extremePoints ℝ (C i)).ncard : ℝ) - 2) := by
    rw [Finset.sum_congr rfl fun p _ ↦ hA p, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.sum_filter, poly_angle_sum (hC i) _ (hfilterC i), hN i]
  have hSc : ∑ p ∈ V, (c p : ℝ) = ∑ i, ((extremePoints ℝ (C i)).ncard : ℝ) := by
    rw [Finset.sum_congr rfl fun p _ ↦ by rw [hc p, Finset.natCast_card_filter],
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, hN i]
  -- the corners of `Q`
  have hEQ : ((V.filter fun p ↦ p ∈ extremePoints ℝ Q : Finset (Fin 2 → ℝ)) :
      Set (Fin 2 → ℝ)) = extremePoints ℝ Q := by
    ext p
    constructor
    · intro h
      exact (Finset.mem_filter.1 (Finset.mem_coe.1 h)).2
    · intro h
      exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hQV p h, h⟩)
  have hEQcard : ((V.filter fun p ↦ p ∈ extremePoints ℝ Q).card : ℝ) ≤ m := by
    have : (V.filter fun p ↦ p ∈ extremePoints ℝ Q).card ≤ m := by
      rw [← Set.ncard_coe_finset, hEQ]
      exact ncard_extremePoints_le b d
    exact_mod_cast this
  -- the corners of the holes
  have hfilterH : ∀ H ∈ 𝓗, ((HC.filter fun p ↦ p ∈ extremePoints ℝ H : Finset (Fin 2 → ℝ)) :
      Set (Fin 2 → ℝ)) = extremePoints ℝ H := by
    intro H hH
    ext p
    constructor
    · intro h
      exact (Finset.mem_filter.1 (Finset.mem_coe.1 h)).2
    · intro h
      exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hHC H hH p h, h⟩)
  have hSB : ∑ p ∈ HC, B p =
      ∑ H ∈ 𝓗, (((HC.filter fun p ↦ p ∈ extremePoints ℝ H).card : ℝ) - 2) := by
    rw [Finset.sum_congr rfl fun p _ ↦ hB p, Finset.sum_comm]
    refine Finset.sum_congr rfl fun H hH ↦ ?_
    rw [← Finset.sum_filter, poly_angle_sum (hHp H hH) _ (hfilterH H hH)]
  have hHCcard : (HC.card : ℝ) ≤
      ∑ H ∈ 𝓗, ((HC.filter fun p ↦ p ∈ extremePoints ℝ H).card : ℝ) := by
    have hsub : HC ⊆ 𝓗.biUnion fun H ↦ HC.filter fun p ↦ p ∈ extremePoints ℝ H := by
      intro p hp
      obtain ⟨-, H, hH, hpH⟩ := Finset.mem_filter.1 hp
      exact Finset.mem_biUnion.2 ⟨H, hH, Finset.mem_filter.2 ⟨hp, hpH⟩⟩
    have := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    exact_mod_cast this
  have hk : ∑ H ∈ 𝓗, ((HC.filter fun p ↦ p ∈ extremePoints ℝ H).card : ℝ) ≤
      3 * ∑ H ∈ 𝓗, (((HC.filter fun p ↦ p ∈ extremePoints ℝ H).card : ℝ) - 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun H hH ↦ ?_
    have h3 : (3 : ℝ) ≤ (HC.filter fun p ↦ p ∈ extremePoints ℝ H).card := by
      exact_mod_cast poly_three_le (hHp H hH) _ (hfilterH H hH)
    linarith
  have hSg : ∑ p ∈ V, g p ≤ (m : ℝ) - 6 := by
    rw [Finset.sum_congr rfl fun p _ ↦ hg p, Finset.sum_add_distrib, ← Finset.sum_filter,
      ← Finset.sum_filter]
    have hVHC : (V.filter fun p ↦ p ∈ HC) = HC := by
      ext p
      rw [Finset.mem_filter]
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨(Finset.mem_filter.1 h).1, h⟩⟩
    rw [hVHC, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, poly_angle_sum hQp _ hEQ, hSB, Finset.sum_const, Finset.sum_const,
      nsmul_eq_mul, nsmul_eq_mul, mul_one]
    linarith
  -- the total
  have htot : 3 * ∑ p ∈ V, A p ≤ 2 * ∑ p ∈ V, (c p : ℝ) + ∑ p ∈ V, g p := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum hpt
  rw [hSA, hSc, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at htot
  have hfinal : (∑ i, ((extremePoints ℝ (C i)).ncard : ℝ)) + 6 ≤ 6 * n + m := by linarith
  exact_mod_cast hfinal

end PlaneConvex
