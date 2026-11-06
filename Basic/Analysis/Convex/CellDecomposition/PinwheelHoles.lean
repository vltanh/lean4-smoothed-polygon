module

public import Basic.Analysis.Convex.CellDecomposition.Defs
public import Basic.Analysis.Convex.CellDecomposition.PolygonOfFrontier
public import Basic.Analysis.Convex.TietzeNakajima
public import Mathlib.Analysis.Convex.Join

/-!
# (B) The holes of a maximal family are pinwheels

Part of the proof of the cell lemma (`Basic.Analysis.Convex.CellDecomposition`).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PlaneConvex

/-! ### Maximality gives the one-point enlargement property -/

/-- Adding a point outside a closed set with nonempty interior to a convex superset adds positive
area. -/
theorem pin_volume_diff_pos {C D : Set (Fin 2 → ℝ)} (hC : IsClosed C)
    (hint : (interior C).Nonempty) {y : Fin 2 → ℝ} (hy : y ∉ C) (hD : Convex ℝ D)
    (hCD : C ⊆ D) (hyD : y ∈ D) : 0 < volume (D \ C) := by
  obtain ⟨z, hz⟩ := hint
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isOpen_interior z hz
  obtain ⟨s, hs, hsC⟩ := Metric.isOpen_iff.1 hC.isOpen_compl y hy
  set t : ℝ := min 1 (s / (2 * (dist z y + r)))
  have hzr : 0 < dist z y + r := by positivity
  have ht : 0 < t := lt_min one_pos (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have hts : t * (dist z y + r) < s := by
    calc t * (dist z y + r) ≤ s / (2 * (dist z y + r)) * (dist z y + r) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hzr.le
      _ = s / 2 := by field_simp
      _ < s := by linarith
  refine lt_of_lt_of_le (Metric.measure_ball_pos volume (y + t • (z - y)) (mul_pos ht hr))
    (measure_mono fun w hw ↦ ?_)
  set u := y + t⁻¹ • (w - y)
  have hwu : w = (1 - t) • y + t • u := by
    simp only [u, smul_add, smul_smul, mul_inv_cancel₀ ht.ne', one_smul, sub_smul]
    abel
  have hu : u ∈ Metric.ball z r := by
    rw [Metric.mem_ball, dist_eq_norm] at hw ⊢
    have : u - z = t⁻¹ • (w - (y + t • (z - y))) := by
      simp only [u, smul_sub, smul_add, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
      abel
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 ht), inv_mul_lt_iff₀ ht]
    exact hw
  have huC : u ∈ C := interior_subset (hball hu)
  refine ⟨?_, fun hwC ↦ hsC ?_ hwC⟩
  · rw [hwu]
    exact hD hyD (hCD huC) (by linarith) ht.le (by ring)
  · rw [Metric.mem_ball, dist_eq_norm] at hw ⊢
    have : w - y = t • (u - y) := by rw [hwu]; simp only [smul_sub, sub_smul, one_smul]; abel
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    have h1 : ‖u - y‖ ≤ dist z y + r := by
      calc ‖u - y‖ = dist u y := (dist_eq_norm _ _).symm
        _ ≤ dist u z + dist z y := dist_triangle _ _ _
        _ ≤ r + dist z y := by linarith [Metric.mem_ball.1 hu]
        _ = dist z y + r := by ring
    calc t * ‖u - y‖ ≤ t * (dist z y + r) := mul_le_mul_of_nonneg_left h1 ht.le
      _ < s := hts

theorem pin_convex_of_isConvexPolygon {P : Set (Fin 2 → ℝ)} (hP : IsConvexPolygon P) :
    Convex ℝ P := by
  obtain ⟨⟨k, a, c, rfl⟩, -, -⟩ := hP
  exact convex_halfPlanesInter a c

theorem pin_isClosed_of_isConvexPolygon {P : Set (Fin 2 → ℝ)} (hP : IsConvexPolygon P) :
    IsClosed P := by
  obtain ⟨⟨k, a, c, rfl⟩, -, -⟩ := hP
  exact isClosed_halfPlanesInter a c

/-- The *one-point enlargement property* of a family of cells in `Q`: no cell `C i` can be
replaced by the convex hull of `C i` and a point `y ∈ Q \ C i` without overlapping another cell.
(Rotating a side of `C i` outwards about one of its endpoints is such an enlargement, with `y`
the new corner on the extension of the adjacent side.) -/
def pin_HasEnlargementProperty {n : ℕ} (Q : Set (Fin 2 → ℝ)) (C : Fin n → Set (Fin 2 → ℝ)) :
    Prop :=
  ∀ i, ∀ y ∈ Q, y ∉ C i →
    ∃ j, j ≠ i ∧ (interior (convexHull ℝ (insert y (C i))) ∩ interior (C j)).Nonempty

/-- A maximal family of cells has the one-point enlargement property: replacing `C i` by
`D = conv (C i ∪ {y})` would give an admissible family of larger total area. -/
theorem exists_overlap_of_isMaximalCells {m n : ℕ} (b : Fin m → Fin 2 → ℝ) (d : Fin m → ℝ)
    (K C : Fin n → Set (Fin 2 → ℝ)) (hC : ∀ i, IsConvexPolygon (C i)) (hKC : ∀ i, K i ⊆ C i)
    (hCQ : ∀ i, C i ⊆ halfPlanesInter b d) (hdisj : NonOverlapping C)
    (hmax : IsMaximalCells (halfPlanesInter b d) K C) :
    pin_HasEnlargementProperty (halfPlanesInter b d) C := by
  classical
  intro i y hyQ hy
  by_contra hcon
  simp only [not_exists, not_and, Set.not_nonempty_iff_eq_empty] at hcon
  set D := convexHull ℝ (insert y (C i))
  have hDconv : Convex ℝ D := convex_convexHull ℝ _
  have hCD : C i ⊆ D := (subset_insert y (C i)).trans (subset_convexHull ℝ _)
  have hyD : y ∈ D := subset_convexHull ℝ _ (mem_insert y _)
  have hDQ : D ⊆ halfPlanesInter b d :=
    convexHull_min (insert_subset_iff.2 ⟨hyQ, hCQ i⟩) (convex_halfPlanesInter b d)
  set C' := Function.update C i D with hC'
  have hC'i : C' i = D := Function.update_self i D C
  have hC'j : ∀ j, j ≠ i → C' j = C j := fun j hj ↦ Function.update_of_ne hj D C
  have hconv' : ∀ j, Convex ℝ (C' j) := by
    intro j
    by_cases hj : j = i
    · rw [hj, hC'i]; exact hDconv
    · rw [hC'j j hj]; exact pin_convex_of_isConvexPolygon (hC j)
  have hK' : ∀ j, K j ⊆ C' j := by
    intro j
    by_cases hj : j = i
    · rw [hj, hC'i]; exact (hKC i).trans hCD
    · rw [hC'j j hj]; exact hKC j
  have hQ' : ∀ j, C' j ⊆ halfPlanesInter b d := by
    intro j
    by_cases hj : j = i
    · rw [hj, hC'i]; exact hDQ
    · rw [hC'j j hj]; exact hCQ j
  have hdisj' : NonOverlapping C' := by
    intro j k hjk
    by_cases hj : j = i
    · subst hj
      rw [hC'i, hC'j k (Ne.symm hjk), Set.disjoint_iff_inter_eq_empty]
      exact hcon k (Ne.symm hjk)
    by_cases hk : k = i
    · subst hk
      rw [hC'i, hC'j j hjk, Set.disjoint_iff_inter_eq_empty, Set.inter_comm]
      exact hcon j hjk
    · rw [hC'j j hj, hC'j k hk]
      exact hdisj hjk
  have h1 := hmax C' hconv' hK' hQ' hdisj'
  have hsplit : ∀ f : Fin n → ℝ≥0∞, ∑ j, f j = f i + ∑ j ∈ Finset.univ.erase i, f j :=
    fun f ↦ (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  rw [hsplit (fun j ↦ volume (C' j)), hsplit (fun j ↦ volume (C j))] at h1
  have hrest : ∑ j ∈ Finset.univ.erase i, volume (C' j) =
      ∑ j ∈ Finset.univ.erase i, volume (C j) :=
    Finset.sum_congr rfl fun j hj ↦ by rw [hC'j j (Finset.ne_of_mem_erase hj)]
  rw [hrest, hC'i] at h1
  have hfin : ∀ j, volume (C j) ≠ ⊤ := fun j ↦ (hC j).2.1.measure_lt_top.ne
  have hR : ∑ j ∈ Finset.univ.erase i, volume (C j) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun j _ ↦ hfin j
  have h2 : volume D ≤ volume (C i) := ENNReal.le_of_add_le_add_right hR h1
  have h3 : volume (C i) + volume (D \ C i) = volume D := by
    rw [measure_add_sdiff (pin_isClosed_of_isConvexPolygon (hC i)).measurableSet.nullMeasurableSet,
      Set.union_eq_right.2 hCD]
  have h4 := pin_volume_diff_pos (pin_isClosed_of_isConvexPolygon (hC i)) (hC i).2.2 hy hDconv
    hCD hyD
  have : volume (C i) + volume (D \ C i) ≤ volume (C i) + 0 := by rw [h3, add_zero]; exact h2
  exact absurd (ENNReal.le_of_add_le_add_left (hfin i) this) (not_le.2 h4)

/-! ### Holes have nonempty interior and polygonal frontier -/

/-- A hole has nonempty interior. -/
theorem pin_interior_hole_nonempty {Q : Set (Fin 2 → ℝ)} (hQconv : Convex ℝ Q)
    (hQint : (interior Q).Nonempty) {n : ℕ} {C : Fin n → Set (Fin 2 → ℝ)}
    (hCcl : ∀ i, IsClosed (C i)) {x : Fin 2 → ℝ} (hx : x ∈ Q \ ⋃ i, C i) :
    (interior (closure (connectedComponentIn (Q \ ⋃ i, C i) x))).Nonempty := by
  set F := Q \ ⋃ i, C i
  obtain ⟨z, hz⟩ := hQint
  have hcl : IsClosed (⋃ i, C i) := isClosed_iUnion_of_finite hCcl
  obtain ⟨s, hs, hsC⟩ := Metric.isOpen_iff.1 hcl.isOpen_compl x hx.2
  set t : ℝ := min 1 (s / (2 * (‖z - x‖ + 1)))
  have ht : 0 < t := lt_min one_pos (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have htn : t * ‖z - x‖ < s / 2 := by
    calc t * ‖z - x‖ ≤ s / (2 * (‖z - x‖ + 1)) * ‖z - x‖ :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
      _ < s / (2 * (‖z - x‖ + 1)) * (‖z - x‖ + 1) :=
          mul_lt_mul_of_pos_left (by linarith) (by positivity)
      _ = s / 2 := by field_simp
  set x' := x + t • (z - x)
  have hx'int : x' ∈ interior Q :=
    hQconv.add_smul_sub_mem_interior' (subset_closure hx.1) hz ⟨ht, ht1⟩
  have hdist : dist x' x < s / 2 := by
    rw [dist_eq_norm, show x' - x = t • (z - x) by simp [x'], norm_smul, Real.norm_eq_abs,
      abs_of_pos ht]
    exact htn
  obtain ⟨ρ, hρ, hρQ⟩ := Metric.isOpen_iff.1 isOpen_interior x' hx'int
  set ρ' := min ρ (s / 2)
  have hρ' : 0 < ρ' := lt_min hρ (by linarith)
  have hball : Metric.ball x' ρ' ⊆ F := by
    intro w hw
    refine ⟨interior_subset (hρQ (Metric.ball_subset_ball (min_le_left _ _) hw)), fun hwC ↦ ?_⟩
    refine hsC ?_ hwC
    rw [Metric.mem_ball] at hw ⊢
    linarith [dist_triangle w x' x, min_le_right ρ (s / 2)]
  have hseg : segment ℝ x x' ⊆ F := by
    intro w hw
    refine ⟨hQconv.segment_subset hx.1 (interior_subset hx'int) hw, fun hwC ↦ ?_⟩
    have : w ∈ Metric.ball x s := (convex_ball x s).segment_subset (Metric.mem_ball_self hs)
      (by rw [Metric.mem_ball]; linarith) hw
    exact hsC this hwC
  have hx'comp : x' ∈ connectedComponentIn F x :=
    (convex_segment x x').isPreconnected.subset_connectedComponentIn (left_mem_segment ℝ x x')
      hseg (right_mem_segment ℝ x x')
  have hballcomp : Metric.ball x' ρ' ⊆ connectedComponentIn F x := by
    rw [connectedComponentIn_eq hx'comp]
    exact (convex_ball x' ρ').isPreconnected.subset_connectedComponentIn
      (Metric.mem_ball_self hρ') hball
  exact ⟨x', mem_interior.2 ⟨Metric.ball x' ρ', hballcomp.trans subset_closure,
    Metric.isOpen_ball, Metric.mem_ball_self hρ'⟩⟩

/-- The frontier of a hole lies in the frontiers of `Q` and of the cells. -/
theorem pin_frontier_hole_subset {Q : Set (Fin 2 → ℝ)} (hQcl : IsClosed Q) {n : ℕ}
    {C : Fin n → Set (Fin 2 → ℝ)} (hCcl : ∀ i, IsClosed (C i)) (x : Fin 2 → ℝ) :
    frontier (closure (connectedComponentIn (Q \ ⋃ i, C i) x)) ⊆
      frontier Q ∪ ⋃ i, frontier (C i) := by
  set F := Q \ ⋃ i, C i
  set U := connectedComponentIn F x
  have hUF : U ⊆ F := connectedComponentIn_subset F x
  have hHQ : closure U ⊆ Q := closure_minimal (hUF.trans sdiff_subset) hQcl
  intro p hp
  have hpH : p ∈ closure U := isClosed_closure.frontier_subset hp
  have hpQ : p ∈ Q := hHQ hpH
  by_cases hpint : p ∈ interior Q
  · right
    by_cases hpC : p ∈ ⋃ i, C i
    · obtain ⟨i, hi⟩ := mem_iUnion.1 hpC
      refine mem_iUnion.2 ⟨i, ?_⟩
      rw [(hCcl i).frontier_eq]
      refine ⟨hi, fun hpi ↦ ?_⟩
      obtain ⟨u, hu, huU⟩ := mem_closure_iff.1 hpH _ isOpen_interior hpi
      exact (hUF huU).2 (mem_iUnion.2 ⟨i, interior_subset hu⟩)
    · exfalso
      have hcl : IsClosed (⋃ i, C i) := isClosed_iUnion_of_finite hCcl
      obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.1
        (isOpen_interior.inter hcl.isOpen_compl) p ⟨hpint, hpC⟩
      have hballF : Metric.ball p r ⊆ F := fun w hw ↦
        ⟨interior_subset (hrsub hw).1, (hrsub hw).2⟩
      obtain ⟨u, hu, huU⟩ := mem_closure_iff.1 hpH _ Metric.isOpen_ball (Metric.mem_ball_self hr)
      have hballU : Metric.ball p r ⊆ U := by
        change Metric.ball p r ⊆ connectedComponentIn F x
        rw [connectedComponentIn_eq huU]
        exact (convex_ball p r).isPreconnected.subset_connectedComponentIn hu hballF
      have : p ∈ interior (closure U) := mem_interior.2 ⟨Metric.ball p r,
        hballU.trans subset_closure, Metric.isOpen_ball, Metric.mem_ball_self hr⟩
      exact hp.2 this
  · left
    rw [hQcl.frontier_eq]
    exact ⟨hpQ, hpint⟩

/-- The frontier of an intersection of half-planes lies on the lines with nonzero normal. -/
theorem pin_frontier_halfPlanesInter_subset {ι : Type*} [Finite ι] (a : ι → Fin 2 → ℝ)
    (c : ι → ℝ) : frontier (halfPlanesInter a c) ⊆ ⋃ l, ⋃ (_ : a l ≠ 0), {x | a l ⬝ᵥ x = c l} := by
  intro p hp
  have hpS : p ∈ halfPlanesInter a c := (isClosed_halfPlanesInter a c).frontier_subset hp
  by_contra hcon
  simp only [mem_iUnion, mem_ofPred_eq, not_exists] at hcon
  apply hp.2
  set O := ⋂ l, {x : Fin 2 → ℝ | a l ≠ 0 → a l ⬝ᵥ x < c l}
  have hO : IsOpen O := by
    refine isOpen_iInter_of_finite fun l ↦ ?_
    by_cases hl : a l = 0
    · have : {x : Fin 2 → ℝ | a l ≠ 0 → a l ⬝ᵥ x < c l} = univ := by ext; simp [hl]
      rw [this]; exact isOpen_univ
    · have : {x : Fin 2 → ℝ | a l ≠ 0 → a l ⬝ᵥ x < c l} = {x | a l ⬝ᵥ x < c l} := by
        ext; simp [hl]
      rw [this]; exact isOpen_lt (by fun_prop) continuous_const
  have hOS : O ⊆ halfPlanesInter a c := by
    intro x hx l
    by_cases hl : a l = 0
    · have := hpS l
      simp only [hl, zero_dotProduct] at this ⊢
      exact this
    · exact (mem_iInter.1 hx l hl).le
  have hpO : p ∈ O := mem_iInter.2 fun l hl ↦ lt_of_le_of_ne (hpS l) (hcon l hl)
  exact mem_interior.2 ⟨O, hOS, hO, hpO⟩

/-! ### The rotation property -/

/-- A point violating only the constraint `l` of a polygon sees only the side on the line `l`:
`conv (C ∪ {y}) ⊆ C ∪ conv (S ∪ {y})` with `S = C ∩ {⟨a l, x⟩ = c l}`. -/
theorem pin_convexHull_insert_subset {ι : Type*} (a : ι → Fin 2 → ℝ) (c : ι → ℝ) (l : ι)
    {y : Fin 2 → ℝ} (hy : ∀ m, m ≠ l → a m ⬝ᵥ y ≤ c m) :
    convexHull ℝ (insert y (halfPlanesInter a c)) ⊆ halfPlanesInter a c ∪
      convexHull ℝ (insert y (halfPlanesInter a c ∩ {x | a l ⬝ᵥ x = c l})) := by
  set S := halfPlanesInter a c
  intro z hz
  rcases S.eq_empty_or_nonempty with hS | hS
  · rw [hS, insert_empty_eq, convexHull_singleton, mem_singleton_iff] at hz
    subst hz
    exact Or.inr (subset_convexHull ℝ _ (mem_insert _ _))
  rw [convexHull_insert hS, (convex_halfPlanesInter a c).convexHull_eq, mem_convexJoin] at hz
  obtain ⟨y', hy', w, hw, s', t, hs, ht, hst, rfl⟩ := hz
  rw [mem_singleton_iff] at hy'
  subst hy'
  by_cases hzS : s' • y' + t • w ∈ S
  · exact Or.inl hzS
  right
  have hdot : ∀ v : Fin 2 → ℝ, v ⬝ᵥ (s' • y' + t • w) = s' * (v ⬝ᵥ y') + t * (v ⬝ᵥ w) := by
    intro v; simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
  have hzl : c l < a l ⬝ᵥ (s' • y' + t • w) := by
    by_contra h
    push Not at h
    apply hzS
    intro m
    by_cases hm : m = l
    · subst hm; exact h
    · rw [hdot]
      have h1 := mul_le_mul_of_nonneg_left (hy m hm) hs
      have h2 := mul_le_mul_of_nonneg_left (hw m) ht
      have h3 : s' * c m + t * c m = c m := by rw [← add_mul, hst, one_mul]
      linarith
  have hwl : a l ⬝ᵥ w ≤ c l := hw l
  rw [hdot] at hzl
  set A := a l ⬝ᵥ y'
  set Bw := a l ⬝ᵥ w
  have ht' : t = 1 - s' := by linarith
  have hA : c l < A := by
    by_contra h
    push Not at h
    have h1 := mul_le_mul_of_nonneg_left h hs
    have h2 := mul_le_mul_of_nonneg_left hwl ht
    have h3 : s' * c l + t * c l = c l := by rw [← add_mul, hst, one_mul]
    linarith
  have hAB : 0 < A - Bw := by linarith
  set σ := (c l - Bw) / (A - Bw)
  have hσ0 : 0 ≤ σ := div_nonneg (by linarith) hAB.le
  have hσ1 : σ < 1 := by rw [div_lt_one hAB]; linarith
  have hσA : σ * (A - Bw) = c l - Bw := div_mul_cancel₀ _ hAB.ne'
  have hσs : σ < s' := by
    by_contra h
    push Not at h
    have h1 : s' * (A - Bw) ≤ σ * (A - Bw) := mul_le_mul_of_nonneg_right h hAB.le
    have key : c l < Bw + s' * (A - Bw) := by
      rw [ht'] at hzl
      linarith [show s' * A + (1 - s') * Bw = Bw + s' * (A - Bw) by ring]
    linarith
  set u := (1 - σ) • w + σ • y'
  have hu : u ∈ S ∩ {x | a l ⬝ᵥ x = c l} := by
    have hdu : ∀ v : Fin 2 → ℝ, v ⬝ᵥ u = (1 - σ) * (v ⬝ᵥ w) + σ * (v ⬝ᵥ y') := by
      intro v; simp only [u, dotProduct_add, dotProduct_smul, smul_eq_mul]
    refine ⟨fun m ↦ ?_, ?_⟩
    · rw [hdu]
      by_cases hm : m = l
      · subst hm
        change (1 - σ) * Bw + σ * A ≤ c m
        linarith [show (1 - σ) * Bw + σ * A = Bw + σ * (A - Bw) by ring]
      · have h1 := mul_le_mul_of_nonneg_left (hw m) (by linarith : (0 : ℝ) ≤ 1 - σ)
        have h2 := mul_le_mul_of_nonneg_left (hy m hm) hσ0
        have h3 : (1 - σ) * c m + σ * c m = c m := by ring
        linarith
    · change a l ⬝ᵥ u = c l
      rw [hdu]
      change (1 - σ) * Bw + σ * A = c l
      linarith [show (1 - σ) * Bw + σ * A = Bw + σ * (A - Bw) by ring]
  set lam := (s' - σ) / (1 - σ)
  have hlam : lam * (1 - σ) = s' - σ := div_mul_cancel₀ _ (by linarith)
  have hlam0 : 0 ≤ lam := div_nonneg (by linarith) (by linarith)
  have hlam1 : lam ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have e1 : (1 - lam) * (1 - σ) = t := by linear_combination -hlam - ht'
  have e2 : (1 - lam) * σ + lam = s' := by linear_combination hlam
  refine segment_subset_convexHull (mem_insert_of_mem _ hu) (mem_insert y' _)
    ⟨1 - lam, lam, by linarith, hlam0, by ring, ?_⟩
  calc (1 - lam) • u + lam • y' = ((1 - lam) * (1 - σ)) • w + ((1 - lam) * σ + lam) • y' := by
        simp only [u]; module
    _ = s' • y' + t • w := by rw [e1, e2, add_comm]

/-- A point of a cell is not in the interior of another cell. -/
theorem pin_inter_interior_eq_empty {n : ℕ} {C : Fin n → Set (Fin 2 → ℝ)}
    (hC : ∀ i, IsConvexPolygon (C i)) (hdisj : NonOverlapping C) {i j : Fin n} (hij : i ≠ j) :
    C i ∩ interior (C j) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro z ⟨hzi, hzj⟩
  have hcl : z ∈ closure (interior (C i)) := by
    rw [(pin_convex_of_isConvexPolygon (hC i)).closure_interior_eq_closure_of_nonempty_interior
      (hC i).2.2]
    exact subset_closure hzi
  obtain ⟨w, hw1, hw2⟩ := mem_closure_iff.1 hcl _ isOpen_interior hzj
  exact Set.disjoint_left.1 (hdisj hij) hw2 hw1

/-- The *rotation property* of a family of cells in `Q`: if a point `y ∈ Q` violates exactly one
constraint `l` of a cell `C i = halfPlanesInter a c` (so that `conv (C i ∪ {y})` adds to `C i` the
triangle-like set `conv (S ∪ {y})` over the side `S = C i ∩ {⟨a l, x⟩ = c l}`), then the interior of
some other cell meets `conv (S ∪ {y})`. Rotating the side `S` outwards about one of its endpoints
is the case where `y` lies on the line of the adjacent side. -/
def pin_HasRotationProperty {n : ℕ} (Q : Set (Fin 2 → ℝ)) (C : Fin n → Set (Fin 2 → ℝ)) :
    Prop :=
  ∀ i, ∀ {k : ℕ} (a : Fin k → Fin 2 → ℝ) (c : Fin k → ℝ), C i = halfPlanesInter a c →
    ∀ l, ∀ y ∈ Q, c l < a l ⬝ᵥ y → (∀ m, m ≠ l → a m ⬝ᵥ y ≤ c m) →
      ∃ j, j ≠ i ∧ (interior (C j) ∩
        convexHull ℝ (insert y (C i ∩ {x | a l ⬝ᵥ x = c l}))).Nonempty

theorem pin_hasRotationProperty_of_enlargement {n : ℕ} {Q : Set (Fin 2 → ℝ)}
    {C : Fin n → Set (Fin 2 → ℝ)} (hC : ∀ i, IsConvexPolygon (C i)) (hdisj : NonOverlapping C)
    (henl : pin_HasEnlargementProperty Q C) : pin_HasRotationProperty Q C := by
  intro i k a c hrep l y hyQ hyl hym
  have hyC : y ∉ C i := by
    rw [hrep]; intro h; exact absurd (h l) (not_le.2 hyl)
  obtain ⟨j, hji, z, hz1, hz2⟩ := henl i y hyQ hyC
  refine ⟨j, hji, z, hz2, ?_⟩
  have hsub := pin_convexHull_insert_subset a c l hym
  rw [← hrep] at hsub
  rcases hsub (interior_subset hz1) with h | h
  · exact absurd (Set.mem_inter h hz2)
      (by rw [pin_inter_interior_eq_empty hC hdisj (Ne.symm hji)]; exact Set.notMem_empty _)
  · exact h

/-- **Local cone structure of a polygon.** Near a point `p` of `halfPlanesInter a c`, only the
constraints active at `p` matter. -/
theorem pin_local_cone {ι : Type*} [Finite ι] (a : ι → Fin 2 → ℝ) (c : ι → ℝ) {p : Fin 2 → ℝ}
    (hp : p ∈ halfPlanesInter a c) :
    ∃ r > 0, ∀ x ∈ Metric.ball p r,
      (x ∈ halfPlanesInter a c ↔ ∀ l, a l ⬝ᵥ p = c l → a l ⬝ᵥ (x - p) ≤ 0) := by
  set O := ⋂ l, {x : Fin 2 → ℝ | a l ⬝ᵥ p < c l → a l ⬝ᵥ x < c l}
  have hO : IsOpen O := by
    refine isOpen_iInter_of_finite fun l ↦ ?_
    by_cases hl : a l ⬝ᵥ p < c l
    · have : {x : Fin 2 → ℝ | a l ⬝ᵥ p < c l → a l ⬝ᵥ x < c l} = {x | a l ⬝ᵥ x < c l} := by
        ext x; simp only [mem_ofPred_eq]; exact ⟨fun h ↦ h hl, fun h _ ↦ h⟩
      rw [this]; exact isOpen_lt (by fun_prop) continuous_const
    · have : {x : Fin 2 → ℝ | a l ⬝ᵥ p < c l → a l ⬝ᵥ x < c l} = univ := by
        ext x; simp only [mem_ofPred_eq, mem_univ, iff_true]; exact fun h ↦ absurd h hl
      rw [this]; exact isOpen_univ
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.1 hO p (mem_iInter.2 fun l h ↦ h)
  refine ⟨r, hr, fun x hx ↦ ⟨fun hxP l hl ↦ ?_, fun h l ↦ ?_⟩⟩
  · rw [dotProduct_sub, hl]; linarith [hxP l]
  · by_cases hl : a l ⬝ᵥ p = c l
    · have := h l hl
      rw [dotProduct_sub, hl] at this
      linarith
    · exact (mem_iInter.1 (hrO hx) l (lt_of_le_of_ne (hp l) hl)).le

/-! ### The remaining steps -/

/-- A scaled point stays in the ball. -/
theorem pin_mem_ball_scale {p x : Fin 2 → ℝ} {r t : ℝ} (hx : x ∈ Metric.ball p r) (ht : 0 < t)
    (ht1 : t ≤ 1) : p + t • (x - p) ∈ Metric.ball p r := by
  rw [Metric.mem_ball, dist_eq_norm] at hx ⊢
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  calc t * ‖x - p‖ ≤ 1 * ‖x - p‖ := mul_le_mul_of_nonneg_right ht1 (norm_nonneg _)
    _ < r := by rw [one_mul]; exact hx

/-- An intersection of half-planes is conic near any point. -/
theorem pin_conic_halfPlanesInter {ι : Type*} [Finite ι] (a : ι → Fin 2 → ℝ) (c : ι → ℝ)
    (p : Fin 2 → ℝ) : ∃ r > 0, ∀ x ∈ Metric.ball p r, ∀ t : ℝ, 0 < t → t ≤ 1 →
      (x ∈ halfPlanesInter a c ↔ p + t • (x - p) ∈ halfPlanesInter a c) := by
  by_cases hp : p ∈ halfPlanesInter a c
  · obtain ⟨r, hr, hcone⟩ := pin_local_cone a c hp
    refine ⟨r, hr, fun x hx t ht ht1 ↦ ?_⟩
    rw [hcone x hx, hcone _ (pin_mem_ball_scale hx ht ht1)]
    simp only [add_sub_cancel_left, dotProduct_smul, smul_eq_mul]
    refine forall_congr' fun l ↦ imp_congr_right fun _ ↦ ?_
    constructor
    · intro h; nlinarith
    · intro h
      by_contra h'
      push Not at h'
      nlinarith
  · obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (isClosed_halfPlanesInter a c).isOpen_compl p hp
    refine ⟨r, hr, fun x hx t ht ht1 ↦ ?_⟩
    exact iff_of_false (hball hx) (hball (pin_mem_ball_scale hx ht ht1))

/-- **Holes are locally conic.** For `p` in a hole `H = closure U` (`U` a connected component of
`F = Q \ ⋃ C i`), `H` coincides near `p` with a cone at `p`: for some `r > 0`, every
`x ∈ B(p, r)` and `t ∈ (0, 1]`, `x ∈ H ↔ p + t (x - p) ∈ H`. -/
theorem pin_hole_locally_conic {m n : ℕ} (b : Fin m → Fin 2 → ℝ) (d : Fin m → ℝ)
    (C : Fin n → Set (Fin 2 → ℝ)) (hC : ∀ i, IsConvexPolygon (C i)) {H : Set (Fin 2 → ℝ)}
    (hH : H ∈ holes (halfPlanesInter b d) C) (p : Fin 2 → ℝ) :
    ∃ r > 0, ∀ x ∈ Metric.ball p r, ∀ t : ℝ, 0 < t → t ≤ 1 →
      (x ∈ H ↔ p + t • (x - p) ∈ H) := by
  classical
  obtain ⟨x₀, -, rfl⟩ := hH
  set F := halfPlanesInter b d \ ⋃ i, C i
  set U := connectedComponentIn F x₀
  -- radii for `Q` and the cells
  obtain ⟨rQ, hrQ, hQc⟩ := pin_conic_halfPlanesInter b d p
  have hcell : ∀ i, ∃ r > 0, ∀ x ∈ Metric.ball p r, ∀ t : ℝ, 0 < t → t ≤ 1 →
      (x ∈ C i ↔ p + t • (x - p) ∈ C i) := by
    intro i
    obtain ⟨⟨k, a, c, hac⟩, -, -⟩ := hC i
    rw [hac]
    exact pin_conic_halfPlanesInter a c p
  choose rC hrC hCc using hcell
  obtain ⟨r, hr, hrrQ, hrrC⟩ : ∃ r > 0, r ≤ rQ ∧ ∀ i, r ≤ rC i := by
    set R : Finset ℝ := insert rQ (Finset.univ.image rC)
    refine ⟨R.min' (Finset.insert_nonempty _ _), ?_, Finset.min'_le R _
      (Finset.mem_insert_self _ _), fun i ↦ Finset.min'_le R _ (Finset.mem_insert_of_mem
        (Finset.mem_image_of_mem _ (Finset.mem_univ i)))⟩
    rcases Finset.mem_insert.1 (Finset.min'_mem R (Finset.insert_nonempty _ _)) with h | h
    · rw [h]; exact hrQ
    · obtain ⟨i, -, hi⟩ := Finset.mem_image.1 h
      rw [← hi]; exact hrC i
  have hFc : ∀ x ∈ Metric.ball p r, ∀ t : ℝ, 0 < t → t ≤ 1 →
      (x ∈ F ↔ p + t • (x - p) ∈ F) := by
    intro x hx t ht ht1
    have hxQ := Metric.ball_subset_ball hrrQ hx
    simp only [F, mem_sdiff, mem_iUnion, not_exists]
    rw [hQc x hxQ t ht ht1]
    refine and_congr_right fun _ ↦ forall_congr' fun i ↦ not_congr ?_
    exact hCc i x (Metric.ball_subset_ball (hrrC i) hx) t ht ht1
  -- the radial segment
  have hseg : ∀ x ∈ Metric.ball p r, x ∈ F → ∀ t : ℝ, 0 < t → t ≤ 1 →
      segment ℝ (p + t • (x - p)) x ⊆ F := by
    intro x hx hxF t ht ht1 z hz
    obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hz
    have hs : α • (p + t • (x - p)) + β • x = p + (α * t + β) • (x - p) := by
      rw [show β = 1 - α by linarith]; module
    rw [hs]
    have hs0 : 0 < α * t + β := by
      rcases eq_or_lt_of_le hα with h | h
      · rw [← h]; linarith
      · nlinarith
    have hs1 : α * t + β ≤ 1 := by nlinarith
    exact (hFc x hx _ hs0 hs1).1 hxF
  have hUc : ∀ x ∈ Metric.ball p r, ∀ t : ℝ, 0 < t → t ≤ 1 →
      (x ∈ U ↔ p + t • (x - p) ∈ U) := by
    intro x hx t ht ht1
    constructor
    · intro hxU
      have hxF : x ∈ F := connectedComponentIn_subset F x₀ hxU
      have hsub := (convex_segment (p + t • (x - p)) x).isPreconnected.subset_connectedComponentIn
        (right_mem_segment ℝ _ x) (hseg x hx hxF t ht ht1)
      rw [← connectedComponentIn_eq hxU] at hsub
      exact hsub (left_mem_segment ℝ _ x)
    · intro hyU
      have hyF : p + t • (x - p) ∈ F := connectedComponentIn_subset F x₀ hyU
      have hxF : x ∈ F := (hFc x hx t ht ht1).2 hyF
      have hsub := (convex_segment (p + t • (x - p)) x).isPreconnected.subset_connectedComponentIn
        (left_mem_segment ℝ _ x) (hseg x hx hxF t ht ht1)
      rw [← connectedComponentIn_eq hyU] at hsub
      exact hsub (right_mem_segment ℝ _ x)
  refine ⟨r, hr, fun x hx t ht ht1 ↦ ⟨fun hxH ↦ ?_, fun hyH ↦ ?_⟩⟩
  · -- scaling towards `p` maps `U ∩ B(p, r)` into `U`
    have hcont : Continuous fun z : Fin 2 → ℝ ↦ p + t • (z - p) := by fun_prop
    have h1 : x ∈ closure (Metric.ball p r ∩ U) := Metric.isOpen_ball.inter_closure ⟨hx, hxH⟩
    have h2 := image_closure_subset_closure_image hcont (mem_image_of_mem _ h1)
    refine closure_mono ?_ h2
    rintro _ ⟨z, ⟨hz, hzU⟩, rfl⟩
    exact (hUc z hz t ht ht1).1 hzU
  · -- scaling away from `p`
    have hy : p + t • (x - p) ∈ Metric.ball p (t * r) := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos ht]
      exact mul_lt_mul_of_pos_left (by rw [← dist_eq_norm]; exact hx) ht
    have hcont : Continuous fun z : Fin 2 → ℝ ↦ p + t⁻¹ • (z - p) := by fun_prop
    have h1 : p + t • (x - p) ∈ closure (Metric.ball p (t * r) ∩ U) :=
      Metric.isOpen_ball.inter_closure ⟨hy, hyH⟩
    have h2 := image_closure_subset_closure_image hcont (mem_image_of_mem _ h1)
    have hx' : p + t⁻¹ • (p + t • (x - p) - p) = x := by
      rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht.ne', one_smul, add_sub_cancel]
    rw [hx'] at h2
    refine closure_mono ?_ h2
    rintro _ ⟨z, ⟨hz, hzU⟩, rfl⟩
    have hz' : p + t⁻¹ • (z - p) ∈ Metric.ball p r := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.2 ht), inv_mul_lt_iff₀ ht]
      rw [Metric.mem_ball, dist_eq_norm] at hz
      exact hz
    refine (hUc _ hz' t ht ht1).2 ?_
    rwa [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ ht.ne', one_smul, add_sub_cancel]

/-- **The core of Böröczky's Lemma 5.** Let `Q = halfPlanesInter b d` be bounded and
`C 0, …, C (n-1)`, `n ≥ 1`, non-overlapping convex polygons in `Q` with the one-point enlargement
property, in its rotation form (`pin_HasRotationProperty`). Then every hole `H` (closure of a
connected component of `Q \ ⋃ C i`) lies in `interior Q`, is locally convex, and has every
extreme point a side point of some cell. (That `H` has nonempty interior and polygonal frontier is
proved separately:
`pin_interior_hole_nonempty`, `pin_frontier_hole_subset`, `pin_frontier_halfPlanesInter_subset`.)

Argument. *Local structure.* Near any point `p`, each polygon coincides with its tangent cone at
`p` (only the half-planes active at `p` matter, `pin_local_cone`), so `H` is locally conic at `p`
(`pin_hole_locally_conic`) and `H` near `p` is a finite union of closed
sectors at `p`, bounded by rays on sides of cells or of `Q`. The frontier of `H` is a finite union
of maximal segments, each on a side of a cell (*cell segments*) or of `Q`; at each *corner* (a
point `v` together with one sector of `H` at `v`) two segment ends meet.

*Rotation lemma.* A cell segment `s` on a side `e = [p, q] = C i ∩ {⟨a l, x⟩ = c l}` of `C i` is
not all of `e`. Otherwise let `y` be the point on the extension, beyond `q`, of the side of `C i`
adjacent at `q`, at small distance; `y` violates only the constraint `l`, and the thin triangle
`conv {p, q, y} = conv (e ∪ {y})` lies, apart from `e`, in `H` (no other cell meets the relative
interior of `e`; the other cells at `p` and `q` lie outside the thin angle; the remaining cells
are at positive distance from `e`), so it meets no other cell's interior, contradicting
`pin_HasRotationProperty`. So every cell segment has an end in the relative
interior of its side.

*Counting.* At a corner `v` at most one incident segment has `v` in the relative interior of its
side (a side through `v` fills an angle `π` at `v`), and none if `v ∈ ∂Q` (the angle of `Q` at
`v` is `≤ π`). Counting segment ends (`#cell segments ≤ #corners off ∂Q`, and
`#segments = #corners`) forces: every corner off `∂Q` is a T-junction (a side of one cell passes
through `v`, the other segment starts at `v` along a side of another cell, and the sector of `H`
at `v` is `< π`), and the segments on `∂Q` form whole boundary cycles. The remaining global
configurations are excluded by turning (or by `pin_convex_of_isClosed_of_isConnected` applied to
`H`, which is then locally convex): two sectors of `H` at one corner, or a boundary cycle along
all of `∂Q`, or an island of cells inside `H`, would give a closed polygon all of whose angles
seen from `H` are convex while it encloses cells, which is impossible (`H` would be convex and
contain those cells). Hence `H ⊆ interior Q`, `H` is locally convex (a half-plane near points of
segments, a sector `< π` near corners), and each extreme point of `H` is a corner, a side point of
a cell (`IsSidePoint`, with `ε` less than the distance from `v` to the other lines of that cell).

Available ingredients (proved above): `pin_local_cone`, `pin_hole_locally_conic` (the local
sector structure), `pin_convexHull_insert_subset`, `pin_inter_interior_eq_empty`,
`pin_frontier_hole_subset`, `pin_interior_hole_nonempty`, and the Tietze–Nakajima theorem
`pin_convex_of_isClosed_of_isConnected`. What remains is to extract the segments and corners of
`frontier H` from the local cones, the rotation lemma (choosing `y` and checking that the thin
triangle lies in `U ∪ e`), the counting, and the turning step.

Estimated size: 1200–2000 lines. -/
theorem pin_hole_structure_of_rotation {m n : ℕ} (hn : 1 ≤ n) (b : Fin m → Fin 2 → ℝ)
    (d : Fin m → ℝ)
    (hQ : Bornology.IsBounded (halfPlanesInter b d)) (C : Fin n → Set (Fin 2 → ℝ))
    (hC : ∀ i, IsConvexPolygon (C i)) (hCQ : ∀ i, C i ⊆ halfPlanesInter b d)
    (hdisj : NonOverlapping C) (hrot : pin_HasRotationProperty (halfPlanesInter b d) C)
    {H : Set (Fin 2 → ℝ)} (hH : H ∈ holes (halfPlanesInter b d) C) :
    H ⊆ interior (halfPlanesInter b d) ∧
      (∀ p ∈ H, ∃ r > 0, Convex ℝ (H ∩ Metric.ball p r)) ∧
      (∀ v ∈ extremePoints ℝ H, ∃ i, IsSidePoint (C i) v) := by
  sorry

/-- **The core of Böröczky's Lemma 5**, for families with the one-point enlargement property:
reduced to its rotation form (`pin_hasRotationProperty_of_enlargement`) and
`pin_hole_structure_of_rotation`. -/
theorem pin_hole_structure {m n : ℕ} (hn : 1 ≤ n) (b : Fin m → Fin 2 → ℝ) (d : Fin m → ℝ)
    (hQ : Bornology.IsBounded (halfPlanesInter b d)) (C : Fin n → Set (Fin 2 → ℝ))
    (hC : ∀ i, IsConvexPolygon (C i)) (hCQ : ∀ i, C i ⊆ halfPlanesInter b d)
    (hdisj : NonOverlapping C) (henl : pin_HasEnlargementProperty (halfPlanesInter b d) C)
    {H : Set (Fin 2 → ℝ)} (hH : H ∈ holes (halfPlanesInter b d) C) :
    H ⊆ interior (halfPlanesInter b d) ∧
      (∀ p ∈ H, ∃ r > 0, Convex ℝ (H ∩ Metric.ball p r)) ∧
      (∀ v ∈ extremePoints ℝ H, ∃ i, IsSidePoint (C i) v) :=
  pin_hole_structure_of_rotation hn b d hQ C hC hCQ hdisj
    (pin_hasRotationProperty_of_enlargement hC hdisj henl) hH

/-! ### (B) The holes of a maximal family are pinwheels -/

/-- **(B) Holes of a maximal family are pinwheels** (Böröczky 2003, proof of Lemma 5). Let
`Q = halfPlanesInter b d` be bounded, `K i` compact convex with nonempty interiors, and `C i`,
`i < n`, `n ≥ 1`, convex polygons with `K i ⊆ C i ⊆ Q`, non-overlapping, of maximal total area
(`IsMaximalCells`). Then the family has pinwheel holes (`HasPinwheelHoles`): every hole `H`
(closure of a connected component of `Q \ ⋃ C i`) is a convex polygon in `interior Q`, each
corner of which is a side point of some cell.

The hypothesis `1 ≤ n` (an auto-parameter, discharged by `omega` at the call site) is needed:
for `n = 0` the only hole of a nonempty `Q` is `Q` itself, which is not contained in
`interior Q`.

Proof: maximality gives the one-point enlargement property (`exists_overlap_of_isMaximalCells`),
from which `pin_hole_structure` (the core of Böröczky's argument) gives the local properties of
each hole; the hole is then convex by the Tietze–Nakajima theorem
(`pin_convex_of_isClosed_of_isConnected`) and a convex polygon
(`pin_isConvexPolygon_of_frontier_subset`). -/
theorem hasPinwheelHoles_of_isMaximalCells {m n : ℕ} (b : Fin m → Fin 2 → ℝ) (d : Fin m → ℝ)
    (hQ : Bornology.IsBounded (halfPlanesInter b d)) (K : Fin n → Set (Fin 2 → ℝ))
    (_hK : ∀ i, Convex ℝ (K i) ∧ IsCompact (K i) ∧ (interior (K i)).Nonempty)
    (C : Fin n → Set (Fin 2 → ℝ)) (hC : ∀ i, IsConvexPolygon (C i)) (hKC : ∀ i, K i ⊆ C i)
    (hCQ : ∀ i, C i ⊆ halfPlanesInter b d) (hdisj : NonOverlapping C)
    (hmax : IsMaximalCells (halfPlanesInter b d) K C) (hn : 1 ≤ n := by omega) :
    HasPinwheelHoles (halfPlanesInter b d) C := by
  classical
  have henl := exists_overlap_of_isMaximalCells b d K C hC hKC hCQ hdisj hmax
  intro H hH
  obtain ⟨hHQ, hloc, hext⟩ := pin_hole_structure hn b d hQ C hC hCQ hdisj henl hH
  obtain ⟨x, hx, rfl⟩ := hH
  have hCcl : ∀ i, IsClosed (C i) := fun i ↦ pin_isClosed_of_isConvexPolygon (hC i)
  have hQint : (interior (halfPlanesInter b d)).Nonempty :=
    ((hC ⟨0, hn⟩).2.2).mono (interior_mono (hCQ ⟨0, hn⟩))
  have hHint := pin_interior_hole_nonempty (convex_halfPlanesInter b d) hQint hCcl hx
  have hclosed : IsClosed (closure (connectedComponentIn
      (halfPlanesInter b d \ ⋃ i, C i) x)) := isClosed_closure
  have hconn : IsConnected (closure (connectedComponentIn
      (halfPlanesInter b d \ ⋃ i, C i) x)) :=
    (isConnected_connectedComponentIn_iff.2 hx).closure
  have hconv := pin_convex_of_isClosed_of_isConnected hclosed hconn hloc
  have hcpt := Metric.isCompact_of_isClosed_isBounded hclosed
    (hQ.subset (hHQ.trans interior_subset))
  -- the lines of `Q` and of the cells
  choose k a c hac using fun i ↦ (hC i).1
  let ι := Fin m ⊕ Σ i, Fin (k i)
  let A : ι → Fin 2 → ℝ := Sum.elim b fun p ↦ a p.1 p.2
  let B : ι → ℝ := Sum.elim d fun p ↦ c p.1 p.2
  have hfr : frontier (closure (connectedComponentIn (halfPlanesInter b d \ ⋃ i, C i) x)) ⊆
      ⋃ l : {l : ι // A l ≠ 0}, {y | A l ⬝ᵥ y = B l} := by
    intro y hy
    rcases pin_frontier_hole_subset (isClosed_halfPlanesInter b d) hCcl x hy with hy | hy
    · obtain ⟨l, hl, hyl⟩ := mem_iUnion₂.1 (pin_frontier_halfPlanesInter_subset b d hy)
      exact mem_iUnion.2 ⟨⟨Sum.inl l, hl⟩, hyl⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.1 hy
      rw [hac i] at hi
      obtain ⟨l, hl, hyl⟩ := mem_iUnion₂.1 (pin_frontier_halfPlanesInter_subset (a i) (c i) hi)
      exact mem_iUnion.2 ⟨⟨Sum.inr ⟨i, l⟩, hl⟩, hyl⟩
  exact ⟨pin_isConvexPolygon_of_frontier_subset hconv hcpt hHint
    (fun l : {l : ι // A l ≠ 0} ↦ A l) (fun l : {l : ι // A l ≠ 0} ↦ B l) (fun l ↦ l.2) hfr,
    hHQ, hext⟩

end PlaneConvex
