module

public import SmoothedPolygons.Ch2.Density
public import External.MahlerIrreducible
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# A worst disk is irreducible (for Lemma 2.2.5)

Helper results for the proof of Lemma 2.2.5 (`lem:no-corner`) by Mahler's lattice route. They are
stated with the notions of §2.1 and of the cited works (`External.MinkowskiMahler`,
`External.Mahler1947`, `External.MahlerIrreducible`), so that `SmoothedPolygons.Ch2.Reinhardt`
can import them.

* `irr_glpd_eq`: `δ_L(K) = area(K)/(4Δ(K))` for every centrally symmetric convex disk `K`. The
  translates `K + L` pack iff `½L` is `K`-admissible (`irr_four_mul_le_latticeDet`, and
  `irr_exists_packing` for `L = 2Λ` with `Λ` critical).
* `irr_isIrreducible_of_worst`: a disk `K` with the worst greatest lattice packing density is
  irreducible in Mahler's sense: a proper symmetric convex subdomain `K'` has smaller area, so
  `Δ(K') ≥ Δ(K)` would give `δ_L(K') < δ_L(K)`.
* `irr_not_isParallelogram_of_worst`: such a disk is not a parallelogram: a parallelogram has
  `δ_L = 1`, the Euclidean disk has `δ_L ≤ π/(2√3) < 1` (`Δ ≥ √3/2` by reduced bases).
* `irr_main`: for such a disk and a support line `{b · x = 1}`, Mahler's Lemma 3
  (`External.mahler_irreducible`) gives a point `x` of a critical lattice on the line; Mahler's
  Theorem 2 (`External.mahler_1947`) gives that the line is the only support line at `x`, and a
  circumscribed centrally symmetric hexagon, of area at most `4Δ(K)`, with an edge on the line.
-/

@[expose] public section

namespace SmoothedPolygons

open MeasureTheory Set Filter Topology External External.MinkowskiMahler

/-! ### Lattice packings and admissible lattices -/

lemma irr_interior_translate (K : Set (Fin 2 → ℝ)) (l : Fin 2 → ℝ) :
    interior ((fun x ↦ x + l) '' K) = (fun x ↦ x + l) '' interior K :=
  ((Homeomorph.addRight l).image_interior K).symm

/-- If `K + L` is a packing, then `½L` is `K`-admissible, so `4Δ(K) ≤ det(L)`. -/
lemma irr_four_mul_le_latticeDet {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K)
    {L : Submodule ℤ (Fin 2 → ℝ)} (hL : IsPlaneLattice L) (hKL : IsLatticePacking K L) :
    4 * minimalDeterminant K ≤ latticeDet L := by
  obtain ⟨u, v, hB, huv⟩ := mm_exists_basis hL
  have hdetL : latticeDet L = |cross u v| := mm_det_eq hL hB
  have hc : cross ((1 / 2 : ℝ) • u) ((1 / 2 : ℝ) • v) = 1 / 4 * cross u v := by
    simp only [cross, Pi.smul_apply, smul_eq_mul]; ring
  have huv' : cross ((1 / 2 : ℝ) • u) ((1 / 2 : ℝ) • v) ≠ 0 := by
    rw [hc]; exact mul_ne_zero (by norm_num) huv
  have hadm : IsAdmissible K (Submodule.span ℤ {(1 / 2 : ℝ) • u, (1 / 2 : ℝ) • v}) := by
    intro x hx hxK
    obtain ⟨m, n, rfl⟩ := mm_mem_span_pair.1 hx
    by_contra hx0
    have h2x : (2 : ℝ) • ((m : ℝ) • (1 / 2 : ℝ) • u + (n : ℝ) • (1 / 2 : ℝ) • v) ∈ L := by
      rw [← hB.2]
      exact mm_mem_span_pair.2 ⟨m, n, by module⟩
    have hne : (0 : Fin 2 → ℝ) ≠ (2 : ℝ) • ((m : ℝ) • (1 / 2 : ℝ) • u +
        (n : ℝ) • (1 / 2 : ℝ) • v) := by
      intro h
      exact hx0 ((smul_eq_zero.1 h.symm).resolve_left two_ne_zero)
    have hd := hKL 0 L.zero_mem _ h2x hne
    rw [irr_interior_translate, irr_interior_translate] at hd
    refine hd.ne_of_mem ⟨_, hxK, add_zero _⟩ ⟨_, mm_neg_mem_interior hK hxK, ?_⟩ rfl
    module
  have h1 := mm_minimalDeterminant_le (mm_isLattice_span huv') hadm
  rw [mm_det_span huv', hc, abs_mul] at h1
  rw [hdetL]
  have : |(1 / 4 : ℝ)| = 1 / 4 := abs_of_pos (by norm_num)
  rw [this] at h1
  linarith

/-- If `Λ` is a critical lattice of `K`, then `K + 2Λ` is a packing, and `det(2Λ) = 4Δ(K)`. -/
lemma irr_exists_packing {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) :
    ∃ L, IsPlaneLattice L ∧ IsLatticePacking K L ∧ latticeDet L = 4 * minimalDeterminant K := by
  obtain ⟨Λ, hΛ⟩ := MahlerIrreducible.irr_exists_critical hK
  obtain ⟨u, v, hB, huv⟩ := mm_exists_basis hΛ.1
  have hc : cross ((2 : ℝ) • u) ((2 : ℝ) • v) = 4 * cross u v := by
    simp only [cross, Pi.smul_apply, smul_eq_mul]; ring
  have h2 : cross ((2 : ℝ) • u) ((2 : ℝ) • v) ≠ 0 := by
    rw [hc]; exact mul_ne_zero (by norm_num) huv
  refine ⟨Submodule.span ℤ {(2 : ℝ) • u, (2 : ℝ) • v}, mm_isLattice_span h2, ?_, ?_⟩
  · intro l hl l' hl' hne
    rw [irr_interior_translate, irr_interior_translate, Set.disjoint_left]
    rintro z ⟨p, hp, rfl⟩ ⟨q, hq, hpq⟩
    obtain ⟨m, n, rfl⟩ := mm_mem_span_pair.1 hl
    obtain ⟨m', n', rfl⟩ := mm_mem_span_pair.1 hl'
    have hmem : ((m - m' : ℤ) : ℝ) • u + ((n - n' : ℤ) : ℝ) • v ∈ Λ := by
      rw [← hB.2]; exact mm_mem_span_pair.2 ⟨_, _, rfl⟩
    have he : ((m - m' : ℤ) : ℝ) • u + ((n - n' : ℤ) : ℝ) • v =
        (1 / 2 : ℝ) • q + (1 / 2 : ℝ) • (-p) := by
      have : q = p + ((m : ℝ) • (2 : ℝ) • u + (n : ℝ) • (2 : ℝ) • v) -
          ((m' : ℝ) • (2 : ℝ) • u + (n' : ℝ) • (2 : ℝ) • v) := eq_sub_of_add_eq hpq
      rw [this]; push_cast; module
    have hint : ((m - m' : ℤ) : ℝ) • u + ((n - n' : ℤ) : ℝ) • v ∈ interior K := by
      rw [he]
      exact hK.1.interior hq (mm_neg_mem_interior hK hp) (by norm_num) (by norm_num)
        (by norm_num)
    have h0 := hΛ.2.1 _ hmem hint
    apply hne
    have hli := mm_linearIndependent_real huv
    rw [LinearIndependent.pair_iff] at hli
    have := hli _ _ h0
    push_cast at this
    have hm : (m : ℝ) = m' := by linarith [this.1]
    have hn : (n : ℝ) = n' := by linarith [this.2]
    rw [hm, hn]
  · change det _ = _
    rw [mm_det_span h2, hc, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4), ← hΛ.2.2,
      mm_det_eq hΛ.1 hB]

/-- **The greatest lattice packing density is `δ_L(K) = area(K)/(4Δ(K))`.** -/
theorem irr_glpd_eq {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) :
    greatestLatticePackingDensity K = volume.real K / (4 * minimalDeterminant K) := by
  have hKc : IsConvexDisk K := ⟨hK.1, hK.2.1, hK.2.2.1⟩
  have hΔ := MahlerIrreducible.irr_minimalDeterminant_pos hK
  obtain ⟨L0, hL0, hpack0, hdet0⟩ := irr_exists_packing hK
  refine IsGreatest.csSup_eq ⟨⟨L0, hL0, hpack0, ?_⟩, ?_⟩
  · rw [ch2_latticePackingDensity_eq hKc hL0 hpack0, hdet0]
  · rintro _ ⟨L, hL, hKL, rfl⟩
    rw [ch2_latticePackingDensity_eq hKc hL hKL]
    exact div_le_div_of_nonneg_left measureReal_nonneg (by positivity)
      (irr_four_mul_le_latticeDet hK hL hKL)

/-! ### A worst disk is irreducible -/

/-- A compact set `K'` properly contained in a convex disk `K` has smaller area. -/
lemma irr_volume_lt {K K' : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) (hK' : IsCompact K')
    (hsub : K' ⊆ K) (hne : K' ≠ K) : volume.real K' < volume.real K := by
  have hn : (interior K \ K').Nonempty := by
    by_contra hn
    rw [not_nonempty_iff_eq_empty, sdiff_eq_empty] at hn
    have h := closure_mono hn
    rw [hK.1.closure_interior_eq_closure_of_nonempty_interior hK.2.2.1,
      hK.2.1.isClosed.closure_eq, hK'.isClosed.closure_eq] at h
    exact hne (le_antisymm hsub h)
  have hpos : 0 < volume (K \ K') :=
    ((isOpen_interior.sdiff hK'.isClosed).measure_pos volume hn).trans_le
      (measure_mono (sdiff_subset_sdiff_left interior_subset))
  have hsplit : volume K = volume K' + volume (K \ K') := by
    rw [← measure_union disjoint_sdiff_right (hK.2.1.isClosed.measurableSet.diff
      hK'.isClosed.measurableSet), union_sdiff_cancel hsub]
  have hfin : volume K' < ⊤ := hK'.measure_lt_top
  have hlt : volume K' < volume K := by
    rw [hsplit]; exact ENNReal.lt_add_right hfin.ne hpos.ne'
  exact (ENNReal.toReal_lt_toReal hfin.ne hK.2.1.measure_lt_top.ne).2 hlt

/-- **A worst disk is irreducible** (Mahler's sense, `External.MahlerIrreducible.IsIrreducible`):
if a proper symmetric convex subdomain `K'` had `Δ(K') ≥ Δ(K)`, then by `irr_glpd_eq`
`δ_L(K') = area(K')/(4Δ(K')) < area(K)/(4Δ(K)) = δ_L(K)`. -/
theorem irr_isIrreducible_of_worst {K : Set (Fin 2 → ℝ)} (hK : IsWorstLatticeDisk K) :
    MahlerIrreducible.IsIrreducible K := by
  refine ⟨hK.1, fun K' hK' hsub hne ↦ ?_⟩
  by_contra hle
  push Not at hle
  have hΔ := MahlerIrreducible.irr_minimalDeterminant_pos hK.1
  have h1 := hK.2 K' hK'
  rw [irr_glpd_eq hK.1, irr_glpd_eq hK'] at h1
  have hv := irr_volume_lt hK.1 hK'.2.1 hsub hne
  have h2 : volume.real K' / (4 * minimalDeterminant K') ≤
      volume.real K' / (4 * minimalDeterminant K) :=
    div_le_div_of_nonneg_left measureReal_nonneg (by positivity) (by linarith)
  have h3 : volume.real K' / (4 * minimalDeterminant K) <
      volume.real K / (4 * minimalDeterminant K) :=
    div_lt_div_of_pos_right hv (by positivity)
  linarith

/-! ### A worst disk is not a parallelogram -/

lemma irr_isCCSDisk_euclidDisk : IsCCSDisk (euclidDisk 1) := by
  have hcont : Continuous fun x : Fin 2 → ℝ ↦ x 0 ^ 2 + x 1 ^ 2 := by fun_prop
  refine ⟨?_, ?_, ⟨0, ?_⟩, ?_⟩
  · intro x hx y hy s t hs ht hst
    simp only [euclidDisk, mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hy ⊢
    have ht' : t = 1 - s := by linarith
    subst ht'
    nlinarith [mul_nonneg hs ht, sq_nonneg (x 0 - y 0), sq_nonneg (x 1 - y 1)]
  · refine Metric.isCompact_of_isClosed_isBounded (isClosed_le hcont continuous_const)
      ((Metric.isBounded_closedBall (x := (0 : Fin 2 → ℝ)) (r := 1)).subset fun x hx ↦ ?_)
    simp only [euclidDisk, mem_ofPred_eq, one_pow] at hx
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    rw [Real.norm_eq_abs, ← sq_le_one_iff_abs_le_one]
    fin_cases i
    · simp only [Fin.zero_eta]; nlinarith [sq_nonneg (x 1)]
    · simp only [Fin.mk_one]; nlinarith [sq_nonneg (x 0)]
  · refine interior_maximal (t := {x : Fin 2 → ℝ | x 0 ^ 2 + x 1 ^ 2 < 1})
      (fun x (hx : x 0 ^ 2 + x 1 ^ 2 < 1) ↦ show x 0 ^ 2 + x 1 ^ 2 ≤ 1 ^ 2 by
        rw [one_pow]; exact hx.le) (isOpen_lt hcont continuous_const) ?_
    simp
  · intro x hx
    simp only [euclidDisk, mem_ofPred_eq, Pi.neg_apply, neg_sq] at hx ⊢
    exact hx

lemma irr_volume_euclidDisk : volume.real (euclidDisk 1) = Real.pi := by
  have heq : euclidDisk 1 =
      (WithLp.toLp 2 : (Fin 2 → ℝ) → EuclideanSpace ℝ (Fin 2)) ⁻¹' Metric.closedBall 0 1 := by
    ext x
    simp only [euclidDisk, mem_ofPred_eq, mem_preimage, mem_closedBall_zero_iff, one_pow]
    rw [← sq_le_one_iff₀ (norm_nonneg _), EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_two]
  rw [heq, measureReal_def, (PiLp.volume_preserving_toLp (Fin 2)).measure_preimage
    measurableSet_closedBall.nullMeasurableSet, EuclideanSpace.volume_closedBall_fin_two]
  simp [Real.pi_pos.le]

/-- **The Euclidean disk has `Δ ≥ √3/2`**: a reduced basis `u, v` of an admissible lattice has
`|u|, |v| ≥ 1` and `2|⟨u, v⟩| ≤ |u|²`, so `det(u, v)² = |u|²|v|² - ⟨u, v⟩² ≥ 3/4`. -/
lemma irr_minimalDeterminant_euclidDisk : √3 / 2 ≤ minimalDeterminant (euclidDisk 1) := by
  obtain ⟨Λ₀, hΛ₀⟩ := MahlerIrreducible.irr_exists_critical irr_isCCSDisk_euclidDisk
  refine le_csInf ⟨_, Λ₀, hΛ₀.1, hΛ₀.2.1, rfl⟩ ?_
  rintro _ ⟨Λ, ⟨hd, hs⟩, hadm, rfl⟩
  have : IsZLattice ℝ Λ := ⟨hs⟩
  obtain ⟨u, v, hspan, hcr, hmin, huv, hip⟩ := PlaneLattice.exists_reduced_basis Λ
  have hu : u ∈ Λ := hspan ▸ Submodule.subset_span (by simp)
  have hu0 : u ≠ 0 := by rintro rfl; simp at hcr
  -- `|u|² ≥ 1`
  have hu1 : 1 ≤ u 0 ^ 2 + u 1 ^ 2 := by
    by_contra h
    push Not at h
    apply hu0
    refine hadm u hu (interior_maximal (t := {x : Fin 2 → ℝ | x 0 ^ 2 + x 1 ^ 2 < 1})
      (fun x (hx : x 0 ^ 2 + x 1 ^ 2 < 1) ↦ show x 0 ^ 2 + x 1 ^ 2 ≤ 1 ^ 2 by
        rw [one_pow]; exact hx.le) (isOpen_lt (by fun_prop) continuous_const) h)
  have hdet : det Λ = |cross u v| := by
    rw [← hspan]; exact mm_det_span hcr
  rw [hdet]
  have hlag : cross u v ^ 2 + (u 0 * v 0 + u 1 * v 1) ^ 2 =
      (u 0 ^ 2 + u 1 ^ 2) * (v 0 ^ 2 + v 1 ^ 2) := by
    simp only [cross]; ring
  have hip2 : (u 0 * v 0 + u 1 * v 1) ^ 2 ≤ (u 0 ^ 2 + u 1 ^ 2) ^ 2 / 4 := by
    have h0 : 0 ≤ |u 0 * v 0 + u 1 * v 1| := abs_nonneg _
    have := mul_le_mul hip hip (by positivity) (by positivity)
    rw [← sq_abs (u 0 * v 0 + u 1 * v 1)]
    nlinarith
  have h34 : 3 / 4 ≤ cross u v ^ 2 := by nlinarith
  have hs3 : (√3 / 2) ^ 2 = 3 / 4 := by rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  by_contra hlt
  push Not at hlt
  have := mul_self_lt_mul_self (abs_nonneg _) hlt
  rw [← sq, ← sq, sq_abs, hs3] at this
  linarith

/-- The Euclidean disk has `δ_L < 1`. -/
lemma irr_glpd_euclidDisk_lt_one : greatestLatticePackingDensity (euclidDisk 1) < 1 := by
  rw [irr_glpd_eq irr_isCCSDisk_euclidDisk, irr_volume_euclidDisk]
  have hΔ := irr_minimalDeterminant_euclidDisk
  have hs : (1.7 : ℝ) < √3 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hpi := Real.pi_lt_d2
  rw [div_lt_one (by linarith)]
  linarith

/-- The coordinates in a basis `u, v`: `x = (det(x, v)/det(u, v)) u + (det(u, x)/det(u, v)) v`. -/
lemma irr_coord_dot {u v : Fin 2 → ℝ} (huv : cross u v ≠ 0) :
    ∃ a : Fin 2 → ℝ, a ≠ 0 ∧ ∀ s t : ℝ, a ⬝ᵥ (s • u + t • v) = s := by
  refine ⟨(cross u v)⁻¹ • ![v 1, -v 0], ?_, fun s t ↦ ?_⟩
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
      Pi.zero_apply, mul_eq_zero, inv_eq_zero, huv, false_or, neg_eq_zero] at h0 h1
    apply huv
    simp only [cross, h0, h1]; ring
  · simp only [dotProduct, Fin.sum_univ_two, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    simp only [cross]; ring

/-- A centrally symmetric parallelogram `K` has `δ_L(K) ≥ 1` (indeed `= 1`): its center is the
origin, the lattice with basis the half-sides `u, v` is admissible, and `area(K) = 4|det(u, v)|`. -/
lemma irr_one_le_glpd_of_parallelogram {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K)
    (hP : Mahler1947.IsParallelogram K) : 1 ≤ greatestLatticePackingDensity K := by
  obtain ⟨c, u, v, huv, hKeq⟩ := hP
  have hmem : ∀ x, x ∈ K ↔ ∃ s t : ℝ, |s| ≤ 1 ∧ |t| ≤ 1 ∧ x = c + s • u + t • v :=
    fun x ↦ by rw [hKeq]; rfl
  -- independence of `u, v`
  have hind : ∀ α β : ℝ, α • u + β • v = 0 → α = 0 ∧ β = 0 := by
    intro α β h
    have hli := mm_linearIndependent_real huv
    rw [LinearIndependent.pair_iff] at hli
    exact hli α β h
  -- the center is the origin
  have hc : c = 0 := by
    have h1 := hK.2.2.2 _ ((hmem _).2 ⟨1, 1, by simp, by simp, rfl⟩)
    have h2 := hK.2.2.2 _ ((hmem _).2 ⟨-1, -1, by simp, by simp, rfl⟩)
    obtain ⟨s, t, hs, ht, hst⟩ := (hmem _).1 h1
    obtain ⟨s', t', hs', ht', hst'⟩ := (hmem _).1 h2
    have := hind (2 + s - s') (2 + t - t') (by
      have e : (2 + s - s') • u + (2 + t - t') • v =
          ((c + s • u + t • v) - -(c + (1 : ℝ) • u + (1 : ℝ) • v)) -
            ((c + s' • u + t' • v) - -(c + (-1 : ℝ) • u + (-1 : ℝ) • v)) := by module
      rw [e, ← hst, ← hst']; simp)
    rw [abs_le] at hs ht hs' ht'
    have hs1 : s = -1 := by linarith [this.1]
    have ht1 : t = -1 := by linarith [this.2]
    have e2 : (2 : ℝ) • c = 0 := by
      have e : (2 : ℝ) • c = (c + s • u + t • v) - (-(c + (1 : ℝ) • u + (1 : ℝ) • v)) -
          ((1 + s) • u + (1 + t) • v) := by module
      rw [e, ← hst, hs1, ht1]; simp
    have := congrArg (fun y ↦ (1 / 2 : ℝ) • y) e2
    simpa [smul_smul] using this
  subst hc
  have hmem' : ∀ x, x ∈ K ↔ ∃ s t : ℝ, |s| ≤ 1 ∧ |t| ≤ 1 ∧ x = s • u + t • v := by
    intro x; rw [hmem]; simp only [zero_add]
  -- the lattice with basis `u, v` is admissible
  have hadm : IsAdmissible K (Submodule.span ℤ {u, v}) := by
    intro x hx hxK
    obtain ⟨m, n, rfl⟩ := mm_mem_span_pair.1 hx
    have hcoord : ∀ a : Fin 2 → ℝ, a ≠ 0 →
        (∀ s t : ℝ, |s| ≤ 1 → |t| ≤ 1 → a ⬝ᵥ (s • u + t • v) ≤ 1) →
        ∀ y ∈ interior K, |a ⬝ᵥ y| < 1 := by
      intro a ha hle y hy
      have hle' : ∀ z ∈ K, a ⬝ᵥ z ≤ 1 := by
        intro z hz
        obtain ⟨s', t', hs', ht', rfl⟩ := (hmem' z).1 hz
        exact hle s' t' hs' ht'
      have h1 := MahlerIrreducible.irr_dot_lt ha hle' hy
      have h2 := MahlerIrreducible.irr_dot_lt ha hle' (mm_neg_mem_interior hK hy)
      rw [dotProduct_neg] at h2
      exact abs_lt.2 ⟨by linarith, h1⟩
    obtain ⟨a, ha, hav⟩ := irr_coord_dot huv
    have huv' : cross v u ≠ 0 := by rw [mm_cross_swap]; exact neg_ne_zero.2 huv
    obtain ⟨b, hb, hbv⟩ := irr_coord_dot huv'
    have hbv' : ∀ s t : ℝ, b ⬝ᵥ (s • u + t • v) = t := fun s t ↦ by
      rw [add_comm]; exact hbv t s
    have hm := hcoord a ha (fun s t hs _ ↦ by rw [hav]; exact (abs_le.1 hs).2) _ hxK
    have hn := hcoord b hb (fun s t _ ht ↦ by rw [hbv']; exact (abs_le.1 ht).2) _ hxK
    rw [hav] at hm
    rw [hbv'] at hn
    have hm0 : m = 0 := Int.abs_lt_one_iff.1 (by exact_mod_cast hm)
    have hn0 : n = 0 := Int.abs_lt_one_iff.1 (by exact_mod_cast hn)
    simp [hm0, hn0]
  have hΔ := mm_minimalDeterminant_le (mm_isLattice_span huv) hadm
  rw [mm_det_span huv] at hΔ
  have hΔpos := MahlerIrreducible.irr_minimalDeterminant_pos hK
  -- `area(K) = 4|det(u, v)|`
  have hvol : volume.real K = 4 * |cross u v| := by
    have himg : K = Matrix.toLin' !![u 0, v 0; u 1, v 1] '' Icc (-1) 1 := by
      have hM : ∀ y : Fin 2 → ℝ, Matrix.toLin' !![u 0, v 0; u 1, v 1] y = y 0 • u + y 1 • v := by
        intro y; ext i
        fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring
      ext x
      simp only [hmem', mem_image, hM, mem_Icc, Pi.le_def, Fin.forall_fin_two, Pi.neg_apply,
        Pi.one_apply]
      constructor
      · rintro ⟨s, t, hs, ht, rfl⟩
        rw [abs_le] at hs ht
        exact ⟨![s, t], ⟨⟨hs.1, ht.1⟩, hs.2, ht.2⟩, by simp⟩
      · rintro ⟨y, ⟨⟨h0, h1⟩, h2, h3⟩, rfl⟩
        exact ⟨y 0, y 1, abs_le.2 ⟨h0, h2⟩, abs_le.2 ⟨h1, h3⟩, rfl⟩
    rw [himg, measureReal_def, Measure.addHaar_image_linearMap, LinearMap.det_toLin',
      Real.volume_Icc_pi, Matrix.det_fin_two_of]
    have : u 0 * v 1 - v 0 * u 1 = cross u v := by simp only [cross]; ring
    rw [this]
    simp only [Pi.one_apply, Pi.neg_apply, sub_neg_eq_add, Fin.prod_univ_two]
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul]
    simp; norm_num
    ring
  rw [irr_glpd_eq hK, hvol, le_div_iff₀ (by positivity)]
  linarith

/-- **A worst disk is not a parallelogram**: a parallelogram has `δ_L ≥ 1`
(`irr_one_le_glpd_of_parallelogram`), while the Euclidean disk has `δ_L < 1`. -/
theorem irr_not_isParallelogram_of_worst {K : Set (Fin 2 → ℝ)} (hK : IsWorstLatticeDisk K) :
    ¬ Mahler1947.IsParallelogram K := fun hP ↦ by
  have h1 := irr_one_le_glpd_of_parallelogram hK.1 hP
  have h2 := hK.2 _ irr_isCCSDisk_euclidDisk
  linarith [irr_glpd_euclidDisk_lt_one]

/-! ### Mahler's hexagon at a point of a critical lattice -/

/-- The centrally symmetric hexagon with vertices `a, b, c, -a, -b, -c` (the same as `rein_hex3`
of `SmoothedPolygons.Ch2.Reinhardt`, which imports this file). -/
def irr_hex3 (a b c : Fin 2 → ℝ) : ZMod 6 → Fin 2 → ℝ :=
  fun k ↦ (![a, b, c, -a, -b, -c] : Fin 6 → Fin 2 → ℝ) k

lemma irr_zmod6_cases (k : ZMod 6) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by
  revert k; decide

lemma irr_hex3_add_three (a b c : Fin 2 → ℝ) (k : ZMod 6) :
    irr_hex3 a b c (k + 3) = -irr_hex3 a b c k := by
  rcases irr_zmod6_cases k with rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · rfl
  · rfl
  · exact (neg_neg a).symm
  · exact (neg_neg b).symm
  · exact (neg_neg c).symm

lemma irr_hex3_forall (P : (Fin 2 → ℝ) → Prop) (hP : ∀ x, P x → P (-x)) {a b c : Fin 2 → ℝ}
    (ha : P a) (hb : P b) (hc : P c) (k : ZMod 6) : P (irr_hex3 a b c k) := by
  rcases irr_zmod6_cases k with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact hc
  · exact hP _ ha
  · exact hP _ hb
  · exact hP _ hc

/-- Two lines `{a · x = 1}`, `{b · x = 1}` that coincide have `a = b`. -/
lemma irr_eq_of_line_subset {a b : Fin 2 → ℝ} (ha : a ≠ 0)
    (h : {x : Fin 2 → ℝ | a ⬝ᵥ x = 1} ⊆ {x | b ⬝ᵥ x = 1}) : b = a := by
  have hN : 0 < a 0 ^ 2 + a 1 ^ 2 := by
    by_contra hle
    apply ha
    ext i; fin_cases i <;> simp <;> nlinarith [sq_nonneg (a 0), sq_nonneg (a 1)]
  have hN' := hN.ne'
  have hp : a ⬝ᵥ ![a 0 / (a 0 ^ 2 + a 1 ^ 2), a 1 / (a 0 ^ 2 + a 1 ^ 2)] = 1 := by
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
  have hq : a ⬝ᵥ ![a 0 / (a 0 ^ 2 + a 1 ^ 2) - a 1, a 1 / (a 0 ^ 2 + a 1 ^ 2) + a 0] = 1 := by
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    ring
  have hbp : b ⬝ᵥ _ = 1 := h hp
  have hbq : b ⬝ᵥ _ = 1 := h hq
  simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hbp hbq
  have e1 : b 0 * a 0 + b 1 * a 1 = a 0 ^ 2 + a 1 ^ 2 := by
    field_simp at hbp
    linarith
  have e2 : b 1 * a 0 - b 0 * a 1 = 0 := by linarith
  have h0 : b 0 = a 0 := by
    apply mul_right_cancel₀ hN'
    linear_combination a 0 * e1 - a 1 * e2
  have h1 : b 1 = a 1 := by
    apply mul_right_cancel₀ hN'
    linear_combination a 1 * e1 + a 0 * e2
  ext i; fin_cases i
  · exact h0
  · exact h1

lemma irr_eq_of_line_eq {a b : Fin 2 → ℝ}
    (h : {x : Fin 2 → ℝ | a ⬝ᵥ x = 1} = {x | b ⬝ᵥ x = 1}) : a = b := by
  by_cases ha : a = 0
  · by_cases hb : b = 0
    · rw [ha, hb]
    · exact irr_eq_of_line_subset hb h.symm.subset
  · exact (irr_eq_of_line_subset ha h.subset).symm

/-- `K` lies on the side of each of its tac-lines `a · x = 1` that contains the origin. -/
lemma irr_dot_le_one {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {a : Fin 2 → ℝ}
    (ha : Mahler1947.IsTacLine K {x | a ⬝ᵥ x = 1}) {x : Fin 2 → ℝ} (hx : x ∈ K) :
    a ⬝ᵥ x ≤ 1 := by
  obtain ⟨⟨b, hb0, c, hℓ, hbK⟩, -⟩ := ha
  have hc : 0 < c := by
    simpa using MahlerIrreducible.irr_dot_lt hb0 hbK (mm_zero_mem_interior hK)
  have hba : c⁻¹ • b = a := by
    refine irr_eq_of_line_eq (Set.ext fun y ↦ ?_)
    have := Set.ext_iff.1 hℓ y
    simp only [mem_ofPred_eq] at this ⊢
    rw [smul_dotProduct, smul_eq_mul, inv_mul_eq_one₀ hc.ne', this, eq_comm]
  rw [← hba, smul_dotProduct, smul_eq_mul, inv_mul_le_iff₀ hc, mul_one]
  exact hbK x hx

/-- The strip between two parallel lines `a · x = ±1`, with `p, q` on the line `a · x = 1`, is
`|det(p - q, x)| ≤ det(p, q)`. -/
lemma irr_strip {a p q y : Fin 2 → ℝ} (hp : a ⬝ᵥ p = 1) (hq : a ⬝ᵥ q = 1) (hpq : 0 < det2 p q)
    (h1 : a ⬝ᵥ y ≤ 1) (h2 : (-a) ⬝ᵥ y ≤ 1) : |det2 (p - q) y| ≤ det2 p q := by
  have key : a ⬝ᵥ y * det2 p q = det2 (p - q) y := by
    simp only [dotProduct, Fin.sum_univ_two, det2, Pi.sub_apply] at hp hq ⊢
    linear_combination (y 0 * q 1 - y 1 * q 0) * hp + (p 0 * y 1 - p 1 * y 0) * hq
  rw [neg_dotProduct] at h2
  rw [abs_le, ← key]
  constructor <;> nlinarith

/-- The six vertices of a hexagon bounded by symmetric lines `a_j · x = 1` (`a_{j+3} = -a_j`)
through the points `s_j = ±e, ±(e + f), ±f`, in terms of `α_j = a_j · s_{j+1} ∈ (0, 1)`:
`w₀ = ℓ₅ ∩ ℓ₀`, `w₁ = ℓ₀ ∩ ℓ₁`, `w₂ = ℓ₁ ∩ ℓ₂` (as in the proof of Theorem 2.3.9). Its area
`det(w₀, w₁) + det(w₁, w₂) + det(w₀, w₂)` is `(4 - p²/(D₀ D₁ D₂)) det(e, f) ≤ 4 det(e, f)`, with
`p = α₀α₁α₂ - (1 - α₀)(1 - α₁)(1 - α₂)` and `D_j = 1 - α_j + α_j α_{j+1}` (Mahler's formula). -/
lemma irr_hexagon_of_dots {e f a₀ a₁ a₂ : Fin 2 → ℝ} {α₀ α₁ α₂ : ℝ} (hD : 0 < det2 e f)
    (h0 : 0 < α₀) (h0' : α₀ < 1) (h1 : 0 < α₁) (h1' : α₁ < 1) (h2 : 0 < α₂) (h2' : α₂ < 1)
    (d0e : a₀ ⬝ᵥ e = 1) (d0f : a₀ ⬝ᵥ f = α₀ - 1) (d1e : a₁ ⬝ᵥ e = 1 - α₁) (d1f : a₁ ⬝ᵥ f = α₁)
    (d2e : a₂ ⬝ᵥ e = -α₂) (d2f : a₂ ⬝ᵥ f = 1) :
    ∃ w₀ w₁ w₂ : Fin 2 → ℝ,
      (0 < det2 w₀ w₁ ∧ 0 < det2 w₁ w₂ ∧ 0 < det2 w₀ w₂ ∧ det2 w₀ w₂ < det2 w₀ w₁ + det2 w₁ w₂ ∧
        det2 w₀ w₁ < det2 w₁ w₂ + det2 w₀ w₂ ∧ det2 w₁ w₂ < det2 w₀ w₁ + det2 w₀ w₂) ∧
      a₀ ⬝ᵥ w₀ = 1 ∧ a₀ ⬝ᵥ w₁ = 1 ∧ a₁ ⬝ᵥ w₁ = 1 ∧ a₁ ⬝ᵥ w₂ = 1 ∧ a₂ ⬝ᵥ w₂ = 1 ∧
      a₂ ⬝ᵥ -w₀ = 1 ∧ det2 w₀ w₁ + det2 w₁ w₂ + det2 w₀ w₂ ≤ 4 * det2 e f := by
  obtain ⟨D₀, hD₀def⟩ : ∃ x : ℝ, x = 1 - α₀ + α₀ * α₁ := ⟨_, rfl⟩
  obtain ⟨D₁, hD₁def⟩ : ∃ x : ℝ, x = 1 - α₁ + α₁ * α₂ := ⟨_, rfl⟩
  obtain ⟨D₂, hD₂def⟩ : ∃ x : ℝ, x = 1 - α₂ + α₂ * α₀ := ⟨_, rfl⟩
  have hD₀ : 0 < D₀ := by rw [hD₀def]; nlinarith
  have hD₁ : 0 < D₁ := by rw [hD₁def]; nlinarith
  have hD₂ : 0 < D₂ := by rw [hD₂def]; nlinarith
  have hD₀' := hD₀.ne'
  have hD₁' := hD₁.ne'
  have hD₂' := hD₂.ne'
  obtain ⟨w₀, hw₀⟩ : ∃ w : Fin 2 → ℝ, w = (α₀ / D₂) • e + (-(1 - α₂) / D₂) • f := ⟨_, rfl⟩
  obtain ⟨w₁, hw₁⟩ : ∃ w : Fin 2 → ℝ, w = ((1 - α₀ + α₁) / D₀) • e + (α₁ / D₀) • f := ⟨_, rfl⟩
  obtain ⟨w₂, hw₂⟩ : ∃ w : Fin 2 → ℝ, w = ((1 - α₁) / D₁) • e + ((1 - α₁ + α₂) / D₁) • f :=
    ⟨_, rfl⟩
  obtain ⟨l₀, hl₀⟩ : ∃ x : ℝ, x = α₁ / D₀ + (1 - α₂) / D₂ := ⟨_, rfl⟩
  obtain ⟨l₁, hl₁⟩ : ∃ x : ℝ, x = α₂ / D₁ + (1 - α₀) / D₀ := ⟨_, rfl⟩
  obtain ⟨l₂, hl₂⟩ : ∃ x : ℝ, x = α₀ / D₂ + (1 - α₁) / D₁ := ⟨_, rfl⟩
  have hl₀p : 0 < l₀ := hl₀ ▸ add_pos (div_pos h1 hD₀) (div_pos (by linarith) hD₂)
  have hl₁p : 0 < l₁ := hl₁ ▸ add_pos (div_pos h2 hD₁) (div_pos (by linarith) hD₀)
  have hl₂p : 0 < l₂ := hl₂ ▸ add_pos (div_pos h0 hD₂) (div_pos (by linarith) hD₁)
  have hcomb : ∀ p q r t : ℝ, det2 (p • e + q • f) (r • e + t • f) = (p * t - q * r) * det2 e f :=
    fun p q r t ↦ by simp only [det2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have eA : det2 w₀ w₁ = l₀ * det2 e f := by
    rw [hw₀, hw₁, hcomb, hl₀]
    congr 1
    field_simp
    rw [hD₀def, hD₂def]
    ring
  have eB : det2 w₁ w₂ = l₁ * det2 e f := by
    rw [hw₁, hw₂, hcomb, hl₁]
    congr 1
    field_simp
    rw [hD₀def, hD₁def]
    ring
  have eC : det2 w₀ w₂ = l₂ * det2 e f := by
    rw [hw₀, hw₂, hcomb, hl₂]
    congr 1
    field_simp
    rw [hD₁def, hD₂def]
    ring
  have t01 : l₀ + l₁ - l₂ = l₀ * l₁ * ((1 - α₀) * (1 - α₁) + α₁) := by
    rw [hl₀, hl₁, hl₂]
    field_simp
    rw [hD₀def, hD₁def, hD₂def]
    ring
  have t12 : l₁ + l₂ - l₀ = l₁ * l₂ * (α₁ * α₂ + (1 - α₁)) := by
    rw [hl₀, hl₁, hl₂]
    field_simp
    rw [hD₀def, hD₁def, hD₂def]
    ring
  have t02 : l₀ + l₂ - l₁ = l₀ * l₂ * (1 - α₂ + α₀ * α₂) := by
    rw [hl₀, hl₁, hl₂]
    field_simp
    rw [hD₀def, hD₁def, hD₂def]
    ring
  -- Mahler's area formula: `4 - (l₀ + l₁ + l₂) = p² / (D₀ D₁ D₂)`
  have tsum : (4 - (l₀ + l₁ + l₂)) * (D₀ * D₁ * D₂) =
      (α₀ * α₁ * α₂ - (1 - α₀) * (1 - α₁) * (1 - α₂)) ^ 2 := by
    rw [hl₀, hl₁, hl₂]
    field_simp
    rw [hD₀def, hD₁def, hD₂def]
    ring
  have hsum4 : l₀ + l₁ + l₂ ≤ 4 := by
    have hp := sq_nonneg (α₀ * α₁ * α₂ - (1 - α₀) * (1 - α₁) * (1 - α₂))
    rw [← tsum] at hp
    have hDDD : 0 < D₀ * D₁ * D₂ := by positivity
    by_contra h
    push Not at h
    have := mul_neg_of_neg_of_pos (sub_neg.2 h) hDDD
    linarith
  have c01 : 0 < (1 - α₀) * (1 - α₁) + α₁ :=
    add_pos (mul_pos (by linarith) (by linarith)) h1
  have c12 : 0 < α₁ * α₂ + (1 - α₁) := add_pos (mul_pos h1 h2) (by linarith)
  have c02 : 0 < 1 - α₂ + α₀ * α₂ := add_pos (by linarith) (mul_pos h0 h2)
  refine ⟨w₀, w₁, w₂, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eA]; exact mul_pos hl₀p hD
  · rw [eB]; exact mul_pos hl₁p hD
  · rw [eC]; exact mul_pos hl₂p hD
  · rw [eA, eB, eC]
    have key : l₀ * det2 e f + l₁ * det2 e f - l₂ * det2 e f =
        l₀ * l₁ * ((1 - α₀) * (1 - α₁) + α₁) * det2 e f := by rw [← t01]; ring
    have := mul_pos (mul_pos (mul_pos hl₀p hl₁p) c01) hD
    linarith
  · rw [eA, eB, eC]
    have key : l₁ * det2 e f + l₂ * det2 e f - l₀ * det2 e f =
        l₁ * l₂ * (α₁ * α₂ + (1 - α₁)) * det2 e f := by rw [← t12]; ring
    have := mul_pos (mul_pos (mul_pos hl₁p hl₂p) c12) hD
    linarith
  · rw [eA, eB, eC]
    have key : l₀ * det2 e f + l₂ * det2 e f - l₁ * det2 e f =
        l₀ * l₂ * (1 - α₂ + α₀ * α₂) * det2 e f := by rw [← t02]; ring
    have := mul_pos (mul_pos (mul_pos hl₀p hl₂p) c02) hD
    linarith
  · rw [hw₀]
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, d0e, d0f]
    field_simp
    rw [hD₂def]
    ring
  · rw [hw₁]
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, d0e, d0f]
    field_simp
    rw [hD₀def]
    ring
  · rw [hw₁]
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, d1e, d1f]
    field_simp
    rw [hD₀def]
    ring
  · rw [hw₂]
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, d1e, d1f]
    field_simp
    rw [hD₁def]
    ring
  · rw [hw₂]
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, d2e, d2f]
    field_simp
    rw [hD₁def]
    ring
  · rw [hw₀]
    simp only [dotProduct_neg, dotProduct_add, dotProduct_smul, smul_eq_mul, d2e, d2f]
    field_simp
    rw [hD₂def]
    ring
  · rw [eA, eB, eC, ← add_mul, ← add_mul]
    exact mul_le_mul_of_nonneg_right hsum4 hD.le

/-- **Mahler's hexagon as a centrally symmetric hexagon** (as in the proof of Theorem 2.3.9). Let
`s₀, …, s₅` be points of `K` with `s₀ - s₁ + s₂ = 0`, `s_{j+3} = -s_j` and `det(s₀, s₁) > 0`, and
let `ℓ_j = {a_j · x = 1}` be the tac-lines of Mahler's Theorem 2 at the `s_j`. Then the lines
`ℓ_j` are the lines of the edges of the hexagon with vertices `w₀, w₁, w₂, -w₀, -w₁, -w₂`, which
contains `K` and has area at most `4 det(s₀, s₁)`. Since `ℓ_j` is the only tac-line at `s_j` and
no two of the lines coincide, `s_j` lies on no other `ℓ_k`, so `α_j = a_j · s_{j+1} ∈ (0, 1)`. -/
lemma irr_hexagon_of_mahler {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {s a : ZMod 6 → Fin 2 → ℝ}
    (h012 : s 0 - s 1 + s 2 = 0) (hsymm : ∀ j, s (j + 3) = -s j) (hsK : ∀ j, s j ∈ K)
    (hpos : 0 < det2 (s 0) (s 1)) (ha : Mahler1947.IsMahlerHexagon K s a) :
    ∃ w₀ w₁ w₂ : Fin 2 → ℝ,
      (0 < det2 w₀ w₁ ∧ 0 < det2 w₁ w₂ ∧ 0 < det2 w₀ w₂ ∧ det2 w₀ w₂ < det2 w₀ w₁ + det2 w₁ w₂ ∧
        det2 w₀ w₁ < det2 w₁ w₂ + det2 w₀ w₂ ∧ det2 w₁ w₂ < det2 w₀ w₁ + det2 w₀ w₂) ∧
      (∀ y ∈ K, |det2 (w₀ - w₁) y| ≤ det2 w₀ w₁ ∧ |det2 (w₁ - w₂) y| ≤ det2 w₁ w₂ ∧
        |det2 (w₂ + w₀) y| ≤ det2 w₀ w₂) ∧
      det2 w₀ w₁ + det2 w₁ w₂ + det2 w₀ w₂ ≤ 4 * det2 (s 0) (s 1) ∧
      ∀ k, a k ⬝ᵥ irr_hex3 w₀ w₁ w₂ k = 1 ∧ a k ⬝ᵥ irr_hex3 w₀ w₁ w₂ (k + 1) = 1 := by
  obtain ⟨hasymm, hsupp, huniq, hdist, -, -, -⟩ := ha
  -- `a_k · s_j ≤ 1`, with equality only for `k = j`
  have hle : ∀ k j, a k ⬝ᵥ s j ≤ 1 := fun k j ↦ irr_dot_le_one hK (hsupp k).1 (hsK j)
  have hlt : ∀ k j, k ≠ j → a k ⬝ᵥ s j < 1 := by
    intro k j hkj
    refine (hle k j).lt_of_ne fun heq ↦ hdist k j hkj ?_
    exact irr_eq_of_line_eq (huniq j _ (hsupp k).1 heq)
  -- the points in the basis `e = s₀`, `f = s₂`
  have hs1 : s 1 = s 0 + s 2 := by rw [← sub_eq_zero, ← neg_eq_zero, ← h012]; abel
  have hs3 : s 3 = -s 0 := hsymm 0
  have hs5 : s 5 = -s 2 := hsymm 2
  have hD : 0 < det2 (s 0) (s 2) := by
    have : det2 (s 0) (s 1) = det2 (s 0) (s 2) := by
      rw [hs1]; simp only [det2, Pi.add_apply]; ring
    linarith
  have d0e : a 0 ⬝ᵥ s 0 = 1 := (hsupp 0).2
  have d0f : a 0 ⬝ᵥ s 2 = a 0 ⬝ᵥ s 1 - 1 := by rw [hs1, dotProduct_add, d0e]; ring
  have d1e : a 1 ⬝ᵥ s 0 = 1 - a 1 ⬝ᵥ s 2 := by
    have h := (hsupp 1).2
    rw [hs1, dotProduct_add] at h
    linarith
  have d2f : a 2 ⬝ᵥ s 2 = 1 := (hsupp 2).2
  have d2e : a 2 ⬝ᵥ s 0 = -(a 2 ⬝ᵥ s 3) := by rw [hs3, dotProduct_neg, neg_neg]
  -- `α_j ∈ (0, 1)`
  have h0' : a 0 ⬝ᵥ s 1 < 1 := hlt 0 1 (by decide)
  have h0 : 0 < a 0 ⬝ᵥ s 1 := by
    have := hlt 0 5 (by decide)
    rw [hs5, dotProduct_neg, d0f] at this
    linarith
  have h1' : a 1 ⬝ᵥ s 2 < 1 := hlt 1 2 (by decide)
  have h1 : 0 < a 1 ⬝ᵥ s 2 := by
    have := hlt 1 0 (by decide)
    rw [d1e] at this
    linarith
  have h2' : a 2 ⬝ᵥ s 3 < 1 := hlt 2 3 (by decide)
  have h2 : 0 < a 2 ⬝ᵥ s 3 := by
    have := hlt 2 1 (by decide)
    rw [hs1, dotProduct_add, d2e, d2f] at this
    linarith
  obtain ⟨w₀, w₁, w₂, hc, l00, l01, l11, l12, l22, l23, hsum⟩ :=
    irr_hexagon_of_dots hD h0 h0' h1 h1' h2 h2' d0e d0f d1e rfl d2e d2f
  -- the edge lines
  have ha3 : a 3 = -a 0 := hasymm 0
  have ha4 : a 4 = -a 1 := hasymm 1
  have ha5 : a 5 = -a 2 := hasymm 2
  have hline3 : ∀ j, a j ⬝ᵥ irr_hex3 w₀ w₁ w₂ j = 1 ∧ a j ⬝ᵥ irr_hex3 w₀ w₁ w₂ (j + 1) = 1 →
      a (j + 3) ⬝ᵥ irr_hex3 w₀ w₁ w₂ (j + 3) = 1 ∧
        a (j + 3) ⬝ᵥ irr_hex3 w₀ w₁ w₂ (j + 3 + 1) = 1 := by
    rintro j ⟨e1, e2⟩
    rw [show j + 3 + 1 = j + 1 + 3 by ring, irr_hex3_add_three, irr_hex3_add_three, hasymm j,
      neg_dotProduct, neg_dotProduct, dotProduct_neg, dotProduct_neg, neg_neg, neg_neg]
    exact ⟨e1, e2⟩
  have hl0 : a 0 ⬝ᵥ irr_hex3 w₀ w₁ w₂ 0 = 1 ∧ a 0 ⬝ᵥ irr_hex3 w₀ w₁ w₂ (0 + 1) = 1 := ⟨l00, l01⟩
  have hl1 : a 1 ⬝ᵥ irr_hex3 w₀ w₁ w₂ 1 = 1 ∧ a 1 ⬝ᵥ irr_hex3 w₀ w₁ w₂ (1 + 1) = 1 := ⟨l11, l12⟩
  have hl2 : a 2 ⬝ᵥ irr_hex3 w₀ w₁ w₂ 2 = 1 ∧ a 2 ⬝ᵥ irr_hex3 w₀ w₁ w₂ (2 + 1) = 1 := ⟨l22, l23⟩
  have hline : ∀ j, a j ⬝ᵥ irr_hex3 w₀ w₁ w₂ j = 1 ∧ a j ⬝ᵥ irr_hex3 w₀ w₁ w₂ (j + 1) = 1 := by
    intro j
    rcases irr_zmod6_cases j with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hl0
    · exact hl1
    · exact hl2
    · exact hline3 0 hl0
    · exact hline3 1 hl1
    · exact hline3 2 hl2
  -- `K` lies in the three strips
  refine ⟨w₀, w₁, w₂, hc, fun y hy ↦ ?_, ?_, hline⟩
  · have hy : ∀ k, a k ⬝ᵥ y ≤ 1 := fun k ↦ irr_dot_le_one hK (hsupp k).1 hy
    refine ⟨irr_strip l00 l01 hc.1 (hy 0) (by rw [← ha3]; exact hy 3),
      irr_strip l11 l12 hc.2.1 (hy 1) (by rw [← ha4]; exact hy 4), ?_⟩
    have e : det2 (w₂ + w₀) y = det2 (w₂ - -w₀) y := by rw [sub_neg_eq_add]
    have e' : det2 w₀ w₂ = det2 w₂ (-w₀) := by simp only [det2, Pi.neg_apply]; ring
    rw [e, e']
    exact irr_strip l22 l23 (e' ▸ hc.2.2.1) (hy 2) (by rw [← ha5]; exact hy 5)
  · have : det2 (s 0) (s 1) = det2 (s 0) (s 2) := by
      rw [hs1]; simp only [det2, Pi.add_apply]; ring
    rw [this]; exact hsum

/-- The six points `±P₀, ±P₁, ±P₂` of a configuration of Mahler's Lemma 2 for a critical lattice
`Λ` of `K`, numbered counterclockwise: `s₀ - s₁ + s₂ = 0`, `s_{j+3} = -s_j`,
`det(s₀, s₁) = Δ(K) > 0`. -/
lemma irr_six_points {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {Λ : Submodule ℤ (Fin 2 → ℝ)}
    (hΛ : IsCritical K Λ) {P₀ P₁ P₂ : Fin 2 → ℝ} (h0Λ : P₀ ∈ Λ) (h1Λ : P₁ ∈ Λ) (h2Λ : P₂ ∈ Λ)
    (h0F : P₀ ∈ frontier K) (h1F : P₁ ∈ frontier K) (h2F : P₂ ∈ frontier K)
    (hB : IsBasis Λ P₀ P₁) (h012 : P₁ = P₀ + P₂) {ℓ : Set (Fin 2 → ℝ)}
    (hon : P₀ ∈ ℓ ∨ -P₀ ∈ ℓ ∨ P₁ ∈ ℓ ∨ -P₁ ∈ ℓ ∨ P₂ ∈ ℓ ∨ -P₂ ∈ ℓ) :
    ∃ s : ZMod 6 → Fin 2 → ℝ, (∀ j, s j ∈ Λ) ∧ (∀ j, s j ∈ frontier K) ∧ s 0 - s 1 + s 2 = 0 ∧
      (∀ j, s (j + 3) = -s j) ∧ 0 < det2 (s 0) (s 1) ∧ det2 (s 0) (s 1) = minimalDeterminant K ∧
      ∃ j, s j ∈ ℓ := by
  have hdet : |cross P₀ P₁| = minimalDeterminant K := by rw [← mm_det_eq hΛ.1 hB, hΛ.2.2]
  have hpos := MahlerIrreducible.irr_minimalDeterminant_pos hK
  have hc : cross P₀ P₁ = cross P₀ P₂ := by rw [h012]; simp only [cross, Pi.add_apply]; ring
  have hneg : ∀ x, x ∈ frontier K → -x ∈ frontier K := fun x hx ↦ mm_neg_mem_frontier hK hx
  rcases lt_or_ge (cross P₀ P₁) 0 with hlt | hge
  · -- clockwise: take `P₀, -P₂, -P₁`
    refine ⟨irr_hex3 P₀ (-P₂) (-P₁), irr_hex3_forall (· ∈ Λ) (fun x hx ↦ Λ.neg_mem hx) h0Λ
      (Λ.neg_mem h2Λ) (Λ.neg_mem h1Λ), irr_hex3_forall (· ∈ frontier K) hneg h0F (hneg _ h2F)
      (hneg _ h1F), ?_, irr_hex3_add_three _ _ _, ?_, ?_, ?_⟩
    · change P₀ - -P₂ + -P₁ = 0
      rw [h012]; abel
    · change 0 < det2 P₀ (-P₂)
      have : det2 P₀ (-P₂) = -cross P₀ P₁ := by
        rw [hc]; simp only [det2, cross, Pi.neg_apply]; ring
      rw [this]; linarith
    · change det2 P₀ (-P₂) = minimalDeterminant K
      have : det2 P₀ (-P₂) = -cross P₀ P₁ := by
        rw [hc]; simp only [det2, cross, Pi.neg_apply]; ring
      rw [this, ← hdet, abs_of_neg hlt]
    · rcases hon with h | h | h | h | h | h
      · exact ⟨0, h⟩
      · exact ⟨3, h⟩
      · exact ⟨5, by change -(-P₁) ∈ ℓ; rwa [neg_neg]⟩
      · exact ⟨2, h⟩
      · exact ⟨4, by change -(-P₂) ∈ ℓ; rwa [neg_neg]⟩
      · exact ⟨1, h⟩
  · have hgt : 0 < cross P₀ P₁ := by
      rcases hge.lt_or_eq with h | h
      · exact h
      · rw [← h, abs_zero] at hdet; linarith
    refine ⟨irr_hex3 P₀ P₁ P₂, irr_hex3_forall (· ∈ Λ) (fun x hx ↦ Λ.neg_mem hx) h0Λ h1Λ h2Λ,
      irr_hex3_forall (· ∈ frontier K) hneg h0F h1F h2F, ?_, irr_hex3_add_three _ _ _, hgt, ?_,
      ?_⟩
    · change P₀ - P₁ + P₂ = 0
      rw [h012]; abel
    · change cross P₀ P₁ = minimalDeterminant K
      rw [← hdet, abs_of_pos hgt]
    · rcases hon with h | h | h | h | h | h
      · exact ⟨0, h⟩
      · exact ⟨3, h⟩
      · exact ⟨1, h⟩
      · exact ⟨4, h⟩
      · exact ⟨2, h⟩
      · exact ⟨5, h⟩

/-- **The main step of Lemma 2.2.5.** Let `K` have the worst greatest lattice packing density and
let `{b · x = 1}` be a support line of `K` (`b · x ≤ 1` on `K`). By Mahler's Lemma 3
(`External.mahler_irreducible`; `K` is irreducible) the line passes through a point `x` of a
critical lattice of `K`, one of the six points `s_j` of Lemma 2. By Mahler's Theorem 2
(`External.mahler_1947`; `K` is not a parallelogram) the line is the only support line of `K` at
`x`, and it is the line of the edge `j` of the hexagon `w₀, w₁, w₂, -w₀, -w₁, -w₂` bounded by the
tac-lines at the `s_j`, which contains `K` (it is the intersection of three strips) and has area
`det(w₀, w₁) + det(w₁, w₂) + det(w₀, w₂) ≤ 4Δ(K)`. -/
theorem irr_main {K : Set (Fin 2 → ℝ)} (hK : IsWorstLatticeDisk K) {b : Fin 2 → ℝ}
    (hb : ∀ x ∈ K, b ⬝ᵥ x ≤ 1) (hbu : ∃ u ∈ K, b ⬝ᵥ u = 1) :
    ∃ x ∈ K, b ⬝ᵥ x = 1 ∧ (∀ c : Fin 2 → ℝ, (∀ y ∈ K, c ⬝ᵥ y ≤ 1) → c ⬝ᵥ x = 1 → c = b) ∧
      ∃ (w₀ w₁ w₂ : Fin 2 → ℝ) (j : ZMod 6),
        (0 < det2 w₀ w₁ ∧ 0 < det2 w₁ w₂ ∧ 0 < det2 w₀ w₂ ∧
          det2 w₀ w₂ < det2 w₀ w₁ + det2 w₁ w₂ ∧ det2 w₀ w₁ < det2 w₁ w₂ + det2 w₀ w₂ ∧
          det2 w₁ w₂ < det2 w₀ w₁ + det2 w₀ w₂) ∧
        (∀ y ∈ K, |det2 (w₀ - w₁) y| ≤ det2 w₀ w₁ ∧ |det2 (w₁ - w₂) y| ≤ det2 w₁ w₂ ∧
          |det2 (w₂ + w₀) y| ≤ det2 w₀ w₂) ∧
        det2 w₀ w₁ + det2 w₁ w₂ + det2 w₀ w₂ ≤ 4 * minimalDeterminant K ∧
        b ⬝ᵥ irr_hex3 w₀ w₁ w₂ j = 1 ∧ b ⬝ᵥ irr_hex3 w₀ w₁ w₂ (j + 1) = 1 := by
  obtain ⟨u, huK, hbu⟩ := hbu
  have hK1 := hK.1
  have hb0 : b ≠ 0 := by rintro rfl; simp at hbu
  have hℓ : Mahler1947.IsTacLine K {x | b ⬝ᵥ x = 1} := ⟨⟨b, hb0, 1, rfl, hb⟩, ⟨u, hbu, huK⟩⟩
  -- Mahler's Lemma 3: a point of a critical lattice on the line
  obtain ⟨Λ, P₀, P₁, P₂, hΛ, h0Λ, h1Λ, h2Λ, h0F, h1F, h2F, hB, h012, hon⟩ :=
    mahler_irreducible (irr_isIrreducible_of_worst hK) hℓ
  obtain ⟨s, hsΛ, hsF, hs012, hsymm, hpos, hsΔ, j, hj⟩ :=
    irr_six_points hK1 hΛ h0Λ h1Λ h2Λ h0F h1F h2F hB h012 hon
  -- Mahler's Theorem 2: the tac-lines at the six points and their hexagon
  obtain ⟨a, ha, -⟩ := mahler_1947 hK1 (irr_not_isParallelogram_of_worst hK) hΛ hsΛ hsF hs012
    hsymm
  have hsK : ∀ k, s k ∈ K := fun k ↦ mm_mem_of_frontier hK1 (hsF k)
  have hbj : b = a j := irr_eq_of_line_eq (ha.2.2.1 j _ hℓ hj)
  obtain ⟨w₀, w₁, w₂, hc, hstrip, hsum, hline⟩ :=
    irr_hexagon_of_mahler hK1 hs012 hsymm hsK hpos ha
  refine ⟨s j, hsK j, hj, fun c hc' hcx ↦ ?_, w₀, w₁, w₂, j, hc, hstrip, ?_, ?_, ?_⟩
  · have hc0 : c ≠ 0 := by rintro rfl; simp at hcx
    rw [hbj]
    exact irr_eq_of_line_eq (ha.2.2.1 j _ ⟨⟨c, hc0, 1, rfl, hc'⟩, ⟨s j, hcx, hsK j⟩⟩ hcx)
  · rw [← hsΔ]; exact hsum
  · rw [hbj]; exact (hline j).1
  · rw [hbj]; exact (hline j).2

/-! ### Support lines in the form `{b · x = 1}` -/

/-- A line `{a · x = c}`, `a ≠ 0`, with `K` on the side `a · x ≤ c` is `{b · x = 1}` with
`b · x ≤ 1` on `K` (`c > 0` since the origin is an interior point of `K`). -/
lemma irr_normal {K ℓ : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K)
    (h : ∃ a : Fin 2 → ℝ, a ≠ 0 ∧ ∃ c, ℓ = {x | a ⬝ᵥ x = c} ∧ ∀ x ∈ K, a ⬝ᵥ x ≤ c) :
    ∃ b : Fin 2 → ℝ, ℓ = {y | b ⬝ᵥ y = 1} ∧ ∀ y ∈ K, b ⬝ᵥ y ≤ 1 := by
  obtain ⟨a, ha, c, rfl, haK⟩ := h
  have hc : 0 < c := by
    simpa using MahlerIrreducible.irr_dot_lt ha haK (mm_zero_mem_interior hK)
  refine ⟨c⁻¹ • a, Set.ext fun y ↦ ?_, fun y hy ↦ ?_⟩
  · simp only [mem_ofPred_eq, smul_dotProduct, smul_eq_mul]
    rw [inv_mul_eq_one₀ hc.ne', eq_comm]
  · rw [smul_dotProduct, smul_eq_mul, inv_mul_le_iff₀ hc, mul_one]
    exact haK y hy

/-- At a boundary point `u` of `K` there is a support line `{b · x = 1}`. -/
lemma irr_exists_normal {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {u : Fin 2 → ℝ}
    (hu : u ∈ frontier K) : ∃ b : Fin 2 → ℝ, (∀ y ∈ K, b ⬝ᵥ y ≤ 1) ∧ b ⬝ᵥ u = 1 := by
  obtain ⟨f, hfu, hfK, -⟩ := mm_support hK hu
  set b : Fin 2 → ℝ := ![f (Pi.single 0 1), f (Pi.single 1 1)]
  have hf : ∀ y, b ⬝ᵥ y = f y := by
    intro y
    have hy : y = y 0 • (Pi.single 0 1 : Fin 2 → ℝ) + y 1 • (Pi.single 1 1 : Fin 2 → ℝ) := by
      ext i; fin_cases i <;> simp
    conv_rhs => rw [hy]
    simp only [map_add, map_smul, smul_eq_mul, dotProduct, Fin.sum_univ_two, b,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  exact ⟨b, fun y hy ↦ (hf y).symm ▸ hfK y hy, (hf u).symm ▸ hfu⟩

end SmoothedPolygons
