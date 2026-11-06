module

public import SmoothedPolygons.Ch2.Reinhardt

/-!
# Lemma 2.2.1 as printed is false

The book's Lemma 2.2.1 claims that every lattice packing `K + L` of a centrally symmetric convex
disk is realized inside a lattice *tiling* by a parallelogram or centrally symmetric hexagon
`H ⊇ K`. This file proves the negation of that statement (`lemma2_2_1_false_as_printed`) with the
"pinwheel" packing of the parallelogram `K = {y | |2y₀ + y₁| ≤ 1, |2y₁ - y₀| ≤ 1}` by `L = ℤ²`.
The corrected Lemma 2.2.1 (`SmoothedPolygons.lemma2_2_1`, Reinhardt's lemma in its classical form)
concludes that the translates `H + L` form a packing.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace SmoothedPolygons


/-- The pinwheel parallelogram `{y | |2y₀ + y₁| ≤ 1, |2y₁ - y₀| ≤ 1}`. -/
def tile_ceK : Set (Fin 2 → ℝ) := {y | |2 * y 0 + y 1| ≤ 1 ∧ |2 * y 1 - y 0| ≤ 1}

/-- The lattice `ℤ²`. -/
noncomputable abbrev tile_ceL : Submodule ℤ (Fin 2 → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 2)))

lemma tile_ce_mem_L {l : Fin 2 → ℝ} : l ∈ tile_ceL ↔ ∀ i, ∃ m : ℤ, (m : ℝ) = l i := by
  rw [tile_ceL, Module.Basis.mem_span_iff_repr_mem]
  simp [Pi.basisFun_repr]

lemma tile_ce_hL : IsPlaneLattice tile_ceL := ⟨inferInstance, IsZLattice.span_top⟩

lemma tile_ce_interior_K {x : Fin 2 → ℝ} (hx : x ∈ interior tile_ceK) :
    |2 * x 0 + x 1| < 1 ∧ |2 * x 1 - x 0| < 1 := by
  have hxK : x ∈ tile_ceK := interior_subset hx
  obtain ⟨h1, h2⟩ := hxK
  rw [abs_le] at h1 h2
  rw [abs_lt, abs_lt]
  obtain ⟨a, ha, ha'⟩ := rein_exists_add_smul_mem hx ![1, 0]
  obtain ⟨b, hb, hb'⟩ := rein_exists_add_smul_mem hx ![-1, 0]
  obtain ⟨c, hc, hc'⟩ := rein_exists_add_smul_mem hx ![0, 1]
  obtain ⟨d, hd, hd'⟩ := rein_exists_add_smul_mem hx ![0, -1]
  simp only [tile_ceK, mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero,
    Matrix.cons_val_one, abs_le] at ha' hb' hc' hd'
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · linarith [hb'.1.1]
  · linarith [ha'.1.2]
  · linarith [hd'.2.1]
  · linarith [hc'.2.2]

lemma tile_ce_zero_mem_interior_K : (0 : Fin 2 → ℝ) ∈ interior tile_ceK := by
  have hU : IsOpen {y : Fin 2 → ℝ | |2 * y 0 + y 1| < 1 ∧ |2 * y 1 - y 0| < 1} := by
    exact (isOpen_lt (by fun_prop) continuous_const).and
      (isOpen_lt (by fun_prop) continuous_const)
  refine mem_interior.2 ⟨{y : Fin 2 → ℝ | |2 * y 0 + y 1| < 1 ∧ |2 * y 1 - y 0| < 1},
    fun y hy ↦ ⟨hy.1.le, hy.2.le⟩, hU, ?_⟩
  simp

lemma tile_ce_hK : IsCCSDisk tile_ceK := by
  refine ⟨?_, ?_, ⟨0, tile_ce_zero_mem_interior_K⟩, ?_⟩
  · intro x hx y hy a b ha hb hab
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    rw [abs_le] at hx1 hx2 hy1 hy2
    simp only [tile_ceK, mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul, abs_le]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith
  · apply Metric.isCompact_of_isClosed_isBounded
    · change IsClosed ({y : Fin 2 → ℝ | |2 * y 0 + y 1| ≤ 1} ∩ {y | |2 * y 1 - y 0| ≤ 1})
      exact (isClosed_le (by fun_prop) continuous_const).inter
        (isClosed_le (by fun_prop) continuous_const)
    · refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨1, fun y hy ↦ ?_⟩
      obtain ⟨h1, h2⟩ := hy
      rw [abs_le] at h1 h2
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      fin_cases i <;> simp only [Real.norm_eq_abs, abs_le] <;> constructor <;>
        simp <;> linarith
  · intro x hx
    obtain ⟨h1, h2⟩ := hx
    refine ⟨?_, ?_⟩
    · simp only [Pi.neg_apply]
      rw [show 2 * -x 0 + -x 1 = -(2 * x 0 + x 1) by ring, abs_neg]; exact h1
    · simp only [Pi.neg_apply]
      rw [show 2 * -x 1 - -x 0 = -(2 * x 1 - x 0) by ring, abs_neg]; exact h2

lemma tile_ce_interior_translate (S : Set (Fin 2 → ℝ)) (l : Fin 2 → ℝ) :
    interior ((fun x ↦ x + l) '' S) = (fun x ↦ x + l) '' interior S := by
  rw [show (fun x : Fin 2 → ℝ ↦ x + l) = ⇑(Homeomorph.addRight l) from rfl,
    ← Homeomorph.image_interior]

lemma tile_ce_hKL : IsLatticePacking tile_ceK tile_ceL := by
  intro l hl l' hl' hne
  rw [Set.disjoint_left]
  intro y hy1 hy2
  rw [tile_ce_interior_translate] at hy1 hy2
  obtain ⟨x, hx, rfl⟩ := hy1
  obtain ⟨x', hx', hxx⟩ := hy2
  obtain ⟨a1, a2⟩ := tile_ce_interior_K hx
  obtain ⟨b1, b2⟩ := tile_ce_interior_K hx'
  obtain ⟨m0, hm0⟩ := tile_ce_mem_L.1 hl 0
  obtain ⟨m1, hm1⟩ := tile_ce_mem_L.1 hl 1
  obtain ⟨n0, hn0⟩ := tile_ce_mem_L.1 hl' 0
  obtain ⟨n1, hn1⟩ := tile_ce_mem_L.1 hl' 1
  simp only at hxx
  have e0 : x' 0 + l' 0 = x 0 + l 0 := by simpa using congrFun hxx 0
  have e1 : x' 1 + l' 1 = x 1 + l 1 := by simpa using congrFun hxx 1
  rw [abs_lt] at a1 a2 b1 b2
  have c1 : ((2 * (n0 - m0) + (n1 - m1) : ℤ) : ℝ) < 2 := by push_cast; linarith
  have c2 : ((2 * (n0 - m0) + (n1 - m1) : ℤ) : ℝ) > -2 := by push_cast; linarith
  have c3 : ((2 * (n1 - m1) - (n0 - m0) : ℤ) : ℝ) < 2 := by push_cast; linarith
  have c4 : ((2 * (n1 - m1) - (n0 - m0) : ℤ) : ℝ) > -2 := by push_cast; linarith
  have d1 : 2 * (n0 - m0) + (n1 - m1) < 2 := by exact_mod_cast c1
  have d2 : 2 * (n0 - m0) + (n1 - m1) > -2 := by exact_mod_cast c2
  have d3 : 2 * (n1 - m1) - (n0 - m0) < 2 := by exact_mod_cast c3
  have d4 : 2 * (n1 - m1) - (n0 - m0) > -2 := by exact_mod_cast c4
  have h0 : n0 = m0 := by omega
  have h1 : n1 = m1 := by omega
  apply hne
  ext i
  fin_cases i
  · simp only [Fin.zero_eta]; rw [← hm0, ← hn0, h0]
  · simp only [Fin.mk_one]; rw [← hm1, ← hn1, h1]

/-- A support-line argument: if `x₀ ∉ int H` and `x₀ ± t w ∈ H`, then `H` lies on one side of
the line through `x₀` in direction `w`. -/
lemma tile_ce_support {H : Set (Fin 2 → ℝ)} (hH : Convex ℝ H) (h0 : (0 : Fin 2 → ℝ) ∈ interior H)
    {x₀ w : Fin 2 → ℝ} (hx₀ : x₀ ∉ interior H) {t : ℝ} (ht : 0 < t) (h1 : x₀ + t • w ∈ H)
    (h2 : x₀ - t • w ∈ H) (hD : 0 < det2 w x₀) : ∀ y ∈ H, det2 w y ≤ det2 w x₀ := by
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hH.interior isOpen_interior hx₀
  have hfH : ∀ y ∈ H, f y ≤ f x₀ := by
    intro y hy
    have hy' : y ∈ closure (interior H) := by
      rw [hH.closure_interior_eq_closure_of_nonempty_interior ⟨0, h0⟩]
      exact subset_closure hy
    exact closure_minimal (fun a ha ↦ (hf a ha).le)
      (isClosed_le f.continuous continuous_const) hy'
  have hw : f w = 0 := by
    have e1 := hfH _ h1
    have e2 := hfH _ h2
    rw [map_add, map_smul, smul_eq_mul] at e1
    rw [map_sub, map_smul, smul_eq_mul] at e2
    nlinarith
  have hpos : 0 < f x₀ := by simpa using hf 0 h0
  intro y hy
  have hc := congrArg f (rein_cramer w x₀ y)
  rw [map_smul, map_add, map_smul, map_smul, hw, smul_eq_mul, smul_eq_mul, smul_eq_mul,
    mul_zero, zero_add] at hc
  have := hfH y hy
  nlinarith

/-- A lattice half-point `x₀ ∈ H` with `-x₀ ∈ H` is not interior when the translates of `H` by
`0` and `2 x₀ ∈ tile_ceL` have disjoint interiors. -/
lemma tile_ce_not_mem_interior {H : Set (Fin 2 → ℝ)} (hH : Convex ℝ H)
    (h0 : (0 : Fin 2 → ℝ) ∈ interior H) {x₀ : Fin 2 → ℝ} (hneg : -x₀ ∈ H)
    (_hne : x₀ ≠ 0)
    (hdisj : Disjoint (interior ((fun x ↦ x + 0) '' H))
      (interior ((fun x ↦ x + (2 : ℝ) • x₀) '' H))) : x₀ ∉ interior H := by
  intro hx
  have hc : Continuous fun t : ℝ ↦ x₀ + t • x₀ := by fun_prop
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), x₀ + t • x₀ ∈ interior H :=
    hc.continuousAt.preimage_mem_nhds (by simpa using isOpen_interior.mem_nhds hx)
  obtain ⟨t, htI, ht⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (Ioo_mem_nhdsGT (zero_lt_one' ℝ))).exists
  have hz2 : (1 - t) • (-x₀) + t • (0 : Fin 2 → ℝ) ∈ interior H :=
    hH.combo_self_interior_mem_interior hneg h0 (by linarith [ht.2]) ht.1 (by ring)
  have hA : x₀ + t • x₀ ∈ interior ((fun x ↦ x + 0) '' H) := by simpa using htI
  have hB : x₀ + t • x₀ ∈ interior ((fun x ↦ x + (2 : ℝ) • x₀) '' H) := by
    rw [tile_ce_interior_translate]
    refine ⟨_, hz2, ?_⟩
    ext i
    simp only [smul_neg, smul_zero, add_zero, Pi.add_apply, Pi.neg_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  exact Set.disjoint_left.1 hdisj hA hB

lemma tile_ce_convex_of_shape {H : Set (Fin 2 → ℝ)}
    (hHt : IsCSParallelogram H ∨ ∃ v, IsCSHexagon v ∧ H = hexagonOf v) : Convex ℝ H := by
  rcases hHt with ⟨u, v, -, rfl⟩ | ⟨v, -, rfl⟩
  · exact (rein_parallelogram_convex_compact u v).1
  · exact convex_convexHull ℝ _

/-- **Lemma 2.2.1 as printed is false.** The book's Lemma 2.2.1 (`lem:reinhardt-tiling`) states
that a lattice packing `K + L` of a centrally symmetric convex disk is realized by placing `K` in
a parallelogram or centrally symmetric hexagon `H` whose `L`-translates tile the plane. For
`L = ℤ²` and the parallelogram `K = {y | |2y₀ + y₁| ≤ 1, |2y₁ - y₀| ≤ 1}` (area `4/5`), `K + L` is
a ("pinwheel") lattice packing, but no convex `H ⊇ K` tiles with `L`: the half-lattice points
`(±1/2, 0)`, `(0, ±1/2)` lie in the relative interiors of the edges of `K`, so `H` keeps them on
its boundary with the support lines of `K` (`tile_ce_not_mem_interior`, `tile_ce_support`), hence
`H ⊆ K`, while `(1/2, 1/2)` is not covered by `K + L`. The corrected Lemma 2.2.1 (`lemma2_2_1`)
concludes that the translates of `H` pack. -/
theorem lemma2_2_1_false_as_printed :
    ¬ ∀ (K : Set (Fin 2 → ℝ)), IsCCSDisk K → ∀ (L : Submodule ℤ (Fin 2 → ℝ)), IsPlaneLattice L →
      IsLatticePacking K L →
      ∃ H, (IsCSParallelogram H ∨ ∃ v, IsCSHexagon v ∧ H = hexagonOf v) ∧ K ⊆ H ∧
        IsLatticeTiling H L := by
  intro h
  obtain ⟨H, hHt, hKH, hT⟩ := h tile_ceK tile_ce_hK tile_ceL tile_ce_hL tile_ce_hKL
  have hH := tile_ce_convex_of_shape hHt
  have h0 : (0 : Fin 2 → ℝ) ∈ interior H := interior_mono hKH tile_ce_zero_mem_interior_K
  have hmemK : ∀ x : Fin 2 → ℝ, |2 * x 0 + x 1| ≤ 1 → |2 * x 1 - x 0| ≤ 1 → x ∈ H :=
    fun x h1 h2 ↦ hKH ⟨h1, h2⟩
  -- the four lattice half-points are on the boundary of `H`
  have hnot : ∀ x₀ : Fin 2 → ℝ, x₀ ∈ tile_ceK → -x₀ ∈ tile_ceK → x₀ ≠ 0 → (2 : ℝ) • x₀ ∈ tile_ceL →
      x₀ ∉ interior H := by
    intro x₀ hx hnx hne hl
    refine tile_ce_not_mem_interior hH h0 (hKH hnx) hne (hT.2 0 (zero_mem _) _ hl ?_)
    intro he
    apply hne
    have := congrArg (fun z ↦ (1 / 2 : ℝ) • z) he
    simp only [smul_zero, smul_smul] at this
    norm_num at this
    exact this.symm
  have hL2 : ∀ a b : ℤ, (![(a : ℝ), b] : Fin 2 → ℝ) ∈ tile_ceL := by
    intro a b
    rw [tile_ce_mem_L]
    intro i; fin_cases i
    · exact ⟨a, by simp⟩
    · exact ⟨b, by simp⟩
  have hsmul : ∀ a b : ℝ, (2 : ℝ) • (![a, b] : Fin 2 → ℝ) = ![2 * a, 2 * b] := by
    intro a b; ext i; fin_cases i <;> simp
  have kmem : ∀ a b : ℝ, |2 * a + b| ≤ 1 → |2 * b - a| ≤ 1 → (![a, b] : Fin 2 → ℝ) ∈ tile_ceK :=
    fun a b h1 h2 ↦ ⟨by simpa using h1, by simpa using h2⟩
  have hne : ∀ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) → (![a, b] : Fin 2 → ℝ) ≠ 0 := by
    intro a b hab he
    rcases hab with ha | hb
    · exact ha (by simpa using congrFun he 0)
    · exact hb (by simpa using congrFun he 1)
  have hneg : ∀ a b : ℝ, -(![a, b] : Fin 2 → ℝ) = ![-a, -b] := by
    intro a b; ext i; fin_cases i <;> simp
  have n1 : (![1 / 2, 0] : Fin 2 → ℝ) ∉ interior H := by
    refine hnot _ (kmem _ _ (by norm_num [abs_le]) (by norm_num [abs_le]))
      (by rw [hneg]; exact kmem _ _ (by norm_num [abs_le]) (by norm_num [abs_le]))
      (hne _ _ (Or.inl (by norm_num))) ?_
    rw [hsmul]; simpa using hL2 1 0
  have n2 : (![-1 / 2, 0] : Fin 2 → ℝ) ∉ interior H := by
    refine hnot _ (kmem _ _ (by norm_num [abs_le]) (by norm_num [abs_le]))
      (by rw [hneg]; exact kmem _ _ (by norm_num [abs_le]) (by norm_num [abs_le]))
      (hne _ _ (Or.inl (by norm_num))) ?_
    rw [hsmul]; convert hL2 (-1) 0 using 1; ext i; fin_cases i <;> norm_num
  have n3 : (![0, 1 / 2] : Fin 2 → ℝ) ∉ interior H := by
    refine hnot _ (kmem _ _ (by norm_num [abs_le]) (by norm_num [abs_le]))
      (by rw [hneg]; exact kmem _ _ (by norm_num [abs_le]) (by norm_num [abs_le]))
      (hne _ _ (Or.inr (by norm_num))) ?_
    rw [hsmul]; simpa using hL2 0 1
  have n4 : (![0, -1 / 2] : Fin 2 → ℝ) ∉ interior H := by
    refine hnot _ (kmem _ _ (by norm_num [abs_le]) (by norm_num [abs_le]))
      (by rw [hneg]; exact kmem _ _ (by norm_num [abs_le]) (by norm_num [abs_le]))
      (hne _ _ (Or.inr (by norm_num))) ?_
    rw [hsmul]; convert hL2 0 (-1) using 1; ext i; fin_cases i <;> norm_num
  -- hence `H ⊆ tile_ceK` by the tile_ce_support lines of `tile_ceK` at these points
  have s1 := tile_ce_support hH h0 n1 (t := 1 / 10) (w := ![1, -2]) (by norm_num)
    (hmemK _ (by norm_num [abs_le]) (by norm_num [abs_le]))
    (hmemK _ (by norm_num [abs_le]) (by norm_num [abs_le]))
    (by norm_num [det2])
  have s2 := tile_ce_support hH h0 n2 (t := 1 / 10) (w := ![-1, 2]) (by norm_num)
    (hmemK _ (by norm_num [abs_le]) (by norm_num [abs_le]))
    (hmemK _ (by norm_num [abs_le]) (by norm_num [abs_le]))
    (by norm_num [det2])
  have s3 := tile_ce_support hH h0 n3 (t := 1 / 10) (w := ![2, 1]) (by norm_num)
    (hmemK _ (by norm_num [abs_le]) (by norm_num [abs_le]))
    (hmemK _ (by norm_num [abs_le]) (by norm_num [abs_le]))
    (by norm_num [det2])
  have s4 := tile_ce_support hH h0 n4 (t := 1 / 10) (w := ![-2, -1]) (by norm_num)
    (hmemK _ (by norm_num [abs_le]) (by norm_num [abs_le]))
    (hmemK _ (by norm_num [abs_le]) (by norm_num [abs_le]))
    (by norm_num [det2])
  -- but `(1/2, 1/2)` is not covered by `H + tile_ceL`
  have hcov : (![1 / 2, 1 / 2] : Fin 2 → ℝ) ∈ ⋃ l ∈ tile_ceL, (fun x ↦ x + l) '' H :=
    hT.1 ▸ mem_univ _
  simp only [mem_iUnion, mem_image] at hcov
  obtain ⟨l, hl, y, hy, hyl⟩ := hcov
  obtain ⟨m, hm⟩ := tile_ce_mem_L.1 hl 0
  obtain ⟨n, hn⟩ := tile_ce_mem_L.1 hl 1
  have e0 : y 0 + l 0 = 1 / 2 := by simpa using congrFun hyl 0
  have e1 : y 1 + l 1 = 1 / 2 := by simpa using congrFun hyl 1
  have t1 := s1 y hy
  have t2 := s2 y hy
  have t3 := s3 y hy
  have t4 := s4 y hy
  simp only [det2, Matrix.cons_val_zero, Matrix.cons_val_one] at t1 t2 t3 t4
  norm_num at t1 t2 t3 t4
  have c1 : ((3 - 4 * m - 2 * n : ℤ) : ℝ) ≤ 2 := by push_cast; linarith
  have c2 : ((3 - 4 * m - 2 * n : ℤ) : ℝ) ≥ -2 := by push_cast; linarith
  have c3 : ((1 - 4 * n + 2 * m : ℤ) : ℝ) ≤ 2 := by push_cast; linarith
  have c4 : ((1 - 4 * n + 2 * m : ℤ) : ℝ) ≥ -2 := by push_cast; linarith
  have d1 : 3 - 4 * m - 2 * n ≤ 2 := by exact_mod_cast c1
  have d2 : 3 - 4 * m - 2 * n ≥ -2 := by exact_mod_cast c2
  have d3 : 1 - 4 * n + 2 * m ≤ 2 := by exact_mod_cast c3
  have d4 : 1 - 4 * n + 2 * m ≥ -2 := by exact_mod_cast c4
  omega

end SmoothedPolygons
