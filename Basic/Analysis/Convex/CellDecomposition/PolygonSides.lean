module

public import Basic.Analysis.Convex.CellDecomposition.Defs

/-!
# (C1) Sides of a convex polygon

Part of the proof of the cell lemma (`Basic.Analysis.Convex.CellDecomposition`).

The proof follows the first argument of the docstring of
`PlaneConvex.IsConvexPolygon.exists_halfPlanesInter_ncard`: discard redundant half-planes (keep a
family `T` of minimal size cutting out `P`); each remaining half-plane meets `P` in a side of
positive length, whose counterclockwise endpoint is a corner of `P`; distinct sides have distinct
counterclockwise endpoints, so there are at most as many sides as corners. The corners are finitely
many because a corner is determined by the set of constraints active at it. Repeating a half-plane
then gives exactly `N` half-planes.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace PlaneConvex

/-! ### Planar helpers -/

/-- The points satisfying the constraints `⟨a j, x⟩ ≤ c j` for `j ∈ T`. -/
private def cut {k : ℕ} (a : Fin k → Fin 2 → ℝ) (c : Fin k → ℝ) (T : Finset (Fin k)) :
    Set (Fin 2 → ℝ) :=
  {x | ∀ j ∈ T, a j ⬝ᵥ x ≤ c j}

/-- Rotation of a vector of the plane by a quarter turn. -/
private def perp (x : Fin 2 → ℝ) : Fin 2 → ℝ := ![-x 1, x 0]

private lemma dot_two (x y : Fin 2 → ℝ) : x ⬝ᵥ y = x 0 * y 0 + x 1 * y 1 := by
  simp [dotProduct, Fin.sum_univ_two]

private lemma perp_dot (x y : Fin 2 → ℝ) : perp x ⬝ᵥ y = -x 1 * y 0 + x 0 * y 1 := by
  simp [perp, dotProduct, Fin.sum_univ_two]

private lemma normSq_pos {x : Fin 2 → ℝ} (hx : x ≠ 0) : 0 < x 0 * x 0 + x 1 * x 1 := by
  by_contra h
  apply hx
  have h0 : x 0 = 0 := by nlinarith [mul_self_nonneg (x 0), mul_self_nonneg (x 1)]
  have h1 : x 1 = 0 := by nlinarith [mul_self_nonneg (x 0), mul_self_nonneg (x 1)]
  ext i; fin_cases i <;> simp [h0, h1]

private lemma dot_perp_self (x : Fin 2 → ℝ) : x ⬝ᵥ perp x = 0 := by
  rw [dotProduct_comm, perp_dot]; ring

private lemma perp_dot_perp (x : Fin 2 → ℝ) : perp x ⬝ᵥ perp x = x 0 * x 0 + x 1 * x 1 := by
  rw [perp_dot]; simp [perp]; ring

private lemma perp_dot_comm (x y : Fin 2 → ℝ) : perp x ⬝ᵥ y = -(perp y ⬝ᵥ x) := by
  rw [perp_dot, perp_dot]; ring

private lemma perp_ne_zero {x : Fin 2 → ℝ} (hx : x ≠ 0) : perp x ≠ 0 := by
  intro h
  have := perp_dot_perp x
  rw [h, zero_dotProduct] at this
  exact (normSq_pos hx).ne this

/-- In the plane, a vector orthogonal to `a ≠ 0` and to `perp a` is zero. -/
private lemma eq_zero_of_dot_eq_zero {a z : Fin 2 → ℝ} (ha : a ≠ 0) (h1 : a ⬝ᵥ z = 0)
    (h2 : perp a ⬝ᵥ z = 0) : z = 0 := by
  rw [dot_two] at h1
  rw [perp_dot] at h2
  have hp := normSq_pos ha
  have e0 : (a 0 * a 0 + a 1 * a 1) * z 0 = 0 := by linear_combination a 0 * h1 - a 1 * h2
  have e1 : (a 0 * a 0 + a 1 * a 1) * z 1 = 0 := by linear_combination a 1 * h1 + a 0 * h2
  ext i; fin_cases i
  · simpa [hp.ne'] using e0
  · simpa [hp.ne'] using e1

/-- If `b` is parallel to `a ≠ 0` (`⟨perp a, b⟩ = 0`), then `b ⟂ z` whenever `a ⟂ z`. -/
private lemma dot_eq_zero_of_parallel {a b z : Fin 2 → ℝ} (ha : a ≠ 0)
    (hab : perp a ⬝ᵥ b = 0) (hz : a ⬝ᵥ z = 0) : b ⬝ᵥ z = 0 := by
  rw [dot_two] at hz ⊢
  rw [perp_dot] at hab
  have e0 : a 0 * (b 0 * z 0 + b 1 * z 1) = 0 := by linear_combination b 0 * hz + z 1 * hab
  have e1 : a 1 * (b 0 * z 0 + b 1 * z 1) = 0 := by linear_combination b 1 * hz - z 0 * hab
  by_contra h
  apply ha
  ext i; fin_cases i
  · simpa [h] using e0
  · simpa [h] using e1

/-- For any two vectors `A, B` of the plane there is a direction `d ≠ 0` with `⟨A, d⟩ ≤ 0` and
`⟨B, d⟩ ≤ 0`. -/
private lemma exists_dir (A B : Fin 2 → ℝ) :
    ∃ d : Fin 2 → ℝ, d ≠ 0 ∧ A ⬝ᵥ d ≤ 0 ∧ B ⬝ᵥ d ≤ 0 := by
  by_cases hdet : A 0 * B 1 - A 1 * B 0 = 0
  · by_cases hA : A = 0
    · by_cases hB : B = 0
      · exact ⟨![1, 0], fun h ↦ by simpa using congrFun h 0, by simp [hA], by simp [hB]⟩
      · exact ⟨perp B, perp_ne_zero hB, by simp [hA], (dot_perp_self B).le⟩
    · refine ⟨perp A, perp_ne_zero hA, (dot_perp_self A).le, ?_⟩
      rw [dotProduct_comm, perp_dot]; linarith
  · set D := A 0 * B 1 - A 1 * B 0
    have hA : A ⬝ᵥ ![(A 1 - B 1) / D, (B 0 - A 0) / D] = -1 := by
      rw [dot_two]; simp; field_simp; ring
    have hB : B ⬝ᵥ ![(A 1 - B 1) / D, (B 0 - A 0) / D] = -1 := by
      rw [dot_two]; simp; field_simp; ring
    refine ⟨_, fun h ↦ ?_, by rw [hA]; norm_num, by rw [hB]; norm_num⟩
    rw [h, dotProduct_zero] at hA
    norm_num at hA

/-- If `α u + β v = m` is a proper convex combination and `u, v ≤ m`, then `u = v = m`. -/
private lemma combo_eq {α β u v m : ℝ} (hα : 0 < α) (hβ : 0 < β) (hαβ : α + β = 1)
    (hu : u ≤ m) (hv : v ≤ m) (h : α * u + β * v = m) : u = m ∧ v = m := by
  have hβ' : β = 1 - α := by linarith
  subst hβ'
  constructor <;> nlinarith

private lemma eq_zero_of_mem_extremePoints {A : Set (Fin 2 → ℝ)} {x e : Fin 2 → ℝ}
    (hx : x ∈ extremePoints ℝ A) (h1 : x + e ∈ A) (h2 : x - e ∈ A) : e = 0 := by
  have hseg : x ∈ openSegment ℝ (x + e) (x - e) :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by ext i; simp; ring⟩
  have := ((mem_extremePoints.1 hx).2 _ h1 _ h2 hseg).1
  simpa using this

private lemma isClosed_cut {k : ℕ} (a : Fin k → Fin 2 → ℝ) (c : Fin k → ℝ)
    (T : Finset (Fin k)) : IsClosed (cut a c T) := by
  have : cut a c T = halfPlanesInter (fun j : T ↦ a j) (fun j : T ↦ c j) := by
    ext x; simp [cut, halfPlanesInter]
  rw [this]; exact isClosed_halfPlanesInter _ _

/-- Moving from `x` in a direction `d` that keeps the active constraints at `x` active stays in
the polygon for small times (of either sign). -/
private lemma eventually_mem_cut {k : ℕ} {a : Fin k → Fin 2 → ℝ} {c : Fin k → ℝ}
    {T : Finset (Fin k)} {x d : Fin 2 → ℝ} (hx : x ∈ cut a c T)
    (hd : ∀ j ∈ T, a j ⬝ᵥ x = c j → a j ⬝ᵥ d = 0) :
    ∀ᶠ t in 𝓝 (0 : ℝ), x + t • d ∈ cut a c T := by
  simp only [cut, mem_ofPred_eq]
  rw [eventually_all_finset]
  intro j hj
  rcases (hx j hj).eq_or_lt with h | h
  · exact Eventually.of_forall fun t ↦ by
      rw [dotProduct_add, dotProduct_smul, h, hd j hj h, smul_zero, add_zero]
  · have hc : Continuous fun t : ℝ ↦ a j ⬝ᵥ (x + t • d) := by fun_prop
    have := hc.tendsto 0
    simp only [zero_smul, add_zero] at this
    exact (this.eventually (gt_mem_nhds h)).mono fun t ht ↦ ht.le

/-- At an interior point, every constraint with nonzero normal is strict. -/
private lemma dot_lt_of_mem_interior {S : Set (Fin 2 → ℝ)} {p u : Fin 2 → ℝ} {r : ℝ}
    (hp : p ∈ interior S) (hS : ∀ x ∈ S, u ⬝ᵥ x ≤ r) (hu : u ≠ 0) : u ⬝ᵥ p < r := by
  have hc : Continuous fun t : ℝ ↦ p + t • u := by fun_prop
  have h1 : Tendsto (fun t : ℝ ↦ p + t • u) (𝓝[>] 0) (𝓝 p) := by
    have := hc.tendsto 0
    simp only [zero_smul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨t, ht, ht0⟩ :=
    ((h1.eventually_mem (mem_interior_iff_mem_nhds.mp hp)).and eventually_mem_nhdsWithin).exists
  have h := hS _ ht
  rw [dotProduct_add, dotProduct_smul, smul_eq_mul] at h
  have hpos : 0 < u ⬝ᵥ u := by rw [dot_two]; exact normSq_pos hu
  have ht0' : (0 : ℝ) < t := ht0
  nlinarith

/-- The core of (C1): for a family `T` of constraints none of which is redundant, cutting out a
bounded set with nonempty interior, the corners are finitely many, at least as many as the
constraints, and there are at least three constraints. -/
private lemma card_le_ncard_extremePoints {k : ℕ} (a : Fin k → Fin 2 → ℝ) (c : Fin k → ℝ)
    (T : Finset (Fin k))
    (hmin : ∀ i ∈ T, ∃ z, (∀ j ∈ T, j ≠ i → a j ⬝ᵥ z ≤ c j) ∧ c i < a i ⬝ᵥ z)
    (hbdd : Bornology.IsBounded (cut a c T)) {p : Fin 2 → ℝ} (hp : p ∈ interior (cut a c T)) :
    (extremePoints ℝ (cut a c T)).Finite ∧ T.card ≤ (extremePoints ℝ (cut a c T)).ncard ∧
      3 ≤ T.card := by
  classical
  set P := cut a c T with hPdef
  have hpP : p ∈ P := interior_subset hp
  have hPc : IsCompact P := Metric.isCompact_of_isClosed_isBounded (isClosed_cut a c T) hbdd
  -- the normals are nonzero
  have ha : ∀ i ∈ T, a i ≠ 0 := by
    intro i hi h
    obtain ⟨z, -, hz⟩ := hmin i hi
    have := hpP i hi
    simp only [h, zero_dotProduct] at this hz
    linarith
  -- the interior point satisfies every constraint strictly
  have hps : ∀ j ∈ T, a j ⬝ᵥ p < c j := fun j hj ↦
    dot_lt_of_mem_interior hp (fun x hx ↦ hx j hj) (ha j hj)
  -- each line `⟨a i, x⟩ = c i` has a point satisfying the other constraints strictly
  have hw : ∀ i ∈ T, ∃ w, a i ⬝ᵥ w = c i ∧ ∀ j ∈ T, j ≠ i → a j ⬝ᵥ w < c j := by
    intro i hi
    obtain ⟨z, hz, hzi⟩ := hmin i hi
    have hpi := hps i hi
    have hden : 0 < a i ⬝ᵥ z - a i ⬝ᵥ p := by linarith
    set t := (c i - a i ⬝ᵥ p) / (a i ⬝ᵥ z - a i ⬝ᵥ p) with ht
    have ht0 : 0 < t := div_pos (by linarith) hden
    have ht1 : t < 1 := (div_lt_one hden).2 (by linarith)
    refine ⟨p + t • (z - p), ?_, fun j hj hji ↦ ?_⟩
    · rw [dotProduct_add, dotProduct_smul, dotProduct_sub, smul_eq_mul, ht,
        div_mul_cancel₀ _ hden.ne']
      ring
    · rw [dotProduct_add, dotProduct_smul, dotProduct_sub, smul_eq_mul]
      have h1 := hps j hj
      have h2 := hz j hj hji
      nlinarith [mul_pos (sub_pos.2 ht1) (sub_pos.2 h1), mul_nonneg ht0.le (sub_nonneg.2 h2)]
  -- the counterclockwise endpoint `v i` of the side on the line `⟨a i, x⟩ = c i`
  have hv : ∀ i, ∃ v : Fin 2 → ℝ, i ∈ T → v ∈ extremePoints ℝ P ∧ a i ⬝ᵥ v = c i ∧
      ∃ t : ℝ, 0 < t ∧ v - t • perp (a i) ∈ P := by
    intro i
    by_cases hi : i ∈ T
    swap
    · exact ⟨0, fun h ↦ (hi h).elim⟩
    obtain ⟨w, hwi, hwj⟩ := hw i hi
    have hwP : w ∈ P := fun j hj ↦ by
      by_cases hji : j = i
      · subst hji; exact hwi.le
      · exact (hwj j hj hji).le
    have hFc : IsCompact (P ∩ {x | a i ⬝ᵥ x = c i}) :=
      hPc.inter_right (isClosed_eq (by fun_prop) continuous_const)
    obtain ⟨v, ⟨hvP, hvi⟩, hvmax⟩ := hFc.exists_isMaxOn (f := fun x ↦ perp (a i) ⬝ᵥ x)
      ⟨w, hwP, hwi⟩ (by fun_prop : Continuous fun x ↦ perp (a i) ⬝ᵥ x).continuousOn
    rw [isMaxOn_iff] at hvmax
    refine ⟨v, fun _ ↦ ⟨?_, hvi, ?_⟩⟩
    · -- `v` is a corner: it is the only maximizer of `perp (a i)` on the side
      refine mem_extremePoints.2 ⟨hvP, fun x hx y hy hseg ↦ ?_⟩
      obtain ⟨α, β, hα, hβ, hαβ, hxy⟩ := hseg
      have e1 : α * (a i ⬝ᵥ x) + β * (a i ⬝ᵥ y) = c i := by
        rw [← hvi, ← hxy, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul,
          smul_eq_mul]
      obtain ⟨hxi, hyi⟩ := combo_eq hα hβ hαβ (hx i hi) (hy i hi) e1
      have e2 : α * (perp (a i) ⬝ᵥ x) + β * (perp (a i) ⬝ᵥ y) = perp (a i) ⬝ᵥ v := by
        rw [← hxy, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      obtain ⟨hx', hy'⟩ := combo_eq hα hβ hαβ (hvmax x ⟨hx, hxi⟩) (hvmax y ⟨hy, hyi⟩) e2
      have key : ∀ z, a i ⬝ᵥ z = c i → perp (a i) ⬝ᵥ z = perp (a i) ⬝ᵥ v → z = v := by
        intro z h1 h2
        exact sub_eq_zero.1 (eq_zero_of_dot_eq_zero (ha i hi)
          (by rw [dotProduct_sub, h1, hvi, sub_self]) (by rw [dotProduct_sub, h2, sub_self]))
      exact ⟨key x hxi hx', key y hyi hy'⟩
    · -- the side has positive length: it contains a point `u` before `v`
      have hev := eventually_mem_cut (x := w) (d := perp (a i)) hwP (fun j hj hjw ↦ by
        by_cases hji : j = i
        · subst hji; exact dot_perp_self _
        · exact absurd hjw (hwj j hj hji).ne)
      obtain ⟨s, hs, hs0⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
        (eventually_mem_nhdsWithin (s := Iio (0 : ℝ)) (a := 0))).exists
      have hs0' : s < 0 := hs0
      have hui : a i ⬝ᵥ (w + s • perp (a i)) = c i := by
        rw [dotProduct_add, dotProduct_smul, dot_perp_self, smul_zero, add_zero, hwi]
      have hpp' : 0 < perp (a i) ⬝ᵥ perp (a i) := by
        rw [perp_dot_perp]; exact normSq_pos (ha i hi)
      have hwle := hvmax w ⟨hwP, hwi⟩
      have hlt : perp (a i) ⬝ᵥ (w + s • perp (a i)) < perp (a i) ⬝ᵥ v := by
        rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
        nlinarith [mul_neg_of_neg_of_pos hs0' hpp']
      refine ⟨(perp (a i) ⬝ᵥ v - perp (a i) ⬝ᵥ (w + s • perp (a i))) /
        (perp (a i) ⬝ᵥ perp (a i)), div_pos (by linarith) hpp', ?_⟩
      have : v - ((perp (a i) ⬝ᵥ v - perp (a i) ⬝ᵥ (w + s • perp (a i))) /
          (perp (a i) ⬝ᵥ perp (a i))) • perp (a i) = w + s • perp (a i) := by
        rw [← sub_eq_zero]
        apply eq_zero_of_dot_eq_zero (ha i hi)
        · rw [dotProduct_sub, dotProduct_sub, dotProduct_smul, dot_perp_self, hvi, hui]
          simp
        · rw [dotProduct_sub, dotProduct_sub, dotProduct_smul, smul_eq_mul,
            div_mul_cancel₀ _ hpp'.ne']
          ring
      rw [this]; exact hs
  choose v hv using hv
  -- distinct sides have distinct counterclockwise endpoints
  have hinj : InjOn v T := by
    intro i hi j hj hij
    by_contra hne
    obtain ⟨-, hvi, ti, hti, hPi⟩ := hv i hi
    obtain ⟨-, hvj, tj, htj, hPj⟩ := hv j hj
    have h1 : 0 ≤ a j ⬝ᵥ perp (a i) := by
      have := hPi j hj
      rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, hij, hvj] at this
      nlinarith
    have h2 : 0 ≤ a i ⬝ᵥ perp (a j) := by
      have := hPj i hi
      rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, ← hij, hvi] at this
      nlinarith
    have hpar : perp (a i) ⬝ᵥ a j = 0 := by
      rw [dotProduct_comm] at h1 h2
      rw [perp_dot_comm (a j)] at h2
      linarith
    obtain ⟨w, hwi, hwj⟩ := hw i hi
    have := dot_eq_zero_of_parallel (z := w - v i) (ha i hi) hpar
      (by rw [dotProduct_sub, hwi, hvi, sub_self])
    rw [dotProduct_sub, hij, hvj, sub_eq_zero] at this
    exact (hwj j hj fun h ↦ hne h.symm).ne this
  -- the corners are finitely many: a corner is determined by its active constraints
  have hfin : (extremePoints ℝ P).Finite := by
    refine Finite.of_finite_image (f := fun x ↦ T.filter fun j ↦ a j ⬝ᵥ x = c j)
      (Set.toFinite _) ?_
    intro x hx y hy hxy
    have hd : ∀ j ∈ T, a j ⬝ᵥ x = c j → a j ⬝ᵥ (y - x) = 0 := by
      intro j hj hjx
      have hxy' : (T.filter fun j ↦ a j ⬝ᵥ x = c j) = T.filter fun j ↦ a j ⬝ᵥ y = c j := hxy
      have : j ∈ T.filter fun j ↦ a j ⬝ᵥ y = c j := by
        rw [← hxy']; exact Finset.mem_filter.2 ⟨hj, hjx⟩
      rw [Finset.mem_filter] at this
      rw [dotProduct_sub, this.2, hjx, sub_self]
    have hev := eventually_mem_cut (extremePoints_subset hx) hd
    have hev' : ∀ᶠ t in 𝓝 (0 : ℝ), x + (-t) • (y - x) ∈ P :=
      (continuous_neg.tendsto' (0 : ℝ) 0 neg_zero).eventually hev
    obtain ⟨t, ⟨h1, h2⟩, ht⟩ := (((hev.and hev').filter_mono nhdsWithin_le_nhds).and
      (eventually_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0))).exists
    have := eq_zero_of_mem_extremePoints hx h1 (by simpa [neg_smul, ← sub_eq_add_neg] using h2)
    rcases smul_eq_zero.1 this with h | h
    · exact absurd h (ne_of_gt ht)
    · exact (sub_eq_zero.1 h).symm
  -- at least three constraints: two half-planes cut out an unbounded set
  have h3 : 3 ≤ T.card := by
    by_contra hlt
    push Not at hlt
    obtain ⟨d, hd0, hd⟩ : ∃ d : Fin 2 → ℝ, d ≠ 0 ∧ ∀ j ∈ T, a j ⬝ᵥ d ≤ 0 := by
      rcases (by omega : T.card = 0 ∨ T.card = 1 ∨ T.card = 2) with h | h | h
      · obtain ⟨d, hd0, -, -⟩ := exists_dir 0 0
        exact ⟨d, hd0, fun j hj ↦ by simp [Finset.card_eq_zero.1 h] at hj⟩
      · obtain ⟨i, hi⟩ := Finset.card_eq_one.1 h
        obtain ⟨d, hd0, h1, -⟩ := exists_dir (a i) (a i)
        refine ⟨d, hd0, fun j hj ↦ ?_⟩
        rw [hi, Finset.mem_singleton] at hj
        subst hj; exact h1
      · obtain ⟨i, i', -, hii⟩ := Finset.card_eq_two.1 h
        obtain ⟨d, hd0, h1, h2⟩ := exists_dir (a i) (a i')
        refine ⟨d, hd0, fun j hj ↦ ?_⟩
        rw [hii, Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl
        exacts [h1, h2]
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hbdd
    have hray : ∀ s : ℝ, 0 ≤ s → p + s • d ∈ P := fun s hs j hj ↦ by
      have := hpP j hj
      have := hd j hj
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
      nlinarith
    have hdpos : 0 < ‖d‖ := norm_pos_iff.2 hd0
    have hCp : ‖p‖ ≤ C := hC p hpP
    have hs : 0 ≤ (C + ‖p‖ + 1) / ‖d‖ := div_nonneg (by linarith [norm_nonneg p]) hdpos.le
    have h1 := hC _ (hray _ hs)
    have h2 : ‖((C + ‖p‖ + 1) / ‖d‖) • d‖ ≤ ‖p + ((C + ‖p‖ + 1) / ‖d‖) • d‖ + ‖p‖ := by
      calc ‖((C + ‖p‖ + 1) / ‖d‖) • d‖ = ‖(p + ((C + ‖p‖ + 1) / ‖d‖) • d) - p‖ := by
            rw [add_sub_cancel_left]
        _ ≤ ‖p + ((C + ‖p‖ + 1) / ‖d‖) • d‖ + ‖p‖ := norm_sub_le _ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs, div_mul_cancel₀ _ hdpos.ne'] at h2
    linarith
  refine ⟨hfin, ?_, h3⟩
  rw [← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard_of_injOn v (fun i hi ↦ (hv i hi).1) hinj hfin

/-! ### (C1) Sides of a convex polygon -/

/-- **(C1) A convex polygon with `N` corners is cut out by `N ≥ 3` half-planes.** If `P` is a
convex polygon (`IsConvexPolygon`), its set of extreme points is finite with `N ≥ 3` elements,
and `P = halfPlanesInter a c` for some `a : Fin N → Fin 2 → ℝ`, `c : Fin N → ℝ`.

Argument. Write `P = halfPlanesInter a₀ c₀` with `k` half-planes. Discard the redundant ones and
merge parallel ones with the same normal direction (keep the smaller offset); call the remaining
normals, sorted by angle, `u₁, …, u_N'`. Each remaining half-plane meets `P` in a side (a segment
of positive length, else it would be redundant), consecutive sides meet in a corner, and the
corners are exactly the extreme points of `P` (`Set.extremePoints`): a point of `P` on a single
side, or in the interior, is the midpoint of two other points of `P`; the common endpoint of two
consecutive sides with non-parallel normals is not. So `N = N'`; `N ≥ 3` because `P` is bounded
with nonempty interior (two half-planes cut out an unbounded set or one with empty interior).
Alternatively: `P` is compact, so it is the convex hull of its extreme points (Krein–Milman);
these are finitely many (each is the intersection point of two of the `k` lines), and the `N`
edges of `conv{p₁, …, p_N}`, with the points in angular order about an interior point, give the
`N` half-planes.

Formalized argument (the first one, without sorting by angle): keep a family `T` of the given
half-planes of minimal size cutting out `P` (so none is redundant, which also merges parallel
ones). Each line of `T` meets `P` in a side of positive length; its counterclockwise endpoint
(the maximizer of `⟨perp aᵢ, x⟩` on the side) is a corner of `P`, and two different sides have
different counterclockwise endpoints (else their normals would be parallel and one of the two
constraints redundant). So `N' = |T| ≤ N`; the corners are finitely many since a corner is
determined by the set of constraints active at it; `N' ≥ 3` since `P` is bounded with nonempty
interior. Repeating one of the `N'` half-planes `N - N'` times gives exactly `N` half-planes
(in fact `N' = N`, which is not needed). -/
theorem IsConvexPolygon.exists_halfPlanesInter_ncard {P : Set (Fin 2 → ℝ)}
    (hP : IsConvexPolygon P) :
    ∃ (a : Fin (extremePoints ℝ P).ncard → Fin 2 → ℝ) (c : Fin (extremePoints ℝ P).ncard → ℝ),
      P = halfPlanesInter a c ∧ 3 ≤ (extremePoints ℝ P).ncard := by
  classical
  obtain ⟨⟨k, a, c, rfl⟩, hbdd, p, hp⟩ := hP
  have huniv : cut a c Finset.univ = halfPlanesInter a c := by
    ext x; simp [cut, halfPlanesInter]
  obtain ⟨T, hT, hTmin⟩ := (Finset.univ.filter fun T : Finset (Fin k) ↦
    cut a c T = halfPlanesInter a c).exists_min_image Finset.card
    ⟨Finset.univ, by simp [huniv]⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT hTmin
  rw [← hT] at hbdd hp ⊢
  -- no constraint of `T` is redundant
  have hmin : ∀ i ∈ T, ∃ z, (∀ j ∈ T, j ≠ i → a j ⬝ᵥ z ≤ c j) ∧ c i < a i ⬝ᵥ z := by
    intro i hi
    have hne : cut a c T ≠ cut a c (T.erase i) := by
      intro h
      have := hTmin (T.erase i) (h.symm.trans hT)
      exact absurd this (not_le.2 (Finset.card_erase_lt_of_mem hi))
    have hsub : cut a c T ⊆ cut a c (T.erase i) := fun x hx j hj ↦
      hx j (Finset.mem_of_mem_erase hj)
    obtain ⟨z, hz, hzT⟩ := exists_of_ssubset (Set.ssubset_iff_subset_ne.2 ⟨hsub, hne⟩)
    refine ⟨z, fun j hj hji ↦ hz j (Finset.mem_erase.2 ⟨hji, hj⟩), ?_⟩
    by_contra hle
    push Not at hle
    refine hzT fun j hj ↦ ?_
    by_cases hji : j = i
    · subst hji; exact hle
    · exact hz j (Finset.mem_erase.2 ⟨hji, hj⟩)
  obtain ⟨hfin, hle, h3⟩ := card_le_ncard_extremePoints a c T hmin hbdd hp
  set N := (extremePoints ℝ (cut a c T)).ncard
  -- a map `Fin N → T` onto `T`
  obtain ⟨j₀, hj₀⟩ : T.Nonempty := Finset.card_pos.1 (by omega)
  let f : Fin N → Fin k := fun m ↦
    if h : (m : ℕ) < T.card then (T.equivFin.symm ⟨m, h⟩ : Fin k) else j₀
  have hfT : ∀ m, f m ∈ T := fun m ↦ by
    simp only [f]
    split_ifs
    · exact (T.equivFin.symm _).2
    · exact hj₀
  have hfsurj : ∀ j ∈ T, ∃ m, f m = j := fun j hj ↦ by
    refine ⟨⟨T.equivFin ⟨j, hj⟩, lt_of_lt_of_le (T.equivFin ⟨j, hj⟩).2 hle⟩, ?_⟩
    simp [f]
  refine ⟨fun m ↦ a (f m), fun m ↦ c (f m), ?_, by omega⟩
  ext x
  simp only [cut, halfPlanesInter, mem_ofPred_eq]
  constructor
  · intro hx m
    exact hx _ (hfT m)
  · intro hx j hj
    obtain ⟨m, rfl⟩ := hfsurj j hj
    exact hx m

end PlaneConvex
