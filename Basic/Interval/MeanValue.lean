module

public import Basic.Interval.Lipschitz

/-!
# Mean value forms on boxes

Bounds on the variation of a function on a box `Icc lo hi` of `Fin n → ℝ` from enclosures of its
partial derivatives: the centred mean value form `f(X) ⊆ f(c) + Df(X) (X - c)` of interval
analysis, also through an implicit root.

* `abs_sub_le_sum_of_update`: bounds `|φ (update w j s) - φ w| ≤ L j |s - w j|` along the
  coordinate directions inside the box add up along the axis-parallel path from `u` to `v`:
  `|φ v - φ u| ≤ Σ_j L j |v j - u j|`;
* `abs_sub_le_sum_of_hasDerivAt`: the same when every partial derivative `∂_j f` on the box lies
  in a set `P j` with `|d| ≤ L j` on `P j` (the mean value theorem on each segment of the path);
  with `u = c` the center of the box, this is the centred form;
* `abs_sub_le_sum_of_implicit`: the same for `u ↦ G u (τ u)`, where `τ u ∈ [tl, th]` is a root of
  `F u`, from enclosures `P j, Pt, Q j, Qt` of the partial derivatives of `F` and `G` on the box
  times `[tl, th]` with `|q - e α / β| ≤ L j` for `q ∈ Q j`, `e ∈ Qt`, `α ∈ P j`, `β ∈ Pt` (the
  vector form of `abs_sub_le_of_implicit`; no differentiability, not even continuity, of `τ` is
  needed).
-/

@[expose] public section

open Set Function

namespace DyadicInterval

variable {n : ℕ}

theorem update_mem_Icc {lo hi w : Fin n → ℝ} (hw : w ∈ Icc lo hi) (j : Fin n) {s : ℝ}
    (hs : s ∈ Icc (lo j) (hi j)) : update w j s ∈ Icc lo hi := by
  constructor <;> intro i <;> by_cases h : i = j
  · subst h; simpa using hs.1
  · simpa [update_of_ne h] using hw.1 i
  · subst h; simpa using hs.2
  · simpa [update_of_ne h] using hw.2 i

/-- The point of the axis-parallel path from `u` to `v` after `k` steps: `v` in the coordinates
`< k`, `u` in the others. -/
def pathPt (u v : Fin n → ℝ) (k : ℕ) : Fin n → ℝ := fun j ↦ if (j : ℕ) < k then v j else u j

theorem pathPt_mem {lo hi u v : Fin n → ℝ} (hu : u ∈ Icc lo hi) (hv : v ∈ Icc lo hi) (k : ℕ) :
    pathPt u v k ∈ Icc lo hi := by
  constructor <;> intro j <;> simp only [pathPt] <;> split_ifs
  exacts [hv.1 j, hu.1 j, hv.2 j, hu.2 j]

theorem pathPt_zero (u v : Fin n → ℝ) : pathPt u v 0 = u := by
  funext j; simp [pathPt]

theorem pathPt_self (u v : Fin n → ℝ) : pathPt u v n = v := by
  funext j; simp [pathPt, j.2]

theorem pathPt_succ (u v : Fin n → ℝ) {k : ℕ} (hk : k < n) :
    pathPt u v (k + 1) = update (pathPt u v k) ⟨k, hk⟩ (v ⟨k, hk⟩) := by
  funext j
  by_cases hj : j = ⟨k, hk⟩
  · subst hj; simp [pathPt]
  · have : (j : ℕ) ≠ k := fun h ↦ hj (Fin.ext h)
    simp only [pathPt, update_of_ne hj]
    split_ifs with h1 h2 h2 <;> first | rfl | omega

theorem pathPt_apply_self (u v : Fin n → ℝ) {k : ℕ} (hk : k < n) :
    pathPt u v k ⟨k, hk⟩ = u ⟨k, hk⟩ := by
  simp [pathPt]

/-- **Bounds along the coordinate directions add up along the axis-parallel path.** -/
theorem abs_sub_le_sum_of_update {φ : (Fin n → ℝ) → ℝ} {lo hi L : Fin n → ℝ}
    (h : ∀ w ∈ Icc lo hi, ∀ j, ∀ s ∈ Icc (lo j) (hi j),
      |φ (update w j s) - φ w| ≤ L j * |s - w j|) :
    ∀ u ∈ Icc lo hi, ∀ v ∈ Icc lo hi, |φ v - φ u| ≤ ∑ j, L j * |v j - u j| := by
  intro u hu v hv
  set g : Fin n → ℝ := fun j ↦ L j * |v j - u j| with hg
  have key : ∀ k ≤ n, |φ (pathPt u v k) - φ u| ≤ ∑ j : Fin n, if (j : ℕ) < k then g j else 0 := by
    intro k
    induction k with
    | zero => intro _; simp [pathPt_zero]
    | succ k ih =>
      intro hk
      have hk' : k < n := hk
      have h1 := ih hk'.le
      have h2 := h _ (pathPt_mem hu hv k) ⟨k, hk'⟩ (v ⟨k, hk'⟩) ⟨hv.1 _, hv.2 _⟩
      rw [← pathPt_succ u v hk', pathPt_apply_self u v hk'] at h2
      have hsum : (∑ j : Fin n, if (j : ℕ) < k + 1 then g j else 0) =
          (∑ j : Fin n, if (j : ℕ) < k then g j else 0) + g ⟨k, hk'⟩ := by
        have e : ∀ j : Fin n, (if (j : ℕ) < k + 1 then g j else 0) =
            (if (j : ℕ) < k then g j else 0) + (if j = ⟨k, hk'⟩ then g j else 0) := by
          intro j
          by_cases hj : j = ⟨k, hk'⟩
          · subst hj; simp
          · have : (j : ℕ) ≠ k := fun h ↦ hj (Fin.ext h)
            simp only [hj, ite_false, add_zero]
            split_ifs with h1 h2 h2 <;> first | rfl | omega
        rw [Finset.sum_congr rfl fun j _ ↦ e j, Finset.sum_add_distrib, Finset.sum_ite_eq']
        simp
      rw [hsum]
      calc |φ (pathPt u v (k + 1)) - φ u|
          ≤ |φ (pathPt u v (k + 1)) - φ (pathPt u v k)| + |φ (pathPt u v k) - φ u| :=
            abs_sub_le _ _ _
        _ ≤ g ⟨k, hk'⟩ + ∑ j : Fin n, if (j : ℕ) < k then g j else 0 := add_le_add h2 h1
        _ = _ := add_comm _ _
  have := key n le_rfl
  rw [pathPt_self] at this
  simpa using this

/-- **The centred mean value form**: if every partial derivative `∂_j f` on the box lies in
`P j`, with `|d| ≤ L j` on `P j`, then `|f v - f u| ≤ Σ_j L j |v j - u j|` on the box. -/
theorem abs_sub_le_sum_of_hasDerivAt {f : (Fin n → ℝ) → ℝ} {lo hi L : Fin n → ℝ}
    {P : Fin n → Set ℝ}
    (hf : ∀ w ∈ Icc lo hi, ∀ j, ∃ d, HasDerivAt (fun s ↦ f (update w j s)) d (w j) ∧ d ∈ P j)
    (hP : ∀ j, ∀ d ∈ P j, |d| ≤ L j) :
    ∀ u ∈ Icc lo hi, ∀ v ∈ Icc lo hi, |f v - f u| ≤ ∑ j, L j * |v j - u j| := by
  refine abs_sub_le_sum_of_update fun w hw j s hs ↦ ?_
  have hwj : w j ∈ Icc (lo j) (hi j) := ⟨hw.1 j, hw.2 j⟩
  obtain ⟨d, hd, e⟩ := exists_eq_mul_sub_of_hasDerivAt (f := fun s ↦ f (update w j s))
    (a := w j) (b := s) (P := (· ∈ P j)) fun s' hs' ↦ by
      have hw' := update_mem_Icc hw j (uIcc_subset_Icc hwj hs hs')
      obtain ⟨d, hder, hd⟩ := hf _ hw' j
      simp only [update_self, update_idem] at hder
      exact ⟨d, hder, hd⟩
  simp only [update_eq_self] at e
  rw [e, abs_mul]
  exact mul_le_mul_of_nonneg_right (hP j d hd) (abs_nonneg _)

/-- **The centred mean value form through an implicit root** (vector form of
`abs_sub_le_of_implicit`): if `τ u ∈ [tl, th]` is a root of `F u` for `u` in the box, the partial
derivatives of `F` and `G` on the box times `[tl, th]` lie in `P j`, `Pt`, `Q j`, `Qt`, the
`t`-derivatives of `F` do not vanish, and `|q - e α / β| ≤ L j` for `q ∈ Q j`, `e ∈ Qt`,
`α ∈ P j`, `β ∈ Pt`, then `|G v (τ v) - G u (τ u)| ≤ Σ_j L j |v j - u j|` on the box. -/
theorem abs_sub_le_sum_of_implicit {F G : (Fin n → ℝ) → ℝ → ℝ} {τ : (Fin n → ℝ) → ℝ}
    {lo hi L : Fin n → ℝ} {tl th : ℝ} {P Q : Fin n → Set ℝ} {Pt Qt : Set ℝ}
    (hF : ∀ w ∈ Icc lo hi, ∀ t ∈ Icc tl th, ∀ j,
      ∃ d, HasDerivAt (fun s ↦ F (update w j s) t) d (w j) ∧ d ∈ P j)
    (hFt : ∀ w ∈ Icc lo hi, ∀ t ∈ Icc tl th, ∃ d, HasDerivAt (F w) d t ∧ d ∈ Pt)
    (hG : ∀ w ∈ Icc lo hi, ∀ t ∈ Icc tl th, ∀ j,
      ∃ d, HasDerivAt (fun s ↦ G (update w j s) t) d (w j) ∧ d ∈ Q j)
    (hGt : ∀ w ∈ Icc lo hi, ∀ t ∈ Icc tl th, ∃ d, HasDerivAt (G w) d t ∧ d ∈ Qt)
    (hcombo : ∀ j, ∀ q ∈ Q j, ∀ e ∈ Qt, ∀ α ∈ P j, ∀ β ∈ Pt, |q - e * α / β| ≤ L j)
    (hPt : ∀ β ∈ Pt, β ≠ 0) (hτ : ∀ w ∈ Icc lo hi, τ w ∈ Icc tl th ∧ F w (τ w) = 0) :
    ∀ u ∈ Icc lo hi, ∀ v ∈ Icc lo hi, |G v (τ v) - G u (τ u)| ≤ ∑ j, L j * |v j - u j| := by
  refine abs_sub_le_sum_of_update (φ := fun w ↦ G w (τ w)) fun w hw j s hs ↦ ?_
  have hwj : w j ∈ Icc (lo j) (hi j) := ⟨hw.1 j, hw.2 j⟩
  have hmem : ∀ u ∈ Icc (lo j) (hi j), update w j u ∈ Icc lo hi := fun u hu ↦
    update_mem_Icc hw j hu
  have key := abs_sub_le_of_implicit (F := fun s t ↦ F (update w j s) t)
    (G := fun s t ↦ G (update w j s) t) (τ := fun s ↦ τ (update w j s)) (a := lo j) (b := hi j)
    (tl := tl) (th := th) (L := L j) (Pu := P j) (Pt := Pt) (Qu := Q j) (Qt := Qt)
    (fun u hu t ht ↦ by
      obtain ⟨d, hd, hP⟩ := hF _ (hmem u hu) t ht j
      simp only [update_self, update_idem] at hd
      exact ⟨d, hd, hP⟩)
    (fun u hu t ht ↦ hFt _ (hmem u hu) t ht)
    (fun u hu t ht ↦ by
      obtain ⟨d, hd, hQ⟩ := hG _ (hmem u hu) t ht j
      simp only [update_self, update_idem] at hd
      exact ⟨d, hd, hQ⟩)
    (fun u hu t ht ↦ hGt _ (hmem u hu) t ht) (hcombo j) hPt
    (fun u hu ↦ hτ _ (hmem u hu)) (w j) hwj s hs
  simpa only [update_eq_self] using key

end DyadicInterval
