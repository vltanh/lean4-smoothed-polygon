module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Mean value bounds through an implicit root

Bounds on the variation of `u ↦ G u (τ u)`, where `τ u` is a root of `F u`, on a box `Icc lo hi`
of `Fin n → ℝ`, from bounds on the partial derivatives of `F` and `G` alone: the implicit function
theorem is not needed, and `τ` need not be differentiable, nor even continuous.

* `exists_eq_mul_sub_of_hasDerivAt`: the mean value theorem in the form `f b - f a = d (b - a)`
  for some `d` with a property `P` that every derivative of `f` on `[a, b]` has;
* `abs_sub_le_of_implicit`: if `τ u ∈ [tl, th]` is a root of `F u` for `u ∈ [a, b]`, and the
  partial derivatives of `F` and `G` on `[a, b] × [tl, th]` lie in sets `P_u, P_t, Q_u, Q_t` with
  `|q - e α / β| ≤ L` for all `q ∈ Q_u, e ∈ Q_t, α ∈ P_u, β ∈ P_t` (`β ≠ 0`), then
  `u ↦ G u (τ u)` is `L`-Lipschitz on `[a, b]` (the mean value theorem along the two
  axis-parallel segments `(u, τ u) → (v, τ u) → (v, τ v)`);
* `abs_sub_le_sum_of_update`: bounds `|φ (update w j s) - φ w| ≤ L j |s - w j|` along the
  coordinate directions inside the box add up along the axis-parallel path from `u` to `v`;
* `abs_sub_le_sum_of_implicit`: the vector form of `abs_sub_le_of_implicit` on a box;
* `lipschitzOnWith_of_abs_sub_le`: entrywise bounds `|f p i - f q i| ≤ Σ_j L i j |p j - q j|` with
  row sums `≤ K` give `LipschitzOnWith K f` in the sup metric of `Fin n → ℝ`.
-/

@[expose] public section

open Set Function

/-- **The mean value theorem for a property of the derivatives**: if at every point of `[a, b]`
(either order) `f` has a derivative with a property `P`, then `f b - f a = d (b - a)` for some `d`
with `P d`. -/
theorem exists_eq_mul_sub_of_hasDerivAt {f : ℝ → ℝ} {a b : ℝ} {P : ℝ → Prop}
    (h : ∀ s ∈ Set.uIcc a b, ∃ d, HasDerivAt f d s ∧ P d) :
    ∃ d, P d ∧ f b - f a = d * (b - a) := by
  -- the case `a < b`
  have key : ∀ a b : ℝ, a < b → (∀ s ∈ Set.Icc a b, ∃ d, HasDerivAt f d s ∧ P d) →
      ∃ d, P d ∧ f b - f a = d * (b - a) := by
    intro a b hab h
    have hd : ∀ s ∈ Set.Icc a b, HasDerivAt f (deriv f s) s := fun s hs ↦ by
      obtain ⟨d, hd, -⟩ := h s hs
      rwa [hd.deriv]
    have hc : ContinuousOn f (Set.Icc a b) := fun s hs ↦ (hd s hs).continuousAt.continuousWithinAt
    obtain ⟨c, hc', hcd⟩ := exists_hasDerivAt_eq_slope f (deriv f) hab hc
      (fun s hs ↦ hd s (Set.Ioo_subset_Icc_self hs))
    obtain ⟨d, hd', hP⟩ := h c (Set.Ioo_subset_Icc_self hc')
    refine ⟨d, hP, ?_⟩
    rw [← hd'.deriv, hcd]
    field_simp [(sub_pos.2 hab).ne']
  rcases lt_trichotomy a b with hab | rfl | hab
  · exact key a b hab fun s hs ↦ h s (Set.Icc_subset_uIcc hs)
  · obtain ⟨d, -, hP⟩ := h a (by simp)
    exact ⟨d, hP, by ring⟩
  · obtain ⟨d, hP, e⟩ := key b a hab fun s hs ↦ h s (Set.Icc_subset_uIcc' hs)
    exact ⟨d, hP, by linarith⟩

/-- **The Lipschitz bound through an implicit root.** -/
theorem abs_sub_le_of_implicit {F G : ℝ → ℝ → ℝ} {τ : ℝ → ℝ} {a b tl th L : ℝ}
    {Pu Pt Qu Qt : Set ℝ}
    (hFu : ∀ u ∈ Icc a b, ∀ t ∈ Icc tl th, ∃ d, HasDerivAt (fun s ↦ F s t) d u ∧ d ∈ Pu)
    (hFt : ∀ u ∈ Icc a b, ∀ t ∈ Icc tl th, ∃ d, HasDerivAt (fun s ↦ F u s) d t ∧ d ∈ Pt)
    (hGu : ∀ u ∈ Icc a b, ∀ t ∈ Icc tl th, ∃ d, HasDerivAt (fun s ↦ G s t) d u ∧ d ∈ Qu)
    (hGt : ∀ u ∈ Icc a b, ∀ t ∈ Icc tl th, ∃ d, HasDerivAt (fun s ↦ G u s) d t ∧ d ∈ Qt)
    (hcombo : ∀ q ∈ Qu, ∀ e ∈ Qt, ∀ α ∈ Pu, ∀ β ∈ Pt, |q - e * α / β| ≤ L)
    (hPt : ∀ β ∈ Pt, β ≠ 0) (hτ : ∀ u ∈ Icc a b, τ u ∈ Icc tl th ∧ F u (τ u) = 0) :
    ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, |G v (τ v) - G u (τ u)| ≤ L * |v - u| := by
  intro u hu v hv
  obtain ⟨htu, hFu0⟩ := hτ u hu
  obtain ⟨htv, hFv0⟩ := hτ v hv
  have hseg : ∀ s ∈ uIcc u v, s ∈ Icc a b := fun s hs ↦ uIcc_subset_Icc hu hv hs
  have hsegt : ∀ s ∈ uIcc (τ u) (τ v), s ∈ Icc tl th := fun s hs ↦ uIcc_subset_Icc htu htv hs
  -- the four mean value steps
  obtain ⟨α, hα, e1⟩ := exists_eq_mul_sub_of_hasDerivAt (f := fun s ↦ F s (τ u)) (a := u) (b := v)
    (P := (· ∈ Pu)) fun s hs ↦ hFu s (hseg s hs) (τ u) htu
  obtain ⟨β, hβ, e2⟩ := exists_eq_mul_sub_of_hasDerivAt (f := fun s ↦ F v s) (a := τ u)
    (b := τ v) (P := (· ∈ Pt)) fun s hs ↦ hFt v hv s (hsegt s hs)
  obtain ⟨q, hq, e3⟩ := exists_eq_mul_sub_of_hasDerivAt (f := fun s ↦ G s (τ u)) (a := u) (b := v)
    (P := (· ∈ Qu)) fun s hs ↦ hGu s (hseg s hs) (τ u) htu
  obtain ⟨e, he, e4⟩ := exists_eq_mul_sub_of_hasDerivAt (f := fun s ↦ G v s) (a := τ u)
    (b := τ v) (P := (· ∈ Qt)) fun s hs ↦ hGt v hv s (hsegt s hs)
  have hβ0 := hPt β hβ
  -- `0 = α (v - u) + β (τ v - τ u)`
  have ht : τ v - τ u = -(α * (v - u)) / β := by
    field_simp
    linarith
  have key : G v (τ v) - G u (τ u) = (q - e * α / β) * (v - u) := by
    have : G v (τ v) - G u (τ u) = (G v (τ v) - G v (τ u)) + (G v (τ u) - G u (τ u)) := by ring
    rw [this, e4, e3, ht]
    field_simp
    ring
  rw [key, abs_mul]
  exact mul_le_mul_of_nonneg_right (hcombo q hq e he α hα β hβ) (abs_nonneg _)

variable {n : ℕ}

private theorem update_mem_Icc {lo hi w : Fin n → ℝ} (hw : w ∈ Icc lo hi) (j : Fin n) {s : ℝ}
    (hs : s ∈ Icc (lo j) (hi j)) : update w j s ∈ Icc lo hi := by
  constructor <;> intro i <;> by_cases h : i = j
  · subst h; simpa using hs.1
  · simpa [update_of_ne h] using hw.1 i
  · subst h; simpa using hs.2
  · simpa [update_of_ne h] using hw.2 i

/-- The point of the axis-parallel path from `u` to `v` after `k` steps: `v` in the coordinates
`< k`, `u` in the others. -/
private def pathPt (u v : Fin n → ℝ) (k : ℕ) : Fin n → ℝ := fun j ↦ if (j : ℕ) < k then v j else u j

private theorem pathPt_mem {lo hi u v : Fin n → ℝ} (hu : u ∈ Icc lo hi) (hv : v ∈ Icc lo hi)
    (k : ℕ) : pathPt u v k ∈ Icc lo hi := by
  constructor <;> intro j <;> simp only [pathPt] <;> split_ifs
  exacts [hv.1 j, hu.1 j, hv.2 j, hu.2 j]

private theorem pathPt_zero (u v : Fin n → ℝ) : pathPt u v 0 = u := by
  funext j; simp [pathPt]

private theorem pathPt_self (u v : Fin n → ℝ) : pathPt u v n = v := by
  funext j; simp [pathPt, j.2]

private theorem pathPt_succ (u v : Fin n → ℝ) {k : ℕ} (hk : k < n) :
    pathPt u v (k + 1) = update (pathPt u v k) ⟨k, hk⟩ (v ⟨k, hk⟩) := by
  funext j
  by_cases hj : j = ⟨k, hk⟩
  · subst hj; simp [pathPt]
  · have : (j : ℕ) ≠ k := fun h ↦ hj (Fin.ext h)
    simp only [pathPt, update_of_ne hj]
    split_ifs with h1 h2 h2 <;> first | rfl | omega

private theorem pathPt_apply_self (u v : Fin n → ℝ) {k : ℕ} (hk : k < n) :
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

/-- **The mean value bound through an implicit root, on a box** (vector form of
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

/-- **Entrywise bounds give a Lipschitz bound in the sup metric**: if
`|f p i - f q i| ≤ Σ_j L i j |p j - q j|` on `S` with `L ≥ 0` and row sums `≤ K`, then `f` is
`K`-Lipschitz on `S`. -/
theorem lipschitzOnWith_of_abs_sub_le {f : (Fin n → ℝ) → Fin n → ℝ}
    {S : Set (Fin n → ℝ)} {L : Fin n → Fin n → ℝ} {K : NNReal} (hL0 : ∀ i j, 0 ≤ L i j)
    (hK : ∀ i, ∑ j, L i j ≤ K)
    (h : ∀ p ∈ S, ∀ q ∈ S, ∀ i, |f p i - f q i| ≤ ∑ j, L i j * |p j - q j|) :
    LipschitzOnWith K f S := by
  refine LipschitzOnWith.of_dist_le_mul fun p hp q hq ↦ ?_
  refine (dist_pi_le_iff (by positivity)).2 fun i ↦ ?_
  rw [Real.dist_eq]
  refine (h p hp q hq i).trans ?_
  calc ∑ j, L i j * |p j - q j| ≤ ∑ j, L i j * dist p q := by
        refine Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left ?_ (hL0 i j)
        rw [← Real.dist_eq]
        exact dist_le_pi_dist p q j
    _ = (∑ j, L i j) * dist p q := by rw [Finset.sum_mul]
    _ ≤ K * dist p q := mul_le_mul_of_nonneg_right (hK i) dist_nonneg
