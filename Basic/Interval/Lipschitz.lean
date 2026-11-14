module

public import Basic.Interval.Program
public import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Lipschitz bounds from enclosures of derivatives

Tools to turn interval enclosures of partial derivatives into Lipschitz bounds, for maps defined
through an implicit root:

* `abs_sub_le_of_implicit`: if `τ(u)` is a root of `F(u, ·)` in `[tl, th]` for `u ∈ [a, b]`, and
  the partial derivatives of `F` and `G` on `[a, b] × [tl, th]` lie in sets `P_u, P_t, Q_u, Q_t`
  with `|q - e α / β| ≤ L` for all `q ∈ Q_u, e ∈ Q_t, α ∈ P_u, β ∈ P_t` (`β ≠ 0`), then
  `u ↦ G(u, τ(u))` is `L`-Lipschitz on `[a, b]`; no differentiability of `τ` is needed (the mean
  value theorem along the two axis-parallel segments `(u, τ u) → (v, τ u) → (v, τ v)`);
* `abs_sub_le_of_grid`: Lipschitz on each cell `[c m, c (m + 1)]` of a monotone grid implies
  Lipschitz on `[c 0, c N]`;
* `exists_mem_uniform_cell`: a point of `[lo, hi]` lies in a cell of the uniform subdivision;
* `lipschitzOnWith_of_abs_sub_le`: entrywise bounds `|f p i - f q i| ≤ Σ_j L i j |p j - q j|` with
  row sums `≤ K` give `LipschitzOnWith K f` in the sup metric of `Fin n → ℝ`.
-/

@[expose] public section

open Set

namespace DyadicInterval

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

/-- **Lipschitz bounds glue along a grid**: if `φ` is `L`-Lipschitz on each cell
`[c m, c (m + 1)]`, `m < N`, of a monotone grid, it is `L`-Lipschitz on `[c 0, c N]`. -/
theorem abs_sub_le_of_grid {φ : ℝ → ℝ} {L : ℝ} {c : ℕ → ℝ} (hc : Monotone c) :
    ∀ N : ℕ, (∀ m < N, ∀ x ∈ Icc (c m) (c (m + 1)), ∀ y ∈ Icc (c m) (c (m + 1)),
      |φ x - φ y| ≤ L * |x - y|) →
      ∀ x ∈ Icc (c 0) (c N), ∀ y ∈ Icc (c 0) (c N), |φ x - φ y| ≤ L * |x - y| := by
  intro N
  induction N with
  | zero =>
    intro _ x hx y hy
    have : x = y := by linarith [hx.1, hx.2, hy.1, hy.2]
    subst this
    simp
  | succ N ih =>
    intro h
    have ih' := ih fun m hm ↦ h m (Nat.lt_succ_of_lt hm)
    have hN := h N (Nat.lt_succ_self N)
    -- glue `[c 0, c N]` and `[c N, c (N + 1)]`
    have glue : ∀ x ∈ Icc (c 0) (c N), ∀ y ∈ Icc (c N) (c (N + 1)),
        |φ x - φ y| ≤ L * |x - y| := by
      intro x hx y hy
      have hN0 : c N ∈ Icc (c 0) (c N) := ⟨hc (Nat.zero_le N), le_rfl⟩
      have hN1 : c N ∈ Icc (c N) (c (N + 1)) := ⟨le_rfl, hc (Nat.le_succ N)⟩
      have h1 := ih' x hx (c N) hN0
      have h2 := hN (c N) hN1 y hy
      have e1 : |x - c N| = c N - x := by rw [abs_sub_comm, abs_of_nonneg (by linarith [hx.2])]
      have e2 : |c N - y| = y - c N := by rw [abs_sub_comm, abs_of_nonneg (by linarith [hy.1])]
      have e3 : |x - y| = y - x := by rw [abs_sub_comm, abs_of_nonneg (by linarith [hx.2, hy.1])]
      rw [e1] at h1
      rw [e2] at h2
      rw [e3]
      calc |φ x - φ y| ≤ |φ x - φ (c N)| + |φ (c N) - φ y| := abs_sub_le _ _ _
        _ ≤ L * (c N - x) + L * (y - c N) := add_le_add h1 h2
        _ = L * (y - x) := by ring
    intro x hx y hy
    rcases le_total x (c N) with hxN | hxN <;> rcases le_total y (c N) with hyN | hyN
    · exact ih' x ⟨hx.1, hxN⟩ y ⟨hy.1, hyN⟩
    · exact glue x ⟨hx.1, hxN⟩ y ⟨hyN, hy.2⟩
    · rw [abs_sub_comm, abs_sub_comm x]
      exact glue y ⟨hy.1, hyN⟩ x ⟨hxN, hx.2⟩
    · exact hN x ⟨hxN, hx.2⟩ y ⟨hyN, hy.2⟩

/-- A point of `[lo, hi]` lies in a cell `[lo + m (hi - lo)/n, lo + (m + 1)(hi - lo)/n]`, `m < n`,
of the uniform subdivision. -/
theorem exists_mem_uniform_cell {lo hi x : ℝ} (hx : x ∈ Icc lo hi) {n : ℕ} (hn : 0 < n) :
    ∃ m < n, lo + m * (hi - lo) / n ≤ x ∧ x ≤ lo + (m + 1) * (hi - lo) / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rcases eq_or_lt_of_le (hx.1.trans hx.2) with he | hlt
  · refine ⟨0, hn, ?_, ?_⟩ <;> simp [he] <;> linarith [hx.1, hx.2]
  set y := (x - lo) * n / (hi - lo) with hy
  have hy0 : 0 ≤ y := div_nonneg (mul_nonneg (by linarith [hx.1]) hn'.le) (by linarith)
  have hyn : y ≤ n := by
    rw [hy, div_le_iff₀ (by linarith)]
    nlinarith [hx.2]
  set m := min (⌊y⌋₊) (n - 1) with hm
  have hmn : m < n := lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hn one_pos)
  refine ⟨m, hmn, ?_, ?_⟩
  · have : (m : ℝ) ≤ y := (Nat.cast_le.2 (min_le_left _ _)).trans (Nat.floor_le hy0)
    rw [hy, le_div_iff₀ (by linarith)] at this
    have h2 : (m : ℝ) * (hi - lo) / n ≤ x - lo := by rw [div_le_iff₀ hn']; linarith
    linarith
  · rcases le_or_gt (n - 1) ⌊y⌋₊ with h | h
    · have hm' : m = n - 1 := by rw [hm, min_eq_right h]
      have : ((m : ℝ) + 1) = n := by
        rw [hm']; rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [this, mul_div_assoc, mul_div_cancel₀ _ hn'.ne']
      linarith [hx.2]
    · have hm' : m = ⌊y⌋₊ := by rw [hm, min_eq_left h.le]
      have := Nat.lt_floor_add_one y
      rw [← hm'] at this
      rw [hy, div_lt_iff₀ (by linarith)] at this
      rw [add_div' _ _ _ hn'.ne', le_div_iff₀ hn']
      nlinarith

/-- **Entrywise bounds give a Lipschitz bound in the sup metric**: if
`|f p i - f q i| ≤ Σ_j L i j |p j - q j|` on `S` with `L ≥ 0` and row sums `≤ K`, then `f` is
`K`-Lipschitz on `S`. -/
theorem lipschitzOnWith_of_abs_sub_le {n : ℕ} {f : (Fin n → ℝ) → Fin n → ℝ}
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

end DyadicInterval
