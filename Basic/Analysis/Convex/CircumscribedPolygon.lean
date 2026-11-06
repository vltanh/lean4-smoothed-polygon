module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Algebra.Order.ToIntervalMod
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.Matrix.Mul
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Circumscribed polygons of a planar convex set; Dowker's theorem

For a compact set `K` in the plane `Fin 2 → ℝ` and `k : ℕ`, `minCircumscribedArea K k` is
`t_K(k)`, the infimum of the areas of the polygons with at most `k` sides containing `K`, that is,
of the intersections of `k` closed half-planes containing `K`.

* `PlaneConvex.minCircumscribedArea_add_le` (**Dowker's theorem**, C. H. Dowker, *On minimum
  circumscribed polygons*, Bull. AMS 50 (1944)): if `m + n = 2k`, then
  `t_K(k) + t_K(k) ≤ t_K(m) + t_K(n)`; in particular `k ↦ t_K(k)` is convex.
* `PlaneConvex.exists_symm_le` (Dowker's theorem for centrally symmetric sets): if `K = -K`, then
  every circumscribed `2j`-gon can be replaced by a centrally symmetric circumscribed `2j`-gon
  (normal directions `±θ₁, …, ±θⱼ`) of no larger area.
* `PlaneConvex.minCircumscribedArea_six_add_le`: the supporting line of the convex function `t_K`
  at `6`, `t_K(6) + 6d ≤ t_K(s) + s d` for `s ≥ 3`, `d = t_K(6) - t_K(7)` (the form in which
  Dowker's theorem enters Fejes Tóth's packing inequality); also `t_K` is antitone
  (`PlaneConvex.antitone_minCircumscribedArea`) and finite for `k ≥ 4`
  (`PlaneConvex.minCircumscribedArea_lt_top`).
* `PlaneConvex.minCircumscribedArea_image_motion`: `t_K(k)` is invariant under Euclidean motions
  `x ↦ A x + b`, `A` orthogonal.

The proof is not Dowker's (which uses the area of a circumscribed polygon as a sum over pairs of
consecutive normals). It is a measure-theoretic "alternating merge": merge the normal directions
of a circumscribed `m`-gon `P` and `n`-gon `Q` in cyclic order and give them alternately to two
`k`-gons `X` and `Y`. Then `X ∩ Y = P ∩ Q` and `X ∪ Y ⊆ P ∪ Q`, so
`|X| + |Y| = |X ∪ Y| + |X ∩ Y| ≤ |P ∪ Q| + |P ∩ Q| = |P| + |Q|`. The inclusion `X ∪ Y ⊆ P ∪ Q`
holds because the normal directions `u` of the support lines of `K` that a point `x` violates
(`h_K(u) < ⟨u, x⟩`) form an arc of length `< π` (the trace of the convex cone where the concave
function `u ↦ ⟨u, x⟩ - h_K(u)` is positive), so a point satisfying every constraint of `X`
violates at most one constraint of `Y` (between two directions of `Y` there is one of `X`, on
both sides).
-/

@[expose] public section

open MeasureTheory Set Real
open scoped ENNReal

namespace PlaneConvex

/-! ### Directions and support functions -/

/-- The unit vector `(cos θ, sin θ)` of angle `θ`. -/
noncomputable def dir (θ : ℝ) : Fin 2 → ℝ := ![Real.cos θ, Real.sin θ]

/-- The support function `h_K(v) = sup_{y ∈ K} ⟨v, y⟩` of a set `K` of the plane. -/
noncomputable def supportFun (K : Set (Fin 2 → ℝ)) (v : Fin 2 → ℝ) : ℝ :=
  sSup ((fun y ↦ v ⬝ᵥ y) '' K)

/-- The polygon cut out by the support half-planes `⟨u, x⟩ ≤ h_K(u)` of `K` with outer normals
`u = dir (θ i)`. -/
def circPolygon (K : Set (Fin 2 → ℝ)) {ι : Type*} (θ : ι → ℝ) : Set (Fin 2 → ℝ) :=
  {x | ∀ i, dir (θ i) ⬝ᵥ x ≤ supportFun K (dir (θ i))}

/-- The polygon cut out by `k` closed half-planes `⟨a i, x⟩ ≤ c i`. -/
def halfPlanesInter {ι : Type*} (a : ι → Fin 2 → ℝ) (c : ι → ℝ) : Set (Fin 2 → ℝ) :=
  {x | ∀ i, a i ⬝ᵥ x ≤ c i}

/-- `t_K(k)`: the infimum of the areas of the intersections of `k` closed half-planes containing
`K`, i.e. of the polygons with at most `k` sides containing `K`. -/
noncomputable def minCircumscribedArea (K : Set (Fin 2 → ℝ)) (k : ℕ) : ℝ≥0∞ :=
  ⨅ (a : Fin k → Fin 2 → ℝ) (c : Fin k → ℝ) (_ : K ⊆ halfPlanesInter a c),
    volume (halfPlanesInter a c)

/-- `x` violates the support half-plane of `K` with outer normal `dir θ`. -/
def Violates (K : Set (Fin 2 → ℝ)) (x : Fin 2 → ℝ) (θ : ℝ) : Prop :=
  supportFun K (dir θ) < dir θ ⬝ᵥ x

theorem dir_dotProduct (θ : ℝ) (x : Fin 2 → ℝ) :
    dir θ ⬝ᵥ x = Real.cos θ * x 0 + Real.sin θ * x 1 := by
  simp [dir, dotProduct, Fin.sum_univ_two]

theorem dir_add_two_pi (θ : ℝ) : dir (θ + 2 * π) = dir θ := by
  simp [dir, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem dir_add_pi (θ : ℝ) : dir (θ + π) = -dir θ := by
  ext i; fin_cases i <;> simp [dir, Real.cos_add_pi, Real.sin_add_pi]

theorem dir_sub_int_mul_two_pi (θ : ℝ) (n : ℤ) : dir (θ - n * (2 * π)) = dir θ := by
  simp [dir, Real.cos_sub_int_mul_two_pi, Real.sin_sub_int_mul_two_pi]

theorem dir_toIcoMod (θ : ℝ) : dir (toIcoMod two_pi_pos 0 θ) = dir θ := by
  rw [toIcoMod, zsmul_eq_mul, dir_sub_int_mul_two_pi]

theorem dir_ne_zero (θ : ℝ) : dir θ ≠ 0 := by
  intro h
  have h0 : Real.cos θ = 0 := by simpa [dir] using congrFun h 0
  have h1 : Real.sin θ = 0 := by simpa [dir] using congrFun h 1
  have := Real.sin_sq_add_cos_sq θ
  rw [h0, h1] at this
  norm_num at this

theorem mem_circPolygon_iff {K : Set (Fin 2 → ℝ)} {ι : Type*} {θ : ι → ℝ} {x : Fin 2 → ℝ} :
    x ∈ circPolygon K θ ↔ ∀ i, ¬ Violates K x (θ i) := by
  simp [circPolygon, Violates]

theorem isClosed_halfPlanesInter {ι : Type*} (a : ι → Fin 2 → ℝ) (c : ι → ℝ) :
    IsClosed (halfPlanesInter a c) := by
  have : halfPlanesInter a c = ⋂ i, {x | a i ⬝ᵥ x ≤ c i} := by ext; simp [halfPlanesInter]
  rw [this]
  exact isClosed_iInter fun i ↦ isClosed_le (by fun_prop) continuous_const

theorem convex_halfPlanesInter {ι : Type*} (a : ι → Fin 2 → ℝ) (c : ι → ℝ) :
    Convex ℝ (halfPlanesInter a c) := by
  have : halfPlanesInter a c = ⋂ i, {x | a i ⬝ᵥ x ≤ c i} := by ext; simp [halfPlanesInter]
  rw [this]
  exact convex_iInter fun i ↦ convex_halfSpace_le
    ⟨fun x y ↦ dotProduct_add _ _ _, fun r x ↦ dotProduct_smul r _ _⟩ (c i)

/-- Finitely many non-overlapping convex sets in `Q` have total area at most `|Q|`. -/
theorem sum_volume_le_of_pairwise_disjoint_interior {ι : Type*} [Fintype ι]
    (C : ι → Set (Fin 2 → ℝ)) (hC : ∀ i, Convex ℝ (C i))
    (hdisj : Pairwise fun i j ↦ Disjoint (interior (C i)) (interior (C j)))
    {Q : Set (Fin 2 → ℝ)} (hsub : ∀ i, C i ⊆ Q) : ∑ i, volume (C i) ≤ volume Q := by
  have hint : ∀ i, volume (interior (C i)) = volume (C i) := fun i ↦
    measure_congr (interior_ae_eq_of_null_frontier (Convex.addHaar_frontier volume (hC i)))
  simp_rw [← hint]
  rw [← tsum_fintype (L := .unconditional _) (fun i ↦ volume (interior (C i))),
    ← measure_iUnion hdisj fun i ↦ isOpen_interior.measurableSet]
  exact measure_mono (iUnion_subset fun i ↦ interior_subset.trans (hsub i))

theorem circPolygon_eq_halfPlanesInter (K : Set (Fin 2 → ℝ)) {ι : Type*} (θ : ι → ℝ) :
    circPolygon K θ = halfPlanesInter (fun i ↦ dir (θ i)) (fun i ↦ supportFun K (dir (θ i))) :=
  rfl

theorem isClosed_circPolygon (K : Set (Fin 2 → ℝ)) {ι : Type*} (θ : ι → ℝ) :
    IsClosed (circPolygon K θ) :=
  isClosed_halfPlanesInter _ _

theorem measurableSet_circPolygon (K : Set (Fin 2 → ℝ)) {ι : Type*} (θ : ι → ℝ) :
    MeasurableSet (circPolygon K θ) :=
  (isClosed_circPolygon K θ).measurableSet

section Support

variable {K : Set (Fin 2 → ℝ)}

theorem bddAbove_image_dotProduct (hK : IsCompact K) (v : Fin 2 → ℝ) :
    BddAbove ((fun y ↦ v ⬝ᵥ y) '' K) :=
  (hK.image (by fun_prop)).bddAbove

theorem dotProduct_le_supportFun (hK : IsCompact K) (v : Fin 2 → ℝ) {y : Fin 2 → ℝ}
    (hy : y ∈ K) : v ⬝ᵥ y ≤ supportFun K v :=
  le_csSup (bddAbove_image_dotProduct hK v) ⟨y, hy, rfl⟩

/-- The support function is subadditive and positively homogeneous. -/
theorem supportFun_smul_add_smul_le (hK : IsCompact K) (hne : K.Nonempty) (v w : Fin 2 → ℝ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    supportFun K (a • v + b • w) ≤ a * supportFun K v + b * supportFun K w := by
  apply csSup_le (hne.image _)
  rintro _ ⟨y, hy, rfl⟩
  simp only [add_dotProduct, smul_dotProduct, smul_eq_mul]
  have h1 := dotProduct_le_supportFun hK v hy
  have h2 := dotProduct_le_supportFun hK w hy
  nlinarith

theorem supportFun_add_supportFun_neg_nonneg (hK : IsCompact K) (hne : K.Nonempty)
    (v : Fin 2 → ℝ) : 0 ≤ supportFun K v + supportFun K (-v) := by
  obtain ⟨y, hy⟩ := hne
  have h1 := dotProduct_le_supportFun hK v hy
  have h2 := dotProduct_le_supportFun hK (-v) hy
  simp only [neg_dotProduct] at h2
  linarith

theorem supportFun_zero (hne : K.Nonempty) : supportFun K 0 = 0 := by
  simp [supportFun, hne.image_const]

theorem supportFun_smul (hK : IsCompact K) (hne : K.Nonempty) (v : Fin 2 → ℝ) {a : ℝ}
    (ha : 0 ≤ a) : supportFun K (a • v) = a * supportFun K v := by
  apply le_antisymm
  · simpa using supportFun_smul_add_smul_le hK hne v 0 ha le_rfl
  · rcases ha.eq_or_lt with rfl | ha
    · simp [supportFun_zero hne]
    · have := supportFun_smul_add_smul_le hK hne (a • v) 0 (inv_nonneg.2 ha.le) le_rfl
      rw [smul_smul, inv_mul_cancel₀ ha.ne', one_smul] at this
      simp only [smul_zero, add_zero, zero_mul] at this
      calc a * supportFun K v ≤ a * (a⁻¹ * supportFun K (a • v)) :=
            mul_le_mul_of_nonneg_left this ha.le
        _ = supportFun K (a • v) := by field_simp

theorem subset_circPolygon (hK : IsCompact K) {ι : Type*} (θ : ι → ℝ) : K ⊆ circPolygon K θ :=
  fun _ hy _ ↦ dotProduct_le_supportFun hK _ hy

/-- Supporting half-planes are the smallest half-planes with given normals containing `K`. -/
theorem supportFun_le_of_subset {a : Fin 2 → ℝ} {c : ℝ} (hne : K.Nonempty)
    (h : ∀ y ∈ K, a ⬝ᵥ y ≤ c) : supportFun K a ≤ c :=
  csSup_le (hne.image _) (by rintro _ ⟨y, hy, rfl⟩; exact h y hy)

end Support

/-! ### The violated directions form an arc of length `< π` -/

section Arc

variable {K : Set (Fin 2 → ℝ)}

theorem dir_combo {θ φ ψ : ℝ} :
    Real.sin (φ - θ) • dir ψ = Real.sin (φ - ψ) • dir θ + Real.sin (ψ - θ) • dir φ := by
  ext i
  fin_cases i <;> simp [dir, Real.sin_sub] <;> ring

theorem violates_add_two_pi_iff {x : Fin 2 → ℝ} {θ : ℝ} :
    Violates K x (θ + 2 * π) ↔ Violates K x θ := by
  simp [Violates, dir_add_two_pi]

theorem Violates.congr_dir {x : Fin 2 → ℝ} {θ θ' : ℝ} (h : dir θ = dir θ') :
    Violates K x θ ↔ Violates K x θ' := by
  simp [Violates, h]

/-- Two antipodal support half-planes cannot both be violated. -/
theorem not_violates_and_violates_add_pi (hK : IsCompact K) (hne : K.Nonempty)
    {x : Fin 2 → ℝ} {θ : ℝ} (h1 : Violates K x θ) (h2 : Violates K x (θ + π)) : False := by
  unfold Violates at h1 h2
  rw [dir_add_pi, neg_dotProduct] at h2
  have := supportFun_add_supportFun_neg_nonneg hK hne (dir θ)
  linarith

/-- **The violated directions form an arc.** If `x` violates the support half-planes with normal
angles `θ ≤ φ`, `φ - θ < π`, then it violates those with angles `ψ ∈ [θ, φ]`. -/
theorem violates_of_le_of_le (hK : IsCompact K) (hne : K.Nonempty) {x : Fin 2 → ℝ}
    {θ φ ψ : ℝ} (hθ : Violates K x θ) (hφ : Violates K x φ) (hθψ : θ ≤ ψ) (hψφ : ψ ≤ φ)
    (hlt : φ - θ < π) : Violates K x ψ := by
  rcases (hθψ.trans hψφ).eq_or_lt with heq | hlt'
  · have : ψ = θ := le_antisymm (heq ▸ hψφ) hθψ
    rwa [this]
  have hS : 0 < Real.sin (φ - θ) := Real.sin_pos_of_pos_of_lt_pi (by linarith) hlt
  have hα : 0 ≤ Real.sin (φ - ψ) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hβ : 0 ≤ Real.sin (ψ - θ) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  set S := Real.sin (φ - θ)
  set α := Real.sin (φ - ψ)
  set β := Real.sin (ψ - θ)
  have hcombo : dir ψ = (α / S) • dir θ + (β / S) • dir φ := by
    have := dir_combo (θ := θ) (φ := φ) (ψ := ψ)
    rw [div_eq_inv_mul, div_eq_inv_mul, mul_smul, mul_smul, ← smul_add, ← this, smul_smul,
      inv_mul_cancel₀ hS.ne', one_smul]
  have hαβ : 0 < α + β := by
    rcases hα.eq_or_lt with h0 | h0
    · rcases hβ.eq_or_lt with h1 | h1
      · exfalso
        apply dir_ne_zero ψ
        rw [hcombo, ← h0, ← h1]
        simp
      · linarith
    · linarith
  have hsub := supportFun_smul_add_smul_le hK hne (dir θ) (dir φ)
    (div_nonneg hα hS.le) (div_nonneg hβ hS.le)
  unfold Violates at hθ hφ ⊢
  rw [hcombo]
  rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  refine lt_of_le_of_lt hsub ?_
  have key : 0 < α / S * (dir θ ⬝ᵥ x - supportFun K (dir θ)) +
      β / S * (dir φ ⬝ᵥ x - supportFun K (dir φ)) := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
    apply div_pos _ hS
    have h1 : 0 < dir θ ⬝ᵥ x - supportFun K (dir θ) := by linarith
    have h2 : 0 < dir φ ⬝ᵥ x - supportFun K (dir φ) := by linarith
    rcases hα.eq_or_lt with h0 | h0
    · rw [← h0, zero_mul, zero_add]; exact mul_pos (by linarith) h2
    · exact add_pos_of_pos_of_nonneg (mul_pos h0 h1) (mul_nonneg hβ h2.le)
  linarith

end Arc

/-! ### The alternating merge -/

section Merge

variable {K : Set (Fin 2 → ℝ)}

/-- Core of the alternating merge. Let `φ` be nondecreasing on positions `< N`, with all values
in a window of length `2π`. If `x` violates the directions at positions `i ≤ j`, then it violates
every direction at a position `s ∈ [i, j]` or at a position `s'` outside `(i, j)`. -/
theorem false_of_violates_pair (hK : IsCompact K) (hne : K.Nonempty) {φ : ℕ → ℝ} {N : ℕ}
    (hmono : ∀ a b, a ≤ b → b < N → φ a ≤ φ b)
    (hwrap : ∀ a b, a < N → b < N → φ b ≤ φ a + 2 * π)
    {x : Fin 2 → ℝ} {i j s s' : ℕ} (his : i ≤ s) (hsj : s ≤ j) (hjN : j < N)
    (hs' : (j ≤ s' ∧ s' < N) ∨ s' ≤ i)
    (hs : ¬ Violates K x (φ s)) (hs'v : ¬ Violates K x (φ s'))
    (hi : Violates K x (φ i)) (hj : Violates K x (φ j)) : False := by
  have hiN : i < N := by omega
  rcases lt_trichotomy (φ j - φ i) π with hlt | heq | hgt
  · exact hs (violates_of_le_of_le hK hne hi hj (hmono _ _ his (by omega)) (hmono _ _ hsj hjN)
      hlt)
  · have : φ j = φ i + π := by linarith
    rw [this] at hj
    exact not_violates_and_violates_add_pi hK hne hi hj
  · have hi' : Violates K x (φ i + 2 * π) := violates_add_two_pi_iff.2 hi
    rcases hs' with ⟨hjs', hs'N⟩ | hs'i
    · exact hs'v (violates_of_le_of_le hK hne hj hi' (hmono _ _ hjs' hs'N)
        (hwrap _ _ hiN hs'N) (by linarith))
    · have := violates_of_le_of_le hK hne hj hi' (ψ := φ s' + 2 * π)
        (hwrap _ _ (by omega) hjN) (by linarith [hmono _ _ hs'i hiN]) (by linarith)
      exact hs'v (violates_add_two_pi_iff.1 this)

/-- In the alternating merge, a point satisfying the constraints at the positions of parity `r`
violates at most one constraint at the positions of the other parity. -/
theorem eq_of_violates_of_violates (hK : IsCompact K) (hne : K.Nonempty) {φ : ℕ → ℝ} {k : ℕ}
    (hmono : ∀ a b, a ≤ b → b < 2 * k → φ a ≤ φ b)
    (hwrap : ∀ a b, a < 2 * k → b < 2 * k → φ b ≤ φ a + 2 * π)
    {x : Fin 2 → ℝ} {r : ℕ} (hr : r < 2)
    (hsat : ∀ s < 2 * k, s % 2 = r → ¬ Violates K x (φ s))
    {i j : ℕ} (hi : i < 2 * k) (hj : j < 2 * k) (hir : i % 2 ≠ r) (hjr : j % 2 ≠ r)
    (hvi : Violates K x (φ i)) (hvj : Violates K x (φ j)) : i = j := by
  by_contra hne'
  wlog hij : i < j generalizing i j
  · exact this hj hi hjr hir hvj hvi (Ne.symm hne') (by omega)
  refine false_of_violates_pair hK hne hmono hwrap (s := i + 1)
    (s' := if r = 0 then 0 else 2 * k - 1) (by omega) (by omega) hj ?_
    (hsat _ (by omega) (by omega)) ?_ hvi hvj
  · split_ifs with h <;> omega
  · split_ifs with h
    · exact hsat _ (by omega) (by omega)
    · exact hsat _ (by omega) (by omega)

theorem circPolygon_parity_eq {φ : ℕ → ℝ} {k r : ℕ} (hr : r < 2) :
    circPolygon K (fun i : Fin k ↦ φ (2 * i + r)) =
      {x | ∀ s < 2 * k, s % 2 = r → ¬ Violates K x (φ s)} := by
  ext x
  simp only [mem_circPolygon_iff, mem_ofPred_eq]
  constructor
  · intro h s hs hsr
    have := h ⟨s / 2, by omega⟩
    rwa [show 2 * (s / 2) + r = s by omega] at this
  · intro h i
    exact h _ (by omega) (by omega)

/-- **The alternating merge.** Let the normal angles of two circumscribed polygons `P = P(p)`
and `Q = P(q)` be listed (up to multiples of `2π`), injectively, at positions `< 2k` of a
nondecreasing sequence `φ` with values in a window of length `2π`. Then the polygons `X` and `Y`
formed by the even and by the odd positions satisfy `|X| + |Y| ≤ |P| + |Q|`. -/
theorem volume_alternate_add_le (hK : IsCompact K) (hne : K.Nonempty) {φ : ℕ → ℝ}
    {k m n : ℕ} (hmono : ∀ a b, a ≤ b → b < 2 * k → φ a ≤ φ b)
    (hwrap : ∀ a b, a < 2 * k → b < 2 * k → φ b ≤ φ a + 2 * π)
    (p : Fin m → ℝ) (q : Fin n → ℝ) (ι : Fin m ⊕ Fin n → ℕ) (hιN : ∀ c, ι c < 2 * k)
    (hι : Function.Injective ι) (hdir : ∀ c, dir (φ (ι c)) = dir (Sum.elim p q c)) :
    volume (circPolygon K fun i : Fin k ↦ φ (2 * i)) +
        volume (circPolygon K fun i : Fin k ↦ φ (2 * i + 1)) ≤
      volume (circPolygon K p) + volume (circPolygon K q) := by
  set X := circPolygon K fun i : Fin k ↦ φ (2 * i)
  set Y := circPolygon K fun i : Fin k ↦ φ (2 * i + 1)
  have hX : X = {x | ∀ s < 2 * k, s % 2 = 0 → ¬ Violates K x (φ s)} := by
    simpa using circPolygon_parity_eq (K := K) (φ := φ) (k := k) (r := 0) (by norm_num)
  have hY : Y = {x | ∀ s < 2 * k, s % 2 = 1 → ¬ Violates K x (φ s)} :=
    circPolygon_parity_eq (by norm_num)
  have hinter : X ∩ Y ⊆ circPolygon K p ∩ circPolygon K q := by
    rintro x ⟨hxX, hxY⟩
    rw [hX] at hxX
    rw [hY] at hxY
    have hall : ∀ c, ¬ Violates K x (Sum.elim p q c) := by
      intro c
      rw [← Violates.congr_dir (hdir c)]
      rcases Nat.mod_two_eq_zero_or_one (ι c) with h | h
      · exact hxX _ (hιN c) h
      · exact hxY _ (hιN c) h
    exact ⟨mem_circPolygon_iff.2 fun i ↦ hall (Sum.inl i),
      mem_circPolygon_iff.2 fun i ↦ hall (Sum.inr i)⟩
  have key : ∀ r < 2, ∀ x, (∀ s < 2 * k, s % 2 = r → ¬ Violates K x (φ s)) →
      x ∈ circPolygon K p ∪ circPolygon K q := by
    intro r hr x hx
    by_contra hcon
    simp only [mem_union, mem_circPolygon_iff, not_or, not_forall, not_not] at hcon
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hcon
    have hvi : Violates K x (φ (ι (Sum.inl i))) := (Violates.congr_dir (hdir _)).2 hi
    have hvj : Violates K x (φ (ι (Sum.inr j))) := (Violates.congr_dir (hdir _)).2 hj
    have hir : ι (Sum.inl i) % 2 ≠ r := fun h ↦ hx _ (hιN _) h hvi
    have hjr : ι (Sum.inr j) % 2 ≠ r := fun h ↦ hx _ (hιN _) h hvj
    have := eq_of_violates_of_violates hK hne hmono hwrap hr hx (hιN _) (hιN _) hir hjr hvi hvj
    exact Sum.inl_ne_inr (hι this)
  have hunion : X ∪ Y ⊆ circPolygon K p ∪ circPolygon K q := by
    rintro x (hx | hx)
    · rw [hX] at hx
      exact key 0 (by norm_num) x hx
    · rw [hY] at hx
      exact key 1 (by norm_num) x hx
  calc volume X + volume Y = volume (X ∪ Y) + volume (X ∩ Y) :=
        (measure_union_add_inter X (measurableSet_circPolygon K _)).symm
    _ ≤ volume (circPolygon K p ∪ circPolygon K q) +
          volume (circPolygon K p ∩ circPolygon K q) :=
        add_le_add (measure_mono hunion) (measure_mono hinter)
    _ = _ := measure_union_add_inter _ (measurableSet_circPolygon K q)

end Merge

/-! ### Minimal circumscribed polygons -/

section MinArea

variable {K : Set (Fin 2 → ℝ)}

theorem minCircumscribedArea_le {k : ℕ} {a : Fin k → Fin 2 → ℝ} {c : Fin k → ℝ}
    (h : K ⊆ halfPlanesInter a c) : minCircumscribedArea K k ≤ volume (halfPlanesInter a c) :=
  iInf_le_of_le a (iInf_le_of_le c (iInf_le_of_le h le_rfl))

theorem minCircumscribedArea_le_circPolygon (hK : IsCompact K) {k : ℕ} (θ : Fin k → ℝ) :
    minCircumscribedArea K k ≤ volume (circPolygon K θ) :=
  minCircumscribedArea_le (subset_circPolygon hK θ)

theorem volume_le_minCircumscribedArea (k : ℕ) : volume K ≤ minCircumscribedArea K k :=
  le_iInf fun _ ↦ le_iInf fun _ ↦ le_iInf fun h ↦ measure_mono h

/-- Every vector is a nonnegative multiple of a unit vector `dir θ`. -/
theorem exists_eq_smul_dir (v : Fin 2 → ℝ) : ∃ r : ℝ, 0 ≤ r ∧ ∃ θ : ℝ, v = r • dir θ := by
  set z : ℂ := ⟨v 0, v 1⟩
  by_cases hz : z = 0
  · refine ⟨0, le_rfl, 0, ?_⟩
    have h0 : v 0 = 0 := by simpa [z] using congrArg Complex.re hz
    have h1 : v 1 = 0 := by simpa [z] using congrArg Complex.im hz
    ext i; fin_cases i <;> simp [h0, h1]
  · refine ⟨‖z‖, norm_nonneg _, Complex.arg z, ?_⟩
    have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz
    have e0 : dir (Complex.arg z) 0 = v 0 / ‖z‖ := by simp [dir, Complex.cos_arg hz, z]
    have e1 : dir (Complex.arg z) 1 = v 1 / ‖z‖ := by simp [dir, Complex.sin_arg, z]
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, Pi.smul_apply, smul_eq_mul, e0]
      exact (mul_div_cancel₀ _ hn).symm
    · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul, e1]
      exact (mul_div_cancel₀ _ hn).symm

/-- A polygon with `k` sides containing `K` contains a circumscribed polygon of `K` with `k`
support lines. -/
theorem exists_circPolygon_subset (hK : IsCompact K) (hne : K.Nonempty) {ι : Type*}
    {a : ι → Fin 2 → ℝ} {c : ι → ℝ} (h : K ⊆ halfPlanesInter a c) :
    ∃ θ : ι → ℝ, circPolygon K θ ⊆ halfPlanesInter a c := by
  choose r hr θ hθ using fun i ↦ exists_eq_smul_dir (a i)
  refine ⟨θ, fun x hx i ↦ ?_⟩
  have hsupp : supportFun K (a i) ≤ c i := supportFun_le_of_subset hne fun y hy ↦ h hy i
  have hx' := hx i
  rw [hθ i, smul_dotProduct, smul_eq_mul]
  rw [hθ i, supportFun_smul hK hne _ (hr i)] at hsupp
  calc r i * (dir (θ i) ⬝ᵥ x) ≤ r i * supportFun K (dir (θ i)) :=
        mul_le_mul_of_nonneg_left hx' (hr i)
    _ ≤ c i := hsupp

theorem minCircumscribedArea_eq_iInf (hK : IsCompact K) (hne : K.Nonempty) (k : ℕ) :
    minCircumscribedArea K k = ⨅ θ : Fin k → ℝ, volume (circPolygon K θ) := by
  apply le_antisymm
  · exact le_iInf fun θ ↦ minCircumscribedArea_le_circPolygon hK θ
  · refine le_iInf fun a ↦ le_iInf fun c ↦ le_iInf fun h ↦ ?_
    obtain ⟨θ, hθ⟩ := exists_circPolygon_subset hK hne h
    exact iInf_le_of_le θ (measure_mono hθ)

/-- **Dowker's theorem** (C. H. Dowker, 1944): `t_K(k) + t_K(k) ≤ t_K(m) + t_K(n)` whenever
`m + n = 2k`; in particular `k ↦ t_K(k)` is convex. -/
theorem minCircumscribedArea_add_le (hK : IsCompact K) (hne : K.Nonempty) {k m n : ℕ}
    (h : m + n = 2 * k) :
    minCircumscribedArea K k + minCircumscribedArea K k ≤
      minCircumscribedArea K m + minCircumscribedArea K n := by
  rw [minCircumscribedArea_eq_iInf hK hne m, minCircumscribedArea_eq_iInf hK hne n,
    ENNReal.iInf_add]
  refine le_iInf fun p ↦ ?_
  rw [ENNReal.add_iInf]
  refine le_iInf fun q ↦ ?_
  let e : Fin (m + n) ≃ Fin m ⊕ Fin n := finSumFinEquiv.symm
  let θ : Fin (m + n) → ℝ := fun s ↦ toIcoMod two_pi_pos 0 (Sum.elim p q (e s))
  let σ := Tuple.sort θ
  let φ : ℕ → ℝ := fun s ↦ if hs : s < m + n then θ (σ ⟨s, hs⟩) else 0
  let ι : Fin m ⊕ Fin n → ℕ := fun c ↦ (σ.symm (e.symm c)).val
  have hmono : ∀ a b, a ≤ b → b < 2 * k → φ a ≤ φ b := by
    intro a b hab hb
    have ha' : a < m + n := by omega
    have hb' : b < m + n := by omega
    simp only [φ, ha', hb', ↓reduceDIte]
    exact Tuple.monotone_sort θ (show (⟨a, ha'⟩ : Fin (m + n)) ≤ ⟨b, hb'⟩ from hab)
  have hrange : ∀ s, 0 ≤ φ s ∧ φ s < 2 * π := by
    intro s
    simp only [φ]
    split_ifs
    · have := toIcoMod_mem_Ico' two_pi_pos (Sum.elim p q (e (σ ⟨s, by omega⟩)))
      exact ⟨this.1, this.2⟩
    · exact ⟨le_rfl, two_pi_pos⟩
  have hwrap : ∀ a b, a < 2 * k → b < 2 * k → φ b ≤ φ a + 2 * π := fun a b _ _ ↦ by
    linarith [hrange a, hrange b]
  have hιN : ∀ c, ι c < 2 * k := fun c ↦ by
    have := (σ.symm (e.symm c)).isLt
    simp only [ι]
    omega
  have hι : Function.Injective ι := by
    intro c c' hcc'
    have : σ.symm (e.symm c) = σ.symm (e.symm c') := Fin.ext hcc'
    simpa using this
  have hdir : ∀ c, dir (φ (ι c)) = dir (Sum.elim p q c) := by
    intro c
    simp only [φ, ι, (σ.symm (e.symm c)).isLt, ↓reduceDIte, Fin.eta, Equiv.apply_symm_apply, θ,
      dir_toIcoMod]
  calc minCircumscribedArea K k + minCircumscribedArea K k ≤
        volume (circPolygon K fun i : Fin k ↦ φ (2 * i)) +
          volume (circPolygon K fun i : Fin k ↦ φ (2 * i + 1)) :=
        add_le_add (minCircumscribedArea_le_circPolygon hK _)
          (minCircumscribedArea_le_circPolygon hK _)
    _ ≤ _ := volume_alternate_add_le hK hne hmono hwrap p q ι hιN hι hdir

/-! ### Centrally symmetric sets -/

theorem supportFun_neg (hsymm : ∀ x ∈ K, -x ∈ K) (v : Fin 2 → ℝ) :
    supportFun K (-v) = supportFun K v := by
  unfold supportFun
  congr 1
  ext t
  simp only [mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨-y, hsymm y hy, by simp⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨-y, hsymm y hy, by simp⟩

/-- A circumscribed polygon with normals `±dir (c i)` of a centrally symmetric set. -/
theorem circPolygon_symm_eq (hsymm : ∀ x ∈ K, -x ∈ K) {ι : Type*} (c : ι → ℝ) :
    circPolygon K (Sum.elim c fun i ↦ c i + π) =
      {x | ∀ i, |dir (c i) ⬝ᵥ x| ≤ supportFun K (dir (c i))} := by
  ext x
  simp only [circPolygon, mem_ofPred_eq, Sum.forall, Sum.elim_inl, Sum.elim_inr, dir_add_pi,
    supportFun_neg hsymm, neg_dotProduct, abs_le]
  constructor
  · rintro ⟨h1, h2⟩ i
    exact ⟨by linarith [h2 i], h1 i⟩
  · intro h
    exact ⟨fun i ↦ (h i).2, fun i ↦ by linarith [(h i).1]⟩

theorem volume_circPolygon_add_pi (hsymm : ∀ x ∈ K, -x ∈ K) {ι : Type*} (p : ι → ℝ) :
    volume (circPolygon K fun i ↦ p i + π) = volume (circPolygon K p) := by
  have : circPolygon K (fun i ↦ p i + π) = -circPolygon K p := by
    ext x
    simp only [Set.mem_neg, circPolygon, mem_ofPred_eq, dir_add_pi, supportFun_neg hsymm,
      neg_dotProduct, dotProduct_neg]
  rw [this, Measure.measure_neg]

/-- **Dowker's theorem for centrally symmetric sets.** If `K = -K`, every circumscribed polygon
with `2j` support lines can be replaced by a centrally symmetric one, with normals
`±dir (c i)`, `i < j`, of no larger area. -/
theorem exists_symm_le (hK : IsCompact K) (hne : K.Nonempty) (hsymm : ∀ x ∈ K, -x ∈ K)
    {j : ℕ} (p : Fin (2 * j) → ℝ) :
    ∃ c : Fin j → ℝ, volume (circPolygon K (Sum.elim c fun i ↦ c i + π)) ≤
      volume (circPolygon K p) := by
  let a : Fin (2 * j) → ℝ := fun i ↦ toIcoMod two_pi_pos 0 (p i)
  have ha : ∀ i, 0 ≤ a i ∧ a i < 2 * π := fun i ↦
    ⟨(toIcoMod_mem_Ico' two_pi_pos (p i)).1, (toIcoMod_mem_Ico' two_pi_pos (p i)).2⟩
  let ψ : Fin (2 * j) → ℝ := fun i ↦ if π ≤ a i then a i - π else a i
  have hψ : ∀ i, 0 ≤ ψ i ∧ ψ i < π := by
    intro i
    simp only [ψ]
    split_ifs with h
    · constructor <;> linarith [ha i]
    · exact ⟨(ha i).1, not_le.1 h⟩
  let σ := Tuple.sort ψ
  let ψ' : ℕ → ℝ := fun s ↦ if hs : s < (2 * j) then ψ (σ ⟨s, hs⟩) else 0
  let φ : ℕ → ℝ := fun s ↦ if s < (2 * j) then ψ' s else ψ' (s - (2 * j)) + π
  have hψ'r : ∀ s, 0 ≤ ψ' s ∧ ψ' s < π := by
    intro s
    simp only [ψ']
    split_ifs
    · exact hψ _
    · exact ⟨le_rfl, pi_pos⟩
  have hψ'σ : ∀ i, ψ' (σ.symm i) = ψ i := by
    intro i
    simp [ψ', (σ.symm i).isLt]
  have hψ'mono : ∀ s t, s ≤ t → t < (2 * j) → ψ' s ≤ ψ' t := by
    intro s t hst ht
    have hs' : s < (2 * j) := by omega
    simp only [ψ', hs', ht, ↓reduceDIte]
    exact Tuple.monotone_sort ψ (show (⟨s, hs'⟩ : Fin (2 * j)) ≤ ⟨t, ht⟩ from hst)
  have hφlo : ∀ s < (2 * j), φ s = ψ' s := fun s hs ↦ by simp [φ, hs]
  have hφhi : ∀ s, φ (s + (2 * j)) = ψ' s + π := fun s ↦ by simp [φ]
  have hφr : ∀ s, 0 ≤ φ s ∧ φ s < 2 * π := by
    intro s
    simp only [φ]
    split_ifs
    · exact ⟨(hψ'r s).1, by linarith [(hψ'r s).2, pi_pos]⟩
    · constructor <;> linarith [hψ'r (s - (2 * j)), pi_pos]
  have hmono : ∀ s t, s ≤ t → t < 2 * (2 * j) → φ s ≤ φ t := by
    intro s t hst ht
    by_cases htm : t < (2 * j)
    · rw [hφlo s (by omega), hφlo t htm]
      exact hψ'mono s t hst htm
    · obtain ⟨t', rfl⟩ : ∃ t', t = t' + (2 * j) := ⟨t - (2 * j), by omega⟩
      rw [hφhi]
      by_cases hsm : s < (2 * j)
      · rw [hφlo s hsm]
        linarith [hψ'r s, hψ'r t']
      · obtain ⟨s', rfl⟩ : ∃ s', s = s' + (2 * j) := ⟨s - (2 * j), by omega⟩
        rw [hφhi]
        linarith [hψ'mono s' t' (by omega) (by omega)]
  have hwrap : ∀ s t, s < 2 * (2 * j) → t < 2 * (2 * j) → φ t ≤ φ s + 2 * π := fun s t _ _ ↦ by
    linarith [hφr s, hφr t]
  let ι : Fin (2 * j) ⊕ Fin (2 * j) → ℕ :=
    Sum.elim (fun i ↦ (σ.symm i).val + if π ≤ a i then (2 * j) else 0)
      (fun i ↦ (σ.symm i).val + if π ≤ a i then 0 else (2 * j))
  have hιN : ∀ c, ι c < 2 * (2 * j) := by
    rintro (i | i) <;> simp only [ι, Sum.elim_inl, Sum.elim_inr] <;>
      have := (σ.symm i).isLt <;> split_ifs <;> omega
  have hι : Function.Injective ι := by
    have key : ∀ i i' : Fin (2 * j), ((σ.symm i).val = (σ.symm i').val) → i = i' := fun i i' h ↦
      σ.symm.injective (Fin.ext h)
    rintro (i | i) (i' | i') h <;> simp only [ι, Sum.elim_inl, Sum.elim_inr] at h <;>
      have h1 := (σ.symm i).isLt <;> have h2 := (σ.symm i').isLt
    · congr 1
      apply key
      split_ifs at h <;> omega
    · exfalso
      have : i = i' := by apply key; split_ifs at h <;> omega
      subst this
      split_ifs at h <;> omega
    · exfalso
      have : i = i' := by apply key; split_ifs at h <;> omega
      subst this
      split_ifs at h <;> omega
    · congr 1
      apply key
      split_ifs at h <;> omega
  have hdirneg : ∀ θ, dir (θ - π) = -dir θ := fun θ ↦ by
    have := dir_add_pi (θ - π)
    rw [sub_add_cancel] at this
    rw [this, neg_neg]
  have hdir : ∀ c, dir (φ (ι c)) = dir (Sum.elim p (fun i ↦ p i + π) c) := by
    rintro (i | i)
    · simp only [ι, Sum.elim_inl]
      split_ifs with h
      · rw [hφhi, hψ'σ]
        simp only [ψ, h, ↓reduceIte, sub_add_cancel, a, dir_toIcoMod]
      · rw [add_zero, hφlo _ (σ.symm i).isLt, hψ'σ]
        simp only [ψ, h, ↓reduceIte, a, dir_toIcoMod]
    · simp only [ι, Sum.elim_inr, dir_add_pi]
      split_ifs with h
      · rw [add_zero, hφlo _ (σ.symm i).isLt, hψ'σ]
        simp only [ψ, h, ↓reduceIte, hdirneg, a, dir_toIcoMod]
      · rw [hφhi, hψ'σ]
        simp only [ψ, h, ↓reduceIte, a, dir_add_pi, dir_toIcoMod]
  have hvol := volume_alternate_add_le hK hne hmono hwrap p (fun i ↦ p i + π) ι hιN hι hdir
  rw [volume_circPolygon_add_pi hsymm] at hvol
  have hpar : ∀ r < 2, circPolygon K (fun i : Fin (2 * j) ↦ φ (2 * i + r)) =
      circPolygon K (Sum.elim (fun i : Fin j ↦ ψ' (2 * i + r))
        fun i : Fin j ↦ ψ' (2 * i + r) + π) := by
    intro r hr
    ext x
    simp only [mem_circPolygon_iff, Sum.forall, Sum.elim_inl, Sum.elim_inr]
    constructor
    · intro h
      refine ⟨fun i ↦ ?_, fun i ↦ ?_⟩
      · have := i.isLt
        have := h ⟨i, by omega⟩
        simp only at this
        rwa [hφlo _ (by omega)] at this
      · have := i.isLt
        have := h ⟨i + j, by omega⟩
        simp only at this
        rwa [show 2 * (i + j : ℕ) + r = (2 * i + r) + (2 * j) by omega, hφhi] at this
    · rintro ⟨h1, h2⟩ i
      by_cases hi : (i : ℕ) < j
      · have := h1 ⟨i, hi⟩
        simp only at this
        rwa [hφlo _ (by omega)]
      · have := i.isLt
        have := h2 ⟨(i : ℕ) - j, by omega⟩
        simp only at this
        rwa [show 2 * (i : ℕ) + r = (2 * (i - j : ℕ) + r) + (2 * j) by omega, hφhi]
  have hX := hpar 0 (by norm_num)
  have hY := hpar 1 (by norm_num)
  simp only [add_zero] at hX
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  have h1 := hcon (fun i ↦ ψ' (2 * i))
  have h2 := hcon (fun i ↦ ψ' (2 * i + 1))
  rw [← hX] at h1
  rw [← hY] at h2
  exact absurd hvol (not_le.2 (ENNReal.add_lt_add h1 h2))

/-! ### Monotonicity, finiteness and the supporting line of `k ↦ t_K(k)` at `6` -/

theorem minCircumscribedArea_succ_le (k : ℕ) :
    minCircumscribedArea K (k + 1) ≤ minCircumscribedArea K k := by
  refine le_iInf fun a ↦ le_iInf fun c ↦ le_iInf fun h ↦ ?_
  have : halfPlanesInter (Fin.cons 0 a : Fin (k + 1) → Fin 2 → ℝ) (Fin.cons 0 c) =
      halfPlanesInter a c := by
    ext x
    simp [halfPlanesInter, Fin.forall_fin_succ]
  rw [← this]
  exact minCircumscribedArea_le (this ▸ h)

theorem antitone_minCircumscribedArea : Antitone (minCircumscribedArea K) :=
  antitone_nat_of_succ_le minCircumscribedArea_succ_le

/-- `t_K(k) < ∞` for `k ≥ 4` (a circumscribed rectangle). -/
theorem minCircumscribedArea_lt_top (hK : IsCompact K) {k : ℕ} (hk : 4 ≤ k) :
    minCircumscribedArea K k < ∞ := by
  let θ : Fin k → ℝ := fun i ↦ (i : ℝ) * (π / 2)
  refine (minCircumscribedArea_le_circPolygon hK θ).trans_lt ?_
  let lo : Fin 2 → ℝ := ![-supportFun K (dir π), -supportFun K (dir (3 * (π / 2)))]
  let hi : Fin 2 → ℝ := ![supportFun K (dir 0), supportFun K (dir (π / 2))]
  have hsub : circPolygon K θ ⊆ Icc lo hi := by
    intro x hx
    have h0 := hx ⟨0, by omega⟩
    have h1 := hx ⟨1, by omega⟩
    have h2 := hx ⟨2, by omega⟩
    have h3 := hx ⟨3, by omega⟩
    simp only [θ, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, zero_mul, one_mul] at h0 h1 h2 h3
    rw [show (2 : ℝ) * (π / 2) = π by ring] at h2
    have hd3 : dir (3 * (π / 2)) = ![0, -1] := by
      rw [show 3 * (π / 2) = π / 2 + π by ring, dir_add_pi]
      ext i; fin_cases i <;> simp [dir]
    rw [dir_dotProduct] at h0 h1 h2
    rw [hd3] at h3
    simp [dotProduct, Fin.sum_univ_two] at h3
    simp at h0 h1 h2
    refine ⟨fun i ↦ ?_, fun i ↦ ?_⟩ <;> fin_cases i <;> simp [lo, hi, hd3] <;> linarith
  exact (measure_mono hsub).trans_lt measure_Icc_lt_top

/-- Convexity of a real sequence gives the supporting line at `6`. -/
theorem convex_seq_six_add_le (g : ℕ → ℝ) {a : ℕ} (ha : a ≤ 6)
    (hconv : ∀ k, a < k → g k + g k ≤ g (k - 1) + g (k + 1)) {s : ℕ} (hs : a ≤ s) :
    g 6 + 6 * (g 6 - g 7) ≤ g s + s * (g 6 - g 7) := by
  set D := g 6 - g 7
  have hsl : ∀ k, a ≤ k → g (k + 1) - g k ≤ g (k + 2) - g (k + 1) := by
    intro k hk
    have := hconv (k + 1) (by omega)
    simp only [Nat.add_sub_cancel] at this
    linarith
  rcases le_or_gt 6 s with h6 | h6
  · induction s, h6 using Nat.le_induction with
    | base => simp
    | succ s hs6 ih =>
      have hup : ∀ n, g 7 - g 6 ≤ g (n + 7) - g (n + 6) := by
        intro n
        induction n with
        | zero => simp
        | succ n ihn =>
          have := hsl (n + 6) (by omega)
          rw [show n + 6 + 2 = (n + 1) + 7 by omega, show n + 6 + 1 = n + 7 by omega] at this
          rw [show (n + 1) + 6 = n + 7 by omega]
          linarith
      obtain ⟨n, rfl⟩ : ∃ n, s = n + 6 := ⟨s - 6, by omega⟩
      have := hup n
      have ih' := ih (by omega)
      rw [show n + 6 + 1 = n + 7 by omega]
      push_cast at ih' ⊢
      linarith
  · have hdown : ∀ n, ∀ t, a ≤ t → t + n = 6 →
        g (t + 1) - g t ≤ -D ∧ g 6 + 6 * D ≤ g t + t * D := by
      intro n
      induction n with
      | zero =>
        intro t _ ht
        subst ht
        have := hsl 6 (by omega)
        simp only [D]
        constructor <;> push_cast <;> linarith
      | succ n ihn =>
        intro t hat ht
        have := ihn (t + 1) (by omega) (by omega)
        have hs' := hsl t hat
        refine ⟨by linarith [this.1], ?_⟩
        have h2 := this.2
        push_cast at h2 ⊢
        linarith [this.1]
    exact (hdown (6 - s) s hs (by omega)).2

/-- **The supporting line of `t_K` at `6`.** With `d = t_K(6) - t_K(7)`,
`t_K(6) + 6d ≤ t_K(s) + s d` for every `s ≥ 3` (convexity of `t_K`, Dowker). -/
theorem minCircumscribedArea_six_add_le (hK : IsCompact K) (hne : K.Nonempty) {s : ℕ}
    (hs : 3 ≤ s) :
    minCircumscribedArea K 6 + 6 * (minCircumscribedArea K 6 - minCircumscribedArea K 7) ≤
      minCircumscribedArea K s + s * (minCircumscribedArea K 6 - minCircumscribedArea K 7) := by
  set t := minCircumscribedArea K
  set g : ℕ → ℝ := fun k ↦ (t k).toReal
  have hfin : ∀ k, 4 ≤ k → t k ≠ ∞ := fun k hk ↦ (minCircumscribedArea_lt_top hK hk).ne
  have hofReal : ∀ k, 4 ≤ k → t k = ENNReal.ofReal (g k) := fun k hk ↦
    (ENNReal.ofReal_toReal (hfin k hk)).symm
  have hdow : ∀ k, 1 ≤ k → t k + t k ≤ t (k - 1) + t (k + 1) := fun k hk ↦
    minCircumscribedArea_add_le hK hne (by omega)
  have hconvR : ∀ k, 4 ≤ k → t (k - 1) ≠ ∞ → g k + g k ≤ g (k - 1) + g (k + 1) := by
    intro k hk hk1
    have h := hdow k (by omega)
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hk1, hfin _ (by omega)⟩) h
    rwa [ENNReal.toReal_add (hfin _ (by omega)) (hfin _ (by omega)),
      ENNReal.toReal_add hk1 (hfin _ (by omega))] at this
  have hg0 : ∀ k, 0 ≤ g k := fun k ↦ ENNReal.toReal_nonneg
  have h76 : t 7 ≤ t 6 := antitone_minCircumscribedArea (by norm_num)
  have hD : t 6 - t 7 = ENNReal.ofReal (g 6 - g 7) := by
    rw [ENNReal.ofReal_sub _ (hg0 7), ← hofReal 6 (by norm_num), ← hofReal 7 (by norm_num)]
  have hD0 : 0 ≤ g 6 - g 7 := by
    have := ENNReal.toReal_mono (hfin 6 (by norm_num)) h76
    simp only [g]
    linarith
  -- the real inequality for `s ≥ 4`, or for `s ≥ 3` if `t 3 < ∞`
  have key : ∀ a, 3 ≤ a → a ≤ 4 → a ≤ s → (∀ k, a ≤ k → t k ≠ ∞) →
      t 6 + 6 * (t 6 - t 7) ≤ t s + s * (t 6 - t 7) := by
    intro a ha3 ha4 has hfa
    have hreal := convex_seq_six_add_le g (a := a) (by omega)
      (fun k hk ↦ hconvR k (by omega) (hfa _ (by omega))) has
    have hts : t s = ENNReal.ofReal (g s) := (ENNReal.ofReal_toReal (hfa s has)).symm
    rw [hD, hts, hofReal 6 (by norm_num), ← ENNReal.ofReal_natCast s,
      show (6 : ℝ≥0∞) = ENNReal.ofReal 6 by simp, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (hg0 6) (by positivity),
      ← ENNReal.ofReal_add (hg0 s) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  by_cases h3 : t 3 = ∞
  · rcases (show s = 3 ∨ 4 ≤ s by omega) with rfl | hs4
    · simp [h3]
    · exact key 4 (by norm_num) le_rfl hs4 hfin
  · exact key 3 le_rfl (by norm_num) hs fun k hk ↦ by
      rcases (show k = 3 ∨ 4 ≤ k by omega) with rfl | hk4
      · exact h3
      · exact hfin k hk4

end MinArea

/-! ### Invariance under Euclidean motions -/

section Motion

open Matrix

variable {K : Set (Fin 2 → ℝ)}

theorem orthogonal_dotProduct_mulVec {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A ∈ Matrix.orthogonalGroup (Fin 2) ℝ) (u v : Fin 2 → ℝ) :
    (A *ᵥ u) ⬝ᵥ (A *ᵥ v) = u ⬝ᵥ v := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul,
    (Matrix.mem_orthogonalGroup_iff' _ _).1 hA, Matrix.vecMul_one]

theorem abs_det_orthogonal {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A ∈ Matrix.orthogonalGroup (Fin 2) ℝ) : |A.det| = 1 := by
  have h := congrArg Matrix.det ((Matrix.mem_orthogonalGroup_iff' _ _).1 hA)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  have : |A.det| * |A.det| = 1 := by rw [← abs_mul, h, abs_one]
  nlinarith [abs_nonneg A.det]

/-- Euclidean motions preserve area. -/
theorem volume_image_motion {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A ∈ Matrix.orthogonalGroup (Fin 2) ℝ) (b : Fin 2 → ℝ) (S : Set (Fin 2 → ℝ)) :
    volume ((fun x ↦ A *ᵥ x + b) '' S) = volume S := by
  have : (fun x ↦ A *ᵥ x + b) '' S = (fun x ↦ x + b) '' (Matrix.toLin' A '' S) := by
    rw [image_image]
    rfl
  rw [this, image_add_right, measure_preimage_add_right, Measure.addHaar_image_linearMap,
    LinearMap.det_toLin', abs_det_orthogonal hA, ENNReal.ofReal_one, one_mul]

theorem image_motion_halfPlanesInter {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A ∈ Matrix.orthogonalGroup (Fin 2) ℝ) (b : Fin 2 → ℝ) {ι : Type*}
    (a : ι → Fin 2 → ℝ) (c : ι → ℝ) :
    (fun x ↦ A *ᵥ x + b) '' halfPlanesInter a c =
      halfPlanesInter (fun i ↦ A *ᵥ a i) (fun i ↦ c i + (A *ᵥ a i) ⬝ᵥ b) := by
  have hAAt : A * A.transpose = 1 := (Matrix.mem_orthogonalGroup_iff _ _).1 hA
  ext x
  simp only [mem_image, halfPlanesInter, mem_ofPred_eq]
  constructor
  · rintro ⟨y, hy, rfl⟩ i
    rw [dotProduct_add, orthogonal_dotProduct_mulVec hA]
    linarith [hy i]
  · intro hx
    refine ⟨A.transpose *ᵥ (x - b), fun i ↦ ?_, ?_⟩
    · have := hx i
      rw [← orthogonal_dotProduct_mulVec hA, Matrix.mulVec_mulVec, hAAt, Matrix.one_mulVec,
        dotProduct_sub]
      linarith
    · rw [Matrix.mulVec_mulVec, hAAt, Matrix.one_mulVec, sub_add_cancel]

theorem minCircumscribedArea_image_motion_le {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A ∈ Matrix.orthogonalGroup (Fin 2) ℝ) (b : Fin 2 → ℝ) (k : ℕ) :
    minCircumscribedArea ((fun x ↦ A *ᵥ x + b) '' K) k ≤ minCircumscribedArea K k := by
  refine le_iInf fun a ↦ le_iInf fun c ↦ le_iInf fun h ↦ ?_
  rw [← volume_image_motion hA b, image_motion_halfPlanesInter hA]
  apply minCircumscribedArea_le
  rw [← image_motion_halfPlanesInter hA]
  exact image_mono h

/-- `t_K(k)` is invariant under Euclidean motions `x ↦ A x + b`, `A` orthogonal. -/
theorem minCircumscribedArea_image_motion {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A ∈ Matrix.orthogonalGroup (Fin 2) ℝ) (b : Fin 2 → ℝ) (k : ℕ) :
    minCircumscribedArea ((fun x ↦ A *ᵥ x + b) '' K) k = minCircumscribedArea K k := by
  refine le_antisymm (minCircumscribedArea_image_motion_le hA b k) ?_
  have hAt : A.transpose ∈ Matrix.orthogonalGroup (Fin 2) ℝ :=
    (Matrix.mem_orthogonalGroup_iff _ _).2
      (by rw [Matrix.transpose_transpose]; exact (Matrix.mem_orthogonalGroup_iff' _ _).1 hA)
  have hinv : (fun x ↦ A.transpose *ᵥ x + -(A.transpose *ᵥ b)) ''
      ((fun x ↦ A *ᵥ x + b) '' K) = K := by
    rw [image_image]
    convert image_id K using 2
    ext x
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, (Matrix.mem_orthogonalGroup_iff' _ _).1 hA,
      Matrix.one_mulVec]
    simp
  calc minCircumscribedArea K k =
        minCircumscribedArea ((fun x ↦ A.transpose *ᵥ x + -(A.transpose *ᵥ b)) ''
          ((fun x ↦ A *ᵥ x + b) '' K)) k := by rw [hinv]
    _ ≤ _ := minCircumscribedArea_image_motion_le hAt _ k

end Motion

end PlaneConvex
