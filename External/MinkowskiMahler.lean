module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Critical lattices of a symmetric convex domain (Minkowski, Mahler)

Cited as Theorem 2.3.6 of Hales–Vajjha, *Packings of Smoothed Polygons*, from H. Minkowski,
*Diophantische Approximationen*, Teubner, 1907, and K. Mahler, *Lattice points in n-dimensional
star bodies II*, Proc. Kon. Ned. Akad. Wet. 49 (1946), 331–343: a critical lattice `Λ` of a
symmetric convex domain `K` has three points `P₀, P₁, P₂` on the boundary of `K` with
`P₁ = P₀ + P₂` such that `P₀, P₁` is a basis of `Λ`, so that `d(Λ) = |det(P₀, P₁)| = Δ(K)`;
conversely, for any three boundary points with `P₁ = P₀ + P₂`, `|det(P₀, P₁)| ≥ Δ(K)`, with
equality exactly when the lattice with basis `P₀, P₁` is critical.

Definitions, in the terms of the sources. The plane is `Fin 2 → ℝ`. A symmetric convex domain is a
compact convex set with nonempty interior, symmetric about the origin `O`. A lattice `Λ` is a
discrete subgroup of `ℝ²` spanning `ℝ²`; its determinant `d(Λ)` is the area of a fundamental
parallelogram (Mathlib's covolume, equal to `|det(a, b)|` for every basis `a, b`). `Λ` is
`K`-admissible if `O` is its only point in the interior of `K`; `Δ(K)` is the infimum of `d(Λ)`
over the `K`-admissible lattices, and a critical lattice is a `K`-admissible lattice with
`d(Λ) = Δ(K)`. These definitions are shared with `External.Mahler1947`.

Proof. Mahler (1947, Lemma 2) quotes the result from his paper A (Lemma 3), which goes back to
Minkowski; we give the classical argument. The converse is Mahler's Lemma 1 ("obvious from the
convexity"): if `P₀, P₂, P₀ + P₂` are boundary points, a support functional `f` at `P₀ + P₂` has
`f(i P₀ + j P₂) ≥ 1` for integers `i, j ≥ 1`, so the lattice with basis `P₀, P₀ + P₂` is
admissible (`mm_isAdmissible`) and its determinant `|det(P₀, P₁)|` is at least `Δ(K)`. For the
direct part, a critical lattice cannot be deformed into admissible lattices of smaller determinant
(`mm_deform`); this gives in turn a lattice point on the boundary (`mm_exists_mem`, shrinking the
lattice), a second independent one (`mm_exists_indep`, compressing transversally), a basis `a, b`
on the boundary (`mm_exists_pair`, a pair of least `|det|`), and finally `a + b` or `a - b` on
the boundary (`mm_add_or_sub_mem`, turning `a` and `b` along their support lines).
-/

@[expose] public section

namespace External

namespace MinkowskiMahler

open Set Filter Topology

/-- The determinant `det(u, v) = u₀v₁ - u₁v₀` of two vectors of the plane. -/
def cross (u v : Fin 2 → ℝ) : ℝ := u 0 * v 1 - u 1 * v 0

/-- A symmetric convex domain: a compact convex set with nonempty interior, symmetric about the
origin. -/
def IsSymmetricConvexDomain (K : Set (Fin 2 → ℝ)) : Prop :=
  Convex ℝ K ∧ IsCompact K ∧ (interior K).Nonempty ∧ ∀ x ∈ K, -x ∈ K

/-- A lattice: a discrete subgroup of `ℝ²` that spans `ℝ²`. -/
def IsLattice (Λ : Submodule ℤ (Fin 2 → ℝ)) : Prop :=
  DiscreteTopology Λ ∧ Submodule.span ℝ (Λ : Set (Fin 2 → ℝ)) = ⊤

/-- The determinant `d(Λ)` of a lattice: the area of a fundamental parallelogram. -/
noncomputable def det (Λ : Submodule ℤ (Fin 2 → ℝ)) : ℝ := ZLattice.covolume Λ

/-- `a, b` is a basis of the lattice `Λ`. -/
def IsBasis (Λ : Submodule ℤ (Fin 2 → ℝ)) (a b : Fin 2 → ℝ) : Prop :=
  LinearIndependent ℤ ![a, b] ∧ Submodule.span ℤ {a, b} = Λ

/-- `Λ` is `K`-admissible: the origin is the only point of `Λ` in the interior of `K`. -/
def IsAdmissible (K : Set (Fin 2 → ℝ)) (Λ : Submodule ℤ (Fin 2 → ℝ)) : Prop :=
  ∀ x ∈ Λ, x ∈ interior K → x = 0

/-- The minimal determinant `Δ(K)`: the infimum of `d(Λ)` over the `K`-admissible lattices. -/
noncomputable def minimalDeterminant (K : Set (Fin 2 → ℝ)) : ℝ :=
  sInf {d | ∃ Λ, IsLattice Λ ∧ IsAdmissible K Λ ∧ det Λ = d}

/-- A critical lattice of `K`: a `K`-admissible lattice with `d(Λ) = Δ(K)`. -/
def IsCritical (K : Set (Fin 2 → ℝ)) (Λ : Submodule ℤ (Fin 2 → ℝ)) : Prop :=
  IsLattice Λ ∧ IsAdmissible K Λ ∧ det Λ = minimalDeterminant K

/-! ### Algebra of `cross` and of lattices with a basis -/

lemma mm_cross_comb (s t s' t' : ℝ) (u v : Fin 2 → ℝ) :
    cross (s • u + t • v) (s' • u + t' • v) = (s * t' - t * s') * cross u v := by
  simp only [cross, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

lemma mm_cross_smul_add (s t : ℝ) (u v w : Fin 2 → ℝ) :
    cross (s • u + t • v) w = s * cross u w + t * cross v w := by
  simp only [cross, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

lemma mm_cross_add_smul (s t : ℝ) (u v w : Fin 2 → ℝ) :
    cross w (s • u + t • v) = s * cross w u + t * cross w v := by
  simp only [cross, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

lemma mm_cross_self (u : Fin 2 → ℝ) : cross u u = 0 := by
  simp only [cross]; ring

lemma mm_cross_swap (u v : Fin 2 → ℝ) : cross v u = -cross u v := by
  simp only [cross]; ring

/-- Cramer's rule: `cross(u, v) x = cross(x, v) u + cross(u, x) v`. -/
lemma mm_cramer (u v x : Fin 2 → ℝ) :
    cross u v • x = cross x v • u + cross u x • v := by
  ext i; fin_cases i <;> simp [cross] <;> ring

lemma mm_eq_comb {u v : Fin 2 → ℝ} (h : cross u v ≠ 0) (x : Fin 2 → ℝ) :
    x = (cross x v / cross u v) • u + (cross u x / cross u v) • v := by
  have := mm_cramer u v x
  calc x = (cross u v)⁻¹ • (cross u v • x) := by rw [smul_smul, inv_mul_cancel₀ h, one_smul]
    _ = _ := by rw [this, smul_add, smul_smul, smul_smul, div_eq_inv_mul, div_eq_inv_mul]

lemma mm_mem_span_pair {a b x : Fin 2 → ℝ} :
    x ∈ Submodule.span ℤ {a, b} ↔ ∃ m n : ℤ, (m : ℝ) • a + (n : ℝ) • b = x := by
  rw [Submodule.mem_span_pair]
  simp only [← Int.cast_smul_eq_zsmul ℝ]

lemma mm_linearIndependent {a b : Fin 2 → ℝ} (h : cross a b ≠ 0) :
    LinearIndependent ℤ ![a, b] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  simp only [← Int.cast_smul_eq_zsmul ℝ] at hst
  have h1 := congrArg (fun x ↦ cross x b) hst
  have h2 := congrArg (fun x ↦ cross a x) hst
  simp only [mm_cross_smul_add, mm_cross_add_smul, mm_cross_self] at h1 h2
  simp only [cross, Pi.zero_apply, mul_zero, sub_zero] at h1 h2
  constructor
  · have : (s : ℝ) * cross a b = 0 := by simp only [cross]; linarith
    exact_mod_cast (mul_eq_zero.1 this).resolve_right h
  · have : (t : ℝ) * cross a b = 0 := by simp only [cross]; linarith
    exact_mod_cast (mul_eq_zero.1 this).resolve_right h

lemma mm_linearIndependent_real {a b : Fin 2 → ℝ} (h : cross a b ≠ 0) :
    LinearIndependent ℝ ![a, b] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h1 := congrArg (fun x ↦ cross x b) hst
  have h2 := congrArg (fun x ↦ cross a x) hst
  simp only [mm_cross_smul_add, mm_cross_add_smul, mm_cross_self] at h1 h2
  simp only [cross, Pi.zero_apply, mul_zero, sub_zero] at h1 h2
  constructor
  · have : s * cross a b = 0 := by simp only [cross]; linarith
    exact (mul_eq_zero.1 this).resolve_right h
  · have : t * cross a b = 0 := by simp only [cross]; linarith
    exact (mul_eq_zero.1 this).resolve_right h

lemma mm_range_pair (a b : Fin 2 → ℝ) : Set.range ![a, b] = {a, b} := by
  rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.singleton_union]

/-- The determinant of a lattice with a basis `a, b` is `|cross(a, b)|`. -/
lemma mm_det_eq {Λ : Submodule ℤ (Fin 2 → ℝ)} (hΛ : IsLattice Λ) {a b : Fin 2 → ℝ}
    (hab : IsBasis Λ a b) : det Λ = |cross a b| := by
  obtain ⟨hd, hs⟩ := hΛ
  have : IsZLattice ℝ Λ := ⟨hs⟩
  obtain ⟨hli, hspan⟩ := hab
  have heq : Submodule.span ℤ (Set.range ![a, b]) = Λ := by rw [mm_range_pair]; exact hspan
  let bas : Module.Basis (Fin 2) ℤ Λ := (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ heq)
  have hb : (Subtype.val ∘ ⇑bas) = ![a, b] := by
    ext i : 1
    simp [bas, Module.Basis.span_apply]
  rw [det, ZLattice.covolume_eq_det Λ bas, hb, Matrix.det_fin_two]
  simp [cross]

/-- Two vectors with `cross(a, b) ≠ 0` span a lattice. -/
lemma mm_isLattice_span {a b : Fin 2 → ℝ} (h : cross a b ≠ 0) :
    IsLattice (Submodule.span ℤ {a, b}) := by
  have hli := mm_linearIndependent_real h
  have hcard : Fintype.card (Fin 2) = Module.finrank ℝ (Fin 2 → ℝ) := by simp
  let bR : Module.Basis (Fin 2) ℝ (Fin 2 → ℝ) := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hbR : Submodule.span ℤ (Set.range bR) = Submodule.span ℤ {a, b} := by
    rw [coe_basisOfLinearIndependentOfCardEqFinrank, mm_range_pair]
  rw [← hbR]
  exact ⟨inferInstance, IsZLattice.span_top⟩

lemma mm_isBasis_span {a b : Fin 2 → ℝ} (h : cross a b ≠ 0) :
    IsBasis (Submodule.span ℤ {a, b}) a b :=
  ⟨mm_linearIndependent h, rfl⟩

lemma mm_det_span {a b : Fin 2 → ℝ} (h : cross a b ≠ 0) :
    det (Submodule.span ℤ {a, b}) = |cross a b| :=
  mm_det_eq (mm_isLattice_span h) (mm_isBasis_span h)

/-- Every lattice has a basis. -/
lemma mm_exists_basis {Λ : Submodule ℤ (Fin 2 → ℝ)} (hΛ : IsLattice Λ) :
    ∃ a b, IsBasis Λ a b ∧ cross a b ≠ 0 := by
  obtain ⟨hd, hs⟩ := hΛ
  have : IsZLattice ℝ Λ := ⟨hs⟩
  have hrank : Module.finrank ℤ Λ = 2 := by rw [ZLattice.rank ℝ Λ]; simp
  let bZ : Module.Basis (Fin 2) ℤ Λ := Module.finBasisOfFinrankEq ℤ Λ hrank
  let bR : Module.Basis (Fin 2) ℝ (Fin 2 → ℝ) := bZ.ofZLatticeBasis ℝ Λ
  have hfun : ⇑bR = ![bR 0, bR 1] := by
    ext i : 1
    fin_cases i <;> rfl
  have hli : LinearIndependent ℤ ![bR 0, bR 1] := by
    rw [← hfun]
    exact bR.linearIndependent.restrict_scalars' ℤ
  have hspan : Submodule.span ℤ {bR 0, bR 1} = Λ := by
    rw [← mm_range_pair, ← hfun]
    exact bZ.ofZLatticeBasis_span ℝ Λ
  have hb : IsBasis Λ (bR 0) (bR 1) := ⟨hli, hspan⟩
  refine ⟨_, _, hb, fun h0 ↦ ?_⟩
  have hdet := mm_det_eq ⟨hd, hs⟩ hb
  rw [h0, abs_zero, det] at hdet
  exact (ZLattice.covolume_pos Λ).ne' hdet

/-! ### Symmetric convex domains -/

section Domain

variable {K : Set (Fin 2 → ℝ)}

lemma mm_isClosed (hK : IsSymmetricConvexDomain K) : IsClosed K := hK.2.1.isClosed

lemma mm_neg_mem_interior (hK : IsSymmetricConvexDomain K) {x : Fin 2 → ℝ}
    (hx : x ∈ interior K) : -x ∈ interior K := by
  have hsub : -interior K ⊆ K := fun y hy ↦ by
    have := hK.2.2.2 _ (interior_subset (Set.mem_neg.1 hy))
    rwa [neg_neg] at this
  exact interior_maximal hsub isOpen_interior.neg (Set.neg_mem_neg.2 hx)

lemma mm_zero_mem_interior (hK : IsSymmetricConvexDomain K) : (0 : Fin 2 → ℝ) ∈ interior K := by
  obtain ⟨p, hp⟩ := hK.2.2.1
  have h := hK.1.interior.add_smul_sub_mem hp (mm_neg_mem_interior hK hp)
    (t := 1 / 2) (by norm_num)
  convert h using 1
  ext i; simp; ring

lemma mm_mem_of_frontier (hK : IsSymmetricConvexDomain K) {x : Fin 2 → ℝ}
    (hx : x ∈ frontier K) : x ∈ K := by
  rw [(mm_isClosed hK).frontier_eq] at hx; exact hx.1

lemma mm_not_mem_interior_of_frontier {x : Fin 2 → ℝ} (hx : x ∈ frontier K) :
    x ∉ interior K := hx.2

lemma mm_mem_frontier (hK : IsSymmetricConvexDomain K) {x : Fin 2 → ℝ} (hx : x ∈ K)
    (hx' : x ∉ interior K) : x ∈ frontier K := by
  rw [(mm_isClosed hK).frontier_eq]; exact ⟨hx, hx'⟩

lemma mm_neg_mem_frontier (hK : IsSymmetricConvexDomain K) {x : Fin 2 → ℝ}
    (hx : x ∈ frontier K) : -x ∈ frontier K := by
  refine mm_mem_frontier hK (hK.2.2.2 _ (mm_mem_of_frontier hK hx)) fun h ↦ hx.2 ?_
  have := mm_neg_mem_interior hK h
  rwa [neg_neg] at this

lemma mm_ne_zero_of_frontier (hK : IsSymmetricConvexDomain K) {x : Fin 2 → ℝ}
    (hx : x ∈ frontier K) : x ≠ 0 := by
  rintro rfl; exact hx.2 (mm_zero_mem_interior hK)

/-- `t x ∈ int K` for `x ∈ K` and `0 ≤ t < 1`. -/
lemma mm_smul_mem_interior (hK : IsSymmetricConvexDomain K) {x : Fin 2 → ℝ} (hx : x ∈ K)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) : t • x ∈ interior K := by
  have := hK.1.combo_interior_self_mem_interior (mm_zero_mem_interior hK) hx
    (a := 1 - t) (b := t) (by linarith) ht0 (by ring)
  simpa using this

/-- `α a + β b ∈ int K` for `a, b ∈ K`, `α, β ≥ 0`, `α + β < 1`. -/
lemma mm_comb_mem_interior (hK : IsSymmetricConvexDomain K) {a b : Fin 2 → ℝ} (ha : a ∈ K)
    (hb : b ∈ K) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β < 1) :
    α • a + β • b ∈ interior K := by
  rcases (add_nonneg hα hβ).eq_or_lt with h | h
  · have h1 : α = 0 := by linarith
    have h2 : β = 0 := by linarith
    simpa [h1, h2] using mm_zero_mem_interior hK
  · have hz : (α / (α + β)) • a + (β / (α + β)) • b ∈ K :=
      hK.1 ha hb (div_nonneg hα h.le) (div_nonneg hβ h.le) (by field_simp)
    have := mm_smul_mem_interior hK hz h.le hαβ
    convert this using 1
    rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ h.ne', mul_div_cancel₀ _ h.ne']

/-- `α a + β b ∈ K` for `a, b ∈ K`, `α, β ≥ 0`, `α + β ≤ 1`. -/
lemma mm_comb_mem (hK : IsSymmetricConvexDomain K) {a b : Fin 2 → ℝ} (ha : a ∈ K)
    (hb : b ∈ K) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β ≤ 1) :
    α • a + β • b ∈ K := by
  rcases hαβ.lt_or_eq with h | h
  · exact interior_subset (mm_comb_mem_interior hK ha hb hα hβ h)
  · exact hK.1 ha hb hα hβ h

/-- On the ray of a boundary point `x`, the points `t x` with `t ≥ 0` in `K` have `t ≤ 1`. -/
lemma mm_le_one_of_smul_mem (hK : IsSymmetricConvexDomain K) {x : Fin 2 → ℝ}
    (hx : x ∈ frontier K) {t : ℝ} (ht : 0 ≤ t) (htx : t • x ∈ K) : t ≤ 1 := by
  by_contra h
  push Not at h
  have := mm_smul_mem_interior hK htx (t := t⁻¹) (inv_nonneg.2 ht) (inv_lt_one_of_one_lt₀ h)
  rw [smul_smul, inv_mul_cancel₀ (by linarith), one_smul] at this
  exact hx.2 this

/-- A support functional at a boundary point `x`: `f x = 1`, `f ≤ 1` on `K`, `f < 1` on the
interior. -/
lemma mm_support (hK : IsSymmetricConvexDomain K) {x : Fin 2 → ℝ} (hx : x ∈ frontier K) :
    ∃ f : StrongDual ℝ (Fin 2 → ℝ), f x = 1 ∧ (∀ y ∈ K, f y ≤ 1) ∧
      ∀ y ∈ interior K, f y < 1 := by
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hK.1.interior isOpen_interior hx.2
  have hpos : 0 < f x := by simpa using hf 0 (mm_zero_mem_interior hK)
  refine ⟨(f x)⁻¹ • f, by simp [hpos.ne'], fun y hy ↦ ?_, fun y hy ↦ ?_⟩
  · have hcl : K ⊆ closure (interior K) := by
      rw [hK.1.closure_interior_eq_closure_of_nonempty_interior hK.2.2.1]; exact subset_closure
    have hc : IsClosed {z | ((f x)⁻¹ • f) z ≤ 1} :=
      isClosed_le (by fun_prop) continuous_const
    refine closure_minimal (fun z hz ↦ ?_) hc (hcl hy)
    have := hf z hz
    simp only [Set.mem_ofPred_eq, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [inv_mul_le_iff₀ hpos]; linarith
  · have := hf y hy
    simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [inv_mul_lt_iff₀ hpos]; linarith

lemma mm_bddBelow (K : Set (Fin 2 → ℝ)) :
    BddBelow {d | ∃ Λ, IsLattice Λ ∧ IsAdmissible K Λ ∧ det Λ = d} :=
  ⟨0, fun _ ⟨_, _, _, hd⟩ ↦ hd ▸ ENNReal.toReal_nonneg⟩

lemma mm_minimalDeterminant_le {Λ : Submodule ℤ (Fin 2 → ℝ)} (hΛ : IsLattice Λ)
    (hadm : IsAdmissible K Λ) : minimalDeterminant K ≤ det Λ :=
  csInf_le (mm_bddBelow K) ⟨Λ, hΛ, hadm, rfl⟩

end Domain

/-! ### The converse: Minkowski's lemma (Mahler's Lemma 1) -/

section Converse

variable {K : Set (Fin 2 → ℝ)}

/-- If `u, w, u + w` are boundary points, then `i u + j w` is not an interior point for integers
`i, j ≥ 0` not both zero: a support functional `f` at `u + w` has `f u, f w ≥ 0` and
`f u + f w = 1`, so `f (i u + j w) ≥ 1` when `i, j ≥ 1`; when `j = 0` (or `i = 0`) use a support
functional at `u` (or `w`). -/
lemma mm_three_point (hK : IsSymmetricConvexDomain K) {u w : Fin 2 → ℝ} (hu : u ∈ frontier K)
    (hw : w ∈ frontier K) (huw : u + w ∈ frontier K) {i j : ℤ} (hi : 0 ≤ i) (hj : 0 ≤ j)
    (hij : i ≠ 0 ∨ j ≠ 0) : (i : ℝ) • u + (j : ℝ) • w ∉ interior K := by
  intro hmem
  rcases eq_or_lt_of_le hi with hi0 | hi0
  · obtain ⟨g, hg1, -, hg3⟩ := mm_support hK hw
    have hj1 : (1 : ℝ) ≤ j := by
      have : j ≠ 0 := hij.resolve_left (by omega)
      exact_mod_cast (show (1 : ℤ) ≤ j by omega)
    have := hg3 _ hmem
    rw [← hi0, map_add, map_smul, map_smul, hg1] at this
    simp at this; linarith
  rcases eq_or_lt_of_le hj with hj0 | hj0
  · obtain ⟨g, hg1, -, hg3⟩ := mm_support hK hu
    have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast (show (1 : ℤ) ≤ i by omega)
    have := hg3 _ hmem
    rw [← hj0, map_add, map_smul, map_smul, hg1] at this
    simp at this; linarith
  obtain ⟨f, hf1, hf2, hf3⟩ := mm_support hK huw
  have hfu := hf2 u (mm_mem_of_frontier hK hu)
  have hfw := hf2 w (mm_mem_of_frontier hK hw)
  rw [map_add] at hf1
  have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast (show (1 : ℤ) ≤ i by omega)
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (show (1 : ℤ) ≤ j by omega)
  have := hf3 _ hmem
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at this
  nlinarith

/-- **Mahler's Lemma 1.** If `P₀, P₂, P₁ = P₀ + P₂` are boundary points, the lattice with basis
`P₀, P₁` is `K`-admissible. -/
lemma mm_isAdmissible (hK : IsSymmetricConvexDomain K) {P₀ P₂ : Fin 2 → ℝ}
    (h₀ : P₀ ∈ frontier K) (h₂ : P₂ ∈ frontier K) (h₁ : P₀ + P₂ ∈ frontier K) :
    IsAdmissible K (Submodule.span ℤ {P₀, P₀ + P₂}) := by
  intro x hx hxK
  obtain ⟨m, n, rfl⟩ := mm_mem_span_pair.1 hx
  -- `x = (m + n) P₀ + n P₂`
  have hx' : (m : ℝ) • P₀ + (n : ℝ) • (P₀ + P₂) = ((m + n : ℤ) : ℝ) • P₀ + (n : ℝ) • P₂ := by
    push_cast; module
  rw [hx'] at hxK ⊢
  set a : ℤ := m + n
  by_contra hne
  have hab : a ≠ 0 ∨ n ≠ 0 := by
    by_contra h; push Not at h; apply hne; simp [h.1, h.2]
  have hneg := mm_neg_mem_interior hK hxK
  have hn₂ := mm_neg_mem_frontier hK h₂
  -- the point `P₁ - P₂ = P₀` for the pair `(P₁, -P₂)`
  have h₁' : P₀ + P₂ + -P₂ ∈ frontier K := by simpa using h₀
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 n with hn | hn
  · exact mm_three_point hK h₀ h₂ h₁ ha hn hab hxK
  · -- `a P₀ + n P₂ = a P₁ + (a - n) (-P₂)`
    refine mm_three_point hK h₁ hn₂ h₁' ha (i := a) (j := a - n) (by omega) (by omega) ?_
    convert hxK using 1; push_cast; module
  · refine mm_three_point hK h₁ hn₂ h₁' (i := -a) (j := n - a) (by omega) (by omega)
      (by omega) ?_
    convert hneg using 1; push_cast; module
  · refine mm_three_point hK h₀ h₂ h₁ (i := -a) (j := -n) (by omega) (by omega) (by omega) ?_
    convert hneg using 1; push_cast; module

/-- If `P₀, P₂, P₀ + P₂` are boundary points, then `P₀, P₂` are linearly independent. -/
lemma mm_cross_ne_zero (hK : IsSymmetricConvexDomain K) {P₀ P₂ : Fin 2 → ℝ}
    (h₀ : P₀ ∈ frontier K) (h₂ : P₂ ∈ frontier K) (h₁ : P₀ + P₂ ∈ frontier K) :
    cross P₀ P₂ ≠ 0 := by
  intro hc
  have hP₀ := mm_ne_zero_of_frontier hK h₀
  -- `P₂ = c P₀`
  obtain ⟨c, hc⟩ : ∃ c : ℝ, P₂ = c • P₀ := by
    by_cases h0 : P₀ 0 = 0
    · have h1 : P₀ 1 ≠ 0 := by
        intro h1; apply hP₀; ext i; fin_cases i <;> simp [h0, h1]
      refine ⟨P₂ 1 / P₀ 1, ?_⟩
      ext i; fin_cases i
      · simp only [cross, h0, zero_mul, zero_sub, neg_eq_zero, mul_eq_zero] at hc
        have h20 : P₂ 0 = 0 := hc.resolve_left h1
        simp [h0, h20]
      · simp; field_simp
    · refine ⟨P₂ 0 / P₀ 0, ?_⟩
      ext i; fin_cases i
      · simp; field_simp
      · simp only [cross] at hc
        simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, smul_eq_mul]
        field_simp
        linarith
  subst hc
  rcases le_or_gt 0 c with hc0 | hc0
  · have hle := mm_le_one_of_smul_mem hK h₀ hc0 (mm_mem_of_frontier hK h₂)
    have hge : 1 ≤ c := by
      by_contra h; push Not at h
      exact h₂.2 (mm_smul_mem_interior hK (mm_mem_of_frontier hK h₀) hc0 h)
    have hc1 : c = 1 := le_antisymm hle hge
    subst hc1
    have := mm_le_one_of_smul_mem hK h₀ (t := 2) (by norm_num)
      (by convert mm_mem_of_frontier hK h₁ using 1; module)
    norm_num at this
  · have hn := mm_neg_mem_frontier hK h₂
    have hle := mm_le_one_of_smul_mem hK h₀ (t := -c) (by linarith)
      (by convert mm_mem_of_frontier hK hn using 1; module)
    have hge : 1 ≤ -c := by
      by_contra h; push Not at h
      have := mm_smul_mem_interior hK (mm_mem_of_frontier hK h₀) (t := -c) (by linarith) h
      apply hn.2
      convert this using 1; module
    have hc1 : c = -1 := by linarith
    subst hc1
    apply mm_ne_zero_of_frontier hK h₁
    module

end Converse

/-! ### Deformations of a critical lattice -/

section Deform

variable {K : Set (Fin 2 → ℝ)}

lemma mm_abs_cross_le (x y : Fin 2 → ℝ) : |cross x y| ≤ 2 * ‖x‖ * ‖y‖ := by
  have hx0 : |x 0| ≤ ‖x‖ := by simpa using norm_le_pi_norm x 0
  have hx1 : |x 1| ≤ ‖x‖ := by simpa using norm_le_pi_norm x 1
  have hy0 : |y 0| ≤ ‖y‖ := by simpa using norm_le_pi_norm y 0
  have hy1 : |y 1| ≤ ‖y‖ := by simpa using norm_le_pi_norm y 1
  calc |cross x y| ≤ |x 0| * |y 1| + |x 1| * |y 0| := by
        simp only [cross]; rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
    _ ≤ ‖x‖ * ‖y‖ + ‖x‖ * ‖y‖ := by gcongr
    _ = 2 * ‖x‖ * ‖y‖ := by ring

lemma mm_comb_ne_zero {u v : Fin 2 → ℝ} (huv : cross u v ≠ 0) {m n : ℤ} (hmn : m ≠ 0 ∨ n ≠ 0) :
    (m : ℝ) • u + (n : ℝ) • v ≠ 0 := by
  intro h
  have h1 := congrArg (fun x ↦ cross x v) h
  have h2 := congrArg (fun x ↦ cross u x) h
  simp only [mm_cross_smul_add, mm_cross_add_smul, mm_cross_self] at h1 h2
  simp only [cross, Pi.zero_apply, mul_zero, sub_zero, zero_mul] at h1 h2
  rcases hmn with hm | hn
  · have : (m : ℝ) * cross u v = 0 := by simp only [cross]; linarith
    exact hm (by exact_mod_cast (mul_eq_zero.1 this).resolve_right huv)
  · have : (n : ℝ) * cross u v = 0 := by simp only [cross]; linarith
    exact hn (by exact_mod_cast (mul_eq_zero.1 this).resolve_right huv)

/-- **The deformation argument.** Let `u, v` be a basis of a lattice whose determinant
`|cross(u, v)|` is `Δ(K)`. A family of lattices with bases `A i → u`, `B i → v`, of smaller
determinant, whose points near the lattice points of `K` stay outside the interior of `K`, would
eventually be admissible: impossible. -/
lemma mm_deform (hK : IsSymmetricConvexDomain K) {u v : Fin 2 → ℝ} (huv : cross u v ≠ 0)
    (hmin : minimalDeterminant K = |cross u v|)
    {ι : Type*} {l : Filter ι} [l.NeBot] {A B : ι → Fin 2 → ℝ}
    (hA : Tendsto A l (𝓝 u)) (hB : Tendsto B l (𝓝 v))
    (hdet : ∀ᶠ i in l, |cross (A i) (B i)| < |cross u v|)
    (htouch : ∀ m n : ℤ, (m ≠ 0 ∨ n ≠ 0) → (m : ℝ) • u + (n : ℝ) • v ∈ K →
      ∀ᶠ i in l, (m : ℝ) • A i + (n : ℝ) • B i ∉ interior K) : False := by
  obtain ⟨R, hR⟩ : ∃ R, ∀ x ∈ K, ‖x‖ ≤ R := hK.2.1.isBounded.exists_norm_le
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR 0 (interior_subset (mm_zero_mem_interior hK)))
  set c := |cross u v| with hc
  have hcpos : 0 < c := abs_pos.2 huv
  have hcross : Tendsto (fun i ↦ cross (A i) (B i)) l (𝓝 (cross u v)) := by
    have hA0 := tendsto_pi_nhds.1 hA 0
    have hA1 := tendsto_pi_nhds.1 hA 1
    have hB0 := tendsto_pi_nhds.1 hB 0
    have hB1 := tendsto_pi_nhds.1 hB 1
    exact (hA0.mul hB1).sub (hA1.mul hB0)
  have hev1 : ∀ᶠ i in l, c / 2 < |cross (A i) (B i)| :=
    hcross.abs.eventually (lt_mem_nhds (by linarith))
  have hev2 : ∀ᶠ i in l, ‖A i‖ < ‖u‖ + 1 := hA.norm.eventually (gt_mem_nhds (by linarith))
  have hev3 : ∀ᶠ i in l, ‖B i‖ < ‖v‖ + 1 := hB.norm.eventually (gt_mem_nhds (by linarith))
  set N : ℕ := ⌈4 * R * (‖u‖ + ‖v‖ + 2) / c⌉₊ with hN
  have hNge : 4 * R * (‖u‖ + ‖v‖ + 2) / c ≤ N := Nat.le_ceil _
  -- the coefficients of the lattice points in `K` are bounded by `N`
  have hbound : ∀ i, c / 2 < |cross (A i) (B i)| → ‖A i‖ < ‖u‖ + 1 → ‖B i‖ < ‖v‖ + 1 →
      ∀ m n : ℤ, (m : ℝ) • A i + (n : ℝ) • B i ∈ K → |(m : ℝ)| ≤ N ∧ |(n : ℝ)| ≤ N := by
    intro i h1 h2 h3 m n hmem
    have hx := hR _ hmem
    have e1 : cross ((m : ℝ) • A i + (n : ℝ) • B i) (B i) = m * cross (A i) (B i) := by
      rw [mm_cross_smul_add, mm_cross_self]; ring
    have e2 : cross (A i) ((m : ℝ) • A i + (n : ℝ) • B i) = n * cross (A i) (B i) := by
      rw [mm_cross_add_smul, mm_cross_self]; ring
    have b1 := mm_abs_cross_le ((m : ℝ) • A i + (n : ℝ) • B i) (B i)
    have b2 := mm_abs_cross_le (A i) ((m : ℝ) • A i + (n : ℝ) • B i)
    rw [e1, abs_mul] at b1
    rw [e2, abs_mul] at b2
    have hnu := norm_nonneg u
    have hnv := norm_nonneg v
    have hnA := norm_nonneg (A i)
    have hnB := norm_nonneg (B i)
    have hm0 := abs_nonneg (m : ℝ)
    have hn0 := abs_nonneg (n : ℝ)
    constructor
    · refine le_trans ?_ hNge
      rw [le_div_iff₀ hcpos]
      have : |(m : ℝ)| * (c / 2) ≤ 2 * R * (‖v‖ + 1) := by
        calc |(m : ℝ)| * (c / 2) ≤ |(m : ℝ)| * |cross (A i) (B i)| := by gcongr
          _ ≤ 2 * ‖(m : ℝ) • A i + (n : ℝ) • B i‖ * ‖B i‖ := b1
          _ ≤ 2 * R * (‖v‖ + 1) := by gcongr
      nlinarith
    · refine le_trans ?_ hNge
      rw [le_div_iff₀ hcpos]
      have : |(n : ℝ)| * (c / 2) ≤ 2 * (‖u‖ + 1) * R := by
        calc |(n : ℝ)| * (c / 2) ≤ |(n : ℝ)| * |cross (A i) (B i)| := by gcongr
          _ ≤ 2 * ‖A i‖ * ‖(m : ℝ) • A i + (n : ℝ) • B i‖ := b2
          _ ≤ 2 * (‖u‖ + 1) * R := by gcongr
      nlinarith
  -- in the finite box of coefficients, the points eventually avoid the interior
  set S : Finset (ℤ × ℤ) := Finset.Icc (-(N : ℤ)) N ×ˢ Finset.Icc (-(N : ℤ)) N
  have hevS : ∀ᶠ i in l, ∀ p ∈ S, (p.1 ≠ 0 ∨ p.2 ≠ 0) →
      (p.1 : ℝ) • A i + (p.2 : ℝ) • B i ∉ interior K := by
    rw [Filter.eventually_all_finset]
    intro p _
    by_cases hp : p.1 ≠ 0 ∨ p.2 ≠ 0
    · by_cases hK' : (p.1 : ℝ) • u + (p.2 : ℝ) • v ∈ K
      · exact (htouch p.1 p.2 hp hK').mono fun i hi _ ↦ hi
      · have hT : Tendsto (fun i ↦ (p.1 : ℝ) • A i + (p.2 : ℝ) • B i) l
            (𝓝 ((p.1 : ℝ) • u + (p.2 : ℝ) • v)) := (hA.const_smul _).add (hB.const_smul _)
        have := hT.eventually ((mm_isClosed hK).isOpen_compl.mem_nhds hK')
        exact this.mono fun i hi _ hint ↦ hi (interior_subset hint)
    · exact Eventually.of_forall fun i h ↦ absurd h hp
  obtain ⟨i, h1, h2, h3, h4, h5⟩ := (hev1.and (hev2.and (hev3.and (hdet.and hevS)))).exists
  have hne : cross (A i) (B i) ≠ 0 := by
    intro h; rw [h, abs_zero] at h1; linarith
  have hadm' : IsAdmissible K (Submodule.span ℤ {A i, B i}) := by
    intro x hx hxK
    obtain ⟨m, n, rfl⟩ := mm_mem_span_pair.1 hx
    by_contra hx0
    have hmn : m ≠ 0 ∨ n ≠ 0 := by
      by_contra h; push Not at h; apply hx0; simp [h.1, h.2]
    obtain ⟨hm, hn⟩ := hbound i h1 h2 h3 m n (interior_subset hxK)
    have hm' := abs_le.1 hm
    have hn' := abs_le.1 hn
    have hmS : (m, n) ∈ S := by
      simp only [S, Finset.mem_product, Finset.mem_Icc]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · have : (-(N : ℝ)) ≤ m := hm'.1
        exact_mod_cast this
      · have : (m : ℝ) ≤ N := hm'.2
        exact_mod_cast this
      · have : (-(N : ℝ)) ≤ n := hn'.1
        exact_mod_cast this
      · have : (n : ℝ) ≤ N := hn'.2
        exact_mod_cast this
    exact h5 (m, n) hmS hmn hxK
  have := mm_minimalDeterminant_le (mm_isLattice_span hne) hadm'
  rw [mm_det_span hne, hmin] at this
  linarith

end Deform

/-! ### The lattice points of a critical lattice on the boundary -/

section Critical

variable {K : Set (Fin 2 → ℝ)}

lemma mm_tendsto_zero {f : ℝ → Fin 2 → ℝ} (hf : Continuous f) :
    Tendsto f (𝓝[>] 0) (𝓝 (f 0)) :=
  (hf.tendsto 0).mono_left nhdsWithin_le_nhds

/-- A critical lattice has a lattice point `≠ 0` in `K`: otherwise the lattice `(1 - t) Λ` would
be admissible for small `t > 0`. -/
lemma mm_exists_mem (hK : IsSymmetricConvexDomain K) {u v : Fin 2 → ℝ} (huv : cross u v ≠ 0)
    (hmin : minimalDeterminant K = |cross u v|) :
    ∃ m n : ℤ, (m ≠ 0 ∨ n ≠ 0) ∧ (m : ℝ) • u + (n : ℝ) • v ∈ K := by
  by_contra hno
  refine mm_deform hK huv hmin (l := 𝓝[>] (0 : ℝ)) (A := fun t ↦ (1 - t) • u)
    (B := fun t ↦ (1 - t) • v) ?_ ?_ ?_ fun m n hmn hmem ↦ absurd ⟨m, n, hmn, hmem⟩ hno
  · simpa using mm_tendsto_zero (f := fun t : ℝ ↦ (1 - t) • u) (by fun_prop)
  · simpa using mm_tendsto_zero (f := fun t : ℝ ↦ (1 - t) • v) (by fun_prop)
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    have : cross ((1 - t) • u) ((1 - t) • v) = (1 - t) ^ 2 * cross u v := by
      simp only [cross, Pi.smul_apply, smul_eq_mul]; ring
    rw [this, abs_mul, abs_of_pos (by nlinarith [ht.1, ht.2])]
    have := abs_pos.2 huv
    have h1 : (1 - t) ^ 2 < 1 := by nlinarith [ht.1, ht.2]
    nlinarith

/-- A critical lattice has a lattice point in `K` independent of any given `x₀ ≠ 0`: otherwise
the lattice could be compressed along a direction transversal to `x₀`, fixing the lattice points
of `K`. -/
lemma mm_exists_indep (hK : IsSymmetricConvexDomain K) {u v : Fin 2 → ℝ} (huv : cross u v ≠ 0)
    (hadm : IsAdmissible K (Submodule.span ℤ {u, v})) (hmin : minimalDeterminant K = |cross u v|)
    {x₀ : Fin 2 → ℝ} (hx₀ : x₀ ≠ 0) :
    ∃ m n : ℤ, (m : ℝ) • u + (n : ℝ) • v ∈ K ∧ cross x₀ ((m : ℝ) • u + (n : ℝ) • v) ≠ 0 := by
  by_contra hno
  push Not at hno
  set w : Fin 2 → ℝ := ![-x₀ 1, x₀ 0]
  set d := cross x₀ w with hd
  have hdpos : d ≠ 0 := by
    have : d = x₀ 0 ^ 2 + x₀ 1 ^ 2 := by simp [hd, w, cross]; ring
    rw [this]
    intro h
    apply hx₀
    ext i; fin_cases i
    · simp; nlinarith [sq_nonneg (x₀ 0), sq_nonneg (x₀ 1)]
    · simp; nlinarith [sq_nonneg (x₀ 0), sq_nonneg (x₀ 1)]
  set T : ℝ → (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun t z ↦ z - (t * cross x₀ z / d) • w
  have hT : ∀ t (m n : ℝ), m • T t u + n • T t v = T t (m • u + n • v) := by
    intro t m n
    simp only [T, mm_cross_add_smul]
    module
  refine mm_deform hK huv hmin (l := 𝓝[>] (0 : ℝ)) (A := fun t ↦ T t u) (B := fun t ↦ T t v)
    ?_ ?_ ?_ ?_
  · simpa [T] using mm_tendsto_zero (f := fun t : ℝ ↦ T t u) (by fun_prop)
  · simpa [T] using mm_tendsto_zero (f := fun t : ℝ ↦ T t v) (by fun_prop)
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    have key : ∀ (z₁ z₂ : Fin 2 → ℝ) (α β : ℝ),
        cross (z₁ - α • w) (z₂ - β • w) = cross z₁ z₂ - β * cross z₁ w - α * cross w z₂ := by
      intros; simp only [cross, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    have hpl : cross x₀ v * cross u w + cross x₀ u * cross w v = d * cross u v := by
      simp only [hd, cross]; ring
    have : cross (T t u) (T t v) = (1 - t) * cross u v := by
      calc cross (T t u) (T t v)
          = cross u v - t / d * (cross x₀ v * cross u w + cross x₀ u * cross w v) := by
            simp only [T]; rw [key]; ring
        _ = (1 - t) * cross u v := by rw [hpl]; field_simp
    rw [this, abs_mul, abs_of_pos (by linarith [ht.2])]
    have := abs_pos.2 huv
    nlinarith [ht.1]
  · intro m n hmn hmem
    refine Eventually.of_forall fun t ↦ ?_
    have h0 := hno m n hmem
    rw [hT]
    have hTz : T t ((m : ℝ) • u + (n : ℝ) • v) = (m : ℝ) • u + (n : ℝ) • v := by
      simp only [T, h0, mul_zero, zero_div, zero_smul, sub_zero]
    rw [hTz]
    intro hint
    exact mm_comb_ne_zero huv hmn (hadm _ (mm_mem_span_pair.2 ⟨m, n, rfl⟩) hint)

lemma mm_cross_int {u v a b : Fin 2 → ℝ} (ha : a ∈ Submodule.span ℤ {u, v})
    (hb : b ∈ Submodule.span ℤ {u, v}) : ∃ j : ℤ, cross a b = j * cross u v := by
  obtain ⟨p, q, rfl⟩ := mm_mem_span_pair.1 ha
  obtain ⟨r, s, rfl⟩ := mm_mem_span_pair.1 hb
  exact ⟨p * s - q * r, by rw [mm_cross_comb]; push_cast; ring⟩

lemma mm_natAbs_cast (j : ℤ) : ((j.natAbs : ℕ) : ℝ) = |(j : ℝ)| := by
  rw [Nat.cast_natAbs, Int.cast_abs]

/-- Two points `a, b` of `span{u, v}` with `|cross(a, b)| = |cross(u, v)| ≠ 0` span it. -/
lemma mm_span_eq {u v a b : Fin 2 → ℝ} (huv : cross u v ≠ 0) (ha : a ∈ Submodule.span ℤ {u, v})
    (hb : b ∈ Submodule.span ℤ {u, v}) (hab : |cross a b| = |cross u v|) :
    Submodule.span ℤ {a, b} = Submodule.span ℤ {u, v} := by
  obtain ⟨p, q, rfl⟩ := mm_mem_span_pair.1 ha
  obtain ⟨r, s, rfl⟩ := mm_mem_span_pair.1 hb
  have hcross : cross ((p : ℝ) • u + (q : ℝ) • v) ((r : ℝ) • u + (s : ℝ) • v)
      = ((p * s - q * r : ℤ) : ℝ) * cross u v := by
    rw [mm_cross_comb]; push_cast; ring
  obtain ⟨D, hD⟩ : ∃ D : ℤ, D = p * s - q * r := ⟨_, rfl⟩
  rw [hcross, ← hD, abs_mul] at hab
  have hD1 : |(D : ℝ)| = 1 := by
    have := abs_pos.2 huv
    field_simp at hab
    linarith
  have hDD : (D : ℝ) * D = 1 := by
    rcases abs_eq (zero_le_one) |>.1 hD1 with h | h <;> rw [h] <;> norm_num
  have hDr : (D : ℝ) = p * s - q * r := by rw [hD]; push_cast; ring
  apply le_antisymm
  · rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨mm_mem_span_pair.2 ⟨_, _, rfl⟩, mm_mem_span_pair.2 ⟨_, _, rfl⟩⟩
  · rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    constructor
    · refine mm_mem_span_pair.2 ⟨D * s, -(D * q), ?_⟩
      push_cast
      calc ((D : ℝ) * s) • ((p : ℝ) • u + (q : ℝ) • v)
            + (-((D : ℝ) * q)) • ((r : ℝ) • u + (s : ℝ) • v)
          = ((D : ℝ) * (p * s - q * r)) • u := by module
        _ = u := by rw [← hDr, hDD, one_smul]
    · refine mm_mem_span_pair.2 ⟨-(D * r), D * p, ?_⟩
      push_cast
      calc (-((D : ℝ) * r)) • ((p : ℝ) • u + (q : ℝ) • v)
            + ((D : ℝ) * p) • ((r : ℝ) • u + (s : ℝ) • v)
          = ((D : ℝ) * (p * s - q * r)) • v := by module
        _ = v := by rw [← hDr, hDD, one_smul]

/-- A critical lattice `span{u, v}` has two lattice points `a, b` in `K` with
`|cross(a, b)| = |cross(u, v)|`: among the pairs of independent lattice points of `K` (they exist
by `mm_exists_mem`, `mm_exists_indep`) take one of least `|cross(a, b)|`; if it were not a basis,
the lattice would have a point `y = α a + β b`, `0 ≤ α, β < 1`, outside `ℤ a + ℤ b`, and `y` or
`a + b - y` would give a lattice point of the interior or a pair of smaller `|cross|`. -/
lemma mm_exists_pair (hK : IsSymmetricConvexDomain K) {u v : Fin 2 → ℝ} (huv : cross u v ≠ 0)
    (hadm : IsAdmissible K (Submodule.span ℤ {u, v})) (hmin : minimalDeterminant K = |cross u v|) :
    ∃ a b, a ∈ Submodule.span ℤ {u, v} ∧ b ∈ Submodule.span ℤ {u, v} ∧ a ∈ K ∧ b ∈ K ∧
      |cross a b| = |cross u v| := by
  classical
  set Λ := Submodule.span ℤ {u, v} with hΛ
  have hc := abs_pos.2 huv
  obtain ⟨m, n, hmn, hK₀⟩ := mm_exists_mem hK huv hmin
  obtain ⟨m', n', hK₁, hc₁⟩ := mm_exists_indep hK huv hadm hmin (mm_comb_ne_zero huv hmn)
  let P : ℕ → Prop := fun k ↦ 0 < k ∧ ∃ a b, a ∈ Λ ∧ b ∈ Λ ∧ a ∈ K ∧ b ∈ K ∧
    |cross a b| = k * |cross u v|
  have hP : ∃ k, P k := by
    have h₀ : (m : ℝ) • u + (n : ℝ) • v ∈ Λ := mm_mem_span_pair.2 ⟨m, n, rfl⟩
    have h₁ : (m' : ℝ) • u + (n' : ℝ) • v ∈ Λ := mm_mem_span_pair.2 ⟨m', n', rfl⟩
    obtain ⟨j, hj⟩ := mm_cross_int h₀ h₁
    have hj0 : j ≠ 0 := by rintro rfl; exact hc₁ (by simpa using hj)
    exact ⟨j.natAbs, Int.natAbs_pos.2 hj0, _, _, h₀, h₁, hK₀, hK₁, by
      rw [hj, abs_mul, mm_natAbs_cast]⟩
  obtain ⟨hk₀, a, b, haΛ, hbΛ, haK, hbK, hab⟩ := Nat.find_spec hP
  set k₀ := Nat.find hP with hk₀def
  by_cases hk1 : k₀ = 1
  · exact ⟨a, b, haΛ, hbΛ, haK, hbK, by rw [hab, hk1]; simp⟩
  exfalso
  have hk2 : (2 : ℝ) ≤ k₀ := by exact_mod_cast (show 2 ≤ k₀ by omega)
  have hcab : cross a b ≠ 0 := by
    intro h; rw [h, abs_zero] at hab; nlinarith
  -- a point of `Λ` outside `ℤ a + ℤ b`
  obtain ⟨x, hxΛ, hxab⟩ : ∃ x ∈ Λ, x ∉ Submodule.span ℤ {a, b} := by
    by_contra h
    push Not at h
    obtain ⟨j, hj⟩ := mm_cross_int (h u (Submodule.subset_span (by simp)))
      (h v (Submodule.subset_span (by simp)))
    have hh : |cross u v| = |(j : ℝ)| * (k₀ * |cross u v|) := by
      conv_lhs => rw [hj]
      rw [abs_mul, hab]
    have h1 : |(j : ℝ)| * k₀ = 1 := by
      have hc' : |cross u v| ≠ 0 := hc.ne'
      apply mul_left_cancel₀ hc'
      linear_combination -hh
    have : (1 : ℝ) ≤ |(j : ℝ)| := by
      have hj0 : j ≠ 0 := by rintro rfl; simp at h1
      have : (1 : ℤ) ≤ |j| := Int.one_le_abs hj0
      exact_mod_cast this
    nlinarith
  have hx := mm_eq_comb hcab x
  set lam := cross x b / cross a b
  set mu := cross a x / cross a b
  set y := x - (⌊lam⌋ : ℝ) • a - (⌊mu⌋ : ℝ) • b with hydef
  have hyΛ : y ∈ Λ := by
    refine Λ.sub_mem (Λ.sub_mem hxΛ ?_) ?_
    · rw [Int.cast_smul_eq_zsmul]; exact zsmul_mem haΛ _
    · rw [Int.cast_smul_eq_zsmul]; exact zsmul_mem hbΛ _
  set α := Int.fract lam
  set β := Int.fract mu
  have hy : y = α • a + β • b := by
    rw [hydef]; conv_lhs => rw [hx]
    simp only [α, β, Int.fract]
    module
  have hyab : y ∉ Submodule.span ℤ {a, b} := by
    intro hy'
    apply hxab
    have : x = y + (⌊lam⌋ : ℝ) • a + (⌊mu⌋ : ℝ) • b := by rw [hydef]; module
    rw [this]
    refine Submodule.add_mem _ (Submodule.add_mem _ hy' ?_) ?_
    · rw [Int.cast_smul_eq_zsmul]
      exact zsmul_mem (Submodule.subset_span (by simp)) _
    · rw [Int.cast_smul_eq_zsmul]
      exact zsmul_mem (Submodule.subset_span (by simp)) _
  have hα0 : 0 ≤ α := Int.fract_nonneg _
  have hα1 : α < 1 := Int.fract_lt_one _
  have hβ0 : 0 ≤ β := Int.fract_nonneg _
  have hβ1 : β < 1 := Int.fract_lt_one _
  rcases lt_trichotomy (α + β) 1 with hlt | heq | hgt
  · have hint := mm_comb_mem_interior hK haK hbK hα0 hβ0 hlt
    rw [← hy] at hint
    have := hadm y hyΛ hint
    exact hyab (this ▸ Submodule.zero_mem _)
  · have hβ : 0 < β := by
      rcases hβ0.lt_or_eq with h | h
      · exact h
      · rw [← h] at heq; linarith
    have hyK : y ∈ K := hy ▸ mm_comb_mem hK haK hbK hα0 hβ0 heq.le
    have hcay : cross a y = β * cross a b := by
      rw [hy, mm_cross_add_smul, mm_cross_self]; ring
    obtain ⟨j, hj⟩ := mm_cross_int haΛ hyΛ
    have hjk : |(j : ℝ)| = β * k₀ := by
      have h1 : |cross a y| = |(j : ℝ)| * |cross u v| := by rw [hj, abs_mul]
      have h2 : |cross a y| = β * (k₀ * |cross u v|) := by
        rw [hcay, abs_mul, abs_of_pos hβ, hab]
      have := h1.symm.trans h2
      field_simp at this
      linarith
    have hlt : j.natAbs < k₀ := by
      have : ((j.natAbs : ℕ) : ℝ) < k₀ := by
        rw [mm_natAbs_cast, hjk]
        have : (0 : ℝ) < k₀ := by linarith
        nlinarith
      exact_mod_cast this
    have hpos : 0 < j.natAbs := by
      have : (0 : ℝ) < ((j.natAbs : ℕ) : ℝ) := by
        rw [mm_natAbs_cast, hjk]; positivity
      exact_mod_cast this
    exact Nat.find_min hP hlt ⟨hpos, a, y, haΛ, hyΛ, haK, hyK, by
      rw [hj, abs_mul, mm_natAbs_cast]⟩
  · set z := a + b - y with hzdef
    have hz : z = (1 - α) • a + (1 - β) • b := by rw [hzdef, hy]; module
    have hint := mm_comb_mem_interior hK haK hbK (α := 1 - α) (β := 1 - β) (by linarith)
      (by linarith) (by linarith)
    rw [← hz] at hint
    have hzΛ : z ∈ Λ := Λ.sub_mem (Λ.add_mem haΛ hbΛ) hyΛ
    have hz0 := hadm z hzΛ hint
    apply hyab
    have : y = a + b := by
      have : a + b - y = 0 := hz0
      exact (sub_eq_zero.1 this).symm
    rw [this]
    exact Submodule.add_mem _ (Submodule.subset_span (by simp))
      (Submodule.subset_span (by simp))

/-- If `a, b` is a basis of a critical lattice lying on the boundary of `K`, then `a + b` or
`a - b` is in `K`: otherwise the lattice points of `K` are `0, ±a, ±b`, and the lattice with basis
`a + t(b - p a)`, `b + t(a - q b)` (`p = f b`, `q = g a` for support functionals `f, g` at `a, b`)
keeps `±a, ±b` on the support lines and has smaller determinant for small `t` of the right sign. -/
lemma mm_add_or_sub_mem (hK : IsSymmetricConvexDomain K) {a b : Fin 2 → ℝ} (hab : cross a b ≠ 0)
    (ha : a ∈ frontier K) (hb : b ∈ frontier K) (hmin : minimalDeterminant K = |cross a b|) :
    a + b ∈ K ∨ a - b ∈ K := by
  by_contra hno
  push Not at hno
  obtain ⟨hp, hm⟩ := hno
  have haK := mm_mem_of_frontier hK ha
  have hbK := mm_mem_of_frontier hK hb
  have hnaK := hK.2.2.2 a haK
  have hnbK := hK.2.2.2 b hbK
  obtain ⟨F₁, c₁, hF₁K, hF₁⟩ := geometric_hahn_banach_closed_point hK.1 (mm_isClosed hK) hp
  obtain ⟨F₂, c₂, hF₂K, hF₂⟩ := geometric_hahn_banach_closed_point hK.1 (mm_isClosed hK) hm
  -- the lattice points of `K` are `0, ±a, ±b`
  have hpts : ∀ m n : ℤ, (m ≠ 0 ∨ n ≠ 0) → (m : ℝ) • a + (n : ℝ) • b ∈ K →
      (m = 1 ∧ n = 0) ∨ (m = -1 ∧ n = 0) ∨ (m = 0 ∧ n = 1) ∨ (m = 0 ∧ n = -1) := by
    intro m n hmn hmem
    have hneg := hK.2.2.2 _ hmem
    have e1 := hF₁K _ hmem
    have e1' := hF₁K _ hneg
    have e2 := hF₂K _ hmem
    have e2' := hF₂K _ hneg
    have fa := hF₁K a haK
    have fb := hF₁K b hbK
    have ga := hF₂K a haK
    have gb := hF₂K (-b) hnbK
    have gna := hF₂K (-a) hnaK
    simp only [map_add, map_sub, map_neg, map_smul, smul_eq_mul] at e1 e1' e2 e2' hF₁ hF₂ gb gna
    rcases lt_trichotomy m 0 with hm0 | hm0 | hm0 <;>
      rcases lt_trichotomy n 0 with hn0 | hn0 | hn0
    · exfalso
      have hm1 : (m : ℝ) ≤ -1 := by exact_mod_cast (show m ≤ -1 by omega)
      have hn1 : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
      nlinarith
    · subst hn0
      have hm' : (m : ℝ) < 0 := by exact_mod_cast hm0
      have h1 : (-m : ℝ) ≤ 1 := mm_le_one_of_smul_mem hK ha (by linarith)
        (by convert hneg using 1; simp)
      have h2 : (-1 : ℤ) ≤ m := by
        have : (-1 : ℝ) ≤ m := by linarith
        exact_mod_cast this
      exact Or.inr (Or.inl ⟨by omega, rfl⟩)
    · exfalso
      have hm1 : (m : ℝ) ≤ -1 := by exact_mod_cast (show m ≤ -1 by omega)
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      nlinarith
    · subst hm0
      have hn' : (n : ℝ) < 0 := by exact_mod_cast hn0
      have h1 : (-n : ℝ) ≤ 1 := mm_le_one_of_smul_mem hK hb (by linarith)
        (by convert hneg using 1; simp)
      have h2 : (-1 : ℤ) ≤ n := by
        have : (-1 : ℝ) ≤ n := by linarith
        exact_mod_cast this
      exact Or.inr (Or.inr (Or.inr ⟨rfl, by omega⟩))
    · subst hm0; subst hn0; simp at hmn
    · subst hm0
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
      have h1 : (n : ℝ) ≤ 1 := mm_le_one_of_smul_mem hK hb hn'.le
        (by convert hmem using 1; simp)
      have h2 : n ≤ 1 := by exact_mod_cast h1
      exact Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩))
    · exfalso
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
      have hn1 : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
      nlinarith
    · subst hn0
      have hm' : (0 : ℝ) < m := by exact_mod_cast hm0
      have h1 : (m : ℝ) ≤ 1 := mm_le_one_of_smul_mem hK ha hm'.le
        (by convert hmem using 1; simp)
      have h2 : m ≤ 1 := by exact_mod_cast h1
      exact Or.inl ⟨by omega, rfl⟩
    · exfalso
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      nlinarith
  obtain ⟨f, hf1, hf2, hf3⟩ := mm_support hK ha
  obtain ⟨g, hg1, hg2, hg3⟩ := mm_support hK hb
  set p := f b with hpdef
  set q := g a with hqdef
  have hp1 : |p| ≤ 1 := by
    have h1 := hf2 b hbK
    have h2 := hf2 (-b) hnbK
    rw [map_neg] at h2
    exact abs_le.2 ⟨by linarith, h1⟩
  have hq1 : |q| ≤ 1 := by
    have h1 := hg2 a haK
    have h2 := hg2 (-a) hnaK
    rw [map_neg] at h2
    exact abs_le.2 ⟨by linarith, h1⟩
  set τ : ℝ := if 0 ≤ p + q then 1 else -1 with hτdef
  have hτ : τ * (p + q) = |p + q| ∧ τ * τ = 1 := by
    by_cases h : 0 ≤ p + q
    · simp [hτdef, h, abs_of_nonneg h]
    · push Not at h; simp [hτdef, h.not_ge, abs_of_neg h]
  set A : ℝ → Fin 2 → ℝ := fun t ↦ (1 - τ * t * p) • a + (τ * t) • b with hAdef
  set B : ℝ → Fin 2 → ℝ := fun t ↦ (τ * t) • a + (1 - τ * t * q) • b with hBdef
  have hfA : ∀ t, f (A t) = 1 := by
    intro t; simp only [hAdef, map_add, map_smul, smul_eq_mul, hf1, ← hpdef]; ring
  have hgB : ∀ t, g (B t) = 1 := by
    intro t; simp only [hBdef, map_add, map_smul, smul_eq_mul, hg1, ← hqdef]; ring
  refine mm_deform hK hab hmin (l := 𝓝[>] (0 : ℝ)) (A := A) (B := B) ?_ ?_ ?_ ?_
  · simpa [hAdef] using mm_tendsto_zero (f := A) (by rw [hAdef]; fun_prop)
  · simpa [hBdef] using mm_tendsto_zero (f := B) (by rw [hBdef]; fun_prop)
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 8 by norm_num)] with t ht
    obtain ⟨ht0, ht1⟩ := ht
    have hφ : cross (A t) (B t) = (1 - t * |p + q| + t ^ 2 * (p * q - 1)) * cross a b := by
      rw [hAdef, hBdef, mm_cross_comb, ← hτ.1]
      linear_combination (t ^ 2 * (p * q - 1) * cross a b) * hτ.2
    have hpq : |p * q| ≤ 1 := by rw [abs_mul]; nlinarith [abs_nonneg p, abs_nonneg q]
    have hpq' := abs_le.1 hpq
    have hs := abs_nonneg (p + q)
    have hs2 : |p + q| ≤ 2 := (abs_add_le p q).trans (by linarith)
    have hφpos : 0 < 1 - t * |p + q| + t ^ 2 * (p * q - 1) := by nlinarith
    have hφlt : 1 - t * |p + q| + t ^ 2 * (p * q - 1) < 1 := by
      rcases hs.lt_or_eq with h | h
      · nlinarith
      · have hq' : q = -p := by
          have := abs_eq_zero.1 h.symm; linarith
        have : p * q - 1 < 0 := by rw [hq']; nlinarith [sq_nonneg p]
        have : t ^ 2 * (p * q - 1) < 0 := mul_neg_of_pos_of_neg (by positivity) this
        rw [← h]; linarith
    rw [hφ, abs_mul, abs_of_pos hφpos]
    have := abs_pos.2 hab
    nlinarith
  · intro m n hmn hmem
    refine Eventually.of_forall fun t hint ↦ ?_
    rcases hpts m n hmn hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have := hf3 _ (by simpa using hint)
      rw [hfA] at this; exact lt_irrefl _ this
    · have := hf3 _ (by simpa using mm_neg_mem_interior hK hint)
      rw [hfA] at this; exact lt_irrefl _ this
    · have := hg3 _ (by simpa using hint)
      rw [hgB] at this; exact lt_irrefl _ this
    · have := hg3 _ (by simpa using mm_neg_mem_interior hK hint)
      rw [hgB] at this; exact lt_irrefl _ this

end Critical

end MinkowskiMahler

open MinkowskiMahler in
/-- **Minkowski (1907), Mahler (1946).** Let `Λ` be a critical lattice of a symmetric convex domain
`K`. Then `Λ` has three points `P₀, P₁, P₂` on the boundary of `K` with `P₁ = P₀ + P₂` (the
parallelogram `O P₀ P₁ P₂`) such that `P₀, P₁` is a basis of `Λ` and
`d(Λ) = |det(P₀, P₁)| = Δ(K)`. Conversely, if `P₀, P₁, P₂` are points on the boundary of `K` with
`P₁ = P₀ + P₂`, then `|det(P₀, P₁)| ≥ Δ(K)`, with equality if and only if the lattice with basis
`P₀, P₁` is critical. -/
theorem minkowski_mahler {K : Set (Fin 2 → ℝ)} (hK : IsSymmetricConvexDomain K) :
    (∀ Λ, IsCritical K Λ →
      ∃ P₀ P₁ P₂ : Fin 2 → ℝ, P₀ ∈ Λ ∧ P₁ ∈ Λ ∧ P₂ ∈ Λ ∧
        P₀ ∈ frontier K ∧ P₁ ∈ frontier K ∧ P₂ ∈ frontier K ∧
        IsBasis Λ P₀ P₁ ∧ P₁ = P₀ + P₂ ∧
        det Λ = |cross P₀ P₁| ∧ |cross P₀ P₁| = minimalDeterminant K) ∧
    ∀ P₀ P₁ P₂ : Fin 2 → ℝ, P₀ ∈ frontier K → P₁ ∈ frontier K → P₂ ∈ frontier K →
      P₁ = P₀ + P₂ →
        minimalDeterminant K ≤ |cross P₀ P₁| ∧
          (|cross P₀ P₁| = minimalDeterminant K ↔
            IsCritical K (Submodule.span ℤ {P₀, P₁})) := by
  refine ⟨fun Λ hΛ ↦ ?_, fun P₀ P₁ P₂ h₀ h₁ h₂ h₀₁₂ ↦ ?_⟩
  · obtain ⟨hlat, hadm, hdet⟩ := hΛ
    obtain ⟨u, v, hbasis, huv⟩ := mm_exists_basis hlat
    have hdetuv : det Λ = |cross u v| := mm_det_eq hlat hbasis
    obtain ⟨-, hspan⟩ := hbasis
    subst hspan
    have hmin : minimalDeterminant K = |cross u v| := hdet ▸ hdetuv
    obtain ⟨a, b, haΛ, hbΛ, haK, hbK, hab⟩ := mm_exists_pair hK huv hadm hmin
    have hab0 : cross a b ≠ 0 := by
      intro h; rw [h, abs_zero] at hab; exact huv (abs_eq_zero.1 hab.symm)
    have hspan' := mm_span_eq huv haΛ hbΛ hab
    -- lattice points of `K` other than `0` are on the boundary
    have hfr : ∀ x ∈ Submodule.span ℤ {u, v}, x ∈ K → x ≠ 0 → x ∈ frontier K :=
      fun x hx hxK hx0 ↦ mm_mem_frontier hK hxK fun h ↦ hx0 (hadm x hx h)
    have ha0 : a ≠ 0 := by rintro rfl; simp [cross] at hab0
    have hb0 : b ≠ 0 := by rintro rfl; simp [cross] at hab0
    have ha := hfr a haΛ haK ha0
    have hb := hfr b hbΛ hbK hb0
    have hmin' : minimalDeterminant K = |cross a b| := by rw [hmin, hab]
    rcases mm_add_or_sub_mem hK hab0 ha hb hmin' with h | h
    · -- `P₀ = a`, `P₂ = b`, `P₁ = a + b`
      have hc : cross a (a + b) = cross a b := by simp only [cross, Pi.add_apply]; ring
      have habΛ : a + b ∈ Submodule.span ℤ {u, v} := Submodule.add_mem _ haΛ hbΛ
      have hab0' : a + b ≠ 0 := by
        intro h0; apply hab0; rw [← hc, h0]; simp [cross]
      have hbasis : IsBasis (Submodule.span ℤ {u, v}) a (a + b) :=
        ⟨mm_linearIndependent (hc ▸ hab0),
          mm_span_eq huv haΛ habΛ (by rw [hc, hab])⟩
      refine ⟨a, a + b, b, haΛ, habΛ, hbΛ, ha, hfr _ habΛ h hab0', hb, hbasis, rfl, ?_, ?_⟩
      · rw [hdetuv, hc, hab]
      · rw [hc, hab, hmin]
    · -- `P₀ = a - b`, `P₂ = b`, `P₁ = a`
      have hc : cross (a - b) a = cross a b := by simp only [cross, Pi.sub_apply]; ring
      have habΛ : a - b ∈ Submodule.span ℤ {u, v} := Submodule.sub_mem _ haΛ hbΛ
      have hab0' : a - b ≠ 0 := by
        intro h0; apply hab0; rw [← hc, h0]; simp [cross]
      have hbasis : IsBasis (Submodule.span ℤ {u, v}) (a - b) a :=
        ⟨mm_linearIndependent (hc ▸ hab0),
          mm_span_eq huv habΛ haΛ (by rw [hc, hab])⟩
      refine ⟨a - b, a, b, habΛ, haΛ, hbΛ, hfr _ habΛ h hab0', ha, hb, hbasis, by abel, ?_, ?_⟩
      · rw [hdetuv, hc, hab]
      · rw [hc, hab, hmin]
  · subst h₀₁₂
    have hc : cross P₀ (P₀ + P₂) = cross P₀ P₂ := by simp only [cross, Pi.add_apply]; ring
    have hc' : cross P₀ (P₀ + P₂) ≠ 0 := hc ▸ mm_cross_ne_zero hK h₀ h₂ h₁
    have hadm := mm_isAdmissible hK h₀ h₂ h₁
    have hlat := mm_isLattice_span hc'
    have hdet := mm_det_span hc'
    refine ⟨hdet ▸ mm_minimalDeterminant_le hlat hadm, fun h ↦ ⟨hlat, hadm, hdet.trans h⟩,
      fun h ↦ hdet.symm.trans h.2.2⟩

end External
