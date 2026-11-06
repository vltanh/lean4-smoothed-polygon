module

public import SmoothedPolygons.Ch2.Mahler
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Boundary parameterization of the minimizer (§2.4)

The regularity of the multi-curve that parameterizes the boundary of a worst disk `K_min`
(Lemmas 2.4.2 and 2.4.3, Corollary 2.4.4), the star conditions and the curvature constraint for
a convex disk whose boundary is parameterized by a multi-curve (Lemmas 2.4.5 and 2.4.6), and the
balanced Reinhardt problem in circle representation (Problem 2.4.8). Multi-points, multi-curves
(Definition 2.4.1) and balanced pairs (Definition 2.4.7) are in `SmoothedPolygons.Ch2.MultiCurve`.

The proofs use the following auxiliary material, proved here: support lines of a centrally
symmetric convex disk and the unit tangent `bdy_tangent` of a boundary with a regular `C¹`
parameterization; the differentiability of a boundary curve subject to an area constraint
(`bdy_hasDerivAt_of_det2_const`, the core of Lemma 2.4.2); the invariance of worst disks and
critical hexagons under orientation-preserving linear maps, used to apply Lemma 2.2.6 (stated in
circle representation); and the identification of a multi-point on the boundary of a worst disk
with the edge midpoints of a critical hexagon (`bdy_eq_hexMidpoint`).

Conventions. As in §2.4, a parameterization of the boundary traverses it counterclockwise (the
*positive orientation*); for a curve `γ` on the boundary of a centrally symmetric convex disk, this
is `det(γ, γ') > 0`. Curves are defined on `ℝ`; `deriv` is the derivative, and the second
derivative `deriv (deriv γ)` is used only almost everywhere (where it exists). Euclidean norms are
written out: `‖v‖² = v₀² + v₁²`.
-/

@[expose] public section

namespace SmoothedPolygons

open MeasureTheory Set Filter Topology Real

/-- `γ : ℝ → ℝ²` is a positively oriented regular `C¹` curve parameterizing the boundary of `K`
(§2.4): `γ` is `C¹` with nonvanishing derivative, its image is the boundary of `K`, and it turns
counterclockwise about the origin. -/
def IsPositiveBoundaryParam (K : Set (Fin 2 → ℝ)) (γ : ℝ → Fin 2 → ℝ) : Prop :=
  ContDiff ℝ 1 γ ∧ (∀ t, deriv γ t ≠ 0) ∧ range γ = frontier K ∧
    ∀ t, 0 < det2 (γ t) (deriv γ t)

/-- The boundary of `K` is parameterized by the `C¹` regular multi-curve `σ` (§2.4,
Lemmas 2.4.5 and 2.4.6): each `σ_j` is a positively oriented regular `C¹` parameterization of the
boundary of `K`, and `j ↦ σ_j(t)` is a multi-point for every `t`. -/
def IsBoundaryMultiCurve (K : Set (Fin 2 → ℝ)) (σ : ZMod 6 → ℝ → Fin 2 → ℝ) : Prop :=
  (∀ j, IsPositiveBoundaryParam K (σ j)) ∧ ∀ t, IsMultiPoint fun j ↦ σ j t

/-! ### Support lines of a convex disk -/

/-- A linear functional on the plane in coordinates: `f(v) = v₀ f(e₀) + v₁ f(e₁)`. -/
lemma bdy_dual_apply (f : StrongDual ℝ (Fin 2 → ℝ)) (v : Fin 2 → ℝ) :
    f v = v 0 * f (Pi.single 0 1) + v 1 * f (Pi.single 1 1) := by
  have hv : v = v 0 • (Pi.single 0 1 : Fin 2 → ℝ) + v 1 • (Pi.single 1 1 : Fin 2 → ℝ) := by
    ext i; fin_cases i <;> simp
  conv_lhs => rw [hv]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- A nonzero vector of the plane has positive squared norm. -/
lemma bdy_sq_pos {u : Fin 2 → ℝ} (hu : u ≠ 0) : 0 < u 0 ^ 2 + u 1 ^ 2 := by
  by_contra h
  apply hu
  have h0 : u 0 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
  have h1 : u 1 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
  ext i; fin_cases i <;> simp [h0, h1]

/-- A centrally symmetric convex disk contains the origin. -/
lemma bdy_zero_mem {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) : (0 : Fin 2 → ℝ) ∈ K := by
  obtain ⟨hconv, -, ⟨y, hy⟩, hsymm⟩ := hK
  have hyK : y ∈ K := interior_subset hy
  have := hconv hyK (hsymm y hyK) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simpa using this

/-- **Tangent lines support `K`.** If `γ` is a positively oriented regular `C¹` parameterization of
the boundary of `K ∈ 𝔎_ccs`, then `K` lies to the left of each tangent line of `γ`:
`det(γ'(τ), x - γ(τ)) ≥ 0` for all `x ∈ K`. A support functional `f` at `γ(τ)` (Hahn–Banach)
satisfies `f(γ'(τ)) = 0`, since `f ∘ γ` is maximal at `τ`; so `f` is a multiple `c det(γ'(τ), ·)`,
and `c < 0` because `0 ∈ K` and `det(γ(τ), γ'(τ)) > 0`. -/
lemma bdy_det2_deriv_sub_nonneg {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K)
    {γ : ℝ → Fin 2 → ℝ} (hγ : IsPositiveBoundaryParam K γ) (τ : ℝ) {x : Fin 2 → ℝ}
    (hx : x ∈ K) : 0 ≤ det2 (deriv γ τ) (x - γ τ) := by
  have h0K := bdy_zero_mem hK
  obtain ⟨hconv, hcomp, hint, -⟩ := hK
  obtain ⟨hC1, hreg, hrange, horient⟩ := hγ
  have hfr : ∀ t, γ t ∈ frontier K := fun t ↦ hrange ▸ mem_range_self t
  have hγK : ∀ t, γ t ∈ K := fun t ↦ hcomp.isClosed.frontier_subset (hfr t)
  -- a support functional at `γ τ`
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hconv.interior isOpen_interior (hfr τ).2
  have hfK : ∀ y ∈ K, f y ≤ f (γ τ) := by
    have hsub : closure (interior K) ⊆ {y | f y ≤ f (γ τ)} :=
      closure_minimal (fun y hy ↦ (hf y hy).le) (isClosed_le f.continuous continuous_const)
    rwa [hconv.closure_interior_eq_closure_of_nonempty_interior hint,
      hcomp.isClosed.closure_eq] at hsub
  -- `f ∘ γ` is maximal at `τ`, so `f (γ' τ) = 0`
  have hdiff : Differentiable ℝ γ := hC1.differentiable (by norm_num)
  have hmax : IsLocalMax (fun t ↦ f (γ t)) τ :=
    Filter.Eventually.of_forall fun t ↦ hfK _ (hγK t)
  have hfu : f (deriv γ τ) = 0 :=
    IsLocalMax.hasDerivAt_eq_zero hmax (f.hasFDerivAt.comp_hasDerivAt τ (hdiff τ).hasDerivAt)
  set u := deriv γ τ with hu_def
  set p := γ τ with hp_def
  set a₀ := f (Pi.single 0 1)
  set a₁ := f (Pi.single 1 1)
  have hfu' := bdy_dual_apply f u
  rw [hfu] at hfu'
  -- `|u|² f = c det(u, ·)`
  have key : ∀ v, (u 0 ^ 2 + u 1 ^ 2) * f v = (a₁ * u 0 - a₀ * u 1) * det2 u v := by
    intro v
    rw [bdy_dual_apply f v]
    unfold det2
    linear_combination (-(u 0 * v 0 + u 1 * v 1)) * hfu'
  have hu2 := bdy_sq_pos (hreg τ)
  have hor := horient τ
  -- the sign of `c`
  have hc_le : (a₁ * u 0 - a₀ * u 1) * det2 p u ≤ 0 := by
    have h1 := key (-p)
    have h2 : f (-p) ≤ 0 := by
      have := hfK 0 h0K
      rw [map_zero] at this
      rw [map_neg]
      linarith
    have h3 : det2 u (-p) = det2 p u := by unfold det2; simp only [Pi.neg_apply]; ring
    rw [h3] at h1
    nlinarith
  have hc_ne : a₁ * u 0 - a₀ * u 1 ≠ 0 := by
    intro hc
    obtain ⟨y, hy⟩ := hint
    have h1 := key y
    have h2 := key p
    rw [hc, zero_mul] at h1 h2
    have := hf y hy
    have hy0 : f y = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · linarith
      · exact h
    have hp0 : f p = 0 := by
      rcases mul_eq_zero.1 h2 with h | h
      · linarith
      · exact h
    linarith
  have hc_neg : a₁ * u 0 - a₀ * u 1 < 0 := by
    rcases lt_or_eq_of_le (nonpos_of_mul_nonpos_left hc_le hor) with h | h
    · exact h
    · exact absurd h hc_ne
  have h1 := key (x - p)
  have h2 : f (x - p) ≤ 0 := by rw [map_sub]; linarith [hfK x hx]
  by_contra hneg
  nlinarith [mul_pos_of_neg_of_neg hc_neg (not_le.1 hneg)]

/-- The derivative of `s ↦ det(u, g(s) - c)` is `det(u, g')`. -/
lemma bdy_hasDerivAt_det2 {g : ℝ → Fin 2 → ℝ} {g' : Fin 2 → ℝ} {t : ℝ} (u c : Fin 2 → ℝ)
    (h : HasDerivAt g g' t) : HasDerivAt (fun s ↦ det2 u (g s - c)) (det2 u g') t := by
  have h0 := hasDerivAt_pi.1 h 0
  have h1 := hasDerivAt_pi.1 h 1
  unfold det2
  simp only [Pi.sub_apply]
  exact ((h1.sub_const (c 1)).const_mul (u 0)).sub ((h0.sub_const (c 0)).const_mul (u 1))

/-- If the tangent line of `γ` at `τ` passes through `δ(τ)`, where `δ` is a differentiable curve
in `K`, then `δ` is tangent to that line at `τ`: `det(γ'(τ), δ'(τ)) = 0`. -/
lemma bdy_det2_deriv_eq_zero {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K)
    {γ : ℝ → Fin 2 → ℝ} (hγ : IsPositiveBoundaryParam K γ) {δ : ℝ → Fin 2 → ℝ}
    (hδ : Differentiable ℝ δ) (hδK : ∀ t, δ t ∈ K) {τ : ℝ}
    (h : det2 (deriv γ τ) (δ τ - γ τ) = 0) : det2 (deriv γ τ) (deriv δ τ) = 0 := by
  have hmin : IsLocalMin (fun t ↦ det2 (deriv γ τ) (δ t - γ τ)) τ := by
    refine Filter.Eventually.of_forall fun t ↦ ?_
    change det2 (deriv γ τ) (δ τ - γ τ) ≤ det2 (deriv γ τ) (δ t - γ τ)
    rw [h]
    exact bdy_det2_deriv_sub_nonneg hK hγ τ (hδK t)
  exact IsLocalMin.hasDerivAt_eq_zero hmin (bdy_hasDerivAt_det2 _ _ (hδ τ).hasDerivAt)

/-- Points of a boundary curve lie in `K`. -/
lemma bdy_mem {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {γ : ℝ → Fin 2 → ℝ}
    (hγ : IsPositiveBoundaryParam K γ) (t : ℝ) : γ t ∈ K :=
  hK.2.1.isClosed.frontier_subset (hγ.2.2.1 ▸ mem_range_self t)

/-- In a multi-point, `s_{j+1} = s_j + s_{j+2}`. -/
lemma bdy_mp_succ {s : ZMod 6 → Fin 2 → ℝ} (hs : IsMultiPoint s) (j : ZMod 6) :
    s (j + 1) = s j + s (j + 2) := by
  have h1 := (hs j).1
  have h2 := (hs (j + 1)).2.1
  rw [show j + 1 + 3 = j + 4 by ring] at h2
  rw [h2] at h1
  linear_combination -h1

/-- `det(w, ·)` and `det(·, w)` determine `w` against a basis: if `det(a, b) ≠ 0` and
`det(a, w) = det(b, w) = 0`, then `w = 0`. -/
lemma bdy_eq_zero_of_det2 {a b w : Fin 2 → ℝ} (hab : det2 a b ≠ 0) (ha : det2 a w = 0)
    (hb : det2 b w = 0) : w = 0 := by
  have h0 : det2 a b * w 0 = 0 := by
    unfold det2 at *; linear_combination (-a 0) * hb + (b 0) * ha
  have h1 : det2 a b * w 1 = 0 := by
    unfold det2 at *; linear_combination (-a 1) * hb + (b 1) * ha
  ext i; fin_cases i
  · exact (mul_eq_zero.1 h0).resolve_left hab
  · exact (mul_eq_zero.1 h1).resolve_left hab

/-- Two vectors parallel to a nonzero vector `u` are parallel. -/
lemma bdy_det2_eq_zero_of_parallel {u a w : Fin 2 → ℝ} (hu : u ≠ 0) (ha : det2 u a = 0)
    (hw : det2 u w = 0) : det2 a w = 0 := by
  have h0 : det2 a w * u 0 = 0 := by
    unfold det2 at *; linear_combination (a 0) * hw - (w 0) * ha
  have h1 : det2 a w * u 1 = 0 := by
    unfold det2 at *; linear_combination (a 1) * hw - (w 1) * ha
  have h : det2 a w * (u 0 ^ 2 + u 1 ^ 2) = 0 := by
    linear_combination (u 0) * h0 + (u 1) * h1
  exact (mul_eq_zero.1 h).resolve_right (bdy_sq_pos hu).ne'

/-- Coordinates in the basis `a, b` (Cramer's rule): `u = (det(a, u)/det(a, b)) b +
(det(u, b)/det(a, b)) a`. -/
lemma bdy_cramer {a b : Fin 2 → ℝ} (u : Fin 2 → ℝ) (hab : det2 a b ≠ 0) :
    u = (det2 a u / det2 a b) • b + (det2 u b / det2 a b) • a := by
  unfold det2 at *
  ext i
  fin_cases i <;>
  · simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring

/-- A centrally symmetric convex disk has the origin in its interior. -/
lemma bdy_zero_mem_interior {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) :
    (0 : Fin 2 → ℝ) ∈ interior K := by
  obtain ⟨hconv, -, ⟨y, hy⟩, hsymm⟩ := hK
  have hy' : -y ∈ interior K := by
    have h1 := (Homeomorph.neg (Fin 2 → ℝ)).preimage_interior K
    have h2 : y ∈ interior ((Homeomorph.neg (Fin 2 → ℝ)) ⁻¹' K) :=
      interior_mono (fun x hx ↦ hsymm x hx) hy
    rw [← h1] at h2
    exact h2
  have := hconv.interior hy hy' (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  simpa using this

/-- A support functional at a boundary point of `K ∈ 𝔎_ccs` (Hahn–Banach). -/
lemma bdy_exists_support {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {y : Fin 2 → ℝ}
    (hy : y ∈ frontier K) :
    ∃ f : StrongDual ℝ (Fin 2 → ℝ), (∀ z ∈ interior K, f z < f y) ∧ ∀ z ∈ K, f z ≤ f y := by
  obtain ⟨hconv, hcomp, hint, -⟩ := hK
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hconv.interior isOpen_interior hy.2
  refine ⟨f, hf, ?_⟩
  have hsub : closure (interior K) ⊆ {z | f z ≤ f y} :=
    closure_minimal (fun z hz ↦ (hf z hz).le) (isClosed_le f.continuous continuous_const)
  rwa [hconv.closure_interior_eq_closure_of_nonempty_interior hint,
    hcomp.isClosed.closure_eq] at hsub

/-- A linear functional vanishing on `e ≠ 0` is a multiple of `det(e, ·)`:
`|e|² f(v) = c det(e, v)`. -/
lemma bdy_dual_eq_det2 (f : StrongDual ℝ (Fin 2 → ℝ)) {e : Fin 2 → ℝ} (he : f e = 0)
    (v : Fin 2 → ℝ) :
    (e 0 ^ 2 + e 1 ^ 2) * f v =
      (f (Pi.single 1 1) * e 0 - f (Pi.single 0 1) * e 1) * det2 e v := by
  have h := bdy_dual_apply f e
  rw [he] at h
  rw [bdy_dual_apply f v]
  unfold det2
  linear_combination (-(e 0 * v 0 + e 1 * v 1)) * h

/-- A point on the boundary line of a closed half-plane `{z | c ≤ det(w, z)}` containing `S` is not
an interior point of `S`. -/
lemma bdy_not_mem_interior {S : Set (Fin 2 → ℝ)} {w : Fin 2 → ℝ} (hw : w ≠ 0) {c : ℝ}
    (hS : ∀ z ∈ S, c ≤ det2 w z) {z₀ : Fin 2 → ℝ} (hz₀ : det2 w z₀ = c) : z₀ ∉ interior S := by
  intro hint
  set n : Fin 2 → ℝ := ![-(w 1), w 0]
  have hn : det2 w n = w 0 ^ 2 + w 1 ^ 2 := by simp [n, det2]; ring
  have hlim : Tendsto (fun ε : ℝ ↦ z₀ - ε • n) (𝓝[>] 0) (𝓝 z₀) := by
    have : Continuous (fun ε : ℝ ↦ z₀ - ε • n) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  obtain ⟨ε, hεS, hε⟩ :=
    ((hlim.eventually (mem_interior_iff_mem_nhds.1 hint)).and self_mem_nhdsWithin).exists
  have h1 := hS _ hεS
  have h2 : det2 w (z₀ - ε • n) = c - ε * (w 0 ^ 2 + w 1 ^ 2) := by
    rw [← hz₀, ← hn]; simp only [det2, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  have h3 := bdy_sq_pos hw
  have hε' : (0 : ℝ) < ε := hε
  nlinarith

/-- A ray from the origin leaves `K` at its boundary point: if `x ∈ ∂K` and `c > 1`, then
`c x ∉ K`. -/
lemma bdy_smul_not_mem {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {x : Fin 2 → ℝ}
    (hx : x ∈ frontier K) {c : ℝ} (hc : 1 < c) : c • x ∉ K := by
  intro hcx
  have h0 := bdy_zero_mem_interior hK
  have hc0 : 0 < c := by linarith
  have hmem : x ∈ openSegment ℝ (0 : Fin 2 → ℝ) (c • x) := by
    refine ⟨1 - c⁻¹, c⁻¹, by rw [sub_pos]; exact inv_lt_one_of_one_lt₀ hc, inv_pos.2 hc0,
      by ring, ?_⟩
    rw [smul_zero, zero_add, smul_smul, inv_mul_cancel₀ hc0.ne', one_smul]
  exact hx.2 (hK.1.openSegment_interior_closure_subset_interior h0 (subset_closure hcx) hmem)

/-- Two boundary points of `K` on the same ray from the origin coincide. -/
lemma bdy_eq_of_smul {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {x y : Fin 2 → ℝ}
    (hx : x ∈ frontier K) (hy : y ∈ frontier K) {r : ℝ} (hr : 0 < r) (h : y = r • x) :
    y = x := by
  have hclosed := hK.2.1.isClosed
  rcases lt_trichotomy r 1 with hr1 | rfl | hr1
  · exfalso
    have hx' : x = r⁻¹ • y := by rw [h, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
    exact bdy_smul_not_mem hK hy (one_lt_inv₀ hr |>.2 hr1)
      (hx' ▸ hclosed.frontier_subset hx)
  · rw [h, one_smul]
  · exact absurd (h ▸ hclosed.frontier_subset hy) (bdy_smul_not_mem hK hx hr1)

/-- If a boundary point `y` of `K` lies strictly between two points `x, z` of `K`, a support
functional at `y` takes the same value at `x`, `y` and `z`. -/
lemma bdy_support_eq_of_openSegment {K : Set (Fin 2 → ℝ)} {f : StrongDual ℝ (Fin 2 → ℝ)}
    {x y z : Fin 2 → ℝ} (hf : ∀ w ∈ K, f w ≤ f y) (hx : x ∈ K) (hz : z ∈ K)
    (hy : y ∈ openSegment ℝ x z) : f x = f y ∧ f z = f y := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
  have h1 := hf x hx
  have h2 := hf z hz
  simp only [map_add, map_smul, smul_eq_mul] at h1 h2 ⊢
  have hb' : b = 1 - a := by linarith
  subst hb'
  have hxz : f x = f z := by
    rcases lt_trichotomy (f x) (f z) with h | h | h
    · nlinarith [mul_pos ha (sub_pos.2 h)]
    · exact h
    · nlinarith [mul_pos hb (sub_pos.2 h)]
  rw [← hxz]
  constructor <;> ring

/-- If a boundary point of `K` lies strictly between two points of `K`, the whole open segment
lies on the boundary. -/
lemma bdy_openSegment_subset_frontier {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K)
    {x y z : Fin 2 → ℝ} (hx : x ∈ K) (hz : z ∈ K) (hy : y ∈ openSegment ℝ x z)
    (hyf : y ∈ frontier K) : openSegment ℝ x z ⊆ frontier K := by
  obtain ⟨f, hfi, hfK⟩ := bdy_exists_support hK hyf
  obtain ⟨hfx, hfz⟩ := bdy_support_eq_of_openSegment hfK hx hz hy
  intro w hw
  have hwK : w ∈ K := hK.1.openSegment_subset hx hz hw
  refine ⟨subset_closure hwK, fun hwi ↦ ?_⟩
  have := hfi w hwi
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hw
  simp only [map_add, map_smul, smul_eq_mul, hfx, hfz] at this
  rw [← add_mul, hab, one_mul] at this
  exact lt_irrefl _ this

/-! ### The unit tangent of the boundary -/

/-- If `det(u, w) = 0` with `u ≠ 0`, then `w` is a multiple of `u`:
`w = (⟨w, u⟩/|u|²) u`. -/
lemma bdy_eq_smul_of_det2_eq_zero {u w : Fin 2 → ℝ} (hu : u ≠ 0) (h : det2 w u = 0) :
    w = ((w 0 * u 0 + w 1 * u 1) / (u 0 ^ 2 + u 1 ^ 2)) • u := by
  have hu2 := (bdy_sq_pos hu).ne'
  unfold det2 at h
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination (u 1) * h
  · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination (-(u 0)) * h

/-- **Uniqueness of the support line.** If `γ` is a positively oriented regular `C¹`
parameterization of the boundary of `K ∈ 𝔎_ccs` and `K` lies to the left of the line through
`γ(a)` in the direction `w ≠ 0`, then `w` is a positive multiple of `γ'(a)`. -/
lemma bdy_support_unique {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {γ : ℝ → Fin 2 → ℝ}
    (hγ : IsPositiveBoundaryParam K γ) (a : ℝ) {w : Fin 2 → ℝ} (hw0 : w ≠ 0)
    (hw : ∀ z ∈ K, 0 ≤ det2 w (z - γ a)) : ∃ c : ℝ, 0 < c ∧ w = c • deriv γ a := by
  have hdiff : Differentiable ℝ γ := hγ.1.differentiable (by norm_num)
  have hmin : IsLocalMin (fun t ↦ det2 w (γ t - γ a)) a := by
    refine Filter.Eventually.of_forall fun t ↦ ?_
    change det2 w (γ a - γ a) ≤ det2 w (γ t - γ a)
    rw [sub_self]
    simpa [det2] using hw _ (bdy_mem hK hγ t)
  have hwu : det2 w (deriv γ a) = 0 :=
    IsLocalMin.hasDerivAt_eq_zero hmin (bdy_hasDerivAt_det2 _ _ (hdiff a).hasDerivAt)
  have hu := hγ.2.1 a
  set c := (w 0 * deriv γ a 0 + w 1 * deriv γ a 1) / (deriv γ a 0 ^ 2 + deriv γ a 1 ^ 2)
  have hwc : w = c • deriv γ a := bdy_eq_smul_of_det2_eq_zero hu hwu
  refine ⟨c, ?_, hwc⟩
  -- the sign: `0 ∈ K` lies to the left of the line
  have h0 := hw 0 (bdy_zero_mem hK)
  have hor := hγ.2.2.2 a
  have : det2 w (0 - γ a) = c * det2 (γ a) (deriv γ a) := by
    rw [hwc]; simp only [det2, Pi.smul_apply, Pi.sub_apply, Pi.zero_apply, smul_eq_mul]; ring
  rw [this] at h0
  have hc0 : 0 ≤ c := nonneg_of_mul_nonneg_left h0 hor
  rcases hc0.lt_or_eq with h | h
  · exact h
  · exact absurd (by rw [hwc, ← h, zero_smul]) hw0

open Classical in
/-- The unit (for the sup norm) tangent vector of the boundary of `K` at a point `x`, read off a
positively oriented parameterization `γ` of the boundary. -/
noncomputable def bdy_tangent (γ : ℝ → Fin 2 → ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  if h : ∃ a, γ a = x then ‖deriv γ h.choose‖⁻¹ • deriv γ h.choose else 0

/-- The tangent `bdy_tangent γ x` at a boundary point `x`: a unit vector, `K` lies to its left,
and it turns counterclockwise about the origin. -/
lemma bdy_tangent_spec {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {γ : ℝ → Fin 2 → ℝ}
    (hγ : IsPositiveBoundaryParam K γ) {x : Fin 2 → ℝ} (hx : x ∈ frontier K) :
    ‖bdy_tangent γ x‖ = 1 ∧ (∀ z ∈ K, 0 ≤ det2 (bdy_tangent γ x) (z - x)) ∧
      0 < det2 x (bdy_tangent γ x) := by
  have hex : ∃ a, γ a = x := by rw [← mem_range, hγ.2.2.1]; exact hx
  have hU : bdy_tangent γ x = ‖deriv γ hex.choose‖⁻¹ • deriv γ hex.choose := by
    rw [bdy_tangent, dite_eq_left hex]
  have ha := hex.choose_spec
  set a := hex.choose
  have hu := hγ.2.1 a
  have hn : 0 < ‖deriv γ a‖ := norm_pos_iff.2 hu
  rw [hU]
  refine ⟨?_, fun z hz ↦ ?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  · have := bdy_det2_deriv_sub_nonneg hK hγ a hz
    rw [ha] at this
    have e : det2 (‖deriv γ a‖⁻¹ • deriv γ a) (z - x) =
        ‖deriv γ a‖⁻¹ * det2 (deriv γ a) (z - x) := by
      simp only [det2, Pi.smul_apply, smul_eq_mul]; ring
    rw [e]
    exact mul_nonneg (inv_nonneg.2 hn.le) this
  · have := hγ.2.2.2 a
    rw [ha] at this
    have e : det2 x (‖deriv γ a‖⁻¹ • deriv γ a) = ‖deriv γ a‖⁻¹ * det2 x (deriv γ a) := by
      simp only [det2, Pi.smul_apply, smul_eq_mul]; ring
    rw [e]
    exact mul_pos (inv_pos.2 hn) this

/-- The unit tangent at a boundary point is unique: it is the only unit vector `w` such that `K`
lies to the left of the line through `x` in the direction `w`. -/
lemma bdy_tangent_unique {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {γ : ℝ → Fin 2 → ℝ}
    (hγ : IsPositiveBoundaryParam K γ) {x : Fin 2 → ℝ} (hx : x ∈ frontier K)
    {w : Fin 2 → ℝ} (hw1 : ‖w‖ = 1) (hw : ∀ z ∈ K, 0 ≤ det2 w (z - x)) :
    w = bdy_tangent γ x := by
  have hex : ∃ a, γ a = x := by rw [← mem_range, hγ.2.2.1]; exact hx
  have hU : bdy_tangent γ x = ‖deriv γ hex.choose‖⁻¹ • deriv γ hex.choose := by
    rw [bdy_tangent, dite_eq_left hex]
  have ha := hex.choose_spec
  set a := hex.choose
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw1
  obtain ⟨c, hc, hwc⟩ := bdy_support_unique hK hγ a hw0 (by rw [ha]; exact hw)
  have hn : 0 < ‖deriv γ a‖ := norm_pos_iff.2 (hγ.2.1 a)
  have hc' : c = ‖deriv γ a‖⁻¹ := by
    rw [hwc, norm_smul, Real.norm_of_nonneg hc.le] at hw1
    field_simp
    linarith
  rw [hU, hwc, hc']

/-- The unit tangent varies continuously along a continuous curve on the boundary: a limit of
support lines is a support line, and the support line at each boundary point is unique. -/
lemma bdy_continuous_tangent {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {γ : ℝ → Fin 2 → ℝ}
    (hγ : IsPositiveBoundaryParam K γ) {τ : ℝ → Fin 2 → ℝ} (hτ : Continuous τ)
    (hτK : ∀ t, τ t ∈ frontier K) : Continuous fun t ↦ bdy_tangent γ (τ t) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  refine (isCompact_sphere (0 : Fin 2 → ℝ) 1).tendsto_nhds_of_unique_mapClusterPt
    (Filter.Eventually.of_forall fun t ↦ ?_) fun w hw hclus ↦ ?_
  · simpa using (bdy_tangent_spec hK hγ (hτK t)).1
  · rw [mem_sphere_zero_iff_norm] at hw
    refine bdy_tangent_unique hK hγ (hτK t₀) hw fun z hz ↦ ?_
    by_contra hneg
    push Not at hneg
    -- `(t, w') ↦ det(w', z - τ t)` is negative near `(t₀, w)`
    have hcont : Continuous fun p : ℝ × (Fin 2 → ℝ) ↦ det2 p.2 (z - τ p.1) := by
      unfold det2; fun_prop
    have hopen : {p : ℝ × (Fin 2 → ℝ) | det2 p.2 (z - τ p.1) < 0} ∈ 𝓝 (t₀, w) :=
      (isOpen_lt hcont continuous_const).mem_nhds hneg
    obtain ⟨V, hV, W, hW, hVW⟩ := mem_nhds_prod_iff.1 hopen
    have hfreq := (mapClusterPt_iff_frequently.1 hclus) W hW
    obtain ⟨t, htW, htV⟩ := (hfreq.and_eventually hV).exists
    have h1 : det2 (bdy_tangent γ (τ t)) (z - τ t) < 0 :=
      hVW (show (t, bdy_tangent γ (τ t)) ∈ V ×ˢ W from ⟨htV, htW⟩)
    have h2 := (bdy_tangent_spec hK hγ (hτK t)).2.1 z hz
    linarith

/-! ### Differentiability of boundary curves with an area constraint -/

/-- `|det(a, b)| ≤ 2 ‖a‖ ‖b‖` for the sup norm. -/
lemma bdy_abs_det2_le (a b : Fin 2 → ℝ) : |det2 a b| ≤ 2 * ‖a‖ * ‖b‖ := by
  have ha0 : |a 0| ≤ ‖a‖ := by simpa using norm_le_pi_norm a 0
  have ha1 : |a 1| ≤ ‖a‖ := by simpa using norm_le_pi_norm a 1
  have hb0 : |b 0| ≤ ‖b‖ := by simpa using norm_le_pi_norm b 0
  have hb1 : |b 1| ≤ ‖b‖ := by simpa using norm_le_pi_norm b 1
  unfold det2
  calc |a 0 * b 1 - a 1 * b 0| ≤ |a 0 * b 1| + |a 1 * b 0| := abs_sub _ _
    _ = |a 0| * |b 1| + |a 1| * |b 0| := by rw [abs_mul, abs_mul]
    _ ≤ ‖a‖ * ‖b‖ + ‖a‖ * ‖b‖ :=
        add_le_add (mul_le_mul ha0 hb1 (abs_nonneg _) (norm_nonneg _))
          (mul_le_mul ha1 hb0 (abs_nonneg _) (norm_nonneg _))
    _ = 2 * ‖a‖ * ‖b‖ := by ring

/-- `det` is jointly continuous. -/
lemma bdy_tendsto_det2 {α : Type*} {l : Filter α} {X Y : α → Fin 2 → ℝ} {x y : Fin 2 → ℝ}
    (hX : Tendsto X l (𝓝 x)) (hY : Tendsto Y l (𝓝 y)) :
    Tendsto (fun a ↦ det2 (X a) (Y a)) l (𝓝 (det2 x y)) := by
  have hX0 := tendsto_pi_nhds.1 hX 0
  have hX1 := tendsto_pi_nhds.1 hX 1
  have hY0 := tendsto_pi_nhds.1 hY 0
  have hY1 := tendsto_pi_nhds.1 hY 1
  exact (hX0.mul hY1).sub (hX1.mul hY0)

/-- `det` of continuous curves is continuous. -/
lemma bdy_continuous_det2 {X Y : ℝ → Fin 2 → ℝ} (hX : Continuous X) (hY : Continuous Y) :
    Continuous fun t ↦ det2 (X t) (Y t) :=
  continuous_iff_continuousAt.2 fun t ↦ bdy_tendsto_det2 (hX.tendsto t) (hY.tendsto t)

/-- **Differentiability of a boundary curve with an area constraint** (the proof of Lemma 2.4.2).
Let `γ` be a positively oriented regular `C¹` parameterization of the boundary of `K ∈ 𝔎_ccs`,
and `τ` a continuous curve on the boundary with `det(γ(t), τ(t))` constant. If
`det(γ(t), u(t)) ≠ 0`, where `u(t)` is the unit tangent of the boundary at `τ(t)`, then `τ` is
differentiable at `t` with `τ'(t) = s u(t)`, where `det(γ'(t), τ(t)) + det(γ(t), u(t)) s = 0`
(equation `eqn:sB`).

The chord `Δ = τ(t + h) - τ(t)` lies between the tangent lines at its two ends (both support
`K`), so `det(u(t), Δ) = o(|Δ|)`, as `u` is continuous; and differentiating the area relation,
`det(γ(t), Δ/h) → -det(γ'(t), τ(t))`. In the basis `u(t), γ(t)` this gives `Δ/h → s u(t)`. -/
lemma bdy_hasDerivAt_of_det2_const {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K)
    {γ : ℝ → Fin 2 → ℝ} (hγ : IsPositiveBoundaryParam K γ) {τ : ℝ → Fin 2 → ℝ}
    (hτ : Continuous τ) (hτK : ∀ t, τ t ∈ frontier K) {c : ℝ}
    (hc : ∀ t, det2 (γ t) (τ t) = c) {t : ℝ} (hb : det2 (γ t) (bdy_tangent γ (τ t)) ≠ 0) :
    HasDerivAt τ ((-det2 (deriv γ t) (τ t) / det2 (γ t) (bdy_tangent γ (τ t))) •
      bdy_tangent γ (τ t)) t := by
  set u := bdy_tangent γ (τ t) with hu_def
  set p := γ t with hp_def
  set D := det2 u p with hD_def
  have hDp : D = -det2 p u := by simp only [D, det2]; ring
  have hD : D ≠ 0 := by rw [hDp, neg_ne_zero]; exact hb
  have hDpos : 0 < |D| := abs_pos.2 hD
  have hdiff : Differentiable ℝ γ := hγ.1.differentiable (by norm_num)
  have hUc := bdy_continuous_tangent hK hγ hτ hτK
  have hu1 : ‖u‖ = 1 := (bdy_tangent_spec hK hγ (hτK t)).1
  rw [hasDerivAt_iff_tendsto_slope_zero]
  set q : ℝ → Fin 2 → ℝ := fun h ↦ h⁻¹ • (τ (t + h) - τ t) with hq
  set A : ℝ → ℝ := fun h ↦ det2 u (q h) / D with hA
  set B : ℝ → ℝ := fun h ↦ det2 (q h) p / D with hB
  have hqAB : q = fun h ↦ A h • p + B h • u := funext fun h ↦ bdy_cramer (q h) hD
  -- `B` converges, by differentiating the area relation
  have hBeq : ∀ h, det2 (q h) p = det2 (h⁻¹ • (γ (t + h) - γ t)) (τ (t + h)) := by
    intro h
    have e1 := hc (t + h)
    have e2 := hc t
    simp only [q, det2, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at e1 e2 ⊢
    linear_combination h⁻¹ * e2 - h⁻¹ * e1
  have hτlim : Tendsto (fun h ↦ τ (t + h)) (𝓝[≠] 0) (𝓝 (τ t)) := by
    have : Tendsto (fun h ↦ τ (t + h)) (𝓝 0) (𝓝 (τ (t + 0))) :=
      ((hτ.comp (continuous_const.add continuous_id)).tendsto 0)
    rw [add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hBlim : Tendsto B (𝓝[≠] 0) (𝓝 (det2 (deriv γ t) (τ t) / D)) := by
    have : B = fun h ↦ det2 (h⁻¹ • (γ (t + h) - γ t)) (τ (t + h)) / D :=
      funext fun h ↦ by simp only [B, hBeq]
    rw [this]
    exact (bdy_tendsto_det2 (hdiff t).hasDerivAt.tendsto_slope_zero hτlim).div_const D
  -- the chord lies between the tangent lines at its ends
  set E : ℝ → ℝ := fun h ↦ 2 * ‖u - bdy_tangent γ (τ (t + h))‖ with hE
  have hElim : Tendsto E (𝓝[≠] 0) (𝓝 0) := by
    have h1 : Tendsto (fun h ↦ bdy_tangent γ (τ (t + h))) (𝓝 0) (𝓝 u) := by
      have := (hUc.comp ((continuous_const (y := t)).add continuous_id)).tendsto 0
      simpa [Function.comp_def, hu_def] using this
    have h2 : Tendsto (fun h ↦ 2 * ‖u - bdy_tangent γ (τ (t + h))‖) (𝓝 0) (𝓝 (2 * ‖u - u‖)) :=
      (tendsto_const_nhds.sub h1).norm.const_mul 2
    simpa using h2.mono_left nhdsWithin_le_nhds
  have hdetq : ∀ h, |det2 u (q h)| ≤ E h * ‖q h‖ := by
    intro h
    set U' := bdy_tangent γ (τ (t + h))
    have h1 : 0 ≤ det2 u (τ (t + h) - τ t) :=
      (bdy_tangent_spec hK hγ (hτK t)).2.1 _ (hK.2.1.isClosed.frontier_subset (hτK (t + h)))
    have h2 : 0 ≤ det2 U' (τ t - τ (t + h)) :=
      (bdy_tangent_spec hK hγ (hτK (t + h))).2.1 _ (hK.2.1.isClosed.frontier_subset (hτK t))
    have h3 : det2 u (τ (t + h) - τ t) ≤ det2 (u - U') (τ (t + h) - τ t) := by
      have : det2 (u - U') (τ (t + h) - τ t) =
          det2 u (τ (t + h) - τ t) + det2 U' (τ t - τ (t + h)) := by
        simp only [det2, Pi.sub_apply]; ring
      linarith
    have h4 := bdy_abs_det2_le (u - U') (τ (t + h) - τ t)
    have e1 : det2 u (q h) = h⁻¹ * det2 u (τ (t + h) - τ t) := by
      simp only [q, det2, Pi.smul_apply, smul_eq_mul]; ring
    have e2 : ‖q h‖ = |h⁻¹| * ‖τ (t + h) - τ t‖ := by
      simp only [q, norm_smul, Real.norm_eq_abs]
    rw [e1, e2, abs_mul, abs_of_nonneg h1]
    calc |h⁻¹| * det2 u (τ (t + h) - τ t)
        ≤ |h⁻¹| * (2 * ‖u - U'‖ * ‖τ (t + h) - τ t‖) :=
          mul_le_mul_of_nonneg_left (h3.trans ((le_abs_self _).trans h4)) (abs_nonneg _)
      _ = E h * (|h⁻¹| * ‖τ (t + h) - τ t‖) := by simp only [E, U']; ring
  -- hence `A → 0`
  have hpos : 0 < |D| / (2 * (‖p‖ + 1)) := div_pos hDpos (by positivity)
  have hAbound : ∀ᶠ h in 𝓝[≠] 0, ‖A h‖ ≤ 2 * E h * |B h| / |D| := by
    filter_upwards [hElim.eventually (gt_mem_nhds hpos)] with h hEh
    have hE0 : 0 ≤ E h := by simp only [E]; positivity
    have hqn : ‖q h‖ ≤ |A h| * ‖p‖ + |B h| := by
      rw [hqAB]
      calc ‖A h • p + B h • u‖ ≤ ‖A h • p‖ + ‖B h • u‖ := norm_add_le _ _
        _ = |A h| * ‖p‖ + |B h| := by rw [norm_smul, norm_smul, hu1, Real.norm_eq_abs,
            Real.norm_eq_abs, mul_one]
    have hAD : |A h| * |D| = |det2 u (q h)| := by
      simp only [A, abs_div]; field_simp
    have h1 : |A h| * |D| ≤ E h * (|A h| * ‖p‖ + |B h|) := by
      rw [hAD]; exact (hdetq h).trans (mul_le_mul_of_nonneg_left hqn hE0)
    have h2 : E h * ‖p‖ ≤ |D| / 2 := by
      have := hEh
      rw [lt_div_iff₀ (by positivity)] at this
      nlinarith [norm_nonneg p]
    rw [Real.norm_eq_abs, le_div_iff₀ hDpos]
    nlinarith [abs_nonneg (A h), abs_nonneg (B h)]
  have hAlim : Tendsto A (𝓝[≠] 0) (𝓝 0) := by
    refine squeeze_zero_norm' hAbound ?_
    have := ((hElim.const_mul 2).mul hBlim.abs).div_const |D|
    simpa [mul_assoc] using this
  -- conclusion
  rw [hqAB]
  have := (hAlim.smul_const p).add (hBlim.smul_const u)
  rw [zero_smul, zero_add] at this
  convert this using 2
  rw [hDp, div_neg, neg_div]

/-- The curve `τ` of `bdy_hasDerivAt_of_det2_const` is `C¹` when `det(γ, u) ≠ 0` everywhere. -/
lemma bdy_contDiff_of_det2_const {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K)
    {γ : ℝ → Fin 2 → ℝ} (hγ : IsPositiveBoundaryParam K γ) {τ : ℝ → Fin 2 → ℝ}
    (hτ : Continuous τ) (hτK : ∀ t, τ t ∈ frontier K) {c : ℝ}
    (hc : ∀ t, det2 (γ t) (τ t) = c) (hb : ∀ t, det2 (γ t) (bdy_tangent γ (τ t)) ≠ 0) :
    ContDiff ℝ 1 τ ∧ ∀ t, deriv τ t = (-det2 (deriv γ t) (τ t) /
      det2 (γ t) (bdy_tangent γ (τ t))) • bdy_tangent γ (τ t) := by
  have hd := fun t ↦ bdy_hasDerivAt_of_det2_const hK hγ hτ hτK hc (hb t)
  have hderiv : ∀ t, deriv τ t = (-det2 (deriv γ t) (τ t) /
      det2 (γ t) (bdy_tangent γ (τ t))) • bdy_tangent γ (τ t) := fun t ↦ (hd t).deriv
  refine ⟨contDiff_one_iff_deriv.2 ⟨fun t ↦ (hd t).differentiableAt, ?_⟩, hderiv⟩
  rw [funext hderiv]
  have hUc := bdy_continuous_tangent hK hγ hτ hτK
  have hγc : Continuous γ := hγ.1.continuous
  have hγ'c : Continuous (deriv γ) := hγ.1.continuous_deriv le_rfl
  exact (((bdy_continuous_det2 hγ'c hτ).neg).div (bdy_continuous_det2 hγc hUc) hb).smul hUc

/-! ### Critical hexagons of a worst disk: multi-points up to scale -/

/-- Two sequences `x, y : ℤ/6ℤ → ℝ²` with `x_{k+1} = x_k + x_{k+2}` that agree at `0` and `1`
agree everywhere. -/
lemma bdy_seq_eq {x y : ZMod 6 → Fin 2 → ℝ} (hx : ∀ k, x (k + 1) = x k + x (k + 2))
    (hy : ∀ k, y (k + 1) = y k + y (k + 2)) (h0 : x 0 = y 0) (h1 : x 1 = y 1) :
    ∀ k, x k = y k := by
  have hx0 := hx 0; have hx1 := hx 1; have hx2 := hx 2; have hx3 := hx 3
  have hy0 := hy 0; have hy1 := hy 1; have hy2 := hy 2; have hy3 := hy 3
  norm_num at hx0 hx1 hx2 hx3 hy0 hy1 hy2 hy3
  have e2 : x 2 = y 2 := by
    have := hx0; rw [h0, h1] at this; rw [hy0] at this; exact (add_left_cancel this).symm
  have e3 : x 3 = y 3 := by
    have := hx1; rw [h1, e2, hy1] at this; exact (add_left_cancel this).symm
  have e4 : x 4 = y 4 := by
    have := hx2; rw [e2, e3, hy2] at this; exact (add_left_cancel this).symm
  have e5 : x 5 = y 5 := by
    have := hx3; rw [e3, e4, hy3] at this; exact (add_left_cancel this).symm
  intro k
  fin_cases k
  · exact h0
  · exact h1
  · exact e2
  · exact e3
  · exact e4
  · exact e5

private lemma bdy_sixthRoot_eq (k : ZMod 6) (n : ℕ) (hn : k.val = n) :
    sixthRoot k = ![Real.cos (Real.pi * n / 3), Real.sin (Real.pi * n / 3)] := by
  rw [sixthRoot, hn]

/-- The sixth roots of unity form a multi-point. -/
lemma bdy_isMultiPoint_sixthRoot : IsMultiPoint sixthRoot := by
  have s0 : sixthRoot 0 = ![1, 0] := by rw [bdy_sixthRoot_eq 0 0 rfl]; simp
  have s1 : sixthRoot 1 = ![1 / 2, √3 / 2] := by rw [bdy_sixthRoot_eq 1 1 rfl]; simp
  have s2 : sixthRoot 2 = ![-(1 / 2), √3 / 2] := by
    rw [bdy_sixthRoot_eq 2 2 rfl]
    have : Real.pi * (2 : ℕ) / 3 = Real.pi - Real.pi / 3 := by push_cast; ring
    rw [this, Real.cos_pi_sub, Real.sin_pi_sub]; simp
  have s3 : sixthRoot 3 = ![-1, 0] := by
    rw [bdy_sixthRoot_eq 3 3 rfl]
    have : Real.pi * (3 : ℕ) / 3 = Real.pi := by push_cast; ring
    rw [this]; simp
  have s4 : sixthRoot 4 = ![-(1 / 2), -(√3 / 2)] := by
    rw [bdy_sixthRoot_eq 4 4 rfl]
    have : Real.pi * (4 : ℕ) / 3 = Real.pi / 3 + Real.pi := by push_cast; ring
    rw [this, Real.cos_add_pi, Real.sin_add_pi]; simp
  have s5 : sixthRoot 5 = ![1 / 2, -(√3 / 2)] := by
    rw [bdy_sixthRoot_eq 5 5 rfl]
    have : Real.pi * (5 : ℕ) / 3 = -(Real.pi / 3) + 2 * Real.pi := by push_cast; ring
    rw [this, Real.cos_add_two_pi, Real.sin_add_two_pi, Real.cos_neg, Real.sin_neg]; simp
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  intro j
  fin_cases j
  on_goal 1 => change sixthRoot 0 + sixthRoot 2 + sixthRoot 4 = 0 ∧ sixthRoot 3 = -sixthRoot 0 ∧
                    det2 (sixthRoot 0) (sixthRoot 1) = √3 / 2
  on_goal 2 => change sixthRoot 1 + sixthRoot 3 + sixthRoot 5 = 0 ∧ sixthRoot 4 = -sixthRoot 1 ∧
                    det2 (sixthRoot 1) (sixthRoot 2) = √3 / 2
  on_goal 3 => change sixthRoot 2 + sixthRoot 4 + sixthRoot 0 = 0 ∧ sixthRoot 5 = -sixthRoot 2 ∧
                    det2 (sixthRoot 2) (sixthRoot 3) = √3 / 2
  on_goal 4 => change sixthRoot 3 + sixthRoot 5 + sixthRoot 1 = 0 ∧ sixthRoot 0 = -sixthRoot 3 ∧
                    det2 (sixthRoot 3) (sixthRoot 4) = √3 / 2
  on_goal 5 => change sixthRoot 4 + sixthRoot 0 + sixthRoot 2 = 0 ∧ sixthRoot 1 = -sixthRoot 4 ∧
                    det2 (sixthRoot 4) (sixthRoot 5) = √3 / 2
  on_goal 6 => change sixthRoot 5 + sixthRoot 1 + sixthRoot 3 = 0 ∧ sixthRoot 2 = -sixthRoot 5 ∧
                    det2 (sixthRoot 5) (sixthRoot 0) = √3 / 2
  all_goals
    simp only [s0, s1, s2, s3, s4, s5, det2]
    refine ⟨?_, ?_, ?_⟩
    · ext i; fin_cases i <;> norm_num
    · ext i; fin_cases i <;> simp
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; linarith [h3]

/-- The edge midpoints of a centrally symmetric hexagon: `m_{j+3} = -m_j`. -/
lemma bdy_hexMidpoint_add_three {v : ZMod 6 → Fin 2 → ℝ} (hv : IsCSHexagon v) (j : ZMod 6) :
    hexMidpoint v (j + 3) = -hexMidpoint v j := by
  have h1 := (hv j).1
  have h2 := (hv (j + 1)).1
  rw [show j + 1 + 3 = j + 3 + 1 by ring] at h2
  simp only [hexMidpoint, midpoint_eq_smul_add, h1, h2]
  rw [← neg_add, smul_neg]

/-- The edge midpoints of a centrally symmetric hexagon: `m_{j+1} = m_j + m_{j+2}`. -/
lemma bdy_hexMidpoint_succ {v : ZMod 6 → Fin 2 → ℝ} (hv : IsCSHexagon v) (j : ZMod 6) :
    hexMidpoint v (j + 1) = hexMidpoint v j + hexMidpoint v (j + 2) := by
  have h1 := (hv j).1
  simp only [hexMidpoint, midpoint_eq_smul_add]
  rw [show j + 2 + 1 = j + 3 by ring, h1, show j + 1 + 1 = j + 2 by ring, ← smul_add]
  congr 1
  abel

/-- The edge midpoints of a centrally symmetric hexagon turn counterclockwise:
`det(m_j, m_{j+1}) > 0`. -/
lemma bdy_det2_hexMidpoint_pos {v : ZMod 6 → Fin 2 → ℝ} (hv : IsCSHexagon v) (j : ZMod 6) :
    0 < det2 (hexMidpoint v j) (hexMidpoint v (j + 1)) := by
  have h01 := (hv j).2.1
  have h12 := (hv (j + 1)).2.1
  have h23 := (hv (j + 2)).2.1
  have e3 := (hv j).1
  rw [show j + 1 + 1 = j + 2 by ring] at h12
  rw [show j + 2 + 1 = j + 3 by ring, e3] at h23
  simp only [hexMidpoint, midpoint_eq_smul_add, show j + 1 + 1 = j + 2 by ring]
  simp only [det2, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, smul_eq_mul, invOf_eq_inv]
    at h01 h12 h23 ⊢
  nlinarith

/-! ### Linear normalization -/

/-- The linear map sending `m₀ ↦ s₀` and `m₁ ↦ s₁` (for bases `m₀, m₁` and `s₀, s₁`). -/
noncomputable def bdy_linMap (m₀ m₁ s₀ s₁ : Fin 2 → ℝ) : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun x := (det2 x m₁ / det2 m₀ m₁) • s₀ + (det2 m₀ x / det2 m₀ m₁) • s₁
  map_add' x y := by
    ext i; simp only [det2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  map_smul' c x := by
    ext i; simp only [det2, Pi.add_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

lemma bdy_linMap_apply (m₀ m₁ s₀ s₁ x : Fin 2 → ℝ) :
    bdy_linMap m₀ m₁ s₀ s₁ x = (det2 x m₁ / det2 m₀ m₁) • s₀ + (det2 m₀ x / det2 m₀ m₁) • s₁ :=
  rfl

lemma bdy_linMap_left {m₀ m₁ : Fin 2 → ℝ} (hm : det2 m₀ m₁ ≠ 0) (s₀ s₁ : Fin 2 → ℝ) :
    bdy_linMap m₀ m₁ s₀ s₁ m₀ = s₀ := by
  rw [bdy_linMap_apply, div_self hm]
  have : det2 m₀ m₀ = 0 := by unfold det2; ring
  rw [this, zero_div, zero_smul, add_zero, one_smul]

lemma bdy_linMap_right {m₀ m₁ : Fin 2 → ℝ} (hm : det2 m₀ m₁ ≠ 0) (s₀ s₁ : Fin 2 → ℝ) :
    bdy_linMap m₀ m₁ s₀ s₁ m₁ = s₁ := by
  rw [bdy_linMap_apply, div_self hm]
  have : det2 m₁ m₁ = 0 := by unfold det2; ring
  rw [this, zero_div, zero_smul, zero_add, one_smul]

lemma bdy_linMap_comp {m₀ m₁ s₀ s₁ : Fin 2 → ℝ} (hm : det2 m₀ m₁ ≠ 0) (hs : det2 s₀ s₁ ≠ 0)
    (y : Fin 2 → ℝ) : bdy_linMap m₀ m₁ s₀ s₁ (bdy_linMap s₀ s₁ m₀ m₁ y) = y := by
  rw [bdy_linMap_apply s₀ s₁ m₀ m₁ y, map_add, map_smul, map_smul, bdy_linMap_left hm,
    bdy_linMap_right hm, add_comm]
  exact (bdy_cramer y hs).symm

/-- The normalization `A` with `A m₀ = s₀`, `A m₁ = s₁`, as a continuous linear equivalence. -/
noncomputable def bdy_normalize {m₀ m₁ s₀ s₁ : Fin 2 → ℝ} (hm : det2 m₀ m₁ ≠ 0)
    (hs : det2 s₀ s₁ ≠ 0) : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ) :=
  (LinearEquiv.ofLinearMap (bdy_linMap m₀ m₁ s₀ s₁) (bdy_linMap s₀ s₁ m₀ m₁)
    (LinearMap.ext fun y ↦ bdy_linMap_comp hm hs y)
    (LinearMap.ext fun y ↦ bdy_linMap_comp hs hm y)).toContinuousLinearEquiv

lemma bdy_normalize_apply {m₀ m₁ s₀ s₁ : Fin 2 → ℝ} (hm : det2 m₀ m₁ ≠ 0)
    (hs : det2 s₀ s₁ ≠ 0) (x : Fin 2 → ℝ) :
    bdy_normalize hm hs x = bdy_linMap m₀ m₁ s₀ s₁ x := rfl

lemma bdy_normalize_zero {m₀ m₁ s₀ s₁ : Fin 2 → ℝ} (hm : det2 m₀ m₁ ≠ 0)
    (hs : det2 s₀ s₁ ≠ 0) : bdy_normalize hm hs m₀ = s₀ :=
  bdy_linMap_left hm s₀ s₁

lemma bdy_normalize_one {m₀ m₁ s₀ s₁ : Fin 2 → ℝ} (hm : det2 m₀ m₁ ≠ 0)
    (hs : det2 s₀ s₁ ≠ 0) : bdy_normalize hm hs m₁ = s₁ :=
  bdy_linMap_right hm s₀ s₁

lemma bdy_normalize_det2 {m₀ m₁ s₀ s₁ : Fin 2 → ℝ} (hm : det2 m₀ m₁ ≠ 0)
    (hs : det2 s₀ s₁ ≠ 0) (x y : Fin 2 → ℝ) :
    det2 (bdy_normalize hm hs x) (bdy_normalize hm hs y) =
      det2 s₀ s₁ / det2 m₀ m₁ * det2 x y := by
  simp only [bdy_normalize_apply, bdy_linMap_apply]
  have key : det2 x m₁ * det2 m₀ y - det2 m₀ x * det2 y m₁ = det2 m₀ m₁ * det2 x y := by
    unfold det2; ring
  have h2 : ∀ a b a' b' : ℝ, det2 (a • s₀ + b • s₁) (a' • s₀ + b' • s₁) =
      (a * b' - b * a') * det2 s₀ s₁ := by
    intro a b a' b'
    unfold det2; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [h2]
  field_simp
  linear_combination key

/-! ### Invariance under orientation-preserving linear maps -/

section Invariance

variable (A : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ)) {δ : ℝ}

/-- The determinant of a linear map of the plane scaling `det` by `δ` is `δ`. -/
lemma bdy_linearMap_det (hA : ∀ x y, det2 (A x) (A y) = δ * det2 x y) :
    LinearMap.det (A : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) = δ := by
  rw [← LinearMap.det_toMatrix', Matrix.det_fin_two]
  have := hA (Pi.single 0 1) (Pi.single 1 1)
  simp only [det2, Pi.single_apply] at this
  norm_num at this
  have e : ∀ x, (A : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) x = A x := fun x ↦ rfl
  simp only [LinearMap.toMatrix'_apply, e]
  linarith

lemma bdy_volume_image (hA : ∀ x y, det2 (A x) (A y) = δ * det2 x y) (S : Set (Fin 2 → ℝ)) :
    volume (A '' S) = ENNReal.ofReal |δ| * volume S := by
  rw [MeasureTheory.Measure.addHaar_image_continuousLinearEquiv, bdy_linearMap_det A hA]

lemma bdy_symm_det2 (hδ : δ ≠ 0) (hA : ∀ x y, det2 (A x) (A y) = δ * det2 x y) (x y : Fin 2 → ℝ) :
    det2 (A.symm x) (A.symm y) = δ⁻¹ * det2 x y := by
  have := hA (A.symm x) (A.symm y)
  simp only [ContinuousLinearEquiv.apply_symm_apply] at this
  rw [this]; field_simp

lemma bdy_isCCSDisk_image {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) : IsCCSDisk (A '' K) := by
  obtain ⟨hconv, hcomp, hint, hsymm⟩ := hK
  refine ⟨hconv.linear_image (A : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)), hcomp.image A.continuous, ?_,
    ?_⟩
  · have h := A.toHomeomorph.image_interior K
    simp only [ContinuousLinearEquiv.coe_toHomeomorph] at h
    rw [← h]; exact hint.image _
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨-x, hsymm x hx, map_neg A x⟩

lemma bdy_frontier_image (K : Set (Fin 2 → ℝ)) : frontier (A '' K) = A '' frontier K := by
  have h := A.toHomeomorph.image_frontier K
  simp only [ContinuousLinearEquiv.coe_toHomeomorph] at h
  exact h.symm

lemma bdy_hexMidpoint_comp (v : ZMod 6 → Fin 2 → ℝ) (j : ZMod 6) :
    hexMidpoint (fun k ↦ A (v k)) j = A (hexMidpoint v j) := by
  simp only [hexMidpoint, midpoint_eq_smul_add, map_smul, map_add]

lemma bdy_hexagonOf_comp (v : ZMod 6 → Fin 2 → ℝ) :
    hexagonOf (fun k ↦ A (v k)) = A '' hexagonOf v := by
  rw [hexagonOf, hexagonOf]
  have h : (A : (Fin 2 → ℝ) → (Fin 2 → ℝ)) '' convexHull ℝ (range v) =
      convexHull ℝ (A '' range v) :=
    LinearMap.image_convexHull (A : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) (range v)
  rw [h, ← range_comp]
  rfl

lemma bdy_isCSHexagon_comp (hδ : 0 < δ) (hA : ∀ x y, det2 (A x) (A y) = δ * det2 x y)
    {v : ZMod 6 → Fin 2 → ℝ} (hv : IsCSHexagon v) : IsCSHexagon fun k ↦ A (v k) := by
  intro j
  obtain ⟨h1, h2, h3⟩ := hv j
  refine ⟨by simp [h1], by rw [hA]; positivity, ?_⟩
  rw [← map_sub, ← map_sub, hA]
  positivity

lemma bdy_isLeastAreaHexagon_image (hδ : 0 < δ) (hA : ∀ x y, det2 (A x) (A y) = δ * det2 x y)
    {K : Set (Fin 2 → ℝ)} {v : ZMod 6 → Fin 2 → ℝ} (hv : IsLeastAreaHexagon K v) :
    IsLeastAreaHexagon (A '' K) fun k ↦ A (v k) := by
  obtain ⟨hcs, hsub, hmin⟩ := hv
  refine ⟨bdy_isCSHexagon_comp A hδ hA hcs, ?_, fun w hw hKw ↦ ?_⟩
  · rw [bdy_hexagonOf_comp]; exact image_mono hsub
  · have hA' := bdy_symm_det2 A hδ.ne' hA
    have hw' := bdy_isCSHexagon_comp A.symm (inv_pos.2 hδ) hA' hw
    have hKw' : K ⊆ hexagonOf fun k ↦ A.symm (w k) := by
      rw [bdy_hexagonOf_comp]
      intro x hx
      exact ⟨A x, hKw ⟨x, hx, rfl⟩, A.symm_apply_apply x⟩
    have := hmin _ hw' hKw'
    rw [bdy_hexagonOf_comp, bdy_volume_image A hA]
    have e : hexagonOf w = A '' hexagonOf fun k ↦ A.symm (w k) := by
      rw [bdy_hexagonOf_comp, ← image_comp]
      simp
    rw [e, bdy_volume_image A hA]
    gcongr

lemma bdy_isConvexDisk_image {K : Set (Fin 2 → ℝ)} (hK : IsConvexDisk K) :
    IsConvexDisk (A '' K) := by
  obtain ⟨hconv, hcomp, hint⟩ := hK
  refine ⟨hconv.linear_image (A : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)), hcomp.image A.continuous, ?_⟩
  have h := A.toHomeomorph.image_interior K
  simp only [ContinuousLinearEquiv.coe_toHomeomorph] at h
  rw [← h]; exact hint.image _

/-- A lattice packing `K + L` gives the lattice packing `A K + A L` of the same density. -/
lemma bdy_latticePacking_image (hδ : 0 < δ) (hA : ∀ x y, det2 (A x) (A y) = δ * det2 x y)
    {K : Set (Fin 2 → ℝ)} (hK : IsConvexDisk K) {L : Submodule ℤ (Fin 2 → ℝ)}
    (hL : IsPlaneLattice L) (hKL : IsLatticePacking K L) :
    ∃ L', IsPlaneLattice L' ∧ IsLatticePacking (A '' K) L' ∧
      latticePackingDensity (A '' K) L' = latticePackingDensity K L := by
  have : DiscreteTopology L := hL.1
  have : IsZLattice ℝ L := ⟨hL.2⟩
  set L' := ZLattice.comap ℝ L A.symm.toLinearMap with hL'_def
  have hmem : ∀ x, x ∈ L' ↔ A.symm x ∈ L := fun x ↦ Iff.rfl
  have hL' : IsPlaneLattice L' := ⟨inferInstance, IsZLattice.span_top⟩
  have hpack : IsLatticePacking (A '' K) L' := by
    intro l hl l' hl' hne
    have e1 : ∀ m, (fun x ↦ x + m) '' (A '' K) = A '' ((fun x ↦ x + A.symm m) '' K) := by
      intro m
      rw [← image_comp, ← image_comp]
      congr 1
      ext x
      simp
    have hint : ∀ S, interior (A '' S) = A '' interior S := by
      intro S
      have h := A.toHomeomorph.image_interior S
      simp only [ContinuousLinearEquiv.coe_toHomeomorph] at h
      exact h.symm
    rw [e1, e1, hint, hint]
    exact (disjoint_image_iff A.injective).2
      (hKL _ ((hmem l).1 hl) _ ((hmem l').1 hl') fun h ↦ hne (A.symm.injective h))
  refine ⟨L', hL', hpack, ?_⟩
  rw [ch2_latticePackingDensity_eq (bdy_isConvexDisk_image A hK) hL' hpack,
    ch2_latticePackingDensity_eq hK hL hKL]
  have hvol : volume.real (A '' K) = δ * volume.real K := by
    rw [measureReal_def, measureReal_def, bdy_volume_image A hA, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (abs_nonneg _), abs_of_pos hδ]
  have hdet : latticeDet L' = δ * latticeDet L := by
    have hrank : Module.finrank ℤ L = 2 := by rw [ZLattice.rank ℝ L]; simp
    let b : Module.Basis (Fin 2) ℤ L := Module.finBasisOfFinrankEq ℤ L hrank
    let b' := b.ofZLatticeComap ℝ L A.symm.toLinearEquiv
    rw [latticeDet, latticeDet, ZLattice.covolume_eq_det L' b', ZLattice.covolume_eq_det L b,
      Matrix.det_fin_two, Matrix.det_fin_two]
    have hb' : ∀ i, (b' i : Fin 2 → ℝ) = A (b i) := fun i ↦ by
      rw [Module.Basis.ofZLatticeComap_apply]
      rfl
    simp only [Matrix.of_apply, Function.comp_apply, hb']
    have := hA (b 0) (b 1)
    simp only [det2] at this
    rw [this, abs_mul, abs_of_pos hδ]
  rw [hvol, hdet]
  have : latticeDet L ≠ 0 := by rw [latticeDet]; exact (ZLattice.covolume_pos L volume).ne'
  field_simp

end Invariance

/-! ### Reindexing hexagons -/

lemma bdy_isLeastAreaHexagon_shift {K : Set (Fin 2 → ℝ)} {v : ZMod 6 → Fin 2 → ℝ}
    (hv : IsLeastAreaHexagon K v) (k : ZMod 6) : IsLeastAreaHexagon K fun j ↦ v (j + k) := by
  have hrange : hexagonOf (fun j ↦ v (j + k)) = hexagonOf v := by
    rw [hexagonOf, hexagonOf]
    congr 1
    exact (Equiv.addRight k).surjective.range_comp v
  obtain ⟨hcs, hsub, hmin⟩ := hv
  refine ⟨fun j ↦ ?_, hrange ▸ hsub, fun w hw hKw ↦ hrange ▸ hmin w hw hKw⟩
  obtain ⟨h1, h2, h3⟩ := hcs (j + k)
  refine ⟨?_, ?_, ?_⟩
  · simpa [add_right_comm] using h1
  · simpa [add_right_comm] using h2
  · simpa [add_right_comm] using h3

lemma bdy_hexMidpoint_shift (v : ZMod 6 → Fin 2 → ℝ) (k j : ZMod 6) :
    hexMidpoint (fun i ↦ v (i + k)) j = hexMidpoint v (j + k) := by
  simp only [hexMidpoint, add_right_comm]

/-! ### The triangle `T₀` -/

/-- A point of the open edge `s₀* s₁*` of `T₀` is not an interior point of `T₀`. -/
lemma bdy_not_mem_interior_sixthTriangle {p : Fin 2 → ℝ}
    (hp : p ∈ openSegment ℝ (sixthRoot 0) (sixthRoot 1)) : p ∉ interior (sixthTriangle 0) := by
  have hpos : det2 (sixthRoot 0) (sixthRoot 1) = √3 / 2 := (bdy_isMultiPoint_sixthRoot 0).2.2
  set w := sixthRoot 0 - sixthRoot 1
  have hw : w ≠ 0 := by
    intro h
    have : sixthRoot 0 = sixthRoot 1 := sub_eq_zero.1 h
    have h' : det2 (sixthRoot 0) (sixthRoot 1) = 0 := by rw [this]; unfold det2; ring
    rw [hpos] at h'
    have : (0 : ℝ) < √3 / 2 := by positivity
    linarith
  have hlin : IsLinearMap ℝ (det2 w) :=
    ⟨fun x y ↦ by simp only [det2, Pi.add_apply]; ring,
      fun c x ↦ by simp only [det2, Pi.smul_apply, smul_eq_mul]; ring⟩
  have h3 : (0 : ℝ) < √3 / 2 := by positivity
  refine bdy_not_mem_interior hw (c := det2 w (sixthRoot 0)) (fun z hz ↦ ?_) ?_
  · have hsub : sixthTriangle 0 ⊆ {z | det2 w (sixthRoot 0) ≤ det2 w z} := by
      refine convexHull_min ?_ (convex_halfSpace_ge hlin _)
      intro z hz
      simp only [zero_add, mem_insert_iff, mem_singleton_iff] at hz
      simp only [mem_ofPred_eq]
      rcases hz with rfl | rfl | rfl
      · exact le_rfl
      · simp only [w, det2, Pi.sub_apply] at hpos ⊢; nlinarith [hpos]
      · simp only [w, det2, Pi.sub_apply, Pi.add_apply] at hpos ⊢; nlinarith [hpos]
    exact hsub hz
  · obtain ⟨a, b, ha, hb, hab, rfl⟩ := hp
    simp only [w, det2, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hb' : b = 1 - a := by linarith
    subst hb'
    ring

section Invariance

variable (A : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ)) {δ : ℝ}

/-- The greatest lattice packing density is invariant under orientation-preserving linear maps. -/
lemma bdy_greatestLatticePackingDensity_image (hδ : 0 < δ)
    (hA : ∀ x y, det2 (A x) (A y) = δ * det2 x y) {K : Set (Fin 2 → ℝ)} (hK : IsConvexDisk K) :
    greatestLatticePackingDensity (A '' K) = greatestLatticePackingDensity K := by
  have hsub : ∀ (B : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ)) {ε : ℝ}, 0 < ε →
      (∀ x y, det2 (B x) (B y) = ε * det2 x y) → ∀ {K' : Set (Fin 2 → ℝ)}, IsConvexDisk K' →
      {d | ∃ L, IsPlaneLattice L ∧ IsLatticePacking K' L ∧ latticePackingDensity K' L = d} ⊆
        {d | ∃ L, IsPlaneLattice L ∧ IsLatticePacking (B '' K') L ∧
          latticePackingDensity (B '' K') L = d} := by
    rintro B ε hε hB K' hK' d ⟨L, hL, hKL, rfl⟩
    exact bdy_latticePacking_image B hε hB hK' hL hKL
  rw [greatestLatticePackingDensity, greatestLatticePackingDensity]
  congr 1
  apply Subset.antisymm
  · have := hsub A.symm (inv_pos.2 hδ) (bdy_symm_det2 A hδ.ne' hA) (bdy_isConvexDisk_image A hK)
    rwa [A.symm_image_image] at this
  · exact hsub A hδ hA hK

/-- The image of a worst disk under an orientation-preserving linear map is a worst disk. -/
lemma bdy_isWorstLatticeDisk_image (hδ : 0 < δ) (hA : ∀ x y, det2 (A x) (A y) = δ * det2 x y)
    {K : Set (Fin 2 → ℝ)} (hK : IsWorstLatticeDisk K) : IsWorstLatticeDisk (A '' K) := by
  obtain ⟨hK1, hK2⟩ := hK
  refine ⟨bdy_isCCSDisk_image A hK1, fun K' hK' ↦ ?_⟩
  rw [bdy_greatestLatticePackingDensity_image A hδ hA ⟨hK1.1, hK1.2.1, hK1.2.2.1⟩]
  exact hK2 K' hK'

end Invariance

/-- **No edge of an inscribed critical hexagon lies on the boundary** (the use of Lemma 2.2.6 in
the proof of Lemma 2.4.2). Let `K` have the worst greatest packing density and `v` be a critical
hexagon of `K`, with edge midpoints `m_j`. Then no point strictly between `m_j` and `m_{j+1}` lies
on the boundary of `K`. Normalize by the linear map `A` with `A m_j = s_j*` (circle
representation): a boundary point `A p` strictly between `s₀*` and `s₁*` is the midpoint of an edge
of a critical hexagon (Lemma 2.2.7), so by Lemma 2.2.6 it lies in the interior of `T₀`; but it lies
on the edge `s₀* s₁*` of `T₀`. -/
lemma bdy_not_mem_frontier_of_openSegment {K : Set (Fin 2 → ℝ)} (hK : IsWorstDisk K)
    {v : ZMod 6 → Fin 2 → ℝ} (hv : IsLeastAreaHexagon K v) (j : ZMod 6) {p : Fin 2 → ℝ}
    (hp : p ∈ openSegment ℝ (hexMidpoint v j) (hexMidpoint v (j + 1))) : p ∉ frontier K := by
  intro hpK
  set w := fun i ↦ v (i + j) with hw_def
  have hw := bdy_isLeastAreaHexagon_shift hv j
  have hwm : ∀ i, hexMidpoint w i = hexMidpoint v (i + j) := bdy_hexMidpoint_shift v j
  have hm0 : hexMidpoint w 0 = hexMidpoint v j := by rw [hwm, zero_add]
  have hm1 : hexMidpoint w 1 = hexMidpoint v (j + 1) := by rw [hwm, add_comm]
  have hcpos : 0 < det2 (hexMidpoint w 0) (hexMidpoint w 1) := by
    have := bdy_det2_hexMidpoint_pos hw.1 0; rwa [zero_add] at this
  have hc := hcpos.ne'
  have hs3 : det2 (sixthRoot 0) (sixthRoot 1) = √3 / 2 := (bdy_isMultiPoint_sixthRoot 0).2.2
  have hspos : 0 < det2 (sixthRoot 0) (sixthRoot 1) := by rw [hs3]; positivity
  have hs := hspos.ne'
  set A := bdy_normalize hc hs
  have hδ : 0 < det2 (sixthRoot 0) (sixthRoot 1) / det2 (hexMidpoint w 0) (hexMidpoint w 1) :=
    div_pos hspos hcpos
  have hA := bdy_normalize_det2 hc hs
  -- `A m_i = s_i*`
  have hAm : ∀ i, A (hexMidpoint w i) = sixthRoot i := by
    refine bdy_seq_eq (fun k ↦ ?_) (fun k ↦ bdy_mp_succ bdy_isMultiPoint_sixthRoot k)
      (bdy_normalize_zero hc hs) (bdy_normalize_one hc hs)
    rw [bdy_hexMidpoint_succ hw.1 k, map_add]
  -- the normalized disk is a worst disk with a critical hexagon in circle representation
  have hKL : IsWorstLatticeDisk (A '' K) :=
    bdy_isWorstLatticeDisk_image A hδ hA (ch2_isWorstLatticeDisk_iff_isWorstDisk.2 hK)
  have hK' : IsWorstDisk (A '' K) := ch2_isWorstLatticeDisk_iff_isWorstDisk.1 hKL
  have hstar : ∃ w', IsLeastAreaHexagon (A '' K) w' ∧ ∀ i, hexMidpoint w' i = sixthRoot i :=
    ⟨fun i ↦ A (w i), bdy_isLeastAreaHexagon_image A hδ hA hw,
      fun i ↦ by rw [bdy_hexMidpoint_comp, hAm]⟩
  -- `A p` is a boundary point strictly between `s₀*` and `s₁*`
  have hAp : A p ∈ openSegment ℝ (sixthRoot 0) (sixthRoot 1) := by
    rw [← hm0, ← hm1] at hp
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hp
    exact ⟨a, b, ha, hb, hab, by rw [map_add, map_smul, map_smul, hAm, hAm]⟩
  have hApK : A p ∈ frontier (A '' K) := by
    rw [bdy_frontier_image]; exact mem_image_of_mem A hpK
  -- `A p` is the midpoint of an edge of a critical hexagon (Lemma 2.2.7)
  obtain ⟨H, ⟨v', hv', -, k, hk⟩, -⟩ := (lemma2_2_7 hK').1 (A p) hApK
  have hv'' := bdy_isLeastAreaHexagon_shift hv' k
  have h0 : hexMidpoint (fun i ↦ v' (i + k)) 0 = A p := by
    rw [bdy_hexMidpoint_shift, zero_add, hk]
  have hne : sixthRoot 0 ≠ sixthRoot 1 := fun h ↦ hs (by rw [h]; unfold det2; ring)
  have hT : A p ∈ sixthTriangle 0 \ {sixthRoot 0, sixthRoot 1} := by
    refine ⟨?_, ?_⟩
    · have : segment ℝ (sixthRoot 0) (sixthRoot 1) ⊆ sixthTriangle 0 :=
        segment_subset_convexHull (by simp) (by simp)
      exact this (openSegment_subset_segment _ _ _ hAp)
    · simp only [mem_insert_iff, mem_singleton_iff, not_or]
      refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
      · rw [h] at hAp; exact hne (left_mem_openSegment_iff.1 hAp)
      · rw [h] at hAp; exact hne (right_mem_openSegment_iff.1 hAp)
  -- Lemma 2.2.6: `A p` lies in the interior of `T₀`
  have hint := lemma2_2_6 hKL hstar hv'' (h0 ▸ hT) 0
  rw [h0] at hint
  exact bdy_not_mem_interior_sixthTriangle hAp hint

/-! ### Multi-points on the boundary of a worst disk -/

/-- Points with equal `det(p, ·)` and `det(·, q)`, where `det(p, q) ≠ 0`, coincide. -/
lemma bdy_eq_of_det2_eq {p q x y : Fin 2 → ℝ} (hpq : det2 p q ≠ 0)
    (h1 : det2 p x = det2 p y) (h2 : det2 x q = det2 y q) : x = y := by
  refine sub_eq_zero.1 (bdy_eq_zero_of_det2 hpq ?_ ?_)
  · unfold det2 at *; simp only [Pi.sub_apply]; linarith
  · unfold det2 at *; simp only [Pi.sub_apply]; linarith

/-- On a line `det(p, ·) = const`, ordered by the coordinate `det(·, q)` (`det(p, q) ≠ 0`), a point
strictly between two others lies in the open segment between them. -/
lemma bdy_mem_openSegment {p q a x b : Fin 2 → ℝ} (hpq : det2 p q ≠ 0)
    (hx : det2 p x = det2 p a) (hb : det2 p b = det2 p a) (h1 : det2 a q < det2 x q)
    (h2 : det2 x q < det2 b q) : x ∈ openSegment ℝ a b := by
  have hden : 0 < det2 b q - det2 a q := by linarith
  set θ := (det2 x q - det2 a q) / (det2 b q - det2 a q) with hθ_def
  have hθ0 : 0 < θ := div_pos (by linarith) hden
  have hθ1 : θ < 1 := (div_lt_one hden).2 (by linarith)
  have hθ : θ * (det2 b q - det2 a q) = det2 x q - det2 a q := div_mul_cancel₀ _ hden.ne'
  refine ⟨1 - θ, θ, by linarith, hθ0, by ring, ?_⟩
  refine bdy_eq_of_det2_eq hpq ?_ ?_
  · simp only [det2, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hb ⊢
    linear_combination θ * hb - hx
  · simp only [det2, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hθ ⊢
    linear_combination hθ

/-- A boundary point strictly between two points of `K` on the line `det(p, ·) = h` makes this line
a support line; this is impossible if `K` has points on both sides of it. -/
lemma bdy_false_of_mem_openSegment {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K)
    {p a b y z₁ z₂ : Fin 2 → ℝ} {h : ℝ} (hp : p ≠ 0) (ha : a ∈ K) (hb : b ∈ K) (hab : a ≠ b)
    (hpa : det2 p a = h) (hpb : det2 p b = h) (hy : y ∈ openSegment ℝ a b)
    (hyK : y ∈ frontier K) (hz₁ : z₁ ∈ K) (hz₂ : z₂ ∈ K) (h₁ : det2 p z₁ < h)
    (h₂ : h < det2 p z₂) : False := by
  obtain ⟨f, hfi, hfK⟩ := bdy_exists_support hK hyK
  obtain ⟨hfa, hfb⟩ := bdy_support_eq_of_openSegment hfK ha hb hy
  -- `f` vanishes on `a - b`, a nonzero multiple of `p`
  have he : det2 (a - b) p = 0 := by unfold det2 at *; simp only [Pi.sub_apply]; linarith
  have hlam := bdy_eq_smul_of_det2_eq_zero hp he
  set c := ((a - b) 0 * p 0 + (a - b) 1 * p 1) / (p 0 ^ 2 + p 1 ^ 2)
  have hc0 : c ≠ 0 := fun h0 ↦ hab (sub_eq_zero.1 (by rw [hlam, h0, zero_smul]))
  have hfp : f p = 0 := by
    have : f (a - b) = 0 := by rw [map_sub, hfa, hfb, sub_self]
    rw [hlam, map_smul, smul_eq_mul] at this
    exact (mul_eq_zero.1 this).resolve_left hc0
  have key := bdy_dual_eq_det2 f hfp
  set κ := f (Pi.single 1 1) * p 0 - f (Pi.single 0 1) * p 1
  have hp2 := bdy_sq_pos hp
  have hy' : det2 p y = h := by
    obtain ⟨α, β, -, -, hαβ, rfl⟩ := hy
    simp only [det2, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hpa hpb ⊢
    linear_combination α * hpa + β * hpb + h * hαβ
  have j : ∀ z ∈ K, κ * det2 p z ≤ κ * h := by
    intro z hz
    have e1 := key z
    have e2 := key y
    rw [hy'] at e2
    have := mul_le_mul_of_nonneg_left (hfK z hz) hp2.le
    linarith
  have j1 := j z₁ hz₁
  have j2 := j z₂ hz₂
  have hκ : κ = 0 := by nlinarith
  obtain ⟨z, hz⟩ := hK.2.2.1
  have e1 := key z
  have e2 := key y
  rw [hκ, zero_mul] at e1 e2
  have := hfi z hz
  have hfz : f z = 0 := (mul_eq_zero.1 e1).resolve_left hp2.ne'
  have hfy : f y = 0 := (mul_eq_zero.1 e2).resolve_left hp2.ne'
  linarith

/-- Two inscribed "trapezoids" at different heights are impossible: if `a₁ = a₂ + p` with
`a₁, a₂ ∈ ∂K` at height `det(p, a₁) = h₁ > 0`, and `b₁ = b₂ + p` with `b₁, b₂ ∈ K` at a greater
height `h₂`, then the chord of `K` at height `h₁` is longer than `|p|` (it contains a chord of the
trapezoid `-p, p, b₁, b₂`), so `a₁` or `a₂` lies strictly between two points of `K` on that
chord, which is impossible since `K` has points above and below it. -/
lemma bdy_false_of_two_levels {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K)
    {p a₁ a₂ b₁ b₂ : Fin 2 → ℝ} (hp : p ≠ 0) (hpK : p ∈ K) (hnpK : -p ∈ K)
    (ha₁ : a₁ ∈ frontier K) (ha₂ : a₂ ∈ frontier K) (ha : a₁ = a₂ + p) (hb₁ : b₁ ∈ K)
    (hb₂ : b₂ ∈ K) (hb : b₁ = b₂ + p) (h₁ : 0 < det2 p a₁) (h₁₂ : det2 p a₁ < det2 p b₁) :
    False := by
  have hpp : det2 p p = 0 := by unfold det2; ring
  set H₁ := det2 p a₁ with hH₁
  set H₂ := det2 p b₁ with hH₂
  have hH₂pos : 0 < H₂ := by linarith
  set l := H₁ / H₂ with hl
  have hl0 : 0 < l := div_pos h₁ hH₂pos
  have hl1 : l < 1 := (div_lt_one hH₂pos).2 h₁₂
  have hlH : l * H₂ = H₁ := div_mul_cancel₀ _ hH₂pos.ne'
  set x := (1 - l) • (-p) + l • b₂ with hx_def
  set z := (1 - l) • p + l • b₁ with hz_def
  have hx : x ∈ K := hK.1 hnpK hb₂ (by linarith) hl0.le (by ring)
  have hz : z ∈ K := hK.1 hpK hb₁ (by linarith) hl0.le (by ring)
  -- heights
  have hpb₂ : det2 p b₂ = H₂ := by
    rw [hH₂, hb]; unfold det2 at hpp ⊢; simp only [Pi.add_apply]; linarith
  have hpa₂ : det2 p a₂ = H₁ := by
    rw [hH₁, ha]; unfold det2 at hpp ⊢; simp only [Pi.add_apply]; linarith
  have hpx : det2 p x = H₁ := by
    rw [← hlH, ← hpb₂]; simp only [x, det2, Pi.add_apply, Pi.smul_apply, Pi.neg_apply,
      smul_eq_mul]; ring
  have hpz : det2 p z = H₁ := by
    rw [← hlH, hH₂]; simp only [z, det2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  -- the coordinate `ξ = det(·, b₁)` along the chord
  have hpq : det2 p b₁ ≠ 0 := hH₂pos.ne'
  have hξa : det2 a₁ b₁ = det2 a₂ b₁ + H₂ := by
    rw [hH₂, ha]; unfold det2; simp only [Pi.add_apply]; ring
  have hξb : det2 b₂ b₁ = -H₂ := by
    rw [hH₂, hb]; unfold det2; simp only [Pi.add_apply]; ring
  have hξz : det2 z b₁ = det2 x b₁ + (2 - l) * H₂ := by
    have hbb : det2 b₁ b₁ = 0 := by unfold det2; ring
    have e1 : det2 z b₁ = (1 - l) * det2 p b₁ + l * det2 b₁ b₁ := by
      simp only [z, det2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    have e2 : det2 x b₁ = -(1 - l) * det2 p b₁ + l * det2 b₂ b₁ := by
      simp only [x, det2, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]; ring
    rw [e1, e2, hbb, hξb, ← hH₂]; ring
  have h0K := bdy_zero_mem hK
  have h00 : det2 p 0 = 0 := by unfold det2; simp
  by_cases hc : det2 x b₁ < det2 a₂ b₁
  · -- `a₂` lies strictly between `x` and `a₁`
    have hmem := bdy_mem_openSegment hpq (a := x) (x := a₂) (b := a₁) (by rw [hpa₂, hpx])
      (by rw [hpx]) hc (by rw [hξa]; linarith)
    exact bdy_false_of_mem_openSegment hK hp hx (hK.2.1.isClosed.frontier_subset ha₁)
      (fun h ↦ by rw [h] at hc; rw [hξa] at hc; linarith) hpx rfl hmem ha₂ h0K hb₁
      (by rw [h00]; exact h₁) h₁₂
  · -- `a₁` lies strictly between `a₂` and `z`
    push Not at hc
    have hmem := bdy_mem_openSegment hpq (a := a₂) (x := a₁) (b := z) (by rw [hpa₂])
      (by rw [hpz, hpa₂]) (by rw [hξa]; linarith) (by rw [hξa, hξz]; nlinarith)
    exact bdy_false_of_mem_openSegment hK hp (hK.2.1.isClosed.frontier_subset ha₂) hz
      (fun h ↦ by rw [← h] at hξz; nlinarith) hpa₂ hpz hmem ha₁ h0K hb₁
      (by rw [h00]; exact h₁) h₁₂

/-- **A multi-point on the boundary of a worst disk is the set of edge midpoints of a critical
hexagon.** If `v` is a critical hexagon of `K` whose edge midpoints `m_j` lie on the boundary, and
`s` is a multi-point on the boundary with `s₀ = m₀`, then `s = m`. Both `s₁, s₂` and `m₁, m₂` are
chords of the boundary parallel to `p = s₀` with `s₁ - s₂ = m₁ - m₂ = p`: at different heights
this contradicts convexity (`bdy_false_of_two_levels`), and at the same height they overlap, which
puts a point strictly between `m₁` and `m₂` on the boundary, contrary to
`bdy_not_mem_frontier_of_openSegment`. -/
lemma bdy_eq_hexMidpoint {K : Set (Fin 2 → ℝ)} (hK : IsWorstDisk K)
    {v : ZMod 6 → Fin 2 → ℝ} (hv : IsLeastAreaHexagon K v)
    (hvK : ∀ j, hexMidpoint v j ∈ frontier K) {s : ZMod 6 → Fin 2 → ℝ} (hs : IsMultiPoint s)
    (hsK : ∀ j, s j ∈ frontier K) (h0 : s 0 = hexMidpoint v 0) :
    ∀ j, s j = hexMidpoint v j := by
  have hK' := hK.1
  have hmem : ∀ x ∈ frontier K, x ∈ K := fun x hx ↦ hK'.2.1.isClosed.frontier_subset hx
  set m := hexMidpoint v with hm_def
  set p := s 0 with hp_def
  have hs1 : s 1 = s 2 + p := by
    have := bdy_mp_succ hs 0; rw [zero_add, zero_add] at this; rw [this, add_comm]
  have hm1 : m 1 = m 2 + p := by
    have := bdy_hexMidpoint_succ hv.1 0; rw [zero_add, zero_add] at this
    change hexMidpoint v 1 = hexMidpoint v 2 + p
    rw [this, add_comm, h0]
  have hd : det2 p (s 1) = √3 / 2 := (hs 0).2.2
  have hcpos : 0 < det2 p (m 1) := by
    have := bdy_det2_hexMidpoint_pos hv.1 0; rw [zero_add] at this; rw [h0]; exact this
  have hp : p ≠ 0 := fun h ↦ by
    rw [h] at hd; simp only [det2, Pi.zero_apply, zero_mul, sub_zero] at hd
    have : (0 : ℝ) < √3 / 2 := by positivity
    linarith
  have hpK : p ∈ K := hmem _ (hsK 0)
  have hnpK : -p ∈ K := hK'.2.2.2 p hpK
  have hpp : det2 p p = 0 := by unfold det2; ring
  have key : s 1 = m 1 := by
    rcases lt_trichotomy (det2 p (s 1)) (det2 p (m 1)) with hlt | heq | hgt
    · exact (bdy_false_of_two_levels hK' hp hpK hnpK (hsK 1) (hsK 2) hs1 (hmem _ (hvK 1))
        (hmem _ (hvK 2)) hm1 (by rw [hd]; positivity) hlt).elim
    · -- the same height: `ξ = det(·, m₁)` orders the chord
      set c := det2 p (m 1) with hc_def
      have hpq : det2 p (m 1) ≠ 0 := hcpos.ne'
      have hls2 : det2 p (s 2) = c := by
        rw [← heq, hs1]; unfold det2 at hpp ⊢; simp only [Pi.add_apply]; linarith
      have hlm2 : det2 p (m 2) = c := by
        rw [hc_def, hm1]; unfold det2 at hpp ⊢; simp only [Pi.add_apply]; linarith
      have hξm1 : det2 (m 1) (m 1) = 0 := by unfold det2; ring
      have hξm2 : det2 (m 2) (m 1) = -c := by
        rw [hc_def, hm1]; unfold det2; simp only [Pi.add_apply]; ring
      have hξs1 : det2 (s 1) (m 1) = det2 (s 2) (m 1) + c := by
        rw [hc_def, hs1]; unfold det2; simp only [Pi.add_apply]; ring
      set z := (1 / 2 : ℝ) • m 1 + (1 / 2 : ℝ) • m 2 with hz_def
      have hz : z ∉ frontier K := by
        refine bdy_not_mem_frontier_of_openSegment hK hv 1 ?_
        exact ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
      have hlz : det2 p z = c := by
        have e : det2 p z = (1 / 2) * det2 p (m 1) + (1 / 2) * det2 p (m 2) := by
          simp only [z, det2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
        rw [e, hlm2, ← hc_def]; ring
      have hξz : det2 z (m 1) = -c / 2 := by
        have e : det2 z (m 1) = (1 / 2) * det2 (m 1) (m 1) + (1 / 2) * det2 (m 2) (m 1) := by
          simp only [z, det2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
        rw [e, hξm1, hξm2]; ring
      rcases lt_trichotomy (det2 (s 2) (m 1)) (det2 (m 2) (m 1)) with h | h | h
      · -- `m₂` lies strictly between `s₂` and `m₁`
        exfalso
        have hm2 := bdy_mem_openSegment hpq (a := s 2) (x := m 2) (b := m 1)
          (by rw [hlm2, hls2]) (by rw [hls2]) h (by rw [hξm2, hξm1]; linarith)
        have hsub := bdy_openSegment_subset_frontier hK' (hmem _ (hsK 2)) (hmem _ (hvK 1)) hm2
          (hvK 2)
        exact hz (hsub (bdy_mem_openSegment hpq (by rw [hlz, hls2]) (by rw [hls2])
          (by rw [hξz]; linarith) (by rw [hξz, hξm1]; linarith)))
      · have h2 : s 2 = m 2 := bdy_eq_of_det2_eq hpq (by rw [hls2, hlm2]) h
        rw [hs1, hm1, h2]
      · -- `m₁` lies strictly between `m₂` and `s₁`
        exfalso
        have hm1' := bdy_mem_openSegment hpq (a := m 2) (x := m 1) (b := s 1)
          (by rw [hlm2]) (by rw [heq, hlm2]) (by rw [hξm2, hξm1]; linarith)
          (by rw [hξm1, hξs1]; linarith)
        have hsub := bdy_openSegment_subset_frontier hK' (hmem _ (hvK 2)) (hmem _ (hsK 1)) hm1'
          (hvK 1)
        exact hz (hsub (bdy_mem_openSegment hpq (by rw [hlz, hlm2]) (by rw [heq, hlm2])
          (by rw [hξz, hξm2]; linarith) (by rw [hξz, hξs1]; linarith)))
    · exact (bdy_false_of_two_levels hK' hp hpK hnpK (hvK 1) (hvK 2) hm1 (hmem _ (hsK 1))
        (hmem _ (hsK 2)) hs1 hcpos hgt).elim
  exact bdy_seq_eq (bdy_mp_succ hs) (bdy_hexMidpoint_succ hv.1) h0 key

/-- Polar form of a nonzero vector of the plane. -/
lemma bdy_polar {x : Fin 2 → ℝ} (hx : x ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ θ : ℝ, x = ρ • ![Real.cos θ, Real.sin θ] := by
  set z : ℂ := ⟨x 0, x 1⟩
  have hz : z ≠ 0 := by
    intro h
    apply hx
    have h0 : x 0 = 0 := congrArg Complex.re h
    have h1 : x 1 = 0 := congrArg Complex.im h
    ext i; fin_cases i <;> simp [h0, h1]
  refine ⟨‖z‖, norm_pos_iff.2 hz, Complex.arg z, ?_⟩
  have h1 := Complex.norm_mul_cos_arg z
  have h2 := Complex.norm_mul_sin_arg z
  ext i; fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, Matrix.cons_val_zero, smul_eq_mul]
    rw [h1]
  · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, Matrix.cons_val_one, Matrix.cons_val_zero,
      smul_eq_mul]
    rw [h2]

/-- Two boundary points in the same direction from the origin coincide. -/
lemma bdy_eq_of_polar {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {x y u : Fin 2 → ℝ}
    (hx : x ∈ frontier K) (hy : y ∈ frontier K) {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    (hxu : x = ρ • u) (hyu : y = r • u) : y = x := by
  refine bdy_eq_of_smul hK hx hy (div_pos hr hρ) ?_
  rw [hyu, hxu, smul_smul, div_mul_cancel₀ _ hρ.ne']

/-- A boundary point of a centrally symmetric convex disk is not the origin. -/
lemma bdy_ne_zero_of_mem_frontier {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {x : Fin 2 → ℝ}
    (hx : x ∈ frontier K) : x ≠ 0 := by
  rintro rfl
  exact hx.2 (bdy_zero_mem_interior hK)

/-- The second part of Lemma 2.2.7 in the form used here: the polar angle `φ_j(θ)` of the midpoint
`s_j` of the critical hexagon at the boundary point of angle `θ`, with `s_j = r (cos φ_j(θ),
sin φ_j(θ))`, `r > 0` real. -/
lemma bdy_lemma2_2_7_polar {K : Set (Fin 2 → ℝ)} (hK : IsWorstDisk K) :
    ∃ φ : ZMod 6 → ℝ → ℝ, φ 0 = id ∧
      (∀ j, Continuous (φ j) ∧ ∀ θ, φ j (θ + 2 * π) = φ j θ + 2 * π) ∧
      ∀ θ, ∃ v, IsLeastAreaHexagon K v ∧ ∀ j, hexMidpoint v j ∈ frontier K ∧
        ∃ r : ℝ, 0 < r ∧ hexMidpoint v j = r • ![Real.cos (φ j θ), Real.sin (φ j θ)] := by
  obtain ⟨φ, hφ0, hφ, hφv⟩ := (lemma2_2_7 hK).2
  refine ⟨φ, hφ0, fun j ↦ ⟨(hφ j).1, (hφ j).2.2⟩, fun θ ↦ ?_⟩
  obtain ⟨v, hv, hvm⟩ := hφv θ
  refine ⟨v, hv, fun j ↦ ⟨(hvm j).1, ?_⟩⟩
  obtain ⟨r, hr, hvj⟩ := (hvm j).2
  exact ⟨r, by exact_mod_cast hr, by simpa using hvj⟩

/-- **Every boundary point of a worst disk is the midpoint of edge `0` of a critical hexagon whose
edge midpoints all lie on the boundary** (Lemma 2.2.7). -/
lemma bdy_exists_hexagon {K : Set (Fin 2 → ℝ)} (hK : IsWorstDisk K) {x : Fin 2 → ℝ}
    (hx : x ∈ frontier K) :
    ∃ v, IsLeastAreaHexagon K v ∧ (∀ j, hexMidpoint v j ∈ frontier K) ∧ hexMidpoint v 0 = x := by
  obtain ⟨φ, hφ0, -, hφv⟩ := bdy_lemma2_2_7_polar hK
  obtain ⟨ρ, hρ, θ, hxθ⟩ := bdy_polar (bdy_ne_zero_of_mem_frontier hK.1 hx)
  obtain ⟨v, hv, hvm⟩ := hφv θ
  obtain ⟨hv0K, r, hr, hv0⟩ := hvm 0
  rw [hφ0, id] at hv0
  exact ⟨v, hv, fun j ↦ (hvm j).1, bdy_eq_of_polar hK.1 hx hv0K hρ hr hxθ hv0⟩

/-- **The curves `σ_j` cover the boundary.** For a multi-curve `σ` on the boundary of a worst disk
whose curve `σ₀` covers the boundary, each `σ_j` covers it: by Lemma 2.2.7, the midpoint `s_j`
of the critical hexagon at the boundary point of angle `θ` lies at the angle `φ_j(θ)`, and
`φ_j` takes every value modulo `2π`. -/
lemma bdy_range_eq {K : Set (Fin 2 → ℝ)} (hK : IsWorstDisk K) {σ : ZMod 6 → ℝ → Fin 2 → ℝ}
    (hσm : ∀ t, IsMultiPoint fun j ↦ σ j t) (hσK : ∀ j t, σ j t ∈ frontier K)
    (hσ₀ : range (σ 0) = frontier K) (j : ZMod 6) : range (σ j) = frontier K := by
  refine Subset.antisymm (range_subset_iff.2 (hσK j)) fun q hq ↦ ?_
  obtain ⟨φ, -, hφ, hφv⟩ := bdy_lemma2_2_7_polar hK
  obtain ⟨ρ, hρ, θq, hqθ⟩ := bdy_polar (bdy_ne_zero_of_mem_frontier hK.1 hq)
  obtain ⟨hc, hper⟩ := hφ j
  set y := toIcoMod two_pi_pos (φ j 0) θq with hy_def
  have hy := toIcoMod_mem_Ico two_pi_pos (φ j 0) θq
  have hper0 : φ j (2 * π) = φ j 0 + 2 * π := by have := hper 0; rwa [zero_add] at this
  obtain ⟨θ, -, hθ⟩ : y ∈ φ j '' Icc 0 (2 * π) :=
    intermediate_value_Icc two_pi_pos.le hc.continuousOn ⟨hy.1, by rw [hper0]; exact hy.2.le⟩
  obtain ⟨v, hv, hvm⟩ := hφv θ
  obtain ⟨hvjK, r, hr, hvj⟩ := hvm j
  have hcos : Real.cos y = Real.cos θq := by
    rw [hy_def, toIcoMod, zsmul_eq_mul]; exact Real.cos_sub_int_mul_two_pi θq _
  have hsin : Real.sin y = Real.sin θq := by
    rw [hy_def, toIcoMod, zsmul_eq_mul]; exact Real.sin_sub_int_mul_two_pi θq _
  rw [hθ, hcos, hsin] at hvj
  have hvq : hexMidpoint v j = q := bdy_eq_of_polar hK.1 hq hvjK hρ hr hqθ hvj
  obtain ⟨t, ht⟩ : hexMidpoint v 0 ∈ range (σ 0) := by rw [hσ₀]; exact (hvm 0).1
  have := bdy_eq_hexMidpoint hK hv (fun i ↦ (hvm i).1) (hσm t) (fun i ↦ hσK i t) ht
  exact ⟨t, (this j).trans hvq⟩

/-- `-x` lies on the boundary of a centrally symmetric disk when `x` does. -/
lemma bdy_neg_mem_frontier {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {x : Fin 2 → ℝ}
    (hx : x ∈ frontier K) : -x ∈ frontier K := by
  have hKn : (Homeomorph.neg (Fin 2 → ℝ)) ⁻¹' K = K := by
    ext y
    exact ⟨fun h ↦ by simpa using hK.2.2.2 _ h, fun h ↦ hK.2.2.2 y h⟩
  have h := (Homeomorph.neg (Fin 2 → ℝ)).preimage_frontier K
  rw [hKn] at h
  rw [← h] at hx
  simpa using hx

/-- The reflected curve `t ↦ -γ(t)` of a positively oriented boundary parameterization of a
centrally symmetric disk is again one. -/
lemma bdy_isPositiveBoundaryParam_neg {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K)
    {γ : ℝ → Fin 2 → ℝ} (hγ : IsPositiveBoundaryParam K γ) :
    IsPositiveBoundaryParam K fun t ↦ -γ t := by
  obtain ⟨hC, hreg, hrange, hor⟩ := hγ
  have hd : ∀ t, deriv (fun t ↦ -γ t) t = -deriv γ t := fun t ↦
    ((hC.differentiable (by norm_num) t).hasDerivAt.neg).deriv
  refine ⟨hC.neg, fun t ↦ by rw [hd]; exact neg_ne_zero.2 (hreg t), ?_, fun t ↦ ?_⟩
  · apply Subset.antisymm
    · rintro _ ⟨t, rfl⟩
      exact bdy_neg_mem_frontier hK (hrange ▸ mem_range_self t)
    · intro x hx
      obtain ⟨t, ht⟩ : -x ∈ range γ := by rw [hrange]; exact bdy_neg_mem_frontier hK hx
      exact ⟨t, by simp [ht]⟩
  · rw [hd]
    have := hor t
    simp only [det2, Pi.neg_apply] at this ⊢
    linarith

/-! ### Regularity of multi-curves -/

/-- **Lemma 2.4.2** (Hales 2011; `lem:sigma2:c1`). Let `K = K_min ∈ 𝔎_ccs` be a centrally symmetric
convex disk that has the worst greatest packing density. Consider a `C⁰` multi-curve
parameterization `σ` of its boundary. If `t ↦ σ₀(t)` is a positively oriented `C¹` regular curve
parameterizing the boundary of `K`, then so is `σ_j(t)` for `j = 1, …, 5`.

Proof, as in the book. Since `σ₀` is a regular `C¹` parameterization, `K` has no corners: the
support line at each boundary point is unique (`bdy_support_unique`), and the unit tangent `u(t)`
of the boundary at `σ₂(t)` is continuous in `t` (`bdy_continuous_tangent`). We have
`det(σ₀(t), u(t)) ≠ 0` and `det(σ₀'(t), σ₂(t)) ≠ 0`: otherwise the tangent line at `σ₂(t)`, resp.
`σ₀(t)`, contains an edge of the hexagon `h_K(t)`, contrary to Lemma 2.2.6
(`bdy_not_mem_frontier_of_openSegment`). The speed `s₂ = -det(σ₀', σ₂)/det(σ₀, u)` of equation
`eqn:sB` is continuous and positive, and `σ₂' = s₂ u` (`bdy_contDiff_of_det2_const`). The same
argument applies to `σ₁` (with `det(σ₀, σ₁) = √3/2`), and `σ_{j+3} = -σ_j`.

Departure from the paper (a gap in the book's argument): the book defines `σ̃₂ = σ₂(t₀) + ∫ u s₂`
and concludes `σ₂ = σ̃₂` from the facts that `σ̃₂` has the same tangent directions and satisfies the
same area relation, which does not show that `σ̃₂` stays on the boundary. Instead we prove directly
that the difference quotients of `σ₂` converge to `s₂(t) u(t)`: the chord from `σ₂(t)` to
`σ₂(t + h)` lies between the tangent lines at its ends, so its direction tends to `u(t)`, and the
area relation `det(σ₀, σ₂) = √3/2` fixes its length (`bdy_hasDerivAt_of_det2_const`).

Departure from the paper (a step the book leaves implicit): the book takes `σ_j(t)` to be the edge
midpoints of the critical hexagon at `σ₀(t)` (Lemma 2.2.7), while the statement allows any
continuous multi-curve on the boundary. We first show that a multi-point on the boundary through
`σ₀(t)` is that set of midpoints (`bdy_eq_hexMidpoint`, comparing the chords of `K` parallel to
`σ₀(t)`); this also gives that each `σ_j` covers the boundary (`bdy_range_eq`). Lemma 2.2.6 is
stated in circle representation; it is applied after the linear normalization `m_j ↦ s_j*`, which
preserves worst disks and critical hexagons (`bdy_isWorstLatticeDisk_image`,
`bdy_isLeastAreaHexagon_image`). -/
theorem lemma2_4_2 {K : Set (Fin 2 → ℝ)} (hK : IsWorstDisk K) {σ : ZMod 6 → ℝ → Fin 2 → ℝ}
    (hσc : ∀ j, Continuous (σ j)) (hσm : ∀ t, IsMultiPoint fun j ↦ σ j t)
    (hσK : ∀ j t, σ j t ∈ frontier K) (hσ₀ : IsPositiveBoundaryParam K (σ 0)) :
    ∀ j, IsPositiveBoundaryParam K (σ j) := by
  have hK' : IsCCSDisk K := hK.1
  have hmem : ∀ x ∈ frontier K, x ∈ K := fun x hx ↦ hK'.2.1.isClosed.frontier_subset hx
  -- the multi-point `σ(t)` is the set of edge midpoints of the critical hexagon at `σ₀(t)`
  have hcrit : ∀ t, ∃ v, IsLeastAreaHexagon K v ∧ ∀ j, σ j t = hexMidpoint v j := fun t ↦ by
    obtain ⟨v, hv, hvK, hv0⟩ := bdy_exists_hexagon hK (hσK 0 t)
    exact ⟨v, hv, bdy_eq_hexMidpoint hK hv hvK (hσm t) (fun j ↦ hσK j t) hv0.symm⟩
  -- no edge of the hexagon `h_K(t)` lies on the boundary (Lemma 2.2.6)
  have hedge : ∀ t j, (1 / 2 : ℝ) • σ j t + (1 / 2 : ℝ) • σ (j + 1) t ∉ frontier K := by
    intro t j
    obtain ⟨v, hv, hσv⟩ := hcrit t
    refine bdy_not_mem_frontier_of_openSegment hK hv j ?_
    rw [← hσv, ← hσv]
    exact ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  -- if the line through `x ∈ ∂K` in a support direction `w` contains `y ∈ K`, the midpoint of
  -- `x` and `y` lies on the boundary
  have hline : ∀ {x y w : Fin 2 → ℝ}, x ∈ K → y ∈ K → w ≠ 0 → (∀ z ∈ K, 0 ≤ det2 w (z - x)) →
      det2 w (y - x) = 0 → (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y ∈ frontier K := by
    intro x y w hx hy hw hsupp hxy
    have hzK : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y ∈ K :=
      hK'.1 hx hy (by norm_num) (by norm_num) (by norm_num)
    refine ⟨subset_closure hzK, bdy_not_mem_interior hw (c := det2 w x) (fun z hz ↦ ?_) ?_⟩
    · have := hsupp z hz
      unfold det2 at this ⊢; simp only [Pi.sub_apply] at this; linarith
    · simp only [det2, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at hxy ⊢
      linarith
  -- multi-point relations
  have e1 : ∀ t, σ 1 t = σ 0 t + σ 2 t := fun t ↦ by
    have := bdy_mp_succ (hσm t) 0; rwa [zero_add, zero_add] at this
  have e5 : ∀ t, σ 5 t = -σ 2 t := fun t ↦ by
    have := (hσm t 2).2.1; rwa [show (2 : ZMod 6) + 3 = 5 from rfl] at this
  have e21 : ∀ t, σ 2 t - σ 1 t = -σ 0 t := fun t ↦ by rw [e1]; abel
  have hsupp0 : ∀ t z, z ∈ K → 0 ≤ det2 (deriv (σ 0) t) (z - σ 0 t) :=
    fun t z hz ↦ bdy_det2_deriv_sub_nonneg hK' hσ₀ t hz
  have hU := fun j t ↦ bdy_tangent_spec hK' hσ₀ (hσK j t)
  have hUne : ∀ j t, bdy_tangent (σ 0) (σ j t) ≠ 0 := fun j t h ↦ by
    have := (hU j t).1; rw [h, norm_zero] at this; exact zero_ne_one this
  -- `det(σ₀(t), u(t)) ≠ 0` for the unit tangent `u(t)` at `σ₂(t)`: otherwise the tangent line at
  -- `σ₂(t)` contains the edge through `σ₂(t)` and `σ₁(t)`, contrary to Lemma 2.2.6
  have hb2 : ∀ t, det2 (σ 0 t) (bdy_tangent (σ 0) (σ 2 t)) ≠ 0 := by
    intro t h
    apply hedge t 1
    have := hline (hmem _ (hσK 2 t)) (hmem _ (hσK 1 t)) (hUne 2 t) (hU 2 t).2.1 (by
      rw [e1]; simp only [det2, Pi.add_apply, Pi.sub_apply] at h ⊢; linarith)
    rw [show (1 : ZMod 6) + 1 = 2 from rfl, add_comm]
    exact this
  -- `det(σ₀'(t), σ₂(t)) ≠ 0`: otherwise the tangent line at `σ₀(t)` contains the edge through
  -- `σ₀(t)` and `σ₁(t)`
  have hc2 : ∀ t, det2 (deriv (σ 0) t) (σ 2 t) ≠ 0 := by
    intro t h
    apply hedge t 0
    have := hline (hmem _ (hσK 0 t)) (hmem _ (hσK 1 t)) (hσ₀.2.1 t) (hsupp0 t) (by
      rw [e1, add_sub_cancel_left]; exact h)
    rwa [zero_add]
  -- the same claims for `σ₁`
  have hb1 : ∀ t, det2 (σ 0 t) (bdy_tangent (σ 0) (σ 1 t)) ≠ 0 := by
    intro t h
    apply hedge t 1
    have := hline (hmem _ (hσK 1 t)) (hmem _ (hσK 2 t)) (hUne 1 t) (hU 1 t).2.1 (by
      rw [e21 t]; simp only [det2, Pi.neg_apply] at h ⊢; linarith)
    rwa [show (1 : ZMod 6) + 1 = 2 from rfl]
  have hc1 : ∀ t, det2 (deriv (σ 0) t) (σ 1 t) ≠ 0 := by
    intro t h
    apply hedge t 5
    have := hline (hmem _ (hσK 0 t)) (hmem _ (hσK 5 t)) (hσ₀.2.1 t) (hsupp0 t) (by
      rw [e5]; rw [e1] at h; simp only [det2, Pi.add_apply, Pi.sub_apply, Pi.neg_apply] at h ⊢
      linarith)
    rw [show (5 : ZMod 6) + 1 = 0 from rfl, add_comm]
    exact this
  -- the area relations `det(σ₀, σ₁) = det(σ₀, σ₂) = √3/2`
  have hdet1 : ∀ t, det2 (σ 0 t) (σ 1 t) = √3 / 2 := fun t ↦ (hσm t 0).2.2
  have hdet2 : ∀ t, det2 (σ 0 t) (σ 2 t) = √3 / 2 := fun t ↦ by
    rw [← hdet1 t, e1]; simp only [det2, Pi.add_apply]; ring
  -- `σ₁, σ₂` are `C¹`, with `σ_j' = s_j u_j` (equation `eqn:sB`)
  obtain ⟨hC2, hd2⟩ := bdy_contDiff_of_det2_const hK' hσ₀ (hσc 2) (hσK 2) hdet2 hb2
  obtain ⟨hC1, hd1⟩ := bdy_contDiff_of_det2_const hK' hσ₀ (hσc 1) (hσK 1) hdet1 hb1
  have hrange := bdy_range_eq hK hσm hσK hσ₀.2.2.1
  -- the speeds `s_j` are positive
  have hP2 : IsPositiveBoundaryParam K (σ 2) := by
    refine ⟨hC2, fun t ↦ ?_, hrange 2, fun t ↦ ?_⟩
    · rw [hd2 t]
      exact smul_ne_zero (div_ne_zero (neg_ne_zero.2 (hc2 t)) (hb2 t)) (hUne 2 t)
    · have hnum : 0 < det2 (deriv (σ 0) t) (σ 2 t) := by
        have := hsupp0 t _ (hmem _ (hσK 1 t))
        rw [e1, add_sub_cancel_left] at this
        exact lt_of_le_of_ne this (Ne.symm (hc2 t))
      have hden : det2 (σ 0 t) (bdy_tangent (σ 0) (σ 2 t)) < 0 := by
        have := (hU 2 t).2.1 _ (hmem _ (hσK 1 t))
        rw [e1] at this
        have h' : det2 (σ 0 t) (bdy_tangent (σ 0) (σ 2 t)) ≤ 0 := by
          simp only [det2, Pi.add_apply, Pi.sub_apply] at this ⊢; linarith
        exact lt_of_le_of_ne h' (hb2 t)
      rw [hd2 t]
      have hs : 0 < -det2 (deriv (σ 0) t) (σ 2 t) / det2 (σ 0 t) (bdy_tangent (σ 0) (σ 2 t)) :=
        div_pos_of_neg_of_neg (by linarith) hden
      have e : det2 (σ 2 t) ((-det2 (deriv (σ 0) t) (σ 2 t) /
          det2 (σ 0 t) (bdy_tangent (σ 0) (σ 2 t))) • bdy_tangent (σ 0) (σ 2 t)) =
          (-det2 (deriv (σ 0) t) (σ 2 t) / det2 (σ 0 t) (bdy_tangent (σ 0) (σ 2 t))) *
            det2 (σ 2 t) (bdy_tangent (σ 0) (σ 2 t)) := by
        simp only [det2, Pi.smul_apply, smul_eq_mul]; ring
      rw [e]
      exact mul_pos hs (hU 2 t).2.2
  have hP1 : IsPositiveBoundaryParam K (σ 1) := by
    refine ⟨hC1, fun t ↦ ?_, hrange 1, fun t ↦ ?_⟩
    · rw [hd1 t]
      exact smul_ne_zero (div_ne_zero (neg_ne_zero.2 (hc1 t)) (hb1 t)) (hUne 1 t)
    · have hnum : det2 (deriv (σ 0) t) (σ 1 t) < 0 := by
        have := hsupp0 t _ (hmem _ (hσK 5 t))
        rw [e5] at this
        have h' : det2 (deriv (σ 0) t) (σ 1 t) ≤ 0 := by
          rw [e1]; simp only [det2, Pi.add_apply, Pi.sub_apply, Pi.neg_apply] at this ⊢
          linarith
        exact lt_of_le_of_ne h' (hc1 t)
      have hden : 0 < det2 (σ 0 t) (bdy_tangent (σ 0) (σ 1 t)) := by
        have := (hU 1 t).2.1 _ (hmem _ (hσK 2 t))
        rw [e21 t] at this
        have h' : 0 ≤ det2 (σ 0 t) (bdy_tangent (σ 0) (σ 1 t)) := by
          simp only [det2, Pi.neg_apply] at this ⊢; linarith
        exact lt_of_le_of_ne h' (Ne.symm (hb1 t))
      rw [hd1 t]
      have hs : 0 < -det2 (deriv (σ 0) t) (σ 1 t) / det2 (σ 0 t) (bdy_tangent (σ 0) (σ 1 t)) :=
        div_pos (by linarith) hden
      have e : det2 (σ 1 t) ((-det2 (deriv (σ 0) t) (σ 1 t) /
          det2 (σ 0 t) (bdy_tangent (σ 0) (σ 1 t))) • bdy_tangent (σ 0) (σ 1 t)) =
          (-det2 (deriv (σ 0) t) (σ 1 t) / det2 (σ 0 t) (bdy_tangent (σ 0) (σ 1 t))) *
            det2 (σ 1 t) (bdy_tangent (σ 0) (σ 1 t)) := by
        simp only [det2, Pi.smul_apply, smul_eq_mul]; ring
      rw [e]
      exact mul_pos hs (hU 1 t).2.2
  -- `σ_{j+3} = -σ_j`
  have hneg : ∀ j, IsPositiveBoundaryParam K (σ j) → IsPositiveBoundaryParam K (σ (j + 3)) := by
    intro j hj
    have : σ (j + 3) = fun t ↦ -σ j t := funext fun t ↦ (hσm t j).2.1
    rw [this]
    exact bdy_isPositiveBoundaryParam_neg hK' hj
  intro j
  fin_cases j
  · exact hσ₀
  · exact hP1
  · exact hP2
  · exact hneg 0 hσ₀
  · exact hneg 1 hP1
  · exact hneg 2 hP2

/-- **Lemma 2.4.3** (Hales 2011, Lemmas 17 and 18; `lem:tangents-lipschitz`). Let `σ` be a `C¹`
multi-curve parameterization of the boundary of `K = K_min ∈ 𝔎_ccs`, giving worst greatest packing
density. Assume that the curve `σ₀` is parameterized according to arclength. Then the tangents
`σ_j'` are Lipschitz continuous for all `j`. -/
theorem lemma2_4_3 {K : Set (Fin 2 → ℝ)} (hK : IsWorstDisk K) {σ : ZMod 6 → ℝ → Fin 2 → ℝ}
    (hσ : ∀ j, ContDiff ℝ 1 (σ j)) (hσm : ∀ t, IsMultiPoint fun j ↦ σ j t)
    (hσK : ∀ j t, σ j t ∈ frontier K) (hσ₀ : range (σ 0) = frontier K)
    (harc : ∀ t, deriv (σ 0) t 0 ^ 2 + deriv (σ 0) t 1 ^ 2 = 1) :
    ∀ j, ∃ C, LipschitzWith C (deriv (σ j)) := by
  sorry

/-- **Corollary 2.4.4** (`lem:multi-curve-c2`). Under the hypotheses of Lemma 2.4.3, the functions
`σ_j'(t)` are differentiable almost everywhere. -/
theorem corollary2_4_4 {K : Set (Fin 2 → ℝ)} (hK : IsWorstDisk K) {σ : ZMod 6 → ℝ → Fin 2 → ℝ}
    (hσ : ∀ j, ContDiff ℝ 1 (σ j)) (hσm : ∀ t, IsMultiPoint fun j ↦ σ j t)
    (hσK : ∀ j t, σ j t ∈ frontier K) (hσ₀ : range (σ 0) = frontier K)
    (harc : ∀ t, deriv (σ 0) t 0 ^ 2 + deriv (σ 0) t 1 ^ 2 = 1) :
    ∀ j, ∀ᵐ t, DifferentiableAt ℝ (deriv (σ j)) t := by
  intro j
  obtain ⟨C, hC⟩ := lemma2_4_3 hK hσ hσm hσK hσ₀ harc j
  exact LipschitzWith.ae_differentiableAt (μ := volume) hC

/-! ### Convexity of multi-curves -/

/-- Differentiating `σ_{j+3} = -σ_j`. -/
lemma bdy_deriv_add_three {σ : ZMod 6 → ℝ → Fin 2 → ℝ}
    (hd : ∀ j, Differentiable ℝ (σ j)) (hm : ∀ t, IsMultiPoint fun j ↦ σ j t) (j : ZMod 6)
    (t : ℝ) : deriv (σ (j + 3)) t = -deriv (σ j) t := by
  have : σ (j + 3) = fun τ ↦ -σ j τ := funext fun τ ↦ (hm τ j).2.1
  rw [this]
  exact (hd j t).hasDerivAt.neg.deriv

/-- Differentiating `σ_j + σ_{j+2} + σ_{j+4} = 0`. -/
lemma bdy_deriv_sum {σ : ZMod 6 → ℝ → Fin 2 → ℝ}
    (hd : ∀ j, Differentiable ℝ (σ j)) (hm : ∀ t, IsMultiPoint fun j ↦ σ j t) (j : ZMod 6)
    (t : ℝ) : deriv (σ j) t + deriv (σ (j + 2)) t + deriv (σ (j + 4)) t = 0 := by
  have h := ((hd j t).hasDerivAt.add (hd (j + 2) t).hasDerivAt).add (hd (j + 4) t).hasDerivAt
  have hz : σ j + σ (j + 2) + σ (j + 4) = fun _ ↦ 0 :=
    funext fun τ ↦ (hm τ j).1
  rw [hz] at h
  exact h.unique (hasDerivAt_const t 0)

/-- The closed star condition (first part of the proof of Lemma 2.4.5): the tangent line at `s_j`
supports `K`, and `K` contains the neighbors `s_{j±1}`, so `σ_j'(t)` lies in the closed cone
spanned by `s_{j+1} - s_j = s_{j+2}` and `s_{j+1}`: `det(s_{j+1}, σ_j') ≥ 0` and
`det(σ_j', s_{j+2}) ≥ 0`. -/
private lemma bdy_cone_closed {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K)
    {σ : ZMod 6 → ℝ → Fin 2 → ℝ} (hσ : IsBoundaryMultiCurve K σ) (j : ZMod 6) (t : ℝ) :
    0 ≤ det2 (σ (j + 1) t) (deriv (σ j) t) ∧ 0 ≤ det2 (deriv (σ j) t) (σ (j + 2) t) := by
  obtain ⟨hpar, hm⟩ := hσ
  have e1 : σ (j + 1) t = σ j t + σ (j + 2) t := bdy_mp_succ (hm t) j
  have e5 : σ (j + 5) t = -σ (j + 2) t := by
    have := (hm t (j + 2)).2.1
    rwa [show j + 2 + 3 = j + 5 by ring] at this
  have h1 := bdy_det2_deriv_sub_nonneg hK (hpar j) t (bdy_mem hK (hpar (j + 5)) t)
  have h2 := bdy_det2_deriv_sub_nonneg hK (hpar j) t (bdy_mem hK (hpar (j + 1)) t)
  rw [e5] at h1
  rw [e1] at h2 ⊢
  constructor
  · unfold det2 at h1 ⊢
    simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply] at h1 ⊢
    linarith
  · unfold det2 at h2 ⊢
    simp only [Pi.add_apply, Pi.sub_apply] at h2 ⊢
    linarith

/-- The tangent `σ_k'(t)` does not point along the edge `s_k s_{k+1}` (second part of the proof
of Lemma 2.4.5). Otherwise the tangent line at `s_k` contains `s_{k+1}`, so it is also tangent to
`σ_{k+1}` there; then `σ_k'`, `σ_{k+1}'` and hence `σ_{k+2}' = σ_{k+1}' - σ_k'` are parallel to
`s_{k+2}`, and the closed cone at `k + 2` contains no nonzero vector in that direction. -/
private lemma bdy_det2_deriv_two_ne {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K)
    {σ : ZMod 6 → ℝ → Fin 2 → ℝ} (hσ : IsBoundaryMultiCurve K σ) (k : ZMod 6) (t : ℝ) :
    det2 (deriv (σ k) t) (σ (k + 2) t) ≠ 0 := by
  intro h
  have hcone := bdy_cone_closed hK hσ (k + 2) t
  obtain ⟨hpar, hm⟩ := hσ
  have hd : ∀ i, Differentiable ℝ (σ i) := fun i ↦ (hpar i).1.differentiable (by norm_num)
  have e1 : σ (k + 1) t = σ k t + σ (k + 2) t := bdy_mp_succ (hm t) k
  -- the tangent line at `s_k` passes through `s_{k+1}`, so it is tangent to `σ_{k+1}`
  have hv : det2 (deriv (σ k) t) (deriv (σ (k + 1)) t) = 0 := by
    refine bdy_det2_deriv_eq_zero hK (hpar k) (hd (k + 1))
      (fun τ ↦ bdy_mem hK (hpar (k + 1)) τ) ?_
    rw [e1, add_sub_cancel_left]
    exact h
  -- `σ_{k+2}' = σ_{k+1}' - σ_k'`
  have hsum := bdy_deriv_sum hd hm k t
  have h4 : deriv (σ (k + 4)) t = -deriv (σ (k + 1)) t := by
    have := bdy_deriv_add_three hd hm (k + 1) t
    rwa [show k + 1 + 3 = k + 4 by ring] at this
  rw [h4] at hsum
  have hw : deriv (σ (k + 2)) t = deriv (σ (k + 1)) t - deriv (σ k) t := by
    linear_combination hsum
  have huw : det2 (deriv (σ k) t) (deriv (σ (k + 2)) t) = 0 := by
    rw [hw]
    unfold det2 at hv ⊢
    simp only [Pi.sub_apply]
    linear_combination hv
  have hbw := bdy_det2_eq_zero_of_parallel ((hpar k).2.1 t) h huw
  -- the closed cone at `k + 2`
  have e3 : σ (k + 2 + 1) t = -σ k t := by
    rw [show k + 2 + 1 = k + 3 by ring]; exact (hm t k).2.1
  have e4 : σ (k + 2 + 2) t = -(σ k t + σ (k + 2) t) := by
    rw [show k + 2 + 2 = k + 1 + 3 by ring, ← e1]; exact (hm t (k + 1)).2.1
  rw [e3, e4] at hcone
  obtain ⟨hc1, hc2⟩ := hcone
  have haw : det2 (σ k t) (deriv (σ (k + 2)) t) = 0 := by
    unfold det2 at hc1 hc2 hbw ⊢
    simp only [Pi.neg_apply, Pi.add_apply] at hc1 hc2
    linarith
  have hab : det2 (σ k t) (σ (k + 2) t) ≠ 0 := by
    have := (hm t k).2.2
    simp only at this
    rw [e1] at this
    have h' : det2 (σ k t) (σ (k + 2) t) = √3 / 2 := by
      rw [← this]; unfold det2; simp only [Pi.add_apply]; ring
    rw [h']
    positivity
  exact (hpar (k + 2)).2.1 t (bdy_eq_zero_of_det2 hab haw hbw)

/-- **Lemma 2.4.5** (star conditions; `lem:star-conditions`). Let `K ∈ 𝔎_ccs` be a convex disk with
boundary parameterized by the `C¹` regular multi-curve `σ`. At a given time `t`, let
`j ↦ s_j = σ_j(t)` be a multi-point on the boundary of `K`. Then for each `j` and time `t`, the
tangent `σ_j'(t)` points into the open cone with apex `s_j` and bounding rays through `s_{j+1}` and
`s_j + s_{j+1}`: `σ_j'(t) = α (s_{j+1} - s_j) + β s_{j+1}` with `α, β > 0`.

Proof, as in the book. The hexagon `h_K(t)` lies in `K`, and `σ_j'(t)` cannot point into it: the
tangent line at `s_j` supports `K` (`bdy_det2_deriv_sub_nonneg`). If `σ_j'(t)` points along the
edge `s_j s_{j+1}`, then `σ_{j+1}'(t)` does too, and the closed cone at `j + 2` forces
`σ_{j+2}'(t) = 0` (`bdy_det2_deriv_two_ne`). If it points along `s_j (s_j + s_{j+1})`, then
`σ_{j-1}'(t)` points along `s_{j-1} s_j`, the first case for `j - 1`.

Departure from the paper (a simpler argument for one step): the book gets the bound on the side of
the ray through `s_j + s_{j+1}` "dually", from `σ_{j+2}'(t)`. Here both bounds of the closed cone
(`bdy_cone_closed`) come from the support line at `s_j`: `h_K(t)` has the two edges `s_j s_{j+1}`
and `s_j s_{j-1}` at `s_j`, with `s_{j+1} - s_j = s_{j+2}` and `s_{j-1} - s_j = -s_{j+1}`, and both
lie to the left of the tangent line. -/
theorem lemma2_4_5 {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {σ : ZMod 6 → ℝ → Fin 2 → ℝ}
    (hσ : IsBoundaryMultiCurve K σ) (j : ZMod 6) (t : ℝ) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧
      deriv (σ j) t = α • (σ (j + 1) t - σ j t) + β • σ (j + 1) t := by
  -- the closed cone
  obtain ⟨hc1, hc2⟩ := bdy_cone_closed hK hσ j t
  -- `σ_j'(t)` does not point along the edge `s_j s_{j+1}`
  have hne2 := bdy_det2_deriv_two_ne hK hσ j t
  obtain ⟨hpar, hm⟩ := hσ
  have hd : ∀ i, Differentiable ℝ (σ i) := fun i ↦ (hpar i).1.differentiable (by norm_num)
  have e1 : σ (j + 1) t = σ j t + σ (j + 2) t := bdy_mp_succ (hm t) j
  -- `σ_j'(t)` does not point along the edge `s_j (s_j + s_{j+1})`: otherwise the tangent line at
  -- `s_j` passes through `s_{j-1} = s_{j+5}`, and `σ_{j-1}'(t)` points along `s_{j-1} s_j`
  have hne1 : det2 (σ (j + 1) t) (deriv (σ j) t) ≠ 0 := by
    intro h
    have e5 : σ (j + 5) t = -σ (j + 2) t := by
      have := (hm t (j + 2)).2.1
      rwa [show j + 2 + 3 = j + 5 by ring] at this
    have hv : det2 (deriv (σ j) t) (deriv (σ (j + 5)) t) = 0 := by
      refine bdy_det2_deriv_eq_zero hK (hpar j) (hd _) (fun τ ↦ bdy_mem hK (hpar (j + 5)) τ) ?_
      rw [e5]
      rw [e1] at h
      unfold det2 at h ⊢
      simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply] at h ⊢
      linarith
    have hu1 : det2 (deriv (σ j) t) (σ (j + 1) t) = 0 := by
      unfold det2 at h ⊢; linarith
    have hpar' := bdy_det2_eq_zero_of_parallel ((hpar j).2.1 t) hv hu1
    have h7 : j + 5 + 2 = j + 1 := by rw [add_assoc]; congr 1
    exact bdy_det2_deriv_two_ne hK ⟨hpar, hm⟩ (j + 5) t (by rwa [h7])
  -- write `σ_j'(t)` in the basis `s_{j+1}, s_{j+2}`
  have hD : det2 (σ (j + 1) t) (σ (j + 2) t) = √3 / 2 := by
    have := (hm t (j + 1)).2.2
    rwa [show j + 1 + 1 = j + 2 by ring] at this
  have hDpos : 0 < det2 (σ (j + 1) t) (σ (j + 2) t) := by rw [hD]; positivity
  refine ⟨det2 (σ (j + 1) t) (deriv (σ j) t) / det2 (σ (j + 1) t) (σ (j + 2) t),
    det2 (deriv (σ j) t) (σ (j + 2) t) / det2 (σ (j + 1) t) (σ (j + 2) t),
    div_pos (lt_of_le_of_ne hc1 (Ne.symm hne1)) hDpos,
    div_pos (lt_of_le_of_ne hc2 (Ne.symm hne2)) hDpos, ?_⟩
  have e12 : σ (j + 1) t - σ j t = σ (j + 2) t := by rw [e1]; abel
  rw [e12]
  exact bdy_cramer _ hDpos.ne'

/-- **Lemma 2.4.6** (curvature constraint; `lem:local-curvature-constrt`, equation
`eqn:local-convexity`). Consider a convex disk `K ∈ 𝔎_ccs` with boundary parameterized by a `C¹`
regular multi-curve `σ` with Lipschitz continuous derivative. Then almost everywhere
`det(σ_j'(t), σ_j''(t)) ≥ 0` for `j ∈ ℤ/6ℤ`.

The second derivatives exist almost everywhere by the Lipschitz assumption (Rademacher's
theorem), and the inequality holds wherever `σ_j''` exists.

Departure from the paper: the book deduces the inequality from Shifrin's Proposition 3.8 (a
simple closed regular plane curve is convex iff its signed curvature can be made nonnegative),
which is stated for smooth (`C^∞`) curves, whereas `σ_j` is only `C¹` with Lipschitz derivative,
so the cited theorem's hypotheses are not met. Instead we argue directly: each tangent line
supports `K` (`K` lies to its left, `bdy_det2_deriv_sub_nonneg`), so
`f(t) = det(σ_j'(t₀), σ_j(t) - σ_j(t₀)) ≥ 0` with `f(t₀) = f'(t₀) = 0`; hence
`det(σ_j'(t₀), σ_j''(t₀)) = f''(t₀) ≥ 0` wherever `σ_j''(t₀)` exists (if `f''(t₀) < 0`, the second
derivative test makes `t₀` a local maximum of `f ≥ 0 = f(t₀)`, so `f = 0` near `t₀` and
`f''(t₀) = 0`). -/
theorem lemma2_4_6 {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {σ : ZMod 6 → ℝ → Fin 2 → ℝ}
    (hσ : IsBoundaryMultiCurve K σ) (hlip : ∀ j, ∃ C, LipschitzWith C (deriv (σ j)))
    (j : ZMod 6) : ∀ᵐ t, 0 ≤ det2 (deriv (σ j) t) (deriv (deriv (σ j)) t) := by
  obtain ⟨hpar, -⟩ := hσ
  -- the second derivative exists almost everywhere, by the Lipschitz assumption (Rademacher)
  obtain ⟨C, hC⟩ := hlip j
  filter_upwards [hC.ae_differentiableAt (μ := volume)] with t₀ hdd
  have hdiff : Differentiable ℝ (σ j) := (hpar j).1.differentiable (by norm_num)
  set u := deriv (σ j) t₀ with hu
  -- `f(t) = det(σ_j'(t₀), σ_j(t) - σ_j(t₀)) ≥ 0`, since the tangent line at `t₀` supports `K`
  set f : ℝ → ℝ := fun t ↦ det2 u (σ j t - σ j t₀) with hf
  have hf_nonneg : ∀ t, 0 ≤ f t :=
    fun t ↦ bdy_det2_deriv_sub_nonneg hK (hpar j) t₀ (bdy_mem hK (hpar j) t)
  have hf0 : f t₀ = 0 := by simp [f, det2]
  have hdf : deriv f = fun t ↦ det2 u (deriv (σ j) t) :=
    funext fun t ↦ (bdy_hasDerivAt_det2 u (σ j t₀) (hdiff t).hasDerivAt).deriv
  -- `f'(t₀) = 0`
  have hdf0 : deriv f t₀ = 0 := by
    rw [hdf]
    simp only [hu, det2]
    ring
  -- `f''(t₀) = det(σ_j'(t₀), σ_j''(t₀))`
  have hddf : deriv (deriv f) t₀ = det2 u (deriv (deriv (σ j)) t₀) := by
    rw [hdf]
    have := bdy_hasDerivAt_det2 u 0 hdd.hasDerivAt
    simp only [sub_zero] at this
    exact this.deriv
  by_contra hneg
  have hlt : deriv (deriv f) t₀ < 0 := by rw [hddf]; exact not_le.1 hneg
  -- by the second derivative test `t₀` would be a local maximum of `f ≥ 0 = f(t₀)`, so `f = 0`
  -- near `t₀`, and then `f''(t₀) = 0`
  have hmax : IsLocalMax f t₀ := isLocalMax_of_deriv_deriv_neg hlt hdf0
    (bdy_hasDerivAt_det2 u (σ j t₀) (hdiff t₀).hasDerivAt).continuousAt
  have hev : f =ᶠ[nhds t₀] fun _ ↦ (0 : ℝ) :=
    Filter.Eventually.mono hmax fun t ht ↦ le_antisymm (hf0 ▸ ht) (hf_nonneg t)
  have h0 := hev.deriv.deriv_eq
  simp only [deriv_const'] at h0
  linarith

/-! ### The balanced Reinhardt problem -/

/-- **Problem 2.4.8** (balanced Reinhardt problem in circle representation;
`pbm:reinhardt-reduction-2`). Describe those `K_min ∈ 𝔎_bal` in circle representation for which
`area(K_min) = inf {area(K) | K ∈ 𝔎_bal in circle representation}`. This predicate says that `K`
is such a minimizer: it is a balanced disk in circle representation whose area is at most that of
every balanced disk in circle representation. -/
def IsBalancedCircleMinimizer (K : Set (Fin 2 → ℝ)) : Prop :=
  (∃ σ tf, IsBalancedPair K σ tf ∧ IsCircleRepresentation σ) ∧
    ∀ K' σ' tf', IsBalancedPair K' σ' tf' → IsCircleRepresentation σ' → volume K ≤ volume K'

end SmoothedPolygons
