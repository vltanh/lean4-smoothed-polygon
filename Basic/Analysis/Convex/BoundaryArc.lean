module

public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Arcs of the boundary of a convex body

Let `K` be a convex set with `0` in its interior in a real normed space (in the applications, a
convex domain of the plane). This file gives the facts about the boundary curve `C = ∂K` that
classical arguments in the geometry of numbers use without proof ("by the convexity of `C`").

* **Radial projection.** `radialProj K x = x / g(x)`, where `g` is the gauge (Minkowski functional)
  of `K`, maps every `x ≠ 0` to the point where the ray from `0` through `x` meets `∂K`
  (`radialProj_mem_frontier`), continuously (`continuousAt_radialProj`), and is the identity on
  `∂K`. For a bounded `K` in the plane it parametrizes `∂K` by direction.
* **Arcs.** For boundary points `R, S`, `arc K R S` is the set of boundary points in the cone
  `{aR + bS | a, b ≥ 0}`: when `R, S` are linearly independent, the arc of `∂K` from `R` to `S`
  subtending an angle less than `π`. Its inner points (`a, b > 0`) form `openArc K R S`. A point
  `P*` of an arc *separates* `P` from `P**` when `P* ∈ openArc K P P**`. The arc is the image of
  the chord `[R, S]` under the radial projection, which gives the intermediate value theorem on
  arcs (`exists_mem_arc_eq`).
* **Chords.** A point `aR + bS` of `K` with `b < 0` lies on the same side of the chord `RS` as `0`
  (`a + b ≤ 1`, `add_le_one_of_neg`): the part of `K` beyond the chord lies in the cone of `R` and
  `S`, and conversely boundary points in that cone lie beyond the chord (`one_le_add`).
* **Segments.** If a boundary point is an inner point of a segment of `K`, the whole segment lies
  on the boundary (`not_mem_interior_of_mem_segment`); a line whose chord has interior inner points
  meets the boundary only at the ends of the chord (`eq_zero_or_eq_one_of_collinear`).
* **Arcs without extreme points.** In the plane, an arc none of whose inner points is an extreme
  point of `K` is the chord `[R, S]`: its midpoint lies on the boundary
  (`midpoint_mem_frontier_of_forall_not_mem_extremePoints`). The cap of `K` beyond the chord is
  the closed convex hull of its extreme points (Krein–Milman), and an extreme point of the cap
  strictly beyond the chord is an extreme point of `K` on the open arc.
-/

@[expose] public section

open Set Filter Topology

namespace BoundaryArc

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E}

/-- The arc of the boundary of `K` between `R` and `S`: the boundary points in the cone spanned by
`R` and `S`. -/
def arc (K : Set E) (R S : E) : Set E :=
  {X | X ∈ frontier K ∧ ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ X = a • R + b • S}

/-- The inner points of the arc between `R` and `S`: the boundary points `aR + bS`, `a, b > 0`. -/
def openArc (K : Set E) (R S : E) : Set E :=
  {X | X ∈ frontier K ∧ ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ X = a • R + b • S}

/-- The radial projection `x ↦ x / g(x)` onto the boundary (`g` the gauge of `K`). -/
noncomputable def radialProj (K : Set E) (x : E) : E := (gauge K x)⁻¹ • x

lemma openArc_subset_arc (R S : E) : openArc K R S ⊆ arc K R S :=
  fun _ ⟨hX, a, b, ha, hb, h⟩ ↦ ⟨hX, a, b, ha.le, hb.le, h⟩

/-- `a x + b y ∈ int K` for `x, y ∈ K`, `a, b ≥ 0`, `a + b < 1`, when `0 ∈ int K`. -/
lemma comb_mem_interior (hK : Convex ℝ K) (h0 : (0 : E) ∈ interior K) {x y : E} (hx : x ∈ K)
    (hy : y ∈ K) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b < 1) :
    a • x + b • y ∈ interior K := by
  rcases (add_nonneg ha hb).eq_or_lt with h | h
  · have h1 : a = 0 := by linarith
    have h2 : b = 0 := by linarith
    simpa [h1, h2] using h0
  · have hz : (a / (a + b)) • x + (b / (a + b)) • y ∈ K :=
      hK hx hy (div_nonneg ha h.le) (div_nonneg hb h.le) (by field_simp)
    have := hK.combo_interior_self_mem_interior h0 hz (a := 1 - (a + b)) (b := a + b)
      (by linarith) h.le (by ring)
    convert this using 1
    rw [smul_zero, zero_add, smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ h.ne',
      mul_div_cancel₀ _ h.ne']

/-- **The part of `K` beyond a chord lies in the cone of its ends.** If `R ∉ int K`, `S ∈ K` and
`aR + bS ∈ K` with `b < 0`, then `a + b ≤ 1`: otherwise `R` would be a combination of
`aR + bS` and `S` with nonnegative weights of sum `< 1`, an interior point. -/
lemma add_le_one_of_neg (hK : Convex ℝ K) (h0 : (0 : E) ∈ interior K) {R S : E}
    (hR : R ∉ interior K) (hS : S ∈ K) {a b : ℝ} (hX : a • R + b • S ∈ K) (hb : b < 0) :
    a + b ≤ 1 := by
  by_contra h
  push Not at h
  have ha : 0 < a := by linarith
  apply hR
  have := comb_mem_interior hK h0 hX hS (a := 1 / a) (b := -b / a) (by positivity)
    (div_nonneg (by linarith) ha.le) (by rw [← add_div, div_lt_one ha]; linarith)
  convert this using 1
  rw [smul_add, smul_smul, smul_smul, one_div, inv_mul_cancel₀ ha.ne', one_smul, add_assoc,
    ← add_smul, show a⁻¹ * b + -b / a = 0 by ring, zero_smul, add_zero]

/-- **Boundary points in the cone of a chord lie beyond it.** If `R, S ∈ K` and `aR + bS ∉ int K`
with `a, b ≥ 0`, then `a + b ≥ 1`. -/
lemma one_le_add (hK : Convex ℝ K) (h0 : (0 : E) ∈ interior K) {R S : E} (hR : R ∈ K)
    (hS : S ∈ K) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hX : a • R + b • S ∉ interior K) :
    1 ≤ a + b := by
  by_contra h
  push Not at h
  exact hX (comb_mem_interior hK h0 hR hS ha hb h)

/-- **A segment through a boundary point lies on the boundary.** If a point `Y ∉ int K` is an inner
point of a segment `[U, V]` of `K`, no point of `[U, V]` is interior (a functional separating `Y`
from `int K` is constant on the segment). -/
lemma not_mem_interior_of_mem_segment (hK : Convex ℝ K) (hne : (interior K).Nonempty)
    {U V Y Z : E} (hU : U ∈ K) (hV : V ∈ K) (hY : Y ∈ openSegment ℝ U V) (hYi : Y ∉ interior K)
    (hZ : Z ∈ segment ℝ U V) : Z ∉ interior K := by
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hK.interior isOpen_interior hYi
  have hle : ∀ x ∈ K, f x ≤ f Y := by
    intro x hx
    have hcl : K ⊆ closure (interior K) := by
      rw [hK.closure_interior_eq_closure_of_nonempty_interior hne]; exact subset_closure
    exact closure_minimal (fun z hz ↦ (hf z hz).le) (isClosed_le f.continuous continuous_const)
      (hcl hx)
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hY
  have e1 := hle U hU
  have e2 := hle V hV
  simp only [map_add, map_smul, smul_eq_mul] at e1 e2 ⊢
  obtain rfl : a = 1 - b := by linarith
  have h1 : f U ≤ f V := by
    by_contra h; push Not at h; nlinarith [mul_pos hb (sub_pos.2 h)]
  have h2 : f V ≤ f U := by
    by_contra h; push Not at h; nlinarith [mul_pos ha (sub_pos.2 h)]
  intro hZi
  have := hf Z hZi
  obtain ⟨c, d, hc, hd, hcd, rfl⟩ := hZ
  simp only [map_add, map_smul, smul_eq_mul] at this
  have hfe : f V = f U := le_antisymm h2 h1
  rw [hfe] at this
  have k1 : c * f U + d * f U = f U := by rw [← add_mul, hcd, one_mul]
  have k2 : (1 - b) * f U + b * f U = f U := by ring
  linarith

/-- **A line meets the boundary at most twice unless it contains a boundary segment.** Let
`U, V ∉ int K` be points such that the inner points of the segment `[U, V]` are interior points of
`K`. Then a point `(1 - t) U + t V` of the line `UV` lying in `K` but not in its interior is `U`
(`t = 0`) or `V` (`t = 1`). -/
lemma eq_zero_or_eq_one_of_collinear (hK : Convex ℝ K) {U V : E} (hU : U ∉ interior K)
    (hV : V ∉ interior K) (hseg : ∀ t ∈ Ioo (0 : ℝ) 1, (1 - t) • U + t • V ∈ interior K)
    {t : ℝ} (hX : (1 - t) • U + t • V ∈ K) (hXi : (1 - t) • U + t • V ∉ interior K) :
    t = 0 ∨ t = 1 := by
  have hM := hseg (1 / 2) ⟨by norm_num, by norm_num⟩
  by_contra h
  push Not at h
  rcases lt_or_gt_of_ne h.1 with h0 | h0
  · -- `t < 0`: `U` lies between the midpoint and `X`
    apply hU
    have hd : (1 - 2 * t) ≠ 0 := by linarith
    set l := (-2 * t) / (1 - 2 * t) with hl
    set m := 1 / (1 - 2 * t) with hm
    have e1 : l * (1 - 1 / 2) + m * (1 - t) = 1 := by rw [hl, hm]; field_simp; ring
    have e2 : l * (1 / 2) + m * t = 0 := by rw [hl, hm]; field_simp; ring
    have := hK.combo_interior_self_mem_interior hM hX (a := l) (b := m)
      (by rw [hl]; exact div_pos (by linarith) (by linarith))
      (by rw [hm]; exact (div_pos one_pos (by linarith)).le)
      (by rw [hl, hm, ← add_div, div_eq_one_iff_eq hd]; ring)
    convert this using 1
    calc U = (l * (1 - 1 / 2) + m * (1 - t)) • U + (l * (1 / 2) + m * t) • V := by
          rw [e1, e2, one_smul, zero_smul, add_zero]
      _ = _ := by module
  rcases lt_or_gt_of_ne h.2 with h1 | h1
  · exact hXi (hseg t ⟨h0, h1⟩)
  · -- `t > 1`: `V` lies between the midpoint and `X`
    apply hV
    have hd : (2 * t - 1) ≠ 0 := by linarith
    set l := (2 * t - 2) / (2 * t - 1) with hl
    set m := 1 / (2 * t - 1) with hm
    have e1 : l * (1 - 1 / 2) + m * (1 - t) = 0 := by rw [hl, hm]; field_simp; ring
    have e2 : l * (1 / 2) + m * t = 1 := by rw [hl, hm]; field_simp; ring
    have := hK.combo_interior_self_mem_interior hM hX (a := l) (b := m)
      (by rw [hl]; exact div_pos (by linarith) (by linarith))
      (by rw [hm]; exact (div_pos one_pos (by linarith)).le)
      (by rw [hl, hm, ← add_div, div_eq_one_iff_eq hd]; ring)
    convert this using 1
    calc V = (l * (1 - 1 / 2) + m * (1 - t)) • U + (l * (1 / 2) + m * t) • V := by
          rw [e1, e2, one_smul, zero_smul, zero_add]
      _ = _ := by module

/-! ### The radial projection -/

lemma gauge_pos_of_ne_zero (h0 : (0 : E) ∈ interior K) (hb : Bornology.IsBounded K) {x : E}
    (hx : x ≠ 0) : 0 < gauge K x :=
  (gauge_pos (absorbent_nhds_zero (mem_interior_iff_mem_nhds.1 h0))
    (NormedSpace.isVonNBounded_of_isBounded ℝ hb)).2 hx

/-- The radial projection of `x ≠ 0` lies on the boundary. -/
lemma radialProj_mem_frontier (hK : Convex ℝ K) (h0 : (0 : E) ∈ interior K)
    (hb : Bornology.IsBounded K) {x : E} (hx : x ≠ 0) : radialProj K x ∈ frontier K := by
  have hg := gauge_pos_of_ne_zero h0 hb hx
  rw [← gauge_eq_one_iff_mem_frontier hK (mem_interior_iff_mem_nhds.1 h0), radialProj,
    gauge_smul_of_nonneg (inv_nonneg.2 hg.le), smul_eq_mul, inv_mul_cancel₀ hg.ne']

/-- The radial projection is the identity on the boundary. -/
lemma radialProj_of_mem_frontier (hK : Convex ℝ K) (h0 : (0 : E) ∈ interior K) {x : E}
    (hx : x ∈ frontier K) : radialProj K x = x := by
  rw [radialProj, (gauge_eq_one_iff_mem_frontier hK (mem_interior_iff_mem_nhds.1 h0)).2 hx,
    inv_one, one_smul]

/-- The radial projection is continuous away from `0`. -/
lemma continuousAt_radialProj (hK : Convex ℝ K) (h0 : (0 : E) ∈ interior K)
    (hb : Bornology.IsBounded K) {x : E} (hx : x ≠ 0) : ContinuousAt (radialProj K) x := by
  have hc := continuous_gauge hK (mem_interior_iff_mem_nhds.1 h0)
  exact ((hc.continuousAt.inv₀ (gauge_pos_of_ne_zero h0 hb hx).ne').smul continuousAt_id)

/-- **Intermediate value theorem on arcs.** If `R, S` are boundary points with `0 ∉ [R, S]` and `f`
is continuous with `f(R) ≤ c ≤ f(S)`, some point `X` of the arc between `R` and `S` has
`f(X) = c` (the arc is the radial projection of the chord `[R, S]`). -/
lemma exists_mem_arc_eq (hK : Convex ℝ K) (h0 : (0 : E) ∈ interior K)
    (hb : Bornology.IsBounded K) {R S : E} (hR : R ∈ frontier K) (hS : S ∈ frontier K)
    (hRS : (0 : E) ∉ segment ℝ R S) {f : E → ℝ} (hf : Continuous f) {c : ℝ} (hRc : f R ≤ c)
    (hSc : c ≤ f S) : ∃ X ∈ arc K R S, f X = c := by
  set p : ℝ → E := fun τ ↦ (1 - τ) • R + τ • S with hp
  have hp0 : ∀ τ ∈ Icc (0 : ℝ) 1, p τ ≠ 0 := by
    intro τ hτ h
    apply hRS
    rw [← h]
    exact ⟨1 - τ, τ, by linarith [hτ.2], hτ.1, by ring, rfl⟩
  have hcont : ContinuousOn (fun τ ↦ f (radialProj K (p τ))) (Icc 0 1) := by
    intro τ hτ
    have h1 : ContinuousAt p τ := by fun_prop
    exact (hf.continuousAt.comp ((continuousAt_radialProj hK h0 hb (hp0 τ hτ)).comp h1))
      |>.continuousWithinAt
  have e0 : f (radialProj K (p 0)) = f R := by
    simp only [hp, sub_zero, one_smul, zero_smul, add_zero, radialProj_of_mem_frontier hK h0 hR]
  have e1 : f (radialProj K (p 1)) = f S := by
    simp only [hp, sub_self, zero_smul, one_smul, zero_add, radialProj_of_mem_frontier hK h0 hS]
  obtain ⟨τ, hτ, hτc⟩ := intermediate_value_Icc zero_le_one hcont (by rw [e0, e1]; exact ⟨hRc, hSc⟩)
  have hg := gauge_pos_of_ne_zero h0 hb (hp0 τ hτ)
  refine ⟨radialProj K (p τ), ⟨radialProj_mem_frontier hK h0 hb (hp0 τ hτ),
    (gauge K (p τ))⁻¹ * (1 - τ), (gauge K (p τ))⁻¹ * τ,
    mul_nonneg (inv_nonneg.2 hg.le) (by linarith [hτ.2]), mul_nonneg (inv_nonneg.2 hg.le) hτ.1,
    ?_⟩, hτc⟩
  simp only [radialProj, hp, smul_add, smul_smul]

/-! ### Arcs without extreme points -/

/-- **An arc whose inner points are not extreme points is a segment.** Let `K` be a compact convex
set with `0` in its interior in a plane (`finrank ℝ E = 2`), and `R, S` linearly independent
boundary points such that no inner point of the arc between them is an extreme point of `K`. Then
the midpoint of `R` and `S` lies on the boundary of `K` (so does the whole chord `[R, S]`, by
`not_mem_interior_of_mem_segment`, and the arc is the chord). -/
theorem midpoint_mem_frontier_of_forall_not_mem_extremePoints [FiniteDimensional ℝ E]
    (hE : Module.finrank ℝ E = 2) (hK : Convex ℝ K) (hKc : IsCompact K)
    (h0 : (0 : E) ∈ interior K) {R S : E} (hR : R ∈ frontier K) (hS : S ∈ frontier K)
    (hRS : LinearIndependent ℝ ![R, S]) (h : ∀ X ∈ openArc K R S, X ∉ K.extremePoints ℝ) :
    (1 / 2 : ℝ) • (R + S) ∈ frontier K := by
  have hKcl := hKc.isClosed
  have hRK : R ∈ K := hKcl.frontier_subset hR
  have hSK : S ∈ K := hKcl.frontier_subset hS
  -- coordinates with respect to `R, S`
  set b := basisOfLinearIndependentOfCardEqFinrank hRS (by simp [hE])
  set α : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (b.coord 0)
  set β : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (b.coord 1)
  have hb0 : b 0 = R := by simp [b]
  have hb1 : b 1 = S := by simp [b]
  have hdec : ∀ x, x = α x • R + β x • S := by
    intro x
    have := b.sum_repr x
    rw [Fin.sum_univ_two, hb0, hb1] at this
    simpa [α, β] using this.symm
  have hαR : α R = 1 := by simp [α, ← hb0]
  have hβR : β R = 0 := by simp [β, ← hb0]
  have hαS : α S = 0 := by simp [α, ← hb1]
  have hβS : β S = 1 := by simp [β, ← hb1]
  have hR0 : R ≠ 0 := hRS.ne_zero 0
  -- the cap beyond the chord
  set Cap := K ∩ ({x | 0 ≤ α x} ∩ {x | 0 ≤ β x} ∩ {x | 1 ≤ α x + β x}) with hCap
  have hCapc : IsCompact Cap := hKc.inter_right (((isClosed_le continuous_const α.continuous).inter
    (isClosed_le continuous_const β.continuous)).inter
    (isClosed_le continuous_const (α.continuous.add β.continuous)))
  have hCapv : Convex ℝ Cap := by
    refine hK.inter ?_
    intro x hx y hy s t hs ht hst
    simp only [mem_inter_iff, mem_ofPred_eq, map_add, map_smul, smul_eq_mul] at hx hy ⊢
    refine ⟨⟨by nlinarith, by nlinarith⟩, by nlinarith⟩
  set T := {x : E | α x + β x ≤ 1} with hT
  have hTc : IsClosed T := isClosed_le (α.continuous.add β.continuous) continuous_const
  have hTv : Convex ℝ T := by
    intro x hx y hy s t hs ht hst
    simp only [hT, mem_ofPred_eq, map_add, map_smul, smul_eq_mul] at hx hy ⊢
    nlinarith
  -- the open set of points strictly beyond the chord, inside the cone
  set U := {x : E | 0 < α x} ∩ {x | 0 < β x} ∩ {x | 1 < α x + β x} with hU
  have hUo : IsOpen U := ((isOpen_lt continuous_const α.continuous).inter
    (isOpen_lt continuous_const β.continuous)).inter
    (isOpen_lt continuous_const (α.continuous.add β.continuous))
  have hUK : ∀ x ∈ U, x ∈ K → x ∈ Cap := fun x hx hxK ↦ by
    simp only [hU, hCap, mem_inter_iff, mem_ofPred_eq] at hx ⊢
    exact ⟨hxK, ⟨hx.1.1.le, hx.1.2.le⟩, hx.2.le⟩
  -- shrinking a segment through a point of `U` towards it
  have shrink : ∀ X ∈ U, X ∈ K → ∀ x₁ ∈ K, ∀ x₂ ∈ K, X ∈ openSegment ℝ x₁ x₂ →
      ∃ ε : ℝ, 0 < ε ∧ X + ε • (x₁ - X) ∈ Cap ∧ X + ε • (x₂ - X) ∈ Cap ∧
        X ∈ openSegment ℝ (X + ε • (x₁ - X)) (X + ε • (x₂ - X)) := by
    intro X hXU hXK x₁ hx₁ x₂ hx₂ hseg
    have c1 : Continuous fun ε : ℝ ↦ X + ε • (x₁ - X) := by fun_prop
    have c2 : Continuous fun ε : ℝ ↦ X + ε • (x₂ - X) := by fun_prop
    have ev1 : ∀ᶠ ε in 𝓝 (0 : ℝ), X + ε • (x₁ - X) ∈ U :=
      c1.continuousAt.preimage_mem_nhds (by simpa using hUo.mem_nhds hXU)
    have ev2 : ∀ᶠ ε in 𝓝 (0 : ℝ), X + ε • (x₂ - X) ∈ U :=
      c2.continuousAt.preimage_mem_nhds (by simpa using hUo.mem_nhds hXU)
    obtain ⟨ε, ⟨⟨h1, h2⟩, hε1⟩, hε0⟩ := (((ev1.and ev2).and (Iio_mem_nhds one_pos)).filter_mono
      nhdsWithin_le_nhds |>.and (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
    have hε0' : (0 : ℝ) < ε := hε0
    have hε1' : ε < 1 := hε1
    have mem : ∀ x ∈ K, X + ε • (x - X) ∈ K := fun x hx ↦ by
      have := hK hXK hx (by linarith : (0 : ℝ) ≤ 1 - ε) hε0'.le (by ring)
      convert this using 1; module
    refine ⟨ε, hε0', hUK _ h1 (mem _ hx₁), hUK _ h2 (mem _ hx₂), ?_⟩
    obtain ⟨a, c, ha, hc, hac, hX⟩ := hseg
    refine ⟨a, c, ha, hc, hac, ?_⟩
    obtain rfl : c = 1 - a := by linarith
    rw [← hX]
    module
  -- the extreme points of the cap lie on the chord side
  have hext : Cap.extremePoints ℝ ⊆ T := by
    intro X hX
    rw [mem_extremePoints] at hX
    obtain ⟨hXC, hXe⟩ := hX
    by_contra hXT
    simp only [hT, mem_ofPred_eq, not_le] at hXT
    obtain ⟨hXK, ⟨hαX, hβX⟩, -⟩ := hXC
    have hαX' : 0 < α X := by
      refine lt_of_le_of_ne hαX fun h0' ↦ hS.2 ?_
      have hβ1 : 1 < β X := by rw [← h0'] at hXT; linarith
      have := comb_mem_interior hK h0 hXK hXK (a := (β X)⁻¹) (b := 0) (by positivity) le_rfl
        (by rw [add_zero]; exact inv_lt_one_of_one_lt₀ hβ1)
      have hXS : X = β X • S := by
        conv_lhs => rw [hdec X]
        rw [← h0', zero_smul, zero_add]
      convert this using 1
      rw [zero_smul, add_zero]
      calc S = ((β X)⁻¹ * β X) • S := by rw [inv_mul_cancel₀ (by linarith), one_smul]
        _ = (β X)⁻¹ • X := by rw [← smul_smul, ← hXS]
    have hβX' : 0 < β X := by
      refine lt_of_le_of_ne hβX fun h0' ↦ hR.2 ?_
      have hα1 : 1 < α X := by rw [← h0'] at hXT; linarith
      have := comb_mem_interior hK h0 hXK hXK (a := (α X)⁻¹) (b := 0) (by positivity) le_rfl
        (by rw [add_zero]; exact inv_lt_one_of_one_lt₀ hα1)
      have hXR : X = α X • R := by
        conv_lhs => rw [hdec X]
        rw [← h0', zero_smul, add_zero]
      convert this using 1
      rw [zero_smul, add_zero]
      calc R = ((α X)⁻¹ * α X) • R := by rw [inv_mul_cancel₀ (by linarith), one_smul]
        _ = (α X)⁻¹ • X := by rw [← smul_smul, ← hXR]
    have hXU : X ∈ U := ⟨⟨hαX', hβX'⟩, hXT⟩
    by_cases hXi : X ∈ interior K
    · -- an interior point is the midpoint of two nearby points of the cap
      have c1 : Continuous fun δ : ℝ ↦ X + δ • R := by fun_prop
      have c2 : Continuous fun δ : ℝ ↦ X - δ • R := by fun_prop
      have hnh : interior K ∩ U ∈ 𝓝 X := (isOpen_interior.inter hUo).mem_nhds ⟨hXi, hXU⟩
      have ev1 : ∀ᶠ δ in 𝓝 (0 : ℝ), X + δ • R ∈ interior K ∩ U :=
        c1.continuousAt.preimage_mem_nhds (by simpa using hnh)
      have ev2 : ∀ᶠ δ in 𝓝 (0 : ℝ), X - δ • R ∈ interior K ∩ U :=
        c2.continuousAt.preimage_mem_nhds (by simpa using hnh)
      obtain ⟨δ, ⟨h1, h2⟩, hδ⟩ := ((ev1.and ev2).filter_mono nhdsWithin_le_nhds
        |>.and (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
      have hδ' : (0 : ℝ) < δ := hδ
      have := (hXe _ (hUK _ h1.2 (interior_subset h1.1)) _ (hUK _ h2.2 (interior_subset h2.1))
        ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by module⟩).1
      have hz : δ • R = 0 := by
        have := congrArg (· - X) this; simpa using this
      exact hR0 ((smul_eq_zero.1 hz).resolve_left hδ'.ne')
    · -- a boundary point on the open arc is not extreme in `K`, hence not in the cap
      have hXF : X ∈ frontier K := ⟨subset_closure hXK, hXi⟩
      have hnot := h X ⟨hXF, α X, β X, hαX', hβX', hdec X⟩
      rw [mem_extremePoints] at hnot
      push Not at hnot
      obtain ⟨x₁, hx₁, x₂, hx₂, hseg, hne⟩ := hnot hXK
      obtain ⟨ε, hε, h1, h2, hseg'⟩ := shrink X hXU hXK x₁ hx₁ x₂ hx₂ hseg
      obtain ⟨e1, e2⟩ := hXe _ h1 _ h2 hseg'
      have z1 : ε • (x₁ - X) = 0 := by have := congrArg (· - X) e1; simpa using this
      have z2 : ε • (x₂ - X) = 0 := by have := congrArg (· - X) e2; simpa using this
      exact hne (sub_eq_zero.1 ((smul_eq_zero.1 z1).resolve_left hε.ne'))
        (sub_eq_zero.1 ((smul_eq_zero.1 z2).resolve_left hε.ne'))
  -- Krein–Milman: the cap lies on the chord side
  have hCapT : Cap ⊆ T := by
    rw [← closure_convexHull_extremePoints hCapc hCapv]
    exact closure_minimal (convexHull_min hext hTv) hTc
  -- but the midpoint is interior, so a point beyond it is in the cap
  by_contra hmid
  have hMK : (1 / 2 : ℝ) • (R + S) ∈ K := by
    have := hK hRK hSK (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (by norm_num)
    convert this using 1; rw [smul_add]
  have hMi : (1 / 2 : ℝ) • (R + S) ∈ interior K := by
    by_contra hi; exact hmid ⟨subset_closure hMK, hi⟩
  have cμ : Continuous fun μ : ℝ ↦ μ • ((1 / 2 : ℝ) • (R + S)) := by fun_prop
  have evμ : ∀ᶠ μ in 𝓝 (1 : ℝ), μ • ((1 / 2 : ℝ) • (R + S)) ∈ K :=
    cμ.continuousAt.preimage_mem_nhds (by simpa using mem_interior_iff_mem_nhds.1 hMi)
  obtain ⟨μ, hμK, hμ⟩ := ((evμ.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Ioi (1 : ℝ) ∈ 𝓝[>] 1)).exists
  have hμ' : (1 : ℝ) < μ := hμ
  have hαZ : α (μ • ((1 / 2 : ℝ) • (R + S))) = μ / 2 := by
    simp only [map_smul, map_add, hαR, hαS, smul_eq_mul]; ring
  have hβZ : β (μ • ((1 / 2 : ℝ) • (R + S))) = μ / 2 := by
    simp only [map_smul, map_add, hβR, hβS, smul_eq_mul]; ring
  have hZ := hCapT ⟨hμK, ⟨by simp only [mem_ofPred_eq, hαZ]; linarith,
    by simp only [mem_ofPred_eq, hβZ]; linarith⟩, by simp only [mem_ofPred_eq, hαZ, hβZ]; linarith⟩
  simp only [hT, mem_ofPred_eq, hαZ, hβZ] at hZ
  linarith

end BoundaryArc
