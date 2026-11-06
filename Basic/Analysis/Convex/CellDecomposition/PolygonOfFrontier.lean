module

public import Basic.Analysis.Convex.CellDecomposition.Defs
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Order.Interval.Set.Infinite

/-!
# Recognizing a convex polygon

A compact convex set with nonempty interior whose frontier lies on finitely many lines is a convex
polygon. Used by part (B) of the cell lemma
(`Basic.Analysis.Convex.CellDecomposition.PinwheelHoles`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace PlaneConvex

/-- Two points of the plane with the same dot products against `a ≠ 0` and against its rotation
`![-a 1, a 0]` are equal. -/
private lemma pof_eq_of_dotProduct_eq {a p q : Fin 2 → ℝ} (ha : a ≠ 0)
    (h1 : a ⬝ᵥ p = a ⬝ᵥ q) (h2 : ![-a 1, a 0] ⬝ᵥ p = ![-a 1, a 0] ⬝ᵥ q) : p = q := by
  have hpos : a 0 ^ 2 + a 1 ^ 2 ≠ 0 := by
    intro h
    apply ha
    have h0 : a 0 = 0 := by nlinarith [sq_nonneg (a 0), sq_nonneg (a 1)]
    have h1 : a 1 = 0 := by nlinarith [sq_nonneg (a 0), sq_nonneg (a 1)]
    ext i; fin_cases i
    · exact h0
    · exact h1
  simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h1 h2
  have e0 : p 0 = q 0 := by
    have : (a 0 ^ 2 + a 1 ^ 2) * (p 0 - q 0) = 0 := by linear_combination a 0 * h1 - a 1 * h2
    simpa [sub_eq_zero, hpos] using this
  have e1 : p 1 = q 1 := by
    have : (a 0 ^ 2 + a 1 ^ 2) * (p 1 - q 1) = 0 := by linear_combination a 1 * h1 + a 0 * h2
    simpa [sub_eq_zero, hpos] using this
  ext i; fin_cases i
  · exact e0
  · exact e1

/-- An infinite set of reals contains three strictly increasing elements. -/
private lemma pof_exists_three {T : Set ℝ} (hT : T.Infinite) :
    ∃ t₁ ∈ T, ∃ t₂ ∈ T, ∃ t₃ ∈ T, t₁ < t₂ ∧ t₂ < t₃ := by
  obtain ⟨s, hsT, hs⟩ := hT.exists_subset_card_eq 3
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hs
  simp only [Finset.coe_insert, Finset.coe_singleton, insert_subset_iff,
    singleton_subset_iff] at hsT
  obtain ⟨hx, hy, hz⟩ := hsT
  rcases hxy.lt_or_gt with h1 | h1 <;> rcases hxz.lt_or_gt with h2 | h2 <;>
    rcases hyz.lt_or_gt with h3 | h3
  all_goals first
    | exact ⟨x, hx, y, hy, z, hz, by linarith, by linarith⟩
    | exact ⟨x, hx, z, hz, y, hy, by linarith, by linarith⟩
    | exact ⟨y, hy, x, hx, z, hz, by linarith, by linarith⟩
    | exact ⟨y, hy, z, hz, x, hx, by linarith, by linarith⟩
    | exact ⟨z, hz, x, hx, y, hy, by linarith, by linarith⟩
    | exact ⟨z, hz, y, hy, x, hx, by linarith, by linarith⟩

/-- A supporting line at a frontier point of a convex set with nonempty interior in the plane:
there is `w ≠ 0` with `⟨w, x⟩ ≤ ⟨w, m⟩` on `S`. -/
private lemma pof_exists_support {S : Set (Fin 2 → ℝ)} (hconv : Convex ℝ S)
    (hint : (interior S).Nonempty) {m : Fin 2 → ℝ} (hm : m ∈ frontier S) :
    ∃ w : Fin 2 → ℝ, w ≠ 0 ∧ ∀ x ∈ S, w ⬝ᵥ x ≤ w ⬝ᵥ m := by
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hconv.interior isOpen_interior hm.2
  set w : Fin 2 → ℝ := fun i ↦ f (Pi.single i 1) with hw
  have hfw : ∀ x, f x = w ⬝ᵥ x := by
    intro x
    have hx : x = x 0 • (Pi.single 0 1 : Fin 2 → ℝ) + x 1 • Pi.single 1 1 := by
      ext i; fin_cases i <;> simp
    calc f x = f (x 0 • (Pi.single 0 1 : Fin 2 → ℝ) + x 1 • Pi.single 1 1) := by rw [← hx]
      _ = w ⬝ᵥ x := by simp [w, dotProduct, Fin.sum_univ_two]; ring
  refine ⟨w, fun hw0 ↦ ?_, fun x hx ↦ ?_⟩
  · obtain ⟨y, hy⟩ := hint
    have := hf y hy
    rw [hfw, hfw, hw0] at this
    simp at this
  · have hxcl : x ∈ closure (interior S) := by
      rw [hconv.closure_interior_eq_closure_of_nonempty_interior hint]
      exact subset_closure hx
    have hsub : closure (interior S) ⊆ {x | f x ≤ f m} :=
      closure_minimal (fun y hy ↦ (hf y hy).le) (isClosed_le f.continuous continuous_const)
    have := hsub hxcl
    simpa [hfw] using this

/-- If a frontier point of `S` lies strictly inside a segment `[e₁, e₃] ⊆ S` contained in the line
`⟨a, x⟩ = c`, then this line supports `S`. -/
private lemma pof_supports_of_mem_segment {S : Set (Fin 2 → ℝ)} (hconv : Convex ℝ S)
    (hint : (interior S).Nonempty) {a : Fin 2 → ℝ} {c : ℝ} (ha : a ≠ 0)
    {e₁ e₃ : Fin 2 → ℝ} (he₁ : e₁ ∈ S) (he₃ : e₃ ∈ S) (hne : e₁ ≠ e₃)
    (h₁ : a ⬝ᵥ e₁ = c) (h₃ : a ⬝ᵥ e₃ = c) {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hm : (1 - θ) • e₁ + θ • e₃ ∈ frontier S) :
    (∀ x ∈ S, a ⬝ᵥ x ≤ c) ∨ (∀ x ∈ S, c ≤ a ⬝ᵥ x) := by
  obtain ⟨w, hw0, hw⟩ := pof_exists_support hconv hint hm
  have hwm : ∀ v : Fin 2 → ℝ, v ⬝ᵥ ((1 - θ) • e₁ + θ • e₃) = (1 - θ) * v ⬝ᵥ e₁ + θ * v ⬝ᵥ e₃ :=
    fun v ↦ by simp [dotProduct_add, dotProduct_smul]
  have k₁ := hw e₁ he₁
  have k₃ := hw e₃ he₃
  rw [hwm] at k₁ k₃
  have heq : w ⬝ᵥ e₁ = w ⬝ᵥ e₃ := by nlinarith
  have ham : a ⬝ᵥ ((1 - θ) • e₁ + θ • e₃) = c := by rw [hwm, h₁, h₃]; ring
  -- `w` is parallel to `a`
  have hd : e₁ 0 ≠ e₃ 0 ∨ e₁ 1 ≠ e₃ 1 := by
    by_contra h
    simp only [not_or, not_not] at h
    exact hne (by ext i; fin_cases i; exacts [h.1, h.2])
  simp only [dotProduct, Fin.sum_univ_two] at heq h₁ h₃
  have hk : a 1 * w 0 - a 0 * w 1 = 0 := by
    rcases hd with hd | hd
    · have : (a 1 * w 0 - a 0 * w 1) * (e₃ 0 - e₁ 0) = 0 := by
        linear_combination (-a 1) * heq - w 1 * (h₃ - h₁)
      exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr (Ne.symm hd))
    · have : (a 1 * w 0 - a 0 * w 1) * (e₃ 1 - e₁ 1) = 0 := by
        linear_combination w 0 * (h₃ - h₁) + a 0 * heq
      exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr (Ne.symm hd))
  have hpos : a 0 ^ 2 + a 1 ^ 2 ≠ 0 := by
    intro h
    apply ha
    have h0 : a 0 = 0 := by nlinarith [sq_nonneg (a 0), sq_nonneg (a 1)]
    have h1 : a 1 = 0 := by nlinarith [sq_nonneg (a 0), sq_nonneg (a 1)]
    ext i; fin_cases i
    · exact h0
    · exact h1
  set μ := (w 0 * a 0 + w 1 * a 1) / (a 0 ^ 2 + a 1 ^ 2) with hμ
  have hwμ : w = μ • a := by
    have e0 : w 0 = μ * a 0 := by
      rw [hμ]
      field_simp
      linear_combination a 1 * hk
    have e1 : w 1 = μ * a 1 := by
      rw [hμ]
      field_simp
      linear_combination (-a 0) * hk
    ext i; fin_cases i
    · exact e0
    · exact e1
  have hμ0 : μ ≠ 0 := by
    rintro h
    rw [h, zero_smul] at hwμ
    exact hw0 hwμ
  have hS : ∀ x ∈ S, μ * (a ⬝ᵥ x) ≤ μ * c := by
    intro x hx
    have := hw x hx
    rw [hwμ, smul_dotProduct, smul_dotProduct, ham] at this
    simpa using this
  rcases hμ0.lt_or_gt with hneg | hpos'
  · exact Or.inr fun x hx ↦ (mul_le_mul_left_of_neg hneg).1 (hS x hx)
  · exact Or.inl fun x hx ↦ le_of_mul_le_mul_left (hS x hx) hpos'

/-- A line `⟨a, x⟩ = c` meeting the frontier of a closed convex set `S` with nonempty interior in
infinitely many points supports `S`. -/
private lemma pof_supports_of_infinite {S : Set (Fin 2 → ℝ)} (hconv : Convex ℝ S)
    (hclosed : IsClosed S) (hint : (interior S).Nonempty) {a : Fin 2 → ℝ} {c : ℝ} (ha : a ≠ 0)
    (hinf : (frontier S ∩ {x | a ⬝ᵥ x = c}).Infinite) :
    (∀ x ∈ S, a ⬝ᵥ x ≤ c) ∨ (∀ x ∈ S, c ≤ a ⬝ᵥ x) := by
  set v : Fin 2 → ℝ := ![-a 1, a 0] with hv
  have hinj : InjOn (fun x ↦ v ⬝ᵥ x) (frontier S ∩ {x | a ⬝ᵥ x = c}) := by
    intro p hp q hq hpq
    exact pof_eq_of_dotProduct_eq ha (hp.2.trans hq.2.symm) hpq
  obtain ⟨t₁, ht₁, t₂, ht₂, t₃, ht₃, h12, h23⟩ := pof_exists_three (hinf.image hinj)
  obtain ⟨p₁, ⟨hp₁f, hp₁l⟩, rfl⟩ := ht₁
  obtain ⟨p₂, ⟨hp₂f, hp₂l⟩, rfl⟩ := ht₂
  obtain ⟨p₃, ⟨hp₃f, hp₃l⟩, rfl⟩ := ht₃
  change a ⬝ᵥ p₁ = c at hp₁l
  change a ⬝ᵥ p₂ = c at hp₂l
  change a ⬝ᵥ p₃ = c at hp₃l
  set θ := (v ⬝ᵥ p₂ - v ⬝ᵥ p₁) / (v ⬝ᵥ p₃ - v ⬝ᵥ p₁) with hθ
  have h13 : 0 < v ⬝ᵥ p₃ - v ⬝ᵥ p₁ := by linarith
  have hθ0 : 0 < θ := div_pos (by linarith) h13
  have hθ1 : θ < 1 := (div_lt_one h13).2 (by linarith)
  have hp₂eq : p₂ = (1 - θ) • p₁ + θ • p₃ := by
    apply pof_eq_of_dotProduct_eq ha
    · simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, hp₁l, hp₂l, hp₃l]
      ring
    · rw [← hv]
      simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, hθ]
      field_simp
      ring
  rw [hp₂eq] at hp₂f
  refine pof_supports_of_mem_segment hconv hint ha (hclosed.frontier_subset hp₁f)
    (hclosed.frontier_subset hp₃f) ?_ hp₁l hp₃l hθ0 hθ1 hp₂f
  rintro rfl
  linarith

/-- Every sphere `‖w - z‖ = ρ` (sup norm) of small radius around a frontier point `z` of a closed
convex set meets the frontier. -/
private lemma pof_exists_frontier_dist {S : Set (Fin 2 → ℝ)} (hconv : Convex ℝ S)
    (hclosed : IsClosed S) {y z : Fin 2 → ℝ} (hy : y ∈ interior S) (hz : z ∈ frontier S)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : ρ ≤ dist y z) : ∃ w ∈ frontier S, dist w z = ρ := by
  have hzS : z ∈ S := hclosed.frontier_subset hz
  have hyz : 0 < dist y z := hρ0.trans_le hρ
  set t := ρ / dist y z with ht
  have ht0 : 0 < t := div_pos hρ0 hyz
  have ht1 : t ≤ 1 := (div_le_one hyz).2 hρ
  have htd : t * dist y z = ρ := by rw [ht]; field_simp
  -- a point of the interior on the sphere
  have hp : z + t • (y - z) ∈ interior S :=
    hconv.add_smul_sub_mem_interior' (subset_closure hzS) hy ⟨ht0, ht1⟩
  have hpd : dist (z + t • (y - z)) z = ρ := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht0,
      ← dist_eq_norm, htd]
  -- a point outside `S` on the sphere
  have hq : z - t • (y - z) ∉ S := by
    intro hq
    have hmem : (t / (1 + t)) • y + (1 / (1 + t)) • (z - t • (y - z)) ∈ interior S :=
      hconv.combo_interior_self_mem_interior hy hq (by positivity) (by positivity)
        (by rw [← add_div, add_comm t 1, div_self (by positivity)])
    have heq : (t / (1 + t)) • y + (1 / (1 + t)) • (z - t • (y - z)) = z := by
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      field_simp
      ring
    rw [heq] at hmem
    exact hz.2 hmem
  have hqd : dist (z - t • (y - z)) z = ρ := by
    rw [dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht0, ← dist_eq_norm, htd]
  have hconn : IsPreconnected (Metric.sphere z ρ) :=
    (isConnected_sphere (by rw [rank_fin_fun]; norm_num) z hρ0.le).isPreconnected
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  have hsub : Metric.sphere z ρ ⊆ interior S ∪ Sᶜ := by
    intro w hw
    by_cases hwS : w ∈ S
    · left
      by_contra hwi
      exact hcon w ⟨subset_closure hwS, hwi⟩ hw
    · exact Or.inr hwS
  have := hconn.subset_left_of_subset_union isOpen_interior hclosed.isOpen_compl
    (Disjoint.mono_left interior_subset disjoint_compl_right) hsub ⟨_, hpd, hp⟩
  exact hq (interior_subset (this hqd))

/-- Every frontier point of `S` lies on one of the lines `⟨a l, x⟩ = c l` that supports `S`. -/
private lemma pof_exists_supporting_line {S : Set (Fin 2 → ℝ)} (hconv : Convex ℝ S)
    (hclosed : IsClosed S) (hint : (interior S).Nonempty) {ι : Type*} [Finite ι]
    (a : ι → Fin 2 → ℝ) (c : ι → ℝ) (ha : ∀ l, a l ≠ 0)
    (hfr : frontier S ⊆ ⋃ l, {x | a l ⬝ᵥ x = c l}) {z : Fin 2 → ℝ} (hz : z ∈ frontier S) :
    ∃ l, a l ⬝ᵥ z = c l ∧ ((∀ x ∈ S, a l ⬝ᵥ x ≤ c l) ∨ (∀ x ∈ S, c l ≤ a l ⬝ᵥ x)) := by
  by_contra hcon
  have hfin : ∀ l, a l ⬝ᵥ z = c l → (frontier S ∩ {x | a l ⬝ᵥ x = c l}).Finite := by
    intro l hl
    by_contra hinf
    exact hcon ⟨l, hl, pof_supports_of_infinite hconv hclosed hint (ha l) hinf⟩
  have hev : ∀ᶠ x in 𝓝 z, ∀ l, a l ⬝ᵥ z ≠ c l → a l ⬝ᵥ x ≠ c l := by
    rw [Filter.eventually_all]
    intro l
    by_cases hl : a l ⬝ᵥ z = c l
    · exact Filter.Eventually.of_forall fun x h ↦ absurd hl h
    · have hcont : Continuous fun x : Fin 2 → ℝ ↦ a l ⬝ᵥ x := by fun_prop
      exact (hcont.continuousAt.eventually_ne hl).mono fun x hx _ ↦ hx
  obtain ⟨r, hr0, hr⟩ := Metric.eventually_nhds_iff.1 hev
  have hWfin : (frontier S ∩ Metric.ball z r).Finite := by
    refine (Set.finite_iUnion fun l ↦
      (?_ : (frontier S ∩ {x | a l ⬝ᵥ x = c l} ∩ Metric.ball z r).Finite)).subset ?_
    · by_cases hl : a l ⬝ᵥ z = c l
      · exact (hfin l hl).subset inter_subset_left
      · exact Set.finite_empty.subset fun x hx ↦ hr (Metric.mem_ball.1 hx.2) l hl hx.1.2
    · rintro x ⟨hxf, hxb⟩
      obtain ⟨l, hl⟩ := mem_iUnion.1 (hfr hxf)
      exact mem_iUnion.2 ⟨l, ⟨hxf, hl⟩, hxb⟩
  obtain ⟨y, hy⟩ := hint
  have hyz : 0 < dist y z := dist_pos.2 fun h ↦ hz.2 (h ▸ hy)
  have hδ : 0 < min r (dist y z) := lt_min hr0 hyz
  apply Set.Ioo_infinite hδ
  refine (hWfin.image fun w ↦ dist w z).subset ?_
  rintro ρ ⟨hρ0, hρ⟩
  obtain ⟨w, hw, hwd⟩ :=
    pof_exists_frontier_dist hconv hclosed hy hz hρ0 (hρ.le.trans (min_le_right _ _))
  exact ⟨w, ⟨hw, Metric.mem_ball.2 (hwd ▸ hρ.trans_le (min_le_left _ _))⟩, hwd⟩

/-- **Recognizing a convex polygon.** A compact convex set with nonempty interior whose frontier
lies in finitely many lines `⟨a l, x⟩ = c l` (`a l ≠ 0`) is a convex polygon.

Argument. For each `l` such that `L_l = {⟨a l, x⟩ = c l}` meets `frontier S` in a segment of
positive length, `L_l` is a supporting line of `S` (a line containing a nondegenerate piece of the
boundary of a convex body with nonempty interior supports it); let `P_l ⊇ S` be the corresponding
closed half-plane. Then `S = ⋂ P_l`: if `x ∈ ⋂ P_l \ S`, take `y ∈ interior S`; the segment
`[y, x]` leaves `S` at a frontier point `z`; near `z` the frontier is a finite union of pieces of
the `L_l` through `z`, at least one of which has positive length on each side of `z` (the
frontier of a planar convex body is a closed curve without isolated pieces), and the half-planes
`P_l` of the lines carrying them cut off `x`, a contradiction. Boundedness and nonempty interior
are inherited from `S`.

Formalization. A line meeting `frontier S` in three points supports `S` (Hahn–Banach at the
middle point, `pof_supports_of_infinite`). Every frontier point `z` lies on such a line: otherwise
near `z` the frontier would be finite, while every small sup-norm sphere around `z` (connected)
meets both `interior S` and the complement, hence the frontier (`pof_exists_supporting_line`).
So `frontier S` misses the interior of `P = ⋂ P_l`, and the connected set `interior P` lies in
`S`; hence `P = closure (interior P) ⊆ S`. -/
theorem pin_isConvexPolygon_of_frontier_subset {S : Set (Fin 2 → ℝ)} (hconv : Convex ℝ S)
    (hcpt : IsCompact S) (hint : (interior S).Nonempty) {ι : Type*} [Finite ι]
    (a : ι → Fin 2 → ℝ) (c : ι → ℝ) (ha : ∀ l, a l ≠ 0)
    (hfr : frontier S ⊆ ⋃ l, {x | a l ⬝ᵥ x = c l}) :
    IsConvexPolygon S := by
  have hclosed := hcpt.isClosed
  -- the half-planes `P_l` (the whole plane when `L_l` does not support `S`)
  have hex : ∀ l, ∃ (a' : Fin 2 → ℝ) (c' : ℝ), (∀ x ∈ S, a' ⬝ᵥ x ≤ c') ∧
      (((∀ x ∈ S, a l ⬝ᵥ x ≤ c l) ∨ (∀ x ∈ S, c l ≤ a l ⬝ᵥ x)) →
        a' ≠ 0 ∧ ∀ x, a l ⬝ᵥ x = c l → a' ⬝ᵥ x = c') := by
    intro l
    by_cases h1 : ∀ x ∈ S, a l ⬝ᵥ x ≤ c l
    · exact ⟨a l, c l, h1, fun _ ↦ ⟨ha l, fun x hx ↦ hx⟩⟩
    by_cases h2 : ∀ x ∈ S, c l ≤ a l ⬝ᵥ x
    · refine ⟨-a l, -c l, fun x hx ↦ ?_, fun _ ↦ ⟨neg_ne_zero.2 (ha l), fun x hx ↦ ?_⟩⟩
      · simpa [neg_dotProduct] using h2 x hx
      · simp [neg_dotProduct, hx]
    · exact ⟨0, 0, fun x _ ↦ by simp, fun h ↦ (h.elim h1 h2).elim⟩
  choose a' c' hS' hsupp' using hex
  set P := halfPlanesInter a' c' with hP
  have hSP : S ⊆ P := fun x hx l ↦ hS' l x hx
  have hPconv : Convex ℝ P := convex_halfPlanesInter a' c'
  have hintP : interior S ⊆ interior P := interior_mono hSP
  -- frontier points of `S` are not interior points of `P`
  have hfrP : ∀ z ∈ frontier S, z ∉ interior P := by
    intro z hz hzP
    obtain ⟨l, hlz, hsupp⟩ := pof_exists_supporting_line hconv hclosed hint a c ha hfr hz
    obtain ⟨hne, hline⟩ := hsupp' l hsupp
    have heq := hline z hlz
    have hnhds : P ∈ 𝓝 z := mem_interior_iff_mem_nhds.1 hzP
    have htend : Tendsto (fun s : ℝ ↦ z + s • a' l) (𝓝[>] 0) (𝓝 z) := by
      have hcont : Continuous fun s : ℝ ↦ z + s • a' l := by fun_prop
      simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    obtain ⟨s, hsP, hs0⟩ := ((htend.eventually hnhds).and self_mem_nhdsWithin).exists
    have hle := (show ∀ i, a' i ⬝ᵥ (z + s • a' l) ≤ c' i from hsP) l
    rw [dotProduct_add, dotProduct_smul, heq, smul_eq_mul] at hle
    have hpos : 0 < a' l ⬝ᵥ a' l :=
      lt_of_le_of_ne (Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _)
        (Ne.symm (dotProduct_self_eq_zero.not.2 hne))
    have : 0 < s * (a' l ⬝ᵥ a' l) := mul_pos hs0 hpos
    linarith
  -- the connected set `interior P` lies in `S`
  have hintPS : interior P ⊆ S := by
    have h := hPconv.interior.isPreconnected.subset_left_of_subset_union isOpen_interior
      hclosed.isOpen_compl (Disjoint.mono_left interior_subset disjoint_compl_right) ?_ ?_
    · exact h.trans interior_subset
    · intro x hx
      by_cases hxS : x ∈ S
      · left
        by_contra hxi
        exact hfrP x ⟨subset_closure hxS, hxi⟩ hx
      · exact Or.inr hxS
    · obtain ⟨y, hy⟩ := hint
      exact ⟨y, hintP hy, hy⟩
  have hPS : P ⊆ S :=
    calc P ⊆ closure P := subset_closure
      _ = closure (interior P) :=
        (hPconv.closure_interior_eq_closure_of_nonempty_interior (hint.mono hintP)).symm
      _ ⊆ closure S := closure_mono hintPS
      _ = S := hclosed.closure_eq
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  refine ⟨⟨n, a' ∘ e.symm, c' ∘ e.symm, ?_⟩, hcpt.isBounded, hint⟩
  rw [subset_antisymm hSP hPS, hP]
  ext x
  simp only [halfPlanesInter, mem_ofPred_eq, Function.comp_apply]
  constructor
  · intro h i
    exact h _
  · intro h l
    simpa using h (e l)

end PlaneConvex
