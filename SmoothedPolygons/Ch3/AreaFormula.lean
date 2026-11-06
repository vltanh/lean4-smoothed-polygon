module

public import SmoothedPolygons.Ch3.CostFunctional
public import SmoothedPolygons.Ch3.ControlSets
public import Basic.Analysis.Convex.StarCurve
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.Analysis.LocallyConvex.Bounded

/-!
# The area of a balanced disk (`eqn:cost`, §3.2)

For a balanced pair `(K, σ)` whose curves are `σ_j(t) = g(t) s_j*` with `g' = gX`, the area of `K`
is the cost `-(3/2) ∫₀^{t_f} tr(JX) dt` (equation `eqn:cost`). The book computes the area as
`½ ∮_{∂K} θ` for the one-form `θ = x dy - y dx` (Green's theorem), splits the boundary into the
six arcs `σ_j([0, t_f])`, and evaluates the pullbacks by Lemma 3.2.1 and Lemma 3.2.2.

Mathlib has no Green's theorem for such regions. We use instead the polar-coordinates formula
`PlaneCurve.IsStarCurve.volume_radialHull` (the area of the region swept from the origin by a
star-shaped closed curve is `½ ∫ det(γ, γ')`), which is Green's formula for regions star-shaped
about the origin. For it we show that a balanced disk is the region swept from the origin by its
boundary curve `σ₀` (`oct_eq_radialHull`) and that `σ₀` is star-shaped (`oct_isStarCurve`).
-/

@[expose] public section

namespace SmoothedPolygons

open MeasureTheory Matrix Set

/-- `det(Av, Aw) = det(A) det(v, w)`. -/
lemma oct_det2_mulVec (A : Mat2) (v w : Fin 2 → ℝ) :
    det2 (A *ᵥ v) (A *ᵥ w) = A.det * det2 v w := by
  simp only [det2, Matrix.det_fin_two, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- `det(-v, -w) = det(v, w)`. -/
lemma oct_det2_neg (v w : Fin 2 → ℝ) : det2 (-v) (-w) = det2 v w := by
  simp only [det2, Pi.neg_apply]
  ring

/-- The rotation `R` maps the sixth root of unity `s_j*` to `s_{j+1}*`. -/
lemma oct_R_mulVec_sixthRoot (j : ZMod 6) : R *ᵥ sixthRoot j = sixthRoot (j + 1) := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  fin_cases j
  · change R *ᵥ sixthRoot 0 = sixthRoot 1
    rw [algA_sixthRoot_zero, algA_sixthRoot_one]
    ext i; fin_cases i <;> simp [R, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · change R *ᵥ sixthRoot 1 = sixthRoot 2
    rw [algA_sixthRoot_one, algA_sixthRoot_two]
    ext i; fin_cases i <;> simp [R, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
      linarith
  · change R *ᵥ sixthRoot 2 = sixthRoot 3
    rw [algA_sixthRoot_two, algA_sixthRoot_three]
    ext i; fin_cases i <;> simp [R, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
      linarith
  · change R *ᵥ sixthRoot 3 = sixthRoot 4
    rw [algA_sixthRoot_three, algA_sixthRoot_four]
    ext i; fin_cases i <;> simp [R, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · change R *ᵥ sixthRoot 4 = sixthRoot 5
    rw [algA_sixthRoot_four, algA_sixthRoot_five]
    ext i; fin_cases i <;> simp [R, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
      linarith
  · change R *ᵥ sixthRoot 5 = sixthRoot 0
    rw [algA_sixthRoot_five, algA_sixthRoot_zero]
    ext i; fin_cases i <;> simp [R, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
      linarith

/-- `Rⁿ s_j* = s_{j+n}*`. -/
lemma oct_R_pow_mulVec_sixthRoot (n : ℕ) (j : ZMod 6) :
    R ^ n *ᵥ sixthRoot j = sixthRoot (j + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, oct_R_mulVec_sixthRoot]
    push_cast
    ring_nf

/-- In a balanced pair, `det(σ_j, σ_j') = (α + β) √3/2 > 0`: the curves turn counterclockwise
about the origin (items 3 and 5 of Definition 2.4.7). -/
lemma oct_det2_deriv_pos {K : Set (Fin 2 → ℝ)} {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {tf : ℝ}
    (hKσ : IsBalancedPair K σ tf) (j : ZMod 6) (t : ℝ) :
    0 < det2 (σ j t) (deriv (σ j) t) := by
  obtain ⟨-, -, -, hmp, -, hstar, -⟩ := hKσ
  obtain ⟨α, β, hα, hβ, h⟩ := hstar j t
  have hd := ((hmp t) j).2.2
  simp only at hd
  have e : det2 (σ j t) (deriv (σ j) t) = (α + β) * (√3 / 2) := by
    rw [h, ← hd]
    simp only [det2, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  rw [e]
  positivity

/-- Each curve of a balanced pair is a star-shaped closed curve with period `6 t_f`. -/
lemma oct_isStarCurve {K : Set (Fin 2 → ℝ)} {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {tf : ℝ}
    (hKσ : IsBalancedPair K σ tf) (j : ZMod 6) : PlaneCurve.IsStarCurve (σ j) (6 * tf) where
  pos := by have := hKσ.2.2.2.2.2.2.1; positivity
  contDiff := (hKσ.2.1 j).1
  periodic := hKσ.2.2.2.2.2.2.2.1 j
  injOn := hKσ.2.2.2.2.2.2.2.2.1 j
  cross_pos := oct_det2_deriv_pos hKσ j

/-- A centrally symmetric convex disk contains the origin in its interior. -/
lemma oct_zero_mem_interior {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) :
    (0 : Fin 2 → ℝ) ∈ interior K := by
  obtain ⟨hconv, -, ⟨x, hx⟩, hsymm⟩ := hK
  have hneg : -interior K ⊆ interior K := by
    refine interior_maximal (fun y hy ↦ ?_) (isOpen_interior.neg)
    simpa using hsymm _ (interior_subset (Set.mem_neg.1 hy))
  have hx' : -x ∈ interior K := hneg (by simpa using hx)
  have := hconv.interior hx hx' (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  simpa [smul_neg] using this

/-- A balanced disk is the region swept from the origin by its boundary curve `σ₀` over one
period: every point of `K` is `r σ₀(t)` with `0 ≤ r ≤ 1` (the gauge of `K` rescales a point to
the boundary), and conversely by convexity, since `0 ∈ K`. -/
lemma oct_eq_radialHull {K : Set (Fin 2 → ℝ)} {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {tf : ℝ}
    (hKσ : IsBalancedPair K σ tf) : K = PlaneCurve.radialHull (σ 0) 0 (6 * tf) := by
  have h0 := oct_zero_mem_interior hKσ.1
  obtain ⟨⟨hconv, hcomp, -, -⟩, -, -, -, -, -, htf, hper, -, himg⟩ := hKσ
  have hK0 : K ∈ nhds (0 : Fin 2 → ℝ) := mem_interior_iff_mem_nhds.1 h0
  apply Subset.antisymm
  · intro y hy
    by_cases hy0 : y = 0
    · exact ⟨0, ⟨le_rfl, by positivity⟩, 0, ⟨le_rfl, zero_le_one⟩, by simp [hy0]⟩
    set c := gauge K y with hc
    have hc0 : 0 < c := (gauge_pos (absorbent_nhds_zero hK0) (hcomp.isVonNBounded (𝕜 := ℝ))).2 hy0
    have hc1 : c ≤ 1 := gauge_le_one_of_mem hy
    have hz : c⁻¹ • y ∈ frontier K := by
      rw [← gauge_eq_one_iff_mem_frontier hconv hK0, gauge_smul_of_nonneg (inv_nonneg.2 hc0.le),
        smul_eq_mul, ← hc, inv_mul_cancel₀ hc0.ne']
    rw [← himg 0] at hz
    obtain ⟨t, ht, hzt⟩ := hz
    refine ⟨t, Ico_subset_Icc_self ht, c, ⟨hc0.le, hc1⟩, ?_⟩
    rw [hzt, smul_smul, mul_inv_cancel₀ hc0.ne', one_smul]
  · rintro y ⟨t, ht, r, hr, rfl⟩
    have hσt : σ 0 t ∈ K := by
      have hmem : ∀ s ∈ Ico 0 (6 * tf), σ 0 s ∈ K := fun s hs ↦
        hcomp.isClosed.frontier_subset (himg 0 ▸ mem_image_of_mem _ hs)
      rcases ht.2.lt_or_eq with h | h
      · exact hmem t ⟨ht.1, h⟩
      · have := hper 0 0
        rw [zero_add] at this
        rw [h, this]
        exact hmem 0 ⟨le_rfl, by positivity⟩
    exact hconv.smul_mem_of_zero_mem (interior_subset h0) hσt hr

/-- For `σ_j = g s_j*` on `[0, t_f]`, the multi-point condition `det(σ₀, σ₁) = √3/2` forces
`det g = 1`. -/
lemma oct_det_eq_one {K : Set (Fin 2 → ℝ)} {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {tf : ℝ}
    (hKσ : IsBalancedPair K σ tf) {g : ℝ → Mat2}
    (hσ : ∀ j, ∀ t ∈ Icc 0 tf, σ j t = g t *ᵥ sixthRoot j) {t : ℝ} (ht : t ∈ Icc 0 tf) :
    (g t).det = 1 := by
  have hd := ((hKσ.2.2.2.1 t) 0).2.2
  simp only [zero_add] at hd
  have hs := (algA_isMultiPoint_sixthRoot 0).2.2
  simp only [zero_add] at hs
  rw [hσ 0 t ht, hσ 1 t ht, oct_det2_mulVec, hs] at hd
  have h3 : (0 : ℝ) < √3 / 2 := by positivity
  nlinarith

/-- `X` is traceless where `g' = gX` and `det g = 1` near `t`: the derivative
`det(g) tr(X)` of `det g` vanishes. -/
lemma oct_trace_eq_zero {g X : ℝ → Mat2} {t : ℝ} {s : Set ℝ} (hs : s ∈ nhds t)
    (hg : HasDerivAtEntrywise g (g t * X t) t) (hdet : ∀ x ∈ s, (g x).det = 1) :
    (X t).trace = 0 := by
  have h1 := hg.det_fin_two
  have h2 : HasDerivAt (fun x ↦ (g x).det) 0 t :=
    (hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq
      (Filter.eventually_of_mem hs fun x hx ↦ hdet x hx)
  have h := h1.unique h2
  have hd := hdet t (mem_of_mem_nhds hs)
  rw [Matrix.det_fin_two] at hd
  rw [Matrix.trace_fin_two]
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h
  linear_combination h - (X t 0 0 + X t 1 1) * hd

/-- `(Bu)ᵀ (AY) (Bu) = uᵀ (Bᵀ A Y B) u`. -/
lemma oct_dotProduct_conj (A Y B : Mat2) (u : Fin 2 → ℝ) :
    (B *ᵥ u) ⬝ᵥ ((A * Y) *ᵥ (B *ᵥ u)) = u ⬝ᵥ ((Bᵀ * A * Y * B) *ᵥ u) := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.mul_apply,
    Matrix.transpose_apply]
  ring

/-- **Equation `eqn:cost`** (§3.2). Let `(K, σ)` be a balanced pair whose curves are
`σ_j(t) = g(t) s_j*` on `[0, t_f]`, with `g' = gX`. Then
`area(K) = -(3/2) ∫₀^{t_f} tr(JX) dt`, the cost of the trajectory.

The book's normalization `σ_j(t + t_f) = σ_{j+1}(t)` (used in its derivation of the terminal
conditions, §3.5: the arcs `σ_j([0, t_f])` follow one another along the boundary) is the hypothesis
`hshift`; without it the formula fails (for the unit disk with `σ_j(t) = Rot(φ(t)) s_j*`, the
area is `π` but the cost is `3(φ(t_f) - φ(0))`). The conditions `det g = 1` and `tr X = 0` of the
book's setting follow from the multi-point condition and need not be assumed.

The proof is the book's: `area(K) = ½ ∫₀^{6t_f} σ₀*θ = ∫₀^{t_f} σ₀*θ + σ₂*θ + σ₄*θ` (the six arcs
`σ₀(t + j t_f) = σ_j(t)`, and `σ_{j+3} = -σ_j` has the same pullback as `σ_j`), then
Lemma 3.2.1 and Lemma 3.2.2 with `u = s₀*`, `s₂* = R² s₀*`, `s₄* = R⁴ s₀*` and `|s₀*| = 1`.

Departure from the paper: the first step, `area(K) = ½ ∮_{∂K} θ`, is Green's theorem in the book;
Mathlib has no Green's theorem for such regions, so we use the polar-coordinates formula
`PlaneCurve.IsStarCurve.volume_radialHull` (Green's formula for regions star-shaped about the
origin), applied to `K = radialHull σ₀` (`oct_eq_radialHull`). -/
theorem eqn_cost {K : Set (Fin 2 → ℝ)} {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {tf : ℝ}
    (hKσ : IsBalancedPair K σ tf) (g X : ℝ → Mat2)
    (hσ : ∀ j, ∀ t ∈ Icc 0 tf, σ j t = g t *ᵥ sixthRoot j)
    (hg : ∀ t ∈ Ioo 0 tf, HasDerivAtEntrywise g (g t * X t) t)
    (hshift : ∀ j t, σ j (t + tf) = σ (j + 1) t) :
    volume K = ENNReal.ofReal (reinhardtCost tf X) := by
  have hdetI : ∀ t ∈ Icc 0 tf, (g t).det = 1 := fun t ht ↦ oct_det_eq_one hKσ hσ ht
  -- the area is `½ ∫₀^{6t_f} det(σ₀, σ₀')` (Green's formula for star-shaped regions)
  rw [oct_eq_radialHull hKσ, (oct_isStarCurve hKσ 0).volume_radialHull]
  congr 1
  obtain ⟨-, hC1, -, hmp, -, -, htf, -, -, -⟩ := hKσ
  set F : ZMod 6 → ℝ → ℝ := fun j t ↦ det2 (σ j t) (deriv (σ j) t) with hF
  have hFc : ∀ j, Continuous (F j) := fun j ↦ by
    have hc := (hC1 j).1.continuous
    have hd := (hC1 j).1.continuous_deriv le_rfl
    have hc0 := (continuous_apply 0).comp hc
    have hc1 := (continuous_apply 1).comp hc
    have hd0 := (continuous_apply 0).comp hd
    have hd1 := (continuous_apply 1).comp hd
    exact (hc0.mul hd1).sub (hc1.mul hd0)
  -- the six arcs: `σ₀(t + n t_f) = σ_n(t)`
  have hshiftN : ∀ n : ℕ, ∀ t, σ 0 (t + n * tf) = σ (n : ZMod 6) t := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro t
      rw [show t + ((n + 1 : ℕ) : ℝ) * tf = (t + tf) + n * tf by push_cast; ring, ih,
        hshift]
      push_cast
      ring_nf
  have hFN : ∀ n : ℕ, ∀ t, F 0 (t + n * tf) = F (n : ZMod 6) t := by
    intro n t
    simp only [hF]
    rw [hshiftN, ← deriv_comp_add_const]
    congr 2
    funext x
    exact hshiftN n x
  -- `∫₀^{6t_f} det(σ₀, σ₀') = Σ_j ∫₀^{t_f} det(σ_j, σ_j')`
  have hsplit : ∫ t in (0 : ℝ)..6 * tf, F 0 t =
      ∑ n ∈ Finset.range 6, ∫ t in (0 : ℝ)..tf, F (n : ZMod 6) t := by
    have h := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := F 0)
      (a := fun n : ℕ ↦ n * tf) (n := 6) fun k _ ↦ (hFc 0).intervalIntegrable _ _
    simp only [Nat.cast_zero, zero_mul, Nat.cast_ofNat] at h
    rw [← h]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [← intervalIntegral.integral_congr (fun t _ ↦ hFN n t),
      intervalIntegral.integral_comp_add_right]
    congr 1 <;> push_cast <;> ring
  -- `σ_{j+3} = -σ_j` has the same pullback as `σ_j`
  have hF3 : ∀ j, F (j + 3) = F j := by
    intro j
    have h : σ (j + 3) = -σ j := funext fun t ↦ ((hmp t) j).2.1
    funext t
    simp only [hF, h, deriv.neg, Pi.neg_apply, oct_det2_neg]
  have hsum : (1 / 2 : ℝ) * ∑ n ∈ Finset.range 6, ∫ t in (0 : ℝ)..tf, F (n : ZMod 6) t =
      ∫ t in (0 : ℝ)..tf, (F 0 t + F 2 t + F 4 t) := by
    have e3 : F 3 = F 0 := hF3 0
    have e4 : F 4 = F 1 := hF3 1
    have e5 : F 5 = F 2 := hF3 2
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, zero_add]
    have i1 := intervalIntegral.integral_add (μ := volume) (a := 0) (b := tf)
      (f := fun t ↦ F 0 t + F 2 t) (g := F 4) (((hFc 0).add (hFc 2)).intervalIntegrable _ _)
      ((hFc 4).intervalIntegrable _ _)
    have i2 := intervalIntegral.integral_add (μ := volume) (a := 0) (b := tf)
      (f := F 0) (g := F 2) ((hFc 0).intervalIntegrable _ _) ((hFc 2).intervalIntegrable _ _)
    rw [e3, e5, i1, i2, e4]
    ring
  change (1 / 2 : ℝ) * ∫ t in (0 : ℝ)..6 * tf, F 0 t = _
  rw [hsplit, hsum, reinhardtCost, ← intervalIntegral.integral_const_mul]
  -- on `(0, t_f)`: Lemma 3.2.1 for each arc, then Lemma 3.2.2
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [(countable_singleton tf).ae_notMem volume] with t htf' ht
  rw [uIoc_of_le htf.le] at ht
  have hto : t ∈ Ioo 0 tf := ⟨ht.1, lt_of_le_of_ne ht.2 htf'⟩
  have htc : t ∈ Icc 0 tf := Ioo_subset_Icc_self hto
  -- Lemma 3.2.1: `σ_j*θ = -s_jᵀ J X s_j dt`
  have hpb : ∀ j, F j t = -(sixthRoot j ⬝ᵥ ((J * X t) *ᵥ sixthRoot j)) := by
    intro j
    have hl := lemma3_2_1 g X t (hg t hto) (hdetI t htc) (sixthRoot j)
    have hloc : σ j =ᶠ[nhds t] fun s ↦ g s *ᵥ sixthRoot j :=
      Filter.eventually_of_mem (Icc_mem_nhds hto.1 hto.2) (hσ j)
    have hd : deriv (σ j) t = (g t * X t) *ᵥ sixthRoot j := by
      rw [hloc.deriv_eq]; exact hl.1.deriv
    simp only [hF]
    rw [hd, hσ j t htc]
    exact hl.2
  -- `X ∈ 𝔰𝔩₂(ℝ)`, so Lemma 3.2.2 applies
  have htr : (X t).trace = 0 :=
    oct_trace_eq_zero (Ioo_mem_nhds hto.1 hto.2) (hg t hto)
      fun x hx ↦ hdetI x (Ioo_subset_Icc_self hx)
  have hl2 := lemma3_2_2 (X t) htr
  have hs2 : sixthRoot 2 = R ^ 2 *ᵥ sixthRoot 0 := by
    rw [oct_R_pow_mulVec_sixthRoot]; norm_num
  have hs4 : sixthRoot 4 = R ^ 4 *ᵥ sixthRoot 0 := by
    rw [oct_R_pow_mulVec_sixthRoot]; norm_num
  rw [hpb, hpb, hpb, hs2, hs4, oct_dotProduct_conj, oct_dotProduct_conj]
  have hu : sixthRoot 0 ⬝ᵥ sixthRoot 0 = 1 := by
    rw [algA_sixthRoot_zero]; simp [dotProduct, Fin.sum_univ_two]
  calc -(sixthRoot 0 ⬝ᵥ ((J * X t) *ᵥ sixthRoot 0)) +
        -(sixthRoot 0 ⬝ᵥ (((R ^ 2)ᵀ * J * X t * R ^ 2) *ᵥ sixthRoot 0)) +
        -(sixthRoot 0 ⬝ᵥ (((R ^ 4)ᵀ * J * X t * R ^ 4) *ᵥ sixthRoot 0))
      = -(sixthRoot 0 ⬝ᵥ ((J * X t + (R ^ 2)ᵀ * J * X t * R ^ 2 +
          (R ^ 4)ᵀ * J * X t * R ^ 4) *ᵥ sixthRoot 0)) := by
        simp only [Matrix.add_mulVec, dotProduct_add]
        ring
    _ = -(3 / 2) * traceForm J (X t) := by
        rw [hl2, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, hu, smul_eq_mul,
          traceForm]
        ring

end SmoothedPolygons
