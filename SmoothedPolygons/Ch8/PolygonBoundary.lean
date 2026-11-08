module

public import SmoothedPolygons.Ch8.FiniteBangBang
public import SmoothedPolygons.Ch3.HyperbolicArc
public import SmoothedPolygons.Ch3.ControlProblem
public import SmoothedPolygons.Ch2.Reinhardt
import SmoothedPolygons.Ch7.SmoothedPolygonDisk

/-!
# Finite bang-bang trajectories bound smoothed polygons (Remark 8.3.3)

Remark 8.3.3 (unlabelled, TeX 7610–7616; label of this formalization `rem:smoothed-polygon`):
"a trajectory `(g, X)` that is extremal and edge-extremal that does not meet the singular locus
`𝒮_sing` defines a balanced disk `K(g, X) ∈ 𝔎_bal` whose boundary is a smoothed polygon,
consisting of finitely many straight edges and hyperbolic arcs." The remark has no proof. Its
content is Theorem 8.3.2 together with the discussion of §7.2 (TeX 5612–5622, recorded as
Lemma 7.2.1): on an interval of constant control at a vertex `e_{i+1}`, two of the state-dependent
curvatures vanish, so `σ_{2m}` (`m ≠ i`) and their opposites move along straight lines, and by
Lemma 3.1.8 the third pair moves along hyperbolic arcs whose asymptotes are those lines. The same
sentence is the first line of the proof of Theorem 16.3.1: "A bang-bang trajectory with finitely
many switches is a polygon with rounded corners of the sort described by Reinhardt".

Definitions: `IsHyperbolicArc` (the conclusion of Lemma 3.1.8), `IsSmoothedPolygonBoundary` (the
boundary is the union of finitely many straight edges and hyperbolic arcs, each hyperbolic arc
joining two edges and having as asymptotes lines that extend edges of the boundary), and
`IsSmoothedPolygon` (the gloss of Theorem 16.3.1, TeX 12800–12804: in addition, a centrally
symmetric convex disk with no corners).

Reading of "defines a balanced disk `K(g, X)`": the disk attached to `(g, X)` (index entry
"`K(g, X)`, attached to data `(g, X)`") is taken as given, a balanced pair `(K, σ)` with
`σ_j = g s_j*` on `[0, t_f]` and `σ_j(t + t_f) = σ_{j+1}(t)`. Such a disk exists when the
trajectory has winding number one (`exists_isBalancedPair_of_isReinhardtAdmissible`), in
particular for every trajectory cheaper than the octagon (`isWindingOne_of_reinhardtCost_lt`) and
so for the global minimizer; the book does not show that it exists for every extremal (admissible
trajectories without winding number one exist, `exists_isReinhardtAdmissible_not_isWindingOne`).
-/

@[expose] public section

namespace SmoothedPolygons

open Set MeasureTheory Filter Topology Matrix

/-- `γ` traces on `[α, β]` (`α < β`, continuous and injective there) an arc of the hyperbola
`det(d₁, x - p₁) · det(d₂, x - p₂) = c`, `c ≠ 0`, whose asymptotes are the non-parallel lines
`p₁ + ℝ d₁` and `p₂ + ℝ d₂`: the form of the conclusion of Lemma 3.1.8 (`lemma3_1_8`). -/
def IsHyperbolicArc (γ : ℝ → Fin 2 → ℝ) (α β : ℝ) (p₁ d₁ p₂ d₂ : Fin 2 → ℝ) : Prop :=
  α < β ∧ ContinuousOn γ (Icc α β) ∧ InjOn γ (Icc α β) ∧ d₁ ≠ 0 ∧ d₂ ≠ 0 ∧ det2 d₁ d₂ ≠ 0 ∧
    ∃ c : ℝ, c ≠ 0 ∧ ∀ t ∈ Icc α β, det2 d₁ (γ t - p₁) * det2 d₂ (γ t - p₂) = c

/-- **The boundary of a smoothed polygon** (Remark 8.3.3; Theorem 16.3.1 and its gloss, TeX
12789–12804): the boundary of `K` is the union of finitely many straight edges `[a_k, b_k]`
(`a_k ≠ b_k`) and finitely many hyperbolic arcs `γ_l([α_l, β_l])`; each hyperbolic arc has as
asymptotes the lines extending two of the edges ("hyperbolic arcs, whose asymptotes are lines
extending the straight edge segments of the boundary") and begins and ends on edges (the boundary
alternates between edges and hyperbolic arcs: each hyperbolic arc rounds a corner between two
edges). -/
def IsSmoothedPolygonBoundary (K : Set (Fin 2 → ℝ)) : Prop :=
  ∃ (m n : ℕ) (a b : Fin m → Fin 2 → ℝ) (γ : Fin n → ℝ → Fin 2 → ℝ) (α β : Fin n → ℝ),
    (∀ k, a k ≠ b k) ∧
    (∀ l, ∃ k₁ k₂, IsHyperbolicArc (γ l) (α l) (β l) (a k₁) (b k₁ - a k₁) (a k₂) (b k₂ - a k₂)) ∧
    (∀ l, γ l (α l) ∈ ⋃ k, segment ℝ (a k) (b k)) ∧
    (∀ l, γ l (β l) ∈ ⋃ k, segment ℝ (a k) (b k)) ∧
    frontier K = (⋃ k, segment ℝ (a k) (b k)) ∪ ⋃ l, γ l '' Icc (α l) (β l)

/-- **A finite-sided smoothed polygon with rounded hyperbolic arcs at each corner, of the sort
described by Reinhardt and Mahler** (Theorem 16.3.1, TeX 12792–12804: "the minimizer `K_min` has
no corners and the boundary alternates between straight edge segments and hyperbolic arcs, whose
asymptotes are lines extending the straight edge segments of the boundary"): a centrally
symmetric convex disk with a unique support line at every boundary point (no corners,
Lemma 2.2.5's form) whose boundary is that of a smoothed polygon (`IsSmoothedPolygonBoundary`). -/
def IsSmoothedPolygon (K : Set (Fin 2 → ℝ)) : Prop :=
  IsCCSDisk K ∧ (∀ x ∈ frontier K, ∃! ℓ, IsSupportLine K ℓ ∧ x ∈ ℓ) ∧
    IsSmoothedPolygonBoundary K

/-! ### Plane geometry and curves of the plane -/

/-- Vectors parallel to a nonzero vector are parallel to each other: if `det(a, b) = 0` and
`det(a, c) = 0` with `a ≠ 0`, then `det(b, c) = 0`. -/
private lemma l3k_det2_eq_zero_of_parallel {a b c : Fin 2 → ℝ} (ha : a ≠ 0) (hb : det2 a b = 0)
    (hc : det2 a c = 0) : det2 b c = 0 := by
  have h0 : a 0 * det2 b c = b 0 * det2 a c - c 0 * det2 a b := by simp only [det2]; ring
  have h1 : a 1 * det2 b c = b 1 * det2 a c - c 1 * det2 a b := by simp only [det2]; ring
  rw [hb, hc, mul_zero, mul_zero, sub_zero] at h0 h1
  by_contra hbc
  apply ha
  ext k
  fin_cases k
  · simpa [hbc] using h0
  · simpa [hbc] using h1

/-- `|w|² = w₀² + w₁² > 0` for `w ≠ 0`. -/
private lemma l3k_sq_add_sq_pos {w : Fin 2 → ℝ} (hw : w ≠ 0) : 0 < w 0 ^ 2 + w 1 ^ 2 := by
  by_contra h
  rw [not_lt] at h
  apply hw
  have h0 : w 0 ^ 2 = 0 := by nlinarith [sq_nonneg (w 0), sq_nonneg (w 1)]
  have h1 : w 1 ^ 2 = 0 := by nlinarith [sq_nonneg (w 0), sq_nonneg (w 1)]
  ext k
  fin_cases k
  · simpa using h0
  · simpa using h1

/-- A point of the segment `[a, b]` lies on the line through `a` with direction `b - a`. -/
private lemma l3k_det2_of_mem_segment {a b x : Fin 2 → ℝ} (hx : x ∈ segment ℝ a b) :
    det2 (b - a) (x - a) = 0 := by
  obtain ⟨θ₁, θ₂, -, -, hθ, rfl⟩ := hx
  have e : θ₁ • a + θ₂ • b - a = θ₂ • (b - a) := by
    rw [show θ₁ = 1 - θ₂ by linarith]; module
  rw [e, rein_det2_smul_right, rein_det2_self, mul_zero]

/-- `Icc c d` is a right neighbourhood of every point of `Ico c d`. -/
private lemma l3k_Icc_mem_nhdsGE {c d t : ℝ} (ht : t ∈ Ico c d) : Icc c d ∈ 𝓝[≥] t :=
  mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1)

/-- A real function with zero derivative within `[c, d]` at every point of `[c, d]` is constant
there. -/
private lemma l3k_const_of_deriv_zero {f : ℝ → ℝ} {c d : ℝ}
    (hf : ∀ t ∈ Icc c d, HasDerivWithinAt f 0 (Icc c d) t) : ∀ t ∈ Icc c d, f t = f c :=
  constant_of_has_deriv_right_zero (fun t ht ↦ (hf t ht).continuousWithinAt)
    (fun t ht ↦ (hf t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (l3k_Icc_mem_nhdsGE ht))

/-- A nonvanishing curve `w` of the plane with `det(w, w') = 0` on `[c, d]` keeps its direction:
`det(w(c), w(t)) = 0`. Proof: `φ = det(w(c), w)² / |w|²` has derivative
`2 det(w(c), w) ⟨w(c), w⟩ det(w, w') / |w|⁴ = 0`, so `φ(t) = φ(c) = 0`. -/
private lemma l3k_det2_eq_zero_of_det2_deriv {w w' : ℝ → Fin 2 → ℝ} {c d : ℝ}
    (hw : ∀ t ∈ Icc c d, HasDerivWithinAt w (w' t) (Icc c d) t)
    (hne : ∀ t ∈ Icc c d, w t ≠ 0) (hpar : ∀ t ∈ Icc c d, det2 (w t) (w' t) = 0) :
    ∀ t ∈ Icc c d, det2 (w c) (w t) = 0 := by
  intro t ht
  have hφ : ∀ s ∈ Icc c d, HasDerivWithinAt
      (fun s ↦ det2 (w c) (w s) ^ 2 / (w s 0 ^ 2 + w s 1 ^ 2)) 0 (Icc c d) s := by
    intro s hs
    have h0 := hasDerivWithinAt_pi.1 (hw s hs) 0
    have h1 := hasDerivWithinAt_pi.1 (hw s hs) 1
    have hf : HasDerivWithinAt (fun s ↦ det2 (w c) (w s)) (det2 (w c) (w' s)) (Icc c d) s := by
      simp only [det2]
      exact (h1.const_mul (w c 0)).sub (h0.const_mul (w c 1))
    have hN := l3k_sq_add_sq_pos (hne s hs)
    convert (hf.pow 2).div ((h0.pow 2).add (h1.pow 2)) hN.ne' using 1
    have hp := hpar s hs
    simp only [det2, Pi.add_apply, Pi.pow_apply] at hp hN ⊢
    rw [eq_div_iff (by positivity)]
    linear_combination (-2 * (w c 0 * w s 1 - w c 1 * w s 0) *
      (w c 0 * w s 0 + w c 1 * w s 1)) * hp
  have h := l3k_const_of_deriv_zero hφ t ht
  simp only [rein_det2_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    zero_div] at h
  rcases div_eq_zero_iff.1 h with h | h
  · exact pow_eq_zero_iff two_ne_zero |>.1 h
  · exact absurd h (l3k_sq_add_sq_pos (hne t ht)).ne'

/-- A curve `σ` with velocity `w` on `[c, d]`, where `w` is nonvanishing with `det(w, w') = 0`,
lies on the line through `σ(c)` with direction `w(c)`: `det(w(c), σ(t) - σ(c))` has derivative
`det(w(c), w(t)) = 0` (`l3k_det2_eq_zero_of_det2_deriv`). -/
private lemma l3k_line_of_det2_deriv {σ w w' : ℝ → Fin 2 → ℝ} {c d : ℝ}
    (hσ : ∀ t ∈ Icc c d, HasDerivWithinAt σ (w t) (Icc c d) t)
    (hw : ∀ t ∈ Icc c d, HasDerivWithinAt w (w' t) (Icc c d) t)
    (hne : ∀ t ∈ Icc c d, w t ≠ 0) (hpar : ∀ t ∈ Icc c d, det2 (w t) (w' t) = 0) :
    ∀ t ∈ Icc c d, det2 (w c) (σ t - σ c) = 0 := by
  have hdir := l3k_det2_eq_zero_of_det2_deriv hw hne hpar
  have hψ : ∀ s ∈ Icc c d,
      HasDerivWithinAt (fun s ↦ det2 (w c) (σ s - σ c)) 0 (Icc c d) s := by
    intro s hs
    have h0 := hasDerivWithinAt_pi.1 (hσ s hs) 0
    have h1 := hasDerivWithinAt_pi.1 (hσ s hs) 1
    have h := ((h1.sub_const (σ c 1)).const_mul (w c 0)).sub
      ((h0.sub_const (σ c 0)).const_mul (w c 1))
    have hd := hdir s hs
    simp only [det2] at hd
    convert h using 1
    · ext s
      simp only [det2, Pi.sub_apply]
    · linarith
  intro t ht
  rw [l3k_const_of_deriv_zero hψ t ht, sub_self]
  simp [det2]

/-- **Constant control at a vertex: two of the curves move along straight lines** (§7.2, TeX
5612–5622: "two of the state-dependent curvatures `κ_j, κ_{j+1}` are zero. Thus the corresponding
trajectories `σ_i(t) = g(t) s_i*`, `i = 2j, 2j + 2`, move along straight lines"; the discussion that
Lemma 7.2.1 records, whose half-plane part is `lemma7_2_1`). If the control of a state trajectory
is the vertex `e_{i+1}` almost everywhere on `[c, d]`, then for every `m ≠ i` the curve
`σ_{2m} = g s_{2m}*` moves along a straight line on `[c, d]`.

Proof ("by the construction of the control from state-dependent curvatures, two of the
state-dependent curvatures are zero"):
1. On `[c, d]` the control is `e_{i+1}` a.e., so the integrand of `X' = [P, X]` agrees a.e. with
   the continuous `[P_i(X), X]`, `P_i(X) = Z_{e_{i+1}}/⟨Z_{e_{i+1}}, X⟩` (`⟨Z_u, X⟩ < 0`,
   `poly_traceForm_neg`): `X` is `C¹` on `[c, d]`, and so are `σ = g s` (`s = s_{2m}*`) and
   `σ' = gXs`, with `σ'' = g(X² + [P_i(X), X])s`.
2. `det(σ', σ'') = det g · det X · κ_m = κ_m`, and the state-dependent curvature is
   `κ_m = -2 u_m/⟨Z_u, X⟩` (`oct_stateCurvature_eq`), which vanishes for `u = e_{i+1}`, `m ≠ i`.
3. A curve whose velocity `w = σ'` never vanishes and satisfies `det(w, w') = 0` keeps the
   direction of `w(c)`: `det(w(c), w)²/|w|²` has zero derivative (`l3k_det2_eq_zero_of_det2_deriv`);
   so `det(w(c), σ - σ(c))` has zero derivative and `σ` lies on the line through `σ(c)` with
   direction `w(c)` (`l3k_line_of_det2_deriv`). -/
private theorem l3st_straight_of_vertexControl {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsStateTrajectory T u g X) {c d : ℝ} (hc : 0 ≤ c) (hcd : c < d) (hd : d ≤ T)
    {i : Fin 3} (hu : ∀ᵐ t, t ∈ Ioo c d → u t = vertex i) {m : Fin 3} (hm : m ≠ i) :
    ∃ p v : Fin 2 → ℝ, v ≠ 0 ∧
      ∀ t ∈ Icc c d, det2 v (g t *ᵥ sixthRoot (2 * (m.val : ZMod 6)) - p) = 0 := by
  obtain ⟨-, -, -, hst, hgI, hXI⟩ := h
  have hsub : Icc c d ⊆ Icc 0 T := Icc_subset_Icc hc hd
  have hcc : c ∈ Icc c d := ⟨le_rfl, hcd.le⟩
  have hgc : ContinuousOn g (Icc 0 T) := Matrix.continuousOn_of_eq_add_integral hgI
  have hXc : ContinuousOn X (Icc 0 T) := Matrix.continuousOn_of_eq_add_integral hXI
  set s := sixthRoot (2 * (m.val : ZMod 6)) with hs
  set F : Mat2 → Mat2 := fun M ↦ controlP (vertex i) M * M - M * controlP (vertex i) M with hF
  have hZX : ∀ t ∈ Icc 0 T, traceForm (controlMatrix (vertex i)) (X t) ≠ 0 := fun t ht ↦
    (poly_traceForm_neg (poly_vertex_mem i) (hst t ht).2).ne
  have hFc : ∀ M, traceForm (controlMatrix (vertex i)) M ≠ 0 → ContinuousAt F M := by
    intro M hM
    have htr : Continuous (traceForm (controlMatrix (vertex i))) :=
      (continuous_const.matrix_mul continuous_id).matrix_trace
    have hP : ContinuousAt (controlP (vertex i)) M :=
      (htr.continuousAt.inv₀ hM).smul continuousAt_const
    exact (hP.mul continuousAt_id).sub (continuousAt_id.mul hP)
  have hFXc : ContinuousOn (fun t ↦ F (X t)) (Icc c d) := fun t ht ↦
    (hFc _ (hZX t (hsub ht))).comp_continuousWithinAt ((hXc t (hsub ht)).mono hsub)
  -- `X' = [P, X]` with `P = Z_{e_{i+1}}/⟨Z_{e_{i+1}}, X⟩` on `[c, d]`: the integrand of the state
  -- equation agrees a.e. on `(c, d)` with this continuous function
  have hXint : ∀ k l, IntervalIntegrable (fun t ↦ F (X t) k l) volume c d ∧
      ∀ t ∈ Icc c d, X t k l = X c k l + ∫ τ in c..t, F (X τ) k l := by
    intro k l
    refine ⟨(continuousOn_iff_entrywise.1 hFXc k l).intervalIntegrable_of_Icc hcd.le,
      fun t ht ↦ ?_⟩
    obtain ⟨hint, heq⟩ := hXI k l
    have hT : 0 ≤ T := hc.trans (hcd.le.trans hd)
    have hint' : ∀ a b, 0 ≤ a → a ≤ b → b ≤ T → IntervalIntegrable (fun τ ↦
        (controlP (u τ) (X τ) * X τ - X τ * controlP (u τ) (X τ)) k l) volume a b :=
      fun a b ha hab hb ↦ hint.mono_set (by
        rw [uIcc_of_le hab, uIcc_of_le hT]; exact Icc_subset_Icc ha hb)
    rw [heq t (hsub ht), heq c (hsub hcc), ← intervalIntegral.integral_add_adjacent_intervals
      (hint' 0 c le_rfl hc (hcd.le.trans hd)) (hint' c t hc ht.1 (ht.2.trans hd)), add_assoc]
    congr 2
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hu, Measure.ae_ne volume d] with τ hτ hτd hτ'
    rw [uIoc_of_le ht.1] at hτ'
    rw [hτ ⟨hτ'.1, lt_of_le_of_ne (hτ'.2.trans ht.2) hτd⟩]
  have hXd : ∀ t ∈ Icc c d, HasDerivWithinAtEntrywise X (F (X t)) (Icc c d) t := fun t ht ↦
    Matrix.hasDerivWithinAtEntrywise_of_eq_add_integral (v := fun τ ↦ F (X τ)) hXint ht
      (hFXc t ht)
  have hgd : ∀ t ∈ Icc c d, HasDerivWithinAtEntrywise g (g t * X t) (Icc c d) t := fun t ht ↦
    (Matrix.hasDerivWithinAtEntrywise_of_eq_add_integral hgI (hsub ht)
      ((hgc.mul hXc) t (hsub ht))).mono hsub
  -- `σ = g s`, `σ' = g X s`, `σ'' = g (X² + X') s`
  have hσ : ∀ t ∈ Icc c d, HasDerivWithinAt (fun t ↦ g t *ᵥ s) ((g t * X t) *ᵥ s)
      (Icc c d) t := fun t ht ↦ (hgd t ht).mulVec_const s
  have hw : ∀ t ∈ Icc c d, HasDerivWithinAt (fun t ↦ (g t * X t) *ᵥ s)
      ((g t * X t * X t + g t * F (X t)) *ᵥ s) (Icc c d) t :=
    fun t ht ↦ ((hgd t ht).mul (hXd t ht)).mulVec_const s
  have hne : ∀ t ∈ Icc c d, (g t * X t) *ᵥ s ≠ 0 := by
    intro t ht h0
    have hdet : (g t * X t).det ≠ 0 := by
      rw [Matrix.det_mul, (hst t (hsub ht)).1, (hst t (hsub ht)).2.2.1]; norm_num
    exact oct_sixthRoot_ne_zero _ (Matrix.eq_zero_of_mulVec_eq_zero hdet h0)
  -- `det(σ', σ'') = det(g) det(X) κ_m = κ_m = -2 u_m/⟨Z_u, X⟩ = 0` (`oct_stateCurvature_eq`)
  have hpar : ∀ t ∈ Icc c d,
      det2 ((g t * X t) *ᵥ s) ((g t * X t * X t + g t * F (X t)) *ᵥ s) = 0 := by
    intro t ht
    obtain ⟨hdg, hX⟩ := hst t (hsub ht)
    have hdetX : (X t).det ≠ 0 := by rw [hX.2.1]; norm_num
    have hmul : g t * X t * X t + g t * F (X t) =
        g t * (X t * (X t + (X t)⁻¹ * F (X t))) := by
      rw [Matrix.mul_add (X t), ← Matrix.mul_assoc (X t) (X t)⁻¹,
        Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdetX), Matrix.one_mul, Matrix.mul_add,
        Matrix.mul_assoc]
    rw [hmul, ← Matrix.mulVec_mulVec s (g t) (X t),
      ← Matrix.mulVec_mulVec s (g t) (X t * (X t + (X t)⁻¹ * F (X t))), oct_det2_mulVec, hdg,
      one_mul, ← Matrix.mulVec_mulVec s (X t), oct_det2_mulVec, hX.2.1, one_mul]
    have hκ := oct_stateCurvature_eq hX (vertex i) (hZX t (hsub ht)) m
    rw [stateCurvature] at hκ
    rw [hκ]
    simp [vertex, hm]
  have hline := l3k_line_of_det2_deriv hσ hw hne hpar
  exact ⟨g c *ᵥ s, (g c * X c) *ᵥ s, hne c hcc, hline⟩

/-! ### Lines through a switching time -/

/-- If `γ` has velocity `v` at `t ∈ [a, b]` (`a < b`) and moves on the line through `p` with
direction `d` during `[a, b]`, then `v` is parallel to `d`. -/
private lemma l3k_det2_vel_eq_zero {γ : ℝ → Fin 2 → ℝ} {v d p : Fin 2 → ℝ} {a b t : ℝ}
    (hab : a < b) (ht : t ∈ Icc a b) (hγ : HasDerivAt γ v t)
    (h : ∀ s ∈ Icc a b, det2 d (γ s - p) = 0) : det2 d v = 0 := by
  have h0 := hasDerivAt_pi.1 hγ 0
  have h1 := hasDerivAt_pi.1 hγ 1
  have hf : HasDerivWithinAt (fun s ↦ det2 d (γ s - p)) (det2 d v) (Icc a b) t := by
    have := (((h1.sub_const (p 1)).const_mul (d 0)).sub
      ((h0.sub_const (p 0)).const_mul (d 1))).hasDerivWithinAt (s := Icc a b)
    convert this using 1
    · ext s
      simp only [det2, Pi.sub_apply]
    · simp only [det2]
  have hz : HasDerivWithinAt (fun s ↦ det2 d (γ s - p)) 0 (Icc a b) t :=
    (hasDerivWithinAt_const t _ 0).congr (fun s hs ↦ h s hs) (h t ht)
  exact (uniqueDiffOn_Icc hab t ht).eq_deriv _ hf hz

/-- **A line continues through a switching time.** A curve with nonzero velocity at `t₀` that
moves on a line `L` during `[c₁, t₀]` and on a line `L'` during `[t₀, d₂]` has `L' = L`: both
lines contain `γ(t₀)` and are parallel to `γ'(t₀)`. So `γ` moves on `L` during `[t₀, d₂]`. -/
private lemma l3k_line_continue {γ : ℝ → Fin 2 → ℝ} {c₁ t₀ d₂ : ℝ} (hc₁ : c₁ < t₀)
    (hd₂ : t₀ < d₂) {v : Fin 2 → ℝ} (hγ : HasDerivAt γ v t₀) (hv : v ≠ 0)
    {p d p' d' : Fin 2 → ℝ} (hd' : d' ≠ 0) (h1 : ∀ t ∈ Icc c₁ t₀, det2 d (γ t - p) = 0)
    (h2 : ∀ t ∈ Icc t₀ d₂, det2 d' (γ t - p') = 0) :
    ∀ t ∈ Icc t₀ d₂, det2 d (γ t - p) = 0 := by
  have hdv := l3k_det2_vel_eq_zero hc₁ ⟨hc₁.le, le_rfl⟩ hγ h1
  have hd'v := l3k_det2_vel_eq_zero hd₂ ⟨le_rfl, hd₂.le⟩ hγ h2
  intro t ht
  have e1 : det2 d' (γ t - γ t₀) = 0 := by
    have := h2 t ht
    have h0 := h2 t₀ ⟨le_rfl, hd₂.le⟩
    rw [show γ t - γ t₀ = (γ t - p') - (γ t₀ - p') by abel, rein_det2_sub_right, this, h0,
      sub_zero]
  have e2 : det2 v (γ t - γ t₀) = 0 := l3k_det2_eq_zero_of_parallel hd' hd'v e1
  have e3 : det2 d (γ t - γ t₀) = 0 :=
    l3k_det2_eq_zero_of_parallel hv (by rw [rein_det2_swap, hdv, neg_zero]) e2
  rw [show γ t - p = (γ t - γ t₀) + (γ t₀ - p) by abel, rein_det2_add_right, e3,
    h1 t₀ ⟨hc₁.le, le_rfl⟩, add_zero]

/-- The image of `[α, β]` (`α < β`) under a continuous injective curve moving on a line is a
segment with distinct endpoints: its coordinate along the line is continuous and injective, so
it maps `[α, β]` onto a nondegenerate interval. -/
private lemma l3k_image_eq_segment {γ : ℝ → Fin 2 → ℝ} {α β : ℝ} (hαβ : α < β)
    (hc : ContinuousOn γ (Icc α β)) (hinj : InjOn γ (Icc α β)) {p w : Fin 2 → ℝ} (hw : w ≠ 0)
    (hline : ∀ t ∈ Icc α β, det2 w (γ t - p) = 0) :
    ∃ a b : Fin 2 → ℝ, a ≠ b ∧ γ '' Icc α β = segment ℝ a b := by
  have hN := l3k_sq_add_sq_pos hw
  set φ : ℝ → ℝ := fun t ↦ (w 0 * (γ t - p) 0 + w 1 * (γ t - p) 1) / (w 0 ^ 2 + w 1 ^ 2)
  have hγφ : ∀ t ∈ Icc α β, γ t = p + φ t • w := by
    intro t ht
    have hl := hline t ht
    simp only [det2, Pi.sub_apply] at hl
    ext k
    fin_cases k
    · simp only [φ, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Fin.zero_eta,
        Fin.isValue]
      field_simp
      linear_combination (-w 1) * hl
    · simp only [φ, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Fin.mk_one,
        Fin.isValue]
      field_simp
      linear_combination (w 0) * hl
  have hφc : ContinuousOn φ (Icc α β) := by
    refine ContinuousOn.div_const ?_ _
    have hk : ∀ k, ContinuousOn (fun t ↦ (γ t - p) k) (Icc α β) := fun k ↦
      (continuousOn_pi.1 (hc.sub continuousOn_const)) k
    exact ((hk 0).const_smul (w 0)).add ((hk 1).const_smul (w 1))
  have himg := hφc.image_Icc hαβ.le
  set mn := sInf (φ '' Icc α β)
  set mx := sSup (φ '' Icc α β)
  have hαI : α ∈ Icc α β := ⟨le_rfl, hαβ.le⟩
  have hβI : β ∈ Icc α β := ⟨hαβ.le, le_rfl⟩
  have hφne : φ α ≠ φ β := by
    intro he
    have : γ α = γ β := by rw [hγφ α hαI, hγφ β hβI, he]
    exact hαβ.ne (hinj hαI hβI this)
  have hα' : φ α ∈ Icc mn mx := himg ▸ mem_image_of_mem φ hαI
  have hβ' : φ β ∈ Icc mn mx := himg ▸ mem_image_of_mem φ hβI
  have hlt : mn < mx := by
    rcases lt_or_gt_of_ne hφne with h | h
    · exact lt_of_le_of_lt hα'.1 (lt_of_lt_of_le h hβ'.2)
    · exact lt_of_le_of_lt hβ'.1 (lt_of_lt_of_le h hα'.2)
  set f : ℝ →ᵃ[ℝ] (Fin 2 → ℝ) := AffineMap.lineMap p (p + w)
  have hf : ∀ r : ℝ, f r = p + r • w := fun r ↦ by
    simp only [f, AffineMap.lineMap_apply, vsub_eq_sub, add_sub_cancel_left, vadd_eq_add]
    abel
  refine ⟨f mn, f mx, fun he ↦ ?_, ?_⟩
  · rw [hf, hf, add_right_inj] at he
    exact hlt.ne (smul_left_injective ℝ hw he)
  · rw [← image_segment, segment_eq_Icc hlt.le, ← himg, image_image]
    exact image_congr fun t ht ↦ by rw [hf, hγφ t ht]

/-! ### The switching intervals of a finite bang-bang control -/

/-- `u` is almost everywhere the vertex `e_{i+1}` near `t`. -/
private def l3k_LocVertex (u : ℝ → Fin 3 → ℝ) (i : Fin 3) (t : ℝ) : Prop :=
  ∃ ε > 0, ∀ᵐ τ, τ ∈ Ioo (t - ε) (t + ε) → u τ = vertex i

/-- **The switching intervals of a finite bang-bang control.** If `u` is bang-bang with finitely
many switches on `[0, T]`, there are times `0 = τ₀ < τ₁ < ⋯ < τ_N = T` (`τ` monotone, constant
after `N`) and vertices `e_{v_l + 1}` with `u = e_{v_l + 1}` almost everywhere on `(τ_l, τ_{l+1})`
and `v_l ≠ v_{l+1}`: the `τ_l`, `0 < l < N`, are the times near which `u` is not almost
everywhere one vertex. -/
private lemma l3k_partition {T : ℝ} (hT : 0 < T) {u : ℝ → Fin 3 → ℝ}
    (hbb : IsFiniteBangBang 0 T u) :
    ∃ (N : ℕ) (τ : ℕ → ℝ) (v : ℕ → Fin 3), 0 < N ∧ τ 0 = 0 ∧ τ N = T ∧ Monotone τ ∧
      (∀ l < N, τ l < τ (l + 1)) ∧
      (∀ l < N, ∀ᵐ t, t ∈ Ioo (τ l) (τ (l + 1)) → u t = vertex (v l)) ∧
      (∀ l, l + 1 < N → v l ≠ v (l + 1)) := by
  classical
  obtain ⟨S, hS⟩ := hbb
  set S' := S.filter (fun t ↦ t ∈ Ioo 0 T ∧ ¬ ∃ i, l3k_LocVertex u i t) with hS'
  set P : Finset ℝ := insert 0 (insert T S') with hP
  have hPsub : ∀ p ∈ P, p ∈ Icc 0 T := by
    intro p hp
    simp only [hP, Finset.mem_insert, hS', Finset.mem_filter] at hp
    rcases hp with rfl | rfl | ⟨-, hp, -⟩
    · exact ⟨le_rfl, hT.le⟩
    · exact ⟨hT.le, le_rfl⟩
    · exact Ioo_subset_Icc_self hp
  have h0P : (0 : ℝ) ∈ P := Finset.mem_insert_self _ _
  have hTP : T ∈ P := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  obtain ⟨n, hn⟩ : ∃ n, P.card = n := ⟨_, rfl⟩
  have hn2 : 2 ≤ n := by
    have hsub : ({0, T} : Finset ℝ) ⊆ P := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      exacts [h0P, hTP]
    have h2 := Finset.card_le_card hsub
    rwa [Finset.card_pair hT.ne, hn] at h2
  set e := P.orderEmbOfFin hn with he
  set τ : ℕ → ℝ := fun l ↦ if h : l < n then e ⟨l, h⟩ else T with hτ
  have hτe : ∀ l (h : l < n), τ l = e ⟨l, h⟩ := fun l h ↦ by simp only [hτ, h, ↓reduceDIte]
  have hτ0 : τ 0 = 0 := by
    rw [hτe 0 (by omega), he, Finset.orderEmbOfFin_zero hn (by omega)]
    exact le_antisymm (Finset.min'_le P 0 h0P) (Finset.le_min' _ _ _ fun y hy ↦ (hPsub y hy).1)
  have hτN : τ (n - 1) = T := by
    rw [hτe (n - 1) (by omega), he, Finset.orderEmbOfFin_last hn (by omega)]
    exact le_antisymm (Finset.max'_le _ _ _ fun y hy ↦ (hPsub y hy).2) (Finset.le_max' P T hTP)
  have hτlt : ∀ l, l + 1 < n → τ l < τ (l + 1) := fun l hl ↦ by
    rw [hτe l (by omega), hτe (l + 1) hl]
    exact e.strictMono (Fin.mk_lt_mk.2 (Nat.lt_succ_self l))
  have hτP : ∀ l < n, τ l ∈ P := fun l hl ↦ by
    rw [hτe l hl]; exact Finset.orderEmbOfFin_mem P hn _
  have hmono : Monotone τ := by
    refine monotone_nat_of_le_succ fun l ↦ ?_
    rcases lt_trichotomy (l + 1) n with h | h | h
    · exact (hτlt l h).le
    · have : l = n - 1 := by omega
      rw [this, hτN, hτ]
      simp only [show ¬ n - 1 + 1 < n by omega, ↓reduceDIte, le_refl]
    · simp only [hτ, show ¬ l < n by omega, show ¬ l + 1 < n by omega, ↓reduceDIte, le_refl]
  -- no point of `P` lies strictly between consecutive `τ`
  have hgap : ∀ l, l + 1 < n → ∀ t ∈ Ioo (τ l) (τ (l + 1)), t ∉ P := by
    intro l hl t ht htP
    have : t ∈ Set.range e := by rw [he, Finset.range_orderEmbOfFin]; exact htP
    obtain ⟨k, rfl⟩ := this
    rw [hτe l (by omega), hτe (l + 1) hl] at ht
    have h1 := e.lt_iff_lt.1 ht.1
    have h2 := e.lt_iff_lt.1 ht.2
    rw [Fin.lt_def] at h1 h2
    simp only at h1 h2
    omega
  -- every point strictly between consecutive `τ` is near a single vertex
  have hloc : ∀ l, l + 1 < n → ∀ t ∈ Ioo (τ l) (τ (l + 1)), ∃ i, l3k_LocVertex u i t := by
    intro l hl t ht
    have ht0 : 0 < t := lt_of_le_of_lt (hPsub _ (hτP l (by omega))).1 ht.1
    have htT : t < T := lt_of_lt_of_le ht.2 (hPsub _ (hτP (l + 1) hl)).2
    have hnP := hgap l hl t ht
    by_cases htS : t ∈ S
    · by_contra hno
      apply hnP
      simp only [hP, hS', Finset.mem_insert, Finset.mem_filter]
      exact Or.inr (Or.inr ⟨htS, ⟨ht0, htT⟩, hno⟩)
    · exact hS t ⟨ht0, htT⟩ htS
  have hv : ∀ l, ∃ i : Fin 3, l + 1 < n → ∀ᵐ t, t ∈ Ioo (τ l) (τ (l + 1)) → u t = vertex i := by
    intro l
    by_cases hl : l + 1 < n
    · obtain ⟨i, hi⟩ := exists_ae_eq_vertex_of_locally (hloc l hl)
      exact ⟨i, fun _ ↦ hi⟩
    · exact ⟨0, fun h ↦ absurd h hl⟩
  choose v hv using hv
  refine ⟨n - 1, τ, v, by omega, hτ0, hτN, hmono, fun l hl ↦ hτlt l (by omega),
    fun l hl ↦ hv l (by omega), fun l hl hvv ↦ ?_⟩
  -- at an interior `τ_{l+1}` the vertices on the two sides differ
  have hl' : l + 1 + 1 < n := by omega
  set t₀ := τ (l + 1)
  have ht₀P := hτP (l + 1) (by omega)
  have ht₀0 : 0 < t₀ := hτ0 ▸ (lt_of_lt_of_le (hτlt 0 (by omega)) (hmono (by omega : 1 ≤ l + 1)))
  have ht₀T : t₀ < T := hτN ▸ (lt_of_lt_of_le (hτlt (l + 1) hl') (hmono (by omega)))
  have hnot : ¬ ∃ i, l3k_LocVertex u i t₀ := by
    simp only [hP, hS', Finset.mem_insert, Finset.mem_filter] at ht₀P
    rcases ht₀P with h | h | h
    · exact absurd h ht₀0.ne'
    · exact absurd h ht₀T.ne
    · exact h.2.2
  apply hnot
  refine ⟨v l, min (t₀ - τ l) (τ (l + 1 + 1) - t₀),
    lt_min (by linarith [hτlt l (by omega)]) (by linarith [hτlt (l + 1) hl']), ?_⟩
  filter_upwards [hv l (by omega), hv (l + 1) hl', Measure.ae_ne volume t₀] with s h1 h2 h3 hs
  have hm1 := min_le_left (t₀ - τ l) (τ (l + 1 + 1) - t₀)
  have hm2 := min_le_right (t₀ - τ l) (τ (l + 1 + 1) - t₀)
  rcases lt_or_gt_of_ne h3 with h | h
  · exact h1 ⟨by linarith [hs.1], h⟩
  · rw [hvv]; exact h2 ⟨h, by linarith [hs.2]⟩

/-- Every time of `[τ₀, τ_N]` lies in a switching interval `[τ_l, τ_{l+1}]`, `l < N`. -/
private lemma l3k_exists_interval {N : ℕ} {τ : ℕ → ℝ} (hN : 0 < N) (hmono : Monotone τ)
    {t : ℝ} (h0 : τ 0 ≤ t) (hN' : t ≤ τ N) : ∃ l < N, t ∈ Icc (τ l) (τ (l + 1)) := by
  classical
  have hex : ∃ k, t ≤ τ k := ⟨N, hN'⟩
  have hkN : Nat.find hex ≤ N := Nat.find_min' hex hN'
  have hspec := Nat.find_spec hex
  rcases hk : Nat.find hex with _ | l
  · rw [hk] at hspec
    exact ⟨0, hN, h0, hspec.trans (hmono (Nat.zero_le 1))⟩
  · rw [hk] at hspec hkN
    have hmin := Nat.find_min hex (show l < Nat.find hex by omega)
    exact ⟨l, by omega, (not_le.1 hmin).le, hspec⟩

/-! ### Packaging -/

/-- The boundary of `K` is that of a smoothed polygon as soon as it is the union of a finite set
`E` of nondegenerate segments and a finite set `H` of hyperbolic arcs whose asymptotes extend
segments of `E` and whose endpoints lie on segments of `E`. -/
private lemma l3k_isSmoothedPolygonBoundary_of_finite {K : Set (Fin 2 → ℝ)}
    {E : Set ((Fin 2 → ℝ) × (Fin 2 → ℝ))} {H : Set ((ℝ → Fin 2 → ℝ) × ℝ × ℝ)}
    (hE : E.Finite) (hH : H.Finite) (hne : ∀ e ∈ E, e.1 ≠ e.2)
    (hhyp : ∀ h ∈ H, ∃ e₁ ∈ E, ∃ e₂ ∈ E,
      IsHyperbolicArc h.1 h.2.1 h.2.2 e₁.1 (e₁.2 - e₁.1) e₂.1 (e₂.2 - e₂.1))
    (hstart : ∀ h ∈ H, ∃ e ∈ E, h.1 h.2.1 ∈ segment ℝ e.1 e.2)
    (hend : ∀ h ∈ H, ∃ e ∈ E, h.1 h.2.2 ∈ segment ℝ e.1 e.2)
    (hfr : frontier K = (⋃ e ∈ E, segment ℝ e.1 e.2) ∪ ⋃ h ∈ H, h.1 '' Icc h.2.1 h.2.2) :
    IsSmoothedPolygonBoundary K := by
  have := hE.to_subtype
  have := hH.to_subtype
  obtain ⟨m, ⟨fE⟩⟩ := Finite.exists_equiv_fin E
  obtain ⟨n, ⟨fH⟩⟩ := Finite.exists_equiv_fin H
  have hmemE : ∀ e ∈ E, segment ℝ e.1 e.2 ⊆ ⋃ k, segment ℝ (fE.symm k).1.1 (fE.symm k).1.2 :=
    fun e he x hx ↦ mem_iUnion.2 ⟨fE ⟨e, he⟩, by simpa using hx⟩
  refine ⟨m, n, fun k ↦ (fE.symm k).1.1, fun k ↦ (fE.symm k).1.2, fun l ↦ (fH.symm l).1.1,
    fun l ↦ (fH.symm l).1.2.1, fun l ↦ (fH.symm l).1.2.2, fun k ↦ hne _ (fE.symm k).2,
    fun l ↦ ?_, fun l ↦ ?_, fun l ↦ ?_, ?_⟩
  · obtain ⟨e₁, he₁, e₂, he₂, h⟩ := hhyp _ (fH.symm l).2
    exact ⟨fE ⟨e₁, he₁⟩, fE ⟨e₂, he₂⟩, by simpa using h⟩
  · obtain ⟨e, he, hx⟩ := hstart _ (fH.symm l).2
    exact hmemE e he hx
  · obtain ⟨e, he, hx⟩ := hend _ (fH.symm l).2
    exact hmemE e he hx
  · rw [hfr]
    congr 1
    · ext x
      simp only [mem_iUnion]
      constructor
      · rintro ⟨e, he, hx⟩
        exact ⟨fE ⟨e, he⟩, by simpa using hx⟩
      · rintro ⟨k, hx⟩
        exact ⟨_, (fE.symm k).2, hx⟩
    · ext x
      simp only [mem_iUnion]
      constructor
      · rintro ⟨h, hh, hx⟩
        exact ⟨fH ⟨h, hh⟩, by simpa using hx⟩
      · rintro ⟨l, hx⟩
        exact ⟨_, (fH.symm l).2, hx⟩

/-! ### Which curves are straight under a vertex control -/

/-- Under the control `e_{i+1}` the curves `σ_{2i}` and `σ_{2i+3}` move along hyperbolic arcs;
the four others along straight lines. -/
private def l3k_IsHyp (i : Fin 3) (j : ZMod 6) : Prop :=
  j = 2 * ((i : ℕ) : ZMod 6) ∨ j = 2 * ((i : ℕ) : ZMod 6) + 3

private lemma l3k_straight_idx (i : Fin 3) (j : ZMod 6) (h : ¬ l3k_IsHyp i j) :
    ∃ m : Fin 3, m ≠ i ∧ (j = 2 * ((m : ℕ) : ZMod 6) ∨ j = 2 * ((m : ℕ) : ZMod 6) + 3) := by
  unfold l3k_IsHyp at h
  revert i j
  decide

private lemma l3k_hyp_neighbours (i : Fin 3) (j : ZMod 6) (h : l3k_IsHyp i j) :
    ¬ l3k_IsHyp i (j - 1) ∧ ¬ l3k_IsHyp i (j + 1) := by
  unfold l3k_IsHyp at h ⊢
  revert i j
  decide

private lemma l3k_hyp_unique (i i' : Fin 3) (j : ZMod 6) (h : l3k_IsHyp i j)
    (h' : l3k_IsHyp i' j) : i = i' := by
  unfold l3k_IsHyp at h h'
  revert i i' j
  decide

/-- **A bang-bang trajectory with finitely many switches bounds a smoothed polygon** (the content
of Remark 8.3.3 and the first sentence of the proof of Theorem 16.3.1, TeX 12808–12810). Let
`(g, X)` be an admissible trajectory of Problem 3.6.2 whose control is bang-bang with finitely many
switches on `[0, t_f]`, and `(K, σ)` the balanced pair attached to it (`σ_j = g s_j*` on
`[0, t_f]`, `σ_j(t + t_f) = σ_{j+1}(t)`). Then the boundary of `K` is that of a smoothed polygon.

Proof (the remark and the sentence of 16.3.1 have none; this is the discussion of §7.2 with
Lemma 3.1.8, made precise):
1. `∂K = ⋃_j σ_j([0, t_f])` (`IsBalancedPair`: `σ₀([0, 6t_f)) = ∂K`, and the shift
   `σ₀(t + k t_f) = σ_k(t)`).
2. The switching intervals (`l3k_partition`): times `0 = τ₀ < ⋯ < τ_N = t_f` with the control a.e.
   one vertex `e_{v_l + 1}` on `(τ_l, τ_{l+1})` and `v_l ≠ v_{l+1}` (the interior `τ_l` are the
   times near which the control is not a.e. one vertex; between two of them it is a.e. one vertex
   because the interval is connected).
3. On `[τ_l, τ_{l+1}]` with control `e_{i+1}`, `σ_{2m}` and `σ_{2m+3} = -σ_{2m}` (`m ≠ i`) move
   along lines (`l3st_straight_of_vertexControl`), so their arcs are segments with distinct ends
   (`l3k_image_eq_segment`: the curve is continuous and injective on the line); `σ_{2i}` and
   `σ_{2i+3}` move along hyperbolic arcs whose asymptotes are the lines of these segments for
   their neighbours `σ_{2i ± 1}`, `σ_{2i+3 ± 1}` (Lemma 3.1.8, `lemma3_1_8`).
4. A curve is hyperbolic under exactly one vertex control (`l3k_hyp_unique`), so at an interior
   switching time a hyperbolic arc of `σ_j` is preceded and followed by an edge of `σ_j`. At
   `t_f ≡ 0` the arc of `σ_j` on `[τ_{N-1}, t_f]` continues as the arc of `σ_{j+1}` on `[0, τ₁]`
   (`σ_j(t + t_f) = σ_{j+1}(t)`). If one of them is straight, it is the edge on which the other
   ends. If both are hyperbolic, they lie on one hyperbola and are merged into the arc of `σ_j` on
   `[τ_{N-1}, t_f + τ₁]`: the neighbouring curves `σ_{j±1}` are straight on both sides of `t_f`, and
   their lines continue through `t_f` (both contain `σ_{j±1}(t_f)` and are parallel to
   `σ_{j±1}'(t_f) ≠ 0`, `l3k_line_continue`), so Lemma 3.1.8 on `[0, τ₁]` applies with the same
   asymptotes, and its constant is the value at `t_f`.
5. Collect the finitely many segments and arcs (`l3k_isSmoothedPolygonBoundary_of_finite`). -/
private theorem l3st_isSmoothedPolygonBoundary_of_isFiniteBangBang {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X : ℝ → Mat2} (h : IsReinhardtAdmissible T u g X) (hbb : IsFiniteBangBang 0 T u)
    {K : Set (Fin 2 → ℝ)} {σ : ZMod 6 → ℝ → Fin 2 → ℝ} (hKσ : IsBalancedPair K σ T)
    (hσ : ∀ j, ∀ t ∈ Icc 0 T, σ j t = g t *ᵥ sixthRoot j)
    (hshift : ∀ j t, σ j (t + T) = σ (j + 1) t) :
    IsSmoothedPolygonBoundary K := by
  obtain ⟨hK, hC1, -, hmp, -, -, hT, -, hinj, himg⟩ := hKσ
  /- 1. The curves, and `∂K = ⋃_j σ_j([0, t_f])`. -/
  have hcont : ∀ j, Continuous (σ j) := fun j ↦ (hC1 j).1.continuous
  have hder : ∀ j t, HasDerivAt (σ j) (deriv (σ j) t) t := fun j t ↦
    ((hC1 j).1.differentiable one_ne_zero t).hasDerivAt
  have hfr6 : ∀ j, ∀ t ∈ Ico 0 (6 * T), σ j t ∈ frontier K := fun j t ht ↦
    himg j ▸ mem_image_of_mem _ ht
  have hbd : ∀ j, ∀ t ∈ Icc 0 T, σ j t ∈ frontier K := fun j t ht ↦
    hfr6 j t ⟨ht.1, by linarith [ht.2]⟩
  have hinj2 : ∀ j {α β : ℝ}, 0 ≤ α → β ≤ 2 * T → InjOn (σ j) (Icc α β) := by
    intro j α β hα hβ
    refine (hinj j).mono fun t ht ↦ ?_
    exact ⟨hα.trans ht.1, by linarith [ht.2]⟩
  have hshiftN : ∀ (k : ℕ) j t, σ j (t + k * T) = σ (j + k) t := by
    intro k
    induction k with
    | zero => intro j t; simp
    | succ k ih =>
      intro j t
      rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc, hshift, ih]
      congr 1
      push_cast
      ring
  have hcover : (⋃ j, σ j '' Icc 0 T) = frontier K := by
    refine subset_antisymm (iUnion_subset fun j ↦ image_subset_iff.2 fun t ht ↦ hbd j t ht) ?_
    intro x hx
    rw [← himg 0] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    have h1 : (⌊t / T⌋₊ : ℝ) * T ≤ t := (le_div_iff₀ hT).1 (Nat.floor_le (div_nonneg ht.1 hT.le))
    have h2 : t < (⌊t / T⌋₊ + 1) * T := (div_lt_iff₀ hT).1 (Nat.lt_floor_add_one _)
    refine mem_iUnion.2 ⟨(⌊t / T⌋₊ : ZMod 6), t - ⌊t / T⌋₊ * T, ⟨by linarith, by linarith⟩, ?_⟩
    have e := hshiftN ⌊t / T⌋₊ 0 (t - ⌊t / T⌋₊ * T)
    rw [zero_add, sub_add_cancel] at e
    exact e.symm
  have hmc : IsMultiCurve 1 σ T := ⟨fun j ↦ (hC1 j).1.contDiffOn, fun t _ ↦ hmp t⟩
  have hreg : ∀ j, ∀ t ∈ Icc 0 T, derivWithin (σ j) (Icc 0 T) t ≠ 0 := fun j t ht ↦ by
    rw [(hder j t).differentiableAt.derivWithin (uniqueDiffOn_Icc hT t ht)]
    exact (hC1 j).2 t
  /- 2. The switching intervals `[τ_l, τ_{l+1}]`, with the vertex `e_{v_l + 1}`. -/
  obtain ⟨N, τ, v, hN, hτ0, hτN, hmono, hlt, hae, hsw⟩ := l3k_partition hT hbb
  have hτI : ∀ l ≤ N, τ l ∈ Icc 0 T := fun l hl ↦
    ⟨hτ0 ▸ hmono (Nat.zero_le l), hτN ▸ hmono hl⟩
  have hIsub : ∀ l < N, Icc (τ l) (τ (l + 1)) ⊆ Icc 0 T := fun l hl ↦
    Icc_subset_Icc (hτI l hl.le).1 (hτI (l + 1) hl).2
  -- a curve is hyperbolic on at most one of two consecutive intervals
  have hnext : ∀ l, l + 1 < N → ∀ j, l3k_IsHyp (v l) j → ¬ l3k_IsHyp (v (l + 1)) j :=
    fun l hl j h h' ↦ hsw l hl (l3k_hyp_unique _ _ _ h h')
  have hprev : ∀ l, l + 1 < N → ∀ j, l3k_IsHyp (v (l + 1)) j → ¬ l3k_IsHyp (v l) j :=
    fun l hl j h h' ↦ hsw l hl (l3k_hyp_unique _ _ _ h' h)
  /- 3. Straight pieces: under the control `e_{i+1}`, `σ_{2m}` and `σ_{2m+3} = -σ_{2m}` (`m ≠ i`)
  move along lines (§7.2), so their arcs are segments. -/
  have hline : ∀ l < N, ∀ j, ¬ l3k_IsHyp (v l) j → ∃ p w : Fin 2 → ℝ, w ≠ 0 ∧
      ∀ t ∈ Icc (τ l) (τ (l + 1)), det2 w (σ j t - p) = 0 := by
    intro l hl j hj
    obtain ⟨m, hm, hjm⟩ := l3k_straight_idx _ _ hj
    obtain ⟨p, w, hw, hpw⟩ := l3st_straight_of_vertexControl h.1 (hτI l hl.le).1 (hlt l hl)
      (hτI (l + 1) hl).2 (hae l hl) hm
    rcases hjm with rfl | rfl
    · exact ⟨p, w, hw, fun t ht ↦ by rw [hσ _ t (hIsub l hl ht)]; exact hpw t ht⟩
    · refine ⟨-p, w, hw, fun t ht ↦ ?_⟩
      have h3 := ((hmp t) (2 * ((m : ℕ) : ZMod 6))).2.1
      simp only at h3
      rw [h3, hσ _ t (hIsub l hl ht), show ∀ x y : Fin 2 → ℝ, -x - -y = -(x - y) from
        fun x y ↦ by abel, rein_det2_neg_right, hpw t ht, neg_zero]
  have hseg : ∀ l j, ∃ a b : Fin 2 → ℝ, l < N → ¬ l3k_IsHyp (v l) j →
      a ≠ b ∧ σ j '' Icc (τ l) (τ (l + 1)) = segment ℝ a b := by
    intro l j
    by_cases hl : l < N
    · by_cases hj : l3k_IsHyp (v l) j
      · exact ⟨0, 0, fun _ h ↦ absurd hj h⟩
      · obtain ⟨p, w, hw, hpw⟩ := hline l hl j hj
        obtain ⟨a, b, hab, himg⟩ := l3k_image_eq_segment (hlt l hl) (hcont j).continuousOn
          (hinj2 j (hτI l hl.le).1 (by linarith [(hτI (l + 1) hl).2])) hw hpw
        exact ⟨a, b, fun _ _ ↦ ⟨hab, himg⟩⟩
    · exact ⟨0, 0, fun h ↦ absurd h hl⟩
  choose a b hab using hseg
  set E : Set ((Fin 2 → ℝ) × (Fin 2 → ℝ)) :=
    {e | ∃ l < N, ∃ j, ¬ l3k_IsHyp (v l) j ∧ e = (a l j, b l j)} with hE
  have hEmem : ∀ l < N, ∀ j, ¬ l3k_IsHyp (v l) j → ∀ t ∈ Icc (τ l) (τ (l + 1)),
      ∃ e ∈ E, σ j t ∈ segment ℝ e.1 e.2 := fun l hl j hj t ht ↦
    ⟨(a l j, b l j), ⟨l, hl, j, hj, rfl⟩, (hab l j hl hj).2 ▸ mem_image_of_mem _ ht⟩
  have hEdet : ∀ l < N, ∀ j, ¬ l3k_IsHyp (v l) j → ∀ t ∈ Icc (τ l) (τ (l + 1)),
      det2 (b l j - a l j) (σ j t - a l j) = 0 := fun l hl j hj t ht ↦
    l3k_det2_of_mem_segment ((hab l j hl hj).2 ▸ mem_image_of_mem _ ht)
  have hEne : ∀ l < N, ∀ j, ¬ l3k_IsHyp (v l) j → b l j - a l j ≠ 0 := fun l hl j hj ↦
    sub_ne_zero.2 (hab l j hl hj).1.symm
  /- 4. Hyperbolic pieces: `σ_{2i}` and `σ_{2i+3}` move along hyperbolic arcs with asymptotes the
  lines of their neighbours (Lemma 3.1.8). -/
  have hhypc : ∀ l < N, ∀ j, l3k_IsHyp (v l) j →
      det2 (b l (j - 1) - a l (j - 1)) (b l (j + 1) - a l (j + 1)) ≠ 0 ∧ ∃ c : ℝ, c ≠ 0 ∧
        ∀ t ∈ Icc (τ l) (τ (l + 1)), det2 (b l (j - 1) - a l (j - 1)) (σ j t - a l (j - 1)) *
          det2 (b l (j + 1) - a l (j + 1)) (σ j t - a l (j + 1)) = c := by
    intro l hl j hj
    obtain ⟨hm, hp⟩ := l3k_hyp_neighbours _ _ hj
    exact lemma3_1_8 hK hmc hbd hcover hreg j (hlt l hl) (hτI l hl.le).1 (hτI (l + 1) hl).2
      (hEne l hl _ hm) (hEne l hl _ hp) (hEdet l hl _ hm) (hEdet l hl _ hp)
  -- the plain hyperbolic arcs, and the arcs merged across `t_f`
  set Hp : Set ((ℝ → Fin 2 → ℝ) × ℝ × ℝ) := {x | ∃ l < N, ∃ j, l3k_IsHyp (v l) j ∧
      ¬ (l + 1 = N ∧ l3k_IsHyp (v 0) (j + 1)) ∧ ¬ (l = 0 ∧ l3k_IsHyp (v (N - 1)) (j - 1)) ∧
      x = (σ j, τ l, τ (l + 1))} with hHp
  set Hm : Set ((ℝ → Fin 2 → ℝ) × ℝ × ℝ) := {x | ∃ j, l3k_IsHyp (v (N - 1)) j ∧
      l3k_IsHyp (v 0) (j + 1) ∧ x = (σ j, τ (N - 1), T + τ 1)} with hHm
  have hN2 : ∀ j, l3k_IsHyp (v (N - 1)) j → l3k_IsHyp (v 0) (j + 1) → 1 < N := by
    intro j hj1 hj0
    by_contra hN1
    rw [show N - 1 = 0 by omega] at hj1
    exact (l3k_hyp_neighbours _ _ hj1).2 hj0
  have hτ1 : 0 < τ 1 := hτ0 ▸ hlt 0 hN
  have hτNm : τ (N - 1 + 1) = T := by rw [Nat.sub_add_cancel hN]; exact hτN
  have hτLT : τ (N - 1) < T := hτNm ▸ hlt (N - 1) (by omega)
  have hEfin : E.Finite :=
    (Set.finite_range (fun p : Fin N × ZMod 6 ↦ (a p.1 p.2, b p.1 p.2))).subset
      (by rintro _ ⟨l, hl, j, -, rfl⟩; exact ⟨(⟨l, hl⟩, j), rfl⟩)
  have hHpfin : Hp.Finite :=
    (Set.finite_range (fun p : Fin N × ZMod 6 ↦ (σ p.2, τ p.1, τ (p.1 + 1)))).subset
      (by rintro _ ⟨l, hl, j, -, -, -, rfl⟩; exact ⟨(⟨l, hl⟩, j), rfl⟩)
  have hHmfin : Hm.Finite :=
    (Set.finite_range (fun j : ZMod 6 ↦ (σ j, τ (N - 1), T + τ 1))).subset
      (by rintro _ ⟨j, -, -, rfl⟩; exact ⟨j, rfl⟩)
  /- 5. Every hyperbolic arc is one: plain arcs by Lemma 3.1.8; an arc of `σ_j` on
  `[τ_{N-1}, t_f]` followed by a hyperbolic arc of `σ_{j+1}` on `[0, τ₁]` (that is, of `σ_j` on
  `[t_f, t_f + τ₁]`) lies on the same hyperbola: the neighbouring lines continue through `t_f`
  (`l3k_line_continue`) and the constant of the hyperbola is the value at `t_f`. -/
  have hmerged : ∀ j, l3k_IsHyp (v (N - 1)) j → l3k_IsHyp (v 0) (j + 1) →
      IsHyperbolicArc (σ j) (τ (N - 1)) (T + τ 1) (a (N - 1) (j - 1))
        (b (N - 1) (j - 1) - a (N - 1) (j - 1)) (a (N - 1) (j + 1))
        (b (N - 1) (j + 1) - a (N - 1) (j + 1)) := by
    intro j hj1 hj0
    have hL : N - 1 < N := by omega
    obtain ⟨hm, hp⟩ := l3k_hyp_neighbours _ _ hj1
    obtain ⟨hm0, hp0⟩ := l3k_hyp_neighbours _ _ hj0
    rw [add_sub_cancel_right] at hm0
    obtain ⟨hD, c, hc, hcurve⟩ := hhypc (N - 1) hL j hj1
    rw [hτNm] at hcurve
    have hI0 : ∀ s ∈ Icc T (T + τ 1), s - T ∈ Icc (τ 0) (τ (0 + 1)) := fun s hs ↦ by
      rw [hτ0, zero_add]; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    -- the lines of `σ_{j-1}` and `σ_{j+1}` continue through `t_f`
    have hc1 : ∀ s ∈ Icc T (T + τ 1),
        det2 (b (N - 1) (j - 1) - a (N - 1) (j - 1)) (σ (j - 1) s - a (N - 1) (j - 1)) = 0 := by
      refine l3k_line_continue (p' := a 0 j) hτLT (by linarith) (hder (j - 1) T)
        ((hC1 (j - 1)).2 T) (hEne 0 hN j hm0) (fun t ht ↦ hEdet (N - 1) hL _ hm t (hτNm ▸ ht))
        fun s hs ↦ ?_
      have e := hshift (j - 1) (s - T)
      rw [sub_add_cancel, sub_add_cancel] at e
      rw [e]
      exact hEdet 0 hN j hm0 _ (hI0 s hs)
    have hc2 : ∀ s ∈ Icc T (T + τ 1),
        det2 (b (N - 1) (j + 1) - a (N - 1) (j + 1)) (σ (j + 1) s - a (N - 1) (j + 1)) = 0 := by
      refine l3k_line_continue (p' := a 0 (j + 1 + 1)) hτLT (by linarith) (hder (j + 1) T)
        ((hC1 (j + 1)).2 T) (hEne 0 hN _ hp0) (fun t ht ↦ hEdet (N - 1) hL _ hp t (hτNm ▸ ht))
        fun s hs ↦ ?_
      have e := hshift (j + 1) (s - T)
      rw [sub_add_cancel] at e
      rw [e]
      exact hEdet 0 hN _ hp0 _ (hI0 s hs)
    -- Lemma 3.1.8 for `σ_{j+1}` on `[0, τ₁]` with the same asymptotes
    obtain ⟨-, c', -, hcurve'⟩ := lemma3_1_8 hK hmc hbd hcover hreg (j + 1) hτ1 le_rfl
      (hτI 1 hN).2 (hEne (N - 1) hL _ hm) (hEne (N - 1) hL _ hp)
      (fun t ht ↦ by
        have e := hshift (j - 1) t
        rw [sub_add_cancel] at e
        rw [add_sub_cancel_right, ← e]
        exact hc1 _ ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      (fun t ht ↦ by
        rw [← hshift (j + 1) t]
        exact hc2 _ ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    have hcc : c' = c := by
      have e := hshift j 0
      rw [zero_add] at e
      rw [← hcurve' 0 ⟨le_rfl, hτ1.le⟩, ← e]
      exact hcurve T ⟨hτLT.le, le_rfl⟩
    refine ⟨by linarith, (hcont j).continuousOn, hinj2 j (hτI _ (by omega)).1 (by
      linarith [(hτI 1 hN).2]), hEne _ hL _ hm, hEne _ hL _ hp, hD, c, hc, fun t ht ↦ ?_⟩
    by_cases htT : t ≤ T
    · exact hcurve t ⟨ht.1, htT⟩
    · have e := hshift j (t - T)
      rw [sub_add_cancel] at e
      rw [e, ← hcc]
      exact hcurve' _ ⟨by linarith, by linarith [ht.2]⟩
  refine l3k_isSmoothedPolygonBoundary_of_finite hEfin (hHpfin.union hHmfin)
    (by rintro _ ⟨l, hl, j, hj, rfl⟩; exact (hab l j hl hj).1) ?_ ?_ ?_ ?_
  · rintro x (⟨l, hl, j, hj, -, -, rfl⟩ | ⟨j, hj1, hj0, rfl⟩)
    · obtain ⟨hm, hp⟩ := l3k_hyp_neighbours _ _ hj
      obtain ⟨hD, c, hc, hcurve⟩ := hhypc l hl j hj
      exact ⟨_, ⟨l, hl, _, hm, rfl⟩, _, ⟨l, hl, _, hp, rfl⟩, hlt l hl, (hcont j).continuousOn,
        hinj2 j (hτI l hl.le).1 (by linarith [(hτI (l + 1) hl).2]), hEne l hl _ hm,
        hEne l hl _ hp, hD, c, hc, hcurve⟩
    · obtain ⟨hm, hp⟩ := l3k_hyp_neighbours _ _ hj1
      exact ⟨_, ⟨N - 1, by omega, _, hm, rfl⟩, _, ⟨N - 1, by omega, _, hp, rfl⟩,
        hmerged j hj1 hj0⟩
  /- 6. The boundary alternates: each hyperbolic arc begins and ends on an edge (consecutive
  vertices differ, so a curve hyperbolic on one interval is straight on the next). -/
  · rintro x (⟨l, hl, j, hj, hnf, hnb, rfl⟩ | ⟨j, hj1, hj0, rfl⟩)
    · rcases Nat.eq_zero_or_pos l with rfl | hl0
      · have hb : ¬ l3k_IsHyp (v (N - 1)) (j - 1) := fun h' ↦ hnb ⟨rfl, h'⟩
        have e := hshift (j - 1) 0
        rw [zero_add, sub_add_cancel] at e
        change ∃ e ∈ E, σ j (τ 0) ∈ segment ℝ e.1 e.2
        rw [hτ0, ← e]
        exact hEmem (N - 1) (by omega) _ hb T ⟨hτLT.le, hτNm.ge⟩
      · obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
        exact hEmem l' (by omega) j (hprev l' hl j hj) _ ⟨(hlt l' (by omega)).le, le_rfl⟩
    · have hN2' := hN2 j hj1 hj0
      have hprev' := hprev (N - 2) (by omega) j (by rwa [show N - 2 + 1 = N - 1 by omega])
      have := hEmem (N - 2) (by omega) j hprev' (τ (N - 2 + 1))
        ⟨(hlt (N - 2) (by omega)).le, le_rfl⟩
      rwa [show N - 2 + 1 = N - 1 by omega] at this
  · rintro x (⟨l, hl, j, hj, hnf, hnb, rfl⟩ | ⟨j, hj1, hj0, rfl⟩)
    · by_cases hlN : l + 1 = N
      · have hf : ¬ l3k_IsHyp (v 0) (j + 1) := fun h' ↦ hnf ⟨hlN, h'⟩
        have e := hshift j 0
        rw [zero_add] at e
        change ∃ e ∈ E, σ j (τ (l + 1)) ∈ segment ℝ e.1 e.2
        rw [hlN, hτN, e]
        exact hEmem 0 hN _ hf 0 ⟨hτ0.le, by rw [zero_add]; exact hτ1.le⟩
      · exact hEmem (l + 1) (by omega) j (hnext l (by omega) j hj) _
          ⟨le_rfl, (hlt (l + 1) (by omega)).le⟩
    · have hN2' := hN2 j hj1 hj0
      have e := hshift j (τ 1)
      change ∃ e ∈ E, σ j (T + τ 1) ∈ segment ℝ e.1 e.2
      rw [add_comm, e]
      exact hEmem 1 hN2' _ (hnext 0 (by omega) _ hj0) _ ⟨le_rfl, (hlt 1 hN2').le⟩
  /- 7. The edges and arcs cover `∂K`, and lie in it. -/
  · refine subset_antisymm ?_ (union_subset ?_ ?_)
    · rw [← hcover]
      intro x hx
      obtain ⟨j, t, ht, rfl⟩ := by simpa only [mem_iUnion, mem_image] using hx
      obtain ⟨l, hl, htl⟩ := l3k_exists_interval hN hmono (hτ0 ▸ ht.1) (hτN ▸ ht.2)
      by_cases hj : l3k_IsHyp (v l) j
      · refine Or.inr (mem_iUnion₂.2 ?_)
        by_cases hf : l + 1 = N ∧ l3k_IsHyp (v 0) (j + 1)
        · have hlN : l = N - 1 := by omega
          subst hlN
          refine ⟨(σ j, τ (N - 1), T + τ 1), Or.inr ⟨j, hj, hf.2, rfl⟩,
            mem_image_of_mem _ ⟨htl.1, ?_⟩⟩
          linarith [htl.2, hτNm.le]
        · by_cases hb : l = 0 ∧ l3k_IsHyp (v (N - 1)) (j - 1)
          · obtain ⟨rfl, hb⟩ := hb
            have e := hshift (j - 1) t
            rw [sub_add_cancel] at e
            refine ⟨(σ (j - 1), τ (N - 1), T + τ 1),
              Or.inr ⟨j - 1, hb, by rwa [sub_add_cancel], rfl⟩, ⟨t + T, ⟨?_, ?_⟩, e⟩⟩
            · linarith [htl.1, hτLT.le, hτ0.ge]
            · rw [zero_add] at htl; linarith [htl.2]
          · exact ⟨(σ j, τ l, τ (l + 1)), Or.inl ⟨l, hl, j, hj, hf, hb, rfl⟩,
              mem_image_of_mem _ htl⟩
      · obtain ⟨e, he, hx⟩ := hEmem l hl j hj t htl
        exact Or.inl (mem_iUnion₂.2 ⟨e, he, hx⟩)
    · refine iUnion₂_subset ?_
      rintro _ ⟨l, hl, j, hj, rfl⟩
      rw [← (hab l j hl hj).2]
      exact image_subset_iff.2 fun t ht ↦ hbd j t (hIsub l hl ht)
    · refine iUnion₂_subset ?_
      rintro _ (⟨l, hl, j, -, -, -, rfl⟩ | ⟨j, -, -, rfl⟩)
      · exact image_subset_iff.2 fun t ht ↦ hbd j t (hIsub l hl ht)
      · exact image_subset_iff.2 fun t ht ↦ hfr6 j t
          ⟨(hτI (N - 1) (by omega)).1.trans ht.1, by linarith [ht.2, (hτI 1 hN).2]⟩

/-- **Remark 8.3.3** (`rem:smoothed-polygon`, label of this formalization; unlabelled, TeX
7610–7616). A trajectory `(g, X)` that is a Pontryagin extremal and edge extremal and does not meet
the singular locus `𝒮_sing` defines a balanced disk `K(g, X)` whose boundary is a smoothed polygon,
consisting of finitely many straight edges and hyperbolic arcs. The disk `K(g, X)` is a hypothesis
(the balanced pair with `σ_j = g s_j*`; see the module docstring for its existence).

Proof: Theorem 8.3.2 (`theorem8_3_2`, on `[0, t_f]`, with
`IsPontryaginExtremal.isExtremalOn`) makes the control bang-bang with finitely many
switches; then `l3st_isSmoothedPolygonBoundary_of_isFiniteBangBang` (the discussion of §7.2 with
Lemma 3.1.8). -/
theorem remark8_3_3 {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (h : IsPontryaginExtremal T u g X Λ₁ ΛR lam) (hedge : IsEdgeExtremalOn 0 T u X)
    (hS : ∀ t ∈ Icc 0 T, (g t, Λ₁ t, X t, ΛR t) ∉ singularLocus) {K : Set (Fin 2 → ℝ)}
    {σ : ZMod 6 → ℝ → Fin 2 → ℝ} (hKσ : IsBalancedPair K σ T)
    (hσ : ∀ j, ∀ t ∈ Icc 0 T, σ j t = g t *ᵥ sixthRoot j)
    (hshift : ∀ j t, σ j (t + T) = σ (j + 1) t) :
    IsSmoothedPolygonBoundary K := by
  have hT : 0 < T := h.1.1
  exact l3st_isSmoothedPolygonBoundary_of_isFiniteBangBang ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
    (theorem8_3_2 (IsPontryaginExtremal.isExtremalOn h le_rfl hT le_rfl) hedge hS) hKσ hσ
    hshift

/-- Being the boundary of a smoothed polygon is invariant under invertible linear maps: lines go to
lines, segments to segments, and `det(A⁻¹d, A⁻¹(x - p)) = det(A⁻¹) det(d, x - p)`, so hyperbolic
arcs with asymptotes go to hyperbolic arcs with the image asymptotes (constant `c det(A⁻¹)²`); the
frontier of the image is the image of the frontier (a linear homeomorphism). -/
theorem IsSmoothedPolygonBoundary.of_mulVec_image {K : Set (Fin 2 → ℝ)} {A : Mat2} (hA : A.det ≠ 0)
    (h : IsSmoothedPolygonBoundary ((fun v ↦ A *ᵥ v) '' K)) : IsSmoothedPolygonBoundary K := by
  obtain ⟨m, n, a, b, γ, α, β, hab, hhyp, hα, hβ, hfr⟩ := h
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.2 hA
  have hBA : ∀ v, A⁻¹ *ᵥ (A *ᵥ v) = v := fun v ↦ by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hAu, Matrix.one_mulVec]
  have hAB : ∀ v, A *ᵥ (A⁻¹ *ᵥ v) = v := fun v ↦ by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hAu, Matrix.one_mulVec]
  have hBinj : Function.Injective (fun v ↦ A⁻¹ *ᵥ v) := fun v w hvw ↦ by
    simpa only [hAB] using congrArg (fun x ↦ A *ᵥ x) hvw
  have hBdet : A⁻¹.det ≠ 0 := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']; exact inv_ne_zero hA
  have hBc : Continuous (fun v ↦ A⁻¹ *ᵥ v) := continuous_const.matrix_mulVec continuous_id
  -- the image of a segment under `A⁻¹` is a segment
  have hseg : ∀ x y : Fin 2 → ℝ,
      (fun v ↦ A⁻¹ *ᵥ v) '' segment ℝ x y = segment ℝ (A⁻¹ *ᵥ x) (A⁻¹ *ᵥ y) := fun x y ↦
    image_segment ℝ (Matrix.mulVecLin A⁻¹).toAffineMap x y
  -- `v ↦ A v` is a homeomorphism, so `∂K = A⁻¹ ∂(A K)`
  let e : (Fin 2 → ℝ) ≃ₜ (Fin 2 → ℝ) :=
    { toFun := fun v ↦ A *ᵥ v, invFun := fun v ↦ A⁻¹ *ᵥ v, left_inv := hBA, right_inv := hAB,
      continuous_toFun := continuous_const.matrix_mulVec continuous_id,
      continuous_invFun := hBc }
  have hfrK : frontier K = (fun v ↦ A⁻¹ *ᵥ v) '' frontier ((fun v ↦ A *ᵥ v) '' K) := by
    have h1 : e '' frontier K = frontier (e '' K) := e.image_frontier K
    change frontier K = (fun v ↦ A⁻¹ *ᵥ v) '' frontier (e '' K)
    rw [← h1, Set.image_image]
    simp only [e, Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk, hBA, Set.image_id']
  refine ⟨m, n, fun k ↦ A⁻¹ *ᵥ a k, fun k ↦ A⁻¹ *ᵥ b k, fun l t ↦ A⁻¹ *ᵥ γ l t, α, β,
    fun k hk ↦ hab k (hBinj hk), fun l ↦ ?_, fun l ↦ ?_, fun l ↦ ?_, ?_⟩
  · obtain ⟨k₁, k₂, hlt, hcont, hinj, hd₁, hd₂, hdet, c, hc, hcurve⟩ := hhyp l
    have hsub : ∀ x y : Fin 2 → ℝ, A⁻¹ *ᵥ x - A⁻¹ *ᵥ y = A⁻¹ *ᵥ (x - y) := fun x y ↦
      (Matrix.mulVec_sub _ _ _).symm
    have hne : ∀ x : Fin 2 → ℝ, x ≠ 0 → A⁻¹ *ᵥ x ≠ 0 := fun x hx h0 ↦
      hx (hBinj (h0.trans (Matrix.mulVec_zero _).symm))
    refine ⟨k₁, k₂, hlt, hBc.comp_continuousOn hcont,
      fun x hx y hy hxy ↦ hinj hx hy (hBinj hxy), ?_, ?_, ?_, A⁻¹.det ^ 2 * c,
      mul_ne_zero (pow_ne_zero 2 hBdet) hc, fun t ht ↦ ?_⟩
    · rw [hsub]; exact hne _ hd₁
    · rw [hsub]; exact hne _ hd₂
    · rw [hsub, hsub, oct_det2_mulVec]; exact mul_ne_zero hBdet hdet
    · simp only [hsub, oct_det2_mulVec]
      rw [← hcurve t ht]
      ring
  · obtain ⟨k, hk⟩ := Set.mem_iUnion.1 (hα l)
    exact Set.mem_iUnion.2 ⟨k, hseg _ _ ▸ Set.mem_image_of_mem _ hk⟩
  · obtain ⟨k, hk⟩ := Set.mem_iUnion.1 (hβ l)
    exact Set.mem_iUnion.2 ⟨k, hseg _ _ ▸ Set.mem_image_of_mem _ hk⟩
  · rw [hfrK, hfr, Set.image_union, Set.image_iUnion, Set.image_iUnion]
    simp only [hseg, Set.image_image]

end SmoothedPolygons
