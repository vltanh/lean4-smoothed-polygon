module

public import SmoothedPolygons.Ch2.BalancedDensity
public import Basic.Analysis.Calculus.DerivInverse

/-!
# Step B1, part 1: the multi-curve of a worst disk

The results of §2.4 (Lemmas 2.4.2, 2.4.3, 2.4.5, 2.4.6) take the multi-curve `σ` of a worst disk
as a hypothesis, with `σ₀` a regular `C¹` parameterization of the boundary by arclength (the
standing assumption of §2.4, TeX 2157–2158: from there on the book assumes that `σ₀` is
parameterized by arclength).
This file produces it: for a worst disk `K` in circle representation (a critical hexagon with
edge midpoints `s_j*`), a balanced pair `(K, σ)` in circle representation
(`IsWorstDisk.exists_isBalancedPair`).

## The book's argument, and how it is filled in

The book takes the parameterization by arclength for granted. Its existence as a `C¹` regular
curve needs the boundary to be `C¹`, which is Lemma 2.2.5 (`lemma2_2_5`: a unique support line at
each boundary point; `rein_Good`). We prove:

1. *The tangent field.* At each boundary point `x` there is a unique unit vector `w` (sup norm)
   with `K` to the left of the line through `x` in the direction `w` (`wd_IsTangent`; existence by
   Hahn–Banach, uniqueness from the unique support line), and it depends continuously on `x`
   along continuous curves on the boundary (`wd_continuous_tangent`; a limit of support lines is a
   support line).
2. *The polar parameterization is `C¹`.* `rein_bd K θ = e(θ)/g_K(e(θ))` satisfies
   `det(e(θ), rein_bd K θ) = 0`; the chord argument of Lemma 2.4.2
   (`bdy_hasDerivAt_of_det2_const`), with the curve `e` in place of `σ₀` and the tangent field of
   step 1 in place of the tangent of `σ₀`, shows that `rein_bd K` is differentiable with derivative
   a positive multiple of the tangent (`wd_hasDerivAt_of_det2_const`,
   `wd_isPositiveBoundaryParam_bd`).
3. *Arclength.* The arclength reparameterization of a regular periodic `C¹` curve is a regular
   `C¹` curve of unit speed (`wd_exists_arclength_reparam`, with the inverse of the arclength from
   `exists_inverse_of_hasDerivAt_pos`).
4. *The multi-curve.* `σ_j(t) = rein_bd K (φ_j(Θ(t)))` with the continuous angles `φ_j` of the edge
   midpoints of the critical hexagons (Lemma 2.2.7, `lemma2_2_7`): a continuous multi-curve on the
   boundary (the midpoints of a critical hexagon of a disk in circle representation form a
   multi-point, `wd_isMultiPoint_hexMidpoint`), so Lemmas 2.4.2, 2.4.3, 2.4.5 and 2.4.6 make
   `(K, σ)` a balanced pair.
-/

@[expose] public section

namespace SmoothedPolygons

open MeasureTheory Set Filter Topology Real

/-! ### The tangent field of a disk with unique support lines -/

/-- `w` is a unit tangent of `K` at `x`: `‖w‖ = 1` (sup norm) and `K` lies to the left of the line
through `x` in the direction `w`. -/
private def wd_IsTangent (K : Set (Fin 2 → ℝ)) (x w : Fin 2 → ℝ) : Prop :=
  ‖w‖ = 1 ∧ ∀ z ∈ K, 0 ≤ det2 w (z - x)

/-- A unit tangent exists at every boundary point (a support functional, Hahn–Banach). -/
private lemma wd_exists_isTangent {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {x : Fin 2 → ℝ}
    (hx : x ∈ frontier K) : ∃ w, wd_IsTangent K x w := by
  obtain ⟨f, hfi, hfK⟩ := bdy_exists_support hK hx
  set n : Fin 2 → ℝ := ![-f (Pi.single 1 1), f (Pi.single 0 1)] with hn_def
  have hn : ∀ y, det2 n y = -f y := fun y ↦ by
    rw [bdy_dual_apply f y]; simp only [hn_def, det2, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hn0 : n ≠ 0 := by
    intro h
    have h1 := hfi 0 (bdy_zero_mem_interior hK)
    have h2 := hn x
    rw [h] at h2
    simp only [det2, Pi.zero_apply, zero_mul, sub_zero] at h2
    rw [map_zero] at h1
    linarith
  refine ⟨‖n‖⁻¹ • n, ?_, fun z hz ↦ ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hn0)]
  · rw [rein_det2_smul_left, hn, map_sub]
    exact mul_nonneg (inv_nonneg.2 (norm_nonneg _)) (by linarith [hfK z hz])

/-- The unit tangent at a boundary point turns counterclockwise about the origin:
`det(x, w) > 0` (the origin is an interior point, to the left of the line). -/
private lemma wd_det2_pos_of_isTangent {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {x w : Fin 2 → ℝ}
    (hw : wd_IsTangent K x w) : 0 < det2 x w := by
  obtain ⟨hw1, hwK⟩ := hw
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw1
  have h0 := bdy_zero_mem_interior hK
  have hle := hwK 0 (interior_subset h0)
  have e : det2 w (0 - x) = det2 x w := by simp only [det2, Pi.sub_apply, Pi.zero_apply]; ring
  rw [e] at hle
  refine lt_of_le_of_ne hle fun h ↦ ?_
  refine bdy_not_mem_interior hw0 (c := det2 w x) (fun z hz ↦ ?_) ?_ h0
  · have := hwK z hz
    rw [rein_det2_sub_right] at this
    linarith
  · have : det2 w x = -det2 x w := rein_det2_swap x w
    simp only [det2, Pi.zero_apply, mul_zero, sub_zero] at this h ⊢
    linarith

/-- The unit tangent at a boundary point is unique when the support line there is unique
(Lemma 2.2.5). -/
private lemma wd_isTangent_unique {K : Set (Fin 2 → ℝ)} (hG : rein_Good K) {x w w' : Fin 2 → ℝ}
    (hx : x ∈ frontier K) (hw : wd_IsTangent K x w) (hw' : wd_IsTangent K x w') : w = w' := by
  have hK := hG.1
  have hxK := rein_frontier_subset hK hx
  have hw0 : w ≠ 0 := by rintro rfl; have := hw.1; simp at this
  have hw0' : w' ≠ 0 := by rintro rfl; have := hw'.1; simp at this
  -- both lines are support lines at `x`, hence equal (Lemma 2.2.5)
  have hℓ := rein_isSupportLine_det2 hw0 hw.2 hxK
  have hℓ' := rein_isSupportLine_det2 hw0' hw'.2 hxK
  have hxℓ : ∀ p : Fin 2 → ℝ, x ∈ {z | det2 p (z - x) = 0} := fun p ↦ by
    simp only [mem_ofPred_eq, sub_self, det2, Pi.zero_apply, mul_zero]
  obtain ⟨ℓ, -, huniq⟩ := hG.2.1 x hx
  have e : {z | det2 w (z - x) = 0} = {z | det2 w' (z - x) = 0} :=
    (huniq _ ⟨hℓ, hxℓ w⟩).trans (huniq _ ⟨hℓ', hxℓ w'⟩).symm
  have hmem : x + w' ∈ {z | det2 w (z - x) = 0} := by
    rw [e]; simp only [mem_ofPred_eq, add_sub_cancel_left, rein_det2_self]
  simp only [mem_ofPred_eq, add_sub_cancel_left] at hmem
  -- so `w' = c w`, with `c > 0` (orientation) and `c = 1` (norm)
  have hc := bdy_eq_smul_of_det2_eq_zero hw0 (by rw [rein_det2_swap, hmem, neg_zero])
  set c := (w' 0 * w 0 + w' 1 * w 1) / (w 0 ^ 2 + w 1 ^ 2)
  have hp := wd_det2_pos_of_isTangent hK hw
  have hp' := wd_det2_pos_of_isTangent hK hw'
  rw [hc, rein_det2_smul_right] at hp'
  have hcpos : 0 < c := by
    by_contra hneg
    push Not at hneg
    nlinarith
  have hn := hw'.1
  rw [hc, norm_smul, hw.1, Real.norm_of_nonneg hcpos.le, mul_one] at hn
  rw [hc, hn, one_smul]

open Classical in
/-- The unit tangent of the boundary of `K` at `x`. -/
private noncomputable def wd_tangent (K : Set (Fin 2 → ℝ)) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  if h : ∃ w, wd_IsTangent K x w then h.choose else 0

private lemma wd_tangent_spec {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) {x : Fin 2 → ℝ}
    (hx : x ∈ frontier K) : wd_IsTangent K x (wd_tangent K x) := by
  have h := wd_exists_isTangent hK hx
  rw [wd_tangent, dite_eq_left h]
  exact h.choose_spec

/-- **The tangent field is continuous** along continuous curves on the boundary: a limit of
support lines is a support line, and the support line is unique at each boundary point. -/
private lemma wd_continuous_tangent {K : Set (Fin 2 → ℝ)} (hG : rein_Good K) {τ : ℝ → Fin 2 → ℝ}
    (hτ : Continuous τ) (hτK : ∀ t, τ t ∈ frontier K) :
    Continuous fun t ↦ wd_tangent K (τ t) := by
  have hK := hG.1
  rw [continuous_iff_continuousAt]
  intro t₀
  refine (isCompact_sphere (0 : Fin 2 → ℝ) 1).tendsto_nhds_of_unique_mapClusterPt
    (Filter.Eventually.of_forall fun t ↦ ?_) fun w hw hclus ↦ ?_
  · simpa using (wd_tangent_spec hK (hτK t)).1
  · rw [mem_sphere_zero_iff_norm] at hw
    refine (wd_isTangent_unique hG (hτK t₀) (wd_tangent_spec hK (hτK t₀))
      ⟨hw, fun z hz ↦ ?_⟩).symm
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
    have h1 : det2 (wd_tangent K (τ t)) (z - τ t) < 0 :=
      hVW (show (t, wd_tangent K (τ t)) ∈ V ×ˢ W from ⟨htV, htW⟩)
    have h2 := (wd_tangent_spec hK (hτK t)).2 z hz
    linarith

/-! ### Differentiability of boundary curves with a constraint -/

/-- **The chord lemma** (the argument of `bdy_hasDerivAt_of_det2_const`, with an arbitrary
differentiable curve `γ` and an arbitrary continuous field `U` of unit tangents). Let `τ` be a
continuous curve on the boundary of `K ∈ 𝔎_ccs` and `U(s)` a unit tangent at `τ(s)`, continuous at
`t`, with `det(γ(s), τ(s)) = c` for all `s`, where `γ` is differentiable at `t`. If
`det(γ(t), U(t)) ≠ 0`, then `τ'(t) = (-det(γ'(t), τ(t))/det(γ(t), U(t))) U(t)`. -/
private lemma wd_hasDerivAt_of_det2_const {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K)
    {γ τ U : ℝ → Fin 2 → ℝ} {γ' : Fin 2 → ℝ} {t c : ℝ} (hγ : HasDerivAt γ γ' t)
    (hτ : Continuous τ) (hτK : ∀ s, τ s ∈ frontier K) (hU : ∀ s, wd_IsTangent K (τ s) (U s))
    (hUc : ContinuousAt U t) (hc : ∀ s, det2 (γ s) (τ s) = c) (hb : det2 (γ t) (U t) ≠ 0) :
    HasDerivAt τ ((-det2 γ' (τ t) / det2 (γ t) (U t)) • U t) t := by
  set u := U t with hu_def
  set p := γ t with hp_def
  set D := det2 u p with hD_def
  have hDp : D = -det2 p u := by simp only [D, det2]; ring
  have hD : D ≠ 0 := by rw [hDp, neg_ne_zero]; exact hb
  have hDpos : 0 < |D| := abs_pos.2 hD
  have hu1 : ‖u‖ = 1 := (hU t).1
  rw [hasDerivAt_iff_tendsto_slope_zero]
  set q : ℝ → Fin 2 → ℝ := fun h ↦ h⁻¹ • (τ (t + h) - τ t) with hq
  set A : ℝ → ℝ := fun h ↦ det2 u (q h) / D with hA
  set B : ℝ → ℝ := fun h ↦ det2 (q h) p / D with hB
  have hqAB : q = fun h ↦ A h • p + B h • u := funext fun h ↦ bdy_cramer (q h) hD
  -- `B` converges, by differentiating the constraint
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
  have hBlim : Tendsto B (𝓝[≠] 0) (𝓝 (det2 γ' (τ t) / D)) := by
    have : B = fun h ↦ det2 (h⁻¹ • (γ (t + h) - γ t)) (τ (t + h)) / D :=
      funext fun h ↦ by simp only [B, hBeq]
    rw [this]
    exact (bdy_tendsto_det2 hγ.tendsto_slope_zero hτlim).div_const D
  -- the chord lies between the tangent lines at its ends
  set E : ℝ → ℝ := fun h ↦ 2 * ‖u - U (t + h)‖ with hE
  have hElim : Tendsto E (𝓝[≠] 0) (𝓝 0) := by
    have h1 : Tendsto (fun h ↦ U (t + h)) (𝓝 0) (𝓝 u) := by
      have h0 : Tendsto (fun h : ℝ ↦ t + h) (𝓝 0) (𝓝 t) := by
        simpa using (continuous_const.add continuous_id).tendsto (0 : ℝ) (f := fun h : ℝ ↦ t + h)
      exact hUc.tendsto.comp h0
    have h2 : Tendsto (fun h ↦ 2 * ‖u - U (t + h)‖) (𝓝 0) (𝓝 (2 * ‖u - u‖)) :=
      (tendsto_const_nhds.sub h1).norm.const_mul 2
    simpa using h2.mono_left nhdsWithin_le_nhds
  have hdetq : ∀ h, |det2 u (q h)| ≤ E h * ‖q h‖ := by
    intro h
    set U' := U (t + h)
    have h1 : 0 ≤ det2 u (τ (t + h) - τ t) :=
      (hU t).2 _ (hK.2.1.isClosed.frontier_subset (hτK (t + h)))
    have h2 : 0 ≤ det2 U' (τ t - τ (t + h)) :=
      (hU (t + h)).2 _ (hK.2.1.isClosed.frontier_subset (hτK t))
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

/-- **The polar parameterization of the boundary of a disk with unique support lines is a
positively oriented regular `C¹` parameterization**, with `2π`-periodic derivative a positive
multiple of the unit tangent. -/
private lemma wd_isPositiveBoundaryParam_bd {K : Set (Fin 2 → ℝ)} (hG : rein_Good K) :
    IsPositiveBoundaryParam K (rein_bd K) := by
  have hK := hG.1
  set U : ℝ → Fin 2 → ℝ := fun s ↦ wd_tangent K (rein_bd K s) with hU_def
  set γ' : ℝ → Fin 2 → ℝ := fun θ ↦ ![-Real.sin θ, Real.cos θ] with hγ'_def
  have hbdc := rein_continuous_bd hK
  have hbdK := rein_bd_mem_frontier hK
  have hUc : Continuous U := wd_continuous_tangent hG hbdc hbdK
  have hUt : ∀ s, wd_IsTangent K (rein_bd K s) (U s) := fun s ↦ wd_tangent_spec hK (hbdK s)
  have hγ : ∀ θ, HasDerivAt rein_dir (γ' θ) θ := by
    intro θ
    refine hasDerivAt_pi.2 fun i ↦ ?_
    fin_cases i
    · simpa [rein_dir, hγ'_def] using Real.hasDerivAt_cos θ
    · simpa [rein_dir, hγ'_def] using Real.hasDerivAt_sin θ
  have hγ'c : Continuous γ' := by simp only [hγ'_def]; fun_prop
  -- `rein_bd K θ = r(θ) e(θ)` with `r(θ) > 0`
  set r : ℝ → ℝ := fun θ ↦ (gauge K (rein_dir θ))⁻¹ with hr_def
  have hr : ∀ θ, 0 < r θ := fun θ ↦ inv_pos.2 (rein_gauge_pos hK (rein_dir_ne_zero θ))
  have hbd : ∀ θ, rein_bd K θ = r θ • rein_dir θ := fun θ ↦ rfl
  have hc : ∀ s, det2 (rein_dir s) (rein_bd K s) = 0 := fun s ↦ by
    rw [hbd, rein_det2_smul_right, rein_det2_self, mul_zero]
  -- `det(e(θ), U(θ)) > 0`
  have hpos : ∀ θ, 0 < det2 (rein_dir θ) (U θ) := by
    intro θ
    have h := wd_det2_pos_of_isTangent hK (hUt θ)
    rw [hbd, rein_det2_smul_left] at h
    exact pos_of_mul_pos_right h (hr θ).le
  have hγbd : ∀ θ, det2 (γ' θ) (rein_bd K θ) = -r θ := by
    intro θ
    rw [hbd, rein_det2_smul_right]
    simp only [hγ'_def, rein_dir, det2, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination (-(r θ)) * Real.sin_sq_add_cos_sq θ
  -- the derivative (the chord lemma)
  have hd : ∀ θ, HasDerivAt (rein_bd K)
      ((-det2 (γ' θ) (rein_bd K θ) / det2 (rein_dir θ) (U θ)) • U θ) θ := fun θ ↦
    wd_hasDerivAt_of_det2_const hK (hγ θ) hbdc hbdK hUt hUc.continuousAt hc (hpos θ).ne'
  have hderiv : ∀ θ, deriv (rein_bd K) θ =
      (-det2 (γ' θ) (rein_bd K θ) / det2 (rein_dir θ) (U θ)) • U θ := fun θ ↦ (hd θ).deriv
  have hcoef : ∀ θ, 0 < -det2 (γ' θ) (rein_bd K θ) / det2 (rein_dir θ) (U θ) := fun θ ↦ by
    rw [hγbd, neg_neg]; exact div_pos (hr θ) (hpos θ)
  have hU0 : ∀ θ, U θ ≠ 0 := fun θ h ↦ by have := (hUt θ).1; rw [h] at this; simp at this
  refine ⟨contDiff_one_iff_deriv.2 ⟨fun θ ↦ (hd θ).differentiableAt, ?_⟩, fun θ ↦ ?_, ?_,
    fun θ ↦ ?_⟩
  · rw [funext hderiv]
    exact (((bdy_continuous_det2 hγ'c hbdc).neg).div (bdy_continuous_det2 rein_continuous_dir hUc)
      fun θ ↦ (hpos θ).ne').smul hUc
  · rw [hderiv]
    exact smul_ne_zero (hcoef θ).ne' (hU0 θ)
  · refine Subset.antisymm (range_subset_iff.2 hbdK) fun x hx ↦ ?_
    obtain ⟨θ, rfl⟩ := rein_frontier_eq_bd hK hx
    exact mem_range_self θ
  · rw [hderiv, rein_det2_smul_right]
    exact mul_pos (hcoef θ) (wd_det2_pos_of_isTangent hK (hUt θ))

/-! ### Reparameterization by arclength -/

/-- **Arclength.** A regular `C¹` curve `β` with period `p > 0` has a reparameterization
`β ∘ Θ` of unit (Euclidean) speed, with `Θ` a continuous increasing bijection,
`Θ(t + L) = Θ(t) + p` (`L` the length of a period) and `(β ∘ Θ)'(t)` a positive multiple of
`β'(Θ(t))`: `Θ` is the inverse of the arclength `ℓ(θ) = ∫₀^θ |β'|`. -/
private lemma wd_exists_arclength_reparam {β : ℝ → Fin 2 → ℝ} (hβ : ContDiff ℝ 1 β)
    (hreg : ∀ θ, deriv β θ ≠ 0) {p : ℝ} (hp : 0 < p) (hper : ∀ θ, β (θ + p) = β θ) :
    ∃ Θ : ℝ → ℝ, Continuous Θ ∧ StrictMono Θ ∧ Function.Surjective Θ ∧ Θ 0 = 0 ∧
      (∃ L : ℝ, 0 < L ∧ ∀ t, Θ (t + L) = Θ t + p) ∧ ContDiff ℝ 1 (fun t ↦ β (Θ t)) ∧
      (∀ t, ∃ c : ℝ, 0 < c ∧ deriv (fun t ↦ β (Θ t)) t = c • deriv β (Θ t)) ∧
      ∀ t, deriv (fun t ↦ β (Θ t)) t 0 ^ 2 + deriv (fun t ↦ β (Θ t)) t 1 ^ 2 = 1 := by
  have hv : Continuous (deriv β) := hβ.continuous_deriv le_rfl
  have hβd : ∀ θ, HasDerivAt β (deriv β θ) θ := fun θ ↦
    (hβ.differentiable one_ne_zero θ).hasDerivAt
  -- the speed `n = |β'|` and the arclength `ℓ = ∫ n`
  set n : ℝ → ℝ := fun θ ↦ √(deriv β θ 0 ^ 2 + deriv β θ 1 ^ 2) with hn_def
  have hnpos : ∀ θ, 0 < n θ := fun θ ↦ Real.sqrt_pos.2 (bdy_sq_pos (hreg θ))
  have hnc : Continuous n := by
    have h0 := (continuous_apply 0).comp hv
    have h1 := (continuous_apply 1).comp hv
    exact ((h0.pow 2).add (h1.pow 2)).sqrt
  set ℓ : ℝ → ℝ := fun θ ↦ ∫ s in (0 : ℝ)..θ, n s with hℓ_def
  have hℓ : ∀ θ, HasDerivAt ℓ (n θ) θ := fun θ ↦ (hnc.integral_hasStrictDerivAt 0 θ).hasDerivAt
  have hℓ0 : ℓ 0 = 0 := by simp [hℓ_def]
  have hvper : ∀ θ, deriv β (θ + p) = deriv β θ := fun θ ↦ by
    rw [← deriv_comp_add_const]
    congr 1
    funext s
    exact hper s
  have hnper : ∀ θ, n (θ + p) = n θ := fun θ ↦ by simp only [hn_def, hvper]
  have hL : ∀ θ, ℓ (θ + p) = ℓ θ + ℓ p := by
    have hd : ∀ θ, HasDerivAt (fun θ ↦ ℓ (θ + p) - ℓ θ) 0 θ := fun θ ↦ by
      have := (HasDerivAt.comp_add_const θ p (hℓ (θ + p))).sub (hℓ θ)
      rwa [hnper, sub_self] at this
    intro θ
    have hc := is_const_of_deriv_eq_zero (fun s ↦ (hd s).differentiableAt)
      (fun s ↦ (hd s).deriv) θ 0
    simp only [zero_add, hℓ0, sub_zero] at hc
    linarith
  obtain ⟨hLpos, Θ, hΘc, hΘm, hΘ0, -, hΘℓ, hΘL, hΘd⟩ :=
    exists_inverse_of_hasDerivAt_pos hℓ hnpos hℓ0 hp hL
  -- `(β ∘ Θ)' = β'(Θ)/n(Θ)`
  have hd : ∀ t, HasDerivAt (fun t ↦ β (Θ t)) ((n (Θ t))⁻¹ • deriv β (Θ t)) t := fun t ↦
    (hβd (Θ t)).scomp t (hΘd t)
  have hderiv : ∀ t, deriv (fun t ↦ β (Θ t)) t = (n (Θ t))⁻¹ • deriv β (Θ t) := fun t ↦
    (hd t).deriv
  refine ⟨Θ, hΘc, hΘm, fun θ ↦ ⟨ℓ θ, hΘℓ θ⟩, hΘ0, ⟨ℓ p, hLpos, hΘL⟩, ?_,
    fun t ↦ ⟨_, inv_pos.2 (hnpos _), hderiv t⟩,
    fun t ↦ ?_⟩
  · refine contDiff_one_iff_deriv.2 ⟨fun t ↦ (hd t).differentiableAt, ?_⟩
    rw [funext hderiv]
    exact ((hnc.comp hΘc).inv₀ fun t ↦ (hnpos _).ne').smul (hv.comp hΘc)
  · rw [hderiv]
    have hs := Real.sq_sqrt (bdy_sq_pos (hreg (Θ t))).le
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_pow, mul_pow, ← mul_add, inv_pow]
    simp only [hn_def]
    rw [hs]
    exact inv_mul_cancel₀ (bdy_sq_pos (hreg (Θ t))).ne'

/-! ### The multi-curve of a worst disk -/

/-- The edge midpoints of every critical hexagon of a disk in circle representation (a critical
hexagon with edge midpoints `s_j*`) form a multi-point: all critical hexagons have the area
`2√3 = 4 det(m₀, m₁)` (`hex_volume_hexagonOf`). -/
private lemma wd_isMultiPoint_hexMidpoint {K : Set (Fin 2 → ℝ)} {v w : ZMod 6 → Fin 2 → ℝ}
    (hv : IsLeastAreaHexagon K v) (hvm : ∀ j, hexMidpoint v j = sixthRoot j)
    (hw : IsLeastAreaHexagon K w) : IsMultiPoint (hexMidpoint w) := by
  -- all critical hexagons have the same area, `4 det(m₀, m₁)`
  have hvw : volume (hexagonOf v) = volume (hexagonOf w) :=
    le_antisymm (hv.2.2 w hw.1 hw.2.1) (hw.2.2 v hv.1 hv.2.1)
  have hreal : volume.real (hexagonOf v) = volume.real (hexagonOf w) := by
    simp only [measureReal_def, hvw]
  have hs3 : det2 (sixthRoot 0) (sixthRoot 1) = √3 / 2 := (bdy_isMultiPoint_sixthRoot 0).2.2
  rw [hex_volume_hexagonOf hv.1, hex_volume_hexagonOf hw.1, hvm, hvm, hs3] at hreal
  set m := hexMidpoint w with hm
  have hsucc : ∀ k, m (k + 1) = m k + m (k + 2) := bdy_hexMidpoint_succ hw.1
  have h3 : ∀ k, m (k + 3) = -m k := bdy_hexMidpoint_add_three hw.1
  -- `det(m_{k+1}, m_{k+2}) = det(m_k, m_{k+1})`
  have hstep : ∀ k, det2 (m (k + 1)) (m (k + 1 + 1)) = det2 (m k) (m (k + 1)) := by
    intro k
    have e : m (k + 1 + 1) = m (k + 1) - m k := by
      rw [hsucc k, show k + 1 + 1 = k + 2 by ring]; abel
    rw [e]; unfold det2; simp only [Pi.sub_apply]; ring
  have hnat : ∀ n : ℕ, det2 (m n) (m (n + 1)) = √3 / 2 := by
    intro n
    induction n with
    | zero => simp only [Nat.cast_zero, zero_add]; linarith
    | succ n ih => push_cast; rw [hstep, ih]
  intro j
  refine ⟨?_, h3 j, ?_⟩
  · have e1 := hsucc j
    have e2 := h3 (j + 1)
    rw [show j + 1 + 3 = j + 4 by ring] at e2
    rw [e2, e1]; abel
  · have := hnat j.val
    simpa using this

/-- **Step B1, part 1: a worst disk in circle representation is a balanced disk** (§2.4, after
Definition 2.4.7: "Every `K_min` ... is balanced"). If `K` is a worst disk with a critical hexagon
whose edge midpoints are `s_j*`, there is a multi-curve `σ` with `(K, σ)` a balanced pair in
circle representation: `σ₀` the arclength parameterization of the boundary from `s₀*`
(`wd_isPositiveBoundaryParam_bd`, `wd_exists_arclength_reparam`), `σ_j` the edge midpoints of the
critical hexagons (Lemma 2.2.7), and Lemmas 2.4.2, 2.4.3, 2.4.5, 2.4.6. -/
theorem IsWorstDisk.exists_isBalancedPair {K : Set (Fin 2 → ℝ)} (hK : IsWorstDisk K)
    {v : ZMod 6 → Fin 2 → ℝ} (hv : IsLeastAreaHexagon K v)
    (hvm : ∀ j, hexMidpoint v j = sixthRoot j) :
    ∃ (σ : ZMod 6 → ℝ → Fin 2 → ℝ) (tf : ℝ), IsBalancedPair K σ tf ∧ IsCircleRepresentation σ := by
  have hK1 := hK.1
  have hG : rein_Good K := rein_good_of_worst (ch2_isWorstLatticeDisk_iff_isWorstDisk.2 hK)
  -- the boundary by polar angle, then by arclength
  have hbd := wd_isPositiveBoundaryParam_bd hG
  obtain ⟨Θ, hΘc, hΘm, hΘs, hΘ0, ⟨L, hL, hΘL⟩, hC1, hcpos, harc⟩ :=
    wd_exists_arclength_reparam hbd.1 hbd.2.1 two_pi_pos (rein_bd_add_two_pi K)
  have hΘL' : Θ L = 2 * π := by have := hΘL 0; rwa [zero_add, hΘ0, zero_add] at this
  -- the continuous angles of the edge midpoints of the critical hexagons (Lemma 2.2.7)
  obtain ⟨φ, hφ0, hφ, hφv⟩ := (lemma2_2_7 hK).2
  set σ : ZMod 6 → ℝ → Fin 2 → ℝ := fun j t ↦ rein_bd K (φ j (Θ t)) with hσ_def
  have hbdc := rein_continuous_bd hK1
  have hσc : ∀ j, Continuous (σ j) := fun j ↦ hbdc.comp ((hφ j).1.comp hΘc)
  have hσK : ∀ j t, σ j t ∈ frontier K := fun j t ↦ rein_bd_mem_frontier hK1 _
  have hmid : ∀ θ, ∃ w, IsLeastAreaHexagon K w ∧ ∀ j, hexMidpoint w j = rein_bd K (φ j θ) := by
    intro θ
    obtain ⟨w, hw, hwm⟩ := hφv θ
    refine ⟨w, hw, fun j ↦ ?_⟩
    obtain ⟨hwK, r, hr, hwr⟩ := hwm j
    exact rein_eq_bd hK1 hwK hr hwr
  -- multi-points
  have hσm : ∀ t, IsMultiPoint fun j ↦ σ j t := by
    intro t
    obtain ⟨w, hw, hwm⟩ := hmid (Θ t)
    have e : (fun j ↦ σ j t) = hexMidpoint w := funext fun j ↦ (hwm j).symm
    rw [e]
    exact wd_isMultiPoint_hexMidpoint hv hvm hw
  -- `σ₀` is a regular positively oriented parameterization by arclength
  have hσ0 : σ 0 = fun t ↦ rein_bd K (Θ t) := by funext t; simp [hσ_def, hφ0]
  have hpar0 : IsPositiveBoundaryParam K (σ 0) := by
    rw [hσ0]
    refine ⟨hC1, fun t h ↦ ?_, ?_, fun t ↦ ?_⟩
    · have := harc t; rw [h] at this; simp at this
    · rw [show (fun t ↦ rein_bd K (Θ t)) = rein_bd K ∘ Θ from rfl, range_comp, hΘs.range_eq,
        image_univ]
      exact hbd.2.2.1
    · obtain ⟨c, hc, hd⟩ := hcpos t
      rw [hd, rein_det2_smul_right]
      exact mul_pos hc (hbd.2.2.2 _)
  -- Lemmas 2.4.2 and 2.4.3
  have hpar := lemma2_4_2 hK hσc hσm hσK hpar0
  have harc0 : ∀ t, deriv (σ 0) t 0 ^ 2 + deriv (σ 0) t 1 ^ 2 = 1 := by rw [hσ0]; exact harc
  have hlip := lemma2_4_3 hK (fun j ↦ (hpar j).1) hσm hσK (hpar 0).2.2.1 harc0
  have hbm : IsBoundaryMultiCurve K σ := ⟨hpar, hσm⟩
  -- periodicity, simplicity and image
  have hper : ∀ j t, σ j (t + L) = σ j t := fun j t ↦ by
    simp only [hσ_def, hΘL, (hφ j).2.2, rein_bd_add_two_pi]
  have hΘmem : ∀ t ∈ Ico 0 L, Θ t ∈ Ico 0 (2 * π) := fun t ht ↦
    ⟨by rw [← hΘ0]; exact hΘm.monotone ht.1, by rw [← hΘL']; exact hΘm ht.2⟩
  have hinj : ∀ j, InjOn (σ j) (Ico 0 L) := by
    intro j s hs t ht hst
    obtain ⟨k, hk⟩ := rein_bd_inj hK1 hst
    have hm := (hφ j).2.1
    have h2π := (hφ j).2.2 0
    rw [zero_add] at h2π
    have a1 := hm.monotone (hΘmem s hs).1
    have a2 := hm (hΘmem s hs).2
    have b1 := hm.monotone (hΘmem t ht).1
    have b2 := hm (hΘmem t ht).2
    have hk0 : k = 0 := by
      have h1 : (k : ℝ) < 1 := by nlinarith [pi_pos]
      have h2 : (-1 : ℝ) < k := by nlinarith [pi_pos]
      have : k < 1 := by exact_mod_cast h1
      have : -1 < k := by exact_mod_cast h2
      omega
    rw [hk0, Int.cast_zero, zero_mul, add_zero] at hk
    exact hΘm.injective (hm.injective hk.symm)
  have himg : ∀ j, σ j '' Ico 0 L = frontier K := by
    intro j
    refine Subset.antisymm (image_subset_iff.2 fun t _ ↦ hσK j t) fun x hx ↦ ?_
    rw [← (hpar j).2.2.1] at hx
    obtain ⟨t, rfl⟩ := hx
    obtain ⟨y, hy, hyt⟩ := Function.Periodic.exists_mem_Ico₀ (hper j) hL t
    exact ⟨y, hy, hyt.symm⟩
  -- circle representation: `σ(0)` is the multi-point through `s₀*`
  have hcirc : IsCircleRepresentation σ := by
    have hvK : ∀ j, hexMidpoint v j ∈ frontier K := fun j ↦ rein_hexMidpoint_mem_frontier hK1 hv j
    have h00 : σ 0 0 = hexMidpoint v 0 := by
      rw [hvm 0]
      simp only [hσ_def, hφ0, id, hΘ0]
      symm
      refine rein_eq_bd hK1 (hvm 0 ▸ hvK 0) one_pos ?_
      ext i; fin_cases i <;> simp [sixthRoot, rein_dir]
    intro j
    rw [← hvm j]
    exact bdy_eq_hexMidpoint hK hv hvK (hσm 0) (fun j ↦ hσK j 0) h00 j
  have h6 : 6 * (L / 6) = L := by ring
  refine ⟨σ, L / 6, ⟨hK1, fun j ↦ ⟨(hpar j).1, (hpar j).2.1⟩, hlip, hσm,
    lemma2_4_6 hK1 hbm hlip, fun j t ↦ lemma2_4_5 hK1 hbm j t, by positivity, ?_, ?_, ?_⟩, hcirc⟩
  · rw [h6]; exact hper
  · rw [h6]; exact hinj
  · rw [h6]; exact himg

end SmoothedPolygons
