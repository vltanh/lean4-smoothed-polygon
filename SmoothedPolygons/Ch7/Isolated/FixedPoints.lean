module

public import SmoothedPolygons.Ch7.Isolated.Defs
public import SmoothedPolygons.Ch7.SmoothedPolygon
public import SmoothedPolygons.Ch7.Isolated.Hyperbolic
public import SmoothedPolygons.Ch7.Isolated.Return
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import SmoothedPolygons.Ch7.Remarks
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# Theorem 7.7.1, steps 6–7: the fixed points of `f⁴` and the final transversality

Step 6 (`iso_fixedPoints`): near the octagon's point, the fixed points of the fourth iterate of the
Poincaré map on the section are the points `q_fix(y₀)`. The book argues "By the implicit function
theorem" (TeX 6616) for each `d` separately; here the inverse function theorem is applied once, at
`q_oct`, and the parameter `y₀(d)` comes from Remark 7.5.2 as in the book (departure from the
paper explained in the section header of step 6). Step 7 (`iso_trace_sq_of_pow_four`,
`iso_y0_of_closing`): the condition `g(t_f) = R` picks `y₀ = y_oct` in this family (the converse
direction of Lemma 7.5.5 for `k = 1`, by the comparison of eigenvalues of its proof).
-/

@[expose] public section

namespace SmoothedPolygons

open Matrix Set Filter Topology MeasureTheory

/-! ### Step 6: the fixed points of `f⁴` near `q_oct`

The book (TeX 6581–6582, 6612–6621): fix `d`; `y₀(d)` is "the real number constructed in
Section 7.5", the inverse of `y₀ ↦ d(y₀) = det Λ₁(q_fix(y₀))`, which is strictly increasing with
range `(0, 9/4)` (Remark 7.5.2), and `q_fix(d) = q_fix(y₀(d))`. "Direct calculation shows that the
fixed point `q_oct` is hyperbolic ... Then the fixed point `q_fix(d)` is also hyperbolic for the
map `f_d⁴` for sufficiently nearby parameters `d`. By the implicit function theorem, for each `d`
near `d_oct`, the function `f_d⁴ - I` can be inverted in an open neighborhood of the fixed point
`q_fix(d)`, forcing the fixed point to be isolated ... Thus, the only fixed points near `q_oct`
are the fixed points `q_fix(d)`."

Departure from the paper: the book applies the implicit function theorem to `f_d⁴ − I` for each
`d` separately, after asserting that `q_fix(d)` stays hyperbolic for nearby `d` (TeX 6615); the
uniqueness "thus the only fixed points near `q_oct` are the `q_fix(d)`" needs neighbourhoods
uniform in `d`, which this does not give. The formal proof applies the inverse function theorem
once, at `q_oct`, to `(section constraints, f⁴ − id)`, whose constraints include `d`; this gives
the uniformity, and the hyperbolicity of `q_fix(d)` for `d ≠ d_oct` is not needed.

Coordinates and notation: `p₀ = iso_phaseCoords q_oct ∈ ℝ⁹`, `F = iso_poincareMapCoords`,
`L = DF(p₀)`, `c = iso_sectionConstraints : ℝ⁹ → ℝ⁵` (`det X - 1`, `⟨X, Λ_R⟩`, `H(e₃)`, `χ₂₃`,
`det Λ₁`) and `T = ker Dc(p₀) = iso_tangentSection`. The map
`Ψ(v) = (c(v), F⁴(v) - v) : ℝ⁹ → ℝ⁵ × ℝ⁹` has at `p₀` the derivative `w ↦ (Dc w, (L⁴ - 1)w)`,
which is injective: `Dc w = 0` means `w ∈ T`, and `L⁴ - 1 = (L - 1)(L + 1)(L² + 1)` is injective
on the `L`-invariant space `T` by hyperbolicity (`iso_hyperbolic` with `θ = 0, π, π/2`). So `Ψ` is
injective on a neighbourhood `W` of `p₀` (the local injectivity part of the inverse function
theorem, `ifp_injOn_of_hasStrictFDerivAt`, from `ApproximatesLinearOn`). On the section, a fixed
point `q` of `f⁴` has `Ψ(q) = (0, 0, 0, 0, d; 0)` with `d = det Λ₁(q)`, and so does `q_fix(y₀)`
with `d = d(y₀)`. By Remark 7.5.2 (`remark7_5_2`), for `d` near `d_oct` the parameter `y₀(d)`
exists and is near `y_oct` (a strictly increasing function with an interval as range has a
continuous inverse), so `q_fix(y₀(d)) ∈ W` and `q = q_fix(y₀(d))` by injectivity. -/

/-- The iterates of the Poincaré map in coordinates are the coordinates of its iterates. -/
lemma ifp_coords_iterate (n : ℕ) {q : iso_PhasePt} (h1 : q.1.trace = 0) (h2 : q.2.1.trace = 0)
    (h3 : q.2.2.trace = 0) :
    iso_poincareMapCoords^[n] (iso_phaseCoords q) = iso_phaseCoords (iso_poincareMap^[n] q) := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    obtain ⟨k1, k2, k3⟩ := irt_poincareMap_traceless h1 h2 h3
    have hF : iso_poincareMapCoords (iso_phaseCoords q) = iso_phaseCoords (iso_poincareMap q) := by
      rw [iso_poincareMapCoords, irt_ofCoords_coords h1 h2 h3]
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hF, ih k1 k2 k3]

/-- The constraints at a point of the section. -/
lemma ifp_constraints_of_section {q : iso_PhasePt} (hq : iso_IsSectionPt q) :
    iso_sectionConstraints (iso_phaseCoords q) = ![0, 0, 0, 0, q.2.1.det] := by
  obtain ⟨h1, h2, h3, hdet, hperp, hH, hχ⟩ := hq
  rw [iso_sectionConstraints, irt_ofCoords_coords h1 h2 h3, hdet, hperp, hH, hχ, sub_self]

/-- The constraint map is `C¹` where the denominators `⟨X, Z_{e₃}⟩`, `⟨X, Z_{e₂}⟩` do not
vanish. -/
lemma ifp_constraints_contDiffAt {p : Fin 9 → ℝ} (hA : -(2 / √3) * p 0 - 2 / 3 * p 2 ≠ 0)
    (hB : 2 / √3 * p 0 - 2 / 3 * p 2 ≠ 0) : ContDiffAt ℝ 1 iso_sectionConstraints p := by
  rw [show iso_sectionConstraints = fun v ↦ ![-(v 0 * v 0) - v 1 * v 2 - 1,
      2 * (v 0 * v 6) + v 1 * v 8 + v 2 * v 7,
      2 * (v 0 * v 3) + (v 4 - 3 / 2) * v 2 + (v 5 + 3 / 2) * v 1 -
        (-(2 / √3) * v 6 - 2 / 3 * v 8) * (-(2 / √3) * v 0 - 2 / 3 * v 2)⁻¹,
      (-(2 / √3) * v 6 - 2 / 3 * v 8) * (-(2 / √3) * v 0 - 2 / 3 * v 2)⁻¹ -
        (2 / √3 * v 6 - 2 / 3 * v 8) * (2 / √3 * v 0 - 2 / 3 * v 2)⁻¹,
      -(v 3 * v 3) - v 4 * v 5] from funext ihy_sectionConstraints_eq, contDiffAt_pi]
  intro i
  fin_cases i <;> dsimp <;> fun_prop (disch := assumption)

/-- **Local injectivity** (inverse function theorem): a map with injective strict derivative at
`a` on a finite-dimensional space is injective near `a`. -/
lemma ifp_injOn_of_hasStrictFDerivAt {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    {f' : E →L[ℝ] F} {a : E} (hf : HasStrictFDerivAt f f' a) (hinj : Function.Injective f') :
    ∃ s ∈ 𝓝 a, InjOn f s := by
  obtain ⟨K, hKpos, hK⟩ := (f' : E →ₗ[ℝ] F).injective_iff_antilipschitz.1 hinj
  have hc : (0 : NNReal) < (2 * K)⁻¹ := by positivity
  obtain ⟨s, hs, happrox⟩ := HasStrictFDerivAt.approximates_deriv_on_nhds hf (Or.inr hc)
  refine ⟨s, hs, fun x hx y hy hxy ↦ ?_⟩
  have h1 := happrox x hx y hy
  rw [hxy, sub_self, zero_sub, norm_neg] at h1
  have h2 : ‖x - y‖ ≤ K * ‖f' (x - y)‖ := by
    have := hK.le_mul_dist x y
    rwa [dist_eq_norm, dist_eq_norm, ContinuousLinearMap.coe_coe, ← map_sub] at this
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hKpos
  have h3 : ‖x - y‖ ≤ ‖x - y‖ / 2 := by
    calc ‖x - y‖ ≤ K * ‖f' (x - y)‖ := h2
      _ ≤ K * (((2 * K)⁻¹ : NNReal) * ‖x - y‖) := by gcongr
      _ = ‖x - y‖ / 2 := by push_cast; field_simp
  have : ‖x - y‖ = 0 := le_antisymm (by linarith [norm_nonneg (x - y)]) (norm_nonneg _)
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

/-- The tangent space `T` of the section at `q_oct` is spanned by `iso_sectionBasis`
(`ihy_tangentSection_eq_sum`). -/
lemma ifp_tangentSection_le_span (v : Fin 9 → ℝ) (hv : v ∈ iso_tangentSection) :
    v ∈ Submodule.span ℝ (range (iso_sectionBasis (y₀ 1) (ellSw (y₀ 1)))) := by
  rw [ihy_tangentSection_eq_sum v hv]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- The derivative of the Poincaré map leaves the tangent space of the section invariant. -/
lemma ifp_fderiv_mem_tangentSection (v : Fin 9 → ℝ) (hv : v ∈ iso_tangentSection) :
    fderiv ℝ iso_poincareMapCoords (iso_phaseCoords (iso_qFix (y₀ 1))) v ∈ iso_tangentSection := by
  set b := iso_sectionBasis (y₀ 1) (ellSw (y₀ 1)) with hb
  set L := fderiv ℝ iso_poincareMapCoords (iso_phaseCoords (iso_qFix (y₀ 1)))
  have hspanT : Submodule.span ℝ (range b) ≤ iso_tangentSection :=
    Submodule.span_le.2 (range_subset_iff.2 iso_sectionBasis_mem)
  have hinv : Submodule.span ℝ (range b) ≤ (Submodule.span ℝ (range b)).comap L.toLinearMap := by
    refine Submodule.span_le.2 (range_subset_iff.2 fun j ↦ ?_)
    change L (b j) ∈ Submodule.span ℝ (range b)
    rw [iso_fderiv_basis j]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact hspanT (hinv (ifp_tangentSection_le_span v hv))

/-- Hyperbolicity gives the injectivity of `L⁴ - 1 = (L - 1)(L + 1)(L² + 1)` on `T`. -/
lemma ifp_pow_four_injective (v : Fin 9 → ℝ) (hv : v ∈ iso_tangentSection)
    (h : (fderiv ℝ iso_poincareMapCoords (iso_phaseCoords (iso_qFix (y₀ 1))))^[4] v = v) :
    v = 0 := by
  set L := fderiv ℝ iso_poincareMapCoords (iso_phaseCoords (iso_qFix (y₀ 1))) with hL
  have hT : ∀ w ∈ iso_tangentSection, L w ∈ iso_tangentSection := ifp_fderiv_mem_tangentSection
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id] at h
  have hv1 : L v ∈ iso_tangentSection := hT v hv
  have hv2 : L (L v) ∈ iso_tangentSection := hT _ hv1
  have hv3 : L (L (L v)) ∈ iso_tangentSection := hT _ hv2
  -- `v₁ = (L + 1)(L² + 1)v` satisfies `Lv₁ = v₁`
  set v₁ := L (L (L v)) + L (L v) + L v + v with hv₁
  have hv₁T : v₁ ∈ iso_tangentSection :=
    iso_tangentSection.add_mem (iso_tangentSection.add_mem (iso_tangentSection.add_mem hv3 hv2)
      hv1) hv
  have hLv₁ : L v₁ = v₁ := by
    simp only [hv₁, map_add, h]; abel
  have h1 : v₁ = 0 := iso_hyperbolic 0 v₁ hv₁T (by
    rw [Real.cos_zero, hLv₁, hLv₁]; module)
  -- `v₂ = (L² + 1)v` satisfies `Lv₂ = -v₂`
  set v₂ := L (L v) + v with hv₂
  have hv₂T : v₂ ∈ iso_tangentSection := iso_tangentSection.add_mem hv2 hv
  have hLv₂ : L v₂ = -v₂ := by
    have : L v₂ + v₂ = v₁ := by simp only [hv₂, hv₁, map_add]; abel
    rw [h1] at this
    exact eq_neg_of_add_eq_zero_left this
  have h2 : v₂ = 0 := iso_hyperbolic Real.pi v₂ hv₂T (by
    rw [Real.cos_pi, hLv₂, map_neg, hLv₂]; module)
  exact iso_hyperbolic (Real.pi / 2) v hv (by
    rw [Real.cos_pi_div_two, mul_zero, zero_smul, sub_zero]; exact h2)

/-! ### Step 6: the theorem -/

/-- Near `q_oct`, the fixed points of `f⁴` on the section are the `q_fix(y₀)`: the book's "Thus,
the only fixed points near `q_oct` are the fixed points `q_fix(d)`" (TeX 6619–6620).

`Ψ = (c, F⁴ - id)` is injective on a neighbourhood `W` of `p₀` (the inverse function theorem at
`q_oct`, instead of the book's implicit function theorem for each `d`: see the section header).
By Remark 7.5.2 (`remark7_5_2`), `d(y₀) = det Λ₁(q_fix(y₀))` is strictly increasing on
`(1/√3, 1)` with range `(0, 9/4)`, so `y₀(d)` exists for `d` in an interval `(d(a), d(b))` around
`d_oct` and lies in `(a, b)`, chosen so that `q_fix(y₀) ∈ W` for `y₀ ∈ (a, b)`. A fixed point `q`
of `f⁴` on the section, in `W` and with `d = det Λ₁(q) ∈ (d(a), d(b))`, has
`Ψ(q) = (0, 0, 0, 0, d; 0) = Ψ(q_fix(y₀(d)))`, so `q = q_fix(y₀(d))`. -/
theorem iso_fixedPoints :
    ∃ V ∈ 𝓝 (iso_qFix (y₀ 1)), ∀ q ∈ V, iso_IsSectionPt q → iso_poincareMap^[4] q = q →
      ∃ y0 ∈ Ioo (1 / √3) 1, q = iso_qFix y0 := by
  obtain ⟨hy0, hy1⟩ := poly_y₀_mem (le_refl 1)
  have hy : 0 < y₀ 1 := poly_y0_pos hy0
  set y := y₀ 1
  set p₀ := iso_phaseCoords (iso_qFix y) with hp₀
  set F := iso_poincareMapCoords
  set L := fderiv ℝ F p₀
  set c := iso_sectionConstraints with hcdef
  set Dc := fderiv ℝ c p₀
  have hFγ : ∀ y', 1 / √3 < y' → y' < 1 → ∀ n : ℕ,
      F^[n] (iso_phaseCoords (iso_qFix y')) = iso_phaseCoords (iso_qFix y') := by
    intro y' h0 h1 n
    obtain ⟨k1, k2, k3, -⟩ := iso_qFix_isSectionPt y' h0 h1
    rw [ifp_coords_iterate n k1 k2 k3, Function.iterate_fixed (iso_poincareMap_qFix y' h0 h1)]
  -- the derivatives at `p₀`
  have hFp : F p₀ = p₀ := hFγ y hy0 hy1 1
  have hF4 : HasStrictFDerivAt (F^[4]) (L ^ 4) p₀ :=
    iso_poincareMapCoords_hasStrictFDerivAt.iterate hFp 4
  obtain ⟨hA, hB⟩ := ihy_qFix_den
  have hcC : ContDiffAt ℝ 1 c p₀ := ifp_constraints_contDiffAt hA hB
  have hc : HasStrictFDerivAt c Dc p₀ := hcC.hasStrictFDerivAt one_ne_zero
  -- `Ψ(v) = (c(v), F⁴(v) - v)` has an injective derivative at `p₀`, so is injective near `p₀`
  set Ψ : (Fin 9 → ℝ) → (Fin 5 → ℝ) × (Fin 9 → ℝ) := fun v ↦ (c v, F^[4] v - v) with hΨdef
  set DΨ : (Fin 9 → ℝ) →L[ℝ] (Fin 5 → ℝ) × (Fin 9 → ℝ) :=
    Dc.prod (L ^ 4 - ContinuousLinearMap.id ℝ _) with hDΨ
  have hΨ : HasStrictFDerivAt Ψ DΨ p₀ := hc.prodMk (hF4.sub (hasStrictFDerivAt_id p₀))
  have hDΨ0 : ∀ w, DΨ w = 0 → w = 0 := by
    intro w hw
    simp only [hDΨ, ContinuousLinearMap.prod_apply, Prod.mk_eq_zero,
      sub_apply, ContinuousLinearMap.id_apply, sub_eq_zero] at hw
    obtain ⟨h1, h2⟩ := hw
    have hwT : w ∈ iso_tangentSection := by
      rw [iso_tangentSection, LinearMap.mem_ker]; exact h1
    refine ifp_pow_four_injective w hwT ?_
    rw [← FunLike.coe_pow_eq_iterate]
    exact h2
  have hinj : Function.Injective DΨ := (injective_iff_map_eq_zero DΨ).2 hDΨ0
  obtain ⟨W, hW, hWinj⟩ := ifp_injOn_of_hasStrictFDerivAt hΨ hinj
  -- `y₀(d)` (Remark 7.5.2): `d(y₀) = det Λ₁(q_fix(y₀))` is strictly increasing with range
  -- `(0, 9/4)`
  obtain ⟨hdet, hmono, hrange, -⟩ := remark7_5_2
  set D := detConstOfMotion
  have hd : ∀ y' ∈ Ioo (1 / √3) 1, (iso_qFix y').2.1.det = D y' := fun y' hy' ↦
    (hdet y' hy'.1 hy'.2 _ _ (strongLift_isStrongLift y' hy'.1) 0
      ⟨le_rfl, (poly_switchTime_pos hy'.1 hy'.2).le⟩).2
  -- an interval `(l, u)` around `y_oct` on which `q_fix(y₀) ∈ W`, and `a < y_oct < b` inside it
  have hY : Ioo (1 / √3) 1 ∩ (fun y' ↦ iso_phaseCoords (iso_qFix y')) ⁻¹' W ∈ 𝓝 y :=
    inter_mem (Ioo_mem_nhds hy0 hy1)
      ((ipc_hasDerivAt_qFix y hy).continuousAt.preimage_mem_nhds hW)
  obtain ⟨l, u, ⟨hly, hyu⟩, hluY⟩ := mem_nhds_iff_exists_Ioo_subset.1 hY
  have ha : (l + y) / 2 ∈ Ioo (1 / √3) 1 := (hluY ⟨by linarith, by linarith⟩).1
  have hb : (y + u) / 2 ∈ Ioo (1 / √3) 1 := (hluY ⟨by linarith, by linarith⟩).1
  have hDa : D ((l + y) / 2) ∈ Ioo 0 (9 / 4) := hrange ▸ mem_image_of_mem D ha
  have hDb : D ((y + u) / 2) ∈ Ioo 0 (9 / 4) := hrange ▸ mem_image_of_mem D hb
  -- the inverse of `d`: for `d ∈ (d(a), d(b))`, `y₀(d)` exists and lies in `(a, b) ⊆ (l, u)`
  have hinv : ∀ d ∈ Ioo (D ((l + y) / 2)) (D ((y + u) / 2)), ∃ y' ∈ Ioo l u, D y' = d := by
    intro d hd'
    obtain ⟨y', hy'I, rfl⟩ : d ∈ D '' Ioo (1 / √3) 1 :=
      hrange ▸ ⟨hDa.1.trans hd'.1, hd'.2.trans hDb.2⟩
    refine ⟨y', ⟨?_, ?_⟩, rfl⟩
    · linarith [(hmono.lt_iff_lt ha hy'I).1 hd'.1]
    · linarith [(hmono.lt_iff_lt hy'I hb).1 hd'.2]
  have hab : Ioo (D ((l + y) / 2)) (D ((y + u) / 2)) ∈ 𝓝 (c p₀ 4) := by
    have h : c p₀ 4 = D y := by
      rw [hp₀, hcdef, ifp_constraints_of_section (iso_qFix_isSectionPt y hy0 hy1)]
      exact hd y ⟨hy0, hy1⟩
    rw [h]
    exact Ioo_mem_nhds (hmono ha ⟨hy0, hy1⟩ (by linarith)) (hmono ⟨hy0, hy1⟩ hb (by linarith))
  -- the neighbourhood of `q_oct`
  have hc4 : ContinuousAt (fun v ↦ c v 4) p₀ :=
    (continuous_apply 4).continuousAt.comp hcC.continuousAt
  set V' := W ∩ (fun v ↦ c v 4) ⁻¹' Ioo (D ((l + y) / 2)) (D ((y + u) / 2))
  have hV'mem : V' ∈ 𝓝 p₀ := inter_mem hW (hc4.preimage_mem_nhds hab)
  refine ⟨iso_phaseCoords ⁻¹' V',
    irt_continuous_phaseCoords.continuousAt.preimage_mem_nhds hV'mem, fun q hqV hsec hfix ↦ ?_⟩
  obtain ⟨hqW, hqd⟩ := hqV
  obtain ⟨y', hy'lu, hdy'⟩ := hinv _ hqd
  obtain ⟨hy'I, hy'W⟩ := hluY hy'lu
  obtain ⟨k1, k2, k3, -⟩ := id hsec
  have hsec' := iso_qFix_isSectionPt y' hy'I.1 hy'I.2
  -- `Ψ(q) = (0, 0, 0, 0, d; 0) = Ψ(q_fix(y₀(d)))`
  have hΨq : Ψ (iso_phaseCoords q) = Ψ (iso_phaseCoords (iso_qFix y')) := by
    have h4 : q.2.1.det = (iso_qFix y').2.1.det := by
      rw [hd y' hy'I, hdy']
      change _ = iso_sectionConstraints (iso_phaseCoords q) 4
      rw [ifp_constraints_of_section hsec]
      rfl
    simp only [hΨdef, hcdef]
    rw [ifp_coords_iterate 4 k1 k2 k3, hfix, sub_self, hFγ y' hy'I.1 hy'I.2 4, sub_self,
      ifp_constraints_of_section hsec, ifp_constraints_of_section hsec', h4]
  have heq := hWinj hqW hy'W hΨq
  refine ⟨y', hy'I, ?_⟩
  obtain ⟨t1, t2, t3, -⟩ := hsec'
  rw [← irt_ofCoords_coords k1 k2 k3, heq, irt_ofCoords_coords t1 t2 t3]

/-! ### Step 7: the final transversality condition -/

/-- If `A ∈ SL₂(ℝ)` and `A⁴ = -I` then `(tr A)² = 2`, by the book's comparison of eigenvalues
(proof of Lemma 7.5.5, TeX 6316–6328, for `k = 1`): let `λ ∈ ℂ` be an eigenvalue of `A`, so
`λ² - (tr A)λ + det A = 0` and the eigenvalues are `λ, λ⁻¹`; comparing eigenvalues on the two
sides of `A⁴ = -I` gives `λ⁴ = -1`. Then `tr A = λ + λ⁻¹` and `(tr A)² = λ² + λ⁻² + 2 = 2`, since
`λ⁻² = -λ²`. (The book writes `λ = exp(πi/4 + πiℓ/2)`, `ℓ ∈ ℤ`, so `tr A = 2cos(π/4 + πℓ/2)`;
`(tr A)² = 2` is the same statement without the polar form.) -/
theorem iso_trace_sq_of_pow_four (A : Mat2) (hdet : A.det = 1) (h4 : A ^ 4 = -1) :
    A.trace ^ 2 = 2 := by
  -- an eigenvalue `μ ∈ ℂ` of `A` (the book's `λ`), with an eigenvector `v`
  set B : Matrix (Fin 2) (Fin 2) ℂ := Complex.ofRealHom.mapMatrix A with hB
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (Matrix.toLin' B)
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hv0 : v ≠ 0 := hv.2
  -- `μ` is a root of `μ² - (tr A)μ + det A`
  have hchar : μ ^ 2 - (A.trace : ℂ) * μ + 1 = 0 := by
    have hBv : B *ᵥ v = μ • v := by rw [← Matrix.toLin'_apply]; exact hv.apply_eq_smul
    have h : (μ • (1 : Matrix (Fin 2) (Fin 2) ℂ) - B).det = 0 :=
      Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv0, by
        rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hBv, sub_self]⟩
    have hdet' : (A 0 0 : ℂ) * A 1 1 - A 0 1 * A 1 0 = 1 := by
      rw [Matrix.det_fin_two] at hdet; exact_mod_cast hdet
    rw [Matrix.det_fin_two] at h
    simp only [hB, RingHom.mapMatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply,
      Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
      Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), smul_eq_mul, mul_one, mul_zero,
      Complex.ofRealHom_eq_coe] at h
    rw [Matrix.trace_fin_two]
    push_cast
    linear_combination h - hdet'
  -- comparing eigenvalues on the two sides of `A⁴ = -I`: `μ⁴ = -1`
  have hμ4 : μ ^ 4 = -1 := by
    have h := hv.pow_apply 4
    rw [← Matrix.toLin'_pow, hB, ← map_pow, h4, map_neg, map_one, map_neg, Matrix.toLin'_one,
      LinearMap.neg_apply, LinearMap.id_apply] at h
    have h' : (μ ^ 4 + 1) • v = 0 := by rw [add_smul, ← h, one_smul, neg_add_cancel]
    exact eq_neg_of_add_eq_zero_left ((smul_eq_zero.1 h').resolve_right hv0)
  -- `tr A = μ + μ⁻¹` and `μ⁻² = -μ²`
  have hμ0 : μ ≠ 0 := by rintro rfl; norm_num at hμ4
  have ht : (A.trace : ℂ) = μ + μ⁻¹ := by
    field_simp
    linear_combination -hchar
  have h2 : ((A.trace ^ 2 : ℝ) : ℂ) = 2 := by
    push_cast
    rw [ht]
    field_simp
    linear_combination hμ4
  exact_mod_cast h2

/-- The final transversality condition picks the octagon in the family: if the trajectory from
`q_fix(y₀)` with four switching intervals ends at `g(4 t_sw) = R`, then `y₀ = y_oct`
(`g(4t_sw) = h⁴R⁴` with `h = g_sw R⁻¹`, so `h⁴ = R⁻³ = -I`, `(tr h)² = 2` by comparing eigenvalues
(`iso_trace_sq_of_pow_four`), and `tr h = 4/(1 + 3y₀²)`; the converse direction of Lemma 7.5.5
for `k = 1`). The book picks the eigenvalues with `ℓ = 0, -k` by a winding-number consideration
(TeX 6322–6326); here the other sign `tr h = -√2` is excluded because `4/(1 + 3y₀²) > 0`. -/
theorem iso_y0_of_closing (y0 : ℝ) (hy0 : 1 / √3 < y0) (hy1 : y0 < 1)
    (h : polygonG y0 (switchTime y0) (4 * switchTime y0) = R) : y0 = y₀ 1 := by
  have hy : 0 < y0 := poly_y0_pos hy0
  have hτ := str_switchTime_pos y0 hy0 hy1
  set hh := segG y0 (switchTime y0) * R⁻¹ with hhdef
  -- `g(4 t_sw) = h⁴ R⁴ = -h⁴ R`
  have hfl : ⌊4 * switchTime y0 / switchTime y0⌋₊ = 4 := by
    rw [mul_div_cancel_right₀ _ hτ.ne']
    exact_mod_cast Nat.floor_natCast 4
  have hR4 : R ^ 4 = -R := by rw [pow_succ, poly_R_pow_three, neg_one_mul]
  rw [polygonG, hfl, show 4 * switchTime y0 - ((4 : ℕ) : ℝ) * switchTime y0 = 0 by push_cast; ring,
    str_segG_zero y0 hy, mul_one, hR4, ← hhdef] at h
  have h4 : hh ^ 4 = -1 := by
    have := congrArg (· * R⁻¹) h
    simp only [Matrix.mul_neg, Matrix.neg_mul, mul_assoc, poly_R_mul_inv, mul_one] at this
    rw [← neg_neg (hh ^ 4), this]
  have hdet : hh.det = 1 := by
    rw [hhdef, Matrix.det_mul, (seg_solution y0 0 hy).2.2.2.2 _, poly_det_Rinv, one_mul]
  have htr := iso_trace_sq_of_pow_four hh hdet h4
  rw [hhdef, trace_segG_switchTime y0 hy0] at htr
  -- `4/(1 + 3y₀²) = √2`, so `3y₀² = 2√2 - 1 = 3 y_oct²`
  have hpos : 0 < 4 / (1 + 3 * y0 ^ 2) := by positivity
  have hsq : 4 / (1 + 3 * y0 ^ 2) = √2 := by rw [← htr, Real.sqrt_sq hpos.le]
  have hs2 : √2 ^ 2 = 2 := poly_sqrt_two_sq
  have h3 : 3 * y0 ^ 2 = 3 * y₀ 1 ^ 2 := by
    rw [poly_three_y₀_one_sq, poly_sqrt8]
    rw [div_eq_iff (by positivity)] at hsq
    nlinarith
  have hy1' : 0 < y₀ 1 := poly_y0_pos (poly_y₀_mem le_rfl).1
  have hprod : (y0 - y₀ 1) * (y0 + y₀ 1) = 0 := by linear_combination h3 / 3
  rcases mul_eq_zero.mp hprod with h' | h'
  · linarith
  · linarith

end SmoothedPolygons
