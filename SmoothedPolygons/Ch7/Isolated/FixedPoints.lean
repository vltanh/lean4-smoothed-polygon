module

public import SmoothedPolygons.Ch7.Isolated.Defs
public import SmoothedPolygons.Ch7.SmoothedPolygon
public import SmoothedPolygons.Ch7.Isolated.Hyperbolic
public import SmoothedPolygons.Ch7.Isolated.Return
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-!
# Theorem 7.7.1, steps 6–7: the implicit function theorem and the final transversality

Step 6: near the octagon's point, the fixed points of the fourth iterate of the Poincaré map on the
section are the points `q_fix(y₀)`. Step 7: the condition `g(t_f) = R` picks `y₀ = y_oct` in this
family (the converse direction of Lemma 7.5.5 for `k = 1`).
-/

@[expose] public section

namespace SmoothedPolygons

open Matrix Set Filter Topology MeasureTheory

/-! ### Step 6: the implicit function theorem

Coordinates and notation: `p₀ = iso_phaseCoords q_oct ∈ ℝ⁹`, `F = iso_poincareMapCoords`,
`L = DF(p₀)`, `c = iso_sectionConstraints : ℝ⁹ → ℝ⁵` (`det X - 1`, `⟨X, Λ_R⟩`, `H(e₃)`, `χ₂₃`,
`det Λ₁`) and `T = ker Dc(p₀) = iso_tangentSection`. The map
`Ψ(v) = (c(v), F⁴(v) - v) : ℝ⁹ → ℝ⁵ × ℝ⁹` has at `p₀` the derivative `w ↦ (Dc w, (L⁴ - 1)w)`,
which is injective: `Dc w = 0` means `w ∈ T`, and `L⁴ - 1 = (L - 1)(L + 1)(L² + 1)` is injective
on the `L`-invariant space `T` by hyperbolicity (`iso_hyperbolic` with `θ = 0, π, π/2`). So `Ψ` is
injective near `p₀` (inverse function theorem, in the form of `ApproximatesLinearOn`). On the
section, a fixed point `q` of `f⁴` has `Ψ(q) = (0, 0, 0, 0, det Λ₁(q); 0)`, and so does
`q_fix(y₀)` with `det Λ₁ = d(y₀)`. The function `d(y₀) = det Λ₁(q_fix(y₀))` has nonzero derivative
at `y_oct`: its derivative is the last component of `DΨ(p₀)γ'`, `γ = q_fix` in coordinates (the
other components vanish since `γ` lies in the section and is fixed by `f⁴`), and `γ' ≠ 0`. So
`d` takes every value near `d(y_oct)` near `y_oct`, and `q = q_fix(y₀)` by injectivity. The
coordinate `d` plays the role of the book's parameter `d` (uniformity in `d` is automatic), and
the monotonicity of `d(y₀)` (Remark 7.5.2) is not needed. -/

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

/-- The tangent space `T` of the section at `q_oct` is spanned by `iso_sectionBasis` (a vector of
`T` is determined by its free coordinates `δX₀₀, δX₀₁, δΛ₁₀₀, δΛ₁₀₁`). -/
lemma ifp_tangentSection_le_span (v : Fin 9 → ℝ) (hv : v ∈ iso_tangentSection) :
    v ∈ Submodule.span ℝ (range (iso_sectionBasis (y₀ 1) (ellSw (y₀ 1)))) := by
  have hy : 0 < y₀ 1 := poly_y0_pos (poly_y₀_mem le_rfl).1
  set b := iso_sectionBasis (y₀ 1) (ellSw (y₀ 1)) with hb
  set w := v - (v 0 • b 0 + (√3 * v 1) • b 1 + (y₀ 1 * v 3) • b 2 + (√3 * y₀ 1 * v 4) • b 3)
    with hw
  have hmem : ∀ j, b j ∈ iso_tangentSection := iso_sectionBasis_mem
  have hwT : w ∈ iso_tangentSection := by
    refine iso_tangentSection.sub_mem hv ?_
    refine iso_tangentSection.add_mem (iso_tangentSection.add_mem (iso_tangentSection.add_mem
      ?_ ?_) ?_) ?_ <;> exact iso_tangentSection.smul_mem _ (hmem _)
  have hw0 : w = 0 := by
    refine ihy_tangentSection_eq_zero w hwT ?_ ?_ ?_ ?_ <;>
      simp only [hw, hb, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        iso_sectionBasis, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
      field_simp <;> ring_nf <;> simp only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] <;> ring
  have hspan : ∀ j, b j ∈ Submodule.span ℝ (range b) := fun j ↦ Submodule.subset_span ⟨j, rfl⟩
  have hv' : v = v 0 • b 0 + (√3 * v 1) • b 1 + (y₀ 1 * v 3) • b 2 + (√3 * y₀ 1 * v 4) • b 3 :=
    sub_eq_zero.1 hw0
  rw [hv']
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_ <;>
    exact Submodule.smul_mem _ _ (hspan _)

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

/-- `q_fix(y₀)` in coordinates, as an explicit function of `y₀` (`ihy_phaseCoords_qFix`). -/
noncomputable def ifp_gamma (y : ℝ) : Fin 9 → ℝ :=
  ![0, -y, 1 / y, 0, strongL₁ y * ((2 * y ^ 2 * (1 + 3 * y ^ 2))⁻¹ * (4 * √3 * y ^ 4)),
    strongL₁ y * ((2 * y ^ 2 * (1 + 3 * y ^ 2))⁻¹ * -(√3 * (1 + y ^ 2) * (3 * y ^ 2 - 1))),
    0, strongLR y * y ^ 2, strongLR y]

lemma ifp_gamma_contDiffAt {y : ℝ} (hy : 0 < y) : ContDiffAt ℝ 1 ifp_gamma y := by
  have h1 : y ≠ 0 := hy.ne'
  have h2 : 4 / (3 * y ^ 2 + 1) ≠ 0 := by positivity
  have h3 : 2 * y ^ 2 * (1 + 3 * y ^ 2) ≠ 0 := by positivity
  have h4 : 12 * √3 * y ^ 4 ≠ 0 := by positivity
  have h5 : 24 * y ^ 6 ≠ 0 := by positivity
  have h6 : 3 * y ^ 2 + 1 ≠ 0 := by positivity
  unfold ifp_gamma strongL₁ strongLR ellSw
  rw [contDiffAt_pi]
  intro i
  fin_cases i <;> dsimp <;> fun_prop (disch := assumption)

/-! ### Step 6: the implicit function theorem -/

/-- Near `q_oct`, the fixed points of `f⁴` on the section are the `q_fix(y₀)`. In coordinates
`(d, ξ)` on `N = ⋃_d N_d` (or with `X₁₀ = 1/y₀` as the parameter), `f⁴ - id` has an invertible
partial derivative `A⁴ - I` in `ξ` (by `iso_hyperbolic` with `θ ∈ {0, π/2, π}`), so its zero set
is a graph over the parameter (`HasStrictFDerivAt.implicitFunctionOfProdDomain`), which the
family `q_fix(y₀)` (`iso_poincareMap_qFix`) fills. -/
theorem iso_fixedPoints :
    ∃ V ∈ 𝓝 (iso_qFix (y₀ 1)), ∀ q ∈ V, iso_IsSectionPt q → iso_poincareMap^[4] q = q →
      ∃ y0 ∈ Ioo (1 / √3) 1, q = iso_qFix y0 := by
  obtain ⟨hy0, hy1⟩ := poly_y₀_mem (le_refl 1)
  have hy : 0 < y₀ 1 := poly_y0_pos hy0
  set y := y₀ 1 with hydef
  set p₀ := iso_phaseCoords (iso_qFix y) with hp₀
  set F := iso_poincareMapCoords with hFdef
  set L := fderiv ℝ F p₀ with hL
  set c := iso_sectionConstraints with hcdef
  set Dc := fderiv ℝ c p₀ with hDc
  have hγ : ∀ y', 0 < y' → iso_phaseCoords (iso_qFix y') = ifp_gamma y' :=
    fun y' h ↦ ihy_phaseCoords_qFix y' h
  have hp₀γ : p₀ = ifp_gamma y := hγ y hy
  have htr : ∀ y', 1 / √3 < y' → y' < 1 → (iso_qFix y').1.trace = 0 ∧
      (iso_qFix y').2.1.trace = 0 ∧ (iso_qFix y').2.2.trace = 0 := fun y' h0 h1 ↦
    ⟨(iso_qFix_isSectionPt y' h0 h1).1, (iso_qFix_isSectionPt y' h0 h1).2.1,
      (iso_qFix_isSectionPt y' h0 h1).2.2.1⟩
  have hFγ : ∀ y', 1 / √3 < y' → y' < 1 → ∀ n : ℕ,
      F^[n] (iso_phaseCoords (iso_qFix y')) = iso_phaseCoords (iso_qFix y') := by
    intro y' h0 h1 n
    obtain ⟨k1, k2, k3⟩ := htr y' h0 h1
    rw [ifp_coords_iterate n k1 k2 k3, Function.iterate_fixed (iso_poincareMap_qFix y' h0 h1)]
  -- the derivatives at `p₀`
  have hFp : F p₀ = p₀ := hFγ y hy0 hy1 1
  have hF4 : HasStrictFDerivAt (F^[4]) (L ^ 4) p₀ :=
    iso_poincareMapCoords_hasStrictFDerivAt.iterate hFp 4
  obtain ⟨hA, hB⟩ := ihy_qFix_den
  have hcC : ContDiffAt ℝ 1 c p₀ := ifp_constraints_contDiffAt hA hB
  have hc : HasStrictFDerivAt c Dc p₀ := hcC.hasStrictFDerivAt one_ne_zero
  -- `Ψ(v) = (c(v), F⁴(v) - v)` has an injective derivative at `p₀`
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
  -- the curve `γ = q_fix` in coordinates and `d(y₀) = det Λ₁(q_fix(y₀))`
  have hγC : ContDiffAt ℝ 1 ifp_gamma y := ifp_gamma_contDiffAt hy
  set γ' := deriv ifp_gamma y with hγ'
  have hγd : HasDerivAt ifp_gamma γ' y := (hγC.differentiableAt one_ne_zero).hasDerivAt
  have hγ'2 : γ' 2 = -(y ^ 2)⁻¹ := by
    have h1 := (hasDerivAt_pi.1 hγd) 2
    have h2 : HasDerivAt (fun y ↦ ifp_gamma y 2) (-(y ^ 2)⁻¹) y := by
      have e : (fun y ↦ ifp_gamma y 2) = fun y ↦ y⁻¹ := by funext y; simp [ifp_gamma]
      rw [e]; exact hasDerivAt_inv hy.ne'
    exact h1.unique h2
  have hIoo : Ioo (1 / √3) 1 ∈ 𝓝 y := Ioo_mem_nhds hy0 hy1
  have hcγ : ∀ᶠ y' in 𝓝 y, c (ifp_gamma y') = ![0, 0, 0, 0, (iso_qFix y').2.1.det] := by
    filter_upwards [hIoo] with y' hy'
    rw [← hγ y' (poly_y0_pos hy'.1)]
    exact ifp_constraints_of_section (iso_qFix_isSectionPt y' hy'.1 hy'.2)
  have hFγ' : ∀ᶠ y' in 𝓝 y, F^[4] (ifp_gamma y') = ifp_gamma y' := by
    filter_upwards [hIoo] with y' hy'
    rw [← hγ y' (poly_y0_pos hy'.1)]
    exact hFγ y' hy'.1 hy'.2 4
  have hc' : HasFDerivAt c Dc (ifp_gamma y) := hp₀γ ▸ hc.hasFDerivAt
  have hF4' : HasFDerivAt (F^[4]) (L ^ 4) (ifp_gamma y) := hp₀γ ▸ hF4.hasFDerivAt
  have hcγd : HasDerivAt (fun y' ↦ c (ifp_gamma y')) (Dc γ') y := hc'.comp_hasDerivAt y hγd
  have hFγd : HasDerivAt (fun y' ↦ F^[4] (ifp_gamma y')) ((L ^ 4) γ') y :=
    hF4'.comp_hasDerivAt y hγd
  have hDcγ : ∀ i : Fin 5, i ≠ 4 → Dc γ' i = 0 := by
    intro i hi
    refine ((hasDerivAt_pi.1 hcγd) i).unique ((hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq ?_)
    filter_upwards [hcγ] with y' hy'
    rw [hy']
    fin_cases i
    · rfl
    · rfl
    · rfl
    · rfl
    · exact absurd rfl hi
  have hLγ : (L ^ 4) γ' = γ' := hFγd.unique (hγd.congr_of_eventuallyEq hFγ')
  have hd0 : Dc γ' 4 ≠ 0 := by
    intro h4
    have hz : DΨ γ' = 0 := by
      simp only [hDΨ, ContinuousLinearMap.prod_apply, sub_apply,
        ContinuousLinearMap.id_apply, hLγ, sub_self, Prod.mk_eq_zero, and_true]
      funext i
      by_cases hi : i = 4
      · rw [hi, h4]; rfl
      · exact hDcγ i hi
    have h2 := congrFun (hDΨ0 γ' hz) 2
    rw [hγ'2, Pi.zero_apply, neg_eq_zero, inv_eq_zero] at h2
    exact (pow_pos hy 2).ne' h2
  set d : ℝ → ℝ := fun y' ↦ c (ifp_gamma y') 4 with hd
  have hdC : ContDiffAt ℝ 1 d y :=
    contDiffAt_pi.1 ((hp₀γ ▸ hcC : ContDiffAt ℝ 1 c (ifp_gamma y)).comp y hγC) 4
  have hdS : HasStrictDerivAt d (Dc γ' 4) y := by
    have h := hdC.hasStrictDerivAt one_ne_zero
    rwa [((hasDerivAt_pi.1 hcγd) 4).deriv] at h
  have hmap : Filter.map d (𝓝 y) = 𝓝 (d y) := HasStrictDerivAt.map_nhds_eq hdS hd0
  -- the neighbourhood
  set Y := Ioo (1 / √3) 1 ∩ ifp_gamma ⁻¹' W with hYdef
  have hY : Y ∈ 𝓝 y :=
    inter_mem hIoo (hγC.continuousAt.preimage_mem_nhds (by rw [← hp₀γ]; exact hW))
  have hdY : d '' Y ∈ 𝓝 (d y) := hmap ▸ image_mem_map hY
  have hc4 : ContinuousAt (fun v ↦ c v 4) p₀ :=
    (continuous_apply 4).continuousAt.comp hcC.continuousAt
  set V' := W ∩ (fun v ↦ c v 4) ⁻¹' (d '' Y) with hV'
  have hV'mem : V' ∈ 𝓝 p₀ :=
    inter_mem hW (hc4.preimage_mem_nhds (by simp only [hd, ← hp₀γ] at hdY; exact hdY))
  refine ⟨iso_phaseCoords ⁻¹' V',
    irt_continuous_phaseCoords.continuousAt.preimage_mem_nhds hV'mem, fun q hqV hsec hfix ↦ ?_⟩
  obtain ⟨hqW, y', ⟨hy'I, hy'W⟩, hdy'⟩ := hqV
  obtain ⟨k1, k2, k3, -⟩ := id hsec
  have hy'0 : 0 < y' := poly_y0_pos hy'I.1
  have hΨq : Ψ (iso_phaseCoords q) = Ψ (ifp_gamma y') := by
    have h4 : d y' = c (iso_phaseCoords q) 4 := hdy'
    simp only [hd, ← hγ y' hy'0, hcdef, ifp_constraints_of_section hsec,
      ifp_constraints_of_section (iso_qFix_isSectionPt y' hy'I.1 hy'I.2)] at h4
    simp only [hΨdef, hcdef]
    rw [ifp_coords_iterate 4 k1 k2 k3, hfix, sub_self, ← hγ y' hy'0, hFγ y' hy'I.1 hy'I.2 4,
      sub_self, ifp_constraints_of_section hsec,
      ifp_constraints_of_section (iso_qFix_isSectionPt y' hy'I.1 hy'I.2)]
    simp only [Matrix.cons_val] at h4
    rw [h4]
  have heq := hWinj hqW hy'W hΨq
  refine ⟨y', hy'I, ?_⟩
  obtain ⟨t1, t2, t3⟩ := htr y' hy'I.1 hy'I.2
  rw [← irt_ofCoords_coords k1 k2 k3, heq, ← hγ y' hy'0, irt_ofCoords_coords t1 t2 t3]

/-! ### Step 7: the final transversality condition -/

/-- If `A ∈ SL₂(ℝ)` and `A⁴ = -I` then `(tr A)² = 2`: by Cayley–Hamilton `A⁴ + I =
(t² - 2)(tA - I)`, `t = tr A`; if `t² ≠ 2` then `tA = I` and `t² = t(a + d) = 2` anyway. -/
theorem iso_trace_sq_of_pow_four (A : Mat2) (hdet : A.det = 1) (h4 : A ^ 4 = -1) :
    A.trace ^ 2 = 2 := by
  have hd : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by rw [← Matrix.det_fin_two]; exact hdet
  have h00 : (A ^ 4) 0 0 = -1 := by rw [h4]; simp
  have h11 : (A ^ 4) 1 1 = -1 := by rw [h4]; simp
  simp only [pow_succ, pow_zero, one_mul, Matrix.mul_apply, Fin.sum_univ_two] at h00 h11
  rw [Matrix.trace_fin_two]
  set a := A 0 0
  set b := A 0 1
  set c := A 1 0
  set d := A 1 1
  have e00 : ((a + d) ^ 2 - 2) * ((a + d) * a - 1) = 0 := by
    linear_combination h00 - (-3 * a ^ 2 - 3 * a * d - b * c - d ^ 2 + 1) * hd
  have e11 : ((a + d) ^ 2 - 2) * ((a + d) * d - 1) = 0 := by
    linear_combination h11 - (-a ^ 2 - 3 * a * d - b * c - 3 * d ^ 2 + 1) * hd
  by_contra hne
  have h2 : (a + d) ^ 2 - 2 ≠ 0 := sub_ne_zero.mpr hne
  have ha : (a + d) * a - 1 = 0 := (mul_eq_zero.mp e00).resolve_left h2
  have hd' : (a + d) * d - 1 = 0 := (mul_eq_zero.mp e11).resolve_left h2
  exact hne (by linear_combination ha + hd')

/-- The final transversality condition picks the octagon in the family: if the trajectory from
`q_fix(y₀)` with four switching intervals ends at `g(4 t_sw) = R`, then `y₀ = y_oct`
(`g(4t_sw) = h⁴R⁴` with `h = g_sw R⁻¹`, so `h⁴ = R⁻³ = -I`, `(tr h)² = 2`, `tr h = 4/(1 + 3y₀²)`;
the converse direction of Lemma 7.5.5 for `k = 1`). -/
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
