module

public import SmoothedPolygons.Ch3.ControlSets
public import SmoothedPolygons.Ch3.StateDynamics
public import Mathlib.Analysis.BoundedVariation
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Lie algebra dynamics (§3.4)

Elementary identities in `𝔰𝔩₂(ℝ)` (Lemma 3.4.1) and the control-dependent dynamics
`X' = [Z_u, X]/⟨Z_u, X⟩` (Theorem 3.4.2).
-/

@[expose] public section

namespace SmoothedPolygons

open MeasureTheory Matrix
open scoped Topology

/-- **Lemma 3.4.1** (`lem:sl2-lemmas`). For matrices in `𝔰𝔩₂(ℝ)`:
1. `⟨X, X⟩ = -2 det X`;
2. if `det(s_j, X s_j) = det(s_j, Y s_j)` for `j = 0, 1, 2` and a multi-point `s`, then `X = Y`;
3. `XY + YX = ⟨X, Y⟩ I₂`;
4. `⟨X, [Y, Z]⟩ = ⟨[X, Y], Z⟩`. -/
theorem lemma3_4_1 :
    (∀ X : Mat2, X.trace = 0 → traceForm X X = -2 * X.det) ∧
    (∀ X Y : Mat2, X.trace = 0 → Y.trace = 0 → ∀ s : ZMod 6 → Fin 2 → ℝ, IsMultiPoint s →
      (∀ j ∈ ({0, 1, 2} : Finset (ZMod 6)), det2 (s j) (X *ᵥ s j) = det2 (s j) (Y *ᵥ s j)) →
      X = Y) ∧
    (∀ X Y : Mat2, X.trace = 0 → Y.trace = 0 → X * Y + Y * X = traceForm X Y • (1 : Mat2)) ∧
    (∀ X Y Z : Mat2, X.trace = 0 → Y.trace = 0 → Z.trace = 0 →
      traceForm X (Y * Z - Z * Y) = traceForm (X * Y - Y * X) Z) := by
  refine ⟨fun X hX ↦ ?_, fun X Y hX hY s hs h ↦ ?_, fun X Y hX hY ↦ ?_,
    fun X Y Z _ _ _ ↦ ?_⟩
  · -- (1)
    rw [algA_eta_of_trace_eq_zero X hX]
    simp [traceForm, Matrix.trace_fin_two, Matrix.det_fin_two]
    ring
  · -- (2): `q(v) = det(v, (X - Y)v)` vanishes at `s₀, s₁, s₂ = s₁ - s₀`, hence so does its polar
    -- form on `s₀, s₁`; as `det(s₀, s₁) ≠ 0`, `q = 0`, and a traceless `X - Y` with `q = 0` is `0`.
    have e4 : s 4 = -s 1 := (hs 1).2.1
    have e024 : s 0 + s 2 + s 4 = 0 := (hs 0).1
    have hD : det2 (s 0) (s 1) = √3 / 2 := (hs 0).2.2
    have hs2 : s 2 = s 1 - s 0 := by
      rw [e4] at e024
      calc s 2 = s 1 - s 0 + (s 0 + s 2 + -s 1) := by abel
        _ = s 1 - s 0 := by rw [e024, add_zero]
    have h0 := h 0 (by simp)
    have h1 := h 1 (by simp)
    have h2 := h 2 (by simp)
    rw [hs2] at h2
    simp only [algA_det2_mulVec, Pi.sub_apply] at h0 h1 h2
    have hD0 : (s 0 0 * s 1 1 - s 0 1 * s 1 0) ^ 2 ≠ 0 := by
      rw [show s 0 0 * s 1 1 - s 0 1 * s 1 0 = det2 (s 0) (s 1) from rfl, hD]; positivity
    have hX11 : X 1 1 = -X 0 0 := by
      rw [Matrix.trace_fin_two] at hX; linear_combination hX
    have hY11 : Y 1 1 = -Y 0 0 := by
      rw [Matrix.trace_fin_two] at hY; linear_combination hY
    set p := s 0 0
    set q := s 0 1
    set r := s 1 0
    set w := s 1 1
    have hA : (X 1 0 - Y 1 0) * (p * w - q * r) ^ 2 = 0 := by
      linear_combination (w ^ 2 - w * q) * h0 + (q ^ 2 - w * q) * h1 + (w * q) * h2
    have hC : (X 0 1 - Y 0 1) * (p * w - q * r) ^ 2 = 0 := by
      linear_combination (-(r ^ 2 - r * p)) * h0 - (p ^ 2 - r * p) * h1 - (r * p) * h2
    have hB : ((X 1 1 - X 0 0) - (Y 1 1 - Y 0 0)) * (p * w - q * r) ^ 2 = 0 := by
      linear_combination (-2 * w * r + w * p + r * q) * h0 + (-2 * q * p + w * p + r * q) * h1 -
        (w * p + r * q) * h2
    have hA' := sub_eq_zero.1 ((mul_eq_zero.1 hA).resolve_right hD0)
    have hB' := (mul_eq_zero.1 hB).resolve_right hD0
    have hC' := sub_eq_zero.1 ((mul_eq_zero.1 hC).resolve_right hD0)
    rw [hX11, hY11] at hB'
    have ha : X 0 0 = Y 0 0 := by linear_combination (-1 / 2) * hB'
    ext i j
    fin_cases i <;> fin_cases j
    · exact ha
    · exact hC'
    · exact hA'
    · simp only [Fin.mk_one, Fin.isValue, hX11, hY11, ha]
  · -- (3)
    rw [algA_eta_of_trace_eq_zero X hX, algA_eta_of_trace_eq_zero Y hY]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [traceForm, Matrix.trace_fin_two] <;> ring
  · -- (4)
    simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.sub_apply]
    ring

/-! ### Lipschitz continuity of `X = g⁻¹g'` -/

/-- `f` is Lipschitz and bounded on `s`. -/
private def algA_LB (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  (∃ K, LipschitzOnWith K f s) ∧ ∃ M, ∀ x ∈ s, |f x| ≤ M

private lemma algA_LB_mul {f h : ℝ → ℝ} {s : Set ℝ} (hf : algA_LB f s) (hh : algA_LB h s) :
    algA_LB (fun x ↦ f x * h x) s := by
  obtain ⟨⟨Kf, hKf⟩, Mf, hMf⟩ := hf
  obtain ⟨⟨Kh, hKh⟩, Mh, hMh⟩ := hh
  refine ⟨⟨Real.toNNReal (max Mf 0 * Kh + max Mh 0 * Kf),
    LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_⟩, max Mf 0 * max Mh 0, fun x hx ↦ ?_⟩
  · rw [Real.coe_toNNReal _ (by positivity), Real.dist_eq]
    have h1 := hKf.dist_le_mul x hx y hy
    have h2 := hKh.dist_le_mul x hx y hy
    rw [Real.dist_eq] at h1 h2
    have e : f x * h x - f y * h y = f x * (h x - h y) + h y * (f x - f y) := by ring
    rw [e]
    calc _ ≤ |f x * (h x - h y)| + |h y * (f x - f y)| := abs_add_le _ _
      _ = |f x| * |h x - h y| + |h y| * |f x - f y| := by rw [abs_mul, abs_mul]
      _ ≤ max Mf 0 * (Kh * dist x y) + max Mh 0 * (Kf * dist x y) := by
          gcongr
          · exact (hMf x hx).trans (le_max_left _ _)
          · exact (hMh y hy).trans (le_max_left _ _)
      _ = _ := by ring
  · rw [abs_mul]
    exact mul_le_mul ((hMf x hx).trans (le_max_left _ _)) ((hMh x hx).trans (le_max_left _ _))
      (abs_nonneg _) (le_max_right _ _)

private lemma algA_LB_add {f h : ℝ → ℝ} {s : Set ℝ} (hf : algA_LB f s) (hh : algA_LB h s) :
    algA_LB (fun x ↦ f x + h x) s := by
  obtain ⟨⟨Kf, hKf⟩, Mf, hMf⟩ := hf
  obtain ⟨⟨Kh, hKh⟩, Mh, hMh⟩ := hh
  exact ⟨⟨_, hKf.add hKh⟩, Mf + Mh, fun x hx ↦ (abs_add_le _ _).trans (add_le_add (hMf x hx)
    (hMh x hx))⟩

private lemma algA_LB_neg {f : ℝ → ℝ} {s : Set ℝ} (hf : algA_LB f s) :
    algA_LB (fun x ↦ -f x) s := by
  obtain ⟨⟨Kf, hKf⟩, Mf, hMf⟩ := hf
  exact ⟨⟨_, hKf.neg⟩, Mf, fun x hx ↦ by rw [abs_neg]; exact hMf x hx⟩

/-- A function Lipschitz on `[0, T]` is bounded there. -/
private lemma algA_LB_of_lipschitzOnWith {f : ℝ → ℝ} {K : NNReal} {T : ℝ}
    (hf : LipschitzOnWith K f (Set.Icc 0 T)) : algA_LB f (Set.Icc 0 T) := by
  refine ⟨⟨K, hf⟩, |f 0| + K * T, fun τ hτ ↦ ?_⟩
  have hT : 0 ≤ T := hτ.1.trans hτ.2
  have h := hf.dist_le_mul τ hτ 0 ⟨le_rfl, hT⟩
  rw [Real.dist_eq, Real.dist_eq, sub_zero, abs_of_nonneg hτ.1] at h
  have h1 := abs_sub_abs_le_abs_sub (f τ) (f 0)
  have h2 : (K : ℝ) * τ ≤ K * T := mul_le_mul_of_nonneg_left hτ.2 K.2
  linarith

/-- `X = g⁻¹g'` is Lipschitz on `[0, t_f]` when `g'` is and `det g = 1`: on `[0, t_f]`,
`g⁻¹ = adj(g)`, the entries of `g'` are bounded and Lipschitz, and so are those of `g` (whose
derivative `g'` is bounded). -/
private lemma algA_lipschitzOnEntrywise_inv_mul {tf : ℝ} {g g' : ℝ → Mat2}
    (hg : ∀ t ∈ Set.Icc 0 tf, HasDerivWithinAtEntrywise g (g' t) (Set.Icc 0 tf) t)
    (hdet : ∀ t ∈ Set.Icc 0 tf, (g t).det = 1) (hLip : LipschitzOnEntrywise g' (Set.Icc 0 tf)) :
    LipschitzOnEntrywise (fun t ↦ (g t)⁻¹ * g' t) (Set.Icc 0 tf) := by
  have hg' : ∀ i j, algA_LB (fun t ↦ g' t i j) (Set.Icc 0 tf) := fun i j ↦ by
    obtain ⟨K, hK⟩ := hLip i j
    exact algA_LB_of_lipschitzOnWith hK
  have hgL : ∀ i j, algA_LB (fun t ↦ g t i j) (Set.Icc 0 tf) := fun i j ↦ by
    obtain ⟨-, M, hM⟩ := hg' i j
    have hL : LipschitzOnWith (Real.toNNReal M) (fun t ↦ g t i j) (Set.Icc 0 tf) :=
      (convex_Icc 0 tf).lipschitzOnWith_of_nnnorm_hasDerivWithin_le (fun t ht ↦ hg t ht i j)
        fun t ht ↦ by
          rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, Real.coe_toNNReal']
          exact (hM t ht).trans (le_max_left _ _)
    exact algA_LB_of_lipschitzOnWith hL
  have hadj : ∀ i k, algA_LB (fun t ↦ (g t).adjugate i k) (Set.Icc 0 tf) := by
    intro i k
    fin_cases i <;> fin_cases k <;> simp only [Matrix.adjugate_fin_two]
    · exact hgL 1 1
    · exact algA_LB_neg (hgL 0 1)
    · exact algA_LB_neg (hgL 1 0)
    · exact hgL 0 0
  intro i j
  have key : algA_LB (fun t ↦ ((g t).adjugate * g' t) i j) (Set.Icc 0 tf) := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    exact algA_LB_add (algA_LB_mul (hadj i 0) (hg' 0 j)) (algA_LB_mul (hadj i 1) (hg' 1 j))
  obtain ⟨⟨K, hK⟩, -⟩ := key
  refine ⟨K, fun x hx y hy ↦ ?_⟩
  have e : ∀ t ∈ Set.Icc 0 tf, ((g t)⁻¹ * g' t) i j = ((g t).adjugate * g' t) i j :=
    fun t ht ↦ by rw [Matrix.inv_def, hdet t ht, Ring.inverse_one, one_smul]
  simp only
  rw [e x hx, e y hy]
  exact hK hx hy

/-- **Theorem 3.4.2** (`thm:X-dynamics-sl2`). Let `g : [0, t_f] → SL₂(ℝ)` be `C¹` with Lipschitz
derivative, `X = g⁻¹g'` with `det X = 1` (the parameterization of Proposition 3.1.9), satisfying the
star inequalities and the curvature conditions `κ_j ≥ 0` almost everywhere, and let `u` be the
control variables (Definition 3.3.2). Then almost everywhere `X' = [Z_u, X]/⟨Z_u, X⟩`. -/
theorem theorem3_4_2 (tf : ℝ) (g g' : ℝ → Mat2)
    (hg : ∀ t ∈ Set.Icc 0 tf, HasDerivWithinAtEntrywise g (g' t) (Set.Icc 0 tf) t)
    (hdet : ∀ t ∈ Set.Icc 0 tf, (g t).det = 1) (hLip : LipschitzOnEntrywise g' (Set.Icc 0 tf))
    (X : ℝ → Mat2) (hX : ∀ t, X t = (g t)⁻¹ * g' t) (hX1 : ∀ t ∈ Set.Icc 0 tf, (X t).det = 1)
    (hstar : ∀ t ∈ Set.Icc 0 tf, 0 < ρ₀ (X t) ∧ 0 < ρ₁ (X t) ∧ 0 < ρ₂ (X t))
    (hcurv : ∀ᵐ t, t ∈ Set.Ioo 0 tf → ∀ j, 0 ≤ stateCurvature (X t) (derivEntrywise X t) j)
    (u : ℝ → Fin 3 → ℝ)
    (hu : ∀ t, u t = controlVariables (stateCurvature (X t) (derivEntrywise X t))) :
    ∀ᵐ t, t ∈ Set.Ioo 0 tf → HasDerivAtEntrywise X
      ((traceForm (controlMatrix (u t)) (X t))⁻¹ •
        (controlMatrix (u t) * X t - X t * controlMatrix (u t))) t := by
  rcases le_or_gt tf 0 with htf | htf
  · exact Filter.Eventually.of_forall fun t ht ↦ absurd (ht.1.trans ht.2) (not_lt.2 htf)
  have hXfun : X = fun s ↦ (g s)⁻¹ * g' s := funext hX
  have htrX : ∀ τ ∈ Set.Icc 0 tf, (X τ).trace = 0 := fun τ hτ ↦ by
    rw [hX]; exact algA_trace_inv_mul_eq_zero htf hg hdet τ hτ
  have hLipX : LipschitzOnEntrywise X (Set.Icc 0 tf) := by
    rw [hXfun]; exact algA_lipschitzOnEntrywise_inv_mul hg hdet hLip
  -- `X + X⁻¹X' ∈ 𝔰𝔩₂(ℝ)` almost everywhere (Corollary 3.1.11)
  have hY : ∀ᵐ t, t ∈ Set.Ioo 0 tf → (X t + (X t)⁻¹ * derivEntrywise X t).trace = 0 :=
    (corollary3_1_11 X 0 tf htf.le htrX (fun t ht ↦ by rw [hX1 t ht]; exact one_ne_zero)
      hLipX).1 ⟨1, hX1⟩
  -- `κ = κ₀ + κ₁ + κ₂ > 0` almost everywhere (Lemma 3.3.1)
  have hpos := lemma3_3_1 tf g g' hg hdet X hX hstar hcurv
  -- `X` is differentiable almost everywhere (Rademacher's theorem for `g'`)
  have hdiff : ∀ᵐ t, t ∈ Set.Ioo 0 tf → HasDerivAtEntrywise X (derivEntrywise X t) t := by
    have h : ∀ i j, ∀ᵐ t, t ∈ Set.Icc 0 tf →
        DifferentiableWithinAt ℝ (fun t ↦ g' t i j) (Set.Icc 0 tf) t := fun i j ↦ by
      obtain ⟨K, hK⟩ := hLip i j
      exact hK.ae_differentiableWithinAt_of_mem_real
    have h' : ∀ᵐ t, ∀ i j, t ∈ Set.Icc 0 tf →
        DifferentiableWithinAt ℝ (fun t ↦ g' t i j) (Set.Icc 0 tf) t := by
      simp only [Filter.eventually_all]
      exact h
    filter_upwards [h'] with t ht htI
    have hn : Set.Icc 0 tf ∈ 𝓝 t := Icc_mem_nhds htI.1 htI.2
    have hg't : HasDerivAtEntrywise g' (derivEntrywise g' t) t := fun i j ↦
      ((ht i j (Set.Ioo_subset_Icc_self htI)).differentiableAt hn).hasDerivAt
    have hgt : HasDerivAtEntrywise g (g' t) t :=
      (hg t (Set.Ioo_subset_Icc_self htI)).hasDerivAtEntrywise hn
    have hdet1 : IsUnit (g t).det := by rw [hdet t (Set.Ioo_subset_Icc_self htI)]; exact isUnit_one
    have hd := (hgt.inv hdet1).mul hg't
    rw [← hXfun] at hd
    exact hd.congr_deriv hd.derivEntrywise.symm
  filter_upwards [hdiff, hcurv, hpos, hY] with t hdt hκ hpos hY ht
  have htI : t ∈ Set.Icc 0 tf := Set.Ioo_subset_Icc_self ht
  obtain ⟨hl1, hl2, hl3, -⟩ := lemma3_4_1
  have hut := hu t
  set X₀ := X t with hX₀
  set X' := derivEntrywise X t with hX'
  set κ : Fin 3 → ℝ := stateCurvature X₀ X' with hκdef
  set Z := controlMatrix (u t) with hZ
  have hXtr : X₀.trace = 0 := htrX t htI
  have hdet1 : X₀.det = 1 := hX1 t htI
  have hX'tr : X'.trace = 0 := algA_trace_derivEntrywise_eq_zero (Icc_mem_nhds ht.1 ht.2) htrX
  -- `κ = κ₀ + κ₁ + κ₂ > 0` (the book writes `κ₁ + κ₂ + κ₃`, an index slip)
  have hκpos : 0 < κ 0 + κ 1 + κ 2 := by
    obtain ⟨j, hj⟩ := hpos ht
    have := hκ ht
    fin_cases j <;> simp at hj <;> linarith [this 0, this 1, this 2]
  -- `κ u_j = κ_j`, so `κ Z_u = Z_κ`
  have hκZ : (κ 0 + κ 1 + κ 2) • Z = controlMatrix κ := by
    rw [hZ, hut]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [controlMatrix, controlVariables] <;> field_simp
  -- `X + X⁻¹X' = κ Z_u` by Lemma 3.4.1(2), since both sides have curvatures `κ_j = κ u_j`
  -- (`eqn:def-Z0`). Lemma 3.4.1(2) is applied to the multi-point `s*`: the curvatures are given
  -- at `s₀*, s₂*, s₄* = -s₁*`, and `det(v, Mv)` is even in `v`.
  have hYZ : X₀ + X₀⁻¹ * X' = (κ 0 + κ 1 + κ 2) • Z := by
    rw [hκZ]
    have hspec := (controlMatrix_spec κ).2.1
    have hneg : ∀ (M : Mat2) (v : Fin 2 → ℝ), det2 (-v) (M *ᵥ -v) = det2 v (M *ᵥ v) := by
      intro M v; simp only [det2, Matrix.mulVec_neg, Pi.neg_apply]; ring
    refine hl2 _ _ (hY ht) (controlMatrix_spec κ).1 sixthRoot algA_isMultiPoint_sixthRoot ?_
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl
    · exact hspec 0
    · -- `s₁* = -s₄*`
      have e : sixthRoot 1 = -sixthRoot 4 := by
        have h4 : sixthRoot 4 = -sixthRoot 1 := (algA_isMultiPoint_sixthRoot 1).2.1
        rw [h4, neg_neg]
      rw [e, hneg, hneg]
      exact hspec 2
    · exact hspec 1
  -- `X' = X(κ Z_u - X)` (`eqn:X-orig`)
  have hXinv : X₀ * X₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ (by rw [hdet1]; exact isUnit_one)
  have hXorig : X' = X₀ * ((κ 0 + κ 1 + κ 2) • Z) - X₀ * X₀ := by
    rw [← hYZ, Matrix.mul_add, ← Matrix.mul_assoc, hXinv, Matrix.one_mul]
    abel
  -- taking traces, `κ ⟨X, Z_u⟩ = ⟨X, X⟩ = -2 det X = -2`
  have hXX : traceForm X₀ X₀ = -2 := by rw [hl1 X₀ hXtr, hdet1]; norm_num
  have hκtr : (κ 0 + κ 1 + κ 2) * traceForm X₀ Z = -2 := by
    have := congrArg Matrix.trace hXorig
    rw [hX'tr, Matrix.trace_sub, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul] at this
    simp only [traceForm] at hXX ⊢
    linarith
  have hZX : traceForm Z X₀ = traceForm X₀ Z := Matrix.trace_mul_comm _ _
  have hne : traceForm Z X₀ ≠ 0 := by
    intro h; rw [← hZX, h, mul_zero] at hκtr; norm_num at hκtr
  -- `P = Z_u/⟨Z_u, X⟩` has `⟨P, X⟩ = 1`
  set P := (traceForm Z X₀)⁻¹ • Z with hP
  have hPtr : P.trace = 0 := by rw [hP, Matrix.trace_smul, (controlMatrix_spec _).1, smul_zero]
  have hPX : traceForm P X₀ = 1 := by
    rw [hP, traceForm, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    exact inv_mul_cancel₀ hne
  -- `X² = -I` (Lemma 3.4.1(1),(3))
  have hXsq : X₀ * X₀ = -1 := by
    have h := hl3 X₀ X₀ hXtr hXtr
    rw [hXX, ← two_smul ℝ] at h
    have h' := congrArg (fun M : Mat2 ↦ (1 / 2 : ℝ) • M) h
    simp only [smul_smul] at h'
    norm_num at h'
    exact h'
  -- `-2XP = κ X Z_u`, as `κ = -2/⟨X, Z_u⟩`
  have h2XP : (-2 : ℝ) • (X₀ * P) = X₀ * ((κ 0 + κ 1 + κ 2) • Z) := by
    rw [hP, Matrix.mul_smul, Matrix.mul_smul, smul_smul]
    congr 1
    rw [hZX] at hne ⊢
    field_simp
    linarith [hκtr]
  -- `[P, X] = -2XP + (PX + XP) = -2XP + ⟨P, X⟩ I = -2XP + I = κ X Z_u - X² = X'`
  have hPX' : P * X₀ - X₀ * P = X' := by
    have h := hl3 P X₀ hPtr hXtr
    rw [hPX, one_smul] at h
    rw [hXorig, ← h2XP, hXsq, ← h]
    module
  have e : (traceForm Z X₀)⁻¹ • (Z * X₀ - X₀ * Z) = X' := by
    rw [← hPX', hP, Matrix.smul_mul, Matrix.mul_smul, smul_sub]
  rw [e]
  exact hdt ht

end SmoothedPolygons
