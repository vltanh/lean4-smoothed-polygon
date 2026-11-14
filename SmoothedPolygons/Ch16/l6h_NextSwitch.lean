module

public import SmoothedPolygons.Ch16.ClusterCoordinates
public import SmoothedPolygons.Ch7.Isolated.Return

/-!
# Theorem 16.4.1, helper: the next switching point along a chattering arc

Along a chattering arc into the singular locus (`IsChatteringArcInto`), if the `n`-th switching
point, rotated by `Ad_{R⁻ᵏ}`, is a phase point `q₀` at which

* `H(e₁) < H(e₂)` (so `e₁` does not maximize at `q₀`),
* along the `e₃`-flow from `q₀`, `H(e₃) < H(e₂)` right after `q₀` (so `e₃` cannot be used next),
* along the `e₂`-flow from `q₀`, `e₂` is the strict maximizer on `(0, t_sw(q₀))` and is beaten by
  `e₁` at times arbitrarily close after `t_sw(q₀)` (`eventually_isSwitch_reinSwitchTime`),

then the next switching time is `τ_n + t_sw(q₀)` and the next switching point, rotated by
`Ad_{R^{-(k+1)}}`, is `reinPoincare q₀` (`l6h_next_switch`). This is the claim "These functions
give the value of the Reinhardt–Poincaré map" (TeX 11838) in the form the proof of Theorem 16.4.1
needs: the extremal follows the vertex flow of its control between two switches
(`iso_arc_eq_vertexFlow`, here `l6h_arc` for `IsExtremalOn`), and the maximum condition decides the
control after `τ_n` and the time of the next switch.

The rotation of a solution by `R⁻ᵏ` (with the controls relabelled, `iso_rotControl`) is
`l6h_isExtremalOn_conj`, the analogue of `irt_conj` of Chapter 7 for solutions without boundary
conditions.
-/

@[expose] public section

namespace SmoothedPolygons

open Set Filter Topology MeasureTheory Matrix
open TriFuller

/-! ### Rotating a solution by `R⁻ᵏ` -/

/-- The state–costate system is invariant under conjugation by `R⁻ᵏ`, with the controls relabelled
by `iso_rotControl k` (`irt_conj` without the boundary conditions). -/
private lemma l6h_conj {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (h : IsStateCostateSolution T u g X Λ₁ ΛR lam) (k : ℕ) :
    IsStateCostateSolution T (fun t ↦ iso_rotControl k (u t)) (fun t ↦ R⁻¹ ^ k * g t * R ^ k)
      (fun t ↦ R⁻¹ ^ k * X t * R ^ k) (fun t ↦ R⁻¹ ^ k * Λ₁ t * R ^ k)
      (fun t ↦ R⁻¹ ^ k * ΛR t * R ^ k) lam := by
  obtain ⟨⟨hT, hum, husim, hst, hgI, hXI⟩, hlam, hpt, hI1, hIR, hmax⟩ := h
  have hC : R ^ k * R⁻¹ ^ k = 1 := poly_Rpow_mul_Rinvpow k
  have hZ : ∀ w, R⁻¹ ^ k * controlMatrix w * R ^ k = controlMatrix (iso_rotControl k w) :=
    ivf_conj_pow_controlMatrix k
  have hJ : R⁻¹ ^ k * J * R ^ k = J := poly_conj_pow_J k
  refine ⟨⟨hT, ?_, fun t ht ↦ ivf_rotControl_mem (husim t ht), fun t ht ↦ ⟨?_, ?_⟩, ?_, ?_⟩,
    hlam, fun t ht ↦ ?_, ?_, ?_, ?_⟩
  · refine measurable_pi_iff.2 fun i ↦ ?_
    exact (measurable_pi_apply _).comp hum
  · rw [poly_det_conj hC, (hst t ht).1]
  · exact poly_isStarState_conj_pow k (hst t ht).2
  · refine poly_isIntegralCurve_congr (irt_isIntegralCurve_conj hgI _ _) hT.le fun t _ ↦ ?_
    exact poly_conj_mul hC _ _
  · refine poly_isIntegralCurve_congr (irt_isIntegralCurve_conj hXI _ _) hT.le fun t _ ↦ ?_
    simp only
    rw [poly_conj_bracket hC, poly_controlP_conj hC (hZ (u t))]
  · obtain ⟨h1, h2, h3, h4⟩ := hpt t ht
    refine ⟨by rw [poly_trace_conj hC, h1], by rw [poly_trace_conj hC, h2],
      by rw [poly_traceForm_conj hC, h3], ?_⟩
    rcases h4 with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (ivf_conj_pow_ne_zero h k))
    · exact Or.inr (Or.inr (ivf_conj_pow_ne_zero h k))
  · refine poly_isIntegralCurve_congr (irt_isIntegralCurve_conj hI1 _ _) hT.le fun t _ ↦ ?_
    exact poly_conj_bracket hC _ _
  · refine poly_isIntegralCurve_congr (irt_isIntegralCurve_conj hIR _ _) hT.le fun t _ ↦ ?_
    exact poly_costateRHS_conj hC hJ (hZ (u t)) lam _ _ _
  · filter_upwards [hmax] with t ht hmem
    obtain ⟨hH, hle⟩ := ht hmem
    have hconj : ∀ w, hamiltonian lam (R⁻¹ ^ k * Λ₁ t * R ^ k) (R⁻¹ ^ k * ΛR t * R ^ k)
        (R⁻¹ ^ k * X t * R ^ k) (iso_rotControl k w) = hamiltonian lam (Λ₁ t) (ΛR t) (X t) w :=
      fun w ↦ poly_hamiltonian_conj hC hJ (hZ w) lam _ _ _
    refine ⟨by rw [hconj, hH], fun v hv ↦ ?_⟩
    obtain ⟨w, hw, rfl⟩ := ivf_exists_rotControl k hv
    rw [hconj, hconj]
    exact hle w hw

/-- **An extremal on `[a, b]`, rotated by `R⁻ᵏ`, is an extremal** with the controls relabelled
(`iso_rotControl k`); its phase points are `iso_adRinvPow k (phaseAt X Λ₁ Λ_R t)`. -/
theorem l6h_isExtremalOn_conj {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (h : IsExtremalOn a b u g X Λ₁ ΛR lam) (k : ℕ) :
    IsExtremalOn a b (fun t ↦ iso_rotControl k (u t)) (fun t ↦ R⁻¹ ^ k * g t * R ^ k)
      (fun t ↦ R⁻¹ ^ k * X t * R ^ k) (fun t ↦ R⁻¹ ^ k * Λ₁ t * R ^ k)
      (fun t ↦ R⁻¹ ^ k * ΛR t * R ^ k) lam :=
  l6h_conj h k

/-- The relabelled vertex: `iso_rotControl k e_j = e_{j + k}`. -/
theorem l6h_rotControl_vertex (k : ℕ) (j : Fin 3) :
    iso_rotControl k (vertex j) = vertex (j + ⟨k % 3, Nat.mod_lt _ (by norm_num)⟩) := by
  funext i
  simp only [iso_rotControl, vertex]
  by_cases hi : i = j + ⟨k % 3, Nat.mod_lt _ (by norm_num)⟩
  · rw [hi, add_sub_cancel_right, Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hi, Pi.single_eq_of_ne]
    intro h; apply hi; rw [← h, sub_add_cancel]

/-! ### Arcs with a constant vertex control -/

/-- On an arc where the control is the vertex `e_m` almost everywhere, a normalized solution of the
state–costate system is the vertex flow from its value at the start of the arc
(`iso_arc_eq_vertexFlow`, whose proof uses only the integral equations and the star states, for
solutions without boundary conditions). -/
private lemma l6h_arc_core {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    (h : IsStateCostateSolution T u g X Λ₁ ΛR (-1)) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ T) (m : Fin 3) (hu : ∀ᵐ t, t ∈ Ioo a b → u t = vertex m) :
    ∀ t ∈ Icc a b, (X t, Λ₁ t, ΛR t) = iso_vertexFlow m (X a, Λ₁ a, ΛR a) (t - a) := by
  obtain ⟨⟨-, -, -, hst, -, hXI⟩, -, -, hI1, hIR, -⟩ := h
  set q : iso_PhasePt := (X a, Λ₁ a, ΛR a) with hq
  have hsub : Icc a b ⊆ Icc 0 T := Icc_subset_Icc ha hb
  have hXc : ContinuousOn X (Icc a b) := (Matrix.continuousOn_of_eq_add_integral hXI).mono hsub
  have h1c : ContinuousOn Λ₁ (Icc a b) := (Matrix.continuousOn_of_eq_add_integral hI1).mono hsub
  have hRc : ContinuousOn ΛR (Icc a b) := (Matrix.continuousOn_of_eq_add_integral hIR).mono hsub
  have hstar : ∀ t ∈ Icc a b, IsStarState (X t) := fun t ht ↦ (hst t (hsub ht)).2
  have hvm : vertex m ∈ controlSimplex := poly_vertex_mem m
  set Y : ℝ → Mat2 := fun t ↦ iso_vfX m q (t - a) with hY
  set Y₁ : ℝ → Mat2 := fun t ↦ iso_vfΛ₁ m q (t - a) with hY₁
  set YR : ℝ → Mat2 := fun t ↦ iso_vfΛR m q (t - a) with hYR
  have hsc : ∀ {φ : ℝ → Mat2} {φ' : ℝ → Mat2}, (∀ s, HasDerivAtEntrywise φ (φ' s) s) →
      ∀ t, HasDerivAtEntrywise (fun s ↦ φ (s - a)) (φ' (t - a)) t := fun {φ φ'} hφ t ↦ by
    have := (hφ (t - a)).scomp (h := fun s ↦ s - a) ((hasDerivAt_id' t).sub_const a)
    rwa [one_smul] at this
  have hY' := hsc (ivf_vfX_hasDerivAt m q)
  have hY₁' := hsc (ivf_vfΛ₁_hasDerivAt m q)
  have hYR' := hsc (ivf_vfΛR_hasDerivAt m q)
  have hP : ∀ t, controlP (vertex m) (Y t) = controlP (vertex m) (X a) := fun t ↦
    ivf_controlP_vfX m q (t - a)
  have hwX : ContinuousOn (fun t ↦ controlP (vertex m) (X t) * X t -
      X t * controlP (vertex m) (X t)) (Icc a b) :=
    ((poly_controlP_continuousOn hXc hvm hstar).mul hXc).sub
      (hXc.mul (poly_controlP_continuousOn hXc hvm hstar))
  have hformX := ivf_integral_form_restrict_ae hXI ha hab hb hwX (by
    filter_upwards [hu] with t ht htI
    rw [ht htI])
  have hXd := fun t (ht : t ∈ Icc a b) ↦
    Matrix.hasDerivWithinAtEntrywise_of_eq_add_integral hformX ht (hwX t ht)
  have hconst := lemma7_1_1 _ X _ _ hXd
  have hPX : ∀ t ∈ Icc a b, controlP (vertex m) (X t) = controlP (vertex m) (X a) := by
    intro t ht
    unfold controlP
    rw [poly_traceForm_comm _ (X t), hconst t ht, poly_traceForm_comm (X _)]
  have hXY : EqOn X Y (Icc a b) := by
    refine Matrix.ODE_solution_unique_of_bound_Icc
      (G := fun _ M ↦ controlP (vertex m) (X a) * M - M * controlP (vertex m) (X a))
      (K := 4 * ∑ k, ∑ l, |controlP (vertex m) (X a) k l|)
      (fun _ _ P Q k l ↦ ?_) hXc (fun t ht ↦ ?_)
      (ivf_continuous_of_hasDerivAt hY').continuousOn (fun t _ ↦ ?_) ?_
    · rw [← Matrix.sub_apply, show ∀ P0 : Mat2, P0 * P - P * P0 - (P0 * Q - Q * P0) =
        P0 * (P - Q) - (P - Q) * P0 from fun P0 ↦ by noncomm_ring]
      simpa only [Matrix.sub_apply] using poly_abs_bracket_le _ (P - Q) k l
    · have := hXd t (Ico_subset_Icc_self ht)
      rwa [hPX t (Ico_subset_Icc_self ht)] at this
    · have := (hY' t).hasDerivWithinAtEntrywise (s := Icc a b)
      rwa [← hP t]
    · simp only [hY, sub_self]
      exact (congrArg Prod.fst (ivf_vertexFlow_zero m q)).symm
  have hw1 : ContinuousOn (fun t ↦ Λ₁ t * X t - X t * Λ₁ t) (Icc a b) :=
    (h1c.mul hXc).sub (hXc.mul h1c)
  have hform1 := poly_integral_form_restrict hI1 ha hab hb hw1 fun _ _ ↦ rfl
  have h1Y : EqOn Λ₁ Y₁ (Icc a b) := by
    obtain ⟨K, hK⟩ := ivf_lax_lipschitz isCompact_Icc hXc
    refine Matrix.ODE_solution_unique_of_bound_Icc (G := fun t M ↦ M * X t - X t * M) (K := K)
      (fun t ht P Q k l ↦ hK t (Ico_subset_Icc_self ht) P Q k l) h1c
      (fun t ht ↦ Matrix.hasDerivWithinAtEntrywise_of_eq_add_integral hform1
        (Ico_subset_Icc_self ht) (hw1 t (Ico_subset_Icc_self ht)))
      (ivf_continuous_of_hasDerivAt hY₁').continuousOn (fun t ht ↦ ?_) ?_
    · have := (hY₁' t).hasDerivWithinAtEntrywise (s := Icc a b)
      rwa [show iso_vfX m q (t - a) = X t from (hXY (Ico_subset_Icc_self ht)).symm] at this
    · simp only [hY₁, sub_self]
      exact (congrArg (fun p : iso_PhasePt ↦ p.2.1) (ivf_vertexFlow_zero m q)).symm
  have hwR : ContinuousOn (fun t ↦ costateRHS (-1) (Λ₁ t) (ΛR t) (X t) (vertex m)) (Icc a b) :=
    poly_costateRHS_continuousOn (-1) hvm h1c hRc hXc hstar
  have hformR := ivf_integral_form_restrict_ae hIR ha hab hb hwR (by
    filter_upwards [hu] with t ht htI
    rw [ht htI]
    rfl)
  have hRY : EqOn ΛR YR (Icc a b) := by
    obtain ⟨K, hK⟩ := ivf_costateRHS_lipschitz isCompact_Icc hXc (controlP (vertex m) (X a))
    refine Matrix.ODE_solution_unique_of_bound_Icc
      (G := fun t M ↦ costateRHS (-1) (Λ₁ t) M (X t) (vertex m)) (K := K)
      (fun t ht P Q k l ↦ hK t (Ico_subset_Icc_self ht) _ _ _ (hPX t (Ico_subset_Icc_self ht))
        P Q k l) hRc
      (fun t ht ↦ Matrix.hasDerivWithinAtEntrywise_of_eq_add_integral hformR
        (Ico_subset_Icc_self ht) (hwR t (Ico_subset_Icc_self ht)))
      (ivf_continuous_of_hasDerivAt hYR').continuousOn (fun t ht ↦ ?_) ?_
    · have := (hYR' t).hasDerivWithinAtEntrywise (s := Icc a b)
      rwa [show iso_vfX m q (t - a) = X t from (hXY (Ico_subset_Icc_self ht)).symm,
        show iso_vfΛ₁ m q (t - a) = Λ₁ t from (h1Y (Ico_subset_Icc_self ht)).symm] at this
    · simp only [hYR, sub_self]
      exact (congrArg (fun p : iso_PhasePt ↦ p.2.2) (ivf_vertexFlow_zero m q)).symm
  intro t ht
  rw [hXY ht, h1Y ht, hRY ht]
  rfl

/-- **An extremal arc with a constant vertex control is the vertex flow** from its initial point
(`iso_arc_eq_vertexFlow` for `IsExtremalOn`). -/
theorem l6h_arc {α β : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    (h : IsExtremalOn α β u g X Λ₁ ΛR (-1)) (m : Fin 3)
    (hu : ∀ᵐ t, t ∈ Ioo α β → u t = vertex m) :
    ∀ t ∈ Icc α β, phaseAt X Λ₁ ΛR t = iso_vertexFlow m (phaseAt X Λ₁ ΛR α) (t - α) := by
  have hab : 0 ≤ β - α := by have := h.1.1; linarith
  have hu' : ∀ᵐ t, t ∈ Ioo 0 (β - α) → u (α + t) = vertex m := by
    have hq := (MeasureTheory.measurePreserving_add_left MeasureTheory.volume
      α).quasiMeasurePreserving.ae hu
    filter_upwards [hq] with t ht htI
    exact ht ⟨by linarith [htI.1], by linarith [htI.2]⟩
  have := l6h_arc_core h le_rfl hab le_rfl m hu'
  intro t ht
  have h' := this (t - α) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  simp only [add_sub_cancel, add_zero, sub_zero] at h'
  exact h'

/-! ### Almost-everywhere helpers (as in `SmoothedPolygons/Ch16/RescaledDynamics.lean`) -/

theorem l6h_vertex_inj {i j : Fin 3} (h : vertex i = vertex j) : i = j := by
  by_contra hij
  have := congrFun h i
  simp [vertex, hij] at this

/-- A property holding almost everywhere on a nonempty open interval holds at some point of it. -/
theorem l6h_exists_mem_of_ae {P : ℝ → Prop} {c d : ℝ} (hcd : c < d)
    (h : ∀ᵐ t, t ∈ Ioo c d → P t) : ∃ t ∈ Ioo c d, P t := by
  by_contra hcon
  push Not at hcon
  have h0 : volume (Ioo c d) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [h] with t ht hmem
    exact hcon t hmem (ht hmem)
  rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at h0
  linarith

/-- A function continuous on `[a, b]` satisfying a closed condition almost everywhere on
`(p, q) ⊆ [a, b]` satisfies it on `[p, q]`. -/
theorem l6h_mem_of_ae {f : ℝ → ℝ} {C : Set ℝ} (hC : IsClosed C) {a b p q τ : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hpq : p < q) (hsub : Icc p q ⊆ Icc a b)
    (hτ : τ ∈ Icc p q) (hae : ∀ᵐ t, t ∈ Ioo p q → f t ∈ C) : f τ ∈ C := by
  have hD : IsClosed (Icc p q ∩ f ⁻¹' C) :=
    (hf.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc hC
  have hsub2 : Ioo p q ⊆ Icc p q ∩ f ⁻¹' C := by
    intro t ht
    by_contra hn
    have hopen : IsOpen (Ioo p q \ (Icc p q ∩ f ⁻¹' C)) := isOpen_Ioo.sdiff hD
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hopen t ⟨ht, hn⟩
    have hnull : ∀ᵐ s, s ∉ Metric.ball t δ := by
      filter_upwards [hae] with s hs hsb
      have h1 := hball hsb
      exact h1.2 ⟨Ioo_subset_Icc_self h1.1, hs h1.1⟩
    have h0 := MeasureTheory.measure_eq_zero_iff_ae_notMem.2 hnull
    rw [Real.volume_ball] at h0
    simp only [ENNReal.ofReal_eq_zero] at h0
    linarith
  have hcl : closure (Ioo p q) ⊆ Icc p q ∩ f ⁻¹' C := closure_minimal hsub2 hD
  rw [closure_Ioo hpq.ne] at hcl
  exact (hcl hτ).2

/-- The Hamiltonians of the vertices are continuous along an extremal. -/
theorem l6h_continuousOn_phaseHam {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    (hext : IsExtremalOn a b u g X Λ₁ ΛR (-1)) (k : Fin 3) :
    ContinuousOn (fun t ↦ phaseHam (phaseAt X Λ₁ ΛR t) (vertex k)) (Icc a b) := by
  have hc := hext.continuousOn_lift
  have hΛ₁ : ContinuousOn Λ₁ (Icc a b) := (continuous_fst.comp continuous_snd).comp_continuousOn hc
  have hX : ContinuousOn X (Icc a b) :=
    (continuous_fst.comp (continuous_snd.comp continuous_snd)).comp_continuousOn hc
  have hΛR : ContinuousOn ΛR (Icc a b) :=
    (continuous_snd.comp (continuous_snd.comp continuous_snd)).comp_continuousOn hc
  have htr : Continuous fun M : Mat2 ↦ M.trace := continuous_id.matrix_trace
  have hne : ∀ t ∈ Icc a b, traceForm (X t) (controlMatrix (vertex k)) ≠ 0 := by
    intro t ht
    have hst := (hext.1.2.2.2.1 (t - a) ⟨by linarith [ht.1], by linarith [ht.2]⟩).2
    simp only [add_sub_cancel] at hst
    rw [poly_traceForm_comm]
    exact (poly_traceForm_neg (poly_vertex_mem k) hst).ne
  exact (htr.comp_continuousOn ((hΛ₁.sub continuousOn_const).mul hX)).sub
    ((htr.comp_continuousOn (hΛR.mul continuousOn_const)).div
      (htr.comp_continuousOn (hX.mul continuousOn_const)) hne)

/-- The maximum condition and `H = 0` of an extremal on `[a, b]`, in the original time. -/
theorem l6h_max {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    (hext : IsExtremalOn a b u g X Λ₁ ΛR (-1)) :
    ∀ᵐ t, t ∈ Ioo a b → phaseHam (phaseAt X Λ₁ ΛR t) (u t) = 0 ∧
      ∀ v ∈ controlSimplex,
        phaseHam (phaseAt X Λ₁ ΛR t) v ≤ phaseHam (phaseAt X Λ₁ ΛR t) (u t) := by
  have hq := (MeasureTheory.measurePreserving_add_left MeasureTheory.volume
    (-a)).quasiMeasurePreserving.ae hext.2.2.2.2.2
  filter_upwards [hq] with s hs hsI
  have := hs ⟨by linarith [hsI.1], by linarith [hsI.2]⟩
  simpa [phaseHam, phaseAt] using this

/-- **At a switching time the two adjacent vertices maximize the Hamiltonian, with value `0`**
(`l6f_switch` of `SmoothedPolygons/Ch16/RescaledDynamics.lean`, private there): the maximum
condition and `H = 0` almost everywhere on each side, and continuity along the lift. -/
theorem l6h_switch {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    (hext : IsExtremalOn a b u g X Λ₁ ΛR (-1)) {τ : ℝ} (hτ : τ ∈ Ioo a b)
    (hsw : IsSwitchingTime u τ) :
    ∃ i j : Fin 3, i ≠ j ∧ (∀ k, phaseHam (phaseAt X Λ₁ ΛR τ) (vertex k) ≤ 0) ∧
      phaseHam (phaseAt X Λ₁ ΛR τ) (vertex i) = 0 ∧
      phaseHam (phaseAt X Λ₁ ΛR τ) (vertex j) = 0 := by
  obtain ⟨i, j, hij, ε, hε, hl, hr⟩ := hsw
  have hφ := l6h_continuousOn_phaseHam hext
  have hmax := l6h_max hext
  have key : ∀ {p q : ℝ} {m : Fin 3}, p < q → Icc p q ⊆ Icc a b → τ ∈ Icc p q →
      (∀ᵐ t, t ∈ Ioo p q → u t = vertex m) → Ioo p q ⊆ Ioo a b →
      (∀ k, phaseHam (phaseAt X Λ₁ ΛR τ) (vertex k) ≤ 0) ∧
        phaseHam (phaseAt X Λ₁ ΛR τ) (vertex m) = 0 := by
    intro p q m hpq hsub hτpq hu hsub'
    have hae : ∀ᵐ t, t ∈ Ioo p q → phaseHam (phaseAt X Λ₁ ΛR t) (vertex m) = 0 ∧
        ∀ k, phaseHam (phaseAt X Λ₁ ΛR t) (vertex k) ≤ 0 := by
      filter_upwards [hmax, hu] with t h1 h2 ht
      obtain ⟨e1, e2⟩ := h1 (hsub' ht)
      rw [h2 ht] at e1 e2
      exact ⟨e1, fun k ↦ (e2 (vertex k) (poly_vertex_mem k)).trans e1.le⟩
    refine ⟨fun k ↦ l6h_mem_of_ae (f := fun t ↦ phaseHam (phaseAt X Λ₁ ΛR t) (vertex k))
      isClosed_Iic (hφ k) hpq hsub hτpq ?_,
      l6h_mem_of_ae (f := fun t ↦ phaseHam (phaseAt X Λ₁ ΛR t) (vertex m))
        isClosed_singleton (hφ m) hpq hsub hτpq ?_⟩
    · filter_upwards [hae] with t ht ht' using (ht ht').2 k
    · filter_upwards [hae] with t ht ht' using (ht ht').1
  have hp : max a (τ - ε) < τ := max_lt hτ.1 (by linarith)
  have hq : τ < min b (τ + ε) := lt_min hτ.2 (by linarith)
  obtain ⟨hle, hi⟩ := key hp (Icc_subset_Icc (le_max_left _ _) hτ.2.le) ⟨hp.le, le_rfl⟩
    (by filter_upwards [hl] with t ht ht' using ht ⟨lt_of_le_of_lt (le_max_right _ _) ht'.1, ht'.2⟩)
    (fun t ht ↦ ⟨lt_of_le_of_lt (le_max_left _ _) ht.1, ht.2.trans hτ.2⟩)
  obtain ⟨-, hj⟩ := key hq (Icc_subset_Icc hτ.1.le (min_le_left _ _)) ⟨le_rfl, hq.le⟩
    (by filter_upwards [hr] with t ht ht' using ht ⟨ht'.1, lt_of_lt_of_le ht'.2 (min_le_right _ _)⟩)
    (fun t ht ↦ ⟨hτ.1.trans ht.1, lt_of_lt_of_le ht.2 (min_le_left _ _)⟩)
  exact ⟨i, j, hij, hle, hi, hj⟩

/-! ### Between two switching times the control is one vertex -/

/-- A time of `(α, β)` that is not a switching time of a finitely bang-bang control has a
neighbourhood on which the control is one vertex (`l3m_local_vertex` of
`SmoothedPolygons/Ch16/MahlerFirst.lean`, private there). -/
private lemma l6h_local_vertex {u : ℝ → Fin 3 → ℝ} {α β t : ℝ} (hbb : IsFiniteBangBang α β u)
    (ht : t ∈ Ioo α β) (hsw : ¬ IsSwitchingTime u t) :
    ∃ i : Fin 3, ∃ η > 0, ∀ᵐ τ, τ ∈ Ioo (t - η) (t + η) → u τ = vertex i := by
  obtain ⟨S, hS⟩ := hbb
  have hfin : ((S.erase t : Finset ℝ) : Set ℝ)ᶜ ∈ 𝓝 t :=
    (S.erase t).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)
  obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.mem_nhds_iff.1 hfin
  set ρ := min ρ₀ (min (t - α) (β - t)) with hρ
  have hρ1 : ρ ≤ ρ₀ := min_le_left _ _
  have hρ2 : ρ ≤ t - α := (min_le_right _ _).trans (min_le_left _ _)
  have hρ3 : ρ ≤ β - t := (min_le_right _ _).trans (min_le_right _ _)
  have hρpos : 0 < ρ := lt_min hρ₀ (lt_min (by linarith [ht.1]) (by linarith [ht.2]))
  have hloc : ∀ s ∈ Ioo (t - ρ) (t + ρ), s ≠ t →
      ∃ i : Fin 3, ∃ η > 0, ∀ᵐ τ, τ ∈ Ioo (s - η) (s + η) → u τ = vertex i := by
    intro s hs hst
    refine hS s ⟨by linarith [hs.1], by linarith [hs.2]⟩ fun hsS ↦ ?_
    have hsb : s ∈ Metric.ball t ρ₀ := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hs.1, hs.2]
    exact hball hsb (by simp [hsS, hst])
  obtain ⟨i, hi⟩ := exists_ae_eq_vertex_of_locally (α := t - ρ) (β := t) fun s hs ↦
    hloc s ⟨hs.1, by linarith [hs.2]⟩ hs.2.ne
  obtain ⟨j, hj⟩ := exists_ae_eq_vertex_of_locally (α := t) (β := t + ρ) fun s hs ↦
    hloc s ⟨by linarith [hs.1], hs.2⟩ hs.1.ne'
  obtain rfl : i = j := by
    by_contra hij
    exact hsw ⟨i, j, hij, ρ, hρpos, hi, hj⟩
  refine ⟨i, ρ, hρpos, ?_⟩
  have hne : ∀ᵐ τ : ℝ, τ ≠ t := by
    rw [ae_iff]
    simp
  filter_upwards [hi, hj, hne] with τ h1 h2 h3 hτ
  rcases lt_or_gt_of_ne h3 with h | h
  · exact h1 ⟨hτ.1, h⟩
  · exact h2 ⟨h, hτ.2⟩

/-- **Between two consecutive switching times the control is one vertex** (almost everywhere):
no time of `(τ n, τ (n + 1))` is a switching time, and the control is locally a vertex there. -/
theorem l6h_ae_vertex_between {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    {τ : ℕ → ℝ} (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) (n : ℕ) :
    ∃ j : Fin 3, ∀ᵐ t, t ∈ Ioo (τ n) (τ (n + 1)) → u t = vertex j := by
  obtain ⟨-, -, -, hbb, hmono, hτI, -, hsw⟩ := h
  have hn := hτI n
  have hn1 := hτI (n + 1)
  refine exists_ae_eq_vertex_of_locally fun t ht ↦ ?_
  have hnot : ¬ IsSwitchingTime u t := by
    intro hs
    obtain ⟨m, hm⟩ := (hsw t ⟨hn.1.trans ht.1, ht.2.trans hn1.2⟩).1 hs
    have h1 : n < m := hmono.lt_iff_lt.1 (hm ▸ ht.1)
    have h2 : m < n + 1 := hmono.lt_iff_lt.1 (hm ▸ ht.2)
    omega
  exact l6h_local_vertex (hbb ((a + τ n) / 2) ((τ (n + 1) + b) / 2) (by linarith [hn.1])
    (by linarith [hn1.2])) ⟨by linarith [hn.1, ht.1], by linarith [hn1.2, ht.2]⟩ hnot

/-! ### The next switching point -/

/-- **The next switching point** (module docstring): if the `n`-th switching point, rotated by
`Ad_{R⁻ᵏ}`, is `q₀`, where `e₁` is strictly below `e₂`, the `e₃`-flow has `H(e₃) < H(e₂)` right
after `q₀`, and the `e₂`-flow has the switching structure of `eventually_isSwitch_reinSwitchTime`,
then the `(n + 1)`-st switching point, rotated by `Ad_{R^{-(k+1)}}`, is `reinPoincare q₀`. -/
theorem l6h_next_switch {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {τ : ℕ → ℝ}
    (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) (n k : ℕ) {q₀ : iso_PhasePt}
    (hq : iso_adRinvPow k (phaseAt X Λ₁ ΛR (τ n)) = q₀)
    (h0 : phaseHam q₀ (vertex 0) < phaseHam q₀ (vertex 1))
    (h2 : ∃ ε > 0, ∀ t ∈ Ioo 0 ε,
      phaseHam (iso_vertexFlow 2 q₀ t) (vertex 2) < phaseHam (iso_vertexFlow 2 q₀ t) (vertex 1))
    (hpos : 0 < reinSwitchTime q₀)
    (hmax : ∀ t ∈ Ioo 0 (reinSwitchTime q₀), ∀ j : Fin 3, j ≠ 1 →
      phaseHam (iso_vertexFlow 1 q₀ t) (vertex j) < phaseHam (iso_vertexFlow 1 q₀ t) (vertex 1))
    (hbeat : ∀ ε > 0, ∃ t ∈ Ioo (reinSwitchTime q₀) (reinSwitchTime q₀ + ε),
      phaseHam (iso_vertexFlow 1 q₀ t) (vertex 1) < phaseHam (iso_vertexFlow 1 q₀ t) (vertex 0)) :
    iso_adRinvPow (k + 1) (phaseAt X Λ₁ ΛR (τ (n + 1))) = reinPoincare q₀ := by
  have hext := h.1
  obtain ⟨hmono, hτI, -, hsw⟩ := h.2.2.2.2
  have hext' := l6h_isExtremalOn_conj hext k
  set u' : ℝ → Fin 3 → ℝ := fun t ↦ iso_rotControl k (u t) with hu'
  set X' : ℝ → Mat2 := fun t ↦ R⁻¹ ^ k * X t * R ^ k with hX'
  set L' : ℝ → Mat2 := fun t ↦ R⁻¹ ^ k * Λ₁ t * R ^ k with hL'
  set Q' : ℝ → Mat2 := fun t ↦ R⁻¹ ^ k * ΛR t * R ^ k with hQ'
  have hQ : ∀ t, phaseAt X' L' Q' t = iso_adRinvPow k (phaseAt X Λ₁ ΛR t) := fun t ↦ rfl
  have hn := hτI n
  have hn1 := hτI (n + 1)
  have hlt : τ n < τ (n + 1) := hmono (Nat.lt_succ_self n)
  set kk : Fin 3 := ⟨k % 3, Nat.mod_lt _ (by norm_num)⟩ with hkk
  have hcont := l6h_continuousOn_phaseHam hext'
  have hM := l6h_max hext'
  obtain ⟨j, hj⟩ := l6h_ae_vertex_between h n
  have hj' : ∀ᵐ t, t ∈ Ioo (τ n) (τ (n + 1)) → u' t = vertex (j + kk) := by
    filter_upwards [hj] with t ht htI
    simp only [hu', ht htI, l6h_rotControl_vertex]
    rfl
  have harc := l6h_arc (hext'.mono hn.1.le hlt hn1.2.le) (j + kk) hj'
  rw [hQ, hq] at harc
  -- the maximum condition on `(τ n, τ (n + 1))`, with the control `e_{j + k}`
  have hMj : ∀ᵐ t, t ∈ Ioo (τ n) (τ (n + 1)) → ∀ i : Fin 3,
      phaseHam (phaseAt X' L' Q' t) (vertex i) ≤
        phaseHam (phaseAt X' L' Q' t) (vertex (j + kk)) := by
    filter_upwards [hM, hj'] with t h1 h2 htI i
    have h1 := (h1 ⟨hn.1.trans htI.1, htI.2.trans hn1.2⟩).2 (vertex i) (poly_vertex_mem i)
    rwa [h2 htI] at h1
  have hsubn : Icc (τ n) (τ (n + 1)) ⊆ Icc a b := Icc_subset_Icc hn.1.le hn1.2.le
  -- (i) the control after `τ n` is not `e₁`
  have hj0 : j + kk ≠ 0 := by
    intro hj0
    have := l6h_mem_of_ae (C := Ici 0) isClosed_Ici
      ((hcont 0).sub (hcont 1)) hlt hsubn ⟨le_rfl, hlt.le⟩ (by
        filter_upwards [hMj] with t ht htI
        have := ht htI 1
        rw [hj0] at this
        exact sub_nonneg.2 this)
    simp only [mem_Ici, Pi.sub_apply, sub_nonneg] at this
    rw [hQ, hq] at this
    linarith
  -- (ii) the control after `τ n` is not `e₃`
  have hj2 : j + kk ≠ 2 := by
    intro hj2
    obtain ⟨ε, hε, hε2⟩ := h2
    set δ := min ε (τ (n + 1) - τ n) with hδ
    have hδ0 : 0 < δ := lt_min hε (by linarith)
    obtain ⟨t, ht, hft⟩ := l6h_exists_mem_of_ae (by linarith : τ n < τ n + δ) (by
      filter_upwards [hMj] with t ht htI
      exact ht ⟨htI.1, htI.2.trans_le (by linarith [min_le_right ε (τ (n + 1) - τ n)])⟩ 1)
    have htI : t ∈ Icc (τ n) (τ (n + 1)) :=
      ⟨ht.1.le, ht.2.le.trans (by linarith [min_le_right ε (τ (n + 1) - τ n)])⟩
    rw [harc t htI, hj2] at hft
    have := hε2 (t - τ n) ⟨by linarith [ht.1], by linarith [ht.2, min_le_left ε (τ (n + 1) - τ n)]⟩
    linarith
  have hj1 : j + kk = 1 := by
    have := (j + kk).isLt
    have h0' : (j + kk).val ≠ 0 := fun h' ↦ hj0 (Fin.ext h')
    have h2' : (j + kk).val ≠ 2 := fun h' ↦ hj2 (Fin.ext h')
    exact Fin.ext (by omega)
  rw [hj1] at harc hMj
  set T := reinSwitchTime q₀ with hT
  -- (iv) the next switch is not later than `t_sw`
  have hle : τ (n + 1) - τ n ≤ T := by
    by_contra hgt
    push Not at hgt
    obtain ⟨t, ht, hbt⟩ := hbeat (τ (n + 1) - τ n - T) (by linarith)
    have hs : τ n + t ∈ Icc (τ n) (τ (n + 1)) :=
      ⟨by linarith [ht.1, hpos], by linarith [ht.2]⟩
    have := l6h_mem_of_ae (C := Iic 0) isClosed_Iic ((hcont 0).sub (hcont 1)) hlt hsubn hs (by
      filter_upwards [hMj] with t' ht' ht'I
      exact sub_nonpos.2 (ht' ht'I 0))
    simp only [mem_Iic, Pi.sub_apply, sub_nonpos] at this
    rw [harc _ hs, add_sub_cancel_left] at this
    linarith
  -- (v) the next switch is not earlier than `t_sw`
  have hge : T ≤ τ (n + 1) - τ n := by
    by_contra hlt'
    push Not at hlt'
    obtain ⟨i₁, j₁, hij, ε₁, hε₁, hl, hr⟩ :=
      (hsw (τ (n + 1)) hn1).2 ⟨n + 1, rfl⟩
    -- the vertex on the left of `τ (n + 1)` is `e_j`
    have hi₁ : i₁ = j := by
      set c := max (τ (n + 1) - ε₁) (τ n) with hc
      have hc1 : c < τ (n + 1) := max_lt (by linarith) hlt
      obtain ⟨t, -, h1, h2⟩ := l6h_exists_mem_of_ae
        (P := fun t ↦ u t = vertex i₁ ∧ u t = vertex j) hc1 (by
          filter_upwards [hl, hj] with t h1 h2 htI
          exact ⟨h1 ⟨lt_of_le_of_lt (le_max_left _ _) htI.1, htI.2⟩,
            h2 ⟨lt_of_le_of_lt (le_max_right _ _) htI.1, htI.2⟩⟩)
      exact l6h_vertex_inj (h1.symm.trans h2)
    have hne : j₁ + kk ≠ 1 := by
      intro h'
      apply hij
      rw [hi₁]
      exact (add_right_cancel (h'.trans hj1.symm)).symm
    set d := min (τ (n + 1) + ε₁) b with hd
    have hd1 : τ (n + 1) < d := lt_min (by linarith) hn1.2
    have hsub' : Icc (τ (n + 1)) d ⊆ Icc a b :=
      Icc_subset_Icc (hn1.1.le) (min_le_right _ _)
    have := l6h_mem_of_ae (C := Ici 0) isClosed_Ici ((hcont (j₁ + kk)).sub (hcont 1)) hd1 hsub'
      ⟨le_rfl, hd1.le⟩ (by
        filter_upwards [hM, hr] with t h1 h2 htI
        have hu1 : u' t = vertex (j₁ + kk) := by
          simp only [hu', h2 ⟨htI.1, htI.2.trans_le (min_le_left _ _)⟩, l6h_rotControl_vertex]
          rfl
        have := (h1 ⟨hn1.1.trans htI.1, htI.2.trans_le (min_le_right _ _)⟩).2 (vertex 1)
          (poly_vertex_mem 1)
        rw [hu1] at this
        exact sub_nonneg.2 this)
    simp only [mem_Ici, Pi.sub_apply, sub_nonneg] at this
    rw [harc _ ⟨hlt.le, le_rfl⟩] at this
    have := hmax (τ (n + 1) - τ n) ⟨by linarith, hlt'⟩ (j₁ + kk) hne
    linarith
  have hgap : τ (n + 1) - τ n = T := le_antisymm hle hge
  have hend := harc (τ (n + 1)) ⟨hlt.le, le_rfl⟩
  rw [hgap, hQ] at hend
  rw [show k + 1 = 1 + k by ring, ← irt_adRinvPow_add, hend]
  rfl

end SmoothedPolygons
