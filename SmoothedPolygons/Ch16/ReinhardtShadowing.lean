module

public import SmoothedPolygons.Ch16.RescaledLimits
public import SmoothedPolygons.Ch16.GlobalBasin

/-!
# Chapter 16: the cluster set of the switching points is invariant (§16.4.2, part 3; N5)

§16.4.2 of Hales–Vajjha, *Packings of Smoothed Polygons* ("Reinhardt switching functions as cubic
polynomials", TeX 12887–12987), and the gap N5 / G16.8 of the plan: the cluster set of the
switching points of a chattering arc is forward invariant under the Fuller–Poincaré map.

## The book's argument, and why it falls short

The book (TeX 12888–12987): (1) the rescaled Reinhardt switching functions `χ(s, r, ξ)/r³` extend
analytically across `r = 0`, where they are the Fuller cubics, so for small `r` their third
`s`-derivative is nonzero and they "behave qualitatively like a monic cubic polynomial";
(2) Weierstrass preparation at each root of the Fuller cubic gives a monic cubic `χ_W` with
coefficients analytic in `(r, ξ)` that "captures all real roots of `χ`"; (3) "All of these defining
conditions [of the cells `𝒞_k`, the parts `𝒟_i`, `𝒟_{1,ij}`] can be carried over to the Reinhardt
dynamical system", giving Reinhardt cells `𝒞_k^R` and parts `𝒟_i^R` near the divisor and "a
continuous extension `F_i` of the Reinhardt–Poincaré map from the interior of `𝒟_i^R` to all of
`𝒟_i^R`", restricting to the Fuller parts at `r = 0`; (4) the proof of Theorem 16.4.1 runs the
descent of Table 16.1 through these parts.

Step (3) is asserted without proof (G16.8): it needs the Fuller parts `𝒟_i` with continuous
branches on closed parts (Proposition 15.3.2, itself only a named proposition, read off Figures
15.2–15.3, and not used by the formal Theorem 16.1.1), and uniform control of the Reinhardt
switching functions near the whole divisor, including the faces where `t_sw → 0`, the 2-cells and
the double-root loci; "`χ_W` … defined for all `s`" also needs a bound on the rescaled switching
times (G16.11). Step (4) ignores the diagonal entries of Table 16.1 (G16.10). The zero count of
step (1) bounds the zeros of one constant-control piece, not the number of pieces of a trajectory
(the third derivative of `χ_ij` changes sign with the control).

## The repair (along the book's lines): relaxed limits

The descent through Reinhardt parts serves only to make the image `F_i(q)` of a cluster point a
cluster point. This is the one property used (`ClusterSetForwardInvariant`, N5): **the cluster set
`Ω = switchClusterSet` is mapped into itself by the honest Fuller–Poincaré map `F_ang =
poincareAngZero`** (with `Ω ⊆ Ξ_{𝒲,0}/V_T`, `mapClusterPt_switchAng_mem_sectionZero`). With it,
Theorem 16.4.1 follows from Theorem 16.1.1 itself (the book's "Repeating the argument of Theorem
16.1.1", TeX 13038–13040) and the hyperbolic box at `q_out`
(`SmoothedPolygons/Ch16/ClusterPoint.lean`). No Reinhardt cells, parts, branch maps or Weierstrass
polynomials are needed, and the three named numerical facts of Layer 5 suffice.

The proof of N5, for a cluster point `ξ ∈ sectionZero` of the `ξ_n` along `n_k`, with
`u₀ = firstControl ξ` and `T = firstSwitchTime ξ`:
1. (`exists_window`) The rescaled windows `[0, T + δ]` after `τ_{n_k}` stay before `b` for some
   `δ > 0`: otherwise the rescaled arcs, uniformly Lipschitz (equicontinuity), would reach `0`
   (`ẑ(q(b)) = 0`, the singular point) at rescaled times `σ_k → σ* ≤ T + δ`, and their limit, a
   relaxed Fuller extremal from `ξ` (`exists_tendsto_rescaledArc` on `[0, σ* - η]`), would vanish at
   `σ*`; it is `flow · ξ u₀` on `[0, T]` (`eq_flow_of_maxCondition_UT`), nonzero there
   (`flow_firstControl_ne_zero`), and Lipschitz, so nonzero on `[T, T + δ]` for small `δ`.
2. (`exists_tendsto_rescaledArc`) On `[0, T + δ]` a subsequence converges to a relaxed Fuller
   extremal `(y, w)` from `ξ`; `y = flow · ξ u₀` and `w = u₀` a.e. on `[0, T]`
   (`eq_flow_of_maxCondition_UT`), and `w ≠ u₀` on a set of positive measure in `(T, T + δ']` for
   every `δ' ≤ δ` (`firstControl_beaten_UT`).
3. (`exists_tendsto_switchAng_poincare`) A Reinhardt switch at rescaled time `→ T`: for small
   `ε > 0`, `u₀` is the strict maximizer of `H_F` at `y(s)`, `s ∈ [T - ε, T - ε/2]` (the switching
   functions are nonzero cubics, with finitely many zeros), hence of the rescaled Reinhardt
   Hamiltonian at the rescaled arc for large `k` (`tendstoUniformlyOn_rescaledHam`), so the
   Reinhardt control is `u₀` there; if there were no Reinhardt switch in rescaled time
   `(T - ε, T + δ')`, the
   control would be `u₀` on all of it (it is constant between switches), and the integrated controls
   would converge to `∫ u₀` there, against step 2. So some switching time `τ_{m_k}` has rescaled
   time in `(T - ε, T + δ')`, and `ξ_{m_k} = ang (rescaledArc n_k ((τ_{m_k} - τ_{n_k})/ρ_{n_k}))`
   tends, as `ε, δ' → 0` (diagonal), to `ang (y(T)) = ang (poincare ξ)`.
4. The class of `ang (poincare ξ)` is `F_ang([ξ])` (`ang_poincare_ang`, `poincareAng_orbitRel`), and
   `ang (poincare ξ) ∈ sectionZero` (`poincare_mem_walls`, `hamMax_poincare`); so `F_ang(Ω) ⊆ Ω`.
Tangencies of the Fuller trajectory (where a Reinhardt switching function dips below zero for a
short rescaled time) only add cluster points (the tangency points, whose image is again
`F(ξ)`); they do not affect the argument.

## Proofs (as formalized)

The four steps above, with two simplifications of the plan.
* Step 1 needs no uniform Lipschitz bound on the whole window: near a point `p ≠ 0` the rescaled
  field is bounded by `‖p‖ + 4` for small `ρ` (`tendstoUniformlyOn_rescaledField`), and a
  bootstrap (`l6i_bootstrap`) keeps the arc in a ball for a short rescaled time, so it cannot
  reach `0` quickly (`l6i_not_reach_zero`). The windows that run past `b` have rescaled times
  `σ_n` of `b` in `[0, T + δ]`, so a subsequence converges to `σ* ≤ T + δ`; the arcs are compared
  at `S' = 0` (`σ*` small) or at `S' = min (σ* - δ/2) T`, where the relaxed limit is
  `flow S' ξ u₀ ≠ 0`. The integral equation is used up to `b` itself (`rescaledArc_eq_integral`
  with `τ_n + σ_n ρ_n = b`); the field is integrable on `[0, σ_n]` because the arc goes from
  `ξ_n ≠ 0` to `0` (`l6i_arc_integral`).
* Step 3 does not transfer the strict optimality of `u₀` through
  `tendstoUniformlyOn_rescaledHam`: on a rescaled window `(T - ε, T + ε)` without switching times
  the control is one vertex `ζ^i` (finite bang-bang control, `l6i_integral_of_no_switch`); by
  pigeonhole one `i` occurs frequently, so `∫_{T-ε}^{T+ε} w = 2ε ζ^i`, hence `w = ζ^i` a.e. there
  (`ζ^i` is an extreme point of `U_T ⊆` unit disk, `l6i_ae_eq_of_integral_eq`); on `(T - ε, T)`
  also `w = u₀`, so `ζ^i = u₀` and `w = u₀` a.e. on `[0, T + ε/2]`, against
  `firstControl_beaten_UT` (`l6i_forced_switch`). The cluster point is then obtained directly
  (`mapClusterPt_iff_frequently`), without a diagonal sequence.
* Step 4: `mapClusterPt_switchAng_mem_sectionZero` puts `ang (F ξ)` in the section, and
  `poincareAngZero_classOf`, `classOf_smul_scale` identify its class.

## Module split and sizes

* `SmoothedPolygons/Ch16/RescaledDynamics.lean`: the uniform convergence of the rescaled field and
  Hamiltonians, and the cluster points in the section (500–900 lines);
* `SmoothedPolygons/Ch16/RelaxedFuller.lean`: `eq_flow_of_maxCondition_UT`,
  `firstControl_beaten_UT` (300–600 lines);
* `SmoothedPolygons/Ch16/RescaledLimits.lean`: the integral equation and the relaxed limits
  (Arzelà–Ascoli; 700–1,000 lines);
* this file: the window, the forced switch and N5 (500–900 lines).
Total for N5: 2,000–3,400 lines.

`ClusterSetForwardInvariant` is a named proposition so that Theorem 16.4.1 can also be used
conditionally on it (`theorem16_4_1_of_clusterSetForwardInvariant`).
-/

@[expose] public section

namespace SmoothedPolygons

open Complex Set Filter Topology MeasureTheory
open TriFuller

/-! ### Helpers: measure theory and the triangle `U_T` -/

/-- Points are null for Lebesgue measure. -/
private lemma l6i_ae_ne (t : ℝ) : ∀ᵐ s : ℝ, s ≠ t := by
  rw [ae_iff]
  simp

/-- A property holding almost everywhere on a nonempty open interval holds at some point of it. -/
private lemma l6i_exists_mem_of_ae {P : ℝ → Prop} {c d : ℝ} (hcd : c < d)
    (h : ∀ᵐ t, t ∈ Ioo c d → P t) : ∃ t ∈ Ioo c d, P t := by
  by_contra hcon
  push Not at hcon
  have h0 : volume (Ioo c d) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [h] with t ht hmem
    exact hcon t hmem (ht hmem)
  rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at h0
  linarith

/-- A measurable function bounded on `[a, b]` is interval integrable on its subintervals. -/
private lemma l6i_intervalIntegrable_of_bound {f : ℝ → ℂ} (hf : Measurable f) {a b C : ℝ}
    (hb : ∀ t ∈ Icc a b, ‖f t‖ ≤ C) {c d : ℝ} (hc : c ∈ Icc a b) (hd : d ∈ Icc a b) :
    IntervalIntegrable f volume c d := by
  have hab : a ≤ b := hc.1.trans hc.2
  have h : IntervalIntegrable f volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
      (Measure.integrableOn_of_bounded (by simp [Real.volume_Ioc]) hf.aestronglyMeasurable
        (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht ↦ hb t (Ioc_subset_Icc_self ht)))
  exact h.mono_set (by rw [uIcc_of_le hab]; exact uIcc_subset_Icc hc hd)

/-- `U_T` lies in the closed unit disk. -/
private lemma l6i_norm_le_one_of_mem_UT {v : ℂ} (hv : v ∈ UT) : ‖v‖ ≤ 1 := by
  have hsub : UT ⊆ Metric.closedBall (0 : ℂ) 1 :=
    convexHull_min (fun x hx ↦ by simp [norm_eq_one_of_mem_VT hx]) (convex_closedBall 0 1)
  simpa using hsub hv

/-- The simplex is mapped into `U_T`. -/
private lemma l6i_simplexToUT_mem {v : Fin 3 → ℝ} (hv : v ∈ controlSimplex) :
    simplexToUT v ∈ UT := by
  have h : simplexToUT v = ∑ m : Fin 3, v m • ζ ^ (m : ℕ) := by
    simp only [simplexToUT, Complex.real_smul]
  rw [h]
  have hconv : Convex ℝ UT := convex_convexHull ℝ VT
  refine hconv.sum_mem (fun m _ ↦ (hv.1 m).1) ?_ fun m _ ↦ ?_
  · rw [Fin.sum_univ_three]; exact hv.2
  · fin_cases m
    · simpa using VT_subset_UT one_mem_VT
    · simpa using VT_subset_UT ζ_mem_VT
    · simpa using VT_subset_UT ζ_sq_mem_VT

private lemma l6i_norm_simplexToUT_le {v : Fin 3 → ℝ} (hv : v ∈ controlSimplex) :
    ‖simplexToUT v‖ ≤ 1 :=
  l6i_norm_le_one_of_mem_UT (l6i_simplexToUT_mem hv)

private lemma l6i_simplexToUT_vertex (m : Fin 3) : simplexToUT (vertex m) = ζ ^ (m : ℕ) := by
  fin_cases m <;> simp [simplexToUT, vertex, Fin.sum_univ_three]

private lemma l6i_continuous_simplexToUT : Continuous simplexToUT := by
  unfold simplexToUT
  fun_prop

private lemma l6i_pow_mem_VT (m : Fin 3) : ζ ^ (m : ℕ) ∈ VT := by
  fin_cases m
  · simpa using one_mem_VT
  · simpa using ζ_mem_VT
  · simpa using ζ_sq_mem_VT

/-- **A unit vector is an extreme point of the unit disk, in integral form**: if `‖g‖ ≤ 1` on
`[p, q]` and `∫_p^q g = (q - p) v` with `‖v‖ = 1`, then `g = v` almost everywhere on `(p, q)`.
(`1 - RR(v, g) ≥ 0` has integral `0`, and `RR(v, g) = 1`, `‖g‖ ≤ 1` force `g = v`.) -/
private lemma l6i_ae_eq_of_integral_eq {g : ℝ → ℂ} {p q : ℝ} (hpq : p < q)
    (hg : IntervalIntegrable g volume p q) (hb : ∀ s ∈ Icc p q, ‖g s‖ ≤ 1) {v : ℂ}
    (hv : ‖v‖ = 1) (hI : ∫ s in p..q, g s = ((q - p : ℝ) : ℂ) * v) :
    ∀ᵐ s, s ∈ Ioo p q → g s = v := by
  set f : ℝ → ℂ := fun s ↦ starRingEnd ℂ v * (v - g s) with hf
  have hfi : IntervalIntegrable f volume p q :=
    (intervalIntegrable_const.sub hg).const_mul _
  set h : ℝ → ℝ := fun s ↦ Complex.reCLM (f s) with hh
  have hhi : IntervalIntegrable h volume p q :=
    ⟨Complex.reCLM.integrable_comp hfi.1, Complex.reCLM.integrable_comp hfi.2⟩
  have hvv : starRingEnd ℂ v * v = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hv]
    norm_num
  have hint : ∫ s in p..q, h s = 0 := by
    rw [hh, Complex.reCLM.intervalIntegral_comp_comm hfi, hf,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub intervalIntegrable_const hg, intervalIntegral.integral_const,
      hI, Complex.real_smul, sub_self, mul_zero, map_zero]
  have hre : ∀ s, h s = 1 - (starRingEnd ℂ v * g s).re := by
    intro s
    simp only [hh, hf, Complex.reCLM_apply, mul_sub, hvv, Complex.sub_re, Complex.one_re]
  have hnorm : ∀ s ∈ Icc p q, ‖starRingEnd ℂ v * g s‖ ≤ 1 := by
    intro s hs
    rw [norm_mul, Complex.norm_conj, hv, one_mul]
    exact hb s hs
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc p q)] h := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [Pi.zero_apply, hre]
    have := (Complex.re_le_norm _).trans (hnorm s (Ioc_subset_Icc_self hs))
    linarith
  have hz := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hpq.le hnn hhi).1 hint
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc] at hz
  filter_upwards [hz] with s hs hsI
  have h1 := hs (Ioo_subset_Ioc_self hsI)
  rw [Pi.zero_apply, hre] at h1
  set c := starRingEnd ℂ v * g s with hc
  have hcre : c.re = 1 := by linarith
  have hcn := hnorm s (Ioo_subset_Icc_self hsI)
  have hcim : c.im = 0 := by
    have e := Complex.sq_norm_sub_sq_re c
    rw [hcre] at e
    have h2 : ‖c‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg c]
    have h3 : c.im ^ 2 ≤ 0 := by linarith
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm h3 (sq_nonneg _))
  have hc1 : c = 1 := Complex.ext (by simpa using hcre) (by simpa using hcim)
  calc g s = (v * starRingEnd ℂ v) * g s := by rw [mul_comm v, hvv, one_mul]
    _ = v * c := by rw [hc]; ring
    _ = v := by rw [hc1, mul_one]

/-! ### Helpers: an a priori bound for integral equations -/

/-- **A bootstrap bound**: if `f(s) = f(s₀) + ∫_{s₀}^s g` on `[s₀, s₁]` with `f` continuous,
`‖g‖ ≤ M` wherever `‖f‖ ≤ R`, `‖f(s₀)‖ ≤ R - 1` and `M (s₁ - s₀) < 1`, then `f` stays in the ball
of radius `R` and `‖f(s) - f(s₀)‖ ≤ M (s - s₀)` on `[s₀, s₁]`. -/
private lemma l6i_bootstrap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → E} {s₀ s₁ R M : ℝ} (hf : ContinuousOn f (Icc s₀ s₁))
    (hint : ∀ s ∈ Icc s₀ s₁, f s = f s₀ + ∫ σ in s₀..s, g σ)
    (hg : ∀ σ ∈ Icc s₀ s₁, ‖f σ‖ ≤ R → ‖g σ‖ ≤ M)
    (h0 : ‖f s₀‖ ≤ R - 1) (hM : M * (s₁ - s₀) < 1) :
    ∀ s ∈ Icc s₀ s₁, ‖f s - f s₀‖ ≤ M * (s - s₀) := by
  have hbound : ∀ s ∈ Icc s₀ s₁, (∀ σ ∈ Ico s₀ s, ‖f σ‖ ≤ R) →
      ‖f s - f s₀‖ ≤ M * (s - s₀) := by
    intro s hs hR
    rw [hint s hs, add_sub_cancel_left]
    have := intervalIntegral.norm_integral_le_of_norm_le_const_ae (a := s₀) (b := s) (C := M)
      (f := g) (by
        filter_upwards [l6i_ae_ne s] with σ hσs hσ
        rw [uIoc_of_le hs.1] at hσ
        exact hg σ ⟨hσ.1.le, hσ.2.trans hs.2⟩ (hR σ ⟨hσ.1.le, lt_of_le_of_ne hσ.2 hσs⟩))
    rwa [abs_of_nonneg (sub_nonneg.2 hs.1)] at this
  have hin : ∀ s ∈ Icc s₀ s₁, ‖f s‖ < R := by
    by_contra hcon
    push Not at hcon
    set A := Icc s₀ s₁ ∩ (fun s ↦ ‖f s‖) ⁻¹' Ici R with hA
    have hAne : A.Nonempty := by
      obtain ⟨s, hs, hs'⟩ := hcon
      exact ⟨s, hs, hs'⟩
    have hAcl : IsClosed A := hf.norm.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hAbdd : BddBelow A := ⟨s₀, fun x hx ↦ hx.1.1⟩
    set t := sInf A with ht
    have htA : t ∈ A := hAcl.csInf_mem hAne hAbdd
    have hlt : ∀ σ ∈ Ico s₀ t, ‖f σ‖ ≤ R := by
      intro σ hσ
      by_contra hσR
      have : t ≤ σ := csInf_le hAbdd ⟨⟨hσ.1, hσ.2.le.trans htA.1.2⟩, (not_le.1 hσR).le⟩
      linarith [hσ.2]
    have hb := hbound t htA.1 hlt
    have hft : ‖f t‖ ≤ ‖f s₀‖ + ‖f t - f s₀‖ := by
      calc ‖f t‖ = ‖f s₀ + (f t - f s₀)‖ := by rw [add_sub_cancel]
        _ ≤ ‖f s₀‖ + ‖f t - f s₀‖ := norm_add_le _ _
    have hM' : M * (t - s₀) ≤ M * (s₁ - s₀) ∨ M < 0 := by
      rcases le_or_gt 0 M with hM0 | hM0
      · exact Or.inl (mul_le_mul_of_nonneg_left (by linarith [htA.1.2]) hM0)
      · exact Or.inr hM0
    have htR : R ≤ ‖f t‖ := htA.2
    rcases hM' with hM' | hM0
    · linarith
    · have := (norm_nonneg _).trans (hg s₀ ⟨le_rfl, htA.1.1.trans htA.1.2⟩ (by linarith))
      linarith
  intro s hs
  exact hbound s hs fun σ hσ ↦ (hin σ ⟨hσ.1, hσ.2.le.trans hs.2⟩).le

/-! ### Helpers: bang-bang controls -/

/-- **A time inside an interval of finite bang-bang control that is not a switching time has a
neighbourhood on which the control is one vertex** (the argument of `l6e_local_vertex` of
`SmoothedPolygons/Ch16/ClusterCoordinates.lean`, private there). -/
private lemma l6i_local_vertex {u : ℝ → Fin 3 → ℝ} {α β t : ℝ} (hbb : IsFiniteBangBang α β u)
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
  filter_upwards [hi, hj, l6i_ae_ne t] with τ h1 h2 h3 hτ
  rcases lt_or_gt_of_ne h3 with h | h
  · exact h1 ⟨hτ.1, h⟩
  · exact h2 ⟨h, hτ.2⟩

/-- Pigeonhole for `Fin 3`: if frequently some `i` works, then some `i` works frequently. -/
private lemma l6i_frequently_exists {P : ℕ → Fin 3 → Prop}
    (h : ∃ᶠ k in atTop, ∃ i, P k i) : ∃ i, ∃ᶠ k in atTop, P k i := by
  by_contra hne
  have hall : ∀ᶠ k in atTop, ∀ i, ¬ P k i :=
    Filter.eventually_all.2 fun i ↦ Filter.not_frequently.1 (not_exists.1 hne i)
  obtain ⟨k, ⟨i, hi⟩, hk⟩ := (h.and_eventually hall).exists
  exact hk i hi

/-! ### Helpers: the chattering arc and its rescaled arcs -/

section Arc

variable {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {τ : ℕ → ℝ}

private lemma l6i_radius_pos (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) (n : ℕ) :
    0 < switchRadius X Λ₁ ΛR τ n :=
  weightedNorm_pos (h.switchPoints.2.2.1 n)

/-- The radii of the switching points tend to `0⁺`. -/
private lemma l6i_radius_tendsto (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) :
    Tendsto (switchRadius X Λ₁ ΛR τ) atTop (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall (l6i_radius_pos h)⟩
  have := (continuous_weightedNorm.tendsto 0).comp h.switchPoints.2.2.2.1
  rw [weightedNorm_zero] at this
  exact this

private lemma l6i_lt (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) : a < b := by
  have := h.1.1.1
  linarith

/-- The control lies in the simplex on `[a, b]`. -/
private lemma l6i_control_mem (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) {t : ℝ}
    (ht : t ∈ Icc a b) : u t ∈ controlSimplex := by
  have := h.1.1.2.2.1 (t - a) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  simpa using this

/-- The control is measurable. -/
private lemma l6i_measurable_control (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) :
    Measurable u := by
  have hm : Measurable fun t ↦ u (a + t) := h.1.1.2.1
  have := hm.comp (measurable_id.sub_const a)
  convert this using 1
  funext t
  simp

/-- The rescaled arc starts at the angular component of the switching point. -/
private lemma l6i_arc_zero (n : ℕ) :
    rescaledArc X Λ₁ ΛR τ n 0 = switchAng X Λ₁ ΛR τ n := by
  simp [rescaledArc, switchAng, ang, switchRadius]

/-- The rescaled arc vanishes at the rescaled time of `b` (the singular point). -/
private lemma l6i_arc_end (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) (n : ℕ) :
    rescaledArc X Λ₁ ΛR τ n ((b - τ n) / switchRadius X Λ₁ ΛR τ n) = 0 := by
  obtain ⟨hblow, hsing, -⟩ := h.switchPoints
  have hρ := (l6i_radius_pos h n).ne'
  have e : τ n + (b - τ n) / switchRadius X Λ₁ ΛR τ n * switchRadius X Λ₁ ΛR τ n = b := by
    rw [div_mul_cancel₀ _ hρ]
    ring
  rw [rescaledArc, e, (fullerCoords_eq_zero_iff (hblow b ⟨(l6i_lt h).le, le_rfl⟩)).2 hsing]
  funext j
  fin_cases j <;> simp [scale]

/-- The angular component of the rescaled arc at the rescaled time of a later switching time is
the angular component of that switching point. -/
private lemma l6i_ang_arc (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) (n m : ℕ) {s : ℝ}
    (he : τ n + s * switchRadius X Λ₁ ΛR τ n = τ m) :
    ang (rescaledArc X Λ₁ ΛR τ n s) = switchAng X Λ₁ ΛR τ m := by
  have hz := h.switchPoints.2.2.1 m
  have := (weightedNorm_ang_smul_scale hz (inv_pos.2 (l6i_radius_pos h n)) one_mem_VT).2
  rw [one_smul, one_smul] at this
  rw [rescaledArc, he, this]
  rfl

/-- **The rescaled arc up to the rescaled time `σ_n = (b - τ_n)/ρ_n` of `b`**: it is continuous
on `[0, σ_n]` and solves the rescaled equation from every starting time `s₀ ∈ [0, σ_n]`. The
integrability of the field on `[0, σ_n]` comes for free from `rescaledArc_eq_integral` at `σ_n`:
the arc goes from `ξ_n ≠ 0` to `0`, so the integral of the field is nonzero. -/
private lemma l6i_arc_integral (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) (n : ℕ) :
    ContinuousOn (rescaledArc X Λ₁ ΛR τ n) (Icc 0 ((b - τ n) / switchRadius X Λ₁ ΛR τ n)) ∧
      ∀ s₀ ∈ Icc 0 ((b - τ n) / switchRadius X Λ₁ ΛR τ n),
        ∀ s ∈ Icc s₀ ((b - τ n) / switchRadius X Λ₁ ΛR τ n),
          rescaledArc X Λ₁ ΛR τ n s = rescaledArc X Λ₁ ΛR τ n s₀ +
            ∫ σ in s₀..s, rescaledField (switchRadius X Λ₁ ΛR τ n)
              (u (τ n + σ * switchRadius X Λ₁ ΛR τ n)) (rescaledArc X Λ₁ ΛR τ n σ) := by
  have hρ := l6i_radius_pos h n
  have hτb : τ n < b := (h.2.2.2.2.2.1 n).2
  set σn := (b - τ n) / switchRadius X Λ₁ ΛR τ n with hσn
  set F : ℝ → Fin 3 → ℂ := fun σ ↦ rescaledField (switchRadius X Λ₁ ΛR τ n)
    (u (τ n + σ * switchRadius X Λ₁ ΛR τ n)) (rescaledArc X Λ₁ ΛR τ n σ) with hF
  have hσn0 : 0 ≤ σn := div_nonneg (by linarith) hρ.le
  have hS : τ n + σn * switchRadius X Λ₁ ΛR τ n ≤ b := by
    rw [hσn, div_mul_cancel₀ _ hρ.ne']
    linarith
  obtain ⟨h0, hrep⟩ := rescaledArc_eq_integral h n hS
  have hrep' : ∀ s ∈ Icc 0 σn,
      rescaledArc X Λ₁ ΛR τ n s = rescaledArc X Λ₁ ΛR τ n 0 + ∫ σ in (0 : ℝ)..s, F σ :=
    hrep
  have hξ : rescaledArc X Λ₁ ΛR τ n 0 ≠ 0 := by
    rw [h0]
    exact ne_zero_of_mem_Xi (h.switchPoints.2.2.2.2 n)
  have hint : IntervalIntegrable F volume 0 σn := by
    refine intervalIntegral.intervalIntegrable_of_integral_ne_zero fun h' ↦ hξ ?_
    have := hrep' σn ⟨hσn0, le_rfl⟩
    rw [l6i_arc_end h n, h', add_zero] at this
    exact this.symm
  have hint' : ∀ c ∈ Icc 0 σn, ∀ d ∈ Icc 0 σn, IntervalIntegrable F volume c d :=
    fun c hc d hd ↦ hint.mono_set (by rw [uIcc_of_le hσn0]; exact uIcc_subset_Icc hc hd)
  refine ⟨?_, fun s₀ hs₀ s hs ↦ ?_⟩
  · have hc := intervalIntegral.continuousOn_primitive_interval' hint left_mem_uIcc
    rw [uIcc_of_le hσn0] at hc
    exact (continuousOn_const.add hc).congr fun s hs ↦ hrep' s hs
  · have hsI : s ∈ Icc 0 σn := ⟨hs₀.1.trans hs.1, hs.2⟩
    change rescaledArc X Λ₁ ΛR τ n s = rescaledArc X Λ₁ ΛR τ n s₀ + ∫ σ in s₀..s, F σ
    rw [hrep' s hsI, hrep' s₀ hs₀, add_assoc,
      intervalIntegral.integral_add_adjacent_intervals (hint' 0 ⟨le_rfl, hσn0⟩ s₀ hs₀)
        (hint' s₀ hs₀ s hsI)]

/-- The rescaled control is measurable and bounded by `1` on windows before `b`. -/
private lemma l6i_rescaledControl (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) (n : ℕ) {S : ℝ}
    (hS : τ n + S * switchRadius X Λ₁ ΛR τ n ≤ b) {c d : ℝ} (hc : c ∈ Icc 0 S)
    (hd : d ∈ Icc 0 S) :
    IntervalIntegrable (rescaledControl u X Λ₁ ΛR τ n) volume c d := by
  have hρ := l6i_radius_pos h n
  have hτ := h.2.2.2.2.2.1 n
  have hmeas : Measurable (rescaledControl u X Λ₁ ΛR τ n) := by
    change Measurable fun s ↦ simplexToUT (u (τ n + s * switchRadius X Λ₁ ΛR τ n))
    exact l6i_continuous_simplexToUT.measurable.comp
      ((l6i_measurable_control h).comp (by fun_prop))
  refine l6i_intervalIntegrable_of_bound (C := 1) hmeas (fun s hs ↦ ?_) hc hd
  refine l6i_norm_simplexToUT_le (l6i_control_mem h ⟨?_, ?_⟩)
  · nlinarith [hτ.1, hs.1]
  · nlinarith [hs.2]

/-- The rescaled Reinhardt field is bounded by `R + 2` on the ball of radius `R` for small `ρ`
(`tendstoUniformlyOn_rescaledField`, and `‖fullerField‖ ≤ max 1 ‖y‖`). -/
private lemma l6i_eventually_field_le (R : ℝ) (hR : 0 ≤ R) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ v ∈ controlSimplex, ∀ y : Fin 3 → ℂ, ‖y‖ ≤ R →
      ‖rescaledField ρ v y‖ ≤ R + 2 := by
  have hU := tendstoUniformlyOn_rescaledField (isCompact_closedBall (0 : Fin 3 → ℂ) R)
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hU 1 one_pos] with ρ hρ v hv y hy
  have hyK : y ∈ Metric.closedBall (0 : Fin 3 → ℂ) R := by simpa using hy
  have h1 : dist (fullerField (simplexToUT v) y) (rescaledField ρ v y) < 1 := hρ (v, y) ⟨hv, hyK⟩
  have h2 : ‖fullerField (simplexToUT v) y‖ ≤ R + 1 := by
    refine (pi_norm_le_iff_of_nonneg (by linarith)).2 fun j ↦ ?_
    fin_cases j
    · simp only [fullerField, Fin.zero_eta, Matrix.cons_val_zero, norm_mul, norm_neg,
        Complex.norm_I, one_mul]
      linarith [l6i_norm_simplexToUT_le hv]
    · simpa [fullerField] using (norm_le_pi_norm y 0).trans (by linarith)
    · simpa [fullerField] using (norm_le_pi_norm y 1).trans (by linarith)
  have h3 := norm_sub_norm_le (rescaledField ρ v y) (fullerField (simplexToUT v) y)
  rw [← dist_eq_norm, dist_comm] at h3
  linarith

/-- **The rescaled arcs cannot reach `0` soon after a time at which they are near a point
`p ≠ 0`** (the equicontinuity step of `exists_window`): along `n_k`, let the rescaled arcs at
the rescaled time `S' ≥ 0` tend to `p`, let `S'` be eventually before the rescaled time `σ_{n_k}`
of `b`, and let `σ_{n_k} - S' → ℓ` with `(‖p‖ + 4) ℓ < min (‖p‖/2) 1`. Then the arcs, which are
`(‖p‖ + 4)`-Lipschitz near `p` for large `k` (`l6i_eventually_field_le`, `l6i_bootstrap`), cannot
vanish at `σ_{n_k}`; but they do (`l6i_arc_end`). -/
private lemma l6i_not_reach_zero (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) {φ : ℕ → ℕ}
    (hφ : StrictMono φ) {S' ℓ : ℝ} (hS' : 0 ≤ S') {p : Fin 3 → ℂ} (hp : p ≠ 0)
    (harc : Tendsto (fun k ↦ rescaledArc X Λ₁ ΛR τ (φ k) S') atTop (𝓝 p))
    (hσ : Tendsto (fun k ↦ (b - τ (φ k)) / switchRadius X Λ₁ ΛR τ (φ k) - S') atTop (𝓝 ℓ))
    (hge : ∀ᶠ k in atTop, S' ≤ (b - τ (φ k)) / switchRadius X Λ₁ ΛR τ (φ k))
    (hℓ : (‖p‖ + 4) * ℓ < min (‖p‖ / 2) 1) : False := by
  have hpn : 0 < ‖p‖ := norm_pos_iff.2 hp
  set R := ‖p‖ + 2 with hR
  set M := ‖p‖ + 4 with hM
  have E1 : ∀ᶠ k in atTop, ∀ v ∈ controlSimplex, ∀ y : Fin 3 → ℂ, ‖y‖ ≤ R →
      ‖rescaledField (switchRadius X Λ₁ ΛR τ (φ k)) v y‖ ≤ R + 2 :=
    ((l6i_radius_tendsto h).comp hφ.tendsto_atTop).eventually
      (l6i_eventually_field_le R (by positivity))
  have E2 : ∀ᶠ k in atTop, dist (rescaledArc X Λ₁ ΛR τ (φ k) S') p < min 1 (‖p‖ / 2) :=
    (Metric.tendsto_nhds.1 harc) _ (by positivity)
  have E3 : ∀ᶠ k in atTop,
      M * ((b - τ (φ k)) / switchRadius X Λ₁ ΛR τ (φ k) - S') < min (‖p‖ / 2) 1 :=
    ((hσ.const_mul M).eventually (gt_mem_nhds hℓ))
  obtain ⟨k, ⟨⟨hk1, hk2⟩, hk3⟩, hk4⟩ := (((E1.and E2).and E3).and hge).exists
  set n := φ k with hn
  set ρ := switchRadius X Λ₁ ΛR τ n with hρdef
  set σn := (b - τ n) / ρ with hσn
  have hρ : 0 < ρ := l6i_radius_pos h n
  have hτ := h.2.2.2.2.2.1 n
  obtain ⟨hcont, hrep⟩ := l6i_arc_integral h n
  have hS'I : S' ∈ Icc 0 σn := ⟨hS', hk4⟩
  have hd2 := lt_min_iff.1 hk2
  have hd3 := lt_min_iff.1 hk3
  have hnorm : ‖rescaledArc X Λ₁ ΛR τ n S' - p‖ < min 1 (‖p‖ / 2) := by
    rw [← dist_eq_norm]; exact hk2
  have hnorm' := lt_min_iff.1 hnorm
  have h0 : ‖rescaledArc X Λ₁ ΛR τ n S'‖ ≤ R - 1 := by
    have := norm_le_norm_add_norm_sub' (rescaledArc X Λ₁ ΛR τ n S') p
    linarith
  have hb := l6i_bootstrap (f := rescaledArc X Λ₁ ΛR τ n)
    (g := fun σ ↦ rescaledField ρ (u (τ n + σ * ρ)) (rescaledArc X Λ₁ ΛR τ n σ))
    (s₀ := S') (s₁ := σn) (R := R) (M := M)
    (hcont.mono (Icc_subset_Icc hS' le_rfl)) (fun s hs ↦ hrep S' hS'I s hs)
    (fun σ hσ hyR ↦ by
      have hσρ : σ * ρ ≤ b - τ n := (le_div_iff₀ hρ).1 hσ.2
      have hmem : τ n + σ * ρ ∈ Icc a b :=
        ⟨by nlinarith [hτ.1, hσ.1, hS'], by linarith⟩
      have := hk1 _ (l6i_control_mem h hmem) _ hyR
      linarith)
    h0 (by linarith) σn ⟨hk4, le_rfl⟩
  rw [l6i_arc_end h n, zero_sub, norm_neg] at hb
  have hlow : ‖p‖ - ‖rescaledArc X Λ₁ ΛR τ n S' - p‖ ≤ ‖rescaledArc X Λ₁ ΛR τ n S'‖ := by
    have := norm_sub_norm_le p (rescaledArc X Λ₁ ΛR τ n S')
    rw [norm_sub_rev] at this
    linarith
  linarith

/-- **On a window without switching times the rescaled control is a vertex** (finite bang-bang
control between switches, `l6i_local_vertex`, `exists_ae_eq_vertex_of_locally`), so its integral
over the window `[p, q]` is `(q - p)` times that vertex (the change of variables
`t = τ_n + sρ_n`). -/
private lemma l6i_integral_of_no_switch (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) (n : ℕ)
    {S p q : ℝ} (hp : 0 < p) (hpq : p < q) (hqS : q ≤ S)
    (hS : τ n + S * switchRadius X Λ₁ ΛR τ n < b)
    (hno : ¬ ∃ m, τ m ∈ Ioo (τ n + p * switchRadius X Λ₁ ΛR τ n)
      (τ n + q * switchRadius X Λ₁ ΛR τ n)) :
    ∃ i : Fin 3, (∫ σ in (0 : ℝ)..q, rescaledControl u X Λ₁ ΛR τ n σ) -
        ∫ σ in (0 : ℝ)..p, rescaledControl u X Λ₁ ΛR τ n σ = ((q - p : ℝ) : ℂ) * ζ ^ (i : ℕ) := by
  have hρ : 0 < switchRadius X Λ₁ ΛR τ n := l6i_radius_pos h n
  set ρ := switchRadius X Λ₁ ΛR τ n with hρdef
  have hτ := h.2.2.2.2.2.1 n
  have hα : a < τ n + p * ρ := by nlinarith [hτ.1, mul_pos hp hρ]
  have hβ : τ n + q * ρ < b := by nlinarith
  have hbb := h.2.2.2.1 _ _ hα hβ
  have hnosw : ∀ t ∈ Ioo (τ n + p * ρ) (τ n + q * ρ), ¬ IsSwitchingTime u t := by
    intro t ht hsw
    obtain ⟨m, hm⟩ := (h.2.2.2.2.2.2.2 t ⟨hα.trans ht.1, ht.2.trans hβ⟩).1 hsw
    exact hno ⟨m, hm ▸ ht⟩
  obtain ⟨i, hi⟩ := exists_ae_eq_vertex_of_locally fun t ht ↦
    l6i_local_vertex hbb ht (hnosw t ht)
  refine ⟨i, ?_⟩
  have hSb : τ n + S * ρ ≤ b := hS.le
  have hS0 : 0 ≤ S := by linarith
  rw [intervalIntegral.integral_interval_sub_left
    (l6i_rescaledControl h n hSb ⟨le_rfl, hS0⟩ ⟨by linarith, hqS⟩)
    (l6i_rescaledControl h n hSb ⟨le_rfl, hS0⟩ ⟨hp.le, by linarith⟩)]
  have e1 : ∫ σ in p..q, rescaledControl u X Λ₁ ΛR τ n σ =
      ∫ σ in p..q, simplexToUT (u (ρ * σ + τ n)) := by
    refine intervalIntegral.integral_congr fun σ _ ↦ ?_
    change simplexToUT (u (τ n + σ * ρ)) = _
    congr 2
    ring
  have e2 := intervalIntegral.integral_comp_mul_add (a := p) (b := q)
    (fun t ↦ simplexToUT (u t)) hρ.ne' (τ n)
  have hle : ρ * p + τ n ≤ ρ * q + τ n := by nlinarith
  have e3 : ∫ t in (ρ * p + τ n)..(ρ * q + τ n), simplexToUT (u t) =
      ∫ _ in (ρ * p + τ n)..(ρ * q + τ n), ζ ^ (i : ℕ) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hi, l6i_ae_ne (ρ * q + τ n)] with t ht hne htI
    rw [uIoc_of_le hle] at htI
    rw [ht ⟨by linarith [htI.1], lt_of_le_of_ne (by linarith [htI.2]) (by
      intro e; exact hne (by linarith))⟩, l6i_simplexToUT_vertex]
  rw [e1, e2, e3, intervalIntegral.integral_const, Complex.real_smul, Complex.real_smul,
    ← mul_assoc, ← Complex.ofReal_mul]
  congr 2
  field_simp
  ring

/-- **The forced switch** (steps 2–3 of the proof of N5): let `(y, w)` be the relaxed limit on
`[0, T + δ]`, `T = t_sw(ξ)`, of the rescaled arcs along `n_k` (`exists_tendsto_rescaledArc`), with
`w = u₀` a.e. on `[0, T]` (`eq_flow_of_maxCondition_UT`). Then for every `ε ∈ (0, min T δ)`
eventually some switching time has rescaled time in `(T - ε, T + ε)`.

Otherwise, frequently, the control is one vertex `ζ^i` on that window (`l6i_integral_of_no_switch`),
for one `i` frequently (pigeonhole), and the integrated controls converge
(`exists_tendsto_rescaledArc`): `∫_{T-ε}^{T+ε} w = 2ε ζ^i`, so `w = ζ^i` a.e. there
(`l6i_ae_eq_of_integral_eq`; `ζ^i` is an extreme point of `U_T`); on `(T - ε, T)` also `w = u₀`, so
`ζ^i = u₀` and `w = u₀` a.e. on `[0, T + ε/2]`, against `firstControl_beaten_UT`. -/
private lemma l6i_forced_switch (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) {n : ℕ → ℕ}
    {ξ : Fin 3 → ℂ} (hz : ξ ≠ 0) {δ : ℝ}
    (hwin : ∀ᶠ k in atTop,
      τ (n k) + (firstSwitchTime ξ + δ) * switchRadius X Λ₁ ΛR τ (n k) < b)
    {y : ℝ → Fin 3 → ℂ} {w : ℝ → ℂ}
    (htraj : IsTrajectory UT 0 (firstSwitchTime ξ + δ) y w)
    (hmax : MaxCondition UT 0 (firstSwitchTime ξ + δ) y w) (hy0 : y 0 = ξ)
    (hint : ∀ s ∈ Icc 0 (firstSwitchTime ξ + δ), Tendsto
        (fun k ↦ ∫ σ in (0 : ℝ)..s, rescaledControl u X Λ₁ ΛR τ (n k) σ) atTop
        (𝓝 (∫ σ in (0 : ℝ)..s, w σ)))
    (hwT : ∀ᵐ t, t ∈ Icc 0 (firstSwitchTime ξ) → w t = firstControl ξ)
    {ε : ℝ} (hε : 0 < ε) (hεT : ε < firstSwitchTime ξ) (hεδ : ε < δ) :
    ∀ᶠ k in atTop, ∃ m, τ m ∈ Ioo
      (τ (n k) + (firstSwitchTime ξ - ε) * switchRadius X Λ₁ ΛR τ (n k))
      (τ (n k) + (firstSwitchTime ξ + ε) * switchRadius X Λ₁ ΛR τ (n k)) := by
  set T := firstSwitchTime ξ with hTdef
  set u₀ := firstControl ξ with hu₀def
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  have hkey : ∃ᶠ k in atTop, ∃ i : Fin 3,
      (∫ σ in (0 : ℝ)..(T + ε), rescaledControl u X Λ₁ ΛR τ (n k) σ) -
        ∫ σ in (0 : ℝ)..(T - ε), rescaledControl u X Λ₁ ΛR τ (n k) σ =
        (((T + ε) - (T - ε) : ℝ) : ℂ) * ζ ^ (i : ℕ) :=
    (hcon.and_eventually hwin).mono fun k hk ↦
      l6i_integral_of_no_switch h (n k) (by linarith) (by linarith)
        (by linarith : T + ε ≤ T + δ) hk.2 hk.1
  obtain ⟨i, hi⟩ := l6i_frequently_exists hkey
  have hlim := (hint (T + ε) ⟨by linarith, by linarith⟩).sub
    (hint (T - ε) ⟨by linarith, by linarith⟩)
  have heq := tendsto_nhds_unique_of_frequently_eq hlim tendsto_const_nhds hi
  have hwi : ∀ c ∈ Icc 0 (T + δ), ∀ d ∈ Icc 0 (T + δ), IntervalIntegrable w volume c d :=
    fun c hc d hd ↦ IsTrajectory.intervalIntegrable_control subset_rfl htraj hc hd
  rw [intervalIntegral.integral_interval_sub_left
    (hwi 0 ⟨le_rfl, by linarith⟩ (T + ε) ⟨by linarith, by linarith⟩)
    (hwi 0 ⟨le_rfl, by linarith⟩ (T - ε) ⟨by linarith, by linarith⟩)] at heq
  have hae := l6i_ae_eq_of_integral_eq (by linarith : T - ε < T + ε)
    (hwi _ ⟨by linarith, by linarith⟩ _ ⟨by linarith, by linarith⟩)
    (fun s hs ↦ IsTrajectory.norm_control_le_one subset_rfl htraj s
      ⟨by linarith [hs.1], by linarith [hs.2]⟩)
    (norm_eq_one_of_mem_VT (l6i_pow_mem_VT i)) heq
  obtain ⟨t, -, ht1, ht2⟩ := l6i_exists_mem_of_ae
    (P := fun t ↦ w t = u₀ ∧ w t = ζ ^ (i : ℕ)) (by linarith : T - ε < T) (by
      filter_upwards [hwT, hae] with t h1 h2 htI
      exact ⟨h1 ⟨by linarith [htI.1], htI.2.le⟩, h2 ⟨htI.1, by linarith [htI.2]⟩⟩)
  have hu : ζ ^ (i : ℕ) = u₀ := ht2.symm.trans ht1
  have hall : ∀ᵐ t, t ∈ Icc 0 (T + ε / 2) → w t = u₀ := by
    filter_upwards [hwT, hae] with t h1 h2 htI
    rcases le_or_gt t T with htT | htT
    · exact h1 ⟨htI.1, htT⟩
    · rw [h2 ⟨by linarith, by linarith [htI.2]⟩, hu]
  exact firstControl_beaten_UT hz (by linarith : 0 < ε / 2)
    (IsTrajectory.mono subset_rfl htraj le_rfl (by linarith) (by linarith))
    (MaxCondition.mono hmax le_rfl (by linarith)) hy0 hall

end Arc

/-! ### The window, the forced switch and N5 -/
/-- **The rescaled windows stay before the singular time** (step 1 of the proof of N5; the
equicontinuity argument): along a chattering arc into `b`, if `ξ_{n_k} → ξ ∈ sectionZero`, then
for some `δ > 0` the windows `[τ_{n_k}, τ_{n_k} + (t_sw(ξ) + δ) ρ_{n_k}]` lie before `b` for all
large `k`. (The rescaled arcs reach `0` at the rescaled time of `b`; their relaxed limit is
`flow · ξ (firstControl ξ)` on `[0, t_sw(ξ)]`, which does not vanish, `flow_firstControl_ne_zero`.)

Proof: let `c₀ > 0` and `R₁` bound `‖z(s, ξ, u₀)‖` below and above on `[0, T]`, `M = R₁ + 4` and
`δ = min (c₀/(4M)) (1/(4M))`. If the windows `[0, T + δ]` frequently run past `b`, the rescaled
times `σ_n = (b - τ_n)/ρ_n` of `b` lie in `[0, T + δ]` along a subsequence, and converge to some
`σ* ≤ T + δ` along a further one. Take `S' = 0` if `σ* ≤ δ/2` (the arcs start at `ξ_n → ξ`) and
`S' = min (σ* - δ/2) T` otherwise (the relaxed limit on `[0, S']`, `exists_tendsto_rescaledArc`,
is `z(·, ξ, u₀)` there, `eq_flow_of_maxCondition_UT`): the arcs at `S'` tend to a point `p` with
`‖p‖ ≥ c₀`, and reach `0` within rescaled time `≈ σ* - S' ≤ δ`, at speed at most `M`
(`l6i_not_reach_zero`). -/
theorem exists_window {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {τ : ℕ → ℝ}
    (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {ξ : Fin 3 → ℂ} (hξ0 : ξ ∈ sectionZero)
    (hξ : Tendsto (fun k ↦ switchAng X Λ₁ ΛR τ (φ k)) atTop (𝓝 ξ)) :
    ∃ δ > 0, ∀ᶠ k in atTop,
      τ (φ k) + (firstSwitchTime ξ + δ) * switchRadius X Λ₁ ΛR τ (φ k) < b := by
  have hz : ξ ≠ 0 := hξ0.1
  have hT : 0 < firstSwitchTime ξ := firstSwitchTime_pos hz
  set T := firstSwitchTime ξ with hTdef
  set u₀ := firstControl ξ with hu₀def
  have hfc : Continuous fun s ↦ flow s ξ u₀ :=
    continuous_iff_continuousAt.2 fun t ↦ (hasDerivAt_flow t ξ u₀).continuousAt
  obtain ⟨s₁, hs₁, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hT.le)
    (hfc.norm.continuousOn (s := Icc 0 T))
  obtain ⟨s₂, -, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hT.le)
    (hfc.norm.continuousOn (s := Icc 0 T))
  set c₀ := ‖flow s₁ ξ u₀‖ with hc₀def
  set R₁ := ‖flow s₂ ξ u₀‖ with hR₁def
  have hc₀ : 0 < c₀ := norm_pos_iff.2 (flow_firstControl_ne_zero hz hs₁)
  have hlo : ∀ s ∈ Icc 0 T, c₀ ≤ ‖flow s ξ u₀‖ := fun s hs ↦ hmin hs
  have hhi : ∀ s ∈ Icc 0 T, ‖flow s ξ u₀‖ ≤ R₁ := fun s hs ↦ hmax hs
  set M := R₁ + 4 with hMdef
  have hM : 0 < M := by positivity
  set d := min (c₀ / (4 * M)) (1 / (4 * M)) with hd
  have hd0 : 0 < d := lt_min (by positivity) (by positivity)
  have hd1 : M * d ≤ c₀ / 4 := by
    calc M * d ≤ M * (c₀ / (4 * M)) := mul_le_mul_of_nonneg_left (min_le_left _ _) hM.le
      _ = c₀ / 4 := by field_simp
  have hd2 : M * d ≤ 1 / 4 := by
    calc M * d ≤ M * (1 / (4 * M)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hM.le
      _ = 1 / 4 := by field_simp
  refine ⟨d, hd0, ?_⟩
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  obtain ⟨χ, hχ, hχP⟩ := extraction_of_frequently_atTop hcon
  set σ : ℕ → ℝ := fun n ↦ (b - τ n) / switchRadius X Λ₁ ΛR τ n with hσdef
  have hσmem : ∀ k, σ (φ (χ k)) ∈ Icc 0 (T + d) := by
    intro k
    have hρ := l6i_radius_pos h (φ (χ k))
    have hτ := h.2.2.2.2.2.1 (φ (χ k))
    refine ⟨div_nonneg (by linarith [hτ.2]) hρ.le, ?_⟩
    rw [hσdef, div_le_iff₀ hρ]
    linarith [not_lt.1 (hχP k)]
  obtain ⟨σs, hσs, χ', hχ', hσlim⟩ := isCompact_Icc.tendsto_subseq hσmem
  set φ₁ := φ ∘ χ ∘ χ' with hφ₁def
  have hφ₁ : StrictMono φ₁ := hφ.comp (hχ.comp hχ')
  have hξ₁ : Tendsto (fun k ↦ switchAng X Λ₁ ΛR τ (φ₁ k)) atTop (𝓝 ξ) :=
    hξ.comp (hχ.comp hχ').tendsto_atTop
  have hσlim' : Tendsto (fun k ↦ σ (φ₁ k)) atTop (𝓝 σs) := hσlim
  have hξn : c₀ ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ R₁ := by
    have e : flow 0 ξ u₀ = ξ := flow_zero ξ u₀
    exact ⟨e ▸ hlo 0 ⟨le_rfl, hT.le⟩, e ▸ hhi 0 ⟨le_rfl, hT.le⟩⟩
  by_cases hsmall : σs ≤ d / 2
  · -- the arcs start at `ξ_n → ξ` and reach `0` within rescaled time `≈ σs ≤ δ/2`
    refine l6i_not_reach_zero h hφ₁ le_rfl hz
      (hξ₁.congr fun k ↦ (l6i_arc_zero _).symm) (hσlim'.sub_const 0)
      (Eventually.of_forall fun k ↦ (hσmem (χ' k)).1) ?_
    have hA : (‖ξ‖ + 4) * (σs - 0) ≤ M * d / 2 := by
      rw [sub_zero]
      calc (‖ξ‖ + 4) * σs ≤ M * σs := mul_le_mul_of_nonneg_right (by linarith) hσs.1
        _ ≤ M * (d / 2) := mul_le_mul_of_nonneg_left hsmall hM.le
        _ = M * d / 2 := by ring
    exact lt_min (by linarith) (by linarith)
  · -- the relaxed limit on `[0, S']` is the first-control flow, nonzero at `S'`
    push Not at hsmall
    set S' := min (σs - d / 2) T with hS'def
    have hS'pos : 0 < S' := lt_min (by linarith) hT
    have hS'T : S' ≤ T := min_le_right _ _
    have hS'σ : S' ≤ σs - d / 2 := min_le_left _ _
    have hgap : σs - S' ≤ d := by
      rcases le_total (σs - d / 2) T with h1 | h1
      · rw [hS'def, min_eq_left h1]; linarith
      · rw [hS'def, min_eq_right h1]; linarith [hσs.2]
    have hev : ∀ᶠ k in atTop, S' < σ (φ₁ k) := hσlim'.eventually (lt_mem_nhds (by linarith))
    have hwin : ∀ᶠ k in atTop, τ (φ₁ k) + S' * switchRadius X Λ₁ ΛR τ (φ₁ k) < b := by
      filter_upwards [hev] with k hk
      have hρ := l6i_radius_pos h (φ₁ k)
      have := (lt_div_iff₀ hρ).1 hk
      linarith
    obtain ⟨ψ, hψ, y, w, htraj, hmaxc, hy0, hunif, -⟩ :=
      exists_tendsto_rescaledArc h hφ₁ hξ₁ hS'pos hwin
    obtain ⟨hyfl, -⟩ := eq_flow_of_maxCondition_UT hz hS'T htraj hmaxc hy0
    have hp : flow S' ξ u₀ ≠ 0 := flow_firstControl_ne_zero hz ⟨hS'pos.le, hS'T⟩
    have harc : Tendsto (fun k ↦ rescaledArc X Λ₁ ΛR τ (φ₁ (ψ k)) S') atTop
        (𝓝 (flow S' ξ u₀)) := by
      have := hunif.tendsto_at ⟨hS'pos.le, le_rfl⟩
      rw [hyfl S' ⟨hS'pos.le, le_rfl⟩] at this
      exact this
    refine l6i_not_reach_zero h (hφ₁.comp hψ) hS'pos.le hp harc
      ((hσlim'.comp hψ.tendsto_atTop).sub_const S') ?_ ?_
    · filter_upwards [hψ.tendsto_atTop.eventually hev] with k hk using hk.le
    · have hpn := hlo S' ⟨hS'pos.le, hS'T⟩
      have hpn' := hhi S' ⟨hS'pos.le, hS'T⟩
      have hA : (‖flow S' ξ u₀‖ + 4) * (σs - S') ≤ M * d :=
        mul_le_mul (by linarith) hgap (by linarith) hM.le
      exact lt_min (by linarith) (by linarith)

/-- **A Reinhardt switch at rescaled time `→ t_sw`** (steps 2–3 of the proof of N5): along a
chattering arc into `b`, if `ξ_{n_k} → ξ ∈ sectionZero`, then there are switching indices
`m_k → ∞` whose angular components tend to `ang (F ξ)`, the angular component of the
Fuller–Poincaré image of `ξ` (relaxed limits, `exists_tendsto_rescaledArc`;
`eq_flow_of_maxCondition_UT`; `firstControl_beaten_UT`; the extremality of the vertices of
`U_T`).

Proof: `exists_window` gives `δ`, and `exists_tendsto_rescaledArc` on `[0, T + δ]` a relaxed limit
`(y, w)` along `n_k`; `y = z(·, ξ, u₀)` and `w = u₀` a.e. on `[0, T]`
(`eq_flow_of_maxCondition_UT`), so `y(T) = F(ξ)`. For a neighbourhood `U` of `ang F(ξ)`, choose
`η` with `ang(B(F ξ, η)) ⊆ U`, then `ε` with `‖y(s) - y(T)‖ < η/2` for `|s - T| < ε`; for large
`k` the arcs are `η/2`-close to `y` and some switching time `τ_m` has rescaled time `s` in
`(T - ε, T + ε)` (`l6i_forced_switch`); then `ξ_m = ang(rescaledArc n_k s) ∈ U`. So `ang F(ξ)` is
a cluster point of the `ξ_n`. **Departure from the plan** (module docstring, step 3): the vertex
used on a window without switches is identified by `w = u₀` a.e. on `[0, T]` and the extremality
of the vertices of `U_T`, not by transferring the strict optimality of `u₀` through
`tendstoUniformlyOn_rescaledHam`; that transfer is not needed. -/
theorem exists_tendsto_switchAng_poincare {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    {τ : ℕ → ℝ} (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {ξ : Fin 3 → ℂ} (hξ0 : ξ ∈ sectionZero)
    (hξ : Tendsto (fun k ↦ switchAng X Λ₁ ΛR τ (φ k)) atTop (𝓝 ξ)) :
    ∃ m : ℕ → ℕ, Tendsto m atTop atTop ∧
      Tendsto (fun k ↦ switchAng X Λ₁ ΛR τ (m k)) atTop (𝓝 (ang (poincare ξ))) := by
  have hz : ξ ≠ 0 := hξ0.1
  have hT : 0 < firstSwitchTime ξ := firstSwitchTime_pos hz
  obtain ⟨δ, hδ, hwin⟩ := exists_window h hφ hξ0 hξ
  obtain ⟨ψ, hψ, y, w, htraj, hmax, hy0, hunif, hint⟩ :=
    exists_tendsto_rescaledArc h hφ hξ (by linarith) hwin
  set T := firstSwitchTime ξ with hTdef
  have hTδ : T ≤ T + δ := by linarith
  obtain ⟨hyfl, hwT⟩ := eq_flow_of_maxCondition_UT hz le_rfl
    (IsTrajectory.mono subset_rfl htraj le_rfl hT hTδ) (MaxCondition.mono hmax le_rfl hTδ) hy0
  have hyT : y T = poincare ξ := hyfl T ⟨hT.le, le_rfl⟩
  have hwin' : ∀ᶠ k in atTop,
      τ (φ (ψ k)) + (T + δ) * switchRadius X Λ₁ ΛR τ (φ (ψ k)) < b :=
    hψ.tendsto_atTop.eventually hwin
  have hcl : MapClusterPt (ang (poincare ξ)) atTop (switchAng X Λ₁ ΛR τ) := by
    rw [mapClusterPt_iff_frequently]
    intro U hU
    have hP : poincare ξ ≠ 0 := poincare_ne_zero hz
    have hcont : ContinuousAt ang (poincare ξ) :=
      continuousOn_ang.continuousAt (isOpen_ne.mem_nhds hP)
    obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.1 (hcont.preimage_mem_nhds hU)
    have hyc : ContinuousWithinAt y (Icc 0 (T + δ)) T :=
      continuousOn_pi.2 (fun j ↦ IsTrajectory.continuousOn subset_rfl htraj j) T ⟨hT.le, hTδ⟩
    obtain ⟨d, hd, hdy⟩ := Metric.continuousWithinAt_iff.1 hyc (η / 2) (by positivity)
    set ε := min (d / 2) (min (T / 2) (δ / 2)) with hεdef
    have hε : 0 < ε := lt_min (by positivity) (lt_min (by positivity) (by positivity))
    have hεd : ε < d := (min_le_left _ _).trans_lt (by linarith)
    have hεT : ε < T := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
    have hεδ : ε < δ := ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (by linarith)
    have hsw := l6i_forced_switch (n := fun k ↦ φ (ψ k)) h hz hwin' htraj hmax hy0 hint hwT
      hε hεT hεδ
    have hu := Metric.tendstoUniformlyOn_iff.1 hunif (η / 2) (by positivity)
    rw [Filter.frequently_atTop]
    intro N
    obtain ⟨k, ⟨⟨m, hm⟩, hku⟩, hkN⟩ := ((hsw.and hu).and (eventually_ge_atTop N)).exists
    set n₀ := φ (ψ k) with hn₀
    have hρ : 0 < switchRadius X Λ₁ ΛR τ n₀ := l6i_radius_pos h n₀
    have hlt : τ n₀ < τ m := by
      have := mul_pos (sub_pos.2 hεT) hρ
      linarith [hm.1]
    refine ⟨m, ?_, ?_⟩
    · have h1 : n₀ < m := h.2.2.2.2.1.lt_iff_lt.1 hlt
      have h2 : k ≤ n₀ := (hψ.id_le k).trans (hφ.id_le (ψ k))
      omega
    · set s := (τ m - τ n₀) / switchRadius X Λ₁ ΛR τ n₀ with hs
      have hse : τ n₀ + s * switchRadius X Λ₁ ΛR τ n₀ = τ m := by
        rw [hs, div_mul_cancel₀ _ hρ.ne']
        ring
      have hs1 : T - ε < s := by
        rw [hs, lt_div_iff₀ hρ]
        linarith [hm.1]
      have hs2 : s < T + ε := by
        rw [hs, div_lt_iff₀ hρ]
        linarith [hm.2]
      have hsI : s ∈ Icc 0 (T + δ) := ⟨by linarith, by linarith⟩
      have hds : dist s T < d := by
        rw [Real.dist_eq, abs_lt]
        constructor <;> linarith
      have h1 : dist (y s) (y T) < η / 2 := hdy hsI hds
      have h2 : dist (rescaledArc X Λ₁ ΛR τ n₀ s) (y s) < η / 2 := by
        rw [dist_comm]
        exact hku s hsI
      have h3 : rescaledArc X Λ₁ ΛR τ n₀ s ∈ Metric.ball (poincare ξ) η := by
        rw [Metric.mem_ball, ← hyT]
        calc dist (rescaledArc X Λ₁ ΛR τ n₀ s) (y T)
            ≤ dist (rescaledArc X Λ₁ ΛR τ n₀ s) (y s) + dist (y s) (y T) := dist_triangle _ _ _
          _ < η / 2 + η / 2 := add_lt_add h2 h1
          _ = η := by ring
      have h4 := hball h3
      rw [Set.mem_preimage, l6i_ang_arc h n₀ m hse] at h4
      exact h4
  obtain ⟨m, hm, hlim⟩ := hcl.tendsto_subseq
  exact ⟨m, hm.tendsto_atTop, hlim⟩

/-- **N5: the cluster set is forward invariant under the Fuller–Poincaré map** (the precise form of
the book's §16.4.2 claim "a continuous extension `F_i` of the Reinhardt–Poincaré map … The
restriction of each `𝒟_i^R` to the exceptional divisor `r = 0` is the previously defined
Fuller-system part `𝒟_i`", TeX 12970–12976, as the proof of Theorem 16.4.1 uses it, TeX
13036–13048): for every chattering arc into the singular locus, the set of cluster classes of its
switching points is mapped into itself by `F_ang`. -/
def ClusterSetForwardInvariant : Prop :=
  ∀ (a b : ℝ) (u : ℝ → Fin 3 → ℝ) (g X Λ₁ ΛR : ℝ → Mat2) (τ : ℕ → ℝ),
    IsChatteringArcInto a b u g X Λ₁ ΛR τ →
      MapsTo poincareAngZero (switchClusterSet (switchAng X Λ₁ ΛR τ))
        (switchClusterSet (switchAng X Λ₁ ΛR τ))

/-- **N5 holds** (step 4 of the plan in the module docstring, from
`exists_tendsto_switchAng_poincare`: a cluster point `ξ` gives the cluster point `ang (F ξ)`, in
the section, of class `F_ang([ξ])`).

Proof: `ang (F ξ)` is a cluster point (`exists_tendsto_switchAng_poincare`), so it lies in the
section (`mapClusterPt_switchAng_mem_sectionZero`), and its class is
`classOf (F ξ) = F_ang (classOf ξ)` (`classOf_smul_scale`, `poincareAngZero_classOf`). -/
theorem clusterSetForwardInvariant : ClusterSetForwardInvariant := by
  intro a b u g X Λ₁ ΛR τ h x hx
  obtain ⟨ξ, hξ0, rfl, hcl⟩ := hx
  obtain ⟨φ, hφ, hξ⟩ := hcl.tendsto_subseq
  obtain ⟨m, hm, hlim⟩ := exists_tendsto_switchAng_poincare h hφ hξ0 hξ
  have hcl' : MapClusterPt (ang (poincare ξ)) atTop (switchAng X Λ₁ ΛR τ) :=
    MapClusterPt.of_comp hm hlim.mapClusterPt
  refine ⟨ang (poincare ξ), mapClusterPt_switchAng_mem_sectionZero h hcl', ?_, hcl'⟩
  rw [poincareAngZero_classOf hξ0]
  have hP := poincare_mem_sectionZero hξ0
  have := classOf_smul_scale one_mem_VT (inv_pos.2 (weightedNorm_pos hP.1)) hP
  rw [one_smul] at this
  exact this

end SmoothedPolygons
