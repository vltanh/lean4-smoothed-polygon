module

public import SmoothedPolygons.Ch6.MatrixCostate
public import SmoothedPolygons.Ch6.MatrixMinimizer
public import SmoothedPolygons.Ch6.PeriodicExtension
public import External.Pontryagin
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# The global minimizer is a Pontryagin extremal (§6.2, §6.5, §6.6)

The book applies the Pontryagin maximum principle, cited from `zelikin2004control`
(Agrachev–Sachkov), to the Reinhardt control problem (Problem 3.6.2) on `SL₂(ℝ) × 𝔰𝔩₂(ℝ)`, with
the costate `(Λ₁, Λ₂)` read through the left trivialization of `T*SL₂(ℝ)` (Proposition 3.6.1) and
the trace form (§6.2, TeX 4662–4835); it computes the Hamiltonian (§6.4, Proposition 6.4.1) and
the costate equations in Lie-algebra form (Proposition 6.5.1, TeX 4999–5085), derives the
transversality conditions (6.6.1), the one for `Λ₁` from `g(t_f) = R` by Corollary 6.5.3
(§6.6 and Remark 6.6.1, TeX 5157–5242), and collects the result as Problem 6.7.1. Proposition
8.1.3 then says (TeX 6791) "We have seen that the global minimizer must be extremal". That
statement is `exists_isPontryaginExtremal_of_isReinhardtMinimizer`: every global minimizer of
Problem 3.6.2 (`IsReinhardtMinimizer`) lifts to a Pontryagin extremal (`IsPontryaginExtremal`).

## Route

The proof follows the book on the matrix system of `SmoothedPolygons/Ch6/MatrixSystem.lean`: the
state `q = (g, X)` lies in the open set `GL₂⁺(ℝ) × C` of `Mat₂(ℝ) × 𝔰𝔩₂(ℝ)`, `C` the open cone of
the star inequalities, on which `⟨Z_u, X⟩ < 0` for `u ∈ U_T` (Lemma 3.3.4), so that the dynamics
`g' = gX`, `X' = [P, X]` are smooth there.

1. A global minimizer of Problem 3.6.2 is a strong local minimizer of the matrix system
   (`IsReinhardtMinimizer.isStrongLocalMinimizer_matrix`,
   `SmoothedPolygons/Ch6/MatrixMinimizer.lean`; `det g` and `det X` are first integrals, so the
   competitors are Reinhardt trajectories).
2. The maximum principle (`External.pontryagin_maximum_principle`: free terminal time, integral
   cost, the boundary map `matrixBoundary` a submersion) gives `λ_cost = ν ≤ 0` and a Lipschitz
   covector curve `p` with `(ν, p(t)) ≠ 0`, the adjoint equation, the maximum condition, `H = 0`
   and transversality.
3. Translation (`isPontryaginExtremal_of_matrixCostate`), with the costates `Λ₁ = covectorΛ₁ q p`,
   the left trivialization `p g` made traceless, and `Λ_R = covectorΛR q p = [Λ₂, X]`
   (`SmoothedPolygons/Ch6/MatrixCostate.lean`):
   * the Hamiltonian of the maximum principle is `hamiltonian ν Λ₁ Λ_R X u`
     (§6.4, `controlHamiltonian_matrix_eq_hamiltonian`), so the maximum condition and `H = 0`
     transfer;
   * the adjoint equation is Hamilton's equations, the hypotheses of Proposition 6.5.1, whose
     conclusion gives the costate equations `Λ₁' = [Λ₁, X]` and `eqn:lamR` at almost every time
     (`hasDerivAt_covectorΛ_of_adjoint`), hence in integral form
     (`isIntegralCurve_covectorΛ_of_adjoint`: `q`, `p` are Lipschitz and `Λ₁`, `Λ_R` polynomial
     in `(q, p)`, so absolutely continuous);
   * transversality (§6.6): `Λ_R(t_f) = R⁻¹Λ_R(0)R` from the variations along which "the initial
     and terminal submanifolds coincide after rotation by `R`" (`covectorΛR_transversality`), and
     `Λ₁(t_f) = R⁻¹Λ₁(0)R` from `g(t_f) = R` by Corollary 6.5.3, as Remark 6.6.1 says
     (`remark6_6_1_lambda1`);
   * nontriviality of the reduced costate: if `ν = 0`, `Λ₁(t₀) = 0` and `Λ_R(t₀) = 0`, then
     `Λ₁ ≡ 0` (Corollary 6.5.3, `IsStateTrajectory.eq_conj_of_isIntegralCurve`), so the `Λ_R`
     equation is linear homogeneous, with coefficients bounded by Lemma 3.3.4, and `Λ_R ≡ 0`
     (`IsStateTrajectory.eq_zero_of_isIntegralCurve_costateRHS`); at `t_f` the covector `p(t_f)`
     then vanishes by the transversality conditions in the directions of the two boundary
     equations left out (`covector_transversality_dropped`, `eq_zero_of_covectorΛ_eq_zero`),
     against `(ν, p(t_f)) ≠ 0`.

The identity of Proposition 6.4.1 (for the left-trivialized costate, `⟨p, gX⟩ = ⟨Λ₁, X⟩`) is
checked in matrix coordinates, where it is the associativity `tr(p(gX)) = tr((pg)X)`, rather than
obtained from `proposition6_4_1`, which is stated for Mathlib's Lie groups; the reason is in the
docstring of `controlHamiltonian_matrix_eq_fullHamiltonian`. Likewise the trivialization of
Proposition 3.6.1 is written in matrix coordinates, `Λ₁ = pg`. The book's "smooth manifold" is
read as the open set `GL₂⁺(ℝ) × C`, with `g(0) = I₂` and `det X(0) = 1` (§3.5) as boundary
conditions, and its "closed control set" as the compact `U_T` (readings D1, D4 of
`External/Pontryagin.lean`).

## Departure from the paper

The only one (E21; see `SmoothedPolygons/Ch6/MatrixSystem.lean`): the maximum principle is applied
with the boundary condition of Problem 3.6.2 less the two equations of `g(t_f) = R` and
`X(t_f) = R⁻¹X(0)R` that the first integrals `det g`, `det X` make redundant. With the book's
boundary condition every admissible trajectory satisfies the conclusions of the maximum principle
with `λ_cost = 0` and `(p g, Λ₂) = (k I₂, 0)` or `(0, c X)`, whose reduced costate `(Λ₁, Λ_R)`
vanishes, so the nontriviality of the reduced costate cannot be derived; with the two equations
left out, transversality excludes these covectors.
-/

@[expose] public section

namespace SmoothedPolygons

open Set MeasureTheory Filter Matrix Pontryagin ControlSystem
open scoped NNReal

/-! ### Calculus tools -/

/-- **FTC for absolutely continuous functions**, in integral form: an absolutely continuous `f`
with derivative `v` at almost every point of `(0, T)` is the indefinite integral of `v`. -/
private lemma mxd_eq_add_integral {f v : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hf : AbsolutelyContinuousOnInterval f 0 T) (hd : ∀ᵐ t, t ∈ Ioo 0 T → HasDerivAt f (v t) t) :
    IntervalIntegrable v volume 0 T ∧ ∀ t ∈ Icc 0 T, f t = f 0 + ∫ s in (0 : ℝ)..t, v s := by
  have hae : ∀ᵐ t, t ∈ Ioc 0 T → deriv f t = v t := by
    have hT' : ∀ᵐ t : ℝ, t ≠ T := by simp [ae_iff, measure_singleton]
    filter_upwards [hd, hT'] with t ht htT htI
    exact (ht ⟨htI.1, lt_of_le_of_ne htI.2 htT⟩).deriv
  have hint : IntervalIntegrable v volume 0 T := by
    refine (hf.intervalIntegrable_deriv).congr_ae ?_
    rw [uIoc_of_le hT]
    exact (ae_restrict_iff' measurableSet_Ioc).2 hae
  refine ⟨hint, fun t ht ↦ ?_⟩
  have hsub : uIcc 0 t ⊆ uIcc 0 T := by
    rw [uIcc_of_le ht.1, uIcc_of_le hT]; exact Icc_subset_Icc_right ht.2
  have h := (hf.mono hsub).integral_deriv_eq_sub
  have h' : ∫ s in (0 : ℝ)..t, v s = ∫ s in (0 : ℝ)..t, deriv f s := by
    refine intervalIntegral.integral_congr_ae ?_
    rw [uIoc_of_le ht.1]
    filter_upwards [hae] with s hs hst
    exact (hs ⟨hst.1, hst.2.trans ht.2⟩).symm
  rw [h', h]
  ring

/-- A `C¹` function of a curve that is Lipschitz on `[0, T]` is absolutely continuous on
`[0, T]`. -/
private lemma mxd_absolutelyContinuous_comp {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {Γ : ℝ → F} {K : ℝ≥0} {T : ℝ} (hT : 0 ≤ T)
    (hΓ : LipschitzOnWith K Γ (Icc 0 T)) {h : F → ℝ} (hh : ContDiff ℝ 1 h) :
    AbsolutelyContinuousOnInterval (fun t ↦ h (Γ t)) 0 T := by
  have hc : IsCompact (Γ '' Icc 0 T) := isCompact_Icc.image_of_continuousOn hΓ.continuousOn
  obtain ⟨K', hK'⟩ := hh.locallyLipschitz.locallyLipschitzOn.exists_lipschitzOnWith_of_compact hc
  have hL : LipschitzOnWith (K' * K) (fun t ↦ h (Γ t)) (uIcc 0 T) := by
    rw [uIcc_of_le hT]
    exact hK'.comp hΓ (mapsTo_image _ _)
  exact hL.absolutelyContinuousOnInterval

/-- The entries of `Λ₁ = covectorΛ₁ q π` are smooth in `(q, π)`. -/
private lemma mxd_contDiff_covectorΛ₁ (i j : Fin 2) :
    ContDiff ℝ 1 (fun w : MatrixState × StrongDual ℝ MatrixState ↦ covectorΛ₁ w.1 w.2 i j) := by
  fin_cases i <;> fin_cases j <;>
    simp only [covectorΛ₁, covectorG, stateG, Matrix.trace_fin_two, Fin.isValue, Matrix.mul_apply,
      Matrix.of_apply, Fin.sum_univ_two, Fin.zero_eta, Fin.mk_one, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply_eq, Matrix.one_apply_ne, ne_eq, one_ne_zero,
      zero_ne_one, not_false_eq_true, smul_eq_mul, mul_one, mul_zero, sub_zero] <;>
    fun_prop

/-- The entries of `Λ_R = covectorΛR q π` are smooth in `(q, π)`. -/
private lemma mxd_contDiff_covectorΛR (i j : Fin 2) :
    ContDiff ℝ 1 (fun w : MatrixState × StrongDual ℝ MatrixState ↦ covectorΛR w.1 w.2 i j) := by
  fin_cases i <;> fin_cases j <;>
    simp only [covectorΛR, covectorΛ₂, stateX, slMatrix, Fin.isValue, Fin.zero_eta, Fin.mk_one,
      Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] <;>
    fun_prop

/-! ### The costate equations in integral form -/

/-- **The costate equations of Problem 6.7.1 in integral form.** Along the pair
`q(t) = (g(t), X(t))` of a Reinhardt state trajectory, a Lipschitz covector curve `p` solving the
adjoint equation of the maximum principle gives costates `Λ₁ = covectorΛ₁ q p` and
`Λ_R = covectorΛR q p` with `Λ₁' = [Λ₁, X]` and `Λ_R' = [P, Λ_R] - ⟨Λ_R, P⟩[P, X] +
[-Λ₁ + (3/2)λ_cost J, X]` in Carathéodory's sense.

Proof: at almost every time `q` and `p` are differentiable with `q' = f(q, u)` and the adjoint
equation (Lebesgue's differentiation theorem; `IsStateTrajectory.isAdmissibleIn_matrix`), where
`hasDerivAt_covectorΛ_of_adjoint` (Proposition 6.5.1) gives the derivatives; `q` (bounded field
on a compact set) and `p` are Lipschitz on `[0, t_f]` and `Λ₁`, `Λ_R` are polynomial in `(q, p)`,
so their entries are absolutely continuous, hence the integrals of their a.e. derivatives. -/
theorem isIntegralCurve_covectorΛ_of_adjoint {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsStateTrajectory T u g X) {ν : ℝ} {p : ℝ → StrongDual ℝ MatrixState}
    (hlip : ∃ K, LipschitzOnWith K p (Icc 0 T))
    (hA : IsAdjoint matrixField matrixCost ν u (fun t ↦ toMatrixState (g t) (X t)) T p) :
    IsIntegralCurve (fun t ↦ covectorΛ₁ (toMatrixState (g t) (X t)) (p t))
        (fun t ↦ covectorΛ₁ (toMatrixState (g t) (X t)) (p t) * X t -
          X t * covectorΛ₁ (toMatrixState (g t) (X t)) (p t)) T ∧
      IsIntegralCurve (fun t ↦ covectorΛR (toMatrixState (g t) (X t)) (p t))
        (fun t ↦ costateRHS ν (covectorΛ₁ (toMatrixState (g t) (X t)) (p t))
          (covectorΛR (toMatrixState (g t) (X t)) (p t)) (X t) (u t)) T := by
  set q : ℝ → MatrixState := fun t ↦ toMatrixState (g t) (X t) with hqdef
  have hadm := h.isAdmissibleIn_matrix
  have hT0 : 0 < T := h.1
  have hIcc : ∀ {t : ℝ}, t ∈ Ioo 0 T → t ∈ Icc 0 T := fun ht ↦ Ioo_subset_Icc_self ht
  have hdom : ∀ t ∈ Icc 0 T, q t ∈ matrixDomain := hadm.2
  have huU : ∀ t ∈ Icc 0 T, u t ∈ controlSimplex := hadm.1.2.1
  have hXq : ∀ t ∈ Icc 0 T, stateX (q t) = X t := fun t ht ↦
    stateX_toMatrixState _ (h.2.2.2.1 t ht).2.1
  -- `q` (a bounded field on a compact set) and `p` are Lipschitz on `[0, T]`, so the entries of
  -- the costates, smooth in `(q, p)`, are absolutely continuous
  obtain ⟨Kp, hKp⟩ := hlip
  have hKq : IsCompact ((q '' Icc 0 T) ×ˢ controlSimplex) :=
    (isCompact_Icc.image_of_continuousOn hadm.1.2.2.1).prod isCompact_controlSimplex
  obtain ⟨M, hM⟩ := hKq.exists_bound_of_continuousOn (isC1On_matrixField.continuousOn.mono (by
    rintro ⟨_, v⟩ ⟨⟨s, hs, rfl⟩, hv⟩
    exact ⟨hdom s hs, hv⟩))
  have hqlip : LipschitzOnWith (Real.toNNReal M) q (Icc 0 T) := by
    refine LipschitzOnWith.of_dist_le_mul fun a ha b hb ↦ ?_
    rw [dist_eq_norm, Real.dist_eq]
    refine (hadm.1.norm_sub_le (fun s hs ↦ hM (q s, u s) ⟨⟨s, hs, rfl⟩, huU s hs⟩) hb ha).trans ?_
    exact mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal M) (abs_nonneg _)
  have hac : ∀ F : MatrixState × StrongDual ℝ MatrixState → ℝ, ContDiff ℝ 1 F →
      AbsolutelyContinuousOnInterval (fun t ↦ F (q t, p t)) 0 T :=
    fun F hF ↦ mxd_absolutelyContinuous_comp hT0.le (hqlip.prodMk hKp) hF
  -- almost everywhere, `q` and `p` are differentiable, with `q' = f(q, u)` and the adjoint
  -- equation (Lebesgue's differentiation theorem)
  have hq' : ∀ᵐ t, t ∈ Ioo 0 T → HasDerivAt q (matrixField (q t) (u t)) t :=
    ae_hasDerivAt_of_eq_add_integral hadm.1.2.2.2.1 ⟨le_rfl, hT0.le⟩ hadm.1.2.2.2.2
  have hp' : ∀ᵐ t, t ∈ Ioo 0 T →
      HasDerivAt p (-((p t).comp (fderiv ℝ (matrixField · (u t)) (q t)) +
        ν • fderiv ℝ (matrixCost · (u t)) (q t))) t := by
    refine ae_hasDerivAt_of_eq_add_integral
      (v := fun r ↦ -((p r).comp (linearization matrixField u q r) +
        ν • fderiv ℝ (matrixCost · (u r)) (q r))) hA.1.neg ⟨hT0.le, le_rfl⟩ (a := p T)
      fun t ht ↦ ?_
    rw [hA.2 t ht, intervalIntegral.integral_neg, intervalIntegral.integral_symm]
  -- there Proposition 6.5.1 gives the derivatives of the costates
  have hd : ∀ᵐ t, t ∈ Ioo 0 T →
      HasDerivAtEntrywise (fun s ↦ covectorΛ₁ (q s) (p s))
        (covectorΛ₁ (q t) (p t) * X t - X t * covectorΛ₁ (q t) (p t)) t ∧
      HasDerivAtEntrywise (fun s ↦ covectorΛR (q s) (p s))
        (costateRHS ν (covectorΛ₁ (q t) (p t)) (covectorΛR (q t) (p t)) (X t) (u t)) t := by
    filter_upwards [hq', hp'] with t hqt hpt htI
    rw [← hXq t (hIcc htI)]
    exact hasDerivAt_covectorΛ_of_adjoint (hdom t (hIcc htI)) (huU t (hIcc htI)) (hqt htI)
      (hpt htI)
  -- in integral form (FTC for absolutely continuous functions)
  refine ⟨fun i j ↦ ?_, fun i j ↦ ?_⟩
  · refine mxd_eq_add_integral (f := fun t ↦ covectorΛ₁ (q t) (p t) i j) hT0.le
      (hac (fun w ↦ covectorΛ₁ w.1 w.2 i j) (mxd_contDiff_covectorΛ₁ i j)) ?_
    filter_upwards [hd] with t ht htI using (ht htI).1 i j
  · refine mxd_eq_add_integral (f := fun t ↦ covectorΛR (q t) (p t) i j) hT0.le
      (hac (fun w ↦ covectorΛR w.1 w.2 i j) (mxd_contDiff_covectorΛR i j)) ?_
    filter_upwards [hd] with t ht htI using (ht htI).2 i j

/-! ### Nontriviality of the reduced costate -/

/-- **Corollary 6.5.3** (`cor:lam1-gen-sol`) for Carathéodory solutions: if `g' = gX` with
`g(0) = I₂` and `Λ₁' = [Λ₁, X]` (integral form), then `Λ₁(t) = g(t)⁻¹Λ₁(0)g(t)` on `[0, t_f]`.

Proof as for `remark6_6_1_lambda1`: the integrands `gX` and `[Λ₁, X]` are continuous, so `g`
and `Λ₁` are differentiable on `[0, t_f]` (FTC-1), and `corollary6_5_3` applies. -/
theorem IsStateTrajectory.eq_conj_of_isIntegralCurve {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X Λ₁ : ℝ → Mat2} (h : IsStateTrajectory T u g X) (hg0 : g 0 = 1)
    (hΛ : IsIntegralCurve Λ₁ (fun t ↦ Λ₁ t * X t - X t * Λ₁ t) T) :
    ∀ t ∈ Icc 0 T, Λ₁ t = (g t)⁻¹ * Λ₁ 0 * g t := by
  obtain ⟨-, -, -, hst, hgI, hXI⟩ := h
  -- the integrands are continuous, so the integral curves are differentiable (FTC-1)
  have hXc : ContinuousOn X (Icc 0 T) := Matrix.continuousOn_of_eq_add_integral hXI
  have hgc : ContinuousOn g (Icc 0 T) := Matrix.continuousOn_of_eq_add_integral hgI
  have hΛc : ContinuousOn Λ₁ (Icc 0 T) := Matrix.continuousOn_of_eq_add_integral hΛ
  have hg : ∀ t ∈ Icc 0 T, Matrix.HasDerivWithinAtEntrywise g (g t * X t) (Icc 0 T) t :=
    fun t ht ↦ Matrix.hasDerivWithinAtEntrywise_of_eq_add_integral hgI ht ((hgc.mul hXc) t ht)
  have hΛ' : ∀ t ∈ Icc 0 T,
      Matrix.HasDerivWithinAtEntrywise Λ₁ (Λ₁ t * X t - X t * Λ₁ t) (Icc 0 T) t :=
    fun t ht ↦ Matrix.hasDerivWithinAtEntrywise_of_eq_add_integral hΛ ht
      (((hΛc.mul hXc).sub (hXc.mul hΛc)) t ht)
  -- Corollary 6.5.3
  exact fun t ht ↦ (corollary6_5_3 T g X Λ₁ hg hg0 (fun s hs ↦ (hst s hs).1) hΛ' t ht).1

/-- Gronwall's inequality forward and backward from `s ∈ [c, d]`: if `φ ≥ 0` is continuous on
`[c, d]` and `φ(t) ≤ C + L |∫ₛᵗ φ|` there, then `φ(t) ≤ C e^{L|t - s|}`. (The private lemma
`le_mul_exp_abs_of_le_add_abs_integral` of `OptimalControl/ODE/Caratheodory.lean`, from
`ControlSystem.le_mul_exp_of_le_add_integral` applied forward and to `r ↦ φ(-r)`.) -/
private lemma mxd_le_mul_exp_abs_of_le_add_abs_integral {φ : ℝ → ℝ} {c d s C L : ℝ}
    (hL : 0 ≤ L) (hs : s ∈ Icc c d) (hφ : ContinuousOn φ (Icc c d))
    (hφ0 : ∀ t ∈ Icc c d, 0 ≤ φ t) (h : ∀ t ∈ Icc c d, φ t ≤ C + L * |∫ r in s..t, φ r|) :
    ∀ t ∈ Icc c d, φ t ≤ C * Real.exp (L * |t - s|) := by
  intro t ht
  rcases le_total s t with hst | hts
  · have hsub : Icc s d ⊆ Icc c d := Icc_subset_Icc_left hs.1
    have := le_mul_exp_of_le_add_integral (a := s) (b := d) hL (hφ.mono hsub)
      (fun r hr ↦ hφ0 r (hsub hr)) (fun r hr ↦ by
        have hnn : 0 ≤ ∫ q in s..r, φ q := intervalIntegral.integral_nonneg hr.1
          fun q hq ↦ hφ0 q ⟨hs.1.trans hq.1, hq.2.trans hr.2⟩
        simpa [abs_of_nonneg hnn] using h r (hsub hr)) t ⟨hst, ht.2⟩
    rwa [abs_of_nonneg (sub_nonneg.2 hst)]
  · have hmem : ∀ r ∈ Icc (-s) (-c), -r ∈ Icc c d := fun r hr ↦
      ⟨by linarith [hr.2], by linarith [hr.1, hs.2]⟩
    have := le_mul_exp_of_le_add_integral (φ := fun r ↦ φ (-r)) (a := -s) (b := -c) hL
      (hφ.comp continuous_neg.continuousOn hmem) (fun r hr ↦ hφ0 _ (hmem r hr))
      (fun r hr ↦ by
        have h1 := h (-r) (hmem r hr)
        have hnn : 0 ≤ ∫ q in -r..s, φ q := intervalIntegral.integral_nonneg
          (by linarith [hr.1]) fun q hq ↦ hφ0 q ⟨(hmem r hr).1.trans hq.1, hq.2.trans hs.2⟩
        rw [intervalIntegral.integral_symm, abs_neg, abs_of_nonneg hnn] at h1
        rw [intervalIntegral.integral_comp_neg, neg_neg]
        exact h1) (-t) ⟨neg_le_neg hts, neg_le_neg ht.1⟩
    rw [abs_of_nonpos (sub_nonpos.2 hts)]
    simp only [neg_neg] at this
    convert this using 3
    ring

/-- The sum `∑ₖₗ |Aₖₗ|` of the absolute values of the entries of a `2 × 2` matrix. -/
private noncomputable def mxd_S (A : Mat2) : ℝ := ∑ k, ∑ l, |A k l|

private lemma mxd_S_nonneg (A : Mat2) : 0 ≤ mxd_S A := by
  unfold mxd_S; positivity

private lemma mxd_abs_le_S (A : Mat2) (i j : Fin 2) : |A i j| ≤ mxd_S A :=
  (Finset.single_le_sum (fun l _ ↦ abs_nonneg (A i l)) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun k ↦ ∑ l, |A k l|) (fun _ _ ↦ by positivity)
      (Finset.mem_univ i))

private lemma mxd_continuous_S : Continuous mxd_S :=
  continuous_finsetSum _ fun k _ ↦ continuous_finsetSum _ fun l _ ↦
    (continuous_id.matrix_elem k l).abs

private lemma mxd_S_add (A B : Mat2) : mxd_S (A + B) ≤ mxd_S A + mxd_S B := by
  unfold mxd_S
  rw [← Finset.sum_add_distrib]
  gcongr with k _
  rw [← Finset.sum_add_distrib]
  gcongr with l _
  exact abs_add_le _ _

private lemma mxd_S_sub (A B : Mat2) : mxd_S (A - B) ≤ mxd_S A + mxd_S B := by
  unfold mxd_S
  rw [← Finset.sum_add_distrib]
  gcongr with k _
  rw [← Finset.sum_add_distrib]
  gcongr with l _
  exact abs_sub _ _

private lemma mxd_S_smul (c : ℝ) (A : Mat2) : mxd_S (c • A) = |c| * mxd_S A := by
  simp only [mxd_S, Matrix.smul_apply, smul_eq_mul, abs_mul, Finset.mul_sum]

private lemma mxd_S_mul (A B : Mat2) : mxd_S (A * B) ≤ mxd_S A * mxd_S B := by
  calc mxd_S (A * B) ≤ ∑ i, ∑ j, ∑ k, |A i k| * |B k j| := by
        unfold mxd_S
        gcongr with i _ j _
        rw [Matrix.mul_apply]
        exact (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (by simp [abs_mul]))
    _ = ∑ i, ∑ k, |A i k| * ∑ j, |B k j| := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
    _ ≤ ∑ i, ∑ k, |A i k| * mxd_S B := by
        gcongr with i _ k _
        exact Finset.single_le_sum (f := fun k ↦ ∑ j, |B k j|) (fun _ _ ↦ by positivity)
          (Finset.mem_univ k)
    _ = mxd_S A * mxd_S B := by
        simp only [mxd_S, Finset.sum_mul]

private lemma mxd_abs_traceForm_le (A B : Mat2) : |traceForm A B| ≤ mxd_S A * mxd_S B := by
  refine le_trans ?_ (mxd_S_mul A B)
  rw [traceForm, Matrix.trace]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  exact Finset.sum_le_sum fun i _ ↦ Finset.single_le_sum (f := fun j ↦ |(A * B) i j|)
    (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ i)

/-- The control matrix `Z_u` depends continuously on `u`. -/
private lemma mxd_continuous_controlMatrix : Continuous controlMatrix := by
  unfold controlMatrix
  refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
  fin_cases i <;> fin_cases j <;> dsimp <;> fun_prop

/-- **Uniqueness for linear Carathéodory equations** (Grönwall): a solution of `Λ' = v` in
integral form on `[0, T]` with `|vᵢⱼ(t)| ≤ K ∑ₖₗ |Λₖₗ(t)|` that vanishes at one time vanishes
identically. -/
theorem IsIntegralCurve.eq_zero_of_abs_le {Λ v : ℝ → Mat2} {T K : ℝ} (h : IsIntegralCurve Λ v T)
    (hv : ∀ t ∈ Icc 0 T, ∀ i j, |v t i j| ≤ K * ∑ k, ∑ l, |Λ t k l|) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Icc 0 T) (h0 : Λ t₀ = 0) : ∀ t ∈ Icc 0 T, Λ t = 0 := by
  have hc : ContinuousOn Λ (Icc 0 T) := Matrix.continuousOn_of_eq_add_integral h
  -- `φ = ∑ₖₗ |Λₖₗ|` is continuous and `|vᵢⱼ| ≤ K' φ` with `K' = max K 0 ≥ 0`
  set φ : ℝ → ℝ := fun t ↦ mxd_S (Λ t) with hφ
  have hφc : ContinuousOn φ (Icc 0 T) := mxd_continuous_S.comp_continuousOn hc
  have hφ0 : ∀ t, 0 ≤ φ t := fun t ↦ mxd_S_nonneg _
  set K' := max K 0 with hK'def
  have hK' : 0 ≤ K' := le_max_right _ _
  have hv' : ∀ t ∈ Icc 0 T, ∀ i j, |v t i j| ≤ K' * φ t := fun t ht i j ↦
    (hv t ht i j).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hφ0 t))
  -- `Λ(t) = ∫_{t₀}^t v`, so `|Λᵢⱼ(t)| ≤ K' |∫_{t₀}^t φ|`
  have hentry : ∀ t ∈ Icc 0 T, ∀ i j, |Λ t i j| ≤ K' * |∫ s in t₀..t, φ s| := by
    intro t ht i j
    have hsub : uIcc t₀ t ⊆ Icc 0 T := uIcc_subset_Icc ht₀ ht
    have hint : ∀ {r}, r ∈ Icc 0 T → IntervalIntegrable (fun s ↦ v s i j) volume 0 r :=
      fun hr ↦ (h i j).1.mono_set (uIcc_subset_uIcc left_mem_uIcc (Icc_subset_uIcc hr))
    have hΛt : Λ t i j = ∫ s in t₀..t, v s i j := by
      have e1 := (h i j).2 t ht
      have e2 := (h i j).2 t₀ ht₀
      have hz : Λ t₀ i j = 0 := by rw [h0]; rfl
      rw [← intervalIntegral.integral_interval_sub_left (hint ht) (hint ht₀)]
      linarith
    rw [hΛt, intervalIntegral.abs_integral_eq_abs_integral_uIoc,
      intervalIntegral.abs_integral_eq_abs_integral_uIoc]
    have hφint : IntegrableOn φ (uIoc t₀ t) :=
      (hφc.integrableOn_Icc).mono_set (uIoc_subset_uIcc.trans hsub)
    have hnn : 0 ≤ ∫ s in uIoc t₀ t, φ s := setIntegral_nonneg_of_ae (Eventually.of_forall
      fun s ↦ hφ0 s)
    rw [abs_of_nonneg hnn, ← integral_const_mul, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le (hφint.const_mul K')
      (ae_restrict_of_forall_mem measurableSet_uIoc fun s hs ↦ ?_)
    rw [Real.norm_eq_abs]
    exact hv' s (hsub (uIoc_subset_uIcc hs)) i j
  have hle : ∀ t ∈ Icc 0 T, φ t ≤ 0 + 4 * K' * |∫ s in t₀..t, φ s| := by
    intro t ht
    have hφt : φ t = |Λ t 0 0| + |Λ t 0 1| + (|Λ t 1 0| + |Λ t 1 1|) := by
      simp [hφ, mxd_S, Fin.sum_univ_two]
    rw [hφt]
    linarith [hentry t ht 0 0, hentry t ht 0 1, hentry t ht 1 0, hentry t ht 1 1]
  -- Grönwall, forward and backward from `t₀`
  have hG := mxd_le_mul_exp_abs_of_le_add_abs_integral (by positivity : 0 ≤ 4 * K') ht₀ hφc
    (fun t _ ↦ hφ0 t) hle
  intro t ht
  have hφt : φ t ≤ 0 := by simpa using hG t ht
  ext i j
  exact abs_nonpos_iff.1 ((mxd_abs_le_S (Λ t) i j).trans hφt)

/-- With `λ_cost = 0` and `Λ₁ = 0` on `[0, t_f]`, the costate equation `eqn:lamR`,
`Λ_R' = [P, Λ_R] - ⟨Λ_R, P⟩[P, X]`, is linear homogeneous with bounded coefficients
(`P = Z_u/⟨Z_u, X⟩`, the denominator bounded away from `0` on the compact set
`X([0, t_f]) × U_T` by Lemma 3.3.4); so a solution vanishing at one time vanishes identically
(`IsIntegralCurve.eq_zero_of_abs_le`). -/
theorem IsStateTrajectory.eq_zero_of_isIntegralCurve_costateRHS {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X : ℝ → Mat2} (h : IsStateTrajectory T u g X) {Λ₁ ΛR : ℝ → Mat2}
    (hΛ₁ : ∀ t ∈ Icc 0 T, Λ₁ t = 0)
    (hΛ : IsIntegralCurve ΛR (fun t ↦ costateRHS 0 (Λ₁ t) (ΛR t) (X t) (u t)) T) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Icc 0 T) (h0 : ΛR t₀ = 0) : ∀ t ∈ Icc 0 T, ΛR t = 0 := by
  obtain ⟨-, -, hu, hst, -, hXI⟩ := h
  have hXc : ContinuousOn X (Icc 0 T) := Matrix.continuousOn_of_eq_add_integral hXI
  -- `∑ₖₗ |Xₖₗ| ≤ C_X` on `[0, t_f]`
  obtain ⟨CX, hCX⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (mxd_continuous_S.comp_continuousOn hXc)
  -- `∑ₖₗ |Pₖₗ| ≤ C_P` on the compact set `X([0, t_f]) × U_T`, where `⟨Z_u, X⟩ < 0`
  -- (Lemma 3.3.4), so that `P = Z_u/⟨Z_u, X⟩` is continuous there
  have hK : IsCompact ((X '' Icc 0 T) ×ˢ controlSimplex) :=
    (isCompact_Icc.image_of_continuousOn hXc).prod isCompact_controlSimplex
  have hZ := mxd_continuous_controlMatrix
  have hPc : ContinuousOn (fun w : Mat2 × (Fin 3 → ℝ) ↦ mxd_S (controlP w.2 w.1))
      ((X '' Icc 0 T) ×ˢ controlSimplex) := by
    have hZ2 : Continuous fun w : Mat2 × (Fin 3 → ℝ) ↦ controlMatrix w.2 :=
      hZ.comp continuous_snd
    refine mxd_continuous_S.comp_continuousOn ?_
    unfold controlP
    refine ContinuousOn.smul (f := fun w : Mat2 × (Fin 3 → ℝ) ↦
      (traceForm (controlMatrix w.2) w.1)⁻¹) ?_ hZ2.continuousOn
    refine ContinuousOn.inv₀ ?_ fun w hw ↦ ?_
    · exact (hZ2.matrix_mul continuous_fst).matrix_trace.continuousOn
    · obtain ⟨⟨s, hs, hsw⟩, hw2⟩ := hw
      rw [← hsw]
      exact ((lemma3_3_4 (X s) (hst s hs).2.1).1 (hst s hs).2.2.2 w.2 hw2).ne
  obtain ⟨CP, hCP⟩ := hK.exists_bound_of_continuousOn hPc
  -- with `λ_cost = 0` and `Λ₁ = 0`, `|(Λ_R')ᵢⱼ| ≤ (2 C_P + 2 C_P² C_X) ∑ₖₗ |Λ_R ₖₗ|`
  refine IsIntegralCurve.eq_zero_of_abs_le hΛ (K := 2 * CP + 2 * CP * CP * CX) ?_ ht₀ h0
  intro t ht i j
  show |costateRHS 0 (Λ₁ t) (ΛR t) (X t) (u t) i j| ≤ _
  set P := controlP (u t) (X t) with hP
  have hSP : mxd_S P ≤ CP :=
    (Real.le_norm_self _).trans (hCP (X t, u t) ⟨⟨t, ht, rfl⟩, hu t ht⟩)
  have hSX : mxd_S (X t) ≤ CX := (Real.le_norm_self _).trans (hCX t ht)
  have e : costateRHS 0 (Λ₁ t) (ΛR t) (X t) (u t) =
      (P * ΛR t - ΛR t * P) - traceForm (ΛR t) P • (P * X t - X t * P) := by
    rw [hΛ₁ t ht]
    simp only [costateRHS, neg_zero, mul_zero, zero_smul, add_zero, zero_mul, sub_zero]
    rfl
  have h0P := mxd_S_nonneg P
  have h0X := mxd_S_nonneg (X t)
  have h0L := mxd_S_nonneg (ΛR t)
  have hCP0 : 0 ≤ CP := h0P.trans hSP
  have hbr : ∀ A B : Mat2, mxd_S (A * B - B * A) ≤ mxd_S A * mxd_S B + mxd_S B * mxd_S A :=
    fun A B ↦ (mxd_S_sub _ _).trans (add_le_add (mxd_S_mul _ _) (mxd_S_mul _ _))
  rw [e]
  calc _ ≤ mxd_S ((P * ΛR t - ΛR t * P) - traceForm (ΛR t) P • (P * X t - X t * P)) :=
        mxd_abs_le_S _ i j
    _ ≤ (mxd_S P * mxd_S (ΛR t) + mxd_S (ΛR t) * mxd_S P) +
        (mxd_S (ΛR t) * mxd_S P) * (mxd_S P * mxd_S (X t) + mxd_S (X t) * mxd_S P) := by
        refine (mxd_S_sub _ _).trans (add_le_add (hbr _ _) ?_)
        rw [mxd_S_smul]
        exact mul_le_mul (mxd_abs_traceForm_le _ _) (hbr _ _) (mxd_S_nonneg _) (by positivity)
    _ = (2 * mxd_S P + 2 * mxd_S P * mxd_S P * mxd_S (X t)) * mxd_S (ΛR t) := by ring
    _ ≤ (2 * CP + 2 * CP * CP * CX) * mxd_S (ΛR t) := by gcongr

/-! ### The translation -/

/-- **Translation of the costate.** Let `(u, g, X)` be an admissible trajectory of Problem 3.6.2,
`q(t) = (g(t), X(t))` its pair in the matrix system, and `(ν, p)` a multiplier and covector curve
satisfying the conclusions of the maximum principle for the matrix system with the boundary map
`matrixBoundary`. Then the costates `Λ₁ = covectorΛ₁ q p` and `Λ_R = covectorΛR q p` make
`(u, g, X, Λ₁, Λ_R, ν)` a Pontryagin extremal.

Proof (see the module docstring, step 3): the costate equations by
`isIntegralCurve_covectorΛ_of_adjoint` (Proposition 6.5.1); transversality by
`remark6_6_1_lambda1` and `covectorΛR_transversality`; the maximum condition and `H = 0` by
`controlHamiltonian_matrix_eq_hamiltonian`; nontriviality: if `ν = 0`, `Λ₁(t₀) = 0` and
`Λ_R(t₀) = 0`, then `Λ₁ ≡ 0` (Corollary 6.5.3, `IsStateTrajectory.eq_conj_of_isIntegralCurve`)
and `Λ_R ≡ 0` (`IsStateTrajectory.eq_zero_of_isIntegralCurve_costateRHS`), so `p(t_f) = 0` by
`covector_transversality_dropped` and `eq_zero_of_covectorΛ_eq_zero` (`g(t_f) = R`, and
`X(t_f)₀₁ < 0` by `stateX_zero_one_neg`), against `(ν, p(t_f)) ≠ 0`. -/
theorem isPontryaginExtremal_of_matrixCostate {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsReinhardtAdmissible T u g X) {ν : ℝ} {p : ℝ → StrongDual ℝ MatrixState}
    (hν : ν ≤ 0) (hlip : ∃ K, LipschitzOnWith K p (Icc 0 T)) (hN : ∀ t ∈ Icc 0 T, (ν, p t) ≠ 0)
    (hA : IsAdjoint matrixField matrixCost ν u (fun t ↦ toMatrixState (g t) (X t)) T p)
    (hM : IsMaximal matrixField matrixCost ν controlSimplex u
      (fun t ↦ toMatrixState (g t) (X t)) T p)
    (hZ : ∀ᵐ t ∂(volume.restrict (Icc 0 T)),
      controlHamiltonian matrixField matrixCost ν (toMatrixState (g t) (X t)) (p t) (u t) = 0)
    (hT : ∀ v w : MatrixState, fderiv ℝ matrixBoundary
      (toMatrixState (g 0) (X 0), toMatrixState (g T) (X T)) (v, w) = 0 → -p 0 v + p T w = 0) :
    IsPontryaginExtremal T u g X (fun t ↦ covectorΛ₁ (toMatrixState (g t) (X t)) (p t))
      (fun t ↦ covectorΛR (toMatrixState (g t) (X t)) (p t)) ν := by
  obtain ⟨hst, hg0, hgT, hXT⟩ := h
  have hT0 : 0 < T := hst.1
  have h0m : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT0.le⟩
  have hTm : T ∈ Icc 0 T := ⟨hT0.le, le_rfl⟩
  have hXq : ∀ t ∈ Icc 0 T, stateX (toMatrixState (g t) (X t)) = X t := fun t ht ↦
    stateX_toMatrixState _ (hst.2.2.2.1 t ht).2.1
  obtain ⟨hΛ₁, hΛR⟩ := isIntegralCurve_covectorΛ_of_adjoint hst hlip hA
  obtain ⟨hG11, hΛ01⟩ := covector_transversality_dropped hT
  refine ⟨hst, hg0, hgT, hXT, remark6_6_1_lambda1 hst hg0 hgT hΛ₁, ?_, hν, ?_, hΛ₁, hΛR, ?_⟩
  · -- transversality for `Λ_R` (§6.6)
    exact covectorΛR_transversality hT (by rw [hXq T hTm, hXq 0 h0m, hXT])
  · intro t ht
    refine ⟨trace_covectorΛ₁ _ _, trace_covectorΛR _ _, ?_, ?_⟩
    · rw [← hXq t ht]
      exact traceForm_covectorΛR_stateX _ _
    -- nontriviality of the reduced costate
    by_contra hcon
    push Not at hcon
    obtain ⟨hν0, h1, h2⟩ := hcon
    subst hν0
    -- `Λ₁ ≡ 0` by Corollary 6.5.3
    have hconj := hst.eq_conj_of_isIntegralCurve hg0 hΛ₁
    have hdet : IsUnit (g t).det := by rw [(hst.2.2.2.1 t ht).1]; exact isUnit_one
    have hΛ₁0 : covectorΛ₁ (toMatrixState (g 0) (X 0)) (p 0) = 0 := by
      have e := congrArg (fun M ↦ g t * M * (g t)⁻¹) (hconj t ht)
      simp only [h1, Matrix.mul_zero, Matrix.zero_mul] at e
      rw [e, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet,
        Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
    have hΛ₁z : ∀ s ∈ Icc 0 T, covectorΛ₁ (toMatrixState (g s) (X s)) (p s) = 0 := fun s hs ↦ by
      rw [hconj s hs, hΛ₁0, Matrix.mul_zero, Matrix.zero_mul]
    -- `Λ_R ≡ 0` by uniqueness for the linear `Λ_R` equation
    have hΛRz := hst.eq_zero_of_isIntegralCurve_costateRHS hΛ₁z hΛR ht h2
    -- at `t_f`, the covector vanishes
    have hXT' : stateX (toMatrixState (g T) (X T)) 0 1 ≠ 0 :=
      (stateX_zero_one_neg (hst.isAdmissibleIn_matrix.2 T hTm)).ne
    apply hN T hTm
    rw [eq_zero_of_covectorΛ_eq_zero (q := toMatrixState (g T) (X T)) hgT hXT' (hΛ₁z T hTm)
      (hΛRz T hTm) hG11 hΛ01]
    rfl
  · -- the maximum condition and `H = 0`
    filter_upwards [(ae_restrict_iff' measurableSet_Icc).1 hM,
      (ae_restrict_iff' measurableSet_Icc).1 hZ] with t hMt hZt htI
    have ht := Ioo_subset_Icc_self htI
    have hH : ∀ v, hamiltonian ν (covectorΛ₁ (toMatrixState (g t) (X t)) (p t))
        (covectorΛR (toMatrixState (g t) (X t)) (p t)) (X t) v =
          controlHamiltonian matrixField matrixCost ν (toMatrixState (g t) (X t)) (p t) v :=
      fun v ↦ by rw [controlHamiltonian_matrix_eq_hamiltonian, hXq t ht]
    refine ⟨by rw [hH]; exact hZt ht, fun v hv ↦ ?_⟩
    rw [hH, hH]
    exact hMt ht v hv

/-- **The global minimizer is a Pontryagin extremal** (`sec:PMP`, label of this formalization:
§6.2 and §6.6 of the book, TeX 4662–4835 and 5157–5242, summarized in Problem 6.7.1 and used in
the proof of Proposition 8.1.3, TeX 6791: "We have seen that the global minimizer must be
extremal"). Every global minimizer `(u, g, X)` of the Reinhardt control problem (Problem 3.6.2)
lifts to a Pontryagin extremal: there are costates `Λ₁, Λ_R` and a multiplier `λ_cost ≤ 0` with
the state–costate equations of Problem 6.7.1, the maximum condition and `H = 0` almost
everywhere, the nontriviality `(λ_cost, Λ₁, Λ_R) ≠ 0` at every time, and the transversality
conditions (6.6.1).

The proof follows the book's route (see the module docstring): the maximum principle on
`SL₂(ℝ) × 𝔰𝔩₂(ℝ)`, read as the open set `GL₂⁺(ℝ) × C` of the matrix system, the costate
equations by Proposition 6.5.1, and the transversality conditions of §6.6, the one for `Λ₁` by
Corollary 6.5.3 (Remark 6.6.1).

Departure from the paper (E21): the maximum principle is applied with the boundary condition less
the two equations made redundant by the first integrals `det g`, `det X` (`matrixBoundary`),
since with them it admits, for every admissible trajectory, covectors whose reduced costate
vanishes, and the nontriviality of `(λ_cost, Λ₁, Λ_R)` would not follow.

Proof: `IsReinhardtMinimizer.isStrongLocalMinimizer_matrix`,
`External.pontryagin_maximum_principle` (with `isOpen_matrixDomain`, `isCompact_controlSimplex`,
`isC1On_matrixField`, `isC1On_matrixCost`, `contDiff_matrixBoundary`,
`surjective_fderiv_matrixBoundary`), and `isPontryaginExtremal_of_matrixCostate`. -/
theorem exists_isPontryaginExtremal_of_isReinhardtMinimizer {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X : ℝ → Mat2} (h : IsReinhardtMinimizer T u g X) :
    ∃ (Λ₁ ΛR : ℝ → Mat2) (lam : ℝ), IsPontryaginExtremal T u g X Λ₁ ΛR lam := by
  have hmin := h.isStrongLocalMinimizer_matrix
  have h0 : toMatrixState (g 0) (X 0) ∈ matrixDomain := hmin.2.1.2 0 ⟨le_rfl, hmin.1.le⟩
  obtain ⟨ν, p, hν, hlip, hN, hA, hM, hZ, hT⟩ :=
    External.pontryagin_maximum_principle isOpen_matrixDomain isCompact_controlSimplex
      isC1On_matrixField isC1On_matrixCost hmin contDiff_matrixBoundary.contDiffAt
      (surjective_fderiv_matrixBoundary
        (w := (toMatrixState (g 0) (X 0), toMatrixState (g T) (X T))) h0)
      hmin.2.2.1 (Eventually.of_forall fun _ hz ↦ hz)
  exact ⟨_, _, ν, isPontryaginExtremal_of_matrixCostate h.1 hν hlip hN hA hM hZ hT⟩

end SmoothedPolygons
