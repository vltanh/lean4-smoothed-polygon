module

public import SmoothedPolygons.Ch6.MatrixCostate
public import SmoothedPolygons.Ch6.MatrixMinimizer
public import SmoothedPolygons.Ch6.PeriodicExtension
public import External.Pontryagin

/-!
# The global minimizer is a Pontryagin extremal: the book's route (§6.2, §6.5, §6.6)

The book applies the Pontryagin maximum principle, cited from `zelikin2004control`
(Agrachev–Sachkov), to the Reinhardt control problem on `SL₂(ℝ) × 𝔰𝔩₂(ℝ)` (§6.2, TeX
4662–4830), derives the costate equations in Lie-algebra form (Proposition 6.5.1, TeX 4999–5085)
and the transversality conditions (6.6.1) (§6.6, TeX 5157–5215, with Remark 6.6.1), and collects
them as Problem 6.7.1; Proposition 8.1.3 then says (TeX 6791) "We have seen that the global
minimizer must be extremal". This file follows that route on the matrix system of
`SmoothedPolygons/Ch6/MatrixSystem.lean` (state space `GL₂⁺(ℝ) × C ⊆ Mat₂(ℝ) × 𝔰𝔩₂(ℝ)`):

1. A global minimizer of Problem 3.6.2 is a strong local minimizer of the matrix system
   (`IsReinhardtMinimizer.isStrongLocalMinimizer_matrix`).
2. The maximum principle (`External.pontryagin_maximum_principle`: free terminal time, integral
   cost, the boundary map `matrixBoundary` a submersion) gives `λ_cost = ν ≤ 0` and a Lipschitz
   covector curve `p` with `(ν, p(t)) ≠ 0`, the adjoint equation, the maximum condition, `H = 0`
   and transversality.
3. Translation (`isPontryaginExtremal_of_matrixCostate`), with `Λ₁ = covectorΛ₁ q p` and
   `Λ_R = covectorΛR q p` (`SmoothedPolygons/Ch6/MatrixCostate.lean`):
   * the Hamiltonian of the maximum principle is `hamiltonian ν Λ₁ Λ_R X u`
     (`controlHamiltonian_matrix_eq_hamiltonian`), so the maximum condition and `H = 0` transfer;
   * the costate equations `Λ₁' = [Λ₁, X]` and `eqn:lamR` hold at almost every time
     (`hasDerivAt_covectorΛ_of_adjoint`: Proposition 6.5.1), hence in integral form
     (`isIntegralCurve_covectorΛ_of_adjoint`: `q`, `p` are Lipschitz and `Λ₁`, `Λ_R` polynomial
     in `(q, p)`, so absolutely continuous);
   * transversality: `Λ_R(t_f) = R⁻¹Λ_R(0)R` (`covectorΛR_transversality`), and
     `Λ₁(t_f) = R⁻¹Λ₁(0)R` from `g(t_f) = R` (Remark 6.6.1 with Corollary 6.5.3,
     `remark6_6_1_lambda1`);
   * nontriviality of the reduced costate: if `ν = 0`, `Λ₁(t₀) = 0` and `Λ_R(t₀) = 0`, then
     `Λ₁ ≡ 0` (Corollary 6.5.3, `IsStateTrajectory.eq_conj_of_isIntegralCurve`), so the `Λ_R`
     equation is linear homogeneous and `Λ_R ≡ 0`
     (`IsStateTrajectory.eq_zero_of_isIntegralCurve_costateRHS`); at `t_f` the covector `p(t_f)`
     then vanishes by the transversality conditions in the directions of the two boundary
     equations left out (`covector_transversality_dropped`, `eq_zero_of_covectorΛ_eq_zero`),
     against `(ν, p(t_f)) ≠ 0`.

Departure from the paper (the only one; E21, see `SmoothedPolygons/Ch6/MatrixSystem.lean`): the
maximum principle is applied with the boundary condition of Problem 3.6.2 less the two equations
of `g(t_f) = R` and `X(t_f) = R⁻¹X(0)R` that the first integrals `det g`, `det X` make redundant.
With the book's boundary condition every admissible trajectory satisfies the conclusions of the
maximum principle with `λ_cost = 0` and `(p g, Λ₂) = (k I₂, 0)` or `(0, c X)`, whose reduced
costate `(Λ₁, Λ_R)` vanishes, so the nontriviality of the reduced costate cannot be derived; with
the two equations left out, transversality excludes these covectors. The rest is the book's
route: Hamilton's equations give Proposition 6.5.1 (`proposition6_5_1`, with the Euler–Arnold
equation `External.euler_arnold`) and the book's derivation of the `Λ_R` equation; §6.8 is not
used. The book's "smooth manifold" `SL₂(ℝ) × 𝔰𝔩₂(ℝ)` is read as the open set `GL₂⁺(ℝ) × C`, with
`g(0) = I₂` and `det X(0) = 1` (§3.5) as boundary conditions, and its "closed control set" as the
compact `U_T` (readings D1, D4 of `External/Pontryagin.lean`).
-/

@[expose] public section

namespace SmoothedPolygons

open Set MeasureTheory Filter Matrix Pontryagin ControlSystem

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
  sorry

/-! ### Nontriviality of the reduced costate -/

/-- **Corollary 6.5.3** (`cor:lam1-gen-sol`) for Carathéodory solutions: if `g' = gX` with
`g(0) = I₂` and `Λ₁' = [Λ₁, X]` (integral form), then `Λ₁(t) = g(t)⁻¹Λ₁(0)g(t)` on `[0, t_f]`.

Proof as for `remark6_6_1_lambda1`: the integrands `gX` and `[Λ₁, X]` are continuous, so `g`
and `Λ₁` are differentiable on `[0, t_f]` (FTC-1), and `corollary6_5_3` applies. -/
theorem IsStateTrajectory.eq_conj_of_isIntegralCurve {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X Λ₁ : ℝ → Mat2} (h : IsStateTrajectory T u g X) (hg0 : g 0 = 1)
    (hΛ : IsIntegralCurve Λ₁ (fun t ↦ Λ₁ t * X t - X t * Λ₁ t) T) :
    ∀ t ∈ Icc 0 T, Λ₁ t = (g t)⁻¹ * Λ₁ 0 * g t := by
  sorry

/-- **Uniqueness for linear Carathéodory equations** (Grönwall): a solution of `Λ' = v` in
integral form on `[0, T]` with `|vᵢⱼ(t)| ≤ K ∑ₖₗ |Λₖₗ(t)|` that vanishes at one time vanishes
identically. -/
theorem IsIntegralCurve.eq_zero_of_abs_le {Λ v : ℝ → Mat2} {T K : ℝ} (h : IsIntegralCurve Λ v T)
    (hv : ∀ t ∈ Icc 0 T, ∀ i j, |v t i j| ≤ K * ∑ k, ∑ l, |Λ t k l|) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Icc 0 T) (h0 : Λ t₀ = 0) : ∀ t ∈ Icc 0 T, Λ t = 0 := by
  sorry

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
  sorry

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

/-- **The global minimizer is a Pontryagin extremal**, by the book's route (§6.2, §6.5, §6.6;
TeX 4662–4830, 4999–5085, 5157–5242; Problem 6.7.1; used in the proof of Proposition 8.1.3,
TeX 6791: "We have seen that the global minimizer must be extremal"). The statement is that of
`exists_isPontryaginExtremal_of_isReinhardtMinimizer`
(`SmoothedPolygons/Ch6/MaximumPrinciple.lean`, proved there through the Iwasawa chart); this proof
is to replace that one.

Proof: `IsReinhardtMinimizer.isStrongLocalMinimizer_matrix`,
`External.pontryagin_maximum_principle` (with `isOpen_matrixDomain`,
`mx_isCompact_controlSimplex`, `isC1On_matrixField`, `isC1On_matrixCost`,
`contDiff_matrixBoundary`, `surjective_fderiv_matrixBoundary`), and
`isPontryaginExtremal_of_matrixCostate`.

Departure from the paper: the maximum principle is applied with the boundary condition less the
two equations made redundant by the first integrals `det g`, `det X` (`matrixBoundary`), since
with them it admits, for every admissible trajectory, covectors whose reduced costate vanishes
(E21; see the module docstring). -/
theorem mx_exists_isPontryaginExtremal_of_isReinhardtMinimizer {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X : ℝ → Mat2} (h : IsReinhardtMinimizer T u g X) :
    ∃ (Λ₁ ΛR : ℝ → Mat2) (lam : ℝ), IsPontryaginExtremal T u g X Λ₁ ΛR lam := by
  have hmin := h.isStrongLocalMinimizer_matrix
  have h0 : toMatrixState (g 0) (X 0) ∈ matrixDomain := hmin.2.1.2 0 ⟨le_rfl, hmin.1.le⟩
  obtain ⟨ν, p, hν, hlip, hN, hA, hM, hZ, hT⟩ :=
    External.pontryagin_maximum_principle isOpen_matrixDomain mx_isCompact_controlSimplex
      isC1On_matrixField isC1On_matrixCost hmin contDiff_matrixBoundary.contDiffAt
      (surjective_fderiv_matrixBoundary
        (w := (toMatrixState (g 0) (X 0), toMatrixState (g T) (X T))) h0)
      hmin.2.2.1 (Eventually.of_forall fun _ hz ↦ hz)
  exact ⟨_, _, ν, isPontryaginExtremal_of_matrixCostate h.1 hν hlip hN hA hM hZ hT⟩

end SmoothedPolygons
