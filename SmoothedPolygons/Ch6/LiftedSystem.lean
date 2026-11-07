module

public import SmoothedPolygons.Ch6.IwasawaChart
public import SmoothedPolygons.Ch3.ControlProblem
public import SmoothedPolygons.Ch4.StarDomain
public import OptimalControl.Pontryagin.Defs

/-!
# The Reinhardt problem in the global chart `ℝ³ × 𝔥*`

The state space to which the maximum principle is applied is `SL₂(ℝ) × 𝔥*`, covered by the
chart `(p, z) ↦ (π(p), Φ(z))`, `π` the Iwasawa chart (`SmoothedPolygons/Ch6/IwasawaChart.lean`)
and `Φ` the map of the upper half-plane onto the adjoint orbit of `J` (Lemma 4.2.1); `X = Φ(z)`
satisfies the star conditions exactly for `z ∈ 𝔥*` (Theorem 4.4.1). So the *lifted problem* lives
on the open set `liftedDomain = ℝ³ × 𝔥* ⊆ ℝ³ × ℝ²`, with

* the dynamics `liftedField`: `p' = iwasawaField p Φ(z)` (the lift of `g' = gX`) and
  `z' = (f₁(z; u), f₂(z; u))` (Problem 4.5.1, Lemma 4.5.2; the denominator does not vanish on
  `𝔥* × U_T` by Lemma 3.3.4);
* the control set `U_T` (`controlSimplex`), compact;
* the cost `liftedCost = -(3/2)⟨J, Φ(z)⟩ = (3/2)(1 + x² + y²)/y` (equation `eqn:cost`);
* the boundary condition `liftedEndpoints p₁`: `p(0) = 0`, `p(T) = p₁` and `z(T) = R⁻¹ · z(0)`
  (Möbius action, `mobius`), the zero set of the `C¹` submersion `liftedBoundary p₁`
  (`k = 8` equations). Here `p₁` is the end point of the lift of the minimizer's `g`, a lift of
  `R`; then `π(p(0)) = I`, `π(p(T)) = R` and `X(T) = R⁻¹X(0)R` (`Φ` is equivariant), which are
  the boundary conditions of Problem 3.6.2.

A Reinhardt trajectory lifts to an admissible pair of the lifted problem
(`IsStateTrajectory.exists_lift`), admissible pairs of the lifted problem project to Reinhardt
trajectories (`isStateTrajectory_of_isAdmissibleIn`), and the costs agree (`cost_liftedCost`).
Hence a global minimizer of the Reinhardt problem (`IsReinhardtMinimizer`) lifts to a (strong
local) minimizer of the lifted problem (`IsReinhardtMinimizer.exists_lift`).

Why this state space (inventory §3.4, `notes/plan_ch5_8_16/inventory.md`): on
`SL₂(ℝ) × 𝔰𝔩₂(ℝ)` (the book's choice) the maximum principle returns the spurious multiplier
`(λ_cost, Λ₁, Λ₂) = (0, 0, cX)` for every trajectory (E21), and on `Mat₂ × 𝔥*` the end condition
`g(T) = R` violates the constraint qualification (`det g` is a first integral). On `ℝ³ × 𝔥*`
the nontriviality of the costate is the nontriviality of the reduced costate `(λ_cost, Λ₁, Λ_R)`,
which is the condition of `IsPontryaginExtremal`.
-/

@[expose] public section

namespace SmoothedPolygons

open Set MeasureTheory Filter Topology Pontryagin ControlSystem
open scoped MatrixGroups

/-- The state space `ℝ³ × ℝ²` of the lifted problem: Iwasawa coordinates `p = (s, r, θ)` of `g`
and the point `z = (x, y)` of the upper half-plane with `X = Φ(x + iy)`. -/
abbrev LiftedState : Type := (ℝ × ℝ × ℝ) × (ℝ × ℝ)

/-- The open set `ℝ³ × 𝔥*` on which the lifted problem is posed. -/
def liftedDomain : Set LiftedState := univ ×ˢ starDomain

/-- The dynamics of the lifted problem: `p' = iwasawaField p Φ(z)`, `z' = (f₁(z; u), f₂(z; u))`. -/
noncomputable def liftedField (q : LiftedState) (u : Fin 3 → ℝ) : LiftedState :=
  (iwasawaField q.1 (Φ q.2.1 q.2.2), (halfPlaneF₁ q.2.1 q.2.2 u, halfPlaneF₂ q.2.1 q.2.2 u))

/-- The cost integrand `-(3/2)⟨J, Φ(z)⟩` of the lifted problem (equation `eqn:cost`). -/
noncomputable def liftedCost (q : LiftedState) (_u : Fin 3 → ℝ) : ℝ :=
  -(3 / 2) * traceForm J (Φ q.2.1 q.2.2)

/-- The Möbius action `z ↦ (az + b)/(cz + d)` of `A = [[a, b], [c, d]]` on the upper half-plane,
in real coordinates `z = x + iy`: with `D = (cx + d)² + c²y²`,
`((ax + b)(cx + d) + acy²)/D + i (ad - bc) y/D`. -/
noncomputable def mobius (A : Mat2) (z : ℝ × ℝ) : ℝ × ℝ :=
  (((A 0 0 * z.1 + A 0 1) * (A 1 0 * z.1 + A 1 1) + A 0 0 * A 1 0 * z.2 ^ 2) /
      ((A 1 0 * z.1 + A 1 1) ^ 2 + A 1 0 ^ 2 * z.2 ^ 2),
    (A 0 0 * A 1 1 - A 0 1 * A 1 0) * z.2 / ((A 1 0 * z.1 + A 1 1) ^ 2 + A 1 0 ^ 2 * z.2 ^ 2))

/-- The boundary map of the lifted problem: `(p(0), p(T) - p₁, z(T) - R⁻¹ · z(0))`. -/
noncomputable def liftedBoundary (p₁ : ℝ × ℝ × ℝ) (w : LiftedState × LiftedState) :
    (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ) × (ℝ × ℝ) :=
  (w.1.1, w.2.1 - p₁, w.2.2 - mobius R⁻¹ w.1.2)

/-- The boundary condition of the lifted problem: `p(0) = 0`, `p(T) = p₁`, `z(T) = R⁻¹ · z(0)`. -/
def liftedEndpoints (p₁ : ℝ × ℝ × ℝ) : Set (LiftedState × LiftedState) :=
  {w | liftedBoundary p₁ w = 0}

/-- The control simplex `U_T` is compact. -/
theorem isCompact_controlSimplex : IsCompact controlSimplex := by
  have hsub : controlSimplex ⊆ Set.pi univ (fun _ : Fin 3 ↦ Icc (0 : ℝ) 1) :=
    fun u hu i _ ↦ hu.1 i
  refine (isCompact_univ_pi fun _ ↦ isCompact_Icc).of_isClosed_subset ?_ hsub
  have e : controlSimplex = (⋂ i, {u : Fin 3 → ℝ | 0 ≤ u i ∧ u i ≤ 1}) ∩
      {u | u 0 + u 1 + u 2 = 1} := by
    ext u; simp [controlSimplex]
  rw [e]
  refine IsClosed.inter (isClosed_iInter fun i ↦ ?_) (isClosed_eq (by fun_prop) continuous_const)
  exact (isClosed_le continuous_const (continuous_apply i)).inter
    (isClosed_le (continuous_apply i) continuous_const)

/-- `ℝ³ × 𝔥*` is open. -/
theorem isOpen_liftedDomain : IsOpen liftedDomain := by
  refine isOpen_univ.prod ?_
  have e : starDomain = {p : ℝ × ℝ | 0 < p.2} ∩ {p | -(1 / √3) < p.1} ∩ {p | p.1 < 1 / √3} ∩
      {p | 1 / 3 < p.1 ^ 2 + p.2 ^ 2} := by
    ext p; simp [starDomain, and_assoc]
  rw [e]
  exact (((isOpen_lt continuous_const continuous_snd).inter
    (isOpen_lt continuous_const continuous_fst)).inter
    (isOpen_lt continuous_fst continuous_const)).inter (isOpen_lt continuous_const (by fun_prop))

/-- A system whose right-hand side is jointly `C¹` on an open set containing `Ω × U` satisfies
the regularity conditions `IsC1On` (`∂ₓf(x, u)` is the restriction of the joint derivative). -/
private lemma iw_isC1On_of_contDiffOn {E V F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : E → V → F} {Ω : Set E} {U : Set V} {O : Set (E × V)} (hO : IsOpen O)
    (hΩU : Ω ×ˢ U ⊆ O) (hf : ContDiffOn ℝ 1 (fun q : E × V ↦ f q.1 q.2) O) : IsC1On f Ω U where
  continuousOn := hf.continuousOn.mono hΩU
  differentiableAt x hx u hu := by
    have hd : DifferentiableAt ℝ (fun q : E × V ↦ f q.1 q.2) (x, u) :=
      (hf.contDiffAt (hO.mem_nhds (hΩU ⟨hx, hu⟩))).differentiableAt one_ne_zero
    exact DifferentiableAt.comp (𝕜 := ℝ) x hd
      (by fun_prop : DifferentiableAt ℝ (fun x : E ↦ (x, u)) x)
  continuousOn_fderiv := by
    have key : ∀ q ∈ O, fderiv ℝ (f · q.2) q.1 =
        (fderiv ℝ (fun q : E × V ↦ f q.1 q.2) q).comp (ContinuousLinearMap.inl ℝ E V) := by
      rintro ⟨x, u⟩ hq
      have hd := (hf.contDiffAt (hO.mem_nhds hq)).differentiableAt one_ne_zero
      exact (HasFDerivAt.comp (𝕜 := ℝ) x hd.hasFDerivAt (hasFDerivAt_prodMk_left x u)).fderiv
    refine ContinuousOn.congr ?_ (fun q hq ↦ key q (hΩU hq))
    exact ((hf.continuousOn_fderiv_of_isOpen hO le_rfl).clm_comp continuousOn_const).mono hΩU

/-- The denominator `D = 2ax + b - cx² - cy²` of `f₁, f₂` (Problem 4.5.1), with
`Z_u = [[a, b], [c, -a]]`; `D = y⟨Z_u, Φ(x + iy)⟩`. -/
private noncomputable def iw_denom (z : ℝ × ℝ) (u : Fin 3 → ℝ) : ℝ :=
  2 * controlMatrix u 0 0 * z.1 + controlMatrix u 0 1 - controlMatrix u 1 0 * z.1 ^ 2 -
    controlMatrix u 1 0 * z.2 ^ 2

/-- `⟨Z_u, Φ(x + iy)⟩ = D/y`. -/
private lemma iw_traceForm_controlMatrix_Φ (z : ℝ × ℝ) (hy : z.2 ≠ 0) (u : Fin 3 → ℝ) :
    traceForm (controlMatrix u) (Φ z.1 z.2) = iw_denom z u / z.2 := by
  have hZ11 : controlMatrix u 1 1 = -controlMatrix u 0 0 := by simp [controlMatrix]; ring
  rw [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two, hZ11, iw_denom]
  simp only [Φ, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  field_simp
  ring

/-- The denominator `D` is negative on `𝔥* × U_T`: `⟨Z_u, Φ(z)⟩ < 0` there (Theorem 4.4.1 and
Lemma 3.3.4, as in the proof of Lemma 4.5.2). -/
private lemma iw_denom_neg {z : ℝ × ℝ} (hz : z ∈ starDomain) {u : Fin 3 → ℝ}
    (hu : u ∈ controlSimplex) : iw_denom z u < 0 := by
  have hy : 0 < z.2 := hz.1
  have hXstar := (theorem4_4_1 z.1 z.2 hy).2 hz
  have hneg := (lemma3_3_4 (Φ z.1 z.2) hXstar.1).1 hXstar.2.2 u hu
  rw [iw_traceForm_controlMatrix_Φ z hy.ne'] at hneg
  by_contra h
  exact absurd hneg (not_lt.2 (div_nonneg (not_lt.1 h) hy.le))

/-- The lifted dynamics satisfies the regularity hypotheses of the maximum principle on
`ℝ³ × 𝔥*` (smooth in the state, the denominator `⟨Z_u, X⟩` being negative on `𝔥* × U_T` by
Lemma 3.3.4). -/
theorem isC1On_liftedField : IsC1On liftedField liftedDomain controlSimplex := by
  refine iw_isC1On_of_contDiffOn (O := {w | 0 < w.1.2.2 ∧ iw_denom w.1.2 w.2 ≠ 0}) ?_ ?_ ?_
  · have hc : Continuous fun w : LiftedState × (Fin 3 → ℝ) ↦ iw_denom w.1.2 w.2 := by
      simp only [iw_denom, controlMatrix, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
      fun_prop
    have hy : Continuous fun w : LiftedState × (Fin 3 → ℝ) ↦ w.1.2.2 := by fun_prop
    exact (isOpen_lt continuous_const hy).inter (isOpen_ne_fun hc continuous_const)
  · rintro ⟨q, u⟩ ⟨hq, hu⟩
    exact ⟨hq.2.1, (iw_denom_neg hq.2 hu).ne⟩
  · intro w hw
    have hy : w.1.2.2 ≠ 0 := hw.1.ne'
    have hD : iw_denom w.1.2 w.2 ≠ 0 := hw.2
    simp only [iw_denom, controlMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at hD
    refine ContDiffAt.contDiffWithinAt ?_
    simp only [liftedField, iwasawaField, iwasawaK, Φ, halfPlaneF₁, halfPlaneF₂, controlMatrix,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    fun_prop (disch := assumption)

/-- The cost integrand is smooth on `ℝ³ × 𝔥*`. -/
theorem isC1On_liftedCost : IsC1On liftedCost liftedDomain controlSimplex := by
  refine iw_isC1On_of_contDiffOn (O := {w | 0 < w.1.2.2}) ?_ ?_ ?_
  · exact isOpen_lt continuous_const (by fun_prop)
  · rintro ⟨q, u⟩ ⟨hq, -⟩
    exact hq.2.1
  · intro w hw
    have hy : w.1.2.2 ≠ 0 := (show 0 < w.1.2.2 from hw).ne'
    refine ContDiffAt.contDiffWithinAt ?_
    simp only [liftedCost, traceForm, J, Φ, Matrix.trace_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    fun_prop (disch := assumption)

/-- The denominator `(cx + d)² + c²y²` of the Möbius map of `A = [[a, b], [c, d]] ∈ SL₂(ℝ)` is
positive on the upper half-plane. -/
private lemma iw_mobius_den_pos {A : Mat2} (hA : A.det = 1) {z : ℝ × ℝ} (hz : 0 < z.2) :
    0 < (A 1 0 * z.1 + A 1 1) ^ 2 + A 1 0 ^ 2 * z.2 ^ 2 := by
  rcases eq_or_ne (A 1 0) 0 with hc | hc
  · have hd : A 1 1 ≠ 0 := by
      intro hd
      rw [Matrix.det_fin_two, hc, hd] at hA
      simp at hA
    simp only [hc, zero_mul, zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      add_zero]
    positivity
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (by positivity)

/-- Equivariance of `Φ` (Remark 4.2.2, `ΦH_smul`) in real coordinates: for `det A = 1` and
`y > 0`, the Möbius map of `A` keeps the upper half-plane and `Φ(A · z) = A Φ(z) A⁻¹`. -/
theorem Φ_mobius {A : Mat2} (hA : A.det = 1) {z : ℝ × ℝ} (hz : 0 < z.2) :
    0 < (mobius A z).2 ∧ Φ (mobius A z).1 (mobius A z).2 = A * Φ z.1 z.2 * A⁻¹ := by
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by rwa [Matrix.det_fin_two] at hA
  have hN := iw_mobius_den_pos hA hz
  refine ⟨by simp only [mobius]; rw [hdet, one_mul]; exact div_pos hz hN, ?_⟩
  -- `g · w` for `g = A ∈ SL₂(ℝ)` and `w = z₁ + iz₂ ∈ ℍ` is `mobius A z`
  let g : SL(2, ℝ) := ⟨A, hA⟩
  let w : UpperHalfPlane := ⟨⟨z.1, z.2⟩, hz⟩
  have hcoe := UpperHalfPlane.coe_specialLinearGroup_apply g w
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at hcoe
  have hnum : ((g 0 0 : ℝ) : ℂ) * (w : ℂ) + ((g 0 1 : ℝ) : ℂ) =
      ⟨A 0 0 * z.1 + A 0 1, A 0 0 * z.2⟩ := by
    apply Complex.ext <;> simp [g, w]
  have hden : ((g 1 0 : ℝ) : ℂ) * (w : ℂ) + ((g 1 1 : ℝ) : ℂ) =
      ⟨A 1 0 * z.1 + A 1 1, A 1 0 * z.2⟩ := by
    apply Complex.ext <;> simp [g, w]
  rw [hnum, hden] at hcoe
  have hnsq : Complex.normSq ⟨A 1 0 * z.1 + A 1 1, A 1 0 * z.2⟩ =
      (A 1 0 * z.1 + A 1 1) ^ 2 + A 1 0 ^ 2 * z.2 ^ 2 := by
    rw [Complex.normSq_mk]; ring
  have hre : (g • w).re = (mobius A z).1 := by
    rw [← UpperHalfPlane.coe_re, hcoe, Complex.div_re, hnsq, mobius]
    field_simp
  have him : (g • w).im = (mobius A z).2 := by
    rw [← UpperHalfPlane.coe_im, hcoe, Complex.div_im, hnsq, mobius]
    field_simp
    ring
  have hinv : ((g⁻¹ : SL(2, ℝ)) : Mat2) = A⁻¹ := by
    refine (Matrix.inv_eq_left_inv ?_).symm
    rw [show A = ((g : SL(2, ℝ)) : Mat2) from rfl, ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have key := ΦH_smul g w
  simp only [ΦH, hre, him, hinv] at key
  exact key

/-- `R⁻¹ = [[1/2, √3/2], [-√3/2, 1/2]]`. -/
private lemma iw_R_inv : R⁻¹ = !![1 / 2, √3 / 2; -(√3 / 2), 1 / 2] := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  refine Matrix.inv_eq_left_inv ?_
  ext i j; fin_cases i <;> fin_cases j <;> simp [R] <;> linarith [h3]

/-- `det R⁻¹ = 1`. -/
private lemma iw_det_R_inv : R⁻¹.det = 1 := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  rw [iw_R_inv, Matrix.det_fin_two_of]
  linear_combination h3 / 4

/-- The Möbius map of `A ∈ SL₂(ℝ)` is smooth on the upper half-plane. -/
private lemma iw_contDiffAt_mobius {A : Mat2} (hA : A.det = 1) {z : ℝ × ℝ} (hz : 0 < z.2) :
    ContDiffAt ℝ 1 (mobius A) z := by
  have hN := (iw_mobius_den_pos hA hz).ne'
  unfold mobius
  fun_prop (disch := assumption)

/-- The boundary map is `C¹` near every pair of states in the upper half-plane. -/
theorem contDiffAt_liftedBoundary (p₁ : ℝ × ℝ × ℝ) {w : LiftedState × LiftedState}
    (hw : 0 < w.1.2.2) : ContDiffAt ℝ 1 (liftedBoundary p₁) w := by
  have hm : ContDiffAt ℝ 1 (fun w : LiftedState × LiftedState ↦ mobius R⁻¹ w.1.2) w :=
    ContDiffAt.comp (g := mobius R⁻¹) w (iw_contDiffAt_mobius iw_det_R_inv hw)
      (by fun_prop : ContDiffAt ℝ 1 (fun w : LiftedState × LiftedState ↦ w.1.2) w)
  unfold liftedBoundary
  exact (by fun_prop : ContDiffAt ℝ 1 (fun w : LiftedState × LiftedState ↦ w.1.1) w).prodMk
    ((by fun_prop : ContDiffAt ℝ 1 (fun w : LiftedState × LiftedState ↦ w.2.1 - p₁) w).prodMk
      ((by fun_prop : ContDiffAt ℝ 1 (fun w : LiftedState × LiftedState ↦ w.2.2) w).sub hm))

/-- The boundary map is a submersion (the constraint qualification of the maximum principle). -/
theorem surjective_fderiv_liftedBoundary (p₁ : ℝ × ℝ × ℝ) {w : LiftedState × LiftedState}
    (hw : 0 < w.1.2.2) : Function.Surjective (fderiv ℝ (liftedBoundary p₁) w) := by
  have hm : DifferentiableAt ℝ (mobius R⁻¹) w.1.2 :=
    (iw_contDiffAt_mobius iw_det_R_inv hw).differentiableAt one_ne_zero
  have h1 : HasFDerivAt (fun w : LiftedState × LiftedState ↦ w.1.1)
      ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.fst ℝ _ _)) w :=
    hasFDerivAt_fst.fst
  have h2 : HasFDerivAt (fun w : LiftedState × LiftedState ↦ w.2.1 - p₁)
      ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)) w :=
    hasFDerivAt_snd.fst.sub_const p₁
  have h4 : HasFDerivAt (fun w : LiftedState × LiftedState ↦ w.1.2)
      ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.fst ℝ _ _)) w :=
    hasFDerivAt_fst.snd
  have h3 : HasFDerivAt (fun w : LiftedState × LiftedState ↦ w.2.2 - mobius R⁻¹ w.1.2)
      ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _) -
        (fderiv ℝ (mobius R⁻¹) w.1.2).comp
          ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.fst ℝ _ _))) w :=
    hasFDerivAt_snd.snd.sub (HasFDerivAt.comp (g := mobius R⁻¹) w hm.hasFDerivAt h4)
  have hD := h1.prodMk (h2.prodMk h3)
  unfold liftedBoundary
  rw [hD.fderiv]
  -- `(a, b, c)` is the image of `((a, 0), (b, c))`
  rintro ⟨a, b, c⟩
  exact ⟨((a, 0), (b, c)), by simp⟩

/-- The cost of a pair of the lifted problem is the Reinhardt cost of its projection. -/
theorem cost_liftedCost (T : ℝ) (u : ℝ → Fin 3 → ℝ) (q : ℝ → LiftedState) :
    cost liftedCost T u q = reinhardtCost T (fun t ↦ Φ (q t).2.1 (q t).2.2) := by
  simp [cost, liftedCost, reinhardtCost, intervalIntegral.integral_const_mul]

/-! ### Lifting and projecting trajectories -/

/-- A star state is `Φ(x + iy)` with `x + iy = (X₀₀ + i)/X₁₀ ∈ 𝔥*`: it is traceless with
determinant one and `⟨J, X⟩ = X₀₁ - X₁₀ < 0` (as `X₁₀ > 0` from `ρ₀ + ρ₁ > 0`), so it lies in the
adjoint orbit of `J` (Lemma 4.1.1), hence is `Φ(z)` for some `z ∈ ℍ` (Lemma 4.2.1), and
`z ∈ 𝔥*` (Theorem 4.4.1). -/
private lemma iw_star_eq_Φ {X : Mat2} (hX : IsStarState X) :
    0 < X 1 0 ∧ X = Φ (X 0 0 / X 1 0) (1 / X 1 0) ∧ (X 0 0 / X 1 0, 1 / X 1 0) ∈ starDomain := by
  obtain ⟨htr, hdet, h0, h1, h2⟩ := hX
  have h3 : 0 < √3 := by positivity
  have hc : 0 < X 1 0 := by
    have a0 := (div_pos_iff_of_pos_right h3).1 h0
    have a1 := (div_pos_iff_of_pos_right h3).1 h1
    linarith
  have h11 : X 1 1 = -X 0 0 := by rw [Matrix.trace_fin_two] at htr; linarith
  have hb : X 0 1 < 0 := by
    rw [Matrix.det_fin_two, h11] at hdet
    nlinarith [sq_nonneg (X 0 0)]
  have hJ : traceForm J X < 0 := by
    simp only [traceForm, J, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    linarith
  have hmem : X ∈ adjointOrbit J := by rw [← lemma4_1_1]; exact ⟨htr, hdet, hJ⟩
  obtain ⟨w, -, hw⟩ := lemma4_2_1.2.2 hmem
  have hy := w.im_pos
  have e10 : X 1 0 = 1 / w.im := by rw [← hw]; simp [ΦH, Φ]
  have e00 : X 0 0 = w.re / w.im := by rw [← hw]; simp [ΦH, Φ]
  have hy' : 1 / X 1 0 = w.im := by rw [e10, one_div_one_div]
  have hx' : X 0 0 / X 1 0 = w.re := by rw [e00, e10]; field_simp
  rw [hx', hy']
  refine ⟨hc, hw.symm, (theorem4_4_1 _ _ hy).1 ?_⟩
  change IsStarState (ΦH w)
  rw [hw]
  exact ⟨htr, hdet, h0, h1, h2⟩

/-- The integral form of a curve in a product, from the integral forms of its components. -/
private lemma iw_prod_eq_add_integral {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [CompleteSpace A] [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B] {T : ℝ}
    (hT : 0 ≤ T) {x v : ℝ → A × B} (h1 : IntervalIntegrable (fun t ↦ (v t).1) volume 0 T)
    (h2 : IntervalIntegrable (fun t ↦ (v t).2) volume 0 T)
    (hx1 : ∀ t ∈ Icc 0 T, (x t).1 = (x 0).1 + ∫ s in (0 : ℝ)..t, (v s).1)
    (hx2 : ∀ t ∈ Icc 0 T, (x t).2 = (x 0).2 + ∫ s in (0 : ℝ)..t, (v s).2) :
    IntervalIntegrable v volume 0 T ∧ ∀ t ∈ Icc 0 T, x t = x 0 + ∫ s in (0 : ℝ)..t, v s := by
  have hv : IntervalIntegrable v volume 0 T := ⟨h1.1.prodMk h2.1, h1.2.prodMk h2.2⟩
  refine ⟨hv, fun t ht ↦ ?_⟩
  have hvt : IntervalIntegrable v volume 0 t := hv.mono_set (by
    rw [uIcc_of_le hT, uIcc_of_le ht.1]; exact Icc_subset_Icc_right ht.2)
  have e1 := (ContinuousLinearMap.fst ℝ A B).intervalIntegral_comp_comm hvt
  have e2 := (ContinuousLinearMap.snd ℝ A B).intervalIntegral_comp_comm hvt
  simp only [ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'] at e1 e2
  exact Prod.ext (by rw [hx1 t ht, Prod.fst_add, e1]) (by rw [hx2 t ht, Prod.snd_add, e2])

/-- The components of a curve in integral form in a product are in integral form. -/
private lemma iw_prod_components {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [CompleteSpace A] [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B] {T : ℝ}
    (hT : 0 ≤ T) {x v : ℝ → A × B} (hv : IntervalIntegrable v volume 0 T)
    (hx : ∀ t ∈ Icc 0 T, x t = x 0 + ∫ s in (0 : ℝ)..t, v s) :
    (IntervalIntegrable (fun t ↦ (v t).1) volume 0 T ∧
      ∀ t ∈ Icc 0 T, (x t).1 = (x 0).1 + ∫ s in (0 : ℝ)..t, (v s).1) ∧
    (IntervalIntegrable (fun t ↦ (v t).2) volume 0 T ∧
      ∀ t ∈ Icc 0 T, (x t).2 = (x 0).2 + ∫ s in (0 : ℝ)..t, (v s).2) := by
  have hvt : ∀ t ∈ Icc 0 T, IntervalIntegrable v volume 0 t := fun t ht ↦ hv.mono_set (by
    rw [uIcc_of_le hT, uIcc_of_le ht.1]; exact Icc_subset_Icc_right ht.2)
  refine ⟨⟨⟨(ContinuousLinearMap.fst ℝ A B).integrable_comp hv.1,
      (ContinuousLinearMap.fst ℝ A B).integrable_comp hv.2⟩, fun t ht ↦ ?_⟩,
    ⟨⟨(ContinuousLinearMap.snd ℝ A B).integrable_comp hv.1,
      (ContinuousLinearMap.snd ℝ A B).integrable_comp hv.2⟩, fun t ht ↦ ?_⟩⟩
  · have e := (ContinuousLinearMap.fst ℝ A B).intervalIntegral_comp_comm (hvt t ht)
    simp only [ContinuousLinearMap.coe_fst'] at e
    rw [hx t ht, Prod.fst_add, e]
  · have e := (ContinuousLinearMap.snd ℝ A B).intervalIntegral_comp_comm (hvt t ht)
    simp only [ContinuousLinearMap.coe_snd'] at e
    rw [hx t ht, Prod.snd_add, e]

/-- The upper half-plane `{y > 0}` is open. -/
private lemma iw_isOpen_upper : IsOpen {w : ℝ × ℝ | 0 < w.2} :=
  isOpen_lt continuous_const continuous_snd

/-- The entries of `Φ` are smooth on the upper half-plane. -/
private lemma iw_contDiffOn_Φ (i j : Fin 2) :
    ContDiffOn ℝ 1 (fun w : ℝ × ℝ ↦ Φ w.1 w.2 i j) {w | 0 < w.2} := by
  intro w hw
  have hy : w.2 ≠ 0 := (show 0 < w.2 from hw).ne'
  refine ContDiffAt.contDiffWithinAt ?_
  fin_cases i <;> fin_cases j <;>
    simp only [Φ, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] <;>
    fun_prop (disch := assumption)

/-- The tangent map of `Φ` (Lemma 4.2.4): `DΦ(z)(r₁, r₂) = [Y_z(r₁, r₂), Φ(z)]`, entry by
entry. -/
private lemma iw_fderiv_Φ {z : ℝ × ℝ} (hy : 0 < z.2) (r : ℝ × ℝ) (i j : Fin 2) :
    fderiv ℝ (fun w : ℝ × ℝ ↦ Φ w.1 w.2 i j) z r =
      (tangentLift z.1 z.2 r.1 r.2 * Φ z.1 z.2 - Φ z.1 z.2 * tangentLift z.1 z.2 r.1 r.2) i j := by
  have hd : DifferentiableAt ℝ (fun w : ℝ × ℝ ↦ Φ w.1 w.2 i j) z :=
    ((iw_contDiffOn_Φ i j).contDiffAt (iw_isOpen_upper.mem_nhds hy)).differentiableAt one_ne_zero
  have hline : HasDerivAt (fun s : ℝ ↦ z + s • r) r 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const r).const_add z
  exact (hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)).unique
    (lemma4_2_4 z.1 z.2 r.1 r.2 hy i j)

/-- `eqn:tangent-map-f1f2` (proof of Lemma 4.5.2): `T Φ(f₁, f₂)` is the class of
`Z_u/⟨Z_u, X⟩`, that is `[Y_z(f₁, f₂), Φ(z)] = [Z_u, Φ(z)]/⟨Z_u, Φ(z)⟩`.

Departure from the paper: the book reads this off by comparing entries along a solution of the
`X`-equation ("This also shows that …"); the projection of lifted pairs needs it at every
`(z, u)`, where it is checked as an identity of rational functions in `x, y` and the entries of
`Z_u`. Both sides are linear in `1/D`, so (with `1/0 = 0`) no hypothesis on `D` is needed. -/
private lemma iw_tangent_map_f1f2 {z : ℝ × ℝ} (hy : z.2 ≠ 0) (u : Fin 3 → ℝ) :
    tangentLift z.1 z.2 (halfPlaneF₁ z.1 z.2 u) (halfPlaneF₂ z.1 z.2 u) * Φ z.1 z.2 -
        Φ z.1 z.2 * tangentLift z.1 z.2 (halfPlaneF₁ z.1 z.2 u) (halfPlaneF₂ z.1 z.2 u) =
      controlP u (Φ z.1 z.2) * Φ z.1 z.2 - Φ z.1 z.2 * controlP u (Φ z.1 z.2) := by
  have hZ11 : controlMatrix u 1 1 = -controlMatrix u 0 0 := by simp [controlMatrix]; ring
  rw [controlP, iw_traceForm_controlMatrix_Φ z hy u]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [tangentLift, Φ, halfPlaneF₁, halfPlaneF₂, iw_denom, Matrix.sub_apply,
      Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Fin.zero_eta, Fin.isValue, Fin.mk_one, smul_eq_mul, hZ11] <;>
    field_simp <;> ring

/-- A Reinhardt state trajectory with `g(0) = I` lifts to an admissible pair of the lifted
problem, with `p(0) = 0` (Lemma 4.2.1, Theorem 4.4.1, Lemma 4.5.2, path lifting through `π`).

Proof: `p` is the lift of `g` through `π` from `0` (`exists_continuousOn_lift`), which solves
`p' = iwasawaField p X` (`isIntegralCurve_lift`); `z = Φ⁻¹(X) = (X₀₀/X₁₀, 1/X₁₀) ∈ 𝔥*`
(Lemmas 4.1.1, 4.2.1, Theorem 4.4.1). Reading of Lemma 4.5.2 for Carathéodory solutions: `X` has
derivative `[P, X]` at almost every time (Lebesgue's differentiation theorem), where Lemma 4.5.2
gives `z' = (f₁, f₂)`; `z` is absolutely continuous, hence the integral of its derivative. -/
theorem IsStateTrajectory.exists_lift {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsStateTrajectory T u g X) (hg0 : g 0 = 1) :
    ∃ q : ℝ → LiftedState, (q 0).1 = 0 ∧
      (∀ t ∈ Icc 0 T, iwasawa (q t).1 = g t ∧ Φ (q t).2.1 (q t).2.2 = X t) ∧
      IsAdmissibleIn liftedField liftedDomain controlSimplex (q 0) T u q := by
  obtain ⟨hT, hmeas, hU, hstate, hgI, hXI⟩ := h
  have hgc : ContinuousOn g (Icc 0 T) := Matrix.continuousOn_of_eq_add_integral hgI
  have hXc : ContinuousOn X (Icc 0 T) := Matrix.continuousOn_of_eq_add_integral hXI
  have hXij := Matrix.continuousOn_iff_entrywise.1 hXc
  -- the Iwasawa coordinates `p` of `g`, from `p(0) = 0` (path lifting through `π`)
  obtain ⟨p, hpc, hp0, hpg⟩ := exists_continuousOn_lift hT.le hgc (fun t ht ↦ (hstate t ht).1)
    (p₀ := 0) (by rw [iwasawa_zero, hg0])
  -- the point `z = (X₀₀/X₁₀, 1/X₁₀)` of `𝔥*` with `X = Φ(z)` (Lemmas 4.1.1, 4.2.1, Thm 4.4.1)
  have hXz := fun t ht ↦ iw_star_eq_Φ (hstate t ht).2
  have hc0 : ∀ t ∈ Icc 0 T, X t 1 0 ≠ 0 := fun t ht ↦ (hXz t ht).1.ne'
  -- the equation for `p` (`isIntegralCurve_lift`)
  obtain ⟨hpi, hpe⟩ := isIntegralCurve_lift hT.le hgI hXc (fun t ht ↦ (hstate t ht).2.1) hpc hpg
  -- the equations for `z`: Lemma 4.5.2 at almost every time
  have hXae : ∀ᵐ t, t ∈ Ioo 0 T → ∀ i j, HasDerivAt (fun s ↦ X s i j)
      ((controlP (u t) (X t) * X t - X t * controlP (u t) (X t)) i j) t := by
    have h := fun i j ↦ iw_ae_hasDerivAt_of_eq_add_integral (hXI i j).1 (hXI i j).2
    filter_upwards [ae_all_iff.2 fun i ↦ ae_all_iff.2 fun j ↦ h i j] with t ht ht' i j
    exact ht i j ht'
  have hzae : ∀ᵐ t, t ∈ Ioo 0 T →
      HasDerivAt (fun s ↦ X s 0 0 / X s 1 0)
        (halfPlaneF₁ (X t 0 0 / X t 1 0) (1 / X t 1 0) (u t)) t ∧
      HasDerivAt (fun s ↦ 1 / X s 1 0) (halfPlaneF₂ (X t 0 0 / X t 1 0) (1 / X t 1 0) (u t)) t := by
    filter_upwards [hXae] with t ht ht'
    have hτ := Ioo_subset_Icc_self ht'
    have hS : Icc 0 T ∈ 𝓝 t := Icc_mem_nhds ht'.1 ht'.2
    obtain ⟨hc, hXΦ, hstar⟩ := hXz t hτ
    have hX := ht ht'
    have hxd := (hX 0 0).div (hX 1 0) hc.ne'
    have hyd := (hasDerivAt_const t (1 : ℝ)).div (hX 1 0) hc.ne'
    have hΦd : Matrix.HasDerivAtEntrywise (fun s ↦ Φ (X s 0 0 / X s 1 0) (1 / X s 1 0))
        (controlP (u t) (Φ (X t 0 0 / X t 1 0) (1 / X t 1 0)) *
            Φ (X t 0 0 / X t 1 0) (1 / X t 1 0) -
          Φ (X t 0 0 / X t 1 0) (1 / X t 1 0) *
            controlP (u t) (Φ (X t 0 0 / X t 1 0) (1 / X t 1 0))) t := by
      intro i j
      rw [← hXΦ]
      exact (hX i j).congr_of_eventuallyEq
        (Filter.eventually_of_mem hS fun s hs ↦ by simp only [← (hXz s hs).2.1])
    obtain ⟨h1, h2, -⟩ := lemma4_5_2 (fun s ↦ X s 0 0 / X s 1 0) (fun s ↦ 1 / X s 1 0) (u t) t
      _ _ hstar (hU t hτ) hxd hyd hΦd
    exact ⟨hxd.congr_deriv h1, hyd.congr_deriv h2⟩
  -- `x = X₀₀/X₁₀` and `y = 1/X₁₀` are absolutely continuous
  have hyac : AbsolutelyContinuousOnInterval (fun t ↦ 1 / X t 1 0) 0 T :=
    iw_absolutelyContinuousOnInterval_comp (O := Ioi 0) (F := fun r : ℝ ↦ 1 / r) isOpen_Ioi
      (contDiffOn_const.div contDiffOn_id fun r hr ↦ (ne_of_gt hr)) hT.le (hXI 1 0).1
      (hXI 1 0).2 fun t ht ↦ (hXz t ht).1
  have hX00ac : AbsolutelyContinuousOnInterval (fun t ↦ X t 0 0) 0 T :=
    iw_absolutelyContinuousOnInterval_comp (O := univ) (F := fun r : ℝ ↦ r) isOpen_univ
      contDiffOn_id hT.le (hXI 0 0).1 (hXI 0 0).2 fun _ _ ↦ mem_univ _
  have hxac : AbsolutelyContinuousOnInterval (fun t ↦ X t 0 0 / X t 1 0) 0 T :=
    (hX00ac.fun_mul hyac).congr fun t _ ↦ by simp only [mul_one_div]
  obtain ⟨hf₁i, hf₁e⟩ := iw_eq_add_integral_of_ae_hasDerivAt hT.le hxac
    (by filter_upwards [hzae] with t h ht; exact (h ht).1)
  obtain ⟨hf₂i, hf₂e⟩ := iw_eq_add_integral_of_ae_hasDerivAt hT.le hyac
    (by filter_upwards [hzae] with t h ht; exact (h ht).2)
  -- assemble the lifted pair `q = (p, z)`
  have hXΦ : ∀ s ∈ Icc 0 T, Φ (X s 0 0 / X s 1 0) (1 / X s 1 0) = X s := fun s hs ↦
    (hXz s hs).2.1.symm
  refine ⟨fun t ↦ (p t, (X t 0 0 / X t 1 0, 1 / X t 1 0)), hp0,
    fun t ht ↦ ⟨hpg t ht, hXΦ t ht⟩, ⟨⟨hmeas, hU, ?_, ?_⟩, fun t ht ↦ ⟨mem_univ _, (hXz t ht).2.2⟩⟩⟩
  · exact hpc.prodMk (((hXij 0 0).div (hXij 1 0) hc0).prodMk
      (continuousOn_const.div (hXij 1 0) hc0))
  · have hz := iw_prod_eq_add_integral (x := fun t ↦ (X t 0 0 / X t 1 0, 1 / X t 1 0))
      (v := fun s ↦ (halfPlaneF₁ (X s 0 0 / X s 1 0) (1 / X s 1 0) (u s),
        halfPlaneF₂ (X s 0 0 / X s 1 0) (1 / X s 1 0) (u s))) hT.le hf₁i hf₂i hf₁e hf₂e
    refine iw_prod_eq_add_integral hT.le ?_ ?_ ?_ ?_
    · refine (intervalIntegrable_congr fun s hs ↦ ?_).1 hpi
      rw [uIoc_of_le hT.le] at hs
      simp only [liftedField, hXΦ s (Ioc_subset_Icc_self hs)]
    · exact hz.1
    · intro t ht
      simp only [liftedField]
      rw [hpe t ht]
      congr 1
      refine intervalIntegral.integral_congr fun s hs ↦ ?_
      rw [uIcc_of_le ht.1] at hs
      simp only [hXΦ s ⟨hs.1, hs.2.trans ht.2⟩]
    · exact hz.2

/-- An admissible pair of the lifted problem projects to a Reinhardt state trajectory
(Theorem 4.4.1, `eqn:tangent-map-f1f2` from the proof of Lemma 4.5.2, `isIntegralCurve_iwasawa`).

Proof: `g = π(p)` solves `g' = gX` by `isIntegralCurve_iwasawa`; `X = Φ(z)` solves `X' = [P, X]`
by the chain rule for absolutely continuous curves, the tangent map of `Φ` (Lemma 4.2.4) and
`eqn:tangent-map-f1f2` (see `iw_tangent_map_f1f2` for the departure there). -/
theorem isStateTrajectory_of_isAdmissibleIn {T : ℝ} (hT : 0 < T) {u : ℝ → Fin 3 → ℝ}
    {q : ℝ → LiftedState} (h : IsAdmissibleIn liftedField liftedDomain controlSimplex (q 0) T u q) :
    IsStateTrajectory T u (fun t ↦ iwasawa (q t).1) (fun t ↦ Φ (q t).2.1 (q t).2.2) := by
  obtain ⟨⟨hmeas, hU, hqc, hint, heq⟩, hdom⟩ := h
  obtain ⟨⟨hpi, hpe⟩, ⟨hzi, hze⟩⟩ := iw_prod_components hT.le hint heq
  have htr : ∀ x y : ℝ, (Φ x y).trace = 0 := fun x y ↦ by
    simp [Φ, Matrix.trace_fin_two]; ring
  refine ⟨hT, hmeas, hU, fun t ht ↦ ⟨det_iwasawa _,
    (theorem4_4_1 _ _ (hdom t ht).2.1).2 (hdom t ht).2⟩, ?_, ?_⟩
  -- `g = π(p)` solves `g' = gX` (`isIntegralCurve_iwasawa`)
  · exact isIntegralCurve_iwasawa hT.le (fun t _ ↦ htr _ _)
      (continuous_fst.comp_continuousOn hqc) hpi hpe
  -- `X = Φ(z)` solves `X' = [P, X]`: the chain rule, the tangent map of `Φ` (Lemma 4.2.4) and
  -- `eqn:tangent-map-f1f2`
  · intro i j
    obtain ⟨hI, hE⟩ := iw_comp_eq_add_integral iw_isOpen_upper (iw_contDiffOn_Φ i j) hT.le hzi hze
      fun t ht ↦ (hdom t ht).2.1
    have hpt : ∀ s ∈ Icc 0 T, fderiv ℝ (fun w : ℝ × ℝ ↦ Φ w.1 w.2 i j) (q s).2
        (liftedField (q s) (u s)).2 = (controlP (u s) (Φ (q s).2.1 (q s).2.2) *
          Φ (q s).2.1 (q s).2.2 - Φ (q s).2.1 (q s).2.2 *
            controlP (u s) (Φ (q s).2.1 (q s).2.2)) i j := fun s hs ↦ by
      rw [iw_fderiv_Φ (hdom s hs).2.1]
      exact congrFun (congrFun (iw_tangent_map_f1f2 (hdom s hs).2.1.ne' (u s)) i) j
    refine ⟨(intervalIntegrable_congr fun s hs ↦ ?_).1 hI, fun t ht ↦ ?_⟩
    · rw [uIoc_of_le hT.le] at hs
      exact hpt s (Ioc_subset_Icc_self hs)
    · change Φ (q t).2.1 (q t).2.2 i j = Φ (q 0).2.1 (q 0).2.2 i j + ∫ s in (0 : ℝ)..t,
        (controlP (u s) (Φ (q s).2.1 (q s).2.2) * Φ (q s).2.1 (q s).2.2 -
          Φ (q s).2.1 (q s).2.2 * controlP (u s) (Φ (q s).2.1 (q s).2.2)) i j
      rw [hE t ht]
      congr 1
      refine intervalIntegral.integral_congr fun s hs ↦ ?_
      rw [uIcc_of_le ht.1] at hs
      exact hpt s ⟨hs.1, hs.2.trans ht.2⟩

/-- `R⁻¹⁻¹ = R`. -/
private lemma iw_R_inv_inv : R⁻¹⁻¹ = R := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hdet : R.det = 1 := by
    rw [R, Matrix.det_fin_two_of]
    linear_combination h3 / 4
  exact Matrix.nonsing_inv_nonsing_inv R (by rw [hdet]; exact isUnit_one)

/-- The terminal condition in the half-plane: `Φ(R⁻¹ · z) = R⁻¹Φ(z)R` (`Φ_mobius`). -/
private lemma iw_Φ_mobius_R_inv {z : ℝ × ℝ} (hz : 0 < z.2) :
    Φ (mobius R⁻¹ z).1 (mobius R⁻¹ z).2 = R⁻¹ * Φ z.1 z.2 * R := by
  rw [(Φ_mobius iw_det_R_inv hz).2, iw_R_inv_inv]

/-- `Φ` is injective on the upper half-plane (Lemma 4.2.1; `y = 1/X₁₀`, `x = X₀₀/X₁₀`). -/
private lemma iw_Φ_inj {z w : ℝ × ℝ} (hw : 0 < w.2)
    (h : Φ z.1 z.2 = Φ w.1 w.2) : z = w := by
  have h10 := congrFun (congrFun h 1) 0
  have h00 := congrFun (congrFun h 0) 0
  simp only [Φ, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at h10 h00
  have hy : z.2 = w.2 := by
    rw [one_div, one_div] at h10
    exact inv_injective h10
  rw [hy] at h00
  exact Prod.ext ((div_left_inj' hw.ne').1 h00) hy

/-- The terminal condition `X(T) = R⁻¹X(0)R` in the half-plane is `z(T) = R⁻¹ · z(0)`. -/
private lemma iw_eq_mobius_of_Φ {z₀ z₁ : ℝ × ℝ} (h₀ : 0 < z₀.2)
    (h : Φ z₁.1 z₁.2 = R⁻¹ * Φ z₀.1 z₀.2 * R) : z₁ = mobius R⁻¹ z₀ :=
  iw_Φ_inj (Φ_mobius iw_det_R_inv h₀).1 (h.trans (iw_Φ_mobius_R_inv h₀).symm)

/-- **A Reinhardt minimizer lifts to a strong local minimizer of the lifted problem**: its lift
`q` (with `p(0) = 0`) minimizes the cost among the admissible pairs of the lifted problem with
the boundary condition `liftedEndpoints (q T).1`, since these project to admissible trajectories
of Problem 3.6.2 with the same cost; in particular it is a strong local minimizer. -/
theorem IsReinhardtMinimizer.exists_lift {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsReinhardtMinimizer T u g X) :
    ∃ q : ℝ → LiftedState, (q 0).1 = 0 ∧
      (∀ t ∈ Icc 0 T, iwasawa (q t).1 = g t ∧ Φ (q t).2.1 (q t).2.2 = X t) ∧
      IsStrongLocalMinimizer liftedField liftedCost liftedDomain controlSimplex
        (liftedEndpoints (q T).1) T u q := by
  obtain ⟨⟨hst, hg0, hgT, hXT⟩, hmin⟩ := h
  obtain ⟨q, hq0, hqgX, hadm⟩ := hst.exists_lift hg0
  have hT : 0 < T := hst.1
  have h0mem : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hTmem : T ∈ Icc 0 T := ⟨hT.le, le_rfl⟩
  refine ⟨q, hq0, hqgX, hT, hadm, ?_, 1, one_pos, ?_⟩
  -- the boundary condition: `z(T) = R⁻¹ · z(0)` since `Φ(z(T)) = X(T) = R⁻¹X(0)R`
  · have hz := iw_eq_mobius_of_Φ (hadm.2 0 h0mem).2.1
      (by rw [(hqgX T hTmem).2, (hqgX 0 h0mem).2, hXT])
    change liftedBoundary (q T).1 (q 0, q T) = 0
    simp only [liftedBoundary, hq0, sub_self, ← hz]
    rfl
  -- a competitor projects to an admissible trajectory of Problem 3.6.2 with the same cost
  · intro T' u' q' hT' hadm' hbd _ _
    have hb : liftedBoundary (q T).1 (q' 0, q' T') = 0 := hbd
    simp only [liftedBoundary, Prod.mk_eq_zero, sub_eq_zero] at hb
    obtain ⟨hb1, hb2, hb3⟩ := hb
    have hadm'' : IsReinhardtAdmissible T' u' (fun t ↦ iwasawa (q' t).1)
        (fun t ↦ Φ (q' t).2.1 (q' t).2.2) := by
      refine ⟨isStateTrajectory_of_isAdmissibleIn hT' hadm', ?_, ?_, ?_⟩
      · simp only [hb1, iwasawa_zero]
      · simp only [hb2, (hqgX T hTmem).1, hgT]
      · simp only [hb3]
        exact iw_Φ_mobius_R_inv (hadm'.2 0 ⟨le_rfl, hT'.le⟩).2.1
    rw [cost_liftedCost, cost_liftedCost]
    calc reinhardtCost T (fun t ↦ Φ (q t).2.1 (q t).2.2) = reinhardtCost T X := by
          simp only [reinhardtCost]
          congr 1
          refine intervalIntegral.integral_congr fun t ht ↦ ?_
          rw [uIcc_of_le hT.le] at ht
          simp only [(hqgX t ht).2]
      _ ≤ _ := hmin T' u' _ _ hadm''

end SmoothedPolygons
