module

public import SmoothedPolygons.Ch6.Hamiltonian
public import SmoothedPolygons.Ch7.DiscreteK

/-!
# Periodic extension of extremals (Remark 6.6.1)

The unlabelled Remark 6.6.1 of §6.6 (TeX 5216–5242):

* "The transversality conditions in the Reinhardt problem require the terminal time to satisfy
  `X(t_f) = R⁻¹X₀R`, where `R` is the usual rotation matrix. Thus, if we extend time, every
  optimal solution can be made into a periodic one. `X(3t_f) = X₀`. The same requirement also
  holds of `g`, `Λ₁` and `Λ_R`, except that the period for `g` is larger: `g(6t_f) = I₂`. Thus,
  every transversal trajectory determines a periodic solution (with discrete rotational
  symmetry) of the lifted trajectories in the cotangent bundle." (`remark6_6_1`)
* "The transversality condition for `Λ₁` is a consequence of the transversality condition for
  `g`. In fact, we know the general solution for `Λ₁` in terms of `g`. See Corollary 6.5.3."
  (`remark6_6_1_lambda1`)

The extension: for `t ∈ [kT, (k + 1)T)`, `s = t - kT`,
`g(t) = g(s)Rᵏ`, `X(t) = R⁻ᵏX(s)Rᵏ`, `Λᵢ(t) = R⁻ᵏΛᵢ(s)Rᵏ`, and the control is rotated, `u(t)`
being `u(s)` with its coordinates permuted cyclically `k` times, so that
`Z_{u(t)} = R⁻ᵏ Z_{u(s)} Rᵏ` (`R⁻¹Z_{e_m}R = Z_{e_{m+1}}`). Since `R³ = -I` and `R⁶ = I`,
conjugation by `R` has order 3 and right multiplication by `R` order 6. The state–costate
equations are invariant under this symmetry (`J` commutes with `R`, the trace form is
conjugation invariant, the star domain is invariant under the rotation, §4.6), and the pieces
join continuously by the transversality conditions (6.6.1).

`IsStateCostateSolution` is the state–costate system of Problem 6.7.1 with the conditions of the
maximum principle but without the boundary conditions: `IsPontryaginExtremal` is it together
with the transversality conditions (6.6.1) (`isPontryaginExtremal_iff`).

The extension is `poly_pw` of `SmoothedPolygons/Ch7/DiscreteK.lean` (the same construction that
assembles the smoothed polygons from one switching interval), with the conjugation identities
of that file: `R⁻¹Z_{e_m}R = Z_{e_{m+1}}` (`poly_Rinv_conj_vertex`, extended to `U_T` by
linearity, `ct_controlMatrix_rot_one`), `R⁻ᵏJRᵏ = J`, `R³ = -I`, and the `R`-invariance of the
star states (`poly_isStarState_conj_pow`). Since the controls are only measurable, the pieces are
glued as Carathéodory solutions (`ct_pw_isIntegralCurve`: change of variables on each piece,
`ct_piece`, and additivity of the integral, `ct_stitch`), and the almost-everywhere conditions
are translated piece by piece (`ct_ae_pw`).
-/

@[expose] public section

namespace SmoothedPolygons

open Set MeasureTheory Filter Topology Matrix
open scoped Interval

/-- The state–costate system of Problem 6.7.1 on `[0, T]` with the conditions of the maximum
principle (§6.2: `λ_cost ≤ 0`, nontriviality, maximum condition and `H = 0` almost everywhere),
without boundary conditions: `IsPontryaginExtremal` without its transversality conditions. -/
def IsStateCostateSolution (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X Λ₁ ΛR : ℝ → Mat2) (lam : ℝ) : Prop :=
  IsStateTrajectory T u g X ∧ lam ≤ 0 ∧
    (∀ t ∈ Set.Icc 0 T, (Λ₁ t).trace = 0 ∧ (ΛR t).trace = 0 ∧ traceForm (ΛR t) (X t) = 0 ∧
      (lam ≠ 0 ∨ Λ₁ t ≠ 0 ∨ ΛR t ≠ 0)) ∧
    IsIntegralCurve Λ₁ (fun t ↦ Λ₁ t * X t - X t * Λ₁ t) T ∧
    IsIntegralCurve ΛR (fun t ↦
      (controlP (u t) (X t) * ΛR t - ΛR t * controlP (u t) (X t)) -
        traceForm (ΛR t) (controlP (u t) (X t)) •
          (controlP (u t) (X t) * X t - X t * controlP (u t) (X t)) +
        ((-Λ₁ t + (3 / 2 * lam) • J) * X t - X t * (-Λ₁ t + (3 / 2 * lam) • J))) T ∧
    ∀ᵐ t, t ∈ Set.Ioo 0 T →
      hamiltonian lam (Λ₁ t) (ΛR t) (X t) (u t) = 0 ∧
        ∀ v ∈ controlSimplex,
          hamiltonian lam (Λ₁ t) (ΛR t) (X t) v ≤ hamiltonian lam (Λ₁ t) (ΛR t) (X t) (u t)

/-- A Pontryagin extremal is a solution of the state–costate system with the transversality
conditions (6.6.1). -/
theorem isPontryaginExtremal_iff {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ} :
    IsPontryaginExtremal T u g X Λ₁ ΛR lam ↔ IsStateCostateSolution T u g X Λ₁ ΛR lam ∧
      g 0 = 1 ∧ g T = R ∧ X T = R⁻¹ * X 0 * R ∧ Λ₁ T = R⁻¹ * Λ₁ 0 * R ∧
      ΛR T = R⁻¹ * ΛR 0 * R := by
  unfold IsPontryaginExtremal IsStateCostateSolution
  tauto

/-- **Remark 6.6.1**, second item (`rem:lam1-transversality`, label of this formalization):
the transversality condition for `Λ₁` follows from the one for `g`: if `g' = gX` with
`g(0) = I₂`, `g(t_f) = R`, and `Λ₁' = [Λ₁, X]`, then `Λ₁(t_f) = R⁻¹Λ₁(0)R`, because
`Λ₁(t) = g(t)⁻¹Λ₁(0)g(t)` (Corollary 6.5.3, for Carathéodory solutions).

Proof as in the book: the integrands `gX` and `[Λ₁, X]` are continuous, so `g` and `Λ₁` are
differentiable on `[0, t_f]` (FTC-1), and Corollary 6.5.3 gives
`Λ₁(t_f) = g(t_f)⁻¹Λ₁(0)g(t_f) = R⁻¹Λ₁(0)R`. -/
theorem remark6_6_1_lambda1 {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ : ℝ → Mat2}
    (h : IsStateTrajectory T u g X) (hg0 : g 0 = 1) (hgT : g T = R)
    (hΛ : IsIntegralCurve Λ₁ (fun t ↦ Λ₁ t * X t - X t * Λ₁ t) T) :
    Λ₁ T = R⁻¹ * Λ₁ 0 * R := by
  obtain ⟨hT, -, -, hst, hgI, hXI⟩ := h
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
  -- Corollary 6.5.3: `Λ₁(t) = g(t)⁻¹ Λ₁(0) g(t)`, and `g(t_f) = R`
  have h := (corollary6_5_3 T g X Λ₁ hg hg0 (fun t ht ↦ (hst t ht).1) hΛ' T ⟨hT.le, le_rfl⟩).1
  rwa [hgT] at h

/-! ### The rotation of controls and the equivariance of the system -/

/-- The control rotated `k` times, `(rot^k v)_j = v_{j - k}` (indices mod 3), so that
`Z_{rot^k v} = R⁻ᵏ Z_v Rᵏ` (`ct_controlMatrix_rot`). -/
private def ct_rot (k : ℕ) (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun j ↦ v ⟨(j.val + 2 * k) % 3, Nat.mod_lt _ (by norm_num)⟩

private lemma ct_rot_succ (k : ℕ) (v : Fin 3 → ℝ) :
    ct_rot (k + 1) v = fun j ↦ ct_rot k v (j - 1) := by
  funext j
  simp only [ct_rot]
  congr 1
  ext
  simp only [Fin.sub_def]
  fin_cases j <;> simp <;> omega

private lemma ct_rot_zero (v : Fin 3 → ℝ) : ct_rot 0 v = v := by
  funext j
  simp [ct_rot, Nat.mod_eq_of_lt j.isLt]

/-- `R⁻¹ Z_v R = Z_{rot v}`: the linear extension to all controls of the identity
`R⁻¹Z_{e_m}R = Z_{e_{m+1}}` for the vertices of `U_T` (`poly_Rinv_conj_vertex`), checked here
entry by entry with `R⁻¹ = [[1/2, √3/2], [-√3/2, 1/2]]` (`poly_R_inv`). -/
private lemma ct_controlMatrix_rot_one (v : Fin 3 → ℝ) :
    controlMatrix (ct_rot 1 v) = R⁻¹ * controlMatrix v * R := by
  rw [poly_R_inv]
  have h3 : √3 ^ 2 = 3 := poly_sqrt3_sq
  have h3' : √3 ≠ 0 := by positivity
  have e0 : ct_rot 1 v 0 = v 2 := rfl
  have e1 : ct_rot 1 v 1 = v 0 := rfl
  have e2 : ct_rot 1 v 2 = v 1 := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [controlMatrix, R, Matrix.mul_apply, Fin.sum_univ_two, e0, e1, e2] <;> field_simp <;>
    simp only [h3] <;> ring


private lemma ct_rot_one_rot (k : ℕ) (v : Fin 3 → ℝ) :
    ct_rot (k + 1) v = ct_rot 1 (ct_rot k v) := by
  rw [ct_rot_succ, ct_rot_succ 0, ct_rot_zero]

private lemma ct_rot_mod (k : ℕ) (v : Fin 3 → ℝ) : ct_rot k v = ct_rot (k % 3) v := by
  funext j
  simp only [ct_rot]
  congr 2
  omega

private lemma ct_rot_rot (k m : ℕ) (v : Fin 3 → ℝ) : ct_rot k (ct_rot m v) = ct_rot (m + k) v := by
  funext j
  simp only [ct_rot]
  congr 2
  omega

/-- `Z_{rot^k v} = R⁻ᵏ Z_v Rᵏ` (from `R⁻¹ Z_v R = Z_{rot v}`, cf. `poly_Rinv_conj_vertex`). -/
private lemma ct_controlMatrix_rot (k : ℕ) (v : Fin 3 → ℝ) :
    controlMatrix (ct_rot k v) = R⁻¹ ^ k * controlMatrix v * R ^ k := by
  induction k with
  | zero => simp [ct_rot_zero]
  | succ k ih =>
    rw [ct_rot_one_rot, ct_controlMatrix_rot_one, ih, pow_succ', pow_succ]
    simp only [Matrix.mul_assoc]

private lemma ct_rot_mem (k : ℕ) {v : Fin 3 → ℝ} (hv : v ∈ controlSimplex) :
    ct_rot k v ∈ controlSimplex := by
  obtain ⟨h01, hsum⟩ := hv
  refine ⟨fun i ↦ h01 _, ?_⟩
  rw [ct_rot_mod]
  have hk : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases (k % 3)
  · simpa [ct_rot_zero] using hsum
  · have e : ct_rot 1 v 0 + ct_rot 1 v 1 + ct_rot 1 v 2 = v 2 + v 0 + v 1 := rfl
    rw [e]; linarith
  · have e : ct_rot 2 v 0 + ct_rot 2 v 1 + ct_rot 2 v 2 = v 1 + v 2 + v 0 := rfl
    rw [e]; linarith

private lemma ct_conj_cancel (k : ℕ) (M : Mat2) : R ^ k * (R⁻¹ ^ k * M * R ^ k) * R⁻¹ ^ k = M := by
  simp only [← Matrix.mul_assoc, poly_Rpow_mul_Rinvpow, Matrix.one_mul]
  rw [Matrix.mul_assoc, poly_Rpow_mul_Rinvpow, Matrix.mul_one]

private lemma ct_controlP_rot (k : ℕ) (v : Fin 3 → ℝ) (S : Mat2) :
    controlP (ct_rot k v) (R⁻¹ ^ k * S * R ^ k) = R⁻¹ ^ k * controlP v S * R ^ k :=
  (poly_controlP_conj (poly_Rpow_mul_Rinvpow k) (ct_controlMatrix_rot k v).symm S).symm

private lemma ct_costateRHS_rot (lam : ℝ) (k : ℕ) (Λ₁ ΛR X : Mat2) (v : Fin 3 → ℝ) :
    costateRHS lam (R⁻¹ ^ k * Λ₁ * R ^ k) (R⁻¹ ^ k * ΛR * R ^ k) (R⁻¹ ^ k * X * R ^ k)
        (ct_rot k v) = R⁻¹ ^ k * costateRHS lam Λ₁ ΛR X v * R ^ k := by
  have h := poly_Rpow_mul_Rinvpow k
  unfold costateRHS
  rw [ct_controlP_rot]
  simp only [poly_conj_add, poly_conj_sub, poly_conj_neg, poly_conj_smul, poly_conj_mul h,
    poly_conj_pow_J, poly_traceForm_conj h]

private lemma ct_hamiltonian_rot (lam : ℝ) (k : ℕ) (Λ₁ ΛR X : Mat2) (v : Fin 3 → ℝ) :
    hamiltonian lam (R⁻¹ ^ k * Λ₁ * R ^ k) (R⁻¹ ^ k * ΛR * R ^ k) (R⁻¹ ^ k * X * R ^ k)
        (ct_rot k v) = hamiltonian lam Λ₁ ΛR X v := by
  have h := poly_Rpow_mul_Rinvpow k
  have hJ : R⁻¹ ^ k * Λ₁ * R ^ k - (3 / 2 * lam) • J =
      R⁻¹ ^ k * (Λ₁ - (3 / 2 * lam) • J) * R ^ k := by
    rw [poly_conj_sub, poly_conj_smul, poly_conj_pow_J]
  unfold hamiltonian
  rw [ct_controlMatrix_rot, poly_traceForm_conj h, poly_traceForm_conj h, hJ,
    poly_traceForm_conj h]


/-! ### Piecewise integral curves (Carathéodory) -/

private lemma ct_mul_apply (A M B : Mat2) (i j : Fin 2) :
    (A * M * B) i j = A i 0 * B 0 j * M 0 0 + A i 0 * B 1 j * M 0 1 + A i 1 * B 0 j * M 1 0 +
      A i 1 * B 1 j * M 1 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- A conjugated, shifted integral curve `t ↦ A f₀(t - c) B` on `[c, c + τ]`. -/
private lemma ct_piece {f0 v0 : ℝ → Mat2} {τ : ℝ} (hτ : 0 ≤ τ) (hI : IsIntegralCurve f0 v0 τ)
    (A B : Mat2) (c : ℝ) (i j : Fin 2) :
    IntervalIntegrable (fun s ↦ (A * v0 (s - c) * B) i j) volume c (c + τ) ∧
      ∀ t ∈ Icc c (c + τ), (A * f0 (t - c) * B) i j =
        (A * f0 0 * B) i j + ∫ s in c..t, (A * v0 (s - c) * B) i j := by
  have hint : ∀ k l, IntervalIntegrable (fun s ↦ v0 (s - c) k l) volume c (c + τ) := by
    intro k l
    simpa [add_comm] using (hI k l).1.comp_sub_right c
  have hint' : ∀ t ∈ Icc c (c + τ), ∀ k l,
      IntervalIntegrable (fun s ↦ v0 (s - c) k l) volume c t := fun t ht k l ↦
    (hint k l).mono_set (by
      rw [uIcc_of_le ht.1, uIcc_of_le (by linarith)]; exact Icc_subset_Icc_right ht.2)
  simp only [ct_mul_apply]
  refine ⟨((((hint 0 0).const_mul _).add ((hint 0 1).const_mul _)).add
    ((hint 1 0).const_mul _)).add ((hint 1 1).const_mul _), fun t ht ↦ ?_⟩
  have hf : ∀ k l, f0 (t - c) k l = f0 0 k l + ∫ s in c..t, v0 (s - c) k l := by
    intro k l
    have e := intervalIntegral.integral_comp_sub_right (f := fun s ↦ v0 s k l) (a := c) (b := t) c
    rw [sub_self] at e
    rw [(hI k l).2 (t - c) ⟨by linarith [ht.1], by linarith [ht.2]⟩, e]
  have h := hint' t ht
  rw [intervalIntegral.integral_add (((h 0 0).const_mul _).add ((h 0 1).const_mul _)
      |>.add ((h 1 0).const_mul _)) ((h 1 1).const_mul _),
    intervalIntegral.integral_add (((h 0 0).const_mul _).add ((h 0 1).const_mul _))
      ((h 1 0).const_mul _),
    intervalIntegral.integral_add ((h 0 0).const_mul _) ((h 0 1).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    hf 0 0, hf 0 1, hf 1 0, hf 1 1]
  ring

/-- Stitching integral curves on adjacent intervals. -/
private lemma ct_stitch {f v : ℝ → Mat2} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (h1 : IsIntegralCurve f v a)
    (h2 : ∀ i j, IntervalIntegrable (fun s ↦ v s i j) volume a b ∧
      ∀ t ∈ Icc a b, f t i j = f a i j + ∫ s in a..t, v s i j) :
    IsIntegralCurve f v b := by
  intro i j
  obtain ⟨hi1, he1⟩ := h1 i j
  obtain ⟨hi2, he2⟩ := h2 i j
  refine ⟨hi1.trans hi2, fun t ht ↦ ?_⟩
  rcases le_total t a with hta | hta
  · exact he1 t ⟨ht.1, hta⟩
  · have hi3 : IntervalIntegrable (fun s ↦ v s i j) volume a t := hi2.mono_set (by
      rw [uIcc_of_le hta, uIcc_of_le hab]; exact Icc_subset_Icc_right ht.2)
    rw [he2 t ⟨hta, ht.2⟩, he1 a ⟨ha, le_rfl⟩, add_assoc,
      intervalIntegral.integral_add_adjacent_intervals hi1 hi3]

/-- **Piecewise integral curves**: the curve `Aⁱ f₀(t - iτ) Bⁱ` on `[iτ, (i+1)τ]`, glued by
`f₀(τ) = A f₀(0) B`, is a (Carathéodory) integral curve of every `v` that agrees with
`Aⁱ v₀(t - iτ) Bⁱ` on the open pieces. -/
private lemma ct_pw_isIntegralCurve {A B : Mat2} {τ : ℝ} (hτ : 0 < τ) {f0 v0 : ℝ → Mat2}
    (hI : IsIntegralCurve f0 v0 τ) (hglue : f0 τ = A * f0 0 * B) (N : ℕ) {v : ℝ → Mat2}
    (hv : ∀ i < N, ∀ t ∈ Ioo (i * τ) ((i + 1) * τ), v t = A ^ i * v0 (t - i * τ) * B ^ i) :
    IsIntegralCurve (poly_pw A B τ f0) v (N * τ) := by
  induction N with
  | zero =>
    intro i j
    refine ⟨by simp, fun t ht ↦ ?_⟩
    have : t = 0 := by simp only [Nat.cast_zero, zero_mul] at ht; exact le_antisymm ht.2 ht.1
    subst this
    simp
  | succ n ih =>
    have ih' := ih fun i hi ↦ hv i (by omega)
    have hn : (n : ℝ) * τ + τ = ((n + 1 : ℕ) : ℝ) * τ := by push_cast; ring
    refine ct_stitch (by positivity) (by rw [← hn]; linarith) ih' fun i j ↦ ?_
    obtain ⟨hint, heq⟩ := ct_piece hτ.le hI (A ^ n) (B ^ n) (n * τ) i j
    rw [hn] at hint heq
    -- `v` agrees with the piece's integrand off the endpoints
    have hae : ∀ᵐ s, s ∈ Ι ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ) →
        (A ^ n * v0 (s - n * τ) * B ^ n) i j = v s i j := by
      filter_upwards [(countable_singleton (((n + 1 : ℕ) : ℝ) * τ)).ae_notMem volume] with s hs hsI
      rw [uIoc_of_le (by rw [← hn]; linarith)] at hsI
      rw [hv n (by omega) s ⟨hsI.1, by
        have := lt_of_le_of_ne hsI.2 hs
        push_cast at this
        exact this⟩]
    refine ⟨hint.congr_ae ((ae_restrict_iff' measurableSet_uIoc).2 hae), fun t ht ↦ ?_⟩
    have ht' : t ∈ Icc ((n : ℝ) * τ) (((n : ℝ) + 1) * τ) := by push_cast at ht; exact ht
    have h0 : (n : ℝ) * τ ∈ Icc ((n : ℝ) * τ) (((n : ℝ) + 1) * τ) := ⟨le_rfl, by nlinarith⟩
    rw [poly_pw_of_mem_Icc hτ hglue ht', poly_pw_of_mem_Icc hτ hglue h0, sub_self, heq t ht]
    congr 1
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae] with s hs hsI
    exact hs (by
      rw [uIoc_of_le ht.1] at hsI
      rw [uIoc_of_le (by rw [← hn]; linarith)]
      exact ⟨hsI.1, hsI.2.trans ht.2⟩)

/-- Almost every point of `(0, Nτ)` is interior to a piece `(iτ, (i+1)τ)` and is translated by
`-iτ` to a point of a given full-measure subset of `(0, τ)`. -/
private lemma ct_ae_pw {τ : ℝ} (hτ : 0 < τ) {P : ℝ → Prop} (h : ∀ᵐ s, s ∈ Ioo 0 τ → P s)
    (N : ℕ) :
    ∀ᵐ t, t ∈ Ioo 0 (N * τ) → ⌊t / τ⌋₊ < N ∧ t - ⌊t / τ⌋₊ * τ ∈ Ioo 0 τ ∧
      P (t - ⌊t / τ⌋₊ * τ) := by
  have hi : ∀ i : ℕ, ∀ᵐ t, t - i * τ ∈ Ioo 0 τ → P (t - i * τ) := fun i ↦
    (measurePreserving_sub_right volume ((i : ℝ) * τ)).quasiMeasurePreserving.ae h
  have hS : ∀ᵐ t, t ∉ range (fun i : ℕ ↦ (i : ℝ) * τ) := (countable_range _).ae_notMem _
  filter_upwards [ae_all_iff.2 hi, hS] with t ht htS htI
  obtain ⟨h1, h2⟩ := poly_floor_mem hτ htI.1.le
  have h1' : (⌊t / τ⌋₊ : ℝ) * τ < t := lt_of_le_of_ne h1 fun h ↦ htS ⟨_, h⟩
  have hmem : t - ⌊t / τ⌋₊ * τ ∈ Ioo 0 τ := ⟨by linarith, by linarith⟩
  refine ⟨(Nat.floor_lt (div_nonneg htI.1.le hτ.le)).2 ((div_lt_iff₀ hτ).2 htI.2), hmem,
    ht _ hmem⟩


/-! ### The periodic extension -/

/-- One period later, the piecewise curve is conjugated once more. -/
private lemma ct_pw_add {A B : Mat2} {τ : ℝ} (hτ : 0 < τ) (f0 : ℝ → Mat2) {t : ℝ} (ht : 0 ≤ t) :
    poly_pw A B τ f0 (t + τ) = A * poly_pw A B τ f0 t * B := by
  have hk : ⌊(t + τ) / τ⌋₊ = ⌊t / τ⌋₊ + 1 := by
    rw [add_div, div_self hτ.ne', Nat.floor_add_one (div_nonneg ht hτ.le)]
  simp only [poly_pw, hk]
  push_cast
  rw [show t + τ - ((⌊t / τ⌋₊ : ℝ) + 1) * τ = t - ⌊t / τ⌋₊ * τ by ring, pow_succ', pow_succ]
  simp only [Matrix.mul_assoc]

/-- **Remark 6.6.1**, first item (`rem:periodic-extension`, label of this formalization): every
Pontryagin extremal on `[0, t_f]` (a "transversal trajectory") extends, with discrete rotational
symmetry, to a periodic solution of the state–costate system: there are `u', g', X', Λ₁', Λ_R'`
on `[0, ∞)`, equal to `u, g, X, Λ₁, Λ_R` on `[0, t_f]` (the control on `[0, t_f)`), such that

* `g'(t + t_f) = g'(t)R`, `X'(t + t_f) = R⁻¹X'(t)R`, `Λᵢ'(t + t_f) = R⁻¹Λᵢ'(t)R`, and the control
  is rotated, `u'(t + t_f)ⱼ = u'(t)_{j-1}` (so `Z_{u'(t + t_f)} = R⁻¹Z_{u'(t)}R`);
* `X'(3t_f) = X₀` and `g'(6t_f) = I₂`, and more generally `u', X', Λ₁', Λ_R'` are periodic with
  period `3t_f` and `g'` with period `6t_f`;
* for every `n ≥ 1`, the extension solves the state–costate system on `[0, n t_f]`
  (`IsStateCostateSolution`), with the same `λ_cost`.

Proof (the book gives the construction in one sentence): on `[kt_f, (k+1)t_f)` put
`u'(t) = rot^k u(t - kt_f)`, `g'(t) = g(t - kt_f)Rᵏ` and `Y'(t) = R⁻ᵏY(t - kt_f)Rᵏ` for
`Y = X, Λ₁, Λ_R`; the transversality conditions (6.6.1) glue the pieces continuously, and the
state–costate system, the Hamiltonian and `U_T` are invariant under the rotation. -/
theorem remark6_6_1 {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (h : IsPontryaginExtremal T u g X Λ₁ ΛR lam) :
    ∃ (u' : ℝ → Fin 3 → ℝ) (g' X' Λ₁' ΛR' : ℝ → Mat2),
      (∀ t ∈ Ico 0 T, u' t = u t) ∧
      (∀ t ∈ Icc 0 T, g' t = g t ∧ X' t = X t ∧ Λ₁' t = Λ₁ t ∧ ΛR' t = ΛR t) ∧
      (∀ t, 0 ≤ t → (u' (t + T) = fun j ↦ u' t (j - 1)) ∧ g' (t + T) = g' t * R ∧
        X' (t + T) = R⁻¹ * X' t * R ∧ Λ₁' (t + T) = R⁻¹ * Λ₁' t * R ∧
        ΛR' (t + T) = R⁻¹ * ΛR' t * R) ∧
      X' (3 * T) = X 0 ∧ g' (6 * T) = 1 ∧
      (∀ t, 0 ≤ t → u' (t + 3 * T) = u' t ∧ g' (t + 6 * T) = g' t ∧ X' (t + 3 * T) = X' t ∧
        Λ₁' (t + 3 * T) = Λ₁' t ∧ ΛR' (t + 3 * T) = ΛR' t) ∧
      ∀ n : ℕ, 0 < n → IsStateCostateSolution (n * T) u' g' X' Λ₁' ΛR' lam := by
  obtain ⟨hst, hg0, hgT, hXT, hΛ₁T, hΛRT, hlam, hcost, hΛ₁I, hΛRI, hH⟩ := h
  have hT : 0 < T := hst.1
  obtain ⟨-, hum, huU, hstar, hgI, hXI⟩ := hst
  have hgglue : g T = 1 * g 0 * R := by rw [hgT, hg0, Matrix.one_mul, Matrix.one_mul]
  -- the floor and the position in the period
  have hfl : ∀ t, 0 ≤ t → ∀ m : ℕ, ⌊(t + m * T) / T⌋₊ = ⌊t / T⌋₊ + m := by
    intro t ht m
    rw [add_div, mul_div_assoc, div_self hT.ne', mul_one, Nat.floor_add_natCast
      (div_nonneg ht hT.le)]
  have hsh : ∀ t, 0 ≤ t → ∀ m : ℕ,
      t + m * T - ((⌊(t + m * T) / T⌋₊ : ℕ) : ℝ) * T = t - ⌊t / T⌋₊ * T := by
    intro t ht m
    rw [hfl t ht m]
    push_cast
    ring
  have hmem : ∀ t, 0 ≤ t → t - ⌊t / T⌋₊ * T ∈ Icc 0 T := fun t ht ↦ by
    obtain ⟨h1, h2⟩ := poly_floor_mem hT ht
    exact ⟨by linarith, by linarith⟩
  have hfl0 : ∀ t ∈ Ico 0 T, ⌊t / T⌋₊ = 0 := fun t ht ↦
    poly_floor_eq hT (by simpa using ht.1) (by simpa using ht.2)
  -- the rotated control
  set u' : ℝ → Fin 3 → ℝ := fun t ↦ ct_rot ⌊t / T⌋₊ (u (t - ⌊t / T⌋₊ * T)) with hu'
  have hu'add : ∀ t, 0 ≤ t → ∀ m : ℕ, u' (t + m * T) = ct_rot m (u' t) := by
    intro t ht m
    have e : t + m * T - ((⌊t / T⌋₊ + m : ℕ) : ℝ) * T = t - ⌊t / T⌋₊ * T := by push_cast; ring
    simp only [hu', hfl t ht m, e, ct_rot_rot]
  refine ⟨u', poly_pw 1 R T g, poly_pw R⁻¹ R T X, poly_pw R⁻¹ R T Λ₁, poly_pw R⁻¹ R T ΛR,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    simp [hu', hfl0 t ht, ct_rot_zero]
  · intro t ht
    have h0 : t ∈ Icc (((0 : ℕ) : ℝ) * T) (((0 : ℕ) + 1) * T) := by simpa using ht
    simp only [poly_pw_of_mem_Icc hT hgglue h0, poly_pw_of_mem_Icc hT hXT h0,
      poly_pw_of_mem_Icc hT hΛ₁T h0, poly_pw_of_mem_Icc hT hΛRT h0]
    simp
  · intro t ht
    refine ⟨?_, by rw [ct_pw_add hT g ht, Matrix.one_mul], ct_pw_add hT X ht, ct_pw_add hT Λ₁ ht,
      ct_pw_add hT ΛR ht⟩
    have := hu'add t ht 1
    rw [Nat.cast_one, one_mul] at this
    rw [this, ct_rot_one_rot 0, ct_rot_zero, ct_rot_succ 0, ct_rot_zero]
  · have h3 : ⌊(0 + ((3 : ℕ) : ℝ) * T) / T⌋₊ = 3 := by rw [hfl 0 le_rfl 3]; simp
    simp only [poly_pw]
    rw [show (3 : ℝ) * T = 0 + ((3 : ℕ) : ℝ) * T by push_cast; ring, h3]
    push_cast
    rw [show (0 : ℝ) + 3 * T - 3 * T = 0 by ring, poly_Rinv_pow_three, poly_R_pow_three]
    simp
  · have h6 : ⌊(0 + ((6 : ℕ) : ℝ) * T) / T⌋₊ = 6 := by rw [hfl 0 le_rfl 6]; simp
    simp only [poly_pw]
    rw [show (6 : ℝ) * T = 0 + ((6 : ℕ) : ℝ) * T by push_cast; ring, h6]
    push_cast
    rw [show (0 : ℝ) + 6 * T - 6 * T = 0 by ring, hg0, one_pow, Matrix.one_mul, Matrix.one_mul,
      show R ^ 6 = (R ^ 3) ^ 2 by rw [← pow_mul], poly_R_pow_three]
    simp
  · intro t ht
    have e3 : t + 3 * T = t + T + T + T := by ring
    have e6 : t + 6 * T = t + T + T + T + T + T + T := by ring
    have p1 : 0 ≤ t + T := by linarith
    have p2 : 0 ≤ t + T + T := by linarith
    have p3 : 0 ≤ t + T + T + T := by linarith
    have p4 : 0 ≤ t + T + T + T + T := by linarith
    have p5 : 0 ≤ t + T + T + T + T + T := by linarith
    have hX3 : ∀ f0 : ℝ → Mat2, poly_pw R⁻¹ R T f0 (t + 3 * T) = poly_pw R⁻¹ R T f0 t := by
      intro f0
      rw [e3, ct_pw_add hT f0 p2, ct_pw_add hT f0 p1, ct_pw_add hT f0 ht]
      simp only [← Matrix.mul_assoc]
      rw [show R⁻¹ * R⁻¹ * R⁻¹ = R⁻¹ ^ 3 by simp [pow_succ], poly_Rinv_pow_three]
      simp only [Matrix.mul_assoc]
      rw [show R * (R * R) = R ^ 3 by simp [pow_succ, Matrix.mul_assoc], poly_R_pow_three]
      simp
    refine ⟨?_, ?_, hX3 X, hX3 Λ₁, hX3 ΛR⟩
    · have := hu'add t ht 3
      rw [show ((3 : ℕ) : ℝ) = 3 by norm_num] at this
      rw [this, ct_rot_mod, show 3 % 3 = 0 from rfl, ct_rot_zero]
    · rw [e6, ct_pw_add hT g p5, ct_pw_add hT g p4, ct_pw_add hT g p3, ct_pw_add hT g p2,
        ct_pw_add hT g p1, ct_pw_add hT g ht]
      simp only [Matrix.one_mul, Matrix.mul_assoc]
      rw [show R * (R * (R * (R * (R * R)))) = (R ^ 3) ^ 2 by
        simp [pow_succ, Matrix.mul_assoc], poly_R_pow_three]
      simp
  · intro n hn
    have hnT : (0 : ℝ) < n * T := mul_pos (by exact_mod_cast hn) hT
    refine ⟨⟨hnT, ?_, fun t ht ↦ ct_rot_mem _ (huU _ (hmem t ht.1)), fun t ht ↦ ?_, ?_, ?_⟩,
      hlam, fun t ht ↦ ?_, ?_, ?_, ?_⟩
    · -- the rotated control is measurable
      refine measurable_pi_iff.2 fun j ↦ ?_
      have hF : Measurable (fun p : ℝ × ℕ ↦
          u (p.1 - p.2 * T) ⟨(j.val + 2 * p.2) % 3, Nat.mod_lt _ (by norm_num)⟩) :=
        measurable_from_prod_countable_left fun k ↦
          (measurable_pi_apply (⟨(j.val + 2 * k) % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3)).comp
            (hum.comp ((measurable_id (α := ℝ)).sub_const ((k : ℝ) * T)))
      exact hF.comp (measurable_id.prodMk (measurable_id.div_const T).nat_floor)
    · -- `det g' = 1` and `X'` is a star state (`R`-invariance of the star domain, §4.6)
      have hs := hstar _ (hmem t ht.1)
      refine ⟨?_, poly_isStarState_conj_pow _ hs.2⟩
      simp only [poly_pw]
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_pow, Matrix.det_pow, poly_det_R, hs.1]
      simp
    · -- `g' = g'X'`
      refine ct_pw_isIntegralCurve hT hgI hgglue n fun i _ t ht ↦ ?_
      rw [poly_pw_of_mem_Ico hT ⟨ht.1.le, ht.2⟩, poly_pw_of_mem_Ico hT ⟨ht.1.le, ht.2⟩]
      exact poly_mul_conj _ _ _ i
    · -- `X' = [P', X']`, with `Z_{u'} = R⁻ⁱ Z_u Rⁱ` (`poly_Rinv_conj_vertex`)
      refine ct_pw_isIntegralCurve hT hXI hXT n fun i _ t ht ↦ ?_
      have hk := poly_floor_eq hT ht.1.le ht.2
      simp only [poly_pw, hu', hk]
      rw [ct_controlP_rot, poly_conj_bracket (poly_Rpow_mul_Rinvpow i)]
    · -- traces, `Λ_R' ⊥ X'`, nontriviality
      obtain ⟨h1, h2, h3, h4⟩ := hcost _ (hmem t ht.1)
      have hc := poly_Rpow_mul_Rinvpow ⌊t / T⌋₊
      simp only [poly_pw]
      refine ⟨by rw [poly_trace_conj hc, h1], by rw [poly_trace_conj hc, h2],
        by rw [poly_traceForm_conj hc, h3], ?_⟩
      have hne : ∀ M : Mat2, M ≠ 0 → R⁻¹ ^ ⌊t / T⌋₊ * M * R ^ ⌊t / T⌋₊ ≠ 0 := fun M hM h' ↦
        hM (by rw [← ct_conj_cancel ⌊t / T⌋₊ M, h']; simp)
      rcases h4 with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (hne _ h))
      · exact Or.inr (Or.inr (hne _ h))
    · -- `Λ₁' = [Λ₁', X']`
      refine ct_pw_isIntegralCurve hT hΛ₁I hΛ₁T n fun i _ t ht ↦ ?_
      rw [poly_pw_of_mem_Ico hT ⟨ht.1.le, ht.2⟩, poly_pw_of_mem_Ico hT ⟨ht.1.le, ht.2⟩,
        poly_conj_bracket (poly_Rpow_mul_Rinvpow i)]
    · -- the `Λ_R` equation, equivariant under the rotation (`J` commutes with `R`)
      refine ct_pw_isIntegralCurve (v0 := fun t ↦ costateRHS lam (Λ₁ t) (ΛR t) (X t) (u t))
        (v := fun t ↦ costateRHS lam (poly_pw R⁻¹ R T Λ₁ t) (poly_pw R⁻¹ R T ΛR t)
          (poly_pw R⁻¹ R T X t) (u' t)) hT hΛRI hΛRT n fun i _ t ht ↦ ?_
      have hk := poly_floor_eq hT ht.1.le ht.2
      simp only [poly_pw, hu', hk]
      exact ct_costateRHS_rot lam i _ _ _ _
    · -- the maximum condition and `H = 0`, almost everywhere
      filter_upwards [ct_ae_pw hT hH n] with t ht htI
      obtain ⟨-, hs, hP, hmax⟩ := ht htI
      have hham : ∀ v, hamiltonian lam (poly_pw R⁻¹ R T Λ₁ t) (poly_pw R⁻¹ R T ΛR t)
          (poly_pw R⁻¹ R T X t) (ct_rot ⌊t / T⌋₊ v) =
            hamiltonian lam (Λ₁ (t - ⌊t / T⌋₊ * T)) (ΛR (t - ⌊t / T⌋₊ * T))
              (X (t - ⌊t / T⌋₊ * T)) v := fun v ↦ ct_hamiltonian_rot lam _ _ _ _ v
      have hu't : u' t = ct_rot ⌊t / T⌋₊ (u (t - ⌊t / T⌋₊ * T)) := rfl
      refine ⟨by rw [hu't, hham]; exact hP, fun v hv ↦ ?_⟩
      have hv' : v = ct_rot ⌊t / T⌋₊ (ct_rot (2 * ⌊t / T⌋₊) v) := by
        rw [ct_rot_rot, ct_rot_mod, show (2 * ⌊t / T⌋₊ + ⌊t / T⌋₊) % 3 = 0 by omega, ct_rot_zero]
      rw [hv', hham, hu't, hham]
      exact hmax _ (ct_rot_mem _ hv)


end SmoothedPolygons
