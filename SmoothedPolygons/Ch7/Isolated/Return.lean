module

public import SmoothedPolygons.Ch7.Isolated.Poincare
public import SmoothedPolygons.Ch7.Isolated.Switching
public import SmoothedPolygons.Ch7.SmoothedPolygon

/-!
# Theorem 7.7.1, step 3: the switching structure of nearby extremals

An extremal near the octagon's crosses the Poincaré section and, restarted there, returns to its
initial point after four applications of the Poincaré map, following the octagon's switching
sequence (eqn:fp). The book omits this step; here it is made precise as follows.

Write `q = (X, Λ₁, Λ_R)`, `χ_ij = irt_chi i j` (`χ₃₁ = irt_chi 2 0`, `χ₃₂ = irt_chi 2 1`,
`χ₂₃ = irt_chi 1 2 = -χ₃₂`), `q_oct = iso_qFix y_oct`, `O(t)` the `e₃`-flow from `q_oct` (the
strong lift of Theorem 7.5.1) and `τ = t_sw`.

* *The `e₃`-flow near the octagon* (`irt_flow_start`, `irt_flow_end`). The closed-form flow is
  jointly continuous (`irt_flow_continuousAt`); the derivative of `χ_ij` along it is
  `irt_G i j` of the current point (`irt_chi_flow_hasDerivAt`). Along `O`, `χ₃₁ > 0` on `[0, τ)`
  and `χ₃₂ > 0` on `(0, τ]` (Lemma 7.5.3), and the zeros are transversal:
  `irt_G 2 0 (O τ) < 0`, `irt_G 2 1 (O 0) > 0` (step 2). By compactness these strict inequalities
  persist, uniformly, for the flow from any `p` near `q_oct` with `χ₃₂(p) ≥ 0`: `χ₃₁` has a unique
  first zero `t_sw(p)` near `τ`, and `χ₃₂ > 0` on `(0, t_sw(p)]`. Near `O(τ) = R⁻¹ q_oct R` the
  flow reaches `χ₃₁ = 0` after a short time.
* *Extremals follow the flow* (`irt_arc`). An extremal starting at `p` uses the control `e₃`
  for as long as the flow from `p` has `χ₃₁ > 0` and `χ₃₂ > 0` (continuation argument with the
  maximum condition, `irt_eq_vertex_of_max`, and uniqueness `iso_arc_eq_vertexFlow`), once it
  is known to use `e₃` on some initial interval. That holds when `χ₃₁(p), χ₃₂(p) > 0`
  (`irt_start_strict`) and, on the switching surface `χ₃₂(p) = 0`, by `irt_start_surface`: a
  maximizing control has `u₁ = 0` near `t = 0` (`irt_eq_zero_of_max`), and since the derivative of
  `χ₃₂` along the vector field of any control on the edge `[e₂, e₃]` is the same positive number
  (`iso_edge_slope`, `iso_chi32_hasDerivAt`), `χ₃₂` becomes positive immediately (a first-order
  expansion of `χ₃₂ = ⟨Λ_R, Z₂⟩/⟨Z₂, X⟩ - ⟨Λ_R, Z₃⟩/⟨Z₃, X⟩` along the integral curve). This
  excludes singular arcs and chattering.
* *Restarts* (`irt_restart`): by `iso_shift` and the `R`-equivariance of the extremal conditions
  (`irt_conj`), an extremal can be restarted at any `s ∈ [0, T)` and conjugated by `R⁻ᵏ`.
* `iso_return`: arc by arc, the extremal from `q₀` is `R⁻ⁱ (e₃-flow from fⁱ q₀) Rⁱ` on
  `[tᵢ, tᵢ₊₁]`; the transversality condition `q(T) = R⁻¹ q₀ R` forces `T = t₄` (otherwise `χ₃₁`
  or `χ₃₂` would vanish inside an arc), and then `f⁴ q₀ = q₀`.
* `iso_section_crossing`: if `χ₃₂(q(0)) = 0` restart at `0`; if `χ₃₂(q(0)) > 0` the extremal has
  just crossed the section, and it crosses it again after three arcs, near `t = 3τ < T` (not near
  `t = T`, as the plan's docstring said: near `T` it crosses the conjugate surface `χ₃₁ = 0`);
  if `χ₃₂(q(0)) < 0` it crosses the section after a short time (the conjugate of the end of an
  `e₃`-arc). The restart point lies on the section: `H = 0` there by `irt_hamiltonian_max`.
-/

@[expose] public section

namespace SmoothedPolygons

open Matrix Set Filter Topology MeasureTheory

/-! ### Switching functions and their derivatives -/

/-- The switching function `χ_ij` at a point of the phase space. -/
noncomputable def irt_chi (i j : Fin 3) (q : iso_PhasePt) : ℝ := switchingFn i j q.2.2 q.1

/-- The derivative of `χ_ij` at `(Λ_R, X)` in the direction `(δΛ_R, δX)`:
`⟨δΛ_R, P_j - P_i⟩ - ⟨Λ_R, P_j⟩⟨P_j, δX⟩ + ⟨Λ_R, P_i⟩⟨P_i, δX⟩` (as `isw_dchi32`). -/
noncomputable def irt_dsw (i j : Fin 3) (ΛR X δΛR δX : Mat2) : ℝ :=
  traceForm δΛR (controlP (vertex j) X - controlP (vertex i) X) -
    traceForm ΛR (controlP (vertex j) X) * traceForm (controlP (vertex j) X) δX +
    traceForm ΛR (controlP (vertex i) X) * traceForm (controlP (vertex i) X) δX

/-- The derivative of `χ_ij` along the `e₃`-vector field at `q`. -/
noncomputable def irt_G (i j : Fin 3) (q : iso_PhasePt) : ℝ :=
  irt_dsw i j q.2.2 q.1 (iso_extremalField (vertex 2) q).2.2 (iso_extremalField (vertex 2) q).1

/-- `⟨Z_{e_k}, X⟩ ≠ 0` for the three vertices: the denominators of the switching functions. -/
def irt_Den (q : iso_PhasePt) : Prop := ∀ k : Fin 3, traceForm (controlMatrix (vertex k)) q.1 ≠ 0

lemma irt_chi_antisymm (i j : Fin 3) (q : iso_PhasePt) : irt_chi i j q = -irt_chi j i q := by
  simp only [irt_chi, switchingFn, traceForm, Matrix.mul_sub, Matrix.trace_sub, neg_sub]

lemma irt_chi_hasDerivAt {i j : Fin 3} {f : ℝ → iso_PhasePt} {f' : iso_PhasePt} {t : ℝ}
    (hX : HasDerivAtEntrywise (fun s ↦ (f s).1) f'.1 t)
    (hR : HasDerivAtEntrywise (fun s ↦ (f s).2.2) f'.2.2 t) (hD : irt_Den (f t)) :
    HasDerivAt (fun s ↦ irt_chi i j (f s)) (irt_dsw i j (f t).2.2 (f t).1 f'.2.2 f'.1) t := by
  have hL : ∀ (Z : Mat2), HasDerivAt (fun s ↦ traceForm (f s).2.2 Z) (traceForm f'.2.2 Z) t := by
    intro Z
    simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    exact (((hR 0 0).mul_const _).add ((hR 0 1).mul_const _)).add
      (((hR 1 0).mul_const _).add ((hR 1 1).mul_const _))
  have hRt : ∀ (Z : Mat2), HasDerivAt (fun s ↦ traceForm Z (f s).1) (traceForm Z f'.1) t := by
    intro Z
    simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    exact (((hX 0 0).const_mul _).add ((hX 1 0).const_mul _)).add
      (((hX 0 1).const_mul _).add ((hX 1 1).const_mul _))
  have hq : ∀ k : Fin 3, HasDerivAt (fun s ↦ traceForm (f s).2.2 (controlMatrix (vertex k)) /
      traceForm (controlMatrix (vertex k)) (f s).1)
      ((traceForm f'.2.2 (controlMatrix (vertex k)) * traceForm (controlMatrix (vertex k)) (f t).1 -
        traceForm (f t).2.2 (controlMatrix (vertex k)) * traceForm (controlMatrix (vertex k)) f'.1)
        / traceForm (controlMatrix (vertex k)) (f t).1 ^ 2) t :=
    fun k ↦ (hL _).div (hRt _) (hD k)
  have e : (fun s ↦ irt_chi i j (f s)) = fun s ↦
      traceForm (f s).2.2 (controlMatrix (vertex j)) /
          traceForm (controlMatrix (vertex j)) (f s).1 -
        traceForm (f s).2.2 (controlMatrix (vertex i)) /
          traceForm (controlMatrix (vertex i)) (f s).1 := by
    funext s; exact str_switchingFn_eq i j _ _
  rw [e]
  refine ((hq j).sub (hq i)).congr_deriv ?_
  have hi := hD i
  have hj := hD j
  simp only [irt_dsw, controlP, traceForm, Matrix.mul_sub, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul] at hi hj ⊢
  field_simp
  ring

lemma irt_chi_continuousAt (i j : Fin 3) {q : iso_PhasePt} (hD : irt_Den q) :
    ContinuousAt (irt_chi i j) q := by
  have e : irt_chi i j = fun q ↦
      traceForm q.2.2 (controlMatrix (vertex j)) / traceForm (controlMatrix (vertex j)) q.1 -
        traceForm q.2.2 (controlMatrix (vertex i)) / traceForm (controlMatrix (vertex i)) q.1 := by
    funext q; exact str_switchingFn_eq i j _ _
  rw [e]
  have hi := hD i
  have hj := hD j
  unfold traceForm at *
  fun_prop (disch := assumption)

lemma irt_G_continuousAt (i j : Fin 3) {q : iso_PhasePt} (hD : irt_Den q) :
    ContinuousAt (irt_G i j) q := by
  have hi := hD i
  have hj := hD j
  have h2 := hD 2
  unfold irt_G irt_dsw iso_extremalField costateRHS controlP traceForm at *
  fun_prop (disch := assumption)

lemma irt_Den_of_star {q : iso_PhasePt} (h : IsStarState q.1) : irt_Den q :=
  fun k ↦ (poly_traceForm_neg (poly_vertex_mem k) h).ne

lemma irt_isOpen_Den : IsOpen {q : iso_PhasePt | irt_Den q} := by
  have e : {q : iso_PhasePt | irt_Den q} =
      ⋂ k : Fin 3, {q | traceForm (controlMatrix (vertex k)) q.1 ≠ 0} := by
    ext q; simp [irt_Den]
  rw [e]
  refine isOpen_iInter_of_finite fun k ↦ isOpen_ne_fun ?_ continuous_const
  unfold traceForm; fun_prop

/-! ### The vertex flow and the Poincaré map preserve `𝔰𝔩₂(ℝ)³` -/

/-- The trace of a curve with an entrywise derivative. -/
lemma irt_trace_hasDerivAt {f : ℝ → Mat2} {f' : Mat2} {t : ℝ} (h : HasDerivAtEntrywise f f' t) :
    HasDerivAt (fun s ↦ (f s).trace) f'.trace t := by
  simp only [Matrix.trace_fin_two]
  exact (h 0 0).add (h 1 1)

/-- A curve whose derivative is everywhere traceless has constant trace. -/
lemma irt_trace_const {f f' : ℝ → Mat2} (hf : ∀ t, HasDerivAtEntrywise f (f' t) t)
    (h0 : ∀ t, (f' t).trace = 0) (t : ℝ) : (f t).trace = (f 0).trace :=
  is_const_of_deriv_eq_zero (fun s ↦ (irt_trace_hasDerivAt (hf s)).differentiableAt)
    (fun s ↦ by rw [(irt_trace_hasDerivAt (hf s)).deriv, h0]) t 0

lemma irt_trace_bracket (A B : Mat2) : (A * B - B * A).trace = 0 := by
  rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

/-- The vertex flow preserves `𝔰𝔩₂(ℝ)³`. -/
lemma irt_vertexFlow_traceless (m : Fin 3) {q : iso_PhasePt} (h1 : q.1.trace = 0)
    (h2 : q.2.1.trace = 0) (h3 : q.2.2.trace = 0) (t : ℝ) :
    (iso_vertexFlow m q t).1.trace = 0 ∧ (iso_vertexFlow m q t).2.1.trace = 0 ∧
      (iso_vertexFlow m q t).2.2.trace = 0 := by
  have hq := ivf_vertexFlow_zero m q
  have hX := irt_trace_const (f := fun s ↦ (iso_vertexFlow m q s).1)
    (fun s ↦ ivf_vfX_hasDerivAt m q s) (fun s ↦ irt_trace_bracket _ _) t
  have hL := irt_trace_const (f := fun s ↦ (iso_vertexFlow m q s).2.1)
    (fun s ↦ ivf_vfΛ₁_hasDerivAt m q s) (fun s ↦ irt_trace_bracket _ _) t
  have hR := irt_trace_const (f := fun s ↦ (iso_vertexFlow m q s).2.2)
    (fun s ↦ ivf_vfΛR_hasDerivAt m q s) (fun s ↦ by
      rw [costateRHS, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, irt_trace_bracket,
        irt_trace_bracket, irt_trace_bracket, smul_zero, sub_zero, add_zero]) t
  simp only [hq] at hX hL hR
  exact ⟨hX.trans h1, hL.trans h2, hR.trans h3⟩

lemma irt_poincareMap_traceless {q : iso_PhasePt} (h1 : q.1.trace = 0) (h2 : q.2.1.trace = 0)
    (h3 : q.2.2.trace = 0) :
    (iso_poincareMap q).1.trace = 0 ∧ (iso_poincareMap q).2.1.trace = 0 ∧
      (iso_poincareMap q).2.2.trace = 0 := by
  obtain ⟨k1, k2, k3⟩ := irt_vertexFlow_traceless 2 h1 h2 h3 (iso_poincareTime q)
  simp only [iso_poincareMap, iso_adR]
  refine ⟨?_, ?_, ?_⟩ <;> rw [poly_trace_conj poly_inv_mul_R] <;> assumption

/-! ### Conjugation by powers of `R` -/

lemma irt_adRinvPow_add (i k : ℕ) (q : iso_PhasePt) :
    iso_adRinvPow i (iso_adRinvPow k q) = iso_adRinvPow (i + k) q := by
  have h1 : R⁻¹ ^ (i + k) = R⁻¹ ^ i * R⁻¹ ^ k := pow_add _ _ _
  have h2 : R ^ (i + k) = R ^ k * R ^ i := by rw [add_comm, pow_add]
  simp only [iso_adRinvPow, h1, h2, Matrix.mul_assoc]

lemma irt_adRinvPow_three_mul (m : ℕ) (q : iso_PhasePt) : iso_adRinvPow (3 * m) q = q := by
  have h1 : R⁻¹ ^ (3 * m) = ((-1 : ℝ) ^ m) • (1 : Mat2) := by
    rw [pow_mul, poly_Rinv_pow_three, ← neg_one_smul ℝ (1 : Mat2), smul_pow, one_pow]
  have h2 : R ^ (3 * m) = ((-1 : ℝ) ^ m) • (1 : Mat2) := by
    rw [pow_mul, poly_R_pow_three, ← neg_one_smul ℝ (1 : Mat2), smul_pow, one_pow]
  have h3 : ∀ A : Mat2, ((-1 : ℝ) ^ m) • (1 : Mat2) * A * (((-1 : ℝ) ^ m) • (1 : Mat2)) = A := by
    intro A
    rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, ← mul_pow,
      neg_one_mul, neg_neg, one_pow, one_smul]
  obtain ⟨a, b, c⟩ := q
  simp only [iso_adRinvPow, h1, h2, h3]

lemma irt_adRinvPow_injective (k : ℕ) : Function.Injective (iso_adRinvPow k) := by
  intro a b hab
  have := congrArg (iso_adRinvPow (2 * k)) hab
  rwa [irt_adRinvPow_add, irt_adRinvPow_add, show 2 * k + k = 3 * k by ring,
    irt_adRinvPow_three_mul, irt_adRinvPow_three_mul] at this

lemma irt_adRinvPow_mod (k : ℕ) (q : iso_PhasePt) :
    iso_adRinvPow k q = iso_adRinvPow (k % 3) q := by
  conv_lhs => rw [← Nat.mod_add_div k 3]
  rw [← irt_adRinvPow_add, irt_adRinvPow_three_mul]

lemma irt_adRinvPow_zero (q : iso_PhasePt) : iso_adRinvPow 0 q = q := by
  simp [iso_adRinvPow]

lemma irt_adRinvPow_one_adR (q : iso_PhasePt) : iso_adRinvPow 1 (iso_adR q) = q := by
  have h : ∀ A : Mat2, R⁻¹ * (R * A * R⁻¹) * R = A := fun A ↦ by
    rw [show R⁻¹ * (R * A * R⁻¹) * R = (R⁻¹ * R) * A * (R⁻¹ * R) by simp only [Matrix.mul_assoc],
      poly_inv_mul_R, Matrix.one_mul, Matrix.mul_one]
  obtain ⟨a, b, c⟩ := q
  simp only [iso_adRinvPow, iso_adR, pow_one, h]

lemma irt_continuous_adRinvPow (k : ℕ) : Continuous (iso_adRinvPow k) := by
  unfold iso_adRinvPow; fun_prop

/-- `χ_ij` is invariant under the simultaneous relabelling `i ↦ i + k`, `j ↦ j + k` and the
conjugation by `R⁻ᵏ`. -/
lemma irt_chi_conj (k : ℕ) (i j : Fin 3) (q : iso_PhasePt) :
    irt_chi (i + ⟨k % 3, Nat.mod_lt _ (by norm_num)⟩) (j + ⟨k % 3, Nat.mod_lt _ (by norm_num)⟩)
      (iso_adRinvPow k q) = irt_chi i j q := by
  have hP : ∀ m : Fin 3, controlP (vertex (m + ⟨k % 3, Nat.mod_lt _ (by norm_num)⟩))
      (R⁻¹ ^ k * q.1 * R ^ k) = R⁻¹ ^ k * controlP (vertex m) q.1 * R ^ k := by
    intro m
    have hm : (⟨(m.val + k) % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3) =
        m + ⟨k % 3, Nat.mod_lt _ (by norm_num)⟩ := by
      ext; simp only [Fin.val_add]; omega
    rw [poly_controlP_conj (poly_Rpow_mul_Rinvpow k) (poly_conj_pow_vertex k m), hm]
  simp only [irt_chi, switchingFn, iso_adRinvPow, hP, ← poly_conj_sub,
    poly_traceForm_conj (poly_Rpow_mul_Rinvpow k)]

/-- Integral curves are compatible with multiplication by constant matrices. -/
lemma irt_isIntegralCurve_conj {f v : ℝ → Mat2} {T : ℝ} (hI : IsIntegralCurve f v T)
    (C D : Mat2) : IsIntegralCurve (fun t ↦ C * f t * D) (fun t ↦ C * v t * D) T := by
  intro i j
  refine ⟨ivf_intervalIntegrable_conj (fun k l ↦ (hI k l).1) C D i j, fun t ht ↦ ?_⟩
  have hv : ∀ k l, IntervalIntegrable (fun s ↦ v s k l) volume 0 t := fun k l ↦
    (hI k l).1.mono_set (by
      rw [uIcc_of_le ht.1, uIcc_of_le (ht.1.trans ht.2)]
      exact Icc_subset_Icc_right ht.2)
  rw [ivf_integral_conj hv C D i j]
  have hf : f t = f 0 + Matrix.of (fun k l ↦ ∫ s in (0 : ℝ)..t, v s k l) := by
    ext k l; exact (hI k l).2 t ht
  change (C * f t * D) i j = (C * f 0 * D) i j + _
  rw [hf, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]

/-- The conditions of a Pontryagin extremal are invariant under conjugation by `R⁻ᵏ`, with the
controls relabelled by `iso_rotControl k`. -/
lemma irt_conj {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (h : IsPontryaginExtremal T u g X Λ₁ ΛR lam) (k : ℕ) :
    IsPontryaginExtremal T (fun t ↦ iso_rotControl k (u t)) (fun t ↦ R⁻¹ ^ k * g t * R ^ k)
      (fun t ↦ R⁻¹ ^ k * X t * R ^ k) (fun t ↦ R⁻¹ ^ k * Λ₁ t * R ^ k)
      (fun t ↦ R⁻¹ ^ k * ΛR t * R ^ k) lam := by
  obtain ⟨⟨hT, hum, husim, hst, hgI, hXI⟩, hg0, hgT, hXT, h1T, hRT, hlam, hpt, hI1, hIR, hmax⟩ := h
  have hC : R ^ k * R⁻¹ ^ k = 1 := poly_Rpow_mul_Rinvpow k
  have hZ : ∀ w, R⁻¹ ^ k * controlMatrix w * R ^ k = controlMatrix (iso_rotControl k w) :=
    ivf_conj_pow_controlMatrix k
  have hJ : R⁻¹ ^ k * J * R ^ k = J := poly_conj_pow_J k
  have hcR : ∀ A : Mat2, R⁻¹ ^ k * (R⁻¹ * A * R) * R ^ k = R⁻¹ * (R⁻¹ ^ k * A * R ^ k) * R := by
    intro A
    have h1 : R⁻¹ ^ k * R⁻¹ = R⁻¹ * R⁻¹ ^ k := (Commute.self_pow R⁻¹ k).eq.symm
    have h2 : R * R ^ k = R ^ k * R := (Commute.self_pow R k).eq
    simp only [← Matrix.mul_assoc, h1]
    simp only [Matrix.mul_assoc, h2]
  refine ⟨⟨hT, ?_, fun t ht ↦ ivf_rotControl_mem (husim t ht), fun t ht ↦ ⟨?_, ?_⟩, ?_, ?_⟩,
    ?_, ?_, ?_, ?_, ?_, hlam, fun t ht ↦ ?_, ?_, ?_, ?_⟩
  · refine measurable_pi_iff.2 fun i ↦ ?_
    exact (measurable_pi_apply _).comp hum
  · rw [poly_det_conj hC, (hst t ht).1]
  · exact poly_isStarState_conj_pow k (hst t ht).2
  · refine poly_isIntegralCurve_congr (irt_isIntegralCurve_conj hgI _ _) hT.le fun t _ ↦ ?_
    exact poly_conj_mul hC _ _
  · refine poly_isIntegralCurve_congr (irt_isIntegralCurve_conj hXI _ _) hT.le fun t _ ↦ ?_
    simp only
    rw [poly_conj_bracket hC, poly_controlP_conj hC (hZ (u t))]
  · simp only [hg0, Matrix.mul_one, poly_Rinvpow_mul_Rpow]
  · simp only [hgT]
    rw [Matrix.mul_assoc, (Commute.self_pow R k).eq, ← Matrix.mul_assoc, poly_Rinvpow_mul_Rpow,
      Matrix.one_mul]
  · simp only [hXT, hcR]
  · simp only [h1T, hcR]
  · simp only [hRT, hcR]
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

/-- Restarting an extremal at `s ∈ [0, T)` and conjugating it by `R⁻ᵏ`. -/
lemma irt_restart {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    (h : IsPontryaginExtremal T u g X Λ₁ ΛR (-1)) {s : ℝ} (hs : s ∈ Ico 0 T) (k : ℕ) :
    ∃ (u' : ℝ → Fin 3 → ℝ) (g' X' Λ₁' ΛR' : ℝ → Mat2),
      IsPontryaginExtremal T u' g' X' Λ₁' ΛR' (-1) ∧
      ∀ t ∈ Icc 0 (T - s),
        (X' t, Λ₁' t, ΛR' t) = iso_adRinvPow k (X (s + t), Λ₁ (s + t), ΛR (s + t)) := by
  have hT : 0 < T := h.1.1
  obtain ⟨-, -, -, hXT, h1T, hRT, -⟩ := id h
  refine ⟨_, _, _, _, _, irt_conj (iso_shift h hs.1) k, fun t ht ↦ ?_⟩
  have hmem : s + t ∈ Icc (((0 : ℕ) : ℝ) * T) ((((0 : ℕ) : ℝ) + 1) * T) := by
    simp only [Nat.cast_zero, zero_mul, zero_add, one_mul]
    exact ⟨by linarith [hs.1, ht.1], by linarith [ht.2]⟩
  have e : ∀ F : ℝ → Mat2, F T = R⁻¹ * F 0 * R → poly_pw R⁻¹ R T F (s + t) = F (s + t) := by
    intro F hF
    rw [poly_pw_of_mem_Icc hT hF hmem]
    simp
  simp only [iso_adRinvPow, e X hXT, e Λ₁ h1T, e ΛR hRT]

/-! ### The maximum condition -/

/-- A maximizer puts no weight on a vertex that is strictly beaten by a maximal vertex. -/
lemma irt_eq_zero_of_max {lam : ℝ} {Λ₁ ΛR X : Mat2} (hX : IsStarState X) {m j : Fin 3}
    (hm : ∀ i, hamiltonian lam Λ₁ ΛR X (vertex i) ≤ hamiltonian lam Λ₁ ΛR X (vertex m))
    (hj : hamiltonian lam Λ₁ ΛR X (vertex j) < hamiltonian lam Λ₁ ΛR X (vertex m))
    {w : Fin 3 → ℝ} (hw : w ∈ controlSimplex)
    (hmax : hamiltonian lam Λ₁ ΛR X (vertex m) ≤ hamiltonian lam Λ₁ ΛR X w) : w j = 0 := by
  set d : Fin 3 → ℝ := fun j ↦ traceForm X (controlMatrix (vertex j)) with hd
  set n : Fin 3 → ℝ := fun j ↦ traceForm ΛR (controlMatrix (vertex j)) with hn
  have hdneg : ∀ j, d j < 0 := fun j ↦ by
    simp only [hd]; rw [poly_traceForm_comm]; exact poly_traceForm_neg (poly_vertex_mem j) hX
  have hD : traceForm X (controlMatrix w) < 0 := by
    rw [poly_traceForm_comm]; exact poly_traceForm_neg hw hX
  have hDw : traceForm X (controlMatrix w) = w 0 * d 0 + w 1 * d 1 + w 2 * d 2 := by
    rw [poly_controlMatrix_eq w]
    simp only [poly_traceForm_add_right, poly_traceForm_smul_right, hd]
  have hNw : traceForm ΛR (controlMatrix w) = w 0 * n 0 + w 1 * n 1 + w 2 * n 2 := by
    rw [poly_controlMatrix_eq w]
    simp only [poly_traceForm_add_right, poly_traceForm_smul_right, hn]
  set r := n m / d m with hr
  -- `n_i ≤ r d_i`, strictly for `i = j`
  have hle : ∀ i, n i - r * d i ≤ 0 := by
    intro i
    have h := hm i
    simp only [hamiltonian] at h
    have h' : r ≤ n i / d i := by simp only [hr, hn, hd]; linarith
    have := (le_div_iff_of_neg (hdneg i)).1 h'
    linarith
  have hjlt : n j - r * d j < 0 := by
    have h := hj
    simp only [hamiltonian] at h
    have h' : r < n j / d j := by simp only [hr, hn, hd]; linarith
    have := (lt_div_iff_of_neg (hdneg j)).1 h'
    linarith
  have hsum : 0 ≤ w 0 * (n 0 - r * d 0) + w 1 * (n 1 - r * d 1) + w 2 * (n 2 - r * d 2) := by
    simp only [hamiltonian] at hmax
    have h' : traceForm ΛR (controlMatrix w) / traceForm X (controlMatrix w) ≤ r := by
      rw [hr]; simp only [hn, hd]; linarith
    rw [div_le_iff_of_neg hD, hDw, hNw] at h'
    linarith
  have hw0 : ∀ i, 0 ≤ w i := fun i ↦ (hw.1 i).1
  have hterm : ∀ i, w i * (n i - r * d i) ≤ 0 := fun i ↦
    mul_nonpos_of_nonneg_of_nonpos (hw0 i) (hle i)
  have hsum0 : ∑ i, w i * (n i - r * d i) = 0 :=
    le_antisymm (Finset.sum_nonpos fun i _ ↦ hterm i) (by rw [Fin.sum_univ_three]; exact hsum)
  have h0 : w j * (n j - r * d j) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonpos fun i _ ↦ hterm i).1 hsum0 j (Finset.mem_univ j)
  rcases mul_eq_zero.mp h0 with h | h
  · exact h
  · exact absurd h hjlt.ne

/-- If the vertex `e_m` strictly beats the other vertices, it is the only maximizer of the
Hamiltonian on `U_T` (the Hamiltonian is a convex combination of its vertex values with weights
`u_j ⟨X, Z_{e_j}⟩/⟨X, Z_u⟩`, as in `poly_hamiltonian_le_of_vertices`). -/
lemma irt_eq_vertex_of_max {lam : ℝ} {Λ₁ ΛR X : Mat2} (hX : IsStarState X) {m : Fin 3}
    (hlt : ∀ j ≠ m, hamiltonian lam Λ₁ ΛR X (vertex j) < hamiltonian lam Λ₁ ΛR X (vertex m))
    {w : Fin 3 → ℝ} (hw : w ∈ controlSimplex)
    (hmax : hamiltonian lam Λ₁ ΛR X (vertex m) ≤ hamiltonian lam Λ₁ ΛR X w) : w = vertex m := by
  have hzero : ∀ j ≠ m, w j = 0 := fun j hj ↦
    irt_eq_zero_of_max hX (fun i ↦ by
      by_cases him : i = m
      · rw [him]
      · exact (hlt i him).le) (hlt j hj) hw hmax
  have hs : ∑ i, w i = 1 := by rw [Fin.sum_univ_three]; exact hw.2
  rw [Finset.sum_eq_single m (fun i _ him ↦ hzero i him) (by simp)] at hs
  funext i
  by_cases him : i = m
  · subst him; rw [hs, vertex, Pi.single_eq_same]
  · rw [hzero i him, vertex, Pi.single_eq_of_ne him]

/-- The state and costates of an extremal are continuous on `[0, T]`. -/
lemma irt_q_continuousOn {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (h : IsPontryaginExtremal T u g X Λ₁ ΛR lam) :
    ContinuousOn (fun t ↦ (X t, Λ₁ t, ΛR t)) (Icc 0 T) := by
  obtain ⟨⟨-, -, -, -, -, hXI⟩, -, -, -, -, -, -, -, hI1, hIR, -⟩ := h
  exact (Matrix.continuousOn_of_eq_add_integral hXI).prodMk
    ((Matrix.continuousOn_of_eq_add_integral hI1).prodMk
      (Matrix.continuousOn_of_eq_add_integral hIR))

/-- The Hamiltonian at a vertex is continuous at points whose `X` is a star state. -/
lemma irt_hamiltonian_continuousAt (m : Fin 3) {q : iso_PhasePt} (hD : irt_Den q) :
    ContinuousAt (fun q : iso_PhasePt ↦ hamiltonian (-1) q.2.1 q.2.2 q.1 (vertex m)) q := by
  have hm : traceForm q.1 (controlMatrix (vertex m)) ≠ 0 := by
    rw [poly_traceForm_comm]; exact hD m
  unfold hamiltonian traceForm at *
  fun_prop (disch := assumption)

/-- Near a time where `χ₃₁ > 0` and `χ₃₂ > 0`, a normalized extremal uses the control `e₃`. -/
lemma irt_vertex_near {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    (h : IsPontryaginExtremal T u g X Λ₁ ΛR (-1)) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc 0 T)
    (h31 : 0 < irt_chi 2 0 (X t₀, Λ₁ t₀, ΛR t₀)) (h32 : 0 < irt_chi 2 1 (X t₀, Λ₁ t₀, ΛR t₀)) :
    ∃ ε > 0, ∀ᵐ t, t ∈ Ioo t₀ (t₀ + ε) → t ∈ Ioo 0 T → u t = vertex 2 := by
  have hc := irt_q_continuousOn h t₀ ht₀
  have hst := h.1.2.2.2.1
  have hD : irt_Den (X t₀, Λ₁ t₀, ΛR t₀) := irt_Den_of_star (hst t₀ ht₀).2
  have h1 := (ContinuousAt.comp_continuousWithinAt (g := irt_chi 2 0)
    (f := fun t ↦ (X t, Λ₁ t, ΛR t)) (irt_chi_continuousAt 2 0 hD) hc).eventually
    (lt_mem_nhds h31)
  have h2 := (ContinuousAt.comp_continuousWithinAt (g := irt_chi 2 1)
    (f := fun t ↦ (X t, Λ₁ t, ΛR t)) (irt_chi_continuousAt 2 1 hD) hc).eventually
    (lt_mem_nhds h32)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 (h1.and h2)
  refine ⟨ε, hε, ?_⟩
  filter_upwards [h.2.2.2.2.2.2.2.2.2.2] with t ht htε htT
  obtain ⟨-, hle⟩ := ht htT
  have htI : t ∈ Icc 0 T := Ioo_subset_Icc_self htT
  obtain ⟨p31, p32⟩ : 0 < irt_chi 2 0 (X t, Λ₁ t, ΛR t) ∧ 0 < irt_chi 2 1 (X t, Λ₁ t, ΛR t) :=
    hball ⟨by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [htε.1, htε.2],
      htI⟩
  refine irt_eq_vertex_of_max (hst t htI).2 (fun j hj ↦ ?_) (h.1.2.2.1 t htI)
    (hle _ (poly_vertex_mem 2))
  have hsub := poly_hamiltonian_sub (-1) (Λ₁ t) (ΛR t) (X t) 2 j
  have hlt : j.val ≠ 2 := fun h' ↦ hj (Fin.ext h')
  have hj' := j.isLt
  rcases (by omega : j.val = 0 ∨ j.val = 1) with h0 | h0
  · rw [show j = 0 from Fin.ext h0] at hsub ⊢
    have : 0 < switchingFn 2 0 (ΛR t) (X t) := p31
    linarith
  · rw [show j = 1 from Fin.ext h0] at hsub ⊢
    have : 0 < switchingFn 2 1 (ΛR t) (X t) := p32
    linarith

/-- Along a normalized extremal the maximum of the Hamiltonian over `U_T` vanishes at every time
(not only almost everywhere): the vertex values are continuous in time. -/
lemma irt_hamiltonian_max {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    (h : IsPontryaginExtremal T u g X Λ₁ ΛR (-1)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    (∀ m : Fin 3, hamiltonian (-1) (Λ₁ t) (ΛR t) (X t) (vertex m) ≤ 0) ∧
      ∃ m : Fin 3, hamiltonian (-1) (Λ₁ t) (ΛR t) (X t) (vertex m) = 0 := by
  have hT : 0 < T := h.1.1
  have hst := h.1.2.2.2.1
  set Hm : Fin 3 → ℝ → ℝ := fun m t ↦ hamiltonian (-1) (Λ₁ t) (ΛR t) (X t) (vertex m) with hHm
  have hcont : ∀ m, ContinuousOn (Hm m) (Icc 0 T) := fun m t ht ↦
    ContinuousAt.comp_continuousWithinAt
      (g := fun q : iso_PhasePt ↦ hamiltonian (-1) q.2.1 q.2.2 q.1 (vertex m))
      (f := fun t ↦ (X t, Λ₁ t, ΛR t))
      (irt_hamiltonian_continuousAt m (irt_Den_of_star (hst t ht).2)) (irt_q_continuousOn h t ht)
  set F : ℝ → ℝ := fun t ↦ max (Hm 0 t) (max (Hm 1 t) (Hm 2 t)) with hF
  have hFc : ContinuousOn F (Icc 0 T) :=
    ContinuousOn.sup (hcont 0) (ContinuousOn.sup (hcont 1) (hcont 2))
  have hae : F =ᵐ[volume.restrict (Icc 0 T)] fun _ ↦ (0 : ℝ) := by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Icc]
    filter_upwards [h.2.2.2.2.2.2.2.2.2.2, (countable_singleton (0 : ℝ)).ae_notMem volume,
      (countable_singleton T).ae_notMem volume] with t ht h0 hT' htI
    have htI' : t ∈ Ioo 0 T :=
      ⟨lt_of_le_of_ne htI.1 (Ne.symm h0), lt_of_le_of_ne htI.2 hT'⟩
    obtain ⟨hH, hle⟩ := ht htI'
    have hle0 : ∀ m, Hm m t ≤ 0 := fun m ↦ (hle _ (poly_vertex_mem m)).trans hH.le
    have hge : 0 ≤ F t := by
      have := poly_hamiltonian_le_of_vertices (-1) (Λ₁ t) (ΛR t) (X t) (hst t htI).2 (F t)
        (fun m ↦ by
          fin_cases m
          · exact le_max_left _ _
          · exact (le_max_left _ _).trans (le_max_right _ _)
          · exact (le_max_right _ _).trans (le_max_right _ _)) (u t) (h.1.2.2.1 t htI)
      rw [hH] at this
      exact this
    exact le_antisymm (max_le (hle0 0) (max_le (hle0 1) (hle0 2))) hge
  have hFt : F t = 0 := Measure.eqOn_Icc_of_ae_eq volume hT.ne hae hFc continuousOn_const ht
  refine ⟨fun m ↦ ?_, ?_⟩
  · have : Hm m t ≤ F t := by
      fin_cases m
      · exact le_max_left _ _
      · exact (le_max_left _ _).trans (le_max_right _ _)
      · exact (le_max_right _ _).trans (le_max_right _ _)
    rw [hFt] at this
    exact this
  · rcases max_choice (Hm 0 t) (max (Hm 1 t) (Hm 2 t)) with h0 | h0
    · exact ⟨0, by rw [← hFt, hF]; exact h0.symm⟩
    · rcases max_choice (Hm 1 t) (Hm 2 t) with h1 | h1
      · exact ⟨1, by rw [← hFt, hF]; simp only; rw [h0, h1]⟩
      · exact ⟨2, by rw [← hFt, hF]; simp only; rw [h0, h1]⟩

/-- A point of a normalized extremal on the switching surface `χ₂₃ = 0` where `χ₃₁ > 0` lies on
the Poincaré section. -/
lemma irt_isSectionPt {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    (h : IsPontryaginExtremal T u g X Λ₁ ΛR (-1)) {t : ℝ} (ht : t ∈ Icc 0 T)
    (h23 : irt_chi 1 2 (X t, Λ₁ t, ΛR t) = 0) (h31 : 0 < irt_chi 2 0 (X t, Λ₁ t, ΛR t)) :
    iso_IsSectionPt (X t, Λ₁ t, ΛR t) := by
  obtain ⟨hle, m, hm⟩ := irt_hamiltonian_max h ht
  obtain ⟨⟨-, -, -, hst, -, -⟩, -, -, -, -, -, -, hpt, -⟩ := h
  have h21 := poly_hamiltonian_sub (-1) (Λ₁ t) (ΛR t) (X t) 1 2
  have h31' := poly_hamiltonian_sub (-1) (Λ₁ t) (ΛR t) (X t) 2 0
  have e23 : switchingFn 1 2 (ΛR t) (X t) = 0 := h23
  have e31 : 0 < switchingFn 2 0 (ΛR t) (X t) := h31
  have hH3 : hamiltonian (-1) (Λ₁ t) (ΛR t) (X t) (vertex 2) = 0 := by
    have hm' := m.isLt
    rcases (by omega : m.val = 0 ∨ m.val = 1 ∨ m.val = 2) with h0 | h0 | h0
    · rw [show m = 0 from Fin.ext h0] at hm
      linarith [hle 2]
    · rw [show m = 1 from Fin.ext h0] at hm
      linarith
    · rwa [show m = 2 from Fin.ext h0] at hm
  refine ⟨(hst t ht).2.1, (hpt t ht).1, (hpt t ht).2.1, (hst t ht).2.2.1, ?_, hH3, h23⟩
  rw [poly_traceForm_comm]
  exact (hpt t ht).2.2.1

/-! ### Extremals follow the `e₃`-flow -/

/-- **Continuation.** An extremal that uses the control `e₃` on an initial interval follows the
`e₃`-flow from its initial point for as long as the flow has `χ₃₁ > 0` and `χ₃₂ > 0`. -/
theorem irt_arc {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    (h : IsPontryaginExtremal T u g X Λ₁ ΛR (-1)) {τp : ℝ} (hτp : 0 < τp)
    (h31 : ∀ t ∈ Ico 0 τp, 0 < irt_chi 2 0 (iso_vertexFlow 2 (X 0, Λ₁ 0, ΛR 0) t))
    (h32 : ∀ t ∈ Ioc 0 τp, 0 < irt_chi 2 1 (iso_vertexFlow 2 (X 0, Λ₁ 0, ΛR 0) t))
    (hstart : ∃ η > 0, ∀ᵐ t, t ∈ Ioo 0 η → u t = vertex 2) :
    ∀ t ∈ Icc 0 (min T τp), (X t, Λ₁ t, ΛR t) = iso_vertexFlow 2 (X 0, Λ₁ 0, ΛR 0) t := by
  have hT : 0 < T := h.1.1
  set b := min T τp with hb
  have hb0 : 0 < b := lt_min hT hτp
  set P : ℝ → Prop := fun s ↦ ∀ᵐ t, t ∈ Ioo 0 s → u t = vertex 2 with hP
  set S := {s ∈ Icc 0 b | P s} with hS
  obtain ⟨η, hη, hηP⟩ := hstart
  have hηS : min η b ∈ S := ⟨⟨(lt_min hη hb0).le, min_le_right _ _⟩, by
    filter_upwards [hηP] with t ht htI using ht ⟨htI.1, htI.2.trans_le (min_le_left _ _)⟩⟩
  have hSne : S.Nonempty := ⟨_, hηS⟩
  have hSbdd : BddAbove S := ⟨b, fun s hs ↦ hs.1.2⟩
  set c := sSup S with hc
  have hcb : c ≤ b := csSup_le hSne fun s hs ↦ hs.1.2
  have hc0 : 0 < c := (lt_min hη hb0).trans_le (le_csSup hSbdd hηS)
  -- `P c`
  have hPc : P c := by
    have hseq : ∀ n : ℕ, ∃ s ∈ S, c - 1 / ((n : ℝ) + 1) < s := by
      intro n
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      exact exists_lt_of_lt_csSup hSne (by linarith)
    choose s hsS hs using hseq
    have hall : ∀ᵐ t, ∀ n, t ∈ Ioo 0 (s n) → u t = vertex 2 := ae_all_iff.2 fun n ↦ (hsS n).2
    filter_upwards [hall] with t ht htI
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 htI.2)
    exact ht n ⟨htI.1, by linarith [hs n]⟩
  -- the extremal is the flow on `[0, c]`
  have hflow : ∀ s, 0 < s → s ≤ b → P s →
      ∀ t ∈ Icc 0 s, (X t, Λ₁ t, ΛR t) = iso_vertexFlow 2 (X 0, Λ₁ 0, ΛR 0) t := by
    intro s hs hsb hPs t ht
    have := iso_arc_eq_vertexFlow h le_rfl hs.le (hsb.trans (min_le_left _ _)) 2 hPs t ht
    rwa [sub_zero] at this
  have hcb' : c = b := by
    by_contra hne
    have hlt : c < b := lt_of_le_of_ne hcb hne
    have hcq := hflow c hc0 hcb hPc c ⟨hc0.le, le_rfl⟩
    have hcT : c ∈ Icc 0 T := ⟨hc0.le, hcb.trans (min_le_left _ _)⟩
    have hcτ : c < τp := hlt.trans_le (min_le_right _ _)
    obtain ⟨ε, hε, hεP⟩ := irt_vertex_near h hcT (by rw [hcq]; exact h31 c ⟨hc0.le, hcτ⟩)
      (by rw [hcq]; exact h32 c ⟨hc0, hcτ.le⟩)
    have hmem : min (c + ε) b ∈ S := by
      refine ⟨⟨by positivity, min_le_right _ _⟩, ?_⟩
      filter_upwards [hPc, hεP, (countable_singleton c).ae_notMem volume] with t h1 h2 h3 htI
      rcases lt_trichotomy t c with htc | htc | htc
      · exact h1 ⟨htI.1, htc⟩
      · exact absurd htc h3
      · exact h2 ⟨htc, htI.2.trans_le (min_le_left _ _)⟩
          ⟨htI.1, htI.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))⟩
    have := le_csSup hSbdd hmem
    rw [← hc] at this
    have : c < min (c + ε) b := lt_min (by linarith) hlt
    linarith
  intro t ht
  exact hflow b hb0 le_rfl (hcb' ▸ hPc) t ht

/-- Start-up off the switching surfaces: `e₃` is the strict maximizer near `t = 0`. -/
lemma irt_start_strict {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    (h : IsPontryaginExtremal T u g X Λ₁ ΛR (-1))
    (h31 : 0 < irt_chi 2 0 (X 0, Λ₁ 0, ΛR 0)) (h32 : 0 < irt_chi 2 1 (X 0, Λ₁ 0, ΛR 0)) :
    ∃ η > 0, ∀ᵐ t, t ∈ Ioo 0 η → u t = vertex 2 := by
  have hT : 0 < T := h.1.1
  obtain ⟨ε, hε, hεP⟩ := irt_vertex_near h ⟨le_rfl, hT.le⟩ h31 h32
  refine ⟨min ε T, lt_min hε hT, ?_⟩
  filter_upwards [hεP] with t ht htI
  exact ht ⟨htI.1, by linarith [htI.2, min_le_left ε T]⟩
    ⟨htI.1, htI.2.trans_le (min_le_right _ _)⟩

/-! #### Tools for the start-up on the switching surface -/

lemma irt_isCompact_simplex : IsCompact controlSimplex := by
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

lemma irt_continuous_controlMatrix : Continuous controlMatrix := by
  unfold controlMatrix
  refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
  fin_cases i <;> fin_cases j <;> dsimp <;> fun_prop

/-- The extremal vector field is continuous in `(q, u)` where `⟨Z_u, X⟩ ≠ 0`. -/
lemma irt_field_continuousAt {p : iso_PhasePt} {u : Fin 3 → ℝ}
    (hu : traceForm (controlMatrix u) p.1 ≠ 0) :
    ContinuousAt (fun x : iso_PhasePt × (Fin 3 → ℝ) ↦ iso_extremalField x.2 x.1) (p, u) := by
  have hZ := irt_continuous_controlMatrix
  unfold iso_extremalField costateRHS controlP traceForm at *
  fun_prop (disch := assumption)

/-- A continuous function of `(q, u)` that is `< r` at `p` for all `u` in a compact set stays
`< r` for `q` near `p`, uniformly in `u`. -/
lemma irt_tube_u {K : Set (Fin 3 → ℝ)} (hK : IsCompact K) {f : iso_PhasePt → (Fin 3 → ℝ) → ℝ}
    {p : iso_PhasePt}
    (hf : ∀ u ∈ K, ContinuousAt (fun x : iso_PhasePt × (Fin 3 → ℝ) ↦ f x.1 x.2) (p, u))
    {r : ℝ} (hr : ∀ u ∈ K, f p u < r) : ∀ᶠ q in 𝓝 p, ∀ u ∈ K, f q u < r :=
  hK.eventually_forall_of_forall_eventually fun u hu ↦ (hf u hu).eventually (gt_mem_nhds (hr u hu))

/-- On the switching surface the derivative of `χ₃₂` along the field of a control on the edge
`[e₂, e₃]` is that along the `e₃`-field (`iso_edge_slope`). -/
lemma irt_edge_dsw {p : iso_PhasePt} (hstar : IsStarState p.1)
    (hχ : switchingFn 1 2 p.2.2 p.1 = 0) {u : Fin 3 → ℝ}
    (hu : u ∈ controlSimplex) (hu0 : u 0 = 0) :
    irt_dsw 2 1 p.2.2 p.1 (iso_extremalField u p).2.2 (iso_extremalField u p).1 =
      irt_G 2 1 p := by
  have ha := (poly_traceForm_neg (poly_vertex_mem 1) hstar).ne
  have hb := (poly_traceForm_neg (poly_vertex_mem 2) hstar).ne
  have h1 := iso_edge_slope p hstar hχ u hu hu0
  have h2 := isw_hasDerivAt_chi32_line p.2.2 p.1 (iso_extremalField u p).2.2
    (iso_extremalField u p).1 ha hb
  have h3 := isw_hasDerivAt_chi32_line p.2.2 p.1 (iso_extremalField (vertex 2) p).2.2
    (iso_extremalField (vertex 2) p).1 ha hb
  rw [h3.deriv] at h1
  exact h2.unique h1

/-- `traceForm` of an integral curve, in integral form. -/
lemma irt_traceForm_integral {f v : ℝ → Mat2} {T : ℝ} (hI : IsIntegralCurve f v T) (Z : Mat2)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    traceForm (f t) Z = traceForm (f 0) Z + ∫ s in (0 : ℝ)..t, traceForm (v s) Z ∧
      traceForm Z (f t) = traceForm Z (f 0) + ∫ s in (0 : ℝ)..t, traceForm Z (v s) := by
  have hv : ∀ k l, IntervalIntegrable (fun s ↦ v s k l) volume 0 t := fun k l ↦
    (hI k l).1.mono_set (by
      rw [uIcc_of_le ht.1, uIcc_of_le (ht.1.trans ht.2)]
      exact Icc_subset_Icc_right ht.2)
  have he : ∀ k l, f t k l = f 0 k l + ∫ s in (0 : ℝ)..t, v s k l := fun k l ↦ (hI k l).2 t ht
  simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  constructor
  · rw [intervalIntegral.integral_add (((hv 0 0).mul_const _).add ((hv 0 1).mul_const _))
      (((hv 1 0).mul_const _).add ((hv 1 1).mul_const _)),
      intervalIntegral.integral_add ((hv 0 0).mul_const _) ((hv 0 1).mul_const _),
      intervalIntegral.integral_add ((hv 1 0).mul_const _) ((hv 1 1).mul_const _),
      intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
      he 0 0, he 0 1, he 1 0, he 1 1]
    ring
  · rw [intervalIntegral.integral_add (((hv 0 0).const_mul _).add ((hv 1 0).const_mul _))
      (((hv 0 1).const_mul _).add ((hv 1 1).const_mul _)),
      intervalIntegral.integral_add ((hv 0 0).const_mul _) ((hv 1 0).const_mul _),
      intervalIntegral.integral_add ((hv 0 1).const_mul _) ((hv 1 1).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      he 0 0, he 0 1, he 1 0, he 1 1]
    ring

/-- The first-order expansion of a quotient, with an explicit second-order remainder. -/
lemma irt_quot_remainder {A B dA dB C t : ℝ} (hB : B ≠ 0) (hC : 0 ≤ C) (ht : 0 ≤ t)
    (hdA : |dA| ≤ C * t) (hdB : |dB| ≤ C * t) (hsmall : C * t ≤ |B| / 2) :
    |(A + dA) / (B + dB) - A / B - (dA * B - A * dB) / B ^ 2| ≤
      2 * C ^ 2 * (|A| + |B|) / |B| ^ 3 * t ^ 2 := by
  have hB0 : 0 < |B| := abs_pos.2 hB
  have hBdB : |B| / 2 ≤ |B + dB| := by
    have := abs_sub_abs_le_abs_sub B (-dB)
    rw [sub_neg_eq_add, abs_neg] at this
    linarith
  have hBdB0 : B + dB ≠ 0 := abs_pos.1 (by linarith)
  have e : (A + dA) / (B + dB) - A / B - (dA * B - A * dB) / B ^ 2 =
      dB * (A * dB - B * dA) / (B ^ 2 * (B + dB)) := by
    field_simp; ring
  rw [e, abs_div, abs_mul, abs_mul, abs_pow, sq_abs]
  have hnum : |dB| * |A * dB - B * dA| ≤ (C * t) * ((|A| + |B|) * (C * t)) := by
    have h1 : |A * dB - B * dA| ≤ |A| * |dB| + |B| * |dA| := by
      rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
    have h2 : |A| * |dB| + |B| * |dA| ≤ (|A| + |B|) * (C * t) := by
      nlinarith [abs_nonneg A, abs_nonneg B]
    exact mul_le_mul hdB (h1.trans h2) (abs_nonneg _) (by positivity)
  have hden : B ^ 2 * (|B| / 2) ≤ B ^ 2 * |B + dB| := by gcongr
  rw [div_le_iff₀ (by positivity)]
  have hB2 : B ^ 2 = |B| ^ 2 := (sq_abs B).symm
  calc |dB| * |A * dB - B * dA| ≤ (C * t) * ((|A| + |B|) * (C * t)) := hnum
    _ = 2 * C ^ 2 * (|A| + |B|) / |B| ^ 3 * t ^ 2 * (B ^ 2 * (|B| / 2)) := by
        rw [hB2]; field_simp
    _ ≤ 2 * C ^ 2 * (|A| + |B|) / |B| ^ 3 * t ^ 2 * (B ^ 2 * |B + dB|) := by gcongr

lemma irt_traceForm_intervalIntegrable {v : ℝ → Mat2} {a b : ℝ}
    (hv : ∀ i j, IntervalIntegrable (fun s ↦ v s i j) volume a b) (Z : Mat2) :
    IntervalIntegrable (fun s ↦ traceForm (v s) Z) volume a b ∧
      IntervalIntegrable (fun s ↦ traceForm Z (v s)) volume a b := by
  simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  exact ⟨(((hv 0 0).mul_const _).add ((hv 0 1).mul_const _)).add
      (((hv 1 0).mul_const _).add ((hv 1 1).mul_const _)),
    (((hv 0 0).const_mul _).add ((hv 1 0).const_mul _)).add
      (((hv 0 1).const_mul _).add ((hv 1 1).const_mul _))⟩

/-- The linearization of `χ₃₂` in terms of `⟨·, Z_{e₂}⟩`, `⟨Z_{e₂}, ·⟩`, `⟨·, Z_{e₃}⟩`,
`⟨Z_{e₃}, ·⟩`. -/
lemma irt_dsw_eq (ΛR X δΛR δX : Mat2) (h1 : traceForm (controlMatrix (vertex 1)) X ≠ 0)
    (h2 : traceForm (controlMatrix (vertex 2)) X ≠ 0) :
    irt_dsw 2 1 ΛR X δΛR δX =
      (traceForm δΛR (controlMatrix (vertex 1)) * traceForm (controlMatrix (vertex 1)) X -
          traceForm ΛR (controlMatrix (vertex 1)) * traceForm (controlMatrix (vertex 1)) δX) /
          traceForm (controlMatrix (vertex 1)) X ^ 2 -
        (traceForm δΛR (controlMatrix (vertex 2)) * traceForm (controlMatrix (vertex 2)) X -
          traceForm ΛR (controlMatrix (vertex 2)) * traceForm (controlMatrix (vertex 2)) δX) /
          traceForm (controlMatrix (vertex 2)) X ^ 2 := by
  simp only [irt_dsw, controlP, traceForm, Matrix.mul_sub, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul] at h1 h2 ⊢
  field_simp
  ring

/-- The scalar core of the start-up: a difference of quotients `a₁/b₁ - a₂/b₂` of absolutely
continuous functions, vanishing at `0`, whose linearization has derivative `≥ κ > 0` almost
everywhere and whose derivatives are bounded, is positive just after `0`. -/
lemma irt_quot_pos {A₁ B₁ A₂ B₂ C κ η₁ : ℝ} {α₁ β₁ α₂ β₂ : ℝ → ℝ} (hB₁ : B₁ ≠ 0)
    (hB₂ : B₂ ≠ 0) (h0 : A₁ / B₁ - A₂ / B₂ = 0) (hκ : 0 < κ) (hη₁ : 0 < η₁) (hC : 0 ≤ C)
    (hi1 : IntervalIntegrable α₁ volume 0 η₁) (hi2 : IntervalIntegrable β₁ volume 0 η₁)
    (hi3 : IntervalIntegrable α₂ volume 0 η₁) (hi4 : IntervalIntegrable β₂ volume 0 η₁)
    (hbd : ∀ s ∈ Icc 0 η₁, |α₁ s| ≤ C ∧ |β₁ s| ≤ C ∧ |α₂ s| ≤ C ∧ |β₂ s| ≤ C)
    (hℓ : ∀ᵐ s, s ∈ Ioo 0 η₁ →
      κ ≤ (α₁ s * B₁ - A₁ * β₁ s) / B₁ ^ 2 - (α₂ s * B₂ - A₂ * β₂ s) / B₂ ^ 2) :
    ∃ η > 0, η ≤ η₁ ∧ ∀ t ∈ Ioo 0 η,
      0 < (A₁ + ∫ s in (0 : ℝ)..t, α₁ s) / (B₁ + ∫ s in (0 : ℝ)..t, β₁ s) -
        (A₂ + ∫ s in (0 : ℝ)..t, α₂ s) / (B₂ + ∫ s in (0 : ℝ)..t, β₂ s) := by
  have hb1 : 0 < |B₁| := abs_pos.2 hB₁
  have hb2 : 0 < |B₂| := abs_pos.2 hB₂
  set K := 2 * C ^ 2 * (|A₁| + |B₁|) / |B₁| ^ 3 + 2 * C ^ 2 * (|A₂| + |B₂|) / |B₂| ^ 3 with hK
  have hK0 : 0 ≤ K := by positivity
  set η := min η₁ (min (|B₁| / (2 * C + 1)) (min (|B₂| / (2 * C + 1)) (κ / (K + 1)))) with hη
  have hη0 : 0 < η := lt_min hη₁ (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  refine ⟨η, hη0, min_le_left _ _, fun t ht ↦ ?_⟩
  have htη₁ : t ≤ η₁ := ht.2.le.trans (min_le_left _ _)
  have ht1 : t < |B₁| / (2 * C + 1) := ht.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have ht2 : t < |B₂| / (2 * C + 1) :=
    ht.2.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have ht3 : t < κ / (K + 1) :=
    ht.2.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hsub : ∀ f : ℝ → ℝ, IntervalIntegrable f volume 0 η₁ → IntervalIntegrable f volume 0 t :=
    fun f hf ↦ hf.mono_set (by
      rw [uIcc_of_le ht.1.le, uIcc_of_le hη₁.le]; exact Icc_subset_Icc_right htη₁)
  have hbnd : ∀ f : ℝ → ℝ, (∀ s ∈ Icc 0 η₁, |f s| ≤ C) → |∫ s in (0 : ℝ)..t, f s| ≤ C * t :=
    fun f hf ↦ by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t) (C := C)
        (f := f) fun x hx ↦ by
          rw [uIoc_of_le ht.1.le] at hx
          exact hf x ⟨hx.1.le, hx.2.trans htη₁⟩
      rwa [Real.norm_eq_abs, sub_zero, abs_of_pos ht.1] at this
  have hd1 := hbnd α₁ fun s hs ↦ (hbd s hs).1
  have hd2 := hbnd β₁ fun s hs ↦ (hbd s hs).2.1
  have hd3 := hbnd α₂ fun s hs ↦ (hbd s hs).2.2.1
  have hd4 := hbnd β₂ fun s hs ↦ (hbd s hs).2.2.2
  have hCt1 : C * t ≤ |B₁| / 2 := by
    rw [lt_div_iff₀ (by positivity)] at ht1; nlinarith [ht.1]
  have hCt2 : C * t ≤ |B₂| / 2 := by
    rw [lt_div_iff₀ (by positivity)] at ht2; nlinarith [ht.1]
  have hR1 := irt_quot_remainder (A := A₁) hB₁ hC ht.1.le hd1 hd2 hCt1
  have hR2 := irt_quot_remainder (A := A₂) hB₂ hC ht.1.le hd3 hd4 hCt2
  -- the linear part
  set L := ∫ s in (0 : ℝ)..t,
    ((α₁ s * B₁ - A₁ * β₁ s) / B₁ ^ 2 - (α₂ s * B₂ - A₂ * β₂ s) / B₂ ^ 2) with hL
  have hLeq : L = ((∫ s in (0 : ℝ)..t, α₁ s) * B₁ - A₁ * ∫ s in (0 : ℝ)..t, β₁ s) / B₁ ^ 2 -
      ((∫ s in (0 : ℝ)..t, α₂ s) * B₂ - A₂ * ∫ s in (0 : ℝ)..t, β₂ s) / B₂ ^ 2 := by
    rw [hL, intervalIntegral.integral_sub, intervalIntegral.integral_div,
      intervalIntegral.integral_div, intervalIntegral.integral_sub, intervalIntegral.integral_sub,
      intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul]
    · exact (hsub _ hi3).mul_const _
    · exact (hsub _ hi4).const_mul _
    · exact (hsub _ hi1).mul_const _
    · exact (hsub _ hi2).const_mul _
    · exact (((hsub _ hi1).mul_const _).sub ((hsub _ hi2).const_mul _)).div_const _
    · exact (((hsub _ hi3).mul_const _).sub ((hsub _ hi4).const_mul _)).div_const _
  have hLb : κ * t ≤ L := by
    have h := intervalIntegral.integral_mono_ae_restrict (μ := volume) ht.1.le
      (f := fun _ ↦ κ) intervalIntegrable_const
      ((((hsub _ hi1).mul_const _).sub ((hsub _ hi2).const_mul _)).div_const _ |>.sub
        ((((hsub _ hi3).mul_const _).sub ((hsub _ hi4).const_mul _)).div_const _)) (by
        rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
        filter_upwards [hℓ, (countable_singleton (0 : ℝ)).ae_notMem volume,
          (countable_singleton t).ae_notMem volume] with s hs h0 ht' hsI
        exact hs ⟨lt_of_le_of_ne hsI.1 (Ne.symm h0),
          (lt_of_le_of_ne hsI.2 ht').trans_le htη₁⟩)
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h
    rw [mul_comm]; exact h
  -- the remainders are `O(t²)`
  have hKt : K * t ^ 2 < κ * t := by
    rw [lt_div_iff₀ (by positivity)] at ht3
    nlinarith [ht.1]
  have hR1' := (abs_le.1 hR1).1
  have hR2' := (abs_le.1 hR2).2
  rw [hLeq] at hLb
  have e1 : A₁ / B₁ = A₂ / B₂ := sub_eq_zero.1 h0
  nlinarith [hR1', hR2', hLb, hKt]

/-! ### The `e₃`-flow near the octagon -/

/-- The derivative of `χ_ij` along the `e₃`-flow. -/
lemma irt_chi_flow_hasDerivAt (i j : Fin 3) (p : iso_PhasePt) (t : ℝ)
    (hD : irt_Den (iso_vertexFlow 2 p t)) :
    HasDerivAt (fun s ↦ irt_chi i j (iso_vertexFlow 2 p s)) (irt_G i j (iso_vertexFlow 2 p t)) t :=
  irt_chi_hasDerivAt (f := iso_vertexFlow 2 p) (f' := iso_extremalField (vertex 2)
    (iso_vertexFlow 2 p t)) (ivf_vfX_hasDerivAt 2 p t) (ivf_vfΛR_hasDerivAt 2 p t) hD

lemma irt_exp_continuous : Continuous (NormedSpace.exp : Mat2 → Mat2) := by
  open scoped Matrix.Norms.Operator in
  have : @CompleteSpace Mat2 PseudoMetricSpace.toUniformSpace := by
    exact inferInstanceAs (CompleteSpace Mat2)
  exact NormedSpace.exp_continuous

/-- The inverse of a continuous curve of invertible matrices is continuous. -/
lemma irt_continuous_inv {Y : Type*} [TopologicalSpace Y] {G : Y → Mat2} (hG : Continuous G)
    (hdet : ∀ y, IsUnit (G y).det) : Continuous fun y ↦ (G y)⁻¹ := by
  have e : (fun y ↦ (G y)⁻¹) = fun y ↦ ((G y).det)⁻¹ • (G y).adjugate := by
    funext y; rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [e]
  exact (hG.matrix_det.inv₀ fun y ↦ (hdet y).ne_zero).smul hG.matrix_adjugate

/-- The closed-form `e₃`-flow is jointly continuous where `⟨Z_{e₃}, X₀⟩ ≠ 0`. -/
lemma irt_flow_continuousAt {p : iso_PhasePt}
    (hp : traceForm (controlMatrix (vertex 2)) p.1 ≠ 0) (t : ℝ) :
    ContinuousAt (fun x : iso_PhasePt × ℝ ↦ iso_vertexFlow 2 x.1 x.2) (p, t) := by
  set S : Set iso_PhasePt := {q | traceForm (controlMatrix (vertex 2)) q.1 ≠ 0} with hS
  have hSo : IsOpen S := isOpen_ne_fun (by unfold traceForm; fun_prop) continuous_const
  have he : Topology.IsOpenEmbedding (fun x : S × ℝ ↦ ((x.1 : iso_PhasePt), x.2)) :=
    hSo.isOpenEmbedding_subtypeVal.prodMap .id
  have hE := irt_exp_continuous
  have hP : Continuous fun q : S ↦ iso_vfP 2 q.1 := by
    have hden : Continuous fun q : S ↦ traceForm (controlMatrix (vertex 2)) q.1.1 := by
      unfold traceForm
      exact (continuous_const.mul (continuous_fst.comp continuous_subtype_val)).matrix_trace
    exact (hden.inv₀ fun q ↦ q.2).smul continuous_const
  have hq : Continuous fun x : S × ℝ ↦ (x.1 : iso_PhasePt) := continuous_subtype_val.comp
    continuous_fst
  have hPx : Continuous fun x : S × ℝ ↦ iso_vfP 2 x.1.1 := hP.comp continuous_fst
  have hX : Continuous fun x : S × ℝ ↦ iso_vfX 2 x.1.1 x.2 := by
    unfold iso_vfX constControlX
    exact ((hE.comp (continuous_snd.smul hPx)).mul (continuous_fst.comp hq)).mul
      (hE.comp (continuous_snd.neg.smul hPx))
  have hG : Continuous fun x : S × ℝ ↦ iso_vfG 2 x.1.1 x.2 := by
    unfold iso_vfG constControlG
    exact (hE.comp (continuous_snd.smul ((continuous_fst.comp hq).add hPx))).mul
      (hE.comp (continuous_snd.neg.smul hPx))
  have hGi : Continuous fun x : S × ℝ ↦ (iso_vfG 2 x.1.1 x.2)⁻¹ :=
    irt_continuous_inv hG fun x ↦ ivf_vfG_isUnit 2 _ _
  have hL : Continuous fun x : S × ℝ ↦ iso_vfΛ₁ 2 x.1.1 x.2 := by
    unfold iso_vfΛ₁
    exact (hGi.mul (continuous_fst.comp (continuous_snd.comp hq))).mul hG
  have hM : Continuous fun x : S × ℝ ↦ iso_vfM 2 x.1.1 x.2 := by
    unfold iso_vfM
    exact ((hE.comp (continuous_snd.neg.smul hPx)).mul (hL.add continuous_const)).mul
      (hE.comp (continuous_snd.smul hPx))
  have hC : Continuous fun x : S × ℝ ↦ iso_vfC 2 x.1.1 x.2 := by
    unfold iso_vfC
    have hf : Continuous (Function.uncurry fun (q : S) (s : ℝ) ↦
        traceForm (iso_vfM 2 q.1 s) (q.1.1 * iso_vfP 2 q.1 - iso_vfP 2 q.1 * q.1.1)) := by
      unfold traceForm
      exact (hM.mul (((continuous_fst.comp hq).mul hPx).sub
        (hPx.mul (continuous_fst.comp hq)))).matrix_trace
    refine Continuous.sub ?_ (intervalIntegral.continuous_parametric_primitive_of_continuous
      (μ := volume) (a₀ := 0) hf)
    unfold traceForm
    exact ((continuous_snd.comp (continuous_snd.comp hq)).mul hPx).matrix_trace
  have hR : Continuous fun x : S × ℝ ↦ iso_vfΛR 2 x.1.1 x.2 := by
    unfold iso_vfΛR
    have hI1 : Continuous fun x : S × ℝ ↦ ∫ σ in (0 : ℝ)..x.2, iso_vfC 2 x.1.1 σ :=
      intervalIntegral.continuous_parametric_primitive_of_continuous (μ := volume) (a₀ := 0)
        (f := fun (q : S) σ ↦ iso_vfC 2 q.1 σ) hC
    have hI2 : Continuous fun x : S × ℝ ↦ (Matrix.of fun i j ↦ ∫ s in (0 : ℝ)..x.2,
        (iso_vfM 2 x.1.1 s * x.1.1.1 - x.1.1.1 * iso_vfM 2 x.1.1 s) i j : Mat2) := by
      refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
      exact intervalIntegral.continuous_parametric_primitive_of_continuous (μ := volume)
        (a₀ := 0) (f := fun (q : S) s ↦ (iso_vfM 2 q.1 s * q.1.1 - q.1.1 * iso_vfM 2 q.1 s) i j)
        (((hM.mul (continuous_fst.comp hq)).sub
          ((continuous_fst.comp hq).mul hM)).matrix_elem i j)
    exact ((hE.comp (continuous_snd.smul hPx)).mul
      (((continuous_snd.comp (continuous_snd.comp hq)).sub
        (hI1.smul (hPx.mul (continuous_fst.comp hq) |>.sub
          ((continuous_fst.comp hq).mul hPx)))).sub hI2)).mul
      (hE.comp (continuous_snd.neg.smul hPx))
  have hall : Continuous ((fun x : iso_PhasePt × ℝ ↦ iso_vertexFlow 2 x.1 x.2) ∘
      (fun x : S × ℝ ↦ ((x.1 : iso_PhasePt), x.2))) := hX.prodMk (hL.prodMk hR)
  exact (he.continuousAt_iff (x := (⟨p, hp⟩, t))).1 hall.continuousAt

/-- A function with negative derivative on `[a, b]` is strictly decreasing there. -/
lemma irt_strictAntiOn {f f' : ℝ → ℝ} {a b : ℝ} (hd : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hneg : ∀ x ∈ Icc a b, f' x < 0) : StrictAntiOn f (Icc a b) := by
  intro x hx z hz hxz
  have hsub : Icc x z ⊆ Icc a b := Icc_subset_Icc hx.1 hz.2
  obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope f f' hxz
    (fun w hw ↦ (hd w (hsub hw)).continuousAt.continuousWithinAt)
    (fun w hw ↦ hd w (hsub (Ioo_subset_Icc_self hw)))
  have hn := hneg c (hsub (Ioo_subset_Icc_self hc))
  rw [eq_div_iff (sub_pos.2 hxz).ne'] at hc'
  nlinarith [sub_pos.2 hxz]

/-- A function with positive derivative on `[a, b]` is strictly increasing there. -/
lemma irt_strictMonoOn {f f' : ℝ → ℝ} {a b : ℝ} (hd : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hpos : ∀ x ∈ Icc a b, 0 < f' x) : StrictMonoOn f (Icc a b) := by
  have := irt_strictAntiOn (f := fun x ↦ -f x) (f' := fun x ↦ -f' x) (a := a) (b := b)
    (fun x hx ↦ (hd x hx).neg) (fun x hx ↦ by linarith [hpos x hx])
  intro x hx z hz hxz
  have := this hx hz hxz
  simp only at this
  linarith

lemma irt_isOpen_pos {f : iso_PhasePt → ℝ} (hf : ∀ q, irt_Den q → ContinuousAt f q) :
    IsOpen {q | irt_Den q ∧ 0 < f q} := by
  rw [isOpen_iff_mem_nhds]
  rintro q ⟨hD, hpos⟩
  exact Filter.inter_mem (irt_isOpen_Den.mem_nhds hD) ((hf q hD).eventually (lt_mem_nhds hpos))

lemma irt_Den_qFix : irt_Den (iso_qFix (y₀ 1)) := by
  obtain ⟨hy0, hy1⟩ := poly_y₀_mem (le_refl 1)
  have h := segX_star (y₀ 1) hy0 hy1 0 ⟨le_rfl, (poly_switchTime_pos hy0 hy1).le⟩
  rw [str_segX_zero _ (poly_y0_pos hy0)] at h
  exact irt_Den_of_star h

/-- The tube lemma for the flow from `q_oct`: an open condition that holds along the octagon's
flow on a compact time set holds, on that set, for the flow from every nearby point. -/
lemma irt_tube {K : Set ℝ} (hK : IsCompact K) {P : iso_PhasePt → Prop} (hPo : IsOpen {q | P q})
    (hP : ∀ t ∈ K, P (iso_vertexFlow 2 (iso_qFix (y₀ 1)) t)) :
    ∀ᶠ p in 𝓝 (iso_qFix (y₀ 1)), ∀ t ∈ K, P (iso_vertexFlow 2 p t) := by
  refine hK.eventually_forall_of_forall_eventually fun t ht ↦ ?_
  exact (irt_flow_continuousAt (irt_Den_qFix 2) t).eventually (hPo.mem_nhds (hP t ht))

/-- The octagon's `e₃`-arc: the facts of Lemma 7.5.3 and of step 2 used below. -/
lemma irt_oct_facts :
    (∀ t ∈ Icc 0 (tsw 1), irt_Den (iso_vertexFlow 2 (iso_qFix (y₀ 1)) t)) ∧
    (∀ t ∈ Icc 0 (tsw 1), t ≠ tsw 1 → 0 < irt_chi 2 0 (iso_vertexFlow 2 (iso_qFix (y₀ 1)) t)) ∧
    (∀ t ∈ Icc 0 (tsw 1), t ≠ 0 → 0 < irt_chi 2 1 (iso_vertexFlow 2 (iso_qFix (y₀ 1)) t)) ∧
    irt_chi 2 0 (iso_vertexFlow 2 (iso_qFix (y₀ 1)) (tsw 1)) = 0 ∧
    irt_G 2 0 (iso_vertexFlow 2 (iso_qFix (y₀ 1)) (tsw 1)) = -iso_chi32Slope (y₀ 1) ∧
    irt_G 2 1 (iso_vertexFlow 2 (iso_qFix (y₀ 1)) 0) = iso_chi32Slope (y₀ 1) := by
  obtain ⟨hy0, hy1⟩ := poly_y₀_mem (le_refl 1)
  have hτ : 0 < tsw 1 := poly_switchTime_pos hy0 hy1
  have hOe : ∀ t, iso_vertexFlow 2 (iso_qFix (y₀ 1)) t =
      (segX (y₀ 1) t, strongΛ₁ (y₀ 1) t, strongΛR (y₀ 1) t) := iso_vertexFlow_qFix _ hy0
  have hlift := strongLift_isStrongLift _ hy0
  have h753 := lemma7_5_3 _ hy0 hy1 _ _ hlift
  have hDen : ∀ t ∈ Icc 0 (tsw 1), irt_Den (iso_vertexFlow 2 (iso_qFix (y₀ 1)) t) :=
    fun t ht ↦ irt_Den_of_star (by rw [hOe]; exact segX_star _ hy0 hy1 t ht)
  have hfun : ∀ i j : Fin 3, (fun s ↦ irt_chi i j (iso_vertexFlow 2 (iso_qFix (y₀ 1)) s)) =
      fun s ↦ switchingFn i j (strongΛR (y₀ 1) s) (segX (y₀ 1) s) := fun i j ↦ by
    funext s; rw [hOe]; rfl
  refine ⟨hDen, fun t ht hne ↦ ?_, fun t ht hne ↦ ?_, ?_, ?_, ?_⟩
  · have h := h753 t ht
    rw [hOe]
    exact lt_of_le_of_ne h.1 fun h0 ↦ hne (h.2.2.1 h0.symm)
  · have h := h753 t ht
    rw [hOe]
    exact lt_of_le_of_ne h.2.1 fun h0 ↦ hne (h.2.2.2 h0.symm)
  · rw [hOe]; exact hlift.2.2.2.2.2.2.1
  · have h1 := irt_chi_flow_hasDerivAt 2 0 (iso_qFix (y₀ 1)) (tsw 1)
      (hDen _ ⟨hτ.le, le_rfl⟩)
    rw [hfun] at h1
    exact h1.unique (iso_chi31_hasDerivAt _ hy0)
  · have h1 := irt_chi_flow_hasDerivAt 2 1 (iso_qFix (y₀ 1)) 0 (hDen _ ⟨le_rfl, hτ.le⟩)
    rw [hfun] at h1
    exact h1.unique (iso_chi32_hasDerivAt _ hy0)

/-- **The flow from near `q_oct`.** For `p` near `q_oct` with `χ₃₂(p) ≥ 0`, the Poincaré time is
near `t_sw`, `χ₃₁ > 0` before it and vanishes there, and `χ₃₂ > 0` after `0`. -/
theorem irt_flow_start (δ : ℝ) (hδ : 0 < δ) : ∃ W ∈ 𝓝 (iso_qFix (y₀ 1)), ∀ p ∈ W,
    0 ≤ irt_chi 2 1 p →
      iso_poincareTime p ∈ Ioo (tsw 1 - δ) (tsw 1 + δ) ∧
      (∀ t ∈ Ico 0 (iso_poincareTime p), 0 < irt_chi 2 0 (iso_vertexFlow 2 p t)) ∧
      irt_chi 2 0 (iso_vertexFlow 2 p (iso_poincareTime p)) = 0 ∧
      (∀ t ∈ Ioc 0 (iso_poincareTime p), 0 < irt_chi 2 1 (iso_vertexFlow 2 p t)) := by
  obtain ⟨hy0, hy1⟩ := poly_y₀_mem (le_refl 1)
  set τ := tsw 1 with hτdef
  have hτ : 0 < τ := poly_switchTime_pos hy0 hy1
  set qo := iso_qFix (y₀ 1) with hqo
  set O : ℝ → iso_PhasePt := fun t ↦ iso_vertexFlow 2 qo t with hO
  obtain ⟨hDen, h31O, h32O, h31τ, hG31, hG32⟩ := irt_oct_facts
  have hκ : 0 < iso_chi32Slope (y₀ 1) := iso_chi32Slope_pos _ hy0 hy1
  have hOc : Continuous O := continuous_iff_continuousAt.2 fun t ↦
    (irt_flow_continuousAt (irt_Den_qFix 2) t).comp (f := fun s ↦ (qo, s))
      (continuousAt_const.prodMk continuousAt_id)
  -- Step 1: near `t_sw` the octagon has `χ₃₁' < 0` and `χ₃₂ > 0`; near `0`, `χ₃₂' > 0`
  have hev1 : ∀ᶠ t in 𝓝 τ, irt_Den (O t) ∧ 0 < -irt_G 2 0 (O t) ∧ 0 < irt_chi 2 1 (O t) := by
    have hDτ := hDen τ ⟨hτ.le, le_rfl⟩
    have hc1 : ContinuousAt (fun t ↦ irt_G 2 0 (O t)) τ :=
      (irt_G_continuousAt 2 0 hDτ).comp hOc.continuousAt
    have hc2 : ContinuousAt (fun t ↦ irt_chi 2 1 (O t)) τ :=
      (irt_chi_continuousAt 2 1 hDτ).comp hOc.continuousAt
    have h32τ : 0 < irt_chi 2 1 (O τ) := h32O τ ⟨hτ.le, le_rfl⟩ hτ.ne'
    have hG : irt_G 2 0 (O τ) < 0 := by rw [hO, hG31]; linarith
    filter_upwards [hOc.continuousAt.eventually (irt_isOpen_Den.mem_nhds hDτ),
      hc1.eventually (gt_mem_nhds hG), hc2.eventually (lt_mem_nhds h32τ)] with t h1 h2 h3
    exact ⟨h1, by linarith, h3⟩
  have hev0 : ∀ᶠ t in 𝓝 0, irt_Den (O t) ∧ 0 < irt_G 2 1 (O t) := by
    have hD0 := hDen 0 ⟨le_rfl, hτ.le⟩
    have hc1 : ContinuousAt (fun t ↦ irt_G 2 1 (O t)) 0 :=
      (irt_G_continuousAt 2 1 hD0).comp hOc.continuousAt
    have hG : 0 < irt_G 2 1 (O 0) := by rw [hO, hG32]; exact hκ
    filter_upwards [hOc.continuousAt.eventually (irt_isOpen_Den.mem_nhds hD0),
      hc1.eventually (lt_mem_nhds hG)] with t h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨δ₂, hδ₂, hb2⟩ := Metric.eventually_nhds_iff.1 hev1
  obtain ⟨δ₃, hδ₃, hb3⟩ := Metric.eventually_nhds_iff.1 hev0
  set δ₁ := min (min δ (τ / 2)) (min (δ₂ / 2) (δ₃ / 2)) with hδ₁
  have hδ₁0 : 0 < δ₁ := lt_min (lt_min hδ (by positivity)) (lt_min (by positivity) (by positivity))
  have hδ₁a : δ₁ ≤ δ := (min_le_left _ _).trans (min_le_left _ _)
  have hδ₁b : δ₁ ≤ τ / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hδ₁c : δ₁ ≤ δ₂ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ₁d : δ₁ ≤ δ₃ / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hA : ∀ t ∈ Icc (τ - δ₁) (τ + δ₁),
      irt_Den (O t) ∧ 0 < -irt_G 2 0 (O t) ∧ 0 < irt_chi 2 1 (O t) := fun t ht ↦
    hb2 (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2])
  have hB : ∀ t ∈ Icc 0 δ₁, irt_Den (O t) ∧ 0 < irt_G 2 1 (O t) := fun t ht ↦
    hb3 (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2])
  -- Step 2: `χ₃₁ < 0` on the octagon's flow just after `t_sw`
  have hend : 0 < -irt_chi 2 0 (O (τ + δ₁)) := by
    have hanti := irt_strictAntiOn (f := fun t ↦ irt_chi 2 0 (O t))
      (f' := fun t ↦ irt_G 2 0 (O t)) (a := τ) (b := τ + δ₁)
      (fun t ht ↦ irt_chi_flow_hasDerivAt 2 0 qo t (hA t ⟨by linarith [ht.1], ht.2⟩).1)
      (fun t ht ↦ by linarith [(hA t ⟨by linarith [ht.1], ht.2⟩).2.1])
    have := hanti ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
    simp only [hO] at this
    rw [h31τ] at this
    linarith
  -- the tube lemma, five times
  have hopen : ∀ f : iso_PhasePt → ℝ, (∀ q, irt_Den q → ContinuousAt f q) →
      IsOpen {q | irt_Den q ∧ 0 < f q} := fun f hf ↦ irt_isOpen_pos hf
  have hT1 := irt_tube (K := Icc 0 (τ - δ₁)) isCompact_Icc
    (hopen _ fun q hq ↦ irt_chi_continuousAt 2 0 hq) fun t ht ↦
      ⟨hDen t ⟨ht.1, by linarith [ht.2]⟩, h31O t ⟨ht.1, by linarith [ht.2]⟩ (by linarith [ht.2])⟩
  have hT2 := irt_tube (K := Icc (τ - δ₁) (τ + δ₁)) isCompact_Icc
    (hopen _ fun q hq ↦ (irt_G_continuousAt 2 0 hq).neg) fun t ht ↦ ⟨(hA t ht).1, (hA t ht).2.1⟩
  have hT3 := irt_tube (K := {τ + δ₁}) isCompact_singleton
    (hopen _ fun q hq ↦ (irt_chi_continuousAt 2 0 hq).neg) fun t ht ↦ by
      rw [mem_singleton_iff] at ht
      subst ht
      exact ⟨(hA _ ⟨by linarith, le_rfl⟩).1, hend⟩
  have hT4 := irt_tube (K := Icc δ₁ (τ + δ₁)) isCompact_Icc
    (hopen _ fun q hq ↦ irt_chi_continuousAt 2 1 hq) fun t ht ↦ by
      rcases le_or_gt t τ with htτ | htτ
      · exact ⟨hDen t ⟨by linarith [ht.1], htτ⟩, h32O t ⟨by linarith [ht.1], htτ⟩
          (by linarith [ht.1])⟩
      · exact ⟨(hA t ⟨by linarith, ht.2⟩).1, (hA t ⟨by linarith, ht.2⟩).2.2⟩
  have hT5 := irt_tube (K := Icc 0 δ₁) isCompact_Icc
    (hopen _ fun q hq ↦ irt_G_continuousAt 2 1 hq) fun t ht ↦ hB t ht
  refine ⟨_, hT1.and (hT2.and (hT3.and (hT4.and hT5))), ?_⟩
  rintro p ⟨h1, h2, h3, h4, h5⟩ h32p
  -- the flow from `p`
  set φ : ℝ → ℝ := fun t ↦ irt_chi 2 0 (iso_vertexFlow 2 p t) with hφ
  set ψ : ℝ → ℝ := fun t ↦ irt_chi 2 1 (iso_vertexFlow 2 p t) with hψ
  have hDp : ∀ t ∈ Icc 0 (τ + δ₁), irt_Den (iso_vertexFlow 2 p t) := by
    intro t ht
    rcases le_or_gt t (τ - δ₁) with h' | h'
    · exact (h1 t ⟨ht.1, h'⟩).1
    · exact (h2 t ⟨h'.le, ht.2⟩).1
  have hφd : ∀ t ∈ Icc 0 (τ + δ₁), HasDerivAt φ (irt_G 2 0 (iso_vertexFlow 2 p t)) t :=
    fun t ht ↦ irt_chi_flow_hasDerivAt 2 0 p t (hDp t ht)
  have hanti : StrictAntiOn φ (Icc (τ - δ₁) (τ + δ₁)) :=
    irt_strictAntiOn (fun t ht ↦ hφd t ⟨by linarith [ht.1], ht.2⟩)
      fun t ht ↦ by have := (h2 t ht).2; simp only [Pi.neg_apply] at this; linarith
  have hφa : 0 < φ (τ - δ₁) := (h1 (τ - δ₁) ⟨by linarith, le_rfl⟩).2
  have hφb : φ (τ + δ₁) < 0 := by
    have := (h3 (τ + δ₁) rfl).2; simp only [Pi.neg_apply] at this; linarith
  have hφc : ContinuousOn φ (Icc (τ - δ₁) (τ + δ₁)) := fun t ht ↦
    (hφd t ⟨by linarith [ht.1], ht.2⟩).continuousAt.continuousWithinAt
  obtain ⟨ts, hts, hφts⟩ := intermediate_value_Icc' (by linarith) hφc ⟨hφb.le, hφa.le⟩
  have hts1 : τ - δ₁ < ts := lt_of_le_of_ne hts.1 fun h ↦ by rw [← h] at hφts; linarith
  have hts2 : ts < τ + δ₁ := lt_of_le_of_ne hts.2 fun h ↦ by rw [h] at hφts; linarith
  -- `φ > 0` before `ts`
  have hφpos : ∀ t ∈ Ico 0 ts, 0 < φ t := by
    intro t ht
    rcases le_or_gt t (τ - δ₁) with h' | h'
    · exact (h1 t ⟨ht.1, h'⟩).2
    · have := hanti ⟨h'.le, by linarith [ht.2]⟩ ⟨hts.1, hts.2⟩ ht.2
      rwa [hφts] at this
  have hτp : iso_poincareTime p = ts := by
    refine IsLeast.csInf_eq ⟨⟨by linarith, hφts⟩, fun t ht ↦ ?_⟩
    by_contra hlt
    exact (hφpos t ⟨ht.1.le, lt_of_not_ge hlt⟩).ne' ht.2
  rw [hτp]
  refine ⟨⟨by linarith, by linarith⟩, hφpos, hφts, fun t ht ↦ ?_⟩
  rcases le_or_gt δ₁ t with h' | h'
  · exact (h4 t ⟨h', by linarith [ht.2]⟩).2
  · have hmono := irt_strictMonoOn (f := ψ) (f' := fun t ↦ irt_G 2 1 (iso_vertexFlow 2 p t))
      (a := 0) (b := δ₁) (fun t ht ↦ irt_chi_flow_hasDerivAt 2 1 p t (h5 t ht).1)
      fun t ht ↦ (h5 t ht).2
    have := hmono ⟨le_rfl, hδ₁0.le⟩ ⟨ht.1.le, h'.le⟩ ht.1
    simp only [hψ, ivf_vertexFlow_zero] at this
    linarith

/-- **The flow from near `O(t_sw) = R⁻¹ q_oct R`.** For `p` there with `χ₃₁(p) > 0`, `χ₃₁`
vanishes after a short time, `χ₃₂ > 0` meanwhile, and the Poincaré map lands near `q_oct`. -/
theorem irt_flow_end (W' : Set iso_PhasePt) (hW' : W' ∈ 𝓝 (iso_qFix (y₀ 1))) (δ : ℝ)
    (hδ : 0 < δ) : ∃ W ∈ 𝓝 (iso_adRinvPow 1 (iso_qFix (y₀ 1))), ∀ p ∈ W,
    0 < irt_chi 2 0 p →
      iso_poincareTime p ∈ Ioo 0 δ ∧
      (∀ t ∈ Ico 0 (iso_poincareTime p), 0 < irt_chi 2 0 (iso_vertexFlow 2 p t)) ∧
      irt_chi 2 0 (iso_vertexFlow 2 p (iso_poincareTime p)) = 0 ∧
      (∀ t ∈ Icc 0 (iso_poincareTime p), 0 < irt_chi 2 1 (iso_vertexFlow 2 p t)) ∧
      iso_poincareMap p ∈ W' := by
  obtain ⟨hy0, hy1⟩ := poly_y₀_mem (le_refl 1)
  set τ := tsw 1 with hτdef
  have hτ : 0 < τ := poly_switchTime_pos hy0 hy1
  set qo := iso_qFix (y₀ 1) with hqo
  obtain ⟨hDen, -, h32O, h31τ, hG31, -⟩ := irt_oct_facts
  have hκ : 0 < iso_chi32Slope (y₀ 1) := iso_chi32Slope_pos _ hy0 hy1
  set κ := iso_chi32Slope (y₀ 1) with hκdef
  -- `O(t_sw) = R⁻¹ q_oct R`
  have hq1 : iso_vertexFlow 2 qo τ = iso_adRinvPow 1 qo := by
    have h := iso_poincareMap_qFix _ hy0 hy1
    rw [iso_poincareMap, iso_poincareTime_qFix _ hy0 hy1] at h
    rw [← irt_adRinvPow_one_adR (iso_vertexFlow 2 qo τ)]
    exact congrArg (iso_adRinvPow 1) h
  set q₁ := iso_adRinvPow 1 qo with hq₁
  have hD1 : irt_Den q₁ := by rw [← hq1]; exact hDen τ ⟨hτ.le, le_rfl⟩
  have h32q : 0 < irt_chi 2 1 q₁ := by rw [← hq1]; exact h32O τ ⟨hτ.le, le_rfl⟩ hτ.ne'
  have hG : irt_G 2 0 q₁ < -(κ / 2) := by rw [← hq1, hG31]; linarith
  have h31q : irt_chi 2 0 q₁ = 0 := by rw [← hq1]; exact h31τ
  have hadR : iso_adR q₁ = qo := by
    obtain ⟨a, b, c⟩ := qo
    simp only [hq₁, iso_adRinvPow, iso_adR, pow_one, ← Matrix.mul_assoc, poly_R_mul_inv,
      Matrix.one_mul]
    simp only [Matrix.mul_assoc, poly_R_mul_inv, Matrix.mul_one]
  -- a neighbourhood of `q₁` where the strict inequalities hold
  have hadRc : Continuous iso_adR := by unfold iso_adR; fun_prop
  set N := {q | irt_Den q ∧ 0 < -(irt_G 2 0 q + κ / 2)} ∩ {q | irt_Den q ∧ 0 < irt_chi 2 1 q} ∩
    iso_adR ⁻¹' W' with hN
  have hNmem : N ∈ 𝓝 q₁ := by
    refine inter_mem (inter_mem ?_ ?_) (hadRc.continuousAt.preimage_mem_nhds (by rwa [hadR]))
    · exact (irt_isOpen_pos (f := fun q ↦ -(irt_G 2 0 q + κ / 2)) fun q hq ↦
        ((irt_G_continuousAt 2 0 hq).add continuousAt_const).neg).mem_nhds ⟨hD1, by linarith⟩
    · exact (irt_isOpen_pos fun q hq ↦ irt_chi_continuousAt 2 1 hq).mem_nhds ⟨hD1, h32q⟩
  have hflow0 : iso_vertexFlow 2 q₁ 0 = q₁ := ivf_vertexFlow_zero 2 q₁
  have hcont := irt_flow_continuousAt (hD1 2) 0
  have hpre : (fun x : iso_PhasePt × ℝ ↦ iso_vertexFlow 2 x.1 x.2) ⁻¹' N ∈ 𝓝 (q₁, 0) :=
    hcont.preimage_mem_nhds (by simp only; rw [hflow0]; exact hNmem)
  rw [nhds_prod_eq, Filter.mem_prod_iff] at hpre
  obtain ⟨U, hU, I, hI, hUI⟩ := hpre
  obtain ⟨ε, hε, hεI⟩ := Metric.mem_nhds_iff.1 hI
  set ε' := min (ε / 2) (δ / 2) with hε'
  have hε'0 : 0 < ε' := lt_min (by positivity) (by positivity)
  have hε'ε : ε' < ε := by have := min_le_left (ε / 2) (δ / 2); linarith
  have hε'δ : ε' < δ := by have := min_le_right (ε / 2) (δ / 2); linarith
  have hmem : ∀ p ∈ U, ∀ t ∈ Icc 0 ε', iso_vertexFlow 2 p t ∈ N := by
    intro p hp t ht
    have htb : t ∈ Metric.ball (0 : ℝ) ε := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
      constructor <;> linarith [ht.1, ht.2]
    have hx : ((p, t) : iso_PhasePt × ℝ) ∈ U ×ˢ I := ⟨hp, hεI htb⟩
    have h1 := hUI hx
    rw [mem_preimage] at h1
    exact h1
  have hsmall : ∀ᶠ p in 𝓝 q₁, irt_chi 2 0 p < κ / 2 * ε' :=
    (irt_chi_continuousAt 2 0 hD1).eventually (gt_mem_nhds (by rw [h31q]; positivity))
  refine ⟨_, inter_mem hU hsmall, ?_⟩
  rintro p ⟨hpU, hpsmall⟩ h31p
  set φ : ℝ → ℝ := fun t ↦ irt_chi 2 0 (iso_vertexFlow 2 p t) with hφ
  have hNp := hmem p hpU
  have hφd : ∀ t ∈ Icc 0 ε', HasDerivAt φ (irt_G 2 0 (iso_vertexFlow 2 p t)) t :=
    fun t ht ↦ irt_chi_flow_hasDerivAt 2 0 p t (hNp t ht).1.1.1
  have hφneg : ∀ t ∈ Icc 0 ε', irt_G 2 0 (iso_vertexFlow 2 p t) < -(κ / 2) :=
    fun t ht ↦ by have := (hNp t ht).1.1.2; linarith
  have hanti : StrictAntiOn φ (Icc 0 ε') :=
    irt_strictAntiOn hφd fun t ht ↦ by linarith [hφneg t ht]
  have hφc : ContinuousOn φ (Icc 0 ε') := fun t ht ↦ (hφd t ht).continuousAt.continuousWithinAt
  have hφ0 : φ 0 = irt_chi 2 0 p := by simp only [hφ, ivf_vertexFlow_zero]
  have hφe : φ ε' < 0 := by
    obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope φ (fun t ↦ irt_G 2 0 (iso_vertexFlow 2 p t))
      hε'0 hφc (fun t ht ↦ hφd t (Ioo_subset_Icc_self ht))
    have := hφneg c (Ioo_subset_Icc_self hc)
    rw [hc', sub_zero, div_lt_iff₀ hε'0] at this
    rw [hφ0] at this
    have hps : irt_chi 2 0 p < κ / 2 * ε' := hpsmall
    nlinarith
  obtain ⟨ts, hts, hφts⟩ := intermediate_value_Icc' hε'0.le hφc ⟨hφe.le, by rw [hφ0]; exact h31p.le⟩
  have hts1 : 0 < ts := lt_of_le_of_ne hts.1 fun h ↦ by
    rw [← h, hφ0] at hφts; linarith
  have hts2 : ts < ε' := lt_of_le_of_ne hts.2 fun h ↦ by rw [h] at hφts; linarith
  have hφpos : ∀ t ∈ Ico 0 ts, 0 < φ t := by
    intro t ht
    have := hanti ⟨ht.1, by linarith [ht.2]⟩ ⟨hts.1, hts.2⟩ ht.2
    rwa [hφts] at this
  have hτp : iso_poincareTime p = ts := by
    refine IsLeast.csInf_eq ⟨⟨hts1, hφts⟩, fun t ht ↦ ?_⟩
    by_contra hlt
    exact (hφpos t ⟨ht.1.le, lt_of_not_ge hlt⟩).ne' ht.2
  rw [iso_poincareMap, hτp]
  exact ⟨⟨hts1, by linarith⟩, hφpos, hφts,
    fun t ht ↦ (hNp t ⟨ht.1, by linarith [ht.2]⟩).1.2.2, (hNp ts ⟨hts.1, hts.2⟩).2⟩

/-- On traceless matrices, `iso_phaseOfCoords` inverts `iso_phaseCoords`. -/
lemma irt_ofCoords_coords {q : iso_PhasePt} (h1 : q.1.trace = 0) (h2 : q.2.1.trace = 0)
    (h3 : q.2.2.trace = 0) : iso_phaseOfCoords (iso_phaseCoords q) = q := by
  obtain ⟨A, B, C⟩ := q
  simp only [Matrix.trace_fin_two] at h1 h2 h3
  simp only [iso_phaseOfCoords, iso_phaseCoords, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp <;> linarith

lemma irt_continuous_phaseCoords : Continuous iso_phaseCoords := by
  unfold iso_phaseCoords
  refine continuous_pi fun i ↦ ?_
  fin_cases i <;> dsimp <;> fun_prop

lemma irt_continuous_phaseOfCoords : Continuous iso_phaseOfCoords := by
  unfold iso_phaseOfCoords
  refine Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_) <;>
    refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_ <;>
    fin_cases i <;> fin_cases j <;> dsimp <;> fun_prop

/-- The Poincaré map is continuous at `q_oct` on traceless points (from
`iso_poincareMapCoords_hasStrictFDerivAt`). -/
lemma irt_poincareMap_near (W' : Set iso_PhasePt) (hW' : W' ∈ 𝓝 (iso_qFix (y₀ 1))) :
    ∃ W ∈ 𝓝 (iso_qFix (y₀ 1)), ∀ p ∈ W, p.1.trace = 0 → p.2.1.trace = 0 → p.2.2.trace = 0 →
      iso_poincareMap p ∈ W' := by
  obtain ⟨hy0, hy1⟩ := poly_y₀_mem (le_refl 1)
  obtain ⟨k1, k2, k3, -⟩ := iso_qFix_isSectionPt _ hy0 hy1
  set v₀ := iso_phaseCoords (iso_qFix (y₀ 1)) with hv₀
  have hF : iso_poincareMapCoords v₀ = v₀ := by
    rw [iso_poincareMapCoords, irt_ofCoords_coords k1 k2 k3, iso_poincareMap_qFix _ hy0 hy1]
  have hFc : ContinuousAt iso_poincareMapCoords v₀ :=
    iso_poincareMapCoords_hasStrictFDerivAt.continuousAt
  have hmem : iso_phaseOfCoords ⁻¹' W' ∈ 𝓝 (iso_poincareMapCoords v₀) :=
    irt_continuous_phaseOfCoords.continuousAt.preimage_mem_nhds
      (by rw [hF, hv₀, irt_ofCoords_coords k1 k2 k3]; exact hW')
  refine ⟨iso_phaseCoords ⁻¹' (iso_poincareMapCoords ⁻¹' (iso_phaseOfCoords ⁻¹' W')),
    irt_continuous_phaseCoords.continuousAt.preimage_mem_nhds (hFc.preimage_mem_nhds hmem),
    fun p hp t1 t2 t3 ↦ ?_⟩
  simp only [mem_preimage, iso_poincareMapCoords, irt_ofCoords_coords t1 t2 t3] at hp
  obtain ⟨l1, l2, l3⟩ := irt_poincareMap_traceless t1 t2 t3
  rwa [irt_ofCoords_coords l1 l2 l3] at hp

/-- **Start-up on the switching surface** (no singular arc, no chattering): an extremal starting
on `χ₃₂ = 0` near `q_oct` uses the control `e₃` on an initial interval. -/
theorem irt_start_surface : ∃ W ∈ 𝓝 (iso_qFix (y₀ 1)),
    ∀ (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X Λ₁ ΛR : ℝ → Mat2),
      IsPontryaginExtremal T u g X Λ₁ ΛR (-1) → (X 0, Λ₁ 0, ΛR 0) ∈ W →
      irt_chi 2 1 (X 0, Λ₁ 0, ΛR 0) = 0 → ∃ η > 0, ∀ᵐ t, t ∈ Ioo 0 η → u t = vertex 2 := by
  obtain ⟨hy0, hy1⟩ := poly_y₀_mem (le_refl 1)
  have hτ : 0 < tsw 1 := poly_switchTime_pos hy0 hy1
  obtain ⟨-, h31O, -, -, -, hG32⟩ := irt_oct_facts
  have hO0 : iso_vertexFlow 2 (iso_qFix (y₀ 1)) 0 = iso_qFix (y₀ 1) := ivf_vertexFlow_zero _ _
  rw [hO0] at hG32
  have h31q : 0 < irt_chi 2 0 (iso_qFix (y₀ 1)) := by
    have := h31O 0 ⟨le_rfl, hτ.le⟩ hτ.ne; rwa [hO0] at this
  have h32q : irt_chi 2 1 (iso_qFix (y₀ 1)) = 0 := by
    have h23 : switchingFn 1 2 (iso_qFix (y₀ 1)).2.2 (iso_qFix (y₀ 1)).1 = 0 :=
      (iso_qFix_isSectionPt _ hy0 hy1).2.2.2.2.2.2
    rw [irt_chi_antisymm]; change -switchingFn 1 2 _ _ = 0; rw [h23, neg_zero]
  have h21 : ∀ q, irt_chi 1 0 q = irt_chi 2 0 q - irt_chi 2 1 q := by
    intro q; simp only [irt_chi, switchingFn, traceForm, Matrix.mul_sub, Matrix.trace_sub]; ring
  have hκo := iso_chi32Slope_pos _ hy0 hy1
  refine ⟨{q | irt_Den q ∧ 0 < irt_G 2 1 q} ∩ {q | irt_Den q ∧ 0 < irt_chi 2 0 q} ∩
    {q | irt_Den q ∧ 0 < irt_chi 1 0 q}, inter_mem (inter_mem ?_ ?_) ?_, ?_⟩
  · exact (irt_isOpen_pos fun q hq ↦ irt_G_continuousAt 2 1 hq).mem_nhds
      ⟨irt_Den_qFix, by rw [hG32]; exact hκo⟩
  · exact (irt_isOpen_pos fun q hq ↦ irt_chi_continuousAt 2 0 hq).mem_nhds ⟨irt_Den_qFix, h31q⟩
  · exact (irt_isOpen_pos fun q hq ↦ irt_chi_continuousAt 1 0 hq).mem_nhds
      ⟨irt_Den_qFix, by rw [h21, h32q, sub_zero]; exact h31q⟩
  rintro T u g X Λ₁ ΛR h ⟨⟨⟨hD, hκp⟩, ⟨-, h31p⟩⟩, ⟨-, h21p⟩⟩ h32p
  set p : iso_PhasePt := (X 0, Λ₁ 0, ΛR 0) with hp
  have hT : 0 < T := h.1.1
  obtain ⟨⟨-, -, husim, hst, -, hXI⟩, -, -, -, -, -, -, hpt, -, hIR, hmax⟩ := id h
  have hstar0 : IsStarState p.1 := (hst 0 ⟨le_rfl, hT.le⟩).2
  have htrR : p.2.2.trace = 0 := (hpt 0 ⟨le_rfl, hT.le⟩).2.1
  have h23p : switchingFn 1 2 p.2.2 p.1 = 0 := by
    have := irt_chi_antisymm 1 2 p; rw [h32p, neg_zero] at this; exact this
  set κ := irt_G 2 1 p with hκ
  -- the vertices `e₂, e₃` and the values at `t = 0`
  set Z1 := controlMatrix (vertex 1) with hZ1
  set Z2 := controlMatrix (vertex 2) with hZ2
  set F : iso_PhasePt → (Fin 3 → ℝ) → iso_PhasePt := fun q w ↦ iso_extremalField w q with hF
  -- linear functionals of the field
  set ℓ : iso_PhasePt → ℝ := fun V ↦ irt_dsw 2 1 p.2.2 p.1 V.2.2 V.1 with hℓ
  have hℓc : Continuous ℓ := by
    simp only [hℓ, irt_dsw, traceForm]; fun_prop
  set m : iso_PhasePt → ℝ := fun V ↦ |traceForm V.2.2 Z1| + |traceForm Z1 V.1| +
    |traceForm V.2.2 Z2| + |traceForm Z2 V.1| with hm
  have hmc : Continuous m := by simp only [hm, traceForm]; fun_prop
  have hFc : ∀ w ∈ controlSimplex, ContinuousAt
      (fun x : iso_PhasePt × (Fin 3 → ℝ) ↦ F x.1 x.2) (p, w) := fun w hw ↦
    irt_field_continuousAt (poly_traceForm_neg hw hstar0).ne
  -- the bound of the field near `p`, uniformly on `U_T`
  obtain ⟨M, hM⟩ := irt_isCompact_simplex.bddAbove_image (f := fun w ↦ m (F p w))
    (fun w hw ↦ (hmc.continuousAt.comp ((hFc w hw).comp (continuousAt_const.prodMk
      continuousAt_id))).continuousWithinAt)
  have hEm := irt_tube_u irt_isCompact_simplex (f := fun q w ↦ m (F q w)) (p := p)
    (fun w hw ↦ hmc.continuousAt.comp (hFc w hw)) (r := M + 1)
    fun w hw ↦ by have := hM ⟨w, hw, rfl⟩; simp only at this ⊢; linarith
  -- the derivative of `χ₃₂` along the field of an edge control, near `p`
  have hedge : IsCompact {w ∈ controlSimplex | w 0 = 0} :=
    irt_isCompact_simplex.inter_right (isClosed_eq (continuous_apply 0) continuous_const)
  have hEl := irt_tube_u hedge (f := fun q w ↦ -ℓ (F q w)) (p := p)
    (fun w hw ↦ hℓc.continuousAt.neg.comp (hFc w hw.1)) (r := -(κ / 2)) fun w hw ↦ by
      simp only [hℓ, hF]
      rw [irt_edge_dsw hstar0 h23p hw.1 hw.2]
      linarith
  -- `χ₃₁ > 0`, `χ₂₁ > 0` near `p`
  have hEc : ∀ᶠ q in 𝓝 p, irt_Den q ∧ 0 < irt_chi 2 0 q ∧ 0 < irt_chi 1 0 q := by
    filter_upwards [(irt_isOpen_pos (f := irt_chi 2 0) fun q hq ↦
        irt_chi_continuousAt 2 0 hq).mem_nhds ⟨hD, h31p⟩,
      (irt_isOpen_pos (f := irt_chi 1 0) fun q hq ↦
        irt_chi_continuousAt 1 0 hq).mem_nhds ⟨hD, h21p⟩] with q ha hb
    exact ⟨ha.1, ha.2, hb.2⟩
  -- along the extremal, for small times
  have hqc := irt_q_continuousOn h 0 ⟨le_rfl, hT.le⟩
  obtain ⟨η₀, hη₀, hball⟩ := Metric.mem_nhdsWithin_iff.1 (hqc.eventually (hEm.and (hEl.and hEc)))
  set η₁ := min (η₀ / 2) T with hη₁
  have hη₁0 : 0 < η₁ := lt_min (by positivity) hT
  have hgood : ∀ s ∈ Icc 0 η₁, (∀ w ∈ controlSimplex, m (F (X s, Λ₁ s, ΛR s) w) < M + 1) ∧
      (∀ w ∈ {w ∈ controlSimplex | w 0 = 0}, -ℓ (F (X s, Λ₁ s, ΛR s) w) < -(κ / 2)) ∧
      irt_Den (X s, Λ₁ s, ΛR s) ∧ 0 < irt_chi 2 0 (X s, Λ₁ s, ΛR s) ∧
        0 < irt_chi 1 0 (X s, Λ₁ s, ΛR s) := by
    intro s hs
    have hsT : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans (min_le_right _ _)⟩
    have hsb : s ∈ Metric.ball (0 : ℝ) η₀ := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
      constructor <;> linarith [hs.1, hs.2, min_le_left (η₀ / 2) T]
    exact hball ⟨hsb, hsT⟩
  -- the scalar functions
  set A1 := traceForm p.2.2 Z1 with hA1
  set B1 := traceForm Z1 p.1 with hB1
  set A2 := traceForm p.2.2 Z2 with hA2
  set B2 := traceForm Z2 p.1 with hB2
  set V : ℝ → iso_PhasePt := fun s ↦ F (X s, Λ₁ s, ΛR s) (u s) with hV
  have hB1ne : B1 ≠ 0 := hD 1
  have hB2ne : B2 ≠ 0 := hD 2
  have hXv : ∀ i j, IntervalIntegrable (fun s ↦ (V s).1 i j) volume 0 η₁ := fun i j ↦
    (hXI i j).1.mono_set (by
      rw [uIcc_of_le hη₁0.le, uIcc_of_le hT.le]; exact Icc_subset_Icc_right (min_le_right _ _))
  have hRv : ∀ i j, IntervalIntegrable (fun s ↦ (V s).2.2 i j) volume 0 η₁ := fun i j ↦
    (hIR i j).1.mono_set (by
      rw [uIcc_of_le hη₁0.le, uIcc_of_le hT.le]; exact Icc_subset_Icc_right (min_le_right _ _))
  have hbnd : ∀ s ∈ Icc 0 η₁, |traceForm (V s).2.2 Z1| ≤ M + 1 ∧ |traceForm Z1 (V s).1| ≤ M + 1 ∧
      |traceForm (V s).2.2 Z2| ≤ M + 1 ∧ |traceForm Z2 (V s).1| ≤ M + 1 := by
    intro s hs
    have hsT : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans (min_le_right _ _)⟩
    have h := ((hgood s hs).1 (u s) (husim s hsT)).le
    simp only [hm] at h
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [abs_nonneg (traceForm (V s).2.2 Z1),
      abs_nonneg (traceForm Z1 (V s).1), abs_nonneg (traceForm (V s).2.2 Z2),
      abs_nonneg (traceForm Z2 (V s).1)]
  have hℓs : ∀ᵐ s, s ∈ Ioo 0 η₁ → κ / 2 ≤
      (traceForm (V s).2.2 Z1 * B1 - A1 * traceForm Z1 (V s).1) / B1 ^ 2 -
        (traceForm (V s).2.2 Z2 * B2 - A2 * traceForm Z2 (V s).1) / B2 ^ 2 := by
    filter_upwards [hmax] with s hs hsI
    have hsη : s ∈ Icc 0 η₁ := Ioo_subset_Icc_self hsI
    have hsT : s ∈ Ioo 0 T := ⟨hsI.1, hsI.2.trans_le (min_le_right _ _)⟩
    obtain ⟨-, -, -, h31s, h21s⟩ := hgood s hsη
    obtain ⟨-, hle⟩ := hs hsT
    have hstar := (hst s (Ioo_subset_Icc_self hsT)).2
    have hu := husim s (Ioo_subset_Icc_self hsT)
    -- the maximizing control lies on the edge `[e₂, e₃]`
    have hsub20 := poly_hamiltonian_sub (-1) (Λ₁ s) (ΛR s) (X s) 2 0
    have hsub10 := poly_hamiltonian_sub (-1) (Λ₁ s) (ΛR s) (X s) 1 0
    have hsub21 := poly_hamiltonian_sub (-1) (Λ₁ s) (ΛR s) (X s) 2 1
    have e20 : 0 < switchingFn 2 0 (ΛR s) (X s) := h31s
    have e10 : 0 < switchingFn 1 0 (ΛR s) (X s) := h21s
    have hu0 : u s 0 = 0 := by
      rcases le_or_gt 0 (switchingFn 2 1 (ΛR s) (X s)) with h32s | h32s
      · refine irt_eq_zero_of_max hstar (m := 2) (fun i ↦ ?_) (by linarith) hu
          (hle _ (poly_vertex_mem 2))
        fin_cases i <;> simp <;> linarith
      · refine irt_eq_zero_of_max hstar (m := 1) (fun i ↦ ?_) (by linarith) hu
          (hle _ (poly_vertex_mem 1))
        fin_cases i <;> simp <;> linarith
    have hl := (hgood s hsη).2.1 (u s) ⟨hu, hu0⟩
    simp only [hℓ, hF] at hl
    rw [irt_dsw_eq _ _ _ _ hB1ne hB2ne] at hl
    simp only [hV, hF]
    linarith
  have hκ2 : 0 < κ / 2 := by positivity
  have h00 : A1 / B1 - A2 / B2 = 0 := by
    have := str_switchingFn_eq 2 1 p.2.2 p.1
    rw [← this]; exact h32p
  have hM0 : 0 ≤ M + 1 := by
    have h1 := hM ⟨vertex 2, poly_vertex_mem 2, rfl⟩
    have h2 : 0 ≤ m (F p (vertex 2)) := by simp only [hm]; positivity
    simp only at h1
    linarith
  obtain ⟨η, hη, hηη₁, hpos⟩ := irt_quot_pos hB1ne hB2ne h00 hκ2 hη₁0 hM0
    (irt_traceForm_intervalIntegrable hRv Z1).1 (irt_traceForm_intervalIntegrable hXv Z1).2
    (irt_traceForm_intervalIntegrable hRv Z2).1 (irt_traceForm_intervalIntegrable hXv Z2).2
    hbnd hℓs
  refine ⟨η, hη, ?_⟩
  filter_upwards [hmax] with t ht htη
  have htη₁ : t ∈ Icc 0 η₁ := ⟨htη.1.le, htη.2.le.trans hηη₁⟩
  have htT : t ∈ Icc 0 T := ⟨htη.1.le, htη₁.2.trans (min_le_right _ _)⟩
  have htT' : t ∈ Ioo 0 T := ⟨htη.1, htη.2.trans_le (hηη₁.trans (min_le_right _ _))⟩
  obtain ⟨-, -, -, h31t, -⟩ := hgood t htη₁
  -- `χ₃₂ > 0` at `t`
  have h32t : 0 < switchingFn 2 1 (ΛR t) (X t) := by
    have hR1 := (irt_traceForm_integral hIR Z1 htT).1
    have hX1 := (irt_traceForm_integral hXI Z1 htT).2
    have hR2 := (irt_traceForm_integral hIR Z2 htT).1
    have hX2 := (irt_traceForm_integral hXI Z2 htT).2
    rw [str_switchingFn_eq, hR1, hX1, hR2, hX2]
    exact hpos t htη
  obtain ⟨-, hle⟩ := ht htT'
  refine irt_eq_vertex_of_max (hst t htT).2 (fun j hj ↦ ?_) (husim t htT)
    (hle _ (poly_vertex_mem 2))
  have hsub := poly_hamiltonian_sub (-1) (Λ₁ t) (ΛR t) (X t) 2 j
  have hlt : j.val ≠ 2 := fun h' ↦ hj (Fin.ext h')
  have hj' := j.isLt
  rcases (by omega : j.val = 0 ∨ j.val = 1) with h0 | h0
  · rw [show j = 0 from Fin.ext h0] at hsub ⊢
    have : 0 < switchingFn 2 0 (ΛR t) (X t) := h31t
    linarith
  · rw [show j = 1 from Fin.ext h0] at hsub ⊢
    linarith

/-! ### One arc -/

/-- **One arc.** An extremal that is, at a time `s < T`, at the conjugate `R⁻ⁱ p Rⁱ` of a point
`p` near `q_oct` with `χ₃₂(p) ≥ 0`, follows the conjugated `e₃`-flow from `p` up to the Poincaré
time of `p` (or up to `T`). -/
lemma irt_one_arc (δ : ℝ) (hδ : 0 < δ) : ∃ W ∈ 𝓝 (iso_qFix (y₀ 1)), ∀ p ∈ W,
    0 ≤ irt_chi 2 1 p →
      iso_poincareTime p ∈ Ioo (tsw 1 - δ) (tsw 1 + δ) ∧
      (∀ t ∈ Ico 0 (iso_poincareTime p), 0 < irt_chi 2 0 (iso_vertexFlow 2 p t)) ∧
      irt_chi 2 0 (iso_vertexFlow 2 p (iso_poincareTime p)) = 0 ∧
      (∀ t ∈ Ioc 0 (iso_poincareTime p), 0 < irt_chi 2 1 (iso_vertexFlow 2 p t)) ∧
      ∀ (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X Λ₁ ΛR : ℝ → Mat2),
        IsPontryaginExtremal T u g X Λ₁ ΛR (-1) → ∀ s ∈ Ico 0 T, ∀ i : ℕ,
        (X s, Λ₁ s, ΛR s) = iso_adRinvPow i p →
        ∀ t ∈ Icc 0 (min (T - s) (iso_poincareTime p)),
          (X (s + t), Λ₁ (s + t), ΛR (s + t)) = iso_adRinvPow i (iso_vertexFlow 2 p t) := by
  obtain ⟨hy0, hy1⟩ := poly_y₀_mem (le_refl 1)
  have hτ₀ : 0 < tsw 1 := poly_switchTime_pos hy0 hy1
  obtain ⟨W₀, hW₀, hW₀p⟩ := irt_flow_start (min δ (tsw 1 / 2)) (lt_min hδ (by positivity))
  obtain ⟨Ws, hWs, hWsp⟩ := irt_start_surface
  refine ⟨W₀ ∩ Ws, inter_mem hW₀ hWs, fun p hp h32 ↦ ?_⟩
  obtain ⟨hτ, h31, h31z, h32'⟩ := hW₀p p hp.1 h32
  have hm1 := min_le_left δ (tsw 1 / 2)
  have hm2 := min_le_right δ (tsw 1 / 2)
  have hτpos : 0 < iso_poincareTime p := by linarith [hτ.1]
  refine ⟨⟨by linarith [hτ.1], by linarith [hτ.2]⟩, h31, h31z, h32', ?_⟩
  intro T u g X Λ₁ ΛR h s hs i hEs t ht
  obtain ⟨u', g', X', Λ₁', ΛR', h', hE'⟩ := irt_restart h hs (2 * i)
  have hE'0 : (X' 0, Λ₁' 0, ΛR' 0) = p := by
    have := hE' 0 ⟨le_rfl, by linarith [hs.2]⟩
    rw [add_zero, hEs, irt_adRinvPow_add, show 2 * i + i = 3 * i by ring,
      irt_adRinvPow_three_mul] at this
    exact this
  have h31' : ∀ t ∈ Ico 0 (iso_poincareTime p),
      0 < irt_chi 2 0 (iso_vertexFlow 2 (X' 0, Λ₁' 0, ΛR' 0) t) := by rw [hE'0]; exact h31
  have h32'' : ∀ t ∈ Ioc 0 (iso_poincareTime p),
      0 < irt_chi 2 1 (iso_vertexFlow 2 (X' 0, Λ₁' 0, ΛR' 0) t) := by rw [hE'0]; exact h32'
  have hstart : ∃ η > 0, ∀ᵐ t, t ∈ Ioo 0 η → u' t = vertex 2 := by
    rcases h32.lt_or_eq with hlt | heq
    · have h31p := h31 0 ⟨le_rfl, hτpos⟩
      rw [ivf_vertexFlow_zero] at h31p
      exact irt_start_strict h' (by rw [hE'0]; exact h31p) (by rw [hE'0]; exact hlt)
    · exact hWsp T u' g' X' Λ₁' ΛR' h' (by rw [hE'0]; exact hp.2) (by rw [hE'0]; exact heq.symm)
  have hT : s ≤ T := hs.2.le
  have hta := irt_arc h' hτpos h31' h32'' hstart t
    ⟨ht.1, le_min ((ht.2.trans (min_le_left _ _)).trans (by linarith [hs.1]))
      (ht.2.trans (min_le_right _ _))⟩
  rw [hE'0] at hta
  have htb := hE' t ⟨ht.1, ht.2.trans (min_le_left _ _)⟩
  rw [hta] at htb
  have := congrArg (iso_adRinvPow i) htb
  rw [irt_adRinvPow_add, show i + 2 * i = 3 * i by ring, irt_adRinvPow_three_mul] at this
  exact this.symm

/-! ### Step 3: the switching structure of nearby extremals -/

/-- An extremal whose initial condition is near the octagon's and whose terminal time is near
`t_f` crosses the section `χ₂₃ = 0` near `t = 0` or near `t = 3t_sw`: some restart of its
twisted-periodic continuation starts on the section, as close to `q_oct` as wanted. (Transversal
crossing by `iso_chi32_hasDerivAt`; the step the book omits.) If `χ₃₂(q(0)) = 0` the restart is
at `0`; if `χ₃₂(q(0)) < 0`, `R⁻¹ q(0) R` is near the end `O(t_sw)` of the octagon's first arc and
the extremal reaches the section after a short time (`irt_flow_end`); if `χ₃₂(q(0)) > 0` it
follows three arcs (`irt_one_arc`) and reaches the section at `t₃ ≈ 3t_sw`. -/
theorem iso_section_crossing (V : Set iso_PhasePt) (hV : V ∈ 𝓝 (iso_qFix (y₀ 1))) :
    ∃ U ∈ 𝓝 (iso_qFix (y₀ 1)), ∃ ε > 0, ∀ (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X Λ₁ ΛR : ℝ → Mat2),
      IsPontryaginExtremal T u g X Λ₁ ΛR (-1) → |T - tf 1| < ε → (X 0, Λ₁ 0, ΛR 0) ∈ U →
      ∃ s ∈ Ico 0 T,
        (poly_pw R⁻¹ R T X s, poly_pw R⁻¹ R T Λ₁ s, poly_pw R⁻¹ R T ΛR s) ∈ V ∧
          iso_IsSectionPt (poly_pw R⁻¹ R T X s, poly_pw R⁻¹ R T Λ₁ s, poly_pw R⁻¹ R T ΛR s) := by
  obtain ⟨hy0, hy1⟩ := poly_y₀_mem (le_refl 1)
  set τ₀ := tsw 1 with hτ₀def
  have hτ₀ : 0 < τ₀ := poly_switchTime_pos hy0 hy1
  set δ := τ₀ / 20 with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨W, hW, hWp⟩ := irt_one_arc δ hδ
  have hstep : ∀ W' ∈ 𝓝 (iso_qFix (y₀ 1)), ∃ W'' ∈ 𝓝 (iso_qFix (y₀ 1)), W'' ⊆ W ∧
      ∀ p ∈ W'', p.1.trace = 0 → p.2.1.trace = 0 → p.2.2.trace = 0 → iso_poincareMap p ∈ W' := by
    intro W' hW'
    obtain ⟨W'', hW'', h⟩ := irt_poincareMap_near W' hW'
    exact ⟨W'' ∩ W, inter_mem hW'' hW, inter_subset_right, fun p hp ↦ h p hp.1⟩
  have hVW : V ∩ W ∈ 𝓝 (iso_qFix (y₀ 1)) := inter_mem hV hW
  obtain ⟨V2, hV2, hV2W, hf2⟩ := hstep (V ∩ W) hVW
  obtain ⟨V1, hV1, hV1W, hf1⟩ := hstep V2 hV2
  obtain ⟨V0, hV0, hV0W, hf0⟩ := hstep V1 hV1
  obtain ⟨We, hWe, hWep⟩ := irt_flow_end (V ∩ W) hVW δ hδ
  have hUe : iso_adRinvPow 1 ⁻¹' We ∈ 𝓝 (iso_qFix (y₀ 1)) :=
    (irt_continuous_adRinvPow 1).continuousAt.preimage_mem_nhds hWe
  refine ⟨V ∩ V0 ∩ iso_adRinvPow 1 ⁻¹' We, inter_mem (inter_mem hV hV0) hUe, δ, hδ, ?_⟩
  intro T u g X Λ₁ ΛR h hT ⟨⟨hq0V, hq0V0⟩, hq0e⟩
  set q₀ : iso_PhasePt := (X 0, Λ₁ 0, ΛR 0) with hq₀
  set E : ℝ → iso_PhasePt := fun t ↦ (X t, Λ₁ t, ΛR t) with hE
  have hTb : 4 * τ₀ - δ < T ∧ T < 4 * τ₀ + δ := by
    have htf : tf 1 = 4 * τ₀ := by rw [tf, hτ₀def]; norm_num
    rw [htf] at hT
    have := abs_lt.1 hT
    constructor <;> linarith [this.1, this.2]
  have hTpos : 0 < T := by linarith
  -- the restart point, on `[0, T)`
  have hpw : ∀ s ∈ Ico 0 T, (poly_pw R⁻¹ R T X s, poly_pw R⁻¹ R T Λ₁ s, poly_pw R⁻¹ R T ΛR s) =
      E s := by
    intro s hs
    have hfl : ⌊s / T⌋₊ = 0 := Nat.floor_eq_zero.2 ((div_lt_one hTpos).2 hs.2)
    simp [hE, poly_pw, hfl]
  have htr0 : q₀.1.trace = 0 ∧ q₀.2.1.trace = 0 ∧ q₀.2.2.trace = 0 := by
    obtain ⟨⟨-, -, -, hst, -, -⟩, -, -, -, -, -, -, hpt, -⟩ := h
    exact ⟨(hst 0 ⟨le_rfl, hTpos.le⟩).2.1, (hpt 0 ⟨le_rfl, hTpos.le⟩).1,
      (hpt 0 ⟨le_rfl, hTpos.le⟩).2.1⟩
  -- landing on the section: `χ₂₃ = 0` after the Poincaré map
  have hland : ∀ q : iso_PhasePt,
      irt_chi 2 0 (iso_vertexFlow 2 q (iso_poincareTime q)) = 0 →
      irt_chi 1 2 (iso_poincareMap q) = 0 := by
    intro q h0
    have hc := irt_chi_conj 1 1 2 (iso_poincareMap q)
    rw [iso_poincareMap, irt_adRinvPow_one_adR] at hc
    rw [iso_poincareMap, ← hc]
    simpa using h0
  -- a point of `W` on the section has `χ₃₁ > 0`
  have h31W : ∀ q ∈ W, irt_chi 1 2 q = 0 → 0 < irt_chi 2 0 q := by
    intro q hq h0
    have h32 : 0 ≤ irt_chi 2 1 q := by rw [irt_chi_antisymm, h0, neg_zero]
    have := (hWp q hq h32).2.1 0 ⟨le_rfl, (hWp q hq h32).1.1.trans' (by linarith)⟩
    rwa [ivf_vertexFlow_zero] at this
  rcases lt_trichotomy (irt_chi 2 1 q₀) 0 with hneg | hzero | hpos
  · -- the extremal is just before the section: conjugate and run to the end of an `e₃`-arc
    obtain ⟨u', g', X', Λ₁', ΛR', h', hE'⟩ := irt_restart h ⟨le_rfl, hTpos⟩ 1
    set p' : iso_PhasePt := iso_adRinvPow 1 q₀ with hp'
    have hp'0 : (X' 0, Λ₁' 0, ΛR' 0) = p' := by
      simpa using hE' 0 ⟨le_rfl, by linarith⟩
    have h31p : 0 < irt_chi 2 0 p' := by
      have hc := irt_chi_conj 1 1 2 q₀
      rw [show (1 : Fin 3) + ⟨1 % 3, Nat.mod_lt _ (by norm_num)⟩ = 2 from rfl,
        show (2 : Fin 3) + ⟨1 % 3, Nat.mod_lt _ (by norm_num)⟩ = 0 from rfl] at hc
      rw [hc, irt_chi_antisymm]
      linarith
    obtain ⟨hτ', h31', h31z', h32', hfW⟩ := hWep p' hq0e h31p
    have h32p : 0 < irt_chi 2 1 p' := by
      have := h32' 0 ⟨le_rfl, hτ'.1.le⟩
      rwa [ivf_vertexFlow_zero] at this
    rw [← hp'0] at h31p h32p h31' h31z' h32' hτ' hfW
    have harc := irt_arc h' hτ'.1 h31' (fun t ht ↦ h32' t (Ioc_subset_Icc_self ht))
      (irt_start_strict h' h31p h32p)
    set q'0 : iso_PhasePt := (X' 0, Λ₁' 0, ΛR' 0) with hq'0
    set τ' := iso_poincareTime q'0 with hτ'def
    have hτ'T : τ' < T := by linarith [hτ'.2]
    have hEτ : E τ' = iso_poincareMap q'0 := by
      have h1 := harc τ' ⟨hτ'.1.le, le_min hτ'T.le le_rfl⟩
      have h2 := hE' τ' ⟨hτ'.1.le, by linarith⟩
      rw [zero_add] at h2
      refine irt_adRinvPow_injective 1 ?_
      change iso_adRinvPow 1 (X τ', Λ₁ τ', ΛR τ') = _
      rw [← h2, h1, iso_poincareMap, irt_adRinvPow_one_adR]
    refine ⟨τ', ⟨hτ'.1.le, hτ'T⟩, ?_⟩
    rw [hpw τ' ⟨hτ'.1.le, hτ'T⟩, hEτ]
    refine ⟨hfW.1, ?_⟩
    rw [← hEτ]
    have h23 : irt_chi 1 2 (E τ') = 0 := by rw [hEτ]; exact hland _ h31z'
    have hEW : E τ' ∈ W := by rw [hEτ]; exact hfW.2
    exact irt_isSectionPt h ⟨hτ'.1.le, hτ'T.le⟩ h23 (h31W _ hEW h23)
  · -- the extremal starts on the section
    refine ⟨0, ⟨le_rfl, hTpos⟩, ?_⟩
    rw [hpw 0 ⟨le_rfl, hTpos⟩]
    have h23 : irt_chi 1 2 (E 0) = 0 := by
      rw [irt_chi_antisymm]; simp only [hE]; rw [← hq₀, hzero, neg_zero]
    exact ⟨hq0V, irt_isSectionPt h ⟨le_rfl, hTpos.le⟩ h23 (h31W _ (hV0W hq0V0) h23)⟩
  · -- the extremal is just after the section: it returns to it after three arcs
    have hnext : ∀ (s : ℝ) (i : ℕ) (q : iso_PhasePt), q ∈ W → 0 ≤ irt_chi 2 1 q →
        s ∈ Ico 0 T → E s = iso_adRinvPow i q → s + iso_poincareTime q ≤ T →
        E (s + iso_poincareTime q) = iso_adRinvPow (i + 1) (iso_poincareMap q) ∧
          irt_chi 1 2 (iso_poincareMap q) = 0 ∧
          iso_poincareTime q ∈ Ioo (tsw 1 - δ) (tsw 1 + δ) := by
      intro s i q hq h32 hs hEs hle
      obtain ⟨hτq, -, h31z, -, harcq⟩ := hWp q hq h32
      have h := harcq T u g X Λ₁ ΛR h s hs i hEs (iso_poincareTime q)
        ⟨by linarith [hτq.1], le_min (by linarith) le_rfl⟩
      refine ⟨?_, hland q h31z, hτq⟩
      change E _ = _ at h
      rw [h, iso_poincareMap]
      conv_lhs => rw [← irt_adRinvPow_one_adR (iso_vertexFlow 2 q (iso_poincareTime q))]
      rw [irt_adRinvPow_add]
    have hχ0 : ∀ q, irt_chi 1 2 q = 0 → 0 ≤ irt_chi 2 1 q := fun q h0 ↦ by
      rw [irt_chi_antisymm, h0, neg_zero]
    obtain ⟨k1, k2, k3⟩ := htr0
    have hp0W : q₀ ∈ W := hV0W hq0V0
    have hE0 : E 0 = iso_adRinvPow 0 q₀ := (irt_adRinvPow_zero q₀).symm
    obtain ⟨hτ0a, -⟩ := (hWp q₀ hp0W hpos.le).1
    have hτ0 := (hWp q₀ hp0W hpos.le).1
    set t1 := 0 + iso_poincareTime q₀ with ht1
    obtain ⟨hE1, h231, -⟩ := hnext 0 0 q₀ hp0W hpos.le ⟨le_rfl, hTpos⟩ hE0
      (by rw [zero_add]; linarith [hτ0.2])
    set p1 := iso_poincareMap q₀ with hp1
    have hp1V : p1 ∈ V1 := hf0 q₀ hq0V0 k1 k2 k3
    obtain ⟨l1, l2, l3⟩ := irt_poincareMap_traceless k1 k2 k3
    have hτ1 := (hWp p1 (hV1W hp1V) (hχ0 _ h231)).1
    obtain ⟨hE2, h232, -⟩ := hnext t1 1 p1 (hV1W hp1V) (hχ0 _ h231)
      ⟨by rw [ht1]; linarith [hτ0.1], by rw [ht1]; linarith [hτ0.2]⟩ hE1
      (by rw [ht1]; linarith [hτ0.2, hτ1.2])
    set t2 := t1 + iso_poincareTime p1 with ht2
    set p2 := iso_poincareMap p1 with hp2
    have hp2V : p2 ∈ V2 := hf1 p1 hp1V l1 l2 l3
    obtain ⟨m1, m2, m3⟩ := irt_poincareMap_traceless l1 l2 l3
    have hτ2 := (hWp p2 (hV2W hp2V) (hχ0 _ h232)).1
    obtain ⟨hE3, h233, -⟩ := hnext t2 2 p2 (hV2W hp2V) (hχ0 _ h232)
      ⟨by rw [ht2, ht1]; linarith [hτ0.1, hτ1.1], by rw [ht2, ht1]; linarith [hτ0.2, hτ1.2]⟩
      hE2 (by rw [ht2, ht1]; linarith [hτ0.2, hτ1.2, hτ2.2])
    set t3 := t2 + iso_poincareTime p2 with ht3
    set p3 := iso_poincareMap p2 with hp3
    have hp3V : p3 ∈ V ∩ W := hf2 p2 hp2V m1 m2 m3
    have ht3T : t3 ∈ Ico 0 T := ⟨by rw [ht3, ht2, ht1]; linarith [hτ0.1, hτ1.1, hτ2.1],
      by rw [ht3, ht2, ht1]; linarith [hτ0.2, hτ1.2, hτ2.2]⟩
    rw [irt_adRinvPow_mod, show (2 + 1) % 3 = 0 from rfl, irt_adRinvPow_zero] at hE3
    refine ⟨t3, ht3T, ?_⟩
    rw [hpw t3 ht3T, hE3]
    refine ⟨hp3V.1, ?_⟩
    rw [← hE3]
    have hEW : E t3 ∈ W := by rw [hE3]; exact hp3V.2
    have h23 : irt_chi 1 2 (E t3) = 0 := by rw [hE3]; exact h233
    exact irt_isSectionPt h (Ico_subset_Icc_self ht3T) h23 (h31W _ hEW h23)

/-- The return map (eqn:fp): a normalized extremal starting on the section near `q_oct`, with
terminal time near `t_f`, is the concatenation of four vertex arcs `e₃, e₁, e₂, e₃` whose
switching times are given by the Poincaré time, `T = t₄`, and `f⁴ q₀ = q₀`. This is where the
strict inequalities of Lemma 7.5.3 (away from the switching times), `iso_chi32_hasDerivAt` and
`iso_edge_slope` (near them), and uniqueness for the extremal dynamics with a vertex control
enter: they show that the extremal is bang-bang with the octagon's switching sequence
(`irt_one_arc`, arc by arc). -/
theorem iso_return :
    ∃ V ∈ 𝓝 (iso_qFix (y₀ 1)), ∃ ε > 0, ∀ (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X Λ₁ ΛR : ℝ → Mat2),
      IsPontryaginExtremal T u g X Λ₁ ΛR (-1) → |T - tf 1| < ε → (X 0, Λ₁ 0, ΛR 0) ∈ V →
      iso_IsSectionPt (X 0, Λ₁ 0, ΛR 0) →
      iso_poincareMap^[4] (X 0, Λ₁ 0, ΛR 0) = (X 0, Λ₁ 0, ΛR 0) ∧
        T = iso_poincareSwitchTimes (X 0, Λ₁ 0, ΛR 0) 4 ∧
        ∀ i < 4, ∀ t ∈ Icc (iso_poincareSwitchTimes (X 0, Λ₁ 0, ΛR 0) i)
            (iso_poincareSwitchTimes (X 0, Λ₁ 0, ΛR 0) (i + 1)),
          (X t, Λ₁ t, ΛR t) = iso_adRinvPow i
            (iso_vertexFlow 2 (iso_poincareMap^[i] (X 0, Λ₁ 0, ΛR 0))
              (t - iso_poincareSwitchTimes (X 0, Λ₁ 0, ΛR 0) i)) := by
  obtain ⟨hy0, hy1⟩ := poly_y₀_mem (le_refl 1)
  set τ₀ := tsw 1 with hτ₀def
  have hτ₀ : 0 < τ₀ := poly_switchTime_pos hy0 hy1
  set δ := τ₀ / 20 with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨W, hW, hWp⟩ := irt_one_arc δ hδ
  have hstep : ∀ W' ∈ 𝓝 (iso_qFix (y₀ 1)), ∃ W'' ∈ 𝓝 (iso_qFix (y₀ 1)), W'' ⊆ W ∧
      ∀ p ∈ W'', p.1.trace = 0 → p.2.1.trace = 0 → p.2.2.trace = 0 → iso_poincareMap p ∈ W' := by
    intro W' hW'
    obtain ⟨W'', hW'', h⟩ := irt_poincareMap_near W' hW'
    exact ⟨W'' ∩ W, inter_mem hW'' hW, inter_subset_right, fun p hp ↦ h p hp.1⟩
  obtain ⟨V3, hV3, hV3W, hf3⟩ := hstep W hW
  obtain ⟨V2, hV2, hV2W, hf2⟩ := hstep V3 hV3
  obtain ⟨V1, hV1, hV1W, hf1⟩ := hstep V2 hV2
  obtain ⟨V0, hV0, hV0W, hf0⟩ := hstep V1 hV1
  refine ⟨V0, hV0, δ, hδ, ?_⟩
  intro T u g X Λ₁ ΛR h hT hq0 hsec
  set q₀ : iso_PhasePt := (X 0, Λ₁ 0, ΛR 0) with hq₀
  set E : ℝ → iso_PhasePt := fun t ↦ (X t, Λ₁ t, ΛR t) with hE
  have hTb : 4 * τ₀ - δ < T ∧ T < 4 * τ₀ + δ := by
    have htf : tf 1 = 4 * τ₀ := by rw [tf, hτ₀def]; norm_num
    rw [htf] at hT
    have := abs_lt.1 hT
    constructor <;> linarith [this.1, this.2]
  -- the end point, by the transversality conditions
  have hET : E T = iso_adRinvPow 1 q₀ := by
    obtain ⟨-, -, -, hXT, h1T, hRT, -⟩ := h
    simp only [hE, hq₀, iso_adRinvPow, pow_one, hXT, h1T, hRT]
  -- the points `pᵢ = fⁱ q₀`
  set p : ℕ → iso_PhasePt := fun i ↦ iso_poincareMap^[i] q₀ with hp
  have hpsucc : ∀ i, p (i + 1) = iso_poincareMap (p i) := fun i ↦ by
    simp only [hp, Function.iterate_succ_apply']
  obtain ⟨k1, k2, k3, -, -, -, h23⟩ := hsec
  have htr : ∀ i, (p i).1.trace = 0 ∧ (p i).2.1.trace = 0 ∧ (p i).2.2.trace = 0 := by
    intro i
    induction i with
    | zero => exact ⟨k1, k2, k3⟩
    | succ i ih => rw [hpsucc]; exact irt_poincareMap_traceless ih.1 ih.2.1 ih.2.2
  have hp0 : p 0 ∈ V0 := hq0
  have hp1 : p 1 ∈ V1 := by rw [hpsucc]; exact hf0 _ hp0 (htr 0).1 (htr 0).2.1 (htr 0).2.2
  have hp2 : p 2 ∈ V2 := by rw [hpsucc]; exact hf1 _ hp1 (htr 1).1 (htr 1).2.1 (htr 1).2.2
  have hp3 : p 3 ∈ V3 := by rw [hpsucc]; exact hf2 _ hp2 (htr 2).1 (htr 2).2.1 (htr 2).2.2
  have hp4 : p 4 ∈ W := by rw [hpsucc]; exact hf3 _ hp3 (htr 3).1 (htr 3).2.1 (htr 3).2.2
  have hpW : ∀ i ≤ 4, p i ∈ W := by
    intro i hi
    interval_cases i
    exacts [hV0W hp0, hV1W hp1, hV2W hp2, hV3W hp3, hp4]
  -- `χ₃₂(fⁱ q₀) = 0`: the Poincaré map lands on the section
  have h23q : irt_chi 1 2 q₀ = 0 := h23
  have hstep32 : ∀ q ∈ W, irt_chi 2 1 q = 0 → irt_chi 2 1 (iso_poincareMap q) = 0 := by
    intro q hq h0
    obtain ⟨-, -, h31z, -, -⟩ := hWp q hq h0.ge
    have hc := irt_chi_conj 1 1 2 (iso_poincareMap q)
    rw [iso_poincareMap, irt_adRinvPow_one_adR] at hc
    rw [irt_chi_antisymm, iso_poincareMap, ← hc]
    simpa using h31z
  have hchi : ∀ i ≤ 4, irt_chi 2 1 (p i) = 0 := by
    intro i hi
    induction i with
    | zero => rw [irt_chi_antisymm, neg_eq_zero]; exact h23q
    | succ i ih => rw [hpsucc]; exact hstep32 _ (hpW i (by omega)) (ih (by omega))
  -- the data of the arcs
  have hd : ∀ i ≤ 4, _ := fun i hi ↦ hWp (p i) (hpW i hi) (hchi i hi).ge
  set τp : ℕ → ℝ := fun i ↦ iso_poincareTime (p i) with hτp
  set ts : ℕ → ℝ := fun i ↦ iso_poincareSwitchTimes q₀ i with hts
  have hts0 : ts 0 = 0 := by simp [hts, iso_poincareSwitchTimes]
  have htsS : ∀ i, ts (i + 1) = ts i + τp i := fun i ↦ by
    simp [hts, hτp, hp, iso_poincareSwitchTimes, Finset.sum_range_succ]
  have hτb : ∀ i ≤ 4, τ₀ - δ < τp i ∧ τp i < τ₀ + δ := fun i hi ↦ (hd i hi).1
  have htsb : ∀ i ≤ 4, i * (τ₀ - δ) ≤ ts i ∧ ts i ≤ i * (τ₀ + δ) := by
    intro i hi
    induction i with
    | zero => simp [hts0]
    | succ i ih =>
      obtain ⟨h1, h2⟩ := ih (by omega)
      obtain ⟨h3, h4⟩ := hτb i (by omega)
      rw [htsS]; push_cast
      constructor <;> linarith
  have hflowend : ∀ i, iso_vertexFlow 2 (p i) (τp i) = iso_adRinvPow 1 (p (i + 1)) := by
    intro i; rw [hpsucc, iso_poincareMap, irt_adRinvPow_one_adR]
  have harc : ∀ i ≤ 4, ts i ∈ Ico 0 T → E (ts i) = iso_adRinvPow i (p i) →
      ∀ t ∈ Icc 0 (min (T - ts i) (τp i)), E (ts i + t) = iso_adRinvPow i
        (iso_vertexFlow 2 (p i) t) := fun i hi hs hEs ↦ (hd i hi).2.2.2.2 T u g X Λ₁ ΛR h _ hs i hEs
  have hnext : ∀ i ≤ 4, ts i ∈ Ico 0 T → E (ts i) = iso_adRinvPow i (p i) → ts (i + 1) ≤ T →
      E (ts (i + 1)) = iso_adRinvPow (i + 1) (p (i + 1)) := by
    intro i hi hs hEs hle
    have hτ0 : 0 ≤ τp i := by linarith [hτb i hi]
    have := harc i hi hs hEs (τp i) ⟨hτ0, le_min (by rw [htsS] at hle; linarith) le_rfl⟩
    rw [htsS, this, hflowend, irt_adRinvPow_add]
  have hEts : ∀ i ≤ 3, E (ts i) = iso_adRinvPow i (p i) := by
    intro i hi
    induction i with
    | zero => rw [hts0, irt_adRinvPow_zero]; rfl
    | succ i ih =>
      have hi' := htsb i (by omega)
      have hi'' := htsb (i + 1) (by omega)
      push_cast at hi''
      refine hnext i (by omega) ⟨hi'.1.trans' (mul_nonneg (Nat.cast_nonneg _) (by linarith)), ?_⟩
        (ih (by omega)) ?_
      · have : (i : ℝ) ≤ 2 := by exact_mod_cast (by omega : i ≤ 2)
        nlinarith
      · have : (i : ℝ) ≤ 2 := by exact_mod_cast (by omega : i ≤ 2)
        nlinarith
  -- `T = t₄`
  have h3b := htsb 3 (by norm_num)
  have hs3 : ts 3 ∈ Ico 0 T := ⟨by push_cast at h3b; linarith, by push_cast at h3b; linarith⟩
  have hTt4 : T = ts 4 := by
    rcases lt_trichotomy T (ts 4) with hlt | heq | hgt
    · exfalso
      rw [htsS] at hlt
      have h := harc 3 (by norm_num) hs3 (hEts 3 (by norm_num)) (T - ts 3)
        ⟨by linarith [hs3.2], le_min le_rfl (by linarith)⟩
      rw [show ts 3 + (T - ts 3) = T by ring, hET, irt_adRinvPow_mod 3] at h
      norm_num [irt_adRinvPow_zero] at h
      have h31 := (hd 3 (by norm_num)).2.1 (T - ts 3) ⟨by linarith [hs3.2], by linarith⟩
      rw [← h, show (2 : Fin 3) = 1 + ⟨1 % 3, Nat.mod_lt _ (by norm_num)⟩ from rfl,
        show (0 : Fin 3) = 2 + ⟨1 % 3, Nat.mod_lt _ (by norm_num)⟩ from rfl, irt_chi_conj,
        h23q] at h31
      exact lt_irrefl _ h31
    · exact heq
    · exfalso
      have hE4 := hnext 3 (by norm_num) hs3 (hEts 3 (by norm_num)) hgt.le
      have h4b := htsb 4 le_rfl
      push_cast at h4b
      have hs4 : ts 4 ∈ Ico 0 T := ⟨by linarith, hgt⟩
      obtain ⟨hτ4a, hτ4b⟩ := hτb 4 le_rfl
      have h := harc 4 le_rfl hs4 hE4 (T - ts 4) ⟨by linarith, le_min le_rfl (by linarith)⟩
      rw [show ts 4 + (T - ts 4) = T by ring, hET] at h
      have hinj : iso_vertexFlow 2 (p 4) (T - ts 4) = q₀ := by
        have := congrArg (iso_adRinvPow 2) h
        rw [irt_adRinvPow_add, irt_adRinvPow_add, irt_adRinvPow_mod (2 + 4),
          irt_adRinvPow_mod (2 + 1)] at this
        norm_num [irt_adRinvPow_zero] at this
        exact this.symm
      have h32 := (hd 4 le_rfl).2.2.2.1 (T - ts 4) ⟨by linarith, by linarith⟩
      rw [hinj, irt_chi_antisymm, h23q, neg_zero] at h32
      exact lt_irrefl _ h32
  -- `f⁴ q₀ = q₀`
  have hE4 := hnext 3 (by norm_num) hs3 (hEts 3 (by norm_num)) hTt4.ge
  rw [← hTt4, hET] at hE4
  have hp4 : p 4 = q₀ := by
    have := congrArg (iso_adRinvPow 2) hE4
    rw [irt_adRinvPow_add, irt_adRinvPow_add, irt_adRinvPow_mod (2 + 1),
      irt_adRinvPow_mod (2 + (3 + 1))] at this
    norm_num [irt_adRinvPow_zero] at this
    exact this.symm
  refine ⟨hp4, hTt4, fun i hi t ht ↦ ?_⟩
  change t ∈ Icc (ts i) (ts (i + 1)) at ht
  change E t = _
  have hsi : ts i ∈ Ico 0 T := by
    have := htsb i (by omega)
    have h3 := htsb 3 (by norm_num)
    push_cast at h3
    refine ⟨le_trans (mul_nonneg (Nat.cast_nonneg _) (by linarith)) this.1, ?_⟩
    have : (i : ℝ) ≤ 3 := by exact_mod_cast (by omega : i ≤ 3)
    nlinarith
  have hEi : E (ts i) = iso_adRinvPow i (p i) := hEts i (by omega)
  have hle : ts (i + 1) ≤ T := by
    rcases (by omega : i + 1 ≤ 3 ∨ i + 1 = 4) with h' | h'
    · have := htsb (i + 1) (by omega)
      have : ((i + 1 : ℕ) : ℝ) ≤ 3 := by exact_mod_cast h'
      nlinarith
    · rw [h', hTt4]
  have := harc i (by omega) hsi hEi (t - ts i)
    ⟨by linarith [ht.1], le_min (by linarith [ht.2]) (by rw [htsS] at ht; linarith [ht.2])⟩
  rw [show ts i + (t - ts i) = t by ring] at this
  exact this

end SmoothedPolygons
