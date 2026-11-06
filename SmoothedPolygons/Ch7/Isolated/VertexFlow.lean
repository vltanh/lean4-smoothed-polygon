module

public import SmoothedPolygons.Ch7.Isolated.Defs
public import SmoothedPolygons.Ch7.SmoothedPolygon

/-!
# Theorem 7.7.1, steps 0–1: normalization, time shift and the vertex flow

Step 0: the conditions of a Pontryagin extremal are homogeneous in the costate (`iso_smul`), and
an extremal can be restarted at any time `s ≥ 0` of its twisted-periodic continuation
(`iso_shift`). Step 1: the closed-form flow `iso_vertexFlow` solves the state–costate equations
with a vertex control (`iso_vertexFlow_solution`), an extremal arc with a vertex control is this
flow (`iso_arc_eq_vertexFlow`), and from `q_fix(y₀)` it is the strong lift of Theorem 7.5.1
(`iso_vertexFlow_qFix`).

## Proofs

* `iso_shift`: the continuation `poly_pw A B T f` of a Carathéodory solution `f` on `[0, T]` with
  `f(T) = A f(0) B` is a Carathéodory solution of the continued right-hand side on every `[0, NT]`
  (`ivf_isIntegralCurve_pw`, interval by interval), and so is its restart at `s`
  (`ivf_isIntegralCurve_shift`). The right-hand sides agree with those of the restarted extremal
  because the equations are equivariant under `Ad(R⁻ᵏ)` with the controls relabelled
  (`ivf_conj_pow_controlMatrix`: `R⁻ᵏ Z_w Rᵏ = Z_{iso_rotControl k w}`), and so is the
  Hamiltonian; the maximum condition holds off a countable union of translates of a null set.
* `iso_vertexFlow_solution`: differentiation of the closed forms of §7.1 (`eqn:const-control-g`,
  `eqn:const-control-z-X`, Corollary 6.5.3 for `Λ₁`, and variation of constants for `Λ_R` in the
  frame `e^{-tP} Λ_R e^{tP}`, where `c(t) = ⟨Λ_R(t), P⟩` by `ivf_vfC_eq`). The hypothesis
  `⟨Z_{e_m}, X₀⟩ ≠ 0` is not needed (for `⟨Z_{e_m}, X₀⟩ = 0`, `P = 0` and the formulas still hold).
* `iso_arc_eq_vertexFlow`: on the arc the right-hand sides agree almost everywhere with continuous
  ones, so the extremal is differentiable there; `⟨X, Z_{e_m}⟩` is constant (Lemma 7.1.1), and
  `X`, `Λ₁`, `Λ_R` are the vertex flow by Grönwall uniqueness for `X' = [P, X]`, the Lax equation
  and `eqn:lamR` (as in `poly_trajectory_unique` and `str_costateΛR_unique`).
* `iso_vertexFlow_qFix`: the `X`- and `Λ₁`-components are those of the strong lift by definition;
  the `Λ_R`-components solve the same costate equation with the same initial value, hence agree
  for all `t ∈ ℝ` (Grönwall forward and backward in time, `ivf_eq_of_hasDerivAt`).
-/

@[expose] public section

namespace SmoothedPolygons

open Matrix Set Filter Topology MeasureTheory

/-! ### Step 0: normalization and time shift -/

/-- The conditions of a Pontryagin extremal are homogeneous in the costate: `(Λ₁, Λ_R, λ_cost)`
may be multiplied by any `c > 0`. -/
theorem iso_smul {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (h : IsPontryaginExtremal T u g X Λ₁ ΛR lam) {c : ℝ} (hc : 0 < c) :
    IsPontryaginExtremal T u g X (fun t ↦ c • Λ₁ t) (fun t ↦ c • ΛR t) (c * lam) := by
  obtain ⟨hst, hg0, hgT, hXT, h1T, hRT, hlam, hpt, hI1, hIR, hmax⟩ := h
  have hc0 : c ≠ 0 := hc.ne'
  have hT : 0 ≤ T := hst.1.le
  -- scaling an integral curve
  have hsc : ∀ {f v : ℝ → Mat2}, IsIntegralCurve f v T →
      IsIntegralCurve (fun t ↦ c • f t) (fun t ↦ c • v t) T := fun {f v} hI i j ↦ by
    obtain ⟨hint, heq⟩ := hI i j
    refine ⟨hint.const_mul c, fun t ht ↦ ?_⟩
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [heq t ht, intervalIntegral.integral_const_mul]
    ring
  have hJ : (3 / 2 * (c * lam)) • J = c • ((3 / 2 * lam) • J) := by rw [smul_smul]; ring_nf
  have htf : ∀ A B : Mat2, traceForm (c • A) B = c * traceForm A B := fun A B ↦ by
    simp [traceForm, Matrix.trace_smul]
  refine ⟨hst, hg0, hgT, hXT, ?_, ?_, mul_nonpos_of_nonneg_of_nonpos hc.le hlam, fun t ht ↦ ?_,
    ?_, ?_, ?_⟩
  · simp only [h1T, Matrix.smul_mul, Matrix.mul_smul]
  · simp only [hRT, Matrix.smul_mul, Matrix.mul_smul]
  · obtain ⟨h1, h2, h3, h4⟩ := hpt t ht
    refine ⟨by rw [Matrix.trace_smul, h1, smul_zero], by rw [Matrix.trace_smul, h2, smul_zero],
      by rw [htf, h3, mul_zero], ?_⟩
    rcases h4 with h | h | h
    · exact Or.inl (mul_ne_zero hc0 h)
    · exact Or.inr (Or.inl (smul_ne_zero hc0 h))
    · exact Or.inr (Or.inr (smul_ne_zero hc0 h))
  · refine poly_isIntegralCurve_congr (hsc hI1) hT fun t _ ↦ ?_
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_sub]
  · refine poly_isIntegralCurve_congr (hsc hIR) hT fun t _ ↦ ?_
    rw [htf, hJ]
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, neg_mul,
      mul_neg]
    module
  · filter_upwards [hmax] with t ht hmem
    obtain ⟨hH, hle⟩ := ht hmem
    have hscale : ∀ v, hamiltonian (c * lam) (c • Λ₁ t) (c • ΛR t) (X t) v =
        c * hamiltonian lam (Λ₁ t) (ΛR t) (X t) v := fun v ↦ by
      simp only [hamiltonian, hJ, ← smul_sub, htf]
      ring
    refine ⟨by rw [hscale, hH, mul_zero], fun v hv ↦ ?_⟩
    rw [hscale, hscale]
    exact mul_le_mul_of_nonneg_left (hle v hv) hc.le

/-! #### The twisted-periodic continuation -/

/-- The relabelling `iso_rotControl k` of the controls is conjugation by `R⁻ᵏ`:
`R⁻ᵏ Z_w Rᵏ = Z_{iso_rotControl k w}` (from `poly_conj_pow_vertex`, by linearity). -/
lemma ivf_conj_pow_controlMatrix (k : ℕ) (w : Fin 3 → ℝ) :
    R⁻¹ ^ k * controlMatrix w * R ^ k = controlMatrix (iso_rotControl k w) := by
  obtain ⟨c, hc⟩ : ∃ c : Fin 3, c = ⟨k % 3, Nat.mod_lt _ (by norm_num)⟩ := ⟨_, rfl⟩
  have hdec : ∀ w : Fin 3 → ℝ, controlMatrix w = ∑ j, w j • controlMatrix (vertex j) := fun w ↦ by
    rw [poly_controlMatrix_eq, Fin.sum_univ_three]
  have hj : ∀ j : Fin 3, (⟨(j.val + k) % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3) = j + c := by
    intro j
    ext
    simp only [Fin.val_add, hc]
    omega
  rw [hdec w, hdec (iso_rotControl k w), Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [← Equiv.sum_comp (Equiv.addRight c)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [poly_conj_smul, poly_conj_pow_vertex, hj]
  simp only [Equiv.coe_addRight, iso_rotControl, ← hc, add_sub_cancel_right]

lemma ivf_rotControl_mem {k : ℕ} {w : Fin 3 → ℝ} (hw : w ∈ controlSimplex) :
    iso_rotControl k w ∈ controlSimplex := by
  obtain ⟨c, hc⟩ : ∃ c : Fin 3, c = ⟨k % 3, Nat.mod_lt _ (by norm_num)⟩ := ⟨_, rfl⟩
  refine ⟨fun i ↦ hw.1 _, ?_⟩
  have h1 : ∑ i, w (i - c) = ∑ i, w i := Equiv.sum_comp (Equiv.subRight c) w
  have h2 := hw.2
  rw [Fin.sum_univ_three, Fin.sum_univ_three] at h1
  simp only [iso_rotControl, ← hc]
  linarith

lemma ivf_exists_rotControl (k : ℕ) {v : Fin 3 → ℝ} (hv : v ∈ controlSimplex) :
    ∃ w ∈ controlSimplex, iso_rotControl k w = v := by
  obtain ⟨c, hc⟩ : ∃ c : Fin 3, c = ⟨k % 3, Nat.mod_lt _ (by norm_num)⟩ := ⟨_, rfl⟩
  refine ⟨fun i ↦ v (i + c), ⟨fun i ↦ hv.1 _, ?_⟩, ?_⟩
  · have h1 : ∑ i, v (i + c) = ∑ i, v i := Equiv.sum_comp (Equiv.addRight c) v
    have h2 := hv.2
    rw [Fin.sum_univ_three, Fin.sum_univ_three] at h1
    linarith
  · funext i
    simp only [iso_rotControl, ← hc, sub_add_cancel]

/-- A nonzero matrix has nonzero `R⁻ᵏ`-conjugates. -/
lemma ivf_conj_pow_ne_zero {M : Mat2} (h : M ≠ 0) (k : ℕ) : R⁻¹ ^ k * M * R ^ k ≠ 0 := by
  intro h0
  apply h
  have := congrArg (fun Y ↦ R ^ k * Y * R⁻¹ ^ k) h0
  simp only [Matrix.mul_zero, Matrix.zero_mul] at this
  rwa [show R ^ k * (R⁻¹ ^ k * M * R ^ k) * R⁻¹ ^ k =
    (R ^ k * R⁻¹ ^ k) * M * (R ^ k * R⁻¹ ^ k) by simp only [Matrix.mul_assoc],
    poly_Rpow_mul_Rinvpow, Matrix.one_mul, Matrix.mul_one] at this

/-- `f̃(τ + T) = A f̃(τ) B` for the continuation `f̃ = poly_pw A B T f`. -/
lemma ivf_pw_add_period {A B : Mat2} {T : ℝ} (hT : 0 < T) (f : ℝ → Mat2) {τ : ℝ} (hτ : 0 ≤ τ) :
    poly_pw A B T f (τ + T) = A * poly_pw A B T f τ * B := by
  have hk : ⌊(τ + T) / T⌋₊ = ⌊τ / T⌋₊ + 1 := by
    rw [add_div, div_self hT.ne', Nat.floor_add_one (div_nonneg hτ hT.le)]
  rw [poly_pw, poly_pw, hk]
  push_cast
  rw [show τ + T - (⌊τ / T⌋₊ + 1) * T = τ - ⌊τ / T⌋₊ * T by ring, pow_succ' A, pow_succ B]
  simp only [Matrix.mul_assoc]

lemma ivf_intervalIntegrable_conj {v : ℝ → Mat2} {a b : ℝ}
    (hv : ∀ i j, IntervalIntegrable (fun s ↦ v s i j) volume a b) (C D : Mat2) (i j : Fin 2) :
    IntervalIntegrable (fun s ↦ (C * v s * D) i j) volume a b := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  exact ((((hv 0 0).const_mul _).add ((hv 1 0).const_mul _)).mul_const _).add
    ((((hv 0 1).const_mul _).add ((hv 1 1).const_mul _)).mul_const _)

/-- The entrywise integral of `C v D` is `C (∫ v) D`. -/
lemma ivf_integral_conj {v : ℝ → Mat2} {a b : ℝ}
    (hv : ∀ i j, IntervalIntegrable (fun s ↦ v s i j) volume a b) (C D : Mat2) (i j : Fin 2) :
    ∫ s in a..b, (C * v s * D) i j = (C * (Matrix.of fun k l ↦ ∫ s in a..b, v s k l) * D) i j := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply]
  rw [intervalIntegral.integral_add
      ((((hv 0 0).const_mul _).add ((hv 1 0).const_mul _)).mul_const _)
      ((((hv 0 1).const_mul _).add ((hv 1 1).const_mul _)).mul_const _),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_add ((hv 0 0).const_mul _) ((hv 1 0).const_mul _),
    intervalIntegral.integral_add ((hv 0 1).const_mul _) ((hv 1 1).const_mul _)]
  simp only [intervalIntegral.integral_const_mul]

/-- The twisted-periodic continuation `f̃ = poly_pw A B T f` of a Carathéodory solution on
`[0, T]` with `f(T) = A f(0) B` is a Carathéodory solution on `[0, NT]`, of the continued
right-hand side. -/
lemma ivf_isIntegralCurve_pw {A B : Mat2} {T : ℝ} (hT : 0 < T) {f v : ℝ → Mat2}
    (hI : IsIntegralCurve f v T) (hglue : f T = A * f 0 * B) (N : ℕ) :
    IsIntegralCurve (poly_pw A B T f) (poly_pw A B T v) (N * T) := by
  have hv : ∀ k l, IntervalIntegrable (fun s ↦ v s k l) volume 0 T := fun k l ↦ (hI k l).1
  induction N with
  | zero =>
    intro i j
    refine ⟨by simp, fun t ht ↦ ?_⟩
    have : t = 0 := by simp only [Nat.cast_zero, zero_mul, mem_Icc] at ht; linarith [ht.1, ht.2]
    subst this
    simp
  | succ n ih =>
    have hn0 : (0 : ℝ) ≤ n * T := by positivity
    have hn1 : (n : ℝ) * T ≤ (n + 1) * T := by nlinarith
    have hpv : EqOn (poly_pw A B T v) (fun s ↦ A ^ n * v (s - n * T) * B ^ n)
        (Ioo (n * T) ((n + 1) * T)) := fun s hs ↦ poly_pw_of_mem_Ico hT ⟨hs.1.le, hs.2⟩
    have hsh : ∀ k l, IntervalIntegrable (fun s ↦ v (s - n * T) k l) volume (n * T)
        ((n + 1) * T) := fun k l ↦ by
      have := (hv k l).comp_sub_right (n * T)
      rwa [zero_add, show T + n * T = (n + 1) * T by ring] at this
    have hpint : ∀ i j, IntervalIntegrable (fun s ↦ poly_pw A B T v s i j) volume (n * T)
        ((n + 1) * T) := fun i j ↦ by
      refine (ivf_intervalIntegrable_conj hsh (A ^ n) (B ^ n) i j).congr_uIoo fun s hs ↦ ?_
      rw [uIoo_of_le hn1] at hs
      simp only [hpv hs]
    have hpeq : ∀ t ∈ Icc ((n : ℝ) * T) ((n + 1) * T), ∀ i j, poly_pw A B T f t i j =
        poly_pw A B T f (n * T) i j + ∫ s in (n * T)..t, poly_pw A B T v s i j := by
      intro t ht i j
      have ht' : t - n * T ∈ Icc 0 T := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hft : f (t - n * T) =
          f 0 + Matrix.of fun k l ↦ ∫ s in (0 : ℝ)..(t - n * T), v s k l := by
        ext k l
        exact (hI k l).2 _ ht'
      have hv' : ∀ k l, IntervalIntegrable (fun s ↦ v s k l) volume 0 (t - n * T) := fun k l ↦
        (hv k l).mono_set (by
          rw [uIcc_of_le ht'.1, uIcc_of_le hT.le]; exact Icc_subset_Icc_right ht'.2)
      have hcongr : ∫ s in (n * T)..t, poly_pw A B T v s i j =
          ∫ s in (n * T)..t, (A ^ n * v (s - n * T) * B ^ n) i j := by
        refine intervalIntegral.integral_congr_uIoo fun s hs ↦ ?_
        rw [uIoo_of_le ht.1] at hs
        simp only [hpv ⟨hs.1, hs.2.trans_le ht.2⟩]
      have hcomp := intervalIntegral.integral_comp_sub_right
        (fun s ↦ (A ^ n * v s * B ^ n) i j) (n * T) (a := n * T) (b := t)
      simp only [sub_self] at hcomp
      rw [poly_pw_of_mem_Icc hT hglue ht, poly_pw_of_mem_Ico hT ⟨le_rfl, by linarith⟩, sub_self,
        hcongr, hcomp, ivf_integral_conj hv', hft]
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
    intro i j
    obtain ⟨hint, heq⟩ := ih i j
    push_cast
    refine ⟨hint.trans (hpint i j), fun t ht ↦ ?_⟩
    rcases le_total t (n * T) with h | h
    · exact heq t ⟨ht.1, h⟩
    · have hnt : IntervalIntegrable (fun s ↦ poly_pw A B T v s i j) volume (n * T) t :=
        (hpint i j).mono_set (by
          rw [uIcc_of_le h, uIcc_of_le hn1]; exact Icc_subset_Icc_right ht.2)
      rw [hpeq t ⟨h, ht.2⟩ i j, heq (n * T) ⟨hn0, le_rfl⟩, add_assoc,
        intervalIntegral.integral_add_adjacent_intervals hint hnt]

/-- A Carathéodory solution on `[0, S]` restarted at `s`, `s + T ≤ S`. -/
lemma ivf_isIntegralCurve_shift {F V : ℝ → Mat2} {S s T : ℝ} (hI : IsIntegralCurve F V S)
    (hs : 0 ≤ s) (hT : 0 ≤ T) (hsT : s + T ≤ S) :
    IsIntegralCurve (fun t ↦ F (s + t)) (fun t ↦ V (s + t)) T := by
  intro i j
  obtain ⟨hint, heq⟩ := hI i j
  have hS : 0 ≤ S := by linarith
  have hsub : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b ≤ S →
      IntervalIntegrable (fun σ ↦ V σ i j) volume a b := fun ha hab hb ↦
    hint.mono_set (by
      rw [uIcc_of_le hab, uIcc_of_le hS]; exact Icc_subset_Icc ha hb)
  refine ⟨?_, fun t ht ↦ ?_⟩
  · have := (hsub hs (by linarith) hsT).comp_add_left s
    simpa only [sub_self, add_sub_cancel_left] using this
  · have hcomp := intervalIntegral.integral_comp_add_left (fun σ ↦ V σ i j) s (a := 0) (b := t)
    simp only [add_zero] at hcomp ⊢
    rw [hcomp, heq (s + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩, heq s ⟨hs, by linarith⟩,
      ← intervalIntegral.integral_add_adjacent_intervals (hsub le_rfl hs (by linarith))
        (hsub hs (by linarith [ht.1]) (by linarith [ht.2]))]
    ring

/-- Left multiplication of a Carathéodory solution by a constant matrix. -/
lemma ivf_isIntegralCurve_const_mul {F V : ℝ → Mat2} {T : ℝ} (hI : IsIntegralCurve F V T)
    (C : Mat2) : IsIntegralCurve (fun t ↦ C * F t) (fun t ↦ C * V t) T := by
  intro i j
  refine ⟨?_, fun t ht ↦ ?_⟩
  · simp only [Matrix.mul_apply, Fin.sum_univ_two]
    exact ((hI 0 j).1.const_mul _).add ((hI 1 j).1.const_mul _)
  · have h0t : ∀ k, IntervalIntegrable (fun s ↦ V s k j) volume 0 t := fun k ↦
      (hI k j).1.mono_set (by
        rw [uIcc_of_le ht.1, uIcc_of_le (ht.1.trans ht.2)]; exact Icc_subset_Icc_right ht.2)
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    rw [intervalIntegral.integral_add ((h0t 0).const_mul _) ((h0t 1).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, (hI 0 j).2 t ht,
      (hI 1 j).2 t ht]
    ring

/-- Restarting an extremal at a time `s ≥ 0`: by the transversality conditions the extremal
continues twisted-periodically (`X(t + T) = R⁻¹X(t)R`, `Λ(t + T) = R⁻¹Λ(t)R`,
`g(t + T) = g(t)R`), and the continuation started at `s`, with `g` renormalized to `g(0) = I₂`, is
again an extremal on `[0, T]`. (Not in the book; needed because an extremal near the octagon need
not start on the Poincaré section.) -/
theorem iso_shift {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (h : IsPontryaginExtremal T u g X Λ₁ ΛR lam) {s : ℝ} (hs : 0 ≤ s) :
    IsPontryaginExtremal T (fun t ↦ iso_extControl T u (s + t))
      (fun t ↦ (poly_pw 1 R T g s)⁻¹ * poly_pw 1 R T g (s + t))
      (fun t ↦ poly_pw R⁻¹ R T X (s + t)) (fun t ↦ poly_pw R⁻¹ R T Λ₁ (s + t))
      (fun t ↦ poly_pw R⁻¹ R T ΛR (s + t)) lam := by
  obtain ⟨⟨hT, hum, husim, hst, hgI, hXI⟩, hg0, hgT, hXT, h1T, hRT, hlam, hpt, hI1, hIR, hmax⟩ := h
  have hR1 : ∀ k : ℕ, R ^ k * R⁻¹ ^ k = 1 := poly_Rpow_mul_Rinvpow
  -- the point `τ - kT ∈ [0, T]` of the original extremal, `k = ⌊τ/T⌋`
  have hpc : ∀ τ : ℝ, 0 ≤ τ → τ - ⌊τ / T⌋₊ * T ∈ Icc 0 T := fun τ hτ ↦ by
    obtain ⟨h1, h2⟩ := poly_floor_mem hT hτ
    exact ⟨by linarith, by linarith⟩
  have hgdet : ∀ τ, 0 ≤ τ → (poly_pw 1 R T g τ).det = 1 := by
    intro τ hτ
    simp only [poly_pw, one_pow, Matrix.one_mul, Matrix.det_mul, Matrix.det_pow,
      (hst _ (hpc τ hτ)).1, poly_det_R, one_pow, mul_one]
  have hgu : IsUnit (poly_pw 1 R T g s).det := by rw [hgdet s hs]; exact isUnit_one
  -- the continued integral curves, restarted at `s`
  obtain ⟨N, hN⟩ : ∃ N : ℕ, s + T ≤ N * T := by
    refine ⟨⌊s / T⌋₊ + 2, ?_⟩
    have := (poly_floor_mem hT hs).2
    push_cast
    linarith
  have hshift : ∀ {A B : Mat2} {f v : ℝ → Mat2}, IsIntegralCurve f v T → f T = A * f 0 * B →
      IsIntegralCurve (fun t ↦ poly_pw A B T f (s + t)) (fun t ↦ poly_pw A B T v (s + t)) T :=
    fun hI hgl ↦ ivf_isIntegralCurve_shift (ivf_isIntegralCurve_pw hT hI hgl N) hs hT.le hN
  refine ⟨⟨hT, ?_, fun t ht ↦ ?_, fun t ht ↦ ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, hlam, fun t ht ↦ ?_,
    ?_, ?_, ?_⟩
  · -- measurability of the continued control
    have hF : Measurable (fun p : ℝ × ℕ ↦ iso_rotControl p.2 (u (p.1 - p.2 * T))) :=
      measurable_from_prod_countable_left fun n ↦ by
        change Measurable fun c : ℝ ↦ iso_rotControl n (u (c - n * T))
        unfold iso_rotControl
        exact Measurable.of_eval fun i ↦
          (measurable_pi_apply _).comp (hum.comp (measurable_sub_const _))
    have hE : Measurable (iso_extControl T u) :=
      hF.comp (measurable_id.prodMk (Nat.measurable_floor.comp (measurable_id.div_const T)))
    exact hE.comp (measurable_const_add s)
  · exact ivf_rotControl_mem (husim _ (hpc (s + t) (by linarith [ht.1])))
  · refine ⟨?_, poly_isStarState_conj_pow _ (hst _ (hpc (s + t) (by linarith [ht.1]))).2⟩
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, hgdet s hs, hgdet (s + t) (by linarith [ht.1])]
    simp
  · -- `g' = gX`
    have h1 := ivf_isIntegralCurve_const_mul (hshift (A := 1) (B := R) hgI
      (by rw [hgT, hg0]; simp))
      (poly_pw 1 R T g s)⁻¹
    refine poly_isIntegralCurve_congr h1 hT.le fun t _ ↦ ?_
    simp only [poly_pw, one_pow, Matrix.one_mul, Matrix.mul_assoc, poly_Rpow_cancel]
  · -- `X' = [P, X]`
    refine poly_isIntegralCurve_congr (hshift hXI hXT) hT.le fun t _ ↦ ?_
    simp only [poly_pw, iso_extControl]
    rw [poly_conj_bracket (hR1 _), poly_controlP_conj (hR1 _) (ivf_conj_pow_controlMatrix _ _)]
  · simp only [add_zero]
    exact Matrix.nonsing_inv_mul _ hgu
  · simp only
    rw [ivf_pw_add_period hT g hs, Matrix.one_mul, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hgu, Matrix.one_mul]
  · simp only [add_zero]
    exact ivf_pw_add_period hT X hs
  · simp only [add_zero]
    exact ivf_pw_add_period hT Λ₁ hs
  · simp only [add_zero]
    exact ivf_pw_add_period hT ΛR hs
  · -- traceless costates, `Λ_R ⊥ X`, nontriviality
    obtain ⟨h1, h2, h3, h4⟩ := hpt _ (hpc (s + t) (by linarith [ht.1]))
    simp only [poly_pw]
    refine ⟨by rw [poly_trace_conj (hR1 _), h1], by rw [poly_trace_conj (hR1 _), h2],
      by rw [poly_traceForm_conj (hR1 _), h3], ?_⟩
    rcases h4 with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (ivf_conj_pow_ne_zero h _))
    · exact Or.inr (Or.inr (ivf_conj_pow_ne_zero h _))
  · -- `Λ₁' = [Λ₁, X]`
    refine poly_isIntegralCurve_congr (hshift hI1 h1T) hT.le fun t _ ↦ ?_
    simp only [poly_pw]
    rw [poly_conj_bracket (hR1 _)]
  · -- the costate equation `eqn:lamR`
    change IsIntegralCurve (fun t ↦ poly_pw R⁻¹ R T ΛR (s + t)) (fun t ↦ costateRHS lam
      (poly_pw R⁻¹ R T Λ₁ (s + t)) (poly_pw R⁻¹ R T ΛR (s + t)) (poly_pw R⁻¹ R T X (s + t))
      (iso_extControl T u (s + t))) T
    refine poly_isIntegralCurve_congr
      (hshift (v := fun t ↦ costateRHS lam (Λ₁ t) (ΛR t) (X t) (u t)) hIR hRT) hT.le
      fun t _ ↦ ?_
    simp only [poly_pw, iso_extControl]
    rw [poly_costateRHS_conj (hR1 _) (poly_conj_pow_J _) (ivf_conj_pow_controlMatrix _ _)]
  · -- the maximum principle and `H = 0`, almost everywhere (translations preserve null sets)
    have hkey : ∀ τ : ℝ,
        (hamiltonian lam (Λ₁ (τ - ⌊τ / T⌋₊ * T)) (ΛR (τ - ⌊τ / T⌋₊ * T)) (X (τ - ⌊τ / T⌋₊ * T))
            (u (τ - ⌊τ / T⌋₊ * T)) = 0 ∧
          ∀ v ∈ controlSimplex, hamiltonian lam (Λ₁ (τ - ⌊τ / T⌋₊ * T))
            (ΛR (τ - ⌊τ / T⌋₊ * T)) (X (τ - ⌊τ / T⌋₊ * T)) v ≤
            hamiltonian lam (Λ₁ (τ - ⌊τ / T⌋₊ * T)) (ΛR (τ - ⌊τ / T⌋₊ * T))
              (X (τ - ⌊τ / T⌋₊ * T)) (u (τ - ⌊τ / T⌋₊ * T))) →
        (hamiltonian lam (poly_pw R⁻¹ R T Λ₁ τ) (poly_pw R⁻¹ R T ΛR τ) (poly_pw R⁻¹ R T X τ)
            (iso_extControl T u τ) = 0 ∧
          ∀ v ∈ controlSimplex, hamiltonian lam (poly_pw R⁻¹ R T Λ₁ τ) (poly_pw R⁻¹ R T ΛR τ)
            (poly_pw R⁻¹ R T X τ) v ≤ hamiltonian lam (poly_pw R⁻¹ R T Λ₁ τ)
              (poly_pw R⁻¹ R T ΛR τ) (poly_pw R⁻¹ R T X τ) (iso_extControl T u τ)) := by
      intro τ ⟨hH, hle⟩
      have hc : ∀ w, hamiltonian lam (poly_pw R⁻¹ R T Λ₁ τ) (poly_pw R⁻¹ R T ΛR τ)
          (poly_pw R⁻¹ R T X τ) (iso_rotControl ⌊τ / T⌋₊ w) =
          hamiltonian lam (Λ₁ (τ - ⌊τ / T⌋₊ * T)) (ΛR (τ - ⌊τ / T⌋₊ * T))
            (X (τ - ⌊τ / T⌋₊ * T)) w := fun w ↦
        poly_hamiltonian_conj (hR1 _) (poly_conj_pow_J _) (ivf_conj_pow_controlMatrix _ w) lam
          _ _ _
      have hu' : iso_extControl T u τ = iso_rotControl ⌊τ / T⌋₊ (u (τ - ⌊τ / T⌋₊ * T)) := rfl
      rw [hu', hc]
      refine ⟨hH, fun v hv ↦ ?_⟩
      obtain ⟨w, hw, rfl⟩ := ivf_exists_rotControl ⌊τ / T⌋₊ hv
      rw [hc]
      exact hle w hw
    have hN0 := ae_iff.1 hmax
    refine ae_iff.2 (measure_mono_null ?_ (measure_union_null
      (measure_iUnion_null fun k : ℕ ↦ (measure_preimage_add_right volume (s - k * T) _).trans hN0)
      ((countable_range fun k : ℕ ↦ (k : ℝ) * T - s).measure_zero volume)))
    intro t ht
    simp only [mem_ofPred_eq, not_imp] at ht
    obtain ⟨htI, hbad⟩ := ht
    have hτ : 0 ≤ s + t := by linarith [htI.1]
    obtain ⟨hf1, hf2⟩ := poly_floor_mem hT hτ
    rcases (show (0 : ℝ) ≤ s + t - ⌊(s + t) / T⌋₊ * T by linarith).eq_or_lt with h0 | hpos
    · exact Or.inr ⟨⌊(s + t) / T⌋₊, by linarith⟩
    · refine Or.inl (mem_iUnion.2 ⟨⌊(s + t) / T⌋₊, ?_⟩)
      rw [mem_preimage, show t + (s - ⌊(s + t) / T⌋₊ * T) = s + t - ⌊(s + t) / T⌋₊ * T by ring]
      simp only [mem_ofPred_eq, not_imp]
      exact ⟨⟨hpos, by linarith⟩, fun hgood ↦ hbad (hkey (s + t) hgood)⟩

/-! ### Step 1: the extremal flow with a vertex control -/

/-- If `P` is a multiple of `Z`, then `⟨Z, e^{tP} X₀ e^{-tP}⟩ = ⟨Z, X₀⟩`. -/
lemma ivf_traceForm_conj_exp (Z X₀ P : Mat2) (c : ℝ) (hP : P = c • Z) (t : ℝ) :
    traceForm Z (NormedSpace.exp (t • P) * X₀ * NormedSpace.exp (-t • P)) = traceForm Z X₀ := by
  have hcomm : Commute Z (NormedSpace.exp (-t • P)) := by
    rw [hP, smul_smul]
    exact commute_exp_smul Z _
  unfold traceForm
  rw [show Z * (NormedSpace.exp (t • P) * X₀ * NormedSpace.exp (-t • P)) =
      Z * NormedSpace.exp (t • P) * X₀ * NormedSpace.exp (-t • P) by simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hcomm.eq,
    Matrix.mul_assoc Z, exp_neg_smul_mul_exp_smul, Matrix.mul_one]

/-- Along the vertex flow `P = Z_{e_m}/⟨Z_{e_m}, X⟩` is constant (Lemma 7.1.1). -/
lemma ivf_controlP_vfX (m : Fin 3) (q : iso_PhasePt) (t : ℝ) :
    controlP (vertex m) (iso_vfX m q t) = iso_vfP m q := by
  unfold controlP
  rw [iso_vfX, constControlX, ivf_traceForm_conj_exp (controlMatrix (vertex m)) q.1 (iso_vfP m q)
    (traceForm (controlMatrix (vertex m)) q.1)⁻¹ rfl]
  rfl

lemma ivf_vfG_isUnit (m : Fin 3) (q : iso_PhasePt) (t : ℝ) : IsUnit (iso_vfG m q t).det := by
  unfold iso_vfG constControlG
  rw [Matrix.det_mul]
  refine IsUnit.mul (IsUnit.of_mul_eq_one (NormedSpace.exp (-t • (q.1 + iso_vfP m q))).det ?_)
    (IsUnit.of_mul_eq_one (NormedSpace.exp (t • iso_vfP m q)).det ?_)
  · rw [← Matrix.det_mul, exp_smul_mul_exp_neg_smul, Matrix.det_one]
  · rw [← Matrix.det_mul, exp_neg_smul_mul_exp_smul, Matrix.det_one]

lemma ivf_vfG_hasDerivAt (m : Fin 3) (q : iso_PhasePt) (t : ℝ) :
    HasDerivAtEntrywise (iso_vfG m q) (iso_vfG m q t * iso_vfX m q t) t :=
  (constControl_solution (vertex m) q.1 t).1

lemma ivf_vfX_hasDerivAt (m : Fin 3) (q : iso_PhasePt) (t : ℝ) :
    HasDerivAtEntrywise (iso_vfX m q)
      (controlP (vertex m) (iso_vfX m q t) * iso_vfX m q t -
        iso_vfX m q t * controlP (vertex m) (iso_vfX m q t)) t :=
  (constControl_solution (vertex m) q.1 t).2.1

/-- `Λ₁(t) = g(t)⁻¹ Λ₁(0) g(t)` solves `Λ₁' = [Λ₁, X]` (Corollary 6.5.3). -/
lemma ivf_vfΛ₁_hasDerivAt (m : Fin 3) (q : iso_PhasePt) (t : ℝ) :
    HasDerivAtEntrywise (iso_vfΛ₁ m q)
      (iso_vfΛ₁ m q t * iso_vfX m q t - iso_vfX m q t * iso_vfΛ₁ m q t) t := by
  have hg := ivf_vfG_hasDerivAt m q t
  have hdet := ivf_vfG_isUnit m q t
  refine ((hg.inv hdet).mul_const q.2.1 |>.mul hg).congr_deriv ?_
  have h1 : (iso_vfG m q t)⁻¹ * (iso_vfG m q t * iso_vfX m q t) = iso_vfX m q t := by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
  rw [h1, iso_vfΛ₁]
  simp only [neg_mul, Matrix.mul_assoc]
  abel

lemma ivf_vfΛ₁_continuous (m : Fin 3) (q : iso_PhasePt) : Continuous (iso_vfΛ₁ m q) :=
  continuous_iff_continuousAt.2 fun t ↦
    (continuousAt_iff_entrywise.2 fun i j ↦ (ivf_vfΛ₁_hasDerivAt m q t i j).continuousAt)

lemma ivf_vfX_continuous (m : Fin 3) (q : iso_PhasePt) : Continuous (iso_vfX m q) :=
  continuous_iff_continuousAt.2 fun t ↦
    (continuousAt_iff_entrywise.2 fun i j ↦ (ivf_vfX_hasDerivAt m q t i j).continuousAt)

lemma ivf_vfM_continuous (m : Fin 3) (q : iso_PhasePt) : Continuous (iso_vfM m q) := by
  refine continuous_iff_continuousAt.2 fun t ↦ continuousAt_iff_entrywise.2 fun i j ↦ ?_
  have h := ((hasDerivAtEntrywise_exp_neg_smul_const (iso_vfP m q) t).mul
    ((ivf_vfΛ₁_hasDerivAt m q t).add_const ((3 / 2 : ℝ) • J))).mul
    (hasDerivAtEntrywise_exp_smul_const (iso_vfP m q) t)
  exact (h i j).continuousAt

lemma ivf_vfC_continuous (m : Fin 3) (q : iso_PhasePt) : Continuous (iso_vfC m q) := by
  have h : Continuous fun s ↦
      traceForm (iso_vfM m q s) (q.1 * iso_vfP m q - iso_vfP m q * q.1) :=
    ((ivf_vfM_continuous m q).matrix_mul continuous_const).matrix_trace
  refine continuous_iff_continuousAt.2 fun t ↦ ?_
  exact ((h.integral_hasStrictDerivAt 0 t).hasDerivAt.const_sub _).continuousAt

lemma ivf_traceForm_sub_left (A B C : Mat2) :
    traceForm (A - B) C = traceForm A C - traceForm B C := by
  simp only [traceForm, Matrix.sub_mul, Matrix.trace_sub]

lemma ivf_traceForm_smul_left (c : ℝ) (A C : Mat2) : traceForm (c • A) C = c * traceForm A C := by
  simp only [traceForm, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

/-- The trace form commutes with the entrywise integral. -/
lemma ivf_traceForm_of_integral {N : ℝ → Mat2} (hN : Continuous N) (B : Mat2) (t : ℝ) :
    traceForm (Matrix.of fun i j ↦ ∫ s in (0 : ℝ)..t, N s i j) B =
      ∫ s in (0 : ℝ)..t, traceForm (N s) B := by
  have hi : ∀ i j (c : ℝ), IntervalIntegrable (fun s ↦ N s i j * c) volume 0 t :=
    fun i j c ↦ ((hN.matrix_elem i j).mul continuous_const).intervalIntegrable _ _
  simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply]
  rw [intervalIntegral.integral_add ((hi 0 0 _).add (hi 0 1 _)) ((hi 1 0 _).add (hi 1 1 _)),
    intervalIntegral.integral_add (hi 0 0 _) (hi 0 1 _),
    intervalIntegral.integral_add (hi 1 0 _) (hi 1 1 _)]
  simp only [intervalIntegral.integral_mul_const]

/-- `c(t) = ⟨Λ_R(t), P⟩` along the vertex flow. -/
lemma ivf_vfC_eq (m : Fin 3) (q : iso_PhasePt) (t : ℝ) :
    iso_vfC m q t = traceForm (iso_vfΛR m q t) (iso_vfP m q) := by
  have hN : Continuous fun s ↦ iso_vfM m q s * q.1 - q.1 * iso_vfM m q s :=
    ((ivf_vfM_continuous m q).matrix_mul continuous_const).sub
      (continuous_const.matrix_mul (ivf_vfM_continuous m q))
  have hpt : ∀ s, traceForm (iso_vfM m q s * q.1 - q.1 * iso_vfM m q s) (iso_vfP m q) =
      traceForm (iso_vfM m q s) (q.1 * iso_vfP m q - iso_vfP m q * q.1) := fun s ↦ by
    simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.sub_apply]
    ring
  have hK : traceForm (iso_vfP m q * q.1 - q.1 * iso_vfP m q) (iso_vfP m q) = 0 := by
    simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.sub_apply]
    ring
  have hFP : NormedSpace.exp (-t • iso_vfP m q) * iso_vfP m q =
      iso_vfP m q * NormedSpace.exp (-t • iso_vfP m q) :=
    ((commute_exp_smul (iso_vfP m q) (-t)).eq).symm
  rw [iso_vfΛR, iso_vfC]
  generalize hL : q.2.2 - _ - _ = L
  have hconj : traceForm (NormedSpace.exp (t • iso_vfP m q) * L *
      NormedSpace.exp (-t • iso_vfP m q)) (iso_vfP m q) = traceForm L (iso_vfP m q) := by
    unfold traceForm
    rw [Matrix.mul_assoc _ (NormedSpace.exp (-t • iso_vfP m q)), hFP, ← Matrix.mul_assoc,
      Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      exp_neg_smul_mul_exp_smul, Matrix.one_mul]
  rw [hconj, ← hL, ivf_traceForm_sub_left, ivf_traceForm_sub_left, ivf_traceForm_smul_left, hK,
    mul_zero, sub_zero, ivf_traceForm_of_integral hN]
  simp only [hpt]

/-- `Λ_R` of the vertex flow solves the costate equation `eqn:lamR` (`λ_cost = -1`). -/
lemma ivf_vfΛR_hasDerivAt (m : Fin 3) (q : iso_PhasePt) (t : ℝ) :
    HasDerivAtEntrywise (iso_vfΛR m q)
      (costateRHS (-1) (iso_vfΛ₁ m q t) (iso_vfΛR m q t) (iso_vfX m q t) (vertex m)) t := by
  have hM := ivf_vfM_continuous m q
  have hC := ivf_vfC_continuous m q
  have hN : Continuous fun s ↦ iso_vfM m q s * q.1 - q.1 * iso_vfM m q s :=
    (hM.matrix_mul continuous_const).sub (continuous_const.matrix_mul hM)
  have hI1 : HasDerivAt (fun t ↦ ∫ σ in (0 : ℝ)..t, iso_vfC m q σ) (iso_vfC m q t) t :=
    (hC.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hI2 : HasDerivAtEntrywise (fun t ↦ Matrix.of fun i j ↦
      ∫ s in (0 : ℝ)..t, (iso_vfM m q s * q.1 - q.1 * iso_vfM m q s) i j)
      (iso_vfM m q t * q.1 - q.1 * iso_vfM m q t) t := fun i j ↦ by
    simpa only [Matrix.of_apply] using
      ((hN.matrix_elem i j).integral_hasStrictDerivAt 0 t).hasDerivAt
  have hL := ((hasDerivAtEntrywise_const q.2.2 t).sub (hasDerivAtEntrywise_smul_const hI1
    (iso_vfP m q * q.1 - q.1 * iso_vfP m q))).sub hI2
  have hE := hasDerivAtEntrywise_exp_smul_const' (iso_vfP m q) t
  have hF := hasDerivAtEntrywise_exp_neg_smul_const (iso_vfP m q) t
  refine ((hE.mul hL).mul hF).congr_deriv ?_
  -- the algebra: conjugation by `E = e^{tP}` is multiplicative
  have hc := ivf_vfC_eq m q t
  rw [costateRHS, ivf_controlP_vfX, ← hc]
  set P := iso_vfP m q
  set E := NormedSpace.exp (t • P)
  set F := NormedSpace.exp (-t • P)
  have hFE : F * E = 1 := exp_neg_smul_mul_exp_smul P t
  have hEF : E * F = 1 := exp_smul_mul_exp_neg_smul P t
  have hEP : E * P * F = P := by
    rw [← (commute_exp_smul P t).eq, Matrix.mul_assoc, hEF, Matrix.mul_one]
  have hEM : E * iso_vfM m q t * F = iso_vfΛ₁ m q t + (3 / 2 : ℝ) • J := by
    simp only [iso_vfM]
    rw [show E * (F * (iso_vfΛ₁ m q t + (3 / 2 : ℝ) • J) * E) * F =
      (E * F) * (iso_vfΛ₁ m q t + (3 / 2 : ℝ) • J) * (E * F) by simp only [Matrix.mul_assoc],
      hEF, Matrix.one_mul, Matrix.mul_one]
  have hX : iso_vfX m q t = E * q.1 * F := rfl
  have hR : iso_vfΛR m q t = E * (q.2.2 -
      (∫ σ in (0 : ℝ)..t, iso_vfC m q σ) • (P * q.1 - q.1 * P) -
      Matrix.of fun i j ↦ ∫ s in (0 : ℝ)..t, (iso_vfM m q s * q.1 - q.1 * iso_vfM m q s) i j) *
      F := rfl
  generalize q.2.2 - (∫ σ in (0 : ℝ)..t, iso_vfC m q σ) • (P * q.1 - q.1 * P) -
      Matrix.of (fun i j ↦ ∫ s in (0 : ℝ)..t, (iso_vfM m q s * q.1 - q.1 * iso_vfM m q s) i j)
    = L at hR ⊢
  -- `E L' F = -c [P, X] - [Λ₁ + (3/2) J, X]`
  have hmid : E * ((0 : Mat2) - iso_vfC m q t • (P * q.1 - q.1 * P) -
      (iso_vfM m q t * q.1 - q.1 * iso_vfM m q t)) * F =
      -(iso_vfC m q t • (P * iso_vfX m q t - iso_vfX m q t * P)) -
        ((iso_vfΛ₁ m q t + (3 / 2 : ℝ) • J) * iso_vfX m q t -
          iso_vfX m q t * (iso_vfΛ₁ m q t + (3 / 2 : ℝ) • J)) := by
    rw [zero_sub, poly_conj_sub, poly_conj_neg, poly_conj_smul, poly_conj_bracket hFE,
      poly_conj_bracket hFE, hEP, hEM, hX]
  rw [hR, hX]
  rw [hX] at hmid
  have hexp : (P * E * L + E * ((0 : Mat2) - iso_vfC m q t • (P * q.1 - q.1 * P) -
      (iso_vfM m q t * q.1 - q.1 * iso_vfM m q t))) * F + E * L * -(F * P) =
      (P * (E * L * F) - E * L * F * P) + E * ((0 : Mat2) - iso_vfC m q t • (P * q.1 - q.1 * P) -
      (iso_vfM m q t * q.1 - q.1 * iso_vfM m q t)) * F := by
    noncomm_ring
  rw [hexp, hmid]
  simp only [smul_sub, neg_smul, show (3 / 2 * (-1) : ℝ) = -(3 / 2) by norm_num]
  noncomm_ring

/-- The vertex flow starts at `q`. -/
lemma ivf_vertexFlow_zero (m : Fin 3) (q : iso_PhasePt) : iso_vertexFlow m q 0 = q := by
  have hG : iso_vfG m q 0 = 1 := (constControl_solution (vertex m) q.1 0).2.2.1
  have hX : iso_vfX m q 0 = q.1 := (constControl_solution (vertex m) q.1 0).2.2.2
  simp only [iso_vertexFlow, hX, iso_vfΛ₁, hG, inv_one, Matrix.one_mul, Matrix.mul_one, iso_vfΛR,
    zero_smul, NormedSpace.exp_zero, intervalIntegral.integral_same, sub_zero]
  ext i j <;> simp

/-! #### Uniqueness for the linear equations (Grönwall) -/

lemma ivf_continuous_of_hasDerivAt {f f' : ℝ → Mat2} (hf : ∀ s, HasDerivAtEntrywise f (f' s) s) :
    Continuous f :=
  continuous_iff_continuousAt.2 fun t ↦
    continuousAt_iff_entrywise.2 fun i j ↦ (hf t i j).continuousAt

/-- Two-sided uniqueness for `f' = G(t, f)` with `G(t, ·)` Lipschitz between `a` and `t`, for
curves differentiable everywhere. -/
lemma ivf_eq_of_hasDerivAt {G : ℝ → Mat2 → Mat2} {f g : ℝ → Mat2} {a t K : ℝ}
    (hG : ∀ s ∈ uIcc a t, ∀ P Q : Mat2, ∀ i j,
      |G s P i j - G s Q i j| ≤ K * ∑ k, ∑ l, |P k l - Q k l|)
    (hf : ∀ s, HasDerivAtEntrywise f (G s (f s)) s)
    (hg : ∀ s, HasDerivAtEntrywise g (G s (g s)) s) (ha : f a = g a) : f t = g t := by
  rcases le_total a t with h | h
  · exact Matrix.ODE_solution_unique_of_bound_Icc (G := G) (K := K)
      (fun s hs P Q i j ↦ hG s (by rw [uIcc_of_le h]; exact Ico_subset_Icc_self hs) P Q i j)
      (ivf_continuous_of_hasDerivAt hf).continuousOn (fun s _ ↦ (hf s).hasDerivWithinAtEntrywise)
      (ivf_continuous_of_hasDerivAt hg).continuousOn (fun s _ ↦ (hg s).hasDerivWithinAtEntrywise)
      ha ⟨h, le_rfl⟩
  · have hrev : ∀ {φ : ℝ → Mat2}, (∀ s, HasDerivAtEntrywise φ (G s (φ s)) s) →
        ∀ s, HasDerivAtEntrywise (fun x ↦ φ (-x)) (-G (-s) (φ (-s))) s := fun {φ} hφ s ↦ by
      have := (hφ (-s)).scomp (h := fun x ↦ -x) (hasDerivAt_neg s)
      rwa [neg_one_smul] at this
    have key := Matrix.ODE_solution_unique_of_bound_Icc (a := -a) (b := -t)
      (G := fun s P ↦ -G (-s) P) (K := K)
      (fun s hs P Q i j ↦ by
        have := hG (-s) (by rw [uIcc_of_ge h]; constructor <;> linarith [hs.1, hs.2]) P Q i j
        change |(-G (-s) P) i j - (-G (-s) Q) i j| ≤ _
        rwa [Matrix.neg_apply, Matrix.neg_apply, neg_sub_neg, abs_sub_comm])
      ((ivf_continuous_of_hasDerivAt (hrev hf)).continuousOn)
      (fun s _ ↦ (hrev hf s).hasDerivWithinAtEntrywise)
      ((ivf_continuous_of_hasDerivAt (hrev hg)).continuousOn)
      (fun s _ ↦ (hrev hg s).hasDerivWithinAtEntrywise)
      (by simpa only [neg_neg] using ha) (show -t ∈ Icc (-a) (-t) from ⟨by linarith, le_rfl⟩)
    simpa only [neg_neg] using key

lemma ivf_abs_le_sum (D : Mat2) (k l : Fin 2) : |D k l| ≤ ∑ i, ∑ j, |D i j| := by
  have h1 : |D k l| ≤ ∑ j, |D k j| :=
    Finset.single_le_sum (f := fun j ↦ |D k j|) (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ l)
  have h2 : ∑ j, |D k j| ≤ ∑ i, ∑ j, |D i j| :=
    Finset.single_le_sum (f := fun i ↦ ∑ j, |D i j|)
      (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) (Finset.mem_univ k)
  linarith

/-- Entrywise bound for the linear part `D ↦ [M, D] - ⟨D, M⟩B` of the costate equation (as
`str_lin_bound`). -/
lemma ivf_lin_bound (M B D : Mat2) {m C : ℝ} (hm : ∀ k l, |M k l| ≤ m)
    (hC : ∀ k l, |B k l| ≤ C) (i j : Fin 2) :
    |((M * D - D * M) - traceForm D M • B) i j| ≤
      (4 * m + 4 * m * C) * ∑ k, ∑ l, |D k l| := by
  set S := ∑ k, ∑ l, |D k l|
  have hD := ivf_abs_le_sum D
  have hm0 : 0 ≤ m := le_trans (abs_nonneg _) (hm 0 0)
  have hS0 : 0 ≤ S := le_trans (abs_nonneg _) (hD 0 0)
  have hp : ∀ a b c d : Fin 2, |M a b * D c d| ≤ m * S := fun a b c d ↦ by
    rw [abs_mul]; exact mul_le_mul (hm _ _) (hD _ _) (abs_nonneg _) hm0
  have hq : ∀ a b c d : Fin 2, |D a b * M c d| ≤ m * S := fun a b c d ↦ by
    rw [abs_mul, mul_comm]; exact mul_le_mul (hm _ _) (hD _ _) (abs_nonneg _) hm0
  have htr : |traceForm D M| ≤ 4 * (m * S) := by
    simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    have := hq 0 0 0 0; have := hq 0 1 1 0; have := hq 1 0 0 1; have := hq 1 1 1 1
    rw [abs_le] at *
    constructor <;> linarith
  have hB : |traceForm D M * B i j| ≤ 4 * (m * S) * C := by
    rw [abs_mul]; exact mul_le_mul htr (hC i j) (abs_nonneg _) (by positivity)
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have := hp i 0 0 j; have := hp i 1 1 j; have := hq i 0 0 j; have := hq i 1 1 j
  rw [abs_le] at *
  constructor <;> nlinarith

/-- The difference of two values of the right-hand side of `eqn:lamR` is linear in `Λ_R`. -/
lemma ivf_costateRHS_sub (lam : ℝ) (Λ₁ P Q X : Mat2) (u : Fin 3 → ℝ) :
    costateRHS lam Λ₁ P X u - costateRHS lam Λ₁ Q X u =
      (controlP u X * (P - Q) - (P - Q) * controlP u X) -
        traceForm (P - Q) (controlP u X) • (controlP u X * X - X * controlP u X) := by
  simp only [costateRHS, traceForm, Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub, sub_smul]
  abel

/-- The costate equation `eqn:lamR` is uniformly Lipschitz in `Λ_R` along a curve `X`, continuous
on a compact set, on which `P = Z_u/⟨Z_u, X⟩` is a constant `P₀`. -/
lemma ivf_costateRHS_lipschitz {X : ℝ → Mat2} {S : Set ℝ} (hS : IsCompact S)
    (hX : ContinuousOn X S) (P₀ : Mat2) :
    ∃ K, ∀ s ∈ S, ∀ (lam : ℝ) (Λ₁ : Mat2) (u : Fin 3 → ℝ), controlP u (X s) = P₀ →
      ∀ P Q : Mat2, ∀ i j, |costateRHS lam Λ₁ P (X s) u i j - costateRHS lam Λ₁ Q (X s) u i j| ≤
        K * ∑ k, ∑ l, |P k l - Q k l| := by
  have hB : ContinuousOn (fun s ↦ P₀ * X s - X s * P₀) S :=
    (continuousOn_const.mul hX).sub (hX.mul continuousOn_const)
  have hBc : ContinuousOn (fun s ↦ ∑ k, ∑ l, |(P₀ * X s - X s * P₀) k l|) S :=
    continuousOn_finsetSum _ fun k _ ↦ continuousOn_finsetSum _ fun l _ ↦
      ((continuousOn_iff_entrywise.1 hB) k l).abs
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hBc
  refine ⟨4 * (∑ k, ∑ l, |P₀ k l|) + 4 * (∑ k, ∑ l, |P₀ k l|) * max C 0,
    fun s hs lam Λ₁ u hu P Q i j ↦ ?_⟩
  rw [← Matrix.sub_apply, ivf_costateRHS_sub, hu]
  exact ivf_lin_bound P₀ _ (P - Q) (ivf_abs_le_sum P₀)
    (fun k l ↦ (ivf_abs_le_sum _ k l).trans ((le_abs_self _).trans
      ((Real.norm_eq_abs _ ▸ hC s hs).trans (le_max_left _ _)))) i j

/-- The Lax equation `Λ₁' = [Λ₁, X]` is uniformly Lipschitz along a curve `X` continuous on a
compact set. -/
lemma ivf_lax_lipschitz {X : ℝ → Mat2} {S : Set ℝ} (hS : IsCompact S) (hX : ContinuousOn X S) :
    ∃ K, ∀ s ∈ S, ∀ P Q : Mat2, ∀ i j,
      |(P * X s - X s * P) i j - (Q * X s - X s * Q) i j| ≤ K * ∑ k, ∑ l, |P k l - Q k l| := by
  have hBc : ContinuousOn (fun s ↦ ∑ k, ∑ l, |X s k l|) S :=
    continuousOn_finsetSum _ fun k _ ↦ continuousOn_finsetSum _ fun l _ ↦
      ((continuousOn_iff_entrywise.1 hX) k l).abs
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hBc
  refine ⟨4 * max C 0, fun s hs P Q i j ↦ ?_⟩
  have h := poly_abs_bracket_le (X s) (P - Q) i j
  have hle : ∑ k, ∑ l, |X s k l| ≤ max C 0 :=
    (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hC s hs).trans (le_max_left _ _))
  rw [← Matrix.sub_apply, show P * X s - X s * P - (Q * X s - X s * Q) =
    -(X s * (P - Q) - (P - Q) * X s) by noncomm_ring, Matrix.neg_apply, abs_neg]
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))

/-- `iso_vertexFlow` solves the state–costate equations with control `e_m` and `λ_cost = -1`, from
`q` at time `0`. -/
theorem iso_vertexFlow_solution (m : Fin 3) (q : iso_PhasePt)
    (hZ : traceForm (controlMatrix (vertex m)) q.1 ≠ 0) (t : ℝ) :
    HasDerivAtEntrywise (fun s ↦ (iso_vertexFlow m q s).1)
        (controlP (vertex m) (iso_vertexFlow m q t).1 * (iso_vertexFlow m q t).1 -
          (iso_vertexFlow m q t).1 * controlP (vertex m) (iso_vertexFlow m q t).1) t ∧
      HasDerivAtEntrywise (fun s ↦ (iso_vertexFlow m q s).2.1)
        ((iso_vertexFlow m q t).2.1 * (iso_vertexFlow m q t).1 -
          (iso_vertexFlow m q t).1 * (iso_vertexFlow m q t).2.1) t ∧
      HasDerivAtEntrywise (fun s ↦ (iso_vertexFlow m q s).2.2)
        (costateRHS (-1) (iso_vertexFlow m q t).2.1 (iso_vertexFlow m q t).2.2
          (iso_vertexFlow m q t).1 (vertex m)) t ∧
      iso_vertexFlow m q 0 = q := by
  -- the hypothesis `⟨Z_{e_m}, X₀⟩ ≠ 0` is not needed: for `⟨Z_{e_m}, X₀⟩ = 0`, `P = 0`
  have _hZ := hZ
  exact ⟨ivf_vfX_hasDerivAt m q t, ivf_vfΛ₁_hasDerivAt m q t, ivf_vfΛR_hasDerivAt m q t,
    ivf_vertexFlow_zero m q⟩

/-- An integral curve on `[0, T]` restricted to `[a, b] ⊆ [0, T]`, with the right-hand side
replaced by a continuous `w` agreeing with it almost everywhere on `(a, b)` (the a.e. version of
`poly_integral_form_restrict`). -/
lemma ivf_integral_form_restrict_ae {f v w : ℝ → Mat2} {T a b : ℝ} (hI : IsIntegralCurve f v T)
    (ha : 0 ≤ a) (hab : a ≤ b) (hbT : b ≤ T) (hw : ContinuousOn w (Icc a b))
    (hvw : ∀ᵐ t, t ∈ Ioo a b → v t = w t) :
    ∀ i j, IntervalIntegrable (fun s ↦ w s i j) volume a b ∧
      ∀ t ∈ Icc a b, f t i j = f a i j + ∫ s in a..t, w s i j := by
  intro i j
  obtain ⟨hint, heq⟩ := hI i j
  have hwij : ContinuousOn (fun s ↦ w s i j) (Icc a b) := continuousOn_iff_entrywise.1 hw i j
  refine ⟨hwij.intervalIntegrable_of_Icc hab, fun t ht ↦ ?_⟩
  have hT : 0 ≤ T := ha.trans (hab.trans hbT)
  have h0a : IntervalIntegrable (fun s ↦ v s i j) volume 0 a := hint.mono_set (by
    rw [uIcc_of_le ha, uIcc_of_le hT]; exact Icc_subset_Icc_right (hab.trans hbT))
  have hat : IntervalIntegrable (fun s ↦ v s i j) volume a t := hint.mono_set (by
    rw [uIcc_of_le ht.1, uIcc_of_le hT]; exact Icc_subset_Icc ha (ht.2.trans hbT))
  have hadd := intervalIntegral.integral_add_adjacent_intervals h0a hat
  have hcongr : ∫ s in a..t, v s i j = ∫ s in a..t, w s i j := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hvw, (countable_singleton b).ae_notMem volume] with s hs hsb hsI
    rw [uIoc_of_le ht.1] at hsI
    rw [hs ⟨hsI.1, lt_of_le_of_ne (hsI.2.trans ht.2) hsb⟩]
  rw [heq t ⟨ha.trans ht.1, ht.2.trans hbT⟩, heq a ⟨ha, hab.trans hbT⟩, ← hcongr, ← hadd]
  ring

/-- On an arc where the control is the vertex `e_m` almost everywhere, a normalized extremal is
the vertex flow from its value at the start of the arc (uniqueness for the linear equations,
Grönwall, as in `poly_trajectory_unique` and `str_costateΛR_unique`). -/
theorem iso_arc_eq_vertexFlow {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    (h : IsPontryaginExtremal T u g X Λ₁ ΛR (-1)) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ T) (m : Fin 3) (hu : ∀ᵐ t, t ∈ Ioo a b → u t = vertex m) :
    ∀ t ∈ Icc a b, (X t, Λ₁ t, ΛR t) = iso_vertexFlow m (X a, Λ₁ a, ΛR a) (t - a) := by
  obtain ⟨⟨-, -, -, hst, -, hXI⟩, -, -, -, -, -, -, -, hI1, hIR, -⟩ := h
  set q : iso_PhasePt := (X a, Λ₁ a, ΛR a) with hq
  have hT : a ≤ T := hab.trans hb
  have hsub : Icc a b ⊆ Icc 0 T := Icc_subset_Icc ha hb
  have haI : a ∈ Icc a b := left_mem_Icc.2 hab
  -- continuity on `[0, T]`
  have hXc : ContinuousOn X (Icc a b) := (Matrix.continuousOn_of_eq_add_integral hXI).mono hsub
  have h1c : ContinuousOn Λ₁ (Icc a b) := (Matrix.continuousOn_of_eq_add_integral hI1).mono hsub
  have hRc : ContinuousOn ΛR (Icc a b) := (Matrix.continuousOn_of_eq_add_integral hIR).mono hsub
  have hstar : ∀ t ∈ Icc a b, IsStarState (X t) := fun t ht ↦ (hst t (hsub ht)).2
  have hvm : vertex m ∈ controlSimplex := poly_vertex_mem m
  have hb' : ∀ᵐ t, t ∈ Ioo a b → u t = vertex m := hu
  -- the vertex flow from `q`, started at time `a`
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
  -- `X`: `⟨X, Z_{e_m}⟩` is constant on the arc (Lemma 7.1.1), then uniqueness for `X' = [P, X]`
  have hwX : ContinuousOn (fun t ↦ controlP (vertex m) (X t) * X t -
      X t * controlP (vertex m) (X t)) (Icc a b) :=
    ((poly_controlP_continuousOn hXc hvm hstar).mul hXc).sub
      (hXc.mul (poly_controlP_continuousOn hXc hvm hstar))
  have hformX := ivf_integral_form_restrict_ae hXI ha hab hb hwX (by
    filter_upwards [hb'] with t ht htI
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
  -- `Λ₁`: uniqueness for the Lax equation `Λ₁' = [Λ₁, X]`
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
  -- `Λ_R`: uniqueness for the costate equation `eqn:lamR`
  have hwR : ContinuousOn (fun t ↦ costateRHS (-1) (Λ₁ t) (ΛR t) (X t) (vertex m)) (Icc a b) :=
    poly_costateRHS_continuousOn (-1) hvm h1c hRc hXc hstar
  have hformR := ivf_integral_form_restrict_ae hIR ha hab hb hwR (by
    filter_upwards [hb'] with t ht htI
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

/-- From `q_fix(y₀)` the `e₃`-flow is the explicit lift of Theorem 7.5.1. -/
theorem iso_vertexFlow_qFix (y0 : ℝ) (hy0 : 1 / √3 < y0) (t : ℝ) :
    iso_vertexFlow 2 (iso_qFix y0) t = (segX y0 t, strongΛ₁ y0 t, strongΛR y0 t) := by
  have hy : 0 < y0 := lt_trans (by positivity) hy0
  have hX : ∀ s, iso_vfX 2 (iso_qFix y0) s = segX y0 s := fun s ↦ rfl
  have h10 : strongΛ₁ y0 0 = strongL₁ y0 • Λ₁₀ y0 := by
    rw [strongΛ₁, str_segG_zero y0 hy, inv_one, Matrix.one_mul, Matrix.mul_one]
  have hΛ₁ : ∀ s, iso_vfΛ₁ 2 (iso_qFix y0) s = strongΛ₁ y0 s := fun s ↦ by
    change (segG y0 s)⁻¹ * strongΛ₁ y0 0 * segG y0 s = strongΛ₁ y0 s
    rw [h10]
    rfl
  -- `Λ_R`: both solve the costate equation along `segX` with `Λ₁ = strongΛ₁` (two-sided
  -- uniqueness, as in `str_costateΛR_unique`)
  obtain ⟨K, hK⟩ := ivf_costateRHS_lipschitz (isCompact_uIcc (a := 0) (b := t))
    (poly_segX_continuous hy).continuousOn !![√3 * y0 / 2, y0; 0, -(√3 * y0 / 2)]
  have hR : iso_vfΛR 2 (iso_qFix y0) t = strongΛR y0 t :=
    ivf_eq_of_hasDerivAt (a := 0)
      (G := fun s P ↦ costateRHS (-1) (strongΛ₁ y0 s) P (segX y0 s) (vertex 2))
      (fun s hs P Q i j ↦ hK s hs (-1) _ (vertex 2) (str_controlP_segX y0 s hy) P Q i j)
      (fun s ↦ by
        have := ivf_vfΛR_hasDerivAt 2 (iso_qFix y0) s
        rwa [hΛ₁, hX] at this)
      (fun s ↦ (costateΛR_solution y0 _ _ _ hy s).1)
      (congrArg (fun p : iso_PhasePt ↦ p.2.2) (ivf_vertexFlow_zero 2 (iso_qFix y0)))
  simp only [iso_vertexFlow, hX, hΛ₁, hR]

end SmoothedPolygons
