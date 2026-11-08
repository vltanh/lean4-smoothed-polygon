module

public import SmoothedPolygons.Ch13.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Chapter 13: symmetries of the Fuller system and the switching functions

§13.2 of Hales–Vajjha, *Packings of Smoothed Polygons* (TeX 10745–10906):

* the polar form of the switching functions (TeX 10755–10784): the angles `θ_{ij}` with
  `u_i - u_j = √3 e^{iθ_{ij}}` (`l4st_sub_eq_sqrt_three_mul_exp`) and
  `χ^k_{ij}(t) = Σ_{m=0}^{3} (t^m/m!) r_{3-m} cos(θ_{3-m} - θ_{ij})`
  (`l4st_switchingFunction_polar`);
* Lemma 13.2.1 (`lem:rescale`): the virial rescaling of solutions;
* Lemma 13.2.2 (`lem:discrete`): the rotation by `ζ`;
* Lemma 13.2.3 (`lem:reversal`): the time reversal `τ`;
* Lemma 13.2.4 (`lem:switch-reversal`): the switching functions under time reversal;
* equation (13.2.7): the switching functions under the rotation by `ζ`;
* the identity `τ(z(-t, z⁰, u)) = z(t, τ(z⁰), ū)`, the first assertion of Lemma 13.2.5
  (`l4st_tau_flow_neg`; Lemma 13.2.5 itself is in `SmoothedPolygons/Ch13/FirstControl.lean`).

The book proves all of them "by direct substitution". For Lemmas 13.2.1–13.2.3, whose solutions
have measurable controls, the substitution is a change of variables `s = t/r` or `s = -t` in the
integral equations of `IsTrajectory`, and the image of a null set is null. Lemma 13.2.3 starts
the reversed solution at the old terminal time `t₂`, so it uses the integral equations between
any two times of `[t₁, t₂]` (`l4b_isTrajectory_integral_eq`; the right-hand sides are integrable
there, `l4b_integrableOn_of_isTrajectory`, because the control is bounded).
-/

@[expose] public section

namespace SmoothedPolygons

open Complex MeasureTheory Set TriFuller

namespace TriFuller

/-! ### Elementary identities -/

private lemma l4b_sqrt3_mul : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)

private lemma l4b_ζ_mem : ζ ∈ VT := by simp [VT]

private lemma l4b_conj_ζ_mul_ζ : starRingEnd ℂ ζ * ζ = 1 := by
  rw [← (l4st_VT_props l4b_ζ_mem l4b_ζ_mem).2.2.2, inv_mul_cancel₀]
  rintro h
  simpa [h] using (l4st_VT_props l4b_ζ_mem l4b_ζ_mem).1

private lemma l4b_ζ_pow_eq_exp (i : ℕ) :
    ζ ^ i = Complex.exp ((2 * Real.pi * i / 3 : ℝ) * I) := by
  rw [ζ, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private lemma l4b_one_sub_ζ : 1 - ζ = √3 * Complex.exp ((-(Real.pi / 6) : ℝ) * I) := by
  rw [l4st_ζ_eq]
  apply Complex.ext
  · rw [Complex.sub_re, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, Real.cos_neg,
      Real.cos_pi_div_six]
    simp only [Complex.one_re]
    nlinarith [l4b_sqrt3_mul]
  · rw [Complex.sub_im, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im, Real.sin_neg,
      Real.sin_pi_div_six]
    simp
    ring

private lemma l4b_one_sub_ζ_sq : 1 - ζ ^ 2 = √3 * Complex.exp ((Real.pi / 6 : ℝ) * I) := by
  rw [l4st_ζ_eq]
  apply Complex.ext
  · rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_six]
    simp [sq]
    nlinarith [l4b_sqrt3_mul]
  · rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im, Real.sin_pi_div_six]
    simp [sq]
    ring

/-- `RR` is additive in its second argument. -/
private lemma l4b_RR_add (a b c : ℂ) : RR a (b + c) = RR a b + RR a c := by
  simp [RR, mul_add]

/-- `RR` is real-homogeneous in its second argument. -/
private lemma l4b_RR_ofReal_mul (a b : ℂ) (s : ℝ) : RR a (s * b) = s * RR a b := by
  simp only [RR]
  rw [mul_left_comm, Complex.re_ofReal_mul]

/-- `RR(e^{iα}, e^{iθ}) = cos(θ - α)`. -/
private lemma l4b_RR_exp (α θ : ℝ) :
    RR (Complex.exp (α * I)) (Complex.exp (θ * I)) = Real.cos (θ - α) := by
  rw [RR, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
    ← Complex.exp_add, show (α : ℂ) * -I + θ * I = ((θ - α : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_ofReal_mul_I_re]

/-- `e^{-iπ/2} = -i`. -/
private lemma l4b_exp_neg_pi_div_two : Complex.exp ((-(Real.pi / 2) : ℝ) * I) = -I := by
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re, Real.cos_neg, Real.cos_pi_div_two]; simp
  · rw [Complex.exp_ofReal_mul_I_im, Real.sin_neg, Real.sin_pi_div_two]; simp

/-- `RR(ā, b̄) = RR(a, b)`. -/
private lemma l4b_RR_conj (a b : ℂ) : RR (starRingEnd ℂ a) (starRingEnd ℂ b) = RR a b := by
  simp [RR, Complex.mul_re]

/-- `RR(va, vb) = RR(a, b)` for `|v| = 1`. -/
private lemma l4b_RR_mul_left {v : ℂ} (hv : starRingEnd ℂ v * v = 1) (a b : ℂ) :
    RR (v * a) (v * b) = RR a b := by
  simp only [RR]
  rw [map_mul, show starRingEnd ℂ v * starRingEnd ℂ a * (v * b) =
    (starRingEnd ℂ v * v) * (starRingEnd ℂ a * b) by ring, hv, one_mul]

/-- The angles `θ_{ij}` of TeX 10771–10778: `u_i - u_j = √3 e^{iθ_{ij}}` with
`θ_{i,i+1} = -π/6 + 2πi/3`, `θ_{i+1,i} = 5π/6 + 2πi/3` and `θ_{i,i-1} = π/6 + 2πi/3`, for the
controls `u_i = ζ^i` (`u_{i-1} = ζ^{i+2}`). -/
theorem l4st_sub_eq_sqrt_three_mul_exp (i : ℕ) :
    ζ ^ i - ζ ^ (i + 1) = √3 * Complex.exp ((-(Real.pi / 6) + 2 * Real.pi * i / 3) * I) ∧
      ζ ^ (i + 1) - ζ ^ i = √3 * Complex.exp ((5 * Real.pi / 6 + 2 * Real.pi * i / 3) * I) ∧
      ζ ^ i - ζ ^ (i + 2) = √3 * Complex.exp ((Real.pi / 6 + 2 * Real.pi * i / 3) * I) := by
  have e1 : ζ ^ i - ζ ^ (i + 1) = √3 * Complex.exp ((-(Real.pi / 6) : ℝ) * I) * ζ ^ i := by
    rw [← l4b_one_sub_ζ]; ring
  have e3 : ζ ^ i - ζ ^ (i + 2) = √3 * Complex.exp ((Real.pi / 6 : ℝ) * I) * ζ ^ i := by
    rw [← l4b_one_sub_ζ_sq]; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [e1, l4b_ζ_pow_eq_exp, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast; ring
  · rw [show ζ ^ (i + 1) - ζ ^ i = -(ζ ^ i - ζ ^ (i + 1)) by ring, e1, l4b_ζ_pow_eq_exp,
      show ((5 * Real.pi / 6 + 2 * Real.pi * i / 3) * I : ℂ) =
        Real.pi * I + ((-(Real.pi / 6) : ℝ) * I + (2 * Real.pi * i / 3 : ℝ) * I) by
        push_cast; ring,
      Complex.exp_add, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  · rw [e3, l4b_ζ_pow_eq_exp, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast; ring

/-- The polar form of the switching functions (TeX 10755–10784). Write the initial condition in
polar coordinates `z_j⁰ = r_j e^{iθ_j}` (`j = 1, 2, 3`), put `r₀ = 1` and `θ₀ = 2πk/3 - π/2`, so
that `z₀⁰ = -iu = r₀ e^{iθ₀}` for the control `u = ζ^k`, and let `d = √3 e^{iα}` (for instance
`d = u_i - u_j`, `α = θ_{ij}`). Then `χ^u_d(t) = RR(e^{iα}, z₃(t, z⁰, u))` and
`χ^u_d(t) = Σ_{m=0}^{3} (t^m/m!) r_{3-m} cos(θ_{3-m} - α)`. Here `r` and `θ` are indexed by
`Fin 4`, with `r 0 = 1` and `θ 0 = 2πk/3 - π/2`. -/
theorem l4st_switchingFunction_polar (k : ℕ) (α : ℝ) (r θ : Fin 4 → ℝ) (hr₀ : r 0 = 1)
    (hθ₀ : θ 0 = 2 * Real.pi * k / 3 - Real.pi / 2) (z : Fin 3 → ℂ)
    (hz : ∀ j : Fin 3, z j = r j.succ * Complex.exp (θ j.succ * I)) (t : ℝ) :
    switchingFunction (ζ ^ k) (√3 * Complex.exp (α * I)) t z =
        RR (Complex.exp (α * I)) (flow t z (ζ ^ k) 2) ∧
      switchingFunction (ζ ^ k) (√3 * Complex.exp (α * I)) t z =
        ∑ m : Fin 4, t ^ (m : ℕ) / (m : ℕ).factorial * r (Fin.rev m) *
          Real.cos (θ (Fin.rev m) - α) := by
  have hsw : switchingFunction (ζ ^ k) (√3 * Complex.exp (α * I)) t z =
      RR (Complex.exp (α * I)) (flow t z (ζ ^ k) 2) := by
    rw [switchingFunction, RR, RR, map_mul, Complex.conj_ofReal, mul_assoc, Complex.re_ofReal_mul]
    have : (0 : ℝ) < √3 := by positivity
    field_simp
  refine ⟨hsw, ?_⟩
  -- `z₀⁰ = -iu = r₀ e^{iθ₀}`
  have hu : -I * ζ ^ k = (r 0 : ℂ) * Complex.exp (θ 0 * I) := by
    rw [hr₀, hθ₀, show ((2 * Real.pi * k / 3 - Real.pi / 2 : ℝ) : ℂ) * I =
        ((2 * Real.pi * k / 3 : ℝ) : ℂ) * I + ((-(Real.pi / 2)) : ℝ) * I by push_cast; ring,
      Complex.exp_add, l4b_exp_neg_pi_div_two, ← l4b_ζ_pow_eq_exp]
    push_cast; ring
  have hflow : flow t z (ζ ^ k) 2 =
      z 2 + (t : ℂ) * z 1 + ((t ^ 2 / 2 : ℝ) : ℂ) * z 0 + ((t ^ 3 / 6 : ℝ) : ℂ) * (-I * ζ ^ k) := by
    simp [flow]; ring
  have hz0 : z 0 = (r 1 : ℂ) * Complex.exp (θ 1 * I) := hz 0
  have hz1 : z 1 = (r 2 : ℂ) * Complex.exp (θ 2 * I) := hz 1
  have hz2 : z 2 = (r 3 : ℂ) * Complex.exp (θ 3 * I) := hz 2
  rw [hsw, hflow, hu, hz0, hz1, hz2]
  simp only [l4b_RR_add, l4b_RR_ofReal_mul, l4b_RR_exp, Fin.sum_univ_four]
  have e0 : Fin.rev (0 : Fin 4) = 3 := rfl
  have e1 : Fin.rev (1 : Fin 4) = 2 := rfl
  have e2 : Fin.rev (2 : Fin 4) = 1 := rfl
  have e3 : Fin.rev (3 : Fin 4) = 0 := rfl
  rw [e0, e1, e2, e3]
  norm_num [Nat.factorial]
  ring

/-- `τ(z(-t, z⁰, u)) = z(t, τ(z⁰), ū)` for all `t`, `z⁰` and `u ∈ ℂ` (the first assertion of
Lemma 13.2.5, TeX 10893–10895; a polynomial identity, by direct substitution in (13.2.2)). -/
theorem l4st_tau_flow_neg (t : ℝ) (z : Fin 3 → ℂ) (u : ℂ) :
    tau (flow (-t) z u) = flow t (tau z) (starRingEnd ℂ u) := by
  funext j
  fin_cases j <;>
    simp [tau, flow, map_sub, map_add, map_mul, map_neg, map_div₀, map_ofNat] <;> ring

/-- `τ` is an involution. -/
theorem l4st_tau_tau (z : Fin 3 → ℂ) : tau (tau z) = z := by
  funext j
  fin_cases j <;> simp [tau]

/-- The Hamiltonian under time reversal: `H_F(τ z, v) = H_F(z, v̄)` (from
`RR(z̄₁, -i z̄₂) = RR(z₁, i z₂)`, TeX 10846–10860). -/
theorem l4st_ham_tau (z : Fin 3 → ℂ) (v : ℂ) : ham (tau z) v = ham z (starRingEnd ℂ v) := by
  simp [ham, RR, tau, Complex.mul_re, Complex.mul_im]
  ring

/-- The Hamiltonian under the virial group: `H_F(v·(r z₁, r² z₂, r³ z₃), v u) = r³ H_F(z, u)` for
`|v| = 1`. -/
theorem l4st_ham_smul_scale {v : ℂ} (hv : ‖v‖ = 1) (r : ℝ) (z : Fin 3 → ℂ) (u : ℂ) :
    ham (v • scale r z) (v * u) = r ^ 3 * ham z u := by
  have hv' : starRingEnd ℂ v * v = 1 := by
    rw [Complex.conj_mul', hv]; simp
  simp only [ham, scale, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  rw [show v * (r ^ 2 * z 1) * I = v * (r ^ 2 * z 1 * I) by ring, l4b_RR_mul_left hv',
    l4b_RR_mul_left hv', show ((r : ℂ) ^ 3 * z 2) = ((r ^ 3 : ℝ) : ℂ) * z 2 by push_cast; ring,
    l4b_RR_ofReal_mul, show ((r : ℂ) ^ 2 * z 1 * I) = ((r ^ 2 : ℝ) : ℂ) * (z 1 * I) by
      push_cast; ring, l4b_RR_ofReal_mul]
  simp only [RR, map_mul, Complex.conj_ofReal]
  rw [mul_assoc, Complex.re_ofReal_mul]
  ring

end TriFuller

/-! ### Trajectories: integrability and the integral equations between any two times -/

private lemma l4b_scale_zero (r : ℝ) (w : Fin 3 → ℂ) : scale r w 0 = r * w 0 := rfl
private lemma l4b_scale_one (r : ℝ) (w : Fin 3 → ℂ) : scale r w 1 = r ^ 2 * w 1 := rfl
private lemma l4b_scale_two (r : ℝ) (w : Fin 3 → ℂ) : scale r w 2 = r ^ 3 * w 2 := rfl
private lemma l4b_tau_zero (w : Fin 3 → ℂ) : tau w 0 = starRingEnd ℂ (w 0) := rfl
private lemma l4b_tau_one (w : Fin 3 → ℂ) : tau w 1 = -starRingEnd ℂ (w 1) := rfl
private lemma l4b_tau_two (w : Fin 3 → ℂ) : tau w 2 = starRingEnd ℂ (w 2) := rfl

private lemma l4b_scale_one_eq (w : Fin 3 → ℂ) : scale 1 w = w := by
  funext j; fin_cases j <;> simp [scale]

private lemma l4b_norm_le_of_mem_VT {v : ℂ} (hv : v ∈ VT) : ‖v‖ ≤ 1 :=
  (l4st_VT_props hv hv).1.le

/-- Along a trajectory of the Fuller system whose controls are bounded by `C`, the right-hand
sides `-iu`, `z₁`, `z₂` are integrable on `[t₁, t₂]` (the control is measurable and bounded; then
`z₁` and `z₂` are continuous there, as indefinite integrals). -/
theorem l4b_integrableOn_of_isTrajectory {U : Set ℂ} {C : ℝ} (hUb : ∀ v ∈ U, ‖v‖ ≤ C)
    {t₁ t₂ : ℝ} {z : ℝ → Fin 3 → ℂ} {u : ℝ → ℂ} (h : IsTrajectory U t₁ t₂ z u) :
    IntegrableOn (fun s ↦ -I * u s) (Icc t₁ t₂) ∧ IntegrableOn (fun s ↦ z s 0) (Icc t₁ t₂) ∧
      IntegrableOn (fun s ↦ z s 1) (Icc t₁ t₂) := by
  obtain ⟨h12, hmeas, hU, hint⟩ := h
  have hI : uIcc t₁ t₂ = Icc t₁ t₂ := uIcc_of_le h12.le
  have i0 : IntegrableOn (fun s ↦ -I * u s) (Icc t₁ t₂) := by
    refine Measure.integrableOn_of_bounded (M := C) measure_Icc_lt_top.ne
      (measurable_const.mul hmeas).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    simpa using hUb _ (hU s hs)
  have c0 : ContinuousOn (fun s ↦ z s 0) (Icc t₁ t₂) := by
    have := intervalIntegral.continuousOn_primitive_interval (a := t₁) (b := t₂)
      (μ := volume) (f := fun s ↦ -I * u s) (by rwa [hI])
    rw [hI] at this
    exact (continuousOn_const.add this).congr fun s hs ↦ (hint s hs).1
  have c1 : ContinuousOn (fun s ↦ z s 1) (Icc t₁ t₂) := by
    have := intervalIntegral.continuousOn_primitive_interval (a := t₁) (b := t₂)
      (μ := volume) (f := fun s ↦ z s 0) (by rw [hI]; exact c0.integrableOn_Icc)
    rw [hI] at this
    exact (continuousOn_const.add this).congr fun s hs ↦ (hint s hs).2.1
  exact ⟨i0, c0.integrableOn_Icc, c1.integrableOn_Icc⟩

/-- The integral equations of a trajectory of the Fuller system (with controls bounded by `C`)
hold between any two times `a, b ∈ [t₁, t₂]`, not only from `t₁`. -/
theorem l4b_isTrajectory_integral_eq {U : Set ℂ} {C : ℝ} (hUb : ∀ v ∈ U, ‖v‖ ≤ C)
    {t₁ t₂ : ℝ} {z : ℝ → Fin 3 → ℂ} {u : ℝ → ℂ} (h : IsTrajectory U t₁ t₂ z u) {a b : ℝ}
    (ha : a ∈ Icc t₁ t₂) (hb : b ∈ Icc t₁ t₂) :
    z b 0 = z a 0 + ∫ s in a..b, -I * u s ∧ z b 1 = z a 1 + ∫ s in a..b, z s 0 ∧
      z b 2 = z a 2 + ∫ s in a..b, z s 1 := by
  obtain ⟨i0, i1, i2⟩ := l4b_integrableOn_of_isTrajectory hUb h
  have hI : uIcc t₁ t₂ = Icc t₁ t₂ := uIcc_of_le h.1.le
  have hsub : ∀ c ∈ Icc t₁ t₂, uIcc t₁ c ⊆ uIcc t₁ t₂ := fun c hc ↦
    uIcc_subset_uIcc left_mem_uIcc (by rw [hI]; exact hc)
  have key : ∀ f : ℝ → ℂ, IntegrableOn f (Icc t₁ t₂) → ∀ w : ℝ → ℂ,
      (∀ c ∈ Icc t₁ t₂, w c = w t₁ + ∫ s in t₁..c, f s) → w b = w a + ∫ s in a..b, f s := by
    intro f hf w hw
    have hf' : IntervalIntegrable f volume t₁ t₂ :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le h.1.le).2 hf
    rw [hw b hb, hw a ha, ← intervalIntegral.integral_interval_sub_left
      (hf'.mono_set (hsub b hb)) (hf'.mono_set (hsub a ha))]
    ring
  obtain ⟨-, -, -, hint⟩ := h
  exact ⟨key _ i0 (fun c ↦ z c 0) fun c hc ↦ (hint c hc).1,
    key _ i1 (fun c ↦ z c 1) fun c hc ↦ (hint c hc).2.1,
    key _ i2 (fun c ↦ z c 2) fun c hc ↦ (hint c hc).2.2⟩

/-- **Lemma 13.2.1** (`lem:rescale`, TeX 10794–10802). If `(z₁, z₂, z₃, u)` is a solution of the
Fuller system on `[t₁, t₂]` satisfying (13.2.5) and (13.2.6), then so is
`(z̃₁, z̃₂, z̃₃, ũ)` on `[r t₁, r t₂]`, where `z̃_j(t) = r^j z_j(t/r)`, `ũ(t) = u(t/r)` and `r > 0`.

Proof (book: "direct substitution into the Fuller system and into the Hamiltonian"): the change
of variables `s = σ/r` in the integral equations gives `z̃₁' = -iũ`, `z̃₂' = z̃₁`, `z̃₃' = z̃₂`
(`r^j · (1/r) · z_{j-1}(t/r) = z̃_{j-1}(t)`); `H_F(z̃(t), v) = r³ H_F(z(t/r), v)` for every `v`
(`l4st_ham_smul_scale` with `v = 1`), and `r³ > 0`, so (13.2.5) and (13.2.6) are preserved; the
exceptional null set is dilated by `r`. -/
theorem lemma13_2_1 {t₁ t₂ r : ℝ} {z : ℝ → Fin 3 → ℂ} {u : ℝ → ℂ} (h : IsExtremal t₁ t₂ z u)
    (hr : 0 < r) :
    IsExtremal (r * t₁) (r * t₂) (fun t ↦ scale r (z (t / r))) (fun t ↦ u (t / r)) := by
  obtain ⟨⟨h12, hmeas, hU, hint⟩, hmax, hH⟩ := h
  have hr0 : r ≠ 0 := hr.ne'
  have hdiv : ∀ t ∈ Icc (r * t₁) (r * t₂), t / r ∈ Icc t₁ t₂ := fun t ht ↦
    ⟨(le_div_iff₀ hr).2 (by linarith [ht.1]), (div_le_iff₀ hr).2 (by linarith [ht.2])⟩
  have hrt : r * t₁ / r = t₁ := by field_simp
  -- `H_F(z̃(t), v) = r³ H_F(z(t/r), v)`
  have hham : ∀ w v, ham (scale r w) v = r ^ 3 * ham w v := fun w v ↦ by
    simpa using l4st_ham_smul_scale (v := 1) (by simp) r w v
  -- the exceptional null set is dilated by `r`
  have hq : QuasiMeasurePreserving (fun t : ℝ ↦ t / r) volume volume := by
    have := Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) (inv_ne_zero hr0)
    convert this using 1
    funext t
    simp [div_eq_inv_mul]
  -- the change of variables `s = σ / r`
  have hcv : ∀ (f : ℝ → ℂ) (t : ℝ), ∫ s in r * t₁..t, f (s / r) = r * ∫ s in t₁..t / r, f s := by
    intro f t
    rw [intervalIntegral.integral_comp_div f hr0, hrt, Complex.real_smul]
  refine ⟨⟨by nlinarith, hmeas.comp (measurable_id.div_const r), fun t ht ↦ hU _ (hdiv t ht),
    fun t ht ↦ ?_⟩, ?_, ?_⟩
  · obtain ⟨e0, e1, e2⟩ := hint (t / r) (hdiv t ht)
    simp only [l4b_scale_zero, l4b_scale_one, l4b_scale_two, hrt]
    refine ⟨?_, ?_, ?_⟩
    · rw [hcv (fun s ↦ -I * u s), e0]; ring
    · rw [intervalIntegral.integral_const_mul, hcv (fun s ↦ z s 0), e1]; ring
    · rw [intervalIntegral.integral_const_mul, hcv (fun s ↦ z s 1), e2]; ring
  · filter_upwards [hq.ae hmax] with t ht hmem v hv
    rw [hham, hham]
    exact mul_le_mul_of_nonneg_left (ht (hdiv t hmem) v hv) (by positivity)
  · filter_upwards [hq.ae hH] with t ht hmem
    rw [hham, ht (hdiv t hmem), mul_zero]

/-- **Lemma 13.2.2** (`lem:discrete`, TeX 10809–10818). If `(z₁, z₂, z₃, u)` is a solution of the
Fuller system satisfying (13.2.5) and (13.2.6) with initial value `z⁰`, then
`(ζz₁, ζz₂, ζz₃, ζu)` is a solution satisfying the same constraints, with initial value `ζz⁰`
(the initial value of `t ↦ ζ • z t` at `t₁` is `ζ • z t₁` by definition).

Proof (book: "direct substitution"): the integral equations are `ℂ`-linear; `ζ V_T = V_T`; and
`H_F(ζ z, ζ v) = H_F(z, v)` because `|ζ| = 1` (`l4st_ham_smul_scale` with `r = 1`). -/
theorem lemma13_2_2 {t₁ t₂ : ℝ} {z : ℝ → Fin 3 → ℂ} {u : ℝ → ℂ} (h : IsExtremal t₁ t₂ z u) :
    IsExtremal t₁ t₂ (fun t ↦ ζ • z t) (fun t ↦ ζ * u t) := by
  obtain ⟨⟨h12, hmeas, hU, hint⟩, hmax, hH⟩ := h
  -- `H_F(ζ w, ζ v) = H_F(w, v)`
  have hham : ∀ w v, ham (ζ • w) (ζ * v) = ham w v := fun w v ↦ by
    simpa [l4b_scale_one_eq] using
      l4st_ham_smul_scale (l4st_VT_props l4b_ζ_mem l4b_ζ_mem).1 1 w v
  have hconj : starRingEnd ℂ ζ ∈ VT := (l4st_VT_props l4b_ζ_mem l4b_ζ_mem).2.2.1
  refine ⟨⟨h12, hmeas.const_mul ζ, fun t ht ↦ (l4st_VT_props l4b_ζ_mem (hU t ht)).2.1,
    fun t ht ↦ ?_⟩, ?_, ?_⟩
  · obtain ⟨e0, e1, e2⟩ := hint t ht
    simp only [Pi.smul_apply, smul_eq_mul]
    refine ⟨?_, ?_, ?_⟩
    · rw [e0, mul_add, ← intervalIntegral.integral_const_mul]
      congr 1
      exact intervalIntegral.integral_congr fun s _ ↦ by ring
    · rw [e1, mul_add, intervalIntegral.integral_const_mul]
    · rw [e2, mul_add, intervalIntegral.integral_const_mul]
  · filter_upwards [hmax] with t ht hmem v hv
    have hv' : v = ζ * (starRingEnd ℂ ζ * v) := by
      rw [← mul_assoc, mul_comm ζ, l4b_conj_ζ_mul_ζ, one_mul]
    rw [hv', hham, hham]
    exact ht hmem _ (l4st_VT_props hconj hv).2.1
  · filter_upwards [hH] with t ht hmem
    rw [hham]
    exact ht hmem

/-- **Lemma 13.2.3** (`lem:reversal`, TeX 10844–10856). If `(z₁, z₂, z₃, u)` is a solution of the
Fuller system on `[t₁, t₂]` satisfying (13.2.5) and (13.2.6), then
`(z̄₁(-t), -z̄₂(-t), z̄₃(-t), ū(-t))`, that is `t ↦ τ(z(-t))` with control `t ↦ ū(-t)`, is a
solution on `[-t₂, -t₁]` satisfying the same constraints, with terminal value `τ(z⁰)` (its value
at `-t₁` is `τ(z(t₁))` by definition).

Proof (book: "direct substitution"): the change of variables `s ↦ -s` in the integral equations,
written between the endpoints `t₂` and `-t`; `conj V_T = V_T`; and
`H_F(τ w, v̄) = H_F(w, v)` (`l4st_ham_tau`). -/
theorem lemma13_2_3 {t₁ t₂ : ℝ} {z : ℝ → Fin 3 → ℂ} {u : ℝ → ℂ} (h : IsExtremal t₁ t₂ z u) :
    IsExtremal (-t₂) (-t₁) (fun t ↦ tau (z (-t))) (fun t ↦ starRingEnd ℂ (u (-t))) := by
  have htraj := h.1
  obtain ⟨⟨h12, hmeas, hU, -⟩, hmax, hH⟩ := h
  have hneg : ∀ t ∈ Icc (-t₂) (-t₁), -t ∈ Icc t₁ t₂ := fun t ht ↦
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have ht₂ : t₂ ∈ Icc t₁ t₂ := ⟨h12.le, le_rfl⟩
  -- the exceptional null set is reflected
  have hq : QuasiMeasurePreserving (fun t : ℝ ↦ -t) volume volume := by
    have := Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) (r := -1) (by norm_num)
    convert this using 1
    funext t
    simp
  refine ⟨⟨by linarith, Complex.continuous_conj.measurable.comp (hmeas.comp measurable_neg),
    fun t ht ↦ (l4st_VT_props (hU _ (hneg t ht)) (hU _ (hneg t ht))).2.2.1, fun t ht ↦ ?_⟩, ?_, ?_⟩
  · -- the integral equations written between the endpoints `-t` and `t₂`
    obtain ⟨e0, e1, e2⟩ := l4b_isTrajectory_integral_eq (fun _ hv ↦ l4b_norm_le_of_mem_VT hv)
      htraj (hneg t ht) ht₂
    simp only [neg_neg, l4b_tau_zero, l4b_tau_one, l4b_tau_two]
    -- the change of variables `s ↦ -s`
    rw [intervalIntegral.integral_comp_neg (fun s ↦ -I * starRingEnd ℂ (u s)),
      intervalIntegral.integral_comp_neg (fun s ↦ starRingEnd ℂ (z s 0)),
      intervalIntegral.integral_comp_neg (fun s ↦ -starRingEnd ℂ (z s 1)), neg_neg,
      intervalIntegral.integral_neg, intervalIntegral.intervalIntegral_conj,
      intervalIntegral.intervalIntegral_conj,
      intervalIntegral.integral_congr (g := fun s ↦ -starRingEnd ℂ (-I * u s))
        fun s _ ↦ by simp]
    rw [intervalIntegral.integral_neg, intervalIntegral.intervalIntegral_conj, e0, e1, e2]
    refine ⟨?_, ?_, ?_⟩ <;> simp only [map_add] <;> ring
  · filter_upwards [hq.ae hmax] with t ht hmem v hv
    rw [l4st_ham_tau, l4st_ham_tau, Complex.conj_conj]
    exact ht (hneg t hmem) _ (l4st_VT_props hv hv).2.2.1
  · filter_upwards [hq.ae hH] with t ht hmem
    rw [l4st_ham_tau, Complex.conj_conj]
    exact ht (hneg t hmem)

/-- **Lemma 13.2.4** (`lem:switch-reversal`, TeX 10862–10871). Let `t₀ ∈ ℝ`, `z⁰ ∈ ℂ³` and
`u ∈ ℂ`, and let `z* = z(t₀, z⁰, u)` be the value at `t₀` of the solution with constant control
`u`. For all `v₁, v₂ ∈ ℂ`,
`χ^u_{v₁-v₂}(t₀ - t, z⁰) = χ^{ū}_{v̄₁-v̄₂}(t, τ(z*))`.

Proof (book: "direct substitution"; an identity of cubic polynomials in `t`): by the flow property
(`l4st_flow_add`) and `l4st_tau_flow_neg`, `z₃(t, τ(z*), ū) = conj z₃(t₀ - t, z⁰, u)`, and
`RR(d̄, w̄) = RR(d, w)`. -/
theorem lemma13_2_4 (t₀ : ℝ) (z : Fin 3 → ℂ) (u v₁ v₂ : ℂ) (t : ℝ) :
    switchingFunction u (v₁ - v₂) (t₀ - t) z =
      switchingFunction (starRingEnd ℂ u) (starRingEnd ℂ v₁ - starRingEnd ℂ v₂) t
        (tau (flow t₀ z u)) := by
  simp only [switchingFunction]
  rw [← l4st_tau_flow_neg, ← l4st_flow_add, ← sub_eq_add_neg, l4b_tau_two, ← map_sub,
    l4b_RR_conj]

/-- **Equation (13.2.7)** (TeX 10874–10877): invariance of the switching functions under the
rotation by `ζ`, `χ^{ζu}_{ζ(v₁-v₂)}(t, ζz⁰) = χ^u_{v₁-v₂}(t, z⁰)` (here with `d = v₁ - v₂`).
Proof: `z₃(t, ζz⁰, ζu) = ζ z₃(t, z⁰, u)` and `RR(ζa, ζb) = RR(a, b)`. -/
theorem eqn13_2_7 (u d : ℂ) (t : ℝ) (z : Fin 3 → ℂ) :
    switchingFunction (ζ * u) (ζ * d) t (ζ • z) = switchingFunction u d t z := by
  have h : flow t (ζ • z) (ζ * u) 2 = ζ * flow t z u 2 := by
    simp [flow]; ring
  simp only [switchingFunction]
  rw [h, l4b_RR_mul_left l4b_conj_ζ_mul_ζ]

end SmoothedPolygons
