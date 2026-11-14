module

public import SmoothedPolygons.Ch15.Continuity

/-!
# Chapter 15: the involution `𝔦 = τ F`, the partition `𝒟₀, …, 𝒟₄` (§15.3)

§15.3 of Hales–Vajjha, *Packings of Smoothed Polygons* ("Involution", TeX 12316–12493):

* `F⁻¹ = τ F τ` and the involution `𝔦 := τ ∘ F` (TeX 12324–12328), made precise (gap G15.6):
  - for the Poincaré map `poincare`, `F(τ F(z)) = τ(z)` holds exactly at the **switching points**,
    the points whose first control is not also their most recent control
    (`poincare_tau_poincare_eq_tau_iff`); every image `F(z)` is a switching point, and the points of
    the top faces `𝒞₂(ζ^{±1}, 0, 2)` are not (`not_isSwitchingPoint_of_mem_topFace`), so the book's
    identity on the closed 3-cells fails there for `poincare` (for example
    `z = (-0.3 + 0.7i, -0.6, -0.84) ∈ 𝒞₂(ζ, 0, 2)`: `t_sw(z) = 5.18584`, `t_sw(τ F z) = 9.38584`);
  - for the book's root-based branch maps it holds **branch-wise**: switching at a time `T` with a
    control `u`, then reversing, switching at the same time `T` with `ū` and reversing again is the
    identity (`tau_flow_tau_flow`);
  - on `Ξ_{𝒲,0}/V_T`: `isSwitchingPointQ_poincareAngZero`,
    `poincareAngZero_tauZero_poincareAngZero`, `involution_involution`;
* "in involution" (`InInvolution`), the loci `∂_res = 𝔦(𝒞₂(ζ, 1, 1))`, `∂_A = 𝔦(𝒞₂(ζ, 0, 2))`,
  `∂_{A,ζ²} = 𝔦(𝒞₂^A)` (with the book's `F_A`), `∂_B = 𝔦(𝒞₂^B)`, and the vanishing of the resultant
  and discriminants along them (from Lemma 13.2.4, TeX 12336–12345, 12425–12427, 12441–12443);
* the parts `𝒟₀, …, 𝒟₄` (TeX 12347–12443), the notion of geometric partition, and Proposition
  15.3.2 as the named proposition `Proposition15_3_2`;
* Remark 15.3.1 (with `q_in` and `q_out` corrected, gap G15.1) is in
  `SmoothedPolygons/Ch15/FixedPointCells.lean`.

## The parts

The book defines `𝒟₁` as "the part of the geometric partition [of the first big cell by
`∂_res ∪ ∂_A`] containing the face `𝒞₂(ζ, 0, 2)`", `𝒟₂`, `𝒟₃` as the two parts of the second big
cell cut by `∂_{A,ζ²}`, with active switching functions `χ_{A,0}` and `χ_{B,1}`, `𝒟₄ := 𝔦(𝒟₃)` and
`𝒟₀ := closure(𝒞₃(ζ) ∖ (𝒟₁ ∪ 𝒟₄))`. Here the parts with a given active switching function are
defined directly by the switch of `poincare` on the open boxes (`switchSet`: the first control of
`F(z)` is `1` when the active function is `χ_A`, and `ū` when it is `χ_B`): `𝒟₂`, `𝒟₃` and `𝒟₄` are
the closures of these sets; `𝒟₁` is the closure of the union of the connected components of the
open first box minus `∂_A ∪ ∂_res` whose closures meet the top face; `𝒟₀` is as in the book. That
these coincide with the book's construction (`𝔦(𝒟₃) = 𝒟₄`), form geometric partitions, and carry
continuous extensions `F_i` of `F` is the content of Proposition 15.3.2, which the book supports
only by Figures 15.2–15.3 ("The proof is contained in the discussion leading up to the
proposition"; gap G15.2). It is stated here as the named proposition `Proposition15_3_2`, to be
certified (layer 5b) or kept as a hypothesis; **Theorem 16.1.1 does not use it**
(`SmoothedPolygons/Ch16/GlobalBasin.lean` works with boxes and the switch of `poincare` directly).

## Proofs

The switching-point facts follow from Lemma 13.2.5 (`lemma13_2_5`, `poincare_tau_poincare`):
`F(z)` has most recent control the first control of `z`, which differs from its own first control
(`firstControl_poincare_ne`); `τ` exchanges first and most recent controls (conjugated). The
vanishing along the `∂`-loci: by Lemma 13.2.4 (`lemma13_2_4`) the switching functions at
`τ(z(T, z⁰, u))` with control `ū` are those at `z⁰` reversed in time about `T`, so a root of order
`m` at `t = 0` at `z⁰` becomes a root of order `m` at `t = T`; the rotation (13.2.7)
(`eqn13_2_7`) and the rescaling (Lemma 13.2.1) bring the point to cell coordinates, multiplying the
switching functions by positive constants and rescaling time. Along `∂_res` the common root comes
directly from the trajectory reversal of Lemma 13.2.5 (`tau_flow_tau_flow`), which returns to
`z₃ = 0` at the switching time.
-/

@[expose] public section

namespace SmoothedPolygons

open Complex Set Filter Topology Polynomial
open scoped Real

namespace TriFuller

/-! ### Switching points and `F⁻¹ = τ F τ` -/

/-- `z` is a **switching point**: its first control is not also its most recent control, so the
extremal through `z` switches at `z` (TeX 10880–10906). -/
def IsSwitchingPoint (z : Fin 3 → ℂ) : Prop := ¬ IsMostRecentControl z (firstControl z)

/-! ### Helpers -/

/-- Time reversal of the Hamiltonian along constant-control trajectories (Lemma 13.2.5,
`tau_flow_neg`, `ham_tau`): `H_F(z(s, τ z, ū), x) = H_F(z(-s, z, u), x̄)`. -/
private lemma l5d_ham_flow_tau (s : ℝ) (z : Fin 3 → ℂ) (u x : ℂ) :
    ham (flow s (tau z) (starRingEnd ℂ u)) x = ham (flow (-s) z u) (starRingEnd ℂ x) := by
  rw [← tau_flow_neg, ham_tau]

private lemma l5d_smul_scale_ne_zero {v : ℂ} (hv : v ∈ VT) {r : ℝ} (hr : 0 < r)
    {z : Fin 3 → ℂ} (hz : z ≠ 0) : v • scale r z ≠ 0 :=
  smul_ne_zero (ne_zero_of_mem_VT hv) (scale_ne_zero hr hz)

/-- The first control under the virial group (`poincare_smul`, `poincare_scale`). -/
private lemma l5d_firstControl_smul_scale {v : ℂ} (hv : v ∈ VT) {r : ℝ} (hr : 0 < r)
    {z : Fin 3 → ℂ} (hz : z ≠ 0) : firstControl (v • scale r z) = v * firstControl z := by
  rw [(poincare_smul hv (scale_ne_zero hr hz)).1, (poincare_scale hr hz).1]

/-- A point `z ≠ 0` is a switching point exactly when its first control is not the conjugate of
the first control of `τ z` (the most recent control of `z`, Lemma 13.2.5). -/
private lemma l5d_isSwitchingPoint_iff {z : Fin 3 → ℂ} (hz : z ≠ 0) :
    IsSwitchingPoint z ↔ starRingEnd ℂ (firstControl (tau z)) ≠ firstControl z := by
  unfold IsSwitchingPoint
  rw [isMostRecentControl_iff_isFirstControl_tau, ← firstControl_eq_iff (tau_ne_zero hz)]
  constructor
  · intro h e
    exact h (by rw [← e, Complex.conj_conj])
  · intro h e
    exact h (by rw [e, Complex.conj_conj])

/-- The first control of `z` is the most recent control of `F(z)`. -/
private lemma l5d_isMostRecentControl_poincare {z : Fin 3 → ℂ} (hz : z ≠ 0) :
    IsMostRecentControl (poincare z) (firstControl z) := by
  refine ⟨firstControl_mem_VT z, firstSwitchTime z, firstSwitchTime_pos hz, fun t ht v hv ↦ ?_⟩
  have e : flow t (poincare z) (firstControl z) =
      flow (firstSwitchTime z + t) z (firstControl z) := by
    rw [poincare, flow_add]
  rw [e]
  exact firstControl_maximizes hz _ ⟨by linarith [ht.1], by linarith [ht.2]⟩ v hv

/-- The first control of `τ F(z)` is the conjugate of the first control of `z` (Lemma 13.2.5). -/
private lemma l5d_firstControl_tau_poincare {z : Fin 3 → ℂ} (hz : z ≠ 0) :
    firstControl (tau (poincare z)) = starRingEnd ℂ (firstControl z) :=
  (firstControl_eq_iff (tau_ne_zero (poincare_ne_zero hz))).2
    (isMostRecentControl_iff_isFirstControl_tau.1 (l5d_isMostRecentControl_poincare hz))

/-- A switching point is not a point at which one control is optimal on a neighbourhood of
`t = 0`. -/
private lemma l5d_not_isSwitchingPoint_of_eventually {z : Fin 3 → ℂ} (hz : z ≠ 0) {u : ℂ}
    (hu : u ∈ VT) (h : ∀ᶠ t in 𝓝 0, ∀ v ∈ VT, ham (flow t z u) v ≤ ham (flow t z u) u) :
    ¬ IsSwitchingPoint z := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 h
  have hin : ∀ t ∈ Icc (-(ε / 2)) (ε / 2), dist t 0 < ε := by
    intro t ht
    rw [Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  have hfc : firstControl z = u :=
    (firstControl_eq_iff hz).2 ⟨hu, ε / 2, by linarith, fun t ht ↦
      hball (hin t ⟨by linarith [ht.1], ht.2⟩)⟩
  unfold IsSwitchingPoint
  rw [hfc, not_not]
  exact ⟨hu, ε / 2, by linarith, fun t ht ↦ hball (hin t ⟨ht.1, by linarith [ht.2]⟩)⟩

/-- The coordinates of `cellPoint p` that the top faces need. -/
private lemma l5d_cellPoint_apply (p : Fin 3 → ℝ) :
    (cellPoint p 0).im = (1 - p 0) * Real.sin (p 2 - p 1) ∧
      (cellPoint p 1).im = p 0 * Real.sin (p 2) ∧ (cellPoint p 2).im = 0 ∧
      (cellPoint p 2).re = -2 * (1 - p 0) * p 0 * Real.sin (p 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [cellPoint, Matrix.cons_val_zero]
    rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  · simp only [cellPoint, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  · simp only [cellPoint, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
      Complex.ofReal_im]
  · simp only [cellPoint, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
      Complex.ofReal_re]

/-- On a top face `θ₂ ∈ {0, π}` (`z₂` real, `z₃ < 0` real), the control `u` is optimal on a whole
neighbourhood of `t = 0` when it is `ζ` and `Im z₁ > 0`, or `ζ²` and `Im z₁ < 0`: the switching
function to `1` is positive at `0`, the one to `ū` is `±√3 t² (Im z₁/2 ± t/12)`, a double root. -/
private lemma l5d_eventually_topFace {z : Fin 3 → ℂ} (h1 : (z 1).im = 0) (h2 : (z 2).im = 0)
    (h3 : (z 2).re < 0) {u : ℂ}
    (hu : (u = ζ ∧ 0 < (z 0).im) ∨ (u = ζ ^ 2 ∧ (z 0).im < 0)) :
    ∀ᶠ t in 𝓝 0, ∀ v ∈ VT, ham (flow t z u) v ≤ ham (flow t z u) u := by
  have h3' : 0 < √3 := by positivity
  have hcont : ∀ v : ℂ, Continuous fun t : ℝ ↦ ham (flow t z u) u - ham (flow t z u) v := by
    intro v
    simp_rw [ham_flow_sub_ham_flow]
    fun_prop
  have key : ∀ v ∈ VT, ∀ᶠ t in 𝓝 0, 0 ≤ ham (flow t z u) u - ham (flow t z u) v := by
    intro v hv
    -- the switching function to `1` is positive at `t = 0`
    have h1pos : 0 < ham (flow 0 z u) u - ham (flow 0 z u) 1 := by
      rw [ham_flow_sub_ham_flow]
      rcases hu with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
        simp [RR_eq_re_mul_add_im_mul, h2, ζ_re, ζ_sq_re] <;> linarith
    have hev1 : ∀ᶠ t in 𝓝 0, 0 ≤ ham (flow t z u) u - ham (flow t z u) 1 :=
      ((hcont 1).continuousAt.eventually_const_lt h1pos).mono fun _ h ↦ h.le
    rcases mem_VT.1 hv with rfl | rfl | rfl
    · exact hev1
    · rcases hu with ⟨rfl, -⟩ | ⟨rfl, hy⟩
      · exact Filter.Eventually.of_forall fun t ↦ by simp
      · -- `ζ² → ζ`: `√3 t² (-Im z₁/2 - t/12) ≥ 0` for `t < -6 Im z₁`
        filter_upwards [Iio_mem_nhds (show (0 : ℝ) < -6 * (z 0).im by linarith)] with t ht
        rw [ham_flow_sub_ham_flow]
        simp only [RR_eq_re_mul_add_im_mul, Complex.sub_re, Complex.sub_im, ζ_re, ζ_im, ζ_sq_re,
          ζ_sq_im, h1, h2, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
          Complex.I_re, Complex.I_im]
        have ht' : 0 ≤ -(z 0).im / 2 - t / 12 := by simp only [Set.mem_Iio] at ht; linarith
        nlinarith [mul_nonneg (mul_nonneg h3'.le (sq_nonneg t)) ht']
    · rcases hu with ⟨rfl, hy⟩ | ⟨rfl, -⟩
      · -- `ζ → ζ²`: `√3 t² (Im z₁/2 + t/12) ≥ 0` for `t > -6 Im z₁`
        filter_upwards [Ioi_mem_nhds (show -6 * (z 0).im < 0 by linarith)] with t ht
        rw [ham_flow_sub_ham_flow]
        simp only [RR_eq_re_mul_add_im_mul, Complex.sub_re, Complex.sub_im, ζ_re, ζ_im, ζ_sq_re,
          ζ_sq_im, h1, h2, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
          Complex.I_re, Complex.I_im]
        have ht' : 0 ≤ (z 0).im / 2 + t / 12 := by simp only [Set.mem_Ioi] at ht; linarith
        nlinarith [mul_nonneg (mul_nonneg h3'.le (sq_nonneg t)) ht']
      · exact Filter.Eventually.of_forall fun t ↦ by simp
  have := (Set.Finite.eventually_all finite_VT).2 key
  filter_upwards [this] with t ht v hv
  linarith [ht v hv]

/-- Every image `F(z)`, `z ≠ 0`, is a switching point: its most recent control is the first control
of `z` (the control used on `[0, t_sw]`), and its first control differs from it
(`firstControl_poincare_ne`). -/
theorem isSwitchingPoint_poincare {z : Fin 3 → ℂ} (hz : z ≠ 0) :
    IsSwitchingPoint (poincare z) := by
  have hF := poincare_ne_zero hz
  rw [l5d_isSwitchingPoint_iff hF, l5d_firstControl_tau_poincare hz, Complex.conj_conj]
  exact (firstControl_poincare_ne hz).symm

/-- `τ` preserves switching points: by Lemma 13.2.5 the first control of `τ(z)` is the conjugate
of the most recent control of `z`, and the most recent control of `τ(z)` the conjugate of the first
control of `z`. -/
theorem isSwitchingPoint_tau_iff {z : Fin 3 → ℂ} (hz : z ≠ 0) :
    IsSwitchingPoint (tau z) ↔ IsSwitchingPoint z := by
  rw [l5d_isSwitchingPoint_iff (tau_ne_zero hz), l5d_isSwitchingPoint_iff hz, tau_tau]
  constructor
  · intro h e
    exact h (by rw [← e, Complex.conj_conj])
  · intro h e
    exact h (by rw [← e, Complex.conj_conj])

/-- The virial group preserves switching points (Lemmas 13.2.1, 13.2.2). -/
theorem isSwitchingPoint_smul_scale_iff {v : ℂ} (hv : v ∈ VT) {r : ℝ} (hr : 0 < r)
    {z : Fin 3 → ℂ} (hz : z ≠ 0) : IsSwitchingPoint (v • scale r z) ↔ IsSwitchingPoint z := by
  have hv0 := ne_zero_of_mem_VT hv
  have hτ : tau (v • scale r z) = starRingEnd ℂ v • scale r (tau z) := by
    rw [tau_smul, tau_scale]
  rw [l5d_isSwitchingPoint_iff (l5d_smul_scale_ne_zero hv hr hz), l5d_isSwitchingPoint_iff hz,
    hτ, l5d_firstControl_smul_scale (conj_mem_VT hv) hr (tau_ne_zero hz),
    l5d_firstControl_smul_scale hv hr hz, map_mul, Complex.conj_conj]
  exact not_congr (mul_right_inj' hv0)

/-- **`F⁻¹ = τ F τ` for the Poincaré map, exactly at switching points** (TeX 12324–12328; gap
G15.6). For `z ≠ 0`, `F(τ F(z)) = τ(z)` if and only if `z` is a switching point: "if" is
`poincare_tau_poincare`; "only if" because `F(τ F z)` is a switching point
(`isSwitchingPoint_poincare`) and `τ(z)` is one only if `z` is (`isSwitchingPoint_tau_iff`). -/
theorem poincare_tau_poincare_eq_tau_iff {z : Fin 3 → ℂ} (hz : z ≠ 0) :
    poincare (tau (poincare z)) = tau z ↔ IsSwitchingPoint z := by
  constructor
  · intro h
    have := isSwitchingPoint_poincare (tau_ne_zero (poincare_ne_zero hz))
    rw [h] at this
    exact (isSwitchingPoint_tau_iff hz).1 this
  · exact poincare_tau_poincare hz

/-- **`F⁻¹ = τ F τ` branch-wise** (TeX 12324–12328; gap G15.6): for any switching time `T` and
control `u` (in particular for the book's root-based maps on closed cells, which switch at a root
`T` of a switching function, double roots included), `τ(z(T, τ(z(T, z⁰, u)), ū)) = z⁰` (Lemma
13.2.5, `tau_flow_neg`, and the flow property `flow_add`). -/
theorem tau_flow_tau_flow (T : ℝ) (z : Fin 3 → ℂ) (u : ℂ) :
    tau (flow T (tau (flow T z u)) (starRingEnd ℂ u)) = z := by
  rw [← tau_flow_neg, ← flow_add, add_neg_cancel, flow_zero, tau_tau]

/-- **The top faces consist of non-switching points** (gap G15.6): at a point of `𝒞₂(ζ, 0, 2)`
(resp. `𝒞₂(ζ², 0, 2)`) the switching function `χ_B` has a double root at `t = 0` with
`χ_{B,2}(0) = ±y₁/2 > 0` and `χ_A(0) > 0`, so the first control `ζ` (resp. `ζ²`) is optimal on both
sides of `t = 0` and is also the most recent control. By `poincare_tau_poincare_eq_tau_iff`, the
identity `F⁻¹ = τ F τ` that the book uses on the closed big cells fails on both top faces. -/
theorem not_isSwitchingPoint_of_mem_topFace :
    (∀ p ∈ topFaceOne, ¬ IsSwitchingPoint (cellPoint p)) ∧
      ∀ p ∈ topFaceTwo, ¬ IsSwitchingPoint (cellPoint p) := by
  have key : ∀ p : Fin 3 → ℝ, p 0 ∈ Ioo 0 1 → p 1 ∈ Ioo 0 π → (p 2 = π ∨ p 2 = 0) →
      ¬ IsSwitchingPoint (cellPoint p) := by
    intro p h0 h1 h2
    obtain ⟨e0, e1, e2, e3⟩ := l5d_cellPoint_apply p
    have hs : 0 < Real.sin (p 1) := Real.sin_pos_of_pos_of_lt_pi h1.1 h1.2
    have hr : 0 < (1 - p 0) * p 0 := mul_pos (by linarith [h0.2]) h0.1
    have hx3 : (cellPoint p 2).re < 0 := by rw [e3]; nlinarith
    have hz : cellPoint p ≠ 0 := fun h ↦ by simp [h] at hx3
    have hy2 : (cellPoint p 1).im = 0 := by
      rcases h2 with h2 | h2 <;> simp [e1, h2]
    rcases h2 with h2 | h2
    · refine l5d_not_isSwitchingPoint_of_eventually hz ζ_mem_VT
        (l5d_eventually_topFace hy2 e2 hx3 (Or.inl ⟨rfl, ?_⟩))
      rw [e0, h2, Real.sin_pi_sub]
      exact mul_pos (by linarith [h0.2]) hs
    · refine l5d_not_isSwitchingPoint_of_eventually hz ζ_sq_mem_VT
        (l5d_eventually_topFace hy2 e2 hx3 (Or.inr ⟨rfl, ?_⟩))
      rw [e0, h2, zero_sub, Real.sin_neg]
      nlinarith [h0.2]
  exact ⟨fun p hp ↦ key p hp.1 hp.2.1 (Or.inl hp.2.2),
    fun p hp ↦ key p hp.1 hp.2.1 (Or.inr hp.2.2)⟩

/-- **The switching point before a non-switching point**: a non-switching point `z ≠ 0` lies in the
interior of a constant-control arc that starts at a switching point `w` (its most recent switching
time is finite, Lemma 13.2.5): `z = z(s, w, u)` with `0 < s < t_sw(w)`, `u` the first control of
`w`, and `F(w) = F(z)`. -/
theorem exists_isSwitchingPoint_of_not {z : Fin 3 → ℂ} (hz : z ≠ 0)
    (h : ¬ IsSwitchingPoint z) :
    ∃ w : Fin 3 → ℂ, w ≠ 0 ∧ w 2 ∈ walls ∧ IsSwitchingPoint w ∧
      ∃ s ∈ Ioo 0 (firstSwitchTime w), z = flow s w (firstControl w) ∧
        poincare w = poincare z := by
  set u := firstControl z with hu
  have hτ : tau z ≠ 0 := tau_ne_zero hz
  -- `u` is also the most recent control, so `ū` is the first control of `τ z` (Lemma 13.2.5)
  have hfτ : firstControl (tau z) = starRingEnd ℂ u :=
    (firstControl_eq_iff hτ).2 (isMostRecentControl_iff_isFirstControl_tau.1 (not_not.1 h))
  -- `S = t_sw(τ z) = -t_rec(z)`, the most recent switching time of `z` (Lemma 13.2.5,
  -- `lemma13_2_5`)
  set S := firstSwitchTime (tau z)
  have hS : 0 < S := firstSwitchTime_pos hτ
  -- `u` is optimal along `t ↦ z(t, z, u)` on `[-S, 0]` (the time reversal of `[0, t_sw(τ z)]`)
  have hback : ∀ t ∈ Icc (-S) 0, ∀ v ∈ VT, ham (flow t z u) v ≤ ham (flow t z u) u := by
    intro t ht v hv
    have := firstControl_maximizes hτ (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩ _
      (conj_mem_VT hv)
    rwa [hfτ, l5d_ham_flow_tau, l5d_ham_flow_tau, neg_neg, Complex.conj_conj,
      Complex.conj_conj] at this
  -- the switching point `w = z(-S, z, u) = τ F(τ z)`
  set w := flow (-S) z u with hw
  have hwF : w = tau (poincare (tau z)) := by
    rw [poincare, hfτ, ← tau_flow_neg, tau_tau]
  have hw0 : w ≠ 0 := hwF ▸ tau_ne_zero (poincare_ne_zero hτ)
  have hflow : ∀ t, flow t w u = flow (t - S) z u := by
    intro t
    rw [hw, ← flow_add]
    congr 1
    ring
  have hfw : firstControl w = u := by
    refine (firstControl_eq_iff hw0).2 ⟨firstControl_mem_VT z, S, hS, fun t ht v hv ↦ ?_⟩
    rw [hflow]
    exact hback _ ⟨by linarith [ht.1], by linarith [ht.2]⟩ v hv
  have hT := firstSwitchTime_pos hz
  have hmax := firstControl_maximizes hz
  -- the first switching time of `w` is `S + t_sw(z)`
  have hTw : firstSwitchTime w = S + firstSwitchTime z := by
    rw [firstSwitchTime, hfw]
    apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
    · obtain ⟨t, ht, v, hv, hlt⟩ := firstControl_beaten hz one_pos
      refine ⟨S + t, by linarith [ht.1], v, hv, ?_⟩
      rwa [hflow, add_sub_cancel_left]
    · rintro a ⟨ha, v, hv, hlt⟩
      by_contra hlt'
      push Not at hlt'
      rw [hflow] at hlt
      rcases le_or_gt (a - S) 0 with h0 | h0
      · exact absurd (hback _ ⟨by linarith, h0⟩ v hv) (not_le.2 hlt)
      · exact absurd (hmax _ ⟨h0.le, by linarith⟩ v hv) (not_le.2 hlt)
    · intro b hb
      obtain ⟨t, ht, v, hv, hlt⟩ := firstControl_beaten hz (show 0 < b - S - firstSwitchTime z by
        linarith)
      refine ⟨S + t, ⟨by linarith [ht.1], v, hv, ?_⟩, by linarith [ht.2]⟩
      rwa [hflow, add_sub_cancel_left]
  refine ⟨w, hw0, ?_, ?_, S, ⟨hS, by rw [hTw]; linarith⟩, ?_, ?_⟩
  · rw [hwF]
    exact conj_mem_walls (poincare_mem_walls hτ)
  · rw [hwF]
    exact (isSwitchingPoint_tau_iff (poincare_ne_zero hτ)).2 (isSwitchingPoint_poincare hτ)
  · rw [hfw, hflow, sub_self, flow_zero]
  · change flow (firstSwitchTime w) w (firstControl w) = flow (firstSwitchTime z) z u
    rw [hfw, hTw, hflow, add_sub_cancel_left]

/-! ### The involution on `Ξ_{𝒲,0}/V_T` -/

/-- A point of `Ξ_{𝒲,0}/V_T` is a switching point if a representative is (equivalently every one,
`isSwitchingPoint_smul_scale_iff`). -/
def IsSwitchingPointQ (x : XiW0Quot) : Prop :=
  ∃ z ∈ sectionZero, classOf z = x ∧ IsSwitchingPoint z

/-- Every representative of a switching point is a switching point. -/
theorem isSwitchingPointQ_iff (x : XiW0Quot) :
    IsSwitchingPointQ x ↔ ∀ z ∈ sectionZero, classOf z = x → IsSwitchingPoint z := by
  constructor
  · rintro ⟨z₀, hz₀, rfl, hsw⟩ z hz hzx
    obtain ⟨v, hv, r, hr, rfl⟩ := (classOf_eq_classOf_iff hz₀ hz).1 hzx.symm
    exact (isSwitchingPoint_smul_scale_iff hv hr hz₀.1).2 hsw
  · intro h
    obtain ⟨z, hz, hzx⟩ := exists_classOf_eq x
    exact ⟨z, hz, hzx, h z hz hzx⟩

/-- Every image `F(x)` is a switching point (`isSwitchingPoint_poincare`). -/
theorem isSwitchingPointQ_poincareAngZero (x : XiW0Quot) :
    IsSwitchingPointQ (poincareAngZero x) := by
  obtain ⟨z, hz, rfl⟩ := exists_classOf_eq x
  exact ⟨poincare z, poincare_mem_sectionZero hz, (poincareAngZero_classOf hz).symm,
    isSwitchingPoint_poincare hz.1⟩

/-- `τ` preserves switching points (`isSwitchingPoint_tau_iff`). -/
theorem isSwitchingPointQ_tauZero_iff (x : XiW0Quot) :
    IsSwitchingPointQ (tauZero x) ↔ IsSwitchingPointQ x := by
  obtain ⟨z, hz, rfl⟩ := exists_classOf_eq x
  have hτ := tau_mem_sectionZero hz
  rw [tauZero_classOf hz]
  constructor
  · intro h
    exact ⟨z, hz, rfl, (isSwitchingPoint_tau_iff hz.1).1 ((isSwitchingPointQ_iff _).1 h _ hτ rfl)⟩
  · intro h
    exact ⟨tau z, hτ, rfl,
      (isSwitchingPoint_tau_iff hz.1).2 ((isSwitchingPointQ_iff _).1 h _ hz rfl)⟩

/-- **`F(τ F(x)) = τ(x)` at switching points of `Ξ_{𝒲,0}/V_T`** (`poincare_tau_poincare`,
`poincareAngZero_classOf`, `tauZero_classOf`). -/
theorem poincareAngZero_tauZero_poincareAngZero {x : XiW0Quot} (hx : IsSwitchingPointQ x) :
    poincareAngZero (tauZero (poincareAngZero x)) = tauZero x := by
  obtain ⟨z, hz, rfl, hsw⟩ := hx
  have hF := poincare_mem_sectionZero hz
  rw [poincareAngZero_classOf hz, tauZero_classOf hF,
    poincareAngZero_classOf (tau_mem_sectionZero hF), tauZero_classOf hz,
    poincare_tau_poincare hz.1 hsw]

/-- The involution `𝔦 := τ ∘ F` (TeX 12324–12328). -/
noncomputable def involution (x : XiW0Quot) : XiW0Quot := tauZero (poincareAngZero x)

/-- "`𝔦 := τ ∘ F` is an involution: `𝔦 = 𝔦⁻¹`" (TeX 12326–12328), on switching points (gap G15.6):
`𝔦(𝔦(x)) = τ F τ F x = τ τ x = x`, and `𝔦(x)` is again a switching point. -/
theorem involution_involution {x : XiW0Quot} (hx : IsSwitchingPointQ x) :
    IsSwitchingPointQ (involution x) ∧ involution (involution x) = x := by
  refine ⟨(isSwitchingPointQ_tauZero_iff _).2 (isSwitchingPointQ_poincareAngZero x), ?_⟩
  unfold involution
  rw [poincareAngZero_tauZero_poincareAngZero hx]
  exact continuous_involutive_tauZero.2 x

/-- Two sets are **in involution** if `𝔦(𝒟) = 𝒟̃` and `𝔦(𝒟̃) = 𝒟` (TeX 12330–12332). -/
def InInvolution (D D' : Set XiW0Quot) : Prop := involution '' D = D' ∧ involution '' D' = D

/-- "The two fixed points `q_in, q_out ∈ 𝒟₁` are in involution" (TeX 12363–12364):
`𝔦(q_out) = τ F(q_out) = τ(q_out) = q_in` and `𝔦(q_in) = q_out` (Lemma 13.5.2, `tauQuot_qOut`). -/
theorem inInvolution_qOut0_qIn0 : InInvolution {qOut0} {qIn0} := by
  have hF : poincareAngZero qOut0 = qOut0 := by
    have h := lemma13_5_2.1
    have hmem : qOut ∈ {x : XiWQuot | poincareAngQuot x = x ∧ hamMaxQuot x = 0} := by
      rw [h]; exact Set.mem_insert _ _
    exact Subtype.ext hmem.1
  have hτ : tauZero qOut0 = qIn0 := Subtype.ext tauQuot_qOut
  have h1 : involution qOut0 = qIn0 := by rw [involution, hF, hτ]
  have h2 : involution qIn0 = qOut0 := by
    have hFin : poincareAngZero qIn0 = qIn0 := by
      have h := lemma13_5_2.1
      have hmem : qIn ∈ {x : XiWQuot | poincareAngQuot x = x ∧ hamMaxQuot x = 0} := by
        rw [h]; exact Set.mem_insert_of_mem _ rfl
      exact Subtype.ext hmem.1
    rw [involution, hFin, ← hτ]
    exact continuous_involutive_tauZero.2 qOut0
  exact ⟨by rw [Set.image_singleton, h1], by rw [Set.image_singleton, h2]⟩

/-! ### The loci `∂_res`, `∂_A`, `∂_{A,ζ²}`, `∂_B` -/

/-- The resultant locus `∂_res := 𝔦(𝒞₂(ζ))` (TeX 12333–12336), `𝒞₂(ζ) = 𝒞₂(ζ, 1, 1)` viewed as the
front and back faces of the first big cell. -/
noncomputable def bdRes : Set XiW0Quot := involution '' (cellClass '' frontBackOne)

/-- The discriminant locus `∂_A := 𝔦(𝒞₂(ζ, 0, 2))` (TeX 12339–12343), `𝒞₂(ζ, 0, 2)` viewed as the
top face `θ₂ = π` of the first big cell (where `poincare` is the book's map,
`continuousWithinAt_topFaceOne`). The book adds "By construction `∂_A` and `𝒞₂(ζ)` are in
involution" (TeX 12344), a slip for `𝒞₂(ζ, 0, 2)`; even so it fails for the involution `𝔦 = τ F` of
the Fuller–Poincaré map: `𝔦(𝔦(x)) = x` needs `x` to be a switching point (`involution_involution`),
and the points of the top face are not (`not_isSwitchingPoint_of_mem_topFace`; gap G15.6). Only the
definition `∂_A = 𝔦(𝒞₂(ζ, 0, 2))` is used. -/
noncomputable def bdA : Set XiW0Quot := involution '' (cellClass '' topFaceOne)

/-- `∂_{A,ζ²} := 𝔦(𝒞₂^A)` (TeX 12424–12426), with the book's root-based map `F_A` on `𝒞₂^A`. -/
noncomputable def bdAζ2 : Set XiW0Quot :=
  (fun p ↦ classOf (tau (cellMapA (cellPoint p)))) '' topFaceTwoA

/-- `∂_B := 𝔦(𝒞₂^B)` (TeX 12441–12442), with `F_B` (which is `poincare` on `𝒞₂^B`,
`firstSwitchTime_topFaceTwo`). -/
noncomputable def bdB : Set XiW0Quot :=
  (fun p ↦ classOf (tau (cellMapB (cellPoint p)))) '' topFaceTwoB

/-! ### Helpers for the `∂`-loci -/

/-- A real polynomial of positive degree with a double root has vanishing discriminant
(`Polynomial.discr_eq_zero_of_isRoot_of_isRoot_derivative`). -/
private lemma l5d_discr_eq_zero_of_sq_dvd {P : ℝ[X]} (hP : 0 < P.natDegree) {b : ℝ}
    (h : (X - C b) ^ 2 ∣ P) : P.discr = 0 := by
  obtain ⟨S, hS⟩ := h
  have hP0 : P ≠ 0 := by rintro rfl; simp at hP
  have h1 : X - C b ∣ P := hS ▸ Dvd.dvd.mul_right (dvd_pow_self _ two_ne_zero) S
  have h2 : X - C b ∣ derivative P := by
    rw [hS, derivative_mul, derivative_pow]
    refine dvd_add (Dvd.dvd.mul_right ?_ _) (Dvd.dvd.mul_right (dvd_pow_self _ two_ne_zero) _)
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (by simp) _) _
  exact discr_eq_zero_of_isRoot_of_isRoot_derivative hP0 (dvd_iff_isRoot.1 h1)
    (dvd_iff_isRoot.1 h2)

/-- `X^m (P /ₘ X^m) = P` for the multiplicity `m` of the root `0`. -/
private lemma l5d_X_pow_mul_divByMonic (P : ℝ[X]) :
    X ^ P.rootMultiplicity 0 * (P /ₘ X ^ P.rootMultiplicity 0) = P := by
  simpa using pow_mul_divByMonic_rootMultiplicity_eq P 0

/-- Dividing out the root `0` keeps the other roots with their multiplicities. -/
private lemma l5d_dvd_divByMonic_X_pow {P : ℝ[X]} {b : ℝ} (hb : b ≠ 0) {k : ℕ}
    (h : (X - C b) ^ k ∣ P) : (X - C b) ^ k ∣ P /ₘ X ^ P.rootMultiplicity 0 := by
  rw [← l5d_X_pow_mul_divByMonic P] at h
  have hcop : IsCoprime (X - C b) (X - C 0) := isCoprime_X_sub_C_of_isUnit_sub (by simpa using hb)
  rw [map_zero, sub_zero] at hcop
  exact hcop.pow_left.pow_right.dvd_of_dvd_mul_left h

private lemma l5d_divByMonic_ne_zero {P : ℝ[X]} (hP : P ≠ 0) :
    P /ₘ X ^ P.rootMultiplicity 0 ≠ 0 := by
  intro h
  apply hP
  rw [← l5d_X_pow_mul_divByMonic P, h, mul_zero]

/-- A double root `b ≠ 0` of `P` makes the discriminant of `P/t^m` vanish. -/
private lemma l5d_discr_divByMonic_eq_zero {P : ℝ[X]} (hP : P ≠ 0) {b : ℝ} (hb : b ≠ 0)
    (h : (X - C b) ^ 2 ∣ P) : (P /ₘ X ^ P.rootMultiplicity 0).discr = 0 := by
  have hd := l5d_dvd_divByMonic_X_pow hb h
  refine l5d_discr_eq_zero_of_sq_dvd ?_ hd
  have := natDegree_le_of_dvd hd (l5d_divByMonic_ne_zero hP)
  rw [natDegree_pow, natDegree_X_sub_C] at this
  lia

/-- A common root `b ≠ 0` of `P` and `Q` makes the resultant of `P/t^m` and `Q/t^n` vanish. -/
private lemma l5d_resultant_divByMonic_eq_zero {P Q : ℝ[X]} (hP : P ≠ 0) {b : ℝ} (hb : b ≠ 0)
    (hPb : P.IsRoot b) (hQb : Q.IsRoot b) :
    (P /ₘ X ^ P.rootMultiplicity 0).resultant (Q /ₘ X ^ Q.rootMultiplicity 0) = 0 := by
  have h1 := l5d_dvd_divByMonic_X_pow (P := P) (k := 1) hb
    (by rw [pow_one]; exact dvd_iff_isRoot.2 hPb)
  have h2 := l5d_dvd_divByMonic_X_pow (P := Q) (k := 1) hb
    (by rw [pow_one]; exact dvd_iff_isRoot.2 hQb)
  rw [pow_one] at h1 h2
  rw [resultant_eq_zero_iff]
  exact ⟨Or.inl (l5d_divByMonic_ne_zero hP),
    fun hc ↦ not_isUnit_X_sub_C b (hc.isUnit_of_dvd' h1 h2)⟩

/-- The switching functions under the rescaling of Lemma 13.2.1 (the substitution behind it, for a
constant control): `χ^c_d(t, (r z₁, r² z₂, r³ z₃)) = r³ χ^c_d(t/r, z)`. -/
private lemma l5d_switchingFunction_scale {r : ℝ} (hr : r ≠ 0) (c d : ℂ) (t : ℝ)
    (y : Fin 3 → ℂ) :
    switchingFunction c d t (scale r y) = r ^ 3 * switchingFunction c d (t / r) y := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hflow : flow t (scale r y) c 2 = ((r ^ 3 : ℝ) : ℂ) * flow (t / r) y c 2 := by
    simp only [flow, scale, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
      Matrix.cons_val_one, Matrix.cons_val_zero]
    push_cast
    field_simp
  rw [switchingFunction, switchingFunction, hflow, RR_ofReal_mul_right, mul_div_assoc]

/-- The switching functions under the virial group: the rotation (13.2.7) (`eqn13_2_7`) and the
rescaling of Lemma 13.2.1, `χ^{vc}_{vd}(t, v·(r z₁, r² z₂, r³ z₃)) = r³ χ^c_d(t/r, z)`. -/
private lemma l5d_switchingFunction_smul_scale {v : ℂ} (hv : v ∈ VT) {r : ℝ} (hr : r ≠ 0)
    (c d : ℂ) (t : ℝ) (y : Fin 3 → ℂ) :
    switchingFunction (v * c) (v * d) t (v • scale r y) =
      r ^ 3 * switchingFunction c d (t / r) y := by
  rw [← l5d_switchingFunction_scale hr]
  rcases mem_VT.1 hv with rfl | rfl | rfl
  · rw [one_mul, one_mul, one_smul]
  · exact eqn13_2_7 c d t (scale r y)
  · rw [pow_two, mul_assoc, mul_assoc, mul_smul, eqn13_2_7, eqn13_2_7]

/-- **Time reversal of the switching cubics in cell form** (Lemma 13.2.4 with Lemmas 13.2.1,
13.2.2): along `v·(r w₁, r² w₂, r³ w₃)` for `w = τ(z(T, z⁰, c))`, the cubic
`χ^{v c̄}_{v(ā - b̄)}` is `r³ χ^c_{a-b}(T - t/r, z⁰)`. -/
private lemma l5d_cubic_transfer {v : ℂ} (hv : v ∈ VT) {r : ℝ} (hr : r ≠ 0) (T : ℝ)
    (w : Fin 3 → ℂ) (c a b : ℂ) :
    (switchingCubic (v * starRingEnd ℂ c) (v * (starRingEnd ℂ a - starRingEnd ℂ b))
        (v • scale r (tau (flow T w c)))).toPoly =
      C (r ^ 3) * (switchingCubic c (a - b) w).toPoly.comp (C T - C r⁻¹ * X) := by
  apply Polynomial.funext
  intro t
  rw [eval_switchingCubic, eval_mul, eval_C, eval_comp, eval_switchingCubic,
    l5d_switchingFunction_smul_scale hv hr, ← lemma13_2_4]
  congr 2
  simp only [eval_sub, eval_C, eval_mul, eval_X]
  rw [div_eq_inv_mul]

/-- A root of order `2` at `t = 0` becomes a root of order `2` at `t = rT`. -/
private lemma l5d_sq_dvd_comp {Q : ℝ[X]} (hQ : X ^ 2 ∣ Q) {r : ℝ} (hr : r ≠ 0) (T : ℝ) :
    (X - C (r * T)) ^ 2 ∣ C (r ^ 3) * Q.comp (C T - C r⁻¹ * X) := by
  obtain ⟨R, rfl⟩ := hQ
  have hL : C T - C r⁻¹ * X = C (-r⁻¹) * (X - C (r * T)) := by
    apply Polynomial.funext
    intro t
    simp only [eval_sub, eval_C, eval_mul, eval_X]
    field_simp
    ring
  rw [mul_comp, pow_comp, X_comp, hL, mul_pow]
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (dvd_mul_left _ _) _) _

/-- `X² ∣ χ` when `t = 0` is a root of multiplicity `2`. -/
private lemma l5d_X_sq_dvd {P : ℝ[X]} (h : P.rootMultiplicity 0 = 2) : X ^ 2 ∣ P := by
  simpa [h] using pow_rootMultiplicity_dvd P 0

private lemma l5d_toPoly_ne_zero (z : Fin 3 → ℂ) :
    (chiA ζ z).toPoly ≠ 0 ∧ (chiB ζ z).toPoly ≠ 0 ∧ (chiA (ζ ^ 2) z).toPoly ≠ 0 := by
  obtain ⟨h1, h2, h3, -⟩ := chiA_chiB_eq z
  refine ⟨Cubic.ne_zero_of_a_ne_zero ?_, Cubic.ne_zero_of_a_ne_zero ?_,
    Cubic.ne_zero_of_a_ne_zero ?_⟩ <;> simp [h1, h2, h3]

private lemma l5d_openBoxOne_sub {p : Fin 3 → ℝ} (hp : p ∈ openBoxOne) : p ∈ cellDomain :=
  ⟨Ioo_subset_Icc_self hp.1, Ioo_subset_Icc_self hp.2.1,
    ⟨by linarith [hp.2.2.1, Real.pi_pos], hp.2.2.2.le⟩⟩

private lemma l5d_openBoxTwo_sub {p : Fin 3 → ℝ} (hp : p ∈ openBoxTwo) : p ∈ cellDomain :=
  ⟨Ioo_subset_Icc_self hp.1, Ioo_subset_Icc_self hp.2.1,
    ⟨hp.2.2.1.le, by linarith [hp.2.2.2, Real.pi_pos]⟩⟩

private lemma l5d_topFaceOne_sub {p : Fin 3 → ℝ} (hp : p ∈ topFaceOne) : p ∈ cellDomain :=
  ⟨Ioo_subset_Icc_self hp.1, Ioo_subset_Icc_self hp.2.1,
    ⟨by rw [hp.2.2]; linarith [Real.pi_pos], hp.2.2.le⟩⟩

private lemma l5d_topFaceTwo_sub {p : Fin 3 → ℝ} (hp : p ∈ topFaceTwo) : p ∈ cellDomain :=
  ⟨Ioo_subset_Icc_self hp.1, Ioo_subset_Icc_self hp.2.1,
    ⟨by rw [hp.2.2]; linarith [Real.pi_pos], by rw [hp.2.2]; linarith [Real.pi_pos]⟩⟩

private lemma l5d_frontBackOne_sub {p : Fin 3 → ℝ} (hp : p ∈ frontBackOne) : p ∈ cellDomain := by
  refine ⟨hp.1, ?_, ⟨by linarith [hp.2.2.1, Real.pi_pos], hp.2.2.2⟩⟩
  rcases hp.2.1 with h | h <;> rw [h] <;> constructor <;> linarith [Real.pi_pos]

/-- `𝔦(x) = class of τ F(z)` on cell points. -/
private lemma l5d_involution_cellClass {p : Fin 3 → ℝ} (hp : p ∈ cellDomain) :
    involution (cellClass p) = classOf (tau (poincare (cellPoint p))) := by
  have hw := cellPoint_mem_sectionZero hp
  rw [involution, cellClass, poincareAngZero_classOf hw,
    tauZero_classOf (poincare_mem_sectionZero hw)]

/-- **The resultant and the discriminants vanish along the `∂`-loci** (Lemma 13.2.4, TeX
12336–12345, 12425–12427 (gap G15.4: "`Δ_{A,0}` vanishes along `∂_A`" there means `∂_{A,ζ²}`),
12441–12443), at their points in the open big cells:
* along `∂_res`, `res_AB = 0`: the trajectory reaches `z₃ = 0` at the switching time `T`, a common
  root of `χ_{A,0}` and `χ_{B,1}`;
* along `∂_A`, `Δ_{A,0} = 0`: `χ_B` has a double root at `0` on the top face `𝒞₂(ζ, 0, 2)`, which
  becomes a double root of `χ_{A,0}` at `T` (`χ^ζ_{ζ-ζ²}` reversed and rotated by `ζ²` is
  `χ^ζ_{ζ-1}`);
* along `∂_{A,ζ²}`, `Δ_{A,0} = 0` for the control `ζ²` (`χ_B` on `𝒞₂(ζ², 0, 2)` becomes `χ_A`);
* along `∂_B`, `Δ_{B,1} = 0` (`χ_B` on `𝒞₂(ζ², 0, 2)` becomes `χ_B` of the control `ζ`).

Proof route: a point `q` of the open cell with `cellClass q = 𝔦(cellClass p)` is
`cellPoint q = v · (r y₁, r² y₂, r³ y₃)` with `y = τ F(cellPoint p)`, `v ∈ V_T`, `r > 0`; the
rotation `v` is read off the first controls (`ζ` on the first open cell, `ū₀` at `y`). On `∂_A`,
`∂_{A,ζ²}` and `∂_B` the book's argument: Lemma 13.2.4 (`lemma13_2_4`) with (13.2.7)
(`eqn13_2_7`) and the rescaling (Lemma 13.2.1) carry the double root of `χ_B` at `0` to a double
root at `r T` (`l5d_cubic_transfer`), and a double root makes the discriminant vanish
(`Polynomial.discr_eq_zero_of_isRoot_of_isRoot_derivative`). On `∂_res` the proof uses the
trajectory reversal of Lemma 13.2.5 instead (`tau_flow_tau_flow`: `z(T, τ F(w), ū₀) = τ w`, whose
third coordinate is `0`), which makes every switching function of `cellPoint q` vanish at `r T` at
once, so `χ_{A,0}` and `χ_{B,1}` have the common root `r T`. On `∂_{A,ζ²}` the book's map `F_A` is
not `poincare` where `Δ_{A,0} = 0` (a tangency), so `v = ζ` is read off the third coordinates
instead: `z₃(T)` is orthogonal to `ζ² - 1` (`χ_A(T) = 0`) and `cellPoint q` has `z₃ < 0`; and
`τ F_A(cellPoint p)` lies in the section because `F_A` does (`continuousOn_cellMapA_cellMapB`). -/
theorem discr_resAB_eq_zero_of_mem_bd :
    (∀ q ∈ openBoxOne, cellClass q ∈ bdRes → resAB ζ (cellPoint q) = 0) ∧
      (∀ q ∈ openBoxOne, cellClass q ∈ bdA → discrA ζ (cellPoint q) = 0) ∧
      (∀ q ∈ openBoxTwo, cellClass q ∈ bdAζ2 → discrA (ζ ^ 2) (cellPoint q) = 0) ∧
      ∀ q ∈ openBoxOne, cellClass q ∈ bdB → discrB ζ (cellPoint q) = 0 := by
  obtain ⟨-, -, -, -, -, hfc1, -⟩ := definition15_1_2
  have hvv : ∀ v ∈ VT, v * starRingEnd ℂ v = 1 := fun v hv ↦ by
    rw [← inv_eq_conj_of_mem_VT hv, mul_inv_cancel₀ (ne_zero_of_mem_VT hv)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `∂_res`: the trajectory reaches `z₃ = 0` at the switching time, a common root
    rintro q hq ⟨x, ⟨p, hp, rfl⟩, hx⟩
    have hpD := l5d_frontBackOne_sub hp
    set w := cellPoint p with hw
    have hw0 : w ∈ sectionZero := cellPoint_mem_sectionZero hpD
    rw [l5d_involution_cellClass hpD] at hx
    have hy := tau_mem_sectionZero (poincare_mem_sectionZero hw0)
    obtain ⟨v, hv, r, hr, hqy⟩ := (classOf_eq_classOf_iff hy
      (cellPoint_mem_sectionZero (l5d_openBoxOne_sub hq))).1 hx
    -- the first controls: `ζ = v ū₀`
    have hu : v * starRingEnd ℂ (firstControl w) = ζ := by
      have h := hfc1 q hq
      rwa [hqy, l5d_firstControl_smul_scale hv hr (tau_ne_zero (poincare_ne_zero hw0.1)),
        l5d_firstControl_tau_poincare hw0.1] at h
    have hT := firstSwitchTime_pos hw0.1
    have hw2 : w 2 = 0 := by
      obtain ⟨-, -, e2, e3⟩ := l5d_cellPoint_apply p
      apply Complex.ext
      · rw [e3]
        rcases hp.2.1 with h | h <;> simp [h]
      · exact e2
    -- `z(T, τ F(w), ū₀) = τ w` (Lemma 13.2.5), whose third coordinate is `0`
    have hback : flow (firstSwitchTime w) (tau (poincare w)) (starRingEnd ℂ (firstControl w)) =
        tau w := by
      have := congrArg tau (tau_flow_tau_flow (firstSwitchTime w) w (firstControl w))
      rw [tau_tau] at this
      exact this
    -- every switching function of `cellPoint q` with the control `ζ` vanishes at `r t_sw(w)`
    have hroot : ∀ d : ℂ,
        switchingFunction ζ d (r * firstSwitchTime w) (cellPoint q) = 0 := by
      intro d
      have hd : d = v * (starRingEnd ℂ v * d) := by rw [← mul_assoc, hvv v hv, one_mul]
      rw [hqy, ← hu, hd, l5d_switchingFunction_smul_scale hv hr.ne',
        mul_div_cancel_left₀ _ hr.ne', switchingFunction, hback]
      simp [tau, hw2, RR]
    have hA : (chiA ζ (cellPoint q)).toPoly.IsRoot (r * firstSwitchTime w) := by
      rw [IsRoot, chiA, eval_switchingCubic, hroot]
    have hB : (chiB ζ (cellPoint q)).toPoly.IsRoot (r * firstSwitchTime w) := by
      rw [IsRoot, chiB, eval_switchingCubic, hroot]
    exact l5d_resultant_divByMonic_eq_zero (l5d_toPoly_ne_zero _).1
      (mul_ne_zero hr.ne' hT.ne') hA hB
  · -- `∂_A`: the double root of `χ_B` at `0` on `𝒞₂(ζ, 0, 2)` becomes one of `χ_{A,0}`
    rintro q hq ⟨x, ⟨p, hp, rfl⟩, hx⟩
    have hpD := l5d_topFaceOne_sub hp
    set w := cellPoint p with hw
    have hw0 : w ∈ sectionZero := cellPoint_mem_sectionZero hpD
    obtain ⟨hfcw, -, hmB, -, -⟩ := topFaceOne_switching hp
    rw [l5d_involution_cellClass hpD] at hx
    have hy := tau_mem_sectionZero (poincare_mem_sectionZero hw0)
    obtain ⟨v, hv, r, hr, hqy⟩ := (classOf_eq_classOf_iff hy
      (cellPoint_mem_sectionZero (l5d_openBoxOne_sub hq))).1 hx
    have hu : v * ζ ^ 2 = ζ := by
      have h := hfc1 q hq
      rwa [hqy, l5d_firstControl_smul_scale hv hr (tau_ne_zero (poincare_ne_zero hw0.1)),
        l5d_firstControl_tau_poincare hw0.1, hfcw, conj_ζ] at h
    have hv2 : v = ζ ^ 2 := by linear_combination (-v) * ζ_pow_three + ζ * hu
    have hT := firstSwitchTime_pos hw0.1
    have htr := l5d_cubic_transfer ζ_sq_mem_VT hr.ne' (firstSwitchTime w) w ζ ζ (ζ ^ 2)
    rw [conj_ζ, conj_ζ_sq, show ζ ^ 2 * ζ ^ 2 = ζ by linear_combination ζ * ζ_pow_three,
      show ζ ^ 2 * (ζ ^ 2 - ζ) = ζ - 1 by linear_combination (ζ - 1) * ζ_pow_three] at htr
    have hQ : X ^ 2 ∣ (switchingCubic ζ (ζ - ζ ^ 2) w).toPoly := by
      have := l5d_X_sq_dvd hmB
      rwa [chiB, conj_ζ] at this
    have hdvd : (X - C (r * firstSwitchTime w)) ^ 2 ∣ (chiA ζ (cellPoint q)).toPoly := by
      have e : chiA ζ (cellPoint q) = switchingCubic ζ (ζ - 1)
          ((ζ ^ 2) • scale r (tau (flow (firstSwitchTime w) w ζ))) := by
        rw [chiA, hqy, hv2, poincare, hfcw]
      rw [e, htr]
      exact l5d_sq_dvd_comp hQ hr.ne' _
    exact l5d_discr_divByMonic_eq_zero (l5d_toPoly_ne_zero _).1 (mul_ne_zero hr.ne' hT.ne') hdvd
  · -- `∂_{A,ζ²}`: the double root of `χ_B` at `0` on `𝒞₂(ζ², 0, 2)` becomes one of `χ_{A,0}`
    rintro q hq ⟨p, hp, hx⟩
    change classOf (tau (cellMapA (cellPoint p))) = cellClass q at hx
    set w := cellPoint p with hw
    obtain ⟨-, -, hmB, -, -, hcard, -⟩ := topFaceTwo_switching hp.1
    set P := (chiA (ζ ^ 2) w).toPoly with hPdef
    have hP0 : P ≠ 0 := (l5d_toPoly_ne_zero w).2.2
    -- the least positive root `T` of `χ_{A,0}` exists (Descartes, `topFaceTwo_switching`)
    have hTmem : leastPosRoot P ∈ {t : ℝ | 0 < t ∧ P.eval t = 0} := by
      apply Set.Nonempty.csInf_mem
      · obtain ⟨t, ht⟩ := Multiset.card_pos_iff_exists_mem.1
          (by rw [hcard hp.2]; norm_num : 0 < (P.roots.filter (fun t ↦ 0 < t)).card)
        rw [Multiset.mem_filter] at ht
        exact ⟨t, ht.2, (mem_roots hP0).1 ht.1⟩
      · exact (P.roots.toFinset.finite_toSet).subset fun t ht ↦ by
          simpa [Multiset.mem_toFinset, mem_roots hP0] using ht.2
    set T := leastPosRoot P with hTdef
    have hcm : cellMapA w = flow T w (ζ ^ 2) := rfl
    -- `τ F_A(w)` is a point of the section (`F_A` lands in the section)
    have hy : tau (cellMapA w) ∈ sectionZero :=
      tau_mem_sectionZero (continuousOn_cellMapA_cellMapB.1 p hp)
    obtain ⟨v, hv, r, hr, hqy⟩ := (classOf_eq_classOf_iff hy
      (cellPoint_mem_sectionZero (l5d_openBoxTwo_sub hq))).1 hx
    -- `v = ζ`: `z₃(T)` is orthogonal to `ζ² - 1` (`χ_A(T) = 0`) and `cellPoint q` has `z₃ < 0`
    set Z := flow T w (ζ ^ 2) 2 with hZdef
    have hZ : RR (ζ ^ 2 - 1) Z = 0 := by
      have h := hTmem.2
      rw [hPdef, chiA, eval_switchingCubic, switchingFunction] at h
      exact (div_eq_zero_iff.1 h).resolve_right (by positivity)
    obtain ⟨-, -, -, e3⟩ := l5d_cellPoint_apply q
    set x := -2 * (1 - q 0) * q 0 * Real.sin (q 1) with hxdef
    have hx0 : x < 0 := by
      have hs : 0 < Real.sin (q 1) := Real.sin_pos_of_pos_of_lt_pi hq.2.1.1 hq.2.1.2
      have : 0 < (1 - q 0) * q 0 := mul_pos (by linarith [hq.1.2]) hq.1.1
      rw [hxdef]; nlinarith
    have hcp : cellPoint q 2 = (x : ℂ) := by simp [cellPoint, hxdef]
    have hRZ : ((r ^ 3 : ℝ) : ℂ) * Z = v * (x : ℂ) := by
      have h3 : cellPoint q 2 = v * (((r ^ 3 : ℝ) : ℂ) * starRingEnd ℂ Z) := by
        rw [hqy, hcm]
        simp [scale, tau, hZdef]
      have := congrArg (starRingEnd ℂ) h3
      rw [hcp, Complex.conj_ofReal, map_mul, map_mul, Complex.conj_ofReal,
        Complex.conj_conj] at this
      calc ((r ^ 3 : ℝ) : ℂ) * Z = (v * starRingEnd ℂ v) * (((r ^ 3 : ℝ) : ℂ) * Z) := by
            rw [hvv v hv, one_mul]
        _ = v * (x : ℂ) := by rw [this]; ring
    have hRv : RR (ζ ^ 2 - 1) v = 0 := by
      have h1 : RR (ζ ^ 2 - 1) (((r ^ 3 : ℝ) : ℂ) * Z) = 0 := by
        rw [RR_ofReal_mul_right, hZ, mul_zero]
      rw [hRZ, mul_comm, RR_ofReal_mul_right] at h1
      exact (mul_eq_zero.1 h1).resolve_left hx0.ne
    have hv1 : v = ζ := by
      have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
      rcases mem_VT.1 hv with rfl | rfl | rfl
      · norm_num [RR_eq_re_mul_add_im_mul, ζ_sq_re, ζ_sq_im] at hRv
      · rfl
      · simp only [RR_eq_re_mul_add_im_mul, Complex.sub_re, Complex.sub_im, ζ_sq_re, ζ_sq_im,
          Complex.one_re, Complex.one_im] at hRv
        nlinarith
    have hT := hTmem.1
    have htr := l5d_cubic_transfer ζ_mem_VT hr.ne' T w (ζ ^ 2) (ζ ^ 2) ζ
    rw [conj_ζ_sq, conj_ζ, show ζ * ζ = ζ ^ 2 by ring,
      show ζ * (ζ - ζ ^ 2) = ζ ^ 2 - 1 by linear_combination (-1 : ℂ) * ζ_pow_three] at htr
    have hQ : X ^ 2 ∣ (switchingCubic (ζ ^ 2) (ζ ^ 2 - ζ) w).toPoly := by
      have := l5d_X_sq_dvd hmB
      rwa [chiB, conj_ζ_sq] at this
    have hdvd : (X - C (r * T)) ^ 2 ∣ (chiA (ζ ^ 2) (cellPoint q)).toPoly := by
      have e : chiA (ζ ^ 2) (cellPoint q) = switchingCubic (ζ ^ 2) (ζ ^ 2 - 1)
          (ζ • scale r (tau (flow T w (ζ ^ 2)))) := by
        rw [chiA, hqy, hv1, hcm]
      rw [e, htr]
      exact l5d_sq_dvd_comp hQ hr.ne' _
    exact l5d_discr_divByMonic_eq_zero (l5d_toPoly_ne_zero _).2.2 (mul_ne_zero hr.ne' hT.ne')
      hdvd
  · -- `∂_B`: the double root of `χ_B` at `0` on `𝒞₂(ζ², 0, 2)` becomes one of `χ_{B,1}`
    rintro q hq ⟨p, hp, hx⟩
    have hpD := l5d_topFaceTwo_sub hp.1
    set w := cellPoint p with hw
    have hw0 : w ∈ sectionZero := cellPoint_mem_sectionZero hpD
    obtain ⟨hfcw, -, hmB, -⟩ := topFaceTwo_switching hp.1
    obtain ⟨-, hFB⟩ := (firstSwitchTime_topFaceTwo hp.1).1 hp.2.le
    have hx' : classOf (tau (poincare w)) = cellClass q := by rw [hFB]; exact hx
    have hy := tau_mem_sectionZero (poincare_mem_sectionZero hw0)
    obtain ⟨v, hv, r, hr, hqy⟩ := (classOf_eq_classOf_iff hy
      (cellPoint_mem_sectionZero (l5d_openBoxOne_sub hq))).1 hx'
    have hu : v * ζ = ζ := by
      have h := hfc1 q hq
      rwa [hqy, l5d_firstControl_smul_scale hv hr (tau_ne_zero (poincare_ne_zero hw0.1)),
        l5d_firstControl_tau_poincare hw0.1, hfcw, conj_ζ_sq] at h
    have hv1 : v = 1 := by
      have hζ0 : ζ ≠ 0 := ne_zero_of_mem_VT ζ_mem_VT
      exact (mul_left_inj' hζ0).1 (by rw [hu, one_mul])
    have hT := firstSwitchTime_pos hw0.1
    have htr := l5d_cubic_transfer one_mem_VT hr.ne' (firstSwitchTime w) w (ζ ^ 2) (ζ ^ 2) ζ
    rw [conj_ζ_sq, conj_ζ, one_mul, one_mul, one_smul] at htr
    have hQ : X ^ 2 ∣ (switchingCubic (ζ ^ 2) (ζ ^ 2 - ζ) w).toPoly := by
      have := l5d_X_sq_dvd hmB
      rwa [chiB, conj_ζ_sq] at this
    have hdvd : (X - C (r * firstSwitchTime w)) ^ 2 ∣ (chiB ζ (cellPoint q)).toPoly := by
      have e : chiB ζ (cellPoint q) = switchingCubic ζ (ζ - ζ ^ 2)
          (scale r (tau (flow (firstSwitchTime w) w (ζ ^ 2)))) := by
        rw [chiB, conj_ζ, hqy, hv1, one_smul, poincare, hfcw]
      rw [e, htr]
      exact l5d_sq_dvd_comp hQ hr.ne' _
    exact l5d_discr_divByMonic_eq_zero (l5d_toPoly_ne_zero _).2.1 (mul_ne_zero hr.ne' hT.ne')
      hdvd

/-! ### The parts `𝒟₀, …, 𝒟₄` -/

/-- The points of an open box at which the Poincaré map switches to the control `v`: the first
control of `F(cellPoint p)` is `v` (on the first cell, `v = 1` when the active switching function is
`χ_A`, `v = ζ²` when it is `χ_B`; on the second cell, `v = 1` resp. `v = ζ`). -/
noncomputable def switchSet (box : Set (Fin 3 → ℝ)) (v : ℂ) : Set (Fin 3 → ℝ) :=
  {p | p ∈ box ∧ firstControl (poincare (cellPoint p)) = v}

/-- The points of the open first box in a set of `Ξ_{𝒲,0}/V_T` (for the loci `∂_A`, `∂_res`). -/
noncomputable def boxCoords (S : Set XiW0Quot) : Set (Fin 3 → ℝ) :=
  {p | p ∈ openBoxOne ∧ cellClass p ∈ S}

/-- `𝒟₁` (TeX 12359–12366): "the part of the geometric partition [of the first big cell by
`∂_res ∪ ∂_A`] containing the face `𝒞₂(ζ, 0, 2)` (that is, the face `θ₂ = π`)": the closure of the
union of the connected components of the open first box minus the closure of `∂_A ∪ ∂_res` whose
closures meet the top face. -/
noncomputable def partD1 : Set (Fin 3 → ℝ) :=
  closure {p | p ∈ openBoxOne \ closure (boxCoords (bdA ∪ bdRes)) ∧
    (closure (connectedComponentIn (openBoxOne \ closure (boxCoords (bdA ∪ bdRes))) p) ∩
      topFaceOne).Nonempty}

/-- `𝒟₂` (TeX 12427–12434): the part of the second big cell containing `𝒞₂^A`, on which the active
switching function is `χ_{A,0}`: the closure of the points of the open second box switching to
`1`. -/
noncomputable def partD2 : Set (Fin 3 → ℝ) := closure (switchSet openBoxTwo 1)

/-- `𝒟₃` (TeX 12436–12438): the other part of the second big cell, on which the active switching
function is `χ_{B,1}`: the closure of the points switching to `ζ`. -/
noncomputable def partD3 : Set (Fin 3 → ℝ) := closure (switchSet openBoxTwo ζ)

/-- `𝒟₄ := 𝔦(𝒟₃)` (TeX 12438–12440), the part of the first big cell on which the active switching
function is `χ_{B,1}`: the closure of the points of the open first box switching to `ζ²` (that it is
`𝔦(𝒟₃)` is part of `Proposition15_3_2`). -/
noncomputable def partD4 : Set (Fin 3 → ℝ) := closure (switchSet openBoxOne (ζ ^ 2))

/-- `𝒟₀` (TeX 12440–12443): "the closure of the complement in the first big cell of the union of
`𝒟₁` and `𝒟₄`". -/
noncomputable def partD0 : Set (Fin 3 → ℝ) := closure (closedBoxOne \ (partD1 ∪ partD4))

/-- The five parts, indexed as in the book. -/
noncomputable def partD : Fin 5 → Set (Fin 3 → ℝ) := ![partD0, partD1, partD2, partD3, partD4]

/-- A **geometric partition** of a set (TeX 12347–12350): "a collection of regular closed subsets
covering the set whose interiors are disjoint" (regular closed: the closure of its interior). -/
def IsGeometricPartition {α : Type*} [TopologicalSpace α] (S : Set α) (P : List (Set α)) :
    Prop :=
  (∀ D ∈ P, closure (interior D) = D) ∧ (∀ x, x ∈ S ↔ ∃ D ∈ P, x ∈ D) ∧
    P.Pairwise fun D D' ↦ Disjoint (interior D) (interior D')

/-- **Proposition 15.3.2** (`prop:partition`, label of this formalization; unlabelled, TeX
12467–12491), as a named proposition (it rests on Figures 15.2–15.3; gap G15.2). "Let `𝒟_i`,
`i = 0, 1, 2, 3, 4` be the geometric partition of the two big cells defined as above. The
Fuller–Poincaré map extends continuously from the interiors of `𝒟_i` to functions `F_i` on the
closures `𝒟_i`, for `i = 0, 1, 2, 3, 4`. The involution acts on the parts
by `𝒟₃ ↔ 𝒟₄`. Moreover, `𝒟₁, 𝒟₂, 𝒟₀` are each in self involution."

Precisely: `𝒟₀, 𝒟₁, 𝒟₄` and `𝒟₂, 𝒟₃` are geometric partitions of the closed first and second big
cells (in coordinates); there are maps `F_i`, continuous on `𝒟_i` and equal to `F` on the interior
of `𝒟_i`; and `τ ∘ F₃` maps `𝒟₃` onto `𝒟₄`, `τ ∘ F₄` maps `𝒟₄` onto `𝒟₃`, and `τ ∘ F_i` maps `𝒟_i`
onto itself for `i = 0, 1, 2` (as sets of `Ξ_{𝒲,0}/V_T`).

The book's proof sketch: discontinuities in the interior of a big cell lie on
`{res_AB = 0} ∪ {Δ_{A0} = 0} ∪ {Δ_{B1} = 0}` (`continuousAt_firstSwitchTime_of_ne_zero`); by Lemma
13.2.4 the involution maps them to the boundary faces (`discr_resAB_eq_zero_of_mem_bd`); on the
2-cells the only discontinuity is `Δ_{A0} = 0` on `𝒞₂(ζ², 0, 2)` (`firstSwitchTime_topFaceTwo`);
pulling back with `𝔦` gives all discontinuities. The topology (regular closed parts, their number,
`𝒟₀` a "very small bubble" attached to `∂_A`) is read off the figures.

Certification plan (layer 5b): the parts are semi-algebraic in `(r₂, cos ψ, sin ψ, cos θ₂, sin θ₂)`
after the substitution of the explicit Poincaré map; a cylindrical decomposition of the cells by
the signs of `Δ_{A,0}`, `Δ_{B,1}`, `res_AB` and of the switching polynomials at the candidate
roots, with interval enclosures of the root branches, decides the switch and the continuity on each
piece. **Not used by Theorem 16.1.1**, whose numerical hypotheses
(`SmoothedPolygons/Ch16/BasinHypotheses.lean`) avoid the curved parts. -/
def Proposition15_3_2 : Prop :=
  IsGeometricPartition closedBoxOne [partD0, partD1, partD4] ∧
    IsGeometricPartition closedBoxTwo [partD2, partD3] ∧
    ∃ G : Fin 5 → (Fin 3 → ℝ) → XiW0Quot,
      (∀ i, ContinuousOn (G i) (partD i) ∧
        ∀ p ∈ interior (partD i), G i p = poincareAngZero (cellClass p)) ∧
      (fun p ↦ tauZero (G 3 p)) '' partD 3 = cellClass '' partD 4 ∧
      (fun p ↦ tauZero (G 4 p)) '' partD 4 = cellClass '' partD 3 ∧
      ∀ i : Fin 5, i ≤ 2 → (fun p ↦ tauZero (G i p)) '' partD i = cellClass '' partD i

end TriFuller

end SmoothedPolygons
