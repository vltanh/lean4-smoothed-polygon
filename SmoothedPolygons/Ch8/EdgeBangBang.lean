module

public import SmoothedPolygons.Ch8.EdgeLandau

/-!
# Extremals of the edge control problem are bang-bang (Theorem 8.1.4)

Theorem 8.1.4 (`thm:edge`): every extremal lifted trajectory of the edge control problem on a
closed interval, normal or abnormal, has a bang-bang control `u_e = ±½` with finitely many
switches. The switching function is `λ₂` (the costate dual to `y`), and the proof shows that its
zeros are isolated: a zero with `λ₂' ≠ 0` is transversal; at a zero with `λ₂' = 0` the costate is
given by (8.1.8) (`eqn_edge_zero`: the extremal is normal there and `x = ±√(-λ₃/λ_cost)`, which
happens at most twice since `x' = y > 0`:
`IsEdgeProblemExtremal.exists_tangentialZeros_subset_pair`), and such a zero is isolated by
Lemma 8.1.5 (`lem:lambda2-Landau`: `λ₂(t) = C tⁿ + O(tⁿ⁺¹)` with `C ≠ 0`, by Gronwall,
Corollary A.1.3).

Lemma 8.1.5 is in `SmoothedPolygons/Ch8/EdgeLandau.lean`.

The private helpers (prefixes `l3d_`, `l3n_`) are: the monotonicity of `f₂` in the control and of
`x` in time, and the bounds on the control-dependent terms along a trajectory (the continuity
arguments of TeX 6846–6852);
the derivative of `λ₂` at its zeros; and the passage from Lemma 8.1.5, stated on a two-sided
interval `(-t₁, t₁)`, to a zero at an endpoint of `[0, T]` (`l3d_landau_glue`: the state and
the normalized costate are continued past the endpoint with the control `u_e = 0`, for which the
solution of (8.1.3), (8.1.7) is explicit: `x = x₀ + y₀ t`, `y = y₀`, `λ₁ = 2x₀t/y₀ + t²`,
`λ₂ = -2x₀t²/y₀ - 2t³/3`).
-/

@[expose] public section

namespace SmoothedPolygons

open Set MeasureTheory Filter Topology Asymptotics
open scoped Interval

/-! ### Elementary facts about `f₂` -/

/-- `-1 + 2√3 x u ≤ -1 + √3 m` for `|x| ≤ m` and `u ∈ [-½, ½]`. -/
private lemma l3d_den_le {x u m : ℝ} (hxm : |x| ≤ m) (hu : u ∈ edgeControlSet) :
    -1 + 2 * √3 * x * u ≤ -1 + √3 * m := by
  have hu' : |u| ≤ 1 / 2 := abs_le.mpr ⟨hu.1, hu.2⟩
  have h3 : 0 ≤ √3 := Real.sqrt_nonneg 3
  have h1 : 2 * √3 * x * u ≤ |2 * √3 * x * u| := le_abs_self _
  have habs : |2 * √3 * x * u| = 2 * √3 * (|x| * |u|) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg h3, abs_two]; ring
  have h2 : |x| * |u| ≤ m * (1 / 2) :=
    mul_le_mul hxm hu' (abs_nonneg _) ((abs_nonneg x).trans hxm)
  nlinarith

/-- `|x| < 1/√3` is `√3 |x| < 1`. -/
private lemma l3d_sqrt3_mul_lt {x : ℝ} (hx : |x| < 1 / √3) : √3 * |x| < 1 := by
  have hs3 : 0 < √3 := by positivity
  rw [lt_div_iff₀ hs3] at hx
  linarith

/-- On the state space, the denominator `-1 + 2√3 x u_e` of `f₂` is negative. -/
private lemma l3d_den_neg {x u : ℝ} (hx : |x| < 1 / √3) (hu : u ∈ edgeControlSet) :
    -1 + 2 * √3 * x * u < 0 :=
  edgeF₂_denom_neg (abs_lt.mp hx).1 (abs_lt.mp hx).2 hu

/-- `f₂` is strictly decreasing in `u_e ∈ [-½, ½]` on the state space (TeX 6840–6841):
`f₂(u) - f₂(v) = 2√3 y² (v - u)/((-1 + 2√3 x u)(-1 + 2√3 x v))`. -/
private lemma l3d_edgeF₂_lt {x y u v : ℝ} (hx : |x| < 1 / √3) (hy : 0 < y)
    (hu : u ∈ edgeControlSet) (hv : v ∈ edgeControlSet) (huv : u < v) :
    edgeF₂ x y v < edgeF₂ x y u := by
  have hdu := l3d_den_neg hx hu
  have hdv := l3d_den_neg hx hv
  have hdu' := hdu.ne
  have hdv' := hdv.ne
  have hs3 : 0 < √3 := by positivity
  have key : edgeF₂ x y u - edgeF₂ x y v =
      2 * √3 * y ^ 2 * (v - u) / ((-1 + 2 * √3 * x * u) * (-1 + 2 * √3 * x * v)) := by
    unfold edgeF₂
    rw [div_sub_div _ _ hdu' hdv']
    congr 1
    ring
  have hpos : 0 < 2 * √3 * y ^ 2 * (v - u) / ((-1 + 2 * √3 * x * u) * (-1 + 2 * √3 * x * v)) :=
    div_pos (by have := sub_pos.mpr huv; positivity) (mul_pos_of_neg_of_neg hdu hdv)
  linarith

/-! ### Consequences of the definition of an edge extremal -/

/-- The first two state equations (8.1.3), `x' = y` and `y' = f₂`, in integral form, with the
integrability of their right-hand sides. -/
private lemma l3d_state {T : ℝ} {ue : ℝ → ℝ} {q : ℝ → Fin 3 → ℝ} {ν : ℝ}
    {p : ℝ → StrongDual ℝ (Fin 3 → ℝ)} (h : IsEdgeProblemExtremal T ue q ν p) :
    IntervalIntegrable (fun s ↦ q s 1) volume 0 T ∧
      IntervalIntegrable (fun s ↦ edgeF₂ (q s 0) (q s 1) (ue s)) volume 0 T ∧
      (∀ t ∈ Icc 0 T, q t 0 = q 0 0 + ∫ s in (0 : ℝ)..t, q s 1) ∧
      ∀ t ∈ Icc 0 T, q t 1 = q 0 1 + ∫ s in (0 : ℝ)..t, edgeF₂ (q s 0) (q s 1) (ue s) := by
  obtain ⟨hT, ⟨⟨-, -, -, hqi, hqe⟩, -⟩, -⟩ := h
  have hcomp : ∀ i : Fin 3,
      IntervalIntegrable (fun s ↦ edgeField (q s) (ue s) i) volume 0 T ∧
        ∀ t ∈ Icc 0 T, q t i = q 0 i + ∫ s in (0 : ℝ)..t, edgeField (q s) (ue s) i := by
    intro i
    let L : (Fin 3 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
    refine ⟨⟨L.integrable_comp hqi.1, L.integrable_comp hqi.2⟩, fun t ht ↦ ?_⟩
    have hsub : IntervalIntegrable (fun s ↦ edgeField (q s) (ue s)) volume 0 t :=
      hqi.mono_set (by rw [uIcc_of_le ht.1, uIcc_of_le hT.le]; exact Icc_subset_Icc le_rfl ht.2)
    have := L.intervalIntegral_comp_comm hsub
    rw [hqe t ht, Pi.add_apply]
    congr 1
    exact this.symm
  exact ⟨(hcomp 0).1, (hcomp 1).1, (hcomp 0).2, (hcomp 1).2⟩

/-- The costates `λ₁, λ₂` are continuous on `[0, T]` (TeX 6846: "continuous by construction"). -/
private lemma l3d_costate {T : ℝ} {ue : ℝ → ℝ} {q : ℝ → Fin 3 → ℝ} {ν : ℝ}
    {p : ℝ → StrongDual ℝ (Fin 3 → ℝ)} (h : IsEdgeProblemExtremal T ue q ν p) :
    ContinuousOn (fun t ↦ edgeCostate (p t) 0) (Icc 0 T) ∧
      ContinuousOn (fun t ↦ edgeCostate (p t) 1) (Icc 0 T) := by
  obtain ⟨-, hi1, he1, hi2, he2⟩ := eqn_costate_edge h
  have hT := h.1
  have key : ∀ {F f : ℝ → ℝ}, IntervalIntegrable f volume 0 T →
      (∀ t ∈ Icc 0 T, F t = F 0 + ∫ s in (0 : ℝ)..t, f s) → ContinuousOn F (Icc 0 T) := by
    intro F f hf hF
    have hf' : IntegrableOn f (uIcc 0 T) volume := by
      rw [uIcc_of_le hT.le]
      exact (intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).mp hf
    have hc := intervalIntegral.continuousOn_primitive_interval hf'
    rw [uIcc_of_le hT.le] at hc
    exact (continuousOn_const.add hc).congr hF
  exact ⟨key hi1 he1, key hi2 he2⟩

/-- The non-control part of an extremal is bounded: `|f₂(x(t), y(t), u)|` and
`|4√3 y(t) u/(-1 + 2√3 x(t) u)|` are bounded on `[0, T] × [-½, ½]` (the denominator stays away
from `0` by compactness of `[0, T]`, TeX 6846–6852). -/
private lemma l3d_bound {T : ℝ} {ue : ℝ → ℝ} {q : ℝ → Fin 3 → ℝ} {ν : ℝ}
    {p : ℝ → StrongDual ℝ (Fin 3 → ℝ)} (h : IsEdgeProblemExtremal T ue q ν p) :
    ∃ M, ∀ t ∈ Icc 0 T, ∀ u ∈ edgeControlSet,
      |edgeF₂ (q t 0) (q t 1) u| ≤ M ∧ |4 * √3 * q t 1 * u / (-1 + 2 * √3 * q t 0 * u)| ≤ M := by
  obtain ⟨hT, ⟨⟨-, -, hqc, -, -⟩, hdom⟩, -⟩ := h
  have hK : IsCompact (Icc 0 T) := isCompact_Icc
  have hX : ContinuousOn (fun t ↦ |q t 0|) (Icc 0 T) :=
    ((continuous_apply 0).comp_continuousOn hqc).abs
  have hY : ContinuousOn (fun t ↦ q t 1) (Icc 0 T) := (continuous_apply 1).comp_continuousOn hqc
  obtain ⟨t₀, ht₀, hmax⟩ := hK.exists_isMaxOn (nonempty_Icc.mpr hT.le) hX
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hY
  obtain ⟨-, hx1, hx2⟩ := hdom t₀ ht₀
  have hm : √3 * |q t₀ 0| < 1 := l3d_sqrt3_mul_lt (abs_lt.mpr ⟨hx1, hx2⟩)
  have hd : 0 < 1 - √3 * |q t₀ 0| := by linarith
  have h3 : 0 < √3 := by positivity
  refine ⟨√3 * C ^ 2 / (1 - √3 * |q t₀ 0|) + 2 * √3 * C / (1 - √3 * |q t₀ 0|),
    fun t ht u hu ↦ ?_⟩
  have hxm : |q t 0| ≤ |q t₀ 0| := hmax ht
  have hyC : |q t 1| ≤ C := by simpa [Real.norm_eq_abs] using hC t ht
  have hC0 : 0 ≤ C := (abs_nonneg _).trans hyC
  have hden : 1 - √3 * |q t₀ 0| ≤ |-1 + 2 * √3 * q t 0 * u| := by
    have := l3d_den_le hxm hu
    rw [abs_of_neg (show -1 + 2 * √3 * q t 0 * u < 0 by linarith)]
    linarith
  have hu' : |u| ≤ 1 / 2 := abs_le.mpr ⟨hu.1, hu.2⟩
  have hb1 : |edgeF₂ (q t 0) (q t 1) u| ≤ √3 * C ^ 2 / (1 - √3 * |q t₀ 0|) := by
    unfold edgeF₂
    rw [abs_div]
    refine div_le_div₀ (by positivity) ?_ hd hden
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos h3, abs_two, abs_pow]
    calc 2 * √3 * |q t 1| ^ 2 * |u| ≤ 2 * √3 * C ^ 2 * (1 / 2) := by gcongr
      _ = √3 * C ^ 2 := by ring
  have hb2 : |4 * √3 * q t 1 * u / (-1 + 2 * √3 * q t 0 * u)| ≤
      2 * √3 * C / (1 - √3 * |q t₀ 0|) := by
    rw [abs_div]
    refine div_le_div₀ (by positivity) ?_ hd hden
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos h3, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    calc 4 * √3 * |q t 1| * |u| ≤ 4 * √3 * C * (1 / 2) := by gcongr
      _ = 2 * √3 * C := by ring
  have hp1 : 0 ≤ √3 * C ^ 2 / (1 - √3 * |q t₀ 0|) := by positivity
  have hp2 : 0 ≤ 2 * √3 * C / (1 - √3 * |q t₀ 0|) := by positivity
  exact ⟨by linarith, by linarith⟩

/-- An inequality between functions continuous on `[0, T]`, `T > 0`, that holds almost everywhere
on `[0, T]` holds everywhere on `[0, T]`. -/
private lemma l3d_le_of_ae {T : ℝ} (hT : 0 < T) {f g : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 T))
    (hg : ContinuousOn g (Icc 0 T)) (h : ∀ᵐ t ∂(volume.restrict (Icc 0 T)), f t ≤ g t) :
    ∀ t ∈ Icc 0 T, f t ≤ g t := by
  have heq := Measure.eqOn_Icc_of_ae_eq volume hT.ne (f := fun t ↦ max (f t - g t) 0)
    (g := fun _ ↦ 0) (h.mono fun t ht ↦ max_eq_right (sub_nonpos.mpr ht))
    ((continuous_id.max continuous_const).comp_continuousOn (hf.sub hg)) continuousOn_const
  intro t ht
  have := heq ht
  simp only at this
  linarith [le_max_left (f t - g t) 0]

/-- **`H = 0` at a zero of the switching function** (proof of (8.1.8), TeX 6866–6869). At a time
`t₂ ∈ [0, T]` with `λ₂(t₂) = 0`, `λ₁ y + λ₃/y + λ_cost x²/y = 0`: off `λ₂ = 0` the Hamiltonian
`H = (λ₁ y + λ₃/y + λ_cost x²/y) + λ₂ f₂` vanishes almost everywhere, the bracket is continuous
and `λ₂ f₂` tends to `0` with `λ₂` (`f₂` is bounded, `l3d_bound`). -/
private lemma l3d_ham_zero {T : ℝ} {ue : ℝ → ℝ} {q : ℝ → Fin 3 → ℝ} {ν : ℝ}
    {p : ℝ → StrongDual ℝ (Fin 3 → ℝ)} (h : IsEdgeProblemExtremal T ue q ν p) {t₂ : ℝ}
    (ht₂ : t₂ ∈ Icc 0 T) (hz : edgeCostate (p t₂) 1 = 0) :
    edgeCostate (p t₂) 0 * q t₂ 1 + edgeCostate (p t₂) 2 / q t₂ 1 +
      ν * (q t₂ 0 ^ 2 / q t₂ 1) = 0 := by
  obtain ⟨M, hM⟩ := l3d_bound h
  obtain ⟨hc0, hc1⟩ := l3d_costate h
  obtain ⟨h3, -⟩ := eqn_costate_edge h
  obtain ⟨hT, ⟨⟨-, hU, hqc, -, -⟩, hdom⟩, -, -, -, -, hH⟩ := h
  have hX : ContinuousOn (fun t ↦ q t 0) (Icc 0 T) := (continuous_apply 0).comp_continuousOn hqc
  have hY : ContinuousOn (fun t ↦ q t 1) (Icc 0 T) := (continuous_apply 1).comp_continuousOn hqc
  have hY0 : ∀ t ∈ Icc 0 T, q t 1 ≠ 0 := fun t ht ↦ (hdom t ht).1.ne'
  have hG : ContinuousOn (fun t ↦ edgeCostate (p t) 0 * q t 1 + edgeCostate (p 0) 2 / q t 1 +
      ν * (q t 0 ^ 2 / q t 1)) (Icc 0 T) :=
    ((hc0.mul hY).add (continuousOn_const.div hY hY0)).add
      (continuousOn_const.mul ((hX.pow 2).div hY hY0))
  have hle := l3d_le_of_ae hT hG.abs (continuousOn_const.mul hc1.abs) (g := fun t ↦
    M * |edgeCostate (p t) 1|) (by
      filter_upwards [hH, ae_restrict_mem measurableSet_Icc] with t ht htI
      rw [eqn_edge_ham] at ht
      unfold edgeHamiltonian at ht
      have hGt : edgeCostate (p t) 0 * q t 1 + edgeCostate (p 0) 2 / q t 1 +
          ν * (q t 0 ^ 2 / q t 1) = -(edgeCostate (p t) 1 * edgeF₂ (q t 0) (q t 1) (ue t)) := by
        rw [← h3 t htI]
        linarith
      rw [hGt, abs_neg, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hM t htI (ue t) (hU t htI)).1 (abs_nonneg _))
  have := hle t₂ ht₂
  simp only [hz, abs_zero, mul_zero] at this
  rw [h3 t₂ ht₂]
  exact abs_nonpos_iff.mp this

/-- **The derivative of `λ₂` at its zeros** (TeX 6846–6852): at a time `t₂ ∈ [0, T]` with
`λ₂(t₂) = 0`, `λ₂` is differentiable within `[0, T]` with derivative the right-hand side of
(8.1.7) at `t₂`, `λ₃/y² - λ₁ + λ_cost x²/y²` (its control-dependent term `λ₂ · 4√3 y u_e/(…)` is
a bounded multiple of `λ₂`, so the integrand of (8.1.7) is continuous at `t₂`). -/
private lemma l3d_hasDerivWithinAt {T : ℝ} {ue : ℝ → ℝ} {q : ℝ → Fin 3 → ℝ} {ν : ℝ}
    {p : ℝ → StrongDual ℝ (Fin 3 → ℝ)} (h : IsEdgeProblemExtremal T ue q ν p) {t₂ : ℝ}
    (ht₂ : t₂ ∈ Icc 0 T) (hz : edgeCostate (p t₂) 1 = 0) :
    HasDerivWithinAt (fun t ↦ edgeCostate (p t) 1)
      (edgeCostate (p t₂) 2 / q t₂ 1 ^ 2 - edgeCostate (p t₂) 0 + ν * q t₂ 0 ^ 2 / q t₂ 1 ^ 2)
      (Icc 0 T) t₂ := by
  obtain ⟨M, hM⟩ := l3d_bound h
  obtain ⟨hc0, hc1⟩ := l3d_costate h
  obtain ⟨h3, -, -, hi2, he2⟩ := eqn_costate_edge h
  obtain ⟨hT, ⟨⟨-, hU, hqc, -, -⟩, hdom⟩, -⟩ := h
  have hX : ContinuousOn (fun t ↦ q t 0) (Icc 0 T) := (continuous_apply 0).comp_continuousOn hqc
  have hY : ContinuousOn (fun t ↦ q t 1) (Icc 0 T) := (continuous_apply 1).comp_continuousOn hqc
  have hY0 : ∀ t ∈ Icc 0 T, q t 1 ^ 2 ≠ 0 := fun t ht ↦ pow_ne_zero 2 (hdom t ht).1.ne'
  set F : ℝ → ℝ := fun s ↦ edgeCostateRHS₂ ν (edgeCostate (p s) 0) (edgeCostate (p s) 1)
    (edgeCostate (p s) 2) (q s 0) (q s 1) (ue s) with hF
  set R : ℝ → ℝ := fun s ↦ edgeCostate (p 0) 2 / q s 1 ^ 2 - edgeCostate (p s) 0 +
    ν * q s 0 ^ 2 / q s 1 ^ 2 with hRdef
  have hR : ContinuousOn R (Icc 0 T) :=
    ((continuousOn_const.div (hY.pow 2) hY0).sub hc0).add
      ((continuousOn_const.mul (hX.pow 2)).div (hY.pow 2) hY0)
  have hFR : ∀ s ∈ Icc 0 T, F s = R s - edgeCostate (p s) 1 *
      (4 * √3 * q s 1 * ue s / (-1 + 2 * √3 * q s 0 * ue s)) := by
    intro s hs
    simp only [hF, hRdef, edgeCostateRHS₂, h3 s hs]
    ring
  have hFt₂ : F t₂ = R t₂ := by rw [hFR t₂ ht₂, hz, zero_mul, sub_zero]
  have hcont : ContinuousWithinAt F (Icc 0 T) t₂ := by
    have h1 : Tendsto (fun s ↦ edgeCostate (p s) 1 *
        (4 * √3 * q s 1 * ue s / (-1 + 2 * √3 * q s 0 * ue s))) (𝓝[Icc 0 T] t₂) (𝓝 0) := by
      apply squeeze_zero_norm' (a := fun s ↦ M * |edgeCostate (p s) 1|)
      · filter_upwards [self_mem_nhdsWithin] with s hs
        rw [Real.norm_eq_abs, abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hM s hs (ue s) (hU s hs)).2 (abs_nonneg _)
      · have := ((hc1 t₂ ht₂).tendsto.abs).const_mul M
        simpa [hz] using this
    have h2 := (hR t₂ ht₂).tendsto.sub h1
    rw [sub_zero, ← hFt₂] at h2
    exact h2.congr' (eventually_nhdsWithin_of_forall fun s hs ↦ (hFR s hs).symm)
  have hint : IntervalIntegrable F volume 0 t₂ :=
    hi2.mono_set (by rw [uIcc_of_le ht₂.1, uIcc_of_le hT.le]; exact Icc_subset_Icc le_rfl ht₂.2)
  have : Fact (t₂ ∈ Icc 0 T) := ⟨ht₂⟩
  have hmeas : StronglyMeasurableAtFilter F (𝓝[Icc 0 T] t₂) volume :=
    ⟨Icc 0 T, self_mem_nhdsWithin,
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).mp hi2).aestronglyMeasurable⟩
  have hd := (intervalIntegral.integral_hasDerivWithinAt_right hint (s := Icc 0 T)
    (t := Icc 0 T) hmeas hcont).const_add (edgeCostate (p 0) 1)
  rw [hFt₂] at hd
  have := hd.congr_of_mem (fun s hs ↦ he2 s hs) ht₂
  simpa [hRdef, h3 t₂ ht₂] using this

/-- A continuous linear functional on `ℝ³` vanishing on the basis vectors is zero. -/
private lemma l3d_eq_zero_of_edgeCostate {p : StrongDual ℝ (Fin 3 → ℝ)}
    (h : ∀ i, edgeCostate p i = 0) : p = 0 := by
  ext v
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum, zero_apply]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [show Pi.single i (v i) = v i • (Pi.single i 1 : Fin 3 → ℝ) by
    rw [← Pi.single_smul, smul_eq_mul, mul_one], map_smul]
  have := h i
  unfold edgeCostate at this
  rw [this, smul_zero]

/-! ### The maximization rule and equation (8.1.8) -/

/-- **The maximization rule of the edge problem** (proof of Theorem 8.1.4, TeX 6840–6845): the
only term of the Hamiltonian (8.1.6) depending on the control is `λ₂ f₂`, and `f₂` is strictly
decreasing in `u_e` (`∂f₂/∂u_e = -2√3 y²/(-1 + 2√3 x u_e)² < 0` on the state space), so at
almost every time `λ₂ > 0` forces `u_e = -½` and `λ₂ < 0` forces `u_e = ½`: `λ₂` is the
switching function. Proof: `Pontryagin.IsMaximal` with `eqn_edge_ham`, and the strict
monotonicity of `f₂` in `u_e` (`l3d_edgeF₂_lt`). -/
theorem IsEdgeProblemExtremal.ae_control_eq_of_switching {T : ℝ} {ue : ℝ → ℝ}
    {q : ℝ → Fin 3 → ℝ} {ν : ℝ} {p : ℝ → StrongDual ℝ (Fin 3 → ℝ)}
    (h : IsEdgeProblemExtremal T ue q ν p) :
    ∀ᵐ t, t ∈ Icc 0 T →
      (0 < edgeCostate (p t) 1 → ue t = -(1 / 2)) ∧ (edgeCostate (p t) 1 < 0 → ue t = 1 / 2) := by
  obtain ⟨-, ⟨⟨-, hU, -, -, -⟩, hdom⟩, -, -, -, hmax, -⟩ := h
  filter_upwards [(ae_restrict_iff' measurableSet_Icc).mp hmax] with t ht htI
  have hut := hU t htI
  obtain ⟨hy, hx1, hx2⟩ := hdom t htI
  have hx : |q t 0| < 1 / √3 := abs_lt.mpr ⟨hx1, hx2⟩
  have hdiff : ∀ u ∈ edgeControlSet, edgeCostate (p t) 1 * edgeF₂ (q t 0) (q t 1) u ≤
      edgeCostate (p t) 1 * edgeF₂ (q t 0) (q t 1) (ue t) := by
    intro u hu
    have := ht htI u hu
    rw [eqn_edge_ham, eqn_edge_ham] at this
    unfold edgeHamiltonian at this
    linarith
  have hm : (-(1 / 2) : ℝ) ∈ edgeControlSet := ⟨le_rfl, by norm_num⟩
  have hp : (1 / 2 : ℝ) ∈ edgeControlSet := ⟨by norm_num, le_rfl⟩
  refine ⟨fun hpos ↦ ?_, fun hneg ↦ ?_⟩
  · by_contra hne
    have hlt := l3d_edgeF₂_lt hx hy hm hut (lt_of_le_of_ne hut.1 (Ne.symm hne))
    have := hdiff _ hm
    have := mul_lt_mul_of_pos_left hlt hpos
    linarith
  · by_contra hne
    have hlt := l3d_edgeF₂_lt hx hy hut hp (lt_of_le_of_ne hut.2 hne)
    have := hdiff _ hp
    have := mul_lt_mul_of_neg_left hlt hneg
    linarith

/-- **Equation (8.1.8)** (`eqn:edge-zero`, the claim in the proof of Theorem 8.1.4, TeX
6854–6874). At a time `t₂` where the switching function `λ₂` and its derivative vanish, the
costate is `λ₃ = -x(t₂)² λ_cost`, `λ₁(t₂) = 0`, and `λ_cost ≠ 0` (the extremal is normal there).
So `-λ₃/λ_cost ≥ 0` and `x(t₂) = ±√(-λ₃/λ_cost)`.

The derivative of `λ₂` at its zero exists: the right-hand side of (8.1.7) for `λ₂` is continuous
at a zero of `λ₂` (its control-dependent term is a bounded multiple of `λ₂`, TeX 6846–6852;
the hypothesis is stated with the derivative within `[0, T]`, which covers the endpoints).

Proof (the book's): `H = 0` at `t₂` (`l3d_ham_zero`: from `H = 0` almost everywhere, by
continuity, since at `λ₂ = 0` the Hamiltonian does not depend on the control) and
`λ₂' = -∂H/∂y = 0` at `t₂` (`l3d_hasDerivWithinAt`, from `eqn_costate_edge`, and the uniqueness
of derivatives within `[0, T]`) form the linear system `λ₁ y + λ₃/y + λ_cost x²/y = 0`,
`λ₃/y² - λ₁ + λ_cost x²/y² = 0` in `(λ₁, λ₃)`, of determinant `2/y ≠ 0`, whose solution is the
one displayed. If `λ_cost = 0`, then `(λ_cost, λ₁, λ₂, λ₃) = 0` at `t₂`, against the
nontriviality of the maximum principle. -/
theorem eqn_edge_zero {T : ℝ} {ue : ℝ → ℝ} {q : ℝ → Fin 3 → ℝ} {ν : ℝ}
    {p : ℝ → StrongDual ℝ (Fin 3 → ℝ)} (h : IsEdgeProblemExtremal T ue q ν p) {t₂ : ℝ}
    (ht₂ : t₂ ∈ Icc 0 T) (hz : edgeCostate (p t₂) 1 = 0)
    (hd : HasDerivWithinAt (fun t ↦ edgeCostate (p t) 1) 0 (Icc 0 T) t₂) :
    edgeCostate (p t₂) 2 = -(q t₂ 0) ^ 2 * ν ∧ edgeCostate (p t₂) 0 = 0 ∧ ν ≠ 0 := by
  have hT := h.1
  have hy := (h.2.1.2 t₂ ht₂).1
  have hy' := hy.ne'
  have hR := (uniqueDiffOn_Icc hT t₂ ht₂).eq_deriv _ (l3d_hasDerivWithinAt h ht₂ hz) hd
  have hH := l3d_ham_zero h ht₂ hz
  have e1 : edgeCostate (p t₂) 0 * q t₂ 1 ^ 2 + edgeCostate (p t₂) 2 + ν * q t₂ 0 ^ 2 = 0 := by
    have : (edgeCostate (p t₂) 0 * q t₂ 1 + edgeCostate (p t₂) 2 / q t₂ 1 +
        ν * (q t₂ 0 ^ 2 / q t₂ 1)) * q t₂ 1 =
        edgeCostate (p t₂) 0 * q t₂ 1 ^ 2 + edgeCostate (p t₂) 2 + ν * q t₂ 0 ^ 2 := by
      field_simp
    rw [← this, hH, zero_mul]
  have e2 : edgeCostate (p t₂) 2 - edgeCostate (p t₂) 0 * q t₂ 1 ^ 2 + ν * q t₂ 0 ^ 2 = 0 := by
    have : (edgeCostate (p t₂) 2 / q t₂ 1 ^ 2 - edgeCostate (p t₂) 0 +
        ν * q t₂ 0 ^ 2 / q t₂ 1 ^ 2) * q t₂ 1 ^ 2 =
        edgeCostate (p t₂) 2 - edgeCostate (p t₂) 0 * q t₂ 1 ^ 2 + ν * q t₂ 0 ^ 2 := by
      field_simp
    rw [← this, hR, zero_mul]
  have hl₃ : edgeCostate (p t₂) 2 = -(q t₂ 0) ^ 2 * ν := by linarith
  have hl₁ : edgeCostate (p t₂) 0 = 0 := by
    have : edgeCostate (p t₂) 0 * q t₂ 1 ^ 2 = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right (by positivity)
  refine ⟨hl₃, hl₁, fun hν ↦ h.2.2.2.1 t₂ ht₂ ?_⟩
  have hp : p t₂ = 0 := l3d_eq_zero_of_edgeCostate fun i ↦ by
    fin_cases i
    · exact hl₁
    · exact hz
    · simpa [hν] using hl₃
  rw [hν, hp]
  rfl

/-! ### At most two zeros of the second kind -/

/-- Along an edge extremal, `x` is strictly increasing on `[0, T]`: `x' = y > 0` (8.1.3). -/
private lemma l3n_strictMonoOn_x {T : ℝ} {ue : ℝ → ℝ} {q : ℝ → Fin 3 → ℝ} {ν : ℝ}
    {p : ℝ → StrongDual ℝ (Fin 3 → ℝ)} (h : IsEdgeProblemExtremal T ue q ν p) :
    StrictMonoOn (fun t ↦ q t 0) (Icc 0 T) := by
  obtain ⟨hyi, -, hxe, -⟩ := l3d_state h
  have hT := h.1
  have hsub : ∀ {b}, b ∈ Icc 0 T → IntervalIntegrable (fun s ↦ q s 1) volume 0 b := fun hb ↦
    hyi.mono_set (by rw [uIcc_of_le hb.1, uIcc_of_le hT.le]; exact Icc_subset_Icc le_rfl hb.2)
  intro s hs t ht hst
  have hpos : 0 < ∫ r in s..t, q r 1 :=
    intervalIntegral.intervalIntegral_pos_of_pos_on ((hsub hs).symm.trans (hsub ht))
      (fun r hr ↦ (h.2.1.2 r ⟨by linarith [hs.1, hr.1], by linarith [ht.2, hr.2]⟩).1) hst
  have e := intervalIntegral.integral_interval_sub_left (hsub ht) (hsub hs)
  change q s 0 < q t 0
  rw [hxe t ht, hxe s hs]
  linarith

/-- At a zero `t₂` of `λ₂` with `λ₂'(t₂) = 0`, `x(t₂) = ±√(-λ₃/λ_cost)` (TeX 6858–6859: (8.1.8),
`eqn_edge_zero`, with `λ₃` constant, `eqn_costate_edge`). -/
private lemma l3n_x_eq_of_tangential {T : ℝ} {ue : ℝ → ℝ} {q : ℝ → Fin 3 → ℝ} {ν : ℝ}
    {p : ℝ → StrongDual ℝ (Fin 3 → ℝ)} (h : IsEdgeProblemExtremal T ue q ν p) {t₂ : ℝ}
    (ht₂ : t₂ ∈ Icc 0 T) (hz : edgeCostate (p t₂) 1 = 0)
    (hd : HasDerivWithinAt (fun t ↦ edgeCostate (p t) 1) 0 (Icc 0 T) t₂) :
    q t₂ 0 = √(-edgeCostate (p 0) 2 / ν) ∨ q t₂ 0 = -√(-edgeCostate (p 0) 2 / ν) := by
  obtain ⟨hl₃, -, hν⟩ := eqn_edge_zero h ht₂ hz hd
  rw [(eqn_costate_edge h).1 t₂ ht₂] at hl₃
  have hsq : q t₂ 0 ^ 2 = -edgeCostate (p 0) 2 / ν := by
    rw [hl₃]
    field_simp
  rw [← abs_eq (Real.sqrt_nonneg _), ← hsq, Real.sqrt_sq_eq_abs]

/-- **At most two zeros of the second kind** (proof of Theorem 8.1.4, TeX 6875–6879). Along an
edge extremal there are at most two times `t₂ ∈ [0, T]` with `λ₂(t₂) = λ₂'(t₂) = 0`: at such a
time `x(t₂) = ±√(-λ₃/λ_cost)` by (8.1.8) (`eqn_edge_zero`; `λ₃` is constant), and `x` is strictly
increasing (`x' = y > 0`, (8.1.3)), so it takes each of these two values at most once. -/
theorem IsEdgeProblemExtremal.exists_tangentialZeros_subset_pair {T : ℝ} {ue : ℝ → ℝ}
    {q : ℝ → Fin 3 → ℝ} {ν : ℝ} {p : ℝ → StrongDual ℝ (Fin 3 → ℝ)}
    (h : IsEdgeProblemExtremal T ue q ν p) :
    ∃ a b : ℝ, {t ∈ Icc 0 T | edgeCostate (p t) 1 = 0 ∧
      HasDerivWithinAt (fun t ↦ edgeCostate (p t) 1) 0 (Icc 0 T) t} ⊆ {a, b} := by
  have hinj := (l3n_strictMonoOn_x h).injOn
  have hsing : ∀ c : ℝ, ∃ a : ℝ, {t ∈ Icc 0 T | q t 0 = c} ⊆ {a} := by
    intro c
    have hs : {t ∈ Icc 0 T | q t 0 = c}.Subsingleton := fun s hs t ht ↦
      hinj hs.1 ht.1 (hs.2.trans ht.2.symm)
    rcases hs.eq_empty_or_singleton with he | ⟨a, ha⟩
    · exact ⟨0, by rw [he]; exact empty_subset _⟩
    · exact ⟨a, ha.subset⟩
  obtain ⟨a, ha⟩ := hsing (√(-edgeCostate (p 0) 2 / ν))
  obtain ⟨b, hb⟩ := hsing (-√(-edgeCostate (p 0) 2 / ν))
  refine ⟨a, b, fun t ht ↦ ?_⟩
  rcases l3n_x_eq_of_tangential h ht.1 ht.2.1 ht.2.2 with hx | hx
  · exact Or.inl (ha ⟨ht.1, hx⟩)
  · exact Or.inr (hb ⟨ht.1, hx⟩)

/-! ### Lemma 8.1.5 at an endpoint -/

open Classical in
/-- The function equal to `f` on `I` and to `g` off `I`. -/
private noncomputable def l3d_glue (I : Set ℝ) (f g : ℝ → ℝ) : ℝ → ℝ := I.piecewise f g

private lemma l3d_glue_of_mem {I : Set ℝ} {f g : ℝ → ℝ} {s : ℝ} (hs : s ∈ I) :
    l3d_glue I f g s = f s := by
  simp only [l3d_glue, Set.piecewise, hs, ite_true]

private lemma l3d_glue_of_not_mem {I : Set ℝ} {f g : ℝ → ℝ} {s : ℝ} (hs : s ∉ I) :
    l3d_glue I f g s = g s := by
  simp only [l3d_glue, Set.piecewise, hs, ite_false]

/-- The half-lines `[0, ∞)`, `(-∞, 0]` and the whole line, with the properties used to glue. -/
private lemma l3d_halfLine {I : Set ℝ} (hI : I = Ici 0 ∨ I = Iic 0 ∨ I = univ) :
    MeasurableSet I ∧ IsClosed I ∧ frontier I ⊆ {0} ∧ (0 : ℝ) ∈ I ∧ I.OrdConnected ∧
      ∀ t ∉ I, ∀ s ∈ Ι (0 : ℝ) t, s ∉ I ∨ s = 0 := by
  rcases hI with rfl | rfl | rfl
  · refine ⟨measurableSet_Ici, isClosed_Ici, frontier_Ici.subset, self_mem_Ici, ordConnected_Ici,
      fun t ht s hs ↦ ?_⟩
    simp only [mem_Ici, not_le] at ht ⊢
    rw [uIoc_of_ge ht.le] at hs
    rcases hs.2.lt_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr h
  · refine ⟨measurableSet_Iic, isClosed_Iic, frontier_Iic.subset, self_mem_Iic, ordConnected_Iic,
      fun t ht s hs ↦ ?_⟩
    simp only [mem_Iic, not_le] at ht ⊢
    rw [uIoc_of_le ht.le] at hs
    exact Or.inl hs.1
  · exact ⟨MeasurableSet.univ, isClosed_univ, by simp, mem_univ _, ordConnected_univ,
      fun t ht ↦ absurd (mem_univ t) ht⟩

/-- `∫₀ᵗ f = F t - F 0` for an antiderivative `F` of a continuous `f`. -/
private lemma l3d_integral_poly {F f : ℝ → ℝ} (hF : ∀ s, HasDerivAt F (f s) s) (hf : Continuous f)
    (t : ℝ) : ∫ s in (0 : ℝ)..t, f s = F t - F 0 :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hF s) (hf.intervalIntegrable _ _)

/-- **Lemma 8.1.5 on one side of `0`** (used at the endpoints of `[0, T]`, proof of Theorem
8.1.4, TeX 6884–6886). Let `I` be `[0, ∞)`, `(-∞, 0]` or `ℝ`, and let the state and the
normalized costate solve (8.1.3) and (8.1.7) on `I ∩ (-t₁, t₁)` with the data of Lemma 8.1.5.
Then `λ₂ ≠ 0` at the points of `I` near `0` other than `0`.

Proof: continue `(u_e, x, y, λ₁, λ₂)` to the other side of `0` by the solution with the control
`u_e = 0`: `x = x₀ + y₀ t`, `y = y₀`, `λ₁ = 2x₀t/y₀ + t²`, `λ₂ = -2x₀t²/y₀ - 2t³/3` (these solve
(8.1.3), (8.1.7) with `(x, y, λ₁, λ₂)(0) = (x₀, y₀, 0, 0)`, `λ_cost = -1`, `λ₃ = x₀²`). The glued
functions satisfy the hypotheses of Lemma 8.1.5 on a small `(-δ, δ)` (with `δ ≤ t₁` and
`δ y₀ ≤ 1/√3 - |x₀|`, so that `|x| < 1/√3` on the continuation), which gives the claim. For
`I = ℝ` nothing is glued. -/
private lemma l3d_landau_glue {x₀ y₀ : ℝ} (hx₀ : |x₀| < 1 / √3) (hy₀ : 0 < y₀) {I : Set ℝ}
    (hI : I = Ici 0 ∨ I = Iic 0 ∨ I = univ) {t₁ : ℝ} (ht₁ : 0 < t₁) {ue x y l₁ l₂ : ℝ → ℝ}
    (hue : Measurable ue) (hU : ∀ t ∈ I ∩ Ioo (-t₁) t₁, ue t ∈ edgeControlSet)
    (hD : ∀ t ∈ I ∩ Ioo (-t₁) t₁, 0 < y t ∧ |x t| < 1 / √3)
    (hcx : ContinuousOn x (I ∩ Ioo (-t₁) t₁)) (hcy : ContinuousOn y (I ∩ Ioo (-t₁) t₁))
    (hc₁ : ContinuousOn l₁ (I ∩ Ioo (-t₁) t₁)) (hc₂ : ContinuousOn l₂ (I ∩ Ioo (-t₁) t₁))
    (hx : ∀ t ∈ I ∩ Ioo (-t₁) t₁, x t = x₀ + ∫ s in (0 : ℝ)..t, y s)
    (hy : ∀ t ∈ I ∩ Ioo (-t₁) t₁, y t = y₀ + ∫ s in (0 : ℝ)..t, edgeF₂ (x s) (y s) (ue s))
    (hl₁ : ∀ t ∈ I ∩ Ioo (-t₁) t₁,
      l₁ t = ∫ s in (0 : ℝ)..t, edgeCostateRHS₁ (-1) (l₂ s) (x s) (y s) (ue s))
    (hl₂ : ∀ t ∈ I ∩ Ioo (-t₁) t₁,
      l₂ t = ∫ s in (0 : ℝ)..t,
        edgeCostateRHS₂ (-1) (l₁ s) (l₂ s) (x₀ ^ 2) (x s) (y s) (ue s)) :
    ∀ᶠ t in 𝓝 0, t ∈ I → t ≠ 0 → l₂ t ≠ 0 := by
  obtain ⟨hIm, hIc, hIf, hI0, hIo, hIout⟩ := l3d_halfLine hI
  obtain ⟨n, -, C, -, hL⟩ := lemma8_1_5 hx₀ hy₀
  -- the radius `δ` of the interval on which Lemma 8.1.5 is applied
  have hδ0 : 0 < min t₁ ((1 / √3 - |x₀|) / y₀) := lt_min ht₁ (div_pos (by linarith) hy₀)
  have hδt : min t₁ ((1 / √3 - |x₀|) / y₀) ≤ t₁ := min_le_left _ _
  have hδx : min t₁ ((1 / √3 - |x₀|) / y₀) * y₀ ≤ 1 / √3 - |x₀| := by
    have := min_le_right t₁ ((1 / √3 - |x₀|) / y₀)
    rwa [le_div_iff₀ hy₀] at this
  set δ := min t₁ ((1 / √3 - |x₀|) / y₀)
  have hsub : ∀ {t}, t ∈ Ioo (-δ) δ → t ∈ I → t ∈ I ∩ Ioo (-t₁) t₁ := fun ht hI' ↦
    ⟨hI', by linarith [ht.1], by linarith [ht.2]⟩
  -- values at `0`
  have h0 : (0 : ℝ) ∈ I ∩ Ioo (-t₁) t₁ := ⟨hI0, by linarith, ht₁⟩
  have hx0 : x 0 = x₀ := by simpa using hx 0 h0
  have hy0 : y 0 = y₀ := by simpa using hy 0 h0
  have hl₁0 : l₁ 0 = 0 := by simpa using hl₁ 0 h0
  have hl₂0 : l₂ 0 = 0 := by simpa using hl₂ 0 h0
  -- integrals over `[0, t]` on either side
  have hae : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ 0 := by
    rw [ae_iff]
    simp
  have hin : ∀ {t}, t ∈ I → ∀ {f g : ℝ → ℝ}, (∀ s ∈ I, f s = g s) →
      ∫ s in (0 : ℝ)..t, f s = ∫ s in (0 : ℝ)..t, g s := fun ht _ _ hfg ↦
    intervalIntegral.integral_congr fun s hs ↦ hfg s (hIo.uIcc_subset hI0 ht hs)
  have hout : ∀ {t}, t ∉ I → ∀ {f g : ℝ → ℝ}, (∀ s ∉ I, f s = g s) →
      ∫ s in (0 : ℝ)..t, f s = ∫ s in (0 : ℝ)..t, g s := fun ht _ _ hfg ↦
    intervalIntegral.integral_congr_ae
      (hae.mono fun s hs0 hs ↦ hfg s ((hIout _ ht s hs).resolve_right hs0))
  -- continuity of a glued function
  have hglue_c : ∀ {f g : ℝ → ℝ}, ContinuousOn f (I ∩ Ioo (-t₁) t₁) → Continuous g →
      f 0 = g 0 → ContinuousOn (l3d_glue I f g) (Ioo (-δ) δ) := by
    intro f g hf hg hfg
    classical
    unfold l3d_glue
    refine ContinuousOn.piecewise ?_ ?_ hg.continuousOn
    · rintro a ⟨-, ha⟩
      obtain rfl : a = 0 := hIf ha
      exact hfg
    · rw [hIc.closure_eq]
      exact hf.mono fun t ht ↦ hsub ht.1 ht.2
  have key := hL δ (l3d_glue I ue fun _ ↦ 0) (l3d_glue I x fun t ↦ x₀ + y₀ * t)
    (l3d_glue I y fun _ ↦ y₀) (l3d_glue I l₁ fun t ↦ 2 * x₀ / y₀ * t + t ^ 2)
    (l3d_glue I l₂ fun t ↦ -(2 * x₀ / y₀) * t ^ 2 - 2 / 3 * t ^ 3) hδ0
    (by classical exact hue.piecewise hIm measurable_const) ?_ ?_
    (hglue_c hcx (by fun_prop) (by simp [hx0])) (hglue_c hcy (by fun_prop) (by simp [hy0]))
    (hglue_c hc₁ (by fun_prop) (by simp [hl₁0])) (hglue_c hc₂ (by fun_prop) (by simp [hl₂0]))
    ?_ ?_ ?_ ?_
  · -- the conclusion
    filter_upwards [eventually_nhdsWithin_iff.mp key.2] with t ht htI ht0
    have := ht ht0
    rwa [l3d_glue_of_mem htI] at this
  · -- the control set
    intro t ht
    by_cases htI : t ∈ I
    · rw [l3d_glue_of_mem htI]
      exact hU t (hsub ht htI)
    · rw [l3d_glue_of_not_mem htI]
      exact ⟨by norm_num, by norm_num⟩
  · -- the state space
    intro t ht
    by_cases htI : t ∈ I
    · rw [l3d_glue_of_mem htI, l3d_glue_of_mem htI]
      exact hD t (hsub ht htI)
    · rw [l3d_glue_of_not_mem htI, l3d_glue_of_not_mem htI]
      refine ⟨hy₀, ?_⟩
      have h1 : |y₀ * t| < δ * y₀ := by
        rw [abs_mul, abs_of_pos hy₀, mul_comm]
        exact mul_lt_mul_of_pos_right (abs_lt.mpr ht) hy₀
      calc |x₀ + y₀ * t| ≤ |x₀| + |y₀ * t| := abs_add_le _ _
        _ < 1 / √3 := by linarith
  · -- `x' = y`
    intro t ht
    by_cases htI : t ∈ I
    · rw [hin htI (g := y) fun s hs ↦ l3d_glue_of_mem hs, l3d_glue_of_mem htI]
      exact hx t (hsub ht htI)
    · rw [hout htI (g := fun _ ↦ y₀) fun s hs ↦ l3d_glue_of_not_mem hs, l3d_glue_of_not_mem htI]
      simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
      ring
  · -- `y' = f₂`
    intro t ht
    by_cases htI : t ∈ I
    · rw [hin htI (g := fun s ↦ edgeF₂ (x s) (y s) (ue s)) fun s hs ↦ by
        simp only [l3d_glue_of_mem hs], l3d_glue_of_mem htI]
      exact hy t (hsub ht htI)
    · rw [hout htI (g := fun _ ↦ 0) fun s hs ↦ by
        simp only [l3d_glue_of_not_mem hs, edgeF₂, mul_zero, zero_div], l3d_glue_of_not_mem htI]
      simp
  · -- the costate equation for `λ₁`
    intro t ht
    by_cases htI : t ∈ I
    · rw [hin htI (g := fun s ↦ edgeCostateRHS₁ (-1) (l₂ s) (x s) (y s) (ue s)) fun s hs ↦ by
        simp only [l3d_glue_of_mem hs], l3d_glue_of_mem htI]
      exact hl₁ t (hsub ht htI)
    · rw [hout htI (g := fun s ↦ 2 * x₀ / y₀ + 2 * s) fun s hs ↦ by
        simp only [l3d_glue_of_not_mem hs, edgeCostateRHS₁]
        field_simp
        ring, l3d_glue_of_not_mem htI,
        l3d_integral_poly (F := fun s ↦ 2 * x₀ / y₀ * s + s ^ 2) (fun s ↦ by
          have := ((hasDerivAt_id' s).const_mul (2 * x₀ / y₀)).fun_add (hasDerivAt_pow 2 s)
          convert this using 1
          push_cast
          ring)
          (by fun_prop)]
      ring
  · -- the costate equation for `λ₂`
    intro t ht
    by_cases htI : t ∈ I
    · rw [hin htI (g := fun s ↦ edgeCostateRHS₂ (-1) (l₁ s) (l₂ s) (x₀ ^ 2) (x s) (y s) (ue s))
        fun s hs ↦ by simp only [l3d_glue_of_mem hs], l3d_glue_of_mem htI]
      exact hl₂ t (hsub ht htI)
    · rw [hout htI (g := fun s ↦ -(4 * x₀ / y₀) * s - 2 * s ^ 2) fun s hs ↦ by
        simp only [l3d_glue_of_not_mem hs, edgeCostateRHS₂, mul_zero, zero_div, sub_zero]
        field_simp
        ring, l3d_glue_of_not_mem htI,
        l3d_integral_poly (F := fun s ↦ -(2 * x₀ / y₀) * s ^ 2 - 2 / 3 * s ^ 3) (fun s ↦ by
          have := ((hasDerivAt_pow 2 s).const_mul (-(2 * x₀ / y₀))).sub
            ((hasDerivAt_pow 3 s).const_mul (2 / 3))
          convert this using 1
          push_cast
          ring)
          (by fun_prop)]
      ring

/-- The translation `F(t₂ + τ) = F(t₂) + ∫₀^τ f(t₂ + s) ds` of an integral equation on `[0, T]`. -/
private lemma l3d_shift {T : ℝ} {F f : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 T)
    (hF : ∀ t ∈ Icc 0 T, F t = F 0 + ∫ s in (0 : ℝ)..t, f s) {t₂ τ : ℝ} (ht₂ : t₂ ∈ Icc 0 T)
    (hτ : t₂ + τ ∈ Icc 0 T) : F (t₂ + τ) = F t₂ + ∫ s in (0 : ℝ)..τ, f (t₂ + s) := by
  have hT : 0 ≤ T := ht₂.1.trans ht₂.2
  have hsub : ∀ {b}, b ∈ Icc 0 T → IntervalIntegrable f volume 0 b := fun hb ↦
    hf.mono_set (by rw [uIcc_of_le hb.1, uIcc_of_le hT]; exact Icc_subset_Icc le_rfl hb.2)
  rw [intervalIntegral.integral_comp_add_left f t₂, add_zero, hF _ hτ, hF _ ht₂, add_assoc,
    ← intervalIntegral.integral_interval_sub_left (hsub hτ) (hsub ht₂)]
  ring

/-- The side(s) of `t₂` inside `[0, T]`: a set `I` (`[0, ∞)` at `t₂ = 0`, `(-∞, 0]` at `t₂ = T`,
`ℝ` inside) and a radius `t₁` with `t₂ + (I ∩ (-t₁, t₁)) ⊆ [0, T]` and `[0, T] - t₂ ⊆ I`. -/
private lemma l3d_choose {T t₂ : ℝ} (hT : 0 < T) (ht₂ : t₂ ∈ Icc 0 T) :
    ∃ I : Set ℝ, ∃ t₁ : ℝ, (I = Ici 0 ∨ I = Iic 0 ∨ I = univ) ∧ 0 < t₁ ∧
      (∀ τ ∈ I ∩ Ioo (-t₁) t₁, t₂ + τ ∈ Icc 0 T) ∧ ∀ s ∈ Icc 0 T, s - t₂ ∈ I := by
  rcases eq_or_lt_of_le ht₂.1 with h0 | h0
  · refine ⟨Ici 0, T, Or.inl rfl, hT, fun τ hτ ↦ ?_, fun s hs ↦ ?_⟩
    · have := mem_Ici.mp hτ.1
      have := hτ.2.2
      constructor <;> linarith
    · have := hs.1
      exact mem_Ici.mpr (by linarith)
  rcases eq_or_lt_of_le ht₂.2 with h1 | h1
  · refine ⟨Iic 0, T, Or.inr (Or.inl rfl), hT, fun τ hτ ↦ ?_, fun s hs ↦ ?_⟩
    · have := mem_Iic.mp hτ.1
      have := hτ.2.1
      constructor <;> linarith
    · have := hs.2
      exact mem_Iic.mpr (by linarith)
  · refine ⟨univ, min t₂ (T - t₂), Or.inr (Or.inr rfl), lt_min h0 (by linarith),
      fun τ hτ ↦ ?_, fun _ _ ↦ mem_univ _⟩
    have := hτ.2.1
    have := hτ.2.2
    have := min_le_left t₂ (T - t₂)
    have := min_le_right t₂ (T - t₂)
    constructor <;> linarith

/-- **A zero of the second kind is isolated** (proof of Theorem 8.1.4, TeX 6881–6886). At a zero
`t₂` of `λ₂` where (8.1.8) holds (`λ₁(t₂) = 0`, `λ₃ = -x(t₂)² λ_cost`, `λ_cost ≠ 0`), after the
time translation `t₂ ↦ 0` and the normalization `λ_cost = -1` (division of the costate by
`-λ_cost > 0`; (8.1.7) is linear in `(λ_cost, λ)`), Lemma 8.1.5 (`lemma8_1_5`, through
`l3d_landau_glue` at the endpoints of `[0, T]`) shows that `λ₂ ≠ 0` near `t₂`, `t ≠ t₂`. -/
private lemma l3d_isolated_tangential {T : ℝ} {ue : ℝ → ℝ} {q : ℝ → Fin 3 → ℝ} {ν : ℝ}
    {p : ℝ → StrongDual ℝ (Fin 3 → ℝ)} (h : IsEdgeProblemExtremal T ue q ν p) {t₂ : ℝ}
    (ht₂ : t₂ ∈ Icc 0 T) (hz : edgeCostate (p t₂) 1 = 0)
    (hl₃ : edgeCostate (p t₂) 2 = -(q t₂ 0) ^ 2 * ν) (hl₁ : edgeCostate (p t₂) 0 = 0)
    (hν0 : ν ≠ 0) :
    ∀ᶠ s in 𝓝 t₂, s ∈ Icc 0 T → s ≠ t₂ → edgeCostate (p s) 1 ≠ 0 := by
  obtain ⟨hyi, hfi, hxe, hye⟩ := l3d_state h
  obtain ⟨hc0, hc1⟩ := l3d_costate h
  obtain ⟨h3, hi1, he1, hi2, he2⟩ := eqn_costate_edge h
  obtain ⟨hT, ⟨⟨hum, hU, hqc, -, -⟩, hdom⟩, hν, -⟩ := h
  have hκ : 0 < -ν := by have := lt_of_le_of_ne hν hν0; linarith
  obtain ⟨I, t₁, hI, ht₁, hIT, hTI⟩ := l3d_choose hT ht₂
  have hJo : (I ∩ Ioo (-t₁) t₁).OrdConnected := (l3d_halfLine hI).2.2.2.2.1.inter ordConnected_Ioo
  have hJ0 : (0 : ℝ) ∈ I ∩ Ioo (-t₁) t₁ := ⟨(l3d_halfLine hI).2.2.2.1, by linarith, ht₁⟩
  have hx₀ : |q t₂ 0| < 1 / √3 := abs_lt.mpr ⟨(hdom t₂ ht₂).2.1, (hdom t₂ ht₂).2.2⟩
  have hmaps : MapsTo (fun τ ↦ t₂ + τ) (I ∩ Ioo (-t₁) t₁) (Icc 0 T) := fun τ hτ ↦ hIT τ hτ
  have hshift : ContinuousOn (fun τ : ℝ ↦ t₂ + τ) (I ∩ Ioo (-t₁) t₁) := by fun_prop
  have hcx : ContinuousOn (fun τ ↦ q (t₂ + τ) 0) (I ∩ Ioo (-t₁) t₁) :=
    ((continuous_apply 0).comp_continuousOn hqc).comp hshift hmaps
  have hcy : ContinuousOn (fun τ ↦ q (t₂ + τ) 1) (I ∩ Ioo (-t₁) t₁) :=
    ((continuous_apply 1).comp_continuousOn hqc).comp hshift hmaps
  have hc₁ : ContinuousOn (fun τ ↦ edgeCostate (p (t₂ + τ)) 0 / -ν) (I ∩ Ioo (-t₁) t₁) :=
    (hc0.comp hshift hmaps).div_const _
  have hc₂ : ContinuousOn (fun τ ↦ edgeCostate (p (t₂ + τ)) 1 / -ν) (I ∩ Ioo (-t₁) t₁) :=
    (hc1.comp hshift hmaps).div_const _
  have hx : ∀ τ ∈ I ∩ Ioo (-t₁) t₁, q (t₂ + τ) 0 = q t₂ 0 + ∫ s in (0 : ℝ)..τ, q (t₂ + s) 1 :=
    fun τ hτ ↦ l3d_shift (F := fun t ↦ q t 0) (f := fun s ↦ q s 1) hyi hxe ht₂ (hIT τ hτ)
  have hy : ∀ τ ∈ I ∩ Ioo (-t₁) t₁, q (t₂ + τ) 1 = q t₂ 1 +
      ∫ s in (0 : ℝ)..τ, edgeF₂ (q (t₂ + s) 0) (q (t₂ + s) 1) (ue (t₂ + s)) :=
    fun τ hτ ↦ l3d_shift (F := fun t ↦ q t 1) (f := fun s ↦ edgeF₂ (q s 0) (q s 1) (ue s)) hfi
      hye ht₂ (hIT τ hτ)
  have hl₁' : ∀ τ ∈ I ∩ Ioo (-t₁) t₁, edgeCostate (p (t₂ + τ)) 0 / -ν =
      ∫ s in (0 : ℝ)..τ, edgeCostateRHS₁ (-1) (edgeCostate (p (t₂ + s)) 1 / -ν)
        (q (t₂ + s) 0) (q (t₂ + s) 1) (ue (t₂ + s)) := by
    intro τ hτ
    have e := l3d_shift (F := fun t ↦ edgeCostate (p t) 0)
      (f := fun s ↦ edgeCostateRHS₁ ν (edgeCostate (p s) 1) (q s 0) (q s 1) (ue s)) hi1 he1 ht₂
      (hIT τ hτ)
    beta_reduce at e
    rw [e, hl₁, zero_add, ← intervalIntegral.integral_div]
    refine intervalIntegral.integral_congr fun s _ ↦ ?_
    simp only [edgeCostateRHS₁]
    field_simp
    ring
  have hl₂' : ∀ τ ∈ I ∩ Ioo (-t₁) t₁, edgeCostate (p (t₂ + τ)) 1 / -ν =
      ∫ s in (0 : ℝ)..τ, edgeCostateRHS₂ (-1) (edgeCostate (p (t₂ + s)) 0 / -ν)
        (edgeCostate (p (t₂ + s)) 1 / -ν) (q t₂ 0 ^ 2) (q (t₂ + s) 0) (q (t₂ + s) 1)
        (ue (t₂ + s)) := by
    intro τ hτ
    have e := l3d_shift (F := fun t ↦ edgeCostate (p t) 1)
      (f := fun s ↦ edgeCostateRHS₂ ν (edgeCostate (p s) 0) (edgeCostate (p s) 1)
        (edgeCostate (p s) 2) (q s 0) (q s 1) (ue s)) hi2 he2 ht₂ (hIT τ hτ)
    beta_reduce at e
    rw [e, hz, zero_add, ← intervalIntegral.integral_div]
    refine intervalIntegral.integral_congr fun s hs ↦ ?_
    have hs' := hIT s (hJo.uIcc_subset hJ0 hτ hs)
    rw [h3 _ hs', ← h3 _ ht₂, hl₃]
    simp only [edgeCostateRHS₂]
    field_simp
    ring
  have hev := l3d_landau_glue hx₀ (hdom t₂ ht₂).1 hI ht₁ (hum.comp (measurable_const_add t₂))
    (fun τ hτ ↦ hU _ (hIT τ hτ))
    (fun τ hτ ↦ ⟨(hdom _ (hIT τ hτ)).1, abs_lt.mpr ⟨(hdom _ (hIT τ hτ)).2.1,
      (hdom _ (hIT τ hτ)).2.2⟩⟩) hcx hcy hc₁ hc₂ hx hy hl₁' hl₂'
  have htend : Tendsto (fun s ↦ s - t₂) (𝓝 t₂) (𝓝 0) := by
    have := (continuous_sub_right t₂).tendsto t₂
    rwa [sub_self] at this
  filter_upwards [htend.eventually hev] with s hs hsI hst h0
  have := hs (hTI s hsI) (sub_ne_zero.mpr hst)
  rw [add_sub_cancel, h0, zero_div] at this
  exact this rfl

/-- **The switching function `λ₂` has finitely many zeros on `[0, T]`** (proof of Theorem 8.1.4,
TeX 6875–6890). The zeros with `λ₂' = 0` are at most two
(`IsEdgeProblemExtremal.exists_tangentialZeros_subset_pair`), and each of them is isolated by
Lemma 8.1.5 (`l3d_isolated_tangential`, with (8.1.8), `eqn_edge_zero`): an open set `U` containing
them meets the zero set only in them. Every other zero is transversal (`λ₂' ≠ 0`,
`l3d_hasDerivWithinAt`), hence isolated; the zeros off `U` form a compact set (closed in
`[0, T]`) of isolated points, so they are finitely many too. -/
private lemma l3d_finite_zeros {T : ℝ} {ue : ℝ → ℝ} {q : ℝ → Fin 3 → ℝ} {ν : ℝ}
    {p : ℝ → StrongDual ℝ (Fin 3 → ℝ)} (h : IsEdgeProblemExtremal T ue q ν p) :
    {t ∈ Icc 0 T | edgeCostate (p t) 1 = 0}.Finite := by
  obtain ⟨-, hc1⟩ := l3d_costate h
  -- the zeros of the second kind: at most two (TeX 6875–6879) ...
  obtain ⟨a, b, hab⟩ := h.exists_tangentialZeros_subset_pair
  have hZ₂ : {t ∈ Icc 0 T | edgeCostate (p t) 1 = 0 ∧
      HasDerivWithinAt (fun t ↦ edgeCostate (p t) 1) 0 (Icc 0 T) t}.Finite :=
    ((finite_singleton b).insert a).subset hab
  -- ... each isolated by Lemma 8.1.5 (TeX 6881–6886)
  have hV : ∀ t ∈ {t ∈ Icc 0 T | edgeCostate (p t) 1 = 0 ∧
      HasDerivWithinAt (fun t ↦ edgeCostate (p t) 1) 0 (Icc 0 T) t}, ∃ V : Set ℝ, IsOpen V ∧
        t ∈ V ∧ ∀ s ∈ V, s ∈ Icc 0 T → s ≠ t → edgeCostate (p s) 1 ≠ 0 := by
    intro t ht
    obtain ⟨hl₃, hl₁, hν0⟩ := eqn_edge_zero h ht.1 ht.2.1 ht.2.2
    obtain ⟨V, hVs, hVo, htV⟩ := eventually_nhds_iff.mp
      (l3d_isolated_tangential h ht.1 ht.2.1 hl₃ hl₁ hν0)
    exact ⟨V, hVo, htV, hVs⟩
  choose! V hVo hVt hVz using hV
  have hUo : IsOpen (⋃ t ∈ {t ∈ Icc 0 T | edgeCostate (p t) 1 = 0 ∧
      HasDerivWithinAt (fun t ↦ edgeCostate (p t) 1) 0 (Icc 0 T) t}, V t) :=
    isOpen_biUnion fun t ht ↦ hVo t ht
  -- the other zeros are transversal, hence isolated; those off `U` form a compact set
  have hZc : IsClosed {t ∈ Icc 0 T | edgeCostate (p t) 1 = 0} :=
    hc1.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hK := isCompact_Icc.of_isClosed_subset (hZc.sdiff hUo) fun t ht ↦ ht.1.1
  have hKfin := hK.finite (isDiscrete_iff_nhdsNE.mpr fun t ht ↦ by
    have hD := l3d_hasDerivWithinAt h ht.1.1 ht.1.2
    have hR : edgeCostate (p t) 2 / q t 1 ^ 2 - edgeCostate (p t) 0 +
        ν * q t 0 ^ 2 / q t 1 ^ 2 ≠ 0 := fun hR ↦ by
      rw [hR] at hD
      exact ht.2 (mem_iUnion₂.mpr ⟨t, ⟨ht.1.1, ht.1.2, hD⟩, hVt t ⟨ht.1.1, ht.1.2, hD⟩⟩)
    rw [inf_principal_eq_bot]
    exact eventually_nhdsWithin_iff.mpr
      ((eventually_nhdsWithin_iff.mp (hD.eventually_ne hR (c := 0))).mono
        fun s hs hst hmem ↦ hs ⟨hmem.1.1, hst⟩ hmem.1.2))
  refine (hZ₂.union hKfin).subset fun s hs ↦ ?_
  by_cases hsU : s ∈ ⋃ t ∈ {t ∈ Icc 0 T | edgeCostate (p t) 1 = 0 ∧
      HasDerivWithinAt (fun t ↦ edgeCostate (p t) 1) 0 (Icc 0 T) t}, V t
  · -- a zero in `U` is one of the zeros of the second kind
    obtain ⟨t, ht, hsV⟩ := mem_iUnion₂.mp hsU
    by_cases hst : s = t
    · exact Or.inl (hst ▸ ht)
    · exact absurd hs.2 (hVz t ht s hsV hs.1 hst)
  · exact Or.inr ⟨hs, hsU⟩

/-! ### Theorem 8.1.4 -/

/-- **Theorem 8.1.4** (`thm:edge`). Consider an extremal lifted trajectory of the edge control
system on a closed interval `[0, T]` (normal or abnormal). Then the control `u_e` is bang-bang
with finitely many switches: it is equal almost everywhere to a piecewise constant function with
values `±½` and finitely many switches on `[0, T]`.

(The book says "the optimal control function"; the statement and the proof concern any extremal,
E49.)

Proof (the book's, TeX 6820–6894):
1. The costate equations (8.1.7) (`eqn_costate_edge`); `λ₃` is constant.
2. `λ₂` is the switching function (`IsEdgeProblemExtremal.ae_control_eq_of_switching`).
3. `λ₂` is differentiable within `[0, T]` at each of its zeros, with derivative the right-hand
   side of (8.1.7) at that time (`l3d_hasDerivWithinAt`: its control-dependent term
   `λ₂ · (bounded)` tends to `0` with `λ₂`, the book's reason). Departure from the paper: the
   book claims that `λ₂'` is continuous (TeX 6846–6852), which holds only after changing the
   control on a null set (the right-hand side of (8.1.7) involves the measurable control, so
   `λ₂` is only absolutely continuous); the proof uses `λ₂'` only at the zeros of `λ₂`, so only
   the derivative there is proved and used.
4. At a zero with `λ₂' = 0`, (8.1.8) holds (`eqn_edge_zero`): `λ_cost ≠ 0` and
   `x = ±√(-λ₃/λ_cost)`. Since `x` is strictly increasing (`x' = y > 0`), there are at most two
   such zeros (`IsEdgeProblemExtremal.exists_tangentialZeros_subset_pair`, TeX 6875–6879). Every
   other zero is transversal (`λ₂' ≠ 0`), hence isolated.
5. After the time translation `t₂ = 0` and the normalization `λ_cost = -1` (the costate equations
   are linear in `(λ_cost, λ)`), Lemma 8.1.5 (`lemma8_1_5`) shows that the zeros of the second
   kind are isolated too (`l3d_isolated_tangential`). At an endpoint of `[0, T]` the state and
   costate are extended beyond it with the control `u_e = 0`, for which the solution is
   explicit (`l3d_landau_glue`); the lemma holds for every measurable control.
6. So the zeros of `λ₂` on `[0, T]` are finitely many (`l3d_finite_zeros`: the at most two zeros
   of the second kind, and the transversal zeros away from them, which form a compact set of
   isolated points); off them `λ₂` has a constant sign near each time of `(0, T)`, and the
   control is a.e. the constant `∓½` there (step 2). The book's "adjusting `u_e` on a set of
   measure zero" is the almost-everywhere formulation. -/
theorem theorem8_1_4 {T : ℝ} {ue : ℝ → ℝ} {q : ℝ → Fin 3 → ℝ} {ν : ℝ}
    {p : ℝ → StrongDual ℝ (Fin 3 → ℝ)} (h : IsEdgeProblemExtremal T ue q ν p) :
    ∃ S : Finset ℝ, ∀ t ∈ Ioo 0 T, t ∉ S → ∃ c ∈ ({-(1 / 2), 1 / 2} : Set ℝ), ∃ ε > 0,
      ∀ᵐ τ, τ ∈ Ioo (t - ε) (t + ε) → ue τ = c := by
  obtain ⟨-, hc1⟩ := l3d_costate h
  have hfin := l3d_finite_zeros h
  have hrule := IsEdgeProblemExtremal.ae_control_eq_of_switching h
  refine ⟨hfin.toFinset, fun t ht htS ↦ ?_⟩
  have htI : t ∈ Icc 0 T := Ioo_subset_Icc_self ht
  have hne : edgeCostate (p t) 1 ≠ 0 := fun h0 ↦ htS (hfin.mem_toFinset.mpr ⟨htI, h0⟩)
  have hcont : ContinuousAt (fun s ↦ edgeCostate (p s) 1) t :=
    hc1.continuousAt (Icc_mem_nhds ht.1 ht.2)
  rcases hne.lt_or_gt with hneg | hpos
  · obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp
      ((hcont.eventually (gt_mem_nhds hneg)).and (Ioo_mem_nhds ht.1 ht.2))
    refine ⟨1 / 2, by simp, ε, hε, ?_⟩
    filter_upwards [hrule] with τ hτ hτε
    obtain ⟨h1, h2⟩ := hball τ (by rwa [Real.ball_eq_Ioo])
    exact (hτ (Ioo_subset_Icc_self h2)).2 h1
  · obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp
      ((hcont.eventually (lt_mem_nhds hpos)).and (Ioo_mem_nhds ht.1 ht.2))
    refine ⟨-(1 / 2), by simp, ε, hε, ?_⟩
    filter_upwards [hrule] with τ hτ hτε
    obtain ⟨h1, h2⟩ := hball τ (by rwa [Real.ball_eq_Ioo])
    exact (hτ (Ioo_subset_Icc_self h2)).1 h1

end SmoothedPolygons
