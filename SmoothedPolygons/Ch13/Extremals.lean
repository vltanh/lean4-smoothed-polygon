module

public import SmoothedPolygons.Ch13.SingularLocus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Chapter 13: extremals of the Fuller system with measurable controls

Two facts that Chapter 13 of Hales–Vajjha, *Packings of Smoothed Polygons*, uses about the
solutions of the Fuller system (13.2.1) with a measurable control satisfying the maximum
condition (13.2.5), and that connect them with the constant-control objects (first control, first
switching time, the Poincaré map):

* "if `u` is chosen according to the maximum principle, then `H_F` is constant along trajectories"
  (TeX 10741–10742; asserted; inventory, gap 1): `l4st_hamMax_eq_of_maxCondition`;
* "The first control is determined by the maximum principle for `t` small and nonnegative"
  (proof of Lemma 13.2.6, TeX 10978–10979): every such solution starting at `z⁰ ≠ 0` uses the
  first control up to the first switching time, `l4st_eq_flow_of_maxCondition`. This is what makes
  the Poincaré map, defined with constant controls, the map along "the solution … with control
  defined by the maximum principle" of TeX 11243–11245.

The proofs use the fundamental theorem of calculus for absolutely continuous functions
(`AbsolutelyContinuousOnInterval.const_of_ae_hasDerivAt_zero`) and Lebesgue's differentiation
theorem; the helpers are prefixed `l4d_`.
-/

@[expose] public section

namespace SmoothedPolygons

open Complex MeasureTheory Set TriFuller Filter Topology

namespace TriFuller

/-! ### Helpers: absolute continuity along a trajectory -/

/-- Almost every real number differs from `x`. -/
private lemma l4d_ae_ne (x : ℝ) : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ x := by
  simp [ae_iff, measure_singleton]

/-- A primitive of a function bounded by `C` on `[a, b]` is `C`-Lipschitz there. -/
private lemma l4d_lipschitzOnWith_of_eq_primitive {f g : ℝ → ℂ} {a b C : ℝ}
    (hg : IntervalIntegrable g volume a b) (hgC : ∀ t ∈ Icc a b, ‖g t‖ ≤ C)
    (hf : ∀ t ∈ Icc a b, f t = f a + ∫ s in a..t, g s) :
    LipschitzOnWith (Real.toNNReal C) f (Icc a b) := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
  have hab : a ≤ b := hx.1.trans hx.2
  have hsub : ∀ c ∈ Icc a b, uIcc a c ⊆ uIcc a b := fun c hc ↦ by
    rw [uIcc_of_le hab, uIcc_of_le hc.1]; exact Icc_subset_Icc le_rfl hc.2
  rw [dist_eq_norm, hf x hx, hf y hy, add_sub_add_left_eq_sub,
    intervalIntegral.integral_interval_sub_left (hg.mono_set (hsub x hx))
      (hg.mono_set (hsub y hy)), Real.dist_eq]
  calc ‖∫ s in y..x, g s‖ ≤ C * |x - y| :=
        intervalIntegral.norm_integral_le_of_norm_le_const fun s hs ↦
          hgC s (uIcc_subset_Icc hy hx (uIoc_subset_uIcc hs))
    _ ≤ ↑(Real.toNNReal C) * |x - y| := by gcongr; exact Real.le_coe_toNNReal C

/-- The coordinates of a trajectory with controls in `V_T` are absolutely continuous (Lipschitz)
on `[t₁, t₂]`. -/
private lemma l4d_ac_traj {t₁ t₂ : ℝ} {z : ℝ → Fin 3 → ℂ} {u : ℝ → ℂ}
    (h : IsTrajectory VT t₁ t₂ z u) (j : Fin 3) :
    AbsolutelyContinuousOnInterval (fun t ↦ z t j) t₁ t₂ := by
  have hle := h.1.le
  have hI : t₁ ∈ Icc t₁ t₂ := ⟨le_rfl, hle⟩
  have hII : t₂ ∈ Icc t₁ t₂ := ⟨hle, le_rfl⟩
  have hc0 := l4d_continuousOn_traj l4d_VT_subset_UT h 0
  have hc1 := l4d_continuousOn_traj l4d_VT_subset_UT h 1
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hc0
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hc1
  have hb := l4d_norm_le_one_of_traj l4d_VT_subset_UT h
  have L : ∃ K, LipschitzOnWith K (fun t ↦ z t j) (Icc t₁ t₂) := by
    fin_cases j
    · exact ⟨_, l4d_lipschitzOnWith_of_eq_primitive
        ((l4d_intervalIntegrable_control l4d_VT_subset_UT h hI hII).const_mul (-I))
        (fun t ht ↦ by
          rw [norm_mul, norm_neg, Complex.norm_I, one_mul]; exact hb t ht)
        fun t ht ↦ (h.2.2.2 t ht).1⟩
    · exact ⟨_, l4d_lipschitzOnWith_of_eq_primitive (hc0.intervalIntegrable_of_Icc hle)
        (fun t ht ↦ hC₀ t ht) fun t ht ↦ (h.2.2.2 t ht).2.1⟩
    · exact ⟨_, l4d_lipschitzOnWith_of_eq_primitive (hc1.intervalIntegrable_of_Icc hle)
        (fun t ht ↦ hC₁ t ht) fun t ht ↦ (h.2.2.2 t ht).2.2⟩
  obtain ⟨K, hK⟩ := L
  rw [← uIcc_of_le hle] at hK
  exact hK.absolutelyContinuousOnInterval

private lemma l4d_ac_re {f : ℝ → ℂ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun t ↦ (f t).re) a b :=
  (Complex.reCLM.lipschitzWith.comp_absolutelyContinuousOnInterval hf).congr
    fun t _ ↦ by simp

private lemma l4d_ac_im {f : ℝ → ℂ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun t ↦ (f t).im) a b :=
  (Complex.imCLM.lipschitzWith.comp_absolutelyContinuousOnInterval hf).congr
    fun t _ ↦ by simp

/-- The maximum of two absolutely continuous functions is absolutely continuous
(`max a b = (a + b + |a - b|)/2`). -/
private lemma l4d_ac_max {f g : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (fun t ↦ max (f t) (g t)) a b := by
  have habs : AbsolutelyContinuousOnInterval (fun t ↦ |f t - g t|) a b :=
    ((lipschitzWith_one_norm (E := ℝ)).comp_absolutelyContinuousOnInterval
      (hf.fun_sub hg)).congr fun t _ ↦ by simp [Real.norm_eq_abs]
  refine (((hf.fun_add hg).fun_add habs).const_mul (1 / 2)).congr fun t _ ↦ ?_
  rcases le_total (f t) (g t) with hle | hle
  · simp only [max_eq_right hle, abs_of_nonpos (sub_nonpos.2 hle)]; ring
  · simp only [max_eq_left hle, abs_of_nonneg (sub_nonneg.2 hle)]; ring

/-- `t ↦ H_F⁺(z(t))` is absolutely continuous along a trajectory. -/
private lemma l4d_ac_hamMax {t₁ t₂ : ℝ} {z : ℝ → Fin 3 → ℂ} {u : ℝ → ℂ}
    (h : IsTrajectory VT t₁ t₂ z u) :
    AbsolutelyContinuousOnInterval (fun t ↦ hamMax (z t)) t₁ t₂ := by
  have R : ∀ j, AbsolutelyContinuousOnInterval (fun t ↦ (z t j).re) t₁ t₂ :=
    fun j ↦ l4d_ac_re (l4d_ac_traj h j)
  have M : ∀ j, AbsolutelyContinuousOnInterval (fun t ↦ (z t j).im) t₁ t₂ :=
    fun j ↦ l4d_ac_im (l4d_ac_traj h j)
  have hham : ∀ v : ℂ, AbsolutelyContinuousOnInterval (fun t ↦ ham (z t) v) t₁ t₂ := by
    intro v
    refine ((((R 0).fun_mul (M 1).fun_neg).fun_add ((M 0).fun_mul (R 1))).fun_add
      (((R 2).const_mul v.re).fun_add ((M 2).const_mul v.im))).congr fun t _ ↦ ?_
    simp only [ham, l4d_RR_eq, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    ring
  exact (l4d_ac_max (hham 1) (l4d_ac_max (hham ζ) (hham (ζ ^ 2)))).congr fun t _ ↦ rfl

/-- The derivative of `RR(f, g)`. -/
private lemma l4d_hasDerivAt_RR {f g : ℝ → ℂ} {f' g' : ℂ} {t : ℝ} (hf : HasDerivAt f f' t)
    (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s ↦ RR (f s) (g s)) (RR f' (g t) + RR (f t) g') t := by
  have hs : HasDerivAt (fun s ↦ star (f s) * g s) (star f' * g t + star (f t) * g') t :=
    (HasDerivAt.star hf).mul hg
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hs
  convert h using 1
  · ext s; simp [RR]
  · simp [RR]

private lemma l4d_ham_le_hamMax (w : Fin 3 → ℂ) {v : ℂ} (hv : v ∈ VT) : ham w v ≤ hamMax w := by
  unfold hamMax
  rcases l4d_mem_VT.1 hv with rfl | rfl | rfl
  · exact le_max_left _ _
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

private lemma l4d_hamMax_eq_of_max {w : Fin 3 → ℂ} {v : ℂ}
    (hmax : ∀ x ∈ VT, ham w x ≤ ham w v) (hv : v ∈ VT) : hamMax w = ham w v :=
  le_antisymm (max_le (hmax 1 l4d_one_mem_VT) (max_le (hmax ζ l4d_ζ_mem_VT)
    (hmax _ l4d_ζ_sq_mem_VT))) (l4d_ham_le_hamMax w hv)

/-- **The Hamiltonian is constant along extremals** (TeX 10741–10742). Along a trajectory of the
Fuller system with controls in `V_T` satisfying the maximum condition (13.2.5), the maximized
Hamiltonian `H_F⁺(z(t))` is constant, and `H_F(z(t), u(t)) = H_F⁺(z(t₁))` for almost every `t`.

Proof: `H_F⁺(z(t)) = RR(z₁, z₂ i) + max_{v ∈ V_T} RR(v, z₃(t))` is absolutely continuous (`z₁` is
Lipschitz, `z₂`, `z₃` are `C¹`, and a maximum of absolutely continuous functions is absolutely
continuous). At almost every `t` it is differentiable, the maximum condition holds and `z₁' = -iu`
(Lebesgue's differentiation theorem); there the derivative of the maximum is `RR(u(t), z₂)`: the
function `H_F⁺(z(·)) - H_F(z(·), u(t))` is `≥ 0` and vanishes at `t`, so its derivative there is
`0` (a maximum of differentiable functions has, where it is differentiable, the derivative of each
active function). The derivative of `RR(z₁, z₂ i)` is `RR(-iu, i z₂) + RR(z₁, i z₁) = -RR(u, z₂)`.
The derivative vanishes almost everywhere, so the absolutely continuous function is constant. -/
theorem l4st_hamMax_eq_of_maxCondition {t₁ t₂ : ℝ} {z : ℝ → Fin 3 → ℂ} {u : ℝ → ℂ}
    (h : IsTrajectory VT t₁ t₂ z u) (hmax : MaxCondition VT t₁ t₂ z u) :
    (∀ t ∈ Icc t₁ t₂, hamMax (z t) = hamMax (z t₁)) ∧
      ∀ᵐ t, t ∈ Icc t₁ t₂ → ham (z t) (u t) = hamMax (z t₁) := by
  have hle := h.1.le
  have hU := l4d_VT_subset_UT
  have hI : t₁ ∈ Icc t₁ t₂ := ⟨le_rfl, hle⟩
  have hII : t₂ ∈ Icc t₁ t₂ := ⟨hle, le_rfl⟩
  have hac := l4d_ac_hamMax h
  have hc0 := l4d_continuousOn_traj hU h 0
  have hc1 := l4d_continuousOn_traj hU h 1
  have hd0 : ∀ᵐ t, t ∈ Ioo t₁ t₂ → HasDerivAt (fun s ↦ z s 0) (-I * u t) t :=
    l4d_ae_hasDerivAt_of_eq_primitive (g := fun s ↦ -I * u s)
      ((l4d_intervalIntegrable_control hU h hI hII).const_mul _) fun t ht ↦ (h.2.2.2 t ht).1
  have hd1 : ∀ t ∈ Ioo t₁ t₂, HasDerivAt (fun s ↦ z s 1) (z t 0) t := fun t ht ↦
    l4d_hasDerivAt_of_eq_primitive (g := fun s ↦ z s 0) hc0 (fun t ht ↦ (h.2.2.2 t ht).2.1) ht
  have hd2 : ∀ t ∈ Ioo t₁ t₂, HasDerivAt (fun s ↦ z s 2) (z t 1) t := fun t ht ↦
    l4d_hasDerivAt_of_eq_primitive (g := fun s ↦ z s 1) hc1 (fun t ht ↦ (h.2.2.2 t ht).2.2) ht
  have hzero : ∀ᵐ t, t ∈ uIcc t₁ t₂ → HasDerivAt (fun s ↦ hamMax (z s)) 0 t := by
    filter_upwards [hd0, hac.ae_differentiableAt, hmax, l4d_ae_ne t₁, l4d_ae_ne t₂]
      with t h0t hdt hmt hne1 hne2 ht
    have htI : t ∈ Icc t₁ t₂ := by rwa [uIcc_of_le hle] at ht
    have htI' : t ∈ Ioo t₁ t₂ :=
      ⟨lt_of_le_of_ne htI.1 (Ne.symm hne1), lt_of_le_of_ne htI.2 hne2⟩
    have hv₀ : u t ∈ VT := h.2.2.1 t htI
    -- `F(s) = RR(z₁(s), z₂(s) i)`
    have hF : HasDerivAt (fun s ↦ RR (z s 0) (z s 1 * I)) (-RR (u t) (z t 1)) t := by
      have := l4d_hasDerivAt_RR (h0t htI') ((hd1 t htI').mul_const I)
      convert this using 1
      simp only [l4d_RR_eq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
        Complex.I_re, Complex.I_im]
      ring
    -- `φ(s) = RR(u(t), z₃(s))`
    have hφ : HasDerivAt (fun s ↦ RR (u t) (z s 2)) (RR (u t) (z t 1)) t := by
      have := l4d_hasDerivAt_RR (hasDerivAt_const t (u t)) (hd2 t htI')
      convert this using 1
      simp [l4d_RR_eq]
    have hG := ((hdt ht).hasDerivAt.sub hF).sub hφ
    have hmin : IsLocalMin
        (fun s ↦ hamMax (z s) - RR (z s 0) (z s 1 * I) - RR (u t) (z s 2)) t := by
      refine Filter.Eventually.of_forall fun s ↦ ?_
      have h1 : hamMax (z t) = ham (z t) (u t) :=
        l4d_hamMax_eq_of_max (fun w hw ↦ hmt htI w hw) hv₀
      have h2 : ham (z s) (u t) ≤ hamMax (z s) := l4d_ham_le_hamMax (z s) hv₀
      simp only [ham] at h1 h2
      dsimp only
      linarith
    have hD : deriv (fun s ↦ hamMax (z s)) t = 0 := by
      have := hmin.hasDerivAt_eq_zero hG
      linarith
    rw [← hD]
    exact (hdt ht).hasDerivAt
  obtain ⟨C, hC⟩ := hac.const_of_ae_hasDerivAt_zero hzero
  have hconst : ∀ t ∈ Icc t₁ t₂, hamMax (z t) = hamMax (z t₁) := fun t ht ↦ by
    rw [hC t (by rwa [uIcc_of_le hle]), hC t₁ (by rw [uIcc_of_le hle]; exact hI)]
  refine ⟨hconst, ?_⟩
  filter_upwards [hmax] with t hmt ht
  rw [← hconst t ht, l4d_hamMax_eq_of_max (fun w hw ↦ hmt ht w hw) (h.2.2.1 t ht)]

/-! ### Helpers: local uniqueness of extremals -/

/-- `|RR(x, y)| ≤ |x||y|`. -/
private lemma l4d_abs_RR_le (x y : ℂ) : |RR x y| ≤ ‖x‖ * ‖y‖ := by
  rw [RR]
  calc |(starRingEnd ℂ x * y).re| ≤ ‖starRingEnd ℂ x * y‖ := Complex.abs_re_le_norm _
    _ = ‖x‖ * ‖y‖ := by rw [norm_mul, Complex.norm_conj]

/-- The control vectors seen through `RR`. -/
private lemma l4d_controlVector_sub (p : Fin 3 → ℂ) (v w : ℂ) :
    (controlVector p v - controlVector p w) 0 = RR (v - w) (p 2) ∧
      (controlVector p v - controlVector p w) 1 = RR (v - w) (p 1) ∧
      (controlVector p v - controlVector p w) 2 = RR (v - w) (p 0) := by
  simp only [controlVector, Pi.sub_apply, l4d_RR_eq, Complex.sub_re, Complex.sub_im]
  refine ⟨?_, ?_, ?_⟩ <;> simp <;> ring

/-- The lexicographic order is total: a nonzero vector or its opposite is positive. -/
private lemma l4d_lexPos_or {x : Fin 3 → ℝ} (hx : x ≠ 0) : LexPos x ∨ LexPos (-x) := by
  have key : ∀ y : Fin 3 → ℝ,
      (0 < y 0 ∨ (y 0 = 0 ∧ 0 < y 1) ∨ (y 0 = 0 ∧ y 1 = 0 ∧ 0 < y 2)) → LexPos y := by
    intro y hy
    rcases hy with h0 | ⟨h0, h1⟩ | ⟨h0, h1, h2⟩
    · exact ⟨0, fun j hj ↦ absurd hj (Fin.not_lt_zero j), h0⟩
    · exact ⟨1, fun j hj ↦ by fin_cases j <;> simp_all, h1⟩
    · exact ⟨2, fun j hj ↦ by fin_cases j <;> simp_all, h2⟩
  rcases lt_trichotomy (x 0) 0 with h0 | h0 | h0
  · exact Or.inr (key _ (Or.inl (by simp only [Pi.neg_apply]; linarith)))
  · rcases lt_trichotomy (x 1) 0 with h1 | h1 | h1
    · exact Or.inr (key _ (Or.inr (Or.inl ⟨by simp [h0], by simp only [Pi.neg_apply]; linarith⟩)))
    · rcases lt_trichotomy (x 2) 0 with h2 | h2 | h2
      · exact Or.inr (key _ (Or.inr (Or.inr ⟨by simp [h0], by simp [h1],
          by simp only [Pi.neg_apply]; linarith⟩)))
      · exact absurd (by ext j; fin_cases j <;> simp [h0, h1, h2]) hx
      · exact Or.inl (key _ (Or.inr (Or.inr ⟨h0, h1, h2⟩)))
    · exact Or.inl (key _ (Or.inr (Or.inl ⟨h0, h1⟩)))
  · exact Or.inl (key _ (Or.inl h0))

/-- Three distinct vertices exhaust `V_T`. -/
private lemma l4d_VT_cases {a b c y : ℂ} (ha : a ∈ VT) (hb : b ∈ VT) (hc : c ∈ VT) (hy : y ∈ VT)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : y = a ∨ y = b ∨ y = c := by
  rcases l4d_mem_VT.1 ha with rfl | rfl | rfl <;> rcases l4d_mem_VT.1 hb with rfl | rfl | rfl <;>
    rcases l4d_mem_VT.1 hc with rfl | rfl | rfl <;> rcases l4d_mem_VT.1 hy with rfl | rfl | rfl <;>
    simp_all

/-- **Local uniqueness** (proof of Lemma 13.2.6, TeX 10978–10995): an extremal from `z(a) ≠ 0`
uses the first control of `z(a)` almost everywhere on some `[a, a + ε]`.

By (13.3.1)–(13.3.2), `RR(d, z₃(t)) = RR(d, z₃⁰) + RR(d, z₂⁰)(t - a) + RR(d, z₁⁰)(t - a)²/2 +
RR(u₃(t), i d)` with `|u₃(t)| ≤ (t - a)³/6`. A control `v` with `v(z⁰, v) ≺ v(z⁰, u₀)` is beaten by
`u₀` for small `t > a` (the first nonzero coefficient is positive, `l4c_cubic_pos`). If a control
`v ≠ u₀` ties with `u₀`, the third control is beaten, so `u ∈ {u₀, v}` a.e. near `a`, and
`RR(u₀ - v, z₃(t)) = RR(u₃(t), i(u₀ - v)) = κ(t - a)³/6` with `κ = RR(u₀ - v, -iu₀) =
RR(u₀ - v, -iv) > 0` (the computation of Lemma 13.2.6: `κ ≥ 0` because `u₀` is the first control,
and `κ = ±√3/2 ≠ 0`); so `v` is beaten too. -/
private lemma l4d_local_unique {a b : ℝ} {z : ℝ → Fin 3 → ℂ} {u : ℝ → ℂ}
    (h : IsTrajectory VT a b z u) (hmax : MaxCondition VT a b z u) (hp : z a ≠ 0) :
    ∃ ε > 0, ∀ᵐ t, t ∈ Ioo a (a + ε) → t ≤ b → u t = firstControl (z a) := by
  set u₀ := firstControl (z a) with hu₀def
  have hfc : IsFirstControl (z a) u₀ := l4st_isFirstControl_firstControl hp
  have hu₀ : u₀ ∈ VT := hfc.1
  have hlex : u₀ ∈ lexMaxControls (z a) := l4st_firstControl_mem_lexMaxControls hp
  have hVT : lexMaxControls (z a) ≠ VT := (lemma13_2_6 hp).2.2
  have hb := l4d_norm_le_one_of_traj l4d_VT_subset_UT h
  have hI : a ∈ Icc a b := ⟨le_rfl, h.1.le⟩
  -- (13.3.2) seen through `RR(d, ·)`
  have hRRz : ∀ d : ℂ, ∀ t ∈ Icc a b, RR d (z t 2) = RR d (z a 2) + RR d (z a 1) * (t - a) +
      RR d (z a 0) / 2 * (t - a) ^ 2 + RR (u3 a u t) (I * d) := by
    intro d t ht
    have e : z t 2 = -I * u3 a u t + (((t - a) ^ 2 / 2 : ℝ) : ℂ) * z a 0 +
        ((t - a : ℝ) : ℂ) * z a 1 + z a 2 := by
      rw [eqn_z3u3 l4d_VT_subset_UT h t ht]; push_cast; ring
    rw [e]
    simp only [l4d_RR_eq, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  have hRRsub : ∀ v w x : ℂ, RR v x - RR w x = RR (v - w) x := fun v w x ↦ by
    simp only [l4d_RR_eq, Complex.sub_re, Complex.sub_im]; ring
  have hmaxt : ∀ᵐ t, t ∈ Icc a b → ∀ v ∈ VT, RR v (z t 2) ≤ RR (u t) (z t 2) := by
    filter_upwards [hmax] with t ht htI v hv
    have := ht htI v hv
    simp only [ham, add_le_add_iff_left] at this
    exact this
  -- (i) a control strictly below `u₀` in the lexicographic order is beaten near `a`
  have hbeat : ∀ v ∈ VT, controlVector (z a) v ≠ controlVector (z a) u₀ →
      ∀ᶠ t in 𝓝[>] a, t ≤ b → RR v (z t 2) < RR u₀ (z t 2) := by
    intro v hv hcv
    have hlt : LexPos (controlVector (z a) u₀ - controlVector (z a) v) := by
      rcases l4d_lexPos_or (sub_ne_zero.2 (Ne.symm hcv)) with h' | h'
      · exact h'
      · rw [neg_sub] at h'
        exact absurd h' (hlex.2 v hv)
    obtain ⟨e0, e1, e2⟩ := l4d_controlVector_sub (z a) u₀ v
    obtain ⟨ε, hε, hpos⟩ := l4c_cubic_pos (a := RR (u₀ - v) (z a 2)) (b := RR (u₀ - v) (z a 1))
      (c := RR (u₀ - v) (z a 0) / 2) (d := -1 / 3) (by
        obtain ⟨k, hk, hk'⟩ := hlt
        fin_cases k
        · left; rw [← e0]; exact hk'
        · right; left
          exact ⟨by rw [← e0]; exact hk 0 (by decide), by rw [← e1]; exact hk'⟩
        · right; right; left
          refine ⟨by rw [← e0]; exact hk 0 (by decide), by rw [← e1]; exact hk 1 (by decide), ?_⟩
          have : 0 < RR (u₀ - v) (z a 0) := by rw [← e2]; exact hk'
          linarith)
    filter_upwards [Ioo_mem_nhdsGT (show a < a + ε by linarith)] with t ht htb
    have htI : t ∈ Icc a b := ⟨ht.1.le, htb⟩
    have hP := hpos (t - a) ⟨sub_pos.2 ht.1, by linarith [ht.2]⟩
    have hR := hRRz (u₀ - v) t htI
    have herr : -((t - a) ^ 3 / 3) ≤ RR (u3 a u t) (I * (u₀ - v)) := by
      have h1 := l4d_abs_RR_le (u3 a u t) (I * (u₀ - v))
      have h2 : ‖I * (u₀ - v)‖ ≤ 2 := by
        rw [norm_mul, Complex.norm_I, one_mul]
        calc ‖u₀ - v‖ ≤ ‖u₀‖ + ‖v‖ := norm_sub_le _ _
          _ = 2 := by rw [l4d_norm_VT hu₀, l4d_norm_VT hv]; norm_num
      have h3 := (eqn_u3 h.2.1 hb t htI).2
      have h4 : 0 ≤ (t - a) ^ 3 / 6 := by have := (sub_pos.2 ht.1).le; positivity
      have h5 : ‖u3 a u t‖ * ‖I * (u₀ - v)‖ ≤ (t - a) ^ 3 / 6 * 2 :=
        mul_le_mul h3 h2 (norm_nonneg _) h4
      have := neg_abs_le (RR (u3 a u t) (I * (u₀ - v)))
      linarith
    have := hRRsub u₀ v (z t 2)
    linarith
  -- every control `x ≠ u₀` is beaten near `a`
  have hall : ∀ᶠ t in 𝓝[>] a, ∀ x ∈ VT, x ≠ u₀ → t ≤ b → RR x (z t 2) < RR u₀ (z t 2) := by
    by_cases htie : ∃ v ∈ VT, v ≠ u₀ ∧ controlVector (z a) v = controlVector (z a) u₀
    · obtain ⟨v, hv, hvu, hcv⟩ := htie
      -- the third control is not tied (Lemma 13.2.6: `V_{T,max} ≠ V_T`)
      have hother : ∀ x ∈ VT, x ≠ u₀ → x ≠ v →
          controlVector (z a) x ≠ controlVector (z a) u₀ := by
        intro x hx hxu hxv hcx
        apply hVT
        refine Set.Subset.antisymm (fun y hy ↦ hy.1) fun y hy ↦ ⟨hy, ?_⟩
        have hcy : controlVector (z a) y = controlVector (z a) u₀ := by
          rcases l4d_VT_cases hu₀ hv hx hy (Ne.symm hvu) (Ne.symm hxu) (Ne.symm hxv) with
            rfl | rfl | rfl
          · rfl
          · exact hcv
          · exact hcx
        rw [hcy]
        exact hlex.2
      have hev : ∀ᶠ t in 𝓝[>] a, ∀ x ∈ VT, x ≠ u₀ → x ≠ v → t ≤ b →
          RR x (z t 2) < RR u₀ (z t 2) := by
        refine (Filter.eventually_all_finite l4d_VT_finite).2 fun x hx ↦ ?_
        by_cases hxu : x = u₀
        · exact Filter.Eventually.of_forall fun t h1 ↦ absurd hxu h1
        by_cases hxv : x = v
        · exact Filter.Eventually.of_forall fun t _ h2 ↦ absurd hxv h2
        filter_upwards [hbeat x hx (hother x hx hxu hxv)] with t ht _ _ htb using ht htb
      -- near `a`, the control is `u₀` or `v` almost everywhere
      obtain ⟨c, hc, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
      have hae : ∀ᵐ s, s ∈ Ioo a c → s ≤ b → u s = u₀ ∨ u s = v := by
        filter_upwards [hmaxt] with s hms hs hsb
        have hsI : s ∈ Icc a b := ⟨hs.1.le, hsb⟩
        by_contra hcon
        push Not at hcon
        have h1 := hsub hs (u s) (h.2.2.1 s hsI) hcon.1 hcon.2 hsb
        have h2 := hms hsI u₀ hu₀
        linarith
      -- `κ = RR(u₀ - v, -iu₀) > 0`
      obtain ⟨e0, e1, e2⟩ := l4d_controlVector_sub (z a) u₀ v
      rw [hcv, sub_self, Pi.zero_apply] at e0 e1 e2
      have hκ : 0 < RR (u₀ - v) (-I * u₀) := by
        obtain ⟨-, ε', hε', hε'max⟩ := hfc
        have h1 := hε'max ε' ⟨hε'.le, le_rfl⟩ v hv
        have h2 := l4c_ham_flow_sub ε' (z a) u₀ u₀ v
        rw [← e0, ← e1, ← e2] at h2
        have h3 : 0 ≤ RR (u₀ - v) (-I * u₀) * ε' ^ 3 := by nlinarith
        have h4 : 0 ≤ RR (u₀ - v) (-I * u₀) :=
          nonneg_of_mul_nonneg_left h3 (by positivity)
        exact lt_of_le_of_ne h4 (Ne.symm (l4d_RR_sub_neg_I_mul_ne_zero hu₀ hv (Ne.symm hvu)))
      have hκv : ∀ w, w = u₀ ∨ w = v → RR w (I * (u₀ - v)) = RR (u₀ - v) (-I * u₀) := by
        rintro w (rfl | rfl) <;>
          simp only [l4d_RR_eq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
            Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im] <;> ring
      -- so `v` is beaten near `a`
      have hbv : ∀ᶠ t in 𝓝[>] a, t ≤ b → RR v (z t 2) < RR u₀ (z t 2) := by
        filter_upwards [Ioo_mem_nhdsGT hc] with t ht htb
        have htI : t ∈ Icc a b := ⟨ht.1.le, htb⟩
        have hR := hRRz (u₀ - v) t htI
        rw [← e0, ← e1, ← e2] at hR
        have hU : RR (u3 a u t) (I * (u₀ - v)) = RR (u₀ - v) (-I * u₀) * (t - a) ^ 3 / 6 := by
          rw [l4d_RR_u3 (l4d_intervalIntegrable_control l4d_VT_subset_UT h hI htI),
            intervalIntegral.integral_congr_ae
              (g := fun s ↦ RR (u₀ - v) (-I * u₀) * (t - s) ^ 2) ?_,
            intervalIntegral.integral_const_mul, l4d_integral_sq_sub]
          · ring
          · filter_upwards [hae] with s hs hsI
            rw [uIoc_of_le htI.1] at hsI
            rw [hκv (u s) (hs ⟨hsI.1, hsI.2.trans_lt ht.2⟩ (hsI.2.trans htb))]
        have := hRRsub u₀ v (z t 2)
        have : 0 < (t - a) ^ 3 := pow_pos (sub_pos.2 ht.1) 3
        nlinarith
      filter_upwards [hev, hbv] with t h1 h2 x hx hxu htb
      by_cases hxv : x = v
      · rw [hxv]; exact h2 htb
      · exact h1 x hx hxu hxv htb
    · push Not at htie
      refine (Filter.eventually_all_finite l4d_VT_finite).2 fun x hx ↦ ?_
      by_cases hxu : x = u₀
      · exact Filter.Eventually.of_forall fun t h1 ↦ absurd hxu h1
      · filter_upwards [hbeat x hx (htie x hx hxu)] with t ht _ htb using ht htb
  obtain ⟨c, hc, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hall
  refine ⟨c - a, sub_pos.2 hc, ?_⟩
  filter_upwards [hmaxt] with t hmt ht htb
  have htI : t ∈ Icc a b := ⟨ht.1.le, htb⟩
  by_contra hne
  have h1 := hsub (show t ∈ Ioo a c by simpa using ht) (u t) (h.2.2.1 t htI) hne htb
  have h2 := hmt htI u₀ hu₀
  linarith

/-- **Extremals follow the first control up to the first switching time** (proof of Lemma 13.2.6,
TeX 10978–10995). Let `z⁰ ≠ 0` and let `(z, u)` be a trajectory of the Fuller system on `[0, T]`
with controls in `V_T`, satisfying the maximum condition (13.2.5), with `z(0) = z⁰` and
`T ≤ t_sw(z⁰)`. Then `u` is the first control of `z⁰` almost everywhere on `[0, T]`, and `z` is the
constant-control solution `t ↦ z(t, z⁰, firstControl z⁰)`.

Proof: (local uniqueness, `l4d_local_unique`) near `t = 0`, `z₃(t) = Q(t) - i u₃(t)` with
`Q(t) = z₃⁰ + z₂⁰ t + z₁⁰ t²/2` and `|u₃(t)| ≤ t³/6` ((13.3.1)–(13.3.2)). A control `v`
outside `V_{T,max}` is beaten by a lower-order term of `Q` for small `t > 0`; if
`V_{T,max} = {ζ^i, ζ^{i+1}}`, the controls `ζ^i, ζ^{i+1}` tie in `Q` and, as `u` takes values in
`{ζ^i, ζ^{i+1}}` there, `RR(ζ^{i+1} - ζ^i, -i u₃(t)) = -(√3/2) t³/6 < 0` (the computation of
Lemma 13.2.6, valid for every control in the edge), so `u = ζ^i` almost everywhere near `0`.
(Continuation) Let `S` be the supremum of the `s ≤ T` such that `u` is the first control almost
everywhere on `[0, s]` (a countable union of null sets is null, so `S` is such an `s`); if
`S < T`, then `z(S) = z(S, z⁰, u₀) ≠ 0` by `l4f_flow_firstControl_ne_zero` (`S ≤ T ≤ t_sw`;
Lemma 13.3.1 does not apply, as `z₃⁰` need not lie on a wall) and the first control of `z(S)` is
still `u₀` (it is optimal on `[S, t_sw]`), so local uniqueness at `z(S)` contradicts the choice of
`S`. -/
theorem l4st_eq_flow_of_maxCondition {z₀ : Fin 3 → ℂ} (hz₀ : z₀ ≠ 0) {T : ℝ}
    (hT : T ≤ firstSwitchTime z₀) {z : ℝ → Fin 3 → ℂ} {u : ℝ → ℂ} (h : IsTrajectory VT 0 T z u)
    (hmax : MaxCondition VT 0 T z u) (h0 : z 0 = z₀) :
    (∀ t ∈ Icc 0 T, z t = flow t z₀ (firstControl z₀)) ∧
      ∀ᵐ t, t ∈ Icc 0 T → u t = firstControl z₀ := by
  set u₀ := firstControl z₀ with hu₀def
  have hu₀ : u₀ ∈ VT := (l4st_isFirstControl_firstControl hz₀).1
  have hT0 : 0 < T := h.1
  -- the times up to which `u = u₀` almost everywhere
  set A : Set ℝ := {s | 0 ≤ s ∧ s ≤ T ∧ ∀ᵐ t, t ∈ Icc 0 s → u t = u₀} with hA
  have hA0 : (0 : ℝ) ∈ A := by
    refine ⟨le_rfl, hT0.le, ?_⟩
    filter_upwards [l4d_ae_ne 0] with t ht htI
    exact absurd (le_antisymm htI.2 htI.1) ht
  have hAbdd : BddAbove A := ⟨T, fun s hs ↦ hs.2.1⟩
  set S := sSup A with hSdef
  have hS0 : 0 ≤ S := le_csSup hAbdd hA0
  have hST : S ≤ T := csSup_le ⟨0, hA0⟩ fun s hs ↦ hs.2.1
  -- `S` is such a time
  have hSA : ∀ᵐ t, t ∈ Icc 0 S → u t = u₀ := by
    rcases hS0.eq_or_lt with hS | hS
    · rw [← hS]; exact hA0.2.2
    have hseq : ∀ n : ℕ, ∃ s ∈ A, S - 1 / (n + 1) < s := by
      intro n
      have : (0 : ℝ) < 1 / (n + 1) := by positivity
      exact exists_lt_of_lt_csSup ⟨0, hA0⟩ (by linarith)
    choose s hsA hslt using hseq
    have hall : ∀ᵐ t, ∀ n, t ∈ Icc 0 (s n) → u t = u₀ := ae_all_iff.2 fun n ↦ (hsA n).2.2
    filter_upwards [hall, l4d_ae_ne S] with t ht htS htI
    have htlt : t < S := lt_of_le_of_ne htI.2 htS
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 htlt)
    exact ht n ⟨htI.1, by linarith [hslt n]⟩
  -- `S = T`
  have hSeq : S = T := by
    by_contra hne
    have hSlt : S < T := lt_of_le_of_ne hST hne
    have hzS : z S = flow S z₀ u₀ := by
      rcases hS0.eq_or_lt with hS | hS
      · rw [← hS, h0, l4st_flow_zero]
      · have h' := l4d_isTrajectory_mono l4d_VT_subset_UT h le_rfl hS hST
        rw [l4d_eq_flow_of_ae_eq h' hu₀ hSA S ⟨hS0, le_rfl⟩, h0, sub_zero]
    have hSsw : S ∈ Icc 0 (firstSwitchTime z₀) := ⟨hS0, hST.trans hT⟩
    have hpS : z S ≠ 0 := by rw [hzS]; exact l4f_flow_firstControl_ne_zero hz₀ hSsw
    have hfcS : firstControl (z S) = u₀ := by
      rw [l4st_firstControl_eq_iff hpS]
      refine ⟨hu₀, firstSwitchTime z₀ - S, by linarith, fun t ht v hv ↦ ?_⟩
      rw [hzS, ← l4st_flow_add]
      exact l4st_firstControl_maximizes hz₀ (S + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩ v hv
    obtain ⟨ε, hε, hloc⟩ := l4d_local_unique
      (l4d_isTrajectory_mono l4d_VT_subset_UT h hS0 hSlt le_rfl)
      (l4d_maxCondition_mono hmax hS0 le_rfl) hpS
    have hcA : min T (S + ε / 2) ∈ A := by
      refine ⟨le_min hT0.le (by linarith), min_le_left _ _, ?_⟩
      filter_upwards [hSA, hloc] with t h1 h2 htI
      by_cases htS : t ≤ S
      · exact h1 ⟨htI.1, htS⟩
      · push Not at htS
        rw [← hfcS]
        exact h2 ⟨htS, by linarith [min_le_right T (S + ε / 2), htI.2]⟩
          (htI.2.trans (min_le_left _ _))
    have h1 : min T (S + ε / 2) ≤ S := le_csSup hAbdd hcA
    have h2 : S < min T (S + ε / 2) := lt_min hSlt (by linarith)
    linarith
  have hTA : ∀ᵐ t, t ∈ Icc 0 T → u t = u₀ := hSeq ▸ hSA
  refine ⟨fun t ht ↦ ?_, hTA⟩
  rw [l4d_eq_flow_of_ae_eq h hu₀ hTA t ht, h0, sub_zero]

end TriFuller

end SmoothedPolygons
