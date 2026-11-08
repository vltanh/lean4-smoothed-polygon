module

public import SmoothedPolygons.Ch13.FirstControl
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Chapter 13: the singular locus of the Fuller system

§13.3 of Hales–Vajjha, *Packings of Smoothed Polygons* (TeX 11070–11157). The singular locus is
the origin of `ℂ³` (TeX 11072).

* Lemma 13.3.1 (`lem:nonzero`): a trajectory with constant control starting on a wall, away from
  `0`, never reaches `0`;
* equations (13.3.1) (`eqn:u3`) and (13.3.2) (`eqn:z3u3`): the triple integral `u₃` of the
  control and the formula `z₃ = -iu₃ + z₁⁰t²/2 + z₂⁰t + z₃⁰`;
* Lemma 13.3.2 (`lemma:no-singular`): the only singular arc is `z ≡ 0`, `u = 0` almost everywhere.

The file also proves the facts about trajectories with measurable controls that these results and
`SmoothedPolygons/Ch13/Extremals.lean` use (names prefixed `l4d_`): the values of `RR` on the
vertices `V_T`, the half-planes containing `U_T`, the maximizers of `RR(·, w)` on `U_T`, the
integrability, continuity and restriction of trajectories, the derivative of a primitive, and
Fubini's theorem on a triangle (Cauchy's formula for repeated integration).
-/

@[expose] public section

namespace SmoothedPolygons

open Complex MeasureTheory Set TriFuller

namespace TriFuller

/-! ### Helpers: the form `RR` and the vertices `V_T` -/

/-- `RR(a, b) = Re a Re b + Im a Im b`. -/
theorem l4d_RR_eq (a b : ℂ) : RR a b = a.re * b.re + a.im * b.im := by
  simp only [RR, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- `RR` is symmetric. -/
theorem l4d_RR_comm (a b : ℂ) : RR a b = RR b a := by
  rw [l4d_RR_eq, l4d_RR_eq]; ring

/-- `RR` is additive in its first argument. -/
theorem l4d_RR_add_left (a b c : ℂ) : RR (a + b) c = RR a c + RR b c := by
  simp only [l4d_RR_eq, Complex.add_re, Complex.add_im]; ring

/-- `RR` is `ℝ`-homogeneous in its first argument. -/
theorem l4d_RR_ofReal_mul_left (r : ℝ) (a c : ℂ) : RR (r * a) c = r * RR a c := by
  simp only [l4d_RR_eq, Complex.re_ofReal_mul, Complex.im_ofReal_mul]; ring

/-- `RR` is `ℝ`-homogeneous in its second argument. -/
theorem l4d_RR_ofReal_mul_right (r : ℝ) (a c : ℂ) : RR a (r * c) = r * RR a c := by
  simp only [l4d_RR_eq, Complex.re_ofReal_mul, Complex.im_ofReal_mul]; ring

/-- `√3 · √3 = 3`. -/
theorem l4d_sqrt3_mul_self : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)

theorem l4d_ζ_re : ζ.re = -1 / 2 := by rw [l4st_ζ_eq]

theorem l4d_ζ_im : ζ.im = √3 / 2 := by rw [l4st_ζ_eq]

theorem l4d_ζ_sq_re : (ζ ^ 2).re = -1 / 2 := by
  rw [pow_two, Complex.mul_re, l4d_ζ_re, l4d_ζ_im]; nlinarith [l4d_sqrt3_mul_self]

theorem l4d_ζ_sq_im : (ζ ^ 2).im = -(√3 / 2) := by
  rw [pow_two, Complex.mul_im, l4d_ζ_re, l4d_ζ_im]; ring

theorem l4d_mem_VT {v : ℂ} : v ∈ VT ↔ v = 1 ∨ v = ζ ∨ v = ζ ^ 2 := by
  simp only [VT, Set.mem_insert_iff, Set.mem_singleton_iff]

theorem l4d_one_mem_VT : (1 : ℂ) ∈ VT := l4d_mem_VT.2 (Or.inl rfl)

theorem l4d_ζ_mem_VT : ζ ∈ VT := l4d_mem_VT.2 (Or.inr (Or.inl rfl))

theorem l4d_ζ_sq_mem_VT : ζ ^ 2 ∈ VT := l4d_mem_VT.2 (Or.inr (Or.inr rfl))

theorem l4d_VT_subset_UT : VT ⊆ UT := subset_convexHull ℝ VT

theorem l4d_VT_finite : VT.Finite := ((Set.finite_singleton _).insert _).insert _

theorem l4d_norm_VT {v : ℂ} (hv : v ∈ VT) : ‖v‖ = 1 := (l4st_VT_props hv hv).1

/-- `RR(v, v) = 1` for `v ∈ V_T`. -/
theorem l4d_RR_self_VT {v : ℂ} (hv : v ∈ VT) : RR v v = 1 := by
  rcases l4d_mem_VT.1 hv with rfl | rfl | rfl <;>
    simp only [l4d_RR_eq, Complex.one_re, Complex.one_im, l4d_ζ_re, l4d_ζ_im, l4d_ζ_sq_re,
      l4d_ζ_sq_im] <;> nlinarith [l4d_sqrt3_mul_self]

/-- `RR(v, w) = -1/2` for distinct `v, w ∈ V_T`. -/
theorem l4d_RR_ne_VT {v w : ℂ} (hv : v ∈ VT) (hw : w ∈ VT) (hne : v ≠ w) :
    RR v w = -1 / 2 := by
  rcases l4d_mem_VT.1 hv with rfl | rfl | rfl <;> rcases l4d_mem_VT.1 hw with rfl | rfl | rfl <;>
    first
    | exact absurd rfl hne
    | simp only [l4d_RR_eq, Complex.one_re, Complex.one_im, l4d_ζ_re, l4d_ζ_im, l4d_ζ_sq_re,
        l4d_ζ_sq_im]; nlinarith [l4d_sqrt3_mul_self]

/-- Every vertex of `U_T` has another vertex. -/
theorem l4d_exists_ne_VT (c : ℂ) : ∃ v ∈ VT, v ≠ c := by
  by_cases h : c = 1
  · refine ⟨ζ, l4d_ζ_mem_VT, fun h' ↦ ?_⟩
    have := congrArg Complex.re (h'.trans h)
    rw [l4d_ζ_re, Complex.one_re] at this
    norm_num at this
  · exact ⟨1, l4d_one_mem_VT, Ne.symm h⟩

/-- For distinct `v, w ∈ V_T`, `RR(v - w, -iv) = ±√3/2 ≠ 0`. -/
theorem l4d_RR_sub_neg_I_mul_ne_zero {v w : ℂ} (hv : v ∈ VT) (hw : w ∈ VT) (hne : v ≠ w) :
    RR (v - w) (-I * v) ≠ 0 := by
  have h3 : 0 < √3 := by positivity
  rcases l4d_mem_VT.1 hv with rfl | rfl | rfl <;> rcases l4d_mem_VT.1 hw with rfl | rfl | rfl <;>
    first
    | exact absurd rfl hne
    | simp only [l4d_RR_eq, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im, Complex.one_re,
        Complex.one_im, l4d_ζ_re, l4d_ζ_im, l4d_ζ_sq_re, l4d_ζ_sq_im]
      intro h; nlinarith [l4d_sqrt3_mul_self]

/-- `RR(·, w)` is `ℝ`-linear. -/
theorem l4d_isLinearMap_RR (w : ℂ) : IsLinearMap ℝ (fun v : ℂ ↦ RR v w) :=
  IsLinearMap.mk (fun x y ↦ l4d_RR_add_left x y w)
    (fun c x ↦ by simp only [l4d_RR_eq, Complex.smul_re, Complex.smul_im, smul_eq_mul]; ring)

/-- `RR(·, w) - α RR(·, m)` is `ℝ`-linear. -/
theorem l4d_isLinearMap_RR_sub (w m : ℂ) (α : ℝ) :
    IsLinearMap ℝ (fun v : ℂ ↦ RR v w - α * RR v m) :=
  IsLinearMap.mk (fun x y ↦ by simp only [l4d_RR_add_left]; ring)
    (fun c x ↦ by simp only [l4d_RR_eq, Complex.smul_re, Complex.smul_im, smul_eq_mul]; ring)

/-- A nonzero real multiple of `i u`, `u ∈ V_T`, is not on a wall: the walls are the real
multiples of the vertices, and no vertex is a real multiple of `i` times a vertex. -/
theorem l4d_I_mul_not_mem_walls {c : ℝ} (hc : c ≠ 0) {u : ℂ} (hu : u ∈ VT) :
    I * (c : ℂ) * u ∉ walls := by
  rintro ((⟨s, -, hs⟩ | ⟨s, -, hs⟩) | ⟨s, -, hs⟩) <;>
  · have hre := congrArg Complex.re hs
    have him := congrArg Complex.im hs
    apply hc
    rcases l4d_mem_VT.1 hu with rfl | rfl | rfl <;>
      simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.one_re, Complex.one_im, pow_zero, pow_one, l4d_ζ_re, l4d_ζ_im,
        l4d_ζ_sq_re, l4d_ζ_sq_im] at hre him <;>
      nlinarith [l4d_sqrt3_mul_self, Real.sqrt_nonneg 3]

/-- A nonzero point of a wall has `RR(w, c) < 0` for the vertex `c` of its ray. -/
theorem l4d_exists_RR_neg_of_mem_walls {w : ℂ} (hw : w ∈ walls) (hne : w ≠ 0) :
    ∃ c ∈ VT, RR w c < 0 := by
  have key : ∀ k : ℕ, ζ ^ k ∈ VT → w ∈ wall k → ∃ c ∈ VT, RR w c < 0 := by
    rintro k hk ⟨s, hs, rfl⟩
    refine ⟨ζ ^ k, hk, ?_⟩
    rw [l4d_RR_ofReal_mul_left, l4d_RR_self_VT hk, mul_one]
    refine lt_of_le_of_ne hs fun h ↦ hne ?_
    rw [h]; simp
  rcases hw with (h | h) | h
  · exact key 0 (by rw [pow_zero]; exact l4d_one_mem_VT) h
  · exact key 1 (by rw [pow_one]; exact l4d_ζ_mem_VT) h
  · exact key 2 l4d_ζ_sq_mem_VT h

/-- A point of `𝒲` with `RR(w, c) < 0`, `c ∈ V_T`, lies on the open ray `ℝ_{<0} c` (the other two
rays have `RR(·, c) ≥ 0`). -/
theorem l4d_eq_neg_mul_of_mem_walls {w c : ℂ} (hw : w ∈ walls) (hc : c ∈ VT)
    (hneg : RR w c < 0) : ∃ s : ℝ, s < 0 ∧ w = s * c := by
  have key : ∀ k : ℕ, ζ ^ k ∈ VT → w ∈ wall k → ∃ s : ℝ, s < 0 ∧ w = s * c := by
    rintro k hk ⟨s, hs, rfl⟩
    rw [l4d_RR_ofReal_mul_left] at hneg
    by_cases hkc : ζ ^ k = c
    · rw [hkc, l4d_RR_self_VT hc] at hneg
      exact ⟨s, by linarith, by rw [hkc]⟩
    · rw [l4d_RR_ne_VT hk hc hkc] at hneg
      exact absurd hneg (by nlinarith)
  rcases hw with (h | h) | h
  · exact key 0 (by rw [pow_zero]; exact l4d_one_mem_VT) h
  · exact key 1 (by rw [pow_one]; exact l4d_ζ_mem_VT) h
  · exact key 2 l4d_ζ_sq_mem_VT h

end TriFuller

/-- **Lemma 13.3.1** (`lem:nonzero`, TeX 11078–11098). Let `z⁰ ∈ ℂ³ ∖ 0` with `z₃⁰ ∈ 𝒲`, and let
`z` be the trajectory with initial condition `z(0) = z⁰` and the constant control given by the
maximum principle (the first control). Then `z(t) ≠ 0` for all `t`.

Proof (the book's): if `z(t₀) = 0`, solving the linear equations (13.2.2) gives
`z_j⁰ = (-1)^{j+1} i t₀^j u/j!`; `z⁰ ≠ 0` forces `t₀ ≠ 0`, and then `z₃⁰ = i t₀³u/6 ∉ 𝒲`, a
contradiction. The book first reduces to `u = 1` by the rotation of Lemma 13.2.2; the computation is
the same for every vertex `u`, and it is done directly (no rotation). The argument covers every
`t₀ ∈ ℝ`, and it does not use that the control is the first control (any constant control in `V_T`
will do; inventory, gap 6). -/
theorem lemma13_3_1 {z : Fin 3 → ℂ} (hz : z ≠ 0) (h₃ : z 2 ∈ walls) (t : ℝ) :
    flow t z (firstControl z) ≠ 0 := by
  intro h0
  have hu : firstControl z ∈ VT := (l4st_isFirstControl_firstControl hz).1
  set u := firstControl z
  have e0 : z 0 - I * t * u = 0 := by simpa [flow] using congrFun h0 0
  have e1 : z 1 + z 0 * t - I * t ^ 2 * u / 2 = 0 := by simpa [flow] using congrFun h0 1
  have e2 : z 2 + z 1 * t + z 0 * t ^ 2 / 2 - I * t ^ 3 * u / 6 = 0 := by
    simpa [flow] using congrFun h0 2
  -- `z_j⁰ = (-1)^{j+1} i t₀^j u / j!`
  have hz0 : z 0 = I * t * u := by linear_combination e0
  have hz1 : z 1 = -(I * t ^ 2 * u / 2) := by linear_combination e1 - t * e0
  have hz2 : z 2 = I * t ^ 3 * u / 6 := by linear_combination e2 - t * e1 + t ^ 2 / 2 * e0
  have ht : t ≠ 0 := by
    rintro rfl
    apply hz
    ext j
    fin_cases j <;> simp [hz0, hz1, hz2]
  refine l4d_I_mul_not_mem_walls (c := t ^ 3 / 6) (by positivity) hu ?_
  rw [hz2] at h₃
  convert h₃ using 1
  push_cast
  ring

namespace TriFuller

/-- The triple integral `u₃(t) = ½ ∫_{t₁}^{t} u(s) (t - s)² ds` of a control (equation `eqn:u3`,
(13.3.1), TeX 11118–11126, written there with `t₁ = 0`). -/
noncomputable def u3 (t₁ : ℝ) (u : ℝ → ℂ) (t : ℝ) : ℂ :=
  (1 / 2) * ∫ s in t₁..t, u s * ((t - s : ℝ) : ℂ) ^ 2

/-- The triangle `U_T` lies in the closed unit disk. -/
theorem l4st_norm_le_one_of_mem_UT {v : ℂ} (hv : v ∈ UT) : ‖v‖ ≤ 1 := by
  have hsub : UT ⊆ Metric.closedBall (0 : ℂ) 1 :=
    convexHull_min (fun x hx ↦ by simp [l4d_norm_VT hx]) (convex_closedBall 0 1)
  simpa using hsub hv

/-! ### Helpers: the maximizers of `RR(·, w)` on `U_T` -/

/-- `U_T` lies in each half-plane `RR(·, c) ≥ -1/2`, `c ∈ V_T`. -/
theorem l4d_neg_half_le_RR_of_mem_UT {v c : ℂ} (hv : v ∈ UT) (hc : c ∈ VT) :
    -1 / 2 ≤ RR v c := by
  have hsub : UT ⊆ {v : ℂ | -1 / 2 ≤ RR v c} := by
    refine convexHull_min (fun x hx ↦ ?_) (convex_halfSpace_ge (l4d_isLinearMap_RR c) _)
    change -1 / 2 ≤ RR x c
    by_cases hxc : x = c
    · rw [hxc, l4d_RR_self_VT hc]; norm_num
    · rw [l4d_RR_ne_VT hx hc hxc]
  exact hsub hv

/-- If two distinct points of `U_T` both maximize `RR(·, w)` on `U_T`, then `w ∈ 𝒲`: otherwise
one vertex `m` is the only maximizer on `V_T` (`l4st_mem_walls_of_maximizers`), the affine
function `RR(·, w) + (2/3)δ(1 - RR(·, m))` (`δ` the gap to the other vertices) is at most `RR(m, w)`
on `V_T`, hence on `U_T`, and a maximizer `v` then has `RR(v, m) ≥ 1`, so `v = m`
(`|v| ≤ 1 = |m|`). -/
theorem l4d_mem_walls_of_maximizers_UT {w v₁ v₂ : ℂ} (h₁ : v₁ ∈ UT) (h₂ : v₂ ∈ UT)
    (hne : v₁ ≠ v₂) (hm₁ : ∀ v ∈ UT, RR v w ≤ RR v₁ w) (hm₂ : ∀ v ∈ UT, RR v w ≤ RR v₂ w) :
    w ∈ walls := by
  by_contra hw
  obtain ⟨m, hm, hmax⟩ : ∃ m ∈ VT, ∀ x ∈ VT, RR x w ≤ RR m w :=
    Set.exists_max_image VT (fun x ↦ RR x w) l4d_VT_finite ⟨1, l4d_one_mem_VT⟩
  have hm' : ∀ y ∈ VT, RR w y ≤ RR w m := fun y hy ↦ by
    rw [l4d_RR_comm w y, l4d_RR_comm w m]; exact hmax y hy
  have hstrict : ∀ x ∈ VT, x ≠ m → RR x w < RR m w := by
    intro x hx hxm
    refine lt_of_le_of_ne (hmax x hx) fun heq ↦ hw ?_
    refine l4st_mem_walls_of_maximizers hx hm hxm (fun y hy ↦ ?_) hm'
    rw [l4d_RR_comm w x, heq, l4d_RR_comm m w]
    exact hm' y hy
  have hnonempty : (VT \ {m}).Nonempty := by
    obtain ⟨v, hv, hvm⟩ := l4d_exists_ne_VT m
    exact ⟨v, hv, hvm⟩
  obtain ⟨x₀, hx₀, hgap⟩ :=
    Set.exists_min_image (VT \ {m}) (fun x ↦ RR m w - RR x w)
      (l4d_VT_finite.subset sdiff_subset) hnonempty
  have hδ : 0 < RR m w - RR x₀ w := sub_pos.2 (hstrict x₀ hx₀.1 hx₀.2)
  set δ := RR m w - RR x₀ w with hδdef
  have hS : UT ⊆ {v : ℂ | RR v w - 2 / 3 * δ * RR v m ≤ RR m w - 2 / 3 * δ} := by
    refine convexHull_min (fun x hx ↦ ?_)
      (convex_halfSpace_le (l4d_isLinearMap_RR_sub w m (2 / 3 * δ)) _)
    change RR x w - 2 / 3 * δ * RR x m ≤ RR m w - 2 / 3 * δ
    by_cases hxm : x = m
    · rw [hxm, l4d_RR_self_VT hm]; linarith
    · rw [l4d_RR_ne_VT hx hm hxm]
      have := hgap x ⟨hx, hxm⟩
      linarith
  have key : ∀ v ∈ UT, (∀ v' ∈ UT, RR v' w ≤ RR v w) → v = m := by
    intro v hv hvmax
    have h1 : RR v w - 2 / 3 * δ * RR v m ≤ RR m w - 2 / 3 * δ := hS hv
    have h2 : RR m w ≤ RR v w := hvmax m (l4d_VT_subset_UT hm)
    have h3 : 1 ≤ RR v m := by nlinarith
    have hnv : v.re * v.re + v.im * v.im ≤ 1 := by
      have h := l4st_norm_le_one_of_mem_UT hv
      have h' : ‖v‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg v]
      rwa [Complex.sq_norm, Complex.normSq_apply] at h'
    have hnm : m.re * m.re + m.im * m.im = 1 := by
      have := l4d_RR_self_VT hm; rwa [l4d_RR_eq] at this
    rw [l4d_RR_eq] at h3
    have hsq : (v.re - m.re) ^ 2 + (v.im - m.im) ^ 2 ≤ 0 := by nlinarith
    apply Complex.ext <;> nlinarith [sq_nonneg (v.re - m.re), sq_nonneg (v.im - m.im)]
  exact hne ((key v₁ h₁ hm₁).trans (key v₂ h₂ hm₂).symm)

/-! ### Helpers: integrability, continuity and restriction of trajectories -/

/-- A measurable function bounded on `[a, b]` is integrable on every subinterval. -/
theorem l4d_intervalIntegrable_of_bound {u : ℝ → ℂ} (hu : Measurable u) {a b C : ℝ}
    (hb : ∀ t ∈ Icc a b, ‖u t‖ ≤ C) {c d : ℝ} (hc : c ∈ Icc a b) (hd : d ∈ Icc a b) :
    IntervalIntegrable u volume c d := by
  have hab : a ≤ b := hc.1.trans hc.2
  have h : IntervalIntegrable u volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
      (Measure.integrableOn_of_bounded (by simp [Real.volume_Ioc]) hu.aestronglyMeasurable
        (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht ↦ hb t (Ioc_subset_Icc_self ht)))
  exact h.mono_set (by rw [uIcc_of_le hab]; exact uIcc_subset_Icc hc hd)

/-- The controls of a trajectory with controls in `U_T` have norm at most `1`. -/
theorem l4d_norm_le_one_of_traj {U : Set ℂ} (hU : U ⊆ UT) {t₁ t₂ : ℝ} {z : ℝ → Fin 3 → ℂ}
    {u : ℝ → ℂ} (h : IsTrajectory U t₁ t₂ z u) : ∀ t ∈ Icc t₁ t₂, ‖u t‖ ≤ 1 :=
  fun t ht ↦ l4st_norm_le_one_of_mem_UT (hU (h.2.2.1 t ht))

/-- The control of a trajectory with controls in `U_T` is integrable on every subinterval. -/
theorem l4d_intervalIntegrable_control {U : Set ℂ} (hU : U ⊆ UT) {t₁ t₂ : ℝ}
    {z : ℝ → Fin 3 → ℂ} {u : ℝ → ℂ} (h : IsTrajectory U t₁ t₂ z u) {c d : ℝ}
    (hc : c ∈ Icc t₁ t₂) (hd : d ∈ Icc t₁ t₂) : IntervalIntegrable u volume c d :=
  l4d_intervalIntegrable_of_bound h.2.1 (l4d_norm_le_one_of_traj hU h) hc hd

/-- A function that is a primitive on `[a, b]` is continuous there. -/
theorem l4d_continuousOn_of_eq_primitive {f g : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b) (hf : ∀ t ∈ Icc a b, f t = f a + ∫ s in a..t, g s) :
    ContinuousOn f (Icc a b) := by
  have h := (continuousOn_const (c := f a)).add
    (intervalIntegral.continuousOn_primitive_interval' hg left_mem_uIcc)
  rw [uIcc_of_le hab] at h
  exact h.congr fun t ht ↦ hf t ht

/-- The coordinates of a trajectory with controls in `U_T` are continuous on `[t₁, t₂]`. -/
theorem l4d_continuousOn_traj {U : Set ℂ} (hU : U ⊆ UT) {t₁ t₂ : ℝ} {z : ℝ → Fin 3 → ℂ}
    {u : ℝ → ℂ} (h : IsTrajectory U t₁ t₂ z u) (j : Fin 3) :
    ContinuousOn (fun t ↦ z t j) (Icc t₁ t₂) := by
  have hle := h.1.le
  have hI : t₁ ∈ Icc t₁ t₂ := ⟨le_rfl, hle⟩
  have hII : t₂ ∈ Icc t₁ t₂ := ⟨hle, le_rfl⟩
  have h0 : ContinuousOn (fun t ↦ z t 0) (Icc t₁ t₂) :=
    l4d_continuousOn_of_eq_primitive hle
      ((l4d_intervalIntegrable_control hU h hI hII).const_mul _) fun t ht ↦ (h.2.2.2 t ht).1
  have h1 : ContinuousOn (fun t ↦ z t 1) (Icc t₁ t₂) :=
    l4d_continuousOn_of_eq_primitive hle (h0.intervalIntegrable_of_Icc hle)
      fun t ht ↦ (h.2.2.2 t ht).2.1
  have h2 : ContinuousOn (fun t ↦ z t 2) (Icc t₁ t₂) :=
    l4d_continuousOn_of_eq_primitive hle (h1.intervalIntegrable_of_Icc hle)
      fun t ht ↦ (h.2.2.2 t ht).2.2
  fin_cases j
  · exact h0
  · exact h1
  · exact h2

/-- The restriction of a trajectory to a subinterval `[a, b] ⊆ [t₁, t₂]` is a trajectory. -/
theorem l4d_isTrajectory_mono {U : Set ℂ} (hU : U ⊆ UT) {t₁ t₂ : ℝ} {z : ℝ → Fin 3 → ℂ}
    {u : ℝ → ℂ} (h : IsTrajectory U t₁ t₂ z u) {a b : ℝ} (ha : t₁ ≤ a) (hab : a < b)
    (hb : b ≤ t₂) : IsTrajectory U a b z u := by
  have hsub : Icc a b ⊆ Icc t₁ t₂ := Icc_subset_Icc ha hb
  have haI : a ∈ Icc t₁ t₂ := ⟨ha, hab.le.trans hb⟩
  have hI : t₁ ∈ Icc t₁ t₂ := ⟨le_rfl, h.1.le⟩
  have hint0 : ∀ c ∈ Icc t₁ t₂, ∀ d ∈ Icc t₁ t₂,
      IntervalIntegrable (fun s ↦ -I * u s) volume c d :=
    fun c hc d hd ↦ (l4d_intervalIntegrable_control hU h hc hd).const_mul _
  have hint : ∀ j : Fin 3, ∀ c ∈ Icc t₁ t₂, ∀ d ∈ Icc t₁ t₂,
      IntervalIntegrable (fun s ↦ z s j) volume c d :=
    fun j c hc d hd ↦
      ((l4d_continuousOn_traj hU h j).mono (uIcc_subset_Icc hc hd)).intervalIntegrable
  refine ⟨hab, h.2.1, fun t ht ↦ h.2.2.1 t (hsub ht), fun t ht ↦ ?_⟩
  have htI := hsub ht
  obtain ⟨e0, e1, e2⟩ := h.2.2.2 t htI
  obtain ⟨f0, f1, f2⟩ := h.2.2.2 a haI
  refine ⟨?_, ?_, ?_⟩
  · rw [e0, f0, add_assoc,
      intervalIntegral.integral_add_adjacent_intervals (hint0 _ hI _ haI) (hint0 _ haI _ htI)]
  · rw [e1, f1, add_assoc,
      intervalIntegral.integral_add_adjacent_intervals (hint 0 _ hI _ haI) (hint 0 _ haI _ htI)]
  · rw [e2, f2, add_assoc,
      intervalIntegral.integral_add_adjacent_intervals (hint 1 _ hI _ haI) (hint 1 _ haI _ htI)]

/-- The maximum condition restricts to subintervals. -/
theorem l4d_maxCondition_mono {U : Set ℂ} {t₁ t₂ : ℝ} {z : ℝ → Fin 3 → ℂ} {u : ℝ → ℂ}
    (h : MaxCondition U t₁ t₂ z u) {a b : ℝ} (ha : t₁ ≤ a) (hb : b ≤ t₂) :
    MaxCondition U a b z u := by
  filter_upwards [h] with t ht htI using ht (Icc_subset_Icc ha hb htI)

/-- A trajectory whose control is almost everywhere a constant `v ∈ U` is the constant-control
solution (13.2.2) (`eqn_z1z2z3`). -/
theorem l4d_eq_flow_of_ae_eq {U : Set ℂ} {a b : ℝ} {z : ℝ → Fin 3 → ℂ} {u : ℝ → ℂ}
    (h : IsTrajectory U a b z u) {v : ℂ} (hv : v ∈ U) (hae : ∀ᵐ t, t ∈ Icc a b → u t = v) :
    ∀ t ∈ Icc a b, z t = flow (t - a) (z a) v := by
  have h' : IsTrajectory U a b z (fun _ ↦ v) := by
    refine ⟨h.1, measurable_const, fun _ _ ↦ hv, fun t ht ↦ ⟨?_, (h.2.2.2 t ht).2⟩⟩
    rw [(h.2.2.2 t ht).1]
    congr 1
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae] with s hs hsI
    rw [uIoc_of_le ht.1] at hsI
    rw [hs ⟨hsI.1.le, hsI.2.trans ht.2⟩]
  exact (eqn_z1z2z3 hv h.1 z).1 h'

/-! ### Helpers: primitives -/

/-- A primitive of a function continuous on `[a, b]` has the derivative `g(t)` at interior
points. -/
theorem l4d_hasDerivAt_of_eq_primitive {f g : ℝ → ℂ} {a b : ℝ} (hg : ContinuousOn g (Icc a b))
    (hf : ∀ t ∈ Icc a b, f t = f a + ∫ s in a..t, g s) {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt f (g t) t := by
  have hint : IntervalIntegrable g volume a t :=
    (hg.mono (Icc_subset_Icc le_rfl ht.2.le)).intervalIntegrable_of_Icc ht.1.le
  have hd : HasDerivAt (fun x ↦ f a + ∫ s in a..x, g s) (g t) t :=
    (intervalIntegral.integral_hasDerivAt_right hint
      ((hg.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo t ht)
      (hg.continuousAt (Icc_mem_nhds ht.1 ht.2))).const_add (f a)
  exact hd.congr_of_eventuallyEq
    (Filter.eventually_of_mem (Ioo_mem_nhds ht.1 ht.2) fun x hx ↦ hf x (Ioo_subset_Icc_self hx))

/-- A primitive of an integrable function has the derivative `g(t)` at almost every interior point
(Lebesgue's differentiation theorem). -/
theorem l4d_ae_hasDerivAt_of_eq_primitive {f g : ℝ → ℂ} {a b : ℝ}
    (hg : IntervalIntegrable g volume a b) (hf : ∀ t ∈ Icc a b, f t = f a + ∫ s in a..t, g s) :
    ∀ᵐ t, t ∈ Ioo a b → HasDerivAt f (g t) t := by
  filter_upwards [hg.ae_hasDerivAt_integral] with t htd ht
  have hab : a ≤ b := ht.1.le.trans ht.2.le
  have hd := (htd (by rw [uIcc_of_le hab]; exact Ioo_subset_Icc_self ht) a left_mem_uIcc).const_add
    (f a)
  exact hd.congr_of_eventuallyEq
    (Filter.eventually_of_mem (Ioo_mem_nhds ht.1 ht.2) fun x hx ↦ hf x (Ioo_subset_Icc_self hx))

/-- If the primitive of a function continuous on `[a, b]` vanishes there, so does the function. -/
theorem l4d_eq_zero_of_primitive_eq_zero {g : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hg : ContinuousOn g (Icc a b)) (h0 : ∀ t ∈ Icc a b, ∫ s in a..t, g s = 0) :
    ∀ t ∈ Icc a b, g t = 0 := by
  have hf : ∀ t ∈ Icc a b, (∫ s in a..t, g s) = (∫ s in a..a, g s) + ∫ s in a..t, g s := by
    intro t _; simp
  have hIoo : EqOn g 0 (Ioo a b) := by
    intro t ht
    have h1 := l4d_hasDerivAt_of_eq_primitive (f := fun t ↦ ∫ s in a..t, g s) hg hf ht
    have h2 : HasDerivAt (fun t ↦ ∫ s in a..t, g s) 0 t :=
      (hasDerivAt_const t (0 : ℂ)).congr_of_eventuallyEq
        (Filter.eventually_of_mem (Ioo_mem_nhds ht.1 ht.2)
          fun x hx ↦ h0 x (Ioo_subset_Icc_self hx))
    exact h1.unique h2
  intro t ht
  exact hIoo.of_subset_closure hg continuousOn_const Ioo_subset_Icc_self
    (by rw [closure_Ioo hab.ne]) ht

/-- If the primitive of an integrable function vanishes on `[a, b]`, the function vanishes almost
everywhere there. -/
theorem l4d_ae_eq_zero_of_primitive_eq_zero {g : ℝ → ℂ} {a b : ℝ}
    (hg : IntervalIntegrable g volume a b) (h0 : ∀ t ∈ Icc a b, ∫ s in a..t, g s = 0) :
    ∀ᵐ t, t ∈ Icc a b → g t = 0 := by
  have hf : ∀ t ∈ Icc a b, (∫ s in a..t, g s) = (∫ s in a..a, g s) + ∫ s in a..t, g s := by
    intro t _; simp
  have hna : ∀ᵐ t ∂volume, t ≠ a := by simp [ae_iff, measure_singleton]
  have hnb : ∀ᵐ t ∂volume, t ≠ b := by simp [ae_iff, measure_singleton]
  filter_upwards [l4d_ae_hasDerivAt_of_eq_primitive (f := fun t ↦ ∫ s in a..t, g s) hg hf, hna,
    hnb] with t h1 hta htb ht
  have ht' : t ∈ Ioo a b := ⟨lt_of_le_of_ne ht.1 (Ne.symm hta), lt_of_le_of_ne ht.2 htb⟩
  have h2 : HasDerivAt (fun t ↦ ∫ s in a..t, g s) 0 t :=
    (hasDerivAt_const t (0 : ℂ)).congr_of_eventuallyEq
      (Filter.eventually_of_mem (Ioo_mem_nhds ht'.1 ht'.2)
        fun x hx ↦ h0 x (Ioo_subset_Icc_self hx))
  exact (h1 ht').unique h2

/-! ### Helpers: Cauchy's formula for repeated integration -/

/-- Fubini on the triangle `a < ρ ≤ s ≤ t`: for a bounded measurable `g`,
`∫_a^t ∫_a^s g(ρ)(s - ρ)ⁿ dρ ds = ∫_a^t g(ρ)(t - ρ)ⁿ⁺¹/(n + 1) dρ`. -/
theorem l4d_integral_integral_mul_pow {g : ℝ → ℂ} (hg : Measurable g) {a t M : ℝ} (hat : a ≤ t)
    (hgM : ∀ ρ ∈ Ioc a t, ‖g ρ‖ ≤ M) (n : ℕ) :
    ∫ s in a..t, ∫ ρ in a..s, g ρ * ((s - ρ : ℝ) : ℂ) ^ n =
      ∫ ρ in a..t, g ρ * (((t - ρ) ^ (n + 1) / (n + 1) : ℝ) : ℂ) := by
  rcases hat.eq_or_lt with rfl | hat'
  · simp
  have hM : 0 ≤ M := (norm_nonneg _).trans (hgM t ⟨hat', le_rfl⟩)
  set μ : Measure ℝ := volume.restrict (Ioc a t) with hμ
  set F : ℝ → ℝ → ℂ := fun s ρ ↦ if ρ ≤ s then g ρ * ((s - ρ : ℝ) : ℂ) ^ n else 0 with hF
  have hmeas : Measurable (Function.uncurry F) := by
    change Measurable fun p : ℝ × ℝ ↦
      if p.2 ≤ p.1 then g p.2 * ((p.1 - p.2 : ℝ) : ℂ) ^ n else 0
    refine Measurable.ite (measurableSet_le measurable_snd measurable_fst) ?_ measurable_const
    exact (hg.comp measurable_snd).mul
      (by fun_prop : Continuous fun p : ℝ × ℝ ↦ ((p.1 - p.2 : ℝ) : ℂ) ^ n).measurable
  have hint : Integrable (Function.uncurry F) (μ.prod μ) := by
    refine Integrable.of_bound hmeas.aestronglyMeasurable (M * (t - a) ^ n) ?_
    rw [hμ, Measure.prod_restrict]
    refine ae_restrict_of_forall_mem (measurableSet_Ioc.prod measurableSet_Ioc) ?_
    rintro ⟨s, ρ⟩ ⟨hs, hρ⟩
    simp only [Function.uncurry_apply_pair, hF]
    split_ifs with hle
    · rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.2 hle)]
      have h1 : s - ρ ≤ t - a := by linarith [hs.2, hρ.1]
      exact mul_le_mul (hgM ρ hρ) (pow_le_pow_left₀ (sub_nonneg.2 hle) h1 n) (by positivity) hM
    · rw [norm_zero]; have : 0 ≤ t - a := by linarith
      positivity
  have hL : ∀ s ∈ Ioc a t, (∫ ρ in a..s, g ρ * ((s - ρ : ℝ) : ℂ) ^ n) = ∫ ρ, F s ρ ∂μ := by
    intro s hs
    have hFs : (fun ρ ↦ F s ρ) = (Iic s).indicator fun ρ ↦ g ρ * ((s - ρ : ℝ) : ℂ) ^ n := by
      ext ρ; simp only [hF, Set.indicator_apply, Set.mem_Iic]
    have hset : Iic s ∩ Ioc a t = Ioc a s := by
      ext ρ; simp only [mem_inter_iff, mem_Iic, mem_Ioc]
      constructor
      · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.trans hs.2⟩
    rw [hFs, integral_indicator measurableSet_Iic, hμ, Measure.restrict_restrict measurableSet_Iic,
      hset, intervalIntegral.integral_of_le hs.1.le]
  have hR : ∀ ρ ∈ Ioc a t,
      g ρ * (((t - ρ) ^ (n + 1) / (n + 1) : ℝ) : ℂ) = ∫ s, F s ρ ∂μ := by
    intro ρ hρ
    have hFρ : (fun s ↦ F s ρ) = (Ici ρ).indicator fun s ↦ g ρ * ((s - ρ : ℝ) : ℂ) ^ n := by
      ext s; simp only [hF, Set.indicator_apply, Set.mem_Ici]
    have hset : Ici ρ ∩ Ioc a t = Icc ρ t := by
      ext s; simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]
      constructor
      · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨h1, hρ.1.trans_le h1, h3⟩
    rw [hFρ, integral_indicator measurableSet_Ici, hμ, Measure.restrict_restrict measurableSet_Ici,
      hset, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hρ.2,
      intervalIntegral.integral_const_mul]
    congr 1
    have hcast : (fun s : ℝ ↦ ((s - ρ : ℝ) : ℂ) ^ n) = fun s ↦ (((s - ρ) ^ n : ℝ) : ℂ) := by
      ext s; push_cast; ring
    have hsub := intervalIntegral.integral_comp_sub_right (fun x : ℝ ↦ x ^ n) ρ (a := ρ) (b := t)
    rw [hcast, intervalIntegral.integral_ofReal, hsub, integral_pow]
    simp
  rw [intervalIntegral.integral_of_le hat, intervalIntegral.integral_of_le hat,
    setIntegral_congr_fun measurableSet_Ioc hL, setIntegral_congr_fun measurableSet_Ioc hR]
  exact integral_integral_swap hint

/-- `∫_a^t ((s - a : ℝ) : ℂ) ds = (t - a)²/2`. -/
theorem l4d_integral_sub_ofReal (a t : ℝ) :
    ∫ s in a..t, ((s - a : ℝ) : ℂ) = (((t - a) ^ 2 / 2 : ℝ) : ℂ) := by
  have hsub := intervalIntegral.integral_comp_sub_right (fun x : ℝ ↦ x) a (a := a) (b := t)
  rw [intervalIntegral.integral_ofReal, hsub, integral_id]
  simp

/-- `∫_a^t (t - s)² ds = (t - a)³/3`. -/
theorem l4d_integral_sq_sub (a t : ℝ) : ∫ s in a..t, (t - s) ^ 2 = (t - a) ^ 3 / 3 := by
  have hsub := intervalIntegral.integral_comp_sub_left (fun x : ℝ ↦ x ^ 2) t (a := a) (b := t)
  rw [hsub, integral_pow]
  norm_num

end TriFuller

/-- **Equation `eqn:u3` (13.3.1)** (TeX 11118–11129). For a measurable control `u` with `|u| ≤ 1`
on `[t₁, t₂]`, `u₃(t) = ½ ∫_{t₁}^{t} u(s)(t - s)² ds` solves the initial value problem `u₃''' = u`,
`u₃(t₁) = u₃'(t₁) = u₃''(t₁) = 0` (the book writes `u(0) = u'(0) = u''(0) = 0` for the initial
conditions of `u₃`): in Carathéodory's sense, it is the threefold iterated integral of `u` from
`t₁` (Cauchy's formula for repeated integration). It satisfies `|u₃(t)| ≤ ½∫_{t₁}^{t} (t - s)² ds
= (t - t₁)³/6` (the book's `O(t³)`).

Proof: Fubini's theorem on the triangle `t₁ < ρ ≤ s ≤ t` (`l4d_integral_integral_mul_pow`), twice:
`∫_{t₁}^{s} ∫_{t₁}^{σ} u = ∫_{t₁}^{s} u(ρ)(s - ρ) dρ`, then
`∫_{t₁}^{t} ∫_{t₁}^{s} u(ρ)(s - ρ) dρ ds = ∫_{t₁}^{t} u(ρ)(t - ρ)²/2 dρ`. The bound is the
book's. -/
theorem eqn_u3 {t₁ t₂ : ℝ} {u : ℝ → ℂ} (hu : Measurable u) (hb : ∀ t ∈ Icc t₁ t₂, ‖u t‖ ≤ 1) :
    ∀ t ∈ Icc t₁ t₂, u3 t₁ u t = (∫ s in t₁..t, ∫ σ in t₁..s, ∫ ρ in t₁..σ, u ρ) ∧
      ‖u3 t₁ u t‖ ≤ (t - t₁) ^ 3 / 6 := by
  intro t ht
  have hbd : ∀ s ∈ Icc t₁ t, ∀ ρ ∈ Ioc t₁ s, ‖u ρ‖ ≤ 1 :=
    fun s hs ρ hρ ↦ hb ρ ⟨hρ.1.le, hρ.2.trans (hs.2.trans ht.2)⟩
  constructor
  · have step1 : ∀ s ∈ uIcc t₁ t,
        (∫ σ in t₁..s, ∫ ρ in t₁..σ, u ρ) = ∫ ρ in t₁..s, u ρ * ((s - ρ : ℝ) : ℂ) := by
      intro s hs
      rw [uIcc_of_le ht.1] at hs
      have h := l4d_integral_integral_mul_pow hu hs.1 (hbd s hs) 0
      simp only [pow_zero, mul_one, zero_add, Nat.cast_zero, pow_one, div_one] at h
      exact h
    have h1 := l4d_integral_integral_mul_pow hu ht.1 (hbd t ⟨ht.1, le_rfl⟩) 1
    simp only [pow_one] at h1
    rw [intervalIntegral.integral_congr step1, h1, u3, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ ↦ ?_
    push_cast
    ring
  · have hle : ‖∫ s in t₁..t, u s * ((t - s : ℝ) : ℂ) ^ 2‖ ≤ ∫ s in t₁..t, (t - s) ^ 2 := by
      refine intervalIntegral.norm_integral_le_of_norm_le ht.1
        (Filter.Eventually.of_forall fun s hs ↦ ?_)
        ((by fun_prop : Continuous fun s : ℝ ↦ (t - s) ^ 2).intervalIntegrable _ _)
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      have := hb s ⟨hs.1.le, hs.2.trans ht.2⟩
      nlinarith [sq_nonneg (t - s), norm_nonneg (u s)]
    rw [l4d_integral_sq_sub] at hle
    rw [u3, norm_mul]
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [this]
    linarith

/-- **Equation `eqn:z3u3` (13.3.2)** (TeX 11131–11134). Along a trajectory of the Fuller system
with controls in `U_T`, `z₃(t) = -i u₃(t) + z₁⁰ (t - t₁)²/2! + z₂⁰ (t - t₁) + z₃⁰` (the book takes
`t₁ = 0`). Proof: integrate the Fuller system three times (`eqn_u3`). -/
theorem eqn_z3u3 {U : Set ℂ} (hU : U ⊆ UT) {t₁ t₂ : ℝ} {z : ℝ → Fin 3 → ℂ} {u : ℝ → ℂ}
    (h : IsTrajectory U t₁ t₂ z u) :
    ∀ t ∈ Icc t₁ t₂, z t 2 = -I * u3 t₁ u t + z t₁ 0 * ((t - t₁ : ℝ) : ℂ) ^ 2 / 2 +
      z t₁ 1 * ((t - t₁ : ℝ) : ℂ) + z t₁ 2 := by
  have hb := l4d_norm_le_one_of_traj hU h
  have hlt := h.1
  have heq := h.2.2.2
  have hI : t₁ ∈ Icc t₁ t₂ := ⟨le_rfl, hlt.le⟩
  have hII : t₂ ∈ Icc t₁ t₂ := ⟨hlt.le, le_rfl⟩
  have huint : IntervalIntegrable u volume t₁ t₂ := l4d_intervalIntegrable_control hU h hI hII
  -- the primitives `I₁ = ∫ u` and `I₂ = ∫ I₁`
  have hI₁c : ContinuousOn (fun s ↦ ∫ ρ in t₁..s, u ρ) (Icc t₁ t₂) := by
    have := intervalIntegral.continuousOn_primitive_interval' huint left_mem_uIcc
    rwa [uIcc_of_le hlt.le] at this
  have hI₂c : ContinuousOn (fun s ↦ ∫ σ in t₁..s, ∫ ρ in t₁..σ, u ρ) (Icc t₁ t₂) := by
    have := intervalIntegral.continuousOn_primitive_interval'
      (hI₁c.intervalIntegrable_of_Icc (μ := volume) hlt.le) left_mem_uIcc
    rwa [uIcc_of_le hlt.le] at this
  have hsub : ∀ s ∈ Icc t₁ t₂, uIcc t₁ s ⊆ Icc t₁ t₂ := fun s hs ↦ by
    rw [uIcc_of_le hs.1]; exact Icc_subset_Icc le_rfl hs.2
  have hz0 : ∀ s ∈ Icc t₁ t₂, z s 0 = z t₁ 0 - I * ∫ ρ in t₁..s, u ρ := by
    intro s hs; rw [(heq s hs).1, intervalIntegral.integral_const_mul]; ring
  have hz1 : ∀ s ∈ Icc t₁ t₂, z s 1 = z t₁ 1 + z t₁ 0 * ((s - t₁ : ℝ) : ℂ) -
      I * ∫ σ in t₁..s, ∫ ρ in t₁..σ, u ρ := by
    intro s hs
    rw [(heq s hs).2.1, intervalIntegral.integral_congr fun σ hσ ↦ hz0 σ (hsub s hs hσ),
      intervalIntegral.integral_sub intervalIntegrable_const
        (((hI₁c.mono (hsub s hs)).intervalIntegrable).const_mul I),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, Complex.real_smul]
    ring
  intro t ht
  have hint1 : IntervalIntegrable (fun s : ℝ ↦ z t₁ 1 + z t₁ 0 * ((s - t₁ : ℝ) : ℂ)) volume t₁ t :=
    (by fun_prop : Continuous fun s : ℝ ↦ z t₁ 1 + z t₁ 0 * ((s - t₁ : ℝ) : ℂ)).intervalIntegrable
      _ _
  have hint2 : IntervalIntegrable (fun s ↦ I * ∫ σ in t₁..s, ∫ ρ in t₁..σ, u ρ) volume t₁ t :=
    ((hI₂c.mono (hsub t ht)).intervalIntegrable).const_mul I
  rw [(heq t ht).2.2, intervalIntegral.integral_congr fun s hs ↦ hz1 s (hsub t ht hs),
    intervalIntegral.integral_sub hint1 hint2,
    intervalIntegral.integral_add intervalIntegrable_const
      ((by fun_prop : Continuous fun s : ℝ ↦ z t₁ 0 * ((s - t₁ : ℝ) : ℂ)).intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, l4d_integral_sub_ofReal, Complex.real_smul,
    ← (eqn_u3 h.2.1 hb t ht).1]
  push_cast
  ring

namespace TriFuller

/-- `RR(u₃(t), d) = ½ ∫_a^t RR(u(s), d)(t - s)² ds`: `RR(·, d)` is a continuous `ℝ`-linear map. -/
theorem l4d_RR_u3 {a t : ℝ} {u : ℝ → ℂ} (hu : IntervalIntegrable u volume a t) (d : ℂ) :
    RR (u3 a u t) d = 1 / 2 * ∫ s in a..t, RR (u s) d * (t - s) ^ 2 := by
  have hRR : ∀ x : ℂ, RR x d = Complex.reCLM (x * starRingEnd ℂ d) := by
    intro x
    simp only [Complex.reCLM_apply, l4d_RR_eq, Complex.mul_re, Complex.conj_re,
      Complex.conj_im]
    ring
  have hint : IntervalIntegrable (fun s ↦ u s * ((t - s : ℝ) : ℂ) ^ 2 * starRingEnd ℂ d)
      volume a t :=
    (hu.mul_continuousOn
      (by fun_prop : Continuous fun s : ℝ ↦ ((t - s : ℝ) : ℂ) ^ 2).continuousOn).mul_const _
  rw [hRR, u3, mul_assoc, ← intervalIntegral.integral_mul_const]
  have hre : ∀ x : ℂ, Complex.reCLM ((1 / 2 : ℂ) * x) = 1 / 2 * Complex.reCLM x := by
    intro x; simp only [Complex.reCLM_apply, Complex.mul_re]; norm_num
  rw [hre, ← ContinuousLinearMap.intervalIntegral_comp_comm _ hint]
  congr 1
  refine intervalIntegral.integral_congr fun s _ ↦ ?_
  simp only [hRR]
  simp only [Complex.reCLM_apply, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im]
  have h2 : ((t - s : ℝ) : ℂ) ^ 2 = (((t - s) ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h2, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The book's second case of Lemma 13.3.2 on a subinterval: a trajectory with controls in `U_T`
satisfying the maximum principle cannot keep `z₃` on an open ray `ℝ_{<0} c`, `c ∈ V_T`, of `𝒲`.
There the maximizing face is the edge opposite `c`, so `RR(u, c) = -1/2` almost everywhere
(the book's `Re u = -1/2` for `c = 1`), `RR(u₃(t), c) = -(t - t₁)³/12`, and by (13.3.2)
`0 = RR(z₃(t), ic) = (t - t₁)³/12 + (quadratic in t)` on `[t₁, t₂]`, which is absurd (the third
finite difference of the right side is `(t₂ - t₁)³/54 ≠ 0`). -/
theorem l4d_false_of_mem_ray {t₁ t₂ : ℝ} {z : ℝ → Fin 3 → ℂ} {u : ℝ → ℂ}
    (h : IsTrajectory UT t₁ t₂ z u) (hmax : MaxCondition UT t₁ t₂ z u) {c : ℂ} (hc : c ∈ VT)
    (hray : ∀ t ∈ Icc t₁ t₂, ∃ s : ℝ, s < 0 ∧ z t 2 = s * c) : False := by
  -- the control lies on the edge opposite `c`: `RR(u, c) = -1/2`
  obtain ⟨v, hv, hvc⟩ := l4d_exists_ne_VT c
  have hA : ∀ᵐ t, t ∈ Icc t₁ t₂ → RR (u t) c = -1 / 2 := by
    filter_upwards [hmax] with t hmt ht
    obtain ⟨s, hs, hzs⟩ := hray t ht
    have h1 := hmt ht v (l4d_VT_subset_UT hv)
    simp only [ham, hzs, add_le_add_iff_left, l4d_RR_ofReal_mul_right] at h1
    rw [l4d_RR_ne_VT hv hc hvc] at h1
    have h2 := l4d_neg_half_le_RR_of_mem_UT (h.2.2.1 t ht) hc
    nlinarith
  -- `z₃` stays on the ray: `RR(z₃, ic) = 0`
  have hB : ∀ t ∈ Icc t₁ t₂, RR (z t 2) (I * c) = 0 := by
    intro t ht
    obtain ⟨s, -, hzs⟩ := hray t ht
    rw [hzs]
    simp only [l4d_RR_eq, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hI : t₁ ∈ Icc t₁ t₂ := ⟨le_rfl, h.1.le⟩
  -- `RR(u₃(t), c) = -(t - t₁)³/12`
  have hu3 : ∀ t ∈ Icc t₁ t₂, RR (u3 t₁ u t) c = -(t - t₁) ^ 3 / 12 := by
    intro t ht
    rw [l4d_RR_u3 (l4d_intervalIntegrable_control subset_rfl h hI ht) c,
      intervalIntegral.integral_congr_ae (g := fun s ↦ -1 / 2 * (t - s) ^ 2) ?_,
      intervalIntegral.integral_const_mul, l4d_integral_sq_sub]
    · ring
    · filter_upwards [hA] with s hs hsI
      rw [uIoc_of_le ht.1] at hsI
      rw [hs ⟨hsI.1.le, hsI.2.trans ht.2⟩]
  -- the cubic `(t - t₁)³/12 + (quadratic)` vanishes on `[t₁, t₂]`
  have hP : ∀ t ∈ Icc t₁ t₂, (t - t₁) ^ 3 / 12 + RR (z t₁ 0) (I * c) * ((t - t₁) ^ 2 / 2) +
      RR (z t₁ 1) (I * c) * (t - t₁) + RR (z t₁ 2) (I * c) = 0 := by
    intro t ht
    have e := hB t ht
    have hz := eqn_z3u3 subset_rfl h t ht
    have h2 : z t₁ 0 * ((t - t₁ : ℝ) : ℂ) ^ 2 / 2 = (((t - t₁) ^ 2 / 2 : ℝ) : ℂ) * z t₁ 0 := by
      push_cast; ring
    rw [hz, h2, mul_comm (z t₁ 1), l4d_RR_add_left, l4d_RR_add_left, l4d_RR_add_left,
      l4d_RR_ofReal_mul_left, l4d_RR_ofReal_mul_left] at e
    have e2 : RR (-I * u3 t₁ u t) (I * c) = -RR (u3 t₁ u t) c := by
      simp only [l4d_RR_eq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
        Complex.I_re, Complex.I_im]
      ring
    rw [e2, hu3 t ht] at e
    linear_combination e
  have hH : 0 < t₂ - t₁ := sub_pos.2 h.1
  have p0 := hP t₁ hI
  have p1 := hP (t₁ + (t₂ - t₁) / 3) ⟨by linarith, by linarith⟩
  have p2 := hP (t₁ + 2 * (t₂ - t₁) / 3) ⟨by linarith, by linarith⟩
  have p3 := hP t₂ ⟨h.1.le, le_rfl⟩
  have : (t₂ - t₁) ^ 3 / 54 = 0 := by linear_combination p3 - 3 * p2 + 3 * p1 - p0
  have : 0 < (t₂ - t₁) ^ 3 / 54 := by positivity
  linarith

/-- If `‖B‖ ≤ x K` for all `x ∈ (0, T]`, then `B = 0`. -/
private lemma l4d_eq_zero_of_norm_le_mul {B : ℂ} {K T : ℝ} (hT : 0 < T) (hK : 0 ≤ K)
    (h : ∀ x : ℝ, 0 < x → x ≤ T → ‖B‖ ≤ x * K) : B = 0 := by
  by_contra hB
  have hr : 0 < ‖B‖ := norm_pos_iff.2 hB
  set x := min T (‖B‖ / (2 * (K + 1)))
  have hx : 0 < x := lt_min hT (by positivity)
  have h1 := h x hx (min_le_left _ _)
  have hx2 : x ≤ ‖B‖ / (2 * (K + 1)) := min_le_right _ _
  have h3 : x * K ≤ ‖B‖ / 2 := by
    calc x * K ≤ ‖B‖ / (2 * (K + 1)) * K := mul_le_mul_of_nonneg_right hx2 hK
      _ ≤ ‖B‖ / 2 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
  linarith

end TriFuller

/-- **Lemma 13.3.2** (`lemma:no-singular`, TeX 11108–11156). Let `(z₁, z₂, z₃, u)` be a controlled
Fuller trajectory on `[t₁, t₂]`, with `z_j` absolutely continuous and `u : [t₁, t₂] → U_T`
measurable, satisfying the maximum principle for the Hamiltonian `H_F`. Suppose that the
trajectory is singular in the sense that for all `t ∈ [t₁, t₂]` the set of controls maximizing the
Hamiltonian is a face of `U_T` and not a vertex. Then `(z₁, z₂, z₃)` is identically zero and the
control is zero almost everywhere. (The book's "`z_j : [t₁, t₂] → ℂ³`" means `ℂ`.)

Proof (the book's, with its gap repaired along its lines). Write `z₃` by (13.3.2) with the bound
`|u₃(t)| ≤ (t - t₁)³/6` of (13.3.1). The set of maximizers of `v ↦ H_F(z(t), v) = RR(z₁, z₂ i) +
RR(v, z₃(t))` on `U_T` is all of `U_T` if `z₃(t) = 0`, an edge if `z₃(t)` lies on an open ray of
`𝒲`, and a vertex otherwise; so the hypothesis says `z₃(t) ∈ 𝒲` for every t
(`l4d_mem_walls_of_maximizers_UT`; only "not a vertex" is used).
1. (Book's second case, on a subinterval.) The book assumes that the maximizing edge is the same
   on the whole interval (TeX 11145–11147; inventory, gap 7). Repair: if `z₃(t₀) ≠ 0` for some
   `t₀`, it lies on the open ray `ℝ_{<0} c` of a vertex `c` (`RR(z₃(t₀), c) < 0`), and by continuity
   `RR(z₃, c) < 0` on an interval `[a, b] ∋ t₀` of positive length; a point of `𝒲` with
   `RR(·, c) < 0` lies on the ray of `c`, so `z₃` stays on that ray on `[a, b]` and the maximizing
   face is the edge opposite `c` there. The book's argument (written for `c = 1`, the edge
   `[ζ, ζ²]`) then applies on `[a, b]` (`l4d_false_of_mem_ray`): `RR(u(t), c) = -½` a.e.,
   `RR(u₃(t), c) = -(t - a)³/12` (from `a`), and `0 = RR(z₃(t), ic) = (t - a)³/12 +
   (quadratic in t)` on `[a, b]`, which is absurd. Hence `z₃ ≡ 0` on `[t₁, t₂]`.
2. (Book's first case.) `z₃ ≡ 0` and `|u₃| ≤ (t - t₁)³/6` give `z₁⁰ = z₂⁰ = z₃⁰ = 0`, then
   `u₃ ≡ 0` by (13.3.2). By (13.3.1) `u₃ = ∫∫∫ u`, and `u = u₃'''` almost everywhere: the
   primitives `∫∫ u` (continuous) and `∫ u` vanish, and so does `u` almost everywhere (Lebesgue's
   differentiation theorem). Then `z₁ = z₁⁰ - i∫u ≡ 0`, `z₂ = z₂⁰ + ∫z₁ ≡ 0` and `z ≡ 0`. -/
theorem lemma13_3_2 {t₁ t₂ : ℝ} {z : ℝ → Fin 3 → ℂ} {u : ℝ → ℂ} (h : IsTrajectory UT t₁ t₂ z u)
    (hmax : MaxCondition UT t₁ t₂ z u)
    (hsing : ∀ t ∈ Icc t₁ t₂,
      IsExtreme ℝ UT (hamArgmax UT (z t)) ∧ (hamArgmax UT (z t)).Nontrivial) :
    (∀ t ∈ Icc t₁ t₂, z t = 0) ∧ ∀ᵐ t, t ∈ Icc t₁ t₂ → u t = 0 := by
  have hlt := h.1
  have hI : t₁ ∈ Icc t₁ t₂ := ⟨le_rfl, hlt.le⟩
  have hII : t₂ ∈ Icc t₁ t₂ := ⟨hlt.le, le_rfl⟩
  -- `z₃(t) ∈ 𝒲` for every `t`
  have hwall : ∀ t ∈ Icc t₁ t₂, z t 2 ∈ walls := by
    intro t ht
    obtain ⟨-, v₁, hv₁, v₂, hv₂, hne⟩ := hsing t ht
    have hm : ∀ v₀ ∈ hamArgmax UT (z t), ∀ v ∈ UT, RR v (z t 2) ≤ RR v₀ (z t 2) := by
      intro v₀ hv₀ v hv
      have := hv₀.2 v hv
      simp only [ham, add_le_add_iff_left] at this
      exact this
    exact l4d_mem_walls_of_maximizers_UT hv₁.1 hv₂.1 hne (hm v₁ hv₁) (hm v₂ hv₂)
  -- Step 1: `z₃ ≡ 0`
  have hz3 : ∀ t ∈ Icc t₁ t₂, z t 2 = 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨t₀, ht₀, hne⟩ := hcon
    obtain ⟨c, hc, hneg⟩ := l4d_exists_RR_neg_of_mem_walls (hwall t₀ ht₀) hne
    have hcont : ContinuousOn (fun t ↦ RR (z t 2) c) (Icc t₁ t₂) := by
      have h2 := l4d_continuousOn_traj subset_rfl h 2
      simp only [l4d_RR_eq]
      exact ((Complex.continuous_re.comp_continuousOn h2).mul continuousOn_const).add
        ((Complex.continuous_im.comp_continuousOn h2).mul continuousOn_const)
    obtain ⟨δ, hδ, hδprop⟩ :=
      Metric.continuousWithinAt_iff.1 (hcont t₀ ht₀) (-(RR (z t₀ 2) c)) (by linarith)
    set a := max t₁ (t₀ - δ / 2)
    set b := min t₂ (t₀ + δ / 2)
    have ha : t₁ ≤ a := le_max_left _ _
    have hb : b ≤ t₂ := min_le_left _ _
    have hab : a < b := by
      rw [max_lt_iff, lt_min_iff, lt_min_iff]
      exact ⟨⟨hlt, by linarith [ht₀.1]⟩, by linarith [ht₀.2], by linarith⟩
    refine l4d_false_of_mem_ray (l4d_isTrajectory_mono subset_rfl h ha hab hb)
      (l4d_maxCondition_mono hmax ha hb) hc fun t ht ↦ ?_
    have htI : t ∈ Icc t₁ t₂ := ⟨ha.trans ht.1, ht.2.trans hb⟩
    have hdist : dist t t₀ < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [le_max_right t₁ (t₀ - δ / 2), ht.1, ht.2,
        min_le_right t₂ (t₀ + δ / 2)]
    have hval := hδprop htI hdist
    rw [Real.dist_eq, abs_lt] at hval
    exact l4d_eq_neg_mul_of_mem_walls (hwall t htI) hc (by linarith [hval.2])
  -- Step 2 (the book's first case): `z⁰ = 0`
  have hb1 := l4d_norm_le_one_of_traj subset_rfl h
  have hz := eqn_z3u3 subset_rfl h
  have hu3b : ∀ t ∈ Icc t₁ t₂, ‖u3 t₁ u t‖ ≤ (t - t₁) ^ 3 / 6 :=
    fun t ht ↦ (eqn_u3 h.2.1 hb1 t ht).2
  have h30 : z t₁ 2 = 0 := hz3 t₁ hI
  have hsmall : ∀ x : ℝ, 0 < x → x ≤ t₂ - t₁ →
      ‖z t₁ 0 * (x : ℂ) / 2 + z t₁ 1‖ ≤ x ^ 2 / 6 := by
    intro x hx hxT
    have ht : t₁ + x ∈ Icc t₁ t₂ := ⟨by linarith, by linarith⟩
    have e1 := hz _ ht
    rw [hz3 _ ht, h30, add_sub_cancel_left] at e1
    have e2 : (x : ℂ) * (z t₁ 0 * (x : ℂ) / 2 + z t₁ 1) = I * u3 t₁ u (t₁ + x) := by
      linear_combination -e1
    have hn := congrArg norm e2
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_of_nonneg hx.le] at hn
    have hb3 := hu3b _ ht
    rw [add_sub_cancel_left] at hb3
    have : x * ‖z t₁ 0 * (x : ℂ) / 2 + z t₁ 1‖ ≤ x * (x ^ 2 / 6) := by
      rw [hn]; linarith
    exact le_of_mul_le_mul_left this hx
  have hT : 0 < t₂ - t₁ := sub_pos.2 hlt
  have h20 : z t₁ 1 = 0 := by
    refine l4d_eq_zero_of_norm_le_mul hT (K := ‖z t₁ 0‖ / 2 + (t₂ - t₁) / 6) (by positivity)
      fun x hx hxT ↦ ?_
    have h1 := hsmall x hx hxT
    have h2 : ‖z t₁ 1‖ ≤ ‖z t₁ 0 * (x : ℂ) / 2 + z t₁ 1‖ + ‖z t₁ 0 * (x : ℂ) / 2‖ := by
      have := norm_sub_le (z t₁ 0 * (x : ℂ) / 2 + z t₁ 1) (z t₁ 0 * (x : ℂ) / 2)
      rwa [add_sub_cancel_left] at this
    have h3 : ‖z t₁ 0 * (x : ℂ) / 2‖ = ‖z t₁ 0‖ / 2 * x := by
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hx.le]
      norm_num
      ring
    nlinarith
  have h10 : z t₁ 0 = 0 := by
    refine l4d_eq_zero_of_norm_le_mul hT (K := 1 / 3) (by norm_num) fun x hx hxT ↦ ?_
    have h1 := hsmall x hx hxT
    rw [h20, add_zero, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hx.le] at h1
    norm_num at h1
    nlinarith
  -- `u₃ ≡ 0`, so the iterated integrals of `u` vanish
  have hu30 : ∀ t ∈ Icc t₁ t₂, u3 t₁ u t = 0 := by
    intro t ht
    have e := hz t ht
    rw [hz3 t ht, h10, h20, h30] at e
    have : I * (I * u3 t₁ u t) = 0 := by linear_combination I * e
    simpa using this
  have huint : IntervalIntegrable u volume t₁ t₂ :=
    l4d_intervalIntegrable_control subset_rfl h hI hII
  have hI₁c : ContinuousOn (fun s ↦ ∫ ρ in t₁..s, u ρ) (Icc t₁ t₂) := by
    have := intervalIntegral.continuousOn_primitive_interval' huint left_mem_uIcc
    rwa [uIcc_of_le hlt.le] at this
  have hI₂c : ContinuousOn (fun s ↦ ∫ σ in t₁..s, ∫ ρ in t₁..σ, u ρ) (Icc t₁ t₂) := by
    have := intervalIntegral.continuousOn_primitive_interval'
      (hI₁c.intervalIntegrable_of_Icc (μ := volume) hlt.le) left_mem_uIcc
    rwa [uIcc_of_le hlt.le] at this
  have hI₃0 : ∀ t ∈ Icc t₁ t₂, ∫ s in t₁..t, ∫ σ in t₁..s, ∫ ρ in t₁..σ, u ρ = 0 :=
    fun t ht ↦ ((eqn_u3 h.2.1 hb1 t ht).1).symm.trans (hu30 t ht)
  -- `u = u₃'''` almost everywhere: differentiate three times
  have hI₂0 := l4d_eq_zero_of_primitive_eq_zero hlt hI₂c hI₃0
  have hI₁0 := l4d_eq_zero_of_primitive_eq_zero hlt hI₁c hI₂0
  have hu0 := l4d_ae_eq_zero_of_primitive_eq_zero huint hI₁0
  -- `z ≡ 0`
  have hz0 : ∀ t ∈ Icc t₁ t₂, z t 0 = 0 := by
    intro t ht
    rw [(h.2.2.2 t ht).1, h10, intervalIntegral.integral_const_mul, hI₁0 t ht]
    ring
  have hz1 : ∀ t ∈ Icc t₁ t₂, z t 1 = 0 := by
    intro t ht
    have hsub : uIcc t₁ t ⊆ Icc t₁ t₂ := by
      rw [uIcc_of_le ht.1]; exact Icc_subset_Icc le_rfl ht.2
    rw [(h.2.2.2 t ht).2.1, h20, intervalIntegral.integral_congr fun s hs ↦ hz0 s (hsub hs)]
    simp
  refine ⟨fun t ht ↦ ?_, hu0⟩
  ext j
  fin_cases j
  · exact hz0 t ht
  · exact hz1 t ht
  · exact hz3 t ht

end SmoothedPolygons
