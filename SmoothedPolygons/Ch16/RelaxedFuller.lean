module

public import SmoothedPolygons.Ch13.Extremals
public import SmoothedPolygons.Ch13.SingularLocus
import Mathlib.Topology.Order.Separable
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Chapter 16: relaxed Fuller extremals follow the first control (for §16.4.2, N5)

Two facts about trajectories of the Fuller system with controls in the triangle `U_T` (relaxed
controls: weak-* limits of `V_T`-valued controls) satisfying the maximum condition, needed by the
proof of N5 (`clusterSetForwardInvariant`, `SmoothedPolygons/Ch16/ReinhardtShadowing.lean`): the
limits of rescaled Reinhardt extremals near the singular locus are such trajectories
(`exists_tendsto_rescaledArc`), and these two facts identify them.

* `eq_flow_of_maxCondition_UT`: the `U_T` form of `eq_flow_of_maxCondition` (proof of Lemma 13.2.6,
  TeX 10978–10995): from `z⁰ ≠ 0`, up to the first switching time, a relaxed extremal is the
  constant-control flow with the first control, and its control is the first control almost
  everywhere;
* `firstControl_beaten_UT`: the `U_T` form of `firstControl_beaten`: no relaxed extremal from
  `z⁰ ≠ 0` keeps the first control (almost everywhere) on an interval `[0, t_sw + ε]`.

## Proofs

`eq_flow_of_maxCondition_UT`: a relaxed extremal has `u(t) ∈ V_T` for almost every `t` with
`z(t) ≠ 0` (`l6f_ae_mem_VT`). Where the maximizing face of `U_T` at `z(t)` is a vertex, the
maximum condition forces `u(t)` to be that vertex. The set `E` of times where the maximizing face
is an edge (`z₃(t)` on the open ray `ℝ_{<0} c` of a wall, `c ∈ V_T`) has measure zero: on `E`,
`χ(t) = RR(ic, z₃(t)) = 0`; `χ` is `C²` with `χ''' = RR(ic, -iu) = -RR(c, u)` almost everywhere,
and at accumulation points of `E`, of those, and of those again (all but countably many points of
`E`, `countable_ofPred_isolated_within`; this replaces Lebesgue's density theorem)
`χ' = χ'' = χ''' = 0`, while the maximum condition puts `u` on the edge opposite `c`,
`RR(u, c) = -1/2`, so `χ''' = 1/2` (the computation of Lemma 13.2.6). The case of all of `U_T`
maximizing (`z₃(t) = 0`) is handled by the same argument: at iterated accumulation points of
`{z₃ = 0}`, `z₂ = z₁ = 0`, so `z(t) = 0` for almost every such `t` (`l6f_ae_zero`).
**Departure from the plan:** the plan cited `lemma13_3_2` for this case, but `{z₃ = 0}` need not
contain an interval (it may be a fat Cantor set), so Lemma 13.3.2, which needs the singular
condition on a whole interval, does not apply; the accumulation-point argument settles it
directly. A relaxed extremal from `z⁰ ≠ 0` does not reach `0` before `t_sw(z⁰)`: at the first zero
`t₀`, on every `[0, t]`, `t < t₀`, the control is in `V_T` almost everywhere, so
`eq_flow_of_maxCondition` (after changing the control on a null set) gives `z = z(·, z⁰, u₀)` on
`[0, t₀)`, hence at `t₀`, contradicting `flow_firstControl_ne_zero`. So `u ∈ V_T` a.e. on
`[0, T]`, the trajectory is a `V_T`-trajectory after changing the control on a null set
(`l6f_VT_traj`), and `eq_flow_of_maxCondition` applies. `firstControl_beaten_UT`: if `u = u₀`
a.e. on `[0, t_sw + ε]`, then `z = flow · z⁰ u₀` there (`IsTrajectory.eq_flow_of_ae_eq`), and by
`firstControl_beaten` some vertex `v` strictly beats `u₀` at some `t ∈ (t_sw, t_sw + ε)`, hence on
an open interval around `t` (continuity), a set of positive measure where the maximum condition
fails.
-/

@[expose] public section

namespace SmoothedPolygons

open Complex MeasureTheory Set Filter Topology

namespace TriFuller

/-! ### Helpers: the maximizers of `RR(·, w)` on `U_T`

(The values of `RR` on `V_T` and the half-planes containing `U_T` are in
`SmoothedPolygons/Ch13/SingularLocus.lean`.) -/

/-- **A maximizer of `RR(·, w)` on `U_T` that is not a vertex** (`w ≠ 0`): the maximizing face is
an edge, and `w` lies on the open ray `ℝ_{<0} c` of the opposite vertex `c`. (Some vertex `m`
maximizes too, so there are two maximizers and `w ∈ 𝒲`.) -/
private lemma l6f_ray_of_max {w u : ℂ} (hw : w ≠ 0) (hu : u ∈ UT) (huV : u ∉ VT)
    (hmax : ∀ v ∈ UT, RR v w ≤ RR u w) : ∃ c ∈ VT, ∃ s : ℝ, s < 0 ∧ w = s * c := by
  obtain ⟨m, hm, hmm⟩ : ∃ m ∈ VT, ∀ x ∈ VT, RR x w ≤ RR m w :=
    Set.exists_max_image VT (fun x ↦ RR x w) finite_VT ⟨1, one_mem_VT⟩
  have hmU : ∀ v ∈ UT, RR v w ≤ RR m w := by
    have hsub : UT ⊆ {v : ℂ | RR v w ≤ RR m w} :=
      convexHull_min (fun x hx ↦ hmm x hx) (convex_halfSpace_le (isLinearMap_RR w) _)
    exact fun v hv ↦ hsub hv
  have hwall := mem_walls_of_maximizers_UT hu (VT_subset_UT hm)
    (fun h ↦ huV (h ▸ hm)) hmax hmU
  obtain ⟨c, hc, hneg⟩ := exists_RR_neg_of_mem_walls hwall hw
  exact ⟨c, hc, eq_neg_mul_of_mem_walls hwall hc hneg⟩

/-! ### Helpers: accumulation points and derivatives -/

/-- The points of `s` at which `s` accumulates. -/
private def l6f_acc (s : Set ℝ) : Set ℝ := {x ∈ s | (𝓝[s \ {x}] x).NeBot}

/-- All but countably many points of `s` are accumulation points of `s`. -/
private lemma l6f_ae_acc (s : Set ℝ) : ∀ᵐ x, x ∈ s → x ∈ l6f_acc s := by
  have hc : (s \ l6f_acc s).Countable := by
    refine (countable_ofPred_isolated_within (s := s)).mono ?_
    rintro x ⟨hxs, hx⟩
    refine ⟨hxs, ?_⟩
    by_contra h
    exact hx ⟨hxs, ⟨h⟩⟩
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hc.measure_zero volume)] with x hx hxs
  by_contra h
  exact hx ⟨hxs, h⟩

/-- A function vanishing on `s` has derivative `0` at an accumulation point of `s`. -/
private lemma l6f_deriv_eq_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {f' : E} {s : Set ℝ} {x : ℝ} (hx : x ∈ l6f_acc s) (hf : HasDerivAt f f' x)
    (h0 : ∀ y ∈ s, f y = 0) : f' = 0 := by
  have := hx.2
  have h1 := hasDerivWithinAt_iff_tendsto_slope.1 (hf.hasDerivWithinAt (s := s))
  have h2 : Tendsto (slope f x) (𝓝[s \ {x}] x) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    simp [slope, h0 y hy.1, h0 x hx.1]
  exact tendsto_nhds_unique h1 h2

/-- Along a trajectory, `z₃' = z₂` and `z₂' = z₁` at interior times. -/
private lemma l6f_hasDerivAt_z {U : Set ℂ} (hU : U ⊆ UT) {a b : ℝ} {z : ℝ → Fin 3 → ℂ}
    {u : ℝ → ℂ} (h : IsTrajectory U a b z u) {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (fun s ↦ z s 2) (z t 1) t ∧ HasDerivAt (fun s ↦ z s 1) (z t 0) t := by
  have hI : a ∈ Icc a b := ⟨le_rfl, h.1.le⟩
  have htI : t ∈ Icc a b := Ioo_subset_Icc_self ht
  have hnhds : Icc a b ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
  have key : ∀ j : Fin 3, (∀ s ∈ Icc a b, z s (j + 1) = z a (j + 1) + ∫ σ in a..s, z σ j) →
      HasDerivAt (fun s ↦ z s (j + 1)) (z t j) t := by
    intro j hj
    have hc := IsTrajectory.continuousOn hU h j
    have hint : IntervalIntegrable (fun σ ↦ z σ j) volume a t :=
      (hc.mono (Icc_subset_Icc le_rfl ht.2.le)).intervalIntegrable_of_Icc ht.1.le
    have hmeas : StronglyMeasurableAtFilter (fun σ ↦ z σ j) (𝓝 t) volume :=
      (hc.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo t ht
    have hd := (intervalIntegral.integral_hasDerivAt_right hint hmeas
      (hc.continuousAt hnhds)).const_add (z a (j + 1))
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [hnhds] with s hs
    exact hj s hs
  exact ⟨key 1 fun s hs ↦ (h.2.2.2 s hs).2.2, key 0 fun s hs ↦ (h.2.2.2 s hs).2.1⟩

/-- Along a trajectory, `z₁' = -iu` almost everywhere (Lebesgue's differentiation theorem). -/
private lemma l6f_ae_hasDerivAt_z0 {U : Set ℂ} (hU : U ⊆ UT) {a b : ℝ} {z : ℝ → Fin 3 → ℂ}
    {u : ℝ → ℂ} (h : IsTrajectory U a b z u) :
    ∀ᵐ t, t ∈ Ioo a b → HasDerivAt (fun s ↦ z s 0) (-I * u t) t := by
  have hint : IntervalIntegrable (fun s ↦ -I * u s) volume a b :=
    (IsTrajectory.intervalIntegrable_control hU h ⟨le_rfl, h.1.le⟩ ⟨h.1.le, le_rfl⟩).const_mul _
  filter_upwards [hint.ae_hasDerivAt_integral] with t ht htI
  have htI' : t ∈ uIcc a b := by rw [uIcc_of_le h.1.le]; exact Ioo_subset_Icc_self htI
  have hd := (ht htI' a left_mem_uIcc).const_add (z a 0)
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Icc_mem_nhds htI.1 htI.2] with s hs
  exact (h.2.2.2 s hs).1

/-- `RR(c, ·)` along a curve with a derivative. -/
private lemma l6f_hasDerivAt_RR_const (c : ℂ) {f : ℝ → ℂ} {f' : ℂ} {t : ℝ}
    (hf : HasDerivAt f f' t) : HasDerivAt (fun s ↦ RR c (f s)) (RR c f') t := by
  have := hasDerivAt_RR (hasDerivAt_const t c) hf
  simpa [RR] using this

/-! ### The times where the maximizing face is not a vertex form a null set -/

/-- **Where `z₃ = 0`, almost everywhere `z = 0`**: at an accumulation point of `{z₃ = 0}`,
`z₂ = z₃' = 0`, and at an accumulation point of those, `z₁ = z₂' = 0` (the density-point
argument). -/
private lemma l6f_ae_zero {U : Set ℂ} (hU : U ⊆ UT) {a b : ℝ} {z : ℝ → Fin 3 → ℂ} {u : ℝ → ℂ}
    (h : IsTrajectory U a b z u) : ∀ᵐ t, t ∈ Ioo a b → z t 2 = 0 → z t = 0 := by
  set E : Set ℝ := {t | t ∈ Ioo a b ∧ z t 2 = 0} with hE
  filter_upwards [l6f_ae_acc E, l6f_ae_acc (l6f_acc E)] with t h1 h2 ht hz
  have htA1 : t ∈ l6f_acc E := h1 ⟨ht, hz⟩
  have htA2 : t ∈ l6f_acc (l6f_acc E) := h2 htA1
  have hz1 : ∀ s ∈ l6f_acc E, z s 1 = 0 := fun s hs ↦
    l6f_deriv_eq_zero hs (l6f_hasDerivAt_z hU h hs.1.1).1 fun y hy ↦ hy.2
  have hz0 : z t 0 = 0 := l6f_deriv_eq_zero htA2 (l6f_hasDerivAt_z hU h ht).2 hz1
  funext j
  fin_cases j
  · exact hz0
  · exact hz1 t htA1
  · exact hz

/-- **`z₃` is almost never on an open ray of the walls** (the χ‴ density-point argument). On
the set `E` of times where `z₃ = s c`, `s < 0`, the function `χ = RR(ic, z₃)` vanishes; at
accumulation points `χ' = RR(ic, z₂) = 0`, then `χ'' = RR(ic, z₁) = 0`, then (at points where
`z₁' = -iu`) `χ''' = RR(ic, -iu) = -RR(c, u) = 0`; but the maximum condition puts `u` on the
edge opposite `c`, `RR(u, c) = -1/2` (Lemma 13.2.6's computation: `χ'''` is a nonzero constant on
the edge). -/
private lemma l6f_ae_not_ray {a b : ℝ} {z : ℝ → Fin 3 → ℂ} {u : ℝ → ℂ}
    (h : IsTrajectory UT a b z u) (hmax : MaxCondition UT a b z u) {c : ℂ} (hc : c ∈ VT) :
    ∀ᵐ t, t ∈ Ioo a b → ¬ ∃ s : ℝ, s < 0 ∧ z t 2 = s * c := by
  set E : Set ℝ := {t | t ∈ Ioo a b ∧ ∃ s : ℝ, s < 0 ∧ z t 2 = s * c} with hE
  filter_upwards [l6f_ae_acc E, l6f_ae_acc (l6f_acc E), l6f_ae_acc (l6f_acc (l6f_acc E)), hmax,
    l6f_ae_hasDerivAt_z0 subset_rfl h] with t h1 h2 h3 hmt hd ht hray
  have htA3 : t ∈ l6f_acc (l6f_acc (l6f_acc E)) := h3 (h2 (h1 ⟨ht, hray⟩))
  have f1 : ∀ s ∈ l6f_acc E, RR (I * c) (z s 1) = 0 := by
    intro s hs
    refine l6f_deriv_eq_zero hs
      (l6f_hasDerivAt_RR_const (I * c) (l6f_hasDerivAt_z subset_rfl h hs.1.1).1) ?_
    rintro y ⟨-, s', -, hs'⟩
    rw [hs']
    simp only [RR_eq_re_mul_add_im_mul, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have f2 : ∀ s ∈ l6f_acc (l6f_acc E), RR (I * c) (z s 0) = 0 := fun s hs ↦
    l6f_deriv_eq_zero hs
      (l6f_hasDerivAt_RR_const (I * c) (l6f_hasDerivAt_z subset_rfl h hs.1.1.1).2) f1
  have f3 : RR (I * c) (-I * u t) = 0 :=
    l6f_deriv_eq_zero htA3 (l6f_hasDerivAt_RR_const (I * c) (hd ht)) f2
  -- the maximum condition: `RR(u(t), c) = -1/2`
  obtain ⟨s, hs, hzs⟩ := hray
  have htI : t ∈ Icc a b := Ioo_subset_Icc_self ht
  obtain ⟨v, hv, hvc⟩ := exists_mem_VT_ne c
  have hA : RR (u t) c = -1 / 2 := by
    have h1 := hmt htI v (VT_subset_UT hv)
    simp only [ham, hzs, add_le_add_iff_left, RR_ofReal_mul_right] at h1
    rw [RR_of_mem_VT_of_ne hv hc hvc] at h1
    have h2 := neg_half_le_RR_of_mem_UT (h.2.2.1 t htI) hc
    nlinarith
  have e : RR (I * c) (-I * u t) = -RR (u t) c := by
    simp only [RR_eq_re_mul_add_im_mul, Complex.mul_re, Complex.mul_im, Complex.neg_re,
      Complex.neg_im, Complex.I_re, Complex.I_im]
    ring
  rw [e, hA] at f3
  norm_num at f3

/-- **A relaxed extremal uses the vertices almost everywhere off the singular locus**: for almost
every `t ∈ [a, b]` with `z(t) ≠ 0`, `u(t) ∈ V_T`. Otherwise the maximizing face at `z(t)` is an
edge (`z₃(t)` on an open ray, `l6f_ae_not_ray`) or all of `U_T` (`z₃(t) = 0`, then `z(t) = 0`
almost surely, `l6f_ae_zero`). -/
private lemma l6f_ae_mem_VT {a b : ℝ} {z : ℝ → Fin 3 → ℂ} {u : ℝ → ℂ}
    (h : IsTrajectory UT a b z u) (hmax : MaxCondition UT a b z u) :
    ∀ᵐ t, t ∈ Icc a b → z t ≠ 0 → u t ∈ VT := by
  have hna : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ a := by simp [ae_iff, measure_singleton]
  have hnb : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ b := by simp [ae_iff, measure_singleton]
  filter_upwards [hmax, l6f_ae_zero subset_rfl h, l6f_ae_not_ray h hmax one_mem_VT,
    l6f_ae_not_ray h hmax ζ_mem_VT, l6f_ae_not_ray h hmax ζ_sq_mem_VT, hna, hnb]
    with t hmt h0 h1 h2 h3 hta htb htI hz
  have ht : t ∈ Ioo a b := ⟨lt_of_le_of_ne htI.1 (Ne.symm hta), lt_of_le_of_ne htI.2 htb⟩
  by_contra huV
  have hz2 : z t 2 ≠ 0 := fun h2 ↦ hz (h0 ht h2)
  have hRR : ∀ v ∈ UT, RR v (z t 2) ≤ RR (u t) (z t 2) := by
    intro v hv
    have := hmt htI v hv
    simp only [ham, add_le_add_iff_left] at this
    exact this
  obtain ⟨c, hc, s, hs, hzs⟩ := l6f_ray_of_max hz2 (h.2.2.1 t htI) huV hRR
  rcases mem_VT.1 hc with rfl | rfl | rfl
  · exact h1 ht ⟨s, hs, hzs⟩
  · exact h2 ht ⟨s, hs, hzs⟩
  · exact h3 ht ⟨s, hs, hzs⟩

/-- A `U_T`-trajectory whose control is in `V_T` almost everywhere is a `V_T`-trajectory after
changing the control on a null set. -/
private lemma l6f_VT_traj {a b : ℝ} {z : ℝ → Fin 3 → ℂ} {u : ℝ → ℂ}
    (h : IsTrajectory UT a b z u) (hmax : MaxCondition UT a b z u)
    (hV : ∀ᵐ t, t ∈ Icc a b → u t ∈ VT) :
    ∃ u' : ℝ → ℂ, IsTrajectory VT a b z u' ∧ MaxCondition VT a b z u' ∧
      ∀ᵐ t, t ∈ Icc a b → u' t = u t := by
  classical
  set u' : ℝ → ℂ := fun t ↦ if u t ∈ VT then u t else 1 with hu'
  have hae : ∀ᵐ t, t ∈ Icc a b → u' t = u t := by
    filter_upwards [hV] with t ht htI
    simp [hu', ht htI]
  refine ⟨u', ⟨h.1, ?_, fun t _ ↦ ?_, fun t ht ↦ ?_⟩, ?_, hae⟩
  · exact Measurable.ite (finite_VT.measurableSet.preimage h.2.1) h.2.1 measurable_const
  · by_cases hu : u t ∈ VT
    · simp [hu', hu]
    · simp only [hu', hu, ↓reduceIte]; exact one_mem_VT
  · obtain ⟨e0, e1, e2⟩ := h.2.2.2 t ht
    refine ⟨?_, e1, e2⟩
    rw [e0]
    congr 1
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae] with s hs hsI
    rw [uIoc_of_le ht.1] at hsI
    rw [hs ⟨hsI.1.le, hsI.2.trans ht.2⟩]
  · filter_upwards [hmax, hae] with t h1 h2 htI v hv
    rw [h2 htI]
    exact h1 htI v (VT_subset_UT hv)

/-- The constant-control flow is continuous in time. -/
private lemma l6f_continuous_flow (z : Fin 3 → ℂ) (u : ℂ) : Continuous fun t ↦ flow t z u :=
  continuous_iff_continuousAt.2 fun t ↦ (hasDerivAt_flow t z u).continuousAt

private lemma l6f_continuous_ham (v : ℂ) : Continuous fun w : Fin 3 → ℂ ↦ ham w v := by
  unfold ham RR
  fun_prop

/-- **Relaxed extremals follow the first control up to the first switching time** (the `U_T` form
of `eq_flow_of_maxCondition`). Let `z⁰ ≠ 0` and let `(z, u)` be a trajectory of the Fuller system on
`[0, T]` with controls in `U_T` satisfying the maximum condition, with `z(0) = z⁰` and
`T ≤ t_sw(z⁰)`. Then `z` is the constant-control solution with the first control of `z⁰`, and `u`
is the first control almost everywhere on `[0, T]`.

Proof: by `l6f_ae_mem_VT`, `u ∈ V_T` almost everywhere where `z ≠ 0`. (1) `z ≠ 0` on `[0, T]`: if
not, at the first zero `t₀ > 0` of `z`, on each `[0, t]`, `t < t₀`, the control is in `V_T` almost
everywhere, so `eq_flow_of_maxCondition` (after changing the control on a null set,
`l6f_VT_traj`) gives `z = z(·, z⁰, u₀)` on `[0, t₀)`, hence at `t₀` by continuity, while
`z(t₀, z⁰, u₀) ≠ 0` (`flow_firstControl_ne_zero`). (2) Then `u ∈ V_T` almost everywhere on
`[0, T]`, and `eq_flow_of_maxCondition` applies on `[0, T]`. -/
theorem eq_flow_of_maxCondition_UT {z₀ : Fin 3 → ℂ} (hz₀ : z₀ ≠ 0) {T : ℝ}
    (hT : T ≤ firstSwitchTime z₀) {z : ℝ → Fin 3 → ℂ} {u : ℝ → ℂ} (h : IsTrajectory UT 0 T z u)
    (hmax : MaxCondition UT 0 T z u) (h0 : z 0 = z₀) :
    (∀ t ∈ Icc 0 T, z t = flow t z₀ (firstControl z₀)) ∧
      ∀ᵐ t, t ∈ Icc 0 T → u t = firstControl z₀ := by
  set u₀ := firstControl z₀ with hu₀def
  have hV := l6f_ae_mem_VT h hmax
  have hzc : ContinuousOn z (Icc 0 T) :=
    continuousOn_pi.2 fun j ↦ IsTrajectory.continuousOn subset_rfl h j
  -- (1) `z ≠ 0` on `[0, T]`
  have hne : ∀ t ∈ Icc 0 T, z t ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨t₁, ht₁, hz₁⟩ := hcon
    set S : Set ℝ := Icc 0 T ∩ z ⁻¹' {0} with hS
    have hSne : S.Nonempty := ⟨t₁, ht₁, hz₁⟩
    have hSbdd : BddBelow S := ⟨0, fun t ht ↦ ht.1.1⟩
    have hScl : IsClosed S := hzc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
    set t₀ := sInf S with ht₀def
    have ht₀S : t₀ ∈ S := hScl.csInf_mem hSne hSbdd
    have hzt₀ : z t₀ = 0 := ht₀S.2
    have ht₀pos : 0 < t₀ := by
      rcases ht₀S.1.1.eq_or_lt with h' | h'
      · exact absurd (by rw [← h0, h']; exact hzt₀) hz₀
      · exact h'
    have ht₀T : t₀ ≤ T := ht₀S.1.2
    have hflow : EqOn z (fun t ↦ flow t z₀ u₀) (Ico 0 t₀) := by
      intro t ht
      rcases ht.1.eq_or_lt with rfl | htpos
      · simp [flow_zero, h0]
      have htT : t ≤ T := ht.2.le.trans ht₀T
      have h' := IsTrajectory.mono subset_rfl h le_rfl htpos htT
      have hm' := MaxCondition.mono hmax le_rfl htT
      have hV' : ∀ᵐ s, s ∈ Icc 0 t → u s ∈ VT := by
        filter_upwards [hV] with s hs hsI
        refine hs ⟨hsI.1, hsI.2.trans htT⟩ fun hz ↦ ?_
        have : t₀ ≤ s := csInf_le hSbdd ⟨⟨hsI.1, hsI.2.trans htT⟩, hz⟩
        linarith [hsI.2, ht.2]
      obtain ⟨u', hu'1, hu'2, -⟩ := l6f_VT_traj h' hm' hV'
      exact (eq_flow_of_maxCondition hz₀ (htT.trans hT) hu'1 hu'2 h0).1 t ⟨htpos.le, le_rfl⟩
    have hlim : z t₀ = flow t₀ z₀ u₀ := by
      refine hflow.of_subset_closure (hzc.mono (Icc_subset_Icc le_rfl ht₀T))
        (l6f_continuous_flow z₀ u₀).continuousOn Ico_subset_Icc_self ?_
        ⟨ht₀pos.le, le_rfl⟩
      rw [closure_Ico ht₀pos.ne]
    exact flow_firstControl_ne_zero hz₀ ⟨ht₀pos.le, ht₀T.trans hT⟩ (hlim ▸ hzt₀)
  -- (2) `u ∈ V_T` almost everywhere on `[0, T]`
  have hV' : ∀ᵐ t, t ∈ Icc 0 T → u t ∈ VT := by
    filter_upwards [hV] with t ht htI using ht htI (hne t htI)
  obtain ⟨u', hu'1, hu'2, hu'3⟩ := l6f_VT_traj h hmax hV'
  obtain ⟨e1, e2⟩ := eq_flow_of_maxCondition hz₀ hT hu'1 hu'2 h0
  refine ⟨e1, ?_⟩
  filter_upwards [e2, hu'3] with t h1 h2 ht
  rw [← h2 ht, h1 ht]

/-- **No relaxed extremal keeps the first control past the first switching time** (the `U_T`
form of `firstControl_beaten`): for `z⁰ ≠ 0` and `ε > 0`, a trajectory with controls in `U_T`
satisfying the maximum condition on `[0, t_sw(z⁰) + ε]` from `z⁰` does not have the first control
almost everywhere on that interval.

Proof: otherwise `z = z(·, z⁰, u₀)` on `[0, t_sw + ε]` (`IsTrajectory.eq_flow_of_ae_eq`); by
`firstControl_beaten` some vertex `v` strictly beats `u₀` at some `t ∈ (t_sw, t_sw + ε)`, hence
on an open interval around `t` (continuity), which has positive measure, while the maximum
condition and `u = u₀` hold almost everywhere there. -/
theorem firstControl_beaten_UT {z₀ : Fin 3 → ℂ} (hz₀ : z₀ ≠ 0) {ε : ℝ} (hε : 0 < ε)
    {z : ℝ → Fin 3 → ℂ} {u : ℝ → ℂ} (h : IsTrajectory UT 0 (firstSwitchTime z₀ + ε) z u)
    (hmax : MaxCondition UT 0 (firstSwitchTime z₀ + ε) z u) (h0 : z 0 = z₀) :
    ¬ ∀ᵐ t, t ∈ Icc 0 (firstSwitchTime z₀ + ε) → u t = firstControl z₀ := by
  intro hae
  set u₀ := firstControl z₀ with hu₀def
  set T := firstSwitchTime z₀ + ε with hTdef
  have hu₀ : u₀ ∈ VT := firstControl_mem_VT z₀
  have hsw := firstSwitchTime_pos hz₀
  have hzf : ∀ t ∈ Icc 0 T, z t = flow t z₀ u₀ := by
    intro t ht
    rw [IsTrajectory.eq_flow_of_ae_eq h (VT_subset_UT hu₀) hae t ht, h0, sub_zero]
  obtain ⟨t, ht, v, hv, hlt⟩ := firstControl_beaten hz₀ hε
  -- `v` beats `u₀` on an open interval around `t`
  have hopen : IsOpen {s : ℝ | ham (flow s z₀ u₀) u₀ < ham (flow s z₀ u₀) v} :=
    isOpen_lt ((l6f_continuous_ham u₀).comp (l6f_continuous_flow z₀ u₀))
      ((l6f_continuous_ham v).comp (l6f_continuous_flow z₀ u₀))
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hopen t hlt
  set p := max (t - δ) (firstSwitchTime z₀) with hp
  set q := min (t + δ) T with hq
  have hpq : p < q := by
    rw [hp, hq, max_lt_iff, lt_min_iff, lt_min_iff]
    exact ⟨⟨by linarith, by linarith [ht.2]⟩, by linarith [ht.1], ht.1.trans ht.2⟩
  have hnull : ∀ᵐ s, s ∉ Ioo p q := by
    filter_upwards [hmax, hae] with s hs1 hs2 hsI
    have hsI' : s ∈ Icc 0 T :=
      ⟨by linarith [le_max_right (t - δ) (firstSwitchTime z₀), hsI.1],
        by linarith [min_le_right (t + δ) T, hsI.2]⟩
    have h1 := hs1 hsI' v (VT_subset_UT hv)
    rw [hs2 hsI', hzf s hsI'] at h1
    have hsb : s ∈ Metric.ball t δ := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [le_max_left (t - δ) (firstSwitchTime z₀),
        min_le_left (t + δ) T, hsI.1, hsI.2]
    exact absurd h1 (not_le.2 (hball hsb))
  have hzero := measure_eq_zero_iff_ae_notMem.2 hnull
  rw [Real.volume_Ioo] at hzero
  exact absurd hzero (by simp [hpq])

end TriFuller

end SmoothedPolygons
