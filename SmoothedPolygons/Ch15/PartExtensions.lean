module

public import SmoothedPolygons.Ch15.PartitionTopology

/-!
# Chapter 15: the continuous extensions `F₃` on `𝒟₃` and `F₄` on `𝒟₄` (towards Proposition 15.3.2)

Two of the five continuous extensions of Proposition 15.3.2 (`Proposition15_3_2`,
`SmoothedPolygons/Ch15/Involution.lean`; TeX 12436–12440, 12467–12491): on the parts where the
active switching function is `χ_B` (the switch `ζ ↔ ζ²`), the switching time is an explicit root
of a quadratic, so the extension is explicit.

Along the control `ζ` or `ζ²` from `cellPoint p`, `Im z₃(t) = t q(t)` with
`q(t) = y₂ + y₁ t/2 + t²/12` (`im_flow_two_cellPoint`), and `ζ²` beats `ζ` (resp. `ζ` beats `ζ²`)
exactly when `Im z₃ < 0` (resp. `> 0`) (`ham_sq_sub_ham_ζ`). The roots of `12 q` are
`lo, hi = -3 y₁ ∓ √(9 y₁² - 12 y₂)` (`twelve_switchQuad`).

* **`𝒟₃`** (second box, first control `ζ²`, switch to `ζ`): `y₂ ≤ 0`, so `q` has the root
  `hi ≥ 0`; on `𝒟₃` the control `1` never beats `ζ²` on `[0, hi]` (`partD3_subset_cellTwoNoA`), and
  `F₃(p) := class of z(hi, cellPoint p, ζ²)` is continuous on `𝒟₃` and equals `F` on
  `𝒟₃ ∩ openBoxTwo` (`continuousOn_extD3`, `extD3_eq`).
* **`𝒟₄`** (first box, first control `ζ`, switch to `ζ²`): on `𝒟₄`, `q` has real roots,
  `y₁ ≤ 0`, and `1` never beats `ζ` on `[0, lo]` (`partD4_subset_cellOneNoA`); `F₄(p) := class of
  z(lo, cellPoint p, ζ)` is continuous on `𝒟₄` (`continuousOn_extD4`) and equals `F` on the
  interior of `𝒟₄` (`extD4_eq`). On the interior the roots are simple: a point of the interior
  with `9 y₁² = 12 y₂` is a limit of points with `9 y₁² < 12 y₂` (moving `ψ`,
  `exists_switchQuadDiscr_neg`), where `q > 0` and no point switches to `ζ²`.

The image lies on the section because two controls tie at the switching time and the
Hamiltonian is conserved (`flow_mem_sectionZero`); the first switching time is computed from
"optimal on `[0, T]`, beaten arbitrarily close after `T`" (`firstSwitchTime_eq_of`).
-/

@[expose] public section

namespace SmoothedPolygons

open Complex Set Filter Topology
open scoped Real

namespace TriFuller

/-! ### General facts: the first switching time and the section -/

/-- **The first control and the first switch from optimality and beating**: `u` maximizes the
Hamiltonian along `z(t, z, u)` on `[0, T]` and is beaten at times arbitrarily close to `T` from the
right. -/
theorem firstSwitchTime_eq_of {z : Fin 3 → ℂ} (hz : z ≠ 0) {u : ℂ} (hu : u ∈ VT) {T : ℝ}
    (hT : 0 < T) (hmax : ∀ t ∈ Icc 0 T, ∀ v ∈ VT, ham (flow t z u) v ≤ ham (flow t z u) u)
    (hbeat : ∀ ε > 0, ∃ t ∈ Ioo T (T + ε), ∃ v ∈ VT, ham (flow t z u) u < ham (flow t z u) v) :
    firstControl z = u ∧ firstSwitchTime z = T := by
  have hfc : firstControl z = u := (firstControl_eq_iff hz).2 ⟨hu, T, hT, hmax⟩
  refine ⟨hfc, ?_⟩
  unfold firstSwitchTime
  rw [hfc]
  apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
  · obtain ⟨t, ht, v, hv, h⟩ := hbeat 1 one_pos
    exact ⟨t, hT.trans ht.1, v, hv, h⟩
  · rintro a ⟨ha, v, hv, hlt⟩
    by_contra hlt'
    push Not at hlt'
    exact absurd (hmax a ⟨ha.le, hlt'.le⟩ v hv) (not_le.2 hlt)
  · intro w hw
    obtain ⟨t, ht, v, hv, h⟩ := hbeat (w - T) (by linarith)
    exact ⟨t, ⟨hT.trans ht.1, v, hv, h⟩, by linarith [ht.2]⟩

/-- The first control of `F(z)` maximizes the Hamiltonian at `F(z)`. -/
theorem ham_le_of_firstControl_poincare {z : Fin 3 → ℂ} (hz : z ≠ 0) :
    ∀ x ∈ VT, ham (poincare z) x ≤ ham (poincare z) (firstControl (poincare z)) := by
  obtain ⟨-, ε, hε, h⟩ := isFirstControl_firstControl (poincare_ne_zero hz)
  intro x hx
  have := h 0 ⟨le_rfl, hε.le⟩ x hx
  rwa [flow_zero] at this

/-- **The image of a point of the section at a tie lies on the section**: if `u` maximizes the
Hamiltonian at `z ∈ Ξ_{𝒲,0}` and at `w = z(T, z, u) ≠ 0`, where it ties with another control `v`,
then `w ∈ Ξ_{𝒲,0}` (the Hamiltonian is conserved, `ham_flow`, and two maximizers put `w₃` on a
wall, `mem_walls_of_maximizers`). -/
theorem flow_mem_sectionZero {z : Fin 3 → ℂ} (hz : z ∈ sectionZero) {u v : ℂ} (hu : u ∈ VT)
    (hv : v ∈ VT) (huv : u ≠ v) {T : ℝ} (h0 : ∀ x ∈ VT, ham z x ≤ ham z u)
    (hT : ∀ x ∈ VT, ham (flow T z u) x ≤ ham (flow T z u) u)
    (hTv : ham (flow T z u) v = ham (flow T z u) u) (hne : flow T z u ≠ 0) :
    flow T z u ∈ sectionZero := by
  have hle : ∀ (w : Fin 3 → ℂ) (a b : ℂ), ham w a ≤ ham w b → RR (w 2) a ≤ RR (w 2) b := by
    intro w a b h
    simp only [ham, RR_comm (w 2)] at h ⊢
    linarith
  refine ⟨hne, mem_walls_of_maximizers hu hv huv (fun x hx ↦ hle _ _ _ (hT x hx))
    (fun x hx ↦ hle _ _ _ ((hT x hx).trans hTv.ge)), ?_⟩
  rw [hamMax_eq_of_forall_le hu hT, ham_flow, ← hamMax_eq_of_forall_le hu h0]
  exact hz.2.2

/-- `H_F(w, ζ²) - H_F(w, ζ) = -√3 Im w₃`. -/
theorem ham_sq_sub_ham_ζ (w : Fin 3 → ℂ) : ham w (ζ ^ 2) - ham w ζ = -(√3 * (w 2).im) := by
  simp only [ham, RR_eq_re_mul_add_im_mul, ζ_re, ζ_im, ζ_sq_re, ζ_sq_im]
  ring

/-! ### Cell coordinates: the quadratic `q` -/

/-- `y₁ = r₁ sin θ₁ = Im z₁` at `cellPoint p`. -/
noncomputable def cellY₁ (p : Fin 3 → ℝ) : ℝ := (1 - p 0) * Real.sin (p 2 - p 1)

/-- `y₂ = r₂ sin θ₂ = Im z₂` at `cellPoint p`. -/
noncomputable def cellY₂ (p : Fin 3 → ℝ) : ℝ := p 0 * Real.sin (p 2)

/-- The quadratic `q(t) = y₂ + y₁ t/2 + t²/12`: `Im z₃(t) = t q(t)` along `ζ` and along `ζ²`. -/
noncomputable def switchQuad (p : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  cellY₂ p + cellY₁ p * t / 2 + t ^ 2 / 12

/-- The discriminant `9 y₁² - 12 y₂` of `12 q`, normalized (`Δ_{B,1}` up to a positive factor). -/
noncomputable def switchQuadDiscr (p : Fin 3 → ℝ) : ℝ := 9 * cellY₁ p ^ 2 - 12 * cellY₂ p

/-- The smaller root `-3 y₁ - √(9 y₁² - 12 y₂)` of `12 q` (when the discriminant is `≥ 0`). -/
noncomputable def switchQuadLo (p : Fin 3 → ℝ) : ℝ := -3 * cellY₁ p - √(switchQuadDiscr p)

/-- The larger root `-3 y₁ + √(9 y₁² - 12 y₂)` of `12 q`. -/
noncomputable def switchQuadHi (p : Fin 3 → ℝ) : ℝ := -3 * cellY₁ p + √(switchQuadDiscr p)

theorem cellPoint_im_eq (p : Fin 3 → ℝ) :
    (cellPoint p 0).im = cellY₁ p ∧ (cellPoint p 1).im = cellY₂ p ∧ (cellPoint p 2).im = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [cellPoint, Matrix.cons_val_zero, Complex.im_ofReal_mul,
      Complex.exp_ofReal_mul_I_im, cellY₁]
  · simp only [cellPoint, Matrix.cons_val_one, Matrix.cons_val_zero, Complex.im_ofReal_mul,
      Complex.exp_ofReal_mul_I_im, cellY₂]
  · exact Complex.ofReal_im _

/-- `Im z₃(t) = t q(t)` along the controls `ζ` and `ζ²` (`Re u = -1/2`). -/
theorem im_flow_two_cellPoint (p : Fin 3 → ℝ) (t : ℝ) {u : ℂ} (hu : u = ζ ∨ u = ζ ^ 2) :
    (flow t (cellPoint p) u 2).im = t * switchQuad p t := by
  obtain ⟨e0, e1, e2⟩ := cellPoint_im_eq p
  have hre : u.re = -1 / 2 := by rcases hu with rfl | rfl; exacts [ζ_re, ζ_sq_re]
  have f2 : flow t (cellPoint p) u 2 =
      cellPoint p 2 + cellPoint p 1 * t + cellPoint p 0 * t ^ 2 / 2 - I * t ^ 3 * u / 6 := rfl
  rw [f2]
  simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.mul_im, Complex.sub_im,
    Complex.add_im, Complex.div_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, e0, e1, e2, hre, switchQuad]
  norm_num
  ring

/-- `12 q(t) = (t - lo)(t - hi)` when the discriminant is `≥ 0`. -/
theorem twelve_switchQuad {p : Fin 3 → ℝ} (hD : 0 ≤ switchQuadDiscr p) (t : ℝ) :
    12 * switchQuad p t = (t - switchQuadLo p) * (t - switchQuadHi p) := by
  have hs : √(switchQuadDiscr p) ^ 2 = 9 * cellY₁ p ^ 2 - 12 * cellY₂ p := Real.sq_sqrt hD
  unfold switchQuad switchQuadLo switchQuadHi
  linear_combination hs

theorem continuous_cellY₁ : Continuous cellY₁ := by unfold cellY₁; fun_prop

theorem continuous_cellY₂ : Continuous cellY₂ := by unfold cellY₂; fun_prop

theorem continuous_switchQuadDiscr : Continuous switchQuadDiscr := by
  have h1 := continuous_cellY₁
  have h2 := continuous_cellY₂
  unfold switchQuadDiscr
  fun_prop

theorem continuous_switchQuadLo : Continuous switchQuadLo := by
  have h1 := continuous_cellY₁
  have h2 := continuous_switchQuadDiscr.sqrt
  unfold switchQuadLo
  fun_prop

theorem continuous_switchQuadHi : Continuous switchQuadHi := by
  have h1 := continuous_cellY₁
  have h2 := continuous_switchQuadDiscr.sqrt
  unfold switchQuadHi
  fun_prop

theorem continuous_cellPoint : Continuous cellPoint := by
  refine continuous_pi fun j ↦ ?_
  fin_cases j
  · change Continuous fun p : Fin 3 → ℝ ↦ ((1 - p 0 : ℝ) : ℂ) * exp (((p 2 - p 1 : ℝ) : ℂ) * I)
    fun_prop
  · change Continuous fun p : Fin 3 → ℝ ↦ (p 0 : ℂ) * exp ((p 2 : ℂ) * I)
    fun_prop
  · change Continuous fun p : Fin 3 → ℝ ↦ ((-2 * (1 - p 0) * p 0 * Real.sin (p 1) : ℝ) : ℂ)
    fun_prop

/-- The flow is jointly continuous in the time and the initial point. -/
theorem continuous_flow_comp {X : Type*} [TopologicalSpace X] {f : X → ℝ} {g : X → Fin 3 → ℂ}
    (hf : Continuous f) (hg : Continuous g) (u : ℂ) :
    Continuous fun x ↦ flow (f x) (g x) u := by
  refine continuous_pi fun j ↦ ?_
  have h0 : Continuous fun x ↦ g x 0 := (continuous_apply 0).comp hg
  have h1 : Continuous fun x ↦ g x 1 := (continuous_apply 1).comp hg
  have h2 : Continuous fun x ↦ g x 2 := (continuous_apply 2).comp hg
  have hc : Continuous fun x ↦ ((f x : ℝ) : ℂ) := Complex.continuous_ofReal.comp hf
  fin_cases j
  · change Continuous fun x ↦ g x 0 - I * (f x : ℂ) * u
    fun_prop
  · change Continuous fun x ↦ g x 1 + g x 0 * (f x : ℂ) - I * (f x : ℂ) ^ 2 * u / 2
    fun_prop
  · change Continuous fun x ↦ g x 2 + g x 1 * (f x : ℂ) + g x 0 * (f x : ℂ) ^ 2 / 2 -
      I * (f x : ℂ) ^ 3 * u / 6
    fun_prop

/-- Along `ζ` or `ζ²` the flow from a cell point never reaches `0`: `z = z(-T, 0, u)` would have
`Im z₃ = -T³/12`, while `Im z₃ = 0` at a cell point. -/
theorem flow_cellPoint_ne_zero {p : Fin 3 → ℝ} (hp : cellPoint p ≠ 0) {u : ℂ}
    (hu : u = ζ ∨ u = ζ ^ 2) (T : ℝ) : flow T (cellPoint p) u ≠ 0 := by
  intro h
  have hz : cellPoint p = flow (-T) 0 u := by
    rw [← h, ← flow_add, add_neg_cancel, flow_zero]
  have him := congrArg (fun w ↦ (w 2).im) hz
  have hre : u.re = -1 / 2 := by rcases hu with rfl | rfl; exacts [ζ_re, ζ_sq_re]
  simp only [(cellPoint_im_eq p).2.2, flow, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons, Pi.zero_apply, zero_mul, zero_div, add_zero, zero_sub,
    ← Complex.ofReal_pow, Complex.neg_im, Complex.mul_im, Complex.div_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, hre] at him
  have hT : T = 0 := by
    norm_num at him
    exact him
  apply hp
  rw [hz, hT, neg_zero, flow_zero]

/-! ### Signs on the boxes -/

private lemma l15_y₂_nonpos {p : Fin 3 → ℝ} (hp : p ∈ closedBoxTwo) : cellY₂ p ≤ 0 :=
  mul_nonpos_of_nonneg_of_nonpos hp.1.1 (Real.sin_nonpos_of_nonpos_of_neg_pi_le hp.2.2.2 hp.2.2.1)

theorem cellY₂_neg_of_mem_openBoxTwo {p : Fin 3 → ℝ} (hp : p ∈ openBoxTwo) : cellY₂ p < 0 :=
  mul_neg_of_pos_of_neg hp.1.1 (Real.sin_neg_of_neg_of_neg_pi_lt hp.2.2.2 hp.2.2.1)

private lemma l15_y₂_pos {p : Fin 3 → ℝ} (hp : p ∈ openBoxOne) : 0 < cellY₂ p :=
  mul_pos hp.1.1 (Real.sin_pos_of_pos_of_lt_pi hp.2.2.1 hp.2.2.2)

private lemma l15_closedBoxOne_sub {p : Fin 3 → ℝ} (hp : p ∈ closedBoxOne) : p ∈ cellDomain :=
  ⟨hp.1, hp.2.1, ⟨by linarith [hp.2.2.1, Real.pi_pos], hp.2.2.2⟩⟩

theorem mem_cellDomain_of_mem_closedBoxTwo {p : Fin 3 → ℝ} (hp : p ∈ closedBoxTwo) :
    p ∈ cellDomain :=
  ⟨hp.1, hp.2.1, ⟨hp.2.2.1, by linarith [hp.2.2.2, Real.pi_pos]⟩⟩

/-- On the closed second box the discriminant is `≥ 9 y₁²`, so `lo ≤ 0 ≤ hi`. -/
theorem switchQuad_roots_of_mem_closedBoxTwo {p : Fin 3 → ℝ} (hp : p ∈ closedBoxTwo) :
    0 ≤ switchQuadDiscr p ∧ switchQuadLo p ≤ 0 ∧ 0 ≤ switchQuadHi p := by
  have hy := l15_y₂_nonpos hp
  have hD : 9 * cellY₁ p ^ 2 ≤ switchQuadDiscr p := by unfold switchQuadDiscr; linarith
  have hs : |3 * cellY₁ p| ≤ √(switchQuadDiscr p) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith)
  refine ⟨le_trans (by positivity) hD, ?_, ?_⟩
  · unfold switchQuadLo; linarith [neg_abs_le (3 * cellY₁ p)]
  · unfold switchQuadHi; linarith [le_abs_self (3 * cellY₁ p), neg_abs_le (3 * cellY₁ p)]

/-! ### `𝒟₃`: the switch `ζ² → ζ` at `hi` -/

/-- The gain of `1` over `ζ²` along `ζ²` from `cellPoint p`. -/
noncomputable def gainOneSq (p : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  ham (flow t (cellPoint p) (ζ ^ 2)) 1 - ham (flow t (cellPoint p) (ζ ^ 2)) (ζ ^ 2)

/-- The closed set of the second box on which `1` does not beat `ζ²` on `[0, hi]`. -/
def cellTwoNoA : Set (Fin 3 → ℝ) :=
  {p | p ∈ closedBoxTwo ∧ ∀ s ∈ Icc (0 : ℝ) 1, gainOneSq p (s * switchQuadHi p) ≤ 0}

private lemma l15_continuous_gainOneSq (s : ℝ) {f : (Fin 3 → ℝ) → ℝ} (hf : Continuous f) :
    Continuous fun p ↦ gainOneSq p (s * f p) := by
  unfold gainOneSq
  have hw := continuous_flow_comp (continuous_const.mul hf : Continuous fun p ↦ s * f p)
    continuous_cellPoint (ζ ^ 2)
  unfold ham RR
  fun_prop

theorem isClosed_cellTwoNoA : IsClosed cellTwoNoA := by
  have : cellTwoNoA = closedBoxTwo ∩ ⋂ s ∈ Icc (0 : ℝ) 1,
      {p | gainOneSq p (s * switchQuadHi p) ≤ 0} := by
    ext p; simp [cellTwoNoA]
  rw [this]
  exact isClosed_closedBoxTwo.inter (isClosed_biInter fun s _ ↦
    isClosed_le (l15_continuous_gainOneSq s continuous_switchQuadHi) continuous_const)

/-- `H_F(z(t), ζ) - H_F(z(t), ζ²) = √3 t q(t)` along `ζ²`. -/
theorem ham_ζ_sub_ham_sq_flow (p : Fin 3 → ℝ) (t : ℝ) :
    ham (flow t (cellPoint p) (ζ ^ 2)) ζ - ham (flow t (cellPoint p) (ζ ^ 2)) (ζ ^ 2) =
      √3 * (t * switchQuad p t) := by
  have := ham_sq_sub_ham_ζ (flow t (cellPoint p) (ζ ^ 2))
  rw [im_flow_two_cellPoint p t (Or.inr rfl)] at this
  linarith

/-- **The points of the open second box switching to `ζ`** switch at `hi`, and `1` does not beat
`ζ²` before. -/
theorem switchSet_openBoxTwo_ζ_subset : switchSet openBoxTwo ζ ⊆ cellTwoNoA := by
  rintro p ⟨hp, hF⟩
  have hpD : p ∈ cellDomain :=
    mem_cellDomain_of_mem_closedBoxTwo (openBoxTwo_subset_closedBoxTwo hp)
  set z := cellPoint p with hzdef
  have hz : z ≠ 0 := (cellPoint_mem_sectionZero hpD).1
  have hfc : firstControl z = ζ ^ 2 := definition15_1_2.2.2.2.2.2.2.1 p hp
  set T := firstSwitchTime z with hTdef
  have hT : 0 < T := firstSwitchTime_pos hz
  have hmax := firstControl_maximizes hz
  rw [hfc] at hmax
  obtain ⟨hD, hlo, hhi0⟩ := switchQuad_roots_of_mem_closedBoxTwo (openBoxTwo_subset_closedBoxTwo hp)
  -- at `F(z)` the control `ζ` is a maximizer, and before `T` the control `ζ²` is
  have hw : ham (poincare z) (ζ ^ 2) ≤ ham (poincare z) ζ := by
    have := ham_le_of_firstControl_poincare hz (ζ ^ 2) ζ_sq_mem_VT
    rwa [hF] at this
  have hpz : poincare z = flow T z (ζ ^ 2) := by rw [poincare, hfc]
  rw [hpz] at hw
  have hq1 : 0 ≤ switchQuad p T := by
    have := ham_ζ_sub_ham_sq_flow p T
    have h3 : 0 < √3 := by positivity
    have : 0 ≤ √3 * (T * switchQuad p T) := by linarith
    exact nonneg_of_mul_nonneg_right (by nlinarith) hT
  -- so `T ≥ hi`; and `ζ` does not beat `ζ²` on `[0, T]`, so `T ≤ hi`
  have hTq := twelve_switchQuad hD T
  have hThi : T = switchQuadHi p := by
    have hge : switchQuadHi p ≤ T := by
      by_contra h
      push Not at h
      have : (T - switchQuadLo p) * (T - switchQuadHi p) < 0 :=
        mul_neg_of_pos_of_neg (by linarith) (by linarith)
      linarith
    by_contra hne
    have hlt : switchQuadHi p < T := lt_of_le_of_ne hge (Ne.symm hne)
    set t := (switchQuadHi p + T) / 2
    have ht0 : 0 < t := by simp only [t]; linarith
    have hq : 0 < switchQuad p t := by
      have := twelve_switchQuad hD t
      have : 0 < (t - switchQuadLo p) * (t - switchQuadHi p) :=
        mul_pos (by simp only [t]; linarith) (by simp only [t]; linarith)
      linarith
    have h1 := hmax t ⟨ht0.le, by simp only [t]; linarith⟩ ζ ζ_mem_VT
    have h2 := ham_ζ_sub_ham_sq_flow p t
    have h3 : 0 < √3 := by positivity
    nlinarith [mul_pos h3 (mul_pos ht0 hq)]
  refine ⟨openBoxTwo_subset_closedBoxTwo hp, fun s hs ↦ ?_⟩
  have hst : s * switchQuadHi p ∈ Icc 0 T := by
    rw [hThi]
    have hhi := (switchQuad_roots_of_mem_closedBoxTwo (openBoxTwo_subset_closedBoxTwo hp)).2.2
    exact ⟨mul_nonneg hs.1 hhi, by nlinarith [hs.2]⟩
  have := hmax _ hst 1 one_mem_VT
  unfold gainOneSq
  linarith

/-- On `𝒟₃` the control `1` does not beat `ζ²` on `[0, hi]`. -/
theorem partD3_subset_cellTwoNoA : partD3 ⊆ cellTwoNoA :=
  closure_minimal switchSet_openBoxTwo_ζ_subset isClosed_cellTwoNoA

/-- On the closed set `cellTwoNoA` the point `z(hi, cellPoint p, ζ²)` lies on the section. -/
theorem flow_hi_mem_sectionZero {p : Fin 3 → ℝ} (hp : p ∈ cellTwoNoA) :
    flow (switchQuadHi p) (cellPoint p) (ζ ^ 2) ∈ sectionZero := by
  have hpD := mem_cellDomain_of_mem_closedBoxTwo hp.1
  have hz := cellPoint_mem_sectionZero hpD
  obtain ⟨hD, -, -⟩ := switchQuad_roots_of_mem_closedBoxTwo hp.1
  have hqhi : switchQuad p (switchQuadHi p) = 0 := by
    have := twelve_switchQuad hD (switchQuadHi p)
    rw [sub_self, mul_zero] at this
    linarith
  refine flow_mem_sectionZero hz ζ_sq_mem_VT ζ_mem_VT (Ne.symm (by
    intro h
    have := congrArg Complex.im h
    rw [ζ_im, ζ_sq_im] at this
    have h3 : 0 < √3 := by positivity
    linarith)) (fun x hx ↦ ?_) (fun x hx ↦ ?_) ?_
    (flow_cellPoint_ne_zero hz.1 (Or.inr rfl) _)
  · rcases mem_VT.1 hx with rfl | rfl | rfl
    · have := hp.2 0 ⟨le_rfl, zero_le_one⟩
      rw [zero_mul, gainOneSq, flow_zero] at this
      linarith
    · have := ham_ζ_sub_ham_sq_flow p 0
      rw [flow_zero] at this
      linarith
    · exact le_rfl
  · rcases mem_VT.1 hx with rfl | rfl | rfl
    · have := hp.2 1 ⟨zero_le_one, le_rfl⟩
      rw [one_mul, gainOneSq] at this
      linarith
    · have := ham_ζ_sub_ham_sq_flow p (switchQuadHi p)
      rw [hqhi, mul_zero, mul_zero] at this
      linarith
    · exact le_rfl
  · have := ham_ζ_sub_ham_sq_flow p (switchQuadHi p)
    rw [hqhi, mul_zero, mul_zero] at this
    linarith

/-- **The extension `F₃`**: the class of `z(hi, cellPoint p, ζ²)`. -/
noncomputable def extD3 (p : Fin 3 → ℝ) : XiW0Quot :=
  classOf (flow (switchQuadHi p) (cellPoint p) (ζ ^ 2))

/-- **`F₃` is continuous on `𝒟₃`.** -/
theorem continuousOn_extD3 : ContinuousOn extD3 partD3 :=
  continuousOn_classOf.comp
    (continuous_flow_comp continuous_switchQuadHi continuous_cellPoint _).continuousOn
    fun _ hp ↦ flow_hi_mem_sectionZero (partD3_subset_cellTwoNoA hp)

/-- **The first switch on `cellTwoNoA ∩ openBoxTwo`** is at `hi`, from `ζ²`: `ζ²` is optimal on
`[0, hi]` (`1` by `cellTwoNoA`, `ζ` because `q ≤ 0` there) and `ζ` beats it right after `hi`. -/
theorem firstSwitchTime_of_mem_cellTwoNoA {p : Fin 3 → ℝ} (hA : p ∈ cellTwoNoA)
    (hp' : p ∈ openBoxTwo) :
    firstControl (cellPoint p) = ζ ^ 2 ∧ firstSwitchTime (cellPoint p) = switchQuadHi p := by
  have hpD := mem_cellDomain_of_mem_closedBoxTwo hA.1
  have hz := cellPoint_mem_sectionZero hpD
  obtain ⟨hD, hlo, hhi0⟩ := switchQuad_roots_of_mem_closedBoxTwo hA.1
  have hhi : 0 < switchQuadHi p := by
    have hy := cellY₂_neg_of_mem_openBoxTwo hp'
    rcases hhi0.lt_or_eq with h | h
    · exact h
    · exfalso
      have := twelve_switchQuad hD 0
      rw [← h, sub_self, mul_zero] at this
      unfold switchQuad at this
      linarith
  have h3 : 0 < √3 := by positivity
  have hmax : ∀ t ∈ Icc 0 (switchQuadHi p), ∀ v ∈ VT,
      ham (flow t (cellPoint p) (ζ ^ 2)) v ≤ ham (flow t (cellPoint p) (ζ ^ 2)) (ζ ^ 2) := by
    intro t ht v hv
    rcases mem_VT.1 hv with rfl | rfl | rfl
    · have := hA.2 (t / switchQuadHi p) ⟨div_nonneg ht.1 hhi.le, (div_le_one hhi).2 ht.2⟩
      rw [div_mul_cancel₀ _ hhi.ne', gainOneSq] at this
      linarith
    · have hq : switchQuad p t ≤ 0 := by
        have := twelve_switchQuad hD t
        have : (t - switchQuadLo p) * (t - switchQuadHi p) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by linarith [ht.1]) (by linarith [ht.2])
        linarith
      have := ham_ζ_sub_ham_sq_flow p t
      nlinarith [mul_nonpos_of_nonneg_of_nonpos ht.1 hq]
    · exact le_rfl
  have hbeat : ∀ ε > 0, ∃ t ∈ Ioo (switchQuadHi p) (switchQuadHi p + ε), ∃ v ∈ VT,
      ham (flow t (cellPoint p) (ζ ^ 2)) (ζ ^ 2) < ham (flow t (cellPoint p) (ζ ^ 2)) v := by
    intro ε hε
    refine ⟨switchQuadHi p + ε / 2, ⟨by linarith, by linarith⟩, ζ, ζ_mem_VT, ?_⟩
    have hq : 0 < switchQuad p (switchQuadHi p + ε / 2) := by
      have := twelve_switchQuad hD (switchQuadHi p + ε / 2)
      have : 0 < (switchQuadHi p + ε / 2 - switchQuadLo p) *
          (switchQuadHi p + ε / 2 - switchQuadHi p) := mul_pos (by linarith) (by linarith)
      linarith
    have := ham_ζ_sub_ham_sq_flow p (switchQuadHi p + ε / 2)
    nlinarith [mul_pos h3 (mul_pos (by linarith : 0 < switchQuadHi p + ε / 2) hq)]
  exact firstSwitchTime_eq_of hz.1 ζ_sq_mem_VT hhi hmax hbeat

/-- **`F₃ = F` on `𝒟₃ ∩ openBoxTwo`**, in particular on the interior of `𝒟₃`
(`firstSwitchTime_of_mem_cellTwoNoA`). -/
theorem extD3_eq {p : Fin 3 → ℝ} (hp : p ∈ partD3) (hp' : p ∈ openBoxTwo) :
    extD3 p = poincareAngZero (cellClass p) := by
  have hA := partD3_subset_cellTwoNoA hp
  have hz := cellPoint_mem_sectionZero (mem_cellDomain_of_mem_closedBoxTwo hA.1)
  obtain ⟨hfc, hT⟩ := firstSwitchTime_of_mem_cellTwoNoA hA hp'
  rw [extD3, cellClass, poincareAngZero_classOf hz, poincare, hfc, hT]


/-! ### `𝒟₄`: the switch `ζ → ζ²` at `lo` -/

/-- The gain of `1` over `ζ` along `ζ` from `cellPoint p`. -/
noncomputable def gainOneZeta (p : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  ham (flow t (cellPoint p) ζ) 1 - ham (flow t (cellPoint p) ζ) ζ

/-- The closed set of the first box on which `q` has real roots, `y₁ ≤ 0`, and `1` does not beat
`ζ` on `[0, lo]`. -/
def cellOneNoA : Set (Fin 3 → ℝ) :=
  {p | p ∈ closedBoxOne ∧ 0 ≤ switchQuadDiscr p ∧ cellY₁ p ≤ 0 ∧
    ∀ s ∈ Icc (0 : ℝ) 1, gainOneZeta p (s * switchQuadLo p) ≤ 0}

private lemma l15_continuous_gainOneZeta (s : ℝ) {f : (Fin 3 → ℝ) → ℝ} (hf : Continuous f) :
    Continuous fun p ↦ gainOneZeta p (s * f p) := by
  unfold gainOneZeta
  have hw := continuous_flow_comp (continuous_const.mul hf : Continuous fun p ↦ s * f p)
    continuous_cellPoint ζ
  unfold ham RR
  fun_prop

theorem isClosed_cellOneNoA : IsClosed cellOneNoA := by
  have : cellOneNoA = closedBoxOne ∩ {p | 0 ≤ switchQuadDiscr p} ∩ {p | cellY₁ p ≤ 0} ∩
      ⋂ s ∈ Icc (0 : ℝ) 1, {p | gainOneZeta p (s * switchQuadLo p) ≤ 0} := by
    ext p
    simp only [cellOneNoA, mem_inter_iff, mem_ofPred_eq, mem_iInter]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      exact ⟨h1, h2, h3, h4⟩
  rw [this]
  exact ((isClosed_closedBoxOne.inter
    (isClosed_le continuous_const continuous_switchQuadDiscr)).inter
    (isClosed_le continuous_cellY₁ continuous_const)).inter (isClosed_biInter fun s _ ↦
    isClosed_le (l15_continuous_gainOneZeta s continuous_switchQuadLo) continuous_const)

/-- `H_F(z(t), ζ²) - H_F(z(t), ζ) = -√3 t q(t)` along `ζ`. -/
private lemma l15_gainSq_ζ (p : Fin 3 → ℝ) (t : ℝ) :
    ham (flow t (cellPoint p) ζ) (ζ ^ 2) - ham (flow t (cellPoint p) ζ) ζ =
      -(√3 * (t * switchQuad p t)) := by
  rw [ham_sq_sub_ham_ζ, im_flow_two_cellPoint p t (Or.inl rfl)]

private lemma l15_ζ_ne_ζ_sq : ζ ≠ ζ ^ 2 := by
  intro h
  have := congrArg Complex.im h
  rw [ζ_im, ζ_sq_im] at this
  have h3 : 0 < √3 := by positivity
  linarith

/-- **The points of the open first box switching to `ζ²`** switch at the smaller root `lo` of `q`
(which then has real roots, with `y₁ < 0`), and `1` does not beat `ζ` before. -/
theorem switchSet_openBoxOne_sq_subset : switchSet openBoxOne (ζ ^ 2) ⊆ cellOneNoA := by
  rintro p ⟨hp, hF⟩
  have hpD : p ∈ cellDomain := l15_closedBoxOne_sub (openBoxOne_subset_closedBoxOne hp)
  set z := cellPoint p with hzdef
  have hz : z ≠ 0 := (cellPoint_mem_sectionZero hpD).1
  have hfc : firstControl z = ζ := definition15_1_2.2.2.2.2.2.1 p hp
  set T := firstSwitchTime z with hTdef
  have hT : 0 < T := firstSwitchTime_pos hz
  have hmax := firstControl_maximizes hz
  rw [hfc] at hmax
  have h3 : 0 < √3 := by positivity
  have hy2 := l15_y₂_pos hp
  -- `q ≥ 0` on `(0, T]` (`ζ²` does not beat `ζ`), and `q(T) ≤ 0` (`ζ²` is optimal at `F(z)`)
  have hqpos : ∀ t ∈ Ioc 0 T, 0 ≤ switchQuad p t := by
    intro t ht
    have h1 := hmax t ⟨ht.1.le, ht.2⟩ (ζ ^ 2) ζ_sq_mem_VT
    have h2 := l15_gainSq_ζ p t
    have : 0 ≤ √3 * (t * switchQuad p t) := by linarith
    exact nonneg_of_mul_nonneg_right (by nlinarith) ht.1
  have hw : ham (poincare z) ζ ≤ ham (poincare z) (ζ ^ 2) := by
    have := ham_le_of_firstControl_poincare hz ζ ζ_mem_VT
    rwa [hF] at this
  have hpz : poincare z = flow T z ζ := by rw [poincare, hfc]
  rw [hpz] at hw
  have hqT : switchQuad p T = 0 := by
    have h2 := l15_gainSq_ζ p T
    have hle : T * switchQuad p T ≤ 0 := by nlinarith
    have : switchQuad p T ≤ 0 := by
      by_contra h
      push Not at h
      nlinarith [mul_pos hT h]
    exact le_antisymm this (hqpos T ⟨hT, le_rfl⟩)
  have hq12 : T ^ 2 + 6 * cellY₁ p * T + 12 * cellY₂ p = 0 := by
    unfold switchQuad at hqT; linarith
  have hD : 0 ≤ switchQuadDiscr p := by
    have : switchQuadDiscr p = (T + 3 * cellY₁ p) ^ 2 := by
      unfold switchQuadDiscr; linear_combination (-1 : ℝ) * hq12
    rw [this]; positivity
  have hy1 : cellY₁ p < 0 := by nlinarith
  have hTq := twelve_switchQuad hD T
  have hlohi : switchQuadLo p ≤ switchQuadHi p := by
    unfold switchQuadLo switchQuadHi; linarith [Real.sqrt_nonneg (switchQuadDiscr p)]
  have hprod : switchQuadLo p * switchQuadHi p = 12 * cellY₂ p := by
    have := twelve_switchQuad hD 0
    unfold switchQuad at this
    linarith
  have hsum : switchQuadLo p + switchQuadHi p = -6 * cellY₁ p := by
    unfold switchQuadLo switchQuadHi; ring
  have hlo0 : 0 < switchQuadLo p := by
    by_contra h
    push Not at h
    nlinarith
  have hTlo : T = switchQuadLo p := by
    have h0 : (T - switchQuadLo p) * (T - switchQuadHi p) = 0 := by rw [← hTq, hqT, mul_zero]
    rcases mul_eq_zero.1 h0 with h | h
    · linarith
    · by_contra hne
      have hlt : switchQuadLo p < T := lt_of_le_of_ne (by linarith) (Ne.symm hne)
      set t := (switchQuadLo p + T) / 2
      have hq : switchQuad p t < 0 := by
        have := twelve_switchQuad hD t
        have : (t - switchQuadLo p) * (t - switchQuadHi p) < 0 :=
          mul_neg_of_pos_of_neg (by simp only [t]; linarith) (by simp only [t]; linarith)
        linarith
      have := hqpos t ⟨by simp only [t]; linarith, by simp only [t]; linarith⟩
      linarith
  refine ⟨openBoxOne_subset_closedBoxOne hp, hD, hy1.le, fun s hs ↦ ?_⟩
  have hst : s * switchQuadLo p ∈ Icc 0 T := by
    rw [hTlo]
    exact ⟨mul_nonneg hs.1 hlo0.le, by nlinarith [hs.2]⟩
  have := hmax _ hst 1 one_mem_VT
  unfold gainOneZeta
  linarith

/-- On `𝒟₄`, `q` has real roots, `y₁ ≤ 0`, and `1` does not beat `ζ` on `[0, lo]`. -/
theorem partD4_subset_cellOneNoA : partD4 ⊆ cellOneNoA :=
  closure_minimal switchSet_openBoxOne_sq_subset isClosed_cellOneNoA

/-- On `cellOneNoA` the point `z(lo, cellPoint p, ζ)` lies on the section. -/
theorem flow_lo_mem_sectionZero {p : Fin 3 → ℝ} (hp : p ∈ cellOneNoA) :
    flow (switchQuadLo p) (cellPoint p) ζ ∈ sectionZero := by
  have hpD := l15_closedBoxOne_sub hp.1
  have hz := cellPoint_mem_sectionZero hpD
  have hqlo : switchQuad p (switchQuadLo p) = 0 := by
    have := twelve_switchQuad hp.2.1 (switchQuadLo p)
    rw [sub_self, zero_mul] at this
    linarith
  refine flow_mem_sectionZero hz ζ_mem_VT ζ_sq_mem_VT l15_ζ_ne_ζ_sq (fun x hx ↦ ?_)
    (fun x hx ↦ ?_) ?_ (flow_cellPoint_ne_zero hz.1 (Or.inl rfl) _)
  · rcases mem_VT.1 hx with rfl | rfl | rfl
    · have := hp.2.2.2 0 ⟨le_rfl, zero_le_one⟩
      rw [zero_mul, gainOneZeta, flow_zero] at this
      linarith
    · exact le_rfl
    · have := l15_gainSq_ζ p 0
      rw [flow_zero] at this
      linarith
  · rcases mem_VT.1 hx with rfl | rfl | rfl
    · have := hp.2.2.2 1 ⟨zero_le_one, le_rfl⟩
      rw [one_mul, gainOneZeta] at this
      linarith
    · exact le_rfl
    · have := l15_gainSq_ζ p (switchQuadLo p)
      rw [hqlo, mul_zero, mul_zero, neg_zero] at this
      linarith
  · have := l15_gainSq_ζ p (switchQuadLo p)
    rw [hqlo, mul_zero, mul_zero, neg_zero] at this
    linarith

/-- **The extension `F₄`**: the class of `z(lo, cellPoint p, ζ)`. -/
noncomputable def extD4 (p : Fin 3 → ℝ) : XiW0Quot :=
  classOf (flow (switchQuadLo p) (cellPoint p) ζ)

/-- **`F₄` is continuous on `𝒟₄`.** -/
theorem continuousOn_extD4 : ContinuousOn extD4 partD4 :=
  continuousOn_classOf.comp
    (continuous_flow_comp continuous_switchQuadLo continuous_cellPoint _).continuousOn
    fun _ hp ↦ flow_lo_mem_sectionZero (partD4_subset_cellOneNoA hp)

/-- `sin² (u₀ + s) - sin² u₀ = sin (2 u₀ + s) sin s`. -/
private lemma l15_sin_sq_sub (u s : ℝ) :
    Real.sin (u + s) ^ 2 - Real.sin u ^ 2 = Real.sin (2 * u + s) * Real.sin s := by
  rw [Real.sin_add, Real.sin_add, Real.sin_two_mul, Real.cos_two_mul]
  linear_combination (Real.sin u ^ 2) * Real.sin_sq_add_cos_sq s -
    (Real.sin s ^ 2) * Real.sin_sq_add_cos_sq u

/-- Near a point with `sin u₀ ≠ 0` there are points with a smaller `sin²`. -/
private lemma l15_exists_sin_sq_lt {u : ℝ} (hu : Real.sin u ≠ 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ s, |s| < δ ∧ Real.sin (u + s) ^ 2 < Real.sin u ^ 2 := by
  have hpi := Real.two_le_pi
  rcases lt_trichotomy (Real.sin (2 * u)) 0 with h | h | h
  · -- `s > 0` small: `sin s > 0`, `sin (2u + s) < 0`
    have hc : ContinuousAt (fun s ↦ Real.sin (2 * u + s)) 0 := by fun_prop
    obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.1
      (hc.eventually (gt_mem_nhds (by simpa using h)))
    set s := min (min δ η) 1 / 2 with hs
    have hs0 : 0 < s := by positivity
    have hs1 : s < δ := by
      have := min_le_left (min δ η) 1; have := min_le_left δ η; simp only [hs]; linarith
    have hs2 : s < η := by
      have := min_le_left (min δ η) 1; have := min_le_right δ η; simp only [hs]; linarith
    have hs3 : s < π := by have := min_le_right (min δ η) 1; simp only [hs]; linarith
    refine ⟨s, by rw [abs_of_pos hs0]; exact hs1, ?_⟩
    have h1 : Real.sin (2 * u + s) < 0 :=
      hball (by rw [Real.dist_eq, sub_zero, abs_of_pos hs0]; exact hs2)
    have h2 : 0 < Real.sin s := Real.sin_pos_of_pos_of_lt_pi hs0 hs3
    have := l15_sin_sq_sub u s
    nlinarith [mul_neg_of_neg_of_pos h1 h2]
  · -- `cos u = 0`: `sin² (u + s) = sin² u cos² s`
    have hcos : Real.cos u = 0 := by
      rw [Real.sin_two_mul] at h
      rcases mul_eq_zero.1 h with h' | h'
      · exact absurd (by linarith : Real.sin u = 0) hu
      · exact h'
    set s := min δ 1 / 2 with hs
    have hs0 : 0 < s := by positivity
    have hs1 : s < δ := by have := min_le_left δ 1; simp only [hs]; linarith
    have hs3 : s < π := by have := min_le_right δ 1; simp only [hs]; linarith
    refine ⟨s, by rw [abs_of_pos hs0]; exact hs1, ?_⟩
    have h2 : 0 < Real.sin s := Real.sin_pos_of_pos_of_lt_pi hs0 hs3
    rw [Real.sin_add, hcos, zero_mul, add_zero]
    have hc2 : Real.cos s ^ 2 = 1 - Real.sin s ^ 2 := by linarith [Real.sin_sq_add_cos_sq s]
    have hu2 : 0 < Real.sin u ^ 2 := by positivity
    nlinarith [mul_pos hu2 (pow_pos h2 2)]
  · -- `s < 0` small: `sin s < 0`, `sin (2u + s) > 0`
    have hc : ContinuousAt (fun s ↦ Real.sin (2 * u + s)) 0 := by fun_prop
    obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.1
      (hc.eventually (lt_mem_nhds (by simpa using h)))
    set s := min (min δ η) 1 / 2 with hs
    have hs0 : 0 < s := by positivity
    have hs1 : s < δ := by
      have := min_le_left (min δ η) 1; have := min_le_left δ η; simp only [hs]; linarith
    have hs2 : s < η := by
      have := min_le_left (min δ η) 1; have := min_le_right δ η; simp only [hs]; linarith
    have hs3 : s < π := by have := min_le_right (min δ η) 1; simp only [hs]; linarith
    refine ⟨-s, by rw [abs_neg, abs_of_pos hs0]; exact hs1, ?_⟩
    have h1 : 0 < Real.sin (2 * u + -s) :=
      hball (by rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos hs0]; exact hs2)
    have h2 : 0 < Real.sin s := Real.sin_pos_of_pos_of_lt_pi hs0 hs3
    have := l15_sin_sq_sub u (-s)
    rw [Real.sin_neg] at this
    nlinarith [mul_pos h1 h2]

/-- **The discriminant of `q` is not locally minimal at `0`**: a point of the open first box with
`9 y₁² = 12 y₂` is a limit of points of the open box with `9 y₁² < 12 y₂` (moving `ψ`; `y₂` does
not depend on `ψ` and `y₁ = r₁ sin(θ₂ - ψ) ≠ 0`). -/
theorem exists_switchQuadDiscr_neg {p : Fin 3 → ℝ} (hp : p ∈ openBoxOne)
    (hD : switchQuadDiscr p = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ p' ∈ openBoxOne, dist p' p < ε ∧ switchQuadDiscr p' < 0 := by
  have hy2 := l15_y₂_pos hp
  have hr1 : 0 < 1 - p 0 := by linarith [hp.1.2]
  have hsin : Real.sin (p 2 - p 1) ≠ 0 := by
    intro h
    unfold switchQuadDiscr cellY₁ at hD
    rw [h, mul_zero] at hD
    linarith
  obtain ⟨s, hs, hlt⟩ := l15_exists_sin_sq_lt hsin
    (lt_min (lt_min hε hp.2.1.1) (by linarith [hp.2.1.2]) : 0 < min (min ε (p 1)) (π - p 1))
  have hs1 : |s| < ε := hs.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hs2 : |s| < p 1 := hs.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hs3 : |s| < π - p 1 := hs.trans_le (min_le_right _ _)
  set p' := Function.update p 1 (p 1 - s) with hp'
  have e0 : p' 0 = p 0 := Function.update_of_ne (by decide) _ _
  have e1 : p' 1 = p 1 - s := Function.update_self _ _ _
  have e2 : p' 2 = p 2 := Function.update_of_ne (by decide) _ _
  refine ⟨p', ⟨by rw [e0]; exact hp.1, ?_, by rw [e2]; exact hp.2.2⟩, ?_, ?_⟩
  · rw [e1]
    constructor <;> linarith [le_abs_self s, neg_abs_le s]
  · refine lt_of_le_of_lt ((dist_pi_le_iff (abs_nonneg s)).2 fun i ↦ ?_) hs1
    by_cases hi : i = 1
    · subst hi
      rw [e1, Real.dist_eq, show p 1 - s - p 1 = -s by ring, abs_neg]
    · rw [hp', Function.update_of_ne hi, dist_self]
      exact abs_nonneg s
  · have hy1' : cellY₁ p' = (1 - p 0) * Real.sin (p 2 - p 1 + s) := by
      unfold cellY₁; rw [e0, e1, e2]; ring_nf
    have hy2' : cellY₂ p' = cellY₂ p := by unfold cellY₂; rw [e0, e2]
    unfold switchQuadDiscr at hD ⊢
    rw [hy1', hy2']
    unfold cellY₁ at hD
    have hr : 0 < (1 - p 0) ^ 2 := by positivity
    nlinarith [mul_lt_mul_of_pos_left hlt hr]

/-- On the interior of `𝒟₄` the two roots of `q` are distinct: otherwise points with
`9 y₁² < 12 y₂` (`q > 0`, never switching to `ζ²`) would fill an open subset of `𝒟₄`. -/
theorem switchQuadDiscr_pos_of_mem_interior {p : Fin 3 → ℝ} (hp : p ∈ interior partD4) :
    0 < switchQuadDiscr p := by
  have hp1 : p ∈ openBoxOne := interior_subset_openBoxOne partD4_subset hp
  have hA := partD4_subset_cellOneNoA (interior_subset hp)
  rcases hA.2.1.lt_or_eq with h | h
  · exact h
  exfalso
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (isOpen_interior.mem_nhds hp)
  obtain ⟨p', -, hp'd, hp'D⟩ := exists_switchQuadDiscr_neg hp1 h.symm hε
  have hp'4 : p' ∈ partD4 := interior_subset (hball hp'd)
  have hopen : IsOpen {q | switchQuadDiscr q < 0} := isOpen_lt continuous_switchQuadDiscr
    continuous_const
  obtain ⟨q, hq, hqS⟩ := mem_closure_iff.1 hp'4 _ hopen hp'D
  exact absurd (switchSet_openBoxOne_sq_subset hqS).2.1 (not_le.2 hq)

/-- **`F₄ = F` on the interior of `𝒟₄`**: `ζ` is optimal on `[0, lo]` (`1` by `cellOneNoA`, `ζ²`
because `q ≥ 0` there) and `ζ²` beats it right after `lo < hi`. -/
theorem extD4_eq {p : Fin 3 → ℝ} (hp : p ∈ interior partD4) :
    extD4 p = poincareAngZero (cellClass p) := by
  have hp1 : p ∈ openBoxOne := interior_subset_openBoxOne partD4_subset hp
  have hA := partD4_subset_cellOneNoA (interior_subset hp)
  have hD := switchQuadDiscr_pos_of_mem_interior hp
  have hz := cellPoint_mem_sectionZero (l15_closedBoxOne_sub hA.1)
  have hy2 := l15_y₂_pos hp1
  have h3 : 0 < √3 := by positivity
  have hsq : 0 < √(switchQuadDiscr p) := Real.sqrt_pos.2 hD
  have hlohi : switchQuadLo p < switchQuadHi p := by
    unfold switchQuadLo switchQuadHi; linarith
  have hprod : switchQuadLo p * switchQuadHi p = 12 * cellY₂ p := by
    have := twelve_switchQuad hD.le 0
    unfold switchQuad at this
    linarith
  have hsum : switchQuadLo p + switchQuadHi p = -6 * cellY₁ p := by
    unfold switchQuadLo switchQuadHi; ring
  have hlo0 : 0 < switchQuadLo p := by
    by_contra h
    push Not at h
    have hy1 := hA.2.2.1
    nlinarith
  have hmax : ∀ t ∈ Icc 0 (switchQuadLo p), ∀ v ∈ VT,
      ham (flow t (cellPoint p) ζ) v ≤ ham (flow t (cellPoint p) ζ) ζ := by
    intro t ht v hv
    rcases mem_VT.1 hv with rfl | rfl | rfl
    · have := hA.2.2.2 (t / switchQuadLo p) ⟨div_nonneg ht.1 hlo0.le, (div_le_one hlo0).2 ht.2⟩
      rw [div_mul_cancel₀ _ hlo0.ne', gainOneZeta] at this
      linarith
    · exact le_rfl
    · have hq : 0 ≤ switchQuad p t := by
        have := twelve_switchQuad hD.le t
        have : 0 ≤ (t - switchQuadLo p) * (t - switchQuadHi p) :=
          mul_nonneg_of_nonpos_of_nonpos (by linarith [ht.2]) (by linarith [ht.2])
        linarith
      have := l15_gainSq_ζ p t
      nlinarith [mul_nonneg ht.1 hq]
  have hbeat : ∀ ε > 0, ∃ t ∈ Ioo (switchQuadLo p) (switchQuadLo p + ε), ∃ v ∈ VT,
      ham (flow t (cellPoint p) ζ) ζ < ham (flow t (cellPoint p) ζ) v := by
    intro ε hε
    set t := switchQuadLo p + min ε (switchQuadHi p - switchQuadLo p) / 2 with ht
    have hm1 := min_le_left ε (switchQuadHi p - switchQuadLo p)
    have hm2 := min_le_right ε (switchQuadHi p - switchQuadLo p)
    have hm0 : 0 < min ε (switchQuadHi p - switchQuadLo p) := lt_min hε (by linarith)
    refine ⟨t, ⟨by simp only [ht]; linarith, by simp only [ht]; linarith⟩, ζ ^ 2, ζ_sq_mem_VT, ?_⟩
    have hq : switchQuad p t < 0 := by
      have := twelve_switchQuad hD.le t
      have : (t - switchQuadLo p) * (t - switchQuadHi p) < 0 :=
        mul_neg_of_pos_of_neg (by simp only [ht]; linarith) (by simp only [ht]; linarith)
      linarith
    have := l15_gainSq_ζ p t
    have ht0 : 0 < t := by simp only [ht]; linarith
    nlinarith [mul_neg_of_pos_of_neg ht0 hq]
  obtain ⟨hfc, hT⟩ := firstSwitchTime_eq_of hz.1 ζ_mem_VT hlo0 hmax hbeat
  rw [extD4, cellClass, poincareAngZero_classOf hz, poincare, hfc, hT]


end TriFuller

end SmoothedPolygons
