module

public import SmoothedPolygons.Ch13.Blowup
public import SmoothedPolygons.Ch13.Extremals
import Mathlib.Basic.Real.Pointwise
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Algebra.MulAction

/-!
# Chapter 13: the Fuller–Poincaré map

§13.5 of Hales–Vajjha, *Packings of Smoothed Polygons* ("Dynamical System and Equilibrium
Points", TeX 11234–11290, 11429–11431):

* the Poincaré map `F(z⁰) = z(t_sw)` along the extremal from `z⁰` with the control given by the
  maximum principle, up to the first switching time (`poincare`, TeX 11236–11251). It is defined
  at every point (see `SmoothedPolygons/Ch13/Defs.lean` on robustness); on the section
  `(ℂ³ ∖ 0)_𝒲` it is well defined in the book's sense: `0 < t_sw < 10 φ(z⁰)` (Lemma 13.2.6,
  Corollary 13.2.7), `F(z⁰) ≠ 0` (Lemma 13.3.1; in fact for every `z⁰ ≠ 0`,
  `flow_firstControl_ne_zero`) and `F(z⁰)₃ ∈ 𝒲`; these uses are silent in the book
  (REPORT.md, E67);
* the equivariance of `F` under `V_T` (Lemma 13.2.2, (13.2.7)) and under rescaling (Lemma 13.2.1),
  so that `F` descends to `(ℝ_{>0} × Ξ)_𝒲/V_T` and induces `F_ang` on `Ξ_𝒲` (`poincareAng`) and on
  `Ξ_𝒲/V_T` (`poincareAngQuot`) (TeX 11251–11275);
* the constancy of the Hamiltonian, so that `F` restricts to the zero set of `H_F⁺` (TeX
  11429–11431): the set `Ξ_{𝒲,0}/V_T` (`XiW0Quot`, which the book never defines formally; Remark
  13.5.1 and Lemma 13.5.5 describe it in words) and the restricted map `poincareAngZero`. On a wall
  two controls tie and give the same value of `H_F`, and the first control maximizes `H_F`, so the
  Hamiltonian at a point of the section is `H_F⁺` (`hamMax`);
* the time reversal `τ` on these spaces, with `F(τ F(z⁰)) = τ(z⁰)` when `z⁰` is a genuine switching
  point (the identity `F⁻¹ = τ F τ` of Chapter 15, from Lemmas 13.2.3 and 13.2.5).

Remark 13.5.1 (TeX 11277–11288) only fixes the notation `F` for these maps and their domains.
-/

@[expose] public section

namespace SmoothedPolygons

open Complex Set Filter Topology

namespace TriFuller

/-! ### Helpers -/

/-- Comparing two values of the Hamiltonian at one point compares the switching terms. -/
private lemma l4h_ham_le_iff (w : Fin 3 → ℂ) (x y : ℂ) :
    ham w x ≤ ham w y ↔ RR (w 2) x ≤ RR (w 2) y := by
  unfold ham
  rw [RR_comm x (w 2), RR_comm y (w 2), add_le_add_iff_left]

private lemma l4h_ne_zero_of_mem_VT {v : ℂ} (hv : v ∈ VT) : v ≠ 0 := by
  intro h
  have := norm_eq_one_of_mem_VT hv
  rw [h, norm_zero] at this
  exact zero_ne_one this

private lemma l4h_inv_mul_mem_VT {u v : ℂ} (hu : u ∈ VT) (hv : v ∈ VT) : u⁻¹ * v ∈ VT := by
  rw [inv_eq_conj_of_mem_VT hu]
  exact mul_mem_VT (conj_mem_VT hu) hv

/-- The maximum `H_F⁺(z)` is attained at a vertex. -/
private lemma l4h_exists_ham_eq_hamMax (w : Fin 3 → ℂ) : ∃ v ∈ VT, ham w v = hamMax w := by
  unfold hamMax
  rcases max_choice (ham w 1) (max (ham w ζ) (ham w (ζ ^ 2))) with h | h
  · exact ⟨1, one_mem_VT, h.symm⟩
  · rcases max_choice (ham w ζ) (ham w (ζ ^ 2)) with h' | h'
    · exact ⟨ζ, ζ_mem_VT, by rw [h, h']⟩
    · exact ⟨ζ ^ 2, by simp [VT], by rw [h, h']⟩

/-- A value of `H_F` at a vertex that bounds the others is `H_F⁺`. -/
private lemma l4h_hamMax_eq {w : Fin 3 → ℂ} {M : ℝ} (h₁ : ∀ v ∈ VT, ham w v ≤ M)
    (h₂ : ∃ v ∈ VT, ham w v = M) : hamMax w = M := by
  obtain ⟨v, hv, rfl⟩ := h₂
  refine le_antisymm ?_ (ham_le_hamMax w hv)
  exact max_le (h₁ 1 one_mem_VT) (max_le (h₁ ζ ζ_mem_VT) (h₁ _ (by simp [VT])))

/-- `H_F(v z, x) = H_F(z, v⁻¹ x)` for `v ∈ V_T` (`ham_smul_scale` with `r = 1`). -/
private lemma l4h_ham_smul {v : ℂ} (hv : v ∈ VT) (w : Fin 3 → ℂ) (x : ℂ) :
    ham (v • w) x = ham w (v⁻¹ * x) := by
  have h := ham_smul_scale (norm_eq_one_of_mem_VT hv) 1 w (v⁻¹ * x)
  rwa [scale_one, mul_inv_cancel_left₀ (l4h_ne_zero_of_mem_VT hv), one_pow, one_mul] at h

/-- `H_F(r z₁, r² z₂, r³ z₃; x) = r³ H_F(z, x)` (`ham_smul_scale` with `v = 1`). -/
private lemma l4h_ham_scale (r : ℝ) (w : Fin 3 → ℂ) (x : ℂ) :
    ham (scale r w) x = r ^ 3 * ham w x := by
  simpa using ham_smul_scale (v := 1) (by simp) r w x

private lemma l4h_flow_smul (t : ℝ) (v : ℂ) (z : Fin 3 → ℂ) (u : ℂ) :
    flow t (v • z) (v * u) = v • flow t z u := by
  funext j; fin_cases j <;> simp [flow] <;> ring

private lemma l4h_flow_scale (r t : ℝ) (z : Fin 3 → ℂ) (u : ℂ) :
    flow (r * t) (scale r z) u = scale r (flow t z u) := by
  funext j; fin_cases j <;> simp [flow, scale] <;> ring

private lemma l4h_continuous_flow (z : Fin 3 → ℂ) (u : ℂ) : Continuous fun t ↦ flow t z u :=
  continuous_iff_continuousAt.2 fun t ↦ (hasDerivAt_flow t z u).continuousAt

private lemma l4h_continuous_ham (v : ℂ) : Continuous fun w : Fin 3 → ℂ ↦ ham w v := by
  unfold ham RR
  fun_prop

private lemma l4h_continuous_ham_flow (z : Fin 3 → ℂ) (u v : ℂ) :
    Continuous fun t ↦ ham (flow t z u) v :=
  (l4h_continuous_ham v).comp (l4h_continuous_flow z u)

private lemma l4h_continuous_hamMax : Continuous hamMax :=
  (l4h_continuous_ham 1).max ((l4h_continuous_ham ζ).max (l4h_continuous_ham _))

private lemma l4h_tau_smul (c : ℂ) (z : Fin 3 → ℂ) : tau (c • z) = starRingEnd ℂ c • tau z := by
  funext j; fin_cases j <;> simp [tau]

private lemma l4h_continuous_tau : Continuous tau := by
  refine continuous_pi fun j ↦ ?_
  fin_cases j
  · exact Complex.continuous_conj.comp (continuous_apply 0)
  · exact (Complex.continuous_conj.comp (continuous_apply 1)).neg
  · exact Complex.continuous_conj.comp (continuous_apply 2)

private lemma l4h_mem_XiW {ξ : Fin 3 → ℂ} : ξ ∈ XiW ↔ ξ ∈ Xi ∧ ξ 2 ∈ walls := Iff.rfl

private lemma l4h_weightedNorm_pow_six (z : Fin 3 → ℂ) :
    weightedNorm z ^ 6 = ‖z 0‖ ^ 6 + ‖z 1‖ ^ 3 + ‖z 2‖ ^ 2 := by
  unfold weightedNorm
  rw [show (1 / 6 : ℝ) = ((6 : ℕ) : ℝ)⁻¹ by norm_num]
  exact Real.rpow_inv_natCast_pow (by positivity) (by norm_num)

/-- `|z_j| ≤ φ(z)^j`. -/
private lemma l4h_norm_le_weightedNorm (z : Fin 3 → ℂ) :
    ‖z 0‖ ≤ weightedNorm z ∧ ‖z 1‖ ≤ weightedNorm z ^ 2 ∧ ‖z 2‖ ≤ weightedNorm z ^ 3 := by
  have h := l4h_weightedNorm_pow_six z
  have hφ : 0 ≤ weightedNorm z := Real.rpow_nonneg (by positivity) _
  have a0 := pow_nonneg (norm_nonneg (z 0)) 6
  have a1 := pow_nonneg (norm_nonneg (z 1)) 3
  have a2 := pow_nonneg (norm_nonneg (z 2)) 2
  refine ⟨?_, ?_, ?_⟩
  · refine (pow_le_pow_iff_left₀ (norm_nonneg _) hφ (by norm_num : 6 ≠ 0)).1 ?_
    rw [h]; linarith
  · refine (pow_le_pow_iff_left₀ (norm_nonneg _) (pow_nonneg hφ 2) (by norm_num : 3 ≠ 0)).1 ?_
    calc ‖z 1‖ ^ 3 ≤ weightedNorm z ^ 6 := by rw [h]; linarith
      _ = (weightedNorm z ^ 2) ^ 3 := by ring
  · refine (pow_le_pow_iff_left₀ (norm_nonneg _) (pow_nonneg hφ 3) (by norm_num : 2 ≠ 0)).1 ?_
    calc ‖z 2‖ ^ 2 ≤ weightedNorm z ^ 6 := by rw [h]; linarith
      _ = (weightedNorm z ^ 3) ^ 2 := by ring

/-- The walls are cones: `c 𝒲 ⊆ 𝒲` for `c ≥ 0`. -/
private lemma l4h_ofReal_mul_mem_walls {c : ℝ} (hc : 0 ≤ c) {w : ℂ} (hw : w ∈ walls) :
    (c : ℂ) * w ∈ walls := by
  have key : ∀ k, w ∈ wall k → (c : ℂ) * w ∈ wall k := by
    rintro k ⟨s, hs, rfl⟩
    exact ⟨c * s, mul_nonpos_of_nonneg_of_nonpos hc hs, by push_cast; ring⟩
  rcases hw with (h | h) | h
  · exact Or.inl (Or.inl (key 0 h))
  · exact Or.inl (Or.inr (key 1 h))
  · exact Or.inr (key 2 h)

/-- `conj 𝒲 = 𝒲` (`conj ζ = ζ²` exchanges `𝒲₁` and `𝒲₂`). -/
private lemma l4h_conj_mem_walls {w : ℂ} (hw : w ∈ walls) : starRingEnd ℂ w ∈ walls := by
  have hζ : starRingEnd ℂ ζ = ζ ^ 2 := by
    rw [← inv_eq_conj_of_mem_VT ζ_mem_VT]
    exact inv_eq_of_mul_eq_one_right (by rw [show ζ * ζ ^ 2 = ζ ^ 3 by ring, ζ_pow_three])
  rcases hw with (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩) | ⟨s, hs, rfl⟩
  · exact Or.inl (Or.inl ⟨s, hs, by simp⟩)
  · exact Or.inr ⟨s, hs, by simp [hζ]⟩
  · refine Or.inl (Or.inr ⟨s, hs, ?_⟩)
    simp only [map_mul, Complex.conj_ofReal, map_pow, hζ]
    linear_combination ((s : ℂ) * ζ) * ζ_pow_three

private lemma l4h_isClosed_wall (k : ℕ) : IsClosed (wall k) := by
  have hn : ‖ζ ^ k‖ = 1 := by rw [norm_pow, norm_eq_one_of_mem_VT ζ_mem_VT, one_pow]
  have hiso : Isometry fun s : ℝ ↦ (s : ℂ) * ζ ^ k := by
    refine Isometry.of_dist_eq fun a b ↦ ?_
    rw [Complex.dist_eq, ← sub_mul, norm_mul, hn, mul_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.dist_eq, Real.norm_eq_abs]
  have e : wall k = (fun s : ℝ ↦ (s : ℂ) * ζ ^ k) '' Iic 0 := by
    ext w
    constructor
    · rintro ⟨s, hs, rfl⟩; exact ⟨s, hs, rfl⟩
    · rintro ⟨s, hs, rfl⟩; exact ⟨s, hs, rfl⟩
  rw [e]
  exact hiso.isClosedEmbedding.isClosedMap _ isClosed_Iic

/-- `Ξ_𝒲` is compact: closed (`φ` is continuous, the walls are closed) and bounded
(`|ξ_j| ≤ 1`). -/
private lemma l4h_isCompact_XiW : IsCompact (XiW : Set (Fin 3 → ℂ)) := by
  have hXi : IsClosed Xi := isClosed_eq continuous_weightedNorm continuous_const
  have hW : IsClosed walls :=
    ((l4h_isClosed_wall 0).union (l4h_isClosed_wall 1)).union (l4h_isClosed_wall 2)
  have hC' : IsClosed (Xi ∩ (fun ξ : Fin 3 → ℂ ↦ ξ 2) ⁻¹' walls) :=
    hXi.inter (hW.preimage (continuous_apply 2))
  have hC : IsClosed (XiW : Set (Fin 3 → ℂ)) := hC'
  refine Metric.isCompact_of_isClosed_isBounded hC
    ((Metric.isBounded_closedBall (x := (0 : Fin 3 → ℂ)) (r := 1)).subset ?_)
  intro ξ hξ
  have h1 : weightedNorm ξ = 1 := (l4h_mem_XiW.1 hξ).1
  obtain ⟨a, b, c⟩ := l4h_norm_le_weightedNorm ξ
  rw [h1, one_pow] at *
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
  intro j
  fin_cases j
  exacts [a, b, c]


/-- **The Poincaré map** `F` of the Fuller system (TeX 11236–11251), in Cartesian coordinates:
`F(z⁰) = z(t_sw, z⁰, u)`, the value at the first switching time `t_sw` of the solution with initial
condition `z⁰` and the constant control `u` given by the maximum principle (the first control). -/
noncomputable def poincare (z : Fin 3 → ℂ) : Fin 3 → ℂ :=
  flow (firstSwitchTime z) z (firstControl z)

/-! ### Well-definedness on the section -/

/-- `t_sw < 10 φ(z⁰)` (Corollary 13.2.7 with `r = φ(z⁰)`, since `|z_j| ≤ φ(z)^j`). -/
theorem firstSwitchTime_lt {z : Fin 3 → ℂ} (hz : z ≠ 0) :
    firstSwitchTime z < 10 * weightedNorm z := by
  obtain ⟨h₁, h₂, h₃⟩ := l4h_norm_le_weightedNorm z
  exact (corollary13_2_7 hz h₁ h₂ h₃ (isFirstControl_firstControl hz)).2

/-- `F` maps `ℂ³ ∖ 0` into `ℂ³ ∖ 0`: `flow_firstControl_ne_zero` at `t = t_sw`
(`0 < t_sw`, `firstSwitchTime_pos`). On the section `(ℂ³ ∖ 0)_𝒲` this is also Lemma 13.3.1 at
`t = t_sw`, the book's silent justification (REPORT.md, E67); off the walls Lemma 13.3.1 does not
apply, and `poincare_tau_poincare` needs `τ F(z⁰) ≠ 0` for every `z⁰ ≠ 0`. -/
theorem poincare_ne_zero {z : Fin 3 → ℂ} (hz : z ≠ 0) : poincare z ≠ 0 := by
  exact flow_firstControl_ne_zero hz ⟨(firstSwitchTime_pos hz).le, le_rfl⟩

/-- `F` lands on the walls: at `t_sw` the first control and the control that beats it right after
`t_sw` both maximize `RR(z₃(t_sw), ·)` (`firstControl_maximizes`, `firstControl_beaten`
and continuity), so `z₃(t_sw) ∈ 𝒲` (`mem_walls_of_maximizers`). -/
private theorem l4st_poincare_mem_walls {z : Fin 3 → ℂ} (hz : z ≠ 0) : poincare z 2 ∈ walls := by
  have hfc := isFirstControl_firstControl hz
  have hmax := firstControl_maximizes hz
  have hT : firstSwitchTime z ∈ Icc 0 (firstSwitchTime z) :=
    ⟨(firstSwitchTime_pos hz).le, le_rfl⟩
  have hbeat := fun {ε : ℝ} (hε : 0 < ε) ↦ firstControl_beaten hz hε
  have hP : poincare z = flow (firstSwitchTime z) z (firstControl z) := rfl
  set u := firstControl z
  set T := firstSwitchTime z
  have huV : u ∈ VT := hfc.1
  have hmT : ∀ v ∈ VT, ham (poincare z) v ≤ ham (poincare z) u := hmax T hT
  by_contra hW
  -- every other control is strictly beaten at `t_sw`, or `F(z⁰)₃` would lie on a wall
  have hlt : ∀ v ∈ VT, v ≠ u → ham (poincare z) v < ham (poincare z) u := by
    intro v hv hne
    by_contra hle
    push Not at hle
    refine hW (mem_walls_of_maximizers huV hv (Ne.symm hne) (fun x hx ↦ ?_) fun x hx ↦ ?_)
    · exact (l4h_ham_le_iff _ _ _).1 (hmT x hx)
    · exact (l4h_ham_le_iff _ _ _).1 ((hmT x hx).trans hle)
  -- so `u` stays optimal near `t_sw`, by continuity
  have hev : ∀ v ∈ VT, ∀ᶠ t in 𝓝 T, ham (flow t z u) v ≤ ham (flow t z u) u := by
    intro v hv
    by_cases hne : v = u
    · rw [hne]; exact Filter.Eventually.of_forall fun _ ↦ le_rfl
    · have h := hlt v hv hne
      rw [hP] at h
      exact ((l4h_continuous_ham_flow z u v).continuousAt.eventually_lt
        (l4h_continuous_ham_flow z u u).continuousAt h).mono fun _ h ↦ h.le
  obtain ⟨ε, hε, hεT⟩ := Metric.eventually_nhds_iff.1 (finite_VT.eventually_all.2 hev)
  obtain ⟨t, ht, v, hv, hlt'⟩ := hbeat hε
  have hd : dist t T < ε := by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2]
  exact absurd (hεT hd v hv) (not_le.2 hlt')

/-- The control switches at `t_sw`: the first control of `F(z⁰)` differs from that of `z⁰`.

Proof route: `F(z⁰) ≠ 0` (`poincare_ne_zero`), so `firstControl (F z⁰)` is the first control
of `F(z⁰)` (`isFirstControl_firstControl`). If it were the first control `u` of `z⁰`, then `u`
would be optimal along `t ↦ z(t, F(z⁰), u) = z(t_sw + t, z⁰, u)` (`flow_add`) for
`t ∈ [0, ε]`, `ε > 0`, against `firstControl_beaten`. -/
theorem firstControl_poincare_ne {z : Fin 3 → ℂ} (hz : z ≠ 0) :
    firstControl (poincare z) ≠ firstControl z := by
  intro heq
  have h1 := isFirstControl_firstControl (poincare_ne_zero hz)
  rw [heq] at h1
  obtain ⟨-, ε, hε, hmax⟩ := h1
  obtain ⟨t, ht, v, hv, hlt⟩ := firstControl_beaten hz hε
  have e : flow t z (firstControl z) =
      flow (t - firstSwitchTime z) (poincare z) (firstControl z) := by
    rw [poincare, ← flow_add]
    congr 1
    ring
  rw [e] at hlt
  exact absurd (hmax _ ⟨by linarith [ht.1], by linarith [ht.2]⟩ v hv) (not_le.2 hlt)

/-! ### Equivariance -/

/-- Equivariance under `V_T` (Lemma 13.2.2 and (13.2.7)): the first control of `v z⁰` is `v` times
that of `z⁰`, the first switching time is the same, and `F(v z⁰) = v F(z⁰)`.

The proof redoes the substitution behind Lemma 13.2.2 for constant controls (`v z(t, z⁰, u) =
z(t, v z⁰, v u)` and `H_F(v z, v u) = H_F(z, u)`) rather than applying it: Lemma 13.2.2 is about
solutions with `H_F = 0` (13.2.6), and `z⁰` here is arbitrary (as in Lemma 13.2.5). -/
theorem poincare_smul {v : ℂ} (hv : v ∈ VT) {z : Fin 3 → ℂ} (hz : z ≠ 0) :
    firstControl (v • z) = v * firstControl z ∧ firstSwitchTime (v • z) = firstSwitchTime z ∧
      poincare (v • z) = v • poincare z := by
  have hv0 := l4h_ne_zero_of_mem_VT hv
  have hvz : v • z ≠ 0 := smul_ne_zero hv0 hz
  obtain ⟨huV, ε, hε, hmax⟩ := isFirstControl_firstControl hz
  have hfc : firstControl (v • z) = v * firstControl z := by
    refine (firstControl_eq_iff hvz).2 ⟨mul_mem_VT hv huV, ε, hε, fun t ht x hx ↦ ?_⟩
    rw [l4h_flow_smul, l4h_ham_smul hv, l4h_ham_smul hv, inv_mul_cancel_left₀ hv0]
    exact hmax t ht _ (l4h_inv_mul_mem_VT hv hx)
  have hT : firstSwitchTime (v • z) = firstSwitchTime z := by
    unfold firstSwitchTime
    rw [hfc]
    congr 1
    ext t
    simp only [Set.mem_ofPred_eq, l4h_flow_smul, l4h_ham_smul hv, inv_mul_cancel_left₀ hv0]
    constructor
    · rintro ⟨ht, x, hx, hlt⟩
      exact ⟨ht, _, l4h_inv_mul_mem_VT hv hx, hlt⟩
    · rintro ⟨ht, x, hx, hlt⟩
      refine ⟨ht, v * x, mul_mem_VT hv hx, ?_⟩
      rwa [inv_mul_cancel_left₀ hv0]
  refine ⟨hfc, hT, ?_⟩
  unfold poincare
  rw [hfc, hT, l4h_flow_smul]

/-- Equivariance under rescaling (Lemma 13.2.1): for `r > 0`, the first control of
`(r z₁, r² z₂, r³ z₃)` is that of `z`, its first switching time is `r t_sw(z)`, and
`F(r z₁, r² z₂, r³ z₃) = (r F(z)₁, r² F(z)₂, r³ F(z)₃)`.

The proof redoes the substitution behind Lemma 13.2.1 for constant controls
(`z(r t, (r z₁, r² z₂, r³ z₃), u) = (r z₁(t), r² z₂(t), r³ z₃(t))` and
`H_F((r z₁, r² z₂, r³ z₃), u) = r³ H_F(z, u)`) rather than applying it: Lemma 13.2.1 is about
solutions with `H_F = 0` (13.2.6), and `z⁰` here is arbitrary (as in Lemma 13.2.5). -/
theorem poincare_scale {r : ℝ} (hr : 0 < r) {z : Fin 3 → ℂ} (hz : z ≠ 0) :
    firstControl (scale r z) = firstControl z ∧
      firstSwitchTime (scale r z) = r * firstSwitchTime z ∧
      poincare (scale r z) = scale r (poincare z) := by
  have hrz : scale r z ≠ 0 := by
    intro h
    have := weightedNorm_scale hr z
    rw [h, weightedNorm_zero] at this
    exact (mul_pos hr (weightedNorm_pos hz)).ne' this.symm
  have hr3 : 0 < r ^ 3 := pow_pos hr 3
  obtain ⟨huV, ε, hε, hmax⟩ := isFirstControl_firstControl hz
  have hfl : ∀ t, flow t (scale r z) (firstControl z) =
      scale r (flow (t / r) z (firstControl z)) := by
    intro t
    rw [← l4h_flow_scale]
    congr 1
    field_simp
  have hfc : firstControl (scale r z) = firstControl z := by
    refine (firstControl_eq_iff hrz).2 ⟨huV, r * ε, mul_pos hr hε, fun t ht x hx ↦ ?_⟩
    rw [hfl, l4h_ham_scale, l4h_ham_scale]
    refine mul_le_mul_of_nonneg_left (hmax _ ⟨div_nonneg ht.1 hr.le, ?_⟩ x hx) hr3.le
    rw [div_le_iff₀ hr]
    linarith [ht.2]
  have hT : firstSwitchTime (scale r z) = r * firstSwitchTime z := by
    unfold firstSwitchTime
    rw [hfc, ← smul_eq_mul, ← Real.sInf_smul_of_nonneg hr.le]
    congr 1
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_smul_set, smul_eq_mul]
    constructor
    · rintro ⟨ht, x, hx, hlt⟩
      refine ⟨t / r, ⟨div_pos ht hr, x, hx, ?_⟩, by field_simp⟩
      rw [hfl, l4h_ham_scale, l4h_ham_scale] at hlt
      exact lt_of_mul_lt_mul_left hlt hr3.le
    · rintro ⟨s, ⟨hs, x, hx, hlt⟩, rfl⟩
      refine ⟨mul_pos hr hs, x, hx, ?_⟩
      rw [l4h_flow_scale, l4h_ham_scale, l4h_ham_scale]
      exact mul_lt_mul_of_pos_left hlt hr3
  refine ⟨hfc, hT, ?_⟩
  unfold poincare
  rw [hfc, hT, l4h_flow_scale]

/-- "By the scaling symmetries, … if the angular components `π_ang(q₁) = π_ang(q₂)` are equal, then
the angular components `π_ang F(q₁) = π_ang F(q₂)` of the images are equal" (TeX 11256–11260). -/
theorem ang_poincare_ang {z : Fin 3 → ℂ} (hz : z ≠ 0) :
    ang (poincare (ang z)) = ang (poincare z) := by
  have hs : 0 < (weightedNorm z)⁻¹ := inv_pos.2 (weightedNorm_pos hz)
  have hF := poincare_ne_zero hz
  rw [show ang z = scale (weightedNorm z)⁻¹ z from rfl, (poincare_scale hs hz).2.2]
  have := (weightedNorm_ang_smul_scale hF hs one_mem_VT).2
  rwa [one_smul, one_smul] at this

/-! ### The Hamiltonian -/

/-- `H_F⁺` under the virial group and time reversal: `H_F⁺(v·(r z₁, r² z₂, r³ z₃)) = r³ H_F⁺(z)`
for `v ∈ V_T`, `r > 0`, and `H_F⁺(τ z) = H_F⁺(z)`. -/
theorem hamMax_smul_scale_and_tau {v : ℂ} (hv : v ∈ VT) {r : ℝ} (hr : 0 < r) (z : Fin 3 → ℂ) :
    hamMax (v • scale r z) = r ^ 3 * hamMax z ∧ hamMax (tau z) = hamMax z := by
  have hr3 : 0 ≤ r ^ 3 := by positivity
  constructor
  · apply l4h_hamMax_eq
    · intro x hx
      rw [l4h_ham_smul hv, l4h_ham_scale]
      exact mul_le_mul_of_nonneg_left (ham_le_hamMax z (l4h_inv_mul_mem_VT hv hx)) hr3
    · obtain ⟨x, hx, hxe⟩ := l4h_exists_ham_eq_hamMax z
      refine ⟨v * x, mul_mem_VT hv hx, ?_⟩
      rw [l4h_ham_smul hv, l4h_ham_scale, inv_mul_cancel_left₀ (l4h_ne_zero_of_mem_VT hv), hxe]
  · apply l4h_hamMax_eq
    · intro x hx
      rw [ham_tau]
      exact ham_le_hamMax z (conj_mem_VT hx)
    · obtain ⟨x, hx, hxe⟩ := l4h_exists_ham_eq_hamMax z
      exact ⟨starRingEnd ℂ x, conj_mem_VT hx, by rw [ham_tau, Complex.conj_conj, hxe]⟩

/-- **The constancy of the Hamiltonian** (TeX 11429–11431, from TeX 10740–10742):
`H_F⁺(F(z⁰)) = H_F⁺(z⁰)`. (The first control maximizes `H_F` at `0` and at `t_sw`, and `H_F` is
constant along the segment, `ham_flow`.) -/
theorem hamMax_poincare {z : Fin 3 → ℂ} (hz : z ≠ 0) : hamMax (poincare z) = hamMax z := by
  have hfc := isFirstControl_firstControl hz
  have hmax := firstControl_maximizes hz
  have hT := (firstSwitchTime_pos hz).le
  have h0 : hamMax z = ham z (firstControl z) := by
    refine l4h_hamMax_eq (fun v hv ↦ ?_) ⟨_, hfc.1, rfl⟩
    have := hmax 0 ⟨le_rfl, hT⟩ v hv
    rwa [flow_zero] at this
  rw [h0, ← ham_flow (firstSwitchTime z) z (firstControl z)]
  exact l4h_hamMax_eq (hmax _ ⟨hT, le_rfl⟩) ⟨_, hfc.1, rfl⟩

/-! ### Time reversal -/

/-- **`F⁻¹ = τ F τ` at genuine switching points** (Lemmas 13.2.3 and 13.2.5 in map form; used in
Chapter 15, TeX 12324–12328, and for the instability of `q_in` in Lemma 13.5.5). If `z⁰ ≠ 0` and
the first control `u` of `z⁰` is not also its most recent control (so that `z⁰` is a switching
point of the extremal through it), then `F(τ(F(z⁰))) = τ(z⁰)`.

Proof route: with `z* = F(z⁰)`, `τ(z⁰) = z(t_sw, τ(z*), ū)` by Lemma 13.2.5; `τ(z*) ≠ 0`
(`poincare_ne_zero`, `tau_tau`), and `ū` is optimal along this segment (the maximum
condition reverses, `ham_tau`), so it is the first control of `τ(z*)`
(`firstControl_eq_iff`) and `t_sw(τ z*) ≥ t_sw(z⁰)`; equality holds because `u` is not
optimal at small negative times along `t ↦ z(t, z⁰, u)`, that is, `ū` is beaten right after
`t_sw` along the reversed segment. -/
theorem poincare_tau_poincare {z : Fin 3 → ℂ} (hz : z ≠ 0)
    (h : ¬ IsMostRecentControl z (firstControl z)) : poincare (tau (poincare z)) = tau z := by
  have hfc := isFirstControl_firstControl hz
  have hT0 := firstSwitchTime_pos hz
  have hmax := firstControl_maximizes hz
  have hzs := poincare_ne_zero hz
  have hP : poincare z = flow (firstSwitchTime z) z (firstControl z) := rfl
  set u := firstControl z
  set T := firstSwitchTime z
  set zs := poincare z
  have huV : u ∈ VT := hfc.1
  -- `u` is beaten at negative times arbitrarily close to `0` (`z⁰` is a switching point)
  have hneg : ∀ ε > 0, ∃ t ∈ Icc (-ε) 0, ∃ v ∈ VT, ham (flow t z u) u < ham (flow t z u) v := by
    intro ε hε
    by_contra hc
    push Not at hc
    exact h ⟨huV, ε, hε, hc⟩
  -- the reversed segment (Lemma 13.2.5): `z(s, τ z*, ū) = τ z(T - s, z⁰, u)`, and
  -- `H_F(τ w, x) = H_F(w, x̄)`
  have key : ∀ s x, ham (flow s (tau zs) (starRingEnd ℂ u)) x =
      ham (flow (T - s) z u) (starRingEnd ℂ x) := by
    intro s x
    rw [← (lemma13_2_5).1, ham_tau, hP, ← flow_add, sub_eq_add_neg]
  have hw : tau zs ≠ 0 := tau_ne_zero hzs
  -- `ū` is the first control of `τ z*`: it is optimal on `[0, T]`
  have hfw : firstControl (tau zs) = starRingEnd ℂ u := by
    refine (firstControl_eq_iff hw).2 ⟨conj_mem_VT huV, T, hT0, fun s hs x hx ↦ ?_⟩
    rw [key, key, Complex.conj_conj]
    exact hmax (T - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩ _ (conj_mem_VT hx)
  -- its first switching time is `T`: `ū` is optimal on `[0, T]` and beaten right after `T`
  have hTw : firstSwitchTime (tau zs) = T := by
    unfold firstSwitchTime
    rw [hfw]
    apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
    · obtain ⟨t, ht, v, hv, hlt⟩ := hneg 1 one_pos
      refine ⟨T - t, by linarith [ht.2], starRingEnd ℂ v, conj_mem_VT hv, ?_⟩
      rwa [key, key, Complex.conj_conj, Complex.conj_conj, sub_sub_cancel]
    · rintro a ⟨ha, v, hv, hlt⟩
      by_contra hlt'
      push Not at hlt'
      rw [key, key, Complex.conj_conj] at hlt
      exact absurd (hmax (T - a) ⟨by linarith, by linarith⟩ _ (conj_mem_VT hv))
        (not_le.2 hlt)
    · intro b hb
      obtain ⟨t, ht, v, hv, hlt⟩ := hneg ((b - T) / 2) (by linarith)
      refine ⟨T - t, ⟨by linarith [ht.2], starRingEnd ℂ v, conj_mem_VT hv, ?_⟩,
        by linarith [ht.1]⟩
      rwa [key, key, Complex.conj_conj, Complex.conj_conj, sub_sub_cancel]
  -- so `F(τ z*) = z(T, τ z*, ū) = τ z(0, z⁰, u) = τ z⁰`
  change flow (firstSwitchTime (tau zs)) (tau zs) (firstControl (tau zs)) = tau z
  rw [hTw, hfw, ← (lemma13_2_5).1, hP, ← flow_add, add_neg_cancel, flow_zero]

/-! ### The angular map on `Ξ_𝒲` and on `Ξ_𝒲/V_T` -/

/-- `F_ang` maps `Ξ_𝒲` to itself. -/
theorem ang_poincare_mem_XiW {ξ : Fin 3 → ℂ} (hξ : ξ ∈ XiW) : ang (poincare ξ) ∈ XiW := by
  have hz := ne_zero_of_mem_Xi (l4h_mem_XiW.1 hξ).1
  have hF := poincare_ne_zero hz
  refine l4h_mem_XiW.2 ⟨ang_mem_Xi hF, ?_⟩
  have e : ang (poincare ξ) 2 =
      (((weightedNorm (poincare ξ))⁻¹ ^ 3 : ℝ) : ℂ) * poincare ξ 2 := by
    simp [ang, scale]
  rw [e]
  exact l4h_ofReal_mul_mem_walls (pow_nonneg (inv_nonneg.2 (weightedNorm_pos hF).le) 3)
    (l4st_poincare_mem_walls hz)

/-- The Fuller–Poincaré map `F_ang : Ξ_𝒲 → Ξ_𝒲` (TeX 11256–11265), `ξ ↦ π_ang F(1, ξ)`. -/
noncomputable def poincareAng (ξ : XiW) : XiW := ⟨ang (poincare ξ), ang_poincare_mem_XiW ξ.2⟩

/-- `F_ang` is `V_T`-equivariant, so it maps orbits to orbits. -/
theorem poincareAng_orbitRel (ξ η : XiW)
    (h : MulAction.orbitRel (rootsOfUnity 3 ℂ) XiW ξ η) :
    MulAction.orbitRel (rootsOfUnity 3 ℂ) XiW (poincareAng ξ) (poincareAng η) := by
  obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 h)
  have hv : ((g : ℂˣ) : ℂ) ∈ VT := (mem_VT_iff_exists_rootsOfUnity _).2 ⟨g, rfl⟩
  have hη := ne_zero_of_mem_Xi (l4h_mem_XiW.1 η.2).1
  refine MulAction.orbitRel_apply.2 (MulAction.mem_orbit_iff.2 ⟨g, Subtype.ext ?_⟩)
  change ((g : ℂˣ) : ℂ) • ang (poincare η) = ang (poincare (((g : ℂˣ) : ℂ) • (η : Fin 3 → ℂ)))
  rw [(poincare_smul hv hη).2.2, ang_smul hv _]

/-- The Fuller–Poincaré map `F_ang : Ξ_𝒲/V_T → Ξ_𝒲/V_T` (TeX 11261–11265: "by equivariance"). -/
noncomputable def poincareAngQuot : XiWQuot → XiWQuot :=
  Quotient.map' poincareAng poincareAng_orbitRel

/-- `H_F⁺` is constant on the `V_T`-orbits of `Ξ_𝒲`. -/
theorem hamMax_orbitRel (ξ η : XiW) (h : MulAction.orbitRel (rootsOfUnity 3 ℂ) XiW ξ η) :
    hamMax ξ = hamMax η := by
  obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 h)
  have hv : ((g : ℂˣ) : ℂ) ∈ VT := (mem_VT_iff_exists_rootsOfUnity _).2 ⟨g, rfl⟩
  have e := (hamMax_smul_scale_and_tau hv one_pos (η : Fin 3 → ℂ)).1
  rw [scale_one, one_pow, one_mul] at e
  exact e

/-- The Hamiltonian `H_F⁺` on `Ξ_𝒲/V_T`. -/
noncomputable def hamMaxQuot : XiWQuot → ℝ :=
  Quotient.lift (fun ξ : XiW ↦ hamMax ξ) hamMax_orbitRel

/-- `Ξ_{𝒲,0}/V_T`: the subset of `Ξ_𝒲/V_T` on which the Hamiltonian vanishes (Remark 13.5.1,
Lemma 13.5.5, TeX 11280–11286, 11434–11436), with the subspace topology (which is also the
quotient topology of `Ξ_{𝒲,0} = {ξ ∈ Ξ_𝒲 | H_F⁺(ξ) = 0}`, a saturated subset). -/
abbrev XiW0Quot : Type := {x : XiWQuot // hamMaxQuot x = 0}

/-- `F_ang` preserves the zero set of the Hamiltonian ("by the constancy of the Hamiltonian, the
map `F` restricts to the zero set of the Hamiltonian", TeX 11429–11431): `H_F⁺(F_ang ξ) =
φ(F ξ)⁻³ H_F⁺(ξ)`. -/
theorem hamMaxQuot_poincareAngQuot_eq_zero_iff (x : XiWQuot) :
    hamMaxQuot (poincareAngQuot x) = 0 ↔ hamMaxQuot x = 0 := by
  refine Quotient.inductionOn' x fun ξ ↦ ?_
  change hamMax (ang (poincare ξ)) = 0 ↔ hamMax ξ = 0
  have hz := ne_zero_of_mem_Xi (l4h_mem_XiW.1 ξ.2).1
  have hF := poincare_ne_zero hz
  have hs := inv_pos.2 (weightedNorm_pos hF)
  have e := (hamMax_smul_scale_and_tau one_mem_VT hs (poincare ξ)).1
  rw [one_smul] at e
  rw [show ang (poincare ξ) = scale (weightedNorm (poincare ξ))⁻¹ (poincare ξ) from rfl, e,
    hamMax_poincare hz]
  constructor
  · intro h0
    exact (mul_eq_zero.1 h0).resolve_left (pow_pos hs 3).ne'
  · intro h0
    rw [h0, mul_zero]

/-- The Fuller–Poincaré map restricted to `Ξ_{𝒲,0}/V_T` (Lemma 13.5.5, TeX 11434). -/
noncomputable def poincareAngZero (x : XiW0Quot) : XiW0Quot :=
  ⟨poincareAngQuot x.1, (hamMaxQuot_poincareAngQuot_eq_zero_iff x.1).2 x.2⟩

/-- `τ` maps `Ξ_𝒲` to itself (`φ(τ ξ) = φ(ξ)`, `conj 𝒲 = 𝒲`). -/
theorem tau_mem_XiW {ξ : Fin 3 → ℂ} (hξ : ξ ∈ XiW) : tau ξ ∈ XiW := by
  obtain ⟨h1, h2⟩ := l4h_mem_XiW.1 hξ
  refine l4h_mem_XiW.2 ⟨?_, ?_⟩
  · have e : weightedNorm (tau ξ) = weightedNorm ξ := by simp [weightedNorm, tau]
    change weightedNorm (tau ξ) = 1
    rw [e]
    exact h1
  · have e : tau ξ 2 = starRingEnd ℂ (ξ 2) := by simp [tau]
    rw [e]
    exact l4h_conj_mem_walls h2

/-- The time reversal `τ` on `Ξ_𝒲`. -/
noncomputable def tauXiW (ξ : XiW) : XiW := ⟨tau ξ, tau_mem_XiW ξ.2⟩

/-- `τ` maps `V_T`-orbits to `V_T`-orbits (`τ(v ξ) = v̄ τ(ξ)`). -/
theorem tauXiW_orbitRel (ξ η : XiW) (h : MulAction.orbitRel (rootsOfUnity 3 ℂ) XiW ξ η) :
    MulAction.orbitRel (rootsOfUnity 3 ℂ) XiW (tauXiW ξ) (tauXiW η) := by
  obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 h)
  have hv : ((g : ℂˣ) : ℂ) ∈ VT := (mem_VT_iff_exists_rootsOfUnity _).2 ⟨g, rfl⟩
  refine MulAction.orbitRel_apply.2 (MulAction.mem_orbit_iff.2 ⟨g⁻¹, Subtype.ext ?_⟩)
  change (((g⁻¹ : rootsOfUnity 3 ℂ) : ℂˣ) : ℂ) • tau (η : Fin 3 → ℂ) =
    tau (((g : ℂˣ) : ℂ) • (η : Fin 3 → ℂ))
  have e : (((g⁻¹ : rootsOfUnity 3 ℂ) : ℂˣ) : ℂ) = (((g : ℂˣ) : ℂ))⁻¹ := by simp
  rw [l4h_tau_smul, e, inv_eq_conj_of_mem_VT hv]

/-- The time reversal `τ` on `Ξ_𝒲/V_T`. -/
noncomputable def tauQuot : XiWQuot → XiWQuot := Quotient.map' tauXiW tauXiW_orbitRel

/-- `τ` preserves the Hamiltonian on `Ξ_𝒲/V_T`. -/
theorem hamMaxQuot_tauQuot (x : XiWQuot) : hamMaxQuot (tauQuot x) = hamMaxQuot x := by
  refine Quotient.inductionOn' x fun ξ ↦ ?_
  change hamMax (tau ξ) = hamMax ξ
  exact (hamMax_smul_scale_and_tau one_mem_VT one_pos _).2

/-- The time reversal `τ` on `Ξ_{𝒲,0}/V_T`. -/
noncomputable def tauZero (x : XiW0Quot) : XiW0Quot :=
  ⟨tauQuot x.1, (hamMaxQuot_tauQuot x.1).trans x.2⟩

/-! ### Topology of the quotients -/

/-- `Ξ_𝒲/V_T` is a compact Hausdorff space (`Ξ_𝒲` is compact, `V_T` finite), and `Ξ_{𝒲,0}/V_T`
is closed in it (`hamMaxQuot` is continuous). -/
theorem compact_t2_isClosed_XiWQuot :
    CompactSpace XiWQuot ∧ T2Space XiWQuot ∧ IsClosed {x : XiWQuot | hamMaxQuot x = 0} := by
  have : CompactSpace XiW := isCompact_iff_compactSpace.mp l4h_isCompact_XiW
  refine ⟨inferInstance, inferInstance, isClosed_eq ?_ continuous_const⟩
  unfold hamMaxQuot
  exact (l4h_continuous_hamMax.comp continuous_subtype_val).quotient_lift _

/-- `τ` is a continuous involution of `Ξ_{𝒲,0}/V_T`. -/
theorem continuous_involutive_tauZero :
    Continuous tauZero ∧ Function.Involutive tauZero := by
  have hτ : Continuous tauXiW :=
    (l4h_continuous_tau.comp continuous_subtype_val).subtype_mk _
  have hq : Continuous tauQuot := hτ.quotient_map' _
  have hinv : ∀ y : XiWQuot, tauQuot (tauQuot y) = y := by
    intro y
    refine Quotient.inductionOn' y fun ξ ↦ ?_
    change Quotient.mk'' (tauXiW (tauXiW ξ)) = Quotient.mk'' ξ
    congr 1
    exact Subtype.ext (tau_tau _)
  exact ⟨(hq.comp continuous_subtype_val).subtype_mk _, fun x ↦ Subtype.ext (hinv x.1)⟩

end TriFuller

end SmoothedPolygons
