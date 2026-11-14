module

public import SmoothedPolygons.Ch16.GlobalBasin
import SmoothedPolygons.Ch13.Jacobian

/-!
# Chapter 16: Theorem 16.2.1, outward and inward Fuller trajectories

§16.2 of Hales–Vajjha, *Packings of Smoothed Polygons* ("Classification of Outward Fuller
Trajectories", TeX 12747–12779): the switching points of a trajectory of the Fuller–Poincaré
dynamical system on `(ℂ³ ∖ 0)/V_T` that emanates from the singular locus `0` all lie on the ray
`ℝ_{>0} × {q_out}` (the outward triangular spiral), and those of a trajectory that tends to `0` on
the ray `ℝ_{>0} × {q_in}` (the inward spiral). Not used by any later result of the book.

Formalized with the Poincaré map `F = poincare` on `ℂ³ ∖ 0` (the map of the dynamical system, TeX
12749–12752), a trajectory being a sequence of switching points `F^k(z⁰)` (inward) or a backward
orbit `F(z_{k+1}) = z_k` (outward), and "in `ℝ_{>0} × {q}` modulo `V_T`" being "the class of the
angular part is `q`" (`classOf`). The radial factor `ρ(x) = φ(F ξ)` (`radialFactor`) is the factor
by which one step multiplies the weighted norm `φ`, by homogeneity (Lemma 13.2.1).

## The book's proof (TeX 12763–12778), and what it leaves implicit

"By time reversal symmetry, it is enough to prove the second statement … Let `q ∈ Ξ_𝒲/V_T` be any
switching point of any trajectory. If `q = q_in`, then it is the inward spiral. Otherwise … by the
Fuller basin theorem and by the stability calculation near `q_in`, for large `j`, the iterates
`F_ang^j(q)` approach the outward spiral. … The outward spiral moves away from the singular locus
(because of the scaling factor `r_scale > 1`), and the Fuller trajectory must then also move away
from the singular locus."

The details the book leaves implicit (REPORT.md, E80), supplied here:
* the basin theorem is about `Ξ_{𝒲,0}`; a trajectory tending to `0` has `H_F⁺ = 0`, because
  `H_F⁺` is constant along it (`hamMax_poincare`) and continuous with `H_F⁺(0) = 0`
  (`hamMax_eq_zero_of_tendsto_zero`); so the theorem holds on all of `(ℂ³ ∖ 0)/V_T` as stated;
* "the stability calculation near `q_in`" is not needed (Theorem 16.1.1 covers every `q ≠ q_in`);
* "approaches the outward spiral … must also move away": `φ(F^{k+1} z) = φ(F^k z) ρ([F^k z])`
  (`weightedNorm_poincare_eq`), `ρ` is continuous at `q_out` with `ρ(q_out) = r_scale > 1`
  (`radialFactor_qOut0`, `continuousAt_radialFactor_qOut0`; Lemma 13.5.2, Remark 13.5.3), so
  eventually `ρ > 1` and the weighted norms are eventually nondecreasing and positive (indeed they
  grow geometrically), against `F^k z → 0`;
* the time reversal: the points `z_k = F(z_{k+1})` of a backward orbit lie on the walls (`F` lands
  on the walls) and have `H_F⁺(z_k) = H_F⁺(z_{k+j}) → H_F⁺(0) = 0`, so they lie in the section;
  `F(τ z_k) = τ z_{k+1}` by `F⁻¹ = τ F τ` at switching points (`poincare_tau_poincare`; every
  `z_k = F(z_{k+1})` is a switching point, `isSwitchingPoint_poincare`).

## Continuity of `ρ` at `q_out`

`continuousAt_radialFactor_qOut0` is proved in the chart of Chapter 13 near `q_out`
(`SmoothedPolygons/Ch13/Jacobian.lean`), not in the cell coordinates of Chapter 15: the chart's
normalization map `chartOf` gives the local inverse, and the chart map `chartMap`, `C¹` at `x_out`
by the implicit function theorem, determines the first switching time near `q_out`.
-/

@[expose] public section

namespace SmoothedPolygons

open Set Filter Topology

namespace TriFuller

/-- The radial factor `ρ(x) = φ(F ξ)` at `x = [ξ] ∈ Ξ_{𝒲,0}/V_T` (`ξ ∈ Ξ_𝒲`, `φ(ξ) = 1`; computed at
the representative `Quotient.out`, and independent of it, `weightedNorm_poincare_eq`): one step of
the Fuller–Poincaré map multiplies the weighted norm by `ρ`. -/
noncomputable def radialFactor (x : XiW0Quot) : ℝ :=
  weightedNorm (poincare ((Quotient.out x.1 : XiW) : Fin 3 → ℂ))

/-! ### The radial factor on representatives -/

/-- The radial factor at the class of a point `ξ` of `Ξ_𝒲` is `φ(F ξ)`: `Quotient.out` is `v ξ`
for some `v ∈ V_T`, and `φ(F(v ξ)) = φ(v F(ξ)) = φ(F ξ)` (`poincare_smul`, `weightedNorm_smul`). -/
private lemma l5g_radialFactor_mk {x : XiW0Quot} {ξ : XiW} (hx : x.1 = Quotient.mk'' ξ) :
    radialFactor x = weightedNorm (poincare (ξ : Fin 3 → ℂ)) := by
  have hrel : MulAction.orbitRel (rootsOfUnity 3 ℂ) XiW
      (Quotient.out (Quotient.mk'' ξ : XiWQuot)) ξ := Quotient.mk_out' ξ
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 hrel)
  have hv : ((g : ℂˣ) : ℂ) ∈ VT := (mem_VT_iff_exists_rootsOfUnity _).2 ⟨g, rfl⟩
  have hmem : (ξ : Fin 3 → ℂ) ∈ Xi ∧ (ξ : Fin 3 → ℂ) 2 ∈ walls := ξ.2
  have hξ0 : (ξ : Fin 3 → ℂ) ≠ 0 := ne_zero_of_mem_Xi hmem.1
  unfold radialFactor
  rw [hx, ← hg]
  change weightedNorm (poincare (((g : ℂˣ) : ℂ) • (ξ : Fin 3 → ℂ))) = _
  rw [(poincare_smul hv hξ0).2.2, weightedNorm_smul hv]

/-- `ρ([ang z]) = φ(F z)/φ(z)` (`poincare_scale`, `weightedNorm_scale`). -/
private lemma l5g_radialFactor_ang {x : XiW0Quot} {z : Fin 3 → ℂ} (hz : z ≠ 0) (hW : ang z ∈ XiW)
    (hx : x.1 = Quotient.mk'' ⟨ang z, hW⟩) :
    radialFactor x = weightedNorm (poincare z) / weightedNorm z := by
  rw [l5g_radialFactor_mk hx]
  have hs : 0 < (weightedNorm z)⁻¹ := inv_pos.2 (weightedNorm_pos hz)
  change weightedNorm (poincare (scale (weightedNorm z)⁻¹ z)) = _
  rw [(poincare_scale hs hz).2.2, weightedNorm_scale hs, div_eq_inv_mul]

/-- `φ(F z) = φ(z) ρ([z])` for `z` in the section: `z = (φ(z) ξ₁, φ(z)² ξ₂, φ(z)³ ξ₃)` with
`ξ = ang z`, `F` commutes with the rescaling (`poincare_scale`) and with `V_T` (`poincare_smul`),
and `φ(r w) = r φ(w)`, `φ(v w) = φ(w)` (`weightedNorm_scale`, `weightedNorm_smul`). -/
theorem weightedNorm_poincare_eq {z : Fin 3 → ℂ} (hz : z ∈ sectionZero) :
    weightedNorm (poincare z) = weightedNorm z * radialFactor (classOf z) := by
  have hc : (classOf z).1 = Quotient.mk'' ⟨ang z, ang_mem_XiW hz.1 hz.2.1⟩ := by
    rw [classOf, dite_eq_left hz]
  rw [l5g_radialFactor_ang hz.1 _ hc, mul_div_cancel₀ _ (weightedNorm_pos hz.1).ne']

/-- `ρ(q_out) = r_scale`: `F(qOutCart) = ζ² (r_scale qOutCart₁, r_scale² qOutCart₂, r_scale³
qOutCart₃)` (Lemma 13.5.2, `poincare_qOutCart`), so `φ(F qOutCart) = r_scale φ(qOutCart)`. -/
theorem radialFactor_qOut0 : radialFactor qOut0 = rScale := by
  have hq := qOutCart_ne_zero
  have hr : 0 < rScale := one_pos.trans rScale_spec.1
  rw [l5g_radialFactor_ang hq ang_qOutCart_mem_XiW.1 rfl, poincare_qOutCart,
    weightedNorm_smul ζ_sq_mem_VT, weightedNorm_scale hr, mul_div_assoc,
    div_self (weightedNorm_pos hq).ne', mul_one]

/-! ### Continuity of the radial factor at `q_out`: the chart of Chapter 13 -/

/-- The ratio `φ(F z)/φ(z)`, invariant under the virial rescalings. -/
private noncomputable def l5g_ratio (z : Fin 3 → ℂ) : ℝ :=
  weightedNorm (poincare z) / weightedNorm z

private lemma l5g_ratio_scale {c : ℝ} (hc : 0 < c) {z : Fin 3 → ℂ} (hz : z ≠ 0) :
    l5g_ratio (scale c z) = l5g_ratio z := by
  rw [l5g_ratio, l5g_ratio, (poincare_scale hc hz).2.2, weightedNorm_scale hc,
    weightedNorm_scale hc, mul_div_mul_left _ _ hc.ne']

/-- `H_F⁺` at a point with `z₃ ∈ ℝ_{<0}`: `H_F(z, ζ) = H_F(z, ζ²) = RR(z₁, i z₂) - z₃/2` beats
`H_F(z, 1) = RR(z₁, i z₂) + z₃`. -/
private lemma l5g_hamMax_of_real_neg {z : Fin 3 → ℂ} (h2 : (z 2).im = 0) (h2' : (z 2).re < 0) :
    hamMax z = (z 0).im * (z 1).re - (z 0).re * (z 1).im - (z 2).re / 2 := by
  simp only [hamMax, ham, RR_eq_re_mul_add_im_mul, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.one_re, Complex.one_im, ζ_re, ζ_im, ζ_sq_re, ζ_sq_im, h2,
    mul_zero, mul_one, add_zero, zero_sub]
  rw [max_self, max_eq_right (by linarith)]
  ring

/-- `chartCart x ≠ 0` (`Re z₁ = -1`). -/
private lemma l5g_chartCart_ne_zero (x : Fin 3 → ℝ) : chartCart x ≠ 0 := by
  intro h
  have := congrArg (fun z ↦ (z 0).re) h
  simp [chartCart] at this

private lemma l5g_continuous_chartCart : Continuous chartCart := by
  refine continuous_pi fun i ↦ ?_
  fin_cases i <;> simp only [chartCart, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> fun_prop

private lemma l5g_continuous_flow (u : ℂ) :
    Continuous fun p : ℝ × (Fin 3 → ℂ) ↦ flow p.1 p.2 u := by
  refine continuous_pi fun i ↦ ?_
  fin_cases i <;> simp only [flow, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> fun_prop

/-- `chartCart x_out = qOutCart` (`H_F⁺(qOutCart) = 0` gives `z₃ = 2(pc + d)`). -/
private lemma l5g_chartCart_xOut : chartCart xOut = qOutCart := by
  obtain ⟨h0, h2, h2'⟩ := qOutCart_normalization
  have hH := hamMax_qOutCart
  rw [l5g_hamMax_of_real_neg h2 h2', h0] at hH
  funext i
  fin_cases i
  · apply Complex.ext <;> simp [chartCart, xOut, h0]
  · apply Complex.ext <;> simp [chartCart, xOut]
  · apply Complex.ext <;> simp [chartCart, xOut, h2]
    linarith

/-- The coordinates of `x_out` used here: `√3 p = (r - 1)/(r + 1) < 1`, `d > 0`, and
`pc + d < 0` (from (13.5.1), `r = r_scale > 6.27`). -/
private lemma l5g_xOut_facts :
    √3 * xOut 0 < 1 ∧ 0 < xOut 2 ∧ xOut 0 * xOut 1 + xOut 2 < 0 := by
  have hr1 := rScale_bounds.1
  have hr : 0 < rScale := by linarith
  have h0 : xOut 0 = (-1 + rScale) / (√3 * (1 + rScale)) := by
    simp only [xOut, qOutCart, equilExact, Matrix.cons_val, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]
    norm_num
  have h2 : xOut 2 = (1 - 3 * rScale - 2 * rScale ^ 2 - 3 * rScale ^ 3 + rScale ^ 4) /
      (3 * (1 + rScale + rScale ^ 3 + rScale ^ 4)) := by
    simp only [xOut, qOutCart, equilExact, Matrix.cons_val, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · have h3 : 0 < √3 := by positivity
    rw [h0, mul_div_assoc', div_lt_one (by positivity)]
    have : √3 * (-1 + rScale) < √3 * (1 + rScale) := by nlinarith
    linarith [mul_comm (√3) (1 + rScale)]
  · rw [h2]
    refine div_pos ?_ (by positivity)
    nlinarith [mul_pos (pow_pos hr 3) (by linarith : (0 : ℝ) < rScale - 4)]
  · have h := qOutCart_normalization.2.2
    rw [← l5g_chartCart_xOut] at h
    simp only [chartCart, Matrix.cons_val, Complex.ofReal_re] at h
    linarith

/-- The first coordinate of `ζ z(t, chartCart x, ζ)`: real part `1/2 - √3(p + t)/2`, imaginary part
`(t - p - √3)/2`. -/
private lemma l5g_flow_chartCart_zero (x : Fin 3 → ℝ) (t : ℝ) :
    (ζ * flow t (chartCart x) ζ 0).re = 1 / 2 - √3 * (x 0 + t) / 2 ∧
      (ζ * flow t (chartCart x) ζ 0).im = (t - x 0 - √3) / 2 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [flow, chartCart, Matrix.cons_val, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, ζ_re, ζ_im]
  norm_num
  constructor
  · ring
  · linear_combination (t / 4) * h3

/-- **The first switching time is read off the chart map** (Möbius inversion): if the first
control of `chartCart x` is `ζ`, then `m = chartMap x 0 = -Im w₁/Re w₁` with
`w₁ = (ζ F(chartCart x))₁ = (1/2 - √3(p + T)/2) + i (T - p - √3)/2`, `T = t_sw(chartCart x)`; when
`Re w₁ ≠ 0` (which holds if `chartMap x 2 ≠ 0`) and `1 - √3 m ≠ 0`,
`T = (p + √3 - m + √3 p m)/(1 - √3 m)`. -/
private lemma l5g_firstSwitchTime_eq {x : Fin 3 → ℝ} (h : firstControl (chartCart x) = ζ)
    (h2 : chartMap x 2 ≠ 0) (h1 : 1 - √3 * chartMap x 0 ≠ 0) :
    firstSwitchTime (chartCart x) =
      (x 0 + √3 - chartMap x 0 + √3 * x 0 * chartMap x 0) / (1 - √3 * chartMap x 0) := by
  have hP : poincare (chartCart x) = flow (firstSwitchTime (chartCart x)) (chartCart x) ζ := by
    rw [poincare, h]
  obtain ⟨hre, him⟩ := l5g_flow_chartCart_zero x (firstSwitchTime (chartCart x))
  rw [← hP] at hre him
  have hm : chartMap x 0 = -((ζ * poincare (chartCart x) 0).re)⁻¹ *
      (ζ * poincare (chartCart x) 0).im := by
    simp only [chartMap, Pi.smul_apply, smul_eq_mul, Matrix.cons_val]
  have hR : (ζ * poincare (chartCart x) 0).re ≠ 0 := by
    intro h0
    apply h2
    simp only [chartMap, Pi.smul_apply, smul_eq_mul, Matrix.cons_val, h0, inv_zero, neg_zero,
      zero_pow two_ne_zero, zero_mul]
  rw [hre, him] at hm
  rw [hre] at hR
  set T := firstSwitchTime (chartCart x)
  set m := chartMap x 0
  have hm' : m * (1 / 2 - √3 * (x 0 + T) / 2) = -((T - x 0 - √3) / 2) := by
    rw [hm, mul_comm, neg_mul, mul_neg, ← mul_assoc, mul_inv_cancel₀ hR, one_mul]
  rw [eq_div_iff h1]
  linear_combination 2 * hm'

/-- **`x ↦ F(chartCart x)` is continuous at `x_out`**: near `x_out` the first control is `ζ`
(`firstControl_eq_of_ofReal_neg`) and the first switching time is the continuous function
`(p + √3 - m + √3 p m)/(1 - √3 m)` of `p = x 0` and `m = chartMap x 0` (`l5g_firstSwitchTime_eq`),
`chartMap` being `C¹` at `x_out` (`contDiffAt_chartMap`: there the switching time is the simple
root of the switching function from `ζ` to `1`, by the implicit function theorem, Chapter 13). -/
private lemma l5g_continuousAt_poincare_chartCart :
    ContinuousAt (fun x ↦ poincare (chartCart x)) xOut := by
  obtain ⟨hp, hd, hpcd⟩ := l5g_xOut_facts
  have hcm : ContinuousAt chartMap xOut := contDiffAt_chartMap.continuousAt
  have hm0 : ContinuousAt (fun x : Fin 3 → ℝ ↦ chartMap x 0) xOut :=
    (continuous_apply 0).continuousAt.comp hcm
  have hm2 : ContinuousAt (fun x : Fin 3 → ℝ ↦ chartMap x 2) xOut :=
    (continuous_apply 2).continuousAt.comp hcm
  have hx0 : ContinuousAt (fun x : Fin 3 → ℝ ↦ x 0) xOut := (continuous_apply 0).continuousAt
  have hc0 : chartMap xOut 0 = xOut 0 := by rw [chartMap_xOut]
  have hc2 : chartMap xOut 2 = xOut 2 := by rw [chartMap_xOut]
  have hden : ContinuousAt (fun x : Fin 3 → ℝ ↦ 1 - √3 * chartMap x 0) xOut :=
    continuousAt_const.sub (continuousAt_const.mul hm0)
  have hden0 : 0 < 1 - √3 * chartMap xOut 0 := by rw [hc0]; linarith
  have hT : ContinuousAt (fun x : Fin 3 → ℝ ↦
      (x 0 + √3 - chartMap x 0 + √3 * x 0 * chartMap x 0) / (1 - √3 * chartMap x 0)) xOut :=
    (((hx0.add continuousAt_const).sub hm0).add ((continuousAt_const.mul hx0).mul hm0)).div
      hden hden0.ne'
  have hflow : ContinuousAt (fun x : Fin 3 → ℝ ↦ flow
      ((x 0 + √3 - chartMap x 0 + √3 * x 0 * chartMap x 0) / (1 - √3 * chartMap x 0))
      (chartCart x) ζ) xOut :=
    (l5g_continuous_flow ζ).continuousAt.comp (hT.prodMk l5g_continuous_chartCart.continuousAt)
  refine hflow.congr ?_
  have e1 : ∀ᶠ x in 𝓝 xOut, x 0 * x 1 + x 2 < 0 :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds hpcd
  have e2 : ∀ᶠ x in 𝓝 xOut, 0 < x 2 := (continuous_apply 2).continuousAt.eventually (lt_mem_nhds hd)
  have e3 : ∀ᶠ x in 𝓝 xOut, 0 < chartMap x 2 :=
    hm2.eventually (lt_mem_nhds (show (0 : ℝ) < chartMap xOut 2 by rw [hc2]; exact hd))
  have e4 : ∀ᶠ x in 𝓝 xOut, 0 < 1 - √3 * chartMap x 0 := hden.eventually (lt_mem_nhds hden0)
  filter_upwards [e1, e2, e3, e4] with x h1 h2 h3 h4
  have hfc : firstControl (chartCart x) = ζ := by
    refine (firstControl_eq_of_ofReal_neg (x₃ := (chartCart x 2).re) ?_ ?_).1 (Or.inl ?_)
    · apply Complex.ext <;> simp [chartCart]
    · simp only [chartCart, Matrix.cons_val, Complex.ofReal_re]; linarith
    · simpa [chartCart] using h2
  rw [poincare, hfc, l5g_firstSwitchTime_eq hfc h3.ne' h4.ne']

/-- A point `z` of the section with `Re z₃ < 0` and `Re z₁ < 0` (so `z₃ ∈ ℝ_{<0}`) rescaled by
`s = -1/Re z₁` is the chart point of `chartOf z` (`H_F⁺ = 0` gives `z₃ = 2(pc + d)`). -/
private lemma l5g_scale_eq_chartCart_chartOf {z : Fin 3 → ℂ} (hz : z ∈ sectionZero)
    (h2 : (z 2).re < 0) (h0 : (z 0).re < 0) :
    scale (-((z 0).re)⁻¹) z = chartCart (chartOf z) := by
  have him : (z 2).im = 0 := im_eq_zero_of_mem_walls hz.2.1 h2
  have hH := hz.2.2
  rw [l5g_hamMax_of_real_neg him h2] at hH
  obtain ⟨a, ha⟩ : ∃ a : ℝ, z 2 = a := ⟨(z 2).re, Complex.ext (by simp) (by simp [him])⟩
  have ha' : a < 0 := by rw [ha, Complex.ofReal_re] at h2; exact h2
  have hω : -starRingEnd ℂ (z 2) / (‖z 2‖ : ℂ) = 1 := by
    rw [ha, Complex.conj_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_neg ha']
    have : (a : ℂ) ≠ 0 := by exact_mod_cast ha'.ne
    push_cast
    field_simp
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = -((z 0).re)⁻¹ := ⟨_, rfl⟩
  have hs0 : s * (z 0).re = -1 := by rw [hs, neg_mul, inv_mul_cancel₀ h0.ne]
  have hco : chartOf z = ![s * (z 0).im, s ^ 2 * (z 1).re, s ^ 2 * (z 1).im] := by
    simp only [chartOf, hω, one_smul, hs]
  rw [← hs, hco]
  funext i
  fin_cases i
  · apply Complex.ext <;> simp [scale, chartCart, hs0]
  · apply Complex.ext <;> simp [scale, chartCart, ← Complex.ofReal_pow]
  · apply Complex.ext <;> simp [scale, chartCart, him, ← Complex.ofReal_pow]
    linear_combination (-2 * s ^ 3) * hH + (-2 * s ^ 2 * (z 1).im) * hs0

/-- `φ(F z)/φ(z) = G(chartOf z)` with `G(x) = φ(F(chartCart x))/φ(chartCart x)`, near `qOutCart`
on the section. -/
private lemma l5g_ratio_eq {z : Fin 3 → ℂ} (hz : z ∈ sectionZero) (h2 : (z 2).re < 0)
    (h0 : (z 0).re < 0) : l5g_ratio z = l5g_ratio (chartCart (chartOf z)) := by
  rw [← l5g_scale_eq_chartCart_chartOf hz h2 h0,
    l5g_ratio_scale (neg_pos.2 (inv_lt_zero.2 h0)) hz.1]

/-- `φ(F z)/φ(z) → r_scale` as `z → qOutCart` on the section. -/
private lemma l5g_tendsto_ratio_qOutCart :
    Tendsto l5g_ratio (𝓝[sectionZero] qOutCart) (𝓝 rScale) := by
  obtain ⟨hq0, -, hq2⟩ := qOutCart_normalization
  have hpcd := l5g_xOut_facts.2.2
  have hG : ContinuousAt (fun x ↦ l5g_ratio (chartCart x)) xOut :=
    (continuous_weightedNorm.continuousAt.comp l5g_continuousAt_poincare_chartCart).div
      (continuous_weightedNorm.comp l5g_continuous_chartCart).continuousAt
      (weightedNorm_pos (l5g_chartCart_ne_zero xOut)).ne'
  have hGv : l5g_ratio (chartCart xOut) = rScale := by
    have hr : 0 < rScale := one_pos.trans rScale_spec.1
    rw [l5g_chartCart_xOut, l5g_ratio, poincare_qOutCart, weightedNorm_smul ζ_sq_mem_VT,
      weightedNorm_scale hr, mul_div_assoc, div_self (weightedNorm_pos qOutCart_ne_zero).ne',
      mul_one]
  have hC : ContinuousAt chartOf qOutCart := eventually_contDiffAt_chartOf.self_of_nhds.continuousAt
  have hCv : chartOf qOutCart = xOut := by
    rw [← l5g_chartCart_xOut, chartOf_chartCart hpcd]
  have hGC : Tendsto (fun z ↦ l5g_ratio (chartCart (chartOf z))) (𝓝 qOutCart) (𝓝 rScale) := by
    rw [← hGv, ← hCv]
    exact (hCv ▸ hG).comp hC
  refine (hGC.mono_left nhdsWithin_le_nhds).congr' ?_
  have hc2 : Continuous fun z : Fin 3 → ℂ ↦ (z 2).re := by fun_prop
  have hc0 : Continuous fun z : Fin 3 → ℂ ↦ (z 0).re := by fun_prop
  have e2 : ∀ᶠ z in 𝓝 qOutCart, (z 2).re < 0 := hc2.continuousAt.eventually (gt_mem_nhds hq2)
  have e0 : ∀ᶠ z in 𝓝 qOutCart, (z 0).re < 0 :=
    hc0.continuousAt.eventually (gt_mem_nhds (show (qOutCart 0).re < 0 by rw [hq0]; norm_num))
  filter_upwards [nhdsWithin_le_nhds e2, nhdsWithin_le_nhds e0, self_mem_nhdsWithin]
    with z hz2 hz0 hz
  exact (l5g_ratio_eq hz hz2 hz0).symm

/-- The rescalings map the section to itself. -/
private lemma l5g_scale_mem_sectionZero {c : ℝ} (hc : 0 < c) {z : Fin 3 → ℂ}
    (hz : z ∈ sectionZero) : scale c z ∈ sectionZero := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have := weightedNorm_scale hc z
    rw [h, weightedNorm_zero] at this
    exact (mul_pos hc (weightedNorm_pos hz.1)).ne' this.symm
  · have e : scale c z 2 = ((c ^ 3 : ℝ) : ℂ) * z 2 := by simp [scale]
    rw [e]
    exact ofReal_mul_mem_walls (by positivity) hz.2.1
  · have := (hamMax_smul_scale_and_tau one_mem_VT hc z).1
    rw [one_smul, hz.2.2, mul_zero] at this
    exact this

/-- `φ(F z)/φ(z) → r_scale` as `z → ang qOutCart` on the section (rescale by `φ(qOutCart)`). -/
private lemma l5g_tendsto_ratio_ang :
    Tendsto l5g_ratio (𝓝[sectionZero] (ang qOutCart)) (𝓝 rScale) := by
  set c := weightedNorm qOutCart
  have hc : 0 < c := weightedNorm_pos qOutCart_ne_zero
  have hsc : scale c (ang qOutCart) = qOutCart := scale_weightedNorm_ang qOutCart_ne_zero
  have hcont : Tendsto (scale c) (𝓝[sectionZero] (ang qOutCart)) (𝓝[sectionZero] qOutCart) := by
    have h : ContinuousWithinAt (scale c) sectionZero (ang qOutCart) :=
      (continuous_scale.comp (continuous_const.prodMk continuous_id)).continuousWithinAt
    have := h.tendsto_nhdsWithin (fun z hz ↦ l5g_scale_mem_sectionZero hc hz)
    rwa [hsc] at this
  refine (l5g_tendsto_ratio_qOutCart.comp hcont).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact l5g_ratio_scale hc hz.1

/-- The quotient map `Ξ_𝒲 → Ξ_𝒲/V_T` is open (`V_T` acts by homeomorphisms). -/
private lemma l5g_isOpenMap_mk : IsOpenMap (Quotient.mk'' : XiW → XiWQuot) := by
  have : ContinuousConstSMul (rootsOfUnity 3 ℂ) XiW :=
    ⟨fun g ↦ continuous_induced_rng.2 (by
      have e : (Subtype.val ∘ fun x : XiW ↦ g • x) =
          fun x : XiW ↦ ((g : ℂˣ) : ℂ) • (x : Fin 3 → ℂ) := rfl
      rw [e]
      exact (continuous_const_smul ((g : ℂˣ) : ℂ)).comp continuous_subtype_val)⟩
  exact isOpenMap_quotient_mk'_mul

/-- **The radial factor is continuous at `q_out`.** Proof, in the chart of Chapter 13
(`SmoothedPolygons/Ch13/Jacobian.lean`: `chartCart`, `chartOf`, `chartMap`, the chart of Lemma
13.5.5):
* `ρ([z]) = φ(F z)/φ(z)` at every point `z` of the section, a ratio invariant under the virial
  group (`l5g_radialFactor_ang`, `l5g_ratio_scale`);
* near `qOutCart` on the section, `z` rescaled by `-1/Re z₁` is the chart point
  `chartCart (chartOf z)` (`H_F⁺ = 0` gives `z₃ = 2(pc + d)`), and `chartOf` is continuous at
  `qOutCart` (`eventually_contDiffAt_chartOf`), with `chartOf qOutCart = x_out`;
* near `x_out` the first control of `chartCart x` is `ζ` (`z₃ ∈ ℝ_{<0}` and `Im z₂ > 0`; Lemma
  13.2.6) and its first switching time `T` is read off the first coordinate `m = chartMap x 0` of
  the chart map, `T = (p + √3 - m + √3 p m)/(1 - √3 m)` with `p = x 0`; `chartMap` is `C¹` at
  `x_out` (`contDiffAt_chartMap`: there the switching time is the simple root of the switching
  function from `ζ` to `1`, by the implicit function theorem), so `x ↦ F(chartCart x)` is
  continuous at `x_out`;
* the quotient map `Ξ_𝒲 → Ξ_𝒲/V_T` is open, which carries the continuity on representatives to
  `Ξ_{𝒲,0}/V_T`.

Departure from the route first planned for this lemma (the cell coordinates of the open first box,
`cellClass` with inverse `cellCoords`, and `continuousAt_firstSwitchTime_of_ne_zero` at `pOut`):
that route needs the continuity of the inverse of `cellClass` on `openCellOne`, which is not
stated anywhere, and the non-vanishing of `Δ_{A,0}`, `Δ_{B,1}`, `res_AB` at `pOut`, still to be
certified; the chart of Chapter 13 supplies the local inverse and the continuity of the switching
time at `q_out`, both proved. The idea is the same (first control `ζ`, simple root). -/
theorem continuousAt_radialFactor_qOut0 : ContinuousAt radialFactor qOut0 := by
  change Tendsto radialFactor (𝓝 qOut0) (𝓝 (radialFactor qOut0))
  rw [radialFactor_qOut0]
  intro U hU
  rw [Filter.mem_map]
  obtain ⟨V, hV, hVU⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 (l5g_tendsto_ratio_ang hU)
  set ξ₀ : XiW := ⟨ang qOutCart, ang_qOutCart_mem_XiW.1⟩
  have hN : {ξ : XiW | (ξ : Fin 3 → ℂ) ∈ V} ∈ 𝓝 ξ₀ :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds hV
  have hM : (Quotient.mk'' : XiW → XiWQuot) '' {ξ : XiW | (ξ : Fin 3 → ℂ) ∈ V} ∈ 𝓝 qOut0.1 :=
    l5g_isOpenMap_mk.image_mem_nhds hN
  filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds hM] with x hx
  obtain ⟨ξ, hξV, hξx⟩ := hx
  have hmem : (ξ : Fin 3 → ℂ) ∈ Xi ∧ (ξ : Fin 3 → ℂ) 2 ∈ walls := ξ.2
  have hH : hamMax (ξ : Fin 3 → ℂ) = 0 := by
    have := x.2
    rw [← hξx] at this
    exact this
  have hsec : (ξ : Fin 3 → ℂ) ∈ sectionZero := ⟨ne_zero_of_mem_Xi hmem.1, hmem.2, hH⟩
  have h1 := hVU ⟨hξV, hsec⟩
  have hφ : weightedNorm (ξ : Fin 3 → ℂ) = 1 := hmem.1
  simp only [mem_preimage, l5g_ratio, hφ, div_one] at h1 ⊢
  rw [l5g_radialFactor_mk hξx.symm]
  exact h1

/-- The iterates of `F` stay in the section and their classes are the iterates of `F_ang`
(`poincare_mem_sectionZero`, `poincareAngZero_classOf`). -/
theorem classOf_poincare_iterate {z : Fin 3 → ℂ} (hz : z ∈ sectionZero) (k : ℕ) :
    poincare^[k] z ∈ sectionZero ∧ classOf (poincare^[k] z) = poincareAngZero^[k] (classOf z) := by
  induction k with
  | zero => exact ⟨hz, rfl⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact ⟨poincare_mem_sectionZero ih.1, by rw [← poincareAngZero_classOf ih.1, ih.2]⟩

/-! ### The Hamiltonian along a trajectory -/

/-- `H_F(·, u)` is continuous. -/
private lemma l5g_continuous_ham (u : ℂ) : Continuous fun z : Fin 3 → ℂ ↦ ham z u := by
  simp only [ham, RR]
  fun_prop

/-- `H_F⁺` is continuous. -/
private lemma l5g_continuous_hamMax : Continuous hamMax :=
  (l5g_continuous_ham 1).max ((l5g_continuous_ham ζ).max (l5g_continuous_ham _))

/-- `H_F⁺(0) = 0`. -/
private lemma l5g_hamMax_zero : hamMax 0 = 0 := by
  simp [hamMax, ham, RR]

/-- The iterates of `F` from `z ≠ 0` are `≠ 0` (`poincare_ne_zero`). -/
private lemma l5g_iterate_ne_zero {z : Fin 3 → ℂ} (hz : z ≠ 0) (k : ℕ) : poincare^[k] z ≠ 0 := by
  induction k with
  | zero => exact hz
  | succ k ih => rw [Function.iterate_succ_apply']; exact poincare_ne_zero ih

/-- `H_F⁺` is constant along the iterates of `F` (`hamMax_poincare`). -/
private lemma l5g_hamMax_iterate {z : Fin 3 → ℂ} (hz : z ≠ 0) (k : ℕ) :
    hamMax (poincare^[k] z) = hamMax z := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', hamMax_poincare (l5g_iterate_ne_zero hz k), ih]

/-- **A trajectory tending to the singular locus has vanishing Hamiltonian** (REPORT.md, E80:
the basin theorem is about `Ξ_{𝒲,0}`). `H_F⁺(F^k z) = H_F⁺(z)` (`hamMax_poincare`), and `H_F⁺` is
continuous with `H_F⁺(0) = 0`, so `H_F⁺(z) = lim H_F⁺(F^k z) = 0`. (This is the scaling argument
`H_F⁺(w) = φ(w)³ H_F⁺(ang w)` with `H_F⁺` bounded on the compact `Ξ`, in its simplest form.) -/
theorem hamMax_eq_zero_of_tendsto_zero {z : Fin 3 → ℂ} (hz : z ≠ 0)
    (h : Tendsto (fun k : ℕ ↦ poincare^[k] z) atTop (𝓝 0)) : hamMax z = 0 := by
  have h1 : Tendsto (fun k : ℕ ↦ hamMax (poincare^[k] z)) atTop (𝓝 (hamMax 0)) :=
    (l5g_continuous_hamMax.tendsto 0).comp h
  simp only [l5g_hamMax_iterate hz, l5g_hamMax_zero] at h1
  exact tendsto_nhds_unique tendsto_const_nhds h1

/-! ### Facts for Theorem 16.2.1 -/

private lemma l5g_continuous_tau : Continuous tau := by
  refine continuous_pi fun i ↦ ?_
  fin_cases i <;> simp only [tau, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> fun_prop

private lemma l5g_tau_zero : tau 0 = 0 := by
  funext i; fin_cases i <;> simp [tau]

/-- `q_in` is a fixed point of `F_ang` (Lemma 13.5.2). -/
private lemma l5g_poincareAngZero_qIn0 : poincareAngZero qIn0 = qIn0 := by
  have h : qIn ∈ {x : XiWQuot | poincareAngQuot x = x ∧ hamMaxQuot x = 0} := by
    rw [lemma13_5_2.1]; exact Or.inr rfl
  exact Subtype.ext h.1

/-- `τ(q_in) = q_out` (`tauQuot_qOut`, `τ` an involution). -/
private lemma l5g_tauZero_qIn0 : tauZero qIn0 = qOut0 := by
  have h : tauZero qOut0 = qIn0 := Subtype.ext tauQuot_qOut
  rw [← h]
  exact continuous_involutive_tauZero.2 qOut0

/-- **The inward statement of Theorem 16.2.1** (the book's route, module docstring): a trajectory
`F^k(z⁰) → 0` with `z⁰ ≠ 0` on a wall has `H_F⁺ = 0`; if its class `x` were not `q_in`, then
`F_ang^k(x) → q_out` (Theorem 16.1.1), `ρ(F_ang^k x) → r_scale > 1`, so `φ(F^k z⁰)` would be
eventually nondecreasing and positive, against `F^k(z⁰) → 0`. -/
private lemma l5g_inward (h₁ : DOutContracts) (h₂ : CellTwoEntersDOut) (h₃ : BoxSubclaims)
    {z₀ : Fin 3 → ℂ} (hz : z₀ ≠ 0) (hw : z₀ 2 ∈ walls)
    (ht : Tendsto (fun k : ℕ ↦ poincare^[k] z₀) atTop (𝓝 0)) (k : ℕ) :
    poincare^[k] z₀ ∈ sectionZero ∧ classOf (poincare^[k] z₀) = qIn0 := by
  have hs : z₀ ∈ sectionZero := ⟨hz, hw, hamMax_eq_zero_of_tendsto_zero hz ht⟩
  have hx : classOf z₀ = qIn0 := by
    by_contra hne
    have hρ : Tendsto (fun k ↦ radialFactor (poincareAngZero^[k] (classOf z₀))) atTop
        (𝓝 rScale) := by
      rw [← radialFactor_qOut0]
      exact continuousAt_radialFactor_qOut0.tendsto.comp (theorem16_1_1 h₁ h₂ h₃ _ hne)
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hρ.eventually (lt_mem_nhds rScale_spec.1))
    have hstep : ∀ j, weightedNorm (poincare^[N + j] z₀) ≤
        weightedNorm (poincare^[N + j + 1] z₀) := by
      intro j
      obtain ⟨hsec, hcl⟩ := classOf_poincare_iterate hs (N + j)
      rw [Function.iterate_succ_apply', weightedNorm_poincare_eq hsec, hcl]
      have h1 := hN (N + j) (Nat.le_add_right N j)
      have h0 := (weightedNorm_pos hsec.1).le
      nlinarith
    have hmono : ∀ j, weightedNorm (poincare^[N] z₀) ≤ weightedNorm (poincare^[N + j] z₀) := by
      intro j
      induction j with
      | zero => exact le_rfl
      | succ j ih => exact ih.trans (hstep j)
    have hφ : Tendsto (fun k ↦ weightedNorm (poincare^[k] z₀)) atTop (𝓝 0) := by
      have := (continuous_weightedNorm.tendsto 0).comp ht
      rwa [weightedNorm_zero] at this
    have hpos := weightedNorm_pos (l5g_iterate_ne_zero hz N)
    obtain ⟨M, hM⟩ := eventually_atTop.1 (hφ.eventually (gt_mem_nhds hpos))
    have h1 := hM (N + M) (Nat.le_add_left M N)
    linarith [hmono M]
  refine ⟨(classOf_poincare_iterate hs k).1, ?_⟩
  rw [(classOf_poincare_iterate hs k).2, hx]
  exact Function.iterate_fixed l5g_poincareAngZero_qIn0 k

end TriFuller

open TriFuller

/-- **Theorem 16.2.1** (`thm:outward-fuller`, TeX 12754–12761). "Consider the Fuller–Poincaré
dynamical system `F` on `(ℂ³ ∖ 0)/V_T`. Every outward trajectory that emanates from the singular
locus has all its switching points in the set `ℝ_{>0} × {q_out}` modulo `V_T`. Every inward
trajectory to the singular locus has all its switching points in the set `ℝ_{>0} × {q_in}` modulo
`V_T`."

Formalized: (outward) if `z_k ≠ 0`, `F(z_{k+1}) = z_k` and `z_k → 0` as `k → ∞` (the switching
points, going back in time, tend to `0`), then every `z_k` lies in the section (with `H_F⁺ = 0`) and
represents `q_out`; (inward) if `z⁰ ≠ 0` lies on a wall and `F^k(z⁰) → 0`, then every `F^k(z⁰)` lies
in the section and represents `q_in`. It depends on Theorem 16.1.1, hence on its three numerical
hypotheses.

Proof (the book's, module docstring): inward: `H_F⁺(z⁰) = 0` (`hamMax_eq_zero_of_tendsto_zero`); let
`x = classOf z⁰`; if `x ≠ q_in`, `F_ang^k(x) → q_out` (`theorem16_1_1`), so
`ρ(F_ang^k x) → r_scale > 1` (`continuousAt_radialFactor_qOut0`, `radialFactor_qOut0`) and
`φ(F^k z⁰) = φ(z⁰) ∏_{j<k} ρ(F_ang^j x)` (`weightedNorm_poincare_eq`, `classOf_poincare_iterate`)
is eventually nondecreasing and positive (it grows geometrically), against `F^k z⁰ → 0`; so
`x = q_in`, a fixed point (`l5g_inward`). Outward, by time reversal: each `z_k = F(z_{k+1})` lies on
a wall (`F` lands on the walls) and has `H_F⁺(z_k) = H_F⁺(z_{k+j}) → H_F⁺(0) = 0`, so lies in the
section; `w_k = τ(z_k)` satisfies `F(w_k) = w_{k+1}` (`poincare_tau_poincare` at the switching
point `z_{k+1} = F(z_{k+2})`) and `w_k → 0`, so `[w_k] = q_in` by the inward case and
`[z_k] = τ q_in = q_out`. -/
theorem theorem16_2_1 (h₁ : DOutContracts) (h₂ : CellTwoEntersDOut) (h₃ : BoxSubclaims) :
    (∀ z : ℕ → Fin 3 → ℂ, (∀ k, z k ≠ 0) → (∀ k, poincare (z (k + 1)) = z k) →
      Tendsto z atTop (𝓝 0) → ∀ k, z k ∈ sectionZero ∧ classOf (z k) = qOut0) ∧
    ∀ z₀ : Fin 3 → ℂ, z₀ ≠ 0 → z₀ 2 ∈ walls →
      Tendsto (fun k : ℕ ↦ poincare^[k] z₀) atTop (𝓝 0) →
      ∀ k, poincare^[k] z₀ ∈ sectionZero ∧ classOf (poincare^[k] z₀) = qIn0 := by
  refine ⟨fun z hz hF ht ↦ ?_, fun z₀ hz hw ht ↦ l5g_inward h₁ h₂ h₃ hz hw ht⟩
  -- the `z_k = F(z_{k+1})` lie on the walls, and `H_F⁺` is constant along the sequence
  have hwall : ∀ k, z k 2 ∈ walls := fun k ↦ by
    rw [← hF k]; exact poincare_mem_walls (hz (k + 1))
  have hconst : ∀ k j, hamMax (z k) = hamMax (z (j + k)) := by
    intro k j
    induction j with
    | zero => rw [zero_add]
    | succ j ih =>
      rw [ih, ← hF (j + k), hamMax_poincare (hz _), show j + 1 + k = j + k + 1 by omega]
  have hH : ∀ k, hamMax (z k) = 0 := by
    intro k
    have h1 : Tendsto (fun j ↦ hamMax (z (j + k))) atTop (𝓝 (hamMax 0)) :=
      (l5g_continuous_hamMax.tendsto 0).comp ((tendsto_add_atTop_iff_nat k).2 ht)
    simp only [← hconst k, l5g_hamMax_zero] at h1
    exact tendsto_nhds_unique tendsto_const_nhds h1
  have hsec : ∀ k, z k ∈ sectionZero := fun k ↦ ⟨hz k, hwall k, hH k⟩
  -- time reversal: `w_k = τ(z_k)` is a forward orbit, `F(w_k) = w_{k+1}`
  have hτF : ∀ k, poincare (tau (z k)) = tau (z (k + 1)) := by
    intro k
    have hsw : IsSwitchingPoint (z (k + 1)) := by
      rw [← hF (k + 1)]; exact isSwitchingPoint_poincare (hz _)
    have := poincare_tau_poincare (hz (k + 1)) hsw
    rwa [hF k] at this
  have hτiter : ∀ k, poincare^[k] (tau (z 0)) = tau (z k) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, hτF]
  have hτt : Tendsto (fun k ↦ poincare^[k] (tau (z 0))) atTop (𝓝 0) := by
    simp only [hτiter]
    have := (l5g_continuous_tau.tendsto 0).comp ht
    rwa [l5g_tau_zero] at this
  have hin := l5g_inward h₁ h₂ h₃ (tau_ne_zero (hz 0)) (tau_mem_sectionZero (hsec 0)).2.1 hτt
  intro k
  refine ⟨hsec k, ?_⟩
  have h1 := (hin k).2
  rw [hτiter] at h1
  have h2 := tauZero_classOf (tau_mem_sectionZero (hsec k))
  rw [tau_tau, h1, l5g_tauZero_qIn0] at h2
  exact h2.symm

end SmoothedPolygons
