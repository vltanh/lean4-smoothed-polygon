module

public import SmoothedPolygons.Ch13.Jacobian
public import Basic.Dynamics.LinearizedStability
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Algebra.MulAction

/-!
# Chapter 13: Lemma 13.5.5 (stability of `q_out`, instability of `q_in`)

Lemma 13.5.5 of Hales–Vajjha, *Packings of Smoothed Polygons* (`lem:eigenvalues`,
TeX 11433–11453): on `Ξ_{𝒲,0}/V_T`, `q_out` is an asymptotically stable fixed point of `F_ang`
and `q_in` is unstable. Chapter 16 relies on it (Theorem 16.1.1, TeX 12596–12598). Chapter 14
(Theorem 14.3.3, TeX 11911–11917) needs more than this lemma: the linearization of `F` at `q_out`
on the exceptional divisor (three eigenvalues of modulus `< 1`; the bound `0.1` is quoted at
TeX 11961), transferred to its own coordinates. It relies on the Jacobian lemmas of
`SmoothedPolygons/Ch13/Jacobian.lean` (`l4st_hasFDerivAt_chartMap`,
`l4st_charpoly_jacobianOut_roots`) with the normalization map `chartOf`
(`l4f_chartOf_chartCart`, `l4f_chartMap_eventuallyEq_chartOf`, `l4f_contDiffAt_chartOf`), not on
`lemma13_5_5`.

The book's proof, and its formalization:
1. "It suffices to show that `q_out` is asymptotically stable. … An open neighborhood of `q_out`
   in `Ξ_{𝒲,0}/V_T` is diffeomorphic to an open subset of `ℝ³`. An explicit calculation of the
   eigenvalues of the Jacobian matrix in terms of local coordinates centered at `q_out` gives the
   result": the chart and the certified Jacobian (`SmoothedPolygons/Ch13/Jacobian.lean`:
   `l4st_exists_chart`, `l4st_chartMap_xOut`, `l4st_hasFDerivAt_chartMap`,
   `l4st_charpoly_jacobianOut`, `l4st_charpoly_jacobianOut_roots`), linearized stability for maps
   (`Function.isAsymptoticallyStable_of_hasFDerivAt`, `Basic/Dynamics/LinearizedStability.lean`;
   the eigenvalues of `Matrix.toLin' M` are the roots of `M.charpoly`, `LinearMap.charpoly_toLin'`)
   and the transfer through the chart (`Function.IsAsymptoticallyStable.of_conj`).
2. "The second assertion follows from the first, because `q_in` is obtained by time reversal from
   `q_out`": `τ ∘ F_ang` is an involution near `q_out` and near `q_in`
   (`l4st_tauZero_poincareAngZero_involutive`, from `F(τ F(z)) = τ(z)` at genuine switching points,
   `l4st_poincare_tau_poincare`, Lemmas 13.2.3 and 13.2.5; not spelled out in the book, inventory
   gap 12), `τ(q_out) = q_in` (`l4st_tauQuot_qOut`), and an asymptotically stable fixed point is
   carried by such a time reversal to an unstable one
   (`Function.IsAsymptoticallyStable.isUnstable_of_involutive`). Its hypotheses: `Ξ_{𝒲,0}/V_T` is
   compact Hausdorff (`l4st_topology_XiWQuot`; a closed subset of a compact Hausdorff space), hence
   locally compact; `F_ang = e⁻¹ ∘ chartMap ∘ e` near `q_out` is continuous there
   (`l4st_contDiffAt_chartMap`, and `ContDiffAt.eventually` for the points near `x_out`); `τ` is a
   continuous involution (`l4st_tauZero_continuous_involutive`); and `q_out` is not isolated in
   `Ξ_{𝒲,0}/V_T` (the chart `e` maps a neighborhood of `q_out` onto a neighborhood of `x_out` in
   `ℝ³`).
-/

@[expose] public section

namespace SmoothedPolygons

open Complex Set Filter Topology

namespace TriFuller

/-! ### Helpers: `τ` and the angular projection -/

/-- `φ(τ z) = φ(z)`. -/
private lemma l4k_weightedNorm_tau (z : Fin 3 → ℂ) : weightedNorm (tau z) = weightedNorm z := by
  simp [weightedNorm, tau]

/-- `τ` commutes with the virial rescalings. -/
private lemma l4k_tau_scale (r : ℝ) (z : Fin 3 → ℂ) : tau (scale r z) = scale r (tau z) := by
  funext i; fin_cases i <;> simp [tau, scale]

/-- `τ` commutes with the angular projection. -/
private lemma l4k_tau_ang (z : Fin 3 → ℂ) : tau (ang z) = ang (tau z) := by
  rw [ang, ang, l4k_weightedNorm_tau, l4k_tau_scale]

private lemma l4k_ne_zero_of_mem_Xi {ξ : Fin 3 → ℂ} (hξ : ξ ∈ Xi) : ξ ≠ 0 := by
  rintro rfl
  have h : weightedNorm 0 = 1 := hξ
  simp [weightedNorm] at h

private lemma l4k_ang_of_mem_Xi {ξ : Fin 3 → ℂ} (hξ : ξ ∈ Xi) : ang ξ = ξ := by
  have h := (l4st_weightedNorm_ang_scale one_pos hξ).2
  have h1 : scale 1 ξ = ξ := by funext i; fin_cases i <;> simp [scale]
  rwa [h1] at h

private lemma l4k_tau_ne_zero {z : Fin 3 → ℂ} (hz : z ≠ 0) : tau z ≠ 0 := by
  intro h
  apply hz
  rw [← l4st_tau_tau z, h]
  funext i; fin_cases i <;> simp [tau]

/-- **`τ ∘ F_ang` is an involution at genuine switching points**, on representatives in `Ξ`:
`τ(π_ang F(τ(π_ang F(ξ)))) = ξ` when the first control of `ξ` is not its most recent control
(`l4st_poincare_tau_poincare`, with `τ ∘ π_ang = π_ang ∘ τ` and `l4st_ang_poincare_ang`). -/
private lemma l4k_tau_ang_poincare_tau_ang_poincare {ξ : Fin 3 → ℂ} (hξ : ξ ∈ Xi)
    (h : ¬ IsMostRecentControl ξ (firstControl ξ)) :
    tau (ang (poincare (tau (ang (poincare ξ))))) = ξ := by
  have hξ0 := l4k_ne_zero_of_mem_Xi hξ
  rw [l4k_tau_ang (poincare ξ),
    l4st_ang_poincare_ang (l4k_tau_ne_zero (l4st_poincare_ne_zero hξ0)),
    l4st_poincare_tau_poincare hξ0 h, l4k_tau_ang, l4st_tau_tau, l4k_ang_of_mem_Xi hξ]

/-! ### Helpers: genuine switching points -/

private lemma l4k_sqrt3_mul_self : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)

private lemma l4k_ζ_re : ζ.re = -1 / 2 := by rw [l4st_ζ_eq]

private lemma l4k_ζ_im : ζ.im = √3 / 2 := by rw [l4st_ζ_eq]

private lemma l4k_ζ_sq_re : (ζ ^ 2).re = -1 / 2 := by
  rw [sq, Complex.mul_re, l4k_ζ_re, l4k_ζ_im]
  linear_combination (-1 / 4 : ℝ) * l4k_sqrt3_mul_self

private lemma l4k_ζ_sq_im : (ζ ^ 2).im = -(√3 / 2) := by
  rw [sq, Complex.mul_im, l4k_ζ_re, l4k_ζ_im]
  ring

/-- A real cubic `a t + b t² + c t³` with `a ≠ 0` takes a negative value in every interval
`[-ε, ε]`. -/
private lemma l4k_exists_cubic_neg {a b c ε : ℝ} (ha : a ≠ 0) (hε : 0 < ε) :
    ∃ t ∈ Icc (-ε) ε, a * t + b * t ^ 2 + c * t ^ 3 < 0 := by
  set M := |b| + |c| + 1 with hM
  have hM0 : 0 < M := by rw [hM]; positivity
  set δ := min ε (min 1 (|a| / (2 * M))) with hδ
  have hδ0 : 0 < δ := lt_min hε (lt_min one_pos (div_pos (abs_pos.2 ha) (by linarith)))
  have hδε : δ ≤ ε := min_le_left _ _
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hδa : M * δ ≤ |a| / 2 := by
    have : δ ≤ |a| / (2 * M) := (min_le_right _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ (by linarith)] at this
    linarith
  -- the quadratic and cubic terms are at most `M δ² ≤ |a| δ / 2` in absolute value
  have hbound : ∀ t : ℝ, |t| = δ → |b * t ^ 2 + c * t ^ 3| ≤ |a| / 2 * δ := by
    intro t ht
    have h2 : |t| ^ 2 = δ ^ 2 := by rw [ht]
    have h3 : |t| ^ 3 ≤ δ ^ 2 := by
      rw [ht, pow_succ]
      exact mul_le_of_le_one_right (by positivity) hδ1
    calc |b * t ^ 2 + c * t ^ 3| ≤ |b| * |t| ^ 2 + |c| * |t| ^ 3 := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_pow, abs_pow]
      _ ≤ |b| * δ ^ 2 + |c| * δ ^ 2 := by
          rw [h2]; gcongr
      _ ≤ M * δ * δ := by rw [hM]; nlinarith [mul_self_nonneg δ]
      _ ≤ |a| / 2 * δ := mul_le_mul_of_nonneg_right hδa hδ0.le
  rcases lt_or_gt_of_ne ha with ha' | ha'
  · refine ⟨δ, ⟨by linarith, hδε⟩, ?_⟩
    have h := (abs_le.1 (hbound δ (abs_of_pos hδ0))).2
    rw [abs_of_neg ha'] at h
    nlinarith
  · refine ⟨-δ, ⟨by linarith, by linarith⟩, ?_⟩
    have h := (abs_le.1 (hbound (-δ) (by rw [abs_neg, abs_of_pos hδ0]))).2
    rw [abs_of_pos ha'] at h
    nlinarith

/-- `H_F(w, ζ) - H_F(w, ζ²) = √3 Im w₃`. -/
private lemma l4k_ham_ζ_sub (w : Fin 3 → ℂ) : ham w ζ - ham w (ζ ^ 2) = √3 * (w 2).im := by
  simp only [ham, RR, Complex.mul_re, Complex.conj_re, Complex.conj_im, l4k_ζ_re, l4k_ζ_im,
    l4k_ζ_sq_re, l4k_ζ_sq_im]
  ring

/-- `Im z₃(t, z⁰, u) = Im z₃⁰ + t Im z₂⁰ + (t²/2) Im z₁⁰ - (t³/6) Re u`. -/
private lemma l4k_flow_two_im (t : ℝ) (z : Fin 3 → ℂ) (u : ℂ) :
    (flow t z u 2).im = (z 2).im + (z 1).im * t + (z 0).im * t ^ 2 / 2 - u.re * t ^ 3 / 6 := by
  simp [flow, Complex.mul_im, Complex.mul_re, pow_succ]
  ring

/-- **Genuine switching points.** At a point `z⁰` with `z₃⁰ ∈ ℝ_{<0}` and `Im z₂⁰ ≠ 0`, the first
control is not the most recent control. (The control `1` is not optimal at `t = 0`; for `ζ` and
`ζ²` the switching function between them, `√3 Im z₃(t)`, has the simple root `t = 0`, so it has
opposite signs for small `t > 0` and small `t < 0`.) -/
private lemma l4k_not_isMostRecentControl {z : Fin 3 → ℂ} (h3 : (z 2).im = 0)
    (h3' : (z 2).re < 0) (h2 : (z 1).im ≠ 0) {u : ℂ} (hu : IsFirstControl z u) :
    ¬ IsMostRecentControl z u := by
  rintro ⟨-, ε₂, hε₂, hmr⟩
  obtain ⟨huV, ε₁, hε₁, hfc⟩ := hu
  have hζV : ζ ∈ VT := by simp [VT]
  have hζ2V : ζ ^ 2 ∈ VT := by simp [VT]
  have h3pos : 0 < √3 := by positivity
  -- the control is optimal on `[-ε, ε]`
  have hopt : ∀ t ∈ Icc (-min ε₁ ε₂) (min ε₁ ε₂), ∀ v ∈ VT,
      ham (flow t z u) v ≤ ham (flow t z u) u := by
    intro t ht v hv
    rcases le_total 0 t with h | h
    · exact hfc t ⟨h, ht.2.trans (min_le_left _ _)⟩ v hv
    · exact hmr t ⟨(neg_le_neg (min_le_right _ _)).trans ht.1, h⟩ v hv
  have hε : 0 < min ε₁ ε₂ := lt_min hε₁ hε₂
  rcases (show u = 1 ∨ u = ζ ∨ u = ζ ^ 2 by simpa [VT] using huV) with rfl | rfl | rfl
  · -- `1` is not optimal at `t = 0`: `H_F(z⁰, ζ) - H_F(z⁰, 1) = -(3/2) Re z₃⁰ > 0`
    have h := hfc 0 ⟨le_rfl, hε₁.le⟩ ζ hζV
    rw [l4st_flow_zero] at h
    simp only [ham, RR, Complex.mul_re, Complex.conj_re, Complex.conj_im, l4k_ζ_re, l4k_ζ_im,
      h3, map_one, Complex.one_re, Complex.one_im] at h
    linarith
  · -- `Im z₃(t) ≥ 0` on `[-ε, ε]`, against its simple root at `0`
    obtain ⟨t, ht, hneg⟩ := l4k_exists_cubic_neg (b := (z 0).im / 2) (c := 1 / 12) h2 hε
    have h := hopt t ht (ζ ^ 2) hζ2V
    have e := l4k_ham_ζ_sub (flow t z ζ)
    rw [l4k_flow_two_im, h3, l4k_ζ_re] at e
    nlinarith [mul_lt_mul_of_pos_left hneg h3pos]
  · obtain ⟨t, ht, hneg⟩ := l4k_exists_cubic_neg (a := -(z 1).im) (b := -((z 0).im / 2))
      (c := -(1 / 12)) (neg_ne_zero.2 h2) hε
    have h := hopt t ht ζ hζV
    have e := l4k_ham_ζ_sub (flow t z (ζ ^ 2))
    rw [l4k_flow_two_im, h3, l4k_ζ_sq_re] at e
    nlinarith [mul_lt_mul_of_pos_left hneg h3pos]

/-- A point of the walls with negative real part lies on `𝒲₀ = ℝ_{≤0}`: it is real. -/
private lemma l4k_im_eq_zero_of_mem_walls {w : ℂ} (hw : w ∈ walls) (hre : w.re < 0) :
    w.im = 0 := by
  rcases hw with (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩) | ⟨s, hs, rfl⟩
  · simp
  · rw [pow_one, Complex.re_ofReal_mul, l4k_ζ_re] at hre
    exfalso; linarith
  · rw [Complex.re_ofReal_mul, l4k_ζ_sq_re] at hre
    exfalso; linarith

/-! ### Helpers: a neighborhood of `q_out` and `q_in` -/

/-- The open set of `Ξ_𝒲` where `Re ξ₃ < 0` and `Im ξ₂ ≠ 0`. -/
private def l4k_U : Set XiW := {ξ | ((ξ : Fin 3 → ℂ) 2).re < 0 ∧ ((ξ : Fin 3 → ℂ) 1).im ≠ 0}

private lemma l4k_isOpen_U : IsOpen l4k_U := by
  have h2 : Continuous fun ξ : XiW ↦ ((ξ : Fin 3 → ℂ) 2).re :=
    Complex.continuous_re.comp ((continuous_apply 2).comp continuous_subtype_val)
  have h1 : Continuous fun ξ : XiW ↦ ((ξ : Fin 3 → ℂ) 1).im :=
    Complex.continuous_im.comp ((continuous_apply 1).comp continuous_subtype_val)
  exact (isOpen_lt h2 continuous_const).inter (isOpen_ne_fun h1 continuous_const)

/-- On `l4k_U`, `τ ∘ F_ang` is an involution. -/
private lemma l4k_involutive_of_mem_U {ξ : XiW} (hξ : ξ ∈ l4k_U) :
    tauXiW (poincareAng (tauXiW (poincareAng ξ))) = ξ := by
  obtain ⟨hXi, hW⟩ := ξ.2
  have h3 : ((ξ : Fin 3 → ℂ) 2).im = 0 := l4k_im_eq_zero_of_mem_walls hW hξ.1
  have hfc := l4st_isFirstControl_firstControl (l4k_ne_zero_of_mem_Xi hXi)
  exact Subtype.ext (l4k_tau_ang_poincare_tau_ang_poincare hXi
    (l4k_not_isMostRecentControl h3 hξ.1 hξ.2 hfc))

/-- `Im (q_out)₂ ≠ 0`: `Im z₂ = (1 - 3r - 2r² - 3r³ + r⁴)/(3(1 + r + r³ + r⁴))` at
`r = r_scale ∈ (6.27, 6.28)`. -/
private lemma l4k_qOutCart_one_im : (qOutCart 1).im ≠ 0 := by
  obtain ⟨h1, h2⟩ := l4st_rScale_bounds
  have hnum : 0 < 1 - 3 * rScale - 2 * rScale ^ 2 - 3 * rScale ^ 3 + rScale ^ 4 := by
    nlinarith [pow_pos (show (0 : ℝ) < rScale by linarith) 2,
      pow_pos (show (0 : ℝ) < rScale by linarith) 3]
  have hden : 0 < 3 * (1 + rScale + rScale ^ 3 + rScale ^ 4) := by positivity
  have : (qOutCart 1).im =
      (1 - 3 * rScale - 2 * rScale ^ 2 - 3 * rScale ^ 3 + rScale ^ 4) /
        (3 * (1 + rScale + rScale ^ 3 + rScale ^ 4)) := by
    simp only [qOutCart, equilExact, Matrix.cons_val, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re]
    ring
  rw [this]
  exact (div_pos hnum hden).ne'

/-- The representative `π_ang(qOutCart)` of `q_out` lies in `l4k_U`, and so does its image by
`τ`, the representative of `q_in`. -/
private lemma l4k_ang_qOutCart_mem_U :
    (⟨ang qOutCart, l4st_ang_qOutCart_mem.1⟩ : XiW) ∈ l4k_U ∧
      (⟨ang (tau qOutCart), l4st_ang_qOutCart_mem.2⟩ : XiW) ∈ l4k_U := by
  obtain ⟨h0, -, h2⟩ := l4st_qOutCart_normalization
  have hne : qOutCart ≠ 0 := by
    intro h; rw [h] at h0; simp at h0
  have hφ := inv_pos.2 (l4st_weightedNorm_pos hne)
  have hre : (ang qOutCart 2).re < 0 := by
    simp only [ang, scale, Matrix.cons_val]
    rw [← Complex.ofReal_pow, Complex.re_ofReal_mul]
    exact mul_neg_of_pos_of_neg (pow_pos hφ 3) h2
  have him : (ang qOutCart 1).im ≠ 0 := by
    simp only [ang, scale, Matrix.cons_val]
    rw [← Complex.ofReal_pow, Complex.im_ofReal_mul]
    exact mul_ne_zero (pow_pos hφ 2).ne' l4k_qOutCart_one_im
  refine ⟨⟨hre, him⟩, ?_⟩
  change (ang (tau qOutCart) 2).re < 0 ∧ (ang (tau qOutCart) 1).im ≠ 0
  rw [← l4k_tau_ang]
  simpa [tau] using And.intro hre him

/-- The image of `l4k_U` in `Ξ_𝒲/V_T` is open (the quotient map by a group action is open). -/
private lemma l4k_isOpen_image_U :
    IsOpen ((Quotient.mk'' : XiW → XiWQuot) '' l4k_U) :=
  isOpenMap_quotient_mk'_mul _ l4k_isOpen_U

/-- The time-reversal identity holds on the points of `Ξ_{𝒲,0}/V_T` over the image of `l4k_U`. -/
private lemma l4k_involutive_of_mem_image {x : XiW0Quot}
    (hx : x.1 ∈ (Quotient.mk'' : XiW → XiWQuot) '' l4k_U) :
    tauZero (poincareAngZero (tauZero (poincareAngZero x))) = x := by
  obtain ⟨ξ, hξ, hξx⟩ := hx
  apply Subtype.ext
  change tauQuot (poincareAngQuot (tauQuot (poincareAngQuot x.1))) = x.1
  rw [← hξx]
  change (Quotient.mk'' (tauXiW (poincareAng (tauXiW (poincareAng ξ)))) : XiWQuot) =
    Quotient.mk'' ξ
  rw [l4k_involutive_of_mem_U hξ]

/-- **Time reversal near the fixed points** (the formal content of "`q_in` is obtained by time
reversal from `q_out`", TeX 11441–11442): `τ ∘ F_ang` is an involution of `Ξ_{𝒲,0}/V_T` near
`q_out` and near `q_in`.

Proof: near `q_out` and near `q_in = τ q_out` every point is a genuine switching point (its first
control is not its most recent control). Both have representatives `ξ ∈ Ξ_𝒲` with
`Re ξ₃ < 0` and `Im ξ₂ ≠ 0` (`Im ξ₂ > 0` from (13.5.1), and `τ` preserves both conditions), an
open set of `Ξ_𝒲` whose image in `Ξ_𝒲/V_T` is open (the quotient map by a group action is open).
On it `ξ₃ ∈ 𝒲₀ = ℝ_{<0}`, so no control of `V_T` is both the first and the most recent control of
`ξ`: the control `1` is not optimal at `t = 0` (`H_F(ξ, ζ) - H_F(ξ, 1) = -(3/2) Re ξ₃ > 0`), and
the switching function between `ζ` and `ζ²`, `H_F(z(t), ζ) - H_F(z(t), ζ²) = √3 Im z₃(t)`, has
the simple root `t = 0` (its derivative there is `√3 Im ξ₂ ≠ 0`), so whichever of the two is
optimal for small `t > 0` is beaten for small `t < 0` (on the wall `𝒲₀` the tie is broken by the
sign of `Im ξ₂`, as in Lemma 13.2.6). There `F(τ F(ξ)) = τ(ξ)` (`l4st_poincare_tau_poincare`),
which passes to the angular map and to the quotient (`τ` commutes with `π_ang`, and
`l4st_ang_poincare_ang`).

The same argument gives the identity on all of the big open cells of Chapter 15
(Definition `def:big:open`, TeX 12104–12110: the points with a representative `z₃ ∈ ℝ_{<0}`,
`Im z₂ ≠ 0`, that is, over the open set above); it is stated here in the neighborhood form that
Lemma 13.5.5 uses, and the cell form belongs with the cells of Chapter 15.
-/
theorem l4st_tauZero_poincareAngZero_involutive :
    (∀ᶠ x in 𝓝 qOut0, tauZero (poincareAngZero (tauZero (poincareAngZero x))) = x) ∧
      ∀ᶠ x in 𝓝 qIn0, tauZero (poincareAngZero (tauZero (poincareAngZero x))) = x := by
  have hmem : ∀ q : XiW0Quot, q.1 ∈ (Quotient.mk'' : XiW → XiWQuot) '' l4k_U →
      ∀ᶠ x in 𝓝 q, tauZero (poincareAngZero (tauZero (poincareAngZero x))) = x := by
    intro q hq
    filter_upwards [(l4k_isOpen_image_U.preimage continuous_subtype_val).mem_nhds hq] with x hx
    exact l4k_involutive_of_mem_image hx
  exact ⟨hmem _ ⟨_, l4k_ang_qOutCart_mem_U.1, rfl⟩, hmem _ ⟨_, l4k_ang_qOutCart_mem_U.2, rfl⟩⟩

end TriFuller

open TriFuller

/-- **Lemma 13.5.5** (`lem:eigenvalues`, TeX 11433–11453). Restrict `F_ang` to the subset
`Ξ_{𝒲,0}/V_T` of `Ξ_𝒲/V_T` on which the Hamiltonian vanishes. On that subset, the fixed point
`q_out` is an asymptotically stable equilibrium, and the fixed point `q_in` is unstable.

Proof: the book's, in the module docstring. The book's numerical eigenvalue computation
("Numerically, the three eigenvalues have absolute value less than `0.1`. The calculations were
made in Mathematica.") is replaced by the exact Jacobian in `ℚ(√3, r_scale)` and a certified bound
on the roots of its characteristic polynomial (`l4st_charpoly_jacobianOut_roots`). -/
theorem lemma13_5_5 :
    Function.IsAsymptoticallyStable poincareAngZero qOut0 ∧
      Function.IsUnstable poincareAngZero qIn0 := by
  obtain ⟨e, he, heq, hconj⟩ := l4st_exists_chart
  -- Step 1: linearized stability in the chart, then transfer through the chart.
  have hchart : Function.IsAsymptoticallyStable chartMap xOut := by
    refine Function.isAsymptoticallyStable_of_hasFDerivAt l4st_chartMap_xOut
      l4st_hasFDerivAt_chartMap fun μ hμ ↦ ?_
    rw [LinearMap.coe_toContinuousLinearMap, Matrix.charpoly_toLin'] at hμ
    exact (l4st_charpoly_jacobianOut_roots μ hμ).trans (by norm_num)
  have hout : Function.IsAsymptoticallyStable poincareAngZero qOut0 :=
    Function.IsAsymptoticallyStable.of_conj e he hconj (heq ▸ hchart)
  refine ⟨hout, ?_⟩
  -- Step 2: time reversal. `Ξ_{𝒲,0}/V_T` is compact Hausdorff, hence locally compact.
  obtain ⟨hcpt, ht2, hcl⟩ := l4st_topology_XiWQuot
  have : CompactSpace XiW0Quot := isCompact_iff_compactSpace.mp hcl.isCompact
  -- `F_ang` is continuous near `q_out`: it is `e⁻¹ ∘ chartMap ∘ e` there.
  have hcm : ∀ᶠ y in 𝓝 (e qOut0), ContinuousAt chartMap y := by
    rw [heq]
    exact (l4st_contDiffAt_chartMap.eventually (by simp)).mono fun y hy ↦ hy.continuousAt
  have hcont : ∀ᶠ x in 𝓝 qOut0, ContinuousAt poincareAngZero x := by
    have hP : ∀ᶠ x in 𝓝 qOut0, x ∈ e.source ∧
        (poincareAngZero x ∈ e.source ∧ e (poincareAngZero x) = chartMap (e x)) ∧
          ContinuousAt chartMap (e x) :=
      (e.open_source.eventually_mem he).and
        (hconj.and ((e.continuousAt he).tendsto.eventually hcm))
    filter_upwards [hP.eventually_nhds] with x hx
    obtain ⟨hxs, ⟨hfs, -⟩, hxc⟩ := hx.self_of_nhds
    have hEq : (e.symm ∘ chartMap ∘ e) =ᶠ[𝓝 x] poincareAngZero := by
      filter_upwards [hx] with y hy
      change e.symm (chartMap (e y)) = poincareAngZero y
      rw [← hy.2.1.2, e.left_inv hy.2.1.1]
    refine ContinuousAt.congr ?_ hEq
    have hsymm : ContinuousAt e.symm (chartMap (e x)) := by
      rw [← (hx.self_of_nhds).2.1.2]
      exact e.continuousAt_symm (e.map_source hfs)
    exact ContinuousAt.comp (f := chartMap ∘ e) hsymm (hxc.comp (e.continuousAt hxs))
  -- `q_out` is not isolated: `e` maps a neighborhood of `q_out` onto a neighborhood of `x_out`.
  have hne : (𝓝[≠] qOut0).NeBot := by
    rw [Filter.neBot_iff]
    intro h
    have hO : IsOpen ({qOut0} : Set XiW0Quot) := (isOpen_singleton_iff_punctured_nhds _).2 h
    have h1 : ({e qOut0} : Set (Fin 3 → ℝ)) ∈ 𝓝 (e qOut0) := by
      simpa using e.image_mem_nhds he (hO.mem_nhds rfl)
    have h2 : 𝓝[≠] (e qOut0) = ⊥ :=
      (isOpen_singleton_iff_punctured_nhds _).1
        (isOpen_iff_mem_nhds.2 fun y hy ↦ by obtain rfl := Set.mem_singleton_iff.1 hy; exact h1)
    exact (Filter.NeBot.ne inferInstance) h2
  obtain ⟨hτc, hττ⟩ := l4st_tauZero_continuous_involutive
  have hτq : tauZero qOut0 = qIn0 := Subtype.ext l4st_tauQuot_qOut
  obtain ⟨h₀, h₁⟩ := l4st_tauZero_poincareAngZero_involutive
  have := hout.isUnstable_of_involutive hcont hτc hττ h₀ (hτq ▸ h₁) hne
  rwa [hτq] at this

end SmoothedPolygons
