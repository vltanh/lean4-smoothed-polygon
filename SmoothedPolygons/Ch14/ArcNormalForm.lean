module

public import SmoothedPolygons.Ch14.ArcCostate
import SmoothedPolygons.Ch7.Isolated.VertexFlow

/-!
# Chapter 14, N4: the normal form of the cleared switching numerators (Theorem 1.3)

Part of the formalization's proof of N4 (`UnstableCurveLeavesStarDomain`, Figure 14.2) without
computer assistance. **Departure from the paper**, by the user's decision: the book reads N4 off a
computed figure (Figure 14.2, TeX 11951–11991; REPORT.md E88); the formalization proves it from
the exact structure of the Reinhardt flow along an `e₂`-arc and an invariant region (see
`SmoothedPolygons/Ch14/ArcParams.lean`, and `SmoothedPolygons/Ch14/ArcRegionInvariant.lean` for
the numbering of the steps).

This file is §1.3: along the `e₂`-arc from a phase point with `X₀ ∈ 𝔥*` and `H(e₂) = 0`, each
cleared switching numerator is an exponential sum with exactly four terms and three universal
coefficients, in the time `τ = t/ε`:
`(√3/(8ε³)) N₂₁(t) = f(τ) = -1 + A e^{-τ} + B e^{-2τ} + Y τ e^{-τ}`,
`(√3/(8ε³)) N₂₃(t) = g(τ) = -1 + A' e^{τ} + B' e^{2τ} - Y' τ e^{τ}`,
with `B = Y - 1 + q`, `A = 1 + f₀ - B`, `B' = Y' - 1 + p`, `A' = 1 + g₀ - B'` (`ArcParams.f`,
`ArcParams.g`). On a section point `g₀ = 0` and `f₀ = -(√3/(3ε³Y')) ⟨Λ̂₀, X₀⟩` (1.5).

## Statements

* `arcF0`, `arcG0`, `arcQ`, `arcP`, `arcParams`: the arc parameters of a phase point
  (`f₀ = (√3/(8ε³)) N₂₁(q)`, `g₀ = (√3/(8ε³)) N₂₃(q)`, `q = -(√3/(6ε)) ⟨Λ̂₀, V_e⟩`,
  `p = (2/(√3 ε)) ⟨Λ̂₀, V_f⟩`, `Λ̂₀ = Λ₁(0) + (3/2) J`).
* `arcParams_Y'` (`Y'` of the parameters is `1 + ρ₀/ε`), `arcParams_radius` (`r = X₁₁`).
* **Theorem 1.3** (`arc_normalForm`). Equivalently (1.4) (`ArcParams.f_eq`, `ArcParams.g_eq`).
* **(1.5)** on section points: `frame_section_costateR` (`Λ_R` in the frame:
  `m_h = -ε h₀`, `m_f = h₀ x_f`, `m_e = h₀ (1 - ε²)/x_f`, `h₀ = ⟨Λ̂₀, X₀⟩`), `arcG0_eq_zero`,
  `arcF0_eq_reducedHam`, `arcParams_A'` (`A' = 2 - Y' - p`), `arcF0_pos_iff` (P1, `f₀ > 0`, says
  that the reduced Hamiltonian `⟨Λ₁ + (3/2) J, X⟩` is negative at the section point).

## Proofs (the route, §1.3)

1. `arcParams_Y'`: (1.3) (`arcEps_sq_mul_arcY_mul_arcY'`). `arcParams_radius`:
   `X00_eq_arcRadius`.
2. Theorem 1.3. By `switchingNum_iso_vertexFlow_one`, `(√3/(8ε³)) N₂₁(t) = -(√3/(12ε²)) u φ_e(t)`
   with `u = e^{-t/ε}`. By `hasDerivAt_arcPhi`, `traceForm_iso_vfM_arcVe` and the fundamental
   theorem of calculus, with `L_e = ⟨Λ₁(0), V_e⟩`,
   `φ_e(t) = φ_e(0) - 2ε(1 - u) L_e + √3(2x_e t + x_e²(1 - u) + 4ε²(u⁻¹ - 1))`
   (`∫₀ᵗ u = ε(1 - u)`, `∫₀ᵗ u⁻¹ = ε(u⁻¹ - 1)`; in Lean: the difference of the two sides has
   derivative `0`, `is_const_of_deriv_eq_zero`). Multiplying by `-(√3/(12ε²)) u` gives four terms:
   the constant `-1`, the term `-(x_e/(2ε²)) t u = Y τ u` (`x_e = -2εY`), a `u²` and a `u` term.
   At `t = 0` the sum is `f₀` (definition of `arcF0`), so the `u` coefficient is `1 + f₀ - B`
   once the `u²` coefficient is `B`; the `u²` coefficient is `-(√3/(6ε))(L_e - √3 x_e²/(2ε))`,
   and with `Λ₁(0) = Λ̂₀ - (3/2) J` and `⟨J, V_e⟩ = -(4ε/√3)(Y² - Y + 1)` (from (1.2),
   `traceForm_ofFrame`, `x_e = -2εY`) it is `Y - 1 + q`. The `N₂₃` computation is the same with
   `φ_f`, `V_f`, `u⁻¹`, `⟨J, V_f⟩ = (ε/√3)(Y'² - Y' + 1)`; `g(0) = g₀` fixes the `e^{τ}`
   coefficient. All coefficient identities are polynomial in `ε, Y, Y', x_e, x_f` modulo
   `x_e = -2εY`, `x_f = εY'/2`, `ε² Y Y' = 1 + ε²` (`linear_combination`). In Lean each of the two
   identities is one `linear_combination` of `√3² = 3` and `u u⁻¹ = 1` with rational cofactors
   (found by polynomial division, checked by `field_simp; ring`). The statement does not assume
   `Λ₁(0)` traceless: the closed forms of `φ_e`, `φ_f` use only `X₀`, `Λ_R(0)` and `H(e₂) = 0`.
3. (1.5): on a section point the three linear conditions `⟨X, Λ_R⟩ = 0`,
   `⟨Λ_R, Z_{e₂}⟩ = ⟨X, Z_{e₂}⟩ h₀`, `⟨Λ_R, Z_{e₃}⟩ = ⟨X, Z_{e₃}⟩ h₀` (`H(e₂) = H(e₃) = 0`,
   `hamiltonian_eq_traceForm_sub`; `H(e₂) = H(e₃) - χ₂₃`, `hamiltonian_sub_eq_switchingFn`) read
   `-2ε m_h + x_e m_f + x_f m_e = 0`, `m_h = -ε h₀`, `2m_h + 4m_f = (-2ε + 4x_f) h₀` in the frame,
   whence `frame_section_costateR`. Then `N₂₁(q) = -(2/3)(ε m_e + x_e m_h) = -8h₀/(3Y')`
   (`x_e x_f = -(1 + ε²)`), which is (1.5); `N₂₃(q) = χ₂₃ ⟨X, Z_{e₂}⟩⟨X, Z_{e₃}⟩ = 0`.
   `A' = 1 + g₀ - B' = 2 - Y' - p`.

Also checked numerically, while the statements were written, against a literal model of the Lean
definitions: the normal form to `10⁻¹⁷` at several times on a chart point near `W^u` and on a
generic phase point with `H(e₂) = 0`; (1.5) and the frame of `Λ_R` on the chart point. The proofs
do not depend on these checks.
-/

@[expose] public section

namespace SmoothedPolygons

open Set Filter Topology

/-- `f₀ = (√3/(8ε³)) N₂₁(q)`, the value at `τ = 0` of the normalized `N₂₁` (Theorem 1.3). -/
noncomputable def arcF0 (q : iso_PhasePt) : ℝ := √3 / (8 * arcEps q ^ 3) * switchingNum 1 0 q

/-- `g₀ = (√3/(8ε³)) N₂₃(q)`, the value at `τ = 0` of the normalized `N₂₃`; `0` on the section. -/
noncomputable def arcG0 (q : iso_PhasePt) : ℝ := √3 / (8 * arcEps q ^ 3) * switchingNum 1 2 q

/-- `q = -(√3/(6ε)) ⟨Λ̂₀, V_e⟩`, `Λ̂₀ = Λ₁(0) + (3/2) J` (Theorem 1.3): `B = Y - 1 + q`. -/
noncomputable def arcQ (q : iso_PhasePt) : ℝ :=
  -(√3 / (6 * arcEps q)) * traceForm (q.2.1 + (3 / 2 : ℝ) • J) (arcVe q.1)

/-- `p = (2/(√3 ε)) ⟨Λ̂₀, V_f⟩` (Theorem 1.3): `B' = Y' - 1 + p`. -/
noncomputable def arcP (q : iso_PhasePt) : ℝ :=
  2 / (√3 * arcEps q) * traceForm (q.2.1 + (3 / 2 : ℝ) • J) (arcVf q.1)

/-- **The arc parameters** `(ε, Y, f₀, g₀, q, p)` of a phase point (§1.3, §2.1). -/
noncomputable def arcParams (q : iso_PhasePt) : ArcParams :=
  ⟨arcEps q, arcY q, arcF0 q, arcG0 q, arcQ q, arcP q⟩

variable {q : iso_PhasePt}

/-! ### Helpers: the trace form, the frame of the state, the closed forms of `φ_e`, `φ_f` -/

private lemma traceForm_add_smul_left (A B C : Mat2) (c : ℝ) :
    traceForm (A + c • B) C = traceForm A C + c * traceForm B C := by
  simp only [traceForm, Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul,
    smul_eq_mul]

private lemma traceForm_smul_right (A B : Mat2) (c : ℝ) :
    traceForm A (c • B) = c * traceForm A B := by
  simp only [traceForm, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

private lemma traceForm_comm (A B : Mat2) : traceForm A B = traceForm B A := by
  simp only [traceForm]
  exact Matrix.trace_mul_comm A B

/-- `⟨J, V_e⟩` in the frame ((1.2)). -/
private lemma traceForm_J_arcVe (q : iso_PhasePt) :
    traceForm J (arcVe q.1) = 2 * -(1 / √3) * frameE q.1 + -(4 / √3) * arcEps q +
      1 / √3 * (-frameE q.1 ^ 2 / arcEps q) := by
  rw [frame_controlMatrix.2.2.2]
  exact traceForm_ofFrame _ _ _ _ _ _

/-- `⟨J, V_f⟩` in the frame ((1.2)). -/
private lemma traceForm_J_arcVf (q : iso_PhasePt) :
    traceForm J (arcVf q.1) = 2 * -(1 / √3) * frameF q.1 +
      -(4 / √3) * (-frameF q.1 ^ 2 / arcEps q) + 1 / √3 * arcEps q := by
  rw [frame_controlMatrix.2.2.2]
  exact traceForm_ofFrame _ _ _ _ _ _

private lemma hasDerivAt_exp_div (ε t : ℝ) :
    HasDerivAt (fun t ↦ Real.exp (t / ε)) (Real.exp (t / ε) / ε) t := by
  exact (((hasDerivAt_id' t).div_const ε).exp).congr_deriv (by ring)

private lemma hasDerivAt_exp_neg_div (ε t : ℝ) :
    HasDerivAt (fun t ↦ Real.exp (-t / ε)) (-(Real.exp (-t / ε) / ε)) t := by
  exact (((hasDerivAt_neg' t).div_const ε).exp).congr_deriv (by ring)

/-- **`φ_e` in closed form** (proof of Theorem 1.3): by `hasDerivAt_arcPhi` and
`traceForm_iso_vfM_arcVe`, `φ_e(t) = φ_e(0) - 2ε(1 - u) L_e + √3(2x_e t + x_e²(1 - u) +
4ε²(u⁻¹ - 1))`, `u = e^{-t/ε}`, `L_e = ⟨Λ₁(0), V_e⟩` (the fundamental theorem of calculus: the
difference has derivative `0`). -/
private lemma arcPhiE_eq (hX : IsStarState q.1) (hH : phaseHam q (vertex 1) = 0) (t : ℝ) :
    arcPhiE q t = arcPhiE q 0 - 2 * arcEps q * (1 - Real.exp (-t / arcEps q)) *
        traceForm q.2.1 (arcVe q.1) +
      √3 * (2 * frameE q.1 * t + frameE q.1 ^ 2 * (1 - Real.exp (-t / arcEps q)) +
        4 * arcEps q ^ 2 * (Real.exp (t / arcEps q) - 1)) := by
  have he : arcEps q ≠ 0 := (arcEps_pos hX).ne'
  set ε := arcEps q with hεdef
  set L := traceForm q.2.1 (arcVe q.1) with hL
  set x := frameE q.1 with hx
  let D : ℝ → ℝ := fun t ↦ arcPhiE q t - (arcPhiE q 0 - 2 * ε * (1 - Real.exp (-t / ε)) * L +
      √3 * (2 * x * t + x ^ 2 * (1 - Real.exp (-t / ε)) + 4 * ε ^ 2 * (Real.exp (t / ε) - 1)))
  have hD : ∀ t, HasDerivAt D 0 t := by
    intro t
    have h1 := (hasDerivAt_arcPhi hX hH t).1
    rw [traceForm_iso_vfM_arcVe hX t, ← hεdef, ← hL, ← hx] at h1
    have hu := hasDerivAt_exp_neg_div ε t
    have hv := hasDerivAt_exp_div ε t
    have h21 := (hasDerivAt_const t (arcPhiE q 0)).sub
      ((((hasDerivAt_const t (1 : ℝ)).sub hu).const_mul (2 * ε)).mul_const L)
    have h22 := (((hasDerivAt_id' t).const_mul (2 * x)).add
      (((hasDerivAt_const t (1 : ℝ)).sub hu).const_mul (x ^ 2))).add
        ((hv.sub (hasDerivAt_const t (1 : ℝ))).const_mul (4 * ε ^ 2))
    have h2 := h21.add (h22.const_mul (√3))
    refine (h1.sub h2).congr_deriv ?_
    field_simp
    ring
  have hc := is_const_of_deriv_eq_zero (fun t ↦ (hD t).differentiableAt) (fun t ↦ (hD t).deriv)
    t 0
  have h0 : D 0 = 0 := by simp [D]
  have := hc.trans h0
  simp only [D] at this
  linarith

/-- **`φ_f` in closed form** (proof of Theorem 1.3): `φ_f(t) = φ_f(0) + 2ε(u⁻¹ - 1) L_f +
√3(-2x_f t + ε²(1 - u) + 4x_f²(u⁻¹ - 1))`, `L_f = ⟨Λ₁(0), V_f⟩`. -/
private lemma arcPhiF_eq (hX : IsStarState q.1) (hH : phaseHam q (vertex 1) = 0) (t : ℝ) :
    arcPhiF q t = arcPhiF q 0 + 2 * arcEps q * (Real.exp (t / arcEps q) - 1) *
        traceForm q.2.1 (arcVf q.1) +
      √3 * (-2 * frameF q.1 * t + arcEps q ^ 2 * (1 - Real.exp (-t / arcEps q)) +
        4 * frameF q.1 ^ 2 * (Real.exp (t / arcEps q) - 1)) := by
  have he : arcEps q ≠ 0 := (arcEps_pos hX).ne'
  set ε := arcEps q with hεdef
  set L := traceForm q.2.1 (arcVf q.1) with hL
  set x := frameF q.1 with hx
  let D : ℝ → ℝ := fun t ↦ arcPhiF q t - (arcPhiF q 0 + 2 * ε * (Real.exp (t / ε) - 1) * L +
      √3 * (-2 * x * t + ε ^ 2 * (1 - Real.exp (-t / ε)) + 4 * x ^ 2 * (Real.exp (t / ε) - 1)))
  have hD : ∀ t, HasDerivAt D 0 t := by
    intro t
    have h1 := (hasDerivAt_arcPhi hX hH t).2
    rw [traceForm_iso_vfM_arcVf hX t, ← hεdef, ← hL, ← hx] at h1
    have hu := hasDerivAt_exp_neg_div ε t
    have hv := hasDerivAt_exp_div ε t
    have h21 := (hasDerivAt_const t (arcPhiF q 0)).add
      (((hv.sub (hasDerivAt_const t (1 : ℝ))).const_mul (2 * ε)).mul_const L)
    have h22 := (((hasDerivAt_id' t).const_mul (-2 * x)).add
      (((hasDerivAt_const t (1 : ℝ)).sub hu).const_mul (ε ^ 2))).add
        ((hv.sub (hasDerivAt_const t (1 : ℝ))).const_mul (4 * x ^ 2))
    have h2 := h21.add (h22.const_mul (√3))
    refine (h1.sub h2).congr_deriv ?_
    field_simp
    ring
  have hc := is_const_of_deriv_eq_zero (fun t ↦ (hD t).differentiableAt) (fun t ↦ (hD t).deriv)
    t 0
  have h0 : D 0 = 0 := by simp [D]
  have := hc.trans h0
  simp only [D] at this
  linarith

/-- `Y'` of the parameters is `1 + ρ₀(X₀)/ε` ((1.3)). -/
theorem arcParams_Y' (hX : IsStarState q.1) : (arcParams q).Y' = arcY' q := by
  have he := arcEps_pos hX
  have hY := one_lt_arcY hX
  have h := arcEps_sq_mul_arcY_mul_arcY' hX
  simp only [ArcParams.Y', arcParams]
  rw [div_eq_iff (by positivity)]
  linear_combination -h

/-- The radius of the parameters is the chart radius `r = X₁₁`. -/
theorem arcParams_radius (hX : IsStarState q.1) : (arcParams q).radius = q.1 0 0 := by
  rw [X00_eq_arcRadius (arcEps_pos hX).ne', ArcParams.radius, arcParams_Y' hX]
  rfl

/-- **Theorem 1.3** (the normal form). Let `q` be a phase point with `X₀` a star state, `Λ_R(0)`
traceless and `H(e₂)(q) = 0`. Along the `e₂`-flow from `q`, with `τ = t/ε`,
`(√3/(8ε³)) N₂₁(t) = f(τ) = -1 + A e^{-τ} + B e^{-2τ} + Y τ e^{-τ}` and
`(√3/(8ε³)) N₂₃(t) = g(τ) = -1 + A' e^{τ} + B' e^{2τ} - Y' τ e^{τ}`, with `B = Y - 1 + q`,
`A = 1 + f₀ - B`, `B' = Y' - 1 + p`, `A' = 1 + g₀ - B'` (`ArcParams.f`, `ArcParams.g`). -/
theorem arc_normalForm (hX : IsStarState q.1) (hR : q.2.2.trace = 0)
    (hH : phaseHam q (vertex 1) = 0) (t : ℝ) :
    √3 / (8 * arcEps q ^ 3) * switchingNum 1 0 (iso_vertexFlow 1 q t) =
        (arcParams q).f (t / arcEps q) ∧
      √3 / (8 * arcEps q ^ 3) * switchingNum 1 2 (iso_vertexFlow 1 q t) =
        (arcParams q).g (t / arcEps q) := by
  have he : 0 < arcEps q := arcEps_pos hX
  have hε : arcEps q ≠ 0 := he.ne'
  have hs : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : √3 ≠ 0 := by positivity
  obtain ⟨-, hxe, hxf, -⟩ := frame_state hX
  have hN := switchingNum_iso_vertexFlow_one hX hR t
  have hN0 := switchingNum_iso_vertexFlow_one hX hR 0
  rw [ivf_vertexFlow_zero] at hN0
  simp only [neg_zero, zero_div, Real.exp_zero, mul_one] at hN0
  have huv : Real.exp (-t / arcEps q) * Real.exp (t / arcEps q) = 1 := by
    rw [← Real.exp_add, neg_div, neg_add_cancel, Real.exp_zero]
  have hu1 : Real.exp (-(t / arcEps q)) = Real.exp (-t / arcEps q) := by rw [neg_div]
  have hu2 : Real.exp (-2 * (t / arcEps q)) = Real.exp (-t / arcEps q) ^ 2 := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have hv2 : Real.exp (2 * (t / arcEps q)) = Real.exp (t / arcEps q) ^ 2 := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  constructor
  · -- `N₂₁`: the four terms `-1`, `Y τ u`, `B u²`, `A u`
    rw [hN.1, arcPhiE_eq hX hH t]
    simp only [ArcParams.f, ArcParams.A, ArcParams.B, arcParams, arcF0, arcQ, hN0.1,
      traceForm_add_smul_left, traceForm_J_arcVe, hu1, hu2, hxe]
    generalize Real.exp (-t / arcEps q) = u at huv ⊢
    generalize Real.exp (t / arcEps q) = v at huv ⊢
    set e := arcEps q
    set Y := arcY q
    linear_combination (norm := skip)
      (u * (Y ^ 2 * e * u - Y ^ 2 * e + Y * t - e * v + e) / (3 * e)) * hs + (-1 : ℝ) * huv
    field_simp
    ring
  · -- `N₂₃`: the four terms `-1`, `-Y' τ u⁻¹`, `B' u⁻²`, `A' u⁻¹`
    rw [hN.2, arcPhiF_eq hX hH t]
    simp only [ArcParams.g, ArcParams.A', ArcParams.B', arcParams_Y' hX]
    simp only [arcParams, arcG0, arcP, hN0.2, traceForm_add_smul_left, traceForm_J_arcVf, hv2,
      hxf]
    generalize Real.exp (-t / arcEps q) = u at huv ⊢
    generalize Real.exp (t / arcEps q) = v at huv ⊢
    set e := arcEps q
    set Yp := arcY' q
    set L := traceForm q.2.1 (arcVf q.1)
    linear_combination (norm := skip)
      (-(-2 * L * √3 * v ^ 2 + 2 * L * √3 * v - Yp ^ 2 * e * √3 ^ 2 * v ^ 2 +
        Yp ^ 2 * e * √3 ^ 2 * v - 3 * Yp ^ 2 * e * v ^ 2 + 3 * Yp ^ 2 * e * v +
        3 * Yp * e * v ^ 2 - 3 * Yp * e * v + Yp * √3 ^ 2 * t * v + e * √3 ^ 2 * u * v -
        e * √3 ^ 2 * v + 3 * e * u * v - 3 * e * v ^ 2 + 3 * e * v - 3 * e) /
          (3 * e * √3 ^ 2)) * hs + (-3 / √3 ^ 2) * huv
    field_simp
    ring

/-- **`Λ_R` on a section point, in the frame** (§1.3, before (1.5)): with
`h₀ = ⟨Λ̂₀, X₀⟩` (`reducedHam`), `m_h = -ε h₀`, `m_f = h₀ x_f`, `m_e = h₀ (1 - ε²)/x_f`. -/
theorem frame_section_costateR (hq : IsArcSectionPt q) :
    frameH q.2.2 = -arcEps q * reducedHam q.2.1 q.1 ∧
      frameF q.2.2 = frameF q.1 * reducedHam q.2.1 q.1 ∧
      frameE q.2.2 = (1 - arcEps q ^ 2) * reducedHam q.2.1 q.1 / frameF q.1 := by
  obtain ⟨⟨⟨-, -, hRt, -, hXR, hH3, hχ⟩, -⟩, hX⟩ := hq
  have he : 0 < arcEps q := arcEps_pos hX
  have hY' : 1 < arcY' q := one_lt_arcY' hX
  have hs0 : √3 ≠ 0 := by positivity
  have hrel := arcEps_sq_mul_arcY_mul_arcY' hX
  obtain ⟨-, -, hxf, -⟩ := frame_state hX
  set h₀ := reducedHam q.2.1 q.1 with hh₀
  -- the three linear conditions of the section
  have tv := traceForm_controlMatrix_vertex hX.1
  have hd1 : traceForm (controlMatrix (vertex 1)) q.1 ≠ 0 := by
    rw [traceForm_comm, tv.2.1]
    exact mul_ne_zero (neg_ne_zero.mpr (by positivity)) hX.2.2.2.1.ne'
  have hd2 : traceForm (controlMatrix (vertex 2)) q.1 ≠ 0 := by
    rw [traceForm_comm, tv.2.2]
    exact mul_ne_zero (neg_ne_zero.mpr (by positivity)) hX.2.2.1.ne'
  have hP2 : traceForm q.2.2 (controlP (vertex 2) q.1) = h₀ := by
    have := hamiltonian_eq_traceForm_sub q.2.1 q.2.2 q.1 (vertex 2)
    rw [hH3] at this
    simp only [hh₀, reducedHam]
    linarith
  have hP1 : traceForm q.2.2 (controlP (vertex 1) q.1) = h₀ := by
    have : switchingFn 1 2 q.2.2 q.1 = traceForm q.2.2 (controlP (vertex 2) q.1) -
        traceForm q.2.2 (controlP (vertex 1) q.1) := by
      simp only [switchingFn, traceForm, Matrix.mul_sub, Matrix.trace_sub]
    linarith
  have hk : ∀ k, traceForm (controlMatrix (vertex k)) q.1 ≠ 0 →
      traceForm q.2.2 (controlP (vertex k) q.1) = h₀ →
      traceForm q.2.2 (controlMatrix (vertex k)) =
        h₀ * traceForm (controlMatrix (vertex k)) q.1 := by
    intro k hd h
    rw [controlP, traceForm_smul_right] at h
    rw [← h]
    field_simp
  have e1 := hk 1 hd1 hP1
  have e2 := hk 2 hd2 hP2
  -- in the frame
  have hXf := state_eq_ofFrame hX
  have hRf : q.2.2 = ofFrame (frameH q.2.2) (frameE q.2.2) (frameF q.2.2) :=
    (ofFrame_frame hRt).symm
  obtain ⟨-, hZ1, hZ2, -⟩ := frame_controlMatrix
  rw [hZ1, hXf, hRf, traceForm_ofFrame, traceForm_ofFrame] at e1
  rw [hZ2, hXf, hRf, traceForm_ofFrame, traceForm_ofFrame] at e2
  rw [hXf, hRf, traceForm_ofFrame] at hXR
  rw [hxf]
  set mh := frameH q.2.2
  set me := frameE q.2.2
  set mf := frameF q.2.2
  have E1 : mh = -arcEps q * h₀ := by
    linear_combination (norm := skip) (√3 / 2) * e1
    field_simp
    ring
  have E2 : mf = arcEps q * arcY' q / 2 * h₀ := by
    linear_combination (norm := skip) (-√3 / 4) * e2 + (-1 / 2 : ℝ) * E1
    field_simp
    ring
  refine ⟨E1, E2, ?_⟩
  rw [eq_div_iff (by positivity)]
  linear_combination hXR + 2 * arcEps q * E1 + 2 * arcEps q * arcY q * E2 + h₀ * hrel

/-- **(1.5)**: on a section point `g₀ = 0` (`χ₂₃ = 0`). -/
theorem arcG0_eq_zero (hq : IsArcSectionPt q) : arcG0 q = 0 := by
  have h := (switchingFn_eq_zero_iff 1 2 hq.2).1 hq.1.1.2.2.2.2.2.2
  simp [arcG0, h]

/-- **(1.5)**: on a section point `f₀ = -(√3/(3ε³Y')) ⟨Λ̂₀, X₀⟩`. -/
theorem arcF0_eq_reducedHam (hq : IsArcSectionPt q) :
    arcF0 q = -(√3 / (3 * arcEps q ^ 3 * arcY' q)) * reducedHam q.2.1 q.1 := by
  obtain ⟨E1, E2, E3⟩ := frame_section_costateR hq
  have hX := hq.2
  have hRt := hq.1.1.2.2.1
  have he := arcEps_pos hX
  have hY' := one_lt_arcY' hX
  have hrel := arcEps_sq_mul_arcY_mul_arcY' hX
  have hs : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : √3 ≠ 0 := by positivity
  obtain ⟨-, -, hxf, -⟩ := frame_state hX
  rw [hxf] at E2 E3
  set h₀ := reducedHam q.2.1 q.1
  have hXf := state_eq_ofFrame hX
  have hRf : q.2.2 = ofFrame (frameH q.2.2) (frameE q.2.2) (frameF q.2.2) :=
    (ofFrame_frame hRt).symm
  obtain ⟨hZ0, hZ1, -, -⟩ := frame_controlMatrix
  unfold arcF0 switchingNum
  rw [hZ0, hZ1, hXf, hRf]
  simp only [traceForm_ofFrame]
  rw [E1, E2, E3]
  set e := arcEps q
  set Y := arcY q
  set Yp := arcY' q
  linear_combination (norm := skip) (h₀ / (3 * Yp * e ^ 3 * √3)) * hs +
    (-h₀ / (2 * Yp * e ^ 3 * √3)) * hrel
  field_simp
  ring

/-- **(1.5)**: on a section point `A' = 2 - Y' - p`. -/
theorem arcParams_A' (hq : IsArcSectionPt q) : (arcParams q).A' = 2 - arcY' q - arcP q := by
  simp only [ArcParams.A', ArcParams.B', arcParams_Y' hq.2]
  simp only [arcParams, arcG0_eq_zero hq]
  ring

/-- **(1.5)**: P1 (`f₀ > 0`) says that the reduced Hamiltonian `⟨Λ₁ + (3/2) J, X⟩` is negative at
the section point. -/
theorem arcF0_pos_iff (hq : IsArcSectionPt q) : 0 < arcF0 q ↔ reducedHam q.2.1 q.1 < 0 := by
  rw [arcF0_eq_reducedHam hq]
  have he := arcEps_pos hq.2
  have hY' := one_lt_arcY' hq.2
  have hc : 0 < √3 / (3 * arcEps q ^ 3 * arcY' q) := by positivity
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

end SmoothedPolygons
