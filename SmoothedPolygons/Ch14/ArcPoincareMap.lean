module

public import SmoothedPolygons.Ch14.ArcRelation
public import SmoothedPolygons.Ch14.ArcStepClosed
public import SmoothedPolygons.Ch14.VertexPoissonBracket
import SmoothedPolygons.Ch7.Isolated.VertexFlow
import SmoothedPolygons.Ch7.Isolated.Return

/-!
# Chapter 14, N4: the Reinhardt–Poincaré map in closed form (Theorem 5.1, Corollary 5.3)

Part of the formalization's proof of N4 (`UnstableCurveLeavesStarDomain`, Figure 14.2) without
computer assistance. **Departure from the paper**, by the user's decision: the book reads N4 off a
computed figure (Figure 14.2, TeX 11951–11991; REPORT.md E88); the formalization proves it from
the exact structure of the Reinhardt flow along an `e₂`-arc and an invariant region (see
`SmoothedPolygons/Ch14/ArcParams.lean`, and `SmoothedPolygons/Ch14/ArcRegionInvariant.lean` for
the numbering of the steps).

This file is §5 of the note (`docs/unstable-curve.pdf`), Theorem 5.1 and Corollary 5.3: if the
`e₂`-arc from a section point `q` switches inside the star domain, its image
`F(q) = reinPoincare q = Ad_{R⁻¹} q(t_sw)` is a section point whose arc parameters are explicit
functions of those of `q` and of `s = e^{τ_sw}`, where `τ_sw` is the switching root of the
four-term exponential sum `f` (`ArcParams.step`): no ODE, one root per step. The radii telescope,
`r(F q) = (ρ₁(q) - ρ₁(F q))/2`, so along any orbit that keeps switching they sum to less than
`ρ₁(q₀)/2` (the budget).

## Statements

* `SwitchesBeforeExit q`: `0 < t_sw(q) < T(q) = ε log Y` (`reinSwitchTime`, `arcExitTime`).
* `ρ_adRinv`: `Ad_{R⁻¹}` permutes the star functions, `(ρ₀, ρ₁, ρ₂)(R⁻¹XR) = (ρ₁, ρ₂, ρ₀)(X)`.
* `switchingNum_adRinv`: the relabelling `N_{i+1, j+1}(Ad_{R⁻¹} q) = N_{ij}(q)`
  (`R⁻¹ Z_{e_m} R = Z_{e_{m+1}}`).
* `reinSwitchTime_eq_tauSw`: `t_sw = ε τ_sw` and `f(τ_sw) = 0`.
* **Theorem 5.1**: `isArcSectionPt_reinPoincare`, `ρ_reinPoincare`
  (`(ρ₀, ρ₁, ρ₂)(F q) = (ρ₁(q), ρ₂(X(t_sw)), ρ₀(X(t_sw)))`), `arcParams_reinPoincare`
  (`arcParams (F q) = (arcParams q).step q_new`: `ε_new = k ε`, `Y_new = 1 + (Y' e^{τ_sw} - 1)/k`,
  `f₀,new = g(τ_sw)/k²`, `g₀,new = 0`, `p_new = -f'(τ_sw)/k²`, with `q_new = arcQ (F q)`, which
  satisfies the relation `R = 0` at the new point, `arcParams_rel`), `radius_reinPoincare`
  (`r(F q) = (ρ₁(q) - ρ₁(F q))/2 = ε(1 - k)/2`). With `ArcParams.step_closed`:
  `Y_new = (Y' s² - 2s + Y)/(Y - s)`, `Y'_new = Y/(Y - s)`, `p_new = (s² - Y s + B)/(Y - s)²`.
* The costate in closed form, (5.4) of the note: `iso_vfΛ₁_one_eq_arcParams` (on a section point,
  `Λ₁(t) = α (X(t) + P) + β u⁻² V_e(t) + γ u² V_f(t)`, `u = e^{-t/ε}`, with `α, β, γ` the
  coefficients of the eigenbasis expansion of Proposition 3.1, `ArcParams.lamAlpha` …), and
  `arcP_adRinv_vertexFlow` (for every `t < T`, with `s = e^{t/ε}`, the rotated point
  `Ad_{R⁻¹} q(t)` has `p = (s² - Y s + B)/(Y - s)²`, `ArcParams.pNew`).
* **Corollary 5.3**: `sum_radius_reinPoincare_iterate` (the telescoping identity),
  `sum_radius_reinPoincare_iterate_lt` (`Σ_{n ≥ 1} r_n < ρ₁(q₀)/2`),
  `tendsto_radius_reinPoincare_iterate` (an orbit that switches forever with `r_n ≥ 0` has
  `r_n → 0`: it chatters into the divisor).

## Proofs (the route, the proof of Theorem 5.1 in the note)

1. `ρ_adRinv`: entrywise, `R = [[1/2, -√3/2], [√3/2, 1/2]]`, `R⁻¹ = Rᵀ` (`field_simp`, `ring`,
   `Real.sq_sqrt`). `switchingNum_adRinv`: `⟨R⁻¹ M R, Z_{m+1}⟩ = ⟨M, R Z_{m+1} R⁻¹⟩ = ⟨M, Z_m⟩`
   (`ivf_conj_pow_controlMatrix` with `iso_rotControl 1 e_m = e_{m+1}`, as
   `iso_rotControl_vertex` of `SmoothedPolygons/Ch16/NextSwitch.lean`; `Matrix.trace_mul_comm`).
2. `reinSwitchTime_eq_tauSw`: for `0 < t < T` the state is a star state
   (`isStarState_iso_vfX_one_iff`), so `χ₂₁(t) = 0 ⟺ N₂₁(t) = 0 ⟺ f(t/ε) = 0`
   (`switchingFn_eq_zero_iff`, `arc_normalForm`). The zero set of `χ₂₁` on `(0, ∞)` has infimum
   `t_sw ∈ (0, T)`, so it is determined by its part in `(0, T)`, which is `ε` times the zero set of
   `f` in `(0, log Y)`; hence `t_sw = ε τ_sw`. The infimum is attained: `f` is continuous and
   `τ_sw > 0`.
3. Section point: `X(t_sw)` is a star state (`t_sw < T`) and `Ad_{R⁻¹}` preserves the star domain
   (`poly_isStarState_conj_pow`); the traces, `det X`, `det Λ₁` and `⟨X, Λ_R⟩` are preserved by the
   flow (`irt_vertexFlow_traceless`, `traceForm_vertexFlow` and the determinant lemma of
   `SmoothedPolygons/Ch14/VertexFlowAnalytic.lean`) and by conjugation; `H(e₂)` is conserved
   (`hamiltonian_vertexFlow`), `H(e₁) = H(e₂)` at the switch (`χ₂₁ = 0`), and after the
   relabelling of step 1 the new `H(e₂)`, `H(e₃)` are the old `H(e₁)`, `H(e₂)`: both `0`, so
   the new `χ₂₃ = 0`.
4. `ρ_reinPoincare`: step 1. Hence `ε_new = ρ₂(t_sw) = ε k` with `k = Y u - 1`, `u = e^{-τ_sw}`
   (`ρ_iso_vfX_one`), `Y_new = 1 + ρ₀(t_sw)/ε_new = 1 + (Y' e^{τ_sw} - 1)/k`, and
   `r(F q) = (ρ₀ - ρ₁)(F q)/2 = (ε - ε k)/2` (`X00_eq_arcRadius`).
5. `f₀,new` and `p_new`. `arcP` and the (2.4) form `-(√3/(3ε³Y')) ⟨Λ̂, X⟩` of `f₀`
   (`arcF0_eq_reducedHam`) are pairings of `Λ̂` with matrices built from `X`, and `Λ₁(t)` has the
   closed form (5.4) (`iso_vfΛ₁_one_eq_arcParams`): the eigenbasis expansion of `Λ₁(0)` carried
   along the arc. Pairing at the rotated point gives `p_new = (s² - Y s + B)/(Y - s)²`
   (`arcP_adRinv_vertexFlow` at `t = t_sw`) and `f₀,new = s² Ψ(s)/(Y (Y - s)²)` at the section
   point `F q` (`isArcSectionPt_reinPoincare`). Eliminating `Y τ_sw = s - A - B/s` with
   `f(τ_sw) = 0` turns these into `-f'(τ_sw)/k²` and `g(τ_sw)/k²`
   (`ArcParams.neg_fDeriv_div_sq_eq_pNew`, `ArcParams.g_div_sq_eq_f0New`). `g₀,new = 0`
   (`arcG0_eq_zero`).
6. Corollary 5.3: induction on `N` with step 4 (`Finset.sum_range_succ`); the bound from
   `ρ₁(F^N q) > 0` (a section point is a star state); the limit: the partial sums of the
   nonnegative `r_n` are bounded, so the series is summable and `r_n → 0`
   (`Summable.tendsto_atTop_zero`).

**The pairings in step 5** are computed in the frame: `Ad_{R⁻¹}` acts on frame components by
`(h, e, f) ↦ (e/2 - h, e - 4h - 4f, -e/4)` (from `S⁻¹ R S = [[0, -2], [1/2, 1]]`), the star
functions are `(ρ₀, ρ₁, ρ₂) = (h + 2f, -h, h - e/2)`, and
`(3/2) J = √3 · ofFrame (-1/2) (-2) (1/2)`, so `Λ̂(t) = √3 M(t)` with `M(t)` free of `√3`. The
proofs conjugate `Λ̂(t)` by `R⁻¹` and pair it with `V_e`, `V_f`, `X` of the rotated state. `√3`
then enters each closed form once, as `√3 · √3 = 3`, and the rest is `field_simp`, `ring` in
`(ε, Y, s, f₀, q, p)` with `Y' = (1 + ε²)/(ε² Y)`. Step 1 uses `ρ_R_conj` and
`poly_Rinv_conj_vertex`; step 3 uses `poly_hamiltonian_conj` for the relabelled Hamiltonians;
step 4 uses `X₁₁ = (ρ₀ - ρ₁)/2`.

**Another route to step 5** (not used): by step 1, `N₂₁^new = N₁₃(t_sw) = N₂₃(t_sw) ε_new/ε` at a
zero of `N₂₁`, which gives `f₀,new = g(τ_sw)/k²`; and `N₂₃^new = -N₂₁` with equal slopes along the
`e₁`- and `e₂`-flows where `χ₂₁ = 0` (Lemma 4.1), which gives `p_new = -f'(τ_sw)/k²`. So
`f₀,new` is the rescaled lead of `e₂` over `e₃` at the switch, and `p_new` the rescaled rate at
which `e₁` overtook `e₂`.

`q_new` is not computed: the proof of Theorem 6.5 only uses the relation `R = 0` at `F q`
(`arcParams_rel`). Along `W^u` `q_new` is numerically the larger root of `R = 0` in `q`, but not
in general (an independent review found a section point outside `𝒢*` whose image takes the
smaller root); the proof never needs to know which root it is.

Also checked numerically, while the statements were written, against a literal model of the Lean
definitions: the update rules, the permutation of the `ρ`'s, the radius identities, the section
conditions at `F q`, to `10⁻¹⁴`, at two section points. The proofs do not depend on these checks.
-/

@[expose] public section

namespace SmoothedPolygons

open Set Filter Topology

/-- **The `e₂`-arc from `q` switches before it leaves the star domain**: `0 < t_sw(q) < T(q)`. -/
def SwitchesBeforeExit (q : iso_PhasePt) : Prop :=
  0 < reinSwitchTime q ∧ reinSwitchTime q < arcExitTime q

variable {q : iso_PhasePt}

/-! ### Frame computations (helpers) -/

private lemma mul_self_sqrt_three : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)

private lemma sqrt_three_ne_zero : √3 ≠ 0 := by positivity

private lemma sq_sqrt_three : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

private lemma sqrt_three_pow_four : √3 ^ 4 = 9 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_sqrt_three]; norm_num

/-- `Ad_{R⁻¹}` in the frame (`S⁻¹ R S = [[0, -2], [1/2, 1]]`):
`R⁻¹ (h H + e E + f F) R = (e/2 - h) H + (e - 4h - 4f) E - (e/4) F`. -/
private lemma adRinv_ofFrame (h e f : ℝ) :
    R⁻¹ * ofFrame h e f * R = ofFrame (e / 2 - h) (e - 4 * h - 4 * f) (-e / 4) := by
  have h3 := sqrt_three_ne_zero
  rw [poly_R_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ofFrame, R, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring_nf <;> simp only [sq_sqrt_three, sqrt_three_pow_four] <;> ring_nf

/-- `(3/2) J = √3 (-(1/2) H - 2E + (1/2) F)` in the frame. -/
private lemma three_halves_smul_J_eq_ofFrame :
    (3 / 2 : ℝ) • J = √3 • ofFrame (-(1 / 2)) (-2) (1 / 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ofFrame, J] <;> field_simp
  · ring
  · simp only [sq_sqrt_three]

private lemma arcVe_ofFrame (h e f : ℝ) :
    arcVe (ofFrame h e f) = ofFrame e (-e ^ 2 / -h) (-h) := by
  rw [arcVe, frameE_ofFrame, (ρ_ofFrame h e f).1]

private lemma arcVf_ofFrame (h e f : ℝ) :
    arcVf (ofFrame h e f) = ofFrame f (-h) (-f ^ 2 / -h) := by
  rw [arcVf, frameF_ofFrame, (ρ_ofFrame h e f).1]

/-! ### Section points (helpers) -/

/-- On a section point `H(e₂) = H(e₃) + χ₂₃ = 0`. -/
private lemma phaseHam_vertex_one_eq_zero (hq : IsArcSectionPt q) : phaseHam q (vertex 1) = 0 := by
  obtain ⟨⟨⟨-, -, -, -, -, h6, h7⟩, -⟩, -⟩ := hq
  have := hamiltonian_sub_eq_switchingFn q.2.1 q.2.2 q.1 1 2
  rw [h7, h6] at this
  unfold phaseHam
  linarith

/-- Inside the star domain, `χ₂₁ = 0` along the `e₂`-arc iff `f(t/ε) = 0` (Theorem 2.3). -/
private lemma switchingFn_one_zero_eq_zero_iff (hq : IsArcSectionPt q) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t < arcExitTime q) :
    switchingFn 1 0 (iso_vertexFlow 1 q t).2.2 (iso_vertexFlow 1 q t).1 = 0 ↔
      (arcParams q).f (t / arcEps q) = 0 := by
  have hH := phaseHam_vertex_one_eq_zero hq
  obtain ⟨⟨⟨-, -, hR, -⟩, -⟩, hX⟩ := hq
  have hstar : IsStarState (iso_vertexFlow 1 q t).1 :=
    (isStarState_iso_vfX_one_iff hX ht0).2 ht
  have hε := arcEps_pos hX
  rw [switchingFn_eq_zero_iff 1 0 hstar,
    ← (arc_normalForm hX hR hH t).1]
  constructor
  · intro h
    rw [h, mul_zero]
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (by positivity)

/-! ### The costate along the arc in closed form (helpers; Theorem 5.1) -/

private lemma ofFrame_congr {h e f h' e' f' : ℝ} (hh : h = h') (he : e = e') (hf : f = f') :
    ofFrame h e f = ofFrame h' e' f' := by
  rw [hh, he, hf]

private lemma sqrt_three_div_six_mul_sqrt_three (x y : ℝ) :
    -(√3 / (6 * x)) * (√3 * y) = -(y / (2 * x)) := by
  rw [show -(√3 / (6 * x)) * (√3 * y) = -(√3 * √3 * y / (6 * x)) by ring, mul_self_sqrt_three]
  ring

private lemma two_div_sqrt_three_mul_sqrt_three (x y : ℝ) :
    2 / (√3 * x) * (√3 * y) = 2 * y / x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · field_simp

private lemma sqrt_three_div_three_mul_sqrt_three (x z y : ℝ) :
    -(√3 / (3 * x * z)) * (√3 * y) = -(y / (x * z)) := by
  rw [show -(√3 / (3 * x * z)) * (√3 * y) = -(√3 * √3 * y / (3 * (x * z))) by ring,
    mul_self_sqrt_three]
  ring

/-- `α/√3` of (5.4). -/
private noncomputable def lamAlphaDivSqrtThree (a : ArcParams) : ℝ :=
  a.eps * (1 + a.eps ^ 2 * (a.Y + a.Y' * a.A - a.Y * a.B'))

/-- `β/√3` of (5.4). -/
private noncomputable def lamBetaDivSqrtThree (a : ArcParams) : ℝ :=
  -(1 / 2) * a.eps ^ 3 * (a.Y' ^ 2 - a.B')

/-- `γ/√3` of (5.4). -/
private noncomputable def lamGammaDivSqrtThree (a : ArcParams) : ℝ :=
  2 * a.eps ^ 3 * (a.Y ^ 2 - a.B)

private lemma lamAlpha_lamBeta_lamGamma_eq_sqrt_three_mul (a : ArcParams) :
    a.lamAlpha = √3 * lamAlphaDivSqrtThree a ∧ a.lamBeta = √3 * lamBetaDivSqrtThree a ∧
      a.lamGamma = √3 * lamGammaDivSqrtThree a := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [ArcParams.lamAlpha, ArcParams.lamBeta, ArcParams.lamGamma, lamAlphaDivSqrtThree,
      lamBetaDivSqrtThree, lamGammaDivSqrtThree] <;> ring

/-- The coefficients of (5.4) on a section point (Theorem 5.1 (i)). -/
private lemma eigenbasis_coeffs_eq_arcParams (hq : IsArcSectionPt q) :
    2 * arcEps q ^ 2 * traceForm q.2.1 (q.1 + iso_vfP 1 q) = (arcParams q).lamAlpha ∧
      arcEps q ^ 2 * traceForm q.2.1 (arcVf q.1) = (arcParams q).lamBeta ∧
      arcEps q ^ 2 * traceForm q.2.1 (arcVe q.1) = (arcParams q).lamGamma := by
  have hX := hq.2
  have hε := (arcEps_pos hX).ne'
  have hY : arcY q ≠ 0 := (zero_lt_one.trans (one_lt_arcY hX)).ne'
  obtain ⟨fh, fe, ff, -⟩ := frame_state hX
  obtain ⟨lh, le, lf⟩ := frame_reducedCostate hq
  have htr : (q.2.1 + (3 / 2 : ℝ) • J).trace = 0 := by
    rw [Matrix.trace_add, Matrix.trace_smul, hq.1.1.2.1]
    simp [J, Matrix.trace_fin_two]
  have hΛ := ofFrame_frame htr
  rw [lh, le, lf] at hΛ
  have hΛ0 := eq_sub_of_add_eq hΛ.symm
  rw [three_halves_smul_J_eq_ofFrame] at hΛ0
  have hX0 := ofFrame_frame hq.1.1.1
  rw [fh, fe, ff, ← arcParams_Y' hX] at hX0
  rw [hΛ0, ← hX0, iso_vfP_one_eq hX, arcVe_ofFrame, arcVf_ofFrame,
    (lamAlpha_lamBeta_lamGamma_eq_sqrt_three_mul _).1,
    (lamAlpha_lamBeta_lamGamma_eq_sqrt_three_mul _).2.1,
    (lamAlpha_lamBeta_lamGamma_eq_sqrt_three_mul _).2.2]
  simp only [smul_ofFrame, ofFrame_sub, ofFrame_add, traceForm_ofFrame]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [lamAlphaDivSqrtThree, lamBetaDivSqrtThree, lamGammaDivSqrtThree, ArcParams.A,
      ArcParams.B, ArcParams.B', ArcParams.Y', arcParams] <;>
    field_simp <;> ring

/-- (5.4) on a section point (the content of `iso_vfΛ₁_one_eq_arcParams`). -/
private lemma iso_vfΛ₁_one_eq_eigenbasis (hq : IsArcSectionPt q) (t : ℝ) :
    iso_vfΛ₁ 1 q t =
      (arcParams q).lamAlpha • (iso_vfX 1 q t + iso_vfP 1 q) +
        ((arcParams q).lamBeta * Real.exp (2 * t / arcEps q)) • arcVe (iso_vfX 1 q t) +
        ((arcParams q).lamGamma * Real.exp (-2 * t / arcEps q)) • arcVf (iso_vfX 1 q t) := by
  obtain ⟨h1, h2, h3⟩ := eigenbasis_coeffs_eq_arcParams hq
  rw [iso_vfΛ₁_one_eq hq.2 hq.1.1.2.1 t, h1, h2, h3]

/-- The frame of `Λ̂(t)/√3 = (Λ₁(t) + (3/2) J)/√3` along the arc, `s = e^{t/ε}`: `H`-component. -/
private noncomputable def lamHatFrameH (a : ArcParams) (s : ℝ) : ℝ :=
  lamAlphaDivSqrtThree a * (-a.eps - 1 / (2 * a.eps)) +
    lamBetaDivSqrtThree a * s ^ 2 * (-2 * a.eps * a.Y / s) +
    lamGammaDivSqrtThree a / s ^ 2 * (a.eps * a.Y' * s / 2) - 1 / 2

/-- The frame of `Λ̂(t)/√3` along the arc: `E`-component. -/
private noncomputable def lamHatFrameE (a : ArcParams) (s : ℝ) : ℝ :=
  lamAlphaDivSqrtThree a * (-2 * a.eps * a.Y / s) +
    lamBetaDivSqrtThree a * s ^ 2 * (-(-2 * a.eps * a.Y / s) ^ 2 / a.eps) +
    lamGammaDivSqrtThree a / s ^ 2 * a.eps - 2

/-- The frame of `Λ̂(t)/√3` along the arc: `F`-component. -/
private noncomputable def lamHatFrameF (a : ArcParams) (s : ℝ) : ℝ :=
  lamAlphaDivSqrtThree a * (a.eps * a.Y' * s / 2) + lamBetaDivSqrtThree a * s ^ 2 * a.eps +
    lamGammaDivSqrtThree a / s ^ 2 * (-(a.eps * a.Y' * s / 2) ^ 2 / a.eps) + 1 / 2

/-- The state and the reduced costate `Λ̂(t) = Λ₁(t) + (3/2) J` along the arc, in the frame. -/
private lemma iso_vfX_iso_vfΛ₁_eq_ofFrame (hq : IsArcSectionPt q) (t : ℝ) :
    iso_vfX 1 q t = ofFrame (-(arcParams q).eps)
        (-2 * (arcParams q).eps * (arcParams q).Y / Real.exp (t / arcEps q))
        ((arcParams q).eps * (arcParams q).Y' * Real.exp (t / arcEps q) / 2) ∧
      iso_vfΛ₁ 1 q t + (3 / 2 : ℝ) • J =
        √3 • ofFrame (lamHatFrameH (arcParams q) (Real.exp (t / arcEps q)))
          (lamHatFrameE (arcParams q) (Real.exp (t / arcEps q)))
          (lamHatFrameF (arcParams q) (Real.exp (t / arcEps q))) := by
  have hX := hq.2
  have hε := (arcEps_pos hX).ne'
  have hs0 : Real.exp (t / arcEps q) ≠ 0 := (Real.exp_pos _).ne'
  have hneg : Real.exp (-t / arcEps q) = (Real.exp (t / arcEps q))⁻¹ := by
    rw [neg_div, Real.exp_neg]
  have h2 : Real.exp (2 * t / arcEps q) = Real.exp (t / arcEps q) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h2' : Real.exp (-2 * t / arcEps q) = (Real.exp (t / arcEps q) ^ 2)⁻¹ := by
    rw [← h2, ← Real.exp_neg]
    congr 1
    ring
  have hXt : iso_vfX 1 q t = ofFrame (-(arcParams q).eps)
      (-2 * (arcParams q).eps * (arcParams q).Y / Real.exp (t / arcEps q))
      ((arcParams q).eps * (arcParams q).Y' * Real.exp (t / arcEps q) / 2) := by
    rw [iso_vfX_one_eq hX t, hneg, arcParams_Y' hX]
    refine ofFrame_congr rfl ?_ ?_ <;> simp only [arcParams] <;> ring
  refine ⟨hXt, ?_⟩
  rw [iso_vfΛ₁_one_eq_eigenbasis hq t, hXt, iso_vfP_one_eq hX, h2, h2', arcVe_ofFrame,
    arcVf_ofFrame, three_halves_smul_J_eq_ofFrame,
    (lamAlpha_lamBeta_lamGamma_eq_sqrt_three_mul _).1,
    (lamAlpha_lamBeta_lamGamma_eq_sqrt_three_mul _).2.1,
    (lamAlpha_lamBeta_lamGamma_eq_sqrt_three_mul _).2.2]
  simp only [smul_ofFrame, ofFrame_add]
  refine ofFrame_congr ?_ ?_ ?_ <;>
    simp only [lamHatFrameH, lamHatFrameE, lamHatFrameF, arcParams] <;> ring

/-- The rotated point `Ad_{R⁻¹} q(t)` in the frame: `ε_n = ε (Y - s)/s`. -/
private lemma adRinv_vertexFlow_eq_ofFrame (hq : IsArcSectionPt q) (t : ℝ) :
    (iso_adRinvPow 1 (iso_vertexFlow 1 q t)).1 =
        ofFrame (-((arcParams q).eps * ((arcParams q).Y - Real.exp (t / arcEps q)) /
            Real.exp (t / arcEps q)))
          (-2 * (arcParams q).eps * (arcParams q).Y / Real.exp (t / arcEps q) +
            4 * (arcParams q).eps -
            2 * (arcParams q).eps * (arcParams q).Y' * Real.exp (t / arcEps q))
          ((arcParams q).eps * (arcParams q).Y / (2 * Real.exp (t / arcEps q))) ∧
      (iso_adRinvPow 1 (iso_vertexFlow 1 q t)).2.1 + (3 / 2 : ℝ) • J =
        √3 • ofFrame
          (lamHatFrameE (arcParams q) (Real.exp (t / arcEps q)) / 2 -
            lamHatFrameH (arcParams q) (Real.exp (t / arcEps q)))
          (lamHatFrameE (arcParams q) (Real.exp (t / arcEps q)) -
            4 * lamHatFrameH (arcParams q) (Real.exp (t / arcEps q)) -
            4 * lamHatFrameF (arcParams q) (Real.exp (t / arcEps q)))
          (-lamHatFrameE (arcParams q) (Real.exp (t / arcEps q)) / 4) := by
  obtain ⟨hXt, hΛt⟩ := iso_vfX_iso_vfΛ₁_eq_ofFrame hq t
  have hs0 : Real.exp (t / arcEps q) ≠ 0 := (Real.exp_pos _).ne'
  have hJ : R⁻¹ * J * R = J := by simpa using poly_conj_pow_J 1
  simp only [iso_adRinvPow, iso_vertexFlow, pow_one]
  refine ⟨?_, ?_⟩
  · rw [hXt, adRinv_ofFrame]
    refine ofFrame_congr ?_ ?_ ?_ <;> field_simp <;> ring
  · rw [show R⁻¹ * iso_vfΛ₁ 1 q t * R + (3 / 2 : ℝ) • J =
        R⁻¹ * (iso_vfΛ₁ 1 q t + (3 / 2 : ℝ) • J) * R by rw [poly_conj_add, poly_conj_smul, hJ],
      hΛt, poly_conj_smul, adRinv_ofFrame]

/-- `s = e^{t/ε} < Y` before the exit time. -/
private lemma exp_div_arcEps_lt_arcY (hq : IsArcSectionPt q) {t : ℝ} (ht : t < arcExitTime q) :
    Real.exp (t / arcEps q) < arcY q := by
  have hε := arcEps_pos hq.2
  have hY := one_lt_arcY hq.2
  rw [← Real.exp_log (by linarith : (0 : ℝ) < arcY q)]
  refine Real.exp_lt_exp.2 ?_
  rw [div_lt_iff₀ hε, mul_comm]
  exact ht

/-- `arcP` of the rotated point (the content of `arcP_adRinv_vertexFlow`). -/
private lemma arcP_adRinv_vertexFlow_eq_pNew (hq : IsArcSectionPt q) {t : ℝ}
    (ht : t < arcExitTime q) :
    arcP (iso_adRinvPow 1 (iso_vertexFlow 1 q t)) =
      (arcParams q).pNew (Real.exp (t / arcEps q)) := by
  have hε := (arcEps_pos hq.2).ne'
  have hY : arcY q ≠ 0 := (zero_lt_one.trans (one_lt_arcY hq.2)).ne'
  have hsY := (sub_pos.2 (exp_div_arcEps_lt_arcY hq ht)).ne'
  have hs0 : Real.exp (t / arcEps q) ≠ 0 := (Real.exp_pos _).ne'
  obtain ⟨hXn, hΛn⟩ := adRinv_vertexFlow_eq_ofFrame hq t
  rw [arcP, show arcEps (iso_adRinvPow 1 (iso_vertexFlow 1 q t)) =
      ρ₁ (iso_adRinvPow 1 (iso_vertexFlow 1 q t)).1 from rfl, hΛn, hXn,
    ivf_traceForm_smul_left, two_div_sqrt_three_mul_sqrt_three, arcVf_ofFrame,
    (ρ_ofFrame _ _ _).1, traceForm_ofFrame]
  generalize Real.exp (t / arcEps q) = s at hsY hs0 ⊢
  simp only [lamHatFrameH, lamHatFrameE, lamHatFrameF, lamAlphaDivSqrtThree, lamBetaDivSqrtThree,
    lamGammaDivSqrtThree, ArcParams.pNew, ArcParams.A, ArcParams.B, ArcParams.B', ArcParams.Y',
    arcParams]
  field_simp
  ring

/-- `f₀` of the rotated point, when it is a section point ((2.4) and the closed form (5.4)):
`s² Ψ(s)/(Y (Y - s)²)`. -/
private lemma arcF0_adRinv_vertexFlow_eq_f0New (hq : IsArcSectionPt q) {t : ℝ}
    (ht : t < arcExitTime q) (hn : IsArcSectionPt (iso_adRinvPow 1 (iso_vertexFlow 1 q t))) :
    arcF0 (iso_adRinvPow 1 (iso_vertexFlow 1 q t)) =
      (arcParams q).f0New (Real.exp (t / arcEps q)) := by
  have hε := (arcEps_pos hq.2).ne'
  have hY : arcY q ≠ 0 := (zero_lt_one.trans (one_lt_arcY hq.2)).ne'
  have hsY := (sub_pos.2 (exp_div_arcEps_lt_arcY hq ht)).ne'
  have hs0 : Real.exp (t / arcEps q) ≠ 0 := (Real.exp_pos _).ne'
  obtain ⟨hXn, hΛn⟩ := adRinv_vertexFlow_eq_ofFrame hq t
  have hY'n : arcY' (iso_adRinvPow 1 (iso_vertexFlow 1 q t)) =
      arcY q / (arcY q - Real.exp (t / arcEps q)) := by
    rw [arcY', hXn, (ρ_ofFrame _ _ _).2.2, (ρ_ofFrame _ _ _).1]
    simp only [arcParams]
    field_simp
    ring
  rw [arcF0_eq_reducedHam hn, reducedHam, show arcEps (iso_adRinvPow 1 (iso_vertexFlow 1 q t)) =
      ρ₁ (iso_adRinvPow 1 (iso_vertexFlow 1 q t)).1 from rfl, hY'n, hΛn, hXn,
    ivf_traceForm_smul_left, sqrt_three_div_three_mul_sqrt_three, (ρ_ofFrame _ _ _).1,
    traceForm_ofFrame]
  generalize Real.exp (t / arcEps q) = s at hsY hs0 ⊢
  simp only [lamHatFrameH, lamHatFrameE, lamHatFrameF, lamAlphaDivSqrtThree, lamBetaDivSqrtThree,
    lamGammaDivSqrtThree, ArcParams.f0New, ArcParams.Psi, ArcParams.A, ArcParams.B, ArcParams.B',
    ArcParams.Y', arcParams]
  field_simp
  ring

/-- `Ad_{R⁻¹}` permutes the star functions: `(ρ₀, ρ₁, ρ₂)(R⁻¹ X R) = (ρ₁, ρ₂, ρ₀)(X)` for
traceless `X`. -/
theorem ρ_adRinv (hX : q.1.trace = 0) :
    ρ₀ (iso_adRinvPow 1 q).1 = ρ₁ q.1 ∧ ρ₁ (iso_adRinvPow 1 q).1 = ρ₂ q.1 ∧
      ρ₂ (iso_adRinvPow 1 q).1 = ρ₀ q.1 := by
  have htr : (R⁻¹ * q.1 * R).trace = 0 := by rw [poly_trace_conj poly_R_mul_inv, hX]
  have hρ := ρ_R_conj (R⁻¹ * q.1 * R) htr
  rw [show R * (R⁻¹ * q.1 * R) * R⁻¹ = (R * R⁻¹) * q.1 * (R * R⁻¹) by
    simp only [Matrix.mul_assoc], poly_R_mul_inv, Matrix.one_mul, Matrix.mul_one] at hρ
  simp only [iso_adRinvPow, pow_one]
  exact ⟨hρ.2.1.symm, hρ.2.2.symm, hρ.1.symm⟩

/-- **The relabelling** of the cleared numerators under `Ad_{R⁻¹}`:
`N_{i+1, j+1}(Ad_{R⁻¹} q) = N_{ij}(q)` (`R⁻¹ Z_{e_m} R = Z_{e_{m+1}}`). -/
theorem switchingNum_adRinv (i j : Fin 3) (q : iso_PhasePt) :
    switchingNum (i + 1) (j + 1) (iso_adRinvPow 1 q) = switchingNum i j q := by
  simp only [switchingNum, iso_adRinvPow, pow_one]
  rw [← poly_Rinv_conj_vertex i, ← poly_Rinv_conj_vertex j, poly_traceForm_conj poly_R_mul_inv,
    poly_traceForm_conj poly_R_mul_inv, poly_traceForm_conj poly_R_mul_inv,
    poly_traceForm_conj poly_R_mul_inv]

/-- The switching time is `ε τ_sw`, and `τ_sw` is a zero of `f`. -/
theorem reinSwitchTime_eq_tauSw (hq : IsArcSectionPt q) (hs : SwitchesBeforeExit q) :
    reinSwitchTime q = arcEps q * (arcParams q).tauSw ∧
      (arcParams q).f (arcParams q).tauSw = 0 := by
  have hX := hq.2
  have hε := arcEps_pos hX
  obtain ⟨hpos, hlt⟩ := hs
  set S := {t : ℝ | 0 < t ∧
    switchingFn 1 0 (iso_vertexFlow 1 q t).2.2 (iso_vertexFlow 1 q t).1 = 0} with hSdef
  set S' := {τ : ℝ | 0 < τ ∧ (arcParams q).f τ = 0} with hS'def
  have hT : arcExitTime q = arcEps q * Real.log (arcY q) := rfl
  have hsw : reinSwitchTime q = sInf S := rfl
  have hSne : S.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [hsw, h, Real.sInf_empty] at hpos
    exact lt_irrefl _ hpos
  have hglb : IsGLB S (reinSwitchTime q) := isGLB_csInf hSne ⟨0, fun t ht ↦ ht.1.le⟩
  obtain ⟨t₁, ht₁S, ht₁lt⟩ := exists_lt_of_csInf_lt hSne hlt
  -- the zeros of `χ₂₁` before the exit are `ε` times the zeros of `f` before `log Y`
  have hlow : ∀ τ ∈ S', reinSwitchTime q ≤ arcEps q * τ := by
    rintro τ ⟨hτ, hf⟩
    by_cases hτT : arcEps q * τ < arcExitTime q
    · refine hglb.1 ⟨by positivity, (switchingFn_one_zero_eq_zero_iff hq (by positivity) hτT).2 ?_⟩
      rwa [mul_div_cancel_left₀ _ hε.ne']
    · linarith
  have hglb' : IsGLB S' (reinSwitchTime q / arcEps q) := by
    refine ⟨fun τ hτ ↦ by rw [div_le_iff₀ hε, mul_comm]; exact hlow τ hτ, fun b hb ↦ ?_⟩
    have hb' : ∀ t ∈ S, t < arcExitTime q → arcEps q * b ≤ t := by
      rintro t ⟨ht0, hχ⟩ htT
      have := hb ⟨by positivity, (switchingFn_one_zero_eq_zero_iff hq ht0.le htT).1 hχ⟩
      rwa [le_div_iff₀ hε, mul_comm] at this
    have hb₁ := hb' t₁ ht₁S ht₁lt
    have : arcEps q * b ≤ reinSwitchTime q := hglb.2 fun t ht ↦ by
      by_cases htT : t < arcExitTime q
      · exact hb' t ht htT
      · linarith
    rwa [le_div_iff₀ hε, mul_comm]
  have hS'ne : S'.Nonempty :=
    ⟨t₁ / arcEps q, by positivity [ht₁S.1],
      (switchingFn_one_zero_eq_zero_iff hq ht₁S.1.le ht₁lt).1 ht₁S.2⟩
  have htau : (arcParams q).tauSw = reinSwitchTime q / arcEps q := hglb'.csInf_eq hS'ne
  refine ⟨by rw [htau]; field_simp, ?_⟩
  have hcont : Continuous (arcParams q).f :=
    continuous_iff_continuousAt.2 fun τ ↦ ((arcParams q).hasDerivAt_f τ).continuousAt
  have hcl : IsClosed {τ | (arcParams q).f τ = 0} := isClosed_eq hcont continuous_const
  have hmem := hglb'.mem_closure hS'ne
  rw [← htau] at hmem
  exact closure_minimal (fun τ (hτ : τ ∈ S') ↦ hτ.2) hcl hmem

/-- At the switch, `χ₂₁(q(t_sw)) = 0`. -/
private lemma switchingFn_one_zero_reinSwitchTime_eq_zero (hq : IsArcSectionPt q)
    (hs : SwitchesBeforeExit q) :
    switchingFn 1 0 (iso_vertexFlow 1 q (reinSwitchTime q)).2.2
      (iso_vertexFlow 1 q (reinSwitchTime q)).1 = 0 := by
  obtain ⟨hτ, hf⟩ := reinSwitchTime_eq_tauSw hq hs
  rw [switchingFn_one_zero_eq_zero_iff hq hs.1.le hs.2, hτ,
    mul_div_cancel_left₀ _ (arcEps_pos hq.2).ne']
  exact hf

/-- **Theorem 5.1**: the image of a section point whose arc switches inside the star domain is a
section point. -/
theorem isArcSectionPt_reinPoincare (hq : IsArcSectionPt q) (hs : SwitchesBeforeExit q) :
    IsArcSectionPt (reinPoincare q) := by
  have hH := phaseHam_vertex_one_eq_zero hq
  have hχ := switchingFn_one_zero_reinSwitchTime_eq_zero hq hs
  obtain ⟨⟨⟨h1, h2, h3, h4, h5, -, -⟩, h8⟩, hX⟩ := hq
  obtain ⟨k1, k2, k3⟩ := irt_vertexFlow_traceless 1 h1 h2 h3 (reinSwitchTime q)
  have hstar : IsStarState (iso_vertexFlow 1 q (reinSwitchTime q)).1 :=
    (isStarState_iso_vfX_one_iff hX hs.1.le).2 hs.2
  have hJ : R⁻¹ * J * R = J := by simpa using poly_conj_pow_J 1
  have hH0 := poly_hamiltonian_conj poly_R_mul_inv hJ (poly_Rinv_conj_vertex 0) (-1)
    (iso_vertexFlow 1 q (reinSwitchTime q)).2.1 (iso_vertexFlow 1 q (reinSwitchTime q)).2.2
    (iso_vertexFlow 1 q (reinSwitchTime q)).1
  have hH1 := poly_hamiltonian_conj poly_R_mul_inv hJ (poly_Rinv_conj_vertex 1) (-1)
    (iso_vertexFlow 1 q (reinSwitchTime q)).2.1 (iso_vertexFlow 1 q (reinSwitchTime q)).2.2
    (iso_vertexFlow 1 q (reinSwitchTime q)).1
  have hd10 := hamiltonian_sub_eq_switchingFn (iso_vertexFlow 1 q (reinSwitchTime q)).2.1
    (iso_vertexFlow 1 q (reinSwitchTime q)).2.2 (iso_vertexFlow 1 q (reinSwitchTime q)).1 1 0
  have hcons := hamiltonian_vertexFlow 1 q (reinSwitchTime q)
  simp only [reinPoincare, iso_adRinvPow, pow_one]
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · rw [poly_trace_conj poly_R_mul_inv]; exact k1
  · rw [poly_trace_conj poly_R_mul_inv]; exact k2
  · rw [poly_trace_conj poly_R_mul_inv]; exact k3
  · rw [poly_det_conj poly_R_mul_inv, det_vertexFlow_fst]; exact h4
  · rw [poly_traceForm_conj poly_R_mul_inv, traceForm_vertexFlow]; exact h5
  · -- `H(e₃)(F q) = H(e₂)(q(t_sw)) = H(e₂)(q) = 0`
    change hamiltonian (-1) _ _ _ (vertex (1 + 1)) = 0
    rw [hH1, hcons]
    exact hH
  · -- `χ₂₃(F q) = χ₁₂(q(t_sw)) = -χ₂₁(q(t_sw)) = 0`
    rw [← hamiltonian_sub_eq_switchingFn (R⁻¹ * (iso_vertexFlow 1 q (reinSwitchTime q)).2.1 * R)]
    change hamiltonian (-1) _ _ _ (vertex (0 + 1)) - hamiltonian (-1) _ _ _ (vertex (1 + 1)) = 0
    rw [hH0, hH1]
    linarith
  · rw [poly_det_conj poly_R_mul_inv, det_vertexFlow_snd]; exact h8
  · exact poly_isStarState_Rinv_conj hstar

/-- **Theorem 5.1**: `(ρ₀, ρ₁, ρ₂)(F q) = (ρ₁(q), ρ₂(X(t_sw)), ρ₀(X(t_sw)))`. It holds for every
section point, whether or not its arc switches before it exits (`SwitchesBeforeExit`). -/
theorem ρ_reinPoincare (hq : IsArcSectionPt q) :
    ρ₀ (reinPoincare q).1 = ρ₁ q.1 ∧
      ρ₁ (reinPoincare q).1 = ρ₂ (iso_vfX 1 q (reinSwitchTime q)) ∧
      ρ₂ (reinPoincare q).1 = ρ₀ (iso_vfX 1 q (reinSwitchTime q)) := by
  obtain ⟨⟨⟨h1, h2, h3, -⟩, -⟩, hX⟩ := hq
  obtain ⟨a, b, c⟩ := ρ_adRinv (q := iso_vertexFlow 1 q (reinSwitchTime q))
    (irt_vertexFlow_traceless 1 h1 h2 h3 (reinSwitchTime q)).1
  exact ⟨a.trans (ρ_iso_vfX_one hX _).1, b, c⟩

/-- `ε_new = ρ₁(F q) = ρ₂(X(t_sw)) = ε k`. -/
private lemma ρ₁_reinPoincare (hq : IsArcSectionPt q) (hs : SwitchesBeforeExit q) :
    ρ₁ (reinPoincare q).1 = arcEps q * (arcParams q).stepK := by
  have hε := arcEps_pos hq.2
  obtain ⟨hτ, -⟩ := reinSwitchTime_eq_tauSw hq hs
  rw [(ρ_reinPoincare hq).2.1, (ρ_iso_vfX_one hq.2 _).2.1, hτ, neg_div,
    mul_div_cancel_left₀ _ hε.ne']
  rfl

/-- **Theorem 5.1** (the Reinhardt–Poincaré map as an explicit map of the parameters). Let `q` be a
section point whose `e₂`-arc switches inside the star domain. Then `k = Y e^{-τ_sw} - 1 > 0` and
`arcParams (F q) = (arcParams q).step q_new` with `q_new = arcQ (F q)`: `ε_new = k ε`,
`Y_new = 1 + (Y' e^{τ_sw} - 1)/k`, `f₀,new = g(τ_sw)/k²`, `g₀,new = 0`, `p_new = -f'(τ_sw)/k²`;
`q_new` is a root of the quadric relation at the new point (`arcParams_rel`). -/
theorem arcParams_reinPoincare (hq : IsArcSectionPt q) (hs : SwitchesBeforeExit q) :
    0 < (arcParams q).stepK ∧
      arcParams (reinPoincare q) = (arcParams q).step (arcQ (reinPoincare q)) := by
  have hX := hq.2
  have hε := arcEps_pos hX
  have hY : arcY q ≠ 0 := (zero_lt_one.trans (one_lt_arcY hX)).ne'
  obtain ⟨hτ, hf⟩ := reinSwitchTime_eq_tauSw hq hs
  have hn := isArcSectionPt_reinPoincare hq hs
  have htτ : reinSwitchTime q / arcEps q = (arcParams q).tauSw := by
    rw [hτ, mul_div_cancel_left₀ _ hε.ne']
  have hsY : Real.exp (arcParams q).tauSw < arcY q := htτ ▸ exp_div_arcEps_lt_arcY hq hs.2
  have hs0 : 0 < Real.exp (arcParams q).tauSw := Real.exp_pos _
  have hk : 0 < (arcParams q).stepK := by
    simp only [ArcParams.stepK, Real.exp_neg]
    rw [sub_pos, ← div_eq_mul_inv, one_lt_div hs0]
    exact hsY
  refine ⟨hk, ?_⟩
  have hρ₁ := ρ₁_reinPoincare hq hs
  have e1 : arcEps (reinPoincare q) = (arcParams q).stepK * (arcParams q).eps := by
    rw [show arcEps (reinPoincare q) = ρ₁ (reinPoincare q).1 from rfl, hρ₁, mul_comm]
    rfl
  have e2 : arcY (reinPoincare q) =
      1 + ((arcParams q).Y' * Real.exp (arcParams q).tauSw - 1) / (arcParams q).stepK := by
    rw [arcY, hρ₁, (ρ_reinPoincare hq).2.2, (ρ_iso_vfX_one hX _).2.2, htτ,
      ← arcParams_Y' hX, mul_div_mul_left _ _ hε.ne']
  have e3 : arcF0 (reinPoincare q) = (arcParams q).g (arcParams q).tauSw /
      ((arcParams q).Y * Real.exp (-(arcParams q).tauSw) - 1) ^ 2 := by
    have h := arcF0_adRinv_vertexFlow_eq_f0New hq hs.2 hn
    rw [htτ] at h
    rw [ArcParams.g_div_sq_eq_f0New _ (arcG0_eq_zero hq) hf hY (sub_pos.2 hsY).ne']
    exact h
  have e6 : arcP (reinPoincare q) = -(arcParams q).fDeriv (arcParams q).tauSw /
      ((arcParams q).Y * Real.exp (-(arcParams q).tauSw) - 1) ^ 2 := by
    have h := arcP_adRinv_vertexFlow_eq_pNew hq hs.2
    rw [htτ] at h
    rw [ArcParams.neg_fDeriv_div_sq_eq_pNew _ hf (sub_pos.2 hsY).ne']
    exact h
  calc arcParams (reinPoincare q)
      = ⟨arcEps (reinPoincare q), arcY (reinPoincare q), arcF0 (reinPoincare q),
          arcG0 (reinPoincare q), arcQ (reinPoincare q), arcP (reinPoincare q)⟩ := rfl
    _ = ⟨(arcParams q).stepK * (arcParams q).eps,
          1 + ((arcParams q).Y' * Real.exp (arcParams q).tauSw - 1) / (arcParams q).stepK,
          (arcParams q).g (arcParams q).tauSw /
            ((arcParams q).Y * Real.exp (-(arcParams q).tauSw) - 1) ^ 2, 0,
          arcQ (reinPoincare q), -(arcParams q).fDeriv (arcParams q).tauSw /
            ((arcParams q).Y * Real.exp (-(arcParams q).tauSw) - 1) ^ 2⟩ := by
        rw [e1, e2, e3, arcG0_eq_zero hn, e6]
    _ = (arcParams q).step (arcQ (reinPoincare q)) := rfl

/-! ### Theorem 5.1: the costate in closed form -/

/-- **(5.4) on a section point** (the costate in closed form, proof of Theorem 5.1): along
the `e₂`-arc from a
section point, with `u = e^{-t/ε}`,
`Λ₁(t) = α (X(t) + P) + β u⁻² V_e(X(t)) + γ u² V_f(X(t))`,
`α = √3 ε (1 + ε²(Y + Y'A - Y B'))`, `β = -(√3/2) ε³ (Y'² - B')`, `γ = 2√3 ε³ (Y² - B)`
(`ArcParams.lamAlpha`, `lamBeta`, `lamGamma`).

Route: `iso_vfΛ₁_one_eq` (`SmoothedPolygons/Ch14/ArcCostate.lean`) gives the form with
`α = 2ε² ⟨Λ₁(0), X₀ + P⟩`, `β = ε² ⟨Λ₁(0), V_f⟩`, `γ = ε² ⟨Λ₁(0), V_e⟩`. For the coefficients:
`frame_reducedCostate` gives the frame `(l_h, l_e, l_f)` of `Λ̂₀`, so
`Λ₁(0) = Λ̂₀ - (3/2) J = ofFrame (l_h + √3/2) (l_e + 2√3) (l_f - √3/2)` (`frame_controlMatrix`:
`J = ofFrame (-1/√3) (-4/√3) (1/√3)`); pair with `X₀ + P = ofFrame (-ε - 1/(2ε)) x_e x_f`,
`V_f`, `V_e` (`traceForm_ofFrame`, `frame_state`, `iso_vfP_one_eq`) and simplify with
`ε² Y Y' = 1 + ε²` and `√3² = 3` (`field_simp`, `ring`). Equivalently (Proposition 3.1):
`⟨Λ̂₀, V_e⟩ = -2√3 ε q`, `⟨Λ̂₀, V_f⟩ = (√3/2) ε p` (definitions of `arcQ`, `arcP`),
`⟨J, V_e⟩ = -(4ε/√3)(Y² - Y + 1)`, `⟨J, V_f⟩ = (ε/√3)(Y'² - Y' + 1)`. Also checked exactly with
sympy against the literal definitions. -/
theorem iso_vfΛ₁_one_eq_arcParams (hq : IsArcSectionPt q) (t : ℝ) :
    iso_vfΛ₁ 1 q t =
      (arcParams q).lamAlpha • (iso_vfX 1 q t + iso_vfP 1 q) +
        ((arcParams q).lamBeta * Real.exp (2 * t / arcEps q)) • arcVe (iso_vfX 1 q t) +
        ((arcParams q).lamGamma * Real.exp (-2 * t / arcEps q)) • arcVf (iso_vfX 1 q t) :=
  iso_vfΛ₁_one_eq_eigenbasis hq t

/-- **Theorem 5.1 for `p`, at every time of the arc**: for a section point `q` and `t < T`,
with `s = e^{t/ε}`, the rotated point `Ad_{R⁻¹} q(t)` has `arcP = π(s)/(Y - s)²`
(`ArcParams.pNew`, `π(s) = s² - Y s + B`). At `t = t_sw` this is `p_new` (with
`ArcParams.neg_fDeriv_div_sq_eq_pNew`, `-f'(τ_sw)/k²`), without Lemma 4.1.

Route: with `V_{f,n}` the matrix `V_f` of the rotated state carried back by `Ad_R`,
`k_s = Y - s` and (5.4), only `γ` and `J` pair with `V_{f,n}`:
`⟨Λ̂(t), V_{f,n}⟩ = γ s⁻² (-s/(4ε² k_s)) + (3/2)(ε/(√3 s k_s))(s² - Y s + Y²)
= (√3 ε/(2 s k_s)) π(s)` (`γ = 2√3 ε³ (Y² - B)`), and `arcP = (2/(√3 ε_n)) ⟨…⟩ = π(s)/k_s²`. -/
theorem arcP_adRinv_vertexFlow (hq : IsArcSectionPt q) {t : ℝ} (ht : t < arcExitTime q) :
    arcP (iso_adRinvPow 1 (iso_vertexFlow 1 q t)) =
      (arcParams q).pNew (Real.exp (t / arcEps q)) :=
  arcP_adRinv_vertexFlow_eq_pNew hq ht

/-- **Theorem 5.1**, the radius: `r(F q) = (ρ₁(q) - ρ₁(F q))/2 = ε (1 - k)/2`. -/
theorem radius_reinPoincare (hq : IsArcSectionPt q) (hs : SwitchesBeforeExit q) :
    (reinPoincare q).1 0 0 = (ρ₁ q.1 - ρ₁ (reinPoincare q).1) / 2 ∧
      (reinPoincare q).1 0 0 = arcEps q * (1 - (arcParams q).stepK) / 2 := by
  have hρ := ρ_reinPoincare hq
  have h00 : ∀ M : Mat2, M 0 0 = (ρ₀ M - ρ₁ M) / 2 := fun M ↦ by
    simp only [ρ₀, ρ₁]
    field_simp
    ring
  have hρ₁ := ρ₁_reinPoincare hq hs
  exact ⟨by rw [h00 (reinPoincare q).1, hρ.1], by
    rw [h00 (reinPoincare q).1, hρ.1, hρ₁, show ρ₁ q.1 = arcEps q from rfl]; ring⟩

/-- **Corollary 5.3** (telescoping): along an orbit of section points that switch inside the
star domain, `Σ_{n=1}^{N} r(F^n q) = (ρ₁(q) - ρ₁(F^N q))/2`. -/
theorem sum_radius_reinPoincare_iterate (q : iso_PhasePt) (N : ℕ)
    (h : ∀ n < N, IsArcSectionPt (reinPoincare^[n] q) ∧ SwitchesBeforeExit (reinPoincare^[n] q)) :
    ∑ n ∈ Finset.range N, (reinPoincare^[n + 1] q).1 0 0 =
      (ρ₁ q.1 - ρ₁ (reinPoincare^[N] q).1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    obtain ⟨h1, h2⟩ := h N (by omega)
    rw [Finset.sum_range_succ, ih fun n hn ↦ h n (by omega), Function.iterate_succ_apply',
      (radius_reinPoincare h1 h2).1]
    ring

/-- **Corollary 5.3**: the radii of the switching points along such an orbit sum to less than
`ρ₁(q₀)/2`. -/
theorem sum_radius_reinPoincare_iterate_lt (hq : IsArcSectionPt q) (N : ℕ)
    (h : ∀ n < N, IsArcSectionPt (reinPoincare^[n] q) ∧ SwitchesBeforeExit (reinPoincare^[n] q)) :
    ∑ n ∈ Finset.range N, (reinPoincare^[n + 1] q).1 0 0 < ρ₁ q.1 / 2 := by
  rw [sum_radius_reinPoincare_iterate q N h]
  have hpos : 0 < ρ₁ (reinPoincare^[N] q).1 := by
    rcases N with _ | N
    · exact hq.2.2.2.2.1
    · obtain ⟨h1, h2⟩ := h N (by omega)
      rw [Function.iterate_succ_apply']
      exact (isArcSectionPt_reinPoincare h1 h2).2.2.2.2.1
  linarith

/-- **Corollary 5.3**: an orbit that switches forever (with nonnegative radii) has `r_n → 0`: it
chatters into the divisor. -/
theorem tendsto_radius_reinPoincare_iterate
    (h : ∀ n, IsArcSectionPt (reinPoincare^[n] q) ∧ SwitchesBeforeExit (reinPoincare^[n] q))
    (hr : ∀ n, 0 ≤ (reinPoincare^[n + 1] q).1 0 0) :
    Tendsto (fun n ↦ (reinPoincare^[n] q).1 0 0) atTop (𝓝 0) := by
  have hsum : ∀ N, ∑ n ∈ Finset.range N, (reinPoincare^[n + 1] q).1 0 0 ≤ ρ₁ q.1 / 2 :=
    fun N ↦ (sum_radius_reinPoincare_iterate_lt (h 0).1 N fun n _ ↦ h n).le
  exact (tendsto_add_atTop_iff_nat 1).mp (summable_of_sum_range_le hr hsum).tendsto_atTop_zero

end SmoothedPolygons
