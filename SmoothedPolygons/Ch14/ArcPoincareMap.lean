module

public import SmoothedPolygons.Ch14.ArcRelation
public import SmoothedPolygons.Ch14.ArcStepClosed
public import SmoothedPolygons.Ch14.VertexPoissonBracket
import SmoothedPolygons.Ch7.Isolated.VertexFlow
import SmoothedPolygons.Ch7.Isolated.Return

/-!
# Chapter 14, N4: the Reinhardt–Poincaré map in closed form (Theorem 2.1, Corollary 2.4)

Part of the formalization's proof of N4 (`UnstableCurveLeavesStarDomain`, Figure 14.2) without
computer assistance. **Departure from the paper**, by the user's decision: the book reads N4 off a
computed figure (Figure 14.2, TeX 11951–11991; REPORT.md E88); the formalization proves it from
the exact structure of the Reinhardt flow along an `e₂`-arc and an invariant region (see
`SmoothedPolygons/Ch14/ArcParams.lean`, and `SmoothedPolygons/Ch14/ArcRegionInvariant.lean` for
the numbering of the steps).

This file is §2.2: if the `e₂`-arc from a section point `q` switches inside the star domain, its
image `F(q) = reinPoincare q = Ad_{R⁻¹} q(t_sw)` is a section point whose arc parameters are
explicit functions of those of `q` and of the switching root `τ_sw` of the four-term exponential
sum `f` (`ArcParams.step`): no ODE, one root per step. The radii telescope,
`r(F q) = (ρ₁(q) - ρ₁(F q))/2`, so along any orbit that keeps switching they sum to less than
`ρ₁(q₀)/2`. It also holds INV Theorem 1 at the phase point (`q_new` in closed form).

## Statements

* `SwitchesBeforeExit q`: `0 < t_sw(q) < T(q) = ε log Y` (`reinSwitchTime`, `arcExitTime`).
* `ρ_adRinv`: `Ad_{R⁻¹}` permutes the star functions, `(ρ₀, ρ₁, ρ₂)(R⁻¹XR) = (ρ₁, ρ₂, ρ₀)(X)`.
* `switchingNum_adRinv`: the relabelling `N_{i+1, j+1}(Ad_{R⁻¹} q) = N_{ij}(q)`
  (`R⁻¹ Z_{e_m} R = Z_{e_{m+1}}`).
* `reinSwitchTime_eq_tauSw`: `t_sw = ε τ_sw` and `f(τ_sw) = 0`.
* **Theorem 2.1**: `isArcSectionPt_reinPoincare`, `ρ_reinPoincare`
  (`(ρ₀, ρ₁, ρ₂)(F q) = (ρ₁(q), ρ₂(X(t_sw)), ρ₀(X(t_sw)))`), `arcParams_reinPoincare`
  (`arcParams (F q) = (arcParams q).step q_new`: `ε_new = k ε`, `Y_new = 1 + (Y' e^{τ_sw} - 1)/k`,
  `f₀,new = g(τ_sw)/k²`, `g₀,new = 0`, `p_new = -f'(τ_sw)/k²`, with `q_new = arcQ (F q)` a root of
  `R = 0` at the new point, `arcParams_rel`), `radius_reinPoincare`
  (`r(F q) = (ρ₁(q) - ρ₁(F q))/2 = ε(1 - k)/2`).
* **INV Theorem 1** (the map in closed form, including `q_new`):
  `iso_vfΛ₁_one_eq_arcParams` (INV (1.4) on a section point: `Λ₁(t) = α (X(t) + P) + β u⁻² V_e(t)
  + γ u² V_f(t)` with `α, β, γ` explicit in the parameters, `ArcParams.lamAlpha` …);
  `arcQ_adRinv_vertexFlow`, `arcP_adRinv_vertexFlow` (for every `t < T`, with `s = e^{t/ε}`, the
  rotated point `Ad_{R⁻¹} q(t)` has `q = Φ(s)/(Y - s)²` and `p = π(s)/(Y - s)²`, `ArcParams.qNew`,
  `ArcParams.pNew`); `arcQ_reinPoincare` (`q_new = Φ(s)/(Y - s)²` with `s = e^{τ_sw}`: no root of
  (2.1) is chosen anywhere). With `ArcParams.step_closed` this gives every parameter of `F q` as a
  rational function of the old ones and `s`.
* **Corollary 2.4**: `sum_radius_reinPoincare_iterate` (the telescoping identity),
  `sum_radius_reinPoincare_iterate_lt` (`Σ_{n ≥ 1} r_n < ρ₁(q₀)/2`),
  `tendsto_radius_reinPoincare_iterate` (an orbit that switches forever with `r_n ≥ 0` has
  `r_n → 0`: it chatters into the divisor).

## Proofs (the route, Theorem 2.1)

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
5. `f₀,new` (the route of §2.2; a simpler one is below): by step 1 `N₂₁^new = N₁₃(t_sw)`;
   at a zero of `N₂₁`, `χ₁₃ = χ₂₃`, so
   `N₁₃ = N₂₃ ⟨X, Z_{e₁}⟩/⟨X, Z_{e₂}⟩ = N₂₃ ε_new/ε` ((1.1)); normalizing by `8ε_new³/√3` and
   `arc_normalForm` gives `f₀,new = ε² g(τ_sw)/ε_new² = g(τ_sw)/k²`. `g₀,new = 0`
   (`arcG0_eq_zero`).
6. `p_new`: `p = g'(0)` on a section point (`ArcParams.hasDerivAt_g_zero`, `g₀ = 0`), so
   `(8ε_new²/√3) p_new` is the slope at `0` of `N₂₃^new` along the new `e₂`-flow. By step 1,
   `N₂₃^new = -N₂₁` (relabelled), and the new `e₂`-flow is the old `e₁`-flow conjugated by
   `R⁻¹` (`irt_chi_conj`-style relabelling of `iso_vertexFlow`). At the switch `χ₂₁ = 0`, so the
   slope of `N₂₁ = χ₂₁ ⟨X, Z_{e₂}⟩⟨X, Z_{e₁}⟩` is the slope of `χ₂₁` times the common positive
   factor, and the slope of `χ₂₁` along the `e₁`-field equals its slope along the `e₂`-field
   (`phaseHamSlope_chi21`, Lemma 2.3; `hasDerivAt_phaseHam_vertexFlow`). With `arc_normalForm`,
   `ε_new² p_new = -ε² f'(τ_sw)`, i.e. `p_new = -f'(τ_sw)/k²`.
   **Simpler route for steps 5–6** (found in review): `arcQ`, `arcP` and the (1.5) form
   `-(√3/(3ε³Y')) ⟨Λ̂, X⟩` of `f₀` depend only on `(X, Λ₁)`, and `Λ₁(t)` has the closed form
   INV (1.4) (`iso_vfΛ₁_one_eq_arcParams`). So `p_new = π(s)/(Y - s)²` (`arcP_adRinv_vertexFlow`
   at `t = t_sw`), which is `-f'(τ_sw)/k²` by `ArcParams.neg_fDeriv_div_sq_eq_pNew` (it uses
   `f(τ_sw) = 0`); and `f₀,new` is the (1.5) form at the section point `F q`
   (`arcF0_eq_reducedHam`, `isArcSectionPt_reinPoincare`), which the table INV (1.5) evaluates
   to `s² Ψ(s)/(Y (Y - s)²) = g(τ_sw)/k²` (`ArcParams.g_div_sq_eq_f0New`). Then Lemma 2.3
   (`SmoothedPolygons/Ch14/VertexPoissonBracket.lean`) is needed only for `SwitchEntersE2`
   (Proposition 3.4 (1)).
7. `q_new = arcQ (F q)` by definition of `step`; it is a root of `R = 0` by `arcParams_rel` at the
   section point `F q`. Which root: `arcQ_reinPoincare` (`q_new = Φ(s)/(Y - s)²`), from
   `arcQ_adRinv_vertexFlow` at `t = t_sw = ε τ_sw` (`reinSwitchTime_eq_tauSw`).
8. Corollary 2.4: induction on `N` with step 4 (`Finset.sum_range_succ`); the bound from
   `ρ₁(F^N q) > 0` (a section point is a star state); the limit: the partial sums of the
   nonnegative `r_n` are bounded, so the series is summable and `r_n → 0`
   (`Summable.tendsto_atTop_zero`).
9. INV Theorem 1 (`iso_vfΛ₁_one_eq_arcParams`, `arcQ_adRinv_vertexFlow`,
   `arcP_adRinv_vertexFlow`, `arcQ_reinPoincare`): see their docstrings (the eigenframe
   computation, INV §1 (i)–(iii) and the table INV (1.5)).

**What the Lean proofs do.** Steps 5–6 take the simpler route, so Lemma 2.3 is not used here.
`ArcParams.step_closed` is not used either: its hypotheses (P1, P2, `F(log Y) < 0`) are not those
of Theorem 2.1, which needs only `f(τ_sw) = 0` and `1 < s < Y`; its steps 6–7 (eliminate
`Y τ_sw = s - A - B/s`) are the lemmas `ArcParams.g_div_sq_eq_f0New` and
`ArcParams.neg_fDeriv_div_sq_eq_pNew`, which need only these, and which both proofs use.
INV Theorem 1 is computed in the frame: `Ad_{R⁻¹}` acts on frame components by
`(h, e, f) ↦ (e/2 - h, e - 4h - 4f, -e/4)` (from `S⁻¹ R S = [[0, -2], [1/2, 1]]`), the star
functions are `(ρ₀, ρ₁, ρ₂) = (h + 2f, -h, h - e/2)`,
and `(3/2) J = √3 · ofFrame (-1/2) (-2) (1/2)`, so `Λ̂(t) = √3 M(t)` with `M(t)` free of `√3`.
Instead of pairing `Λ̂(t)` with the carried-back vectors `R V_{e,n} R⁻¹` (the table INV (1.5)), the
proofs conjugate `Λ̂(t)` by `R⁻¹` and pair it with `V_e`, `V_f`, `X` of the rotated state (the same
numbers). `√3` then enters each closed form once, as `√3 · √3 = 3`, and the rest is `field_simp`,
`ring` in `(ε, Y, s, f₀, q, p)` with `Y' = (1 + ε²)/(ε² Y)`. Step 1 uses `ρ_R_conj` and
`poly_Rinv_conj_vertex`; step 3 uses `poly_hamiltonian_conj` for the relabelled Hamiltonians; step 4
uses `X₁₁ = (ρ₀ - ρ₁)/2`.

Also checked numerically, while the statements were written, against a literal model of the Lean
definitions: the update rules, the permutation of the `ρ`'s, the radius identities, the section
conditions at `F q`, to `10⁻¹⁴`, at two section points. The proofs do not depend on these checks.
**Which root of `R = 0` is `q_new`.** At those two points, and along `W^u` (numerically), `q_new`
is the larger root, but not in general: an independent review found the section point
`(ε, Y, f₀, p) = (0.3, 3, 0.01, 0.01)`, `q = -0.00666` (P1, P2, P4, `r > 0`; E fails), whose
image has `q_new = 2587.398`, the smaller root (the other is `2618.817`); off `𝒢*`, 118 of 696
sampled images took the smaller root, inside `𝒢*` all 72 the larger, and a point of `𝒢*` can
itself sit on either root. INV Theorem 1 removes the question: `q_new = Φ(s)/(Y - s)²`
(`arcQ_reinPoincare`).
-/

@[expose] public section

namespace SmoothedPolygons

open Set Filter Topology

/-- **The `e₂`-arc from `q` switches before it leaves the star domain**: `0 < t_sw(q) < T(q)`. -/
def SwitchesBeforeExit (q : iso_PhasePt) : Prop :=
  0 < reinSwitchTime q ∧ reinSwitchTime q < arcExitTime q

variable {q : iso_PhasePt}

/-! ### Frame computations (helpers) -/

private lemma n4f_sqrt3_mul_self : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)

private lemma n4f_sqrt3_ne : √3 ≠ 0 := by positivity

private lemma n4f_sqrt3_sq : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

private lemma n4f_sqrt3_pow4 : √3 ^ 4 = 9 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, n4f_sqrt3_sq]; norm_num

/-- `Ad_{R⁻¹}` in the frame (`S⁻¹ R S = [[0, -2], [1/2, 1]]`):
`R⁻¹ (h H + e E + f F) R = (e/2 - h) H + (e - 4h - 4f) E - (e/4) F`. -/
private lemma n4f_adRinv_ofFrame (h e f : ℝ) :
    R⁻¹ * ofFrame h e f * R = ofFrame (e / 2 - h) (e - 4 * h - 4 * f) (-e / 4) := by
  have h3 := n4f_sqrt3_ne
  rw [poly_R_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ofFrame, R, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring_nf <;> simp only [n4f_sqrt3_sq, n4f_sqrt3_pow4] <;> ring_nf

/-- `(3/2) J = √3 (-(1/2) H - 2E + (1/2) F)` in the frame. -/
private lemma n4f_three_halves_J :
    (3 / 2 : ℝ) • J = √3 • ofFrame (-(1 / 2)) (-2) (1 / 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ofFrame, J] <;> field_simp
  · ring
  · simp only [n4f_sqrt3_sq]

private lemma n4f_arcVe_ofFrame (h e f : ℝ) :
    arcVe (ofFrame h e f) = ofFrame e (-e ^ 2 / -h) (-h) := by
  rw [arcVe, frameE_ofFrame, (ρ_ofFrame h e f).1]

private lemma n4f_arcVf_ofFrame (h e f : ℝ) :
    arcVf (ofFrame h e f) = ofFrame f (-h) (-f ^ 2 / -h) := by
  rw [arcVf, frameF_ofFrame, (ρ_ofFrame h e f).1]

/-! ### Section points (helpers) -/

/-- On a section point `H(e₂) = H(e₃) + χ₂₃ = 0`. -/
private lemma n4f_phaseHam_one (hq : IsArcSectionPt q) : phaseHam q (vertex 1) = 0 := by
  obtain ⟨⟨⟨-, -, -, -, -, h6, h7⟩, -⟩, -⟩ := hq
  have := hamiltonian_sub_eq_switchingFn q.2.1 q.2.2 q.1 1 2
  rw [h7, h6] at this
  unfold phaseHam
  linarith

/-- Inside the star domain, `χ₂₁ = 0` along the `e₂`-arc iff `f(t/ε) = 0` (Theorem 1.3). -/
private lemma n4f_chi21_iff (hq : IsArcSectionPt q) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t < arcExitTime q) :
    switchingFn 1 0 (iso_vertexFlow 1 q t).2.2 (iso_vertexFlow 1 q t).1 = 0 ↔
      (arcParams q).f (t / arcEps q) = 0 := by
  have hH := n4f_phaseHam_one hq
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

/-! ### The costate along the arc in closed form (helpers; INV Theorem 1) -/

private lemma n4f_ofFrame_eq {h e f h' e' f' : ℝ} (hh : h = h') (he : e = e') (hf : f = f') :
    ofFrame h e f = ofFrame h' e' f' := by
  rw [hh, he, hf]

private lemma n4f_sqrt3_cancel6 (x y : ℝ) : -(√3 / (6 * x)) * (√3 * y) = -(y / (2 * x)) := by
  rw [show -(√3 / (6 * x)) * (√3 * y) = -(√3 * √3 * y / (6 * x)) by ring, n4f_sqrt3_mul_self]
  ring

private lemma n4f_sqrt3_cancel2 (x y : ℝ) : 2 / (√3 * x) * (√3 * y) = 2 * y / x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · field_simp

private lemma n4f_sqrt3_cancel3 (x z y : ℝ) :
    -(√3 / (3 * x * z)) * (√3 * y) = -(y / (x * z)) := by
  rw [show -(√3 / (3 * x * z)) * (√3 * y) = -(√3 * √3 * y / (3 * (x * z))) by ring,
    n4f_sqrt3_mul_self]
  ring

/-- `α/√3` of INV (1.4). -/
private noncomputable def n4f_al (a : ArcParams) : ℝ :=
  a.eps * (1 + a.eps ^ 2 * (a.Y + a.Y' * a.A - a.Y * a.B'))

/-- `β/√3` of INV (1.4). -/
private noncomputable def n4f_be (a : ArcParams) : ℝ := -(1 / 2) * a.eps ^ 3 * (a.Y' ^ 2 - a.B')

/-- `γ/√3` of INV (1.4). -/
private noncomputable def n4f_ga (a : ArcParams) : ℝ := 2 * a.eps ^ 3 * (a.Y ^ 2 - a.B)

private lemma n4f_lam (a : ArcParams) :
    a.lamAlpha = √3 * n4f_al a ∧ a.lamBeta = √3 * n4f_be a ∧ a.lamGamma = √3 * n4f_ga a := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [ArcParams.lamAlpha, ArcParams.lamBeta, ArcParams.lamGamma, n4f_al, n4f_be,
      n4f_ga] <;> ring

/-- The coefficients of INV (1.4) on a section point (INV Theorem 1 (i)). -/
private lemma n4f_coeffs (hq : IsArcSectionPt q) :
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
  rw [n4f_three_halves_J] at hΛ0
  have hX0 := ofFrame_frame hq.1.1.1
  rw [fh, fe, ff, ← arcParams_Y' hX] at hX0
  rw [hΛ0, ← hX0, iso_vfP_one_eq hX, n4f_arcVe_ofFrame, n4f_arcVf_ofFrame, (n4f_lam _).1,
    (n4f_lam _).2.1, (n4f_lam _).2.2]
  simp only [smul_ofFrame, ofFrame_sub, ofFrame_add, traceForm_ofFrame]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [n4f_al, n4f_be, n4f_ga, ArcParams.A, ArcParams.B, ArcParams.B', ArcParams.Y',
      arcParams] <;>
    field_simp <;> ring

/-- INV (1.4) on a section point (the content of `iso_vfΛ₁_one_eq_arcParams`). -/
private lemma n4f_vfΛ₁ (hq : IsArcSectionPt q) (t : ℝ) :
    iso_vfΛ₁ 1 q t =
      (arcParams q).lamAlpha • (iso_vfX 1 q t + iso_vfP 1 q) +
        ((arcParams q).lamBeta * Real.exp (2 * t / arcEps q)) • arcVe (iso_vfX 1 q t) +
        ((arcParams q).lamGamma * Real.exp (-2 * t / arcEps q)) • arcVf (iso_vfX 1 q t) := by
  obtain ⟨h1, h2, h3⟩ := n4f_coeffs hq
  rw [iso_vfΛ₁_one_eq hq.2 hq.1.1.2.1 t, h1, h2, h3]

/-- The frame of `Λ̂(t)/√3 = (Λ₁(t) + (3/2) J)/√3` along the arc, `s = e^{t/ε}`: `H`-component. -/
private noncomputable def n4f_Mh (a : ArcParams) (s : ℝ) : ℝ :=
  n4f_al a * (-a.eps - 1 / (2 * a.eps)) + n4f_be a * s ^ 2 * (-2 * a.eps * a.Y / s) +
    n4f_ga a / s ^ 2 * (a.eps * a.Y' * s / 2) - 1 / 2

/-- The frame of `Λ̂(t)/√3` along the arc: `E`-component. -/
private noncomputable def n4f_Me (a : ArcParams) (s : ℝ) : ℝ :=
  n4f_al a * (-2 * a.eps * a.Y / s) + n4f_be a * s ^ 2 * (-(-2 * a.eps * a.Y / s) ^ 2 / a.eps) +
    n4f_ga a / s ^ 2 * a.eps - 2

/-- The frame of `Λ̂(t)/√3` along the arc: `F`-component. -/
private noncomputable def n4f_Mf (a : ArcParams) (s : ℝ) : ℝ :=
  n4f_al a * (a.eps * a.Y' * s / 2) + n4f_be a * s ^ 2 * a.eps +
    n4f_ga a / s ^ 2 * (-(a.eps * a.Y' * s / 2) ^ 2 / a.eps) + 1 / 2

/-- The state and the reduced costate `Λ̂(t) = Λ₁(t) + (3/2) J` along the arc, in the frame. -/
private lemma n4f_frame_flow (hq : IsArcSectionPt q) (t : ℝ) :
    iso_vfX 1 q t = ofFrame (-(arcParams q).eps)
        (-2 * (arcParams q).eps * (arcParams q).Y / Real.exp (t / arcEps q))
        ((arcParams q).eps * (arcParams q).Y' * Real.exp (t / arcEps q) / 2) ∧
      iso_vfΛ₁ 1 q t + (3 / 2 : ℝ) • J =
        √3 • ofFrame (n4f_Mh (arcParams q) (Real.exp (t / arcEps q)))
          (n4f_Me (arcParams q) (Real.exp (t / arcEps q)))
          (n4f_Mf (arcParams q) (Real.exp (t / arcEps q))) := by
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
    refine n4f_ofFrame_eq rfl ?_ ?_ <;> simp only [arcParams] <;> ring
  refine ⟨hXt, ?_⟩
  rw [n4f_vfΛ₁ hq t, hXt, iso_vfP_one_eq hX, h2, h2', n4f_arcVe_ofFrame, n4f_arcVf_ofFrame,
    n4f_three_halves_J, (n4f_lam _).1, (n4f_lam _).2.1, (n4f_lam _).2.2]
  simp only [smul_ofFrame, ofFrame_add]
  refine n4f_ofFrame_eq ?_ ?_ ?_ <;> simp only [n4f_Mh, n4f_Me, n4f_Mf, arcParams] <;> ring

/-- The rotated point `Ad_{R⁻¹} q(t)` in the frame: `ε_n = ε (Y - s)/s`. -/
private lemma n4f_frame_rot (hq : IsArcSectionPt q) (t : ℝ) :
    (iso_adRinvPow 1 (iso_vertexFlow 1 q t)).1 =
        ofFrame (-((arcParams q).eps * ((arcParams q).Y - Real.exp (t / arcEps q)) /
            Real.exp (t / arcEps q)))
          (-2 * (arcParams q).eps * (arcParams q).Y / Real.exp (t / arcEps q) +
            4 * (arcParams q).eps -
            2 * (arcParams q).eps * (arcParams q).Y' * Real.exp (t / arcEps q))
          ((arcParams q).eps * (arcParams q).Y / (2 * Real.exp (t / arcEps q))) ∧
      (iso_adRinvPow 1 (iso_vertexFlow 1 q t)).2.1 + (3 / 2 : ℝ) • J =
        √3 • ofFrame
          (n4f_Me (arcParams q) (Real.exp (t / arcEps q)) / 2 -
            n4f_Mh (arcParams q) (Real.exp (t / arcEps q)))
          (n4f_Me (arcParams q) (Real.exp (t / arcEps q)) -
            4 * n4f_Mh (arcParams q) (Real.exp (t / arcEps q)) -
            4 * n4f_Mf (arcParams q) (Real.exp (t / arcEps q)))
          (-n4f_Me (arcParams q) (Real.exp (t / arcEps q)) / 4) := by
  obtain ⟨hXt, hΛt⟩ := n4f_frame_flow hq t
  have hs0 : Real.exp (t / arcEps q) ≠ 0 := (Real.exp_pos _).ne'
  have hJ : R⁻¹ * J * R = J := by simpa using poly_conj_pow_J 1
  simp only [iso_adRinvPow, iso_vertexFlow, pow_one]
  refine ⟨?_, ?_⟩
  · rw [hXt, n4f_adRinv_ofFrame]
    refine n4f_ofFrame_eq ?_ ?_ ?_ <;> field_simp <;> ring
  · rw [show R⁻¹ * iso_vfΛ₁ 1 q t * R + (3 / 2 : ℝ) • J =
        R⁻¹ * (iso_vfΛ₁ 1 q t + (3 / 2 : ℝ) • J) * R by rw [poly_conj_add, poly_conj_smul, hJ],
      hΛt, poly_conj_smul, n4f_adRinv_ofFrame]

/-- `s = e^{t/ε} < Y` before the exit time. -/
private lemma n4f_exp_lt (hq : IsArcSectionPt q) {t : ℝ} (ht : t < arcExitTime q) :
    Real.exp (t / arcEps q) < arcY q := by
  have hε := arcEps_pos hq.2
  have hY := one_lt_arcY hq.2
  rw [← Real.exp_log (by linarith : (0 : ℝ) < arcY q)]
  refine Real.exp_lt_exp.2 ?_
  rw [div_lt_iff₀ hε, mul_comm]
  exact ht

/-- `arcQ` of the rotated point (the content of `arcQ_adRinv_vertexFlow`). -/
private lemma n4f_arcQ_rot (hq : IsArcSectionPt q) {t : ℝ} (ht : t < arcExitTime q) :
    arcQ (iso_adRinvPow 1 (iso_vertexFlow 1 q t)) =
      (arcParams q).qNew (Real.exp (t / arcEps q)) := by
  have hε := (arcEps_pos hq.2).ne'
  have hY : arcY q ≠ 0 := (zero_lt_one.trans (one_lt_arcY hq.2)).ne'
  have hsY := (sub_pos.2 (n4f_exp_lt hq ht)).ne'
  have hs0 : Real.exp (t / arcEps q) ≠ 0 := (Real.exp_pos _).ne'
  obtain ⟨hXn, hΛn⟩ := n4f_frame_rot hq t
  rw [arcQ, show arcEps (iso_adRinvPow 1 (iso_vertexFlow 1 q t)) =
      ρ₁ (iso_adRinvPow 1 (iso_vertexFlow 1 q t)).1 from rfl, hΛn, hXn,
    ivf_traceForm_smul_left, n4f_sqrt3_cancel6, n4f_arcVe_ofFrame, (ρ_ofFrame _ _ _).1,
    traceForm_ofFrame]
  generalize Real.exp (t / arcEps q) = s at hsY hs0 ⊢
  simp only [n4f_Mh, n4f_Me, n4f_Mf, n4f_al, n4f_be, n4f_ga, ArcParams.qNew, ArcParams.Phi,
    ArcParams.A, ArcParams.B, ArcParams.B', ArcParams.Y', arcParams]
  field_simp
  ring

/-- `arcP` of the rotated point (the content of `arcP_adRinv_vertexFlow`). -/
private lemma n4f_arcP_rot (hq : IsArcSectionPt q) {t : ℝ} (ht : t < arcExitTime q) :
    arcP (iso_adRinvPow 1 (iso_vertexFlow 1 q t)) =
      (arcParams q).pNew (Real.exp (t / arcEps q)) := by
  have hε := (arcEps_pos hq.2).ne'
  have hY : arcY q ≠ 0 := (zero_lt_one.trans (one_lt_arcY hq.2)).ne'
  have hsY := (sub_pos.2 (n4f_exp_lt hq ht)).ne'
  have hs0 : Real.exp (t / arcEps q) ≠ 0 := (Real.exp_pos _).ne'
  obtain ⟨hXn, hΛn⟩ := n4f_frame_rot hq t
  rw [arcP, show arcEps (iso_adRinvPow 1 (iso_vertexFlow 1 q t)) =
      ρ₁ (iso_adRinvPow 1 (iso_vertexFlow 1 q t)).1 from rfl, hΛn, hXn,
    ivf_traceForm_smul_left, n4f_sqrt3_cancel2, n4f_arcVf_ofFrame, (ρ_ofFrame _ _ _).1,
    traceForm_ofFrame]
  generalize Real.exp (t / arcEps q) = s at hsY hs0 ⊢
  simp only [n4f_Mh, n4f_Me, n4f_Mf, n4f_al, n4f_be, n4f_ga, ArcParams.pNew,
    ArcParams.A, ArcParams.B, ArcParams.B', ArcParams.Y', arcParams]
  field_simp
  ring

/-- `f₀` of the rotated point, when it is a section point ((1.5) and the table INV (1.5)):
`s² Ψ(s)/(Y (Y - s)²)`. -/
private lemma n4f_arcF0_rot (hq : IsArcSectionPt q) {t : ℝ} (ht : t < arcExitTime q)
    (hn : IsArcSectionPt (iso_adRinvPow 1 (iso_vertexFlow 1 q t))) :
    arcF0 (iso_adRinvPow 1 (iso_vertexFlow 1 q t)) =
      (arcParams q).f0New (Real.exp (t / arcEps q)) := by
  have hε := (arcEps_pos hq.2).ne'
  have hY : arcY q ≠ 0 := (zero_lt_one.trans (one_lt_arcY hq.2)).ne'
  have hsY := (sub_pos.2 (n4f_exp_lt hq ht)).ne'
  have hs0 : Real.exp (t / arcEps q) ≠ 0 := (Real.exp_pos _).ne'
  obtain ⟨hXn, hΛn⟩ := n4f_frame_rot hq t
  have hY'n : arcY' (iso_adRinvPow 1 (iso_vertexFlow 1 q t)) =
      arcY q / (arcY q - Real.exp (t / arcEps q)) := by
    rw [arcY', hXn, (ρ_ofFrame _ _ _).2.2, (ρ_ofFrame _ _ _).1]
    simp only [arcParams]
    field_simp
    ring
  rw [arcF0_eq_reducedHam hn, reducedHam, show arcEps (iso_adRinvPow 1 (iso_vertexFlow 1 q t)) =
      ρ₁ (iso_adRinvPow 1 (iso_vertexFlow 1 q t)).1 from rfl, hY'n, hΛn, hXn,
    ivf_traceForm_smul_left, n4f_sqrt3_cancel3, (ρ_ofFrame _ _ _).1, traceForm_ofFrame]
  generalize Real.exp (t / arcEps q) = s at hsY hs0 ⊢
  simp only [n4f_Mh, n4f_Me, n4f_Mf, n4f_al, n4f_be, n4f_ga, ArcParams.f0New, ArcParams.Psi,
    ArcParams.A, ArcParams.B, ArcParams.B', ArcParams.Y', arcParams]
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
    · refine hglb.1 ⟨by positivity, (n4f_chi21_iff hq (by positivity) hτT).2 ?_⟩
      rwa [mul_div_cancel_left₀ _ hε.ne']
    · linarith
  have hglb' : IsGLB S' (reinSwitchTime q / arcEps q) := by
    refine ⟨fun τ hτ ↦ by rw [div_le_iff₀ hε, mul_comm]; exact hlow τ hτ, fun b hb ↦ ?_⟩
    have hb' : ∀ t ∈ S, t < arcExitTime q → arcEps q * b ≤ t := by
      rintro t ⟨ht0, hχ⟩ htT
      have := hb ⟨by positivity, (n4f_chi21_iff hq ht0.le htT).1 hχ⟩
      rwa [le_div_iff₀ hε, mul_comm] at this
    have hb₁ := hb' t₁ ht₁S ht₁lt
    have : arcEps q * b ≤ reinSwitchTime q := hglb.2 fun t ht ↦ by
      by_cases htT : t < arcExitTime q
      · exact hb' t ht htT
      · linarith
    rwa [le_div_iff₀ hε, mul_comm]
  have hS'ne : S'.Nonempty :=
    ⟨t₁ / arcEps q, by positivity [ht₁S.1], (n4f_chi21_iff hq ht₁S.1.le ht₁lt).1 ht₁S.2⟩
  have htau : (arcParams q).tauSw = reinSwitchTime q / arcEps q := hglb'.csInf_eq hS'ne
  refine ⟨by rw [htau]; field_simp, ?_⟩
  have hcont : Continuous (arcParams q).f :=
    continuous_iff_continuousAt.2 fun τ ↦ ((arcParams q).hasDerivAt_f τ).continuousAt
  have hcl : IsClosed {τ | (arcParams q).f τ = 0} := isClosed_eq hcont continuous_const
  have hmem := hglb'.mem_closure hS'ne
  rw [← htau] at hmem
  exact closure_minimal (fun τ (hτ : τ ∈ S') ↦ hτ.2) hcl hmem

/-- At the switch, `χ₂₁(q(t_sw)) = 0`. -/
private lemma n4f_chi21_tsw (hq : IsArcSectionPt q) (hs : SwitchesBeforeExit q) :
    switchingFn 1 0 (iso_vertexFlow 1 q (reinSwitchTime q)).2.2
      (iso_vertexFlow 1 q (reinSwitchTime q)).1 = 0 := by
  obtain ⟨hτ, hf⟩ := reinSwitchTime_eq_tauSw hq hs
  rw [n4f_chi21_iff hq hs.1.le hs.2, hτ, mul_div_cancel_left₀ _ (arcEps_pos hq.2).ne']
  exact hf

/-- **Theorem 2.1**: the image of a section point whose arc switches inside the star domain is a
section point. -/
theorem isArcSectionPt_reinPoincare (hq : IsArcSectionPt q) (hs : SwitchesBeforeExit q) :
    IsArcSectionPt (reinPoincare q) := by
  have hH := n4f_phaseHam_one hq
  have hχ := n4f_chi21_tsw hq hs
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

/-- **Theorem 2.1**: `(ρ₀, ρ₁, ρ₂)(F q) = (ρ₁(q), ρ₂(X(t_sw)), ρ₀(X(t_sw)))`. It holds for every
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
private lemma n4f_ρ₁_reinPoincare (hq : IsArcSectionPt q) (hs : SwitchesBeforeExit q) :
    ρ₁ (reinPoincare q).1 = arcEps q * (arcParams q).stepK := by
  have hε := arcEps_pos hq.2
  obtain ⟨hτ, -⟩ := reinSwitchTime_eq_tauSw hq hs
  rw [(ρ_reinPoincare hq).2.1, (ρ_iso_vfX_one hq.2 _).2.1, hτ, neg_div,
    mul_div_cancel_left₀ _ hε.ne']
  rfl

/-- **Theorem 2.1** (the Reinhardt–Poincaré map as an explicit map of the parameters). Let `q` be a
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
  have hsY : Real.exp (arcParams q).tauSw < arcY q := htτ ▸ n4f_exp_lt hq hs.2
  have hs0 : 0 < Real.exp (arcParams q).tauSw := Real.exp_pos _
  have hk : 0 < (arcParams q).stepK := by
    simp only [ArcParams.stepK, Real.exp_neg]
    rw [sub_pos, ← div_eq_mul_inv, one_lt_div hs0]
    exact hsY
  refine ⟨hk, ?_⟩
  have hρ₁ := n4f_ρ₁_reinPoincare hq hs
  have e1 : arcEps (reinPoincare q) = (arcParams q).stepK * (arcParams q).eps := by
    rw [show arcEps (reinPoincare q) = ρ₁ (reinPoincare q).1 from rfl, hρ₁, mul_comm]
    rfl
  have e2 : arcY (reinPoincare q) =
      1 + ((arcParams q).Y' * Real.exp (arcParams q).tauSw - 1) / (arcParams q).stepK := by
    rw [arcY, hρ₁, (ρ_reinPoincare hq).2.2, (ρ_iso_vfX_one hX _).2.2, htτ,
      ← arcParams_Y' hX, mul_div_mul_left _ _ hε.ne']
  have e3 : arcF0 (reinPoincare q) = (arcParams q).g (arcParams q).tauSw /
      ((arcParams q).Y * Real.exp (-(arcParams q).tauSw) - 1) ^ 2 := by
    have h := n4f_arcF0_rot hq hs.2 hn
    rw [htτ] at h
    rw [ArcParams.g_div_sq_eq_f0New _ (arcG0_eq_zero hq) hf hY (sub_pos.2 hsY).ne']
    exact h
  have e6 : arcP (reinPoincare q) = -(arcParams q).fDeriv (arcParams q).tauSw /
      ((arcParams q).Y * Real.exp (-(arcParams q).tauSw) - 1) ^ 2 := by
    have h := n4f_arcP_rot hq hs.2
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

/-! ### INV Theorem 1: the image in closed form -/

/-- **INV (1.4) on a section point** (INV Theorem 1 (i)): along the `e₂`-arc from a
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
`ε² Y Y' = 1 + ε²` and `√3² = 3` (`field_simp`, `ring`). Equivalently (INV §1):
`⟨Λ̂₀, V_e⟩ = -2√3 ε q`, `⟨Λ̂₀, V_f⟩ = (√3/2) ε p` (definitions of `arcQ`, `arcP`),
`⟨J, V_e⟩ = -(4ε/√3)(Y² - Y + 1)`, `⟨J, V_f⟩ = (ε/√3)(Y'² - Y' + 1)`. Also checked exactly with
sympy against the literal definitions. -/
theorem iso_vfΛ₁_one_eq_arcParams (hq : IsArcSectionPt q) (t : ℝ) :
    iso_vfΛ₁ 1 q t =
      (arcParams q).lamAlpha • (iso_vfX 1 q t + iso_vfP 1 q) +
        ((arcParams q).lamBeta * Real.exp (2 * t / arcEps q)) • arcVe (iso_vfX 1 q t) +
        ((arcParams q).lamGamma * Real.exp (-2 * t / arcEps q)) • arcVf (iso_vfX 1 q t) :=
  n4f_vfΛ₁ hq t

/-- **INV Theorem 1 for `q`, at every time of the arc**: for a section point `q` and `t < T`,
with `s = e^{t/ε}` (so `s < Y`), the rotated point `Ad_{R⁻¹} q(t)` has
`arcQ = Φ(s)/(Y - s)²` (`ArcParams.qNew`). At `t = t_sw` this is `q_new` (`arcQ_reinPoincare`).

Route (INV §1 (ii)–(iii)). Put `X_n = R⁻¹ X(t) R`, `Λ_n = R⁻¹ Λ₁(t) R`, `k_s = Y - s`.
1. `R⁻¹ J R = J` (`R = (1/2) I + (√3/2) J`), so `Λ_n + (3/2) J = R⁻¹ Λ̂(t) R`,
   `Λ̂(t) = Λ₁(t) + (3/2) J`; the trace form is conjugation invariant, so
   `⟨Λ_n + (3/2) J, V_e(X_n)⟩ = ⟨Λ̂(t), V_{e,n}⟩` with `V_{e,n} = R V_e(X_n) R⁻¹`.
2. `ε_n = ρ₁(X_n) = ρ₂(X(t)) = ε k_s/s` (`ρ_adRinv`, `ρ_iso_vfX_one`), nonzero for `t < T`.
3. The table INV (1.5) (the frame form of `R` is `S⁻¹ R S = [[0, -2], [1/2, 1]]`; twelve `2 × 2`
   products, `ofFrame_mul_sub`-style entrywise computation): the pairings of `V_{e,n}` with
   `X(t) + P`, `V_e(t)`, `V_f(t)`, `J` are `-2s/(ε² k_s)`, `-4s/(ε² k_s)`, `s/(ε² k_s)`,
   `-(4ε/(√3 s k_s))(Y'² s⁴ - 3Y' s³ + (YY' + 3) s² - 3Y s + Y²)`; those of `V_{f,n}` are `0`, `0`,
   `-s/(4ε² k_s)`, `(ε/(√3 s k_s))(s² - Y s + Y²)`; those of `R X_n R⁻¹ = X(t)` are `-1`,
   `-2Y/s`, `Y' s/2`, `-(2ε/(√3 s))(Y' s² - s + Y)`.
4. By `iso_vfΛ₁_one_eq_arcParams` (`u = 1/s`, so `u⁻² = s²`, `u² = s⁻²`):
   `⟨Λ̂(t), V_{e,n}⟩ = α(-2s/(ε² k_s)) + β s² (-4s/(ε² k_s)) + γ s⁻² (s/(ε² k_s))
   + (3/2) ⟨J, V_{e,n}⟩ = -(2√3 ε/(s k_s)) Φ(s)` (with `1/ε² = YY' - 1` and `Y B' = Y - Y A'`,
   `A' = 2 - Y' - p`), so `arcQ = -(√3/(6ε_n)) ⟨…⟩ = Φ(s)/k_s²`.
Also checked exactly with sympy against the literal definitions (matrix exponentials, `R`,
`arcVe`), symbolically in `ε, Y, u, Λ₁` and at exact points (with the table, `t` of both signs). -/
theorem arcQ_adRinv_vertexFlow (hq : IsArcSectionPt q) {t : ℝ} (ht : t < arcExitTime q) :
    arcQ (iso_adRinvPow 1 (iso_vertexFlow 1 q t)) =
      (arcParams q).qNew (Real.exp (t / arcEps q)) :=
  n4f_arcQ_rot hq ht

/-- **INV Theorem 1 for `p`, at every time of the arc**: for a section point `q` and `t < T`,
with `s = e^{t/ε}`, the rotated point `Ad_{R⁻¹} q(t)` has `arcP = π(s)/(Y - s)²`
(`ArcParams.pNew`, `π(s) = s² - Y s + B`). At `t = t_sw` this is `p_new` (with
`ArcParams.neg_fDeriv_div_sq_eq_pNew`, `-f'(τ_sw)/k²`), without Lemma 2.3.

Route: as `arcQ_adRinv_vertexFlow` with `V_{f,n}`: only `γ` and `J` pair with it,
`⟨Λ̂(t), V_{f,n}⟩ = γ s⁻² (-s/(4ε² k_s)) + (3/2)(ε/(√3 s k_s))(s² - Y s + Y²)
= (√3 ε/(2 s k_s)) π(s)` (`γ = 2√3 ε³ (Y² - B)`), and `arcP = (2/(√3 ε_n)) ⟨…⟩ = π(s)/k_s²`. -/
theorem arcP_adRinv_vertexFlow (hq : IsArcSectionPt q) {t : ℝ} (ht : t < arcExitTime q) :
    arcP (iso_adRinvPow 1 (iso_vertexFlow 1 q t)) =
      (arcParams q).pNew (Real.exp (t / arcEps q)) :=
  n4f_arcP_rot hq ht

/-- **INV Theorem 1, `q_new` in closed form**: for a section point whose arc switches inside the
star domain, `q_new = arcQ (F q) = Φ(s)/(Y - s)²` with `s = e^{τ_sw}` (`ArcParams.qNew`). This
settles which root of the quadric relation (2.1) at the new point `q_new` is; no root is chosen.

Route: `reinPoincare q = Ad_{R⁻¹} q(t_sw)` (definition), `t_sw = ε τ_sw < T`
(`reinSwitchTime_eq_tauSw`, `SwitchesBeforeExit`), and `arcQ_adRinv_vertexFlow` at `t = t_sw`
(`t_sw/ε = τ_sw`, `arcEps_pos`). -/
theorem arcQ_reinPoincare (hq : IsArcSectionPt q) (hs : SwitchesBeforeExit q) :
    arcQ (reinPoincare q) = (arcParams q).qNew (Real.exp (arcParams q).tauSw) := by
  obtain ⟨hτ, -⟩ := reinSwitchTime_eq_tauSw hq hs
  have h := arcQ_adRinv_vertexFlow hq hs.2
  rw [hτ, mul_div_cancel_left₀ _ (arcEps_pos hq.2).ne'] at h
  rw [reinPoincare, hτ]
  exact h

/-- **Theorem 2.1**, (2.2): `r(F q) = (ρ₁(q) - ρ₁(F q))/2 = ε (1 - k)/2`. -/
theorem radius_reinPoincare (hq : IsArcSectionPt q) (hs : SwitchesBeforeExit q) :
    (reinPoincare q).1 0 0 = (ρ₁ q.1 - ρ₁ (reinPoincare q).1) / 2 ∧
      (reinPoincare q).1 0 0 = arcEps q * (1 - (arcParams q).stepK) / 2 := by
  have hρ := ρ_reinPoincare hq
  have h00 : ∀ M : Mat2, M 0 0 = (ρ₀ M - ρ₁ M) / 2 := fun M ↦ by
    simp only [ρ₀, ρ₁]
    field_simp
    ring
  have hρ₁ := n4f_ρ₁_reinPoincare hq hs
  exact ⟨by rw [h00 (reinPoincare q).1, hρ.1], by
    rw [h00 (reinPoincare q).1, hρ.1, hρ₁, show ρ₁ q.1 = arcEps q from rfl]; ring⟩

/-- **Corollary 2.4** (telescoping): along an orbit of section points that switch inside the
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

/-- **Corollary 2.4**: the radii of the switching points along such an orbit sum to less than
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

/-- **Corollary 2.4**: an orbit that switches forever (with nonnegative radii) has `r_n → 0`: it
chatters into the divisor. -/
theorem tendsto_radius_reinPoincare_iterate
    (h : ∀ n, IsArcSectionPt (reinPoincare^[n] q) ∧ SwitchesBeforeExit (reinPoincare^[n] q))
    (hr : ∀ n, 0 ≤ (reinPoincare^[n + 1] q).1 0 0) :
    Tendsto (fun n ↦ (reinPoincare^[n] q).1 0 0) atTop (𝓝 0) := by
  have hsum : ∀ N, ∑ n ∈ Finset.range N, (reinPoincare^[n + 1] q).1 0 0 ≤ ρ₁ q.1 / 2 :=
    fun N ↦ (sum_radius_reinPoincare_iterate_lt (h 0).1 N fun n _ ↦ h n).le
  exact (tendsto_add_atTop_iff_nat 1).mp (summable_of_sum_range_le hr hsum).tendsto_atTop_zero

end SmoothedPolygons
