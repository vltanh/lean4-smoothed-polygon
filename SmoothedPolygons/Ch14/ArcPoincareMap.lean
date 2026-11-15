module

public import SmoothedPolygons.Ch14.ArcRelation
public import SmoothedPolygons.Ch14.VertexPoissonBracket
import SmoothedPolygons.Ch7.Isolated.VertexFlow
import SmoothedPolygons.Ch7.Isolated.Return

/-!
# Chapter 14, N4: the Reinhardt–Poincaré map in closed form (Theorem 2.1, Corollary 2.4)

`notes/n4/proof.md` §2.2: if the `e₂`-arc from a section point `q` switches inside the star
domain, its image `F(q) = reinPoincare q = Ad_{R⁻¹} q(t_sw)` is a section point whose arc
parameters are explicit functions of those of `q` and of the switching root `τ_sw` of the
four-term exponential sum `f` (`ArcParams.step`): no ODE, one root per step. The radii telescope,
`r(F q) = (ρ₁(q) - ρ₁(F q))/2`, so along any orbit that keeps switching they sum to less than
`ρ₁(q₀)/2`. Part of the reduction of N4 to (INV) (`ArcRegionInvariant`).

**Departure from the paper.** The book computes the unstable curve numerically (Figure 14.2,
TeX 11951–11991); the formalization proves N4 from (INV) by the exact structure of the arcs (see
`SmoothedPolygons/Ch14/ArcParams.lean`).

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
* **Corollary 2.4**: `sum_radius_reinPoincare_iterate` (the telescoping identity),
  `sum_radius_reinPoincare_iterate_lt` (`Σ_{n ≥ 1} r_n < ρ₁(q₀)/2`),
  `tendsto_radius_reinPoincare_iterate` (an orbit that switches forever with `r_n ≥ 0` has
  `r_n → 0`: it chatters into the divisor).

## Proofs (the route, proof.md Theorem 2.1)

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
5. `f₀,new`: by step 1 `N₂₁^new = N₁₃(t_sw)`; at a zero of `N₂₁`, `χ₁₃ = χ₂₃`, so
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
7. `q_new = arcQ (F q)` by definition of `step`; it is a root of `R = 0` by `arcParams_rel` at the
   section point `F q`.
8. Corollary 2.4: induction on `N` with step 4 (`Finset.sum_range_succ`); the bound from
   `ρ₁(F^N q) > 0` (a section point is a star state); the limit: the partial sums of the
   nonnegative `r_n` are bounded, so the series is summable and `r_n → 0`
   (`Summable.tendsto_atTop_zero`).

Checked against the literal model (`notes/n4f/check2.py`: the update rules, the permutation of the
`ρ`'s, the radius identities, the section conditions at `F q`, to `10⁻¹⁴`, at two section points;
`q_new` is the larger root of `R = 0` there, as the research found along `W^u`).
-/

@[expose] public section

namespace SmoothedPolygons

open Set Filter Topology

/-- **The `e₂`-arc from `q` switches before it leaves the star domain**: `0 < t_sw(q) < T(q)`. -/
def SwitchesBeforeExit (q : iso_PhasePt) : Prop :=
  0 < reinSwitchTime q ∧ reinSwitchTime q < arcExitTime q

variable {q : iso_PhasePt}

/-- `Ad_{R⁻¹}` permutes the star functions: `(ρ₀, ρ₁, ρ₂)(R⁻¹ X R) = (ρ₁, ρ₂, ρ₀)(X)` for
traceless `X`. -/
theorem ρ_adRinv (hX : q.1.trace = 0) :
    ρ₀ (iso_adRinvPow 1 q).1 = ρ₁ q.1 ∧ ρ₁ (iso_adRinvPow 1 q).1 = ρ₂ q.1 ∧
      ρ₂ (iso_adRinvPow 1 q).1 = ρ₀ q.1 := by
  sorry

/-- **The relabelling** of the cleared numerators under `Ad_{R⁻¹}`:
`N_{i+1, j+1}(Ad_{R⁻¹} q) = N_{ij}(q)` (`R⁻¹ Z_{e_m} R = Z_{e_{m+1}}`). -/
theorem switchingNum_adRinv (i j : Fin 3) (q : iso_PhasePt) :
    switchingNum (i + 1) (j + 1) (iso_adRinvPow 1 q) = switchingNum i j q := by
  sorry

/-- The switching time is `ε τ_sw`, and `τ_sw` is a zero of `f`. -/
theorem reinSwitchTime_eq_tauSw (hq : IsArcSectionPt q) (hs : SwitchesBeforeExit q) :
    reinSwitchTime q = arcEps q * (arcParams q).tauSw ∧
      (arcParams q).f (arcParams q).tauSw = 0 := by
  sorry

/-- **Theorem 2.1**: the image of a section point whose arc switches inside the star domain is a
section point. -/
theorem isArcSectionPt_reinPoincare (hq : IsArcSectionPt q) (hs : SwitchesBeforeExit q) :
    IsArcSectionPt (reinPoincare q) := by
  sorry

/-- **Theorem 2.1**: `(ρ₀, ρ₁, ρ₂)(F q) = (ρ₁(q), ρ₂(X(t_sw)), ρ₀(X(t_sw)))`. -/
theorem ρ_reinPoincare (hq : IsArcSectionPt q) (hs : SwitchesBeforeExit q) :
    ρ₀ (reinPoincare q).1 = ρ₁ q.1 ∧
      ρ₁ (reinPoincare q).1 = ρ₂ (iso_vfX 1 q (reinSwitchTime q)) ∧
      ρ₂ (reinPoincare q).1 = ρ₀ (iso_vfX 1 q (reinSwitchTime q)) := by
  sorry

/-- **Theorem 2.1** (the Reinhardt–Poincaré map as an explicit map of the parameters). Let `q` be a
section point whose `e₂`-arc switches inside the star domain. Then `k = Y e^{-τ_sw} - 1 > 0` and
`arcParams (F q) = (arcParams q).step q_new` with `q_new = arcQ (F q)`: `ε_new = k ε`,
`Y_new = 1 + (Y' e^{τ_sw} - 1)/k`, `f₀,new = g(τ_sw)/k²`, `g₀,new = 0`, `p_new = -f'(τ_sw)/k²`;
`q_new` is a root of the quadric relation at the new point (`arcParams_rel`). -/
theorem arcParams_reinPoincare (hq : IsArcSectionPt q) (hs : SwitchesBeforeExit q) :
    0 < (arcParams q).stepK ∧
      arcParams (reinPoincare q) = (arcParams q).step (arcQ (reinPoincare q)) := by
  sorry

/-- **Theorem 2.1**, (2.2): `r(F q) = (ρ₁(q) - ρ₁(F q))/2 = ε (1 - k)/2`. -/
theorem radius_reinPoincare (hq : IsArcSectionPt q) (hs : SwitchesBeforeExit q) :
    (reinPoincare q).1 0 0 = (ρ₁ q.1 - ρ₁ (reinPoincare q).1) / 2 ∧
      (reinPoincare q).1 0 0 = arcEps q * (1 - (arcParams q).stepK) / 2 := by
  sorry

/-- **Corollary 2.4** (telescoping): along an orbit of section points that switch inside the
star domain, `Σ_{n=1}^{N} r(F^n q) = (ρ₁(q) - ρ₁(F^N q))/2`. -/
theorem sum_radius_reinPoincare_iterate (q : iso_PhasePt) (N : ℕ)
    (h : ∀ n < N, IsArcSectionPt (reinPoincare^[n] q) ∧ SwitchesBeforeExit (reinPoincare^[n] q)) :
    ∑ n ∈ Finset.range N, (reinPoincare^[n + 1] q).1 0 0 =
      (ρ₁ q.1 - ρ₁ (reinPoincare^[N] q).1) / 2 := by
  sorry

/-- **Corollary 2.4**: the radii of the switching points along such an orbit sum to less than
`ρ₁(q₀)/2`. -/
theorem sum_radius_reinPoincare_iterate_lt (hq : IsArcSectionPt q) (N : ℕ)
    (h : ∀ n < N, IsArcSectionPt (reinPoincare^[n] q) ∧ SwitchesBeforeExit (reinPoincare^[n] q)) :
    ∑ n ∈ Finset.range N, (reinPoincare^[n + 1] q).1 0 0 < ρ₁ q.1 / 2 := by
  sorry

/-- **Corollary 2.4**: an orbit that switches forever (with nonnegative radii) has `r_n → 0`: it
chatters into the divisor. -/
theorem tendsto_radius_reinPoincare_iterate
    (h : ∀ n, IsArcSectionPt (reinPoincare^[n] q) ∧ SwitchesBeforeExit (reinPoincare^[n] q))
    (hr : ∀ n, 0 ≤ (reinPoincare^[n + 1] q).1 0 0) :
    Tendsto (fun n ↦ (reinPoincare^[n] q).1 0 0) atTop (𝓝 0) := by
  sorry

end SmoothedPolygons
