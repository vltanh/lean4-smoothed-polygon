module

public import SmoothedPolygons.Ch16.RescaledLimits
public import SmoothedPolygons.Ch16.GlobalBasin

/-!
# Chapter 16: the cluster set of the switching points is invariant (§16.4.2, part 3; N5)

§16.4.2 of Hales–Vajjha, *Packings of Smoothed Polygons* ("Reinhardt switching functions as cubic
polynomials", TeX 12887–12987), and the gap N5 / G16.8 of the plan: the cluster set of the
switching points of a chattering arc is forward invariant under the Fuller–Poincaré map.

## The book's argument, and why it falls short

The book (TeX 12888–12987): (1) the rescaled Reinhardt switching functions `χ(s, r, ξ)/r³` extend
analytically across `r = 0`, where they are the Fuller cubics, so for small `r` their third
`s`-derivative is nonzero and they "behave qualitatively like a monic cubic polynomial";
(2) Weierstrass preparation at each root of the Fuller cubic gives a monic cubic `χ_W` with
coefficients analytic in `(r, ξ)` that "captures all real roots of `χ`"; (3) "All of these defining
conditions [of the cells `𝒞_k`, the parts `𝒟_i`, `𝒟_{1,ij}`] can be carried over to the Reinhardt
dynamical system", giving Reinhardt cells `𝒞_k^R` and parts `𝒟_i^R` near the divisor and "a
continuous extension `F_i` of the Reinhardt–Poincaré map from the interior of `𝒟_i^R` to all of
`𝒟_i^R`", restricting to the Fuller parts at `r = 0`; (4) the proof of Theorem 16.4.1 runs the
descent of Table 16.1 through these parts.

Step (3) is asserted without proof (G16.8): it needs the Fuller parts `𝒟_i` with continuous
branches on closed parts (Proposition 15.3.2, itself only a named proposition, read off Figures
15.2–15.3, and not used by the formal Theorem 16.1.1), and uniform control of the Reinhardt
switching functions near the whole divisor, including the faces where `t_sw → 0`, the 2-cells and
the double-root loci; "`χ_W` … defined for all `s`" also needs a bound on the rescaled switching
times (G16.11). Step (4) ignores the diagonal entries of Table 16.1 (G16.10). The zero count of
step (1) bounds the zeros of one constant-control piece, not the number of pieces of a trajectory
(the third derivative of `χ_ij` changes sign with the control).

## The repair (along the book's lines): relaxed limits

The descent through Reinhardt parts serves only to make the image `F_i(q)` of a cluster point a
cluster point. This is the one property used (`ClusterSetForwardInvariant`, N5): **the cluster set
`Ω = switchClusterSet` is mapped into itself by the honest Fuller–Poincaré map `F_ang =
poincareAngZero`** (with `Ω ⊆ Ξ_{𝒲,0}/V_T`, `mapClusterPt_switchAng_mem_sectionZero`). With it,
Theorem 16.4.1 follows from Theorem 16.1.1 itself (the book's "Repeating the argument of Theorem
16.1.1", TeX 13038–13040) and the hyperbolic box at `q_out`
(`SmoothedPolygons/Ch16/ClusterPoint.lean`). No Reinhardt cells, parts, branch maps or Weierstrass
polynomials are needed, and the three named numerical facts of Layer 5 suffice.

The proof of N5, for a cluster point `ξ ∈ sectionZero` of the `ξ_n` along `n_k`, with
`u₀ = firstControl ξ` and `T = firstSwitchTime ξ`:
1. (`exists_window`) The rescaled windows `[0, T + δ]` after `τ_{n_k}` stay before `b` for some
   `δ > 0`: otherwise the rescaled arcs, uniformly Lipschitz (equicontinuity), would reach `0`
   (`ẑ(q(b)) = 0`, the singular point) at rescaled times `σ_k → σ* ≤ T + δ`, and their limit, a
   relaxed Fuller extremal from `ξ` (`exists_tendsto_rescaledArc` on `[0, σ* - η]`), would vanish at
   `σ*`; it is `flow · ξ u₀` on `[0, T]` (`eq_flow_of_maxCondition_UT`), nonzero there
   (`flow_firstControl_ne_zero`), and Lipschitz, so nonzero on `[T, T + δ]` for small `δ`.
2. (`exists_tendsto_rescaledArc`) On `[0, T + δ]` a subsequence converges to a relaxed Fuller
   extremal `(y, w)` from `ξ`; `y = flow · ξ u₀` and `w = u₀` a.e. on `[0, T]`
   (`eq_flow_of_maxCondition_UT`), and `w ≠ u₀` on a set of positive measure in `(T, T + δ']` for
   every `δ' ≤ δ` (`firstControl_beaten_UT`).
3. (`exists_tendsto_switchAng_poincare`) A Reinhardt switch at rescaled time `→ T`: for small
   `ε > 0`, `u₀` is the strict maximizer of `H_F` at `y(s)`, `s ∈ [T - ε, T - ε/2]` (the switching
   functions are nonzero cubics, with finitely many zeros), hence of the rescaled Reinhardt
   Hamiltonian at the rescaled arc for large `k` (`tendstoUniformlyOn_rescaledHam`), so the
   Reinhardt control is `u₀` there; if there were no Reinhardt switch in rescaled time
   `(T - ε, T + δ')`, the
   control would be `u₀` on all of it (it is constant between switches), and the integrated controls
   would converge to `∫ u₀` there, against step 2. So some switching time `τ_{m_k}` has rescaled
   time in `(T - ε, T + δ')`, and `ξ_{m_k} = ang (rescaledArc n_k ((τ_{m_k} - τ_{n_k})/ρ_{n_k}))`
   tends, as `ε, δ' → 0` (diagonal), to `ang (y(T)) = ang (poincare ξ)`.
4. The class of `ang (poincare ξ)` is `F_ang([ξ])` (`ang_poincare_ang`, `poincareAng_orbitRel`), and
   `ang (poincare ξ) ∈ sectionZero` (`poincare_mem_walls`, `hamMax_poincare`); so `F_ang(Ω) ⊆ Ω`.
Tangencies of the Fuller trajectory (where a Reinhardt switching function dips below zero for a
short rescaled time) only add cluster points (the tangency points, whose image is again
`F(ξ)`); they do not affect the argument.

## Module split and sizes

* `SmoothedPolygons/Ch16/RescaledDynamics.lean`: the uniform convergence of the rescaled field and
  Hamiltonians, and the cluster points in the section (500–900 lines);
* `SmoothedPolygons/Ch16/RelaxedFuller.lean`: `eq_flow_of_maxCondition_UT`,
  `firstControl_beaten_UT` (300–600 lines);
* `SmoothedPolygons/Ch16/RescaledLimits.lean`: the integral equation and the relaxed limits
  (Arzelà–Ascoli; 700–1,000 lines);
* this file: the window, the forced switch and N5 (500–900 lines).
Total for N5: 2,000–3,400 lines.

`ClusterSetForwardInvariant` is a named proposition so that Theorem 16.4.1 can also be used
conditionally on it (`theorem16_4_1_of_clusterSetForwardInvariant`).
-/

@[expose] public section

namespace SmoothedPolygons

open Complex Set Filter Topology MeasureTheory
open TriFuller

/-- **The rescaled windows stay before the singular time** (step 1 of the proof of N5; the
equicontinuity argument): along a chattering arc into `b`, if `ξ_{n_k} → ξ ∈ sectionZero`, then
for some `δ > 0` the windows `[τ_{n_k}, τ_{n_k} + (t_sw(ξ) + δ) ρ_{n_k}]` lie before `b` for all
large `k`. (The rescaled arcs reach `0` at the rescaled time of `b`; their relaxed limit is
`flow · ξ (firstControl ξ)` on `[0, t_sw(ξ)]`, which does not vanish, `flow_firstControl_ne_zero`.)
-/
theorem exists_window {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {τ : ℕ → ℝ}
    (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {ξ : Fin 3 → ℂ} (hξ0 : ξ ∈ sectionZero)
    (hξ : Tendsto (fun k ↦ switchAng X Λ₁ ΛR τ (φ k)) atTop (𝓝 ξ)) :
    ∃ δ > 0, ∀ᶠ k in atTop,
      τ (φ k) + (firstSwitchTime ξ + δ) * switchRadius X Λ₁ ΛR τ (φ k) < b := by
  sorry

/-- **A Reinhardt switch at rescaled time `→ t_sw`** (steps 2–3 of the proof of N5): along a
chattering arc into `b`, if `ξ_{n_k} → ξ ∈ sectionZero`, then there are switching indices
`m_k → ∞` whose angular components tend to `ang (F ξ)`, the angular component of the
Fuller–Poincaré image of `ξ` (relaxed limits, `exists_tendsto_rescaledArc`;
`eq_flow_of_maxCondition_UT`; `firstControl_beaten_UT`; the strict optimality of the first control
just before `t_sw(ξ)`, transferred by `tendstoUniformlyOn_rescaledHam`). -/
theorem exists_tendsto_switchAng_poincare {a b : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    {τ : ℕ → ℝ} (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {ξ : Fin 3 → ℂ} (hξ0 : ξ ∈ sectionZero)
    (hξ : Tendsto (fun k ↦ switchAng X Λ₁ ΛR τ (φ k)) atTop (𝓝 ξ)) :
    ∃ m : ℕ → ℕ, Tendsto m atTop atTop ∧
      Tendsto (fun k ↦ switchAng X Λ₁ ΛR τ (m k)) atTop (𝓝 (ang (poincare ξ))) := by
  sorry

/-- **N5: the cluster set is forward invariant under the Fuller–Poincaré map** (the precise form of
the book's §16.4.2 claim "a continuous extension `F_i` of the Reinhardt–Poincaré map … The
restriction of each `𝒟_i^R` to the exceptional divisor `r = 0` is the previously defined
Fuller-system part `𝒟_i`", TeX 12970–12976, as the proof of Theorem 16.4.1 uses it, TeX
13036–13048): for every chattering arc into the singular locus, the set of cluster classes of its
switching points is mapped into itself by `F_ang`. -/
def ClusterSetForwardInvariant : Prop :=
  ∀ (a b : ℝ) (u : ℝ → Fin 3 → ℝ) (g X Λ₁ ΛR : ℝ → Mat2) (τ : ℕ → ℝ),
    IsChatteringArcInto a b u g X Λ₁ ΛR τ →
      MapsTo poincareAngZero (switchClusterSet (switchAng X Λ₁ ΛR τ))
        (switchClusterSet (switchAng X Λ₁ ΛR τ))

/-- **N5 holds** (step 4 of the plan in the module docstring, from
`exists_tendsto_switchAng_poincare`: a cluster point `ξ` gives the cluster point `ang (F ξ)`, in
the section, of class `F_ang([ξ])`). -/
theorem clusterSetForwardInvariant : ClusterSetForwardInvariant := by
  sorry

end SmoothedPolygons
