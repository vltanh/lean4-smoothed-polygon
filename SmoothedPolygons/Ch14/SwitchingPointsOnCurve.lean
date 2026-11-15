module

public import SmoothedPolygons.Ch14.NoReturnTools
public import SmoothedPolygons.Ch16.ClusterPoint

/-!
# Chapter 14: the switching points lie on the curve once they converge (Theorem 16.4.1, (i) ⇒ (ii))

"All switches must be on the unstable curve, which meets that exceptional divisor at a single point
`(0, x_out)`" (proof of Theorem 14.4.1, Hales–Vajjha, *Packings of Smoothed Polygons*,
TeX 12004–12005). This is the second part of Theorem 16.4.1, time reversed (the book cites
neither; REPORT.md, E88): `theorem16_4_1_reverse` (`SmoothedPolygons/Ch16/ClusterPoint.lean`)
gives it, but from the three named numerical facts of Layer 5, which it needs only for the first
part (the convergence of the angular components to `q_out` modulo `V_T`). Theorem 14.4.1 has that
convergence as a hypothesis ("emanates from the fixed point `(r, x̃) = (0, x_out)`"), so its proof
needs the second part from the first alone, without the numerical facts:

* `IsChatteringArcInto.eventually_mem_localUnstableSet`: along a chattering arc into the singular
  locus whose switching points converge to `q_in` modulo `V_T`, eventually each switching point,
  rotated onto the section `χ₂₃ = 0`, is `lieChartIn p` with `p` on the local unstable curve of `e`
  (the stable curve `W^s(q_in)` of the Reinhardt–Poincaré map `e⁻¹` in the mirrored chart);
* `IsChatteringArcOutOf.eventually_mem_localUnstableSet`: its time reversal, the form used by
  Theorem 14.4.1: along a chattering arc out of the singular locus whose switching points converge
  backward to `q_out`, eventually (backward in time) each switching point, rotated, is `lieChart p`
  with `p` on `W^u_loc(e, U)`, `r > 0`.

## Proofs (planned)

The first: step 5 of the proof of `theorem16_4_1_of_clusterSetForwardInvariant` verbatim (from
"`(2)` the stable curve" on), with `hmod` the hypothesis `hconv`: that block uses the numerical
facts only through `hmod`. Its private helpers (`l6h_tendsto_chart_in` and what it needs:
`l6h_rot_point`, `l6h_tendsto_radius`, `l6h_switch_section`, `l6h_qOut_facts`,
`l6h_eventually_ham0_neg`, `l6h_chartG` and its lemmas, `l6h_rep_unique`,
`l6h_phaseHam_adRinvPow`, `l6h_fullerCoords_adRinvPow`, `l6h_isBlowupPhasePt_adRinvPow`,
`l6h_lieChartIn_inj`) are private in ClusterPoint.lean. The cheapest route: move that block of
ClusterPoint.lean into a public lemma there with exactly the statement below (a refactor, no
statement of the file changes; `theorem16_4_1_of_clusterSetForwardInvariant` then calls it), and
prove the first lemma here by it; otherwise copy the helpers (about 500 lines). The second: as
`theorem16_4_1_reverse`: `IsChatteringArcOutOf.reverse` is a chattering arc into the singular locus
whose angular components are `τ` of the original ones (`switchAng_reverse`), so they converge to
`τ (ang q_out) = ang (τ q_out)` (`TendstoModVT.tau`, `tau_ang`); apply the first lemma and rotate
back (`Ad_{R⁻ᵏ} ∘ τ = τ ∘ Ad_{R^{-2k}}`, `reinTau_spec`, `lieChartIn = τ ∘ lieChart`), as in the
proof of `theorem16_4_1_reverse` (about 80 lines).
Size: 150–250 lines with the refactor, 600–700 without.
-/

@[expose] public section

namespace SmoothedPolygons

open Set Filter Topology
open TriFuller

/-- **Theorem 16.4.1, second part from the first**: along a chattering arc into the singular locus
whose switching points converge to `q_in` modulo `V_T`, for every analytic extension `e` of the
Reinhardt–Poincaré map at `q_out` and every neighborhood `U` of the fixed point, eventually each
switching point, rotated onto the section `χ₂₃ = 0`, is `lieChartIn p` with `p` on the local
unstable set of `e` in `U` (the stable curve `W^s(q_in)` of `e⁻¹` in the mirrored chart) and
`r > 0`. No numerical fact is used. -/
theorem IsChatteringArcInto.eventually_mem_localUnstableSet {a b : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X Λ₁ ΛR : ℝ → Mat2} {τ : ℕ → ℝ} (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ)
    (hconv : TendstoModVT (switchAng X Λ₁ ΛR τ) (ang (tau qOutCart)))
    {e : OpenPartialHomeomorph (ℝ × (Fin 3 → ℝ)) (ℝ × (Fin 3 → ℝ))}
    (he : IsReinhardtPoincareExtension e) {U : Set (ℝ × (Fin 3 → ℝ))} (hU : U ∈ 𝓝 chartPtOut) :
    ∀ᶠ n in atTop, ∃ k : ℕ, ∃ p ∈ Function.localUnstableSet e chartPtOut U, 0 < p.1 ∧
      iso_adRinvPow k (phaseAt X Λ₁ ΛR (τ n)) = lieChartIn p := by
  sorry

/-- **All switches are on the unstable curve** (proof of Theorem 14.4.1, TeX 12004–12005; the
second part of Theorem 16.4.1, time reversed, from the first): along a chattering arc out of the
singular locus whose switching points converge backward to `q_out` modulo `V_T`, for every
analytic extension `e` and every neighborhood `U` of the fixed point, eventually (`τ n ↓ a`) each
switching point, rotated onto the section `χ₂₃ = 0`, is `lieChart p` with `p` on the local unstable
curve `W^u_loc(e, U)` and `r > 0`. No numerical fact is used. -/
theorem IsChatteringArcOutOf.eventually_mem_localUnstableSet {a b : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X Λ₁ ΛR : ℝ → Mat2} {τ : ℕ → ℝ} (h : IsChatteringArcOutOf a b u g X Λ₁ ΛR τ)
    (hconv : TendstoModVT (switchAng X Λ₁ ΛR τ) (ang qOutCart))
    {e : OpenPartialHomeomorph (ℝ × (Fin 3 → ℝ)) (ℝ × (Fin 3 → ℝ))}
    (he : IsReinhardtPoincareExtension e) {U : Set (ℝ × (Fin 3 → ℝ))} (hU : U ∈ 𝓝 chartPtOut) :
    ∀ᶠ n in atTop, ∃ k : ℕ, ∃ p ∈ Function.localUnstableSet e chartPtOut U, 0 < p.1 ∧
      iso_adRinvPow k (phaseAt X Λ₁ ΛR (τ n)) = lieChart p := by
  sorry

end SmoothedPolygons
