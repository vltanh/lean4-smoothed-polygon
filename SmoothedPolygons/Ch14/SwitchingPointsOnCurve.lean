module

public import SmoothedPolygons.Ch14.NoReturnTools
public import SmoothedPolygons.Ch16.ClusterPoint

/-!
# Chapter 14: the switching points lie on the curve once they converge (Theorem 16.4.1, (i) ⇒ (ii))

"All switches must be on the unstable curve, which meets that exceptional divisor at a single point
`(0, x_out)`" (proof of Theorem 14.4.1, Hales–Vajjha, *Packings of Smoothed Polygons*,
TeX 12004–12005). This is the second part of Theorem 16.4.1, time reversed (the book cites
neither; REPORT.md, E88). Theorem 14.4.1 has the first part, the convergence of the angular
components to `q_out` modulo `V_T`, as a hypothesis ("emanates from the fixed point
`(r, x̃) = (0, x_out)`"), so its proof needs the second part from the first alone, without the
numerical facts of Theorem 16.1.1. Both forms are proved in
`SmoothedPolygons/Ch16/ClusterPoint.lean` (imported here), where the second parts of Theorem 16.4.1
and of its time reversal are derived from them:

* `IsChatteringArcInto.eventually_mem_localUnstableSet`: along a chattering arc into the singular
  locus whose switching points converge to `q_in` modulo `V_T`, eventually each switching point,
  rotated onto the section `χ₂₃ = 0`, is `lieChartIn p` with `p` on the local unstable curve of `e`
  (the stable curve `W^s(q_in)` of the Reinhardt–Poincaré map `e⁻¹` in the mirrored chart); this is
  step 5 of the proof of `theorem16_4_1_of_clusterSetForwardInvariant`, which uses the first part
  only through the convergence;
* `IsChatteringArcOutOf.eventually_mem_localUnstableSet`: its time reversal, the form used by
  Theorem 14.4.1 (`SmoothedPolygons/Ch14/NoReturnProof.lean`): along a chattering arc out of the
  singular locus whose switching points converge backward to `q_out`, eventually (backward in time)
  each switching point, rotated, is `lieChart p` with `p` on `W^u_loc(e, U)`, `r > 0`
  (`IsChatteringArcOutOf.reverse`, `switchAng_reverse`, `TendstoModVT.tau`, and the rotation back
  `Ad_{R⁻ᵏ} ∘ τ = τ ∘ Ad_{R^{-2k}}`); `theorem16_4_1_reverse` derives its second part from it.

This module declares nothing; it gathers the two lemmas and the reversal tools for the proof of
Theorem 14.4.1.
-/
