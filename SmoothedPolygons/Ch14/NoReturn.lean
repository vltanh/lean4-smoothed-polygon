module

public import SmoothedPolygons.Ch16.ClusterCoordinates

/-!
# Chapter 14: Theorem 14.4.1 (no return), as a named proposition

Theorem 14.4.1 (`thm:no-return`) of Hales–Vajjha, *Packings of Smoothed Polygons* (TeX
11995–12013): "A trajectory of the Reinhardt system that emanates from the fixed point
`(r, x̃) = (0, x_out)` on the exceptional divisor does not return to the exceptional divisor. A
trajectory of the Reinhardt system that tends to the fixed point `(r, x̃) = (0, x_in)` on the
exceptional divisor did not emanate at an earlier time from the exceptional divisor."

It is stated here as the named proposition `Theorem14_4_1`, a hypothesis of the final assembly of
Theorem 16.3.1 (`SmoothedPolygons/Ch16/NoChattering.lean`). Layer 7 proves it from the numerical
fact N4 (`theorem14_4_1`, `SmoothedPolygons/Ch14/NoReturnProof.lean`; N4 is the named hypothesis
`UnstableCurveLeavesStarDomain`, `SmoothedPolygons/Ch14/UnstableCurve.lean`). The book's proof
rests on a figure: "All switches must be on the unstable curve, which meets that exceptional
divisor at a single point `(0, x_out)`. Any trajectory that returns to the singular locus must
chatter … This would require the unstable curve to contain a sequence of forward iterates of points
tending to the exceptional divisor. This does not happen, because the unstable curve hits the
boundary of the star domain" (the numerical computation of Figure 14.2, TeX 11951–11991,
uncertified by the authors' own statement; REPORT.md, E88).

## The formal statement

A trajectory "emanating from `(0, x_out)`" is a chattering arc out of the singular locus
(`IsChatteringArcOutOf`, normalized by `λ_cost = -1`) whose switching points converge backward to
`q_out` modulo `V_T`; "returning to the exceptional divisor" is meeting the singular locus again
(the exceptional divisor lies over the singular locus; a return at a finite time means the lift
meets it). A trajectory "tending to `(0, x_in)`" is a chattering arc into the singular locus whose
switching points converge to `q_in`; "emanated at an earlier time from the divisor" is meeting the
singular locus at an earlier time. The trajectories are extremals that are bang-bang with finitely
many switches on compact subintervals away from the singular locus (as Chapter 8 gives for the
minimizer, Theorem 8.3.2). The two parts are time reversals of each other
(`IsChatteringArcInto.reverse`).

**A reading, and why it is no restriction.** The hypothesis "finitely bang-bang on compact
subintervals of `(a, c)`" is not in the book's statement ("A trajectory of the Reinhardt system");
it is a reading of it: the book's proof speaks of the switches of the trajectory ("All switches
must be on the unstable curve"), and without edge extremality Chapter 8 gives no finite bang-bang
structure (REPORT.md, E57). It is in the safe direction for a hypothesis (it weakens the
statement), it is what the assembly of Theorem 16.3.1 can supply (Theorem 8.3.2 on the excursion),
and with it the interior claims follow from Lemma 8.3.4 (`lemma8_3_4`), so that only the endpoint
(`c` in part 1, `a` in part 2) carries content. Layer 7 settles it: the statement without the
hypothesis is equivalent (`theorem14_4_1_iff_unrestricted`,
`SmoothedPolygons/Ch14/NoReturnReading.lean`). The hypothesis is used only before the first return
to the singular locus, where a normal extremal is edge extremal
(`IsExtremalOn.isEdgeExtremalOn_of_ne_zero`) and so finitely bang-bang by Theorem 8.3.2.
Registration name: "Thm 14.4.1 (locally finitely bang-bang extremals)".

## The proof (Layer 7, `SmoothedPolygons/Ch14/NoReturnProof.lean`)

1. **All switches are on the unstable curve.** The switching points of a trajectory emanating from
   `q_out` lie, eventually backward, on the local unstable curve `W^u_loc(q_out)` (`theorem14_3_3`):
   `IsChatteringArcOutOf.eventually_mem_localUnstableSet`
   (`SmoothedPolygons/Ch16/ClusterPoint.lean`), the second part of Theorem 16.4.1 time
   reversed (the book cites neither; E88). It uses only the convergence to `q_out`, which is a
   hypothesis of the statement, and no numerical fact. (`theorem16_4_1_reverse` gives the same
   conclusion but takes the three facts of Table 16.1 as hypotheses, which it needs only to prove
   that convergence.)
2. **The numerical fact N4** (`UnstableCurveLeavesStarDomain`, a named hypothesis): the forward
   orbit of every point of `W^u_loc(q_out)` with `r > 0` switches cyclically and then reaches the
   boundary of the star domain before its next switch. The curve reaches the boundary near
   `(r, x̃₂₁) ≈ (0.21, -3.03)`; once `r ≳ 0.065`, one arc suffices (TeX 11985–11991). Three
   independent numerical models confirm it (module docstring of
   `SmoothedPolygons/Ch14/UnstableCurve.lean`). Following the user's decision (no
   computer-assisted certificate), N4 is being reduced to the single-step statement
   `ArcRegionInvariant` (work in progress).
3. **A return chatters.** If the lift met the singular locus again, then at the first return `s`
   the extremal is a chattering arc into it (`exists_isChatteringArcInto`, Lemma 8.3.4). A
   switching point of the arc out of `q_out` that lies on `W^u_loc` is also a switching point of
   this return arc. Its forward orbit follows the Reinhardt–Poincaré iterates while they switch
   cyclically, and by N4 the arc from the last iterate leaves the star domain before its next
   switch. An extremal cannot do that, because its states are star states (the state constraint
   in `IsExtremalOn`; `IsChatteringArcInto.not_reachesStarBoundary`,
   `SmoothedPolygons/Ch14/UnstableCurveSwitches.lean`).
4. **The second statement** follows by time reversal: it is the first statement applied to the
   reflected extremal (`theorem14_4_1_in`; `IsChatteringArcInto.reverse`,
   `SmoothedPolygons/Ch14/NoReturnTools.lean`, and `switchAng_reverse`,
   `SmoothedPolygons/Ch16/ClusterCoordinates.lean`).
-/

@[expose] public section

namespace SmoothedPolygons

open Set Filter Topology
open TriFuller

/-- **Theorem 14.4.1** (`thm:no-return`, TeX 11995–12002), for locally finitely bang-bang
extremals (a reading of "a trajectory of the Reinhardt system", see the module docstring), as a
named proposition (Layer 7).
1. A trajectory (an extremal on `[a, c]`, `λ_cost = -1`, finitely bang-bang on compact
   subintervals of `(a, c)`) that emanates from `(0, x_out)` — a chattering arc out of the singular
   locus at `a`, on some `[a, b] ⊆ [a, c]`, whose switching points converge backward to `q_out` —
   does not return to the exceptional divisor: its lift avoids the singular locus on `(a, c]`.
2. A trajectory that tends to `(0, x_in)` — a chattering arc into the singular locus at `c`, on some
   `[b, c] ⊆ [a, c]`, whose switching points converge to `q_in` — did not emanate at an earlier time
   from the exceptional divisor: its lift avoids the singular locus on `[a, c)`. -/
def Theorem14_4_1 : Prop :=
  (∀ (a b c : ℝ) (u : ℝ → Fin 3 → ℝ) (g X Λ₁ ΛR : ℝ → Mat2) (τ : ℕ → ℝ),
      IsExtremalOn a c u g X Λ₁ ΛR (-1) → b ∈ Ioc a c →
      (∀ α β, a < α → β < c → IsFiniteBangBang α β u) →
      IsChatteringArcOutOf a b u g X Λ₁ ΛR τ →
      TendstoModVT (switchAng X Λ₁ ΛR τ) (ang qOutCart) →
      ∀ t ∈ Ioc a c, (g t, Λ₁ t, X t, ΛR t) ∉ singularLocus) ∧
    ∀ (a b c : ℝ) (u : ℝ → Fin 3 → ℝ) (g X Λ₁ ΛR : ℝ → Mat2) (τ : ℕ → ℝ),
      IsExtremalOn a c u g X Λ₁ ΛR (-1) → b ∈ Ico a c →
      (∀ α β, a < α → β < c → IsFiniteBangBang α β u) →
      IsChatteringArcInto b c u g X Λ₁ ΛR τ →
      TendstoModVT (switchAng X Λ₁ ΛR τ) (ang (tau qOutCart)) →
      ∀ t ∈ Ico a c, (g t, Λ₁ t, X t, ΛR t) ∉ singularLocus

end SmoothedPolygons
