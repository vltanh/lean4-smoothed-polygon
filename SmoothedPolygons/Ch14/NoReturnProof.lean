module

public import SmoothedPolygons.Ch14.NoReturn
public import SmoothedPolygons.Ch14.UnstableCurveSwitches
public import SmoothedPolygons.Ch14.SwitchingPointsOnCurve

/-!
# Chapter 14: Theorem 14.4.1 (no return) from the numerical fact N4

Theorem 14.4.1 (`thm:no-return`) of Hales–Vajjha, *Packings of Smoothed Polygons* (TeX
11995–12013), as the named proposition `Theorem14_4_1` (`SmoothedPolygons/Ch14/NoReturn.lean`),
proved from the numerical fact N4 (`UnstableCurveLeavesStarDomain`,
`SmoothedPolygons/Ch14/UnstableCurve.lean`: the unstable curve `W^u(q_out)` reaches the boundary of
the star domain, Figure 14.2): `theorem14_4_1`.

## The book's proof (TeX 12003–12013), step by step

"All switches must be on the unstable curve, which meets that exceptional divisor at a single point
`(0, x_out)`. Any trajectory that returns to the singular locus must chatter (that is, must use
infinitely many switches to arrive). This would require the unstable curve to contain a sequence of
*forward* iterates of points tending to the exceptional divisor. This does not happen, because the
unstable curve hits the boundary of the star domain. The second statement follows from the first
by time reversal."

First statement (`theorem14_4_1_out`). Let the extremal on `[a, c]` (`λ_cost = -1`, finitely
bang-bang on compact subintervals of `(a, c)`) emanate from `q_out`: a chattering arc out of the
singular locus on `[a, b]` whose switching points `τ n ↓ a` converge backward to `q_out` modulo
`V_T`. Suppose its lift meets the singular locus at some `t ∈ (a, c]`; then `t > b` (the arc avoids
it on `(a, b]`).
1. **The first return.** Let `s ∈ (b, t]` be the first meeting time after `b`
   (`IsExtremalOn.exists_first_mem_singularLocus`): the lift is on the singular locus at `s` and off
   it on `(a, s)`.
2. **"All switches must be on the unstable curve"**: for the extension `e` and the neighborhood `U`
   of N4, eventually each switching point `τ N` of the arc out of `a`, rotated by `Ad_{R⁻ᵏ}`, is
   `lieChart p` with `p ∈ W^u_loc(e, U)`, `r > 0`
   (`IsChatteringArcOutOf.eventually_mem_localUnstableSet`, Theorem 16.4.1 time reversed, from the
   convergence hypothesis; no numerical fact). Fix such `N`.
3. **"Any trajectory that returns to the singular locus must chatter"**: on `[a', s]`, with
   `a' = (τ (N + 1) + τ N)/2 ∈ (a, s)`, the extremal is a chattering arc into the singular locus
   (`exists_isChatteringArcInto`: its switching times in `(a', s)` accumulate at `s`, Lemma 8.3.4);
   `τ N` is one of them, `σ n₀ = τ N` (the arc's switching sequence `σ` enumerates all switching
   times in `(a', s)`, and `τ N` is a switching time there).
4. **"This does not happen, because the unstable curve hits the boundary of the star domain"**: by
   N4 the orbit of `lieChart p` reaches the boundary of the star domain
   (`ReachesStarBoundary (lieChart p)`), which no switching point of a chattering arc can do
   (`IsChatteringArcInto.not_reachesStarBoundary` at `σ n₀`): a contradiction. (Its proof: the
   switching points `σ (n₀ + j)` follow the Reinhardt–Poincaré iterates of `lieChart p` while they
   switch cyclically, and the arc from the last one leaves the star domain before the next switch,
   which an extremal, whose states are star states, cannot do.)

Second statement (`theorem14_4_1_in`), **by time reversal**: the reflection `t ↦ a + c - t` of the
extremal on `[a, c]` (`IsExtremalOn.reverse`, `IsFiniteBangBang.reverseControl`) turns the
chattering arc into the singular locus on `[b, c]` into a chattering arc out of it on
`[a, a + c - b]` (`IsChatteringArcInto.reverse`) whose switching points converge backward to
`τ(q_in) = q_out` (`switchAng_reverse`, `TendstoModVT.tau`, `tau_ang_tau_qOutCart`); the first
statement for the reflected extremal (an instance of `theorem14_4_1_out`) gives that its lift avoids
the singular locus on `(a, c]`, i.e. the original lift avoids it on `[a, c)`
(`reverse_mem_singularLocus_iff`).

The book's "trajectory of the Reinhardt system" lives in the star domain: the hypothesis
`IsExtremalOn a c …` contains the state constraint (`IsStateTrajectory`: `IsStarState (X t)` on
`[a, c]`), which step 4 uses. The finite bang-bang hypothesis of `Theorem14_4_1` (the reading of
"trajectory") is used only on `(a, s)`, where Theorem 8.3.2 gives it anyway: the statement without
it is equivalent (`theorem14_4_1_iff_unrestricted`, `SmoothedPolygons/Ch14/NoReturnReading.lean`).

## Proofs (planned)

`theorem14_4_1_out`: steps 1–4 above (about 150 lines: the choice of `N` with
`eventually_atTop`, the location of `τ N` in `σ` from the two enumerations — `τ N ∈ (a', s)` is a
switching time, so `τ N = σ n₀` by `IsSwitchingSeqInto` — and the bookkeeping of intervals).
`theorem14_4_1_in`: the reflection (about 60 lines). `theorem14_4_1`: the two together.
Size: 200–300 lines.
-/

@[expose] public section

namespace SmoothedPolygons

open Set Filter Topology
open TriFuller

/-- **Theorem 14.4.1, first statement** (`thm:no-return`, TeX 11995–11998), from N4: a trajectory
(an extremal on `[a, c]`, `λ_cost = -1`, finitely bang-bang on compact subintervals of `(a, c)`)
that emanates from `(0, x_out)` — a chattering arc out of the singular locus at `a` on
`[a, b] ⊆ [a, c]` whose switching points converge backward to `q_out` modulo `V_T` — does not return
to the exceptional divisor: its lift avoids the singular locus on `(a, c]`. -/
theorem theorem14_4_1_out (hN4 : UnstableCurveLeavesStarDomain) {a b c : ℝ}
    {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {τ : ℕ → ℝ}
    (hext : IsExtremalOn a c u g X Λ₁ ΛR (-1)) (hb : b ∈ Ioc a c)
    (hbb : ∀ α β, a < α → β < c → IsFiniteBangBang α β u)
    (hout : IsChatteringArcOutOf a b u g X Λ₁ ΛR τ)
    (hconv : TendstoModVT (switchAng X Λ₁ ΛR τ) (ang qOutCart)) :
    ∀ t ∈ Ioc a c, (g t, Λ₁ t, X t, ΛR t) ∉ singularLocus := by
  sorry

/-- **Theorem 14.4.1, second statement** (`thm:no-return`, TeX 11999–12002), from N4, by time
reversal (an instance of `theorem14_4_1_out` for the reflected extremal): a trajectory that tends to
`(0, x_in)` — a chattering arc into the singular locus at `c` on `[b, c] ⊆ [a, c]` whose switching
points converge to `q_in` modulo `V_T` — did not emanate at an earlier time from the exceptional
divisor: its lift avoids the singular locus on `[a, c)`. -/
theorem theorem14_4_1_in (hN4 : UnstableCurveLeavesStarDomain) {a b c : ℝ}
    {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {τ : ℕ → ℝ}
    (hext : IsExtremalOn a c u g X Λ₁ ΛR (-1)) (hb : b ∈ Ico a c)
    (hbb : ∀ α β, a < α → β < c → IsFiniteBangBang α β u)
    (hin : IsChatteringArcInto b c u g X Λ₁ ΛR τ)
    (hconv : TendstoModVT (switchAng X Λ₁ ΛR τ) (ang (tau qOutCart))) :
    ∀ t ∈ Ico a c, (g t, Λ₁ t, X t, ΛR t) ∉ singularLocus := by
  sorry

/-- **Theorem 14.4.1** (`thm:no-return`, TeX 11995–12013), for locally finitely bang-bang extremals
(the reading of `Theorem14_4_1`, equivalent to the unrestricted statement,
`theorem14_4_1_iff_unrestricted`), **from the numerical fact N4** (`UnstableCurveLeavesStarDomain`,
Figure 14.2): the book's proof, the first statement by `theorem14_4_1_out` and the second by time
reversal, `theorem14_4_1_in`. -/
theorem theorem14_4_1 (hN4 : UnstableCurveLeavesStarDomain) : Theorem14_4_1 := by
  sorry

end SmoothedPolygons
