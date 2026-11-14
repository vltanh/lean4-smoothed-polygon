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
Theorem 16.3.1 (`SmoothedPolygons/Ch16/NoChattering.lean`); it is proved in Layer 7. The book's
proof rests on a figure: "All switches must be on the unstable curve, which meets that exceptional
divisor at a single point `(0, x_out)`. Any trajectory that returns to the singular locus must
chatter … This would require the unstable curve to contain a sequence of forward iterates of points
tending to the exceptional divisor. This does not happen, because the unstable curve hits the
boundary of the star domain" (the numerical computation of Figure 14.2, TeX 11951–11991,
uncertified by the authors' own statement; G14.10).

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
(`IsChatteringArcOutOf.reverse`).

**A reading, to be settled in Layer 7.** The hypothesis "finitely bang-bang on compact
subintervals of `(a, c)`" is not in the book's statement ("A trajectory of the Reinhardt system");
it is a reading of it: the book's proof speaks of the switches of the trajectory ("All switches
must be on the unstable curve"), and without edge extremality Chapter 8 gives no finite bang-bang
structure (REPORT.md, E57). It is in the safe direction for a hypothesis (it weakens the
statement), it is what the assembly of Theorem 16.3.1 can supply (Theorem 8.3.2 on the excursion),
and with it the interior claims follow from Lemma 8.3.4 (`lemma8_3_4`), so that only the endpoint
(`c` in part 1, `a` in part 2) carries content. Layer 7 is to settle whether the statement without
it has a counterexample (a non-bang-bang extremal through the singular locus) or whether the
reading is the only sensible one. Registration name: "Thm 14.4.1 (locally finitely bang-bang
extremals)".

## Plan for Layer 7 (N4)

1. By the time-reversed Theorem 16.4.1 (`theorem16_4_1_reverse`; the book does not cite it,
   G14.11), the switching points of a trajectory emanating from `q_out` lie on the local unstable
   curve `W^u_loc(q_out)` (`theorem14_3_3`), eventually backward.
2. **N4** (the numerical content, to be certified): every point of `W^u_loc(q_out)` with `r > 0` has
   a forward iterate under the Reinhardt–Poincaré map at which the trajectory reaches the boundary
   of the star domain before its next switch (the curve reaches the boundary near
   `(r, x̃₂₁) ≈ (0.21, -3.03)`; from `r ≳ 0.065` on, one arc suffices, TeX 11975–11991). A
   certificate: a validated enclosure of `W^u_loc` (a Lipschitz graph over `r ∈ (0, r₀]` with cone
   conditions, from the contraction `< 1/10` and the expansion `r_scale`), then validated iteration
   of the closed-form flow on a fundamental domain `[r₀/r_scale, r₀]` with interval Newton for the
   switching times, until the star condition fails.
3. A trajectory returning to the singular locus at a later time chatters into it (Lemma 8.3.4), so
   by Theorem 16.4.1 its switching points approach the divisor; with steps 1–2 that is impossible
   (before reaching the divisor the trajectory leaves the star domain, where no Reinhardt
   trajectory lives, Theorem 4.4.1).
4. The second statement: time reversal (`IsChatteringArcOutOf.reverse`, `fullerCoords_reinTau`).
Size: 150–400 lines with N4 as a hypothesis; certification of N4 5,000–15,000 lines.
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
