module

public import SmoothedPolygons.Ch14.FixedPointManifolds

/-!
# Chapter 14: the unstable curve reaches the boundary of the star domain (N4, Figure 14.2)

The numerical fact behind Theorem 14.4.1 (`thm:no-return`) of Hales–Vajjha, *Packings of Smoothed
Polygons*: §14.4, "A Computation of the Unstable Manifold" (TeX 11922–11991). The book computes the
global unstable curve of the fixed point `(0, x_out)` in Mathematica (Figure 14.2, "The unstable
curve `r ↦ (r, x̃₂₁(r))` … starts at the outward fixed point `x̃₂₁out ≈ -2.39` and continues to the
boundary `x̃*₂₁(r) = √3 - 1/r` of the star domain … 434 data points") and states, TeX 11983–11991:
"We check that the other switching functions `χ_ij` remain positive, so that the switching
sequence is always cyclical `3 ↦ 2 ↦ 1 ↦ 3 ↦ ⋯`. The unstable curve reaches the boundary of the
star domain near `(r, x̃₂₁) ≈ (0.21, -3.03)`. Once `r` is at least about `0.065`, a Reinhardt
trajectory starting on the unstable curve reaches the boundary of the star domain before the next
switching time, and the forward step of the Reinhardt–Poincaré map is no longer defined." The
authors did not certify it ("these calculations might be repeated using more rigorous numerical
methods such as interval arithmetic", TeX 11952–11955; REPORT.md, E88). The proof of
Theorem 14.4.1 uses exactly this: "This does not happen, because the unstable curve hits the
boundary of the star domain" (TeX 12009–12010).

This file defines the conditions on the orbits (`SwitchEntersE2`, `ArcSwitchesToE1`,
`ArcLeavesStarDomain`, `ReachesStarBoundary`) and states the fact as the named proposition
`UnstableCurveLeavesStarDomain` (N4). It proves nothing: N4 is a hypothesis of `theorem14_4_1`
(`SmoothedPolygons/Ch14/NoReturnProof.lean`) and of Mahler's First conjecture in its strongest
current form (`theorem16_3_1_of_unstableCurveLeavesStarDomain`,
`SmoothedPolygons/Ch16/BasinFacts.lean`).

## The statement (`UnstableCurveLeavesStarDomain`, N4)

For some analytic extension `e` of the Reinhardt–Poincaré map at `(0, x̃_out)` (Lemma 14.3.1) and
some neighborhood `U` of the fixed point, every point `p` of the local unstable curve
`W^u_loc(e, U)` (`Function.localUnstableSet`, a `C^∞` curve by Theorem 14.3.3) with `r > 0` has a
forward orbit that reaches the boundary of the star domain (`ReachesStarBoundary (lieChart p)`):
for some `K`, the iterates `q_j = F^j (lieChart p)` (`F = reinPoincare`, phase points, no chart
after the first) satisfy
* for `j ≤ K`, `SwitchEntersE2 q_j`: the control after the switch at `q_j` is `e₂`
  (`H(e₁) < H(e₂)` at `q_j`, and `e₃` drops below `e₂` at once along its own flow);
* for `j < K`, `ArcSwitchesToE1 q_j`: along the `e₂`-arc, `e₂` is the strict maximizer up to
  `t_sw(q_j)`, where `e₁` takes over (the switching sequence is cyclic; the "other switching
  functions remain positive");
* `ArcLeavesStarDomain q_K`: the `e₂`-arc from `q_K` leaves the star domain at a time `T`, with `e₂`
  the strict maximizer on `(0, T)` ("reaches the boundary of the star domain before the next
  switching time").
These are the hypotheses of `IsChatteringArcInto.next_switchPoint_eq_reinPoincare` along the orbit,
plus the exit: what the proof needs (`IsChatteringArcInto.not_reachesStarBoundary`,
`SmoothedPolygons/Ch14/UnstableCurveSwitches.lean`), about the true closed-form flow
(`iso_vertexFlow`), and nothing about the chart beyond the first point.

Remarks on the form.
* With `∃ U`, `∃ e` and `∀ e` give equivalent statements: two extensions agree on a ball around
  the fixed point (both are analytic and equal `reinChartMap` on `{r > 0}`; identity theorem), so
  their local unstable sets in a small `U` agree (`localUnstableSet e p U` uses `e` only on `U`,
  and it shrinks with `U`), and `lemma14_3_1` provides one extension. `∃ e` is the weaker form.
* `U` stays existential: for a large `U`, `e` off its source and `lieChart` off its domain are junk
  values, so "for every `U`" would be false. One `U` is all the proof needs, because the switching
  points lie on `W^u_loc(e, U)` for every `U ∈ 𝓝 chartPtOut`
  (`IsChatteringArcOutOf.eventually_mem_localUnstableSet`). The statement is not vacuous:
  Theorem 14.3.3 puts points with `r > 0` on `W^u_loc(e, U)` for every such `U`.
* The statement is about all of `W^u_loc(e, U) ∩ {r > 0}`, not a fundamental domain: `K` grows like
  `log(1/r)/log r_scale` as `r → 0`. Near the fixed point the conditions are those of the local
  theory (`eventually_isSwitch_reinSwitchTime`, `eventually_switchStructure`).
* Along the `e₂`-arc `ρ₁` is constant (`⟨Z_{e₂}, X⟩` is constant, Lemma 7.1.1); the arc leaves `𝔥*`
  through `ρ₂ = 0`, where `⟨X, Z_{e₁}⟩ → 0` and `H(e₁) → -∞` (so `e₂` stays the strict maximizer up
  to the boundary). In Lean `phaseHam` at a point with `⟨X, Z_v⟩ = 0` is a junk value (division by
  zero), hence the open interval `(0, T)`. Rotated by `Ad_{R⁻¹}`, the side `ρ₂ = 0` is the side
  `ρ₁ = 0`, i.e. `x = 1/√3`, which is the chart boundary `x̃₂₁ = √3 - 1/r` of Figure 14.2.

## Numerical evidence

Three independent numerical models of these definitions (an ODE solver in double precision, a
Taylor-series ODE solver in `mpmath`, and the exact `cosh`/`sinh` closed form of `iso_vertexFlow`
at 60 digits), each following the orbits of points of `W^u` over a fundamental domain to their
exit, confirm N4. Every orbit switches cyclically and then leaves the star domain through `ρ₂ = 0`,
with `K = 2` or `3` steps from `r ∈ [10⁻³, 6.21·10⁻³)`, as the book says. The last switching point
before a one-arc exit has `r ≥ r* ≈ 0.06495` (the book's "about 0.065"; a TeX comment gives
`0.0641`), and the switching points approach the chart boundary at
`(r, x̃₂₁) → (0.209847, -3.033319)` (the book's `(0.21, -3.03)`). All margins of N4 (the gaps of
the Hamiltonians at the switching points and along the arcs, the slopes at the simple zeros of the
switching functions, the transversality `ρ₂'(T) = -1` of the exit) are positive and bounded below
in the natural scales `H ~ r³`, `t ~ r` near the divisor.

**The threshold** `r*` is degenerate: there the switch and the exit of the arc coincide, and the
cleared switching function `χ₂₁ ⟨X, Z_{e₁}⟩ ⟨X, Z_{e₂}⟩` at the exit tends to `0`. Above `r*` this
value is linear in the parameter of the curve; below `r*` the switching point lies at distance
`ε → 0` from the side `ρ₁ = 0` and the next arc runs along it into a cusp of `𝔥*`, with rate
`ω = 1/(2ε)`, where the margins have positive limits in the natural scales of that arc. So N4 holds
on both sides of `r*`, but no uniform inequality in the raw variables, and no interval enclosure,
decides the ordering of the switch and the exit near `r*`: any proof needs a local asymptotic
argument there.

## Status

N4 stays a named hypothesis. Following the user's decision for the book's numerical facts (proofs
without computer assistance, the computation kept as a Python reference in `numerics/`), N4 is
being reduced, by the exact structure of the `e₂`-arcs, to a single-step statement about the
Reinhardt–Poincaré map, `ArcRegionInvariant` (work in progress, `SmoothedPolygons/Ch14/Arc*.lean`).
Along an `e₂`-arc `⟨Z_{e₂}, X⟩` is constant, `e^{tP}` and `e^{t(X₀ + P)}` are hyperbolic with the
same rate `ω = 1/(2ρ₁)` (`det(X₀ + P) = det P`, Lemma 7.1.3), so the state, the exit time and the
cleared switching functions along the arc are explicit exponential polynomials.
-/

@[expose] public section

namespace SmoothedPolygons

open Set Filter Topology

/-- **After a switch at `q`, the control is `e₂`** (the cyclic switching sequence
`3 → 2 → 1 → 3`, TeX 11983–11985): at the point `q` of the section `χ₂₃ = 0`, `e₁` is strictly
below `e₂`, and along the `e₃`-flow from `q`, `e₃` falls strictly below `e₂` right after `q` (so an
extremal through `q` can use neither `e₁` nor `e₃` next). These are the hypotheses `h0`, `h2` of
`IsChatteringArcInto.next_switchPoint_eq_reinPoincare`. -/
def SwitchEntersE2 (q : iso_PhasePt) : Prop :=
  phaseHam q (vertex 0) < phaseHam q (vertex 1) ∧
    ∃ ε > 0, ∀ t ∈ Ioo 0 ε,
      phaseHam (iso_vertexFlow 2 q t) (vertex 2) < phaseHam (iso_vertexFlow 2 q t) (vertex 1)

/-- **The `e₂`-arc from `q` switches to `e₁` at `t_sw(q)`** (TeX 11983–11985: "We check that the
other switching functions `χ_ij` remain positive, so that the switching sequence is always
cyclical"): `t_sw(q) > 0`, `e₂` is the strict maximizer of the Hamiltonian among the vertices along
the `e₂`-flow on `(0, t_sw(q))`, and `e₁` beats `e₂` at times arbitrarily close after `t_sw(q)`.
These are the hypotheses `hpos`, `hmax`, `hbeat` of
`IsChatteringArcInto.next_switchPoint_eq_reinPoincare`, the conditions under which
`reinPoincare q` is the next switching point (rotated) of an extremal through `q`. -/
def ArcSwitchesToE1 (q : iso_PhasePt) : Prop :=
  0 < reinSwitchTime q ∧
    (∀ t ∈ Ioo 0 (reinSwitchTime q), ∀ j : Fin 3, j ≠ 1 →
      phaseHam (iso_vertexFlow 1 q t) (vertex j) < phaseHam (iso_vertexFlow 1 q t) (vertex 1)) ∧
    ∀ ε > 0, ∃ t ∈ Ioo (reinSwitchTime q) (reinSwitchTime q + ε),
      phaseHam (iso_vertexFlow 1 q t) (vertex 1) < phaseHam (iso_vertexFlow 1 q t) (vertex 0)

/-- **The `e₂`-arc from `q` reaches the boundary of the star domain before the next switching time**
(TeX 11987–11991: "a Reinhardt trajectory starting on the unstable curve reaches the boundary of the
star domain before the next switching time, and the forward step of the Reinhardt–Poincaré map is
no longer defined"): at some time `T > 0` the state `X(T)` of the `e₂`-flow from `q` is not a star
state, and `e₂` is the strict maximizer of the Hamiltonian among the vertices on `(0, T)`. -/
def ArcLeavesStarDomain (q : iso_PhasePt) : Prop :=
  ∃ T > 0, ¬ IsStarState (iso_vfX 1 q T) ∧ ∀ t ∈ Ioo 0 T, ∀ j : Fin 3, j ≠ 1 →
    phaseHam (iso_vertexFlow 1 q t) (vertex j) < phaseHam (iso_vertexFlow 1 q t) (vertex 1)

/-- **The forward orbit of `q` under the Reinhardt–Poincaré map reaches the boundary of the star
domain**: for some `K`, the iterates `F^j q` (`F = reinPoincare`, `j < K`) switch cyclically
(`SwitchEntersE2`, `ArcSwitchesToE1`), and the arc from `F^K q` (where the control is again `e₂`)
leaves the star domain before its next switch. -/
def ReachesStarBoundary (q : iso_PhasePt) : Prop :=
  ∃ K : ℕ, (∀ j ≤ K, SwitchEntersE2 (reinPoincare^[j] q)) ∧
    (∀ j < K, ArcSwitchesToE1 (reinPoincare^[j] q)) ∧ ArcLeavesStarDomain (reinPoincare^[K] q)

/-- **N4: the unstable curve `W^u(q_out)` reaches the boundary of the star domain** (Figure 14.2,
TeX 11951–11991; the numerical fact on which the proof of Theorem 14.4.1 rests, "This does not
happen, because the unstable curve hits the boundary of the star domain", TeX 12009–12010). There
are an analytic extension `e` of the Reinhardt–Poincaré map at `(0, x̃_out)` (Lemma 14.3.1) and a
neighborhood `U` of the fixed point such that the forward orbit of every point `p` of the local
unstable curve `W^u_loc(e, U)` with `r > 0` reaches the boundary of the star domain
(`ReachesStarBoundary (lieChart p)`). With `∃ U`, this is equivalent to the same for every
extension `e`; `U` must stay existential (module docstring). See the module docstring for the
reading, the numerical evidence and the threshold. -/
def UnstableCurveLeavesStarDomain : Prop :=
  ∃ e : OpenPartialHomeomorph (ℝ × (Fin 3 → ℝ)) (ℝ × (Fin 3 → ℝ)),
    IsReinhardtPoincareExtension e ∧ ∃ U ∈ 𝓝 chartPtOut,
      ∀ p ∈ Function.localUnstableSet e chartPtOut U, 0 < p.1 → ReachesStarBoundary (lieChart p)

end SmoothedPolygons
