module

public import SmoothedPolygons.Ch14.FixedPointManifolds

/-!
# Chapter 14: the unstable curve reaches the boundary of the star domain (N4, Figure 14.2)

The numerical fact behind Theorem 14.4.1 (`thm:no-return`) of Hales–Vajjha, *Packings of Smoothed
Polygons*: §14.4, "A Computation of the Unstable Manifold" (TeX 11922–11991). The book computes the
global unstable curve of the fixed point `(0, x_out)` in Mathematica (Figure 14.2, "The unstable
curve `r ↦ (r, x̃₂₁(r))` … starts at the outward fixed point `x̃₂₁out ≈ -2.39` and continues to the
boundary `x̃*₂₁(r) = √3 - 1/r` of the star domain … 434 data points") and states, TeX 11975–11986:
"We check that the other switching functions `χ_ij` remain positive, so that the switching
sequence is always cyclical `3 ↦ 2 ↦ 1 ↦ 3 ↦ ⋯`. The unstable curve reaches the boundary of the
star domain near `(r, x̃₂₁) ≈ (0.21, -3.03)`. Once `r` is at least about `0.065`, a Reinhardt
trajectory starting on the unstable curve reaches the boundary of the star domain before the next
switching time, and the forward step of the Reinhardt–Poincaré map is no longer defined." The
authors did not certify it ("these calculations might be repeated using more rigorous numerical
methods such as interval arithmetic", TeX 11954–11957; REPORT.md, E88). The proof of
Theorem 14.4.1 uses exactly this: "This does not happen, because the unstable curve hits the
boundary of the star domain" (TeX 12007–12008).

## The statement (`UnstableCurveLeavesStarDomain`, N4)

For an analytic extension `e` of the Reinhardt–Poincaré map at `(0, x̃_out)` (Lemma 14.3.1) and a
neighborhood `U` of the fixed point, every point `p` of the local unstable curve
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
* `∃ e` or `∀ e` give equivalent statements: two extensions agree on a ball around the fixed point
  (both are analytic and equal `reinChartMap` on `{r > 0}`; identity theorem), so their local
  unstable sets in a small `U` agree, and `lemma14_3_1` provides one. `∃` is the weaker form.
* The statement is about all of `W^u_loc(e, U) ∩ {r > 0}`, not a fundamental domain: `K` grows like
  `log(1/r)/log r_scale` as `r → 0`. Near the fixed point the conditions are those of the local
  theory (`eventually_isSwitch_reinSwitchTime`, `eventually_switchStructure`), and the reduction to
  a fundamental domain is the first step of the certificate (below).
* Along the `e₂`-arc `ρ₁` is constant (`⟨Z_{e₂}, X⟩` is constant, Lemma 7.1.1); the arc leaves `𝔥*`
  through `ρ₂ = 0`, where `⟨X, Z_{e₁}⟩ → 0` and `H(e₁) → -∞` (so `e₂` stays the strict maximizer up
  to the boundary). In Lean `phaseHam` at a point with `⟨X, Z_v⟩ = 0` is a junk value (division by
  zero), hence the open interval `(0, T)`. Rotated by `Ad_{R⁻¹}`, the side `ρ₂ = 0` is the side
  `ρ₁ = 0`, i.e. `x = 1/√3`, which is the chart boundary `x̃₂₁ = √3 - 1/r` of Figure 14.2.

## The numerical check (`notes/l7st/`, README.txt there)

Two independent models of the Lean definitions: double precision (scipy, DOP853, `rtol = 1e-13`)
and mpmath (dps 30–34, Taylor series ODE solver). The switch is the first zero of the cleared
numerator `N₂₁ = χ₂₁ ⟨X, Z_{e₁}⟩ ⟨X, Z_{e₂}⟩` (same sign as `χ₂₁` in `𝔥*`; `χ₂₁` itself has a pole
at the exit, which a naive zero search takes for a switch). Points of `W^u`:
`(s, x̃_out + v s + w s²)`, `v = γ'(0) ≈ (-1.0777, -13.389, 3.9344)` (secant iteration and
Richardson extrapolation), `w ≈ (-2.56, -36.2, 7.7)`; the error in the stable directions is
contracted by `≈ 0.08` per step. Checks: the fixed point (`t_sw/r → 8.843`,
`r'/r → r_scale = 6.27417`); 480 points of the fundamental domain `D = {r ∈ [10⁻³, 6.21·10⁻³)}`
(double precision) and 32 orbits started on `{r ∈ [10⁻⁵, 6.27·10⁻⁵)}` (mpmath), each followed to its
exit.

Results. Every orbit switches cyclically and then leaves the star domain through `ρ₂ = 0`, with
`K = 2` or `3` steps from `D` (`K = 4` or `5` from `r ~ 10⁻⁵`), as the book says. The last
switching point before a one-arc exit has `r ≥ r* ≈ 0.0650` (the book's "about 0.065"; its comment
gives `0.0641`), and the switching points approach the chart boundary at
`(r, x̃₂₁) → (0.2098, -3.0326)` (the book's `(0.21, -3.03)`; `√3 - 1/0.2098 = -3.034`).
Margins (mpmath, 188 arcs of the 32 orbits). Near the divisor (`r < 0.01`), in the natural scales
`H ~ r³`, `t ~ r`: `H(e₂) - H(e₁) ≥ 13.2 r³` at the switching points; the slope of
`H(e₃) - H(e₂)` along the `e₃`-flow `≤ -7.8 r²`; `χ₂₃(t)/t ≥ 8.5 r²` on the arcs;
`χ₂₁(t)/(t_sw - t) ≥ 1.8 r²` before a switch; `-N₂₁'(t_sw) ≥ 115 r²` (simple zeros). In the global
part (`r ≥ 0.01`, raw values): `H(e₂) - H(e₁) ≥ 1.4·10⁻⁵`, `-(H(e₃) - H(e₂))' ≥ 8.5·10⁻⁴`,
`χ₂₃(t)/t ≥ 9.3·10⁻⁴`, `χ₂₁(t)/(t_sw - t) ≥ 2.0·10⁻⁴`, `-N₂₁'(t_sw) ≥ 0.012` (all at `r ≈ 0.0102`,
still the scale `r³ ≈ 10⁻⁶`); on the exit arcs `χ₂₁ ≥ 0.0054` on `(0, T)` and `ρ₂'(T) = -1.000`
(transversal). The 480 double-precision orbits give the same signs. All margins are positive, and
bounded below in these scales, away from one point:

**The threshold** `r*`, where the switch and the exit coincide (`N₂₁` and `ρ₂` vanish together),
is degenerate; the orbits of the points of `W^u` near one parameter value in each fundamental domain
pass close to it (on `D`, `s* ≈ 0.0018895`):
* from above (one-arc exit): `N₂₁(T_exit) ≈ 23.4 (s - s*)`, linear in the parameter `s` of `D`;
* from below (switch, then exit): the switching point lies at distance `ε = ρ₁ → 0` from the side
  `ρ₁ = 0` (after the rotation), and the next arc runs along that side into a cusp of `𝔥*`, with the
  rate `ω = 1/(2ε)`; for `ε ∈ [1.5·10⁻⁴, 4·10⁻³]` (18 orbits, double precision; smaller `ε` is
  numerically stiff and was not reached) `T/ε - log(1/ε) = 0.854…0.868`, `N₂₁(T)/ε² = 0.50…0.43`
  and `⟨Λ_R(T), Z_{e₁}⟩/ε = -0.44…-0.37` (the exit sign, in the natural scale `Λ_R ~ ε` of that
  arc), fitted by `a + b ε log(1/ε)` with limits `0.868`, `0.42`, `-0.36` as `ε → 0`.
So N4 holds there too, but with margins that vanish at `r*`: no uniform inequality (and no interval
enclosure) gives it there; it needs a local asymptotic argument.

## Proving N4 in Lean without computer assistance (the user's decision), and why it is hard

The user's decision for the book's numerical facts: proofs in Lean from exact structure and a small
number of explicit inequalities proved by ordinary tactics (a departure from the book, which
computes), with the computation kept as a Python reference (`numerics/`, rigorous ball
arithmetic). The best analytic route I can see for N4:

1. **Exact structure of an arc.** Along an `e₂`-arc `⟨Z_{e₂}, X⟩ = -(2/√3) ρ₁` is constant, so
   `P = Z_{e₂}/⟨Z_{e₂}, X₀⟩` is constant with `det P = -1/(4ρ₁²)`, and `det(X₀ + P) = det P` (both
   traceless, `det X₀ = 1`, `⟨X₀, P⟩ = 1`): the two one-parameter groups of the closed form,
   `e^{tP}` and `e^{t(X₀ + P)}` (`g = e^{t(X₀+P)} e^{-tP}`), are hyperbolic with the same rate
   `ω = 1/(2ρ₁)`. Hence along the arc `ρ₀(t)`, `ρ₂(t)` are `a + b cosh 2ωt + c sinh 2ωt` (one
   explicit exit time, a root of a quadratic in `e^{2ωt}`), and the cleared switching numerators
   `N₂ⱼ(t) = χ₂ⱼ ⟨X, Z_{e_j}⟩ ⟨X, Z_{e₂}⟩` are exponential polynomials
   `Σ c_{mk} t^m e^{2kωt}` (`m ≤ 2` from the quadratures of `Λ_R`, `|k| ≤ 3`) whose coefficients
   are polynomial in the entries of the initial point and in `1/ρ₁` (checked numerically: the fit
   residual is `10⁻¹⁵`, `notes/l7st/`). All conditions of N4 on one arc are then sign conditions of
   such functions on explicit intervals; the zero counts (one simple zero of `N₂₁`, none of `N₂₃`,
   `ρ₂`) could come from Rolle/Descartes-type bounds for exponential polynomials, the switching and
   exit times from sign changes at two explicit bracketing times.
2. **A trapping region instead of the curve.** `W^u` is only known to be a `C^∞` graph
   (Theorem A.3.1), with no explicit bounds. Replace it by an explicit region
   `𝒯 = {0 < r ≤ r₂, |x̃ - c(r)| ≤ κ(r)}` around a polynomial centre curve `c` (from the reference
   computation, `c(r) = x̃_out + v r + w r² + …`), and prove (a) every point of `𝒯` with `r < r*⁻`
   switches cyclically and maps into `𝒯` with `r` multiplied by at least `λ > 1` (`r'/r` falls from
   `r_scale ≈ 6.27` at the divisor to `≈ 4.3` at `r ≈ 0.037`), (b) every point of `𝒯` with
   `r ≥ r*⁻` reaches the star boundary within two arcs, (c) near the divisor, `W^u_loc ⊆ 𝒯`:
   the curve is tangent to `(1, v)` (Theorem 14.3.3), and the forward invariance of the tip of `𝒯`
   needs second-order bounds of the extension `e` on an explicit box, i.e. quantitative versions of
   Lemmas 14.2.3, 14.2.4 and 14.3.1 (Cauchy estimates of the analytic rescaled flow on an explicit
   complex polydisk, through the implicit switching time).
3. **The threshold** by an asymptotic analysis of the closed form: above `r*` the sign of
   `N₂₁(T_exit)` (linear in `r - r*`) and the monotonicity of `N₂₁` before `T_exit`; below `r*` the
   cusp arc, with `ω = 1/(2ε)`, expanded in `ε` through the cusp (`T/ε - log(1/ε)` and
   `⟨Λ_R(T), Z_{e₁}⟩/ε` have finite nonzero limits).

What makes it hard: (i) the global part has no small parameter (`r` up to `0.21`; the chart
coordinates move far from `x̃_out`, e.g. `ℓ̃₁₁` from `-4.9` to `-9` at `r ≈ 0.16`), so nothing
reduces to the Fuller system of Chapter 13 there; (ii) the switching times are transcendental (first
zeros of exponential polynomials with secular terms `t e^{…}`, `t² e^{…}`, for which Descartes'
rule does not apply directly), and each of the 2–3 arcs needs them bracketed for every point of a
4-dimensional region (or of a validated tube around a curve); (iii) the curve itself must be
located, which needs explicit derivative bounds of a 4-dimensional map near the divisor, i.e.
the asymptotics of Chapter 14 with explicit constants; (iv) the threshold makes every uniform margin
vanish, so it needs its own asymptotic argument, through the cusp of `𝔥*`. I see no structure
(monotonicity, an invariant ordering, a conserved quantity beyond `H = 0`, `det Λ₁ = 9/4`,
`⟨X, Λ_R⟩ = 0`) that would replace (ii)–(iii) by a few inequalities. A computer-free proof of N4
looks like a research project of its own (more than 10,000 lines, without a firm estimate); I
recommend keeping N4 as a named hypothesis unless the reference computation reveals more structure.

## What the Python reference should compute (to support the analytic route)

1. `W^u` on a fundamental domain `D = {r ∈ [r₀, e₁(r₀)]}` (`r₀ ≈ 10⁻³`) with rigorous error bounds:
   the Taylor data `v = γ'(0) ≈ (-1.0777, -13.389, 3.9344)`, `γ''(0)/2 ≈ (-2.56, -36.2, 7.7)`, and a
   validated tube (the contraction `≈ 0.08` per step makes it thin).
2. Along each orbit from `D`, per arc: the switching time and the slope `N₂₁'(t_sw)`, the exit time
   and `ρ₂'(T)`, and every margin of N4 (as in the numerical check above, normalized by `r³`, `r²`
   near the divisor), the number `K` of arcs (2 or 3) as a function on `D`.
3. The threshold: its parameter `s*` on `D`, `r*`, the end point `(0.2098, -3.0326)` of the curve of
   switching points, the slope `dN₂₁(T_exit)/ds` at `s*`, and below `s*` the `ε`-expansion of the
   cusp arc (`T/ε - log(1/ε)`, `N₂₁(T)/ε²`, `⟨Λ_R(T), Z_{e₁}⟩/ε`) with rigorous bounds for
   `ε ∈ (0, ε₀]`, in the time `t/ε` and the costate `Λ_R/ε` (in `t` the arc is stiff: the
   double-precision check did not get below `ε ≈ 10⁻⁴`).
4. For the trapping region: a candidate `𝒯` (centre `c(r)`, widths `κ(r)`), its forward-invariance
   margins, the expansion `r'/r`, and bounds of `DF` on `𝒯` (the transversal contraction).
5. The coefficients `c_{mk}(p)` of `N₂₁`, `N₂₃`, `ρ₀`, `ρ₂` on each arc and their sign patterns over
   the regions, to see whether a Descartes-type count certifies the zero counts.

## The interval route (superseded by the decision above)

With kernel-checked interval arithmetic (`Basic/Interval/`, notes/briefs/lp_report.md) the same
three parts would be: quantitative local bounds near the divisor (Taylor models in `r` of the
rescaled flow, 2,000–4,000 lines); validated iteration of `10²–10³` thin boxes covering `D` through
their 2–3 arcs (a new `exp` enclosure; about `10⁵` steps, 10 h CPU, a soundness chain of 1,500–2,500
lines); and the threshold by the analytic argument of step 3 (1,000–2,000 lines): 5,000–10,000 lines
in all, the estimate of `SmoothedPolygons/Ch14/NoReturn.lean`.
-/

@[expose] public section

namespace SmoothedPolygons

open Set Filter Topology

/-- **After a switch at `q`, the control is `e₂`** (the cyclic switching sequence
`3 → 2 → 1 → 3`, TeX 11977–11980): at the point `q` of the section `χ₂₃ = 0`, `e₁` is strictly
below `e₂`, and along the `e₃`-flow from `q`, `e₃` falls strictly below `e₂` right after `q` (so an
extremal through `q` can use neither `e₁` nor `e₃` next). These are the hypotheses `h0`, `h2` of
`IsChatteringArcInto.next_switchPoint_eq_reinPoincare`. -/
def SwitchEntersE2 (q : iso_PhasePt) : Prop :=
  phaseHam q (vertex 0) < phaseHam q (vertex 1) ∧
    ∃ ε > 0, ∀ t ∈ Ioo 0 ε,
      phaseHam (iso_vertexFlow 2 q t) (vertex 2) < phaseHam (iso_vertexFlow 2 q t) (vertex 1)

/-- **The `e₂`-arc from `q` switches to `e₁` at `t_sw(q)`** (TeX 11975–11980: "We check that the
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
(TeX 11982–11986: "a Reinhardt trajectory starting on the unstable curve reaches the boundary of the
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
happen, because the unstable curve hits the boundary of the star domain", TeX 12007–12008). For an
analytic extension `e` of the Reinhardt–Poincaré map at `(0, x̃_out)` (Lemma 14.3.1) there is a
neighborhood `U` of the fixed point such that the forward orbit of every point `p` of the local
unstable curve `W^u_loc(e, U)` with `r > 0` reaches the boundary of the star domain
(`ReachesStarBoundary (lieChart p)`). See the module docstring for the reading, the numerical check
and the certification plan. -/
def UnstableCurveLeavesStarDomain : Prop :=
  ∃ e : OpenPartialHomeomorph (ℝ × (Fin 3 → ℝ)) (ℝ × (Fin 3 → ℝ)),
    IsReinhardtPoincareExtension e ∧ ∃ U ∈ 𝓝 chartPtOut,
      ∀ p ∈ Function.localUnstableSet e chartPtOut U, 0 < p.1 → ReachesStarBoundary (lieChart p)

end SmoothedPolygons
