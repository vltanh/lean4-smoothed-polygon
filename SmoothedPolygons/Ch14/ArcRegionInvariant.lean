module

public import SmoothedPolygons.Ch14.ArcLocal

/-!
# Chapter 14, N4 from one single-step statement (INV) (Theorem 5.2)

`notes/n4/proof.md` §5.2. The numerical fact N4 (`UnstableCurveLeavesStarDomain`,
`SmoothedPolygons/Ch14/UnstableCurve.lean`: the global unstable curve over `q_out` reaches the
boundary of the star domain, Figure 14.2) follows from one statement about one step of the
Reinhardt–Poincaré map on the explicit region `𝒢*` (`arcRegion`):

> **(INV)** (`ArcRegionInvariant`) If `q ∈ 𝒢*` and `F(log Y) < 0` (the arc from `q` switches
> inside the star domain), then `F(q) ∈ 𝒢*`, or the arc from `F(q)` leaves the star domain
> before switching (`ArcLeavesStarDomain (F q)`).

**Departure from the paper.** The book computes the unstable curve in Mathematica and reads off
that it reaches the boundary of the star domain (Figure 14.2, TeX 11951–11991; the authors did not
certify it, TeX 11954–11957, REPORT.md E88). The formalization does not locate the curve: it
proves N4 from (INV) by the exact structure of the `e₂`-arcs (closed-form state, four-term
switching numerators, an explicit one-step map of four parameters, the telescoping of the radii;
`SmoothedPolygons/Ch14/ArcParams.lean` … `ArcLocal.lean`). (INV) itself is open; it replaces N4
as the named hypothesis of Mahler's First conjecture
(`theorem16_3_1_of_arcRegionInvariant`, `SmoothedPolygons/Ch16/MahlerFirstArcRegion.lean`).

## Statements

* `ArcRegionInvariant` (INV), with its status below.
* `ArcRegionInvariant.reachesStarBoundary`: under (INV), the forward orbit of every point of `𝒢*`
  reaches the boundary of the star domain (`ReachesStarBoundary`).
* **Theorem 5.2** (`unstableCurveLeavesStarDomain_of_arcRegionInvariant`): (INV) implies N4.

## Proofs (the route, proof.md Theorem 5.2)

1. `ArcRegionInvariant.reachesStarBoundary`, by strong induction on `⌊ρ₁(q)/r(q)⌋₊` (or on any
   natural number bounding `ρ₁(q)/(2 r(q))`). Let `q ∈ 𝒢*`; it has P1 and P4, so
   `SwitchEntersE2 q` (`switchEntersE2_of_arc`).
   * If `F(log Y) ≥ 0`: `ArcLeavesStarDomain q` (`arcLeavesStarDomain_of_arc`); take `K = 0`.
   * If `F(log Y) < 0`: `ArcSwitchesToE1 q` (`arcSwitchesToE1_of_arc`); `F q` is a section point
     with P1, P4, `r > 0` (`arc_propagation`), so `SwitchEntersE2 (F q)`. By (INV), either
     `ArcLeavesStarDomain (F q)` (take `K = 1`), or `F q ∈ 𝒢*`: then `r(F q) > r(q)`
     (`radius_lt_of_mem_arcRegion`) and `ρ₁(F q) = ρ₁(q) - 2 r(F q)` (`radius_reinPoincare`), so
     `ρ₁(F q)/r(F q) < ρ₁(q)/r(q) - 2`; by induction `ReachesStarBoundary (F q)` with some `K'`,
     and `ReachesStarBoundary q` with `K = K' + 1` (`Function.iterate_succ_apply`).
   This is the termination argument of Corollary 2.4: the radii increase and sum to less than
   `ρ₁(q₀)/2`, so the orbit has fewer than `ρ₁(q₀)/(2 r(q₀))` switching points.
2. Theorem 5.2: take `e` from `lemma14_3_1` and `U = V` from Lemma 5.1
   (`exists_nhds_lieChart_mem_arcRegion`). A point `p` of `Function.localUnstableSet e chartPtOut U`
   lies in `U` (its backward orbit starts at `p`), so for `r > 0`, `lieChart p ∈ 𝒢*`, and step 1
   gives `ReachesStarBoundary (lieChart p)`.

## Status of (INV) (the research notes, `notes/n4/proof.md` §5.2, §7)

* *In words*: on the region `𝒢*` of section points with `r > 0`, `f₀ > 0`, `q ≤ 0`, `p > 0` and
  `(Y - 1)(Y' - 2) ≤ Y - 2`, one step of the Reinhardt–Poincaré map either stays in `𝒢*` or lands
  on a point whose arc exits. P1, P4 and `r > 0` at `F(q)` hold automatically
  (`arc_propagation`); what remains is P2 (`q_new ≤ 0`) and E at `F(q)`, unless `F(q)` exits.
  By Theorem 2.1 (`arcParams_reinPoincare`) this is a statement about `(ε, Y, f₀, p)`, the
  switching root `τ_sw` of the four-term sum `f` (the zero of `F` in `(log y₊, log Y)`), and the
  root `q_new` of the quadric relation (2.1) at the new point that the phase point selects (along
  `W^u` the larger root, `notes/n4/nf.py`): four real variables, elementary functions, one
  transcendental root. E at the new point depends only on `(ε, Y, τ_sw)`.
* *Numerical evidence* (mpmath, 40–80 digits; not rigorous, not interval arithmetic):
  `notes/n4/region_star.py` sampled chart points with `r` log-uniform in `[10⁻⁶, 0.25]` and `x̃` in
  `x̃_out + [-1.5, 1.5] × [-6, 6] × [-2, 2]` and in a box three times larger: 845 points of `𝒢*`
  whose arc switches; every one of them, and every later point of its orbit, stayed in `𝒢*` until
  an exiting arc (1 to 7 steps). Without E (the region `𝒢`), the same held on samples of the whole
  section (`notes/n4/region_nf.py`: 297 switching points drawn in `(ε, Y, f₀, p)` with both roots
  of (2.1); `notes/n4/region_test.py`: 1,672). P2 is the condition that fails at images near the
  boundary (cusp arcs, `q_new > 0`), and those images always passed the exit test. Along `W^u`
  (`notes/n4/conditions.py`, 160 orbits of a fundamental domain) the margins are positive:
  `λ_lb ≥ 1.524`, `-q ≥ 1.06·10⁻³`, and near the divisor `-q/r² ≥ 9.617`. The threshold of
  `W^u` (`r* ≈ 0.0649`) is covered by Theorem 4.1 (`arcRegionInvariant_near_threshold`).
* *Research status*: open. No proof is known; the research (`notes/briefs/n4_research_report.md`)
  suggests looking for structure in `q_new` like the one that gave `f₀,new` and `p_new`, or a
  certificate (elementary functions only, as the Fuller certificates of Chapter 16, but on a
  four-dimensional region that is a cone near the divisor). (INV) is not weaker than N4: it
  concerns all of `𝒢*`, not only the unstable curve; the choice to name it instead of N4 is about
  form (a single explicit step, easier to state, test and certify), not strength. Points of `𝒢*`
  near the divisor with `x̃₂₁ > -1/√3` are excluded by E and were not studied.
-/

@[expose] public section

namespace SmoothedPolygons

open Set Filter Topology

/-- **(INV): the region `𝒢*` is invariant under the Reinhardt–Poincaré map until the exit**
(`notes/n4/proof.md` §5.2). For every point `q` of `𝒢*` (`arcRegion`: a section point with
`r > 0`, `f₀ > 0`, `q ≤ 0`, `p > 0`, `(Y - 1)(Y' - 2) ≤ Y - 2`) whose `e₂`-arc switches inside the
star domain (`F(log Y) < 0`), its image `F(q) = reinPoincare q` is again in `𝒢*`, or the `e₂`-arc
from `F(q)` leaves the star domain before switching. A single-step statement about an explicit map
of four real parameters (Theorem 2.1). Status: **open**; numerically true on 845 sampled switching
points of `𝒢*` and all their orbits (mpmath, not rigorous). See the module docstring. -/
def ArcRegionInvariant : Prop :=
  ∀ q ∈ arcRegion, (arcParams q).F (Real.log (arcY q)) < 0 →
    reinPoincare q ∈ arcRegion ∨ ArcLeavesStarDomain (reinPoincare q)

/-- Under (INV), the forward orbit of every point of `𝒢*` reaches the boundary of the star domain:
it switches cyclically for finitely many steps (the radii increase and sum to less than
`ρ₁(q)/2`) and then an arc exits. -/
theorem ArcRegionInvariant.reachesStarBoundary (h : ArcRegionInvariant) {q : iso_PhasePt}
    (hq : q ∈ arcRegion) : ReachesStarBoundary q := by
  sorry

/-- **Theorem 5.2** (proof.md §5.2): **(INV) implies N4**, the numerical fact behind
Theorem 14.4.1 (`UnstableCurveLeavesStarDomain`, Figure 14.2). Departure from the paper: the book
computes the unstable curve numerically; here N4 follows from (INV) by the exact structure of the
arcs, without locating the curve. -/
theorem unstableCurveLeavesStarDomain_of_arcRegionInvariant (h : ArcRegionInvariant) :
    UnstableCurveLeavesStarDomain := by
  sorry

end SmoothedPolygons
