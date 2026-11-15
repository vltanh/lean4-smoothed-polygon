module

public import SmoothedPolygons.Ch14.ArcLocal
public import SmoothedPolygons.Ch14.ArcStepRegion

/-!
# Chapter 14, N4 from the single-step statement (INV) (Theorem 5.2), and (INV)

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
`SmoothedPolygons/Ch14/ArcParams.lean` … `ArcLocal.lean`), and proves (INV) by explicit identities
and inequalities (`notes/inv/inv.md`; `SmoothedPolygons/Ch14/ArcStepClosed.lean`,
`ArcStepRegion.lean`, `ArcStepExit.lean`). So N4 holds (`unstableCurveLeavesStarDomain`), and with
it Mahler's First conjecture (`theorem16_3_1_unconditional`,
`SmoothedPolygons/Ch16/MahlerFirstArcRegion.lean`).

## Statements

* `ArcRegionInvariant` (INV), with its status below.
* `ArcRegionInvariant.reachesStarBoundary`: under (INV), the forward orbit of every point of `𝒢*`
  reaches the boundary of the star domain (`ReachesStarBoundary`).
* **Theorem 5.2** (`unstableCurveLeavesStarDomain_of_arcRegionInvariant`): (INV) implies N4.
* **inv.md Theorem 2** (`arcRegionInvariant_sharp`, (INV) in a sharper form): for `q ∈ 𝒢*` with
  `F(log Y) < 0` and `s = e^{τ_sw}`, `F(q)` is a section point with `r > 0`, P1, P4,
  `SwitchEntersE2`, and `f₀ ≥ q (1 - 1/Y)` at `F(q)`; if `ψ(s) ≥ 0` then `F(q) ∈ 𝒢*`; if
  `ψ(s) < 0` then `Y(F q) ≥ 16/5` and the arc from `F(q)` exits (`ArcLeavesStarDomain`).
* `arcRegionInvariant : ArcRegionInvariant` ((INV), from the sharp form; proved below from it).
* `unstableCurveLeavesStarDomain : UnstableCurveLeavesStarDomain` (N4, unconditionally; a term).

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
   gives `ReachesStarBoundary (lieChart p)`. (Steps 1–2 are written out and compile in
   `notes/n4rev/Thm52Check.lean`.)
3. `arcRegionInvariant_sharp` (inv.md §7, the proof of Theorem 2): see its docstring; it assembles
   Theorem 1 (`ArcParams.step_closed`, `arcQ_reinPoincare`), Proposition 2 (`ArcParams.rel_eq`),
   Corollary 1.2 (`ArcParams.E_new_iff`), Propositions 3–5 (`ArcParams.Phi_nonpos`,
   `ArcParams.YNew_ge`, `ArcParams.qNew_le_f0New`) and Lemma 6 (`arcLeavesStarDomain_of_Y_ge`) with
   Proposition 3.4 (`switchesBeforeExit_of_arc`, `arc_propagation`, `switchEntersE2_of_arc`).
4. `arcRegionInvariant`: the two cases of the sharp form (proved below).
5. `unstableCurveLeavesStarDomain`: Theorem 5.2 applied to `arcRegionInvariant` (a term).

## Status of (INV)

* *In words*: on the region `𝒢*` of section points with `r > 0`, `f₀ > 0`, `q ≤ 0`, `p > 0` and
  `(Y - 1)(Y' - 2) ≤ Y - 2`, one step of the Reinhardt–Poincaré map either stays in `𝒢*` or lands
  on a point whose arc exits. P1, P4 and `r > 0` at `F(q)` hold automatically
  (`arc_propagation`); what remains is P2 (`q_new ≤ 0`) and E at `F(q)`, unless `F(q)` exits.
* *Proved* (research round 2, `notes/inv/inv.md` Theorem 2; confirmed by the independent review,
  `notes/briefs/n4_review_report.md`, which re-derived Theorem 1, recomputed all three Bernstein
  certificates and assembled (INV) in Lean from the statements now in this library,
  `notes/n4rev/InvAssemblyCheck.lean`). **The Lean proof is in progress**: the statements are here
  and in `ArcStepClosed.lean`, `ArcStepRegion.lean`, `ArcStepExit.lean`, `ArcPoincareMap.lean`
  (`arcQ_reinPoincare`), `ArcConditions.lean` (`arcLeavesStarDomain_of_Y_ge`), with `sorry`. The
  proof uses no computer: every step is a polynomial identity, a finite list of nonnegative
  rationals, `log s ≥ 2(s - 1)/(s + 1)` or `log(16/5) > 297/256`. Three facts make it work:
  1. `q_new` is explicit, `q_new = Φ(s)/(Y - s)²` with `s = e^{τ_sw}` (Theorem 1: the costate has
     constant coefficients in a moving eigenbasis, (1.4)); no root of (2.1) is chosen (along `W^u`
     it is the larger root, but not in general, see `SmoothedPolygons/Ch14/ArcPoincareMap.lean`).
  2. The relation is a budget: `R = Y²ε⁴R̃` and `R̃ = 0` reads
     `2(YY' - 1)(Y' - 2)(-q) = [Y'(f₀ - q) - Yp]² + 4p(-q) + 2(YY' - 1)(Y - 2)p
     + 2Y'(3 - (Y - 2)(Y' - 2)) f₀`: on `𝒢*` every term on the right is `≥ 0`.
  3. A dichotomy by E at the image, the cubic inequality `ψ(s) ≥ 0`: if it holds the image is in
     `𝒢*` (Proposition 3); if not, `Y_new ≥ 16/5`, beyond the root `Y_* = 3.16258` of
     `g(Y) = Y log Y - (Y - 1) - (Y - 1)²/Y`, and the next arc exits (Proposition 5, Lemma 6).
* *Numerical evidence* (not part of the proof): `notes/n4/region_star.py` (845 switching points of
  `𝒢*` and their orbits, round 1), `notes/inv/crosscheck.py` (35,418 points of `𝒢*`, 34,921
  switching; every hypothesis and conclusion of Propositions 3–5 and Theorem 2), the review's
  `notes/n4rev/t9_inv_sample.py` (12,900 points, 0 failures; the least `Y_new` where `ψ < 0` is
  `3.287 ≥ 16/5`) and `t11_chart_orbits.py` (2,588 chart points: every orbit exits after at most 7
  switching arcs). Along `W^u` the orbit has seven switching arcs; at the seventh `ψ(s) = -19.5`,
  `Y_new = 38.2`, and the next arc exits.
* (INV) is not weaker than N4: it concerns all of `𝒢*`, not only the unstable curve.
-/

@[expose] public section

namespace SmoothedPolygons

open Set Filter Topology

/-- **(INV): the region `𝒢*` is invariant under the Reinhardt–Poincaré map until the exit**
(`notes/n4/proof.md` §5.2). For every point `q` of `𝒢*` (`arcRegion`: a section point with
`r > 0`, `f₀ > 0`, `q ≤ 0`, `p > 0`, `(Y - 1)(Y' - 2) ≤ Y - 2`) whose `e₂`-arc switches inside the
star domain (`F(log Y) < 0`), its image `F(q) = reinPoincare q` is again in `𝒢*`, or the `e₂`-arc
from `F(q)` leaves the star domain before switching. A single-step statement about an explicit map
of four real parameters (Theorem 2.1). Status: **proved** in `notes/inv/inv.md` (Theorem 2;
confirmed by the review, `notes/briefs/n4_review_report.md`); Lean proof in progress
(`arcRegionInvariant`, from `arcRegionInvariant_sharp`). See the module docstring. -/
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

/-- **(INV), sharp form** (`notes/inv/inv.md` Theorem 2). Let `q ∈ 𝒢*` with `F(log Y) < 0` (the
arc switches inside the star domain) and `s = e^{τ_sw}`. Then `F(q) = reinPoincare q` is a section
point with `r > 0`, P1 and P4 (so `SwitchEntersE2 (F q)`), and `f₀ ≥ q (1 - 1/Y)` at `F(q)`
(Proposition 5); moreover
* if `ψ(s) ≥ 0` (`ArcParams.psiE`), then `F(q) ∈ 𝒢*`;
* if `ψ(s) < 0`, then `Y(F q) ≥ 16/5` and the arc from `F(q)` leaves the star domain before
  switching.
Equivalently, `F(q)`'s arc exits whenever `Y_new ≥ 16/5`, and `F(q) ∈ 𝒢*` whenever `Y_new < 16/5`.

Route (inv.md §7; the Lean assembly is `rv_arcRegionInvariant` of
`notes/n4rev/InvAssemblyCheck.lean`, which compiles against these statements up to the forms of
the hypotheses). Write `a = arcParams q`, `s = e^{τ_sw}`.
1. From `q ∈ 𝒢*`: a section point, `r > 0`, P1, P2, P4, E. `switchesBeforeExit_of_arc`:
   `SwitchesBeforeExit q`. `arc_propagation`: `F q` is a section point with P1, P4, `r(F q) > 0`;
   `switchEntersE2_of_arc` at `F q`.
2. `ε > 0` (`arcEps_pos`), `Y > 1` (`one_lt_arcY`), `a.Y' = arcY' q` (`arcParams_Y'`), `g₀ = 0`
   (`arcG0_eq_zero`), `a.radius = r` (`arcParams_radius`), so `Y' - 2 > 0` (`r = ε(Y' - 2)/2`),
   and E gives `Y - 2 > 0`.
3. `R̃ = 0`: `ArcParams.rel_eq` and `arcParams_rel` (`Y² ε⁴ ≠ 0`).
4. `ArcParams.exp_tauSw_spec`: `Y - 1 < s`, `1 < s < Y`, `π(s) > 0`, `F(log s) = 0`.
5. The image in closed form: `arcParams_reinPoincare` (`arcParams (F q) = a.step (arcQ (F q))`)
   and `ArcParams.step_closed` give `arcY (F q) = Y_new(s)`, `arcY' (F q) = Y'_new(s)`
   (`arcParams_Y'` at `F q`), `arcF0 (F q) = f₀,new(s)`; `arcQ_reinPoincare` gives
   `arcQ (F q) = q_new(s)`.
6. Proposition 5 (`ArcParams.qNew_le_f0New`, with `Y - 2 ≥ 0`, `Y' - 2 ≥ 0`): the inequality
   `f₀ ≥ q (1 - 1/Y)` at `F q`.
7. If `ψ(s) ≥ 0`: `ArcParams.Phi_nonpos` gives `Φ(s) ≤ 0`, so `q_new = Φ(s)/(Y - s)² ≤ 0`
   (`div_nonpos_of_nonpos_of_nonneg`); `ArcParams.E_new_iff` gives E at `F q`; with step 1,
   `F q ∈ 𝒢*`.
8. If `ψ(s) < 0`: `ArcParams.YNew_ge` gives `Y(F q) ≥ 16/5`; `arcLeavesStarDomain_of_Y_ge` at `F q`
   (section point, `r > 0`, P1, P4 by step 1; the inequality by step 6). -/
theorem arcRegionInvariant_sharp {q : iso_PhasePt} (hq : q ∈ arcRegion)
    (hF : (arcParams q).F (Real.log (arcY q)) < 0) :
    IsArcSectionPt (reinPoincare q) ∧ 0 < (reinPoincare q).1 0 0 ∧
      0 < arcF0 (reinPoincare q) ∧ 0 < arcP (reinPoincare q) ∧ SwitchEntersE2 (reinPoincare q) ∧
      arcQ (reinPoincare q) * (1 - 1 / arcY (reinPoincare q)) ≤ arcF0 (reinPoincare q) ∧
      (0 ≤ (arcParams q).psiE (Real.exp (arcParams q).tauSw) → reinPoincare q ∈ arcRegion) ∧
      ((arcParams q).psiE (Real.exp (arcParams q).tauSw) < 0 →
        16 / 5 ≤ arcY (reinPoincare q) ∧ ArcLeavesStarDomain (reinPoincare q)) := by
  sorry

/-- **(INV)** (`notes/inv/inv.md` Theorem 2): the region `𝒢*` is invariant under the
Reinhardt–Poincaré map until the exit. From the sharp form `arcRegionInvariant_sharp`, by cases on
the sign of `ψ(s)`. -/
theorem arcRegionInvariant : ArcRegionInvariant := by
  intro q hq hF
  obtain ⟨-, -, -, -, -, -, hin, hout⟩ := arcRegionInvariant_sharp hq hF
  by_cases h : 0 ≤ (arcParams q).psiE (Real.exp (arcParams q).tauSw)
  · exact Or.inl (hin h)
  · exact Or.inr (hout (not_le.1 h)).2

/-- **N4, unconditionally**: the unstable curve `W^u(q_out)` reaches the boundary of the star
domain (Figure 14.2; the numerical fact behind Theorem 14.4.1). Theorem 5.2 applied to (INV).
Departure from the paper: the book computes the unstable curve numerically (TeX 11951–11991);
here N4 is proved, from the exact structure of the arcs and the proof of (INV) in
`notes/inv/inv.md`. -/
theorem unstableCurveLeavesStarDomain : UnstableCurveLeavesStarDomain :=
  unstableCurveLeavesStarDomain_of_arcRegionInvariant arcRegionInvariant

end SmoothedPolygons
