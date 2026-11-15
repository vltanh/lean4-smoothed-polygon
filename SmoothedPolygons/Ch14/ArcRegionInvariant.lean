module

public import SmoothedPolygons.Ch14.ArcLocal
public import SmoothedPolygons.Ch14.ArcStepRegion

/-!
# Chapter 14, N4 from the single-step statement (INV) (Theorem 5.2), and (INV)

Part of the formalization's proof of N4 without computer assistance (a departure from the paper,
by the user's decision: the book reads N4 off the computed Figure 14.2; see below), and its last
step. N4
(`UnstableCurveLeavesStarDomain`, `SmoothedPolygons/Ch14/UnstableCurve.lean`: the global unstable
curve over `q_out` reaches the boundary of the star domain, Figure 14.2) follows from one statement
about one step of the Reinhardt–Poincaré map on the explicit region `𝒢*` (`arcRegion`):

> **(INV)** (`ArcRegionInvariant`) If `q ∈ 𝒢*` and `F(log Y) < 0` (the arc from `q` switches
> inside the star domain), then `F(q) ∈ 𝒢*`, or the arc from `F(q)` leaves the star domain
> before switching (`ArcLeavesStarDomain (F q)`).

**Departure from the paper**, by the user's decision. The book computes the unstable curve in
Mathematica and reads off that it reaches the boundary of the star domain (Figure 14.2,
TeX 11951–11991; the authors did not certify it, TeX 11952–11955, REPORT.md E88). The
formalization does not locate the curve: it proves N4 from (INV) by the exact structure of the
`e₂`-arcs (closed-form state, four-term switching numerators, an explicit one-step map of four
parameters, the telescoping of the radii; `SmoothedPolygons/Ch14/ArcParams.lean` …
`ArcLocal.lean`), and proves (INV) by explicit identities and inequalities
(`SmoothedPolygons/Ch14/ArcStepClosed.lean`, `ArcStepRegion.lean`, `ArcStepExit.lean`). So N4
holds (`unstableCurveLeavesStarDomain`), and with it Theorem 14.4.1 and Mahler's First conjecture
(`theorem14_4_1_unconditional`, `theorem16_3_1_unconditional`,
`SmoothedPolygons/Ch16/MahlerFirstArcRegion.lean`).

## The numbering of the steps

The N4 modules (all in `SmoothedPolygons/Ch14/`) number the steps of the proof as follows.

The reduction of N4 to (INV):
* §1, the `e₂`-arc. §1.1–§1.2: the frame, (1.1)–(1.3) and **Proposition 1.1** (the state along
  the arc, the exit time `T = ε log Y`), `ArcFrame.lean`. §1.3: **Lemma 1.2** (the nilpotent
  eigenvectors `V_e`, `V_f`) and the quadratures, `ArcCostate.lean`; **Theorem 1.3** (the
  four-term normal form) and (1.5) (`f₀` from the reduced Hamiltonian), `ArcNormalForm.lean`;
  (1.4), the normal form in the parameters, `ArcParams.lean`.
* §2, the map. §2.1, the quadric relation (2.1): `ArcRelation.lean`. §2.2, **Theorem 2.1** (the
  map in closed form), (2.2) (the radius) and **Corollary 2.4** (the telescoping of the radii):
  `ArcPoincareMap.lean`. **Lemma 2.3** (the Poisson brackets of the vertex Hamiltonians):
  `VertexPoissonBracket.lean`.
* §3, one arc: **Lemmas 3.1–3.3** on the parameters, `ArcParams.lean`; **Proposition 3.4** and the
  expansion bound (3.1), `ArcConditions.lean`.
* §5, the region: `𝒢*` (§5.2, `ArcConditions.lean`), **Lemma 5.1** (`ArcLocal.lean`) and
  **Theorem 5.2** ((INV) implies N4, this file).

The proof of (INV), whose items carry the prefix INV (INV §1–§7 are the proofs of INV Theorem 1,
INV Propositions 2–5, INV Lemma 6 and INV Theorem 2, in that order):
* **INV Theorem 1** (the map in closed form, `q_new` included), with its formulas INV (1.1)–(1.5)
  and **INV Corollary 1.2** (E at the image): `ArcStepClosed.lean`, `ArcCostate.lean` (INV (1.4),
  the costate in a moving eigenbasis) and `ArcPoincareMap.lean` (at the phase point);
* **INV Proposition 2** (`R = Y²ε⁴R̃`, the form INV (2.2) of the relation) and INV Corollary 2.1
  (the relation as a budget, INV (2.3)): `ArcStepClosed.lean`, `ArcStepRegion.lean`;
* **INV Propositions 3 and 4**: `ArcStepRegion.lean`; **INV Proposition 5** and **INV Lemma 6**:
  `ArcStepExit.lean` (and `ArcConditions.lean` for Lemma 6 on the flow);
* **INV Theorem 2** ((INV) in a sharp form): this file.

## Statements

* `ArcRegionInvariant` (INV).
* `ArcRegionInvariant.reachesStarBoundary`: under (INV), the forward orbit of every point of `𝒢*`
  reaches the boundary of the star domain (`ReachesStarBoundary`).
* **Theorem 5.2** (`unstableCurveLeavesStarDomain_of_arcRegionInvariant`): (INV) implies N4.
* **INV Theorem 2** (`arcRegionInvariant_sharp`, (INV) in a sharper form): for `q ∈ 𝒢*` with
  `F(log Y) < 0` and `s = e^{τ_sw}`, `F(q)` is a section point with `r > 0`, P1, P4,
  `SwitchEntersE2`, and `f₀ ≥ q (1 - 1/Y)` at `F(q)`; if `ψ(s) ≥ 0` then `F(q) ∈ 𝒢*`; if
  `ψ(s) < 0` then `Y(F q) ≥ 16/5` and the arc from `F(q)` exits (`ArcLeavesStarDomain`).
* `arcRegionInvariant : ArcRegionInvariant` ((INV), from the sharp form).
* `unstableCurveLeavesStarDomain : UnstableCurveLeavesStarDomain` (N4, unconditionally; a term).

## Proofs (the route, Theorem 5.2)

1. `ArcRegionInvariant.reachesStarBoundary`, by induction on a natural number `n > ρ₁(q)/r(q)`
   (`n4h_reach`: the statement for all `q ∈ 𝒢*` with `ρ₁(q)/r(q) < n`). Let `q ∈ 𝒢*`; it has P1
   and P4, so `SwitchEntersE2 q` (`switchEntersE2_of_arc`).
   * If `F(log Y) ≥ 0`: `ArcLeavesStarDomain q` (`arcLeavesStarDomain_of_arc`); take `K = 0`.
   * If `F(log Y) < 0`: `ArcSwitchesToE1 q` (`arcSwitchesToE1_of_arc`); `F q` is a section point
     with P1, P4, `r > 0` (`arc_propagation`), so `SwitchEntersE2 (F q)`. By (INV), either
     `ArcLeavesStarDomain (F q)` (take `K = 1`), or `F q ∈ 𝒢*`: then `r(F q) > r(q)`
     (`radius_lt_of_mem_arcRegion`) and `ρ₁(F q) = ρ₁(q) - 2 r(F q)` (`radius_reinPoincare`), so
     `ρ₁(F q)/r(F q) < ρ₁(q)/r(q) - 2`, so `F q` satisfies the bound `n - 1`; by induction
     `ReachesStarBoundary (F q)` with some `K'`,
     and `ReachesStarBoundary q` with `K = K' + 1` (`Function.iterate_succ_apply`).
   This is the termination argument of Corollary 2.4: the radii increase and sum to less than
   `ρ₁(q₀)/2`, so the orbit has fewer than `ρ₁(q₀)/(2 r(q₀))` switching points.
2. Theorem 5.2: take `e` from `lemma14_3_1` and `U = V` from Lemma 5.1
   (`exists_nhds_lieChart_mem_arcRegion`). A point `p` of `Function.localUnstableSet e chartPtOut U`
   lies in `U` (its backward orbit starts at `p`), so for `r > 0`, `lieChart p ∈ 𝒢*`, and step 1
   gives `ReachesStarBoundary (lieChart p)`.
3. `arcRegionInvariant_sharp` (INV §7, the proof of INV Theorem 2): see its docstring; it
   assembles INV Theorem 1 (`ArcParams.step_closed`, `arcQ_reinPoincare`), INV Proposition 2
   (`ArcParams.rel_eq`), INV Corollary 1.2 (`ArcParams.E_new_iff`), INV Propositions 3–5
   (`ArcParams.Phi_nonpos`, `ArcParams.YNew_ge`, `ArcParams.qNew_le_f0New`) and INV Lemma 6
   (`arcLeavesStarDomain_of_Y_ge`) with Proposition 3.4 (`switchesBeforeExit_of_arc`,
   `arc_propagation`, `switchEntersE2_of_arc`).
4. `arcRegionInvariant`: the two cases of the sharp form.
5. `unstableCurveLeavesStarDomain`: Theorem 5.2 applied to `arcRegionInvariant` (a term).

## (INV)

* *In words*: on the region `𝒢*` of section points with `r > 0`, `f₀ > 0`, `q ≤ 0`, `p > 0` and
  `(Y - 1)(Y' - 2) ≤ Y - 2`, one step of the Reinhardt–Poincaré map either stays in `𝒢*` or lands
  on a point whose arc exits. P1, P4 and `r > 0` at `F(q)` hold automatically
  (`arc_propagation`); what remains is P2 (`q_new ≤ 0`) and E at `F(q)`, unless `F(q)` exits.
* *Proved*: `arcRegionInvariant`, from `arcRegionInvariant_sharp`, with the real-number lemmas of
  `ArcStepClosed.lean`, `ArcStepRegion.lean`, `ArcStepExit.lean` and the flow lemmas
  `arcQ_reinPoincare` (`ArcPoincareMap.lean`) and `arcLeavesStarDomain_of_Y_ge`
  (`ArcConditions.lean`). (The argument was confirmed by an independent review, which re-derived
  INV Theorem 1, recomputed the three Bernstein certificates and assembled (INV) in Lean from these
  statements before they were proved.) The proof uses no computer: every step is a polynomial
  identity, a finite list of nonnegative rationals, an inequality for the logarithm
  (`log s ≥ 2(s - 1)/(s + 1)`, `log(16/5) > 297/256`, `log t ≥ 1 - 1/t`, `log t ≤ sinh(log t)`),
  or elementary calculus (the intermediate value theorem, and monotonicity from the sign of a
  derivative in Lemmas 3.1–3.2; the intermediate value theorem in INV Proposition 4). Three facts
  make it work:
  1. `q_new` is explicit, `q_new = Φ(s)/(Y - s)²` with `s = e^{τ_sw}` (INV Theorem 1: the costate
     has constant coefficients in a moving eigenbasis, INV (1.4)); no root of (2.1) is chosen
     (along `W^u` it is the larger root, but not in general, see
     `SmoothedPolygons/Ch14/ArcPoincareMap.lean`).
  2. The relation is a budget: `R = Y²ε⁴R̃` and `R̃ = 0` reads
     `2(YY' - 1)(Y' - 2)(-q) = [Y'(f₀ - q) - Yp]² + 4p(-q) + 2(YY' - 1)(Y - 2)p
     + 2Y'(3 - (Y - 2)(Y' - 2)) f₀`: on `𝒢*` every term on the right is `≥ 0`.
  3. A dichotomy by E at the image, the cubic inequality `ψ(s) ≥ 0`: if it holds the image is in
     `𝒢*` (INV Proposition 3); if not, `Y_new ≥ 16/5`, beyond the root `Y_* = 3.16258` of
     `g(Y) = Y log Y - (Y - 1) - (Y - 1)²/Y`, and the next arc exits (INV Proposition 5, INV
     Lemma 6).
* *Numerical evidence* (not part of the proof): samples of 845 switching points of `𝒢*` and
  their orbits; of 35,418 points of `𝒢*` (34,921 switching), checking every hypothesis and
  conclusion of INV Propositions 3–5 and INV Theorem 2; of 12,900 points (no failure; the least
  `Y_new` where `ψ < 0` is `3.287 ≥ 16/5`); and of 2,588 chart points (every orbit exits after at
  most 7 switching arcs). Along `W^u`, from the point with `r = 10⁻⁶`, the orbit has seven
  switching arcs; at the seventh
  `ψ(s) = -19.5`, `Y_new = 38.2`, and the next arc exits.
* (INV) is not weaker than N4: it concerns all of `𝒢*`, not only the unstable curve.
-/

@[expose] public section

namespace SmoothedPolygons

open Set Filter Topology

/-- **(INV): the region `𝒢*` is invariant under the Reinhardt–Poincaré map until the exit**
(§5.2). For every point `q` of `𝒢*` (`arcRegion`: a section point with
`r > 0`, `f₀ > 0`, `q ≤ 0`, `p > 0`, `(Y - 1)(Y' - 2) ≤ Y - 2`) whose `e₂`-arc switches inside the
star domain (`F(log Y) < 0`), its image `F(q) = reinPoincare q` is again in `𝒢*`, or the `e₂`-arc
from `F(q)` leaves the star domain before switching. A single-step statement about an explicit map
of four real parameters (Theorem 2.1). It is proved: `arcRegionInvariant` (INV Theorem 2), from
`arcRegionInvariant_sharp`. See the module docstring. -/
def ArcRegionInvariant : Prop :=
  ∀ q ∈ arcRegion, (arcParams q).F (Real.log (arcY q)) < 0 →
    reinPoincare q ∈ arcRegion ∨ ArcLeavesStarDomain (reinPoincare q)

/-- The induction of `ArcRegionInvariant.reachesStarBoundary` (Corollary 2.4): every
point of `𝒢*` with `ρ₁(q)/r(q) < n` reaches the boundary of the star domain. -/
private theorem n4h_reach (h : ArcRegionInvariant) :
    ∀ n : ℕ, ∀ q ∈ arcRegion, ρ₁ q.1 / q.1 0 0 < n → ReachesStarBoundary q := by
  intro n
  induction n with
  | zero =>
    intro q hq hn
    obtain ⟨hs, hr, -⟩ := hq
    have : 0 < ρ₁ q.1 / q.1 0 0 := div_pos hs.2.2.2.2.1 hr
    simp only [Nat.cast_zero] at hn
    linarith
  | succ n ih =>
    intro q hq hn
    have hq' := hq
    obtain ⟨hs, hr, h1, h2, h4, -⟩ := hq'
    have hE2 : SwitchEntersE2 q := switchEntersE2_of_arc hs h1 h4
    by_cases hF : (arcParams q).F (Real.log (arcY q)) < 0
    · have hsw := arcSwitchesToE1_of_arc hs hr h1 h2 h4 hF
      obtain ⟨hFs, hF1, hF4, -, hFr, -⟩ := arc_propagation hs hr h1 h2 h4 hF
      have hFE2 : SwitchEntersE2 (reinPoincare q) := switchEntersE2_of_arc hFs hF1 hF4
      rcases h q hq hF with hin | hout
      · have hlt := radius_lt_of_mem_arcRegion hq hF
        have hrad := (radius_reinPoincare hs (switchesBeforeExit_of_arc hs h1 h2 hF).1).1
        have hρ : 0 < ρ₁ q.1 := hs.2.2.2.2.1
        have hm : ρ₁ (reinPoincare q).1 / (reinPoincare q).1 0 0 < n := by
          have e1 : ρ₁ (reinPoincare q).1 = ρ₁ q.1 - 2 * (reinPoincare q).1 0 0 := by linarith
          have h3 : ρ₁ q.1 / (reinPoincare q).1 0 0 < ρ₁ q.1 / q.1 0 0 := by
            rw [div_lt_div_iff₀ hFr hr]; nlinarith
          rw [e1, sub_div, mul_div_assoc, div_self hFr.ne', mul_one]
          push_cast at hn
          linarith
        obtain ⟨K, hK1, hK2, hK3⟩ := ih _ hin hm
        refine ⟨K + 1, ?_, ?_, ?_⟩
        · intro j hj
          rcases j with _ | j
          · simpa using hE2
          · rw [Function.iterate_succ_apply]; exact hK1 j (by omega)
        · intro j hj
          rcases j with _ | j
          · simpa using hsw
          · rw [Function.iterate_succ_apply]; exact hK2 j (by omega)
        · rw [Function.iterate_succ_apply]; exact hK3
      · refine ⟨1, ?_, ?_, ?_⟩
        · intro j hj
          interval_cases j
          · simpa using hE2
          · simpa using hFE2
        · intro j hj
          interval_cases j
          simpa using hsw
        · simpa using hout
    · refine ⟨0, ?_, ?_, ?_⟩
      · intro j hj
        interval_cases j
        simpa using hE2
      · intro j hj
        omega
      · simpa using arcLeavesStarDomain_of_arc hs hr h1 h2 h4 (not_lt.1 hF)

/-- Under (INV), the forward orbit of every point of `𝒢*` reaches the boundary of the star domain:
it switches cyclically for finitely many steps (the radii increase and sum to less than
`ρ₁(q)/2`) and then an arc exits. -/
theorem ArcRegionInvariant.reachesStarBoundary (h : ArcRegionInvariant) {q : iso_PhasePt}
    (hq : q ∈ arcRegion) : ReachesStarBoundary q := by
  obtain ⟨n, hn⟩ := exists_nat_gt (ρ₁ q.1 / q.1 0 0)
  exact n4h_reach h n q hq hn

/-- **Theorem 5.2** (§5.2): **(INV) implies N4** (`fig:unstable-curve`), the numerical fact behind
Theorem 14.4.1 (`UnstableCurveLeavesStarDomain`, Figure 14.2). Departure from the paper (the
user's decision): the book computes the unstable curve numerically; here N4 follows from (INV) by
the exact structure of the arcs, without locating the curve. -/
theorem unstableCurveLeavesStarDomain_of_arcRegionInvariant (h : ArcRegionInvariant) :
    UnstableCurveLeavesStarDomain := by
  obtain ⟨e, he⟩ := lemma14_3_1
  obtain ⟨V, hV, hVr⟩ := exists_nhds_lieChart_mem_arcRegion
  refine ⟨e, he, V, hV, fun p hp hp1 => ?_⟩
  obtain ⟨y, hy0, hy, -⟩ := hp
  have hpV : p ∈ V := hy0 ▸ (hy 0).1
  obtain ⟨n, hn⟩ := exists_nat_gt (ρ₁ (lieChart p).1 / (lieChart p).1 0 0)
  exact n4h_reach h n _ (hVr p hpV hp1) hn

/-- **(INV), sharp form** (INV Theorem 2). Let `q ∈ 𝒢*` with `F(log Y) < 0` (the
arc switches inside the star domain) and `s = e^{τ_sw}`. Then `F(q) = reinPoincare q` is a section
point with `r > 0`, P1 and P4 (so `SwitchEntersE2 (F q)`), and `f₀ ≥ q (1 - 1/Y)` at `F(q)`
(INV Proposition 5); moreover
* if `ψ(s) ≥ 0` (`ArcParams.psiE`), then `F(q) ∈ 𝒢*`;
* if `ψ(s) < 0`, then `Y(F q) ≥ 16/5` and the arc from `F(q)` leaves the star domain before
  switching.
Consequently, `F(q)`'s arc exits whenever `Y_new ≥ 16/5`, and `F(q) ∈ 𝒢*` whenever
`Y_new < 16/5` (the two cases of `ψ(s)` overlap in `Y_new`, so this is not an equivalence).

Route (INV §7). Write `a = arcParams q`, `s = e^{τ_sw}`.
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
6. INV Proposition 5 (`ArcParams.qNew_le_f0New`, with `Y - 2 ≥ 0`, `Y' - 2 ≥ 0`): the inequality
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
  obtain ⟨hs, hr, h1, h2, h4, hE⟩ := hq
  set a := arcParams q with ha_def
  have hsw := (switchesBeforeExit_of_arc hs h1 h2 hF).1
  obtain ⟨-, hpar⟩ := arcParams_reinPoincare hs hsw
  have hQ := arcQ_reinPoincare hs hsw
  obtain ⟨hFs, hF1, hF4, -, hFr, -⟩ := arc_propagation hs hr h1 h2 h4 hF
  have hSE := switchEntersE2_of_arc hFs hF1 hF4
  have he : 0 < a.eps := arcEps_pos hs.2
  have hY1 : 1 < a.Y := one_lt_arcY hs.2
  have hY' : a.Y' = arcY' q := arcParams_Y' hs.2
  have hg0 : a.g0 = 0 := arcG0_eq_zero hs
  have hrad : a.radius = q.1 0 0 := arcParams_radius hs.2
  have hb : 0 < a.Y' - 2 := by
    have h0 : 0 < a.radius := by rw [hrad]; exact hr
    simp only [ArcParams.radius] at h0
    by_contra hh
    have : a.eps * (a.Y' - 2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos he.le (not_lt.1 hh)
    linarith
  have hE' : (a.Y - 1) * (a.Y' - 2) ≤ a.Y - 2 := by rw [hY']; exact hE
  have ha : 0 < a.Y - 2 := by nlinarith
  have hR : a.relT = 0 := by
    have h0 := a.rel_eq he.ne' (by linarith)
    rw [arcParams_rel hs] at h0
    have : a.Y ^ 2 * a.eps ^ 4 ≠ 0 := by positivity
    exact (mul_eq_zero.1 h0.symm).resolve_left this
  obtain ⟨hsY1, hs1, hsY, hpi, hFs0⟩ := a.exp_tauSw_spec h1 h2 hY1.le hF
  set s := Real.exp a.tauSw with hs_def
  obtain ⟨hcY, hcY', hcf, -⟩ := a.step_closed he hY1 hg0 h1 h2 hF (arcQ (reinPoincare q))
  have hYn : arcY (reinPoincare q) = a.YNew s := (congrArg ArcParams.Y hpar).trans hcY
  have hYn' : arcY' (reinPoincare q) = a.YNew' s :=
    (arcParams_Y' hFs.2).symm.trans ((congrArg ArcParams.Y' hpar).trans hcY')
  have hfn : arcF0 (reinPoincare q) = a.f0New s := (congrArg ArcParams.f0 hpar).trans hcf
  have h5 := a.qNew_le_f0New ha.le hb.le h1.le h2 h4.le hs1 hsY1.le hsY hFs0
  have h5' : arcQ (reinPoincare q) * (1 - 1 / arcY (reinPoincare q)) ≤ arcF0 (reinPoincare q) := by
    rw [hQ, hYn, hfn]; exact h5
  refine ⟨hFs, hFr, hF1, hF4, hSE, h5', fun hpsi ↦ ?_, fun hpsi ↦ ?_⟩
  · refine ⟨hFs, hFr, hF1, ?_, hF4, ?_⟩
    · rw [hQ]
      exact div_nonpos_of_nonpos_of_nonneg
        (a.Phi_nonpos ha hb hE' h2 h4.le hR hsY1.le hsY hpi.le hpsi) (sq_nonneg _)
    · rw [hYn, hYn']
      exact (a.E_new_iff hsY.ne).2 hpsi
  · have hYge := a.YNew_ge (by linarith) (by linarith) hsY1.le hsY hpsi
    exact ⟨hYn ▸ hYge, arcLeavesStarDomain_of_Y_ge hFs hFr hF1 hF4 (hYn ▸ hYge) h5'⟩

/-- **(INV)** (INV Theorem 2): the region `𝒢*` is invariant under the
Reinhardt–Poincaré map until the exit. From the sharp form `arcRegionInvariant_sharp`, by cases on
the sign of `ψ(s)`. -/
theorem arcRegionInvariant : ArcRegionInvariant := by
  intro q hq hF
  obtain ⟨-, -, -, -, -, -, hin, hout⟩ := arcRegionInvariant_sharp hq hF
  by_cases h : 0 ≤ (arcParams q).psiE (Real.exp (arcParams q).tauSw)
  · exact Or.inl (hin h)
  · exact Or.inr (hout (not_le.1 h)).2

/-- **N4, unconditionally** (`fig:unstable-curve`): the unstable curve `W^u(q_out)` reaches the
boundary of the star domain (Figure 14.2; the numerical fact behind Theorem 14.4.1). Theorem 5.2
applied to (INV) (`arcRegionInvariant`). Departure from the paper (the user's decision): the book
computes the unstable curve numerically (TeX 11951–11991); here N4 is proved without computer
assistance, from the exact structure of the arcs and the proof of (INV). -/
theorem unstableCurveLeavesStarDomain : UnstableCurveLeavesStarDomain :=
  unstableCurveLeavesStarDomain_of_arcRegionInvariant arcRegionInvariant

end SmoothedPolygons
