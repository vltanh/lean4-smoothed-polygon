module

public import SmoothedPolygons.Ch14.ArcLocal
public import SmoothedPolygons.Ch14.ArcStepRegion

/-!
# Chapter 14, the unstable curve: Theorem A from the one-step statement (INV), and (INV)

The last step of the formalization's proof, without computer assistance, of the fact behind
Figure 14.2 (N4, `UnstableCurveLeavesStarDomain`, `SmoothedPolygons/Ch14/UnstableCurve.lean`: the
unstable curve over `q_out` reaches the boundary of the star domain). **Departure from the paper**,
by the user's decision: the book reads the fact off a Mathematica computation (Figure 14.2,
TeX 11951–11991; the authors did not certify it, TeX 11952–11955; REPORT.md E88). The proof does
not locate the curve. It is written up for the book's authors in `docs/unstable-curve.pdf` (the
note), whose numbering the N4 modules use. The fact follows from one statement about one step of
the Reinhardt–Poincaré map on an explicit region `𝒢*` of the section (`arcRegion`):

> **(INV)** (`ArcRegionInvariant`) If `q ∈ 𝒢*` and `F(log Y) < 0` (the arc from `q` switches
> inside the star domain), then `F(q) ∈ 𝒢*`, or the `e₂`-arc from `F(q)` leaves the star domain
> before switching (`ArcLeavesStarDomain (F q)`).

## Where the steps of the note are

The note uses the book's notation, and these modules use their own names. The note's section
`N_{9/4}` is `IsArcSectionPt`, and its points `q` are phase points. Its numbers `ρ₁`, `μ₂`, `μ₀`,
`k₁`, `k₂`, `k₃` are `arcEps`, `arcY`, `arcY'`, `arcF0`, `arcQ`, `arcP` (the fields `eps`, `Y`,
`Y'`, `f0`, `q`, `p` of `ArcParams`). Its eigenvectors `E₊`, `E₋` are `arcVe`, `arcVf`; its time
`ϑ = t/ρ₁` is `τ`; its switch value `η = e^{ϑ_sw}` is `s`; its region `𝒯` is `arcRegion` (`𝒢*`).
Its functions `φ₂₁`, `φ₂₃` are `ArcParams.f`, `ArcParams.g`; `Θ` is `ArcParams.F` in the variable
`log ω`; `Υ` is `ArcParams.psiE`; and `χ̄_ij` is `switchingNum`.

All files are in `SmoothedPolygons/Ch14/`.
* §2, one arc in closed form: (1.1), (2.1), (2.2) and **Proposition 2.1** (the state, the exit time
  `T = ε log Y`), `ArcFrame.lean`; **Lemma 2.2** (the eigenvectors `V_e = V₊`, `V_f = V₋` of
  `ad(X₀ + P)`), `ArcCostate.lean`; the parameters (2.3), **Theorem 2.3** (the four-term normal
  form) and (2.4), `ArcNormalForm.lean`.
* §3, **Proposition 3.1** (the relation `det Λ₁ = 9/4`): `ArcRelation.lean` (`R = 0`) and
  `ArcStepClosed.lean` (`R = Y² ε⁴ R̃`, `rel_eq`).
* §4, one arc: **Lemma 4.1** (Poisson brackets), `VertexPoissonBracket.lean`; (4.1),
  **Lemmas 4.2, 4.3**, `ArcParams.lean`; **Proposition 4.4**, `ArcConditions.lean`.
* §5, the map: **Theorem 5.1** (`arcParams_reinPoincare`, with the costate in closed form (5.4)),
  `ArcPoincareMap.lean` and `ArcStepClosed.lean` (`step_closed`); **Corollary 5.2**
  (`arc_propagation`), `ArcConditions.lean`; **Corollary 5.3** (the budget), `ArcPoincareMap.lean`.
* §6, the region `𝒢*` (`arcRegion`, `ArcConditions.lean`); **Lemmas 6.1–6.3**,
  `ArcStepRegion.lean`; **Lemma 6.4** (the exit criterion), `ArcStepExit.lean` and
  `ArcConditions.lean`; **Theorem 6.5** (`arcRegionInvariant_sharp`), this file.
* §7, **Lemma 7.1** (near the fixed point every chart point lies in `𝒢*`), `ArcLocal.lean`; the
  proof of **Theorem A**, this file.

## Statements

* `ArcRegionInvariant` (INV).
* `ArcRegionInvariant.reachesStarBoundary`: under (INV), the forward orbit of every point of `𝒢*`
  reaches the boundary of the star domain (`ReachesStarBoundary`).
* `unstableCurveLeavesStarDomain_of_arcRegionInvariant`: (INV) implies N4 (Theorem A in the form
  that Theorem 14.4.1 uses).
* **Theorem 6.5** (`arcRegionInvariant_sharp`, (INV) in a sharper form): for `q ∈ 𝒢*` with
  `F(log Y) < 0`, `F(q)` is a section point with `r > 0`, `f₀ > 0`, `p > 0`, `SwitchEntersE2`,
  and `f₀ ≥ q (1 - 1/Y)` at `F(q)`; if `Y(F q) < 16/5` then `F(q) ∈ 𝒢*`; if `Y(F q) ≥ 16/5` then
  the arc from `F(q)` exits (`ArcLeavesStarDomain`).
* `arcRegionInvariant : ArcRegionInvariant` ((INV), from the sharp form).
* `unstableCurveLeavesStarDomain : UnstableCurveLeavesStarDomain` (N4, unconditionally; a term).

## Proofs (the route, the proof of Theorem A in §7 of the note)

1. `ArcRegionInvariant.reachesStarBoundary`, by induction on a natural number `n > ρ₁(q)/r(q)`
   (`reachesStarBoundary_of_lt_nat`: the statement for all `q ∈ 𝒢*` with `ρ₁(q)/r(q) < n`).
   Let `q ∈ 𝒢*`; it has `f₀ > 0` and `p > 0`, so `SwitchEntersE2 q` (`switchEntersE2_of_arc`).
   * If `F(log Y) ≥ 0`: `ArcLeavesStarDomain q` (`arcLeavesStarDomain_of_arc`); take `K = 0`.
   * If `F(log Y) < 0`: `ArcSwitchesToE1 q` (`arcSwitchesToE1_of_arc`); `F q` is a section point
     with `f₀ > 0`, `p > 0`, `r > 0` (`arc_propagation`), so `SwitchEntersE2 (F q)`. By (INV),
     either `ArcLeavesStarDomain (F q)` (take `K = 1`), or `F q ∈ 𝒢*`: then `r(F q) > r(q)`
     (`radius_lt_of_mem_arcRegion`) and `ρ₁(F q) = ρ₁(q) - 2 r(F q)` (`radius_reinPoincare`), so
     `ρ₁(F q)/r(F q) < ρ₁(q)/r(q) - 2`, so `F q` satisfies the bound `n - 1`; by induction
     `ReachesStarBoundary (F q)` with some `K'`, and `ReachesStarBoundary q` with `K = K' + 1`.
   This is the budget of Corollary 5.3: the radii increase and sum to less than `ρ₁(q₀)/2`, so
   the orbit has fewer than `ρ₁(q₀)/(2 r(q₀))` switching points.
2. N4: take `e` from `lemma14_3_1` and `U = V` from Lemma 7.1
   (`exists_nhds_lieChart_mem_arcRegion`). A point `p` of `Function.localUnstableSet e chartPtOut U`
   lies in `U`, so for `r > 0`, `lieChart p ∈ 𝒢*`, and step 1 gives
   `ReachesStarBoundary (lieChart p)`.
3. `arcRegionInvariant_sharp` (Theorem 6.5): see its docstring. It assembles Theorem 5.1
   (`arcParams_reinPoincare`, `ArcParams.step_closed`), Proposition 3.1 at `F q`
   (`arcParams_rel`, `ArcParams.rel_eq`), Lemmas 6.1–6.3 (`ArcParams.q_nonpos_of_relT`,
   `ArcParams.f0_ge_of_relT`, `ArcParams.pNew_lt`, `ArcParams.two_lt_YNew`, `ArcParams.YNew_ge`,
   `ArcParams.E_new_iff`) and Lemma 6.4 (`arcLeavesStarDomain_of_Y_ge`) with Proposition 4.4 and
   Corollary 5.2 (`switchesBeforeExit_of_arc`, `arc_propagation`, `switchEntersE2_of_arc`).
4. `arcRegionInvariant`: the two cases of the sharp form.
5. `unstableCurveLeavesStarDomain`: step 2 applied to `arcRegionInvariant` (a term).

## Why (INV) holds

* On `𝒢*` (`r > 0`, `f₀ > 0`, `q ≤ 0`, `p > 0`, `(Y - 1)(Y' - 2) ≤ Y - 2`), one step keeps
  `r > 0`, `f₀ > 0` and `p > 0` by itself (`arc_propagation`). What needs an argument is `q ≤ 0`
  and the expansion condition at `F(q)`, unless `F(q)` exits.
* The relation `R̃ = 0` (Proposition 3.1) rearranges to
  `2Y'(ab - 3) f₀ = 2q[(YY' - 1) b - 2p] + (Y'(f₀ - q) - Yp)² + 2(YY' - 1) a p`
  (`a = Y - 2`, `b = Y' - 2`). So when `2p < (2Y' - 1) b` and `ab ≤ 3`, `q > 0` is impossible, and
  `f₀ ≥ q (1 - 1/Y)` holds in any case (Lemma 6.1).
* At the next point `p` is small: `2p_new < (2Y'_new - 1)(Y'_new - 2)` by the explicit formulas
  of Theorem 5.1 (Lemma 6.2), because the switch comes before the exit.
* If `Y_new < 16/5`, the expansion condition holds at `F(q)` (Lemma 6.3), so `ab < 3` there and
  Lemma 6.1 gives `q_new ≤ 0`: `F(q) ∈ 𝒢*`. If `Y_new ≥ 16/5`, the next arc exits (Lemma 6.4,
  with `f₀ ≥ q (1 - 1/Y)` from Lemma 6.1).
* The proof uses no computer: every step is a polynomial identity, elementary calculus
  (monotonicity from the sign of a derivative, the intermediate value theorem), or the bound
  `log(16/5) > 297/256` (four terms of a series with positive terms).
* *Numerical evidence* (not part of the proof): samples of about 46,000 switching points of `𝒢*`
  (Lemmas 6.1–6.2 and Theorem 6.5 held at each), and of 2,588 chart points (every orbit exits after
  at most 7 switching arcs). Along `W^u`, from the point with `r = 10⁻⁶`, the orbit has seven
  switching arcs; at the seventh `Y_new = 38.2`, and the next arc exits.
* (INV) is not weaker than N4: it concerns all of `𝒢*`, not only the unstable curve.
-/

@[expose] public section

namespace SmoothedPolygons

open Set Filter Topology

/-- **(INV): the region `𝒢*` is invariant under the Reinhardt–Poincaré map until the exit**
(§6). For every point `q` of `𝒢*` (`arcRegion`: a section point with
`r > 0`, `f₀ > 0`, `q ≤ 0`, `p > 0`, `(Y - 1)(Y' - 2) ≤ Y - 2`) whose `e₂`-arc switches inside the
star domain (`F(log Y) < 0`), its image `F(q) = reinPoincare q` is again in `𝒢*`, or the `e₂`-arc
from `F(q)` leaves the star domain before switching. A single-step statement about an explicit map
of four real parameters (Theorem 5.1). It is proved: `arcRegionInvariant` (Theorem 6.5), from
`arcRegionInvariant_sharp`. See the module docstring. -/
def ArcRegionInvariant : Prop :=
  ∀ q ∈ arcRegion, (arcParams q).F (Real.log (arcY q)) < 0 →
    reinPoincare q ∈ arcRegion ∨ ArcLeavesStarDomain (reinPoincare q)

/-- The induction of `ArcRegionInvariant.reachesStarBoundary` (Corollary 5.3): every
point of `𝒢*` with `ρ₁(q)/r(q) < n` reaches the boundary of the star domain. -/
private theorem reachesStarBoundary_of_lt_nat (h : ArcRegionInvariant) :
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
  exact reachesStarBoundary_of_lt_nat h n q hq hn

/-- **Theorem A** (§7 of the note), in the form that Theorem 14.4.1 uses: **(INV) implies N4**
(`fig:unstable-curve`), the numerical fact behind
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
  exact reachesStarBoundary_of_lt_nat h n _ (hVr p hpV hp1) hn

/-- **Theorem 6.5** of the note (one step from `𝒢*`; (INV) in a sharp form). Let `q ∈ 𝒢*` with
`F(log Y) < 0` (the arc switches inside the star domain). Then `F(q) = reinPoincare q` is a section
point with `r > 0`, `f₀ > 0` and `p > 0` (so `SwitchEntersE2 (F q)`), and `f₀ ≥ q (1 - 1/Y)` at
`F(q)`; moreover
* if `Y(F q) < 16/5`, then `F(q) ∈ 𝒢*`;
* if `Y(F q) ≥ 16/5`, then the arc from `F(q)` leaves the star domain before switching.

Route (the note, proof of Theorem 6.5). Write `a = arcParams q`, `s = e^{τ_sw}`, and
`b = arcParams (F q)` for the parameters of the next point.
1. From `q ∈ 𝒢*`: a section point, `r > 0`, `f₀ > 0`, `q ≤ 0`, `p > 0` and the expansion condition.
   `switchesBeforeExit_of_arc`: `SwitchesBeforeExit q`. `arc_propagation` (Corollary 5.2): `F q`
   is a section point with `f₀ > 0`, `p > 0`, `r(F q) > 0`; `switchEntersE2_of_arc` at `F q`
   (Proposition 4.4 (1)).
2. `ε > 0`, `Y > 1`, `g₀ = 0`, `a.radius = r`, so `Y' - 2 > 0`; the expansion condition gives
   `Y - 2 > 0`. `ArcParams.exp_tauSw_spec` (Lemma 4.3): `Y - 1 < s`, `1 < s < Y`.
3. The next point in closed form (Theorem 5.1): `arcParams_reinPoincare` and
   `ArcParams.step_closed` give `Y(F q) = Y_new(s)`, `Y'(F q) = Y'_new(s)`, `p(F q) = p_new(s)`.
4. The relation at the next point (Proposition 3.1): `b.relT = 0` (`arcParams_rel` at the section
   point `F q`, `ArcParams.rel_eq`).
5. Lemma 6.2 (`ArcParams.pNew_lt`, `ArcParams.two_lt_YNew`): `2 b.p < (2 b.Y' - 1)(b.Y' - 2)` and
   `b.Y > 2`; also `b.Y' = Y/(Y - s) > 2` since `2s > Y`. So Lemma 6.1 applies to `b`; its part (ii)
   (`ArcParams.f0_ge_of_relT`) gives `f₀ ≥ q (1 - 1/Y)` at `F q`.
6. If `Y(F q) < 16/5`: Lemma 6.3 (`ArcParams.YNew_ge`, contrapositive) gives `ψ(s) ≥ 0`, which is
   the expansion condition at `F q` (`ArcParams.E_new_iff`). It gives `Y'(F q) - 2 < 1`, and
   `Y(F q) - 2 < 6/5`, so `(b.Y - 2)(b.Y' - 2) < 3`, and Lemma 6.1 (i)
   (`ArcParams.q_nonpos_of_relT`) gives `q(F q) ≤ 0`. So `F q ∈ 𝒢*`.
7. If `Y(F q) ≥ 16/5`: Lemma 6.4 (`arcLeavesStarDomain_of_Y_ge`) at `F q`, with step 5. -/
theorem arcRegionInvariant_sharp {q : iso_PhasePt} (hq : q ∈ arcRegion)
    (hF : (arcParams q).F (Real.log (arcY q)) < 0) :
    IsArcSectionPt (reinPoincare q) ∧ 0 < (reinPoincare q).1 0 0 ∧
      0 < arcF0 (reinPoincare q) ∧ 0 < arcP (reinPoincare q) ∧ SwitchEntersE2 (reinPoincare q) ∧
      arcQ (reinPoincare q) * (1 - 1 / arcY (reinPoincare q)) ≤ arcF0 (reinPoincare q) ∧
      (arcY (reinPoincare q) < 16 / 5 → reinPoincare q ∈ arcRegion) ∧
      (16 / 5 ≤ arcY (reinPoincare q) → ArcLeavesStarDomain (reinPoincare q)) := by
  obtain ⟨hs, hr, h1, h2, h4, hE⟩ := hq
  set a := arcParams q with ha_def
  have hsw := (switchesBeforeExit_of_arc hs h1 h2 hF).1
  obtain ⟨-, hpar⟩ := arcParams_reinPoincare hs hsw
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
  obtain ⟨hsY1, hs1, hsY, -, -⟩ := a.exp_tauSw_spec h1 h2 hY1.le hF
  set s := Real.exp a.tauSw with hs_def
  obtain ⟨hcY, hcY', -, hcp, -⟩ := a.step_closed he hY1 hg0 h1 h2 hF (arcQ (reinPoincare q))
  have hYn : arcY (reinPoincare q) = a.YNew s := (congrArg ArcParams.Y hpar).trans hcY
  have hYn' : arcY' (reinPoincare q) = a.YNew' s :=
    (arcParams_Y' hFs.2).symm.trans ((congrArg ArcParams.Y' hpar).trans hcY')
  have hpn : arcP (reinPoincare q) = a.pNew s := (congrArg ArcParams.p hpar).trans hcp
  -- step 4: the relation at the next point
  have hbY' : (arcParams (reinPoincare q)).Y' = arcY' (reinPoincare q) := arcParams_Y' hFs.2
  have hbR : (arcParams (reinPoincare q)).relT = 0 := by
    have hbe : 0 < arcEps (reinPoincare q) := arcEps_pos hFs.2
    have hbY : 0 < arcY (reinPoincare q) := by linarith [one_lt_arcY hFs.2]
    have h0 := (arcParams (reinPoincare q)).rel_eq hbe.ne' hbY.ne'
    rw [arcParams_rel hFs] at h0
    have : arcY (reinPoincare q) ^ 2 * arcEps (reinPoincare q) ^ 4 ≠ 0 := by positivity
    exact (mul_eq_zero.1 h0.symm).resolve_left this
  -- step 5: Lemma 6.2, so Lemma 6.1 applies at the next point
  have hYn2 : 2 < arcY (reinPoincare q) := by
    rw [hYn]; exact a.two_lt_YNew (by linarith) (by linarith) hs1 hsY1.le hsY
  have hbW : 2 < (arcParams (reinPoincare q)).Y' := by
    rw [hbY', hYn']
    unfold ArcParams.YNew'
    rw [lt_div_iff₀ (by linarith)]
    linarith
  have hbp : 2 * (arcParams (reinPoincare q)).p <
      (2 * (arcParams (reinPoincare q)).Y' - 1) * ((arcParams (reinPoincare q)).Y' - 2) := by
    rw [hbY', hYn']
    change 2 * arcP (reinPoincare q) < _
    rw [hpn]
    exact a.pNew_lt h2 hs1 hsY1.le hsY
  have h5' : arcQ (reinPoincare q) * (1 - 1 / arcY (reinPoincare q)) ≤ arcF0 (reinPoincare q) :=
    (arcParams (reinPoincare q)).f0_ge_of_relT hbR hYn2.le hbW hF1.le hF4.le hbp
  refine ⟨hFs, hFr, hF1, hF4, hSE, h5', fun hlt ↦ ?_, fun hge ↦ ?_⟩
  · -- step 6: the expansion condition and `q ≤ 0` at the next point
    have hpsi : 0 ≤ a.psiE s := by
      by_contra h
      push Not at h
      have := a.YNew_ge (by linarith) (by linarith) hsY1.le hsY h
      rw [← hYn] at this
      linarith
    have hEn : (arcY (reinPoincare q) - 1) * (arcY' (reinPoincare q) - 2) ≤
        arcY (reinPoincare q) - 2 := by
      rw [hYn, hYn']; exact (a.E_new_iff hsY.ne).2 hpsi
    have hw : arcY' (reinPoincare q) - 2 < 1 := by
      by_contra h
      push Not at h
      nlinarith [mul_le_mul_of_nonneg_left h (by linarith : (0:ℝ) ≤ arcY (reinPoincare q) - 1)]
    have hab : (arcY (reinPoincare q) - 2) * ((arcParams (reinPoincare q)).Y' - 2) ≤ 3 := by
      rw [hbY']
      nlinarith [mul_le_mul_of_nonneg_left hw.le (by linarith : (0:ℝ) ≤ arcY (reinPoincare q) - 2)]
    exact ⟨hFs, hFr, hF1,
      (arcParams (reinPoincare q)).q_nonpos_of_relT hbR hYn2.le hbW hF1.le hF4.le hbp hab, hF4, hEn⟩
  · -- step 7: the exit criterion
    exact arcLeavesStarDomain_of_Y_ge hFs hFr hF1 hF4 hge h5'

/-- **(INV)**, the one-step statement used in the proof of Theorem A: the region `𝒢*` is invariant
under the Reinhardt–Poincaré map until the exit. From the sharp form `arcRegionInvariant_sharp`
(Theorem 6.5 of the note), by cases on `Y(F q) < 16/5`. -/
theorem arcRegionInvariant : ArcRegionInvariant := by
  intro q hq hF
  obtain ⟨-, -, -, -, -, -, hin, hout⟩ := arcRegionInvariant_sharp hq hF
  by_cases h : arcY (reinPoincare q) < 16 / 5
  · exact Or.inl (hin h)
  · exact Or.inr (hout (not_lt.1 h))

/-- **N4, unconditionally** (`fig:unstable-curve`): the unstable curve `W^u(q_out)` reaches the
boundary of the star domain (Figure 14.2; the numerical fact behind Theorem 14.4.1). Theorem A
applied to (INV) (`arcRegionInvariant`). Departure from the paper (the user's decision): the book
computes the unstable curve numerically (TeX 11951–11991); here N4 is proved without computer
assistance, from the exact structure of the arcs and the proof of (INV). -/
theorem unstableCurveLeavesStarDomain : UnstableCurveLeavesStarDomain :=
  unstableCurveLeavesStarDomain_of_arcRegionInvariant arcRegionInvariant

end SmoothedPolygons
