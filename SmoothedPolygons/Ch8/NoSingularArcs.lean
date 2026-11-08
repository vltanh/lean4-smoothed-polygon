module

public import SmoothedPolygons.Ch8.SingularLocus
public import SmoothedPolygons.Ch8.CircleVariation
public import SmoothedPolygons.Ch8.EdgeBangBang

/-!
# The global minimizer has no singular subarcs (Theorem 8.2.7)

Theorem 8.2.7 (`thm:no-singular-arcs`, TeX 7315): "The global minimizer of the Reinhardt problem
does not contain any singular subarcs." A singular subarc (Definition 6.2.1(3),
`IsSingularSubarc`) is an open time interval on which the maximum condition does not determine the
control: at every time the Hamiltonian has at least two maximizers in `U_T`. By Lemma 8.2.1 the set
of maximizers is then an edge of `U_T` or all of `U_T`.

The book's proof (TeX 7320–7391) treats only the singular subarcs on which the Hamiltonian is
independent of the control (all of `U_T` maximizes): by Theorem 8.2.6 they are circular arcs, and
a circular arc is not a local minimizer (second variation, `l3st_exists_lt_cost_of_circleArc`).
That case is `l3st_not_hamiltonian_const_of_isReinhardtMinimizer`, which is all that the proof of
Theorem 16.3.1 uses ("A trajectory cannot remain on the singular locus for any positive interval
of time by Theorem 8.2.7", TeX 12816–12817).

## Gap G8: the statement as printed is not settled

The printed statement also covers singular subarcs on which the maximizers form an edge of
`U_T` at every time (`|I| = 2`), which the proof does not treat (the text before Theorem 8.2.6,
TeX 7253–7258, says that edges are handled by Theorem 8.1.4; but Theorem 8.1.4 shows that the
*edge problem* determines a bang-bang control, not that the *Reinhardt* Hamiltonian determines
the control). Status (worked out for this layer, see the report):

* **Normal lifts** (`λ_cost ≠ 0`) of a global minimizer have no singular subarcs, by a repair
  along the book's lines. On an interval where the maximizers are an edge `{u_j = 0}` at every
  time, the control lies in the edge, and the Reinhardt costate, pulled back to the edge
  submanifold `{g = g₀ h(t₀)⁻¹ h(s, x)}` of (8.1.1) and shifted by `(3/2) λ_cost d(s + x)` (the
  cost identity, `edgeCost_identity`), is a costate of the edge problem with `λ_edge =
  (3/2) λ_cost ≠ 0` whose `λ₂` is a positive multiple of the Reinhardt switching function of the
  edge (the `y`-component of `ν = cotangentNu`, §6.8); so `λ₂ ≡ 0` on the interval, then
  `λ₂' ≡ 0`, and (8.1.8) (`eqn_edge_zero`) gives `x² = -λ₃/λ_edge` constant, against `x' = y > 0`.
  A singular subarc that mixes edges and all of `U_T` contains, by continuity, an interval of one
  of the two kinds (the set `{Λ_R = 0}` is closed; on a component of its complement the
  maximizing edge is locally constant by upper semicontinuity of the maximizers).
* **Abnormal lifts** (`λ_cost = 0`) are not covered. Along every trajectory with control in an
  edge there is a two-parameter family of abnormal costates (the conormal bundle of the edge
  submanifold, which contains Remark 8.1.6's, `remark8_1_6`) for which the Hamiltonian vanishes
  on the edge; the edge is the set of maximizers where the Hamiltonian at the third vertex is
  negative (with the printed signs of Remark 8.1.6 it is the set of minimizers). An abnormal lift
  is edge-singular on an interval exactly when it is conormal there. Whether a global minimizer
  can carry a global abnormal lift (with the transversality conditions and the maximum condition
  on all of `[0, T]`) that is of this kind on some interval is not settled by the book or here.
  No counterexample is known (none can be exhibited without knowing the minimizer).

So `theorem8_2_7` is stated as printed and is not expected to be provable from the book's
arguments alone: what is missing is the exclusion of abnormal lifts of a global minimizer whose
costate lies, on some interval where the control is in an edge, in the conormal bundle of that
edge's submanifold (8.1.1). Theorem 16.3.1 does not depend on it.
-/

@[expose] public section

namespace SmoothedPolygons

open Set MeasureTheory Filter Topology Matrix

/-- **Theorem 8.2.7, the case its proof covers**: a lift of a global minimizer has no singular
subarc on which the Hamiltonian is independent of the control (equivalently, by Theorem 8.2.6, the
lift does not stay in the singular locus on any open interval). This is the part of
Theorem 8.2.7 used by Theorem 16.3.1.

Proof (the book's, TeX 7320–7391): by Theorem 8.2.6 (`theorem8_2_6`, applied to the restriction
`l3st_isExtremalOn_of_isPontryaginExtremal`) the subarc is a circular arc, `X ≡ J` on `[a, b]`;
by the second variation (`l3st_exists_lt_cost_of_circleArc`) some admissible trajectory has
smaller cost, against minimality. Expected size: 40–80 lines. -/
theorem l3st_not_hamiltonian_const_of_isReinhardtMinimizer {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X : ℝ → Mat2} (hmin : IsReinhardtMinimizer T u g X) {Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (hext : IsPontryaginExtremal T u g X Λ₁ ΛR lam) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b ≤ T) :
    ¬ ∀ t ∈ Ioo a b, ∀ v ∈ controlSimplex, ∀ w ∈ controlSimplex,
      hamiltonian lam (Λ₁ t) (ΛR t) (X t) v = hamiltonian lam (Λ₁ t) (ΛR t) (X t) w := by
  sorry

/-- **Theorem 8.2.7** (`thm:no-singular-arcs`), as printed. The global minimizer of the Reinhardt
problem contains no singular subarcs: for every global minimizer, every Pontryagin extremal lifting
it, and every open interval `(a, b) ⊆ [0, T]`, the lift is not a singular subarc on `(a, b)`
(Definition 6.2.1(3)).

Status (gap G8, see the module docstring): the book's proof covers the singular subarcs on which
the Hamiltonian is independent of the control
(`l3st_not_hamiltonian_const_of_isReinhardtMinimizer`); edge-singular subarcs of normal lifts are
excluded by the repair described in the module docstring (Theorem 8.1.4's claim (8.1.8),
`eqn_edge_zero`, and the monotonicity of `x`); edge-singular subarcs of abnormal lifts are not
excluded by any argument known here. The statement is kept as printed (it is neither proved nor
refuted); Theorem 16.3.1 uses only the covered case.

Proof route for the covered cases:
1. If `{t ∈ (a, b) | Λ_R(t) = 0}` has interior, Lemma 8.2.1 and Theorem 8.2.6 give a circular arc:
   `l3st_not_hamiltonian_const_of_isReinhardtMinimizer`.
2. Otherwise a component `(c, d)` of `{Λ_R ≠ 0} ∩ (a, b)` has, at every time, an edge as its set of
   maximizers (Lemma 8.2.1), the same edge `{u_j = 0}` throughout (upper semicontinuity of the
   maximizers and connectedness), and `u_j = 0` a.e. there.
3. For `λ_cost ≠ 0`: the pulled-back costate is an edge costate with `λ₂ ≡ 0` (step 2), so (8.1.8)
   holds on `(c, d)` and `x` is constant there, against `x' = y > 0` (`eqn_xy_edge`).
4. For `λ_cost = 0`: missing (module docstring). -/
theorem theorem8_2_7 {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (hmin : IsReinhardtMinimizer T u g X) {Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (hext : IsPontryaginExtremal T u g X Λ₁ ΛR lam) {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ T) :
    ¬ IsSingularSubarc lam Λ₁ ΛR X a b := by
  sorry

end SmoothedPolygons
