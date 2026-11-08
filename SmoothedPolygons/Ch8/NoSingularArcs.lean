module

public import SmoothedPolygons.Ch8.SingularLocus
public import SmoothedPolygons.Ch8.CircleVariation
public import SmoothedPolygons.Ch8.EdgeBangBang
public import SmoothedPolygons.Ch8.EdgeExtremal
public import SmoothedPolygons.Ch8.EdgePullback

/-!
# The global minimizer has no singular subarcs (Theorem 8.2.7)

Theorem 8.2.7 (`thm:no-singular-arcs`, TeX 7315): "The global minimizer of the Reinhardt problem
does not contain any singular subarcs." A singular subarc (Definition 6.2.1(3), `IsSingularSubarc`)
is an open time interval on which the maximum condition does not determine the control: at every
time the Hamiltonian has at least two maximizers in `U_T`. By Lemma 8.2.1 the set of maximizers is
then an edge of `U_T` or all of `U_T`.

## The authors' reading (formalized as `theorem8_2_7`)

The book's proof (TeX 7320–7391) treats only the singular subarcs on which the Hamiltonian is
independent of the control (all of `U_T` maximizes): by Theorem 8.2.6 they are circular arcs, and a
circular arc is not a local minimizer (second variation, `l3st_exists_lt_cost_of_circleArc`). This
covered case is `not_forall_hamiltonian_eq_of_isReinhardtMinimizer`, which is what the proof of
Theorem 16.3.1 uses ("A trajectory cannot remain on the singular locus for any positive interval
of time by Theorem 8.2.7", TeX 12816–12817).

The edge case is left to the edge control problem: "The theorem is only true if we include
secondary edge optimal control problem" (the authors' comment before the theorem, TeX 7300–7302),
"We say Reinhardt problem here rather than Reinhardt control problem because we want to include the
edge control problem" (TeX 7312–7313), and Chapter 1 (TeX 806–821): when the maximizing face is an
edge, the control problem is modified to the edge control problem, whose extremals are bang-bang
with finitely many switches (Theorem 8.1.4). So "singular" refers, on an interval where the control
lies in an edge of `U_T`, to the maximization of the edge problem's Hamiltonian (the minimizer is
edge extremal, Proposition 8.1.3), and elsewhere to the Reinhardt Hamiltonian. `theorem8_2_7`
states this reading (the user's decision): every subarc `(a, b)` of the global minimizer either
contains a subinterval on which the control lies in an edge, and on such an interval the edge arc
has edge costates, none of which has a singular subarc of the edge problem (`IsEdgeSingularSubarc`);
or it contains none, and then no lift is a singular subarc on `(a, b)`.

The edge part holds for every extremal of the edge problem
(`IsEdgeProblemExtremal.not_isEdgeSingularSubarc`: on an edge-singular subarc `λ₂ ≡ 0`, then (8.1.8)
makes `x²` constant, against `x' = y > 0`), the rest by the circle and a localization (on a
singular subarc, near a time with `Λ_R ≠ 0` the maximizers are one edge, so the control lies in
that edge).

## Normal lifts: the literal statement

For normal lifts (`λ_cost ≠ 0`) the statement holds as printed:
`not_isSingularSubarc_of_isReinhardtMinimizer_of_isNormalExtremal`. On an interval where the
maximizers are an edge `{u_j = 0}` at every time, the control lies in that edge, and the Reinhardt
costate pulled back to the edge submanifold of (8.1.1) and shifted by `(3/2) λ_cost d(s + x)`
(`edgePullback`, `SmoothedPolygons/Ch8/EdgePullback.lean`) is an edge costate with `H_e = H_R`
(`IsExtremalOn.isEdgeProblemExtremal_edgePullback`), so the edge arc is an edge-singular subarc of
an edge extremal, which is impossible. Intervals that mix edges and all of `U_T` contain, by
continuity, an interval of one of the two kinds; on intervals with `Λ_R ≡ 0` the circle argument
applies.

## Abnormal lifts: the literal statement is open

For abnormal lifts (`λ_cost = 0`) the printed statement (no `IsSingularSubarc` at all, for every
lift of the global minimizer) is neither proved nor refuted, and is not formalized. Along every
trajectory with control in an edge there is a two-parameter family of abnormal costates (the
conormal bundle of the edge submanifold of (8.1.1), which contains Remark 8.1.6's, `remark8_1_6`,
with the sign of gap G4) for which the Hamiltonian vanishes on the edge; the edge is the set of
maximizers where the Hamiltonian at the third vertex is negative. An abnormal lift is
edge-singular on an interval exactly when it is conormal there, and then its pulled-back costate
vanishes, so it gives no edge costate. What is missing is the exclusion of global abnormal lifts
of a global minimizer (with the transversality conditions and the maximum condition on all of
`[0, T]`) that are conormal to an edge submanifold on some interval. No counterexample is known
(none can be exhibited without knowing the minimizer). Theorem 16.3.1 does not depend on it.
-/

@[expose] public section

namespace SmoothedPolygons

open Set MeasureTheory Filter Topology Matrix

/-- A **singular subarc of an extremal of the edge control problem** (Definition 6.2.1(3) for the
edge control problem of Definition 8.1.1; the "secondary edge optimal control problem" of
TeX 7300–7302): on the open interval `(α, β)` the maximization of the edge Hamiltonian (8.1.6)
over the control set `[-½, ½]` does not determine the edge control, i.e. at every time it has at
least two maximizers. -/
def IsEdgeSingularSubarc (ν : ℝ) (q : ℝ → Fin 3 → ℝ) (p : ℝ → StrongDual ℝ (Fin 3 → ℝ))
    (α β : ℝ) : Prop :=
  α < β ∧ ∀ t ∈ Ioo α β, ∃ v ∈ edgeControlSet, ∃ w ∈ edgeControlSet, v ≠ w ∧
    (∀ v' ∈ edgeControlSet, Pontryagin.controlHamiltonian edgeField edgeCost ν (q t) (p t) v' ≤
      Pontryagin.controlHamiltonian edgeField edgeCost ν (q t) (p t) v) ∧
    ∀ v' ∈ edgeControlSet, Pontryagin.controlHamiltonian edgeField edgeCost ν (q t) (p t) v' ≤
      Pontryagin.controlHamiltonian edgeField edgeCost ν (q t) (p t) w

/-- **An extremal of the edge control problem has no singular subarc** (the argument of steps 4
and 6 of the proof of Theorem 8.1.4, TeX 6846–6894).

Proof: by (8.1.6) (`eqn_edge_ham`) only `λ₂ f₂(x, y, u_e)` depends on the control, and `f₂` is
strictly decreasing in `u_e` (as in `l3st_edge_max_rule`), so two distinct maximizers at `t` force
`λ₂(t) = 0`. On an edge-singular subarc `(α, β)`, `λ₂ ≡ 0`, so `λ₂` has derivative `0` at every
`t ∈ (α, β)` and (8.1.8) (`eqn_edge_zero`) gives `ν ≠ 0` and `x(t)² = -λ₃/ν`, a constant
(`λ₃` is constant, `eqn_costate_edge`). But `x' = y > 0` (admissibility in `edgeDomain`) makes `x`
strictly increasing, so it takes three distinct values on `(α, β)`, which cannot have the same
square. Expected size: 80–150 lines. -/
theorem IsEdgeProblemExtremal.not_isEdgeSingularSubarc {T : ℝ} {ue : ℝ → ℝ}
    {q : ℝ → Fin 3 → ℝ} {ν : ℝ} {p : ℝ → StrongDual ℝ (Fin 3 → ℝ)}
    (h : IsEdgeProblemExtremal T ue q ν p) {α β : ℝ} (hα : 0 ≤ α) (hβ : β ≤ T) :
    ¬ IsEdgeSingularSubarc ν q p α β := by
  sorry

/-- **Theorem 8.2.7, the case its proof covers**: a lift of a global minimizer has no singular
subarc on which the Hamiltonian is independent of the control (equivalently, by Theorem 8.2.6, the
lift does not stay in the singular locus on any open interval). This is the part of
Theorem 8.2.7 used by Theorem 16.3.1.

Proof (the book's, TeX 7320–7391): by Theorem 8.2.6 (`theorem8_2_6`, applied to the restriction
`l3st_isExtremalOn_of_isPontryaginExtremal`) the subarc is a circular arc, `X ≡ J` on `[a, b]`;
by the second variation (`l3st_exists_lt_cost_of_circleArc`) some admissible trajectory has
smaller cost, against minimality. Expected size: 40–80 lines. -/
theorem not_forall_hamiltonian_eq_of_isReinhardtMinimizer {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X : ℝ → Mat2} (hmin : IsReinhardtMinimizer T u g X) {Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (hext : IsPontryaginExtremal T u g X Λ₁ ΛR lam) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b ≤ T) :
    ¬ ∀ t ∈ Ioo a b, ∀ v ∈ controlSimplex, ∀ w ∈ controlSimplex,
      hamiltonian lam (Λ₁ t) (ΛR t) (X t) v = hamiltonian lam (Λ₁ t) (ΛR t) (X t) w := by
  sorry

/-- **Theorem 8.2.7** (`thm:no-singular-arcs`), in the authors' reading: the global minimizer of
the Reinhardt problem contains no subarc on which its control is not determined by maximization,
where on an interval with the control in an edge of `U_T` maximization refers to the Hamiltonian of
the edge control problem, and elsewhere to the Reinhardt Hamiltonian (module docstring; TeX
7300–7302, 7312–7313, 806–821). For a global minimizer and an interval `(a, b) ⊆ [0, T]`:

1. if the control lies in the edge `{u_j = 0}` almost everywhere on `(a, b)`, the edge arc
   `(edgeParam j u, edgeState j X a)` has an edge costate (Proposition 8.1.3: the minimizer is
   edge extremal), and no edge costate of it has a singular subarc of the edge problem
   (`IsEdgeSingularSubarc`) in `[0, b - a]`;
2. if the control lies in no edge on any subinterval of `(a, b)`, no lift of the minimizer to a
   Pontryagin extremal is a singular subarc (`IsSingularSubarc`) on `(a, b)`.

Every subarc either contains a subinterval of the first kind (part 1 applies to it) or is of the
second kind, so in either case the control is determined by the relevant maximization somewhere on
it. The literal statement (`IsSingularSubarc` excluded for every lift on every interval) holds for
normal lifts (`not_isSingularSubarc_of_isReinhardtMinimizer_of_isNormalExtremal`) and is open for
abnormal lifts (module docstring).

Proof:
1. Existence: `proposition8_1_3` (edge extremality on `[0, T]`, applied to `[a, b]`). No singular
   subarc: `IsEdgeProblemExtremal.not_isEdgeSingularSubarc` (Theorem 8.1.4's argument).
2. Suppose a lift is a singular subarc on `(a, b)`. If `Λ_R(t₀) ≠ 0` for some `t₀ ∈ (a, b)`, then
   at `t₀` the maximizers are an edge `{u_k = 0}` (Lemma 8.2.1, `lemma8_2_1`; two maximizers
   exclude a vertex), the third vertex `e_k` is strictly worse near `t₀` (continuity,
   `l3st_continuousOn_lift`), so near `t₀` the maximizers are that same edge (Lemma 8.2.1 again,
   with `Λ_R ≠ 0` near `t₀`), and the maximum condition puts the control in it almost everywhere
   on a subinterval, against the hypothesis. So `Λ_R ≡ 0` on `(a, b)`, the Hamiltonian is
   independent of the control there, against `not_forall_hamiltonian_eq_of_isReinhardtMinimizer`
   (Theorems 8.2.6 and 8.2.3, the second variation).
Expected size: 100–200 lines (with the localization helper shared with
`not_isSingularSubarc_of_isReinhardtMinimizer_of_isNormalExtremal`). -/
theorem theorem8_2_7 {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (hmin : IsReinhardtMinimizer T u g X) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ T) :
    (∀ j : Fin 3, (∀ᵐ t, t ∈ Ioo a b → u t j = 0) →
      (∃ (ν : ℝ) (p : ℝ → StrongDual ℝ (Fin 3 → ℝ)),
        IsEdgeProblemExtremal (b - a) (fun t ↦ edgeParam j (u (a + t))) (edgeState j X a) ν p) ∧
      ∀ (ν : ℝ) (p : ℝ → StrongDual ℝ (Fin 3 → ℝ)),
        IsEdgeProblemExtremal (b - a) (fun t ↦ edgeParam j (u (a + t))) (edgeState j X a) ν p →
        ∀ α β : ℝ, 0 ≤ α → β ≤ b - a → ¬ IsEdgeSingularSubarc ν (edgeState j X a) p α β) ∧
    ((∀ (j : Fin 3) (c d : ℝ), a ≤ c → c < d → d ≤ b → ¬ ∀ᵐ t, t ∈ Ioo c d → u t j = 0) →
      ∀ (Λ₁ ΛR : ℝ → Mat2) (lam : ℝ), IsPontryaginExtremal T u g X Λ₁ ΛR lam →
        ¬ IsSingularSubarc lam Λ₁ ΛR X a b) := by
  sorry

/-- **Theorem 8.2.7 for normal lifts, as printed**: a lift of a global minimizer to a normal
Pontryagin extremal (`λ_cost ≠ 0`, Definition 6.2.1(2)) has no singular subarc
(Definition 6.2.1(3)) at all. This is the repair, along the book's lines, of gap G8 for normal
lifts (module docstring); for abnormal lifts the printed statement is open.

Proof:
1. Suppose the lift is a singular subarc on `(a, b)`. If `Λ_R ≡ 0` on `(a, b)`, the Hamiltonian is
   independent of the control there: `not_forall_hamiltonian_eq_of_isReinhardtMinimizer`.
2. Otherwise, as in step 2 of `theorem8_2_7`, there are an edge `{u_k = 0}` and `[c, d] ⊆ (a, b)`,
   `c < d`, on which the maximizers of the Reinhardt Hamiltonian are that edge at every time and
   the control lies in it almost everywhere.
3. The pulled-back costate (`IsExtremalOn.isEdgeProblemExtremal_edgePullback`, on the restriction
   `l3st_isExtremalOn_of_isPontryaginExtremal` to `[c, d]`, with `λ_cost ≠ 0`) is an edge costate
   of the edge arc, with `H_e(v) = H_R(edgeControlIn k v)`
   (`IsExtremalOn.controlHamiltonian_edgePullback`). Two distinct maximizers of `H_R` in the edge
   give two distinct maximizers of `H_e` in `[-½, ½]` (their edge parameters), at every time of
   `(0, d - c)`: an edge-singular subarc, against
   `IsEdgeProblemExtremal.not_isEdgeSingularSubarc` (`λ₂ ≡ 0`, then (8.1.8) makes `x²` constant,
   against `x' = y > 0`).
Expected size: 60–120 lines. -/
theorem not_isSingularSubarc_of_isReinhardtMinimizer_of_isNormalExtremal {T : ℝ}
    {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2} (hmin : IsReinhardtMinimizer T u g X)
    {Λ₁ ΛR : ℝ → Mat2} {lam : ℝ} (hext : IsNormalExtremal T u g X Λ₁ ΛR lam) {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ T) :
    ¬ IsSingularSubarc lam Λ₁ ΛR X a b := by
  sorry

end SmoothedPolygons
