module

public import SmoothedPolygons.Ch13.Extremals
public import SmoothedPolygons.Ch13.SingularLocus

/-!
# Chapter 16: relaxed Fuller extremals follow the first control (for §16.4.2, N5)

Two facts about trajectories of the Fuller system with controls in the triangle `U_T` (relaxed
controls: weak-* limits of `V_T`-valued controls) satisfying the maximum condition, needed by the
proof of N5 (`clusterSetForwardInvariant`, `SmoothedPolygons/Ch16/ReinhardtShadowing.lean`): the
limits of rescaled Reinhardt extremals near the singular locus are such trajectories
(`exists_tendsto_rescaledArc`), and these two facts identify them.

* `eq_flow_of_maxCondition_UT`: the `U_T` form of `eq_flow_of_maxCondition` (proof of Lemma 13.2.6,
  TeX 10978–10995): from `z⁰ ≠ 0`, up to the first switching time, a relaxed extremal is the
  constant-control flow with the first control, and its control is the first control almost
  everywhere;
* `firstControl_beaten_UT`: the `U_T` form of `firstControl_beaten`: no relaxed extremal from
  `z⁰ ≠ 0` keeps the first control (almost everywhere) on an interval `[0, t_sw + ε]`.

## Proofs (plan)

`eq_flow_of_maxCondition_UT`: a relaxed extremal has `u(t) ∈ V_T` for almost every `t`. Where the
maximizing face of `U_T` at `z(t)` is a vertex, the maximum condition forces `u(t)` to be that
vertex. The set `E` of times where the maximizing face is an edge `[v₁, v₂]` has measure zero: on
`E`, `χ(t) = RR(v₁ - v₂, z₃(t)) = 0`; `χ` is `C²` with `χ''' = RR(v₁ - v₂, -iu)` almost
everywhere, and at density points of `E` (Lebesgue's density theorem) `χ' = χ'' = χ''' = 0`,
while `RR(v₁ - v₂, -iu) = -Im(v̄₂ v₁) = ±√3/2` for every `u` in the edge (the computation of
Lemma 13.2.6); the case of all of `U_T` maximizing is `z₃ = z₂ = z₁ = 0` on an interval,
`lemma13_3_2`. So `u ∈ V_T` a.e., the trajectory is a `V_T`-trajectory after changing the control
on a null set, and `eq_flow_of_maxCondition` applies. `firstControl_beaten_UT`: if `u = u₀` a.e. on
`[0, t_sw + ε]`, then `z = flow · z⁰ u₀` there (the integral equations), and by
`firstControl_beaten` some vertex `v` strictly beats `u₀` at some `t ∈ (t_sw, t_sw + ε)`, hence on
a neighborhood of `t` (continuity), a set of positive measure where the maximum condition fails.
Size: 300–600 lines.
-/

@[expose] public section

namespace SmoothedPolygons

open Complex MeasureTheory Set

namespace TriFuller

/-- **Relaxed extremals follow the first control up to the first switching time** (the `U_T` form
of `eq_flow_of_maxCondition`). Let `z⁰ ≠ 0` and let `(z, u)` be a trajectory of the Fuller system on
`[0, T]` with controls in `U_T` satisfying the maximum condition, with `z(0) = z⁰` and
`T ≤ t_sw(z⁰)`. Then `z` is the constant-control solution with the first control of `z⁰`, and `u`
is the first control almost everywhere on `[0, T]`. -/
theorem eq_flow_of_maxCondition_UT {z₀ : Fin 3 → ℂ} (hz₀ : z₀ ≠ 0) {T : ℝ}
    (hT : T ≤ firstSwitchTime z₀) {z : ℝ → Fin 3 → ℂ} {u : ℝ → ℂ} (h : IsTrajectory UT 0 T z u)
    (hmax : MaxCondition UT 0 T z u) (h0 : z 0 = z₀) :
    (∀ t ∈ Icc 0 T, z t = flow t z₀ (firstControl z₀)) ∧
      ∀ᵐ t, t ∈ Icc 0 T → u t = firstControl z₀ := by
  sorry

/-- **No relaxed extremal keeps the first control past the first switching time** (the `U_T`
form of `firstControl_beaten`): for `z⁰ ≠ 0` and `ε > 0`, a trajectory with controls in `U_T`
satisfying the maximum condition on `[0, t_sw(z⁰) + ε]` from `z⁰` does not have the first control
almost everywhere on that interval. -/
theorem firstControl_beaten_UT {z₀ : Fin 3 → ℂ} (hz₀ : z₀ ≠ 0) {ε : ℝ} (hε : 0 < ε)
    {z : ℝ → Fin 3 → ℂ} {u : ℝ → ℂ} (h : IsTrajectory UT 0 (firstSwitchTime z₀ + ε) z u)
    (hmax : MaxCondition UT 0 (firstSwitchTime z₀ + ε) z u) (h0 : z 0 = z₀) :
    ¬ ∀ᵐ t, t ∈ Icc 0 (firstSwitchTime z₀ + ε) → u t = firstControl z₀ := by
  sorry

end TriFuller

end SmoothedPolygons
