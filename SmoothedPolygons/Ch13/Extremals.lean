module

public import SmoothedPolygons.Ch13.SingularLocus

/-!
# Chapter 13: extremals of the Fuller system with measurable controls

Two facts that Chapter 13 of Hales–Vajjha, *Packings of Smoothed Polygons*, uses about the
solutions of the Fuller system (13.2.1) with a measurable control satisfying the maximum
condition (13.2.5), and that connect them with the constant-control objects (first control, first
switching time, the Poincaré map):

* "if `u` is chosen according to the maximum principle, then `H_F` is constant along trajectories"
  (TeX 10741–10742; asserted; inventory, gap 1): `l4st_hamMax_eq_of_maxCondition`;
* "The first control is determined by the maximum principle for `t` small and nonnegative"
  (proof of Lemma 13.2.6, TeX 10978–10979): every such solution starting at `z⁰ ≠ 0` uses the
  first control up to the first switching time, `l4st_eq_flow_of_maxCondition`. This is what makes
  the Poincaré map, defined with constant controls, the map along "the solution … with control
  defined by the maximum principle" of TeX 11243–11245.
-/

@[expose] public section

namespace SmoothedPolygons

open Complex MeasureTheory Set TriFuller

namespace TriFuller

/-- **The Hamiltonian is constant along extremals** (TeX 10741–10742). Along a trajectory of the
Fuller system with controls in `V_T` satisfying the maximum condition (13.2.5), the maximized
Hamiltonian `H_F⁺(z(t))` is constant, and `H_F(z(t), u(t)) = H_F⁺(z(t₁))` for almost every `t`.

Proof route: `H_F⁺(z(t)) = RR(z₁, z₂ i) + max_{v ∈ V_T} RR(v, z₃(t))` is Lipschitz (a maximum of
three `C¹` functions plus an absolutely continuous one). At almost every `t` it is differentiable,
the maximum condition holds and `z₁' = -iu`; there the derivative of the maximum is `RR(v*, z₂)`
for any maximizer `v*`, in particular for `v* = u(t)` (a maximum of differentiable functions has,
where it is differentiable, the derivative of each active function), and the derivative of
`RR(z₁, z₂ i)` is `RR(-iu, i z₂) + RR(z₁, i z₁) = -RR(u, z₂)`. The derivative vanishes almost
everywhere, so the Lipschitz function is constant. -/
theorem l4st_hamMax_eq_of_maxCondition {t₁ t₂ : ℝ} {z : ℝ → Fin 3 → ℂ} {u : ℝ → ℂ}
    (h : IsTrajectory VT t₁ t₂ z u) (hmax : MaxCondition VT t₁ t₂ z u) :
    (∀ t ∈ Icc t₁ t₂, hamMax (z t) = hamMax (z t₁)) ∧
      ∀ᵐ t, t ∈ Icc t₁ t₂ → ham (z t) (u t) = hamMax (z t₁) := by
  sorry

/-- **Extremals follow the first control up to the first switching time** (proof of Lemma 13.2.6,
TeX 10978–10995). Let `z⁰ ≠ 0` and let `(z, u)` be a trajectory of the Fuller system on `[0, T]`
with controls in `V_T`, satisfying the maximum condition (13.2.5), with `z(0) = z⁰` and
`T ≤ t_sw(z⁰)`. Then `u` is the first control of `z⁰` almost everywhere on `[0, T]`, and `z` is the
constant-control solution `t ↦ z(t, z⁰, firstControl z⁰)`.

Proof route: (local uniqueness) near `t = 0`, `z₃(t) = Q(t) - i u₃(t)` with
`Q(t) = z₃⁰ + z₂⁰ t + z₁⁰ t²/2` and `u₃(t) ∈ (t³/6) · conv(V_T)` ((13.3.1)–(13.3.2)). A control `v`
outside `V_{T,max}` is beaten by a lower-order term of `Q` for small `t > 0`; if
`V_{T,max} = {ζ^i, ζ^{i+1}}`, the controls `ζ^i, ζ^{i+1}` tie in `Q` and, as `u` takes values in
`[ζ^i, ζ^{i+1}]` there, `RR(ζ^{i+1} - ζ^i, -i u₃(t)) = -(√3/2) t³/6 < 0` (the computation of
Lemma 13.2.6, valid for every control in the edge: `RR(1 - ζ, -iw) = √3/2` for `w ∈ [1, ζ]`), so
`u = ζ^i` almost everywhere near `0`. (Continuation) Let `S` be the supremum of the `s ≤ T` such
that `u` is the first control almost everywhere on `[0, s]`; if `S < T`, then `z(S) =
z(S, z⁰, u) ≠ 0` by `l4f_flow_firstControl_ne_zero` (`S ≤ T ≤ t_sw`; Lemma 13.3.1 does not apply,
as `z₃⁰` need not lie on a wall) and the first control of `z(S)` is still `u` (it is optimal on
`[S, t_sw]`), so local uniqueness at `z(S)` contradicts the choice of `S`. -/
theorem l4st_eq_flow_of_maxCondition {z₀ : Fin 3 → ℂ} (hz₀ : z₀ ≠ 0) {T : ℝ}
    (hT : T ≤ firstSwitchTime z₀) {z : ℝ → Fin 3 → ℂ} {u : ℝ → ℂ} (h : IsTrajectory VT 0 T z u)
    (hmax : MaxCondition VT 0 T z u) (h0 : z 0 = z₀) :
    (∀ t ∈ Icc 0 T, z t = flow t z₀ (firstControl z₀)) ∧
      ∀ᵐ t, t ∈ Icc 0 T → u t = firstControl z₀ := by
  sorry

end TriFuller

end SmoothedPolygons
