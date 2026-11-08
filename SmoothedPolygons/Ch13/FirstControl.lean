module

public import SmoothedPolygons.Ch13.Symmetry

/-!
# Chapter 13: walls, the first control and the switching times

§13.2 of Hales–Vajjha, *Packings of Smoothed Polygons* ("Walls" and "Switching Times",
TeX 10910–11068, and the most recent control, TeX 10880–10906):

* the walls (TeX 10910–10926): at a switch between `ζ` and `ζ²` the maximum condition reads
  `RR(z₃, ζ) = RR(z₃, ζ²) ≥ RR(z₃, 1)`, whose solution set is `ℝ_{≤0}`
  (`l4st_wall_zero_iff`), and switching can only occur when `z₃ ∈ 𝒲`
  (`l4st_mem_walls_of_maximizers`);
* Lemma 13.2.6 (`lem:first-control`): the first control is the lexicographic maximum of the
  control vectors, with the tie rule `{ζ^i, ζ^{i+1}} ↦ ζ^i`; with it, the first control exists and
  is unique (`l4st_exists_isFirstControl`, `l4st_isFirstControl_unique`);
* Corollary 13.2.7 (`cor:10`): `t_sw < 10 r` when `|z_i| ≤ r^i`;
* Lemma 13.2.8 (unlabelled): `χ_{ζ,ζ²} + χ_{ζ²,ζ} = 0`;
* Lemma 13.2.5 (`lem:first-negative-control`): the most recent control and switching time by
  time reversal;
* the basic properties of the first switching time: `0 < t_sw` for `z⁰ ≠ 0` (TeX 10750–10753:
  "`t = 0` is an isolated zero of the relevant switching function"), the first control is optimal
  on `[0, t_sw]`, and it is beaten at times arbitrarily close to `t_sw` from the right;
* the first-control trajectory of `z⁰ ≠ 0` does not reach `0` on `[0, t_sw]`
  (`l4f_flow_firstControl_ne_zero`; Lemma 13.3.1 covers only `z₃⁰ ∈ 𝒲`).

The informal corollary after Lemma 13.2.8 (TeX 11063–11067: switching back and forth between `ζ`
and `ζ²` happens at consecutive roots of one cubic, and after its largest root the control switches
to `1`) is not a numbered result and is not used later; it is not formalized.
-/

@[expose] public section

namespace SmoothedPolygons

open Complex MeasureTheory Set TriFuller

namespace TriFuller

/-! ### Walls -/

/-- The wall between `ζ` and `ζ²` (TeX 10912–10918): `RR(w, ζ) = RR(w, ζ²) ≥ RR(w, 1)` if and only
if `w ∈ ℝ_{≤0} = 𝒲₀`. -/
theorem l4st_wall_zero_iff (w : ℂ) :
    (RR w ζ = RR w (ζ ^ 2) ∧ RR w 1 ≤ RR w ζ) ↔ w ∈ wall 0 := by
  sorry

/-- "Switching of controls can only occur when `z₃ ∈ 𝒲`" (TeX 10925–10926): if two distinct
controls of `V_T` both maximize `RR(w, ·)` over `V_T`, then `w ∈ 𝒲`. (The rotation by `ζ^k` takes
the wall `𝒲₀` to `𝒲_k`; `l4st_wall_zero_iff`.) -/
theorem l4st_mem_walls_of_maximizers {w u v : ℂ} (hu : u ∈ VT) (hv : v ∈ VT) (huv : u ≠ v)
    (hmu : ∀ x ∈ VT, RR w x ≤ RR w u) (hmv : ∀ x ∈ VT, RR w x ≤ RR w v) : w ∈ walls := by
  sorry

/-! ### The first control -/

/-- The first control is unique: two first controls of the same point coincide.

Proof: if `u ≠ u'` were both first controls, comparing the maximum conditions along the two
trajectories (`RR(u - u', z₃(t, z⁰, u)) ≥ 0 ≥ RR(u - u', z₃(t, z⁰, u'))` for small `t ≥ 0`) and
using `RR(u - u', -i(u - u')) = 0` forces all four Taylor coefficients of `RR(u - u', z₃(t, z⁰, u))`
to vanish, while its cubic coefficient is `RR(u - u', -iu)/6 = ±√3/12 ≠ 0`. -/
theorem l4st_isFirstControl_unique {z : Fin 3 → ℂ} {u u' : ℂ} (hu : IsFirstControl z u)
    (hu' : IsFirstControl z u') : u = u' := by
  sorry

/-- The most recent control is unique (the time reversal of `l4st_isFirstControl_unique`). -/
theorem l4st_isMostRecentControl_unique {z : Fin 3 → ℂ} {u u' : ℂ}
    (hu : IsMostRecentControl z u) (hu' : IsMostRecentControl z u') : u = u' := by
  sorry

end TriFuller

/-- **Lemma 13.2.6** (`lem:first-control`, TeX 10955–11009). Let `z⁰ ∈ ℂ³ ∖ 0` and let
`V_{T,max} ⊆ V_T` be the set of controls whose control vectors `v(z⁰, u)` are maximal in the
lexicographic order. Then
* if `V_{T,max} = {u}`, then `u` is the first control;
* if `V_{T,max} = {ζ^i, ζ^{i+1}}` has two elements, then the first control is `ζ^i`;
* `V_{T,max} ≠ V_T`.

Proof (the book's):
1. Two vectors that are equal in the lexicographic order are equal; if `V_{T,max} = V_T`, the
   three control vectors are equal, `RR(z_j⁰, 1) = RR(z_j⁰, ζ) = RR(z_j⁰, ζ²)`, and
   `1 + ζ + ζ² = 0` (the three vertices span `ℂ` over `ℝ`) forces `z⁰ = 0`.
2. The first control maximizes `RR(z₃(t), ·)` for small `t ≥ 0`, and
   `z₃(t) = z₃⁰ + z₂⁰ t + z₁⁰ t²/2 - iut³/6` (13.2.2): the switching function
   `RR(u - v, z₃(t, z⁰, u))` has the Taylor coefficients `RR(z₃⁰, u - v)`, `RR(z₂⁰, u - v)`,
   `RR(z₁⁰, u - v)/2`, `RR(-iu, u - v)/6`, and its sign for small `t > 0` is the sign of the first
   nonzero one. If `V_{T,max} = {u}`, for each `v ≠ u` the first nonzero coefficient among the
   first three is positive (`v(z⁰, v) ≺ v(z⁰, u)`), so `u` maximizes on some `[0, ε]`.
3. If `V_{T,max} = {ζ^i, ζ^{i+1}}`, the first three coefficients for the pair vanish and the
   cubic one decides: by rotation (Lemma 13.2.2, (13.2.7)) take `i = 0`; with the control `ζ`,
   `RR(-iζt³/3!, ζ - 1) = -t³/(4√3) < 0`, so `ζ` is not maximizing, while with the control `1`,
   `RR(-it³/3!, 1 - ζ) = t³/(4√3) > 0`, so `1 = ζ⁰` maximizes on some `[0, ε]` (the third control
   is beaten as in step 2). -/
theorem lemma13_2_6 {z : Fin 3 → ℂ} (hz : z ≠ 0) :
    (∀ u : ℂ, lexMaxControls z = {u} → IsFirstControl z u) ∧
      (∀ i : ℕ, lexMaxControls z = {ζ ^ i, ζ ^ (i + 1)} → IsFirstControl z (ζ ^ i)) ∧
      lexMaxControls z ≠ VT := by
  sorry

namespace TriFuller

/-- Every `z⁰ ≠ 0` has a first control (Lemma 13.2.6: `V_{T,max}` is nonempty, and it is a
singleton or a pair `{ζ^i, ζ^{i+1}}` since it is not `V_T`). -/
theorem l4st_exists_isFirstControl {z : Fin 3 → ℂ} (hz : z ≠ 0) : ∃ u, IsFirstControl z u := by
  sorry

/-- For `z⁰ ≠ 0`, `firstControl z⁰` is the first control of `z⁰`. -/
theorem l4st_isFirstControl_firstControl {z : Fin 3 → ℂ} (hz : z ≠ 0) :
    IsFirstControl z (firstControl z) := by
  sorry

/-- For `z⁰ ≠ 0`, `firstControl z⁰ = u` if and only if `u` is the first control of `z⁰`. -/
theorem l4st_firstControl_eq_iff {z : Fin 3 → ℂ} (hz : z ≠ 0) {u : ℂ} :
    firstControl z = u ↔ IsFirstControl z u := by
  sorry

/-- "In this way, the first control must maximize the lexicographical order" (TeX 10990–10991):
the first control of `z⁰ ≠ 0` lies in `V_{T,max}`. -/
theorem l4st_firstControl_mem_lexMaxControls {z : Fin 3 → ℂ} (hz : z ≠ 0) :
    firstControl z ∈ lexMaxControls z := by
  sorry

/-- For `z⁰ ≠ 0`, `t = 0` is not a limit of switching times: `t_sw > 0` (TeX 10750–10753). -/
theorem l4st_firstSwitchTime_pos {z : Fin 3 → ℂ} (hz : z ≠ 0) : 0 < firstSwitchTime z := by
  sorry

/-- The first control is optimal along its trajectory on the closed interval `[0, t_sw]`. -/
theorem l4st_firstControl_maximizes {z : Fin 3 → ℂ} (hz : z ≠ 0) :
    ∀ t ∈ Icc 0 (firstSwitchTime z), ∀ v ∈ VT,
      ham (flow t z (firstControl z)) v ≤ ham (flow t z (firstControl z)) (firstControl z) := by
  sorry

/-- The trajectory switches at `t_sw`: the first control is beaten at times arbitrarily close to
`t_sw` from the right (in fact on a whole interval `(t_sw, t_sw + ε)`, the switching functions
being polynomials). -/
theorem l4st_firstControl_beaten {z : Fin 3 → ℂ} (hz : z ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ t ∈ Ioo (firstSwitchTime z) (firstSwitchTime z + ε), ∃ v ∈ VT,
      ham (flow t z (firstControl z)) (firstControl z) < ham (flow t z (firstControl z)) v := by
  sorry

/-- **The first-control trajectory does not reach the singular locus up to `t_sw`**: for
`z⁰ ≠ 0` with first control `u₀` and `t ∈ [0, t_sw]`, `z(t, z⁰, u₀) ≠ 0`. (Lemma 13.3.1,
`lemma13_3_1`, gives `z(t) ≠ 0` for every `t`, but only when `z₃⁰ ∈ 𝒲`; here `z₃⁰` is arbitrary.)

Proof route: `z(0, z⁰, u₀) = z⁰ ≠ 0` (`l4st_flow_zero`). Suppose `z(S, z⁰, u₀) = 0` with
`0 < S ≤ t_sw`. By the flow property (`l4st_flow_add`), `z(t, z⁰, u₀) = z(t - S, 0, u₀)`, whose
third coordinate is `-iu₀(t - S)³/6` by (13.2.2). The control `u₀ζ` lies in `V_T`
(`l4st_isFirstControl_firstControl`, `l4st_VT_props`), and
`H_F(z(t), u₀ζ) - H_F(z(t), u₀) = RR(u₀ζ - u₀, -iu₀(t - S)³/6) = -(√3/12)(t - S)³`
(`|u₀| = 1` and `RR(ζ - 1, -i) = -√3/2`), which is `> 0` for `t < S`: `u₀ζ` strictly beats `u₀` at
every `t ∈ (0, S) ⊆ [0, t_sw]`, against `l4st_firstControl_maximizes`. -/
theorem l4f_flow_firstControl_ne_zero {z : Fin 3 → ℂ} (hz : z ≠ 0) {t : ℝ}
    (ht : t ∈ Icc 0 (firstSwitchTime z)) : flow t z (firstControl z) ≠ 0 := by
  sorry

end TriFuller

/-- **Corollary 13.2.7** (`cor:10`, TeX 11011–11045). Let `z ∈ ℂ³ ∖ 0` satisfy `|z_i| ≤ r^i` for
`i = 1, 2, 3`, and let `u` be the first control. Then the switching function from `u` to `u/ζ`
has a positive root less than `10r`. In particular, the first switching time `t_sw` is less than
`10r`.

Proof (the book's): by rotation (Lemma 13.2.2) take `u = ζ`.
1. Claim: `v(z, ζ) ≻ v(z, 1)` strictly. It is `⪰` because `ζ` is the first control
   (`l4st_firstControl_mem_lexMaxControls`); if the vectors were equal, `V_{T,max} = {1, ζ}` by
   Lemma 13.2.6 (c), and Lemma 13.2.6 (b) would make `1` the first control
   (`l4st_isFirstControl_unique`).
2. `√3 χ(t) = RR(ζ - 1, z₃(t)) = -t³/(4√3) + Σ_{k=0}^{2} RR(ζ - 1, z_{3-k}) t^k/k!`: the leading
   coefficient is negative and, by the claim, the lowest nonzero coefficient is positive, so there
   is a positive root (intermediate value theorem).
3. For `t ≥ 10r`, `t⁻³ Σ_{k=0}^{2} |RR(ζ - 1, z_{3-k})| t^k/k! ≤ √3 Σ 10^{k-3}/k! < 1/(4√3)`
   (`|ζ - 1| = √3`, `|z_{3-k}| ≤ r^{3-k}`; the book's first `<` should be `≤`, and the final strict
   inequality `0.0611·√3 < 1/(4√3)` holds), so `χ(t) < 0`: the root is below `10r`, and `χ < 0`
   near `10r` makes `u/ζ` beat `u` before `10r`, so `t_sw < 10r`. -/
theorem corollary13_2_7 {z : Fin 3 → ℂ} (hz : z ≠ 0) {r : ℝ} (h₁ : ‖z 0‖ ≤ r)
    (h₂ : ‖z 1‖ ≤ r ^ 2) (h₃ : ‖z 2‖ ≤ r ^ 3) {u : ℂ} (hu : IsFirstControl z u) :
    (∃ t, 0 < t ∧ t < 10 * r ∧ switchingFunction u (u - u / ζ) t z = 0) ∧
      firstSwitchTime z < 10 * r := by
  sorry

/-- **Lemma 13.2.8** (unlabelled, TeX 11047–11061). Fix `z⁰ ∈ ℂ³ ∖ 0` with `z₃⁰ ∈ ℝ_{≤0}`, the wall
between the control modes `ζ` and `ζ²`. Then the switching functions with initial condition `z⁰`
at `t = 0` satisfy `χ_{ζ,ζ²}(t) + χ_{ζ²,ζ}(t) = 0` for all `t`, where `χ_{ij} = χ^i_{ij}` is
computed with its own control.

Proof (book: "an easy computation"): the two cubics differ only in their `t³` terms, and the sum is
`(1/√3) RR(ζ - ζ², -i(ζ - ζ²)) t³/6 = 0`. The hypotheses `z⁰ ≠ 0` and `z₃⁰ ∈ ℝ_{≤0}` are not used
(the identity holds for every `z⁰`; inventory, gap 5); the statement is kept as printed. -/
theorem lemma13_2_8 {z : Fin 3 → ℂ} (hz : z ≠ 0) (h₃ : z 2 ∈ wall 0) (t : ℝ) :
    switchingFunction ζ (ζ - ζ ^ 2) t z + switchingFunction (ζ ^ 2) (ζ ^ 2 - ζ) t z = 0 := by
  sorry

/-- **Lemma 13.2.5** (`lem:first-negative-control`, TeX 10891–10906). For each `t ∈ ℝ`,
`τ(z(-t, z⁰, u)) = z(t, τ(z⁰), ū)`. Also, the most recent control of `z⁰` is `u` if `ū` is the
first control of `τ(z⁰)`. Moreover, the most recent switching time for the initial condition
`z⁰ ∈ ℂ³ ∖ 0` is `-t_sw`, where `t_sw` is the first positive switching time of `τ(z⁰)`.

Proof (book: "follows from the time-reversal symmetry (Lemma 13.2.3)"): the first identity is
`l4st_tau_flow_neg` (a polynomial identity). With `H_F(τ w, v) = H_F(w, v̄)` (`l4st_ham_tau`) and
`conj V_T = V_T`, the maximum condition for `ū` along `s ↦ z(s, τ(z⁰), ū)` on `[0, ε]` is the
maximum condition for `u` along `t ↦ z(t, z⁰, u)` on `[-ε, 0]`, which gives the second assertion;
with the uniqueness of the first and most recent controls
(`l4st_isFirstControl_unique`, `l4st_isMostRecentControl_unique`) and the existence of the first
control of `τ(z⁰) ≠ 0` (Lemma 13.2.6), the sets defining `mostRecentSwitchTime z⁰` and
`firstSwitchTime (τ z⁰)` are opposite, which gives the third.

Departure from the paper (route): Lemma 13.2.3 (`lemma13_2_3`) is about solutions with
`H_F = 0` (13.2.6), and Lemma 13.2.5 concerns every `z⁰` (the Hamiltonian need not vanish), so the
proof uses the substitution behind Lemma 13.2.3 (`l4st_tau_flow_neg`, `l4st_ham_tau`) for
constant controls instead of the lemma itself. -/
theorem lemma13_2_5 :
    (∀ (t : ℝ) (z : Fin 3 → ℂ) (u : ℂ), tau (flow (-t) z u) = flow t (tau z) (starRingEnd ℂ u)) ∧
      (∀ (z : Fin 3 → ℂ) (u : ℂ), IsFirstControl (tau z) (starRingEnd ℂ u) →
        IsMostRecentControl z u) ∧
      ∀ z : Fin 3 → ℂ, z ≠ 0 → mostRecentSwitchTime z = -firstSwitchTime (tau z) := by
  sorry

end SmoothedPolygons
