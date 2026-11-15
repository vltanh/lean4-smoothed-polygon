module

public import SmoothedPolygons.Ch14.UnstableCurve
public import SmoothedPolygons.Ch16.NextSwitch

/-!
# Chapter 14: a chattering arc has no switching point whose orbit reaches the star boundary

The dynamical half of the proof of Theorem 14.4.1 (`thm:no-return`, Hales–Vajjha, *Packings of
Smoothed Polygons*, TeX 12003–12008): "Any trajectory that returns to the singular locus must
chatter (that is, must use infinitely many switches to arrive). This would require the unstable
curve to contain a sequence of forward iterates of points tending to the exceptional divisor. This
does not happen, because the unstable curve hits the boundary of the star domain."

Along a chattering arc into the singular locus (`IsChatteringArcInto`: infinitely many switching
times `τ n ↑ b`), if the `n`-th switching point, rotated by `Ad_{R⁻ᵏ}`, is a phase point `q₀` whose
forward orbit under the Reinhardt–Poincaré map reaches the boundary of the star domain
(`ReachesStarBoundary q₀`, the conclusion of the numerical fact N4,
`SmoothedPolygons/Ch14/UnstableCurve.lean`), we get a contradiction
(`IsChatteringArcInto.not_reachesStarBoundary`):

1. `IsChatteringArcInto.iterate_reinPoincare`: while the orbit switches cyclically, the switching
   points `τ (n + j)`, rotated by `Ad_{R^{-(k+j)}}`, are the iterates `F^j q₀`
   (`IsChatteringArcInto.next_switchPoint_eq_reinPoincare`, by induction on `j`);
2. `IsChatteringArcInto.arc_eq_vertexFlow`: from a switching point where the control after the
   switch is `e₂` (`SwitchEntersE2`), the extremal is the `e₂`-flow up to the next switching time,
   at which some other vertex reaches the Hamiltonian of `e₂`;
3. `IsChatteringArcInto.false_of_arcLeavesStarDomain`: if the `e₂`-flow from the switching point
   leaves the star domain at a time `T` before any vertex reaches `e₂` (`ArcLeavesStarDomain`), the
   next switching time is not in `(0, T)` (step 2), so the extremal follows the flow up to `T` and
   its state at `τ n + T` is not a star state — but the extremal's states are star states (the state
   constraint, `IsStateTrajectory`; Theorem 4.4.1): a contradiction. This is "the forward step of
   the Reinhardt–Poincaré map is no longer defined" (TeX 11985–11986), read for an extremal: an
   extremal that switches infinitely often cannot pass through such a point.

## Proofs (planned)

Step 2 is the first half of the proof of `IsChatteringArcInto.next_switchPoint_eq_reinPoincare`
(`SmoothedPolygons/Ch16/NextSwitch.lean`): the parts (i)–(ii) (the control after `τ n` is neither
`e₁` nor `e₃`, from the two conditions of `SwitchEntersE2`) give the vertex flow on
`[τ n, τ (n + 1)]` (`l6h_arc`), and part (v) gives the vertex `j₁ + k` used right after
`τ (n + 1)`, which differs from `e₂` and maximizes the Hamiltonian there, so that by continuity its
Hamiltonian at `τ (n + 1)` is at least that of `e₂`. The helpers `l6h_conj`,
`l6h_isExtremalOn_conj`, `l6h_arc_core`, `l6h_arc`, `l6h_ae_vertex_between` of NextSwitch.lean are
private: copy them with a new prefix (about 250 lines), or make them public there (no statement
changes). Step 3: with `s = τ (n + 1) - τ n > 0`, `s < T` contradicts the strict maximality of `e₂`
at `s`; `s ≥ T` gives `R⁻ᵏ X(τ n + T) Rᵏ = iso_vfX 1 q₀ T`, a star state by
`poly_isStarState_conj_pow` and the state constraint of `IsExtremalOn`. Step 1: induction on `j`,
`Function.iterate_succ_apply'`. Size: 350–500 lines (about 250 of them the copied helpers).
-/

@[expose] public section

namespace SmoothedPolygons

open Set Filter Topology
open TriFuller

/-- **From a switching point where the control after the switch is `e₂`, the extremal is the
`e₂`-flow up to the next switching time**, at which some other vertex reaches the Hamiltonian of
`e₂` (in the frame rotated by `Ad_{R⁻ᵏ}`). -/
theorem IsChatteringArcInto.arc_eq_vertexFlow {a b : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X Λ₁ ΛR : ℝ → Mat2} {τ : ℕ → ℝ} (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) (n k : ℕ)
    {q₀ : iso_PhasePt} (hq : iso_adRinvPow k (phaseAt X Λ₁ ΛR (τ n)) = q₀)
    (he : SwitchEntersE2 q₀) :
    (∀ t ∈ Icc (τ n) (τ (n + 1)),
      iso_adRinvPow k (phaseAt X Λ₁ ΛR t) = iso_vertexFlow 1 q₀ (t - τ n)) ∧
      ∃ j : Fin 3, j ≠ 1 ∧
        phaseHam (iso_vertexFlow 1 q₀ (τ (n + 1) - τ n)) (vertex 1) ≤
          phaseHam (iso_vertexFlow 1 q₀ (τ (n + 1) - τ n)) (vertex j) := by
  sorry

/-- **A chattering arc cannot pass through a switching point whose `e₂`-arc leaves the star domain
before any switch**: the extremal would follow the arc out of the star domain. -/
theorem IsChatteringArcInto.false_of_arcLeavesStarDomain {a b : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X Λ₁ ΛR : ℝ → Mat2} {τ : ℕ → ℝ} (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) (n k : ℕ)
    {q₀ : iso_PhasePt} (hq : iso_adRinvPow k (phaseAt X Λ₁ ΛR (τ n)) = q₀)
    (he : SwitchEntersE2 q₀) (hl : ArcLeavesStarDomain q₀) : False := by
  sorry

/-- **The switching points follow the Reinhardt–Poincaré map while the orbit switches cyclically**:
if the `n`-th switching point, rotated by `Ad_{R⁻ᵏ}`, is `q₀`, and the iterates `F^j q₀`, `j < K`,
switch cyclically, then the `(n + j)`-th switching point, rotated by `Ad_{R^{-(k+j)}}`, is `F^j q₀`
for `j ≤ K` (`IsChatteringArcInto.next_switchPoint_eq_reinPoincare`, by induction). -/
theorem IsChatteringArcInto.iterate_reinPoincare {a b : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X Λ₁ ΛR : ℝ → Mat2} {τ : ℕ → ℝ} (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) (n k : ℕ)
    {q₀ : iso_PhasePt} (hq : iso_adRinvPow k (phaseAt X Λ₁ ΛR (τ n)) = q₀) {K : ℕ}
    (he : ∀ j < K, SwitchEntersE2 (reinPoincare^[j] q₀))
    (hs : ∀ j < K, ArcSwitchesToE1 (reinPoincare^[j] q₀)) :
    ∀ j ≤ K, iso_adRinvPow (k + j) (phaseAt X Λ₁ ΛR (τ (n + j))) = reinPoincare^[j] q₀ := by
  sorry

/-- **No switching point of a chattering arc into the singular locus has a forward orbit reaching
the boundary of the star domain** (TeX 12005–12008: "This would require the unstable curve to
contain a sequence of forward iterates of points tending to the exceptional divisor. This does not
happen, because the unstable curve hits the boundary of the star domain"): the switching points
after `τ n` follow the orbit (`iterate_reinPoincare`) until its arc leaves the star domain, which
the extremal cannot follow (`false_of_arcLeavesStarDomain`). -/
theorem IsChatteringArcInto.not_reachesStarBoundary {a b : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X Λ₁ ΛR : ℝ → Mat2} {τ : ℕ → ℝ} (h : IsChatteringArcInto a b u g X Λ₁ ΛR τ) (n k : ℕ)
    {q₀ : iso_PhasePt} (hq : iso_adRinvPow k (phaseAt X Λ₁ ΛR (τ n)) = q₀) :
    ¬ ReachesStarBoundary q₀ := by
  sorry

end SmoothedPolygons
